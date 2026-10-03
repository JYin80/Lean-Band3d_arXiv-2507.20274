/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.Primitive
import RBM3D.Loop.GLoop

/-!
# The `K`-loop layer, first ticket (KL1): the tree-sum definition of `𝒦^{(n)}`, `d ≥ 3`

Ticket T2008.  Names are in `RBM.Loop`, every new public name has the prefix `KL` (or the file
stem `KLTree_`).

* Sections 1-5 (lines from `namespace RBM.Loop` to `end Proofs2`) are the compiled draft of the
  T2004 probe (`64b58eb:RBM3D/Probe/T2004Pins.lean` lines 41-501), copied verbatim:
  the laminar API, the definition of `𝒦` by the tree sum `(eq_Ktree)` (`KLK`), `(Kn2sol)`,
  `(Kn3sol)`, the parameter range `KLPar` and the local propagator shapes `KLPT`, the molecule
  layer `KLKpi`, `KLSigmaPi`, `(eq_K-Kpi)`, `(WI_calK)` at `n = 2`.
* Section 6: ports from `RBM2D/Loop/{TreeRep,Kcal}.lean` at `c9a24cf` (the laminar API lemmas,
  `KLSigmaPi_empty_symm`).
* Section 7: the kernel-generic successors `treeEqRhsS`, `MLoopM`, `IsKLoopS` of the merged
  `treeEqRhs`, `MLoop`, `IsKLoop` (which are frozen).
* Section 8: the compiled instances at `d = 3, L = 5, W = 2, g = 1/2, E = 0, t = 9/10`.
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. The definition of `𝒦` (pin `Def_Ktza`, option B: the tree sum is the definition) -/

section Laminar

variable {n : ℕ} [NeZero n]

/-- The root node `(0, n-1)`, whose arc contains every non-root vertex. -/
def KLwholeP (n : ℕ) [NeZero n] : Fin n × Fin n :=
  (0, ⟨n - 1, by have := NeZero.pos n; omega⟩)

/-- Vertex `v` lies in the arc of `J = (i, j)`: `i ≤ v < j`. -/
def KLInArc (J : Fin n × Fin n) (v : Fin n) : Prop := J.1 ≤ v ∧ v < J.2

instance (J : Fin n × Fin n) (v : Fin n) : Decidable (KLInArc J v) := by
  unfold KLInArc; infer_instance

/-- The arc of `J` is contained in the arc of `J'`. -/
def KLArcLe (J J' : Fin n × Fin n) : Prop := J'.1 ≤ J.1 ∧ J.2 ≤ J'.2

instance (J J' : Fin n × Fin n) : Decidable (KLArcLe J J') := by
  unfold KLArcLe; infer_instance

/-- The width `j - i` of the arc of `(i, j)`. -/
def KLarcWidth (J : Fin n × Fin n) : ℕ := J.2.val - J.1.val

/-- The internal vertices of the tree of `F`: `F ∪ {root}`. -/
def KLnodes (F : Finset (Fin n × Fin n)) : Finset (Fin n × Fin n) := insert (KLwholeP n) F

theorem KLmem_nodes_of_mem {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n} (h : J ∈ F) :
    J ∈ KLnodes F := mem_insert_of_mem h

/-- The smallest node of a set of candidates, or the root if there is none. -/
noncomputable def KLminNode (s : Finset (Fin n × Fin n)) : Fin n × Fin n :=
  if h : s.Nonempty then Classical.choose (s.exists_min_image KLarcWidth h) else KLwholeP n

theorem KLminNode_mem_or {s : Finset (Fin n × Fin n)} :
    KLminNode s ∈ s ∨ KLminNode s = KLwholeP n := by
  unfold KLminNode
  split_ifs with h
  · exact Or.inl (Classical.choose_spec (s.exists_min_image KLarcWidth h)).1
  · exact Or.inr rfl

/-- The parent of the leaf `v`: the smallest node whose arc contains `v`. -/
noncomputable def KLleafPar (F : Finset (Fin n × Fin n)) (v : Fin n) : Fin n × Fin n :=
  KLminNode ((KLnodes F).filter fun J => KLInArc J v)

/-- The parent of the node `J`: the smallest other node whose arc contains the arc of `J`. -/
noncomputable def KLnodePar (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) : Fin n × Fin n :=
  KLminNode ((KLnodes F).filter fun J' => KLArcLe J J' ∧ J' ≠ J)

theorem KLleafPar_mem (F : Finset (Fin n × Fin n)) (v : Fin n) : KLleafPar F v ∈ KLnodes F := by
  rcases KLminNode_mem_or (s := (KLnodes F).filter fun J => KLInArc J v) with h | h
  · exact (mem_filter.1 h).1
  · rw [KLleafPar, h]; exact mem_insert_self _ _

theorem KLnodePar_mem (F : Finset (Fin n × Fin n)) (J : Fin n × Fin n) :
    KLnodePar F J ∈ KLnodes F := by
  rcases KLminNode_mem_or (s := (KLnodes F).filter fun J' => KLArcLe J J' ∧ J' ≠ J) with h | h
  · exact (mem_filter.1 h).1
  · rw [KLnodePar, h]; exact mem_insert_self _ _

/-- Over the empty family every leaf hangs on the root: the star. -/
theorem KLleafPar_empty (v : Fin n) :
    KLleafPar (∅ : Finset (Fin n × Fin n)) v = KLwholeP n := by
  rcases KLminNode_mem_or (s := (KLnodes (∅ : Finset (Fin n × Fin n))).filter
    fun J => KLInArc J v) with h | h
  · have h1 := (mem_filter.1 h).1
    have h2 : (KLnodes (∅ : Finset (Fin n × Fin n))) = {KLwholeP n} := by simp [KLnodes]
    rw [h2, mem_singleton] at h1
    exact h1
  · exact h

end Laminar

section Value

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The value of the tree of `F` with leaf weights `M v` and internal edge weights `E J`:
`∑_b ∏_v (M_v)_{a_v, b(par v)} ∏_{J ∈ F} (E_J)_{b(J), b(par J)}`, summed over the labels `b` of
all internal vertices. -/
noncomputable def KLtreeValW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) : ℂ :=
  ∑ b : ↥(KLnodes F) → Zd d L,
    (∏ v : Fin n, M v (a v) (b ⟨KLleafPar F v, KLleafPar_mem F v⟩)) *
      ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)

/-- `(M-graph-value-unsummed)` without the prefactor: leaf edges `Θ^{(σ_v,σ_{v+1})}_t`
`(f-external)`, internal edges `Θ^{(σ_i,σ_j)}_t - I` `(f-internal)`. -/
noncomputable def KLtreeValG {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (F : Finset (Fin n × Fin n)) : ℂ :=
  KLtreeValW d L F a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
    (fun J => thetaEdge d L g m t (σ J.1.1) (σ J.1.2) - 1)

/-- `(eq_Ktree)`: `m_σ W^{-d(n-1)} ∑_{F ∈ TSP(n)} Γ_F`, `m_σ = ∏ m(σ_i)`. -/
noncomputable def KLn (W : ℕ) (m : Bool → ℂ) (t : ℝ) (n : ℕ) [NeZero n] (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  (∏ i, m (σ i)) * (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, KLtreeValG d L g m t σ a F

/-- The tree representation on loop indices: `m(σ₁)` at `n = 1`, `(Kn2sol)` at `n = 2`,
`(eq_Ktree)` at `n ≥ 3`; `0` on the empty loop. -/
noncomputable def KLgen (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  if I.length = 1 then m (I.σ.getD 0 false)
  else if I.length = 2 then
    kTwo d L W g m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0) (I.a.getD 1 0)
  else if h : 3 ≤ I.length then
    haveI : NeZero I.length := ⟨by omega⟩
    KLn d L g W m t I.length (fun i => I.σ.getD i false) (fun i => I.a.getD i 0)
  else 0

/-- **`𝒦^{(n)}_{t,σ,a}`** of `Def_Ktza` at the energy `E`: `m(σ) = mSigma E σ` (`m(+) = m(E+i0)`). -/
noncomputable def KLK (W : ℕ) (E t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  KLgen d L g W (mSigma E) t I

/-- The loop index of a sign vector and a label vector of the same length. -/
def KLloopOf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) : LoopIdx (Zd d L) :=
  ⟨List.ofFn σ, List.ofFn a⟩

end Value

/-! ## 2. What is proved here about the definition -/

section Proofs

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- Over the empty family the tree is the star `∑_b ∏_v (M_v)_{a_v b}`. -/
theorem KLtreeValW_empty {n : ℕ} [NeZero n] (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥(∅ : Finset (Fin n × Fin n)) → Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L ∅ a M E = ∑ b : Zd d L, ∏ v : Fin n, M v (a v) b := by
  have : Unique ↥(KLnodes (∅ : Finset (Fin n × Fin n))) :=
    { default := ⟨KLwholeP n, mem_insert_self _ _⟩
      uniq := fun x => Subtype.ext (by
        have hx : (x : Fin n × Fin n) ∈ ({KLwholeP n} : Finset (Fin n × Fin n)) := by
          simpa [KLnodes] using x.2
        exact mem_singleton.1 hx) }
  rw [KLtreeValW,
    ← (Equiv.funUnique ↥(KLnodes (∅ : Finset (Fin n × Fin n))) (Zd d L)).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun c => ?_
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, KLleafPar_empty]
  rfl

private theorem KLn_cast (W : ℕ) (m : Bool → ℂ) (t : ℝ) {k k' : ℕ} (hk : NeZero k)
    (hk' : NeZero k') (h : k = k') (σ : Fin k → Bool) (a : Fin k → Zd d L)
    (σ' : Fin k' → Bool) (a' : Fin k' → Zd d L)
    (hσ : ∀ i : Fin k, σ i = σ' (Fin.cast h i)) (ha : ∀ i : Fin k, a i = a' (Fin.cast h i)) :
    @KLn d L _ g W m t k hk σ a = @KLn d L _ g W m t k' hk' σ' a' := by
  subst h
  have h1 : σ = σ' := funext fun i => by simpa using hσ i
  have h2 : a = a' := funext fun i => by simpa using ha i
  subst h1 h2
  rfl

/-- On `KLloopOf σ a` with `n ≥ 3`, the loop-index form is the tree sum. -/
theorem KLgen_loopOf (W : ℕ) (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    KLgen d L g W m t (KLloopOf d L σ a) = KLn d L g W m t n σ a := by
  have hlen : (KLloopOf d L σ a).length = n := by simp [KLloopOf, LoopIdx.length]
  have h1 : (KLloopOf d L σ a).length ≠ 1 := by omega
  have h2 : (KLloopOf d L σ a).length ≠ 2 := by omega
  have h3 : 3 ≤ (KLloopOf d L σ a).length := by omega
  simp only [KLgen, h1, h2, ↓reduceIte, h3, ↓reduceDIte]
  refine KLn_cast d L g W m t _ _ hlen _ _ _ _ (fun i => ?_) (fun i => ?_)
  · have hi : (i : ℕ) < n := by have := i.isLt; omega
    simp [KLloopOf, List.getD_eq_getElem?_getD, hi]
    rfl
  · have hi : (i : ℕ) < n := by have := i.isLt; omega
    simp [KLloopOf, List.getD_eq_getElem?_getD, hi]
    rfl

/-- `𝒦^{(1)}_{t,σ,a} = m(σ)`. -/
theorem KLK_one (W : ℕ) (E t : ℝ) (s : Bool) (a : Zd d L) :
    KLK d L g W E t ⟨[s], [a]⟩ = mSigma E s := by
  simp [KLK, KLgen, LoopIdx.length]

/-- **`(Kn2sol)`**: `𝒦^{(2)}_{t,σ,a} = W^{-d} m₁ m₂ Θ_{t m₁ m₂}(a₁, a₂)`. -/
theorem KLK_two (W : ℕ) (E t : ℝ) (s₁ s₂ : Bool) (a₁ a₂ : Zd d L) :
    KLK d L g W E t ⟨[s₁, s₂], [a₁, a₂]⟩
      = ((W : ℂ) ^ d)⁻¹ * (mSigma E s₁ * mSigma E s₂)
          * Theta d L g ((t : ℂ) * (mSigma E s₁ * mSigma E s₂)) a₁ a₂ := by
  simp [KLK, KLgen, kTwo, LoopIdx.length]

/-- **`(Kn3sol)`**: `𝒦^{(3)} = W^{-2d} m₁m₂m₃ ∑_b Θ_{t m₁m₂}(a₁,b) Θ_{t m₂m₃}(a₂,b) Θ_{t m₃m₁}(a₃,b)`. -/
theorem KLK_three (W : ℕ) (E t : ℝ) (s₁ s₂ s₃ : Bool) (a₁ a₂ a₃ : Zd d L) :
    KLK d L g W E t ⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩
      = (((W : ℂ) ^ d)⁻¹) ^ 2 * (mSigma E s₁ * mSigma E s₂ * mSigma E s₃) *
          ∑ b : Zd d L, Theta d L g ((t : ℂ) * (mSigma E s₁ * mSigma E s₂)) a₁ b *
            Theta d L g ((t : ℂ) * (mSigma E s₂ * mSigma E s₃)) a₂ b *
              Theta d L g ((t : ℂ) * (mSigma E s₃ * mSigma E s₁)) a₃ b := by
  have hI : (⟨[s₁, s₂, s₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L))
      = KLloopOf d L ![s₁, s₂, s₃] ![a₁, a₂, a₃] := by
    simp [KLloopOf]
  rw [hI, KLK, KLgen_loopOf d L g W (mSigma E) t (le_refl 3), KLn, TSP_three,
    Finset.sum_singleton, KLtreeValG, KLtreeValW_empty]
  have h20 : ((2 : Fin 3) + 1) = 0 := rfl
  have h01 : ((0 : Fin 3) + 1) = 1 := rfl
  have h12 : ((1 : Fin 3) + 1) = 2 := rfl
  simp only [Fin.prod_univ_three, thetaEdge, h20, h01, h12, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  simp only [show (3 : ℕ) - 1 = 2 from rfl]
  ring

/-- The new definition agrees with the merged `kTwo`, `kThree` of `Loop/Primitive.lean`,
`Loop/TreeThree.lean`. -/
theorem KLK_two_eq_kTwo (W : ℕ) (E t : ℝ) (s₁ s₂ : Bool) (a₁ a₂ : Zd d L) :
    KLK d L g W E t ⟨[s₁, s₂], [a₁, a₂]⟩ = kTwo d L W g (mSigma E) t s₁ s₂ a₁ a₂ := by
  simp [KLK, KLgen, LoopIdx.length]

end Proofs

/-! ## 3. The parameter range and the local propagator hypotheses -/

/-- **The parameter range of the bound pins.**  `L ≥ 3`, `W ≥ 1`, `0 < g ≤ gmax` (the paper's
`λ̂ ≤ 𝔡⁻¹`, `(eq:WO)`), `|E| ≤ 2 - κ` (bulk), `0 ≤ t < 1`.  `κ`, `gmax` are fixed before the
constants of a pin; the constants do not depend on a point of this structure. -/
structure KLPar (κ gmax : ℝ) where
  L : ℕ
  W : ℕ
  hL : 3 ≤ L
  hW : 1 ≤ W
  g : ℝ
  hg0 : 0 < g
  hg1 : g ≤ gmax
  E : ℝ
  hE : |E| ≤ 2 - κ
  t : ℝ
  ht0 : 0 ≤ t
  ht1 : t < 1

instance KLPar.neZero {κ gmax : ℝ} (p : KLPar κ gmax) : NeZero p.L := ⟨by have := p.hL; omega⟩

/-- Property 5 of `lem_propTH`, `(prop:ThfadC)`, for the `(+,-)` propagator `Θ_t = Theta d L g t`
(the other charges follow from property 4, `norm_Theta_apply_le`):
`|Θ_t(0,a)| ≤ C_d B_{t,|a|} e^{-c_d |a|/ℓ_t}`.  `C_d, c_d` depend on `d, gmax` only. -/
def KLDecay (d : ℕ) (gmax : ℝ) : Prop :=
  ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g (t : ℂ) 0 a‖
        ≤ Cd * Bparam d L g t (zdistD d L a) * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)

/-- Property 5', `(prop:ThfadC_short)`: for equal charges (`ξ = t m(σ)²`),
`|Θ_ξ(0,a)| ≤ C_κ (1_{a=0} + g² e^{-c_κ|a|})`.  `C_κ, c_κ` depend on `d, κ, gmax` only. -/
def KLShort (d : ℕ) (κ gmax : ℝ) : Prop :=
  ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s : Bool, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g ((t : ℂ) * (mSigma E s * mSigma E s)) 0 a‖
        ≤ Cκ * ((if a = 0 then 1 else 0) + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))

/-- Property 6, `(prop:BD1)`: `|Θ_t(0,a+r) - Θ_t(0,a)| ≺ (g²+|1-t|)⁻¹ |r|/(|a|+1)^{d-1}` for
`|r| ≤ c|a|`, every fixed `c < 1`, loss `L^τ`; the constant depends on `c`.  The paper writes
`|r| ≲ |a|`; for `c ≥ 1` the estimate is false (`r = -a`: at `t = 0` one has `Θ_0 = I`, the left
side is `1` and the right side is of order `L^τ/|a|`; the script `ext`, block `bd`, shows the
constant growing like `L`), so the range is part of the pin (paper-delta candidate `T2004c`). -/
def KLDiffOne (d : ℕ) (gmax : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
    g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
      (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g (t : ℂ) 0 (a + r) - Theta d L g (t : ℂ) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ)
            * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- Property 7, `(prop:BD2)`: `|Θ_t(0,a+r)+Θ_t(0,a-r)-2Θ_t(0,a)| ≺ (g²+|1-t|)⁻¹ |r|²/(|a|+1)^d`
for `|r| ≤ c|a|`, every fixed `c < 1` (same range as `KLDiffOne`, same paper-delta `T2004c`). -/
def KLDiffTwo (d : ℕ) (gmax : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
    g ≤ gmax → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a r : Zd d L,
      (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta d L g (t : ℂ) 0 (a + r) + Theta d L g (t : ℂ) 0 (a - r)
          - 2 * Theta d L g (t : ℂ) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2
            * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- Property 8, `(prop:ThfadC0)`: `|Θ̊_t(0,a)| ≺ (g²+|1-t|)⁻¹ /(|a|+1)^{d-2}`. -/
def KLZero (d : ℕ) (gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C > (0 : ℝ), ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ gmax →
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Zd d L,
      haveI : NeZero L := ⟨by omega⟩
      ‖Theta0 d L g (t : ℂ) 0 a‖
        ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-- The properties 5, 5', 6, 7, 8 of `lem_propTH` at the shapes the `K`-loop layer uses
(gate PT supplies them; properties 1-4 are merged: `Propagator/Props4.lean`). -/
structure KLPT (d : ℕ) (κ gmax : ℝ) : Prop where
  decay : KLDecay d gmax
  short : KLShort d κ gmax
  diffOne : KLDiffOne d gmax
  diffTwo : KLDiffTwo d gmax
  zeroMode : KLZero d gmax

/-! ## 4. The molecule layer: `K^{(π)}`, the self-energy `Σ^{(π)}` -/

section Molecule

variable {n : ℕ}

/-- `F_long(Γ, σ)` of `(eq:defKpi)`: the internal edges of `F` between regions of different
charge. -/
def KLFlong (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) : Finset (Fin n × Fin n) :=
  F.filter fun J => σ J.1 ≠ σ J.2

/-- `TSP(P_a, σ, π)`: the trees whose long internal edges are exactly `π`. -/
def KLTSPlong (n : ℕ) (σ : Fin n → Bool) (π : Finset (Fin n × Fin n)) :
    Finset (Finset (Fin n × Fin n)) :=
  (TSP n).filter fun F => KLFlong F σ = π

/-- The alternating sign vector. -/
def KLsigAlt (n : ℕ) : Fin n → Bool := fun k => decide (k.val % 2 = 0)

variable (d L : ℕ) [NeZero L] (g : ℝ) [NeZero n]

/-- `K^{(π)}(t,σ,a)` of `(eq:defKpi)`, with the factor `∏ m(σ_i)` of `Γ^{(n)}`
(`(M-graph-value-unsummed)`). -/
noncomputable def KLKpi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L)
    (π : Finset (Fin n × Fin n)) : ℂ :=
  (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F

/-- The self-energy of one tree: the leaf edges are removed, `δ_v` is the internal endpoint of
the leaf edge at `a_v`, all internal vertices are summed. -/
noncomputable def KLselfW (F : Finset (Fin n × Fin n)) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ)
    (δ : Fin n → Zd d L) : ℂ :=
  ∑ b : ↥(KLnodes F) → Zd d L,
    (∏ v : Fin n, if δ v = b ⟨KLleafPar F v, KLleafPar_mem F v⟩ then (1 : ℂ) else 0) *
      ∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩) (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)

/-- `Σ^{(π)}(t,σ,δ)` of `(eq:molecule-Kpi)` (first stage: all internal vertices summed); with the
factor `∏ m(σ_i)` of the `M`-loops. `Σ^{(∅)}` is the molecule of `(eq:molecule-decay)`,
`(eq:Sigma-empty-sum-zero)`. -/
noncomputable def KLSigmaPi (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (δ : Fin n → Zd d L) : ℂ :=
  (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π,
    KLselfW d L F (fun J => thetaEdge d L g m t (σ J.1.1) (σ J.1.2) - 1) δ

/-- `max_{i,j} |a_i - a_j|`. -/
def KLmaxDist {n : ℕ} (a : Fin n → Zd d L) : ℕ :=
  Finset.univ.sup fun q : Fin n × Fin n => zdistD d L (a q.1 - a q.2)

end Molecule

/-! ## 5. What is proved here about the molecule layer and `(WI_calK)` at `n = 2` -/

section Proofs2

private theorem KLsum_TSPlong {n : ℕ} {M : Type*} [AddCommMonoid M] (σ : Fin n → Bool)
    (f : Finset (Fin n × Fin n) → M) :
    ∑ π ∈ (diagonals n).powerset, ∑ F ∈ KLTSPlong n σ π, f F = ∑ F ∈ TSP n, f F := by
  refine sum_fiberwise_of_maps_to (fun F hF => ?_) f
  rw [mem_powerset]
  have hF' := (mem_filter.1 hF).1
  exact (filter_subset _ _).trans (mem_powerset.1 hF')

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- **`(eq_K-Kpi)`**: `𝒦^{(n)}_{t,σ,a} = W^{-d(n-1)} ∑_{π ⊂ Z^{off}_n} K^{(π)}(t,σ,a)`, `n ≥ 3`. -/
theorem KLK_eq_sum_Kpi (W : ℕ) (E t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    KLK d L g W E t (KLloopOf d L σ a)
      = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
          ∑ π ∈ (diagonals n).powerset, KLKpi d L g (mSigma E) t σ a π := by
  rw [KLK, KLgen_loopOf d L g W (mSigma E) t hn σ a, KLn]
  simp only [KLKpi, ← Finset.mul_sum]
  rw [KLsum_TSPlong]
  ring

/-- Re-attaching the leaf edges to the self-energy gives back the tree value. -/
theorem KLtreeValW_eq_sum_selfW {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a M E = ∑ δ : Fin n → Zd d L, KLselfW d L F E δ * ∏ v, M v (a v) (δ v) := by
  simp only [KLselfW, sum_mul]
  rw [sum_comm, KLtreeValW]
  refine sum_congr rfl fun b _ => ?_
  have h : ∀ δ : Fin n → Zd d L,
      (∏ v : Fin n, if δ v = b ⟨KLleafPar F v, KLleafPar_mem F v⟩ then (1 : ℂ) else 0) *
          (∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩)
            (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)) *
        ∏ v, M v (a v) (δ v) =
      (∏ J : ↥F, E J (b ⟨J.1, KLmem_nodes_of_mem J.2⟩)
          (b ⟨KLnodePar F J, KLnodePar_mem F J⟩)) *
        ∏ v, (if δ v = b ⟨KLleafPar F v, KLleafPar_mem F v⟩ then M v (a v) (δ v) else 0) := by
    intro δ
    rw [mul_comm (∏ v : Fin n, _), mul_assoc, ← prod_mul_distrib]
    congr 2
    funext v
    split_ifs <;> simp
  simp_rw [h, ← mul_sum]
  rw [mul_comm]
  congr 1
  have := (prod_univ_sum (fun _ : Fin n => (univ : Finset (Zd d L)))
    (fun v x => if x = b ⟨KLleafPar F v, KLleafPar_mem F v⟩ then M v (a v) x else 0)).symm
  rw [Fintype.piFinset_univ] at this
  rw [this]
  refine prod_congr rfl fun v _ => ?_
  rw [Fintype.sum_ite_eq']

/-- **The first stage of `(eq:molecule-Kpi)`**:
`K^{(π)}(t,σ,a) = ∑_δ Σ^{(π)}(t,σ,δ) ∏_v Θ^{(σ_v,σ_{v+1})}_t(a_v, δ_v)`. -/
theorem KLKpi_eq_sum_SigmaPi {n : ℕ} [NeZero n] (m : Bool → ℂ) (t : ℝ) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (π : Finset (Fin n × Fin n)) :
    KLKpi d L g m t σ a π
      = ∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ π δ *
          ∏ v, thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) (δ v) := by
  simp only [KLKpi, KLSigmaPi, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [KLtreeValG, KLtreeValW_eq_sum_selfW d L F a, Finset.mul_sum]

private theorem KLmSigma_mul_not {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    mSigma E s * mSigma E (!s) = 1 := by
  have h := norm_mE hE
  have h1 : mE E * (starRingEnd ℂ) (mE E) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  cases s
  · simp only [mSigma, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [mul_comm]; exact h1
  · simpa [mSigma] using h1

/-- **`(WI_calK)` at `n = 2`**, both charge orders: `∑_{a₂} 𝒦^{(2)}_{t,(s,-s),(a₁,a₂)}
= (2 i W^d η_t)⁻¹ (𝒦^{(1)}_{t,+} - 𝒦^{(1)}_{t,-})`, `η_t = (1-t) Im m(E)`. -/
theorem KLward_two (hL : 3 ≤ L) (W : ℕ) (hW : 1 ≤ W) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) (s : Bool) (a₁ : Zd d L) :
    ∑ x : Zd d L, KLK d L g W E t ⟨[s, !s], [a₁, x]⟩
      = (2 * Complex.I * (W : ℂ) ^ d * (Gauss.etaT E t : ℂ))⁻¹ *
          (KLK d L g W E t ⟨[true], [a₁]⟩ - KLK d L g W E t ⟨[false], [a₁]⟩) := by
  have hE2 : |E| ≤ 2 := hE.le
  have hm := KLmSigma_mul_not hE2 s
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have him : 0 < (mE E).im := mE_im_pos hE
  have ht1 : (1 : ℝ) - t ≠ 0 := by linarith [ht.2]
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht.1]; exact ht.2
  have hLHS : ∑ x : Zd d L, KLK d L g W E t ⟨[s, !s], [a₁, x]⟩
      = ((W : ℂ) ^ d)⁻¹ * (1 - (t : ℂ))⁻¹ := by
    have h1 : ∀ x : Zd d L, KLK d L g W E t ⟨[s, !s], [a₁, x]⟩
        = ((W : ℂ) ^ d)⁻¹ * Theta d L g (t : ℂ) a₁ x := by
      intro x
      rw [KLK_two, hm]
      simp
    simp_rw [h1]
    rw [← Finset.mul_sum, sum_Theta_row_of_three_le hL hξ a₁]
  rw [hLHS]
  simp only [KLK_one]
  have hsub : mSigma E true - mSigma E false = ((2 * (mE E).im : ℝ) : ℂ) * Complex.I := by
    simp [mSigma, Complex.sub_conj]
  rw [hsub, Gauss.etaT]
  have him0 : (((mE E).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast him.ne'
  have ht0 : ((1 : ℂ) - t) ≠ 0 := by exact_mod_cast ht1
  have hWd : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ hW0
  push_cast
  field_simp

end Proofs2

/-! ## 6. Ports from `RBM2D/Loop/{TreeRep,Kcal}.lean` (commit `c9a24cf`) -/

/-! ### The laminar API: port of `RBM2D/Loop/TreeRep.lean:185-413` (`Z2`-free, `Fin n × Fin n` only)

The RBM2D lemmas are `private` there; here they are public with the prefix `KL` (the next
tickets of gate KL use them).  `wholeP_mem_nodes` (`Kcal.lean:103`) is added. -/

section LaminarAPI

variable {n : ℕ} [NeZero n]

/-- The root belongs to the nodes of every tree.  Port of `RBM2D/Loop/Kcal.lean:103`. -/
theorem KLwholeP_mem_nodes (F : Finset (Fin n × Fin n)) : KLwholeP n ∈ KLnodes F :=
  mem_insert_self _ _

theorem KLminNode_le {s : Finset (Fin n × Fin n)} {e : Fin n × Fin n} (he : e ∈ s) :
    KLminNode s ∈ s ∧ KLarcWidth (KLminNode s) ≤ KLarcWidth e := by
  have h : s.Nonempty := ⟨e, he⟩
  unfold KLminNode
  split_ifs
  exact ⟨(Classical.choose_spec (s.exists_min_image KLarcWidth h)).1,
    (Classical.choose_spec (s.exists_min_image KLarcWidth h)).2 e he⟩

/-! ### Laminarity -/

/-- `F` is a family of diagonals with no crossing pair: an element of `T_SP(n)`. -/
def KLIsTSP (F : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ F, IsDiag n d.1 d.2) ∧ CrossingFree F

omit [NeZero n] in
theorem KLisTSP_of_mem_TSP {F : Finset (Fin n × Fin n)} (h : F ∈ TSP n) : KLIsTSP F := by
  rw [mem_TSP] at h
  refine ⟨fun d hd => ?_, h.2⟩
  have := h.1 hd
  simp only [diagonals, mem_filter, mem_univ, true_and] at this
  exact this

theorem KLarcLe_wholeP (d : Fin n × Fin n) : KLArcLe d (KLwholeP n) := by
  refine ⟨Fin.zero_le _, ?_⟩
  simp only [KLwholeP, Fin.le_def]
  have := d.2.isLt
  omega

theorem KLlt_of_mem_nodes {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ KLnodes F) : d.1 < d.2 := by
  rcases mem_insert.1 hd with rfl | hd
  · simp only [KLwholeP, Fin.lt_def, Fin.val_zero]; omega
  · exact (hF.1 d hd).1

/-- **Laminarity**: two nodes are nested or have disjoint arcs. -/
theorem KLnodes_laminar {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) {d e : Fin n × Fin n}
    (hd : d ∈ KLnodes F) (he : e ∈ KLnodes F) :
    KLArcLe d e ∨ KLArcLe e d ∨ d.2 ≤ e.1 ∨ e.2 ≤ d.1 := by
  rcases mem_insert.1 he with rfl | he'
  · exact Or.inl (KLarcLe_wholeP d)
  rcases mem_insert.1 hd with rfl | hd'
  · exact Or.inr (Or.inl (KLarcLe_wholeP e))
  have h1 := hF.2 d hd' e he'
  have hd2 := (hF.1 d hd').1
  have he2 := (hF.1 e he').1
  simp only [Crossing, not_or, not_and, not_lt] at h1
  simp only [KLArcLe, Fin.le_def, Fin.lt_def] at h1 hd2 he2 ⊢
  omega

omit [NeZero n] in
theorem KLInArc.mono {d e : Fin n × Fin n} {v : Fin n} (h : KLInArc d v) (hde : KLArcLe d e) :
    KLInArc e v := by
  simp only [KLInArc, KLArcLe, Fin.le_def, Fin.lt_def] at *
  omega

omit [NeZero n] in
theorem KLArcLe.trans {d e f : Fin n × Fin n} (h1 : KLArcLe d e)
    (h2 : KLArcLe e f) : KLArcLe d f := by
  simp only [KLArcLe, Fin.le_def] at *
  omega

omit [NeZero n] in
theorem KLArcLe.antisymm {d e : Fin n × Fin n} (h1 : KLArcLe d e) (h2 : KLArcLe e d) : d = e := by
  simp only [KLArcLe, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

omit [NeZero n] in
theorem KLarcWidth_le_of_arcLe {d e : Fin n × Fin n} (h : KLArcLe d e) :
    KLarcWidth d ≤ KLarcWidth e := by
  simp only [KLArcLe, KLarcWidth, Fin.le_def] at *
  omega

omit [NeZero n] in
theorem KLeq_of_arcLe_of_width {d e : Fin n × Fin n} (hd : d.1 ≤ d.2) (h : KLArcLe d e)
    (hw : KLarcWidth e ≤ KLarcWidth d) : d = e := by
  simp only [KLArcLe, KLarcWidth, Fin.le_def] at *
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The containers of a vertex are totally ordered by inclusion. -/
theorem KLarcLe_total_of_inArc {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F)
    {d e : Fin n × Fin n}
    (hd : d ∈ KLnodes F) (he : e ∈ KLnodes F) {v : Fin n} (hdv : KLInArc d v) (hev : KLInArc e v) :
    KLArcLe d e ∨ KLArcLe e d := by
  rcases KLnodes_laminar hF hd he with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp only [KLInArc, Fin.le_def, Fin.lt_def] at hdv hev h; omega
  · simp only [KLInArc, Fin.le_def, Fin.lt_def] at hdv hev h; omega

/-- **Characterization of `leafPar`**: the node that contains `v` and is contained in every
node containing `v`. -/
theorem KLleafPar_eq {F : Finset (Fin n × Fin n)} {v : Fin n} {e : Fin n × Fin n}
    (he : e ∈ KLnodes F) (hev : KLInArc e v)
    (hmin : ∀ e' ∈ KLnodes F, KLInArc e' v → KLArcLe e e') : KLleafPar F v = e := by
  have hmem : e ∈ (KLnodes F).filter fun e => KLInArc e v := mem_filter.2 ⟨he, hev⟩
  obtain ⟨h1, h2⟩ := KLminNode_le hmem
  have h3 := mem_filter.1 h1
  exact (KLeq_of_arcLe_of_width (le_of_lt (lt_of_le_of_lt hev.1 hev.2)) (hmin _ h3.1 h3.2) h2).symm

/-- The root vertex `n - 1` hangs on `whole`. -/
theorem KLleafPar_root (F : Finset (Fin n × Fin n)) {v : Fin n} (hv : v.val = n - 1) :
    KLleafPar F v = KLwholeP n := by
  rcases KLminNode_mem_or (s := (KLnodes F).filter fun e => KLInArc e v) with h | h
  · exfalso
    have := (mem_filter.1 h).2
    simp only [KLInArc, Fin.lt_def] at this
    have := (KLminNode ((KLnodes F).filter fun e => KLInArc e v)).2.isLt
    omega
  · exact h

/-- **Characterization of `nodePar`**: the node strictly above `d` contained in every node
strictly above `d`. -/
theorem KLnodePar_eq {F : Finset (Fin n × Fin n)} {d e : Fin n × Fin n} (hd : d.1 ≤ d.2)
    (he : e ∈ KLnodes F) (hde : KLArcLe d e) (hne : e ≠ d)
    (hmin : ∀ e' ∈ KLnodes F, KLArcLe d e' → e' ≠ d → KLArcLe e e') : KLnodePar F d = e := by
  have hmem : e ∈ (KLnodes F).filter fun e => KLArcLe d e ∧ e ≠ d := mem_filter.2 ⟨he, hde, hne⟩
  obtain ⟨h1, h2⟩ := KLminNode_le hmem
  have h3 := mem_filter.1 h1
  have he12 : e.1 ≤ e.2 := le_trans hde.1 (le_trans hd hde.2)
  exact (KLeq_of_arcLe_of_width he12 (hmin _ h3.1 h3.2.1 h3.2.2) h2).symm

/-- The strict containers of a node are totally ordered by inclusion. -/
theorem KLarcLe_total_of_arcLe {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    {d e e' : Fin n × Fin n} (hd : d ∈ KLnodes F) (he : e ∈ KLnodes F) (he' : e' ∈ KLnodes F)
    (h1 : KLArcLe d e) (h2 : KLArcLe d e') : KLArcLe e e' ∨ KLArcLe e' e := by
  have hlt := KLlt_of_mem_nodes hF hn hd
  rcases KLnodes_laminar hF he he' with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · simp only [KLArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega
  · simp only [KLArcLe, Fin.le_def, Fin.lt_def] at h1 h2 h hlt; omega

/-- `leafPar` is the smallest container of a non-root vertex. -/
theorem KLleafPar_spec {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) {v : Fin n}
    (hv : v.val < n - 1) :
    KLInArc (KLleafPar F v) v ∧ ∀ e ∈ KLnodes F, KLInArc e v → KLArcLe (KLleafPar F v) e := by
  have hW : KLwholeP n ∈ (KLnodes F).filter fun e => KLInArc e v := by
    refine mem_filter.2 ⟨KLwholeP_mem_nodes F, Fin.zero_le _, ?_⟩
    simp only [KLwholeP, Fin.lt_def]; exact hv
  obtain ⟨h1, h2⟩ := KLminNode_le hW
  have hm := mem_filter.1 h1
  refine ⟨hm.2, fun e he hev => ?_⟩
  rcases KLarcLe_total_of_inArc hF hm.1 he hm.2 hev with h | h
  · exact h
  · have hemem : e ∈ (KLnodes F).filter fun e => KLInArc e v := mem_filter.2 ⟨he, hev⟩
    have := (KLminNode_le hemem).2
    rw [KLeq_of_arcLe_of_width (le_of_lt (lt_of_le_of_lt hev.1 hev.2)) h this]
    exact ⟨le_refl _, le_refl _⟩

/-- `nodePar` is the smallest strict container of a node other than `whole`. -/
theorem KLnodePar_spec {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    {d : Fin n × Fin n} (hd : d ∈ KLnodes F) (hdw : d ≠ KLwholeP n) :
    KLnodePar F d ∈ KLnodes F ∧ KLArcLe d (KLnodePar F d) ∧ KLnodePar F d ≠ d ∧
      ∀ e ∈ KLnodes F, KLArcLe d e → e ≠ d → KLArcLe (KLnodePar F d) e := by
  have hW : KLwholeP n ∈ (KLnodes F).filter fun e => KLArcLe d e ∧ e ≠ d :=
    mem_filter.2 ⟨KLwholeP_mem_nodes F, KLarcLe_wholeP d, fun h => hdw h.symm⟩
  obtain ⟨h1, h2⟩ := KLminNode_le hW
  have hm := mem_filter.1 h1
  have hlt := KLlt_of_mem_nodes hF hn hd
  refine ⟨hm.1, hm.2.1, hm.2.2, fun e he hde hne => ?_⟩
  rcases KLarcLe_total_of_arcLe hF hn hd hm.1 he hm.2.1 hde with h | h
  · exact h
  · have hemem : e ∈ (KLnodes F).filter fun e => KLArcLe d e ∧ e ≠ d := mem_filter.2 ⟨he, hde, hne⟩
    have := (KLminNode_le hemem).2
    have he12 : e.1 ≤ e.2 := le_trans hde.1 (le_trans (le_of_lt hlt) hde.2)
    rw [KLeq_of_arcLe_of_width he12 h this]
    exact ⟨le_refl _, le_refl _⟩

theorem KLwholeP_not_mem {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) : KLwholeP n ∉ F := by
  intro h
  have := (hF.1 _ h).2.2
  simp [KLwholeP] at this

/-- A vertex in some arc is not the root. -/
theorem KLlt_of_inArc {d : Fin n × Fin n} {v : Fin n} (hv : KLInArc d v) : v.val < n - 1 := by
  have := (KLarcLe_wholeP d).2
  simp only [KLInArc, KLwholeP, Fin.le_def, Fin.lt_def] at hv this
  omega

/-! ### Which side of a cut `J` the parents lie on -/

section Side

variable {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) {J : Fin n × Fin n}
  (hJ : J ∈ F)
include hF hJ

theorem KLnot_arcLe_wholeP : ¬KLArcLe (KLwholeP n) J := by
  intro h
  have hJd := (hF.1 J hJ)
  obtain ⟨-, -, hw⟩ := hJd
  simp only [KLArcLe, KLwholeP, Fin.le_def] at h
  apply hw
  have := J.2.isLt
  constructor <;> simp only [Fin.val_zero] at h ⊢ <;> omega

theorem KLne_wholeP : J ≠ KLwholeP n := fun h => KLwholeP_not_mem hF (h ▸ hJ)

theorem KLleafPar_arcLe_of_inArc {v : Fin n} (hv : KLInArc J v) : KLArcLe (KLleafPar F v) J :=
  (KLleafPar_spec hF (KLlt_of_inArc hv)).2 J (KLmem_nodes_of_mem hJ) hv

theorem KLnot_arcLe_leafPar {v : Fin n} (hv : ¬KLInArc J v) : ¬KLArcLe (KLleafPar F v) J := by
  intro h
  by_cases hr : v.val < n - 1
  · exact hv ((KLleafPar_spec hF hr).1.mono h)
  · have hroot : v.val = n - 1 := by have := v.isLt; omega
    rw [KLleafPar_root F hroot] at h
    exact KLnot_arcLe_wholeP hF hJ h

include hn in
theorem KLnodePar_arcLe {d : Fin n × Fin n} (hd : d ∈ F) (hdJ : KLArcLe d J) (hne : d ≠ J) :
    KLArcLe (KLnodePar F d) J :=
  (KLnodePar_spec hF hn (KLmem_nodes_of_mem hd) (KLne_wholeP hF hd)).2.2.2 J (KLmem_nodes_of_mem hJ) hdJ
    (Ne.symm hne)

include hn in
omit hJ in
theorem KLnot_arcLe_nodePar {d : Fin n × Fin n} (hd : d ∈ F) (hdJ : ¬KLArcLe d J) :
    ¬KLArcLe (KLnodePar F d) J := fun h =>
  hdJ ((KLnodePar_spec hF hn (KLmem_nodes_of_mem hd) (KLne_wholeP hF hd)).2.1.trans h)

include hn in
theorem KLnot_arcLe_nodePar_self : ¬KLArcLe (KLnodePar F J) J := by
  obtain ⟨-, h1, h2, -⟩ := KLnodePar_spec hF hn (KLmem_nodes_of_mem hJ) (KLne_wholeP hF hJ)
  exact fun h => h2 (h.antisymm h1)

end Side

end LaminarAPI

/-! ### `Σ^{(∅)}` is symmetric: port of `RBM2D/Loop/Kcal.lean:498-526, 758-776` -/

section SigmaSymm

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- Reflection invariance of `Θ_ξ`: `(Θ_ξ)_{x-p, x-q} = (Θ_ξ)_{pq}` (properties 1-2).
Port of `RBM2D/Loop/Kcal.lean:498-507` (`Theta_reflect`). -/
theorem KLTheta_reflect (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (x p q : Zd d L) :
    Theta d L g ξ (x - p) (x - q) = Theta d L g ξ p q := by
  have h1 := Theta_apply_add_right_of_three_le (g := g) hL hξ q p (x - p - q)
  have e1 : q + (x - p - q) = x - p := by abel
  have e2 : p + (x - p - q) = x - q := by abel
  rw [e1, e2] at h1
  rw [h1]
  have h2 := congrFun (congrFun (Theta_transpose_of_three_le (g := g) hL hξ) p) q
  simpa [Matrix.transpose_apply] using h2

/-- Reflection of the self-energy of one tree.  Port of `RBM2D/Loop/Kcal.lean:509-525`. -/
theorem KLselfW_reflect {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (x : Zd d L)
    (hE : ∀ e p q, E e (x - p) (x - q) = E e p q) (δ : Fin n → Zd d L) :
    KLselfW d L F E (fun i => x - δ i) = KLselfW d L F E δ := by
  unfold KLselfW
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ => Equiv.subLeft x) _ _ fun b => ?_
  simp only [Equiv.piCongrRight_apply]
  congr 1
  · refine Finset.prod_congr rfl fun v _ => ?_
    have hiff : ∀ y : Zd d L, (x - δ v = y) ↔ (δ v = x - y) := fun y => by
      constructor
      · intro h; rw [← h, sub_sub_cancel]
      · intro h; rw [h, sub_sub_cancel]
    simp only [hiff]
    rfl
  · refine Finset.prod_congr rfl fun e _ => ?_
    exact (hE _ _ _).symm

/-- **The symmetry `g(s) = g(-s)`** (`3-4_properties-k-g.tex:95` of `[YY_25]`'s RBM2D port) for every
`σ`: `Σ^{(∅)}(t, σ, d₁ + s) = Σ^{(∅)}(t, σ, d₁ - s)` when `s₀ = 0`.  Port of
`RBM2D/Loop/Kcal.lean:759-777` (`SigmaPi_empty_symm`), with the factor `∏ m` inside `KLSigmaPi`. -/
theorem KLSigmaPi_empty_symm (hL : 3 ≤ L) {E : ℝ} (hE : |E| < 2) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) {n : ℕ} [NeZero n] (σ : Fin n → Bool) (d₁ : Zd d L)
    (s : Fin n → Zd d L) (_ : s 0 = 0) :
    KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ + s i)
      = KLSigmaPi d L g (mSigma E) t σ ∅ (fun i => d₁ - s i) := by
  have hE2 : |E| ≤ 2 := hE.le
  have hx : (fun i => d₁ - s i) = fun i => (d₁ + d₁) - (d₁ + s i) :=
    funext fun i => by abel
  rw [hx]
  unfold KLSigmaPi
  congr 1
  refine Finset.sum_congr rfl fun F _ => ?_
  refine (KLselfW_reflect d L F _ (d₁ + d₁) (fun e p q => ?_) (fun i => d₁ + s i)).symm
  have hξ : ‖(t : ℂ) * (mSigma E (σ e.1.1) * mSigma E (σ e.1.2))‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 ht.1 ht.2 _ _
  simp only [Matrix.sub_apply, Matrix.one_apply, sub_right_inj, thetaEdge,
    KLTheta_reflect d L g hL hξ]

end SigmaSymm

/-! ## 7. Kernel-generic successors of `treeEqRhs`, `MLoop`, `IsKLoop` (gate BA)

The merged `treeEqRhs`, `MLoop`, `IsKLoop` (`RBM3D/Loop/TreeRep.lean:142-165`) hard-wire
`S = SB d L g` and the initial data `M^{(k)} = W^{-(k-1)d} ∏ m 1(a₁ = … = a_k)`; they are frozen.
The successors below take any kernel `S` and any initial data `M`, and the equalities with the
merged ones are proved. -/

section KernelGeneric

variable (d L : ℕ) [NeZero L] (W : ℕ)

/-- `treeEqRhs` for an arbitrary kernel `S` in place of `S^{(B)}`:
`W^d Σ_{1≤k<l≤n} Σ_{a,b} K(cutL^{(a)}_{k,l}) S_{ab} K(cutR^{(b)}_{k,l})`. -/
noncomputable def treeEqRhsS (S : Matrix (Zd d L) (Zd d L) ℂ) (K : LoopIdx (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  ((W : ℂ) ^ d) * ∑ k ∈ Icc 1 I.length, ∑ l ∈ Ioc k I.length,
    ∑ a : Zd d L, ∑ b : Zd d L,
      K (I.cutGlueL k l a) * S a b * K (I.cutGlueR k l b)

/-- The initial data of the random band matrix model with a free label profile `R`:
`W^{-(k-1)d} ∏ m(σ_i) · R(σ, a)`.  `MLoop` is the case `R = 1(a₁ = … = a_k)`
(`KLMLoop_eq_MLoopM`). -/
noncomputable def MLoopM (m : Bool → ℂ) (R : List Bool → List (Zd d L) → ℂ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) * (I.σ.map m).prod * R I.σ I.a

/-- The label profile `1(a₁ = … = a_k)` of the model `MLoop`. -/
def KLallEq : List Bool → List (Zd d L) → ℂ :=
  fun _ a => if ∀ x ∈ a, ∀ y ∈ a, x = y then 1 else 0

/-- `IsKLoop` for an arbitrary kernel `S` and arbitrary initial data `M` (a value on every
loop index), the one-loop value `m` as before. -/
def IsKLoopS (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) (M : LoopIdx (Zd d L) → ℂ)
    (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length →
      HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t) ∧
  (∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K 0 I = M I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = m s)

variable (g : ℝ)

/-- `treeEqRhs` is `treeEqRhsS` at the kernel `S^{(B)}`. -/
theorem treeEqRhs_eq_treeEqRhsS (K : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) :
    treeEqRhs d L W g K I = treeEqRhsS d L W (SB d L g) K I := rfl

/-- `MLoop` is `MLoopM` at the profile `1(a₁ = … = a_k)`. -/
theorem KLMLoop_eq_MLoopM (m : Bool → ℂ) :
    MLoop d L W m = MLoopM d L W m (KLallEq d L) := rfl

/-- `IsKLoop` is `IsKLoopS` at the kernel `S^{(B)}` and the initial data `MLoop`. -/
theorem IsKLoop_iff_IsKLoopS (m : Bool → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) :
    IsKLoop d L W g m T K ↔ IsKLoopS d L W (SB d L g) m (MLoopM d L W m (KLallEq d L)) T K :=
  Iff.rfl

end KernelGeneric

/-! ## 8. The instances: `d = 3`, `L = 5`, `W = 2`, `g = λ = 1/2`, `E = 0`, `t = 9/10` -/

section Instances
/-- The instance data: `L = 5` (`125` blocks), `W = 2` (`N = (WL)^3 = 1000`), `g = 1/2`
(`W^{-3/2} ≤ g ≤ 𝔡⁻¹` for `𝔡 ≤ 1/2`), `E = 0` (`m(+) = i`), `t = 9/10`, `κ = gmax = 1`. -/
noncomputable def KLinstPar : KLPar 1 1 where
  L := 5
  W := 2
  hL := by norm_num
  hW := by norm_num
  g := 1 / 2
  hg0 := by norm_num
  hg1 := by norm_num
  E := 0
  hE := by norm_num
  t := 9 / 10
  ht0 := by norm_num
  ht1 := by norm_num

/-- A nondegenerate loop: charges `(+,-,+)`, labels three distinct blocks of `Z_5^3`. -/
def KLinstσ : Fin 3 → Bool := ![true, false, true]

def KLinsta : Fin 3 → Zd 3 5 := ![0, 1, 2]

/-- The scales at the instance data: `η_t = 1/10`,
`B_{t,0} = 514/175 = 2.9371`. -/
theorem KLinst_scales :
    Gauss.etaT 0 (9 / 10) = 1 / 10 ∧ Bparam 3 5 (1 / 2) (9 / 10) 0 = 514 / 175 := by
  refine ⟨?_, ?_⟩
  · have : mE 0 = Complex.I := by
      simp only [mE]
      have h : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
        rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h]; push_cast; simp
    rw [Gauss.etaT, this]; norm_num
  · norm_num [Bparam, abs_of_pos]

/-- `(Kn2sol)` at the instance data. -/
theorem KLinst_two :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, 1]⟩
      = ((2 : ℂ) ^ 3)⁻¹ * (mSigma 0 true * mSigma 0 false)
          * Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 1 := by
  simpa using KLK_two 3 5 (1 / 2) 2 0 (9 / 10) true false 0 1

/-- `(Kn3sol)` at the instance data. -/
theorem KLinst_three :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false, true], [0, 1, 2]⟩
      = (((2 : ℂ) ^ 3)⁻¹) ^ 2 * (mSigma 0 true * mSigma 0 false * mSigma 0 true) *
          ∑ b : Zd 3 5,
            Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false)) 0 b *
              Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 false * mSigma 0 true)) 1 b *
                Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true)) 2 b := by
  simpa using KLK_three 3 5 (1 / 2) 2 0 (9 / 10) true false true 0 1 2

/-- `(WI_calK)` at `n = 2`, proved: `s = +`, `a₁ = 0`. -/
theorem KLinst_ward_two :
    ∑ x : Zd 3 5, KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (Gauss.etaT 0 (9 / 10) : ℂ))⁻¹ *
          (KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ - KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[false], [0]⟩) := by
  simpa using KLward_two 3 5 (1 / 2) (by norm_num) 2 (by norm_num) (E := 0) (by norm_num)
    (t := 9 / 10) ⟨by norm_num, by norm_num⟩ true 0

/-- `(eq_K-Kpi)` at `n = 4` for `σ = (+,-,+,-)`: three trees, `π ∈ {∅, {(0,2)}, {(1,3)}, …}`. -/
theorem KLinst_Kpi :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])
      = (((2 : ℂ) ^ 3)⁻¹) ^ 3 * ∑ π ∈ (diagonals 4).powerset,
          KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ![0, 1, 2, 3] π := by
  simpa using KLK_eq_sum_Kpi 3 5 (1 / 2) 2 0 (9 / 10) (n := 4) (by norm_num)
    ![true, false, true, false] ![0, 1, 2, 3]

/-- `(eq:K-Kpi)`-first stage `K^{(π)} = Σ_δ Σ^{(π)} ∏ Θ` at `n = 4`, `σ = (+,-,+,-)`, `π = ∅`. -/
theorem KLinst_Kpi_SigmaPi :
    KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ![0, 1, 2, 3] ∅
      = ∑ δ : Fin 4 → Zd 3 5,
          KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, false, true, false] ∅ δ *
            ∏ v, thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (![true, false, true, false] v)
              (![true, false, true, false] (v + 1)) (![0, 1, 2, 3] v) (δ v) :=
  KLKpi_eq_sum_SigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) _ _ ∅

/-- `Σ^{(∅)}` symmetry at `n = 3`, `σ = (+,-,+)`, `d₁ = 1`, `s = (0,1,2)`: the two arguments
`d₁ + s` and `d₁ - s` are different label vectors. -/
theorem KLinst_SigmaPi_symm :
    KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun i => (1 : Zd 3 5) + KLinsta i)
      = KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLinstσ ∅ (fun i => (1 : Zd 3 5) - KLinsta i) :=
  KLSigmaPi_empty_symm 3 5 (1 / 2) (by norm_num) (E := 0) (by norm_num)
    (t := 9 / 10) ⟨by norm_num, by norm_num⟩ KLinstσ 1 KLinsta rfl

/-- `treeEqRhs = treeEqRhsS (SB d L g)` for `K = 𝒦` at the instance data, on the `3`-loop. -/
theorem KLinst_treeEqRhsS :
    treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 KLinstσ KLinsta)
      = treeEqRhsS 3 5 2 (SB 3 5 (1 / 2)) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 KLinstσ KLinsta) :=
  treeEqRhs_eq_treeEqRhsS 3 5 2 (1 / 2) _ _

/-- `MLoop = MLoopM` at the instance data (`m = mSigma 0`, `W = 2`) on the `3`-loop. -/
theorem KLinst_MLoopM :
    MLoop 3 5 2 (mSigma 0) (KLloopOf 3 5 KLinstσ KLinsta)
      = MLoopM 3 5 2 (mSigma 0) (KLallEq 3 5) (KLloopOf 3 5 KLinstσ KLinsta) :=
  congrFun (KLMLoop_eq_MLoopM 3 5 2 (mSigma 0)) _

/-- `IsKLoop ↔ IsKLoopS` for the family `𝒦` on `T = [0,1)` at the instance data
(the left side is `KLisKLoopPin` of ticket KL3, not proved here). -/
theorem KLinst_IsKLoopS :
    IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I)
      ↔ IsKLoopS 3 5 2 (SB 3 5 (1 / 2)) (mSigma 0) (MLoopM 3 5 2 (mSigma 0) (KLallEq 3 5))
          (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  IsKLoop_iff_IsKLoopS 3 5 2 (1 / 2) (mSigma 0) _ _

/-- `𝒦^{(1)} = m(σ)` and `𝒦^{(2)} = kTwo` at the instance data. -/
theorem KLinst_one_two_kTwo :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ = mSigma 0 true ∧
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true, false], [0, 1]⟩
      = kTwo 3 5 2 (1 / 2) (mSigma 0) (9 / 10) true false 0 1 :=
  ⟨KLK_one 3 5 (1 / 2) 2 0 (9 / 10) true 0, KLK_two_eq_kTwo 3 5 (1 / 2) 2 0 (9 / 10) true false 0 1⟩

/-- `KLgen` on `KLloopOf` is the tree sum at `n = 4` (alternating charges). -/
theorem KLinst_gen_loopOf :
    KLgen 3 5 (1 / 2) 2 (mSigma 0) (9 / 10) (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])
      = KLn 3 5 (1 / 2) 2 (mSigma 0) (9 / 10) 4 ![true, false, true, false] ![0, 1, 2, 3] :=
  KLgen_loopOf 3 5 (1 / 2) 2 (mSigma 0) (9 / 10) (by norm_num) _ _

end Instances

end RBM.Loop
