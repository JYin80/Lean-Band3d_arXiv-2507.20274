/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KCactus
import RBM3D.BA.KBase
import RBM3D.BA.Ward
import RBM3D.Loop.KLTree
import RBM3D.Loop.TreeRep

/-!
# Stage K, row K05a: the derivative of the cactus value and its leaf part

Ticket T2370 (design BA-DK, `docs/reports/T2360-design.md` §3 (a), §4 row K05a; supervisor
`docs/supervisor/2026-10-10-0350.md` C1-C3).  The cactus value `Γ_M(F) = BAGamma` of K04
(`BA/KCactus.lean`) is an instance of the generic tree value `KLgval`
(`Loop/KLCut.lean:58`): a finite sum of finite products.  Here:

1. The four pins `BASplicedFam`, `BAGammaDerivRHS`, `BAGammaDerivStmt`, `BALeafPairsStmt`.
2. **`baGamma_hasDerivAt`** (target 2): `∂_t Γ_F` is the sum of the leaf terms and the chord terms
   of `BAGammaDerivRHS`.  Product rule on `KLgval` (`BAKTreeDeriv_gval_hasDerivAt`, the `KLgval`
   form of the merged `KLhasDerivAt_treeValW`, `Loop/KLCut.lean:178`); a leaf weight
   `Θ^{(σ_v,σ_{v+1})}` has derivative `ΘMΘ` (`BATheta_hasDerivAt`) and
   `(ΘMΘ)(a_v, ·) = Σ_b (ΘM)(a_v, b) Θ(b, ·)` (`BAKTreeDeriv_gval_leaf_mul`, the `KLgval` form of
   `treeValW_leaf_mul`, `Loop/KLTreeDeriv.lean:168`); a chord weight `tΘ` has derivative
   `Θ + tΘMΘ = Θ·Θ` (`BATheta_resolvent`); an `M`-edge weight is constant, so the term with that
   weight replaced by `0` vanishes.
3. **`baLeafPairs`** (target 3): the leaf part of `W^{-d(n-1)} Σ_F ∂_tΓ_F` is the sum of the `n`
   leaf pairs of `treeEqRhsS` at `S = 1`, for every family with `BASplicedFam`: the pair
   `(v+1, v+2)` for the leaf `v ≤ n-2` (its 2-piece is `(Kn2sol)`, the closed form of
   `BASplicedFam`, never `BAGamma` at `n = 2`: supervisor 0350 C1) and the wrap pair `(1, n)` for
   the leaf `v = n-1`, whose 2-piece is read from the other end (C2): `Θ^{(σ',σ)} M^{(σ'σ)}`
   is the transpose of `Θ^{(σσ')} M^{(σσ')}` (`BAKTreeDeriv_P_swap`; `M^{(σ'σ)} = (M^{(σσ')})ᵀ`
   from the definition of `BAMss`, `ΘM = MΘ` from the resolvent identities).  The list facts
   `KLloopOf_cutGlue*` are public.  No hypothesis `0 < W` is needed: at `W^d = 0` both sides
   vanish (`n - 1 ≥ 2`).
4. **`BAKcac`**, `BAKcac_spliced`: the spliced family of supervisor 0350 C1 (length 1: `PropSpin m`;
   length 2: the closed form `(Kn2sol)`; length `≥ 3`: `W^{-d(n-1)} Σ_{F ∈ TSP n} BAGamma`;
   `0` on loops with `σ.length ≠ a.length`), with `BASplicedFam`.  K05b proves `IsKLoopS` for it.

Public: the four pins, `baGamma_hasDerivAt`, `baLeafPairs`, `BAKcac`, `BAKcac_spliced`, the four
`KLloopOf_cutGlue*` facts and the instances (section 7).  Every other helper is `private` with the
stem `BAKTreeDeriv_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 0. The pins (copied verbatim from Part 1 of `docs/tickets/checks/T2370-check.lean`) -/

/-- **`BASplicedFam`** (supervisor 0350 C1): the K05b witness family. Length 1: `PropSpin m`. Length 2: the closed form
`(Kn2sol)` (`1_2:1175`; the 2-loop is not a cactus). Length `n ≥ 3`: the cactus sum `W^{-d(n-1)} ∑_{F ∈ TSP n} BAGamma`. -/
def BASplicedFam (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ (t : ℝ) (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = PropSpin m s) ∧
  (∀ (t : ℝ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L),
    K t ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂) ∧
  (∀ (t : ℝ) (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
    K t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a)

/-- **`BAGammaDerivRHS`**: `∂_t Γ_F`. A leaf `v` carries `Θ → ΘMΘ`, written as `Σ_b (ΘM^{(σ_vσ_{v+1})})(a_v, b) Γ_F(a_v ← b)`.
A chord `J` carries `tΘ → Θ²` (`∂_t(tΘ) = Θ + tΘMΘ = Θ²`, `BATheta_resolvent`), written as the cactus `KLgval` with the
weight of the edge `Sum.inl J` replaced. -/
noncomputable def BAGammaDerivRHS (d L n : ℕ) [NeZero L] [NeZero n] (g E : ℝ) (m : ℂ) (t : ℝ)
    (F : Finset (Fin n × Fin n)) (σ : Fin n → Bool) (a : Fin n → Zd d L) : ℂ :=
  (∑ v : Fin n, ∑ b : Zd d L,
      (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
        BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)) +
  ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
      (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) (BAslotLeaf F)
      (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ) (Sum.inl J)
        (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
      (BACactusValSrc F) (BACactusValTgt F)

/-- **`BAGammaDerivStmt`** (target 2): the derivative of every cactus value at the BA data, `0 ≤ t < 1`. -/
def BAGammaDerivStmt (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (n : ℕ) [NeZero n] (g κ E : ℝ) (m : ℂ), 3 ≤ n → BAReal d L g κ E m →
    ∀ (F : Finset (Fin n × Fin n)), KLIsTSP F → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      HasDerivAt (fun s : ℝ => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) s F σ a)
        (BAGammaDerivRHS d L n g E m t F σ a) t

/-- **`BALeafPairsStmt`** (target 3; supervisor 0350 Q1 table, C1, C2): for every family with `BASplicedFam`, the leaf part of
`W^{-d(n-1)} Σ_F ∂_tΓ_F` equals the `n` leaf pairs of `treeEqRhsS` at `S = 1`: the pair `(v+1, v+2)` for `v ≤ n-2` and the
wrap pair `(1, n)` for `v = n-1` (whose 2-piece is reversed; C2). -/
def BALeafPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ v : Fin n, ∑ b : Zd d L,
          (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
            BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)
        = ∑ v : Fin n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
              (KLloopOf d L σ a))

/-! ## 1. Matrix facts: the wrap pair -/

section Mat

variable {d L : ℕ} [NeZero L]

omit [NeZero L] in
/-- `M^{(σ₂,σ₁)} = (M^{(σ₁,σ₂)})ᵀ` for every `M` (only commutativity of `ℂ`). -/
private theorem BAKTreeDeriv_Mss_swap (B : Matrix (Zd d L) (Zd d L) ℂ) (s s' : Bool) :
    BAMss d L B s' s = (BAMss d L B s s')ᵀ := by
  ext a b
  simp only [BAMss, Matrix.of_apply, Matrix.transpose_apply, mul_comm]

/-- `Θ^{(σ₂,σ₁)} = (Θ^{(σ₁,σ₂)})ᵀ`, no hypothesis (`Ring.inverse` commutes with `ᵀ`). -/
private theorem BAKTreeDeriv_Theta_swap (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) :
    BATheta d L g E m t s' s = (BATheta d L g E m t s s')ᵀ := by
  unfold BATheta PropThetaQ
  rw [BAKTreeDeriv_Mss_swap, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]

/-- `Θ M^{(σσ')} = M^{(σσ')} Θ` at `0 ≤ t < 1` (the two resolvent identities `BATheta_resolvent`). -/
private theorem BAKTreeDeriv_Theta_comm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (s s' : Bool) :
    BATheta d L g E m t s s' * BAMss d L (BAMB d L g (E : ℂ) m) s s' =
      BAMss d L (BAMB d L g (E : ℂ) m) s s' * BATheta d L g E m t s s' := by
  obtain ⟨h1, h2⟩ := BATheta_resolvent d L g κ E m hr t ht0 ht1 s s'
  by_cases ht : (t : ℂ) = 0
  · rw [ht, zero_smul, add_zero] at h1
    rw [h1, Matrix.mul_one, Matrix.one_mul]
  · have h3 : (t : ℂ) • (BATheta d L g E m t s s' * BAMss d L (BAMB d L g (E : ℂ) m) s s') =
        (t : ℂ) • (BAMss d L (BAMB d L g (E : ℂ) m) s s' * BATheta d L g E m t s s') :=
      add_left_cancel (h2.symm.trans h1)
    exact smul_right_injective _ ht h3

/-- **The wrap pair** (supervisor 0350 C2): `(Θ^{(σ',σ)} M^{(σ'σ)})(x, y) = (Θ^{(σσ')} M^{(σσ')})(y, x)`.
Hypotheses: `BAReal`, `0 ≤ t < 1`; the symmetry of `M(σ)` is not used. -/
private theorem BAKTreeDeriv_P_swap (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (s s' : Bool) (x y : Zd d L) :
    (BATheta d L g E m t s' s * BAMss d L (BAMB d L g (E : ℂ) m) s' s) x y =
      (BATheta d L g E m t s s' * BAMss d L (BAMB d L g (E : ℂ) m) s s') y x := by
  rw [BAKTreeDeriv_Theta_swap, BAKTreeDeriv_Mss_swap, ← Matrix.transpose_mul, Matrix.transpose_apply,
    ← BAKTreeDeriv_Theta_comm g κ E m hr ht0 ht1 s s']

end Mat

/-! ## 2. The product rule for `KLgval` -/

section Generic

variable {d L : ℕ} [NeZero L] {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [DecidableEq Lf]
  [Fintype Ed] [DecidableEq Ed]

/-- **The product rule for `KLgval`**: the derivative of the value of a weighted tree has one term per leaf weight and one
per edge weight (the `KLgval` form of `KLhasDerivAt_treeValW`, `Loop/KLCut.lean:178`). -/
private theorem BAKTreeDeriv_gval_hasDerivAt (a : Lf → Zd d L) (p : Lf → Nd) (c q : Ed → Nd)
    {M : ℝ → Lf → Matrix (Zd d L) (Zd d L) ℂ} {Ew : ℝ → Ed → Matrix (Zd d L) (Zd d L) ℂ}
    {M' : Lf → Matrix (Zd d L) (Zd d L) ℂ} {Ew' : Ed → Matrix (Zd d L) (Zd d L) ℂ} {t : ℝ}
    (hM : ∀ ℓ i j, HasDerivAt (fun r => M r ℓ i j) (M' ℓ i j) t)
    (hE : ∀ e i j, HasDerivAt (fun r => Ew r e i j) (Ew' e i j) t) :
    HasDerivAt (fun r => KLgval d L a (M r) p (Ew r) c q)
      (∑ ℓ, KLgval d L a (Function.update (M t) ℓ (M' ℓ)) p (Ew t) c q
        + ∑ e, KLgval d L a (M t) p (Function.update (Ew t) e (Ew' e)) c q) t := by
  unfold KLgval
  refine (HasDerivAt.fun_sum fun b _ =>
    (HasDerivAt.fun_finsetProd fun ℓ _ => hM ℓ _ _).mul
      (HasDerivAt.fun_finsetProd fun e _ => hE e _ _)).congr_deriv ?_
  conv_rhs => arg 1; rw [Finset.sum_comm]
  conv_rhs => arg 2; rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [KLprod_update_eq (fun w => M t w (a w) (b (p w))) _ ℓ
      (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, smul_eq_mul]
    ring
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [KLprod_update_eq (fun e => Ew t e (b (c e)) (b (q e))) _ e
      (fun e' he => by rw [Function.update_of_ne he]), Function.update_self, smul_eq_mul]
    ring

omit [DecidableEq Ed] in
/-- **Linearity in one leaf weight** (the `KLgval` form of `treeValW_leaf_mul`, `Loop/KLTreeDeriv.lean:168`): the leaf `v`
with weight `A B` gives `∑_z A_{a_v z}` times the tree with the leaf relabelled `z` and weight `B`. -/
private theorem BAKTreeDeriv_gval_leaf_mul (a : Lf → Zd d L) (M : Lf → Matrix (Zd d L) (Zd d L) ℂ)
    (p : Lf → Nd) (Ew : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) (v : Lf)
    (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    KLgval d L a (Function.update M v (A * B)) p Ew c q
      = ∑ z : Zd d L, A (a v) z * KLgval d L (Function.update a v z) (Function.update M v B) p Ew c q := by
  simp only [KLgval, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [KLprod_update_eq (fun w => M w (a w) (b (p w))) _ v
    (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, Matrix.mul_apply,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [KLprod_update_eq (fun w => M w (a w) (b (p w))) _ v
    (fun w hw => by rw [Function.update_of_ne hw, Function.update_of_ne hw]),
    Function.update_self, Function.update_self]
  ring

omit [DecidableEq Lf] in
/-- A zero edge weight kills the value. -/
private theorem BAKTreeDeriv_gval_zero_edge (a : Lf → Zd d L) (M : Lf → Matrix (Zd d L) (Zd d L) ℂ)
    (p : Lf → Nd) (Ew : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) (e : Ed) :
    KLgval d L a M p (Function.update Ew e 0) c q = 0 := by
  unfold KLgval
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp), mul_zero]

end Generic

/-! ## 3. Target 2: `baGamma_hasDerivAt` -/

section Deriv

variable {d L : ℕ} [NeZero L]

/-- `ΘΘ = Θ + tΘMΘ` (the first conjunct `Θ = 1 + tMΘ` of `BATheta_resolvent` multiplied by `Θ` on the left). -/
private theorem BAKTreeDeriv_ThetaSq (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂ =
      BATheta d L g E m t σ₁ σ₂ + (t : ℂ) • (BATheta d L g E m t σ₁ σ₂ *
        BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂) := by
  have h1 := (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
  calc BATheta d L g E m t σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂
      = BATheta d L g E m t σ₁ σ₂ * (1 + (t : ℂ) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
          BATheta d L g E m t σ₁ σ₂)) := by rw [← h1]
    _ = _ := by rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc]

/-- A chord weight `tΘ`: `∂_t (tΘ) = Θ + tΘMΘ = ΘΘ`, entrywise. -/
private theorem BAKTreeDeriv_hasDerivAt_chord (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) (i j : Zd d L) :
    HasDerivAt (fun r : ℝ => ((r : ℂ) • BATheta d L g E m r σ₁ σ₂) i j)
      ((BATheta d L g E m t σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂) i j) t := by
  have h := ((hasDerivAt_id t).ofReal_comp).mul (BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₁ σ₂ i j)
  simp only [Matrix.smul_apply, smul_eq_mul]
  refine h.congr_deriv ?_
  rw [BAKTreeDeriv_ThetaSq g κ E m hr ht0 ht1 σ₁ σ₂]
  simp [Matrix.add_apply, Matrix.smul_apply]

/-- **Target 2** (`BAGammaDerivStmt`): `∂_t Γ_F` for `F` crossing-free at `0 ≤ t < 1`, the BA data `BAReal`.  The proof
is the product rule on the cactus `KLgval`: a leaf weight `Θ^{(σ_v,σ_{v+1})}` has derivative `ΘMΘ`, rewritten as
`∑_b (ΘM)(a_v, b) Γ_F(a_v ← b)`; a chord weight `tΘ` has derivative `Θ·Θ`; an `M`-edge weight is constant.
Hypotheses beyond the pin: none (`KLIsTSP F` and `3 ≤ n` are not used). -/
theorem baGamma_hasDerivAt (d : ℕ) : BAGammaDerivStmt d := by
  intro L _ n _ g κ E m hn hr F hF σ a t ht0 ht1
  have hE : ∀ (e : ↥F ⊕ BAslot F) (i j : Zd d L),
      HasDerivAt (fun r : ℝ => BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) r F σ e i j)
        ((Sum.elim (fun J : ↥F => BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2))
          (fun _ : BAslot F => (0 : Matrix (Zd d L) (Zd d L) ℂ)) e) i j) t := by
    rintro (J | s) i j
    · exact BAKTreeDeriv_hasDerivAt_chord g κ E m hr ht0 ht1 (σ J.1.1) (σ J.1.2) i j
    · exact hasDerivAt_const t _
  have key := BAKTreeDeriv_gval_hasDerivAt (d := d) (L := L) a (BAslotLeaf F) (BACactusValSrc F)
    (BACactusValTgt F) (M := fun r => BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) r σ)
    (Ew := fun r => BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) r F σ)
    (M' := fun ℓ => BATheta d L g E m t (σ ℓ) (σ (ℓ + 1)) *
      BAMss d L (BAMB d L g (E : ℂ) m) (σ ℓ) (σ (ℓ + 1)) * BATheta d L g E m t (σ ℓ) (σ (ℓ + 1)))
    (t := t)
    (fun ℓ i j => BATheta_hasDerivAt d L g κ E m hr ht0 ht1 (σ ℓ) (σ (ℓ + 1)) i j) hE
  refine key.congr_deriv ?_
  unfold BAGammaDerivRHS
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [BAKTreeDeriv_gval_leaf_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hB : Function.update (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) v
        (BATheta d L g E m t (σ v) (σ (v + 1))) =
        BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ := Function.update_eq_self v _
    rw [hB]
    rfl
  · have h0 : ∀ s : BAslot F, KLgval d L a (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ)
        (BAslotLeaf F) (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ)
          (Sum.inr s) 0) (BACactusValSrc F) (BACactusValTgt F) = 0 := fun s =>
      BAKTreeDeriv_gval_zero_edge _ _ _ _ _ _ _
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, h0, Finset.sum_const_zero, add_zero]

end Deriv

/-! ## 4. The list facts: `KLloopOf` against `cutGlueL`, `cutGlueR` -/

section Lists

variable {d L : ℕ}

/-- `List.ofFn` of an updated function (`List.set`). -/
private theorem BAKTreeDeriv_ofFn_update {α : Type*} {n : ℕ} (a : Fin n → α) (v : Fin n) (x : α) :
    List.ofFn (Function.update a v x) = (List.ofFn a).take v ++ x :: (List.ofFn a).drop (v + 1) := by
  have h := List.set_eq_take_append_cons_drop (l := List.ofFn a) (i := v.val) (a := x)
  have hv : v.val < (List.ofFn a).length := by simp
  simp only [hv, ↓reduceIte] at h
  rw [← h]
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_set, Function.update_apply]
  by_cases hi : i = v.val
  · subst hi
    simp
  · have : ¬ (⟨i, by simpa using h1⟩ : Fin n) = v := fun h => hi (by rw [← h])
    simp [this, Ne.symm hi]

/-- **The `n`-loop piece of the cut `(v+1, v+2)`** (leaf pair, `v ≤ n-2`): `cutGlueL` keeps `σ` and replaces `a_v` by `x`
(the identity needs no hypothesis on `v`). -/
theorem KLloopOf_cutGlueL_leaf {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueL (v.val + 1) (v.val + 2) x = KLloopOf d L σ (Function.update a v x) := by
  simp only [LoopIdx.cutGlueL, KLloopOf, show v.val + 2 - 1 = v.val + 1 by omega,
    show v.val + 1 - 1 = v.val by omega, List.take_append_drop, BAKTreeDeriv_ofFn_update]

/-- **The 2-loop piece of the cut `(v+1, v+2)`** (leaf pair, `v ≤ n-2`): `cutGlueR` is `⟨[σ_v, σ_{v+1}], [a_v, x]⟩`. -/
theorem KLloopOf_cutGlueR_leaf {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 < n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueR (v.val + 1) (v.val + 2) x = ⟨[σ v, σ (v + 1)], [a v, x]⟩ := by
  have hv1 : (v + 1 : Fin n) = ⟨v.val + 1, hv⟩ := Fin.ext (by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hv])
  simp only [LoopIdx.cutGlueR, KLloopOf, show v.val + 1 - 1 = v.val by omega,
    show v.val + 2 - (v.val + 1) = 1 by omega, hv1]
  refine LoopIdx.ext ?_ ?_
  · change List.take (1 + 1) (List.drop (↑v) (List.ofFn σ)) = [σ v, σ ⟨↑v + 1, hv⟩]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp
  · change List.take 1 (List.drop (↑v) (List.ofFn a)) ++ [x] = [a v, x]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i <;> simp

/-- **The 2-loop piece of the wrap cut `(1, n)`** (`v = n-1`): `cutGlueL` is `⟨[σ_0, σ_{n-1}], [x, a_{n-1}]⟩`, the 2-loop
read from the other end. -/
theorem KLloopOf_cutGlueL_wrap {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 = n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueL 1 n x = ⟨[σ 0, σ v], [x, a v]⟩ := by
  simp only [LoopIdx.cutGlueL, KLloopOf, Nat.sub_self, List.take_zero, List.nil_append]
  refine LoopIdx.ext ?_ ?_
  · change List.take 1 (List.ofFn σ) ++ List.drop (n - 1) (List.ofFn σ) = [σ 0, σ v]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i
    · rw [List.getElem_append_left (by simp; omega)]; simp
    · simp only [List.length_take, List.length_ofFn, min_le_iff, Std.le_refl, true_or, List.getElem_append_right,
        List.getElem_drop, List.getElem_ofFn, List.getElem_cons_succ, List.getElem_cons_zero]
      congr 1; exact Fin.ext (by simp; omega)
  · change x :: List.drop (n - 1) (List.ofFn a) = [x, a v]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : i < 2 := by simpa using h2
    interval_cases i
    · simp
    · simp only [List.getElem_cons_succ, List.getElem_drop, add_zero, List.getElem_ofFn, List.getElem_cons_zero]
      congr 1; exact Fin.ext (by simp; omega)

/-- **The `n`-loop piece of the wrap cut `(1, n)`** (`v = n-1`): `cutGlueR` keeps `σ` and replaces `a_{n-1}` by `x`. -/
theorem KLloopOf_cutGlueR_wrap {n : ℕ} (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n)
    (hv : v.val + 1 = n) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueR 1 n x = KLloopOf d L σ (Function.update a v x) := by
  simp only [LoopIdx.cutGlueR, KLloopOf, Nat.sub_self, List.drop_zero, BAKTreeDeriv_ofFn_update]
  refine LoopIdx.ext ?_ ?_
  · change List.take (n - 1 + 1) (List.ofFn σ) = List.ofFn σ
    rw [show n - 1 + 1 = n by omega]
    simp
  · change List.take (n - 1) (List.ofFn a) ++ [x] =
      List.take (v : ℕ) (List.ofFn a) ++ x :: List.drop ((v : ℕ) + 1) (List.ofFn a)
    rw [show (v : ℕ) = n - 1 by omega, show n - 1 + 1 = n by omega]
    simp

end Lists

/-! ## 5. The spliced family `BAKcac` -/

section Kcac

variable (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

/-- **`BAKcac`**, the spliced family of supervisor 0350 C1 (`BASplicedFam`): on a loop with `σ.length = a.length`, length 1
is `PropSpin m`, length 2 the closed form `(Kn2sol)`, length `n ≥ 3` the cactus sum `W^{-d(n-1)} ∑_{F ∈ TSP n} BAGamma` over
the `Fin n` view of the lists (`getD`; at `I = KLloopOf σ a` the view is `(σ, a)`, `BAKcac_spliced`); `0` otherwise. -/
noncomputable def BAKcac (t : ℝ) (I : LoopIdx (Zd d L)) : ℂ :=
  if I.σ.length = I.a.length then
    if I.a.length = 1 then PropSpin m (I.σ.getD 0 false)
    else if I.a.length = 2 then
      (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t (I.σ.getD 0 false) (I.σ.getD 1 false) *
        BAMss d L (BAMB d L g (E : ℂ) m) (I.σ.getD 0 false) (I.σ.getD 1 false)) (I.a.getD 0 0) (I.a.getD 1 0)
    else if h : 3 ≤ I.a.length then
      haveI : NeZero I.a.length := ⟨by omega⟩
      (((W : ℂ) ^ d)⁻¹) ^ (I.a.length - 1) * ∑ F ∈ TSP I.a.length,
        BAGamma d L I.a.length (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F (fun i => I.σ.getD i false)
          (fun i => I.a.getD i 0)
    else 0
  else 0

variable {d L W g E m}

private theorem BAKTreeDeriv_getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (x : α) (i : Fin n) :
    (List.ofFn f).getD i x = f i := by
  simp [List.getD_eq_getElem?_getD]

/-- `BAKcac` on a well-formed loop of length `n ≥ 3`, read through the `Fin n` view. -/
private theorem BAKTreeDeriv_Kcac_eq (t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (Zd d L))
    (hlen : I.a.length = n) (hwf : I.σ.length = I.a.length) :
    BAKcac d L W g E m t I = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n,
      BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F (fun i : Fin n => I.σ.getD i false)
        (fun i : Fin n => I.a.getD i 0) := by
  subst hlen
  have h1 : I.a.length ≠ 1 := by omega
  have h2 : I.a.length ≠ 2 := by omega
  simp only [BAKcac, hwf, h1, h2, ↓reduceIte, hn, ↓reduceDIte]

/-- **`BAKcac_spliced`** (target 4): `BAKcac` satisfies the three clauses of the pin `BASplicedFam`. -/
theorem BAKcac_spliced : BASplicedFam d L W g E m (BAKcac d L W g E m) := by
  refine ⟨fun t s a => ?_, fun t σ₁ σ₂ a₁ a₂ => ?_, fun t n _ hn σ a => ?_⟩
  · simp [BAKcac]
  · simp [BAKcac]
  · rw [BAKTreeDeriv_Kcac_eq t hn (KLloopOf d L σ a) (by simp [KLloopOf]) (by simp [KLloopOf])]
    simp only [KLloopOf, BAKTreeDeriv_getD_ofFn]

end Kcac

/-! ## 6. Target 3: `baLeafPairs` -/

section Leaf

variable {d L : ℕ} [NeZero L]

/-- `W^d · W^{-d} · W^{-d(n-1)} = W^{-d(n-1)}` for `n ≥ 2`, also at `W^d = 0` (`0⁻¹ = 0`, `0^{n-1} = 0`). -/
private theorem BAKTreeDeriv_scalar (w : ℂ) {n : ℕ} (hn : 2 ≤ n) :
    w * w⁻¹ * (w⁻¹) ^ (n - 1) = (w⁻¹) ^ (n - 1) := by
  by_cases hw : w = 0
  · subst hw
    simp [zero_pow (show n - 1 ≠ 0 by omega)]
  · rw [mul_inv_cancel₀ hw, one_mul]

/-- The algebra of one pair: `W^d ∑_x (W^{-d(n-1)} ∑_F Γ_F(x)) (W^{-d} P(x)) = W^{-d(n-1)} ∑_F ∑_b P(b) Γ_F(b)`. -/
private theorem BAKTreeDeriv_pair_alg {ι : Type*} (S : Finset ι) (w : ℂ) {n : ℕ} (hn : 2 ≤ n)
    (P : Zd d L → ℂ) (Γ : ι → Zd d L → ℂ) :
    w * ∑ x : Zd d L, ((w⁻¹) ^ (n - 1) * ∑ F ∈ S, Γ F x) * (w⁻¹ * P x) =
      (w⁻¹) ^ (n - 1) * ∑ F ∈ S, ∑ b : Zd d L, P b * Γ F b := by
  have h : ∀ x : Zd d L, w * (((w⁻¹) ^ (n - 1) * ∑ F ∈ S, Γ F x) * (w⁻¹ * P x)) =
      (w * w⁻¹ * (w⁻¹) ^ (n - 1)) * (P x * ∑ F ∈ S, Γ F x) := fun x => by ring
  rw [Finset.mul_sum]
  simp only [h, BAKTreeDeriv_scalar w hn]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _

/-- The same with the two factors exchanged (the wrap pair `(1, n)`: the 2-loop is on the left). -/
private theorem BAKTreeDeriv_pair_alg' {ι : Type*} (S : Finset ι) (w : ℂ) {n : ℕ} (hn : 2 ≤ n)
    (P : Zd d L → ℂ) (Γ : ι → Zd d L → ℂ) :
    w * ∑ x : Zd d L, (w⁻¹ * P x) * ((w⁻¹) ^ (n - 1) * ∑ F ∈ S, Γ F x) =
      (w⁻¹) ^ (n - 1) * ∑ F ∈ S, ∑ b : Zd d L, P b * Γ F b := by
  rw [← BAKTreeDeriv_pair_alg S w hn P Γ]
  congr 1
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **Target 3** (`BALeafPairsStmt`): the leaf part of `W^{-d(n-1)} ∑_F ∂_tΓ_F` is the sum of the `n` leaf pairs of
`treeEqRhsS` at `S = 1`, for every family `K` with `BASplicedFam`.  Leaf `v ≤ n-2`: the pair `(v+1, v+2)`, `cutGlueL` is
the `n`-loop with `a_v ← x` (clause 3), `cutGlueR` the 2-loop `⟨[σ_v,σ_{v+1}],[a_v,x]⟩` (clause 2, the closed form).  Leaf
`v = n-1`: the wrap pair `(1, n)`, `cutGlueL` is the 2-loop `⟨[σ_0,σ_{n-1}],[x,a_{n-1}]⟩` read from the other end, closed by
`BAKTreeDeriv_P_swap` (C2), `cutGlueR` the `n`-loop with `a_{n-1} ← x`.  No hypothesis `0 < W`: at `W^d = 0` both sides
are `0`. -/
theorem baLeafPairs (d : ℕ) : BALeafPairsStmt d := by
  intro L W _ g κ E m hr K hK n _ hn σ a t ht0 ht1
  obtain ⟨-, hK2, hK3⟩ := hK
  have hv : ∀ v : Fin n, (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ b : Zd d L,
        (BATheta d L g E m t (σ v) (σ (v + 1)) * BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b *
          BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b)
      = ((W : ℂ) ^ d) * ∑ x : Zd d L,
          K t (LoopIdx.cutGlueL (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
            (KLloopOf d L σ a)) *
          K t (LoopIdx.cutGlueR (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) x
            (KLloopOf d L σ a)) := by
    intro v
    by_cases hlt : v.val + 1 < n
    · simp only [hlt, ↓reduceIte]
      have e1 : ∀ x : Zd d L, K t (LoopIdx.cutGlueL (v.val + 1) (v.val + 2) x (KLloopOf d L σ a)) =
          (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n,
            BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v x) := fun x => by
        rw [KLloopOf_cutGlueL_leaf σ a v x]
        exact hK3 t n hn σ _
      have e2 : ∀ x : Zd d L, K t (LoopIdx.cutGlueR (v.val + 1) (v.val + 2) x (KLloopOf d L σ a)) =
          (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t (σ v) (σ (v + 1)) *
            BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) x := fun x => by
        rw [KLloopOf_cutGlueR_leaf σ a v hlt x]
        exact hK2 t _ _ _ _
      simp only [e1, e2]
      exact (BAKTreeDeriv_pair_alg (TSP n) _ (by omega)
        (fun b => (BATheta d L g E m t (σ v) (σ (v + 1)) *
          BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b)
        (fun F b => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b))).symm
    · have hv' : v.val + 1 = n := by have := v.isLt; omega
      have h0 : v + 1 = 0 := Fin.ext (by
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), hv', Nat.mod_self]; rfl)
      simp only [hlt, ↓reduceIte]
      have e1 : ∀ x : Zd d L, K t (LoopIdx.cutGlueL 1 n x (KLloopOf d L σ a)) =
          (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t (σ v) (σ (v + 1)) *
            BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) x := fun x => by
        rw [KLloopOf_cutGlueL_wrap σ a v hv' x, hK2 t (σ 0) (σ v) x (a v), h0,
          BAKTreeDeriv_P_swap g κ E m hr ht0 ht1 (σ v) (σ 0) x (a v)]
      have e2 : ∀ x : Zd d L, K t (LoopIdx.cutGlueR 1 n x (KLloopOf d L σ a)) =
          (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n,
            BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v x) := fun x => by
        rw [KLloopOf_cutGlueR_wrap σ a v hv' x]
        exact hK3 t n hn σ _
      simp only [e1, e2]
      exact (BAKTreeDeriv_pair_alg' (TSP n) _ (by omega)
        (fun b => (BATheta d L g E m t (σ v) (σ (v + 1)) *
          BAMss d L (BAMB d L g (E : ℂ) m) (σ v) (σ (v + 1))) (a v) b)
        (fun F b => BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ (Function.update a v b))).symm
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => hv v

end Leaf

/-! ## 7. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
the real-axis data of `(self_m)` on the `4³ = 64` blocks), `t = 1/2`, `W = 2`, the charges `σ = (+,+,-)` at `n = 3` and
`σ = (+,+,-,+)` at `n = 4`, the labels three resp. four distinct blocks.  `n = 3` has the one tree `∅`; `n = 4` has the three
trees `∅`, `{(0,2)}`, `{(1,3)}` (`TSP_four`), so there the chord term of `BAGammaDerivRHS` is present (`F = {(0,2)}`) and the
cactus sum of `BAKcac` has three terms.  The hypotheses are discharged: `BAReal` by `P.real`, `KLIsTSP F` by a direct proof
resp. `KLisTSP_of_mem_TSP`, `BASplicedFam` by `BAKcac_spliced`, `0 ≤ 1/2 < 1`, `3 ≤ n`. -/

namespace KTreeDerivInst

open RBM.BA.MFixedPointInst

private theorem BAKTreeDeriv_isTSP_empty {n : ℕ} : KLIsTSP (∅ : Finset (Fin n × Fin n)) :=
  ⟨fun d hd => absurd hd (Finset.notMem_empty d), fun e he => absurd he (Finset.notMem_empty e)⟩

private theorem BAKTreeDeriv_isTSP_F02 :
    KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

/-- **Target 2 at `n = 3`**, `F = ∅`, the flow point `P`, `t = 1/2`. -/
example :
    HasDerivAt (fun s : ℝ => BAGamma 3 4 3 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) s ∅
        ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]])
      (BAGammaDerivRHS 3 4 3 P.g0 P.E P.m0 (1 / 2) ∅ ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]])
      (1 / 2) :=
  baGamma_hasDerivAt 3 4 3 P.g0 P.m0.im P.E P.m0 (le_refl 3) P.real ∅ BAKTreeDeriv_isTSP_empty _ _ (1 / 2)
    (by norm_num) (by norm_num)

/-- **Target 2 at `n = 4`**, `F = {(0,2)}` (one chord: the chord term of `BAGammaDerivRHS` is present). -/
example :
    HasDerivAt (fun s : ℝ => BAGamma 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) s
        {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])
      (BAGammaDerivRHS 3 4 4 P.g0 P.E P.m0 (1 / 2) {((0 : Fin 4), (2 : Fin 4))} ![true, true, false, true]
        ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])
      (1 / 2) :=
  baGamma_hasDerivAt 3 4 4 P.g0 P.m0.im P.E P.m0 (by norm_num) P.real _ BAKTreeDeriv_isTSP_F02 _ _ (1 / 2)
    (by norm_num) (by norm_num)

/-- **Target 3 at `n = 3`** with the family `BAKcac` (`W = 2`): the leaf part of `W^{-2d} ∑_F ∂_tΓ_F` is the three leaf pairs
`(1,2)`, `(2,3)`, `(1,3)` of `treeEqRhsS`. -/
example :=
  baLeafPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 3 (le_refl 3)
    ![true, true, false] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0]] (1 / 2) (by norm_num) (by norm_num)

/-- **Target 3 at `n = 4`** with the family `BAKcac` (`W = 2`): three trees in the sum, four leaf pairs. -/
example :=
  baLeafPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 4 (by norm_num)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] (1 / 2) (by norm_num)
    (by norm_num)

/-- `BAKcac_spliced` at the data: the three clauses of `BASplicedFam`. -/
example : BASplicedFam 3 4 2 P.g0 P.E P.m0 (BAKcac 3 4 2 P.g0 P.E P.m0) := BAKcac_spliced

/-- Clause 1 (length 1: `PropSpin`), clause 2 (length 2: the closed form `(Kn2sol)`) and clause 3 (length 4: the cactus sum
over `TSP 4`, three trees) of `BAKcac_spliced`, applied at `t = 1/2` and the data above. -/
example := (BAKcac_spliced (d := 3) (L := 4) (W := 2) (g := P.g0) (E := P.E) (m := P.m0)).1 (1 / 2) true ![0, 0, 0]

example := (BAKcac_spliced (d := 3) (L := 4) (W := 2) (g := P.g0) (E := P.E) (m := P.m0)).2.1 (1 / 2) true false
  ![0, 0, 0] ![1, 0, 0]

example := (BAKcac_spliced (d := 3) (L := 4) (W := 2) (g := P.g0) (E := P.E) (m := P.m0)).2.2 (1 / 2) 4
  (by norm_num) ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-! ### The list identities of target 3 at `n = 4` (`d = 1`, `L = 3`, `σ = (+,-,+,+)`, `a = (0,1,2,0)`, `x = 1`), by `decide` -/

/-- Leaf `v = 1` (pair `(2, 3)`): `cutGlueL` keeps `σ` and sets `a_1 := x`. -/
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueL 2 3 ![1] =
    KLloopOf 1 3 ![true, false, true, true] (Function.update ![![0], ![1], ![2], ![0]] 1 ![1]) := by decide

/-- Leaf `v = 1` (pair `(2, 3)`): `cutGlueR` is the 2-loop `⟨[σ_1, σ_2], [a_1, x]⟩`. -/
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueR 2 3 ![1] =
    ⟨[false, true], [![1], ![1]]⟩ := by decide

/-- Wrap pair `(1, 4)`: `cutGlueL` is the 2-loop `⟨[σ_0, σ_3], [x, a_3]⟩`. -/
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueL 1 4 ![1] =
    ⟨[true, true], [![1], ![0]]⟩ := by decide

/-- Wrap pair `(1, 4)`: `cutGlueR` keeps `σ` and sets `a_3 := x`. -/
example : (KLloopOf 1 3 ![true, false, true, true] ![![0], ![1], ![2], ![0]]).cutGlueR 1 4 ![1] =
    KLloopOf 1 3 ![true, false, true, true] (Function.update ![![0], ![1], ![2], ![0]] 3 ![1]) := by decide

/-- The four public list facts at these data (`v = 1`, resp. `v = 3`). -/
example := KLloopOf_cutGlueL_leaf (d := 1) (L := 3) ![true, false, true, true] ![![0], ![1], ![2], ![0]] 1 ![1]

example := KLloopOf_cutGlueR_leaf (d := 1) (L := 3) ![true, false, true, true] ![![0], ![1], ![2], ![0]] 1
  (by decide) ![1]

example := KLloopOf_cutGlueL_wrap (d := 1) (L := 3) ![true, false, true, true] ![![0], ![1], ![2], ![0]] 3
  (by decide) ![1]

example := KLloopOf_cutGlueR_wrap (d := 1) (L := 3) ![true, false, true, true] ![![0], ![1], ![2], ![0]] 3
  (by decide) ![1]

end KTreeDerivInst

end RBM.BA
