/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.List.GetD
import RBM3D.Loop.KLCut

/-!
# The `K`-loop layer, third ticket (KL3): the tree sum `𝒦` solves `Def_Ktza`, `d ≥ 3`

Ticket T2020 (design ticket T2004, row KL3).  Names are in `RBM.Loop`.

**`RBM.Loop.KLK_isKLoop`** is the pin `KLisKLoopPin`
(`64b58eb:RBM3D/Probe/T2004Pins.lean:755-760`), proved: for `3 ≤ L`, `1 ≤ W`, `|E| < 2`, the tree
sum `KLK` of KL1 (`m(σ)` at `n = 1`, `(Kn2sol)` at `n = 2`, `(eq_Ktree)` at `n ≥ 3`) is a family of
`K`-loops on `t ∈ [0,1)` in the sense of the merged `IsKLoop` (`RBM3D/Loop/TreeRep.lean:158`):

* `(pro_dyncalK)` with `(calGonIND)`, for loops of length `n ≥ 2`:
  `∂_t 𝒦^{(n)} = W^d ∑_{1≤k<l≤n} ∑_{a,b} 𝒦(cutL^{(a)}_{k,l}) S^{(B)}_{ab} 𝒦(cutR^{(b)}_{k,l})`;
* `(eq:initial_K)`, `(eq:KMloop)`: `𝒦_0 = MLoop`, for loops of length `n ≥ 2`;
* `𝒦^{(1)} = m(σ)`.

This is the existence half of `Def_Ktza`; the uniqueness half is the pin `KLuniquePin` (ticket KL4).
The paper writes `t ∈ [0,1]`; `Θ_1` does not exist, so the equations are stated on `Set.Ico 0 1`
(paper-delta candidate T2020a, `T2004d` of `docs/DECISIONS.md:142`).  The theorem adds no
hypothesis: its type is the body of the pin.

## The proof: a port of `RBM2D/Loop/TreeRep.lean` at `c9a24cf`

Source lines (all at `c9a24cf`): `section Assembly` 1669, `KN` 1823, `KNInternal` 1914,
`Lists` 1997, `Final` 2438, the pinned theorem `isPrimitive_Kcal` 2563; the edge facts
`SB_apply_comm` 64, `hasDerivAt_thetaEdge` 123, `hasDerivAt_thetaEdge'` 132, `kTwo_rotate` 143,
`rhs_kTwo_left` 151, `rhs_kTwo_right` 164 and `sum_perm4'` 466 (private in
`RBM3D/Loop/KLCut.lean`, re-ported here).

Changes: `Z2 L ↦ Zd d L`; the tree and cut names of RBM2D ↦ the merged KL1/KL2 names
(`treeValW ↦ KLtreeValW`, `treeValG ↦ KLtreeValG`, `Kn ↦ KLn`, `Kgen ↦ KLgen`,
`treeValW_cut ↦ KLtreeValW_cut`, `sum_cut ↦ KLsum_cut`, `gval_in_eq ↦ KLgval_in_eq`, …);
`thetaEdge L m`, `SB L`, `kTwo L W m` become `thetaEdge d L g m`, `SB d L g`, `kTwo d L W g m`;
`W^2 ↦ W^d`; the bound variable `d` of RBM2D (an edge) is called `ed`, since `d` is the dimension
here; `primRhs`, `primInit`, `IsPrimitive`, `mSig`, `Kcal` ↦ `treeEqRhs`, `MLoop`, `IsKLoop`,
`mSigma`, `KLK`.  Merged lemmas replace RBM2D's: `hasDerivAt_Theta_mul_apply`
(`RBM3D/Propagator/Deriv.lean:108`) for `hasDerivAt_Theta_apply` and the chain rule,
`treeEqRhs_two` (`RBM3D/Loop/TreeRep.lean:194`), `hasDerivAt_kTwo`, `kTwo_zero`
(`RBM3D/Loop/Primitive.lean:65, 80`), `norm_mul_mSigma_lt_one` (`RBM3D/Defs/Semicircle.lean:91`) for
`TreeRep_norm_mSig`.

The argument.  (1) `KLhasDerivAt_treeValW` (KL2): the derivative of one tree has one term per
leaf and one per internal edge, and `∂_t Θ_{tμ} = μ Θ S^{(B)} Θ` (`hasDerivAt_thetaEdge'`).
(2) `leaf_term`, `leaf_pair_term`, `root_pair_term`: the term of the leaf `v` is the pair
`(k, l) = (v+1, v+2)`, or `(1, n)` for the root, whose `2`-loop piece is `kTwo` and whose other
piece is `KLn` with `a_v := x`.  (3) `treeValW_internal_cut`, `internal_term`, `diag_pair_term`:
the term of the internal edge `J = (i, j)`, summed over the trees `F ∋ J`, is the pair
`(i+1, j+1)`: the cut `KLtreeValW_cut` at `J` and the cut bijection `KLsum_cut` give a product of
two trees on the polygons with `n - w + 1` and `w + 1` vertices (`w = j - i`), and
`W^d (W^d)⁻¹^{n''-1} (W^d)⁻¹^{n'-1} = (W^d)⁻¹^{n-1}` for `n' + n'' = n + 2`.
(4) `sum_pairs`: the pairs `1 ≤ k < l ≤ n` are the `n` leaf pairs and the pairs `(i+1, j+1)` of
the diagonals; `n = 2` is `hasDerivAt_kTwo`.  (5) `Kn_zero`: at `t = 0`, `Θ_0 = 1`, the internal
edges `Θ_0 - 1` vanish, and only the star `F = ∅` survives,
`∑_b ∏_v 1(a_v = b) = 1(a₁ = … = a_n)`.

Public names: `KLK_isKLoop` and the instances `KLTreeDerivInst_*` (section 4); every helper is
`private` (as the corresponding helpers are in RBM2D).
-/

set_option linter.style.longLine false

namespace RBM.Loop

open Finset

/-! ## 1. Edge facts and a fourfold reordering -/

section EdgeFacts

/-- `S^(B)` is symmetric, entrywise.  Port of `RBM2D/Loop/TreeRep.lean:64` at `c9a24cf`
(`SB_apply_comm`). -/
private theorem SB_apply_comm (d L : ℕ) [NeZero L] (g : ℝ) (x y : Zd d L) :
    SB d L g x y = SB d L g y x :=
  congrFun (congrFun (SB_transpose d L g) y) x

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- The derivative of an edge: `∂_t (Θ_{t μ})_{ab} = μ (Θ S^(B) Θ)_{ab}`.  Port of
`RBM2D/Loop/TreeRep.lean:123` at `c9a24cf` (`hasDerivAt_thetaEdge`), with the merged
`RBM.hasDerivAt_Theta_mul_apply` (`RBM3D/Propagator/Deriv.lean:108`) in place of RBM2D's
`hasDerivAt_Theta_apply` and the chain rule. -/
private theorem hasDerivAt_thetaEdge (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (a b : Zd d L) :
    HasDerivAt (fun r : ℝ => thetaEdge d L g m r s s' a b)
      ((thetaEdge d L g m t s s' * SB d L g * thetaEdge d L g m t s s') a b * (m s * m s')) t :=
  (hasDerivAt_Theta_mul_apply d L g (norm_SB d L g hL) ht a b).congr_deriv (mul_comm _ _)

/-- Port of `RBM2D/Loop/TreeRep.lean:132` at `c9a24cf` (`hasDerivAt_thetaEdge'`). -/
private theorem hasDerivAt_thetaEdge' (hL : 3 ≤ L) (m : Bool → ℂ) {t : ℝ} (s s' : Bool)
    (ht : ‖(t : ℂ) * (m s * m s')‖ < 1) (i j : Zd d L) :
    HasDerivAt (fun r : ℝ => thetaEdge d L g m r s s' i j)
      ((((m s * m s') • (thetaEdge d L g m t s s' * SB d L g)) * thetaEdge d L g m t s s') i j) t :=
  (hasDerivAt_thetaEdge hL m s s' ht i j).congr_deriv (by
    rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, mul_comm])

variable (W : ℕ) [NeZero W] (m : Bool → ℂ) (t : ℝ)

omit [NeZero W] in
/-- `(Kn2sol)` is invariant under reading the `2`-loop from the other end.  Port of
`RBM2D/Loop/TreeRep.lean:143` at `c9a24cf` (`kTwo_rotate`). -/
private theorem kTwo_rotate (hL : 3 ≤ L) (s s' : Bool) (ht : ‖(t : ℂ) * (m s * m s')‖ < 1)
    (x y : Zd d L) : kTwo d L W g m t s s' x y = kTwo d L W g m t s' s y x := by
  have hΘ := congrFun (congrFun (Theta_transpose_of_three_le (g := g) hL ht) y) x
  simp only [Matrix.transpose_apply] at hΘ
  rw [kTwo, kTwo, mul_comm (m s') (m s), hΘ]

/-- Substituting `(Kn2sol)` for a short chain on the right: `W^d · W^{-d} = 1` and
`W^d ∑_{x,y} f(x) S_{xy} K_{(s,s'),(a,y)} = ∑_x (m m' Θ_{t m m'} S)_{ax} f(x)`.  Port of
`RBM2D/Loop/TreeRep.lean:151` at `c9a24cf` (`rhs_kTwo_left`), `W^2 ↦ W^d`. -/
private theorem rhs_kTwo_left (s s' : Bool) (a : Zd d L) (f : Zd d L → ℂ) :
    (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L, f x * SB d L g x y * kTwo d L W g m t s s' a y
      = ∑ x : Zd d L, ((m s * m s') • (thetaEdge d L g m t s s' * SB d L g)) a x * f x := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul, kTwo, thetaEdge]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [SB_apply_comm d L g x y]
  field_simp

/-- The same with the short chain on the left (the wrap-around pair `(1, n)`).  Port of
`RBM2D/Loop/TreeRep.lean:164` at `c9a24cf` (`rhs_kTwo_right`), `W^2 ↦ W^d`. -/
private theorem rhs_kTwo_right (hL : 3 ≤ L) (s s' : Bool) (ht : ‖(t : ℂ) * (m s * m s')‖ < 1)
    (a : Zd d L) (f : Zd d L → ℂ) :
    (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L, kTwo d L W g m t s s' x a * SB d L g x y * f y
      = ∑ y : Zd d L, ((m s * m s') • (thetaEdge d L g m t s' s * SB d L g)) a y * f y := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [kTwo_rotate W m t hL s s' ht x a, kTwo, thetaEdge]
  field_simp

end EdgeFacts

/-- Reordering a fourfold sum with two `Finset` ranges: `(a, b, c, d) ↦ (d, c, a, b)`.  Private
copy of the private `sum_perm4'` of `RBM3D/Loop/KLCut.lean` (RBM2D: `TreeRep.lean:466` at `c9a24cf`). -/
private theorem sum_perm4' {α β γ δ : Type*} [Fintype γ] [Fintype δ] (s : Finset α) (t : Finset β)
    (f : α → β → γ → δ → ℂ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c, ∑ d, f a b c d = ∑ d, ∑ c, ∑ a ∈ s, ∑ b ∈ t, f a b c d :=
  calc ∑ a ∈ s, ∑ b ∈ t, ∑ c, ∑ d, f a b c d = ∑ a ∈ s, ∑ b ∈ t, ∑ d, ∑ c, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ d, ∑ b ∈ t, ∑ c, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ a ∈ s, ∑ b ∈ t, ∑ c, f a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a ∈ s, ∑ c, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a ∈ s, ∑ b ∈ t, f a b c d := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ## 2. The derivative of the tree sum, the classification of the pairs `(k, l)`, the initial
value -/

section Assembly

variable (d L : ℕ) [NeZero L] {n : ℕ} [NeZero n]

/-- **Linearity in one leaf**: `M_v = A B` gives `∑_z A_{a_v z}` times the tree with the leaf
relabelled `z` and weight `B`. -/
private theorem treeValW_leaf_mul (F : Finset (Fin n × Fin n)) (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (v : Fin n)
    (A B : Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a (Function.update M v (A * B)) E
      = ∑ z : Zd d L, A (a v) z * KLtreeValW d L F (Function.update a v z)
        (Function.update M v B) E := by
  simp only [KLtreeValW, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [KLprod_update_eq (fun w => M w (a w) (b ⟨KLleafPar F w, KLleafPar_mem F w⟩)) _ v
    (fun w hw => by rw [Function.update_of_ne hw]), Function.update_self, Matrix.mul_apply,
    Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [KLprod_update_eq (fun w => M w (a w) (b ⟨KLleafPar F w, KLleafPar_mem F w⟩)) _ v
    (fun w hw => by rw [Function.update_of_ne hw, Function.update_of_ne hw]),
    Function.update_self, Function.update_self]
  ring

variable {d L}
variable {g : ℝ} (hL : 3 ≤ L) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
  {J : Fin n × Fin n} (hJ : J ∈ F)
  (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hF hn hJ hm

/-- **The internal edge `J`, differentiated, is a product of two smaller trees.**  With leaf
weights `Θ_{t m(σ_v) m(σ_{v+1})}` and internal weights `Θ - 1`, putting `Θ_J S Θ_J` on the edge
`J` gives `∑_{u,w} (inside polygon, root label u) S_{uw} (outside polygon, glue label w)`.
The small polygons enter only through their charges `σi`, `σo` (read off `σ`) and labels. -/
private theorem treeValW_internal_cut (σ : Fin n → Bool) (a : Fin n → Zd d L)
    (σi : Fin (KLwIn J + 1) → Bool) (ai : Zd d L → Fin (KLwIn J + 1) → Zd d L)
    (σo : Fin (n - KLwIn J + 1) → Bool) (ao : Zd d L → Fin (n - KLwIn J + 1) → Zd d L)
    (hσi : ∀ i : Fin (KLwIn J + 1), σi i = σ (KLunShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - KLwIn J + 1), σo i = σ (KLunColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : KLLIn J, ai u (KLinV J v) = a v)
    (hao0 : ∀ w, ao w (KLglueV J) = w) (hao1 : ∀ w, ∀ v : KLLOut J, ao w (KLoutV J v) = a v) :
    KLtreeValW d L F a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
        (Function.update (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) ⟨J, hJ⟩
          (thetaEdge d L g m t (σ J.1) (σ J.2) * SB d L g * thetaEdge d L g m t (σ J.1) (σ J.2)))
      = ∑ u : Zd d L, ∑ w : Zd d L,
          KLtreeValG d L g m t σi (ai u) (KLFIn F J) * SB d L g u w * KLtreeValG d L g m t σo (ao w) (KLFOut F J) := by
  have hJd := hF.1 J hJ
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  have hw : KLwIn J = J.2.val - J.1.val := rfl
  -- vertex / region bookkeeping
  have si : ∀ i : Fin (KLwIn J + 1), (KLunShift J (i, i)).1.val = i.val + J.1.val := fun i =>
    (KLunShift_val (i, i)).1
  have so : ∀ i : Fin (n - KLwIn J + 1), (KLunColP J (i, i)).1.val = KLunCol J i.val := fun i =>
    (KLunColP_val (i, i) hJ2).1
  have hΘT : (thetaEdge d L g m t (σ J.1) (σ J.2)).transpose = thetaEdge d L g m t (σ J.2) (σ J.1) := by
    rw [thetaEdge_comm d L g m t (σ J.2)]
    exact Theta_transpose_of_three_le hL (hm _ _)
  have hσi' : ∀ (i : Fin (KLwIn J + 1)) (v : Fin n), v.val = i.val + J.1.val → σi i = σ v := by
    intro i v hv; rw [hσi i]; congr 1; exact Fin.ext (by rw [si i, hv])
  have hσo' : ∀ (i : Fin (n - KLwIn J + 1)) (v : Fin n), v.val = KLunCol J i.val → σo i = σ v := by
    intro i v hv; rw [hσo i]; congr 1; exact Fin.ext (by rw [so i, hv])
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hsucc : ∀ v : Fin n, v.val < n - 1 → (v + 1 : Fin n).val = v.val + 1 := by
    intro v hv; rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
  -- inside side conditions
  have hM0i : thetaEdge d L g m t (σi (Fin.last _)) (σi (Fin.last _ + 1))
      = (thetaEdge d L g m t (σ J.1) (σ J.2)).transpose := by
    rw [hΘT, Fin.last_add_one, hσi' _ J.2 (by simp only [Fin.val_last, KLwIn]; omega),
      hσi' 0 J.1 (by simp)]
  have hM1i : ∀ v : KLLIn J, thetaEdge d L g m t (σi (KLinV J v)) (σi (KLinV J v + 1))
      = thetaEdge d L g m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := KLinV_val v.2
    have hlt : (KLinV J v.1).val < KLwIn J := by rw [h1]; simp only [KLwIn]; omega
    have hvn : v.1.val < n - 1 := by omega
    rw [hσi' _ v.1 (by rw [h1]; omega), hσi' _ (v.1 + 1) (by
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      omega)]
  have hEi : ∀ ed : KLEIn F J, thetaEdge d L g m t (σi (KLshiftIn J ed.1.1).1) (σi (KLshiftIn J ed.1.1).2) - 1
      = thetaEdge d L g m t (σ ed.1.1.1) (σ ed.1.1.2) - 1 := by
    intro ed
    have hlt := (hF.1 ed.1.1 ed.1.2).1
    have hv := KLshiftIn_val ed.2.1 (le_of_lt hlt)
    have hdJ := ed.2.1
    simp only [KLArcLe, Fin.le_def] at hdJ
    rw [hσi' _ ed.1.1.1 (by rw [hv.1]; omega),
      hσi' _ ed.1.1.2 (by rw [hv.2]; omega)]
  -- outside side conditions
  have hg : (KLglueV J).val = J.1.val := by simp only [KLglueV, KLwIn]; omega
  have hM0o : thetaEdge d L g m t (σo (KLglueV J)) (σo (KLglueV J + 1))
      = thetaEdge d L g m t (σ J.1) (σ J.2) := by
    have hg1 : (KLglueV J + 1).val = J.1.val + 1 := by
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last, hg]; simp only [KLwIn]; omega), hg]
    rw [hσo' _ J.1 (by rw [hg, KLunCol_of_le le_rfl]), hσo' _ J.2 (by
      rw [hg1, KLunCol_of_gt (by omega)]; simp only [KLwIn]; omega)]
  have hM1o : ∀ v : KLLOut J, thetaEdge d L g m t (σo (KLoutV J v)) (σo (KLoutV J v + 1))
      = thetaEdge d L g m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    have h1 := KLoutV_val v.1 hJ2
    rw [hσo' _ v.1 (by rw [h1, KLunCol_col (by omega) hJw])]
    congr 1
    by_cases hr : v.1.val = n - 1
    · have hlast : KLoutV J v.1 = Fin.last _ := by
        refine Fin.ext ?_
        rw [h1, Fin.val_last, KLcol_of_gt (by omega), hr]; simp only [KLwIn]; omega
      have hv1 : v.1 + 1 = 0 := by
        refine Fin.ext ?_
        rw [Fin.val_add, hone, hr, Nat.sub_add_cancel (by omega), Nat.mod_self]; rfl
      rw [hlast, Fin.last_add_one, hv1]
      exact hσo' 0 0 (by simp [KLunCol])
    · have hvn : v.1.val < n - 1 := by have := v.1.isLt; omega
      have hlt : (KLoutV J v.1).val < n - KLwIn J := by
        rw [h1]; rcases hvs with h | h
        · rw [KLcol_of_le (by omega)]; simp only [KLwIn]; omega
        · rw [KLcol_of_gt (by omega)]; simp only [KLwIn]; omega
      refine hσo' _ _ ?_
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      rcases hvs with h | h
      · rw [KLcol_of_le (by omega)]
        by_cases h' : v.1.val + 1 ≤ J.1.val
        · rw [KLunCol_of_le h']
        · have : v.1.val + 1 = J.1.val := by omega
          rw [this, KLunCol_of_le le_rfl]
      · rw [KLcol_of_gt (by omega), KLunCol_of_gt (by simp only [KLwIn]; omega)]
        simp only [KLwIn]; omega
  have hEo : ∀ ed : KLEOut F J, thetaEdge d L g m t (σo (KLshiftOut J ed.1.1).1) (σo (KLshiftOut J ed.1.1).2) - 1
      = thetaEdge d L g m t (σ ed.1.1.1) (σ ed.1.1.2) - 1 := by
    intro ed
    have hE := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem ed.1.2) ed.2
    have hv := KLshiftOut_val ed.1.1 hJ2
    rw [hσo' _ ed.1.1.1 (by rw [hv.1, KLunCol_col hE.1 hJw]),
      hσo' _ ed.1.1.2 (by rw [hv.2, KLunCol_col hE.2.1 hJw])]
  rw [KLtreeValW_cut d L hF hn hJ a _ _ (thetaEdge d L g m t (σ J.1) (σ J.2)) (SB d L g)
    (thetaEdge d L g m t (σ J.1) (σ J.2))]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [KLgval_in_eq hF hn hJ d L a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
      (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) u _ (ai u)
        (fun v => thetaEdge d L g m t (σi v) (σi (v + 1)))
      (fun ed => thetaEdge d L g m t (σi ed.1.1) (σi ed.1.2) - 1) (hai0 u) (hai1 u) hM0i hM1i hEi,
    KLgval_out_eq hF hn hJ d L a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
      (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) w _ (ao w)
        (fun v => thetaEdge d L g m t (σo v) (σo (v + 1)))
      (fun ed => thetaEdge d L g m t (σo ed.1.1) (σo ed.1.2) - 1) (hao0 w) (hao1 w) hM0o hM1o hEo]
  rfl

end Assembly

section KN

/-- The derivative of an edge weight: `μ Θ S Θ`, written as `(μ • (Θ S)) Θ`. -/
private noncomputable abbrev dTheta (d L : ℕ) [NeZero L] (g : ℝ) (m : Bool → ℂ) (t : ℝ)
    (s s' : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((m s * m s') • (thetaEdge d L g m t s s' * SB d L g)) * thetaEdge d L g m t s s'

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- Linearity in one internal edge weight. -/
private theorem treeValW_edge_smul {n : ℕ} [NeZero n] (F : Finset (Fin n × Fin n))
    (a : Fin n → Zd d L)
    (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ) (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (ed : ↥F)
    (c : ℂ) (X : Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a M (Function.update E ed (c • X))
      = c * KLtreeValW d L F a M (Function.update E ed X) := by
  simp only [KLtreeValW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [KLprod_update_eq (fun e => E e (b ⟨e.1, KLmem_nodes_of_mem e.2⟩)
      (b ⟨KLnodePar F e, KLnodePar_mem F e⟩)) _ ed (fun e he => by rw [Function.update_of_ne he]),
    KLprod_update_eq (fun e => E e (b ⟨e.1, KLmem_nodes_of_mem e.2⟩)
      (b ⟨KLnodePar F e, KLnodePar_mem F e⟩)) _ ed (fun e he => by rw [Function.update_of_ne he]),
    Function.update_self, Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

variable (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

omit hL hm in
private theorem dTheta_eq (s s' : Bool) :
    dTheta d L g m t s s' = (m s * m s') • (thetaEdge d L g m t s s' * SB d L g * thetaEdge d L g m t s s') := by
  rw [dTheta, Matrix.smul_mul]

omit [NeZero W] in
/-- **The derivative of `KLn`**: one term per leaf and one per internal edge of every tree. -/
private theorem hasDerivAt_Kn {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    HasDerivAt (fun r => KLn d L g W m r n σ a)
      ((∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n,
        (∑ v : Fin n, KLtreeValW d L F a (Function.update
            (fun v => thetaEdge d L g m t (σ v) (σ (v + 1))) v (dTheta d L g m t (σ v) (σ (v + 1))))
            (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1)
          + ∑ ed : ↥F, KLtreeValW d L F a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
            (Function.update (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) ed
              (dTheta d L g m t (σ ed.1.1) (σ ed.1.2))))) t := by
  refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun F _ => ?_)
  refine KLhasDerivAt_treeValW d L (fun v i j => ?_) (fun ed i j => ?_)
  · exact hasDerivAt_thetaEdge' hL m _ _ (hm _ _) i j
  · have := (hasDerivAt_thetaEdge' (g := g) hL m (σ ed.1.1) (σ ed.1.2) (hm _ _) i j).sub_const
      ((1 : Matrix (Zd d L) (Zd d L) ℂ) i j)
    simpa using this

omit hL hm [NeZero W] in
/-- **A leaf term**: differentiating the leaf `v` in every tree gives
`∑_x (μ Θ S)_{a_v x} K(a with a_v := x)`. -/
private theorem leaf_term {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) (v : Fin n) :
    (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * ∑ F ∈ TSP n,
        KLtreeValW d L F a (Function.update
            (fun v => thetaEdge d L g m t (σ v) (σ (v + 1))) v (dTheta d L g m t (σ v) (σ (v + 1))))
          (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1)
      = ∑ x : Zd d L, ((m (σ v) * m (σ (v + 1))) • (thetaEdge d L g m t (σ v) (σ (v + 1)) * SB d L g))
          (a v) x * KLn d L g W m t n σ (Function.update a v x) := by
  have hM : Function.update (fun v => thetaEdge d L g m t (σ v) (σ (v + 1))) v
      (thetaEdge d L g m t (σ v) (σ (v + 1))) = fun v => thetaEdge d L g m t (σ v) (σ (v + 1)) :=
    Function.update_eq_self _ _
  simp only [dTheta, treeValW_leaf_mul, hM, KLn, KLtreeValG, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun F _ => by ring

omit hL hm [NeZero W] in
/-- Exchanging `∑_F ∑_{J ∈ F}` for `∑_J ∑_{F ∋ J}`. -/
private theorem sum_edges_swap {n : ℕ} [NeZero n] (φ : (F : Finset (Fin n × Fin n)) → ↥F → ℂ) :
    ∑ F ∈ TSP n, ∑ ed : ↥F, φ F ed
      = ∑ J ∈ diagonals n, ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
          (if h : J ∈ F then φ F ⟨J, h⟩ else 0) := by
  have h1 : ∀ F ∈ TSP n, ∑ ed : ↥F, φ F ed
      = ∑ J ∈ diagonals n, (if h : J ∈ F then φ F ⟨J, h⟩ else 0) := by
    intro F hF
    have e1 : ∑ ed : ↥F, φ F ed = ∑ ed : ↥F, (if h : ed.1 ∈ F then φ F ⟨ed.1, h⟩ else 0) :=
      Finset.sum_congr rfl fun ed _ => by rw [dite_eq_left ed.2]
    rw [e1, Finset.sum_coe_sort F (fun J => if h : J ∈ F then φ F ⟨J, h⟩ else 0)]
    refine Finset.sum_subset (mem_TSP.1 hF).1 fun J _ hJ => ?_
    rw [dite_eq_right hJ]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun F _ => by split_ifs <;> rfl

end KN

section KNInternal

variable {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

/-- **An internal-edge term**: differentiating the edge `J` in every tree containing it gives
`W ∑_{x,y} K(outside, glue x) S_{xy} K(inside, root y)`, the cut-and-glue term of `J`. -/
private theorem internal_term {n : ℕ} [NeZero n] (hn : 2 ≤ n) {J : Fin n × Fin n}
    (hJd : IsDiag n J.1 J.2) (σ : Fin n → Bool) (a : Fin n → Zd d L)
    (σi : Fin (KLwIn J + 1) → Bool) (ai : Zd d L → Fin (KLwIn J + 1) → Zd d L)
    (σo : Fin (n - KLwIn J + 1) → Bool) (ao : Zd d L → Fin (n - KLwIn J + 1) → Zd d L)
    (hσi : ∀ i : Fin (KLwIn J + 1), σi i = σ (KLunShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - KLwIn J + 1), σo i = σ (KLunColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : KLLIn J, ai u (KLinV J v) = a v)
    (hao0 : ∀ w, ao w (KLglueV J) = w) (hao1 : ∀ w, ∀ v : KLLOut J, ao w (KLoutV J v) = a v)
    (hprod : (∏ i, m (σi i)) * ∏ i, m (σo i) = (∏ i, m (σ i)) * (m (σ J.1) * m (σ J.2))) :
    (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
        (if h : J ∈ F then KLtreeValW d L F a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
          (Function.update (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) ⟨J, h⟩
            (dTheta d L g m t (σ J.1) (σ J.2))) else 0)
      = (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
          KLn d L g W m t (n - KLwIn J + 1) σo (ao x) * SB d L g x y * KLn d L g W m t (KLwIn J + 1) σi (ai y) := by
  have hJw := KLwidth_of_isDiag hJd
  have hJn := J.2.isLt
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.2 (NeZero.ne W))
  -- each tree containing `J`
  have hterm : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if h : J ∈ F then KLtreeValW d L F a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
          (Function.update (fun ed : ↥F => thetaEdge d L g m t (σ ed.1.1) (σ ed.1.2) - 1) ⟨J, h⟩
            (dTheta d L g m t (σ J.1) (σ J.2))) else 0)
        = (m (σ J.1) * m (σ J.2)) * ∑ u : Zd d L, ∑ w : Zd d L,
            KLtreeValG d L g m t σi (ai u) (KLFIn F J) * SB d L g u w *
              KLtreeValG d L g m t σo (ao w) (KLFOut F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    rw [dite_eq_left hJF, dTheta_eq, treeValW_edge_smul,
      treeValW_internal_cut hL (KLisTSP_of_mem_TSP hFT) hn hJF m t hm σ a σi ai σo ao hσi hσo
        hai0 hai1 hao0 hao1]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  -- the cut bijection
  have hbij := KLsum_cut hJd hn (fun G H => ∑ u : Zd d L, ∑ w : Zd d L,
    KLtreeValG d L g m t σi (ai u) H * SB d L g u w * KLtreeValG d L g m t σo (ao w) G)
  rw [hbij]
  -- regroup into the two `KLn`
  have hwn : KLwIn J ≤ n := by simp only [KLwIn]; omega
  have hconst : (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))
      = (W : ℂ) ^ d * ((∏ i, m (σo i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - KLwIn J + 1 - 1))
          * ((∏ i, m (σi i)) * ((W : ℂ) ^ d)⁻¹ ^ (KLwIn J + 1 - 1)) := by
    have hpow : (W : ℂ) ^ d * ((W : ℂ) ^ d)⁻¹ ^ (n - KLwIn J + 1 - 1) *
        ((W : ℂ) ^ d)⁻¹ ^ (KLwIn J + 1 - 1)
        = ((W : ℂ) ^ d)⁻¹ ^ (n - 1) := by
      rw [Nat.add_sub_cancel, Nat.add_sub_cancel, mul_assoc, ← pow_add, Nat.sub_add_cancel hwn]
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ' ((W : ℂ) ^ d)⁻¹ k, ← mul_assoc, mul_inv_cancel₀ hW,
        one_mul]
    calc (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))
        = ((∏ i, m (σi i)) * ∏ i, m (σo i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) := by rw [hprod]; ring
      _ = _ := by rw [← hpow]; ring
  calc (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * ((m (σ J.1) * m (σ J.2)) *
        ∑ G ∈ TSP (n - KLwIn J + 1), ∑ H ∈ TSP (KLwIn J + 1), ∑ u : Zd d L, ∑ w : Zd d L,
          KLtreeValG d L g m t σi (ai u) H * SB d L g u w * KLtreeValG d L g m t σo (ao w) G)
      = ∑ x : Zd d L, ∑ y : Zd d L, ∑ G ∈ TSP (n - KLwIn J + 1), ∑ H ∈ TSP (KLwIn J + 1),
          ((∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2))) *
            (KLtreeValG d L g m t σo (ao x) G * SB d L g x y * KLtreeValG d L g m t σi (ai y) H) := by
        rw [← mul_assoc, Finset.mul_sum]
        simp only [Finset.mul_sum]
        rw [sum_perm4' (TSP (n - KLwIn J + 1)) (TSP (KLwIn J + 1)) (fun G H u w =>
          (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) * (m (σ J.1) * m (σ J.2)) *
            (KLtreeValG d L g m t σi (ai u) H * SB d L g u w * KLtreeValG d L g m t σo (ao w) G))]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
          Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by
            rw [SB_apply_comm d L g y x]; ring
    _ = (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
          KLn d L g W m t (n - KLwIn J + 1) σo (ao x) * SB d L g x y * KLn d L g W m t (KLwIn J + 1) σi (ai y) := by
        rw [hconst]
        simp only [KLn, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm (s := TSP (KLwIn J + 1))]
        exact Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun H _ => by ring

end KNInternal

section Lists

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `KLgen` on a loop of known length `n ≥ 3` is `KLn`. -/
private theorem Kgen_eq (W : ℕ) (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (I : LoopIdx (Zd d L)) (h : I.length = n) :
    KLgen d L g W m t I = KLn d L g W m t n (fun i => I.σ.getD i false) (fun i => I.a.getD i 0) := by
  subst h
  have h1 : I.length ≠ 1 := by omega
  have h2 : I.length ≠ 2 := by omega
  simp only [KLgen, h1, h2, ite_false, dite_eq_left hn]

private theorem Kgen_two (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s₁ s₂ : Bool) (x y : Zd d L) :
    KLgen d L g W m t ⟨[s₁, s₂], [x, y]⟩ = kTwo d L W g m t s₁ s₂ x y := by
  simp [KLgen, LoopIdx.length]

private theorem Kgen_one (W : ℕ) (m : Bool → ℂ) (t : ℝ) (s : Bool) (x : Zd d L) :
    KLgen d L g W m t ⟨[s], [x]⟩ = m s := by
  simp [KLgen, LoopIdx.length]

/-! ### Splitting the pairs `(k, l)` of `(pro_dyncalK)` -/

/-- The pair `(k, l)` of the leaf edge at `v`: `(v+1, v+2)`, or `(1, n)` for the root. -/
private def leafPair {n : ℕ} (v : Fin n) : ℕ × ℕ :=
  if v.val + 1 < n then (v.val + 1, v.val + 2) else (1, n)

private theorem sum_pairs {n : ℕ} [NeZero n] (hn : 3 ≤ n) (f : ℕ → ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l
      = ∑ v : Fin n, f (leafPair v).1 (leafPair v).2
        + ∑ J ∈ diagonals n, f (J.1.val + 1) (J.2.val + 1) := by
  -- the pairs as a finset of `ℕ × ℕ`
  set P : Finset (ℕ × ℕ) := (Finset.Icc 1 n).sigma (fun k => Finset.Ioc k n) |>.map
    ⟨fun p => (p.1, p.2), fun p q h => by
      simp only [Prod.mk.injEq] at h; exact Sigma.ext h.1 (heq_of_eq h.2)⟩ with hP
  have hLHS : ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l = ∑ p ∈ P, f p.1 p.2 := by
    rw [hP, Finset.sum_map, Finset.sum_sigma]
    rfl
  have hmem : ∀ p : ℕ × ℕ, p ∈ P ↔ 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n := by
    intro p
    simp only [hP, Finset.mem_map, Finset.mem_sigma, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨k, l⟩, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨p.1, p.2⟩, ⟨⟨h1, le_of_lt (lt_of_lt_of_le h2 h3)⟩, h2, h3⟩, rfl⟩
  have hinjL : Set.InjOn (fun v : Fin n => leafPair v) (Finset.univ : Finset (Fin n)) := by
    intro v _ w _ h
    simp only [leafPair] at h
    refine Fin.ext ?_
    have := v.isLt; have := w.isLt
    split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> omega
  have hinjD : Set.InjOn (fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1))
      (diagonals n : Set (Fin n × Fin n)) := by
    intro J _ K _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have hsplit : P = (Finset.univ.image fun v : Fin n => leafPair v) ∪
      ((diagonals n).image fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1)) := by
    ext p
    rw [hmem, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hl : p.2 = p.1 + 1
      · refine Or.inl ⟨⟨p.1 - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [leafPair]
        split_ifs with hc <;> ext <;> simp <;> omega
      by_cases hr : p.1 = 1 ∧ p.2 = n
      · refine Or.inl ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
        simp only [leafPair]
        split_ifs with hc <;> ext <;> simp <;> omega
      · refine Or.inr ⟨(⟨p.1 - 1, by omega⟩, ⟨p.2 - 1, by omega⟩), ?_, ?_⟩
        · rw [KLmem_diagonals_iff]
          refine ⟨by rw [Fin.lt_def]; simp; omega, by simp; omega, by simp; omega⟩
        · ext <;> simp <;> omega
    · rintro (⟨v, -, rfl⟩ | ⟨J, hJ, rfl⟩)
      · simp only [leafPair]; have := v.isLt
        split_ifs <;> simp <;> omega
      · obtain ⟨h1, h2, h3⟩ := KLmem_diagonals_iff.1 hJ
        rw [Fin.lt_def] at h1
        have := J.2.isLt
        simp; omega
  have hdisj : Disjoint (Finset.univ.image fun v : Fin n => leafPair v)
      ((diagonals n).image fun J : Fin n × Fin n => (J.1.val + 1, J.2.val + 1)) := by
    rw [Finset.disjoint_left]
    rintro p hp hq
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨J, hJ, hJv⟩ := Finset.mem_image.1 hq
    obtain ⟨h1, h2, h3⟩ := KLmem_diagonals_iff.1 hJ
    rw [Fin.lt_def] at h1
    have := J.2.isLt
    simp only [leafPair] at hJv
    split_ifs at hJv <;> simp only [Prod.mk.injEq] at hJv <;> omega
  rw [hLHS, hsplit, Finset.sum_union hdisj, Finset.sum_image hinjL, Finset.sum_image hinjD]

/-! ### Reading entries of the cut-and-glue lists -/

section ListGetD

variable {α : Type*} {l l' : List α} {ed : α}

private theorem getD_take_append_of_lt {k i : ℕ} (hi : i < k) (hk : k ≤ l.length) :
    (l.take k ++ l').getD i ed = l.getD i ed := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take]
  simp [hi]

private theorem getD_take_append_of_ge {k i : ℕ} (hi : k ≤ i) (hk : k ≤ l.length) :
    (l.take k ++ l').getD i ed = l'.getD (i - k) ed := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega), List.length_take, min_eq_left hk]

private theorem getD_drop' {k i : ℕ} : (l.drop k).getD i ed = l.getD (k + i) ed := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_drop_take {k j i : ℕ} (hi : i < j) :
    ((l.drop k).take j).getD i ed = l.getD (k + i) ed := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop, hi]

private theorem getD_cons_succ' {x : α} {i : ℕ} : (x :: l).getD (i + 1) ed = l.getD i ed := by
  simp [List.getD_eq_getElem?_getD]

end ListGetD

private theorem Kgen_of_length_two (W : ℕ) (m : Bool → ℂ) (t : ℝ) (I : LoopIdx (Zd d L))
    (h : I.length = 2) :
    KLgen d L g W m t I = kTwo d L W g m t (I.σ.getD 0 false) (I.σ.getD 1 false) (I.a.getD 0 0)
      (I.a.getD 1 0) := by
  simp [KLgen, h]

variable (hL : 3 ≤ L) (W : ℕ) [NeZero W] (m : Bool → ℂ) {t : ℝ}
  (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)

/-- **A leaf pair** `(v+1, v+2)` of `(pro_dyncalK)` is the leaf term of `v`. -/
private theorem leaf_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (hlen : I.length = n) (v : Fin n) (hv : v.val + 1 < n) :
    (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
        KLgen d L g W m t (I.cutGlueL (v.val + 1) (v.val + 2) x) * SB d L g x y *
          KLgen d L g W m t (I.cutGlueR (v.val + 1) (v.val + 2) y)
      = ∑ x : Zd d L, ((m (I.σ.getD v false) * m (I.σ.getD (v + 1 : Fin n) false)) •
          (thetaEdge d L g m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) * SB d L g))
          (I.a.getD v 0) x *
          KLn d L g W m t n (fun i => I.σ.getD i false)
            (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hv1 : ((v + 1 : Fin n) : ℕ) = v.val + 1 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), Nat.mod_eq_of_lt hv]
  -- the left chain: the same polygon with `a_v := x`
  have hL' : ∀ x, KLgen d L g W m t (I.cutGlueL (v.val + 1) (v.val + 2) x)
      = KLn d L g W m t n (fun i => I.σ.getD i false)
          (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
    intro x
    have hlenL : (I.cutGlueL (v.val + 1) (v.val + 2) x).length = n := by
      rw [LoopIdx.length_cutGlueL I x (by omega) (by omega) (by omega)]; omega
    rw [Kgen_eq W m t hn _ hlenL]
    congr 1
    · funext i
      simp only [LoopIdx.cutGlueL, show v.val + 2 - 1 = v.val + 1 by omega, List.take_append_drop]
    · funext i
      simp only [LoopIdx.cutGlueL, show v.val + 2 - 1 = v.val + 1 by omega,
        show v.val + 1 - 1 = v.val by omega]
      by_cases hiv : i = v
      · subst hiv
        rw [Function.update_self, getD_take_append_of_ge le_rfl (by omega), Nat.sub_self]
        rfl
      · rw [Function.update_of_ne hiv]
        have hiv' : i.val ≠ v.val := fun h => hiv (Fin.ext h)
        rcases Nat.lt_or_gt_of_ne hiv' with h | h
        · rw [getD_take_append_of_lt h (by omega)]
        · rw [getD_take_append_of_ge (by omega) (by omega),
            show i.val - v.val = (i.val - v.val - 1) + 1 by omega, getD_cons_succ', getD_drop']
          congr 1; omega
  -- the right chain: the `2`-loop `(σ_v, σ_{v+1}), (a_v, y)`
  have hR' : ∀ y, KLgen d L g W m t (I.cutGlueR (v.val + 1) (v.val + 2) y)
      = kTwo d L W g m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) (I.a.getD v 0) y := by
    intro y
    have hlenR : (I.cutGlueR (v.val + 1) (v.val + 2) y).length = 2 := by
      rw [LoopIdx.length_cutGlueR I y (by omega) (by omega) (by omega)]; omega
    rw [Kgen_of_length_two W m t _ hlenR]
    simp only [LoopIdx.cutGlueR, show v.val + 1 - 1 = v.val by omega,
      show v.val + 2 - (v.val + 1) = 1 by omega]
    have e1 : (List.take 1 (List.drop v.val I.a) ++ [y]).getD 0 0 = I.a.getD v 0 := by
      rw [getD_take_append_of_lt (by omega) (by simp; omega), getD_drop', Nat.add_zero]
    have e2 : (List.take 1 (List.drop v.val I.a) ++ [y]).getD 1 0 = y := by
      rw [getD_take_append_of_ge (by omega) (by simp; omega)]
      simp
    rw [getD_drop_take (by omega), getD_drop_take (by omega), hv1, e1, e2]
    simp
  simp_rw [hL', hR']
  exact rhs_kTwo_left W m t _ _ _ _

include hL hm in
/-- **The root pair** `(1, n)` of `(pro_dyncalK)` is the leaf term of the root `v = n - 1` (the left
chain is the `2`-loop `(σ₀, σ_{n-1})`, the right chain the polygon with `a_{n-1} := y`). -/
private theorem root_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (hlen : I.length = n) (v : Fin n) (hv : v.val = n - 1) :
    (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
        KLgen d L g W m t (I.cutGlueL 1 n x) * SB d L g x y * KLgen d L g W m t (I.cutGlueR 1 n y)
      = ∑ x : Zd d L, ((m (I.σ.getD v false) * m (I.σ.getD (v + 1 : Fin n) false)) •
          (thetaEdge d L g m t (I.σ.getD v false) (I.σ.getD (v + 1 : Fin n) false) * SB d L g))
          (I.a.getD v 0) x *
          KLn d L g W m t n (fun i => I.σ.getD i false)
            (Function.update (fun i : Fin n => I.a.getD i 0) v x) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hv1 : ((v + 1 : Fin n) : ℕ) = 0 := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n), hv,
      Nat.sub_add_cancel (by omega), Nat.mod_self]
  -- the left chain: the `2`-loop `(σ₀, σ_{n-1}), (x, a_{n-1})`
  have hL' : ∀ x, KLgen d L g W m t (I.cutGlueL 1 n x)
      = kTwo d L W g m t (I.σ.getD 0 false) (I.σ.getD v false) x (I.a.getD v 0) := by
    intro x
    have hlenL : (I.cutGlueL 1 n x).length = 2 := by
      rw [LoopIdx.length_cutGlueL I x le_rfl (by omega) (by omega)]; omega
    rw [Kgen_of_length_two W m t _ hlenL]
    simp only [LoopIdx.cutGlueL, Nat.sub_self, List.take_zero, List.nil_append]
    have e1 : (List.take 1 I.σ ++ List.drop (n - 1) I.σ).getD 0 false = I.σ.getD 0 false :=
      getD_take_append_of_lt (by omega) (by omega)
    have e2 : (List.take 1 I.σ ++ List.drop (n - 1) I.σ).getD 1 false = I.σ.getD v false := by
      rw [getD_take_append_of_ge le_rfl (by omega), Nat.sub_self, getD_drop', hv, Nat.add_zero]
    have e3 : (x :: List.drop (n - 1) I.a).getD 1 0 = I.a.getD v 0 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, getD_cons_succ', getD_drop', hv, Nat.add_zero]
    rw [e1, e2, e3]
    rfl
  -- the right chain: the polygon with `a_{n-1} := y`
  have hR' : ∀ y, KLgen d L g W m t (I.cutGlueR 1 n y)
      = KLn d L g W m t n (fun i => I.σ.getD i false)
          (Function.update (fun i : Fin n => I.a.getD i 0) v y) := by
    intro y
    have hlenR : (I.cutGlueR 1 n y).length = n := by
      rw [LoopIdx.length_cutGlueR I y le_rfl (by omega) (by omega)]; omega
    rw [Kgen_eq W m t hn _ hlenR]
    congr 1
    · funext i
      simp only [LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (by omega),
        ← List.getD_eq_getElem?_getD]
    · funext i
      simp only [LoopIdx.cutGlueR, Nat.sub_self, List.drop_zero, show n - 1 + 1 = n by omega]
      by_cases hiv : i = v
      · subst hiv
        rw [Function.update_self, getD_take_append_of_ge (by omega) (by omega), hv, Nat.sub_self]
        rfl
      · rw [Function.update_of_ne hiv]
        have hi : i.val < n - 1 := by
          have := i.isLt; have : i.val ≠ v.val := fun h => hiv (Fin.ext h); omega
        rw [getD_take_append_of_lt hi (by omega)]
  simp_rw [hL', hR']
  rw [rhs_kTwo_right W m t hL _ _ (hm _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h0 : (v + 1 : Fin n) = 0 := Fin.ext (by rw [hv1]; rfl)
  rw [h0, mul_comm (m (I.σ.getD 0 false))]
  rfl

omit [NeZero L] in
/-- The charges of the two chains: the inside chain has `σ_p, …, σ_q`, the outside chain
`σ_0, …, σ_p, σ_q, …, σ_{n-1}`, so together they have every charge once and `σ_p, σ_q` twice. -/
private theorem prod_chains (φ : ℕ → ℂ) {n p q : ℕ} (hpq : p + 2 ≤ q) (hq : q < n) :
    (∏ i ∈ Finset.range (q - p + 1), φ (p + i)) *
        ∏ i ∈ Finset.range (n - (q - p) + 1), φ (if i ≤ p then i else i + (q - p - 1))
      = (∏ i ∈ Finset.range n, φ i) * (φ p * φ q) := by
  have h1 : ∏ i ∈ Finset.range (q - p + 1), φ (p + i) = ∏ i ∈ Finset.Ico p (q + 1), φ i := by
    rw [Finset.prod_Ico_eq_prod_range, show q + 1 - p = q - p + 1 by omega]
  have h2 : ∏ i ∈ Finset.range (n - (q - p) + 1), φ (if i ≤ p then i else i + (q - p - 1))
      = (∏ i ∈ Finset.range (p + 1), φ i) * ∏ i ∈ Finset.Ico q n, φ i := by
    rw [← Finset.prod_range_mul_prod_Ico _ (show p + 1 ≤ n - (q - p) + 1 by omega)]
    have e1 : ∀ i ∈ Finset.range (p + 1), φ (if i ≤ p then i else i + (q - p - 1)) = φ i := by
      intro i hi; rw [Finset.mem_range] at hi; rw [ite_eq_left (by omega)]
    have e2 : ∀ i ∈ Finset.Ico (p + 1) (n - (q - p) + 1),
        φ (if i ≤ p then i else i + (q - p - 1)) = φ (i + (q - p - 1)) := by
      intro i hi; rw [Finset.mem_Ico] at hi; rw [ite_eq_right (by omega)]
    rw [Finset.prod_congr rfl e1, Finset.prod_congr rfl e2,
      Finset.prod_Ico_add' φ (p + 1) (n - (q - p) + 1) (q - p - 1),
      show p + 1 + (q - p - 1) = q by omega, show n - (q - p) + 1 + (q - p - 1) = n by omega]
  rw [h1, h2]
  -- split everything at `p`, `p + 1`, `q`, `q + 1`
  rw [← Finset.prod_range_mul_prod_Ico φ (show p + 1 ≤ n by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show p < q + 1 by omega),
    ← Finset.prod_Ico_consecutive φ (show p + 1 ≤ q + 1 by omega) (show q + 1 ≤ n by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show q < n by omega)]
  rw [← Finset.prod_Ico_consecutive φ (show p + 1 ≤ q by omega) (show q ≤ q + 1 by omega)]
  simp only [Nat.Ico_succ_singleton, Finset.prod_singleton]
  ring

include hL hm in
/-- **A diagonal pair** `(J.1+1, J.2+1)` of `(pro_dyncalK)` is the internal-edge term of `J`. -/
private theorem diag_pair_term {n : ℕ} [NeZero n] (hn : 3 ≤ n) (I : LoopIdx (Zd d L)) (hI : I.WF)
    (hlen : I.length = n) {J : Fin n × Fin n} (hJd : IsDiag n J.1 J.2) :
    (W : ℂ) ^ d * ∑ x : Zd d L, ∑ y : Zd d L,
        KLgen d L g W m t (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x) * SB d L g x y *
          KLgen d L g W m t (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y)
      = (∏ i, m (I.σ.getD (i : Fin n) false)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) *
          ∑ F ∈ (TSP n).filter (fun F => J ∈ F),
            (if h : J ∈ F then KLtreeValW d L F (fun i : Fin n => I.a.getD i 0)
              (fun v => thetaEdge d L g m t (I.σ.getD (v : Fin n) false)
                (I.σ.getD (v + 1 : Fin n) false))
              (Function.update (fun ed : ↥F => thetaEdge d L g m t (I.σ.getD ed.1.1 false)
                (I.σ.getD ed.1.2 false) - 1) ⟨J, h⟩
                (dTheta d L g m t (I.σ.getD J.1 false) (I.σ.getD J.2 false))) else 0) := by
  have hσl : I.σ.length = n := by rw [hI]; exact hlen
  have hal : I.a.length = n := hlen
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  have hw : KLwIn J = J.2.val - J.1.val := rfl
  have hwn : KLwIn J + 2 ≤ n := by
    obtain ⟨-, -, h3⟩ := hJd
    simp only [KLwIn]; by_contra h; apply h3; omega
  -- the chains
  let σi : Fin (KLwIn J + 1) → Bool := fun i => ((I.σ.drop J.1.val).take (KLwIn J + 1)).getD i false
  let ai : Zd d L → Fin (KLwIn J + 1) → Zd d L := fun y i =>
    ((I.a.drop J.1.val).take (KLwIn J) ++ [y]).getD i 0
  let σo : Fin (n - KLwIn J + 1) → Bool := fun i =>
    (I.σ.take (J.1.val + 1) ++ I.σ.drop J.2.val).getD i false
  let ao : Zd d L → Fin (n - KLwIn J + 1) → Zd d L := fun x i =>
    (I.a.take J.1.val ++ x :: I.a.drop J.2.val).getD i 0
  have hKR : ∀ y, KLgen d L g W m t (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y)
      = KLn d L g W m t (KLwIn J + 1) σi (ai y) := by
    intro y
    have hlenR : (I.cutGlueR (J.1.val + 1) (J.2.val + 1) y).length = KLwIn J + 1 := by
      rw [LoopIdx.length_cutGlueR I y (by omega) (by omega) (by omega)]; simp only [KLwIn]; omega
    rw [Kgen_eq W m t (by omega) _ hlenR]
    simp only [LoopIdx.cutGlueR, show J.1.val + 1 - 1 = J.1.val by omega,
      show J.2.val + 1 - (J.1.val + 1) = KLwIn J by simp only [KLwIn]; omega]
    rfl
  have hKL : ∀ x, KLgen d L g W m t (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x)
      = KLn d L g W m t (n - KLwIn J + 1) σo (ao x) := by
    intro x
    have hlenL : (I.cutGlueL (J.1.val + 1) (J.2.val + 1) x).length = n - KLwIn J + 1 := by
      rw [LoopIdx.length_cutGlueL I x (by omega) (by omega) (by omega)]; simp only [KLwIn]; omega
    rw [Kgen_eq W m t (by omega) _ hlenL]
    simp only [LoopIdx.cutGlueL, show J.1.val + 1 - 1 = J.1.val by omega,
      show J.2.val + 1 - 1 = J.2.val by omega]
    rfl
  -- the hypotheses of `internal_term`
  have hσi : ∀ i : Fin (KLwIn J + 1), σi i = I.σ.getD ((KLunShift J (i, i)).1 : Fin n) false := by
    intro i
    simp only [σi]
    rw [getD_drop_take i.isLt, (KLunShift_val (i, i)).1, add_comm]
  have hσo : ∀ i : Fin (n - KLwIn J + 1), σo i = I.σ.getD ((KLunColP J (i, i)).1 : Fin n) false := by
    intro i
    simp only [σo]
    rw [(KLunColP_val (i, i) hJ2).1]
    dsimp only
    have hi := i.isLt
    by_cases h : i.val ≤ J.1.val
    · rw [getD_take_append_of_lt (by omega) (by omega), KLunCol_of_le h]
    · rw [getD_take_append_of_ge (by omega) (by omega), getD_drop', KLunCol_of_gt (by omega)]
      congr 1; simp only [KLwIn]; omega
  have hai0 : ∀ u, ai u (Fin.last _) = u := by
    intro u
    simp only [ai, Fin.val_last]
    rw [getD_take_append_of_ge le_rfl (by simp; omega), Nat.sub_self]
    rfl
  have hai1 : ∀ u, ∀ v : KLLIn J, ai u (KLinV J v) = I.a.getD (v.1 : Fin n) 0 := by
    intro u v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := KLinV_val v.2
    simp only [ai]
    rw [h1, getD_take_append_of_lt (by simp only [KLwIn]; omega) (by simp; omega), getD_drop']
    congr 1; omega
  have hg : (KLglueV J).val = J.1.val := by simp only [KLglueV, KLwIn]; omega
  have hao0 : ∀ x, ao x (KLglueV J) = x := by
    intro x
    simp only [ao]
    rw [hg, getD_take_append_of_ge le_rfl (by omega), Nat.sub_self]
    rfl
  have hao1 : ∀ x, ∀ v : KLLOut J, ao x (KLoutV J v) = I.a.getD (v.1 : Fin n) 0 := by
    intro x v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    simp only [ao]
    rw [KLoutV_val v.1 hJ2]
    rcases hvs with h | h
    · rw [KLcol_of_le (by omega), getD_take_append_of_lt h (by omega)]
    · rw [KLcol_of_gt (by omega), getD_take_append_of_ge (by simp only [KLwIn]; omega) (by omega),
        show v.1.val - (KLwIn J - 1) - J.1.val = (v.1.val - J.2.val) + 1 by simp only [KLwIn]; omega,
        getD_cons_succ', getD_drop']
      congr 1; omega
  have hprod : (∏ i, m (σi i)) * ∏ i, m (σo i)
      = (∏ i, m (I.σ.getD (i : Fin n) false)) *
        (m (I.σ.getD J.1 false) * m (I.σ.getD J.2 false)) := by
    set φ : ℕ → ℂ := fun j => m (I.σ.getD j false) with hφdef
    have e1 : ∏ i, m (σi i) = ∏ i ∈ Finset.range (J.2.val - J.1.val + 1), φ (J.1.val + i) := by
      rw [← Fin.prod_univ_eq_prod_range (fun j => φ (J.1.val + j))]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [σi, φ]; rw [getD_drop_take i.isLt]
    have e2 : ∏ i, m (σo i) = ∏ i ∈ Finset.range (n - (J.2.val - J.1.val) + 1),
        φ (if i ≤ J.1.val then i else i + (J.2.val - J.1.val - 1)) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun j => φ (if j ≤ J.1.val then j else j + (J.2.val - J.1.val - 1)))]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hσo i, (KLunColP_val (i, i) hJ2).1]
      simp only [φ, KLunCol, KLwIn]
    have e3 : ∏ i, m (I.σ.getD (i : Fin n) false) = ∏ i ∈ Finset.range n, φ i :=
      Fin.prod_univ_eq_prod_range φ n
    rw [e1, e2, e3, prod_chains φ hJw hJn]
  rw [internal_term hL W m hm (by omega) hJd _ _ σi ai σo ao hσi hσo hai0 hai1 hao0 hao1 hprod]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hKL, hKR]

include hL hm in
/-- **The ODE**: for every loop of length `n ≥ 3` the tree representation `KLgen` satisfies
`(pro_dyncalK)`. -/
private theorem hasDerivAt_Kgen (I : LoopIdx (Zd d L)) (hI : I.WF) (h3 : 3 ≤ I.length) :
    HasDerivAt (fun r => KLgen d L g W m r I) (treeEqRhs d L W g (KLgen d L g W m t) I) t := by
  set n := I.length with hn
  have : NeZero n := ⟨by omega⟩
  set σF : Fin n → Bool := fun i => I.σ.getD i false with hσF
  set aF : Fin n → Zd d L := fun i => I.a.getD i 0 with haF
  have hfun : (fun r => KLgen d L g W m r I) = fun r => KLn d L g W m r n σF aF :=
    funext fun r => Kgen_eq W m r h3 I rfl
  rw [hfun]
  refine (hasDerivAt_Kn hL W m hm σF aF).congr_deriv ?_
  -- the derivative: leaf terms and edge terms
  rw [Finset.sum_add_distrib, mul_add, Finset.sum_comm, Finset.mul_sum,
    sum_edges_swap (fun F ed => KLtreeValW d L F aF (fun v => thetaEdge d L g m t (σF v) (σF (v + 1)))
      (Function.update (fun ed : ↥F => thetaEdge d L g m t (σF ed.1.1) (σF ed.1.2) - 1) ed
        (dTheta d L g m t (σF ed.1.1) (σF ed.1.2)))), Finset.mul_sum]
  -- `(pro_dyncalK)`: leaf pairs, the root pair and the diagonals
  rw [treeEqRhs, ← hn, sum_pairs h3 (fun k l => ∑ x : Zd d L, ∑ y : Zd d L,
      KLgen d L g W m t (I.cutGlueL k l x) * SB d L g x y * KLgen d L g W m t (I.cutGlueR k l y)),
    mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [leaf_term W m σF aF v]
    simp only [leafPair]
    split_ifs with hv
    · exact (leaf_pair_term W m (t := t) h3 I hI rfl v hv).symm
    · exact (root_pair_term hL W m hm h3 I hI rfl v (by have := v.isLt; omega)).symm
  · refine Finset.sum_congr rfl fun J hJ => ?_
    exact (diag_pair_term hL W m hm h3 I hI rfl (KLmem_diagonals_iff.1 hJ)).symm

end Lists

section Final

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem prod_getD_eq {α : Type*} (l : List α) (f : α → ℂ) (ed : α) {n : ℕ}
    (h : l.length = n) :
    ∏ i : Fin n, f (l.getD i ed) = (l.map f).prod := by
  subst h
  rw [← List.prod_ofFn]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

private theorem allEq_iff {α : Type*} (l : List α) (ed : α) {n : ℕ} (h : l.length = n) (hn : 0 < n) :
    (∀ x ∈ l, ∀ y ∈ l, x = y) ↔ ∀ i : Fin n, l.getD i ed = l.getD 0 ed := by
  subst h
  constructor
  · intro H i
    rw [List.getD_eq_getElem _ _ i.isLt, List.getD_eq_getElem _ _ hn]
    exact H _ (List.getElem_mem _) _ (List.getElem_mem _)
  · intro H x hx y hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    have h1 := H ⟨i, hi⟩
    have h2 := H ⟨j, hj⟩
    rw [List.getD_eq_getElem _ _ hi] at h1
    rw [List.getD_eq_getElem _ _ hj] at h2
    rw [h1, h2]

/-- The star with identity matrices: `∑_b ∏_v δ_{a_v b} = 1(all a_v equal)`. -/
private theorem star_one {n : ℕ} [NeZero n] (a : Fin n → Zd d L) :
    ∑ b : Zd d L, ∏ v : Fin n, (1 : Matrix (Zd d L) (Zd d L) ℂ) (a v) b
      = if ∀ v, a v = a 0 then 1 else 0 := by
  simp only [Matrix.one_apply, Finset.prod_boole, Finset.mem_univ, true_imp_iff]
  rw [Finset.sum_eq_single (a 0)]
  · intro b _ hb
    exact ite_eq_right (fun h => hb (h 0).symm)
  · intro h; exact absurd (Finset.mem_univ _) h

variable (W : ℕ) [NeZero W] (m : Bool → ℂ)

private theorem thetaEdge_zero (s s' : Bool) : thetaEdge d L g m 0 s s' = 1 := by
  simp [thetaEdge, Theta_zero]

omit [NeZero W] in
/-- **The initial value** of the tree representation: at `t = 0` all internal edges vanish,
only the star survives, and it is `1(a₁ = ⋯ = aₙ)`. -/
private theorem Kn_zero {n : ℕ} [NeZero n] (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    KLn d L g W m 0 n σ a = (∏ i, m (σ i)) * ((W : ℂ) ^ d)⁻¹ ^ (n - 1) *
      (if ∀ v, a v = a 0 then 1 else 0) := by
  rw [KLn]
  congr 1
  rw [Finset.sum_eq_single ∅]
  · rw [KLtreeValG, KLtreeValW_empty]
    simp only [thetaEdge_zero]
    exact star_one a
  · intro F _ hF
    obtain ⟨ed, hd⟩ := Finset.nonempty_iff_ne_empty.2 hF
    rw [KLtreeValG, KLtreeValW]
    refine Finset.sum_eq_zero fun b _ => ?_
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ (⟨ed, hd⟩ : ↥F)) ?_)
    simp [thetaEdge_zero]
  · intro h; exact absurd (empty_mem_TSP n) h

omit [NeZero W] in
private theorem Kgen_zero (I : LoopIdx (Zd d L)) (hI : I.WF) (h2 : 2 ≤ I.length) :
    KLgen d L g W m 0 I = MLoop d L W m I := by
  rcases Nat.lt_or_ge I.length 3 with h | h
  · -- `n = 2`
    have hlen : I.length = 2 := by omega
    obtain ⟨σ, a⟩ := I
    have ha : a.length = 2 := hlen
    have hσ : σ.length = 2 := hI.trans ha
    obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 ha
    obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
    rw [Kgen_two]
    exact kTwo_zero m s₁ s₂ x₁ x₂
  · -- `n ≥ 3`
    have : NeZero I.length := ⟨by omega⟩
    have hσl : I.σ.length = I.length := hI
    have hall : (∀ v : Fin I.length, I.a.getD v 0 = I.a.getD ((0 : Fin I.length) : ℕ) 0)
        ↔ ∀ x ∈ I.a, ∀ y ∈ I.a, x = y := by
      rw [Fin.val_zero]
      exact (allEq_iff I.a 0 (n := I.length) rfl (by omega)).symm
    rw [Kgen_eq W m 0 h I rfl, Kn_zero, MLoop, prod_getD_eq I.σ m false hσl]
    simp only [hall]
    ring

variable (hL : 3 ≤ L) {t : ℝ} (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hm

/-- `n = 2`: the tree representation is `(Kn2sol)`, which solves `(pro_dyncalK)`. -/
private theorem hasDerivAt_Kgen_two (I : LoopIdx (Zd d L)) (hI : I.WF) (h2 : I.length = 2) :
    HasDerivAt (fun r => KLgen d L g W m r I) (treeEqRhs d L W g (KLgen d L g W m t) I) t := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 2 := h2
  have hσ : σ.length = 2 := hI.trans ha
  obtain ⟨x₁, x₂, rfl⟩ := List.length_eq_two.1 ha
  obtain ⟨s₁, s₂, rfl⟩ := List.length_eq_two.1 hσ
  have hfun : (fun r => KLgen d L g W m r ⟨[s₁, s₂], [x₁, x₂]⟩)
      = fun r => kTwo d L W g m r s₁ s₂ x₁ x₂ := funext fun r => Kgen_two W m r _ _ _ _
  rw [hfun, treeEqRhs_two]
  simp only [Kgen_two]
  exact hasDerivAt_kTwo (norm_SB d L g hL) (pow_ne_zero d (Nat.cast_ne_zero.2 (NeZero.ne W))) m
    s₁ s₂ (hm _ _) x₁ x₂

/-- **`(pro_dyncalK)` for the tree representation, every `n ≥ 2`.** -/
private theorem hasDerivAt_Kgen_all (I : LoopIdx (Zd d L)) (hI : I.WF) (h2 : 2 ≤ I.length) :
    HasDerivAt (fun r => KLgen d L g W m r I) (treeEqRhs d L W g (KLgen d L g W m t) I) t := by
  rcases Nat.lt_or_ge I.length 3 with h | h
  · exact hasDerivAt_Kgen_two W m hL hm I hI (by omega)
  · exact hasDerivAt_Kgen hL W m hm I hI h

end Final
/-! ## 3. The pinned theorem -/

section Pinned

/-- **Pin `Def_Ktza`** (`(pro_dyncalK)`, `(calGonIND)`, `(eq:initial_K)`, `(eq:KMloop)`): the tree
sum `KLK` solves the convolution tree equations on `t ∈ [0,1)`, takes the `M`-loop value at
`t = 0`, and `𝒦^{(1)} = m(σ)`.  (The paper writes `t ∈ [0,1]`; `Θ_1` does not exist.) -/
theorem KLK_isKLoop :
    ∀ (d L W : ℕ) [NeZero L] (g E : ℝ), 3 ≤ L → 1 ≤ W → |E| < 2 →
      IsKLoop d L W g (mSigma E) (Set.Ico 0 1) (fun t I => KLK d L g W E t I) := by
  intro d L W _ g E hL hW hE
  have : NeZero W := ⟨by omega⟩
  have hE2 : |E| ≤ 2 := hE.le
  refine ⟨fun t ht I hI h2 => ?_, fun I hI h2 => Kgen_zero W (mSigma E) I hI h2,
    fun t _ s a => KLK_one d L g W E t s a⟩
  have hm : ∀ s s' : Bool, ‖(t : ℂ) * (mSigma E s * mSigma E s')‖ < 1 := fun s s' =>
    norm_mul_mSigma_lt_one hE2 ht.1 ht.2 s s'
  exact hasDerivAt_Kgen_all W (mSigma E) hL hm I hI h2

end Pinned

/-! ## 4. The compiled instances: `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`

`L = 5` (`125` blocks), `W = 2` (`W^d = 8`), `m(+) = i`.  Every hypothesis of `KLK_isKLoop`
(`3 ≤ 5`, `1 ≤ 2`, `|0| < 2`) is discharged; the three clauses are applied at `t = 9/10`, at the left
end point `t = 0` of `[0,1)`, to loops of length `2`, `3`, `4` with alternating charges and distinct
labels, and to constant and non-constant labels at `t = 0`. -/

section Instances

/-- `m(+) = m^{(0)} = i` at the energy `E = 0`. -/
private theorem mE_zero_eq : mE 0 = Complex.I := by
  simp only [mE]
  have h : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]; push_cast; simp

/-- **The instance of `KLK_isKLoop`**: `𝒦` is a family of `K`-loops on `[0,1)` at the data above. -/
theorem KLTreeDerivInst_isKLoop :
    IsKLoop 3 5 2 (1 / 2) (mSigma 0) (Set.Ico 0 1) (fun t I => KLK 3 5 (1 / 2) 2 0 t I) :=
  KLK_isKLoop 3 5 2 (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)

/-- Clause 1 (`(pro_dyncalK)`) at `t = 9/10`, loop `(+,-)`, labels `(0, 1)`. -/
theorem KLTreeDerivInst_ode_two :
    HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s ⟨[true, false], [0, 1]⟩)
      (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        ⟨[true, false], [0, 1]⟩) (9 / 10) :=
  KLTreeDerivInst_isKLoop.1 (9 / 10) ⟨by norm_num, by norm_num⟩ _ rfl (le_refl 2)

/-- Clause 1 at `t = 9/10`, loop `(+,-,+)`, labels `(0, 1, 2)`: the tree `F = ∅` only. -/
theorem KLTreeDerivInst_ode_three :
    HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 KLinstσ KLinsta))
      (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 KLinstσ KLinsta)) (9 / 10) :=
  KLTreeDerivInst_isKLoop.1 (9 / 10) ⟨by norm_num, by norm_num⟩ _ (by simp [LoopIdx.WF, KLloopOf])
    (by simp [LoopIdx.length, KLloopOf])

/-- Clause 1 at `t = 9/10`, loop `(+,-,+,-)`, labels `(0, 1, 2, 3)`: three trees, among them the
two with an internal edge `(0,2)` or `(1,3)`. -/
theorem KLTreeDerivInst_ode_four :
    HasDerivAt
      (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3]))
      (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 (9 / 10) I)
        (KLloopOf 3 5 ![true, false, true, false] ![0, 1, 2, 3])) (9 / 10) :=
  KLTreeDerivInst_isKLoop.1 (9 / 10) ⟨by norm_num, by norm_num⟩ _ (by simp [LoopIdx.WF, KLloopOf])
    (by simp [LoopIdx.length, KLloopOf])

/-- Clause 1 at the left end point `t = 0 ∈ [0,1)`, loop `(+,-,+)`, labels `(0, 1, 2)`. -/
theorem KLTreeDerivInst_ode_zero :
    HasDerivAt (fun s => KLK 3 5 (1 / 2) 2 0 s (KLloopOf 3 5 KLinstσ KLinsta))
      (treeEqRhs 3 5 2 (1 / 2) (fun I => KLK 3 5 (1 / 2) 2 0 0 I)
        (KLloopOf 3 5 KLinstσ KLinsta)) 0 :=
  KLTreeDerivInst_isKLoop.1 0 ⟨le_refl 0, by norm_num⟩ _ (by simp [LoopIdx.WF, KLloopOf])
    (by simp [LoopIdx.length, KLloopOf])

/-- Clause 2 (`(eq:initial_K)`) on the constant-label loop `(+,-,+)`, labels `(0, 0, 0)`:
`𝒦_0 = (W^d)^{-2} m(+) m(-) m(+) = i / 64`. -/
theorem KLTreeDerivInst_init_const :
    KLK 3 5 (1 / 2) 2 0 0 ⟨[true, false, true], [0, 0, 0]⟩ = Complex.I / 64 := by
  have h : KLK 3 5 (1 / 2) 2 0 0 ⟨[true, false, true], [0, 0, 0]⟩
      = MLoop 3 5 2 (mSigma 0) ⟨[true, false, true], [0, 0, 0]⟩ :=
    KLTreeDerivInst_isKLoop.2.1 ⟨[true, false, true], [0, 0, 0]⟩ rfl (by simp [LoopIdx.length])
  rw [h]
  simp [MLoop, mSigma, mE_zero_eq, LoopIdx.length]
  ring

/-- Clause 2 on the loop `(+,-,+)` with three distinct labels `(0, 1, 2)`: `𝒦_0 = 0`. -/
theorem KLTreeDerivInst_init_nonconst :
    KLK 3 5 (1 / 2) 2 0 0 (KLloopOf 3 5 KLinstσ KLinsta) = 0 := by
  have h : KLK 3 5 (1 / 2) 2 0 0 (KLloopOf 3 5 KLinstσ KLinsta)
      = MLoop 3 5 2 (mSigma 0) (KLloopOf 3 5 KLinstσ KLinsta) :=
    KLTreeDerivInst_isKLoop.2.1 _ (by simp [LoopIdx.WF, KLloopOf]) (by simp [LoopIdx.length, KLloopOf])
  rw [h]
  have hne : ¬ ∀ x ∈ (KLloopOf 3 5 KLinstσ KLinsta).a, ∀ y ∈ (KLloopOf 3 5 KLinstσ KLinsta).a,
      x = y := by
    intro H
    have := H 0 (by simp [KLloopOf, KLinsta]) 1 (by simp [KLloopOf, KLinsta])
    have h2 : (0 : ZMod 5) = 1 := by simpa using congrFun this 0
    exact absurd h2 (by decide)
  simp [MLoop, hne]

/-- Clause 3 (`𝒦^{(1)} = m(σ)`) at `t = 9/10`: `𝒦^{(1)}_{t,+,0} = m(+) = i`. -/
theorem KLTreeDerivInst_one :
    KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ = Complex.I := by
  have h : KLK 3 5 (1 / 2) 2 0 (9 / 10) ⟨[true], [0]⟩ = mSigma 0 true :=
    KLTreeDerivInst_isKLoop.2.2 (9 / 10) ⟨by norm_num, by norm_num⟩ true 0
  rw [h]
  simp [mSigma, mE_zero_eq]

end Instances

end RBM.Loop
