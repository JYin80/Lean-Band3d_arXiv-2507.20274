/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Kernel.Evolution
import RBM3D.Induction.NewPQ
import RBM3D.Induction.GridDuhamelN

/-!
# The zero-mode calculus of Step 3, case `1 - s ≤ ilambda²/L²` (`d ≥ 3`)

Ticket T2112 (S3-20).  Paper: arXiv:2507.20274, `3_5:1435-1601`
(`def;zero_mode_remove`, `(normQA2)`, the commutation remark `3_5:1540-1545`,
`(eq_L-Keee_nonzeromode)`, `(iisuwjyys)`, and the combination at `3_5:1590`).  No RBM1D/RBM2D
source: the zero-mode regime does not exist for `d ≤ 2` (portmap P.7 row S3-20).

`Q^{(A)}` is the merged `RBM.zeroModeSet` (`RBM3D/Kernel/Evolution.lean:199`).  Targets:

1. `(normQA2)`: `norm_zeroModeOp_le`, `norm_zeroModeSet_le` (`‖Q^{(A)} 𝒜‖_∞ ≤ 2^{|A|} ‖𝒜‖_∞`), and
   linearity (`zeroModeSet_add`, `zeroModeSet_smul`, `zeroModeSetLin`, `zeroModeSet_sub`,
   `zeroModeSet_sum`).
2. Commutation: `zeroModeSet_UN`, `zeroModeSet_ThetaN`, `Ind.zeroModeSet_Ugen` (and the
   single-index forms `zeroModeOp_UN`, `zeroModeOp_ThetaN`, `Ind.zeroModeOp_Ugen`): `Q^{(A)}`
   commutes with `𝒰^{(n)}`, `Θ^{(n)}`.  The ingredients are `ZeroModeCalc_tensorKer_zeroModeOp`
   (`Q^{(i)}` acting on the right of a tensor kernel; the merged `zeroModeOp_tensorKer` is the
   left-hand identity) and `ZeroModeCalc_projMat_mul_Theta_comm` (`Proj_{e^⊥}` commutes with
   `Θ_ξ`; the merged `projMat_mul_Theta` gives `Proj_{e^⊥} Θ_ξ = Θ̊_ξ` only).
3. `(iisuwjyys)` on the grid: `Ind.zeroModeCalc_duhamel_at` (`Q^{(A)}` outside `𝒰`),
   `Ind.zeroModeCalc_duhamel_inside_at` (`Q^{(A)}` inside `𝒰`, by target 2).
4. The combination with `lem: newPQ` (`3_5:1590`): `Gauss.Sizes.zeroModeCalc_LK_expansion` for every
   `A`, and `Gauss.Sizes.zeroModeCalc_LK_expansion_empty` for `A = ∅`;
   `sameSignOutside_of_STIdiff_subset` and `sameSignOutside_union_STIdiff` are the bridge to
   `RBM.SameSignOutside` (the hypothesis of `norm_zeroModeSet_UN_le` also needs `0 < Im m_i`, false
   for `mSigma E false`; the consumer form for mixed signs is `ekSumDecayNonzero_holds` with
   `Ind.Ugen_eq_UN_EKsgn`).

Every helper that is not a target is `private` (`zmc…`) or prefixed `ZeroModeCalc_`.
-/

set_option linter.style.longLine false

namespace RBM

open Matrix

/-! ## 1. `(normQA2)` and linearity of `Q^{(A)}` -/

section Linear

variable {d L : ℕ} [NeZero L] {n : ℕ}

theorem ZeroModeCalc_zeroModeOp_add (i : Fin n) (S T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (S + T) = zeroModeOp d L i S + zeroModeOp d L i T := by
  funext a
  simp only [zeroModeOp, avgOp, Pi.add_apply, Finset.sum_add_distrib, mul_add]
  ring

theorem ZeroModeCalc_zeroModeOp_smul (i : Fin n) (c : ℂ) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (c • T) = c • zeroModeOp d L i T := by
  funext a
  simp only [zeroModeOp, avgOp, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

/-- `Q^{(i)}` as a `ℂ`-linear map on `n`-index tensors. -/
noncomputable def ZeroModeCalc_zeroModeOpLin (i : Fin n) :
    ((Fin n → Zd d L) → ℂ) →ₗ[ℂ] ((Fin n → Zd d L) → ℂ) where
  toFun := zeroModeOp d L i
  map_add' := ZeroModeCalc_zeroModeOp_add i
  map_smul' := ZeroModeCalc_zeroModeOp_smul i

theorem ZeroModeCalc_zeroModeOp_sum {ι : Type*} (s : Finset ι) (i : Fin n) (F : ι → (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (∑ x ∈ s, F x) = ∑ x ∈ s, zeroModeOp d L i (F x) :=
  map_sum (ZeroModeCalc_zeroModeOpLin (d := d) (L := L) i) F s

private theorem zmc_foldr_add (l : List (Fin n)) (S T : (Fin n → Zd d L) → ℂ) :
    l.foldr (fun i f => zeroModeOp d L i f) (S + T)
      = l.foldr (fun i f => zeroModeOp d L i f) S + l.foldr (fun i f => zeroModeOp d L i f) T := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, ZeroModeCalc_zeroModeOp_add]

private theorem zmc_foldr_smul (l : List (Fin n)) (c : ℂ) (T : (Fin n → Zd d L) → ℂ) :
    l.foldr (fun i f => zeroModeOp d L i f) (c • T)
      = c • l.foldr (fun i f => zeroModeOp d L i f) T := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [List.foldr_cons, List.foldr_cons, ih, ZeroModeCalc_zeroModeOp_smul]

/-- `Q^{(A)}` is additive. -/
theorem zeroModeSet_add (A : Finset (Fin n)) (S T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (S + T) = zeroModeSet d L A S + zeroModeSet d L A T :=
  zmc_foldr_add _ S T

/-- `Q^{(A)}` is homogeneous. -/
theorem zeroModeSet_smul (A : Finset (Fin n)) (c : ℂ) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (c • T) = c • zeroModeSet d L A T :=
  zmc_foldr_smul _ c T

/-- `Q^{(A)}` as a `ℂ`-linear map on `n`-index tensors. -/
noncomputable def zeroModeSetLin (A : Finset (Fin n)) :
    ((Fin n → Zd d L) → ℂ) →ₗ[ℂ] ((Fin n → Zd d L) → ℂ) where
  toFun := zeroModeSet d L A
  map_add' := zeroModeSet_add A
  map_smul' := zeroModeSet_smul A

theorem zeroModeSet_zero (A : Finset (Fin n)) : zeroModeSet d L A (0 : (Fin n → Zd d L) → ℂ) = 0 :=
  map_zero (zeroModeSetLin (d := d) (L := L) A)

theorem zeroModeSet_sub (A : Finset (Fin n)) (S T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (S - T) = zeroModeSet d L A S - zeroModeSet d L A T :=
  map_sub (zeroModeSetLin (d := d) (L := L) A) S T

theorem zeroModeSet_sum {ι : Type*} (s : Finset ι) (A : Finset (Fin n))
    (F : ι → (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (∑ x ∈ s, F x) = ∑ x ∈ s, zeroModeSet d L A (F x) :=
  map_sum (zeroModeSetLin (d := d) (L := L) A) F s

@[simp] theorem zeroModeSet_empty (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L (∅ : Finset (Fin n)) T = T := by
  simp [zeroModeSet]

/-- **`(normQA2)`, one index** (`3_5:1454`): `‖Q^{(i)} 𝒜‖_∞ ≤ 2 ‖𝒜‖_∞`. -/
theorem norm_zeroModeOp_le (i : Fin n) (T : (Fin n → Zd d L) → ℂ) :
    ‖zeroModeOp d L i T‖ ≤ 2 * ‖T‖ := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by
      have := NeZero.ne L
      have : 0 < L := Nat.pos_of_ne_zero this
      exact_mod_cast this
    positivity
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  have hsum : ‖∑ c : Zd d L, T (Function.update a i c)‖ ≤ (L : ℝ) ^ d * ‖T‖ := by
    calc ‖∑ c : Zd d L, T (Function.update a i c)‖
        ≤ ∑ c : Zd d L, ‖T (Function.update a i c)‖ := norm_sum_le _ _
      _ ≤ ∑ _c : Zd d L, ‖T‖ := Finset.sum_le_sum fun c _ => norm_le_pi_norm T _
      _ = (L : ℝ) ^ d * ‖T‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          show ((Fintype.card (Zd d L) : ℕ) : ℝ) = (L : ℝ) ^ d by simp [ZMod.card]]
  have hinv : ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ := by simp
  calc ‖zeroModeOp d L i T a‖
      = ‖T a - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update a i c)‖ := rfl
    _ ≤ ‖T a‖ + ‖((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update a i c)‖ := norm_sub_le _ _
    _ ≤ ‖T‖ + ((L : ℝ) ^ d)⁻¹ * ((L : ℝ) ^ d * ‖T‖) := by
        rw [norm_mul, hinv]
        exact add_le_add (norm_le_pi_norm T a)
          (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = 2 * ‖T‖ := by field_simp; ring

private theorem zmc_norm_foldr_le (l : List (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    ‖l.foldr (fun i f => zeroModeOp d L i f) T‖ ≤ 2 ^ l.length * ‖T‖ := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.foldr_cons, List.length_cons, pow_succ]
    calc ‖zeroModeOp d L j (l.foldr (fun i f => zeroModeOp d L i f) T)‖
        ≤ 2 * ‖l.foldr (fun i f => zeroModeOp d L i f) T‖ := norm_zeroModeOp_le j _
      _ ≤ 2 * (2 ^ l.length * ‖T‖) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 2 ^ l.length * 2 * ‖T‖ := by ring

/-- **`(normQA2)`** (`3_5:1454`): `‖Q^{(A)} ∘ 𝒜‖_∞ ≤ 2^{|A|} ‖𝒜‖_∞` for `Q^{(A)} = ∏_{i ∈ A} Q^{(i)}`
(each factor has `(∞→∞)`-norm at most `2`; sup norm on `(Fin n → Z_L^d) → ℂ`). -/
theorem norm_zeroModeSet_le (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    ‖zeroModeSet d L A T‖ ≤ 2 ^ A.card * ‖T‖ := by
  have h := zmc_norm_foldr_le A.toList T
  rwa [Finset.length_toList] at h

end Linear

/-! ## 2. `Q^{(i)}` on the right of a tensor kernel, and the commutation with `𝒰^{(n)}`, `Θ^{(n)}` -/

section Commute

variable {d L : ℕ} [NeZero L] {g : ℝ} {n : ℕ}

/-- Reindexing of `Σ_b Σ_c G(b[i ↦ c], b_i)` as `Σ_b Σ_y G(b, y)` (the involution
`(b, c) ↦ (b[i ↦ c], b_i)` of `(Z_L^d)^n × Z_L^d`). -/
private theorem zmc_sum_update (i : Fin n) (G : (Fin n → Zd d L) → Zd d L → ℂ) :
    ∑ b : Fin n → Zd d L, ∑ c : Zd d L, G (Function.update b i c) (b i)
      = ∑ b : Fin n → Zd d L, ∑ y : Zd d L, G b y := by
  let e : ((Fin n → Zd d L) × Zd d L) ≃ ((Fin n → Zd d L) × Zd d L) :=
    { toFun := fun p => (Function.update p.1 i p.2, p.1 i)
      invFun := fun p => (Function.update p.1 i p.2, p.1 i)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have h := Equiv.sum_comp e (fun p => G p.1 p.2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  exact h

/-- `(M (I - L^{-d} J))_{xy} = M_{xy} - L^{-d} Σ_c M_{xc}`. -/
private theorem zmc_mul_projMat_apply (M : Matrix (Zd d L) (Zd d L) ℂ) (x y : Zd d L) :
    (M * projMat d L) x y = M x y - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, M x c := by
  simp only [projMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
    mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul]
  ring

/-- `((I - L^{-d} J) M)_{xy} = M_{xy} - L^{-d} Σ_c M_{cy}`. -/
private theorem zmc_projMat_mul_apply (M : Matrix (Zd d L) (Zd d L) ℂ) (x y : Zd d L) :
    (projMat d L * M) x y = M x y - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, M c y := by
  simp only [projMat, Matrix.sub_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.of_apply,
    sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.mul_sum]

/-- Commutation with `I - L^{-d} J` says that column sums equal row sums. -/
private theorem zmc_sum_col_eq_row {M : Matrix (Zd d L) (Zd d L) ℂ}
    (h : projMat d L * M = M * projMat d L) (x y : Zd d L) :
    ∑ c : Zd d L, M c y = ∑ c : Zd d L, M x c := by
  have hL0 : ((L : ℂ) ^ d)⁻¹ ≠ 0 := by
    have : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    exact inv_ne_zero (pow_ne_zero _ this)
  have h1 := congrFun (congrFun h x) y
  rw [zmc_projMat_mul_apply, zmc_mul_projMat_apply] at h1
  exact mul_left_cancel₀ hL0 (sub_right_injective h1)

/-- **`Q^{(i)}` on the right of a tensor kernel**: `K ∘ Q^{(i)} = K[i ↦ K_i (I - L^{-d} J)]`.
(The merged `zeroModeOp_tensorKer` is the left-hand identity.) -/
theorem ZeroModeCalc_tensorKer_zeroModeOp (i : Fin n) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (T : (Fin n → Zd d L) → ℂ) :
    tensorKer d L K (zeroModeOp d L i T)
      = tensorKer d L (Function.update K i (K i * projMat d L)) T := by
  funext a
  set R : (Fin n → Zd d L) → ℂ := fun b => ∏ j ∈ Finset.univ.erase i, K j (a j) (b j) with hR
  have hRupd : ∀ b c, R (Function.update b i c) = R b := fun b c =>
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hsplit : ∀ F : Fin n → ℂ, ∏ j, F j = F i * ∏ j ∈ Finset.univ.erase i, F j := fun F => by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hF : ∀ b, (∏ j, K j (a j) (b j)) = K i (a i) (b i) * R b := fun b =>
    hsplit (fun j => K j (a j) (b j))
  have hF' : ∀ b, (∏ j, Function.update K i (K i * projMat d L) j (a j) (b j))
      = (K i * projMat d L) (a i) (b i) * R b := by
    intro b
    rw [hsplit fun j => Function.update K i (K i * projMat d L) j (a j) (b j)]
    simp only [Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  have hm : ∀ x y : Zd d L, (K i * projMat d L) x y
      = K i x y - ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, K i x c := fun x y => zmc_mul_projMat_apply _ x y
  have hcross : ∑ b : Fin n → Zd d L, K i (a i) (b i) * R b *
        (((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update b i c))
      = ((L : ℂ) ^ d)⁻¹ * ∑ b : Fin n → Zd d L, (∑ y : Zd d L, K i (a i) y) * R b * T b := by
    have h1 : ∀ b : Fin n → Zd d L, K i (a i) (b i) * R b *
          (((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update b i c))
        = ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L,
            (K i (a i) (b i) * R (Function.update b i c) * T (Function.update b i c)) := by
      intro b
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hRupd]; ring
    rw [Finset.sum_congr rfl fun b _ => h1 b, ← Finset.mul_sum]
    congr 1
    rw [zmc_sum_update i (fun b' y => K i (a i) y * R b' * T b')]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  simp only [tensorKer, zeroModeOp, avgOp, hF, hF', hm, mul_sub, Finset.sum_sub_distrib, sub_mul]
  refine congrArg₂ (· - ·) rfl ?_
  rw [hcross]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `Q^{(i)}` commutes with a tensor kernel whose `i`-th factor commutes with `I - L^{-d} J`. -/
theorem ZeroModeCalc_zeroModeOp_tensorKer_comm (i : Fin n) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (hK : projMat d L * K i = K i * projMat d L) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (tensorKer d L K T) = tensorKer d L K (zeroModeOp d L i T) := by
  rw [zeroModeOp_tensorKer, ZeroModeCalc_tensorKer_zeroModeOp, hK]

/-- If a map commutes with each `Q^{(j)}`, `j ∈ A`, it commutes with `Q^{(A)}`. -/
theorem ZeroModeCalc_zeroModeSet_comm_of_comm
    (Φ : ((Fin n → Zd d L) → ℂ) → ((Fin n → Zd d L) → ℂ)) (A : Finset (Fin n))
    (h : ∀ j ∈ A, ∀ T, zeroModeOp d L j (Φ T) = Φ (zeroModeOp d L j T))
    (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (Φ T) = Φ (zeroModeSet d L A T) := by
  have key : ∀ l : List (Fin n),
      (∀ j ∈ l, ∀ T, zeroModeOp d L j (Φ T) = Φ (zeroModeOp d L j T)) →
      l.foldr (fun i f => zeroModeOp d L i f) (Φ T)
        = Φ (l.foldr (fun i f => zeroModeOp d L i f) T) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons j l ih =>
      intro hl
      rw [List.foldr_cons, List.foldr_cons,
        ih (fun k hk => hl k (List.mem_cons_of_mem _ hk)),
        hl j (List.mem_cons_self ..)]
  exact key A.toList fun j hj => h j (Finset.mem_toList.mp hj)

/-- **`Q^{(A)}` commutes with a tensor kernel** whose factors at the indices of `A` commute with
`I - L^{-d} J`. -/
theorem ZeroModeCalc_zeroModeSet_tensorKer_comm (A : Finset (Fin n)) (K : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (hK : ∀ i ∈ A, projMat d L * K i = K i * projMat d L) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (tensorKer d L K T) = tensorKer d L K (zeroModeSet d L A T) :=
  ZeroModeCalc_zeroModeSet_comm_of_comm (tensorKer d L K) A
    (fun j hj T' => ZeroModeCalc_zeroModeOp_tensorKer_comm j K (hK j hj) T') T

/-- A matrix with all row sums and all column sums equal to `c` commutes with `I - L^{-d} J`. -/
theorem ZeroModeCalc_projMat_comm_of_sums (M : Matrix (Zd d L) (Zd d L) ℂ) (c : ℂ)
    (hrow : ∀ a, ∑ b, M a b = c) (hcol : ∀ b, ∑ a, M a b = c) :
    projMat d L * M = M * projMat d L := by
  ext a b
  rw [zmc_projMat_mul_apply, zmc_mul_projMat_apply, hcol, hrow]

/-- **`Proj_{e^⊥}` commutes with `Θ_ξ`** (`3_5:1540-1545`): `Θ_ξ` is symmetric with all row (and
column) sums `(1 - ξ)⁻¹`.  The merged `projMat_mul_Theta` gives the left-hand side as `Θ̊_ξ`. -/
theorem ZeroModeCalc_projMat_mul_Theta_comm (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    projMat d L * Theta d L g ξ = Theta d L g ξ * projMat d L := by
  have hT := Theta_transpose_of_three_le (d := d) (L := L) (g := g) hL hξ
  refine ZeroModeCalc_projMat_comm_of_sums _ ((1 - ξ)⁻¹) (fun a => sum_Theta_row_of_three_le hL hξ a)
    fun b => ?_
  have hsym : ∀ a : Zd d L, Theta d L g ξ a b = Theta d L g ξ b a := fun a => by
    have := congrFun (congrFun hT b) a
    simpa using this
  rw [Finset.sum_congr rfl fun a _ => hsym a]
  exact sum_Theta_row_of_three_le hL hξ b

/-- `Proj_{e^⊥}` commutes with `(1 - s μ S^{(B)}) Θ_{tμ}`, the one-index factor of `𝒰^{(n)}`. -/
theorem ZeroModeCalc_projMat_mul_uKer_comm (hL : 3 ≤ L) {μ : ℂ} {s t : ℝ} (hξ : ‖(t : ℂ) * μ‖ < 1) :
    projMat d L * uKer d L g μ s t = uKer d L g μ s t * projMat d L := by
  have hS : Commute (projMat d L) (SB d L g) := projMat_mul_SB_comm hL
  have hΘ : Commute (projMat d L) (Theta d L g ((t : ℂ) * μ)) := ZeroModeCalc_projMat_mul_Theta_comm hL hξ
  exact ((Commute.sub_right (Commute.one_right _) (Commute.smul_right hS _)).mul_right hΘ)

/-- `Proj_{e^⊥}` commutes with `μ S^{(B)} Θ_{tμ}`, the one-index factor of `Θ^{(n)}`. -/
theorem ZeroModeCalc_projMat_mul_thetaKer_comm (hL : 3 ≤ L) {μ : ℂ} {t : ℝ} (hξ : ‖(t : ℂ) * μ‖ < 1) :
    projMat d L * thetaKer d L g μ t = thetaKer d L g μ t * projMat d L := by
  have hS : Commute (projMat d L) (SB d L g) := projMat_mul_SB_comm hL
  have hΘ : Commute (projMat d L) (Theta d L g ((t : ℂ) * μ)) := ZeroModeCalc_projMat_mul_Theta_comm hL hξ
  exact ((Commute.smul_right hS _).mul_right hΘ)

/-- **`Q^{(A)}` commutes with `𝒰^{(n)}_{s,t,σ}`** (`3_5:1540-1545`, `(def_Ustz)`): for `3 ≤ L`,
`‖t m_i m_{i+1}‖ < 1`, every `A ⊂ ⟦n⟧`, `s` arbitrary. -/
theorem zeroModeSet_UN (hL : 3 ≤ L) {m : Fin n → ℂ} {s t : ℝ}
    (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (UN d L g m s t T) = UN d L g m s t (zeroModeSet d L A T) := by
  rw [UN_eq_tensorKer]
  exact ZeroModeCalc_zeroModeSet_tensorKer_comm A _ (fun i _ => ZeroModeCalc_projMat_mul_uKer_comm hL (hξ i)) T

/-- The single-index form of `zeroModeSet_UN`: `Q^{(i)} 𝒰 = 𝒰 Q^{(i)}`. -/
theorem zeroModeOp_UN (hL : 3 ≤ L) {m : Fin n → ℂ} {s t : ℝ}
    (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (i : Fin n) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L i (UN d L g m s t T) = UN d L g m s t (zeroModeOp d L i T) := by
  rw [UN_eq_tensorKer]
  exact ZeroModeCalc_zeroModeOp_tensorKer_comm i _ (ZeroModeCalc_projMat_mul_uKer_comm hL (hξ i)) T

/-- The `i`-th summand of `Θ^{(n)}`: `(Θ^{(n)}_i K ∘ 𝒜)_a = Σ_b K_{a_i b} 𝒜_{a(i ↦ b)}`. -/
private noncomputable def zmcSlot (i : Fin n) (K : Matrix (Zd d L) (Zd d L) ℂ)
    (T : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b, K (a i) b * T (Function.update a i b)

private theorem zmcSlot_comm (i j : Fin n) (K : Matrix (Zd d L) (Zd d L) ℂ)
    (hK : i = j → projMat d L * K = K * projMat d L) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L j (zmcSlot i K T) = zmcSlot i K (zeroModeOp d L j T) := by
  funext a
  by_cases hij : i = j
  · subst hij
    have hsum := zmc_sum_col_eq_row (hK rfl)
    simp only [zeroModeOp, avgOp, zmcSlot, Function.update_idem, Function.update_self,
      mul_sub, Finset.sum_sub_distrib]
    refine congrArg₂ (· - ·) rfl ?_
    calc ((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, ∑ b : Zd d L, K c b * T (Function.update a i b)
        = ((L : ℂ) ^ d)⁻¹ * ∑ b : Zd d L, (∑ c : Zd d L, K c b) * T (Function.update a i b) := by
          rw [Finset.sum_comm]
          exact congrArg _ (Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul])
      _ = ((L : ℂ) ^ d)⁻¹ * ((∑ c : Zd d L, K (a i) c) * ∑ b : Zd d L, T (Function.update a i b)) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => by rw [hsum (a i) b]
      _ = ∑ b : Zd d L, K (a i) b * (((L : ℂ) ^ d)⁻¹ * ∑ c : Zd d L, T (Function.update a i c)) := by
          rw [← Finset.sum_mul]; ring
  · have hji : j ≠ i := fun h => hij h.symm
    simp only [zeroModeOp, avgOp, zmcSlot, Function.update_of_ne hij,
      Function.update_comm hji, mul_sub, Finset.sum_sub_distrib]
    refine congrArg₂ (· - ·) rfl ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring

/-- `Θ^{(n)}_{t,σ} = Σ_i (slot-`i` kernel `μ_i S^{(B)} Θ_{t μ_i})`. -/
private theorem zmc_ThetaN_eq (m : Fin n → ℂ) (t : ℝ) (T : (Fin n → Zd d L) → ℂ) :
    ThetaN d L g m t T = ∑ i, zmcSlot i (thetaKer d L g (cycProd m i) t) T := by
  funext a
  simp only [ThetaN, zmcSlot, Finset.sum_apply]

/-- `Q^{(j)}` commutes with `Θ^{(n)}_{t,σ}` (`3_5:1540-1545`). -/
theorem zeroModeOp_ThetaN (hL : 3 ≤ L) {m : Fin n → ℂ} {t : ℝ}
    (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (j : Fin n) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeOp d L j (ThetaN d L g m t T) = ThetaN d L g m t (zeroModeOp d L j T) := by
  rw [zmc_ThetaN_eq, zmc_ThetaN_eq, ZeroModeCalc_zeroModeOp_sum]
  exact Finset.sum_congr rfl fun i _ =>
    zmcSlot_comm i j _ (fun _ => ZeroModeCalc_projMat_mul_thetaKer_comm hL (hξ i)) T

/-- **`Q^{(A)}` commutes with `Θ^{(n)}_{t,σ}`** (`3_5:1540-1545`, `(def:op_thn)`): for `3 ≤ L`,
`‖t m_i m_{i+1}‖ < 1`, every `A ⊂ ⟦n⟧`. -/
theorem zeroModeSet_ThetaN (hL : 3 ≤ L) {m : Fin n → ℂ} {t : ℝ}
    (hξ : ∀ i, ‖(t : ℂ) * cycProd m i‖ < 1) (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (ThetaN d L g m t T) = ThetaN d L g m t (zeroModeSet d L A T) :=
  ZeroModeCalc_zeroModeSet_comm_of_comm (ThetaN d L g m t) A (fun j _ T' => zeroModeOp_ThetaN hL hξ j T') T

end Commute

/-! ## 3. The bridge to `SameSignOutside` and the sign data of `Ugen` -/

section Bridge

/-- `i ∈ I_diff(σ)` iff `σ_i ≠ σ_{i+1}` (cyclic). -/
theorem ZeroModeCalc_mem_STIdiff {k : ℕ} (σ : Fin k → Bool) (i : Fin k) :
    i ∈ Gauss.Sizes.STIdiff σ ↔ σ i ≠ σ (finRotate k i) := by
  simp [Gauss.Sizes.STIdiff]

/-- `A ⊇ I_diff(σ)` in the form of the hypothesis of `STEKNonzero`. -/
theorem ZeroModeCalc_STIdiff_subset_iff {k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k)) :
    Gauss.Sizes.STIdiff σ ⊆ A ↔ ∀ i, σ i ≠ σ (finRotate k i) → i ∈ A :=
  ⟨fun h i hi => h ((ZeroModeCalc_mem_STIdiff σ i).2 hi), fun h i hi => h i ((ZeroModeCalc_mem_STIdiff σ i).1 hi)⟩

/-- **`A ⊇ I_diff(σ)` gives `SameSignOutside`** for every sign assignment `i ↦ f(σ_i)`; with
`f = mSigma E` this is the hypothesis of `norm_zeroModeSet_UN_le`, with `f = PropSpin m` that of
the evolution pins (`EKsgn m σ i = PropSpin m (σ i)`). -/
theorem sameSignOutside_of_STIdiff_subset {k : ℕ} (f : Bool → ℂ) (σ : Fin k → Bool)
    {A : Finset (Fin k)} (h : Gauss.Sizes.STIdiff σ ⊆ A) :
    SameSignOutside (fun i => f (σ i)) A := by
  intro i hi
  by_contra hne
  exact hi (h ((ZeroModeCalc_mem_STIdiff σ i).2 fun heq => hne (congrArg f heq)))

/-- `A ∪ I_diff(σ)`, the index set of `lem: newPQ`, satisfies `SameSignOutside`. -/
theorem sameSignOutside_union_STIdiff {k : ℕ} (f : Bool → ℂ) (σ : Fin k → Bool)
    (A : Finset (Fin k)) :
    SameSignOutside (fun i => f (σ i)) (A ∪ Gauss.Sizes.STIdiff σ) :=
  sameSignOutside_of_STIdiff_subset f σ Finset.subset_union_right

end Bridge

/-! ## 4. The kernel `Ugen`: commutation with `Q^{(A)}` -/

namespace Ind

section UgenCommute

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `Ugen` is the merged `UN` at the sign data `EKsgn (mE E) σ` (`EKsgn m σ i = PropSpin m (σ i)`,
`mSigma E b = PropSpin (mE E) b`): the form in which `STEKNonzero` / `ekSumDecayNonzero_holds` are
stated. -/
theorem Ugen_eq_UN_EKsgn (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) :
    Ugen d L g E σ v w = UN d L g (EKsgn (mE E) σ) v w := rfl

/-- **`Q^{(A)}` commutes with `𝒰_{v,w,σ}`** at the energy `E`, `|E| ≤ 2`, for `0 ≤ w < 1`
(`v` arbitrary). -/
theorem zeroModeSet_Ugen (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool)
    {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (A : Finset (Fin k)) (T : (Fin k → Zd d L) → ℂ) :
    zeroModeSet d L A (Ugen d L g E σ v w T) = Ugen d L g E σ v w (zeroModeSet d L A T) :=
  zeroModeSet_UN hL (fun i => norm_mul_mSigma_lt_one hE hw0 hw1 (σ i) (σ (finRotate k i))) A T

/-- The single-index form of `zeroModeSet_Ugen`. -/
theorem zeroModeOp_Ugen (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool)
    {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) (i : Fin k) (T : (Fin k → Zd d L) → ℂ) :
    zeroModeOp d L i (Ugen d L g E σ v w T) = Ugen d L g E σ v w (zeroModeOp d L i T) :=
  zeroModeOp_UN hL (fun i => norm_mul_mSigma_lt_one hE hw0 hw1 (σ i) (σ (finRotate k i))) i T

end UgenCommute

/-! ### 5. `(iisuwjyys)` on the grid -/

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss RBM.Path

section GridDuhamel

private theorem zmc_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j := by
  unfold gridTime gridStep
  exact add_nonneg hs0 (mul_nonneg (Nat.cast_nonneg j)
    (div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)))

private theorem zmc_gridTime_lt_one (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    (hK : K n ≠ 0) (ht1 : t n < 1) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have hstep : 0 ≤ gridStep s t K n := div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)
  have hmono : gridTime s t K n j ≤ gridTime s t K n (K n) := by
    unfold gridTime
    have := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hj) hstep
    linarith
  rw [gridTime_last s t K n hK] at hmono
  linarith

variable {d : ℕ} (sz : Sizes d)

/-- **`(iisuwjyys)` on the grid, `Q^{(A)}` outside `𝒰`** (`3_5:1546-1568`; the grid form of
`(eq_L-Keee_nonzeromode)` + Duhamel): the stopped grid Duhamel identity `stoppedDuhamelN_at`
(`A_{j∧τ} = 𝒰_{u_0,u_{j∧τ}} A_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_{j∧τ}} (P_i + ξ_{i+1})`, hypotheses at
the single size index `n`, DECISIONS §29 (4)) with `Q^{(A)}` applied pathwise and split by the
additivity of `𝒰` and of `Q^{(A)}`.  Needs neither the case condition `1 - s ≤ ilambda²/L²` nor any
commutation; the kernel index is `u_{i+1}` (`GridDuhamelN_Ugen_duhamel_telescope`). -/
theorem zeroModeCalc_duhamel_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (A : Finset (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz)
    (hjτ : min j (τ ω) ≤ K n) :
    zeroModeSet d (sz.L n) A (AvecN sz E s t K n (min j (τ ω)) σ ω) =
      zeroModeSet d (sz.L n) A
          (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0)
            (gridTime s t K n (min j (τ ω))) (AvecN sz E s t K n 0 σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          zeroModeSet d (sz.L n) A
            (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
              (gridTime s t K n (min j (τ ω))) (predIncN sz E s t K n i σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          zeroModeSet d (sz.L n) A
            (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
              (gridTime s t K n (min j (τ ω))) (martIncN sz E s t K n i σ ω)) := by
  have h := stoppedDuhamelN_at sz E s t K n hE hs0 hst ht1 hK σ τ j ω hjτ
  rw [h, zeroModeSet_add, zeroModeSet_sum]
  simp only [GridDuhamelN_Ugen_add, zeroModeSet_add, Finset.sum_add_distrib]
  ring

/-- **`(iisuwjyys)` on the grid, `Q^{(A)}` inside `𝒰`** (`3_5:1540-1568`): moving `Q^{(A)}` through
`𝒰_{·,u_{j∧τ}}` by `zeroModeSet_Ugen` (all slot parameters `‖u_{j∧τ} m_i m_{i+1}‖ < 1` since
`0 ≤ u_{j∧τ} < 1`),
`Q^{(A)} A_{j∧τ} = 𝒰_{u_0,u_{j∧τ}} Q^{(A)} A_0 + Σ_i 𝒰_{u_{i+1},u_{j∧τ}} Q^{(A)} P_i
  + Σ_i 𝒰_{u_{i+1},u_{j∧τ}} Q^{(A)} ξ_{i+1}`.
`Q^{(A)}` is deterministic and linear, so `Q^{(A)} ξ_{i+1}` is the tensor of the `≤ 2^{|A|}`
coordinate martingale differences `ξ_{i+1}(a')` (that it is a martingale difference of
`Q^{(A)} A_{i+1}` is the integrability bookkeeping of S3-21). -/
theorem zeroModeCalc_duhamel_inside_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (A : Finset (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz)
    (hjτ : min j (τ ω) ≤ K n) :
    zeroModeSet d (sz.L n) A (AvecN sz E s t K n (min j (τ ω)) σ ω) =
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (zeroModeSet d (sz.L n) A (AvecN sz E s t K n 0 σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (predIncN sz E s t K n i σ ω)) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (martIncN sz E s t K n i σ ω)) := by
  have hw0 := zmc_gridTime_nonneg s t K n hs0 hst (min j (τ ω))
  have hw1 := zmc_gridTime_lt_one s t K n hst hK ht1 hjτ
  have hL := sz.three_le_L n
  rw [zeroModeCalc_duhamel_at sz E s t K n hE hs0 hst ht1 hK σ A τ j ω hjτ,
    zeroModeSet_Ugen hL hE.le σ hw0 hw1]
  simp only [zeroModeSet_Ugen hL hE.le σ hw0 hw1]

end GridDuhamel

end Ind

/-! ## 6. The combination with `lem: newPQ` (`3_5:1590`) -/

namespace Gauss.Sizes

open RBM.Gauss RBM.Loop

/-- **`(𝓛 − 𝒦)` through `lem: newPQ`** (`3_5:1590`: "combining `(yurenAL)`, `(yurenAK)`"):
subtracting the two identities of `stNewPQ_holds` (one data `(ℓ, k, ξ, σ', ι, A')` serves both
`𝓛` and `𝒦`; no different form of the `𝒦` half is needed),
`(Q^{(A)}(𝓛 − 𝒦)^{(m)})_{σ,a} = (Q^{(A ∪ I_diff(σ))}(𝓛 − 𝒦)^{(m)})_{σ,a}
  + Σ_α ξ_α (2 i N η_τ)^{-(m - k_α)} (Q^{(A_α)}(𝓛 − 𝒦)^{(k_α)})_{σ_α, a_α}`
with `A_α ⊇ I_diff(σ_α)`, `1 ≤ k_α ≤ m - 1`, for `(𝓛 − 𝒦)` the merged `STLKM` at `H = seqHflow`
(`𝓛 − 𝒦 = Lloop − STKloop` by definition).  Every index set on the right contains `I_diff` of its
charge vector, i.e. `SameSignOutside` holds (`sameSignOutside_of_STIdiff_subset`,
`sameSignOutside_union_STIdiff`). -/
theorem zeroModeCalc_LK_expansion (d m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        zeroModeSet d (sz.L n) A (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ)
              (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) /
                (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α)
                (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := stNewPQ_holds d m σ A
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, ?_⟩
  intro sz n E τ hE hτ0 hτ1 ω a
  obtain ⟨hL, hK⟩ := h sz n E τ hE hτ0 hτ1 ω a
  have hsub : ∀ {k' : ℕ} (A'' : Finset (Fin k')) (σ'' : Fin k' → Bool) (b : Fin k' → Zd d (sz.L n)),
      zeroModeSet d (sz.L n) A'' (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ'' a') b
        = zeroModeSet d (sz.L n) A'' (fun a' => Lloop sz n E τ σ'' a' ω) b
          - zeroModeSet d (sz.L n) A'' (fun a' => STKloop sz n E τ σ'' a') b := by
    intro k' A'' σ'' b
    have := congrFun (zeroModeSet_sub (d := d) (L := sz.L n) A''
      (fun a' => Lloop sz n E τ σ'' a' ω) (fun a' => STKloop sz n E τ σ'' a')) b
    exact this
  simp only [hsub]
  rw [hL, hK]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **`(𝓛 − 𝒦)` through `lem: newPQ`, `A = ∅`** (`3_5:1590`): `(𝓛 − 𝒦)^{(m)}_{σ,a}` is
`(Q^{(I_diff(σ))}(𝓛 − 𝒦)^{(m)})_{σ,a}` plus lower loops with `A_α ⊇ I_diff(σ_α)`. -/
theorem zeroModeCalc_LK_expansion_empty (d m : ℕ) (σ : Fin m → Bool) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        STLKM sz n E τ (sz.seqHflow n τ ω) σ a =
          zeroModeSet d (sz.L n) (STIdiff σ)
              (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) /
                (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α)
                (fun a' => STLKM sz n E τ (sz.seqHflow n τ ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion d m σ ∅
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun sz n E τ hE hτ0 hτ1 ω a => ?_⟩
  simpa using h sz n E τ hE hτ0 hτ1 ω a

end Gauss.Sizes

/-! ## 7. Compiled nonempty instances (`d = 3`)

Targets 1 and 2 at `d = 3`, `L = 4` (`Zd 3 4`, 64 points), `n = 3`, `σ = (+,-,+)`,
`A = I_diff(σ) = {0, 1}` (nonempty, proper), the nonzero tensor `δ₀ = 1_{a = 0}`, `g = 1/2`,
`E = 0` (`m(+) = i`, `m(-) = -i`), `(v, w) = (9/10, 99/100)`; every deterministic hypothesis
(`3 ≤ L`, `|E| ≤ 2`, `0 ≤ w < 1`, `‖w μ_i‖ < 1`) is discharged.  Targets 3 and 4 at the merged
`sz0` (`d = 3`, `L_0 = 4`, `W_0 = 32`, `ilambda_0 = 1/64`), `n = 0`, `E ≡ 0`, `s ≡ 1/10`,
`t ≡ 1/2`, `K ≡ 4`, `τ ≡ 3`, `j = 4`, `σ = (+,-,+)`, `A = I_diff(σ)`, for every sample `ω`. -/

namespace ZeroModeCalcInst

open RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Ind RBM.Path

/-- `σ = (+,-,+)`: `I_diff(σ) = {0, 1}`. -/
private def zmcSigma : Fin 3 → Bool := ![true, false, true]

/-- The point mass `δ₀` on `(Z_4^3)^3`. -/
private noncomputable def zmcDelta : (Fin 3 → Zd 3 4) → ℂ := fun a => if a = 0 then 1 else 0

private theorem zmcDelta_ne : zmcDelta ≠ 0 := fun h => by
  have := congrFun h 0
  simp [zmcDelta] at this

private theorem zmcIdiff_card : (STIdiff zmcSigma).card = 2 := by decide

private theorem zmcSigma_nonconst : zmcSigma 0 ≠ zmcSigma 1 := by decide

/-- Target 1, `(normQA2)` for `Q^{(A)}`, `A = I_diff(σ)`, `|A| = 2`: `‖Q^{(A)} δ₀‖ ≤ 4 ‖δ₀‖`. -/
example : zmcDelta ≠ 0 ∧
    ‖zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta‖ ≤ 2 ^ 2 * ‖zmcDelta‖ := by
  refine ⟨zmcDelta_ne, ?_⟩
  have h := norm_zeroModeSet_le (d := 3) (L := 4) (STIdiff zmcSigma) zmcDelta
  rwa [zmcIdiff_card] at h

/-- Target 1, `(normQA2)` for one index. -/
example : ‖zeroModeOp 3 4 (1 : Fin 3) zmcDelta‖ ≤ 2 * ‖zmcDelta‖ :=
  norm_zeroModeOp_le 1 zmcDelta

/-- Target 1, linearity of `Q^{(A)}` at `A = I_diff(σ)`: additivity, homogeneity, subtraction, sums. -/
example : zmcDelta ≠ 0 ∧
    zeroModeSet 3 4 (STIdiff zmcSigma) (zmcDelta + (2 : ℂ) • zmcDelta)
      = zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta
        + (2 : ℂ) • zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta :=
  ⟨zmcDelta_ne, by rw [zeroModeSet_add, zeroModeSet_smul]⟩

example :
    zeroModeSet 3 4 (STIdiff zmcSigma) (zmcDelta - (3 : ℂ) • zmcDelta)
      = zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta
        - (3 : ℂ) • zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta := by
  rw [zeroModeSet_sub, zeroModeSet_smul]

example : zeroModeSet 3 4 (STIdiff zmcSigma) (∑ i : Fin 3, (i.val + 1 : ℂ) • zmcDelta)
    = ∑ i : Fin 3, zeroModeSet 3 4 (STIdiff zmcSigma) ((i.val + 1 : ℂ) • zmcDelta) :=
  zeroModeSet_sum _ _ _

example : zeroModeSet 3 4 (∅ : Finset (Fin 3)) zmcDelta = zmcDelta := zeroModeSet_empty _

/-- The slot condition of the sign data `m(σ_i) = mSigma 0 (σ_i)` at `w = 99/100`. -/
private theorem zmc_slot_lt_one (i : Fin 3) :
    ‖(((99 / 100 : ℝ)) : ℂ) * cycProd (fun i => mSigma 0 (zmcSigma i)) i‖ < 1 :=
  norm_mul_mSigma_lt_one (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (zmcSigma i) (zmcSigma (finRotate 3 i))

/-- Target 2: `Q^{(A)}` commutes with `𝒰^{(3)}_{9/10, 99/100, σ}` (`UN` form). -/
example : zmcDelta ≠ 0 ∧
    zeroModeSet 3 4 (STIdiff zmcSigma)
        (UN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (9 / 10) (99 / 100) zmcDelta)
      = UN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (9 / 10) (99 / 100)
          (zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta) :=
  ⟨zmcDelta_ne, zeroModeSet_UN (by norm_num) zmc_slot_lt_one _ _⟩

/-- Target 2: `Q^{(A)}` commutes with `Θ^{(3)}_{99/100, σ}`. -/
example : zmcDelta ≠ 0 ∧
    zeroModeSet 3 4 (STIdiff zmcSigma)
        (ThetaN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (99 / 100) zmcDelta)
      = ThetaN 3 4 (1 / 2 : ℝ) (fun i => mSigma 0 (zmcSigma i)) (99 / 100)
          (zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta) :=
  ⟨zmcDelta_ne, zeroModeSet_ThetaN (by norm_num) zmc_slot_lt_one _ _⟩

/-- Target 2: `Q^{(A)}` commutes with `Ugen` (the kernel of the grid identity). -/
example : zmcDelta ≠ 0 ∧
    zeroModeSet 3 4 (STIdiff zmcSigma)
        (Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) zmcDelta)
      = Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100)
          (zeroModeSet 3 4 (STIdiff zmcSigma) zmcDelta) :=
  ⟨zmcDelta_ne, zeroModeSet_Ugen (by norm_num) (by norm_num) zmcSigma (by norm_num)
    (by norm_num) _ _⟩

/-- Target 2, one index: `Q^{(1)}` commutes with `Ugen`. -/
example : zeroModeOp 3 4 (1 : Fin 3) (Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) zmcDelta)
    = Ugen 3 4 (1 / 2 : ℝ) 0 zmcSigma (9 / 10) (99 / 100) (zeroModeOp 3 4 (1 : Fin 3) zmcDelta) :=
  zeroModeOp_Ugen (by norm_num) (by norm_num) zmcSigma (by norm_num) (by norm_num) _ _

/-- Target 2, the matrix identity behind it: `Proj_{e^⊥} Θ_ξ = Θ_ξ Proj_{e^⊥}` at
`d = 3`, `L = 4`, `g = 1/2`, `ξ = 99/100`. -/
example : projMat 3 4 * Theta 3 4 (1 / 2 : ℝ) ((99 / 100 : ℝ) : ℂ)
    = Theta 3 4 (1 / 2 : ℝ) ((99 / 100 : ℝ) : ℂ) * projMat 3 4 :=
  ZeroModeCalc_projMat_mul_Theta_comm (by norm_num) (by
    rw [Complex.norm_real]; norm_num)

/-- `Q^{(i)}` on the right of a tensor kernel, at the kernels of `𝒰`. -/
example : tensorKer 3 4 (fun i => uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) i)
        (9 / 10) (99 / 100)) (zeroModeOp 3 4 (1 : Fin 3) zmcDelta)
    = tensorKer 3 4 (Function.update
        (fun i => uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) i)
          (9 / 10) (99 / 100)) 1
        (uKer 3 4 (1 / 2 : ℝ) (cycProd (fun i => mSigma 0 (zmcSigma i)) 1) (9 / 10) (99 / 100)
          * projMat 3 4)) zmcDelta :=
  ZeroModeCalc_tensorKer_zeroModeOp 1 _ zmcDelta

/-- The bridge: `SameSignOutside` at `A = I_diff(σ)`, for the sign data of `Ugen` at `E = 0`. -/
example : SameSignOutside (fun i => mSigma 0 (zmcSigma i)) (STIdiff zmcSigma) :=
  sameSignOutside_of_STIdiff_subset (mSigma 0) zmcSigma (Finset.Subset.refl _)

example : SameSignOutside (fun i => PropSpin Complex.I (zmcSigma i))
    ((∅ : Finset (Fin 3)) ∪ STIdiff zmcSigma) :=
  sameSignOutside_union_STIdiff (PropSpin Complex.I) zmcSigma ∅

/-! ### Targets 3 and 4 at `sz0` -/

private noncomputable def zmcE : ℕ → ℝ := fun _ => 0
private noncomputable def zmcS : ℕ → ℝ := fun _ => 1 / 10
private noncomputable def zmcT : ℕ → ℝ := fun _ => 1 / 2
private def zmcK : ℕ → ℕ := fun _ => 4

/-- Target 3, `Q^{(A)}` outside `𝒰`: `τ ≡ 3`, `j = 4` (so `j ∧ τ = 3 ≤ K = 4`), `σ = (+,-,+)`,
`A = I_diff(σ)`, every sample `ω`; the sum has three terms. -/
example (ω : PathΩ sz0) :
    zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
        (AvecN sz0 zmcE zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) zmcSigma ω) =
      zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
          (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 0)
            (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (AvecN sz0 zmcE zmcS zmcT zmcK 0 0 zmcSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
            (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1))
              (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
              (predIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
            (Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1))
              (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
              (martIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) :=
  zeroModeCalc_duhamel_at sz0 zmcE zmcS zmcT zmcK 0 (by norm_num [zmcE]) (by norm_num [zmcS])
    (by norm_num [zmcS, zmcT]) (by norm_num [zmcT]) (by norm_num [zmcK]) zmcSigma
    (STIdiff zmcSigma) (fun _ => 3) 4 ω (by norm_num [zmcK])

/-- Target 3, `Q^{(A)}` inside `𝒰` (same data). -/
example (ω : PathΩ sz0) :
    zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
        (AvecN sz0 zmcE zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)) zmcSigma ω) =
      Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 0)
          (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
          (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
            (AvecN sz0 zmcE zmcS zmcT zmcK 0 0 zmcSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1))
            (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
              (predIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (zmcE 0) zmcSigma (gridTime zmcS zmcT zmcK 0 (i + 1))
            (gridTime zmcS zmcT zmcK 0 (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
              (martIncN sz0 zmcE zmcS zmcT zmcK 0 i zmcSigma ω)) :=
  zeroModeCalc_duhamel_inside_at sz0 zmcE zmcS zmcT zmcK 0 (by norm_num [zmcE])
    (by norm_num [zmcS]) (by norm_num [zmcS, zmcT]) (by norm_num [zmcT]) (by norm_num [zmcK])
    zmcSigma (STIdiff zmcSigma) (fun _ => 3) 4 ω (by norm_num [zmcK])

/-- Target 4 (`A = ∅`): `d = 3`, `m = 3`, `σ = (+,-,+)`, `n = 0`, `E = 0`, `τ = 1/2`,
every sample and every label vector. -/
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a =
        zeroModeSet 3 (sz0.L 0) (STIdiff zmcSigma)
            (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α)
              (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion_empty 3 3 zmcSigma
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩

/-- Target 4 for a nonempty `A = {2}` (`A ∪ I_diff(σ) = {0, 1, 2}`), same data. -/
example : ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
    (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
    (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
    ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)),
      zeroModeSet 3 (sz0.L 0) ({2} : Finset (Fin 3))
          (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a =
        zeroModeSet 3 (sz0.L 0) (({2} : Finset (Fin 3)) ∪ STIdiff zmcSigma)
            (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) zmcSigma a') a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) *
                (etaT 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α)
              (fun a' => STLKM sz0 0 0 (1 / 2) (sz0.seqHflow 0 (1 / 2) ω) (σ' α) a') (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeCalc_LK_expansion 3 3 zmcSigma {2}
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun ω a =>
    h sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) ω a⟩

end ZeroModeCalcInst

end RBM
