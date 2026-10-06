/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.NQLin
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.AzumaProxyN
import RBM3D.Induction.QVN
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step34Pins
import RBM3D.Evolution.Nonzero
import RBM3D.Propagator.Prop5Hold
import RBM3D.Propagator.Prop5Short

/-!
# The grid ingredients of the zero-mode-removed evolution `Q^{(A)}(𝓛 − 𝒦)^{(k)}` (`d ≥ 3`)

Ticket T2274 (S3-21, stochastic layer ST-3, case (ii) `1 − s ≤ ilambda²/L²`).  Paper:
arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `def;zero_mode_remove`
(`3_5:1446`), `(normQA2)` (`3_5:1475`), `lem: newPQ` (`3_5:1482`), the commutation
(`3_5:1540-1545`), `(iisuwjyys)` (`3_5:1546`), `lem:STOeq_Qt_nonzero` (`3_5:1561`),
`lem:sum_decay_nonzero` (`3_5:1666`), the proof `3_5:1889-1928`, and
`A_deterministic_estimates.tex:204-232`.  No RBM1D/RBM2D source (portmap `T2041` P.7 rows S3-20,
S3-21): the zero-mode regime does not exist for `d ≤ 2`.

## What is here

* §1 (`RBM`) `zeroModeSet_idem` : `Q^{(A)} ∘ Q^{(A)} = Q^{(A)}`; the real kernel `qtNZ_q` of
  `Q^{(A)}` and its row sum `≤ 2^{|A|}`; the `∞→∞` duality `qtNZ_sum_norm_le_of_bound`.
* §2 (`RBM.Ind`) the vocabulary `cQVNZN`, `assembledRHSNZN`.
* §3 `nzUgen_holds`: `lem:sum_decay_nonzero` for the grid kernel `Ugen`, loss-free (EK-5), as an
  operator bound and as a row-sum bound with one constant.
* §4 `nz_hker`, §5 `nz_hdriftN`: the fields `hker`, `hdrift` of `GridAssemblyHypN` for the class
  "fixed points of `Q^{(A)}`".
* §6 `subGaussStop_nzN`: the Azuma input `SubGaussStopN` for `Q^{(A)} Z_j`.
* §7 `yMomentBounds_nzN`: the `Y`-moment inputs `YMomentBoundsN` pass to `Q^{(A)} Y`.
* §8 `budgetNZN`: the budget `assembledRHSNZN ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.
* §9 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QtNonzeroInst`): every target at
  concrete nondegenerate data (`szB` for `nzUgen_holds`, `nz_hker`; the merged `sz0` data for
  the others).

No conclusion pin is proved here; the registry is unchanged.  Every helper that the ticket does not
pin is `private` or carries the prefix `qtNZ_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. `Q^{(A)}` is a projection; its real kernel; the `∞→∞` duality -/

namespace RBM

section Projection

variable {d L : ℕ} [NeZero L]

/-- The identity kernel acts as the identity on tensors. -/
private theorem qtNZ_tensorKer_one {n : ℕ} (T : (Fin n → Zd d L) → ℂ) :
    tensorKer d L (fun _ : Fin n => (1 : Matrix (Zd d L) (Zd d L) ℂ)) T = T := by
  funext a
  unfold tensorKer
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    have hne : ∃ i, a i ≠ b i := by
      by_contra h
      exact hba (funext fun i => by
        by_contra hi
        exact h ⟨i, fun e => hi e.symm⟩)
    obtain ⟨i, hi⟩ := hne
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- `Q^{(A)}` is the tensor kernel with `Proj_{e^⊥}` at the indices of `A` and the identity elsewhere. -/
private theorem qtNZ_zeroModeSet_eq {n : ℕ} (A : Finset (Fin n)) (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A T =
      tensorKer d L (fun i => if i ∈ A then projMat d L else 1) T := by
  have h := zeroModeSet_tensorKer (d := d) (L := L) A
    (fun _ : Fin n => (1 : Matrix (Zd d L) (Zd d L) ℂ)) T
  rw [qtNZ_tensorKer_one] at h
  rw [h]
  congr 1
  funext i
  by_cases hi : i ∈ A <;> simp [hi]

/-- **`Q^{(A)} ∘ Q^{(A)} = Q^{(A)}`** (target 3): `Q^{(i)}` is the projection `I - P^{(i)}`
(`P^{(i)} P^{(i)} = P^{(i)}`, `projMat_mul_self`) and the `Q^{(i)}` commute. -/
theorem zeroModeSet_idem (d L : ℕ) [NeZero L] (n : ℕ) (A : Finset (Fin n))
    (T : (Fin n → Zd d L) → ℂ) :
    zeroModeSet d L A (zeroModeSet d L A T) = zeroModeSet d L A T := by
  rw [qtNZ_zeroModeSet_eq A T, zeroModeSet_tensorKer]
  congr 1
  funext i
  by_cases hi : i ∈ A
  · simp [hi, projMat_mul_self]
  · simp [hi]

/-- The one-index real kernel of `Q^{(A)}` at the index `i`. -/
private def qtNZ_f (d L : ℕ) {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (x y : Zd d L) : ℝ :=
  if i ∈ A then (if x = y then (1 : ℝ) else 0) - ((L : ℝ) ^ d)⁻¹ else (if x = y then (1 : ℝ) else 0)

/-- The real kernel `q_{b b'} = ∏_i q_i(b_i, b'_i)` of `Q^{(A)}`. -/
private def qtNZ_q (d L : ℕ) {k : ℕ} (A : Finset (Fin k)) (b b' : Fin k → Zd d L) : ℝ :=
  ∏ i, qtNZ_f d L A i (b i) (b' i)

/-- `(Q^{(A)} T)_b = Σ_{b'} q_{b b'} T_{b'}` with the **real** kernel `q`. -/
private theorem qtNZ_zeroModeSet_apply {k : ℕ} (A : Finset (Fin k)) (T : (Fin k → Zd d L) → ℂ)
    (b : Fin k → Zd d L) :
    zeroModeSet d L A T b = ∑ b', ((qtNZ_q d L A b b' : ℝ) : ℂ) * T b' := by
  rw [qtNZ_zeroModeSet_eq]
  unfold tensorKer
  refine Finset.sum_congr rfl fun b' _ => ?_
  congr 1
  unfold qtNZ_q
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold qtNZ_f
  by_cases hi : i ∈ A
  · by_cases hb : b i = b' i <;>
      simp [hi, hb, projMat, Matrix.sub_apply, Matrix.of_apply]
  · by_cases hb : b i = b' i <;> simp [hi, hb, Matrix.one_apply]

/-- The one-index row sum of the real kernel: `Σ_c |q_i(x, c)| ≤ 2` at `i ∈ A` and `= 1` otherwise. -/
private theorem qtNZ_sum_abs_f_le {k : ℕ} (A : Finset (Fin k)) (i : Fin k) (x : Zd d L) :
    ∑ c, |qtNZ_f d L A i x c| ≤ if i ∈ A then 2 else 1 := by
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by
      have := NeZero.ne L
      have : 0 < L := Nat.pos_of_ne_zero this
      exact_mod_cast this
    positivity
  have hcard : ((Fintype.card (Zd d L) : ℕ) : ℝ) = (L : ℝ) ^ d := by simp [ZMod.card]
  have hone : ∑ c : Zd d L, (if x = c then (1 : ℝ) else 0) = 1 := by simp
  by_cases hi : i ∈ A
  · simp only [hi, ite_true]
    calc ∑ c, |qtNZ_f d L A i x c|
        ≤ ∑ c : Zd d L, ((if x = c then (1 : ℝ) else 0) + ((L : ℝ) ^ d)⁻¹) := by
          refine Finset.sum_le_sum fun c _ => ?_
          unfold qtNZ_f
          simp only [hi, ite_true]
          have hinv : 0 ≤ ((L : ℝ) ^ d)⁻¹ := inv_nonneg.2 hL0.le
          by_cases hxc : x = c
          · simp only [hxc, ite_true]
            rw [abs_le]
            constructor <;> linarith
          · simp only [hxc, ite_false]
            rw [zero_sub, abs_neg, abs_of_nonneg hinv]
            linarith
      _ = 2 := by
          rw [Finset.sum_add_distrib, hone, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            mul_inv_cancel₀ hL0.ne']
          norm_num
  · simp only [hi, ite_false]
    refine le_of_eq ?_
    unfold qtNZ_f
    simp only [hi, ite_false]
    rw [Finset.sum_congr rfl fun c _ => (by
      by_cases hxc : x = c <;> simp [hxc] : |(if x = c then (1 : ℝ) else 0)| = if x = c then 1 else 0)]
    exact hone

/-- **The row sum of the real kernel of `Q^{(A)}` is at most `2^{|A|}`** (the `(normQA2)` of the paper
in the form needed for the moments of `Q^{(A)} Y`). -/
private theorem qtNZ_sum_abs_q_le {k : ℕ} (A : Finset (Fin k)) (b : Fin k → Zd d L) :
    ∑ b', |qtNZ_q d L A b b'| ≤ 2 ^ A.card := by
  unfold qtNZ_q
  have h1 : ∑ b' : Fin k → Zd d L, |∏ i, qtNZ_f d L A i (b i) (b' i)|
      = ∏ i, ∑ c, |qtNZ_f d L A i (b i) c| := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [Finset.abs_prod]
  rw [h1]
  calc ∏ i, ∑ c, |qtNZ_f d L A i (b i) c|
      ≤ ∏ i : Fin k, (if i ∈ A then (2 : ℝ) else 1) :=
        Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => abs_nonneg _)
          fun i _ => qtNZ_sum_abs_f_le A i (b i)
    _ = 2 ^ A.card := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **The `∞→∞` duality**: if the linear functional `X ↦ Σ_b κ_b X_b` has norm at most `C` for the
sup norm, then `Σ_b |κ_b| ≤ C` (test on `X_b = conj(κ_b)/|κ_b|`). -/
private theorem qtNZ_sum_norm_le_of_bound {ι : Type*} [Fintype ι] (κ : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ X : ι → ℂ, ‖∑ b, κ b * X b‖ ≤ C * ‖X‖) : ∑ b, ‖κ b‖ ≤ C := by
  set X : ι → ℂ := fun b => (κ b)⁻¹ * ((‖κ b‖ : ℝ) : ℂ) with hX
  have hX1 : ‖X‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
    by_cases hb : κ b = 0
    · simp [hX, hb]
    · have hn : ‖κ b‖ ≠ 0 := norm_ne_zero_iff.2 hb
      simp only [hX, norm_mul, norm_inv, Complex.norm_real, norm_norm]
      rw [inv_mul_cancel₀ hn]
  have hsum : ∑ b, κ b * X b = ((∑ b, ‖κ b‖ : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : κ b = 0
    · simp [hX, hb]
    · simp only [hX]
      field_simp
  have h1 := h X
  rw [hsum, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun b _ => norm_nonneg _)] at h1
  exact h1.trans (by nlinarith)

end Projection

end RBM

/-! ## 2. The vocabulary (targets 1-2 of the ticket, verbatim) -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- The sub-Gaussian proxy of the `j`-th propagated zero-mode-removed increment (case (ii)):
`Δ · k · C² · (Γ(ΓΛ) B_{u_j}^{2k}/η_{u_j} + W^{-D''})` (`C` = row-sum bound of `Q^{(A)}∘𝒰`;
no ratio factor, no far part: the analogue of `cQVNonAltN`, `NQGood2.lean:115`). -/
def cQVNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C Γ Λ D'' : ℝ) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * C ^ 2 *
    (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D'')))).toNNReal

/-- The right side of `AssembledN` (`GridAssemblyN.lean:227`) at `m = K n` for the zero-mode-removed
evolution: kernel weight `κ ≡ C`, `εK ≡ 0`, drift level `cA · dDriftLinN`, proxy `cQVNZN`,
step error `cA · stepErrN` (`cA = 2^{|A|}`); the analogue of `assembledRHSLinN` (`NQLin.lean:825`). -/
def assembledRHSNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y τK εq X0 : ℝ) : ℝ :=
  C * X0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      C * (cA * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
      stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
        (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k))

/-! ## 3. `lem:sum_decay_nonzero` for the grid kernel `Ugen` (target 4) -/

/-- **The row of `Q^{(A)} ∘ 𝒰` from an operator bound**: if `‖Q^{(A)} 𝒰 X‖_∞ ≤ C ‖X‖_∞` for all `X`, then
for every label `a` the functional `X ↦ (Q^{(A)} 𝒰 X)(a)` is `Σ_b κ_b X_b` with `Σ_b |κ_b| ≤ C`
(`Q^{(A)} ∘ 𝒰` is the tensor kernel with `Proj_{e^⊥} ∘ uKer` at `A`, `zeroModeSet_tensorKer`;
`κ_b = ∏_i K_i(a_i, b_i)`; then the `∞→∞` duality). -/
private theorem qtNZ_row_of_op (d L : ℕ) [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (A : Finset (Fin k)) (v w : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hop : ∀ X : (Fin k → Zd d L) → ℂ, ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖)
    (a : Fin k → Zd d L) :
    ∃ κ : (Fin k → Zd d L) → ℂ,
      (∀ X : (Fin k → Zd d L) → ℂ,
        zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C := by
  set K' : Fin k → Matrix (Zd d L) (Zd d L) ℂ := fun i =>
    if i ∈ A then projMat d L * uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w
    else uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w with hK'
  have hrow : ∀ X : (Fin k → Zd d L) → ℂ, zeroModeSet d L A (Ugen d L g E σ v w X) a =
      ∑ b, (∏ i, K' i (a i) (b i)) * X b := by
    intro X
    change zeroModeSet d L A (UN d L g (fun i => mSigma E (σ i)) v w X) a = _
    rw [UN_eq_tensorKer, zeroModeSet_tensorKer]
    rfl
  refine ⟨fun b => ∏ i, K' i (a i) (b i), hrow, ?_⟩
  exact qtNZ_sum_norm_le_of_bound _ hC fun X => by
    rw [← hrow X]
    exact (norm_le_pi_norm _ a).trans (hop X)

/-- **The coarse row of `Q^{(A)} ∘ 𝒰`** (no window condition; used where `lem:sum_decay_nonzero` does not
apply, e.g. at the case-(i) data of the merged instances): `Σ_b |κ_b| ≤ 2^{|A|} ((1 - v)/(1 - w))^k`
(`norm_zeroModeSet_le` and the merged `norm_UN_le`). -/
private theorem qtNZ_row_coarse (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2)
    {k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k)) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w)
    (hw1 : w < 1) (a : Fin k → Zd d L) :
    ∃ κ : (Fin k → Zd d L) → ℂ,
      (∀ X : (Fin k → Zd d L) → ℂ,
        zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧
      ∑ b, ‖κ b‖ ≤ 2 ^ A.card * ((1 - v) / (1 - w)) ^ k := by
  have h1 : 0 ≤ (1 - v) / (1 - w) := div_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ 2 ^ A.card * ((1 - v) / (1 - w)) ^ k := by positivity
  refine qtNZ_row_of_op d L g E σ A v w hC (fun X => ?_) a
  calc ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖
      ≤ 2 ^ A.card * ‖Ugen d L g E σ v w X‖ := norm_zeroModeSet_le A _
    _ ≤ 2 ^ A.card * (((1 - v) / (1 - w)) ^ k * ‖X‖) :=
        mul_le_mul_of_nonneg_left
          (norm_UN_le hL (fun i => norm_mSigma hE (σ i)) hv0 hvw hw1 X) (by positivity)
    _ = 2 ^ A.card * ((1 - v) / (1 - w)) ^ k * ‖X‖ := by ring

/-- Target 4, `RBM.Ind.nzUgen_holds`: `lem:sum_decay_nonzero` (`3_5:1666`) for the grid kernel `Ugen`,
loss-free (EK-5), as an operator bound and as a row-sum bound with one constant.  The merged
`ekSumDecayNonzero_holds` (deterministic, no decay class, no sum-zero) at `m = mE E`
(`norm_mE`, `|E| < 2`), `Ugen = UN … (EKsgn (mE E) σ)` (`Ugen_eq_UN_EKsgn`); the row-sum form is
the `∞→∞` duality (`qtNZ_sum_norm_le_of_bound`) for the row `κ_b = ∏_i K_i(a_i, b_i)` of the tensor
kernel `Q^{(A)} ∘ 𝒰` (`zeroModeSet_tensorKer`). -/
theorem nzUgen_holds :
    ∀ (d k : ℕ), 3 ≤ d → 2 ≤ k → ∀ Λg κ' : ℝ, 0 < Λg → 0 < κ' →
      ∃ C : ℝ, 0 < C ∧
        ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g E : ℝ, 0 < g → g ≤ Λg → |E| < 2 → κ' ≤ (mE E).im →
          ∀ v w : ℝ, 0 ≤ v → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ v → v ≤ w → w < 1 →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            (∀ X : (Fin k → Zd d L) → ℂ, ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖) ∧
            ∀ a : Fin k → Zd d L, ∃ κ : (Fin k → Zd d L) → ℂ,
              (∀ X : (Fin k → Zd d L) → ℂ,
                zeroModeSet d L A (Ugen d L g E σ v w X) a = ∑ b, κ b * X b) ∧
              ∑ b, ‖κ b‖ ≤ C := by
  intro d k hd hk Λg κ' hΛg hκ'
  obtain ⟨C, hC, H⟩ := ekSumDecayNonzero_holds d k Λg κ' (prop5Short_holds d Λg κ')
    (prop8ZeroMode_holds d Λg κ') hd hk hΛg hκ'
  refine ⟨C, hC, ?_⟩
  intro L _ hL g E hg hgΛ hE hκE v w hv0 hvg hvw hw1 σ A hA
  have hop : ∀ X : (Fin k → Zd d L) → ℂ,
      ‖zeroModeSet d L A (Ugen d L g E σ v w X)‖ ≤ C * ‖X‖ := fun X =>
    H L hL g hg hgΛ v w hv0 hvg hvw hw1 (mE E) (norm_mE hE.le) hκE σ A
      ((ZeroModeCalc_STIdiff_subset_iff σ A).1 hA) X
  exact ⟨hop, fun a => qtNZ_row_of_op d L g E σ A v w hC.le hop a⟩

/-! ## 4. The field `hker` for the class "fixed points of `Q^{(A)}`" (target 5) -/

/-- Target 5, `RBM.Ind.nz_hker`: the `hker` field of `GridAssemblyHypN` (`GridAssemblyN.lean:201`) for
the class `Cls := fun _ _ X => zeroModeSet d (sz.L n) A X = X`, `κ ≡ C`, `εK ≡ 0`.  For
`X = Q^{(A)} X`: `𝒰 X = 𝒰 Q^{(A)} X = Q^{(A)} 𝒰 X` (`zeroModeSet_Ugen`, `0 ≤ u_m < 1`, `|E| ≤ 2`,
`3 ≤ L`), so `‖(𝒰 X)(a)‖ ≤ ‖Q^{(A)} 𝒰 X‖ ≤ C ‖X‖ ≤ C M`. -/
theorem nz_hker :
    ∀ {d k : ℕ} (sz : Sizes d) (n : ℕ) (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
      (K : ℕ) (C : ℝ), 0 ≤ C → |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) →
      (∀ i m, i ≤ m → m ≤ K → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
        ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X)‖ ≤ C * ‖X‖) →
      ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
        (∀ b, ‖X b‖ ≤ M) → zeroModeSet d (sz.L n) A X = X →
        ∀ a, ‖Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X a‖ ≤ C * M + 0 * δ := by
  intro d k sz n E σ A u K C hC hE hu0 hu1 hop i m him hmK X M δ hM hδ hXM hXQ a
  have hL := sz.three_le_L n
  have hcomm : zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X) =
      Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X := by
    have h := zeroModeSet_Ugen (d := d) (L := sz.L n) (g := sz.lam n) hL hE σ (v := u i)
      (hu0 m hmK) (hu1 m hmK) A X
    rw [hXQ] at h
    exact h
  have hXn : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).2 hXM
  calc ‖Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X a‖
      = ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X) a‖ := by
        rw [hcomm]
    _ ≤ ‖zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X)‖ :=
        norm_le_pi_norm _ a
    _ ≤ C * ‖X‖ := hop i m him hmK X
    _ ≤ C * M := mul_le_mul_of_nonneg_left hXn hC
    _ = C * M + 0 * δ := by ring

/-! ## 5. The drift of the zero-mode-removed hierarchy on `GoodLinN` (target 6) -/

/-- Target 6, `RBM.Ind.nz_hdriftN`: the drift of the zero-mode-removed hierarchy on `GoodLinN`
(`Q^{(A)}` of the merged `driftTensorN`): `‖(Q^{(A)} Dr)(b)‖ ≤ 2^{|A|} ‖Dr‖ ≤ 2^{|A|} · dDriftLinN`
(`norm_zeroModeSet_le` = `(normQA2)`, `nqLin_hdriftN`; the sup over `b` by `pi_norm_le_iff_of_nonneg`). -/
theorem nz_hdriftN :
    ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ}, 2 ≤ k → ∀ (σ : Fin k → Bool) (A : Finset (Fin k))
      (E s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ),
      (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈
        GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
      ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
        ‖zeroModeSet d (sz.L n) A
            (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ) b‖ ≤
          2 ^ A.card * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) := by
  intro d sz n k hk σ A E s v K Γ Φ₁ Φ₂ Φ₃ τ hτG ω j hjK hjτ b
  have hD := nqLin_hdriftN sz hk σ E s v K Γ Φ₁ Φ₂ Φ₃ τ hτG ω j hjK hjτ
  have hD0 : 0 ≤ dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    (norm_nonneg _).trans (hD (fun _ => 0))
  have hDn : ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ‖ ≤
      dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    (pi_norm_le_iff_of_nonneg hD0).2 hD
  calc ‖zeroModeSet d (sz.L n) A
          (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ) b‖
      ≤ ‖zeroModeSet d (sz.L n) A
          (driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ)‖ :=
        norm_le_pi_norm _ b
    _ ≤ 2 ^ A.card * ‖driftTensorN sz n (E n) (gridTime s v K n j) (pathH sz s v K n j ω) σ‖ :=
        norm_zeroModeSet_le A _
    _ ≤ 2 ^ A.card * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)

/-! ## 6. The Azuma input for `Q^{(A)} Z_j` (target 7) -/

section Azuma

/-- `Re Σ_{b,b'} κ_b conj(κ_{b'}) e_{bb'} ≤ C² M` when `‖e_{bb'}‖ ≤ M` and `Σ_b ‖κ_b‖ ≤ C`
(`(Σ‖κ‖)² · max‖e‖`, the `∞→∞` row-sum form of the quadratic variation). -/
private theorem qtNZ_re_sum_le {ι : Type*} [Fintype ι] (κ : ι → ℂ) (e : ι → ι → ℂ) {C M : ℝ}
    (hC : ∑ b, ‖κ b‖ ≤ C) (hM0 : 0 ≤ M) (hM : ∀ b b', ‖e b b'‖ ≤ M) :
    (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * e b b').re ≤ C ^ 2 * M := by
  have hS0 : 0 ≤ ∑ b, ‖κ b‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  calc (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * e b b').re
      ≤ ‖∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') * e b b'‖ := Complex.re_le_norm _
    _ ≤ ∑ b, ∑ b', ‖κ b * (starRingEnd ℂ) (κ b') * e b b'‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
    _ ≤ ∑ b, ∑ b', ‖κ b‖ * ‖κ b'‖ * M :=
        Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun b' _ => by
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_left (hM b b') (by positivity)
    _ = (∑ b, ‖κ b‖) * (∑ b', ‖κ b'‖) * M := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
    _ ≤ C ^ 2 * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM0
        nlinarith [hC, hS0]

/-- Target 7, `RBM.Ind.subGaussStop_nzN`: the Azuma input (`SubGaussStopN`, `StepDecompN.lean:215`) for the
zero-mode-removed first-chaos part `Q^{(A)} Z_j`, proxy `cQVNZN`, on any stopping family that stays in
`GoodSetN` (its `STeeM` clause only), from a row-sum bound `≤ C` of `Q^{(A)}∘𝒰_{u_{j+1},u_m}`.
`𝒰(Q^{(A)} Z_j)(a) = Q^{(A)} 𝒰(Z_j)(a) = Σ_b κ_b Z_j(b)` (commutation `zeroModeSet_Ugen`, the row
`κ`); `azumaSubGN` with `Φ = loopFamN …` and the weights `κ` (as `azumaProxy_subG_ugen`,
`AzumaProxyN.lean:980`); `qvPropagatedN` at these weights; `Re Σ κ κ̄' ee ≤ C² max‖ee(u_{j+1})‖` and
the `STeeM` clause (D4) of `GoodSetN` at `u_j` plus the shift `eeShiftErrN` (the hypothesis `hδ`). -/
theorem subGaussStop_nzN :
    ∀ {d k : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin k → Bool)
      (A : Finset (Fin k)) (C Γ Λ Φ τ' D' D'' : ℝ) (τ : PathΩ sz → ℕ),
      2 ≤ k → (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) →
      0 ≤ C → 0 ≤ Γ → 0 ≤ Λ →
      (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
      (∀ ω j, j < τ ω → pathH sz s v K n j ω ∈
        sz.GoodSetN n (E n) (gridTime s v K n j) k Γ Λ Φ τ' D') →
      ∀ m, m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
        (∃ κ : (Fin k → Zd d (sz.L n)) → ℂ,
          (∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
            zeroModeSet d (sz.L n) A (Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1))
              (gridTime s v K n m) X) a = ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C) →
        ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrN d (sz.L n) (sz.W n) (E n) k
            (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') →
        SubGaussStopN sz (E n) σ (gridTime s v K n) τ
          (fun j ω => zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω)) m a j
          (cQVNZN sz E s v K n k C Γ Λ D'' j) := by
  intro d k sz E s v K n σ A C Γ Λ Φ τ' D' D'' τ hk hE hs0 hsv hv1 hC hΓ hΛ hτ hG m hm a j hj
    ⟨κ, hκ, hκC⟩ hδ
  have hKn : K n ≠ 0 := by omega
  have hmono : ∀ i i', i ≤ i' → gridTime s v K n i ≤ gridTime s v K n i' := fun i i' h =>
    ST_gridTime_mono s v K n (hsv n) h
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => by
    have h := hmono 0 i (Nat.zero_le i)
    rw [ST_gridTime_zero] at h
    linarith [hs0 n]
  have hule : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi =>
    (hmono i (K n) hi).trans_eq (gridTime_last s v K n hKn)
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => (hule i hi).trans_lt (hv1 n)
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hj1 : j + 1 ≤ K n := by omega
  have hL := sz.three_le_L n
  -- the stopped combination is the `κ`-weighted first-chaos sum
  have hcomm : ∀ ω' : PathΩ sz,
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1)) (gridTime s v K n m)
        (zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω')) a =
      ∑ b, κ b * ZfamN sz s v K n j (loopFamN sz E s v K n j σ) ω' b := by
    intro ω'
    rw [← zeroModeSet_Ugen hL (hE n).le σ (hu0 m) (hu1 m hm) A]
    exact hκ _
  -- the variance majorant on the good set
  have hQ : ∀ M ∈ sz.GoodSetN n (E n) (gridTime s v K n j) k Γ Λ Φ τ' D', M.IsHermitian →
      gridStep s v K n * ∑ c : CoordF d (sz.L n) (sz.W n),
        (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
          ‖∑ b, κ b * dirDerivN (loopFamN sz E s v K n j σ b) M
            (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤
        (cQVNZN sz E s v K n k C Γ Λ D'' j : ℝ) := by
    intro M hM hMh
    have hq := qvPropagatedN d sz n (E n) (hE n) (gridTime s v K n (j + 1)) (hu0 _) (hu1 _ hj1)
      M hMh k hk σ κ
    obtain ⟨-, -, -, -, -, -, hD4, -, -⟩ := hM
    have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := hmono j (j + 1) (Nat.le_succ j)
    have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hee : ∀ b b' : Fin k → Zd d (sz.L n),
        ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤
          Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
            etaT (E n) (gridTime s v K n j)) + ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
      intro b b'
      have h1 := hD4 σ b b'
      have h2 := norm_STeeM_shiftN_le sz n (hE n) hMh hjj (hu1 _ hj1) σ b b'
      have h3 : ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b'‖ ≤
          ‖sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ +
            ‖sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b' -
              sz.STeeM n (E n) (gridTime s v K n j) M σ b b'‖ := by
        have := norm_add_le (sz.STeeM n (E n) (gridTime s v K n j) M σ b b')
          (sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b' -
            sz.STeeM n (E n) (gridTime s v K n j) M σ b b')
        rwa [add_sub_cancel] at this
      linarith
    have hMee0 : 0 ≤ Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
        etaT (E n) (gridTime s v K n j)) + ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
      (norm_nonneg _).trans (hee (fun _ => 0) (fun _ => 0))
    have hre := qtNZ_re_sum_le κ (fun b b' => sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b')
      hκC hMee0 hee
    calc gridStep s v K n * ∑ c : CoordF d (sz.L n) (sz.W n),
          (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
            ‖∑ b, κ b * dirDerivN (loopFamN sz E s v K n j σ b) M
              (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2
        ≤ gridStep s v K n * ((k : ℝ) * (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
            sz.STeeM n (E n) (gridTime s v K n (j + 1)) M σ b b').re) :=
          mul_le_mul_of_nonneg_left hq hΔ
      _ ≤ gridStep s v K n * ((k : ℝ) * (C ^ 2 * (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
            etaT (E n) (gridTime s v K n j)) + ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre (Nat.cast_nonneg k)) hΔ
      _ = gridStep s v K n * ((k : ℝ) * C ^ 2 *
            (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
              etaT (E n) (gridTime s v K n j)) + ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ (cQVNZN sz E s v K n k C Γ Λ D'' j : ℝ) := Real.le_coe_toNNReal _
  have hΦ : ∀ b, HermTestFun sz n (loopFamN sz E s v K n j σ b) := fun b =>
    (hermTestFunLoopN sz k n (E n) (gridTime s v K n (j + 1)) (hE n) (hu0 _) (hu1 _ hj1) σ b).1
  have key := azumaSubGN sz s v K n (loopFamN sz E s v K n j σ) hΦ κ τ
    (fun j' => sz.GoodSetN n (E n) (gridTime s v K n j') k Γ Λ Φ τ' D') hτ hG j
    (cQVNZN sz E s v K n k C Γ Λ D'' j) hQ
  have hfun : (fun ω' : PathΩ sz => Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s v K n (j + 1))
        (gridTime s v K n m) (zeroModeSet d (sz.L n) A (ZvecN sz E s v K n j σ ω')) a) =
      fun ω => ∑ b, κ b * ZfamN sz s v K n j (loopFamN sz E s v K n j σ) ω b :=
    funext hcomm
  unfold SubGaussStopN
  simp only []
  rw [hfun]
  exact key

end Azuma

/-! ## 7. The `Y`-moment inputs pass to `Q^{(A)} Y` (target 8) -/

section Moments

variable {Ω : Type*} {m : MeasurableSpace Ω} [m₀ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- `|x| ≤ 1 + x⁴`. -/
private theorem qtNZ_abs_le (x : ℝ) : |x| ≤ 1 + x ^ 4 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x ^ 2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x + 1 / 2)]

/-- `x² ≤ 1 + x⁴`. -/
private theorem qtNZ_sq_le (x : ℝ) : x ^ 2 ≤ 1 + x ^ 4 := by
  nlinarith [sq_nonneg (x ^ 2 - 1 / 2)]

/-- **A real linear combination of conditionally centred `L⁴` variables**: with weights `q` and
`c = Σ|q|`, the combination `y = Σ q_i x_i` is conditionally centred, in `L⁴`, with
`E[y² | m] ≤ c² v` and `E y⁴ ≤ c⁴ w` when each `x_i` has `E[x_i² | m] ≤ v` and `E x_i⁴ ≤ w`
(Cauchy-Schwarz twice: `y² ≤ c Σ|q_i| x_i²`, `y⁴ ≤ c³ Σ|q_i| x_i⁴`; linearity and monotonicity of the
conditional expectation). -/
private theorem qtNZ_comb {ι : Type*} [Fintype ι]
    (x : ι → Ω → ℝ) (q : ι → ℝ) {v w : ℝ}
    (hxm : ∀ i, AEStronglyMeasurable (x i) μ)
    (h0 : ∀ i, μ[x i | m] =ᵐ[μ] 0)
    (h4 : ∀ i, Integrable (fun ω => x i ω ^ 4) μ)
    (h2 : ∀ i, μ[fun ω => x i ω ^ 2 | m] ≤ᵐ[μ] fun _ => v)
    (hi4 : ∀ i, ∫ ω, x i ω ^ 4 ∂μ ≤ w) :
    μ[fun ω => ∑ i, q i * x i ω | m] =ᵐ[μ] 0 ∧
    Integrable (fun ω => (∑ i, q i * x i ω) ^ 4) μ ∧
    μ[fun ω => (∑ i, q i * x i ω) ^ 2 | m] ≤ᵐ[μ] (fun _ => (∑ i, |q i|) ^ 2 * v) ∧
    ∫ ω, (∑ i, q i * x i ω) ^ 4 ∂μ ≤ (∑ i, |q i|) ^ 4 * w := by
  set c : ℝ := ∑ i, |q i| with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hint1 : ∀ i, Integrable (x i) μ := fun i =>
    Integrable.mono' ((integrable_const (1 : ℝ)).add (h4 i)) (hxm i)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact qtNZ_abs_le (x i ω))
  have hsq_meas : ∀ i, AEStronglyMeasurable (fun ω => x i ω ^ 2) μ := fun i =>
    (continuous_pow 2).comp_aestronglyMeasurable (hxm i)
  have hint2 : ∀ i, Integrable (fun ω => x i ω ^ 2) μ := fun i =>
    Integrable.mono' ((integrable_const (1 : ℝ)).add (h4 i)) (hsq_meas i)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact qtNZ_sq_le (x i ω))
  have hy_meas : AEStronglyMeasurable (fun ω => ∑ i, q i * x i ω) μ :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hxm i).const_mul (q i)
  have hy2_meas : AEStronglyMeasurable (fun ω => (∑ i, q i * x i ω) ^ 2) μ :=
    (continuous_pow 2).comp_aestronglyMeasurable hy_meas
  have hy4_meas : AEStronglyMeasurable (fun ω => (∑ i, q i * x i ω) ^ 4) μ :=
    (continuous_pow 4).comp_aestronglyMeasurable hy_meas
  -- pointwise Cauchy-Schwarz
  have P2 : ∀ ω, (∑ i, q i * x i ω) ^ 2 ≤ c * ∑ i, |q i| * x i ω ^ 2 := by
    intro ω
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ) (r := fun i => q i * x i ω)
      (f := fun i => |q i|) (g := fun i => |q i| * x i ω ^ 2) (fun i _ => abs_nonneg _)
      (fun i _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)) (fun i _ => ?_)
    have : (q i * x i ω) ^ 2 = |q i| * (|q i| * x i ω ^ 2) := by
      rw [mul_pow, ← sq_abs (q i)]; ring
    exact this.le
  have P2' : ∀ ω, (∑ i, |q i| * x i ω ^ 2) ^ 2 ≤ c * ∑ i, |q i| * x i ω ^ 4 := by
    intro ω
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun i => |q i| * x i ω ^ 2) (f := fun i => |q i|) (g := fun i => |q i| * x i ω ^ 4)
      (fun i _ => abs_nonneg _) (fun i _ => mul_nonneg (abs_nonneg _) (by positivity))
      (fun i _ => ?_)
    have : (|q i| * x i ω ^ 2) ^ 2 = |q i| * (|q i| * x i ω ^ 4) := by ring
    exact this.le
  have P4 : ∀ ω, (∑ i, q i * x i ω) ^ 4 ≤ c ^ 3 * ∑ i, |q i| * x i ω ^ 4 := by
    intro ω
    have h1 : (∑ i, q i * x i ω) ^ 4 = ((∑ i, q i * x i ω) ^ 2) ^ 2 := by ring
    have h2 : ((∑ i, q i * x i ω) ^ 2) ^ 2 ≤ (c * ∑ i, |q i| * x i ω ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) (P2 ω) 2
    have h3 : (c * ∑ i, |q i| * x i ω ^ 2) ^ 2 = c ^ 2 * (∑ i, |q i| * x i ω ^ 2) ^ 2 := by ring
    have h4' : c ^ 2 * (∑ i, |q i| * x i ω ^ 2) ^ 2 ≤ c ^ 2 * (c * ∑ i, |q i| * x i ω ^ 4) :=
      mul_le_mul_of_nonneg_left (P2' ω) (sq_nonneg _)
    calc (∑ i, q i * x i ω) ^ 4 ≤ c ^ 2 * (c * ∑ i, |q i| * x i ω ^ 4) := by
          rw [h1]; exact h2.trans (h3.le.trans h4')
      _ = c ^ 3 * ∑ i, |q i| * x i ω ^ 4 := by ring
  -- integrable majorants
  have hdom4 : Integrable (fun ω => c ^ 3 * ∑ i, |q i| * x i ω ^ 4) μ :=
    (integrable_finsetSum _ fun i _ => (h4 i).const_mul (|q i|)).const_mul (c ^ 3)
  have hdom2 : Integrable (fun ω => c * ∑ i, |q i| * x i ω ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => (hint2 i).const_mul (|q i|)).const_mul c
  have hy4 : Integrable (fun ω => (∑ i, q i * x i ω) ^ 4) μ :=
    Integrable.mono' hdom4 hy4_meas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact P4 ω)
  have hy2 : Integrable (fun ω => (∑ i, q i * x i ω) ^ 2) μ :=
    Integrable.mono' hdom2 hy2_meas (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact P2 ω)
  refine ⟨?_, hy4, ?_, ?_⟩
  · -- conditional mean
    have hfs : (fun ω => ∑ i, q i * x i ω) = ∑ i, (q i • x i) := by
      funext ω; simp [Finset.sum_apply]
    rw [hfs]
    have h1 := condExp_finsetSum (μ := μ) (s := Finset.univ) (f := fun i => q i • x i)
      (fun i _ => (hint1 i).smul (q i)) m
    have h2 : ∀ᵐ ω ∂μ, ∀ i, (μ[q i • x i | m]) ω = 0 := by
      rw [ae_all_iff]
      intro i
      filter_upwards [condExp_smul (μ := μ) (q i) (x i) m, h0 i] with ω hω1 hω2
      rw [hω1, Pi.smul_apply, hω2]
      simp
    filter_upwards [h1, h2] with ω hω1 hω2
    rw [hω1, Finset.sum_apply]
    exact Finset.sum_eq_zero fun i _ => hω2 i
  · -- conditional second moment
    have hfs : (fun ω => c * ∑ i, |q i| * x i ω ^ 2) = c • ∑ i, (|q i| • fun ω => x i ω ^ 2) := by
      funext ω; simp [Finset.sum_apply]
    have hmono := condExp_mono (m := m) hy2 hdom2 (Filter.Eventually.of_forall P2)
    have hA := condExp_smul (μ := μ) c (∑ i, (|q i| • fun ω => x i ω ^ 2)) m
    have hB := condExp_finsetSum (μ := μ) (s := Finset.univ)
      (f := fun i => |q i| • fun ω => x i ω ^ 2) (fun i _ => (hint2 i).smul (|q i|)) m
    have hC : ∀ᵐ ω ∂μ, ∀ i, (condExp m μ (|q i| • fun ω => x i ω ^ 2)) ω ≤ |q i| * v := by
      rw [ae_all_iff]
      intro i
      filter_upwards [condExp_smul (μ := μ) (|q i|) (fun ω => x i ω ^ 2) m, h2 i] with ω hω1 hω2
      rw [hω1, Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hω2 (abs_nonneg _)
    filter_upwards [hmono, hA, hB, hC] with ω hω1 hω2 hω3 hω4
    rw [hfs] at hω1
    refine hω1.trans ?_
    rw [hω2, Pi.smul_apply, smul_eq_mul, hω3, Finset.sum_apply]
    calc c * ∑ i, (condExp m μ (|q i| • fun ω => x i ω ^ 2)) ω ≤ c * ∑ i, |q i| * v :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hω4 i) hc0
      _ = c ^ 2 * v := by rw [← Finset.sum_mul]; ring
  · -- fourth moment
    calc ∫ ω, (∑ i, q i * x i ω) ^ 4 ∂μ ≤ ∫ ω, c ^ 3 * ∑ i, |q i| * x i ω ^ 4 ∂μ :=
          integral_mono hy4 hdom4 P4
      _ = c ^ 3 * ∑ i, |q i| * ∫ ω, x i ω ^ 4 ∂μ := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (h4 i).const_mul (|q i|)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
      _ ≤ c ^ 3 * ∑ i, |q i| * w := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc0 3)
          exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi4 i) (abs_nonneg _)
      _ = c ^ 4 * w := by rw [← Finset.sum_mul]; ring

/-- **One scalar multiple**: `qtNZ_comb` at a single term. If `Z` is conditionally centred with
`E[Z² | m] ≤ V`, `E Z⁴ ≤ W` (`V, W ≥ 0`) and `|r| ≤ R`, then `r Z` is conditionally centred, in `L⁴`, with
`E[(rZ)² | m] ≤ R² V` and `E (rZ)⁴ ≤ R⁴ W`. -/
private theorem qtNZ_scalar (Z : Ω → ℝ) (r R : ℝ) (hr : |r| ≤ R) {V W : ℝ} (hV : 0 ≤ V)
    (hW : 0 ≤ W) (hZm : AEStronglyMeasurable Z μ) (hZ0 : μ[Z | m] =ᵐ[μ] 0)
    (hZ4 : Integrable (fun ω => Z ω ^ 4) μ) (hZ2 : μ[fun ω => Z ω ^ 2 | m] ≤ᵐ[μ] fun _ => V)
    (hZW : ∫ ω, Z ω ^ 4 ∂μ ≤ W) :
    μ[fun ω => r * Z ω | m] =ᵐ[μ] 0 ∧ Integrable (fun ω => (r * Z ω) ^ 4) μ ∧
      μ[fun ω => (r * Z ω) ^ 2 | m] ≤ᵐ[μ] (fun _ => R ^ 2 * V) ∧
      ∫ ω, (r * Z ω) ^ 4 ∂μ ≤ R ^ 4 * W := by
  obtain ⟨c0, c4, c2, cI⟩ := qtNZ_comb (m := m) (μ := μ) (ι := Unit) (fun _ => Z) (fun _ => r)
    (v := V) (w := W) (fun _ => hZm) (fun _ => hZ0) (fun _ => hZ4) (fun _ => hZ2) (fun _ => hZW)
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  have hr2 : r ^ 2 ≤ R ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg r) hr 2
    rwa [sq_abs] at this
  have h4abs : |r| ^ 4 = r ^ 4 := Even.pow_abs (by decide) r
  have hr4 : r ^ 4 ≤ R ^ 4 := by
    have := pow_le_pow_left₀ (abs_nonneg r) hr 4
    rwa [h4abs] at this
  simp only [Finset.univ_unique, Finset.sum_singleton] at c0 c4 c2 cI
  refine ⟨c0, c4, c2.trans (Filter.Eventually.of_forall fun ω => ?_), cI.trans ?_⟩
  · rw [sq_abs]
    exact mul_le_mul_of_nonneg_right hr2 hV
  · rw [h4abs]
    exact mul_le_mul_of_nonneg_right hr4 hW

/-- A real variable `f` that is `0` or `g` at every point, with `g` measurable and `f⁴`
a.e.-strongly measurable, is a.e.-strongly measurable (`f = f⁴ / g³` pointwise, `x/0 = 0`): the set
`{j < τ}` of a stopping family need not be measurable here. -/
private theorem qtNZ_aesm_of_pow4 (f g : Ω → ℝ) (hg : Measurable g)
    (hfg : ∀ ω, f ω = 0 ∨ f ω = g ω) (hf4 : AEStronglyMeasurable (fun ω => f ω ^ 4) μ) :
    AEStronglyMeasurable f μ := by
  have heq : f = fun ω => f ω ^ 4 / g ω ^ 3 := by
    funext ω
    rcases hfg ω with h | h
    · simp [h]
    · rw [h]
      by_cases hg0 : g ω = 0
      · simp [hg0]
      · field_simp
  rw [heq]
  exact (hf4.aemeasurable.div (hg.pow_const 3).aemeasurable).aestronglyMeasurable

end Moments

section YMoments

variable {d : ℕ} (sz : Sizes d)

/-- `Q^{(A)}` commutes with the stopped propagated increment: the `b`-th stopped edge of `Q^{(A)} Y`
is `Σ_{b'} q_{b b'}` times the `b'`-th stopped edge of `Y` (`zeroModeSet_Ugen` for `0 ≤ u_m < 1`,
`|E| ≤ 2`, `3 ≤ L`; the real kernel `q` of `Q^{(A)}`). -/
private theorem qtNZ_stopped_comm {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k))
    (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ)
    (hE : |E| ≤ 2) (hum0 : 0 ≤ u m) (hum1 : u m < 1) (b : Fin k → Zd d (sz.L n)) (j : ℕ)
    (ω : PathΩ sz) :
    stoppedEdgeN sz E σ u (u m) τ (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω =
      ∑ b', ((qtNZ_q d (sz.L n) A b b' : ℝ) : ℂ) * stoppedEdgeN sz E σ u (u m) τ Y b' j ω := by
  unfold stoppedEdgeN
  by_cases hω : ω ∈ {ω' | j < τ ω'}
  · simp only [Set.indicator_of_mem hω]
    rw [← zeroModeSet_Ugen (sz.three_le_L n) hE σ hum0 hum1 A, qtNZ_zeroModeSet_apply]
  · simp [Set.indicator_of_notMem hω]

/-- Target 8, `RBM.Ind.yMomentBounds_nzN`: the `Y`-moment inputs (`YMomentBoundsN`,
`GridAssemblyN.lean:141`) pass to `Q^{(A)} Y` with the levels `4^{|A|+1} v`, `16^{|A|+1} w`.
`stoppedEdgeN (Q^{(A)} Y)_b = Σ_{b'} q_{b b'} stoppedEdgeN (Y)_{b'}` (commutation at `u_m`) with the
real kernel `q` of `Q^{(A)}` and `Σ_{b'} |q_{b b'}| ≤ 2^{|A|}`; then linearity of the conditional
expectation and `(Σ q x)² ≤ (Σ|q|) Σ|q| x²`, `(Σ q x)⁴ ≤ (Σ|q|)³ Σ|q| x⁴` (`qtNZ_comb`, for the real
and the imaginary part separately, `q` being real); the measurability of the stopped edges needs no
measurability of `{j < τ}` (`qtNZ_aesm_of_pow4`). -/
theorem yMomentBounds_nzN :
    ∀ {d : ℕ} (sz : Sizes d) {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
      (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ),
      |E| ≤ 2 → (∀ i ≤ K, 0 ≤ u i) → (∀ i ≤ K, u i < 1) →
      YMomentBoundsN sz E σ u τ K Y v w →
      YMomentBoundsN sz E σ u τ K (fun j ω => zeroModeSet d (sz.L n) A (Y j ω))
        (fun j => 4 ^ (A.card + 1) * v j) (fun j => 16 ^ (A.card + 1) * w j) := by
  intro d sz n k E σ A u τ K Y v w hE hu0 hu1 hY
  obtain ⟨hYm, hY⟩ := hY
  refine ⟨fun j => ?_, fun m hm b j hj => ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional
      (zeroModeSetLin (d := d) (L := sz.L n) A)).comp_stronglyMeasurable (hYm j)
  · -- the stopped edges of `Y` and their real kernel
    have hall := fun b' => hY m hm b' j hj
    have hid := qtNZ_stopped_comm sz E σ A u τ Y m hE (hu0 m hm) (hu1 m hm) b j
    -- measurability of the (unstopped) `b'`-th edge
    have hgm : ∀ b', Measurable (fun ω => (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
        (Y j ω) b').re) := by
      intro b'
      have hcont : Continuous (fun T : (Fin k → Zd d (sz.L n)) → ℂ =>
          (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) T b').re) := by
        refine Complex.continuous_re.comp ?_
        unfold Ugen UN
        exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
      exact (hcont.comp_stronglyMeasurable ((hYm j).mono ((filt sz).le (j + 1)))).measurable
    have hgm' : ∀ b', Measurable (fun ω => (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
        (Y j ω) b').im) := by
      intro b'
      have hcont : Continuous (fun T : (Fin k → Zd d (sz.L n)) → ℂ =>
          (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) T b').im) := by
        refine Complex.continuous_im.comp ?_
        unfold Ugen UN
        exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
      exact (hcont.comp_stronglyMeasurable ((hYm j).mono ((filt sz).le (j + 1)))).measurable
    have hre_dich : ∀ b' ω, (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).re = 0 ∨
        (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).re =
          (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b').re := by
      intro b' ω
      by_cases hω : ω ∈ {ω' | j < τ ω'}
      · right; simp [stoppedEdgeN, Set.indicator_of_mem hω]
      · left; simp [stoppedEdgeN, Set.indicator_of_notMem hω]
    have him_dich : ∀ b' ω, (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).im = 0 ∨
        (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).im =
          (Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b').im := by
      intro b' ω
      by_cases hω : ω ∈ {ω' | j < τ ω'}
      · right; simp [stoppedEdgeN, Set.indicator_of_mem hω]
      · left; simp [stoppedEdgeN, Set.indicator_of_notMem hω]
    have hre_m : ∀ b', AEStronglyMeasurable
        (fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).re) (pathP sz) := fun b' =>
      qtNZ_aesm_of_pow4 _ _ (hgm b') (hre_dich b') (hall b').2.2.1.aestronglyMeasurable
    have him_m : ∀ b', AEStronglyMeasurable
        (fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).im) (pathP sz) := fun b' =>
      qtNZ_aesm_of_pow4 _ _ (hgm' b') (him_dich b') (hall b').2.2.2.1.aestronglyMeasurable
    -- the real kernel
    set q : (Fin k → Zd d (sz.L n)) → ℝ := fun b' => qtNZ_q d (sz.L n) A b b' with hq
    have hre_pt : ∀ ω, (stoppedEdgeN sz E σ u (u m) τ
          (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω).re =
        ∑ b', q b' * (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).re := by
      intro ω
      rw [hid ω, Complex.re_sum]
      exact Finset.sum_congr rfl fun b' _ => Complex.re_ofReal_mul _ _
    have him_pt : ∀ ω, (stoppedEdgeN sz E σ u (u m) τ
          (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω).im =
        ∑ b', q b' * (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).im := by
      intro ω
      rw [hid ω, Complex.im_sum]
      exact Finset.sum_congr rfl fun b' _ => Complex.im_ofReal_mul _ _
    -- the levels are nonnegative
    obtain ⟨b0⟩ : Nonempty (Fin k → Zd d (sz.L n)) := ⟨fun _ => 0⟩
    have hv0 : 0 ≤ v j := by
      have h1 : 0 ≤ᵐ[pathP sz] (pathP sz)[fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b0 j ω).re ^ 2 |
          filt sz j] := condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      obtain ⟨ω, hω⟩ := (h1.and (hall b0).2.2.2.2.1).exists
      exact hω.1.trans hω.2
    have hw0 : 0 ≤ w j :=
      (integral_nonneg fun ω => by positivity).trans (hall b0).2.2.2.2.2.2.1
    -- the row sum of the kernel
    have hc0 : 0 ≤ ∑ b', |q b'| := Finset.sum_nonneg fun b' _ => abs_nonneg _
    have hc : ∑ b', |q b'| ≤ 2 ^ A.card := qtNZ_sum_abs_q_le A b
    have hc2 : (∑ b', |q b'|) ^ 2 ≤ 4 ^ (A.card + 1) := by
      calc (∑ b', |q b'|) ^ 2 ≤ ((2 : ℝ) ^ A.card) ^ 2 := pow_le_pow_left₀ hc0 hc 2
        _ = 4 ^ A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 4 ^ (A.card + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    have hc4 : (∑ b', |q b'|) ^ 4 ≤ 16 ^ (A.card + 1) := by
      calc (∑ b', |q b'|) ^ 4 ≤ ((2 : ℝ) ^ A.card) ^ 4 := pow_le_pow_left₀ hc0 hc 4
        _ = 16 ^ A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 16 ^ (A.card + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    -- the real and imaginary parts
    obtain ⟨r0, r4, r2, rI⟩ := qtNZ_comb (m := filt sz j) (μ := pathP sz)
      (fun b' ω => (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).re) q hre_m
      (fun b' => (hall b').1) (fun b' => (hall b').2.2.1)
      (fun b' => (hall b').2.2.2.2.1) (fun b' => (hall b').2.2.2.2.2.2.1)
    obtain ⟨i0, i4, i2, iI⟩ := qtNZ_comb (m := filt sz j) (μ := pathP sz)
      (fun b' ω => (stoppedEdgeN sz E σ u (u m) τ Y b' j ω).im) q him_m
      (fun b' => (hall b').2.1) (fun b' => (hall b').2.2.2.1)
      (fun b' => (hall b').2.2.2.2.2.1) (fun b' => (hall b').2.2.2.2.2.2.2)
    simp only [hre_pt, him_pt]
    refine ⟨r0, i0, r4, i4, ?_, ?_, ?_, ?_⟩
    · refine r2.trans (Filter.Eventually.of_forall fun ω => ?_)
      exact mul_le_mul_of_nonneg_right hc2 hv0
    · refine i2.trans (Filter.Eventually.of_forall fun ω => ?_)
      exact mul_le_mul_of_nonneg_right hc2 hv0
    · exact rI.trans (mul_le_mul_of_nonneg_right hc4 hw0)
    · exact iI.trans (mul_le_mul_of_nonneg_right hc4 hw0)

end YMoments

/-! ## 8. The budget of the case-(ii) grid endpoint (target 9) -/

section Budget

/-- The absorption step (`y N_p ≤ B`, `N_p⁻¹ ≤ X`, `B ≥ 0` give `y ≤ B X`). -/
private theorem qtNZ_absorb {y Np B X : ℝ} (hNp : 0 < Np) (hB : 0 ≤ B) (h : y * Np ≤ B)
    (hX : Np⁻¹ ≤ X) : y ≤ B * X := by
  have h1 : y ≤ B * Np⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hNp]; exact h
  exact h1.trans (mul_le_mul_of_nonneg_left hX hB)

/-- The final bookkeeping on plain reals: `t₁ ≤ P₀X/6`, `t₂ ≤ P₀(Φ₁+Φ₂+Φ₃)X/6`,
`t₃ ≤ P₀Λ^{1/2}X/12 + P₀X/12`, `t₄, t₅ ≤ P₀X/6` give `Σ t ≤ P₀(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) X`
(the coefficient of `Λ^{1/2} X` is `2/3 ≤ 1`, `X ≤ Λ^{1/2} X` for `Λ^{1/2} ≥ 1`). -/
private theorem qtNZ_final {t1 t2 t3 t4 t5 P0 X Λr Φ₁ Φ₂ Φ₃ : ℝ} (hP0 : 0 ≤ P0) (hX : 0 ≤ X)
    (hΛr : 1 ≤ Λr) (hΦ₁ : 0 ≤ Φ₁) (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (T1 : t1 ≤ P0 / 6 * X)
    (T2 : t2 ≤ P0 / 6 * ((Φ₁ + Φ₂ + Φ₃) * X))
    (T3 : t3 ≤ P0 / 12 * (Λr * X) + P0 / 12 * X) (T4 : t4 ≤ P0 / 6 * X)
    (T5 : t5 ≤ P0 / 6 * X) :
    t1 + t2 + t3 + t4 + t5 ≤ P0 * (Λr + Φ₁ + Φ₂ + Φ₃) * X := by
  have hPX : P0 * X ≤ P0 * (Λr * X) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hΛr) hP0
  have hΦ : 0 ≤ P0 * ((Φ₁ + Φ₂ + Φ₃) * X) :=
    mul_nonneg hP0 (mul_nonneg (add_nonneg (add_nonneg hΦ₁ hΦ₂) hΦ₃) hX)
  have e : P0 * (Λr + Φ₁ + Φ₂ + Φ₃) * X = P0 * (Λr * X) + P0 * ((Φ₁ + Φ₂ + Φ₃) * X) := by ring
  rw [e]
  nlinarith [T1, T2, T3, T4, T5, hPX, hΦ]

/-- Target 9, `RBM.Ind.budgetNZN`: the budget of the case-(ii) grid endpoint at the linear levels
(the analogue of `budgetNonAltLinN`, `NQLin.lean:966`; no ratio weights, no far parts):
`assembledRHSNZN ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.  `B_{u_j} ≤ B_v`, `B_s ≤ B_v`
(`STBctl_mono`), `Σ_j Δ/η_{u_j}` by `hlog`, `KΔ = v - s ≤ 1`, `B_v ≥ N^{-1}` (`cont_inv_size_le_Bctl`:
`N^{-D_Y}`, `N^{-D_t}`, `√(k W^{-D''})` are absorbed by `N^k ·`), `Λ ≥ 1`. -/
theorem budgetNZN :
    ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C cA : ℝ)
      (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ),
      2 ≤ k → 0 < C → 0 ≤ cA → 0 ≤ ε₁ → |E n| < 2 → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
      Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n → 0 ≤ Φ₁ n → 0 ≤ Φ₂ n → 0 ≤ Φ₃ n →
      ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
        (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
      X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k →
      ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) →
      C * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
          Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
      ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
          (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
      ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      cA * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      assembledRHSNZN sz E s v K n k C cA Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y τK εq X0 ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
          (sz.Bctl n (v n)) ^ k := by
  intro d sz E s v K n k C cA Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y D_t τK εq ε₀ ε₁ X0 hk hC hcA hε₁ hE hs0 hsv hv1
    hK hΓ hΛ hΦ₁ hΦ₂ hΦ₃ hlog hX0 hR H1 H2 H3 H4 H5 H6
  -- elementary facts
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : 1 ≤ (sz.W n * sz.L n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
    exact_mod_cast (show 1 ≤ sz.size n from h)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ k := pow_pos hN0 k
  have hmono : ∀ i i', i ≤ i' → gridTime s v K n i ≤ gridTime s v K n i' := fun i i' h =>
    ST_gridTime_mono s v K n hsv h
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => by
    have h := hmono 0 i (Nat.zero_le i)
    rw [ST_gridTime_zero] at h
    linarith
  have huK := gridTime_last s v K n hK
  have hule : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi =>
    (hmono i (K n) hi).trans_eq huK
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => (hule i hi).trans_lt hv1
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hKΔ : (K n : ℝ) * gridStep s v K n = v n - s n := by
    have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
    unfold gridStep
    rw [mul_div_cancel₀ _ hK']
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by rw [hKΔ]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hBv0 := Sizes.STBctl_pos sz n hv1
  have hX0' : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg hBv0.le _
  have hXN : (((sz.size n : ℕ) : ℝ) ^ k)⁻¹ ≤ (sz.Bctl n (v n)) ^ k := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le)
      (ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (mE_im_pos hE).le) (Real.log_nonneg hN1)
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  have hWD : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBmono : ∀ i ≤ K n, sz.Bctl n (gridTime s v K n i) ≤ sz.Bctl n (v n) := fun i hi =>
    Sizes.STBctl_mono sz n (hule i hi) hv1
  have hBpos : ∀ i ≤ K n, 0 < sz.Bctl n (gridTime s v K n i) := fun i hi =>
    Sizes.STBctl_pos sz n (hu1 i hi)
  have hη : ∀ i ≤ K n, 0 < etaT (E n) (gridTime s v K n i) := fun i hi => etaT_pos hE (hu1 i hi)
  -- T1: the initial term
  have T1 : C * X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k := by
    have hBs0 := Sizes.STBctl_pos sz n (hsv.trans_lt hv1)
    have hBs : sz.Bctl n (s n) ≤ sz.Bctl n (v n) := Sizes.STBctl_mono sz n hsv hv1
    calc C * X0 ≤ C * (((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :=
          mul_le_mul_of_nonneg_left hX0 hC.le
      _ = (C * ((sz.size n : ℕ) : ℝ) ^ ε₁) * (sz.Bctl n (s n)) ^ k := by ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * (sz.Bctl n (s n)) ^ k :=
          mul_le_mul_of_nonneg_right H1 (pow_nonneg hBs0.le _)
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * (sz.Bctl n (v n)) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBs0.le hBs k) (by positivity)
  -- T2: the drift term
  have T2 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      C * (cA * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) := by
    set X : ℝ := (sz.Bctl n (v n)) ^ k with hXdef
    set Ls : ℝ := (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) with hLsdef
    set Dc : ℝ := ((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n with hDc
    have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hDc0 : 0 ≤ Dc := by
      have := mul_nonneg hk2 hΦ₁
      linarith
    have hDc_le : Dc ≤ (k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n) := by
      have h0 : 0 ≤ 2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n := by
        have h1 : 0 ≤ (k : ℝ) - 1 := by linarith
        nlinarith [mul_nonneg h1 hΦ₂, mul_nonneg h1 hΦ₃]
      have e : (k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n) - Dc =
          2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n := by rw [hDc]; ring
      linarith
    have hterm : gridStep s v K n * ∑ j ∈ Finset.range (K n),
        C * (cA * dDriftLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) ≤
        (C * cA * Γ n * Γ n * Dc * X) * ∑ j ∈ Finset.range (K n),
          gridStep s v K n / etaT (E n) (gridTime s v K n j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
      have hBj : (sz.Bctl n (gridTime s v K n j)) ^ k ≤ X :=
        pow_le_pow_left₀ (hBpos j hjK).le (hBmono j hjK) k
      have hηj := hη j hjK
      unfold dDriftLinN
      calc gridStep s v K n * (C * (cA * (Γ n * Γ n *
              ((sz.Bctl n (gridTime s v K n j)) ^ k / etaT (E n) (gridTime s v K n j)) * Dc)))
          = (C * cA * Γ n * Γ n * Dc) * (gridStep s v K n *
              ((sz.Bctl n (gridTime s v K n j)) ^ k / etaT (E n) (gridTime s v K n j))) := by ring
        _ ≤ (C * cA * Γ n * Γ n * Dc) * (gridStep s v K n * (X / etaT (E n) (gridTime s v K n j))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hBj hηj.le) hΔ0)
              (by positivity)
        _ = (C * cA * Γ n * Γ n * Dc * X) * (gridStep s v K n / etaT (E n) (gridTime s v K n j)) := by
            ring
    have hpos : 0 ≤ C * cA * Γ n * Γ n * Dc * X := by positivity
    calc _ ≤ (C * cA * Γ n * Γ n * Dc * X) * ∑ j ∈ Finset.range (K n),
          gridStep s v K n / etaT (E n) (gridTime s v K n j) := hterm
      _ ≤ (C * cA * Γ n * Γ n * Dc * X) * Ls := mul_le_mul_of_nonneg_left hlog hpos
      _ ≤ (C * cA * Γ n * Γ n * ((k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n)) * X) * Ls := by
          refine mul_le_mul_of_nonneg_right ?_ hLs0
          refine mul_le_mul_of_nonneg_right ?_ hX0'
          exact mul_le_mul_of_nonneg_left hDc_le (by positivity)
      _ = (C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * Ls) *
            ((Φ₁ n + Φ₂ n + Φ₃ n) * X) := by rw [hΓ]; ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * ((Φ₁ n + Φ₂ n + Φ₃ n) * X) :=
          mul_le_mul_of_nonneg_right H2
            (mul_nonneg (add_nonneg (add_nonneg hΦ₁ hΦ₂) hΦ₃) hX0')
  -- T3: the quadratic-variation term
  have T3 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    set X : ℝ := (sz.Bctl n (v n)) ^ k with hXdef
    set Ls : ℝ := (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) with hLsdef
    -- the summands
    have hcq : ∀ j ∈ Finset.range (K n),
        (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ) =
        (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * (gridStep s v K n *
            ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j))) +
          gridStep s v K n * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      intro j hj
      have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
      have hBj := hBpos j hjK
      have hηj := hη j hjK
      unfold cQVNZN
      rw [Real.coe_toNNReal _ (by positivity)]
      ring
    have hsum : ∑ j ∈ Finset.range (K n), (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ) ≤
        ((k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2) +
          (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
      rw [Finset.sum_congr rfl hcq, Finset.sum_add_distrib]
      refine add_le_add ?_ ?_
      · rw [← Finset.mul_sum]
        have h1 : ∑ j ∈ Finset.range (K n), gridStep s v K n *
            ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j)) ≤
            X ^ 2 * ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
          have hB2 : (sz.Bctl n (gridTime s v K n j)) ^ (2 * k) ≤ X ^ 2 := by
            calc (sz.Bctl n (gridTime s v K n j)) ^ (2 * k) ≤ (sz.Bctl n (v n)) ^ (2 * k) :=
                  pow_le_pow_left₀ (hBpos j hjK).le (hBmono j hjK) _
              _ = X ^ 2 := by rw [hXdef, ← pow_mul, mul_comm]
          have hηj := hη j hjK
          calc gridStep s v K n * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
                etaT (E n) (gridTime s v K n j))
              ≤ gridStep s v K n * (X ^ 2 / etaT (E n) (gridTime s v K n j)) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB2 hηj.le) hΔ0
            _ = X ^ 2 * (gridStep s v K n / etaT (E n) (gridTime s v K n j)) := by ring
        have hc0 : 0 ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n := by positivity
        calc (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * ∑ j ∈ Finset.range (K n), gridStep s v K n *
              ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j))
            ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * (X ^ 2 * Ls) :=
              mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hlog (sq_nonneg _))) hc0
          _ = (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 := by ring
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        calc (K n : ℝ) * (gridStep s v K n * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')))
            = ((K n : ℝ) * gridStep s v K n) * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
              ring
          _ ≤ 1 * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
              mul_le_mul_of_nonneg_right hKΔ1 (by positivity)
          _ = (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := one_mul _
    have ha0 : 0 ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 := by positivity
    have hb0 : 0 ≤ (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := by positivity
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt (((k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2) +
          (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) ≤
        C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X +
          C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine (nqBudget_sqrt_add_le ha0 hb0).trans (le_of_eq ?_)
      have e1 : (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 =
          (C * Γ n * X) ^ 2 * (((k : ℝ) * Ls) * Λ n) := by ring
      have e2 : (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') =
          C ^ 2 * ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by ring
      have hA0 : 0 ≤ C * Γ n * X := by positivity
      rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC.le]
      ring
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * X) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * Ls))) * (Λ n ^ ((1 : ℝ) / 2) * X) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right H3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * X := by
      refine qtNZ_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) * ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact H4
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNZN sz E s v K n k C (Γ n) (Λ n) D'' j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X +
            C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) +
          ((sz.size n : ℕ) : ℝ) ^ εq * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
          ring
      _ ≤ _ := add_le_add k1 k2
  -- T4, T5
  have T4 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    qtNZ_absorb hNk (by positivity) ((mul_comm _ _).trans_le H5) hXN
  have T5 : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k := by
    have e : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
        stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k)) =
        cA * ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine (mul_le_mul_of_nonneg_left hR hcA).trans ?_
    exact qtNZ_absorb hNk (by positivity) ((mul_comm _ _).trans_le (by linarith [H6])) hXN
  unfold assembledRHSNZN
  exact qtNZ_final hP0 hX0' hΛr1 hΦ₁ hΦ₂ hΦ₃ T1 T2 T3 T4 T5

end Budget

/-! ## 9. Compiled nonempty instances (`d = 3`)

Numbering of the ticket.  (1) `idem_instance`, (2) `nzUgen_instance`, (3) `nz_hker_instance`: at `L = 4`
(`Zd 3 4`, 64 points), `g = 1` (`1 - g²/L² = 15/16`), `E = 0` (`m(+) = i`, `Im m = 1`), `σ = (+,-,+)`
(`I_diff(σ) = {0, 1}`), `A = I_diff(σ)`, the point mass `δ₀`, the case-(ii) window `(v, w) = (15/16, 31/32)` of
`PrecInst` (`szB`: `L = 4`, `ilambda = 1`).  (4) `nz_hdrift_instance`, (5) `subGaussStop_nz_instance`
(`cQVNZN_inst_pos`), (6) `yMoment_zero_instance` (`Y ≡ 0`, the `Y` of the merged bundle
`GridAssemblyNInst.gridAsm_bundle`) and `yMoment_random_instance` (a nonzero Gaussian `Y_j = ζ_j δ₀`),
(7) `budgetNZN_instance`: at the merged `sz0` of `NQLinInst`/`NQGood2Inst` (`L = 4`, `W = 32`, `N = 2^21`,
`E = 1/2`, grid `(sInst, vg, Kg) = (0, 1/32, 4)`, levels `(Γ, Λ, Φ) = (4, 3, 1)`, `(Φ₁, Φ₂, Φ₃) = (1, 12, 1)`,
`τ' = 1/5`, `D' = 6`, `D'' = 5`) with the exit time `tau0 = goodExitTauN …` of `NQGood2Inst` (positive at every
sample). -/

namespace QtNonzeroInst

open RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.GridGoodNInst RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.NQGood1Inst
  RBM.Ind.NQGood2Inst RBM.Ind.NQLinInst

/-- The point mass `δ₀` on `(Z_4^3)^3`. -/
private def qnDelta : (Fin 3 → Zd 3 4) → ℂ := fun a => if a = 0 then 1 else 0

private theorem qnDelta_ne : qnDelta ≠ 0 := fun h => by
  have := congrFun h 0
  simp [qnDelta] at this

/-- `I_diff(σ) = {0, 1}` for `σ = (+,-,+)`. -/
private theorem qnIdiff : STIdiff sig3 = {0, 1} := by decide

/-- `(Q^{(A)} δ₀)(0) = (1 - L^{-3})²` for `A = I_diff(σ) = {0, 1}` (the real kernel `q_{00}`), every `L`. -/
private theorem qn_Q_delta_zero' (L : ℕ) [NeZero L] :
    zeroModeSet 3 L (STIdiff sig3) (fun a : Fin 3 → Zd 3 L => if a = 0 then (1 : ℂ) else 0) 0 =
      (((1 - ((L : ℝ) ^ 3)⁻¹) ^ 2 : ℝ) : ℂ) := by
  rw [qtNZ_zeroModeSet_apply, Finset.sum_eq_single (0 : Fin 3 → Zd 3 L)]
  · have hq : qtNZ_q 3 L (STIdiff sig3) (0 : Fin 3 → Zd 3 L) 0 = (1 - ((L : ℝ) ^ 3)⁻¹) ^ 2 := by
      rw [qnIdiff]
      simp [qtNZ_q, qtNZ_f, Fin.prod_univ_three]
      ring
    simp [hq]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `(Q^{(A)} δ₀)(0) = (1 - 4^{-3})² = (63/64)²` (`L = 4`). -/
private theorem qn_Q_delta_zero :
    zeroModeSet 3 4 (STIdiff sig3) qnDelta 0 = (((63 / 64) ^ 2 : ℝ) : ℂ) := by
  have h := qn_Q_delta_zero' 4
  have e : (1 - (((4 : ℕ) : ℝ) ^ 3)⁻¹) ^ 2 = (63 / 64 : ℝ) ^ 2 := by norm_num
  rw [e] at h
  exact h

/-! ### (1) `zeroModeSet_idem` at `d = 3`, `L = 4`, `A = {0, 1}`, `T = δ₀` -/

/-- **Instance of `zeroModeSet_idem`**: `Q^{(A)} Q^{(A)} δ₀ = Q^{(A)} δ₀`, where `δ₀ ≠ 0` and
`Q^{(A)} δ₀` is neither `δ₀` nor `0` (its value at `0` is `(63/64)²`). -/
theorem idem_instance :
    zeroModeSet 3 4 (STIdiff sig3) (zeroModeSet 3 4 (STIdiff sig3) qnDelta) =
        zeroModeSet 3 4 (STIdiff sig3) qnDelta ∧
      qnDelta ≠ 0 ∧ zeroModeSet 3 4 (STIdiff sig3) qnDelta ≠ qnDelta ∧
      zeroModeSet 3 4 (STIdiff sig3) qnDelta ≠ 0 := by
  refine ⟨zeroModeSet_idem 3 4 3 _ qnDelta, qnDelta_ne, fun h => ?_, fun h => ?_⟩
  · have h0 := congrFun h 0
    rw [qn_Q_delta_zero] at h0
    simp [qnDelta] at h0
    norm_num at h0
  · have h0 := congrFun h 0
    rw [qn_Q_delta_zero] at h0
    simp at h0

/-! ### (2) `nzUgen_holds` at `L = 4`, `g = 1`, `E = 0`, `(v, w) = (15/16, 31/32)` -/

private theorem qn_mE0_im : (mE 0).im = 1 := by
  rw [mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Instance of `nzUgen_holds`** (`d = 3`, `k = 3`, `Λ_g = 1`, `κ' = 1/2`): at `L = 4`, `g = 1`
(`0 < g ≤ Λ_g`), `E = 0` (`κ' = 1/2 ≤ Im m(0) = 1`), the case-(ii) window `1 - g²/L² = 15/16 = v ≤ w = 31/32
< 1`, `σ = (+,-,+)`, `A = I_diff(σ)`, `X = δ₀`: the operator bound and the row at the label `0`, every
hypothesis discharged (`prop5Short_holds`, `prop8ZeroMode_holds` are unconditional). -/
theorem nzUgen_instance :
    ∃ C : ℝ, 0 < C ∧ qnDelta ≠ 0 ∧
      ‖zeroModeSet 3 4 (STIdiff sig3) (Ugen 3 4 1 0 sig3 (15 / 16) (31 / 32) qnDelta)‖ ≤
        C * ‖qnDelta‖ ∧
      ∃ κ : (Fin 3 → Zd 3 4) → ℂ,
        (∀ X : (Fin 3 → Zd 3 4) → ℂ,
          zeroModeSet 3 4 (STIdiff sig3) (Ugen 3 4 1 0 sig3 (15 / 16) (31 / 32) X) 0 =
            ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := nzUgen_holds 3 3 le_rfl (by norm_num) 1 (1 / 2) one_pos (by norm_num)
  have h := H 4 (by norm_num) 1 0 one_pos le_rfl (by norm_num) (by rw [qn_mE0_im]; norm_num)
    (15 / 16) (31 / 32) (by norm_num) (by norm_num) (by norm_num) (by norm_num) sig3
    (STIdiff sig3) (Finset.Subset.refl _)
  exact ⟨C, hC, qnDelta_ne, h.1 qnDelta, h.2 0⟩

/-! ### (3) `nz_hker` at `szB`, `K = 1`, `u_0 = 15/16`, `u_1 = 31/32`, `X = Q^{(A)} δ₀` -/

/-- The grid times `u_0 = 15/16`, `u_1 = 31/32` (`u_i = 15/16 + i/32`). -/
private def qnU : ℕ → ℝ := fun i => 15 / 16 + (i : ℝ) / 32

private theorem qnU_nonneg (i : ℕ) : 0 ≤ qnU i := by
  unfold qnU
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

private theorem qnU_lt_one {i : ℕ} (hi : i ≤ 1) : qnU i < 1 := by
  unfold qnU
  have : (i : ℝ) ≤ 1 := by exact_mod_cast hi
  linarith

private theorem qnU_ge {i : ℕ} : 15 / 16 ≤ qnU i := by
  unfold qnU
  have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

private theorem qnU_mono {i m : ℕ} (h : i ≤ m) : qnU i ≤ qnU m := by
  unfold qnU
  have : (i : ℝ) ≤ m := Nat.cast_le.2 h
  linarith

/-- **Instance of `nz_hker`**: the operator bound of (2) at the three pairs `(u_i, u_m)`, `i ≤ m ≤ 1`, gives
the `hker` bound `‖(𝒰_{u_i,u_m} X)(a)‖ ≤ C ‖X‖ + 0 · 0` for the nonzero fixed point `X = Q^{(A)} δ₀`
(`X ≠ 0`, class membership `Q^{(A)} X = X` by `zeroModeSet_idem`), at `sz = szB`, `n = 0`
(`L = 4`, `ilambda = 1`), every label `a`. -/
theorem nz_hker_instance :
    ∃ C : ℝ, 0 < C ∧ zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta ≠ 0 ∧
      ∀ i m, i ≤ m → m ≤ 1 → ∀ a : Fin 3 → Zd 3 (szB.L 0),
        ‖Ugen 3 (szB.L 0) (szB.lam 0) 0 sig3 (qnU i) (qnU m)
            (zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta) a‖ ≤
          C * ‖zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta‖ + 0 * 0 := by
  obtain ⟨C, hC, H⟩ := nzUgen_holds 3 3 le_rfl (by norm_num) 1 (1 / 2) one_pos (by norm_num)
  have hop : ∀ i m, i ≤ m → m ≤ 1 → ∀ X : (Fin 3 → Zd 3 (szB.L 0)) → ℂ,
      ‖zeroModeSet 3 (szB.L 0) (STIdiff sig3)
          (Ugen 3 (szB.L 0) (szB.lam 0) 0 sig3 (qnU i) (qnU m) X)‖ ≤ C * ‖X‖ := by
    intro i m him hm X
    have hi : i ≤ 1 := him.trans hm
    refine (H (szB.L 0) (szB.three_le_L 0) (szB.lam 0) 0 (by norm_num [szB]) (by norm_num [szB])
      (by norm_num) (by rw [qn_mE0_im]; norm_num) (qnU i) (qnU m) (qnU_nonneg i) ?_ (qnU_mono him)
      (qnU_lt_one hm) sig3 (STIdiff sig3) (Finset.Subset.refl _)).1 X
    have h := qnU_ge (i := i)
    norm_num [szB]
    linarith
  refine ⟨C, hC, idem_instance.2.2.2, fun i m him hm a => ?_⟩
  exact nz_hker szB 0 0 sig3 (STIdiff sig3) qnU 1 C hC.le (by norm_num)
    (fun i hi => qnU_nonneg i) (fun i hi => qnU_lt_one hi) hop i m him hm
    (zeroModeSet 3 (szB.L 0) (STIdiff sig3) qnDelta) _ 0 (norm_nonneg _) le_rfl
    (fun b => norm_le_pi_norm _ b) (zeroModeSet_idem 3 (szB.L 0) 3 _ _) a

/-! ### (4) `nz_hdriftN` on the `GoodLinN` instance of `NQLinInst`, `A = ∅` and `A = I_diff(σ)` -/

/-- **Instance of `nz_hdriftN`** at the data of `NQLinInst.hdrift_lin_instance` (`sz0`, `k = 3`, `σ = (+,-,+)`,
levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, 12, 1)`), for every `A`: strictly before the exit time of
`GoodSetN ∩ GoodLinN`, `‖(Q^{(A)} Dr_j)(b)‖ ≤ 2^{|A|} · dDriftLinN`. -/
theorem nz_hdrift_instance (A : Finset (Fin 3)) :
    ∀ ω j, j < Kg 0 →
      j < nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0 ω →
      ∀ b : Fin 3 → Zd 3 (sz0.L 0),
        ‖zeroModeSet 3 (sz0.L 0) A (driftTensorN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j)
            (pathH sz0 sInst vg Kg 0 j ω) sig3) b‖ ≤
          2 ^ A.card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 j) 3 (Γ4 0) (Φ1 0)
            ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0) :=
  nz_hdriftN sz0 (n := 0) (k := 3) (by norm_num) sig3 A Einst sInst vg Kg Γ4 Φ1 (fun _ => 12) Φ1
    (nqLinExitTauN sz0 Einst sInst vg Kg 3 Γ4 Λ3 Φ1 Φ1 (fun _ => 12) Φ1 (1 / 5) 6 0)
    (fun ω j hj => (mem_of_lt_nqLinExitTauN hj).2)

/-- `A = ∅`: the first grid step `j = 0` at every sample (the exit time is positive at every sample,
`nqLinExitTauN_pos`). -/
example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :
    ‖zeroModeSet 3 (sz0.L 0) (∅ : Finset (Fin 3)) (driftTensorN sz0 0 (Einst 0)
        (gridTime sInst vg Kg 0 0) (pathH sz0 sInst vg Kg 0 0 ω) sig3) b‖ ≤
      2 ^ (∅ : Finset (Fin 3)).card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0)
        (Φ1 0) ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0) :=
  nz_hdrift_instance ∅ ω 0 (by norm_num [Kg]) (nqLinExitTauN_pos ω) b

/-- `A = I_diff(σ)` (`|A| = 2`, the factor `2^{|A|} = 4`). -/
example (ω : PathΩ sz0) (b : Fin 3 → Zd 3 (sz0.L 0)) :
    ‖zeroModeSet 3 (sz0.L 0) (STIdiff sig3) (driftTensorN sz0 0 (Einst 0)
        (gridTime sInst vg Kg 0 0) (pathH sz0 sInst vg Kg 0 0 ω) sig3) b‖ ≤
      2 ^ (STIdiff sig3).card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0)
        (Φ1 0) ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0) :=
  nz_hdrift_instance (STIdiff sig3) ω 0 (by norm_num [Kg]) (nqLinExitTauN_pos ω) b

/-- The level of the bound is positive (so the instance is not vacuous): `2^{|A|} · dDriftLinN > 0`. -/
theorem nz_hdrift_level_pos (A : Finset (Fin 3)) :
    0 < 2 ^ A.card * dDriftLinN sz0 0 (Einst 0) (gridTime sInst vg Kg 0 0) 3 (Γ4 0) (Φ1 0)
      ((fun _ : ℕ => (12 : ℝ)) 0) (Φ1 0) := by
  have h : 0 < dDriftLinN sz0 0 (1 / 2) 0 3 4 1 12 1 := dDriftLinN_inst_pos
  have e : gridTime sInst vg Kg 0 0 = 0 := grid_data.2.1
  have e' : Einst 0 = 1 / 2 := rfl
  rw [e, e']
  exact mul_pos (by positivity) h

/-! ### (5) `subGaussStop_nzN` at the `sz0` grid data of `NQLinInst` -/

private theorem qn_gridTime_nonneg (i : ℕ) : 0 ≤ gridTime sInst vg Kg 0 i := by
  have h := ST_gridTime_mono sInst vg Kg 0 (sInst_le_vg 0) (Nat.zero_le i)
  rw [ST_gridTime_zero] at h
  exact (sInst_nonneg 0).trans h

private theorem qn_gridTime_le {i : ℕ} (hi : i ≤ Kg 0) : gridTime sInst vg Kg 0 i ≤ 1 / 32 := by
  have h := (ST_gridTime_mono sInst vg Kg 0 (sInst_le_vg 0) hi).trans_eq
    (gridTime_last sInst vg Kg 0 (by norm_num [Kg]))
  simpa [vg] using h

/-- **Instance of `subGaussStop_nzN`**: at `sz0` (`L = 4`, `W = 32`), `E = 1/2`, `k = 3`, `σ = (+,-,+)`, the grid
`(0, 1/32, 4)`, the exit time `tau0` of `GoodSetN` (levels `(4, 3, 1)`, `τ' = 1/5`, `D' = 6`, positive at every
sample), `D'' = 5` (the shift hypothesis is `delta_shift_ok`), every `m ≤ 4`, `j < m`, every label `a`,
every `A`: the row premise is the coarse row `Σ_b|κ_b| ≤ 2^{|A|} ((1-u_{j+1})/(1-u_m))^3 ≤ C₀ := 2^{|A|}
(32/31)^3` of `qtNZ_row_coarse` (the case-(ii) window of EK-5 does not contain `u_{j+1} ≤ 1/32` here). -/
theorem subGaussStop_nz_instance (A : Finset (Fin 3)) (m : ℕ) (hm : m ≤ Kg 0)
    (a : Fin 3 → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < m) :
    SubGaussStopN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0
      (fun j ω => zeroModeSet 3 (sz0.L 0) A (ZvecN sz0 Einst sInst vg Kg 0 j sig3 ω)) m a j
      (cQVNZN sz0 Einst sInst vg Kg 0 3 (2 ^ A.card * (32 / 31) ^ 3) (Γ4 0) (Λ3 0) 5 j) := by
  have hj1 : j + 1 ≤ Kg 0 := hj.trans_le hm
  have hv0 := qn_gridTime_nonneg (j + 1)
  have hvw : gridTime sInst vg Kg 0 (j + 1) ≤ gridTime sInst vg Kg 0 m :=
    ST_gridTime_mono sInst vg Kg 0 (sInst_le_vg 0) (by omega)
  have hw1 : gridTime sInst vg Kg 0 m < 1 := (qn_gridTime_le hm).trans_lt (by norm_num)
  obtain ⟨κ, hκ, hκC⟩ := qtNZ_row_coarse 3 (sz0.L 0) (sz0.lam 0) (sz0.three_le_L 0)
    (Einst_abs_lt 0).le sig3 A hv0 hvw hw1 a
  have hratio : (1 - gridTime sInst vg Kg 0 (j + 1)) / (1 - gridTime sInst vg Kg 0 m) ≤ 32 / 31 := by
    have h1 := qn_gridTime_le hm
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hr0 : 0 ≤ (1 - gridTime sInst vg Kg 0 (j + 1)) / (1 - gridTime sInst vg Kg 0 m) :=
    div_nonneg (by linarith) (by linarith)
  refine subGaussStop_nzN sz0 Einst sInst vg Kg 0 sig3 A (2 ^ A.card * (32 / 31) ^ 3) (Γ4 0) (Λ3 0)
    (Φ1 0) (1 / 5) 6 5 tau0 (by norm_num) Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one
    (by positivity) (by norm_num [Γ4]) (by norm_num [Λ3])
    (goodExitMeasN sz0 Einst sInst vg Kg 0 3 Γ4 Λ3 Φ1 (1 / 5) 6) tau0_mem m hm a j hj
    ⟨κ, hκ, hκC.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hratio 3) (by positivity))⟩
    (delta_shift_ok j (hj.trans_le hm))

/-- The proxy of the instance is positive (`Δ = 1/128 > 0`, `C₀ > 0`, `Γ = 4`, `Λ = 3`, `B_{u_j} > 0`,
`η_{u_j} > 0`): `SubGaussStopN` is not asserted at the trivial proxy `0`. -/
theorem cQVNZN_inst_pos (A : Finset (Fin 3)) {j : ℕ} (hj : j < Kg 0) :
    0 < cQVNZN sz0 Einst sInst vg Kg 0 3 (2 ^ A.card * (32 / 31) ^ 3) (Γ4 0) (Λ3 0) 5 j := by
  unfold cQVNZN
  rw [Real.toNNReal_pos]
  have hΔ : 0 < gridStep sInst vg Kg 0 := by rw [grid_data.1]; norm_num
  have hu1 : gridTime sInst vg Kg 0 j < 1 := (qn_gridTime_le hj.le).trans_lt (by norm_num)
  have hB := Sizes.STBctl_pos sz0 0 hu1
  have hη := etaT_pos (Einst_abs_lt 0) hu1
  have hW : (0 : ℝ) < ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast sz0.W_pos 0) _
  have : (0 : ℝ) < Γ4 0 * (Γ4 0 * Λ3 0) := by norm_num [Γ4, Λ3]
  positivity

/-! ### (6) `yMomentBounds_nzN` at `Y ≡ 0` (the merged `GridAssemblyNInst` bundle has `Y = 0`) -/

set_option linter.flexible false in
/-- `YMomentBoundsN` holds for `Y ≡ 0` and any nonnegative levels (the pattern of the `hY` field of
`GridAssemblyNInst.gridAsm_bundle`). -/
private theorem qn_yMoment_zero {d : ℕ} (sz : Sizes d) {n k : ℕ} (E : ℝ) (σ : Fin k → Bool)
    (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (K : ℕ) (v w : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j) :
    YMomentBoundsN sz E σ u τ K
      (fun (_ : ℕ) (_ : PathΩ sz) (_ : Fin k → Zd d (sz.L n)) => (0 : ℂ)) v w := by
  refine ⟨fun j => stronglyMeasurable_const, fun m _ b j _ => ?_⟩
  have h0 : ∀ ω, stoppedEdgeN sz E σ u (u m) τ
      (fun (_ : ℕ) (_ : PathΩ sz) (_ : Fin k → Zd d (sz.L n)) => (0 : ℂ)) b j ω = 0 := by
    intro ω
    simp [stoppedEdgeN, Ugen, UN]
  simp only [h0]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp
  all_goals first
    | exact Filter.Eventually.of_forall fun _ => rfl
    | exact Filter.Eventually.of_forall fun _ => le_rfl
    | exact Filter.Eventually.of_forall fun _ => hv j
    | exact hw j

/-- **Instance of `yMomentBounds_nzN`** at `sz0`, `n = 0`, `E = 1/2`, `σ = (+,-,+)`, the grid `(0, 1/32, 4)`, the
exit time `tau0`, every `A` (in particular `A = I_diff(σ)`), `Y ≡ 0` with the levels `v = w = 0` (this is the `Y` of the
merged bundle `GridAssemblyNInst.gridAsm_bundle`; the levels `4^{|A|+1} · 0`, `16^{|A|+1} · 0` of the conclusion
are `0` too). -/
theorem yMoment_zero_instance (A : Finset (Fin 3)) :
    YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) tau0 (Kg 0)
      (fun j ω => zeroModeSet 3 (sz0.L 0) A
        ((fun (_ : ℕ) (_ : PathΩ sz0) (_ : Fin 3 → Zd 3 (sz0.L 0)) => (0 : ℂ)) j ω))
      (fun _ => 4 ^ (A.card + 1) * 0) (fun _ => 16 ^ (A.card + 1) * 0) :=
  yMomentBounds_nzN sz0 (n := 0) (k := 3) (Einst 0) sig3 A (gridTime sInst vg Kg 0) tau0 (Kg 0)
    (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) (Einst_abs_lt 0).le (fun i _ => qn_gridTime_nonneg i)
    (fun i hi => (qn_gridTime_le hi).trans_lt (by norm_num))
    (qn_yMoment_zero sz0 _ _ _ _ _ (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl))

/-! ### (6b) `yMomentBounds_nzN` at a genuinely random `Y_j = ζ_j δ₀`

`ζ_j = √Δ · Re tr X_{j+1}` is the Gaussian increment of `GridAssemblyNInst` (`gridAsm_witZ`, a centred
Gaussian under `pathP`, independent of `filt j`): `Y_j = ζ_j δ₀` is `filt (j+1)`-measurable, not identically
zero, conditionally centred, in `L⁴`, with `E[ζ_j² | filt j] = E ζ_j²` (independent increments,
`condExp_indep_eq`), and the levels are `v = R² E ζ_j²`, `w = R⁴ E ζ_j⁴` with `R = (32/31)³ ≥ |(𝒰 δ₀)(b)|`
(`norm_UN_apply_le`).  `τ ≡ K = 4` (the stopping family never stops). -/

/-- The Gaussian increment `ζ_j` of `GridAssemblyNInst` at the size index `0`. -/
private abbrev qnZ (j : ℕ) : PathΩ sz0 → ℝ := fun ω => GridAssemblyNInst.gridAsm_witZ 0 j ω

/-- `ζ_j` as a function of the `(j+1)`-st draw. -/
private noncomputable def qnG : sz0.SeqΩ → ℝ := fun y =>
  Real.sqrt (gridStep sInst tInst GridAssemblyNInst.gridAsm_K 0) *
    linTr (sz := sz0) 0 (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      (Sizes.seqXmat sz0 0 y)

private theorem qnZ_eq (j : ℕ) : qnZ j = fun ω => qnG (ω (j + 1)) := rfl

private theorem qnG_meas : Measurable qnG :=
  (markov_measurable_linTr_seqXmat_sz0 1).const_mul _

private theorem qnG_memLp : MemLp qnG 4 (Sizes.seqP sz0) := by
  have h1 : MemLp (fun y : sz0.SeqΩ => linTr (sz := sz0) 0
      (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
      (Sizes.seqXmat sz0 0 y)) 4 (Sizes.seqP sz0) := by
    refine (memLp_map_measure_iff (g := id) aestronglyMeasurable_id
      (markov_measurable_linTr_seqXmat_sz0 1).aemeasurable).1 ?_
    rw [map_linTr_seqXmat]
    exact_mod_cast memLp_id_gaussianReal (4 : ℝ≥0)
  exact h1.const_mul _

private theorem qnZ_memLp (j : ℕ) : MemLp (qnZ j) 4 (pathP sz0) := by
  have h := qnG_memLp
  rw [← map_incr sz0 j] at h
  exact (memLp_map_measure_iff qnG_meas.aestronglyMeasurable
    (measurable_pi_apply (j + 1)).aemeasurable).1 h

private theorem qnZ_int4 (j : ℕ) : Integrable (fun ω => qnZ j ω ^ 4) (pathP sz0) := by
  have h : Integrable (fun ω => ‖qnZ j ω‖ ^ 4) (pathP sz0) :=
    (qnZ_memLp j).integrable_norm_pow' (p := 4)
  have h4 : ∀ ω, ‖qnZ j ω‖ ^ 4 = qnZ j ω ^ 4 := fun ω => by
    rw [Real.norm_eq_abs]; exact Even.pow_abs (by decide) _
  simpa only [h4] using h

private theorem qnG_integral : ∫ y, qnG y ∂(Sizes.seqP sz0) = 0 := by
  unfold qnG
  rw [integral_const_mul, integral_linTr_seqXmat, mul_zero]

private theorem qnZ_integral (j : ℕ) : ∫ ω, qnZ j ω ∂(pathP sz0) = 0 := by
  have h := integral_map (μ := pathP sz0) (φ := fun ω : PathΩ sz0 => ω (j + 1)) (f := qnG)
    (measurable_pi_apply (j + 1)).aemeasurable (by rw [map_incr]; exact qnG_meas.aestronglyMeasurable)
  rw [map_incr] at h
  rw [← qnG_integral]
  exact h.symm

/-- Independent increments: for a measurable `f`, `E[f(ζ_j) | filt j] = E f(ζ_j)` (`condExp_indep_eq`,
`indep_incr`). -/
private theorem qnZ_condExp (j : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    (pathP sz0)[fun ω => f (qnZ j ω) | filt sz0 j] =ᵐ[pathP sz0]
      fun _ => ∫ ω, f (qnZ j ω) ∂(pathP sz0) := by
  have hle₁ : MeasurableSpace.comap (fun ω : PathΩ sz0 => ω (j + 1)) inferInstance ≤
      (inferInstance : MeasurableSpace (PathΩ sz0)) := (measurable_pi_apply (j + 1)).comap_le
  have hmeas : StronglyMeasurable[MeasurableSpace.comap (fun ω : PathΩ sz0 => ω (j + 1))
      inferInstance] (fun ω => f (qnZ j ω)) :=
    ((hf.comp qnG_meas).comp (comap_measurable (fun ω : PathΩ sz0 => ω (j + 1)))).stronglyMeasurable
  exact condExp_indep_eq hle₁ ((filt sz0).le j) hmeas (indep_incr sz0 j)

/-- The point mass `δ₀` on `(Z_{L_0}^3)^3` at the size index `0` of `sz0` (`L_0 = 4`). -/
private def qnδ : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ := fun b => if b = 0 then 1 else 0

/-- The random tensor `Y_j = ζ_j δ₀`. -/
private noncomputable def qnY (j : ℕ) (ω : PathΩ sz0) : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ :=
  fun b => ((qnZ j ω : ℝ) : ℂ) * qnδ b

private theorem qnY_meas (j : ℕ) : StronglyMeasurable[filt sz0 (j + 1)] (qnY j) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz0 (j + 1)) _ _ fun b =>
    (Complex.measurable_ofReal.comp (GridAssemblyNInst.gridAsm_measurable_witZ 0 j)).mul_const _

/-- `𝒰 (c · X) = c · 𝒰 X` for a scalar `c`. -/
private theorem qn_Ugen_smul (d L : ℕ) [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (c : ℂ) (X : (Fin k → Zd d L) → ℂ) (b : Fin k → Zd d L) :
    Ugen d L g E σ v w (fun b' => c * X b') b = c * Ugen d L g E σ v w X b := by
  unfold Ugen UN
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ => by ring

/-- **Instance of `yMomentBounds_nzN` with a random `Y`**: at `sz0`, `E = 1/2`, `σ = (+,-,+)`, the grid
`(0, 1/32, 4)`, `τ ≡ 4`, `A = I_diff(σ)`, `Y_j = ζ_j δ₀` (a nonzero Gaussian multiple of the point mass,
conditionally centred, in `L⁴`): `YMomentBoundsN` holds for `Y` with the levels `v_j = R² E ζ_j²`,
`w_j = R⁴ E ζ_j⁴` (`R = (32/31)³`), and the theorem gives it for `Q^{(A)} Y` with the levels
`4^{|A|+1} v_j`, `16^{|A|+1} w_j`; `Y_0` and `Q^{(A)} Y_0` are nonzero at some sample. -/
theorem yMoment_random_instance :
    ∃ v w : ℕ → ℝ, (∀ j, 0 ≤ v j) ∧ (∀ j, 0 ≤ w j) ∧
      YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0) qnY v w ∧
      YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0)
        (fun j ω => zeroModeSet 3 (sz0.L 0) (STIdiff sig3) (qnY j ω))
        (fun j => 4 ^ ((STIdiff sig3).card + 1) * v j)
        (fun j => 16 ^ ((STIdiff sig3).card + 1) * w j) ∧
      (∃ ω, qnY 0 ω ≠ 0) ∧ (∃ ω, zeroModeSet 3 (sz0.L 0) (STIdiff sig3) (qnY 0 ω) ≠ 0) := by
  set R : ℝ := (32 / 31) ^ 3 with hR
  have hV : ∀ j, 0 ≤ R ^ 2 * ∫ ω, qnZ j ω ^ 2 ∂(pathP sz0) := fun j =>
    mul_nonneg (sq_nonneg _) (integral_nonneg fun ω => sq_nonneg _)
  have hW : ∀ j, 0 ≤ R ^ 4 * ∫ ω, qnZ j ω ^ 4 ∂(pathP sz0) := fun j =>
    mul_nonneg (by positivity) (integral_nonneg fun ω => by positivity)
  have hY : YMomentBoundsN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0) qnY
      (fun j => R ^ 2 * ∫ ω, qnZ j ω ^ 2 ∂(pathP sz0))
      (fun j => R ^ 4 * ∫ ω, qnZ j ω ^ 4 ∂(pathP sz0)) := by
    refine ⟨qnY_meas, fun m hm b j hj => ?_⟩
    have hjK : j < Kg 0 := hj.trans_le hm
    set ρ : ℂ := Ugen 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 (gridTime sInst vg Kg 0 (j + 1))
      (gridTime sInst vg Kg 0 m) qnδ b with hρ
    have hρn : ‖ρ‖ ≤ R := by
      have h1 := norm_UN_apply_le (sz0.three_le_L 0) (m := fun i => mSigma (Einst 0) (sig3 i))
        (fun i => norm_mSigma (Einst_abs_lt 0).le (sig3 i)) (g := sz0.lam 0)
        (qn_gridTime_nonneg (j + 1))
        (ST_gridTime_mono sInst vg Kg 0 (sInst_le_vg 0) (show j + 1 ≤ m by omega))
        ((qn_gridTime_le hm).trans_lt (by norm_num)) qnδ b
      have hδ : ‖qnδ‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
        unfold qnδ; split_ifs <;> simp
      have hratio : (1 - gridTime sInst vg Kg 0 (j + 1)) / (1 - gridTime sInst vg Kg 0 m) ≤ 32 / 31 := by
        have h1 := qn_gridTime_le hm
        have := qn_gridTime_nonneg (j + 1)
        rw [div_le_iff₀ (by linarith)]
        linarith
      have hr0 : 0 ≤ (1 - gridTime sInst vg Kg 0 (j + 1)) / (1 - gridTime sInst vg Kg 0 m) :=
        div_nonneg (by linarith [(qn_gridTime_le (show j + 1 ≤ Kg 0 by omega))])
          (by linarith [(qn_gridTime_le hm)])
      refine h1.trans ?_
      calc ((1 - gridTime sInst vg Kg 0 (j + 1)) / (1 - gridTime sInst vg Kg 0 m)) ^ 3 * ‖qnδ‖
          ≤ (32 / 31) ^ 3 * 1 := mul_le_mul (pow_le_pow_left₀ hr0 hratio 3) hδ (norm_nonneg _)
            (by positivity)
        _ = R := by rw [hR, mul_one]
    have hind : ∀ ω, stoppedEdgeN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
        (gridTime sInst vg Kg 0 m) (fun _ => Kg 0) qnY b j ω = ((qnZ j ω : ℝ) : ℂ) * ρ := by
      intro ω
      have hmem : ω ∈ {ω' : PathΩ sz0 | j < (fun _ : PathΩ sz0 => Kg 0) ω'} := hjK
      unfold stoppedEdgeN
      rw [Set.indicator_of_mem hmem]
      exact qn_Ugen_smul 3 (sz0.L 0) (sz0.lam 0) (Einst 0) sig3 _ _ _ qnδ b
    have hre : ∀ ω, (stoppedEdgeN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
        (gridTime sInst vg Kg 0 m) (fun _ => Kg 0) qnY b j ω).re = ρ.re * qnZ j ω := by
      intro ω; rw [hind ω, Complex.re_ofReal_mul]; ring
    have him : ∀ ω, (stoppedEdgeN sz0 (Einst 0) sig3 (gridTime sInst vg Kg 0)
        (gridTime sInst vg Kg 0 m) (fun _ => Kg 0) qnY b j ω).im = ρ.im * qnZ j ω := by
      intro ω; rw [hind ω, Complex.im_ofReal_mul]; ring
    have hZ0 : (pathP sz0)[qnZ j | filt sz0 j] =ᵐ[pathP sz0] 0 := by
      filter_upwards [qnZ_condExp j (fun x => x) measurable_id] with ω hω
      simpa [qnZ_integral j] using hω
    have hZ2 := qnZ_condExp j (fun x => x ^ 2) (by fun_prop)
    have hZm := (qnZ_memLp j).aestronglyMeasurable
    obtain ⟨a0, a4, a2, aI⟩ := qtNZ_scalar (m := filt sz0 j) (μ := pathP sz0) (qnZ j) ρ.re R
      ((Complex.abs_re_le_norm ρ).trans hρn) (integral_nonneg fun ω => sq_nonneg _)
      (integral_nonneg fun ω => by positivity) hZm hZ0 (qnZ_int4 j) (hZ2.le) le_rfl
    obtain ⟨b0, b4, b2, bI⟩ := qtNZ_scalar (m := filt sz0 j) (μ := pathP sz0) (qnZ j) ρ.im R
      ((Complex.abs_im_le_norm ρ).trans hρn) (integral_nonneg fun ω => sq_nonneg _)
      (integral_nonneg fun ω => by positivity) hZm hZ0 (qnZ_int4 j) (hZ2.le) le_rfl
    simp only [hre, him]
    exact ⟨a0, b0, a4, b4, a2, b2, aI, bI⟩
  refine ⟨fun j => R ^ 2 * ∫ ω, qnZ j ω ^ 2 ∂(pathP sz0),
    fun j => R ^ 4 * ∫ ω, qnZ j ω ^ 4 ∂(pathP sz0), hV, hW, hY, ?_, ?_, ?_⟩
  · exact yMomentBounds_nzN sz0 (n := 0) (k := 3) (Einst 0) sig3 (STIdiff sig3)
      (gridTime sInst vg Kg 0) (fun _ => Kg 0) (Kg 0) qnY _ _ (Einst_abs_lt 0).le
      (fun i _ => qn_gridTime_nonneg i) (fun i hi => (qn_gridTime_le hi).trans_lt (by norm_num)) hY
  · obtain ⟨ω, hω⟩ := GridAssemblyNInst.gridAsm_witZ_ne_zero 0 0
    refine ⟨ω, fun h => hω ?_⟩
    have h0 := congrFun h 0
    have h1 : qnδ (0 : Fin 3 → Zd 3 (sz0.L 0)) = 1 := by simp [qnδ]
    simp only [qnY, h1, mul_one, Pi.zero_apply] at h0
    exact_mod_cast h0
  · obtain ⟨ω, hω⟩ := GridAssemblyNInst.gridAsm_witZ_ne_zero 0 0
    refine ⟨ω, fun h => hω ?_⟩
    have h0 := congrFun h 0
    have e : qnY 0 ω = (((qnZ 0 ω : ℝ) : ℂ)) • qnδ := rfl
    have hQ : zeroModeSet 3 (sz0.L 0) (STIdiff sig3) qnδ 0 =
        (((1 - (((sz0.L 0 : ℕ) : ℝ) ^ 3)⁻¹) ^ 2 : ℝ) : ℂ) := qn_Q_delta_zero' (sz0.L 0)
    have hL4 : ((sz0.L 0 : ℕ) : ℝ) = 4 := by rw [sz0_values.1]; norm_num
    rw [e, zeroModeSet_smul] at h0
    simp only [Pi.smul_apply, hQ, hL4, Pi.zero_apply, smul_eq_mul] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_right (by norm_num)
    exact_mod_cast h1

/-! ### (7) `budgetNZN` at the data of `NQLinInst.budgetNonAltLinN_instance` -/

private theorem qn_W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num

private theorem qn_N0 : ((sz0.size 0 : ℕ) : ℝ) = 2097152 := by rw [sz0_values.2.2.1]; norm_num

private theorem qn_two_pow_rpow (m : ℕ) (y : ℝ) : ((2 : ℝ) ^ m) ^ y = (2 : ℝ) ^ ((m : ℝ) * y) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

private theorem qn_N_rpow (y : ℝ) : ((sz0.size 0 : ℕ) : ℝ) ^ y = (2 : ℝ) ^ ((21 : ℝ) * y) := by
  have h := qn_two_pow_rpow 21 y
  rw [qn_N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, h]
  norm_num

/-- `N^{2/21} = 4` (`N = 2^21`), so `Γ = N^{ε₁} = 4`. -/
private theorem qn_N_eps1 : ((sz0.size 0 : ℕ) : ℝ) ^ ((2 : ℝ) / 21) = 4 := by
  rw [qn_N_rpow, show (21 : ℝ) * (2 / 21) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem qn_N_nine : ((sz0.size 0 : ℕ) : ℝ) ^ (9 : ℝ) = 2097152 ^ 9 := by
  rw [show (9 : ℝ) = ((9 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, qn_N0]

private theorem qn_im_ge : (24 / 25 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (48 / 25 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  linarith

/-- `Ls = Im m(1/2)⁻¹ · log N ≤ 22` (`log N = 21 log 2 < 14.56`, `Im m(1/2) ≥ 24/25`). -/
private theorem qn_Ls_le :
    (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) ≤ 22 := by
  have e : Einst 0 = 1 / 2 := rfl
  rw [e, qn_N0, show (2097152 : ℝ) = 2 ^ 21 by norm_num, Real.log_pow]
  have hpos : 0 < (mE (1 / 2)).im := lt_of_lt_of_le (by norm_num) qn_im_ge
  have h2 : (mE (1 / 2)).im⁻¹ ≤ 25 / 24 := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]; linarith [qn_im_ge]
  have l2 := Real.log_two_lt_d9
  have h3 : (0 : ℝ) ≤ ((21 : ℕ) : ℝ) * Real.log 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  push_cast at h3 ⊢
  nlinarith [inv_nonneg.2 hpos.le]

private theorem qn_Ls_nonneg :
    0 ≤ (mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ) := by
  have hN1 : (1 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := by rw [qn_N0]; norm_num
  exact mul_nonneg (inv_nonneg.2 (mE_im_pos (Einst_abs_lt 0)).le) (Real.log_nonneg hN1)

/-- **Instance of `budgetNZN`** at the data of `NQLinInst.budgetNonAltLinN_instance` (`d = 3`, `sz0`, `n = 0`:
`L = 4`, `W = 32`, `N = 2^21`; `E = 1/2`, grid `(sInst, vg, Kg)`: `Δ = 1/128`, `u_j = j/128`; `k = 3`; levels
`(Γ, Λ, Φ₁, Φ₂, Φ₃) = (4, 3, 1, 12, 1)` with `Γ = N^{2/21}`); the constants `C = 5`, `cA = 4 = 2^{|I_diff(σ)|}`,
`D'' = 5`, `D_Y = 1`, `D_t = -5`, `τ_K = 1/21`, `ε_q = 1`, `ε₀ = 9`, `ε₁ = 2/21`, `X0 = 4 B_0^3`: every
hypothesis is discharged (`hlog`, `hR` are the merged `NQBudgetInst.hlog_instance`, `hR_instance`; the six
absorption inequalities are numerical at `N = 2^21`).  Nothing is left open. -/
theorem budgetNZN_instance :
    assembledRHSNZN sz0 Einst sInst vg Kg 0 3 5 4 Γ4 Λ3 Φ1 (fun _ => 12) Φ1 5 1 (1 / 21) 1
        (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (9 : ℝ) *
        (Λ3 0 ^ ((1 : ℝ) / 2) + Φ1 0 + (fun _ : ℕ => (12 : ℝ)) 0 + Φ1 0) * (sz0.Bctl 0 (vg 0)) ^ 3 := by
  have hLs := qn_Ls_le
  have hLs0 := qn_Ls_nonneg
  refine budgetNZN sz0 Einst sInst vg Kg 0 3 5 4 Γ4 Λ3 Φ1 (fun _ => 12) Φ1 5 1 (-5) (1 / 21) 1 9
    (2 / 21) (4 * (sz0.Bctl 0 (sInst 0)) ^ 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Einst_abs_lt 0) (by norm_num [sInst]) (by norm_num [sInst, vg]) (by norm_num [vg])
    (by norm_num [Kg]) (by rw [qn_N_eps1]) (by norm_num [Λ3]) (by norm_num [Φ1]) (by norm_num)
    (by norm_num [Φ1]) NQBudgetInst.hlog_instance (by rw [qn_N_eps1]) NQBudgetInst.hR_instance
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- H1
    rw [qn_N_eps1, qn_N_nine]; norm_num
  · -- H2
    rw [qn_N_eps1, qn_N_nine]
    nlinarith
  · -- H3
    have hs : Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ * Real.log ((sz0.size 0 : ℕ) : ℝ))) ≤ 9 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by push_cast; nlinarith⟩
    generalize Real.sqrt (((3 : ℕ) : ℝ) * ((mE (Einst 0)).im⁻¹ *
      Real.log ((sz0.size 0 : ℕ) : ℝ))) = S at hs ⊢
    rw [qn_N_eps1, qn_N_nine, Real.rpow_one, qn_N0]
    nlinarith
  · -- H4
    have hW : ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) ≤ 1 := by
      rw [qn_W0, Real.rpow_neg (by norm_num), show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
      norm_num
    have hW0 : (0 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hs : Real.sqrt (((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by push_cast; nlinarith⟩
    generalize Real.sqrt (((3 : ℕ) : ℝ) * ((sz0.W 0 : ℕ) : ℝ) ^ (-(5 : ℝ))) = S at hs ⊢
    rw [qn_N_nine, Real.rpow_one, qn_N0]
    nlinarith
  · -- H5
    rw [qn_N_nine, Real.rpow_neg_one, qn_N0]; norm_num
  · -- H6
    rw [qn_N_nine, neg_neg, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, qn_N0]
    norm_num

end QtNonzeroInst

end RBM.Ind

end

#print axioms RBM.zeroModeSet_idem
#print axioms RBM.Ind.cQVNZN
#print axioms RBM.Ind.assembledRHSNZN
#print axioms RBM.Ind.nzUgen_holds
#print axioms RBM.Ind.nz_hker
#print axioms RBM.Ind.nz_hdriftN
#print axioms RBM.Ind.subGaussStop_nzN
#print axioms RBM.Ind.yMomentBounds_nzN
#print axioms RBM.Ind.budgetNZN
#print axioms RBM.Ind.QtNonzeroInst.idem_instance
#print axioms RBM.Ind.QtNonzeroInst.nzUgen_instance
#print axioms RBM.Ind.QtNonzeroInst.nz_hker_instance
#print axioms RBM.Ind.QtNonzeroInst.nz_hdrift_instance
#print axioms RBM.Ind.QtNonzeroInst.nz_hdrift_level_pos
#print axioms RBM.Ind.QtNonzeroInst.subGaussStop_nz_instance
#print axioms RBM.Ind.QtNonzeroInst.cQVNZN_inst_pos
#print axioms RBM.Ind.QtNonzeroInst.yMoment_zero_instance
#print axioms RBM.Ind.QtNonzeroInst.yMoment_random_instance
#print axioms RBM.Ind.QtNonzeroInst.budgetNZN_instance
