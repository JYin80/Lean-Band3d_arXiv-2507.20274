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

Case (ii), `1 − s ≤ ilambda²/L²`.  Paper: Definition 4.12 (`def;zero_mode_remove`), (4.43) `normQA2`,
Lemma 4.13 (`lem: newPQ`), the commutation (4.46) `eq_L-Keee_nonzeromode`, (4.47) `iisuwjyys`,
Lemma 4.14 (`lem:STOeq_Qt_nonzero`), Lemma 4.17 (`lem:sum_decay_nonzero`) and its proof (Subsection 4.5
and Appendix A).  No RBM1D/RBM2D source: the zero-mode regime does not exist for `d ≤ 2`.

## What is here

* §1 (`RBM`) `zeroModeSet_idem` : `Q^{(A)} ∘ Q^{(A)} = Q^{(A)}`; the real kernel `qtNZ_q` of
  `Q^{(A)}` and its row sum `≤ 2^{|A|}`; the `∞→∞` duality `qtNZ_sum_norm_le_of_bound`.
* §2 (`RBM.Ind`) the vocabulary `cQVNZN`, `assembledRHSNZN`.
* §3 `nzUgen_holds`: Lemma 4.17 `lem:sum_decay_nonzero` for the grid kernel `Ugen`, loss-free, as an
  operator bound and as a row-sum bound with one constant.
* §4 `nz_hker`, §5 `nz_hdriftN`: the fields `hker`, `hdrift` of `GridAssemblyHypN` for the class
  "fixed points of `Q^{(A)}`".
* §6 `subGaussStop_nzN`: the Azuma input `SubGaussStopN` for `Q^{(A)} Z_j`.
* §7 `yMomentBounds_nzN`: the `Y`-moment inputs `YMomentBoundsN` pass to `Q^{(A)} Y`.
* §8 `budgetNZN`: the budget `assembledRHSNZN ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.

Every helper that is not part of the statements is `private` or carries the prefix `qtNZ_`.
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

/-- **`Q^{(A)} ∘ Q^{(A)} = Q^{(A)}`**: `Q^{(i)}` is the projection `I - P^{(i)}`
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

/-- **The row sum of the real kernel of `Q^{(A)}` is at most `2^{|A|}`** ((4.43) `normQA2`
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

/-! ## 2. The vocabulary -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-- The sub-Gaussian proxy of the `j`-th propagated zero-mode-removed increment (case (ii)):
`Δ · k · C² · (Γ(ΓΛ) B_{u_j}^{2k}/η_{u_j} + W^{-D''})` (`C` = row-sum bound of `Q^{(A)}∘𝒰`;
no ratio factor, no far part: the analogue of `cQVNonAltN`). -/
def cQVNZN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C Γ Λ D'' : ℝ) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * C ^ 2 *
    (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / etaT (E n) (gridTime s v K n j)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D'')))).toNNReal

/-- The right side of `AssembledN` at `m = K n` for the zero-mode-removed
evolution: kernel weight `κ ≡ C`, `εK ≡ 0`, drift level `cA · dDriftLinN`, proxy `cQVNZN`,
step error `cA · stepErrN` (`cA = 2^{|A|}`); the analogue of `assembledRHSLinN`. -/
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

/-! ## 3. Lemma 4.17 `lem:sum_decay_nonzero` for the grid kernel `Ugen` -/

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

/-- **`RBM.Ind.nzUgen_holds`**: Lemma 4.17 `lem:sum_decay_nonzero` for the grid kernel `Ugen`,
loss-free, as an operator bound and as a row-sum bound with one constant.  The
`ekSumDecayNonzero_holds` (deterministic, no decay class, no sum-zero) at `m = mE E`
(`norm_mE`, `|E| < 2`), `Ugen = UN … (EKsgn (mE E) σ)`; the row-sum form is
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

/-! ## 4. The field `hker` for the class "fixed points of `Q^{(A)}`" -/

/-- **`RBM.Ind.nz_hker`**: the `hker` field of `GridAssemblyHypN` for
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

/-! ## 5. The drift of the zero-mode-removed hierarchy on `GoodLinN` -/

/-- **`RBM.Ind.nz_hdriftN`**: the drift of the zero-mode-removed hierarchy on `GoodLinN`
(`Q^{(A)}` of `driftTensorN`): `‖(Q^{(A)} Dr)(b)‖ ≤ 2^{|A|} ‖Dr‖ ≤ 2^{|A|} · dDriftLinN`
(`norm_zeroModeSet_le` = (4.43) `normQA2`, `nqLin_hdriftN`; the sup over `b` by `pi_norm_le_iff_of_nonneg`). -/
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

/-! ## 6. The Azuma input for `Q^{(A)} Z_j` -/

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

/-- **`RBM.Ind.subGaussStop_nzN`**: the Azuma input (`SubGaussStopN`) for the
zero-mode-removed first-chaos part `Q^{(A)} Z_j`, proxy `cQVNZN`, on any stopping family that stays in
`GoodSetN` (its `STeeM` clause only), from a row-sum bound `≤ C` of `Q^{(A)}∘𝒰_{u_{j+1},u_m}`.
`𝒰(Q^{(A)} Z_j)(a) = Q^{(A)} 𝒰(Z_j)(a) = Σ_b κ_b Z_j(b)` (commutation `zeroModeSet_Ugen`, the row
`κ`); `azumaSubGN` with `Φ = loopFamN …` and the weights `κ` (as `azumaProxy_subG_ugen`); `qvPropagatedN` at these weights; `Re Σ κ κ̄' ee ≤ C² max‖ee(u_{j+1})‖` and
the `STeeM` clause of `GoodSetN` at `u_j` plus the shift `eeShiftErrN` (the hypothesis `hδ`). -/
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

/-! ## 7. The `Y`-moment inputs pass to `Q^{(A)} Y` -/

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

/-- **`RBM.Ind.yMomentBounds_nzN`**: the `Y`-moment inputs (`YMomentBoundsN`) pass to `Q^{(A)} Y` with the levels `4^{|A|+1} v`, `16^{|A|+1} w`.
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

/-! ## 8. The budget of the case-(ii) grid endpoint -/

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

/-- **`RBM.Ind.budgetNZN`**: the budget of the case-(ii) grid endpoint at the linear levels
(the analogue of `budgetNonAltLinN`; no ratio weights, no far parts):
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
    -- the initial term
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
    -- the drift term
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
    -- the quadratic-variation term
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
    -- the last two terms
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

end RBM.Ind

end
