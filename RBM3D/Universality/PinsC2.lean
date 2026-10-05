/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Step1Good
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# `RBM3D.Universality.PinsC2` (UN-12b): the C″ re-pin of the C form, the C-form Step 1

Ticket T2213 (DECISIONS §69; supervisor verdict `docs/supervisor/2026-10-05-1955.md` part B, findings
T2208a, T2208b).  **No merged signature is changed** (CLAUDE.md §5.3): the successors live here.

*The findings.*  (T2208a) The merged `UNStep1GoodC'` (`PinsDens.lean:116`) is false: its hypotheses
`UNTrLocalInit` (a statement about `sN(ouInit)`) and `UNNormBound` (a statement about `H`) never observe the
deterministic mean `μ` of the centred model, but its conclusion reads all eigenvalues of
`ouInit = a H + (1 - a) μ` (condition (2.3)); a change of `μ` by `R_n` in one eigenvalue moves `sN` only by
`≤ 2/(N Im z)`, below the tolerance.  `not_UNStep1GoodC'_of_diag` makes this a compiled fact on any diagonal model
meeting the hypotheses.  (T2208b) The merged `UNTrLocalInit` (`PinsK.lean:259`) is false for the band model: the
spectrum of `ouInit = e^{-t*/2} H` is dilated by `1 - e^{-t*/2} ≈ t*/2` against a `τ_s`-independent `m`, and
`m(z) - a⁻¹ m(a⁻¹ z) ≈ 0.17 t*` at `z = i` exceeds the tolerance `W^τ Bctl` for `τ_s > 1/6` (argued, not
compiled).

*The repair (supervisor 1955 B2).*  `UNTrLocalInit'` has the tolerance `W^τ (Bctl + t*)`; the structural
`UNMeanBound` bounds the mean; `UNStep1GoodC''` and `UNCoreC''` are the C-form pins over them.

*Registry reclassification (DECISIONS §66 (2), §69; the merged docstrings still say "owed" and are not
edited).*  `UNTrLocalInit` (a predicate false for the band model), `UNStep1GoodC'` (false:
`not_UNStep1GoodC'_of_diag`) and `UNCoreC'` (superseded: its hypothesis `UNTrLocalInit` fails for the band model)
move to the class `refutedProps`.  Consequently the merged instances `UNKInst.inst_coreC_band` (`PinsK.lean:673`)
and `UNDensInst.inst_coreC_band'` (`PinsDens.lean:630`) are vacuous (they assume `UNTrLocalInit` of the band
model, which is false); `PinsC2Inst.inst_coreC_band''` replaces them.  `UNTrLocalInit'` and `UNCoreC''` are
owed; `UNMeanBound` is structural; `UNStep1GoodC''` is proved here (`step1GoodC''`) and not registered.

Sections: 1 the pins; 2 elementary helpers (private); 3 matrix facts and the C-form dictionary; 4 monotonicity
and the mean bound; 5 the band instance of `UNTrLocalInit'` (the scaling argument); 6 the conditional
refutation; 7 the C-form Step 1; 8 compiled nonempty instances (`PinsC2Inst`).

Ported (private helpers, prefix `PinsC2_`): `Step1Good_inv_mul_re`, `_inv_mul_im`, `_exp_le_one`,
`_one_le_inv`, `_inv_le`, `_one_sub_exp_le`, `_half_le_one_sub_exp`, `_one_sub_exp_pos`, `_sqrt_exp`,
`_rpow_ev`, `_W_le_size`, `_W_tendsto`, `_bctl`, and the proofs of `_strip`, `_regular`, `_rate`, `_at_n`,
`step1Good'_det`, `step1Good'` of `Universality/Step1Good.lean` (T2208, a42cad0) with the C-form changes;
`PinsDens_one_le_Nsz` (`PinsDens.lean:293`); `STBctl_mono` (`Induction/ScaleFacts.lean:74`, copied, not imported).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal ComplexOrder

namespace RBM.Univ

/-! ## 1. The pins -/

section Init

variable {d : ℕ}

/-- **Pin `UNTrLocalInit'` (owed; band: `unTrLocalInit'_band_zero`; BA: the BA row of BA-C1b)**: the merged
`UNTrLocalInit` (`PinsK.lean:259`, refuted for the band model, finding T2208b) with the tolerance
`W^τ (Bctl n (1 - Im z) + t*)`, `t* = ouTStar sz τs n` (supervisor 1955 B2): the spectrum of `ouInit` is shifted by
`O(t*)` against a `τ_s`-independent `m`.  Registry class: **owed**. -/
def UNTrLocalInit' (sz : Sizes d) (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
  ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
    M.μ {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1 ∧
        ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) <
          ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
      ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNMeanBound` (structural)**: the deterministic mean of a centred model has all eigenvalues `≤ N^{CV₀}` in
modulus, eventually (supervisor 1955 B2; finding T2208a: `UNStep1GoodC'` never observes the mean).  Band: mean `0`
(`unMeanBound_toC`); BA: `‖λΨ‖ ≤ 2d 𝔡⁻¹ ≤ N^{CV₀}` eventually for `CV₀ > 0`.  Registry class: **structural**. -/
def UNMeanBound (sz : Sizes d) (M : UNModelC sz) (CV₀ : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ i, |(M.mean_herm n).eigenvalues i| ≤ Nsz sz n ^ CV₀

end Init

/-- **`UNStep1GoodC''`** (proved here by `step1GoodC''`; not registered): `UNStep1GoodC'` (`PinsDens.lean:116`,
refuted on diagonal models by `not_UNStep1GoodC'_of_diag`, false in general: supervisor 1955 B1) with `UNTrLocalInit ↦ UNTrLocalInit'` and
`UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`. -/
def UNStep1GoodC'' : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
      UNDens' m E ρ δ → UNTrLocalInit' sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M.toUNModel CV₀ → UNMeanBound sz M CV₀ →
      ∀ τs D : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → 0 < D →
        ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
          M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ≤
            ENNReal.ofReal (Nsz sz n ^ (-D))

/-- **`UNCoreC''` (owed, BA-C1b `baBUniv_of_rows`)**: `UNCoreC'` (`PinsDens.lean:131`, superseded: its hypothesis
`UNTrLocalInit` fails for the band model, supervisor 1955 B1) with `UNTrLocalInit ↦ UNTrLocalInit'` and
`UNMeanBound sz M CV₀` beside `UNNormBound sz M.toUNModel CV₀`.  Registry class: **owed**. -/
def UNCoreC'' : Prop :=
  UNL32 → UNGUELocal → UNGreenCorrAllC →
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → UNTrLocal sz M.toUNModel m E δ → UNTrLocalInit' sz M m E δ →
          (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M.toUNModel CV₀ ∧ UNMeanBound sz M CV₀) → UNClaimAllC sz M E →
          ∀ E' : ℝ, |E'| < 2 → ∀ k : ℕ, 1 ≤ k → ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            UNUnivDilAt sz M.toUNModel ρ E E' k O

/-! ## 2. Elementary helpers (private; copies, see the module docstring) -/

private theorem PinsC2_one_le_Nsz {d : ℕ} (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  have h1 : 1 ≤ sz.size n := by
    simp only [Sizes.size]
    have := sz.three_le_L n
    have := sz.W_pos n
    exact Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by omega))
  exact_mod_cast h1

private theorem PinsC2_inv_mul_re (a : ℝ) (X : ℂ) : (((a : ℝ) : ℂ)⁻¹ * X).re = a⁻¹ * X.re := by
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul]

private theorem PinsC2_inv_mul_im (a : ℝ) (X : ℂ) : (((a : ℝ) : ℂ)⁻¹ * X).im = a⁻¹ * X.im := by
  rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]

private theorem PinsC2_exp_le_one {T : ℝ} (hT : 0 ≤ T) : Real.exp (-T / 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; linarith

private theorem PinsC2_one_le_inv {T : ℝ} (hT : 0 ≤ T) : 1 ≤ (Real.exp (-T / 2))⁻¹ := by
  rw [one_le_inv₀ (Real.exp_pos _)]
  exact PinsC2_exp_le_one hT

/-- `(e^{-T/2})⁻¹ ≤ 1 + T` for `0 ≤ T ≤ 1`. -/
private theorem PinsC2_inv_le {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    (Real.exp (-T / 2))⁻¹ ≤ 1 + T := by
  have h := Real.add_one_le_exp (-T / 2)
  have h1 : (0 : ℝ) < -T / 2 + 1 := by linarith
  refine (inv_anti₀ h1 h).trans ?_
  rw [inv_le_iff_one_le_mul₀ h1]
  nlinarith

/-- `1 - e^{-T} ≤ T`. -/
private theorem PinsC2_one_sub_exp_le (T : ℝ) : 1 - Real.exp (-T) ≤ T := by
  have := Real.add_one_le_exp (-T); linarith

/-- `T / 2 ≤ 1 - e^{-T}` for `0 ≤ T ≤ 1`. -/
private theorem PinsC2_half_le_one_sub_exp {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1) :
    T / 2 ≤ 1 - Real.exp (-T) := by
  have h := Real.add_one_le_exp T
  have h1 : (0 : ℝ) < T + 1 := by linarith
  have h2 : Real.exp (-T) ≤ (T + 1)⁻¹ := by
    rw [Real.exp_neg]; exact inv_anti₀ h1 h
  have h3 : (T + 1)⁻¹ ≤ 1 - T / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1]; nlinarith
  linarith

/-- `x / 4 ≤ 1 - e^{-x/2}` for `0 ≤ x ≤ 1`. -/
private theorem PinsC2_quarter_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 4 ≤ 1 - Real.exp (-x / 2) := by
  have h := PinsC2_half_le_one_sub_exp (T := x / 2) (by linarith) (by linarith)
  have e : -(x / 2) = -x / 2 := by ring
  rw [e] at h
  linarith

private theorem PinsC2_one_sub_exp_pos {T : ℝ} (hT : 0 < T) : 0 < 1 - Real.exp (-T) := by
  have : Real.exp (-T) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  linarith

private theorem PinsC2_sqrt_exp (T : ℝ) : Real.sqrt (Real.exp (-T)) = Real.exp (-T / 2) :=
  (Real.exp_half (-T)).symm

private theorem PinsC2_rpow_ev {e c : ℝ} (he : e < 0) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ e ≤ c := by
  have h := (tendsto_rpow_neg_atTop (y := -e) (by linarith)).eventually (ge_mem_nhds hc)
  simpa using h

/-- `W ≤ N`: `W ≤ W L ≤ (W L)^d` for `d ≥ 1`. -/
private theorem PinsC2_W_le_size {d : ℕ} (sz : Sizes d) (hd : 0 < d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ Nsz sz n := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd.ne' _
  exact_mod_cast h1.trans h2

/-- `W → ∞` along an admissible sequence (`W ≥ N^𝔠` and `N → ∞`). -/
private theorem PinsC2_W_tendsto {d : ℕ} {sz : Sizes d} {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hN, hB, -⟩ := hA
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  exact tendsto_atTop_mono' atTop hB h1

/-- `Bctl (1 - η') ≤ Bctl (1 - η)` for `0 < η ≤ η'` (copy of `STBctl_mono`, `Induction/ScaleFacts.lean:74`). -/
private theorem PinsC2_Bctl_anti {d : ℕ} (sz : Sizes d) (n : ℕ) {η η' : ℝ} (hη : 0 < η) (hηη' : η ≤ η') :
    sz.Bctl n (1 - η') ≤ sz.Bctl n (1 - η) := by
  have hsu : 1 - η' ≤ 1 - η := by linarith
  have hu : 1 - η < 1 := by linarith
  unfold Sizes.Bctl Bparam
  have hxu : 0 < 1 - (1 - η) := by linarith
  have hxs : 0 < 1 - (1 - η') := by linarith
  rw [abs_of_pos hxu, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (sz.lam n ^ 2 + (1 - (1 - η')))⁻¹ ≤ (sz.lam n ^ 2 + (1 - (1 - η)))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η')))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η)))⁻¹ :=
    inv_anti₀ (by positivity) (by gcongr)
  have hK : 0 ≤ ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  gcongr

/-- `Bctl (1 - η) ≥ (N η)⁻¹` for `η > 0`: the second summand of `Bparam`. -/
private theorem PinsC2_Bctl_ge {d : ℕ} (sz : Sizes d) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    (Nsz sz n * η)⁻¹ ≤ sz.Bctl n (1 - η) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Nsz Sizes.size
    push_cast; rw [mul_pow]
  have habs : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold Sizes.Bctl Bparam
  rw [habs]
  have e1 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [e1, inv_one, mul_one, mul_add]
  have t1 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + η)⁻¹ := by
    have : 0 < sz.lam n ^ 2 + η := by positivity
    positivity
  have t2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ = (Nsz sz n * η)⁻¹ := by
    rw [hN, ← mul_inv, mul_assoc]
  rw [t2]
  linarith

/-- `Bctl (1 - η) ≥ 0` for `η > 0`. -/
private theorem PinsC2_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    0 ≤ sz.Bctl n (1 - η) := by
  have hN0 : 0 < Nsz sz n := lt_of_lt_of_le one_pos (PinsC2_one_le_Nsz sz n)
  exact (inv_nonneg.2 (by positivity)).trans (PinsC2_Bctl_ge sz n hη)

/-- **The local-law precision at height `y`** (`Step1Good_bctl`, `Step1Good.lean:301`):
`W^{τ_s/8} Bctl n (1 - y) ≤ N^{-15τ_s/16} + N^{τ_s/8} (N y)⁻¹`, for `τ_s ≤ 𝔠𝔡`, `𝔠 < 1`. -/
private theorem PinsC2_bctl {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 𝔡 τs : ℝ} (hd : 0 < d) (h𝔠 : 0 < 𝔠)
    (h𝔠1 : 𝔠 < 1) (h𝔡 : 0 < 𝔡) (hτs : 0 < τs) (hτ𝔠 : τs ≤ 𝔠 * 𝔡) (hN1 : 1 ≤ Nsz sz n)
    (hB : Nsz sz n ^ 𝔠 ≤ (sz.W n : ℝ))
    (hWO : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) {y : ℝ} (hy : 0 < y) :
    ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y) ≤
      Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hApos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := Real.rpow_pos_of_pos hW0 _
  have hlam := Sizes.lam_sq_mul_pow_ge sz n hWO
  have hb := un_Bctl_le sz n hy hApos hlam
  have hfloor := un_step1_floor hN1 hW1 h𝔠 h𝔠1 h𝔡 hτs hτ𝔠 hB
  have hWN : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) ≤ Nsz sz n ^ (τs / 8) :=
    Real.rpow_le_rpow hW0.le (PinsC2_W_le_size sz hd n) (by linarith)
  have hAinv : (((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ = ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) :=
    (Real.rpow_neg hW0.le _).symm
  have hy' : 0 ≤ (Nsz sz n * y)⁻¹ := by
    have : 0 < Nsz sz n := by linarith
    positivity
  calc ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - y)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) *
          ((((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡))⁻¹ + (Nsz sz n * y)⁻¹) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hW0.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) +
          ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (Nsz sz n * y)⁻¹ := by rw [hAinv]; ring
    _ ≤ Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * y)⁻¹ :=
        add_le_add hfloor (mul_le_mul_of_nonneg_right hWN hy')


/-! ## 3. Matrix facts and the C-form dictionary -/

section MatrixFacts

/-- A Hermitian matrix is positive semidefinite iff its real spectrum is nonnegative. -/
private theorem PinsC2_psd_iff {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    X.PosSemidef ↔ ∀ y ∈ spectrum ℝ X, 0 ≤ y := by
  rw [hX.posSemidef_iff_eigenvalues_nonneg, hX.spectrum_real_eq_range_eigenvalues]
  constructor
  · rintro h y ⟨i, rfl⟩
    exact h i
  · intro h i
    exact h _ ⟨i, rfl⟩

private theorem PinsC2_spec_sub {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (R : ℝ) {y : ℝ} :
    y ∈ spectrum ℝ (R • (1 : Matrix ι ι ℂ) - X) ↔ ∃ x ∈ spectrum ℝ X, y = R - x := by
  have h := spectrum.singleton_sub_eq X R
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [← h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    exact ⟨b, hb, by rw [ha]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R, rfl, x, hx, rfl⟩

private theorem PinsC2_spec_add {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (R : ℝ) {y : ℝ} :
    y ∈ spectrum ℝ (R • (1 : Matrix ι ι ℂ) + X) ↔ ∃ x ∈ spectrum ℝ X, y = R + x := by
  have h := spectrum.singleton_add_eq X R
  rw [Algebra.algebraMap_eq_smul_one] at h
  rw [← h]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    exact ⟨b, hb, by rw [ha]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨R, rfl, x, hx, rfl⟩

private theorem PinsC2_herm_sub {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (R : ℝ) : (R • (1 : Matrix ι ι ℂ) - X).IsHermitian :=
  (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hX

private theorem PinsC2_herm_add {ι : Type} [Fintype ι] [DecidableEq ι] {X : Matrix ι ι ℂ} (hX : X.IsHermitian)
    (R : ℝ) : (R • (1 : Matrix ι ι ℂ) + X).IsHermitian :=
  (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).add hX

/-- `|λ_i(A)| ≤ R` for all `i` iff `R • 1 - A` and `R • 1 + A` are positive semidefinite. -/
private theorem PinsC2_abs_iff_psd {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (R : ℝ) :
    (∀ i, |hA.eigenvalues i| ≤ R) ↔
      (R • (1 : Matrix ι ι ℂ) - A).PosSemidef ∧ (R • (1 : Matrix ι ι ℂ) + A).PosSemidef := by
  rw [PinsC2_psd_iff (PinsC2_herm_sub hA R), PinsC2_psd_iff (PinsC2_herm_add hA R)]
  constructor
  · intro h
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨x, hx, rfl⟩ := (PinsC2_spec_sub A R).1 hy
      rw [hA.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      linarith [(abs_le.1 (h i)).2]
    · obtain ⟨x, hx, rfl⟩ := (PinsC2_spec_add A R).1 hy
      rw [hA.spectrum_real_eq_range_eigenvalues] at hx
      obtain ⟨i, rfl⟩ := hx
      linarith [(abs_le.1 (h i)).1]
  · rintro ⟨h1, h2⟩ i
    have hmem : hA.eigenvalues i ∈ spectrum ℝ A := hA.eigenvalues_mem_spectrum_real i
    have a1 := h1 (R - hA.eigenvalues i) ((PinsC2_spec_sub A R).2 ⟨_, hmem, rfl⟩)
    have a2 := h2 (R + hA.eigenvalues i) ((PinsC2_spec_add A R).2 ⟨_, hmem, rfl⟩)
    exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Weyl for a convex combination** (route: `|λ_i| ≤ R` for all `i` iff `R • 1 ∓ A` positive semidefinite;
`R • 1 - C = a (R • 1 - A) + (1 - a) (R • 1 - B)`).  Used for `ouInit = a H + (1 - a) μ`. -/
theorem un_eigenvalues_abs_le_convex :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
      (hC : C.IsHermitian) {a R : ℝ}, 0 ≤ a → a ≤ 1 → C = a • A + (1 - a) • B →
        (∀ i, |hA.eigenvalues i| ≤ R) → (∀ i, |hB.eigenvalues i| ≤ R) → ∀ i, |hC.eigenvalues i| ≤ R := by
  intro ι _ _ A B C hA hB hC a R ha0 ha1 hCeq hAR hBR
  obtain ⟨hA1, hA2⟩ := (PinsC2_abs_iff_psd hA R).1 hAR
  obtain ⟨hB1, hB2⟩ := (PinsC2_abs_iff_psd hB R).1 hBR
  rw [PinsC2_abs_iff_psd hC R]
  have e1 : R • (1 : Matrix ι ι ℂ) - C = a • (R • (1 : Matrix ι ι ℂ) - A) + (1 - a) • (R • (1 : Matrix ι ι ℂ) - B) := by
    rw [hCeq]; module
  have e2 : R • (1 : Matrix ι ι ℂ) + C = a • (R • (1 : Matrix ι ι ℂ) + A) + (1 - a) • (R • (1 : Matrix ι ι ℂ) + B) := by
    rw [hCeq]; module
  refine ⟨?_, ?_⟩
  · rw [e1]; exact (hA1.smul ha0).add (hB1.smul (by linarith))
  · rw [e2]; exact (hA2.smul ha0).add (hB2.smul (by linarith))

/-- Every diagonal entry of a real diagonal matrix is one of its `IsHermitian.eigenvalues` (route: `charpoly_eq`,
`charpoly_diagonal`; the order of `eigenvalues` is not needed). -/
theorem un_exists_eigenvalues_eq_diagonal :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
      (hA : (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian) (j : ι), ∃ i, hA.eigenvalues i = u j := by
  intro ι _ _ u hA j
  have h1 := hA.charpoly_eq
  rw [Matrix.charpoly_diagonal] at h1
  have h2 := congrArg (Polynomial.eval (u j : ℂ)) h1
  rw [Polynomial.eval_prod, Polynomial.eval_prod] at h2
  have h3 : ∏ i, Polynomial.eval (u j : ℂ) (Polynomial.X - Polynomial.C (u i : ℂ)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ j) (by simp)
  rw [h3, eq_comm, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, -, hi⟩ := h2
  refine ⟨i, ?_⟩
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hi
  have : ((u j : ℝ) : ℂ) = ((hA.eigenvalues i : ℝ) : ℂ) := by
    simpa [sub_eq_zero] using hi
  exact_mod_cast this.symm


/-- `N⁻¹ tr (diag u - z)⁻¹ = mV u z` (`Gres`, the explicit inverse `diag ((u - z)⁻¹)`). -/
theorem stieltjesN_diagonal :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {z : ℂ}, 0 < z.im →
      stieltjesN (Matrix.diagonal (fun i => (u i : ℂ))) z = mV u z := by
  intro ι _ _ u z hz
  have hne : ∀ i, (u i : ℂ) - z ≠ 0 := fun i h => by
    have h2 : z.im = 0 := by
      have := congrArg Complex.im h
      simpa using this
    linarith
  have hsub : (Matrix.diagonal (fun i => (u i : ℂ))) - z • (1 : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => (u i : ℂ) - z) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hinv : (Matrix.diagonal (fun i => (u i : ℂ) - z))⁻¹ =
      Matrix.diagonal (fun i => ((u i : ℂ) - z)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    have hd : (fun i => ((u i : ℂ) - z) * ((u i : ℂ) - z)⁻¹) = fun _ => (1 : ℂ) :=
      funext fun i => mul_inv_cancel₀ (hne i)
    rw [hd, Matrix.diagonal_one]
  unfold stieltjesN Gres mV
  simp only [ite_true]
  rw [hsub, ← Matrix.nonsing_inv_eq_ringInverse, hinv, Matrix.trace_diagonal]

/-- `|(a - z)⁻¹| ≤ 1 / Im z`. -/
private theorem PinsC2_norm_inv_le (a : ℝ) {z : ℂ} (hz : 0 < z.im) : ‖((a : ℂ) - z)⁻¹‖ ≤ 1 / z.im := by
  rw [norm_inv]
  have h1 : z.im ≤ ‖(a : ℂ) - z‖ := by
    have := Complex.abs_im_le_norm ((a : ℂ) - z)
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg] at this
    rwa [abs_of_pos hz] at this
  rw [one_div]
  exact inv_anti₀ hz h1

/-- The `η`-Lipschitz bridge on a vertical line (`stieltjesN_eq_mV`, termwise
`|(λ - z)⁻¹ - (λ - z')⁻¹| ≤ |z - z'| / (Im z Im z')`). -/
theorem stieltjesN_vert_le :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}, H.IsHermitian → ∀ (x y y' : ℝ), 0 < y → 0 < y' →
      ‖stieltjesN H ⟨x, y⟩ - stieltjesN H ⟨x, y'⟩‖ ≤ |y - y'| / (y * y') := by
  intro ι _ _ H hH x y y' hy hy'
  rw [stieltjesN_eq_mV hH (z := ⟨x, y⟩) hy, stieltjesN_eq_mV hH (z := ⟨x, y'⟩) hy']
  unfold mV
  have hterm : ∀ i : ι, ‖((hH.eigenvalues i : ℂ) - ⟨x, y⟩)⁻¹ - ((hH.eigenvalues i : ℂ) - ⟨x, y'⟩)⁻¹‖ ≤
      |y - y'| / (y * y') := by
    intro i
    set l : ℝ := hH.eigenvalues i
    have hz1 : (⟨x, y⟩ : ℂ) ≠ (l : ℂ) := fun h => by
      have := congrArg Complex.im h; simp at this; linarith
    have hne1 : (l : ℂ) - ⟨x, y⟩ ≠ 0 := sub_ne_zero.2 hz1.symm
    have hne2 : (l : ℂ) - ⟨x, y'⟩ ≠ 0 := by
      intro h
      have := congrArg Complex.im h; simp at this; linarith
    have e : ((l : ℂ) - ⟨x, y⟩)⁻¹ - ((l : ℂ) - ⟨x, y'⟩)⁻¹ =
        ((l : ℂ) - ⟨x, y⟩)⁻¹ * ((l : ℂ) - ⟨x, y'⟩)⁻¹ * (((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩)) := by
      field_simp
    rw [e, norm_mul, norm_mul]
    have h1 : ‖((l : ℂ) - ⟨x, y⟩)⁻¹‖ ≤ 1 / y := PinsC2_norm_inv_le l (z := ⟨x, y⟩) hy
    have h2 : ‖((l : ℂ) - ⟨x, y'⟩)⁻¹‖ ≤ 1 / y' := PinsC2_norm_inv_le l (z := ⟨x, y'⟩) hy'
    have h3 : ‖((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩)‖ = |y - y'| := by
      have : ((l : ℂ) - ⟨x, y'⟩) - ((l : ℂ) - ⟨x, y⟩) = ((y - y' : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h3]
    calc ‖((l : ℂ) - ⟨x, y⟩)⁻¹‖ * ‖((l : ℂ) - ⟨x, y'⟩)⁻¹‖ * |y - y'|
        ≤ (1 / y) * (1 / y') * |y - y'| :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (abs_nonneg _)
      _ = |y - y'| / (y * y') := by field_simp
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, _root_.inv_zero, zero_mul, sub_self, norm_zero]; positivity
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hpos
    rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
    calc (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, (((hH.eigenvalues i : ℂ) - ⟨x, y⟩)⁻¹ - ((hH.eigenvalues i : ℂ) - ⟨x, y'⟩)⁻¹)‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i : ι, |y - y'| / (y * y') :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hterm i)) (by positivity)
      _ = |y - y'| / (y * y') := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-- The spectral dictionary `mV (λ(A) - E) (w) = stieltjesN A (w + E)` for a Hermitian `A`. -/
private theorem PinsC2_mV_shift {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (E : ℝ) {w : ℂ} (hw : 0 < w.im) :
    mV (fun i => hA.eigenvalues i - E) w = stieltjesN A (w + (E : ℂ)) := by
  have hz : 0 < (w + (E : ℂ)).im := by
    rw [Complex.add_im, Complex.ofReal_im, add_zero]; exact hw
  rw [stieltjesN_eq_mV hA hz]
  unfold mV
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  push_cast
  ring

/-- The C-form dictionary `mV (vOUC) (w) = stieltjesN (ouInit) (w + E)` (no rescaling; from `stieltjesN_eq_mV`). -/
theorem mV_vOUC :
    ∀ {d : ℕ} (sz : Sizes d) (M : UNModelC sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im →
      mV (vOUC sz M n τs E ω) w = stieltjesN (ouInit M n (ouTStar sz τs n) ω) (w + E) := by
  intro d sz M n τs E ω w hw
  exact PinsC2_mV_shift (ouInit_isHermitian M n (ouTStar sz τs n) ω) E hw

/-- `stieltjesN (a H) z = a⁻¹ stieltjesN H (a⁻¹ z)` (`Gres`; `a H - z = a (H - a⁻¹ z)`, `Ring.inverse_mul`). -/
private theorem PinsC2_stieltjesN_smul {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) {a : ℂ}
    (ha : a ≠ 0) (z : ℂ) : stieltjesN (a • H) z = a⁻¹ * stieltjesN H (a⁻¹ * z) := by
  unfold stieltjesN Gres
  simp only [ite_true]
  have hmat : a • H - z • (1 : Matrix ι ι ℂ) = (a • (1 : Matrix ι ι ℂ)) * (H - ((a⁻¹ * z) • (1 : Matrix ι ι ℂ))) := by
    rw [Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, mul_inv_cancel_left₀ ha]
  have hu : IsUnit (a • (1 : Matrix ι ι ℂ)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (isUnit_iff_ne_zero.2 ha).map _
  have hinv : Ring.inverse (a • (1 : Matrix ι ι ℂ)) = a⁻¹ • (1 : Matrix ι ι ℂ) := by
    rw [← Matrix.nonsing_inv_eq_ringInverse]
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [hmat, Ring.inverse_mul (Or.inl hu), hinv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp only [smul_eq_mul]
  ring

/-- For a mean-`0` model `ouInit = a H`, `a = e^{-t/2}`, and `stieltjesN (a H) z = a⁻¹ stieltjesN H (a⁻¹ z)`. -/
theorem stieltjesN_ouInit_toC :
    ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz) {z : ℂ}, 0 < z.im →
      stieltjesN (ouInit M.toC n t ω) z =
        ((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((Real.exp (-t / 2) : ℝ) : ℂ)⁻¹ * z) := by
  intro d sz M n t ω z hz
  have ha0 : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have haC : ((Real.exp (-t / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  have hI : ouInit M.toC n t ω = ((Real.exp (-t / 2) : ℝ) : ℂ) • M.H n ω := by
    ext i j
    simp [ouInit, UNModel.toC, Complex.real_smul]
  rw [hI]
  exact PinsC2_stieltjesN_smul (M.H n ω) haC z

end MatrixFacts

/-! ## 4. Monotonicity in the window, the mean bound of a mean-`0` model -/

/-- `UNDens'` passes to a smaller window. -/
theorem UNDens'.mono {m : ℕ → ℂ → ℂ} {E : ℝ} {ρ : ℕ → ℝ} {δ δ' : ℝ} (hδ : 0 < δ) (hδδ' : δ ≤ δ')
    (h : UNDens' m E ρ δ') : UNDens' m E ρ δ := by
  obtain ⟨⟨-, c, C, Lp, hc, hC, hLp, hev⟩, c', K, Lp', hc', hK, hLp', hev'⟩ := h
  refine ⟨⟨hδ, c, C, Lp, hc, hC, hLp, ?_⟩, c', K, Lp', hc', hK, hLp', ?_⟩
  · filter_upwards [hev] with n hn
    obtain ⟨h1, h2, h3⟩ := hn
    exact ⟨fun x η hx hη hη10 => h1 x η (hx.trans hδδ') hη hη10,
      fun x y η hx hy hη hη10 => h2 x y η (hx.trans hδδ') (hy.trans hδδ') hη hη10, h3⟩
  · filter_upwards [hev'] with n hn
    obtain ⟨h1, h2⟩ := hn
    exact ⟨fun z hz hz1 hz2 => h1 z (hz.trans hδδ') hz1 hz2,
      fun z z' hz hz1 hz2 hz' hz1' hz2' => h2 z z' (hz.trans hδδ') hz1 hz2 (hz'.trans hδδ') hz1' hz2'⟩

/-- `UNTrLocal` passes to a smaller window (the bad event shrinks). -/
theorem UNTrLocal.mono {d : ℕ} {sz : Sizes d} {M : UNModel sz} {m : ℕ → ℂ → ℂ} {E δ δ' : ℝ}
    (hδδ' : δ ≤ δ') (h : UNTrLocal sz M m E δ') : UNTrLocal sz M m E δ := by
  intro ε τ D hε hτ hD
  filter_upwards [h ε τ D hε hτ hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨z, h1, h2, h3, h4⟩
  exact ⟨z, h1.trans hδδ', h2, h3, h4⟩

/-- A mean-`0` model (in particular `(UNModel.band sz).toC`) has `UNMeanBound` for every `CV₀`. -/
theorem unMeanBound_toC {d : ℕ} (sz : Sizes d) (M : UNModel sz) (CV₀ : ℝ) : UNMeanBound sz M.toC CV₀ := by
  refine Eventually.of_forall fun n i => ?_
  have h0 : ((M.toC.mean_herm n).eigenvalues) = 0 :=
    (Matrix.IsHermitian.eigenvalues_eq_zero_iff (M.toC.mean_herm n)).2 rfl
  rw [h0]
  simp only [Pi.zero_apply, abs_zero]
  exact Real.rpow_nonneg (by linarith [PinsC2_one_le_Nsz sz n]) _


/-- `2 X B ≤ X² B` for `X ≥ 2`, `B ≥ 0`. -/
private theorem PinsC2_aux1 {X B : ℝ} (hX : 2 ≤ X) (hB : 0 ≤ B) : 2 * (X * B) ≤ X * X * B := by
  have h : 2 * X ≤ X * X := by nlinarith
  calc 2 * (X * B) = (2 * X) * B := by ring
    _ ≤ (X * X) * B := mul_le_mul_of_nonneg_right h hB

/-- `T C ≤ X² T` for `C ≤ X`, `X ≥ 1`, `T ≥ 0`. -/
private theorem PinsC2_aux2 {X T Cb : ℝ} (hX : 1 ≤ X) (hC : Cb ≤ X) (hT : 0 ≤ T) : T * Cb ≤ X * X * T := by
  have h : Cb ≤ X * X := by nlinarith
  calc T * Cb ≤ T * (X * X) := mul_le_mul_of_nonneg_left h hT
    _ = X * X * T := by ring

/-- `X B + 2 B ≤ X² B` for `X ≥ 2`, `B ≥ 0`. -/
private theorem PinsC2_aux3 {X B : ℝ} (hX : 2 ≤ X) (hB : 0 ≤ B) : X * B + 2 * B ≤ X * X * B := by
  have h : X + 2 ≤ X * X := by nlinarith
  calc X * B + 2 * B = (X + 2) * B := by ring
    _ ≤ (X * X) * B := mul_le_mul_of_nonneg_right h hB

/-! ## 5. The band instance of `UNTrLocalInit'`: the scaling argument -/

/-- The norm of `(y : ℝ) * I`. -/
private theorem PinsC2_norm_re_zero (y : ℝ) : ‖((y : ℝ) : ℂ) * Complex.I‖ = |y| := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 1000000 in
-- the rescaling argument has many `set` abbreviations and `linarith` calls in one proof
/-- **`unTrLocalInit'_of_unTrLocal`** (supervisor 1955 B2, "Band"): for a mean-`0` model and an `n`-independent
reference `m` bounded by `K` and `Lp`-Lipschitz on `|Re z - E| ≤ δ'`, `0 < Im z ≤ 2`, the local law in the window
`δ' > δ` gives `UNTrLocalInit'` in the window `δ`.  Route: `stieltjesN_ouInit_toC`; the point `ζ = a⁻¹ z` lies in
the window `δ'` eventually (`(1 + t*) δ + t* |E| ≤ δ'`) with `Im ζ ≥ Im z`, so `Bctl (1 - Im ζ) ≤ Bctl (1 - Im z)`;
`‖a⁻¹ m (a⁻¹ z) - m z‖ ≤ t* (K + Lp (|E| + δ + 1))`; for `Im ζ ∈ (1, a⁻¹]` the bridge `stieltjesN_vert_le` and the
Lipschitz bound to `Re ζ + i` (cost `≤ 2 (1 + Lp) t*`); the local law at `(ε, τ/2, D)`, and `2 W^{τ/2} ≤ W^τ`,
`const ≤ W^τ` eventually (`W → ∞`). -/
theorem unTrLocalInit'_of_unTrLocal :
    ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModel sz) (m : ℂ → ℂ) (E δ δ' K Lp : ℝ), 0 < δ → δ < δ' →
        (∀ z : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 → ‖m z‖ ≤ K) →
        (∀ z z' : ℂ, |z.re - E| ≤ δ' → 0 < z.im → z.im ≤ 2 →
          |z'.re - E| ≤ δ' → 0 < z'.im → z'.im ≤ 2 → ‖m z - m z'‖ ≤ Lp * ‖z - z'‖) →
        UNTrLocal sz M (fun _ => m) E δ' → UNTrLocalInit' sz M.toC (fun _ => m) E δ := by
  intro d sz 𝔠 𝔡 hA M m E δ δ' K Lp hδ hδδ' hK hLip hLoc
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK ⟨E, 1⟩ (by simpa using by linarith) one_pos (by norm_num))
  have hLp0 : 0 ≤ Lp := by
    have h := hLip ⟨E, 1⟩ ⟨E, 1 / 2⟩ (by simpa using by linarith) one_pos (by norm_num)
      (by simpa using by linarith) (by norm_num) (by norm_num)
    have hn : ‖(⟨E, 1⟩ : ℂ) - ⟨E, 1 / 2⟩‖ = 1 / 2 := by
      have : (⟨E, 1⟩ : ℂ) - ⟨E, 1 / 2⟩ = ((1 / 2 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp; norm_num
      rw [this, PinsC2_norm_re_zero]; norm_num
    rw [hn] at h
    nlinarith [norm_nonneg (m ⟨E, 1⟩ - m ⟨E, 1 / 2⟩)]
  intro τs hτs0 hτs1 ε τ D hε hτ hD
  have hW := PinsC2_W_tendsto hA
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  set Cb : ℝ := 2 + 2 * Lp + K + Lp * (|E| + δ + 1) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hδE : 0 < δ + |E| + 1 := by positivity
  filter_upwards [hLoc ε (τ / 2) D hε (by linarith) hD,
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + τs) (c := (δ' - δ) / (δ + |E| + 1)) (by linarith)
      (div_pos (by linarith) hδE)),
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hW).eventually_ge_atTop (max 2 Cb),
    hNtend.eventually_ge_atTop 1] with n hLn hTn hXn hN1
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  set T : ℝ := ouTStar sz τs n with hTdef
  have hTN : T = Nsz sz n ^ (-1 + τs) := rfl
  have hTpos : 0 < T := Real.rpow_pos_of_pos hN0 _
  have hT1 : T ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hTδ : T ≤ (δ' - δ) / (δ + |E| + 1) := hTn
  have hTδ' : T * (δ + |E| + 1) ≤ δ' - δ := by
    rw [le_div_iff₀ hδE] at hTδ; exact hTδ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hXdef
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hXn
  have hXC : Cb ≤ X := (le_max_right _ _).trans hXn
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = X * X := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    rw [hXdef, ← Real.rpow_add hW0]; congr 1; ring
  refine le_trans (measure_mono ?_) hLn
  rintro ω ⟨z, hz1, hz2, hz3, hz4⟩
  by_contra hno
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hno
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hz2
  set a : ℝ := Real.exp (-T / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have hainv : a⁻¹ ≤ 1 + T := PinsC2_inv_le hTpos.le hT1
  have hainv1 : 1 ≤ a⁻¹ := PinsC2_one_le_inv hTpos.le
  have hainv2 : a⁻¹ ≤ 2 := by linarith
  set ζ : ℂ := ((a : ℝ) : ℂ)⁻¹ * z with hζ
  have hζre : ζ.re = a⁻¹ * z.re := PinsC2_inv_mul_re a z
  have hζim : ζ.im = a⁻¹ * z.im := PinsC2_inv_mul_im a z
  have hζim_ge : z.im ≤ ζ.im := by
    rw [hζim]; nlinarith
  have hζim_le : ζ.im ≤ 1 + T := by
    rw [hζim]; nlinarith
  have hzabs : |z.re - E| ≤ δ := hz1
  have hζre_dom : |ζ.re - E| ≤ δ' := by
    rw [hζre]
    have e1 : a⁻¹ * z.re - E = a⁻¹ * (z.re - E) + (a⁻¹ - 1) * E := by ring
    rw [e1]
    have h1 : |a⁻¹ * (z.re - E)| ≤ (1 + T) * δ := by
      rw [abs_mul, abs_of_pos (inv_pos.2 ha0)]
      exact mul_le_mul hainv hzabs (abs_nonneg _) (by linarith)
    have h2 : |(a⁻¹ - 1) * E| ≤ T * |E| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |a⁻¹ * (z.re - E) + (a⁻¹ - 1) * E| ≤ |a⁻¹ * (z.re - E)| + |(a⁻¹ - 1) * E| := abs_add_le _ _
      _ ≤ (1 + T) * δ + T * |E| := add_le_add h1 h2
      _ ≤ δ' := by nlinarith [abs_nonneg E]
  have hzdom : |z.re - E| ≤ δ' := by linarith
  have hz2' : z.im ≤ 2 := by linarith
  -- the point `z''` of the local law
  set z'' : ℂ := ⟨ζ.re, min ζ.im 1⟩ with hz''
  have hz''im : z''.im = min ζ.im 1 := rfl
  have hz''re : z''.re = ζ.re := rfl
  have hz''im_ge : z.im ≤ z''.im := by
    rw [hz''im]; exact le_min hζim_ge hz3
  have hz''im_le : z''.im ≤ 1 := min_le_right _ _
  have hz''pos : 0 < z''.im := lt_of_lt_of_le hzim hz''im_ge
  have hζpos : 0 < ζ.im := lt_of_lt_of_le hzim hζim_ge
  have hloc := hno z'' (by rw [hz''re]; exact hζre_dom)
    (hz2.trans hz''im_ge) hz''im_le
  have hBc : sz.Bctl n (1 - z''.im) ≤ sz.Bctl n (1 - z.im) := PinsC2_Bctl_anti sz n hzim hz''im_ge
  have hB0 : 0 ≤ sz.Bctl n (1 - z.im) := PinsC2_Bctl_nonneg sz n hzim
  have hB0'' : 0 ≤ sz.Bctl n (1 - z''.im) := PinsC2_Bctl_nonneg sz n hz''pos
  have hlocS : ‖stieltjesN (M.H n ω) z'' - m z''‖ ≤ X * sz.Bctl n (1 - z.im) :=
    hloc.trans (mul_le_mul_of_nonneg_left hBc (by linarith))
  -- the bridge from `ζ` to `z''`
  have hdomζ : |ζ.re - E| ≤ δ' ∧ 0 < ζ.im ∧ ζ.im ≤ 2 := ⟨hζre_dom, hζpos, by linarith⟩
  have hdomz'' : |z''.re - E| ≤ δ' ∧ 0 < z''.im ∧ z''.im ≤ 2 := ⟨by rw [hz''re]; exact hζre_dom, hz''pos, by linarith⟩
  have hbrS : ‖stieltjesN (M.H n ω) ζ - stieltjesN (M.H n ω) z''‖ ≤ T := by
    by_cases hc : ζ.im ≤ 1
    · have : z'' = ζ := by
        apply Complex.ext
        · rfl
        · rw [hz''im]; exact min_eq_left hc
      rw [this, sub_self, norm_zero]; exact hTpos.le
    · push Not at hc
      have hz''1 : z''.im = 1 := by rw [hz''im]; exact min_eq_right hc.le
      have hζeta : ζ = ⟨ζ.re, ζ.im⟩ := rfl
      have hz''eta : z'' = ⟨ζ.re, 1⟩ := by
        apply Complex.ext
        · rfl
        · exact hz''1
      rw [hz''eta]
      have := stieltjesN_vert_le (M.herm n ω) ζ.re ζ.im 1 hζpos one_pos
      rw [← hζeta] at this
      refine this.trans ?_
      rw [mul_one, abs_of_pos (by linarith), div_le_iff₀ hζpos]
      have h1 : ζ.im - 1 ≤ T := by linarith
      have h2 : T ≤ T * ζ.im := le_mul_of_one_le_right hTpos.le hc.le
      linarith
  have hbrm : ‖m ζ - m z''‖ ≤ Lp * T := by
    by_cases hc : ζ.im ≤ 1
    · have : z'' = ζ := by
        apply Complex.ext
        · rfl
        · rw [hz''im]; exact min_eq_left hc
      rw [this, sub_self, norm_zero]; positivity
    · push Not at hc
      have hz''1 : z''.im = 1 := by rw [hz''im]; exact min_eq_right hc.le
      refine (hLip ζ z'' hdomζ.1 hdomζ.2.1 hdomζ.2.2 hdomz''.1 hdomz''.2.1 hdomz''.2.2).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hLp0
      have : ζ - z'' = ((ζ.im - 1 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hz''1, hz''re]
      rw [this, PinsC2_norm_re_zero, abs_of_pos (by linarith)]
      linarith
  -- the scaling bridge `‖a⁻¹ m ζ - m z‖`
  have hmζ : ‖m ζ‖ ≤ K := hK ζ hdomζ.1 hdomζ.2.1 hdomζ.2.2
  have hζz : ‖ζ - z‖ ≤ T * (|E| + δ + 1) := by
    have e : ζ - z = (((a⁻¹ - 1 : ℝ) : ℂ)) * z := by
      rw [hζ]; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hzn : ‖z‖ ≤ |E| + δ + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
      rw [abs_of_pos hzim]
      have : |z.re| ≤ |E| + δ := by
        calc |z.re| = |(z.re - E) + E| := by ring_nf
          _ ≤ |z.re - E| + |E| := abs_add_le _ _
          _ ≤ δ + |E| := by linarith
          _ = |E| + δ := add_comm _ _
      linarith
    exact mul_le_mul (by linarith) hzn (norm_nonneg _) hTpos.le
  have hmz : ‖m ζ - m z‖ ≤ Lp * (T * (|E| + δ + 1)) :=
    (hLip ζ z hdomζ.1 hdomζ.2.1 hdomζ.2.2 hzdom hzim hz2').trans (mul_le_mul_of_nonneg_left hζz hLp0)
  have hscale : ‖((a : ℝ) : ℂ)⁻¹ * m ζ - m z‖ ≤ T * K + Lp * (T * (|E| + δ + 1)) := by
    have e : ((a : ℝ) : ℂ)⁻¹ * m ζ - m z = (((a⁻¹ - 1 : ℝ) : ℂ)) * m ζ + (m ζ - m z) := by
      push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add ?_ hmz)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul (by linarith) hmζ (norm_nonneg _) hTpos.le
  -- assemble
  have hdict := stieltjesN_ouInit_toC sz M n T ω hzim
  rw [hdict] at hz4
  have hsplit : ((a : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((a : ℝ) : ℂ)⁻¹ * z) - m z =
      ((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) ζ - stieltjesN (M.H n ω) z'') +
      ((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) z'' - m z'') +
      ((a : ℝ) : ℂ)⁻¹ * (m z'' - m ζ) + (((a : ℝ) : ℂ)⁻¹ * m ζ - m z) := by
    rw [← hζ]; ring
  have hainvn : ‖((a : ℝ) : ℂ)⁻¹‖ ≤ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]; exact hainv2
  have hfin : ‖((a : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((a : ℝ) : ℂ)⁻¹ * z) - m z‖ ≤
      2 * (X * sz.Bctl n (1 - z.im)) + T * Cb := by
    rw [hsplit]
    have t1 : ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) ζ - stieltjesN (M.H n ω) z'')‖ ≤ 2 * T := by
      rw [norm_mul]
      exact mul_le_mul hainvn hbrS (norm_nonneg _) (by norm_num)
    have t2 : ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) z'' - m z'')‖ ≤ 2 * (X * sz.Bctl n (1 - z.im)) := by
      rw [norm_mul]
      exact mul_le_mul hainvn hlocS (norm_nonneg _) (by norm_num)
    have t3 : ‖((a : ℝ) : ℂ)⁻¹ * (m z'' - m ζ)‖ ≤ 2 * (Lp * T) := by
      rw [norm_mul, ← norm_neg (m z'' - m ζ), neg_sub]
      exact mul_le_mul hainvn hbrm (norm_nonneg _) (by norm_num)
    have t4 := hscale
    calc _ ≤ ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) ζ - stieltjesN (M.H n ω) z'')‖ +
          ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN (M.H n ω) z'' - m z'')‖ +
          ‖((a : ℝ) : ℂ)⁻¹ * (m z'' - m ζ)‖ + ‖((a : ℝ) : ℂ)⁻¹ * m ζ - m z‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ 2 * T + 2 * (X * sz.Bctl n (1 - z.im)) + 2 * (Lp * T) + (T * K + Lp * (T * (|E| + δ + 1))) := by
          linarith
      _ = 2 * (X * sz.Bctl n (1 - z.im)) + T * Cb := by rw [hCb]; ring
  -- contradiction with `hz4`
  have hz4' : ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + T) <
      ‖((a : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((a : ℝ) : ℂ)⁻¹ * z) - m z‖ := hz4
  have hup : 2 * (X * sz.Bctl n (1 - z.im)) + T * Cb ≤
      ((sz.W n : ℕ) : ℝ) ^ τ * (sz.Bctl n (1 - z.im) + T) := by
    rw [hWτ]
    have h1 := PinsC2_aux1 hX2 hB0
    have h2 := PinsC2_aux2 (by linarith : (1 : ℝ) ≤ X) hXC hTpos.le
    linarith
  linarith


/-- **`unTrLocalInit'_band_zero`**: the band model at `msc`, `E = 0`: `UNTrLocal` in the window `1/2` gives
`UNTrLocalInit'` in the window `1/4` (`K = 1` from `norm_msc_lt_one`, `Lp = 10000/81` from `un_msc_lip` with
`un_msc_im_ge` on `|Re z| ≤ 1/2`, `0 < Im z ≤ 2 ≤ 10`). -/
theorem unTrLocalInit'_band_zero :
    ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 →
      UNTrLocal sz (UNModel.band sz) (fun _ => msc) 0 (1 / 2) →
        UNTrLocalInit' sz (UNModel.band sz).toC (fun _ => msc) 0 (1 / 4) := by
  intro d sz 𝔠 𝔡 hA hT
  refine unTrLocalInit'_of_unTrLocal sz hA (UNModel.band sz) msc 0 (1 / 4) (1 / 2) 1 (10000 / 81)
    (by norm_num) (by norm_num) ?_ ?_ hT
  · intro z _ hz1 _
    exact (norm_msc_lt_one hz1).le
  · intro z z' hz hz1 hz2 hz' hz1' hz2'
    exact un_msc_lip hz1 hz1' (un_msc_im_ge hz1 (by linarith) (by simpa using hz))
      (un_msc_im_ge hz1' (by linarith) (by simpa using hz'))

/-! ## 6. The conditional refutation of `UNStep1GoodC'` (finding T2208a) -/

/-- The eigenvalues of a Hermitian matrix depend only on the matrix. -/
private theorem PinsC2_eig_eq {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) : hA.eigenvalues = hB.eigenvalues := by
  subst h; rfl

/-- A real diagonal matrix is Hermitian. -/
private theorem PinsC2_diag_herm {ι : Type*} [DecidableEq ι] (u : ι → ℝ) :
    (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _ (funext fun i => Complex.conj_ofReal _)

/-- The rank-one transfer on `mV`: changing one entry moves `mV` by at most `2 / (N Im z)`. -/
private theorem PinsC2_mV_single {ι : Type} [Fintype ι] [DecidableEq ι] (u u' : ι → ℝ) (j : ι)
    (h : ∀ i, i ≠ j → u' i = u i) {z : ℂ} (hz : 0 < z.im) :
    ‖mV u' z - mV u z‖ ≤ 2 / ((Fintype.card ι : ℝ) * z.im) := by
  have hc : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨j⟩
  unfold mV
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_eq_single j]
  · rw [norm_mul, norm_inv, Complex.norm_natCast]
    have h1 := PinsC2_norm_inv_le (u' j) hz
    have h2 := PinsC2_norm_inv_le (u j) hz
    have h3 : ‖(((u' j : ℝ) : ℂ) - z)⁻¹ - (((u j : ℝ) : ℂ) - z)⁻¹‖ ≤ 1 / z.im + 1 / z.im :=
      (norm_sub_le _ _).trans (add_le_add h1 h2)
    calc (Fintype.card ι : ℝ)⁻¹ * ‖(((u' j : ℝ) : ℂ) - z)⁻¹ - (((u j : ℝ) : ℂ) - z)⁻¹‖
        ≤ (Fintype.card ι : ℝ)⁻¹ * (1 / z.im + 1 / z.im) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 2 / ((Fintype.card ι : ℝ) * z.im) := by field_simp; ring
  · intro i _ hi
    rw [h i hi, sub_self]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- A deterministic event of probability `< 1` is empty (the sets do not depend on `ω`): used in the form
"`μ S ≤ ofReal c`, `c < 1`, `S = univ` is impossible". -/
private theorem PinsC2_univ_not_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {c : ℝ} (hc : c < 1) (h : μ Set.univ ≤ ENNReal.ofReal c) : False := by
  rw [measure_univ] at h
  have := (ENNReal.one_le_ofReal).1 h
  linarith

/-- The shifted centred model: the same `H` and law, the mean replaced by `μ`. -/
private def PinsC2_shift {d : ℕ} {sz : Sizes d} (M : UNModelC sz)
    (μ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hμ : ∀ n, (μ n).IsHermitian) : UNModelC sz :=
  { M with mean := μ, mean_herm := hμ }

/-- `not_UNStep1GoodC'_of_diag`: if a deterministic diagonal model `H = mean = diag γ_n` meets the hypotheses of
`UNStep1GoodC'`, then `UNStep1GoodC'` gives `False`.  Route: `M'` = `M` with `mean' n = diag (γ_n + R_n e_{i₀})`,
`R_n = 4N (N^{CV₀+1} + |E| + |γ_{n,i₀}| + 1)` (independent of `τ_s`); `ouInit M' = diag (γ_n + (1 - a) R_n e_{i₀})`;
`UNTrLocalInit` transfers from `M` at `τ/2` (`stieltjesN_diagonal`: the two transforms differ by `≤ 2/(Nη)`, and
`(Nη)⁻¹ ≤ Bctl (1 - η)`; `W^{τ/2} ≥ 2` eventually); `M'.toUNModel = M.toUNModel`; `UNStep1GoodC'` at `M'`,
`τ_s = min (𝔠𝔡) (1/2)`, `D = 1`; the bad event is everything, because `un_exists_eigenvalues_eq_diagonal` gives an
eigenvalue `γ_{i₀} + (1 - a) R_n ≥ N^{CV₀+1} + |E| + 1` of `ouInit M'` (`1 - a ≥ t*/4 ≥ N^{-1}/4`), so (2.3) fails;
`1 ≤ N^{-1}` is false for `N ≥ 2`. -/
theorem not_UNStep1GoodC'_of_diag :
    UNStep1GoodC' →
      ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
        ∀ (M : UNModelC sz) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ),
          (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) →
          (∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ))) →
          ∀ (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
            UNDens' m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ →
              UNNormBound sz M.toUNModel CV₀ → False := by
  intro hS d hd 𝔠 𝔡 sz hA M γ hH hmean m E ρ δ hD hT CV₀ hCV hN
  have hτs0 : 0 < min (𝔠 * 𝔡) (1 / 2) := lt_min (mul_pos hA.1 hA.2.1) (by norm_num)
  have hτs1 : min (𝔠 * 𝔡) (1 / 2) < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hτsle : min (𝔠 * 𝔡) (1 / 2) ≤ 𝔠 * 𝔡 := min_le_left _ _
  -- the shifted mean
  let i0 : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) := fun n _ => 0
  let R : ℕ → ℝ := fun n => 4 * Nsz sz n * (Nsz sz n ^ (CV₀ + 1) + |E| + |γ n (i0 n)| + 1)
  let w : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ := fun n i => γ n i + (if i = i0 n then R n else 0)
  let M' : UNModelC sz := PinsC2_shift M (fun n => Matrix.diagonal (fun i => ((w n i : ℝ) : ℂ)))
    (fun n => PinsC2_diag_herm (w n))
  have hM'μ : M'.μ = M.μ := rfl
  have hM'H : ∀ n ω, M'.H n ω = M.H n ω := fun _ _ => rfl
  have hM'mean : ∀ n, M'.mean n = Matrix.diagonal (fun i => ((w n i : ℝ) : ℂ)) := fun _ => rfl
  -- `ouInit` of both models
  have hI : ∀ n (t : ℝ) ω, ouInit M n t ω = Matrix.diagonal (fun i => (γ n i : ℂ)) := by
    intro n t ω
    unfold ouInit
    rw [hmean n, hH n ω, sub_self, smul_zero, add_zero]
  have hI' : ∀ n (t : ℝ) ω, ouInit M' n t ω =
      Matrix.diagonal (fun i => ((γ n i + (1 - Real.exp (-t / 2)) * (if i = i0 n then R n else 0) : ℝ) : ℂ)) := by
    intro n t ω
    unfold ouInit
    rw [hM'mean n, hM'H n ω, hH n ω]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq,
        Complex.real_smul, w]
      push_cast
      ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  -- `UNTrLocalInit` transfers
  have hT' : UNTrLocalInit sz M' m E δ := by
    intro τs hτs0' hτs1' ε τ D hε hτ hD
    have hW := PinsC2_W_tendsto hA
    filter_upwards [hT τs hτs0' hτs1' ε (τ / 2) D hε (by linarith) hD,
      ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hW).eventually_ge_atTop 2] with n hn hX
    refine le_trans (measure_mono ?_) hn
    rintro ω ⟨z, hz1, hz2, hz3, hz4⟩
    have hN0 : (0 : ℝ) < Nsz sz n := lt_of_lt_of_le one_pos (PinsC2_one_le_Nsz sz n)
    have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hz2
    refine ⟨z, hz1, hz2, hz3, ?_⟩
    set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hXdef
    have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = X * X := by
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      rw [hXdef, ← Real.rpow_add hW0]; congr 1; ring
    have hB0 := PinsC2_Bctl_nonneg sz n hzim
    have hBge := PinsC2_Bctl_ge sz n hzim
    have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
      exact_mod_cast sz.card_Idx n
    have hD1 : ‖stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - stieltjesN (ouInit M n (ouTStar sz τs n) ω) z‖ ≤
        2 * sz.Bctl n (1 - z.im) := by
      rw [hI' n _ ω, hI n _ ω, stieltjesN_diagonal _ hzim, stieltjesN_diagonal _ hzim]
      refine (PinsC2_mV_single (γ n) _ (i0 n) ?_ hzim).trans ?_
      · intro i hi
        simp [hi]
      · rw [hcard, div_eq_mul_inv]
        linarith
    rw [hWτ] at hz4
    have h3 := PinsC2_aux3 (show 2 ≤ X from hX) hB0
    have h4 : ‖stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - m n z‖ ≤
        ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖ +
          ‖stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - stieltjesN (ouInit M n (ouTStar sz τs n) ω) z‖ := by
      have := norm_add_le (stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z)
        (stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - stieltjesN (ouInit M n (ouTStar sz τs n) ω) z)
      have e : stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z +
          (stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - stieltjesN (ouInit M n (ouTStar sz τs n) ω) z) =
            stieltjesN (ouInit M' n (ouTStar sz τs n) ω) z - m n z := by ring
      rw [e] at this
      exact this
    linarith
  -- apply the pin at `M'`
  obtain ⟨c, C, hc, hev⟩ := hS d hd 𝔠 𝔡 sz hA M' m E ρ δ hD hT' CV₀ hCV hN
    (min (𝔠 * 𝔡) (1 / 2)) 1 hτs0 hτs1 hτsle one_pos
  obtain ⟨n, hn, hN2⟩ := (hev.and (hA.2.2.1.eventually_ge_atTop 2)).exists
  have hN1 : (1 : ℝ) ≤ Nsz sz n := PinsC2_one_le_Nsz sz n
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by exact_mod_cast sz.card_Idx n
  set τs : ℝ := min (𝔠 * 𝔡) (1 / 2) with hτsdef
  set t : ℝ := ouTStar sz τs n with htdef
  have htN : t = Nsz sz n ^ (-1 + τs) := rfl
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have ht0 : 0 < t := Real.rpow_pos_of_pos hN0 _
  have htge : (Nsz sz n)⁻¹ ≤ t := by
    rw [htN, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hquarter := PinsC2_quarter_le ht0.le ht1
  have hRq : (Nsz sz n)⁻¹ / 4 * R n = Nsz sz n ^ (CV₀ + 1) + |E| + |γ n (i0 n)| + 1 := by
    simp only [R]
    field_simp
  have hRnn : 0 ≤ R n := by
    simp only [R]; positivity
  have hmain : ∀ ω, ¬ (IsRegular32 (vOUC sz M' n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
        (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M' n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8))) := by
    intro ω hh
    have h23 := hh.1.2
    have hdiag := PinsC2_diag_herm (fun j => γ n j + (1 - Real.exp (-t / 2)) * (if j = i0 n then R n else 0))
    obtain ⟨i, hi⟩ := un_exists_eigenvalues_eq_diagonal
      (fun j => γ n j + (1 - Real.exp (-t / 2)) * (if j = i0 n then R n else 0)) hdiag (i0 n)
    have heig := PinsC2_eig_eq (ouInit_isHermitian M' n t ω) hdiag (hI' n t ω)
    have h23i := h23 i
    simp only [vOUC] at h23i
    rw [hcard, show ((ouInit_isHermitian M' n (ouTStar sz τs n) ω).eigenvalues i) = hdiag.eigenvalues i from
      congrFun heig i, hi] at h23i
    simp only [ite_true] at h23i
    have hge : Nsz sz n ^ (CV₀ + 1) + 1 ≤
        γ n (i0 n) + (1 - Real.exp (-t / 2)) * R n - E := by
      have h1 : (Nsz sz n)⁻¹ / 4 * R n ≤ (1 - Real.exp (-t / 2)) * R n :=
        mul_le_mul_of_nonneg_right (by linarith) hRnn
      have h2 := neg_abs_le (γ n (i0 n))
      have h3 := neg_le_abs E
      have h4 := le_abs_self E
      linarith
    have := (le_abs_self _).trans h23i
    linarith
  refine PinsC2_univ_not_le M'.μ (c := Nsz sz n ^ (-(1 : ℝ))) ?_ ?_
  · rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  · have hset : {ω | ¬ (IsRegular32 (vOUC sz M' n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
          (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
        ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M' n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
          ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
            |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} = Set.univ :=
      Set.eq_univ_of_forall hmain
    rw [← hset]
    exact hn


/-! ## 7. The C-form Step 1 -/

/-- **The closeness hypothesis of `freeConv_stable_lip`** on the strip, C form (`Step1Good_strip`,
`Step1Good.lean:333`, with `v = λ(A) - E`, no `e^{-T/2}` factor in the dictionary, the local law at the tolerance
`N^{-15τ_s/16} + N^{τ_s/8} (N y)⁻¹ + N^{-1+9τ_s/8}` and the bridge term `T (K + Lp (|E| + δ + 1))` of
`‖m ζ - a⁻¹ m (a⁻¹ ζ)‖`): for `|Re w| ≤ c₁`, `c₀ t/4 ≤ Im w ≤ 1/2`. -/
private theorem PinsC2_strip {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs c₀ c₁ K Lp : ℝ}
    (hN1 : 1 ≤ N) (hc₀ : 0 < c₀) (hδ : 0 < δ) (hc₁ : c₁ ≤ δ / 4) (hK0 : 0 ≤ K) (hLp0 : 0 ≤ Lp)
    (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (hK : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → ‖mr z‖ ≤ K)
    (hlip : ∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mr z - mr z'‖ ≤ Lp * ‖z - z'‖)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    {w : ℂ} (hw : |w.re| ≤ c₁) (hlow : c₀ * (1 - Real.exp (-T)) / 4 ≤ w.im) (hw1 : w.im ≤ 1 / 2) :
    ‖mV (fun i => hA.eigenvalues i - E) w -
        (Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * mr ((Real.sqrt (Real.exp (-T)) : ℂ)⁻¹ * (w + E))‖ ≤
      (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        (K + Lp * (|E| + δ + 1)) * T := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hT1' : T ≤ 1 := by linarith
  rw [PinsC2_sqrt_exp]
  have ha0 : 0 < Real.exp (-T / 2) := Real.exp_pos _
  have hainv : (Real.exp (-T / 2))⁻¹ ≤ 1 + T := PinsC2_inv_le hTpos.le hT1'
  have hainv1 : 1 ≤ (Real.exp (-T / 2))⁻¹ := PinsC2_one_le_inv hTpos.le
  have hhalf := PinsC2_half_le_one_sub_exp hTpos.le hT1'
  have hy : c₀ / 8 * T ≤ w.im := by
    have : c₀ / 8 * T ≤ c₀ * (1 - Real.exp (-T)) / 4 := by nlinarith
    exact this.trans hlow
  have hy0 : 0 < c₀ / 8 * T := by positivity
  have hw0 : 0 < w.im := lt_of_lt_of_le hy0 hy
  have hc₁0 : 0 ≤ c₁ := (abs_nonneg _).trans hw
  have hdict : mV (fun i => hA.eigenvalues i - E) w = stieltjesN A (w + (E : ℂ)) := PinsC2_mV_shift hA E hw0
  rw [hdict]
  set a : ℝ := Real.exp (-T / 2) with ha
  set ζ : ℂ := w + (E : ℂ) with hζ
  set ζ' : ℂ := ((a : ℝ) : ℂ)⁻¹ * ζ with hζ'
  have hζre : ζ.re = w.re + E := by rw [hζ, Complex.add_re, Complex.ofReal_re]
  have hζim : ζ.im = w.im := by rw [hζ, Complex.add_im, Complex.ofReal_im, add_zero]
  have hζ're : ζ'.re = a⁻¹ * (w.re + E) := by rw [hζ', PinsC2_inv_mul_re, hζre]
  have hζ'im : ζ'.im = a⁻¹ * w.im := by rw [hζ', PinsC2_inv_mul_im, hζim]
  have hζdom : |ζ.re - E| ≤ δ := by
    rw [hζre]; have : w.re + E - E = w.re := by ring
    rw [this]; linarith
  have hζ'dom : |ζ'.re - E| ≤ δ := by
    rw [hζ're]
    have e1 : a⁻¹ * (w.re + E) - E = a⁻¹ * w.re + (a⁻¹ - 1) * E := by ring
    rw [e1]
    have h1 : |a⁻¹ * w.re| ≤ (1 + T) * c₁ := by
      rw [abs_mul, abs_of_pos (inv_pos.2 ha0)]
      exact mul_le_mul hainv hw (abs_nonneg _) (by linarith)
    have h2 : |(a⁻¹ - 1) * E| ≤ T * |E| := by
      rw [abs_mul, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    calc |a⁻¹ * w.re + (a⁻¹ - 1) * E| ≤ |a⁻¹ * w.re| + |(a⁻¹ - 1) * E| := abs_add_le _ _
      _ ≤ (1 + T) * c₁ + T * |E| := add_le_add h1 h2
      _ ≤ δ := by nlinarith [abs_nonneg E]
  have hζ'pos : 0 < ζ'.im := by rw [hζ'im]; positivity
  have hζ'le : ζ'.im ≤ 1 := by
    rw [hζ'im]
    calc a⁻¹ * w.im ≤ (1 + T) * (1 / 2) := mul_le_mul hainv hw1 hw0.le (by linarith)
      _ ≤ 1 := by linarith
  have hζpos : 0 < ζ.im := by rw [hζim]; exact hw0
  have hζle : ζ.im ≤ 1 := by rw [hζim]; linarith
  have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := by rw [hζim]; exact hedge.trans hy
  have herrz := hpt ζ hζdom hdomlo hζle
  -- `(N Im ζ)⁻¹ ≤ 8 c₀⁻¹ N^{-τs}`
  have hNT : N * T = N ^ τs := by
    have : N ^ (1 + (-1 + τs)) = N * N ^ (-1 + τs) := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hTN, ← this]; congr 1; ring
  have hinv : (N * ζ.im)⁻¹ ≤ 8 * c₀⁻¹ * (N ^ τs)⁻¹ := by
    have h1 : N * (c₀ / 8 * T) ≤ N * ζ.im := by
      rw [hζim]; exact mul_le_mul_of_nonneg_left hy hN0.le
    have h2 : 0 < N * (c₀ / 8 * T) := by positivity
    refine (inv_anti₀ h2 h1).trans (le_of_eq ?_)
    rw [← hNT]
    have : N * (c₀ / 8 * T) = c₀ / 8 * (N * T) := by ring
    rw [this, mul_inv, inv_div]
    have hNTpos : 0 < N * T := by positivity
    field_simp
  have hsplit : N ^ (τs / 8) * (N ^ τs)⁻¹ = N ^ (-(7 * τs / 8)) := by
    rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
  have herr' : ‖stieltjesN A ζ - mr ζ‖ ≤
      (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) := by
    refine herrz.trans ?_
    have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
    have h1 : N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ 8 * c₀⁻¹ * N ^ (-(7 * τs / 8)) := by
      calc N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (τs / 8) * (8 * c₀⁻¹ * (N ^ τs)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv hNa
        _ = 8 * c₀⁻¹ * (N ^ (τs / 8) * (N ^ τs)⁻¹) := by ring
        _ = _ := by rw [hsplit]
    linarith
  -- the bridge `‖m ζ - a⁻¹ m (a⁻¹ ζ)‖ ≤ T (K + Lp (|E| + δ + 1))`
  have hmζ' : ‖mr ζ'‖ ≤ K := hK ζ' hζ'dom hζ'pos hζ'le
  have hζζ' : ‖ζ - ζ'‖ ≤ T * (|E| + δ + 1) := by
    have e : ζ - ζ' = (((1 - a⁻¹ : ℝ) : ℂ)) * ζ := by
      rw [hζ']; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    have hζn : ‖ζ‖ ≤ |E| + δ + 1 := by
      refine (Complex.norm_le_abs_re_add_abs_im ζ).trans ?_
      rw [abs_of_pos hζpos, hζre]
      have : |w.re + E| ≤ |E| + δ := by
        calc |w.re + E| ≤ |w.re| + |E| := abs_add_le _ _
          _ ≤ δ + |E| := by linarith
          _ = |E| + δ := add_comm _ _
      linarith
    exact mul_le_mul (by linarith) hζn (norm_nonneg _) hTpos.le
  have hm1 : ‖mr ζ - mr ζ'‖ ≤ Lp * (T * (|E| + δ + 1)) :=
    (hlip ζ ζ' hζdom hζpos hζle hζ'dom hζ'pos hζ'le).trans (mul_le_mul_of_nonneg_left hζζ' hLp0)
  have hm2 : ‖mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ'‖ ≤ T * K := by
    have e : mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ' = (((1 - a⁻¹ : ℝ) : ℂ)) * mr ζ' := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    exact mul_le_mul (by linarith) hmζ' (norm_nonneg _) hTpos.le
  have hbridge : ‖mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ'‖ ≤ (K + Lp * (|E| + δ + 1)) * T := by
    have e : mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ' = (mr ζ - mr ζ') + (mr ζ' - ((a : ℝ) : ℂ)⁻¹ * mr ζ') := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    nlinarith
  have e2 : stieltjesN A ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ' =
      (stieltjesN A ζ - mr ζ) + (mr ζ - ((a : ℝ) : ℂ)⁻¹ * mr ζ') := by ring
  rw [e2]
  refine (norm_add_le _ _).trans ?_
  linarith


/-- **The regularity part**, C form (`Step1Good_regular`, `Step1Good.lean:423`; supervisor 2.2): `[32]`-regularity
(2.2), (2.3) of `v = λ(A) - E` with `g = N^{-1+τ_s/4}`, `c = c_box/40`, `C = 2K + c_box + 2`, `CV = CV₀ + 1`, from the
local law at the points `x + E + iη` (`η ≤ 1/2`: `Im m_V ∈ [c_box/2, K + c_box/2]`; `1/2 < η ≤ 10`: `η Im m_V`
nondecreasing and `Im m_V ≤ 1/η`) and from `|λ_i(A)| ≤ N^{CV₀}`. -/
private theorem PinsC2_regular {ι : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) {N T E δ τs cb K CV₀ G : ℝ}
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hcb : 0 < cb) (hK : 0 < K) (hδ : 0 < δ)
    (hτs : 0 < τs) (hTN : T = N ^ (-1 + τs)) (hT1 : T ≤ 1 / 2) (hG : G ≤ δ)
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) + N ^ (-1 + 9 * τs / 8) ≤ cb / 2)
    (hnorm : ∀ i, |hA.eigenvalues i| ≤ N ^ CV₀) (hCV : 0 ≤ CV₀) :
    IsRegular32 (fun i => hA.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
      (cb / 40) (2 * K + cb + 2) (CV₀ + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  have hgpos : 0 < N ^ (-1 + τs / 4) := Real.rpow_pos_of_pos hN0 _
  have hg12 : N ^ (-1 + τs / 4) ≤ 1 / 2 := by
    calc N ^ (-1 + τs / 4) ≤ N ^ (-1 + τs) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = T := hTN.symm
      _ ≤ 1 / 2 := hT1
  have hK0 : 0 < K := hK
  -- the bulk claim: `η ≤ 1/2`
  have hmain : ∀ E' η : ℝ, |E'| ≤ G → N ^ (-1 + τs / 4) ≤ η → η ≤ 1 / 2 →
      cb / 2 ≤ (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im ∧
        (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im ≤ K + cb / 2 := by
    intro E' η hE' hgη hη1
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    set ζ : ℂ := (⟨E', η⟩ : ℂ) + (E : ℂ) with hζ
    have hzre : ζ.re = E' + E := by rw [hζ, Complex.add_re, Complex.ofReal_re]
    have hzim : ζ.im = η := by rw [hζ, Complex.add_im, Complex.ofReal_im, add_zero]
    have hdomre : |ζ.re - E| ≤ δ := by
      rw [hzre]; have : E' + E - E = E' := by ring
      rw [this]; linarith
    have hgg : N ^ (-1 + τs / 8) ≤ N ^ (-1 + τs / 4) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hdomlo : N ^ (-1 + τs / 8) ≤ ζ.im := by rw [hzim]; exact hgg.trans hgη
    have hzpos : 0 < ζ.im := by rw [hzim]; exact hη0
    have hdomhi : ζ.im ≤ 1 := by rw [hzim]; linarith
    have herrz := hpt ζ hdomre hdomlo hdomhi
    have hNg : N * N ^ (-1 + τs / 4) = N ^ (τs / 4) := by
      have : N ^ (1 + (-1 + τs / 4)) = N * N ^ (-1 + τs / 4) := by rw [Real.rpow_add hN0, Real.rpow_one]
      rw [← this]; congr 1; ring
    have hinv : (N * ζ.im)⁻¹ ≤ (N ^ (τs / 4))⁻¹ := by
      rw [← hNg]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (by rw [hzim]; exact hgη) hN0.le)
    have hsplit : N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ = N ^ (-(τs / 8)) := by
      rw [← Real.rpow_neg hN0.le, ← Real.rpow_add hN0]; congr 1; ring
    have hloc : ‖stieltjesN A ζ - mr ζ‖ ≤ cb / 2 := by
      refine herrz.trans (le_trans ?_ herr)
      have hNa : 0 ≤ N ^ (τs / 8) := Real.rpow_nonneg hN0.le _
      have : N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (-(τs / 8)) := by
        calc N ^ (τs / 8) * (N * ζ.im)⁻¹ ≤ N ^ (τs / 8) * (N ^ (τs / 4))⁻¹ :=
              mul_le_mul_of_nonneg_left hinv hNa
          _ = _ := hsplit
      linarith
    obtain ⟨hb1, hb2⟩ := hbox ζ hdomre hzpos hdomhi
    have hIm : |(stieltjesN A ζ).im - (mr ζ).im| ≤ cb / 2 := by
      calc |(stieltjesN A ζ).im - (mr ζ).im| = |(stieltjesN A ζ - mr ζ).im| := by rw [Complex.sub_im]
        _ ≤ ‖stieltjesN A ζ - mr ζ‖ := Complex.abs_im_le_norm _
        _ ≤ cb / 2 := hloc
    have hmrim : (mr ζ).im ≤ K := (le_abs_self _).trans ((Complex.abs_im_le_norm _).trans hb2)
    obtain ⟨h1, h2⟩ := abs_le.mp hIm
    have hdict : mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩ = stieltjesN A ζ :=
      PinsC2_mV_shift hA E (w := ⟨E', η⟩) hη0
    rw [hdict]
    exact ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_⟩
  · intro E' η hE' hgη hη10
    have hη0 : 0 < η := lt_of_lt_of_le hgpos hgη
    by_cases hη12 : η ≤ 1 / 2
    · obtain ⟨h1, h2⟩ := hmain E' η hE' hgη hη12
      exact ⟨by linarith, by linarith⟩
    · have hη12' : 1 / 2 < η := not_le.mp hη12
      obtain ⟨hl, -⟩ := hmain E' (1 / 2) hE' hg12 le_rfl
      have hmono := mV_eta_mul_im_mono
        (fun i => hA.eigenvalues i - E) E' (1 / 2) η (by norm_num) hη12'.le
      set S := (mV (fun i => hA.eigenvalues i - E) ⟨E', η⟩).im with hS
      have h4 : cb / 4 ≤ η * S := by nlinarith
      have hSpos : 0 < S := by
        by_contra hneg
        push Not at hneg
        nlinarith [mul_nonneg hη0.le (neg_nonneg.2 hneg)]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_le_mul_of_nonneg_right hη10 hSpos.le]
      · have hle := mV_im_le_inv (fun i => hA.eigenvalues i - E) E' η hη0
        have : 1 / η ≤ 2 := by
          rw [div_le_iff₀ hη0]; linarith
        linarith
  · intro i
    rw [hcard]
    have hlam := hnorm i
    have h1 : |hA.eigenvalues i - E| ≤ N ^ CV₀ + |E| := by
      calc |hA.eigenvalues i - E| ≤ |hA.eigenvalues i| + |E| := abs_sub _ _
        _ ≤ N ^ CV₀ + |E| := by linarith
    have hx1 : (1 : ℝ) ≤ N ^ CV₀ := Real.one_le_rpow hN1 hCV
    have hpow : N ^ (CV₀ + 1) = N ^ CV₀ * N := by rw [Real.rpow_add hN0, Real.rpow_one]
    rw [hpow]
    nlinarith [mul_le_mul_of_nonneg_right hx1 (by linarith [abs_nonneg E] : (0 : ℝ) ≤ N - 1)]

/-- The size conditions of the rate: `C₀ (ε + 2T) ≤ N^{-3τ_s/8}` for
`ε = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) + N^{-1+9τ_s/8} + Kb T`, `T = N^{-1+τ_s}`; the four exponent gaps `9τ_s/16`,
`τ_s/2`, `1 - 3τ_s/2`, `1 - 11τ_s/8` (positive iff `τ_s < 2/3`). -/
private theorem PinsC2_rate {N τs C₀ c₀ Kb : ℝ} (hN0 : 0 < N) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀) (hKb : 0 ≤ Kb)
    (h1 : N ^ (-(9 * τs / 16)) ≤ 1 / (5 * C₀)) (h2 : N ^ (-(τs / 2)) ≤ c₀ / (40 * C₀))
    (h3 : N ^ (-(1 - 3 * τs / 2)) ≤ 1 / (5 * C₀))
    (h4 : N ^ (-(1 - 11 * τs / 8)) ≤ 1 / (5 * C₀ * (Kb + 1))) :
    C₀ * ((N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        Kb * N ^ (-1 + τs) + N ^ (-1 + τs)) ≤ N ^ (-(3 * τs / 8)) := by
  have hX : 0 < N ^ (-(3 * τs / 8)) := Real.rpow_pos_of_pos hN0 _
  have eA : N ^ (-(15 * τs / 16)) = N ^ (-(9 * τs / 16)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eB : N ^ (-(7 * τs / 8)) = N ^ (-(τs / 2)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eC : N ^ (-1 + 9 * τs / 8) = N ^ (-(1 - 3 * τs / 2)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have eD : N ^ (-1 + τs) = N ^ (-(1 - 11 * τs / 8)) * N ^ (-(3 * τs / 8)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  set X := N ^ (-(3 * τs / 8)) with hXdef
  set p := N ^ (-(9 * τs / 16)) with hp
  set q := N ^ (-(τs / 2)) with hq
  set r := N ^ (-(1 - 3 * τs / 2)) with hr
  set r' := N ^ (-(1 - 11 * τs / 8)) with hr'
  rw [eA, eB, eC, eD]
  have q1 : p * (5 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h1
  have q2 : q * (40 * C₀) ≤ c₀ := (le_div_iff₀ (by positivity)).1 h2
  have q3 : r * (5 * C₀) ≤ 1 := (le_div_iff₀ (by positivity)).1 h3
  have q4 : r' * (5 * C₀ * (Kb + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).1 h4
  have hq2 : c₀⁻¹ * (q * (40 * C₀)) ≤ 1 := by
    calc c₀⁻¹ * (q * (40 * C₀)) ≤ c₀⁻¹ * c₀ := mul_le_mul_of_nonneg_left q2 (by positivity)
      _ = 1 := inv_mul_cancel₀ hc₀.ne'
  have hs : C₀ * p + 8 * C₀ * c₀⁻¹ * q + C₀ * r + C₀ * (Kb + 1) * r' ≤ 1 := by
    have e : 8 * C₀ * c₀⁻¹ * q = c₀⁻¹ * (q * (40 * C₀)) / 5 := by ring
    rw [e]
    nlinarith
  calc C₀ * ((p * X + 8 * c₀⁻¹ * (q * X)) + r * X + Kb * (r' * X) + r' * X)
      = X * (C₀ * p + 8 * C₀ * c₀⁻¹ * q + C₀ * r + C₀ * (Kb + 1) * r') := by ring
    _ ≤ X * 1 := mul_le_mul_of_nonneg_left hs hX.le
    _ = X := mul_one _


/-- **The deterministic half at one `n`**, C form (`Step1Good_at_n`, `Step1Good.lean:600`): all the size conditions
are hypotheses.  Regularity from `PinsC2_regular`; the free-convolution part from `freeConv_stable_lip` (`hFC`,
the three conjuncts used) with the strip closeness `PinsC2_strip` at `ε = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) +
N^{-1+9τ_s/8} + Kb T`, and `ρ₀ = ρ_n` by uniqueness of limits. -/
private theorem PinsC2_at_n {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (mr : ℂ → ℂ) (ρn : ℝ) {N T E δ τs cb K Lp C₀ c₀ c₁ CV₀ G : ℝ}
    (hδ : 0 < δ) (hcb : 0 < cb) (hK : 0 < K) (hLp : 0 < Lp) (hC₀ : 0 < C₀) (hc₀ : 0 < c₀)
    (hc₁ : c₁ ≤ δ / 4) (hτs : 0 < τs) (hCV : 0 ≤ CV₀)
    (hN : |E| + 2 ≤ N) (hcard : (Fintype.card ι : ℝ) = N) (hTN : T = N ^ (-1 + τs))
    (hTc : T ≤ c₀) (hT1 : T ≤ 1 / 2) (hET : |E| * T ≤ δ / 4) (hG : G ≤ δ)
    (hedge : N ^ (-1 + τs / 8) ≤ c₀ / 8 * T)
    (hXc : N ^ (-(3 * τs / 8)) ≤ C₀ * c₀)
    (herr : N ^ (-(15 * τs / 16)) + N ^ (-(τs / 8)) + N ^ (-1 + 9 * τs / 8) ≤ cb / 2)
    (hrate : C₀ * ((N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
        (K + Lp * (|E| + δ + 1)) * T + T) ≤ N ^ (-(3 * τs / 8)))
    (hbox : ∀ z : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 → cb ≤ (mr z).im ∧ ‖mr z‖ ≤ K)
    (hlip : ∀ z z' : ℂ, |z.re - E| ≤ δ → 0 < z.im → z.im ≤ 1 →
      |z'.re - E| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mr z - mr z'‖ ≤ Lp * ‖z - z'‖)
    (hρn : Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρn))
    (hFC : ∀ (v : ι → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε → ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mr ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (mr ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (ε + t))
    (hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → N ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN A ζ - mr ζ‖ ≤ N ^ (-(15 * τs / 16)) + N ^ (τs / 8) * (N * ζ.im)⁻¹ + N ^ (-1 + 9 * τs / 8))
    (hnorm : ∀ i, |hA.eigenvalues i| ≤ N ^ CV₀) :
    IsRegular32 (fun i => hA.eigenvalues i - E) (N ^ (-1 + τs / 4)) G
        (cb / 40) (2 * K + cb + 2) (CV₀ + 1) ∧
      ∃ mfc : ℂ → ℂ, IsFreeConv32 (fun i => hA.eigenvalues i - E) (1 - Real.exp (-T)) mfc ∧
        ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
          |ρ' - ρn| ≤ N ^ (-(3 * τs / 8)) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < N := by linarith
  have hTpos : 0 < T := by rw [hTN]; exact Real.rpow_pos_of_pos hN0 _
  refine ⟨PinsC2_regular hA mr hN hcard hcb hK hδ hτs hTN hT1 hG hbox hpt herr hnorm hCV, ?_⟩
  have ht : 0 < 1 - Real.exp (-T) := PinsC2_one_sub_exp_pos hTpos
  have htT : 1 - Real.exp (-T) ≤ T := PinsC2_one_sub_exp_le T
  set ε : ℝ := (N ^ (-(15 * τs / 16)) + 8 * c₀⁻¹ * N ^ (-(7 * τs / 8))) + N ^ (-1 + 9 * τs / 8) +
    (K + Lp * (|E| + δ + 1)) * T with hεdef
  have hε0 : 0 ≤ ε := by positivity
  have hεc : ε ≤ c₀ := by
    have h1 : C₀ * ε ≤ C₀ * c₀ := by
      refine le_trans ?_ (hrate.trans hXc)
      have : C₀ * ε ≤ C₀ * (ε + T) := mul_le_mul_of_nonneg_left (by linarith) hC₀.le
      exact this
    exact le_of_mul_le_mul_left h1 hC₀
  have hK0 : 0 ≤ K := hK.le
  have hLp0 : 0 ≤ Lp := hLp.le
  obtain ⟨ρ, ρ₀, h1, h2, h3⟩ := hFC (fun i => hA.eigenvalues i - E)
    (Real.exp (-T)) (1 - Real.exp (-T)) ε
    ht (htT.trans hTc) (by ring) hε0 hεc
    (fun w hw hlow hw1 => PinsC2_strip hA mr hN1 hc₀ hδ hc₁ hK0 hLp0 hTN hT1 hET hedge
      (fun z hz hz1 hz2 => (hbox z hz hz1 hz2).2) hlip hpt hw hlow hw1)
  have hρ : ρ₀ = ρn := tendsto_nhds_unique h2 hρn
  refine ⟨freeConvST (fun i => hA.eigenvalues i - E) (1 - Real.exp (-T)),
    isFreeConv51_freeConvST _ ht.le, ρ, h1, ?_⟩
  rw [← hρ]
  refine h3.trans (le_trans ?_ hrate)
  exact mul_le_mul_of_nonneg_left (by linarith) hC₀.le


set_option maxHeartbeats 1000000 in
-- the deterministic half (a port of `step1Good'_det`) has 16 eventual conditions in one proof
/-- **`step1GoodC''_det`**: eventually in `n`, every `ω` on which the `UNTrLocalInit'` local law holds at heights
`≥ N^{-1+τ_s/8}` (at `τ = τ_s/8`) and all eigenvalues of `H` are `≤ N^{CV₀}` has the good event of `UNStep1GoodC''`.
Target 4 (`freeConv_stable_lip`) at `mref = m n`, `E₀ = E`, `A = |E|`, `v = vOUC`, `s = e^{-t*}`, `t = 1 - e^{-t*}`;
strip closeness through `mV_vOUC` and the Lipschitz bridge `‖m ζ - a⁻¹ m (a⁻¹ ζ)‖ ≤ t* (K + Lp (|E| + δ + 1))`;
`ε_n = (N^{-15τ_s/16} + 8 c₀⁻¹ N^{-7τ_s/8}) + N^{-1+9τ_s/8} + (K + Lp (|E| + δ + 1)) N^{-1+τ_s}`; (2.3) by
`un_eigenvalues_abs_le_convex` with `UNMeanBound`; `ρ₀ = ρ n` by uniqueness of limits.  Constants `c C` before
`∀ᶠ n` (`c = c_box/40`, `C = 2K + c_box + 2`). -/
theorem step1GoodC''_det :
    ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ (M : UNModelC sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ),
        UNDens' m E ρ δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNMeanBound sz M CV₀ →
        ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 →
          ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz,
            (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ z.im → z.im ≤ 1 →
              ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖ ≤
                ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n)) →
            (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀) →
            (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                  (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8))) := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV hMean τs hτs0 hτs1 hτs𝔠𝔡
  obtain ⟨hδ, c', C', Lp', hc', hC', hLp', hUev⟩ := hD.1
  obtain ⟨cb, K, Lp, hcb, hK, hLp, hbev⟩ := hD.2
  obtain ⟨c₀, c₁, C₀, hc₀, hc₀c₁, hc₁δ, hC₀, hFC⟩ :=
    freeConv_stable_lip cb K Lp δ |E| hcb hK hLp hδ (abs_nonneg E)
  have hd0 : 0 < d := by omega
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  have hcd := un_admissible_cd_lt_half sz hd0 hA
  have h𝔠1 : 𝔠 < 1 := by
    have h1 := un_admissible_c_mul_lt_one sz hd0 hA
    have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    nlinarith
  have hτs23 : τs < 2 / 3 := by linarith
  have hσ0 : 0 < min (τs / 4) ((1 - τs) / 3) := lt_min (by linarith) (by linarith)
  set Kb : ℝ := K + Lp * (|E| + δ + 1) with hKbdef
  have hKb : 0 ≤ Kb := by positivity
  refine ⟨cb / 40, 2 * K + cb + 2, by positivity, ?_⟩
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  have hc₁4 : c₁ ≤ δ / 4 := by
    refine hc₁δ.trans ?_
    exact div_le_div_of_nonneg_left hδ.le (by norm_num) (by nlinarith [abs_nonneg E])
  filter_upwards [hbev, hUev, hA.2.2.2.1, hA.2.2.2.2, hNtend.eventually_ge_atTop (|E| + 2), hMean,
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + τs) (c := min c₀ (1 / 2)) (by linarith)
      (lt_min hc₀ (by norm_num))),
    hNtend.eventually (PinsC2_rpow_ev (e := -(min (τs / 4) ((1 - τs) / 3))) (c := δ / 4)
      (by linarith) (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(7 * τs / 8)) (c := c₀ / 8) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(15 * τs / 16)) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(τs / 8)) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + 9 * τs / 8) (c := cb / 6) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(9 * τs / 16)) (c := 1 / (5 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(τs / 2)) (c := c₀ / (40 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(1 - 3 * τs / 2)) (c := 1 / (5 * C₀)) (by linarith)
      (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(1 - 11 * τs / 8)) (c := 1 / (5 * C₀ * (Kb + 1)))
      (by linarith) (by positivity)),
    hNtend.eventually (PinsC2_rpow_ev (e := -(3 * τs / 8)) (c := C₀ * c₀) (by linarith)
      (by positivity))] with
    n hbn hUn hB hWO hNE hMn eT eG eedge e15 e18 e19 e9 e12 er er' eX
  intro ω hLL hnorm
  have : Nonempty (Idx d (sz.L n) (sz.W n)) := ⟨fun _ => 0⟩
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by linarith [abs_nonneg E]
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  have hTpos : 0 < ouTStar sz τs n := Real.rpow_pos_of_pos hN0 _
  have hTc : ouTStar sz τs n ≤ c₀ := eT.trans (min_le_left _ _)
  have hT1 : ouTStar sz τs n ≤ 1 / 2 := eT.trans (min_le_right _ _)
  have hET : |E| * ouTStar sz τs n ≤ δ / 4 := by
    have h1 : ouTStar sz τs n ≤ δ / (4 * (1 + |E|)) := hTc.trans (hc₀c₁.trans hc₁δ)
    calc |E| * ouTStar sz τs n ≤ |E| * (δ / (4 * (1 + |E|))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg E)
      _ ≤ δ / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [abs_nonneg E]
  have hedge : Nsz sz n ^ (-1 + τs / 8) ≤ c₀ / 8 * ouTStar sz τs n := by
    have hsplit : Nsz sz n ^ (-1 + τs / 8) =
        Nsz sz n ^ (-(7 * τs / 8)) * Nsz sz n ^ (-1 + τs) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right eedge (Real.rpow_nonneg hN0.le _)
  have hpt : ∀ ζ : ℂ, |ζ.re - E| ≤ δ → Nsz sz n ^ (-1 + τs / 8) ≤ ζ.im → ζ.im ≤ 1 →
      ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) ζ - m n ζ‖ ≤
        Nsz sz n ^ (-(15 * τs / 16)) + Nsz sz n ^ (τs / 8) * (Nsz sz n * ζ.im)⁻¹ +
          Nsz sz n ^ (-1 + 9 * τs / 8) := by
    intro ζ h1 h2 h3
    have hpos : 0 < ζ.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) h2
    refine (hLL ζ h1 h2 h3).trans ?_
    rw [mul_add]
    have hb := PinsC2_bctl sz n hd0 h𝔠 h𝔠1 h𝔡 hτs0 hτs𝔠𝔡 hN1 hB hWO.1 hpos
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hWN : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) ≤ Nsz sz n ^ (τs / 8) :=
      Real.rpow_le_rpow hW0.le (PinsC2_W_le_size sz hd0 n) (by linarith)
    have hWT : ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * ouTStar sz τs n ≤ Nsz sz n ^ (τs / 8) * Nsz sz n ^ (-1 + τs) :=
      mul_le_mul hWN le_rfl hTpos.le (Real.rpow_nonneg hN0.le _)
    have hsplit : Nsz sz n ^ (τs / 8) * Nsz sz n ^ (-1 + τs) = Nsz sz n ^ (-1 + 9 * τs / 8) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    linarith
  have hnormA : ∀ i, |(ouInit_isHermitian M n (ouTStar sz τs n) ω).eigenvalues i| ≤ Nsz sz n ^ CV₀ := by
    have ha0 : 0 ≤ Real.exp (-(ouTStar sz τs n) / 2) := (Real.exp_pos _).le
    have ha1 : Real.exp (-(ouTStar sz τs n) / 2) ≤ 1 := PinsC2_exp_le_one hTpos.le
    refine un_eigenvalues_abs_le_convex (M.herm n ω) (M.mean_herm n)
      (ouInit_isHermitian M n (ouTStar sz τs n) ω) ha0 ha1 ?_ hnorm hMn
    unfold ouInit
    module
  have hrate := PinsC2_rate (τs := τs) hN0 hC₀ hc₀ hKb e9 e12 er er'
  have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = Nsz sz n := by
    exact_mod_cast sz.card_Idx n
  have hFC' : ∀ (v : Idx d (sz.L n) (sz.W n) → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε →
      ε ≤ c₀ →
      (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
        ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * m n ((Real.sqrt s : ℂ)⁻¹ * (w + E))‖ ≤ ε) →
      ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
        Tendsto (fun η : ℝ => (m n ⟨E, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
          |ρ - ρ₀| ≤ C₀ * (ε + t) := by
    intro v s t ε h1 h2 h3 h4 h5 h6
    obtain ⟨ρ, ρ₀, a, b, c, -⟩ := hFC (m n) E le_rfl hbn.1 hbn.2 v s t ε h1 h2 h3 h4 h5 h6
    exact ⟨ρ, ρ₀, a, b, c⟩
  exact PinsC2_at_n (ouInit_isHermitian M n (ouTStar sz τs n) ω) (m n) (ρ n) hδ hcb hK hLp hC₀ hc₀ hc₁4 hτs0
    hCV hNE hcard rfl hTc hT1 hET (by linarith) hedge eX (by linarith) hrate hbn.1 hbn.2 hUn.2.2 hFC' hpt hnormA

/-- **`step1GoodC''`**: **the pin `UNStep1GoodC''`**, from `step1GoodC''_det`, `UNTrLocalInit'` at
`(τ_s, τ_s/8, τ_s/8, D + 1)` and `UNNormBound` at `D + 1` (two bad events, `2 N^{-D-1} ≤ N^{-D}` for `N ≥ 2`;
`UNMeanBound` is deterministic). -/
theorem step1GoodC'' : UNStep1GoodC'' := by
  intro d hd 𝔠 𝔡 sz hA M m E ρ δ hD hT CV₀ hCV hN hMean τs D hτs0 hτs1 hτs𝔠𝔡 hD0
  obtain ⟨c, C, hc, hdet⟩ := step1GoodC''_det d hd 𝔠 𝔡 sz hA M m E ρ δ hD CV₀ hCV hMean τs hτs0 hτs1 hτs𝔠𝔡
  refine ⟨c, C, hc, ?_⟩
  have hT1 := hT τs hτs0 hτs1 (τs / 8) (τs / 8) (D + 1) (by positivity) (by positivity) (by linarith)
  have hN1 := hN (D + 1) (by linarith)
  filter_upwards [hdet, hT1, hN1, (hA.2.2.1 : Tendsto (fun n => Nsz sz n) atTop atTop).eventually_ge_atTop 2]
    with n hdn hTn hNn hN2
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith
  set A : Set (Sizes.SeqΩ sz) := {ω | ∃ z : ℂ, |z.re - E| ≤ δ ∧ Nsz sz n ^ (-1 + τs / 8) ≤ z.im ∧
    z.im ≤ 1 ∧ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * (sz.Bctl n (1 - z.im) + ouTStar sz τs n) <
      ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} with hAdef
  set B : Set (Sizes.SeqΩ sz) := {ω | ∃ i, Nsz sz n ^ CV₀ < |(M.herm n ω).eigenvalues i|} with hBdef
  have hsub : {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
                (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧
              ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
                ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                  |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))} ⊆ A ∪ B := by
    intro ω hω
    by_contra hnot
    simp only [hAdef, hBdef, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and,
      not_lt] at hnot
    obtain ⟨h1, h2⟩ := hnot
    exact hω (hdn ω (fun z hz1 hz2 hz3 => h1 z hz1 hz2 hz3) (fun i => h2 i))
  calc M.μ _ ≤ M.μ (A ∪ B) := measure_mono hsub
    _ ≤ M.μ A + M.μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) + ENNReal.ofReal (Nsz sz n ^ (-(D + 1))) :=
        add_le_add hTn hNn
    _ = ENNReal.ofReal (Nsz sz n ^ (-(D + 1)) + Nsz sz n ^ (-(D + 1))) :=
        (ENNReal.ofReal_add (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _)).symm
    _ ≤ ENNReal.ofReal (Nsz sz n ^ (-D)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e : Nsz sz n ^ (-(D + 1)) = Nsz sz n ^ (-D) * (Nsz sz n)⁻¹ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
        have hinv : (Nsz sz n)⁻¹ ≤ 1 / 2 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) hN2
        have hpos : 0 ≤ Nsz sz n ^ (-D) := Real.rpow_nonneg hN0.le _
        rw [e]
        nlinarith


/-! ## 8. Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

The data: `RBM.Gauss.SizesInst.sz0` (`d = 3`; `n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`),
`𝔠 = 1/6`, `𝔡 = 1/10`, the band model (mean `0`, `.toC`), `m = msc`, `E = 0`, `ρ = rhoSC 0`, `δ' = 1/2`,
`δ = 1/4` (`UNDens'.mono` of `un_dens'_msc_zero`, `UNTrLocal.mono`), `τ_s = 1/60 = 𝔠𝔡`, `D = 1`, `k = 1`, `E' = 0`,
`𝒪 = bump`.  The band rows `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow` and the pins `UNL32`, `UNGUELocal`,
`UNGreenCorrAllC`, `UNClaimAllC`, `UNCoreC''` are other gates' pins and stay hypotheses; every deterministic
hypothesis (`Admissible`, `UNDens'`, `UNTrLocalInit'`, `UNMeanBound`, `|0| < 2`, `1 ≤ 1`, `IsTestFun bump`) is
discharged.  The conclusions of `step1GoodC''` are eventual in `n` (the size conditions hold only for
`N ≳ e^{2.3 · 10^3}` at these constants: the instances do not use a concrete `n`; DECISIONS §56). -/

namespace PinsC2Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- The deterministic diagonal centred model `H = mean = diag γ_n` under the law `Sizes.seqP sz`. -/
def diagModel {d : ℕ} (sz : Sizes d) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ) : UNModelC sz where
  μ := Sizes.seqP sz
  prob := inferInstance
  H := fun n _ => Matrix.diagonal (fun i => (γ n i : ℂ))
  herm := fun n _ => PinsC2_diag_herm (γ n)
  meas := fun n i j => measurable_const
  mean := fun n => Matrix.diagonal (fun i => (γ n i : ℂ))
  mean_herm := fun n => PinsC2_diag_herm (γ n)

/-- `inst_diag_model`: a deterministic diagonal centred model `H = mean = diag γ_n` exists for every `sz`, `γ`
(law `Sizes.seqP sz`, `diagModel`): the structural hypotheses of `not_UNStep1GoodC'_of_diag` are satisfiable. -/
theorem inst_diag_model :
    ∀ {d : ℕ} (sz : Sizes d) (γ : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → ℝ),
      ∃ M : UNModelC sz, (∀ n ω, M.H n ω = Matrix.diagonal (fun i => (γ n i : ℂ))) ∧
        ∀ n, M.mean n = Matrix.diagonal (fun i => (γ n i : ℂ)) := by
  intro d sz γ
  exact ⟨diagModel sz γ, fun _ _ => rfl, fun _ => rfl⟩

/-- Instance of `not_UNStep1GoodC'_of_diag` at `sz0`, `𝔠 = 1/6`, `𝔡 = 1/10`, the diagonal model `diagModel sz0 γ`
(structural hypotheses by `inst_diag_model`), `m = msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/4`, `CV₀ = 1`: `UNDens'` is
discharged (`UNDens'.mono`, `un_dens'_msc_zero`); `UNStep1GoodC'` is the pin refuted here; `UNTrLocalInit` and
`UNNormBound` of the diagonal model stay hypotheses: for the semicircle-quantile `γ` of preflight (vi) they hold
(argued, not compiled), for an arbitrary `γ` they need not. -/
theorem inst_not_UNStep1GoodC'_diag (hS : UNStep1GoodC')
    (γ : ∀ n : ℕ, Idx 3 (sz0.L n) (sz0.W n) → ℝ)
    (hTi : UNTrLocalInit sz0 (diagModel sz0 γ) (fun _ => msc) 0 (1 / 4))
    (hN : UNNormBound sz0 (diagModel sz0 γ).toUNModel 1) : False :=
  not_UNStep1GoodC'_of_diag hS 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (diagModel sz0 γ) γ (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 4)
    (UNDens'.mono (by norm_num) (by norm_num) un_dens'_msc_zero) hTi 1 zero_le_one hN

/-- `inst_unTrLocalInit'_band`: `unTrLocalInit'_band_zero` at `sz0` with the band local law from the row
`UNTrLocalBandRow` at `κ = 1`, `E = 0`, `δ = 1/2`; `UNLocAvgBand` and the row stay hypotheses. -/
theorem inst_unTrLocalInit'_band :
    UNLocAvgBand → UNTrLocalBandRow →
      UNTrLocalInit' sz0 (UNModel.band sz0).toC (fun _ => msc) 0 (1 / 4) := by
  intro hLoc rT
  exact unTrLocalInit'_band_zero sz0 sz0_adm
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))

/-- `inst_step1GoodC''_band`: `step1GoodC''` at `sz0`, `(UNModel.band sz0).toC`, `msc`, `E = 0`, `ρ = rhoSC 0`,
`δ = 1/4` (`UNDens'.mono` of `un_dens'_msc_zero`), `UNTrLocalInit'` from `inst_unTrLocalInit'_band`, the norm bound
from `UNNormBandRow`, `UNMeanBound` from `unMeanBound_toC`, `τ_s = 1/60`, `D = 1`. -/
theorem inst_step1GoodC''_band :
    UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
        (UNModel.band sz0).toC.μ {ω | ¬ (IsRegular32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω)
              (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
              (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (CV₀ + 1) ∧
            ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω)
                (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
              ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
                |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤
          ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ))) := by
  intro hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  refine ⟨CV₀, hCV, ?_⟩
  exact step1GoodC'' 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 4) (UNDens'.mono (by norm_num) (by norm_num) un_dens'_msc_zero)
    (inst_unTrLocalInit'_band hLoc rT) CV₀ hCV hN (unMeanBound_toC sz0 (UNModel.band sz0) CV₀)
    (1 / 60) 1 (by norm_num) (by norm_num) (by norm_num) one_pos

/-- `inst_step1GoodC''_det_band`: `step1GoodC''_det` at the same data (`CV₀ = 1`); the event hypotheses on `ω`
stay hypotheses (they hold only for `N ≳ e^{2.3 · 10^3}` at these constants). -/
theorem inst_step1GoodC''_det_band :
    ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz0,
      (∀ z : ℂ, |z.re - 0| ≤ 1 / 4 → Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 8) ≤ z.im → z.im ≤ 1 →
        ‖stieltjesN (ouInit (UNModel.band sz0).toC n (ouTStar sz0 (1 / 60) n) ω) z - msc z‖ ≤
          ((sz0.W n : ℕ) : ℝ) ^ ((1 / 60 : ℝ) / 8) * (sz0.Bctl n (1 - z.im) + ouTStar sz0 (1 / 60) n)) →
      (∀ i, |((UNModel.band sz0).herm n ω).eigenvalues i| ≤ Nsz sz0 n ^ (1 : ℝ)) →
      (IsRegular32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4))
            (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (1 + 1) ∧
        ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz0 (UNModel.band sz0).toC n (1 / 60) 0 ω)
            (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧
          ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧
            |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8))) :=
  step1GoodC''_det 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 4) (UNDens'.mono (by norm_num) (by norm_num) un_dens'_msc_zero) 1 zero_le_one
    (unMeanBound_toC sz0 (UNModel.band sz0) 1) (1 / 60) (by norm_num) (by norm_num) (by norm_num)

/-- `inst_coreC_band''` (replaces the vacuous `UNKInst.inst_coreC_band`, `UNDensInst.inst_coreC_band'`):
`UNCoreC''` at `(UNModel.band sz0).toC`, `msc`, `E = 0`, `ρ = ρ_sc(0)`, `δ = 1/4`, `E' = 0`, `k = 1`, `𝒪 = bump`;
discharged: `UNDens'` (`UNDens'.mono`, `un_dens'_msc_zero`), `UNTrLocal` at `1/4` (`UNTrLocal.mono`),
`UNTrLocalInit'` (`unTrLocalInit'_band_zero`), `UNMeanBound` (`unMeanBound_toC`); kept: `UNL32`, `UNGUELocal`,
`UNGreenCorrAllC`, the band local law at `1/2`, the norm bound, `UNClaimAllC` (preflight (iii): numbers for each). -/
theorem inst_coreC_band'' :
    UNCoreC'' → UNL32 → UNGUELocal → UNGreenCorrAllC →
      UNTrLocal sz0 (UNModel.band sz0) (fun _ => msc) 0 (1 / 2) →
      (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀) →
      UNClaimAllC sz0 (UNModel.band sz0).toC 0 →
        UNUnivDilAt sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) := by
  intro hcore h32 hGL hGC hT hN hC
  obtain ⟨CV₀, hCV, hN'⟩ := hN
  exact hcore h32 hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0).toC (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 4) (UNDens'.mono (by norm_num) (by norm_num) un_dens'_msc_zero)
    (UNTrLocal.mono (by norm_num) hT) (unTrLocalInit'_band_zero sz0 sz0_adm hT)
    ⟨CV₀, hCV, hN', unMeanBound_toC sz0 (UNModel.band sz0) CV₀⟩ hC 0 (by norm_num) 1 le_rfl bump bump_testFun

/-! ### Instances of the matrix facts and the dictionary (all hypotheses discharged) -/

/-- An eigenvalue of a real diagonal matrix is one of its diagonal entries. -/
private theorem PinsC2_eig_diag_entry {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ)
    (hA : (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian) (i : ι) : ∃ j, hA.eigenvalues i = u j := by
  have hmem := hA.eigenvalues_mem_spectrum_real i
  rw [spectrum.mem_iff] at hmem
  by_contra hno
  push Not at hno
  apply hmem
  have e : (algebraMap ℝ (Matrix ι ι ℂ)) (hA.eigenvalues i) - Matrix.diagonal (fun j => (u j : ℂ)) =
      Matrix.diagonal (fun j => ((hA.eigenvalues i : ℂ) - u j)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  rw [e, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro j
  refine isUnit_iff_ne_zero.2 fun h => hno j ?_
  have := sub_eq_zero.1 h
  exact_mod_cast this

private theorem PinsC2_eig_diag_abs {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → ℝ) {R : ℝ}
    (hu : ∀ j, |u j| ≤ R) (hA : (Matrix.diagonal (fun i => (u i : ℂ))).IsHermitian) :
    ∀ i, |hA.eigenvalues i| ≤ R := by
  intro i
  obtain ⟨j, hj⟩ := PinsC2_eig_diag_entry u hA i
  rw [hj]; exact hu j

private theorem PinsC2_diag_convex {ι : Type} [DecidableEq ι] (u v : ι → ℝ) (a : ℝ) :
    Matrix.diagonal (fun i => ((a * u i + (1 - a) * v i : ℝ) : ℂ)) =
      a • Matrix.diagonal (fun i => (u i : ℂ)) + (1 - a) • Matrix.diagonal (fun i => (v i : ℂ)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Complex.real_smul]
  · simp [hij]

/-- Instance of `un_eigenvalues_abs_le_convex`: `ι = Fin 3`, `A = diag (2, -1, 1/2)`, `B = diag (-1, 1, 0)`,
`a = 1/3`, `R = 2`; `C = a A + (1 - a) B` is diagonal. -/
theorem inst_un_eigenvalues_abs_le_convex :
    ∀ i, |(PinsC2_diag_herm (fun j : Fin 3 =>
        (1 / 3 : ℝ) * (![2, -1, 1 / 2] : Fin 3 → ℝ) j + (1 - 1 / 3) * (![-1, 1, 0] : Fin 3 → ℝ) j)).eigenvalues i| ≤ 2 :=
  un_eigenvalues_abs_le_convex (PinsC2_diag_herm (![2, -1, 1 / 2] : Fin 3 → ℝ))
    (PinsC2_diag_herm (![-1, 1, 0] : Fin 3 → ℝ)) (PinsC2_diag_herm _) (a := 1 / 3) (R := 2) (by norm_num)
    (by norm_num) (PinsC2_diag_convex _ _ _)
    (PinsC2_eig_diag_abs _ (fun j => by fin_cases j <;> norm_num) _)
    (PinsC2_eig_diag_abs _ (fun j => by fin_cases j <;> norm_num) _)

/-- Instance of `un_exists_eigenvalues_eq_diagonal`: `diag (1, 2, 3)`, the entry `2`. -/
theorem inst_un_exists_eigenvalues_eq_diagonal :
    ∃ i, (PinsC2_diag_herm (![1, 2, 3] : Fin 3 → ℝ)).eigenvalues i = 2 :=
  un_exists_eigenvalues_eq_diagonal (![1, 2, 3] : Fin 3 → ℝ) (PinsC2_diag_herm _) 1

/-- Instance of `stieltjesN_diagonal`: `diag (1, 2, 3)` at `z = i`. -/
theorem inst_stieltjesN_diagonal :
    stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) (⟨0, 1⟩ : ℂ) =
      mV (![1, 2, 3] : Fin 3 → ℝ) (⟨0, 1⟩ : ℂ) :=
  stieltjesN_diagonal (![1, 2, 3] : Fin 3 → ℝ) (by simp)

/-- Instance of `stieltjesN_vert_le`: `H = diag (1, 2, 3)`, `x = 0`, `y = 1`, `y' = 2`. -/
theorem inst_stieltjesN_vert_le :
    ‖stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) ⟨0, 1⟩ -
        stieltjesN (Matrix.diagonal (fun i => ((![1, 2, 3] : Fin 3 → ℝ) i : ℂ))) ⟨0, 2⟩‖ ≤ |1 - 2| / (1 * 2) :=
  stieltjesN_vert_le (PinsC2_diag_herm (![1, 2, 3] : Fin 3 → ℝ)) 0 1 2 one_pos two_pos

/-- Instance of `mV_vOUC` at `sz0`, the band model, `τ_s = 1/60`, `E = 0`, any `ω`, `w = i`. -/
theorem inst_mV_vOUC (ω : Sizes.SeqΩ sz0) :
    mV (vOUC sz0 (UNModel.band sz0).toC 0 (1 / 60) 0 ω) (⟨0, 1⟩ : ℂ) =
      stieltjesN (ouInit (UNModel.band sz0).toC 0 (ouTStar sz0 (1 / 60) 0) ω) ((⟨0, 1⟩ : ℂ) + (0 : ℝ)) :=
  mV_vOUC sz0 (UNModel.band sz0).toC 0 (1 / 60) 0 ω (w := ⟨0, 1⟩) one_pos

/-- Instance of `stieltjesN_ouInit_toC` at `sz0`, the band model, `t = t*`, any `ω`, `z = i`. -/
theorem inst_stieltjesN_ouInit_toC (ω : Sizes.SeqΩ sz0) :
    stieltjesN (ouInit (UNModel.band sz0).toC 0 (ouTStar sz0 (1 / 60) 0) ω) (⟨0, 1⟩ : ℂ) =
      ((Real.exp (-(ouTStar sz0 (1 / 60) 0) / 2) : ℝ) : ℂ)⁻¹ *
        stieltjesN ((UNModel.band sz0).H 0 ω)
          (((Real.exp (-(ouTStar sz0 (1 / 60) 0) / 2) : ℝ) : ℂ)⁻¹ * (⟨0, 1⟩ : ℂ)) :=
  stieltjesN_ouInit_toC sz0 (UNModel.band sz0) 0 (ouTStar sz0 (1 / 60) 0) ω (z := ⟨0, 1⟩) one_pos

end PinsC2Inst

end RBM.Univ

end
