/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Prop6Path
import RBM3D.BA.KBase
import RBM3D.BA.KKernel
import RBM3D.BA.GreenSchur
import RBM3D.Evolution.Pins

/-!
# Stage E of the block Anderson model (BA-E1)

The evolution kernel, the five stage-E pins, `lem:sum_Ndecay` and the `Ξ` bounds at BA.

Ticket T2388.  Paper: `A_deterministic_estimates.tex:85-160` (`(eq:decompUalt)`, `(Xi_infint)`,
`(eq:decayXi)`), `3_5_Loop_Hierarchy.tex:1600-1680`; design `docs/reports/T2378-design.md` §2-§3,
probe `t/T2378:RBM3D/Probe/T2378Pins.lean:180-370`.

1. Vocabulary: `BAuKer` (`(1 - s M^{(σ₁σ₂)}) Θ_t^{(σ₁σ₂)}`, `3_5:116`), `BAUN` (`(def_Ustz)`),
   `BAXi` (`Ξ = (t - s) M Θ_t`), and the identities `BAuKer_eq_one_add` (`(eq:decompUalt)`) and
   `BAuKer_convex`.
2. The five stage-E pins `BAEKSumNdecay`, `BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2`,
   `BAEKSumDecayNonzero`: the shape of `Evolution/Pins.lean:64-140` with `BAReal d L g κ E m` in
   place of `‖m‖ = 1` and no propagator antecedent (`baProp5to8_holds`).
3. `baEKSumNdecay_holds`: `‖Ξ‖_{∞→∞} ≤ (t - s)/(1 - t)` from the Ward row sums
   (`BAMss_norm_eq_BAK`, `BAK_row_sum`), then the product over the `n` factors.
4. The BA `Ξ` pins `BAEKXiDecay`, `BAEKXiBall`, `BAEKSameRow` and their proofs, from
   `BAuKer_convex`, `baProp5_holds` and `baProp5s_holds` (no `Mbound_AO`).
5. Compiled nonempty instances at `d = 3`, the flow datum `n = 0` of `sz0`.

Private helpers carry the stem `EKPins_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

noncomputable section

open RBM

namespace RBM.BA

/-! ## 1. Vocabulary -/

/-- The one-index kernel `(1 - s M^{(σ₁σ₂)}) Θ_t^{(σ₁σ₂)}` (`3_5:116`). -/
def BAuKer (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - (s : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * BATheta d L g E m t σ₁ σ₂

/-- The evolution kernel `U^{(n)}_{s,t,σ}` of `(def_Ustz)`, cyclic `σ_{n+1} = σ₁`. -/
def BAUN (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) {n : ℕ} (σ : Fin n → Bool) (s t : ℝ)
    (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b : Fin n → Zd d L, (∏ i, BAuKer d L g E m s t (σ i) (σ (finRotate n i)) (a i) (b i)) * A b

/-- `Ξ = (t - s) M^{(σ₁σ₂)} Θ_t^{(σ₁σ₂)}` of `(eq:decompUalt)` (`A:98`). -/
def BAXi (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((t : ℂ) - s) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂)

/-- `(eq:decompUalt)` for the block Anderson kernel, `Ξ = (t - s) M Θ_t` (`A:98-100`): from `Θ = 1 + t M Θ`. -/
theorem BAuKer_eq_one_add {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m s t σ₁ σ₂ = 1 + ((t : ℂ) - s) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
      BATheta d L g E m t σ₁ σ₂) := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
  unfold BAuKer
  rw [sub_mul, one_mul, smul_mul_assoc]
  linear_combination (norm := module) h

/-- `(eq:decompUalt)` in the notation of `BAXi`: `uKer = 1 + Ξ`. -/
theorem BAuKer_eq_one_add_Xi {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m s t σ₁ σ₂ = 1 + BAXi d L g E m s t σ₁ σ₂ :=
  BAuKer_eq_one_add hr ht0 ht1 σ₁ σ₂

/-- For `t > 0`: `(1 - sM)(1 - tM)⁻¹ = (s/t) 1 + (1 - s/t) Θ_t`, so `Ξ_{ab} = ((t-s)/t) Θ_{t,ab}` for `a ≠ b` and the decay
`(eq:decayXi)` of `Ξ` is that of `Θ` (`BAProp5`): `Mbound_AO` is not needed. -/
theorem BAuKer_convex {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BAuKer d L g E m s t σ₁ σ₂ = ((s : ℂ) / t) • (1 : Matrix (Zd d L) (Zd d L) ℂ) +
      (1 - (s : ℂ) / t) • BATheta d L g E m t σ₁ σ₂ := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0.le ht1 σ₁ σ₂).1
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hX : BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂ =
      ((t : ℂ)⁻¹) • (BATheta d L g E m t σ₁ σ₂ - 1) := by
    have h' : BATheta d L g E m t σ₁ σ₂ - 1 = (t : ℂ) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
        BATheta d L g E m t σ₁ σ₂) := sub_eq_of_eq_add' h
    rw [h', smul_smul, inv_mul_cancel₀ htc, one_smul]
  rw [BAuKer_eq_one_add hr ht0.le ht1, hX]
  match_scalars <;> field_simp <;> ring

/-! ## 2. The five stage-E pins (shape of `Evolution/Pins.lean:64-140`, `BAReal d L g κ E m` for `‖m‖ = 1`) -/

/-- `lem:sum_Ndecay` (`3_5:1620`): `‖U^{(n)}_{s,t,σ} ∘ 𝒜‖_∞ ≤ ((1-s)/(1-t))^n ‖𝒜‖_∞`; the proof is Ward row sums
(`BAK_row_sum`) and `|M^{(σσ')}_{ab}| = BAK_{ab}` (`BAMss_norm_eq_BAK`, `BA/KKernel.lean:102`). -/
def BAEKSumNdecay (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ A : (Fin n → Zd d L) → ℂ,
      ‖BAUN d L g E m σ s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖

/-- `(sum_res_1)`, any `σ` (`3_5:1639`). -/
def BAEKSumDecay1 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A →
          ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * (ellT L g t ^ 2 / ellT L g s ^ 2) *
            ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-- `(sum_res_2_NAL)`: non-alternating `σ` (`3_5:1649`). -/
def BAEKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) → ∀ A : (Fin n → Zd d L) → ℂ,
          EKFastDecay g s W ε D A → ‖BAUN d L g E m σ s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)

/-- `(sumAzero) ⟹ (sum_res_2)` (`3_5:1659`); `log L ≤ W^ε` is the `d = 3` absorption of `(eq:latticesum_d3)`
(`A:194-198`), `L^d ≤ W^K` is `(Main_DEL_COND)`. -/
def BAEKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      Real.log L ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → EKSumZero A →
          ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-- `lem:sum_decay_nonzero` (`3_5:1666`), case (ii) `1 - g²/L² ≤ s ≤ t < 1`, `A ⊇ I_diff(σ)`. -/
def BAEKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) →
          ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L A (BAUN d L g E m σ s t 𝒜)‖ ≤ C * ‖𝒜‖

/-! ## 3. `lem:sum_Ndecay` at BA: `(Xi_infint)` and the product bound -/

section Ndecay

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `|Q_ab| = BAK_ab` and the Ward row sums of `BAK` give `‖M^{(σ₁σ₂)}‖_{∞→∞} ≤ 1` (`(eq:WardM)`; `BAMss_norm_eq_BAK`,
`BAK_row_sum`; the twin of the private `BAKBase_norm`, `BA/KBase.lean:151`). -/
private theorem EKPins_norm_Q_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ ≤ 1 := by
  have h : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa [BAMss_norm_eq_BAK] using (BAK_row_sum d L g E m hr.1 a).le
  exact_mod_cast h

/-- `(eq:THETAinftinf)`: `‖Θ_t‖_{∞→∞} ≤ 1/(1 - t)` from `Θ = 1 + t M Θ` and `‖M‖ ≤ 1`. -/
private theorem EKPins_norm_Theta_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) : ‖BATheta d L g E m t σ₁ σ₂‖ ≤ (1 - t)⁻¹ := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂).1
  have hQ := EKPins_norm_Q_le hr σ₁ σ₂
  set Θ := BATheta d L g E m t σ₁ σ₂
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  have h1 : ‖Θ‖ ≤ 1 + t * ‖Θ‖ := by
    calc ‖Θ‖ = ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) + (t : ℂ) • (Q * Θ)‖ := by rw [← h]
      _ ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖(t : ℂ) • (Q * Θ)‖ := norm_add_le _ _
      _ ≤ 1 + t * ‖Θ‖ := by
          rw [norm_one]
          refine add_le_add le_rfl ?_
          calc ‖(t : ℂ) • (Q * Θ)‖ ≤ ‖(t : ℂ)‖ * ‖Q * Θ‖ := norm_smul_le _ _
            _ ≤ t * (‖Q‖ * ‖Θ‖) := by
                rw [Complex.norm_real, Real.norm_of_nonneg ht0]
                exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) ht0
            _ ≤ t * (1 * ‖Θ‖) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQ (norm_nonneg _)) ht0
            _ = t * ‖Θ‖ := by rw [one_mul]
  have h1t : 0 < 1 - t := by linarith
  rw [← one_div, le_div_iff₀ h1t]
  nlinarith

/-- Each one-index factor `(1 - s M) Θ_t` has `(∞→∞)`-norm at most `(1 - s)/(1 - t)` (`(Xi_infint)` and `(eq:decompUalt)`). -/
private theorem EKPins_norm_uKer_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (ht : t < 1) (σ₁ σ₂ : Bool) :
    ‖BAuKer d L g E m s t σ₁ σ₂‖ ≤ (1 - s) / (1 - t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have h1t : 0 < 1 - t := by linarith
  have hQ := EKPins_norm_Q_le hr σ₁ σ₂
  have hΘ := EKPins_norm_Theta_le hr ht0 ht σ₁ σ₂
  set Θ := BATheta d L g E m t σ₁ σ₂
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  have hc : ‖(t : ℂ) - s‖ = t - s := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [BAuKer_eq_one_add hr ht0 ht σ₁ σ₂]
  calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) + ((t : ℂ) - s) • (Q * Θ)‖
      ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖ + ‖((t : ℂ) - s) • (Q * Θ)‖ := norm_add_le _ _
    _ ≤ 1 + (t - s) * (1 - t)⁻¹ := by
        rw [norm_one]
        refine add_le_add le_rfl ?_
        calc ‖((t : ℂ) - s) • (Q * Θ)‖ ≤ ‖(t : ℂ) - s‖ * ‖Q * Θ‖ := norm_smul_le _ _
          _ ≤ (t - s) * (‖Q‖ * ‖Θ‖) := by
              rw [hc]; exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (by linarith)
          _ ≤ (t - s) * (1 * (1 - t)⁻¹) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hQ hΘ (norm_nonneg _) zero_le_one) (by linarith)
          _ = (t - s) * (1 - t)⁻¹ := by rw [one_mul]
    _ = (1 - s) / (1 - t) := by field_simp; ring

end Ndecay

section NdecayThm

open scoped Matrix.Norms.Operator

/-- **`lem:sum_Ndecay` for the block Anderson model** (`A:95-110`): `(Xi_infint)`, the bound `(1 - s)/(1 - t)` of each
one-index factor, and the product over the `n` indices (`norm_tensorKer_le`, `BAUN` is a tensor kernel). -/
theorem baEKSumNdecay_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumNdecay d n Λ κ := by
  intro _ _ L hL g hg hgΛ E m hr σ s t hs hst ht A
  have : NeZero L := ⟨by omega⟩
  have h := norm_tensorKer_le (d := d) (L := L) (fun i : Fin n => BAuKer d L g E m s t (σ i) (σ (finRotate n i))) A
  have hpos : 0 ≤ (1 - s) / (1 - t) := div_nonneg (by linarith) (by linarith)
  refine le_trans h ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ∏ i : Fin n, ‖BAuKer d L g E m s t (σ i) (σ (finRotate n i))‖
      ≤ ∏ _i : Fin n, (1 - s) / (1 - t) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => EKPins_norm_uKer_le hr hs hst ht _ _
    _ = ((1 - s) / (1 - t)) ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end NdecayThm

/-! ## 4. The BA `Ξ` pins (`(eq:decayXi)`, ball sums, `(eq:samecolor)`; band forms `Evolution/XiPins.lean:281-357`) -/

section XiPins

open scoped Matrix.Norms.Operator

/-- `(eq:decayXi)` (`A:115-118`) for `Ξ = (t - s) M^{(σ₁σ₂)} Θ_t^{(σ₁σ₂)}`, uniform in `g ∈ (0, Λ]` and in the bulk
data `BAReal d L g κ E m`, every charge pair (`BAReal` in place of `‖μ‖ = 1`). -/
def BAEKXiDecay (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
        ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
          ‖BAXi d L g E m s t σ₁ σ₂ a b‖
            ≤ C * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L (a - b) : ℝ) + 1) ^ (d - 2))⁻¹
              * Real.exp (-(c * (zdistD d L (a - b) : ℝ)) / ellT L g t)

/-- Ball sums of `Ξ` over any set within distance `R ≤ Λ' ℓ_s` of a centre. -/
def BAEKXiBall (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t →
        ∀ σ₁ σ₂ : Bool, ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ R : ℝ, 1 ≤ R → R ≤ Λ' * ellT L g s →
          ∀ (a ctr : Zd d L) (D : Finset (Zd d L)), (∀ b ∈ D, (zdistD d L (ctr - b) : ℝ) ≤ R) →
            ∑ b ∈ D, ‖BAXi d L g E m s t σ₁ σ₂ a b‖
              ≤ C * Λ' ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|))

/-- `(eq:samecolor)` (`A:209`): at a same-sign index the one-index factor `(1 - s M^{(σσ)}) Θ_t^{(σσ)}` is bounded in the
`∞ → ∞` norm, uniformly in `L, g ≤ Λ, s, t`; bulk `κ ≤ Im m` inside `BAReal`. -/
def BAEKSameRow (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ σ : Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
        ‖BAuKer d L g E m s t σ σ‖ ≤ C

end XiPins

section XiProofs

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `M^{(σ₁σ₂)}` is invariant under the diagonal shift (`BAMB_shift`, `BA/Ward.lean:53`; `M(-) = M^*`). -/
private theorem EKPins_Mss_shift (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ (a + r) (b + r) = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b := by
  have hM := BAMB_shift d L g (E : ℂ) m
  have hs : ∀ (σ : Bool) (x y : Zd d L),
      BAMsigma d L (BAMB d L g (E : ℂ) m) σ (x + r) (y + r) = BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y := by
    intro σ x y
    cases σ
    · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, hM]
    · simp only [BAMsigma, ite_true, hM]
  simp only [BAMss, Matrix.of_apply, hs]

/-- `Θ_t(a + r, b + r) = Θ_t(a, b)`, every `(σ₁, σ₂)` (the pattern of `BAMB_shift`; a copy of the private
`baP8_BATheta_shift`, `BA/Prop6Path.lean:495`). -/
private theorem EKPins_Theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b r : Zd d L) :
    BATheta d L g E m t σ₁ σ₂ (a + r) (b + r) = BATheta d L g E m t σ₁ σ₂ a b := by
  have hA : (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂).submatrix
      (Equiv.addRight r) (Equiv.addRight r)
      = 1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ := by
    ext x y
    have h1 : (x + r = y + r) ↔ (x = y) := add_left_inj r
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      Equiv.coe_addRight, h1, EKPins_Mss_shift]
  have h2 := Matrix.inv_submatrix_equiv
    (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) (Equiv.addRight r) (Equiv.addRight r)
  rw [hA] at h2
  unfold BATheta PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 a) b
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- `Θ_t(a, b) = Θ_t(0, b - a)`. -/
private theorem EKPins_Theta_apply (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    BATheta d L g E m t σ₁ σ₂ a b = BATheta d L g E m t σ₁ σ₂ 0 (b - a) := by
  have h := EKPins_Theta_shift g E m t σ₁ σ₂ 0 (b - a) a
  simpa using h

/-- For `t > 0`: `Ξ = ((t - s)/t) (Θ_t - 1)` (`Θ = 1 + t M Θ`, `BAuKer_convex`). -/
private theorem EKPins_Xi_eq {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) :
    BAXi d L g E m s t σ₁ σ₂ = (((t - s) / t : ℝ) : ℂ) • (BATheta d L g E m t σ₁ σ₂ - 1) := by
  have h := (BATheta_resolvent d L g κ E m hr t ht0.le ht1 σ₁ σ₂).1
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have h' : BATheta d L g E m t σ₁ σ₂ - 1 = (t : ℂ) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
      BATheta d L g E m t σ₁ σ₂) := sub_eq_of_eq_add' h
  unfold BAXi
  rw [h', smul_smul]
  congr 1
  push_cast
  field_simp

omit [NeZero L] in
/-- The zero mode is absorbed in the decay profile (`zeroMode_le_of_ge_mul`, `Kernel/PropT.lean:89`,
`m = k + 2`): for `‖θ‖ ≤ C_d B_{t,|x|} e^{-c|x|/ℓ_t}` and `1 - t ≥ g²/L²`,
`‖θ‖ ≤ C_d (1 + 2 (2(k+2))^k) (g²+|1-t|)⁻¹ (|x|+1)^{-k} e^{-c|x|/ℓ_t}`. -/
private theorem EKPins_theta_absorb {k : ℕ} {g t Cd cd : ℝ} (hL : 3 ≤ L) (ht : t < 1)
    (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hCd : 0 < Cd) (x : Zd (k + 2) L) (θ : ℂ)
    (hb : ‖θ‖ ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L x)
      * Real.exp (-cd * (zdistD (k + 2) L x : ℝ) / ellT L g t)) :
    ‖θ‖ ≤ (Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k)) * (g ^ 2 + |1 - t|)⁻¹
      * (((zdistD (k + 2) L x : ℝ) + 1) ^ k)⁻¹
      * Real.exp (-(cd * (zdistD (k + 2) L x : ℝ)) / ellT L g t) := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_of_lt (by omega : 1 < L)
  set A : ℝ := (g ^ 2 + |1 - t|)⁻¹ with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set r : ℝ := (zdistD (k + 2) L x : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hz := zeroMode_le_of_ge_mul (k := k) (L := L) (g := g) (t := t) (m := k + 2)
    (by omega) hL1 ht (zdistD_le (k + 2) x) hgt
  have hcast : ((2 : ℝ) * ((k + 2 : ℕ) : ℝ)) ^ k = (2 * ((k : ℝ) + 2)) ^ k := by
    push_cast; ring_nf
  rw [hcast] at hz
  have hBp : Bparam (k + 2) L g t (zdistD (k + 2) L x)
      ≤ (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * (A * ((r + 1) ^ k)⁻¹) := by
    simp only [Bparam, powW, hA, hr] at hz ⊢
    simp only [show k + 2 - 2 = k from rfl] at hz ⊢
    have hpow : (0 : ℝ) < ((zdistD (k + 2) L x : ℝ) + 1) ^ k := by positivity
    nlinarith [hz, inv_nonneg.mpr hpow.le]
  have hE0 : 0 ≤ Real.exp (-cd * r / ellT L g t) := (Real.exp_pos _).le
  have hexp : -cd * r / ellT L g t = -(cd * r) / ellT L g t := by rw [neg_mul]
  rw [hexp] at hb
  calc ‖θ‖ ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L x) * Real.exp (-(cd * r) / ellT L g t) := hb
    _ ≤ Cd * ((1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) * (A * ((r + 1) ^ k)⁻¹))
          * Real.exp (-(cd * r) / ellT L g t) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBp hCd.le) (Real.exp_pos _).le
    _ = (Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k)) * A * ((r + 1) ^ k)⁻¹
          * Real.exp (-(cd * r) / ellT L g t) := by ring

/-- `(eq:decayXi)` entrywise, with visible constants: `Θ`-decay `hbd` (from `BAProp5`) gives
`‖Ξ_{ab}‖ ≤ (Cd C_B + Λ² + 1) (1 - s) (g²+|1-t|)⁻¹ (|a-b|+1)^{-k} e^{-c|a-b|/ℓ_t}`; for `a ≠ b` the factor is
`(t-s)/t ≤ 1 - s`, for `a = b` the unit `1` is absorbed by `1 ≤ (Λ²+1)(g²+|1-t|)⁻¹`. -/
private theorem EKPins_Xi_entry_le {k : ℕ} {g κ E Λ Cd cd : ℝ} {m : ℂ} (hL : 3 ≤ L) (hg : 0 < g) (hgΛ : g ≤ Λ)
    (hCd : 0 < Cd) (hr : BAReal (k + 2) L g κ E m)
    (hbd : ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ x : Zd (k + 2) L,
      ‖BATheta (k + 2) L g E m t σ₁ σ₂ 0 x‖ ≤ Cd * Bparam (k + 2) L g t (zdistD (k + 2) L x)
        * Real.exp (-cd * (zdistD (k + 2) L x : ℝ) / ellT L g t))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t)
    (σ₁ σ₂ : Bool) (a b : Zd (k + 2) L) :
    ‖BAXi (k + 2) L g E m s t σ₁ σ₂ a b‖
      ≤ (Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) + Λ ^ 2 + 1) * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
        * (((zdistD (k + 2) L (a - b) : ℝ) + 1) ^ k)⁻¹
        * Real.exp (-(cd * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t) := by
  have ht0 : 0 ≤ t := hs.trans hst
  set A : ℝ := (g ^ 2 + |1 - t|)⁻¹ with hA
  have hA0 : 0 < A := by
    rw [hA]; have : 0 < 1 - t := by linarith
    rw [abs_of_pos this]; positivity
  set R : ℝ := (zdistD (k + 2) L (a - b) : ℝ) with hR
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  set CB : ℝ := 1 + 2 * (2 * ((k : ℝ) + 2)) ^ k with hCB
  have hCB0 : 0 < CB := by rw [hCB]; positivity
  have hP : 0 < (R + 1) ^ k := by positivity
  have hE : 0 < Real.exp (-(cd * R) / ellT L g t) := Real.exp_pos _
  set Pw : ℝ := A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) with hPw
  have hPw0 : 0 < Pw := by rw [hPw]; positivity
  -- the profile of `Θ` at `(a, b)`
  have hθ : ‖BATheta (k + 2) L g E m t σ₁ σ₂ a b‖ ≤ (Cd * CB) * Pw := by
    rw [EKPins_Theta_apply]
    have hba : zdistD (k + 2) L (b - a) = zdistD (k + 2) L (a - b) := by
      rw [← zdistD_neg (k + 2) L (b - a), neg_sub]
    have h := EKPins_theta_absorb (L := L) (k := k) hL ht hgt hCd (b - a) _ (hbd t ht0 ht σ₁ σ₂ (b - a))
    rw [hba] at h
    refine h.trans (le_of_eq ?_)
    rw [hPw, hA]; ring
  have hunit : 1 ≤ (Λ ^ 2 + 1) * A := by
    have hgl : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
    have h1t : |1 - t| ≤ 1 := by
      rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]; linarith
    have hden : g ^ 2 + |1 - t| ≤ Λ ^ 2 + 1 := by linarith
    have hden0 : 0 < g ^ 2 + |1 - t| := by
      have : 0 < 1 - t := by linarith
      rw [abs_of_pos this]; positivity
    rw [hA, ← div_eq_mul_inv, one_le_div hden0]
    exact hden
  by_cases ht00 : t = 0
  · -- then `s = 0` and `Ξ = 0`
    have hs0 : s = 0 := le_antisymm (ht00 ▸ hst) hs
    have hΞ : BAXi (k + 2) L g E m s t σ₁ σ₂ = 0 := by
      unfold BAXi; rw [ht00, hs0]; simp
    rw [hΞ]
    simp only [Matrix.zero_apply, norm_zero]
    have : 0 ≤ (Cd * CB + Λ ^ 2 + 1) * (1 - s) * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) := by
      have : 0 ≤ 1 - s := by linarith
      positivity
    exact this
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht00)
    have hcoef0 : 0 ≤ (t - s) / t := div_nonneg (by linarith) htpos.le
    have hcoef : (t - s) / t ≤ 1 - s := by
      rw [div_le_iff₀ htpos]; nlinarith
    rw [EKPins_Xi_eq hr htpos ht, Matrix.smul_apply, Matrix.sub_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hcoef0]
    have hdiag : ‖BATheta (k + 2) L g E m t σ₁ σ₂ a b - (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) a b‖
        ≤ (Cd * CB + Λ ^ 2 + 1) * Pw := by
      by_cases hab : a = b
      · subst hab
        have hR00 : R = 0 := by simp [hR]
        have hPw' : Pw = A := by
          rw [hPw, hR00]; simp
        rw [hPw']
        refine (norm_sub_le _ _).trans ?_
        rw [Matrix.one_apply_eq, norm_one]
        rw [hPw'] at hθ
        nlinarith [hθ, hunit]
      · rw [Matrix.one_apply_ne hab, sub_zero]
        refine hθ.trans ?_
        have h1 : 0 ≤ Λ ^ 2 + 1 := by positivity
        nlinarith [mul_nonneg h1 hPw0.le]
    calc (t - s) / t * ‖BATheta (k + 2) L g E m t σ₁ σ₂ a b - (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) a b‖
        ≤ (1 - s) * ((Cd * CB + Λ ^ 2 + 1) * Pw) :=
          mul_le_mul hcoef hdiag (norm_nonneg _) (by linarith)
      _ = (Cd * CB + Λ ^ 2 + 1) * (1 - s) * A * ((R + 1) ^ k)⁻¹ * Real.exp (-(cd * R) / ellT L g t) := by
          rw [hPw]; ring

/-- The ball-sum step of `lem:sum_decay`, generic in the entries `X b` (the twin of `ek_sum_ball_norm_XiKer_le`,
`Evolution/XiPins.lean:176`: only the pointwise bound on `‖Ξ_{ab}‖` is read): `Σ_{b ∈ D} ‖X b‖ ≤ 4 C₀ ballC Λ'² (ĝ²+|1-s|)/(ĝ²+|1-t|)`
for `D` in the ball of radius `R ≤ Λ' ℓ_s` around `ctr`. -/
private theorem EKPins_sum_ball_le {k : ℕ} {g : ℝ} (hL : 3 ≤ L) (hg : 0 < g) {C₀ c : ℝ} (hC₀ : 0 < C₀)
    (hc : 0 < c) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < 1) (a ctr : Zd (k + 2) L)
    (X : Zd (k + 2) L → ℂ)
    (hbd : ∀ b, ‖X b‖ ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD (k + 2) L (a - b) : ℝ) + 1) ^ k)⁻¹
      * Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t))
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {R : ℝ} (hR : 1 ≤ R) (hRℓ : R ≤ Λ * ellT L g s) (D : Finset (Zd (k + 2) L))
    (hD : ∀ b ∈ D, ((zdistD (k + 2) L (ctr - b) : ℕ) : ℝ) ≤ R) :
    ∑ b ∈ D, ‖X b‖ ≤ (4 * C₀ * ballC k) * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast le_trans (by norm_num) hL
  have hs1 : s < 1 := lt_of_le_of_lt hst ht
  have habs : |1 - s| = 1 - s := abs_of_pos (by linarith)
  have hgt0 : (0 : ℝ) < g ^ 2 + |1 - t| := by
    have : 0 < 1 - t := by linarith
    rw [abs_of_pos this]; positivity
  -- the entries, with the exponential thrown away
  have hpt : ∀ b ∈ D, ‖X b‖ ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
      * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
    intro b _
    refine (hbd b).trans ?_
    have hexp : Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hℓ : 0 < ellT L g t := ellT_pos hL1
      have : 0 ≤ c * (zdistD (k + 2) L (a - b) : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hℓ.le
    have hnn : (0 : ℝ) ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
        * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
      have : (0 : ℝ) ≤ 1 - s := by linarith
      positivity
    calc C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹
          * Real.exp (-(c * (zdistD (k + 2) L (a - b) : ℝ)) / ellT L g t)
        ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp hnn
      _ = C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := mul_one _
  -- the ball sum of the polynomial factor (the ball is around `ctr`, the entries around `a`)
  have hball : ∑ b ∈ D, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ ≤ ballC k * R ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun b _ => ?_)
      (sum_ball_min_pow_le (L := L) k hR D ctr a hD)
    have hmin : min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R
        ≤ ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) := min_le_left _ _
    have h1 : (0 : ℝ) < (min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R + 1) ^ k := by
      have : (0 : ℝ) ≤ min ((zdistD (k + 2) L (a - b) : ℕ) : ℝ) R :=
        le_min (Nat.cast_nonneg _) (by linarith)
      positivity
    exact inv_anti₀ h1 (pow_le_pow_left₀ (by positivity) (by linarith) k)
  have hcoef : (0 : ℝ) ≤ C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹ := by
    have : (0 : ℝ) ≤ 1 - s := by linarith
    positivity
  -- `R² ≤ Λ² ℓ_s²`, and `(1-s) ℓ_s² ≤ ĝ² + |1-s|`
  have hℓs : (1 : ℝ) ≤ ellT L g s := one_le_ellT hL1
  have hR2 : R ^ 2 ≤ Λ ^ 2 * ellT L g s ^ 2 := by
    have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R) hRℓ 2
    rwa [mul_pow] at this
  have hkey : (1 - s) * (Λ ^ 2 * ellT L g s ^ 2) ≤ Λ ^ 2 * (g ^ 2 + |1 - s|) := by
    have h := one_sub_mul_ellT_sq_le (L := L) (g := g) (s := s) hg.le hs1
    rw [habs] at h
    nlinarith [sq_nonneg Λ, ellT_pos hL1 (L := L) (g := g) (t := s)]
  calc ∑ b ∈ D, ‖X b‖
      ≤ ∑ b ∈ D, (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
          * ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := Finset.sum_le_sum hpt
    _ = (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹)
          * ∑ b ∈ D, ((((zdistD (k + 2) L (a - b) : ℕ) : ℝ) + 1) ^ k)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹) * (ballC k * R ^ 2) :=
        mul_le_mul_of_nonneg_left hball hcoef
    _ ≤ (C₀ * (1 - s) * (g ^ 2 + |1 - t|)⁻¹) * (ballC k * (Λ ^ 2 * ellT L g s ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoef
        exact mul_le_mul_of_nonneg_left hR2 (ballC_nonneg k)
    _ = C₀ * ballC k * ((1 - s) * (Λ ^ 2 * ellT L g s ^ 2)) * (g ^ 2 + |1 - t|)⁻¹ := by ring
    _ ≤ C₀ * ballC k * (Λ ^ 2 * (g ^ 2 + |1 - s|)) * (g ^ 2 + |1 - t|)⁻¹ := by
        have h0 : (0 : ℝ) ≤ C₀ * ballC k := mul_nonneg hC₀.le (ballC_nonneg k)
        have := mul_le_mul_of_nonneg_left hkey h0
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) * (g ^ 2 + |1 - t|)⁻¹) := by ring
    _ ≤ 4 * C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) := by
        rw [div_eq_mul_inv]
        have h0 : (0 : ℝ) ≤ C₀ * ballC k * Λ ^ 2 * ((g ^ 2 + |1 - s|) * (g ^ 2 + |1 - t|)⁻¹) := by
          refine mul_nonneg (mul_nonneg (mul_nonneg hC₀.le (ballC_nonneg k)) (sq_nonneg Λ)) ?_
          have h1 : (0 : ℝ) ≤ g ^ 2 + |1 - s| := by positivity
          have h2 : (0 : ℝ) ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
          exact mul_nonneg h1 h2
        linarith

end XiProofs

section XiThms

open scoped Matrix.Norms.Operator

/-- **`(eq:decayXi)` at BA** (`A:115-118`), from `BAuKer_convex` (`Ξ_{ab} = ((t-s)/t) Θ_{t,ab}`, `a ≠ b`) and `baProp5_holds`;
no `Mbound_AO`, no smallness of `g` or of `‖M - m₀ I‖`. -/
theorem baEKXiDecay_holds (d : ℕ) (Λ κ : ℝ) : BAEKXiDecay d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := baProp5_holds (k + 2) Λ κ hd hΛ hκ
  refine ⟨Cd * (1 + 2 * (2 * ((k : ℝ) + 2)) ^ k) + Λ ^ 2 + 1, cd, by positivity, hcd, ?_⟩
  intro L hL g hg hgΛ E m hr s t hs hst ht hgt σ₁ σ₂ a b
  have : NeZero L := ⟨by omega⟩
  exact EKPins_Xi_entry_le (L := L) (k := k) hL hg hgΛ hCd hr
    (fun t ht0 ht1 σ₁ σ₂ x => hbd L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ x) hs hst ht hgt σ₁ σ₂ a b

/-- **Ball sums of `Ξ` at BA** (`A:131-149`, third step of `(sum_res_deriv_red)`): from `baEKXiDecay_holds`. -/
theorem baEKXiBall_holds (d : ℕ) (Λ κ : ℝ) : BAEKXiBall d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨C₀, c, hC₀, hc, hdec⟩ := baEKXiDecay_holds d Λ κ hd hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨4 * C₀ * ballC k, mul_pos (by positivity) (ballC_pos k), ?_⟩
  intro L hL g hg hgΛ E m hr s t hs hst ht hgt σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr D hD
  have : NeZero L := ⟨by omega⟩
  exact EKPins_sum_ball_le (L := L) hL hg hC₀ hc hs hst ht a ctr _
    (fun b => hdec L hL g hg hgΛ E m hr s t hs hst ht hgt σ₁ σ₂ a b) hΛ' hR hRℓ D hD

/-- **`(eq:samecolor)` at BA** (`A:209`): `‖(1 - s M^{(σσ)}) Θ_t^{(σσ)}‖_{∞→∞} ≤ 1 + ‖Θ_t^{(σσ)}‖`, `‖Θ‖ ≤ Σ_b |Θ(0,b)|`
(translation invariance), `baProp5s_holds`, `Σ_b e^{-c|b|} ≤ expC`; `M^{(σσ)}` is the matrix `Q` with `‖Q‖_{∞→∞} ≤ 1`. -/
theorem baEKSameRow_holds (d : ℕ) (Λ κ : ℝ) : BAEKSameRow d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cκ, hCκ, cκ, hcκ, hbd⟩ := baProp5s_holds (k + 2) Λ κ hd hΛ hκ
  have hexp0 : 0 ≤ expC k cκ := by
    unfold expC
    have : (0 : ℝ) < cκ ^ (k + 3) := by positivity
    positivity
  refine ⟨1 + Cκ * (1 + Λ ^ 2 * expC k cκ), by positivity, ?_⟩
  intro L hL g hg hgΛ E m hr σ s t hs hst ht
  have : NeZero L := ⟨by omega⟩
  have ht0 : 0 ≤ t := hs.trans hst
  have hQ := EKPins_norm_Q_le hr σ σ
  have hTheta : ‖BATheta (k + 2) L g E m t σ σ‖ ≤ Cκ * (1 + Λ ^ 2 * expC k cκ) := by
    refine (norm_le_sum_row_zero _ (fun a b c => EKPins_Theta_shift g E m t σ σ a b c)).trans ?_
    calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ 0 b‖
        ≤ ∑ b : Zd (k + 2) L, Cκ * ((if b = 0 then 1 else 0)
            + g ^ 2 * Real.exp (-cκ * (zdistD (k + 2) L b : ℝ))) :=
          Finset.sum_le_sum fun b _ => hbd L hL g hg hgΛ E m hr t ht0 ht σ b
      _ = Cκ * (1 + g ^ 2 * ∑ b : Zd (k + 2) L,
            Real.exp (-(cκ * (zdistD (k + 2) L b : ℝ)))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          · simp
          · exact congrArg _ (Finset.sum_congr rfl fun b _ => by ring_nf)
      _ ≤ Cκ * (1 + Λ ^ 2 * expC k cκ) := by
          have hsum := sum_radial_exp_decay_le (L := L) k hcκ
          have hg2 : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
          have hs0 : 0 ≤ ∑ b : Zd (k + 2) L, Real.exp (-(cκ * (zdistD (k + 2) L b : ℝ))) :=
            Finset.sum_nonneg fun b _ => (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left ?_ hCκ.le
          have h1 := mul_le_mul_of_nonneg_left hsum (sq_nonneg g)
          have h2 := mul_le_mul_of_nonneg_right hg2 hexp0
          linarith
  -- `uKer = 1 + Ξ` with `‖Ξ‖ ≤ (t - s) ‖Q‖ ‖Θ‖ ≤ ‖Θ‖`
  rw [BAuKer_eq_one_add hr ht0 ht σ σ]
  have hc : ‖(t : ℂ) - s‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  calc ‖(1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ) + ((t : ℂ) - s) •
        (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ * BATheta (k + 2) L g E m t σ σ)‖
      ≤ 1 + ‖((t : ℂ) - s) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ *
          BATheta (k + 2) L g E m t σ σ)‖ := by
        have := norm_add_le (1 : Matrix (Zd (k + 2) L) (Zd (k + 2) L) ℂ)
          (((t : ℂ) - s) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ *
            BATheta (k + 2) L g E m t σ σ))
        rwa [norm_one] at this
    _ ≤ 1 + Cκ * (1 + Λ ^ 2 * expC k cκ) := by
        have hsmul := norm_smul_le ((t : ℂ) - s) (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ *
          BATheta (k + 2) L g E m t σ σ)
        have hmul := norm_mul_le (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ) (BATheta (k + 2) L g E m t σ σ)
        have h1 : ‖((t : ℂ) - s) • (BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ *
            BATheta (k + 2) L g E m t σ σ)‖ ≤ 1 * ‖BATheta (k + 2) L g E m t σ σ‖ := by
          refine hsmul.trans ?_
          refine mul_le_mul hc (hmul.trans ?_) (norm_nonneg _) zero_le_one
          calc ‖BAMss (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ σ‖ * ‖BATheta (k + 2) L g E m t σ σ‖
              ≤ 1 * ‖BATheta (k + 2) L g E m t σ σ‖ := mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
            _ = ‖BATheta (k + 2) L g E m t σ σ‖ := one_mul _
        rw [one_mul] at h1
        linarith

end XiThms

/-! ## 5. Compiled nonempty instances (`d = 3`, the flow datum `n = 0` of `sz0`)

`L = 4`, `g₀ = √t₀ λ ≤ λ = 1/64`, `κ = 1/2`, `BAReal` by `BAflow_real` (`BA/GreenSchur.lean:59`) at the merged flow
`flow_sz0` (`BA/FlowPins.lean:1235`), `Λ = 1`, `n = 2`, `σ = (+,-)` (`(+,+)` for the non-alternating and same-sign
rows), `s = 0`, `t = 1/2 ≤ 1 - g₀²/L²`, `W = 16`, `ε = 1/2` (`W^ε = 4`), `D = 2`, `A = δ_0` (`(deccA0)` holds).  The four
open pins stay hypotheses of their instances; every deterministic hypothesis is discharged. -/

namespace EKPinsInst

open RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- `g₀`, `E`, `m₀` of the flow of `sz0` at `n = 0`. -/
abbrev gI : ℝ := BAflowLam0 sz0 zSeq 0
abbrev EI : ℝ := BAflowEs sz0 zSeq 0
abbrev mI : ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0

/-- The tensor `δ_0` on `(Z_L^3)^2`. -/
def AI : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ := fun a => if a = 0 then 1 else 0

theorem AI_zero : AI 0 = 1 := by simp [AI]

theorem gI_pos : 0 < gI := by
  have hT : 0 < BAflowT0 sz0 zSeq 0 := by linarith [t0_sz0 0]
  exact mul_pos (Real.sqrt_pos.mpr hT) (sz0_lam_pos 0)

theorem gI_le : gI ≤ 1 / 64 := by
  have hm : 0 < (BAm 3 (sz0.L 0) (sz0.lam 0) (zSeq 0)).im := by
    rw [BAm_zSeq 0]; linarith [mS_im_half (sz0.L 0) (sz0.lam 0) (sz0_lam_L 0)]
  have h := BAg0_le (sz0_lam_pos 0).le (zSeq_im_pos 0) hm
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  unfold gI BAflowLam0 BAflowT0
  rw [← hl]
  exact h

theorem LI_real : ((sz0.L 0 : ℕ) : ℝ) = 4 := by rw [sz0_values.1]; norm_num

/-- the bulk data `BAReal` at the flow datum. -/
theorem hrI : BAReal 3 (sz0.L 0) gI (1 / 2) EI mI := BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 0

/-- `g₀² / L² ≤ 1 - t` for every `t ≤ 1/2`. -/
theorem gI_sq_le : gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 ≤ 1 - 1 / 2 := by
  rw [LI_real]
  have := gI_le
  have := gI_pos
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

theorem AI_fastDecay : EKFastDecay gI 0 (16 : ℝ) (1 / 2) 2 AI := by
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hℓ : 1 ≤ ellT (sz0.L 0) gI 0 := one_le_ellT (by rw [LI_real]; norm_num)
    simp at hij
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 16) (1 / 2 : ℝ)]
  · simp only [AI, ha, ↓reduceIte, norm_zero]
    positivity

/-- `lem:sum_Ndecay` at the flow datum: `‖U ∘ δ_0‖_∞ ≤ ((1-s)/(1-t))² ‖δ_0‖_∞`, `s = 0`, `t = 1/2`. -/
theorem inst_baEKSumNdecay :
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AI‖ ≤ ((1 - 0) / (1 - 1 / 2)) ^ 2 * ‖AI‖ :=
  baEKSumNdecay_holds 3 2 1 (1 / 2) (by norm_num) le_rfl (sz0.L 0) (sz0.three_le_L 0) gI gI_pos
    (gI_le.trans (by norm_num)) EI mI hrI ![true, false] 0 (1 / 2) le_rfl (by norm_num) (by norm_num) AI

/-- The lattice ball of radius `1` around `0` (`ℓ¹` distance). -/
def ballI : Finset (Zd 3 (sz0.L 0)) := Finset.univ.filter fun b => zdistD 3 (sz0.L 0) (0 - b) ≤ 1

theorem zero_mem_ballI : (0 : Zd 3 (sz0.L 0)) ∈ ballI := by simp [ballI]

theorem ballI_dist : ∀ b ∈ ballI, (zdistD 3 (sz0.L 0) (0 - b) : ℝ) ≤ 1 := fun b hb => by
  exact_mod_cast (Finset.mem_filter.1 hb).2

/-- `baEKXiDecay_holds` at `σ = (+,-)`, `s = 0`, `t = 1/2`, every pair `(a, b)`. -/
theorem inst_baEKXiDecay : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a b : Zd 3 (sz0.L 0),
    ‖BAXi 3 (sz0.L 0) gI EI mI 0 (1 / 2) true false a b‖
      ≤ C * (1 - 0) * (gI ^ 2 + |1 - 1 / 2|)⁻¹ * (((zdistD 3 (sz0.L 0) (a - b) : ℝ) + 1) ^ (3 - 2))⁻¹
        * Real.exp (-(c * (zdistD 3 (sz0.L 0) (a - b) : ℝ)) / ellT (sz0.L 0) gI (1 / 2)) := by
  obtain ⟨C, c, hC, hc, H⟩ := baEKXiDecay_holds 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  exact ⟨C, c, hC, hc, fun a b => H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) EI mI hrI
    0 (1 / 2) le_rfl (by norm_num) (by norm_num) gI_sq_le true false a b⟩

/-- `baEKXiBall_holds` at the 7-point ball around `ctr = 0`, `a = 0`, `Λ' = 1`, `R = 1 ≤ ℓ_s`. -/
theorem inst_baEKXiBall : ∃ C : ℝ, 0 < C ∧ (0 : Zd 3 (sz0.L 0)) ∈ ballI ∧
    ∑ b ∈ ballI, ‖BAXi 3 (sz0.L 0) gI EI mI 0 (1 / 2) true false 0 b‖
      ≤ C * 1 ^ 2 * ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) := by
  obtain ⟨C, hC, H⟩ := baEKXiBall_holds 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  exact ⟨C, hC, zero_mem_ballI, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) EI mI hrI
    0 (1 / 2) le_rfl (by norm_num) (by norm_num) gI_sq_le true false 1 le_rfl 1 le_rfl
    (by rw [one_mul]; exact one_le_ellT (by rw [LI_real]; norm_num)) 0 0 ballI ballI_dist⟩

open scoped Matrix.Norms.Operator in
/-- `baEKSameRow_holds` at `m₀`, both signs, `s = 0`, `t = 1/2`. -/
theorem inst_baEKSameRow : ∃ C : ℝ, 0 < C ∧
    ∀ σ : Bool, ‖BAuKer 3 (sz0.L 0) gI EI mI 0 (1 / 2) σ σ‖ ≤ C := by
  obtain ⟨C, hC, H⟩ := baEKSameRow_holds 3 1 (1 / 2) le_rfl one_pos (by norm_num)
  exact ⟨C, hC, fun σ => H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) EI mI hrI σ
    0 (1 / 2) le_rfl (by norm_num) (by norm_num)⟩

theorem sixteen_rpow_half : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
  rw [← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

theorem half_le_one_sub : (1 / 2 : ℝ) ≤ 1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by
  have := gI_sq_le
  linarith

/-- An instance of `BAEKSumDecay1` (`(sum_res_1)`): the pin is the only hypothesis (BA-E2). -/
theorem inst_BAEKSumDecay1 (h : BAEKSumDecay1 3 2 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      (ellT (sz0.L 0) gI (1 / 2) ^ 2 / ellT (sz0.L 0) gI 0 ^ 2) *
        ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ 2 * ‖AI‖ + (16 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) le_rfl one_pos (by norm_num)
  exact ⟨C, hC, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) 16 (1 / 2) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [sixteen_rpow_half]) 0 (1 / 2) le_rfl (by norm_num)
    half_le_one_sub (by norm_num) EI mI hrI ![true, false] AI AI_fastDecay⟩

/-- An instance of `BAEKSumDecayNAL` (`(sum_res_2_NAL)`, `σ = (+,+)`). -/
theorem inst_BAEKSumDecayNAL (h : BAEKSumDecayNAL 3 2 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, true] 0 (1 / 2) AI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ (2 - 1) * ‖AI‖ + (16 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) le_rfl one_pos (by norm_num)
  exact ⟨C, hC, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) 16 (1 / 2) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [sixteen_rpow_half]) 0 (1 / 2) le_rfl (by norm_num)
    half_le_one_sub (by norm_num) EI mI hrI ![true, true] ⟨0, by decide⟩ AI AI_fastDecay⟩

/-- An instance of `BAEKSumDecayNonzero` at the window `1 - g₀²/L² ≤ s ≤ t < 1`, `s = 1 - g₀²/L²`,
`t = 1 - g₀²/(2 L²)`, `A = {0, 1} ⊇ I_diff(+,-)`. -/
theorem inst_BAEKSumDecayNonzero (h : BAEKSumDecayNonzero 3 2 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖zeroModeSet 3 (sz0.L 0) Finset.univ (BAUN 3 (sz0.L 0) gI EI mI ![true, false]
      (1 - gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) (1 - gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2)) AI)‖ ≤ C * ‖AI‖ := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) le_rfl one_pos (by norm_num)
  have hL4 : (0 : ℝ) < ((sz0.L 0 : ℕ) : ℝ) ^ 2 := by rw [LI_real]; norm_num
  have hq : 0 < gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 := div_pos (pow_pos gI_pos 2) hL4
  have hq2 : gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by have := gI_sq_le; linarith
  have hst : gI ^ 2 / (2 * ((sz0.L 0 : ℕ) : ℝ) ^ 2) = (gI ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2) / 2 := by
    field_simp
  refine ⟨C, hC, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) _ _ (by linarith)
    le_rfl (by rw [hst]; linarith) (by rw [hst]; linarith) EI mI hrI ![true, false] Finset.univ
    (fun i _ => Finset.mem_univ i) AI⟩

/-! ### An instance of `BAEKSumDecay2` (`(sumAzero)`): `𝒜 = δ_0 ⊗ (δ_0 - δ_e)`, `e = (1,0,0)` -/

/-- `e = (1,0,0)`. -/
abbrev eI : Zd 3 (sz0.L 0) := ![1, 0, 0]

/-- The sum-zero tensor `δ_0 ⊗ (δ_0 - δ_e)`. -/
def AzI : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ := fun b =>
  if b 0 = 0 then (if b 1 = 0 then 1 else 0) - (if b 1 = eI then 1 else 0) else 0

theorem zdistD_eI : zdistD 3 (sz0.L 0) eI = 1 := by
  unfold zdistD
  simp only [zdist, eI, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZMod.val_zero, tsub_zero, zero_le, inf_of_le_left, add_zero, Matrix.cons_val]
  decide

theorem zero_ne_eI : (0 : Zd 3 (sz0.L 0)) ≠ eI := by
  intro h
  have := congrFun h 0
  simp only [eI, Pi.zero_apply, Matrix.cons_val_zero] at this
  exact absurd this (by decide)

theorem AzI_vals : AzI ![0, 0] = 1 ∧ AzI ![0, eI] = -1 := by
  simp [AzI, zero_ne_eI, zero_ne_eI.symm]

theorem AzI_fastDecay : EKFastDecay gI 0 (16 : ℝ) (1 / 2) 2 AzI := by
  intro a ⟨i, j, hij⟩
  by_cases h : AzI a = 0
  · rw [h]; simp only [norm_zero]; positivity
  · exfalso
    have h0 : a 0 = 0 := by
      by_contra hc; simp [AzI, hc] at h
    have h1 : a 1 = 0 ∨ a 1 = eI := by
      by_contra hc
      rw [not_or] at hc
      simp [AzI, h0, hc.1, hc.2] at h
    have hE : ∀ y : Zd 3 (sz0.L 0), y = 0 ∨ y = eI → zdistD 3 (sz0.L 0) y ≤ 1 := by
      rintro y (rfl | rfl)
      · simp
      · rw [zdistD_eI]
    have hd : ∀ i j : Fin 2, zdistD 3 (sz0.L 0) (a i - a j) ≤ 1 := by
      refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · simp
      · rw [h0, zero_sub, zdistD_neg]; exact hE _ h1
      · rw [h0, sub_zero]; exact hE _ h1
      · simp
    have hℓ : 1 ≤ ellT (sz0.L 0) gI 0 := one_le_ellT (by rw [LI_real]; norm_num)
    rw [sixteen_rpow_half] at hij
    have h2 : (zdistD 3 (sz0.L 0) (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast hd i j
    linarith

theorem AzI_sumZero : EKSumZero AzI := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  rw [Finset.sum_filter, ek_sum_fin_two]
  have e : ∀ x' y : Zd 3 (sz0.L 0), (if (![x', y] : Fin 2 → Zd 3 (sz0.L 0)) 0 = x then AzI ![x', y] else 0)
      = if x' = x then (if x' = 0 then (if y = 0 then (1 : ℂ) else 0) - (if y = eI then 1 else 0)
          else 0) else 0 := by
    intro x' y
    simp [AzI]
  simp only [e]
  by_cases hx : x = 0
  · subst hx
    simp [Finset.sum_ite_eq', Finset.sum_sub_distrib]
  · simp

theorem log_le_half : Real.log ((sz0.L 0 : ℕ) : ℝ) ≤ (16 : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [sixteen_rpow_half, LI_real]
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  linarith

/-- An instance of `BAEKSumDecay2` (`(sumAzero) ⟹ (sum_res_2)`, `σ = (+,-)`, `K = 2`: `L³ = 64 ≤ 16² = W^K`). -/
theorem inst_BAEKSumDecay2 (h : BAEKSumDecay2 3 2 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖BAUN 3 (sz0.L 0) gI EI mI ![true, false] 0 (1 / 2) AzI‖ ≤ (16 : ℝ) ^ (C * (1 / 2)) *
      ((gI ^ 2 + |1 - 0|) / (gI ^ 2 + |1 - 1 / 2|)) ^ 2 * ‖AzI‖ + (16 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) le_rfl one_pos (by norm_num) 2 two_pos
  exact ⟨C, hC, H (sz0.L 0) (sz0.three_le_L 0) gI gI_pos (gI_le.trans (by norm_num)) 16 (1 / 2) 2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [sixteen_rpow_half]) log_le_half
    (by rw [LI_real]; norm_num [Real.rpow_two]) 0 (1 / 2) le_rfl (by norm_num) half_le_one_sub (by norm_num)
    EI mI hrI ![true, false] AzI AzI_fastDecay AzI_sumZero⟩

end EKPinsInst

end RBM.BA

end
