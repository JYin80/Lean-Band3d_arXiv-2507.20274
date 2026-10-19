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
# Evolution kernel estimates at the block Anderson model

The evolution kernel, the statements of `lem:sum_Ndecay` and `lem:sum_decay`, and the `Ξ` bounds at BA.

Paper: Subappendix A.2 (`ks`: `(eq:decompUalt)`, `(Xi_infint)`, `(eq:decayXi)`), Subsection 4.4 (`ks-statements`).

1. Vocabulary: `BAuKer` (`(1 - s M^{(σ₁σ₂)}) Θ_t^{(σ₁σ₂)}`, (3.12) `def_Ustz`), `BAUN` (`(def_Ustz)`),
   `BAXi` (`Ξ = (t - s) M Θ_t`), and the identities `BAuKer_eq_one_add` (`(eq:decompUalt)`) and
   `BAuKer_convex`.
2. The four kernel-sum statements `BAEKSumNdecay`, `BAEKSumDecay1`, `BAEKSumDecayNAL`, `BAEKSumDecay2`: the shape of
   the corresponding statements of `Evolution/Pins.lean` with `BAReal d L g κ E m` in
   place of `‖m‖ = 1` and no propagator antecedent (`baProp5to8_holds`).
3. `baEKSumNdecay_holds`: `‖Ξ‖_{∞→∞} ≤ (t - s)/(1 - t)` from the Ward row sums
   (`BAMss_norm_eq_BAK`, `BAK_row_sum`), then the product over the `n` factors.
4. The BA `Ξ` statements `BAEKXiDecay`, `BAEKXiBall`, `BAEKSameRow` and their proofs, from
   `BAuKer_convex`, `baProp5_holds` and `baProp5s_holds` (no `Mbound_AO`).

The names of the private helpers begin with EKPins_.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

noncomputable section

open RBM

namespace RBM.BA

/-! ## 1. Vocabulary -/

/-- The one-index kernel `(1 - s M^{(σ₁σ₂)}) Θ_t^{(σ₁σ₂)}` ((3.12) `def_Ustz`). -/
def BAuKer (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - (s : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) * BATheta d L g E m t σ₁ σ₂

/-- The evolution kernel `U^{(n)}_{s,t,σ}` of `(def_Ustz)`, cyclic `σ_{n+1} = σ₁`. -/
def BAUN (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) {n : ℕ} (σ : Fin n → Bool) (s t : ℝ)
    (A : (Fin n → Zd d L) → ℂ) : (Fin n → Zd d L) → ℂ :=
  fun a => ∑ b : Fin n → Zd d L, (∏ i, BAuKer d L g E m s t (σ i) (σ (finRotate n i)) (a i) (b i)) * A b

/-- `Ξ = (t - s) M^{(σ₁σ₂)} Θ_t^{(σ₁σ₂)}` of `(eq:decompUalt)`. -/
def BAXi (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (s t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  ((t : ℂ) - s) • (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂)

/-- `(eq:decompUalt)` for the block Anderson kernel, `Ξ = (t - s) M Θ_t`: from `Θ = 1 + t M Θ`. -/
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

/-! ## 2. The four kernel-sum statements (shape of `Evolution/Pins.lean`, `BAReal d L g κ E m` for `‖m‖ = 1`) -/

/-- `lem:sum_Ndecay` (Lemma 4.15): `‖U^{(n)}_{s,t,σ} ∘ 𝒜‖_∞ ≤ ((1-s)/(1-t))^n ‖𝒜‖_∞`; the proof is Ward row sums
(`BAK_row_sum`) and `|M^{(σσ')}_{ab}| = BAK_{ab}` (`BAMss_norm_eq_BAK`). -/
def BAEKSumNdecay (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ A : (Fin n → Zd d L) → ℂ,
      ‖BAUN d L g E m σ s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖

/-- (4.53) `sum_res_1`, any `σ`. -/
def BAEKSumDecay1 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A →
          ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * (ellT L g t ^ 2 / ellT L g s ^ 2) *
            ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-- (4.54) `sum_res_2_NAL`: non-alternating `σ`. -/
def BAEKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) → ∀ A : (Fin n → Zd d L) → ℂ,
          EKFastDecay g s W ε D A → ‖BAUN d L g E m σ s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)

/-- (4.55) `sumAzero` ⟹ (4.56) `sum_res_2`; `log L ≤ W^ε` is the `d = 3` absorption of (A.19) `eq:latticesum_d3`,
`L^d ≤ W^K` is (2.9) `Main_DEL_COND`. -/
def BAEKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ K : ℝ, 0 < K → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
      Real.log L ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
      ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ, EKFastDecay g s W ε D A → EKSumZero A →
          ‖BAUN d L g E m σ s t A‖ ≤ W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-! ## 3. `lem:sum_Ndecay` at BA: `(Xi_infint)` and the product bound -/

section Ndecay

open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L]

/-- `|Q_ab| = BAK_ab` and the Ward row sums of `BAK` give `‖M^{(σ₁σ₂)}‖_{∞→∞} ≤ 1` (`(eq:WardM)`; `BAMss_norm_eq_BAK`,
`BAK_row_sum`; as the private `BAKBase_norm`). -/
theorem EKPins_norm_Q_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ ≤ 1 := by
  have h : ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa [BAMss_norm_eq_BAK] using (BAK_row_sum d L g E m hr.1 a).le
  exact_mod_cast h

/-- `(eq:THETAinftinf)`: `‖Θ_t‖_{∞→∞} ≤ 1/(1 - t)` from `Θ = 1 + t M Θ` and `‖M‖ ≤ 1`. -/
theorem EKPins_norm_Theta_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
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
theorem EKPins_norm_uKer_le {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {s t : ℝ} (hs : 0 ≤ s)
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

/-- **`lem:sum_Ndecay` for the block Anderson model**: `(Xi_infint)`, the bound `(1 - s)/(1 - t)` of each
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

/-! ## 4. The BA `Ξ` statements (`(eq:decayXi)`, ball sums, `(eq:samecolor)`; band forms in `Evolution/XiPins.lean`) -/

section XiPins

open scoped Matrix.Norms.Operator

/-- `(eq:decayXi)` for `Ξ = (t - s) M^{(σ₁σ₂)} Θ_t^{(σ₁σ₂)}`, uniform in `g ∈ (0, Λ]` and in the bulk
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

/-- (A.20) `eq:samecolor`: at a same-sign index the one-index factor `(1 - s M^{(σσ)}) Θ_t^{(σσ)}` is bounded in the
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

/-- `M^{(σ₁σ₂)}` is invariant under the diagonal shift (`BAMB_shift`; `M(-) = M^*`). -/
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

/-- `Θ_t(a + r, b + r) = Θ_t(a, b)`, every `(σ₁, σ₂)` (the pattern of `BAMB_shift`; as the private
`baP8_BATheta_shift` of `BA/Prop6Path.lean`). -/
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
/-- The zero mode is absorbed in the decay profile (`zeroMode_le_of_ge_mul`,
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

/-- The ball-sum step of `lem:sum_decay`, generic in the entries `X b` (the analogue of `ek_sum_ball_norm_XiKer_le` of
`Evolution/XiPins.lean`: only the pointwise bound on `‖Ξ_{ab}‖` is read): `Σ_{b ∈ D} ‖X b‖ ≤ 4 C₀ ballC Λ'² (ĝ²+|1-s|)/(ĝ²+|1-t|)`
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

/-- **`(eq:decayXi)` at BA**, from `BAuKer_convex` (`Ξ_{ab} = ((t-s)/t) Θ_{t,ab}`, `a ≠ b`) and `baProp5_holds`;
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

/-- **Ball sums of `Ξ` at BA** (third step of `(sum_res_deriv_red)`): from `baEKXiDecay_holds`. -/
theorem baEKXiBall_holds (d : ℕ) (Λ κ : ℝ) : BAEKXiBall d Λ κ := by
  intro hd hΛ hκ
  obtain ⟨C₀, c, hC₀, hc, hdec⟩ := baEKXiDecay_holds d Λ κ hd hΛ hκ
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨4 * C₀ * ballC k, mul_pos (by positivity) (ballC_pos k), ?_⟩
  intro L hL g hg hgΛ E m hr s t hs hst ht hgt σ₁ σ₂ Λ' hΛ' R hR hRℓ a ctr D hD
  have : NeZero L := ⟨by omega⟩
  exact EKPins_sum_ball_le (L := L) hL hg hC₀ hc hs hst ht a ctr _
    (fun b => hdec L hL g hg hgΛ E m hr s t hs hst ht hgt σ₁ σ₂ a b) hΛ' hR hRℓ D hD

/-- **`(eq:samecolor)` at BA**: `‖(1 - s M^{(σσ)}) Θ_t^{(σσ)}‖_{∞→∞} ≤ 1 + ‖Θ_t^{(σσ)}‖`, `‖Θ‖ ≤ Σ_b |Θ(0,b)|`
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
end RBM.BA

end
