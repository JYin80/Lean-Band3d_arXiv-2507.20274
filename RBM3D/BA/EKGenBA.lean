/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.NQGood1Gen
import RBM3D.Induction.QProxy
import RBM3D.BA.EKPins
import RBM3D.BA.EKSum
import RBM3D.BA.EKNonzero
import RBM3D.BA.TwistKer
import RBM3D.BA.TwistStep2
import RBM3D.BA.GreenSchur
import RBM3D.BA.EMn2BA
import RBM3D.BA.SEforLnBA

/-!
# The block Anderson kernel layer of the evolution-kernel sum estimates

Paper: arXiv:2507.20274, Lemma 4.15 (`lem:sum_Ndecay`), Lemma 4.16 (`lem:sum_decay`) and Lemma 4.17 (`lem:sum_decay_nonzero`)
of Subsection 4.4, read at the block Anderson model (the proof of Steps 3-6 of Theorem 8.2, `lem:main_ind_BA`: the
proofs extend verbatim).  A leaf file.

BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; `gK = BAflowLam0`; `Aof κ = (κ+1)/κ`.

* 1. `BAEKKer` (the only public `def`): the model class of the kernel hypotheses, `STEKKer d`-typed.
* 2. `baEKKer_flow`: the `hKer` bundle (`κm = κ`, the class, the window and the comparison of `g₀` with `λ`) of
  `stExpIniIgL'_of`, `stExpIntIIgL_of` at the BA family.
* 3. the forms `baEKSumNdecaygL_holds`, `baEKSumRes2NALgL_holds`, `baEKSumRes2gL_holds`, `baEKNonzerogL_holds` at `@BAEKKer d`: the class is unpacked,
  `Step2Kern_UN_BA` turns `Step2Gen_UN` into `BAUN`, the corresponding estimate for `BAUN` is applied at `g = gK n`, and the
  `≺` lift is the private core `EKGenBA_core`, the analogue of the private band-typed `prec_core` (`Evolution/Prec.lean`) at a law
  `μ` and a kernel coupling `gK`; `prec_L_pow_le`, `prec_log_le` are re-proved as `EKGenBA_L_pow_le`, `EKGenBA_log_le`.
* 4. `baEKSumDecayNonzeroA_holds`: the form of `lem:sum_decay_nonzero` with the threshold `(1 - s) L² ≤ A g²`, every `A > 0`.
* 5. `baNQGoodGen_kerNAL`, `baQProxyG_kerEK4`: the deterministic kernel classes at the BA family.

The comparison of `g₀` with `λ` is stated once, in `baEKKer_flow`, and used in no proof here.  The names of the private helpers
begin with EKGenBA_.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The class `BAEKKer` and the flow bundle -/

/-- **`BAEKKer`**: the carrier `C` is the BA carrier at the coupling `gK` with the real energies `E`
and bulk data `BAReal` at every `n` (bulk parameter `κ`); the kernel `Step2Gen_UN C` is then `BAUN` (`Step2Kern_UN_BA`).  There is
no window field: the window is the forms' own `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`.  It has the type `STEKKer d` when read as `@BAEKKer d`. -/
def BAEKKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n)

/-- **`baEKKer_flow`**: the `hKer` bundle at the BA family with `κm = κ`: `κ ≤ Im m` at every `n`
(`EMn2BA_mF_data`), the class at the flow carrier (`BAflow_real`), the window (`BAflow_lam0_window`), and the comparison
`g₀² ≤ λ²`, `λ² ≤ ((κ+1)/κ) g₀²` (`TwistStep2_lam0_sq`) with `0 ≤ g₀ λ`. -/
theorem baEKKer_flow (d : ℕ) : ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    (∀ n, κm ≤ ((baFMz sz z).m n).im) ∧ BAEKKer sz (baFMz sz z) (BAflowLam0 sz z) κm ∧
      (∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹) ∧
      ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
        sz.lam n ^ 2 ≤ (κm + 1) / κm * BAflowLam0 sz z n ^ 2 := by
  intro κ hκ
  refine ⟨κ, hκ, fun sz ε 𝔠 𝔡 z hflow => ⟨fun n => (EMn2BA_mF_data sz hflow n).1,
    ⟨BAflowEs sz z, rfl, fun n => BAflow_real κ ε 𝔠 𝔡 sz z hflow n⟩, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow, fun n => ?_⟩⟩
  have h := TwistStep2_lam0_sq hκ hflow n
  refine ⟨?_, h.1, h.2⟩
  have e : BAflowLam0 sz z n * sz.lam n = Real.sqrt (BAflowT0 sz z n) * (sz.lam n * sz.lam n) := by
    unfold BAflowLam0; ring
  rw [e]
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_self_nonneg _)

/-! ## 2. The `≺` lift: the private band helpers of `Evolution/Prec.lean` at a law `μ` and a kernel coupling `gK`

Copies (text of the private helpers of `Prec.lean`, `Sizes`-only, no band object): `EKGenBA_W_rpow_ge` (`prec_W_rpow_ge`), `EKGenBA_one_lt_W`
(`prec_one_lt_W`), `EKGenBA_L_pow_le` (`prec_L_pow_le`), `EKGenBA_log_le` (`prec_log_le`), `EKGenBA_window` (`prec_window`),
`EKGenBA_ratio_ge_one` (`prec_ratio_ge_one`); `EKGenBA_core` is `prec_core` with `Prec sz` read as `PrecL sz μ`,
`STEKDecay` as `STEKDecayKgL gK μ`, `STEKLow` as `STEKLowgL μ`, `Prec.whp` as `StochDomAt.highProb`, and `EKFastDecay (sz.lam n)` as
`EKFastDecay (gK n)`; no measure-theoretic hypothesis beyond the `StochDomAt` calculus (all lemmas are stated for any measure). -/

section Lift

/-- `M ≤ W^a` eventually, for `a > 0`: `W ≥ N^𝔠 → ∞` (`prec_W_rpow_ge`). -/
private theorem EKGenBA_W_rpow_ge {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hSz : sz.SizeTendsto)
    (hBw : sz.Bandwidth 𝔠) {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∀ᶠ n in atTop, M ≤ ((sz.W n : ℕ) : ℝ) ^ a := by
  have hf : ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) :=
    ((tendsto_rpow_atTop (mul_pos h𝔠 ha)).comp hSz).eventually (eventually_ge_atTop M)
  filter_upwards [hf, hBw] with n hn hb
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  calc M ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * a) := hn
    _ = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ a := Real.rpow_mul hN _ _
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ a := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hb ha.le

/-- `4 ≤ W^ε` (with `ε > 0`) gives `1 < W` (`prec_one_lt_W`). -/
private theorem EKGenBA_one_lt_W {W ε : ℝ} (hW0 : 0 ≤ W) (hε : 0 < ε) (h4 : 4 ≤ W ^ ε) : 1 < W := by
  by_contra hcon
  push Not at hcon
  have := Real.rpow_le_one hW0 hcon hε.le
  linarith

/-- `L^d ≤ N ≤ W^{1/𝔠}` from `W ≥ N^𝔠` (`prec_L_pow_le`). -/
private theorem EKGenBA_L_pow_le {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (n : ℕ)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) :
    ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := by
  have hLW : (sz.L n) ^ d ≤ sz.size n := by
    have hW : 0 < sz.W n := sz.W_pos n
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) d
  have h1 : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hLW
  have h2 := sz.size_rpow_le_W_rpow h𝔠 n hb (τ := 1) zero_le_one
  rw [Real.rpow_one] at h2
  exact h1.trans h2

/-- `log L ≤ W^ε` from `L^d ≤ W^K` and `W^{ε/2} ≥ 2K/(ε d)` (`prec_log_le`). -/
private theorem EKGenBA_log_le {L W K ε : ℝ} {d : ℕ} (hd0 : 0 < d) (hL : 0 ≤ L) (hK : 0 < K) (hε : 0 < ε)
    (hW : 0 < W) (hLK : L ^ d ≤ W ^ K) (hM : 2 * K / (ε * d) ≤ W ^ (ε / 2)) : Real.log L ≤ W ^ ε := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd0
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε * d / (2 * K) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have h1 : Real.log L ≤ L ^ a / a := Real.log_le_rpow_div hL ha0
  have h2 : L ^ a ≤ W ^ (ε / 2) := by
    calc L ^ a = (L ^ (d : ℝ)) ^ (a / d) := by
          rw [← Real.rpow_mul hL]; congr 1; field_simp
      _ = (L ^ d) ^ (a / d) := by rw [Real.rpow_natCast]
      _ ≤ (W ^ K) ^ (a / d) := Real.rpow_le_rpow (pow_nonneg hL _) hLK (by positivity)
      _ = W ^ (ε / 2) := by
          rw [← Real.rpow_mul hW.le]; congr 1; rw [ha]; field_simp
  have hinv : 1 / a = 2 * K / (ε * d) := by rw [ha]; field_simp
  calc Real.log L ≤ L ^ a / a := h1
    _ ≤ W ^ (ε / 2) / a := div_le_div_of_nonneg_right h2 ha0.le
    _ = W ^ (ε / 2) * (2 * K / (ε * d)) := by rw [div_eq_mul_one_div, hinv]
    _ ≤ W ^ (ε / 2) * W ^ (ε / 2) := mul_le_mul_of_nonneg_left hM (Real.rpow_nonneg hW.le _)
    _ = W ^ ε := by rw [← Real.rpow_add hW]; congr 1; ring

/-- The window `W⁻¹ ≤ (1-t)/(1-s)` passes to every `v ∈ [s,t]` (`prec_window`). -/
private theorem EKGenBA_window {W s t v : ℝ} (hsv : s ≤ v) (hvt : v ≤ t) (ht : t < 1)
    (hW : W⁻¹ ≤ (1 - t) / (1 - s)) : W⁻¹ ≤ (1 - t) / (1 - v) :=
  hW.trans (div_le_div_of_nonneg_left (by linarith) (by linarith : 0 < 1 - v) (by linarith))

/-- The ratio `(g²+|1-v|)/(g²+|1-t|) ≥ 1` for `v ≤ t < 1` (`prec_ratio_ge_one`). -/
private theorem EKGenBA_ratio_ge_one {g v t : ℝ} (hvt : v ≤ t) (ht : t < 1) :
    1 ≤ (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - t|) := by
  have h1 : 0 < 1 - t := by linarith
  have h0 : 0 < g ^ 2 + |1 - t| := by
    have : 0 < |1 - t| := abs_pos.2 h1.ne'
    positivity
  rw [one_le_div h0]
  have : |1 - t| ≤ |1 - v| := by
    rw [abs_of_pos h1, abs_of_pos (by linarith : 0 < 1 - v)]; linarith
  linarith

/-- **The shared absorption step** (`prec_core`) at a law `μ` and a kernel coupling `gK`: an estimate of the shape
`f ≤ W^{Cε} ρ ‖𝒜‖ + W^{-D₀+C}` (for `EKFastDecay (gK n)` data) with `ρ ≥ 1` gives `f ≺ ρ X` from `‖𝒜‖ ≺ X`, `X ≥ N^{-b}` w.h.p.
and the decay hypothesis w.h.p.; `ε = min(1/2, τ d/(4C))`, `D₀ = C + 1 + D/𝔠`. -/
private theorem EKGenBA_core {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (hd0 : 0 < d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hSz : sz.SizeTendsto) (hBw : sz.Bandwidth 𝔠) {s t : ℕ → ℝ} {k : ℕ} (gK : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin k → Zd d (sz.L n)) → ℂ) (hdec : STEKDecayKgL gK μ s t 𝒜)
    (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) (hlow : STEKLowgL μ s t X)
    (hdom : PrecL sz μ (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X)
    (f : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) (ρ : ∀ n, TimeIcc s t n → ℝ) {C : ℝ} (hC : 0 < C)
    (hρ : ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, 1 ≤ ρ n v)
    (hpin : ∀ ε D₀ : ℝ, 0 < ε → ε < 1 → 1 < D₀ → ∀ᶠ n in atTop,
      ∀ (v : TimeIcc s t n) (ω : sz.SeqΩ),
        EKFastDecay (gK n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D₀ (𝒜 n v ω) →
        f n v ω ≤ ((sz.W n : ℕ) : ℝ) ^ (C * ε) * ρ n v * ‖𝒜 n v ω‖ + ((sz.W n : ℕ) : ℝ) ^ (-D₀ + C)) :
    PrecL sz μ (U := fun n => TimeIcc s t n) f (fun n v ω => ρ n v * X n v ω) := by
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hSz
  obtain ⟨b, hb⟩ := hlow
  refine StochDomAt.of_highProbAt_add_rpow_neg (b := b) hsize ?_ ?_
  · refine Gauss.HighProbAt.mono hb ?_
    filter_upwards [hρ] with n hρn ω hω v
    have hXn := hω v
    have hX0 : 0 ≤ X n v ω := le_trans (Real.rpow_nonneg (Nat.cast_nonneg _) _) hXn
    calc ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω := hXn
      _ = 1 * X n v ω := by ring
      _ ≤ _ := by gcongr; exact hρn v
  · intro τ hτ D hD
    have hε0 : 0 < min (1 / 2 : ℝ) (τ * d / (4 * C)) := lt_min (by norm_num) (by positivity)
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (1 / 2 : ℝ) (τ * d / (4 * C)) := ⟨_, rfl⟩
    rw [← hεdef] at hε0
    have hε1 : ε < 1 := by rw [hεdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεle : ε ≤ τ * d / (4 * C) := by rw [hεdef]; exact min_le_right _ _
    have hCε : C * ε / d ≤ τ / 4 := by
      rw [div_le_iff₀ (by exact_mod_cast hd0)]
      calc C * ε ≤ C * (τ * d / (4 * C)) := by gcongr
        _ = τ / 4 * d := by field_simp
    have hD₀ : 1 < C + 1 + D / 𝔠 := by
      have : 0 < D / 𝔠 := by positivity
      linarith
    have hE1 := hdec ε (C + 1 + D / 𝔠) hε0 (by linarith)
    have hE2 := StochDomAt.highProb hdom (τ := τ / 4) (by positivity)
    refine Gauss.HighProbAt.mono (Gauss.HighProbAt.inter hsize hE1 hE2) ?_
    have hf1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
      Eventually.of_forall fun n => by exact_mod_cast sz.one_le_size n
    filter_upwards [hf1, hBw, hpin ε (C + 1 + D / 𝔠) hε0 hε1 hD₀, hρ] with n h1 h2 hpn hρn
    intro ω hω v
    obtain ⟨hω1, hω2⟩ := hω
    have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hpv := hpn v ω (hω1 v)
    have ha : ((sz.W n : ℕ) : ℝ) ^ (C * ε) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
      (sz.W_rpow_le hd0 n (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le h1 hCε)
    have hy := hω2 v
    have hw : ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
      have e1 : -(C + 1 + D / 𝔠) + C = -(1 + D / 𝔠) := by ring
      rw [e1]
      have hneg : -(1 + D / 𝔠) ≤ 0 := by
        have : 0 < D / 𝔠 := by positivity
        linarith
      calc ((sz.W n : ℕ) : ℝ) ^ (-(1 + D / 𝔠)) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(1 + D / 𝔠)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h2 hneg
        _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-(1 + D / 𝔠))) := by rw [← Real.rpow_mul hNpos.le]
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
            refine Real.rpow_le_rpow_of_exponent_le h1 ?_
            have : 𝔠 * (-(1 + D / 𝔠)) = -𝔠 - D := by field_simp; ring
            rw [this]; linarith
    have hNq : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := Real.rpow_pos_of_pos hNpos _
    have hX0 : 0 ≤ X n v ω := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_pos_of_neg hNq hneg
      linarith [norm_nonneg (𝒜 n v ω)]
    have hr0 : 0 ≤ ρ n v := le_trans zero_le_one (hρn v)
    have hq : ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hNpos]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    calc f n v ω
        ≤ ((sz.W n : ℕ) : ℝ) ^ (C * ε) * ρ n v * ‖𝒜 n v ω‖ +
          ((sz.W n : ℕ) : ℝ) ^ (-(C + 1 + D / 𝔠) + C) := hpv
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ρ n v) * (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * X n v ω) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul (mul_le_mul_of_nonneg_right ha hr0) hy (norm_nonneg _)
            (mul_nonneg hNq.le hr0)) hw
      _ = (((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) * (ρ n v * X n v ω) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (ρ n v * X n v ω) + ((sz.size n : ℕ) : ℝ) ^ (-D) :=
          add_le_add (mul_le_mul_of_nonneg_right hq (mul_nonneg hr0 hX0)) le_rfl

end Lift

/-! ## 3. The A-form of `lem:sum_decay_nonzero` at BA -/

section NonzeroA

open scoped Matrix.Norms.Operator

/-- **`baEKSumDecayNonzeroA_holds`**: the form of `lem:sum_decay_nonzero` at BA with the threshold `1 - g²/L² ≤ s`
replaced by `(1 - s) L² ≤ A g²`, every `A > 0`.  The product step is that of the proof of `lem:sum_decay_nonzero` at BA (`BA/EKNonzero`): a same-sign index
carries `baEKSameRow_holds`, an index of `A` carries `baTwKerZero_holds` (`BATwKerZero` takes any `A > 0`); the constant is `Ci ^ n`,
`Ci = max Cs Cz`, depending on `(d, n, Λ, κ, A)` only. -/
theorem baEKSumDecayNonzeroA_holds (d n : ℕ) (Λ κ : ℝ) :
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ → ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ s t : ℝ, 0 ≤ s → (1 - s) * (L : ℝ) ^ 2 ≤ A * g ^ 2 → s ≤ t → t < 1 →
        ∀ (E : ℝ) (m : ℂ), haveI : NeZero L := ⟨by omega⟩
          BAReal d L g κ E m → ∀ σ : Fin n → Bool, ∀ Aset : Finset (Fin n), (∀ i, σ i ≠ σ (finRotate n i) → i ∈ Aset) →
            ∀ 𝒜 : (Fin n → Zd d L) → ℂ, ‖zeroModeSet d L Aset (BAUN d L g E m σ s t 𝒜)‖ ≤ C * ‖𝒜‖ := by
  intro hd _hn hΛ hκ A hA
  obtain ⟨Cs, hCs, hsame⟩ := baEKSameRow_holds d Λ κ hd hΛ hκ
  obtain ⟨Cz, hCz, hzero⟩ := baTwKerZero_holds d Λ κ hd hΛ hκ A hA
  set Ci : ℝ := max Cs Cz with hCi
  have hCi0 : 0 < Ci := lt_of_lt_of_le hCs (le_max_left _ _)
  refine ⟨Ci ^ n, pow_pos hCi0 n, ?_⟩
  intro L hL g hg hgΛ s t hs hthr hst ht E m hr σ Aset hAset 𝒜
  have : NeZero L := ⟨by omega⟩
  have key : ∀ i : Fin n,
      ‖(if i ∈ Aset then projMat d L * BAuKer d L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer d L g E m s t (σ i) (σ (finRotate n i)))‖ ≤ Ci := by
    intro i
    by_cases hi : i ∈ Aset
    · simp only [hi, ite_true]
      exact (hzero L hL g hg hgΛ E m hr (σ i) (σ (finRotate n i)) s t hs hthr hst ht).trans (le_max_right _ _)
    · have hσ : σ i = σ (finRotate n i) := by
        by_contra hne
        exact hi (hAset i hne)
      simp only [hi, ite_false]
      rw [← hσ]
      exact (hsame L hL g hg hgΛ E m hr (σ i) s t hs hst ht).trans (le_max_left _ _)
  have hUN : BAUN d L g E m σ s t 𝒜
      = tensorKer d L (fun i : Fin n => BAuKer d L g E m s t (σ i) (σ (finRotate n i))) 𝒜 := rfl
  rw [hUN, zeroModeSet_tensorKer]
  calc ‖tensorKer d L
        (fun i => if i ∈ Aset then projMat d L * BAuKer d L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer d L g E m s t (σ i) (σ (finRotate n i))) 𝒜‖
      ≤ (∏ i, ‖(if i ∈ Aset then projMat d L * BAuKer d L g E m s t (σ i) (σ (finRotate n i))
          else BAuKer d L g E m s t (σ i) (σ (finRotate n i)))‖) * ‖𝒜‖ := norm_tensorKer_le _ _
    _ ≤ (∏ _i : Fin n, Ci) * ‖𝒜‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => key i
    _ = Ci ^ n * ‖𝒜‖ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end NonzeroA

/-! ## 4. The five forms at `@BAEKKer d`, law `seqP (sz.withLam 0)` -/

section Forms

/-- `Im (E + m) ≠ 0` from the bulk datum `κ ≤ Im m`, `0 < κ` (the hypothesis `hIm` of `Step2Kern_UN_BA`). -/
private theorem EKGenBA_hIm {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) :
    (((E : ℝ) : ℂ) + m).im ≠ 0 := by
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  exact (hκ.trans_le hr.2).ne'

/-- **`baEKSumNdecaygL_holds`** from `baEKSumNdecay_holds`; the band version is
`stek_sumNdecay_holds`, so no core is needed. -/
theorem baEKSumNdecaygL_holds (d : ℕ) : STEKSumNdecaygL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hE⟩ hg s t hs hst ht σ 𝒜 X hX hdom
  subst hC
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hAdm.2.2.1
  have hr : ∀ n (v : TimeIcc s t n), 0 ≤ (1 - (v : ℝ)) / (1 - t n) := fun n v =>
    div_nonneg (by linarith [(v.2).2, ht n, hst n]) (by linarith [ht n])
  have h1 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n)
      (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * ‖𝒜 n v ω‖)
      (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * X n v ω) :=
    StochDomAt.mul (ξ₁ := fun n (v : TimeIcc s t n) (_ : sz.SeqΩ) => ((1 - (v : ℝ)) / (1 - t n)) ^ n_)
      (ξ₂ := fun n v ω => ‖𝒜 n v ω‖) (ζ₁ := fun n (v : TimeIcc s t n) (_ : sz.SeqΩ) => ((1 - (v : ℝ)) / (1 - t n)) ^ n_)
      (ζ₂ := X) hsize (fun _ _ _ => norm_nonneg _) (fun n v _ => pow_nonneg (hr n v) _)
      (StochDomAt.refl hsize (fun n v _ => pow_nonneg (hr n v) _)) hdom
  refine StochDomAt.of_subset h1 fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hg] with n hn' ω hω
  obtain ⟨v, hv⟩ := hω
  refine ⟨v, lt_of_lt_of_le hv ?_⟩
  beta_reduce
  rw [Step2Kern_UN_BA sz gK E n (EKGenBA_hIm hκ (hE n))]
  exact baEKSumNdecay_holds d n_ 𝔡⁻¹ κ hd hn (sz.L n) (sz.three_le_L n) (gK n) hn'.1 hn'.2 (E n) _ (hE n) σ
    (v : ℝ) (t n) (hs n |>.trans (v.2).1) (v.2).2 (ht n) (𝒜 n v ω)

/-- **`baEKSumRes2NALgL_holds`** from `baEKSumDecayNAL_holds`; the ratio is at `(n_ - 1)`. -/
theorem baEKSumRes2NALgL_holds (d : ℕ) : STEKSumRes2NALgL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hE⟩ hg s t hwin σ hσ 𝒜 hdec X hlow hdom
  subst hC
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : 0 < d := by omega
  obtain ⟨Cc, hCc, hpin⟩ := baEKSumDecayNAL_holds d n_ 𝔡⁻¹ κ hd hn hΛ hκ
  refine EKGenBA_core sz _ hd0 h𝔠 hSz hBw gK 𝒜 hdec X hlow hdom
    (fun n v ω => ‖Step2Gen_UN (baFM sz gK E) n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
    (fun n v => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ (n_ - 1)) hCc ?_ ?_
  · exact Eventually.of_forall fun n v => one_le_pow₀ (EKGenBA_ratio_ge_one (v.2).2 (ht1 n))
  · intro ε D₀ hε0 hε1 hD₀
    filter_upwards [EKGenBA_W_rpow_ge sz h𝔠 hSz hBw hε0 4, hg, hW] with n h4 hgn hWn v ω hdecay
    have hWpos : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW1 := EKGenBA_one_lt_W hWpos hε0 h4
    rw [Step2Kern_UN_BA sz gK E n (EKGenBA_hIm hκ (hE n))]
    exact hpin (sz.L n) (sz.three_le_L n) (gK n) hgn.1 hgn.2 ((sz.W n : ℕ) : ℝ) ε D₀
      hW1 hε0 hε1 hD₀ h4 (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n)
      (EKGenBA_window (v.2).1 (v.2).2 (ht1 n) hWn) (E n) _ (hE n) σ hσ (𝒜 n v ω) hdecay

/-- **`baEKSumRes2gL_holds`** from `baEKSumDecay2_holds`, `K = 1/𝔠`: `L^d ≤ W^K`
from `W ≥ N^𝔠` and `log L ≤ W^ε` from it (eventually, `W → ∞`). -/
theorem baEKSumRes2gL_holds (d : ℕ) : STEKSumRes2gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hE⟩ hg s t hwin σ 𝒜 hdec hzero X hlow hdom
  subst hC
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : 0 < d := by omega
  have hK : 0 < 1 / 𝔠 := one_div_pos.2 h𝔠
  obtain ⟨Cc, hCc, hpin⟩ := baEKSumDecay2_holds d n_ 𝔡⁻¹ κ hd hn hΛ hκ (1 / 𝔠) hK
  refine EKGenBA_core sz _ hd0 h𝔠 hSz hBw gK 𝒜 hdec X hlow hdom
    (fun n v ω => ‖Step2Gen_UN (baFM sz gK E) n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
    (fun n v => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ n_) hCc ?_ ?_
  · exact Eventually.of_forall fun n v => one_le_pow₀ (EKGenBA_ratio_ge_one (v.2).2 (ht1 n))
  · intro ε D₀ hε0 hε1 hD₀
    filter_upwards [EKGenBA_W_rpow_ge sz h𝔠 hSz hBw hε0 4,
      EKGenBA_W_rpow_ge sz h𝔠 hSz hBw (half_pos hε0) (2 * (1 / 𝔠) / (ε * d)), hg, hW, hBw]
      with n h4 hM hgn hWn hb v ω hdecay
    have hWpos : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW1 := EKGenBA_one_lt_W hWpos hε0 h4
    have hLK := EKGenBA_L_pow_le sz h𝔠 n hb
    have hlog : Real.log ((sz.L n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
      EKGenBA_log_le hd0 (Nat.cast_nonneg _) hK hε0 (by linarith) hLK hM
    rw [Step2Kern_UN_BA sz gK E n (EKGenBA_hIm hκ (hE n))]
    exact (hpin (sz.L n) (sz.three_le_L n) (gK n) hgn.1 hgn.2 ((sz.W n : ℕ) : ℝ) ε D₀
      hW1 hε0 hε1 hD₀ h4 hlog hLK (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n)
      (EKGenBA_window (v.2).1 (v.2).2 (ht1 n) hWn) (E n) _ (hE n)
      σ (𝒜 n v ω) hdecay (hzero n v ω)).trans (le_of_eq (by ring))

/-- **`baEKNonzerogL_holds`**, for every `Aof` (the A-form): from `baEKSumDecayNonzeroA_holds` at `A = Aof κ ≥ 1`; the
threshold `(1 - v) L² ≤ (1 - s) L² ≤ Aof κ · gK²` passes to every `v ∈ [s, t]`, and the constant `C` is absorbed by
`StochDomAt.const_mul_left`. -/
theorem baEKNonzerogL_holds (d : ℕ) (Aof : ℝ → ℝ) :
    STEKNonzerogL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) Aof := by
  intro hd n_ hn κ 𝔠 𝔡 hκ hA sz hAdm C gK ⟨E, hC, hE⟩ hg s t hthr hs hst ht σ Aset hAset 𝒜 X hX hdom
  subst hC
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hSz
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨Cc, hCc, hpin⟩ := baEKSumDecayNonzeroA_holds d n_ 𝔡⁻¹ κ hd hn hΛ hκ (Aof κ) (by linarith)
  have h1 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n) (fun n v ω => Cc * ‖𝒜 n v ω‖) X :=
    StochDomAt.const_mul_left hsize hCc.le hX hdom
  refine StochDomAt.of_subset h1 fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hg] with n hgn ω hω
  obtain ⟨v, hv⟩ := hω
  refine ⟨v, lt_of_lt_of_le hv ?_⟩
  beta_reduce
  rw [Step2Kern_UN_BA sz gK E n (EKGenBA_hIm hκ (hE n))]
  have hvthr : (1 - (v : ℝ)) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ Aof κ * gK n ^ 2 :=
    (mul_le_mul_of_nonneg_right (by linarith [(v.2).1]) (sq_nonneg _)).trans (hthr n)
  exact hpin (sz.L n) (sz.three_le_L n) (gK n) hgn.1 hgn.2 (v : ℝ) (t n) ((hs n).trans (v.2).1) hvthr (v.2).2 (ht n)
    (E n) _ (hE n) σ Aset hAset (𝒜 n v ω)

end Forms

/-! ## 5. The deterministic kernel classes at the BA family -/

section D1

/-- **`baNQGoodGen_kerNAL`**: `NQGoodGen_KerNALFam` at the BA family, `Ck` from
`baEKSumDecayNAL_holds d k 𝔡⁻¹ κ`; the class is read at every `n` with `0 < g₀ n ≤ 𝔡⁻¹` (`BAflow_lam0_window`, eventually). -/
theorem baNQGoodGen_kerNAL (d : ℕ) :
    NQGoodGen_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) := by
  intro hd k hk κ ε 𝔡 hκ hε h𝔡
  obtain ⟨Ck, hCk, hpin⟩ := baEKSumDecayNAL_holds d k 𝔡⁻¹ κ hd hk (inv_pos.2 h𝔡) hκ
  refine ⟨Ck, hCk, fun sz 𝔠 z hflow => ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro hW ε' D hε0 hε1 hD hWε s t hs hst ht hWt σ hσ A hA
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  change ‖Step2Gen_UN (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n σ s t A‖ ≤ _
  rw [Step2Kern_UN_BA sz _ _ n (EKGenBA_hIm hκ hr)]
  exact hpin (sz.L n) (sz.three_le_L n) (BAflowLam0 sz z n) hn.1 hn.2 ((sz.W n : ℕ) : ℝ) ε' D hW hε0 hε1 hD hWε s t hs hst ht hWt
    (BAflowEs sz z n) _ hr σ hσ A hA

/-- **`baQProxyG_kerEK4`**: `QProxyG_KerEK4Fam` at the BA family, `C4` from
`baEKSumDecay2_holds d k 𝔡⁻¹ κ … KL`. -/
theorem baQProxyG_kerEK4 (d : ℕ) :
    RBM.Ind.QProxyG_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) := by
  intro hd k hk κ ε 𝔡 KL hκ hε h𝔡 hKL
  obtain ⟨C4, hC4, hpin⟩ := baEKSumDecay2_holds d k 𝔡⁻¹ κ hd hk (inv_pos.2 h𝔡) hκ KL hKL
  refine ⟨C4, hC4, fun sz 𝔠 z hflow => ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro hW hLK ε' D hε0 hε1 hD hWε hlog s t hs hst ht hWt σ A hA hsum
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  change ‖Step2Gen_UN (baFM sz (BAflowLam0 sz z) (BAflowEs sz z)) n σ s t A‖ ≤ _
  rw [Step2Kern_UN_BA sz _ _ n (EKGenBA_hIm hκ hr)]
  exact hpin (sz.L n) (sz.three_le_L n) (BAflowLam0 sz z n) hn.1 hn.2 ((sz.W n : ℕ) : ℝ) ε' D hW hε0 hε1 hD hWε hlog hLK s t hs hst ht hWt
    (BAflowEs sz z n) _ hr σ A hA hsum

end D1

end RBM.BA

end
