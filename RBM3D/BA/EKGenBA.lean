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
# U3-BA (a), file 1: the BA kernel layer (ticket T2507, row a)

Paper: arXiv:2507.20274, `lem:sum_Ndecay`, `lem:sum_decay`, `lem:sum_decay_nonzero` (`3_5:1615-1666`) read at the block Anderson
model (`7_8:2099-2100`: Steps 3-6 extend verbatim).  New leaf: no merged file is edited.  The check is
`docs/tickets/checks/T2507-check.lean` (pins `T2507_*`).

BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; `gK = BAflowLam0`; `Aof κ = (κ+1)/κ`.

* 1. `BAEKKer` (= `T2507_EKKer`; the only new public `def`): the model class of the kernel pins, `STEKKer d`-typed.
* 2. `baEKKer_flow` (= `T2507_KerFlowBA`): the `hKer` bundle (`κm = κ`, the class, the window and R1) of `ST_step6_caseII_of_pinsgL`,
  `stExpIniIgL'_of`, `stExpIntIIgL_of` at the BA family.
* 3. the five forms `baEKSum{Ndecay,Res1,Res2NAL,Res2}gL_holds`, `baEKNonzerogL_holds` at `@BAEKKer d`: the class is unpacked,
  `Step2Kern_UN_BA` turns `Step2Gen_UN` into stage E's `BAUN`, the stage-E pin is applied at `g = gK n`, and the `≺` lift is the
  private core `EKGenBA_core`, the twin of the private band-typed `prec_core` (`Evolution/Prec.lean:130`) at a law `μ` and a
  kernel coupling `gK`; `prec_L_pow_le`, `prec_log_le` (`Prec.lean:73, 86`) are copied as `EKGenBA_L_pow_le`, `EKGenBA_log_le`.
* 4. `baEKSumDecayNonzeroA_holds` (= `T2507_EKNonzeroA`): `BAEKSumDecayNonzero` with the threshold `(1 - s) L² ≤ A g²`, every `A > 0`.
* 5. `baNQGoodGen_kerNAL`, `baQProxyG_kerEK4` (= `T2507_KerNALBA`, `T2507_KerEK4BA`): the deterministic kernel classes D1 of
  T2491 and T2498 at the BA family.
* 6. compiled nonempty instances at `d = 3` (`sz0`, `zSeq`, `flow_sz0`).

R1 (UBA-C1) is stated once, in target 2, and used in no proof here.  Private helpers carry the stem `EKGenBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open private step34Gen_win_sz0 step34Gen_Az step34Gen_Az_sumZero step34Gen_Az_decay step34Gen_norm_Az_le
  step34Gen_norm_delta0_le from RBM3D.Chain.Step34Gen

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 1 and 2: the class `BAEKKer` and the flow bundle -/

/-- **Target 1, `BAEKKer`** (= `T2507_EKKer`; UBA-C2): the carrier `C` is the BA carrier at the coupling `gK` with the real energies `E`
and bulk data `BAReal` at every `n` (bulk parameter `κ`); the kernel `Step2Gen_UN C` is then stage E's `BAUN` (`Step2Kern_UN_BA`).  There is
no window field: the window is the forms' own `∀ᶠ n, 0 < gK n ∧ gK n ≤ 𝔡⁻¹`.  It has the type `STEKKer d` when read as `@BAEKKer d`. -/
def BAEKKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, C = baFM sz gK E ∧ ∀ n, BAReal d (sz.L n) (gK n) κ (E n) (BAmF sz gK E n)

/-- **Target 2, `baEKKer_flow`** (= `T2507_KerFlowBA`): the `hKer` bundle at the BA family with `κm = κ`: `κ ≤ Im m` at every `n`
(`EMn2BA_mF_data`), the class at the flow carrier (`BAflow_real`), the window (`BAflow_lam0_window`), and the comparison R1
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

Copies (text of `Prec.lean:42-130`, `Sizes`-only, no band object): `EKGenBA_W_rpow_ge` (`prec_W_rpow_ge`), `EKGenBA_one_lt_W`
(`prec_one_lt_W`), `EKGenBA_L_pow_le` (`prec_L_pow_le`), `EKGenBA_log_le` (`prec_log_le`), `EKGenBA_window` (`prec_window`),
`EKGenBA_ratio_ge_one` (`prec_ratio_ge_one`); `EKGenBA_core` is `prec_core` (`Prec.lean:130`) with `Prec sz` read as `PrecL sz μ`,
`STEKDecay` as `STEKDecayKgL gK μ`, `STEKLow` as `STEKLowgL μ`, `Prec.whp` as `StochDomAt.highProb`, and `EKFastDecay (sz.lam n)` as
`EKFastDecay (gK n)`; no measure-theoretic hypothesis beyond the merged `StochDomAt` calculus (all lemmas are stated for any measure). -/

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

/-- **The shared absorption step** (`prec_core`, `Prec.lean:130`) at a law `μ` and a kernel coupling `gK`: a pin of the shape
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

/-! ## 3. Target 4: the A-form of `lem:sum_decay_nonzero` at BA -/

section NonzeroA

open scoped Matrix.Norms.Operator

/-- **Target 4, `baEKSumDecayNonzeroA_holds`** (= `T2507_EKNonzeroA`): `BAEKSumDecayNonzero` (`EKPins:134`) with the threshold `1 - g²/L² ≤ s`
replaced by `(1 - s) L² ≤ A g²`, every `A > 0`.  The product step of `baEKSumDecayNonzero_holds` (`EKNonzero:261-300`): a same-sign index
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

/-! ## 4. Target 3: the five forms at `@BAEKKer d`, law `seqP (sz.withLam 0)` -/

section Forms

/-- `Im (E + m) ≠ 0` from the bulk datum `κ ≤ Im m`, `0 < κ` (the hypothesis `hIm` of `Step2Kern_UN_BA`). -/
private theorem EKGenBA_hIm {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hκ : 0 < κ) (hr : BAReal d L g κ E m) :
    (((E : ℝ) : ℂ) + m).im ≠ 0 := by
  rw [Complex.add_im, Complex.ofReal_im, zero_add]
  exact (hκ.trans_le hr.2).ne'

/-- **Target 3 (a), `baEKSumNdecaygL_holds`** (= `T2507_SumNdecayBA`) from `baEKSumNdecay_holds` (`EKPins:218`); the band text is
`stek_sumNdecay_holds` (`Prec.lean:215`), no core needed. -/
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

/-- **Target 3 (b), `baEKSumRes1gL_holds`** (= `T2507_SumRes1BA`) from `baEKSumDecay1_holds` (`EKSum:200`): the ratio factor is
`ρ = (ℓ_t²/ℓ_v²)·ratio^n ≥ 1` (`ℓ` is monotone in time at the coupling `gK n ≥ 0`). -/
theorem baEKSumRes1gL_holds (d : ℕ) : STEKSumRes1gL d (fun sz => Sizes.seqP (sz.withLam 0)) (@BAEKKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hE⟩ hg s t hwin σ 𝒜 hdec X hlow hdom
  subst hC
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  obtain ⟨hs, hst, ht, ht1, hW⟩ := hwin
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hd0 : 0 < d := by omega
  obtain ⟨Cc, hCc, hpin⟩ := baEKSumDecay1_holds d n_ 𝔡⁻¹ κ hd hn hΛ hκ
  refine EKGenBA_core sz _ hd0 h𝔠 hSz hBw gK 𝒜 hdec X hlow hdom
    (fun n v ω => ‖Step2Gen_UN (baFM sz gK E) n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
    (fun n v => (ellT (sz.L n) (gK n) (t n) ^ 2 / ellT (sz.L n) (gK n) (v : ℝ) ^ 2) *
      ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ n_) hCc ?_ ?_
  · filter_upwards [hg] with n hgn v
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have h1 : 1 ≤ ellT (sz.L n) (gK n) (t n) ^ 2 / ellT (sz.L n) (gK n) (v : ℝ) ^ 2 := by
      rw [one_le_div (pow_pos (ellT_pos hL1) 2)]
      exact pow_le_pow_left₀ (ellT_pos hL1).le (ellT_mono hgn.1.le (v.2).2 (ht1 n)) 2
    exact one_le_mul_of_one_le_of_one_le h1 (one_le_pow₀ (EKGenBA_ratio_ge_one (v.2).2 (ht1 n)))
  · intro ε D₀ hε0 hε1 hD₀
    filter_upwards [EKGenBA_W_rpow_ge sz h𝔠 hSz hBw hε0 4, hg, hW] with n h4 hgn hWn v ω hdecay
    have hWpos : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW1 := EKGenBA_one_lt_W hWpos hε0 h4
    rw [Step2Kern_UN_BA sz gK E n (EKGenBA_hIm hκ (hE n))]
    have hpv := hpin (sz.L n) (sz.three_le_L n) (gK n) hgn.1 hgn.2 ((sz.W n : ℕ) : ℝ) ε D₀
      hW1 hε0 hε1 hD₀ h4 (v : ℝ) (t n) ((hs n).trans (v.2).1) (v.2).2 (ht n)
      (EKGenBA_window (v.2).1 (v.2).2 (ht1 n) hWn) (E n) _ (hE n) σ (𝒜 n v ω) hdecay
    refine hpv.trans (le_of_eq ?_)
    ring

/-- **Target 3 (c), `baEKSumRes2NALgL_holds`** (= `T2507_SumRes2NALBA`) from `baEKSumDecayNAL_holds` (`EKSum:290`); the ratio is at `(n_ - 1)`. -/
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

/-- **Target 3 (d), `baEKSumRes2gL_holds`** (= `T2507_SumRes2BA`) from `baEKSumDecay2_holds` (`EKSum:1772`), `K = 1/𝔠`: `L^d ≤ W^K`
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

/-- **Target 3 (e), `baEKNonzerogL_holds`** (= `T2507_NonzeroBA`), for every `Aof` (the A-form): from target 4 at `A = Aof κ ≥ 1`; the
threshold `(1 - v) L² ≤ (1 - s) L² ≤ Aof κ · gK²` passes to every `v ∈ [s, t]`, and the constant `C` of the pin is absorbed by
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

/-! ## 5. Target 5: the deterministic kernel classes D1 of T2491 and T2498 at the BA family -/

section D1

/-- **Target 5 (a), `baNQGoodGen_kerNAL`** (= `T2507_KerNALBA`): `NQGoodGen_KerNALFam` at the BA family, `Ck` from
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

/-- **Target 5 (b), `baQProxyG_kerEK4`** (= `T2507_KerEK4BA`): `QProxyG_KerEK4Fam` at the BA family, `C4` from
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

/-! ## 6. Compiled nonempty instances at `d = 3`

Data: `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N ≥ 2^21`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`BA/FlowPins.lean:1214`), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `gK = BAflowLam0 sz0 zSeq`, `n_ = 2` (forms) and `k = 3` (targets 5), `Aof κ = (κ+1)/κ = 3`.
The tensor family is the point mass `δ₀` (and `δ₀ ⊗ (δ₀ - δ_e)` for the sum-zero form), the control is `X ≡ 1`; the `PrecL` inputs are discharged
(deterministic domination at the BA law `seqP (sz0.withLam 0)`), the window is `(s, t) = (0, 1/16)` (`step34Gen_win_sz0`, moved from `sz0.lam` to `gK` by
`step34Gen_winK_of_cmp` and R1) and, for form (e), `s = 1 - lam²/L²`, `t = (1 + s)/2` (so `(1 - s) L² = lam² ≤ 3 g₀²`).  The band helpers of
`Chain/Step34Gen.lean` that the instances reuse (`step34Gen_win_sz0`, `step34Gen_Az` and its three facts, `step34Gen_norm_delta0_le`) are private there and
are read by `open private`; nothing is edited. -/

namespace EKGenBAInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.Gauss.InductionDefsInst

/-- Deterministic domination gives `≺` at any law (`prec_of_le`, `Defs/StochDomAt.lean:136`, at a law `μ`). -/
private theorem EKGenBA_precL_of_le {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ n u ω, ξ n u ω ≤ ζ n u ω) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => ?_
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  nlinarith [hle n u ω, hζ n u ω]

/-- `δ₀` has `(deccA0)` at every coupling, start time and `W > 0` (the `a = 0` case contradicts `W^ε ℓ_s > 0`). -/
private theorem EKGenBA_fastDecay_delta0 {n d L : ℕ} [NeZero L] (hL : 1 ≤ L) (g s W ε D : ℝ) (hW : 0 < W) :
    EKFastDecay g s W ε D (ekDelta0 n d L) := by
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have := mul_pos (Real.rpow_pos_of_pos hW ε) (ellT_pos (g := g) (t := s) hL1)
    simp at hij
    linarith
  · simp only [ekDelta0, ha, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg hW.le _

private theorem inst_L1 (n : ℕ) : 1 ≤ sz0.L n := by have := sz0.three_le_L n; omega

private theorem inst_Wpos (n : ℕ) : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n

private theorem inst_W4 (n : ℕ) : (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
  have h16 : (16 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := (by norm_num : (16 : ℝ) ≤ 32).trans (W_ge_32 n)
  calc (4 : ℝ) = (16 : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_sq (by norm_num)]
    _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) h16 (by norm_num)

/-- **Target 1 at the flow** (`T2507_EKKer`): the carrier `baFMz sz0 zSeq` is in the class at `κ = 1/2` (energies `BAflowEs`, `BAflow_real`). -/
private theorem inst_kernel : BAEKKer sz0 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) (1 / 2) :=
  ⟨BAflowEs sz0 zSeq, rfl, fun n => BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n⟩

private theorem inst_window : ∀ᶠ n in atTop, 0 < BAflowLam0 sz0 zSeq n ∧ BAflowLam0 sz0 zSeq n ≤ ((1 / 10 : ℝ))⁻¹ :=
  BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0

/-- R1 at `κ = 1/2` (`TwistStep2_lam0_sq`, `0 ≤ g₀ λ`). -/
private theorem inst_R1 : ∀ n, 0 ≤ BAflowLam0 sz0 zSeq n * sz0.lam n ∧ BAflowLam0 sz0 zSeq n ^ 2 ≤ sz0.lam n ^ 2 ∧
    sz0.lam n ^ 2 ≤ ((1 / 2 : ℝ) + 1) / (1 / 2) * BAflowLam0 sz0 zSeq n ^ 2 := fun n => by
  have h := TwistStep2_lam0_sq (by norm_num : (0 : ℝ) < 1 / 2) flow_sz0 n
  refine ⟨?_, h.1, h.2⟩
  have e : BAflowLam0 sz0 zSeq n * sz0.lam n = Real.sqrt (BAflowT0 sz0 zSeq n) * (sz0.lam n * sz0.lam n) := by
    unfold BAflowLam0; ring
  rw [e]
  exact mul_nonneg (Real.sqrt_nonneg _) (mul_self_nonneg _)

private theorem inst_win : STEKWinKgL sz0 (BAflowLam0 sz0 zSeq) sInst tInst :=
  step34Gen_winK_of_cmp inst_R1 step34Gen_win_sz0

private theorem inst_prec_delta0 (s t : ℕ → ℝ) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => TimeIcc s t n) (fun n _ _ => ‖ekDelta0 2 3 (sz0.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  EKGenBA_precL_of_le sz0 _ (fun _ _ _ => zero_le_one) (fun n _ _ => step34Gen_norm_delta0_le 2 3 (sz0.L n))

private theorem inst_prec_Az (s t : ℕ → ℝ) :
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => TimeIcc s t n) (fun n _ _ => ‖step34Gen_Az (sz0.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  EKGenBA_precL_of_le sz0 _ (fun _ _ _ => zero_le_one) (fun n _ _ => step34Gen_norm_Az_le (sz0.L n))

private theorem inst_low (s t : ℕ → ℝ) : STEKLowgL (Sizes.seqP (sz0.withLam 0)) s t (fun _ _ _ => (1 : ℝ)) :=
  ⟨0, Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v => by simp)⟩

private theorem inst_decay_delta0 (s t : ℕ → ℝ) :
    STEKDecayKgL (BAflowLam0 sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) s t (fun n _ _ => ekDelta0 2 3 (sz0.L n)) := by
  intro ε D hε hD
  exact Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v =>
    EKGenBA_fastDecay_delta0 (inst_L1 n) _ _ _ _ _ (inst_Wpos n))

private theorem inst_decay_Az (s t : ℕ → ℝ) :
    STEKDecayKgL (BAflowLam0 sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) s t (fun n _ _ => step34Gen_Az (sz0.L n)) := by
  intro ε D hε hD
  refine Gauss.HighProbAt.of_eventually_univ ?_
  have h4s : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp (step34Gen_W_tendsto sz0_admissible)).eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [h4s] with n h4 ω v
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast inst_L1 n
  refine step34Gen_Az_decay (sz0.L n) (sz0.three_le_L n) _ _ _ _ _ (inst_Wpos n) ?_
  have h1 := one_le_ellT (g := BAflowLam0 sz0 zSeq n) (t := (v : ℝ)) hL1
  have h2 : 1 < ((sz0.W n : ℕ) : ℝ) ^ ε * ellT (sz0.L n) (BAflowLam0 sz0 zSeq n) (v : ℝ) := by nlinarith
  exact h2

/-- **Target 1** (`T2507_EKKer`) and **target 2** (`T2507_KerFlowBA`) at the flow of `sz0` and `κ = 1/2`: some `κm > 0` (`= κ`) with `κm ≤ Im m` at every `n`,
the class at `κm`, the window `0 < g₀ ≤ 𝔡⁻¹` (eventually) and R1 at every `n`. -/
example : ∃ κm : ℝ, 0 < κm ∧ (∀ n, κm ≤ ((baFMz sz0 zSeq).m n).im) ∧ BAEKKer sz0 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) κm ∧
    (∀ᶠ n in atTop, 0 < BAflowLam0 sz0 zSeq n ∧ BAflowLam0 sz0 zSeq n ≤ ((1 / 10 : ℝ))⁻¹) ∧
    ∀ n, 0 ≤ BAflowLam0 sz0 zSeq n * sz0.lam n ∧ BAflowLam0 sz0 zSeq n ^ 2 ≤ sz0.lam n ^ 2 ∧
      sz0.lam n ^ 2 ≤ (κm + 1) / κm * BAflowLam0 sz0 zSeq n ^ 2 := by
  obtain ⟨κm, hκm, H⟩ := baEKKer_flow 3 (1 / 2) (by norm_num)
  exact ⟨κm, hκm, H sz0 (1 / 10) (1 / 6) (1 / 10) zSeq flow_sz0⟩

example : BAEKKer sz0 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) (1 / 2) := inst_kernel

/-- **Target 3 (a)**: `(sum_res_Ndecay)` at `(s, t) = (0, 1/16)`, `σ = (+, -)`, `𝒜 = δ₀`, `X ≡ 1`. -/
example := baEKSumNdecaygL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) inst_kernel inst_window sInst tInst (fun _ => le_rfl)
  (fun n => by simp only [sInst, tInst]; norm_num) (fun n => by simp only [tInst]; norm_num) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one) (inst_prec_delta0 sInst tInst)

/-- **Target 3 (b)**: `(sum_res_1)`. -/
example := baEKSumRes1gL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) inst_kernel inst_window sInst tInst inst_win ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (inst_decay_delta0 sInst tInst) (fun _ _ _ => (1 : ℝ)) (inst_low sInst tInst)
  (inst_prec_delta0 sInst tInst)

/-- **Target 3 (c)**: `(sum_res_2_NAL)`, `σ = (+, +)` (non-alternating). -/
example := baEKSumRes2NALgL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) inst_kernel inst_window sInst tInst inst_win ![true, true] ⟨0, by decide⟩
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (inst_decay_delta0 sInst tInst) (fun _ _ _ => (1 : ℝ)) (inst_low sInst tInst)
  (inst_prec_delta0 sInst tInst)

/-- **Target 3 (d)**: `(sum_res_2)` for the sum-zero tensor `δ₀ ⊗ (δ₀ - δ_e)`. -/
example := baEKSumRes2gL_holds 3 le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) inst_kernel inst_window sInst tInst inst_win ![true, false]
  (fun n _ _ => step34Gen_Az (sz0.L n)) (inst_decay_Az sInst tInst) (fun n _ _ => step34Gen_Az_sumZero (sz0.L n))
  (fun _ _ _ => (1 : ℝ)) (inst_low sInst tInst) (inst_prec_Az sInst tInst)

private theorem inst_lam_ratio_nonneg (n : ℕ) : 0 ≤ sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by positivity

private theorem inst_lam_ratio_pos (n : ℕ) : 0 < sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
  have : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast (by have := inst_L1 n; omega : 0 < sz0.L n)
  have := sz0_lam_pos n
  positivity

private theorem inst_lam_ratio_le_one (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 := by
  have h := sz0_lam_L n
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast inst_L1 n
  have h3 : (1 : ℝ) ≤ (((sz0.L n) ^ 3 : ℕ) : ℝ) := by
    push_cast; exact one_le_pow₀ hL1
  have h2 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 2 := one_le_pow₀ hL1
  rw [div_le_one (by linarith)]
  nlinarith [sq_nonneg (sz0.lam n)]

/-- the threshold `(1 - s) L² ≤ Aof κ · g₀²` of form (e) for `s = 1 - lam²/L²`, `Aof (1/2) = 3` (R1). -/
private theorem inst_thr (n : ℕ) :
    (1 - (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) * ((sz0.L n : ℕ) : ℝ) ^ 2 ≤
      ((fun κ : ℝ => (κ + 1) / κ) (1 / 2)) * BAflowLam0 sz0 zSeq n ^ 2 := by
  have h := (inst_R1 n).2.2
  have hL : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz0.L n : ℕ) : ℝ) := by exact_mod_cast (by have := inst_L1 n; omega : 0 < sz0.L n)
    positivity
  have e : (1 - (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) * ((sz0.L n : ℕ) : ℝ) ^ 2 = sz0.lam n ^ 2 := by
    rw [sub_sub_cancel, div_mul_cancel₀ _ hL.ne']
  rw [e]
  exact h

/-- **Target 3 (e)**, `Aof κ = (κ+1)/κ` (`= 3` at `κ = 1/2`): `lem:sum_decay_nonzero` at `σ = (+, -)`, `A = univ`, `s = 1 - lam²/L²`, `t = (1 + s)/2`. -/
example := baEKNonzerogL_holds 3 (fun κ => (κ + 1) / κ) le_rfl 2 le_rfl (1 / 2) (1 / 6) (1 / 10) (by norm_num) (by norm_num) sz0 sz0_admissible
  (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) inst_kernel inst_window
  (fun n => 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2) (fun n => (1 + (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) / 2)
  inst_thr (fun n => by linarith [inst_lam_ratio_le_one n]) (fun n => by linarith [inst_lam_ratio_nonneg n])
  (fun n => by linarith [inst_lam_ratio_pos n]) ![true, false] Finset.univ (fun i _ => Finset.mem_univ i)
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one)
  (inst_prec_delta0 (fun n => 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)
    (fun n => (1 + (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) / 2))

/-- **Target 4** at the flow datum of some index `n` (the window `0 < g₀ ≤ 10`), `A = 3`: the bound of `lem:sum_decay_nonzero` at `σ = (+, -)`,
`A = univ`, `s = 1 - lam²/L²` (`(1 - s) L² = lam² ≤ 3 g₀²`), `t = (1 + s)/2`, `𝒜 = δ₀`. -/
example : ∃ C : ℝ, 0 < C ∧ ∃ n : ℕ,
    ‖zeroModeSet 3 (sz0.L n) Finset.univ (BAUN 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n)
      (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) ![true, false]
      (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2) ((1 + (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) / 2)
      (ekDelta0 2 3 (sz0.L n)))‖ ≤ C * ‖ekDelta0 2 3 (sz0.L n)‖ := by
  obtain ⟨C, hC, H⟩ := baEKSumDecayNonzeroA_holds 3 2 10 (1 / 2) le_rfl le_rfl (by norm_num) (by norm_num) 3 (by norm_num)
  obtain ⟨n, hn⟩ := inst_window.exists
  refine ⟨C, hC, n, H (sz0.L n) (sz0.three_le_L n) (BAflowLam0 sz0 zSeq n) hn.1 (hn.2.trans (by norm_num))
    (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2) ((1 + (1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2)) / 2)
    (by linarith [inst_lam_ratio_le_one n]) (by have := inst_thr n; norm_num at this ⊢; linarith)
    (by linarith [inst_lam_ratio_nonneg n]) (by linarith [inst_lam_ratio_pos n]) (BAflowEs sz0 zSeq n)
    (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) (BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0 n)
    ![true, false] Finset.univ (fun i _ => Finset.mem_univ i) (ekDelta0 2 3 (sz0.L n))⟩

/-- **Target 5 (a)** at `k = 3`: the class `NQGoodGen_KerNAL` at the BA carrier (`Ck` from `baEKSumDecayNAL_holds`), and its bound at some index `n`
(window discharged), `ε = 1/2`, `D = 2`, `(s, t) = (0, 1/16)`, `σ = (+, +, -)` (non-alternating), `𝒜 = δ₀`. -/
example : ∃ Ck : ℝ, 0 < Ck ∧ (∀ᶠ n in atTop, NQGoodGen_KerNAL (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) 3 Ck n) ∧
    ∃ n : ℕ, ‖Step2Gen_UN (baFMz sz0 zSeq) n ![true, true, false] 0 (1 / 16) (ekDelta0 3 3 (sz0.L n))‖ ≤
      ((sz0.W n : ℕ) : ℝ) ^ (Ck * (1 / 2)) *
        ((BAflowLam0 sz0 zSeq n ^ 2 + |1 - 0|) / (BAflowLam0 sz0 zSeq n ^ 2 + |1 - 1 / 16|)) ^ (3 - 1) * ‖ekDelta0 3 3 (sz0.L n)‖ +
      ((sz0.W n : ℕ) : ℝ) ^ (-2 + Ck) := by
  obtain ⟨Ck, hCk, H⟩ := baNQGoodGen_kerNAL 3 le_rfl 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  have h := H sz0 (1 / 6) zSeq flow_sz0
  obtain ⟨n, hn⟩ := h.exists
  exact ⟨Ck, hCk, h, n, hn (by linarith [W_ge_32 n]) (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num) (inst_W4 n) 0 (1 / 16) le_rfl
    (by norm_num) (inst_win.2.2.1 n) ((inv_anti₀ (by norm_num) (W_ge_32 n)).trans (by norm_num)) ![true, true, false] ⟨0, by decide⟩
    (ekDelta0 3 3 (sz0.L n)) (EKGenBA_fastDecay_delta0 (inst_L1 n) _ _ _ _ _ (inst_Wpos n))⟩

/-- **Target 5 (b)** at `k = 3`, `KL = 6 = 1/𝔠`: the class `QProxyG_KerEK4` at the BA carrier along the flow of `sz0` (`C4` from `baEKSumDecay2_holds`), at
some index `n`. -/
example : ∃ C4 : ℝ, 0 < C4 ∧ ∃ n : ℕ, RBM.Ind.QProxyG_KerEK4 (baFMz sz0 zSeq) (BAflowLam0 sz0 zSeq) 3 6 C4 n := by
  obtain ⟨C4, hC4, H⟩ := baQProxyG_kerEK4 3 le_rfl 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) 6 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨C4, hC4, (H sz0 (1 / 6) zSeq flow_sz0).exists⟩

/-- **U-D P7** (`baEta_antitone`, covered): `η_u = (1 - u) Im m` is antitone in `u` at the BA carrier along the flow of `sz0` (`NQGood1Gen_eta_anti` at
`baStep2Mat_loopForm`). -/
example (n : ℕ) (u u' : ℝ) (hu : u ≤ u') :
    (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).eta n u' ≤ (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).eta n u :=
  NQGood1Gen_eta_anti (baStep2Mat_loopForm 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0) n hu

end EKGenBAInst

end RBM.BA

end
