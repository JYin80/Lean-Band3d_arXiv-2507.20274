/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Eq729B

/-!
# UN-51 (RandomLayerA): Lemma 2.8 at `z = e + iη` and the size-level rows, `d ≥ 3`

Port of RBM2D `Universality/GUEPhase/RandomLayerA.lean` (521 lines, `9e0f275`).  Paper:
arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex:566-581` (the two scales), the flow `𝐇_t`
(`(eq:zztE)`, `1_2:787-795`).

Public declarations (namespace `RBM.Univ.GUEPhase`).
* `RandomLayer_lem28`: Lemma 2.8 at `z = e + iη`, with `η_{t₀} = √t₀ η` and `1 - t₀ ≤ η/c_κ`.
* `RandomLayer_rows_flow`: the assembly at an arbitrary scale `η` and abstract flow data `(E', t₀)`
  that satisfy the Lemma 2.8 facts (hypotheses): from the size-level conditions `r1..r4` to
  `0 ≤ t₁ ≤ t₀`, `h730`, `hscale`, `hell`, `hell1` of `gueGrid_pathBounds`
  (`t₁ = (1 - ζ(t_n)) t₀`).  `RandomLayer_rows`: the same for the flow `E' = lemE z_n`,
  `t₀ = lemT z_n` of the source (`z_n = e_n + iη_n`).
* `RandomLayer_rowsLL`, `RandomLayer_rowsQ`: `r1..r4` at `η_LL = N^{-1+2τ_U}` (`τ_D = τ_U/2`) and at
  the QUE scale `η_Q` (`τ_D = τ_U`) from `Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡`,
  `0 ≤ t_n ≤ N^{-1+τ_U}`.
* `RandomLayer_etaLL_pos`, `RandomLayer_etaLL_le_one`, `RandomLayer_etaQ_pos`,
  `RandomLayer_etaQ_le_one`.
Compiled instances: `RBM.Univ.GUEPhase.RandomLayerInst`.

Port map (`d = 2` to `d ≥ 3`): `d : Sizes` becomes `sz : Sizes d`; `d.size n = (WL)^2` becomes
`Nsz sz n = (WL)^d`; `spectralZ`, `spectralM` become `zt`, `mE`; `zztE_quant` becomes
`lemma28_quant` and `zRange`/`im_msc_ge` (`c_κ = √(κ(4-κ))/8`).  Replaced at `d ≥ 3`: the energy
margin `κ/2` is not needed (`lemma28_quant` keeps `κ`); `hell` is `L^d(1-t₁) ≤ lam²` (source
`L²(1-t₁) ≤ 1`) with the new `hell1 : L^d(1-t₁) ≤ 1` (`gueGrid_pathBounds`); the range condition
`N^{-1+τ} ≤ 1 - t₁` and its hypothesis `r5` have no twin (`STFlow` carries the domain); the QUE
scale `η_Q = W^{-𝔡/3} lam W^{d/2}/N` carries `lam`, so `η_Q > 0` needs `0 < lam n` and
`η_Q ≤ 1` holds eventually (`queDomain`); the source's `RandomLayer_rowsQ` rows are the merged
`Eq729B_claimA`, `Eq729B_h730_hscale_real` (`r1`, `r2`).
Helpers that the ticket does not pin are `private` with the prefix `RandomLayer_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop
  RBM.Univ RBM.Endpoints
open scoped NNReal ENNReal

variable {d : ℕ}

/-! ### Lemma 2.8 at `z = e + iη` -/

/-- **Lemma 2.8 at `z = e + iη`**, `|e| ≤ 2 - κ`, `0 < η ≤ 1`: `|lemE z| ≤ 2 - κ`, `1/16 ≤ t₀ < 1`
(`t₀ = lemT z`), `η_{t₀} = etaT E' t₀ = √t₀ η` (so `η/4 ≤ η_{t₀} ≤ η`) and `1 - t₀ ≤ η/c_κ`,
`c_κ = √(κ(4-κ))/8` (`im_msc_ge`, `zRange`: `1 - t₀ = Im z/(Im m + Im z)`). -/
theorem RandomLayer_lem28 {κ e η : ℝ} (hκ : 0 < κ) (he : |e| ≤ 2 - κ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) {z : ℂ} (hz : z = (e : ℂ) + (η : ℂ) * Complex.I) :
    0 < z.im ∧ |lemE z| ≤ 2 - κ ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧
      etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η ∧ η / 4 ≤ etaT (lemE z) (lemT z) ∧
      etaT (lemE z) (lemT z) ≤ η ∧ 1 - lemT z ≤ η / (Real.sqrt (κ * (4 - κ)) / 8) := by
  have hre : z.re = e := by simp [hz]
  have him : z.im = η := by simp [hz]
  have hzim : 0 < z.im := him ▸ hη0
  have hz1 : z.im ≤ 1 := him ▸ hη1
  have hzκ : |z.re| ≤ 2 - κ := hre ▸ he
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg e]
  obtain ⟨hE', ht16, -, -⟩ := lemma28_quant hκ hzim hz1 hzκ
  have ht1 : lemT z < 1 := lemT_lt_one hzim
  have heta : etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * η := by
    rw [etaT_eq_zt_im, zt_im_lemma28 hzim, him]
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hs1 : Real.sqrt (lemT z) ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  have hc0 : 0 < Real.sqrt (κ * (4 - κ)) / 8 :=
    div_pos (Real.sqrt_pos.2 (mul_pos hκ (by linarith))) (by norm_num)
  have hform := (zRange κ hκ z hzim hz1 hzκ).2.2.2.1
  have hmk := im_msc_ge hκ hzim hz1 hzκ
  have hma := msc_im_pos hzim
  refine ⟨hzim, hE', ht16, ht1, heta, ?_, ?_, ?_⟩
  · rw [heta]; nlinarith
  · rw [heta]; nlinarith
  · calc 1 - lemT z = z.im / ((msc z).im + z.im) := hform
      _ ≤ z.im / (Real.sqrt (κ * (4 - κ)) / 8) :=
          div_le_div_of_nonneg_left hzim.le hc0 (by linarith)
      _ = η / (Real.sqrt (κ * (4 - κ)) / 8) := by rw [him]

/-! ### The assembly at an arbitrary scale -/

/-- **`RandomLayer_rows` for abstract flow data**: from the size-level conditions to the hypotheses of
`gueGrid_pathBounds` at an arbitrary scale
`η_n > 0`, exponent `τ_D`, constant `c > 0`, flow data `(E', t₀)` with the Lemma 2.8 facts
(`1/16 ≤ t₀ < 1`, `η_{t₀} = √t₀ η`, `1 - t₀ ≤ η/c`) and `0 ≤ t_n`: with `t₁ = (1 - ζ(t_n)) t₀`,
`0 ≤ t₁ ≤ t₀` (every `n`), `h730`, `hscale`, `hell`, `hell1` (eventually) from
`r1: t ≤ N^{-τ_D} η/4`, `r2: 4 (Nη)⁻¹ ≤ N^{-τ_D}`, `r3: L^d (η/c + t) ≤ lam²`, `r4: L^d (η/c + t) ≤ 1`. -/
theorem RandomLayer_rows_flow (sz : Sizes d) {c τD : ℝ} {t t0 η E' : ℕ → ℝ}
    (ht : ∀ n, 0 ≤ t n) (hη0 : ∀ n, 0 < η n) (hs : ∀ n, 1 / 16 ≤ t0 n) (ht1 : ∀ n, t0 n < 1)
    (heta : ∀ n, etaT (E' n) (t0 n) = Real.sqrt (t0 n) * η n) (h1t : ∀ n, 1 - t0 n ≤ η n / c)
    (r1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τD) * (η n / 4))
    (r2 : ∀ᶠ n in atTop, 4 * (Nsz sz n * η n)⁻¹ ≤ Nsz sz n ^ (-τD))
    (r3 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / c + t n) ≤ sz.lam n ^ 2)
    (r4 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / c + t n) ≤ 1) :
    (∀ n, 0 ≤ (1 - ouZeta (t n)) * t0 n) ∧ (∀ n, (1 - ouZeta (t n)) * t0 n ≤ t0 n) ∧
      (∀ᶠ n in atTop, t0 n - (1 - ouZeta (t n)) * t0 n ≤ Nsz sz n ^ (-τD) * etaT (E' n) (t0 n)) ∧
      (∀ᶠ n in atTop, (gueScale sz E' n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τD)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * t0 n) ≤ sz.lam n ^ 2) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * t0 n) ≤ 1) := by
  have hNpos : ∀ n, 0 < Nsz sz n := Nsz_pos sz
  have hζ0 : ∀ n, 0 ≤ ouZeta (t n) := fun n => ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 : ∀ n, ouZeta (t n) ≤ 1 := fun n => ZeroModeProfile_ouZeta_le_one (t n)
  have hζt : ∀ n, ouZeta (t n) ≤ t n := fun n => ZeroModeProfile_ouZeta_le (t n)
  have ht0pos : ∀ n, 0 ≤ t0 n := fun n => by linarith [hs n]
  have hs4 : ∀ n, (1 / 4 : ℝ) ≤ Real.sqrt (t0 n) := fun n => by
    rw [Real.le_sqrt (by norm_num) (ht0pos n)]; linarith [hs n]
  have hηe : ∀ n, η n / 4 ≤ etaT (E' n) (t0 n) := fun n => by
    rw [heta n]; nlinarith [hη0 n, hs4 n]
  have hdiff : ∀ n, t0 n - (1 - ouZeta (t n)) * t0 n ≤ t n := fun n => by
    have := ht1 n
    nlinarith [hζ0 n, hζt n, ht0pos n]
  have hdiff1 : ∀ n, 1 - (1 - ouZeta (t n)) * t0 n ≤ η n / c + t n := fun n => by
    have h2 : ouZeta (t n) * t0 n ≤ t n := by
      nlinarith [hζ0 n, hζt n, ht0pos n, ht1 n]
    nlinarith [h1t n]
  refine ⟨fun n => mul_nonneg (by linarith [hζ1 n]) (ht0pos n),
    fun n => by nlinarith [hζ0 n, ht0pos n], ?_, ?_, ?_, ?_⟩
  · filter_upwards [r1] with n hN
    calc _ ≤ t n := hdiff n
      _ ≤ Nsz sz n ^ (-τD) * (η n / 4) := hN
      _ ≤ Nsz sz n ^ (-τD) * etaT (E' n) (t0 n) :=
          mul_le_mul_of_nonneg_left (hηe n) (Real.rpow_nonneg (hNpos n).le _)
  · filter_upwards [r2] with n hN
    refine le_trans ?_ hN
    unfold gueScale
    have hSη : 0 < Nsz sz n * (η n / 4) := mul_pos (hNpos n) (by linarith [hη0 n])
    calc (Nsz sz n * etaT (E' n) (t0 n))⁻¹ ≤ (Nsz sz n * (η n / 4))⁻¹ :=
          inv_anti₀ hSη (mul_le_mul_of_nonneg_left (hηe n) (hNpos n).le)
      _ = 4 * (Nsz sz n * η n)⁻¹ := by
          have := hη0 n; have := hNpos n; field_simp
  · filter_upwards [r3] with n hN
    exact le_trans (mul_le_mul_of_nonneg_left (hdiff1 n) (by positivity)) hN
  · filter_upwards [r4] with n hN
    exact le_trans (mul_le_mul_of_nonneg_left (hdiff1 n) (by positivity)) hN

/-- **`RandomLayer_rows`** (the form of the source, `RandomLayerA.lean:137`): the sequence
`z_n = e_n + i η_n`, `|e_n| ≤ 2 - κ`, `0 < η_n ≤ 1`, `t₀ = lemT z_n`, `E' = lemE z_n`, `t₁ = (1 - ζ(t_n)) t₀`.
The size-level conditions `r1..r4` (`c = c_κ = √(κ(4-κ))/8`) give, in this order, `|E' n| ≤ 2 - κ`,
`0 ≤ t₁`, `t₁ ≤ t₀`, `t₀ < 1` (every `n`), `h730`, `hscale`, `hell`, `hell1` (eventually): the
hypotheses of `gueGrid_pathBounds` (the source's range condition and its hypothesis `r5` have no twin). -/
theorem RandomLayer_rows (sz : Sizes d) {κ τD : ℝ} (hκ : 0 < κ) {e η t : ℕ → ℝ} (z : ℕ → ℂ)
    (hz : ∀ n, z n = (e n : ℂ) + (η n : ℂ) * Complex.I) (he : ∀ n, |e n| ≤ 2 - κ)
    (hη0 : ∀ n, 0 < η n) (hη1 : ∀ n, η n ≤ 1) (ht : ∀ n, 0 ≤ t n)
    (r1 : ∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τD) * (η n / 4))
    (r2 : ∀ᶠ n in atTop, 4 * (Nsz sz n * η n)⁻¹ ≤ Nsz sz n ^ (-τD))
    (r3 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / (Real.sqrt (κ * (4 - κ)) / 8) + t n) ≤
      sz.lam n ^ 2)
    (r4 : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (η n / (Real.sqrt (κ * (4 - κ)) / 8) + t n) ≤ 1) :
    (∀ n, |lemE (z n)| ≤ 2 - κ) ∧ (∀ n, 0 ≤ (1 - ouZeta (t n)) * lemT (z n)) ∧
      (∀ n, (1 - ouZeta (t n)) * lemT (z n) ≤ lemT (z n)) ∧ (∀ n, lemT (z n) < 1) ∧
      (∀ᶠ n in atTop, lemT (z n) - (1 - ouZeta (t n)) * lemT (z n) ≤
        Nsz sz n ^ (-τD) * etaT (lemE (z n)) (lemT (z n))) ∧
      (∀ᶠ n in atTop, (gueScale sz (fun n => lemE (z n)) n (lemT (z n)))⁻¹ ≤ Nsz sz n ^ (-τD)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * lemT (z n)) ≤ sz.lam n ^ 2) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * lemT (z n)) ≤ 1) := by
  have hκ2 : κ ≤ 2 := by linarith [abs_nonneg (e 0), he 0]
  have L28 := fun n => RandomLayer_lem28 hκ (he n) (hη0 n) (hη1 n) (hz n)
  obtain ⟨hnn, hle, h730, hscale, hell, hell1⟩ := RandomLayer_rows_flow sz (c := Real.sqrt (κ * (4 - κ)) / 8)
    (τD := τD) (t := t) (t0 := fun n => lemT (z n)) (η := η) (E' := fun n => lemE (z n)) ht hη0
    (fun n => (L28 n).2.2.1) (fun n => (L28 n).2.2.2.1) (fun n => (L28 n).2.2.2.2.1)
    (fun n => (L28 n).2.2.2.2.2.2.2) r1 r2 r3 r4
  exact ⟨fun n => (L28 n).2.1, hnn, hle, fun n => (L28 n).2.2.2.1, h730, hscale, hell, hell1⟩

/-! ### Size-level facts -/

/-- `L^d N^{-1+a} = N^a / W^d` (`N = W^d L^d`). -/
private theorem RandomLayer_Ld_mul_rpow (sz : Sizes d) (n : ℕ) (a : ℝ) :
    ((sz.L n : ℕ) : ℝ) ^ d * Nsz sz n ^ (-1 + a) = Nsz sz n ^ a / ((sz.W n : ℕ) : ℝ) ^ d := by
  have hN : Nsz sz n = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Nsz, Sizes.size, mul_pow]
  have hNpos := Nsz_pos sz n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
  have hLd : ((sz.L n : ℕ) : ℝ) ^ d ≠ 0 := by positivity
  have e : ((sz.L n : ℕ) : ℝ) ^ d * (Nsz sz n)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [hN]; field_simp
  rw [Real.rpow_add hNpos, Real.rpow_neg_one]
  calc ((sz.L n : ℕ) : ℝ) ^ d * ((Nsz sz n)⁻¹ * Nsz sz n ^ a)
      = (((sz.L n : ℕ) : ℝ) ^ d * (Nsz sz n)⁻¹) * Nsz sz n ^ a := by ring
    _ = _ := by rw [e]; ring

private theorem RandomLayer_one_le_N (sz : Sizes d) (n : ℕ) : (1 : ℝ) ≤ Nsz sz n := by
  exact_mod_cast sz.one_le_size n

private theorem RandomLayer_rpow_mul_eq {x a b c e : ℝ} (hx : 0 < x) (h : a + b = c + e) :
    x ^ a * x ^ b = x ^ c * x ^ e := by
  rw [← Real.rpow_add hx, ← Real.rpow_add hx, h]

/-- `N^{a} ≤ W^{a/𝔠}` and `W^{a/𝔠} ≤ W^{b}` for `a/𝔠 ≤ b`, `W ≥ 1`: the conversion used in `r3`, `r4`. -/
private theorem RandomLayer_N_le_W {sz : Sizes d} {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) {n : ℕ}
    (hb : Nsz sz n ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a / 𝔠 ≤ b) : Nsz sz n ^ a ≤ ((sz.W n : ℕ) : ℝ) ^ b :=
  (Sizes.size_rpow_le_W_rpow sz h𝔠 n hb ha).trans (Real.rpow_le_rpow_of_exponent_le hW1 hab)

/-! ### The size-level conditions at the two scales -/

/-- **`r1..r4` at `η = η_LL = N^{-1+2τ_U}`** (the scale of the local law), `τ_D = τ_U/2`, for any
`0 ≤ t_n ≤ N^{-1+τ_U}`, `c > 0`: `Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡`, `3 ≤ d`.  `r1`: `N^{τ_U/2} ≥ 4`;
`r2`: `N^{3τ_U/2} ≥ 4`; `r3`: `C N^{2τ_U} W^{-d} ≤ W^{2𝔡-d} ≤ lam²` with `C = 1/c + 1`, i.e.
`C ≤ W^{2𝔡 - 2τ_U/𝔠}` (`τ_U < 𝔠𝔡`); `r4`: `C N^{2τ_U} ≤ W ≤ W^d` (`τ_U ≤ 𝔠/12`). -/
theorem RandomLayer_rowsLL (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 τU c : ℝ} (hA : sz.Admissible 𝔠 𝔡)
    (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠 𝔡) (hc : 0 < c) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ ouTStar sz τU n) :
    (∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-(τU / 2)) * (ouEtaLL sz τU n / 4)) ∧
      (∀ᶠ n in atTop, 4 * (Nsz sz n * ouEtaLL sz τU n)⁻¹ ≤ Nsz sz n ^ (-(τU / 2))) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n) ≤ sz.lam n ^ 2) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n) ≤ 1) := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  obtain ⟨h12c, -, hτc𝔡, -⟩ := ouTauMax_slack h𝔠 h𝔡 hτUc
  have hWtop := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  set C : ℝ := 1 / c + 1 with hC
  have hC0 : 0 < C := by positivity
  have hE2 : ∀ᶠ n in atTop, 1 ≤ Nsz sz n := hsz.eventually (eventually_ge_atTop (1 : ℝ))
  have hE3 : ∀ᶠ n in atTop, 4 ≤ Nsz sz n ^ (τU / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τU / 2)).comp hsz).eventually_ge_atTop 4
  have hE4 : ∀ᶠ n in atTop, 4 ≤ Nsz sz n ^ (3 * τU / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 3 * τU / 2)).comp hsz).eventually_ge_atTop 4
  have hE5 : ∀ᶠ n in atTop, C ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 - 2 * τU / 𝔠) :=
    ((tendsto_rpow_atTop (by
      have : 2 * τU / 𝔠 < 2 * 𝔡 := by rw [div_lt_iff₀ h𝔠]; nlinarith
      linarith : 0 < 2 * 𝔡 - 2 * τU / 𝔠)).comp hWtop).eventually_ge_atTop C
  have hE6 : ∀ᶠ n in atTop, C ≤ ((sz.W n : ℕ) : ℝ) := hWtop.eventually_ge_atTop C
  have hE7 : ∀ᶠ n in atTop, 1 ≤ ((sz.W n : ℕ) : ℝ) := hWtop.eventually_ge_atTop 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hE2, hE3] with n hS1 h1
    have hS0 : 0 < Nsz sz n := by linarith
    unfold ouEtaLL
    have e := RandomLayer_rpow_mul_eq (a := -(τU / 2)) (b := -1 + 2 * τU) (c := -1 + τU)
      (e := τU / 2) hS0 (by ring)
    have hp : 0 < Nsz sz n ^ (-1 + τU) := Real.rpow_pos_of_pos hS0 _
    calc t n ≤ Nsz sz n ^ (-1 + τU) := ht n
      _ ≤ Nsz sz n ^ (-1 + τU) * Nsz sz n ^ (τU / 2) / 4 := by nlinarith
      _ = Nsz sz n ^ (-(τU / 2)) * (Nsz sz n ^ (-1 + 2 * τU) / 4) := by rw [← e]; ring
  · filter_upwards [hE2, hE4] with n hS1 h1
    have hS0 : 0 < Nsz sz n := by linarith
    unfold ouEtaLL
    have e1 : Nsz sz n * Nsz sz n ^ (-1 + 2 * τU) = Nsz sz n ^ (2 * τU) := by
      rw [mul_comm, ← Real.rpow_add_one hS0.ne']; ring_nf
    have e2 : Nsz sz n ^ (-(τU / 2)) = (Nsz sz n ^ (2 * τU))⁻¹ * Nsz sz n ^ (3 * τU / 2) := by
      rw [← Real.rpow_neg hS0.le, ← Real.rpow_add hS0]; ring_nf
    rw [e1, e2]
    have hp : 0 < (Nsz sz n ^ (2 * τU))⁻¹ := by positivity
    nlinarith
  · filter_upwards [hE2, hE5, hbw, hWO, hE7] with n hS1 hC5 hNW hWOn hW1
    have hS0 : 0 < Nsz sz n := by linarith
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have hlam := Sizes.lam_sq_mul_pow_ge sz n hWOn.1
    have htt : t n ≤ Nsz sz n ^ (-1 + 2 * τU) :=
      (ht n).trans (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith))
    have hX : ouEtaLL sz τU n / c + t n ≤ C * Nsz sz n ^ (-1 + 2 * τU) := by
      unfold ouEtaLL
      rw [hC, add_mul, one_mul, div_eq_mul_one_div, mul_comm]; linarith
    have hN2 := RandomLayer_N_le_W h𝔠 hNW hW1 (a := 2 * τU) (b := 2 * τU / 𝔠) (by positivity) le_rfl
    -- `C N^{2τ_U} ≤ C W^{2τ_U/𝔠} ≤ W^{2𝔡} ≤ lam² W^d`
    have e : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) =
        ((sz.W n : ℕ) : ℝ) ^ (2 * τU / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 - 2 * τU / 𝔠) := by
      rw [← Real.rpow_add hW0]; congr 1; ring
    have hp := Real.rpow_nonneg hW0.le (2 * τU / 𝔠)
    calc ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n)
        ≤ ((sz.L n : ℕ) : ℝ) ^ d * (C * Nsz sz n ^ (-1 + 2 * τU)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = C * (Nsz sz n ^ (2 * τU) / ((sz.W n : ℕ) : ℝ) ^ d) := by
          rw [← RandomLayer_Ld_mul_rpow sz n (2 * τU)]; ring
      _ ≤ sz.lam n ^ 2 := by
          rw [← mul_div_assoc, div_le_iff₀ hWd]
          calc C * Nsz sz n ^ (2 * τU) ≤ C * ((sz.W n : ℕ) : ℝ) ^ (2 * τU / 𝔠) :=
                mul_le_mul_of_nonneg_left hN2 hC0.le
            _ ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * τU / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡 - 2 * τU / 𝔠) := by
                rw [mul_comm C]; exact mul_le_mul_of_nonneg_left hC5 hp
            _ = ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := e.symm
            _ ≤ _ := hlam
  · filter_upwards [hE2, hbw, hE6, hE7] with n hS1 hNW hCW hW1
    have hS0 : 0 < Nsz sz n := by linarith
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have htt : t n ≤ Nsz sz n ^ (-1 + 2 * τU) :=
      (ht n).trans (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith))
    have hX : ouEtaLL sz τU n / c + t n ≤ C * Nsz sz n ^ (-1 + 2 * τU) := by
      unfold ouEtaLL
      rw [hC, add_mul, one_mul, div_eq_mul_one_div, mul_comm]; linarith
    have hN2 : Nsz sz n ^ (2 * τU) ≤ ((sz.W n : ℕ) : ℝ) := by
      have := RandomLayer_N_le_W h𝔠 hNW hW1 (a := 2 * τU) (b := 1) (by positivity) (by
        rw [div_le_iff₀ h𝔠]; linarith)
      simpa using this
    have hWW : ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
      rw [← pow_two]; exact pow_le_pow_right₀ hW1 (by omega)
    calc ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaLL sz τU n / c + t n)
        ≤ ((sz.L n : ℕ) : ℝ) ^ d * (C * Nsz sz n ^ (-1 + 2 * τU)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = C * (Nsz sz n ^ (2 * τU) / ((sz.W n : ℕ) : ℝ) ^ d) := by
          rw [← RandomLayer_Ld_mul_rpow sz n (2 * τU)]; ring
      _ ≤ 1 := by
          rw [← mul_div_assoc, div_le_one hWd]
          calc C * Nsz sz n ^ (2 * τU) ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) :=
                mul_le_mul hCW hN2 (by positivity) hW0.le
            _ ≤ _ := hWW

/-- `2 N^{τ_U} ≤ W^{2𝔡}` from `W ≥ N^𝔠`, `τ_U ≤ 𝔠𝔡/12`, `W ≥ 1` and `2 ≤ W^{23𝔡/12}` (the `ζ`-part of `hell`,
`Eq729B_derived`). -/
private theorem RandomLayer_two_N_le (sz : Sizes d) {n : ℕ} {𝔠 𝔡 τU : ℝ} (h𝔠 : 0 < 𝔠)
    (hτU : 0 ≤ τU) (hτ12 : τU ≤ 𝔠 * 𝔡 / 12) (hNW : Nsz sz n ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) (h2 : 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12)) :
    2 * Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have e1 := RandomLayer_N_le_W h𝔠 hNW hW1 hτU (b := 𝔡 / 12) (by rw [div_le_iff₀ h𝔠]; linarith)
  have e3 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) =
      ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  rw [e3]
  have := Real.rpow_nonneg hW0.le (𝔡 / 12)
  calc 2 * Nsz sz n ^ τU ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) := by linarith
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) :=
        mul_le_mul_of_nonneg_right h2 this
    _ = _ := mul_comm _ _

/-- **`r1..r4` at `η = η_Q = W^{-𝔡/3} lam W^{d/2}/N`** (the scale of (7.47)), `τ_D = τ_U`, for any
`0 ≤ t_n ≤ N^{-1+τ_U}`, `c > 0`: `Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡`, `3 ≤ d`.  `r1`, `r2`: Claim A
`4 N^{2τ_U} ≤ N η_Q` (`Eq729B_claimA`, `τ_U ≤ 𝔠𝔡/12`) with `Eq729B_h730_hscale_real`; `r3`:
`L^d η_Q/c ≤ lam a/2` (`L^d η_Q W^{4𝔡/3} = lam a`, `a = W^{-d/2+𝔡}`, `2/c ≤ W^{4𝔡/3}`) and
`L^d t ≤ N^{τ_U} W^{-d} ≤ a²/2` (`2N^{τ_U} ≤ W^{2𝔡}`); `r4`: `L^d η_Q/c ≤ 1/2` (`lam a ≤ 𝔡⁻²`,
`2𝔡⁻²/c ≤ W^{4𝔡/3}`) and `L^d t ≤ N^{τ_U} W^{-d} ≤ 1/2` (`N^{τ_U} ≤ W`, `2 ≤ W`). -/
theorem RandomLayer_rowsQ (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 τU c : ℝ} (hA : sz.Admissible 𝔠 𝔡)
    (hτU : 0 < τU) (hτUc : τU ≤ ouTauMax 𝔠 𝔡) (hc : 0 < c) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ ouTStar sz τU n) :
    (∀ᶠ n in atTop, t n ≤ Nsz sz n ^ (-τU) * (ouEtaQ sz 𝔡 n / 4)) ∧
      (∀ᶠ n in atTop, 4 * (Nsz sz n * ouEtaQ sz 𝔡 n)⁻¹ ≤ Nsz sz n ^ (-τU)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n) ≤ sz.lam n ^ 2) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n) ≤ 1) := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  obtain ⟨h12c, h12𝔡, -, -⟩ := ouTauMax_slack h𝔠 h𝔡 hτUc
  have hτ12 : τU ≤ 𝔠 * 𝔡 / 12 := by linarith
  have hWtop := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  have hE1 : ∀ᶠ n in atTop, 1 ≤ ((sz.W n : ℕ) : ℝ) := hWtop.eventually_ge_atTop 1
  have hE2 : ∀ᶠ n in atTop, 2 ≤ ((sz.W n : ℕ) : ℝ) := hWtop.eventually_ge_atTop 2
  have hE4 : ∀ᶠ n in atTop, 4 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 𝔡 / 2)).comp hWtop).eventually_ge_atTop 4
  have hE5 : ∀ᶠ n in atTop, 2 / c ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 4 * 𝔡 / 3)).comp hWtop).eventually_ge_atTop (2 / c)
  have hE6 : ∀ᶠ n in atTop, 2 * (𝔡⁻¹) ^ 2 / c ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 4 * 𝔡 / 3)).comp hWtop).eventually_ge_atTop
      (2 * (𝔡⁻¹) ^ 2 / c)
  have hE7 : ∀ᶠ n in atTop, 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 23 * 𝔡 / 12)).comp hWtop).eventually_ge_atTop 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hsz.eventually (eventually_ge_atTop (1 : ℝ)), hbw, hWO, hE4] with n hN1 hNW hWOn h4
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hη : 0 < ouEtaQ sz 𝔡 n := by
      unfold ouEtaQ
      have := Real.rpow_pos_of_pos hW0 (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hW0 ((d : ℝ) / 2)
      have := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 (-(d : ℝ) / 2 + 𝔡)) hWOn.1
      have := Nsz_pos sz n
      positivity
    have hclaim := Eq729B_claimA sz n h𝔡 hτ12 hNW h4 hWOn.1
    obtain ⟨hh1, -⟩ := Eq729B_h730_hscale_real (N := Nsz sz n) (ηQ := ouEtaQ sz 𝔡 n) (s := 1 / 4)
      (ζt := t n) hN1 hτU hη le_rfl (by linarith [hclaim]) (ht n)
    linarith [hh1]
  · filter_upwards [hsz.eventually (eventually_ge_atTop (1 : ℝ)), hbw, hWO, hE4] with n hN1 hNW hWOn h4
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hη : 0 < ouEtaQ sz 𝔡 n := by
      unfold ouEtaQ
      have := Real.rpow_pos_of_pos hW0 (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hW0 ((d : ℝ) / 2)
      have := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 (-(d : ℝ) / 2 + 𝔡)) hWOn.1
      have := Nsz_pos sz n
      positivity
    have hclaim := Eq729B_claimA sz n h𝔡 hτ12 hNW h4 hWOn.1
    obtain ⟨-, hh2⟩ := Eq729B_h730_hscale_real (N := Nsz sz n) (ηQ := ouEtaQ sz 𝔡 n) (s := 1 / 4)
      (ζt := t n) hN1 hτU hη le_rfl (by linarith [hclaim]) (ht n)
    have e : (Nsz sz n * (1 / 4 * ouEtaQ sz 𝔡 n))⁻¹ = 4 * (Nsz sz n * ouEtaQ sz 𝔡 n)⁻¹ := by
      rw [show Nsz sz n * (1 / 4 * ouEtaQ sz 𝔡 n) = (Nsz sz n * ouEtaQ sz 𝔡 n) / 4 by ring, inv_div]
      ring
    rw [← e]; exact hh2
  · filter_upwards [hbw, hWO, hE1, hE5, hE7] with n hNW hWOn hW1 hc5 h2
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have hN2 := RandomLayer_two_N_le sz h𝔠 hτU.le hτ12 hNW hW1 h2
    have ha0 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := Real.rpow_pos_of_pos hW0 _
    have hid := Eq729B_Ld_mul_etaQ sz n 𝔡
    have ha2 : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d =
        ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hW0.le,
        ← Real.rpow_natCast ((sz.W n : ℕ) : ℝ) d, ← Real.rpow_add hW0]
      congr 1; push_cast; ring
    have hρc : 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) * c := (div_le_iff₀ hc).1 hc5
    have hlam := hWOn.1
    have hη0 : 0 < ouEtaQ sz 𝔡 n := by
      unfold ouEtaQ
      have := Real.rpow_pos_of_pos hW0 (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hW0 ((d : ℝ) / 2)
      have := lt_of_lt_of_le ha0 hlam
      have := Nsz_pos sz n
      positivity
    generalize ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) = a at *
    generalize ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) = ρ at *
    have hx : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) ≤ sz.lam n * a / 2 := by
      have e : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) * (ρ * c) = sz.lam n * a := by
        rw [← hid]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left hρc
        (show 0 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) by positivity)]
    have hy : ((sz.L n : ℕ) : ℝ) ^ d * t n ≤ a ^ 2 / 2 := by
      have h1 := RandomLayer_Ld_mul_rpow sz n τU
      have h2' : Nsz sz n ^ τU / ((sz.W n : ℕ) : ℝ) ^ d ≤ a ^ 2 / 2 := by
        rw [div_le_iff₀ hWd, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2), ha2]
        linarith
      exact (mul_le_mul_of_nonneg_left (ht n) hLd.le).trans (h1 ▸ h2')
    calc ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n)
        = ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) + ((sz.L n : ℕ) : ℝ) ^ d * t n := by ring
      _ ≤ sz.lam n * a / 2 + a ^ 2 / 2 := add_le_add hx hy
      _ ≤ sz.lam n ^ 2 := by nlinarith
  · filter_upwards [hbw, hWO, hE1, hE2, hE6] with n hNW hWOn hW1 hW2 hc6
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    have ha0 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) := Real.rpow_pos_of_pos hW0 _
    have hid := Eq729B_Ld_mul_etaQ sz n 𝔡
    have hρc : 2 * (𝔡⁻¹) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) * c := (div_le_iff₀ hc).1 hc6
    have hlam := hWOn.1
    have hlam2 := hWOn.2
    have hη0 : 0 < ouEtaQ sz 𝔡 n := by
      unfold ouEtaQ
      have := Real.rpow_pos_of_pos hW0 (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hW0 ((d : ℝ) / 2)
      have := lt_of_lt_of_le ha0 hlam
      have := Nsz_pos sz n
      positivity
    have hNW1 : Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) := by
      have := RandomLayer_N_le_W h𝔠 hNW hW1 hτU.le (b := 1) (by rw [div_le_iff₀ h𝔠]; linarith)
      rwa [Real.rpow_one] at this
    have hy : ((sz.L n : ℕ) : ℝ) ^ d * t n ≤ 1 / 2 := by
      have h1 := RandomLayer_Ld_mul_rpow sz n τU
      have hWW : ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [← pow_two]; exact pow_le_pow_right₀ hW1 (by omega)
      have h2' : Nsz sz n ^ τU / ((sz.W n : ℕ) : ℝ) ^ d ≤ 1 / 2 := by
        rw [div_le_iff₀ hWd]; nlinarith
      exact (mul_le_mul_of_nonneg_left (ht n) hLd.le).trans (h1 ▸ h2')
    generalize ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) = a at *
    generalize ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) = ρ at *
    have hx : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) ≤ 1 / 2 := by
      have e : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) * (ρ * c) = sz.lam n * a := by
        rw [← hid]; field_simp
      have hla : sz.lam n * a ≤ (𝔡⁻¹) ^ 2 := by
        have : a ≤ 𝔡⁻¹ := hlam.trans hlam2
        have := hlam2
        nlinarith [mul_le_mul hlam2 (hlam.trans hlam2) ha0.le (inv_pos.2 h𝔡).le]
      have hq : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) := by positivity
      have hD : 0 < (𝔡⁻¹) ^ 2 := by positivity
      have h1 : ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) * (2 * (𝔡⁻¹) ^ 2) ≤ (𝔡⁻¹) ^ 2 :=
        calc _ ≤ ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) * (ρ * c) :=
              mul_le_mul_of_nonneg_left hρc hq
          _ = sz.lam n * a := e
          _ ≤ _ := hla
      by_contra h
      push Not at h
      nlinarith [mul_pos (sub_pos.2 h) hD]
    calc ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c + t n)
        = ((sz.L n : ℕ) : ℝ) ^ d * (ouEtaQ sz 𝔡 n / c) + ((sz.L n : ℕ) : ℝ) ^ d * t n := by ring
      _ ≤ 1 / 2 + 1 / 2 := add_le_add hx hy
      _ = 1 := by norm_num

/-! ### The scales -/

/-- `0 < η_LL`. -/
theorem RandomLayer_etaLL_pos (sz : Sizes d) (τU : ℝ) (n : ℕ) : 0 < ouEtaLL sz τU n :=
  Real.rpow_pos_of_pos (Nsz_pos sz n) _

/-- `η_LL ≤ 1` for `τ_U ≤ 1/2` (`N ≥ 1`). -/
theorem RandomLayer_etaLL_le_one (sz : Sizes d) {τU : ℝ} (hτU : τU ≤ 1 / 2) (n : ℕ) :
    ouEtaLL sz τU n ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (RandomLayer_one_le_N sz n) (by linarith)

/-- `0 < η_Q` where `0 < lam n` (the scale `η_Q = W^{-𝔡/3} lam W^{d/2}/N` carries `lam`). -/
theorem RandomLayer_etaQ_pos (sz : Sizes d) (𝔡 : ℝ) {n : ℕ} (hlam : 0 < sz.lam n) :
    0 < ouEtaQ sz 𝔡 n := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have := Real.rpow_pos_of_pos hW (-(𝔡 / 3)); have := Real.rpow_pos_of_pos hW ((d : ℝ) / 2)
  have := Nsz_pos sz n
  unfold ouEtaQ
  positivity

/-- `η_Q ≤ 1` eventually (`queDomain` at `E = 0`, `κ = 2`, `ε₀ = 𝔡/3`: `W → ∞`, `lam ≤ 𝔡⁻¹`). -/
theorem RandomLayer_etaQ_le_one (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, ouEtaQ sz 𝔡 n ≤ 1 := by
  have h𝔡 := hA.2.1
  filter_upwards [queDomain sz hA (ε₀ := 𝔡 / 3) (κ := 2) (by linarith) (by linarith)] with n hn
  have h : sz.locDomain 2 (𝔠 * (𝔡 - 𝔡 / 3)) n
      (((0 : ℝ) : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) := hn 0 (by norm_num)
  simpa using h.2.2

/-! ## Compiled nonempty instances

`d = 3`, `sz0` (`Defs/Sizes.lean:260`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`,
`W = 32`, `N = 2097152`), `sz0.Admissible (1/6) (1/10)`, `κ = 1/10`, `c = c_κ = √(κ(4-κ))/8`,
`τ_U = ouTauMax (1/6) (1/10) = 1/720`, the times `t_n = ouTStar sz0 τ_U n = N^{-1+τ_U} > 0` (so `ζ(t_n) > 0`
and `t₁ < t₀`), the flow data of `RandomLayer_lem28` at `z_n = i η_LL`, `E = 0`; every hypothesis is
discharged. -/

namespace RandomLayerInst

open RBM.Gauss.SizesInst

private theorem tau_eq : ouTauMax (1 / 6) (1 / 10) = 1 / 720 := by
  unfold ouTauMax; norm_num [min_def]

private theorem tau_pos : 0 < ouTauMax (1 / 6) (1 / 10) := by rw [tau_eq]; norm_num

private def zLL (n : ℕ) : ℂ :=
  ((0 : ℝ) : ℂ) + ((ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) n : ℝ) : ℂ) * Complex.I

private theorem hc0 : 0 < Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8 :=
  div_pos (Real.sqrt_pos.2 (by norm_num)) (by norm_num)

/-- `RandomLayer_lem28` at `e = 0`, `η = 1/2`, `κ = 1/10`. -/
theorem inst_lem28 : ∃ z : ℂ, z = ((0 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I ∧ 0 < z.im ∧
    |lemE z| ≤ 2 - 1 / 10 ∧ 1 / 16 ≤ lemT z ∧ lemT z < 1 ∧
    etaT (lemE z) (lemT z) = Real.sqrt (lemT z) * (1 / 2) ∧ (1 / 2 : ℝ) / 4 ≤ etaT (lemE z) (lemT z) ∧
    etaT (lemE z) (lemT z) ≤ 1 / 2 ∧
    1 - lemT z ≤ (1 / 2 : ℝ) / (Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8) :=
  ⟨_, rfl, RandomLayer_lem28 (κ := 1 / 10) (e := 0) (η := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) rfl⟩

/-- `RandomLayer_rowsLL` and `RandomLayer_rowsQ` at `sz0`, `t = ouTStar`. -/
theorem inst_rowsLL :
    (∀ᶠ n in atTop, ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n ≤
      Nsz sz0 n ^ (-(ouTauMax (1 / 6) (1 / 10) / 2)) * (ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) n / 4)) ∧
    (∀ᶠ n in atTop, 4 * (Nsz sz0 n * ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) n)⁻¹ ≤
      Nsz sz0 n ^ (-(ouTauMax (1 / 6) (1 / 10) / 2))) ∧
    (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) n /
      (Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8) + ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n) ≤
      sz0.lam n ^ 2) ∧
    (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) n /
      (Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8) + ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n) ≤ 1) :=
  RandomLayer_rowsLL sz0 (le_refl 3) sz0_admissible tau_pos le_rfl hc0 (fun _ => le_rfl)

theorem inst_rowsQ :
    (∀ᶠ n in atTop, ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n ≤
      Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10)) * (ouEtaQ sz0 (1 / 10) n / 4)) ∧
    (∀ᶠ n in atTop, 4 * (Nsz sz0 n * ouEtaQ sz0 (1 / 10) n)⁻¹ ≤ Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10))) ∧
    (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (ouEtaQ sz0 (1 / 10) n /
      (Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8) + ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n) ≤
      sz0.lam n ^ 2) ∧
    (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (ouEtaQ sz0 (1 / 10) n /
      (Real.sqrt ((1 / 10 : ℝ) * (4 - 1 / 10)) / 8) + ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)) n) ≤ 1) :=
  RandomLayer_rowsQ sz0 (le_refl 3) sz0_admissible tau_pos le_rfl hc0 (fun _ => le_rfl)

/-- `RandomLayer_rows` at the flow data of `RandomLayer_lem28` at `z_n = i η_LL` (`E = 0`),
`τ_D = τ_U/2`, `t_n = ouTStar`: the conclusions are the hypotheses of `gueGrid_pathBounds`. -/
example :=
  RandomLayer_rows sz0 (κ := 1 / 10) (τD := ouTauMax (1 / 6) (1 / 10) / 2) (e := fun _ => 0)
    (η := ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10))) (t := ouTStar sz0 (ouTauMax (1 / 6) (1 / 10)))
    (by norm_num) zLL (fun n => rfl) (fun n => by norm_num) (RandomLayer_etaLL_pos sz0 _)
    (RandomLayer_etaLL_le_one sz0 (by rw [tau_eq]; norm_num)) (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    inst_rowsLL.1 inst_rowsLL.2.1 inst_rowsLL.2.2.1 inst_rowsLL.2.2.2

/-- The scales at `sz0`. -/
theorem inst_etaLL : 0 < ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) 0 ∧
    ouEtaLL sz0 (ouTauMax (1 / 6) (1 / 10)) 0 ≤ 1 :=
  ⟨RandomLayer_etaLL_pos sz0 _ 0, RandomLayer_etaLL_le_one sz0 (by rw [tau_eq]; norm_num) 0⟩

theorem inst_etaQ : 0 < ouEtaQ sz0 (1 / 10) 0 ∧ ∀ᶠ n in atTop, ouEtaQ sz0 (1 / 10) n ≤ 1 :=
  ⟨RandomLayer_etaQ_pos sz0 _ (by change 0 < ((2 * (((0 : ℕ) : ℝ) + 1)) ^ 6)⁻¹; norm_num),
    RandomLayer_etaQ_le_one sz0 sz0_admissible⟩

end RandomLayerInst

end RBM.Univ.GUEPhase

end
