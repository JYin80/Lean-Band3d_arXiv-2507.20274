/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.CltFar
import RBM3D.Evolution.CltMoments2G
import RBM3D.Evolution.MeanFarG

/-!
# `lem;CLT`, far part, over the carrier: the pin `STCltFargL` (ticket T2479, X1b-2, targets 5-9)

Additive restatement of `Evolution/CltFar.lean:69-104, 308-1857` over a flow carrier `C : FlowFM sz`
and a law `μ`; none of the four band files is edited.  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex`, `lem;CLT` (`3_5:2173-2176`), proof `3_5:2182-2249`.  Mixed
charges `σ 0 ≠ σ 1` only (the range of `STThPropsg`, `STKpropsg`); the propagator is the carrier's
`STThg` (U-C4); the energy enters through `κ ≤ Im (C.m n)` (X1-C1), no `|E| ≤ 2 - κ`, `‖m‖ = 1`,
`PropSpin`, `Theta`, `seqP`, `STLKM` in any generic statement; no coupling comparison (UBA-C1).
The band producers and the band bridge (section 6) and the instances (section 7) are at the band
data.

* **Target 5.** `cltFar_domg`, `cltFar_offg`, `cltFar_flucg` (band `CltFar.DomStmt`, `OffStmt`,
  `FlucStmt`, theorems `:586`, `:1167`, `:1505`): `STGdecayWgL` for `STGdecayW`, `κ ≤ Im (C.m n)`
  for `|E| ≤ 2 - κ`, `μ` for `seqP`, `STCltIsoConclgL` for `STCltIsoConcl`.
* **Target 6.** `stCltFargL_holds d : STCltFargL d` (the merged pin of `Chain/CltGen`, proved for
  every `d`): the mean part `meanFar_eventuallyg` at `τ/2`, `cltFar_flucg` at `(τ/2, D+3)`,
  `cltFar_offg` at `(D₀, D+1)`, `D₀ = 6d/5 + (d-2)/𝔠 + 1`, the deterministic split
  `f = 𝔼 f + c_n fluc + off` (`cltMom2_decompg`) and the union over
  `{σ // σ 0 ≠ σ 1} × (Fin 2 → Z_L^d)` inside `PrecL`.
* **Target 7.** `bandFM_STThPropsg`, `bandFM_STKpropsg`: the band producers of the pins
  `STThPropsg`, `STKpropsg` (`prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`,
  `bandFM_STThg`, `KLK_two`; the proofs are the private band producers of `MeanFarG`, brought in
  by `open private`).
* **Target 8.** `stCltFar_of_gL d : STCltFargL d → STCltFar d` (the band bridge, `HCltOf` as in
  `stCltIso_holds`).
* **Target 9.** Compiled nonempty instances at the band data of `Step5Inst`
  (`d = 3`, `szCL`, `sCL`, `tCL`).

Reused by name or by `open private` (model-free or size-level): the size facts, `cltFarZ`,
`cltFar_dom_key`, `cltFar_dom_tail`, `cltFar_wpow_le`, `cltFar_one_sub_ge`, `cltFar_double_sum_le`,
`cltFar_zeta_off`, `cltFar_off_numeric`, the arithmetic of the moment step (`cltFar_Lp_le`,
`cltFar_Bq_le`, `cltFar_Gq_le`, `cltFar_assemble`, ...), `cltFar_zeta_ge`, `cltFar_union_bound`,
`cltFar_union_numeric` (`Evolution/CltFar.lean`), and `meanFarG_B`, `meanFarG_B_bound`,
`meanFarG_chk_*` (`Evolution/MeanFarG.lean`).  Restated under the stem `cltFarG_`: what mentions
the model.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private cltFar_ell_sq cltFar_c3 cltFar_c0 cltFar_c3_pos cltFar_polylog cltFarZ cltFar_one_le_L cltFar_one_le_W
  cltFar_one_le_N cltFar_Lpow_le cltFar_Wpow_le cltFar_L_le cltFar_W_le cltFar_card_Zd cltFar_card_pair_le
  cltFar_W_rpow_le cltFar_dom_key cltFar_dom_tail cltFar_wpow_le cltFar_one_sub_ge cltFar_double_sum_le
  cltFar_zeta_off cltFar_off_numeric cltFar_Npow_le_W cltFarKp cltFarKp_nonneg cltFar_Lp_le cltFar_Bq_le
  cltFar_Gq_le cltFar_R_le cltFar_assemble cltFar_theta_eq cltFar_theta_ge cltFar_zeta_ge cltFar_union_bound
  cltFar_union_numeric from RBM3D.Evolution.CltFar
open private meanFarG_B meanFarG_B_bound
  from RBM3D.Evolution.MeanFarG

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. The single good event and the per-label tail (target 5a) -/

section Dom

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The single good event of `(Eq:Gdecay_w)` at `u = s`** (`(eq:propcalB)`, `3_5:2155`): the union over `(σ, a, b)` is inside the
probability, by taking the witnesses `u = (s, σ, ![a,b])` in the union of `STGdecayWgL` (band `cltFar_good_event`, `CltFar:351`). -/
private theorem cltFarG_good_event {s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayWgL C μ s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, μ {ω | ∃ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * cltFarZ sz n (s n) Dw (zdistInf d (sz.L n) (a - b)) <
          ‖C.L n (s n) σ ![a, b] ω - C.K n (s n) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [hG Dw hDw τ hτ D₁ hD₁] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω ⟨σ, a, b, hω⟩
  refine ⟨(⟨s n, le_rfl, hst n⟩, σ, ![a, b]), ?_⟩
  have h1 : (1 - s n) ≠ 0 := (sub_pos.2 (hs1 n)).ne'
  simp only [div_self h1, Real.one_rpow, one_mul]
  have e : (![a, b] : Fin 2 → Zd d (sz.L n)) 0 - (![a, b] : Fin 2 → Zd d (sz.L n)) 1 = a - b := by simp
  rw [e]
  exact hω

/-- The single-index form of `cltFarG_good_event` (band `cltFar_bad_one`). -/
private theorem cltFarG_bad_one {s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayWgL C μ s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * cltFarZ sz n (s n) Dw (zdistInf d (sz.L n) (a - b)) <
          ‖C.L n (s n) σ ![a, b] ω - C.K n (s n) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [cltFarG_good_event C μ hs1 hst hG hDw hτ hD₁] with n hn σ a b
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact ⟨σ, a, b, hω⟩

/-- **Target 5a: the per-label tail `CltMom2.DomHypg`** (`(eq:propcalB)`, `3_5:2155`; band `cltFar_dom`, `CltFar:586`) from
`(Eq:Gdecay_w)` at `u = s` (`STGdecayWgL`) with `Λ' = N^τ`, `q₁ = N^{-D₁}`, eventually, every `σ`.  The event
`{N^τ < |𝗕_β| (r^{d-2} + 1)}`, `𝗕 = A^{6/5}(𝓛-𝒦)^{(2)}_{s,σ,β}`, is contained in the `≺` event
`{N^{τ/2} ζ' < |(𝓛-𝒦)^{(2)}|}` of `(Eq:Gdecay_w)` (`cltFarG_bad_one` at `(τ/2, D₁, D_w = 3/𝔠)`) because
`A^{6/5} R ζ' ≤ c₀ + 2𝔡^{-4} ≤ N^{τ/2}` (`cltFar_dom_key`, `cltFar_dom_tail`). -/
theorem cltFar_domg (hd : 3 ≤ d) {𝔠 𝔡 Cd : ℝ} (hAdm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs1 : ∀ n, s n < 1)
    (hst : ∀ n, s n ≤ t n) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool,
      CltMom2.DomHypg C μ n (s n) σ (((sz.size n : ℕ) : ℝ) ^ τ) (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hDw : (0 : ℝ) < ((3 : ℕ) : ℝ) / 𝔠 := by positivity
  have hbad := cltFarG_bad_one C μ hs1 hst hG hDw (τ := τ / 2) (D₁ := D₁) (half_pos hτ) hD₁
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hbig : ∀ᶠ n in atTop, cltFar_c0 d + 2 * (𝔡⁻¹) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hSz).eventually_ge_atTop _
  filter_upwards [hbad, hev, hBw, hWO, hbig] with n hbadn hAn hBwn hWOn hbign
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  intro σ β _
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (cltFar_one_le_N sz n)
  have hreg_s : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s n := le_trans (hreg n).1 (by linarith [hst n])
  have hrL : zdistInf d (sz.L n) (β 0 - β 1) ≤ sz.L n := st5_zdistInf_le sz n _
  have hkey := cltFar_dom_key hd sz n (hs1 n) hg hreg_s hA1 (zdistInf d (sz.L n) (β 0 - β 1)) hrL
    (((3 : ℕ) : ℝ) / 𝔠)
  have htail := cltFar_dom_tail sz n h𝔠 hA1 hg hgΛ hBwn (zdistInf d (sz.L n) (β 0 - β 1)) hrL
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set A : ℝ := STAI sz n with hAdef
  set R : ℝ := ((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) ^ (d - 2) + 1 with hRdef
  set ζ' : ℝ := sz.Bctl n (s n) ^ (1 / 5 : ℝ) * STWB sz n (s n) (zdistInf d (sz.L n) (β 0 - β 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (β 0 - β 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-(((3 : ℕ) : ℝ) / 𝔠)) with hζ'
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hZ : A ^ (6 / 5 : ℝ) * R * ζ' ≤ N ^ (τ / 2) := by
    have := hkey
    linarith
  have hβ : (![β 0, β 1] : Fin 2 → Zd d (sz.L n)) = β := by
    funext i; fin_cases i <;> rfl
  have hnormB : ∀ ω, ‖STcltBg C n (s n) σ β ω‖ =
      A ^ (6 / 5 : ℝ) * ‖C.L n (s n) σ ![β 0, β 1] ω - C.K n (s n) σ ![β 0, β 1]‖ := by
    intro ω
    have hA65 : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := by positivity
    rw [hβ]
    unfold STcltBg
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hA65]
    rfl
  refine le_trans (measure_mono ?_) (hbadn σ (β 0) (β 1))
  intro ω hω
  have hω' : N ^ τ < ‖STcltBg C n (s n) σ β ω‖ * R := hω
  rw [hnormB] at hω'
  change N ^ (τ / 2) * ζ' < ‖C.L n (s n) σ ![β 0, β 1] ω - C.K n (s n) σ ![β 0, β 1]‖
  by_contra hcon0
  have hcon := not_lt.1 hcon0
  have hA65 : 0 ≤ A ^ (6 / 5 : ℝ) := Real.rpow_nonneg hA0.le _
  have hR0 : 0 ≤ R := by positivity
  have h1 : A ^ (6 / 5 : ℝ) * ‖C.L n (s n) σ ![β 0, β 1] ω - C.K n (s n) σ ![β 0, β 1]‖ * R ≤
      A ^ (6 / 5 : ℝ) * (N ^ (τ / 2) * ζ') * R := by gcongr
  have h2 : A ^ (6 / 5 : ℝ) * (N ^ (τ / 2) * ζ') * R = N ^ (τ / 2) * (A ^ (6 / 5 : ℝ) * R * ζ') := by ring
  have h3 : N ^ (τ / 2) * (A ^ (6 / 5 : ℝ) * R * ζ') ≤ N ^ (τ / 2) * N ^ (τ / 2) :=
    mul_le_mul_of_nonneg_left hZ (Real.rpow_nonneg hN0.le _)
  have h4 : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  linarith

end Dom

/-! ## 2. Per-index bounds: the propagator, `𝒦`, the weights `Z`, the envelope `BY` -/

section PerN

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- Conjuncts 1 (shift) and 3 (`(prop:ThfadC)`) of `STThPropsg` at one index `n`, for every time `u ∈ [0,1)` and mixed `σ`
(band `CltFarH5`, `CltFar:652`). -/
private def cltFarG_H (n : ℕ) (C₅ c₅ : ℝ) : Prop :=
  ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
    (∀ x y, STThg C n (σ 0) (σ 1) u x y = STThg C n (σ 0) (σ 1) u 0 (y - x)) ∧
    ∀ a, ‖STThg C n (σ 0) (σ 1) u 0 a‖ ≤ C₅ * Bparam d (sz.L n) (sz.lam n) u (zdistD d (sz.L n) a) *
      Real.exp (-c₅ * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (sz.lam n) u)

/-- **`(prop:ThfadC)` in the sup form**: `|Θ_u(x,y)| ≤ C₅ (1 + 2^{d-1}) / g²` for `u < 1`, `g²/L² ≤ 1 - u`
(`meanFar_T1`, `Evolution/MeanFar.lean:762`; band `cltFar_Theta_all`, `CltFar:670`). -/
private theorem cltFarG_Theta_all (hd : 3 ≤ d) (n : ℕ) {u C₅ c₅ : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - u) (hC₅ : 0 ≤ C₅) (hc₅ : 0 < c₅)
    (h5 : cltFarG_H C n C₅ c₅) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (x y : Zd d (sz.L n)) :
    ‖STThg C n (σ 0) (σ 1) u x y‖ ≤ C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := by
  obtain ⟨hsh, hdec⟩ := h5 u hu0 hu1 σ hσ
  rw [hsh x y]
  have h := meanFar_T1 hd (sz.three_le_L n) hg hu1 hreg hC₅ hc₅ (fun x => STThg C n (σ 0) (σ 1) u 0 x) hdec (y - x)
  refine h.trans ?_
  have hr : (1 : ℝ) ≤ (((zdistInf d (sz.L n) (y - x) : ℕ) : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (y - x) : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have hc : 0 ≤ C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := by positivity
  exact div_le_self hc hr

/-- **The uniform constant `c_Θ`** of the far steps: eventually in `n`, `A ≥ 1`, `|Θ_{t}(x,y)| ≤ c_Θ / g²` at the time `t n` and
`|𝒦^{(2)}_{s,σ,(a,b)}| ≤ c_Θ` at the time `s n` (mixed `σ`): from `STThPropsg` conjuncts 1, 3 and `STKpropsg` conjunct 2
(`‖𝒦‖ ≤ c₁/A ≤ c₁`); replaces the band `cltFar_Theta_all`, `cltFar_K_le`, `cltFar_K_le'`. -/
private theorem cltFarG_inputs (hd : 3 ≤ d) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (hreg : STReg5I sz s t) (hev : ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ STAI sz n) (hTh : STThPropsg C)
    (hKp : STKpropsg C s) :
    ∃ cΘ : ℝ, 0 ≤ cΘ ∧ ∀ᶠ n in atTop, 0 < sz.lam n ∧ 1 ≤ STAI sz n ∧
      (∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ x y : Zd d (sz.L n),
        ‖STThg C n (σ 0) (σ 1) (t n) x y‖ ≤ cΘ / sz.lam n ^ 2) ∧
      (∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a b : Zd d (sz.L n), ‖C.K n (s n) σ ![a, b]‖ ≤ cΘ) := by
  obtain ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, H⟩ := hTh
  obtain ⟨-, c₁, hc₁, hKb⟩ := hKp
  refine ⟨max (C₅ * (1 + 2 ^ (d - 1))) c₁, le_max_of_le_right hc₁.le, ?_⟩
  filter_upwards [hev, H, hKb] with n hn hHn hKn
  obtain ⟨hg, hA1⟩ := hn
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have h5 : cltFarG_H C n C₅ c₅ := fun u hu0 hu1 σ hσ => by
    obtain ⟨hsh, -, hdec, -, -⟩ := hHn u hu0 hu1 σ hσ
    exact ⟨hsh, hdec⟩
  refine ⟨hg, hA1, fun σ hσ x y => ?_, fun σ hσ a b => ?_⟩
  · have ht0 : 0 ≤ t n := (hs0 n).trans (hst n)
    have ht1 : t n < 1 := by
      have h1 := (hreg n).1
      have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
        exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
      have : 0 < sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := div_pos (pow_pos hg 2) (pow_pos hL0 2)
      linarith
    exact (cltFarG_Theta_all C hd n ht0 ht1 hg (hreg n).1 hC₅.le hc₅ h5 σ hσ x y).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hg2.le)
  · exact ((hKn σ hσ a b).trans (div_le_self hc₁.le hA1)).trans (le_max_right _ _)

/-- `|Z_β| ≤ 2 c_Θ²` for every `β` (`g² |Θ| ≤ c_Θ`; band `cltFar_Z_le`, `CltFar:701`). -/
private theorem cltFarG_Z_le (n : ℕ) {s t cΘ : ℝ} (hcΘ0 : 0 ≤ cΘ) (hg : 0 < sz.lam n) (σ : Fin 2 → Bool)
    (hT : ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ cΘ / sz.lam n ^ 2)
    (a β : Fin 2 → Zd d (sz.L n)) : ‖CltMom2.Zg C n s t σ a β‖ ≤ 2 * cΘ ^ 2 := by
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hg2T : ∀ x y, sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ cΘ := by
    intro x y
    calc sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ sz.lam n ^ 2 * (cΘ / sz.lam n ^ 2) :=
          mul_le_mul_of_nonneg_left (hT x y) hg2.le
      _ = cΘ := by field_simp
  unfold CltMom2.Zg
  split_ifs
  · rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hg2.le]
    have h1 := hg2T (a 0) (β 0)
    have h2 : sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖ ≤ 2 * cΘ := by
      calc _ ≤ sz.lam n ^ 2 * (‖STThg C n (σ 0) (σ 1) t (β 1) (a 1)‖ + ‖STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖) :=
            mul_le_mul_of_nonneg_left (norm_sub_le _ _) hg2.le
        _ = sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 1) (a 1)‖ +
            sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖ := by ring
        _ ≤ cΘ + cΘ := add_le_add (hg2T _ _) (hg2T _ _)
        _ = 2 * cΘ := by ring
    calc sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (a 0) (β 0)‖ *
        (sz.lam n ^ 2 * ‖STThg C n (σ 0) (σ 1) t (β 1) (a 1) - STThg C n (σ 0) (σ 1) t (β 0) (a 1)‖)
        ≤ cΘ * (2 * cΘ) := mul_le_mul h1 h2 (by positivity) hcΘ0
      _ = 2 * cΘ ^ 2 := by ring
  · rw [norm_zero]; positivity

/-- `Σ_β |Z_β| ≤ N² · 2 c_Θ²` (band `cltFar_ZZ_le`). -/
private theorem cltFarG_ZZ_le (n : ℕ) {s t cΘ : ℝ} (hcΘ0 : 0 ≤ cΘ) (hg : 0 < sz.lam n) (σ : Fin 2 → Bool)
    (hT : ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ cΘ / sz.lam n ^ 2) (a : Fin 2 → Zd d (sz.L n)) :
    ∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * (2 * cΘ ^ 2) := by
  have h := Finset.sum_le_card_nsmul Finset.univ (fun β : Fin 2 → Zd d (sz.L n) => ‖CltMom2.Zg C n s t σ a β‖)
    (2 * cΘ ^ 2) (fun β _ => cltFarG_Z_le C n hcΘ0 hg σ hT a β)
  rw [Finset.card_univ, nsmul_eq_mul] at h
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_right (cltFar_card_pair_le sz n) (by positivity)

/-- `η_s^{-2} ≤ N⁴/κ'²` (`1 - s ≥ N^{-2}`, `Im m ≥ κ'`; band `cltFar_eta_inv_le`, `CltFar:790`). -/
private theorem cltFarG_eta_inv_le (n : ℕ) {s t κ' : ℝ} (hd2 : 2 ≤ d) (hκ' : κ' ≤ (C.m n).im)
    (hκ'0 : 0 < κ') (hst : s ≤ t) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) : (etaOf (C.m n) s)⁻¹ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1s := cltFar_one_sub_ge sz n hd2 hst hreg hA1
  have hη : κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2) ≤ etaOf (C.m n) s := by
    unfold etaOf
    exact mul_le_mul hκ' h1s (by positivity) (hκ'0.le.trans hκ') |>.trans_eq (by ring)
  have hη0 : 0 < κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2) := by positivity
  have h1 : (etaOf (C.m n) s)⁻¹ ≤ (κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2))⁻¹ := inv_anti₀ hη0 hη
  have h2 : (etaOf (C.m n) s)⁻¹ ^ 2 ≤ ((κ' * (1 / ((sz.size n : ℕ) : ℝ) ^ 2))⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.2 (hη0.le.trans hη)) h1 2
  refine h2.trans (le_of_eq ?_)
  field_simp

/-- **The envelope** `BY ≤ 𝔡^{-4} (κ'^{-2} + c_Θ) N⁶`: `A^{6/5} ≤ A² ≤ 𝔡^{-4}N²`, `η_s^{-2} ≤ N⁴/κ'²`,
`Σ_β |𝒦_β| ≤ N² c_Θ` (band `cltFar_BY_le`, `CltFar:808`). -/
private theorem cltFarG_BY_le (n : ℕ) {s t cΘ κ' 𝔡 : ℝ} (σ : Fin 2 → Bool) (hcΘ0 : 0 ≤ cΘ)
    (hκ' : κ' ≤ (C.m n).im) (hκ'0 : 0 < κ') (hst : s ≤ t) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hA1 : 1 ≤ STAI sz n)
    (hK : ∀ a b : Zd d (sz.L n), ‖C.K n s σ ![a, b]‖ ≤ cΘ) (hd : 2 ≤ d) :
    CltMom2.BYg C n s σ ≤ 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) * ((sz.size n : ℕ) : ℝ) ^ 6 := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hAN : STAI sz n ≤ (𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    unfold STAI
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) (cltFar_Wpow_le sz n) (by positivity) (by positivity)
  have hA65 : STAI sz n ^ (6 / 5 : ℝ) ≤ 𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hA1 (show (6 / 5 : ℝ) ≤ 2 by norm_num)
    rw [Real.rpow_two] at h1
    have h2 : STAI sz n ^ 2 ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 := pow_le_pow_left₀ hA0.le hAN 2
    calc STAI sz n ^ (6 / 5 : ℝ) ≤ ((𝔡⁻¹) ^ 2 * ((sz.size n : ℕ) : ℝ)) ^ 2 := h1.trans h2
      _ = 𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by ring
  have hηinv := cltFarG_eta_inv_le C n hd hκ' hκ'0 hst hreg hA1
  have hKβ : ∀ β : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β‖ ≤ cΘ := by
    intro β
    have hβ : (![β 0, β 1] : Fin 2 → Zd d (sz.L n)) = β := by funext i; fin_cases i <;> rfl
    have := hK (β 0) (β 1)
    rwa [hβ] at this
  have hKsum : ∑ β : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * cΘ := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun β : Fin 2 → Zd d (sz.L n) => ‖C.K n s σ β‖) cΘ
      (fun β _ => hKβ β)
    rw [Finset.card_univ, nsmul_eq_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_right (cltFar_card_pair_le sz n) hcΘ0)
  unfold CltMom2.BYg
  have hsum0 : 0 ≤ (etaOf (C.m n) s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β‖ := by positivity
  calc STAI sz n ^ (6 / 5 : ℝ) * ((etaOf (C.m n) s)⁻¹ ^ 2 + ∑ β : Fin 2 → Zd d (sz.L n), ‖C.K n s σ β‖)
      ≤ (𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2) *
          (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 * cΘ) :=
        mul_le_mul hA65 (add_le_add hηinv hKsum) hsum0 (by positivity)
    _ ≤ 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) * ((sz.size n : ℕ) : ℝ) ^ 6 := by
        have hN24 : ((sz.size n : ℕ) : ℝ) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ 6 := pow_le_pow_right₀ hN1 (by norm_num)
        have hd4 : 0 ≤ 𝔡⁻¹ ^ 4 := by
          have : 0 ≤ 𝔡⁻¹ := by
            have := hg.trans_le hgΛ
            exact this.le
          positivity
        have e : (𝔡⁻¹ ^ 4 * ((sz.size n : ℕ) : ℝ) ^ 2) *
            (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 * cΘ) =
            𝔡⁻¹ ^ 4 * (((sz.size n : ℕ) : ℝ) ^ 6 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 4 * cΘ) := by
          field_simp
        rw [e]
        have e2 : 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) * ((sz.size n : ℕ) : ℝ) ^ 6 =
            𝔡⁻¹ ^ 4 * (((sz.size n : ℕ) : ℝ) ^ 6 / κ' ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 6 * cΘ) := by
          field_simp
        rw [e2]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_right hN24 hcΘ0)) hd4

end PerN

/-! ## 3. Target 5b: the off-window part `CltMom2.offg` -/

section Off

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The sum bound for `CltMom2.offg`**: `|off| ≤ (1-s)² (L^d)² K_Θ X (2 K_Θ)` when `|Θ_t| ≤ K_Θ` and every off-window
`|𝓑 - 𝔼𝓑|` is at most `X` (band `cltFar_off_sum_le`, `CltFar:897`). -/
private theorem cltFarG_off_sum_le (n : ℕ) {s t : ℝ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) {KΘ Xb : ℝ} (hKΘ : 0 ≤ KΘ) (hXb : 0 ≤ Xb)
    (hΘ : ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ KΘ)
    (hX : ∀ b₁ b₂ : Zd d (sz.L n),
      Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) →
      ‖(C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) -
        ∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ‖ ≤ Xb) :
    ‖CltMom2.offg C μ n s t σ a ω‖ ≤
      (1 - s) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (KΘ * Xb * (KΘ + KΘ)))) := by
  unfold CltMom2.offg
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have hM : 0 ≤ KΘ * Xb * (KΘ + KΘ) := by positivity
  refine (cltFar_double_sum_le (M := KΘ * Xb * (KΘ + KΘ)) _ _ _ hM ?_).trans ?_
  · intro b₁ b₂ hb
    rw [norm_mul, norm_mul]
    refine mul_le_mul (mul_le_mul (hΘ _ _) (hX b₁ b₂ hb) (norm_nonneg _) hKΘ) ?_ (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (add_le_add (hΘ _ _) (hΘ _ _))
  · rw [cltFar_card_Zd]
    push_cast
    exact le_rfl

/-- **The deterministic bound of `‖offg‖` on the good event** (`(eq:propcalB)`, `3_5:2155`; band `cltFar_off_det`, `CltFar:1045`): if every
`|𝓛^{(2)} - 𝒦^{(2)}|_{s,σ,(b₁,b₂)}` is at most `N ζ'_s(|b₁ - b₂|)` (the single good event of `STGdecayWgL` at `u = s`) and the
per-entry bad events have probability `≤ N^{-D₁}`, then
`|off| ≤ 2 c_Θ² N² (2 N (c₀+1) W^{-D_w} + (N⁴/κ'² + c_Θ) N^{-D₁})`: the sum has `≤ N²` terms, `|Θ_t| ≤ c_Θ/g²`,
`(1-s)² (c_Θ/g²)² ≤ c_Θ²` (`1 - s ≤ g²`), the profile is `≤ (c₀+1) W^{-D_w}` off the window (`cltFar_zeta_off`) and
`|𝔼 𝓑| ≤ N ζ' + (η_s^{-2} + |𝒦|) N^{-D₁}` (`meanFarG_B_bound`, `cltFarG_eta_inv_le`). -/
private theorem cltFarG_off_det [IsProbabilityMeasure μ] (hd : 3 ≤ d) (n : ℕ) {s t cΘ κ' Dw D₁ : ℝ}
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) (hL : meanFarG_LEnv C n s)
    (hκ' : κ' ≤ (C.m n).im) (hκ'0 : 0 < κ') (hst : s < t) (hs1 : s < 1) (hcΘ0 : 0 ≤ cΘ)
    (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hreg2 : 1 - s ≤ sz.lam n ^ 2)
    (hA1 : 1 ≤ STAI sz n) (hT : ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ cΘ / sz.lam n ^ 2)
    (hK : ∀ a b : Zd d (sz.L n), ‖C.K n s σ ![a, b]‖ ≤ cΘ) (hDw : 0 < Dw)
    (hlwD : Dw ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hω : ∀ b₁ b₂ : Zd d (sz.L n),
      ‖C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)))
    (hP1 : ∀ b₁ b₂ : Zd d (sz.L n),
      μ {ω' | ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) <
          ‖C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖CltMom2.offg C μ n s t σ a ω‖ ≤ 2 * cΘ ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 2 *
      (2 * (((sz.size n : ℕ) : ℝ) * ((cltFar_c0 d + 1) * ((sz.W n : ℕ) : ℝ) ^ (-Dw))) +
        (((sz.size n : ℕ) : ℝ) ^ 4 / κ' ^ 2 + cΘ) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  have hreg_s : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s := le_trans hreg (by linarith)
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have hW1 := cltFar_one_le_W sz n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set Xb : ℝ := 2 * (N * ((cltFar_c0 d + 1) * W ^ (-Dw))) + (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁) with hXb
  have hW0 : 0 < W := by linarith
  have hXb0 : 0 ≤ Xb := by
    have : 0 ≤ N ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have : 0 ≤ W ^ (-Dw) := Real.rpow_nonneg hW0.le _
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hKΘ : 0 ≤ cΘ / sz.lam n ^ 2 := by positivity
  have hη := cltFarG_eta_inv_le C n (s := s) (t := t) (by omega) hκ' hκ'0 hst.le hreg hA1
  have hX : ∀ b₁ b₂ : Zd d (sz.L n),
      Real.log W ^ 3 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) →
      ‖(C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) -
        ∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ‖ ≤ Xb := by
    intro b₁ b₂ hoff
    have hr : zdistInf d (sz.L n) (b₁ - b₂) ≤ sz.L n := st5_zdistInf_le sz n _
    have hζ := cltFar_zeta_off hd sz n hs1 hg hreg_s hA1 hDw hlwD _ hr hoff
    have hZ0 : 0 ≤ cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) := by
      unfold cltFarZ
      have hBctl0 : 0 ≤ sz.Bctl n s := by
        unfold Sizes.Bctl Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]
        positivity
      have hSTWB0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) (b₁ - b₂)) := by
        unfold STWB Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]
        positivity
      positivity
    have hZ0' : 0 ≤ N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) :=
      mul_nonneg (Real.rpow_nonneg hN0.le _) hZ0
    have hB : ‖∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ‖ ≤
        N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) +
          ((etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![b₁, b₂]‖) * N ^ (-D₁) :=
      meanFarG_B_bound C μ n hL σ b₁ b₂ (τ := 1) (Z := cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)))
        (D₁ := D₁) hZ0' (hP1 b₁ b₂)
    have hX1 := hω b₁ b₂
    have hND : 0 ≤ N ^ (-D₁) := Real.rpow_nonneg hN0.le _
    have hNZ : N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) ≤
        N * ((cltFar_c0 d + 1) * W ^ (-Dw)) := by
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left hζ hN0.le
    have hE2 : ((etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![b₁, b₂]‖) * N ^ (-D₁) ≤
        (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁) :=
      mul_le_mul_of_nonneg_right (add_le_add hη (hK b₁ b₂)) hND
    calc ‖(C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) -
          ∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ‖
        ≤ ‖C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]‖ +
          ‖∫ ω', (C.L n s σ ![b₁, b₂] ω' - C.K n s σ ![b₁, b₂]) ∂μ‖ := norm_sub_le _ _
      _ ≤ N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) +
          (N ^ (1 : ℝ) * cltFarZ sz n s Dw (zdistInf d (sz.L n) (b₁ - b₂)) +
            ((etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![b₁, b₂]‖) * N ^ (-D₁)) := add_le_add hX1 hB
      _ ≤ N * ((cltFar_c0 d + 1) * W ^ (-Dw)) + (N * ((cltFar_c0 d + 1) * W ^ (-Dw)) +
            (N ^ 4 / κ' ^ 2 + cΘ) * N ^ (-D₁)) := by
          gcongr
      _ = Xb := by rw [hXb]; ring
  have hsum := cltFarG_off_sum_le C μ n σ a ω hKΘ hXb0 hT hX
  refine hsum.trans ?_
  have hLd := cltFar_Lpow_le sz n
  have hLd0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have h1 : (1 - s) * (cΘ / sz.lam n ^ 2) ≤ cΘ := by
    calc (1 - s) * (cΘ / sz.lam n ^ 2) = cΘ * ((1 - s) / sz.lam n ^ 2) := by ring
      _ ≤ cΘ * 1 := mul_le_mul_of_nonneg_left (div_le_one_of_le₀ hreg2 hg2.le) hcΘ0
      _ = cΘ := mul_one _
  have h2 : (1 - s) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
      (cΘ / sz.lam n ^ 2 * Xb * (cΘ / sz.lam n ^ 2 + cΘ / sz.lam n ^ 2)))) =
      2 * ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * Xb := by ring
  rw [h2]
  have h3 : ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 ≤ cΘ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by linarith) hKΘ) h1 2
  have h4 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d ≤ N ^ 2 := by nlinarith
  calc 2 * ((1 - s) * (cΘ / sz.lam n ^ 2)) ^ 2 * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * Xb
      ≤ 2 * cΘ ^ 2 * N ^ 2 * Xb := by gcongr
    _ = 2 * cΘ ^ 2 * N ^ 2 * Xb := rfl

/-- **Target 5b: the off-window part** (`(eq:propcalB)`, `3_5:2155`; band `cltFar_off`, `CltFar:1167`): `‖CltMom2.offg‖ ≤ W^{-D}` for every
mixed `σ` and every `a` at once, off an event of probability `≤ N^{-D'}`.  The event is the single good event of `(Eq:Gdecay_w)` at
`u = s` (`cltFarG_good_event` at `(D_w, τ, D₁) = (D + 3/𝔠 + 1, 1, D')`, the union over `(σ, a, b)` being inside `STGdecayWgL`); on it
`cltFarG_off_det` bounds `‖off‖` and `cltFar_off_numeric` gives `≤ W^{-D}` (`N³ ≤ W^{3/𝔠}`, `N⁶ ≤ W^{6/𝔠}`, `W → ∞`, `D_w² ≤ log W`).
The constant `c_Θ` is that of `STThPropsg`, `STKpropsg` (`cltFarG_inputs`). -/
theorem cltFar_offg {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1)
    (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd)
    (hTh : STThPropsg C) (hKp : STKpropsg C s) (D D' : ℝ) (hD : 0 < D) (hD' : 0 < D') :
    ∀ᶠ n in atTop, μ {ω | ∃ σ : Fin 2 → Bool, σ 0 ≠ σ 1 ∧ ∃ a : Fin 2 → Zd d (sz.L n),
        ((sz.W n : ℕ) : ℝ) ^ (-D) < ‖CltMom2.offg C μ n (s n) (t n) σ a ω‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := by
  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hDw : (0 : ℝ) < D + 3 / 𝔠 + 1 := by positivity
  have hD₁ : (0 : ℝ) < D + 6 / 𝔠 + 2 := by positivity
  have hgood := cltFarG_good_event C μ hs1 hst' hG hDw (τ := 1) (D₁ := D') one_pos hD'
  have hbad := cltFarG_bad_one C μ hs1 hst' hG hDw (τ := 1) (D₁ := D + 6 / 𝔠 + 2) one_pos hD₁
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  obtain ⟨cΘ, hcΘ0, hin⟩ := cltFarG_inputs C hd hs0 hst' hreg hev hTh hKp
  have hc0 : 0 < cltFar_c0 d := by
    unfold cltFar_c0
    have := cltFar_c3_pos d
    positivity
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hSz)
  have hWev : ∀ᶠ n in atTop, (D + 3 / 𝔠 + 1) ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧
      2 * cΘ ^ 2 * (2 * (cltFar_c0 d + 1) + 1 / κ ^ 2 + cΘ) ≤ ((sz.W n : ℕ) : ℝ) :=
    ((Real.tendsto_log_atTop.comp hWt).eventually_ge_atTop _).and (hWt.eventually_ge_atTop _)
  filter_upwards [hgood, hbad, hin, hBw, hWO, hWev] with n hgn hbn hinn hBwn hWOn hWn
  obtain ⟨hg, hA1, hTn, hKn⟩ := hinn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hlwD, hbig⟩ := hWn
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 := cltFar_one_le_W sz n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL := meanFarG_lenv_of_rep C μ hrep hκ n (hm n) (hs1 n)
  refine le_trans (measure_mono ?_) hgn
  intro ω hω
  obtain ⟨σ, hσ, a, hσa⟩ := hω
  by_contra hno
  have hω' : ∀ b₁ b₂ : Zd d (sz.L n),
      ‖C.L n (s n) σ ![b₁, b₂] ω - C.K n (s n) σ ![b₁, b₂]‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * cltFarZ sz n (s n) (D + 3 / 𝔠 + 1) (zdistInf d (sz.L n) (b₁ - b₂)) := by
    intro b₁ b₂
    by_contra h
    exact hno ⟨σ, b₁, b₂, not_le.1 h⟩
  have hdet := cltFarG_off_det C μ hd n σ a ω hL (hm n) hκ (hst n) (hs1 n) hcΘ0 hg (hreg n).1 (hreg n).2 hA1
    (hTn σ hσ) (hKn σ hσ) hDw hlwD hω' (fun b₁ b₂ => hbn σ b₁ b₂)
  have hQ3 := cltFar_Npow_le_W hN0 hW0 h𝔠 hBwn 3
  have hQ6 := cltFar_Npow_le_W hN0 hW0 h𝔠 hBwn 6
  have hWN := cltFar_W_le sz (by omega) n
  have hnum := cltFar_off_numeric (N := ((sz.size n : ℕ) : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
    (a := 3 / 𝔠) (b := 6 / 𝔠) (cΘ := cΘ) (c₀ := cltFar_c0 d) (κ' := κ) hW1 hWN
    hD.le (by positivity) (by simpa using hQ3) (by simpa using hQ6) hcΘ0 hc0.le hκ hbig
  have := hdet.trans hnum
  linarith [hσa]

end Off

/-! ## 4. Target 5c: the window fluctuation `c_n · flucg` -/

section Fluc

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `BY (w^{d-2} + 1) ≤ N⁹` at one index (`cltFarG_BY_le`, `cltFar_wpow_le`; `2𝔡^{-4}(κ'^{-2} + c_Θ) ≤ N`, `(log W)^{3(d-2)} ≤ N`;
band `cltFar_BYw_le`, `CltFar:1323`). -/
private theorem cltFarG_BYw_le (hd : 3 ≤ d) (n : ℕ) {s t cΘ κ' 𝔡 : ℝ} (σ : Fin 2 → Bool) (hcΘ0 : 0 ≤ cΘ)
    (hκ' : κ' ≤ (C.m n).im) (hκ'0 : 0 < κ') (hst : s ≤ t) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹)
    (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hA1 : 1 ≤ STAI sz n)
    (hK : ∀ a b : Zd d (sz.L n), ‖C.K n s σ ![a, b]‖ ≤ cΘ)
    (hKc : 2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) ≤ ((sz.size n : ℕ) : ℝ))
    (hlwpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ)) :
    CltMom2.BYg C n s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1) ≤
      ((sz.size n : ℕ) : ℝ) ^ 9 := by
  have hN1 := cltFar_one_le_N sz n
  have hBY := cltFarG_BY_le C n σ hcΘ0 hκ' hκ'0 hst hg hgΛ hreg hA1 hK (by omega)
  have hw := cltFar_wpow_le sz n (s := s) hlwpow
  have hBY0 : 0 ≤ CltMom2.BYg C n s σ := by
    unfold CltMom2.BYg
    positivity
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg (cltFar_one_le_W sz n)
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) s := ellT_pos (cltFar_one_le_L sz n)
  have hw0 : 0 ≤ (Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1 := by positivity
  calc CltMom2.BYg C n s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)
      ≤ (𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) * ((sz.size n : ℕ) : ℝ) ^ 6) * (2 * ((sz.size n : ℕ) : ℝ) ^ 2) :=
        mul_le_mul hBY hw hw0 (by positivity)
    _ = (2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ)) * ((sz.size n : ℕ) : ℝ) ^ 8 := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 8 := mul_le_mul_of_nonneg_right hKc (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ 9 := by ring

/-- **The bound of `rhsg/θ^{2p}` at one index** (`(eq:main_challenge3)`, `3_5:2213`; band `cltFar_rhs_bound`, `CltFar:1409`): with
`Λ' = N^{τ/2}`, `q₁ = N^{-D₁}`, `εf = W^{-m₃/𝔠}`, `θ ≥ θ₀ = N^τ ℓ_s⁴/(|a₁-a₂|^{d-2}+1)`, `D + 2 ≤ pτ`, `D₁ ≥ 18p + D + 4`,
`m₃ ≥ 6p + D + 3`: `CltMom2.rhsg/θ^{2p} ≤ N^{-D}`.  The three terms are `N^{-pτ}·K_p(log W)^{24p}`,
`BY^{2p}(w^{d-2}+1)^{2p} |labels| N^{-D₁} ≤ N^{18p+2-D₁}` (`BY (w^{d-2}+1) ≤ N⁹`) and
`W^{-m₃/𝔠}(Σ|Z|·R_a)^{2p} ≤ (4c_Θ²)^{2p} N^{6p-m₃}`. -/
private theorem cltFarG_rhs_bound (hd : 3 ≤ d) (n : ℕ)
    {s t cΘ κ' 𝔠 𝔡 M τ D D₁ θ : ℝ} {p m₃ : ℕ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (hτ : 0 < τ) (hpτ : D + 2 ≤ (p : ℝ) * τ) (hM : 0 < M)
    (hD₁ : 18 * (p : ℝ) + D + 4 ≤ D₁) (hm₃ : 6 * (p : ℝ) + D + 3 ≤ (m₃ : ℝ)) (hcΘ0 : 0 ≤ cΘ)
    (hκ' : κ' ≤ (C.m n).im) (hκ'0 : 0 < κ') (hst : s ≤ t)
    (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ 𝔡⁻¹) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t)
    (hA1 : 1 ≤ STAI sz n) (hT : ∀ x y : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t x y‖ ≤ cΘ / sz.lam n ^ 2)
    (hK : ∀ a b : Zd d (sz.L n), ‖C.K n s σ ![a, b]‖ ≤ cΘ) (h𝔠 : 0 < 𝔠)
    (hBwn : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hN3 : 3 ≤ ((sz.size n : ℕ) : ℝ))
    (hpoly : 4 * cltFarKp d M p * Real.log ((sz.size n : ℕ) : ℝ) ^ (24 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2)
    (hcΘp : (4 * cΘ ^ 2) ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ))
    (hKc : 2 * 𝔡⁻¹ ^ 4 * (1 / κ' ^ 2 + cΘ) ≤ ((sz.size n : ℕ) : ℝ))
    (hlwpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ))
    (hθ : ((sz.size n : ℕ) : ℝ) ^ τ * (ellT (sz.L n) (sz.lam n) s ^ 4 /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ θ) :
    CltMom2.rhsg C n s t σ a p M (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-D₁))
        (((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠))) / θ ^ (2 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 := cltFar_one_le_W sz n
  have hL1 := cltFar_one_le_L sz n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT hL1
  -- the three bounds
  have hLp := cltFar_Lp_le (N := ((sz.size n : ℕ) : ℝ)) (τ := τ) (D := D) (p := p) hN1 hpτ
  have hBYw := cltFarG_BYw_le C hd n σ hcΘ0 hκ' hκ'0 hst hg hgΛ hreg hA1 hK hKc hlwpow
  have hBYw0 : 0 ≤ CltMom2.BYg C n s σ *
      ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1) := by
    have : 0 ≤ CltMom2.BYg C n s σ := by
      unfold CltMom2.BYg
      positivity
    positivity
  have hBq := cltFar_Bq_le (N := ((sz.size n : ℕ) : ℝ)) (D := D) (D₁ := D₁) (p := p) hN1 hBYw0 hBYw
    (Nat.cast_nonneg _) (cltFar_card_pair_le sz n) hD₁
  have hZZ := cltFarG_ZZ_le C n hcΘ0 hg σ hT a (s := s)
  have hSZ0 : 0 ≤ ∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR0 : 0 ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hεf := cltFar_W_rpow_le hN0 h𝔠 hBwn m₃
  have hGq := cltFar_Gq_le (N := ((sz.size n : ℕ) : ℝ)) (D := D) (p := p) (m₃ := m₃) hN1
    hεf hSZ0 hZZ hR0
    (cltFar_R_le sz n _ (st5_zdistInf_le sz n _)) hcΘp hm₃
  have hrhs : CltMom2.rhsg C n s t σ a p M (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-D₁))
        (((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠))) =
      (cltFarKp d M p * Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) *
        ((((sz.size n : ℕ) : ℝ) ^ (τ / 2)) ^ (2 * p) +
          (CltMom2.BYg C n s σ * ((Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s) ^ (d - 2) + 1)) ^ (2 * p) *
            (Fintype.card (Fin 2 → Zd d (sz.L n)) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) *
        (ellT (sz.L n) (sz.lam n) s ^ 4 / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ^ (2 * p) +
      ((sz.W n : ℕ) : ℝ) ^ (-((m₃ : ℝ) / 𝔠)) *
        (∑ β : Fin 2 → Zd d (sz.L n), ‖CltMom2.Zg C n s t σ a β‖) ^ (2 * p) := by
    unfold CltMom2.rhsg cltFarKp
    ring
  rw [hrhs]
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hKL : cltFarKp d M p * Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 / 4 := by
    have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
      Real.log_le_log (by linarith) (cltFar_W_le sz (by omega) n)
    have : Real.log ((sz.W n : ℕ) : ℝ) ^ (24 * p) ≤ Real.log ((sz.size n : ℕ) : ℝ) ^ (24 * p) :=
      pow_le_pow_left₀ hlw0 hlwN _
    have h1 := mul_le_mul_of_nonneg_left this (cltFarKp_nonneg (d := d) (by omega) hM.le p)
    linarith
  have hR1 : 1 ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by
    have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) := by positivity
    linarith
  exact cltFar_assemble hN3 hτ hℓ1 hR1 (cltFarKp_nonneg (by omega) hM.le p) hlw0 hKL (by positivity) hLp
    (by positivity) hBq (Real.rpow_nonneg (by linarith) _) hSZ0 hGq hθ

/-- **Target 5c: the window fluctuation** `c_n · flucg` (`(eq:main_challenge3)`, `3_5:2213-2249`; band `cltFar_fluc`, `CltFar:1505`) at
one index `(σ, a)`: `P(N^τ A^{-6/5}/(|a₁-a₂|^{d-2}+1) < ‖c_n flucg‖) ≤ N^{-D}`, eventually, uniformly in `σ₀ ≠ σ₁` and `a`.
Route: `cltMom2_tail_eventuallyg` (Markov, `2p`-th moment, `STCltIsoConclgL`) at `Λ' = N^{τ/2}`, `q₁ = N^{-D₁}` (`DomHypg` by
`cltFar_domg`), `εf = W^{-m₃/𝔠}`, with `p = ⌈(D+2)/τ⌉`, `D₁ = 18p + ⌈D⌉ + 4`, `m₃ = 6p + ⌈D⌉ + 3`; the event is `{θ < ‖flucg‖}` with
`θ = N^τ g⁴/((1-s)² R_a) ≥ θ₀ = N^τ ℓ_s⁴/R_a` (`1 - s ≤ g²`, `cltFar_theta_ge`), and `cltFarG_rhs_bound` bounds `rhsg/θ^{2p} ≤ N^{-D}`. -/
theorem cltFar_flucg {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1)
    (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd)
    (hTh : STThPropsg C) (hKp : STKpropsg C s) (hiso : STCltIsoConclgL C μ s) (τ D : ℝ) (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
            (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
          ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
            CltMom2.flucg C μ n (s n) (t n) σ a ω‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hAdm' : sz.Admissible 𝔠 𝔡 := ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨M, hM, HT⟩ := cltMom2_tail_eventuallyg C μ hd hκ hrep hTh hiso t
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  -- the exponents
  obtain ⟨p, hpdef⟩ : ∃ p : ℕ, p = ⌈(D + 2) / τ⌉₊ := ⟨_, rfl⟩
  have hp1 : 1 ≤ p := by
    rw [hpdef]
    exact Nat.ceil_pos.2 (by positivity)
  have hpτ : D + 2 ≤ (p : ℝ) * τ := by
    have h1 : (D + 2) / τ ≤ (p : ℝ) := by rw [hpdef]; exact Nat.le_ceil _
    calc D + 2 = (D + 2) / τ * τ := by field_simp
      _ ≤ (p : ℝ) * τ := mul_le_mul_of_nonneg_right h1 hτ.le
  obtain ⟨m₃, hm₃def⟩ : ∃ m₃ : ℕ, m₃ = 6 * p + ⌈D⌉₊ + 3 := ⟨_, rfl⟩
  have hm₃ : 6 * (p : ℝ) + D + 3 ≤ (m₃ : ℝ) := by
    have := Nat.le_ceil D
    rw [hm₃def]; push_cast; linarith
  obtain ⟨m₁, hm₁def⟩ : ∃ m₁ : ℕ, m₁ = 18 * p + ⌈D⌉₊ + 4 := ⟨_, rfl⟩
  have hD₁ : 18 * (p : ℝ) + D + 4 ≤ (m₁ : ℝ) := by
    have := Nat.le_ceil D
    rw [hm₁def]; push_cast; linarith
  have hD₁0 : (0 : ℝ) < (m₁ : ℝ) := by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg _]
  have hm₃0 : (0 : ℝ) < (m₃ : ℝ) := by linarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg _]
  have hD'0 : (0 : ℝ) < (m₃ : ℝ) / 𝔠 := by positivity
  -- the eventual inputs
  have hdom := cltFar_domg C μ hd hAdm' hs1 hst' hreg hG (τ := τ / 2) (D₁ := (m₁ : ℝ)) (half_pos hτ) hD₁0
  have hisoN := HT p hp1 ((m₃ : ℝ) / 𝔠) hD'0
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  obtain ⟨cΘ, hcΘ0, hin⟩ := cltFarG_inputs C hd hs0 hst' hreg hev hTh hKp
  have hpure : ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 4 * cltFarKp d M p * Real.log x ^ (24 * p) ≤ x ^ 2 ∧
      (4 * cΘ ^ 2) ^ (2 * p) ≤ x ∧
      2 * 𝔡⁻¹ ^ 4 * (1 / κ ^ 2 + cΘ) ≤ x ∧
      Real.log x ^ (3 * (d - 2)) ≤ x ∧ (40 : ℝ) ≤ 𝔠 * Real.log x ∧ 2 * (d : ℝ) ≤ 𝔠 * Real.log x := by
    have h1 := cltFar_polylog (4 * cltFarKp d M p) 2 two_pos (24 * p)
    have h2 := cltFar_polylog 1 1 one_pos (3 * (d - 2))
    have h3 : ∀ᶠ x : ℝ in atTop, (40 : ℝ) ≤ 𝔠 * Real.log x :=
      (Filter.Tendsto.const_mul_atTop h𝔠 Real.tendsto_log_atTop).eventually_ge_atTop 40
    have h4 : ∀ᶠ x : ℝ in atTop, 2 * (d : ℝ) ≤ 𝔠 * Real.log x :=
      (Filter.Tendsto.const_mul_atTop h𝔠 Real.tendsto_log_atTop).eventually_ge_atTop _
    filter_upwards [eventually_ge_atTop (3 : ℝ), h1, eventually_ge_atTop ((4 * cΘ ^ 2) ^ (2 * p)),
      eventually_ge_atTop (2 * 𝔡⁻¹ ^ 4 * (1 / κ ^ 2 + cΘ)), h2, h3, h4]
      with x a b c e f g h
    refine ⟨a, ?_, c, e, ?_, g, h⟩
    · simpa [Real.rpow_two] using b
    · simpa [Real.rpow_one] using f
  filter_upwards [hdom, hisoN, hin, hBw, hWO, hSz.eventually hpure] with n hdomn hisoNn hinn hBwn hWOn hpn
  obtain ⟨hg, hA1, hTn, hKn⟩ := hinn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hN3, hpoly, hcΘp, hKc, hlwpow, h40', h2d'⟩ := hpn
  intro σ hσ a
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hlw𝔠 : 𝔠 * Real.log ((sz.size n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hN0 𝔠) hBwn
    rwa [Real.log_rpow hN0] at this
  have h40 : (40 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := h40'.trans hlw𝔠
  have h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := h2d'.trans hlw𝔠
  have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg (cltFar_one_le_W sz n)
  have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
    Real.log_le_log (by linarith [cltFar_one_le_W sz n]) (cltFar_W_le sz (by omega) n)
  have hlwpow' : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 * (d - 2)) ≤ ((sz.size n : ℕ) : ℝ) :=
    (pow_le_pow_left₀ hlw0 hlwN _).trans hlwpow
  have hs1n := hs1 n
  have hv : 0 < 1 - s n := sub_pos.2 hs1n
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (s n) := one_le_ellT (cltFar_one_le_L sz n)
  have hRpos : 0 < ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hA65 : 0 < STAI sz n ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos hA0 _
  -- `θ`
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = ((sz.size n : ℕ) : ℝ) ^ τ *
      (sz.lam n ^ 4 / ((1 - s n) ^ 2 * (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1))) := ⟨_, rfl⟩
  have hθ₀ : ((sz.size n : ℕ) : ℝ) ^ τ * (ellT (sz.L n) (sz.lam n) (s n) ^ 4 /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) ≤ θ := by
    rw [hθdef]
    exact cltFar_theta_ge (Real.rpow_nonneg hN0.le _) hRpos hs1n (cltFar_ell_sq hg hs1n (hreg n).2)
  have hθpos : 0 < θ := by
    rw [hθdef]
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_pos_of_pos hN0 _
    positivity
  -- the event
  have hcn : 0 < (1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) := by
    have : 0 < (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) := hA65
    positivity
  have hθeq : ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) /
      ((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ))) = θ := by
    rw [hθdef, Real.rpow_neg hA0.le]
    exact cltFar_theta_eq hA65 hRpos hg hs1n
  have hset : {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.flucg C μ n (s n) (t n) σ a ω‖} =
      {ω | θ < ‖CltMom2.flucg C μ n (s n) (t n) σ a ω‖} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcn.le, ← div_lt_iff₀' hcn, hθeq]
  rw [hset]
  have hmom := hisoNn σ hσ a (((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (((sz.size n : ℕ) : ℝ) ^ (-(m₁ : ℝ))) θ (hm n) hg hs1n
    ((hs0 n).trans (hst n).le) (ht n) (hreg n).1 h40 h2d (Real.rpow_nonneg hN0.le _) (hdomn σ) hθpos
  refine hmom.trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact cltFarG_rhs_bound C hd n σ a hτ hpτ hM hD₁ hm₃ hcΘ0 (hm n) hκ (hst n).le hg hgΛ (hreg n).1 hA1 (hTn σ hσ) (hKn σ hσ)
    h𝔠 hBwn hN3 hpoly hcΘp hKc hlwpow' hθ₀

end Fluc

/-! ## 5. Target 6: the pin `STCltFargL` -/

section Far

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **The deterministic splitting of the far part** (`3_5:2182-2186`; band `cltFar_far_le`, `CltFar:1691`): `f = 𝔼 f + c_n fluc + off`
(`cltMom2_decompg`), so `|f| ≤ |𝔼 f| + |c_n fluc| + |off| ≤ (2 N^{τ/2} + 1) ζ ≤ N^τ ζ` for `N^{τ/2} ≥ 3`, `|off| ≤ W^{-D₀} ≤ ζ`. -/
private theorem cltFarG_far_le [IsProbabilityMeasure μ] (n : ℕ) {s t : ℝ} (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) (hL : cltMom2G_LEnv C n s) (hg : 0 < sz.lam n) {Nh ζ Woff : ℝ}
    (hmean : ‖∫ ω', STfFarg C n s t σ a ω' ∂μ‖ ≤ Nh * ζ)
    (hfl : ‖(((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
      CltMom2.flucg C μ n s t σ a ω‖ ≤ Nh * ζ)
    (hoff : ‖CltMom2.offg C μ n s t σ a ω‖ ≤ Woff) (hWζ : Woff ≤ ζ) (hζ0 : 0 ≤ ζ) (hNh : 3 ≤ Nh) :
    ‖STfFarg C n s t σ a ω‖ ≤ Nh * Nh * ζ := by
  have hdec := cltMom2_decompg C μ n s t hL hg σ a ω
  have h1 : ‖STfFarg C n s t σ a ω‖ ≤
      ‖STfFarg C n s t σ a ω - ∫ ω', STfFarg C n s t σ a ω' ∂μ‖ + ‖∫ ω', STfFarg C n s t σ a ω' ∂μ‖ := by
    calc ‖STfFarg C n s t σ a ω‖
        = ‖(STfFarg C n s t σ a ω - ∫ ω', STfFarg C n s t σ a ω' ∂μ) + ∫ ω', STfFarg C n s t σ a ω' ∂μ‖ := by
          rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hdec] at h1
  have h2 := norm_add_le
    ((((1 - s) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
      CltMom2.flucg C μ n s t σ a ω) (CltMom2.offg C μ n s t σ a ω)
  have h3 : 2 * Nh * ζ + ζ ≤ Nh * Nh * ζ := by
    nlinarith [mul_nonneg hζ0 (mul_nonneg (sub_nonneg.2 hNh) (by linarith : (0 : ℝ) ≤ Nh + 1))]
  linarith

/-- **`lem;CLT`, far part, over the carrier** (target 6; `3_5:2173-2176`, proof `3_5:2182-2249`; band `stCltFar_holds`, `CltFar:1757`):
the merged pin `STCltFargL d` (`Chain/CltGen`) for every `d`.  `f = 𝔼 f + c_n fluc + off` (`cltMom2_decompg`): the mean part is
`meanFar_eventuallyg` at `τ/2`, the window fluctuation is `cltFar_flucg` at `(τ/2, D+3)` for one `(σ, a)` (`STCltIsoConclgL` is
`stCltIsogL_holds` on the same `HCltOf`), the off-window part is `cltFar_offg` at `(6d/5 + (d-2)/𝔠 + 1, D+1)` for every `(σ, a)` at
once; the union over the index set is the explicit finite union over `{σ // σ 0 ≠ σ 1} × (Fin 2 → Z_L^d)` (`≤ 4N²` elements)
inside `PrecL`. -/
theorem stCltFargL_holds (d : ℕ) : STCltFargL d := by
  intro κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t hH hreg hTh hKp hX
  have hiso : STCltIsoConclgL C μ s := stCltIsogL_holds d κ δ 𝔠 𝔡 Cd sz C μ g' E H₀ s t hH
  obtain ⟨hd, hκ, -, -, hAdm, hm, hs0, hst, ht1, -, hrep, -, -, -, hG, -, -⟩ := hH
  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  have hAdm' : sz.Admissible 𝔠 𝔡 := ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht1 n)
  intro τ hτ D hD
  have hD₀ : (0 : ℝ) < 6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1 := by
    have h3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have h1 : 0 ≤ ((d : ℝ) - 2) / 𝔠 := div_nonneg (by linarith) h𝔠.le
    linarith
  have hmean := meanFar_eventuallyg C μ hd hκ hAdm' hm s t hs0 hst ht1 hrep hreg hG hTh hKp hX (τ / 2) (half_pos hτ)
  have hoff := cltFar_offg C μ hd hκ hAdm' hm s t hs0 hst ht1 hrep hreg hG hTh hKp
    (6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1) (D + 1) hD₀ (by linarith)
  have hfluc := cltFar_flucg C μ hd hκ hAdm' hm s t hs0 hst ht1 hrep hreg hG hTh hKp hiso (τ / 2) (D + 3)
    (half_pos hτ) (by linarith)
  have hev := st5_eventually_A_ge_one sz h𝔡 hWO
  have hpure : ∀ᶠ x : ℝ in atTop, 5 ≤ x ∧ 3 ≤ x ^ (τ / 2) := by
    have h1 : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ (τ / 2) :=
      (tendsto_rpow_atTop (half_pos hτ)).eventually_ge_atTop 3
    filter_upwards [eventually_ge_atTop (5 : ℝ), h1] with x a b
    exact ⟨a, b⟩
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hSz)
  filter_upwards [hmean, hoff, hfluc, hev, hBw, hWO, hSz.eventually hpure,
    hWt.eventually_ge_atTop (2 * ((𝔡⁻¹ ^ 2) ^ (6 / 5 : ℝ)))] with n hmn hon hfn hAn hBwn hWOn hpn hbig
  obtain ⟨hg, hA1⟩ := hAn
  obtain ⟨-, hgΛ⟩ := hWOn
  obtain ⟨hN5, hNh⟩ := hpn
  have hN1 := cltFar_one_le_N sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hL := cltMom2G_lenv_of_rep C μ hrep hκ n (hm n) (hs1 n)
  change μ (badSetAt sz.size _ _ τ n) ≤ _
  refine (cltFar_union_bound μ _
    {ω | ∃ (σ : Fin 2 → Bool), σ 0 ≠ σ 1 ∧ ∃ a : Fin 2 → Zd d (sz.L n),
      ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) < ‖CltMom2.offg C μ n (s n) (t n) σ a ω‖}
    (fun q : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) =>
      {ω | ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
          CltMom2.flucg C μ n (s n) (t n) q.1.1 q.2 ω‖})
    (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hN0.le _) ?_ hon (fun q => hfn q.1.1 q.1.2 q.2)).trans ?_
  · -- the bad event is covered
    intro ω hω
    obtain ⟨u, hu⟩ := hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have hoff' : ∀ (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)),
        ‖CltMom2.offg C μ n (s n) (t n) σ a ω‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (-(6 * (d : ℝ) / 5 + ((d : ℝ) - 2) / 𝔠 + 1)) := by
      intro σ hσ a
      by_contra h
      exact hc1 ⟨σ, hσ, a, not_le.1 h⟩
    have hfl' : ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) *
        CltMom2.flucg C μ n (s n) (t n) u.1.1.1 u.1.2 ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (STAI sz n ^ (-(6 / 5 : ℝ)) /
          (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
      by_contra h
      exact hc2 (Set.mem_iUnion.2 ⟨(u.1.1, u.1.2), not_le.1 h⟩)
    have hr : zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) ≤ sz.L n := st5_zdistInf_le sz n _
    have hζ := cltFar_zeta_ge hd sz n h𝔠 h𝔡 hA1 hg hgΛ hBwn _ hr hbig
    have hζ0 : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1) := by
      have : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg hA0.le _
      positivity
    have hfar := cltFarG_far_le C μ n u.1.1.1 u.1.2 ω hL hg (hmn u.1.1.1 u.1.1.2 u.1.2) hfl'
      (hoff' u.1.1.1 u.1.1.2 u.1.2) hζ hζ0 hNh
    have hNN : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    rw [hNN] at hfar
    have hu' : ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) /
        (((zdistInf d (sz.L n) (u.1.2 0 - u.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1)) <
        ‖STfFarg C n (s n) (t n) u.1.1.1 u.1.2 ω‖ := hu
    linarith
  · -- the numerics
    apply ENNReal.ofReal_le_ofReal
    refine cltFar_union_numeric hN5 ?_
    have h1 : Fintype.card ({σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) =
        Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} * Fintype.card (Fin 2 → Zd d (sz.L n)) :=
      Fintype.card_prod _ _
    have h2 : Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} ≤ 4 := by
      have h := Fintype.card_subtype_le (fun σ : Fin 2 → Bool => σ 0 ≠ σ 1)
      have h' : Fintype.card (Fin 2 → Bool) = 4 := by simp
      omega
    rw [h1]
    push_cast
    have h3 := cltFar_card_pair_le sz n
    have h4 : ((Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h2
    calc ((Fintype.card {σ : Fin 2 → Bool // σ 0 ≠ σ 1} : ℕ) : ℝ) * ((Fintype.card (Fin 2 → Zd d (sz.L n)) : ℕ) : ℝ)
        ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := mul_le_mul h4 h3 (Nat.cast_nonneg _) (by norm_num)

end Far

/-! ## 6. The band: the producers of `STThPropsg`, `STKpropsg` (target 7) and the band bridge (target 8) -/

/-! ## 7. Compiled nonempty instances (`d = 3`, band data of `Step5Inst`: `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`)

`szCL` is the merged sequence of `RBM.Gauss.Step5Inst` (`d = 3`, `L_n = 2 (n+24)^5`, `W_n = 2^{n+24}`, `lam ≡ 1`, `s ≡ 0`,
`1 - t_n = L_n^{-2}`, `E_n = lemE z_n`, `κ = 1/2`, `𝔠 = 1/6`, `𝔡 = 1/10`, `Cd = 1`).  Every deterministic hypothesis is discharged:
the admissibility, `κ ≤ Im m`, `0 ≤ sCL < tCL < 1`, `CltRepg` (`cltRepg_band`), `STReg5I` (`szCL_reg5I`), `STExpInvgL`
(`stExpInvgL_band`), `STThPropsg`, `STKpropsg` (targets 7a, 7b), `HCltOf` (`cltGood_hCltOf_szCL`) and `STCltIsoConclgL`
(`stCltIsogL_holds`).  The only hypotheses of the examples are the Step 2 pins `STLocalEntryUgL`, `STGdecayWgL` (another gate).  The index
set of `STCltFarConclgL` is nonempty at every `n` (`szCL_cltFar_index_nonempty`). -/

end RBM.BA

end
