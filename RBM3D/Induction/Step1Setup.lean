/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.PerTimeCalc
import RBM3D.Induction.ConArg
import RBM3D.Induction.ContinuityNet
import RBM3D.Green.Pins

/-!
# Step 1 of `lem:main_ind`, first part: elementary facts, scales, per-time lemmas, loops, bridge
(ST-1, S1-35)

Ticket T2079.  Port of `RBM2D/Induction/Step1.lean` at `c9a24cf` up to `end Bridge` (lines 1-965,
cited `Step1:line`) to `arXiv:2507.20274`: Step 1 of `lem:main_ind`, (`lRB1`) `1_2:1321` and
(`Gtmwc`) `1_2:1327` (the merged `STStep1Loop`, `STStep1Weak`), `3_5:64-66`.

## The cut

S1-35 (this file) is `Step1:1-965`: `Step1TargetV3` (`:84`), sections `Elementary` (`:90`),
`Scales` (`:211`), `Generic` (`:462`), `Loops` (`:508`), `Bridge` (`:729`-`:965`).  S1-36 is
`Step1:967-1515`: `WeakLawSeq` (`s1x`, `s1a`, `s1f`, `s1_card_block*` `:983-1000`, `s1_card_loops`,
`s1_wl_seq`), `Net` (`s1Net`, `s1_forb`), `Bootstrap` (`s1_boot`, `s1_weakPT`, `s1_loopPT`),
`step1` (`:1378`), `Checks`.

## Declarations of `Step1:1-965` (RBM2D line) and what became of them

* `Step1TargetV3` `:84` -> `Step1TargetV3 d := STGbEXPii d → STGbEXPij d → STStep1 d`: both
  conjuncts `STStep1Loop`, `STStep1Weak` of the merged pin `STStep1`.
* `Elementary`: `s1_bulk` `:94` (alias of `ContinuityNet.cont_bulk`), `s1_im_le_one` `:107`
  (dropped), `s1_inv_rpow` `:112`, `s1_mul_rpow_le` `:116` (private), `s1_size_eq` `:122`
  (`size = (WL)^d`), `s1_one_le_L` `:125`, `s1_one_le_W` `:128`, `s1_one_le_size` `:130`,
  `s1_W_sq_le_size` `:135` -> `s1_W_pow_le_size` (`W^d ≤ N`), `s1_hsize` `:141`,
  `s1_scaleM_le_W2` `:145` (**deleted**: `M_u = W² ℓ² η` has no `d ≥ 3` reading; its uses become
  `STBctl_ge` (`s1_Wd_le_Bctl`, `s1_F8`, `s1_loop_det`) and `cont_inv_size_le_Bctl` (`s1_F6`)),
  `s1_ratio_pt` `:159` (`a_s (1-s)/(1-u) ≤ a_s^{1-𝔠_d}`); new: `s1_d_pos`.
* `Scales`: `S1Std` `:214` (**new fields `hWO`, `h𝔠d`, `h𝔠d'`**), `s1_std_of_mainIndHyp` `:229` ->
  `s1_std_of_stFlow`, `s1_Ms_ge` `:233` -> `s1_a_le`, `s1_Ms_tendsto` `:242` -> `s1_B_tendsto`,
  `s1_Ms_pos`, `s1_Mu_pos` `:254`, `:259` -> `s1_B_pos`, `s1_Bu_pos`, `s1_Ms_ev_pow` `:264` ->
  `s1_B_ev_pow`, `s1_one_le_Ms` `:268` -> `s1_B_le_one`, `s1_ratio_ev` `:273`, `s1Ms` `:282` ->
  `s1B`, `s1_Npow_le` `:285` -> `s1_apow_le`, `s1_c1_pos` `:293`, `s1_c0_pos` `:296`,
  `s1_F3` `:300`, `s1_F4` `:329`, `s1_F5` `:382`, `s1_F6` `:418`, `s1_F7` `:439`, `s1_F8` `:445`.
* `Generic`: `s1_pt_of_le` `:467` (private), `s1_highProb_of_pt` `:481`, `s1_pt_of_highProb`
  `:488`, `s1_stochDom_unit` `:499`; new (private): `s1_pt_of_ev_or`.
* `Loops`: `s1T1` `:513`, `s1_blockMat_herm` `:515` (private), `s1_ellT_nonneg` `:519` (dropped: no
  `ℓ` in the `d ≥ 3` controls), `s1_loop_det` `:525`, `s1_Kbound_seq` `:550`, `S1H55` `:570`,
  `s1_h55` `:581`, `s1_LI` `:641`.
* `Bridge`: `s1_green_blockMat`, `s1_greenBlk_apply`, `s1_diagSq_eq`, `s1_offSq_eq`,
  `s1_norm_loopPM` `:735-766` (dropped: the merged `Green.diagSq`, `offSq`, `loopPM` are on the fine
  lattice `Idx d L W`, and `STGiiGEX`, `STGijGEX` are on the sample, so the entries of `Gt`,
  `STGM` are read directly), `s1_zdist_le_one` `:774` (private), `s1_mem_sbSupport` `:794`
  (dropped: `sbSupport` is the `d = 2` five-point profile), `s1_near_card` `:810`, `s1_gexRHS_le`
  `:823`, `s1xM` `:858`, `s1xM_ge`, `s1xM_le`, `s1xM_nonneg` `:862-871`, `s1_gMax_le` `:877`,
  `s1xM_le_add` `:892`, `s1_wl_det` `:918`; new: `s1_llErrMat_eq`, `s1_STGM_norm`,
  `s1_omegaC_eq_one`, `s1_indMax_eq_one` (the merged sample-level indicators `STomegaC`,
  `STindMax` read at `s1xM`).
* DECISIONS §26: `StochDomAt.of_subset_whp`, `StochDomAt.of_subset_compl` (probe `752e027`
  `:907`, `:926`), absent from `Defs/StochDomAt.lean`, are proved in section 0.

## Dimension-dependent statements (ST1-COMMON item 2)

`W²` -> `W^d`, `(WL)²` -> `(WL)^d = N`, `Z2 L` -> `Zd d L`; `M_s⁻¹` -> `a_s := sz.Bctl n s =
W^{-d} B_{s,0}` (merged `ScaleFacts.lean:12-34`); `(ℓ_u/ℓ_s)² M_u⁻¹` -> `(1-s)/(1-u) · a_s`; the
exponent `30` of `CondStInd` -> the parameter `𝔠_d` of `STConStInd`.  Constants:
`6 -> 2·3^d ≥ √(2·9^d + 1)` (F4), `25 → 2·9^d` and `26 → 2·9^d + 1` (`s1_gexRHS_le`,
`s1_wl_det`: `STgexRHS` sums the two orientations `σ ∈ {(+,-),(-,+)}`, and the `zdistInf` ball
of radius `1` has `≤ 3^d` blocks).  The ticket's `2d + 1` is the `zdistD` ball and is not used.

## Map `S1Std`/`MainIndHyp` -> merged hypotheses (`STFlow sz κ ε 𝔠 𝔡 z`, `E = STflowE z`)

`hκ`, `hc`, `h𝔡` <- the pin arguments and `Admissible.1`; `hE` <- `lemma28_quant`;
`hN` <- `Admissible.2.2.1`; `hB` <- `.2.2.2.1`; `hWO` <- `.2.2.2.2` (new); `hτ`, `hR` <-
`Green.v3_premises_of_stFlow` (`τ = ε/2`); `hs0`, `hst`, `ht1` <- the pin (`t ≤ lemT z < 1`);
`hCond` <- `STConStInd 𝔠_d s t`; `InitLK` <- `STLK s`; `InitLocal` <- `STLocalMax s`;
`KboundConcl κ` <- `STKbound`; `InitDecay` unused; `GbEXPHypV3 d (κ/2) c τ` <- `STGbEXPii d`,
`STGbEXPij d` (`STGbEXPav` unused).

## Time windows (DECISIONS §29)

`0 ≤ s` is used exactly in `STBctl_ge` (`s1_Wd_le_Bctl`, `s1_F8`, the `u < 1/2` branches of
`s1_h55`, `s1_LI`) and `cont_inv_size_le_Bctl` (`s1_F6`); `s1_ratio_pt` and the `u ≥ 1/2` branch of
`s1_LI` use only `s ≤ u ≤ t < 1`.  The facts that need `lam ≤ 𝔡⁻¹` or `a_s → 0` are `∀ᶠ n`; the
pointwise facts are `∀ n`.  No statement here contains `ℓ` or uses `L^d ≤ W^K`.  The constants
depend on `κ, 𝔡, d, k` only.  Section 7 holds the compiled instances at `d = 3` and the
counterexample to dropping `0 ≤ s`.
-/

set_option linter.style.longLine false

noncomputable section

/-! ## 0. Two `≺`-calculus lemmas of the T2015 probe (DECISIONS §26; probe `752e027`, §4.0) -/

namespace RBM.StochDomAt

open MeasureTheory Filter RBM RBM.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- A failure event eventually contained in a failure event or the complement of a `w.h.p.`
event.  Probe `752e027:RBM3D/Probe/T2015Pins.lean:907` (`StochDomAt.of_subset_whp`). -/
theorem of_subset_whp (hsize : Tendsto size atTop atTop) {U₁ : ℕ → Type*}
    {ξ ζ : ∀ l, U l → Ω → ℝ} {f g : ∀ l, U₁ l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (h : StochDomAt P size f g) (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size f g τ' l ∪ (Ξ l)ᶜ) : StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' (D + 1) (by linarith), hΞ (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with l h0 h1 h2 h3
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc P (badSetAt size ξ ζ τ l) ≤ P (badSetAt size f g τ' l ∪ (Ξ l)ᶜ) := measure_mono h0
    _ ≤ P (badSetAt size f g τ' l) + P (Ξ l)ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- A failure event eventually contained in the complement of a `w.h.p.` event.  Probe
`752e027:RBM3D/Probe/T2015Pins.lean:926` (`StochDomAt.of_subset_compl`). -/
theorem of_subset_compl {ξ ζ : ∀ l, U l → Ω → ℝ} {Ξ : ℕ → Set Ω}
    (hΞ : HighProbAt P size Ξ)
    (hsub : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, badSetAt size ξ ζ τ l ⊆ (Ξ l)ᶜ) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [hsub τ hτ, hΞ D hD] with l h1 h2
  exact (measure_mono h1).trans h2

end RBM.StochDomAt

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The pin `Step1TargetV3` -/

/-- **Successor of RBM2D's `Step1TargetV3`** (`Step1:84`, `GbEXPHypV3 d (κ/2) c τ` with
`MainIndHyp`) in its `d`-dimensional form: Step 1 of `lem:main_ind` (`1_2:1317-1328`, `3_5:64-66`)
is the merged pin `STStep1 d` (the hypotheses `STKbound`, `STLK s`, `STLocalMax s`, `STConStInd` and
the flow are `STStep1`'s own, they play the roles of `KboundConcl`, `InitLK`, `InitLocal`,
`CondStInd`, `MainIndHyp`), under the two parts `STGbEXPii`, `STGbEXPij` of `lem_GbEXP`
(`3_5:21`, `3_5:24`) that RBM2D's `GbEXPHypV3` carries.  It covers **both** conjuncts
`STStep1Loop` and `STStep1Weak` of `STStep1`; S1-36 proves it. -/
def Step1TargetV3 (d : ℕ) : Prop :=
  STGbEXPii d → STGbEXPij d → STStep1 d

/-- `Step1TargetV3 d` is `STStep1 d` under the two `lem_GbEXP` parts. -/
theorem stStep1_of_target {d : ℕ} (h : Step1TargetV3 d) (hii : STGbEXPii d) (hij : STGbEXPij d) :
    STStep1 d := h hii hij

/-! ## 2. Elementary facts -/

section Elementary

variable {d : ℕ} (sz : Sizes d)

/-- Bulk energy: `|E| < 2` and `√(2κ)/2 ≤ Im m` for `|E| ≤ 2 - κ` (`Step1:94`; the merged
`ContinuityNet.cont_bulk`, `spectralM` is `mE`). -/
theorem s1_bulk {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    |E| < 2 ∧ Real.sqrt (2 * κ) / 2 ≤ (mE E).im :=
  ContinuityNet.cont_bulk hκ hE

/-- `x⁻¹ ^ p = x ^ (-p)` for `x ≥ 0` (`Step1:112`). -/
theorem s1_inv_rpow {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : x⁻¹ ^ p = x ^ (-p) := by
  rw [Real.rpow_neg hx, Real.inv_rpow hx]

/-- `K x^p ≤ x^q` from `K ≤ x^{q-p}` (`Step1:116`). -/
private theorem s1_mul_rpow_le {x K p q : ℝ} (hx : 0 < x) (h : K ≤ x ^ (q - p)) :
    K * x ^ p ≤ x ^ q := by
  have e : x ^ q = x ^ (q - p) * x ^ p := by rw [← Real.rpow_add hx]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hx.le _)

/-- `N = (W L)^d` (`Step1:122`, `s1_size_eq`: `size = (WL)^d`). -/
theorem s1_size_eq (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) = (((sz.W n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ)) ^ d := by
  simp [Sizes.size]

theorem s1_one_le_L (n : ℕ) : 1 ≤ sz.L n := by
  have := sz.three_le_L n; omega

theorem s1_one_le_W (n : ℕ) : 1 ≤ sz.W n := sz.W_pos n

theorem s1_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n

/-- `W^d ≤ N` (`Step1:135`, `W² ≤ N` at `d = 2`). -/
theorem s1_W_pow_le_size (n : ℕ) : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  rw [s1_size_eq, mul_pow]
  have h1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast s1_one_le_L sz n
  have h2 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ h1
  nlinarith [pow_nonneg (Nat.cast_nonneg (sz.W n) : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ)) d]

theorem s1_hsize (h : sz.SizeTendsto) : Tendsto sz.size atTop atTop :=
  tendsto_natCast_atTop_iff.mp h

/-- `N → ∞` forces `d ≥ 1` (for `d = 0` the scale `N = (WL)^0 = 1` is constant). -/
theorem s1_d_pos (h : sz.SizeTendsto) : 0 < d := by
  by_contra hd
  have hd0 : d = 0 := by omega
  obtain ⟨n, hn⟩ := (h.eventually_ge_atTop 2).exists
  subst hd0
  have : ((sz.size n : ℕ) : ℝ) = 1 := by simp [Sizes.size]
  linarith

/-- The deterministic ratio fact behind Step 1 (`Step1:159`, `ℓ_u ℓ_s^{-1} ≤ M_s^{1/60}`;
`(ℓ_u/ℓ_s)² M_u⁻¹ ≤ M_s^{-14/15}`), `d ≥ 3` form: with `a_s = W^{-d}B_{s,0}`, from
`(con_st_ind)` `a_t^c ≤ (1-t)/(1-s)` (`c = 𝔠_d`, `1_2:1296`) and `s ≤ u ≤ t < 1`,
`a_s (1-s)/(1-u) ≤ a_s^{1-c}`.  No `0 ≤ s` is needed.  (The exponent `30` of RBM2D is `1/c`.) -/
theorem s1_ratio_pt (n : ℕ) {c s u t : ℝ} (hc : 0 < c) (hsu : s ≤ u) (hut : u ≤ t) (ht : t < 1)
    (hstep : (sz.Bctl n t) ^ c ≤ (1 - t) / (1 - s)) :
    sz.Bctl n s * ((1 - s) / (1 - u)) ≤ (sz.Bctl n s) ^ (1 - c) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu1
  have hxt : 0 < 1 - t := by linarith
  have hxs : 0 < 1 - s := by linarith
  have has : 0 < sz.Bctl n s := sz.STBctl_pos n hs1
  have hat : sz.Bctl n s ≤ sz.Bctl n t := sz.STBctl_mono n (hsu.trans hut) ht
  have h1 : (1 - t) ≤ (1 - u) := by linarith
  exact closure_scale hc has hat hxt hxs h1 hstep

end Elementary

/-! ## 3. The standing hypotheses and the scale facts along the window -/

section Scales

/-- The deterministic hypotheses of `STStep1` that Step 1 uses (RBM2D `S1Std`, `Step1:214`: all of
`MainIndHyp` but the three initial-data clauses): `κ` bulk, `𝔠` bandwidth, `𝔡` window
(`(eq:WO)`, a **new field** at `d ≥ 3`: `ilambda` is a sequence), `τ` the range exponent
(`1 - t ≥ N^{-1+τ}`), `𝔠_d ∈ (0, 10^{-2}]` the constant of `(con_st_ind)`.  Public: S1-36 uses it. -/
structure S1Std {d : ℕ} (sz : Sizes d) (κ 𝔠 𝔡 τ 𝔠d : ℝ) (E s t : ℕ → ℝ) : Prop where
  hκ : 0 < κ
  hE : ∀ n, |E n| ≤ 2 - κ
  hc : 0 < 𝔠
  h𝔡 : 0 < 𝔡
  hτ : 0 < τ
  h𝔠d : 0 < 𝔠d
  h𝔠d' : 𝔠d ≤ 1 / 100
  hs0 : ∀ n, 0 ≤ s n
  hst : ∀ n, s n ≤ t n
  ht1 : ∀ n, t n < 1
  hN : sz.SizeTendsto
  hB : sz.Bandwidth 𝔠
  hWO : sz.WO 𝔡
  hCond : sz.STConStInd 𝔠d s t
  hR : sz.RangeCond τ t

variable {d : ℕ} {sz : Sizes d} {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}

/-- `S1Std` from the merged flow hypotheses (`Step1:229` `s1_std_of_mainIndHyp`): `STFlow`,
`0 ≤ s ≤ t ≤ lemT z`, `STConStInd 𝔠_d s t`; `τ = ε/2` (`Green.v3_premises_of_stFlow`),
`E = STflowE z`. -/
theorem s1_std_of_stFlow {ε : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔠d : 0 < 𝔠d)
    (h𝔠d' : 𝔠d ≤ 1 / 100) (hflow : STFlow sz κ ε 𝔠 𝔡 z) (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hC : sz.STConStInd 𝔠d s t) : S1Std sz κ 𝔠 𝔡 (ε / 2) 𝔠d (STflowE z) s t := by
  obtain ⟨hA, -, ht1, hR⟩ := Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hz0 : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (sz.STsize_pos n) _) (hflow.2 n).2.1
  exact ⟨hκ, fun n => (lemma28_quant hκ (hz0 n) (hflow.2 n).2.2 (hflow.2 n).1).1, hA.1, hA.2.1,
    half_pos hε, h𝔠d, h𝔠d', hs0, hst, ht1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, hC, hR⟩

/-- `c₀ = min(2𝔠𝔡, τ) > 0`. -/
theorem s1_c0_pos (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : 0 < min (2 * 𝔠 * 𝔡) τ :=
  lt_min (by have := h.hc; have := h.h𝔡; positivity) h.hτ

/-- `s_n < 1`. -/
theorem s1_s_lt_one (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (n : ℕ) : s n < 1 :=
  lt_of_le_of_lt (h.hst n) (h.ht1 n)

/-- `a_s = W^{-d} B_{s,0} > 0`. -/
theorem s1_B_pos (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (n : ℕ) : 0 < sz.Bctl n (s n) :=
  sz.STBctl_pos n (s1_s_lt_one h n)

/-- `a_u > 0` for `u ≤ t n`. -/
theorem s1_Bu_pos (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (n : ℕ) {u : ℝ} (hu : u ≤ t n) :
    0 < sz.Bctl n u :=
  sz.STBctl_pos n (lt_of_le_of_lt hu (h.ht1 n))

/-- `a_u ≤ 2 N^{-c₀}` for `u ≤ t n`, eventually (RBM2D `s1_Ms_ge`, `Step1:233`,
`M_u ≥ Im m N^{c₀}`; merged `scaleFacts_R1`, needs `(eq:WO)`). -/
theorem s1_a_le (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n →
      sz.Bctl n u ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔠 * 𝔡) τ)) :=
  scaleFacts_R1 sz 𝔠 𝔡 τ t h.h𝔡 h.hB h.hWO h.hR

/-- `a_s → 0` (RBM2D `s1_Ms_tendsto`, `Step1:242`, `M_s → ∞`). -/
theorem s1_B_tendsto (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    Tendsto (fun n => sz.Bctl n (s n)) atTop (nhds 0) := by
  have hc0 := s1_c0_pos h
  have hS : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := h.hN
  have h1 : Tendsto (fun n => 2 * ((sz.size n : ℕ) : ℝ) ^ (-(min (2 * 𝔠 * 𝔡) τ))) atTop
      (nhds (2 * 0)) :=
    ((tendsto_rpow_neg_atTop hc0).comp hS).const_mul 2
  rw [mul_zero] at h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun n => (s1_B_pos h n).le) ?_
  filter_upwards [s1_a_le h] with n hn
  exact hn (s n) (h.hst n)

/-- `a_s^p ≤ K` eventually (`p > 0`, `K > 0`; RBM2D `s1_Ms_ev_pow`, `Step1:264`). -/
theorem s1_B_ev_pow (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) {p : ℝ} (hp : 0 < p) {K : ℝ} (hK : 0 < K) :
    ∀ᶠ n : ℕ in atTop, sz.Bctl n (s n) ^ p ≤ K := by
  have h0 : Tendsto (fun n => sz.Bctl n (s n) ^ p) atTop (nhds ((0 : ℝ) ^ p)) :=
    (s1_B_tendsto h).rpow_const (Or.inr hp.le)
  rw [Real.zero_rpow hp.ne'] at h0
  exact (h0.eventually (gt_mem_nhds hK)).mono fun n hn => hn.le

/-- `a_s ≤ 1` eventually (RBM2D `s1_one_le_Ms`, `Step1:268`). -/
theorem s1_B_le_one (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, sz.Bctl n (s n) ≤ 1 := by
  have := s1_B_ev_pow h (p := 1) one_pos one_pos
  simpa using this

/-- `a_s` at the energy `E n` (RBM2D `s1Ms`, `Step1:282`: there `M_s`, here `M_s⁻¹ = W^{-d}B_{s,0}`). -/
abbrev s1B (sz : Sizes d) (s : ℕ → ℝ) (n : ℕ) : ℝ := sz.Bctl n (s n)

/-- From `a ≤ 2 N^{-c₀}`: `a^p ≤ 2 N^{-c₀ p}` for `0 ≤ p ≤ 1` (replaces RBM2D `s1_Npow_le`,
`Step1:285`). -/
theorem s1_apow_le {a N c₀ p : ℝ} (ha : 0 ≤ a) (hN : 0 ≤ N) (hle : a ≤ 2 * N ^ (-c₀))
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : a ^ p ≤ 2 * N ^ (-(c₀ * p)) := by
  have h1 : a ^ p ≤ (2 * N ^ (-c₀)) ^ p := Real.rpow_le_rpow ha hle hp0
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN _), ← Real.rpow_mul hN] at h1
  have h2 : (2 : ℝ) ^ p ≤ 2 := by
    calc (2 : ℝ) ^ p ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp1
      _ = 2 := Real.rpow_one 2
  have h3 : 0 ≤ N ^ (-c₀ * p) := Real.rpow_nonneg hN _
  have e : -c₀ * p = -(c₀ * p) := by ring
  rw [e] at h1 h3
  exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)

/-- (`con_st_ind`, `Step1:273` `s1_ratio_ev`) `a_s (1-s)/(1-u) ≤ a_s^{14/15}` uniformly in
`u ∈ [s,t]`, eventually (`𝔠_d ≤ 1/100 ≤ 1/15`, `a_s ≤ 1`). -/
theorem s1_ratio_ev (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, s n ≤ u → u ≤ t n →
      sz.Bctl n (s n) * ((1 - s n) / (1 - u)) ≤ sz.Bctl n (s n) ^ ((14 : ℝ) / 15) := by
  filter_upwards [h.hCond, s1_B_le_one h] with n hn hle u hsu hut
  have h1 := s1_ratio_pt sz n h.h𝔠d hsu hut (h.ht1 n) hn.1
  refine h1.trans ?_
  exact Real.rpow_le_rpow_of_exponent_ge (s1_B_pos h n) hle (by linarith [h.h𝔠d'])


/-- `K ≤ N^y` eventually (`y > 0`). -/
theorem s1_N_pow_ev (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) {y : ℝ} (hy : 0 < y) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, K ≤ ((sz.size n : ℕ) : ℝ) ^ y :=
  ((tendsto_rpow_atTop hy).comp h.hN).eventually_ge_atTop K

/-- The exponent `τ₀` of the initial-data step: `N^{τ₀} a_s^{1/2} < a_s^{1/4}`, eventually
(RBM2D `s1_F3`, `Step1:300`, `N^{τ₀} M_s^{-1/2} < M_s^{-1/4}`), `τ₀ = c₀/8`. -/
theorem s1_F3 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∃ τ₀ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ) ^ τ₀ * (s1B sz s n) ^ ((1 : ℝ) / 2) < (s1B sz s n) ^ ((1 : ℝ) / 4) := by
  have hc0 := s1_c0_pos h
  set c₀ := min (2 * 𝔠 * 𝔡) τ with hc₀
  refine ⟨c₀ * (1 / 8), by positivity, ?_⟩
  filter_upwards [s1_a_le h, s1_N_pow_ev h (y := c₀ * (1 / 8)) (by positivity) 3,
    Eventually.of_forall (s1_one_le_size sz)] with n hn1 hn2 hn3
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn3
  have ha : 0 < s1B sz s n := s1_B_pos h n
  have hb := s1_apow_le ha.le hN0.le (hn1 (s n) (h.hst n)) (p := (1 : ℝ) / 4) (by norm_num)
    (by norm_num)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set b := s1B sz s n ^ ((1 : ℝ) / 4) with hbdef
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hsq : s1B sz s n ^ ((1 : ℝ) / 2) = b * b := by
    rw [hbdef, ← Real.rpow_add ha]; norm_num
  have hXpos : 0 < N ^ (c₀ * (1 / 8)) := Real.rpow_pos_of_pos hN0 _
  have hmul : N ^ (c₀ * (1 / 8)) * N ^ (-(c₀ * (1 / 4))) = (N ^ (c₀ * (1 / 8)))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; congr 1; ring
  have h1 : N ^ (c₀ * (1 / 8)) * b < 1 := by
    calc N ^ (c₀ * (1 / 8)) * b ≤ N ^ (c₀ * (1 / 8)) * (2 * N ^ (-(c₀ * (1 / 4)))) :=
          mul_le_mul_of_nonneg_left hb hXpos.le
      _ = 2 * (N ^ (c₀ * (1 / 8)))⁻¹ := by rw [← hmul]; ring
      _ < 1 := by
          have : (N ^ (c₀ * (1 / 8)))⁻¹ ≤ 3⁻¹ := inv_anti₀ (by norm_num) hn2
          linarith
  rw [hsq]
  nlinarith [mul_pos hb0 hb0]

/-- The exponent `ε` of the gap `f ≪ a` at the net: `(2·3^d) a_s^{7/15} ≤ N^{-ε} (a_s^{1/4}/2)`,
eventually (RBM2D `s1_F4`, `Step1:329`, constant `6`; here `C_d = 2·3^d ≥ √(2·9^d + 1)`, the root
of the constant of `s1_wl_det`), `ε = c₀/8`. -/
theorem s1_F4 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      (2 * (3 : ℝ) ^ d) * (s1B sz s n) ^ ((7 : ℝ) / 15) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-ε) * ((s1B sz s n) ^ ((1 : ℝ) / 4) / 2) := by
  have hc0 := s1_c0_pos h
  set c₀ := min (2 * 𝔠 * 𝔡) τ with hc₀
  refine ⟨c₀ * (1 / 8), by positivity, ?_⟩
  filter_upwards [s1_a_le h, s1_N_pow_ev h (y := (11 / 120 : ℝ) * c₀) (by positivity)
    (4 * (2 * (3 : ℝ) ^ d)), Eventually.of_forall (s1_one_le_size sz)] with n hn1 hn2 hn3
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn3
  have ha : 0 < s1B sz s n := s1_B_pos h n
  have he := s1_apow_le ha.le hN0.le (hn1 (s n) (h.hst n)) (p := (13 : ℝ) / 60) (by norm_num)
    (by norm_num)
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set b := s1B sz s n ^ ((1 : ℝ) / 4) with hbdef
  set e := s1B sz s n ^ ((13 : ℝ) / 60) with hedef
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hsq : s1B sz s n ^ ((7 : ℝ) / 15) = b * e := by
    rw [hbdef, hedef, ← Real.rpow_add ha]; norm_num
  have hX : 0 < N ^ (c₀ * (1 / 8)) := Real.rpow_pos_of_pos hN0 _
  have hY : 0 < N ^ ((11 / 120 : ℝ) * c₀) := Real.rpow_pos_of_pos hN0 _
  have hXinv : N ^ (-(c₀ * (1 / 8))) = (N ^ (c₀ * (1 / 8)))⁻¹ := by
    rw [Real.rpow_neg hN0.le]
  have hmul : N ^ (c₀ * (1 / 8)) * N ^ (-(c₀ * (13 / 60))) = (N ^ ((11 / 120 : ℝ) * c₀))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; congr 1; ring
  -- `2 C X e ≤ 1`
  have key : 2 * (2 * (3 : ℝ) ^ d) * (N ^ (c₀ * (1 / 8)) * e) ≤ 1 := by
    have hC0 : (0 : ℝ) < 2 * (3 : ℝ) ^ d := by positivity
    calc 2 * (2 * (3 : ℝ) ^ d) * (N ^ (c₀ * (1 / 8)) * e)
        ≤ 2 * (2 * (3 : ℝ) ^ d) * (N ^ (c₀ * (1 / 8)) * (2 * N ^ (-(c₀ * (13 / 60))))) := by
          gcongr
      _ = 4 * (2 * (3 : ℝ) ^ d) * (N ^ ((11 / 120 : ℝ) * c₀))⁻¹ := by
          rw [show 4 * (2 * (3 : ℝ) ^ d) * (N ^ ((11 / 120 : ℝ) * c₀))⁻¹ =
            2 * (2 * (3 : ℝ) ^ d) * (2 * (N ^ (c₀ * (1 / 8)) * N ^ (-(c₀ * (13 / 60))))) by
              rw [hmul]; ring]
          ring
      _ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hY]; exact hn2
  rw [hsq, hXinv]
  have hXne : N ^ (c₀ * (1 / 8)) ≠ 0 := hX.ne'
  have : (N ^ (c₀ * (1 / 8)))⁻¹ * (b / 2) - 2 * (3 : ℝ) ^ d * (b * e) =
      (N ^ (c₀ * (1 / 8)))⁻¹ * (b / 2) *
        (1 - 2 * (2 * (3 : ℝ) ^ d) * (N ^ (c₀ * (1 / 8)) * e)) := by
    field_simp
  rw [← sub_nonneg, this]
  exact mul_nonneg (by positivity) (by linarith)

/-- The exponent `c'` of `Ω(u,c')`: `2 a_s^{1/4} ≤ W^{-c'}`, eventually (RBM2D `s1_F5`,
`Step1:382`; there `W² ≤ N`, here `W^τ ≤ N^{τ/d}`, `d ≥ 1`), `c' = c₀/8`. -/
theorem s1_F5 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∃ c' > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      2 * (s1B sz s n) ^ ((1 : ℝ) / 4) ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') := by
  have hc0 := s1_c0_pos h
  have hd : 0 < d := s1_d_pos sz h.hN
  set c₀ := min (2 * 𝔠 * 𝔡) τ with hc₀
  refine ⟨c₀ * (1 / 8), by positivity, ?_⟩
  filter_upwards [s1_a_le h, s1_N_pow_ev h (y := c₀ * (1 / 8)) (by positivity) 4,
    Eventually.of_forall (s1_one_le_size sz)] with n hn1 hn2 hn3
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hn3
  have ha : 0 < s1B sz s n := s1_B_pos h n
  have hb := s1_apow_le ha.le hN0.le (hn1 (s n) (h.hst n)) (p := (1 : ℝ) / 4) (by norm_num)
    (by norm_num)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set b := s1B sz s n ^ ((1 : ℝ) / 4) with hbdef
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  -- `W^{c'} ≤ N^{c'}`
  have hW1 : ((sz.W n : ℕ) : ℝ) ^ (c₀ * (1 / 8)) ≤ N ^ (c₀ * (1 / 8)) := by
    refine (sz.W_rpow_le hd n (by positivity)).trans ?_
    refine Real.rpow_le_rpow_of_exponent_le hn3 ?_
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    rw [div_le_iff₀ (by linarith)]
    nlinarith [show 0 < c₀ * (1 / 8) by positivity]
  have hw : 0 < ((sz.W n : ℕ) : ℝ) ^ (c₀ * (1 / 8)) := Real.rpow_pos_of_pos hW0 _
  have hX : 0 < N ^ (c₀ * (1 / 8)) := Real.rpow_pos_of_pos hN0 _
  have hmul : N ^ (c₀ * (1 / 8)) * N ^ (-(c₀ * (1 / 4))) = (N ^ (c₀ * (1 / 8)))⁻¹ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_neg hN0.le]; congr 1; ring
  have h1 : 2 * b * ((sz.W n : ℕ) : ℝ) ^ (c₀ * (1 / 8)) ≤ 1 := by
    calc 2 * b * ((sz.W n : ℕ) : ℝ) ^ (c₀ * (1 / 8))
        ≤ 2 * (2 * N ^ (-(c₀ * (1 / 4)))) * N ^ (c₀ * (1 / 8)) := by gcongr
      _ = 4 * (N ^ (c₀ * (1 / 8)))⁻¹ := by rw [← hmul]; ring
      _ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hX]; exact hn2
  rw [Real.rpow_neg hW0.le, ← one_div, le_div_iff₀ hw]
  exact h1

/-- `N⁻¹ ≤ a_s^{1/4}/2`, eventually (the mesh of the net is finer than `a/2`; RBM2D `s1_F6`,
`Step1:418`: there `M_s ≤ W² ≤ N`, here `N⁻¹ ≤ W^{-d}B_{s,0}`, `cont_inv_size_le_Bctl`). -/
theorem s1_F6 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop,
      ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (s1B sz s n) ^ ((1 : ℝ) / 4) / 2 := by
  filter_upwards [s1_N_pow_ev h (y := (3 : ℝ) / 4) (by norm_num) 2] with n hn
  have ha : 0 < s1B sz s n := s1_B_pos h n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (s1_one_le_size sz n)
  have hle : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ s1B sz s n :=
    ContinuityNet.cont_inv_size_le_Bctl sz n (h.hs0 n) (s1_s_lt_one h n)
  have h1 : ((sz.size n : ℕ) : ℝ)⁻¹ ^ ((1 : ℝ) / 4) ≤ (s1B sz s n) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (inv_nonneg.2 hN0.le) hle (by norm_num)
  have h2 : 2 * ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-((1 : ℝ) / 4)) := by
    refine s1_mul_rpow_le hN0 ?_
    have : -((1 : ℝ) / 4) - -1 = 3 / 4 := by norm_num
    rw [this]; exact hn
  rw [s1_inv_rpow hN0.le] at h1
  rw [Real.rpow_neg_one] at h2
  linarith

/-- `a_s^{1/4} ≤ 1`, eventually (RBM2D `s1_F7`, `Step1:439`). -/
theorem s1_F7 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, (s1B sz s n) ^ ((1 : ℝ) / 4) ≤ 1 := by
  filter_upwards [s1_B_le_one h] with n hn
  exact Real.rpow_le_one (s1_B_pos h n).le hn (by norm_num)

/-- `W^{-d} ≤ a_s^{14/15}`, eventually (RBM2D `s1_F8`, `Step1:445`, `W⁻² ≤ M_s^{-14/15}`): from
`STBctl_ge` (`0 ≤ s`) and `ilambda ≤ 𝔡⁻¹` (`(eq:WO)`), `W^{-d} ≤ (𝔡⁻² + 1) a_s ≤ a_s^{14/15}` once
`(𝔡⁻² + 1) a_s^{1/15} ≤ 1`. -/
theorem s1_F8 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (s1B sz s n) ^ ((14 : ℝ) / 15) := by
  have hK : 0 < ((𝔡⁻¹) ^ 2 + 1)⁻¹ := by positivity
  filter_upwards [h.hWO, s1_B_ev_pow h (p := (1 : ℝ) / 15) (by norm_num) hK] with n hWO hn
  have ha : 0 < s1B sz s n := s1_B_pos h n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz n
  have hlam0 : 0 ≤ sz.lam n :=
    le_trans (Real.rpow_nonneg hW0.le _) hWO.1
  have hlam : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hWO.2 2
  have hge := sz.STBctl_ge n (h.hs0 n) (s1_s_lt_one h n)
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * s1B sz s n := by
    have hl : 0 < sz.lam n ^ 2 + 1 := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
        = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ * (sz.lam n ^ 2 + 1) := by
          field_simp
      _ ≤ s1B sz s n * (sz.lam n ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hge hl.le
      _ = _ := mul_comm _ _
  have h2 : (sz.lam n ^ 2 + 1) * s1B sz s n ≤ ((𝔡⁻¹) ^ 2 + 1) * s1B sz s n :=
    mul_le_mul_of_nonneg_right (by linarith) ha.le
  have hsplit : s1B sz s n = s1B sz s n ^ ((1 : ℝ) / 15) * s1B sz s n ^ ((14 : ℝ) / 15) := by
    rw [← Real.rpow_add ha]; norm_num
  have h3 : ((𝔡⁻¹) ^ 2 + 1) * s1B sz s n ≤ s1B sz s n ^ ((14 : ℝ) / 15) := by
    have hp : 0 < s1B sz s n ^ ((14 : ℝ) / 15) := Real.rpow_pos_of_pos ha _
    have h4 : ((𝔡⁻¹) ^ 2 + 1) * s1B sz s n ^ ((1 : ℝ) / 15) ≤ 1 := by
      calc ((𝔡⁻¹) ^ 2 + 1) * s1B sz s n ^ ((1 : ℝ) / 15)
          ≤ ((𝔡⁻¹) ^ 2 + 1) * ((𝔡⁻¹) ^ 2 + 1)⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ (by positivity)
    calc ((𝔡⁻¹) ^ 2 + 1) * s1B sz s n
        = (((𝔡⁻¹) ^ 2 + 1) * s1B sz s n ^ ((1 : ℝ) / 15)) * s1B sz s n ^ ((14 : ℝ) / 15) := by
          rw [mul_assoc, ← hsplit]
      _ ≤ 1 * s1B sz s n ^ ((14 : ℝ) / 15) := mul_le_mul_of_nonneg_right h4 hp.le
      _ = _ := one_mul _
  exact h1.trans (h2.trans h3)

end Scales


/-! ## 4. Generic `PerTimeDomAt` helpers -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- A deterministic bound `ξ ≤ N^τ ζ` (eventually, for every `τ > 0`) gives `ξ ≺ ζ`
(RBM2D `s1_pt_of_le`, `Step1:467`). -/
private theorem s1_pt_of_le {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), ∀ᶠ l : ℕ in atTop, ∀ u ω, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ] with l hl u
  have : {ω | (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hl u ω
  rw [this, measure_empty]
  exact zero_le

/-- The union bound in event form: `ξ ≺ ζ` per time, with polynomially many parameters, gives that
`ξ ≤ N^τ ζ` for all parameters simultaneously with high probability (RBM2D `s1_highProb_of_pt`,
`Step1:481`). -/
theorem s1_highProb_of_pt [∀ l, Fintype (U l)] {ξ ζ : ∀ l, U l → Ω → ℝ} {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ᶠ l : ℕ in atTop, (Fintype.card (U l) : ℝ) ≤ (size l : ℝ) ^ C)
    (h : PerTimeDomAt P size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    HighProbAt P size (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω}) :=
  PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt (stochDomAt_of_perTimeDomAt P size hC0 hC h) hτ

/-- Conversely, a high-probability event for every `τ > 0` gives `ξ ≺ ζ` per time (RBM2D
`s1_pt_of_highProb`, `Step1:488`). -/
theorem s1_pt_of_highProb {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), HighProbAt P size
      (fun l => {ω | ∀ u, ξ l u ω ≤ (size l : ℝ) ^ τ * ζ l u ω})) :
    PerTimeDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl u
  refine (measure_mono ?_).trans hl
  intro ω hω hω'
  exact absurd (hω' u) (not_le.2 hω)

/-- Per time along a `Unit`-indexed family is the uniform statement (RBM2D `s1_stochDom_unit`,
`Step1:499`). -/
theorem s1_stochDom_unit {ξ ζ : ∀ _ : ℕ, Unit → Ω → ℝ} (h : PerTimeDomAt P size ξ ζ) :
    StochDomAt P size ξ ζ :=
  stochDomAt_of_perTimeDomAt P size (C := 0) le_rfl
    (Eventually.of_forall fun _ => by simp) h

/-- Case splitting under `≺`, the case distinction holding only for large `l` (the form of
`PerTimeCalc.PerTime.stochDom_of_forall_or` with `∀ᶠ l`, needed because `ilambda ≤ 𝔡⁻¹` holds only
eventually): if for all large `l` and all `(u, ω)` the pair `(ξ, ζ)` is dominated by `(ξ₁, ζ₁)`
or by `(ξ₂, ζ₂)`, then `ξ₁ ≺ ζ₁` and `ξ₂ ≺ ζ₂` give `ξ ≺ ζ`. -/
private theorem s1_pt_of_ev_or (hsize : Tendsto size atTop atTop)
    {ξ ζ ξ₁ ζ₁ ξ₂ ζ₂ : ∀ l, U l → Ω → ℝ}
    (h₁ : PerTimeDomAt P size ξ₁ ζ₁) (h₂ : PerTimeDomAt P size ξ₂ ζ₂)
    (hor : ∀ᶠ l : ℕ in atTop, ∀ u ω, (ξ l u ω ≤ ξ₁ l u ω ∧ ζ₁ l u ω ≤ ζ l u ω) ∨
      (ξ l u ω ≤ ξ₂ l u ω ∧ ζ₂ l u ω ≤ ζ l u ω)) : PerTimeDomAt P size ξ ζ := by
  refine PerTimeCalc.PerTime.perTimeCalc_of_imp_union hsize h₁ h₂ fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hor] with l hl u ω hu
  have hpos : 0 ≤ (size l : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases hl u ω with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])
  · exact Or.inr (by nlinarith [mul_le_mul_of_nonneg_left h2 hpos])

end Generic

/-! ## 5. The loop family: (55) at `t₁ = max(s, 1/2)`, and (`lRB1`) with the indicator -/

section Loops

variable {d : ℕ} {sz : Sizes d} {κ 𝔠 𝔡 τ 𝔠d : ℝ} {E s t : ℕ → ℝ}

/-- `c₁ = √(2κ)/2 > 0` (RBM2D `s1_c1_pos`, `Step1:293`). -/
theorem s1_c1_pos (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : 0 < Real.sqrt (2 * κ) / 2 := by
  have := Real.sqrt_pos.2 (by linarith [h.hκ] : 0 < 2 * κ); linarith

/-- `W^{-d} ≤ (ilambda² + 1) W^{-d} B_{u,0}` for `0 ≤ u < 1` (`STBctl_ge`): the volume factor is
at most the control up to the coupling (replaces RBM2D's `W⁻² ≤ M_u⁻¹`, `s1_scaleM_le_W2`). -/
theorem s1_Wd_le_Bctl (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n u := by
  have hge := sz.STBctl_ge n hu0 hu1
  have hl : 0 < sz.lam n ^ 2 + 1 := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
      = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹ * (sz.lam n ^ 2 + 1) := by
        field_simp
    _ ≤ sz.Bctl n u * (sz.lam n ^ 2 + 1) := mul_le_mul_of_nonneg_right hge hl.le
    _ = _ := mul_comm _ _

/-- `ilambda² + 1 ≤ 𝔡⁻² + 1`, eventually (`(eq:WO)`). -/
theorem s1_lam_sq_le (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) :
    ∀ᶠ n : ℕ in atTop, sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
  filter_upwards [h.hWO] with n hWO
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz n
  have hlam0 : 0 ≤ sz.lam n := le_trans (Real.rpow_nonneg hW0.le _) hWO.1
  have : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hWO.2 2
  linarith

/-- The start time `t₁ = max(s, 1/2)` of the continuity argument (RBM2D `s1T1`, `Step1:513`,
RBM1D `startTime`). -/
abbrev s1T1 (s : ℕ → ℝ) (n : ℕ) : ℝ := max (s n) (1 / 2)

private theorem s1_blockMat_herm {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    (blockMat d L W M).IsHermitian :=
  hM.submatrix _

/-- (`Lboundfor1/2`) (5-6:20--22 of the `d = 2` paper) at a time `u ≤ 1/2` (deterministic):
`|𝓛_{u,σ,a}| ≤ (2/c₁)^k (W^{-d})^{k-1}` when `Im m ≥ c₁` (RBM2D `s1_loop_det`, `Step1:525`;
`d = 2`: `(2/c₁)^k M_u^{-(k-1)}`, via `W⁻² ≤ M_u⁻¹`; here the volume factor `W^{-d}` is kept and
compared with `a_s` by `s1_Wd_le_Bctl`).  `norm_loopM_le_sharp`, `Im z_u = (1-u) Im m ≥ c₁/2`. -/
theorem s1_loop_det {L W : ℕ} [NeZero L] [NeZero W] {E u c₁ : ℝ} (hc₁ : 0 < c₁)
    (hm : c₁ ≤ (mE E).im) (hu : u ≤ 1 / 2)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian) {k : ℕ} (hk : 1 ≤ k)
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ‖loopFine d L W M (zt E u) σ a‖ ≤ (2 / c₁) ^ k * (((W : ℝ) ^ d)⁻¹) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hη : c₁ / 2 ≤ |(zt E u).im| := by
    rw [zt_im, abs_of_nonneg (mul_nonneg (by linarith) (by linarith))]
    calc c₁ / 2 ≤ (1 / 2) * (mE E).im := by linarith
      _ ≤ (1 - u) * (mE E).im := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h1 := norm_loopM_le_sharp d L W (s1_blockMat_herm hM) (by positivity : 0 < c₁ / 2) hη σ a
  have h3 : (c₁ / 2)⁻¹ = 2 / c₁ := by rw [inv_div]
  rw [h3] at h1
  simpa [loopFine] using h1

/-- `KboundConcl κ` along the sequence, per time: `|𝒦_{s,σ,a}| ≺ (W^{-d}B_{s,0})^{k-1}`
(`ML:Kbound`; RBM2D `s1_Kbound_seq`, `Step1:550`): the pin `STKbound` at the time sequence `s`
(`0 ≤ s < 1`), read per time by `perTimeOfStochDomAt`. -/
theorem s1_Kbound_seq (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (hK : STKbound sz E) {k : ℕ}
    (hk : 1 ≤ k) :
    sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p _ => ‖STKloop sz n (E n) (s n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (s n)) ^ (k - 1)) :=
  Path.perTimeOfStochDomAt (seqP sz) sz.size _ _ (hK s h.hs0 (s1_s_lt_one h) k hk)

/-- Hypothesis (55) of `lem_ConArg` (5-6:43–45; `3_5:46` `(eq:loopbound_s)`) at `t₁ = max(s, 1/2)`:
`max_{σ,a} |𝓛_{t₁,σ,a}| ≺ (W^{-d}B_{t₁,0})^{k-1}` per time, for every `k ≥ 1` (RBM2D `S1H55`,
`Step1:570`; this is the hypothesis `h55` of the merged `ConArgPin`). -/
def S1H55 (sz : Sizes d) (E s : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Sizes.Lloop sz n (E n) (s1T1 s n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (s1T1 s n)) ^ (k - 1))

/-- **(55) at `t₁ = max(s, 1/2)`** (Case 2, 5-6:33--36, and Case 3, 5-6:72, of the `d = 2` paper):
for `s ≥ 1/2`, `𝓛 = (𝓛-𝒦) + 𝒦` with `STLK` (`InitLK`) and `STKbound` (`Lboundfors`); for `s < 1/2`
the deterministic bound `s1_loop_det` at `1/2` with `W^{-d} ≤ (𝔡⁻² + 1) a_{1/2}`.  RBM2D `s1_h55`
(`Step1:581`), RBM1D `eq54`, `eq55` (`Hierarchy/Step1.lean:375,399`).  The case distinction
`s n ≥ 1/2` is pointwise in `n`; the constant `(2/c₁)^k (𝔡⁻² + 1)^{k-1}` of the second case
needs `ilambda ≤ 𝔡⁻¹` and so holds for large `n`. -/
theorem s1_h55 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (hIK : STLK sz E s) (hK : STKbound sz E) :
    S1H55 sz E s := by
  intro k hk
  have hsize := s1_hsize sz h.hN
  have hc1 := s1_c1_pos h
  have hLK : sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Sizes.Lloop sz n (E n) (s n) p.1 p.2 ω - STKloop sz n (E n) (s n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (s n)) ^ k) :=
    Path.perTimeOfStochDomAt (seqP sz) sz.size _ _ (hIK k hk)
  have hsum := PerTimeCalc.PerTime.perTimeCalc_add hsize hLK (s1_Kbound_seq h hK hk)
  have hMt1 : ∀ n, 0 < sz.Bctl n (s1T1 s n) := fun n =>
    sz.STBctl_pos n (max_lt (s1_s_lt_one h n) (by norm_num))
  have h₁ := PerTimeCalc.PerTime.perTimeCalc_mono hsize (P := seqP sz) (size := sz.size)
    (ζ' := fun n (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
      (sz.Bctl n (s1T1 s n)) ^ (k - 1))
    (fun n _ _ => pow_nonneg (hMt1 n).le _) 2 ?_ hsum
  swap
  · filter_upwards [s1_B_le_one h] with n hn p ω
    have ha := s1_B_pos h n
    have h2 : (sz.Bctl n (s n)) ^ k ≤ (sz.Bctl n (s n)) ^ (k - 1) :=
      pow_le_pow_of_le_one ha.le hn (Nat.sub_le k 1)
    have h3 : sz.Bctl n (s n) ≤ sz.Bctl n (s1T1 s n) :=
      sz.STBctl_mono n (le_max_left _ _) (max_lt (s1_s_lt_one h n) (by norm_num))
    have h4 : (sz.Bctl n (s n)) ^ (k - 1) ≤ (sz.Bctl n (s1T1 s n)) ^ (k - 1) :=
      pow_le_pow_left₀ ha.le h3 _
    change (sz.Bctl n (s n)) ^ k + (sz.Bctl n (s n)) ^ (k - 1) ≤
      2 * (sz.Bctl n (s1T1 s n)) ^ (k - 1)
    linarith
  set C : ℝ := (2 / (Real.sqrt (2 * κ) / 2)) ^ k * ((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have h₂ := PerTimeCalc.PerTime.stochDom_of_le_const_mul hsize (P := seqP sz) (size := sz.size)
    (ξ := fun n (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
      C * (sz.Bctl n (s1T1 s n)) ^ (k - 1))
    (ζ := fun n (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
      (sz.Bctl n (s1T1 s n)) ^ (k - 1))
    (fun n _ _ => mul_nonneg hC0 (pow_nonneg (hMt1 n).le _))
    (fun n _ _ => pow_nonneg (hMt1 n).le _) C (fun _ _ _ => le_rfl)
  refine s1_pt_of_ev_or hsize h₁ h₂ ?_
  filter_upwards [s1_lam_sq_le h] with n hlam p ω
  by_cases hs : 1 / 2 ≤ s n
  · left
    have ht : s1T1 s n = s n := max_eq_left hs
    refine ⟨?_, le_rfl⟩
    rw [ht]
    exact norm_le_norm_sub_add _ _
  · right
    have hs' : s n < 1 / 2 := not_le.1 hs
    have ht : s1T1 s n = 1 / 2 := max_eq_right hs'.le
    refine ⟨?_, le_rfl⟩
    rw [ht]
    have hdet := s1_loop_det (d := d) (L := sz.L n) (W := sz.W n) hc1
      (s1_bulk h.hκ (h.hE n)).2 (le_refl (1 / 2 : ℝ)) (sz.seqHflow n (1 / 2) ω)
      (Sizes.seqHflow_isHermitian sz n _ ω) hk p.1 p.2
    have hW := s1_Wd_le_Bctl sz n (u := 1 / 2) (by norm_num) (by norm_num)
    have hW' : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (1 / 2) :=
      hW.trans (mul_le_mul_of_nonneg_right hlam (sz.STBctl_pos n (by norm_num)).le)
    have h5 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) ≤
        (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (1 / 2)) ^ (k - 1) :=
      pow_le_pow_left₀ (by positivity) hW' _
    rw [mul_pow] at h5
    calc ‖Sizes.Lloop sz n (E n) (1 / 2) p.1 p.2 ω‖
        ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) := hdet
      _ ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k *
          (((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) * sz.Bctl n (1 / 2) ^ (k - 1)) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = C * sz.Bctl n (1 / 2) ^ (k - 1) := by rw [hCdef]; ring

/-- The indicator `STomegaC` of `{‖G_u‖_max ≤ C₀}` is at most `1`. -/
theorem s1_omegaC_le_one (n : ℕ) (E τ C₀ : ℝ) (ω : sz.SeqΩ) :
    sz.STomegaC n E τ C₀ ω ≤ 1 := by
  unfold Sizes.STomegaC; split_ifs <;> norm_num

/-- **`(lRB1)` with the indicator, per time sequence** (`jsajufua`, 5-6:57–59 of the `d = 2`
paper, from `lem_ConArg`, `3_5:42-62`, and (`Lboundfor1/2`) for `u < 1/2`; RBM2D `s1_LI`,
`Step1:641`, RBM1D `eq58_seq`, `Hierarchy/Step1.lean:419`): for every time sequence
`u n ∈ [s n, t n]` and `k ≥ 1`,
`1(‖G_u‖_max ≤ 2) |𝓛_{u,σ,a}| ≺ ((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1}` per time.
For `u ≥ 1/2` this is the merged `conArg` at `(t₁, u)`, `t₁ = max(s,1/2)`, with
`(W^{-d}B_{t₁,0} η_{t₁}/η_u)^{k-1} ≤ ((1-s)/(1-u) W^{-d}B_{s,0})^{k-1}` (`STBctl_xmono`,
`η_s/η_u = (1-s)/(1-u)`); for `u < 1/2` the deterministic bound `s1_loop_det` with
`W^{-d} ≤ (𝔡⁻² + 1) a_s ≤ (𝔡⁻² + 1) a_s (1-s)/(1-u)` (`(1-s)/(1-u) ≥ 1`). -/
theorem s1_LI (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : S1H55 sz E s) (u : ℕ → ℝ)
    (hu : ∀ n, u n ∈ Set.Icc (s n) (t n)) {k : ℕ} (hk : 1 ≤ k) :
    sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => sz.STomegaC n (E n) (u n) 2 ω * ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
  have hsize := s1_hsize sz h.hN
  have hc1 := s1_c1_pos h
  have hs1 : ∀ n, s n < 1 := s1_s_lt_one h
  have hu1 : ∀ n, u n < 1 := fun n => lt_of_le_of_lt (hu n).2 (h.ht1 n)
  have hcon := conArg sz κ (1 / 4) 2 E (s1T1 s) (fun n => max (u n) (s1T1 s n)) h.hκ h.hE
    (by norm_num) (by norm_num) (fun n => le_max_of_le_right (by norm_num))
    (fun n => le_max_right _ _)
    (fun n => max_lt (hu1 n) (max_lt (hs1 n) (by norm_num))) h.hN h55 k hk
  have hζ0 : ∀ n, 0 ≤ ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1) := fun n =>
    mul_nonneg (pow_nonneg (div_nonneg (by linarith [hs1 n]) (by linarith [hu1 n])) _)
      (pow_nonneg (s1_B_pos h n).le _)
  set C : ℝ := (2 / (Real.sqrt (2 * κ) / 2)) ^ k * ((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have h₂ := PerTimeCalc.PerTime.stochDom_of_le_const_mul hsize (P := seqP sz) (size := sz.size)
    (ξ := fun n (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
      C * (((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)))
    (ζ := fun n (_ : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (_ : sz.SeqΩ) =>
      ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
    (fun n _ _ => mul_nonneg hC0 (hζ0 n)) (fun n _ _ => hζ0 n) C (fun _ _ _ => le_rfl)
  refine s1_pt_of_ev_or hsize hcon h₂ ?_
  filter_upwards [s1_lam_sq_le h] with n hlam p ω
  by_cases hu12 : 1 / 2 ≤ u n
  · left
    have ht2 : max (u n) (s1T1 s n) = u n := max_eq_left (max_le (hu n).1 hu12)
    have hs1' : s n ≤ s1T1 s n := le_max_left _ _
    have hs1'' : s1T1 s n < 1 := max_lt (hs1 n) (by norm_num)
    have hxu : 0 < 1 - u n := by linarith [hu1 n]
    refine ⟨?_, ?_⟩
    · simp only [ht2]; exact le_rfl
    · simp only [ht2]
      have hE2 : |E n| < 2 := (s1_bulk h.hκ (h.hE n)).1
      rw [scaleFacts_etaT_div_etaT hE2]
      have hx := sz.STBctl_xmono n hs1' hs1''
      have h1 : sz.Bctl n (s1T1 s n) * ((1 - s1T1 s n) / (1 - u n)) ≤
          ((1 - s n) / (1 - u n)) * sz.Bctl n (s n) := by
        have e1 : sz.Bctl n (s1T1 s n) * ((1 - s1T1 s n) / (1 - u n)) =
            ((1 - s1T1 s n) * sz.Bctl n (s1T1 s n)) / (1 - u n) := by ring
        have e2 : ((1 - s n) / (1 - u n)) * sz.Bctl n (s n) =
            ((1 - s n) * sz.Bctl n (s n)) / (1 - u n) := by ring
        rw [e1, e2]
        exact div_le_div_of_nonneg_right hx hxu.le
      calc (sz.Bctl n (s1T1 s n) * ((1 - s1T1 s n) / (1 - u n))) ^ (k - 1)
          ≤ (((1 - s n) / (1 - u n)) * sz.Bctl n (s n)) ^ (k - 1) :=
            pow_le_pow_left₀ (mul_nonneg (sz.STBctl_pos n hs1'').le
              (div_nonneg (by linarith) hxu.le)) h1 _
        _ = ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1) := mul_pow _ _ _
  · right
    have hu' : u n < 1 / 2 := not_le.1 hu12
    refine ⟨?_, le_rfl⟩
    have hxu : 0 < 1 - u n := by linarith [hu1 n]
    have hdet := s1_loop_det (d := d) (L := sz.L n) (W := sz.W n) hc1
      (s1_bulk h.hκ (h.hE n)).2 hu'.le (sz.seqHflow n (u n) ω)
      (Sizes.seqHflow_isHermitian sz n _ ω) hk p.1 p.2
    have hW := s1_Wd_le_Bctl sz n (u := s n) (h.hs0 n) (hs1 n)
    have hrat : 1 ≤ (1 - s n) / (1 - u n) := by
      rw [one_le_div hxu]; linarith [(hu n).1]
    have hBs := s1_B_pos h n
    have hW' : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
        ((𝔡⁻¹) ^ 2 + 1) * (sz.Bctl n (s n) * ((1 - s n) / (1 - u n))) := by
      refine hW.trans ?_
      calc (sz.lam n ^ 2 + 1) * sz.Bctl n (s n)
          ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (s n) := mul_le_mul_of_nonneg_right hlam hBs.le
        _ ≤ ((𝔡⁻¹) ^ 2 + 1) * (sz.Bctl n (s n) * ((1 - s n) / (1 - u n))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact le_mul_of_one_le_right hBs.le hrat
    have h5 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) ≤
        (((𝔡⁻¹) ^ 2 + 1) * (sz.Bctl n (s n) * ((1 - s n) / (1 - u n)))) ^ (k - 1) :=
      pow_le_pow_left₀ (by positivity) hW' _
    rw [mul_pow, mul_pow] at h5
    have hind := s1_omegaC_le_one (sz := sz) n (E n) (u n) 2 ω
    have hnn : 0 ≤ ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖ := norm_nonneg _
    calc sz.STomegaC n (E n) (u n) 2 ω * ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖
        ≤ ‖Sizes.Lloop sz n (E n) (u n) p.1 p.2 ω‖ := mul_le_of_le_one_left hnn hind
      _ ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ (k - 1) := hdet
      _ ≤ (2 / (Real.sqrt (2 * κ) / 2)) ^ k *
          (((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) *
            (sz.Bctl n (s n) ^ (k - 1) * ((1 - s n) / (1 - u n)) ^ (k - 1))) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = C * (((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
          rw [hCdef]; ring

end Loops

/-! ## 6. Bridges: the lattice ball, `‖G_u - m‖_max`, the indicators, `STgexRHS` -/

section Bridge

variable {d : ℕ}

private theorem s1_zdist_le_one {L : ℕ} [NeZero L] {x : ZMod L} (h : zdist L x ≤ 1) :
    x = 0 ∨ x = 1 ∨ x = -1 := by
  have hx : x.val < L := ZMod.val_lt x
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hx' : x = ((x.val : ℕ) : ZMod L) := (ZMod.natCast_zmod_val x).symm
  simp only [zdist] at h
  rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val = L - 1) with h0 | h0 | h0
  · left; rw [hx', h0]; simp
  · right; left; rw [hx', h0]; simp
  · right; right; rw [hx', h0, Nat.cast_sub (by omega)]; simp

/-- **The number of near blocks** (RBM2D `s1_near_card`, `Step1:810`, `≤ 5`: the `sbSupport` of the
`d = 2` profile): `#{a' : |a' - a|_∞ ≤ 1} ≤ 3^d` (the `L^∞` ball of radius `1` of the paper,
`zdistInf`; it has exactly `3^d` points for `L ≥ 3`.  The ticket's `2d + 1` is the `zdistD` ball). -/
theorem s1_near_card {L : ℕ} [NeZero L] (a : Zd d L) :
    ((Finset.univ.filter (fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1)).card : ℝ) ≤ 3 ^ d := by
  classical
  set T : Finset (Zd d L) :=
    Fintype.piFinset (fun _ : Fin d => ({0, 1, -1} : Finset (ZMod L))) with hT
  have hsub : Finset.univ.filter (fun a' : Zd d L => zdistInf d L (a' - a) ≤ 1) ⊆
      T.image (fun v => v + a) := by
    intro a' ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    refine Finset.mem_image.2 ⟨a' - a, ?_, by simp⟩
    rw [hT, Fintype.mem_piFinset]
    intro i
    have hi : zdist L ((a' - a) i) ≤ 1 :=
      Finset.sup_le_iff.1 ha' i (Finset.mem_univ i)
    rcases s1_zdist_le_one hi with h0 | h0 | h0 <;> simp [h0]
  have hTcard : T.card ≤ 3 ^ d := by
    rw [hT, Fintype.card_piFinset]
    have := Finset.prod_le_pow_card (Finset.univ : Finset (Fin d))
      (fun _ => ({0, 1, -1} : Finset (ZMod L)).card) 3 (fun _ _ => Finset.card_le_three)
    simpa using this
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  exact_mod_cast this.trans hTcard

end Bridge

section BridgeEntries

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `‖G_u - m‖_max = max_{i,j} |(G_u - m)_{ij}|` at the matrix `M` (RBM2D `s1xM`, `Step1:858`;
entries `llErrMat`, `Green/Pins.lean:73`). -/
def s1xM (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun q : Idx d L W × Idx d L W => Green.llErrMat d L W E u M q.1 q.2)

theorem s1xM_ge (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) :
    Green.llErrMat d L W E u M i j ≤ s1xM d L W E u M :=
  Finset.le_sup' (fun q : Idx d L W × Idx d L W => Green.llErrMat d L W E u M q.1 q.2)
    (Finset.mem_univ (i, j))

theorem s1xM_le {E u B : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ i j, Green.llErrMat d L W E u M i j ≤ B) : s1xM d L W E u M ≤ B :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

theorem s1xM_nonneg (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    0 ≤ s1xM d L W E u M := by
  obtain ⟨i⟩ : Nonempty (Idx d L W) := inferInstance
  exact (norm_nonneg _).trans (s1xM_ge E u M i i)

/-- `llErrMat` as the matrix inverse (`Gres = Ring.inverse`, `Matrix.nonsing_inv_eq_ringInverse`). -/
theorem s1_llErrMat_eq (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) :
    Green.llErrMat d L W E u M i j =
      ‖(M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
        (if i = j then mE E else 0)‖ := by
  unfold Green.llErrMat Gres
  simp only [ite_true]
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- `‖G_u‖_max ≤ 1 + ‖G_u - m‖_max` (`|m| = 1`; RBM2D `s1_gMax_le`, `Step1:877`, `gMax`). -/
theorem s1_gMax_le {E u : ℝ} (hE : |E| ≤ 2) (M : Matrix (Idx d L W) (Idx d L W) ℂ)
    (i j : Idx d L W) : ‖Gres M (zt E u) true i j‖ ≤ 1 + s1xM d L W E u M := by
  have h1 := norm_le_norm_sub_add (Gres M (zt E u) true i j) (if i = j then mE E else 0)
  have h2 : ‖(if i = j then mE E else 0)‖ ≤ 1 := by
    split_ifs
    · rw [norm_mE hE]
    · simp
  have h3 := s1xM_ge E u M i j
  unfold Green.llErrMat at h3
  linarith

/-- One-sided Lipschitz bound of `‖G_u - m‖_max` in the resolvent entries (RBM2D `s1xM_le_add`,
`Step1:892`). -/
theorem s1xM_le_add {E u u' δ : ℝ} {M M' : Matrix (Idx d L W) (Idx d L W) ℂ}
    (h : ∀ i j, ‖(M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (M' - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j‖ ≤ δ) :
    s1xM d L W E u M ≤ s1xM d L W E u' M' + δ := by
  refine s1xM_le fun i j => ?_
  have h1 := s1xM_ge E u' M' i j
  have h6 := norm_le_norm_sub_add
    ((M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (if i = j then mE E else 0))
    ((M' - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (if i = j then mE E else 0))
  have h4 : ((M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (if i = j then mE E else 0)) -
      ((M' - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (if i = j then mE E else 0)) =
      (M - zt E u • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j -
      (M' - zt E u' • (1 : Matrix (Idx d L W) (Idx d L W) ℂ))⁻¹ i j := by ring
  rw [h4] at h6
  have h7 := h i j
  rw [s1_llErrMat_eq] at h1 ⊢
  linarith

end BridgeEntries

section BridgeSample

variable {d : ℕ} (sz : Sizes d)

/-- The merged sample-level entry `‖(G_u - M)_{xy}‖` (`STGM`) is `llErrMat` at `H_u(ω)`. -/
theorem s1_STGM_norm (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖sz.STGM n E u ω x y‖ = Green.llErrMat d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) x y := rfl

/-- `‖G_u - m‖_max ≤ C₀ - 1` gives the indicator `STomegaC = 1` of `{‖G_u‖_max ≤ C₀}`
(RBM2D: `gMax E u M ≤ 2`, `Step1:877`). -/
theorem s1_omegaC_eq_one (n : ℕ) (ω : sz.SeqΩ) {E u C₀ : ℝ} (hE : |E| ≤ 2)
    (hx : s1xM d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) ≤ C₀ - 1) :
    sz.STomegaC n E u C₀ ω = 1 := by
  unfold Sizes.STomegaC
  have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖Sizes.Gt sz n E u true ω x y‖ ≤ C₀ := by
    intro x y
    have h1 := s1_gMax_le (u := u) hE (sz.seqHflow n u ω) x y
    have e : Sizes.Gt sz n E u true ω x y = Gres (sz.seqHflow n u ω) (zt E u) true x y := rfl
    rw [e]
    linarith
  simp [hall]

/-- `‖G_u - m‖_max ≤ A` gives the indicator `STindMax = 1` of `Ω(u, A)`. -/
theorem s1_indMax_eq_one (n : ℕ) (ω : sz.SeqΩ) {E u A : ℝ}
    (hx : s1xM d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) ≤ A) :
    sz.STindMax n E u A ω = 1 := by
  unfold Sizes.STindMax
  have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖sz.STGM n E u ω x y‖ ≤ A := by
    intro x y
    rw [s1_STGM_norm]
    exact (s1xM_ge E u _ x y).trans hx
  simp [hall]

/-- **The right side of (`GijGEX`)** is at most `2·9^d B + W^{-d}` if every
`|𝓛^{(2)}_{σ,(a',b')}| ≤ B` (RBM2D `s1_gexRHS_le`, `Step1:823`, `25 B + W⁻²`: at `d = 2` one
orientation and `5 · 5` neighbours; here `STgexRHS` sums the two orientations
`σ ∈ {(+,-),(-,+)}` and each `L^∞`-ball of radius `1` has `≤ 3^d` blocks, `s1_near_card`). -/
theorem s1_gexRHS_le (n : ℕ) (E u B : ℝ) (ω : sz.SeqΩ)
    (hL : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), ‖Sizes.Lloop sz n E u σ b ω‖ ≤ B)
    (a b : Zd d (sz.L n)) :
    sz.STgexRHS n E u ω a b ≤ 2 * 9 ^ d * B + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hL (fun _ => true) (fun _ => 0))
  unfold Sizes.STgexRHS
  set Fa := Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1)
    with hFa
  set Fb := Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1)
    with hFb
  have hFa' : (Fa.card : ℝ) ≤ 3 ^ d := s1_near_card a
  have hFb' : (Fb.card : ℝ) ≤ 3 ^ d := s1_near_card b
  have h3d : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hinner : ∀ σ : Fin 2 → Bool,
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖Sizes.Lloop sz n E u σ ![a', b'] ω‖ ≤ 3 ^ d * (3 ^ d * B) := by
    intro σ
    calc ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖Sizes.Lloop sz n E u σ ![a', b'] ω‖
        ≤ ∑ _a' ∈ Fa, ((3 : ℝ) ^ d * B) := Finset.sum_le_sum fun a' _ => by
          calc ∑ b' ∈ Fb, ‖Sizes.Lloop sz n E u σ ![a', b'] ω‖ ≤ ∑ _b' ∈ Fb, B :=
                Finset.sum_le_sum fun b' _ => hL σ ![a', b']
            _ = Fb.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 3 ^ d * B := mul_le_mul_of_nonneg_right hFb' hB
      _ = Fa.card * ((3 : ℝ) ^ d * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ d * (3 ^ d * B) := mul_le_mul_of_nonneg_right hFa' (by positivity)
  have hS : ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖Sizes.Lloop sz n E u σ ![a', b'] ω‖ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
    calc _ ≤ ∑ _σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ((3 : ℝ) ^ d * (3 ^ d * B)) := Finset.sum_le_sum fun σ _ => hinner σ
      _ = (({![true, false], ![false, true]} : Finset (Fin 2 → Bool)).card : ℝ) *
          (3 ^ d * (3 ^ d * B)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_two
  have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then (1 : ℝ) else 0) ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; positivity
  have h9 : 2 * ((3 : ℝ) ^ d * (3 ^ d * B)) = 2 * 9 ^ d * B := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
  linarith

/-- **The deterministic core of the weak-law step** (5-6:60–63; RBM2D `s1_wl_det`, `Step1:918`):
on `{‖G_u - m‖_max ≤ 2a}`, with `2a ≤ W^{-c'}` (so `Ω(u,c')` holds and `‖G_u‖_max ≤ 2`), the three
per-time bounds `1_Ω |G_{pq}|² ≤ N^τ 𝓛-terms` (`STGiiGEX`, `STGijGEX`) and `1_Ω |𝓛| ≤ N^τ g` give
`|(G_u - m)_{ij}|² ≤ (2·9^d + 1) N^{2τ} g` (RBM2D `26`; `s1_gexRHS_le`).  Stated at the sample
`ω` with the merged `STGM`, `STindMax`, `STomegaC`, `STmaxLoop2`, `STgexRHS`; the hypotheses
`hii`, `hij` are literally the events produced by `Prec.whp` from `STGiiGEX`, `STGijGEX`. -/
theorem s1_wl_det (n : ℕ) (ω : sz.SeqΩ) {E u a c' g Nτ : ℝ} (hE : |E| ≤ 2) (hc' : 0 < c')
    (hx : s1xM d (sz.L n) (sz.W n) E u (sz.seqHflow n u ω) ≤ 2 * a)
    (hΩ : 2 * a ≤ ((sz.W n : ℕ) : ℝ) ^ (-c')) (hNτ : 1 ≤ Nτ) (hg : 0 ≤ g)
    (hWg : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ g)
    (hLoop : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      sz.STomegaC n E u 2 ω * ‖Sizes.Lloop sz n E u σ b ω‖ ≤ Nτ * g)
    (hii : ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      sz.STindMax n E u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖sz.STGM n E u ω p.1 p.2‖ ^ 2 ≤
        Nτ * sz.STmaxLoop2 n E u ω)
    (hij : ∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2},
      sz.STindMax n E u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω *
          ‖Sizes.Gt sz n E u true ω p.1.1 p.1.2‖ ^ 2 ≤
        Nτ * sz.STgexRHS n E u ω (sz.STblk n p.1.1) (sz.STblk n p.1.2)) :
    ∀ i j, ‖sz.STGM n E u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz n
  have hWc : ((sz.W n : ℕ) : ℝ) ^ (-c') ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hom : sz.STindMax n E u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω = 1 :=
    s1_indMax_eq_one sz n ω (hx.trans hΩ)
  have hom2 : sz.STomegaC n E u 2 ω = 1 :=
    s1_omegaC_eq_one sz n ω hE (by linarith)
  have hLoop' : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖Sizes.Lloop sz n E u σ b ω‖ ≤ Nτ * g := fun σ b => by
    have := hLoop σ b
    rwa [hom2, one_mul] at this
  have hB : 0 ≤ Nτ * g := mul_nonneg (by linarith) hg
  have hmax : sz.STmaxLoop2 n E u ω ≤ Nτ * g :=
    Finset.sup'_le _ _ fun p _ => hLoop' _ _
  have hgle : g ≤ Nτ * g := by nlinarith
  intro i j
  by_cases hij' : i = j
  · subst hij'
    have h1 := hii (i, i)
    rw [hom, one_mul] at h1
    have h2 : Nτ * sz.STmaxLoop2 n E u ω ≤ Nτ * (Nτ * g) :=
      mul_le_mul_of_nonneg_left hmax (by linarith)
    have h3 : 0 ≤ Nτ ^ 2 * g := mul_nonneg (sq_nonneg _) hg
    have h9 : (0 : ℝ) ≤ 9 ^ d := by positivity
    have h4 : Nτ * (Nτ * g) ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by
      nlinarith [mul_nonneg h9 h3]
    simp only at h1
    linarith
  · have h1 := hij ⟨(i, j), hij'⟩
    rw [hom, one_mul] at h1
    simp only at h1
    have hGM : sz.STGM n E u ω i j = Sizes.Gt sz n E u true ω i j := by
      unfold Sizes.STGM; simp [hij']
    have h2 := s1_gexRHS_le sz n E u (Nτ * g) ω hLoop' (sz.STblk n i) (sz.STblk n j)
    have h3 : Nτ * sz.STgexRHS n E u ω (sz.STblk n i) (sz.STblk n j) ≤
        Nτ * (2 * 9 ^ d * (Nτ * g) + Nτ * g) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by linarith)
    have e : Nτ * (2 * 9 ^ d * (Nτ * g) + Nτ * g) = (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by ring
    rw [hGM]
    linarith

end BridgeSample

end RBM.Ind

/-! ## 7. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; `κ = ε = 1/10`; the flow points
`z_n = 1/2 + i N_n^{-4/5}` of `InductionDefsInst` (`flow_z0`); times `s ≡ 0 ≤ u ≤ t ≡ 1/16 ≤ lemT z_n`;
`𝔠_d = 1/100` (`conStInd_inst`).  `S1Std` is discharged completely (`s1Std_sz0`), so every
statement of sections 3-6 about the scales holds at these data.  What stays a hypothesis of an
instance is another gate's pin (`STKbound`, `STLK`, `STLocalMax`, `STGbEXPii`, `STGbEXPij`,
`Step1TargetV3` itself, proved by S1-36) or, for `s1_wl_det` at `u = 1/16`, an event premise on the
sample (`‖G_u - m‖_max ≤ 2a`, `STGiiGEX`, `STGijGEX` at `ω`). -/

namespace RBM.Ind.Step1SetupInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Path
  RBM.Gauss.StochDomAtInst Filter MeasureTheory

/-- `S1Std` at `(sz0, z0, s ≡ 0, t ≡ 1/16)`: `κ = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`, `τ = ε/2`,
`𝔠_d = 1/100`; every field is discharged. -/
theorem s1Std_sz0 :
    S1Std sz0 (1 / 10) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (STflowE z0) sInst tInst :=
  s1_std_of_stFlow (by norm_num) (by norm_num) (by norm_num) le_rfl flow_z0 (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) sixteenth_le_lemT
    (conStInd_inst (by norm_num))

/-- **Instance of `s1_std_of_stFlow`, `s1_c0_pos`, `s1_s_lt_one`, `s1_B_pos`, `s1_Bu_pos`,
`s1_c1_pos`**: `c₀ = min(2𝔠𝔡, τ) = 1/30 > 0`, `a_s(0) > 0` at `n = 0`. -/
example : 0 < min (2 * (1 / 6 : ℝ) * (1 / 10)) ((1 / 10) / 2) := s1_c0_pos s1Std_sz0
example : sInst 0 < 1 := s1_s_lt_one s1Std_sz0 0
example : 0 < sz0.Bctl 0 (sInst 0) := s1_B_pos s1Std_sz0 0
example : 0 < sz0.Bctl 0 (1 / 32) := s1_Bu_pos s1Std_sz0 0 (u := 1 / 32) (by simp only [tInst]; norm_num)
example : 0 < Real.sqrt (2 * (1 / 10 : ℝ)) / 2 := s1_c1_pos s1Std_sz0

/-- **Instances of the elementary facts** at `sz0`, `n = 0` (`L = 4`, `W = 32`, `N = 2097152`). -/
example : ((sz0.size 0 : ℕ) : ℝ) = (((sz0.W 0 : ℕ) : ℝ) * ((sz0.L 0 : ℕ) : ℝ)) ^ 3 :=
  s1_size_eq sz0 0
example : 1 ≤ sz0.L 0 := s1_one_le_L sz0 0
example : 1 ≤ sz0.W 0 := s1_one_le_W sz0 0
example : (1 : ℝ) ≤ ((sz0.size 0 : ℕ) : ℝ) := s1_one_le_size sz0 0
example : ((sz0.W 0 : ℕ) : ℝ) ^ 3 ≤ ((sz0.size 0 : ℕ) : ℝ) := s1_W_pow_le_size sz0 0
example : Tendsto sz0.size atTop atTop := s1_hsize sz0 sz0_tendsto
example : 0 < 3 := s1_d_pos sz0 sz0_tendsto
example : ((2 : ℝ)⁻¹) ^ ((1 : ℝ) / 4) = (2 : ℝ) ^ (-((1 : ℝ) / 4)) := s1_inv_rpow (by norm_num) _
example : |(1 / 2 : ℝ)| < 2 ∧ Real.sqrt (2 * 1) / 2 ≤ (mE (1 / 2)).im :=
  s1_bulk one_pos (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num)
/-- `s1_apow_le` at `a = 1/4`, `N = 16`, `c₀ = 1/2`, `p = 1/2`. -/
example : (1 / 4 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 * (16 : ℝ) ^ (-((1 / 2 : ℝ) * (1 / 2))) :=
  s1_apow_le (by norm_num) (by norm_num)
    (by
      have h : (16 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 4 := by
        rw [Real.rpow_neg (by norm_num), show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h]; norm_num)
    (by norm_num) (by norm_num)

/-- **Scale facts at `sz0`** (rows R1, R2 of the exponent table): `a_u ≤ 2N^{-c₀}`, `a_s → 0`,
`a_s^p ≤ K`, `a_s ≤ 1`, `N^y ≥ K`, `ilambda² + 1 ≤ 𝔡⁻² + 1`, all eventually. -/
example : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ tInst n →
    sz0.Bctl n u ≤ 2 * ((sz0.size n : ℕ) : ℝ) ^ (-(min (2 * (1 / 6 : ℝ) * (1 / 10)) ((1 / 10) / 2))) :=
  s1_a_le s1Std_sz0
example : Tendsto (fun n => sz0.Bctl n (sInst n)) atTop (nhds 0) := s1_B_tendsto s1Std_sz0
example : ∀ᶠ n : ℕ in atTop, sz0.Bctl n (sInst n) ^ ((1 : ℝ) / 8) ≤ 1 :=
  s1_B_ev_pow s1Std_sz0 (by norm_num) one_pos
example : ∀ᶠ n : ℕ in atTop, sz0.Bctl n (sInst n) ≤ 1 := s1_B_le_one s1Std_sz0
example : ∀ᶠ n : ℕ in atTop, 3 ≤ ((sz0.size n : ℕ) : ℝ) ^ ((1 : ℝ) / 8) :=
  s1_N_pow_ev s1Std_sz0 (by norm_num) 3
example : ∀ᶠ n : ℕ in atTop, sz0.lam n ^ 2 + 1 ≤ ((1 / 10 : ℝ)⁻¹) ^ 2 + 1 :=
  s1_lam_sq_le s1Std_sz0
example : (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ (sz0.lam 0 ^ 2 + 1) * sz0.Bctl 0 (1 / 2) :=
  s1_Wd_le_Bctl sz0 0 (by norm_num) (by norm_num)

/-- **Instance of `s1_ratio_pt`**: `n` with `a_t^{𝔠_d} ≤ (1-t)/(1-s)` (`conStInd_inst`), `s = 0 ≤
u = 1/32 ≤ t = 1/16`: `a_0 (1-0)/(1-1/32) ≤ a_0^{1-1/100}`. -/
example : ∃ n : ℕ, sz0.Bctl n 0 * ((1 - 0) / (1 - 1 / 32)) ≤ (sz0.Bctl n 0) ^ (1 - (1 / 100 : ℝ)) := by
  obtain ⟨n, hn, -⟩ := (conStInd_inst (𝔠d := 1 / 100) (by norm_num)).exists
  exact ⟨n, s1_ratio_pt sz0 n (c := 1 / 100) (s := 0) (u := 1 / 32) (t := 1 / 16) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by simpa [sInst, tInst] using hn)⟩

/-- **Instance of `s1_ratio_ev`**. -/
example : ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, sInst n ≤ u → u ≤ tInst n →
    sz0.Bctl n (sInst n) * ((1 - sInst n) / (1 - u)) ≤ sz0.Bctl n (sInst n) ^ ((14 : ℝ) / 15) :=
  s1_ratio_ev s1Std_sz0

/-- **Instances of `s1_F3`-`s1_F8`** (`∃ τ₀, ε, c'` and the eventual inequalities). -/
example : ∃ τ₀ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ((sz0.size n : ℕ) : ℝ) ^ τ₀ * (s1B sz0 sInst n) ^ ((1 : ℝ) / 2) <
      (s1B sz0 sInst n) ^ ((1 : ℝ) / 4) := s1_F3 s1Std_sz0
example : ∃ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (2 * (3 : ℝ) ^ 3) * (s1B sz0 sInst n) ^ ((7 : ℝ) / 15) ≤
      ((sz0.size n : ℕ) : ℝ) ^ (-ε) * ((s1B sz0 sInst n) ^ ((1 : ℝ) / 4) / 2) := s1_F4 s1Std_sz0
example : ∃ c' > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    2 * (s1B sz0 sInst n) ^ ((1 : ℝ) / 4) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-c') := s1_F5 s1Std_sz0
example : ∀ᶠ n : ℕ in atTop,
    ((sz0.size n : ℕ) : ℝ)⁻¹ ≤ (s1B sz0 sInst n) ^ ((1 : ℝ) / 4) / 2 := s1_F6 s1Std_sz0
example : ∀ᶠ n : ℕ in atTop, (s1B sz0 sInst n) ^ ((1 : ℝ) / 4) ≤ 1 := s1_F7 s1Std_sz0
example : ∀ᶠ n : ℕ in atTop,
    (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ (s1B sz0 sInst n) ^ ((14 : ℝ) / 15) := s1_F8 s1Std_sz0

/-! ### Further windows `[s_0, t_0]` at `sz0` (constant times), for the branches `u ≥ 1/2`, `s ≥ 1/2` -/

/-- `(con_st_ind)` at constant times `s_0 < t_0 < 1` for every `𝔠_d > 0`, eventually: `W^{-3}B_{t_0,0}
≤ 2 (1 - t_0)⁻¹ W^{-3} → 0` (`Bctl_const_le`). -/
theorem s1Setup_conStInd_const {s0 t0 𝔠d : ℝ} (hst : s0 < t0) (ht : t0 < 1) (h𝔠 : 0 < 𝔠d) :
    STConStInd sz0 𝔠d (fun _ => s0) (fun _ => t0) := by
  have hW : Tendsto (fun n : ℕ => (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp W_tendsto_sz0)
  have hup : Tendsto (fun n : ℕ => 2 * (1 - t0)⁻¹ * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) := by
    simpa using hW.const_mul (2 * (1 - t0)⁻¹)
  have hB : Tendsto (fun n => sz0.Bctl n t0) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_)
      (fun n => Bctl_const_le n ht)
    exact (sz0.STBctl_pos n ht).le
  have h0 : Tendsto (fun n => sz0.Bctl n t0 ^ 𝔠d) atTop (nhds ((0 : ℝ) ^ 𝔠d)) :=
    hB.rpow_const (Or.inr h𝔠.le)
  rw [Real.zero_rpow h𝔠.ne'] at h0
  have hpos : 0 < (1 - t0) / (1 - s0) := div_pos (by linarith) (by linarith)
  filter_upwards [h0.eventually (gt_mem_nhds hpos)] with n hn
  exact ⟨hn.le, (div_lt_one (by linarith)).2 (by linarith)⟩

/-- The bulk `|lemE z0_n| ≤ 2 - 1/10`. -/
theorem bulk_z0' (n : ℕ) : |STflowE z0 n| ≤ 2 - 1 / 10 :=
  (lemma28_quant (z := z0 n) (κ := 1 / 10) (by norm_num) (z0_im_pos n) (z0_im_le_one n)
    (z0_locDomain n).1).1

/-- `S1Std` at `sz0` on any constant window `0 ≤ s_0 < t_0 < 1` (`τ = 1/20`, `𝔠_d = 1/100`):
the window `[1/16, 3/4]` has `s < 1/2 ≤ u`, the window `[1/2, 3/4]` has `1/2 ≤ s`. -/
theorem s1Std_sz0_const {s0 t0 : ℝ} (hs0 : 0 ≤ s0) (hst : s0 < t0) (ht : t0 < 1) :
    S1Std sz0 (1 / 10) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (STflowE z0)
      (fun _ => s0) (fun _ => t0) := by
  refine ⟨by norm_num, bulk_z0', by norm_num, by norm_num, by norm_num, by norm_num, le_rfl,
    fun _ => hs0, fun _ => hst.le, fun _ => ht, sz0_tendsto, sz0_admissible.2.2.2.1,
    sz0_admissible.2.2.2.2, s1Setup_conStInd_const hst ht (by norm_num), ?_⟩
  have h1 : Tendsto (fun n : ℕ => ((sz0.size n : ℕ) : ℝ) ^ (-((19 : ℝ) / 20))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp sz0_tendsto
  filter_upwards [h1.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - t0))] with n hn
  have : (-1 + (1 / 10 : ℝ) / 2) = -((19 : ℝ) / 20) := by norm_num
  rw [this]
  exact hn.le

/-! ### The loop family at `sz0` -/

/-- **Instance of `s1_loop_det`** (`d = 3`, `L = 4`, `W = 32`, `E = 1/2`, `u = 1/4`, `k = 2`, the
Hermitian matrix `H_u(ω)` of the flow at every sample `ω`): `c₁ = √2/2 ≤ Im m(1/2)`. -/
example (ω : sz0.SeqΩ) :
    ‖loopFine 3 (sz0.L 0) (sz0.W 0) (sz0.seqHflow 0 (1 / 4) ω) (zt (1 / 2) (1 / 4))
        ![true, false] ![0, 0]‖ ≤
      (2 / (Real.sqrt (2 * 1) / 2)) ^ 2 * ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹) ^ (2 - 1) :=
  s1_loop_det (d := 3) (c₁ := Real.sqrt (2 * 1) / 2)
    (by positivity)
    (s1_bulk (κ := 1) one_pos
      (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num)).2 (by norm_num) _
    (Sizes.seqHflow_isHermitian sz0 0 _ ω) (k := 2) (by norm_num) _ _

/-- **Instance of `s1T1`**: `t₁ = max(s, 1/2)` is `1/2` for `s ≡ 1/16` and `3/4` for `s ≡ 3/4`. -/
example : s1T1 (fun _ => (1 : ℝ) / 16) 0 = 1 / 2 ∧ s1T1 (fun _ => (3 : ℝ) / 4) 0 = 3 / 4 := by
  constructor <;> simp only [s1T1] <;> norm_num

/-- **Instance of `s1_Kbound_seq`** (`STKbound`, the `ML:Kbound` pin of the KL gate, stays a
hypothesis). -/
example (hK : STKbound sz0 (STflowE z0)) (k : ℕ) (hk : 1 ≤ k) :
    sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p _ => ‖STKloop sz0 n (STflowE z0 n) (sInst n) p.1 p.2‖)
      (fun n _ _ => (sz0.Bctl n (sInst n)) ^ (k - 1)) :=
  s1_Kbound_seq s1Std_sz0 hK hk

/-- **Instances of `s1_h55`** at the windows `[0, 1/16]` (`s < 1/2`) and `[1/2, 3/4]`
(`1/2 ≤ s`); `STLK` (`(Eq:L-KGt)`) and `STKbound` are other gates' pins. -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hK : STKbound sz0 (STflowE z0)) :
    S1H55 sz0 (STflowE z0) sInst := s1_h55 s1Std_sz0 hLK hK
example (hLK : STLK sz0 (STflowE z0) (fun _ => 1 / 2)) (hK : STKbound sz0 (STflowE z0)) :
    S1H55 sz0 (STflowE z0) (fun _ => 1 / 2) :=
  s1_h55 (s1Std_sz0_const (s0 := 1 / 2) (t0 := 3 / 4) (by norm_num) (by norm_num) (by norm_num))
    hLK hK

/-- **Instance of `s1_LI`**, window `[0, 1/16]`, `u ≡ 1/32 < 1/2` (the deterministic branch). -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hK : STKbound sz0 (STflowE z0)) (k : ℕ)
    (hk : 1 ≤ k) :
    sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p ω => sz0.STomegaC n (STflowE z0 n) (1 / 32) 2 ω *
        ‖Sizes.Lloop sz0 n (STflowE z0 n) (1 / 32) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - sInst n) / (1 - 1 / 32)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1)) :=
  s1_LI s1Std_sz0 (s1_h55 s1Std_sz0 hLK hK) (fun _ => 1 / 32)
    (fun n => ⟨by simp [sInst], by simp only [tInst]; norm_num⟩) hk

/-- **Instance of `s1_LI`**, window `[1/16, 3/4]`, `u ≡ 5/8 ≥ 1/2` (the branch through `conArg`,
`s < 1/2`: `t₁ = 1/2`). -/
example (hLK : STLK sz0 (STflowE z0) (fun _ => 1 / 16)) (hK : STKbound sz0 (STflowE z0))
    (k : ℕ) (hk : 1 ≤ k) :
    sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p ω => sz0.STomegaC n (STflowE z0 n) (5 / 8) 2 ω *
        ‖Sizes.Lloop sz0 n (STflowE z0 n) (5 / 8) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - 1 / 16) / (1 - 5 / 8)) ^ (k - 1) * (sz0.Bctl n (1 / 16)) ^ (k - 1)) :=
  have h := s1Std_sz0_const (s0 := 1 / 16) (t0 := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
  s1_LI h (s1_h55 h hLK hK) (fun _ => 5 / 8) (fun n => ⟨by norm_num, by norm_num⟩) hk

/-- **Instance of `s1_LI`**, window `[1/2, 3/4]`, `u ≡ 5/8` (`s ≥ 1/2`: `t₁ = s`). -/
example (hLK : STLK sz0 (STflowE z0) (fun _ => 1 / 2)) (hK : STKbound sz0 (STflowE z0))
    (k : ℕ) (hk : 1 ≤ k) :
    sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
      (fun n p ω => sz0.STomegaC n (STflowE z0 n) (5 / 8) 2 ω *
        ‖Sizes.Lloop sz0 n (STflowE z0 n) (5 / 8) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - 1 / 2) / (1 - 5 / 8)) ^ (k - 1) * (sz0.Bctl n (1 / 2)) ^ (k - 1)) :=
  have h := s1Std_sz0_const (s0 := 1 / 2) (t0 := 3 / 4) (by norm_num) (by norm_num) (by norm_num)
  s1_LI h (s1_h55 h hLK hK) (fun _ => 5 / 8) (fun n => ⟨by norm_num, by norm_num⟩) hk

/-! ### The lattice ball, `‖G_u - m‖_max` and the weak-law step at `sz0` -/

/-- **Instance of `s1_near_card`** (`d = 3`, `L = 4`): at most `3^3 = 27` near blocks; the count is
`27` (the `L^∞` ball has `27` points, not the `7` of the `ℓ¹` ball). -/
example (a : Zd 3 4) :
    ((Finset.univ.filter (fun a' : Zd 3 4 => zdistInf 3 4 (a' - a) ≤ 1)).card : ℝ) ≤ 3 ^ 3 :=
  s1_near_card a
example : (Finset.univ.filter (fun a' : Zd 3 4 => zdistInf 3 4 (a' - 0) ≤ 1)).card = 27 := by
  decide

theorem seqHflow_zero_sz0 (n : ℕ) (ω : sz0.SeqΩ) : sz0.seqHflow n 0 ω = 0 := by
  simp [Sizes.seqHflow]

theorem hE_half : |(1 / 2 : ℝ)| ≤ 2 := by
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num

/-- `‖G_0 - m‖_max = 0`: at `u = 0` the flow matrix is `0` and `G_0 = m I`. -/
theorem s1xM_time_zero_sz0 (ω : sz0.SeqΩ) :
    s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) 0 (sz0.seqHflow 0 0 ω) ≤ 0 := by
  refine s1xM_le fun i j => ?_
  rw [seqHflow_zero_sz0]
  exact (Green.llErrMat_time_zero hE_half i j).le

example (ω : sz0.SeqΩ) (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    Green.llErrMat 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) i j ≤
      s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) := s1xM_ge _ _ _ i j
example (ω : sz0.SeqΩ) : 0 ≤ s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) :=
  s1xM_nonneg _ _ _
example (ω : sz0.SeqΩ) (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    Green.llErrMat 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) i j =
      ‖(sz0.seqHflow 0 (1 / 16) ω - zt (1 / 2) (1 / 16) •
          (1 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))⁻¹ i j -
        (if i = j then mE (1 / 2) else 0)‖ := s1_llErrMat_eq _ _ _ i j
example (ω : sz0.SeqΩ) (i j : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖Gres (sz0.seqHflow 0 (1 / 16) ω) (zt (1 / 2) (1 / 16)) true i j‖ ≤
      1 + s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) :=
  s1_gMax_le hE_half _ i j
example (ω : sz0.SeqΩ) :
    s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) ≤
      s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) + 0 :=
  s1xM_le_add (fun i j => by simp)
example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖sz0.STGM 0 (1 / 2) (1 / 16) ω x y‖ =
      Green.llErrMat 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) x y :=
  s1_STGM_norm sz0 0 _ _ ω x y

/-- **Instances of `s1_omegaC_eq_one`, `s1_indMax_eq_one`** at `u = 0`, where `G_0 = m I`. -/
example (ω : sz0.SeqΩ) : sz0.STomegaC 0 (1 / 2) 0 2 ω = 1 :=
  s1_omegaC_eq_one sz0 0 ω hE_half ((s1xM_time_zero_sz0 ω).trans (by norm_num))
example (ω : sz0.SeqΩ) : sz0.STindMax 0 (1 / 2) 0 (1 / 10) ω = 1 :=
  s1_indMax_eq_one sz0 0 ω ((s1xM_time_zero_sz0 ω).trans (by norm_num))

/-- **Instance of `s1_gexRHS_le`** (`n = 0`, `E = 1/2`, `u = 1/16`, every sample `ω`, every pair of
blocks): the envelope `|𝓛^{(2)}| ≤ η⁻²` (`Sizes.norm_Lloop_le`) gives `B = η⁻²`. -/
example (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    sz0.STgexRHS 0 (1 / 2) (1 / 16) ω a b ≤
      2 * 9 ^ 3 * (etaT (1 / 2) (1 / 16))⁻¹ ^ 2 + (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ :=
  s1_gexRHS_le sz0 0 (1 / 2) (1 / 16) _ ω
    (fun σ b => Sizes.norm_Lloop_le sz0 0 (E := 1 / 2) (t := 1 / 16)
      (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num) (k := 1) σ b ω) a b

private theorem maxLoop2_nonneg (n : ℕ) (E u : ℝ) (ω : sz0.SeqΩ) : 0 ≤ sz0.STmaxLoop2 n E u ω :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : Zd 3 (sz0.L n) × Zd 3 (sz0.L n) =>
    ‖Sizes.Lloop sz0 n E u ![false, true] ![p.1, p.2] ω‖) (Finset.mem_univ ((0, 0))))

private theorem gexRHS_nonneg (n : ℕ) (E u : ℝ) (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L n)) :
    0 ≤ sz0.STgexRHS n E u ω a b := by
  unfold Sizes.STgexRHS
  refine add_nonneg (Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun a' _ =>
    Finset.sum_nonneg fun b' _ => norm_nonneg _) (mul_nonneg (by positivity) ?_)
  split_ifs <;> norm_num

/-- **Instance of `s1_wl_det` at `u = 0`, no premise left**: `n = 0` (`L = 4`, `W = 32`),
`E = 1/2`, `c' = 1/10`, `a = 0`, `N^τ = 1`, `g = η⁻² + 1`; at `u = 0` the matrix is `0` and
`G_0 = m I`, so the premises on the sample (`‖G_u - m‖_max ≤ 2a`, `STGiiGEX`, `STGijGEX`, the loop
bound) are all proved. -/
example (ω : sz0.SeqΩ) :
    ∀ i j, ‖sz0.STGM 0 (1 / 2) 0 ω i j‖ ^ 2 ≤
      (2 * 9 ^ 3 + 1) * (1 : ℝ) ^ 2 * ((etaT (1 / 2) 0)⁻¹ ^ 2 + 1) := by
  have hx := (s1xM_time_zero_sz0 ω).trans (by norm_num : (0 : ℝ) ≤ 2 * 0)
  have hzero : ∀ i j, ‖sz0.STGM 0 (1 / 2) 0 ω i j‖ = 0 := fun i j => by
    rw [s1_STGM_norm, seqHflow_zero_sz0]; exact Green.llErrMat_time_zero hE_half i j
  have hom2 : sz0.STomegaC 0 (1 / 2) 0 2 ω = 1 :=
    s1_omegaC_eq_one sz0 0 ω hE_half ((s1xM_time_zero_sz0 ω).trans (by norm_num))
  have hW1 : (1 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz0 0
  have hg : 0 ≤ (etaT (1 / 2) 0)⁻¹ ^ 2 + 1 := by
    have := sq_nonneg ((etaT (1 / 2) 0)⁻¹); linarith
  refine s1_wl_det sz0 0 ω (E := 1 / 2) (u := 0) (a := 0) (c' := 1 / 10)
    (g := (etaT (1 / 2) 0)⁻¹ ^ 2 + 1) (Nτ := 1) hE_half (by norm_num)
    hx (by rw [mul_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _) le_rfl hg
    ?_ ?_ ?_ ?_
  · exact (inv_le_one_of_one_le₀ (one_le_pow₀ hW1)).trans (by nlinarith [sq_nonneg ((etaT (1 / 2) 0)⁻¹)])
  · intro σ b
    rw [hom2, one_mul, one_mul]
    exact (Sizes.norm_Lloop_le sz0 0 (E := 1 / 2) (t := 0)
      (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num) (k := 1) σ b ω).trans
      (by linarith)
  · intro p
    rw [hzero, one_mul]
    simpa using maxLoop2_nonneg 0 (1 / 2) 0 ω
  · intro p
    have h0 : ‖Sizes.Gt sz0 0 (1 / 2) 0 true ω p.1.1 p.1.2‖ = 0 := by
      have := hzero p.1.1 p.1.2
      unfold Sizes.STGM at this
      simpa [p.2] using this
    rw [h0]
    simpa using gexRHS_nonneg 0 (1 / 2) 0 ω (sz0.STblk 0 p.1.1) (sz0.STblk 0 p.1.2)

/-- **Instance of `s1_wl_det` at `u = 1/16`** (a nonzero time): the same deterministic data
(`E = 1/2`, `c' = 1/10`, `N^τ = 1`, `g = η⁻² + 1`, `a = W^{-c'}/2`, the loop bound proved by the
envelope); the event premise `‖G_u - m‖_max ≤ 2a` and the two pins `STGiiGEX`, `STGijGEX` at `ω`
(other gates) stay hypotheses. -/
example (ω : sz0.SeqΩ)
    (hx : s1xM 3 (sz0.L 0) (sz0.W 0) (1 / 2) (1 / 16) (sz0.seqHflow 0 (1 / 16) ω) ≤
      2 * (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) / 2))
    (hii : ∀ p : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0),
      sz0.STindMax 0 (1 / 2) (1 / 16) (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) ω *
          ‖sz0.STGM 0 (1 / 2) (1 / 16) ω p.1 p.2‖ ^ 2 ≤
        1 * sz0.STmaxLoop2 0 (1 / 2) (1 / 16) ω)
    (hij : ∀ p : {p : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0) // p.1 ≠ p.2},
      sz0.STindMax 0 (1 / 2) (1 / 16) (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) ω *
          ‖Sizes.Gt sz0 0 (1 / 2) (1 / 16) true ω p.1.1 p.1.2‖ ^ 2 ≤
        1 * sz0.STgexRHS 0 (1 / 2) (1 / 16) ω (sz0.STblk 0 p.1.1) (sz0.STblk 0 p.1.2)) :
    ∀ i j, ‖sz0.STGM 0 (1 / 2) (1 / 16) ω i j‖ ^ 2 ≤
      (2 * 9 ^ 3 + 1) * (1 : ℝ) ^ 2 * ((etaT (1 / 2) (1 / 16))⁻¹ ^ 2 + 1) := by
  have hW1 : (1 : ℝ) ≤ ((sz0.W 0 : ℕ) : ℝ) := by exact_mod_cast s1_one_le_W sz0 0
  have hWc : ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hW1 (by norm_num)
  have hom2 : sz0.STomegaC 0 (1 / 2) (1 / 16) 2 ω = 1 :=
    s1_omegaC_eq_one sz0 0 ω hE_half (by linarith)
  have hg : 0 ≤ (etaT (1 / 2) (1 / 16))⁻¹ ^ 2 + 1 := by
    have := sq_nonneg ((etaT (1 / 2) (1 / 16))⁻¹); linarith
  refine s1_wl_det sz0 0 ω (E := 1 / 2) (u := 1 / 16) (c' := 1 / 10)
    (a := ((sz0.W 0 : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) / 2) (g := (etaT (1 / 2) (1 / 16))⁻¹ ^ 2 + 1)
    (Nτ := 1) hE_half (by norm_num) hx (by linarith) le_rfl hg ?_ ?_ hii hij
  · exact (inv_le_one_of_one_le₀ (one_le_pow₀ hW1)).trans (by nlinarith [sq_nonneg ((etaT (1 / 2) (1 / 16))⁻¹)])
  · intro σ b
    rw [hom2, one_mul, one_mul]
    exact (Sizes.norm_Lloop_le sz0 0 (E := 1 / 2) (t := 1 / 16)
      (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; norm_num) (by norm_num) (k := 1) σ b ω).trans
      (by linarith)

/-! ### The generic helpers and the `≺`-calculus lemmas at `sz0` -/

/-- **Instance of `s1_stochDom_unit`**: per time over `Unit` is uniform (`Xi ≺ Ze`). -/
example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ze :=
  s1_stochDom_unit PerTimeCalcInst.pt_Xi_Ze

/-- **Instance of `s1_highProb_of_pt` and `s1_pt_of_highProb`** (`#(Fin 2) = 2 ≤ N^1`): the
per-time `Xi ≺ Ze` over `Fin 2` gives the `w.h.p.` events for every `τ > 0`, and these give back the
per-time statement. -/
example : ∀ᶠ l : ℕ in atTop, (Fintype.card (Fin 2) : ℝ) ≤ ((sz0.size l : ℕ) : ℝ) ^ (1 : ℝ) := by
  filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
  simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn)
example : HighProbAt (seqP sz0) sz0.size
    (fun l => {ω | ∀ _u : Fin 2, Xi l () ω ≤ ((sz0.size l : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze l () ω}) :=
  s1_highProb_of_pt (U := fun _ => Fin 2) (C := 1) zero_le_one
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    precPT_Xi_Ze (by norm_num : (0 : ℝ) < 1 / 10)
example : PerTimeDomAt (seqP sz0) sz0.size (U := fun _ => Fin 2) (fun n _ ω => Xi n () ω)
    (fun n _ ω => Ze n () ω) :=
  s1_pt_of_highProb fun τ hτ => s1_highProb_of_pt (U := fun _ => Fin 2) (C := 1) zero_le_one
    (by
      filter_upwards [tendsto_sz0_size.eventually (eventually_ge_atTop 2)] with n hn
      simpa using (show (2 : ℝ) ≤ (sz0.size n : ℝ) by exact_mod_cast hn))
    precPT_Xi_Ze hτ

/-- **Instance of `StochDomAt.of_subset_whp`** (DECISIONS §26): `Xi ≺ Ch` from `Xi ≺ Ze` and the
good event `univ` (`Ze ≤ Ch`, so `bad(Xi, Ch) ⊆ bad(Xi, Ze) ∪ univᶜ`). -/
example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi Ch :=
  StochDomAt.of_subset_whp tendsto_sz0_size (f := Xi) (g := Ze) prec_Xi_Ze
    (highProbAt_univ (seqP sz0) sz0.size) fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun l ω ⟨u, hu⟩ => Or.inl ⟨u,
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (by unfold Ze Ch; linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩⟩

/-- **Instance of `StochDomAt.of_subset_compl`**: on the `w.h.p.` event
`{∀ u, Xi ≤ N^{1/10} Ze}` (`whp_Xi`), the failure event of `Xi ≺ N^{1/10} Ze` is empty. -/
example : StochDomAt (seqP sz0) sz0.size (U := fun _ => Unit) Xi
    (fun n u ω => ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze n u ω) :=
  StochDomAt.of_subset_compl whp_Xi fun τ hτ => by
    filter_upwards [Eventually.of_forall (sz0.one_le_size)] with l hl ω ⟨u, hu⟩ hΞ
    have h1 : (1 : ℝ) ≤ ((sz0.size l : ℕ) : ℝ) ^ τ :=
      Real.one_le_rpow (by exact_mod_cast hl) hτ.le
    have h2 := hΞ u
    have h3 : 0 ≤ ((sz0.size l : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Ze l u ω :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Ze_nonneg l u ω)
    nlinarith

/-- **Instance of `s1_omegaC_le_one`** (`n = 0`, every sample). -/
example (ω : sz0.SeqΩ) : sz0.STomegaC 0 (1 / 2) (1 / 16) 2 ω ≤ 1 :=
  s1_omegaC_le_one (sz := sz0) 0 (1 / 2) (1 / 16) 2 ω

/-- **DECISIONS §29 (1): `0 ≤ u` cannot be dropped from `s1_Wd_le_Bctl`** (hence from `s1_F8`,
`s1_loop_det`'s consumers): at `n = 0` (`L = 4`, `W = 32`, `ilambda = 1/64`) and `u = -10^6` the
volume factor `W^{-3}` exceeds `(ilambda² + 1) W^{-3} B_{u,0}` (`B` is `~10^{-6}`). -/
example : ¬ ((((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ ≤ (sz0.lam 0 ^ 2 + 1) * sz0.Bctl 0 (-(10 : ℝ) ^ 6)) := by
  have hW : ((sz0.W 0 : ℕ) : ℝ) = 32 := by norm_num [sz0]
  have hL : ((sz0.L 0 : ℕ) : ℝ) = 4 := by norm_num [sz0]
  have hl : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
  have ha : |1 - (-(10 : ℝ) ^ 6)| = 1000001 := by rw [abs_of_pos] <;> norm_num
  unfold Sizes.Bctl Bparam
  rw [hW, hL, hl, ha]
  norm_num

/-! ### The pin `Step1TargetV3` -/

/-- **Instance of `Step1TargetV3`** (the pin, proved by S1-36) applied at the data of the file:
`d = 3`, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠_d = 1/100`, `s ≡ 0 < t ≡ 1/16 ≤ lemT z_n`;
`STConStInd` is discharged (`conStInd_inst`); `STKbound`, `STLK`, `STLocalMax` (the pins of the
KL, loop and local-law gates) and `STGbEXPii`, `STGbEXPij` stay hypotheses.  Both conjuncts of
`STStep1` are produced. -/
example (h : Step1TargetV3 3) (hii : STGbEXPii 3) (hij : STGbEXPij 3)
    (hK : STKbound sz0 (STflowE z0)) (hLK : STLK sz0 (STflowE z0) sInst)
    (hLoc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  stStep1_of_target h hii hij (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 100) (by norm_num) le_rfl (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    zero_le_lemT (fun n => by simp only [sInst, tInst]; norm_num) sixteenth_le_lemT hK hLK hLoc
    (conStInd_inst (by norm_num))

end RBM.Ind.Step1SetupInst

end
