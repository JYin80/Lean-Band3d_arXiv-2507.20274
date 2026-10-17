/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.LemDecCalELip
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.NQGood1Gen
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.Step6KitGen

/-!
# The regime-generic self-absorption bootstrap over the carrier family (U3s4 row a, file 1; ticket T2505)

Generic form of `Induction/QtNonzeroBoot.lean` §1-§4 (not edited) over a carrier `Cm : Step2Mat sz` and a law `μ`, namespace `RBM.BA`, no `BA/*`
import.  Paper: arXiv:2507.20274, `lem:STOeq_Qt` (`3_5:1362-1378`, `(am;asoi222)` `3_5:1366`), the bound before "solving which" `3_5:1916-1930`.
No new mathematics (`7_8:1841`).

* **Target 1** `STXiRoundgL'` (= `T2505_XiRoundgL'`, binding) and the bridge `bandFM_STXiRound'`.
* **Target 2** `stBoot_roundsg` (the abstract finite bootstrap at a law), `stXiBootgL'_of_round` (one carrier: the crude start from `StepDecompGen_LoopForm`,
  `‖m‖ ≤ 1`, `STKboundgL` and the Hermitian event of `LemDecCalELipG_FlowMod`; the contraction from `DecayGen_Spec` and the range condition),
  `stXiBootRgL'_of_round` (= `T2505_XiBootROfRound` at the bundle `QtBootGen_Hyp`, conclusion binding; the regime `R` is a parameter).
* The two family texts read by the hypotheses: `QtBootGen_FlowModFam` (= `T2505_FlowModFam`, the merged U4s3 text `DuhamelII:726-727`, no new class)
  and the bundle `QtBootGen_Hyp` fixed at the 1a of row a (guarded probability law: Amend of the 1b, see the report).

The model-free private helpers of `QtNonzeroBoot` (the contraction, the `STbootRHS` facts) are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private qtBoot_Y qtBoot_c qtBoot_c_pos qtBoot_contraction qtBoot_bootRHS_update qtBoot_bootRHS_one_le from RBM3D.Induction.QtNonzeroBoot

open private NQEndFlowGen_prec_of_le_right from RBM3D.Chain.NQEndFlowGen

open private nqEnd_rangeCond_mono from RBM3D.Induction.NQEndLin

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1: the round text -/

section Texts

/-- **Target 1, `STXiRoundgL'`** (= `T2505_XiRoundgL'`, binding; band `STXiRound'`, `QtNonzeroBoot.lean:92`): `STXiBootgL'` with `m ≤ n_` in the
`XLK` hypotheses and the summand `B_u^{1/6} XLK n_ u`; the merged `STXiRoundPTgL''` with `PrecPTL` replaced with `PrecL`. -/
def STXiRoundgL' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)

end Texts

/-! ## 2. The family texts of the hypotheses -/

section Hyps

/-- **Family row 16** (= `T2505_FlowModFam`; the merged U4s3 hypothesis text `hFM`, `DuhamelII.lean:726-727`, copied; no new class): the flow modulus
of `𝓛` over the family, `∃ c` after `(κ, ε, 𝔡)` and before `(sz, 𝔠, z)`. -/
def QtBootGen_FlowModFam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (sz : Sizes d) (𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → LemDecCalELipG_FlowMod (mkM sz z) (law sz) c

/-- **The bundle `Hyp` of `T2505_XiBootROfRound`** (fixed at the 1a of row a): the flow facts `Step2EventsGen_Flow` (admissibility, `T0 < 1`); the law is a
probability measure at every flow (guarded: the 1b form of (H2)); at every flow with `0 < κ` the loop form with some energy, `‖m‖ ≤ 1` and the spectral data
`DecayGen_Spec`; the range condition of `T0` (`∃ τ > 0`); and the flow modulus of `𝓛` (`QtBootGen_FlowModFam`, read for the Hermitian event). -/
def QtBootGen_Hyp (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  Step2EventsGen_Flow d Flow T0 ∧
  (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → IsProbabilityMeasure (law sz)) ∧
  (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
    (∃ E : ℕ → ℝ, StepDecompGen_LoopForm (mkM sz z) E) ∧ (∀ n, ‖(mkM sz z).m n‖ ≤ 1) ∧
      ∃ κm : ℝ, DecayGen_Spec (mkM sz z).toFlowFM κm) ∧
  (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
    ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z)) ∧
  QtBootGen_FlowModFam d law Flow mkM

end Hyps

/-! ## 3. The abstract self-absorption bootstrap at a law -/

section Boot

variable {d : ℕ}

/-- **The abstract self-absorption bootstrap at a law** (band `stBoot_rounds`, `QtNonzeroBoot.lean:136`; paper `3_5:1923-1930`, "solving which"): from a crude
start `ξ ≺ N^{C₀}` and a round `ξ ≺ Y ⇒ ξ ≺ N^{-c} Y + R` (every deterministic `Y ≥ 1` of the endpoint `π q`), `ξ ≺ R` after `⌈C₀/c⌉ + 1` rounds, over `PrecL sz μ`.
The round count depends on `C₀, c` only, never on `n`. -/
theorem stBoot_roundsg (sz : Sizes d) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto) {U : ℕ → Type} (π : ∀ n, U n → ℝ)
    (ξ : ∀ n, U n → sz.SeqΩ → ℝ) (R : ℕ → ℝ → ℝ) (c C₀ : ℝ) (hc : 0 < c) (hC₀ : 0 ≤ C₀)
    (hR : ∀ n u, 1 ≤ R n u)
    (h0 : PrecL sz μ (U := U) ξ (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ C₀))
    (hround : ∀ Y : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ Y n u) →
      PrecL sz μ (U := U) ξ (fun n q _ => Y n (π n q)) →
      PrecL sz μ (U := U) ξ (fun n q _ => ((sz.size n : ℕ) : ℝ) ^ (-c) * Y n (π n q) + R n (π n q))) :
    PrecL sz μ (U := U) ξ (fun n q _ => R n (π n q)) := by
  have hN1 : ∀ n, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hNc : ∀ n, ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
  have hNc0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := fun n => Real.rpow_nonneg (by linarith [hN1 n]) _
  -- (a) `Y_j ≥ 1`
  have hY1 : ∀ j n u, 1 ≤ qtBoot_Y sz c C₀ R j n u := by
    intro j
    induction j with
    | zero => intro n u; exact Real.one_le_rpow (hN1 n) hC₀
    | succ j ih =>
      intro n u
      have := mul_nonneg (hNc0 n) (zero_le_one.trans (ih n u))
      have := hR n u
      change 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u + R n u
      linarith
  -- (b) `ξ ≺ Y_j`
  have hYp : ∀ j, PrecL sz μ (U := U) ξ (fun n q _ => qtBoot_Y sz c C₀ R j n (π n q)) := by
    intro j
    induction j with
    | zero => exact h0
    | succ j ih => exact hround (qtBoot_Y sz c C₀ R j) (hY1 j) ih
  -- (c) `Y_j ≤ N^{C₀ - j c} + j R`
  have hYb : ∀ j n u, qtBoot_Y sz c C₀ R j n u ≤
      ((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) + j * R n u := by
    intro j
    induction j with
    | zero => intro n u; simp [qtBoot_Y]
    | succ j ih =>
      intro n u
      have hR0 : 0 ≤ R n u := zero_le_one.trans (hR n u)
      have hpow : ((sz.size n : ℕ) : ℝ) ^ (-c) * ((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) =
          ((sz.size n : ℕ) : ℝ) ^ (C₀ - ((j + 1 : ℕ) : ℝ) * c) := by
        rw [← Real.rpow_add (by linarith [hN1 n])]
        congr 1
        push_cast
        ring
      have h1 : ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u ≤
          ((sz.size n : ℕ) : ℝ) ^ (-c) * (((sz.size n : ℕ) : ℝ) ^ (C₀ - j * c) + j * R n u) :=
        mul_le_mul_of_nonneg_left (ih n u) (hNc0 n)
      have h2 : ((sz.size n : ℕ) : ℝ) ^ (-c) * ((j : ℝ) * R n u) ≤ (j : ℝ) * R n u := by
        have := mul_le_mul_of_nonneg_right (hNc n) (mul_nonneg (Nat.cast_nonneg j) hR0)
        linarith
      change ((sz.size n : ℕ) : ℝ) ^ (-c) * qtBoot_Y sz c C₀ R j n u + R n u ≤
        ((sz.size n : ℕ) : ℝ) ^ (C₀ - ((j + 1 : ℕ) : ℝ) * c) + ((j + 1 : ℕ) : ℝ) * R n u
      rw [← hpow]
      push_cast
      nlinarith
  -- (d) at `r = ⌈C₀/c⌉ + 1`
  set r : ℕ := ⌈C₀ / c⌉₊ + 1 with hr
  have hrc : C₀ - (r : ℝ) * c ≤ -c := by
    have h1 : C₀ / c ≤ (⌈C₀ / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : C₀ ≤ (⌈C₀ / c⌉₊ : ℝ) * c := by
      have := (div_le_iff₀ hc).1 h1
      linarith
    rw [hr]
    push_cast
    nlinarith
  have hYr : ∀ n u, qtBoot_Y sz c C₀ R r n u ≤ ((r : ℝ) + 1) * R n u := by
    intro n u
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (C₀ - (r : ℝ) * c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (hN1 n) (by linarith)
    have h2 := hYb r n u
    have h3 := hR n u
    nlinarith
  -- (e) the constant `r + 1` is absorbed
  have hrp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hmain : PrecL sz μ (U := U) ξ (fun n q _ => ((r : ℝ) + 1) * R n (π n q)) :=
    NQEndFlowGen_prec_of_le_right (hYp r) fun n q ω => hYr n (π n q)
  have hmain' := StochDomAt.const_mul_right (sz.tendsto_size hsz) (inv_pos.2 hrp)
    (fun n q ω => mul_nonneg hrp.le (zero_le_one.trans (hR n (π n q)))) hmain
  refine (show (fun n (q : U n) (ω : sz.SeqΩ) => ((r : ℝ) + 1)⁻¹ * (((r : ℝ) + 1) * R n (π n q))) =
    fun n (q : U n) _ => R n (π n q) from ?_) ▸ hmain'
  funext n q ω
  field_simp

/-- A pointwise larger right side keeps `≺`, eventually in `n` (band `qtBoot_prec_of_le_ev`, over `PrecL`). -/
private theorem QtBootGen_prec_of_le_ev {sz : Sizes d} {μ : Measure sz.SeqΩ} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) : PrecL sz μ ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, hle.mono fun n hn ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(1 - u)⁻¹ ≤ N B_u` for `u < 1` (`W^{-d}B_{u,0} ≥ W^{-d}(L^d(1-u))⁻¹ = (N(1-u))⁻¹`; the size-level half of the band `expWII_inv_Neta_le`, `ExpWardII:303`). -/
private theorem QtBootGen_inv_one_sub_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) * sz.Bctl n u := by
  have h1 : 0 < 1 - u := by linarith
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hsize : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
    simp only [Sizes.size, Nat.cast_pow, Nat.cast_mul, mul_pow]
    rw [mul_assoc, mul_inv]
  have hB : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ sz.Bctl n u := by
    rw [hsize, RBM.Ind.ContinuityNet.cont_Bctl_eq sz n hu, mul_add]
    have h5 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - u))⁻¹ := by
      have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      have h6 : 0 ≤ sz.lam n ^ 2 + (1 - u) := by positivity
      positivity
    linarith
  calc (1 - u)⁻¹ = ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [mul_inv, mul_inv_cancel_left₀ hN.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left hB hN.le

/-- **The deterministic crude bound** (band `qtBoot_crude`, `QtNonzeroBoot.lean:337`, deterministic half): for a Hermitian `M`, `0 ≤ v < 1`, `B_v ≤ 1`, `‖𝒦^{(m)}_v‖ ≤ N`,
`m = n_`, and `N ≥ 2 + κm^{-n_}`: `Ξ̂^{(𝓛-𝒦)}_{v,n_}(M) ≤ N^{2 n_ + 1}`.  `η_v⁻¹ ≤ κm⁻¹ N` (`DecayGen_Spec`, `QtBootGen_inv_one_sub_le`, `B ≤ 1`), `B⁻¹ ≤ N`
(`cont_inv_size_le_Bctl`), and the Hermitian crude loop bound `STXiLKMg_crudeNg`. -/
private theorem QtBootGen_crude_det {sz : Sizes d} (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1)
    {κm : ℝ} (hκm : 0 < κm) (hIm : ∀ n, κm ≤ (Cm.m n).im) (hηeq : ∀ (n : ℕ) (t : ℝ), Cm.eta n t = (1 - t) * (Cm.m n).im)
    {n n_ : ℕ} (hn : 1 ≤ n_) (hN2 : 2 + κm⁻¹ ^ n_ ≤ ((sz.size n : ℕ) : ℝ))
    {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hM : M.IsHermitian) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hB1 : sz.Bctl n v ≤ 1) (hKN : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)), ‖Cm.K n v σ a‖ ≤ ((sz.size n : ℕ) : ℝ)) :
    STXiLKMg Cm n v n_ M ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hBpos : 0 < sz.Bctl n v := STBctl_pos sz n hv1
  have hμ0 : 0 < κm⁻¹ := inv_pos.2 hκm
  have hImpos : 0 < (Cm.m n).im := lt_of_lt_of_le hκm (hIm n)
  have hηpos : 0 < Cm.eta n v := by rw [hηeq]; exact mul_pos (by linarith) hImpos
  have hcr := STXiLKMg_crudeNg hL (hm n) hM hv0 hv1 hB1 hn (le_refl n_) hKN
  -- `η⁻¹ ≤ κm⁻¹ N`
  have hη : (Cm.eta n v)⁻¹ ≤ κm⁻¹ * ((sz.size n : ℕ) : ℝ) := by
    have h1 := QtBootGen_inv_one_sub_le sz n hv1
    rw [hηeq, mul_inv]
    calc (1 - v)⁻¹ * ((Cm.m n).im)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * sz.Bctl n v) * κm⁻¹ :=
          mul_le_mul h1 (inv_anti₀ hκm (hIm n)) (inv_nonneg.2 hImpos.le) (by positivity)
      _ ≤ (((sz.size n : ℕ) : ℝ) * 1) * κm⁻¹ := by gcongr
      _ = κm⁻¹ * ((sz.size n : ℕ) : ℝ) := by ring
  -- `B⁻¹ ≤ N`
  have hBinv : (sz.Bctl n v)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    have h1 := RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n hv0 hv1
    have h2 := inv_anti₀ (inv_pos.2 hN0) h1
    rwa [inv_inv] at h2
  have hηn : (Cm.eta n v)⁻¹ ^ n_ ≤ κm⁻¹ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hηpos.le) hη n_
  have hBn : 1 / (sz.Bctl n v) ^ n_ ≤ ((sz.size n : ℕ) : ℝ) ^ n_ := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hBpos.le) hBinv n_
  have hμn : 0 ≤ κm⁻¹ ^ n_ := pow_nonneg hμ0.le n_
  have hX1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := one_le_pow₀ hN1
  have hX2 : ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) :=
    pow_le_pow_right₀ hN1 (by omega)
  have hX3 : ((sz.size n : ℕ) : ℝ) ^ (n_) * ((sz.size n : ℕ) : ℝ) ^ (n_) = ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by
    rw [← pow_add]; congr 1; ring
  have hX4 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (n_) = ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) := by
    rw [pow_succ]; ring
  refine hcr.trans ?_
  have hnum : ((Cm.eta n v)⁻¹ ^ n_ + ((sz.size n : ℕ) : ℝ)) / (sz.Bctl n v) ^ n_ ≤
      (κm⁻¹ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ n_ := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul (by linarith) hBn (by positivity) (by positivity)
  have hexp : (κm⁻¹ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ n_ + ((sz.size n : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ n_ =
      κm⁻¹ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) + ((sz.size n : ℕ) : ℝ) ^ (n_ + 1) := by
    rw [← hX3, ← hX4]; ring
  have hpow : ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by
    rw [pow_succ]; ring
  have hX0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by positivity
  calc 1 + ((Cm.eta n v)⁻¹ ^ n_ + ((sz.size n : ℕ) : ℝ)) / (sz.Bctl n v) ^ n_
      ≤ 1 + (κm⁻¹ ^ n_ * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) + ((sz.size n : ℕ) : ℝ) ^ (n_ + 1)) := by
        rw [← hexp]; linarith
    _ ≤ (2 + κm⁻¹ ^ n_) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := by nlinarith
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * n_) := mul_le_mul_of_nonneg_right hN2 hX0
    _ = _ := hpow.symm

/-- **The crude start** (band `qtBoot_crude`; DECISIONS §62 (1); paper `3_5:1923-1926` supplies no a priori bound): for `n_ ≥ 1`,
`Ξ̂^{(𝓛-𝒦)}_{v,n_} ≺ N^{2 n_ + 1}` over the pairs, at a law `μ`.  `𝒦` is bounded by `N` through `stKbound_timeIccgL` (the pin `STKboundgL`) and `B ≤ 1`
(the contraction at the range exponent `τ`); the loop bound is the Hermitian one on the high-probability event `G` of the flow modulus (`LemDecCalELipG_FlowMod`,
first, third and fourth conjuncts); the failure event lies in `(G n)ᶜ`. -/
private theorem QtBootGen_crude {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {τ : ℝ} (hτ : 0 < τ) {c : ℝ} (hFM : LemDecCalELipG_FlowMod Cm μ c)
    (hK : STKboundgL Cm.toFlowFM μ) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hrange : sz.RangeCond τ t) {n_ : ℕ} (hn : 1 ≤ n_) :
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 n_ ω)
      (fun n _ _ => ((sz.size n : ℕ) : ℝ) ^ (((2 * n_ + 1 : ℕ) : ℝ))) := by
  obtain ⟨Hm, G, hLM, hG, hherm⟩ := lemDecCalELipG_flowMod_base hFM
  have hsize := hA.2.2.1
  have hcon := qtBoot_contraction sz hA (ε := 2 * τ) (by linarith) ht1 (by rwa [show 2 * τ / 2 = τ by ring])
  have hKb := stKbound_timeIccgL sz Cm.toFlowFM μ hsize hK s t hs (fun n => (hst n).le) ht1 n_ hn
  have hKdet := ((st6_prec_det_iffg sz μ inferInstance hsize _ _).1 hKb) 1 one_pos
  obtain ⟨hκm, hIm, hηeq⟩ := hspec
  intro τ' hτ' D hD
  filter_upwards [hG D hD, hcon, hKdet, hsize.eventually_ge_atTop (2 + κm⁻¹ ^ n_)] with n hGn hc hKn hN2
  refine le_trans (measure_mono ?_) hGn
  intro ω hω
  by_contra hωG
  have hωG' : ω ∈ G n := by simpa using hωG
  obtain ⟨q, hq⟩ := hω
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hv0 : 0 ≤ q.1.1 := (hs n).trans q.2.1
  have hvt : q.1.1 ≤ t n := q.2.2.1.trans q.2.2.2
  have hv1 : q.1.1 < 1 := hvt.trans_lt (ht1 n)
  have hB1 : sz.Bctl n q.1.1 ≤ 1 := (hc q.1.1 hv0 hvt).1
  have hBpos : 0 < sz.Bctl n q.1.1 := STBctl_pos sz n hv1
  -- `|𝒦| ≤ N`
  have hKN : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖Cm.K n q.1.1 σ a‖ ≤ ((sz.size n : ℕ) : ℝ) := by
    intro σ a
    have h1 := hKn (⟨q.1.1, q.2.1, hvt⟩, σ, a)
    have h2 : (sz.Bctl n q.1.1) ^ (n_ - 1) ≤ 1 := pow_le_one₀ hBpos.le hB1
    rw [Real.rpow_one] at h1
    have h3 : ((sz.size n : ℕ) : ℝ) * (sz.Bctl n q.1.1) ^ (n_ - 1) ≤ ((sz.size n : ℕ) : ℝ) := by
      calc ((sz.size n : ℕ) : ℝ) * (sz.Bctl n q.1.1) ^ (n_ - 1)
          ≤ ((sz.size n : ℕ) : ℝ) * 1 := mul_le_mul_of_nonneg_left h2 hN0.le
        _ = _ := mul_one _
    exact h1.trans h3
  have hHerm := (hherm n ω hωG' q.1.1 q.1.1 hv0 hv1.le hv0 hv1.le).1
  have hdet := QtBootGen_crude_det Cm hL hm hκm hIm hηeq hn hN2 hHerm hv0 hv1 hB1 hKN
  rw [STXiLKMg_Hf hLM] at hdet
  have hτ1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
  have hC : ((sz.size n : ℕ) : ℝ) ^ (((2 * n_ + 1 : ℕ) : ℝ)) = ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) :=
    Real.rpow_natCast _ _
  have hq' : ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.size n : ℕ) : ℝ) ^ (((2 * n_ + 1 : ℕ) : ℝ)) <
      STXiLKg Cm.toFlowFM n q.1.1 n_ ω := hq
  rw [hC] at hq'
  have : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * n_ + 1) := by positivity
  nlinarith

/-- **Target 2, `stXiBootgL'_of_round`** (band `stXiBoot'_of_round`, `QtNonzeroBoot.lean:522`; regime-free; DECISIONS §62 (1), (2), (4), §105 (1) O2; paper `3_5:1923-1930`):
the abstract bootstrap `stBoot_roundsg` with `ξ = Ξ̂^{(𝓛-𝒦)}_{v,n_}`, `π q = q.1.2`, `R n u = STbootRHS 1 (XL u) (XLK u) B_s n_ p` (`≥ 1`), `C₀ = 2 n_ + 1`
(`QtBootGen_crude`), `c = qtBoot_c 𝔠 𝔡 (2τ) = min (2 𝔡 𝔠) τ / 12` (`qtBoot_contraction` at the range exponent `τ` of the flow in place of the band's `ε/2`); the round
for a control `Y ≥ 1` is `STXiRoundgL'` at `XLK' := Y` in the slot `m = n_` (`STbootRHS` reads `XLK` at lengths `≤ n_ - 1` only, `qtBoot_bootRHS_update`) followed by
`B_u^{1/6} Y ≤ N^{-c} Y`.  No regime predicate, no `STConStInd`; `STKboundgL` enters the crude start only (paper-delta candidate `T2505a`). -/
theorem stXiBootgL'_of_round {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (hm : ∀ n, ‖Cm.m n‖ ≤ 1) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm)
    {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {τ : ℝ} (hτ : 0 < τ) {c : ℝ} (hFM : LemDecCalELipG_FlowMod Cm μ c)
    (hK : STKboundgL Cm.toFlowFM μ) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hrange : sz.RangeCond τ t) (hround : STXiRoundgL' Cm.toFlowFM μ s t) :
    STXiBootgL' Cm.toFlowFM μ s t := by
  have hsize := hA.2.2.1
  have hcon := qtBoot_contraction sz hA (ε := 2 * τ) (by linarith) ht1 (by rwa [show 2 * τ / 2 = τ by ring])
  have hc := qtBoot_c_pos hA.1 hA.2.1 (ε := 2 * τ) (by linarith)
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => STBctl_pos sz n ((hst n).trans (ht1 n))
  have hR1 : ∀ n u, 1 ≤ STbootRHS 1 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p := fun n u =>
    qtBoot_bootRHS_one_le (by omega) (fun m => hXL m n u) (fun m => zero_le_one.trans (hXLK m n u)) (hBs n).le
  refine stBoot_roundsg sz μ hsize (U := STPair s t) (fun n q => q.1.2)
    (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 n_ ω)
    (fun n u => STbootRHS 1 (fun m => XL m n u) (fun m => XLK m n u) (sz.Bctl n (s n)) n_ p)
    (qtBoot_c 𝔠 𝔡 (2 * τ)) (((2 * n_ + 1 : ℕ) : ℝ)) hc (Nat.cast_nonneg _) hR1
    (QtBootGen_crude Cm μ hL hm hspec hA hτ hFM hK hs hst ht1 hrange (by omega)) ?_
  intro Y hY1 hYp
  -- the round at `XLK' = Y` in the slot `n_`
  set XLK' : ℕ → ℕ → ℝ → ℝ := fun m n u => if m = n_ then Y n u else XLK m n u with hXLK'
  have hXLK'n : ∀ n u, XLK' n_ n u = Y n u := fun n u => by simp [hXLK']
  have hXLK'm : ∀ m, m ≠ n_ → ∀ n u, XLK' m n u = XLK m n u := fun m hm n u => by simp [hXLK', hm]
  have hXLK'1 : ∀ m n u, 1 ≤ XLK' m n u := by
    intro m n u
    by_cases hm : m = n_
    · rw [hm, hXLK'n]; exact hY1 n u
    · rw [hXLK'm m hm]; exact hXLK m n u
  have hXLK'p : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 m ω)
        (fun n q _ => XLK' m n q.1.2) := by
    intro m hm1 hmn
    by_cases hm : m = n_
    · rw [hm]
      simp only [hXLK'n]
      exact hYp
    · have h1 : m + 1 ≤ n_ := by omega
      simp only [hXLK'm m hm]
      exact hXLKp m hm1 h1
  have h := hround n_ p hn hp XL XLK' hXL hXLK'1 hXLp hXLK'p
  refine QtBootGen_prec_of_le_ev h ?_
  filter_upwards [hcon] with n hcn
  intro q ω
  have hu0 : 0 ≤ q.1.2 := (hs n).trans (q.2.1.trans q.2.2.1)
  have hcq := (hcn q.1.2 hu0 q.2.2.2).2
  have hupd : STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK' m n q.1.2) (sz.Bctl n (s n)) n_ p =
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p :=
    qtBoot_bootRHS_update (by norm_num) (fun m hm1 hm2 => hXLK'm m (by omega) n q.1.2)
  change (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK' n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK' m n q.1.2) (sz.Bctl n (s n)) n_ p ≤
    ((sz.size n : ℕ) : ℝ) ^ (-(qtBoot_c 𝔠 𝔡 (2 * τ))) * Y n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p
  rw [hXLK'n, hupd]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hcq (zero_le_one.trans (hY1 n q.1.2))) _

end Boot

/-! ## 4. The regime-generic bootstrap over a carrier family -/

/-- **Target 2, `stXiBootRgL'_of_round`** (= `T2505_XiBootROfRound` at `Hyp := QtBootGen_Hyp`, conclusion binding; band `stXiBootR_of_round`, `QtNonzeroBoot.lean:581`;
supervisor `2026-10-06-1356` O2): the round pin `STXiRoundgL'` over an ingredient setting `STIngRgL d R` of a carrier family gives `STXiBootgL'` over the same setting.  The
constant `𝔠_d` of the hypothesis is kept; the regime `R`, `STKboundgL`, `STKwardgL`, `STLKgL s`, `STConStInd`, `STStep2ConclgL` go to the round only (`STKboundgL` also to the crude
start).  The flow premises are the bundle `QtBootGen_Hyp` (guarded: `0 < κ`, `Flow`); the modulus `∃ c` of its last conjunct comes after `(κ, ε, 𝔡)` and before `(sz, 𝔠, z)`. -/
theorem stXiBootRgL'_of_round (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hH : QtBootGen_Hyp d law Flow mkM T0)
    (h : STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t)) :
    STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) := by
  obtain ⟨hFl, hProb, hLoop, hRange, hFM⟩ := hH
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨cH, hcH, hFMall⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨⟨E, hL⟩, hm, κm, hspec⟩ := hLoop sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨τ, hτ, hrange0⟩ := hRange sz κ ε 𝔠 𝔡 z hκ hε hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hrange : sz.RangeCond τ t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  have := hProb sz κ ε 𝔠 𝔡 z hκ hflow
  exact stXiBootgL'_of_round (mkM sz z) (law sz) hL hm hspec (hFl.1 sz κ ε 𝔠 𝔡 z hflow) hτ (hFMall sz 𝔠 z hflow) hK hs hst ht1 hrange
    (H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2)

/-! ## 5. The band reading of the bundle -/

section BandBundle

/-- The energy of a flow is in the bulk: `|E(z)| ≤ |Re z| ≤ 2 - κ` (`abs_lemE_le`; private copy of `QEndB1GenCheck.flow_abs_le`). -/
private theorem QtBootGen_flow_abs_le {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    |STflowE z n| ≤ 2 - κ :=
  (abs_lemE_le (ST_flow_im_pos sz hz n)).trans (hz.2 n).1

/-- **Family row 16 at the band family** (`seqP`, `STFlow`, `bandStep2Mat · (STflowE ·)`; every `d`): `c = 1`, `lemDecCalELipG_flowMod_band` (`Hm = seqHflow`, `G = contGood`). -/
theorem qtBootGen_flowModFam_band (d : ℕ) :
    QtBootGen_FlowModFam d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) :=
  fun κ ε 𝔡 hκ hε h𝔡 => ⟨1, zero_le_one, fun sz 𝔠 z hz =>
    lemDecCalELipG_flowMod_band sz (sz.tendsto_size hz.1.2.2.1) (STflowE z)⟩

/-- **The bundle `QtBootGen_Hyp` at the band family** (`seqP`, `STFlow`, `bandStep2Mat · (STflowE ·)`, `lemT`; every `d`): the flow facts are `Step2EventsGen_bandFlow`, the law is
`seqP` (a probability measure), the loop form is `stepDecompGen_loopForm_band` with `E = STflowE z`, `‖m‖ = ‖mE E‖ = 1` (`norm_mE`), the spectral data `DecayGen_bandSpec`
(`κm = √κ/2`), the range condition `ε/2` (`v3_premises_of_stFlow` at `t = lemT z`), and the flow modulus `qtBootGen_flowModFam_band` (`c = 1`). -/
theorem qtBootGen_hyp_band (d : ℕ) :
    QtBootGen_Hyp d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  refine ⟨Step2EventsGen_bandFlow d, fun sz _ _ _ _ _ _ _ => inferInstance, ?_, ?_, qtBootGen_flowModFam_band d⟩
  · intro sz κ ε 𝔠 𝔡 z hκ hz
    exact ⟨⟨STflowE z, stepDecompGen_loopForm_band sz _ fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith)⟩,
      fun n => (norm_mE (by linarith [QtBootGen_flow_abs_le hz n])).le,
      ⟨Real.sqrt κ / 2, DecayGen_bandSpec sz hκ (QtBootGen_flow_abs_le hz)⟩⟩
  · intro sz κ ε 𝔠 𝔡 z hκ hε hz
    exact ⟨ε / 2, half_pos hε, (Green.v3_premises_of_stFlow sz hκ hε hz (fun n => le_rfl)).2.2.2⟩

end BandBundle

/-! ## 6. Compiled nonempty instances (`d = 3`)

Data of the merged band instances (`Induction/Defs.lean:403-440`, `Induction/Step34Pins.lean:843-944`): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`,
`N = 2^21`), the flow `z0` (`z_n = 1/2 + i N_n^{-4/5}`, `flow_z0` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`), `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z0`, `STCaseI`: `sz0_caseI`; `(con_st_ind)`
for every `𝔠_d > 0`: `sz0_con`), `C_d = 1`.  What stays a hypothesis of an example is another gate's pin: the round pin `STXiRoundgL'` (proved in `Chain/QtXiRoundLiftGen`, the second
file of this row) and the stochastic premises `STLKgL s`, `STStep2ConclgL` of `STIngRgL` (`STKboundgL`, `STKwardgL` are theorems of the flow). -/

end RBM.BA

end
