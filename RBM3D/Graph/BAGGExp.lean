/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExpandW

/-!
# BA-L2c2a: the GG expansion `(B.20)` with the D402 coefficient (T2409)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:393-405` (cited `B:line`;
`GGGamma`, [yang2024Del, Lemma B.11]), with the corrected coefficient
`(W - 1)_{xβ} = (M⁺S⁺)_{xβ}` in the first two sums (paper delta D402; the printed `(B.20)`
has `S⁺_{xβ}` there and fails numerically).  The law is the block Anderson flow
`H_t = g₀ Ψ + √t V` with `S^{(B)}(0) = I`, i.e. `PF d L W 0` (DECISIONS §57 (3)).

## Contents (namespace `RBM.Graph`, private prefix `BAGGExp_`)

1. **The pin**, copied verbatim from the T2387 probe
   (`t/T2387:RBM3D/Probe/T2387Pins.lean:287-349`, at fe433f2): `ba_W_sub_one` (D402:
   `W - 1 = M⁺ S⁺` with `S⁺ = S W`), `BAGGGammaL`, `BAGGGammaR`, `BAGGGamma`.
2. **`baGGGamma_holds : ∀ d, BAGGGamma d`**, unconditionally (`gaussIBP` discharged).  Route
   of [yang2024Del, Lemma B.11]: the basic expansion `baLanlw_holds` at `x` applied to
   `Ǧ_{y'x} f` (`BAGGExp_df_mul`: the product rule for the two `HasDerivAt`'s), the pathwise
   split `G = Ǧ + M`, the linear system `v_x = Σ_β (M⁺S)_{xβ} v_β + r_x` for
   `v_x = 𝔼[Ǧ_{y'x} Ǧ_{xy} f]`, solved by `W = (1 - M⁺S)⁻¹` (`baW_mul`): `v = W r`, and
   `W (M⁺S) = W - 1` is where D402 enters.  Only `BASelf`, `baM_row_sq`, `baM_symm` and the
   Gershgorin bound `baW_isUnit` are used (C1, L5): no smallness of `g` or of `‖M - m₀ I‖`.
3. Compiled instances (`RBM.Graph.BAGGExpInst`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green RBM.BA

/-! ## 1. The pin (copied verbatim from the T2387 probe) -/

section GGGammaPin
variable (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)

/-- Left side of `GGGamma` (`B:393-405`): `Ǧ_{y'x} Ǧ_{xy} f` (the stage-L2c pin of `t/T2161:RBM3D/Probe/T2161Pins.lean:1408-1450`). -/
def BAGGGammaL (x y y' : Idx d L W) (ω : Ω d L W) : ℂ :=
  BAlwGc d L W g0 E t m ω y' x * BAlwGc d L W g0 E t m ω x y * BAlwf d L W g0 E t m P ω

/-- Right side with the corrected coefficient `(W - 1)_{xβ} = (M⁺S⁺)_{xβ}` (D402, `ba_W_sub_one`) in the first two sums. -/
def BAGGGammaR (x y y' : Idx d L W) (ω : Ω d L W) : ℂ :=
  (∑ β, (BAlwW d L W g0 E t m - 1) x β * BAlwM d L W g0 E m β y * BAlwM d L W g0 E m y' β * BAlwf d L W g0 E t m P ω +
    ∑ β, (BAlwW d L W g0 E t m - 1) x β * (BAlwGc d L W g0 E t m ω β y * BAlwM d L W g0 E m y' β +
        BAlwM d L W g0 E m β y * BAlwGc d L W g0 E t m ω y' β) * BAlwf d L W g0 E t m P ω +
    ∑ w, ∑ α, ∑ β, BAlwW d L W g0 E t m x w * BAlwM d L W g0 E m w α * BAlwS d L W t α β *
      (BAlwGc d L W g0 E t m ω β β * BAlwG d L W g0 E t m ω α y * BAlwGc d L W g0 E t m ω y' w * BAlwf d L W g0 E t m P ω +
        BAlwGc d L W g0 E t m ω α w * BAlwG d L W g0 E t m ω β y * BAlwG d L W g0 E t m ω y' β * BAlwf d L W g0 E t m P ω -
        BAlwG d L W g0 E t m ω β y * BAlwGc d L W g0 E t m ω y' w * BAlwdf d L W g0 E t m P ω β α))

end GGGammaPin

/-- **`GGGamma`** (corrected, D402): `𝔼[BAGGGammaL] = 𝔼[BAGGGammaR]` over `PF d L W 0` (proved: `baGGGamma_holds`, `Graph/BAGGExp.lean:358`). -/
def BAGGGamma (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (x y y' : Idx d L W),
      ∫ ω, BAGGGammaL d L W g0 E t m P x y y' ω ∂(PF d L W 0) = ∫ ω, BAGGGammaR d L W g0 E t m P x y y' ω ∂(PF d L W 0)

/-! ## 2. Tameness on the one-size law

A function of the sample `ω : Ω d L W` is `BAGGExp_TL` if it is, through the slice at size `0`, a `Tame` function of the
sequence space `lwWxSizes d L W 0 hL`; then it is integrable for `PF d L W 0` (as in `baLweight_holds`). -/

section BAGGExpTL

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- A tame function of the sequence space, read through the slice at size `0`, is integrable for `PF d L W 0`
(copy of the private `BAExpandW_integrable_PF`). -/
private theorem BAGGExp_integrable_PF (hL : 3 ≤ L) {F : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ}
    {G : Ω d L W → ℂ} (hF : Tame (lwWxSizes d L W 0 hL) F)
    (h : ∀ ω', G (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') = F ω') : Integrable G (PF d L W 0) := by
  have hG : G = F ∘ lwWxSec 0 hL := by
    funext ω
    have := h (lwWxSec 0 hL ω)
    rw [lwWx_slice_sec] at this
    exact this
  have hGc : Continuous G := by rw [hG]; exact hF.cont.comp (lwWx_continuous_sec hL)
  have hmap := Sizes.seqP_map_slice (lwWxSizes d L W 0 hL) 0
  rw [← hmap]
  refine (integrable_map_measure hGc.aestronglyMeasurable
    (Sizes.measurable_slice (lwWxSizes d L W 0 hL) 0).aemeasurable).2 ?_
  have e : G ∘ Sizes.slice (lwWxSizes d L W 0 hL) 0 = F := funext h
  rw [e]
  exact Tame.integrable (gaussIBP (lwWxSizes d L W 0 hL)) hF

/-- `g` is a tame function of the sequence space through the slice at size `0`. -/
private def BAGGExp_TL (hL : 3 ≤ L) (g : Ω d L W → ℂ) : Prop :=
  ∃ F : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ, Tame (lwWxSizes d L W 0 hL) F ∧
    ∀ ω', g (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') = F ω'

variable {hL : 3 ≤ L}

private theorem BAGGExp_TL.const (c : ℂ) : BAGGExp_TL hL (fun _ : Ω d L W => c) :=
  ⟨fun _ => c, Tame.const _, fun _ => rfl⟩

private theorem BAGGExp_TL.add {g₁ g₂ : Ω d L W → ℂ} (h₁ : BAGGExp_TL hL g₁) (h₂ : BAGGExp_TL hL g₂) :
    BAGGExp_TL hL (fun ω => g₁ ω + g₂ ω) := by
  obtain ⟨F₁, t₁, e₁⟩ := h₁
  obtain ⟨F₂, t₂, e₂⟩ := h₂
  exact ⟨fun ω' => F₁ ω' + F₂ ω', t₁.add t₂, fun ω' => by beta_reduce; rw [e₁, e₂]⟩

private theorem BAGGExp_TL.sub {g₁ g₂ : Ω d L W → ℂ} (h₁ : BAGGExp_TL hL g₁) (h₂ : BAGGExp_TL hL g₂) :
    BAGGExp_TL hL (fun ω => g₁ ω - g₂ ω) := by
  obtain ⟨F₁, t₁, e₁⟩ := h₁
  obtain ⟨F₂, t₂, e₂⟩ := h₂
  exact ⟨fun ω' => F₁ ω' - F₂ ω', t₁.sub t₂, fun ω' => by beta_reduce; rw [e₁, e₂]⟩

private theorem BAGGExp_TL.mul {g₁ g₂ : Ω d L W → ℂ} (h₁ : BAGGExp_TL hL g₁) (h₂ : BAGGExp_TL hL g₂) :
    BAGGExp_TL hL (fun ω => g₁ ω * g₂ ω) := by
  obtain ⟨F₁, t₁, e₁⟩ := h₁
  obtain ⟨F₂, t₂, e₂⟩ := h₂
  exact ⟨fun ω' => F₁ ω' * F₂ ω', t₁.mul t₂, fun ω' => by beta_reduce; rw [e₁, e₂]⟩

private theorem BAGGExp_TL.sum {ι : Type*} (s : Finset ι) {g : ι → Ω d L W → ℂ}
    (h : ∀ i ∈ s, BAGGExp_TL hL (g i)) : BAGGExp_TL hL (fun ω => ∑ i ∈ s, g i ω) := by
  choose! F hF he using h
  refine ⟨fun ω' => ∑ i ∈ s, F i ω', Tame.sum s hF, fun ω' => ?_⟩
  exact Finset.sum_congr rfl fun i hi => he i hi ω'

private theorem BAGGExp_TL.integrable {g : Ω d L W → ℂ} (h : BAGGExp_TL hL g) : Integrable g (PF d L W 0) := by
  obtain ⟨F, tF, e⟩ := h
  exact BAGGExp_integrable_PF hL tF e

variable (hL) in
/-- `G_{ab}` is tame (`Im z_t ≠ 0`). -/
private theorem BAGGExp_TL_G {g0 E t : ℝ} {m : ℂ} (hz : (ztOf m E t).im ≠ 0) (a b : Idx d L W) :
    BAGGExp_TL hL (fun ω => BAlwG d L W g0 E t m ω a b) :=
  ⟨baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t a b,
    (BAExpand_tame_baG (lwWxSizes d L W 0 hL) 0 hz g0 t a b), fun _ => rfl⟩

variable (hL) in
/-- `Ǧ_{ab}` is tame (`Im z_t ≠ 0`). -/
private theorem BAGGExp_TL_Gc {g0 E t : ℝ} {m : ℂ} (hz : (ztOf m E t).im ≠ 0) (a b : Idx d L W) :
    BAGGExp_TL hL (fun ω => BAlwGc d L W g0 E t m ω a b) :=
  (BAGGExp_TL_G hL hz a b).sub (BAGGExp_TL.const _)

variable (hL) in
/-- `f` is tame (`Im z_t ≠ 0`). -/
private theorem BAGGExp_TL_f {g0 E t : ℝ} {m : ℂ} (hz : (ztOf m E t).im ≠ 0)
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    BAGGExp_TL hL (fun ω => BAlwf d L W g0 E t m P ω) :=
  ⟨baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P),
    (baPoly_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz g0 t (lwWxRename d L W P)).tame,
    fun ω' => (baWx_baPoly hL g0 E t m ω' P).symm⟩

variable (hL) in
/-- `∂_{h_{βα}} f` is tame (`0 < t`, `Im z_t ≠ 0`). -/
private theorem BAGGExp_TL_df {g0 E t : ℝ} {m : ℂ} (hz : (ztOf m E t).im ≠ 0) (ht : 0 < t)
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (β α : Idx d L W) :
    BAGGExp_TL hL (fun ω => BAlwdf d L W g0 E t m P ω β α) :=
  ⟨dhSample (lwWxSizes d L W 0 hL) 0 t β α (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P)),
    lwStein_tame_dhSample (baPoly_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz g0 t (lwWxRename d L W P)) t β α,
    fun ω' => (baWx_dh hL hz ht g0 β α ω' P).symm⟩

end BAGGExpTL

/-! ## 3. The polynomial `Ǧ_{y'x} f` and its derivative -/

section BAGGExpCalc

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `G = Ǧ + M`, pathwise. -/
private theorem BAGGExp_G_eq (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) (i j : Idx d L W) :
    BAlwG d L W g0 E t m ω i j = BAlwGc d L W g0 E t m ω i j + BAlwM d L W g0 E m i j := by
  simp [BAlwGc]

variable (d L W) in
/-- The resolvent polynomial `(G_{y'x} - M_{y'x}) f` whose value is `Ǧ_{y'x} f`. -/
private def BAGGExp_Pt (g0 E : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) (y' x : Idx d L W) :
    MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  (MvPolynomial.X (true, y', x) - MvPolynomial.C (BAlwM d L W g0 E m y' x)) * P

/-- `f̃ = Ǧ_{y'x} f`. -/
private theorem BAGGExp_f_mul (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y' x : Idx d L W) (ω : Ω d L W) :
    BAlwf d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' x) ω =
      BAlwGc d L W g0 E t m ω y' x * BAlwf d L W g0 E t m P ω := by
  simp [BAGGExp_Pt, BAlwf, LWPins_resPoly, MvPolynomial.eval_mul, BAlwGc, BAlwG]

/-- **The derivative of `Ǧ_{y'x} f`** (product rule for the two `HasDerivAt`'s): `∂_{h_{βα}}(Ǧ_{y'x} f) =
-G_{y'β} G_{αx} f + Ǧ_{y'x} ∂_{h_{βα}} f` (`0 < t`). -/
private theorem BAGGExp_df_mul (hL : 3 ≤ L) {t : ℝ} (ht : 0 < t) (g0 E : ℝ) (m : ℂ)
    (hz : (ztOf m E t).im ≠ 0) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y' x β α : Idx d L W) (ω : Ω d L W) :
    BAlwdf d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' x) ω β α =
      -(BAlwG d L W g0 E t m ω y' β * BAlwG d L W g0 E t m ω α x * BAlwf d L W g0 E t m P ω) +
        BAlwGc d L W g0 E t m ω y' x * BAlwdf d L W g0 E t m P ω β α := by
  obtain ⟨ω', rfl⟩ : ∃ ω', ω = Sizes.slice (lwWxSizes d L W 0 hL) 0 ω' :=
    ⟨lwWxSec 0 hL ω, (lwWx_slice_sec 0 hL ω).symm⟩
  have hH : ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω')).IsHermitian :=
    BAExpand_Hm_isHermitian (lwWxSizes d L W 0 hL) 0 g0 t ω'
  have h1 := lwWx_hasDerivAt_Gres hH hz true β α y' x
  have h2 : HasDerivAt (fun s : ℂ => LWPins_resPoly d L W (ztOf m E t) P
      ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') + s • single β α (1 : ℂ)))
      (BAlwdf d L W g0 E t m P (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') β α) 0 := by
    have := BAExpand_bridge_hasDerivAt hL hz ht g0 β α ω' P
    rw [baWx_dh hL hz ht g0 β α ω' P] at this
    exact this
  have h3 := (h1.sub_const (BAlwM d L W g0 E m y' x)).mul h2
  have e : (fun s : ℂ => LWPins_resPoly d L W (ztOf m E t) (BAGGExp_Pt d L W g0 E m P y' x)
      ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') + s • single β α (1 : ℂ))) =
      fun s : ℂ => (Gres ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') +
          s • single β α (1 : ℂ)) (ztOf m E t) true y' x - BAlwM d L W g0 E m y' x) *
        LWPins_resPoly d L W (ztOf m E t) P
          ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') + s • single β α (1 : ℂ)) := by
    funext s
    simp [BAGGExp_Pt, LWPins_resPoly, MvPolynomial.eval_mul]
  change deriv (fun s : ℂ => LWPins_resPoly d L W (ztOf m E t) (BAGGExp_Pt d L W g0 E m P y' x)
      ((g0 : ℂ) • PsiI d L W + Hflow d L W t (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') + s • single β α (1 : ℂ))) 0 = _
  rw [e]
  refine h3.deriv.trans ?_
  simp only [zero_smul, add_zero]
  change -(BAlwG d L W g0 E t m _ y' β * BAlwG d L W g0 E t m _ α x) * BAlwf d L W g0 E t m P _ +
    (BAlwG d L W g0 E t m _ y' x - BAlwM d L W g0 E m y' x) * BAlwdf d L W g0 E t m P _ β α = _
  unfold BAlwGc
  ring

end BAGGExpCalc

/-! ## 4. The pathwise identities -/

section BAGGExpAlg

variable {d L W : ℕ} [NeZero L] [NeZero W]

variable (d L W) in
/-- The summand `ζ_β = (M_{βy} M_{y'β} + Ǧ_{βy} M_{y'β} + M_{βy} Ǧ_{y'β}) f` of the first two sums of `(B.20)`. -/
private def BAGGExp_zeta (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y y' β : Idx d L W) (ω : Ω d L W) : ℂ :=
  (BAlwM d L W g0 E m β y * BAlwM d L W g0 E m y' β + BAlwGc d L W g0 E t m ω β y * BAlwM d L W g0 E m y' β +
    BAlwM d L W g0 E m β y * BAlwGc d L W g0 E t m ω y' β) * BAlwf d L W g0 E t m P ω

variable (d L W) in
/-- The summand of the third sum of `(B.20)` at the vertex `w` (without the weight `W_{xw}`). -/
private def BAGGExp_B (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (y y' w : Idx d L W) (ω : Ω d L W) : ℂ :=
  ∑ α, ∑ β, BAlwM d L W g0 E m w α * BAlwS d L W t α β *
    (BAlwGc d L W g0 E t m ω β β * BAlwG d L W g0 E t m ω α y * BAlwGc d L W g0 E t m ω y' w * BAlwf d L W g0 E t m P ω +
      BAlwGc d L W g0 E t m ω α w * BAlwG d L W g0 E t m ω β y * BAlwG d L W g0 E t m ω y' β * BAlwf d L W g0 E t m P ω -
      BAlwG d L W g0 E t m ω β y * BAlwGc d L W g0 E t m ω y' w * BAlwdf d L W g0 E t m P ω β α)

/-- The right side of `(B.20)` is `Σ_β (W - 1)_{xβ} ζ_β + Σ_w W_{xw} B_w`, pathwise. -/
private theorem BAGGExp_R_eq (g0 E t : ℝ) (m : ℂ) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (x y y' : Idx d L W) (ω : Ω d L W) :
    BAGGGammaR d L W g0 E t m P x y y' ω =
      ∑ β, (BAlwW d L W g0 E t m - 1) x β * BAGGExp_zeta d L W g0 E t m P y y' β ω +
        ∑ w, BAlwW d L W g0 E t m x w * BAGGExp_B d L W g0 E t m P y y' w ω := by
  have h12 : ∑ β, (BAlwW d L W g0 E t m - 1) x β * BAlwM d L W g0 E m β y * BAlwM d L W g0 E m y' β *
        BAlwf d L W g0 E t m P ω +
      ∑ β, (BAlwW d L W g0 E t m - 1) x β * (BAlwGc d L W g0 E t m ω β y * BAlwM d L W g0 E m y' β +
        BAlwM d L W g0 E m β y * BAlwGc d L W g0 E t m ω y' β) * BAlwf d L W g0 E t m P ω =
      ∑ β, (BAlwW d L W g0 E t m - 1) x β * BAGGExp_zeta d L W g0 E t m P y y' β ω := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun β _ => by unfold BAGGExp_zeta; ring
  have h3 : ∀ w, ∑ α, ∑ β, BAlwW d L W g0 E t m x w * BAlwM d L W g0 E m w α * BAlwS d L W t α β *
      (BAlwGc d L W g0 E t m ω β β * BAlwG d L W g0 E t m ω α y * BAlwGc d L W g0 E t m ω y' w *
          BAlwf d L W g0 E t m P ω +
        BAlwGc d L W g0 E t m ω α w * BAlwG d L W g0 E t m ω β y * BAlwG d L W g0 E t m ω y' β *
          BAlwf d L W g0 E t m P ω -
        BAlwG d L W g0 E t m ω β y * BAlwGc d L W g0 E t m ω y' w * BAlwdf d L W g0 E t m P ω β α) =
      BAlwW d L W g0 E t m x w * BAGGExp_B d L W g0 E t m P y y' w ω := by
    intro w
    unfold BAGGExp_B
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  unfold BAGGGammaR
  rw [h12]
  exact congrArg _ (Finset.sum_congr rfl fun w _ => h3 w)

/-- **The pathwise identity of the basic expansion at `Ǧ_{y'x} f`** (`B:359-372`, then `G = Ǧ + M`):
`BAlanlwR (Ǧ_{y'x} f) = Σ_β (M⁺S)_{xβ} Ǧ_{y'β} Ǧ_{βy} f + Σ_β (M⁺S)_{xβ} ζ_β + B_x`. -/
private theorem BAGGExp_pathwise (hL : 3 ≤ L) {t : ℝ} (ht : 0 < t) (g0 E : ℝ) (m : ℂ)
    (hz : (ztOf m E t).im ≠ 0) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ)
    (x y y' : Idx d L W) (ω : Ω d L W) :
    BAlanlwR d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' x) x y ω =
      ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) x β * BAGGGammaL d L W g0 E t m P β y y' ω +
        ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) x β * BAGGExp_zeta d L W g0 E t m P y y' β ω +
        BAGGExp_B d L W g0 E t m P y y' x ω := by
  have hPm : ∀ u : Idx d L W → ℂ,
      ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) x β * u β =
        ∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwM d L W g0 E m α x * BAlwS d L W t α β * u β := by
    intro u
    simp only [Matrix.mul_apply, BAlwMp, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h1 : ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) x β * BAGGGammaL d L W g0 E t m P β y y' ω +
      ∑ β, (BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) x β * BAGGExp_zeta d L W g0 E t m P y y' β ω =
      ∑ α, ∑ β, BAlwM d L W g0 E m x α * BAlwM d L W g0 E m α x * BAlwS d L W t α β *
        (BAlwG d L W g0 E t m ω β y * BAlwG d L W g0 E t m ω y' β * BAlwf d L W g0 E t m P ω) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← mul_add]
    rw [hPm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    unfold BAGGGammaL BAGGExp_zeta
    rw [BAGGExp_G_eq g0 E t m ω β y, BAGGExp_G_eq g0 E t m ω y' β]
    ring
  rw [h1]
  unfold BAlanlwR BAGGExp_B
  simp only [BAGGExp_f_mul, BAGGExp_df_mul hL ht g0 E m hz P y' x]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [BAGGExp_G_eq g0 E t m ω α x]
  ring

end BAGGExpAlg

/-! ## 5. Target 2: `(B.20)` with the D402 coefficient -/

section BAGGExpHolds

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Closure of `BAGGExp_TL` under the operations of the identity (atoms first). -/
local macro "bagg_tl" : tactic =>
  `(tactic| repeat' first
    | exact BAGGExp_TL.const _
    | (apply BAGGExp_TL_Gc; assumption)
    | (apply BAGGExp_TL_G; assumption)
    | (apply BAGGExp_TL_f; assumption)
    | (apply BAGGExp_TL_df <;> assumption)
    | apply BAGGExp_TL.mul
    | apply BAGGExp_TL.add
    | apply BAGGExp_TL.sub
    | (apply BAGGExp_TL.sum; intros; skip))

/-- **`GGGamma`** (`B:393-405`, [yang2024Del, Lemma B.11], corrected: D402) on the block Anderson law `PF d L W 0`, for
every `d`: the pin `BAGGGamma`.  For `0 < t < 1`: `lanlw` at `x` applied to `Ǧ_{y'x} f` (`baLanlw_holds`,
`BAGGExp_pathwise`) gives `v = (M⁺S) v + r` for `v_x = 𝔼[Ǧ_{y'x} Ǧ_{xy} f]`, so `v = W r` by `W (1 - M⁺S) = 1`
(`baW_mul`), and `W (M⁺S) = W - 1` is the D402 coefficient; for `t = 0` both sides vanish. -/
theorem baGGGamma_holds (d : ℕ) : BAGGGamma d := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 P x y y'
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · have hL0 : ∀ ω, BAGGGammaL d L W g0 E 0 m P x y y' ω = 0 := fun ω => by
      simp [BAGGGammaL, BAExpand_Gc_zero]
    have hS0 : Matrix.of (BAlwS d L W 0) = 0 := by
      ext i j
      simp [BAlwS]
    have hW0 : BAlwW d L W g0 E 0 m = 1 := by
      simp [BAlwW, hS0]
    have hR0 : ∀ ω, BAGGGammaR d L W g0 E 0 m P x y y' ω = 0 := fun ω => by
      simp [BAGGGammaR, BAlwS, hW0, BAExpand_Gc_zero]
    simp [hL0, hR0]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    -- integrability
    have iL : ∀ a : Idx d L W, Integrable (fun ω => BAGGGammaL d L W g0 E t m P a y y' ω) (PF d L W 0) := by
      intro a
      refine BAGGExp_TL.integrable (hL := hL) ?_
      unfold BAGGGammaL
      bagg_tl
    have iZ : ∀ a : Idx d L W, Integrable (fun ω => BAGGExp_zeta d L W g0 E t m P y y' a ω) (PF d L W 0) := by
      intro a
      refine BAGGExp_TL.integrable (hL := hL) ?_
      unfold BAGGExp_zeta
      bagg_tl
    have iB : ∀ a : Idx d L W, Integrable (fun ω => BAGGExp_B d L W g0 E t m P y y' a ω) (PF d L W 0) := by
      intro a
      refine BAGGExp_TL.integrable (hL := hL) ?_
      unfold BAGGExp_B
      bagg_tl
    -- the vectors of expectations and their linear relation
    set Pm : Matrix (Idx d L W) (Idx d L W) ℂ := BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t) with hPm
    set v : Idx d L W → ℂ := fun a => ∫ ω, BAGGGammaL d L W g0 E t m P a y y' ω ∂(PF d L W 0) with hv
    set z : Idx d L W → ℂ := fun a => ∫ ω, BAGGExp_zeta d L W g0 E t m P y y' a ω ∂(PF d L W 0) with hz'
    set b : Idx d L W → ℂ := fun a => ∫ ω, BAGGExp_B d L W g0 E t m P y y' a ω ∂(PF d L W 0) with hb
    have hrel : ∀ a, v a - ∑ β, Pm a β * v β = ∑ β, Pm a β * z β + b a := by
      intro a
      have h1 := baLanlw_holds d L W hL g0 E t m hSelf ht.le ht1 (BAGGExp_Pt d L W g0 E m P y' a) a y
      have e1 : ∫ ω, BAlanlwL d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' a) a y ω ∂(PF d L W 0) = v a := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        unfold BAlanlwL BAGGGammaL
        rw [BAGGExp_f_mul]
        ring
      have iS1 : Integrable (fun ω => ∑ β, Pm a β * BAGGGammaL d L W g0 E t m P β y y' ω) (PF d L W 0) :=
        integrable_finsetSum _ fun β _ => (iL β).const_mul _
      have iS2 : Integrable (fun ω => ∑ β, Pm a β * BAGGExp_zeta d L W g0 E t m P y y' β ω) (PF d L W 0) :=
        integrable_finsetSum _ fun β _ => (iZ β).const_mul _
      have e2 : ∫ ω, BAlanlwR d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' a) a y ω ∂(PF d L W 0) =
          ∑ β, Pm a β * v β + (∑ β, Pm a β * z β + b a) := by
        have hpw : ∀ ω, BAlanlwR d L W g0 E t m (BAGGExp_Pt d L W g0 E m P y' a) a y ω =
            ∑ β, Pm a β * BAGGGammaL d L W g0 E t m P β y y' ω +
              ∑ β, Pm a β * BAGGExp_zeta d L W g0 E t m P y y' β ω +
              BAGGExp_B d L W g0 E t m P y y' a ω := fun ω => BAGGExp_pathwise hL ht g0 E m hz P a y y' ω
        have iS12 : Integrable (fun ω => ∑ β, Pm a β * BAGGGammaL d L W g0 E t m P β y y' ω +
            ∑ β, Pm a β * BAGGExp_zeta d L W g0 E t m P y y' β ω) (PF d L W 0) := iS1.add iS2
        simp_rw [hpw]
        have hS1 : ∫ ω, ∑ β, Pm a β * BAGGGammaL d L W g0 E t m P β y y' ω ∂(PF d L W 0) = ∑ β, Pm a β * v β := by
          rw [integral_finsetSum _ fun β _ => (iL β).const_mul (Pm a β)]
          exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _
        have hS2 : ∫ ω, ∑ β, Pm a β * BAGGExp_zeta d L W g0 E t m P y y' β ω ∂(PF d L W 0) = ∑ β, Pm a β * z β := by
          rw [integral_finsetSum _ fun β _ => (iZ β).const_mul (Pm a β)]
          exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _
        rw [integral_add iS12 (iB a), integral_add iS1 iS2, hS1, hS2, add_assoc]
      have : v a = ∑ β, Pm a β * v β + (∑ β, Pm a β * z β + b a) := by rw [← e1, h1, e2]
      rw [this]; ring
    have hW : BAlwW d L W g0 E t m * (1 - Pm) = 1 := baW_mul hL g0 E t m hSelf ht.le ht1
    have hWP : BAlwW d L W g0 E t m * Pm = BAlwW d L W g0 E t m - 1 := by
      rw [mul_sub, mul_one] at hW
      rw [← hW]
      abel
    set r : Idx d L W → ℂ := fun a => ∑ β, Pm a β * z β + b a with hr
    have hvec : v = BAlwW d L W g0 E t m *ᵥ r := by
      have h1 : (1 - Pm) *ᵥ v = r := by
        funext a
        have := hrel a
        simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
        simpa [Matrix.mulVec, dotProduct] using this
      rw [← h1, Matrix.mulVec_mulVec, hW, Matrix.one_mulVec]
    have hvx : v x = ∑ w, BAlwW d L W g0 E t m x w * r w := by
      have := congrFun hvec x
      simpa [Matrix.mulVec, dotProduct] using this
    -- the right side
    have iR1 : Integrable (fun ω => ∑ β, (BAlwW d L W g0 E t m - 1) x β *
        BAGGExp_zeta d L W g0 E t m P y y' β ω) (PF d L W 0) :=
      integrable_finsetSum _ fun β _ => (iZ β).const_mul _
    have iR2 : Integrable (fun ω => ∑ w, BAlwW d L W g0 E t m x w *
        BAGGExp_B d L W g0 E t m P y y' w ω) (PF d L W 0) :=
      integrable_finsetSum _ fun w _ => (iB w).const_mul _
    have eR : ∫ ω, BAGGGammaR d L W g0 E t m P x y y' ω ∂(PF d L W 0) =
        ∑ β, (BAlwW d L W g0 E t m - 1) x β * z β + ∑ w, BAlwW d L W g0 E t m x w * b w := by
      simp_rw [BAGGExp_R_eq]
      rw [integral_add iR1 iR2, integral_finsetSum _ fun β _ => (iZ β).const_mul ((BAlwW d L W g0 E t m - 1) x β),
        integral_finsetSum _ fun w _ => (iB w).const_mul (BAlwW d L W g0 E t m x w)]
      congr 1
      · exact Finset.sum_congr rfl fun β _ => integral_const_mul _ _
      · exact Finset.sum_congr rfl fun w _ => integral_const_mul _ _
    have h4 : ∑ w, BAlwW d L W g0 E t m x w * ∑ β, Pm w β * z β = ∑ β, (BAlwW d L W g0 E t m - 1) x β * z β := by
      rw [← hWP]
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun w _ => by ring
    rw [eR]
    change v x = _
    rw [hvx]
    simp only [hr, mul_add, Finset.sum_add_distrib, h4]

end BAGGExpHolds

/-! ## 6. Compiled instances (namespace `RBM.Graph.BAGGExpInst`)

`d = 3`, `L = 3`, `g₀ = 0`, `E = 0`, `m = i` (`BAExpandInst.baSelf_zero`: `M^{(B)} = i I`, `m = L^{-d} tr M^{(B)}`),
`t = 1/2`; three distinct sites `x = 0`, `y = e₀`, `y' = e₁`.  Every hypothesis of `baGGGamma_holds` is discharged
(`gaussIBP` is proved inside it).  The check that the printed `(B.20)` fails and the corrected one holds numerically
is a script, not Lean (the prove report). -/

end RBM.Graph

end
