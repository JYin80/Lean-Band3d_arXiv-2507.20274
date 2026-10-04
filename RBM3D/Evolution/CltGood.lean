/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.FarEntry
import RBM3D.Evolution.CltPath
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The good event of the replacement step on the finite model (ticket T2149, row S5-20)

Port of `RBM2D/Evolution/CltGood.lean` (697 lines, commit `c9a24cf`) onto the fine model
`RBM3D/Gauss/FineModel.lean`, with the dictionary `d : Sizes ↦ sz : Sizes d`, `Coord ↦ CoordF d`,
`P L W ↦ PF d L W (sz.lam n)`, `Z2, zdist2 ↦ Zd d, zdistInf`, `splitEquiv ↦ split`.  Paper
(arXiv:2507.20274): the coordinate tails are the entry bounds `|X_{ij}| ≺ S_{ij}^{1/2}` used at the
step length `W^{-1/2}` of `CltPathBound` (`CltPath.lean:110`); the bounds `|G_{xy}| ≤ 2` and the far
decay `|G_{xy}| ≤ W^{-D'}` are `(Gt_bound_flow)` (`1_2:1342`) at the section `τ` and the log-scale far
decay of `3_5:2245` (`STFarEntryAtLog`, `FarEntry.lean:673`).

Dictionary of the hypotheses (RBM2D `HClt` → merged RBM3D), bundled in `HClt`:
* `SizeTendsto`, `Bandwidth`, `(eq:WO)` → `STFlow.1 = Admissible` (`Defs/Sizes.lean:177`);
* `|E n| ≤ 2 - κ`, `t n < 1`, `RangeCond` → `v3_premises_of_stFlow` (`Green/Pins.lean:1049`);
* `Step2LocalPT`, `Step2DecayPT` → `STStep2Concl` on `[s, t]` (`STLocalEntryU` read at the section
  `τ` by `prec_timeIcc_section`, `FarEntry.lean:63`; `STGdecayW` inside `stFarEntryAtLog`);
* `GbEXPHypV3` → proved inside `stFarEntryAtLog` (`3 ≤ d`).

Results (namespace `RBM.Evol`), every `∀ᶠ n` along `sz : Sizes d`:
* `cltCoord_tail : CltCoordTail sz` (item 2): every real coordinate exceeds `W^{-1/2}` with
  probability `≤ 2 exp(-W/2) ≤ N^{-D}` (variance `gvarF ≤ W^{-d}`, `W ≥ N^𝔠`, `d ≥ 2`);
* `cltGmax_whp : CltGmaxWhp sz` (item 3): under `HClt`, all `G_τ(±)_{xy}` are `≤ 2` outside an event
  of probability `≤ N^{-D}` (`STLocalEntryU` at `τ`, `|m| = 1`, `STWB ≤ 2 N^{-a}`);
* `cltFarEntry_whp : CltFarEntryWhp sz` (item 4): far entries are `≤ W^{-D'}` outside such an event
  (`stFarEntryAtLog` at `D' + 1`, `N^𝔠 ≤ W`);
* `cltGood_whp : CltGoodWhp sz` (item 5): `¬ cltGoodAt` has probability `≤ N^{-D}`.

The union over the `N²` entries is inside the probability of `Prec` (`badSetAt`), so the exponents
are `D`, `D'+1` without the `+2` of RBM2D's per-time pins.  The transfer from `Sizes.seqP sz` to
`PF` is `Sizes.seqP_map_slice` and `Measure.map_apply` for the measurable failure events (the
integral form is `cltTransfer`, `CltSwap.lean:323`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Evol

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## 1. The pins -/

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **`HClt`** (the hypothesis bundle of the CLT step at a time sequence `τ`, replacing RBM2D's
`SizeTendsto`, `Bandwidth`, `RangeCond`, `Step2LocalPT`, `Step2DecayPT`, `GbEXPHypV3`): `3 ≤ d`,
the flow `STFlow sz κ ε 𝔠 𝔡 z` (`0 < κ`, `0 < ε`), `0 ≤ s ≤ τ ≤ t ≤ lemT z`, and the Step 2
conclusions `STStep2Concl` on `[s, t]` at the energy `E = STflowE z`. -/
def HClt (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  3 ≤ d ∧ 0 < κ ∧ 0 < ε ∧ STFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ τ n) ∧
    (∀ n, τ n ≤ t n) ∧ (∀ n, t n ≤ lemT (z n)) ∧ STStep2Concl sz (STflowE z) s t Cd

/-- The conclusion event of `CltCoordTail`: every real coordinate exceeds `W^{-1/2}` with
probability `≤ N^{-D}`. -/
def CltCoordConcl (D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ c : CoordF d (sz.L n) (sz.W n),
    PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ((sz.W n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Pin E1** (coordinate tails): every real coordinate exceeds `W^{-1/2}` with probability
`≤ N^{-D}`, eventually (`gvarF ≤ W^{-d}`, `d ≥ 2`, `W ≥ N^𝔠`). -/
def CltCoordTail : Prop :=
  2 ≤ d → ∀ 𝔠 : ℝ, 0 < 𝔠 → sz.SizeTendsto → sz.Bandwidth 𝔠 →
    ∀ D : ℝ, 0 < D → CltCoordConcl sz D

/-- The conclusion event of `CltGmaxWhp`, at the energy sequence `E`, the time sequence `τ` and the
charge `D`: all entries of `G_τ(±)` are `≤ 2` outside an event of probability `≤ N^{-D}`. -/
def CltGmaxConcl (E τ : ℕ → ℝ) (D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntry d (sz.L n) (sz.W n) (E n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Pin E2** (`(Gt_bound_flow)` at the section `τ`): under `HClt`, all entries of `G_τ(±)` at
`Hflow … (τ n) ω` are `≤ 2` outside an event of probability `≤ N^{-D}`, eventually. -/
def CltGmaxWhp : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
    ∀ D : ℝ, 0 < D → CltGmaxConcl sz (STflowE z) τ D

/-- The conclusion event of `CltFarEntryWhp`: entries with `c (log W)^3 ℓ_τ ≤ |[x] - [y]|_∞` are
`≤ W^{-D'}` outside an event of probability `≤ N^{-D}`. -/
def CltFarEntryConcl (E τ : ℕ → ℝ) (c D' D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntry d (sz.L n) (sz.W n) (E n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **Pin E3** (the log-scale far decay, `STFarEntryAtLog`): under `HClt`, for every `c > 0`, the
entries of `G_τ(±)` whose blocks are at distance `≥ c (log W)^3 ℓ_τ` are `≤ W^{-D'}` outside an
event of probability `≤ N^{-D}`, eventually. -/
def CltFarEntryWhp : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
    ∀ c : ℝ, 0 < c → ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D →
      CltFarEntryConcl sz (STflowE z) τ c D' D

/-- The conclusion of `CltGoodWhp`: the merged `cltGoodAt` (`CltPath.lean:83`) at the far threshold
`θ n` holds outside an event of probability `≤ N^{-D}`. -/
def CltGoodConcl (E τ θ : ℕ → ℝ) (D' D : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    PF d (sz.L n) (sz.W n) (sz.lam n)
        {ω | ¬ cltGoodAt d (sz.L n) (sz.W n) (E n) (τ n) (θ n) D' ω} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- **The consumer's form** (new): under `HClt`, the deterministic good set `cltGoodAt` of the path
bound holds with high probability, at every far threshold `θ n ≥ c (log W)^3 ℓ_τ`. -/
def CltGoodWhp : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (s τ t : ℕ → ℝ) (Cd : ℝ), HClt sz κ ε 𝔠 𝔡 z s τ t Cd →
    ∀ (c : ℝ) (θ : ℕ → ℝ), 0 < c →
      (∀ n, c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤ θ n) →
      ∀ D' : ℝ, 0 < D' → ∀ D : ℝ, 0 < D → CltGoodConcl sz (STflowE z) τ θ D' D

end Pins

/-! ## 2. Private helpers -/

section Helpers

/-- The entries `G_u(σ)_{xy}` of the resolvent of `H_u(ω)` are measurable in `ω`. -/
private theorem cltGood_gEntry_meas {d L W : ℕ} [NeZero L] [NeZero W] (E s u : ℝ) (σ : Bool)
    (x y : Idx d L W) :
    Measurable fun ω : Ω d L W => gEntry d L W E s (Hflow d L W u ω) σ x y := by
  have hH : Measurable fun ω : Ω d L W => Hflow d L W u ω :=
    Measurable.of_eval fun a => Measurable.of_eval fun b => measurable_Hflow d L W u a b
  exact (walk_measurable_Gres_apply (zt E s) σ x y).comp hH

/-- The transfer from the common product space `Sizes.seqP sz` to the finite model `PF`, for a
measurable event (`Sizes.seqP_map_slice`). -/
private theorem cltGood_P_le_of_seqP {d : ℕ} (sz : Sizes d) (n : ℕ)
    {S : Set (Ω d (sz.L n) (sz.W n))} (hS : MeasurableSet S) {b : ℝ≥0∞}
    (h : Sizes.seqP sz (Sizes.slice sz n ⁻¹' S) ≤ b) :
    PF d (sz.L n) (sz.W n) (sz.lam n) S ≤ b := by
  rw [← Sizes.seqP_map_slice sz n, Measure.map_apply (Sizes.measurable_slice sz n) hS]
  exact h

private theorem cltGood_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) :
    (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]

/-- `G(-)_{xy} = conj G(+)_{yx}` for a Hermitian `M`, in norm. -/
private theorem cltGood_norm_gEntry_false {d L W : ℕ} [NeZero L] [NeZero W] (E s : ℝ)
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) (x y : Idx d L W) :
    ‖gEntry d L W E s M false x y‖ = ‖gEntry d L W E s M true y x‖ := by
  have h := cltGood_Gres_conjTranspose hM (zt E s) true
  have h2 : gEntry d L W E s M false x y = star (gEntry d L W E s M true y x) := by
    have h3 := congrFun (congrFun h x) y
    rw [Matrix.conjTranspose_apply] at h3
    exact h3.symm
  rw [h2, norm_star]

/-- A bound on `G(+)` at every pair gives the same bound for both charges. -/
private theorem cltGood_exists_true {d L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (E s : ℝ) (hM : M.IsHermitian) {r : ℝ}
    (h : ∃ (σ : Bool) (x y : Idx d L W), r < ‖gEntry d L W E s M σ x y‖) :
    ∃ x y : Idx d L W, r < ‖gEntry d L W E s M true x y‖ := by
  obtain ⟨σ, x, y, hr⟩ := h
  cases σ
  · rw [cltGood_norm_gEntry_false E s hM] at hr
    exact ⟨y, x, hr⟩
  · exact ⟨x, y, hr⟩

end Helpers

/-! ## 3. Item 2: the coordinate tail -/

section CoordTail

/-- Every coordinate variance is at most `W^{-d}` (`gvarF ≤ svarF = W^{-d} sbKernelR ≤ W^{-d}`,
`∑ sbKernelR = 1`). -/
private theorem cltGood_gvarF_le {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L) (g : ℝ)
    (c : CoordF d L W) : (gvarF d L W g c : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hk : sbKernelR d L g ((split d L W c.1).1 - (split d L W c.2.1).1) ≤ 1 := by
    rw [← sum_sbKernelR d L g hL]
    exact Finset.single_le_sum (f := fun x => sbKernelR d L g x)
      (fun x _ => sbKernelR_nonneg d L g x) (Finset.mem_univ _)
  have hs : svarF d L W g c.1 c.2.1 ≤ ((W : ℝ) ^ d)⁻¹ := by
    unfold svarF SBR
    simp only [Matrix.of_apply]
    calc ((W : ℝ) ^ d)⁻¹ * sbKernelR d L g ((split d L W c.1).1 - (split d L W c.2.1).1)
        ≤ ((W : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left hk (by positivity)
      _ = _ := mul_one _
  have h0 := svarF_nonneg d L W g c.1 c.2.1
  change (if c.1 = c.2.1 then svarF d L W g c.1 c.2.1 else svarF d L W g c.1 c.2.1 / 2) ≤ _
  split_ifs <;> linarith

/-- The Gaussian tail of one coordinate on the finite model:
`P(W^{-1/2} < |ω_c|) ≤ 2 exp(-W/2)` (variance at most `W^{-d}`, `d ≥ 2`). -/
private theorem cltGood_coord_tail_finite {d L W : ℕ} [NeZero L] [NeZero W] (hL : 3 ≤ L)
    (hd : 2 ≤ d) (g : ℝ) (c : CoordF d L W) :
    PF d L W g {ω | (W : ℝ) ^ (-(1 / 2 : ℝ)) < |ω c|} ≤
      ENNReal.ofReal (2 * Real.exp (-(W : ℝ) / 2)) := by
  have hW : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  set B : ℝ := (W : ℝ) ^ (-(1 / 2 : ℝ)) with hBdef
  have hB : 0 ≤ B := Real.rpow_nonneg hW.le _
  have hB2 : B ^ 2 = (W : ℝ)⁻¹ := by
    rw [hBdef, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    norm_num [Real.rpow_neg_one]
  have hmeas : Measurable (fun ω : Ω d L W => ω c) := measurable_pi_apply c
  have hv0 : (0 : ℝ) ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  let v : ℝ≥0 := ⟨((W : ℝ) ^ d)⁻¹, hv0⟩
  have hsg : HasSubgaussianMGF (fun ω : Ω d L W => ω c) v (PF d L W g) := by
    rw [← HasSubgaussianMGF.id_map_iff hmeas.aemeasurable]
    have hmap : (PF d L W g).map (fun ω : Ω d L W => ω c) = gaussianReal 0 (gvarF d L W g c) :=
      Measure.infinitePi_map_eval _ c
    rw [hmap]
    refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
    rw [mgf_id_gaussianReal]
    apply Real.exp_le_exp.2
    have h1 := cltGood_gvarF_le (W := W) hL g c
    have h2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
    have hvc : (v : ℝ) = ((W : ℝ) ^ d)⁻¹ := rfl
    simp only [zero_mul, zero_add]
    rw [hvc]
    nlinarith
  have h1 := hsg.measure_ge_le hB
  have h2 := hsg.neg.measure_ge_le hB
  have hexp : -B ^ 2 / (2 * (v : ℝ)) ≤ -(W : ℝ) / 2 := by
    change -B ^ 2 / (2 * ((W : ℝ) ^ d)⁻¹) ≤ _
    rw [hB2]
    have hWd : (W : ℝ) ^ 2 ≤ (W : ℝ) ^ d := pow_le_pow_right₀ hW1 hd
    have hWd0 : (0 : ℝ) < (W : ℝ) ^ d := by positivity
    have : -(W : ℝ)⁻¹ / (2 * ((W : ℝ) ^ d)⁻¹) = -((W : ℝ) ^ d / (W : ℝ)) / 2 := by
      field_simp
    rw [this]
    have h3 : (W : ℝ) ≤ (W : ℝ) ^ d / (W : ℝ) := by
      rw [le_div_iff₀ hW]; nlinarith
    linarith
  have h1' := h1.trans (Real.exp_le_exp.2 hexp)
  have h2' := h2.trans (Real.exp_le_exp.2 hexp)
  have hsub : {ω : Ω d L W | B < |ω c|} ⊆
      {ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} := by
    intro ω hω
    have hω' : B < |ω c| := hω
    rcases le_abs.1 (le_of_lt hω') with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hf1 : PF d L W g {ω | B ≤ ω c} ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h1'
  have hf2 : PF d L W g {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} ≤
      ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := by
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal h2'
  have hp : (0 : ℝ) ≤ Real.exp (-(W : ℝ) / 2) := (Real.exp_pos _).le
  calc PF d L W g {ω | B < |ω c|}
      ≤ PF d L W g ({ω | B ≤ ω c} ∪ {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω}) :=
        measure_mono hsub
    _ ≤ PF d L W g {ω | B ≤ ω c} + PF d L W g {ω | B ≤ (-(fun ω : Ω d L W => ω c)) ω} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) +
          ENNReal.ofReal (Real.exp (-(W : ℝ) / 2)) := add_le_add hf1 hf2
    _ = ENNReal.ofReal (2 * Real.exp (-(W : ℝ) / 2)) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf

/-- `2 exp(-W/2) ≤ N^{-D}` eventually, from `W ≥ N^𝔠` and `N → ∞`. -/
private theorem cltGood_tail_eventually {d : ℕ} (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hN : sz.SizeTendsto) (hW : sz.Bandwidth 𝔠) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      2 * Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := by
  have hx : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hN
  have h1 : Tendsto (fun x : ℝ => x ^ (D / 𝔠) * Real.exp (-(1 / 2) * x)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D / 𝔠) (1 / 2) (by norm_num)
  filter_upwards [(h1.comp hx).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)), hW,
    hN.eventually_gt_atTop 0] with n hn hWn hN0
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := hN0
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set x : ℝ := N ^ 𝔠 with hxdef
  have hND : x ^ (D / 𝔠) = N ^ D := by
    rw [hxdef, ← Real.rpow_mul hNpos.le]
    congr 1
    field_simp
  have hNDpos : 0 < N ^ D := Real.rpow_pos_of_pos hNpos D
  have hexp : Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ Real.exp (-(1 / 2) * x) := by
    apply Real.exp_le_exp.2
    linarith
  have hexp0 : 0 < Real.exp (-(1 / 2) * x) := Real.exp_pos _
  have hcomb : 2 * Real.exp (-(1 / 2) * x) * N ^ D ≤ 1 := by
    have : N ^ D * Real.exp (-(1 / 2) * x) < 1 / 2 := by
      have hn' : x ^ (D / 𝔠) * Real.exp (-(1 / 2) * x) < 1 / 2 := hn
      rwa [hND] at hn'
    nlinarith
  rw [Real.rpow_neg hNpos.le]
  calc 2 * Real.exp (-((sz.W n : ℕ) : ℝ) / 2) ≤ 2 * Real.exp (-(1 / 2) * x) := by linarith
    _ = 2 * Real.exp (-(1 / 2) * x) * N ^ D * (N ^ D)⁻¹ := by field_simp
    _ ≤ 1 * (N ^ D)⁻¹ := by gcongr
    _ = (N ^ D)⁻¹ := one_mul _

/-- **Item 2.**  Every real coordinate exceeds `W^{-1/2}` with probability at most `N^{-D}`,
eventually. -/
theorem cltCoord_tail {d : ℕ} (sz : Sizes d) : CltCoordTail sz := by
  intro hd 𝔠 h𝔠 hN hW D hD
  unfold CltCoordConcl
  filter_upwards [cltGood_tail_eventually sz h𝔠 hN hW D] with n hn c
  exact (cltGood_coord_tail_finite (sz.three_le_L n) hd _ c).trans (ENNReal.ofReal_le_ofReal hn)

end CoordTail

/-! ## 4. Item 3: all entries `≤ 2` -/

section Gmax

/-- `STWB ≤ 2 N^{-a}` with `a = min(2𝔠𝔡, ε/2)`, eventually, uniformly in `K` and in `u ≤ t_n`:
`W^{-d} B_{u,K} ≤ (ilambda² W^d)⁻¹ + (N (1-u))⁻¹`, `(ilambda² W^d)⁻¹ ≤ W^{-2𝔡} ≤ N^{-2𝔠𝔡}`
(`(eq:WO)`, `W ≥ N^𝔠`), `(N (1-u))⁻¹ ≤ N^{-ε/2}` (`RangeCond`). -/
private theorem cltGood_STWB_le {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht : ∀ n, t n ≤ lemT (z n)) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℝ, u ≤ t n → ∀ K : ℕ,
      STWB sz n u K ≤ 2 * (((sz.size n : ℕ) : ℝ) ^ min (2 * 𝔠 * 𝔡) (ε / 2))⁻¹ := by
  obtain ⟨⟨h𝔠, h𝔡, hN, hBW, hWO⟩, -, ht1, hRC⟩ :=
    RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  filter_upwards [hBW, hWO, hRC] with n hBn hWOn hRn u hu K
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hu1 : u < 1 := lt_of_le_of_lt hu (ht1 n)
  have hv : 0 < 1 - u := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWOn.1
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hA := lam_sq_mul_pow_ge sz n hWOn.1
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hmain : STWB sz n u K ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
      (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
    unfold STWB Bparam
    rw [abs_of_pos hv]
    have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
        (sz.lam n ^ 2)⁻¹ := by
      have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
      have hb : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
        inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
      calc (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
          ≤ (sz.lam n ^ 2)⁻¹ * 1 := mul_le_mul ha hb (by positivity) (by positivity)
        _ = _ := mul_one _
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
          ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ +
            (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
      _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
            (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
          rw [hNe]; field_simp
  set a : ℝ := min (2 * 𝔠 * 𝔡) (ε / 2) with ha
  have ha1 : a ≤ 2 * 𝔠 * 𝔡 := min_le_left _ _
  have ha2 : a ≤ ε / 2 := min_le_right _ _
  have hNa : 0 < ((sz.size n : ℕ) : ℝ) ^ a := Real.rpow_pos_of_pos hNpos _
  -- first term
  have h1 : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ a)⁻¹ := by
    apply inv_anti₀ hNa
    have e1 : ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔠 * 𝔡) :=
      Real.rpow_le_rpow_of_exponent_le hN1 ha1
    have e2 : ((sz.size n : ℕ) : ℝ) ^ (2 * 𝔠 * 𝔡) =
        (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 * 𝔡) := by
      rw [← Real.rpow_mul hNpos.le]; congr 1; ring
    have e3 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 * 𝔡) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hBn (by linarith)
    linarith
  -- second term
  have h2 : (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ a)⁻¹ := by
    apply inv_anti₀ hNa
    have e1 : ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1 ha2
    have e2 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) =
        ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := by
      calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2)
          = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := by
            rw [Real.rpow_one]
        _ = ((sz.size n : ℕ) : ℝ) ^ (1 + (-1 + ε / 2)) := (Real.rpow_add hNpos _ _).symm
        _ = _ := by congr 1; ring
    have e3 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) ≤ 1 - u := by linarith
    calc ((sz.size n : ℕ) : ℝ) ^ a ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) := e1
      _ = ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 + ε / 2) := e2.symm
      _ ≤ ((sz.size n : ℕ) : ℝ) * (1 - u) := mul_le_mul_of_nonneg_left e3 hNpos.le
  linarith

/-- **Item 3.**  Under `HClt`, all entries of `G_τ(±)` are `≤ 2` outside an event of probability
`≤ N^{-D}`, eventually. -/
theorem cltGmax_whp {d : ℕ} (sz : Sizes d) : CltGmaxWhp sz := by
  intro κ ε 𝔠 𝔡 z s τ t Cd h D hD
  obtain ⟨hd, hκ, hε, hflow, hs, hsτ, hτt, ht, hS2⟩ := h
  obtain ⟨⟨h𝔠, h𝔡, hN, hBW, hWO⟩, hE, ht1, hRC⟩ :=
    RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hN
  set a : ℝ := min (2 * 𝔠 * 𝔡) (ε / 2) with ha
  have ha0 : 0 < a := lt_min (by positivity) (by linarith)
  have hLoc := prec_timeIcc_section sz hsτ hτt hS2.1
  have hP := hLoc (a / 2) (by linarith) D hD
  filter_upwards [hP, cltGood_STWB_le sz hκ hε hflow ht,
    hsize.eventually (eventually_le_rpow 2 (show 0 < a / 2 by linarith)),
    hsize.eventually_ge_atTop 1] with n hn hW hq hN1
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set q : ℝ := N ^ (a / 2) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hNpos _
  have hqq : N ^ a = q * q := by
    rw [hqdef, ← Real.rpow_add hNpos]; congr 1; ring
  have hmE : ‖mE (STflowE z n)‖ = 1 := norm_mE (le_of_lt ((hE n).trans (by linarith)))
  -- the failure event on the finite model
  let T : Set (Ω d (sz.L n) (sz.W n)) := ⋃ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    {ω | q * STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)) <
      ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω)
          true p.1 p.2 - (if p.1 = p.2 then mE (STflowE z n) else 0)‖ ^ 2}
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.iUnion fun p => ?_
    exact measurableSet_lt measurable_const
      (((cltGood_gEntry_meas (STflowE z n) (τ n) (τ n) true p.1 p.2).sub
        measurable_const).norm.pow_const 2)
  have hsub : {ω : Ω d (sz.L n) (sz.W n) | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
      2 < ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
        (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ⊆ T := by
    intro ω hω
    obtain ⟨x, y, hxy⟩ := cltGood_exists_true (STflowE z n) (τ n)
      (Hflow_isHermitian d (sz.L n) (sz.W n) (τ n) ω) hω
    refine Set.mem_iUnion.2 ⟨(x, y), ?_⟩
    have hite : ‖(if x = y then mE (STflowE z n) else 0)‖ ≤ 1 := by
      split_ifs
      · exact hmE.le
      · simp
    have h1 := norm_sub_norm_le
      (gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
        (Hflow d (sz.L n) (sz.W n) (τ n) ω) true x y)
      (if x = y then mE (STflowE z n) else 0)
    have h2 := hW (τ n) (hτt n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
    have h3 : q * STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) ≤ 1 := by
      calc q * STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))
          ≤ q * (2 * (N ^ a)⁻¹) := mul_le_mul_of_nonneg_left h2 hq0.le
        _ = 2 / q := by rw [hqq]; field_simp
        _ ≤ 1 := by rw [div_le_one hq0]; exact hq
    change q * STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) <
      ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
          (Hflow d (sz.L n) (sz.W n) (τ n) ω) true x y -
        (if x = y then mE (STflowE z n) else 0)‖ ^ 2
    have h4 : 1 < ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
          (Hflow d (sz.L n) (sz.W n) (τ n) ω) true x y -
        (if x = y then mE (STflowE z n) else 0)‖ := by linarith
    nlinarith
  calc PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
          (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖}
      ≤ PF d (sz.L n) (sz.W n) (sz.lam n) T := measure_mono hsub
    _ ≤ ENNReal.ofReal (N ^ (-D)) := cltGood_P_le_of_seqP sz n hTmeas
      ((measure_mono fun ω hω => by
        obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
        exact ⟨p, hp⟩).trans hn)

end Gmax

/-! ## 5. Item 4: the far entries -/

section Far

/-- **Item 4.**  Under `HClt`, for every `c > 0`, the entries of `G_τ(±)` with
`c (log W)^3 ℓ_τ ≤ |[x] - [y]|_∞` are `≤ W^{-D'}` outside an event of probability `≤ N^{-D}`,
eventually: `stFarEntryAtLog` at `(c, D' + 1)` and `N^𝔠 ≤ W`. -/
theorem cltFarEntry_whp {d : ℕ} (sz : Sizes d) : CltFarEntryWhp sz := by
  intro κ ε 𝔠 𝔡 z s τ t Cd h c hc D' hD' D hD
  obtain ⟨hd, hκ, hε, hflow, hs, hsτ, hτt, ht, hS2⟩ := h
  have hF := stFarEntryAtLog hd sz hκ hε hflow hs ht hsτ hτt hS2
  obtain ⟨h𝔠, h𝔡, hN, hBW, hWO⟩ := id hflow.1
  have hP := hF c hc (D' + 1) (by linarith) 𝔠 h𝔠 D hD
  filter_upwards [hP, hBW] with n hn hWn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  let T : Set (Ω d (sz.L n) (sz.W n)) := ⋃ p : Bool × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
    {ω | N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) <
      ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n) (Hflow d (sz.L n) (sz.W n) (τ n) ω)
          p.1 p.2.1 p.2.2‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2) : ℕ) : ℝ)
          then 1 else 0)}
  have hTmeas : MeasurableSet T := by
    refine MeasurableSet.iUnion fun p => ?_
    exact measurableSet_lt measurable_const
      ((cltGood_gEntry_meas (STflowE z n) (τ n) (τ n) p.1 p.2.1 p.2.2).norm.mul measurable_const)
  have hsub : {ω : Ω d (sz.L n) (sz.W n) | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
      c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
          ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
            (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
        ((sz.W n : ℕ) : ℝ) ^ (-D') <
          ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
            (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ⊆ T := by
    rintro ω ⟨σ, x, y, hf, hg⟩
    refine Set.mem_iUnion.2 ⟨(σ, x, y), ?_⟩
    have hf' : c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
        ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) := hf
    change N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) <
      ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
          (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖ *
        (if c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) then 1 else 0)
    simp only [hf', ↓reduceIte, mul_one]
    calc N ^ 𝔠 * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1))
        ≤ ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
          mul_le_mul_of_nonneg_right hWn (Real.rpow_nonneg hW0.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D') := by
          calc ((sz.W n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1))
              = ((sz.W n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) := by
                rw [Real.rpow_one]
            _ = ((sz.W n : ℕ) : ℝ) ^ (1 + (-(D' + 1))) := (Real.rpow_add hW0 _ _).symm
            _ = _ := by congr 1; ring
      _ < _ := hg
  calc PF d (sz.L n) (sz.W n) (sz.lam n) {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
              (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖}
      ≤ PF d (sz.L n) (sz.W n) (sz.lam n) T := measure_mono hsub
    _ ≤ ENNReal.ofReal (N ^ (-D)) :=
        cltGood_P_le_of_seqP sz n hTmeas
          ((measure_mono fun ω hω => by
            obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
            exact ⟨p, hp⟩).trans hn)

end Far

/-! ## 6. Item 5: the good set -/

section Good

/-- **Item 5.**  Under `HClt`, the deterministic good set `cltGoodAt` of the path bound holds
outside an event of probability `≤ N^{-D}`, at every far threshold `θ n ≥ c (log W)^3 ℓ_τ`:
the union of the events of items 3 and 4 at `D + 1`, `2 N^{-(D+1)} ≤ N^{-D}` once `N ≥ 2`. -/
theorem cltGood_whp {d : ℕ} (sz : Sizes d) : CltGoodWhp sz := by
  intro κ ε 𝔠 𝔡 z s τ t Cd h c θ hc hθ D' hD' D hD
  have h3 := cltGmax_whp sz κ ε 𝔠 𝔡 z s τ t Cd h (D + 1) (by linarith)
  have h4 := cltFarEntry_whp sz κ ε 𝔠 𝔡 z s τ t Cd h c hc D' hD' (D + 1) (by linarith)
  have hsize : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz h.2.2.2.1.1.2.2.1
  unfold CltGmaxConcl at h3
  unfold CltFarEntryConcl at h4
  unfold CltGoodConcl
  filter_upwards [h3, h4, hsize.eventually_ge_atTop 2] with n h3n h4n hN2
  have hN2' : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hp : (0 : ℝ) ≤ N ^ (-(D + 1)) := Real.rpow_nonneg hNpos.le _
  have h22 : 2 * N ^ (-(D + 1)) ≤ N ^ (-D) := by
    have e : N ^ (-(D + 1)) = N ^ (-D) * N⁻¹ := by
      rw [show -(D + 1) = -D + (-1) by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
    rw [e]
    have hD0 : 0 ≤ N ^ (-D) := Real.rpow_nonneg hNpos.le _
    have h2N : 2 * N⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hNpos]; exact hN2'
    nlinarith
  have hsub : {ω : Ω d (sz.L n) (sz.W n) |
      ¬ cltGoodAt d (sz.L n) (sz.W n) (STflowE z n) (τ n) (θ n) D' ω} ⊆
      {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        2 < ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
          (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} ∪
      {ω | ∃ (σ : Bool) (x y : Idx d (sz.L n) (sz.W n)),
        c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
            ((zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 -
              (split d (sz.L n) (sz.W n) y).1) : ℕ) : ℝ) ∧
          ((sz.W n : ℕ) : ℝ) ^ (-D') <
            ‖gEntry d (sz.L n) (sz.W n) (STflowE z n) (τ n)
              (Hflow d (sz.L n) (sz.W n) (τ n) ω) σ x y‖} := by
    intro ω hω
    by_contra hno
    apply hω
    refine ⟨fun σ x y => ?_, fun σ x y hθ' => ?_⟩
    · by_contra hlt
      push Not at hlt
      exact hno (Or.inl ⟨σ, x, y, hlt⟩)
    · by_contra hlt
      push Not at hlt
      exact hno (Or.inr ⟨σ, x, y, (hθ n).trans hθ', hlt⟩)
  calc PF d (sz.L n) (sz.W n) (sz.lam n)
        {ω | ¬ cltGoodAt d (sz.L n) (sz.W n) (STflowE z n) (τ n) (θ n) D' ω}
      ≤ PF d (sz.L n) (sz.W n) (sz.lam n) _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (N ^ (-(D + 1))) + ENNReal.ofReal (N ^ (-(D + 1))) := add_le_add h3n h4n
    _ = ENNReal.ofReal (2 * N ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal h22

end Good

end RBM.Evol

/-! ## 7. Compiled nonempty instances

At `d = 3` on the merged `Step5Inst.szCL` (`Induction/Step5Pins.lean:640`: `m = n + 24`,
`L_n = 2 m^5`, `W_n = 2^m`, `lam ≡ 1`), the flow `flow_zCL` (`κ = ε = 1/10`, `𝔠 = 1/6`,
`𝔡 = 1/10`, `z = zCL`), `s = τ ≡ 0` (`sCL`), `t = tCL` (`t_n = 1 - L_n^{-2}`), `C_d = 1`.  Only
`STStep2Concl` (the Step 2 pins, another gate) stays a hypothesis; every deterministic hypothesis of
`HClt` is discharged (`flow_zCL`, `lemT_zCL`, `szCL_hst`).  The statements go through the generic
definitions applied to `szCL` (the elaboration trap of T2141).  The far set is nonempty at every
`n` for `c = 1` (`farEntry_szCL_far_nonempty`), so the events of items 4 and 5 are not vacuous. -/

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-- `HClt` at `szCL` (every deterministic hypothesis discharged; `STStep2Concl` is the hypothesis). -/
theorem cltGood_hclt_szCL (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    HClt szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1 :=
  ⟨le_refl 3, by norm_num, by norm_num, flow_zCL, fun _ => le_rfl, fun _ => le_rfl,
    fun n => (szCL_hst n).le, lemT_zCL, hStep2⟩

/-- **Instance of `cltCoord_tail`** at `szCL`, `D = 10` (`2 ≤ 3`, `SizeTendsto`, `Bandwidth (1/6)`
discharged). -/
example : CltCoordConcl szCL 10 :=
  cltCoord_tail szCL (by norm_num) (1 / 6) (by norm_num) szCL_tendsto szCL_bandwidth 10
    (by norm_num)

/-- **Instance of `cltGmax_whp`** at `szCL`, `τ = s ≡ 0`, `D = 10`. -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    CltGmaxConcl szCL (STflowE zCL) sCL 10 :=
  cltGmax_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
    (cltGood_hclt_szCL hStep2) 10 (by norm_num)

/-- **Instance of `cltFarEntry_whp`** at `szCL`, `c = 1`, `D' = 5`, `D = 10`; the far set is nonempty
at every `n`. -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    CltFarEntryConcl szCL (STflowE zCL) sCL 1 5 10 ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
  ⟨cltFarEntry_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
    (cltGood_hclt_szCL hStep2) 1 (by norm_num) 5 (by norm_num) 10 (by norm_num),
   farEntry_szCL_far_nonempty⟩

/-- **Instance of `cltGood_whp`** at `szCL`, `c = 1`, `θ_n = (log W_n)^3 ℓ_s`, `D' = 5`, `D = 10`. -/
example (hStep2 : STStep2Concl szCL (STflowE zCL) sCL tCL 1) :
    CltGoodConcl szCL (STflowE zCL) sCL
        (fun n => 1 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n))
        5 10 ∧ ∀ n, farEntry_FarNonempty szCL sCL 1 n :=
  ⟨cltGood_whp szCL (1 / 10) (1 / 10) (1 / 6) (1 / 10) zCL sCL sCL tCL 1
    (cltGood_hclt_szCL hStep2) 1
    (fun n => 1 * Real.log ((szCL.W n : ℕ) : ℝ) ^ 3 * ellT (szCL.L n) (szCL.lam n) (sCL n))
    (by norm_num) (fun _ => le_rfl) 5 (by norm_num) 10 (by norm_num),
   farEntry_szCL_far_nonempty⟩

end RBM.Gauss.Step5Inst

namespace RBM.Evol

#print axioms cltCoord_tail
#print axioms cltGmax_whp
#print axioms cltFarEntry_whp
#print axioms cltGood_whp
#print axioms RBM.Gauss.Step5Inst.cltGood_hclt_szCL

end RBM.Evol

end
