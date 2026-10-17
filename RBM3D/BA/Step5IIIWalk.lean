/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIGood2
import RBM3D.BA.Step5IIIEdet2
import RBM3D.BA.Step5IIIKer2
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.Step2IterBA
import RBM3D.Chain.Step2CloseGen
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Induction.PfStep5

/-!
# U5d-1: the per-time layer of the stopped grid walk of BA case (iii) of Step 5 (ticket T2493, first half)

Paper: `lem:pf_step5` (`3_5:2376-2383`; stopping time `(eq:def_TTT)` `:2369-2372`; Duhamel form `(int_K-L_ST)` `:136`; `TailtoTail`
`:2345-2367`; `lem_dec_calE` `:2317-2338`); BA `7_8:2101` ("we therefore omit the details", paper-delta candidate T2459a).
Band twins (not edited): `Induction/PfStep5.lean`, `Induction/PfStep5Grid.lean`, `Induction/PfStep5Alg.lean`.
Design `docs/reports/T2459-design.md` U5-3; check `docs/tickets/checks/T2493-check.lean`.

This is the first half of the pre-signed split of ticket T2493; the second half (the walk `BAStep5IIIWalk`, the lift `BAStep5IIIFromWalk`,
targets 6-8) is `BA/Step5IIIWalk2.lean` on `t/T2493b`, which reads the public results below (stem `Step5IIIWalk_`).

**Targets 1-5** (the `T2493_*` pins of the check; each has a compiled nonempty instance in section 11):

* 1. `baStep5III_EMatrix_level` (a), `baStep5IIIGood_bundle` (b); `Step5IIIWalk_good_of_flow` is `baStep5IIIGoodThm_holds` read as a theorem whose
  conclusion head is `BAStep5IIIGood` (the registry scan counts the binder of (b) as proved by it).
* 2. `baStep5IIIJsharp_measurable`, `baStep5III_goodMeas`.
* 3. `baStep5III_crudeQV`: (H2), `‖STeeMg‖ ≤ 2N(16N)⁶`.
* 4. `baStep5III_walkLevel`: the bundle at the walk level `D_u = D* + 2 log_W (1-u)`.
* 5. `baStep5III_duhamel`: `(int_K-L_ST)` at `Step2Gen_UN` of a carrier with K1-K3 (`Step5IIIWalk_duhamel`), `Cdu = 64`, exponent `7`.

**The per-time layer** (read by the second half; band twins in brackets):

* `Step5IIIWalk_apriori` (`pfStep5_apriori`), `Step5IIIWalk_Kcrude`: the a priori bound `‖(𝓛-𝒦)^{(2)}‖ ≤ N³`.
* `Step5IIIWalk_ugenSum` (`pfStep5Alg_ugenSum'`): the drift sum at the BA kernel from `TailtoTail`.
* `Step5IIIWalk_mart_real` (`pfStep5_mart_real`, the constant `Cq` a parameter), `Step5IIIWalk_Ctot`, `Step5IIIWalk_assemble` (`pfStep5_assemble`): the
  four-term assembly (initial term, drift, martingale, Duhamel remainder).
* `Step5IIIWalk_pertime_det`, `Step5IIIWalk_pertime` (`pfStep5_pertime`, `pfStep5_perj`): the drift and quadratic-variation bounds at a grid time.
* `Step5IIIWalk_xx` (`pfStep5_xx`): `‖STeeUMg‖ ≤ (2 Cq p + 1) T̂²` at a grid time, along the flow.
* `Step5IIIWalk_good_transfer`: the good event of targets 1-2 moved to the grid walk (`Step2EventsGenTw_baLaw`).
* `Step5IIIWalk_init` (`pfStep5_init_le`), `Step5IIIWalk_drift_eq`, `Step5IIIWalk_hQ` (the loss budget `lossE2wG · W^{2θ'} S_θ ≤ N^τ`).

Registry: `BAStep5IIIEMatrix` is concluded by `baStep5III_EMatrix_level` (its `owedProps` line is removed).  Helpers carry the stem `Step5IIIWalk_`;
the private lemmas of the band files are reached by `open private` (the dispatcher's copy-or-open rule, §153 (1)); nothing is copied from RBM1D/RBM2D.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private pfStep5Grid_abs pfStep5Grid_slot pfStep5Grid_slot_apply pfStep5Grid_slot_add pfStep5Grid_slot_sub
  pfStep5Grid_slot_smul pfStep5Grid_slot_one pfStep5Grid_norm_slot pfStep5Grid_sum2 pfStep5Grid_update2
  pfStep5Grid_update2' pfStep5Grid_alg pfStep5Grid_inv_le from RBM3D.Induction.PfStep5Grid
open private pfStep5_drift_sum pfStep5_mart_sum pfStep5_Zineq pfStep5_final_ineq pfStep5_init_le pfStep5_tailTD_mono
  pfStep5_tailTD_floor pfStep5_tailTD_nonneg pfStep5_lvl pfStep5_W2_le pfStep5_rpow_le pfStep5_y_three_half pfStep5_sizes
  from RBM3D.Induction.PfStep5

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 1 and 2: the bundle bridge and the measurable-preimage form -/

section Bundle

/-- **Target 1 (a)** (`T2493_EMatrixLevel`; U5c target 2 in the bundle's name): the matrix part `BAStep5IIIEMatrix` at `(D, J)` gives it at
`(D', J♯(D'))` for `D' ≤ D`.  The conclusion head is `BAStep5IIIEMatrix` (registry, DECISIONS §290 (3)); the content is
`baStep5III_matrix_level` (`BAStep5IIIEMatrix` unfolds to its inline text). -/
theorem baStep5III_EMatrix_level (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D D' Λ K₀ J θ Cd : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      D' ≤ D → BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
        BAStep5IIIEMatrix sz lam0 E n u D' Λ K₀ (BAStep5IIIJsharp sz lam0 E n D' u H) θ Cd H :=
  fun sz lam0 E n u D D' Λ K₀ J θ Cd H hD h => baStep5III_matrix_level d sz lam0 E n u D D' Λ K₀ J θ Cd H hD h

/-- **Target 1 (b)** (`T2493_GoodBundle`): U5c's good event `BAStep5IIIGood` with its matrix part read as `BAStep5IIIEMatrix` (definitional). -/
theorem baStep5IIIGood_bundle {d : ℕ} :
    ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (D Cd : ℝ), BAStep5IIIGood sz z s t D Cd →
      ∀ τ' D₁ θ : ℝ, 0 < τ' → 0 < D₁ → 0 < θ → θ < 1 → ∀ᶠ n in atTop, ∀ u : TimeIcc s t n, ∃ G : Set sz.SeqΩ,
        Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) ∧ ∀ ω ∈ G,
          BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
            (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n D (u : ℝ) (sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω)) θ Cd
            (sz.seqHflowBA (BAflowLam0 sz z) n (u : ℝ) ω) := by
  intro sz z s t D Cd h τ' D₁ θ hτ' hD₁ hθ0 hθ1
  filter_upwards [h τ' D₁ θ hτ' hD₁ hθ0 hθ1] with n hn u
  obtain ⟨G, hG, hGm⟩ := hn u
  exact ⟨G, hG, fun ω hω => hGm ω hω⟩

/-- The good event of U5c at a flow: `baStep5IIIGoodThm_holds` read as a statement about the good event itself (its arguments are the
arguments of `BAStep5IIIGoodThm`; the four carrier predicates are other gates' pins and stay hypotheses).  Its conclusion head is
`BAStep5IIIGood`. -/
theorem Step5IIIWalk_good_of_flow {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (hCd : 0 < Cd) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (hT : ∀ n, t n ≤ BAflowT0 sz z n) (hReg : STReg5III sz s t)
    (hAvg : STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (hLmax : STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (hLK : STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (hDec : STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) (D : ℝ) (hD : 0 < D) :
    BAStep5IIIGood sz z s t D Cd :=
  baStep5IIIGoodThm_holds d hd κ ε 𝔠 𝔡 Cd sz z hκ hε h𝔡 hCd hflow s t hs hst hT hReg hAvg hLmax hLK hDec D hD

/-- The Hermitian matrices are a measurable (closed) set (copy of `EigenMeasurable.measurableSet_isHermitian`,
`Universality/EigenMeasurable.lean:295`, private there). -/
private theorem Step5IIIWalk_meas_herm {n : Type*} [Fintype n] [DecidableEq n] :
    MeasurableSet {A : Matrix n n ℂ | A.IsHermitian} := by
  have hcont : Continuous (fun A : Matrix n n ℂ => Aᴴ) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.conjTranspose_apply]
    exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
  have heq : {A : Matrix n n ℂ | A.IsHermitian} = {A | Aᴴ = A} := rfl
  rw [heq]
  exact (isClosed_eq hcont continuous_id).measurableSet

/-- A family of measurable inequalities over two countable index types cuts out a measurable set. -/
private theorem Step5IIIWalk_meas_le {X ι κ : Type*} [MeasurableSpace X] [Countable ι] [Countable κ]
    (f g : ι → κ → X → ℝ) (hf : ∀ i j, Measurable (f i j)) (hg : ∀ i j, Measurable (g i j)) :
    MeasurableSet {x : X | ∀ i j, f i j x ≤ g i j x} := by
  have : {x : X | ∀ i j, f i j x ≤ g i j x} = ⋂ i, ⋂ j, {x | f i j x ≤ g i j x} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => measurableSet_le (hf i j) (hg i j)

/-- **Target 2 (a)** (`T2493_JsharpMeas`; band `pfStep5Grid_JsharpM_measurable`, `Induction/PfStep5Grid.lean:197`, private):
`J♯` is measurable in the matrix. -/
theorem baStep5IIIJsharp_measurable (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D u : ℝ),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        BAStep5IIIJsharp sz lam0 E n D u H := by
  intro sz lam0 E n D u
  have hne : (Finset.univ : Finset ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))).Nonempty :=
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have hG := Step2EventsGenTw_baGrid sz lam0 E
  have h := Finset.measurable_sup' (s := Finset.univ) hne
    (f := fun (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
        ‖STLKMg (baStep2Mat sz lam0 E) n u H p.1 p.2‖ / STtailTD sz n u D p.2)
    (fun p _ => ((Step2EventsGen_STLKMg_measurable hG n u p.1 p.2).norm).div_const _)
  have h2 := (measurable_const (a := (1 : ℝ))).max h
  convert h2 using 1
  funext H
  simp [BAStep5IIIJsharp, Finset.sup'_apply]

/-- **Target 2 (b)** (`T2493_GoodMeas`; band `pfStep5_goodMeas`, `Induction/PfStep5.lean:270`): the matrix part at the realized control is a
measurable set of matrices.  (ii), (iii) and the right side of (vi) do not depend on `H`; the left sides are measurable by F9
(`Step2EventsGenTw_baGrid`). -/
theorem baStep5III_goodMeas (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ θ Cd : ℝ),
      MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ (BAStep5IIIJsharp sz lam0 E n D u H) θ Cd H} := by
  intro sz lam0 E n u D Λ K₀ θ Cd
  classical
  have hG := Step2EventsGenTw_baGrid sz lam0 E
  have hLM : ∀ {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ := fun σ a => (hG.meas_LM n u σ a).norm
  have hLK : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
        ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ := fun σ a =>
    (Step2EventsGen_STLKMg_measurable hG n u σ a).norm
  have hJ := baStep5IIIJsharp_measurable d sz lam0 E n D u
  have m1 : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ | H.IsHermitian} :=
    Step5IIIWalk_meas_herm
  have m2 := Step5IIIWalk_meas_le (ι := Fin 2 → Bool) (κ := Fin 2 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖)
    (fun σ a H => BAStep5IIIJsharp sz lam0 E n D u H * STtailTD sz n u D a) (fun σ a => hLK σ a)
    (fun σ a => hJ.mul_const _)
  have m3 : MeasurableSet {_H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤
        K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹} := MeasurableSet.const _
  have m4 : MeasurableSet {_H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)} := MeasurableSet.const _
  have m5 := Step5IIIWalk_meas_le (ι := Bool) (κ := Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖)
    (fun σ a H => Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
    (fun σ a => ((hG.meas_LM n u (fun _ : Fin 1 => σ) (fun _ => a)).sub measurable_const).norm)
    (fun σ a => measurable_const)
  have m6 := Step5IIIWalk_meas_le (ι := Fin 2 → Bool) (κ := Fin 2 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖)
    (fun σ a H => Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) (fun σ a => hLM σ a) (fun σ a => measurable_const)
  have m7 := Step5IIIWalk_meas_le (ι := Fin 3 → Bool) (κ := Fin 3 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖)
    (fun σ a H => Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) (fun σ a => hLM σ a) (fun σ a => measurable_const)
  have m8 := Step5IIIWalk_meas_le (ι := Fin 4 → Bool) (κ := Fin 4 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖)
    (fun σ a H => Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) (fun σ a => hLM σ a) (fun σ a => measurable_const)
  have m9 := Step5IIIWalk_meas_le (ι := Fin 6 → Bool) (κ := Fin 6 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖)
    (fun σ a H => Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) (fun σ a => hLM σ a) (fun σ a => measurable_const)
  have m10 := Step5IIIWalk_meas_le (ι := Fin 2 → Bool) (κ := Fin 2 → Zd d (sz.L n))
    (fun σ a (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖)
    (fun σ a H => ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 *
      Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))
    (fun σ a => hLK σ a) (fun σ a => measurable_const)
  unfold BAStep5IIIEMatrix
  simp only [Set.ofPred_and]
  exact m1.inter (m2.inter (m3.inter (m4.inter (m5.inter (m6.inter (m7.inter (m8.inter (m9.inter m10))))))))

end Bundle

/-! ## 2. Target 3: the crude quadratic variation at the flow ((H2) of `baStep5IIITailSqQV_holds`) -/

section CrudeQV

/-- **Target 3** (`T2493_CrudeQV`; band `difRep2_norm_STeeM_le_N`, `Path/DifREP2.lean:1277`): eventually, for `u ≤ t_n ≤ t₀` and Hermitian `H`,
`‖STeeMg‖ ≤ 2N(16N)⁶` (the `Y` of `pfStep5_farAbsorb`).  `gridRepTailBA_STeeMg_norm_le` at `η = 1/(16N)`, which is below `η_u` once
`N^ε ≥ 1/(8κ)` (`gridRepTailBA_eta`). -/
theorem baStep5III_crudeQV (d : ℕ) :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ,
      (∀ n, t n ≤ BAflowT0 sz z n) → ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n →
        ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
          ∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
            ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u H σ b b'‖ ≤
              2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6 := by
  intro κ ε 𝔠 𝔡 sz z hκ hε hflow t htT
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hNε : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ ε) atTop atTop := (tendsto_rpow_atTop hε).comp hsize
  filter_upwards [hNε.eventually_ge_atTop (1 / (8 * κ)), hsize.eventually_ge_atTop 1] with n hεn hN1 u hu H hH σ b b'
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hη := gridRepTailBA_eta hκ sz hflow t n (htT n) hN0 hεn u hu
  have h := gridRepTailBA_STeeMg_norm_le sz (BAflowLam0 sz z) (BAflowEs sz z) n u hH
    (η := 1 / (16 * ((sz.size n : ℕ) : ℝ))) (by positivity) hη σ b b'
  rw [one_div, inv_inv] at h
  exact h

end CrudeQV

/-! ## 3. Target 4: the walk level -/

section WalkLevel

/-- **Target 4** (`T2493_WalkLevel`; band `pfStep5_perj`, `Induction/PfStep5.lean:1406-1468`): on the matrix part at the crude level `D*` and
`J♯(u, D_u) < W^{ε₀}` (`ε₀ ≤ 1/2`), both bundle parts hold at the walk level `D_u = D* + 2 log_W (1-u)` with the control `J♯(u, D_u)` and
`Λ = K₀ = N^{τ'}`.  The matrix part is U5c target 2 (`D_u ≤ D*` for `u ≥ 0`); the scalar part is U5c target 4 at `D* - 6`, with
`1 - u ≥ lam² ≥ W^{-3}` giving `D_u ≥ D* - 6`. -/
theorem baStep5III_walkLevel (d : ℕ) (hd : 3 ≤ d) :
    ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) →
      STReg5III sz s t → ∀ Dst τ' θ Cd ε₀ : ℝ, 0 ≤ τ' → ε₀ ≤ 1 / 2 →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ))) →
      ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
        BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
          (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H →
        BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H <
          ((sz.W n : ℕ) : ℝ) ^ ε₀ →
        BAStep5IIIEScalar sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (((sz.size n : ℕ) : ℝ) ^ τ')
            (((sz.size n : ℕ) : ℝ) ^ τ')
            (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H) ∧
          BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ))
            (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
            (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H) θ Cd H := by
  intro κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg Dst τ' θ Cd ε₀ hτ' hε₀ hfl
  have hsc := baStep5III_scalar_flow d hd κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg (Dst - 2 * (d : ℝ)) τ' hτ' hfl
  filter_upwards [hsc] with n hn u H hmat hJ
  have hW1' : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWhalf : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hW1' (by norm_num)
  -- the scalar part at the crude level `D* - 6` with `J = 1`: `0 ≤ u < 1`, `lam² ≤ 1 - u`, `1 ≤ lam² W³`, `4 ≤ log W`
  obtain ⟨-, hu0, hu1, -, hreg, hA, -, -, hlog, -, -, -⟩ := hn u (Dst - 2 * (d : ℝ)) 1 le_rfl le_rfl hWhalf
  have hW1 : 1 < ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have := Real.log_nonpos hW0.le (not_lt.1 hcon)
    linarith
  -- the level `D_u ∈ [D* - 6, D*]`
  have hlv := pfStep5Grid_level d ((sz.W n : ℕ) : ℝ) Dst (u : ℝ) (u : ℝ) hW1 le_rfl hu1
  have hWdl : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℕ) : ℝ)) ≤ 1 - (u : ℝ) := by
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
      rw [inv_le_iff_one_le_mul₀' hWd]; nlinarith
    linarith
  have hlow : Dst - 2 * (d : ℝ) ≤ PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ) := by
    have := hlv.2.2.2 hWdl
    norm_num at this ⊢
    linarith
  have hup : PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ) ≤ Dst := hlv.2.2.1 hu0
  have hJ1 := (baStep5IIIJsharp_spec d sz (BAflowLam0 sz z) (BAflowEs sz z) n
    (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H).1
  have hJW : BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H ≤
      ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) :=
    hJ.le.trans (Real.rpow_le_rpow_of_exponent_le hW1' hε₀)
  exact ⟨hn u _ _ hlow hJ1 hJW, baStep5III_matrix_level d sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst _ _ _ _ θ Cd H hup hmat⟩

end WalkLevel

/-! ## 4. Target 5: the Duhamel form at the BA kernel -/

section Duhamel

open scoped Matrix.Norms.Operator

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {n : ℕ}

/-- The `ℓ^∞` operator norm of a matrix is at most `ρ` when every row sum is. -/
theorem Step5IIIWalk_norm_le_rows {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ a, ∑ b, ‖A a b‖ ≤ ρ) : ‖A‖ ≤ ρ := by
  rw [Matrix.linfty_opNorm_def]
  have hs : (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) ≤ ρ.toNNReal := Finset.sup_le fun a _ => by
    rw [← NNReal.coe_le_coe]
    simpa [NNReal.coe_sum, Real.coe_toNNReal _ hρ] using h a
  have := NNReal.coe_le_coe.mpr hs
  simpa [Real.coe_toNNReal _ hρ] using this

/-- **K1 gives the one-slot identity** `u_{s,t} = 1 + (t - s) θ_t` (`0 ≤ t < 1`, every `s`): `u_{t,t} = 1` and `u_{s,t} = (1 - sX) Θ_t`,
`θ_t = X Θ_t` (`Chain/Step2Gen.lean:188-193`). -/
theorem Step5IIIWalk_uKer_eq (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (s : ℝ) :
    Step2Gen_uKer C n σ σ' s t = 1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n σ σ' t := by
  have h1 : Step2Gen_uKer C n σ σ' t t = 1 := (hker.1 σ σ' 0 t t ht0 ht1 ht0 ht1).1
  unfold Step2Gen_uKer at h1 ⊢
  unfold Step2Gen_thetaKer
  set X := Step2Kern_Mss C n σ σ' * C.S n with hX
  have hsplit : (1 - (s : ℂ) • X) = (1 - (t : ℂ) • X) + ((t - s : ℝ) : ℂ) • X := by
    push_cast; rw [sub_smul]; abel
  rw [hsplit, add_mul, h1, smul_mul_assoc]


/-- Row sums of `θ_t`: K3 at `s = -1` (`u_{-1,t} - 1 = (t + 1) θ_t`). -/
theorem Step5IIIWalk_theta_rows (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a : Zd d (sz.L n)) : ∑ b, ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ (1 - t)⁻¹ := by
  have h3 := hker.2.2.1 σ σ' (-1) t ht0 ht1 a
  have e : ∀ b, ‖Step2Gen_uKer C n σ σ' (-1) t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ =
      (t + 1) * ‖Step2Gen_thetaKer C n σ σ' t a b‖ := by
    intro b
    rw [Step5IIIWalk_uKer_eq hker σ σ' ht0 ht1 (-1)]
    simp only [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_left, smul_eq_mul, norm_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (by linarith)]
    ring
  simp only [e, ← Finset.mul_sum] at h3
  have habs : |t - -1| = t + 1 := by rw [abs_of_nonneg (by linarith)]; ring
  rw [habs] at h3
  have hpos : 0 < t + 1 := by linarith
  have : (t + 1) * ∑ b, ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ (t + 1) * (1 - t)⁻¹ := h3
  exact le_of_mul_le_mul_left this hpos

theorem Step5IIIWalk_theta_norm (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖Step2Gen_thetaKer C n σ σ' t‖ ≤ (1 - t)⁻¹ :=
  Step5IIIWalk_norm_le_rows _ (inv_nonneg.2 (by linarith)) (Step5IIIWalk_theta_rows hker σ σ' ht0 ht1)

/-- The resolvent identity `θ_w - θ_v = (w - v) θ_w θ_v` from K1 (the semigroup law with `u = -1`) and the one-slot identity. -/
theorem Step5IIIWalk_theta_resolvent (hker : GridRepTailGen_Ker C n) (σ σ' : Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Step2Gen_thetaKer C n σ σ' w - Step2Gen_thetaKer C n σ σ' v =
      ((w - v : ℝ) : ℂ) • (Step2Gen_thetaKer C n σ σ' w * Step2Gen_thetaKer C n σ σ' v) := by
  have hs := (hker.1 σ σ' (-1) v w hv0 hv1 hw0 hw1).2
  rw [Step5IIIWalk_uKer_eq hker σ σ' hw0 hw1 v, Step5IIIWalk_uKer_eq hker σ σ' hv0 hv1 (-1),
    Step5IIIWalk_uKer_eq hker σ σ' hw0 hw1 (-1)] at hs
  set θw := Step2Gen_thetaKer C n σ σ' w
  set θv := Step2Gen_thetaKer C n σ σ' v
  have hc : ((v + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : v + 1 ≠ 0)
  refine smul_right_injective _ hc ?_
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one] at hs
  push_cast at hs ⊢
  simp only [smul_sub, smul_smul]
  linear_combination (norm := module) (-1 : ℂ) • hs

/-! ### The operators `𝒰_{v,w}`, `Θ^{(2)}_t` on the sup-normed 2-index tensors -/

section Ops

variable (C) (n) (σ : Fin 2 → Bool)

/-- `𝒰_{v,w}` as a bounded operator: slot `0` and slot `1` of the one-index kernel `uKer` at the charges `(σ_i, σ_{i+1})`. -/
private def Step5IIIWalk_Uc (v w : ℝ) :
    ((Fin 2 → Zd d (sz.L n)) → ℂ) →L[ℂ] ((Fin 2 → Zd d (sz.L n)) → ℂ) :=
  pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_uKer C n (σ 0) (σ (finRotate 2 0)) v w) *
    pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_uKer C n (σ 1) (σ (finRotate 2 1)) v w)

/-- `Θ^{(2)}_t` as a bounded operator. -/
private def Step5IIIWalk_Tc (t : ℝ) :
    ((Fin 2 → Zd d (sz.L n)) → ℂ) →L[ℂ] ((Fin 2 → Zd d (sz.L n)) → ℂ) :=
  pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) t) +
    pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) t)

variable {C} {n} {σ}

private theorem Step5IIIWalk_Uc_apply (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (v w : ℝ) :
    Step5IIIWalk_Uc C n σ v w A = Step2Gen_UN C n σ v w A := by
  funext a
  rw [Step5IIIWalk_Uc, mul_apply_eq_comp]
  simp only [Step2Gen_UN, pfStep5Grid_slot_apply, Fin.prod_univ_two]
  rw [pfStep5Grid_sum2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pfStep5Grid_update2', pfStep5Grid_update2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem Step5IIIWalk_Tc_apply (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (t : ℝ) :
    Step5IIIWalk_Tc C n σ t A = Step2Gen_ThetaN C n σ t A := by
  funext a
  simp only [Step5IIIWalk_Tc, Step2Gen_ThetaN, Fin.sum_univ_two, Pi.add_apply, _root_.add_apply, pfStep5Grid_slot_apply]

end Ops

/-! ### Norm bounds from K1-K3 -/

section Norms

variable {σ : Fin 2 → Bool} (hker : GridRepTailGen_Ker C n)
include hker

/-- the slot operator of `θ_x`, `0 ≤ x ≤ ut < 1`, has norm `≤ (1 - ut)⁻¹`. -/
private theorem Step5IIIWalk_norm_slotTheta (i : Fin 2) {x ut : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) x)‖ ≤ (1 - ut)⁻¹ :=
  (pfStep5Grid_norm_slot d (sz.L n) i _).trans
    ((Step5IIIWalk_theta_norm hker _ _ hx0 (lt_of_le_of_lt hxu hu1)).trans (pfStep5Grid_inv_le hxu hu1))

private theorem Step5IIIWalk_norm_Tc {x ut : ℝ} (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖Step5IIIWalk_Tc C n σ x‖ ≤ 2 * (1 - ut)⁻¹ := by
  unfold Step5IIIWalk_Tc
  have h0 := Step5IIIWalk_norm_slotTheta hker (σ := σ) 0 hx0 hxu hu1
  have h1 := Step5IIIWalk_norm_slotTheta hker (σ := σ) 1 hx0 hxu hu1
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (1 - ut)⁻¹ + (1 - ut)⁻¹ := add_le_add h0 h1
    _ = 2 * (1 - ut)⁻¹ := by ring

/-- `‖θ_w - θ_v‖ ≤ (w - v) (1 - ut)⁻²` (the resolvent identity). -/
private theorem Step5IIIWalk_theta_sub_norm (σ' σ'' : Bool) {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut)
    (hu1 : ut < 1) :
    ‖Step2Gen_thetaKer C n σ' σ'' w - Step2Gen_thetaKer C n σ' σ'' v‖ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hv1 : v < 1 := lt_of_le_of_lt hvw hw1
  rw [Step5IIIWalk_theta_resolvent hker σ' σ'' hv0 hv1 (hv0.trans hvw) hw1, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  refine mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans ?_) (by linarith)
  have h1 := (Step5IIIWalk_theta_norm hker σ' σ'' (hv0.trans hvw) hw1).trans (pfStep5Grid_inv_le hwu hu1)
  have h2 := (Step5IIIWalk_theta_norm hker σ' σ'' hv0 hv1).trans (pfStep5Grid_inv_le (hvw.trans hwu) hu1)
  calc _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) (inv_nonneg.2 (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem Step5IIIWalk_norm_Tc_sub {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖Step5IIIWalk_Tc C n σ w - Step5IIIWalk_Tc C n σ v‖ ≤ 2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) w -
      Step2Gen_thetaKer C n (σ i) (σ (finRotate 2 i)) v)‖ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 := fun i =>
    (pfStep5Grid_norm_slot d (sz.L n) i _).trans (Step5IIIWalk_theta_sub_norm hker _ _ hv0 hvw hwu hu1)
  have e : Step5IIIWalk_Tc C n σ w - Step5IIIWalk_Tc C n σ v =
      pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w -
        Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) v) +
      pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w -
        Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) v) := by
    unfold Step5IIIWalk_Tc
    rw [pfStep5Grid_slot_sub, pfStep5Grid_slot_sub]
    abel
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 + (w - v) * ((1 - ut)⁻¹) ^ 2 := add_le_add (hB 0) (hB 1)
    _ = 2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by ring

private theorem Step5IIIWalk_norm_uKer (σ' σ'' : Bool) {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut)
    (hu1 : ut < 1) : ‖Step2Gen_uKer C n σ' σ'' v w‖ ≤ (1 - ut)⁻¹ := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have h1 : (1 - v) / (1 - w) ≤ (1 - w)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.mpr (by linarith)) (by linarith)
  have h2 : 0 ≤ (1 - v) / (1 - w) := div_nonneg (by linarith) (by linarith)
  exact (Step5IIIWalk_norm_le_rows _ h2 (hker.2.1 σ' σ'' v w hv0 hvw hw1)).trans (h1.trans (pfStep5Grid_inv_le hwu hu1))

private theorem Step5IIIWalk_norm_Uc {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖Step5IIIWalk_Uc C n σ v w‖ ≤ ((1 - ut)⁻¹) ^ 2 := by
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d (sz.L n) i (Step2Gen_uKer C n (σ i) (σ (finRotate 2 i)) v w)‖ ≤
      (1 - ut)⁻¹ := fun i =>
    (pfStep5Grid_norm_slot d (sz.L n) i _).trans (Step5IIIWalk_norm_uKer hker _ _ hv0 hvw hwu hu1)
  unfold Step5IIIWalk_Uc
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul (hB 0) (hB 1) (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem Step5IIIWalk_Uc_expand {v w : ℝ} (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Step5IIIWalk_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • Step5IIIWalk_Tc C n σ w =
      (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
  unfold Step5IIIWalk_Uc Step5IIIWalk_Tc
  rw [Step5IIIWalk_uKer_eq hker _ _ hw0 hw1 v, Step5IIIWalk_uKer_eq hker _ _ hw0 hw1 v,
    pfStep5Grid_slot_add, pfStep5Grid_slot_add, pfStep5Grid_slot_smul, pfStep5Grid_slot_smul,
    pfStep5Grid_slot_one, pfStep5Grid_slot_one]
  exact pfStep5Grid_alg _ _ _

private theorem Step5IIIWalk_norm_quad {w ut : ℝ} (hw0 : 0 ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)‖ ≤
      ((1 - ut)⁻¹) ^ 2 := by
  have h0 := Step5IIIWalk_norm_slotTheta hker (σ := σ) 0 hw0 hwu hu1
  have h1 := Step5IIIWalk_norm_slotTheta hker (σ := σ) 1 hw0 hwu hu1
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul h0 h1 (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem Step5IIIWalk_norm_Uc_sub_one {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖Step5IIIWalk_Uc C n σ v w - 1‖ ≤ 3 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hB1 : 1 ≤ (1 - ut)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  have hδ0 : 0 ≤ w - v := by linarith
  have hδ1 : w - v ≤ 1 := by
    have : 0 ≤ v := hv0
    nlinarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := Step5IIIWalk_Uc_expand hker (σ := σ) (v := v) hw0 hw1
  have e' : Step5IIIWalk_Uc C n σ v w - 1 =
      ((w - v : ℝ) : ℂ) • Step5IIIWalk_Tc C n σ w + (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
    rw [← e]; abel
  rw [e']
  have hT := Step5IIIWalk_norm_Tc hker (σ := σ) hw0 hwu hu1
  have hQ := Step5IIIWalk_norm_quad hker (σ := σ) hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * (2 * B) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ ≤ 3 * (w - v) * B ^ 2 := by
        have h1 : B ≤ B ^ 2 := by nlinarith
        have h2 : (w - v) * (w - v) * B ^ 2 ≤ 1 * (w - v) * B ^ 2 := by
          have := mul_le_mul_of_nonneg_right hδ1 hδ0
          have := mul_le_mul_of_nonneg_right this (sq_nonneg B)
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hδ0]

private theorem Step5IIIWalk_norm_Uc_sub_one_Tc {v w ut : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖Step5IIIWalk_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • Step5IIIWalk_Tc C n σ v‖ ≤
      3 * (w - v) ^ 2 * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hδ0 : 0 ≤ w - v := by linarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := Step5IIIWalk_Uc_expand hker (σ := σ) (v := v) hw0 hw1
  have e' : Step5IIIWalk_Uc C n σ v w - 1 - ((w - v : ℝ) : ℂ) • Step5IIIWalk_Tc C n σ v =
      ((w - v : ℝ) : ℂ) • (Step5IIIWalk_Tc C n σ w - Step5IIIWalk_Tc C n σ v) +
        (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d (sz.L n) 0 (Step2Gen_thetaKer C n (σ 0) (σ (finRotate 2 0)) w) *
          pfStep5Grid_slot d (sz.L n) 1 (Step2Gen_thetaKer C n (σ 1) (σ (finRotate 2 1)) w)) := by
    rw [← e, smul_sub]; abel
  rw [e']
  have hT := Step5IIIWalk_norm_Tc_sub hker (σ := σ) hv0 hvw hwu hu1
  have hQ := Step5IIIWalk_norm_quad hker (σ := σ) hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * (2 * (w - v) * B ^ 2) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = 3 * (w - v) ^ 2 * B ^ 2 := by ring

end Norms

/-! ### The Duhamel form -/

/-- **The Duhamel form `(int_K-L_ST)` at the kernel `Step2Gen_UN` of a carrier with K1-K3** (deterministic, any 2-index tensors; band
`pfStep5Grid_duhamel`, `Induction/PfStep5Grid.lean:892`, with the energy bound and the unit modulus of `m` replaced by the kernel class): on a grid
`u_{j+1} = u_j + Δ`, `0 ≤ u_0`, `u_k < 1`, if `A_j = A_0 + Δ Σ_{i<j} (Θ^{(2)}_{u_i,σ} A_i + F_i) + Rem_j + Mart_j` for `j ≤ k` with
`|A_j| ≤ M`, `|Rem_j| ≤ R`, then
`|A_k - 𝒰_{u_0,u_k} A_0 - Δ Σ_{j<k} 𝒰_{u_j,u_k} F_j - Σ_{j<k} 𝒰_{u_j,u_k}(Mart_{j+1} - Mart_j)| ≤ 64 (1-u_k)^{-7} (R + Δ M)`. -/
theorem Step5IIIWalk_duhamel (hker : GridRepTailGen_Ker C n) (Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (hk : u k < 1)
    (hA : ∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) (hRem : ∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R)
    (hrec : ∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (Step2Gen_ThetaN C n σ (u i) (A i) b + F i b) + Rem j b + Mart j b)
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖A k a - Step2Gen_UN C n σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k, Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) := by
  have hmono : Monotone u := monotone_nat_of_le_succ fun j => by rw [hu j]; linarith
  have hform : ∀ j, u j = u 0 + j * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hu j, ih]; push_cast; ring
  have hunn : ∀ j, 0 ≤ u j := fun j => hu0.trans (hmono (Nat.zero_le j))
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => lt_of_le_of_lt (hmono hj) hk
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := hform k
    have := hunn 0
    linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRem 0 (Nat.zero_le _) 0)
  have hB : 1 ≤ ((1 - u k)⁻¹) := by
    rw [one_le_inv₀ (by linarith [hunn k])]
    linarith [hunn k]
  have hB0 : 0 ≤ ((1 - u k)⁻¹) := by linarith
  have hrhs : 0 ≤ 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) := by positivity
  cases k with
  | zero =>
    have h0 : Step2Gen_UN C n σ (u 0) (u 0) (A 0) = A 0 := Step2Gen_UN_self C n hker.1 σ (hunn 0) hk (A 0)
    simpa [h0] using hrhs
  | succ m =>
    have hu1 : u (m + 1) < 1 := hk
    have hmΔ : ((m : ℝ) + 1) * Δ ≤ 1 := by exact_mod_cast hkΔ
    have hd : ∀ j, u (j + 1) - u j = Δ := fun j => by rw [hu j]; ring
    have hPk : Step5IIIWalk_Uc C n σ (u (m + 1)) (u (m + 1)) = 1 :=
      ContinuousLinearMap.ext fun B => by
        rw [Step5IIIWalk_Uc_apply, one_apply_eq_self]
        exact Step2Gen_UN_self C n hker.1 σ (hunn _) hu1 B
    have hPX : ∀ j, j < m + 1 → Step5IIIWalk_Uc C n σ (u j) (u (m + 1)) =
        Step5IIIWalk_Uc C n σ (u (j + 1)) (u (m + 1)) * Step5IIIWalk_Uc C n σ (u j) (u (j + 1)) := by
      intro j hj
      refine ContinuousLinearMap.ext fun B => ?_
      rw [mul_apply_eq_comp, Step5IIIWalk_Uc_apply, Step5IIIWalk_Uc_apply, Step5IIIWalk_Uc_apply]
      exact (Step2Gen_UN_comp C n hker.1 σ (u := u j) (v := u (j + 1)) (w := u (m + 1))
        (hunn _) (hlt _ hj) (hunn _) hu1 B).symm
    have hP : ∀ j, j ≤ m + 1 → ‖Step5IIIWalk_Uc C n σ (u j) (u (m + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => Step5IIIWalk_norm_Uc hker (hunn j) (hmono hj) le_rfl hu1
    have hXn : ∀ j, j < m + 1 → ‖Step5IIIWalk_Uc C n σ (u j) (u (j + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => Step5IIIWalk_norm_Uc hker (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
    have hX1 : ∀ j, j < m + 1 → ‖Step5IIIWalk_Uc C n σ (u j) (u (j + 1)) - 1‖ ≤
        3 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := Step5IIIWalk_norm_Uc_sub_one hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hX2 : ∀ j, j < m + 1 → ‖Step5IIIWalk_Uc C n σ (u j) (u (j + 1)) - 1 -
        (Δ : ℂ) • Step5IIIWalk_Tc C n σ (u j)‖ ≤ 3 * Δ ^ 2 * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := Step5IIIWalk_norm_Uc_sub_one_Tc hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hΘ : ∀ j, j < m + 1 → ‖Step5IIIWalk_Tc C n σ (u j)‖ ≤ 2 * ((1 - u (m + 1))⁻¹) :=
      fun j hj => Step5IIIWalk_norm_Tc hker (hunn j) (hmono (Nat.le_of_lt hj)) hu1
    have hΘΘ : ∀ j, j + 1 < m + 1 → ‖Step5IIIWalk_Tc C n σ (u j) -
        Step5IIIWalk_Tc C n σ (u (j + 1))‖ ≤ 2 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      rw [norm_sub_rev]
      have := Step5IIIWalk_norm_Tc_sub hker (σ := σ) (hunn j) (hmono (Nat.le_succ j)) (hmono hj.le) hu1
      rwa [hd] at this
    have hA' : ∀ j, j ≤ m + 1 → ‖A j‖ ≤ M := fun j hj => (pi_norm_le_iff_of_nonneg hM).mpr (hA j hj)
    have hRem' : ∀ j, j ≤ m + 1 → ‖Rem j‖ ≤ R := fun j hj => (pi_norm_le_iff_of_nonneg hR).mpr (hRem j hj)
    have hrec' : ∀ j, j < m + 1 → A (j + 1) - A j =
        (Δ : ℂ) • (Step5IIIWalk_Tc C n σ (u j) (A j) + F j) + (Rem (j + 1) - Rem j) +
          (Mart (j + 1) - Mart j) := by
      intro j hj
      funext b
      have h1 := hrec (j + 1) (by omega) b
      have h0 := hrec j (by omega) b
      rw [Finset.sum_range_succ] at h1
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Step5IIIWalk_Tc_apply]
      linear_combination h1 - h0
    have habs := pfStep5Grid_abs (E := (Fin 2 → Zd d (sz.L n)) → ℂ) m Δ ((1 - u (m + 1))⁻¹) M R hB hΔ hmΔ
      (fun j => Step5IIIWalk_Uc C n σ (u j) (u (m + 1)))
      (fun j => Step5IIIWalk_Uc C n σ (u j) (u (j + 1)))
      (fun j => Step5IIIWalk_Tc C n σ (u j)) A F Rem Mart hPk hPX hP hXn hX1 hX2 hΘ hΘΘ hA' hRem' hrec'
    refine le_trans ?_ habs
    refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ a)
    congr 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Step5IIIWalk_Uc_apply]
    rw [Finset.mul_sum]
    rfl

end Duhamel

/-! ## 5. The a priori bound -/

section Apriori

/-- `‖𝓛^{(ℓ)}_{z,σ,a}(H)‖ ≤ η^{-ℓ}` for Hermitian `H` and `η ≤ |Im z|` (band `norm_loopFine_crudeN`, `Induction/NQGood1.lean:916`, at a general
spectral parameter). -/
theorem Step5IIIWalk_norm_loopFine_le {d L W : ℕ} [NeZero L] [NeZero W] {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hM : M.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (σ : Fin ℓ → Bool)
    (a : Fin ℓ → Zd d L) : ‖loopFine d L W M z σ a‖ ≤ η⁻¹ ^ ℓ := by
  have hMb : (blockMat d L W M).IsHermitian := hM.submatrix _
  have hwf : (loopOf σ a).σ.length = (loopOf σ a).a.length := by simp [loopOf]
  have hlen : (loopOf σ a).a.length = ℓ := by simp [loopOf]
  have h := RBM.Ind.norm_gloop_le_of_le_abs_im hMb hη hz (loopOf σ a) hwf (by rw [hlen]; exact hℓ)
  rw [hlen] at h
  unfold loopFine
  rw [loopM_eq_loopL]
  refine h.trans ?_
  have hW : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne W)
  have hWi : (((W : ℝ) ^ d)⁻¹) ^ (ℓ - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW))
  have h0 : 0 ≤ η⁻¹ ^ ℓ := by positivity
  calc η⁻¹ ^ ℓ * (((W : ℝ) ^ d)⁻¹) ^ (ℓ - 1) ≤ η⁻¹ ^ ℓ * 1 := mul_le_mul_of_nonneg_left hWi h0
    _ = _ := mul_one _

/-- **The crude bound of `𝒦^{(2)}` along a flow, uniformly in `u ∈ [0, t_n]`**: stage K (`baKbound_holds`, `max |𝒦^{(2)}_{u,σ,a}| ≺ B_{u,0}`) read as a
deterministic fact, `𝒦` not depending on the sample (`Step5IIIGood_det_of_prec`, `Step5IIIGood_uniform`). -/
theorem Step5IIIWalk_Kcrude {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      2 ≤ sz.size n → ‖(baFMz sz z).K n u σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * sz.Bctl n u := by
  have key := Step5IIIGood_uniform (s := fun _ => (0 : ℝ)) (t := t) (fun n => ht0 n)
    (fun n u => 2 ≤ sz.size n → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
      ‖(baFMz sz z).K n u σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) * sz.Bctl n u) fun τ hτ => ?_
  · filter_upwards [key] with n hn u hu0 hut σ a h2
    exact hn ⟨u, hu0, hut⟩ h2 σ a
  · have hK := baKbound_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ (fun n => (hτ n).1)
      (fun n => ((hτ n).2.trans (htT n)).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)) 2 (by norm_num)
    have := Step5IIIGood_det_of_prec (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) => ‖(baFMz sz z).K n (τ n) p.1 p.2‖)
      (fun n _ => sz.Bctl n (τ n) ^ (2 - 1)) hK (half_pos one_pos)
    filter_upwards [this] with n hn h2 σ a
    simpa using hn h2 (σ, a)

/-- **The a priori bound** (band `pfStep5_apriori`, `Induction/PfStep5.lean:1269`): eventually, for `0 ≤ u ≤ t_n ≤ t₀`, Hermitian `H` and every label,
`‖(𝓛 - 𝒦)^{(2)}_{u,σ,a}(H)‖ ≤ N³`.  `‖𝓛^{(2)}‖ ≤ η_u⁻² ≤ (16N)²` (`gridRepTailBA_eta`, the resolvent bound) and `‖𝒦^{(2)}‖ ≤ N^{1/2} B_{u,0}`,
`B_{u,0} ≤ 2 (W^d (1-u))⁻¹ ≤ 32 N` (`gridRepTailGen_window_BA`). -/
theorem Step5IIIWalk_apriori {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d) (z : ℕ → ℂ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
        ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
          ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hNε : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ ε) atTop atTop := (tendsto_rpow_atTop hε).comp hsize
  filter_upwards [Step5IIIWalk_Kcrude hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow t ht0 htT, hNε.eventually_ge_atTop (1 / (8 * κ)),
    hsize.eventually_ge_atTop 300] with n hK hεn hN u hu0 hut H hH σ a
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hη := gridRepTailBA_eta hκ sz hflow t n (htT n) hN0 hεn u hut
  have hwin := gridRepTailGen_window_BA hκ sz hflow t n (htT n) hN0 hεn
  have hu1 : u < 1 := lt_of_le_of_lt hut hwin.1
  have hy : (1 - u)⁻¹ ≤ 16 * N := hwin.2 u hu0 hut
  have hη0 : 0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) u := lt_of_lt_of_le (by positivity) hη
  -- the `𝓛` part
  have hL : ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n u H σ a‖ ≤ (16 * N) ^ 2 := by
    have h := Step5IIIWalk_norm_loopFine_le hH (z := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) u)
      (η := 1 / (16 * N)) (by positivity) (by rw [ztOf_im, abs_of_pos hη0]; exact hη) (by norm_num : 1 ≤ 2) σ a
    rwa [one_div, inv_inv] at h
  -- the `𝒦` part
  have hKn : ‖(baFMz sz z).K n u σ a‖ ≤ N ^ (1 / 2 : ℝ) * (32 * N) := by
    have hN2 : 2 ≤ sz.size n := by
      have : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by rw [← hNdef]; linarith
      exact_mod_cast this
    have h := hK u hu0 hut σ a hN2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hN0.le _))
    refine (Step5IIIGood_Bctl_le sz n hu1).trans ?_
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
    have h1u : 0 < 1 - u := by linarith
    have : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (1 - u)⁻¹ :=
      inv_anti₀ h1u (le_mul_of_one_le_left h1u.le hW1)
    linarith
  have hs : N ^ (1 / 2 : ℝ) ≤ N := by
    calc N ^ (1 / 2 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one N
  unfold STLKMg STLMg
  calc ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n u H σ a - (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n u σ a‖
      ≤ ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).LM n u H σ a‖ +
        ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).K n u σ a‖ := norm_sub_le _ _
    _ ≤ (16 * N) ^ 2 + N ^ (1 / 2 : ℝ) * (32 * N) := add_le_add hL hKn
    _ ≤ N ^ 3 := by
        have h1 : N ^ (1 / 2 : ℝ) * (32 * N) ≤ 32 * N * N := by nlinarith [Real.rpow_nonneg hN0.le (1 / 2 : ℝ)]
        nlinarith

end Apriori

/-! ## 6. `ugenSum'` at the BA kernel -/

section UgenSum

variable {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {n : ℕ}

/-- `Step2Gen_UN` is linear in the tensor: a scalar factor comes out. -/
private theorem Step5IIIWalk_UN_smul {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (c : ℂ) (A : (Fin k → Zd d (sz.L n)) → ℂ)
    (a : Fin k → Zd d (sz.L n)) :
    Step2Gen_UN C n σ s t (fun b => c * A b) a = c * Step2Gen_UN C n σ s t A a := by
  unfold Step2Gen_UN
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `tailTD > 0` for `W > 0`. -/
private theorem Step5IIIWalk_tailTD_pos {W u D r : ℝ} (hW : 0 < W) : 0 < tailTD d W u D r := by
  unfold tailTD
  have := Real.rpow_pos_of_pos hW (-D)
  positivity

/-- One term of `ugenSum'` (band `pfStep5Alg_ugen_term`, `Induction/PfStep5Alg.lean:181`): `‖(𝒰_{v,w,σ} ∘ ℰ)_a‖ ≤ p (Cc T_{w,D'} + ((1-v)/(1-w))² W^{-D'})`
when `‖ℰ_b‖ ≤ p T_{v,D'}(|b₁-b₂|)`, from `TailtoTail` on the carrier. -/
private theorem Step5IIIWalk_ugen_term {Cc v w D' p : ℝ} (σ : Fin 2 → Bool)
    (hTT : ∀ A : (Fin 2 → Zd d (sz.L n)) → ℂ,
      (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
      ∀ a, ‖Step2Gen_UN C n σ v w A a‖ ≤ Cc * tailTD d ((sz.W n : ℕ) : ℝ) w D' (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - v) / (1 - w)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (hW : 0 < ((sz.W n : ℕ) : ℝ)) (ℰ : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hℰ : ∀ b, ‖ℰ b‖ ≤ p * tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) (b 0 - b 1) : ℝ))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖Step2Gen_UN C n σ v w ℰ a‖ ≤
      p * (Cc * tailTD d ((sz.W n : ℕ) : ℝ) w D' (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - v) / (1 - w)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  have hT : 0 < tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) ((fun _ => 0 : Fin 2 → Zd d (sz.L n)) 0 -
      (fun _ => 0 : Fin 2 → Zd d (sz.L n)) 1) : ℝ) := Step5IIIWalk_tailTD_pos hW
  have hp0 : 0 ≤ p := by
    by_contra hneg
    have hneg := not_le.1 hneg
    have h1 := hℰ (fun _ => 0)
    have h2 := mul_neg_of_neg_of_pos hneg hT
    linarith [norm_nonneg (ℰ (fun _ => 0))]
  rcases hp0.eq_or_lt with hp | hp
  · have hz : ∀ b, ℰ b = 0 := fun b => by
      have := hℰ b
      rw [← hp, zero_mul] at this
      exact norm_le_zero_iff.1 this
    have h0 : Step2Gen_UN C n σ v w ℰ a = 0 := by
      unfold Step2Gen_UN
      simp [hz]
    rw [h0, norm_zero, ← hp, zero_mul]
  · set A : (Fin 2 → Zd d (sz.L n)) → ℂ := fun b => (((p⁻¹ : ℝ)) : ℂ) * ℰ b with hA
    have hAb : ∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := fun b => by
      rw [hA, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hp.le)]
      calc p⁻¹ * ‖ℰ b‖ ≤ p⁻¹ * (p * tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hℰ b) (inv_nonneg.2 hp.le)
        _ = tailTD d ((sz.W n : ℕ) : ℝ) v D' (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := by field_simp
    have hℰA : ℰ = fun b => ((p : ℝ) : ℂ) * A b := by
      funext b
      rw [hA]
      simp only
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne', Complex.ofReal_one, one_mul]
    have hUN := hTT A hAb a
    have hUg : Step2Gen_UN C n σ v w ℰ a = ((p : ℝ) : ℂ) * Step2Gen_UN C n σ v w A a := by
      rw [hℰA]
      exact Step5IIIWalk_UN_smul σ v w ((p : ℝ) : ℂ) A a
    rw [hUg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
    exact mul_le_mul_of_nonneg_left hUN hp.le

/-- **`ugenSum'` at the BA kernel** (band `pfStep5Alg_ugenSum'`, `Induction/PfStep5Alg.lean:236`, with the constant `Cc` of
`baStep5IIIKernel_at_flow` and the levels `D_j`): for nonnegative weights `c_j` and tensors `ℰ_j` dominated by `p_j T_{u_j,D_j}`, the weighted sum
of `𝒰_{u_j,u_k,σ} ∘ ℰ_j` is dominated by `Σ c_j p_j (Cc T_{u_k,D_j} + ((1-u_j)/(1-u_k))² W^{-D_j})`. -/
theorem Step5IIIWalk_ugenSum {Cc : ℝ}
    (hTT : ∀ D s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
        (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
        ∀ a, ‖Step2Gen_UN C n σ s t A a‖ ≤ Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
          ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hW : 0 < ((sz.W n : ℕ) : ℝ)) (σ : Fin 2 → Bool) (k : ℕ) (u c p D : ℕ → ℝ) (ℰ : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hu0 : 0 ≤ u 0) (hmono : ∀ j, u j ≤ u (j + 1)) (hk : u k < 1) (hgk : sz.lam n ^ 2 ≤ 1 - u k) (hc : ∀ j, 0 ≤ c j)
    (hℰ : ∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d ((sz.W n : ℕ) : ℝ) (u j) (D j) (zdistInf d (sz.L n) (b 0 - b 1) : ℝ))
    (a : Fin 2 → Zd d (sz.L n)) :
    ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖ ≤
      ∑ j ∈ Finset.range k, c j * p j *
        (Cc * tailTD d ((sz.W n : ℕ) : ℝ) (u k) (D j) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
          ((1 - u j) / (1 - u k)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D j))) := by
  have hm : Monotone u := monotone_nat_of_le_succ hmono
  have term : ∀ j ∈ Finset.range k, ‖Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖ ≤
      p j * (Cc * tailTD d ((sz.W n : ℕ) : ℝ) (u k) (D j) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
        ((1 - u j) / (1 - u k)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D j))) := fun j hj => by
    have hjk : j < k := Finset.mem_range.1 hj
    exact Step5IIIWalk_ugen_term σ (hTT (D j) (u j) (u k) (hu0.trans (hm (Nat.zero_le j))) (hm hjk.le) hk hgk σ) hW (ℰ j)
      (hℰ j hjk) a
  calc ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖
      ≤ ∑ j ∈ Finset.range k, ‖((c j : ℝ) : ℂ) * Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖ := norm_sum_le _ _
    _ = ∑ j ∈ Finset.range k, c j * ‖Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖ :=
        Finset.sum_congr rfl fun j _ => by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc j)]
    _ ≤ ∑ j ∈ Finset.range k, c j * p j *
          (Cc * tailTD d ((sz.W n : ℕ) : ℝ) (u k) (D j) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
            ((1 - u j) / (1 - u k)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D j))) :=
        Finset.sum_le_sum fun j hj => by
          calc c j * ‖Step2Gen_UN C n σ (u j) (u k) (ℰ j) a‖
              ≤ c j * (p j * (Cc * tailTD d ((sz.W n : ℕ) : ℝ) (u k) (D j) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
                ((1 - u j) / (1 - u k)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-(D j)))) :=
                mul_le_mul_of_nonneg_left (term j hj) (hc j)
            _ = _ := by ring

end UgenSum

/-! ## 7. The martingale term, real part -/

/-- **The martingale term, real part** (band `pfStep5_mart_real`, `Induction/PfStep5.lean:737`, with the quadratic-variation constant `C7` a parameter: `Cq` of `baStep5IIITailSqQV_holds`): from `x_j ≤ (2 C₇ p_j + 1) T²` for the quadratic variations, the
grid sums and `N^{-D_g} ≤ T²`, the tail of conjunct 4 is at most `Q (r₁ log W + 2 r₂ X + 2) T`. -/
theorem Step5IIIWalk_mart_real (d : ℕ) (C7 : ℝ) (hC70 : 0 < C7) (k : ℕ) (u : ℕ → ℝ) (Δ g W Q ε₀ T q Nm Mn : ℝ)
    (xx : ℕ → ℝ) (hg : 0 < g) (hW : 1 < W) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1) (hgk : g ^ 2 ≤ 1 - u k)
    (hm : 1 ≤ g ^ 2 * W ^ d) (hlog : 4 ≤ Real.log W) (hε₀ : 0 ≤ ε₀) (hQ : 1 ≤ Q) (hT : 0 ≤ T)
    (hNm : Nm ≤ T ^ 2) (hqQ : q ≤ Real.sqrt Q)
    (hx : ∀ j, j < k → xx j ≤ (2 * C7 * (Q * ((1 - u j)⁻¹ +
        W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2)
    (hMn : Mn ≤ q * (∑ j ∈ Finset.range k, Δ * xx j + Nm) ^ (1 / 2 : ℝ)) :
    Mn ≤ Q * (Real.sqrt (2 * C7 * d) * Real.log W +
      2 * Real.sqrt (C7) * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) + 2) * T := by
  rw [← Real.sqrt_eq_rpow] at hMn
  set X : ℝ := W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) with hXdef
  set Λ : ℝ := Real.log W with hΛdef
  have hΛ : 1 ≤ Λ := by linarith
  have hW0 : 0 < W := by linarith
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg (by positivity) _)
  have hQ0 : 0 < Q := by linarith
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hform : ∀ j, u j = u 0 + j * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hu j, ih]; push_cast; ring
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := hform k
    linarith
  obtain hsum := pfStep5_mart_sum d k u Δ g W ε₀ hg hW hΔ hu0 hu huk hgk hm hε₀
  -- the sum of the quadratic variations
  have hS : ∑ j ∈ Finset.range k, Δ * xx j ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) := by
    calc ∑ j ∈ Finset.range k, Δ * xx j
        ≤ ∑ j ∈ Finset.range k, Δ * ((2 * C7 * (Q * ((1 - u j)⁻¹ +
            W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2) :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hx j (Finset.mem_range.1 hj)) hΔ
      _ = T ^ 2 * (2 * C7 * Q * (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹ +
            W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) +
            (k : ℝ) * Δ) := by
          have e : ∀ j, Δ * ((2 * C7 * (Q * ((1 - u j)⁻¹ +
              W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2) =
              T ^ 2 * (2 * C7 * Q * (Δ * ((1 - u j)⁻¹ +
              W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + Δ) :=
            fun j => by ring
          rw [Finset.sum_congr rfl (fun j _ => e j)]
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg T)
          have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * C7 * Q)
          linarith
  -- the sum plus `Nm`
  have hSN : ∑ j ∈ Finset.range k, Δ * xx j + Nm ≤
      T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) := by
    have e : T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) =
        T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) + T ^ 2 := by ring
    rw [e]
    linarith
  set r₁ : ℝ := Real.sqrt (2 * C7 * d) with hr₁
  set r₂ : ℝ := Real.sqrt C7 with hr₂
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr₁sq : r₁ ^ 2 = 2 * C7 * d := Real.sq_sqrt (by positivity)
  have hr₂sq : r₂ ^ 2 = C7 := Real.sq_sqrt hC70.le
  have hr₁0 : 0 ≤ r₁ := Real.sqrt_nonneg _
  have hr₂0 : 0 ≤ r₂ := Real.sqrt_nonneg _
  set s : ℝ := r₁ * Λ + 2 * r₂ * X + 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hZ : 2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2 ≤ Q * s ^ 2 :=
    pfStep5_Zineq hd0 hC70.le hQ hΛ hX0 hr₁0 hr₂0 hr₁sq hr₂sq
  have hsq : Real.sqrt (∑ j ∈ Finset.range k, Δ * xx j + Nm) ≤ T * (Real.sqrt Q * s) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc ∑ j ∈ Finset.range k, Δ * xx j + Nm
        ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) := hSN
      _ ≤ T ^ 2 * (Q * s ^ 2) := mul_le_mul_of_nonneg_left hZ (sq_nonneg T)
      _ = (T * (Real.sqrt Q * s)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hQ0.le]
  have hQQ : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0.le
  calc Mn ≤ q * Real.sqrt (∑ j ∈ Finset.range k, Δ * xx j + Nm) := hMn
    _ ≤ Real.sqrt Q * (T * (Real.sqrt Q * s)) :=
        mul_le_mul hqQ hsq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt Q * Real.sqrt Q) * s * T := by ring
    _ = Q * s * T := by rw [hQQ]

/-! ## 8. The four-term assembly -/

section Assemble

/-- The total constant of the closure: `7 c + 3 + c d + √(2 Cq d) + 2 √Cq`, `c = Cc + 1` (band `pfStep5_Ctot`, `Induction/PfStep5.lean:490`, with the
constants `Cc` of `TailtoTail` and `Cq` of the quadratic variation at BA). -/
def Step5IIIWalk_Ctot (d : ℕ) (Cc Cq : ℝ) : ℝ :=
  7 * (Cc + 1) + 3 + (Cc + 1) * d + Real.sqrt (2 * Cq * d) + 2 * Real.sqrt Cq

theorem Step5IIIWalk_Ctot_ge {d : ℕ} {Cc Cq : ℝ} (hCc : 0 < Cc) : 4 ≤ Step5IIIWalk_Ctot d Cc Cq := by
  unfold Step5IIIWalk_Ctot
  have := Real.sqrt_nonneg (2 * Cq * d)
  have := Real.sqrt_nonneg Cq
  have : (0 : ℝ) ≤ (Cc + 1) * d := by positivity
  linarith

/-- **The assembly of the pathwise estimate at the BA kernel** (band `pfStep5_assemble`, `Induction/PfStep5.lean:857`): on the grid
`u_{j+1} = u_j + Δ`, `A_k` is dominated by `Q C_tot (1 + log W + X) T̂_k`, `T̂_k = T_{u_k, D_{u_k}}`, `D_u = D* + 2 log_W (1-u)`.  The four terms are
the initial term (`TailtoTail`, hypothesis `hI`), the drift (`Step5IIIWalk_ugenSum` and `pfStep5_drift_sum`, hypothesis `hF`), the martingale
(hypothesis `hMt`, from `Step5IIIWalk_mart_real`) and the Duhamel remainder (`Step5IIIWalk_duhamel`, hypothesis `hRm`). -/
theorem Step5IIIWalk_assemble {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {n : ℕ} (hker : GridRepTailGen_Ker C n) {Cc Cq : ℝ}
    (hCc : 0 < Cc)
    (hTT : ∀ D s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → sz.lam n ^ 2 ≤ 1 - t →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
        (∀ b, ‖A b‖ ≤ tailTD d ((sz.W n : ℕ) : ℝ) s D (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) →
        ∀ a, ‖Step2Gen_UN C n σ s t A a‖ ≤ Cc * tailTD d ((sz.W n : ℕ) : ℝ) t D (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
          ((1 - s) / (1 - t)) ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D))
    (Δ M R Q ε₀ Dst : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ) (A F Rem Mart : ℕ → (Fin 2 → Zd d (sz.L n)) → ℂ)
    (hg : 0 < sz.lam n) (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1) (hgk : sz.lam n ^ 2 ≤ 1 - u k)
    (hm : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hQ : 1 ≤ Q) (hε₀ : 0 ≤ ε₀)
    (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hA : ∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) (hRem : ∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R)
    (hrec : ∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (Step2Gen_ThetaN C n σ (u i) (A i) b + F i b) + Rem j b + Mart j b)
    (hF : ∀ j, j < k → ∀ b, ‖F j b‖ ≤ Q * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) *
        tailTD d ((sz.W n : ℕ) : ℝ) (u j) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u j)) (zdistInf d (sz.L n) (b 0 - b 1) : ℝ))
    (hI : ∀ b, ‖A 0 b‖ ≤ 4 * Q *
        tailTD d ((sz.W n : ℕ) : ℝ) (u 0) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u 0)) (zdistInf d (sz.L n) (b 0 - b 1) : ℝ))
    (hMt : ∀ a, ‖∑ j ∈ Finset.range k,
        Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
        Q * (Real.sqrt (2 * Cq * d) * Real.log ((sz.W n : ℕ) : ℝ) + 2 * Real.sqrt Cq *
          (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ))) + 2) *
        tailTD d ((sz.W n : ℕ) : ℝ) (u k) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u k)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))
    (hRm : 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dst)) :
    ∀ a, ‖A k a‖ ≤ Q * Step5IIIWalk_Ctot d Cc Cq *
      (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ))) *
      tailTD d ((sz.W n : ℕ) : ℝ) (u k) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u k)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := by
  intro a
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set g : ℝ := sz.lam n with hgdef
  have hW0 : 0 < W := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have h1k : 0 < 1 - u k := lt_of_lt_of_le hg2 hgk
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hMono : Monotone u := monotone_nat_of_le_succ hmono
  have hunn : ∀ j, 0 ≤ u j := fun j => hu0.trans (hMono (Nat.zero_le j))
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => lt_of_le_of_lt (hMono hj) huk
  have hlvl := pfStep5Grid_level d W Dst
  -- `T̂_k`
  set Th : ℝ := tailTD d W (u k) (PfStep5Grid_level W Dst (u k)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) with hThdef
  have hTh0 : 0 ≤ Th := pfStep5_tailTD_nonneg hW0.le
  have hTfl : W ^ (-(PfStep5Grid_level W Dst (u k))) ≤ Th := pfStep5_tailTD_floor
  -- the level at the time `u_j` against the last time
  have hlev : ∀ j, j ≤ k → PfStep5Grid_level W Dst (u k) ≤ PfStep5Grid_level W Dst (u j) ∧
      ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j))) =
        W ^ (-(PfStep5Grid_level W Dst (u k))) := by
    intro j hj
    have hj1 : 0 < 1 - u j := by linarith [hlt j hj]
    obtain ⟨-, h2, -, -⟩ := hlvl (u j) (u k) hW (hMono hj) huk
    obtain ⟨hjj, -, -, -⟩ := hlvl (u j) (u j) hW le_rfl (hlt j hj)
    obtain ⟨hjk, -, -, -⟩ := hlvl (u j) (u k) hW (hMono hj) huk
    refine ⟨h2, ?_⟩
    rw [hjj, hjk]
    field_simp
  -- (1) the initial term
  have hT1 : ‖Step2Gen_UN C n σ (u 0) (u k) (A 0) a‖ ≤ 4 * Q * (Cc + 1) * Th := by
    have h := Step5IIIWalk_ugenSum hTT hW0 σ 1 (fun j => if j = 0 then u 0 else u k) (fun _ => 1) (fun _ => 4 * Q)
      (fun _ => PfStep5Grid_level W Dst (u 0)) (fun _ => A 0)
      (by simpa using hu0) (fun j => by
        by_cases hj : j = 0
        · subst hj; simpa using hMono (Nat.zero_le k)
        · simp [hj])
      (by simpa using huk) (by simpa using hgk) (fun _ => zero_le_one) (fun j hj b => by
        have : j = 0 := by omega
        subst this
        simpa using hI b) a
    simp only [Finset.sum_range_one, Nat.one_ne_zero, ↓reduceIte, one_mul, Complex.ofReal_one] at h
    obtain ⟨hl1, hl2⟩ := hlev 0 (Nat.zero_le k)
    have hmono1 : tailTD d W (u k) (PfStep5Grid_level W Dst (u 0)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ Th :=
      pfStep5_tailTD_mono hW.le hl1
    have hmono2 : ((1 - u 0) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u 0))) ≤ Th :=
      hl2.le.trans hTfl
    calc ‖Step2Gen_UN C n σ (u 0) (u k) (A 0) a‖
        ≤ 4 * Q * (Cc * tailTD d W (u k) (PfStep5Grid_level W Dst (u 0))
            (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) + ((1 - u 0) / (1 - u k)) ^ 2 *
            W ^ (-(PfStep5Grid_level W Dst (u 0)))) := h
      _ ≤ 4 * Q * (Cc * Th + Th) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact add_le_add (mul_le_mul_of_nonneg_left hmono1 hCc.le) hmono2
      _ = 4 * Q * (Cc + 1) * Th := by ring
  -- (2) the drift term
  have hT2 : ‖∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a‖ ≤
      (Cc + 1) * Q * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th := by
    have h := Step5IIIWalk_ugenSum hTT hW0 σ k u (fun _ => Δ)
      (fun j => Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ +
        W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)))
      (fun j => PfStep5Grid_level W Dst (u j)) F hu0 hmono huk hgk (fun _ => hΔ) hF a
    refine h.trans ?_
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hWd : 0 < W ^ d := pow_pos hW0 d
    have hterm : ∀ j ∈ Finset.range k, Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) *
        (Cc * tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
          ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j)))) ≤
        Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) * ((Cc + 1) * Th) := by
      intro j hj
      have hjk : j ≤ k := (Finset.mem_range.1 hj).le
      obtain ⟨hl1, hl2⟩ := hlev j hjk
      have hmono1 : tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤
          Th := pfStep5_tailTD_mono hW.le hl1
      have hmono2 : ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j))) ≤ Th :=
        hl2.le.trans hTfl
      have hpos : 0 ≤ Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
          (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) := by
        have : 0 < 1 - u j := by linarith [hlt j hjk]
        positivity
      refine mul_le_mul_of_nonneg_left ?_ hpos
      calc Cc * tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) +
          ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j)))
          ≤ Cc * Th + Th := add_le_add (mul_le_mul_of_nonneg_left hmono1 hCc.le) hmono2
        _ = (Cc + 1) * Th := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hds := pfStep5_drift_sum d k u Δ g W ε₀ hg hW hΔ hu0 hu huk hgk hm hε₀
    have e : ∑ j ∈ Finset.range k, Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) * ((Cc + 1) * Th) =
        Q * ((Cc + 1) * Th) * (Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ *
          ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hQT : 0 ≤ Q * ((Cc + 1) * Th) := by positivity
    calc Q * ((Cc + 1) * Th) * (Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ *
          ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)))
        ≤ Q * ((Cc + 1) * Th) * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hds hQT
      _ = (Cc + 1) * Q * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th := by
          ring
  -- (3) the remainder
  have hT4 : 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) ≤ Th := by
    refine hRm.trans ?_
    obtain ⟨-, -, h3, -⟩ := hlvl (u k) (u k) hW le_rfl huk
    exact (Real.rpow_le_rpow_of_exponent_le hW.le (neg_le_neg (h3 (hunn k)))).trans hTfl
  -- the Duhamel form and the triangle inequality
  have hdu := Step5IIIWalk_duhamel hker Δ M R σ k u A F Rem Mart hΔ hu0 hu huk hA hRem hrec a
  have hMt' := hMt a
  set U0 := Step2Gen_UN C n σ (u 0) (u k) (A 0) a with hU0
  set S1 := ∑ j ∈ Finset.range k, (Δ : ℂ) * Step2Gen_UN C n σ (u j) (u k) (F j) a with hS1
  set S2 := ∑ j ∈ Finset.range k,
    Step2Gen_UN C n σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a with hS2
  have htri : ‖A k a‖ ≤ ‖A k a - U0 - S1 - S2‖ + ‖U0‖ + ‖S1‖ + ‖S2‖ := by
    have e : A k a = (A k a - U0 - S1 - S2) + U0 + S1 + S2 := by ring
    calc ‖A k a‖ = ‖(A k a - U0 - S1 - S2) + U0 + S1 + S2‖ := by rw [← e]
      _ ≤ ‖(A k a - U0 - S1 - S2) + U0 + S1‖ + ‖S2‖ := norm_add_le _ _
      _ ≤ (‖(A k a - U0 - S1 - S2) + U0‖ + ‖S1‖) + ‖S2‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ((‖A k a - U0 - S1 - S2‖ + ‖U0‖) + ‖S1‖) + ‖S2‖ := by
          gcongr; exact norm_add_le _ _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hX0 : 0 ≤ W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg (by positivity) _)
  have hfin := pfStep5_final_ineq (Q := Q) (c := Cc + 1) (d := d) (Λ := Real.log W)
    (X := W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) (r₁ := Real.sqrt (2 * Cq * d))
    (r₂ := Real.sqrt Cq) (Th := Th) hQ (by linarith) hd0 (by linarith) hX0
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hTh0
  unfold Step5IIIWalk_Ctot
  calc ‖A k a‖ ≤ ‖A k a - U0 - S1 - S2‖ + ‖U0‖ + ‖S1‖ + ‖S2‖ := htri
    _ ≤ Th + 4 * Q * (Cc + 1) * Th + (Cc + 1) * Q * (d * Real.log W +
        3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th +
        Q * (Real.sqrt (2 * Cq * d) * Real.log W + 2 * Real.sqrt Cq *
          (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) + 2) * Th :=
        by linarith
    _ ≤ _ := by linarith

end Assemble

/-! ## 9. The per-time bounds at a grid time -/

section PerTime

/-- `lossE2wG ≥ 0` (all its factors are nonnegative once `W, L ≥ 1`). -/
theorem Step5IIIWalk_loss_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (Λ K₀ : ℝ) :
    0 ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have h1 := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d)
    (one_le_pow₀ hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * d)))
  have h2 := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d)
    (one_le_pow₀ hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (6 * d)))
  have h3 := Real.log_nonneg hW1
  unfold lossE2wG lossE2
  positivity

/-- `1 ≤ W^{2θ'} S_θ`, `S_θ = Σ_y e^{-(θ/2)√|y|}` (the term `y = 0` is `1`; `W ≥ 1`, `θ' ≥ 0`). -/
theorem Step5IIIWalk_Phi_ge_one {d : ℕ} (sz : Sizes d) (n : ℕ) {θ Cd : ℝ} (hθ : 0 ≤ θ) (hCd : 0 ≤ Cd) :
    1 ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
      ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hS : 1 ≤ ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) := by
    have h := Finset.single_le_sum (f := fun y : Zd d (sz.L n) => Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))))
      (fun y _ => (Real.exp_pos _).le) (Finset.mem_univ (0 : Zd d (sz.L n)))
    have h0 : Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) (0 : Zd d (sz.L n)) : ℝ))) = 1 := by
      rw [Step5IIIKer_zdistInf_zero]; simp
    simpa [h0] using h
  have hP : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) :=
    Real.one_le_rpow hW1 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; positivity)
  nlinarith

/-- **The per-time bounds at a grid time** (band `pfStep5_pertime`, `Induction/PfStep5.lean:1054`; deterministic, one time `u`): from the bundle
(`BAStep5IIIEScalar`, `BAStep5IIIEMatrix`) at the walk level `D` with the control `J ≤ W^{ε₀}`, `baStep5IIIEdet_holds` gives the drift
`ℰ^{(𝓛-𝒦)×(𝓛-𝒦)} + ℰ^{G̃}` of the list-loop at `KLloopOf σ b` and the quadratic variation `STeeMg` (near pairs, cut `2ℓ*`):
`≤ Q (W^{2ε₀} w y² + y + W^{3ε₀/2} w^{1/2} y^{3/2}) T` and `≤ Q (y + W^{3ε₀} w^{1/2} y^{3/2}) T²`, `y = (1-u)⁻¹`, `w = (W^d)⁻¹`, whenever
`Q ≥ lossE2wG · W^{2θ'} S_θ` (the loss of `lem_dec_calE`; the J-free factor `W^{2θ'} S_θ` of (vi), T2459f). -/
theorem Step5IIIWalk_pertime_det {d : ℕ} (hd : 3 ≤ d) {sz : Sizes d} {lam0 E : ℕ → ℝ} {n : ℕ} {u D Λ K₀ J θ Cd ε₀ Q : ℝ}
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hθ : 0 < θ) (hCd : 0 < Cd)
    (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (hε₀ : 0 ≤ ε₀)
    (hJ : J ≤ ((sz.W n : ℕ) : ℝ) ^ ε₀)
    (hQ : lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
        ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) ≤ Q) :
    (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STelklkMg (baStep2Mat sz lam0 E) n u H (KLloopOf d (sz.L n) σ b) +
          STegtMg (baStep2Mat sz lam0 E) n u H (KLloopOf d (sz.L n) σ b)‖ ≤
        Q * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 + (1 - u)⁻¹ +
          ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) * STtailTD sz n u D b) ∧
    (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ b b'‖ ≤
        Q * ((1 - u)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) * STtailTD sz n u D b ^ 2) := by
  obtain ⟨hlk, hwG, hdif⟩ := baStep5IIIEdet_holds d hd sz lam0 E n u D Λ K₀ J θ Cd H hθ hCd hs hm
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := Step5IIIEdet_W_pos sz n
  have hu1 : u < 1 := Step5IIIEdet_u_lt_one hs
  have h1u : 0 < 1 - u := by linarith
  have hy0 : 0 < (1 - u)⁻¹ := inv_pos.2 h1u
  have hWd : 0 < W ^ d := pow_pos hW0 d
  have hw0 : 0 ≤ (W ^ d)⁻¹ := inv_nonneg.2 hWd.le
  have habs : |1 - u| = 1 - u := abs_of_pos h1u
  have hJ1 := Step5IIIEdet_one_le_J hs
  have hJ0 : 0 ≤ J := by linarith
  have hT0 : ∀ b, 0 ≤ STtailTD sz n u D b := fun b => (Step5IIIGood_tail_pos sz n u D b).le
  have hJ2 : J ^ 2 ≤ W ^ (2 * ε₀) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 2)
    rwa [show ε₀ * 2 = 2 * ε₀ by ring, Real.rpow_two] at this
  have hJ32 : J ^ (3 / 2 : ℝ) ≤ W ^ (3 * ε₀ / 2) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rwa [show ε₀ * (3 / 2 : ℝ) = 3 * ε₀ / 2 by ring] at this
  have hJ3 : J ^ (3 : ℝ) ≤ W ^ (3 * ε₀) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 3)
    rwa [mul_comm] at this
  have hloss0 := Step5IIIWalk_loss_nonneg sz n Λ K₀
  have hΦ := Step5IIIWalk_Phi_ge_one sz n hθ.le hCd.le
  have hLQ : lossE2wG d (sz.L n) (sz.W n) Λ K₀ ≤ Q := (le_mul_of_one_le_right hloss0 hΦ).trans hQ
  have hQ0 : 0 ≤ Q := hloss0.trans hLQ
  have hlist := baStep2Mat_listLink sz lam0 E
  have hwy : ∀ c : ℝ, (W ^ d * |1 - u|)⁻¹ = (W ^ d)⁻¹ * (1 - u)⁻¹ := fun c => by rw [habs, mul_inv]
  refine ⟨fun σ b => ?_, fun σ b b' hnear => ?_⟩
  · have e1 := hlk σ b
    have e2 := hwG σ b
    rw [← STELKLKMg_eq_STelklkMg (baStep2Mat sz lam0 E) hlist n u H σ b,
      ← STEGtMg_eq_STegtMg (baStep2Mat sz lam0 E) hlist n u H σ b]
    have hT := hT0 b
    have c1 : ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ b‖ ≤
        Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b) := by
      refine e1.trans ?_
      rw [hwy 0]
      calc lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((W ^ d)⁻¹ * (1 - u)⁻¹ * J ^ 2)) * STtailTD sz n u D b
          ≤ Q * ((1 - u)⁻¹ * ((W ^ d)⁻¹ * (1 - u)⁻¹ * W ^ (2 * ε₀))) * STtailTD sz n u D b := by gcongr
        _ = _ := by ring
    have c2 : ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ b‖ ≤
        Q * ((1 - u)⁻¹ * STtailTD sz n u D b + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b) := by
      refine e2.trans ?_
      rw [hwy 0]
      have hite : (if (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ 2 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> norm_num
      have hyw := pfStep5_y_three_half hy0 hw0
      calc lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤
              2 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) + ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) *
              STtailTD sz n u D b)
          ≤ Q * ((1 - u)⁻¹ * (1 + ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * W ^ (3 * ε₀ / 2)) * STtailTD sz n u D b) := by
            gcongr
        _ = Q * ((1 - u)⁻¹ * STtailTD sz n u D b + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b) := by
            have e : (1 - u)⁻¹ * (1 + ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * W ^ (3 * ε₀ / 2)) =
                (1 - u)⁻¹ + W ^ (3 * ε₀ / 2) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) := by
              rw [mul_add, mul_one, ← hyw]; ring
            rw [e]; ring
    refine (norm_add_le _ _).trans ((add_le_add c1 c2).trans (le_of_eq ?_))
    ring
  · have e := hdif σ b b' hnear
    refine e.trans ?_
    rw [hwy 0]
    have hite : (if (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ 6 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hyw := pfStep5_y_three_half hy0 hw0
    have hT := hT0 b
    calc lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (W ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) *
          ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) ≤ 6 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) +
            ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D b ^ 2)
        ≤ Q * ((1 - u)⁻¹ * (1 + ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * W ^ (3 * ε₀)) * STtailTD sz n u D b ^ 2) := by
          gcongr
      _ = Q * ((1 - u)⁻¹ + W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n u D b ^ 2 := by
          have e : (1 - u)⁻¹ * (1 + ((W ^ d)⁻¹ * (1 - u)⁻¹) ^ (1 / 2 : ℝ) * W ^ (3 * ε₀)) =
              (1 - u)⁻¹ + W ^ (3 * ε₀) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) := by
            rw [mul_add, mul_one, ← hyw]; ring
          rw [mul_assoc Q, e]; ring

/-- **The per-time bounds along the flow** (band `pfStep5_perj`, `Induction/PfStep5.lean:1406`): eventually, at every `u ∈ [s_n, t_n]` and matrix `H`,
the matrix part at the crude level `D*` and `J♯(u, D_u) < W^{ε₀}` give (target 4, `baStep5III_walkLevel`, then
`Step5IIIWalk_pertime_det` at `Λ = K₀ = N^{τ'}`, `J = J♯(u, D_u)`) the drift and quadratic-variation bounds at the level `D_u`, for `Q_n` above
the loss `lossE2wG · W^{2θ'} S_θ`. -/
theorem Step5IIIWalk_pertime {d : ℕ} (hd : 3 ≤ d) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ)
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (hReg : STReg5III sz s t) (Dst τ' θ Cd ε₀ : ℝ) (hτ' : 0 ≤ τ') (hε₀ : 0 ≤ ε₀)
    (hε₀h : ε₀ ≤ 1 / 2) (hθ : 0 < θ) (hCd : 0 < Cd)
    (hfl : ∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ)))
    (Q : ℕ → ℝ)
    (hQ : ∀ᶠ n in atTop, lossE2wG d (sz.L n) (sz.W n) (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') *
        (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (((d : ℕ) : ℝ) * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) ≤ Q n) :
    ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H →
      BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H <
        ((sz.W n : ℕ) : ℝ) ^ ε₀ →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STelklkMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b) +
            STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b)‖ ≤
          Q n * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - (u : ℝ))⁻¹) ^ 2 + (1 - (u : ℝ))⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b) ∧
      (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ b b'‖ ≤
          Q n * ((1 - (u : ℝ))⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b ^ 2) := by
  filter_upwards [baStep5III_walkLevel d hd κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg Dst τ' θ Cd ε₀ hτ' hε₀h hfl, hQ] with n hn hQn u H hmat hJ
  obtain ⟨hsc, hmat'⟩ := hn u H hmat hJ
  exact Step5IIIWalk_pertime_det (d := d) hd hθ hCd hsc hmat' hε₀ hJ.le hQn

/-- **The good event at a grid index, transferred to the grid walk** (targets 1-2 and `Step2EventsGenTw_baLaw`): if `G ⊆ SeqΩ` has mass `≥ 1 - c`
and the matrix part at the realized control holds at `H = seqHflowBA ω` for `ω ∈ G`, then off an event of probability `≤ c` the grid state
`H_j = Hpath j ω` carries the matrix part at the grid time `u_j`. -/
theorem Step5IIIWalk_good_transfer {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (hK : K n ≠ 0) (D Λ K₀ θ Cd c : ℝ) (G : Set sz.SeqΩ)
    (hG : Sizes.seqP (sz.withLam 0) Gᶜ ≤ ENNReal.ofReal c)
    (hGm : ∀ ω ∈ G, BAStep5IIIEMatrix sz lam0 E n (gridTime s t K n j) D Λ K₀
        (BAStep5IIIJsharp sz lam0 E n D (gridTime s t K n j) (sz.seqHflowBA lam0 n (gridTime s t K n j) ω)) θ Cd
        (sz.seqHflowBA lam0 n (gridTime s t K n j) ω)) :
    (baStep2Mat sz lam0 E).Pp {ω | ¬ BAStep5IIIEMatrix sz lam0 E n (gridTime s t K n j) D Λ K₀
        (BAStep5IIIJsharp sz lam0 E n D (gridTime s t K n j) ((baStep2Mat sz lam0 E).Hpath s t K n j ω)) θ Cd
        ((baStep2Mat sz lam0 E).Hpath s t K n j ω)} ≤ ENNReal.ofReal c := by
  have hS := baStep5III_goodMeas d sz lam0 E n (gridTime s t K n j) D Λ K₀ θ Cd
  have hlaw := Step2EventsGenTw_baLaw sz lam0 E s t K n j hs0 hst hK _ hS.compl
  refine le_trans (le_of_eq hlaw) (le_trans (measure_mono ?_) hG)
  intro ω' hω'
  by_contra hnG
  exact hω' (hGm ω' (not_not.mp hnG))

/-- The initial term (band `pfStep5_init_le`, `Induction/PfStep5.lean:1234`, `STDecayStronggL` at `s`): `‖A_0‖ ≤ Q (B_s² e^{-√r} + W^{-D*})` gives
`‖A_0‖ ≤ 4 Q T_{s, D_s}`, `D_s = D* + 2 log_W (1-s)`. -/
theorem Step5IIIWalk_init {d : ℕ} (sz : Sizes d) (n : ℕ) {s Dst Q : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hQ : 0 ≤ Q) (a : Fin 2 → Zd d (sz.L n)) {x : ℂ}
    (hx : ‖x‖ ≤ Q * (sz.Bctl n s ^ 2 * Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
      ((sz.W n : ℕ) : ℝ) ^ (-Dst))) :
    ‖x‖ ≤ 4 * Q * tailTD d ((sz.W n : ℕ) : ℝ) s (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst s)
      (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) :=
  hx.trans (by
    have := mul_le_mul_of_nonneg_left (pfStep5_init_le sz n hs0 hs1 hW a (Dst := Dst)) hQ
    linarith)

/-- The drift of the grid walk at loop length `2` (`Σ_{l=3}^{2}` is empty): `Θ^{(2)}` of the observable plus the list-loop drift
`ℰ^{(𝓛-𝒦)×(𝓛-𝒦)} + ℰ^{G̃}` at `KLloopOf σ b`. -/
theorem Step5IIIWalk_drift_eq {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) :
    STgDriftNg Cm s t K n σ b k ω =
      Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s t K n k) (fun b' => STgANg Cm s t K n σ b' k ω) b +
        (STelklkMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ b) +
          STegtMg Cm n (gridTime s t K n k) (Cm.Hpath s t K n k ω) (KLloopOf d (sz.L n) σ b)) := by
  unfold STgDriftNg STgANg
  rw [show Finset.Icc 3 2 = (∅ : Finset ℕ) by decide, Finset.sum_empty, add_zero, add_assoc]

/-- **The weighted quadratic variation at a grid time** (band `pfStep5_xx`, `Induction/PfStep5.lean:1326`): there is `Cq = Cq(d, κ, 𝔡)` such that, along
a flow and for every `D* ≥ 0`, some `D₂ ≥ 0` gives, eventually, for `0 ≤ v ≤ w ≤ t_n ≤ t₀`, `lam² ≤ 1 - w`, Hermitian `H` whose quadratic variation
`STeeMg_v(H)` is `≤ p T_{v,D_v}²` on the near pairs (cut `2ℓ*`):
`‖STeeUMg_{v,w}(H)_{σ,a}‖ ≤ (2 Cq p + 1) T_{w,D_w}²`, `D_u = D* + 2 log_W (1-u)`.  Inputs: the crude bound (target 3), the `uKer` far field
(`baStep5III_uKer_far`), the far absorption (`pfStep5_farAbsorb`) and `baStep5IIITailSqQV_holds` (the coupling crossing `lam0 ≤ lam` enters through
`baStep5III_lam0_le_lam` at `0 < g₀`, `BAflow_lam0_window`). -/
theorem Step5IIIWalk_xx {d : ℕ} (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ Cq : ℝ, 0 < Cq ∧ ∀ (ε 𝔠 : ℝ), 0 < ε → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ,
      (∀ n, t n ≤ BAflowT0 sz z n) → ∀ Dst : ℝ, 0 ≤ Dst → ∃ D₂ : ℝ, 0 ≤ D₂ ∧ ∀ᶠ n in atTop,
        ∀ (v w p : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
          (a : Fin 2 → Zd d (sz.L n)), 0 ≤ v → v ≤ w → w ≤ t n → sz.lam n ^ 2 ≤ 1 - w → 0 ≤ p → H.IsHermitian →
          (∀ b b' : Fin 2 → Zd d (sz.L n),
            (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
            ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v H σ b b'‖ ≤
              p * STtailTD sz n v (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst v) b ^ 2) →
          ‖STeeUMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v w H σ a‖ ≤
            (2 * Cq * p + 1) * STtailTD sz n w (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst w) a ^ 2 := by
  obtain ⟨Cq, hCq, hQV⟩ := baStep5IIITailSqQV_holds d hd κ 𝔡 hκ h𝔡
  refine ⟨Cq, hCq, fun ε 𝔠 hε sz z hflow t htT Dst hDst => ?_⟩
  obtain ⟨D₂, hD₂, hfarEv⟩ := pfStep5_farAbsorb sz 𝔠 𝔡 hflow.1 Dst hDst
  refine ⟨D₂, hD₂, ?_⟩
  have hWt := Step5IIIKer_W_tendsto hflow.1
  filter_upwards [hfarEv, baStep5III_crudeQV d κ ε 𝔠 𝔡 sz z hκ hε hflow t htT,
    baStep5III_uKer_far d hd κ ε 𝔡 hκ hε h𝔡 (D₂ + 1) (by linarith) 𝔠 sz z hflow, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow,
    hWt.eventually_gt_atTop 1, (Real.tendsto_log_atTop.comp hWt).eventually_ge_atTop 4]
    with n hfar hcrude huf hlam0 hW1 hlog v w p H σ a hv hvw hwt hreg hp hH hH1
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have hw1 : w < 1 := hwt.trans_lt ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hY0 : 0 ≤ 2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6 := by positivity
  have hk := hQV sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level W Dst v) (D₂ + 1) v w p
    (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) H σ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) hlam0.1 hlam0.2
    (baStep5III_lam0_le_lam hκ hflow n hlam0.1) hv hvw hw1 hreg hlog hp hY0 hH1
    (fun b b' => hcrude v (hvw.trans hwt) H hH σ b b')
    (fun τ τ' x y hxy => huf v w hv hvw (hwt.trans (htT n)) hreg τ τ' x y hxy) a
  obtain ⟨hl1, hl2, hl3⟩ := pfStep5_lvl (Dst := Dst) hW1 hv hvw hw1
  set Th : ℝ := STtailTD sz n w (PfStep5Grid_level W Dst w) a with hTh
  have hT1 : STtailTD sz n w (PfStep5Grid_level W Dst v) a ≤ Th := pfStep5Alg_tailAnti sz n w _ _ a hl1
  have hT1' : 0 ≤ STtailTD sz n w (PfStep5Grid_level W Dst v) a := (LemDecCalELip_tail_pos sz n w _ a).le
  have hfl : W ^ (-(PfStep5Grid_level W Dst w)) ≤ Th := lemDecCalEPrec_tail_ge sz n w _ a
  have hWn : 0 ≤ W ^ (-(PfStep5Grid_level W Dst w)) := Real.rpow_nonneg hW0.le _
  have hρ4 : ((1 - v) / (1 - w)) ^ 4 * (W ^ (-(PfStep5Grid_level W Dst v))) ^ 2 =
      (W ^ (-(PfStep5Grid_level W Dst w))) ^ 2 := by
    rw [← hl3]; ring
  have hfar' : W ^ (-(2 * Dst)) ≤ Th ^ 2 := pfStep5_W2_le (d := d) hW1 (hv.trans hvw) hw1
  have hfar2 : 4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) * ((sz.L n : ℕ) : ℝ) ^ d *
      ((1 - v) / (1 - w)) ^ 3 * W ^ (-(D₂ + 1)) ≤ Th ^ 2 := by
    refine le_trans ?_ ((hfar v w hv hvw hreg).trans hfar')
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW1.le (by linarith)) ?_
    have : 0 ≤ (1 - v) / (1 - w) := div_nonneg (by linarith) (by linarith)
    positivity
  have h1 : STtailTD sz n w (PfStep5Grid_level W Dst v) a ^ 2 ≤ Th ^ 2 := pow_le_pow_left₀ hT1' hT1 2
  have h2 : (W ^ (-(PfStep5Grid_level W Dst w))) ^ 2 ≤ Th ^ 2 := pow_le_pow_left₀ hWn hfl 2
  rw [hρ4] at hk
  have hCp : 0 ≤ Cq * p := mul_nonneg hCq.le hp
  calc _ ≤ _ := hk
    _ ≤ Cq * p * (Th ^ 2 + Th ^ 2) + Th ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCp) hfar2
    _ = (2 * Cq * p + 1) * Th ^ 2 := by ring

end PerTime

/-! ## 10. The loss budget -/

section Budget

/-- `lossE2wG` is `K₀² Λ⁶` times its value at `Λ = K₀ = 1` (`lossE2 = 10¹² (1600 d⁴)^d K₀² Λ⁶ …`). -/
theorem Step5IIIWalk_loss_eq (d L W : ℕ) (Λ K₀ : ℝ) :
    lossE2wG d L W Λ K₀ = K₀ ^ 2 * Λ ^ 6 * lossE2wG d L W 1 1 := by
  unfold lossE2wG lossE2
  ring

/-- **The loss budget** (band `lemDecCalEPrec_lossWG_eventually`, `Induction/LemDecCalEPrec.lean:246`, at `Λ = K₀ = N^{τ'}`, with the J-free factor of the
quadratic variation): for `12 τ' ≤ τ/4` and `2 θ (Cd + 1) ≤ τ/4`, eventually `lossE2wG · (W^{2θ d (Cd+1)} S_θ) ≤ N^τ`.  (`K₀² Λ⁶ = N^{8τ'} ≤ 32⁶ N^{12τ'}`
is the band's `(32 N^{2τ'})⁶`; `W^d ≤ N`; `S_θ` is bounded uniformly, `baStep5IIIE_sumTheta`.) -/
theorem Step5IIIWalk_hQ {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (hsize : sz.SizeTendsto) {τ τ' θ Cd : ℝ} (hτ : 0 < τ) (hτ' : 0 ≤ τ')
    (hθ : 0 < θ) (hCd : 0 < Cd) (h12 : 12 * τ' ≤ τ / 4) (hθ' : 2 * (θ * (Cd + 1)) ≤ τ / 4) :
    ∀ᶠ n in atTop, lossE2wG d (sz.L n) (sz.W n) (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') *
      (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
        ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  obtain ⟨Cθ, hCθ, hS⟩ := baStep5IIIE_sumTheta d (by omega) θ hθ
  have hNτ4 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ (τ / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp hsize
  filter_upwards [lemDecCalEPrec_lossWG_eventually sz (by omega) hsize hτ (by positivity : 0 ≤ 2 * τ') (by linarith),
    hNτ4.eventually_ge_atTop Cθ, hsize.eventually_ge_atTop 1] with n hL hC hN1
  obtain ⟨hW1, hL1, hNe, hLN, hWdN, hWN, hN1'⟩ := pfStep5_sizes sz n (by omega : 1 ≤ d)
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have hQ1 : 1 ≤ N ^ τ' := Real.one_le_rpow hN1 hτ'
  -- the loss at `Λ = K₀ = N^{τ'}` is at most the band's at `(32 N^{2τ'}, 1)`
  have hlossle : lossE2wG d (sz.L n) (sz.W n) (N ^ τ') (N ^ τ') ≤ lossE2wG d (sz.L n) (sz.W n) (32 * N ^ (2 * τ')) 1 := by
    rw [Step5IIIWalk_loss_eq d (sz.L n) (sz.W n) (N ^ τ') (N ^ τ'), Step5IIIWalk_loss_eq d (sz.L n) (sz.W n) (32 * N ^ (2 * τ')) 1]
    refine mul_le_mul_of_nonneg_right ?_ (by
      have := Step5IIIWalk_loss_nonneg sz n 1 1
      exact this)
    have h2 : N ^ (2 * τ') = (N ^ τ') ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [h2, one_pow, one_mul]
    have : (N ^ τ') ^ 2 * (N ^ τ') ^ 6 = (N ^ τ') ^ 8 := by ring
    have h3 : (N ^ τ') ^ 8 ≤ (N ^ τ') ^ 12 := pow_le_pow_right₀ hQ1 (by norm_num)
    calc (N ^ τ') ^ 2 * (N ^ τ') ^ 6 = (N ^ τ') ^ 8 := this
      _ ≤ (N ^ τ') ^ 12 := h3
      _ ≤ (32 * (N ^ τ') ^ 2) ^ 6 := by
          have e : (32 * (N ^ τ') ^ 2) ^ 6 = 32 ^ 6 * (N ^ τ') ^ 12 := by ring
          rw [e]
          have : (1 : ℝ) ≤ 32 ^ 6 := by norm_num
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ N ^ τ') 12]
  have hloss : lossE2wG d (sz.L n) (sz.W n) (N ^ τ') (N ^ τ') ≤ N ^ (τ / 2) := hlossle.trans hL
  -- `W^{2θ d (Cd+1)} ≤ N^{2θ (Cd+1)}`
  have hWpow : W ^ (2 * (θ * (d * (Cd + 1)))) ≤ N ^ (2 * (θ * (Cd + 1))) := by
    have e : W ^ (2 * (θ * (d * (Cd + 1)))) = (W ^ d) ^ (2 * (θ * (Cd + 1))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
    rw [e]
    exact Real.rpow_le_rpow (by positivity) hWdN (by positivity)
  have hNθ : N ^ (2 * (θ * (Cd + 1))) ≤ N ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hN1 hθ'
  have hSθ : ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) ≤ N ^ (τ / 4) :=
    (hS sz n).trans hC
  have hsum : N ^ (τ / 2) * N ^ (τ / 4) * N ^ (τ / 4) = N ^ τ := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
  have hS0 : 0 ≤ ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) :=
    Finset.sum_nonneg fun y _ => (Real.exp_pos _).le
  calc lossE2wG d (sz.L n) (sz.W n) (N ^ τ') (N ^ τ') * (W ^ (2 * (θ * (d * (Cd + 1)))) *
        ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))))
      ≤ N ^ (τ / 2) * (N ^ (τ / 4) * N ^ (τ / 4)) := by
        refine mul_le_mul hloss (mul_le_mul (hWpow.trans hNθ) hSθ hS0 (by positivity)) (by positivity) (by positivity)
    _ = N ^ τ := by rw [← mul_assoc, hsum]

end Budget

/-! ## 11. Compiled nonempty instances at `d = 3` (targets 1-5)

`sz0`, `zSeq`, `flow_sz0` with `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`), `Cd = 1`, `θ = 1/10`.  Every
deterministic premise is discharged; the four carrier predicates of Steps 2-4 stay hypotheses where the good event enters. -/

end RBM.BA

end
