/-
Release check for T2482 (dispatcher V3, Tue Oct 13 00:02 UTC 2026; DECISIONS §282).  U U5b = `BA/Step5IIIEdet` (+ named second file
`BA/Step5IIIEdet2`): the ℰ-bounds of BA case (iii) of Step 5 (`lem_dec_calE`, `3_5:2317-2336`) through the Hilbert-Schmidt
route (design `docs/reports/T2459-design.md` U5-2 `:172-182`, row U5b `:255`; probe `t/T2459:RBM3D/Probe/T2459Pins.lean`
`:103-150`, `:278-307`, `:360-369`, never merged).  Contents: the trace bounds for the Frobenius norm; the loop bound
`‖𝓛^{(k)}_{σ,a}‖ ≤ ∏_i √‖𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}‖` (`k ≥ 2`, `H` Hermitian) at the BA carrier `baStep2Mat`; the premise
bundle (the successor of `E2Hyp` without its entry conjuncts); the lattice sum `S_θ`; the bounds `lk`, `wG`, `dif` and their
conjunction.
Coupling (supervisor 1457 UBA-C1, DECISIONS §269 (2); R1 = supervisor 1752 TN-C1, DECISIONS §273 (1)): not triggered.  The
statements read `sz.lam` at the size level only (`0 < sz.lam n`, `sz.lam² ≤ 1 - u`, `1 ≤ sz.lam² W^d`); kernel facts enter as
hypotheses of the bundle at `baStep2Mat sz lam0 E` with `lam0 E` free; no `lam0 ≤ sz.lam`, no comparison text, no `A`.  No grid
statement (TN-C4): no `STGridRepNgL` below.
Part 1: merged names.  Part 2: the target statements as `Prop` values (prefix `T2482_`): `T2482_TraceMulLe`, `T2482_TraceMul3Le`
(the probe's compiled results `:281`, `:299`, up to the prefix, universe and binder style; binding), `T2482_BAScalar`,
`T2482_BAMatrix`, `T2482_BAEdet` (probe `:107`, `:116`, `:134` verbatim up to the prefix; binding), `T2482_EdetLk`,
`T2482_EdetWG`, `T2482_EdetDif` (the three conjuncts of `T2482_BAEdet` under its premises; binding), `T2482_TraceProdLe`,
`T2482_LoopHS`, `T2482_SumTheta` (new; binding, an equivalent restatement only if the 1a reports it and the 1a-audit signs);
then shapes (not binding): the assembly, the U5c and U5d readings, instances, R1 at BA for the record.  Part 3: the band twins
(unchanged; not edited).
Merged names only.  No proof terms, no placeholders.
Run: lake env lean docs/tickets/checks/T2482-check.lean
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Carrier
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistStep2
import RBM3D.Loop.GLoop
import RBM3D.Loop.GLoopFlow
import RBM3D.Gauss.BlockAnderson
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.BAAuxGraph2
import RBM3D.Induction.Step1Setup
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.PfStep5Grid
import RBM3D.Path.LemDecCalE
import RBM3D.Path.LemDecCalEwG
import RBM3D.Path.LemDecCalEdif
import RBM3D.Path.LemDecCalEdif2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the Step 2 vocabulary over a carrier (`Chain/Step2Gen`): loops, the stopped control, the three error terms of `lem_dec_calE`
#check @RBM.BA.STLMg
#check @RBM.BA.STLKMg
#check @RBM.BA.STavgMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.STELKLKMg
#check @RBM.BA.STEEkMg
#check @RBM.BA.STLIMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.Gauss.Sizes.STeeLoop
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.tailTD
#check @RBM.Gauss.zdistInf
-- the BA carrier (`BA/Step2BA`, `BA/FlowPins`) and the flow matrix (Hermitian)
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_LM
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baFM
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Graph.BAAuxGraph2_seqHflowBA_herm
-- loops as traces, the block identity, the resolvent and its adjoint (`Loop/GLoop`, `Loop/GLoopFlow`, `Graph/LWWeightExp`)
#check @RBM.Gauss.loopM
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.Gauss.blockMat
#check @RBM.Gauss.Gres
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.Eblk
#check @RBM.Gauss.Eblk_apply
#check @RBM.Graph.lwWx_Gres_conjTranspose
#check @Matrix.frobenius_norm_mul
#check @Matrix.frobenius_norm_def
-- sources of the matrix bundle (inputs of U5c; not read in U5b)
#check @RBM.BA.STKboundgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.BA.baEMn2ExpHK
#check @RBM.BA.EMn2BA_K_two
-- model-free lattice facts of the band layer (imported) and the loss budget
#check @RBM.Path.LemDecCalE_sum_tail_tail
#check @RBM.Path.LemDecCalEwG_sum_sqrt_tail
#check @RBM.Path.LemDecCalE_e10a
#check @RBM.Path.LemDecCalE_sum_zd_le
#check @RBM.Path.LemDecCalE_exp_conv
#check @RBM.Path.LemDecCalE_tailT_shift
#check @RBM.Path.lossE2
#check @RBM.Path.lossE2wG
-- instance data (`sz0`, `zSeq`, `flow_sz0`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0

/-! ## Part 2: the target statements (content binding as marked) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

section HS
open scoped Matrix.Norms.Frobenius

/-- **Target 1 (a)** (content binding; the probe's `T2459_trace_mul_le`, `:281`): Cauchy-Schwarz for the trace in the Frobenius
(= Hilbert-Schmidt) norm. -/
def T2482_TraceMulLe : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ), ‖(A * B).trace‖ ≤ ‖A‖ * ‖B‖

/-- **Target 1 (b)** (content binding; the probe's `T2459_trace_mul3_le`, `:299`). -/
def T2482_TraceMul3Le : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A B C : Matrix ι ι ℂ), ‖(A * B * C).trace‖ ≤ ‖A‖ * ‖B‖ * ‖C‖

/-- **Target 1 (c)** (content binding, new): `|tr(X₁⋯X_k)| ≤ ∏ ‖X_i‖_F` for `k ≥ 2` (at `k = 1` it is false: `|tr X| ≤ √N ‖X‖_F`). -/
def T2482_TraceProdLe : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (l : List (Matrix ι ι ℂ)), 2 ≤ l.length →
    ‖l.prod.trace‖ ≤ (l.map fun A => ‖A‖).prod

end HS

/-- **Target 2** (content binding, new; design (O1) `:175`): the loop bound at the BA carrier.  With
`X_i = E_{a_{i-1}}^{1/2} G(σ_i) E_{a_i}^{1/2}`, `𝓛^{(k)}_{σ,a} = tr(X₁⋯X_k)` and, `H` Hermitian, `‖X_i‖_F² = 𝓛^{(2)}_{(σ_i,!σ_i),(a_i,a_{i-1})}`
(`a_{i-1} = a ((finRotate k).symm i)`); every loop is bounded through its legs' mixed-charge two-loops. -/
def T2482_LoopHS (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H.IsHermitian →
    ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), 2 ≤ k →
      ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤
        ∏ i : Fin k, Real.sqrt ‖(baStep2Mat sz lam0 E).LM n u H ![σ i, !(σ i)] ![a i, a ((finRotate k).symm i)]‖

/-- **Target 6 (a)** (content binding, new): the lattice sum `S_θ = Σ_y e^{-(θ/2)√|y|_∞}` of the `dif` factor, bounded uniformly in
`L` (merged: rates `1/2`, `1/4` only, `LemDecCalE_sum_zd_le`, `Path/LemDecCalE.lean:314`). -/
def T2482_SumTheta (d : ℕ) : Prop :=
  1 ≤ d → ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ),
    ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) ≤ C

/-- **Target 3 (a)** (content binding; the probe's `T2459_BAscalar`, `:107`, verbatim): the scalar part of the bundle, `E2Hyp`
(`Path/LemDecCalE.lean:69`) without (P-e6), (P-e7/8), `|E| < 2`; `J ≤ W^{1/2}`. -/
def T2482_BAScalar {d : ℕ} (sz : Sizes d) (n : ℕ) (u D Λ K₀ J : ℝ) : Prop :=
  3 ≤ d ∧ 0 ≤ u ∧ u < 1 ∧ 0 < sz.lam n ∧ sz.lam n ^ 2 ≤ 1 - u ∧ 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ∧ 1 ≤ Λ ∧ 1 ≤ K₀ ∧
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D ∧
    1 ≤ J ∧ J ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)

/-- **Target 3 (b)** (content binding; the probe's `T2459_BAmatrix`, `:116`, verbatim): the matrix part at `baStep2Mat`:
`H` Hermitian; (i) the stopped control; (ii) `‖𝒦^{(2)}_{(+,-)}‖ ≤ K₀ M_u⁻¹`; (iii) its far field at `ℓ* = (log W)^{3/2}`;
(iv) `STavgMg`; (v) `𝓛^{(k)}`, `k = 2, 3, 4, 6`; (vi) the `J`-free decay of `(𝓛-𝒦)^{(2)}`. -/
def T2482_BAMatrix {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ J * STtailTD sz n u D a) ∧
  (∀ a b : Zd d (sz.L n), ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ K₀ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ a b : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (a - b) : ℝ) →
    ‖(baStep2Mat sz lam0 E).K n u ![true, false] ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
  (∀ (σ : Bool) (a : Zd d (sz.L n)), ‖STavgMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ∧
  (∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2) ∧
  (∀ (σ : Fin 4 → Bool) (a : Fin 4 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 3) ∧
  (∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd d (sz.L n)), ‖(baStep2Mat sz lam0 E).LM n u H σ a‖ ≤ Λ * ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 5) ∧
  (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (θ * (d * (Cd + 1))) * Λ *
    ((((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) ^ 2 * Real.exp (-(θ * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1) : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **Target 7** (content binding; the probe's `T2459_BAEdet`, `:134`, verbatim): `lem_dec_calE` at BA, deterministic, one time `u`,
`S = 1`; loss `lossE2wG` (`Path/LemDecCalEwG.lean:74`); indicators at `2ℓ*` (`wG`) and `6ℓ*` (`dif`), near cut `2ℓ*` (T2459b);
the `dif` factor `W^{2θd(Cd+1)} S_θ` (T2459f). -/
def T2482_BAEdet (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    T2482_BAScalar sz n u D Λ K₀ J → T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a) ∧
    (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
        lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)) ∧
    (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2))

/-- **Target 4** (content binding; conjunct 1 of `T2482_BAEdet`): `res_deccalE_lk` (`3_5:2318`) at BA. -/
def T2482_EdetLk (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    T2482_BAScalar sz n u D Λ K₀ J → T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a

/-- **Target 5** (content binding; conjunct 2 of `T2482_BAEdet`): `res_deccalE_wG` (`3_5:2325`) at BA, indicator at `2ℓ*`. -/
def T2482_EdetWG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    T2482_BAScalar sz n u D Λ K₀ J → T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤
      lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ *
        ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
          (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)

/-- **Target 6 (b)** (content binding; conjunct 3 of `T2482_BAEdet`): `res_deccalE_dif` (`3_5:2329`) at BA, near cut `2ℓ*`,
indicator at `6ℓ*`, factor `W^{2θd(Cd+1)} S_θ`. -/
def T2482_EdetDif (d : ℕ) : Prop :=
  3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd →
    T2482_BAScalar sz n u D Λ K₀ J → T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    ∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) *
          ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ *
          ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2)

/-! ### Shapes (not binding): assembly and readings -/

/-- The assembly of target 7 from targets 4, 5, 6 (b) (the split boundary: U5b-1 has 4, 5; U5b-2 has 6, 7). -/
example : Prop := ∀ d : ℕ, T2482_EdetLk d → T2482_EdetWG d → T2482_EdetDif d → T2482_BAEdet d

/-- The U5c reading: its per-time good event concludes the bundle at the flow matrix `seqHflowBA`, `Λ = K₀ = N^{τ'}`, with the
realized control `J` inside the scalar range (`J ≤ W^{1/2}`; audit O2). -/
example : Prop := ∀ (sz : Sizes 3) (z : ℕ → ℂ) (n : ℕ) (u D τ' J θ Cd : ℝ) (ω : sz.SeqΩ),
  T2482_BAScalar sz n u D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') J ∧
    T2482_BAMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n u D (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') J θ Cd
      (sz.seqHflowBA (BAflowLam0 sz z) n u ω)

/-- The U5d reading: the `dif` conjunct gives premise (H1) of U5a's `T2481_BATailSqQV` (`docs/tickets/checks/T2481-check.lean:224`)
at `v = u`, near cut `2ℓ*`, with `p = lossE2wG · W^{2θd(Cd+1)} S_θ · (1-u)⁻¹ (1 + τ_u^{1/2} J³)` (indicator `≤ 1`). -/
example : Prop := ∀ (sz : Sizes 3) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ)
    (H : Matrix (Idx 3 (sz.L n) (sz.W n)) (Idx 3 (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
  T2482_EdetDif 3 → 0 < θ → 0 < Cd → T2482_BAScalar sz n u D Λ K₀ J → T2482_BAMatrix sz lam0 E n u D Λ K₀ J θ Cd H →
    ∀ b b' : Fin 2 → Zd 3 (sz.L n),
      (∀ i : Fin 2, (zdistInf 3 (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeMg (baStep2Mat sz lam0 E) n u H σ b b'‖ ≤
        (lossE2wG 3 (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (3 * (Cd + 1)))) *
            ∑ y : Zd 3 (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf 3 (sz.L n) y : ℝ)))) *
          ((1 - u)⁻¹ * (1 + (((sz.W n : ℕ) : ℝ) ^ 3 * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)))) * STtailTD sz n u D b ^ 2

/-- R1 (the one comparison text, TN-C1, DECISIONS §273 (1)) at BA, for the record: no U5b statement reads it (UBA-C1 not
triggered); a crossing found at 1a would use this text or its guarded per-index consequence. -/
example : Prop := ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ), 0 < κ → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
  ∀ n, 0 ≤ BAflowLam0 sz z n * sz.lam n ∧ BAflowLam0 sz z n ^ 2 ≤ sz.lam n ^ 2 ∧
    sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2

/-! ### Shapes (not binding): instances at `d = 3`, `sz0`, `n = 1` (`L = 8`, `W = 1024`), `u = 1/2`, `D = 40`,
`Λ = K₀ = J = 1`, `θ = 1/10`, `Cd = 1` (the probe's data, `:154`, `:363`) -/

/-- Target 8 (a): the scalar part at the instance (the probe proves it, `T2459_scalar_sz0`). -/
example : Prop := T2482_BAScalar SizesInst.sz0 1 (1 / 2) 40 1 1 1

/-- Target 8 (a): the loop bound at `H = 0` (Hermitian), `k = 6`. -/
example : Prop := T2482_LoopHS 3 → ∀ (σ : Fin 6 → Bool) (a : Fin 6 → Zd 3 (SizesInst.sz0.L 1)),
  ‖(baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)).LM 1 (1 / 2)
      (0 : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ) σ a‖ ≤
    ∏ i : Fin 6, Real.sqrt ‖(baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)).LM 1 (1 / 2)
      (0 : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ)
      ![σ i, !(σ i)] ![a i, a ((finRotate 6).symm i)]‖

/-- Target 8 (b): `S_θ` at `θ = 1/10` along `sz0`. -/
example : Prop := T2482_SumTheta 3 → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
  ∑ y : Zd 3 (SizesInst.sz0.L n), Real.exp (-((1 / 10 : ℝ) / 2 * Real.sqrt (zdistInf 3 (SizesInst.sz0.L n) y : ℝ))) ≤ C

/-- Target 8 (b): target 7 at the instance, the `lk` conjunct; the matrix part stays a hypothesis (audit O2). -/
example : Prop := T2482_BAEdet 3 →
  ∀ H : Matrix (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) (Idx 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1)) ℂ,
    T2482_BAMatrix SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) 1 (1 / 2) 40 1 1 1
      (1 / 10) 1 H →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (SizesInst.sz0.L 1)),
      ‖STELKLKMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq)) 1 (1 / 2) H σ a‖ ≤
        lossE2wG 3 (SizesInst.sz0.L 1) (SizesInst.sz0.W 1) 1 1 *
          ((1 - (1 / 2 : ℝ))⁻¹ * ((((SizesInst.sz0.W 1 : ℕ) : ℝ) ^ 3 * |1 - (1 / 2 : ℝ)|)⁻¹ * (1 : ℝ) ^ 2)) *
            STtailTD SizesInst.sz0 1 (1 / 2) 40 a

end RBM.BA

/-! ## Part 3: the band twins (the entry-level layer U5b replaces; unchanged, not edited) -/

#check @RBM.Path.E2Hyp
#check @RBM.Path.E2HypWG
#check @RBM.Path.E2HypDif
#check @RBM.Path.LemDecCalE_lk
#check @RBM.Path.lemDecCalE_lk
#check @RBM.Path.LemDecCalE_wG
#check @RBM.Path.lemDecCalE_wG
#check @RBM.Path.LemDecCalE_dif
#check @RBM.Path.lemDecCalE_dif
#check @RBM.Path.lossE2dif
#check @RBM.Path.LemDecCalE_e6
#check @RBM.Path.LemDecCalE_e9
#check @RBM.Path.LemDecCalEdif_STeeM_le
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.PfStep5Grid_JsharpM

end
