import RBM3D.Induction.PfStep5Grid
import RBM3D.Induction.TailtoTailSq
import RBM3D.Path.DifREP3

/-!
# T2231 check file (S5-11b, `RBM3D/Induction/PfStep5.lean`): vocabulary, pins, `#check`s

Section 0: three conclusion predicates (vocabulary, `Prop`-valued `def`s).  Section 1: the six pins of
targets 1-6; target 7 is the merged `STPfStep5` (`Step5Pins.lean:211`), unchanged; target 8 is the merged
`STStep5III` (`Step5Pins.lean:458`).  Section 2: `#check` of every merged name the ticket cites.
No proofs, no `sorry`, no `by`.
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 0. Vocabulary -/

/-- **The grid conclusion** (b1-b3): there is `ε₁ > 0` such that for every `ε₀ ∈ (0, ε₁)` and every `D > 0`
there is a level `D* ≥ D + 2d` such that for every section `tt n ∈ [s_n, t_n]` and every probability
exponent `D'`, some grid `K` from `s` to `tt` has, eventually, `J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for **all**
`k ≤ K` outside an event of probability `≤ N^{-D'}` (the grid depends on `D'`: the grid exponent `C_K` of
`STGridRepNAt` depends on its `D`). -/
def PfStep5_walkConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ D : ℝ, 0 < D →
    ∃ Dst : ℝ, D + 2 * (d : ℝ) ≤ Dst ∧ ∀ tt : ∀ n, TimeIcc s t n, ∀ D' : ℝ, 0 < D' →
      ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n in atTop,
        pathP sz {ω | ∀ k, k ≤ K n →
          PfStep5Grid_JsharpM sz n (E n)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => (tt m : ℝ)) K n k))
              (gridTime s (fun m => (tt m : ℝ)) K n k) (pathH sz s (fun m => (tt m : ℝ)) K n k ω) <
            ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- **The per-time conclusion** (b4): `STLK2 ≺ T_{u,D}` per time on `[s,t] × {±}² × (Z_L^d)²`. -/
def PfStep5_PTConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2)

/-- **The uniform conclusion** (b5): `STLK2 ≺ T_{u,D}` uniformly in `u` (the union over `u` inside `P`). -/
def PfStep5_PrecConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2)

/-! ## 1. Pins -/

/-- **Target 1** (realization): every grid state is a single-time state at the grid time
(`H_k = seqXmat(c)`, `c = √s ω₀ + √Δ Σ_{i ≤ k} ω_i`; `ω' := (√u_k)⁻¹ • c` if `u_k > 0`, any `ω'` if `u_k = 0`). -/
def PfStep5_realize_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz), 0 ≤ s n → s n ≤ t n →
    ∃ ω' : sz.SeqΩ, sz.seqHflow n (gridTime s t K n j) ω' = pathH sz s t K n j ω

/-- **Target 2** (the good event of S5-09 is the preimage of a measurable set of matrices). -/
def PfStep5_goodMeas_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (Jst : ℕ → ℝ → ℝ → ℝ) (τ' : ℝ) (n : ℕ) (u : ℝ),
    ∃ S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), MeasurableSet S ∧
      ∀ ω : sz.SeqΩ, ω ∈ lemDecCalEPrec_good sz E D Jst τ' n u ↔ sz.seqHflow n u ω ∈ S

/-- **Target 3** (far-remainder absorption, DECISIONS §71): with `Y = 2N(16N)^6` (`difRep2_norm_STeeM_le_N`
at `m = 2`), some `D₂` gives `4 Y L^d ρ³ W^{-D₂} ≤ W^{-2D*}` eventually, uniformly in `0 ≤ v ≤ w`,
`ilambda² ≤ 1 - w` (`ρ = (1-v)/(1-w) ≤ ilambda^{-2} ≤ W^d`, `L^d ≤ N ≤ W^{1/𝔠}`). -/
def PfStep5_farAbsorb_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, sz.Admissible 𝔠 𝔡 → ∀ Dst : ℝ, 0 ≤ Dst → ∃ D₂ : ℝ, 0 ≤ D₂ ∧
    ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) * ((sz.L n : ℕ) : ℝ) ^ d *
          ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))

/-- **Target 4** (the stopped loop on the grid, b1-b3): the setting of Step 5, regime (iii), gives the grid
conclusion. -/
def PfStep5_walk_pin (d : ℕ) : Prop :=
  STIngR5 d STReg5III (fun sz E s t => PfStep5_walkConcl sz E s t)

/-- **Target 5** (endpoint, sections, descent `D_u ≥ D`, b4). -/
def PfStep5_PT_of_walk_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    STReg5III sz s t →
    (∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ sz.lam n ^ 2) →
    PfStep5_walkConcl sz E s t → PfStep5_PTConcl sz E s t

/-- **Target 6** (the lift `PrecPT → Prec`, b5; DECISIONS §64 (4): deterministic right side, floor `W^{-D}`). -/
def PfStep5_lift_pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
        STReg5III sz s t →
        PfStep5_PTConcl sz (STflowE z) s t → PfStep5_PrecConcl sz (STflowE z) s t

/-- Target 7 is the merged pin, unchanged. -/
example : Prop := STPfStep5 3

/-- Target 8 (one line, `ST_step5_caseIII_of_pf`) is the merged pin, unchanged. -/
example : Prop := STStep5III 3

/-- The instances' data: the pins at `SizesInst.sz0`. -/
example : Prop := PfStep5_realize_pin SizesInst.sz0
example : Prop := PfStep5_goodMeas_pin SizesInst.sz0
example : Prop := PfStep5_farAbsorb_pin SizesInst.sz0

end RBM.Gauss.Sizes

/-! ## 2. Merged names -/

-- the pin and its consumers
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Sizes.STPfConcl
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STStep5III
#check @RBM.Gauss.Sizes.ST_step5_caseIII_of_pf
#check @RBM.Gauss.Step5Inst.inst_pfStep5
#check @RBM.Gauss.Step5Inst.inst_skeletonIII
-- S5-11a (T2221)
#check @RBM.Gauss.Sizes.PfStep5Grid_level
#check @RBM.Gauss.Sizes.PfStep5Grid_JsharpM
#check @RBM.Gauss.Sizes.PfStep5Grid_stopIdx
#check @RBM.Gauss.Sizes.pfStep5Grid_level
#check @RBM.Gauss.Sizes.pfStep5Grid_Jsharp
#check @RBM.Gauss.Sizes.pfStep5Grid_stop
#check @RBM.Gauss.Sizes.pfStep5Grid_below
#check @RBM.Gauss.Sizes.pfStep5Grid_duhamel
-- S5-10 (T2209), S5-10a (T2215)
#check @RBM.Gauss.Sizes.pfStep5Alg_tailAnti
#check @RBM.Gauss.Sizes.pfStep5Alg_ugenSum'
#check @RBM.Gauss.Sizes.pfStep5Alg_riemann
#check @RBM.Gauss.Sizes.pfStep5Alg_goodStop'
#check @RBM.Gauss.Sizes.pfStep5Alg_goodProb
#check @RBM.Gauss.Sizes.pfStep5Alg_closure
#check @RBM.Gauss.Sizes.tailtoTailSq_kernel
-- S5-09 (T2193), S5-09a (T2198)
#check @RBM.Gauss.Sizes.lemDecCalEPrec_good
#check @RBM.Gauss.Sizes.lemDecCalEPrec_prob
#check @RBM.Gauss.Sizes.lemDecCalEPrec_goodDet
#check @RBM.Gauss.Sizes.lemDecCalEPrec_gij
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Gauss.Sizes.lemDecCalEPrec_numeric
#check @RBM.Gauss.Sizes.lemDecCalEPrec_QW
#check @RBM.Gauss.Sizes.lemDecCalEPrec_lossWG_eventually
#check @RBM.Gauss.Sizes.lemDecCalEPrec_Kbound
#check @RBM.Gauss.Sizes.lemDecCalEPrec_tail_ge
#check @RBM.Gauss.Sizes.lemDecCalEPrec_floor
#check @RBM.Gauss.Sizes.lemDecCalEPrec_rel
#check @RBM.Gauss.Sizes.lemDecCalEPrec_htN
#check @RBM.Gauss.Sizes.stLemDecCalE_holds
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp
#check @RBM.Gauss.Sizes.LemDecCalELip_Jsharp_basic
#check @RBM.Gauss.Sizes.LemDecCalELip_LK2
#check @RBM.Gauss.Sizes.LemDecCalELip_relcont
#check @RBM.Gauss.Sizes.LemDecCalELip_lift
#check @RBM.Ind.ContinuityNet.contGood
-- Step 2 grid layer
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Gauss.Sizes.STgAN
#check @RBM.Gauss.Sizes.STgDriftN
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STelklkM
#check @RBM.Gauss.Sizes.STegtM
#check @RBM.Gauss.Sizes.STELKLKM_eq_STelklkM
#check @RBM.Gauss.Sizes.STEGtM_eq_STegtM
#check @RBM.Gauss.Sizes.STgDrift_eq_STgDriftN
#check @RBM.Gauss.Sizes.STLM_measurable
#check @RBM.Gauss.Sizes.STLKM_measurable
#check @RBM.Gauss.Sizes.STGMM_measurable
#check @RBM.Gauss.Sizes.ST_pathP_eq_seqP
#check @RBM.Gauss.Sizes.ST_whp_grid
#check @RBM.Gauss.Sizes.ST_model_of_whp_grid
#check @RBM.Gauss.Sizes.ST_PT_of_sections
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.Ind.Ugen
-- walk, measurability, domination
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime_last
#check @RBM.Path.pathH_isHermitian
#check @RBM.Gauss.walk_measurable_Gres_apply
#check @RBM.Gauss.walk_measurable_loopFine
#check @RBM.Gauss.Sizes.walk_measurable_Lloop
#check @RBM.Green.loopPM
#check @RBM.Green.gexRHS
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.StochDomAt.precomp_param
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.STFlow
