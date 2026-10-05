import RBM3D.Path.LemDecCalEdif2
import RBM3D.Path.LemDecCalEwG
import RBM3D.Green.GbEXP
import RBM3D.Path.NetLift2
import RBM3D.Path.KellStar
import RBM3D.Induction.Step5Kit

/-!
# T2193 (S5-09) check file: the pin change of DECISIONS §61 and the cited merged names

Section 1: the new text of `STLemDecCalEConcl` (copy of `RBM3D/Induction/Step5Pins.lean:161-186` on `main`,
changed in two places only: line 162 gains the premise `∀ n u D, Jst n u D ≤ W_n^{1/2}` (DECISIONS §63); line 163's floor
`size n ≤ W^D` becomes `(L^d W^{6d})² ≤ W^D`, written as in `E2HypDif` (`Path/LemDecCalEdif.lean:64`) and
`E2HypWG` (`Path/LemDecCalEwG.lean:67`)).  `sz` is an explicit binder here instead of the section variable
of `Step5Pins.lean:136`; the elaborated signature is the same.
Section 2: the shape of target 2 (the `u`-uniform form of the merged `GijGEXPTSwap`, `Green/Pins.lean:283`,
with `sz.PrecPT` replaced by `sz.Prec`, nothing else changed).
Section 3: `#check` of every merged name the ticket cites.
Section 4: Prop-valued examples (statement shapes only).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The new pin text (target 1; DECISIONS §61, §63) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

def STLemDecCalEConcl_new_pin {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ Jst : ℕ → ℝ → ℝ → ℝ, (∀ n u D, 1 ≤ Jst n u D) →
    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
    ∀ D : ℝ, 0 < D →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ * Jst n (p.1 : ℝ) D ^ 2 *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (p.1 : ℝ) D ^ (3 / 2 : ℝ)) *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz
        (U := fun n => {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)})
        (fun n q ω => ‖STee sz n (E n) (q.1.1.1 : ℝ) ω q.1.1.2.1 q.1.1.2.2 q.1.2‖)
        (fun n q _ => (1 - (q.1.1.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (q.1.1.2.2 0 - q.1.1.2.2 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (q.1.1.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (q.1.1.1 : ℝ) D ^ (3 : ℝ)) *
          STtailTD sz n (q.1.1.1 : ℝ) D q.1.1.2.2 ^ 2)

end RBM.Gauss.Sizes

/-! ## 2. The shape of target 2: `GijGEXPTSwap` uniformly in `u ∈ [s,t]` -/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Loop

def LemDecCalEPrec_gijU_shape {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  sz.Prec (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => if p.2.1 = p.2.2 then 0 else ‖Gt sz n (E n) p.1 true ω p.2.1 p.2.2‖ ^ 2)
    (fun n p ω => gexRHS d (sz.L n) (sz.W n) (E n) p.1 (sz.seqHflow n p.1 ω)
      (STblk sz n p.2.2) (STblk sz n p.2.1))

end RBM.Green

/-! ## 3. Every merged name the ticket cites -/

-- the pin, its consumers, the instance machinery (`Induction/Step5Pins`, c8e4f17)
#check @RBM.Gauss.Sizes.STLemDecCalEConcl
#check @RBM.Gauss.Sizes.STLemDecCalE
#check @RBM.Gauss.Sizes.STPfConcl
#check @RBM.Gauss.Sizes.STPfStep5
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STIdx2
#check @RBM.Gauss.Sizes.STtailTD
#check @RBM.Gauss.Sizes.STLK2
#check @RBM.Gauss.Sizes.STELKLK
#check @RBM.Gauss.Step5Inst.InstIng5Concl
#check @RBM.Gauss.Step5Inst.inst_ing5_III
#check @RBM.Gauss.Step5Inst.inst_lemDecCalE
#check @RBM.Gauss.Step5Inst.sz0_reg5III
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.tailTD
-- S5-05 = T2164 (`Path/LemDecCalE`, 6e63fbc)
#check @RBM.Path.lossE2
#check @RBM.Path.E2Hyp
#check @RBM.Path.LemDecCalE_lk
#check @RBM.Path.lemDecCalE_lk
#check @RBM.Path.LemDecCalE_e2
#check @RBM.Path.LemDecCalE_floor
#check @RBM.Path.LemDecCalE_floor_A
#check @RBM.Path.LemDecCalE_inst
-- S5-06 = T2171 (`Path/LemDecCalEdif`, 7d9f111) and S5-07 = T2181 (`Path/LemDecCalEdif2`, a34c217)
#check @RBM.Path.E2HypDif
#check @RBM.Path.lossE2dif
#check @RBM.Path.LemDecCalE_dif
#check @RBM.Path.lemDecCalE_dif
#check @RBM.Path.LemDecCalEdif_inst_a
#check @RBM.Path.LemDecCalEdif_inst_b
-- S5-08 = T2172 (`Path/LemDecCalEwG`, 3e22603)
#check @RBM.Path.E2HypWG
#check @RBM.Path.lossE2wG
#check @RBM.Path.LemDecCalE_wG
#check @RBM.Path.lemDecCalE_wG
#check @RBM.Path.LemDecCalEwG_inst
-- matrix-level vocabulary and the `seqHflow` bridges
#check @RBM.Gauss.Sizes.STLM
#check @RBM.Gauss.Sizes.STLKM
#check @RBM.Gauss.Sizes.STEGtM
#check @RBM.Gauss.Sizes.STELKLKM
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STEGt
#check @RBM.Gauss.Sizes.STee
#check @RBM.Gauss.Sizes.STLM_seqHflow
#check @RBM.Gauss.Sizes.STeeM_seqHflow
#check @RBM.Gauss.Sizes.STegtM_seqHflow
#check @RBM.Gauss.Sizes.STelklkM_seqHflow
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.Gauss.Sizes.STblk
-- the `STIngR5` premises used
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLmaxU
#check @RBM.Gauss.Sizes.STLKU
#check @RBM.Gauss.Sizes.STKbound
-- M2: (GijGEX)
#check @RBM.Green.gbEXPV3
#check @RBM.Green.stGbEXP_holds
#check @RBM.Green.GbEXPV3Theorem
#check @RBM.Green.gijGEXPTSwap_giiGEXPT_of_V3
#check @RBM.Green.GijGEXPTSwap
#check @RBM.Green.AsGMcPT
#check @RBM.Green.asGMcPT_iff_forall_prec
#check @RBM.Green.gexRHS
#check @RBM.Green.stGijGEX_of_gijOmegaSeq
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Green.rangeCond_mono
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Gauss.Sizes.STGbEXP
-- the net lift and the `≺` calculus
#check @RBM.Ind.step2LocalNetLift
#check @RBM.Gauss.Sizes.stNetLift2_holds
#check @RBM.Gauss.exists_netPt_close
#check @RBM.Gauss.netPt_mem_Icc
#check @RBM.Path.perTimeDomAt_iff_forall_section
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.tendsto_size
#check @RBM.Gauss.Sizes.st5_prec_mono
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
-- (Kell*)
#check @RBM.Path.KellStarEv
#check @RBM.Path.kellStarEv

/-! ## 4. Statement shapes (Prop-valued, no proof obligations) -/

-- target 3 after the change: `STLemDecCalE d` unfolds to this
example (d : ℕ) : Prop :=
  RBM.Gauss.Sizes.STIngR5 d RBM.Gauss.Sizes.STReg5III
    (fun sz E s t => RBM.Gauss.Sizes.STLemDecCalEConcl_new_pin sz E s t)

-- the endpoint `stLemDecCalE_holds (d : ℕ) : STLemDecCalE d` (type, on `main`'s name)
example : Prop := ∀ d : ℕ, RBM.Gauss.Sizes.STLemDecCalE d

-- the instance `inst_lemDecCalE` at the new conclusion (data `sz0, z0, sInst, tInst`)
example : Prop := ∀ Cd : ℝ, 0 < Cd →
  RBM.Gauss.Step5Inst.InstIng5Concl (fun sz E s t => RBM.Gauss.Sizes.STLemDecCalEConcl_new_pin sz E s t)
    RBM.Gauss.SizesInst.sz0 RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst
    RBM.Gauss.InductionDefsInst.tInst Cd

-- nonvacuity of the new floor at `sz0` (`L = 4(n+1) ≤ W = (2(n+1))^5`, so it holds at `D = 42` for every `n`)
example : Prop :=
  ∀ᶠ n in Filter.atTop,
    (((RBM.Gauss.Sizes.L RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ) ^ 3 *
        ((RBM.Gauss.Sizes.W RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ) ^ (6 * 3)) ^ 2 ≤
      ((RBM.Gauss.Sizes.W RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ) ^ (42 : ℝ)

-- nonvacuity of the new `J* ≤ W` premise (`Jst ≡ 1`, `W ≥ 1`)
example : Prop := ∀ n : ℕ, (1 : ℝ) ≤ ((RBM.Gauss.Sizes.W RBM.Gauss.SizesInst.sz0 n : ℕ) : ℝ)
