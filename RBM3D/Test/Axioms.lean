/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Lean

/-!
# Axiom audit: the `#assert_rbm_axioms` command

`#assert_rbm_axioms` walks every declaration in the namespace `RBM` visible in the
current environment, collects the axioms it depends on (the same computation as
`#print axioms`), and **fails** unless each of them is either

* one of `propext`, `Classical.choice`, `Quot.sound`, or
* one of the named **interface axioms** listed in `RBM.Audit.interfaceAxioms`.

Any `sorry` (`sorryAx`) therefore breaks the build, and so does any new `axiom` that has
not been added to the list deliberately.

The interface list is **empty**, as in the sister projects `RBM1D` and `RBM2D`: what this
paper cites rather than proves is carried as hypotheses (`RBM.ThetaDecay`, see
`RBM3D/Propagator/Interface.lean`), so a result resting on a borrowed estimate says so in
its own statement.  The list is kept, and the command still checks it, so that a future
exception would have to be written down here.

The command also:

* fails if any listed interface axiom does not exist, or exists but is not an axiom --
  so the list cannot rot as the interface files are edited;
* fails if it finds fewer than `20` theorems in `RBM`, so that a renamed namespace cannot
  make the audit pass vacuously;
* reports what the development consists of -- **theorems**, definitions and axioms,
  counting only handwritten declarations (recursors, `casesOn`, `noConfusion`, equation
  lemmas and internal proofs are the compiler's, not the project's);
* reports, for each interface `Prop` (`RBM.Audit.interfaceProps`), how many theorems carry
  it as a hypothesis, excluding the `Prop`'s own projections.  That count is the honest
  measure of how much of the development rests on what the paper cites rather than proves:
  it is `0` while the borrowing is inert, and turns positive the moment a real result
  depends on it.

A third class sits outside both ledgers: **refuted** premises (`refutedProps`, DECISIONS §66 (2)), pins shown
false -- by a compiled theorem or by the argument of a named supervisor verdict -- and superseded by a primed
successor.  A refuted pin is not a debt (nobody can prove it) and not a borrowing; its definition stays in the
library (CLAUDE.md §5.3) and a theorem carrying it is vacuously true, so it is reported and classified but kept
out of the two ledgers, and `#assert_rbm_axioms` fails if a refuted name is also in one of the other three lists.

A fourth class is **superseded, not needed** (`supersededProps`, DECISIONS §66 (2) class, §68 (9), §73 (4), §76 (3)): pins
that nothing the closure needs consumes any more (the generic Steps 3-6, the unprimed Step-6 ingredients of regime (i)); their
definitions stay (CLAUDE.md §5.3), they are neither borrowed nor owed, and `#assert_rbm_axioms` fails if a superseded name is
also in one of the other four lists.
-/

namespace RBM.Audit

open Lean Elab Command

/-- The axioms every `RBM` declaration may use unconditionally. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Interface axioms: **none**.  The results this paper cites but does not prove are
`Prop`s in `RBM3D/Propagator/Interface.lean` (`RBM.ThetaDecay`), assumed by the theorems that
need them, not asserted.  The list is kept so that the exception remains available and
visible: adding a name here would be a deliberate act, recording that the development is
allowed to rest on a result from outside the paper. -/
def interfaceAxioms : List Name := []

/-! ### The two ledgers

A premise this development does not prove is one of two things, and the difference
matters more than the count:

* **borrowed** -- the paper cites it from the literature rather than proving it.  These
  are long-term assumptions: discharging one means proving something the paper itself
  does not.
* **owed** -- the paper does prove it (or it is a routine consequence), and it is assumed
  here only to get on with the next layer.  These are debts of this formalization, not of
  the paper.

Reporting them in one list makes "zero axioms" look better than the situation is.
-/

/-- Premises the **paper** cites rather than proves.  The pins of `lem_propTH` properties
5–8 (T2003, DECISIONS §13) and their KL-local form (T2004, §15) replace the old bundle
of four estimates and its two false difference bounds (deleted by T2127) as the statements route H
(DECISIONS §14) discharges; they are not authorised
external inputs (DECISIONS §5), so they must end up proved.  Route H proved `lem_propTH`
5–8 for every `d ≥ 3` (T2023, T2024, T2027), so `Prop5Decay`, `Prop8ZeroMode`, `Prop5to8`,
`ThetaDecay`, `ThetaDecayShort` and `ThetaZeroMode` left this list. -/
def borrowedProps : List Name :=
  [`RBM.Loop.KLPT,
   `RBM.Univ.UNL32] -- LSY Thm 2.2 (arXiv:1609.09011), the one external input of bulk universality (DECISIONS §5; T2174, UN-01)

/-- Premises **this development** owes: provable here, assumed for now.

`KLoopBound` was here rather than in `borrowedProps` because the paper does prove it:
Appendix A.5 says the proof "is analogous to that of Lemma 3.11 in `[YY_25]`, but requires
additional modifications to handle the higher-dimensional setting `d ≥ 3`.  For the
reader's convenience, we provide the proof below", and then gives it in full.  T2125 left
it: no theorem assumes it, and `KLoopBound_KLK` (`Loop/KLFinal.lean`) proves it for `K = KLK`. -/
def owedProps : List Name :=
  [`RBM.Gauss.Sizes.STLK,           -- (a) of `lem:main_ind` at `s`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STLmax,         -- `(eq:loopbound_s)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STDecay,        -- (b), first part: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STDecayStrong,  -- (b), second part: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STLocalMax,     -- (c) `(Gt_bound+IND)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STExp2,         -- (d) `(Eq:Gtlp_exp+IND)`: ST-6 chain induction (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STMainInd,      -- `lem:main_ind`: end of the ST-6 chain; class not signed in §19, owed by the §20 rule (T2028)
   `RBM.Gauss.Sizes.STBootstrap,    -- continuity bootstrap of Step 1 (`3_5:64`): S1-36 (T2028, T2015 b.10)
   `RBM.Gauss.Sizes.STForbidden,    -- forbidden-region estimate of Step 1: S1-36 (T2028, §20 rule; class not signed in §19)
   `RBM.Green.AsGMcPT,              -- `(asGMc)` per time: from (`Gtmwc`) of Step 1, RBM2D `Path/GoodSet.lean:439` `goodSet_asGMc` (T2028, §20 rule)
   `RBM.Gauss.Sizes.STLmaxU, -- `(Eq:LGxb)` uniform in `u ∈ [s,t]`: ST-6 chain / Step 4
   `RBM.Gauss.Sizes.STLKU, -- `(Eq:L-KGt-flow)` uniform in `u ∈ [s,t]`: ST-6 chain / Step 3 (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep3R, -- Step 3 per regime `R` (generic form): consumer `ST_mainIndR_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep4R, -- Step 4 per regime `R` (generic form): consumer `ST_mainIndR_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (not in the §25 list; owed, T2049 proposal)
   `RBM.Gauss.Sizes.STStep3I, -- Step 3, case (i): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
   `RBM.Gauss.Sizes.STStep3II, -- Step 3, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
   `RBM.Gauss.Sizes.STStep4I, -- Step 4, case (i): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
   `RBM.Gauss.Sizes.STStep4II, -- Step 4, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245; S3-27 cancelled, DECISIONS §68 (9)) (T2049 proposal)
   `RBM.Gauss.Sizes.STIngR, -- generic setting of an ingredient of Steps 3-4 (T2049 proposal; owed)
   `RBM.Gauss.Sizes.STIterR, -- generic setting of `lem:iterations` (T2049 proposal; owed)
   `RBM.Gauss.Sizes.STOeqNQ, -- `lem:STOeq_NQ` (DECISIONS §25)
   `RBM.Gauss.Sizes.STXiBoot, -- `(am;asoi222)` (`3_5:1366`), the conclusion of `lem:STOeq_Qt` and `lem:STOeq_Qt_nonzero`: S3-18b, S3-22; hypothesis of `iterationsA_step` (T2087)
   `RBM.Gauss.Sizes.STXiBoot', -- `(am;asoi222)` at `B_s` (DECISIONS §80): S3-18b, S3-22; hypothesis of `STIterR'`; hypothesis of `iterationsB_step` (T2259)
   `RBM.Gauss.Sizes.STOeqQt', -- `lem:STOeq_Qt`, R2* (DECISIONS §80): S3-18b
   `RBM.Gauss.Sizes.STOeqQtNZ', -- `lem:STOeq_Qt_nonzero`, R2* (DECISIONS §80): S3-22
   `RBM.Gauss.Sizes.STIterR', -- generic setting of `lem:iterations` over `STXiBoot'` (DECISIONS §80); proved at both regimes by T2259 (`stIterations'_holds`, `stIterationsII'_holds`); no generic proof
   `RBM.Gauss.Sizes.STAvgU, -- `(Gt_avgbound_flow)` uniform in `u ∈ [s,t]` (`1_2:1344`), one of the three parts of `STStep2Concl` (DECISIONS §25): the Step 2 chain; hypothesis of `iterationsA_avg_of_STAvgU` (T2087)
   `RBM.Gauss.Sizes.STLocalEntryU, -- `(Gt_bound_flow)` uniform in `u ∈ [s,t]` (`1_2:1342`), one of the three parts of `STStep2Concl` (DECISIONS §25): the Step 2 chain; hypothesis of `lemDecCalEPrec_gij`, `lemDecCalEPrec_perTime_bounds` (T2193, DECISIONS §20 rule: owed)
   `RBM.Gauss.Sizes.STStep2DecayPT, -- `(Eq:Gdecay_w)` per time (`1_2:1349-1351`): hypothesis of `stNetLift2_part1`/`step2NetLift`; proved by the Step 2 chain ST2-04 (T2074, DECISIONS §20 rule: owed)
   `RBM.Gauss.Sizes.STGdecayW, -- `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]` (`1_2:1349`, `Step34Pins.lean:208`): hypothesis of `stDecayLoopU_of_step2` (T2135 Amend 1, DECISIONS §39); proved by the Step 2 chain ST2-04 (DECISIONS §20 rule: owed)
   `RBM.Gauss.Sizes.STStep2LocalPT, -- `(Gt_bound_flow)` per time (`1_2:1343`): hypothesis of `step2LocalNetLift`/`stNetLift2_holds`; proved by the Step 2 chain ST2-04 (T2082, DECISIONS §20 rule: owed)
   `RBM.Gauss.Sizes.STStep2AvgPT, -- `(Gt_avgbound_flow)` per time (`1_2:1345`): hypothesis of `step2AvgNetLift`/`stNetLift2_holds`; proved by the Step 2 chain ST2-04 (T2082, DECISIONS §20 rule: owed)
   `RBM.Gauss.Sizes.STOptL2, -- `(eq:opt_L2)` (`3_5:470`): ST2-14, ST2-15 (T2066, DECISIONS §28); `stOptL2_of_pins` (T2116) proves it from `STLWB` and `STGridMart`, so it stays owed through those two
   `RBM.Gauss.Sizes.STStep2, -- Step 2 of `lem:main_ind` (`1_2:1340-1357`): ST2-04 (`ST_step2_of_pins`) (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWB, -- `lem:LWterm` (`3_5:385-404`): LW gate; `STLWB_of_LWterm`/`STLWT_of_LWtermExp` (T2080) prove it from the LW pin, so it stays owed through `LWterm`/`LWtermExp` (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWT, -- `lem: EWGn2_N` (`3_5:406-415`): LW gate; `STLWB_of_LWterm`/`STLWT_of_LWtermExp` (T2080) prove it from the LW pin, so it stays owed through `LWterm`/`LWtermExp` (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STInitialGT2, -- `(initialGT2)` (`3_5:28-30`): Step 1 / ST-6 chain (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWassm, -- `(eq:LW_assm)` (`3_5:388`): Step 1 / ST-6 chain (T2066, DECISIONS §28)
   `RBM.Gauss.Sizes.STLWassmExp, -- `(eq:LW_assm_exp)` (`3_5:409`): Step 1 / ST-6 chain (T2066, DECISIONS §28)
   -- T2197 (BA-C1a, DECISIONS §20): the block Anderson chain pins over a law (`RBM3D/BA/FlowPins.lean`)
   `RBM.BA.BAProp5, -- `lem_propTH` property 5 (`prop:ThfadC`) for `Θ_BA`: BA-P5 (T2197; T2161 b.2: owed)
   `RBM.BA.BAProp5s, -- property 5, short form (`prop:ThfadC_short`) for `Θ_BA`: BA-P1 (T2197; T2161 b.2: owed)
   `RBM.BA.BAProp6, -- property 6 (`prop:BD1`) for `Θ_BA`: BA-P6 (T2197; T2161 b.2: owed)
   `RBM.BA.BAProp7, -- property 7 (`prop:BD2`) for `Θ_BA`: BA-P6 (T2197; T2161 b.2: owed)
   `RBM.BA.BAProp8, -- property 8 (`prop:ThfadC0`) for `Θ_BA`: BA-P7 (T2197; T2161 b.2: owed)
   `RBM.BA.BAProp5to8, -- the bundle of properties 5-8 for `Θ_BA` (its projections are the only theorems that assume it): BA-P8 (T2197; T2161 b.2: owed)
   `RBM.BA.STLmaxgL, -- `(Eq:L-KGt2)` at a law `μ` over a flow carrier, hypothesis of the instance `inst_BAConArg'` and of `not_BAConArg_of_data`; owed like its band form `STLmax`: BA chain, BA-V2/BA-K4 (T2197)
   `RBM.BA.STKboundgL, -- `ML:Kbound` `max |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}` at a law `μ` over a flow carrier (`1_2:1056`), hypothesis of the instance `inst_baBootstrap'` (T2269); owed: the BA chain, BA-K4/BA-V2
   `RBM.BA.STLKgL, -- `(Eq:L-KGt)` (a) at a law `μ` over a flow carrier, hypothesis of the instance `inst_baBootstrap'` (T2269); owed like its band form `STLK`: BA chain, BA-V2/BA-K4
   `RBM.BA.STLocalMaxgL, -- `(Gt_bound+IND)` at a law `μ` over a flow carrier, hypothesis of the instances `inst_baS1_boot`, `inst_baS1_weakPT`, `inst_baS1_loopPT`, `inst_baBootstrap'` (T2269); owed like its band form `STLocalMax`: BA chain, BA-V2/BA-S3
   -- T2067 (LW-P, DECISIONS §20, §24 b.11): the LW pins, proved by LW-01..LW-14 (T2040 b.9)
   `RBM.Gauss.Sizes.LWterm, -- `lem:LWterm` (`3_5:385-404`): LW-01
   `RBM.Gauss.Sizes.LWtermB, -- `lem:LWterm`, "in particular" (`3_5:393-397`): LW-01
   `RBM.Gauss.Sizes.LWtermExp, -- `lem: EWGn2_N` (`3_5:406-415`): LW-01, LW-16
   `RBM.Gauss.Sizes.LWtermExpS, -- `lem: EWGn2_N`, strict regime: LW-01
   `RBM.Gauss.Sizes.LWtermExpN, -- `lem: EWGn2_N`, `1 - t ≤ ĝ²/L²`: LW-16
   `RBM.Gauss.Sizes.LWtermEXP, -- `lem:LWterm_EXP` (`6:83-88`): LW-14
   `RBM.Gauss.Sizes.LWCutExp, -- one cut of `(eq:EGC)` in expectation, `(eq:ELW_term)` (`B:10-13`), premise of `lwTermEXP_of_cut` (T2236): LW-14b
   `RBM.Gauss.Sizes.LWExpG5', -- `I₄₂`, `J₄₂` (`(eq;I42inG)`, `(eq;EGxy:x=y)`) with first kernel `S^{(B)}` or `K⁺` and last charge `±`, premise of `lwCutExp_of_terms` (T2243): LW-14c
   `RBM.Gauss.Sizes.LWG5Expand, -- `(eq:sizeGammamu_E)`, `B:91-108`: the fixed list of packed graphs with `𝔼 𝒢_xy = Σ m^j 𝔼 Γ_μ` (`n_M ≤ 1`, `n_W ≥ 2`, attached, `ord ≥ 4·1_{x=y} + 5·1_{x≠y}`), premise of `lwExpG5'_of_expand` (T2255): LW-14e
   `RBM.Gauss.Sizes.LWMoment, -- `lem:LW_moment` (`7_8:72-77`): LW-02
   `RBM.Gauss.Sizes.LWMomentExp, -- `lem:LW_moment_exp` (`7_8:78-83`): LW-02, LW-13
   `RBM.Gauss.Sizes.LWReduceB, -- reduction of `lem:LWterm` to `lem:LW_moment` (`7_8:20-91`): LW-01
   `RBM.Gauss.Sizes.LWReduceT, -- reduction of `lem: EWGn2_N` to `lem:LW_moment_exp`: LW-01
   -- T2067: the random premises of the LW pins (ST chain)
   `RBM.Gauss.Sizes.LWInteg, -- integrability of `|f_{xy}|^p`
   `RBM.Gauss.Sizes.LWInit, -- `(initialGT2)` (`3_5:30`)
   `RBM.Gauss.Sizes.LWLoop2, -- `(LW_assm)` (`3_5:388`)
   `RBM.Gauss.Sizes.LWLoopExp, -- `(LW_assm_exp)` (`3_5:411`)
   `RBM.Gauss.Sizes.LWXi, -- `(eq:Gbyxi3)` (`7_8:963-966`)
   `RBM.Gauss.Sizes.LWAvgLaw, -- `(Gt_avgbound_flow)` (`1_2:1344`)
   `RBM.Gauss.Sizes.LWAssm, -- conjunction of the hypotheses of `lem:LWterm` with random parts (§20: unsure, owed)
   `RBM.Gauss.Sizes.LWAssmExp, -- conjunction of the hypotheses of `lem: EWGn2_N` with random parts (§20: unsure, owed)
   `RBM.Gauss.Sizes.STGoodAt, -- the pathwise good event (E1)-(E5) of one self-improving step of Step 2 (`3_5:537-577`), hypothesis of `ST_good_engine`; `ST_good_prob` (T2080) proves `P(¬ STGoodAt) ≤ N^{-D'}` from (E1)-(E4) and the pins, not `STGoodAt` itself: ST2-04 (T2071; class proposed: owed)
   `RBM.Gauss.Sizes.STStep1Weak, -- `(Gtmwc)` (`1_2:1327`), the weak-law conclusion of `STStep1`, uniform in `u ∈ [s,t]`; hypothesis of the ST2-03 event theorems: S1-36 (T2080; class proposed: owed)
   `RBM.Gauss.Sizes.STScaleInv, -- `(eq:LW_assm_exp)` at the scale family at every time section (`3_5:409`, `521-527`); hypothesis of `ST_LW_sections`, `ST_event_lw`, `ST_event_mg`: ST2-04/ST2-05 (T2080; class proposed: owed)
   -- T2092 (ST2-04, class proposed: owed): hypotheses of the Step 2 iteration and closure (`Induction/Step2Iterate.lean`)
   `RBM.Gauss.Sizes.STScaleOk, -- admissible scale family `K_u` (`3_5:521-527`): clause of `STScaleAdm`, supplied by `stScaleExists_holds` (T2081); hypothesis of `ST_selfImprove`, `ST_next`
   `RBM.Gauss.Sizes.STScaleAdm, -- scale iteration `(eq:def_ell1)` (`3_5:571-577`): supplied by `stScaleExists_holds` (T2081); hypothesis of `ST_iterate`, `ST_decay_pt`
   `RBM.Gauss.Sizes.STStep2Local, -- `(Gt_bound_flow)` single-charge form of the probe: proved by `ST_step2_of_pins` through `STNetLift2`; hypothesis of `ST_concl_of_step2`
   `RBM.Gauss.Sizes.STStep2Avg, -- `(Gt_avgbound_flow)` single-charge form of the probe (paper-delta T2039g): hypothesis of `ST_avgU_of_avg`, `ST_concl_of_step2`
   `RBM.Gauss.Sizes.STStep2Parts, -- the probe's `STStep2` (triple conclusion): hypothesis of `ST_step2_concl` (T2092a)
   `RBM.Gauss.Sizes.STLocalEntry, -- local law for the entries, a hypothesis of `lem:LWterm_EXP`: first used by T2067
   `RBM.Green.FlucGainUpTo', -- gain interface of the higher-order minor expansion `(GavLGEX)` (`3_5:33`): hypothesis of the budget and moment bounds of T2096; proved by S1-22 `flucGainUpTo'_of_minorDiffGainUpTo'` (T2096, §20 rule; class proposed: owed)
   `RBM.Gauss.Sizes.STStep5I, -- `lem:main_ind` Step 5, case (i) `3_5:1939`: consumer `ST_mainIndR_*_of_steps` (T2245), producer S5-02; S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.STStep5II, -- Step 5, case (ii): consumer `ST_mainIndR_*_of_steps` (T2245), producer S5-02; S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.STEtermsMid, -- `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1979`); S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.STDuhamelI, -- integrated hierarchy `(iois-mtx2)`, case (i); S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.STDuhamelII, -- integrated hierarchy with `Q^{(1)}`, case (ii); S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.STIniTermI, -- initial term `(iksjuwjx0)`, case (i); S5-01 (T2138, DECISIONS §40: owed)
   `RBM.Gauss.Sizes.PfStep5_walkConcl, -- `lem:pf_step5` grid conclusion `J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for all `k ≤ K` w.h.p. (`3_5:2364-2383`): proved under the premises of `STIngR5` by `pfStep5_walk`; hypothesis of `pfStep5_PT_of_walk` (T2231, S5-11b: owed)
   `RBM.Univ.UNBUniv, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNGUELocal, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNTrLocal, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNClaim417, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNOUQUE, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNOULL, -- (T2276, UN-51a: owed; owner UN-51 `RandomLayerB` `g1Row`; hypothesis of `ouDiag_of_ouLL`, which proves `UNOUDiag` from it)
   `RBM.Univ.UNG1Row, -- (T2276, UN-51a: owed; owner UN-51 `RandomLayerA/B`; with `UNG2bRow` gives `UNOURow` by `ouRow_of_pins`)
   `RBM.Univ.UNG2bRow, -- (T2276, UN-51a: owed; owner UN-52 `QUEFlow` `g2bRow`; with `UNG1Row` gives `UNOURow` by `ouRow_of_pins`)
   `RBM.Univ.UNOUClaims, -- bulk universality pin, the two 𝐇_t claims (T2273, UN-21: owed; owner UNOURow)
   `RBM.Univ.UNUyw, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNMLOut, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNLocAvgBand, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNQueBand, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNUnivMainRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNJakUywRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNClaimRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNNormBound, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNNormBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNTrLocalBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNDensBandRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
   `RBM.Univ.UNClaim417C, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNGreenCorrC, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNGreenCorrAllC, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNOUQUEk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNOUDiagk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNEMCTE2k, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNJakk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNUywk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNQuek, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNLocAvgk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNOURowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNEMCTE2Rowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNJakUywRowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNClaimRowk, -- bulk universality pin, model-generic (T2187, UN-01b: owed)
   `RBM.Univ.UNTrLocalInit', -- bulk universality pin, primed successor of the refuted UNTrLocalInit, tolerance W^τ (Bctl + t*) (T2213, UN-12b: owed; band: unTrLocalInit'_band_zero; BA: BA-C1b row)
   `RBM.Univ.UNCoreC'', -- bulk universality pin, successor of the superseded UNCoreC' (T2213, UN-12b: owed; BA-C1b)
   `RBM.Univ.UNGUESchurTail, -- bulk universality pin, the Schur tail of the GUE local law (T2244, UN-09: owed; UN-10 GUELocalSchur; with un_gueLocal_of_tail gives UNGUELocal)
   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`)
   `RBM.Univ.UNLocAvgBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-M1, `(G_bound_ave)` from `BAEnd_locSC`)
   `RBM.Univ.UNMLOutBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-V3, `lem:main_ind_BA` outputs on the T2197 carrier)
   `RBM.Univ.UNOURowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
   `RBM.Univ.UNEMCTE2RowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
   `RBM.Univ.UNJakUywRowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
   `RBM.Univ.UNClaimRowBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner the model-generic UN rows at `UNKind.ba`)
   `RBM.Univ.UNDensBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-C2, `unDens'_freeConvST`)
   `RBM.Univ.UNTrLocalBARow, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1)
   `RBM.Univ.UNTrLocalInitBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1, BA model at coupling `λ e^{t*/2}`, BA-D8)
   `RBM.Univ.UNNormBARow, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-N1, `‖V‖ + λ‖Ψ‖`)
   `RBM.BA.BAEnd_QUEL, -- `(Meq:QUE)`, `(Meq:QUE2)` for block Anderson, `MR:decol_BA` third bullet `1_2:655` (T2241, BA-C1b: owed; owner BA-M3)
   `RBM.BA.BAGbEXPii, -- `lem_GbEXP_BA` `(GiiGEX)` event form `1(Ω(t, ε₀)) ‖G_t - M‖²_max ≺ max 𝓛^{(2)}` over the BA carrier, `7_8:1916-1946`; T2256 (supervisor 2026-10-05-2252 Q2, T2256a: owed; owner BA-G6)
   `RBM.BA.BAGbEXPij, -- `lem_GbEXP_BA` `(GijGEX)` event form on `(G_t - M)_{xy}`, `x ≠ y`, over the BA carrier, `7_8:1916-1946`; T2256 (supervisor 2026-10-05-2252 Q2, T2256a: owed; owner BA-G6)
   `RBM.BA.BAGbEXPav, -- `lem_GbEXP_BA` `(GavLGEX)` over the BA carrier under `(initialGT2)`, `7_8:1916-1946`; T2256 (supervisor 2026-10-05-2252 Q2: owed; owner BA-G6)
   `RBM.BA.BAFlowMember, -- finite modification of a member of `Fam(0)` is a `BAFlow` sequence (route (A), probe `T2205Pins.lean:1796-1803`); T2256 (owed; owner BA-S3, proved in probe 5.3)
   `RBM.Gauss.Sizes.STStep5Concl, -- uniform Step-5 conclusion `STGdecayW … 0 ∧ STDecayStrongU` (`3_5:1935`), the hypothesis of the assembly instance `inst_assembly`: S5-02 (T2143; class proposed: owed, as `STStep2Concl`, DECISIONS §40)
   `RBM.Gauss.Sizes.STExp2U, -- `1_2:1392-1396` (`Eq:Gtlp_exp_flow`) target of Step 6: consumer `ST_mainIndR_*_of_steps` (T2245), through `STStep6R`; S6-01 (T2204, DECISIONS §67: owed)
   `RBM.Gauss.Sizes.STStep6I, -- `6:97` regime (i) pin: consumer `ST_mainIndR_*_of_steps` (T2245); S6-02 skeleton; ingredients S6-03...S6-07, S6-09...S6-11; S6-01 (T2204, DECISIONS §67: owed)
   `RBM.Gauss.Sizes.STStep6II, -- `6:97` regime (ii) pin: consumer `ST_mainIndR_*_of_steps` (T2245); S6-02; S6-12; S6-01 (T2204, DECISIONS §67: owed)
   `RBM.Gauss.Sizes.STStep6III, -- `6:94-96` regime (iii) pin: consumer `ST_mainIndR_*_of_steps` (T2245); S6-02; S6-08; S6-01 (T2204, DECISIONS §67: owed)
   `RBM.Endpoints.decol, -- Thm 2.1 `1_2:357-370`: MA-03 `decol_of_locSC` + MA-04; MA-01 (T2210, DECISIONS §16, §20: owed)
   `RBM.Endpoints.locSC, -- Thm 2.2 `1_2:386-395`: MA-04 `MANetLoc` from MA-03; MA-01 (T2210, DECISIONS §16, §20: owed)
   `RBM.Endpoints.QUE, -- Thm 2.3 `1_2:406-420`: MA-05 `MAQUE`; MA-01 (T2210, DECISIONS §16, §20: owed)
   `RBM.Endpoints.QDiff, -- Thm 2.5 `1_2:488-511`: MA-04 `MANetQD` from MA-03; MA-01 (T2210, DECISIONS §16, §20: owed)
   `RBM.Endpoints.BUniv] -- Thm 2.4 `1_2:452-459`, the `abbrev` of `UNBUniv`: UN-52, MA-06; MA-01 (T2210, DECISIONS §16, §20: owed)

/-- Predicates that *define the objects under study* rather than assert a result about
them: assuming one is saying what the data is, not borrowing a theorem.  They are listed
so that the scan below can tell them apart from real premises -- and so that adding one
is a deliberate act. -/
def structuralProps : List Name :=
  [`RBM.Loop.IsKLoop,         -- `Def_Ktza`: what it means to be a family of `K`-loops
   `RBM.Loop.IsDiag,          -- `(i,j)` is a diagonal of the polygon
   `RBM.Loop.Crossing,        -- two diagonals cross
   `RBM.SameSignOutside,      -- `A ⊇ I_diff(σ)`, the condition of `lem:sum_decay_nonzero`
   `RBM.Graph.Case.Rel,       -- the case relation of `lem_scalingorder`, a parameter
   `RBM.NormStochDom,         -- `‖A‖ ≺ ζ`: notation of `(stoch_domination)`, not a result
   `RBM.NormStochDomAt,       -- notation of `(stoch_domination)` at scale `N`
   `RBM.Path.PerTimeDomAt,    -- notation of `(stoch_domination)` at scale `N`
   `RBM.Gauss.Sizes.WO,       -- `(eq:WO)`: the window of the size sequence
   `RBM.Gauss.Sizes.Bandwidth, -- `(Main_DEL_COND)`: `W ≥ N^𝔠`
   `RBM.Gauss.Sizes.SizeTendsto, -- `N → ∞` along the size sequence
   `RBM.Gauss.Sizes.Admissible, -- the standing hypotheses of the main results
   `RBM.Gauss.Sizes.locDomain, -- the spectral domain `𝐃_{κ,ε}`
   `RBM.Green.GoodEvent,      -- the event Ω of (4.10): every entry of `G` within `δ` of `m·I`
   `RBM.Green.LDERow,         -- row large-deviation event, input of `lem_GbEXP` (later ST-1)
   `RBM.Green.LDECol,         -- column large-deviation event, input of `lem_GbEXP` (later ST-1)
   `RBM.Green.LDEQuad,        -- quadratic large-deviation event; h.p. bound S1-19 `stochDom_ldeQuad`
   `RBM.Green.Stable,         -- stability of `1 − ξS` with constant `K`; band profile S1-24
   `RBM.EKFastDecay,          -- `(deccA0)`: decay of the tensor `A` beyond the window `W^ε ℓ_s`, a data condition on `A` (EK-3, T2034)
   `RBM.Green.AgreeOffRow,    -- two samples agree on every coordinate off row `i` (S1-11 RowIndep)
   `RBM.Green.FinDep,         -- `g` reads finitely many Gaussian coordinates: a property of the function, hypothesis of `Tame.ofBdd` (T2031)
   `RBM.Green.IsRowCoord,     -- the coordinate `c` is a coordinate of row `k`: a membership predicate defining `E_k = condRow`, hypothesis of `rowSplit_apply_of_isRowCoord` (S1-17 FlucVanish, T2061)
   `RBM.Graph.Tame1,          -- `F` is `C¹`-tame (tame, differentiable along every coordinate, tame partials): hypothesis of `stein_sample`; proved for resolvent polynomials by `lwPoly_tame1` (T2060)
   `RBM.Gauss.Sizes.STConStInd, -- `(con_st_ind)` (`1_2:1296`): a condition on the time sequences (T2028, DECISIONS §19)
   `RBM.Gauss.Sizes.STFlow, -- the setting of `MR:locSC` and `zztE`: `Admissible` and `locDomain` (T2028, DECISIONS §19)
   `RBM.Graph.LGraph.DotWF, -- at most one dotted edge per pair of vertices, none a loop (`def_graph1`, `7_8:141`; T2050)
   `RBM.Gauss.Sizes.STPsiClass, -- the class of profiles `Ψ_t(|a-b|)` of `(eq:Psi)` (`3_5:385-393`): data condition of `STLWB`, `STEMn2Poly` (T2066)
   `RBM.Gauss.Sizes.LWWindow, -- the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` of the control parameter (T2051; registered by T2067)
   `RBM.Gauss.Sizes.LWClass, -- the class `Ψ_t(·)` of `lem:LWterm` (`3_5:388-392`): positivity and window (T2051; registered by T2067)
   `RBM.Gauss.Sizes.LWPsiRel, -- monotonicity and `(eq:Psi)` of the class (`3_5:391`) (T2051; registered by T2067)
   `RBM.Gauss.Sizes.LWPsiAll, -- the hypotheses on the class shared by the graph lemmas (T2051; registered by T2067)
   `RBM.Graph.NGraph.IsNested, -- properties (1)-(3) of a nested graph (`7_8:956`): a data condition on the graph (T2050; registered by T2067)
   `RBM.Graph.NGraph.NoGhost, -- no ghost edge: a data condition on the graph (T2050; registered by T2067)
   `RBM.Graph.NGraph.GhostOK, -- at most one ghost edge per path, an ending edge: a data condition on the graph (T2050; registered by T2067)
   `RBM.Graph.NGraph.EndAt, -- the ending edge `k` of the path `𝔓_j` at its end `s` is attached to `α_i` (`7_8:1123-1125`): a defining predicate of the ending-edge types, hypothesis of `anpKey2_endAt_ends` and the type lemmas of `Graph/AnpKey2` (T2242)
   `RBM.Graph.NGraph.IsA1, -- ending edge of type A1 on `𝐃_π` (`7_8:1127`): a defining predicate of the case split, hypothesis of `anpKey2_caseI_ne` (T2242)
   `RBM.Graph.NGraph.IsA2, -- ending edge of type A2 on `𝐃_π` (`7_8:1130`): a defining predicate of the A2 replacement, hypothesis of `anpKey2_A2_factor`, `anpKey2_A2_val` (T2242)
   `RBM.Graph.NGraph.IsB1, -- ending edge of type B1 (`7_8:1134`): a defining predicate of the case split, hypothesis of `anpKey2_caseI_ne` (T2242)
   `RBM.Graph.NGraph.IsB2, -- ending edge of type B2 (`7_8:1136`): a defining predicate of the case split, hypothesis of `anpKey4_caseIII_ne`, `anpKey4_solid` (T2260)
   `RBM.Graph.AnpCaseIII, -- case (III) of the induction step (`7_8:1245`): two B2 ending edges at an internal vertex with `deg_s = 2`, a defining predicate of the case split, hypothesis of `anpKey4_reduce` (T2260)
   `RBM.Graph.NGraph.NoA2, -- `(eq:noA2)` (`7_8:1146`), no A2 edge on `𝐃_π`: a data condition on the graph, hypothesis of `anpDetGhReg_of_noA2` and of the case pins (T2242)
   `RBM.Graph.anpKey5_perPath, -- every path of a nested graph has at most one edge that is a ghost or in the reserved set `M` (the long edges of LW-12f's union bound): a data condition on the pair `(Γ, M)`, hypothesis of `anpKey5_cert`, `anpKey5_cross_ge`, `anpKey5_inside_ge` (T2264)
   `RBM.Path.HermTestFun,      -- the class of observables `Φ` (`C²` and bounded at Hermitian points): a data condition on `Φ`, hypothesis of `stepDecomp` (T2073, ST2-22; DECISIONS §20)
   `RBM.Gauss.AdjacentMismatch, -- two consecutive block labels of a finite label word differ: a data condition on the labels, hypothesis of `initialLoopValue_zero_of_adjacentMismatch` (T2077, S1-06; DECISIONS §20)
   `RBM.Graph.LGraph.Consistent, -- a term `Dot · Γ` of the dotted edge partition has no `×`-dotted edge inside a class of `=`-dotted edges (`dot-def`, `7_8:221`; T2050)
   `RBM.Graph.LGraph.XBetween, -- `Γ` has a `×`-dotted edge between `u` and `v`: a defining predicate of normal graphs (`defnlvl0` (iii), `7_8:205`; T2050), hypothesis of the counting lemmas `lvl1_master`, `lvl1_k1`, `lvl1_k2` (T2128)
   `RBM.Gauss.Sizes.LWAttached, -- every internal molecule of a packed graph is attached to two solid edges between different molecules (`B:84-86`): a data condition on the graph, hypothesis of `lwGraphPrec1` (T2255)
   `RBM.Graph.LGraph.IsExtMol, -- an external molecule: a molecule containing an external vertex (`def_poly`, `7_8:172`): a defining predicate of the auxiliary graph, hypothesis of the nested-form lemmas of `Graph/AuxGraph` (T2170)
   `RBM.Graph.lvl1Split, -- how the weight split of the dotted edge partition (`dot-def`) changes a list of solid edges: a relation that describes the objects, mentioned only by the `brecOn` that Lean generates for it (T2128)
   `RBM.Graph.lvl1Split.below, -- auxiliary predicate that Lean generates for the recursive inductive `lvl1Split` (T2128)
   `RBM.Graph.Lvl1Reach.below, -- auxiliary predicate that Lean generates for the recursive inductive `Lvl1Reach` (reachability by `strat_local`, `B:135-157`) (T2128)
   `RBM.Green.AgreeOffRows,   -- two samples agree on every coordinate off the rows in the finite set `S` (the `Finset` version of `AgreeOffRow`): hypothesis of `Xentry_congr_of_not_mem`, `Hflow_submatrix_set_congr` (T2105, S1-22)
   `RBM.Path.UkerFar, -- the far-kernel condition `‖ukerMat 1 u v a b‖ ≤ W^{-D'}` beyond distance `R`: a data condition on the kernel, hypothesis of `uopLocalMax`, `uopPairLocalMax`; supplied by `kellStarEv` (T2097, ST2-25; DECISIONS §20)
   `RBM.Gauss.Sizes.STIngR5, -- the shape of every Step-5 pin: `∀ 3 ≤ d, 𝔠d` with the Step 1-4 premises implying the conclusion `Concl` in the regime `R`; S5-01 (T2138, DECISIONS §40)
   `RBM.Gauss.Sizes.STReg5I, -- Step 5 regime (i) `3_5:1939`: a data condition on the times; S5-01 (T2138, DECISIONS §40)
   `RBM.Gauss.Sizes.STReg5II, -- Step 5 regime (ii); S5-01 (T2138, DECISIONS §40)
   `RBM.Gauss.Sizes.STReg5Mid, -- Step 5 window of cases (i)+(ii); S5-01 (T2138, DECISIONS §40)
   `RBM.Gauss.Sizes.STReg5III, -- Step 5 regime (iii); S5-01 (T2138, DECISIONS §40)
   `RBM.Univ.UNDens, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.IsRegular32, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.IsFreeConv32, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.InWindow, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.queBadMat, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.UNBadY, -- bulk universality: condition on data (T2162 report (d) 4; T2174, UN-01)
   `RBM.Univ.Step1LocalEventGUE, -- bulk universality: the GUE-side local event (averaged law at the `UNGUELocal` precision plus the entry bound `‖X x y‖ ≤ 1`), an event on the data; a hypothesis of `gue_err_pow` (T2220, UN-11; DECISIONS §20: condition on data, as `IsRegular32`)
   `RBM.Univ.GUEGoodAt, -- bulk universality: the GUE-side good event (`vGUE` is [32]-regular, a solution of (2.5) has a density at 0 within `N^{-3τs/8}` of `ρ_sc(E₀)`), an event on the data; a hypothesis of `guetranslation_core`, `guetranslation_uniform` (T2226, UN-14; DECISIONS §20: condition on data, as `IsRegular32`)
   `RBM.Univ.InjSum_IsTestFun, -- T2178: test-function condition (smooth, compact support) on data; a hypothesis of deterministic lemmas (DECISIONS §20, §56)
   `RBM.Univ.UNKind.bulk, -- bulk universality: the energy set of a model class (`|E| ≤ 2 - κ` for the band model), a Prop-valued field of data; a hypothesis of the generic pins (T2187, UN-01b; DECISIONS §20: condition on data)
   `RBM.Univ.UNDens', -- bulk universality: condition on data, UNDens plus the box hypotheses of freeConv_stable_lip (T2201, UN-01c; DECISIONS §66)
   `RBM.Univ.UNMeanBound, -- bulk universality: condition on data, eigenvalue bound of the deterministic mean of a centred model (T2213, UN-12b; DECISIONS §69)
   `RBM.Gauss.Sizes.STReg5IV, -- Step 5 regime (iv); S5-01 (T2138, DECISIONS §40)
   `RBM.Gauss.Sizes.STStep2Core, -- Step-2 conclusion restricted to sub-intervals (`1_2:1342-1344`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STRegSeq, -- a two-stage regime cut at an intermediate time; S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STIngR6, -- the shape of the Step-6 regime pins (`1_2:1281`, `1295-1297`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STStep6R, -- the Step-6 pin at one regime; S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STStep5R, -- the Step-5 pin at one regime `R` (`STIngR5` with `STStep5Concl`), the hypothesis of the generic step `ST_mainIndR_of_steps` (T2245, DECISIONS §68 (7), §20: structural, as `STStep6R`)
   `RBM.Gauss.Sizes.STMainIndR, -- `lem:main_ind` under a regime `R` of the time sequences (supervisor 1806 Q2 "The fix"); T2245, DECISIONS §68 (7), §20: structural, as `STStep6R`
   `RBM.Gauss.Sizes.STStep6Concl, -- the Step-6 conclusion (`Eq:Gtlp_exp_flow` on the window); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpAvgAt, -- averaged improved bound at a time (`6:12-17`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpAvgU, -- averaged improved bound uniformly in u (`6:14-16`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpDuhEq, -- Duhamel identity along a window (`6:3-7`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpDuhEqQ, -- Duhamel identity with Q along a window (`6:109-116`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STDriftHi, -- window `ilambda^2/L^d <= 1-t` of the drift bounds (`6:58`, `6:83`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpLKLKHiConcl, -- conclusion of the (L-K)x(L-K) drift bound (`6:58-62`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpEGtHiConcl, -- conclusion of the LW drift bound (`6:83-88`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpDriftHiConcl, -- conclusion of the drift bound (`6:83-88`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpDriftLoConcl, -- conclusion of the regime (iv) drift bound (`6:63-66`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpDriftDecayConcl, -- conclusion of the drift decay (`3_5:1634`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpWardIConcl, -- conclusion of the Ward term, regime (i) (`6:104-107`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpWardIIConcl, -- conclusion of the Ward term, regime (ii) (`6:137-141`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpIntConcl, -- conclusion of the integrated estimate (`6:94-132`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpIntQConcl, -- conclusion of the integrated estimate with Q (`6:94-132`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpIniIConcl, -- conclusion of the initial term, regime (i) (`6:117`); S6-01 (T2204, DECISIONS §67: structural)
   `RBM.Gauss.Sizes.STExpIniIConcl', -- conclusion of the initial term, regime (i), positive mollifier constants (`6:117`; T2223a); S6-11 (T2223, DECISIONS §20: structural)
   `RBM.Gauss.Sizes.STExpWardIConcl', -- conclusion of the Ward term, regime (i), positive mollifier constants (`6:104-107`, `6:121-131`; DECISIONS §73); S6-10 (T2232, DECISIONS §20: structural)
   `RBM.Gauss.Sizes.STExpIntQConcl', -- conclusion of the integrated estimate with Q, regime (i), positive mollifier constants (`6:109-132`; DECISIONS §73); S6-09a (T2239, DECISIONS §20: structural)
   `RBM.Gauss.Sizes.STSigMixed, -- the sign class `σ₁ ≠ σ₂` of the index set `STIdx2P` (`6:104`): a data predicate, a binder of the transfer theorems `expIntIQ_ini/_star_bound/_back` of S6-09b (T2257, DECISIONS §20: structural)
   `RBM.Endpoints.locBad1, -- the bad event of `(G_bound)` in `locSC` (MA-01, `Endpoints.lean:136`); `¬ locBad1` is a hypothesis of the deterministic `decol_core` (MA-03, T2225, DECISIONS §20: structural)
   `RBM.Endpoints.locBad2, -- the bad event of `(G_bound_ave)` in `locSC` (MA-01, `Endpoints.lean:140`); hypothesis of the deterministic cover lemma `locBad2_net` (MA-04, T2230, DECISIONS §20: structural)
   `RBM.Endpoints.qd1Bad, -- the bad event of `(eq:diffu1)` in `QDiff` (MA-01, `Endpoints.lean:144`); hypothesis of the deterministic cover lemma `qd1Bad_net` (MA-04, T2230, DECISIONS §20: structural)
   `RBM.Endpoints.qd2Bad, -- the bad event of `(eq:diffu2)` in `QDiff` (MA-01, `Endpoints.lean:148`); hypothesis of the deterministic cover lemma `qd2Bad_net` (MA-04, T2230, DECISIONS §20: structural)
   `RBM.BA.BAWinBulk, -- the window `[√(1 - c₁) g₀, g₀]` lies in the `κ`-bulk of the block Anderson flow (BA-D8, `CouplingWindow.lean:799`); a predicate on the data, hypothesis of `BAFamZ_im_m_ge`, `BATrivialLmax` (BA-S2a, T2238, DECISIONS §20, T2205 portmap P.2: structural)
   `RBM.Univ.queWindow] -- the energy window `𝓘_E(ε₀) = {x : |x - E| ≤ W^{-ε₀} (ilambda W^{d/2}/N)}` of `(eq:defIE)` (`1_2:409`): a condition on the eigenvalue `x`, hypothesis of the deterministic inclusions `queBad_sub`, `que2Bad_sub` (MA-05a, T2240, DECISIONS §20: structural)

/-- **Refuted** premises (DECISIONS §66 (2), class "superseded, refuted"): pins shown false, by a compiled
theorem or by the argument of the named supervisor verdict, and superseded by a primed successor.  Their
definitions stay in the library (CLAUDE.md §5.3: no merged signature is changed), and a theorem that carries one
as a hypothesis is vacuously true; so they are **neither borrowed nor owed**: they are in neither ledger, which
keeps "owed = ∅" reachable.  They stay classified so that the scan, which still finds them in the hypotheses of the
merged theorems and of the refutations, does not report them as unregistered; and a name may be in this list or in
the three above, never in both (`#assert_rbm_axioms` checks the disjointness, so that a union merge cannot
silently put a refuted pin back into `owedProps`). -/
def refutedProps : List Name :=
  [`RBM.Univ.UNStep1Good,   -- false: `not_UNStep1Good`, `not_UNStep1Good_band` (T2201, `Universality/PinsDens.lean`); successor `UNStep1Good'`
   `RBM.Univ.UNInfty1Row,   -- false: argued, supervisor 2026-10-05-1651 1.3 (needs the GUE bulk one-point limit; not compiled); successor `UNInfty1Row'`
   `RBM.Univ.UNStep1GoodC,  -- false: `not_UNStep1GoodC` (T2201); successor `UNStep1GoodC'`
   `RBM.Univ.UNCoreC,       -- false: argued, supervisor 2026-10-05-1651 1.3 (not compiled); successor `UNCoreC'`
   `RBM.Univ.UNTrLocalInit, -- false for the band model at every admissible sequence: argued, supervisor 2026-10-05-1955 B1 (T2208b; not compiled); successor `UNTrLocalInit'`
   `RBM.Univ.UNStep1GoodC', -- false: `not_UNStep1GoodC'_of_diag` (T2213; on a diagonal model meeting its hypotheses), argued in general, supervisor 2026-10-05-1955 B1 (T2208a); successor `UNStep1GoodC''` (proved: `step1GoodC''`)
   `RBM.Univ.UNCoreC']      -- superseded, not shown false: its hypothesis `UNTrLocalInit` fails for the band model (supervisor 2026-10-05-1955 B1-B2); successor `UNCoreC''`

/-- **Superseded, not needed** (DECISIONS §66 (2) class, §68 (9), §73 (4), §76 (3)): definitions kept (CLAUDE.md §5.3),
consumed by nothing that the closure needs; **neither borrowed nor owed**.  They are not false (as `refutedProps`) and
not debts (nothing needs them): the closure of `lem:main_ind` goes through `ST_mainIndR_*_of_steps` and
`ST_mainInd_of_regimes` (T2245), which consume the regime pins `STStep3I/II`, `STStep4I/II`, `STStep5I/II`,
`STStep6I/II/III`, and through the primed successors of the Step-6 ingredients; a name is in this list or in the
other four, never in two (`#assert_rbm_axioms` checks the disjointness). -/
def supersededProps : List Name :=
  [`RBM.Gauss.Sizes.STStep3,    -- Step 3, any regime: S3-27 cancelled (DECISIONS §68 (9)); the regime pins `STStep3I/II` are consumed by `ST_mainIndR_*_of_steps` (T2245)
   `RBM.BA.BAConArg',            -- `lem_ConArg_BA` in the `Φ_t` form (T2197 Amend 1): not refuted, not provable from its premises by the band route (T2237a, DECISIONS §81); its event-form successor `BAConArg''` is proved (`baConArg''_holds`, T2237)
   `RBM.Gauss.Sizes.STStep4,    -- Step 4, any regime: S3-27 cancelled (DECISIONS §68 (9)); the regime pins `STStep4I/II` are consumed by `ST_mainIndR_*_of_steps` (T2245)
   `RBM.Gauss.Sizes.STStep5,    -- Step 5, general `0 ≤ s < t < 1`: S5-29 cancelled (DECISIONS §68 (9)); the regime pins `STStep5I..IV` are consumed by `ST_mainIndR_*_of_steps` (T2245)
   `RBM.Gauss.Sizes.STStep6,    -- Step 6, general `0 ≤ s < t ≤ t₀`: S6-13 cancelled (DECISIONS §68 (10)); still carried by `ST_step6R_of_any`; the regime pins `STStep6I..IV` are consumed by `ST_mainIndR_*_of_steps` (T2245)
   `RBM.Gauss.Sizes.STExpIniI,  -- initial term of regime (i), unprimed: successor `STExpIniI'` (proved, T2223); its successor is consumed by `ST_step6_caseI_of_pins''` (T2239; DECISIONS §73 (4))
   `RBM.Gauss.Sizes.STExpIntI,  -- integrated estimate of regime (i), unprimed: successor `STExpIntI'` (S6-09b); its successor is consumed by `ST_step6_caseI_of_pins''` (T2239; DECISIONS §73 (4))
   `RBM.Gauss.Sizes.STOeqNQ',   -- superseded by `STOeqNQ''` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
   `RBM.Gauss.Sizes.STOeqQt,    -- superseded by `STOeqQt'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
   `RBM.Gauss.Sizes.STOeqQtNZ,  -- superseded by `STOeqQtNZ'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
   `RBM.Gauss.Sizes.STIterations,  -- superseded by `STIterations'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)
   `RBM.Gauss.Sizes.STIterationsII]  -- superseded by `STIterationsII'` (R2*, DECISIONS §80 (1)); definition kept (CLAUDE.md §5.3)

/-- The premises the audit reports on: borrowed plus owed. -/
def interfaceProps : List Name := borrowedProps ++ owedProps

/-- **Non-vacuity certificates** (`docs/QUEUE.md`, Q41).  For a premise `p`, a theorem of
this development witnessing that `p` is *satisfiable*: either an object that satisfies it,
or a weakening of it that is proved here.

This is the one thing the axiom count cannot see.  If a premise is false, every theorem
carrying it is vacuously true, and the audit still reports `0 axioms` and a healthy list
of dependents -- which is exactly what happened while `(prop:ThfadC_short)` was stated
without its `σ₁ = σ₂` restriction (`docs/paper-deltas.md`, D11).  The certificate column
below is the positive half of that record; `RBM3D/Test/InterfaceShape.lean` holds both
halves and says, premise by premise, what a certificate would take.

A certificate must name a real theorem, for a registered premise; otherwise the build
fails.  The column is deliberately mostly empty: it reports a gap rather than hiding it. -/
def certificates : List (Name × Name) := []

/-! ### Finding the premises, instead of being told them

`interfaceProps` used to be a hand-written list, and the moment a new assumption appeared
the report stayed silent about it -- a report that claims to account for everything and
quietly does not.  The scan below finds the premises itself: a `Prop`-valued definition in
`RBM` that some theorem takes as a hypothesis and **no** theorem of this development
proves.  Anything it finds that is in none of the three lists above fails the build.
-/

/-- The type is `∀ …, Prop`. -/
private partial def resultIsProp : Expr → Bool
  | .forallE _ _ b _ => resultIsProp b
  | .sort u => u == .zero
  | _ => false

/-- The constants occurring in the hypotheses of a `∀`-telescope. -/
private partial def binderConsts : Expr → Array Name
  | .forallE _ d b _ => binderConsts b ++ d.getUsedConstants
  | _ => #[]

/-- The head constant of the conclusion of a `∀`-telescope. -/
private partial def conclusionHead : Expr → Option Name
  | .forallE _ _ b _ => conclusionHead b
  | e => e.getAppFn.constName?

/-- `Prop`-valued definitions of `RBM`, the theorems that assume them, and the theorems
that prove them.  `ignore` keeps the audit's own fixtures out of the development.

A structure's projections do not count as proving its fields: the projection `P.f` of a bundle `P`
produces a `Prop` of the field from a `P`, which is bookkeeping, not a proof.

Neither does a **certificate**: a theorem that concludes the premise `p` of *one* family has the
premise as its conclusion head, but it does not prove it of the arbitrary object that every theorem
carrying the premise quantifies over.  Counting it as a proof made the premise disappear from the scan -- a report that
goes quiet exactly when someone certifies an assumption is worse than no report -- so the
names in `certificates` are excluded here (`witness`). -/
def scanPremises (env : Environment) (ignore : Name → Bool) (witness : Name → Bool) :
    Array Name := Id.run do
  let keep (n : Name) : Bool := (`RBM).isPrefixOf n && !n.isInternalDetail && !ignore n
  let propDefs := env.constants.fold (init := #[]) fun acc n ci =>
    if keep n && (match ci with | .defnInfo _ | .inductInfo _ => true | _ => false)
        && resultIsProp ci.type then acc.push n else acc
  let mut assumed : Array Name := #[]
  let mut proved : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if keep n then
      match ci with
      | .thmInfo _ =>
        for c in binderConsts ci.type do
          if propDefs.contains c && !assumed.contains c then assumed := assumed.push c
        let isProj := propDefs.any fun p =>
          isStructure env p && (getStructureFields env p).any fun f => p ++ f == n
        unless isProj || witness n do
          match conclusionHead ci.type with
          | some h => if propDefs.contains h && !proved.contains h then proved := proved.push h
          | none => pure ()
      | _ => pure ()
  return assumed.filter fun n => !proved.contains n

/-- Declarations the compiler generates (recursors, `casesOn`, `noConfusion`, equation
lemmas, internal proofs) are not part of the development and are not counted. -/
def isHandwritten (env : Environment) (n : Name) (ci : ConstantInfo) : Bool :=
  (`RBM).isPrefixOf n && !(`RBM.Audit).isPrefixOf n && !n.isInternalDetail
    && !isAuxRecursor env n && !isNoConfusion env n
    && !(match ci with | .recInfo _ => true | _ => false)

/-- Fails unless every declaration in `RBM` uses only `allowedAxioms` together with the
declared `interfaceAxioms`, and reports what the development consists of: how many
theorems, how many definitions, how many axioms, and how many theorems rest on each
interface hypothesis. -/
elab "#assert_rbm_axioms" : command => do
  let env ← getEnv
  -- the interface list must name real axioms
  for n in interfaceAxioms do
    match env.find? n with
    | none => throwError m!"axiom audit: interface axiom `{n}` does not exist"
    | some (.axiomInfo _) => pure ()
    | some _ => throwError m!"axiom audit: `{n}` is listed as an interface axiom but is \
        not an axiom"
  -- the handwritten declarations of `RBM`, classified
  let handwritten := env.constants.fold (init := #[]) fun acc n ci =>
    if isHandwritten env n ci then acc.push (n, ci) else acc
  let thms := handwritten.filter fun (_, ci) => match ci with | .thmInfo _ => true | _ => false
  let axs := handwritten.filter fun (_, ci) => match ci with | .axiomInfo _ => true | _ => false
  let defs := handwritten.filter fun (_, ci) =>
    match ci with
    | .defnInfo _ | .inductInfo _ | .ctorInfo _ | .opaqueInfo _ => true
    | _ => false
  if thms.size < 20 then
    throwError m!"axiom audit: only {thms.size} theorems found in `RBM`"
  -- every declaration may use only the permitted axioms
  let permitted := allowedAxioms ++ interfaceAxioms
  let mut bad : Array MessageData := #[]
  let mut counts : Array (Name × Nat) := interfaceAxioms.toArray.map (·, 0)
  for (n, _) in handwritten do
    let usedAxioms ← collectAxioms n
    let extra := usedAxioms.filter fun a => !permitted.contains a
    unless extra.isEmpty do
      bad := bad.push m!"{n} depends on {extra.toList}"
    counts := counts.map fun (a, k) => if usedAxioms.contains a && a != n then (a, k + 1) else (a, k)
  unless bad.isEmpty do
    throwError m!"axiom audit failed:\n{MessageData.joinSep bad.toList "\n"}"
  -- every certificate must name a real theorem, for a registered premise
  for (p, c) in certificates do
    unless (borrowedProps ++ owedProps ++ structuralProps).contains p do
      throwError m!"axiom audit: `{c}` is registered as a certificate for `{p}`, which is \
        not a registered premise"
    match env.find? c with
    | some (.thmInfo _) => pure ()
    | _ => throwError m!"axiom audit: the certificate `{c}` of `{p}` is not a theorem"
  -- the premises, found rather than declared
  let found := scanPremises env (fun n => (`RBM.Audit).isPrefixOf n)
    (fun n => certificates.any fun (_, c) => c == n)
  let classified := borrowedProps ++ owedProps ++ structuralProps ++ refutedProps ++ supersededProps
  -- a refuted premise must not also be borrowed, owed or structural
  let revived := refutedProps.filter fun n => (borrowedProps ++ owedProps ++ structuralProps).contains n
  unless revived.isEmpty do
    throwError m!"axiom audit: {revived.length} refuted premise(s) are also in `borrowedProps`, \
      `owedProps` or `structuralProps`: {revived}\n\
      A refuted pin is in `refutedProps` only (DECISIONS §66 (2)); never put it back into a ledger."
  -- a superseded premise must not also be borrowed, owed, structural or refuted
  let resurrected := supersededProps.filter fun n =>
    (borrowedProps ++ owedProps ++ structuralProps ++ refutedProps).contains n
  unless resurrected.isEmpty do
    throwError m!"axiom audit: {resurrected.length} superseded premise(s) are also in `borrowedProps`, \
      `owedProps`, `structuralProps` or `refutedProps`: {resurrected}\n\
      A superseded pin is in `supersededProps` only (DECISIONS §76 (3)); never put it back into a ledger."
  let unregistered := found.filter fun n => !classified.contains n
  unless unregistered.isEmpty do
    throwError m!"axiom audit: {unregistered.size} premise(s) that no theorem of this \
      development proves are in none of `borrowedProps`, `owedProps`, \
      `structuralProps`, `refutedProps`, `supersededProps`:\n  {unregistered.toList}\n\
      Classify each of them: borrowed from the literature, owed by this formalization, \
      a predicate that defines the objects under study, refuted (shown false and superseded), or superseded \
      (not needed)."
  -- how much of the development rests on each premise
  -- a Prop's own projections (`P.f`, …) mention it but rest on nothing
  let isInterfaceOwn (n : Name) : Bool := interfaceProps.any fun p => p.isPrefixOf n
  let usageOf (ps : List Name) := ps.map fun p =>
    (p, (thms.filter fun (n, ci) =>
      !isInterfaceOwn n && (ci.type.getUsedConstants).contains p).size)
  let usage := usageOf interfaceProps
  let carried : Nat := usage.foldl (init := 0) fun acc (_, k) => acc + k
  let certOf (p : Name) : MessageData :=
    match certificates.find? (fun (q, _) => q == p) with
    | some (_, c) => m!" [certificate: {c}]"
    | none => m!" [no certificate]"
  let ledger (title : MessageData) (ps : List Name) : MessageData :=
    m!"{title}\n{MessageData.joinSep ((usageOf ps).map fun (p, k) =>
      m!"  {p}: {k}{certOf p}") "\n"}"
  let usageReport := usage.map fun (p, k) => m!"  {p}: {k}"
  let axiomLine :=
    if interfaceAxioms.isEmpty then
      m!"no project axioms: what the paper cites rather than proves is carried as \
        hypotheses, not asserted"
    else
      m!"interface axioms, with the number of other declarations depending on each:\n\
        {MessageData.joinSep (counts.toList.map fun (a, k) => m!"  {a}: {k}") "\n"}"
  let _ := usageReport
  -- how the premises the scan found fall into the three ledgers, and which registered
  -- premises nothing currently rests on
  let foundBorrowed := found.filter (borrowedProps.contains ·)
  let foundOwed := found.filter (owedProps.contains ·)
  let foundStructural := found.filter (structuralProps.contains ·)
  let foundRefuted := found.filter (refutedProps.contains ·)
  let foundSuperseded := found.filter (supersededProps.contains ·)
  let unused := classified.filter fun n => !found.contains n
  let registryLine :=
    if unused.isEmpty then
      m!"registry: {borrowedProps.length} borrowed + {owedProps.length} owed + \
        {structuralProps.length} structural + {refutedProps.length} refuted + {supersededProps.length} superseded, \
        every one of them \
        carrying something"
    else
      m!"registry: {borrowedProps.length} borrowed + {owedProps.length} owed + \
        {structuralProps.length} structural + {refutedProps.length} refuted + {supersededProps.length} superseded; {unused.length} \
        registered premise(s) carry nothing yet: {unused}"
  let carriedLine :=
    if carried = 0 then
      m!"no theorem yet rests on a premise"
    else
      m!"{ledger m!"theorems resting on each premise the PAPER borrows:" borrowedProps}\n\
        {ledger m!"theorems resting on each premise THIS FORMALIZATION owes:" owedProps}"
  logInfo m!"axiom audit: {thms.size} theorems, {defs.size} definitions, {axs.size} axioms \
    in `RBM` (compiler-generated declarations excluded).\n\
    All within {allowedAxioms}; {axiomLine}.\n\
    {carriedLine}\n\
    premises found by scanning: {found.size} (borrowed {foundBorrowed.size}, \
    owed {foundOwed.size}, structural {foundStructural.size}, refuted {foundRefuted.size}, superseded {foundSuperseded.size}).\n\
    {registryLine}.\n\
    non-vacuity certificates: {certificates.length} of \
    {borrowedProps.length + owedProps.length} premises in the two ledgers; the rest are \
    not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would \
    take)"

/-- **Reverse test.**  Fails unless the scan reports `p` as an unclassified premise.  The
point of `#assert_rbm_axioms` is that adding an assumption without classifying it breaks
the build; this checks that the mechanism actually fires, on a fixture kept out of the
development (`RBM.Audit.Fixture`). -/
elab "#assert_rbm_audit_detects " p:ident : command => do
  let env ← getEnv
  let n := p.getId
  let found := scanPremises env (fun _ => false)
    (fun n => certificates.any fun (_, c) => c == n)
  let classified := borrowedProps ++ owedProps ++ structuralProps ++ refutedProps ++ supersededProps
  let unregistered := found.filter fun m => !classified.contains m
  unless unregistered.contains n do
    throwError m!"audit reverse test: the scan did not report `{n}` as an unclassified \
      premise; it found {unregistered.toList}"
  logInfo m!"audit reverse test: an unclassified premise is caught ({n})."

end RBM.Audit
