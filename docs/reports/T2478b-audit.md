Auditor model: claude-opus-5-5
# T2478b audit (T1b of T2478: targets 7-11), round 1 — Tue Oct 13 02:06:38 UTC 2026
Branch `t/T2478b` HEAD 3166b5d9, merge-base with `main` 6039f7ed (T1a merged). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2478b-audit1` (detached). Scratch: `<scratchpad>/T2478b/`.

## 1. Diff, build, axioms, hygiene
```
$ git diff --stat main...t/T2478b
 RBM3D/Chain/OptL2Gen.lean      | 1423 +++   RBM3D/Chain/Step2CloseGen.lean |  921 +++   RBM3D/Test/Axioms.lean |  4 +-
$ git diff --stat main...t/T2478b -- RBM3D/Induction RBM3D/Path RBM3D/Evolution RBM3D/BA RBM3D/Chain/Step2Gen.lean RBM3D/Chain/Step2Kern.lean \
    RBM3D/Chain/Carrier.lean 'RBM3D/Chain/DecayGen*.lean' 'RBM3D/Chain/Step2EventsGen*.lean' RBM3D/Chain/NewKLKGen.lean RBM3D/Chain/CltGen.lean \
    RBM3D/Chain/Step2IterGen.lean RBM3D/Chain/Step2IterGen2.lean RBM3D.lean | wc -l
       0                                    # G1 (target 12) and T1a files untouched
$ lake build RBM3D.Chain.OptL2Gen RBM3D.Chain.Step2CloseGen    (errors/warnings of the two new files: none; tail)
Build completed successfully (3854 jobs).   exit 0
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^ *(private )?axiom |set_option maxHeartbeats" OptL2Gen.lean Step2CloseGen.lean | wc -l
       0
$ lake env lean Audit.lean    # #print axioms of all 21 public theorem/def of the two files
'RBM.BA.OptL2aJg' / 'optL2Gen_bandStep2_OptL2aJ' / 'stOptL2a_driftg' / 'stOptL2a_martingaleg' / 'stOptL2a_gronwallg' / 'stOptL2_of_pinsg' /
'optL2Gen_stOptL2_of_pins_band' / 'Step2IterGen_ListLink' / 'step2IterGen_listLink_band' / 'STthetaOpg_eq_ThetaN' / 'STLMg_eq_STLIMg' /
'STLKMg_eq_STLKIMg' / 'STELKLKMg_eq_STelklkMg' / 'STEGtMg_eq_STegtMg' / 'STEEMg_eq_STeeMg' / 'STgAg_eq_STgANg' / 'STgDriftg_eq_STgDriftNg' /
'stStep2LocalPT_of_L2decayDecG' / 'stLocalAvgOfL2_holdsDecG' / 'step2CloseGen_stLocalAvgOfL2_band' / 'step2CloseGen_step2_of_pinsLW''
  each: depends on axioms: [propext, Classical.choice, Quot.sound]        (21 lines, 0 errors in the file)
$ lake env lean docs/tickets/checks/T2478-check.lean | grep -c error ; exit
0   exit 0
```
Library scan (scratch copy of `RBM3D.lean` with the two root imports after the last `import`; `RBM3D.lean` itself not edited):
```
$ diff RBM3D.lean Root.lean
553a554,555
> import RBM3D.Chain.OptL2Gen
> import RBM3D.Chain.Step2CloseGen
$ lake env lean Root.lean
axiom audit: 14253 theorems, 4499 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 61, structural 45, refuted 6, superseded 14).        exit 0
$ lake build RBM3D      # the branch's RBM3D.lean as is (without the two imports)
error: RBM3D.lean:556:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, ...
```
The branch's registry is consistent only once the two root imports are in (the `STOptL2gL` line is removed because `stOptL2_of_pinsg` concludes it). The hub's §3 (A)4 step adds them; see Observation O1.

Registry diff (`Test/Axioms.lean`, owed list): `-` the T1a line `RBM.BA.STOptL2gL` ("concluded by `stOptL2_of_pinsg` (T2478 T1b ...), which removes this line"); `+` `RBM.BA.STStep1LoopgL` (owed, the generic Step 1 premise, beside `STStep1WeakgL` at `:146`). This matches the hub's instruction "move it as the registry rules ask" and the line text on main.

## 2. Layering and ticket greps
```
$ grep -n '^import' OptL2Gen.lean Step2CloseGen.lean
OptL2Gen.lean:6:import RBM3D.Chain.Step2IterGen     OptL2Gen.lean:7:import RBM3D.Induction.OptL2b
Step2CloseGen.lean:6:import RBM3D.Chain.Step2IterGen2   :7:import RBM3D.Chain.OptL2Gen   :8:import RBM3D.Induction.LocalAvg2   :9:import RBM3D.Evolution.FarEntry
$ python3 -I cone.py . RBM3D.Chain.OptL2Gen RBM3D.Chain.Step2CloseGen RBM3D.Induction.EMn2Exp2
RBM3D.Chain.OptL2Gen cone modules: 114 BA modules: [] DifREP2/EMn2Exp2/LWTermHolds in cone: []
RBM3D.Chain.Step2CloseGen cone modules: 151 BA modules: [] DifREP2/EMn2Exp2/LWTermHolds in cone: []
RBM3D.Induction.EMn2Exp2 cone modules: 97 BA modules: ['RBM3D.BA.FlowPins', 'RBM3D.BA.MFixedPoint'] ...
$ grep -rln "import RBM3D.Chain.\(OptL2Gen\|Step2CloseGen\)$" RBM3D RBM3D.lean
RBM3D/Chain/Step2CloseGen.lean
TN-C4  grep -nE "STGridRepNgL|ST_gridMart_of_repN|stGridRepN_holds" (both files) | wc -l   ->  0
UBA-C1 grep -nE "\bgK\b|BAflowLam0|withLam|lam0" (both files) | wc -l                      ->  0
U-C4   grep -nE "^(noncomputable )?(private )?def": OptL2Gen:59 OptL2aJg (ℝ); Step2CloseGen:65 Step2IterGen_ListLink (Prop); :370-379 private ℝ constants K1/K2/S/C2
X1-C1  generic regions (OptL2Gen 52-1246, Step2CloseGen 166-804): hits only `(hNew : Step2IterGen_NewKLK d Flow mk)` x3 (pattern `KLK d` in the class name); Step2CloseGen 166-804: 0
open private: Step2CloseGen.lean:49  la2_zdistInf_add_le la2_zdistInf_neg la2_zdistInf_zero from RBM3D.Induction.LocalAvg2   (no private deleted)
```

## 3. Statements against the pins (scratch `Audit.lean` = check-file imports + `import RBM3D.Chain.Step2CloseGen` + check Part 1-2 up to `### Shapes` + the block)
```
example : T2478_OptL2OfPinsg := @stOptL2_of_pinsg                                  -- target 8
example : T2478_LocalReaderDec := @stStep2LocalPT_of_L2decayDecG                    -- target 9
example : T2478_LocalAvgOfL2Dec := @stLocalAvgOfL2_holdsDecG                        -- target 9
example {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) : T2478_ListLink Cm ↔ Step2IterGen_ListLink Cm := Iff.rfl   -- target 10
$ lake env lean Audit.lean 2>&1 | grep -c error
0
```
Target 7 (no `T2478_*` pin; shapes = substitution map over the band statements, 1a-audit O2). Token diff of the conclusions (after the binder `(h𝔡 : 0 < 𝔡) :`), band `OptL2a.lean` mapped by `pathP sz, pathH sz, STFlow, lemT, STStep1Loop/Weak, STLK, OptL2aJ ↦ Cm.Pp, Cm.Hpath, Flow, T0, …gL, OptL2aJg`:
```
$ python3 -I t7diff.py RBM3D/Induction/OptL2a.lean RBM3D/Chain/OptL2Gen.lean
stOptL2a_drift -> stOptL2a_driftg: token diff after map: ['- Gauss.HighProbAt', '+ HighProbAt', '- ((mk', '+ (mk', '- z).Pp)', '+ z).Pp',
  '- ‖STgDrift', '+ ‖STgDriftg', '+ (mk', '+ z)', '- (STflowE', '- z', '- n)', '- ((etaT', '- (STflowE', '- z', '- n)', '+ (((mk', '+ sz', '+ z).eta', '+ n']
stOptL2a_martingale -> stOptL2a_martingaleg: token diff after map: ['- STgA', '+ STgAg', '+ (mk', '+ z)', '- (STflowE', '- z', '- n)', ... (same pair x3, STgA/STgDrift)]
stOptL2a_gronwall -> stOptL2a_gronwallg: token diff after map: none
```
Residues are exactly the map items `STgDrift/STgA sz (STflowE z) ↦ STgDriftg/STgAg Cm`, `etaT (STflowE z n) ↦ Cm.eta n` (my map did not cover their per-`n` argument form), a namespace prefix and parentheses: no change of quantifier order, exponents (`3/2`, `5/4`, `-2`, `-D`), windows or grid. The generic hypotheses added before `κ ε 𝔡` are F1-F2, F9, F3, the Hermitian walk, `STBdatagL`, `STLWBgL`/`STEMn2PolygL`/`STGridMartgL`, target 1: the ticket's list (target 7, §Inputs (b)-(c)). In addition each band statement is recovered from the generic one (OptL2Gen.lean `example : type_of% @RBM.Gauss.Sizes.stOptL2a_drift/_martingale/_gronwall`, `type_of% @stOptL2_of_pins`; Step2CloseGen `type_of% @stLocalAvgOfL2_holds`; all compile in the build above).
Target 10: the seven identities (Step2CloseGen:82-152) are the band `STthetaOp_eq_ThetaN`, `STLM_eq_STLIM`, `STLKM_eq_STLKIM`, `STELKLKM_eq_STelklkM`, `STEGtM_eq_STegtM`, `STEEM_eq_STeeM`, `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN` over `Cm` with `hL : Step2IterGen_ListLink Cm` (`STthetaOpg_eq_ThetaN` is `rfl`, no `hL`); `ST_gridMart_of_repN` not restated (TN-C4 grep 0).
Target 11 (`step2CloseGen_step2_of_pinsLW'`, Step2CloseGen:836):
```
theorem step2CloseGen_step2_of_pinsLW' {d : ℕ} (hd : 3 ≤ d) (hLW : LWterm d) (hLWE : LWtermExp d)
    (hEMe : STEMn2Exp d) (hMart : STGridMart d) : STStep2 d
band (Step2Iterate:1793): ST_step2_of_pinsLW' (hd : 3 ≤ d) (hNew : STNewKLK d) (hLW : LWtermExp d) (hEMe : STEMn2Exp d)
    (hRep : STGridRepN d) (hOpt : STOptL2 d) (hClos : STLocalAvgOfL2 d) : STStep2 d
```
Ticket text: "every pin discharged by merged band producers and `LWtermExp d` as a hypothesis (as `ST_step2_of_pinsLW'`; no `Graph/LWTermHolds` import)". Delivered keeps three more hypotheses, each a merged theorem outside the ticket's cone: `LWterm` (`lwterm_holds`, `Graph/LWTermHolds.lean:682`, excluded by the ticket; needed by `STLWB_of_LWterm` for target 8), `STEMn2Exp` (`stEMn2Exp_holds`, `Induction/EMn2Exp2.lean:1274`, cone has `BA.FlowPins`, `BA.MFixedPoint`: excluded by the no-BA closure), `STGridMart` (`stGridMart_holds`, `Path/DifREP2.lean:2283`, not in the ticket's import list). So the ticket's literal text for target 11 cannot be met inside its own layout (`STEMn2Exp` at least). The delivered form is the closest reading; the choice (accept as delivered / allow a `Path/DifREP2` import for `STGridMart` / take `STOptL2` instead of `LWterm`, as the band does) is the dispatcher's. The prover raised it as T2478e. **Needs dispatcher sign-off.**

## 4. Vacuity, hidden hypotheses, cycles
- The new carrier class `Step2IterGen_ListLink` is a two-conjunct `Prop` def (no structure fields), discharged at the band by `step2IterGen_listLink_band` (`STLM_eq_STLIM`, `rfl`). No new `structure`/`class`; no field of `FlowFM`/`Step2Mat`/`Step2Data` added.
- No cycle: OptL2Gen ← Step2IterGen (merged), Step2CloseGen ← Step2IterGen2, OptL2Gen (cone script above); no importer other than Step2CloseGen.
- Premises left open in the public statements are registered pins: `STLWBgL`, `STEMn2PolygL`, `STGridMartgL`, `STBdatagL`, `STGiiGEXgL`, `STGijDecgL`, `STGavLGEXgL`, `STStep1WeakgL`, `STStep1LoopgL` (newly owed), `STL2decayPTgL` (concluded by T1a), `STLKgL`; library scan passes with the two imports (section 1). Target 11's four hypotheses are all proved merged theorems (see above), so the corollary is not vacuous. No external (unauthorized) hypothesis is introduced.

## 5. Compiled nonempty instances (data: `d = 3`, `sz0` with `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, flow `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, window `s ≡ 0`, `t ≡ 1/16`, `𝔠_d = 1/26`)
```
$ grep -c '^example' OptL2Gen.lean Step2CloseGen.lean
OptL2Gen.lean:8   Step2CloseGen.lean:7
```
| target | example | discharged at the data | left as hypothesis |
|---|---|---|---|
| 7 drift/martingale/Grönwall | OptL2Gen 1277/1297/1309 (`τ = 1`, `D = 1`, `K_n = ⌈N^CK⌉`) | F1-F3, F9, Hermitian walk, `STBdatagL`, target 1 (`step2IterGen_newKLK_band`), `STEMn2PolygL` (`stEMn2Poly_holds`), `(con_st_ind)` (`conStInd_inst`), time ranges | `STLWBgL`, `STGridMartgL` (pins), `STLKgL`, Step 1 (stochastic) |
| 8 `stOptL2_of_pinsg` | OptL2Gen 1340 | same | same |
| 9 reader, closing pin | Step2CloseGen 853, 865 | `flowOK`, size data, `(GiiGEX)`, `(GavLGEX)` (`stGbEXP_holds`), `STGijDecgL` (`bandFM_STGijDecgL_of_three_le`) | `STStep1WeakgL`, `STL2decayPTgL` |
| 10 | Step2CloseGen 884/886/900 at `n = 100`, `u = 1/32` | class by `step2IterGen_listLink_band` | none |
| 11 | Step2CloseGen 910 (`inst_step2`) | all cone producers | `LWterm 3`, `LWtermExp 3`, `STEMn2Exp 3`, `STGridMart 3` |
No `N = 0`, empty index, collapsed window or `False` premise; window `[0, 1/16]` nonempty, `L_n ≥ 4`; all compile in the module build.

## 6. Paper deltas
`docs/paper-deltas.md` has no T2478 entry yet (numbered at merge). Candidates in the prove report: T1a's T2478a-c (`T2478-prove.md`), T2478d (target 9: shift lemma + lattice sum in place of `(eq:Psirelations)`, `7_8:2033-2050`), T2478e (target 11's four hypotheses). Every Lean/paper difference found above (target 9 route, carrier-level inputs, target 11 hypotheses) is covered.

## 7. Verdict per target
- Target 7 (`OptL2aJg`, `stOptL2a_driftg`, `_martingaleg`, `_gronwallg`): **PASS**.
- Target 8 (`stOptL2_of_pinsg` = `T2478_OptL2OfPinsg`): **PASS**.
- Target 9 (`stStep2LocalPT_of_L2decayDecG` = `T2478_LocalReaderDec`, `stLocalAvgOfL2_holdsDecG` = `T2478_LocalAvgOfL2Dec`; band recovered): **PASS**.
- Target 10 (`Step2IterGen_ListLink` = `T2478_ListLink` by `Iff.rfl`, seven identities): **PASS**.
- Target 11 (`step2CloseGen_step2_of_pinsLW'`): builds, axioms clean, instance compiled, not vacuous; the statement keeps `LWterm`, `STEMn2Exp`, `STGridMart` beyond the ticket's "only `LWtermExp`", which the ticket's own layout makes unattainable. **PASS subject to dispatcher sign-off** (question: accept the four-hypothesis form, or amend the row).
- Target 12 (G1): diff empty, **PASS**.

Overall: PASS on targets 7-10 and 12; **needs dispatcher sign-off** on target 11 (T2478e).

## Observations (no RETURN)
- O1. `RBM3D.lean` (ticket: sole writable, import lines) is not edited on the branch; as it stands, `lake build RBM3D` on `t/T2478b` fails the registry check (`STOptL2gL` removed, `stOptL2_of_pinsg` not imported). With the two imports (hub §3 (A)4) the scan passes (section 1). The hub must add both lines before the full build.
- O2. Prove report (2) cone counts (115/152) include the module itself; my script counts 114/151 without it. No effect.
- O3. `(a′) 4`: `StepDecompGen_LoopForm` covers only the `LM` conjunct of `Step2IterGen_ListLink`; the bridge of dispatcher answer (5) was not used. No statement effect (the class is discharged at the band; BA instance is T1-BA).
