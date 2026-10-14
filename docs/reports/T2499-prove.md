Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 01:45:18 UTC 2026

Targets (mathematics only): at the BA tuple `(seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`, d = 3:
T1 `baPfStep5_of_walk` = `BAStep5IIIWalk → BAStep5IIIFromWalk → STPfStep5gL`; T2 `baPfStep5_holds` = `STPfStep5gL` (`lem:pf_step5`, `3_5:2364-2383`);
T3 `baStep5III_holds` = `STStep5IIIgL` (Step 5 case `λ² ≤ 1-t`, `3_5:2284`). No new mathematics: composition of merged results. T4 = instances of T2, T3 and the assembly.

### (i) Exponent table (all inherited; nothing new)

| quantity | value / where | constraint | slack |
|---|---|---|---|
| `𝔠d` (walk) | `1/100`, `baStep5IIIWalk_holds` (`BA/Step5IIIWalk2:763-765`: `refine ⟨1/100, _, le_rfl, _⟩`) | pin `0 < 𝔠d ≤ 1/100` (`Chain/Step5Gen:191-197`); `(con_st_ind)`: `Bctl^𝔠d ≤ (1-t)/(1-s) < 1` eventually | holds for every `𝔠d > 0` eventually (`s1Setup_conStInd_const`, `Step1Setup:1226`); at `1/100`, `s=1/10`, `t=1/2`: ratio `5/9`, first good n = 26 (below) |
| `κm` | `κm = κ` (`BA/SEforLnBA:152-158`) | `κm ≤ Im m` (field `κ ≤ Im m` of `BAdom`, `BA/MFixedPoint:435`) | `1/2 ≤ 4/5` at the instance (`Im m ≥ 4/5`, `mS_im_half`, `FlowPins:1147`, used `:1215`) |
| `T0 < 1`, `η = (1-t) Im m` | `Step5CasesGen_FlowFacts` (`Chain/Step5CasesGen:140`), BA proof via `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, `rfl` | `T0 = Im m/(Im m + Im z) < 1` | instance: `T0 ≥ 2/3` (`t0_sz0`, `FlowPins:1227`) |
| regime `STReg5III` | `lam_n² ≤ 1 - t_n` (`Induction/Step5Pins:58-59`) | the index set of `STPfConclgL` (`Step5Gen:139-144`) is empty unless this holds | instance `lam_n² ≤ 1/4096 ≤ 1/2` for all n (`Step5IIIGood_reg_sz0`, `:623`) |
| `(log W)^{2(d-2)}` | `((D ln W)²+1)^{d-2} ≤ W^{8𝔡/5}` (`Induction/Step5Cases:281`, used inside `ST_step5_caseIII_of_pfgL`, `Step5CasesGen:406-470`, with `y = (W^d(1-u))⁻¹ ≤ W^{-2𝔡}` from `(eq:WO)`) | `W^{2𝔡} ≤ lam² W^d`, `y^{4/5}·polylog ≤ 1` | at d=3, `𝔡=1/10`: exponent `8𝔡/5 = 4/25`; eventual (conclusion-side) threshold in n: D=1 ≈ 8199, D=40 ≈ 5.6e8 (`poly.out`, below); it is a conclusion-side `∀ᶠ`, not a hypothesis |
| `ε₁, ε₀, D*` (walk grid) | inside `BAStep5IIIWalkConcl` (`Step5IIIWalk2:63-71`): `ε₀ < ε₁`, `D* ≥ D + 2d` | merged, not read here | `D + 6` at d=3 |
| flow constants | `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)` (`flow_sz0`, `FlowPins:1214`) | `BAFlow`: `Admissible 𝔠 𝔡` and `BAdom` | `Bandwidth 1/6`: `N0^{1/6} = 11.3 ≤ W0 = 32`; `WO 1/10`: `W0^{-1.4} = 0.0078 ≤ lam0 = 1/64 ≤ 10`; `N0^{-0.9} = 2.0e-6 ≤ 1/4 ≤ 11/30 ≤ Im z` |
| `Cd` | `Cd = 1` (instance), any `Cd > 0` in the pin | `0 < Cd` | n/a |
| dimension | d = 3 (`3 ≤ d` binder of `STIngR5gL`, `le_rfl`) | U-C5 | n/a |

Hypothesis-set check (T2, T3): T3 needs `Step5CasesGen_FlowFacts 3 …` (= `baStep5CasesGen_flowFacts 3`, merged, guard `∀ κ > 0, ∃ κm > 0, …`) and T2. T1 and T2 need only the two closed Props `baStep5IIIWalk_holds`, `baStep5IIIFromWalk_holds` (merged, no family binder). No `∃ C` after `(sz, z)`; the only `∃` is `𝔠d`, before `(sz, z)`.

### (ii) One concrete nondegenerate instance (T4 (a) (b) (c)), checked by script

Data: `sz0` (`Defs/Sizes:258-262`: `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `N = (WL)^3`; n=0: L=4, W=32, N=2097152, lam=1/64), `zSeq`, `flow_sz0`, `s ≡ 1/10 < t ≡ 1/2 < t0` (`half_lt_t0`), `𝔠d = 1/100`, `Cd = 1`, d = 3. Index set nonempty: `TimeIcc s t = [1/10, 1/2]`, regime holds for all n. Discharged: flow, horizon, regime (`Step5IIIGood_reg_sz0`), `(con_st_ind)` (`s1Setup_conStInd_const`). Hypotheses kept: the nine carrier predicates `STKboundgL, STKwardgL, STLKgL, STDecaygL, STDecayStronggL, STStep1LoopgL, STStep2ConclgL, STLmaxUgL, STLKUgL` (other gates' pins; the last two are the two inline `PrecL` binders of `STIngR5gL`, passed as in `Step5IIIWalk2:1058-1063`). (c): `ST_step5_assemblygL` (`Step5CasesGen:169`) at `t ≡ 1/2` needs only `s n ≤ t n`.

```
$ python3 -I .../scratchpad/T2499/inst.py        (writes inst.out; no Lean)
reg5III: max lam^2 = 0.000244140625 <= 1/2
T0 >= (4/5)/(6/5) = 0.6666666666666667 > 1/2: True (Im m + Im z = 6/5, Im m >= 4/5: FlowPins.lean t0_sz0)
BAdom: 1/2 <= 4/5: True ; N0^(-0.9) = 2.0442456484533175e-06 <= 1/4; 11/30 <= Im z <= 7/10 <= 1
Bandwidth n=0: N^(1/6) = 11.31370849898476 <= W = 32
WO n=0: 0.007812500000000002 <= lam = 0.015625 <= 10
ratio (1-t)/(1-s) = 0.5555555555555556 <1; Bctl(0)^cd = 0.907655507030396 (fails at n=0)
first n0 with Bctl^cd <= 5/9 for all n in [n0,3000): 26 ; Bctl(n0)^cd = 0.5535428423325404 ; W(n0) = 459165024
first n0 for the proof bound (4W^-3)^cd <= 5/9: 27
limit: 4*W^-3 -> 8.46486672970345e-57 (n=3000); (4W^-3)^cd -> 0.27496423060882064 -> 0 as n->inf
index nonempty: TimeIcc s t = [1/10,1/2] nonempty, lam^2 <= 1-t at all n (checked above)
$ python3 -I .../scratchpad/T2499/poly.py        (conclusion-side polylog threshold, d=3, 𝔡=1/10)
D=1: ok for all n >= ~8199 (ln W = 48.5)
D=40: ok for all n >= ~560360361 (ln W = 104.2)
```
(`inst.py` asserts also `lam_n ≤ 1/64`, `N^{1/6} ≤ W`, `W^{-1.4} ≤ lam ≤ 10` for all n < 3000.) `(con_st_ind)` fails at small n (n < 26 at `𝔠d = 1/100`) and holds from `n0 = 26` (proof bound `4W^{-3}`: from 27), a `∀ᶠ` with a moderate threshold; it is the `∀ᶠ` of `STConStInd` (`Induction/Defs:168-169`), so no hypothesis needs a large n. External-hypothesis limit: none of the nine carrier predicates is an external paper input (other gates' pins); the only limit entering the discharged side is `(4 W_n^{-3})^{1/100} → 0` (last script line), which is `Bctl_const_le` (`Induction/Defs:472`) plus `W → ∞`.

Check file (dispatcher's, read-only run in the worktree): `lake env lean docs/tickets/checks/T2499-check.lean` gives `exit 0`, 0 errors, so the pins `T2499_STPfStep5BA`, `T2499_STStep5IIIBA`, `T2499_MainOfParts` and the four shapes elaborate against the merged names.

### Route per target (merged file:line) and import list

```
T1  Step5IIIWalk2:1058-1063 (compiled `example`): intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd; obtain ⟨𝔠d,h0,h1,H⟩ := walk hd κ ε 𝔡 hκ hε h𝔡 Cd hCd;
    refine ⟨𝔠d,h0,h1, fun 𝔠 sz z hflow s t hs hst ht hR hKb … hLKU => ?_⟩; exact fromWalk κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hflow s t hs hst ht hR (H 𝔠 sz z …)
T2  T1 at baStep5IIIWalk_holds (:763), baStep5IIIFromWalk_holds (:977)
T3  ST_step5_caseIII_of_pfgL (Chain/Step5CasesGen:406) 3 _ _ _ _ (baStep5CasesGen_flowFacts 3 (BA/SEforLnBA:152)) baPfStep5_holds
T4  (a) T2 then the Step5IIIWalk2:994-1065 instance route (H at flow_sz0, Step5IIIGood_reg_sz0, s1Setup_conStInd_const, half_lt_t0)
    (b) T3 at the same data  (c) ST_step5_assemblygL (Step5CasesGen:169)
```
Imports: `Step5IIIWalk2` already brings `Step5Gen`, `Step34Gen`, `Step1Setup`, `FlowPins`, `Step5IIIGood`; `SEforLnBA` brings `Step5CasesGen` (checked by import-closure script, 2026-10-14: `SEforLnBA closure has Step5CasesGen: True`; `Step5IIIWalk2` closure lacks `SEforLnBA` and `Step5CasesGen`). List: `RBM3D.BA.Step5IIIWalk2`, `RBM3D.BA.SEforLnBA` (`RBM3D.Chain.Step5CasesGen` optional, harmless).

### Family table, UBA-C1, registry, name clash

- Family: premise 1 (`Step5CasesGen_FlowFacts 3 …`, guarded `∀ κ > 0, ∃ κm > 0`) discharged by `baStep5CasesGen_flowFacts 3` (T3 only); premise 2 (two closed Props) by the two `_holds` (T1, T2); premise 3 (binders of `STIngR5gL`) passed through, nine carrier predicates kept in T4.
- UBA-C1: no size/kernel crossing in the new file (U5's one crossing `baStep5III_lam0_le_lam` is inside U5d); `withLam` only in `seqP (sz.withLam 0)`.
- Registry (`Test/Axioms.lean`, worktree HEAD 3f945e60): `owedProps` line `RBM.BA.STPfStep5gL` at `:213`, T2462 header comment at `:206`, `STDecayStronggL` at `:230`. `scanPremises` (`:469-490`) drops a premise as soon as some theorem has it as conclusion head: `baPfStep5_of_walk` and `baPfStep5_holds` do, so the line must go (otherwise `registryLine` lists it under "carry nothing yet", `:599-609`); `STDecayStronggL` stays (still a hypothesis, no theorem concludes it). `STStep5IIIgL` is unregistered and already concluded by `ST_step5_caseIII_of_pfgL`. Private instance defs (`_private…` names) fail `(`RBM).isPrefixOf` and are not scanned.

```
$ grep -rn "baPfStep5_of_walk\|baPfStep5_holds\|baStep5III_holds\|Step5IIITargets" RBM3D RBM3D.lean | wc -l   (worktree t/T2499)
0
$ ls RBM3D/BA/Step5IIITargets.lean  ->  No such file or directory
```

### Verdicts

- T1 `baPfStep5_of_walk`: PASS (hypotheses = two merged closed Props; route compiled as an `example` at `Step5IIIWalk2:1058-1063`).
- T2 `baPfStep5_holds`: PASS (both inputs merged and proved, `:763`, `:977`).
- T3 `baStep5III_holds`: PASS (premise 1 merged at `SEforLnBA:152`; `d` is the explicit first argument 3).
- T4 instances (a) (b) (c): PASS (every deterministic hypothesis holds at the numbers above; only the nine carrier predicates stay hypotheses).
- Open point for 1b (not a failure): the unification `Step5CasesGen_FlowFacts 3 (fun sz κ ε 𝔠 𝔡 z => BAFlow …) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)` against `baFMz`, `BAflowT0` is eta, checked only at statement level by the check file (`example : Prop`); the term-level application of T3 is the first place it is elaborated as a term.

## (b) Script output (stage 1b, commits 7b82acb5, 0c272838 on t/T2499, Wed Oct 14 01:51:36 UTC 2026)

```
$ wc -l RBM3D/BA/Step5IIITargets.lean            -> 112   (estimate 60 / 100 / 160; design 150 / 250 / 450; stop line 450)
$ lake build RBM3D.BA.Step5IIITargets 2>&1 | tail -1
Build completed successfully (4122 jobs).
$ lake build   (full library, with the registry edit)  tail -1
Build completed successfully (4377 jobs).
$ lake env lean <scratch>/ax.lean   (#print axioms)
'RBM.BA.baPfStep5_of_walk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baPfStep5_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baStep5III_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean <scratch>/pins.lean  (the three T2499_* defs of the check copied under the file's names, plus
   example : T2499_MainOfParts := baPfStep5_of_walk ; example : T2499_STPfStep5BA := baPfStep5_holds ;
   example : T2499_STStep5IIIBA := baStep5III_holds)                 -> exit 0, no output
$ lake env lean docs/tickets/checks/T2499-check.lean 2>&1 | grep -c error   -> 0
```

Target statements (extracted by awk from the file; binder lines cut at 170 columns):
```
theorem baPfStep5_of_walk :
    BAStep5IIIWalk → BAStep5IIIFromWalk →
      STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := by
theorem baPfStep5_holds :
    STPfStep5gL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
theorem baStep5III_holds :
    STStep5IIIgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 :=
```
Route per target (file:line of the new file): T1 `:42-50` (the `Step5IIIWalk2:1058-1063` text with the two inputs as binders);
T2 `:52-54`, T3 `:57-59`.  Family table as used: premise 1 (`baStep5CasesGen_flowFacts 3`, `SEforLnBA:152`) enters T3 only, with the
`_ _ _ _` tuple arguments unified at term level (the open point of (a): it elaborates); premise 2 = the two closed Props, T1/T2;
premise 3 = binders of `STIngR5gL`, passed through.  UBA-C1 as used: no crossing, no size/kernel level read in the file; `withLam` only in
`seqP (sz.withLam 0)` and `seqP (SizesInst.sz0.withLam 0)`.

Compiled nonempty instances (T4), same file `:61-110`; `grep -n '^example\|^private theorem'`:
```
80:private theorem Step5IIITargets_inst_pf (hp : Step5IIITargets_instPrem) :     (a) uses baPfStep5_holds
88:example (hp : Step5IIITargets_instPrem) : STPfConclgL (baFMz sz0 zSeq) (seqP (sz0.withLam 0)) (fun _ => 1/10) (fun _ => 1/2)
93:private theorem Step5IIITargets_inst_step5 (hp : Step5IIITargets_instPrem) :   (b) uses baStep5III_holds
101:example (hp : Step5IIITargets_instPrem) : STStep5ConclgL … (fun _ => 1/10) (fun _ => 1/2)
106:example (hp : Step5IIITargets_instPrem) : STDecaygL … (fun _ => 1/2) ∧ STDecayStronggL … (fun _ => 1/2)     (c) via ST_step5_assemblygL
```
Data: d = 3, `sz0`, `zSeq`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 ≤ t₀` (`half_lt_t0`), `Cd = 1`.  Discharged: flow,
horizon, regime (`Step5IIIGood_reg_sz0`), `(con_st_ind)` (`s1Setup_conStInd_const` at the pin's `𝔠d`).  Hypothesis kept: the private bundle
`Step5IIITargets_instPrem` = the nine carrier predicates of `STIngR5gL` (other gates' pins; the same nine as `Step5IIIWalk2_instPrem`).

Registry edit and scan (`#assert_rbm_axioms`, full `lake build`; before = the new file imported, `Test/Axioms.lean` unedited):
```
before: registry: 2 borrowed + 120 owed + 123 structural + 7 refuted + 18 superseded; 147 registered premise(s) carry nothing yet: [… RBM.BA.STPfStep5gL …]
        (before-build line 6801 of the saved log lists "RBM.BA.STPfStep5gL,")
after:  registry: 2 borrowed + 119 owed + 123 structural + 7 refuted + 18 superseded; 146 registered premise(s) carry nothing yet   ("STPfStep5gL": 0 hits in the log)
both:   axiom audit: 14957 theorems, 4631 definitions, 0 axioms in `RBM` ; premises found by scanning: 123 (borrowed 1, owed 56, structural 46, refuted 6, superseded 14)
$ git diff main...t/T2499 -- RBM3D/Test/Axioms.lean | grep '^[+-] '     (edit: delete the owedProps line `RBM.BA.STPfStep5gL`; append to the T2462 header comment
   "; `STPfStep5gL` left this list (concluded by `baPfStep5_holds`, T2499)"; 1 line removed, 1 line changed, both located by name)
```
Greps on the new file (hypothesis rules):
```
C1 grep (BAK_le_small|…|STGridRepNgL)                       -> 0 hits
X1-C4 grep '^(noncomputable )?(def|abbrev|structure) '       -> 0 hits (one `private def Step5IIITargets_instPrem`, stem-prefixed, not matched)
local copies of STPfStep5gL|STStep5IIIgL|STIngR5gL|Step5CasesGen_FlowFacts|BAStep5III*, and T2459_*/T2462_* text -> 0 hits
withLam outside the two allowed forms -> 0 ; 'gK|≤ A \*' -> 0 ; sorry|admit|native_decide|axiom -> 0
name clash: grep -rn 'baPfStep5_of_walk|baPfStep5_holds|baStep5III_holds|Step5IIITargets' RBM3D RBM3D.lean, outside the new file:
  RBM3D/Test/Axioms.lean:206 (the registry note added here)   RBM3D.lean:600 (the one import line)
git diff main...t/T2499 --stat:  RBM3D.lean | 1 + ; RBM3D/BA/Step5IIITargets.lean | 112 ; RBM3D/Test/Axioms.lean | 3 +-
git diff main...t/T2499 -- RBM3D/BA/Step5IIIWalk.lean RBM3D/BA/Step5IIIWalk2.lean RBM3D/BA/SEforLnBA.lean RBM3D/Chain RBM3D/Induction | wc -l  -> 0
importers of Step5IIITargets: RBM3D.lean only
```
Ports: none (no text from RBM1D/RBM2D); the proof text of T1 is the merged `Step5IIIWalk2:1058-1063` example, reused in this project.

Narrative.  A composition of merged results; no preflight correction needed ((a′) absent).  The new file's three theorems and instances built on the
first elaboration.  The `T2499_*` pins match the targets up to the name (pins.lean above).  `ST_step5_assemblygL` takes the explicit `hst`, supplied as `s ≤ t` at the instance.
(7) U5's landed total: the ticket states U5a–U5d = 7,718 lines; this row adds 112 (new file) → 7,830, against T2459 (d)'s 6,900 (the 7,718 is the ticket's figure, not recomputed here).

## (c) Verified Mathlib names

None used (no Mathlib name appears in the new file beyond `one_pos`, `le_rfl`, `norm_num`, all elaborated).

## (d) Open issues and paper-delta candidates

- None new.  T2459a (D702, "we therefore omit the details", `7_8:2101`): its open note "U5e not yet written" closes with `baPfStep5_of_walk`, `baPfStep5_holds`, `baStep5III_holds`.
- BA case (iii) is proved at d = 3 only (U-C5); the nine carrier predicates of `STIngR5gL` (incl. `STDecayStronggL`, owner V) remain hypotheses of the instances.
- Observation: `lake build RBM3D.BA.Step5IIITargets` prints seven long-line warnings for the module doc (lines 13-24, before the `set_option`); no statement affected.
