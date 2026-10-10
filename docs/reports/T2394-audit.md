Auditor model: claude-opus-5-5

# T2394 audit (BA-L0: generic LW pins over the carrier), round 1. Sat Oct 10 22:14:59 UTC 2026

Branch `t/T2394` at 3efd9da (base 5ba1ebe). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2394-audit1` (detached).
Pin source: the ticket's check file pins only names (no statement text), so the statement pin is the probe
`t/T2387:RBM3D/Probe/T2387Pins.lean:39-244`, with the renamings and drops the ticket requires (L2).

## 1. Statements against the probe pin (script diff)

`blocks.py` extracts every `def/abbrev/theorem` block from the probe and from the two new files, substitutes
`C.msig n σc` by its probe body `(if σc then C.m n else (starRingEnd ℂ) (C.m n))` (ticket: `FlowFM.msig` not to be
copied), renames `STLWBG/STLWTG -> STLWBgL/STLWTgL` (merged `Step2Gen` names), and compares the text.
```
$ python3 -I blocks.py probe.lean RBM3D/Chain/LWGen.lean RBM3D/BA/LWPinsBA.lean > blocks.out; awk <summary> blocks.out
IDENTICAL (32): LWcutg->LWcutg LWEg->LWEg LWAvgLawgL->LWAvgLawgL LWLoop2gL->LWLoop2gL LWAssmgL->LWAssmgL 
LWLoopExpgL->LWLoopExpgL LWAssmExpgL->LWAssmExpgL LWtermG->LWtermG LWtermExpG->LWtermExpG LWtermEXPG->LWtermEXPG 
PinFam->PinFam bandPin->bandPin baPin->baPin band_LWE->band_LWE band_LWAvgLaw->band_LWAvgLaw band_LWAssm->band_LWAssm 
band_LWAssmExp->band_LWAssmExp LWterm_iff->LWterm_iff LWtermExp_iff->LWtermExp_iff LWtermEXP_iff->LWtermEXP_iff 
STLWB_iff->STLWB_bandPin STLWT_iff->STLWT_bandPin band_LWtermG->band_LWtermG band_LWtermExpG->band_LWtermExpG 
band_LWtermEXPG->band_LWtermEXPG band_STLWBG->band_STLWBgL band_STLWTG->band_STLWTgL BALWterm->BALWterm 
BALWtermExp->BALWtermExp BALWtermEXP->BALWtermEXP BASTLWB->BASTLWB BASTLWT->BASTLWT
DIFFERS: (none)
absent on branch: FlowFM.msig STEGtg STLWassmgL STLWBG STLWTG STEMn2ExpG band_STEGt band_STLWassm STEMn2Exp_iff 
band_STEMn2ExpG BASTEMn2Exp
branch-only: Ψ0 Ψ0_window ell0
```
(`Ψ0`, `Ψ0_window`, `ell0` are `private` instance data.) Every absent name is one the ticket
excludes: `FlowFM.msig`, `STEGtg`, `STLWassmgL`, `STLWBG/STLWTG` (merged `Step2Gen` names used instead),
`STEMn2Exp*` (row T2-BA), `band_STEGt`/`band_STLWassm` (merged `bandFM_STEGt`/`bandFM_STLWassm`).
```
$ grep -nE "^(def|abbrev|theorem) (STmsigg|STEGtg|STLWassmgL|STLWassmExpgL|STLWBgL|STLWTgL|STEMn2ExpgL|STEMn2Exp|FlowFM\.msig)\b" <both new files> | wc -l
0
```
Kernel check of the bridges (the strongest statement check: each generic pin at the band data *is* the merged band pin):
all seven `Iff.rfl`/`rfl` bridges and `STLWB_bandPin`/`STLWT_bandPin` compile (build below). Hypotheses, quantifier
order (`3 ≤ d →` first, fixed `κ ε 𝔡`, then `𝔠 sz z`, `Flow`, `t`, window/assumption, then `D`), exponents
(`Φ(0)Φ(|a-b|)²`, `B^{1/2}`, `B^{5/2}`, `(log W)^10`, `W^{-d}`), and index sets (`lam²/L^d ≤ 1-t` subtype) are thus
forced to coincide with `Graph/LWPins.lean` `LWterm`/`LWtermExp`/`LWtermEXP` at the band carrier.
Extra check in scratch (`ax.lean`): `example : bandPin LWtermG 3 = RBM.Gauss.Sizes.LWterm 3 := rfl` compiles.

## 2. Hidden hypotheses, vacuity, cycles

- `PinFam` is a type `abbrev`; `bandPin`/`baPin` are plain applications. No new structure. `FlowFM`
  (`Chain/Carrier.lean:55-69`, merged) has data fields only (`L K G M S eta m`), no `Prop` field.
- BA readings are `abbrev ... : ℕ → Prop` with no proof (owed BA-L6 / T1-BA, T7-BA), as the ticket requires.
- Import check (ii), and no cycle:
```
$ python3 -I clos.py . RBM3D.Chain.LWGen   (forbidden = Graph.LWTermHolds|LWExpTerm*|LWMoment*|AuxGraph*|Step2Events|Step2Iterate|LWPinsBA)
RBM3D.Chain.LWGen closure size 70
forbidden in closure: []
$ grep -rln "import RBM3D.Chain.LWGen\|import RBM3D.BA.LWPinsBA" RBM3D RBM3D.lean
RBM3D/BA/LWPinsBA.lean
RBM3D.lean
```
- Dependencies of the band theorems are merged results (`lwterm_holds`, `lwtermExp_holds`, `lwTermEXP_holds`,
  `STLWB_of_LWterm`, `STLWT_of_LWtermExp`); no external hypothesis is introduced.

## 3. Compiled nonempty instances (`d = 3`)

- Band instances `band_LWtermG`, `band_LWtermExpG`, `band_LWtermEXPG`, `band_STLWBgL`, `band_STLWTgL`: closed
  theorems at `d = 3` with no hypotheses (`LWPinsBA.lean:57-61`).
- `example : Prop := BALWterm 3` (`:84`), as the ticket requires.
- Three BA readings applied at concrete data (`:88-106`): `sz0` (`n=0`: `L=4`, `W=32`, `λ=1/64`), `flow_sz0`
  (`κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`), `t ≡ 1/2` with `half_lt_t0 : 1/2 < BAflowT0 sz0 zSeq n`, `ε₀ = 1/10`,
  `Ψ_n = W_n^{-1/2}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}` proved for every `n` by `Ψ0_window`), `ℓ ≡ 0` (`ell0`),
  `D = 1`. Deterministic hypotheses (`3 ≤ 3`, positivity, flow, horizon, window, `ℓ` range) are discharged; the
  hypotheses left are the stochastic pins of other gates (`STInitialGT2gL`, `LWLoopExpgL`, `STLWassmExpgL`,
  `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL`). Not degenerate: `N = (W L)^3 > 0`, no empty
  index, window strict on both sides (ratios `W^{-1}`, `W^{-2/5}`), no `False` premise.
All compile (module build below).

## 4. Build, axioms, hygiene, diff

```
$ lake build RBM3D.Chain.LWGen RBM3D.BA.LWPinsBA | tail -1 ; echo exit $?
Build completed successfully (3963 jobs).
exit 0
$ grep -nE "LWGen|LWPinsBA" build.log | grep -c warning     # all are linter.style.longLine in module docstrings
11
$ lake build RBM3D 2>&1 | grep -E "RBM3D.lean|Build completed"     # registry pre-check (#assert_rbm_axioms)
info: RBM3D.lean:439:0: axiom audit: 11230 theorems, 3376 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4207 jobs).
$ lake env lean ax.lean
'RBM.BA.band_LWtermG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWtermExpG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWtermEXPG' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_STLWBgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_STLWTgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWterm_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWtermExp_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWtermEXP_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLWB_bandPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.STLWT_bandPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAvgLaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAssm' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.band_LWAssmExp' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Chain/LWGen.lean RBM3D/BA/LWPinsBA.lean | wc -l
0
$ lake env lean docs/tickets/checks/T2394-check.lean ; echo exit $?      (on the branch)
exit 0     (0 error lines)
$ git diff --name-status main...t/T2394
M	RBM3D.lean
A	RBM3D/BA/LWPinsBA.lean
A	RBM3D/Chain/LWGen.lean
$ git diff main...t/T2394 -- RBM3D.lean     (two lines after `import RBM3D.BA.EKSum`, before #assert_rbm_axioms)
+import RBM3D.Chain.LWGen
+import RBM3D.BA.LWPinsBA
$ wc -l RBM3D/Chain/LWGen.lean RBM3D/BA/LWPinsBA.lean      (stop line 600)
151 + 111 = 262 total
```
G1: no merged file other than `RBM3D.lean` is touched; `Test/Axioms.lean` unchanged, and the registry passes without
an owed line (no theorem takes `BALW*`/`BASTLW*` as a hypothesis yet). Frozen signatures untouched.

## 5. Paper deltas

The prove report proposes T2394a (carrier pins read `C.S`, `C.L`, `C.m`, `C.eta` in place of `SB`, `Lloop`, `mE`,
`etaT`; equal at the band by `Iff.rfl`) and T2394b (`STLWBgL`/`STLWTgL` carry no `3 ≤ d`; the BA readings are
provable only at `3 ≤ d`). These cover the only Lean/paper differences the new statements introduce; all other
content is the merged band pins verbatim at the band carrier.

## 6. Verdicts

| target | verdict |
|---|---|
| `Chain/LWGen.lean` (10 carrier names, `PinFam`, `bandPin`, 9 bridges) | PASS |
| `BA/LWPinsBA.lean` (`baPin`, 5 BA readings, 5 band instances, instances) | PASS |
| `RBM3D.lean` (two import lines) | PASS |

Observations (no RETURN):
- O1: `BASTLWB 3` has no applied example (the ticket requires only `BALWterm 3` as a `Prop`; the other three readings
  are applied).
- O2: 11 `linter.style.longLine` warnings in the module docstrings of both new files (the `set_option` comes after the
  docstring). Style only.
- O3: the check file pins names only, so the statement comparison is against the probe text (section 1).
