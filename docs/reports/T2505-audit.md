Auditor model: claude-opus-5-5
# T2505 audit, round 1: row a (U3s4a, targets 1-5). 2026-10-14 12:06 UTC

Inputs: ticket `docs/tickets/T2505.md`, check `docs/tickets/checks/T2505-check.lean`, report `docs/reports/T2505-prove.md`. Branch `t/T2505` at 2a7ddae2, merge-base with `main` d3104f3b.
Audit worktree: `../RBM3D-wt/T2505-audit1`, detached at 2a7ddae2 (it already existed and was clean: `git status --short | wc -l` gave 0). Scratch files: `$SCRATCH/T2505/`.

## 0. Diff scope
```
$ git diff --name-status main...t/T2505
M	RBM3D.lean
A	RBM3D/Chain/QtBootGen.lean
A	RBM3D/Chain/QtXiRoundLiftGen.lean
M	RBM3D/Test/Axioms.lean
$ git diff --stat main...t/T2505 -- RBM3D/Induction RBM3D/BA RBM3D/Graph | wc -l
       0
```
`RBM3D.lean`: two `import` lines added after `import RBM3D.Chain.QEndB1Gen`, before `#assert_rbm_axioms`. `Test/Axioms.lean`: one `owedProps` line, `` `RBM.BA.STXiRoundgL' ``, which is the registry line the ticket expects for row a. Every touched file is a sole writable file of row a. The six band files, `Step3` and `Step4` are unchanged.

## 1. Statements against the pins (script diff, then compiled equalities)
```
$ diff <T2505_XiRoundgL' from check, renamed> <STXiRoundgL' from QtBootGen.lean:55, renamed>        -> exit=0 (identical)
$ diff <T2505_FlowModFam, whitespace-normalised> <QtBootGen_FlowModFam, whitespace-normalised>    -> exit=0 (identical)
```
The scratch file `AuditCheck.lean` contains `import RBM3D.Chain.QtXiRoundLiftGen` and the check's Part 2 (lines 75-173, verbatim), followed by:
```
example … : T2505_XiRoundgL' Cf μ s t = STXiRoundgL' Cf μ s t := rfl                                   -- target 1
example … : T2505_FlowModFam d law Flow mkM = QtBootGen_FlowModFam d law Flow mkM := rfl               -- row 16
example : T2505_XiBootROfRound QtBootGen_Hyp := fun d R law Flow mkM T0 hH h => stXiBootRgL'_of_round d R law Flow mkM T0 hH h   -- target 2
example … : STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 =
    STIngRgL d STCaseI law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) := rfl
example : ∀ d, STOeqQt' d := stOeqQt'_holds_of_gen          -- target 5, the same type as RBM.Ind.stOeqQt'_holds
$ lake env lean $SCRATCH/T2505/AuditCheck.lean   -> exit=0, 0 lines containing "error"
```
**Target 4.** The conclusion of `stOeqQtgL'_of` (`QtXiRoundLiftGen:466`) is literally `STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0`, the merged pin read under its own name. I compared its premise list with the merged `stOeqQtRoundPTgL''_of` (`QEndB1Gen:886`) by script, with comment lines removed:
```
$ diff <stOeqQtRoundPTgL''_of binders> <stXiRoundQtgL_of binders>
54,…c54,57   (only difference: after hB45 the target adds)
>     (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
$ diff <stXiRoundQtgL_of binders> <stOeqQtgL'_of binders>   -> only the conclusion line differs
```
The premises are therefore exactly rows 1-13, 15 and 16 of the ticket's family-premise table: the T2498 premises unchanged, then `NQEndFlowGen_KLipFam` (merged, T2491) and `T2505_FlowModFam` (= the merged text). There is no D1 premise, which belongs to row b.

**Target 2.**
- `stBoot_roundsg` is band `stBoot_rounds` (`QtNonzeroBoot:136`) with `Prec sz` replaced by `PrecL sz μ`. All other binders are the same, as the ticket requires.
- `stXiBootgL'_of_round` replaces the band's `STFlow` and `lemT` data with these premises: carrier `LoopForm`, `‖m‖ ≤ 1`, `DecayGen_Spec`, `Admissible`, `RangeCond τ t` (`0 < τ`), `LemDecCalELipG_FlowMod Cm μ c`, `STKboundgL`, and `0 ≤ s < t < 1`. Its conclusion is `STXiBootgL'`.
- `stXiBootRgL'_of_round` matches `T2505_XiBootROfRound` (the compiled example above). The regime `R` is a parameter, and `Hyp := QtBootGen_Hyp`, which the check leaves to row a's 1a.

**Target 3.**
- `stXiRoundgL'_of_PTfam` (`QtXiRoundLiftGen:364`) takes `STOeqQtRoundPTgL''` to `STIngRgL d STCaseI … STXiRoundgL'`.
- Its premises are table rows 2, 3, 4 and 12, plus rows 15 and 16, all guarded by `0 < κ → Flow`.
- The ticket pins no name for target 3. The carrier-level lift is private (`QtLiftGen_lift`); the report's (d) proposes this as `T2505d`.

**Target 5.**
- `QtXiRoundLiftGenCheck.stOeqQtgL'_band (d) (hd : 3 ≤ d) : STOeqQtgL' d seqP STFlow (bandStep2Mat · (STflowE ·)).toFlowFM lemT` has no open hypothesis: every row is discharged at the band (`QtXiRoundLiftGen:590-626`).
- `stOeqQt'_holds_of_gen (d) : STOeqQt' d` has the band statement's type.

Quantifier order: `QtBootGen_FlowModFam` has `∀ κ ε 𝔡, … ∃ c, 0 ≤ c ∧ ∀ sz 𝔠 z, Flow … →`, so the pinned `∃ c` comes after `(κ, ε, 𝔡)` and before `(sz, z)`. T2498's `∃` are unchanged.
```
$ grep -cE "∀ \(sz : Sizes d\)" QtBootGen.lean QtXiRoundLiftGen.lean
QtBootGen.lean:9   QtXiRoundLiftGen.lean:56
```
I read every hit in the signatures above. Each is guarded by `0 < κ → Flow …` or is one of the merged unguarded T2498 rows (`hLaw`, `hC`, `hWard`, `hSeq`, `hS`, `hKK`, copied unchanged). There is no `∀ n` drift or hierarchy premise: `hExp`, `hKL`, `hKT` and `hU` are `∀ᶠ n`.

## 2. Hidden hypotheses, vacuity, cycles
- No `structure` is introduced. `QtBootGen_Hyp` is a `def` conjunction, the `Hyp` parameter the check leaves to row a. It is discharged with no hypothesis at the band family by `qtBootGen_hyp_band (d)` (`QtBootGen:450`), so it is not vacuous.
- `QtBootGen_FlowModFam` is the merged U4s3 text (identical, section 1), discharged by `qtBootGen_flowModFam_band` (`c = 1`). Its BA source, `baLemDecCalELipG_flowMod` (T2501), is merged.
- Every premise of the endpoint `stOeqQtgL'_of` is discharged at the band family in `stOeqQtgL'_band` with no open hypothesis. So the premise set is satisfiable at every `d ≥ 3`, and no limit check is owed: row a adds no external hypothesis.
- Cycles: the new files import only merged modules, and no band, Chain or BA file imports them.
```
$ grep -n '^import' <new files>
QtBootGen.lean: Induction.QtNonzeroBoot, Induction.LemDecCalELip, Chain.NQEndFlowGen, Chain.NQGood1Gen, Chain.KDecayGen, Chain.Step6KitGen
QtXiRoundLiftGen.lean: Chain.QtBootGen, Chain.QEndB1Gen, Induction.QtXiRoundLift
$ grep -rlnE 'import RBM3D.Chain.Qt(BootGen|XiRoundLiftGen)' RBM3D RBM3D.lean
RBM3D/Chain/QtXiRoundLiftGen.lean
RBM3D.lean
```
There is no `BA/*` or `Chain.Step2Kern` import.

Hypothesis rules. I ran my own `stmts.py` over each public `def`/`theorem` statement, cut at the first top-level `:=`:
```
QtBootGen.lean:55  def STXiRoundgL' hits=[]          QtBootGen.lean:83  def QtBootGen_FlowModFam hits=[]
QtBootGen.lean:91  def QtBootGen_Hyp hits=[]         QtBootGen.lean:114 theorem stBoot_roundsg hits=[]
QtBootGen.lean:346 theorem stXiBootgL'_of_round hits=[]   QtBootGen.lean:409 theorem stXiBootRgL'_of_round hits=[]
QtXiRoundLiftGen.lean:364 theorem stXiRoundgL'_of_PTfam hits=[]
QtXiRoundLiftGen.lean:397 theorem stXiRoundQtgL_of hits=['Lloop']     (KLloopOf in hKK, excepted by the ticket)
QtXiRoundLiftGen.lean:466 theorem stOeqQtgL'_of hits=['Lloop']        (same)
band bridges/re-derivations (bandFM_STXiRound', qtBootGen_*_band, QtXiRoundLiftGenCheck.*_band*): hits STFlow/STflowE/lemT/seqP only (allowed)
X1-C4 pinned-name redefinitions: 0     TN-C4: 0     withLam: 0
```

## 3. Compiled nonempty instances (`d = 3`, `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `N_0 = 2^21`; `z0`; window `[s,t] = [0, 1/16]`; `C_d = 1`)
| target | location | data, discharged / left as another gate's pin |
|---|---|---|
| 1 | `QtBootGen:540`; `QtXiRoundLiftGen:678` | `bandFM_STIngR` at `d = 3`. `STXiRoundgL'` evaluated at `(sz0, z0)` with `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`. Left as hypotheses: `STLKgL`, `STStep2ConclgL`, and the pair controls |
| 2 | `QtBootGen:478, 496, 509, 519`; `QtXiRoundLiftGen:716, 723` | `stBoot_roundsg` at `sz0` (`ξ ≡ 1` over `Unit`, `c = C₀ = 1`, `R ≡ 2`). `stXiBootgL'_of_round` at the band carrier with every deterministic premise discharged (`LoopForm`, `norm_mE`, `DecayGen_bandSpec`, `Admissible`, `τ = 1/20`, the flow modulus at `c = 1`, `stKbound_of_flow`, `0 ≤ s < t < 1`, `RangeCond`). At `:723` the round is discharged by `stXiRoundQtgL_band3`. At `:716`, `stXiBootRgL'_of_round 3 STCaseI … (qtBootGen_hyp_band 3) stXiRoundQtgL_band3` gives `STOeqQtgL'` with no hypothesis |
| 3 | `QtXiRoundLiftGen:752, 766, 778` | Family level at `d = 3`, with every premise discharged (per-time pin `stOeqQtRoundPTgL''_band`). Carrier level at `(sz0, z0)`, where only `STXiRoundPTgL''` is left as a hypothesis. Mesh arithmetic at `N = 7`, `n_ = 2`, `c = 1` |
| 4 | `QtXiRoundLiftGen:678, 698` (+ `stOeqQtgL'_band3`, `:628`) | `stOeqQtgL'_of` with every row discharged at the band. Conclusion applied at `(sz0, z0)` with `n_ = 2`, `p = 1`. Left as hypotheses: `STLKgL s`, `STStep2ConclgL`, and the pair controls `≺ 1` |
| 5 | `QtXiRoundLiftGen:742, 746` | `stOeqQt'_holds_of_gen 3` and `stXiRoundQt_holds_of_gen 3` evaluated by `inst_ing` at `(sz0, z0, sInst, tInst)` |

Every deterministic hypothesis is discharged at concrete data: the index sets are nonempty, the window is not collapsed (`0 < 1/16 < 1`), `N_0 = 2^21` is moderate, and no premise is `False`. What stays an example hypothesis is a stochastic pin of other gates (`STLKgL`, `STStep2ConclgL`, the pair controls) or, at carrier level, the round or per-time pin. In both cases the same file also discharges that pin elsewhere (`:716`, `:723`, `:752`).

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Chain.QtBootGen RBM3D.Chain.QtXiRoundLiftGen
⚠ [3923/3934] Replayed RBM3D.Chain.QtBootGen        (warnings: longLine only)
Build completed successfully (3949 jobs).            (grep -c '^error' = 0)
$ lake env lean RBM3D/Chain/QtBootGen.lean; lake env lean RBM3D/Chain/QtXiRoundLiftGen.lean   (fresh elaboration from source)
QtBootGen exit=0 errors=0
QtXiRoundLiftGen exit=0 errors=0
$ lake build        (whole library, #assert_rbm_axioms; run by the auditor in addition to the hub's merge build)
info: RBM3D.lean:622:0: axiom audit: 15231 theorems, 4702 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.STXiRoundgL': 7 [no certificate]
Build completed successfully (4392 jobs).            (grep -c '^error' = 0)
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^ *axiom ' QtBootGen.lean QtXiRoundLiftGen.lean   -> no output (exit 1)
$ wc -l   551 QtBootGen.lean, 788 QtXiRoundLiftGen.lean (both < 2,000)
```
`#print axioms` (in `AuditCheck.lean`): for each of the 16 declarations below, the output is `depends on axioms: [propext, Classical.choice, Quot.sound]`.
- `QtBootGen`: `STXiRoundgL'`, `bandFM_STXiRound'`, `QtBootGen_FlowModFam`, `QtBootGen_Hyp`, `stBoot_roundsg`, `stXiBootgL'_of_round`, `stXiBootRgL'_of_round`, `qtBootGen_flowModFam_band`, `qtBootGen_hyp_band`.
- `QtXiRoundLiftGen`: `stXiRoundgL'_of_PTfam`, `stXiRoundQtgL_of`, `stOeqQtgL'_of`, `stOeqQt'_holds_of_gen`, `QtXiRoundLiftGenCheck.{stOeqQtgL'_band, stXiRoundQtgL_band, stXiRoundQt_holds_of_gen}`.

Name clash: `git grep` on `main`, `t/T2505b`, `t/T2502c` and `t/T2506b` found no declaration of any of the 15 new public names or namespaces outside these two files (0 hits each).

## 5. Paper deltas
The Lean/paper differences row a introduces are all proposed in the prove report's (d):
- `T2505a`: the crude start holds on the Hermitian event `G` of `LemDecCalELipG_FlowMod` and reads `STKboundgL`; the contraction level is `min(2𝔡𝔠, τ)` with `τ` from `RangeCond`, where the band uses `ε/2`.
- `T2505b`: the net mesh `N^{-(6n_+18+2c)}` with the pinned Hölder `c`.
- `T2505c`: the guarded probability premise of the bundle.
- `T2505d`: the carrier-level lift is private.

The conclusions are the merged T2491 pin texts, whose deltas are already recorded at T2491. Using `hFM` in targets 2 and 4 is covered by `T2505a`. No uncovered difference.

## 6. Observations (no RETURN)
- O1. The ticket names target 5 `stOeqQtgL'_band`, but its full name is `RBM.BA.QtXiRoundLiftGenCheck.stOeqQtgL'_band`, following the merged precedent `QEndB1GenCheck.stOeqQtRoundPTgL''_band`. The statement is unaffected. The dispatcher may record the qualified name.
- O2. Target 3's public name `stXiRoundgL'_of_PTfam` has no file-stem prefix. The ticket pins no name for target 3, and it is a target rather than a helper (§3 (E)).
- O3. The ticket lists target-5 instances at `szB`/`zB` and `sz0`. `szB` is the case-(ii) data (`szB_caseII`, row c), so for case (i) the instances at `sz0` are the applicable ones.
- O4. `QtBootGen` also imports `Induction/LemDecCalELip` and `Chain/Step6KitGen`, which are not in the ticket's import list. Both are merged modules, neither is `BA/*` or `Step2Kern`, and (a′) records `Step6KitGen`.
- O5. The report's statement of 1,339 lines against the hi estimate of 1,160 is calibration data only. Neither file reaches 2,000 lines, so no stop rule fired.

## Verdict
| target | statement | vacuity / hidden / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| 1 `STXiRoundgL'` + `bandFM_STXiRound'` | = `T2505_XiRoundgL'` (diff 0, `rfl`) | none | yes | pass / std 3 | n/a | **PASS** |
| 2 `stBoot_roundsg`, `stXiBootgL'_of_round`, `stXiBootRgL'_of_round` | `T2505_XiBootROfRound QtBootGen_Hyp` compiles | `Hyp` discharged at band | yes | pass / std 3 | T2505a, c | **PASS** |
| 3 `stXiRoundgL'_of_PTfam` | per-time pin → `STXiRoundgL'`, rows 2-4, 12, 15, 16 | none | yes | pass / std 3 | T2505b, d | **PASS** |
| 4 `stXiRoundQtgL_of`, `stOeqQtgL'_of` | concludes the merged `STOeqQtgL'`; premises = T2498 + rows 15, 16 | discharged at band | yes | pass / std 3 | covered | **PASS** |
| 5 `stOeqQtgL'_band`, `stOeqQt'_holds_of_gen` | no open hypothesis, `d ≥ 3` / `∀ d` | none | yes | pass / std 3 | n/a | **PASS** |

Overall: **PASS** (row a). This audit needs no dispatcher sign-off.
