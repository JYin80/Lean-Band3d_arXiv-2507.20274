Auditor model: claude-opus-5-5

# T2259 audit (round 1) — S3-24b `Induction/IterationsB` — Tue Oct  6 06:16:49 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2259-audit1`, detached at `04e4465` (`t/T2259`), merge-base `7672749`.
Statement script: `T2259/stmt.lean` in the scratchpad = `docs/tickets/checks/T2259-check.lean` + `import RBM3D.Induction.IterationsB` + five `example`s.

## 1. Statements against the pins (script)
```
$ lake env lean T2259/stmt.lean      # check file + these lines before `end RBM.Gauss.Sizes.T2259Check`
example : T2259_iterationsB_step := @RBM.Gauss.Sizes.iterationsB_step
example : T2259_stIterations'_holds := @RBM.Gauss.Sizes.stIterations'_holds
example : T2259_stIterationsII'_holds := @RBM.Gauss.Sizes.stIterationsII'_holds
example : T2259_inst_iterations' := @RBM.Gauss.IterationsBInst.inst_iterations'
example : T2259_inst_iterationsII' := @RBM.Gauss.IterationsBInst.inst_iterationsII'
#print axioms RBM.Gauss.Sizes.stIterations'_holds
#print axioms RBM.Gauss.Sizes.stIterationsII'_holds
-- output (tail, error lines: none)
'RBM.Gauss.Sizes.stIterations'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stIterationsII'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
All five pinned statements are matched exactly. The main targets are `∀ d, STIterations' d` and `∀ d, STIterationsII' d` with the merged
pins `STIterR'`/`STIterations'`/`STIterationsII'` (`NQEndFlow.lean:133-152`, unchanged: `git diff --stat main...HEAD -- NQEndFlow IterationsA Step34Pins` is empty).
`STIterR'` keeps the paper's order (`3 ≤ d → ∀ κ ε 𝔡 > 0, ∀ Cd > 0, ∃ 𝔠d ∈ (0,1/100], ∀ 𝔠 sz z, …`), the full index set
`{(r,k): 2≤r≤n-1} ∪ {(r,k-1): 2≤r≤n+2}`, and `n ≥ 2, k ≥ 1` of `lem:iterations` (`3_5:1407-1417`). The general pin is proved, not a special case.

Step against the merged step (24 private names renamed, public names kept):
```
$ diff <(sed -n 1283,1340p IterationsA.lean | perl -pe 's/\biterationsA_(<24 private names>)(?![\w'"'"'])/iterationsB_\1/g') <(sed -n 454,512p IterationsB.lean)
1c1
< theorem iterationsA_step (hsize : Tendsto sz.size atTop atTop)
> theorem iterationsB_step (hsize : Tendsto sz.size atTop atTop)
3c3
<     (hboot : STXiBoot sz E s t)
>     (hboot : STXiBoot' sz E s t)
42,43c42,44
<     have hlow := (hBn ⟨q.1.2, q.2.1.trans q.2.2.1, q.2.2.2⟩).1
<     have hb := hC (A n) (iterationsB_rho E s n q.1.2) (T n) (sz.Bctl n q.1.2) (N + 4)
>     -- R2*: the lower bound of `IterationsAScale.Bctl` at `w = s ∈ [s,t]` (`s ≤ v ≤ u ≤ t` on a pair)
>     have hlow := (hBn ⟨s n, le_rfl, q.2.1.trans (q.2.2.1.trans q.2.2.2)⟩).1
>     have hb := hC (A n) (iterationsB_rho E s n q.1.2) (T n) (sz.Bctl n (s n)) (N + 4)
```
Exactly the two changes the ticket's Design specifies.

Copied private block (target 1):
```
$ diff <(sed -n '876,1046p;1072,1276p' IterationsA.lean | perl <private-only rename>) <(sed -n '67,237p;240,444p' IterationsB.lean) && echo IDENTICAL
private names:       24
IDENTICAL (0 hunks)
```
## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE '^(theorem|lemma|def|abbrev|structure|instance)' IterationsB.lean     # public declarations
454:theorem iterationsB_step   570:theorem stIterations'_holds   581:theorem stIterationsII'_holds
606:theorem inst_iterations'   627:theorem inst_iterationsII'
$ grep -cE '^private (theorem|lemma|def|noncomputable def)' IterationsB.lean
30
$ grep -nE 'sorry|admit|native_decide|^axiom|maxHeartbeats|open private|_private' IterationsB.lean
(no output)
```
- The new file defines no structure or Prop. `IterationsAScale` (merged) is the only structure-typed hypothesis of the step. Both pins discharge it from
  the merged public `iterationsA_scale_I` (`2 ≤ d`, `𝔠d ≤ 1/16`) and `iterationsA_scale_II` (`𝔠d ≤ 1/24`) at `𝔠d = 1/100` (`IterationsB.lean:575-578`, `:586-589`).
- The pin's hypotheses `hrela`/`havg`/`hapri` of the step come from merged lemmas inside `iterationsB_setting` (`:534-553`):
  `v3_premises_of_stFlow`, `tendsto_size`, `stKbound_timeIcc` (reindexed by `StochDomAt.precomp_param`), `iterationsA_rela_of_K`, `iterationsA_avg_of_STAvgU`
  (from `hStep2.2.1`), and `iterationsA_apriori_of_lRB1`. `STXiBoot'` stays the pin's own hypothesis, as pinned.
- Unused pin hypotheses: `STKbound`, `STLK` (both), `STCaseII` (case ii). Unused premises make a statement weaker, not vacuous. The merged pin is unchanged.
- No cycle. Registry pre-check run in the audit worktree after `lake build RBM3D` (`Build completed successfully (4062 jobs).`):
```
$ printf 'import RBM3D\nimport RBM3D.Induction.IterationsB\n#assert_rbm_axioms\n' > registry.lean; lake env lean registry.lean
axiom audit: 7620 theorems, 2557 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Gauss.Sizes.STXiBoot': 4 [no certificate]
  RBM.Gauss.Sizes.STIterR': 0 [no certificate]
premises found by scanning: 153 (borrowed 1, owed 98, structural 37, refuted 6, superseded 11).
registry: 2 borrowed + 158 owed + 98 structural + 7 refuted + 12 superseded; 124 registered premise(s) carry nothing yet
exit 0
```
This matches the prove report's AFTER block: owed 158, found 153, and no unregistered premise. `STIterations'`/`STIterationsII'` are no longer in the owed list.
- External-type hypothesis `STXiBoot'`: this is another gate's pin (S3-18b/S3-22), not an external input. The prove report's (a) Note 3 checks it at the
  instance data: `hlow` at `w = s` gives `(cvA)⁻¹W³ = 0.5 ≤ 1.0139` (case i) and equality `1.1912` (case ii).

## 3. Compiled nonempty instances (all in `IterationsB.lean`, compiled by the build below)
| Endpoint | Instance | Deterministic hypotheses discharged | Left as hypotheses (other gates' pins) |
|---|---|---|---|
| `stIterations'_holds` | `inst_iterations'` `:606` (d=3, szB, zB, κ=ε=𝔡=1/10, 𝔠=1/6, s,t = 7/8,15/16) | `flow_zB`, `0≤s`, `s<t`, `szB_flow_ht`, `szB_regIterI`, `conStInd_const` | STKbound, STLK, STStep1Loop, STStep2Concl, STXiBoot', IH |
| same, STKbound | `example` `:648` | STKbound by `stKbound_of_flow szB (d=3) flow_zB` | STLK, Step1/2, STXiBoot', IH |
| `stIterationsII'_holds` | `inst_iterationsII'` `:627` (s,t = 15/16, 31/32) | as above with `szB_caseII` | as above |
| `iterationsB_step` | `example` `:684` case (ii) (N,k)=(3,2); `:720` case (i) (3,2); `:702` (2,1) | `hS` from public `iterationsA_scale_II/I` at szB (`conStInd_const`, `abs_lemE_lt_two`, `szB_WO`), `hsize`, `2≤N`, `1≤k` | STXiBoot', hrela, havg, hapri, IH1, IH2 |
| consistency | `example` `:739` (generic sz) | `stXiBoot'_of_stXiBoot … hS.t_lt_one` | — |

There are no degenerate cases. `IH1` is nonempty at `(3,2)` (r = 2). `s < t < 1` and `|E| < 2` hold, and the window is not collapsed. The index sets are the actual
`STPair`/`TimeIcc` types of `szB` (`L = 4`, `W_n = n+4`).

## 4. Build and axioms (audit worktree)
```
$ lake build RBM3D.Induction.IterationsB
ℹ [3847/3847] Built RBM3D.Induction.IterationsB (5.3s)
info: RBM3D/Induction/IterationsB.lean:755:0: 'RBM.Gauss.Sizes.iterationsB_step' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:756:0: 'RBM.Gauss.Sizes.stIterations'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:757:0: 'RBM.Gauss.Sizes.stIterationsII'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:758:0: 'RBM.Gauss.IterationsBInst.inst_iterations'' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Induction/IterationsB.lean:759:0: 'RBM.Gauss.IterationsBInst.inst_iterationsII'' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3847 jobs).
$ lake build ... | grep -E 'IterationsB' | grep -E 'warning|error'
(no output)
$ git diff --name-only main...HEAD
RBM3D/Induction/IterationsB.lean
RBM3D/Test/Axioms.lean
```
The registry hunk (`git diff main...HEAD -- RBM3D/Test/Axioms.lean`) removes `STIterations'` and `STIterationsII'` from `owedProps`. It rewrites the `STIterR'` comment to
"…(DECISIONS §80); proved at both regimes by T2259 (`stIterations'_holds`, `stIterationsII'_holds`); no generic proof" and appends
"; hypothesis of `iterationsB_step` (T2259)" to `STXiBoot'`. This is exactly the ticket's registry spec. The prover changed no frozen or merged signature.

## 5. Paper deltas
- R2* (`(am;asoi222)` taken at `B_s` instead of `B_u`) is already in `docs/paper-deltas.md:1522` (D563, T2246a–c).
- The rewrite of the Ψ calculus, `p ≥ 2`, the stronger scale premises and case (ii) are D170–D173 (`paper-deltas.md:689-701`, T2087).
- The new file adds no Lean/paper statement difference beyond these. The unused `STKbound`/`STLK`/`STCaseII` belong to the merged pin's shape and do not change
  the statement proved. Not proposing any new candidate is correct.

## Observations (no effect on verdict)
- O1. The ticket's literal acceptance command `sed 's/iterationsA_/iterationsB_/g'` gives 22 hunks, because public `iterationsA_*` calls are renamed too. The private-only
  rename gives 0 hunks (§1 above). This is a defect of the ticket's command, not of the copy.
- O2. `git merge-tree --write-tree main t/T2259` reports `CONFLICT (content): Merge conflict in RBM3D/Test/Axioms.lean`. Main's T2258 removed the adjacent
  `STOeqNQ''` line (`:124`). The hub must take the union of the two hunks (H23 b): keep main's removal plus T2259's two removals and two comment edits.
- O3. In the instance data, `STConStInd (1/100)` first holds near `W ≈ 1.2·10¹⁰` (preflight Note 1). This is the pin's own eventual-in-`n` hypothesis
  (`𝔠d ≤ 1/100` is forced by the pin). It is discharged for every `𝔠d > 0` by merged `conStInd_const`, with no explicit witness, exactly as merged `inst_iterations`.
  It is not an artificial witness.
- O4. The ticket's instance (3) data `(N,k) = (2,1)` has an empty `IH1`. The prover added nonempty `(3,2)` examples for both cases.

## Verdicts
- Target 1 (copied private block): **PASS**.
- Target 2 `iterationsB_step`: **PASS**.
- Target 3 (private setting facts): **PASS**.
- Target 4 `stIterations'_holds`, `stIterationsII'_holds`: **PASS**.
- Target 5 (instances (1)–(5)): **PASS**.
- Registry edit: **PASS**.

**Overall: PASS.** No dispatcher sign-off needed. Hub note: resolve the `Test/Axioms.lean` merge conflict (O2) by union at merge.
