Auditor model: claude-opus-5-5

# T2282 audit (UN-51g, `RBM3D/Universality/OUInterfaceK.lean`), round 1 — Tue Oct  6 11:01:45 UTC 2026

Branch `t/T2282` at 6c0bf96, merge-base = main b39ac53. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2282-audit1` (detached).
Scratch: `<scratchpad>/T2282/{A,B,ax,root}.lean`.

## 0. Files touched
```
$ git diff --stat main...t/T2282
 RBM3D/Test/Axioms.lean               |   9 +-
 RBM3D/Universality/OUInterfaceK.lean | 488 +++++++++++++++++++++++++++++++++++
$ git diff main...t/T2282 -- RBM3D/Test/Axioms.lean   (summary of the 9 changed lines)
- `RBM.Univ.UNOULL  - `RBM.Univ.UNG1Row  - `RBM.Univ.UNG2bRow  - `RBM.Univ.UNOUDiagk  - `RBM.Univ.UNOURowk
+ `RBM.Univ.UNOULLk + `RBM.Univ.UNG1Rowk + `RBM.Univ.UNG2bRowk + `RBM.Univ.UNOUProfRowk   (each with a T2282 comment)
$ owedProps entry count: main 272, t/T2282 271   (−5 + 4 = −1, as the ticket's Registry)
```
Only the two sole writable files; no merged file or frozen signature touched; `UNKind` unchanged.

## 1. Statement vs pin (script diffs)
Pins/vocabulary: check file sections 2–3 vs target file sections 2–3 (between the `## 2. Vocabulary` header and the next section header, header comments stripped):
```
$ diff <(awk '/## 2. Vocabulary/,/## 4. Target/' check | grep -v '^/-!') <(awk '/## 2. Vocabulary/,/## 4. Generic assembly/' target | grep -v '^/-!')
diff exit 0          (75 lines, byte-identical: UNOUProfile, UNOUProfile.band, UNOUProfRowk, UNOULLk, UNOUEq747k, UNG1Rowk, UNG2bRowk)
```
Theorem statements, whitespace-normalised text of check `T2282_<name>` body vs target `theorem <name> :` type:
```
ouDiagk_of_ouLLk IDENTICAL
unOUProfRowk_band IDENTICAL
UNOULLk_band IDENTICAL
UNOUEq747k_band IDENTICAL
UNG1Rowk_band IDENTICAL
unG2bRow_of_k IDENTICAL
ouRow_of_pinsk_band IDENTICAL
```
(`ouRowk_of_pins` has named binders `(K) (P) {ML Loc Que} (hprof : …)`; checked by elaboration below.)

Check (A): check file with sections 2–3 deleted, `import RBM3D.Universality.OUInterfaceK` added, plus
`example : RBM.Univ.T2282Check.T2282_<name> := @RBM.Univ.<name>` for all 8 theorems of targets 3–4:
```
$ lake env lean A.lean | grep error ; exit 0      (14 examples: 6 of check §5 + 8 added)
```
Check (B): full check file + target import + `rfl` transports:
```
example : @RBM.Univ.UNOULLk = @RBM.Univ.T2282Check.UNOULLk := rfl
example … : RBM.Univ.UNOUProfRowk K P = RBM.Univ.T2282Check.UNOUProfRowk K ⟨P.pm, P.pp⟩ := rfl
example … : RBM.Univ.UNOUEq747k K P sz 𝔡 τU = RBM.Univ.T2282Check.UNOUEq747k K ⟨P.pm, P.pp⟩ sz 𝔡 τU := rfl
example … : RBM.Univ.UNG1Rowk K P ML Loc Que = …T2282Check.UNG1Rowk K (fun d => ⟨(P d).pm, (P d).pp⟩) ML Loc Que := rfl
example … : RBM.Univ.UNG2bRowk K P = …T2282Check.UNG2bRowk K (fun d => ⟨(P d).pm, (P d).pp⟩) := rfl
example (d) : (RBM.Univ.UNOUProfile.band d).pm = (RBM.Univ.T2282Check.UNOUProfile.band d).pm := rfl   (and .pp)
$ lake env lean B.lean | grep error ; exit 0
```
Mathematics vs ticket: `UNOUProfRowk` has `∃ C` after `𝔡 κ` and before `sz n` (§29 (6)), `0 < z.im ≤ 1`, `0 ≤ ζ ≤ 1`,
`0 < lam ≤ 𝔡⁻¹`, bound `C lam⁻² W^{-d}` for both profiles (design (b)); `UNOULLk`/`UNOUEq747k` carry the bulk
condition inside `∀ᶠ n` (design (d)), scale `ouEtaLL`/`ouEtaQ`, error `qdBoundExp sz n τ η_Q` (design (c), O3);
`UNG1Rowk` keeps `τU ≤ ouTauMax 𝔠 𝔡` (design (f)); `UNG2bRowk` has no `τU` bound and the premise `UNOUProfRowk` (design (e), O2).
All as pinned. No special case passes for a general target: the generic theorems are stated for free `K`, `P`.

## 2. Vacuity / hidden hypotheses / cycles
- `UNOUProfile K`: two data fields `pm pp`, no Prop field. No structure hides a hypothesis.
- Imports: `RBM3D.Universality.ZeroModeProfile`, `RBM3D.Universality.PinsK` only (no `Main.*`, no `BA.*`, no `RBM3D`): no cycle; both merged.
- `ouDiagk_of_ouLLk`: proof by the copied filter lemma on `T n = {0 ≤ t ≤ ouTStar}` (nonemptiness witnessed by `(0,0)`), Markov, union bound — the bulk predicate stays inside the predicate, as design (d) requires. No `κ > 2` case needed.
- Band bridges are genuine proofs (padding lemma `OUInterfaceK_pad`, both directions), not definitional tricks; `unOUProfRowk_band` is `profTilde_rowDiff` (merged).
- External hypotheses: none new; the owed premises (`UNOULLk`, `UNG1Rowk`, `UNG2bRowk`, `UNOUProfRowk`) are registered owed pins of other gates.

## 3. Compiled nonempty instances (namespace `RBM.Univ.OUInterfaceKInst`, `d = 3`, `sz0`)
| endpoint | instance | deterministic hypotheses |
|---|---|---|
| `unOUProfRowk_band` | `inst_profRow_band : UNOUProfRowk (UNKind.band 3) (UNOUProfile.band 3)` | `3 ≤ 3` by `le_rfl`; no premise left |
| `ouDiagk_of_ouLLk` | `inst_ouDiagk_band : UNOULLk (band 3) sz0 (1/1000) → UNOUDiagk (band 3) sz0 (1/1000)` | none; `UNOULLk` = UN-51 pin |
| `UNOULLk_band` | `inst_ouLLk_band` at `sz0`, `1/1000` | none |
| `UNOUEq747k_band` | `inst_Eq747k_band` at `sz0`, `𝔡 = 1/10`, `τU = 1/1000` | none |
| `UNG1Rowk_band` | closed `↔` (no parameters); used by `inst_g1k_band`, which applies `UNG1Rowk` at `d=3`, `𝔠=1/6`, `𝔡=1/10`, `sz0_admissible`, `0 < 1/1000`, `1/1000 ≤ ouTauMax (1/6) (1/10) = 1/720` (`norm_num`) | all discharged |
| `unG2bRow_of_k` | `inst_g2b_of_k (r2 : UNG2bRowk band…) : UNG2bRow` | none; `r2` = UN-52 pin |
| `ouRowk_of_pins` | `inst_ouRowk_band r1 r2 : UNOURowk (fun d => UNKind.band d) …` with `hprof := unOUProfRowk_band` discharged | `hprof` discharged; `r1`, `r2` other gates' pins |
| `ouRow_of_pinsk_band` | `inst_ouRow_band r1 r2 : UNOURow` | as above |
`sz0` is the merged admissible size sequence (`SizesInst.sz0`, `L ≥ 3`, `W > 0`): no `N = 0`, no empty index, no `False` premise.

## 4. Build, axioms, hygiene
```
$ lake build RBM3D.Universality.OUInterfaceK 2>&1 | grep -E "error|OUInterfaceK|Build completed"
⚠ [3739/3739] Replayed RBM3D.Universality.OUInterfaceK
warning: RBM3D/Universality/OUInterfaceK.lean:15:100: This line exceeds the 100 character limit, please shorten it!
  (… same linter warning at :16, :19, :20, :22)
Build completed successfully (3739 jobs).
$ lake env lean ax.lean     (#print axioms of every theorem in the file)
ouDiagk_of_ouLLk: [propext, Classical.choice, Quot.sound]
ouRowk_of_pins: [propext, Classical.choice, Quot.sound]
unOUProfRowk_band: [propext, Classical.choice, Quot.sound]
UNOULLk_band: [propext, Classical.choice, Quot.sound]
UNOUEq747k_band: [propext, Classical.choice, Quot.sound]
UNG1Rowk_band: [propext, Classical.choice, Quot.sound]
unG2bRow_of_k: [propext, Classical.choice, Quot.sound]
ouRow_of_pinsk_band: [propext, Classical.choice, Quot.sound]
OUInterfaceK_UNOULL_of_k: [propext, Classical.choice, Quot.sound]
OUInterfaceK_UNG1Row_of_k: [propext, Classical.choice, Quot.sound]
OUInterfaceKInst.inst_profRow_band / inst_ouDiagk_band / inst_ouLLk_band / inst_Eq747k_band /
  inst_g1k_band / inst_g2b_of_k / inst_ouRowk_band / inst_ouRow_band: [propext, Classical.choice, Quot.sound]  (8 lines, verbatim each)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Universality/OUInterfaceK.lean ; exit 1 (no hits)
```
Registry pre-check (root as the hub will merge it: `RBM3D.lean` with `import RBM3D.Universality.OUInterfaceK` inserted after the last `import` line, run as a scratch copy):
```
$ lake env lean root.lean
axiom audit: 8206 theorems, 2668 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: …
root-with-import exit 0
```
Without the root import (branch as is), `lake build RBM3D` fails, as expected:
```
error: RBM3D.lean:326:0: axiom audit: 5 premise(s) that no theorem of this development proves are in none of …
  [RBM.Univ.UNOUDiagk, RBM.Univ.UNG1Row, RBM.Univ.UNOURowk, RBM.Univ.UNG2bRow, RBM.Univ.UNOULL]
```
— i.e. the 5 deletions are discharged exactly by the new file's theorems (`ouDiagk_of_ouLLk`, `OUInterfaceK_UNG1Row_of_k`,
`ouRowk_of_pins`, `unG2bRow_of_k`, `OUInterfaceK_UNOULL_of_k`). Merge note for the hub: the root import and the
`Axioms.lean` change must land in the same commit (ticket: "Root import: added by the hub at merge").

Name clash (`git grep -lw <name> main -- RBM3D RBM3D.lean`): 0 files for each of the 17 new public names
(UNOUProfile, UNOUProfRowk, UNOULLk, UNOUEq747k, UNG1Rowk, UNG2bRowk, ouDiagk_of_ouLLk, ouRowk_of_pins,
unOUProfRowk_band, UNOULLk_band, UNOUEq747k_band, UNG1Rowk_band, unG2bRow_of_k, ouRow_of_pinsk_band,
OUInterfaceKInst, OUInterfaceK_UNOULL_of_k, OUInterfaceK_UNG1Row_of_k).

## 5. Paper deltas
Prove report §(d): T2282a (generic interface design: profile, row-difference shape, η_Q / qdBoundExp, bulk inside `∀ᶠ`),
T2282b (`UNG2bRowk` without `τ_U` bound), T2282c (registry mechanics: `↔` does not discharge a registered premise; two
extra one-direction theorems). Every Lean/ticket difference (design (a)–(f)) is covered by T2282a/b; no paper statement
is changed beyond T2162b/T2276a (ticket). Coverage complete.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. Two unpinned theorems `OUInterfaceK_UNOULL_of_k`, `OUInterfaceK_UNG1Row_of_k` are public (file-stem prefixed, allowed by
  CLAUDE.md §3 (E)); the ticket's interface rule says helpers `private`. They are needed for the registry scan (T2282c);
  dispatcher may note it.
- O2. Five long-line linter warnings in the module docstring (`:15–:22`).
- O3. Prove report line 1 is `Prover model: claude-sonnet-5-5` (role `prover`), consistent with §3 (D).
- O4. `UNG2bRowk` is claimed true for every `(K, P)`; that is UN-52's obligation (owed pin), not checked here.

## Verdict
| target | verdict |
|---|---|
| 1 `UNOUProfile`, `UNOUProfile.band` | PASS |
| 2 pins `UNOUProfRowk`, `UNOULLk`, `UNOUEq747k`, `UNG1Rowk`, `UNG2bRowk` | PASS |
| 3 `ouDiagk_of_ouLLk`, `ouRowk_of_pins` | PASS |
| 4.1–4.6 band bridges | PASS |
| 5 instances | PASS |

**T2282: PASS.** No dispatcher sign-off needed.
