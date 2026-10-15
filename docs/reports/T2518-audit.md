Auditor model: claude-opus-5-5

# T2518 audit (round 1): M3 `BA/MADecolQUE`, decol and QUE at block Anderson, per-`d` `UNQueBA` bridge

Written 2026-10-15 09:41 UTC (`date -u`). Branch `t/T2518` = d621c193, merge-base = `main` = 13b68cea. Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2518-audit1` (detached at d621c193). Scratch files: scratchpad `T2518/audit.lean`, `T2518/theta.lean` (not committed).

## 1. Diff scope (sole writable files)

```
$ git diff --stat main...t/T2518
 RBM3D.lean               |   1 +
 RBM3D/BA/MADecolQUE.lean | 532 +++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean   |   5 +-
```
`RBM3D.lean`: `+import RBM3D.BA.MADecolQUE` after the last import (before `#assert_rbm_axioms`). `Test/Axioms.lean`: the `owedProps`
header comment gets "`BAEnd_QUEL` left this list (T2518: `baEnd_QUEL_three`, `BA/MADecolQUE`)"; the line `RBM.BA.BAEnd_QUEL` is deleted;
the `UNQuek` owner text is replaced with the ticket's wording. These are exactly the ticket's three registry edits (located by name). No merged file other than these is touched,
and no frozen signature is changed. `MADecolQUE` has 532 lines, under the 900 stop line. The spare `MAQUEBA` is not used.

## 2. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.MADecolQUE 2>&1 | grep -A2 MADecolQUE ; ... | tail -1
⚠ [4361/4361] Replayed RBM3D.BA.MADecolQUE
warning: RBM3D/BA/MADecolQUE.lean:12:0: The module doc-string for a file should be the first command after the imports.
Build completed successfully (4361 jobs).
$ grep -nE 'sorry|admit|native_decide|^\s*axiom ' RBM3D/BA/MADecolQUE.lean | wc -l
       0
$ lake env lean $SCRATCH/audit.lean     (#print axioms part)
'RBM.BA.baEnd_decolL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_QUEL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unQueBAAt_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMADecol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMAQUE' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baQueFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMz_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unQueBAAt_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_decolL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_QUEL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.UNQueBA_iff_at' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The only warning is a style linter warning (doc-string placement). The registry scan comes from the prove report's full build: before, `owed 52`; after, `owed 51`; 0 new premises.
The hub's full `lake build` at merge re-checks it.

## 3. Statements against the pins (script)

The scratch file `audit.lean` contains `import RBM3D.BA.MADecolQUE`, then Part 2 of `docs/tickets/checks/T2518-check.lean` copied verbatim by `awk`,
then the lines below. `MADecolQUE_rowDiff` is reached by `open private ... from RBM3D.BA.MADecolQUE`.
```
example : ∀ d, UNQueBAAt d ↔ T2518_UNQueBAAt d := fun _ => Iff.rfl
example : T2518_QueIffAt := UNQueBA_iff_at
example : T2518_MzDiag := fun sz n z hz x => baMz_diag sz n z hz x
example : T2518_MADecolAll := baMADecol
example : T2518_DecolOfML := baEnd_decolL
example : T2518_DecolThree := baEnd_decolL_three
example : T2518_RowDiff := MADecolQUE_rowDiff
example : T2518_QueFixed := fun sz n ε₀ c E ε K z => baQueFixed sz n ε₀ c E ε K z
example : T2518_MAQUEAll := baMAQUE
example : T2518_QUEOfML := baEnd_QUEL
example : T2518_QUEThree := baEnd_QUEL_three
example : T2518_QueCore := unQueBAAt_of_QUEL
example : T2518_QueAtOfML := unQueBAAt_of_ML
example : T2518_QueAtThree := unQueBAAt_three
example : T2518_QueBridge := fun h => UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QUEL d hd (h d)
$ lake env lean $SCRATCH/audit.lean ; echo exit $?   → no error lines; exit 0
```
All 15 pins match their targets definitionally. The pins are binding, and they were compiled at release.

`baThetaDiff` (C3 input, on `main`) against `T2515_ThetaDiffBA` (text copied verbatim from `T2515-check.lean:162-169`):
```
example : T2515_ThetaDiffBA := baThetaDiff
$ lake env lean $SCRATCH/theta.lean ; echo exit $?   → exit 0
```
MN1 pin texts read by name (`BA/MAPins.lean`): `BAMADecol d := BAEnd_locSCL d → BAEnd_decolL d` (:161) and
`BAMAQUE d := BAEnd_QDiffL d → BAEnd_QUEL d` (:164). `BAEnd_decolL` (:121-123) and `BAEnd_QUEL` (`UNPins:333-336`) keep the paper's order:
`3 ≤ d`, `(𝔠, 𝔡)`, `sz.Admissible`, `κ`, the exponents, then `∀ᶠ n`. The law is `seqP (sz.withLam 0)`, the matrix is `seqHBA`, and the domain is the ρ-bulk `BAbulk`.
Target 2 (private decol core) matches the ticket's mathematics. Hypothesis `¬ ∃ z, BAendDom κ ε n z ∧ BAlocBad1z τL n z ω`, the two scalar bounds
`W^{τL}·𝓑(N^{-1+ε},0) ≤ 1` and `2N^{-1+ε} ≤ N^{-1+τ}`, and `ε ≤ 1` give `¬ BAdecolBad κ τ n ω`, via `z = μ_k + iη` and `decol_spectral_core` with `Im M_xx ≤ 1`.
Target 6 (`MADecolQUE_que2Bad_sub`, lines 187-258, private) is generic in `Ω` and `Hm`. It is used only through `baQueFixed`, whose pin matches.

## 4. Hidden hypotheses, vacuity, cycles (ticket greps)

```
C1  grep msc|locDomain|...|m • 1          → 2 hits, :67 and :184, both inside doc-strings (band-twin citations); 0 in statements
X1-C4 grep '^(def|abbrev|structure) '     → 52:def UNQueBAAt (d : ℕ) : Prop :=        (only public def)
      grep 'def (BAEnd_decolL|...|BAMz)\b' outside MAPins/UNPins → 0
Θ   grep 'Θ|PropThetaQ'                    → 0
MN-D3 grep 'ℕ → Prop\)|· = 3'              → 0
UBA grep withLam (not 'seqP (sz|S0.withLam 0)') → 0  (16 hits, all the law)
```
- There are no structure fields. `UNQueBAAt` is a plain `Prop` def, equal to `UNQuek` at `UNKind.ba d` by `Iff.rfl`.
- Dependencies are merged results on `main` 13b68cea: `baEnd_locSCL(_three)` (M1 a), `baEnd_QDiffL(_three)` (T2516), `baThetaDiff` (T2515 a),
  `QUEFlow_*`, `queCore_quad_blk` (via `open private`), `queChain`, `queDomain`, `decol_scalars`, `decol_spectral_core`. None of them imports `MADecolQUE`, so there is no cycle.
- No external hypothesis is added. The `d > 3` forms enter only through `UNMLOutBA d` (Jun decision B, §316), as the pins state.
- Name-clash grep, `(theorem|lemma|def) <name>\b` on `main`, `t/T2515b` and `t/T2517`, for all 11 new public names: 0 hits each.

## 5. Compiled nonempty instances (file `:386-528`, compiled in the module build)

The data is `d = 3`, class sequence `S0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `S0_adm`, `κ = clsκ 4 (3/10) > 0`.
| target | instance | hypotheses |
|---|---|---|
| 1 `baMz_diag` | `sz0`, n=0, z=i, x=0; and `S0`, n=1, z=E_*+i/2 | `0 < Im z` by `simp`/`norm_num` |
| 3 `baMADecol` | `BAMADecol 3` at the merged step chain `baMANetLoc ∘ baLocSCFixed_of_ML ∘ unMLOutBA_three`, (τ,D)=(1/10,1) | all discharged |
| 4 `baEnd_decolL(_three)` | `S0`, (τ,D)=(1/10,1); `_ML` form at `unMLOutBA_three` | all discharged |
| 5b/5c (private) | ∃ n with `E_* + iη_Q ∈ BAendDom` (via `S0_bulk`); row bound with C>0 at n=0 | all discharged |
| 6/7 `baQueFixed` | ∃ n, ε = qdBoundExp, K = Cλ⁻²W⁻³, from `baEnd_QDiffL_three` and `baThetaDiff` at `S0` | all discharged, `0 < η_Q` proved |
| 8 `baMAQUE`, `baEnd_QUEL(_three)` | (ε₀,c,τ)=(1/30,1/60,1/300); `baMAQUE 3` at the step chain `baMANetQD ∘ baQDiffFixed_of_ML` | 6 sign/order hyps by `norm_num` |
| 8 non-vacuity | `queBound W (1/10)(1/30)(1/60)(1/300) < 1` for every `W > 1` | proved |
| 9 `unQueBAAt_three`, `_of_ML`, `_of_QUEL` | same data | all discharged |
| 9 bridge | `∀ d, BAEnd_QUEL d → UNQueBA` (one line) and its `d = 3` read at `S0` | `∀ d` premise is the `d > 3` open pin (§316) |
Order checks: ε₀ = 1/30 < 𝔡/2 = 1/20, c = 1/60 < ε₀, c = 1/60 < 𝔡/5 = 1/50, τ > 0. No instance uses `N = 0`, an empty index set, a collapsed window or a `False` premise.
The bound in the target-8 instance is `< 1` for every `W > 1`, so the instance does not depend on an astronomically large witness. The proof's eventual threshold sits inside `∀ᶠ` and is not part of the instance.

## 6. Paper deltas

- The public endpoint texts are the merged MN1 pins (`BAEnd_decolL`, `BAEnd_QUEL`). Their Lean/paper differences (explicit form, law `seqP (sz.withLam 0)`, ρ-bulk)
  are already in `docs/paper-deltas.md:1653` as **D689 (T2449a–c)**.
- `UNQueBAAt` is a per-`d` cut of the merged `UNQuek`/`UNQueBA` (`Iff.rfl`). It introduces no new mathematics against the paper.
- `baMz_diag` (`M_xx = m`, `Im M_xx ≤ 1`) agrees with `(eq:ukx)`, `1_2:397-401`.
- `baQueFixed` is an internal fixed-`n` Markov step, the twin of the band `queFixed`.
- The prove report (d) proposes no candidate and gives these reasons. I agree; there is no uncovered statement difference.

## 7. Observations (no effect on verdict)

- O1: There is a module doc-string linter warning at `MADecolQUE.lean:12`; the build still passes.
- O2: The prove report records that the registry lines moved: `BAEnd_QUEL` is at `:180` and `UNQuek` at `:385` on 13b68cea, not the ticket's `:183` and `:388`. The lines were located by name, as the ticket allows.
- O3: Line 1 of the prove report reads `Prover model: claude-sonnet-5-5`. This matches the `prover-hard` role.

## Verdict per target

| target | verdict |
|---|---|
| P `UNQueBAAt`, `UNQueBA_iff_at` | PASS |
| 1 `baMz_diag` | PASS |
| 2 decol core (private) | PASS |
| 3 `baMADecol` | PASS |
| 4 `baEnd_decolL`, `baEnd_decolL_three` | PASS |
| 5 measurability / domain / row differences (private) | PASS |
| 6 generic `que2Bad_sub` (private) | PASS |
| 7 `baQueFixed` | PASS |
| 8 `baMAQUE`, `baEnd_QUEL`, `baEnd_QUEL_three` | PASS |
| 9 `unQueBAAt_of_QUEL`, `_of_ML`, `_three`, bridge | PASS |
| 10 instances | PASS |
| registry / `RBM3D.lean` | PASS (full build at merge by the hub) |

**Overall: PASS.** No dispatcher sign-off needed.
