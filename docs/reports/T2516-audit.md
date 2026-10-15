Auditor model: claude-opus-5-5

# T2516 audit (round 1) — M/N M2, `BA/MAQDiff`

Written Thu Oct 15 09:01:19 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2516-audit1`, detached at `t/T2516` 7c80bd9a (parent `main` 3a67e18d).
Scratch (uncommitted, outside the repo): `scratchpad/T2516/audit_pins.lean` = `docs/tickets/checks/T2516-check.lean` + `import RBM3D.BA.MAQDiff` + the examples below.

## 1. Diff scope
```
$ git diff --name-only main...t/T2516
RBM3D.lean
RBM3D/BA/MAQDiff.lean
$ git diff main...t/T2516 -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.MAQDiff
```
Both are sole writable files (new `MAQDiff`; one import line, after the last `import`, before `#assert_rbm_axioms`). No merged file edited, so no frozen signature changed. `Test/Axioms.lean` untouched (ticket Decision (6)).

## 2. Statements against the pins (script)
```
$ cd T2516-audit1 && lake env lean <scratch>/audit_pins.lean > pins.out 2>&1; echo exit=$?; grep -c error pins.out
exit=0
0
```
Examples elaborated in that file (all accepted):
```
example : ∀ {d} (sz : Sizes d) κ ε n z, BAendDom sz κ ε n z ↔ T2516_EndDom sz κ ε n z := fun _ _ _ _ _ => Iff.rfl
example : ∀ {d} (sz : Sizes d) τ n z ω σ, BAqdBadz sz τ n z ω σ ↔ T2516_QdBadz sz τ n z ω σ := fun _ _ _ _ _ _ => Iff.rfl
example : ∀ d, BAEnd_QDiffL d ↔ T2516_EndQDiff d := fun _ => Iff.rfl
example : ∀ d, BAQDiffFixed d ↔ T2516_QDiffFixed d := fun _ => Iff.rfl
example : ∀ d, BAMANetQD d ↔ T2516_NetQD d := fun _ => Iff.rfl
example : T2516_Trace := @baTrace2
example : T2516_Profile := @baProfile_eq
example : T2516_ProfLip := baProf_lip
example : T2516_FixedOfML := baQDiffFixed_of_ML
example : T2516_NetQDAll := baMANetQD
example : T2516_EndOfML := baEnd_QDiffL
example : T2516_EndThree := baEnd_QDiffL_three
example : ∀ d, BAMAFixed d := baMAFixed_holds
example : (∀ d, UNMLOutBA d → BAQDiffFixed d) = T2516_FixedOfML := rfl
example : (∀ d, BAMANetQD d) = T2516_NetQDAll := rfl
example : BAEnd_QDiffL 3 = T2516_EndThree := rfl
```
The MN1 texts used are the merged `BA/MAPins` names and are `Iff.rfl` to the check's inlined T2514 pins; the eight public targets inhabit the `T2516_*` pins exactly (no weakened/strengthened variant, no extra binder). Quantifier order of target 6: `∀ κ, 0 < κ → ∃ C, 0 < C ∧ ∀ d sz n η z w, …` — constant before `d` and `sz`, as pinned (U5S-C3). `baProfile_eq` carries `0 < sz.lam n`, as pinned. Per-`d` forms only; `d > 3` only through `UNMLOutBA d` (Jun decision B, §316), as pinned.

Ticket hypothesis-rule greps (in the audit worktree):
```
$ awk '/^theorem /{p=1} p{print} /:= by|:=$/{p=0}' MAQDiff.lean | grep -cE 'mE\b|\|E\| ≤ 2|SB d|M = m|m • 1|etaT|STFlow|lemT|lemE|msc|locDomain|Mband|sz\.Gn|ThetaP[MP]|profP[MP]|KLK_two|Theta d'
0
$ grep -cE '^(noncomputable )?(def|abbrev|structure) ' MAQDiff.lean
0
$ git grep -nE 'def (BAEnd_QDiffL|BAQDiffFixed|BAMANetQD|BAMAFixed|BAprof|BAqdBadz|BAendDom|BAGz)\b' -- RBM3D | grep -v MAPins.lean   (no output, exit 1)
$ grep -cE 'ℕ → Prop\)|· = 3' MAQDiff.lean
0
$ grep -n withLam MAQDiff.lean | grep -vc 'seqP (\(sz\|S0\).withLam 0)'
0
$ grep -nE '\b(sorry|admit|axiom|native_decide)\b' MAQDiff.lean   (no output, exit 1)
```

## 3. Vacuity, hidden hypotheses, cycles
- Public declarations: 8 theorems (lines 107, 208, 432, 768, 965, 1012, 1016, 1019); every helper is `private` with stem `MAQDiff_`; no public def/structure, so no hypothesis sits in a new structure field.
- Only non-deterministic premise of targets 5, 9: `UNMLOutBA d` (merged def `BA/UNPins:110`); at `d = 3` it is discharged by the merged theorem `unMLOutBA_three` (`#check` above: `RBM.BA.unMLOutBA_three : RBM.Univ.UNMLOutBA 3`), so `baEnd_QDiffL_three` has no premise. Target 8 (`BAMANetQD d = BAQDiffFixed d → BAEnd_QDiffL d`) is the pinned implication shape.
- Dependencies are merged (`main` 3a67e18d: `BA/MAPins`, `BA/MALocal`, `MainIndTermBA`, `KInduct`, …); `MAQDiff` imports nothing unmerged; no cycle (it is a leaf: nothing imports it besides `RBM3D.lean`).
- `open private` reaches merged privates only (`Main/ZTransfer`, `BA/ConArg`, `BA/MALocal`, `Main/ZNet`; lines 83-84, 421, 860-861); none is restated.
- No external hypothesis is introduced.

## 4. Compiled nonempty instances (`section Inst`, MAQDiff.lean:1029-1094; compiled in the module build of §5)
| target | data | hypotheses discharged |
|---|---|---|
| 1 `baTrace2`, 2 `baProfile_eq` | `S0` (`d = 3`, `(L,g) = (4,3/10)`), `n = 0`, `z_n = E_* + i/2`, both `σ`, arbitrary `ω, a, b` | `0 < Im z` by `norm_num`; `0 < S0.lam 0` by `(fp 4 _).g0_pos` |
| 6 `baProf_lip` | `κ = clsκ 4 _` (`clsκ_pos`), `n = 0`, `η = 1/4`, `z = E_* + i/2`, `w = E_* + i/4` (`z ≠ w`), both `σ` | all five order hypotheses by `norm_num`; both bulk hypotheses by merged `cls_bulk 4` (`BA/UNPins:863`) |
| 5 `baQDiffFixed_of_ML` | `d = 3` at `unMLOutBA_three`; `(𝔠,𝔡) = (1/6,1/10)`, `S0_adm`, `(κ,ε,τ,D) = (clsκ,1/20,1/10,2)` | `3 ≤ 3`, positivities; plus end domain nonempty at every `n` (`inst_locAvg_domain`, `BA/UNPins:990`) |
| 8 `baMANetQD` | same data, fed with target 5 at `d = 3` | same; end domain nonempty |
| 9 `baEnd_QDiffL_three`, `baEnd_QDiffL`, `baMAFixed_holds` | same data; `_three` unconditional; the other two under `hML : UNMLOutBA 3` (an MN1/V pin, inhabited by `unMLOutBA_three`) | all deterministic ones |
No `N = 0`, empty index, collapsed window (`η = 1/4 ≤ Im z, Im w ≤ 1`, `ε = 1/20`), `False` premise or astronomically large witness: the instances quantify over all `n` via `∀ᶠ`/concrete `n = 0`, at the merged admissible class sequence.

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.BA.MAQDiff ; grep -c '^error' build.log ; grep -c 'MAQDiff.lean' build.log
✔ [4358/4358] Built RBM3D.BA.MAQDiff (15s)
Build completed successfully (4358 jobs).
0
0
$ #print axioms (in audit_pins.lean)
'RBM.BA.baTrace2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProfile_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baQDiffFixed_of_ML' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProf_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMANetQD' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_QDiffL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEnd_QDiffL_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baMAFixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake build   (full library, audit worktree; extra to the brief) ; grep -c '^error' full.log
info: RBM3D.lean:651:0: axiom audit: 15473 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 127 (borrowed 1, owed 54, structural 52, refuted 6, superseded 14).
Build completed successfully (4421 jobs).
0
```
Registry: scan count 127 equals the prover's pasted `before` line (parent 3a67e18d); 0 new, 0 removed, as the ticket expects.

## 6. Paper deltas
- `T2516a` (prove report (d)): the `z`-Lipschitz bound `baProf_lip` of the BA profile (`C = 12 κ'⁻²(1+κ'⁻²)`, `κ' = (πκ)^5/2048`), which the paper leaves inside the omitted "net and perturbation argument" (`1_2_Intro_model_result.tex:1228`). Proposed; covers the one new statement.
- The endpoint shapes (explicit `W^τ`, `N^{-D}`, law `seqP (sz.withLam 0)`, ρ-bulk) are the MN1 pins already covered by D689 (T2449a–c, `docs/paper-deltas.md:1653`).
- `baTrace2`, `baProfile_eq` are the paper's flow-transfer identities at BA (`(eq:diffu1,2)` route) with the pinned loop orientation `(b,a)`; no statement difference beyond D689. Coverage complete.

## 7. Verdict per target
| target | verdict |
|---|---|
| 1 `baTrace2` | PASS |
| 2 `baProfile_eq` | PASS |
| 3, 4 private comparisons, `MAQDiff_det_of_precL` | PASS (private, not endpoints) |
| 5 `baQDiffFixed_of_ML` | PASS |
| 6 `baProf_lip` | PASS |
| 7 private cover lemma | PASS (private) |
| 8 `baMANetQD` | PASS |
| 9 `baEnd_QDiffL`, `baEnd_QDiffL_three`, `baMAFixed_holds` | PASS |
| 10 instances | PASS |

**Ticket verdict: PASS.** No dispatcher sign-off needed.

## 8. Observations (no RETURN)
- O1: the ticket's grep "`grep -n unMLOutBA_three` = target 9 and its instance only" also hits the instances of targets 5 and 8 (MAQDiff.lean:1066, 1076); those are instances, not statements, and the prove report lists them. No statement impact.
- O2: ticket F1 calls `BA/MAPins`, `BA/MALocal` unmerged; they are on `main` 3a67e18d (the 1b started after the T2514 row a merge, Decision (1) satisfied).
- O3: ticket row 8 (Θ transfer) is inline as private `MAQDiff_Mss_smul`/`MAQDiff_Theta_smul` (MAQDiff.lean:192, 199), since T2515 row a is not on `main` (Decision (3)).
- O4: (a′) records the cover's `N`-threshold as `C ≤ N` with the opaque `∃ C`; it is internal to the `∀ᶠ` proof and changes no statement.
