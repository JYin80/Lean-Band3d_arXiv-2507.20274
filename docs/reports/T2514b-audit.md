Auditor model: claude-opus-5-5

# T2514b audit (row b: B1-B6, `RBM3D/BA/MATrLocalBA.lean`), round 1

Written Thu Oct 15 08:27:54 UTC 2026 (`date -u`). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2514b-audit1`, detached at
`t/T2514b` = c02bf2ab. Row-b diff = `git diff 112ffba2...t/T2514b` (stacked on row a's 112ffba2). Scratch files (uncommitted):
`<scratchpad>/T2514b/pins.lean` (= `docs/tickets/checks/T2514-check.lean` + `import RBM3D.BA.MATrLocalBA` + the examples below).

## 1. Diff, build, axioms, hygiene
```
$ git diff 112ffba2 HEAD --name-only
RBM3D.lean
RBM3D/BA/MATrLocalBA.lean
RBM3D/Test/Axioms.lean
$ lake build RBM3D.BA.MATrLocalBA      (audit worktree; error/sorry lines of the log)
✔ [3900/3900] Built RBM3D.BA.MATrLocalBA (46s)
Build completed successfully (3900 jobs).
exit=0
$ lake env lean <scratch>/pins.lean   (tail)
'RBM.BA.unTrLocalBAAt_of_locAvg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalBARow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalInitBAAt'_of_locAvg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.unTrLocalInitBARow'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0 error-lines=0
$ grep -cE <pattern> RBM3D/BA/MATrLocalBA.lean
C1   'mE\b|\|E\| ≤ 2|SB d|M = m|m • 1|etaT|STFlow|lemT|lemE|msc|locDomain|Mband|sz\.Gn' : 0
X1-C4 '^(private )?(noncomputable )?(def|abbrev|structure) '                          : 0
MN-D3 'ℕ → Prop\)|· = 3'                                                              : 0
F1   'unMLOutBA_three|baMLOutTL_three'                                                : 0
hygiene 'sorry|admit|native_decide|^axiom'                                            : 0
```
Sole writable files of row b: `RBM3D/BA/MATrLocalBA.lean` (new), `RBM3D.lean` (one import line), `RBM3D/Test/Axioms.lean`
(row-b lines). The row-b diff touches exactly these. No merged file other than these two registry/import files is edited; no
frozen signature touched (new file only). Imports: `BA/MAPins`, `BA/MReg`, `Main/BUnivHolds`, `Universality/PinsC2` (all merged).

## 2. Statements against the pins (script)
Appended to the check file and compiled (exit 0 above):
```
example : ∀ d, UNLocAvgBAAt d ↔ T2514_LocAvgAt d := fun _ => Iff.rfl
example : ∀ d, UNTrLocalBAAt d ↔ T2514_TrLocalAt d := fun _ => Iff.rfl
example : ∀ d, UNTrLocalInitBAAt' d ↔ T2514_TrLocalInitAt d := fun _ => Iff.rfl
example : T2514_TrLocalCore := unTrLocalBAAt_of_locAvg
example : T2514_TrLocalInitCore := unTrLocalInitBAAt'_of_locAvg
example : T2514_Rows := ⟨unTrLocalBARow_holds, unTrLocalInitBARow'_holds⟩
example : T2514_ReadIff := ⟨UNLocAvgBA_iff_at, UNTrLocalBARow_iff_at, UNTrLocalInitBARow'_iff_at⟩
```
Target statements as written (`grep -nE '^theorem'`):
```
80:theorem unTrLocalBAAt_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d :=
92:theorem unTrLocalBARow_holds : UNTrLocalBARow :=
237:theorem unTrLocalInitBAAt'_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d :=
448:theorem unTrLocalInitBARow'_holds : UNTrLocalInitBARow' :=
```
- B2, B4 have the MNO-C3 shape `∀ d, 3 ≤ d → (reading at d) → (target at d)` and conclude the per-`d` defs (not their
  unfolding), as F6 requires. B3, B5 conclude the merged heads `UNTrLocalBARow`, `UNTrLocalInitBARow'` with no binder; they are
  one line each from B2/B4 and P6 (`:92-93`, `:448-449`).
- Quantifier order, `κ`, `κ/2` window, `δ`, `ε τ D`, `W^τ Bctl`, `W^τ (Bctl + t*)`, law `UNModelC.ba sz`, `BAm d (L n) (lam n)`:
  definitionally the pins (the `Iff.rfl` lines). No `∃` constant (U5S-C3: the four `∃` hits are two `obtain` in a private proof and
  two event sets of instances). `withLam` appears only in a private lemma and in B4's proof at `sz.withLam (lamHat …)` (UBA-C1).
- B1 is private (`MATrLocalBA_unif`, `:57`), as the ticket specifies.
- The P4-P6 defs read by row b are unchanged on `main` after row a's merge (3a67e18d): `git diff 112ffba2 main -- RBM3D/BA/MAPins.lean`
  adds only one `example` (19 lines, `:256-273`), no def/theorem text changes.

## 3. Hidden hypotheses, vacuity, cycles
- `UNLocAvgBAAt`, `UNTrLocalBAAt`, `UNTrLocalInitBAAt'` are `Prop` defs with explicit binders (no structure fields). Rows B3/B5 are
  conditional on `UNLocAvgBA` only through the merged texts' own `UNLocAvgBA →` binder (P6 `Iff.rfl`); nothing is added.
- B2's hypothesis `∀ᶠ BAbulk κ E` is unused in the proof (as in the pin); harmless (it is in the pin).
- No circular dependency: B2/B4 take `UNLocAvgBAAt d`, concluded on `main` by row a's `unLocAvgBAAt_of_locSCL` / `unLocAvgBAAt_of_ML`
  (`main:RBM3D/BA/MALocal.lean:843, 858`), which do not import row b. No unmerged name read (F1 grep 0).

## 4. Compiled nonempty instances (B6), `MATrLocalBA.lean:457-517`
```
472:example (hL : UNLocAvgBAAt 3) :                    -- B2 conclusion at S0
479:example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, ... -- B2 applied at ε = τ = 1/10, D = 1
487:example (hL : UNLocAvgBA) :                        -- B3
494:example (hL : UNLocAvgBAAt 3) :                    -- B4
501:example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, ... -- B4 applied at τs = 1/2, ε = τ = 1/10, D = 1
511:example (hL : UNLocAvgBA) :                        -- B5
```
Data: `d = 3`, `S0 = clsS 4 _ _` (merged `UNPins:884`; `L = 4`, `W_n` growing), `(𝔠, 𝔡) = (1/6, 1/10)` discharged by `S0_adm`
(`UNPins:887`), `κ = clsκ 4 _` with `clsκ_pos`, `E = (fp 4 _).E` with `S0_bulk` (`UNPins:891`), `δ = (π κ)^3/8 > 0` (`MATrLocalBA_hδ`),
window hypothesis discharged by merged `BAbulk_window` (`MReg:122`) in `MATrLocalBA_hwin`; numeric side conditions by `norm_num`.
Nondegenerate (no `N = 0`, positive window, nonempty bulk). The only binders are `UNLocAvgBAAt 3` / `UNLocAvgBA`, other gates' pins
(row a A8/A7) that were not on the branch base; allowed by CLAUDE.md §4 step 2. All six compile (module build above).

## 5. Registry and full-library check
`git diff -U0 112ffba2 HEAD -- RBM3D/Test/Axioms.lean`: deletes the owed lines `UNTrLocalBARow`, `UNTrLocalInitBARow'`; replaces
the owner texts of `UNTrLocal`, `UNTrLocalInit'`:
```
BA instance: `UNTrLocalBARow`, proved by `unTrLocalBARow_holds` (T2514b, `BA/MATrLocalBA.lea…
BA instance: `UNTrLocalInitBARow'`, proved by `unTrLocalInitBARow'_holds` (T2514b, `BA/MATrLocal…
```
As the prove report states (b4), the branch alone fails `#assert_rbm_axioms` (unregistered premise `UNLocAvgBAAt`), because row a's
A6 is not on its base. Simulation of the hub's merge onto current `main` (89947ef7, row a merged), in a scratch detached worktree (removed after the run)
`/Users/junyin/Lean_proof/RBM3D-wt/T2514b-audit1-merge`: `MATrLocalBA.lean` copied from `t/T2514b`, the row-b Axioms diff applied
(`git apply -3`: "Applied patch to 'RBM3D/Test/Axioms.lean' cleanly."), `import RBM3D.BA.MATrLocalBA` added after the last import:
```
$ lake build
info: RBM3D.lean:651:0: axiom audit: 15469 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 125 (borrowed 1, owed 52, structural 52, refuted 6, superseded 14).
registry: 2 borrowed + 117 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry nothing yet: [...]
Build completed successfully (4421 jobs).
exit=0
```
`UNTrLocalBARow`, `UNTrLocalInitBARow'` do not appear in the scan's uncertified list; 0 new unregistered premises.

## 6. Paper deltas
Row b introduces no new Lean statement: B3/B5 conclude merged texts (`UNPins:169-186`); B2/B4 and P4-P5 are their per-`d` cut
(`Iff.rfl`). The tolerance `W^τ (Bctl + t*)` of `UNTrLocalInit'` is covered by D532 (T2213); the explicit form and law
`seqP (sz.withLam 0)` by D689 (a). The prove report proposes no candidate (d); the route differences (scaling identity instead of a
coupling-Lipschitz bound, bulk at `λ̂` at level `κ/16`) are proof-internal. Coverage complete.

## 7. Observations (no verdict effect)
- O1 (merge mechanics): `git diff --stat main...t/T2514b` also lists `RBM3D/BA/MAPins.lean` (+260; merge-base b2326aac, because
  row a was merged by file copy, not by git merge). The hub must bring in only the three row-b files (CLAUDE.md §3 (A) 3), and
  `RBM3D.lean` is a union with row a's import lines (a cherry-pick of f3c524a2 onto `main` conflicts there; the line-based apply in §5
  is clean). §5 shows the result builds.
- O2: on `main`, `UNLocAvgBAAt 3` is now derivable (`unLocAvgBAAt_of_ML 3 le_rfl unMLOutBA_three`, `MALocal:858`,
  `MainIndTermBA:47`); the instances could drop the binder after the rebase. Not required: the binder was another gate's pin at the
  branch base.
- O3: imports differ from the ticket's list (`Universality/PinsC2` instead of `BA/CouplingWindow`; the merged coupling window is not
  used, per the 1b route). No statement effect.
- O4: file size 521 lines, under the 800 stop line.

## Verdicts
| target | verdict |
|---|---|
| B1 `MATrLocalBA_unif` (private) | PASS |
| B2 `unTrLocalBAAt_of_locAvg` | PASS |
| B3 `unTrLocalBARow_holds` | PASS |
| B4 `unTrLocalInitBAAt'_of_locAvg` | PASS |
| B5 `unTrLocalInitBARow'_holds` | PASS |
| B6 instances | PASS |

Overall: **PASS**. No dispatcher sign-off needed. Merge note: bring in the row-b files only (O1).
