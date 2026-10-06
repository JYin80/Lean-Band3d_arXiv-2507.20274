Auditor model: claude-opus-5-5
# T2229 audit, round 1 (S6-12a, `Induction/ExpWardII`): Tue Oct  6 00:26:07 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2229-audit1`, detached at `e259f2e` (t/T2229; merge-base with main `dc2d99b`, main now `b750bf3`).

## 1. Diff scope (sole writable files)
```
$ git diff --stat main...t/T2229
 RBM3D/Induction/ExpWardII.lean | 517 +++++
 RBM3D/Test/Axioms.lean         |   1 -
$ git diff main...t/T2229 -- RBM3D/Test/Axioms.lean   (the one hunk)
@@ -232,7 +232,6 @@ def owedProps : List Name :=
-   `RBM.Gauss.Sizes.STExpWardII, -- `6:137-141` Ward term, regime (ii): S6-12; S6-01 (T2204, DECISIONS §67: owed)
$ git diff main...t/T2229 -- RBM3D/Induction/Step6Pins.lean RBM3D/Induction/Step6Kit.lean RBM3D/Induction/WardII.lean | wc -l
0
$ git merge-tree --write-tree main t/T2229 ; echo $?
0
```
`STExpIntII` line and structural `STExpWardIIConcl` stay; merged pin text unchanged. `$S` = `<scratchpad>/T2229/`.

## 2. Build, hygiene, axioms
```
$ lake build RBM3D.Induction.ExpWardII          (audit worktree)
✔ [3859/3859] Built RBM3D.Induction.ExpWardII (3.9s)
Build completed successfully (3859 jobs).        exit 0 ; grep -c '^error' = 0
$ lake env lean RBM3D/Induction/ExpWardII.lean   (forced recompile)
exit 0, no output
$ git diff main...t/T2229 -- RBM3D/Induction/ExpWardII.lean | grep -E '^\+.*\b(sorry|admit|native_decide)\b|^\+axiom' | wc -l
0
$ grep -nE '^(private )?def ' RBM3D/Induction/ExpWardII.lean | wc -l      -> 0 (no new public Prop)
```
`#print axioms` (in `$S/T2229AuditCheck.lean`, below), verbatim:
```
'RBM.Gauss.Sizes.expWII_slot0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWII_slot1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWII_two_slot_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWII_inv_Neta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.expWII_det_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.STExpWardIIConcl_of_avgU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stExpWardII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWardII_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_skeleton6II_Wd' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_inv_Neta_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_slot0' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_slot1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_det_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Step6Inst.inst_expWII_two_slot_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pin (script, compiled)
`$S/T2229AuditCheck.lean` = imports of `docs/tickets/checks/T2229-check.lean` + `import RBM3D.Induction.ExpWardII` + its
sections 1-2 verbatim (awk-extracted) + one `example : T2229Check.X := @RBM.Gauss.Sizes.X` per section-2 `def`
(7) + `example (d : ℕ) : STExpWardII d := stExpWardII_holds d` + each section-3 statement (awk-extracted) as
`example : <stmt> := @RBM.Gauss.Step6Inst.<inst>` (5) + the 15 `#print axioms` above.
```
$ grep -c '^example' $S/T2229AuditCheck.lean
13
$ lake env lean $S/T2229AuditCheck.lean ; echo exit $?
exit 0          (grep -c error $S/check.out = 0)
```
Section-3 examples as generated (excerpt):
```
example :
  LWtermEXP 3 → STExpIntII 3 →
    InstIng6Concl (fun sz E s t => STStep6Concl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
  := @RBM.Gauss.Step6Inst.inst_skeleton6II_Wd
example :
  STExpAvgU szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
    STExpWardIIConcl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32)
  := @RBM.Gauss.Step6Inst.inst_expWII_concl
```
Against the paper (`6:137-141`): the pin's conclusion `STExpWardIIConcl` (`Step6Pins.lean:368`) is
`‖f_u − Q^{({1,2})}f_u‖ ≺ (Bctl n u)^3`, uniformly over `u ∈ TimeIcc s t`, `σ 0 ≠ σ 1`, all `a`, `Bctl = W^{-d}B_{u,0}`;
paper: second term `≤ (W^{-d}B_{t,0})^2 (Nη_t)^{-1} ≤ (W^{-d}B_{t,0})^3`, `σ₁ ≠ σ₂`. Same quantity, same exponent 3,
same index ranges; premise `STExpAvgU` = `(res_ELK_n=1)` uniform in `u` (exponent 2). The proved theorem is the
general pin `STExpWardII d` for every `d` (not a special case; `3 ≤ d` is a binder of `STIngR6` and is unused).

## 4. Hidden hypotheses, vacuity, cycles
- No structure/class introduced; no `def` in the file. `stExpWardII_holds` takes `𝔠_d = 1/100` and uses
  `hflow.1.2.2.1` (`SizeTendsto`), `st6_flowE_le`, `hs0`, `hst`, `st5_t_lt_one`, premise `STExpAvgU`
  (file `:419-424`); the other `STIngR6` binders are unused (regime not needed: paper-delta `T2229a`).
- `STExpWardIIConcl_of_avgU` (`:364`): hypotheses `SizeTendsto`, `0 < κ`, `|E n| ≤ 2-κ`, `0 ≤ s n`, `s n ≤ t n`
  (unused `_hst`, pinned), `t n < 1`, `STExpAvgU`; all satisfiable together (instance `inst_expWII_concl`).
- Conclusion is not vacuous: `TimeIcc s t n` is nonempty for `s ≤ t`, `{σ // σ 0 ≠ σ 1}` contains `![true,false]`,
  and `Prec` is via `st6_prec_det_iff` an eventual pointwise bound `≤ N^τ B^3` for every `τ > 0`.
- No external hypothesis added. Imports are merged modules only (`Step6Kit`, `WardII`, `ExpAvg`, `ExpEtermsA`,
  `ExpDuhamel`, `Loop.KLUnique`, `Path.Walk`); no import of `RBM3D`; no cycle (module builds standalone).
- Name clash (`git grep -l <name> main -- RBM3D RBM3D.lean | wc -l`): 0 for each of `expWII_slot0`, `expWII_slot1`,
  `expWII_two_slot_bound`, `expWII_inv_Neta_le`, `expWII_det_bound`, `STExpWardIIConcl_of_avgU`, `stExpWardII_holds`,
  `inst_expWardII_holds`, `inst_skeleton6II_Wd`, `inst_expWII_`. Unpinned helpers are `private expWII_*` (`:52-165`).

## 5. Compiled nonempty instances (same file, `RBM.Gauss.Step6Inst`, `:439-513`)
| target | instance | data | open hypotheses |
|---|---|---|---|
| 7b `stExpWardII_holds` | `inst_expWardII_holds`, `inst_skeleton6II_Wd` | `szB` (L=4, W_n=n+4, λ=1), `zB`, (15/16, 31/32), regime `szB_reg5II` via merged `inst_ing6_II` | stochastic `STIngR6` premises + `STExpAvgU` inside `InstIng6Concl`; `LWtermEXP 3`, `STExpIntII 3` (other gates' pins) |
| 7a `STExpWardIIConcl_of_avgU` | `inst_expWII_concl` | `szB`, `zB`, κ=1/10, s=15/16, t=31/32 | `STExpAvgU` only; `0 ≤ 15/16`, `15/16 ≤ 31/32`, `31/32 < 1` by `norm_num` |
| 5 `expWII_inv_Neta_le` | `inst_expWII_inv_Neta_le` | n=0, E=0, u=15/16 | none |
| 2, 3 slots | `inst_expWII_slot0`, `inst_expWII_slot1` | n=0, E=0, u=15/16, σ=(+,-), a=(0,0) | none (`decide` for σ0≠σ1) |
| 6 `expWII_det_bound` | `inst_expWII_det_bound` | same, M = η⁻¹+1 (proved from `norm_Lloop_le`, `norm_mSigma`) | none |
| 4 two slots | `inst_expWII_two_slot_bound` | d=3, L=4, T ≡ 1, M=1 | none |
None degenerate (`N = 4096`, nonempty index sets, `u < 1`, nontrivial σ). All compile (section 2).

## 6. Registry pre-check (§20 (2))
Root build without the root import fails as the ticket predicts (hub adds `import RBM3D.Induction.ExpWardII` at merge):
```
$ lake build RBM3D        (audit worktree, no root import)
error: RBM3D.lean:273:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of ...
  [RBM.Gauss.Sizes.STExpWardII]
✔ [4030/4033] Built RBM3D.Test.Axioms (3.1s)
```
With the root imports + the new module (`$S/precheck2.lean` = `grep '^import' RBM3D.lean` + `import RBM3D.Induction.ExpWardII` + `#assert_rbm_axioms`):
```
$ lake env lean $S/precheck2.lean ; echo exit $?
axiom audit: 6718 theorems, 2268 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
premises found by scanning: 123 (borrowed 1, owed 89, structural 27, refuted 6).
registry: 2 borrowed + 140 owed + 84 structural + 7 refuted; 110 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
exit 0
$ grep -c 'STExpWardII[],]' $S/precheck2.out                    -> 0
$ git show dc2d99b:RBM3D/Test/Axioms.lean | grep -c 'Sizes.STExpWardII,'   -> 1
$ grep -c 'Sizes.STExpWardII,' RBM3D/Test/Axioms.lean          -> 0
```
Owed 140 = base 141 − 1 (base figure from the prove report `:185`, consistent with the one deleted line).

## 7. Paper deltas
Lean/paper differences and coverage (prove report (d)):
- the regime is not used, `(N(1-t))⁻¹ ≤ W^{-d}B_{t,0}` in every regime, `(Im m)⁻¹` bulk constant: `T2229a`;
- decomposition as two one-slot Ward identities with constant 3 instead of the closed form with `N^{-1}tr G̃`: `T2229b`.
The form of `STExpWardIIConcl` itself (uniform `u`, `≺`) is the merged S6-01 pin, not introduced here. Coverage complete.

## 8. Verdict
| target | verdict |
|---|---|
| 1 bridges (private) | PASS |
| 2 `expWII_slot0` | PASS |
| 3 `expWII_slot1` | PASS |
| 4 `expWII_two_slot_bound` | PASS |
| 5 `expWII_inv_Neta_le` | PASS |
| 6 `expWII_det_bound` | PASS |
| 7a `STExpWardIIConcl_of_avgU` | PASS |
| 7b `stExpWardII_holds` | PASS |
| 8 instances (5 required + 3 extra) | PASS |
| registry (`Axioms.lean`, one line) | PASS |

**T2229: PASS.** No dispatcher sign-off needed.
Observations (no verdict effect): (1) forced `lake env lean` recompile also exits 0. (2) The hub must add the root import together with the merge; without it `#assert_rbm_axioms` fails (§6).
(3) Main moved to `b750bf3` (T2228 merged its `Axioms.lean` deletions); `git merge-tree` against current main is clean.
