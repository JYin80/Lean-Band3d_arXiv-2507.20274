Auditor model: claude-opus-5-5

# T2268 audit (round 1) — S3-16a `Induction/QLevelsA.lean`

Audit time: Tue Oct  6 07:55:45 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2268-audit1`,
detached at `t/T2268` = 5839c77 (base c01b292, an ancestor; `main` now c77e68c).

## 1. Diff scope and hygiene

```
$ git diff --stat main...t/T2268
 RBM3D/Induction/QLevelsA.lean | 687 ++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 687 insertions(+)
$ grep -nE "sorry|admit|^axiom| axiom |native_decide|maxHeartbeats" RBM3D/Induction/QLevelsA.lean; echo "grep exit $?"
grep exit 1
```
Only the sole writable file (new). `RBM3D/Test/Axioms.lean` untouched (none expected). No frozen signature touched
(no existing file modified). Imports: `RBM3D.Induction.QDriftB`, `RBM3D.Induction.B45` (both merged).

Public declarations (script: `grep -nE "^(theorem|def|...)"`): `altB45N_levelM` :376, `startLevelQN` :421,
`crudeLKM_of_level` :462, `QLevelsAInst.altB45N_levelM_instance` :637, `.startLevelQN_instance` :655,
`.crudeLKM_of_level_instance` :670. All other declarations are `private` (`QLevelsA_*` chain, instance helpers).

## 2. Build and axioms

```
$ lake build RBM3D.Induction.QLevelsA
⚠ [3857/3857] Built RBM3D.Induction.QLevelsA (8.9s)
warning: RBM3D/Induction/QLevelsA.lean:10:100: This line exceeds the 100 character limit, please shorten it!
... (10 such longLine warnings, lines 10-23, header before `set_option linter.style.longLine false`; 0 others)
Build completed successfully (3857 jobs).
exit 0
```

Statement script + axioms (`$S/audit_check.lean` = check file's imports + `import RBM3D.Induction.QLevelsA`,
the check file's `namespace T2268Check … end T2268Check` block copied verbatim by `sed`, then):
```
example : T2268_altB45N_levelM := @RBM.Ind.altB45N_levelM
example : T2268_startLevelQN := @RBM.Ind.startLevelQN
example : T2268_crudeLKM_of_level := @RBM.Ind.crudeLKM_of_level
example := RBM.Ind.QLevelsAInst.altB45N_levelM_instance ![true, false, false] rfl (fun _ => 0)
example := RBM.Ind.QLevelsAInst.startLevelQN_instance ![true, false, false] rfl (fun _ => 0)
example := RBM.Ind.QLevelsAInst.crudeLKM_of_level_instance ![true, false, false]
#print axioms … (6 names)
$ lake env lean $S/audit_check.lean; echo "exit $?"
'RBM.Ind.altB45N_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.startLevelQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.crudeLKM_of_level' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.altB45N_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.startLevelQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsAInst.crudeLKM_of_level_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
The three pinned `Prop`s elaborate against the Lean theorems as `@`-terms: the statements are the pins exactly
(hypotheses, binder order, `2 ≤ d`, `m + 1 + 1` indices, `N^τN`, `B^(m+2)`, `η⁻¹`).

Registry pre-check:
```
$ printf 'import RBM3D\nimport RBM3D.Induction.QLevelsA\n#assert_rbm_axioms\n' > $S/registry.lean
$ lake env lean $S/registry.lean > $S/registry.out 2>&1; echo "exit $?"; grep -ciE "error" $S/registry.out
exit 0
0
```

## 3. Per-target review

**Target 1 (private copies `QLevelsA_ward_finM` :134, `QLevelsA_Psum_LK_leM` :161, chain :52-122).** Not pinned
(private, §3 (E)); hypotheses `hE : |E| < 2`, `hu0`, `hu1`, `hH : H.IsHermitian`. Used only inside the file. PASS.

**Target 2 `altB45N_levelM` (:376).** Statement = pin (script above). Compared with merged `B45_det2`
(`B45.lean:2577`): same hypothesis list with `ω : sz.SeqΩ` replaced by `H` + `hH : H.IsHermitian` and
`STLKtensor sz n E u ω` by `sz.STLKM n E u H`; conclusion's second conjunct restated on `altB4N`/`altB5N`
(`QDriftA.lean:59,71`; `ℬ₅ = −(…)`, absorbed by `norm_neg`). Generalisation, not a special case. Hypotheses are
explicit norms/inequalities; no structure field carries a hypothesis; dependencies (`B45_B4_le`, merged B45/QDriftA
names) are merged; no cycle. Only case (i) `N⁻¹ ≤ 1 − u` (as `B45_det`): proposed as `T2268b`. PASS.

**Target 3 `startLevelQN` (:421).** Statement = pin. Proof: `STQop … a = A a − STPsum A (a 0) * ϑ u a` by `rfl`,
`norm_sub_le`, `hYtop`, and the private `QLevelsA_PiM`/`QLevelsA_absorb` (same `𝒫`-bound as target 2, without
`hϑ'`, matching the pin). The paper's `≺` at `3_5:1676-1706` becomes a deterministic per-matrix level: `T2268a`.
PASS.

**Target 4 `crudeLKM_of_level` (:462).** Statement = pin; `pi_norm_le_iff_of_nonneg` with `0 ≤ W^{C₀}`. No hidden
hypotheses (general `k`, `σ`, `Y`, `C₀`). PASS.

## 4. Compiled nonempty instances (same file, :480-683)

Data: merged `sz0`, `d = 3`, `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `m = 1` (3-index tensors),
`E = 0`, `u = 0`, `κ = 1`, `Γ = 2`, `H = 0` (`Matrix.isHermitian_zero`), `ν = 8`, `X = 1`, `ωf = 2`,
`Fv = W^{-36}`, `τN = 2`, explicit `ϑ = QopAlgebra_mollifier 3 L 2 lam` with `Λ = (1+40·6)·6^6 = 11244096`.
- Every deterministic hypothesis is discharged inside the instance theorems: `hNu0`, `hMΛ0`
  (`7·(3·64·2·11244096·64) ≈ 1.93e12 ≤ N^2 ≈ 4.40e12`, `norm_num`), `hFv0'`, `hY0`/`hF0`/`hYtop0` from the merged
  `zero_mem_goodSetN_of_levels` (clauses (G2), (Dec)), `moll_sup`/`moll_deriv` from `QopAlgebra_mollifier_props`.
- Non-vacuity: `hF`'s window is attained (`window0`: label `![0, (2,2,2)]` with `ℓ_0·ωf = 2 ≤ diam_∞`); the
  instances quantify over alternating `σ` and labels `a`, and the audit compiled them at the concrete
  `σ = ![true,false,false]` (`hσ` by `rfl`), `a = fun _ => 0` (§2, exit 0). No `N = 0`, empty index, collapsed
  window, or `False` premise; constants are moderate (`Λ ≈ 1.1e7`, `N ≈ 2.1e6`), not astronomically large.
- Target 4 instance: `k = 3`, `Y = 3B^3 ≤ 24 ≤ 32 = W^1` (`Bctl0 : 0 < B ≤ 2`).
All three instances: PASS.

## 5. Paper deltas

`docs/paper-deltas.md` has no `T2268` entry yet (`grep -n T2268 docs/paper-deltas.md`: no output). The prove report
(d) proposes:
- `T2268a`: start level (`3_5:1676-1690`) and `(y27kasdfg)` per matrix, deterministic, `N^τ` in place of `≺`,
  only `H.IsHermitian` + `hY`/`hF` (covers the Lean/paper difference of targets 2-3).
- `T2268b`: case (i) `N⁻¹ ≤ 1 − u` only (case (ii) `1 − u < g²/L²` not covered).
- `T2268c`: duplication of `B45_det` (cleanup note, not a statement difference).
Every Lean/paper statement difference found is covered. PASS.

## 6. Observations (no verdict effect)

1. 10 `longLine` warnings in the file header (lines 10-23) precede `set_option linter.style.longLine false` (:33).
2. The branch base is c01b292; `main` has advanced to c77e68c (other modules only). The hub's full build at merge
   covers the interaction.
3. Instance theorems are public names in `RBM.Ind.QLevelsAInst` (as in sibling `QDriftBInst`); harmless.

## Verdict

| Target | Statement | Hidden hyp./vacuity/cycle | Instance | Build/axioms | Deltas | Verdict |
|---|---|---|---|---|---|---|
| 1 (private copies) | n/a (unpinned) | none | used by 2-3 | ok | n/a | PASS |
| 2 `altB45N_levelM` | = pin | none | compiled, nondegenerate | ok | T2268a/b | PASS |
| 3 `startLevelQN` | = pin | none | compiled, nondegenerate | ok | T2268a | PASS |
| 4 `crudeLKM_of_level` | = pin | none | compiled, nondegenerate | ok | none needed | PASS |

**T2268: PASS.** No dispatcher sign-off needed.
