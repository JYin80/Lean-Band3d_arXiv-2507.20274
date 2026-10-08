Auditor model: claude-opus-5-5

# T2332 audit (round 1) — LW engine, `RBM3D/Graph/LWEngine.lean` — Thu Oct  8 13:59:13 UTC 2026

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2332-audit1`, detached at `t/T2332` = `bd9d092` (merge-base with `main`: `5b6221f`).
Scratch: `$SP/T2332/aud/` (`eq.py`, `ax.lean`, `chk.lean`).

## 1. Statement (script diff against the ticket's pin)

```
$ python3 -I eq.py     (whitespace-normalized block equality; check = docs/tickets/checks/T2332-check.lean)
lwEvX equal: True
LWLocRegConcl equal: True
lw_localregularX vs pin equal: True
merged lw_localregular conclusion == LWLocRegConcl body: True
MERGED HEAD: theorem lw_localregular (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) :
```
The fourth line compares `LWLocRegConcl`'s body with the text of merged `lw_localregular` (`LocalRegular6d.lean`) after `∃ outs errs : List (PGraph (Fin 2)),`, so the six conjuncts really are the merged ones, word for word.

```
$ lake env lean chk.lean   (check imports + import RBM3D.Graph.LWEngine + the check's section 2 +
                            example : RBM.Graph.T2332Check.T2332_lw_localregularX := RBM.Graph.lw_localregularX)
chk_exit=0
```
Quantifier order: `∀ p c, 0 < c → ∀ K0 d D, ∃ outsX errsX, ∀ m, m ≠ 0 → …`. `m` now comes after `∃` (the point of the ticket); the cutoff
`lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters` does not depend on `m`. The only hypotheses are `0 < c` and the binder `m ≠ 0`. Nothing is weakened compared with the merged
`lw_localregular`: every conjunct is the merged one, with `nWS ≥ p` added.

## 2. Vacuity, hidden hypotheses, cycles

- The target uses no structure. `LocStepX` is an inductive `Prop` used only inside the proof. Its constructor hypotheses (`hp hx hv hwf hbad hnb hy hp1 hq1`) are
  copied from `LocStep` and mention no `m` and no `coeff` (`sed -n '/^inductive LocStepX/,…'` read in the audit). The target does not take `LocStepX` as an argument.
  The proof builds it from `lvl1_exists_step 1` (`lwEngine_exists_stepX`).
- Proof path (read): `lw_localregularX` uses `lwEngine_exists` (well-founded recursion on `Lvl1Mu K` through `lvl1Lt_wf`, the shape of `lvl1_exists_aux`, no fuel), then `lwEngine_assemble`
  (merged `lvl1_induction`, `lvl1_step_good`, `lvl1_size_le`, `pathInv2_locStep`, `locReg6Inv_locStep`, `locReg6_of_locCostGe`), then `lw_nWS_ge`. Every dependency
  is a merged declaration on `main` or a declaration in this file. Nothing depends on T2297 or LW-13b, so there is no cycle.
- No external hypothesis is added, so no limit check is owed.

## 3. Compiled nonempty instance (namespace `RBM.Graph.LWEngineInst`)

`lwEngine_inst_localregularX` (`LWEngine.lean:893`) applies `lw_localregularX 2 (1/4) (by norm_num) 1 3 10`. That is `p = 2`, `c = 1/4`, `K0 = 1`, `d = 3`, `D = 10`.
It evaluates the **same** tagged pair `outsX errsX` at `m = Complex.I` and at `m = (1+I)/2`, and discharges `m ≠ 0` both times (`Complex.I_ne_zero`, and `re` of `(1+I)/2 = 0` gives a contradiction). At `m = i` it also discharges the following:
- conjunct 2, at `W = 27`, `L = 3`, `Ψ = 27^{-1/4}`, with `L^3 ≤ W^1` and `W^{-3/2} ≤ Ψ ≤ W^{-1/4}` both proved;
- conjunct 4, the expectation identity, at the merged concrete data `lwWxInstSz`, `lwWxInstSp`, `lwWxInstM`, `z = zt 0 (1/2)`, `u = 1/2`. Every premise is discharged: `gaussIBP`,
  `lwWx_inst_im`, `lwWx_flow`, `lwWx_inst_hSp`, `lwSymm_inst_hSpT`, `lwWx_inst_hM`, `lwSymm_inst_hM0`;
- conjuncts 1, 5 and `nWS ≥ 2`.

At `m = (1+i)/2` it states the whole conclusion. The data hypotheses of conjunct 4 stay inside `LWLocRegConcl` because they are part of the pinned conclusion, not premises of the target.
None of these is degenerate: `p = 2`, the index set is not empty, and the window has positive width. The other instances, `lwEngine_inst_stepX`, `lwEngine_inst_two_m`, `lwEngine_inst_stepX_edge_gg`
(all three rules, each at two `m`), `lwEngine_inst_nWS_ge`, `lwEngine_inst_step1_identity` and `lwEngine_inst_lwEvX` (tag `(3,1)`, giving `-1` at `i` and `i/4` at `(1+i)/2`), all compile
(build in §4).

## 4. Build, axioms, hygiene, scope

```
$ lake build RBM3D.Graph.LWEngine 2>&1 | grep -E "error|warning: .*LWEngine|sorry|Build completed"
Build completed successfully (3887 jobs).
exit=0

$ lake env lean ax.lean | sed 's/RBM.Graph.//'
'lwEvX' depends on axioms: [propext, Classical.choice, Quot.sound]
'LWLocRegConcl' depends on axioms: [propext, Classical.choice, Quot.sound]
'lw_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'lw_nWS_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'lvl1WeightOuts0_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'lvl1EdgeOuts0_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'lvl1GGOuts0_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_localregularX' depends on axioms: [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_stepX_edge_gg' depends on axioms: [propext, Classical.choice, Quot.sound]
'LWEngineInst.lwEngine_inst_step1_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0

$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom|^\s*axiom " RBM3D/Graph/LWEngine.lean | wc -l
       0
$ grep -n "^import" RBM3D/Graph/LWEngine.lean
6:import RBM3D.Graph.LocalRegular6d
7:import RBM3D.Graph.LWExpTerm5
$ git diff --stat main...t/T2332
 RBM3D/Graph/LWEngine.lean | 937 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 937 insertions(+)
$ grep -rln "lwEvX\|LWLocRegConcl\|lw_localregularX\|LWEngineInst" --include='*.lean' RBM3D | grep -v "^RBM3D/Probe"   (main worktree)
(no output)
```
The diff touches only the sole writable file. The imports are exactly the ones the ticket lists. No merged file or frozen signature changes. The file has 937 lines, under the 1500-line stop rule.

## 5. Paper deltas

- The `m`-free tagged lists, with each graph's coefficient multiplied by `m^j m̄^{j'}` (against the paper's "polynomial in `m, m̄, m^{-1}, …`", `7_8_light_weight.tex:144`), are covered by
  candidate **T2332a** in the prove report, (d) 5.
- The extra conjunct `nWS ≥ p` is covered by candidate **T2332b**, (d) 6.
- The other conjuncts are the merged `lw_localregular` text verbatim (§1), so they need no new delta.

## 6. Observations (no effect on the verdict)

- O1. The pin requires the binder `m ≠ 0`, but the proof does not use it. It is harmless, because conjunct 4 carries its own `m ≠ 0`.
- O2. Public helpers beyond the ticket's list (`lvl1PackX`, `LocStepX.eval`, `LocStepX.eval_one`) are listed in the prove report, (d) 3, for the dispatcher. All other helpers carry the
  file-stem prefix `lwEngine_`.
- O3. The instance of conjunct 4 at the second `m` is not discharged at concrete data. Merged concrete data exist only for `m = mE 0 = i`. The pin does not require it.

## Verdict

| target | verdict |
|---|---|
| `lwEvX` | PASS |
| `LWLocRegConcl` | PASS |
| `lw_localregularX` | PASS |

Ticket T2332: **PASS**. No dispatcher sign-off needed.
