Auditor model: claude-opus-5-5

# T2272 audit (round 1) — S3-16b `Induction/QLevelsB.lean`

Written Tue Oct  6 08:55:32 UTC 2026 (`date -u`). Branch `t/T2272` at 4e80637 (merge-base with main c22b80b), audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2272-audit1` (detached at t/T2272, build cache cloned per CLAUDE.md §2).

## 1. Files touched

```
$ git diff --name-only main...t/T2272
RBM3D/Induction/QLevelsB.lean
$ grep -nE "sorry|admit|native_decide|^axiom|maxHeartbeats" RBM3D/Induction/QLevelsB.lean; echo grep-exit=$?
grep-exit=1
```
Only the sole writable file; `RBM3D/Test/Axioms.lean` untouched (none expected). Imports are merged modules only
(`QLevelsA`, `ScaleFacts`, `Step2Core`, `Step2Events`, `AzumaProxyN`). No frozen signature edited (new file only).

## 2. Statements against the pins (script diff + Lean elaboration)

Text diff (whitespace-normalised Prop body of `docs/tickets/checks/T2272-check.lean` vs theorem statement):
```
$ python3 T2272/diff.py
dDriftAltQN def identical: True
goodSetN_LKM_le statement identical: True
goodSetN_LKM_far statement identical: True
qopB13N_levelM statement identical: True
dFlowQN_levelM statement identical: True
alt_hdriftQN statement identical: True
dDriftAltQN_nonneg statement identical: True
```
Lean check: a scratch file `T2272/Pin.lean` importing `RBM3D.Induction.QLevelsB`, containing the check file's six
`T2272_*` Prop texts verbatim (with the vocabulary `dDriftAltQN` resolved to the branch definition), and
`example : T2272_<t> := RBM.Ind.<t>` for each of the six targets:
`$ lake env lean T2272/Pin.lean` -> no error lines, exit=0 (its `#print axioms` output is in section 4).
All six `example`s elaborate: each theorem has exactly the pinned type.

Mathematical reading (ticket Design (a)-(e)): target 3 is `(normQA)` at `m+1` on the block with the
existential `C_n` fixed before `sz` (depends on `d, m, Λg, K, C, c`); target 4 adds the `ℬ₄+ℬ₅` level of
`altB45N_levelM` and the alternating hypothesis `σ (last) = !σ 0`; target 5 fixes `C = (1+40·d(m+1))6^{d(m+1)}`,
`c = 1/2`, so `C_n` depends on `(d, m, Λg, K)` only, and its conclusion
`∀ ω j, j < Kg n → j < τ ω → ∀ b, ‖dGridQN … j ω b‖ ≤ dDriftAltQN … (gridTime … j) …` is the shape of
`GridAssemblyHypN.hdrift` (`GridAssemblyN.lean:208`: `∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω`)
with `K = Kg n`. Target 6 is `hdDrift0` (`:206`) once `|E| < 2`, `u_j < 1` are supplied. Quantifier order: fixed
parameters before `∃ Cn` before `sz, n`, as pinned. No `≺`, no lift, no probability (§64 (4)).

Per-target statement verdict: all six match the pin.

## 3. Hidden hypotheses, vacuity, cycles

- Hypotheses of the public theorems are norms/inequalities, `GoodSetN` membership (merged def, `GridGoodN:124`),
  `STMollifierProps` (merged, `Step34Pins:510`) and the pathwise `hτG`; no new structure, no new `Prop` taken as a
  hypothesis. Proofs only destructure merged clauses (`hH.2.1` = (G2), `hH.2.2.1` = (Dec), `hG.1` = Hermitian,
  `hϑ.2.1`, `hϑ.2.2.2`).
- No cycle: every dependency is a merged name on main (check file `#check`s; imports above).
- Joint satisfiability of all hypotheses of targets 4 and 5 is witnessed by the compiled instances (section 5).
- New public names, 0 hits on main:
```
$ for n in dDriftAltQN goodSetN_LKM_le goodSetN_LKM_far qopB13N_levelM dFlowQN_levelM alt_hdriftQN \
    dDriftAltQN_nonneg QLevelsBInst; do echo "$n: $(git grep -n -w "$n" main -- RBM3D | wc -l)"; done
dDriftAltQN:        0
goodSetN_LKM_le:        0
goodSetN_LKM_far:        0
qopB13N_levelM:        0
dFlowQN_levelM:        0
alt_hdriftQN:        0
dDriftAltQN_nonneg:        0
QLevelsBInst:        0
```
Helpers are `private` (`QLevelsB_*`, and the `QLevelsBInst` numerics).

## 4. Build and axioms (audit worktree)

```
$ lake build RBM3D.Induction.QLevelsB
⚠ [3858/3858] Built RBM3D.Induction.QLevelsB (8.0s)
warning: RBM3D/Induction/QLevelsB.lean:15:100: This line exceeds the 100 character limit, please shorten it!
...  (only longLine / unused-variable warnings; `grep -c "^error"` = 0)
Build completed successfully (3858 jobs).
exit=0
```
```
'RBM.Ind.goodSetN_LKM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.goodSetN_LKM_far' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.qopB13N_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dFlowQN_levelM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.alt_hdriftQN' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.dDriftAltQN_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.goodSetN_LKM_le_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.goodSetN_LKM_far_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.qopB13N_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.dFlowQN_levelM_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.alt_hdriftQN_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Ind.QLevelsBInst.dDriftAltQN_nonneg_instance' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Registry pre-check (`import RBM3D` + `import RBM3D.Induction.QLevelsB` + `#assert_rbm_axioms`, `lake env lean`):
```
 RBM.Univ.UNTrLocalInit,
 RBM.Gauss.Sizes.STOeqNQ'].
non-vacuity certificates: 0 of 159 premises in the two ledgers; ...
reg-exit=0
```

## 5. Compiled nonempty instances (namespace `RBM.Ind.QLevelsBInst`, same file, built above)

Data: `sz0`, `d = 3`, `n = 4` (concrete: `L = 20`, `W = 10^5`, `N = 8·10^18`, `lam = 10^{-6}`; lemmas `W4`, `L4`,
`N4`, `lam4`), `m = 2` (4-index tensors), `K = 2`, `Λg = 1`, `E = 0`, `u = 0`, `κ = 1`, `H = 0 ∈ GoodSetN` at
`(Γ,Λ,Φ) = (4,100,1)` (`zero_mem_goodSetN_of_levels`), `τ' = 1/10`, `ε' = 1/5`, `D' = 40`, `ν = W`, `X = 1`,
`τ_N = 2`, explicit mollifier `QopAlgebra_mollifier 3 L 3 lam` with `QopAlgebra_mollifier_props`.

| target | instance | discharged at concrete data |
|---|---|---|
| 1 | `goodSetN_LKM_le_instance` (`j` with `1 ≤ j < 4`) | membership, `u < 1` |
| 2 | `goodSetN_LKM_far_instance` | membership, `j = 4 ≤ 10`; far window shown attained (`window4`, `diam_∞ = 10 ≥ √10`) |
| 3 | `qopB13N_levelM_instance` (every `σ`, `a`) | `3 ≤ d`, `0 < lam ≤ 1`, `1 < W`, `4 ≤ W^{1/5} = 10`, `L^3 ≤ W^2`, `3W^{1/10} ≤ W^{1/5}`, mollifier props, `0 ≤ u < 1`, membership |
| 4 | `dFlowQN_levelM_instance` (`σ = ![T,F,T,F]`) | all of 3, plus `|0| ≤ 1`, `N⁻¹ ≤ 1`, `ΓΦ = 4 ≤ W`, `(√10)^6 = 1000 ≤ W`, `W ≤ N`, `W^{-40} ≤ W·N^{-8}` (`hFv4`), `9·3·4^6·2·C·W^2 ≤ N^2` (`hMΛ4`), `σalt_last` (by `decide`) |
| 5 | `alt_hdriftQN_instance` (walk `s≡0`, `v≡1/2`, `Kg≡4`, `τ≡1`, `j = 0`, every `ω`, `b`) | all of 4 at `u_0 = 0`, `hτG` via `azumaProxy_pathH_zero_of_s_zero` + `ST_gridTime_zero` + `zero_mem_inst`; `0 < 4`, `0 < 1` |
| 6 | `dDriftAltQN_nonneg_instance` | `|0| < 2`, `0 < 1`, `0 ≤ 4, 1, 1` |

Nondegenerate: `N ≠ 0`, nonempty label types (`Fin 4 → Zd 3 20`), window not collapsed, `j = 0 < Kg = 4`,
`0 < τ = 1`, no `False` premise. Witness sizes are moderate (`N^{τ_N} = N^2 ≈ 6.4·10^37` against
`≈ 8·10^24` on the left of `hMΛ4`; `τ_N = 2` is within the ticket's allowed `1` or `2`). At `H = 0` the entries may
vanish; the ticket accepts this (instances test hypotheses and application), and the prove report says so (lines 70, 192).

## 6. Paper deltas

Prove report (d): `T2272a` (pathwise per-matrix deterministic drift level with losses `W^{C_nε'}`, `N^{τ_N}` in place
of `≺`; sum of three summands) — this is the only Lean/paper difference introduced here (the alternating hypothesis
and the numeric side conditions of target 4 are those of the merged `altB45N_levelM` / `STQopNorm`, covered by their
tickets). `T2272b`: none (no extra side condition). Coverage complete.

## 7. Observations (no verdict effect)

Prove report 203 lines, line 1 `Prover model: claude-sonnet-5-5`; docstring long-line warnings only; concrete `n = 4`
replaces the ticket's optional existential-`n` device (no crude-sup hypothesis needed).

## Verdict

| target | statement | hidden hyp / cycle | instance | build / axioms | deltas | verdict |
|---|---|---|---|---|---|---|
| `dDriftAltQN` (vocab) | verbatim | — | used by 4-6 | ok | — | PASS |
| 1 `goodSetN_LKM_le` | = pin | none | ok | ok | T2272a | PASS |
| 2 `goodSetN_LKM_far` | = pin | none | ok | ok | T2272a | PASS |
| 3 `qopB13N_levelM` | = pin | none | ok | ok | T2272a | PASS |
| 4 `dFlowQN_levelM` | = pin | none | ok | ok | T2272a | PASS |
| 5 `alt_hdriftQN` | = pin; fits `hdrift` | none | ok | ok | T2272a | PASS |
| 6 `dDriftAltQN_nonneg` | = pin; fits `hdDrift0` | none | ok | ok | — | PASS |

**T2272: PASS.** No dispatcher sign-off needed.
