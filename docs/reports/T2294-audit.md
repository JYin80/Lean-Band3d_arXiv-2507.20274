Auditor model: claude-opus-5-5

# T2294 (S3-18a1, `Induction/QEndA.lean`) — audit round 1

Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2294-audit1`, detached at `t/T2294` = `15d3389`; `main` = `90ce008`;
`date -u`: Tue Oct  6 13:53:31 UTC 2026. Scratch scripts in the scratchpad's `T2294/` folder.

**Verdict: PASS (all targets).** No dispatcher sign-off needed to merge. Observations O4/O5 are for the S3-18a2 draft.

## 1. Scope, build, axioms, hygiene
```
$ git diff --name-only main...t/T2294 ; wc -l RBM3D/Induction/QEndA.lean
RBM3D/Induction/QEndA.lean                       # the only sole writable file touched; Test/Axioms.lean, RBM3D.lean untouched
    1967
$ lake build RBM3D.Induction.QEndA
ℹ [3864/3864] Built RBM3D.Induction.QEndA (8.9s)
Build completed successfully (3864 jobs).       EXIT 0 ; lines "^error": 0 ; warning lines in QEndA.lean: 0
$ grep "depends on axioms" build.log | grep QEndA | sed 's/.*axioms: //' | sort | uniq -c
  36 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|maxHeartbeats|^axiom|^\s*axiom " QEndA.lean | wc -l
       0
$ registry pre-check: import RBM3D + import RBM3D.Induction.QEndA + #assert_rbm_axioms (lake env lean)
axiom audit: 8601 theorems, 2817 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 153 (borrowed 1, owed 94, structural 41, refuted 6, superseded 11).   exit 0
$ name clash: grep -rnw --include=*.lean <name> on main's RBM3D/ and RBM3D.lean, 36 public names of QEndA.lean
names with hits on main: 0
```
Imports: `QBudgetB`, `QGridB`, `GridEnvelopeN`, `NQGood2`, `GridAssemblyN` (all merged; none of `RBM3D`, `NQEndLin`,
`NQEndFlow*`, `QtNonzero*`). Instance helpers come from merged check namespaces (`GridDriftNCheck`, `GridEnvelopeNCheck`,
`QGridBCheck`). No circular dependency (new file, imports only merged modules).

## 2. Pinned statements (script diff + compile against the check file)
```
$ python3 pin.py   # comments stripped, whitespace collapsed; check file §2 vs QEndA.lean
altYSetN IDENTICAL
altExitTauN IDENTICAL
altYGridN vs pin IDENTICAL
$ lake env lean stmt.lean   # check-file imports + import QEndA + check-file namespace RBM.Ind.T2294Check verbatim, then:
#   example : RBM.Ind.T2294Check.T2294_altYGridN := @RBM.Ind.altYGridN
#   example : @RBM.Ind.T2294Check.altYSetN = @RBM.Ind.altYSetN := rfl
#   example : @RBM.Ind.T2294Check.altExitTauN = @RBM.Ind.altExitTauN := rfl
exit 0
```
`altYGridN`: hypotheses `0 ≤ s`, `s ≤ v`, `v < 1`, `K ≠ 0`, `1 ≤ X`, `Prec(STXiLK … l ≺ X)` on `TimeIcc s v n`, then
`∀ C` (`K+1 ≤ N^C` eventually), `∀ ε > 0` → `HighProbAt` of the grid event at level `N^ε X`. Quantifier order as pinned.
`Prec` is at length `l` only (no current-length control; §62 (2), §95 (3)). External input = the owed `STLKU`-type gate;
the report gives a limit check at `u = 0` (`STXiLK = 1`); acceptable as the ticket keeps `Prec` a hypothesis.

## 3. Free targets: statement vs ticket mathematics (signatures read in QEndA.lean)
| target | line | check against ticket / merged consumer | verdict |
|---|---|---|---|
| `measurableAltYSetN`, `mem_of_lt_altExitTauN`, `altExitMeasN` | 90, 100, 110 | three memberships; `MeasurableSet[filt sz j] {j < τ}` | PASS |
| C1a `gridDriftQN_envelope` | 247 | eventually, a.e., `∀ j < K n`, `∀ a`: `‖rGridQN … (mollifier m+1) σ j ω a‖ ≤ qErrQN … (m+1) C₁ C₂ (N^{τK} η_{u_{j+1}}^{-(m+2)}) j`, `C₁ = (1+40d(m+1))6^{d(m+1)}`, `C₂ = 1000(1+d(m+1))²`; premise `STKbound E` explicit | PASS |
| C1b `assembledRHSAltQN_qErr_le` | 350 | LHS = `AssembledN` RHS (`GridAssemblyN.lean:249-255`) at `m = K n`, `κ = kappaAltQN`, `εK = epsAltQN`, `c = cQVAltQN`, `dDrift = dd j`, `δD` const, `stepErr = qErrQN`, sup term `Xs ≤ X0`; RHS literally `assembledRHSAltQN … + N^{-D_t}`; `hsum` has the shape of `sum_weighted_qErrQN_le` (`QGridB.lean:565`) at `m ↦ m+1` (weight exponent `m+2`, envelope `η^{-(m+2)}`) | PASS |
| C2 `hQ_altQN`, `subGaussStop_altQN` | 442, 580 | `∀ M ∈ GoodSetN(u_j, m+2, …)`, Hermitian: `Δ·((m+2)·qvFormQN(u_{j+1}, u_p)(M)) ≤ cQVAltQN … D'' p a j`; `SubGaussStopN` at `τ = altExitTauN` with proxy `cQVAltQN`. Shift premise `≤ W^{-(D''+1)}`, `2 ≤ W`, `hMee` added (T2294c) | PASS |
| C3 `alt_hkerGridQN` | 632 | conclusion = `hker` field (`GridAssemblyN.lean:203`) at `u = gridTime`, `Cls = altClsQN … ε' Dc`, `κ = kappaAltQN`, `εK = epsAltQN`; regime premises `v ≤ 1-g²/L²`, `W⁻¹ ≤ (1-v)/(1-s)` explicit | PASS |
| C4 `alt_hdriftGridQN`, `alt_hA0clsGridQN`, `alt_hDclsGridQN` | 665, 709, 735 | conclusions = `hdrift`, `hA0cls`, `hDcls` fields (`∀ ω j, j < K → j < τ ω → …`; `∀ ω, 0 < τ ω → Cls 0 δ0 (A0 ω)`); `hY` from component 3 with `Yl n ≤ ν X`; crude sups (`hcrude`; `hAcr`, `hDcr`) explicit premises of the merged `alt_hA0clsQN`/`alt_hDclsQN` (T2294e) | PASS |
| C5 `altEnd_hexp`, `_stronglyMeasurable_zVecQN`, `_aFroz_eq_aTrue`, `altEnd_unQ`, `altEnd_yMomentsMax` | 805-926 | `altEnd_hexp` is literally `hexp` (`GridAssemblyN.lean:196-199`) at `A = aFrozQN`, `A0 = aTrueQN 0`, `Dr/Z/Y/R = dGridQN/zVecQN/yVecQN/rGridQN`; C5c on `K n ≤ τ ω`; C5d `‖𝓛−𝒦‖ ≤ ‖𝒬_u(𝓛−𝒦)‖ + N^{τN} B_u^{m+2} X` under the `altB45N_levelM` hypotheses, alternating `σ`; C5e one `C_P` before `K`, premise `∀ n, 0 < lam n` (T2294d) | PASS |

Deviations from the ticket's Design text are all added explicit premises in "statements free" targets, each proposed as a
paper-delta candidate (ticket allows `T2294c`-type additions): F1/F2/F3 of the prove report (a). None weakens a conclusion,
none hides a hypothesis in a structure (the only structure involved is the merged `GridAssemblyHypN`, unchanged).

## 4. Compiled nonempty instances (namespace `RBM.Ind.QEndAInst`, all built above)
```
$ grep -nE "^theorem .*_instance" QEndA.lean | cut -c1-70
1395 altYSetN_instance          1405 altYGridN_instance          1448 gridDriftQN_envelope_instance
1476 assembledRHSAltQN_qErr_le_instance   1555 hQ_altQN_subGaussStop_altQN_instance
1685 alt_hkerGridQN_instance    1706 alt_hdriftGridQN_instance   1733 alt_hA0clsGridQN_instance
1771 alt_hDclsGridQN_instance   1846 altExitMeasN_instance       1855 altEnd_hexp_instance
1878 altEnd_stronglyMeasurable_zVecQN_instance  1885 altEnd_aFroz_eq_aTrue_instance
1896 altEnd_unQ_instance        1913 altEnd_yMomentsMax_instance   (+ line 1435: example : T2294_altYGridN := @altYGridN)
```
Data: `sz0` (`d = 3`), `n = 4` (`L = 20`, `W = 10^5`), `m = 2` (`k = 4`), `E ≡ 0`, window `[0, 1/2]`, `K ≡ 4`,
alternating `σalt`; eventual targets at `sz0_tendsto` and an `n` from `.exists`. Checked by reading each call:
- `altYGridN_instance`: all deterministic premises discharged (`K+1 = 5 ≤ N^1` from `sz0_tendsto`, `ε = 1/10`, `X ≡ 1`,
  `l = 3`); only `Prec` stays a hypothesis (owed gate, ticket instance (2)).
- C1a: `STKbound` discharged by the proved `stKbound_holds` (no hypothesis left). C1b: `hsum` from the merged
  `sum_weighted_qErrQN_instance` at `K n = N^{31}`, `Xs = 1 ≤ X0 = 2`.
- C2: `M = 0`, `D'' = 5 + C_Q`, `D' = D''+2`; `hδ` discharged at fixed `n` (`altEnd_shift_fixed`), `W_n ≥ qProxyW0`.
- C3/C4a-c/C5a-e: every regime, window, `ν`, `hFv`, `hMΛ`, class and crude-sup premise discharged; `0 < τ ω` proved
  for every `ω` (`H_0 = 0` in all three sets); C4c derives `hAcr`, `hDcr` via `altEnd_crudeSup`, `altEnd_driftSup`.
No `N = 0`, empty index, collapsed window (`Δ > 0` stated in C2) or `False` premise. **Instances: PASS.**

## 5. Paper-delta coverage
Proposed in the prove report (d): `T2294a` (separate `hY` event at `N^ε XLK(n_−1)`), `T2294b` (`qErrQN` vs `stepErrN`,
bridge C1b), `T2294c` (C2 shift `W^{-(D''+1)}`, `2 ≤ W`, `M_ee ≤ W^{C₀}`), `T2294d` (`∀ n, 0 < lam n` from
`yMomentsQUnifN`), `T2294e` (crude sups at length `k` not in `GoodSetN`), `T2294f` (class exponent `ε'` ≠ `τ'`).
`grep -n T2294 docs/paper-deltas.md` → 0 lines (dispatcher appends). Every statement difference found in §3 is covered. **PASS.**

## 6. Observations (no RETURN)
- O1. C2/C3 take the regime at the window (`v ≤ 1−g²/L²`, `W⁻¹ ≤ (1−v)/(1−s)`) instead of at `(u_p, u_{j+1})`: stronger
  premises, met by S3-18a2's data (`STCaseI`, `v ≤ t`; `(1−t)/(1−s) ≤ (1−v)/(1−s)`).
- O2. The C2 instance needs `n` with `W_n ≥ qProxyW0` and `K = ⌈N^{D''+14}⌉`: the threshold is a merged opaque
  constant and the grid is the `AssembledN` regime; this is not a witness that holds only because a quantity is huge.
- O3. The C3 (zero tensor) and C5d (`H = 0`, `u = 0`) instances have trivial conclusions. That is the ticket's
  prescribed data (instances (5), (6)), and every premise is discharged at it.
- O4 (for the S3-18a2 draft, dispatcher). `T2294_altGridEndQN_shape` has only `sz.WO 𝔡` (eventual `lam > 0`), while
  `altEnd_yMomentsMax` (through the merged `yMomentsQUnifN`) needs `∀ n, 0 < sz.lam n` (`T2294d`).
- O5 (for the S3-18a2 draft, dispatcher). `hDcr` via `altEnd_driftSup` needs `dDriftLinN ≤ W^{C₀}`, but `Φ₁, Φ₂, Φ₃`
  are arbitrary in the shape. The report proposes a per-`n` split (`T2294e`, F1). Settle this before S3-18a2 is released.
- O6. Prove report: registry counts 8533/2795 vs 8601/2817 here, because `main` moved on (premise count 153 is the same in both).
  The prover states that no RBM2D file was read, so no port citation is owed.
