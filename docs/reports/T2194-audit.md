Auditor model: claude-opus-5-5

# T2194 audit (round 1): S3-14 `Induction/QProxy`, Mon Oct  5 17:56:39 UTC 2026

Inputs: ticket `docs/tickets/T2194.md` + `T2194-amend-1.md` (T8 pin gains `0 ≤ c`); check file `docs/tickets/checks/T2194-check.lean`;
prove report `docs/reports/T2194-prove.md`; branch `t/T2194` at `fec932a` (base `d783ee3`); audit worktree `RBM3D-wt/T2194-audit1` (detached).

## 1. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.Induction.QProxy                      # audit worktree, exit=0
ℹ [3843/3843] Built RBM3D.Induction.QProxy (12s)
Build completed successfully (3843 jobs).
$ grep "QProxy.lean.*depends on axioms" build.log | sed 's/.*axioms: //' | sort | uniq -c
  44 [propext, Classical.choice, Quot.sound]               # = the 44 public declarations of the file
$ grep -cE "^(warning|error).*QProxy" build.log  -> 0 ;  grep -cE "sorryAx|does not depend" build.log -> 0
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|^set_option" QProxy.lean
59:set_option linter.style.longLine false   60: ...unusedSectionVars false   61: ...unusedVariables false   (no sorry/admit/axiom/native_decide)
$ git diff --name-only main...t/T2194
RBM3D/Induction/QProxy.lean                               # sole writable file; Test/Axioms.lean, RBM3D.lean untouched
$ printf 'import RBM3D\nimport RBM3D.Induction.QProxy\n#assert_rbm_axioms\n' > assert.lean; lake env lean assert.lean   # exit=0
axiom audit: 5781 theorems, 2067 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms ...
```
Imports (`QProxy.lean:6-10`): `Induction/QGridA`, `Induction/QopNorm`, `Induction/AzumaProxyN2`, `Induction/NQGood2`,
`Evolution/SumDecayZero`: all merged; not `RBM3D`, not T2186's files. No frozen signature touched (new file only).
New public names, `git grep -nwE "(theorem|def|abbrev|lemma) <name>" main`: 0 hits each for the 14 ticket names and
`qProxyCn qProxyCQ qProxy4C qProxyW0 deltaTensor`.

## 2. Pinned targets 1, 2, 3a, 3b, 7a, 7b, 8 (check file §2-§3 incl. amend 1)
```
$ diff <(sed -n 139,169p docs/tickets/checks/T2194-check.lean) <(sed -n 74,104p RBM3D/Induction/QProxy.lean) && echo IDENTICAL
IDENTICAL_DEFS_139-169_vs_74-104                         # qqTensorN, qvFormQN, zVecQN, yVecQN: byte-identical (incl. `noncomputable`)
$ cat chk.lean   # check file lines 1-16, + `import RBM3D.Induction.QProxy`, lines 17-251 without #check, then:
example : @RBM.Ind.T2194Check.qqTensorN = @RBM.Ind.qqTensorN := rfl      (same for qvFormQN, zVecQN, yVecQN)
example : T2194_martIncQN_ae_eq := @RBM.Ind.martIncQN_ae_eq
example : T2194_qv_at_propagatorQ := @RBM.Ind.qv_at_propagatorQ
example : T2194_qqTensorN_sumZero := @RBM.Ind.qqTensorN_sumZero
example : T2194_azumaSubGQ_ugenN := @RBM.Ind.azumaSubGQ_ugenN
example : T2194_azumaSubGQ_gridExitN := @RBM.Ind.azumaSubGQ_gridExitN
example : T2194_yMomentsQUnifN := @RBM.Ind.yMomentsQUnifN                  # the amended pin (`0 ≤ c`, check line 243)
$ lake env lean chk.lean ; echo exit=$?
exit=0                                                     # no output lines
```
Every pinned statement is proved with exactly the pinned type (the `example`s elaborate `@name` against the `Prop`).

## 3. Unpinned targets 4, 5, 6a, 6b against the ticket's mathematics
Signatures read at `QProxy.lean:623, 919, 1102, 1167` (verbatim extraction in the prove report (b), re-read here).
- **T4 `qqTensorBoundsN`**: `3 ≤ d`, `0 < Λg, K, C, c`, `3 ≤ L`, `0 < g ≤ Λg`, `1 < W`, `0 < ε < 1`, `4 ≤ W^ε`, `L^d ≤ W^K`,
  `d W^τ' ≤ W^ε`, `0 ≤ C₀`, `C_n + 2 < D`, `qProxyW0 … C₀ ε D ≤ W`, `STMollifierProps g C c ϑ`, `0 ≤ t < 1`, `‖T‖ ≤ M_ee ≤ W^{C₀}`,
  (Vb) form `ℓ_t W^τ' ≤ STdiamInf (b ⧺ b') → ‖T b b'‖ ≤ W^{-D}`. Conclusion: (i) `≤ W^{2C_nε}M_ee + W^{-D+C_Q}`; (ii) `EKFastDecay g t W ε (D−C_Q)`
  in `b'` for each `b`; (iii) `W^ε ℓ_t ≤ zdistD(b i − b j)` (the `ℓ¹` spread of `EKFastDecay`, `Evolution/Pins.lean:51`) `→ ≤ W^{-D+C_Q}`.
  Order `C_n, C_Q` (functions of `(d,m,Λg,K,C,c)`) → `ε, C₀, D` → `W₀` as in the ticket. (iii) is stronger than the ticket's
  `W^{-D+C_Q}(2+M_ee)`. `C_n + 2 < D` is a "D large" restriction (preflight row T4 (i)). PASS.
- **T5 `ugenPairQN_le_of_bounds`**: hypotheses of `nqGood1_ugenPairN_le_of_bounds` (`NQGood1.lean:431`) with `hσ` removed (any `σ`),
  `hdW`/`τ'` replaced by the `ℓ¹` slice/block decay at one level `δ'` (the `EKFastDecay` form at time `s`), plus `EKSumZero` in both
  blocks (`hz1`, `hz2`), `log L ≤ W^ε`, `L^d ≤ W^K`, `D₂ > k+1`, `0 ≤ δ' ≤ W^{-D₂}`. Conclusion `κ₄(κ₄M' + W^{C₄}δ') + W^{C₄}(W^kδ')`,
  `κ₄ = W^{C₄ε} r_{s,t}^k`, `C₄ = qProxy4C d k Λg κ' K` (`Classical.choose` of `ekSumDecay2_holds` with the merged
  `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds … (1/2)`; `QProxy.lean:444`). Matches ticket item 5. PASS.
- **T6a `qvFormQN_le_of_bounds`**: as T4 + T5 at `s = v`, `t = w`, `k = m+1`, `1 ≤ m`, `m + 2 + C_Q < D`; `hT`/`hTfar` bound
  `STeeM n E v M σ` by `M_ee ≤ W^{C₀}` and by `W^{-D}` in the (Vb) window. Right side closed form: `κ₄(κ₄ M_Q + W^{C₄}δ_Q) + W^{C₄}W^{m+1}δ_Q`,
  `M_Q = W^{2C_nε}M_ee + W^{-D+C_Q}`, `δ_Q = W^{-D+C_Q}` (stronger than the ticket's `δ_Q(2+M_ee)`), named constants
  `qProxy4C`, `qProxyCn`, `qProxyCQ`. PASS.
- **T6b `qvFormQN_le_of_goodSetN`**: 6a at `M ∈ sz.GoodSetN n E u (m+1) Γ Λ Φ τ' D` with `M_ee = Γ(ΓΛ)B_u^{2k}/η_u` (clause D4,
  `GridGoodN.lean:150`) and (Vb) (`:153`); hypothesis `M_ee ≤ W^{C₀}`. Preflight (iii) by script over the 10 target statements:
```
$ python3 stmt.py QProxy.lean <10 targets>
qqTensorBoundsN / ugenPairQN_le_of_bounds / qvFormQN_le_of_bounds / azumaSubGQ_ugenN / azumaSubGQ_gridExitN / yMomentsQUnifN /
martIncQN_ae_eq / qv_at_propagatorQ / qqTensorN_sumZero:  forbidden: {} | Φ in hyps: 0 Φ in concl: 0 | Γ/Λ/Φ binders: []
qvFormQN_le_of_goodSetN forbidden: {} | Φ in hyps: 2 Φ in concl: 0 | Γ/Λ/Φ binders: ['{Γ Λ Φ : ℝ}']
   Φ contexts: ["... {σ : Fin (m + 1) → Bool} {Γ Λ Φ : ℝ} {M : M", ") ℂ} (hM : M ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D) (hMee"]
(forbidden tokens: STXiLK STXiLKM STsupXiLK STNQConcl goodExitTauN Prec)
```
  `Φ` occurs only in its binder and the `GoodSetN` membership; no current-length level anywhere (§62 (4)). PASS.

## 4. Hidden hypotheses, vacuity, cycles
- No `structure`/`class`/new `Prop` in the file; no public theorem takes a new `Prop` premise (registry unchanged, §1).
- Constants `qProxyCn/CQ/4C/W0` (`QProxy.lean:434-456`) are `Classical.choose` of merged theorems under a `dite` on their range
  (default `1`/`2` outside); every theorem using them carries the range hypotheses (`hd`, `hΛ`, `hK`, `hC`, `hc`, `hκ'`, `hk`).
- External inputs: none new (EK-4 through merged `ekSumDecay2_holds`; PT through merged `prop5Decay_holds`, `prop5Short_holds`,
  `prop6Diff1_holds`). Dependencies are merged modules only; no cycle.

## 5. Compiled nonempty instances (namespace `RBM.Ind.QProxyInst`, all built in §1)
| target | instance (file line) | data / degeneracy check |
|---|---|---|
| 2 | `martIncQN_ae_eq_instance` 1506 | `sz0`, `QGridACheck` `E0 s0 t0 K0`, `n=j=0`, `sigma4` (4 indices), `moll`; hyps by `norm_num`/`data` |
| 3a | `qv_at_propagatorQ_instance` 1518 | `E=1/2`, `u=1/3<w=1/2`, `M = coordinateMatrix (0,0,true)` (Hermitian, non-scalar), `m=3` |
| 3b | `qqTensorN_sumZero_instance` 1551 | `QopAlgebra_mollifier 3 5 1 1`, clause 1 of `_props`; `Adelta_ne` (`A ≠ 0`), `Adelta_not_sumZero` |
| 4 | `qqTensorBoundsN_instance` 2156 | `sz0`, `n` with `W_n ≥ qProxyW0` (`exists_nat_ge`), `m=3`, `ε=1/5`, `τ'=1/10`, `C₀=4`, `D=C_Q+6`, `t=0`, delta tensor `≠ 0`; `ℓ¹` window attained (conjunct) |
| 5 | `ugenPairQN_le_of_bounds_instance` 1823 | `d=3,k=2,L=5,g=1/2,W=25,ε=1/2,D₂=4`, `s=1/2<t=9/10`, `E=0`, `σ=(+,−)`, `T=w⊗w ≠ 0` sum-zero, `M'=1`, `δ'=0`; window attained (`window_five`) |
| 6a, 6b | `qvFormQN_le_of_bounds_instance` 2130, `_of_goodSetN_instance` 2109 | same `sz0`, `n`; `u=v=0<w=1/2`, `E=0`, `σ=sigma4`, `M=0 ∈ GoodSetN … 4 100 1 (1/10) Dq` (`zero_mem_goodSetN_of_levels`); `hT`,`hTfar` = clauses (D4),(Vb); `L^∞` window attained |
| 7a | `azumaSubGQ_ugenN_instance` 1562 | `τ ≡ K 0 = 4`, `G 0 = {0}`, `G j = {Hermitian}`, `Q` = exact form at `M = 0`; `0 < p ≤ 4` |
| 7b | `azumaSubGQ_gridExitN_instance` 1582; `_instance_zero` 1597 | `G j = GoodSetN …` (`measurableGoodSetN`), `hQ` kept (S3-15/18 majorant, allowed); and `G j = {0}` with `hQ` discharged |
| 8 | `yMomentsQUnifN_instance_pos` 1641, `yMomentsQUnifN_instance` 1658 | `m=3`, `κ=1`, `τ'=1/2`, `C=(1+360)6^9`, `c=1/2`, `ϑ_n = QopAlgebra_mollifier`, `K=Kg`, `n` from the filter, `P > 0`, `Δ > 0` |

Every deterministic hypothesis is discharged at the concrete data (read at the lines above; the `sz0_numeric` lemma, 1999,
proves `1<W`, `4≤W^ε`, `log L≤W^ε`, `L^3≤W^2`, `3W^{1/10}≤W^{1/5}`, `W₀≤W`, `w ≤ 1−g²/L²`, `W⁻¹≤(1−w)/(1−v)`, `M_ee≤W^4`).
No `N = 0`, empty index, collapsed window or `False` premise. The `n` of items 4/6 comes from `exists_nat_ge` on the threshold of
the theorem itself, as the ticket prescribes ("eventually in `n`").

## 6. Ports and paper deltas
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h      -> 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Induction/AltProxyQ.lean
 RBM2D/Induction/AltProxyQ.lean | 530 +++++------------------------------------
 1 file changed, 64 insertions(+), 466 deletions(-)
$ git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Induction/AltProxyQ.lean | sed -n '93p;98p;107p;112p;227p;281p;303p;972p;1027p;1272p'
def qqTensorN … | def qvFormQN … | def zVecQN … | def yVecQN … | theorem martIncQN_ae_eq … | theorem qv_at_propagatorQ … |
theorem doubleSumZero_qqTensorN … | theorem azumaSubGQ_ugen … | theorem azumaSubGQ_goodExit … | theorem yMomentsQUnifN …
```
Port citations in the prove report (b) match `c9a24cf` at the cited lines. Lean/paper (ticket) differences and coverage:
- 7b at any measurable exit family, `azumaSubGQ_goodExit` not ported: `T2194a`.
- variance proxy via two EK-4 stages, any `σ`, block-wise sum-zero/decay, `log L ≤ W^ε`, `L^d ≤ W^K`: `T2194b`.
- `C_Q = 2C_n+2` as a function of `(d,m,Λg,K,C,c)` (ticket wrote `C_Q(d,m,K,C)`), `W₀` explicit hypothesis, no `(2+M_ee)` factor: `T2194c`.
- `C_P` gains `2m+2`, needs `0 ≤ c` (amend 1): `T2194d`.
All differences found in §3 are covered by `T2194a`-`T2194d`.

## 7. Observations (no effect on statement, instance, build, axioms or delta coverage)
1. The registry pre-check count here (5781 theorems) differs from the prove report's (5684): `lake env lean` reads the root
   `RBM3D` olean copied from the main build cache (main is ahead of the branch base by T2196); exit 0 and 0 axioms both ways.
2. Unpinned public helpers `deltaTensor`, `Adelta`, `Mx`, `w5`, `T5`, `*_ne`, `w5_sumZero` live in the instance namespace
   `RBM.Ind.QProxyInst` (not `private`, not file-stem-prefixed; §3 (E)); 0 clashes on main. `qProxy*` constants are stem-prefixed.
3. The hypothesis `C_n + 2 < D` of T4 (and `m + 2 + C_Q < D` of 6a) is a "large `D`" restriction recorded in preflight row T4 (i)
   and (a′) row (3); the dispatcher may fold it into `T2194c`.
4. File size 2261 lines vs ticket estimate 1350/1600/1900; amend 1's 2000-line stop rule was before targets 7-8 (they end at 1486).

## Verdict
| target | verdict |
|---|---|
| 1 vocabulary | PASS |
| 2 `martIncQN_ae_eq` | PASS |
| 3a `qv_at_propagatorQ`, 3b `qqTensorN_sumZero` | PASS |
| 4 `qqTensorBoundsN` | PASS |
| 5 `ugenPairQN_le_of_bounds` | PASS |
| 6a `qvFormQN_le_of_bounds`, 6b `qvFormQN_le_of_goodSetN` | PASS |
| 7a `azumaSubGQ_ugenN`, 7b `azumaSubGQ_gridExitN` | PASS |
| 8 `yMomentsQUnifN` (amended pin) | PASS |

**T2194: PASS.** No dispatcher sign-off needed.
