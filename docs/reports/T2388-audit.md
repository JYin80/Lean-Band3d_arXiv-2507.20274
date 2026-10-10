Auditor model: claude-opus-5-5
# T2388 audit (round 2) — BA-E1 `RBM3D/BA/EKPins.lean`

Date (`date -u`): Sat Oct 10 15:57:23 UTC 2026. Branch `t/T2388` at b9ac5cf (merge-base b7efc3b; `main` e67bfbd).
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2388-audit2` (detached at b9ac5cf). Scratch: scratchpad `T2388/`.
Round 1 RETURNed only on paper-delta coverage (no Lean change asked). The branch head is unchanged (b9ac5cf). The repair
is report section (d), candidates T2388d and T2388e. Every check below was rerun from scratch.

## 1. Scope, hygiene, build
```
$ git diff --name-only main...HEAD
RBM3D.lean
RBM3D/BA/EKPins.lean
RBM3D/Test/Axioms.lean
$ git diff main...HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean | grep '^[+-]'   (abridged to the + lines)
+import RBM3D.BA.EKPins
+   `RBM.BA.BAEKSumDecay1, -- ... (T2388, BA-E1, T2378 §2: owed; owner BA-E2)
+   `RBM.BA.BAEKSumDecayNAL, -- ... (T2388, BA-E1, T2378 §2: owed; owner BA-E2)
+   `RBM.BA.BAEKSumDecay2, -- ... (T2388, BA-E1, T2378 §2: owed; owner BA-E2)
+   `RBM.BA.BAEKSumDecayNonzero, -- ... (T2388, BA-E1, T2378 §2: owed; owner BA-E3)
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/BA/EKPins.lean | wc -l
       0
$ wc -l RBM3D/BA/EKPins.lean
     856        (stop line 2,000; split point 1,500 not reached)
$ lake build RBM3D.BA.EKPins | grep -E "error|warning: declaration uses|Build completed"
Build completed successfully (3756 jobs).
$ lake build | grep -E "BAEK|error|Build completed|axiom audit"     (registry pre-check)
info: RBM3D.lean:433:0: axiom audit: 11077 theorems, 3257 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.BA.BAEKSumDecay1: 1 [no certificate]
  RBM.BA.BAEKSumDecayNAL: 1 [no certificate]
  RBM.BA.BAEKSumDecay2: 1 [no certificate]
  RBM.BA.BAEKSumDecayNonzero: 1 [no certificate]
Build completed successfully (4201 jobs).
$ lake env lean docs/tickets/checks/T2388-check.lean   -> no error lines; exit 0
```
No existing file other than the two rebase-union files is touched, so no frozen signature changes.

## 2. Axioms (`lake env lean <scratch>/Ax.lean`, importing `RBM3D.BA.EKPins`)
```
'RBM.BA.BAuKer_eq_one_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAuKer_eq_one_add_Xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAuKer_convex' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSumNdecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKXiDecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKXiBall_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baEKSameRow_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_baEKSumNdecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_baEKXiDecay' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_baEKXiBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_baEKSameRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_BAEKSumDecay1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_BAEKSumDecayNAL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_BAEKSumDecayNonzero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.EKPinsInst.inst_BAEKSumDecay2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## 3. Statements against the pin
Targets 1-2: the pin text is the probe `t/T2378:RBM3D/Probe/T2378Pins.lean`. Script `ext2.py` extracts each declaration
(a def up to its blank line; a theorem up to `:= by`):
```
$ git show t/T2378:RBM3D/Probe/T2378Pins.lean > probe.lean; git show t/T2388:RBM3D/BA/EKPins.lean > ek.lean
$ for f in probe ek; do python3 ext2.py $f.lean BAuKer BAUN BAEKSumNdecay BAEKSumDecay1 BAEKSumDecayNAL \
    BAEKSumDecay2 BAEKSumDecayNonzero BAuKer_eq_one_add BAuKer_convex > $f.stmt; done
$ wc -l probe.stmt ek.stmt; diff probe.stmt ek.stmt && echo IDENTICAL; grep -c MISSING probe.stmt ek.stmt
      47 probe.stmt
      47 ek.stmt
IDENTICAL
ek.stmt:0
probe.stmt:0
```
Target 3: `theorem baEKSumNdecay_holds (d n : ℕ) (Λ κ : ℝ) : BAEKSumNdecay d n Λ κ` (EKPins.lean:218). It is unconditional
and has the paper's bound `((1-s)/(1-t))^n` (`A:100-104`, `(Xi_infint)`). The proof is `EKPins_norm_Q_le` (Ward row sums),
then `EKPins_norm_Theta_le` (`Θ = 1 + tMΘ`), then `norm_tensorKer_le`.

Target 4: the pins are not in the probe; the ticket fixes them as the band forms `Evolution/XiPins.lean:281-307` with
`BAReal` in place of `‖μ‖ = 1`. Read side by side (band text `sed -n 280,307p`, BA text EKPins.lean:240-268):
| pin | band → BA | verdict |
|---|---|---|
| `BAEKXiDecay` | drops `Prop5Decay d Λ →` (merged `baProp5_holds`); adds `0 < κ`; `∀ μ, ‖μ‖=1` → `∀ E m, BAReal d L g κ E m`; adds `∀ σ₁ σ₂`; `XiKer` → `BAXi`; RHS, ranges `0≤s≤t<1`, `g²/L² ≤ 1-t` identical | PASS |
| `BAEKXiBall` | the same substitutions; `Λ' ≥ 1`, `1 ≤ R ≤ Λ'ℓ_s`, `D` within `R` of `ctr`; RHS `CΛ'²(g²+|1-s|)/(g²+|1-t|)` identical | PASS |
| `BAEKSameRow` | `∀ m, ‖m‖=1 → κ ≤ Im m` → `∀ E m, BAReal` (`BAReal` contains `κ ≤ m.im`); `uKer … (m(σ)²)` → `BAuKer … σ σ` | PASS |
Constants `(d, Λ, κ)` come before `∃ C`, as the band. `BAXi` (`(t-s)•(M^{(σ₁σ₂)} Θ_t)`, EKPins.lean:58) is the paper's
`Ξ^{(i)}` (`A:99`), with `S^{(B)} = I` at BA.

## 4. Hidden hypotheses, vacuity, cycles
```
def RBM.BA.BAReal := fun d L [NeZero L] g κ E m => RBM.BA.BASelf d L g (↑E) m ∧ κ ≤ m.im
def RBM.BA.BASelf := fun d L [NeZero L] g z m => 0 < m.im ∧ m = (↑(L ^ d))⁻¹ * (RBM.BA.BAMB d L g z m).trace
@RBM.BA.BAflow_real : ∀ {d} (κ ε 𝔠 𝔡 : ℝ) (sz) (z), BAFlow sz κ ε 𝔠 𝔡 z → ∀ n, BAReal d (sz.L n) (BAflowLam0 sz z n) κ …
RBM.BA.FlowPinsInst.flow_sz0 : BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq
```
- The pins are plain `Prop` defs with explicit binders; there are no structure fields. `BAReal` is the merged bulk datum
  (self-consistency and `κ ≤ Im m`), and it is inhabited at the instance by `BAflow_real … flow_sz0 0` (both merged).
- The four open pins appear only as hypotheses of their instances. They are registered owed (§1).
- No cycle: the file imports only merged modules (`BA.Prop6Path`, `BA.KBase`, `BA.KKernel`, `BA.GreenSchur`,
  `Evolution.Pins`).
- No external hypothesis, so no limit check is needed.
- Name clash (`git grep -lw <name> main -- 'RBM3D/*.lean' | grep -v Probe | wc -l`): every name has 0 hits.
```
BAuKer:0 BAUN:0 BAXi:0 BAuKer_eq_one_add_Xi:0 BAEKSumNdecay:0 BAEKXiDecay:0 BAEKXiBall:0 BAEKSameRow:0 EKPinsInst:0 baEKSumNdecay_holds:0 baEKXiDecay_holds:0 baEKXiBall_holds:0 baEKSameRow_holds:0
```

## 5. Compiled nonempty instances (EKPins.lean §5, `namespace EKPinsInst`; all compile, §1-§2)
Common data: `d = 3`; `L = sz0.L 0 = 4` (`LI_real`); `g = gI > 0` (`gI_pos`) with `gI ≤ 1/64` (`gI_le`); `Λ = 1`;
`κ = 1/2`; `BAReal` from `hrI`; `n = 2`; `s = 0`; `t = 1/2`, which satisfies `g²/L² ≤ 1-t` (`gI_sq_le`).
| endpoint | instance | data |
|---|---|---|
| `baEKSumNdecay_holds` | `inst_baEKSumNdecay` :690 | `σ = (+,-)`, `A = δ_0` (`AI_zero`) |
| `baEKXiDecay_holds` | `inst_baEKXiDecay` :704 | `σ = (+,-)`, every `a b` |
| `baEKXiBall_holds` | `inst_baEKXiBall` :713 | `D = ballI ∋ 0` (ℓ¹ radius 1), `Λ' = R = 1 ≤ ℓ_s` (`one_le_ellT`) |
| `baEKSameRow_holds` | `inst_baEKSameRow` :723 | both `σ` |
| open pins (hypothesis) | `inst_BAEKSumDecay1/NAL/Nonzero/Decay2` :738-843 | `W=16, ε=1/2, D=2` (`W^ε = 4`, `sixteen_rpow_half`). NAL: `σ = (+,+)`. Nonzero: `s = 1-g²/L² < t = 1-g²/(2L²) < 1`. Decay2: `K = 2`, `log 4 ≤ 4`, `4³ ≤ 16²`, sum-zero `AzI` |
Every deterministic hypothesis is discharged in the term. None is degenerate: `L = 4`, `n = 2`, the tensors are nonzero,
the ball is nonempty and the windows are open.

## 6. Paper deltas
```
$ grep -o "^- T2388[a-e]" docs/reports/T2388-prove.md
- T2388a
- T2388b
- T2388c
- T2388d
- T2388e
```
- T2388a: `BAEKSumNdecay` carries `BAReal`, `g ≤ Λ`. T2388c: the new public `BAXi`, `BAuKer_eq_one_add_Xi`.
- T2388b: `(eq:decayXi)` for all `(a,b)`, proved through `Θ` (not `Mbound_AO`), `Λ`-dependent constant.
- T2388d (new; round-1 item 1): `BAEKSameRow` `‖1+Ξ‖ ≤ C` is weaker than `(eq:samecolor)` (`A:209`): it has no `t-s` factor
  and no `Proj_{e⊥}` part. The entry checks this against the paper's own use at `A:227` ("`(eq:decompUalt)` and the first
  bound in `(eq:samecolor)` give `‖1+Ξ^{(i)}‖ ≲ 1`", read above). It names the band consumers (`Nonzero.lean`, `SumDecay.lean`).
- T2388e (new; round-1 item 2): `BAEKXiBall` is a Lean-only form. It has an arbitrary `D` within `R ≤ Λ'ℓ_s` and the factor
  `Λ'²`, against the inline cutoff `W^εℓ_s` and the factor `W^{2ε}` of `A:131-149`.
- The four open pins have the band shapes, which band deltas D33, D34, D37, D38 and D74 cover (round 1). The probe pin text
  is unchanged (§3).
Every Lean/paper statement difference found in §3 now has a candidate.

## 7. Verdicts
- Target 1 (`BAuKer`, `BAUN`, `BAuKer_eq_one_add`, `BAuKer_convex`): **PASS**.
- Target 2 (the five stage-E pins): **PASS**. The text is identical to the probe, and the instances compile.
- Target 3 (`baEKSumNdecay_holds`): **PASS**. It is unconditional, uses the standard axioms, and has a nondegenerate
  instance.
- Target 4 (`BAEKXiDecay`, `BAEKXiBall`, `BAEKSameRow` and their proofs): **PASS**. The statements are the ticket's band
  forms, and the round-1 coverage gap is closed by T2388d and T2388e.
- Target 5 (instances): **PASS**.
- Target 6 (registry, four owed lines, pre-check): **PASS**.

**Overall: PASS.** Needs dispatcher sign-off: no.

### Observations (not grounds for RETURN)
- `BAXi`, `BAuKer_eq_one_add_Xi` are public and unpinned (needed by the Ξ pins; T2388c); `EKPinsInst` carries the stem.
