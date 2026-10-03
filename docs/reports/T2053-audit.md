Auditor model: claude-opus-5-5

# T2053 audit, round 1 (EK-6: `Evolution/Prec.lean`, Amend 1 edit of `STEKNonzero`), Sat Oct  3 19:11:32 UTC 2026

Branch `t/T2053` at `6270281`, merge-base `6ef5d49`; audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2053-audit1` (detached).

## 1. Scope of the diff
```
$ git diff --stat main...t/T2053
 RBM3D/Evolution/Prec.lean       | 657 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Induction/Step34Pins.lean |   5 +-
$ git diff 6ef5d49 main -- RBM3D/Induction/Step34Pins.lean | wc -l      (main drift on the pin file)
       0
$ git merge-tree --write-tree main t/T2053 >/dev/null; echo $?
0
```
Both files are writable (Prec.lean: ticket; Step34Pins.lean: Amend 1, that edit only). `RBM3D/Test/Axioms.lean` untouched (no new `Prop`).

## 2. Statements (targets vs pin)
```
$ grep -n "^theorem stek_" RBM3D/Evolution/Prec.lean
215:theorem stek_sumNdecay_holds (d : ℕ) : STEKSumNdecay d := by
242:theorem stek_sumRes2NAL_holds (d : ℕ) : STEKSumRes2NAL d := by
358:theorem stek_sumRes1_holds (d : ℕ) : STEKSumRes1 d := by
391:theorem stek_sumRes2_holds (d : ℕ) : STEKSumRes2 d := by
422:theorem stek_nonzero_holds (d : ℕ) : STEKNonzero d := by
$ lake env lean ax.lean   (example : ∀ d, STEK… d := stek_…_holds, five lines)
exit 0
```
Each type is exactly the ticket's `(d : ℕ) : STEK… d`; no extra hypotheses. The `STEK*` definitions (`Step34Pins.lean` section 4) are merged T2049 pins and are unchanged except for Amend 1:
```
$ git diff main...t/T2053 -- RBM3D/Induction/Step34Pins.lean   (hunk lines only)
-bulk `κ ≤ Im m` (both charges): `‖Q^{(A)}∘U_{v,t,σ}∘𝒜_v‖_∞ ≺ X` from `‖𝒜_v‖_∞ ≺ X` (no decay hypothesis). -/
+bulk `κ ≤ Im m` (both charges): `‖Q^{(A)}∘U_{v,t,σ}∘𝒜_v‖_∞ ≺ X` from `‖𝒜_v‖_∞ ≺ X` (no decay hypothesis).
+The window carries `0 ≤ s` (DECISIONS §27, T2053 Amend 1): without it `ilambda > L` lets `[s,t]` reach negative times. -/
-    ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
+    ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
```
Matches Amend 1 exactly: `(∀ n, 0 ≤ s n) →` inserted right after the `1 - g²/L² ≤ s` hypothesis; one docstring sentence citing DECISIONS §27; nothing else changed. Merged users of `STEKNonzero` other than its definition:
```
$ grep -rln "STEKNonzero" RBM3D --include='*.lean'     (main)
RBM3D/Induction/Step34Pins.lean
```
so no merged instance/theorem is broken (the module rebuilds as a dependency of Prec, section 4).
Paper check: `lem:sum_decay_nonzero` case (ii) lives in times `[0,1)` (DECISIONS §27); `0 ≤ s` is a restoration, not a weakening of the paper's statement. Windows of the other four pins: `STEKSumNdecay` `0 ≤ s ≤ t < 1`; Res1/NAL/Res2 `STEKWin` (`0 ≤ s ≤ t ≤ 1-g²/L²`, `t<1`, eventually `W⁻¹ ≤ (1-t)/(1-s)`); parameters `𝔠 𝔡`, `Admissible`, `κ`, `n_ ≥ 2`, `3 ≤ d` before the sequence; conclusions with the paper's ratio exponents `n`, `n-1`, `n`, and `ℓ_t²/ℓ_v²` for Res1. No special-case adapter.

## 3. Vacuity, hidden hypotheses, cycles
- The five theorems are closed (no hypotheses beyond `d`); the proofs use merged theorems `ekSumNdecay_holds`, `ekSumDecay1_holds`, `ekSumDecayNAL_holds`, `ekSumDecay2_holds`, `ekSumDecayNonzero_holds`, `prop5Decay_holds`, `prop5Short_holds`, `prop6Diff1_holds`, `prop8ZeroMode_holds` (imports: `Step34Pins`, `Evolution.{SumDecay,SumDecayZero,Nonzero}`, `Propagator.Prop6Hold`; no `import RBM3D`). No structure field carries a hypothesis; no new `Prop`; no external hypothesis, so no limit check is required.
- Probe copy:
```
$ diff <(git show 3c58211:RBM3D/Probe/T2041Pins.lean | sed -n 691,830p | sed "s/stek_sumNdecay (d/stek_sumNdecay_holds (d/; s/stek_sumRes2NAL (d/stek_sumRes2NAL_holds (d/") <(sed -n 215,354p RBM3D/Evolution/Prec.lean); echo $?
0
```
(probe lines 684-690 are a section docstring, 831-832 blank/end: not code.)

## 4. Compiled nonempty instances (`Prec.lean:588-656`, 10 `example`s, all compile)
| target | data `(sz, s, t)` | window discharge |
|---|---|---|
| Ndecay | `(sz0, sInst≡0, tInst≡1/16)`, `(szB, 7/8, 15/16)`, `(szB, 15/16, 31/32)` | `norm_num` per `n` |
| Res1, NAL (`σ=(+,+)`, `k=0`), Res2 | `(sz0, 0, 1/16)`, `(szB, 7/8, 15/16)` | `win_sz0`, `win_szB_I` (proved, incl. the `∀ᶠ` via `W ≥ 32` / `W ≥ 4`) |
| Nonzero (`σ=(+,-)`, `A=univ`) | `(szB, 15/16, 31/32)` | `1-1/16 ≤ 15/16`, `0 ≤ 15/16`, `15/16 ≤ 31/32`, `31/32 < 1` by `norm_num` |

All with `d=3`, `n_=2`, `𝔠=1/6`, `𝔡=1/10`, `κ=1/2`, `m≡i` (`‖i‖=1`, `Im i = 1 ≥ 1/2`), `sz0_admissible`/`szB_admissible` (merged), `X≡1`. Tensors: `ekDelta0` (point mass, value 1 at 0: nonzero) and, for Res2, `Az = δ₀⊗(δ₀-δ_e)` with `Az_zero : Az L ![0,0] = 1` and `Az_sumZero : EKSumZero (Az L)` proved. `STEKDecay` (`decay_delta0` for all `n`; `decay_Az` eventually from `4 ≤ W^ε`), `STEKLow` (`low_one`, `b=0`), `‖𝒜‖ ≺ 1` (`prec_delta0`, `prec_Az` via `prec_of_le`) are private theorems of the same file with no open hypotheses. Sequences are nondegenerate (`N → ∞`, `L ≥ 4`, `g ∈ (0,1]`), nonempty windows, no `False` premise. This matches Amend 1's instance list (plus a third Ndecay instance).

## 5. Build and axioms (audit worktree)
```
$ lake build RBM3D.Evolution.Prec 2>&1 | grep -E "error|Build completed"; echo exit $?
Build completed successfully (3706 jobs).
exit 0
$ grep warning build.log   (5 warnings, none in Prec.lean: line-length in LaplaceGauss/PropUnit, unused hyp in HeatProduct, doc-string position in Step34Pins:12 — all pre-existing lines)
$ lake env lean ax.lean
'RBM.Gauss.Sizes.stek_sumNdecay_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes1_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes2NAL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_sumRes2_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Gauss.Sizes.stek_nonzero_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
$ grep -nE "sorry|admit|native_decide|^\s*axiom " RBM3D/Evolution/Prec.lean RBM3D/Induction/Step34Pins.lean; echo $?
1
```
Unpinned helpers are `private` (`prec_*`, `norm_delta0_le`, `decay_*`, `low_one`, `Az*`, `win_*`, `I_im`); instances in namespace `RBM.Gauss.PrecInst`. Frozen signatures: only the Amend-1-authorized `STEKNonzero` change.

## 6. Paper deltas
```
$ grep -nE "T2016a|T2016b|T2016f|T2042a|T2041c" docs/paper-deltas.md | cut -c1-60
287:## D33 · `(sum_res_2)` 带 `log L ≤ W^ε`（2026-10-03，T2016a
291:## D34 · `lem:sum_decay` 三条要求 `4 ≤ W^ε`（2026-10-03，T2016b
307:## D38 · EK 钉文的常数对 `g ∈ (0, Λ]` 一致，距离用 `ℓ¹`（2026-10-03，T2016f）
335:## D45 · `(sum_res_2)` 要求 `L` 关于 `W` 多项式：`L^d ≤ W^K`（2026-10-03，T2042a
351:- **D50（T2041c）**：`lem_+Q` 带 `4 ≤ W^ε` 与 `L^d ≤ W^K`（与 D45 / §21 同源：远处项有 `L^{dm}` 个）。
```
The targets add no new statement difference: the pins' eventual conditions are discharged along the sequence, not added as hypotheses; `0 ≤ s` needs no delta (DECISIONS §27). Coverage complete.

## 7. Observations (no effect on statements, instances, build, axioms or deltas)
- O1. The prove report's section (b) build log says the full `lake build` ran before the commit on base `6ef5d49`; main has since moved to `65ccfb3` (12 new modules, `RBM3D.lean`, `Test/Axioms.lean`). `git merge-tree` is clean and `Step34Pins.lean` is unchanged on main; the hub's merge-time full build covers the rest.

## Verdicts
- `stek_sumNdecay_holds`: PASS
- `stek_sumRes1_holds`: PASS
- `stek_sumRes2NAL_holds`: PASS
- `stek_sumRes2_holds`: PASS
- `stek_nonzero_holds`: PASS (with the Amend 1 pin edit, checked in section 2)

Overall: **PASS**. No dispatcher sign-off needed.
