Auditor model: claude-opus-5-5
# T2054 audit (round 1): S3-02 `stContract_holds` — Sat Oct  3 15:14:58 UTC 2026
Audit worktree: `/Users/junyin/Lean_proof/RBM3D-wt/T2054-audit1`, detached at `607d0e0` (t/T2054). Target: `stContract_holds (d : ℕ) : STContract d`.

## 1. Statement against the pin
```
$ lake env lean scratchpad/T2054/audit.lean      # in the audit worktree
stContract_holds : ∀ (d : ℕ), STContract d
'RBM.Gauss.Sizes.stContract_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
$ git diff main...t/T2054 -- RBM3D/Induction/Step34Pins.lean | wc -l
       0
```
The `#check (@stContract_holds : ∀ d : ℕ, STContract d)` elaborates, so the type is exactly the merged pin
(`Step34Pins.lean:307`), which this branch does not touch. Pin vs `3_5:922-932` (`yi2oslxj2`, `u2jzooi-2`), read by hand:
- part (1): `1 ≤ k`, `k+1 ≤ m`, all `σ`, `a_1..a_{m-1}`, sum over `a_m = x`; RHS `(W^d η_τ)^{-1}(M_{2k-1} M_{2m-2k-1})^{1/2}`: matches
  (`max_σ` on the LHS = `∀ σ`).
- part (2): `4 ≤ m`, `1 ≤ p`, `1 ≤ k < j+1 < l ≤ m-1` (label `a_{j+1}` = paper's `a_j`), `|𝒜(x)| ≤ C`, sum over `x` and `y ∈ 𝒜 x`
  at position `j`; RHS `C (W^d η)^{-1}(M_{2k-1} M_{2m-2l-1})^{1/2} M_{2(l-k)p}^{1/(2p)}`: matches. Lean takes `0 ≤ C` where the paper
  has `C > 0` (Lean is the stronger statement). Fixed parameters `(sz, n, E, τ, ω)` before the index data; no `∀ᶠ`.
- Hypotheses `|E| < 2`, `0 ≤ τ < 1` only. `3 ≤ d` not assumed (general `d`).
Verdict: PASS.

## 2. Vacuity, hidden hypotheses, cycles
```
$ sed -n 6,8p RBM3D/Induction/Contract.lean
import RBM3D.Induction.Step34Pins
import RBM3D.Hierarchy.ContractionBasic
import RBM3D.Gauss.FlowCalculus
$ git diff --name-only main...t/T2054
RBM3D/Induction/Contract.lean
```
- Imports are the three merged modules the ticket allows (not `RBM3D`). No structure carrying hypotheses: `STContract`
  quantifies over the merged `Sizes d`; the proof (`Contract.lean:1046-1094`) uses only `etaT_pos`, `etaT_eq_zt_im`,
  `seqHflow_isHermitian` (merged) and private lemmas of this file. No owed pin is assumed, no circular use (the theorem's
  only premise-free input is the pin's own definition).
- Non-vacuous: the premises `|E| < 2`, `0 ≤ τ < 1` hold at `E = 0`, `τ = 1/2` (§3).
Verdict: PASS.

## 3. Compiled nonempty instances (same file)
```
$ grep -n "^example" RBM3D/Induction/Contract.lean
1110:example : etaT 0 (1 / 2) = 1 / 2 := by
1116:example :
1128:example :
$ sed -n 1123,1124p RBM3D/Induction/Contract.lean
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).1 2 1
    (by norm_num) (by norm_num) ![true, false] ![0]
$ sed -n 1136,1139p RBM3D/Induction/Contract.lean
  (stContract_holds 3 sz0 0 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0).2 4 1 3 1
    ⟨1, by norm_num⟩ 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun x => {x}) (fun x => by simp) ![true, false, true, false]
    ![0, 0, 0]
$ cat scratchpad/T2054/audit.lean | tail -1 ; lake env lean scratchpad/T2054/audit.lean   (no error on this line)
example : sz0.L 0 = 4 ∧ sz0.W 0 = 32 := by constructor <;> rfl
```
- Data: `d = 3`, `sz0`, `n = 0` (`L = 4`, `W = 32`, so `|Zd 3 4| = 64` labels, `W^3 = 32768`), `E = 0`, `τ = 1/2`
  (`η = 1/2`, compiled at line 1110), `ω = 0`. Part (1) at `m = 2, k = 1`; part (2) at `m = 4, k = 1, j = 1` (label `a_2`),
  `l = 3, p = 1, C = 1, 𝒜 x = {x}` (`|𝒜 x| = 1 ≤ 1` discharged by `simp`). These are exactly the ticket's instances.
- Every hypothesis of the theorem is deterministic and discharged; no `N = 0`, empty index, collapsed window or `False`
  premise. `ω = 0` is an admissible sample (the pin is `∀ ω`).
Verdict: PASS.

## 4. Build, axioms, hygiene
```
$ lake build RBM3D.Induction.Contract      # audit worktree, cache copied from main (no Contract.olean there)
✔ [3706/3706] Built RBM3D.Induction.Contract (5.8s)
Build completed successfully (3706 jobs).
exit=0
$ grep -E "error|warning" build.log | grep Contract   -> (no lines; warnings listed are other modules' lint replays)
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/Induction/Contract.lean ; echo "grep rc=$?"
grep rc=1
$ grep -n "set_option" RBM3D/Induction/Contract.lean
34:set_option linter.style.longLine false
35:set_option linter.unusedSectionVars false
36:set_option linter.unusedDecidableInType false
```
Axioms (§1): `[propext, Classical.choice, Quot.sound]`. Diff touches only the sole writable file
`RBM3D/Induction/Contract.lean` (new, 1143 lines); `RBM3D/Test/Axioms.lean` untouched (allowed: registry lines only, and the
ticket assigns the `owedProps` removal to the cleanup ticket). No frozen signature changed. All other declarations are
`private` (CLAUDE.md §3 (E)): `grep -nE "^(theorem|def|lemma)" Contract.lean` returns only line 1046 `theorem stContract_holds`.
Verdict: PASS.

## 5. Paper deltas
```
$ grep -n "STContract\|yi2oslxj2\|u2jzooi" docs/paper-deltas.md
(no lines)
```
The theorem's statement is the merged pin (T2049); this ticket introduces no new Lean/paper statement difference. The
only pin/paper differences found in §1 (`∀ σ` for `max_σ`; `0 ≤ C` for `C > 0`) are equivalences or strengthenings of the
Lean side, not losses. The prove report's (d) item 3 ("none") is consistent. Proof-route differences (b.7 item 3) are
internal and need no delta. No missing coverage.
Verdict: PASS.

## Observations (no effect on verdict)
- O1. Prove report (d) item 1: the `owedProps` line for `STContract` (`RBM3D/Test/Axioms.lean:119`) can be removed after
  merge (cleanup ticket). (d) item 2: `inst_contract` in `Step34Pins.lean:1041` can now be discharged by `stContract_holds 3`.
- O2. The pin's part (2) with `C = 0` is trivially true on both sides; the instance uses `C = 1`, nondegenerate.
- O3. Three file-local `set_option` linter switches (lines 34-36); style only.

## Verdict
| target | verdict |
|---|---|
| `stContract_holds : ∀ d, STContract d` | PASS |

No dispatcher sign-off needed. On merge, the hub's registry scan should stop reporting `STContract` as owed (prove report b.5).
