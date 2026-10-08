Auditor model: claude-opus-5-5

# T2336 audit (BA-P4c, `RBM3D/BA/KHeatDiff.lean`), round 1 — Thu Oct  8 14:52:47 UTC 2026

Branch `t/T2336` at `462ebdd`; merge base with `main` `d002ba6` (T2335 merge); audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2336-audit1` (detached at `462ebdd`). Scratch: scratchpad `T2336/`.

## 1. Files touched

```
$ git diff --stat main...t/T2336 ; git diff --name-status main...t/T2336
 RBM3D/BA/KHeatDiff.lean | 1757 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1757 insertions(+)
A	RBM3D/BA/KHeatDiff.lean
```
Only the sole writable file (new). No merged file changed, so no frozen signature touched.
Imports: `RBM3D.BA.KHeatTail` (merged on `main`, `d002ba6 T2335: merge BA-P4b BA/KHeatTail`; it imports
`RBM3D.BA.KHeat`) and `Mathlib.Algebra.Group.ForwardDiff`; both listed in the module docstring and the prove report,
as the ticket's "and what a lemma needs; list it" allows. Never `import RBM3D`.

## 2. Statements against the pin (`docs/tickets/checks/T2336-check.lean` section 2)

Script: body of `def T2336_<n> : Prop :=` from the check file vs the type of `theorem <n> :` from the Lean file,
whitespace-normalised, `diff`:
```
== kBA_diff1_le
IDENTICAL
== kBA_diff2_le
IDENTICAL
$ wc -c pin_*.txt lean_*.txt     (non-empty extractions)
 461 pin_kBA_diff1_le.txt   557 pin_kBA_diff2_le.txt   460 lean_kBA_diff1_le.txt   556 lean_kBA_diff2_le.txt
```
(1-byte difference = trailing space removed by the normaliser.) Elaborated equality (scratch `eq.lean` = check-file
imports + `import RBM3D.BA.KHeatDiff` + the check namespace without `#check`s):
```
example : RBM.BA.T2336Check.T2336_kBA_diff1_le := RBM.BA.kBA_diff1_le
example : RBM.BA.T2336Check.T2336_kBA_diff2_le := RBM.BA.kBA_diff2_le
$ lake env lean eq.lean  -> exit=0
```
Quantifier order as pinned: `d, 2 ≤ d, Λ, κ` fixed before `∃ C`, then uniform in `L ≥ 3`, `g ∈ (0, Λ]`, `BAReal`,
`τ ∈ (0, L²]`, `a`, directions. Decay `min 1 τ^{-(d+1)/2}` (resp. `τ^{-(d+2)/2}`), polynomial factor
`(1 + |a|²/max τ 1)^{-(⌊d/2⌋+1)}`: verbatim the dispatcher's corrected form.

**`BAKhat_diff_le`** (public, shape by the prover; ticket mathematics (1)):
```
theorem BAKhat_diff_le : ∀ d : ℕ, 2 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E : ℝ) (m : ℂ), 0 < g → g ≤ Λ → BAReal d L g κ E m →
      ∀ (j : Fin d) (k : Zd d L),
        |fwdDiff (Pi.single j (1 : ZMod L)) (BAKhat d L g E m) k|
            ≤ C * g ^ 2 * (L : ℝ)⁻¹ * (Real.sqrt (BAthetaSq d L k) + (L : ℝ)⁻¹) ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ N →
          |(fwdDiff (Pi.single j (1 : ZMod L)))^[i] (BAKhat d L g E m) k| ≤ C * g ^ 2 * ((L : ℝ)⁻¹) ^ i
```
`BAthetaSq d L k = Σ_j (2π|k_j|_L/L)²` (`KSymbol.lean:483`), so `√BAthetaSq = |θ_k|`. Matches the ticket's
`|Δ_j K̂| ≤ C g² L^{-1}(|θ_k|+L^{-1})` and `|Δ_j^r K̂| ≤ C_r g² L^{-r}`; Lean covers every order `r ≤ N` for arbitrary
`N` (ticket: `2 ≤ r ≤ d+2`), a stronger-in-range form with `C = C(d,Λ,κ,N)`. Not pinned; reported as T2336b.

## 3. Hidden hypotheses, vacuity, cycles

Public declarations (script: non-`private` `theorem|lemma|def|…` lines):
```
1573:theorem kBA_diff1_le    1599:theorem kBA_diff2_le    1656:theorem BAKhat_diff_le
1722:theorem inst_diff1     1731:theorem inst_diff2     1742:theorem inst_symb      (namespace KHeatDiffInst)
```
All 67 helpers are `private` with prefix `KHeatDiff_`. No new structure, class or Prop-valued hypothesis: the only
predicate in the targets is the merged `BAReal` (the pin's own). No external hypothesis is introduced, so no limit
check is needed. Dependencies are merged (`kBA_fourier`, `BAK_gap`, `BAK_off_le`-derived moments, `kBA_le` of T2335);
the regime split is assembled by `KHeatDiff_comb` from two proved private theorems `KHeatDiff_A` (τ ≥ 1, Fourier +
summation by parts) and `KHeatDiff_B` (τ ≤ 1), with no assumption left open. No cycle (new leaf module).
Name clash (outside the new file and `Probe/`):
```
$ grep -rn "kBA_diff1_le\|kBA_diff2_le\|BAKhat_diff_le\|KHeatDiffInst" --include='*.lean' RBM3D | grep -v "BA/KHeatDiff.lean\|Probe/" | wc -l
       0
```

## 4. Compiled nonempty instances

`inst_diff1`, `inst_diff2`, `inst_symb` (lines 1722-1751) apply the three theorems at `d = 3`, `L = 4`, `Λ = 10`,
`κ = Im m₀`, `τ = 1 ∈ (0, 16]`, `a = ![1, 0, 2]` (`a ≠ 0`), `j = 0` / `(i, j) = (0, 2)` / `j = 1`, `k = ![1,0,2]`,
`N = 5`, orders 1 and 3, at the merged flow point `MFixedPointInst.P : FlowPt 4 10`. Every hypothesis is discharged:
`2 ≤ 3`, `0 < 10`, `P.real.1.1 : 0 < Im m₀`, `3 ≤ 4`, `P.g0_pos`, `P.g0_le : g0 ≤ 10`, `P.real : BAReal 3 4 g0 (Im m₀) E m₀`,
`one_pos`, `1 ≤ 4²`. `P` is built from the merged existence proof `exists_flowPt` (`MFixedPoint.lean:886-893`,
`Nonempty (FlowPt L g)` proved, not assumed), so the data are concrete and nondegenerate (no `N = 0`, empty index,
`False` premise or collapsed window; `τ = 1` is the ticket's prescribed instance value). They compile (section 5).

## 5. Build and axioms (audit worktree)

```
$ lake build RBM3D.BA.KHeatDiff
⚠ [3744/3744] Built RBM3D.BA.KHeatDiff (15s)
Build completed successfully (3744 jobs).
exit=0
```
Warnings in the new file: only `linter.style.longLine` at lines 22-25 (module docstring); no errors.
```
$ lake env lean eq.lean
'RBM.BA.kBA_diff1_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.kBA_diff2_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAKhat_diff_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_diff1' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_diff2' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.KHeatDiffInst.inst_symb' depends on axioms: [propext, Classical.choice, Quot.sound]
RBM.BA.MFixedPointInst.P : RBM.BA.MFixedPointInst.FlowPt 4 10
exit=0
$ grep -nE "\bsorry\b|\badmit\b|^\s*axiom\b|native_decide|@\[implemented_by|\bunsafe\b" RBM3D/BA/KHeatDiff.lean ; echo $?
1                                   (no hits)
```
Registry pre-check (scratch `reg.lean`: `import RBM3D` / `import RBM3D.BA.KHeatDiff` / `#assert_rbm_axioms`):
```
$ lake env lean reg.lean
axiom audit: 10230 theorems, 3037 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: ...
premises found by scanning: 140 (borrowed 1, owed 79, structural 41, refuted 6, superseded 13).
exit=0
```
(No new registry premise; the ticket says "Registry: none".) The full `lake build` is the hub's at merge.

## 6. Paper deltas

Prove report (d):
- T2336a: the `max τ 1` decay factor (dispatcher's correction of supervisor 1048 C4; negative control in (a)(iii)),
  and the route difference (paper `A:50-56` sums by parts on `Θ̂`, Lean on the heat-kernel Fourier summand).
- T2336b: `BAKhat_diff_le` as a new statement (one-direction symbol regularity, all orders `≤ N`).
Every Lean/paper difference found in sections 2-3 (corrected decay factor; heat-kernel route; symbol lemma with
arbitrary order) is covered by T2336a/T2336b. The pins themselves have no paper counterpart beyond `A:50-56`.

## 7. Observations (no RETURN)

- File length 1757 lines: above the ticket's size band top (1700), below the binding stop rule (1800).
- `main` has advanced to `3f750b6` since the merge base `d002ba6`; `git diff main...t/T2336` still lists only the new
  file. The hub's full build at merge is the check against the new `main`.

## 8. Verdict

| target | statement | hidden hyp / vacuity / cycle | instance | build / axioms | paper deltas | verdict |
|---|---|---|---|---|---|---|
| `kBA_diff1_le` | identical to pin (text + `example` exit 0) | none | `inst_diff1`, compiled | pass / 3 std | T2336a | **PASS** |
| `kBA_diff2_le` | identical to pin (text + `example` exit 0) | none | `inst_diff2`, compiled | pass / 3 std | T2336a | **PASS** |
| `BAKhat_diff_le` | matches ticket math (1); order range `≤ N` arbitrary (stronger) | none | `inst_symb`, compiled | pass / 3 std | T2336b | **PASS** |

**T2336: PASS.** No dispatcher sign-off needed.
