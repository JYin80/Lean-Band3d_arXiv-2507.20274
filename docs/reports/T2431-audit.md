Auditor model: claude-opus-5-5

# T2431 audit (round 1): BA-TL TL-V, `RBM3D/BA/TwistChain.lean`

Audit time: Mon Oct 12 00:41:42 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2431-audit1`, detached at `t/T2431` = `198fa66`.

## Verdict: PASS (both targets)

| target | statement | hidden hyp / vacuity / cycle | instance | build / axioms | paper deltas |
|---|---|---|---|---|---|
| `baTwistLoopBase_holds` | PASS (pin verbatim) | PASS | PASS | PASS | PASS (none needed) |
| `baChainTL_holds` | PASS (pin verbatim) | PASS | PASS | PASS | PASS (none needed) |

## 1. Diff scope and hygiene

```
$ git diff --stat main...t/T2431
 RBM3D/BA/TwistChain.lean | 297 +++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 297 insertions(+)
$ git log --oneline main..t/T2431
198fa66 T2431: TwistChain base case baTwistLoopBase_holds, chain baChainTL_holds, instances
$ git diff --stat main t/T2431 -- RBM3D/BA/TwistPins.lean RBM3D/Induction RBM3D/BA/FlowPins.lean
(no output: pins and frozen files untouched)
$ grep -nE "sorry|admit|native_decide|^axiom|[^_]axiom " RBM3D/BA/TwistChain.lean
(no output; grep exit=1)
$ grep -rn "baTwistLoopBase_holds\|baChainTL_holds\|TwistChain_" RBM3D | grep -v BA/TwistChain.lean
(no output: no name clash)
```
Only `RBM3D/BA/TwistChain.lean` is touched (sole writable; the `RBM3D.lean` import is added by the hub at merge). 297 lines against the stop line of 1,000. Every unpinned helper is `private` with the stem `TwistChain_` (declaration list: lines 43, 53, 58, 63, 69, 82, 98, 152, 194, 200, 206, 212, 218, 226); public: lines 110 and 240 only.

## 2. Statements against the pins

The ticket pins the two targets as the TL0 definitions `BATwistLoopBase d` (`TwistPins.lean:164`) and `BAChainTL d` (`:185`), unchanged on the branch (diff above). The theorems' types are those definitions literally:

```
$ lake env lean T2431/ax.lean      (import RBM3D.BA.TwistChain)
'RBM.BA.baTwistLoopBase_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baChainTL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
baTwistLoopBase_holds : ∀ (d : ℕ), BATwistLoopBase d
baChainTL_holds : ∀ (d : ℕ), BAChainTL d
ax exit=0
```
(the same file also elaborates `example (d : ℕ) : BATwistLoopBase d := baTwistLoopBase_holds d` and the `BAChainTL` analogue.)

Pins (for reference, `TwistPins.lean:164-166, 185-188`):
```
def BATwistLoopBase (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    STG0M (baFMz sz z) → BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) (fun _ => 0)
def BAChainTL (d : ℕ) : Prop :=
  BAMainIndTL d STAny → STHorizonG d (…) (fun sz z => BAflowT0 sz z) →
    STBaseG d (fun sz => Sizes.seqP (sz.withLam 0)) (…) baFMz → BATwistLoopBase d →
      (∀ κ ε 𝔠 𝔡 (sz : Sizes d) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z)) → BAMLOutTL d
```
No new hypothesis (ticket item 4, C1): the theorems take only `d : ℕ`. Quantifier order, the exponent `3/2` of `BATwistLoopLaw`, the time range `0 ≤ t_n ≤ T0` of `BAMLOutTL`, all four charges `σ : Fin 2 → Bool` and all `(a, c₁, c₂)` are those of the merged pins.

Proof shapes checked against the ticket:
- Target 1 (lines 110-139): `STG0M` rewrites `G_0 = M`; `BAMfine_eq` with `0 < Im m_F` from `BAflow_real … n |>.1.1` at every `n`; `twChg` keeps the offset form (`TwistChain_chg_off`); `twLoopX` of offset forms = `W^{-d} MB₂_{ac₁} MB₁_{c₂a}` via merged `twCirc_holds`; `Θ_0 = 1` by `simp [BATheta, PropThetaQ]`; `twK_ba` gives `twK`; `‖L̃_0 − K̃_0‖ = 0` and `TwistChain_precL_of_zero` (copy of `MainIndBase.lean:71-78`) closes the `PrecL` with the nonnegative control `Bctl^{3/2}`. The error is exactly zero, so this is the genuine base case, not a weakened bound.
- Target 2 (lines 152-185, 240-262): induction over `stChainTime t K k` with invariant `STConclgL ∧ BATwistLoopLaw`; `k = 0` from `hbase` and `hTL … (hG …)`; step calls `BAMainIndTL d STAny` with regime `trivial` and the sixth input `ih'.2`; output mixing on `t_n = 0` with five copied mix lemmas plus `TwistChain_TL2_mix` (same `StochDomAt.of_subset_union` proof; the index type of `BATwistLoopLaw` does not depend on `τ`).

## 3. Hidden hypotheses, vacuity, cycles

- No structure field carries a hypothesis: the premises of `BAChainTL` are the five explicit `Prop`s of the pin. `BAMainIndTL d STAny` (BA-V V2a), `STHorizonG`, `STBaseG`, `STG0M` at `baFMz` (BA-V `GLoopAtT0`, registry `Test/Axioms.lean:139`) are other gates' pins, named as such by the ticket; `BATwistLoopBase d` is discharged by target 1 in the instances.
- No cycle: `TwistChain.lean` imports `RBM3D.BA.TwistPins` only; nothing on `main` imports it; `BAMainIndTL` is not used to prove itself (it is consumed once per chain step).
- Not vacuous: target 1's conclusion is proved with `ξ ≡ 0`, the exact identity `L̃_0 = K̃_0`; target 2's conclusion holds at every `0 ≤ t_n ≤ T0`, including the class `t_n = 0` via mixing (instances below exercise both `t ≡ 0` and `t ≡ 1/2`).

## 4. Compiled nonempty instances (`TwistChain.lean:272-295`)

Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`), `zSeq`, `flow_sz0`, `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`.
```
$ sed -n 272,297p RBM3D/BA/TwistChain.lean | grep -n "example\|flow_sz0\|half_lt_t0"
3:example (hG : STG0M (baFMz sz0 zSeq)) : BATwistLoopLaw (baFMz sz0 zSeq) μ0 (fun _ => 0) :=
4:  baTwistLoopBase_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 zSeq flow_sz0 hG
8:example (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (…) (fun sz z => BAflowT0 sz z))
13:    (by norm_num) sz0 zSeq flow_sz0 (fun _ => 0) (fun _ => le_rfl) (fun n => by linarith [half_lt_t0 n])).2.2.2.2.2
15:/-- Target 2 at `t ≡ 1/2` (`1/2 ≤ T0` by `half_lt_t0`): the six conclusions, the TL2 conjunct extracted. -/
16:example (hm : BAMainIndTL 3 STAny) (hh : STHorizonG 3 (…) (fun sz z => BAflowT0 sz z))
22:    (by norm_num) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)
```
(`(…)` abbreviates the `BAFlow` lambda; lines verbatim otherwise.) Every deterministic hypothesis is discharged at the data: `3 ≤ 3` (`le_rfl`), the three positivities (`norm_num`), `BAFlow` (`flow_sz0`), `0 ≤ t_n` and `t_n ≤ T0_n` (`le_rfl`/`norm_num`, `half_lt_t0`); the base premise `BATwistLoopBase 3` is discharged by target 1 (`baTwistLoopBase_holds 3`). Remaining hypotheses (`STG0M` at the carrier, `BAMainIndTL 3 STAny`, `STHorizonG`, `STBaseG`) are other gates' owed pins, as ticket item 3 prescribes. Not degenerate: `N = (LW)^3 ≥ 4^3·2^15` at `n = 0`, nonempty block index, `t ≡ 1/2` in `(0, T0]`. Instances compile (build §5).

## 5. Build, axioms, check file

```
$ lake build RBM3D.BA.TwistChain        (audit worktree)
✔ [3998/3998] Built RBM3D.BA.TwistChain (3.8s)
Build completed successfully (3998 jobs).
exit=0
$ grep -c "^error" build.log
0
$ lake env lean RBM3D/BA/TwistChain.lean 2>&1 | grep -E "error|sorry"
(no output; direct elab exit=0)
$ lake env lean docs/tickets/checks/T2431-check.lean      (on the branch)
check exit=0   (0 error lines)
```
Axioms (§2): `propext`, `Classical.choice`, `Quot.sound` only, for both targets. Full `lake build` is run by the hub at merge.

## 6. Paper deltas

Both statements are the TL0 pins verbatim and the file adds no other public declaration, so this ticket introduces no Lean/paper statement difference; the prove report's (d) "none (`T2431a` not needed)" is correct. The differences inside the pins themselves (exponent `3/2` vs the proofs' `2 − δ`, `twK` explicit) are TL0's (T2421/T2413) coverage, not this ticket's.

## 7. Observations (no effect on verdict)

- O1. Prove report line 1 is `Prover model: claude-sonnet-5-5`; 213 lines (≤ 250).
- O2. `set_option linter.* false` at file top (longLine, unusedSectionVars, unusedVariables, flexible): style only.
