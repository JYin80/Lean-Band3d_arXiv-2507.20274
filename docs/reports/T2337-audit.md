Auditor model: claude-opus-5-5
# T2337 audit (round 1) — BA-P5 `RBM3D/BA/Prop5.lean`, written Thu Oct  8 14:20:08 UTC 2026

Branch `t/T2337` = 002430d (merge-base with `main` 10dab65; `main` = 66cfb76). Audit worktree
`/Users/junyin/Lean_proof/RBM3D-wt/T2337-audit1` (detached at 002430d, cache cloned per CLAUDE.md §2).

## 1. Diff scope

```
$ git diff --stat main...t/T2337
 RBM3D/BA/Prop5.lean | 1479 +++++++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1479 insertions(+)
```
Only the sole writable file; no merged file and no frozen signature touched. Imports (lines 6-8):
`RBM3D.BA.KHeatTail`, `RBM3D.BA.FlowPins`, `RBM3D.Propagator.Prop5Hold` = exactly the ticket's list.

## 2. Statements against the pins (script diff vs `docs/tickets/checks/T2337-check.lean` §2)

```
$ for n in BAProp5mixed BAProp8mixed; do awk '/^def '$n' /{p=1} p&&/^$/{p=0} p' <file> | tr -s ' \n' ' '; ... diff; done
BAProp5mixed:      505 bytes
IDENTICAL
BAProp8mixed:      470 bytes
IDENTICAL
```
Each pin equals `BAProp5`/`BAProp8` (`BA/FlowPins.lean:171/:215`, read in the worktree) with the single
extra binder `σ₁ ≠ σ₂ →` after `∀ σ₁ σ₂ : Bool,`: same parameter order (`d Λ κ` fixed, `∃ C, ∃ c`
before `∀ L g E m t`), same `Bparam`·`exp(-c|a|/ℓ_t)` loss, same `(g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`,
same ranges `3 ≤ L`, `0 < g ≤ Λ`, `0 ≤ t < 1`, `BAReal d L g κ E m`.

Target theorems (file lines 928, 1389):
```
theorem baProp5mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp5mixed d Λ κ
theorem baProp8mixed_holds (d : ℕ) (Λ κ : ℝ) : BAProp8mixed d Λ κ
```
Check-file equality (b): scratch file = check-file imports + `import RBM3D.BA.Prop5` + check §1-§2 +
```
example : RBM.BA.T2337Check.T2337_baProp5mixed_holds := RBM.BA.baProp5mixed_holds
example : RBM.BA.T2337Check.T2337_baProp8mixed_holds := RBM.BA.baProp8mixed_holds
```
`lake env lean` on it: no error lines, exit 0 (output in §5).

Special case: both targets are the `σ₁ ≠ σ₂` restriction of the owed general pins `BAProp5`/`BAProp8`;
this is exactly what the ticket pins (registry: none; `σ₁ = σ₂` and `BAProp5to8` are P8). They do
not pass for, and are not claimed as, the general `BAProp5`/`BAProp8`. Docstrings (lines 922-927,
1383-1388) say so.

## 3. Hidden hypotheses, vacuity, cycles

- Both theorems take only `(d : ℕ) (Λ κ : ℝ)`; no structure argument, no extra hypothesis. Every
  hypothesis in the conclusion is a binder of the pin itself.
- Dependencies used in the proofs (lines 930-933, 1391-1394): `kBA_le` (`BA/KHeatTail`), `kBA_gap`
  (`BA/KHeat`), `RBM.Heat.lg_bulk` (`Propagator/LaplaceGauss`), and private `baP5_*` helpers in the
  same file. All are merged on `main` (imported modules); no import of `RBM3D` root, so no cycle.
- No external hypothesis is introduced (none to limit-check).
- Public names added: `BAProp5mixed`, `BAProp8mixed`, `baProp5mixed_holds`, `baProp8mixed_holds`,
  `Prop5Inst.inst_prop5{,_large_eps}`, `Prop5Inst.inst_prop8{,_large_eps,_zero}` (grep of
  `^(theorem|lemma|def|noncomputable def|abbrev)`); every other declaration is `private` (59 hits of
  `private`), file-stem prefix `baP5`.

## 4. Compiled nonempty instances

`namespace RBM.BA.Prop5Inst` (lines 1422-1477), data `RBM.BA.MFixedPointInst.P : FlowPt 4 10`
(`MFixedPoint.lean:893`, fields `g0_pos : 0 < g0`, `g0_le : g0 ≤ g`, `real : BAReal 3 L g0 m0.im E m0`,
`:881-883`). Applications:
```
inst_prop5           : baProp5mixed_holds 3 10 P.m0.im ... ; H 4 _ P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1/2)   ... true false (by decide) ![1,0,0]
inst_prop5_large_eps : ... (1/100) ... false true (by decide) ![2,1,0]   (zdistD = 3 by decide)
inst_prop8           : baProp8mixed_holds 3 10 P.m0.im ... (1/2)   ... true false (by decide) ![1,0,0]
inst_prop8_large_eps : ... (1/100) ... false true (by decide) ![2,1,0]
inst_prop8_zero      : ... t = 0, a = 0
```
Every deterministic hypothesis is discharged at concrete data: `3 ≤ 3`, `0 < 10`,
`0 < Im m₀` (`P.real.1.1`), `3 ≤ 4`, `0 < g₀ ≤ 10`, `BAReal` (`P.real`), `0 ≤ t < 1` (`norm_num`),
`σ₁ ≠ σ₂` (`decide`), `a = ![1,0,0] ≠ 0` with `zdistD = 1` (`decide`). This is the ticket's data
(`d = 3`, `L = 4`, `t = 1/2`, `a = ![1,0,0]`, KKernel/MFixedPoint instance point); nondegenerate
(`L = 4`, nonzero `a`, `t` interior, `g₀ > 0`, no `False` premise). Both charge orders covered. No
pinned-gate hypothesis remains. All compile (build §5).

## 5. Build and axioms

```
$ lake build RBM3D.BA.Prop5   (filtered: error|sorry|Build completed)
Build completed successfully (3743 jobs).
exit=0
$ lake env lean scratch/Audit.lean   (check-equality examples + #print axioms; RBM.* #check echo lines filtered)
'RBM.BA.baProp5mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baProp8mixed_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop5' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop5_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8_large_eps' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.Prop5Inst.inst_prop8_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
$ grep -nE "sorry|admit|native_decide|^axiom|^\s*axiom " RBM3D/BA/Prop5.lean
forbidden-grep exit=1   (no hits)
```
The hub runs the full `lake build` (with `#assert_rbm_axioms`) at merge; `main` has advanced
(10dab65 → 66cfb76: T2332 `Graph/LWEngine`, T2333 `Induction/DuhamelI`), no shared file.

## 6. Paper deltas

Prove report §(d):
- `T2337a`: `BAProp5mixed`/`BAProp8mixed` restrict properties 5 and 8 of `lem_propTH` to `σ₁ ≠ σ₂`
  (paper: all charges). This is the only Lean/paper statement difference introduced; covered.
- `T2337b`: proof-internal note (`γ = t g²` vs band `t g²/(1+2dg²)`), not a statement difference.
The underlying pin texts (`BAProp5`/`BAProp8`) are merged and unchanged; no new difference there.

## 7. Observations (no effect on verdict)

- The file sets `linter.style.longLine false`, `linter.unusedVariables false` etc. (lines 41-45);
  style only.
- The `example (d Λ κ) : BAProp5mixed d Λ κ := baProp5mixed_holds d Λ κ` lines (959, 1414) are
  restatements, not instances; the concrete instances are the `Prop5Inst` theorems (§4).

## Verdict

| Target | Verdict |
|---|---|
| `BAProp5mixed` (pin) | PASS (identical to check file) |
| `BAProp8mixed` (pin) | PASS (identical to check file) |
| `baProp5mixed_holds` | PASS |
| `baProp8mixed_holds` | PASS |

Ticket T2337: **PASS**. No dispatcher sign-off needed.
