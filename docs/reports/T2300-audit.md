Auditor model: claude-opus-5-5

# T2300 audit (round 1) — BA-C2 `RBM3D/BA/MReg.lean` — Tue Oct  6 14:14:22 UTC 2026

Branch `t/T2300` at a4d82d3; detached audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2300-audit1`.

**Verdict: PASS** for all 7 targets (observations O1–O3 below; none changes a statement, instance, build, axiom or delta coverage).

## 1. Scope
```
$ git diff --stat main...t/T2300
 RBM3D/BA/MReg.lean     | 384 +++++++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean |   1 -
 2 files changed, 384 insertions(+), 1 deletion(-)
$ git diff main...t/T2300 -- RBM3D/Test/Axioms.lean | grep "^[-+] "
-   `RBM.Univ.UNDensBARow', -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-C2, `unDens'_freeConvST`)
```
Only the two sole writable files; the Axioms change is the one owed-line deletion the ticket orders (§20). No merged signature touched.

## 2. Build (audit worktree)
```
$ lake build RBM3D.BA.MReg   # error/warning lines and tail only
(warnings in RBM3D/BA/MReg.lean: 13, all: This line exceeds the 100 character limit, please shorten it!; 75 other warning lines come from rebuilt upstream modules)
Build completed successfully (3754 jobs).
exit 0
$ grep -nwE "sorry|admit|axiom|native_decide" RBM3D/BA/MReg.lean ; echo $?
1
```

## 3. Statements vs. the check-file pins, and axioms
Scratch file = check-file imports + `import RBM3D.BA.MReg` + check file body + the 7 `example : …_pin := @…` lines of the ticket acceptance + `#print axioms` of the 7 targets.
```
$ lake env lean AuditT2300Eq.lean ; echo exit $?
'RBM.BA.BAm_sub_le_of_im' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAbulk_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_lip_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BArho_rate_of_bulk' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAm_im_lower_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens'_ba' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDensBARow'_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```
So every target is definitionally the dispatcher's pin; target 7 has type `UNDensBARow'` (merged `UNPins.lean:159`), verbatim.
Mathematical reading of the pins (from the signatures):
- T1 `BAm_sub_le_of_im`: `0<c`, `0<Im z, Im z'`, `c ≤ Im m` at both points ⇒ `‖Δm‖ ≤ ‖Δz‖/c²`. Matches (R1); no sign of `g`, no `d`, `L` condition.
- T2 `BAbulk_window`: `0<κ`, `BAbulk κ E`, `|x−E| ≤ (πκ)³/8` ⇒ `BAbulk (κ/2) x`. Matches (R2), no `3 ≤ L`, `0 < g` added.
- T3/T4: Lipschitz `1/(π³κ²)` of `ρ` on the κ-bulk; rate `2η/(π³κ²)` for all `η>0`. Match (R3), (R4).
- T5: window `|x−E| ≤ (πκ)³/8`, `0<η≤10` ⇒ `Im m ≥ (πκ)⁵/2048`. Matches (R5).
- T6 `unDens'_ba`: eventual κ-bulk at `E`, `0<δ≤(πκ)³/8` ⇒ `UNDens'` of `(BAm·, BArho·E)`; proof fixes `c=(πκ)⁵/2048`, `C=K=1`, `Lp=1/c²` before `filter_upwards [hb]` (MReg.lean:300-302, 324): constants depend on κ only, quantifier order as in `UNDens'` (`PinsDens.lean:59`).
- T7: `δ₀ = (πκ)³/8` (MReg.lean:335), chosen before any `∀ᶠ n`; unused premises `3 ≤ d`, `Admissible` (binders `_` at :334) — weaker hypotheses use, not a special case.

## 4. Hidden hypotheses, vacuity, cycles
- No new structure, `def`, or `Prop`-valued definition; all hypotheses are in the signatures (`BAbulk`, order relations, `0 < Im`).
- Imports: `RBM3D.BA.ImmLower`, `RBM3D.BA.Boundary`, `RBM3D.BA.UNPins` + two Mathlib modules (MReg.lean:6-10), exactly the ticket list; all merged on `main`; new file, so no cycle.
- Merged dependencies used (signatures read): `BASelf_sub_le` (ImmLower:252), `BASelf_of_tendsto` (Boundary:164), `BAm_norm_le_one` (Ward:136), `BAbulk_iff_exists` (MFixedPoint:830), `BAm_im_lower_of_bulk` (ImmLower:424), `BAm_im_ge_mul` (ImmLower:327). No external hypothesis is introduced; nothing to limit-check.
- Unconditional: `#print axioms` above; no owed pin as a hypothesis of any target.

## 5. Registry pre-check
Root `lake build RBM3D` without the new import (the hub adds it at merge) flags the expected premise:
```
error: RBM3D.lean:342:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structural
  [RBM.Univ.UNDensBARow']
```
Pre-check as the hub will see it (scratch = all `import` lines of `RBM3D.lean` + `import RBM3D.BA.MReg` + `#assert_rbm_axioms`):
```
$ lake env lean AuditT2300Reg.lean ; echo exit $? ; grep -c UNDensBARow out
exit 0
axiom audit: 8632 theorems, 2823 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
 Quot.sound]; no project axioms: what the paper cites rather than proves is carried as hypotheses, not asserted.
0
```
`UNDensBARow'` is now counted as proved (absent from the owed ledger and from the unregistered list).

## 6. Compiled nonempty instances
In-file (MReg.lean:343-384, compiled by the build above, no open hypothesis):
- (I1) `example : UNDensBARow' := unDensBARow'_holds` — T7.
- (I2) T2 at `d=3, L=4, g=g0P, E=EP, κ=(Im mS 4 10)/π`; `0<κ` from `(selfS 4 10).1`, the bulk datum proved from `flowP_real` (`MReg_flow_bulk`, :351-354). Nondegenerate (κ>0, nontrivial window).
- (I3) T5 at the same point, all `x` in the window, `0<η≤10`.
- (I4) T6 at the merged admissible class sequence `S0 : Sizes 3` (`S0_adm`), `κ = clsκ 4 _ > 0` (`clsκ_pos`), eventual bulk `S0_bulk` (UNPins.lean:891), every `0<δ≤(πκ)³/8`.
- (I5) the merged consumer `inst_step1GoodC''_ba` with `rD := unDensBARow'_holds`; the remaining hypotheses `rT rN hLoc` are other gates' owed pins (BA-N1 etc.), allowed.
Targets 1, 3, 4 have no `example` of their own (the ticket's list (I1)–(I5) does not ask for one; T1, T4 are exercised inside (I4)). Auditor's check that their hypotheses are jointly satisfiable at concrete nondegenerate data (scratch `AuditT2300Inst.lean`, not committed):
```
-- target 1 at z = EP + i, z' = EP + i/2 (distinct points), c = (πκ)^5/2048
-- target 3 at x = EP, y = EP + (πκ)^3/8 (distinct), bulk level κ/2 from target 2
-- target 4 at E = EP, η = 1
$ lake env lean AuditT2300Inst.lean ; echo exit $?
exit 0
```
(T1 at `z=EP+i`, `z'=EP+i/2`, `c=(πκ)⁵/2048` discharged by T5; T3 at `x=EP`, `y=EP+(πκ)³/8`, level κ/2 from T2; T4 at `η=1`.) See O1.

## 7. Paper deltas
- The pin `UNDensBARow'` is merged and unchanged; its `UNDens'` form vs. the paper's "continuous density" (`1_2:624`) is the structural form registered with T2201 (`docs/paper-deltas.md:1471`, D512: "`UNDens'` 结构性").
- Targets 1–5 are quantitative consequences of `(self_m)` (`1_2:626-629`) with lossy constants the paper does not state; they restate no paper statement differently. No new delta needed; the prove report (d) proposes none, consistent with the ticket's expectation.

## 8. Per-target verdicts
| # | name | statement | hidden/vacuity | instance | axioms | verdict |
|---|---|---|---|---|---|---|
| 1 | `RBM.BA.BAm_sub_le_of_im` | = pin | none | auditor scratch (O1) | std | PASS |
| 2 | `RBM.BA.BAbulk_window` | = pin | none | (I2) | std | PASS |
| 3 | `RBM.BA.BArho_lip_of_bulk` | = pin | none | auditor scratch (O1) | std | PASS |
| 4 | `RBM.BA.BArho_rate_of_bulk` | = pin | none | auditor scratch (O1) | std | PASS |
| 5 | `RBM.BA.BAm_im_lower_window` | = pin | none | (I3) | std | PASS |
| 6 | `RBM.Univ.unDens'_ba` | = pin | none | (I4) | std | PASS |
| 7 | `RBM.Univ.unDensBARow'_holds` | = `UNDensBARow'` verbatim | none | (I1), (I5) | std | PASS |

## 9. Observations (not defects)
- **O1** Targets 1, 3, 4 carry no in-file `example`; the ticket's instance list omits them, and the auditor compiled concrete nondegenerate applications (§6). Same handling as T2261-audit O3. A later touch of `BA/MReg` could add the three lines.
- **O2** The 100-char warnings are on docstring lines 13-38, before `set_option linter.style.longLine false` (:42); style only.
- **O3** File length 384 lines, inside the ticket's 300/500/800 estimate and far below the 1500 cap (§98 (2)).
