Auditor model: claude-opus-5-5

# T2514 audit, row a (P1-P6, A1-A9), round 1 — Thu Oct 15 08:12:35 UTC 2026

Branch `t/T2514` at cf63c909 (merge-base with `main` = b2326aac). Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2514-audit1`
(detached at cf63c909). Scratch: `<scratchpad>/T2514/{defdiff.py, aud.lean, aud.out, build.log, full.log}`, uncommitted.

## 1. Statements against the pins

### 1a. P1-P3 text against the probe (`git show 921369b:RBM3D/Probe/T2449Pins.lean`, lines 150-260), whitespace-normalised
```
$ python3 -I defdiff.py probe.lean RBM3D/BA/MAPins.lean
BAGz / BAMz / BAprof / BAendDom / BAlocBad1z / BAlocBad2z / BAqdBadz / BAdecolBad      probe:True MAPins:True identical:True
BAEnd_locSCL / BAEnd_QDiffL / BAEnd_decolL / BAThm27L                                   probe:True MAPins:True identical:True
BAlocSCFixed / BAQDiffFixed / BAMAFixed / BAMANetLoc / BAMANetQD / BAMADecol / BAMAQUE  probe:True MAPins:True identical:True
```
(19 lines of output, one per name, all `identical:True`; condensed here.)

### 1b. All targets against the check's `T2514_*` pins (Lean)
`aud.lean` = `import RBM3D.BA.MALocal` + `docs/tickets/checks/T2514-check.lean` (Part 1 `#check`s and Part 2 pins, unchanged) + these auditor `example`s:
```
P1 (per sz): BAendDom ↔ T2514_EndDom, BAlocBad1z ↔ T2514_LocBad1z, BAlocBad2z ↔ T2514_LocBad2z,
             BAqdBadz ↔ T2514_QdBadz, BAdecolBad ↔ T2514_DecolBad                         (Iff.rfl each)
P2/P3 (∀ d): BAEnd_locSCL/EndLocSC, BAEnd_QDiffL/EndQDiff, BAEnd_decolL/EndDecol, BAThm27L/Thm27,
             BAlocSCFixed/LocSCFixed, BAQDiffFixed/QDiffFixed, BAMAFixed/MAFixed, BAMANetLoc/NetLoc,
             BAMANetQD/NetQD, BAMADecol/MADecol, BAMAQUE/MAQUE                              (fun _ => Iff.rfl each)
P4/P5 (∀ d): UNLocAvgBAAt/LocAvgAt, UNTrLocalBAAt/TrLocalAt, UNTrLocalInitBAAt'/TrLocalInitAt (fun _ => Iff.rfl)
P6:  example : T2514_ReadIff := ⟨UNLocAvgBA_iff_at, UNTrLocalBARow_iff_at, UNTrLocalInitBARow'_iff_at⟩
A2:  example : T2514_FixedOfML   := baLocSCFixed_of_ML
A3:  example : T2514_NetLocAll   := baMANetLoc
A4:  example : T2514_EndOfML     := baEnd_locSCL
A5:  example : T2514_EndThree    := baEnd_locSCL_three
A6:  example : T2514_BridgeAt    := unLocAvgBAAt_of_locSCL
A7:  example : T2514_BridgeAll   := UNLocAvgBA_of_BAEnd_locSCL
A8:  example : T2514_LocAvgOfML  := unLocAvgBAAt_of_ML
```
```
$ cd RBM3D-wt/T2514-audit1 && lake env lean <scratch>/aud.lean > aud.out 2>&1; echo exit=$?
exit=0
$ grep -cE "^.*: (error|warning)" aud.out
0
```
So the check compiles on the branch, and every target equals its pin up to definitional unfolding (the unfoldings the ticket allows:
`BAGz`, `BAMz`, `BAprof`, `T2514_QDExp`). The P6 theorems are proved by `Iff.rfl` (`MAPins.lean`, verified by reading the source).
Quantifier order (`3 ≤ d → ∀ 𝔠 𝔡 sz, Admissible → ∀ κ ε τ D > 0 → ∀ᶠ n`), losses `W^τ`, `N^{-D}`, the window `N^{-1+ε} ≤ Im z ≤ 1`,
the ρ-bulk `BAbulk`, and the law `seqP (sz.withLam 0)` are those of the pins. MNO-C3 holds: A6 is `∀ d, 3 ≤ d → BAEnd_locSCL d → UNLocAvgBAAt d`
and concludes the per-`d` def; A7 is one line (`UNLocAvgBA_iff_at.2 fun d hd => unLocAvgBAAt_of_locSCL d hd (h d)`).

## 2. Hidden hypotheses, vacuity, cycles
```
$ grep -nE "sorry|admit|native_decide|^axiom|^(private )?(noncomputable )?(structure|class|instance)" MAPins.lean MALocal.lean | wc -l
       0
$ grep -cE "opaque|implemented_by|@\[extern" MAPins.lean MALocal.lean
MALocal.lean:0
MAPins.lean:0
$ git grep -n "theorem unMLOutBA_three" main -- RBM3D
main:RBM3D/BA/MainIndTermBA.lean:47:theorem unMLOutBA_three : Univ.UNMLOutBA 3 := unMLOutBA_of_famStep 3 baMainIndFamTL_three
```
- No structure, class or instance: no hypothesis is carried in a field. Hypotheses of the targets are only `UNMLOutBA d` (A2, A4, A8; V's merged
  per-`d` output), `BAlocSCFixed d` (A3, the pin's own premise), `BAEnd_locSCL d` (A6, A7), `3 ≤ d`.
- `UNMLOutBA 3` is discharged by the merged `unMLOutBA_three` (above), so A5 `baEnd_locSCL_three : BAEnd_locSCL 3` is unconditional.
  The ticket's F1 ("unmerged, T2511 row b") is out of date: T2511 row b merged at c536c603, before b2326aac.
- No cycle: the imports of both files are merged modules (`BA/UNPins`, `MFixedPoint`, `MReg`, `Propagator/Pins`, `Endpoints`, `BA/MainIndTermBA`,
  `RandomLayerBGBA`, `GreenSchur`, `EMn2BA`, `Ward`, `Main/FixedZ`, `ZTransfer`, `ZNet`). `MALocal` imports `MAPins`; nothing imports `MALocal`.
- External hypotheses: none.

## 3. Compiled nonempty instances (built by the module build of §4)
| endpoint | instance (file:line) | data | open hypotheses |
|---|---|---|---|
| P6 (3 `Iff`s) | `MAPins.lean:259` | `S0`, `d = 3`, `κ_* = clsκ`, `E_* = (fp 4 _).E` with `S0_bulk`, `δ = (πκ_*)³/8` window by `BAbulk_window` | `UNLocAvgBA`, `UNTrLocalBARow`, `UNTrLocalInitBARow'` (other gates' pins: row b, and `d > 3` under Jun decision B) |
| A2 | `MALocal.lean:873` | `S0`, `(𝔠,𝔡) = (1/6,1/10)` by `S0_adm`, `κ_*`, `ε = 1/20`, `τ = 1/10`, `D = 2`, `unMLOutBA_three`; plus `∀ n, ∃ z, BAendDom …` (`inst_locAvg_domain`) | none |
| A3, A4 | `MALocal.lean:883` | same, net applied to `baLocSCFixed_of_ML 3 unMLOutBA_three`; domain nonempty at every `n` | none |
| A5 | `MALocal.lean:893` | same | none |
| A6, A8 | `MALocal.lean:897` | `unLocAvgBAAt_of_ML 3 le_rfl unMLOutBA_three` at `S0`, `ε = τ = 1/10`, `D = 1` | none |
| A6, A7 | `MALocal.lean:902` | A6 at `baEnd_locSCL_three`; A7 at `S0`, `d = 3` | `∀ d, BAEnd_locSCL d` (`d > 3` open, Jun decision B, §316) |
| A1 helpers | `MALocal.lean:910` | `sz0`, `flow_sz0`, `κ = 1/2`, `n = 0` | none |
No `N = 0`, empty index, collapsed window or `False` premise: the end domain at the instance's `κ_*, ε` is nonempty at every `n`
(`MAPins.lean:241`, `MALocal.lean:873`), and `Admissible` is discharged by the merged `S0_adm`.

## 4. Build, axioms, scope
```
$ lake build RBM3D.BA.MAPins RBM3D.BA.MALocal 2>&1 | grep -E "error|Build completed"; echo exit=$?
Build completed successfully (4357 jobs).
exit=0
$ grep -E "^warning: RBM3D/BA/(MAPins|MALocal)" build.log | grep -v "exceeds the 100"
warning: RBM3D/BA/MALocal.lean:16:0: The module doc-string for a file should be the first command after the imports.
(8 further warnings in the two files: line length only)
$ lake env lean aud.lean | grep "depends on axioms"   (condensed: name → axioms)
UNLocAvgBA_iff_at, UNTrLocalBARow_iff_at, UNTrLocalInitBARow'_iff_at   [propext, Classical.choice, Quot.sound]
baLocSCFixed_of_ML, baMANetLoc, baEnd_locSCL, baEnd_locSCL_three        [propext, Classical.choice, Quot.sound]
unLocAvgBAAt_of_locSCL, UNLocAvgBA_of_BAEnd_locSCL, unLocAvgBAAt_of_ML   [propext, Classical.choice, Quot.sound]
MALocal_bulk_abs_le, MALocal_im_I_ge, MALocal_G_sub_M, MALocal_avg_sub_m, MALocal_STWB_le, MALocal_Bctl_le  [propext, Classical.choice, Quot.sound]
$ lake build 2>&1 | grep -E "^exit=|Build completed|^error|axiom audit:|^registry" | cut -c1-110   (full library, extra check)
info: RBM3D.lean:650:0: axiom audit: 15465 theorems, 4750 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
registry: 2 borrowed + 119 owed + 141 structural + 7 refuted + 19 superseded; 161 registered premise(s) carry
Build completed successfully (4420 jobs).
exit=0
$ git diff --name-status main...t/T2514
M	RBM3D.lean
A	RBM3D/BA/MALocal.lean
A	RBM3D/BA/MAPins.lean
M	RBM3D/Test/Axioms.lean
$ git diff main...t/T2514 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep -E "^[-+][^-+]" | cut -c1-150
+import RBM3D.BA.MAPins
+import RBM3D.BA.MALocal
-   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`); `UNMLOutBA` left this list (BA: T2504)
-   `RBM.Univ.UNLocAvgBA, -- bulk universality, block Anderson (T2241, BA-C1b: owed; owner BA-M1, `(G_bound_ave)` from `BAEnd_locSC`)
+   -- T2241 (BA-C1b, DECISIONS §20): the UN-side block Anderson pins (`RBM3D/BA/UNPins.lean`); `UNMLOutBA` left this list (BA: T2504); `UNL
-   `RBM.Univ.UNLocAvgk, -- bulk universality pin, model-generic (T2187, UN-01b): structural as `UNTrLocal` (supervisor 0853 Q2 (d), (e)). Band
+   `RBM.Univ.UNLocAvgk, -- bulk universality pin, model-generic (T2187, UN-01b): structural as `UNTrLocal` (supervisor 0853 Q2 (d), (e)). Band
$ ... | grep -E "^\+.*UNLocAvgk" | sed -E 's/.*(BA instance.*)/\1/'
BA instance: `UNLocAvgBA` from `∀ d, BAEnd_locSCL d` by `UNLocAvgBA_of_BAEnd_locSCL` (T2514a; per `d` `unLocAvgBAAt_of_ML`); `d > 3` out of scope: Jun decision B (§316)
```
- Touched files = row a's sole writable files (`MAPins`, `MALocal`, the `RBM3D.lean` import lines, the registry lines named by the ticket).
  The imports are added after the last `import` line; `#assert_rbm_axioms` passes. Owed count 120 → 119 (`UNLocAvgBA` removed), 0 new premises.
- No merged declaration is edited. `open private` is used for `Main/ZNet` (`znet_*`, allowed by Decision (6)) and for `BA/FlowPins` (`FlowPins_eig_le`; see O2).
- Sizes: `MAPins` 279 (stop 350), `MALocal` 927 (stop 1,300). No public def in `MALocal` (X1-C4); public helpers carry the `MALocal_` prefix (§3 (E)).

## 5. Paper deltas
- The targets are the probe/check texts (§1). Their differences from `MR:locSC` (`1_2:386-393`, BA bullet `1_2:651-653`) are covered by
  D689 (T2449a-c): (a) the explicit form `W^τ`, `N^{-D}` with law `seqP (sz.withLam 0)`; (c) `|x-y|` read as `distB`. The ρ-bulk end domain in place of
  `|E| ≤ e_λ - κ` is DECISIONS §51, already used in D689. The two events `(G_bound)`, `(G_bound_ave)` are stated as two `≤ N^{-D}` bounds, not one intersection
  with probability `≥ 1 - N^{-D}`. This is the probe text: equivalent after `D → D + 1` and covered by D689 (a).
- P4-P6 and A6-A8 are Lean readings of merged pins (`Iff.rfl`, plus the exact identity `calB 0 = Bctl` from `calB_zero_eq_Bctl`); they make no new paper-statement difference.
- I agree with the prove report (d): no new candidate is needed.

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. The ticket's "no new mathematics except F5" is exceeded in one place. Two new public facts of `(self_m)` are proved
  and used only inside the proof: `MALocal_bulk_abs_le` (ρ-bulk ⊂ `|x| ≤ 2 + 2d|g|`) and `MALocal_im_I_ge` (`Im m(i) ≥ (2+2d|g|)^{-2}`).
  The prover disclosed both in (a) rows 6 and 10. They are standard-axiom theorems, have an instance at `MALocal.lean:918`, and are not targets.
- O2. `open private FlowPins_eig_le from RBM3D.BA.FlowPins`: Decision (6) names only `Main/*`. No merged file changes, so the dispatcher only needs to note it.
- O3. The ticket's F1 is out of date (`unMLOutBA_three` is merged), so `UNMLOutBA 3` is no binder in `MALocal`. The `MAPins.lean:228` example keeps `hML : UNMLOutBA 3`
  because `MAPins` does not import `MainIndTermBA`; the probe text does the same.
- O4. Lint: 8 line-length warnings and 1 module-docstring-position warning (`MALocal.lean:16`). `MAPins` is 279 lines, above the ticket's high estimate of 265 and below the stop line of 350.
- O5. Prove report (a) rows 7, 8 and 10 had inexact constants. (a′) corrects them, and the Lean (`hCN` threshold, `4R + 2`, `BAdom κ_f` sections) has the corrected values.

## Verdicts
| target | verdict |
|---|---|
| P1 `BAGz`…`BAdecolBad`; P2 `BAEnd_locSCL`, `BAEnd_QDiffL`, `BAEnd_decolL`, `BAThm27L`; P3 seven step pins | PASS |
| P4 `UNLocAvgBAAt`; P5 `UNTrLocalBAAt`, `UNTrLocalInitBAAt'`; P6 three `Iff.rfl` | PASS |
| A1 (private / `MALocal_` helpers) | PASS |
| A2 `baLocSCFixed_of_ML` | PASS |
| A3 `baMANetLoc` | PASS |
| A4 `baEnd_locSCL` | PASS |
| A5 `baEnd_locSCL_three` (unconditional) | PASS |
| A6 `unLocAvgBAAt_of_locSCL`; A7 `UNLocAvgBA_of_BAEnd_locSCL`; A8 `unLocAvgBAAt_of_ML` | PASS |
| A9 instances | PASS |

**Overall: PASS.** No dispatcher sign-off is needed for the merge. O1 and O2 are for the dispatcher's notes only.
