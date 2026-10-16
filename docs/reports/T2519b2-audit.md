Auditor model: claude-opus-5-5
# T2519 row b′ (t/T2519b2, head aa49d4d3), audit round 2
Written Fri Oct 16 16:18:34 UTC 2026 (`date -u`). Worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2519b2-audit2` (detached at aa49d4d3). Scope: `git diff 19df37e2...t/T2519b2`; target 7 `gueGrid_twistBA` and its instance `GUETwistBAInst.twist_sz0`. Scratch `<S>` = scratchpad `T2519b2/`; `<S>/mainwt` = a detached scratch worktree of `main` 432301f7 with the two branch files copied in (composition checks only, §3).

**Verdict: PASS (target 7).** Round 1's RETURN (degenerate instance window) is repaired: the instance now uses row a's GUE-phase window. On `main`, its K-bound premise is discharged outright by the merged `Hyp_Kt_detDomBA`, and its PB premise by the merged `gueGrid_pathBoundsBA`, at the same data (§3).

## 1. Statement against the signed pin (`T2519_HoffBA`, b992c2e7:RBM3D/Probe/T2519Pins.lean:79-98)
```
$ git show b992c2e7:RBM3D/Probe/T2519Pins.lean > <S>/probe.lean
$ sed -n 80,98p probe.lean | sed 's/T2519_PathBoundsBA/GUEPathBoundsBA/;s/^ *//;s/ *$//' > pin.txt
$ sed -n 926,944p RBM3D/BA/GUETwistBA2.lean | sed 's/^theorem gueGrid_twistBA (d : ℕ) : //;s/ := by$//;s/^ *//;s/ *$//' > lean.txt
$ diff pin.txt lean.txt && echo "DIFF EMPTY ($(wc -l < pin.txt) lines)"
DIFF EMPTY (      19 lines)
$ diff <(sed -n 56,68p probe.lean | sed 's/T2519_PathBoundsBA/GUEPathBoundsBA/') <(sed -n 42,54p RBM3D/BA/GUEProcBA.lean) && echo PB DIFF EMPTY
PB DIFF EMPTY
$ lake env lean <S>/audit_check.lean   # probe :25 open line, :56-68 and :79-98 copied verbatim into namespace RBM.BA.AuditScratch, then
#   example : ∀ d, T2519_HoffBA d := fun d => gueGrid_twistBA d
#   example : @T2519_PathBoundsBA = @GUEPathBoundsBA := rfl
'RBM.BA.gueGrid_twistBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBAInst.twist_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0   (0 error lines)
```
The repair commit (`git diff ee2e973c aa49d4d3`) touches only `RBM3D/BA/GUETwistBA2.lean` §5, at lines 978-1172. The target text at 926-944 is unchanged.
- The hypotheses are exactly the signed text: `3 ≤ d`; `κ Λ` fixed before the sequences; F1 `4 ≤ n0`; F2 `0 < g n →`; the eventual `g` window; `BAReal` at every `n`; the time window; the K-bound with `∀ ε > 0, ∀ᶠ n` and `2 ≤ |I| ≤ 4`; PB.
- The conclusion is the second `StochDomAt` of `T2517_OneLoopBA`.

Statement: **PASS**.

## 2. Hidden hypotheses, vacuity, cycles
- Every premise is in the signature.
- `GUEPathBoundsBA` is row a's signed `def`: a conjunction of two `StochDomAt`, with no structure fields. `git diff --stat 19df37e2 t/T2519b2 -- RBM3D/BA/GUEProcBA.lean RBM3D/BA/TwistAvg*.lean` is empty (0 lines).
- The internal `Prop` `GUETwistBA_Good` is not in the target. `GUETwistBA_good` discharges it from `hPB`, `hKm` and `hKb`.
- Imports are `GUEProcBA`, `GUEOneLoop`, `TwistAvgA2` and `TwistAvgB` (GUETwistBA2 imports GUETwistBA and TwistAvgB). There is no import of `BA.TwistPins` (Amend 2 item 6), and the new files have no importers, so there is no cycle.
- `open private` from `TwistAvgB` is used as Amend 3 item 3 allows. No `BA/TwistAvg*` file is edited.
- External-limit check of the two open premises: they are other gates' pins, and both are now merged as theorems that apply at the instance data (§3).

Hidden hypotheses and vacuity: **PASS**.

## 3. Compiled nonempty instance
`GUETwistBAInst.twist_sz0` (GUETwistBA2.lean:1152-1172) compiles. Its data:
- `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`);
- the BA flow datum `gI, EI, mI`, with `κ = 1/2` and `Λ = 10`;
- **the GUE-phase window** `1 − t₀ = x_n = λ_n²/(4L_n³)`, `t₀ − t₁ = x_n/(2N_n)` (lines 1027-1030, identical to row a's `ix/it0/it1`, main `GUEHypABA.lean:661-663`);
- `n₀ = 4`, and `KtI` from `gueK_existsBA` (loops of length up to 16).

It discharges `Tendsto size`, `4 ≤ n₀`, the `g` window, `BAReal`, `0 ≤ t₁ ≤ t₀ < 1` (private `_t1_nonneg/_t10/_t0_lt`, now real proofs rather than `norm_num` on constants) and `Kt = m` on 1-loops. `hKb` and `hPB` stay open. The window is not collapsed: `t₀ − t₁ = x_n/(2N_n) > 0` (`_x_pos`) and `t₀ < 1`. It is not astronomically tuned: `N_0 = 2^21`, and the checks hold for every `n`.

Round 1's defect: `hKb` was false at the old window. The audit checks the open premises on `main`, where rows a and c are merged.
```
$ git worktree add --detach <S>/mainwt main   # 432301f7; cache cloned; cp the two branch files into RBM3D/BA/
$ (cd <S>/mainwt && lake build RBM3D.BA.GUETwistBA2 RBM3D.BA.GUEHypABA RBM3D.BA.GUEPathBoundsBA)
✔ [4121/4122] Built RBM3D.BA.GUETwistBA (16s)
✔ [4122/4122] Built RBM3D.BA.GUETwistBA2 (41s)
Build completed successfully (4122 jobs).
Build completed successfully (4011 jobs).
$ lake env lean <S>/full_check.lean    # in <S>/mainwt; key lines:
# open private GUETwistBAInst_h730 GUETwistBAInst_hell GUETwistBAInst_KtI_spec GUETwistBAInst_t1_nonneg
#   GUETwistBAInst_t10 GUETwistBAInst_t0_lt from RBM3D.BA.GUETwistBA2
# open private j_hscale j_hell j_hell1 from RBM3D.BA.GUEPathBoundsBA
# theorem audit_hKb : <hKb of twist_sz0, verbatim> := by
#   intro ε hε
#   have h := Hyp_Kt_detDomBA (d := 3) le_rfl sz0 (κ := 1/2) (Λ := (1/10)⁻¹) (τU := 1/20) _ _ _ 4 real_I
#     (BAflow_lam0_window …) GUETwistBAInst_t1_nonneg GUETwistBAInst_t10 GUETwistBAInst_t0_lt
#     (tendsto_natCast_atTop_iff.mp sz0_tendsto) GUETwistBAInst_h730 GUETwistBAInst_hell KtI
#     (fun n _ I => (GUETwistBAInst_KtI_spec n).1 I) (fun n _ s hs I hI h1 h2 => (GUETwistBAInst_KtI_spec n).2 …) ε hε
#   filter_upwards [h] with n hn s hs I hI h2 h4 using hn s hs I hI h2 (by omega)
# theorem audit_hPB (hLK : STLKgL (baFM sz0 gI EI) (Sizes.seqP (sz0.withLam 0)) t1I)
#     (hLoc : STLocalEntrygL (baFM sz0 gI EI) (Sizes.seqP (sz0.withLam 0)) t1I) :
#     GUEPathBoundsBA sz0 gI EI t1I t0I mI (gueGridK sz0 4) 4 KtI :=
#   gueGrid_pathBoundsBA sz0 le_rfl (𝔠 := 1/6) (𝔡 := 1/10) (κ := 1/2) (τU := 1/20) flow_sz0.1 _ _ real_I (BAflow_lam0_window …)
#     … GUETwistBAInst_h730 j_hscale (Eventually.of_forall j_hell) (Eventually.of_forall j_hell1) GUETwistBAInst_hell KtI … hLK hLoc
# example (hLK …) (hLoc …) := twist_sz0 audit_hKb (audit_hPB hLK hLoc)
'RBM.BA.GUETwistBAInst.audit_hKb' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBAInst.audit_hPB' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0   (0 error lines)
```
- **`hKb`** is the conclusion of the merged, fully deterministic `Hyp_Kt_detDomBA` (main `BA/GUEHypABA.lean:268-283`), cut from `|I| ≤ 2·4` to `≤ 4` by `omega`. Its premises `h730` and `hell` are exactly the branch's private checks `GUETwistBAInst_h730` and `GUETwistBAInst_hell` (lines 1091, 1115). `hKinit` and `hK` come from `KtI`'s clauses.
- **`hPB`** is the conclusion of the merged `gueGrid_pathBoundsBA` (main `BA/GUEPathBoundsBA.lean:616-634`) at the same `KtI`. The only inputs left open are row c's step-0 inputs `hLK` and `hLoc`: the V3 pin `UNMLOutBA`, another gate, which row c's own instance also leaves open (main `GUEPathBoundsBA.lean:765-772`).
- So at this data every deterministic premise of the chain holds, and no premise is false.

The branch keeps `hKb` as a hypothesis because its base, 19df37e2, has no `GUEHypABA`. Round 1's Required item 2 ("otherwise keep it as a hypothesis together with those checks") allows this.

Instance: **PASS**.

## 4. Build, axioms, hygiene, diff scope
```
$ lake build RBM3D.BA.GUETwistBA RBM3D.BA.GUETwistBA2 ; echo exit $?      # audit worktree, aa49d4d3
✔ [4113/4114] Built RBM3D.BA.GUETwistBA (15s)
✔ [4114/4114] Built RBM3D.BA.GUETwistBA2 (40s)
Build completed successfully (4114 jobs).
exit 0
$ grep 'warning' build.txt | grep -c GUETwistBA
0
$ grep -nE 'sorry|admit|native_decide|^\s*axiom ' RBM3D/BA/GUETwistBA*.lean | wc -l
       0
$ git diff --name-only 19df37e2...t/T2519b2
RBM3D.lean
RBM3D/BA/GUETwistBA.lean
RBM3D/BA/GUETwistBA2.lean
$ git diff 19df37e2...t/T2519b2 -- RBM3D.lean | grep '^[+-][^+-]'
+import RBM3D.BA.GUETwistBA
+import RBM3D.BA.GUETwistBA2
$ tail -1 RBM3D.lean
#assert_rbm_axioms
$ grep -n 'maxHeartbeats' RBM3D/BA/GUETwistBA*.lean
RBM3D/BA/GUETwistBA2.lean:358:set_option maxHeartbeats 1600000 in
$ wc -l RBM3D/BA/GUETwistBA.lean RBM3D/BA/GUETwistBA2.lean
    1799 RBM3D/BA/GUETwistBA.lean
    1178 RBM3D/BA/GUETwistBA2.lean
    2977 total
```
- The axioms of the target and of the instance are the standard three (§1).
- Only row b′'s sole writable files are in the diff, and no frozen signature is touched.
- Both files are under 2,000 lines.
- Merge compatibility: both files also build on `main` 432301f7 (§3), with no name clash against main's `GUEHypABA` or `GUEPathBoundsBA` (`full_check.lean` imports all three).

Build: **PASS**.

## 5. Paper deltas
The prove report (d) proposes four candidates:
- `T2519ba`: the grid form of TL1/T.7 with the `M`-weighted block trace;
- `T2519bb`: the moment order carries the grid's union exponent;
- `T2519bc`: the `localLaw` split at `Λ_j = N^{-τ}`;
- `T2519bd`: F1, F2 and the eventual window.

The repair changes no statement, so it needs no new delta. Coverage: **PASS**.

## 6. Observations (no verdict effect)
1. **Landing line exceeded.** The landed sum is 2,977 against row b′'s 2,719 (+258; the prove report's repair section states the same). Under Amend 2 item 5 the row still goes to audit and merge, but no importing row starts until the dispatcher answers the short REQ.
2. **The instance could be tightened after merge.** With rows a and c merged, `twist_sz0` can drop `hKb` outright: `audit_hKb` above is a compiled proof of it. A primed instance would then have `hLK` and `hLoc` as its only open premises. This is the dispatcher's choice (prove report (d) 3).
3. **Stale lines in the prove report.** (b2):74 still describes the old window `[17/20, 9/10]`. The repair section (:265-300) explicitly supersedes it, so no statement or instance claim is affected.
4. **Scratch worktree left in place.** The audit's scratch worktree `<S>/mainwt` is still registered with git; it contains only copied files and no commits.
