Auditor model: claude-opus-5-5
# T2470 audit (round 1) — BA-L L3d2a `BAMomentGen` (`lem:LW_moment` at BA)
Written Mon Oct 12 21:12:08 UTC 2026. Audit worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2470-audit1`, detached at `t/T2470` head `1010ab31` (base `e9d820fc`). Scratch `$S` = `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2470`.

## 1. Statements against the pins (check file `docs/tickets/checks/T2470-check.lean`)
`$S/stmtcheck.lean` = `import RBM3D.Graph.BAMomentGenB` + Part 2 of the check file verbatim + the identity lines below + `#print axioms`.
```lean
example : T2470_LWfgBand := fun {d} sz E n t ω x y => LWfg_bandFM sz E n t ω x y
example : T2470_LWMomentG = @LWMomentG := rfl
example : T2470_MomentBand := LWMoment_iff_bandPin
example : T2470_BALWMoment = BALWMoment := rfl
example : T2470_LocRegXHolds := ba_localregularX_holds
example : T2470_MomentOfAnp = BALWMomentOfAnp := rfl
example : T2470_Moment := @baLWMoment_of_anp
example : T2470_PathBinder = (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapePath sh BAFrameStepTN) := rfl
-- target 1 (b), the check file's (non-binding) shape, as the type of LWfg_baFMz
example : (∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    (t : ℂ) * LWfg (baFMz sz z) n t ω x y = fxyVal (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAExp14a_slc sz n ω)).toLData x y) := @LWfg_baFMz
```
```
$ cd $WT && lake env lean $S/stmtcheck.lean > $S/stmt.out 2>&1; echo EXIT $?; grep -c error $S/stmt.out
EXIT 0
0
$ lake env lean docs/tickets/checks/T2470-check.lean   (original check file, on the branch)
EXIT 0
0
```
The `rfl` lines for `LWMomentG`, `BALWMoment`, `BALWMomentOfAnp` make the defs definitionally the pinned Props (same binders, `∃ c` before `𝔠`,
`p ∈ 2ℕ`, `LWAssmgL` window/class, `(η⁻¹ Φ(0) Φ(c|a−b|))^p` with `zdistInf` on blocks, as `7_8:72-77`). The theorems `LWfg_bandFM`,
`LWMoment_iff_bandPin`, `ba_localregularX_holds`, `baLWMoment_of_anp` elaborate at exactly the pinned types. Decision (i):
```
$ git log --oneline main | grep -c 'T2469: merge'        -> 0      (T2469.state: proving, updated Mon Oct 12 21:10:21 UTC 2026)
$ git merge-base --is-ancestor 03109267 t/T2470          -> 03109267 (T2466 merge) is ancestor of t/T2470
```
So `T2470_Moment` (path binder first) is the right form (decision (i) "not merged"); T2466 imported (decision (ii) "merged").
Target 3 discharges `T2448_Binder` with `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` (A:155-157); its statement has no binder (O2R-C3).
Target 4 is a **conditional adapter** (path binder; `BAAnpAuxG d` as statement-def antecedent), exactly as the ticket pins it; not the unconditional
BA `lem:LW_moment` (CLAUDE.md §5.6); the prove report says so (b, narrative).

## 2. Hidden hypotheses, vacuity, cycles
Meta script `$S/meta.lean` (public declarations of the two modules, the hypotheses they carry, the transitive closure of target 4):
```
public decls: 85; without stem BAMomentGen_: [RBM.BA.BALWMoment, RBM.BA.BALWMomentOfAnp, RBM.BA.LWMomentG, RBM.BA.LWMoment_iff_bandPin,
 RBM.BA.LWfg, RBM.BA.LWfg_baFMz, RBM.BA.LWfg_bandFM, RBM.BA.baLWMoment_of_anp, RBM.BA.ba_localregularX_holds,
 RBM.Graph.BAGraph.scalingSize.congr_simp, RBM.Graph.BAGraph.sizeConst.congr_simp]
public decls with flagged hypotheses: [RBM.BA.baLWMoment_of_anp : hyp mentions RBM.Graph.BAShapePath,
 RBM.BA.BAMomentGen_prec_scale : hyp mentions RBM.BA.STInitialGT2gL, ... (17 BAMomentGen_* helpers: STInitialGT2gL),
 RBM.BA.BAMomentGen_prec_far_r : hyp mentions RBM.Graph.PGraph.LocReg345,
 RBM.BA.BAMomentGen_prec_far : hyp mentions RBM.Graph.PGraph.LocReg345, ...]
closure of baLWMoment_of_anp: 65814 constants; from LWMomentExp/LWMomentExpA/LWProv/AuxGraphRooted/BAZetaExp: []
axiomInfo in closure: [Quot.sound, Classical.choice, propext]
```
(flag list: `LocStd`, `LocReg345`, `BAAnpAuxG`, `LWAssmgL`, `LWLoop2gL`, `STInitialGT2gL`, `LWXigL`, `BAShapePath`.)
- No new `structure`/`inductive`/`class`; `BAAnpAuxG`, `LWAssmgL`, `LWLoop2gL` occur in no public theorem hypothesis (only inside
  `LWMomentG`/`BALWMomentOfAnp`/the instance); `STInitialGT2gL` (registered owed) appears in helper hypotheses unfolded from `LWAssmgL`.
- The only unproved premises of target 4 are the ticket's: the path binder (T2469) and `BAAnpAuxG d` (L3d1). External-limit check: (a) row 9 /
  "External hypotheses" of the prove report (exponent compatibility of `STInitialGT2gL`, `LWLoop2gL` at `t=1/2`; `BAAnpAuxG` rate equals the
  merged band `lwAnp_holds`). No cycle: the route reads no `LWMomentExp`/`LWProv`/`AuxGraphRooted`/`BAZetaExp` constant (closure above).
- Non-vacuity of the engine lists (preflight F5) is proved: `BAMomentGen_lists_nonempty : BALocRegConcl 2 c K0 3 D outs errs → outs ++ errs ≠ []`.

## 3. Compiled nonempty instances
| target | instance | data | left as hypotheses |
|---|---|---|---|
| 1 (a), 1 (b) | A:1542, A:1537 | `sz0`, `zSeq`, `n = 0` (`L=4, W=32`), `t = 1/2`, `x = 0`, `y = 1` | none |
| 2 | A:1528 | `(LWMoment_iff_bandPin 3).1 (lwMoment_holds 3)` | none |
| 3 | A:1532, B:840 | `p=2, c=1/4, K0=2, d=3, D=10`; B:840 adds `outs ++ errs ≠ []` | none |
| 4 | B:471-482 | `d=3`, `p=2`, `sz0`, `zSeq`, `flow_sz0` (`κ=1/2, ε=𝔡=1/10, 𝔠=1/6`), `t ≡ 1/2` (`half_lt_t0`), `ε₀=1/10`, `Ψ=Φ≡W^{-1/2}`, `C₁=C₂=2, C₃=1, Cc≡1`; window, class, `(eq:Psi)` discharged (`BAMomentGen_Ψ0_window`, `BAMomentGen_psiAll0`) | path binder, `BAAnpAuxG 3`, `STInitialGT2gL`, `LWLoop2gL` (all allowed by ticket 5 (iii)) |
All four compile in the module build below. No `N = 0`, empty index, collapsed window or `False` premise.

## 4. Build, axioms, hygiene, diff
```
$ lake build RBM3D.Graph.BAMomentGen RBM3D.Graph.BAMomentGenB   (audit worktree)
Build completed successfully (4061 jobs).   EXIT 0   (errors: 0; warnings are linter only)
$ lake build   (whole library, audit worktree at t/T2470; runs #assert_rbm_axioms and the premise scan)
non-vacuity certificates: 0 of 106 premises in the two ledgers; ...
Build completed successfully (4305 jobs).   EXIT 0
$ grep "depends on axioms" $S/stmt.out
'RBM.BA.LWfg_bandFM' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWfg_baFMz' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.LWMoment_iff_bandPin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_localregularX_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.baLWMoment_of_anp' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAMomentGen_lists_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -nE '\b(sorry|admit|native_decide)\b|^\s*axiom\b|^(inductive|structure|class)\b' A B ; echo $?
1
$ git diff --name-only main...t/T2470
RBM3D.lean
RBM3D/Graph/BAMomentGen.lean
RBM3D/Graph/BAMomentGenB.lean
$ git diff main...t/T2470 -- RBM3D.lean   -> +import RBM3D.Graph.BAMomentGen / +import RBM3D.Graph.BAMomentGenB after the last import line
$ wc -l A B  ->  1549 / 847   (stop line 2,000 per file)
$ git diff main...t/T2470 -- RBM3D/Test | wc -l  -> 0
```
All touched files are sole writable files; no merged file edited; `Test/Axioms.lean` unchanged.

## 5. Paper deltas
Lean vs paper `lem:LW_moment` (`7_8:72-77`, BA sketch `B:408-416`): `c` fixed to `1` (uniform in `p`; paper: `c` depends on `p`; stronger,
the `∃ c` placement is as in the merged band pin `LWMoment`); `Ψ_t` replaced by the class `Φ` inside `LWAssmgL` (inherited from the merged band
pin). The BA proof being a sketch is already D615. The two antecedents of target 4 are other gates' pins (temporary), not paper differences.
Prove report (d) 2 proposes no new candidate; I find no statement difference without coverage.

## 6. Observations (no effect on statement, instance, build, axioms, or paper-delta coverage)
- O1. Ticket C1 asks that helpers with a `LocStd`/`LocReg345` hypothesis stay private; `BAMomentGen_prec_far_r` (A:1438) and
  `BAMomentGen_prec_far` (A:1467) are public (stem-prefixed, §3 (E) satisfied) and carry `(BAShadowPG Q).LocReg345 p` in `h15`/`hAnpL`.
  The premise scan passes (producers exist); the dispatcher may ask for `private` in a later touch.
- O2. Route deviations from the ticket's input table (no target change): `baAuxNested_holds`, `baStart_nM_le`, `baClaimSize_E` unused;
  `ρ = (2K+1)(log W)²` (F1); `open private` of three `BASizeClaim`/`BAVocab` helpers (A:48-50).
- O3. Branch base `e9d820fc` predates `c986735f` (T2465 merge) on `main`; `RBM3D.lean` needs a union at merge (hub step 4).

## Verdict
| target | verdict |
|---|---|
| 1 `LWfg`, `LWfg_bandFM`, `LWfg_baFMz` | PASS |
| 2 `LWMomentG`, `LWMoment_iff_bandPin`, `BALWMoment` | PASS |
| 3 `ba_localregularX_holds` | PASS |
| 4 `BALWMomentOfAnp`, `baLWMoment_of_anp` (conditional adapter as pinned: path binder, `BAAnpAuxG`) | PASS |
| 5 instances | PASS |
**T2470: PASS.** No dispatcher sign-off needed.
