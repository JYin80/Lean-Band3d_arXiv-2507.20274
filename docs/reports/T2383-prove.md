Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 12:06:18 UTC 2026

Setting: `RBM3D/Induction/LoopGenN.lean` (720 lines) and `Induction/HierarchyN.lean` (253 lines) on main `2192dea` (worktree `RBM3D-wt/T2383` is at `2192dea`, `LoopGenN.lean` identical to main). Probe text: `t/T2379:RBM3D/Probe/T2379Pins.lean:108-392` (`git show`; the T2379 prove report B0 records `lake build RBM3D.Probe.T2379Pins` = "Build completed successfully (3775 jobs)", standard axioms).

### (i) Exponent table (the constants the targets depend on)

| quantity | value | constraint | slack |
|---|---|---|---|
| g, LoopGenN block `:55-622` (T2379-prove B3, `git diff --no-index --numstat`) | 136 added / 568 = 0.2394 | tripwire g <= 0.5 (ticket 5, sup 1155 C6) | 0.2606 (= 148 lines of 568) |
| f_sem, LoopGenN (lines moved into the band instance) | 0 (band instance = `recovers_loopGenN`, 3 lines, probe 369-371) | f_sem <= 0.30 | 0.30 |
| band-object lines, two files (design §4 row T5s1) | 804 = 568 + 236 | denominator of the two-file g | - |
| two-file g if HierarchyN.lean takes x edited lines | (136 + x)/804 | <= 0.5 iff x <= 266 | HierarchyN.lean has 253 lines in all: x = 253 gives 0.484 < 0.5, so the g tripwire cannot fire from edits of existing HierarchyN lines (new lines add to x) |
| design edit figure for T5s1 | 202 (design §4 `:149`); 202 - 136 = 66 for HierarchyN.lean | model value (design §4 formula), not measured for HierarchyN | x = 66 gives 0.251 |
| band-token lines (script below) | LoopGenN block 74 of 568; HierarchyN body 68 of 224 | rho = 1.81 (T2379 B3): x ~ 1.81 * 68 = 123 gives g_two = 0.32 | < 0.5 |
| stop line (ticket) | 800 net diff lines of the two files | net diff <= 800 | G-edit 136 + 99 removed = 235 touched in LoopGenN.lean |
| generic hypotheses of `loopGenNOf` (probe 302-306) | `3 <= L`, `0 < m.im`, `u < 1`, `M.IsHermitian`; `g : R` arbitrary | `SB_mulVec_one` needs only `3 <= L` (`Defs/Block.lean:113`, `g` free); `ztOf_im`: `Im ztOf m E u = (1-u) Im m` (`Loop/GLoopFlow.lean:64`) so `Im z != 0` for `u < 1` | no `\|E\| < 2`, no window |
| band recovery | `m = mE E`: `zt_eq_ztOf` is `rfl` (`GLoopFlow.lean:60`); `PropSpin (mE E) s = mSigma E s` by `if`-unfolding; `0 < Im mE E` iff `\|E\| < 2` (`mE_im_pos`, `Defs/Semicircle.lean:56`) | G1 | exact |
| BA data | `d = 3`, `g = 0`, `m = BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n`, `L = sz0.L n = 4(n+1)` | `0 < Im m` is `BAmF_sz0_im_pos` (`BA/FlowPins.lean:1422`, a theorem on main) | no external hypothesis |

Public declarations and their users outside the two files (grep over `RBM3D/` and `docs/tickets/checks/`):

| declaration (file) | users |
|---|---|
| `loopGenN`, `stLoopGenNForm_holds`, `hierarchyN_holds`, `LoopGenN_check_stLoopGenNForm_sz0`, `LoopGenN_check_hierarchyN_sz0` (LoopGenN.lean) | `hierarchyN_holds`: code uses `Induction/ExpHier.lean:457` and `GridDriftN.lean:872` (the other hits `ExpHier:35,448`, `Step6Pins:209`, `GridDriftN:38,51` are comments, read by `sed -n`); `loopGenN`: check files only (T2111, T2305); `stLoopGenNForm_holds`: none in `RBM3D/`; the two checks: none |
| `STLoopGenNForm`, `HierarchyN`, `hierarchyN_of_loopGenN`, `hierarchyN_two`, `loopGenNForm_two_of_loopGenN2`, `HierarchyN_check_sz0`, `HierarchyN_check_two_sz0`, `HierarchyN_check_loopGenNForm_two_sz0` (HierarchyN.lean) | `HierarchyN`, `hierarchyN_two`, `STLoopGenNForm`: only comment/docstring hits (`ExpHier.lean:36,363,446-447`, `GridDriftN.lean:723`, `HierAlgebra.lean:727-728`), no code use outside the two files; the rest: none in `RBM3D/` |

Rebuild cone (script below): modules that import `LoopGenN` or `HierarchyN` transitively, including the two: 51 (matches design §4); direct importers: `LoopGenN` <- `ExpHier`, `GridDriftN`; `HierarchyN` <- `LoopGenN`. None of the 20 certificate-named modules of design §6 is in the cone. The BA instance needs `import RBM3D.BA.FlowPins` in `LoopGenN.lean`: `FlowPins` (direct imports `BA.MFixedPoint`, `Induction.Defs`, `Induction.Step2Defs`, `Loop.KLTree`) has 64 transitive imports, none of them `LoopGenN`/`HierarchyN` (no cycle); 5 of them are not yet upstream of `LoopGenN`.

### (ii) One concrete nondegenerate instance (every hypothesis of Targets 1, 3, 4 at once)

Band: `d = 3, L = 3, W = 2, g = 1/2, E = 1/2, u = 1/2`, `m = mE (1/2)`, loop `(+,-,+)`, `a = (0,1,2)` (length 3), `M` Hermitian non-scalar (`LoopGenN_M0`, merged, `LoopGenN.lean:638-646`). BA: `sz0`, `n = 0`: `L = 4, W = 32, lam = 1/64`, `g = 0`, `u = 1/2`, `M = 1`.
```
$ python3 -I .../scratchpad/T2383/inst.py          (pure arithmetic, no Lean)
band: |E|<2: True  3<=L: True  u<1: True  0<Im m: True  Im m=0.968246
band: m^2+E m+1 = True  (m = mE E is the semicircle root)
band: ztOf m E u = 0.375000+0.484123i, Im = (1-u) Im m = 0.484123 > 0: True
band: Idx 3 3 2 sites (W L)^d = 216 ; W^d = 8 ; loop (+,-,+), a=(0,1,2): length 3
band: Im mE E>0 iff |E|<2 on grid [-3,3] step .01 (4-E^2>0): True
BA: sz0 n=0: L=4 W=32 lam=1/64 size=(W L)^3=2097152; g=0; 3<=L: True; u=1/2<1
BA: SB kernel at g=0 is 1_{x=0} (Defs/Block.lean:36): column sums 1 for any 3<=L, g (SB_mulVec_one, Defs/Block.lean:113)
g_LoopGenN =136/568 = 0.2394 ; thresholds g<=0.5, f_sem<=0.30
```
External hypothesis: none in Targets 1, 3, 4 (all hypotheses are deterministic). The BA value `0 < Im m` is not computed by script (`m` is `mS/sqrt t0` with `mS` defined by the subordination fixed point, `BA/MFixedPoint.lean:865`); it is the merged theorem `BAmF_sz0_im_pos`. The kernel at `g = 0`: `sbKernel d L 0 x = 1` at `x = 0` (`(1+0)^{-1}`), and `0` at `zdistD = 1` (factor `g^2 = 0`), else `0` (`Defs/Block.lean:36-40`).

Script for the counts above (pure Python over the repository text; no Lean written):
```
$ python3 -I - <<'EOF' ... (token regex zt|spectralMSign|mSigma|spectralZ|spectralM_im_pos|hE|genMat|mE|STmsig|sz.ST*|STLIM|STKloop|KLK|sz0; import-cone BFS)
LoopGenN block 55-622 lines: 568
  band-token lines: 74
HierarchyN total lines: 254 (python split) ; lines 31-253 (after header): 224
  band-token lines: 68
cone size (incl. the two roots, all RBM3D modules): 51
certificate-named modules in cone: []
direct importers of LoopGenN: ['RBM3D.Induction.ExpHier', 'RBM3D.Induction.GridDriftN']
direct importers of HierarchyN: ['RBM3D.Induction.LoopGenN']
BA.FlowPins transitive imports: 64 ; contain LoopGenN/HierarchyN: False False
LoopGenN transitive imports: 73 ; FlowPins already upstream of LoopGenN: False
x_max for g<=0.5: 266.0 ; (136+253)/804 = 0.484
```
(The 74 band-token lines here against 75 in T2379 B3 is the token-list difference; the 136/568 figure is T2379's `numstat`, not re-derived here: reproducing it needs the generic block as a file, which this stage may not write.)

### Statements, bridge and the HierarchyN question (mathematics only)

- **Targets 1, 3, 4, 5 (LoopGenN).** Generic `loopGenNOf d L W g m E hL hm u hu1 M hM sigma a` (probe 302-364): `genMatOf ... = W^d Sum_{k<l} Sum_{x,y} L(cutL_x) S L(cutR_y) + W^d Sum_k Sum_{x,y} (L_{(s_k),(x)} - PropSpin m s_k) S L(cut_y)` along `z_u = ztOf m E u = E + (1-u) m`, with `genMatOf` the generic-`m` copy of `genMat` (`Path/OneStep.lean:68`; `genMat_eq_genMatOf` is `rfl`). The derivative step needs `d_u ztOf m E u = -m` (probe 118) and `Im z_u = (1-u) Im m != 0`; every other step is the merged band-free algebra. Bridge: `loopGenN d L W g E hL hE u hu1 M hM sigma a := loopGenNOf ... (mE E) ... (mE_im_pos hE) ...` (probe 369-371); `stLoopGenNForm_holds`, `hierarchyN_holds` follow unchanged. Names `genMatOf`, `loopGenNOf`, `recovers_loopGenN`, `genMat_eq_genMatOf` are absent from `RBM3D/` (grep: no match for any of the four, `def|theorem` form). Tripwire: g = 0.2394, f_sem = 0 (both T2379-measured; the HierarchyN part can only raise g to <= 0.484 on existing lines, row 4 of (i)).
- **Target 2 (HierarchyN.lean): the generic hierarchy cannot be stated or proved inside the two sole files.** Every band-specific declaration there reads, in its statement, objects defined outside them: `HierarchyN` and `hierarchyN_of_loopGenN` read `sz.STKloop` (`Induction/Defs.lean:64`, via `KLK`, `Loop/KLTree.lean:145`, the star-tree closed form in `E`), `sz.STLKIM`, `sz.STksimLKM`, `sz.STelklkM`, `sz.STegtM` (`Induction/Step2Defs.lean:713-750`, `STLKIM = STLIM - KLK E`), `sz.STllPairN` (`Induction/HierAlgebra.lean:693`); the proof of `hierarchyN_of_loopGenN` is `loopDrift_sub_K_deriv_n` (`HierAlgebra.lean:729`, band: `sz`, `E`, `|E| < 2`, `mSigma E`). A generic `HierarchyN` over `m` therefore needs a generic `KLK` (the K-tree closed form, class (t) of T2379 design §1.3) and a generic `loopDrift_sub_K_deriv_n`; both belong to row T5s2 (`HierAlgebra`) and the K rows, which are other tickets, and the probe (108-392) contains no HierarchyN text (design §4 `:169`: "content = probe 118-364 plus the band corollary"). `STLoopGenNForm` alone does not read `KLK`, but it reads `sz.STllPairN`/`sz.STegtM` (HierAlgebra/Step2Defs), so a generic form of it would be a private twin of those definitions plus a bridge. `hierarchyN_two` and `loopGenNForm_two_of_loopGenN2` read `HierarchyN2`/`LoopGenN2` (`Path/DriftAlgebra.lean`, band). The two band-frozen G1 items for this file, `hierarchyN_holds` and `stLoopGenNForm_holds`, are proved in `LoopGenN.lean` from the generic theorem and need no HierarchyN.lean edit.

### Verdict per target

| target | verdict | reason |
|---|---|---|
| 1 `LoopGenN.lean` generic block + band corollaries | PASS | hypotheses `3 <= L, 0 < m.im, u < 1` hold at the instance (ii); probe compiled; bridge `m = mE E` is `rfl` plus `mE_im_pos` |
| 2 `HierarchyN.lean` generic restatement | BLOCKED | the generic `HierarchyN` needs a generic `KLK`/`ST*` vocabulary and a generic `loopDrift_sub_K_deriv_n` (HierAlgebra, T5s2), outside the sole writable files; the ticket does not say whether Target 2 means (A) leave the HierarchyN.lean declarations band-only and unchanged (0 edit lines, 0 moved; their G1 check then holds trivially) or (B) add private generic twins of `STllPairN`/`STegtM`/`STLoopGenNForm` only, or (C) wait for T5s2. Question for the dispatcher: which of (A), (B), (C) |
| 3 G1 checks | PASS | `example : <old statement> := <old name>` for the 13 declarations of the table (i); with (A) the 8 HierarchyN.lean ones are unchanged text |
| 4 BA instance (`g = 0`, `m = BAmF`, `sz0`, `n = 0`) | PASS | all hypotheses discharged by merged theorems (`BAmF_sz0_im_pos`, `sz0.three_le_L`); requires `import RBM3D.BA.FlowPins` in `LoopGenN.lean` (acyclic, checked above); names used exist on main (`BAmF`, `BAflowEs`, `BAflowLam0`, `zSeq`, `BAmF_sz0_im_pos`, `sz0`); T2382 edits `BA/FlowPins` (disjoint files, ticket's sibling scan) so those names must not be renamed there |
| 5 tripwire | PASS (no fire) | g = 0.2394 for the measured block, <= 0.484 for the two files even if every existing HierarchyN line is edited; f_sem = 0 |
| 6 registry | PASS | theorems only; no new owed pin expected |

Overall stage-1a verdict: BLOCKED on Target 2 (question above); Targets 1, 3-6 PASS.

## (a′) Preflight corrections — Sat Oct 10 12:29:27 UTC 2026

Amend 1 (`docs/tickets/T2383-amend-1.md`, DECISIONS §196) resolves the BLOCKED row of Target 2 as option (A): `HierarchyN.lean` untouched (generic restatement goes to T5s2); Target 4 (BA instance) moves to T5-BA, replaced by a non-band generic instance with no `BA/*` import. Rows 1, 3, 5, 6 of the verdict table stand.

## (b) Script output (stage 1b, prover `claude-sonnet-5-5`, worktree `RBM3D-wt/T2383`, branch `t/T2383`, commit `ddf93af`)

Tripwire (binding), measured on the branch (`git diff -U0` hunk counts, hunks starting before the instance section):
```
$ git diff --numstat            (before commit; LoopGenN.lean only)
160	99	RBM3D/Induction/LoopGenN.lean
added in block(<650): 139  after: 21      removed in block: 99
$ wc -l RBM3D/Induction/LoopGenN.lean   -> 781   (main: 720; stop line 800 not reached)
$ git diff --name-only main...t/T2383   -> RBM3D/Induction/LoopGenN.lean
$ git diff --stat main...t/T2383 -- RBM3D/Induction/HierarchyN.lean | wc -l   -> 0
```
- g (LoopGenN block, edited lines / 568 band-object lines) = 139/568 = 0.245; over both files (denominator 804, `HierarchyN.lean` 0 edits) 139/804 = 0.173. Both below 0.5 (the preflight's T2379 probe figure was 136/568 = 0.239).
- f_sem = 0 (the band statement `loopGenN` is a 1-line corollary; no lines moved into a band instance). Below 0.30. Tripwire does not fire.

Build and axioms:
```
$ lake build RBM3D.Induction.LoopGenN      -> Build completed successfully (3756 jobs).
$ lake build                               -> Build completed successfully (4197 jobs).   (runs #assert_rbm_axioms, 0 "error" lines)
info: LoopGenN.lean:776:0: 'RBM.Ind.loopGenNOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: LoopGenN.lean:777:0: 'RBM.Ind.loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: LoopGenN.lean:778:0: 'RBM.Ind.recovers_loopGenN' depends on axioms: [propext, Classical.choice, Quot.sound]
info: LoopGenN.lean:779:0: 'RBM.Ind.genMat_eq_genMatOf' depends on axioms: [propext, Classical.choice, Quot.sound]
info: LoopGenN.lean:780:0: 'RBM.Ind.stLoopGenNForm_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
info: LoopGenN.lean:781:0: 'RBM.Ind.hierarchyN_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Imports of `LoopGenN.lean` unchanged (no `BA/*`): `HierarchyN`, `Hierarchy.ContractionSecondLoop`, `Hierarchy.ContractionBasic`, `Gauss.LoopCoordinate`, `Gauss.LoopGenerator`. Registry (Target 6): no new owed pin (theorems/def only); the full `lake build` runs `#assert_rbm_axioms` through `import RBM3D` and passes; `Test/Axioms.lean` not touched.

Name-clash grep (new public names `genMatOf`, `loopGenNOf`, `recovers_loopGenN`, `genMat_eq_genMatOf`) over `RBM3D/` excluding `Induction/LoopGenN.lean`: no match.

G1 check (target 3): scratch file `scratchpad/T2383/G1.lean` (`import RBM3D.Induction.LoopGenN`, `import RBM3D.Induction.HierarchyN`) holds `example : <old statement text of main:LoopGenN.lean:548-560> := RBM.Ind.loopGenN d L W g E hL hE u hu1 M hM σ a`, `example (d) : STLoopGenNForm d := stLoopGenNForm_holds d`, `example (d) : HierarchyN d := hierarchyN_holds d`, `example (d) : HierarchyN d := hierarchyN_of_loopGenN d (stLoopGenNForm_holds d)`:
```
$ lake env lean scratchpad/T2383/G1.lean ; echo $?   -> (no output) 0
```
The two merged checks `LoopGenN_check_stLoopGenNForm_sz0`, `LoopGenN_check_hierarchyN_sz0` compile unchanged in the file. `HierarchyN.lean` is identical to main, so its declarations' G1 is trivial.

Target statements (extracted from the file by `sed`): generic definition and theorem
```
def genMatOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (m : ℂ) (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  (1 / 2 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
      deriv (deriv (fun y : ℝ =>
        loopL d L W (blockMat d L W (M + (y : ℂ) • coordinateMatrix d L W c)) (ztOf m E u) I)) 0 +
    deriv (fun v : ℝ => loopL d L W (blockMat d L W M) (ztOf m E v) I) u
theorem loopGenNOf (d L W : ℕ) (g : ℝ) [NeZero L] [NeZero W] (m : ℂ) (E : ℝ) (hL : 3 ≤ L)
    (hm : 0 < m.im) (u : ℝ) (hu1 : u < 1) (M : Matrix (Idx d L W) (Idx d L W) ℂ) (hM : M.IsHermitian)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    genMatOf d L W g m E u M (loopOf σ a) = (W:ℂ)^d * Σ_{k'∈[1,len]} Σ_{l'∈(k',len]} Σ_{x,y}
        loopL .. (ztOf m E u) (cutGlueL k' l' x) * SB d L g x y * loopL .. (ztOf m E u) (cutGlueR k' l' y)
      + (W:ℂ)^d * Σ_{k'} Σ_{x,y} (loopL .. (ztOf m E u) ⟨[σ_k'],[x]⟩ - PropSpin m σ_k') * SB d L g x y
        * loopL .. (ztOf m E u) (cutGlue k' y)
theorem genMat_eq_genMatOf ... : genMat d L W g E u M I = genMatOf d L W g (mE E) E u M I := rfl
theorem recovers_loopGenN : type_of% @loopGenN := fun .. => loopGenNOf d L W g (mE E) E hL (mE_im_pos hE) u hu1 M hM σ a
theorem loopGenN  -- old name, old statement (zt E u, mSigma E, |E| < 2), proved by `loopGenNOf .. (mE E) .. (mE_im_pos hE) ..`
```
(The elided summation lines are verbatim in the file, `LoopGenN.lean` `loopGenNOf`, lines 567-580.) The band-free private lemmas are reused unchanged; the band-specific private lemmas (`hasDerivAt_Gsig_spec`, `edgeTerm`, `hasDerivAt_word_spec`, `deriv_spec`, `trace_edgeTerm`, `pairCut`, `specEdge`, `avg`, `avg_eq`, `edge_algebra`) were replaced in place by the generic texts of the probe `t/T2379:RBM3D/Probe/T2379Pins.lean:118-286`, plus `LoopGenN_hasDerivAt_ztOf` (new, private); the generic block is the probe text (source: branch `t/T2379` at commit `00a2206`; no RBM1D/RBM2D port in this ticket).

Compiled nonempty instances (in `LoopGenN.lean`, section `Instances`, all hypotheses discharged, no `BA/*` import):
- non-band generic: `example := loopGenNOf 3 3 2 (1/2) Complex.I 3 le_rfl (by simp) (1/2) (by norm_num) LoopGenN_M0 LoopGenN_M0_isHermitian ![true,false,true] ![(0 : Zd 3 3),1,2]` (`m = i`, `0 < m.im` by `simp`, `E = 3` outside the band `|E| < 2`, non-scalar Hermitian `LoopGenN_M0` (`LoopGenN_M0_apply`: entry (0,1) = 1), loop (+,-,+), 216 sites);
- band at `m = mE (1/2)` through the generic theorem (second `example`); the merged `LoopGenN_check_loopGenN` (band `loopGenN`), `LoopGenN_check_stLoopGenNForm_sz0`, `LoopGenN_check_hierarchyN_sz0` (sz0, `E = 0`, `M = 1`, k = 3) remain and compile.
Narrative: `m = I` is not the semicircle value at any `E`; its flow `ztOf I 3 u = 3 + (1-u) i` has `Im = 1 - u > 0` for `u < 1`.

## (c) Verified Mathlib / project names used
- `PropSpin` (`Propagator/Pins.lean:30`), `ztOf`, `etaOf`, `ztOf_im` (`Loop/GLoopFlow.lean:55,58,64`), `mE_im_pos` (`Defs/Semicircle.lean:56`): found by `grep` this session.
- `hasDerivAt_green_moving`, `hasDerivAt_id`, `HasDerivAt.ofReal_comp`, `HasDerivAt.star`, `Complex.I`: used in the probe text, elaborate in the build.

## (d) Open issues and paper-delta candidates
- Target 2 (generic `HierarchyN`, `STLoopGenNForm`) is deferred to T5s2 by Amend 1; `HierarchyN.lean` has 0 edit lines.
- Target 4 (BA instance at `BAmF`, probe 385-388) is deferred to the BA-side row T5-BA by Amend 1; replaced here by the non-band instance above.
- Paper-delta candidate `T2383a`: none (the generic theorem at `m = mE E` is the band statement; no Lean/paper statement difference arises).
