Prover model: claude-sonnet-5-5
# T2517 row b (branch `t/T2517b`, stage 1b): prove report (Thu Oct 15 10:39:59 UTC 2026)
Scope: targets 6, 7, 9 of `docs/tickets/T2517.md` (new `RBM3D/BA/GUEEq729BA.lean`, one import line in `RBM3D.lean`), stacked on row a's first commit `db2015e4`.
Target 8 is not written (ticket Decision (1) = DECISIONS §339 (1); CONTROL.md:13 (Released item 485: "target 8 moved to C5; reads no C3 name"); `T2517-1a-audit.md` observation 2; `T2517-prove.md` (a) row 12): no `BA/GUEKPrim` import. Sections (a), (a′), (a″) are in `docs/reports/T2517-prove.md`
and `docs/reports/T2517-1a-audit.md` (PASS); not edited here; I found no error in (a) for row b, so no (a′). `<S>` = scratchpad `T2517b/` (not in the repository).
Status: target 6 = `oneStepEnvelopeGUEOf`:171, `condExp_loop_step_gueBA`:467, `condExp_loop_drift_gueBA`:488 (= `T2517_DriftBA`); target 7 = `eq729FBA`:531, `eq729eBA`:538, `eq729_eG2BA`:599, `eq729_duhamelBA`:642, `eq729_one_stepBA`:743 (= `T2517_OneStepBA`);
target 9 = instances `RBM.BA.GUEEq729BAInst` (b6). All in `RBM3D/BA/GUEEq729BA.lean` (1,331 lines), built, committed on `t/T2517b` (HEAD 35835a36), standard axioms only. No stop rule of the ticket fired.

## (b) Script output
### b1 Section commits and `wc -l` (stop rule H134, DECISIONS §148 (5); ticket stop lines: 1,400 soft, 2,000 binding; census row b central 958 pure / 1,246 wide, `T2517-prove.md` (a) row 11)
```
$ git log --format="%h %s" db2015e4..HEAD ; wc -l RBM3D/BA/GUEEq729BA.lean  (the `date -u` after each commit, from the tool log)
8f90facc 10:07:46 UTC  wc -l   339  §1-§2: jets, time step, oneStepEnvelopeGUEOf (target 6)
164da98e 10:08:21 UTC  wc -l   525  §3: condExp_loop_step_gueBA, condExp_loop_drift_gueBA (target 6)
14dfddbc 10:08:47 UTC  wc -l  1098  §4-§5: eq729FBA, eq729eBA, eq729_eG2BA, eq729_duhamelBA, eq729_one_stepBA (target 7)
fdb001f3 10:11:57 UTC  wc -l  1323  §6: instances (target 9) + import line in RBM3D.lean
73ccb8ae 10:21:02 UTC  wc -l  1330  eq729_one_stepBA stated with the signed let bodies
929718c0 10:26:14 UTC  wc -l  1331  module docstring
f7eb29d0 10:28:41 UTC  wc -l  1331  instance docstrings
35835a36 10:30:25 UTC  wc -l  1331  three unused open-private names dropped
```
No stop line reached: 1,331 < 1,400 < 2,000; inside the wide census range 1,196-1,595.
### b2 Builds (`<S>/build8.log`, `fullbuild4.log`, `fullbuild5.log`)
```
$ lake build RBM3D.BA.GUEEq729BA        # 10:29:55 UTC, content of 35835a36
✔ [3935/3935] Built RBM3D.BA.GUEEq729BA (17s)  /  Build completed successfully (3935 jobs).     # lines of the log naming this file with `warning`: 0
$ lake build   # full, f7eb29d0: 10:27:20-10:28:36 UTC, EXIT=0, real 1:16.26
info: RBM3D.lean:655:0: axiom audit: 15511 theorems, 4757 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: ...    Build completed successfully (4425 jobs).
$ lake build   # full, 35835a36 (header-only change; cached): 10:30:22-10:30:25 UTC, EXIT=0, Build completed successfully (4425 jobs).
# integration check (uncommitted, restored): `RBM3D/BA/GUEOneLoop.lean` swapped for main's merged file (ff7bd277, 1,395 lines) in this working copy, then `git show HEAD:...` copied back (`git status --short` empty):
$ lake build RBM3D.BA.GUEEq729BA        # 10:35:14 UTC, `<S>/build_vs_main.log`: ✔ Built RBM3D.BA.GUEOneLoop (14s); ✔ [3935/3935] Built RBM3D.BA.GUEEq729BA (17s); EXIT=0
```
### b3 `#print axioms` of every new public declaration and instance (`<S>/axioms.lean`, run on 35835a36)
```
'RBM.BA.oneStepEnvelopeGUEOf' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.condExp_loop_step_gueBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.condExp_loop_drift_gueBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729FBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729eBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_eG2BA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_duhamelBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.eq729_one_stepBA' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.oneStepEnvelopeGUEOf_check' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.condExp_loop_step_gueBA_check' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.condExp_loop_drift_gueBA_check' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_eG2BA_check' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_duhamelBA_check' -> [propext, Classical.choice, Quot.sound]
'RBM.BA.GUEEq729BAInst.eq729_one_stepBA_check' -> [propext, Classical.choice, Quot.sound]
```
### b4 Targets 6 and 7, statements extracted by script (`<S>/extract.py`); the other public theorems are at `RBM3D/BA/GUEEq729BA.lean:` oneStepEnvelopeGUEOf:171 condExp_loop_step_gueBA:467 condExp_loop_drift_gueBA:488 eq729FBA:531 eq729eBA:538 eq729_eG2BA:599 eq729_duhamelBA:642 eq729_one_stepBA:743
```
--- condExp_loop_drift_gueBA (RBM3D/BA/GUEEq729BA.lean:488-503)
theorem condExp_loop_drift_gueBA :
    ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (m : ℂ), 0 < m.im → ‖m‖ ≤ 1 →
    ∀ {I : LoopIdx (Zd d (sz.L n))}, I.WF → 0 ≤ t1 n → t1 n ≤ t0 n → K n ≠ 0 → k < K n →
      gridTime t1 t0 K n (k + 1) < 1 →
      ∀ᵐ ω ∂(Pgue (sz.withLam 0)),
        ‖(Pgue (sz.withLam 0))[fun ω' : PathΩ (sz.withLam 0) =>
              loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
                (gueHBA sz g t1 t0 K n (k + 1) ω'))
                (ztOf m E (gridTime t1 t0 K n (k + 1))) I | filt (sz.withLam 0) k] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
              (ztOf m E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n k)
              (gueHBA sz g t1 t0 K n k ω) I‖
        ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf m (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (I.length + 4) *
              gridStep t1 t0 K n ^ ((3 : ℝ) / 2)
--- eq729_one_stepBA (RBM3D/BA/GUEEq729BA.lean:743-772)
theorem eq729_one_stepBA :
    ∀ {d : ℕ} (sz : Sizes d) (g t1 t0 E : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n : ℕ)
      (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
      let F : ℕ → PathΩ (sz.withLam 0) → LoopIdx (Zd d (sz.L n)) → ℂ := fun k ω I =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k)) I
      let e : ℕ → LoopIdx (Zd d (sz.L n)) → ℂ := fun k I =>
        (∫ ω, F k ω I ∂(Pgue (sz.withLam 0))) - Kt n (gridTime t1 t0 K n k) I
      0 < (m n).im → ‖m n‖ ≤ 1 → 0 ≤ t1 n → t1 n ≤ t0 n → t0 n < 1 →
      ∀ {Λ ρ p Bk : ℝ}, Λ = (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ → Λ ≤ 1 → 0 ≤ ρ →
      ρ * Λ ≤ 1 → 0 ≤ p →
      ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1 →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ) →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2) →
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s) →
      ∀ {k : ℕ}, k < K n →
      (∀ a, ‖(∫ ω, F k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ρ * Λ ^ 2) →
      ∀ {B : Set (PathΩ (sz.withLam 0))}, Pgue (sz.withLam 0) B ≤ ENNReal.ofReal p →
      (∀ ω ∉ B, ∀ σ a, ‖F k ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ ρ * Λ) →
      (∀ ω ∉ B, ∀ s1 s2 x y,
        ‖F k ω ⟨[s1, s2], [x, y]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2) →
      (∀ ω ∉ B, ∀ s1 s2 s3 x y w,
        ‖F k ω ⟨[s1, s2, s3], [x, y, w]⟩ - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤
          ρ * Λ ^ 3) →
      (∀ s1 s2 x y, ‖e k ⟨[s1, s2], [x, y]⟩‖ ≤ Bk) →
      ∀ (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)),
        ‖e (k + 1) ⟨[s1, s2], [a1, a2]⟩‖ ≤
          (1 + gridStep t1 t0 K n * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) * Bk +
            eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)
```
### b5 Statement diff against the signed texts (`<S>/diff_t2517.py`: check lines 156-204 with the 4 inline bodies replaced by `gueHBA sz g t1 t0 K n X ω`; and the auditor-style `example`)
```
inline bodies replaced: T6 3 T7 1
T6 condExp_loop_drift_gueBA vs T2517_DriftBA: check tokens 373, mine 373, differing hunks 0
T7 eq729_one_stepBA vs T2517_OneStepBA: check tokens 859, mine 859, differing hunks 0
$ lake env lean <S>/signed_test.lean   # signed_test.lean: `def T2517_DriftBA`, `def T2517_OneStepBA` (check text, `gueHBA` bodies) and
#   example : T2517_DriftBA := @condExp_loop_drift_gueBA     example : T2517_OneStepBA := @eq729_one_stepBA
EXIT=0
```
### b6 Compiled nonempty instances (namespace `RBM.BA.GUEEq729BAInst` from `RBM3D/BA/GUEEq729BA.lean:1107`: `_check` theorems at :1146 envelope, :1167 step, :1179 drift, :1196 `eq729_eG2BA`, :1216 duhamel, :1288 `eq729_one_stepBA`; `example`s at :1309, :1321; proof terms by script)
Data: `d = 3`, `sz0` (`L_0 = 4`, `W_0 = 32`, `N = 2097152`), `n = k = 0`, flow datum `g₀, E₀, m₀` of `sz0` (`hr0I`: `BAReal` at `κ = 1/2`, so `1/2 ≤ Im m₀ ≤ ‖m₀‖ ≤ 1`),
`t₁ = 17/20`, `t₀ = 9/10`, `K = 131072` (`N Δ = 4/5`), `ρ = 1`, `Λ = (N η(t₀))⁻¹ ∈ [4.76e-6, 9.54e-6]`, `Bk = 200`, `Kt = Eq729AInst_Kt` (band: `c(t₁) = 10⁻⁶`, `c' = N c²`).
```
--- condExp_loop_drift_gueBA_check (from :1192)
  condExp_loop_drift_gueBA sz0 gI t1I t0I KI 0 0 E0I m0I im_pos norm_le (loop2_wf _ 0 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) grid_lt
--- eq729_one_stepBA_check (from :1301)
  eq729_one_stepBA sz0 gI t1I t0I EI mI KI 0 (fun n => Eq729AInst_Kt (sz0.L n)) im_pos norm_le
    (by norm_num) (by norm_num) (by norm_num) (Λ := ΛI) (ρ := 1) (p := p) (Bk := 200) rfl Λ_le_one
    zero_le_one (by linarith [Λ_le_one]) hp0 (by rw [size0]; unfold gridStep; norm_num)
    (Eq729AInst_hKb (by linarith [Λ_ge]))
    (fun s _ s1 s2 s3 x y w => by rw [Eq729AInst_Kt_three, norm_zero]; positivity)
    Eq729AInst_hKd (k := 0) (by norm_num) hX hB hg1 hg2 hg3 hBk_inst s1 s2 a1 a2
--- oneStepEnvelopeGUEOf_check (from :1157)
  oneStepEnvelopeGUEOf 3 2 2 ⟨1 / 5, 9 / 10⟩ 0 (by norm_num)
    (by
      rw [Complex.norm_def]
      exact Real.sqrt_le_one.mpr (by norm_num [Complex.normSq_mk]))
    (loop2 2 0 1) (loop2_wf 2 0 1) 0 (1 / 4) le_rfl (by norm_num) (by norm_num) 1
    Matrix.isHermitian_one
```
Discharged in the T7 instance: `0 < Im m`, `‖m‖ ≤ 1`, `0 ≤ t₁ ≤ t₀ < 1`, `Λ ≤ 1`, `ρΛ ≤ 1`, `N Δ ≤ 1`, `hK2b`, `hK3b`, `hKd`, `k < K`, `hBk` (`‖e_0‖ ≤ 200`). Left as hypotheses (other gates' pins):
`hX` (row a's `gueGrid_expect_oneLoopBA`), `hB`, `hg1`-`hg3` (C5), and `p ≥ 0`; the first `example` (:1309) takes `B = univ`, `p = 1`, leaving only `hX`. T6, step, `eq729_eG2BA`, `eq729_duhamelBA`: no pin left.
### b7 Name-level tables (`<S>/names_table3.py`: identifiers of the file that resolve to a declaration of the 216-module import closure; `module pub/PRIV: name:line`; the local-name filter of the script drops `X.add`-style tokens, so `Eq729A_BM.add/.sub/.mul/.integrable` and `Sizes.size/.withLam` were added by hand, lines checked with `grep -n`)
Every `PRIV` name is read by `open private … from` (45 names opened: 23 `Drift`, 14 `Eq729A` lemmas, 4 `Eq729A` instance helpers, 1 `Generator`, 3 `OneStep`; the table of the planned names, `<S>/names.txt`, was produced before the first Lean file was written).
```
BA.FlowPins pub: BAmF:252 BAflowEs:383 BAflowLam0:386 zSeq:1181
BA.GUEOneLoop pub: gueHBA:45 gueHBA_isHermitian:49
BA.GreenStab pub: g0I:332 E0I:333 m0I:334
BA.Ward pub: BAm_norm_le_one:136
Defs.Lattice pub: Zd:63
Defs.Sizes pub: Idx:46 Sizes:138 sz0:260 sz0_values:267 Sizes.size:157 Sizes.withLam:182
Gauss.BlockAnderson pub: PsiI:52 PsiI_isHermitian:65
Gauss.FineModel pub: Ω:84 Xmat:113 Xmat_isHermitian:142 coordinateMatrix_isHermitian:388 continuous_Xmat:427
Gauss.FlowCalculus pub: norm_gloop_le_crude:708
Gauss.Model pub: Vtx:60
Induction.Split pub: RBM.Ind.norm_gloop_le_of_le_abs_im:757
Loop.GLoop pub: Eblk:55
Loop.GLoopFlow pub: ztOf:55 etaOf:58 ztOf_im:64 Gres:74 blockMat:105 loopL:123 cutGlue:317
Path.OneStep pub: OneStep_norm_one_le:851 OneStep_isHermitian_add_realSmul:1264 OneStep_J1:1278 OneStep_J2:1283 OneStep_norm_J2_le:1391 OneStep_norm_J1_sub_le:1418 OneStep_card_Idx:1597
Path.OneStep PRIV: OneStep_hasDerivAt_w0:1109 OneStep_hasDerivAt_w1:1121 OneStep_hasDerivAt_trace:1227
Path.Walk pub: filt:62 gridStep:67 gridTime:70 walk_measurable_loopL:780 walk_measurable_blockMat:788
Universality.GUEPhase.Bootstrap pub: SBgue:54 primBilGUE:173 primRhsGUE:178 primRhsGUE_sub:190
Universality.GUEPhase.Drift PRIV: Drift_integrable_normX:182 Drift_integral_normX_le:191 Drift_Hs:227 Drift_Hs_eq:231 Drift_Hs_herm:235 Drift_continuous_Hs:239
                                  Drift_continuous_gloop:270 Drift_card_Block:432 Drift_g:450 Drift_space_step:568 Drift_taylor2:615 Drift_closure:687 Drift_deriv_deriv:735
                                  Drift_condExp_freezeC:948 Drift_herm_of_isHermitian:1009 Drift_Phi:1023 Drift_continuous_Phi:1027 Drift_norm_Phi_le:1034
                                  Drift_isHermitian_add_smul:1040 Drift_scaledSlice:1109 Drift_measurable_scaledSlice:1112 Drift_map_scaledSlice:1138 Drift_gueH_succ':1174
Universality.GUEPhase.Eq729A pub: eq729_primBil2:52 eq729_norm_primBil2_le:132 eq729_step_nonneg:283 eq729_time_mem:300 eq729_Kdisc:562 eq729c:723
Universality.GUEPhase.Eq729A PRIV: Eq729A_loopL_one_false:166 Eq729A_BM:187 Eq729A_BM_const:190 Eq729A_BM.add:193 Eq729A_BM.sub:199 Eq729A_BM.mul:205 Eq729A_BM.sum:213
                                   Eq729A_BM.integrable:223 Eq729A_time_succ:288 Eq729A_norm_integral_Wsum_le':438 Eq729A_integral_primBil_left:449 Eq729A_integral_primBil_right:466
                                   Eq729A_quad:484 Eq729A_pair:519 Eq729AInst_Kt:1113 Eq729AInst_Kt_three:1134 Eq729AInst_hKb:1182 Eq729AInst_hKd:1189
Universality.GUEPhase.Generator pub: mSigOf:62 genMatGUEOf:68 egtNGUEOf:79 loopGenGUEOf:1168
Universality.GUEPhase.Generator PRIV: Generator_hasDerivAt_Gsig_spec:751
Universality.GUEPhase.Grid pub: gueUnit:52 Pgue:61 gueH:77 gueH_isHermitian:164 gueH_adapted:181
Universality.Pins pub: gueP:67
```
### b8 Greps (`<S>/greps.py`, comments dropped, run on 35835a36)
```
declarations: 54 public (incl. examples): 16
C1 regex hits in public declarations (comments dropped; statements incl. instance bodies): []
gueH/Pgue/PathΩ/filt in public declarations not followed by `withLam 0`: []
private declarations using Pgue/gueH at a generic `sz`: ['GUEEq729BA_condExp_step', 'GUEEq729BA_measurable_shift_filt']
X1-C4 def hits (GUEEq729BA.lean, RBM3D.lean): []
imports of the V modules: 0
sorry/admit/axiom/native_decide: 0
import closure (RBM3D modules): 216 V hits: []
$ grep -c 'sz\.lam\|\.lam\b' RBM3D/BA/GUEEq729BA.lean      -> 0   (UBA-C1: no `sz.lam`)
```
### b9 Scope, importers, clashes, ports
```
$ git diff --stat db2015e4 HEAD                          -> RBM3D.lean | 1 +,  RBM3D/BA/GUEEq729BA.lean | 1331 +   (2 files)
$ git diff --stat 13b68cea HEAD -- RBM3D/Universality RBM3D/Path RBM3D/Gauss RBM3D/Loop RBM3D/BA/GreenStab.lean RBM3D/BA/FlowPins.lean RBM3D/Test   -> (empty: no merged file changed)
$ grep -rln GUEEq729BA RBM3D RBM3D.lean                 -> RBM3D/BA/GUEEq729BA.lean, RBM3D.lean   (importers: RBM3D.lean only)
$ grep -rlwE "<the 8 public names|GUEEq729BAInst|GUEEq729BA_>" RBM3D-wt/*/RBM3D (1191 directories) and main/RBM3D (ff7bd277), minus this file  -> 0 files   # 10:36:35 UTC
$ git ls-tree -r main --name-only | grep -c GUEEq729BA   -> 0
ports: no RBM1D/RBM2D text copied; RBM1D/RBM2D `diff --stat`: n/a. Band sources (read, unchanged; last commit touching each): Drift.lean 5d0b6da1, Eq729A.lean 9c3bfc7e, Generator.lean 4db59940, OneStep.lean 5d0b6da1.
```
### b10 Narrative
1. `oneStepEnvelopeGUEOf` follows the proof of `oneStepEnvelopeGUE` (Drift:765-914) along `ztOf m E`: the space step, the constant closure and the Taylor lemma are the band's private lemmas, which are generic in
   the spectral parameter and its imaginary part (`open private`). New analysis: `GUEEq729BA_time_step` and the jets' derivative along `ztOf m E` (`OneStep_hasDerivAt_w0/w1/trace` fed by the generic-`m`
   `Generator_hasDerivAt_Gsig_spec`); the spectral direction is `m_σ · 1` and `‖m‖ ≤ 1` bounds it (the band's `‖m‖ = 1` is not needed).
2. `condExp_loop_step_gueBA` is a corollary of a private lemma at an arbitrary Hermitian shift `A` over any `sz'` (`GUEEq729BA_condExp_step`), taken at `sz' = sz.withLam 0`, `A = g Ψ_I`: all matrix types
   stay over `(sz.withLam 0).L n`, the shape of `gueHBA`; the freezing lemma and the law transfer are `Drift_condExp_freezeC`, `Drift_map_scaledSlice`. `condExp_loop_drift_gueBA` combines it with the envelope.
3. Target 7: `eq729_eG2BA`, `eq729_duhamelBA` and the loop facts (`GUEEq729BA_loop_BM`, `_loop_bound`, ...) are twins of `eq729_eG2`, `eq729_duhamel`, `Eq729A_loop_*`, re-proved at `gueHBA`; `eq729_Kdisc`,
   `eq729_primBil2`, `eq729_norm_primBil2_le`, `eq729c`, `loopGenGUEOf` (no `0 ≤ u`, no `3 ≤ L`) and the `Eq729A_BM` calculus are read by name or `open private`. `Eq729A_BM` terms are combined by explicit
   applications `Eq729A_BM.add …`: dot notation does not resolve those private names from another module (compile error `And.integrable`).
4. `eq729_one_stepBA` is stated with the signed `let` bodies (b5: 859 tokens, 0 hunks); its proof starts with `clear_value`/`subst` to `eq729FBA`, `eq729eBA` (both `rfl`) and then follows `eq729_one_step`
   (Eq729A:760-1073). Steps that differ from the band proof beyond renaming: `‖mSigOf m σ‖ ≤ 1` (band `= 1`), the envelope constant at `ℓ = 2` (`16·5⁴ = 10000`, closed by `norm_num`), no `0 ≤ u` (`loopGenGUEOf`).
5. Instances: b6. The five `sz0` instances use `hr0I` (`n = 0` only), so they are at `n = 0`; `Eq729AInst_*` (private band instance helpers) supply `Kt`, `hK2b`, `hKd` of the T7 instance.
6. Instance arguments (H317 (3), `T2517-1a-audit.md` §2): no explicit instance argument; `NeZero (sz.L n)`, `NeZero (sz.W n)` are the global instances `Sizes.neZeroL`, `Sizes.neZeroW` (`Defs/Sizes.lean:152-153`); the mismatch of the inline body is removed by `gueHBA` (row a), used in both statements.
7. D1 (ii) is target 6 (BA leaf, public, Decision (3)); D1 (iii): the substitution table is what the signed texts of T6, T7 encode (b5, 0 hunks); `BAReal` enters only through the instances (`hr0I`), the theorems need `0 < Im m`, `‖m‖ ≤ 1`.
8. Coverage as used by row b (ticket table): rows 10, 12, 13 are read (names in b7); row 11 is written here; rows 1-9 are row a's; row 14 (target 8) moved to C5; row 15 is C5's.
9. Registry: no new line (`hX`, `hB`, `hg1`-`hg3`, `hBk` are explicit hypotheses as in the band `eq729_one_step`; no `Prop` structure or named premise is introduced). Sibling scan: the only shared file is `RBM3D.lean`.

## (c) Mathlib names
New relative to the merged band files (script: tokens of the file minus tokens of Drift, Eq729A, Generator, OneStep, GUEOneLoop, GreenStab; `#check` and module lookup in `<S>/mathlib_check.lean`, EXIT=0):
`Complex.im_le_norm : ∀ z, z.im ≤ ‖z‖` (Mathlib.Analysis.Complex.Norm); `Complex.norm_def : ‖z‖ = √(normSq z)` (same); `Complex.normSq_mk` (Mathlib.Basic.Complex.Basic);
`Real.sqrt_le_one : √x ≤ 1 ↔ x ≤ 1` (Mathlib.Analysis.Real.Sqrt); `inv_le_comm₀ : 0 < a → 0 < b → (a⁻¹ ≤ b ↔ b⁻¹ ≤ a)` (Mathlib.Algebra.Order.GroupWithZero.Basic).
All other Mathlib/core names occur in the merged files above (same toolchain `leanprover/lean4:v4.34.0`). Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. Branch history: `t/T2517b` contains the probe commit `c305806d` (below `db2015e4`), so `git diff --name-only 13b68cea HEAD` lists `RBM3D/Probe/T2517Pins.lean` (branch-only, never merged), `RBM3D/BA/GUEOneLoop.lean` (row a),
   `RBM3D/BA/GUEEq729BA.lean`, `RBM3D.lean`. Merge order a → b; row b adds only `GUEEq729BA.lean` and one import line (CONTROL.md:743: the hub applies `db2015e4...t/T2517b` onto main).
2. The instances read four private band-instance helpers (`Eq729AInst_Kt`, `_Kt_three`, `_hKb`, `_hKd`) by `open private`; renaming them in `Eq729A.lean` would break `GUEEq729BAInst` (no merged file is changed here).
3. `hX` (row a's `gueGrid_expect_oneLoopBA` conclusion form) and `hB`, `hg1`-`hg3`, `hBk` (C5's `HypA`/`PathBounds` twins, ticket coverage row 15) of `eq729_one_stepBA` are inputs; nothing here proves them.
4. The Lean instance data (b6) differ from the illustrative numbers of (a)(ii) (`t₁ = 1/4`, `t₀ = 1/2`, `K = 2^22`, `E = 0.5`): the instance reuses the band family `Eq729AInst_Kt`, defined on `[17/20, 9/10]`, and the flow datum `hr0I` of `sz0`; the hypotheses are discharged by proofs, not by (a)(ii).
5. Paper-delta candidates (row a's `T2517a`, `T2517b` are in the ticket's item (7), not here):
   - `T2517c` (statement): the BA drift, conditional step and (7.29) one-step recursion are stated at a free flow datum `(g, E, m)` with `0 < Im m`, `‖m‖ ≤ 1` (band twins: `m = m_sc(E)`, `|E| < 2`); `grep -i envelope paper/tex/*.tex`: no hit
     (the constant `16 (ℓ+3)⁴ N⁴ (1 + η⁻¹)^{ℓ+4}` is Lean-side); `m` is the flow-point value of `(eq:zt)`, `1_2:716`.
   - `T2517d` (carrier): the GUE part of the BA path is `Pgue (sz.withLam 0)` (`S^{(B)}(0) = 1`) shifted by `H_0 = g Ψ_I`, a grid walk instead of the Brownian motion `(MBM)`, `1_2:685-691` (the grid-walk delta of the band layer, now with the shift).
