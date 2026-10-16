Prover model: claude-sonnet-5-5
## (b) Row b, stage 1b (`prover-max`, claude-sonnet-5-5) — written Fri Oct 16 14:34:39 UTC 2026
Ticket T2519, row b (targets 6 and 8): `RBM3D/BA/GUEDuhamelBA.lean`, reserve `RBM3D/BA/GUEDuhamelBA2.lean`, `RBM3D.lean` (2 import lines). Branch `t/T2519b`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2519b`, stacked on row a's first commit `19df37e2`; my commits `38ffa12a` (14:04:56 UTC), `7607f59b` (14:18:02), `94a5105f` (14:25:03), `8f4c89c3` (14:32:56, last; the full build of (b1) precedes it; (b5) ran on this tree). Sections (a), (a′), (a″) of the 1a are in `docs/reports/T2519-prove.md`, the 1a-audit (counts as PASS, Amend 3) in `docs/reports/T2519-1a-audit.md`; Amends 1-3 read. This report covers row b only. Scratch: `<scratchpad>/T2519b/` (CONTROL H28).
**Verdict: all targets of row b (6, 8) are built, instanced and committed; no obstruction; no stop rule of the ticket was hit** (no file over 2,000; no merged file or statement changed; no `private` deleted; no V module imported; R2 not needed; no public result with an unproved `Prop` premise).
### (b1) Build, axioms, sizes (script output)
```
$ lake build RBM3D.BA.GUEDuhamelBA RBM3D.BA.GUEDuhamelBA2    # 14:31:21 UTC
✔ [3952/3953] Built RBM3D.BA.GUEDuhamelBA (6.2s)
✔ [3953/3953] Built RBM3D.BA.GUEDuhamelBA2 (11s)
Build completed successfully (3953 jobs).
$ lake build                                                   # full library: 14:31:41 -> 14:32:50 UTC, exit=0; log tail:
info: RBM3D.lean:661:0: axiom audit: 15606 theorems, 4806 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4431 jobs).
$ #print axioms (script `axioms.lean`, 14:32 UTC), 27 declarations, grouped:
[propext, Classical.choice, Quot.sound]: 26 declarations: Duhamel_step_decompBA, Duhamel_drift_remainder_aeBA, Duhamel_azuma_ZBA, Duhamel_azuma_YBA, GUEDuhamelBA_Vp, GUEDuhamelBA_Zst, Inst.Duhamel_azuma_ZBA_check, Inst.Duhamel_azuma_YBA_check, Inst.bI_nonneg, Inst.hb_I, Inst.hv_I, Inst.hv_I1, Inst.eta_pos_I1, gueGrid_loop_duhamelBA, Inst.Duhamel_step_decompBA_check, Inst.Duhamel_drift_remainder_aeBA_check, Inst.gueGrid_loop_duhamelBA_check, Inst.hscale_I, Inst.real_I, Inst.im_pos_I, Inst.norm_le_I, GUEDuhamelBA_Phi, GUEDuhamelBA_Zinc, GUEDuhamelBA_Yst, GUEDuhamelBA_r, GUEDuhamelBA_hflow
does not depend on any axioms: 1 declarations: Inst.loop2_wf
$ wc -l / non-blank:   RBM3D/BA/GUEDuhamelBA.lean wc-l=     948 non-blank=853   RBM3D/BA/GUEDuhamelBA2.lean wc-l=    1058 non-blank=1003
```
Sizes (Amend 2 items 5, 8; landed numbers, so the landed forecast is the figure itself; `wc -l` printed before the four commits: 841 + 1,057, 842 + 1,058, 948 + 1,058, 948 + 1,058; stop sizes never reached): `GUEDuhamelBA` 948 and `GUEDuhamelBA2` 1,058 `wc -l`, each below the soft 1,500 and the binding 2,000; the row sums to 2,006 against the row landing line 2,245 (= max(1.67 × 776, 1.34 × 1,675); the 1a central of the Duhamel layer is pure 776 / wide 1,675, `docs/reports/T2519-prove.md` (iii′) "rows: b"); landed / wide central = 1.20, / pure central = 2.58. The reserve file is used because the row total, 2,006, would pass 1,500 in a single file (ticket Layout "reserve `GUEDuhamelBA2` past 1,500"; Amend 2 item 2); neither file passes 1,500 itself; the split is at the DuhamelB / DuhamelC boundary.
### (b2) Name-level tables (0149 :98)
Plan table at the 1b start: `python3 nametable.py namelist0.txt` (88 names, `file:line`) was run before the first Lean line was written (tool order: before the first `Write` of `GUEDuhamelBA.lean`); grouped by file:
```
U.GUE/DuhamelA1: Duhamel_vGue_gradMat_le:926, Duhamel_loopMax_le_crude:955, Duhamel_loopMax_shift_le:1053
U.GUE/DuhamelA2: DuhamelGood:166, DuhamelZ:170, DuhamelR:175, DuhamelT:180, DuhamelB:185, Duhamel_measurableSet_good:202, Duhamel_Z_re_im:219, Duhamel_measurable_R:408, Duhamel_integral_step:462, Duhamel_measurable_loop:523, Duhamel_norm_T_le:594, Duhamel_norm_B_le:818, Duhamel_measurable_coord:891, Duhamel_gueH_measurable_filt:906, DuhamelA2_condExp_freezeC:915
U.GUE/DuhamelB: Duhamelv:177, Duhamel_exists_level:794, Duhamel_Vp_le:839, Duhamel_qv_le_crude:949, DuhamelB_FY:389, DuhamelB_measurable_FY:394, DuhamelB_condSubG_frozen:450, DuhamelB_measurable_gradMat:150, DuhamelB_measurable_vGue:136, DuhamelB_sm_indicator_lin:236, DuhamelB_loopOf_eq:676, DuhamelB_size_pos:817, DuhamelB_size_eq:822, DuhamelB_norm_green_le:828
U.GUE/DuhamelC: DuhamelC_lam0:914, DuhamelC_epsY:917, DuhamelC_card_le:937, DuhamelC_num_step:609, DuhamelC_num_Q:626, DuhamelC_num_E1:671, DuhamelC_num_E2:706, DuhamelC_num_E3:742, DuhamelC_num_E4:753, DuhamelC_num_E5:787, DuhamelC_num_Y:829, DuhamelC_num_tau:895, DuhamelC_ev_exp_rpow:574, DuhamelC_ev_exp_lin:588, DuhamelC_size_pos:921, DuhamelC_L_pow_le:927, DuhamelC_lam0_pos:989, DuhamelC_K_cast:995, DuhamelC_loopOf_wf:1067, DuhamelC_loopOf_length:1071, DuhamelC_sqrt_add_le:132
not matched by the script's declaration regex (found by the as-used script below): DuhamelC_card_le', gueH_isHermitian, gueH_adapted
U.GUE/Markov: gueHasCondSubgaussianMGF_linear:615, gueHasCondSubgaussianMGF_of_frozen:184, gue_highProb_incr_le:863, vGue:291
Path/Azuma: azuma_complex:87
Path/Stop: firstHit:42, lt_firstHit_measurableSet:62, lt_firstHit_imp:75
U.GUE/Drift: gueH_succ:925
BA/GUEOneLoop: gueHBA:58, gueHBA_isHermitian:62, gueHBA_succ:72
BA/GUEEq729BA: condExp_loop_drift_gueBA:488
BA/GUEProcBA: GUEPathBoundsBA:42, BAKFam:60, BAPB:77
Chain/StepDecompGen: hermTestFunLoopNOf:101
U.GUE/Generator: genMatGUEOf:68
Loop/GLoopFlow: ztOf:55, etaOf:58, ztOf_im:64
U.GUE/Grid: gueGridK:106, gueGridK_ne_zero:108, Pgue:61, gueUnit:52
Path/Walk: gridStep:67, gridTime:70
Path/StepDecomp: gradMat:80, HermTestFun:186
Induction/PerTimeCalc: perTimeCalc_highProbAt_mono:112, perTimeCalc_highProbAt_inter:119
Defs/StochDomAt: highProbAt_iInter:279
```
As used (script `used.lean`: every project constant in the types and proof terms of the two files, 14:25-14:26 UTC; lines re-grepped; `*` = not in the plan; structural names and projections omitted):
```
BA.FlowPins: BAflowEs*:383, BAflowLam0*:386, BAmF*:252, flow_sz0*:1214, zSeq*:1181
BA.GUEEq729BA: condExp_loop_drift_gueBA:488
BA.GUEOneLoop: gueHBA:58, gueHBA_isHermitian:62, gueHBA_succ:72
BA.GreenSchur: BAflow_real*:59
BA.MFixedPoint: BAReal*:432, BASelf*:193
BA.Ward: BAm_norm_le_one*:136
Chain.StepDecompGen: hermTestFunLoopNOf:101
Defs.StochDomAt: highProbAt_iInter:279
Gauss.BlockAnderson: PsiI_isHermitian*:65
Gauss.FineModel: seqHflow_isHermitian*:531
Induction.PerTimeCalc: perTimeCalc_highProbAt_inter:119, perTimeCalc_highProbAt_mono:112
Induction.Split: loopMax_nonneg*:538
Loop.GLoopFlow: ztOf_im:64
Path.Azuma: azuma_complex:87
Path.Stop: lt_firstHit_imp:75, lt_firstHit_measurableSet:62
U.GUE.Drift: gueH_succ:925
U.GUE.DuhamelA2: DuhamelA2_Phi*:984, DuhamelA2_condExp_freezeC:915, DuhamelA2_continuous_Phi*:988, DuhamelA2_herm*:962, DuhamelA2_herm_of_isHermitian*:970, DuhamelA2_measurable_seqHflow*:198, DuhamelA2_norm_Phi_le*:996, DuhamelB:185, DuhamelGood:166, DuhamelR:175, DuhamelT:180, DuhamelZ:170, Duhamel_Z_re_im:219, Duhamel_integral_step:462, Duhamel_measurable_coord:891, Duhamel_measurable_loop:523, Duhamel_norm_B_le:818, Duhamel_norm_T_le:594, zero_mem_good*:1115
U.GUE.DuhamelB: DuhamelB_FY:389, DuhamelB_condSubG_frozen:450, DuhamelB_loopOf_eq:676, DuhamelB_measurable_FY:394, DuhamelB_measurable_gradMat:150, DuhamelB_measurable_vGue:136, DuhamelB_sm_indicator_lin:236, DuhamelB_standardBorelMatrix*:160, Duhamel_Vp_le:839, Duhamel_exists_level:794, Duhamel_qv_le_crude:949, Duhamelv:177
U.GUE.DuhamelC: DuhamelC_K_cast:995, DuhamelC_card_le':976, DuhamelC_card_le:937, DuhamelC_epsY:917, DuhamelC_ev_exp_lin:588, DuhamelC_ev_exp_rpow:574, DuhamelC_lam0:914, DuhamelC_lam0_pos:989, DuhamelC_loopOf_length:1071, DuhamelC_loopOf_wf:1067, DuhamelC_num_E1:671, DuhamelC_num_E2:706, DuhamelC_num_E3:742, DuhamelC_num_E4:753, DuhamelC_num_E5:787, DuhamelC_num_Q:626, DuhamelC_num_Y:829, DuhamelC_num_step:609, DuhamelC_num_tau:895, DuhamelC_size_pos:921, DuhamelC_sqrt_add_le:132
U.GUE.Grid: gueH_adapted:181, gueH_isHermitian:164
U.GUE.Markov: gueHasCondSubgaussianMGF_linear:615, gue_highProb_incr_le:863, sz0_size_tendsto_nat*:1122
vocabulary (structures, defs of the statements): HermTestFun, HighProbAt, Idx, L, LoopIdx, Markov_standardBorelPathΩ, PathΩ, Pgue, Pgue_isProbabilityMeasure, PsiI, SeqCoord, SeqΩ, Sizes, StochDomAt, W, WF, Zd, a, badSetAt, blockMat, etaOf, filt, firstHit, genMatGUEOf, gradMat, gridStep, gridTime, gueGridK, gueH, gueUnit, gueUnit_isProbabilityMeasure, length, linTr, loopL, loopMax, loopOf, mk, neZeroL, neZeroW, seqHflow, seqXmat, size, sz0, vGue, withLam, ztOf, σ
```
Planned, not read in the end (15): `BAKFam`, `BAPB`, `GUEPathBoundsBA` (row a §1: not needed by this row), `Duhamel_vGue_gradMat_le`, `Duhamel_loopMax_le_crude`, `Duhamel_loopMax_shift_le`, `Duhamel_measurableSet_good`, `Duhamel_measurable_R`, `Duhamel_gueH_measurable_filt`, `gueHasCondSubgaussianMGF_of_frozen`, `gueGridK_ne_zero`, `DuhamelB_size_pos`, `DuhamelB_size_eq`, `DuhamelB_norm_green_le`, `DuhamelC_L_pow_le`.
### (b3) Target statements (extracted from the files by script `extract.py`; docstrings omitted) and statement diff against the band twins
```
-- RBM3D/BA/GUEDuhamelBA2.lean:953-978
theorem gueGrid_loop_duhamelBA {d : ℕ} (sz : Sizes d) {τU : ℝ} (hτU : 0 < τU) (n0 : ℕ)
    {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hsize : Tendsto (fun n => sz.size n) atTop atTop)
    (hm : ∀ n, 0 < (m n).im) (hm1 : ∀ n, ‖m n‖ ≤ 1) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n)
    (ht0 : ∀ n, t0 n < 1)
    (hscale : ∀ᶠ n in atTop,
      (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ (-τU))
    (ℓ : ℕ) (_hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ 2 * n0) :
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × (Fin ℓ → Bool) × (Fin ℓ → Zd d (sz.L n))) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2)
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n 0 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n 0)) (loopOf p.2.1 p.2.2)
          - (gridStep t1 t0 (gueGridK sz n0) n : ℂ) * ∑ j ∈ Finset.range p.1,
              genMatGUEOf d (sz.L n) (sz.W n) (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)
                (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω) (loopOf p.2.1 p.2.2)‖)
      (fun n p ω => Real.sqrt (gridTime t1 t0 (gueGridK sz n0) n p.1 - t1 n) *
          (⨆ j : Fin p.1, Real.sqrt ((((sz.size n : ℕ) : ℝ))⁻¹ *
            (etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n j))⁻¹ ^ 2 *
            RBM.Ind.loopMax d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
              (gueHBA sz g t1 t0 (gueGridK sz n0) n j ω))
              (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n j)) (2 * ℓ)))
        + (((sz.size n : ℕ) : ℝ) *
            etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ ℓ) 
-- RBM3D/BA/GUEDuhamelBA.lean:660-672
theorem Duhamel_step_decompBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} (hm : 0 < m.im) (hwf : I.WF) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    {j : ℕ} (hj : j < K n) (ω : PathΩ (sz.withLam 0)) (hgood : ω (j + 1) ∈ DuhamelGood (sz.withLam 0) n) :
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n (j + 1) ω))
        (ztOf m E (gridTime t1 t0 K n (j + 1))) I
        - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n j ω))
            (ztOf m E (gridTime t1 t0 K n j)) I
        - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n j)
            (gueHBA sz g t1 t0 K n j ω) I
      = GUEDuhamelBA_Zinc sz g t1 t0 K n E m I j ω + GUEDuhamelBA_Yst sz g t1 t0 K n E m I (j + 1) ω
        - DuhamelB (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n)
            (gueHBA sz g t1 t0 K n j ω)
        + GUEDuhamelBA_r sz g t1 t0 K n E m I j ω 
-- RBM3D/BA/GUEDuhamelBA.lean:680-694
theorem Duhamel_drift_remainder_aeBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (E : ℝ) (m : ℂ)
    (hm : 0 < m.im) (hm1 : ‖m‖ ≤ 1) {I : LoopIdx (Zd d (sz.L n))} (hwf : I.WF)
    (ht1 : 0 ≤ t1 n) (hst : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hk : k < K n) :
    ∀ᵐ ω ∂(Pgue (sz.withLam 0)),
      ‖(∫ y, loopL d (sz.L n) (sz.W n)
            (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω
              + GUEDuhamelBA_hflow sz n (gridStep t1 t0 K n / ((sz.size n : ℕ) : ℝ)) y))
            (ztOf m E (gridTime t1 t0 K n (k + 1))) I ∂(gueUnit (sz.withLam 0)))
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
              (ztOf m E (gridTime t1 t0 K n k)) I
          - (gridStep t1 t0 K n : ℂ) * genMatGUEOf d (sz.L n) (sz.W n) m E (gridTime t1 t0 K n k)
              (gueHBA sz g t1 t0 K n k ω) I‖
        ≤ 16 * ((I.length : ℝ) + 3) ^ 4 * (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ^ 4 *
            (1 + (etaOf m (gridTime t1 t0 K n (k + 1)))⁻¹) ^ (I.length + 4) *
              gridStep t1 t0 K n ^ ((3 : ℝ) / 2) 
-- RBM3D/BA/GUEDuhamelBA.lean:784-789
theorem Duhamel_azuma_ZBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} {lam : ℝ} (hlam : 0 < lam) (hv : 0 ≤ Duhamelv (sz.withLam 0) t1 t0 K n) (k : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue (sz.withLam 0)).real
        {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_Zst sz g t1 t0 K n E m I lam (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * lam))) 
-- RBM3D/BA/GUEDuhamelBA.lean:796-804
theorem Duhamel_azuma_YBA (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (m : ℂ)
    {I : LoopIdx (Zd d (sz.L n))} {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ j < K n, ∀ M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      M.IsHermitian → ∀ y,
      ‖DuhamelT (sz.withLam 0) n (GUEDuhamelBA_Phi sz t1 t0 K n E m I j) (Duhamelv (sz.withLam 0) t1 t0 K n) M y‖ ≤ b)
    {k : ℕ} (hk : k ≤ K n) {ε : ℝ} (hε : 0 ≤ ε) :
    (Pgue (sz.withLam 0)).real
        {ω | ε ≤ ‖∑ j ∈ Finset.range k, GUEDuhamelBA_Yst sz g t1 t0 K n E m I (j + 1) ω‖}
      ≤ 4 * Real.exp (-ε ^ 2 / (4 * (k * (4 * b ^ 2)))) 
```
```
$ python3 stmt_diff.py   # band statement, renamed by the dictionary band -> BA (gueH -> gueHBA, zt -> ztOf, etaT -> etaOf, genMatGUE -> genMatGUEOf, gueScale/gueLmax/envConst written out, Pgue sz -> Pgue (sz.withLam 0), process names), vs the BA statement; token diff
== gueGrid_loop_duhamel (band) vs gueGrid_loop_duhamelBA (BA): 626 vs 626 tokens, ratio 1.000
== Duhamel_drift_remainder_ae (band) vs Duhamel_drift_remainder_aeBA (BA): 379 vs 379 tokens, ratio 0.997
  replace  band[Loop.LoopIdx] -> BA[LoopIdx]
== Duhamel_step_decomp (band) vs Duhamel_step_decompBA (BA): 360 vs 351 tokens, ratio 0.931
  replace  band[he] -> BA[hm]
  replace  band[| e |] -> BA[0]
  replace  band[2] -> BA[m.im]
  delete   band[) ( ht1 : 0 ≤ t1 n] -> BA[]
== Duhamel_azuma_Z (band) vs Duhamel_azuma_ZBA (BA): 156 vs 157 tokens, ratio 0.895
== Duhamel_azuma_Y (band) vs Duhamel_azuma_YBA (BA): 234 vs 235 tokens, ratio 0.930
```
### (b4) Compiled nonempty instances (target 8; `d = 3`, `sz0`, namespace `RBM.BA.GUEDuhamelBAInst`; statements at the concrete data are at the `:` ranges, proof terms below)
```
-- Duhamel_step_decompBA_check: statement BA/GUEDuhamelBA.lean:848-861; proof term BA/GUEDuhamelBA.lean:861-864
  Duhamel_step_decompBA sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) (im_pos_I 0)
    (loop2_wf _ 0 1) (by norm_num) (by norm_num) (j := 0) (by norm_num) (0 : PathΩ (sz0.withLam 0))
    DuhamelA2Inst.zero_mem_good
-- Duhamel_drift_remainder_aeBA_check: statement BA/GUEDuhamelBA.lean:867-880; proof term BA/GUEDuhamelBA.lean:880-882
  Duhamel_drift_remainder_aeBA sz0 gI t1I t0I KI 0 0 (EI 0) (mI 0) (im_pos_I 0) (norm_le_I 0)
    (I := loop2 (sz0.L 0) 0 1) (loop2_wf _ 0 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
-- Duhamel_azuma_ZBA_check: statement BA/GUEDuhamelBA.lean:897-901; proof term BA/GUEDuhamelBA.lean:901-902
  Duhamel_azuma_ZBA sz0 gI t1I t0I KI 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) one_pos hv_I 3 zero_le_one
-- Duhamel_azuma_YBA_check: statement BA/GUEDuhamelBA.lean:938-942; proof term BA/GUEDuhamelBA.lean:942-944
  Duhamel_azuma_YBA sz0 gI t1I t0I KI1 0 (EI 0) (mI 0) (I := loop2 (sz0.L 0) 0 1) (b := bI) bI_nonneg hb_I
    (k := 1) le_rfl (ε := 1) zero_le_one
-- gueGrid_loop_duhamelBA_check: statement BA/GUEDuhamelBA2.lean:1033-1051; proof term BA/GUEDuhamelBA2.lean:1051-1054
  gueGrid_loop_duhamelBA sz0 (τU := 1 / 2) (by norm_num) 1 (g := gI) (E := EI) (t1 := t1I) (t0 := t0I) (m := mI)
    MarkovInst.sz0_size_tendsto_nat im_pos_I norm_le_I
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) hscale_I 2 (by norm_num) (by norm_num)
```
Data: `sz0` (`N_0 = 2,097,152`), the BA flow datum `(gI, EI, mI)` of `sz0` at every `n` (`BAflow_real`, `BAReal` at `κ = 1/2`: `0 < Im m`, `‖m‖ ≤ 1` by `BAm_norm_le_one`), `t₁ = 17/20 < t₀ = 9/10`, `K = 131072` (and `K = 1` for the `Ỹ` instance), the 2-loop `(+,-; 0, 1)` over `Z_4^3`, the zero path (in the truncation set, `DuhamelA2Inst.zero_mem_good`); main: `τU = 1/2`, `n₀ = 1`, `ℓ = 2`, `hsize` = `MarkovInst.sz0_size_tendsto_nat`, `hscale_I` proved (`η_{t₀} ≥ 1/20`, `N ≥ 400`, eventually). No hypothesis is left; `hb_I` is discharged by `GUEDuhamelBA_bddC2C_Phi` and `Duhamel_norm_T_le`.
### (b5) Greps, closure, name clash (`final_data.sh`, 14:32:56-14:32:58 UTC; all expected counts)
```
X1-C4 defs: 0
imports MainInd|TwistPins|Step6|TwistStep|TwistAvg: 0
TwistAvg names read: RBM3D/BA/GUEDuhamelBA.lean:0 RBM3D/BA/GUEDuhamelBA2.lean:0 
sz.lam (UBA-C1): RBM3D/BA/GUEDuhamelBA.lean:0 RBM3D/BA/GUEDuhamelBA2.lean:0 
sorry|admit|native_decide|axiom: RBM3D/BA/GUEDuhamelBA.lean:0 RBM3D/BA/GUEDuhamelBA2.lean:0 
Prop-valued new defs: RBM3D/BA/GUEDuhamelBA.lean:0 RBM3D/BA/GUEDuhamelBA2.lean:0 
GUEDuhamelBA.lean:6:import RBM3D.BA.GUEEq729BA GUEDuhamelBA.lean:7:import RBM3D.Universality.GUEPhase.DuhamelC GUEDuhamelBA.lean:8:import RBM3D.Chain.StepDecompGen GUEDuhamelBA2.lean:6:import RBM3D.BA.GUEDuhamelBA 
232 modules; BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg*) in closure: []
C1 regex (`c1.py`, ticket token list; `gueH`, `Pgue`, `filt`, `PathΩ` only at `sz.withLam 0`) over the 36 public declarations: 0 hits (the same script on the band `DuhamelC.lean` flags `zt`, `etaT`, `gueScale`, `gueH`)
git diff --name-only 19df37e2..HEAD:
RBM3D.lean RBM3D/BA/GUEDuhamelBA.lean RBM3D/BA/GUEDuhamelBA2.lean 
 3 files changed, 2008 insertions(+)
main(9e07cc2e): GUEDuhamelBA_hflow=0 GUEDuhamelBA_Phi=0 GUEDuhamelBA_Zinc=0 GUEDuhamelBA_Yst=0 GUEDuhamelBA_r=0 GUEDuhamelBA_Vp=0 GUEDuhamelBA_Zst=0 Duhamel_azuma_ZBA=0 Duhamel_azuma_YBA=0 Duhamel_step_decompBA=0 Duhamel_drift_remainder_aeBA=0 gueGrid_loop_duhamelBA=0 GUEDuhamelBAInst=0 
t/T2519(f44898b4): GUEDuhamelBA_hflow=0 GUEDuhamelBA_Phi=0 GUEDuhamelBA_Zinc=0 GUEDuhamelBA_Yst=0 GUEDuhamelBA_r=0 GUEDuhamelBA_Vp=0 GUEDuhamelBA_Zst=0 Duhamel_azuma_ZBA=0 Duhamel_azuma_YBA=0 Duhamel_step_decompBA=0 Duhamel_drift_remainder_aeBA=0 gueGrid_loop_duhamelBA=0 GUEDuhamelBAInst=0 
t/T2519b2(19df37e2): GUEDuhamelBA_hflow=0 GUEDuhamelBA_Phi=0 GUEDuhamelBA_Zinc=0 GUEDuhamelBA_Yst=0 GUEDuhamelBA_r=0 GUEDuhamelBA_Vp=0 GUEDuhamelBA_Zst=0 Duhamel_azuma_ZBA=0 Duhamel_azuma_YBA=0 Duhamel_step_decompBA=0 Duhamel_drift_remainder_aeBA=0 gueGrid_loop_duhamelBA=0 GUEDuhamelBAInst=0 
```
(`git grep -w` over `RBM3D/*.lean`, refs `main`, row a `t/T2519`, row b′ `t/T2519b2` at the hashes printed in the lines above; files of this row excluded; `loop2_wf` etc. exist only inside the namespace `RBM.BA.GUEDuhamelBAInst`.)
### (b6) Coverage as used, registry and scan, `TwistAvg*`, D1
- Coverage (ticket rows; `GUEDuhamelBA.lean` = `A`, `GUEDuhamelBA2.lean` = `B`): **6** path `gueH` -> `gueHBA`, `gueHBA_succ`, `gueHBA_isHermitian` (C4 a, merged): `A:741, 747, 759`. **8** drift `condExp_loop_drift_gue` (`Drift:1318`, read by `DuhamelA2:1008`) -> `condExp_loop_drift_gueBA` (`GUEEq729BA:488`, C4 b, merged): `A:750` (inside `Duhamel_drift_remainder_aeBA`), consumed at `B:981`. **13** flow datum: instances only, `BAflow_real` `A:835`, `BAm_norm_le_one` `A:840`. **14** padding `0 < g`: not needed (`g` is free in every public statement). **19** grid layer read by name: `gue_highProb_incr_le` `B:826`, `gueH_isHermitian/adapted/succ` `A:127, 133, 140`, `genMatGUEOf`; `DuhamelA1` through `Duhamel_Vp_le` `B:206`. **20** twelve band twins: three of them (`DuhamelA2` §7, `DuhamelB`, `DuhamelC`) are this row. Rows 1-5, 7, 9-12, 15-18, 21: other rows.
- Registry and scan: no `RBM3D/Test/Axioms.lean` line is assigned to row b and none was edited. My files define no `Prop`-valued def and no public result with a `Prop` premise (grep above: 0). Library built without my two imports (14:27:01 -> 14:28:09 UTC, `lake build RBM3D`, exit 0) and with them: `axiom audit: 15586 theorems, 4790 definitions` -> `15606 theorems, 4806 definitions`, 0 axioms; `premises found by scanning: 124 (borrowed 1, owed 51, structural 52, refuted 6, superseded 14)` and `registry: 2 borrowed + 115 owed + 143 structural + 7 refuted + 19 superseded` identical in both. New owedProps lines: none.
- `BA/TwistAvg*` names read: none (0 hits above; the 1a's plan for row b′ is not mine). V modules imported: none.
- D1 (i)-(v): (i) `hoff` is row b′ (target 7); (ii) vocabulary: row a; this row reads none of `GUEPathBoundsBA`, `BAKFam`, `BAPB`; (iii) K and positivity: not read; (iv) layout L1: two new BA leaves, no band file edited, no `private` deleted (C5S-C3 failed at the 1a: in place -1,059 / -160 against >= 500, `T2519-prove.md:86`, (a) `central.py` output); (v) `M`-local law: the Duhamel layer reads no local law.
### Narrative (design and findings)
1. Row b = target 6 (the BA loop Duhamel layer: `Duhamel_drift_remainder_aeBA`, `Duhamel_step_decompBA`, `Duhamel_azuma_ZBA`, `Duhamel_azuma_YBA`, and the endpoint `gueGrid_loop_duhamelBA`) and target 8 (instances). Nothing of row a is imported, so the merge order a -> b is not forced at the Lean level (only the `RBM3D.lean` import lines).
2. The band processes `DuhamelPhi/Vp/Zinc/Zst/Yst/r` are hard-wired to `gueH sz` and `zt e`. They are redone once, as `private` stem-prefixed definitions and lemmas, at a generic model `sz` and a Hermitian shift `A n` of the path (`A n + gueH sz …`, flow `ztOf μ e`); the public statements are the specialisations `sz := sz.withLam 0`, `A n := g Ψ_I` (`gueHBA` is `A n + gueH (sz.withLam 0) …` by `rfl`), one term each. The public processes `GUEDuhamelBA_Phi/Zinc/Yst/r/Vp/Zst` are written out at `gueHBA` (rule E: stem-prefixed).
3. Read by name: the generic band lemmas (`Duhamel_Z_re_im`, `Duhamel_integral_step`, `Duhamel_norm_T_le`, `Duhamel_norm_B_le`, `Duhamel_Vp_le`, `Duhamel_qv_le_crude`, `Duhamel_exists_level`, `gue_highProb_incr_le`, `gueHasCondSubgaussianMGF_linear`, `azuma_complex`); by `open private … from`: 13 band privates of `DuhamelA2`/`DuhamelB`, 21 of `DuhamelC`, and 15 of `GUEDuhamelBA` in `GUEDuhamelBA2`. No merged file edited, no `private` deleted.
4. BA mathematics that differs from the band: (i) `|E n| ≤ 2 - κ` becomes `0 < Im m n ∧ ‖m n‖ ≤ 1` (no `κ`); (ii) `Duhamel_grid_facts` has `‖z_{j+1} - z_j‖ = Δ`, which needs `‖mE E‖ = 1`; at BA it is `≤ Δ ‖m‖ ≤ Δ`, exactly what `Duhamel_Vp_le` takes (`hzd`); (iii) the `C²` class of the loop observable at `ztOf m E` is `hermTestFunLoopNOf` (`Chain/StepDecompGen:101`, needs `u < 1` only), so `Duhamel_step_decompBA` has no `0 ≤ t1 n`; (iv) the drift remainder is derived from `condExp_loop_drift_gueBA` by the freezing lemma `DuhamelA2_condExp_freezeC` (as the band does from `condExp_loop_drift_gue`); its a.s. bound enters the private generic main theorem as the hypothesis `hdr` and is supplied by `Duhamel_drift_remainder_aeBA` in `gueGrid_loop_duhamelBA`; (v) `gueLmax` is written inline, `RBM.Ind.loopMax … (2 * ℓ)`: row a's `gueLmaxBA` (branch `t/T2519` at `f44898b4`, `GUEProcBA.lean:127-129`) is by definition the same term with `l`, so row c may pass the conclusion by `exact`.
5. Statement audit: after the dictionary, `gueGrid_loop_duhamel` and `gueGrid_loop_duhamelBA` are token-identical (626/626); the drift remainder differs by one namespace token; the step decomposition and the Azuma tails differ in the binder header only (and `he -> hm`, `ht1` dropped, in the step decomposition). No hypothesis added or hidden, no structure field, no frozen signature changed, no `RBG_*` text read.
6. The new import beyond the C4 b / `DuhamelC` closure is `RBM3D.Chain.StepDecompGen` (84-module closure, T-lane, no V names); total closure 232 modules, none of `BA.(MainInd|TwistPins|Step6|TwistStep|TwistAvg*)`.
## (c) Verified Mathlib names (all `#check`ed, 0 errors, scratch `mathlib_names.lean`, last run 14:14 UTC; names written in new lines; the ported lines use the same names as the band files they copy)
`Real.rpow_neg`, `Real.sqrt_eq_rpow`, `inv_anti₀`, `Real.sqrt_pos`, `Real.mul_self_sqrt`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.sqrt_nonneg`, `mul_le_mul_of_nonneg_left`, `Complex.im_le_norm`, `Complex.norm_real`, `Real.norm_of_nonneg`, `norm_neg`, `norm_mul`, `Complex.conj_ofReal`, `Matrix.conjTranspose_smul`, `MeasureTheory.memLp_top_of_bound`, `Measurable.const_add`, `measurable_pi_iff`, `Filter.Eventually.of_forall`, `Filter.Tendsto.eventually`, `Filter.eventually_ge_atTop`, `MeasureTheory.ae_all_iff`, `MeasureTheory.measure_mono_null`, `MeasureTheory.Integrable.mono`, `Matrix.IsHermitian.add`; instance lines also use `Nat.lt_one_iff`, `div_nonneg`, `Nat.cast_nonneg`, `one_pos`, `zero_le_one`, `le_rfl`, `Real.exp_pos` (`#check` 0 errors, 14:30 UTC). Verified absent: none looked for.
## (d) Open issues and paper-delta candidates
- `T2519ba1`: the discrete Duhamel remainder of the GUE-phase loops is stated at the BA grid path `g Ψ_I + H_k` along `z_t = E + (1 - t) m` with `0 < Im m ∧ ‖m‖ ≤ 1` in place of `|E| ≤ 2 - κ`; the paper has no statement (the GUE phase is "essentially identical to [YY_25, Theorem 2.6]", `paper/tex/1_2_Intro_model_result.tex:566-570`).
- `T2519ba2`: `‖z_{j+1} - z_j‖ ≤ Δ ‖m‖` (equality only if `‖m‖ = 1`); only the inequality is used. `T2519ba3`: `Duhamel_step_decompBA` needs no `0 ≤ t1 n` (the `C²` bound of the loops needs `u < 1` only).
- Public surface: the ticket pins `Duhamel_drift_remainder_aeBA`, `Duhamel_step_decompBA` (target 6) and `gueGrid_loop_duhamelBA`; `Duhamel_azuma_ZBA`, `Duhamel_azuma_YBA` and the processes `GUEDuhamelBA_Phi/Zinc/Yst/r/Vp/Zst/hflow` are public because the ticket lists "the Azuma lines" under target 6 and the step decomposition needs the processes; all other generic pieces (telescope, `Z_bound`, pathwise, events, main, `bddC2C`, `grid_facts`) are `private`.
- Branch note for the hub: `t/T2519b` has the 1a probe `RBM3D/Probe/T2519Pins.lean` and row a's first commit in its history (stacking as instructed); the row's own diff is `git diff 19df37e2..t/T2519b` (3 files, (b5)); the probe is never merged.
- Open: (1) row c reads `gueGrid_loop_duhamelBA` with `hscale` at `etaOf (m n) (t0 n)` and `0 < Im m n`, `‖m n‖ ≤ 1` from `BAReal`; the identification with `gueLmaxBA` is by unfolding and is not re-checked on a merged tree. (2) No port from RBM1D/RBM2D: the twins copy the RBM3D band files (last change: `DuhamelA2` `168c9fd3`, `DuhamelB` `198f15c7`, `DuhamelC` `64fab291`, all on `main`); no RBM1D/RBM2D diff-stat applies.
