Prover model: claude-sonnet-5-5
(a) Math preflight: not repeated; sections (a), (a′), (a″) of `docs/reports/T2519-prove.md` (stage 1a, probe `t/T2519` b992c2e7) and the 1a-audit `docs/reports/T2519-1a-audit.md` (PASS under Amend 3, CONTROL H326 (2)) stand. This stage adds no (a′) correction.
## (b) Row b′, stage 1b (`prover-max`, claude-sonnet-5-5) — written Fri Oct 16 15:50:14 UTC 2026 (`date -u`)
Ticket T2519, row b′ (target 7 `gueGrid_twistBA` and its instance): new `RBM3D/BA/GUETwistBA.lean` (steps 1-3, vocabulary, PB interface), `RBM3D/BA/GUETwistBA2.lean` (steps 4-5, the theorem, the instance), `RBM3D.lean` (2 import lines after the last import). Branch `t/T2519b2`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2519b2`, stacked on row a's first commit `19df37e2`; head `ee2e973c`. Scratch `<S>` = scratchpad `T2519b2/` (not in the repository).
**Verdict: target 7 (`gueGrid_twistBA`) is proved, instanced at `d = 3`, built (both modules and the full library, `#assert_rbm_axioms` included) and committed; no stop rule of the ticket was hit** (no file over 2,000; no merged file or statement changed; no `private` deleted; no V module imported other than `BA/TwistAvgA2`, `BA/TwistAvgB` (Amend 3 item 3); no hypothesis added to the signed text). One consequence to book: the landed `wc -l` sum is above the row's landing line (see (d) 1).
### (b1) Commits, sizes, builds, axioms (script output)
```
$ TZ=UTC git log --format='%h %cd %s' --date=format-local:'%H:%M:%S UTC' 19df37e2..HEAD
ee2e973c 15:48:29 UTC T2519 row b': docstring of GUETwistBA_T names the probe's twTrBA as such (full lake build passes
912091df 15:29:09 UTC T2519 row b': lint cleanup, GUETwistBA_Good_of_loops (concludes the Good predicate for the axiom
2a5c84a0 15:18:53 UTC T2519 row b': BA/GUETwistBA2 steps 4-5, gueGrid_twistBA and its d = 3 instance, imports (WIP bef
6a93a541 14:48:50 UTC T2519 row b': BA/GUETwistBA steps 1-3 (Stein identity with a test function, moment identity, Hil
$ wc -l RBM3D/BA/GUETwistBA.lean RBM3D/BA/GUETwistBA2.lean; grep -c . <the two files>
    1799 RBM3D/BA/GUETwistBA.lean
    1080 RBM3D/BA/GUETwistBA2.lean
    2879 total
RBM3D/BA/GUETwistBA.lean:1621
RBM3D/BA/GUETwistBA2.lean:1015
$ python3 -c ...   # landed vs stop 2,000 and vs the landing line (Amend 2 items 5, 8)
file 1: 1799 / 2000 (headroom 201); file 2: 1080 / 2000 (headroom 920); sum 2879 vs landing line 2719 (= 1.67 x 1628): +160
```
```
$ lake build RBM3D.BA.GUETwistBA 2>&1 | grep -E 'GUETwistBA|error|Build completed'
Build completed successfully (4112 jobs).
$ lake build RBM3D.BA.GUETwistBA2 2>&1 | grep -E 'GUETwistBA|error|Build completed'
Build completed successfully (4114 jobs).
$ lake build   # full library, last run before the final commit: 15:47:07 -> 15:48:20 UTC, exit 0 (`date -u` before and after, tool log); log lines:
7730:info: RBM3D.lean:661:0: axiom audit: 15700 theorems, 4812 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7853:premises found by scanning: 125 (borrowed 1, owed 51, structural 53, refuted 6, superseded 14).
8016:Build completed successfully (4431 jobs).
$ lake build 2>&1 | tail -1   # rerun at report time (no-op)
Build completed successfully (4431 jobs).
```
```
$ python3 <S>/axioms.py   # '#print axioms' of the 127 public declarations of the two files (<S>/axioms.lean, <S>/axioms_out.txt)
127 declarations; 0 with an axiom outside {propext, Classical.choice, Quot.sound}; {('Classical.choice', 'Quot.sound', 'propext'): 126, ('propext',): 1}
$ grep -E "'RBM.BA.(gueGrid_twistBA|GUETwistBA_(time|step|good|Good_of_loops|moment_tail)|GUETwistBAInst.twist_sz0)'" <S>/axioms_out.txt
'RBM.BA.GUETwistBA_Good_of_loops' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBA_good' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBA_moment_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBA_time' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBA_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.gueGrid_twistBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBAInst.twist_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### (b2) Target statement, diff against the pin, instance (script output)
```
$ awk '/^theorem gueGrid_twistBA/{f=1} f{print NR": "$0} f && /:= by$/{exit}' RBM3D/BA/GUETwistBA2.lean
926: theorem gueGrid_twistBA (d : ℕ) : 3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
927:     ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (n0 : ℕ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ),
928:     Tendsto (fun n => sz.size n) atTop atTop → 4 ≤ n0 →
929:     (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
930:     (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) →
931:     (∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ : Bool) (a : Zd d (sz.L n)), Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ) →
932:     (∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)),
933:       I.WF → 2 ≤ I.length → I.length ≤ 4 →
934:       ‖Kt n s I‖ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) s)⁻¹ ^ (I.length - 1)) →
935:     GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt →
936:     StochDomAt (Pgue (sz.withLam 0)) sz.size
937:       (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
938:         ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
939:             Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
940:               Gres (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω)
941:                 (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) true y x -
942:           BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
943:       (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
944:         (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹) := by
$ <S>/diff_stmt.sh   # statement vs `git show b992c2e7:RBM3D/Probe/T2519Pins.lean | sed -n 79,98p` (`T2519_HoffBA`), `diff -w`, T2519_PathBoundsBA -> GUEPathBoundsBA
pin lines:       19, file-statement lines:       19
DIFF EMPTY (modulo whitespace; T2519_PathBoundsBA -> GUEPathBoundsBA)
$ diff -w <(probe T2519_PathBoundsBA, renamed) <(def GUEPathBoundsBA, BA/GUEProcBA.lean)   # the one substituted name
identical modulo whitespace (13 lines)
```
The compiled nonempty instance (`d = 3`; `sz0`: `L_0 = 4, W_0 = 32, N_0 = 2097152`, merged `sz0_values`, `Defs/Sizes.lean:267`; BA flow datum; window `[17/20, 9/10]`; `n₀ = 4`; `Kt = KtI` from `gueK_existsBA`). Discharged: `3 ≤ d`, `κ = 1/2 > 0`, `Λ = 10 > 0`, `Tendsto size` (`sz0_tendsto`), `4 ≤ n₀`, `0 < g_n ≤ 10` eventually (`BAflow_lam0_window`), `BAReal` at `κ = 1/2` for every `n` (`BAflow_real`), `0 ≤ t₁ ≤ t₀ < 1`, `Kt = m` on 1-loops (`GUETwistBA_Kt_one` from the clauses of `gueK_existsBA`). Open arrows (other gates' pins): the K-bound (conclusion form of row a's `Hyp_Kt_detDomBA`) and PB `GUEPathBoundsBA` (row c's `gueGrid_pathBoundsBA`). No `N = 0`, empty index set, collapsed window (`t₀ - t₁ = 1/20`) or `False` premise.
```
$ awk '/^theorem twist_sz0/{f=1} f{print NR": "$0} f && /hKb hPB$/{exit}' RBM3D/BA/GUETwistBA2.lean
1054: theorem twist_sz0
1055:     (hKb : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (t1I n) (t0I n), ∀ I : LoopIdx (Zd 3 (sz0.L n)),
1056:       I.WF → 2 ≤ I.length → I.length ≤ 4 →
1057:       ‖KtI n s I‖ ≤ ((sz0.size n : ℕ) : ℝ) ^ ε * (((sz0.size n : ℕ) : ℝ) * etaOf (mI n) s)⁻¹ ^ (I.length - 1))
1058:     (hPB : GUEPathBoundsBA sz0 gI EI t1I t0I mI (gueGridK sz0 4) 4 KtI) :
1059:     StochDomAt (Pgue (sz0.withLam 0)) sz0.size
1060:       (fun n (p : Fin (gueGridK sz0 4 n + 1) × Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) ω =>
1061:         ‖(((sz0.W n : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L n) (sz0.W n) p.2.1, ∑ y ∈ Iblk 3 (sz0.L n) (sz0.W n) p.2.2,
1062:             Mres (((gI n : ℝ) : ℂ) • PsiI 3 (sz0.L n) (sz0.W n)) (EI n : ℂ) (mI n) x y *
1063:               Gres (gueHBA sz0 gI t1I t0I (gueGridK sz0 4) n p.1 ω)
1064:                 (ztOf (mI n) (EI n) (gridTime t1I t0I (gueGridK sz0 4) n p.1)) true y x -
1065:           BAMss 3 (sz0.L n) (BAMB 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n)) true true p.2.1 p.2.2‖)
1066:       (fun n p _ => ‖BAMB 3 (sz0.L n) (gI n) (EI n : ℂ) (mI n) p.2.1 p.2.2‖ *
1067:         (((sz0.size n : ℕ) : ℝ) * etaOf (mI n) (gridTime t1I t0I (gueGridK sz0 4) n p.1))⁻¹) :=
1068:   gueGrid_twistBA 3 le_rfl sz0 (1 / 2) ((1 / 10 : ℝ)⁻¹) (by norm_num) (by norm_num) gI EI t1I t0I mI 4 KtI
1069:     (tendsto_natCast_atTop_iff.mp sz0_tendsto) le_rfl (BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) sz0 zSeq flow_sz0) real_I
1070:     (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
1071:     (GUETwistBA_Kt_one sz0 (by norm_num) (fun n _ I => (GUETwistBAInst_KtI_spec n).1 I)
1072:       (fun n _ s hs I hI h1 h2 => (GUETwistBAInst_KtI_spec n).2 s hs I hI h1 h2) real_I
1073:       (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num))
1074:     hKb hPB
$ sed -n '1021,1025p;1037,1040p' RBM3D/BA/GUETwistBA2.lean
abbrev gI : ℕ → ℝ := BAflowLam0 sz0 zSeq
abbrev EI : ℕ → ℝ := BAflowEs sz0 zSeq
abbrev mI : ℕ → ℂ := BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)
abbrev t1I : ℕ → ℝ := fun _ => 17 / 20
abbrev t0I : ℕ → ℝ := fun _ => 9 / 10
def KtI (n : ℕ) : ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ :=
  Classical.choose (gueK_existsBA 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (GUETwistBAInst_g_pos n)
    (show (0 : ℝ) < 1 / 2 by norm_num) (real_I n) (t1 := t1I n) (t0 := t0I n) (by norm_num) (by norm_num) (by norm_num) (4 * 4))
```
### (b3) Greps, name clashes, diff (script output)
```
$ python3 <S>/c1.py   # ticket C1 / X1-C4 / UBA-C1 / `sz.withLam 0` rules (T2519.md:78), docstrings and comments dropped
C1 regex hits (`SB d L g` with g != 0 counted; `SB d L 0` is allowed by the ticket rule): 0 | X1-C4 (def|abbrev|structure) hits: 0
sz.lam occurrences (code, comments dropped): [('GUETwistBA2.lean', 1032), ('GUETwistBA2.lean', 1033)]
gueH/Pgue/filt/PathΩ with next token: {('PathΩ', '(sz.withLam 0)'): 9, ('Pgue', '(sz.withLam 0)'): 17, ('Pgue', '(sz0.withLam 0)'): 1}
$ grep -cE '^import RBM3D\.BA\.(MainInd|TwistPins|Step6|TwistStep)' <the two files>; grep -n '^import' <the two files>
RBM3D/BA/GUETwistBA.lean:0
RBM3D/BA/GUETwistBA2.lean:0
RBM3D/BA/GUETwistBA.lean:6:import RBM3D.BA.GUEProcBA
RBM3D/BA/GUETwistBA.lean:7:import RBM3D.BA.GUEOneLoop
RBM3D/BA/GUETwistBA.lean:8:import RBM3D.BA.TwistAvgA2
RBM3D/BA/GUETwistBA2.lean:6:import RBM3D.BA.GUETwistBA
RBM3D/BA/GUETwistBA2.lean:7:import RBM3D.BA.TwistAvgB
$ grep -cE 'sorry|admit|native_decide|^axiom |^ *axiom ' <the two files>
RBM3D/BA/GUETwistBA.lean:0
RBM3D/BA/GUETwistBA2.lean:0
$ git grep -l -E 'GUETwistBA|gueGrid_twistBA' <the 559 other local branches; `git for-each-ref refs/heads` = 560> -- RBM3D RBM3D.lean   # name-clash scan of every new name (stem `GUETwistBA`, target, namespace `GUETwistBAInst`)
main:RBM3D/BA/GUEProcBA.lean
t/T2519:RBM3D/BA/GUEProcBA.lean
t/T2519b:RBM3D/BA/GUEProcBA.lean
t/T2519c:RBM3D/BA/GUEProcBA.lean
$ git grep -n -E 'GUETwistBA|gueGrid_twistBA' main -- RBM3D RBM3D.lean | cut -c1-120
main:RBM3D/BA/GUEProcBA.lean:25:  `gueGrid_twistBA`, row b′).
$ git grep -n -E '^[[:space:]]*(private )?(noncomputable )?(theorem|lemma|def|abbrev|structure|namespace) +[A-Za-z.]*(GUETwistBA|gueGrid_twistBA)' main t/T2519 t/T2519b t/T2519c -- RBM3D RBM3D.lean | wc -l   # declaration-level hits on the 4 refs that mention the names
       0
$ git diff --stat 19df37e2..HEAD
 RBM3D.lean                |    2 +
 RBM3D/BA/GUETwistBA.lean  | 1799 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/GUETwistBA2.lean | 1080 +++++++++++++++++++++++++++
 3 files changed, 2881 insertions(+)
$ git diff --stat main...HEAD   # also lists row a's first commit: row a was merged to main by files, not by ancestry (merge-base cabd9a3d)
 RBM3D.lean                 |    3 +
 RBM3D/BA/GUEProcBA.lean    |  133 ++++
 RBM3D/BA/GUETwistBA.lean   | 1799 ++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/BA/GUETwistBA2.lean  | 1080 ++++++++++++++++++++++++++
 RBM3D/Probe/T2519Pins.lean |  298 ++++++++
 RBM3D/Test/Axioms.lean     |    1 +
 6 files changed, 3314 insertions(+)
```
### (b4) Name-level tables (0149 :98): coverage as used, `BA/TwistAvg*` names, `open private` (script output)
```
$ lake env lean <S>/used.lean   # every `RBM3D.*` constant in the types/values of the two files' declarations (not defined in them), `module: names;` (prefixes `RBM.`, `BA.`, `Gauss.`, `Univ.GUEPhase.` dropped); constants used outside the two files: project (RBM3D.*) 154, Lean/Mathlib/Batteries 1351
BA.CombesThomas: BAct_rate; BA.EMn2BA: EMn2BA_SB_zero; BA.FlowPins: BAKsol, BAMres_fine_apply, BAflowEs, BAflowLam0, BAflowT0, BAmF, FlowPinsInst.BAm_zSeq, FlowPinsInst.flow_sz0, FlowPinsInst.mS_im_half, FlowPinsInst.sz0_lam_L, FlowPinsInst.sz0_lam_pos, FlowPinsInst.zSeq, FlowPinsInst.zSeq_im_pos; BA.GUEKPrim: gueK_existsBA, kTwoGUEBA; BA.GUEOneLoop: gueHBA, ol_gueHBA_eq, GUEOneLoop_H0_herm (private), GUEOneLoop_Mdata (private), GUEOneLoop_contract (private); BA.GUEProcBA: GUEPathBoundsBA; BA.GreenSchur: BAflow_lam0_window, BAflow_real; BA.GreenStab: baM_row_l1; BA.KInduct: baKsol_one; BA.MFixedPoint: BAMB, BAMsigma, BAMss, BAReal, BASelf, BAm, BAt0_pos, MFixedPointInst.mS;
BA.TwistAvgA2: TwistAvgA2_cs, TwistAvgA2_holder_nat, TwistAvgA2_lyap1, TwistAvgA2_lyap2, TwistAvgA2_root_pow_self; BA.TwistAvgB: TwistAvgB_S1 (private), TwistAvgB_expo (private), TwistAvgB_markov (private), TwistAvgB_union (private); BA.Ward: BAMB_row_sq_real, BAm_norm_le_one; Chain.ExpAvgGen: ExpAvgGen_G_cont (private), ExpAvgGen_G_norm (private), ExpAvgGen_Gres_blockMat (private), ExpAvgGen_Hb_herm (private), ExpAvgGen_resolvent_id (private), ExpAvgGen_sum_Eblk (private), ExpAvgGen_trG_bdd (private), ExpAvgGen_trace_expand (private); Defs.Block: SB, sum_SB_row; Defs.Lattice: Zd, card_Zd; Defs.RadialSum: expC;
Defs.Sizes: Iblk, Idx, Sizes, Sizes.L, Sizes.W, Sizes.W_pos, Sizes.lam, Sizes.neZeroL, Sizes.neZeroW, Sizes.size, Sizes.three_le_L, Sizes.withLam, SizesInst.sz0, SizesInst.sz0_tendsto, split, splitEquiv; Defs.StochDomAt: Sizes.one_le_size, StochDomAt, badSetAt; Gauss.BlockAnderson: PsiI; Gauss.DominationAt: GaussianProduct.Sample, GaussianProduct.law, GaussianProduct.stein; Gauss.FineModel: CoordF, Sizes.SeqCoord, Sizes.SeqΩ, Sizes.measurable_slice, Sizes.seqGvar, Sizes.slice, Xmat, coordinateMatrix, coordinateMatrix_isHermitian, gvarF, Ω;
Gauss.FlowCalculus: HflowBlock, continuous_matrixTrace, hasDerivAt_green_moving, norm_Eblk_le_inv_W_sq, norm_Gsig_le_inv_eta, norm_gloop_le_crude, norm_matrix_entry_le_opNorm; Gauss.LoopCoordinate: coordinateBlock, hasDerivAt_HflowBlock_update; Gauss.Model: Vtx; Graph.LWWeightExp: lwWx_Gres_conjTranspose; Green.EntryCore: green; Hierarchy.ContractionBasic: trace_mul_single_mul_single; Hierarchy.ContractionSecondLoop: sum_coordinateBlock_trace_pair; Loop.GLoop: Eblk, Eblk_apply, Eblk_isHermitian; Loop.GLoopFlow: Gres, Mres, blockMat, etaOf, loopL, loopOf, ztOf, ztOf_im; Loop.KLTree: KLloopOf; Loop.TreeRep: LoopIdx, LoopIdx.WF, LoopIdx.a, LoopIdx.length, LoopIdx.mk, LoopIdx.σ;
Path.Walk: PathΩ, gridStep, gridTime; Propagator.Pins: PropSpin; Universality.GUEPhase.Bootstrap: primRhsGUE; Universality.GUEPhase.Generator: mSigOf; Universality.GUEPhase.Grid: Pgue, Pgue_isProbabilityMeasure, gueGridK, gueGridK_ne_zero, gueUnitVar; Universality.GUEPhase.HypA: Hyp_primRhs_one (private); Universality.GUEPhase.OneLoop: olComb, olComb_measurable, olVar, ol_map_comb_slice, OneLoop_blockMat_Xmat (private), OneLoop_card_Zd (private), OneLoop_gloop_one (private), OneLoop_integrable_coord_smul (private), OneLoop_integrable_of_cont_bdd (private), OneLoop_sum_gue_block (private);
```
```
$ grep -oh 'TwistAvg[A-Za-z0-9_]*\|lwWx_[A-Za-z_]*\|TwistPins[A-Za-z0-9_.]*' <the two files> | sort | uniq -c   # every BA/TwistAvg* name read (Amend 3 item 3); `TwistPins` named: none
   3 lwWx_Gres_conjTranspose
   1 TwistAvg
   1 TwistAvgA2
   2 TwistAvgA2_cs
   1 TwistAvgA2_holder_nat
   1 TwistAvgA2_lyap1
   1 TwistAvgA2_lyap2
   1 TwistAvgA2_root_pow_self
   2 TwistAvgB
   4 TwistAvgB_expo
   3 TwistAvgB_markov
   5 TwistAvgB_S1
   3 TwistAvgB_union
$ grep -n '^open private' <the two files> | cut -c1-110   # private statements read; no `private` deleted, no BA/TwistAvg* file edited
RBM3D/BA/GUETwistBA.lean:44:open private ExpAvgGen_G_cont ExpAvgGen_G_norm ExpAvgGen_Hb_herm ExpAvgGen_trG_bdd
RBM3D/BA/GUETwistBA.lean:48:open private OneLoop_integrable_coord_smul OneLoop_integrable_of_cont_bdd OneLoop_
RBM3D/BA/GUETwistBA.lean:50:open private GUEOneLoop_contract GUEOneLoop_H0_herm GUEOneLoop_Mdata from RBM3D.BA
RBM3D/BA/GUETwistBA2.lean:39:open private TwistAvgB_S1 TwistAvgB_markov TwistAvgB_expo TwistAvgB_union from RB
RBM3D/BA/GUETwistBA2.lean:40:open private Hyp_primRhs_one from RBM3D.Universality.GUEPhase.HypA
RBM3D/BA/GUETwistBA2.lean:41:open private ExpAvgGen_G_cont ExpAvgGen_G_norm ExpAvgGen_Hb_herm ExpAvgGen_Gres_b
RBM3D/BA/GUETwistBA2.lean:43:open private OneLoop_blockMat_Xmat OneLoop_gloop_one from RBM3D.Universality.GUEP
RBM3D/BA/GUETwistBA2.lean:44:open private GUEOneLoop_H0_herm GUEOneLoop_Mdata from RBM3D.BA.GUEOneLoop
```
```
$ lake env lean <S>/closure.lean   # import closure (Amend 2 item 6): the transitive TwistPins is the accepted one; direct imports of the excluded modules: 0 (grep above)
modules in the import closure of RBM3D.BA.GUETwistBA2: 5651 (366 under RBM3D); matching MainInd|TwistPins|Step6|TwistStep: [RBM3D.BA.TwistPins]
BA.TwistAvg* modules in the closure: [RBM3D.BA.TwistAvgA, RBM3D.BA.TwistAvgA2, RBM3D.BA.TwistAvgB]
```
Coverage as used (ingredient -> Lean name (module) -> consumer; uses located by script in the files):
```
PB `lk k`, k = 1, 2, 4 (needs 4 ≤ n₀), and `localLaw` at the grid times -> `GUEPathBoundsBA` (BA/GUEProcBA §1, row a) -> `GUETwistBA_good` (`hPB.1` three times, `hPB.2` once)
K-bound (2 ≤ |I| ≤ 4) and `Kt = m` on 1-loops -> the premises `hKb`, `hKm` of the signed text -> `GUETwistBA_good`, `GUETwistBA_Good_of_loops`
one-time Gaussian law of `gueHBA … j` -> `ol_gueHBA_eq` (BA/GUEOneLoop), `olVar`, `olComb`, `ol_map_comb_slice` (GUEPhase/OneLoop) -> `GUETwistBA_time`
Stein formula, `∂G` -> `GaussianProduct.stein` (Gauss/DominationAt) -> `GUETwistBA_stein_F`; `hasDerivAt_green_moving` (Gauss/FlowCalculus) -> `GUETwistBA_hasDerivAt_G`
pair contraction Σ_c v_c tr(A B_c) tr(C B_c) -> `sum_coordinateBlock_trace_pair` (Hierarchy/ContractionSecondLoop), `OneLoop_sum_gue_block` (private) -> `GUETwistBA_pair_gvar`, `_pair_unif`
ℓ¹ row and |M^{(B)}_{ab}| ≤ 1 -> `baM_row_l1` (BA/GreenStab) -> `GUETwistBA_time`, `GUETwistBA_step`; `BAMB_row_sq_real`, `BAm_norm_le_one` (BA/Ward) -> `GUETwistBA_time`, `GUETwistBA_eta_pos_le`
bootstrap, Markov, exponent count, union -> `TwistAvgB_S1` (`_moment_tail`), `_markov` (`_moment_tail`), `_expo`, `_union` (`_step`) (private, `open private`); `TwistAvgA2_root_pow_self`, `_lyap1`, `_lyap2`, `_holder_nat` (`_moment_bound`), `TwistAvgA2_cs` (file 1)
identity t_{aq} - M^{(++)}_{aq} = M^{(B)}_{aq} T_{qa} -> `BAMres_fine_apply` (BA/FlowPins), `BAMss` -> `GUETwistBA_ident` (new)
instance only -> `gueK_existsBA` (`KtI`), `baKsol_one` (`GUETwistBA_Kt_one`), `Hyp_primRhs_one` (private), `BAflow_real`, `BAflow_lam0_window`, `flow_sz0`, `sz0_tendsto`, `sz0`
used downstream (not in this stage): `gueGrid_twistBA` is the `hoff` producer of the merged `gueGrid_expect_oneLoopBA` (BA/GUEOneLoop) through row d
```
### (b5) Registry and scan for the target (script output, then text)
```
$ git diff --stat 19df37e2..HEAD -- RBM3D/Test/Axioms.lean | wc -l   # registry file untouched by this row
       0
$ grep -n 'GUEPathBoundsBA' RBM3D/Test/Axioms.lean | cut -c1-90   # row a's structural registry line: the premise `hPB`
384:   `RBM.BA.GUEPathBoundsBA, -- BA twin of `GUEPathBounds` (T2519 row a, `BA/GUEProcBA`
$ grep -n '^def .*: Prop' <the two files> | cut -c1-90   # the `Prop` definitions of this row
RBM3D/BA/GUETwistBA.lean:1570:def GUETwistBA_Good (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : 
$ grep -n '^theorem GUETwistBA_Good_of_loops' RBM3D/BA/GUETwistBA.lean | cut -c1-90   # a theorem whose conclusion head is `GUETwistBA_Good`
1608:theorem GUETwistBA_Good_of_loops (sz : Sizes d) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {K : 
$ grep -n 'premises found by scanning' <S>/clone_full.txt   # merge simulation: clone of this worktree in scratch + main's GUEProcBA, GUEHypABA, GUEEntryGridBA, GUEDuhamelBA(2), RBM3D.lean, Test/Axioms.lean + the 2 import lines; `lake build`
7857:premises found by scanning: 125 (borrowed 1, owed 51, structural 53, refuted 6, superseded 14).
8020:Build completed successfully (4435 jobs).
```
Registry: no line is assigned to row b′ (Amend 2 item 1; the ticket's Registry paragraph names rows a, c, d); `RBM3D/Test/Axioms.lean` is untouched. Scan: the first full `lake build` of this stage (15:24:44 -> 15:25:06 UTC, exit 1, tool log) stopped at the `RBM3D` root with `error: RBM3D.lean:661:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`, `supersededProps`: [RBM.BA.GUETwistBA_Good]`: the one `Prop` definition of this row (hypothesis `hgood` of `GUETwistBA_time`, `GUETwistBA_step`) had no theorem with head `GUETwistBA_Good`. Remedy inside the two files: `GUETwistBA_Good_of_loops` (the pointwise half of `GUETwistBA_good`) concludes it; the next full build (15:27:04 -> 15:28:57, exit 0) lists no unclassified premise.
Ports: none. No text is copied from `../RBM1D` or `../RBM2D`, and no command of this stage read, built or ran anything there (checked by a search of the stage's tool calls); no RBM1D/RBM2D diff-stat.
### Narrative (≤ 40 lines)
- Route R1 (Amend 1 item 3) = Lemma T.7 (`docs/tickets/T2398-TL-proofs.md:64-78`) at the one-time Gaussian law of `gueHBA … j` (`law v`, `v_c = t₁ gvar_c + c₀ w_c`, `Ŝ = t₁ S^{(B)}(0) + σ`, `S^{(B)}(0) = 1`). File 1 = steps 1-3 with the vocabulary and the PB interface; file 2 = steps 4-5, the theorem, the instance (the ticket's split).
- File 1: Stein with a test function (`GUETwistBA_stein_F`, `_stein_defect`); `GUETwistBA_momentId`: `𝔼|T_{qa}|^{2p} = 𝔼[Σ_{p'} M_{qp'} D_{p'} (M_{p'a} + T_{p'a}) Φ_p(T_{qa}) + (p-1) R₁ T^{p-2} T̄^p + p R₂ |T|^{2p-2}]` for the twisted block trace `T_{qa} = W^{-d} tr(G Π_{qa}) - M^{(B)}_{qa}`; the derivative terms `R₁` (charges ++−−), `R₂` (+−+−) bounded by pair contraction and Hilbert-Schmidt Cauchy-Schwarz against 2- and 4-loops (`GUETwistBA_RB1`, `_RB2`); the envelope `‖T‖, ‖D‖, ‖R_i‖ ≤ 2N²η⁻³`; the PB interface `GUETwistBA_good`; the identity `GUETwistBA_ident`; the entrywise bound `GUETwistBA_Tm_le_entries`.
- File 2: the real recursion `X^{2p} ≤ C_M ρΛ (X^{2p-1} + X·X^{2p-1}) + (2p-1) A X^{2p-2} + (C_M + 2p)(E+1)^{2p+1} δ` at the maximiser over pairs (`GUETwistBA_moment_bound`), bootstrap `TwistAvgB_S1` and Markov (`_moment_tail`), one grid time (`GUETwistBA_time`: `P(s < |T_{qa}|) ≤ (C′ρ²Λ_j/s)^{2p}`), one size `n` (`GUETwistBA_step`), the theorem.
- Constants (as in the files): `ε = τ/4`, `ρ = N^ε`, `ρ² = N^{τ/2}`, `e = 32 n₀ + 64`, `p = ⌈(D + e + 3 + 4)/τ⌉`, `D′ = D + 12p + 7`, `C′ = (4p+2)(2C_M + 1) + 2` (`C_M` of `baM_row_l1`), `K = 2C_M + 1`, `w = ρ²`, envelope `E = 2N²(NΛ_j)³`; the numeric conditions (`2(2C_M+1) ≤ N^{τ/2}`, `C′^{2p} ≤ N²`, `(C_M+2p)3^{2p+1} N^{12p+5} N^{-D′} ≤ 1`, `N ≥ 2^e + 2`) hold eventually in `n` (`tendsto_rpow_atTop`, `Tendsto size`).
- Union: over `(j, a, q)`, at most `(K n + 1) N²` indices, `K n = (N+1)^e`; each term `≤ N^{-(D+e+5)}` (`TwistAvgB_expo`), plus `Pgue B ≤ N^{-D′}` (`GUETwistBA_final_num`, `TwistAvgB_union`).
- Split at `Λ_j = N^{-τ}` (`Λ_j = (Nη_j)⁻¹`): for `Λ_j ≥ N^{-τ}` the entrywise `localLaw` gives `|T_{qa}| ≤ max|G - M| ≤ N^ε Λ_j^{1/2} ≤ N^τ Λ_j` (`GUETwistBA_triv`); for `Λ_j < N^{-τ}` the moment bound applies (`K ρ² Λ_j ≤ 1/2`, `Λ_j ≤ 1`, `Λ_j ≥ 1/N`).
- Every hypothesis of the signed text is a hypothesis of the theorem; none is added, none weakened; the statement is the pin's modulo the name `GUEPathBoundsBA` (diff above).
- D1 (i) holds as stated in Amend 1 item 3: R1 closes at `(Nη_u)⁻¹` from PB `lk 1, 2, 4` and `localLaw` at the same grid time, the K-bound at lengths 2 and 4, `Kt = m` on 1-loops, `BAReal` and `baM_row_l1`; no twisted 2-loop at `(Nη)⁻²`, no `twTr` declaration (the one textual hit is a docstring naming the probe's `twTrBA`), no TL/V name beyond `BA/TwistAvg*`, no second change of `n₀`: no stop of Amend 1 item 4. UBA-C1: `sz.lam` occurs only in the private proof `GUETwistBAInst_g_pos` (lines 1032-1033), in no public statement.
- Sizes: 1,799 and 1,080 lines (both < 2,000, no stop); the sum is above the row's landing line, see (d) 1. `maxHeartbeats` is raised once (`GUETwistBA_time`, 1,600,000, with the comment the linter asks for).
- Merge: a clone of this worktree with main's rows a and b files and the two modules builds the full library (4435 jobs, audit passes, scan counts as above). The hub applies the row's own diff (3 files; `git diff main...HEAD` also shows row a's first commit, see above).
## (c) Verified Mathlib names
Checked by `grep` in `.lake/packages/mathlib` this stage (file:line), one line each:
```
Real.rpow_le_one_of_one_le_of_nonpos   Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:670
Real.one_le_rpow                       Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:678
Real.rpow_le_rpow_of_exponent_le       Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:617
Real.sqrt_eq_rpow                      Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:986  (√x = x ^ (1 / (2 : ℝ)))
tendsto_rpow_atTop (root namespace)    Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean:38
le_self_pow₀                           Mathlib/Algebra/Order/GroupWithZero/Basic.lean:505
ENNReal.toReal_le_of_le_ofReal         Mathlib/Basic/ENNReal/Real.lean:283
MeasureTheory.measureReal_def          Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:105
Set.mem_ofPred_eq                      Mathlib/Data/Set/Operations.lean:79  (`Set.mem_setOf_eq` is its deprecated alias, :81)
```
Verified absent or deprecated (first builds of this stage, now replaced): `Real.tendsto_rpow_atTop` (unknown constant; the name is the root `tendsto_rpow_atTop`); `if_true` -> `ite_true`, `Set.mem_setOf_eq` -> `Set.mem_ofPred_eq`, `push_neg` -> `push Not` (deprecation warnings).
Script (`<S>/names.lean`): the 319 distinct identifiers typed in the two files that resolve, in the file's namespaces/opens, to a declaration outside `RBM3D`: Mathlib 273, Init 42, Lean 4; the Mathlib ones (all resolve; both modules build):
```
AddCommMonoid Complex.abs_im_le_norm Complex.add_im Complex.mul_conj' Complex.norm_natCast Complex.norm_real Complex.ofReal_im Complex.ofReal_one Complex.ofReal_sum Complex.real_smul Complex.star_def Continuous ENNReal ENNReal.ofReal ENNReal.ofReal_add ENNReal.ofReal_le_ofReal ENNReal.toReal_le_of_le_ofReal Filter Filter.Eventually.of_forall Filter.Tendsto Filter.atTop Filter.eventually_ge_atTop Filter.map Finite
FiniteDimensional.proper_rclike Finset Finset.card_univ Finset.exists_mem_eq_sup' Finset.le_sup' Finset.mem_filter Finset.mem_univ Finset.mul_sum Finset.single_le_sum Finset.sum_add_distrib Finset.sum_comm Finset.sum_congr Finset.sum_const Finset.sum_const_zero Finset.sum_eq_single Finset.sum_eq_zero Finset.sum_ite_eq Finset.sum_ite_eq' Finset.sum_ite_irrel Finset.sum_le_sum Finset.sum_mul Finset.sum_mul_sum Finset.sum_nbij'
Finset.sum_neg_distrib Finset.sum_nonneg Finset.sum_sub_distrib Finset.univ Fintype Fintype.card Fintype.card_fin Fintype.card_prod Fintype.ofFinite Fintype.sum_prod_type Function.update Function.update_eq_self HasDerivAt HasDerivWithinAt LinearMap.toContinuousLinearMap Matrix Matrix.IsHermitian Matrix.add Matrix.add_mul Matrix.comp Matrix.conjTranspose_apply Matrix.conjTranspose_conjTranspose Matrix.conjTranspose_mul
Matrix.conjTranspose_smul Matrix.diag_apply Matrix.diagonal_apply Matrix.diagonal_mul Matrix.ext Matrix.inv Matrix.map Matrix.mul_add Matrix.mul_apply Matrix.mul_assoc Matrix.mul_diagonal Matrix.mul_one Matrix.mul_smul Matrix.neg Matrix.neg_mul Matrix.nonsing_inv_eq_ringInverse Matrix.of Matrix.of_apply Matrix.one_apply Matrix.one_mul Matrix.single Matrix.single_apply Matrix.smul_apply Matrix.smul_mul Matrix.sub Matrix.sub_mul
Matrix.submatrix Matrix.submatrix_apply Matrix.trace Matrix.traceLinearMap Matrix.trace_add Matrix.trace_conjTranspose Matrix.trace_mul_comm Matrix.trace_neg Matrix.trace_smul Matrix.trace_sub Matrix.trace_sum Measurable MeasurableSet MeasurableSpace MeasureTheory.Integrable MeasureTheory.Integrable.of_bound MeasureTheory.IsProbabilityMeasure MeasureTheory.Measure MeasureTheory.integrable_const
MeasureTheory.integrable_finsetSum MeasureTheory.integral_add MeasureTheory.integral_congr_ae MeasureTheory.integral_const_mul MeasureTheory.integral_finsetSum MeasureTheory.integral_indicator_const MeasureTheory.integral_map MeasureTheory.integral_mono_of_nonneg MeasureTheory.integral_neg MeasureTheory.integral_nonneg MeasureTheory.integral_sub MeasureTheory.measurableSet_toMeasurable MeasureTheory.measureReal_def
MeasureTheory.measure_empty MeasureTheory.measure_mono MeasureTheory.measure_toMeasurable MeasureTheory.measure_union_le MeasureTheory.norm_integral_le_integral_norm MeasureTheory.subset_toMeasurable MeasureTheory.toMeasurable MulZeroClass.mul_zero MulZeroClass.zero_mul NNReal NNReal.coe_add NNReal.coe_mk NNReal.coe_mul NNReal.coe_one Nat.cast_le Nat.cast_nonneg Nat.cast_sub Nat.le_ceil Norm.norm Path Pi.add_apply Pi.mul_apply
Pi.sub_apply ProperSpace ProperSpace.isCompact_closedBall Real.mul_self_sqrt Real.norm_of_nonneg Real.one_le_rpow Real.rpow_add Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow_of_exponent_le Real.rpow_mul Real.rpow_natCast Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_pos_of_pos Real.self_le_rpow_of_one_le Real.sq_sqrt Real.sqrt Real.sqrt_eq_rpow Real.sqrt_le_sqrt Real.sqrt_mul Real.sqrt_one Real.sqrt_sq
Set Set.Icc Set.eq_empty_of_forall_notMem Set.indicator_of_mem Set.indicator_of_notMem Set.mem_ofPred_eq Star.star ZMod.card abs_nonneg abs_of_pos add_le_add add_le_add_left add_mul add_zero by_cases by_contra continuous_const continuous_finsetSum continuous_id div_eq_mul_inv div_le_one div_nonneg hasDerivAt_const integral_complex_ofReal inv_le_one_of_one_le inv_pow ite_and ite_mul le_abs_self le_max_left le_max_right le_of_eq
le_refl le_rfl le_self_pow le_trans lt_of_le_of_lt lt_of_lt_of_le lt_of_mul_lt_mul_left lt_of_not_ge mul_add mul_assoc mul_div_mul_right mul_inv_cancel mul_ite mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_le_of_le_one_left mul_neg mul_nonneg mul_nonneg_iff_of_pos_left mul_one mul_pos mul_pow mul_self_lt_mul_self mul_sub neg_mul norm_add_le norm_image_sub_le_of_norm_deriv_le_segment' norm_le_zero_iff
norm_mul norm_nonneg norm_num norm_pow norm_star norm_sub_le norm_sum_le norm_zero not_le not_lt nsmul_eq_mul one_div one_le_mul_of_one_le_of_one_le one_mul one_smul positivity pow_add pow_mul pow_ne_zero pow_nonneg pow_pos pow_succ pow_succ' smul_eq_mul smul_mul_assoc sq_nonneg star_mul' star_neg star_one star_zero sub_eq_zero sub_zero symm tendsto_rpow_atTop trans zero_add zero_le zero_le_one zero_smul
```
## (d) Open issues and paper-delta candidates
1. **Landing line (Amend 2 item 5).** Landed `wc -l` sum 2,879 (1,799 + 1,080) against row b′'s line 2,719 (= 1.67 × 1,628): +160. Non-blank lines 1,621 / 1,015 against the Amend 2 forecast ≈ 1,160 / 780. Both files are under 2,000. Per Amend 2 item 5 the row still goes to audit and merge, but no row that imports it (row d: `gueGrid_eq729BA` reads target 7) starts until the dispatcher answers; the short REQ is the dispatcher's.
2. **`GUETwistBA_Good_of_loops`** is a public lemma outside the ticket's list, added so that the library audit's scan finds a theorem concluding the `Prop` definition `GUETwistBA_Good` (see (b5)); no registry line is needed.
3. **Instance.** PB (`GUEPathBoundsBA`, row c) and the K-bound stay hypotheses of `twist_sz0` (the ticket allows it). The K-bound is the conclusion form of row a's `Hyp_Kt_detDomBA` (main `BA/GUEHypABA.lean:268`, merged 9e07cc2e), which this branch (stacked on row a's first commit) does not contain; after the merge a primed instance can discharge `hKb` (dispatcher's choice). The numeric check of the scales of the open arrows (K-bound scale, `C_M`, Monte Carlo of the twisted trace against `(Nη)⁻¹`) is the 1a's `(a)(ii)` (`T2519-prove.md:20-40`); this stage adds none.
4. **Consumer fit.** Row d passes `n₀ ≥ 4`, `Kt` the BA primitive family, PB at `n₀ ≥ 4` (row c, Amend 1 item 1 (a)) and `hKdet` cut from `2 ≤ |I| ≤ 2 n₀` to `|I| ≤ 4` by `omega`, as in the probe example (`T2519Pins.lean:233-242`). Amend 4 item 3: row b′ is unaffected (its window is already `∀ᶠ n, 0 < g n ∧ g n ≤ Λ`, `BAReal` at every `n`).
5. **Paper-delta candidates** (proposed; the dispatcher numbers them):
   - `T2519ba` (grid form of TL1): the twisted averaged law `|Tr(G̊_u P_{c1c2})| ≺ W^{-d} B_{u,0}` (Lemma T.7, `T2398-TL-proofs.md:64`) is proved at the grid times `j ≤ K n = (N+1)^{32 n₀+64}` simultaneously in `j` and the block pairs, for the weighted trace `t_{aq}` against `M^{(++)}_{aq}` with bound `|M^{(B)}_{aq}| (Nη_u)⁻¹`, from PB `lk` for `k = 1, 2, 4`, `localLaw`, the K-bound and `Kt = m` (T.7's inputs (I2), (I3) for `n ∈ {2, 4}`); extends `T2519a` (`n₀ = 4`).
   - `T2519bb` (bookkeeping): the moment order `p = ⌈(D + 32 n₀ + 71)/τ⌉` carries the union exponent of the grid (`gueGridK`); the paper has a continuous time.
   - `T2519bc` (proof structure): for `(Nη_u)⁻¹ ≥ N^{-τ}` the Lean proof uses the entrywise `localLaw` (`|T_{qa}| ≤ max|G - M| ≤ N^ε (Nη_u)^{-1/2} ≤ N^τ (Nη_u)⁻¹`); T.7's Step 5 absorbs `C_M W^ε W^{-d}B ≤ 1/2` from the window (`W^{-d}B_{u,0} ≤ W^{-𝔡}`), which `Λ_j < N^{-τ}` supplies here.
   - `T2519bd` (Lean bookkeeping, signed text): F1 `4 ≤ n₀` and F2 the guard `0 < g n →` on `Kt = m` (`Sizes.lam` is unsigned); the window is eventual in `n` (Amend 4 item 8).
## Repair (audit round 1 RETURN, `docs/reports/T2519b2-audit.md`; repairer claude-opus-5-5) — written Fri Oct 16 16:11:16 UTC 2026 (`date -u`)
Defect: the window `[17/20, 9/10]` of `twist_sz0` made the open premise `hKb` false (audit §3). Repair items 1-4 below; this section supersedes the instance window, line numbers and sizes in (b1), (b2), (b3) `sz.lam` line, the narrative's UBA-C1 and Sizes bullets, and (d) 1, 3.
```
$ TZ=UTC git log -1 --format='%h %cd' --date=format-local:'%H:%M:%S UTC'; git diff --stat ee2e973c aa49d4d3 | head -1
aa49d4d3 16:10:44 UTC
 RBM3D/BA/GUETwistBA2.lean | 126 ++++++++++++++++++++++++++++++++++++++++------
$ lake build RBM3D.BA.GUETwistBA …; lake build RBM3D.BA.GUETwistBA2 …   (| grep -E 'GUETwistBA|error|Build completed')
Build completed successfully (4112 jobs).
Build completed successfully (4114 jobs).
$ lake build   # full library, 16:09:19 -> 16:10:32 UTC, exit 0; log line 8016 (7730: axiom audit, 0 axioms in `RBM`; 7853: scan counts as in (b5))
Build completed successfully (4431 jobs).
$ lake env lean <S>/ax_r1.lean
'RBM.BA.gueGrid_twistBA' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GUETwistBAInst.twist_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
$ wc -l RBM3D/BA/GUETwistBA.lean RBM3D/BA/GUETwistBA2.lean | tr -s ' \n' ' '   # stop 2,000 each; landing line 2,719
 1799 RBM3D/BA/GUETwistBA.lean 1178 RBM3D/BA/GUETwistBA2.lean 2977 total
$ grep -nE '^(private )?abbrev (NI|xI|t0I|t1I)' RBM3D/BA/GUETwistBA2.lean   # item 1: row a's window (main GUEHypABA.lean:661-663)
1027:private abbrev NI (n : ℕ) : ℝ := ((sz0.size n : ℕ) : ℝ)
1028:private abbrev xI (n : ℕ) : ℝ := sz0.lam n ^ 2 / (4 * ((sz0.L n : ℕ) : ℝ) ^ 3)
1029:abbrev t0I (n : ℕ) : ℝ := 1 - xI n
1030:abbrev t1I (n : ℕ) : ℝ := t0I n - xI n / (2 * NI n)
$ grep -nE -A1 '^private theorem GUETwistBAInst_(hell|h730) :' RBM3D/BA/GUETwistBA2.lean   # item 2 (Hyp_Kt_detDomBA's premises, τU = 1/20)
1091:private theorem GUETwistBAInst_hell :
1092-    ∀ᶠ n : ℕ in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - t1I n) ≤ 2 * gI n ^ 2 := by
1115:private theorem GUETwistBAInst_h730 :
1116-    ∀ᶠ n : ℕ in atTop, t0I n - t1I n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)) * etaOf (mI n) (t0I n) := by
$ diff <(git show ee2e973c:<F> | awk '/^theorem twist_sz0/…/:=$/') <(awk … <F>) && echo …   # instance statement text (now line 1152)
twist_sz0 statement text unchanged vs ee2e973c
$ sed -n '1168p;1171,1172p' RBM3D/BA/GUETwistBA2.lean   # proof term 1166-1172: 1168 and 1171 changed; 1166-1167, 1169-1170, 1172 as before (item 3)
    GUETwistBAInst_t1_nonneg GUETwistBAInst_t10 GUETwistBAInst_t0_lt
      GUETwistBAInst_t1_nonneg GUETwistBAInst_t10 GUETwistBAInst_t0_lt)
    hKb hPB
```
- Window: `1 - t₀ = x_n = λ_n²/(4L_n³)`, `t₀ - t₁ = x_n/(2N_n)`; `0 ≤ t₁ ≤ t₀ < 1` by the private `GUETwistBAInst_t1_nonneg`, `_t10`, `_t0_lt`, which also feed `gueK_existsBA` in `KtI` (lines 1136, 1145). The private lemmas `GUETwistBAInst_L`, `_N`, `_x_pos`, `_x_le`, `_t0`, `_t1_nonneg`, `_t10`, `_t0_lt`, `_hell`, `_h730` are ports of row a's `GUEHypABAInst_*` (main `RBM3D/BA/GUEHypABA.lean:668-757`, merged in 9e07cc2e; RBM3D only, no RBM1D/RBM2D text).
- `hKb` stays a hypothesis: the branch base 19df37e2 has no `BA/GUEHypABA` (item 2, "otherwise"). At this data it is `Hyp_Kt_detDomBA`'s conclusion (τU = 1/20, n₀ = 4) cut from `≤ 2 * 4` to `≤ 4`; its deterministic premises are `GUETwistBAInst_h730`, `GUETwistBAInst_hell` above.
- UBA-C1: `sz0.lam` now also occurs in the private abbrev `xI` and in the private proofs at lines 1054, 1060, 1086-1087, 1097-1111; no public statement names it. No statement and no paper-delta changes. Sizes: 1,178 / 2,000 for file 2; the sum 2,977 is 258 lines above the 2,719 landing line (this supersedes (d) 1).
