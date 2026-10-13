Prover model: claude-sonnet-5-5
# T2473b (T4s2b: `Chain/GridAssemblyGen`, target 7) -- prove report, stage 1b of the third row of T2473
Branch `t/T2473b` (stacked on `t/T2473`, probe `RBM3D/Probe/T2473Pins.lean` stays on it and is never merged); worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2473b`. Binding: Amend 1, Amend 2, supervisor 2351 T4S2-C2/C3, CONTROL H134 stop rule (`wc -l` at each section commit).

## (a) Math preflight
Not repeated here: the stage-1a material of this row is `docs/reports/T2473-prove.md` (a), (a″), (a‴) and `docs/reports/T2473-1a-audit.md`. Seconds after the first `date -u` of the stage (Tue Oct 13 02:32:38 UTC 2026) `ls docs/reports | grep T2473` printed `T2473-1a-audit.md T2473-audit.md T2473-prove.md`: no `T2473b-prove.md` existed, so this file has no section (a) of its own.

## (a′) Preflight corrections -- Tue Oct 13 03:06:47 UTC 2026
One route correction, no verdict change. (a) (i) row `(1+(1-u)^{-1})^k` and the ticket (target 7) say the coarse bound follows from K2 (`0 ≤ v ≤ w < 1`). The pin `GridAssemblyHypNg` has `0 ≤ u i < 1` for `i ≤ K` and no order between `u (j+1)` and `u m`, so K2 does not apply. K3 gives it for any `0 ≤ v, w < 1`: `Σ_b ‖uKer_{v,w}(a,b)‖ ≤ 1 + |w - v| (1 - w)^{-1} ≤ 1 + (1 - w)^{-1}` (`GridAssemblyGen_row_le`, private, `RBM3D/Chain/GridAssemblyGen.lean:225`; the same `|w - v| ≤ 1` step as band `gridAsm_norm_uKer_le`, `GridAssemblyN:586`). The kernel class is still T2471's single text `GridRepTailGen_Ker`; nothing is added.

## (b) Script output
Merge of `main` first: commit 2bb389f1 (merge of main 1e73b1b8). The only conflict was `RBM3D/Test/Axioms.lean` (T4s2a's registry lines on both sides); it was resolved by taking main's file (`git diff main -- RBM3D/Test/Axioms.lean | wc -l` printed 0; `git diff main --stat` then listed only the probe file).
```
$ TZ=UTC git log --format='%h %cd %s' -3
ce109b72 Tue Oct 13 02:52:08 UTC 2026 T2473b: GridAssemblyGen band bridges, band corollaries and compiled instances (target 7)
6105217c Tue Oct 13 02:43:20 UTC 2026 T2473b: GridAssemblyGen pins, measurability of Z/Y, stoppedAzumaZNg, assembledNg (target 7; no instances yet)
2bb389f1 Tue Oct 13 02:33:09 UTC 2026 T2473b: merge main (T4s2a merged, T2478) into t/T2473b
$ date -u; git log --oneline -1; wc -l (stop size 2,000 per file)
Tue Oct 13 03:00:14 UTC 2026
ce109b72 T2473b: GridAssemblyGen band bridges, band corollaries and compiled instances (target 7)
    1197 RBM3D/Chain/GridAssemblyGen.lean
$ wc -l at the first section commit (6105217c)
     838
$ lake build RBM3D.Chain.GridAssemblyGen | tail -2; warnings from the file
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3863 jobs).
0
$ lake env lean axioms_mine.lean  (#print axioms of the 17 public declarations of the file)
  17 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean root_check.lean > root_check2.out; echo exit=$?; head -1 root_check2.out    (03:05:33-03:06:42 UTC; RBM3D.lean + import RBM3D.Chain.GridAssemblyGen + #assert_rbm_axioms; identical to the 02:52 run)
root_check exit=0
axiom audit: 14377 theorems, 4526 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ diff root_base.out root_check.out    (root_base.lean = RBM3D.lean unchanged, run 02:55-02:56 UTC)
1c1
< axiom audit: 14348 theorems, 4517 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
---
> axiom audit: 14377 theorems, 4526 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
diff-exit=1 (only the theorem/definition counts differ)
$ lake env lean inst_ax.lean   (scratch copy: the 8 examples renamed inst3_1..8, the private instance theorem made public; #print axioms of the 9)
   9 depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean names3.lean | grep -c error     (37 `#check` lines of the Mathlib names of (c))
0
$ date -u
Tue Oct 13 03:01:23 UTC 2026
$ grep -nE "def .*[Kk]er|def Ugen" ; grep -n STGridRepNgL ; grep -n "^import RBM3D.BA" ; grep -nE "InitMem|zero_mem_goodSet" ; grep -nwE "sorry|admit|native_decide|axiom"   (the file)
(no hit: exit=1)
$ grep -nE "withLam|BAflowLam0|gK" (the file)
79:increment is `ZfamNg` (`Cm.Hpath`); the theorem is the band `azumaSubGN` at `sz.withLam g` under `StepDecompGen_WalkForm`
282:`StepDecompGen_WalkForm Cm lam' Ψ` (the carrier walk is `Ψ n + pathH (sz.withLam lam')`, adapted to the coordinate filtration),
318:  exact hT.comp (pathH_measurable_filt (sz.withLam lam') s t K n j)
1162:  AbCN (sz0.withLam sz0.lam) s0 t0 K0 0 0 (loopFamNgShift Cm0 Ψ0 s0 t0 K0 0 0 σ3) U3 b3 (fun _ => 0)
1165:    AbCN (sz0.withLam sz0.lam) s0 t0 K0 0 0 (loopFamNgShift Cm0 Ψ0 s0 t0 K0 0 0 σ3) U3 b3 ω = A₀3 := by
$ python3 x1c1_3.py  (hypothesis-rule grep of the ticket, hit lines classified)
docstring: L22,31,32,65,117,123,195,206,251,252,282,292,310,390,845,863,872,916
W / LoopForm unfolding (proof): L316,318,325
band bridge / band corollary: L846,885,886,926,930,956
band instance: L1051,1054,1072,1166
hits in generic statement text: 0
$ grep -n "^open private" -A3 (the file) ; line of each opened private in GridAssemblyN
open private gridAsm_measurable_deriv_zero gridAsm_loopL_line_regular gridAsm_azuma_step gridAsm_mart_moment4
  gridAsm_norm_pow4_le_re_im gridAsm_zBudget gridAsm_moment4_budget_le gridAsm_yBudget gridAsm_card_label
  from RBM3D.Induction.GridAssemblyN
708:private theorem gridAsm_measurable_deriv_zero {α : Type*} [Measura
812:private theorem gridAsm_loopL_line_regular (d L W : ℕ) [NeZero L] 
475:private theorem gridAsm_azuma_step {X : ℕ → Ω' → ℂ} {m : ℕ}
411:private theorem gridAsm_mart_moment4 (d : ℕ → Ω' → ℝ) (v w : ℕ → ℝ
1196:private lemma gridAsm_norm_pow4_le_re_im (z : ℂ) : ‖z‖ ^ 4 ≤ 2 * 
1054:private theorem gridAsm_zBudget (k : ℕ) {ε : ℝ} (hε : 0 < ε) (D₁ 
1093:private theorem gridAsm_moment4_budget_le {K : ℕ} {Δ P : ℝ} (hΔ0 
1144:private theorem gridAsm_yBudget {N : ℝ} (hN2 : (2 : ℝ) ≤ N) (k : 
1578:private theorem gridAsm_card_label (n k : ℕ) :
$ python3 pindiff3.py  (definitions of the 8 pins vs the probe texts RBM3D/Probe/T2473Pins.lean, docstrings excluded)
IDENTICAL qvFormNg
IDENTICAL StoppedAzumaZNg
IDENTICAL AzumaSubGNg
IDENTICAL YMomentBoundsNg
IDENTICAL YMomentsConclNg
IDENTICAL YMomentsNg
IDENTICAL GridAssemblyHypNg
IDENTICAL AssembledNg
identical-def count: 8 of 8
$ python3 stmt3.py  (theorem statements extracted from the file)
253: theorem GridAssemblyGen_norm_UN_coarse {C : FlowFM sz} {n : ℕ} (hK : GridRepTailGen_Ker C n) {k : ℕ} (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) {X : (Fin k → Zd d (sz.L n)) → ℂ} {M : ℝ} (hM : 0 ≤ M) (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Zd d (sz.L n)) : ‖Step2Gen_UN C n σ v w X a‖ ≤ (1 + (1 - w)⁻¹) ^ k * M

363: theorem GridAssemblyGen_stronglyMeasurable_ZvecNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) : StronglyMeasurable[filt sz (j + 1)] (fun ω => ZvecNg Cm s t K n j σ ω)

372: theorem GridAssemblyGen_stronglyMeasurable_YvecNg (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool) : StronglyMeasurable[filt sz (j + 1)] (fun ω => YvecNg Cm s t K n j σ ω)

423: theorem stoppedAzumaZNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] {E lam' : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hL : StepDecompGen_LoopForm Cm E) (hW : StepDecompGen_WalkForm Cm lam' Ψ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedAzumaZNg Cm s t K

807: theorem assembledNg (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] : AssembledNg Cm

$ python3 inst3.py  (instances: statements of the 8 examples and of the private instance theorem, first 4 lines)
--- L938-963  (26 lines)
   example : sz.SizeTendsto → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
       D₁ + 4 * D + (k : ℝ) + 2 * C_P + 8 ≤ C_K →
       ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
         (Δ : ℝ) (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
   ...
--- L990-993  (4 lines)
   example : StronglyMeasurable[filt sz0 (2 + 1)]
         (fun ω => ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K 0 2 ![true, true, false] ω) ∧
       StronglyMeasurable[filt sz0 (2 + 1)]
         (fun ω => YvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K 0 2 ![true, true, false] ω) :=
--- L1002-1008  (7 lines)
   example (C : ℝ≥0) (hC : 0 < C)
       (hsub : ∀ j < Kg 0, SubGaussStopNg GridAssemblyGen_Cm ![true, true, false] (gridTime sInst vg Kg 0) (fun _ => Kg 0)
         (fun j ω => ZvecNg GridAssemblyGen_Cm sInst vg Kg 0 j ![true, true, false] ω) (Kg 0) (fun _ => 0) j C) :
       GridAssemblyGen_Cm.Pp.real {ω | 4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ)) ≤
   ...
--- L1023-1038  (16 lines)
   private theorem GridAssemblyGen_assembled_instance_gen (ε : ℝ) (hε : 0 < ε) (D D₁ C_P : ℝ)
       (hCK : D₁ + 4 * D + ((3 : ℕ) : ℝ) + 2 * C_P + 8 ≤ 17) (hCP : 0 ≤ C_P) :
       ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool)
         (Z : ℕ → PathΩ sz0 → (Fin 3 → Zd 3 (sz0.L n)) → ℂ) (cc : ℝ≥0), 0 < cc →
   ...
--- L1080-1090  (11 lines)
   example : ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz0),
       GridAssemblyGen_Cm.Pp.real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
       ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
         ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM n ![true, true, false] (gridTime sInst tInst gridAsm_K n 0)
   ...
--- L1100-1113  (14 lines)
   example : ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool) (cc : ℝ≥0), 0 < cc →
       (∀ m ≤ gridAsm_K n, ∀ (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ), j < m →
         SubGaussStopNg GridAssemblyGen_Cm σ (gridTime sInst tInst gridAsm_K n) (fun _ => gridAsm_K n)
           (fun j ω => ZvecNg GridAssemblyGen_Cm sInst tInst gridAsm_K n j σ ω) m a j cc) →
   ...
--- L1121-1123  (3 lines)
   example (σ : Fin 3 → Bool) (M : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ)
       (a : Fin 3 → Zd 3 (sz0.L 0)) :
       RBM.Ind.qvFormN sz0 0 (gridAsm_E 0) 0 (1 / 16) σ M a = qvFormNg GridAssemblyGen_Cm 0 0 (1 / 16) σ M a :=
--- L1127-1129  (3 lines)
   example (X : (Fin 3 → Zd 3 (sz0.L 0)) → ℂ) (a : Fin 3 → Zd 3 (sz0.L 0)) (hX : ∀ b, ‖X b‖ ≤ 1) :
       ‖Step2Gen_UN GridAssemblyGen_Cm.toFlowFM 0 ![true, true, false] (1 / 16) (1 / 32) X a‖ ≤
         (1 + (1 - (1 / 32 : ℝ))⁻¹) ^ 3 * 1 :=
--- L1173-1177  (5 lines)
   example (x : ℝ) (hx : 0 ≤ x) :
       Cm0.Pp.real {ω | x ≤ ‖∑ j ∈ Finset.range (min 1 ((fun _ : PathΩ sz0 => K0 0) ω)),
           Step2Gen_UN Cm0.toFlowFM 0 σ3 (gridTime s0 t0 K0 0 (j + 1)) (gridTime s0 t0 K0 0 1)
             (ZvecNg Cm0 s0 t0 K0 0 j σ3 ω) b3‖} ≤
   ...
examples + instance theorem: 9
$ clash3.sh  (git grep -w of 17 new public names + stems GridAssemblyGen, GridAssemblyGenCheck in RBM3D/ and RBM3D.lean, main + 93 other t/T24* branches; Probe file of t/T2473 excluded)
(done)
       2
$ git diff main...HEAD --name-only ; forbidden-file diff lines ; importers of GridAssemblyGen
RBM3D/Chain/GridAssemblyGen.lean
RBM3D/Probe/T2473Pins.lean
       0
(importers: exit=1)
$ ports: RBM1D/RBM2D
none copied from ../RBM1D or ../RBM2D; source = RBM3D/Induction/GridAssemblyN.lean at 686cf716 (main 78f4cc14)
```
Narrative.
(1) Delivered: `RBM3D/Chain/GridAssemblyGen.lean`, 1,197 lines against the stop size 2,000 (838 at the first section commit): the eight pins of target 7 (script diff above: all eight definitions identical to the probe texts `T2473Pins.lean:125-247`), the theorems `stoppedAzumaZNg` (`:423`), `assembledNg` (`:807`), `GridAssemblyGen_stronglyMeasurable_ZvecNg` / `_YvecNg` (`:363`, `:372`), the helper `GridAssemblyGen_norm_UN_coarse` (`:253`), the band bridges `bandStep2_qvFormN`, `bandStep2_YMomentBoundsN`, `bandStep2_GridAssemblyHypN` and the band corollary `stoppedAzumaZN_of_Ng`. Target 6 is T2474's, targets 8-10 are T4s2c's; `AzumaSubGNg` and `YMomentsNg` are statements here and are proved there.
(2) Hypotheses: `assembledNg` takes only `[IsProbabilityMeasure Cm.Pp]` (the probe binder); the kernel class is the bundle field `hKer`. `stoppedAzumaZNg` and the two measurability theorems take `StepDecompGen_LoopForm Cm E` and `StepDecompGen_WalkForm Cm lam' Ψ` (D2 (1): W and the compat; T2474's merged texts, no new named `Prop`): the carrier walk is adapted through `hW`, `Cm.LM` is measurable through `hL`. No hypothesis was added to a pin or a target, no signature changed.
(3) Proofs are the band proofs with `Ugen` replaced by `Step2Gen_UN Cm.toFlowFM n`, `pathP sz` by `Cm.Pp`, the coarse bound by K3 ((a′)); the Carathéodory measurability of `loopDerivN` is redone at the spectral value `ztOf (Cm.m n) (E n) u` (`GridAssemblyGen_measurable_loopDerivZ`) on top of the opened private `gridAsm_measurable_deriv_zero`, `gridAsm_loopL_line_regular`.
(4) One `open private` declaration (9 model-free helpers of `GridAssemblyN`, lines in the output above); none for a BA reading. No `BA/*` import, no initial-membership statement (supervisor 2351 T4S2-C2/C3: grep prints nothing), no `STGridRepNgL`, no kernel definition.
(5) `bandStep2_qvFormN` is proved from K4 (`gridRepTailGen_ker_band`) with `|E n| ≤ 2`, `0 ≤ w < 1`; it needs no `NQGood1` import (the probe used `|w| < 1` through `qvFormN_eq_re_UgenPairN`).
(6) Band corollaries. `stoppedAzumaZN_of_Ng` is the merged `StoppedAzumaZN sz E s t K` in full. For `AssembledN` the example at `:938` is the `E n`-slice (the band pin quantifies `E : ℝ` inside `∀ᶠ n`, the generic pin is per carrier), converted through `bandStep2_GridAssemblyHypN` and `bandStep2_SubGaussStopN`; it is not the literal `AssembledN sz` (candidate T2473f).
(7) Instances (statements in the output above, all axioms standard): `:990` `ZvecNg`/`YvecNg` measurability at `n = 0`, `j = 2`; `:1002` `stoppedAzumaZNg` at `n = 0` (`N = 2097152`), grid `(sInst, vg, Kg)`, `k = 3`, proxy `C > 0`, tail `< 1`, with the sub-Gaussian family for `ZvecNg` (the output of `azumaSubGNg`, row T4s2c) as the only open hypothesis; `:1173` `stoppedAzumaZNg` with **no open hypothesis** (`m = 1`, step `j = 0`, sub-Gaussianity from T2474's `subGaussStopNg_zvecNg`); `:1023`/`:1080` `assembledNg` at `sz0`, window `(0, 1/16)`, `K_n = N_n^17`, `k = 3`, `D = D₁ = 1`, `C_P = 0`, `C_K = 17` (`1 + 4 + 3 + 0 + 8 = 16 ≤ 17`), `A_0 ≡ 1`, with the genuinely random witness `Z_j = √Δ Re tr X_{j+1}` whose `SubGaussStopNg` is the band `gridAsm_witSubGaussStop` through `bandStep2_SubGaussStopN` (no open hypothesis); `:1100` the same with `Z = ZvecNg` (sub-Gaussian family open, as above); `:1121` `qvFormNg` bridge, `:1127` the coarse bound at `v > w`.
(8) Registry: `root_check.lean` (a copy of `RBM3D.lean` with `import RBM3D.Chain.GridAssemblyGen`, then `#assert_rbm_axioms`) exits 0 with 0 axioms; its output differs from the same run without the line only in the theorem/definition counts, so no new premise is reported and no line was added to `RBM3D/Test/Axioms.lean`. `RBM3D.lean` is not edited: CLAUDE.md §1 and §3 (A) 4 give the root import to the hub, as for T4s2a (the run prompt mentions the root import line; the hub adds `import RBM3D.Chain.GridAssemblyGen` after the last import line).
(9) Stop rules checked: file far below 2,000; no pin differs from the probe; no premise outside D2/(a)-(i); no new `FlowFM`/`Step2Mat` field, third kernel or `BA/*` import; none of `Induction/*`, `Path/*`, `BA/*`, `Chain/{Carrier,Step2Gen,Step2Kern,GridDuhamelGen,DecayGen,Step34Gen,StepDecompGen,Step2EventsGen,HierDriftGen,GridRepTailGen,GridRepTailGen2}` edited (diff line count 0). `main` moved to 78f4cc14 (T2480, T2483 merges) after my merge; none of the files I import changed (`git diff 1e73b1b8 main --name-only` has no hit on them).

## (c) Verified Mathlib names (all `#check`ed in `names3.lean`, 0 errors, 03:04 UTC; used in the file)
`Measurable.of_eval_matrix`, `Measurable.eval_matrix`, `Measurable.prodMk`, `Measurable.of_eval`, `Measurable.stronglyMeasurable`, `stronglyMeasurable_condExp`
`measureReal_mono`, `measureReal_union_le`, `measureReal_biUnion_finset_le`, `measureReal_iUnion_fintype_le`, `mul_meas_ge_le_integral_of_nonneg`
`integral_mono`, `integral_add`, `integral_const_mul`, `Finset.prod_univ_sum`, `Fintype.piFinset_univ`, `Finset.prod_le_prod₀`, `Finset.sum_ite_eq`
`Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.range_mono`, `Finset.stronglyMeasurable_fun_sum`, `continuous_finsetSum`, `pow_le_pow_left₀`, `pow_le_pow_iff_left₀`
`Real.rpow_nonneg`, `Real.one_le_rpow`, `Nat.card_Icc`, `ae_all_iff`, `MeasureTheory.ae_iff`, `MeasurableSet.const`, `Complex.norm_real`, `Real.norm_of_nonneg`
`div_le_div_of_nonneg_right`, `apply_ite`, `Matrix.one_apply`, `add_sub_cancel`, `ite_true`
Deprecated, not used: `if_true` (a warning in the first compile; `ite_true` is used). Verified absent: an instance `MeasurableSub₂ (Matrix ι ι ℂ)` (`chk1.lean`: `failed to synthesize`), so the difference of two matrix-valued maps is measurable entrywise (`Measurable.of_eval_matrix`, `Measurable.eval_matrix` with the filtration passed by `@`).

## (d) Open issues and paper-delta candidates
- Hub: add `import RBM3D.Chain.GridAssemblyGen` after the last import line of `RBM3D.lean` at merge. The five imports of the file (`GridDuhamelGen`, `StepDecompGen`, `GridRepTailGen2`, `DecayGen`, `Induction/GridAssemblyN`) are on `main` (`git cat-file -e main:<file>`); the `GridRepTailGen2` import is `T2473-prove.md` (a″) finding 1. Merge after T4s2a's audit PASS (T4s2a is on `main` since 86eb22f2). T4s2c (`AzumaProxyGen`: targets 8-10) imports this file and `GridGoodGen`.
- BA readings are statement level and were not compiled in this run: the BA source of `hKer` is `gridRepTailGen_ker_BA` (T2473-prove.md (a) table, merged T2471); the BA reading `AssembledNg (baStep2Mat ..)` typechecked in the probe (T2473-prove.md (a″), probe `:394-395`). The BA initial membership (target 9) is untouched and still the owed T4-BA item.
- T2473f: the pins `StoppedAzumaZNg` / `AssembledNg` are per carrier: the energy is the carrier's (`E` and `|E n| < 2` / `hE : |E| ≤ 2` are gone); the band `AssembledN` has `E : ℝ` inside `∀ᶠ n`, so its band corollary is the `E n`-slice (example `:938`).
- T2473g: the coarse kernel bound `(1 + (1 - u_m)⁻¹)^k` comes from K3, not K2 (K2 needs `v ≤ w`; the pin has no order on `u`); see (a′).
- T2473h: `stoppedAzumaZNg` and `GridAssemblyGen_stronglyMeasurable_*` carry `StepDecompGen_LoopForm` and `StepDecompGen_WalkForm`; the band theorems have no such hypothesis (the band loops and walk are fixed).
- T2473i: `bandStep2_qvFormN` has `|E n| ≤ 2`, `0 ≤ w < 1` (K4 window) instead of the probe's `|w| < 1`.
