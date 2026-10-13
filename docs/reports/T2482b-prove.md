Prover model: claude-sonnet-5-5
# T2482b (U5b-2: `RBM3D/BA/Step5IIIEdet2.lean`) - stage 1b prove report, written Tue Oct 13 05:33:04 UTC 2026
Stage 1b of U5b-2 (targets 6-7 and 8 (b)) on branch `t/T2482b`, stacked on `t/T2482` (e1cfd825), worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2482b`.  First `date -u` of the stage: Tue Oct 13 04:39:21 UTC 2026; `main` (268e07d4) was merged into the branch first (merge commit 75a9c3f0; the `date -u` just before the merge printed 04:39:54 UTC).

## (a) Math preflight
Not repeated here: `docs/reports/T2482-prove.md` (a) lines 2-77, (a″) lines 79-213 (probe step), and `docs/reports/T2482-1a-audit.md` (PASS; split confirmed in §6 item 3; the instance at `n = 800` fixed in §6 item 2).  `ls docs/reports | grep 2482` at the start of this stage listed `T2482-1a-audit.md`, `T2482-audit.md`, `T2482-prove.md` only, so this file is new and has no section (a) of its own.
## (a′) Preflight corrections
None: I found no mistake in (a) or (a″).  Two constants of (a) (i-b) are realised differently (narrative item 8); the loss still dominates them, proved in Lean (`Step5IIIEdet2_const_near`, `_const_far`).

## (b) Script output
Block 1 is `final_ev.sh` -> `final_ev.out` (scratchpad `T2482b/`), run after the last edit of the file; each `$` line states its command.  Lines longer than 200 columns are cut in this block only.
```
$ date -u; git log --first-parent --format="%h %s" e1cfd825..HEAD; wc -l (new file)
Tue Oct 13 05:32:26 UTC 2026
49b2de45 T2482: U5b-2 BA/Step5IIIEdet2 instances: far-regime concrete point, near-cut lemma
4b57edfa T2482: U5b-2 root import of BA/Step5IIIEdet2 (full lake build passed, #assert_rbm_axioms clean)
fda8a916 T2482: U5b-2 BA/Step5IIIEdet2 (targets 6-7, 8 (b): S_theta, dif cases (A)-(D), assembly, instances)
75a9c3f0 T2482b: merge main into t/T2482b (stacked on t/T2482)
    1277 RBM3D/BA/Step5IIIEdet2.lean
$ section sizes (lines between "## n." headings of the file)
1. Target 6 (a): the lattice sum `S_θ`                    L52   -98    47 lines
2. Scalar facts: the shift by `6ℓ*`, the floors, the b   L99   -190   92 lines
3. The legs of the six-loops of `dif`                      L191  -358   168 lines
4. The bridge `STeeMg` to explicit six-loops, and the re   L359  -495   137 lines
5. The pointwise bounds of the six-loop, cases (A)-(D)     L496  -691   196 lines
6. The sums over `c` of one six-loop                       L692  -863   172 lines
7. The final comparisons and the loss budget (E-c) for `   L864  -1055  192 lines
8. Target 6 (b): `res_deccalE_dif` (`3_5:2329`)            L1056 -1147  92 lines
9. Target 7: the assembly                                  L1148 -1175  28 lines
10. Instances (target 8 (b)): `d = 3`, `sz0`, `u = 1/2`,   L1176 -1277  102 lines
$ lake build RBM3D.BA.Step5IIIEdet RBM3D.BA.Step5IIIEdet2 2>&1 | tail -2; ... | grep -c "Step5IIIEdet2.lean" (warning/error lines of the new file)
build exit 0
info: RBM3D/Induction/HierAlgebra.lean:902:0: 'RBM.Ind.loopDrift_sub_K_deriv_n' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3851 jobs).
0
$ full lake build (RBM3D.lean with the import line), log head/tail:
start: Tue Oct 13 05:29:18 UTC 2026
info: RBM3D.lean:577:0: axiom audit: 14559 theorems, 4546 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
Build completed successfully (4345 jobs).
exit 0
6185:  RBM.BA.BAStep5IIIEMatrix: 21 [no certificate]
end:   Tue Oct 13 05:30:27 UTC 2026
$ python3 gen_ax.py (writes ax2.lean = #print axioms of every public theorem/def of the file, names2.lean = #check of every Mathlib-style identifier it uses); lake env lean names2.lean | grep -cE "unk ...
38 public declarations; 74 prefixed + 30 bare names
0
$ lake env lean ax2.lean | sed "s/^.*depends on axioms: //" | sort | uniq -c
  38 [propext, Classical.choice, Quot.sound]
$ python3 stmt2.py diff  (statements extracted from the file vs the pins of docs/tickets/checks/T2482-check.lean and vs t/T2459:RBM3D/Probe/T2459Pins.lean)
baStep5IIIE_sumTheta       L92    vs T2482_SumTheta         text-equal (body, whitespace-normalised): True
baStep5IIIE_dif            L1066  vs T2482_EdetDif          text-equal (body, whitespace-normalised): True
BAStep5IIIEdet             L1153  vs T2482_BAEdet           text-equal (body, whitespace-normalised): True
baStep5IIIEdet_holds       L1171  vs (= BAStep5IIIEdet d)   text-equal (body, whitespace-normalised): True
BAStep5IIIEdet             L1153  vs t/T2459 probe :134 (2a6ad6e0) text-equal (body, whitespace-normalised): True
$ lake env lean aud_ex.lean (the check pins + probe list/glue texts + examples: every target = its pin; BAStep5IIIEdet d = T2482_BAEdet d := rfl)
0
exit 0 (grep -c error above)
$ lake env lean docs/tickets/checks/T2482-check.lean (on the branch)
exit 0; error lines: 0
$ instances in the file (grep -n "^example")
1185:example : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
1191:example : ∀ d : ℕ, 1 ≤ d → ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ),
1197:example (H : Matrix (Idx 3 (SizesInst.sz0.L 800) (SizesInst.sz0.W 800)) (Idx 3 (SizesInst.sz0.L 800) (Siz
1207:example (H : Matrix (Idx 3 (SizesInst.sz0.L 800) (SizesInst.sz0.W 800)) (Idx 3 (SizesInst.sz0.L 800) (Siz
1247:example (H : Matrix (Idx 3 (SizesInst.sz0.L 800) (SizesInst.sz0.W 800)) (Idx 3 (SizesInst.sz0.L 800) (Siz
1268:example (H : Matrix (Idx 3 (SizesInst.sz0.L 800) (SizesInst.sz0.W 800)) (Idx 3 (SizesInst.sz0.L 800) (Siz
$ C1 grep 1; C1 grep 2; hygiene; UBA-C1 crossing grep; sz.lam reads
rc=1
rc=1
rc=1
rc=1
rc=1
$ git diff --stat main...HEAD; importers of the module
 RBM3D.lean                  |    1 +
 RBM3D/BA/Step5IIIEdet2.lean | 1277 +++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Probe/T2482Pins.lean  |  395 +++++++++++++
 3 files changed, 1673 insertions(+)
RBM3D.lean:574:import RBM3D.BA.Step5IIIEdet2
RBM3D/BA/Step5IIIEdet.lean:23:`S_θ`, the assembly) is `BA/Step5IIIEdet2.lean` (U5b-2).
$ hypothesis table: projections of the bundle read in the file (grep -no "hm\.[0-9.]*")
hm.1: L314 L340 L546 L684
hm.2.2.2.1: L212
hm.2.2.2.2.2.2.2.1: L315 L341
hm.2.2.2.2.2.2.2.2.1: L508
hm.2.2.2.2.2.2.2.2.2: L211
$ public declarations (theorem/def at column 0): count and the pinned ones with line numbers
38
92:theorem baStep5IIIE_sumTheta (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ : 0 <
1066:theorem baStep5IIIE_dif (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0
1153:def BAStep5IIIEdet (d : ℕ) : Prop :=
1171:theorem baStep5IIIEdet_holds (d : ℕ) : BAStep5IIIEdet d := fun hd
$ the proof terms of the instances (section Instances2 to the end of the file, only the applications; line numbers of the file)
1187:  obtain ⟨C, hC, h⟩ := baStep5IIIE_sumTheta 3 (by norm_num) (1 / 10) (by norm_num)
1192:    ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) ≤ C := baStep5IIIE_sumTheta
1195:discharged by `Step5IIIEdet_scalar_sz0_800`; the matrix part is the pin of U5c's good event (audit O2) and the near cut is the antecedent of
1203:  baStep5IIIE_dif 3 le_rfl SizesInst.sz0 _ _ 800 (1 / 2) 40 1 1 1 (1 / 10) 1 H (by norm_num) (by norm_num)
1204:    Step5IIIEdet_scalar_sz0_800 hmat σ a a' hnear
1218:  exact baStep5IIIE_dif 3 le_rfl SizesInst.sz0 _ _ 800 (1 / 2) 40 1 1 1 (1 / 10) 1 H (by norm_num) (by norm_num)
1219:    Step5IIIEdet_scalar_sz0_800 hmat σ a a (Step5IIIEdet2_near_self Step5IIIEdet_scalar_sz0_800 a)
1239:  have hx0 := Step5IIIEdet_log_ge_four Step5IIIEdet_scalar_sz0_800
1256:  have h := baStep5IIIE_dif 3 le_rfl SizesInst.sz0 _ _ 800 (1 / 2) 40 1 1 1 (1 / 10) 1 H (by norm_num) (by norm_num)
1257:    Step5IIIEdet_scalar_sz0_800 hmat ![true, false] Step5IIIEdet2_pt Step5IIIEdet2_pt
1258:    (Step5IIIEdet2_near_self Step5IIIEdet_scalar_sz0_800 _)
1271:  baStep5IIIEdet_holds 3 le_rfl SizesInst.sz0 _ _ 800 (1 / 2) 40 1 1 1 (1 / 10) 1 H (by norm_num) (by norm_num)
1272:    Step5IIIEdet_scalar_sz0_800 hmat
section Instances2 starts at L1178; examples: 6
$ naming rule (E): public theorem/def not pinned and not stem-prefixed; private declarations; open private
rc=1
4
41:open private lemDecCalE_zdistInf_sub_comm lemDecCalE_zdistInf_tri_real lemDecCalE_sum_zdist_le lemDecCalE_zdist_le_zdistInf from RBM3D.Path.LemDecCalE
```
Block 2: `python3 stmt2.py full`, the statements extracted from the file (docstrings excluded; whitespace-normalised; one line each):
```
[baStep5IIIE_sumTheta  L92] theorem baStep5IIIE_sumTheta (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ : 0 < θ) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (n : ℕ), ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ))) ≤ C
[baStep5IIIE_dif  L1066] theorem baStep5IIIE_dif (d : ℕ) (hd : 3 ≤ d) (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hθ : 0 < θ) (hCd : 0 < Cd) (hs : BAStep5IIIEScalar sz n u D Λ K₀ J) (hm : BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H) (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)) (hnear : ∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) : ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) * ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2)
[BAStep5IIIEdet  L1153] def BAStep5IIIEdet (d : ℕ) : Prop := 3 ≤ d → ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u D Λ K₀ J θ Cd : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), 0 < θ → 0 < Cd → BAStep5IIIEScalar sz n u D Λ K₀ J → BAStep5IIIEMatrix sz lam0 E n u D Λ K₀ J θ Cd H → (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STELKLKMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ * J ^ 2)) * STtailTD sz n u D a) ∧ (∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ‖STEGtMg (baStep2Mat sz lam0 E) n u H σ a‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 / 2 : ℝ)) * STtailTD sz n u D a)) ∧ (∀ (σ : Fin 2 → Bool) (a a' : Fin 2 → Zd d (sz.L n)), (∀ i : Fin 2, (zdistInf d (sz.L n) (a i - a' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) → ‖STeeMg (baStep2Mat sz lam0 E) n u H σ a a'‖ ≤ lossE2wG d (sz.L n) (sz.W n) Λ K₀ * (((sz.W n : ℕ) : ℝ) ^ (2 * (θ * (d * (Cd + 1)))) * ∑ y : Zd d (sz.L n), Real.exp (-(θ / 2 * Real.sqrt (zdistInf d (sz.L n) y : ℝ)))) * ((1 - u)⁻¹ * ((if (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) ≤ 6 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) then 1 else 0) + (((sz.W n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ ^ (1 / 2 : ℝ) * J ^ (3 : ℝ)) * STtailTD sz n u D a ^ 2))
[baStep5IIIEdet_holds  L1171] theorem baStep5IIIEdet_holds (d : ℕ) : BAStep5IIIEdet d
```
Block 3: name-clash grep of the new public names (`Step5IIIEdet2`, `baStep5IIIE_sumTheta`, `baStep5IIIE_dif`, `BAStep5IIIEdet`, `baStep5IIIEdet_holds`; `clash.sh`, `git grep -l -E` over every local ref but `t/T2482b`, `RBM3D` and `RBM3D.lean`; the 54 s run ended Tue Oct 13 05:18:45 UTC 2026 (mtime of `clash.out`); the prefix `Step5IIIEdet2` covers the two helpers added later):
```
HIT main: main:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2473c: t/T2473c:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2482: t/T2482:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2484b: t/T2484b:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2486: t/T2486:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2488: t/T2488:RBM3D/BA/Step5IIIEdet.lean 
HIT t/T2489: t/T2489:RBM3D/BA/Step5IIIEdet.lean 
refs scanned: 500; refs with hits: 7
$ git grep -n -E "<names>" <ref> -- RBM3D RBM3D.lean   (what the seven hits are, ref = main, t/T2473c, t/T2482, t/T2484b, t/T2486, t/T2488, t/T2489)
<ref>:RBM3D/BA/Step5IIIEdet.lean:23:`S_θ`, the assembly) is `BA/Step5IIIEdet2.lean` (U5b-2).      <- the same docstring line in all seven refs, no declaration
$ bash clash_wt.sh   # Tue Oct 13 05:09:46 - 05:14:30 UTC 2026 (every worktree RBM3D-wt/T24*, uncommitted files included; main worktree; the check files)
worktrees scanned (T24*, uncommitted files included): 237
main worktree RBM3D/ (outside BA/Step5IIIEdet.lean): none
docs/tickets/checks: T2482-check.lean:3 (header comment), T2485-check.lean:242 (comment: "the 1b then applies `BAStep5IIIEdet 3` (an exact-type hypothesis")
```
Block 4: hypothesis table.  Bundle conjunct -> the steps of this file that use it (lines of `RBM3D/BA/Step5IIIEdet2.lean` unless a first-half file is named):
- Hermitian `hm.1`: L314 L340 L546 L684 (`_glue5`, `_glue2`, `_loop_B`, `_loop_D`): the HS and glue bounds (target 2).
- (i) stopped control: only through `Step5IIIEdet_leg_long` (`BA/Step5IIIEdet.lean:505`) in (C), (D); (iii) far field of 𝒦 `hm.2.2.2.1`: L212 (`_leg_plus_dec`) and through `leg_long`.
- (v) `k = 2`: through `Step5IIIEdet_leg_short` (`BA/Step5IIIEdet.lean:486`), the two short legs of (B); `k = 4` `hm.2.2.2.2.2.2.2.1`: L315 L341 (the glued 4-loop `≤ Λ τ³`); `k = 6` `hm.2.2.2.2.2.2.2.2.1`: L508 (`_loop_A`).
- (vi) `hm.2.2.2.2.2.2.2.2.2`: L211 (`_leg_plus_dec`, hence `_leg_dec`, (B)).  Not read in this file: (ii) the `K₀` bound (read by no chain, finding F2 of (a)), (iv) `STavgMg` and (v) `k = 3` (read by `wG` in the first half).
- Scalar part: through the first-half lemmas `Step5IIIEdet_{W_pos, W_gt_one, tau_le_one, floor, floor_one, loss_ge, log_ge_four, one_le_J, one_le_Λ, u_lt_one}`; `0 < sz.lam n` and `J ≤ W^{1/2}` are not read (as in the first half; candidate T2482a).
Block 5: reuse census (merged lemma -> file:line, `grep -n` of this stage).  `Path/LemDecCalE`: `LemDecCalE_sum_tail_tail` :395, `LemDecCalE_e10a` :186, `LemDecCalE_e4c` :550, `LemDecCalE_tailT_anti` :515, `LemDecCalE_sum_zd_le` :314 (adapted); `open private` (L41 of the file): `lemDecCalE_zdistInf_sub_comm` :131, `lemDecCalE_zdist_le_zdistInf` :135, `lemDecCalE_zdistInf_tri_real` :140, `lemDecCalE_sum_zdist_le` :274.  `Path/LemDecCalEwG`: `lossE2wG` :74.  `Loop/GLoopFlow`: `loopM_eq_loopL` :127 (in the bridge).  `Defs/Tail`: `tailTD_nonneg` :177.  `BA/Step5IIIEdet` (U5b-1): `baStep5IIIE_loop_hs` :255, `baStep5IIIE_loop_glue` :264, `Step5IIIEdet_swap` :289, `_leg_short` :486, `_leg_long` :505, `_leg_long'` :866, `_floor` :357, `_floor_one` :391, `_loss_ge` :440, `_sum_split` :997, `_sqrt_le_self` :983, `_rpow_three_halves` :992, `_tail_eq` :399, `_tau_le_one` :350, `_W_pos` :328, `_W_gt_one` :332, `_log_ge_four` :434, `_one_le_J` :436, `_one_le_Λ` :432, `_u_lt_one` :431, `baStep5IIIE_lk` :582, `baStep5IIIE_wG` :1156, `Step5IIIEdet_scalar_sz0_800` :1417.  Not reused: `Path/LemDecCalEdif` §1 (as decided at the 1a).  Copies: the `STeeMg` bridge is the scratch `br2.lean` of (a″) P7 (`Step5IIIEdet2_STeeMg_eq`), the `S_θ` proof is `LemDecCalE_sum_zd_le` at the rate `θ/2`.  No RBM1D/RBM2D text is ported, so there is no diff-stat.
Block 6: UBA-C1 table.  Size level: this file reads no `sz.lam` (grep above, rc=1; the bundle of the first half reads it); kernel level: `baStep2Mat sz lam0 E` with `lam0 E` free, 𝒦 only through bundle (iii); crossing: no `lam0 ≤ sz.lam`, no `gK`, no `A` (grep rc=1).  Not triggered.  C1 greps rc=1, also in comments.  TN-C4: `STGridRepNgL` 0 hits.

Narrative (facts of this stage; the evidence is above).
1. Delivered: `RBM3D/BA/Step5IIIEdet2.lean`, 1,277 lines (stop line 2,000; the 1,800 reserve rule is not reached, `Step5IIIEdet3` unused), commits fda8a916 (file) and 49b2de45 (instances); the root import `import RBM3D.BA.Step5IIIEdet2` at `RBM3D.lean:574`, commit 4b57edfa.  Targets: 6 (a) `baStep5IIIE_sumTheta`, 6 (b) `baStep5IIIE_dif`, 7 `BAStep5IIIEdet`, `baStep5IIIEdet_holds`, 8 (b) 6 examples (section `Instances2` from L1178).
2. Statements: the four declarations are text-equal to `T2482_SumTheta`, `T2482_EdetDif`, `T2482_BAEdet`, and `BAStep5IIIEdet` equals `T2459_BAEdet` (`t/T2459:RBM3D/Probe/T2459Pins.lean:134`) up to the bundle names; `aud_ex.lean` (the check pins, the 1a-audit list/glue texts, `example : ∀ d, T2482_X d := ...` for targets 1, 2, 4, 5, 6, 7, `BAStep5IIIEdet d = T2482_BAEdet d := rfl`) elaborates with 0 errors.
3. `dif`, bridge: at `m = 2`, `S = 1`, `STeeMg` is `W^d Σ_c` of two six-loops with blocks `(a₀,a₁,c,a₁',a₀',c)`, `(a₁,a₀,c,a₀',a₁',c)` (`Step5IIIEdet2_STeeMg_eq`); the second loop is the first with the roles `0 <-> 1` swapped, so one lemma family serves both.  `_hs6` is target 2 at `k = 6`; `_glue5`, `_glue2` are `baStep5IIIE_loop_glue` at `p = 5, 2` (the glued 4-loop is `≤ Λ τ³` by (v)).
4. Cases, `c` in the ball of radius `3ℓ*` about `a₀` or `a₁` or outside: (A) `_loop_A`: `Λ τ⁵` by (v), `k = 6`.  (B) `_loop_B`: legs `(a₁,a₀)`, `(a₀',a₁')` `≤ Λ τ` by (v), `k = 2`; four long legs `≤ a₂ τ² (e^{-(θ/2)√r} + 2 (L^d)⁻¹)²` by `_leg_dec` ((vi), (iii), the floor `W^{-D} ≤ τ² L^{-2d}`), one decaying factor kept.  (C) `_loop_C`: glue at `c`; the four other legs satisfy `δ ≥ ℓ*` and `δ ≥ r - 6ℓ*` (`linarith` from the near cut, the ball and `r > 6ℓ*`), so each is `≤ 2 J e^{√6 Y} T(r)`.  (D) `_loop_D`: six long legs in three pairs, `_pt_pair`.
5. Sums: `_loop_sum_near` (valid for every `r`): `2 N₆ Λ τ⁵ + Λ τ (a₂² τ⁴ 27)(S_θ + 2)`; `_loop_sum_far` (`r > 6ℓ*`): `2 N₆ √(Λ τ³)(2 J E T)² + (2 J E)³ T (2 S_d + 1) τ² T` by `LemDecCalE_sum_tail_tail`; `N₆ = (2·3ℓ* + 1)^d`, `E = e^{√6 Y}`, `T = T_{u,D}(r)`; the ball has at most `2 N₆` points (`LemDecCalE_e10a`), the split is `Step5IIIEdet_sum_split`.
6. Comparisons: `_final_near` (indicator 1) and `_final_far` (indicator 0) are real-number lemmas.  E-c in Lean: `2 E² Λ (2 N₆ + 81 Λ²) ≤ lossE2wG` (`_const_near`) and `16 E³ (N₆ Λ + 2 S_d + 1) ≤ lossE2wG` (`_const_far`), `N₆ = (2·3ℓ* + 1)^d`, from `Step5IIIEdet_loss_ge` and `3√6 ≤ 8`; no fallback loss is needed.
7. Rule check: `J` enters only in (C), (D), each time with `√τ` (`_final_far`: `Ω √τ J³`); the indicator terms (A), (B) are `J`-free (`_final_near`).  No entry-level bound of the resolvent, no energy bound, no `M = m·1`, no band kernel, no 𝒦 bound at equal charges.
8. Differences from (a) (constants only, inside the loss): (B) keeps one decaying leg and bounds `e + 2 (L^d)⁻¹ ≤ 3` on the other three, giving `27 (S_θ + 2)` per loop (`S_θ ≥ 1` by the term `y = 0`) in place of (a)'s `16 S_θ`; every shift is bounded by the single `E = e^{√6 Y}` (all cuts are `≤ 6ℓ*`), total `E³ ≤ e^{8Y}`, in place of the per-leg shifts of (a).
9. Instances: `S_θ` at `d = 3`, `θ = 1/10` along `sz0` (all `n`); `dif` and the assembly at `n = 800` (`L = 3204`, `6ℓ* ≤ L/2`: every window nonempty, 1a-audit §6.2) with `Step5IIIEdet_scalar_sz0_800` (first half), `θ = 1/10`, `Cd = 1`, and the matrix part `hmat` a hypothesis (U5c's good event, audit O2): generic `(σ, a, a')` with the near cut as hypothesis, `a' = a` (`Step5IIIEdet2_near_self`), and the concrete far-regime point `σ = (+,-)`, `a = a' = (0, (1500, 0, 0))` with `|a₀ - a₁|_∞ = 1500` (`_pt_dist`, `decide`) and `6ℓ* < 1500` (`_pt_far`), whose statement carries the indicator `0`.
10. Registry: the full `lake build` with the import line ran 05:29:18 - 05:30:27 UTC, exit 0, 4345 jobs; `#assert_rbm_axioms` reports 0 axioms in `RBM` and no unclassified premise.  The premises of the new theorems are `BAStep5IIIEScalar` (concluded by the first-half witness theorems `Step5IIIEdet_scalar_sz0_one`, `_800`) and `BAStep5IIIEMatrix` (an `owedProps` line, `RBM3D/Test/Axioms.lean:239`); `BAStep5IIIEdet` is proved by `baStep5IIIEdet_holds`.
11. Scratch: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2482b/` (`parts/`, `assemble.sh`, `final_ev.sh`, `stmt2.py`, `clash.sh`, `clash_wt.sh`, `aud_ex.lean`, `ax2.lean`, `names2.lean`, `mkreport2.py`).

## (c) Verified Mathlib names
`names2.lean` (`#check @name` for the 104 identifiers the file uses, 74 with a namespace prefix and 30 bare lemma names; 0 unknown, 0 errors, block 1) covers, among others: `Real.sqrt_le_iff`, `Real.sq_sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_mul`, `Real.sqrt_sq`, `Real.sqrt_le_sqrt`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_eq_rpow`, `Real.sqrt_eq_zero_of_nonpos`, `Real.exp_le_one_iff`, `Real.exp_nat_mul`, `Real.exp_sum`, `Real.one_le_exp`, `Real.one_le_rpow`, `Real.rpow_mul`, `Real.rpow_two`, `Real.rpow_natCast`, `Real.rpow_nonneg`, `Real.rpow_le_rpow_of_exponent_le`, `Real.log_pow`, `Real.log_le_log`, `Finset.single_le_sum`, `Finset.sum_add_distrib`, `Finset.sum_comm`, `Finset.sum_pair`, `Finset.sum_ite_eq`, `Finset.prod_insert`, `Finset.prod_singleton`, `Finset.prod_univ_sum`, `Finset.card_le_card`, `Finset.card_union_le`, `Finset.sup_le`, `Fin.prod_univ_six`, `Fintype.sum_equiv`, `Fintype.piFinset_univ`, `Equiv.subLeft`, `ZMod.card`, `Matrix.one_apply`, `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `inv_le_one_of_one_le₀`, `le_mul_of_one_le_right`, `one_le_mul_of_one_le_of_one_le`, `one_le_pow₀`, `pow_le_pow_left₀`, `pow_le_pow_right₀`, `nsmul_eq_mul`.  Used by the far-regime instance: `Real.log_lt_log`, `Real.log_two_lt_d9`, `Real.log_pow`.  Verified absent: none needed.

## (d) Open issues and paper-delta candidates
1. Root import: `RBM3D.lean:574` is in commit 4b57edfa as the task asked; hub rule (A) 4 adds the same line at merge, so avoid a duplicate.  The probe `RBM3D/Probe/T2482Pins.lean` is still on the branch (never merged).
2. Bundle conjuncts not read by this half: (ii), (iv), (v) `k = 3`; `K₀` enters only through the loss; `0 < sz.lam n` and `J ≤ W^{1/2}` are read by neither half (candidate T2482a of the U5b-1 audit).
3. For U5c/U5d: `baStep5IIIEdet_holds d` gives the three ℰ-bounds from the two bundle parts; the matrix part is the hypothesis U5c concludes.  The constant of `S_θ` is `(1 + 96/(θ/(2d))⁴)^d`.  Per (a″) row (viii) the `dif` conjunct feeds (H1) of the merged `BAStep5IIITailSqQV` (`BA/Step5IIIKer2.lean:347`); I did not re-check that coupling in this stage.
4. Paper-delta candidates: none new.  Pending candidates this half falls under: T2459b (`res_deccalE_dif`, `3_5:2327-2335`: near cut `ℓ*` and indicator `4ℓ*` in the paper, `2ℓ*` and `6ℓ*` here), T2459c (Hilbert-Schmidt route), T2459f (the factor `W^{2θd(Cd+1)} S_θ`), T2482a (the cap `J ≤ W^{1/2}`), D437 (explicit loss in place of `≺`).  `S = 1` is the identity matrix of the carrier `baStep2Mat`, not a difference introduced here.
5. No stop rule of the ticket fired; no REQ trigger (file 1,277 lines; with the first half 1,493 the pair is 2,770 lines, below 3,600).
