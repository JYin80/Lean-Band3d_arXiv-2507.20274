Auditor model: claude-opus-5-5
# T2174 audit (UN-01, promote the UN-D1 probe to `RBM3D/Universality/Pins.lean`) — Mon Oct  5 04:46:04 UTC 2026
Branch `t/T2174` at `e989d82` (merge-base = main = `87cf70c`); audit worktree `RBM3D-wt/T2174-audit1` (detached).
Scratch: `<scratchpad>/T2174/` (`probe.lean` = `git show 73b451c:RBM3D/Probe/T2162Pins.lean`, `ax.lean`, `pre.lean`).

## 1. Statements vs the pin (target 1): script diff against the probe at `73b451c`
```
$ wc -l probe.lean RBM3D/Universality/Pins.lean
    2041 probe.lean
    1900 RBM3D/Universality/Pins.lean
$ diff probe.lean RBM3D/Universality/Pins.lean | grep "^[<>]" | grep -v "^< #print axioms"
< # T2162 probe (UN-D1): the pins of bulk universality `Thm: B_Univ` at `d ≥ 3`
> # `RBM3D.Universality.Pins` (UN-01): the pins of bulk universality `Thm: B_Univ` at `d ≥ 3`
< Design probe of ticket T2162 (branch `t/T2162` only, never merged, no root import).  Paper:
> Promotion of the UN-D1 design probe of ticket T2162 (`RBM3D/Probe/T2162Pins.lean` at `73b451c`) to
> the library (ticket T2174; statements unchanged).  Paper:
< convolution step is `τ_s ≤ 𝔠𝔡` (sharp up to `τ_s < 16𝔠𝔡/(3+𝔠)`), RBM2D `τ_s ≤ 𝔠`. -/
> convolution step is `τ_s ≤ 𝔠𝔡` (for `W = N^𝔠` the inequality holds exactly for `τ_s ≤ 32𝔠𝔡/(15+2𝔠)`, so `τ_s ≤ 𝔠𝔡` is not the sharp range; paper-delta candidate T2174a, docstring only), RBM2D `τ_s ≤ 𝔠`. -/
< 
< /-! ## 8. Axioms of every public declaration of this file (only `propext`, `Classical.choice`, `Quot.sound`) -/
< 
```
Result: lines 1-1899 of the probe are byte-identical except the module docstring (2 lines) and one docstring
sentence of `un_step1_floor` (`Pins.lean:996`); section 8 (`#print axioms`) is dropped (run below). Every pin,
row, composition theorem, exponent lemma, bad-event lemma and instance is the probe's text, names unchanged,
imports identical (`Defs/Sizes`, `Defs/StochDomAt`, `Defs/SemicircleIntegral`, `Gauss/BlockAnderson`,
`Induction/Defs`, `Propagator/Gap`, two Mathlib BumpFunction files; no `import RBM3D`).
The probe statements were audited against the paper by T2162 (`docs/reports/T2162-audit.md`: 2(a) `UNBUniv` vs
`1_2:452-459` PASS, 2(c) `UNL32` PASS, 2(d) `UNBadY`/`queBadMat` vs `1_2:409-416, 570-577` PASS, 2(b) `UNCore`
PASS with dispatcher sign-off, which this ticket's release presupposes). No statement weakened or strengthened.

Docstring check of the one changed sentence (`un_step1_floor` concludes `W^{τs/8} W^{-2𝔡} ≤ N^{-15τs/16}`):
at `W = N^𝔠`, `𝔠(τs/8 − 2𝔡) ≤ −15τs/16 ⇔ τs(2𝔠+15)/16 ≤ 2𝔠𝔡 ⇔ τs ≤ 32𝔠𝔡/(15+2𝔠)`. The new sentence is
correct; the old one was wrong. Comment only.

§29 checklist (ticket): (5) `∩_z` inside the probability, (6) `Admissible`, `Tendsto size`, `0 < τ` as premises,
(7) `N`-scale of `UNL32` / `W`-scale of `(Meq:QUE)` — all carried verbatim (e.g. `UNL32` at `Pins.lean:281`:
`∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop → …`, `(sz.size n)^δ`; `UNBUniv` at `:177`:
`sz.Admissible 𝔠 𝔡 → ∀ k, 1 ≤ k → ∀ κ, 0 < κ → ∀ E, |E| ≤ 2 - κ → ∀ O, IsTestFun O → Tendsto … (𝓝 0)`).
**Target 1: PASS.**

## 2. Vacuity, hidden hypotheses, cycles
```
$ grep -nE "^structure|^  [a-z]+ :" Pins.lean   (fields of the only structure)
104:structure UNModel {d : ℕ} (sz : Sizes d) where
107:  prob : IsProbabilityMeasure μ
109:  H : ∀ n : ℕ, Sizes.SeqΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
110:  herm : ∀ n ω, (H n ω).IsHermitian
111:  meas : ∀ n (i j : Idx d (sz.L n) (sz.W n)), Measurable fun ω => H n ω i j
116:def UNModel.band ...   125:def UNModel.ba ...   (both constructed, every field discharged)
```
`UNModel` carries only data and well-formedness (probability, Hermitian, measurable), inhabited by `band` and `ba`;
no result hidden in a field. All pins are `def … : Prop` registered below; composition theorems take them as
explicit hypotheses. Imports are merged modules on `main`; no cycle (the file imports no `RBM3D.Universality.*`).
External input `UNL32` (LSY Thm 2.2, DECISIONS §5): its arithmetic premises have the proved limit check
`un_L32_arith` with instances at `(N,τ) = (2097152,1/2)` and the sharp threshold `(65536,1/8)` (used in section 7,
4 hits); regularity premises routed through the owed `UNStep1Good`. **PASS.**

## 3. Compiled nonempty instances (target 3)
Section 7 is unchanged (diff above). Use of each proved section 1-6 theorem in section 7 (`grep -cw`):
```
2 un_core_of_rows   1 un_claimAll_of_rows   1 un_bUniv_of_rows   2 unBadY_measure_le   2 unBadY_subset
5 un_dens_msc_zero  4 un_L32_arith  3 un_window_sub  1 un_window_N_scale  1 un_W_neg_le  1 un_step1_floor
1 un_que_params 1 un_que_exponent 1 un_cprime 1 un_claim_exponent 1 un_const_absorb 1 un_Bctl_le
1 un_d_lt_half 1 un_dc_lt_one 1 un_rhoSC_lower 1 un_rhoSC_lip 1 un_rhoSC_edge 1 unBadY_card_le
0: helper lemmas only (dbmMat_isHermitian, ouMat_isHermitian, ouMat_zero, un_msc_*, rhoSC_pos,
   isTestFun_comp_smul, unBUniv_diff_eq, unMy_eq) — used inside the proofs above, not endpoints.
```
Key instance (`Pins.lean:1757-1768`):
```lean
theorem inst_bUniv_band (rI …) (rN : UNNormBandRow) (h32 : UNL32) (hML : ∀ d, UNMLOut d) (hLoc : UNLocAvgBand)
    (hQ : UNQueBand) (hGL : UNGUELocal) (hGC : UNGreenCorrAll) : Tendsto (… kPoint 1 bump 0 … sz0 …) atTop (𝓝 0) :=
  un_bUniv_of_rows rI rU rC rE rJ rO rD rT rN h32 hML hLoc hQ hGL hGC 3 le_rfl (1 / 6) (1 / 10) sz0
    sz0_adm 1 le_rfl (1 / 10) (by norm_num) 0 (by norm_num) bump bump_testFun
theorem inst_badY_measure : (Measure.dirac ()) {_ω : Unit | UNBadY 3 4 32 (1/64) (1/10) 0 0 0} ≤ ((2*3+1 : ℕ) : ℝ≥0∞) * 1 :=
  unBadY_measure_le (d := 3) (L := 4) (W := 32) (Measure.dirac ()) (by norm_num) (by norm_num)
    (by norm_num) (by rw [Nat.cast_ofNat, pow32]; norm_num) _ (fun _ => 0) 1 (fun b => prob_le_one)
```
Data `sz0` (d = 3, L = 4, W = 32, lam = 1/64, N = 2097152), `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `k = 1`, `E = 0`,
`bump` with `bump 0 = 1` (`bump_nondegenerate`); `Admissible` by merged `sz0_admissible`; `UNDens` discharged by
`un_dens_msc_zero` in `inst_core_band`/`inst_core_of_rows`; `badY_zero` shows the bad event nonempty. Remaining
hypotheses are UN/MA pins and rows (other gates), as CLAUDE.md §4 step 2 allows. Not degenerate. **PASS.**

## 4. Build, axioms, hygiene, diff scope (target 2 included)
```
$ lake build RBM3D.Universality.Pins
✔ [3328/3328] Built RBM3D.Universality.Pins (8.0s)
Build completed successfully (3328 jobs).            exit 0, 0 error lines
$ lake build                                          (whole library, worktree)
Build completed successfully (3946 jobs).            exit 0
$ lake env lean ax.lean   # import RBM3D.Universality.Pins + the probe's 139 section-8 `#print axioms` lines
exit 0; lines = '… depends on axioms: [propext, Classical.choice, Quot.sound]': 139; other lines: 0
'RBM.Univ.UNBUniv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_bUniv_of_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unBadY_measure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_dens_msc_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.UNInst.inst_bUniv_band' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean pre.lean   # import RBM3D; import RBM3D.Universality.Pins; #assert_rbm_axioms
precheck exit 0
1:axiom audit: 5297 theorems, 1872 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
7:  RBM.Univ.UNL32: 5 [no certificate]
122:premises found by scanning: 101 (borrowed 1, owed 79, structural 21).
123:registry: 2 borrowed + 113 owed + 56 structural; 70 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -nE "sorry|admit|native_decide|^\s*axiom|#print" Pins.lean
(no output)
$ git diff --name-only main...t/T2174
RBM3D/Test/Axioms.lean
RBM3D/Universality/Pins.lean
$ git diff main...t/T2174 -- RBM3D/Test/Axioms.lean | grep -E "^[-+]" | grep -v "^[-+][-+]" | grep -v '^+   `RBM\.Univ\.'
-  [`RBM.Loop.KLPT]
+  [`RBM.Loop.KLPT,
$ grep -rln -e "namespace RBM.Univ" -e "RBM\.Univ\." RBM3D | grep -v Universality/Pins.lean
RBM3D/Test/Axioms.lean        (registry lines only: no name clash)
```
Registry (only list lines changed; no frozen signature touched): `borrowedProps` + `UNL32`; `owedProps` + 26
`RBM.Univ.*` (the 15 pins of target 2, nine rows `UNInfty1Row UNUnivMainRow UNOURow UNEMCTE2Row UNJakUywRow
UNClaimRow UNDensBandRow UNTrLocalBandRow UNNormBandRow`, `UNGreenCorrAll`, `UNNormBound`); `structuralProps` +
`UNDens IsRegular32 IsFreeConv32 InWindow queBadMat UNBadY`. Consistent with T2162 report (d) 4 ("owed all other
`UN*` pins and rows") and portmap P.4 (`UNNormBound / UNNormBandRow`: owed, line 262). **PASS.**

## 5. Paper deltas
No Lean statement differs from the probe, so D382–D388 (T2162a–g, `docs/paper-deltas.md:1341-1347`) still cover
every Lean/paper difference of these pins. T2174a (prove report (d) 1) is a docstring correction, not a statement
difference. **PASS.**

## 6. Observations (no effect on statement, instance, build, axioms or delta coverage)
- O1. T2174a is a comment fix, not a Lean/paper statement difference; the dispatcher may file it as a doc fix rather
  than a numbered paper-delta.
- O2. Ticket target 2 says "the six rows"; nine `*Row` names exist in the probe and all nine are registered owed
  (the extra three band rows plus `UNGreenCorrAll`, `UNNormBound` were reported unclassified by the pre-check
  without them). Classification matches T2162 (d) 4 / portmap P.4.
- O3. `inst_bUniv_band` keeps the deterministic row `UNDensBandRow` as a hypothesis (already noted by the T2162
  audit; `un_dens_msc_zero` is at `δ = 1/2 > κ/2`); unchanged here, as the ticket requires.

## 7. Verdict per target
| target | verdict |
|---|---|
| 1 sections 1-6 promoted verbatim | PASS |
| 2 registry lines + pre-check | PASS |
| 3 section 7 instances | PASS |

**Overall: PASS.** No dispatcher sign-off needed.
