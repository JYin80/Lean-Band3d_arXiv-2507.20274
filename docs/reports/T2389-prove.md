Prover model: claude-sonnet-5-5

## (a) Math preflight — Sat Oct 10 13:13:58 UTC 2026

Scripts (not Lean) live in the scratchpad subdirectory `T2389/` (`seg.py`, `tok.py`, `cons.py`, `cone.py`, `inst.py`, `thr.py`).

### (i) Exponent table, D = 0 replacements, segments, G1 names, plan against the stop line

Generic statement over D (all three files): `D n : Matrix (Idx d (sz.L n) (sz.W n)) .. ℂ` deterministic, `(D n).IsHermitian`; `z : ℕ → ℂ`, `(z n).im ≠ 0`; `0 ≤ t n ≤ 1`; resolvent `green (D n + seqHflow sz n (t n) ω) (z n)` read through `blockMat`; the row/column/quad left sides keep `H = seqHflow` (the row of X). BA instance: `D n = g₀ Ψ`, `z n = ztOf m₀ E t` (`BAGt_eq_green`, probe 44).

| quantity | value (sz0, n=0, d=3) | constraint | slack |
|---|---|---|---|
| L, W, N=(WL)^3, g=lam | 4, 32, 2097152, 1/64 | `g²L³ ≤ 1/64` (`FlowPins.lean:1150`) | equality at n=0 |
| t | 1/2 | `0 ≤ t ≤ T₀ < 1`; generic needs only `t ≤ 1` (`LDE_perTime_sq_of_rowSum` h1, LDE:732; `LDEQuadInst_meas_le` hu1, IBPPoly:962) | T₀=0.69374: 0.194; to 1: 0.5 |
| Im z_t = (1-t) Im m₀ | 0.499746 | `≠ 0` (generic hz, replaces `zt_im_ne_zero hκ hE ht1`) | η⁻¹=2.001 |
| ‖m₀‖ | 0.999493 | `≤ 1`, used only by `FlucBoundD` (B=2(η⁻¹+1)=6.002, ε=4η⁻¹=8.004) | 5.1e-4 |
| ‖D‖ = ‖g₀Ψ‖_op | 0.0781 (g₀=0.013014) | none (Hermitian only; no smallness, supervisor C1) | n/a |
| κ=1/2 ≤ Im m₀ | 0.999493 (Im m_S = 0.832488 ≥ 4/5) | `BAdom`, `BAReal` | 0.4995 |
| ε=1/10 | N^{-1+ε}=2.04e-6 ≤ Im z=0.3675 ≤ 1 | `BAdom` | 1.8e5 |
| 𝔠=1/6 | N^𝔠=11.31 ≤ W=32 | Bandwidth | 2.83 |
| (eq:WO), 𝔡=1/10 | W^{-1.4}=0.00781 ≤ g=0.015625 ≤ 10 | `WO` | ×2.0, ×640 |
| Ccard | N(N-1)=4.398e12 ≤ N²=4.398e12 | `eventually_card_LdeIdx_le` (RowIndep:1178), Ccard=2 | N pairs |
| `hwConst q ≤ N^{τ(q+1)-D}`, q=⌈(D+1)/τ⌉ | (τ,D)=(1,1): 125000 ≤ 4.4e12 (n=0); (1/2,1): 1.1e11 > 3.0e9 at n=0, true from n=1 | eventual in N (`eventually_le_rpow`, IBPPoly:1036); this is the conclusion's ∀ᶠ, not a hypothesis | (1,1): 3.5e7 |

No external hypothesis occurs in any target (all hypotheses are deterministic), so no limit computation is owed.

**D = 0 steps beyond Hermitian / Im z ≠ 0 / independence, with the replacement:**
1. `flucAvg_zt_im_pos` (LDE:193) `|E|<2, t<1 ⟹ Im z_t>0`: hypothesis `0 < z.im` (BA: `ba_G_data` 4th clause).
2. `norm_mE` (`‖m‖=1`; LDE:239-253, `flucBound_env` LDE:308): hypothesis `‖m‖ ≤ 1` (BA: `BAMfine_norm_le_one` GreenSchur:105 with `M_xx = m₀`). Only the `FlucBoundD` family uses it; the four BALDEin conjuncts do not.
3. `zt_im_ne_zero hκ hE ht1` (EntryDom:79) in `stochDom_ldeRow/Col` (LDE:859, 901) and `stochDom_ldeQuad` (IBPPoly:1038): hypothesis `∀ n, (z n).im ≠ 0`.
4. `ht1 : t n < 1` used as `t n ≤ 1`: hypothesis `t n ≤ 1`.
5. u = 0 case (`LDEQuadInst_seqHflow_zero` IBPPoly:422, `chaos_modelChaos_zero` :842): at u=0 only the row `h` of X vanishes (`modelChaos_h`), `D+X(0)=D ≠ 0`; the chaos `Σ h B h̄ - Σ σ B` is still 0. No change.
6. Envelope `‖green H z‖ ≤ |Im z|⁻¹` (`norm_Gsig_le_inv_eta`, FlowCalculus:644) and continuity (`continuous_green_of_isHermitian`, :191) take any Hermitian `H`: `H = D + X` (`Matrix.IsHermitian.add`). No spectral bound on `‖D+X‖` is used anywhere.
7. Off-row dependence: `Hflow_submatrix_congr_offRowCoord` (RowIndep:609) is applied as a black box to the `X` part; `(D+X).submatrix = D.submatrix + X.submatrix` (`Matrix.submatrix_add`), D constant. Measurability: entries of `D+X-z` are `measurable_const + measurable_seqHflow_entry`.
8. Profile: `svar d L W (sz.lam n)` at `sz.withLam 0` is `svar d L W 0` (`(sz.withLam 0).lam n` is `0` by the structure update, `Defs/Sizes.lean:182`); `svarF_eq_svar` is `rfl` (FineModel:68).

**Segments (script `seg.py`, `tok.py`; lines of the segment / declarations / lines containing a D-bearing token):** LDE 102-398: 297/24/86; LDE 464-602: 139/8/26; LDE 718-931: 214/3/13; RowIndep 879-964: 86/6/26; RowIndep 1252-1454: 203/6/11; IBPPoly 397-1078: 682/45/196. Totals 1621 / 92 / 358.
- LDE 464-602: `im_green_diag`, `green_diag_ne_zero` are already generic in a Hermitian `H`; restate `isUnit_det_Hflow_sub`, `green_Hflow_diag_ne_zero`, `minorRowConj_eq_greenMinor`, `ldeColLHS_eq`, `rowVarSum_minorRowConj_eq`.
- LDE 718-931: restate `stochDom_ldeRow`, `stochDom_ldeCol` in the BALDEin shape (`blockMat (green (D+H) z)`, `PerTimeDomAt`); the private bridge `LDE_perTime_sq_of_rowSum` and `LDE_*_submatrix` stay (R).
- RowIndep: `minorCol`/`minorRowConj` get D-twins; `minorCol_congr`, `measurable_minorCol`, `minorCol_eq_greenMinor`, `ldeRowLHS_eq`, `rowVarSum_eq`, `minorRowConj_congr`, `measurable_minorRowConj` restated; `rowSum_ae_eq_zero_of_varSum_eq_zero`, `rowSum_rowCoeffNorm`, `highProb_norm_rowSum_sq_le` read only `rowSum`/`rowVarSum`/`C` (no change).
- IBPPoly: `minorRes, modelChaos(Eps), vqM, sqVq` and every lemma on them get the argument `D` (196 token lines); `gaussIBP`, `hwConst(_pos)` unchanged; `stochDom_ldeQuad` restated, band version a corollary.

**Findings.**
- **F-A (conflict with the sole-writable-files list).** LDE 102-398 reads `greenMinorMat`, `greenDiagCentered`, `greenMinorDiagCentered`, `flucDiag`, `flucDiagMinor`, `flucAvg` (defs at `FlucVanish.lean:322, 813-829, 1028`, group B, twin route, not writable here) and `norm_flucDiag_sub_flucDiagMinor_le` (FlucVanish:841). A D-restatement of 7 of the 9 G1 names of this segment (`measurable_greenDiagCentered`, `measurable_greenMinorDiagCentered`, `norm_greenMinorMat_apply_le_etaT`, `norm_greenDiagCentered_le_env`, `flucBound_env`, `integrable_norm_flucAvg_pow`, `condExpDiag`; the other two, `measurable_green_apply`, `norm_green_apply_le_etaT`, need only `green`) needs D-twin defs `LDE_greenMinorMatD, …, LDE_flucAvgD, LDE_FlucBoundD`, bridging lemmas `D=0 ⟹ band def` (`zero_add`) and a copy of the 50-line FlucVanish:841 lemma, all inside `LDE.lean` (counted below, ~130 lines). `BALDEin` does not use them. The later row that twins group B must reuse these names.
- **F-B (ticket wording).** hLrow/hLcol use the time-sequence `stochDom_rowSum_generalTime` (RowIndep:1193) through the private `LDE_perTime_sq_of_rowSum` (LDE:732), as the band `stochDom_ldeRow` does, not `stochDom_rowSum_general` (RowIndep:1237, fixed u). The bridge is private to `LDE.lean`, so the generic D-theorems `LDE_stochDom_ldeRow_shift/_Col_shift` (stem-prefixed, public) must be proved in `LDE.lean`; `BA/GreenLDE.lean` only instantiates them.
- **F-C (iii, block support).** No hypothesis of `stochDom_rowSum_generalTime` or of the generic LDE/quad statements is a support condition; the profile enters as `svarF … ((sz.withLam 0).lam n)`; I find no step of the four conjuncts that uses a.s. block support. Recorded route if needed (G3a): `Measure.infinitePi_map_eval` (Mathlib `Probability/ProductMeasure.lean:478`: `(infinitePi μ).map (fun x ↦ x i) = μ i`), `gaussianReal_zero_var` (`Probability/Distributions/Gaussian/Real.lean:229`: `gaussianReal μ 0 = Measure.dirac μ`), `ae_dirac_eq` (`MeasureTheory/Measure/Dirac/Basic.lean:159`), `ae_map_iff` (`MeasureTheory/Measure/Map.lean:249`) with `measurable_pi_apply c`; the variance `gvarF … (sz.withLam 0).lam` vanishes off the block because `sbKernelR d L 0 x = if x = 0 then 1 else 0` (`Defs/Block.lean:74-76`); `SeqCoord` is countable (`Σ ℕ, Fintype`) so `ae_all_iff` gives one null set.

**G1 names (script `cons.py`; line numbers at `bf5f0d5`; 28 = LDE 15 + RowIndep 10 + IBPPoly 3).** Statement unchanged, no edit (6): `im_green_diag` LDE:476, `green_diag_ne_zero` :503 (both for any Hermitian `H`), `hwConst` IBPPoly:721, `hwConst_pos` :723, `rowSum_ae_eq_zero_of_varSum_eq_zero` RowIndep:1292, `rowSum_rowCoeffNorm` :1347. Restated over D, band name kept as the D=0 corollary (22): LDE `measurable_green_apply` :122, `measurable_greenDiagCentered` :162, `measurable_greenMinorDiagCentered` :167, `norm_green_apply_le_etaT` :213, `norm_greenMinorMat_apply_le_etaT` :230, `norm_greenDiagCentered_le_env` :239, `flucBound_env` :308, `integrable_norm_flucAvg_pow` :373, `condExpDiag` :395 (def), `isUnit_det_Hflow_sub` :535, `green_Hflow_diag_ne_zero` :541, `stochDom_ldeRow` :850, `stochDom_ldeCol` :892; RowIndep `minorCol` :883 (def), `minorCol_congr` :894, `measurable_minorCol` :902, `ldeRowLHS_eq` :935, `rowVarSum_eq` :951, `minorRowConj` :1257 (def), `minorRowConj_congr` :1267, `measurable_minorRowConj` :1275; IBPPoly `stochDom_ldeQuad` :1022. Names with a mention outside the three files (regex scan, `cons.py`): the 18 of LDE (15) and IBPPoly (3), in `Graph/LWMoment*`, `Universality/GUEPhase/*` and `Green/{IBPRem,IBP,FlucIter,FlucIterGain,CondDom,GbEXP}`; the six outside `Green/` are `im_green_diag`, `green_diag_ne_zero`, `measurable_green_apply`, `norm_green_apply_le_etaT`, `hwConst`, `hwConst_pos`; the 10 RowIndep names are used inside LDE/IBPPoly only. The plan keeps each defined band def/statement text unchanged (twin generic decl + `D=0` bridge by `zero_add`), so every old statement is reproduced; this is checked by compiling the 28 `example : <old> := <name>` in 1b/2.

**Cone and plan (script `cone.py` at HEAD 85e7cd6; counts are estimates, not measurements).** Reverse import closure of the three files: 156 modules, 191450 lines, 6 `Graph/LWExpCert*` modules (`LWExpCert, B, BS0, BS1, S0, S1`): as in the ticket. Names `BALDEin`, `BAX`, `BAGt_eq_green` absent outside `Probe/`.

| piece | new lines I | deleted X |
|---|---|---|
| LDE 102-398 (D-twin defs 48, bridges 33, FlucVanish:841 copy 50, edits 86+20, 8 corollaries 72) | 309 | 86 |
| LDE 464-602 | 48 | 26 |
| LDE 718-931 (2 generic ×42 + 2 corollaries ×18) | 120 | 34 |
| RowIndep 879-964 / 1252-1454 (twin defs + 7 theorems) | 77 / 36 | 0 |
| IBPPoly 397-1078 (token edits 196+40, generic quad 14, corollary 34) | 284 | 196 |
| `BA/GreenLDE.lean` (pins 68, 3 conjuncts 75, `ba_G_data` 35, instance+3 band corollaries 76, headers 50, hLdiag 8, bridges 18) | 330 | – |
| total | 1204 | 342 |

Net (I−X) 862; insertions only 1204; insertions+deletions 1546. With a factor 1.3 on the estimate: 1120 / 1565 / 2010. Stop line 1800 is not exceeded at the central value under any reading (ticket central 1214); under the insertions+deletions reading the high case exceeds it. Rule for 1b: read `git diff --numstat` on the three files after targets 1-2; if insertions+deletions exceed 1470 (= 1800 − 330) before `BA/GreenLDE.lean` starts, stop and split (G2a = targets 1-2, G2b = targets 3-5).

### (ii) One nondegenerate instance (d = 3, sz0, n = 0, flow_sz0, t ≡ 1/2)

Hypotheses of the three generic theorems and of `baLDEin_holds 3`: `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`FlowPins.lean:1235`), `0 ≤ t ≤ T₀` (`half_lt_t0`, :1275), `D = g₀Ψ` Hermitian, `Im z_t ≠ 0`, `t ≤ 1`, `size → ∞`, `card OffPair ≤ N^2`. Fine-lattice dimension N = 2097152 cannot be inverted, so the script computes the block data on Z_4^3 (`PsiB` = ℓ¹-distance-1 adjacency, `Defs/Lattice.lean:71,108`; `mS`, `zS`, `wI = 6i/5`, `MFixedPoint.lean:849-868`; `BAt0`, `BAflowE`, :279-280; `BAflowLam0 = √T₀ g`, `FlowPins.lean:412`; `m₀ = m_S/√T₀`, `BAmF_sz0_eq`, :1285), and checks the D-shift calculus on a random 8×8 Hermitian `D` (‖D‖ = 1.248, not small): the minor formula for `D+X`, independence of the minor of row/column i of X, and `E|Σ_k X_ik G^{(i)}_{kj}|² = u Σ_k S_ik |G^{(i)}_{kj}|²` by Monte Carlo (2e5 samples).

Command: `cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/966b45d4-be15-4db2-88b3-45a074bfecd5/scratchpad/T2389 && python3 inst.py` (and `python3 thr.py`):
```
N=2097152 L=4 W=32 lam=0.015625 (1/64=0.015625)  g^2L^3=0.015625
mS=0.000000+0.832488j Im mS=0.832488(>=4/5) zS=0.000000+0.367512j Im zS=0.367512  (11/30=0.3667<=Im zS<=0.7)
BAdom: kappa<=Im m: True  N^(-1+eps)=2.044e-06 <= Im z: True  Im z<=1: True
Bandwidth W>=N^c: 11.314<=32  WO: W^(-d/2+dd)=0.00781<=lam=0.01562<=1/dd=10
BASelf residual at (zS,mS): 0.0
T0=0.693740 (>=2/3) E=0.000000 g0=0.013014 m0=0.000000+0.999493j |m0|=0.999493(<=1) Im m0=0.999493(>=kappa)
BAReal self_m residual at real E, g0, m0: 2.220446049250313e-16
t=0.5<=T0:True  z_t=0.000000+0.499746j Im z_t=0.499746 = (1-t)Im m0=0.499746 >0
D=g0*Psi Hermitian (real symmetric): True  ||D||_op=0.0781
OffPair card N(N-1)=4398044413952 <= N^2=4398046511104: True
minor formula (D+X) max err: 2.48e-16
minor of D+X independent of row/col i of X: 0.00e+00
E|sum_k X_ik G^(i)_kj|^2 MC=0.10037 vs u*sum S_ik|G^(i)_kj|^2=0.10077 (D != 0, ||D||=1.248)
tau=1 D=1: q=2 hwConst(q)=125000 exponent tau(q+1)-D=2 N(0)^e=4.398e+12 first n with hwConst<=N^e: 0 (N=2097152)
tau=0.5 D=1: q=4 hwConst(q)=111577100832 exponent tau(q+1)-D=1.5 N(0)^e=3.037e+09 first n with hwConst<=N^e: 1 (N=549755813888)
```
Cone command and output: `python3 -I …/T2389/cone.py` gives `modules in cone: 156 lines: 191450` and `LWExpCert modules: 6`.

### Verdicts
- Target 1 (in-place G segments over D): PASS, with finding F-A (the group-B definitions are not writable, so the D-twin defs go inside `LDE.lean`) and F-B (generic row/column theorems must live in `LDE.lean`).
- Target 2 (G1 checks, 28 names): PASS (22 restated with D=0 corollaries, 6 unchanged).
- Target 3 (`BA/GreenLDE.lean`: `BAGt_eq_green`, `BAX`, `BALDEin`, `baLDEin_holds`): PASS; hLdiag is the merged `stochDom_normSq_Hflow_diag`; hLrow, hLcol, hLquad are instances of the generic D-theorems (F-B); block support is not needed by my trace (F-C).
- Target 4 (`ba_G_data`): PASS (from `BAFlow` and `0 ≤ t ≤ T₀` only; no `g ≤ W^{-ε}`, no smallness of `‖M - m₀I‖`).
- Target 5 (nonempty instance): PASS (data above; compiled in 1b).
- Overall: PASS. Plan central 862 / 1204 / 1546 (net / insertions / insertions+deletions) against stop line 1800.

## (b) Script output — written Sat Oct 10 16:37:03 UTC 2026

### b1. Lines against the stop line (1,800, binding), and the cone
`git diff main --numstat -- Green/LDE Green/RowIndep Green/IBPPoly` (insertions, deletions) and `wc -l RBM3D/BA/GreenLDE.lean`, at each section commit (net3 = insertions - deletions of the three files):
```
d4bb8fd net3=266 wcGreenLDE=0   total=266      c554c46 net3=646 wcGreenLDE=179 total=825      d50b567 net3=688 wcGreenLDE=245 total=933
cf80279 net3=688 wcGreenLDE=245 total=933      b5dc671 (HEAD) net3=733 wcGreenLDE=245 total=978   (stop line 1800: not reached)
256 213 Green/IBPPoly.lean ; 492 73 Green/LDE.lean ; 271 0 Green/RowIndep.lean ; 245 BA/GreenLDE.lean ; RBM3D.lean +1 import line
git diff --name-only main...HEAD:  RBM3D.lean RBM3D/BA/GreenLDE.lean RBM3D/Green/IBPPoly.lean RBM3D/Green/LDE.lean RBM3D/Green/RowIndep.lean
python3 -I cone.py (reverse import closure of the three files, main e67bfbd): modules in cone: 156 lines: 191450 ; LWExpCert modules: 6
```
### b2. Builds, registry, hygiene
```
$ lake build RBM3D.BA.GreenLDE | tail -1         Build completed successfully (3758 jobs).
$ lake build   (15:36:19 -> 16:34:55 UTC, from fullbuild2.start/.end; exit 0)      Build completed successfully (4200 jobs).
RBM3D.lean:432:0: axiom audit: 11072 theorems, 3240 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).   [#assert_rbm_axioms, in the same build]
$ grep -cE '\bsorry\b|\badmit\b|native_decide|^axiom ' <4 files>    BA/GreenLDE 0, Green/LDE 0, Green/RowIndep 0, Green/IBPPoly 0
$ lake env lean docs/tickets/checks/T2389-check.lean      exit 0, 0 error lines (116 output lines; 0 lines with warning, error or sorry)
```
### b3. Axioms (`lake env lean ax3.lean`)
```
'RBM.BA.baLDEin_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.BAGt_eq_green' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.ba_G_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.GreenLDE_BAX_ae_block_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDE_stochDom_ldeRow_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.LDE_stochDom_ldeCol_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.IBPPoly_stochDom_ldeQuad_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeRow' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeCol' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Green.stochDom_ldeQuad' depends on axioms: [propext, Classical.choice, Quot.sound]
```
### b4. Target statements, extracted from the files by script (`stmts.py`, whitespace collapsed, wrapped at 215 columns)
```
-- RBM3D/BA/GreenLDE.lean:46
theorem BAGt_eq_green {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : BAGt sz lam0 E n t ω = RBM.green ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + Matrix.of fun i j : Idx d (sz.L n) (sz.W n)
  => seqHflow (sz.withLam 0) n t ω i j) (ztOf (BAmF sz lam0 E n) (E n) t)
-- RBM3D/BA/GreenLDE.lean:84
def BALDEin (d : ℕ) : Prop := ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → Path.PerTimeDomAt
  (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n)) (fun n u ω => Green.ldeRowLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (BAGt sz
  (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) (fun n u ω => Green.ldeRowRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1
  u.1.2) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Green.OffPair d (sz.L n) (sz.W n)) (fun n u ω => Green.ldeColLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d (sz.L n)
  (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) u.1.1 u.1.2) (fun n u ω => Green.ldeColRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t
  n) ω)) u.1.1 u.1.2) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n)) (fun n i ω => Green.ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω)) (blockMat d
  (sz.L n) (sz.W n) (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) (svar d (sz.L n) (sz.W n) 0) (t n) i) (fun n i ω => Green.ldeQuadRHS (svar d (sz.L n) (sz.W n) 0) (blockMat d (sz.L n) (sz.W n) (BAGt sz
  (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω)) i) ∧ Path.PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => Vtx d (sz.L n) (sz.W n)) (fun n i ω => ‖blockMat d (sz.L n) (sz.W n) (BAX sz n (t n) ω) i i‖
  ^ 2) (fun n i _ => svar d (sz.L n) (sz.W n) 0 i i)
-- RBM3D/BA/GreenLDE.lean:199
theorem baLDEin_holds (d : ℕ) : BALDEin d
-- RBM3D/BA/GreenLDE.lean:55
theorem ba_G_data {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) : t < 1 ∧ BAReal d (sz.L n) (BAflowLam0 sz z n) κ
  (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) ∧ 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ∧ 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) t).im ∧ (∀ ω, BAGt
  sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω - BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n = -(BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n * BAflowPert sz (BAflowLam0 sz z) (BAflowEs sz z) n t ω * BAGt sz
  (BAflowLam0 sz z) (BAflowEs sz z) n t ω)) ∧ ∀ x y, ‖BAMfine sz (BAflowLam0 sz z) (BAflowEs sz z) n x y‖ ≤ 1
-- RBM3D/BA/GreenLDE.lean:168
theorem GreenLDE_BAX_ae_block_support {d : ℕ} (sz : Sizes d) (n : ℕ) (t : ℝ) : ∀ᵐ (ω : (sz.withLam 0).SeqΩ) ∂(Sizes.seqP (sz.withLam 0)), ∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).1 ≠ (split d
  (sz.L n) (sz.W n) y).1 → BAX sz n t ω x y = 0
-- RBM3D/Green/LDE.lean:1149
theorem LDE_stochDom_ldeRow_shift (hsz : sz.SizeTendsto) (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0) {t : ℕ → ℝ} (ht0 :
  ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n)) (fun n u ω => ldeRowLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (green (D n +
  sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2) (fun n u ω => ldeRowRHS (svar d (sz.L n) (sz.W n) (sz.lam n)) (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2)
-- RBM3D/Green/LDE.lean:1193
theorem LDE_stochDom_ldeCol_shift (hsz : sz.SizeTendsto) (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0) {t : ℕ → ℝ} (ht0 :
  ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) : sz.PrecPT (U := fun n => OffPair d (sz.L n) (sz.W n)) (fun n u ω => ldeColLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω)) (blockMat d (sz.L n) (sz.W n) (green (D n +
  sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2) (fun n u ω => ldeColRHS (svar d (sz.L n) (sz.W n) (sz.lam n)) (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow n (t n) ω) (z n))) u.1.1 u.1.2)
-- RBM3D/Green/IBPPoly.lean:1037
theorem IBPPoly_stochDom_ldeQuad_shift (sz : Sizes d) (hsz : sz.SizeTendsto) (D : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hD : ∀ n, (D n).IsHermitian) {z : ℕ → ℂ} (hz : ∀ n, (z n).im ≠ 0)
  {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht1 : ∀ n, t n ≤ 1) : sz.PrecPT (U := fun n => Vtx d (sz.L n) (sz.W n)) (fun n i ω => ldeQuadLHS (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω)) (blockMat d (sz.L n) (sz.W
  n) (green (D n + sz.seqHflow n (t n) ω) (z n))) (svar d (sz.L n) (sz.W n) (sz.lam n)) (t n) i) (fun n i ω => ldeQuadRHS (svar d (sz.L n) (sz.W n) (sz.lam n)) (blockMat d (sz.L n) (sz.W n) (green (D n + sz.seqHflow
  n (t n) ω) (z n))) i)
```
`BAX`, `BALDEin`, `BALDEin_diag` against `t/T2378:RBM3D/Probe/T2378Pins.lean` (whitespace-normalised text): BAX identical: True; BALDEin identical: True; BALDEin_diag statement identical: True.
### b5. Compiled nonempty instances (d = 3, `sz0`, `flow_sz0`, t = 1/2 <= T0; every deterministic hypothesis discharged)
```
BA/GreenLDE.lean:227   example := baLDEin_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
  SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le)
BA/GreenLDE.lean:232   example : Path.PerTimeDomAt ... (the hLquad conjunct at the same data) := (baLDEin_holds 3 ... ).2.2.1
Green/LDE.lean:1608,1612  example := LDE_stochDom_ldeRow_shift / LDE_stochDom_ldeCol_shift sz0 sz0_tendsto LDE_shiftD_sz0 LDE_shiftD_sz0_isHermitian (z := fun _ => zt 0 (1/2)) ..
Green/IBPPoly.lean:1179   example := IBPPoly_stochDom_ldeQuad_shift sz0 sz0_tendsto LDE_shiftD_sz0 LDE_shiftD_sz0_isHermitian (z := fun _ => zt 0 (1 / 2)) ...
Green/RowIndep.lean:1764, 1777 (shifted minor columns / rows at sz0, D = (1/2) I, u = 1/2); Green/LDE.lean:1618-1664 (LDE_flucBound_envD, envelopes, bounded weight, integrability, measurability, LDE_shift_zero at D = (1/2) I, sz0, n = 0)
Band corollaries at D = 0: LDE.lean:1670, 1674 (measurable_green_apply, norm_green_apply_le_etaT), RowIndep.lean:1514 (ldeRowLHS_eq), IBPPoly.lean:1167 (stochDom_ldeQuad_sz0, the band instance)
```
### b6. Name clashes and G1
```
$ python3 -I clash.py   public names added (not present at base bf5f0d5): 53 ; public names removed: 0 ; hits of added names in other files of the branch tree: 0
$ lean g1.lean  (#check @n for the 28 names of the ticket, #print for the defs condExpDiag, minorCol, minorRowConj, hwConst), once against main's build, once against the branch build
diff g1.main.txt g1.branch.txt: exit 0 (198 lines each, 28 names)
```
`python3 -I declchanged.py` (statement text base `bf5f0d5` vs HEAD): `LDE: changed public 0, changed private 4, removed 0, G1 names among changed: []`; `RowIndep: 0, 0, 0, []`; `IBPPoly: changed public 29, changed private 3, removed 0, G1 names among changed: []` (`minorRes` ... `chaos_modelChaos_zero`, the shift `D` enters); outside `IBPPoly.lean` those 29 occur only in docstrings (`Universality/GUEPhase/AuxCarrier.lean:358, 498-499`), and the full build is clean. Ports from RBM1D/RBM2D: none in this stage (no `diff --stat` owed).

### Narrative
- Resumed per rule H after an API session-limit stop: commits `d4bb8fd`, `c554c46` existed; the uncommitted edits (block-support lemma, two band examples in `LDE.lean`) were kept; later commits `d50b567`, `cf80279`, `b5dc671`. The full build above is on `b5dc671`.
- IBPPoly (in place): `D` is an argument of `minorRes`, `modelChaos(Eps)`, `vqM`, `sqVq` and their lemmas; `stochDom_ldeQuad` is the one-line corollary of `IBPPoly_stochDom_ldeQuad_shift` at `D = 0`, `z = z_t`. RowIndep: the band declarations stay; a section adds `RowIndep_minorColD`, `RowIndep_minorRowConjD`, their congruence, measurability and alignment lemmas, and the bridges `RowIndep_minorColD_zero`, `RowIndep_minorRowConjD_zero`.
- LDE: `LDE_stochDom_ldeRow_shift/_Col_shift` use the private bridge `LDE_perTime_sq_of_rowSum` with `stochDom_rowSum_generalTime` (finding F-B of (a)); `stochDom_ldeRow`, `stochDom_ldeCol` are corollaries at `D = 0`. F-A of (a): the `FlucVanish` definitions are group B, so the nine G1 names of LDE 102-398 keep their old text and proofs and get twins `LDE_*D` (defs, envelopes, `LDE_FlucBoundD`, `LDE_flucBound_envD`, `LDE_integrable_norm_flucAvg_powD`), with the bridge `LDE_shift_zero`.
- Beyond Hermitian / `Im z != 0` / independence the twins use `‖m‖ <= 1` (only `LDE_norm_greenDiagCentered_le_envD`, `LDE_norm_greenMinorDiagCentered_le_envD`, `LDE_flucBound_envD`) and `t n <= 1`; the four `BALDEin` conjuncts need neither the first nor any smallness (no `g <= W^(-eps)`, no `‖M - m0 I‖`): the data come from `ba_G_data` (`BAFlow`, `0 <= t <= T0`).
- `BALDEin`: hLrow, hLcol, hLquad are the generic theorems at `sz.withLam 0`, `D n = (g0 : C) • PsiI`, `z n = ztOf (BAmF ..) (E n) (t n)`, rewritten by `BAGt_eq_green` and `GreenLDE_perTime_congr`; hLdiag is `BALDEin_diag` = `Green.stochDom_normSq_Hflow_diag (sz.withLam 0)`. The pin text equals the probe (b4).
- Block support (F-C of (a)): `GreenLDE_BAX_ae_block_support` is proved (zero variance gives an a.s. zero coordinate; Mathlib names in (c)); none of the four conjuncts uses it. Rule E: three instance helpers and that lemma were renamed with file-stem prefixes (`cf80279`); `BALDEin_diag` is named by the ticket (target 3).
## (c) Verified Mathlib names (`grep -rn` in `.lake/packages/mathlib/Mathlib`)
`MeasureTheory.Measure.infinitePi_map_eval` (Probability/ProductMeasure.lean:478); `ProbabilityTheory.gaussianReal_zero_var` (Probability/Distributions/Gaussian/Real.lean:229); `MeasureTheory.ae_dirac_iff` (MeasureTheory/Measure/Dirac/Basic.lean:154); `MeasureTheory.ae_map_iff` (MeasureTheory/Measure/Map.lean:249); `measurableSet_eq_fun` (MeasureTheory/MeasurableSpace/Constructions.lean:1091); `MeasureTheory.ae_all_iff` (MeasureTheory/OuterMeasure/AE.lean:152); `measurable_pi_apply` (Constructions.lean:584); `Matrix.submatrix_add` (LinearAlgebra/Matrix/Defs.lean:499); `Matrix.IsHermitian.add` (LinearAlgebra/Matrix/Hermitian.lean:209). Names verified absent: none searched.
## (d) Open issues and paper-delta candidates
- D1 (ticket wording, target 1, "each band theorem becomes the corollary at D = 0"): literally true for `stochDom_ldeRow`, `stochDom_ldeCol`, `stochDom_ldeQuad`; the IBPPoly objects carry `D` in place. The other restated band names (the nine fluctuation-layer names of LDE 102-398; `minorCol`, `minorRowConj` and their lemmas; `ldeRowLHS_eq`, `rowVarSum_eq`) keep their old proofs and statements (G1, b6); their `D`-versions are separate declarations tied to them by `LDE_shift_zero`, `RowIndep_minorColD_zero`, `RowIndep_minorRowConjD_zero` and the examples for `measurable_green_apply`, `norm_green_apply_le_etaT`, `ldeRowLHS_eq`; the other lemmas of that group have no `D = 0` example. Reason: the `FlucVanish` definitions are group B, not writable here (F-A). A group-B ticket that makes them generic can delete the `LDE_*D` duplicates; later rows that twin group B must reuse these names.
- D2: `GreenLDE_BAX_ae_block_support` is unused by `BALDEin`; it is available for BA-G3a (`BA/GreenSchur.lean:18`).
- D3: the instances of the generic `D`-theorems use `D = (1/2) I` (`LDE_shiftD_sz0`); the BA instance (`baLDEin_holds 3 ..`) uses `D = g0 Psi` by construction. Main has moved to `2a05b1d` (four more import lines in `RBM3D.lean`); the four source files are untouched there since `bf5f0d5`.
- Paper-delta candidate T2389a: the Gaussian part `X` of the BA carrier is the band model of `sz.withLam 0` (`Gauss/BlockAnderson.lean:83`), whose off-block entries have variance `0` and vanish almost surely (`GreenLDE_BAX_ae_block_support`); it is not a block-diagonal matrix by construction.
- Paper-delta candidate T2389b: the generic `D`-statements assume `0 <= t n <= 1` and `Im z n != 0` (the band statements assume `t n < 1` and `|E n| <= 2 - kappa`); the band statements are recovered unchanged (b6).
