Prover model: claude-sonnet-5-5
## (a) Math preflight
Cited, not repeated: `docs/reports/T2479-prove.md` (a) (verdict PASS, Mon Oct 12 23:29:09 UTC 2026; `T2479b-prove.md` did not exist when this run started). Its rows that bear on this run: target 6 union row (`N^-(D+1)+c N^-(D+3) <= N^-D`, `c <= 4N^2`, `N >= 5`, slack 0 at `N = 5`), the fluc call `(tau/2, D+3)` (`p = ceil((D_f+2)/tau_f)`, `m3 = 6p+ceil(D_f)+3`, `m1 = 18p+ceil(D_f)+4`), `D0 = 6d/5+(d-2)/c+1`, the instance `d=3, n=0`, and the line estimate for `CltFarG`: central 958, low 817, high 1194 (instance section excluded); split decision: X1b-2 = `CltFarG`, reserve `CltFarG2` unneeded.
### (a′) Preflight corrections
None: no verdict, exponent or instance row of (a) changed.
## (b) Script output — Tue Oct 13 00:50:20 UTC 2026
Scratch scripts in `scratchpad/T2479b/`: `stmts.py`, `examples.py`, `gtab.py`, `reuse.py`, `stmtcheck.lean`, `mkreport.py`. Order as the ticket asks: layout (b1), tables (b2, b3), statements (b4), greps (b5), registry (b6), instances (b7); then builds, name clash, tripwire, narrative.
**b1. Layout, line counts against the stop line 2,000, imports, G1** (branch `t/T2479b`, stacked on `t/T2479` 03f828ee; `git log -1 --format="%h parents: %p" eb27633c` is the merge of main 82deb62b)
```
$ git log --oneline eb27633c..HEAD; for c in <3 commits>: git show $c:RBM3D/Evolution/CltFarG.lean | wc -l  (the stop-rule counts at the section commits)
9bedb306 T2479b: CltFarG sections 6-7 (band producers, band bridge, instances), root import
c01f7ded T2479b: CltFarG sections 4-5 (window fluctuation, the pin stCltFargL_holds)
ffc00e76 T2479b: CltFarG sections 1-3 (good event, per-label tail, per-index bounds, off-window part)
eb27633c parents: 03f828ee 82deb62b
ffc00e76      532
c01f7ded      894
9bedb306     1070
$ git rev-parse --short HEAD; wc -l RBM3D/Evolution/CltFarG.lean; git diff main...t/T2479b --name-only; grep -n "^import" RBM3D/Evolution/CltFarG.lean; git diff main...t/T2479b -- <6 band+G files> RBM3D/Chain RBM3D/Induction RBM3D/BA | wc -l
9bedb306
    1070 RBM3D/Evolution/CltFarG.lean
RBM3D.lean
RBM3D/Evolution/CltFarG.lean
6:import RBM3D.Evolution.CltFar
7:import RBM3D.Evolution.CltMoments2G
8:import RBM3D.Evolution.MeanFarG
       0
$ grep -n "## [0-9]\." RBM3D/Evolution/CltFarG.lean | cut -c1-60   (instance section = section 7)
69:/-! ## 1. The single good event and the per-label tail (t
170:/-! ## 2. Per-index bounds: the propagator, `𝒦`, the wei
340:/-! ## 3. Target 5b: the off-window part `CltMom2.offg` 
541:/-! ## 4. Target 5c: the window fluctuation `c_n · flucg
771:/-! ## 5. Target 6: the pin `STCltFargL` -/
903:/-! ## 6. The band: the producers of `STThPropsg`, `STKp
952:/-! ## 7. Compiled nonempty instances (`d = 3`, band dat
```
1070 lines in all, 951 before the instance section (`CltFarG:952-1070`), against the stop line 2,000 and the reserve rule 1,800: `CltFarG2` is not needed. (a) predicted 958 (instance section excluded).
**b2. Reuse table (iii)** (`python3 -I reuse.py`: the 73 declarations of `Evolution/CltFar.lean` before its instance section)
```
open private (36): cltFar_ell_sq, cltFar_c3, cltFar_c0, cltFar_c3_pos, cltFar_polylog, cltFarZ, cltFar_one_le_L, cltFar_one_le_W, cltFar_Lpow_le, cltFar_Wpow_le, cltFar_L_le, cltFar_W_le, cltFar_one_le_N, cltFar_card_Zd, cltFar_card_pair_le, cltFar_W_rpow_le, cltFar_dom_key, cltFar_dom_tail, cltFar_wpow_le, cltFar_one_sub_ge, cltFar_double_sum_le, cltFar_zeta_off, cltFar_off_numeric, cltFar_Npow_le_W, cltFarKp, cltFarKp_nonneg, cltFar_Lp_le, cltFar_Bq_le, cltFar_Gq_le, cltFar_R_le, cltFar_assemble, cltFar_theta_eq, cltFar_theta_ge, cltFar_zeta_ge, cltFar_union_bound, cltFar_union_numeric
restated (20): cltFar_B_bound->meanFarG_B_bound (open private), cltFar_good_event->cltFarG_good_event, cltFar_bad_one->cltFarG_bad_one, cltFar_dom->cltFar_domg, CltFarH5->cltFarG_H, cltFar_Theta_all->cltFarG_Theta_all (+cltFarG_inputs), cltFar_K_le->STKpropsg conj 2 (cltFarG_inputs), cltFar_K_le'->cltFarG_inputs (c1/A <= c1), cltFar_Z_le->cltFarG_Z_le, cltFar_ZZ_le->cltFarG_ZZ_le, cltFar_eta_inv_le->cltFarG_eta_inv_le, cltFar_BY_le->cltFarG_BY_le, cltFar_off_sum_le->cltFarG_off_sum_le, cltFar_off_det->cltFarG_off_det, cltFar_off->cltFar_offg, cltFar_BYw_le->cltFarG_BYw_le, cltFar_rhs_bound->cltFarG_rhs_bound, cltFar_fluc->cltFar_flucg, cltFar_far_le->cltFarG_far_le, stCltFar_holds->stCltFargL_holds
band only (17): CltFar.DomStmt, CltFar.OffStmt, CltFar.FlucStmt, cltFar_norm_integral_le, cltFar_K_eq, cltFar_Theta_shift, cltFar_Bparam_le, cltFar_BctlSTWB, cltFar_n_K, cltFar_three_halves, cltFar_size_real, cltFar_mE_im_ge, cltFar_Theta_sup, cltFar_H5_at, cltFar_N_le_W, cltFar_div_step, cltFar_fluc_numeric
band declarations before the instance section: 73
```
Of the 17 band-only declarations: `DomStmt/OffStmt/FlucStmt` (no reader), `cltFar_K_eq`, `cltFar_Theta_shift`, `cltFar_n_K`, `cltFar_mE_im_ge`, `cltFar_Theta_sup`, `cltFar_H5_at` (band propagator and `|E| <= 2 - kappa`: supplied by `STThPropsg`, `STKpropsg`); `cltFar_norm_integral_le`, `cltFar_Bparam_le`, `cltFar_BctlSTWB`, `cltFar_three_halves`, `cltFar_size_real`, `cltFar_N_le_W`, `cltFar_div_step`, `cltFar_fluc_numeric` are model-free and are used inside the reused lemmas (not named in `CltFarG`). Also reused by name: `meanFar_T1` (`Theta_all`), `cltMom2_decompg`, `cltMom2_tail_eventuallyg`, `meanFar_eventuallyg`, `cltMom2G_lenv_of_rep`, `meanFarG_lenv_of_rep`, `stCltIsogL_holds`, `stExpInvgL_band`, `cltRepg_band`; the `HCltOf` term of the bridge is the pattern of `stCltIso_holds` (`CltStep:1556-1573`), copied.
**b3. Hypothesis table (iv)** (band fact the segment reads -> premise that supplies it; every fact has one, the stop rule did not fire)
- `|E n| <= 2 - kappa`, `kappa' = min kappa (1/2) <= Im (mE (E n))` -> `forall n, kappa <= (C.m n).im` (`HCltOf` field 6; `kappa' = kappa`); `||mE|| = 1`, `PropSpin`, `Theta` are not read.
- measurability and `||L|| <= eta^-2` of the loops, `IsProbabilityMeasure mu` -> `CltRepg` (field 11) with `kappa <= Im m` (`meanFarG_lenv_of_rep`, `cltMom2G_lenv_of_rep`, `CltRepg.1`).
- `STGdecayW` -> `STGdecayWgL` (field 15); `STCltIsoConcl` -> `STCltIsoConclgL` (`stCltIsogL_holds` on the same `HCltOf`); `Admissible c d` -> field 5; `0 <= s < t < 1` -> fields 7-9; regime `lam^2/L^2 <= 1-t`, `1-s <= lam^2` -> `STReg5I sz s t`.
- `Theta` shift and `(prop:ThfadC)` (sup bound `c_Theta/g^2` through `meanFar_T1`) -> `STThPropsg` conjuncts 1, 3 (`cltFarG_Theta_all`, `cltFarG_inputs`); `||K^(2)_s|| <= c1/A` -> `STKpropsg` conjunct 2 (`c1/A <= c1`, `A >= 1` from `WO`); `c_Theta := max (C5 (1+2^(d-1))) c1`.
- mean part (target 4, X1b-1) -> `meanFar_eventuallyg` (`STThPropsg` 1, 3, 5; `STKpropsg` 1, 2; `STExpInvgL`); weights and moment bound (X1b-1) -> `STThPropsg` 1, 3, 4; target 7 (band) -> `prop5Decay_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`, `KLK_two`, `Theta` shift/symmetry.
**b4. Target statements, extracted by script** (`python3 -I stmts.py RBM3D/Evolution/CltFarG.lean`; the 7 non-private declarations; binders `{d} {sz} (C) (mu)` of targets 5 are section variables)
```
CltFarG.lean:110: theorem cltFar_domg :: (hd : 3 ≤ d) {𝔠 𝔡 Cd : ℝ} (hAdm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, CltMom2.DomHypg C μ n (s n) σ (((sz.size n : ℕ) : ℝ) ^ τ) (((sz.size n : ℕ) : ℝ) ^ (-D₁))
CltFarG.lean:482: theorem cltFar_offg :: {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1) (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd) (hTh : STThPropsg C) (hKp : STKpropsg C s) (D D' : ℝ) (hD : 0 < D) (hD' : 0 < D') : ∀ᶠ n in atTop, μ {ω | ∃ σ : Fin 2 → Bool, σ 0 ≠ σ 1 ∧ ∃ a : Fin 2 → Zd d (sz.L n), ((sz.W n : ℕ) : ℝ) ^ (-D) < ‖CltMom2.offg C μ n (s n) (t n) σ a ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))
CltFarG.lean:651: theorem cltFar_flucg :: {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1) (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd) (hTh : STThPropsg C) (hKp : STKpropsg C s) (hiso : STCltIsoConclgL C μ s) (τ D : ℝ) (hτ : 0 < τ) (hD : 0 < D) : ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n), μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) < ‖(((1 - s n) ^ 2 / (sz.lam n ^ 4 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ)) : ℝ) : ℂ) * CltMom2.flucg C μ n (s n) (t n) σ a ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
CltFarG.lean:807: theorem stCltFargL_holds :: (d : ℕ) : STCltFargL d
CltFarG.lean:911: theorem bandFM_STThPropsg :: {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E : ℕ → ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) : STThPropsg (bandFM sz E)
CltFarG.lean:917: theorem bandFM_STKpropsg :: {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E s t : ℕ → ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1) (hreg : STReg5I sz s t) : STKpropsg (bandFM sz E) s
CltFarG.lean:926: theorem stCltFar_of_gL :: (d : ℕ) (hF : STCltFargL d) : STCltFar d
```
Statement check against the ticket pins (`stmtcheck.lean`: the `def T2479_*` text of `docs/tickets/checks/T2479-check.lean` copied by script, then the four lines below; `lake env lean`):
```
/-! statement checks: each new public theorem against the check's pin -/
example : T2479_FarPin := stCltFargL_holds
example : T2479_ThPropsBand := @bandFM_STThPropsg
example : T2479_KPropsBand := @bandFM_STKpropsg
example : T2479_BandFar := stCltFar_of_gL
exit=0
```
Premise changes against `T2479_ThPropsBand`, `T2479_KPropsBand`: none (the examples are `@`-applications that elaborate against the check text, so binder order and hypotheses agree up to definitional unfolding). `T2479_FarPin`, `T2479_BandFar` hold as `stCltFargL_holds`, `stCltFar_of_gL`. Targets 5 (`cltFar_domg`, `cltFar_offg`, `cltFar_flucg`) have no pin in the check; their premises are fields of `HCltOf` plus the pins (b3).
**b5. Greps** (ticket target 10; statement lines of the 7 new public declarations, `stmts.out`)
```
X1-C1 hits (statement text; line = declaration):
  5 bandFM_STThPropsg
  6 bandFM_STKpropsg
UBA-C1 (gK|withLam|lam0|BAflowLam0|seqHflowBA) hits: 0
TN-C4 (STGridRepNgL) hits in the file: 0
X1-C4 (def|abbrev|structure of the pins) hits in the file: 0
U-C4 def lines in the file:
178:private def cltFarG_H (n : ℕ) (C₅ c₅ : ℝ) : Prop :=
U-C4 (Ring.inverse|Matrix.of|Theta d) hits in the file: 0
sorry|admit|native_decide|axiom hits: 0
```
X1-C1: the two hits are `bandFM_STThPropsg`, `bandFM_STKpropsg` (target 7, premise `|E n| <= 2 - kappa`: band side, allowed); no hit in targets 5, 6, 8 (their statements are generic). `cltFarG_H` (private) is a `Prop` about `STThg`, `Bparam`, no kernel or propagator is built.
**b6. Registry lines and root import**
```
$ git diff main...t/T2479b -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-]"
--- a/RBM3D.lean
+++ b/RBM3D.lean
+import RBM3D.Evolution.CltFarG
$ grep -n "premises found by scanning\|^registry:\|unregistered" <full lake build log>
5896:premises found by scanning: 127 (borrowed 1, owed 61, structural 45, refuted 6, superseded 14).
5897:registry: 2 borrowed + 111 owed + 122 structural + 7 refuted + 18 superseded; 133 registered premise(s) carry nothing yet: [R
```
No new registry line: the whole-library build (which runs the scan of `Test/Axioms.lean`, an error on any unregistered premise) passes with `import RBM3D.Evolution.CltFarG` in `RBM3D.lean`. The scan counts of the already registered `STThPropsg`, `STKpropsg`, `STCltIsoConclgL`, `CltMom2.DomHypg` rose from 5, 1, 2, 2 (`T2479-prove.md` b8) to 8, 4, 3, 3 (the full-build log, `RBM.BA.STThPropsg: 8 ...`); no other premise is new. `STCltFargL` gets no line (target 6 proves it).
**b7. The compiled nonempty instances** (`d = 3`, band data of `Step5Inst`: `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`)
```
$ python3 -I examples.py RBM3D/Evolution/CltFarG.lean
CltFarG.lean:977: example : STThPropsg (bandFM szCL (STflowE zCL)) :=
CltFarG.lean:980: example : STKpropsg (bandFM szCL (STflowE zCL)) sCL :=
CltFarG.lean:986: example (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
CltFarG.lean:1006: example (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
CltFarG.lean:1019: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
CltFarG.lean:1040: example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
CltFarG.lean:1049: example (n : ℕ) := szCL_cltFar_index_nonempty n
CltFarG.lean:1052: example : STCltFar 3 := stCltFar_of_gL 3 (stCltFargL_holds 3)
CltFarG.lean:1055: example : ∀ d : ℕ, STCltFargL d := stCltFargL_holds
CltFarG.lean:1056: example : ∀ d : ℕ, STCltFargL d → STCltFar d := stCltFar_of_gL
$ sed -n '1037,1052p' RBM3D/Evolution/CltFarG.lean   (target 6 and target 8, verbatim)
/-- **Instance of target 6** (`stCltFargL_holds`, the pin `STCltFargL 3`) at the band data: `HCltOf` is `cltGood_hCltOf_szCL`,
`STReg5I` is `szCL_reg5I`, `STThPropsg`, `STKpropsg` are targets 7a, 7b, `STExpInvgL` is `stExpInvgL_band`; the index set of the
conclusion is nonempty at every `n` (the next example). -/
example (hLoc : STLocalEntryUgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL)
    (hDec : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
    STCltFarConclgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL :=
  stCltFargL_holds 3 (1 / 2) (1 / 10) (1 / 6) (1 / 10) 1 szCL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) szCL.lam
    (STflowE zCL) (fun _ => 0) sCL tCL (cltGood_hCltOf_szCL hLoc hDec) szCL_reg5I cltFarG_chk_Th cltFarG_chk_K
    (stExpInvgL_band szCL _)

/-- The index set of `STCltFarConclgL` at `(szCL, sCL, tCL)` is nonempty at every `n` (merged `szCL_cltFar_index_nonempty`; it is the
index type of `STCltFarConcl`): the instance of target 6 is not vacuous. -/
example (n : ℕ) := szCL_cltFar_index_nonempty n

/-- **Instance of target 8**: the band pin `STCltFar 3` from the generic pin. -/
example : STCltFar 3 := stCltFar_of_gL 3 (stCltFargL_holds 3)
```
Discharged at the data: `Admissible (1/6) (1/10)`, `kappa = 1/2 <= Im m`, `0 <= sCL < tCL < 1`, `CltRepg` (`cltRepg_band`), `STReg5I` (`szCL_reg5I`), `STExpInvgL` (`stExpInvgL_band`), `STThPropsg`, `STKpropsg` (targets 7a, 7b), `HCltOf` (`cltGood_hCltOf_szCL`), `STCltIsoConclgL` (`stCltIsogL_holds`). The only hypotheses of the examples are `STLocalEntryUgL`, `STGdecayWgL` (Step 2 pins, another gate). The index set of `STCltFarConclgL` is nonempty at every `n` (`szCL_cltFar_index_nonempty`, line 1049); the flucg instance uses `sigma = (+,-)`, `a = (x_n, 0)`, `|a_1 - a_2| = L_n/2`; the dom instance states `DomHypg` for every `sigma` and `beta` and then specialises to `beta = (0,0)` (window radius `(log W_n)^3 ell_s > 0`).
**b8. Builds, check file, axioms**
```
$ lake build RBM3D.Evolution.CltFarG | tail -3; warnings in CltFarG.lean
info: RBM3D/Evolution/CltFarG.lean:1066:0: 'RBM.BA.stCltFar_of_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3825 jobs).
lake build RBM3D.Evolution.CltFarG  20.85s user 4.88s system 224% cpu 11.445 total
warnings in CltFarG.lean: 0
$ lake build   (whole library, runs #assert_rbm_axioms) | tail
non-vacuity certificates: 0 of 113 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4323 jobs).
lake build  54.73s user 5.08s system 104% cpu 56.970 total
5777:info: RBM3D.lean:555:0: axiom audit: 14220 theorems, 4492 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean docs/tickets/checks/T2479-check.lean
exit=0 error-lines=0
$ #print axioms of the 7 public declarations (lines 1060-1066 of the file, in the build log)
CltFarG.lean:1060:0: 'RBM.BA.cltFar_domg' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1061:0: 'RBM.BA.cltFar_offg' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1062:0: 'RBM.BA.cltFar_flucg' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1063:0: 'RBM.BA.stCltFargL_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1064:0: 'RBM.BA.bandFM_STThPropsg' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1065:0: 'RBM.BA.bandFM_STKpropsg' depends on axioms: [propext, Classical.choice, Quot.sound]
CltFarG.lean:1066:0: 'RBM.BA.stCltFar_of_gL' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**b9. Name clash** of the 7 public names and the stem `cltFarG_` (`git grep -nE "<7 names|cltFarG_>" <ref> -- RBM3D/*.lean RBM3D.lean | wc -l`)
```
main:        3
t/T2469b:        0
t/T2471b:        0
t/T2472:        0
t/T2473:        0
t/T2474:        0
t/T2475:        0
t/T2476:        0
t/T2477:        0
t/T2478:        0
t/T2479:        3
$ git grep -nE "<pattern>" main -- ... | cut -c1-110   (the 3 hits on main)
main:RBM3D/Evolution/CltMoments2G.lean:589:/-- The band producer of `STThPropsg` (the statement of the second 
main:RBM3D/Test/Axioms.lean:222:   `RBM.BA.STThPropsg, -- shift, symmetry, `(prop:ThfadC)`, `(prop:BD1)`, `(pr
main:RBM3D/Test/Axioms.lean:223:   `RBM.BA.STKpropsg, -- invariance of `𝒦^{(2)}` under translations and the re
```
The 3 hits on `main` (and on `t/T2479`) are comments: a docstring in `CltMoments2G.lean:589` and the registry comments `Test/Axioms.lean:222-223` that name `bandFM_STThPropsg`, `bandFM_STKpropsg` as the second row's producers. No declaration clash; `main` is at 6039f7ed now (T2478 merged after this branch took 82deb62b).
**b10. X1-C5 tripwire** (`python3 -I gtab.py`; band `CltFar.lean` declarations against their `CltFarG` restatements, blank and `--` lines dropped, `g = (added + removed)/band lines` by `difflib`; `f_sem` = band lines of lemmas moved to the band producers, i.e. read from the pins, over (band lines + moved lines))
```
segment       band   gen  added  removed  g=(a+r)/band  moved  f_sem
good event      25    25      9        9         0.720      0  0.000
dom             55    57     11        9         0.364      0  0.000
perN           109   143     94       60         1.413     40  0.268
off            180   177     61       64         0.694      0  0.000
fluc           200   202     59       57         0.580      0  0.000
far            120   114     38       44         0.683      0  0.000
moved-lemma names found in band: ['cltFar_H5_at', 'CltFarH5', 'cltFar_Theta_all', 'cltFar_K_le', "cltFar_K_le'"]
```
`f_sem` is at most 0.268 (perN: `CltFarH5`, `cltFar_H5_at`, `cltFar_Theta_all`, `cltFar_K_le`, `cltFar_K_le'` replaced by `cltFarG_H`, `cltFarG_Theta_all`, `cltFarG_inputs`), below 0.30; `g` is 0.36-0.72 on the other five rows and 1.41 on perN (where the band lemmas were rewritten into the pin form). No twin needed.
**Narrative.**
1. Row. X1b-2 of the pre-signed split of T2479: targets 5-9 in `RBM3D/Evolution/CltFarG.lean` (new); `RBM3D.lean` gets its root import line. No band, chain, induction or BA file is edited (b1: the three-dot diff touches `RBM3D.lean` and `CltFarG.lean` only; 0 lines in the band files). Imports are exactly `CltFar`, `CltMoments2G`, `MeanFarG`; `CltFarG2` is not created.
2. Size. 1070 lines in 3 section commits (532, 894, 1070); 951 before the instance section against the predicted central 958 of (a). No stop rule fired: no file above 2,000, every band fact has a premise (b3), no `BA/*` or `IniTerm*` import, one propagator `STThg`, no comparison text (b5), `f_sem` 0.268 at most (b10).
3. Method. The model-dependent band lemmas of `CltFar.lean:308-1857` are restated over `(C, mu)` under the stem `cltFarG_`, with `STThg` for `Theta`, `C.L - C.K` for `STLKM`, `etaOf (C.m n)` for `etaT E`, `kappa <= Im (C.m n)` for the band spectral facts (`kappa' = kappa`), `STGdecayWgL` for `STGdecayW`. 36 model-free or size-level private lemmas of `CltFar` come in by `open private` (b2), as do `meanFarG_B`, `meanFarG_B_bound` of X1b-1.
4. One constant for the propagator and the kernel. `cltFarG_inputs` turns `STThPropsg` (conjuncts 1, 3, `meanFar_T1`) and `STKpropsg` (conjunct 2, `A >= 1`) into one `c_Theta >= 0` with `||Theta_t(x,y)|| <= c_Theta/g^2` and `||K_s|| <= c_Theta` (mixed charges, eventually in `n`); the off-window, envelope and moment lemmas take these two bounds as hypotheses and do not read the pins again.
5. Statements. `cltFar_domg` holds for every `sigma` (its premises are the admissibility, `STReg5I`, `STGdecayWgL`); `cltFar_offg` and `cltFar_flucg` quantify mixed `sigma` (the range of `STThPropsg`, `STKpropsg` and the index set `{sigma // sigma 0 != sigma 1}` of the merged `STCltFarConclgL`; the band `cltFar_off` was for every `sigma`). `stCltFargL_holds d : STCltFargL d` is the merged pin, no premise added; `stCltFar_of_gL` builds `HCltOf` as `stCltIso_holds` does (`cltCk (kappa/2)`, `eps/2`) and applies targets 7a, 7b at `kappa/2`.
6. Target 7. The proofs of `bandFM_STThPropsg`, `bandFM_STKpropsg` are the private producers `meanFarG_chk_Th`, `meanFarG_chk_K` of X1b-1 (merged, 82deb62b), brought in by `open private`, so `CltFarG` adds no further copy (the copies `cltMom2G_chk_Th` in `CltMoments2G` and `meanFarG_chk_Th`, `meanFarG_chk_K` in `MeanFarG` are X1b-1's, merged); the statements equal `T2479_ThPropsBand`, `T2479_KPropsBand` (b4). 
7. Instances (b7). Target 6 at the band data takes `cltGood_hCltOf_szCL`; examples: line 977 target 7a, 980 7b, 986 5a, 1006 5b, 1019 5c, 1040 target 6, 1049 index set, 1052 target 8, 1055-1056 the check pins; all deterministic premises are discharged and the two Step 2 pins stay hypotheses.
8. Estimate check. X1b-1 actual-over-central was 1.08 (its report); here 951/958 = 0.99 like for like.
## (c) Verified Mathlib names (each by `#check` in `scratchpad/T2479b/names.lean`, importing `RBM3D.Evolution.CltFarG`: exit 0, 0 errors, 43 checks; names verified absent: none searched)
`Nat.ceil_pos`, `Nat.le_ceil`, `Real.tendsto_log_atTop`, `Filter.Tendsto.const_mul_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `Fintype.card_subtype_le`, `Fintype.card_prod`, `Finset.sum_le_card_nsmul`, `div_le_div_of_nonneg_right`, `div_pos`, `div_le_self`, `inv_anti₀`, `pow_le_pow_left₀`, `Real.rpow_le_rpow_of_exponent_le`, `Real.log_le_log`, `Real.log_rpow`, `Real.rpow_two`, `norm_sub_le`, `norm_add_le`, `div_lt_iff₀'`, `ENNReal.ofReal_le_ofReal`, `Filter.eventually_ge_atTop`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_add`, `Real.rpow_natCast`, `Real.one_le_rpow`, `nsmul_eq_mul`, `Real.norm_of_nonneg`, `Complex.norm_real`, `le_max_of_le_right`, `le_max_left`, `le_max_right`, `MeasureTheory.measure_mono`, `Set.mem_iUnion`, `Set.mem_union`, `one_le_pow₀`, `Real.log_nonneg`, `Filter.Eventually.and`, `Filter.Tendsto.eventually_ge_atTop`, `Filter.Tendsto.eventually_gt_atTop`, `Finset.card_univ`. All other names occur in text copied from the compile-checked band files. `measure_mono` needs the namespace `MeasureTheory` (unqualified it is unknown without `open`).
## (d) Open issues and paper-delta candidates
- O1 (X1b-1's O1: target 7 written three times in private form). The public `bandFM_STThPropsg`, `bandFM_STKpropsg` reuse the private producers of `MeanFarG` by `open private` (`meanFarG_chk_Th`, `_K`, `_m`, `_t1`, `_E`), so no new copy; the private copies `cltMom2G_chk_Th` (`CltMoments2G`) and `meanFarG_chk_Th`, `_K` (`MeanFarG`) remain (merged files, not edited). Risk: a later rename or removal of those privates in `MeanFarG` breaks `CltFarG`.
- O2. `Test/Axioms.lean:222-223` (written by X1b-1) list only X1b-1 users of `STThPropsg`, `STKpropsg` as "hypothesis of ..."; the new users are `cltFar_offg`, `cltFar_flucg` (and `stCltFargL_holds` through the pin). Not edited (the ticket makes the file append-only); the comment is not false.
- O3. The branch is not rebased on `main` 6039f7ed (T2478 merged after this branch took 82deb62b). `RBM3D.lean` differs there only by one added import line after the last `import`; the hub keeps both lines.
- O4. `T2479_MeanFarg` (target 4) remains an example in `MeanFarG` (X1b-1); target 6 reads the fields of `HCltOf` directly.
- O5. The ticket's check file has no pin for target 5; the three statements are proposals (premises: fields of `HCltOf`, `STReg5I`, `STThPropsg`, `STKpropsg`, `STCltIsoConclgL`).
- Paper-delta candidates. `T2479c`: the far steps over the carrier take their constants from the pins: `c_Theta = max (C5 (1+2^(d-1))) c1` (propagator sup bound and `||K|| <= c1/A`), not `C5 (1+2^(d-1))` for both as in the band `cltFar_K_le`; and `kappa' = kappa` instead of `min kappa (1/2)` (same family as `T2479b` of X1b-1). Observation, not a delta: `cltFar_offg` is for mixed charges only (the band `cltFar_off` was for every `sigma`), as the index set of the merged pin. No other Lean/paper statement difference was found in targets 5-9.
