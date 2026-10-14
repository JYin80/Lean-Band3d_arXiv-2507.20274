Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 14:18:26 UTC 2026

### (i) Exponent table (tuple `(law, Flow, mkM, Hf, Es, T0)` generic; BA = `(seqP∘withLam 0, BAFlow, baStep2Mat, seqHflowBA, BAflowEs, BAflowT0)`)
| row | quantity | value | constraint (source) | slack |
|---|---|---|---|---|
| 1 | dimension | `3 ≤ d` in every pin; instances `d = 3` | used only as `2 ≤ d` (`L^d ≥ L²`): `iterationsA_scale_Ig` `IterationsGen:505`, `st_hBA_I` `ScaleFacts3:323` | 1 |
| 2 | `𝔠d`, Step 3 (iii) (target 1) | `1/100` (pin `∃ 𝔠d ≤ 1/100`) | not consumed by the proof (`Step3:377-405`: only `step3_xB`, `(lRB1)`) | 0 vs pin text |
| 3 | `𝔠d`, Step 3 (i) (target 2) | `min c₁ c₂`, `0 < · ≤ 1/100` (`c₁` of `STOeqQtgL'`, `c₂` of `STIterationsgL'`) | `≤ 1/16` for `iterationsA_scale_Ig`; `2𝔠d ≤ 1/8` (`ρ² ≤ (2A)^{2𝔠d} ≤ 2A^{1/8}`) | 21/400 in `𝔠d`; 21/200 in `2𝔠d` |
| 4 | `𝔠d`, Step 3 (ii) (target 3) | `min c₁ c₂ ≤ 1/100` | `≤ 1/24` for `iterationsA_scale_IIg` `:514` (`T ρ² A^{7/8} = A^{-1/8+3𝔠d} ≤ 1`); `≤ 1/4` for `st_hBA_II` `:380` | 19/600; 6/25 |
| 5 | `𝔠d`, Step 4 (targets 4, 9) | the bootstrap pin's constant `≤ 1/100` | only the exponent of `STConStInd`; `st5_conStInd_mono` (`Step5Kit:101`): smaller exponent = stronger | n/a |
| 6 | `A, T, cB, cv, K` (i) | `A = λ²W^d`, `T = 2A⁻¹`, `2,2,2` | `T A^{3/4} = 2A^{-1/4} ≤ cB`; `T ρ² A^{7/8} = 2ρ²A^{-1/8} ≤ cB K` (ρ² ≤ K A^{1/8}) | exponent 1/4 (A ≥ 1) |
| 7 | `A, T, cB, cv, K` (ii) | `A = (W^{-d}B_s)⁻¹`, `T = A^{-1+𝔠d}`, `1,1,1` | `T A^{3/4} = A^{-1/4+𝔠d} ≤ 1`; `ρ² ≤ A^{2𝔠d} ≤ A^{1/8}` | `𝔠d`: 6/25; 21/200 |
| 8 | Step 3 (iii) window factor | `2^{k-1}` | `(1-s)B_s ≤ 2(1-u)B_u` for `λ² ≤ 1-u` (`step3_xB` `Step3:57`): `2(1+a)/(1+2a) ≤ 2`, `a = L^{-d}` | 0.0303 at `L=4, d=3` (script) |
| 9 | Step 4 skeleton | `p > 2/τ` for each `τ > 0` | `2/(4p) ≤ τ/4`, then `N^{τ/2}·RHS ≤ N^τ` (`Step4:60-150`) | `τ=1/10, p=21`: 0.00119 (script) |
| 10 | `Aof κ` (BA, R1) | `(κ+1)/κ` | `1 ≤ Aof`; `g₀² ≤ λ²`; `λ² ≤ Aof g₀²` (`TwistStep2_lam0_sq` `:740`, `g₀² = T0 λ²`, `T0 ≥ κ/(κ+1)` `:731`); `0 ≤ g₀λ` (sqrt) | `1/κ` for `Aof ≥ 1`; `λ² ≤ Aof g₀²` is equality at `T0 = κ/(κ+1)` (non-strict, closes); `g₀² ≤ λ²`: `(1-T0)λ²` |
| 11 | D1 `C5` (target 6) | `C(d, k, 𝔡⁻¹, κ, A=(κ+1)/κ)` of `baEKSumDecayNonzeroA_holds` `EKGenBA:262` (`3 ≤ d`, `2 ≤ k`, `0<Λ,κ,A`) | `∃ C5` after `(k, κ, 𝔡)`, before `(sz, ε, 𝔠, z)`: the constant does not depend on `n, sz, z` | ordering closes |
| 12 | D1 window | `(1-v)L_n² ≤ Aof κ · g₀_n²`, `0 ≤ v ≤ w < 1`; `Λ = 𝔡⁻¹` from `BAflow_lam0_window` (eventually) | nonempty: `v ∈ [1 - A g₀²/L², w]` since `A g₀² > 0` | script rows "D1 window" |
| 13 | `τ` of `hT0` | `ε/2` | `N^{-1+ε/2} ≤ 1-T0`: from `1-T0 ≥ Im z/2 ≥ N^{-1+ε}/2` and `N^{ε/2} ≥ 2` (`baFlow_premises` `NetLiftBA:65`, via `EMn2BA_one_sub_T0` `EMn2BA:111`: `Im z/2 ≤ 1-T0`) | `N_0^{ε/2} = 2.0705 ≥ 2` at `sz0` (script) |
| 14 | `IterationsGen2_Fam` rows used | Step 3 (iii): rows 1, 2; Step 3 (i),(ii): rows 1-4 (eta ratio by `IterationsGen_eta_ratio` `IterationsGen:326`, scale facts `:505/:514`); Step 4: rows 1, 2 | rows 5-6 (`Step34Gen_LCompat`, Hermitian `Hf`) feed only `iterationsB_settingg`, which Steps 3-4 do not call (band `step3_assemble` `Step3:334`, `step4_of_ing` `Step4:156`) | no premise outside the bundle; Steps 3 (iii), 4 use a sub-bundle (table (iv), allowed) |
| 15 | regime inclusions (target 9) | `STReg5III ⊆ STCaseI`, `STReg5I ⊆ STCaseI`, `STReg5I = STRegIterI` (`MainIndRegimes:125, 137`; `Step34Pins:493`, `Step5Pins:44`) | `R' ⊆ R` for target 5 | exact |

### (ii) One concrete nondegenerate instance (`d = 3`, merged data; the pin binders `STKboundgL`, `STKwardgL`, `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'`, the two induction hypotheses stay hypotheses)
* Regime (iii) and STCaseI; targets 1, 6, 7 (a), 8 (iii), 9 (`STCaseI`, `STReg5III`): `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `λ=(2(n+1))^{-6}`), `z = zSeq`, `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`flow_sz0` `FlowPins:1214`), `2/3 ≤ T0` (`t0_sz0` `:1227`), `T0 ≤ 25/36` (`t0_sz0_le` `Step1Fam:753`); `s ≡ 1/2 < t ≡ 2/3`; `Aof(1/2) = 3`.
* STCaseII; targets 3, 7 (b), 8 (ii), 9 (`STCaseII`): `TwistStep2_szII` (`L≡4`, `W=n+25`, `λ≡5`), `TwistStep2_flowII` (`TwistStep2:1353`), `(κ,ε,𝔠,𝔡) = (3/5000, 1/2, 1/9, 1/10)`, `T0 ≥ 1/2000`; `s ≡ 0 < t ≡ 1/2000`.
* Regime (i) `STReg5I`; targets 2, 8 (i), 9 (`STReg5I`): `sz0` has no window (`λ_0 = 1/64` by `sz0_values`, so `1-s_0 ≤ 1/4096` forces `s_0 ≥ 4095/4096 > 25/36 ≥ T0_0 > s_0`, `t0_sz0_le`); private datum as `szI` (`ZeroModeBA:242-347`): `L≡4`, `W=n+25`, `λ≡2`, `(3/1000, 1/2, 1/9, 1/10)`, `T0 ≥ 1/400`, `s ≡ 0 < t ≡ 1/400`.
* External hypothesis `STConStInd 𝔠d s t` (`Defs:168`, eventually in `n`, for every produced `𝔠d > 0`): limit `Bctl_n(t) = W_n^{-3}[(λ_n²+x)⁻¹+(L_n³x)⁻¹] ≤ 2/(x W_n³) → 0` (`x = 1-t`, `W_n → ∞`), so `Bctl_n^{𝔠d} → 0 < (1-t)/(1-s)` (merged: `s1Setup_conStInd_const` `Step1Setup:1226` for `sz0`; `conStInd_const` `Step34Pins:825` for the `n+25` data). The thresholds below are illustrations at `𝔠d = 1/100`; for `𝔠d = 1/1000` at `sz0` the first `n` is 2.95e11, which is why the proof must use the limit lemma, not a witness.

Command and output (scratch script, no Lean: `python3 <scratchpad>/T2509/pf.py`, exact fractions, floats only for rpow):
```
== sz0 (iii),(i)-empty kappa 1/2 eps 1/10 s 1/2 t 2/3 T0>= 2/3  kappa/(kappa+1)= 0.3333333333333333 ok t<=T0 lower bd: True
   Aof=(k+1)/k = 3.0  R1: need T0*A>=1 : min T0 = 0.3333333333333333 *A = 1.0
   regime(iii) l^2<=1-t: True  regime(i): False  regime(ii) 1-s<=l^2/L^2: False
   t<1: True  s<t: True  s>=0: True
   n=0 N=2097152  N^(eps/2)=2.0705 (>=2)  N^(-1+eps/2)=9.873e-07 <= 1-t=0.33333
   n=1 N=549755813888  N^(eps/2)=3.8637 (>=2)  N^(-1+eps/2)=7.028e-12 <= 1-t=0.33333
   n=5 N=212986666247081951232  N^(eps/2)=10.3853 (>=2)  N^(-1+eps/2)=4.876e-20 <= 1-t=0.33333
   con_st_ind c=1/100: ratio=0.66667, first n0=8 (n0-1 fails: True), Bctl(n0)^c=0.65536
   con_st_ind c=1/1000: ratio=0.66667, first n0=295253706553 (n0-1 fails: True), Bctl(n0)^c=0.66667
   D1 window n=0: (1-v)L^2<=A*g0^2, g0^2>=2/3*lam^2 -> v>=0.999969 ; v in [max(0,vmin),w], w<1 nonempty: True
== szII (ii) kappa 3/5000 eps 1/2 s 0 t 1/2000 T0>= 1/2000  kappa/(kappa+1)= 0.0005996402158704777 ok t<=T0 lower bd: True
   Aof=(k+1)/k = 1667.6666666666667  R1: need T0*A>=1 : min T0 = 0.0005996402158704777 *A = 1.0
   regime(iii) l^2<=1-t: False  regime(i): False  regime(ii) 1-s<=l^2/L^2: True
   t<1: True  s<t: True  s>=0: True
   n=0 N=1000000  N^(eps/2)=31.6228 (>=2)  N^(-1+eps/2)=3.162e-05 <= 1-t=0.99950
   n=1 N=1124864  N^(eps/2)=32.5668 (>=2)  N^(-1+eps/2)=2.895e-05 <= 1-t=0.99950
   n=5 N=1728000  N^(eps/2)=36.2565 (>=2)  N^(-1+eps/2)=2.098e-05 <= 1-t=0.99950
   con_st_ind c=1/100: ratio=0.99950, first n0=0 (n0-1 fails: n/a), Bctl(n0)^c=0.88185
   con_st_ind c=1/1000: ratio=0.99950, first n0=0 (n0-1 fails: n/a), Bctl(n0)^c=0.98751
   D1 window n=0: (1-v)L^2<=A*g0^2, g0^2>=1/2000*lam^2 -> v>=0.000000 ; v in [max(0,vmin),w], w<1 nonempty: True
== szI (i) kappa 3/1000 eps 1/2 s 0 t 1/400 T0>= 1/400  kappa/(kappa+1)= 0.0029910269192422734 ok t<=T0 lower bd: True
   Aof=(k+1)/k = 334.3333333333333  R1: need T0*A>=1 : min T0 = 0.0029910269192422734 *A = 1.0
   regime(iii) l^2<=1-t: False  regime(i): True  regime(ii) 1-s<=l^2/L^2: False
   t<1: True  s<t: True  s>=0: True
   n=0 N=1000000  N^(eps/2)=31.6228 (>=2)  N^(-1+eps/2)=3.162e-05 <= 1-t=0.99750
   n=1 N=1124864  N^(eps/2)=32.5668 (>=2)  N^(-1+eps/2)=2.895e-05 <= 1-t=0.99750
   n=5 N=1728000  N^(eps/2)=36.2565 (>=2)  N^(-1+eps/2)=2.098e-05 <= 1-t=0.99750
   con_st_ind c=1/100: ratio=0.99750, first n0=0 (n0-1 fails: n/a), Bctl(n0)^c=0.89413
   con_st_ind c=1/1000: ratio=0.99750, first n0=0 (n0-1 fails: n/a), Bctl(n0)^c=0.98887
   D1 window n=0: (1-v)L^2<=A*g0^2, g0^2>=1/400*lam^2 -> v>=0.791042 ; v in [max(0,vmin),w], w<1 nonempty: True
== exponent table checks (exact fractions)
  case(i) iterationsA_scale_Ig: cd<=1/16                     value=1/100 bound=1/16 slack=21/400 ok=True
  case(i) rho^2<=(2A)^{2cd}<=2A^{1/8}: 2cd<=1/8              value=1/50 bound=1/8 slack=21/200 ok=True
  case(ii) iterationsA_scale_IIg: cd<=1/24 (T rho^2 A^{7/8}: -1/8+3cd<=0) value=1/100 bound=1/24 slack=19/600 ok=True
  case(ii) rho^2<=A^{2cd}<=A^{1/8}: 2cd<=1/8                 value=1/50 bound=1/8 slack=21/200 ok=True
  case(ii) T A^{3/4}=A^{-1/4+cd}<=1: cd<=1/4 (st_hBA_II)     value=1/100 bound=1/4 slack=6/25 ok=True
  case(i) T A^{3/4}=2A^{-1/4}<=cB=2: exponent 0<=1/4         value=0 bound=1/4 slack=1/4 ok=True
  case(i) 2^{2cd}=1.01396 <=2 ; scale c=1+(2^cd)^(r-1) at r=2: 2.00696
  Step3 pins: cd<=1/100 (pin text)                           value=1/100 bound=1/100 slack=0 ok=True
  Step3(iii) x*B_u>=W^-d(1/2+a), y*B_s<=W^-d(1+a): factor 2 -> ratio<=2(1+a)/(1+2a)<=2 ; a=L^-d at L=4,d=3: 1.96970
  Step4: tau=1/10 -> p>2/tau, p=21 : 2/(4p)=0.02381 <= tau/4=0.02500
  Step4: tau=1/20 -> p>2/tau, p=41 : 2/(4p)=0.01220 <= tau/4=0.01250
  RangeCond tau=eps/2 : N^{eps/2}>=2 needs N>=2^{2/eps}: eps=1/10 -> 1048576 ; sz0 N_0=2097152 ok=True ; eps=1/2 -> 16
```
Reading: regime (iii) holds at `sz0` (all `n < 300`), regime (i) holds at `szI`, regime (ii) at `szII`; the (i) window is empty at `sz0` (`regime(i): False`), as the ticket says. `t ≤ T0`, `s < t < 1`, `0 ≤ s`, the `RangeCond (ε/2)` margin, the R1 equality `T0_min · Aof = 1`, and a nonempty D1 window hold in each datum.

### Verdict
* Targets 1-5 (generic producers, `Chain/Step34RGen`): PASS (no premise outside `IterationsGen2_Fam`; rows 14; constants rows 2-9 close).
* Target 6 (`baQtNZGen_kerNZ`): PASS (rows 10-12; `C5` before `(sz, z)`).
* Targets 7-10 (BA bootstraps, Steps 3-4 per regime, instances): PASS (rows 10, 13, 15; instance data above).
* No pin, row or stop line moves; the generic producers need no premise outside `IterationsGen2_Fam`: no 1a-audit needed. Overall: PASS.

## (a′) Preflight corrections — Wed Oct 14 14:58:24 UTC 2026
* Row 15 / instance (ii): `STReg5I` and `STRegIterI` are equivalent, not equal (`∀ n, A n ∧ B n` against `(∀ n, A n) ∧ ∀ n, B n`); the proofs convert (`hregI`, `Step34BAInst_regI`).
* Row 14: bundle rows read: targets 1, 4 row 1 only; targets 2, 3 rows 1-4; rows 5-6 (`hLC`) by none of 1-5 (b7 last grep). No verdict changes.

## (b) Script output — Wed Oct 14 14:58:24 UTC 2026

### b1. Builds (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2509`, branch `t/T2509`)
```
$ lake build RBM3D.Chain.Step34RGen RBM3D.BA.Step34BA  -> Build completed successfully (4182 jobs). (lines matching 'error': 0)
$ lake build (whole library, `#assert_rbm_axioms`)  -> Build completed successfully (4406 jobs). (lines matching 'error': 0)
info: RBM3D.lean:636:0: axiom audit: 15362 theorems, 4725 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ git log --oneline b4147edc..t/T2509
0768f64d T2509: Step34BA header wording
d4eb5824 T2509: registry, STXiBootgL' left the owed list (DECISIONS §331 (6))
d92e8f35 T2509: BA/Step34BA (targets 6-10), registry owner texts, root imports
b16cd918 T2509: Chain/Step34RGen (targets 1-5: generic Steps 3-4 producers, band re-derivations, instances)
$ grep -nE 'sorry|admit|native_decide|^axiom' <both files> | wc -l  -> 0
```

### b2. `#print axioms` (scratch `ax_all.lean`)
```
35 of 35 declarations depend on exactly [propext, Classical.choice, Quot.sound]: the 5+10 targets (b3), the 5 band re-derivations `Step34RGenCheck.st*_holds_of_gen`, the 15 instance theorems (b5).
```

### b3. Target statements, extracted from the files by `stmts.py` (`<FAM>`, `<BA>` are the two strings printed last)
```
[1] stStep3RegIIIgL_of: <FAM> IterationsGen2_Fam d law Flow mkM Hf Es T0 → STStep3RgL d STReg5III law Flow (fun sz z => (mkM sz z).toFlowFM) T0
[2] stStep3RegIgL_of: <FAM> IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 → STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 → STStep3RgL d STReg5I law Flow (fun sz z => (mkM sz z).toFlowFM) T0
[3] stStep3IIgL_of: <FAM> IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtNZgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 → STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 → STStep3RgL d STCaseII law Flow (fun sz z => (mkM sz z).toFlowFM) T0
[4] stStep4RgL_of_ing: ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ), IterationsGen2_Fam d law Flow mkM Hf Es T0 → STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0 (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) → STStep4RgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
[5] stStep34RgL_mono: ∀ (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ), (∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) → (STStep3RgL d R law Flow mk T0 → STStep3RgL d R' law Flow mk T0) ∧ (STStep4RgL d R law Flow mk T0 → STStep4RgL d R' law Flow mk T0)
[6] baQtNZGen_kerNZ (d : ℕ) : QtNZGen_KerNZFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowLam0 sz z) (fun κ => (κ + 1) / κ)
[7a] baOeqQtgL'_holds (d : ℕ) : STOeqQtgL' d <BA>
[7b] baOeqQtNZgL'_holds (d : ℕ) : STOeqQtNZgL' d <BA>
[8iii] baStep3RegIII_holds (d : ℕ) : STStep3RgL d STReg5III <BA>
[8i] baStep3RegI_holds (d : ℕ) : STStep3RgL d STReg5I <BA>
[8ii] baStep3II_holds (d : ℕ) : STStep3RgL d STCaseII <BA>
[9i] baStep4I_holds (d : ℕ) : STStep4RgL d STCaseI <BA>
[9ii] baStep4II_holds (d : ℕ) : STStep4RgL d STCaseII <BA>
[9iii] baStep4RegIII_holds (d : ℕ) : STStep4RgL d STReg5III <BA>
[9iv] baStep4RegI_holds (d : ℕ) : STStep4RgL d STReg5I <BA>
<FAM> = ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
<BA>  = (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z)
```

### b4. Statement diff against the pins (the auditor's `example : T2509_X := <name>`, scratch `pins2.lean`, not committed)
```
$ lake env lean pins2.lean  (check Part 2 verbatim + T2507_KerNZ/Fam/BA verbatim + 17 examples)  -> exit 0, errors: 0
examples (T2509 pin <- proof term): T2507_KerNZBA <- baQtNZGen_kerNZ; T2509_KerNZBA <- baQtNZGen_kerNZ; T2509_OeqQtBA <- baOeqQtgL'_holds; T2509_OeqQtNZBA <- baOeqQtNZgL'_holds; T2509_Step3RegIIIBA <- baStep3RegIII_holds; T2509_Step3RegIBA <- baStep3RegI_holds; T2509_Step3IIBA <- baStep3II_holds; T2509_Step4IBA <- baStep4I_holds; T2509_Step4IIBA <- baStep4II_holds; T2509_Step4RegIIIBA <- baStep4RegIII_holds; T2509_Step4RegIBA <- baStep4RegI_holds; T2509_shape_V2aRead <- ⟨…⟩; T2509_Step3RegIIIOf <- stStep3RegIIIgL_of; T2509_Step3RegIOf <- stStep3RegIgL_of; T2509_Step3IIOf <- stStep3IIgL_of; T2509_Step4ROfIng <- stStep4RgL_of_ing; T2509_Step34Mono <- stStep34RgL_mono
$ lake env lean docs/tickets/checks/T2509-check.lean  -> exit 0, errors: 0
$ script diff, bodies (whitespace-collapsed) of T2509_KerNZBA (T2509-check:181) and T2507_KerNZBA (T2507-check:201) after T2507_KerNZFam -> QtNZGen_KerNZFam, T2507_KerNZBA -> T2509_KerNZBA -> identical
```

### b5. Compiled nonempty instances (every deterministic hypothesis discharged; `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STLmaxUgL` of Step 3 stay binders: other gates' pins)
```
Chain/Step34RGen: theorems inst_step3RegIIIgL@621 inst_step3RegIgL@638 inst_step3IIgL@657 inst_step4RgL@676 inst_step34Mono@694; examples (band pins `…_holds_of_gen` through `inst_step3R`/`inst_step4R`) @713 @717 @722 @727 @730
BA/Step34BA: theorems inst_baQtNZGen_kerNZ@290 inst_baOeqQtgL'@335 inst_baOeqQtNZgL'@347 inst_baStep3RegIII@359 inst_baStep3RegI@372 inst_baStep3II@385 inst_baStep4I@398 inst_baStep4II@412 inst_baStep4RegIII@426 inst_baStep4RegI@440; example (window of the D1 instance) @301
```

### b6. Registry scan (`import RBM3D` + `#assert_rbm_axioms` inside the full build); before = library without the two import lines (main b4147edc), after = branch tip
```
theorems in `RBM`: 15327 → 15362 (+35); definitions 4725 → 4725; axioms 0 → 0
theorems resting on a registered premise, changed entries (before→after): STStep3R 8→10, STLKgL 27→41, STLmaxUgL 6→18, STLKUgL 11→17, STXiBootgL' 9→(left the owed list), STStep2ConclgL 17→31, STStep1LoopgL 22→34
`RBM.BA.STXiBootgL'` in the "carry nothing yet" list: before True, after False (DECISIONS §331 (6): removed from `owedProps`, comment `-- T2509 ... left this list`)
registry: 2 borrowed + 122 owed + 140 structural + 7 refuted + 19 superseded; 157 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,   [before]
registry: 2 borrowed + 121 owed + 140 structural + 7 refuted + 19 superseded; 156 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,   [after]
```

### b7. Hypothesis rules (ticket commands; output)
```
$ C1 grep (mE|norm_mE|\|E\||SB d|BAK_le_small|BAMB_upper_small|Mbound_AO|W^(-eps|BAm_im_lower_window|STGridRepNgL) <both files>  -> 0 hits
$ X1-C4 grep '^(noncomputable )?(def|abbrev|structure) ' <both files>  -> 0 hits
$ UBA grep -n withLam <both files> minus the lines `seqP (<sz>.withLam 0)` (sz, sz0, szI, TwistStep2_szII)  -> 0 hits
$ band objects in file 1 before line 529 (`Step34RGenCheck`): grep -nE 'STFlow|STflowE|etaT|bandFM|bandStep2Mat|lemT'  -> 0 hits
$ grep -c gK / grep -c '^import RBM3D.BA' on file 1  -> 0 / 0
$ U5S-C3 grep -nE "∀ \(sz : Sizes d\)" <both files>: lines F1:290 F1:291 F1:293 F1:328 F1:329 F1:331 F1:361 F1:362 F1:364 F1:487 F1:488 F1:490 F1:513 F1:514 F1:515 F2:82 F2:91 F2:100 F2:114 (F1: family binders of the 5 producers and the inclusion of target 5; F2: the four slot theorems hSpec, hm, hR1, hT0)
$ grep -n 'hFl\.\|hProb sz\|hLoop sz\|(hLC' file 1 -> lines 299 300 342 343 344 345 375 376 377 378 500 501 (299-300 target 1, 342-345 target 2, 375-378 target 3, 500-501 target 4)
```

### b8. Name clashes, diff, line counts
```
$ clash.py: 35 new public names, searched in RBM3D/ and RBM3D.lean outside the two new files and Probe/ (word-bounded)  -> 32 names: 0 hits; stStep4RgL_of_ing(1 RBM3D/Test/Axioms.lean) baOeqQtgL'_holds(1 RBM3D/Test/Axioms.lean) baOeqQtNZgL'_holds(1 RBM3D/Test/Axioms.lean) in RBM3D/Test/Axioms.lean (registry comments of this ticket)
$ git diff --stat main...t/T2509 ->  RBM3D.lean|   2 +; RBM3D/BA/Step34BA.lean| 455 +++++++++++++++++++++++++++; RBM3D/Chain/Step34RGen.lean| 739 ++++++++++++++++++++++++++++++++++++++++++++; RBM3D/Test/Axioms.lean|   8 +-; 4 files changed, 1200 insertions(+), 4 deletions(-);
$ git diff main...t/T2509 -- RBM3D/Induction RBM3D/Chain/Step34Gen.lean RBM3D/Chain/IterationsGen2.lean | wc -l  -> 0   (G1)
$ grep -rl 'Step34RGen\|Step34BA' RBM3D RBM3D.lean  -> RBM3D/Test/Axioms.lean RBM3D/Chain/Step34RGen.lean RBM3D/BA/Step34BA.lean RBM3D.lean (Test/Axioms.lean: registry comments only)
$ wc -l  ->      739 Chain/Step34RGen.lean;     455 BA/Step34BA.lean;    1194 total; stop lines 1250 / 800
```

### b9. Narrative (the ticket's report items (1)-(9); the 1a fill-in rows (i)-(ix))
(i) constants: `𝔠d` target 1 `1/100` (not consumed, as band `Step3:377`); targets 2, 3 `min c₁ c₂ ≤ 1/100` (`c₁` of the bootstrap pin, `c₂` of the `lem:iterations` pin; `(con_st_ind)` at the minimum gives it at each, `st5_conStInd_mono`; the scale facts need `≤ 1/16` (i), `≤ 1/24` and `≤ 1/4` (ii), all implied); target 4 the ingredient pin's. `C5` = constant of `baEKSumDecayNonzeroA_holds d k 𝔡⁻¹ κ` at `A = (κ+1)/κ`, after `(k, κ, 𝔡)`, before `(sz, ε, 𝔠, z)`; `C₆` after `κ`; `Aof κ = (κ+1)/κ`; `τ = ε/2` (`baFlow_premises`).
(ii) twins. Written, private: `Step34RGen_{finish, skeleton, hbase, assemble, step4_skeleton, hscale_I, hscale_II, band_Kbound, band_Kward}` and the band bundle `Step34RGen_fam3`; `Step34BA_{hSpec, hm, hR1, hT0}`; `Step34BAInst_{K, con, regIII, regI}`. Reused by `open private`: `step3_xB`, `step3_psi0_le` (Induction/Step3), `iterationsB_K_pairsg` (IterationsGen2), `IterationsGen_Ep` (IterationsGen), `EKGenBA_hIm`, and the regime-(i) datum `szI zI flowI szI_window szI_regIterI` and `szII_caseII` of `BA/ZeroModeBA`. No scale twin is written: `Step34RGen_hscale_I/II` read the band `st_hscale_I'/II'` (ScaleFacts3:303, 310) at the energy `E'` with `η_{E'} = Cm.eta` (`IterationsGen_Ep`, as `iterationsA_scale_Ig`), `st_hBA_I/II` (:323, :380) are size-level and used as they are (the ticket priced 50 lines).
(iii) routes (merged `file:line`). 1: `step3_xB` (Induction/Step3:62) + `iterationsA_prec_absorbg` (Chain/IterationsGen:135) + `iterationsA_prec_mono_rightg` (:119) on `STStep1LoopgL`. 2, 3: `Step34RGen_assemble` = `_skeleton` + `_hbase` + `_finish` over `st_iterate` (ScaleFacts3:106) with `iterationsA_scale_Ig` (IterationsGen:505) / `iterationsA_scale_IIg` (:514), `Step34RGen_hscale_I/II`, `st_hBA_I/II`, `iterationsB_K_pairsg` (IterationsGen2:340), `iterationsA_apriori_of_lRB1g` (IterationsGen:377), `_avg_of_STAvgUg` (:346), `_rela_of_Kg` (:448), `st_prec_one_add_supg` (:47).
4: `Step34RGen_step4_skeleton` with `st_Bctl_ge` (ScaleFacts3:56), `st_prec_one_add_supg`, `st_prec_of_xig` (IterationsGen:73), `st_bootRHS_one`. 5: unfolding of the two pins. 6: `baEKSumDecayNonzeroA_holds` (BA/EKGenBA:262), `Step2Kern_UN_BA` (Chain/Step2Kern:124), `BAflow_lam0_window` (BA/GreenSchur:72), `BAflow_real` (:59). 7: `stOeqQtgL'_of` (Chain/QtXiRoundLiftGen:466), `stOeqQtNZgL'_of` (Chain/QtNonzeroBootGen:507), slots in (iv); `d < 3` vacuous (`by_cases`).
8: 1-3 at `baIterationsGen2_fam` (BA/ZeroModeBA:120), 7 and `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds` (:132, :140). 9: 4 at 7 (`STCaseI`, `STCaseII`); `STReg5III`, `STReg5I` by target 5 along `st_caseI_of_reg5III`, `st_caseI_of_reg5I` (Induction/MainIndRegimes:125, 137). 10: instances (vi).
(iv) family slots (27 of `stOeqQtgL'_of`, 25 of `stOeqQtNZgL'_of`): hSE `baSEforLn_holds d STAny` (BA/SEforLnBA:221); hFlow `Step2EventsGenTw_baFlow` (Chain/Step2EventsGenTw:53); hSpec `Step34BA_hSpec` (`κm` from `baStep5CasesGen_flowFacts`, SEforLnBA:152); hL `baStep2Mat_loopForm` (:135); hW `baStep2Mat_walkForm` (BA/GridDriftBA:71, `lam' = 0`, `Ψ = g₀•PsiI`); hLaw `Step2EventsGenTw_baLaw` (:63); hC `baStep34_LCompat` (SEforLnBA:122); hWard `DecayGenTw_baWardPair` (Chain/DecayGenTw:44); hKcal `baKcalDecay_holds` (BA/KDecayBA:692); hEK `baEtermDecaygL` (SEforLnBA:271, `3 ≤ d` by `by_cases`); hm `Step34BA_hm` (`BAm_norm_le_one`, BA/Ward:136); hSeq `baStep2Mat_S` (GridDriftBA:86); hS `baStep2Mat_S_rowSum` (:90); hRow `gridRepTailGen_ker_BA` (BA/GridRepTailBA:60); hKK `rfl`; hExp, hKL, hKT, hU `baHierDrift_classes` (GridDriftBA:631, `∀ n` for hExp, eventual for the rest); hKerFam `baNQGoodGen_kerNAL` (EKGenBA:456) / `baQtNZGen_kerNZ` (6); hR1 `Step34BA_hR1` / `TwistStep2_lam0_sq` (BA/TwistStep2:740); hT0 `Step34BA_hT0`; hEK4 `baQProxyG_kerEK4` (EKGenBA:471); hTh `baStep5KerGen_thDecay` (BA/Step5KerBA:132, binders `κ, 𝔡` -> `𝔡, κ`); hB45 `baB45Gen_facts` (BA/B45BA:205); hKLip `baKloop_lip` (BA/KLipBA:208); hFM `baLemDecCalELipG_flowMod` (Step5KerBA:390).
(v) UBA-C1: R1 enters only as the slot hR1 (7a: `1 ≤ Aof κ`, `0 ≤ g₀λ`, `g₀² ≤ λ²`, `λ² ≤ Aof κ g₀²`; 7b: `λ² ≤ Aof κ g₀²`, both from `TwistStep2_lam0_sq`, `0 ≤ g₀λ` by `g₀ = √t₀ λ`) and at D1 (6: window `(1 - v) L² ≤ Aof κ g₀²`). Regimes, `Bctl`, `STConStInd` in 1-5, 8-10 are size-level (`sz.lam`); file 1 has no `gK` (b7). C1: the statements carry `BAFlow`, `baFMz`, `BAflowLam0`, `κ`; `‖m‖ ≤ 1` is proved inside `Step34BA_hm`, not assumed; no `mE`, `|E|`, `SB d` (b7).
(vi) instance data (`d = 3`): A `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `zSeq`, `flow_sz0` at `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `t0_sz0: T₀ ≥ 2/3`, `s ≡ 1/2 < t ≡ 2/3`, `lam² ≤ 1/64 ≤ 1/3 = 1 - t` (`sz0_lam_L`), `Aof (1/2) = 3`; targets 6, 7a, 8 (iii), 9 (`STCaseI`, `STReg5III`). B `szI` (`L ≡ 4`, `W = n + 25`, `lam ≡ 2`), `flowI` at `(3/1000, 1/2, 1/9, 1/10)`, `T₀ ≥ 1/400`, `s ≡ 0 < t ≡ 1/400`; targets 8 (i), 9 (`STReg5I`). C `TwistStep2_szII` (`L ≡ 4`, `W = n + 25`, `lam ≡ 5`), `TwistStep2_flowII` at `(3/5000, 1/2, 1/9, 1/10)`, `T₀ ≥ 1/2000`, `s ≡ 0 < t ≡ 1/2000`; targets 7b, 8 (ii), 9 (`STCaseII`). Target 6 at `k = 3`, `(κ, 𝔡) = (1/2, 1/10)`, `(sz0, zSeq)`: the `example` takes an index with `0 < g₀`, `v = w = 1 - 3 g₀²/L²` (window nonempty, `3 g₀² ≤ 1 ≤ L²`) and applies the D1 bound at `σ = (+,-,+)`, `Aset = univ`, `X ≡ 1`. File 1: band family (`IterationsGen2_famBand 3`), `sz0` `(0, 1/16)`, `szB` `(7/8, 15/16)`, `(15/16, 31/32)`; `STKboundgL`, `STKwardgL`, the bootstrap and `lem:iterations` pins discharged.
(vii) registry: b6; (viii) lines: 739 / 455 against bottom-up 800 / 500 and stop lines 1250 / 800 (row total 1194 against 1,300 bottom-up and 1,320-1,840 calibrated, i.e. below the calibrated range; the ticket's 50 lines for scale twins and its ≤ 120 lines for a private datum were not spent, see (ii)); (ix) name clashes: b8.
Deviations from the ticket text (none changes a pinned statement): file 1 also imports `Chain/QtXiRoundLiftGen`, `Chain/QtNonzeroBootGen` (the band re-derivations 5′ read `stOeqQtgL'_band`, `stOeqQtNZgL'_band`; still no `BA/*`); `:214` is removed from `owedProps` under DECISIONS §331 (6) (b6); the regime-(i) datum is read from `BA/ZeroModeBA` by `open private` instead of a new private datum.

## (c) Mathlib names (the ones introduced by this ticket; verified by `#check` in `mlib.lean`, all other names are in the band text ported, compile-verified)
@one_le_div : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α}, 0 < b → (1 ≤ a / b ↔ b ≤ a)
Nat.one_le_pow : ∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
@div_mul_cancel₀ : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] {b : G₀} (a : G₀), b ≠ 0 → a / b * b = a
@sub_sub_cancel : ∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G), a - (a - b) = b
@div_le_one : ∀ {α : Type u_1} [inst : Semifield α] [inst_1 : PartialOrder α] [PosMulReflectLT α] {a b : α}, 0 < b → (a / b ≤ 1 ↔ a ≤ b)
@Filter.Eventually.exists : ∀ {α : Type u_1} {p : α → Prop} {f : Filter α} [f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
@Filter.Eventually.and : ∀ {α : Type u_1} {p q : α → Prop} {f : Filter α}, Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
@Filter.Eventually.mono : ∀ {α : Type u_1} {p q : α → Prop} {f : Filter α}, (∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
Real.sqrt_nonneg : ∀ (x : ℝ), 0 ≤ √x
@mul_self_nonneg : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : LinearOrder R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a : R), 0 ≤ a * a 
Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
* Paper-delta candidates: none (`T2509a` unused): the band proofs at a new carrier; D-ledger note only: `Aof κ = (κ+1)/κ` is the constant of `TwistStep2_lam0_sq` (`λ² ≤ ((κ+1)/κ) g₀²`, equality at `T₀ = κ/(κ+1)`).
* Targets 7-9 are vacuous for `d < 3` (every pin starts `3 ≤ d →`, as the band); there is no statement at `STAny` (DECISIONS §331 (2)) and no `BAStep3R`/`BAStep4R` (§331 (4)).
* Binders left in the instances are other gates' pins: `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL` and `STLmaxUgL` (the Step 3 conclusion, read by Step 4). V2a's reading (Decision (3)) is `T2509_shape_V2aRead d`, compiled in `pins2.lean` from targets 8-9 (b4).
* The regime-(i) instances (8 (i), 9 (`STReg5I`)) depend on the private datum of `BA/ZeroModeBA` through `open private`; a change of that datum in a later ticket would break them; no merged file is edited here.
