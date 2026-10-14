Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 04:30:22 UTC 2026

Row a only (targets 1-9: `Step6Gen`, `Step6KitGen`). Targets are conversions of band Step 6 at the carrier; no new mathematics. Constants below are those of the band texts (`Induction/Step6Pins`, `Step6Kit`, `Defs/Sizes`) and the carrier pins (`Chain/Step34Gen`, `Chain/LWGen`); d = 3, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6.

### (i) Exponent table
| # | quantity | value | constraint it must satisfy | slack at the instance (script lines below) |
|---|---|---|---|---|
| 1 | target factor `G = (lam² W^d)^(-1/5)` (`STExpTarget`, `Step6Pins:65`) | exponent -1/5 | `G > 0` needs `lam n ≠ 0` (at `lam = 0` Mathlib gives `0^(-1/5) = 0`, target collapses to `B³`); `(eq:WO)` gives `lam² W^d ≥ W^(2𝔡)` (`lam_sq_mul_pow_ge`, `Defs/Sizes:193`), hence `G ≤ W^(-2𝔡/5)` | sz0 n=0: `lam²W³ = 8 ≥ W^(2𝔡) = 2`; `G = 0.6598 ≤ W^(-2𝔡/5) = 32^(-0.04) = 0.8706` |
| 2 | `𝔠d` (inside `STIngR6gL`, min of ingredient constants) | `0 < 𝔠d ≤ 1/100` | `STConStInd 𝔠d`: `B_t^𝔠d ≤ (1-t)/(1-s) < 1` eventually; monotone in `𝔠d` with no extra premise (`st5_conStInd_mono`, `Step5Kit:101`: `B < 1` follows from `STConStInd` itself), so the min of the ingredient constants works | sz0 regime III, n=0: `B^(1/100) = 0.9020 ≤ 0.9375`; smallest admissible `𝔠d` at n=0 is 0.006255 (slack factor 1.6 to 1/100); for every `𝔠d > 0` it holds eventually (limit, `conStInd_const`, `Step34Pins:825`) |
| 3 | ratio exponent in the initial term (regimes III, IV) | 2 (= `n_`) | `stek_sumNdecay` with `n_ = 2` gives `((1-v)/(1-t))^2 X`; `n_ ≥ 2` is the pin's hypothesis; matches `((1-s)/(1-u))² T_s` | `n_ = 2`, slack 0 (equality of exponents) |
| 4 | comparison `((1-s)/(1-u))² T_s ≤ 4 T_u`, hypothesis `(1-s) B_s ≤ 2 (1-u) B_u` (`st6_cmp_ini`, `st6_xB_III/IV`) | constant 4 = 2² | hypothesis from the window (III: `1-u ≥ lam²`; IV: `1-s ≤ lam²/L^d`) | III boundary `1-u = lam²`: `3.0987e-5 ≤ 3.1471e-5` (1.6 %), `1.0629e-2 ≤ 1.2034e-2`; IV: `8.64e-7 ≤ 2.34e-6` |
| 5 | monotonicity and cube `T_s ≤ T_u`, `B_u³ ≤ T_u` (`st6_target_mono`, `st6_cube_le_target`) | exponent 3 | only `G ≥ 0`, `B ≥ 0` (`B³ = B²·B ≤ B²(G+B)`) | all four instance lines: true, `B_u³ = 3.61e-14 ≤ T_u = 7.208e-10` (III, u=1/16); IV: `4.06e-9 ≤ 5.86e-7` |
| 6 | drift exponents `STExpEGtHiConcl`: 5/2; `STExpLKLKHiConcl`: 11/5 | 5/2, 11/5 | row a copies the 5/2 verbatim from `LWtermEXPG` (`LWGen:119`; band `LWPins:320`) in `STExpEGtHiConclgL` and in target 6; `5/2 > 11/5` and `B < 1` give `B^(5/2) ≤ B^(11/5) ≤ B²`. The closure `∫ (…)² (1-v)⁻¹ B^(11/5) dv ≲ T_u` is inside the ingredient pins (`STExpIntConcl`), not a row-a obligation | `B = 3.3e-5`: `6.3e-12 ≤ 1.4e-10 ≤ 1.1e-9` |
| 7 | R1: `0 ≤ gK·lam`, `gK² ≤ lam²`, `lam² ≤ A gK²`; `A` with `1 ≤ A` (`STEKNonzerogL` takes `1 ≤ Aof κ`) | BA: `A = (κ+1)/κ`; band `A = 1`, `gK = lam` | A-form window `(1-s)L² ≤ A gK²` follows from the band window `(1-s)L² ≤ lam²` (regime II) and `lam² ≤ A gK²`; `gK ≤ lam ≤ 𝔡⁻¹` for `gK > 0` | κ = 1/10: `A = 11 ≥ 1`; szB n=0, `gK = lam/2`: `1/4 ≤ 1 ≤ 11/4`, window `1 ≤ 1 ≤ 11/4`; the gK-level window without `A` is `1 ≤ 1/4`, false (A is needed) |
| 8 | `(eq:WO)`: `W^(-d/2+𝔡) ≤ lam ≤ 𝔡⁻¹`; Bandwidth `W ≥ N^𝔠`; `N = (WL)^d` | exponent `-1.4`, `𝔠 = 1/6` | `Admissible 𝔠 𝔡` (`Defs/Sizes:177`) | sz0 n=0: `7.8e-3 ≤ 1/64 ≤ 10`; `N^(1/6) = 11.31 ≤ W = 32` |
| 9 | regime windows I-IV, `STDriftHi` `lam²/L^d ≤ 1-t` | thresholds `lam²/L²`, `lam²/L^d`, `lam²` | `Step5Pins:44-64`; `STDriftHi` holds in I, II, III (`st6_hi_of_reg5*`) | script lines "regime": all n < 50; boundaries hit (I: `1-t = lam²/L² = 1/16`; II: `1-s = lam²/L² = 1/16`; IV: `1-s = 25/64 = lam²/L^d` only in the `s = 39/64` comparison line; the regime-IV window itself is `3/8 ≤ 25/64`) but windows have `s < t` |
| 10 | flow: `|E| ≤ 2-κ`, `N^(-1+ε) ≤ Im z ≤ 1`, `t ≤ lemT z`; bulk `Im m(E) ≥ √(2κ)/2`; family premise 3 `κm ≤ Im m` | κ = 1/10 | `locDomain`; `st6_mE_im_ge` | E = 1/2: `Im m = 0.9682 ≥ 0.2236` (so `κm = 0.2236` works); z0: `lemT ≥ 0.99999 ≥ 1/16`; zB: `lemT = 0.98399 ≥ 31/32` |
| 11 | `Bparam d L g t K` at `K = 0` has `((K+1)^(d-2))⁻¹ = 1` | `d - 2 = 1` | `3 ≤ d` | d = 3 |

### (ii) One concrete nondegenerate instance
Data: d = 3, κ = ε = 𝔡 = 1/10, 𝔠 = 1/6, E ≈ 1/2. sz0: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^(-6)` (n=0: L=4, W=32, N=2097152, lam=1/64), `z0 n = 1/2 + i N^(-4/5)`, regime III `(s,t) = (0,1/16)`. szB: `L=4, W_n=n+4, lam=1`, `zB = 1/2 + i/64`, regimes I `(7/8,15/16)`, II `(15/16,31/32)`. szG = szB with `lam = 5`, regime IV `(5/8,3/4)`. Time bounds `t ≤ lemT` are computed with `msc(z) = (-z + √(z²-4))/2` on the branch with `Im > 0`, `lemT = |msc|²`, `lemE = -2 Re msc / |msc|`. Exact rationals via `fractions`, floats for rpow. Same data as the merged band instances (`Step6Kit:1086-1288`; sizes `Defs/Sizes:260`, `Step34Pins:710`, `Step5Pins:497`).

Command: `python3 -I /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502/inst.py` (about 30 s). Output:
```
OK   sz0 n<50 (n=0: L=4,W=32,N=2097152,lam=1/64): WO W^(-d/2+dd)=7.813e-03<=lam<=1/dd, Bandwidth N^(1/6)=11.31<=W, lam^2W^d=8>=W^(2dd)=2, N increasing
OK   szB n<50 (n=0: L=4,W=4,N=4096,lam=1): WO W^(-d/2+dd)=1.436e-01<=lam<=1/dd, Bandwidth N^(1/6)=4.00<=W, lam^2W^d=64>=W^(2dd)=1.32, N increasing
OK   szG n<50 (n=0: L=4,W=4,N=4096,lam=5): WO W^(-d/2+dd)=1.436e-01<=lam<=1/dd, Bandwidth N^(1/6)=4.00<=W, lam^2W^d=1600>=W^(2dd)=1.32, N increasing
OK   z0 n=0: |Re z|=0.5<=2-kap, N^(-1+eps)=2.044e-06<=Im z=8.764e-06<=1, lemE=0.5000, lemT=0.999991>=1/16 (t=1/16)
OK   z0 n=1: |Re z|=0.5<=2-kap, N^(-1+eps)=2.715e-11<=Im z=4.054e-10<=1, lemE=0.5000, lemT=1.000000>=1/16 (t=1/16)
OK   z0 n=2: |Re z|=0.5<=2-kap, N^(-1+eps)=3.812e-14<=Im z=1.181e-12<=1, lemE=0.5000, lemT=1.000000>=1/16 (t=1/16)
OK   zB n=0: N^(-0.9)=5.609e-04<=1/64, lemE=0.5000, lemT=0.983992>=31/32
OK   regime I (szB,7/8,15/16): s<t, window, STDriftHi=True, n<50 (n=0: lam^2=1.000e+00, L^2=16, L^d=64, 1-s=0.12500, 1-t=0.06250)
OK   regime II (szB,15/16,31/32): s<t, window, STDriftHi=True, n<50 (n=0: lam^2=1.000e+00, L^2=16, L^d=64, 1-s=0.06250, 1-t=0.03125)
OK   regime III (sz0,0,1/16): s<t, window, STDriftHi=True, n<50 (n=0: lam^2=2.441e-04, L^2=16, L^d=64, 1-s=1.00000, 1-t=0.93750)
OK   regime IV (szG,5/8,3/4): s<t, window, STDriftHi=True, n<50 (n=0: lam^2=2.500e+01, L^2=16, L^d=64, 1-s=0.37500, 1-t=0.25000)
OK   III sz0 n=0 s=0 u=4095/4096 (1-u=lam^2): (1-s)B_s=3.0987e-05<=2(1-u)B_u=3.1471e-05; ratio^2 T_s=1.0629e-02<=4T_u=1.2034e-02; T_s=6.335e-10<=T_u=3.009e-03; B_u^3=2.68e-04<=T_u
OK   III sz0 n=0 s=0 u=1/16: (1-s)B_s=3.0987e-05<=2(1-u)B_u=6.1973e-05; ratio^2 T_s=7.2081e-10<=4T_u=2.8831e-09; T_s=6.335e-10<=T_u=7.208e-10; B_u^3=3.61e-14<=T_u
OK   IV szG n=0 s=39/64 u=3/4 (1-s=lam^2/L^3): (1-s)B_s=4.8453e-04<=2(1-u)B_u=7.9769e-04; ratio^2 T_s=8.6353e-07<=4T_u=2.3441e-06; T_s=3.537e-07<=T_u=5.860e-07; B_u^3=4.06e-09<=T_u
OK   IV szG n=0 s=5/8 u=3/4: (1-s)B_s=4.7505e-04<=2(1-u)B_u=7.9769e-04; ratio^2 T_s=8.3019e-07<=4T_u=2.3441e-06; T_s=3.690e-07<=T_u=5.860e-07; B_u^3=4.06e-09<=T_u
  III sz0 (0,1/16): r=0.9375; first n=0
  I szB (7/8,15/16): r=0.5000; numeric first n (cap 1e6)=None; analytic n >= ((Bparam=1.191)/r^100)^(1/3)-4 = 1.15e+10
  II szB (15/16,31/32): r=0.5000; numeric first n (cap 1e6)=None; analytic n >= ((Bparam=1.470)/r^100)^(1/3)-4 = 1.23e+10
  IV szG (5/8,3/4): r=0.6667; numeric first n (cap 1e6)=346246; analytic n >= ((Bparam=0.102)/r^100)^(1/3)-4 = 3.46e+05
OK   I szB s=7/8, 1-t=0.9/8: t=0.88750<=lemT(zB)=0.98399, window n<50: True, ConStInd(1/100) first n=30
OK   II szB s=15/16, 1-t=0.9/16: t=0.94375<=lemT(zB)=0.98399, window n<50: True, ConStInd(1/100) first n=32
OK   IV szG s=39/64, 1-t=0.9*25/64: t=0.64844<=lemT(zB)=0.98399, window n<50: True, ConStInd(1/100) first n=11
sz0 n=0 III: smallest cd with B^cd<=15/16 is 0.0062552956575850785
OK   monotone in cd (B<1): B^(1/50)=0.8135 <= B^(1/100)=0.9020
OK   A=(kap+1)/kap=11>=1
OK   R1 szB n=0: gK*lam=1/2>=0, gK^2=1/4<=lam^2=1<=A gK^2=11/4
OK   regime II window (1-s)L^2=1<=lam^2=1 (band) <= A gK^2=11/4 (A-form)
OK   without A the gK-level window (1-s)L^2=1<=gK^2=1/4 FAILS (so A is needed)
OK   gK=1/2<=1/dd=10
OK   step34Gen_ratio_le at n=0 szB: r(gK;v,t)<=A r(lam;v,t), v=15/16,t=31/32
OK   bulk: Im m(1/2)=0.9682 >= sqrt(2 kap)/2=0.2236
OK   exponents at sz0 n=0,u=1/16: B=3.305e-05<1 so B^(5/2)=6.281e-12<=B^(11/5)=1.388e-10<=B^2=1.092e-09; G=0.6598=(lam^2W^d)^(-1/5), W^(-2dd/5)=0.8706>=G
ALL OK
```
Finding on `STConStInd` (hypothesis of target 2): it is an eventual statement; the merged limit lemma `conStInd_const` (`Step34Pins:825`) discharges it for every `𝔠d > 0`. Numerically, at the band's regime I, II, IV data it first holds only at `n ≈ 1.2e10` (I), `1.2e10` (II), `3.5e5` (IV) with `𝔠d = 1/100` (rows "analytic" above), because the ratio `(1-t)/(1-s)` is 1/2 and 2/3. For the numeric instances use regime III (holds from n = 0) and the thin-window variants (ratio 0.9, the three rows "1-t=0.9/…" above: first n = 30, 32, 11). External hypotheses of the row-a texts (pins not yet proved: `STExpAvgAtgL`-family, `LWtermEXPG`, `STEKSumNdecaygL`, `STEKNonzerogL`): the limit statement of lesson 14 is the one above for `STConStInd`, and `B_n(t) = W_n^(-3) Bparam → 0` for the sequences with `W_n → ∞`.

### Verdicts (row a)
- Targets 1, 2, 4, 5, 6, 7, 8, 9: PASS. Every hypothesis set holds at the instance; the arithmetic closes with the slacks in (i).
- Target 3 (ingredient texts `T2502_ExpAvgAtgL` … `T2502_ExpDuhEqgL`, `T2502_EGtHiConclgL`): PASS as statements (exponents 2, 5/2 copied; the proofs belong to rows b, c).
- Overall: PASS. Not covered by this section by the stage rule: census/size, name-clash, `open private` lists.

## (b) Script output, row a (T2502, branch `t/T2502`) — Wed Oct 14 05:24:54 UTC 2026
Scratch scripts and raw outputs: `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2502/` (`greps.sh`, `c1.py`, `clash2.py`, `closure.py`, `extract2.py`, `inst_cov.py`, `chk_a.lean`, `axioms_all.lean`, `names.lean`).
**Build, size, commits**
```
$ git log --format=%h main..HEAD | tr "\n" " "; wc -l RBM3D/Chain/Step6Gen.lean RBM3D/Chain/Step6KitGen.lean
b0d28f34 b6bcabe8 490c4c84 a87b9efe 3d2aea81 016f17e0 c7f3228d ad715697 
902 RBM3D/Chain/Step6Gen.lean
1248 RBM3D/Chain/Step6KitGen.lean
2150 total
$ lake build RBM3D.Chain.Step6Gen RBM3D.Chain.Step6KitGen 2>&1 | tail -1
Build completed successfully (3860 jobs).
$ lake build 2>&1 | grep -E "Built RBM3D \(|axiom audit:|non-vacuity|Build completed"   (after the last edit)
ℹ [4383/4384] Built RBM3D (71s)
info: RBM3D.lean:614:0: axiom audit: 15118 theorems, 4687 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
non-vacuity certificates: 0 of 124 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4384 jobs).
$ lake build 2>&1 | grep -E "Built |Building "   (first full build after the registry edit; no other module is `Built`/`Building`, 205 lines `Replayed`)
Built RBM3D.Test.Axioms;Built RBM3D.Test.AuditNegative;Built RBM3D;
$ lake env lean docs/tickets/checks/T2502-check.lean >/dev/null 2>&1; echo "exit $?"
exit 0
```
**Axioms** of the new public declarations (`axioms_all.lean`: one `#print axioms RBM.BA.<name>` per public declaration of the two files)
```
declarations printed: 122; axiom sets: {'propext, Classical.choice, Quot.sound': 122}; "error" lines: 0; "sorryAx": 0
'RBM.BA.ST_step6_caseI_of_pinsgL' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.st6_caseI_coreg' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.st6_EGtHi_of_LWg' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**Target statements**, extracted by script (`extract2.py`: header, plus the body of a `def`; cut at 170 characters; the other defs of targets 1-3 are listed in the files)
```
Step6Gen.lean:40 STExpErrg (n : ℕ) (u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ := (∫ ω, C.L n u σ a ω ∂μ) - C.K n u σ a
Step6Gen.lean:72 STExp2UgL (s t : ℕ → ℝ) : Prop := PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (fun n p _ => ‖(∫ ω, C.L n (p.1 : ℝ) p.2.1 p.2.2 ω ∂…
Step6Gen.lean:100 STIngR6gL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law …) (Flow …) (mk …) (T0 …) (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Pr…
Step6Gen.lean:115 STStep6RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law …) (Flow …) (mk …) (T0 …) : Prop := STIngR6gL d R law Flow mk T0 (fun sz z s t => STStep6Concl…
Step6Gen.lean:85 theorem STExp2gL_of_STExp2UgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STExp2UgL C μ s t) : STExp2gL C μ t
Step6Gen.lean:153 STExpAvgAtgL (u : ℕ → ℝ) : Prop := PrecL sz μ (U := fun n => Bool × Zd d (sz.L n)) (fun n p _ => ‖(∫ ω, C.L n (u n) (fun _ : Fin 1 => p.1) (fun _ => p.2) ω ∂μ) - (if p.1 …
Step6Gen.lean:316 STImproveExpAvergL : Prop := 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u …
Step6Gen.lean:179 STExpDuhamelZAtgL (n : ℕ) : Prop := ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 → ∀ (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)), zeroModeSet d (sz.L n) A (fu…
Step6Gen.lean:323 STExpDuhamelZgL : Prop := ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, STExpDuhamelZAtgL (mk sz z) (law sz) n
Step6Gen.lean:201 STExpDuhEqgL (s t : ℕ → ℝ) : Prop := ∀ᶠ n in atTop, ∀ (u : TimeIcc s t n) (σ : Fin 2 → Bool) (A : Finset (Fin 2)) (a : Fin 2 → Zd d (sz.L n)), zeroModeSet d (sz.L n) A (f…
Step6Gen.lean:532 theorem STIngR6_iff_gL : STIngR6 d R Concl ↔ STIngR6gL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ …
Step6Gen.lean:540 theorem STStep6R_iff_gL : STStep6R d R ↔ STStep6RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n…
Step6KitGen.lean:76 theorem st6_precU_of_forall_seqg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {W : ℕ → Type*} (F G : ∀ n, ℝ → W n → ℝ) (h : ∀…
Step6KitGen.lean:139 theorem LWAvgLawgL_of_STAvgUgL_at {s t u : ℕ → ℝ} (hsu : ∀ n, s n ≤ u n) (hut : ∀ n, u n ≤ t n) (hK1 : ∀ (n : ℕ) (τ : ℝ) (a : Zd d (sz.L n)), 0 ≤ τ → τ < 1 → C.K n τ (fun…
Step6KitGen.lean:284 theorem st6_EGtHi_of_LWg (s t : ℕ → ℝ) : IsProbabilityMeasure μ → sz.SizeTendsto → (∀ n, s n ≤ t n) → STDriftHi sz s t → Step2EventsGen_Rot3 C → (∀ u : ℕ → ℝ, (∀ n, s n ≤…
Step6KitGen.lean:338 theorem st6_expAvgU_of_ping (hAvg : STImproveExpAvergL d law Flow mk T0) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {sz : Sizes d} {z : ℕ → ℂ} (hfl…
Step6KitGen.lean:365 theorem st6_ini_sumNdecayg (hSum : STEKSumNdecaygL d law Ker) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm) {sz : Sizes d} (hadm : sz.Admissible 𝔠 𝔡) (C : FlowFM sz) (gK : ℕ →…
Step6KitGen.lean:401 theorem st6_ini_nonzerog {Aof : ℝ → ℝ} (hNZ : STEKNonzerogL d law Ker Aof) (hd : 3 ≤ d) {κm 𝔠 𝔡 : ℝ} (hκm : 0 < κm) (hAof : 1 ≤ Aof κm) {sz : Sizes d} (hadm : sz.Admissib…
Step6KitGen.lean:505 theorem st6_caseIII_coreg {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hR : STReg5III sz s t) (hlk…
Step6KitGen.lean:676 theorem ST_step6_caseIII_of_pinsgL {Ker : STEKKer d} (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz, IsProbabilityMeasure (law sz)) (hFF : Step5CasesGen_FlowFacts …
```
**Statement diff against the ticket pins** (uncommitted scratch `chk_a.lean` = the check's binding texts of Part 2, `T2502_ExpDuhamelQgL`, and 15 examples, each `rfl` or an application; the grep lists the 14 that start `example :`)
```
$ lake env lean chk_a.lean >/dev/null 2>&1; echo "exit $?"; grep -oE "^example : [A-Za-z0-9_]+" chk_a.lean | cut -c11- | tr "\n" " "
exit 0
STExp2UgL STStep2CoregL STIngR6gL STStep6RgL STExpAvgAtgL STImproveExpAvergL STExpHierAtgL STExpDuhamelZAtgL STExpDuhamelQAtgL STExpDuhamelZgL STExpDuhamelQgL STExpDuhEqgL STExpEGtHiConclgL T2502_EGtHiOfLW 
```
**Instances** (target 9; every endpoint theorem is applied at concrete data in the same file)
```
$ python3 -I inst_cov.py   (examples; theorems named inside an example body)
Step6Gen.lean examples: 37 theorems: 47 theorems named in an example: 44 not named: ['Step6Gen_ingR6_iff_congr', 'Step6Gen_ingR6_of_gL', 'STExpLKLKHi_iff_gL']
Step6KitGen.lean examples: 26 theorems: 30 theorems named in an example: 30 not named: []
```
Data: `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`, `E = 1/2`, `(s,t) = (0, 1/16)`), `szB` (`(7/8, 15/16)`, `(15/16, 31/32)`), `szG` (`(5/8, 3/4)`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, at `bandFM`, law `seqP`. Cores: `Step6KitGen` calls `st6_case*_coreg` at lines 1095 1110 1135 1156 ; wrappers: `inst_step6*` at lines 1171 1186 1204 1229 . Discharged: flow, windows, regime, law, admissibility, flow facts (`step5CasesGen_flowFacts_band`), F7 (`Step2EventsGen_bandRot3`), `hK1` (`ST_Kloop_one`), the proved kernel pins `stek_sumNdecaygL_band`, `stek_nonzerogL_band` with `STEKBandKer` at `κm = √(2κ)/2`. Left as hypotheses (pins of other gates): `LWtermEXPG` and its per-`u` bound, the ingredient pins, the Duhamel families (rows b, c; V1s2'/V1s3'), `STExp2gL` at `s`, the Step 2-5 conclusions. `Step6Gen_ingR6_*` are used inside the pin bridges; `STExpLKLKHi_iff_gL` is applied in `Step6KitGen`.
**Name clash, hygiene, layering, closure, hypothesis rules**
```
$ python3 -I clash2.py   (declared names of the two files against `main`, `t/T2498`, the working tree)
new public names: 122
ref main declarations scanned: 30794 clash hits: []
ref t/T2498 declarations scanned: 30699 clash hits: []
working tree (other files) declarations scanned: 30794 clash hits: []
$ greps.sh   STGridRepNgL | withLam | sorry|admit|axiom|native_decide hits in (Step6Gen, Step6KitGen): 0 0 | 0 0 | 0 0
imports: Induction.Step6Pins, Chain.Step5Gen, Chain.LWGen, Chain.Step34Gen, Chain.Step6Gen, Induction.Step6Kit, Chain.Step2EventsGen, Chain.Step5CasesGen
importers: RBM3D/Chain/Step6KitGen.lean, RBM3D.lean; column-0 def/abbrev/structure in Step6KitGen: 0; `open private`: Step5CasesGen_prec_mono Step5CasesGen_prec_cover from RBM3D.Chain.Step5CasesGen
$ python3 -I closure.py . RBM3D.Chain.Step6Gen RBM3D.Chain.Step6KitGen
closure size 158; QProxy/QDrift/QLevels/QBudget/QEnd/QtNonzero/QtXiRoundLift/Probe/RBM3D.BA./BA.LWPinsBA/Chain.Step2Kern: 0 each; Induction.Step3 and Induction.Step4 (exact names): not in the closure
$ python3 -I c1.py   (C1 / X1-C1 token grep of the ticket, comments stripped; hits by region)
Step6Gen.lean: public statements 0; bridges 103; instances 100
Step6KitGen.lean: public statements 0; instances 177
```
The C1 hits are bridges (`bandFM_*`, `*_iff_gL`, `*_of_gL`, `*_to_gL`, private `Step6Gen_STthetaOp_eq`) and instances. U5S-C3 (`grep -nE "∀ \(sz : Sizes d\)"`): the premise hits are `hK1` and `hKer` of the wrappers; the others are tuple binders of defs and bridge helpers. `gK` occurs only in `st6_ini_sumNdecayg`, `st6_ini_nonzerog`, the four wrappers and private band helpers of the instances; `sz.withLam`: 0.
**Registry and scan** (`RBM3D/Test/Axioms.lean`; scan before = `lake env lean RBM3D.lean` at the base commit, after = `lake build`)
```
$ git diff --numstat main...HEAD -- RBM3D.lean RBM3D/Test/Axioms.lean
2	0	RBM3D.lean
32	1	RBM3D/Test/Axioms.lean
registered (29 new names): owed 13 (STExp2UgL, STImproveExpAvergL, STExpLKLKHigL, STExpDriftLogL, STExpDriftDecaygL, STExpWardIgL, STExpWardIIgL, STExpIniIgL, STExpIntIgL, STExpIntIIgL, STExpIntIIIgL, STExpIntIVgL, LWtermEXPG); structural 15 (STIngR6gL, STStep6RgL, STStep6ConclgL, STStep2CoregL, 9 `*ConclgL`, STSigAll, STSigSame; STStep6RgL and STStep6ConclgL are concluded by theorems, the other 13 were flagged by the scan); superseded 1 (STStep6gL); the owner text of `STExp2U` is extended (that is the 30th added line)
before: axiom audit: 15041 theorems, 4642 definitions, 0 axioms; non-vacuity certificates: 0 of 111 premises
after:  axiom audit: 15118 theorems, 4687 definitions, 0 axioms; non-vacuity certificates: 0 of 124 premises
premise rows before/after: 111 / 124  removed: []
new rows (premise: theorems resting on it): BA.LWtermEXPG:5, BA.STExp2UgL:3, BA.STExpDriftDecaygL:2, BA.STExpDriftLogL:2, BA.STExpIniIgL:2, BA.STExpIntIIIgL:2, BA.STExpIntIIgL:2, BA.STExpIntIVgL:2, BA.STExpIntIgL:2, BA.STExpLKLKHigL:4, BA.STExpWardIIgL:2, BA.STExpWardIgL:2, BA.STImproveExpAvergL:5
changed counts (before->after): BA.STAvgUgL 6->7, BA.STDecaygL 9->10, BA.STGdecayWgL 20->22, BA.STLKUgL 5->7, BA.STLKgL 21->22, BA.STLmaxUgL 5->6, BA.STLmaxgL 12->13, BA.STLocalEntryUgL 5->7, BA.STLocalEntrygL 5->7, Sizes.STExp2U 3->4
$ git diff --name-only main...HEAD; git diff --stat main...HEAD -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Gauss RBM3D/Evolution (+ other Chain files)
RBM3D.lean RBM3D/Chain/Step6Gen.lean RBM3D/Chain/Step6KitGen.lean RBM3D/Test/Axioms.lean 
(band dirs and other `Chain/*` files: empty)
```
**Family premises as used** (ticket table, U5S-C3; the guard is the one of the premise; rows 9-14 are not used in row a)
| # | wrapper argument | band discharge (compiled in the instances) / BA owner | targets |
|---|---|---|---|
| 1 | `hμ : ∀ sz, IsProbabilityMeasure (law sz)` | instance `isProbabilityMeasure_seqP` / same | 5-8 |
| 2+3 | `hFF : Step5CasesGen_FlowFacts` (admissible sizes, `T0 < 1`; the draft rows 2 and 3 merged) | `step5CasesGen_flowFacts_band` / `baStep5CasesGen_flowFacts` | 7, 8 |
| 4 | `hRot : ∀ sz z, Step2EventsGen_Rot3 (mk sz z)` (I-III) | `Step2EventsGen_bandRot3` / `Step2EventsGenTw_baRot3` | 6, 8 |
| 15 (new) | `hK1 : ∀ sz z n τ a, 0 ≤ τ → τ < 1 → (mk sz z).K n τ ![+] ![a] = (mk sz z).m n` | `ST_Kloop_one` / candidate `baKsol_one` (`BA/KInduct:77`: `BAReal`, `t ∈ [0,1)`), not checked at `baFM` here | 5, 6, 8 |
| 5, 6 | `hSum`, `hNZ`, `hAof : ∀ κm > 0, 1 ≤ Aof κm`, `gK`, and `hKer : ∀ κ > 0, ∃ κm > 0, ∀ sz ε 𝔠 𝔡 z, Flow … → κm ≤ Im m ∧ Ker sz (mk sz z) (gK sz z) κm ∧ (∀ᶠ n, 0 < gK n ≤ 𝔡⁻¹) [∧ R1 at Aof κm, regime (ii)]` (`κm` before `(sz, z)`) | `stek_sumNdecaygL_band`, `stek_nonzerogL_band`, `STEKBandKer`, `Aof = 1` / U3-BA `STEKKer`, R1 conjunct of `baIniTermGen_kerFacts` (`A = (κ+1)/κ`, `κm = κ`) | 7, 8 |
| 7 | `hLW : LWtermEXPG` (I-III) | `band_LWtermEXPG` / not produced (V1-BA uses the cores with `BALWtermEXPTw`) | 6, 8 |
| 8 | the ingredient pins `STExp*gL`, `STImproveExpAvergL`, `STExpDuhamelZgL`, `STExpDuhamelQgL` | generic: V1s2'/V1s3', rows b, c / V1-BA | 8 |
**UBA-C1 as used.** Targets 1-4 and the cores read the size level `sz.lam` only (`Bctl`, `STExpTarget`, `STDriftHi`, `STReg5*`, the mollifier at `sz.lam n`) and the one kernel `Step2Gen_UN C`; `st6_ini_sumNdecayg` takes `STEKSumNdecaygL` (no ratio, no R1); R1 (`hcmp`) is read only by `st6_ini_nonzerog`, turning the band window `(1-s)L² ≤ lam²` into `(1-s)L² ≤ Aof κm · gK²`; `sz.withLam`: 0.

**Narrative** (facts above; ports are from this project's band files at `6b359e50`, `RBM1D`/`RBM2D` were not read, so the RBM1D diff-stat is n/a)
1. Delivered, row a only: `Chain/Step6Gen.lean` (targets 1-4: vocabulary, texts, pins, bridges, instances) and `Chain/Step6KitGen.lean` (5-9), 2 import lines in `RBM3D.lean`, 29 new registry names and the extended owner text of `STExp2U`. No band or merged file is in the diff.
2. Ports: `Step6Kit` `st6_prec_det_iff` `:81`, `st6_precU_of_forall_seq` `:115`, the `_at` bridges `:170-210`, `st6_prec_pi_norm` `:225`, `st6_prec_of_forall_fin` `:241`, `st6_EGt_eq_LWE` `:327`, `st6_EGtHi_of_LW` `:571`, `st6_ini_sumNdecay` `:600`, `st6_ini_nonzero` `:651`, `st6_cover_exp2U` `:696`, the four skeletons `:737-1028`, `st6_duhEq_of_pin` `:361`, `st6_duhEqQ_of_pin` `:833`, `st6_expAvgU_of_pin` `:557`, `st6_mollifier_family` `:845`, `st6_GdecayW_of_zero` `:1046`, `ST_step6R_mono` `:1078`; `Step6Pins` `:45-471`. Substitutions: `Prec sz` to `PrecL sz μ`, `STExpErr E` to `STExpErrg C μ`, `Ugen`/`STthetaOp` to `Step2Gen_UN`/`Step2Gen_ThetaN`, `stek_*_holds` to the pins `STEKSumNdecaygL`/`STEKNonzerogL`, `STFlow`-facts to `Step5CasesGen_FlowFacts`.
3. Size: 902 + 1,248 = 2,150 against 535 + 1,000 = 1,535 (×1.40) and the stop line 2,150; the commit `016f17e0` was at 2,202 before compaction (b, first block).
4. Each core takes the conclusions of the pins (`hlk hegt hdec hward hini hduh hint`) as hypotheses and `STExpEGtHiConclgL` explicitly, as the ticket says; each wrapper derives them from the family pins and the premises of the table above.
5. Deviations from the draft table: draft rows 2 and 3 merge into `hFF`; rows 5 and 6 merge into `hKer` with `κm` before `(sz, z)` (so the class, the window of `gK` and R1 are stated at one bulk datum; the band instance is compiled with `κm = √(2κ)/2`; the BA choice is open, (d) 3); new premises `hK1` (row 15) and `hAof`.
6. Eventual twins (ticket (5)): the band pins `STExpDuhamelZ`/`Q` give the generic eventual families (`STExpDuhamelZ_to_gL`, `STExpDuhamelQ_to_gL`, `d = 3`); the integrated pins `STExpIntI..IVgL` read the eventual `STExpDuhEqgL`, so they imply the band pins (`STExpInt*_of_gL`) and not conversely.
7. The check file `docs/tickets/checks/T2502-check.lean` compiles on this branch; the 13 binding texts are matched in the scratch file (12 by `rfl`, `T2502_EGtHiOfLW` by applying `st6_EGtHi_of_LWg`). The full `lake build` passes with the registry edits; no band, merged `Chain/*` or certificate module is rebuilt (only `Test.Axioms`, `Test.AuditNegative`, `RBM3D` besides the two new modules). T2503 interface: `STIngR6gL`, `STStep6RgL` equal `T2502_IngR6gL`, `T2502_Step6RgL` by `rfl`, so no amend is needed.
8. W1 and W2 (rows c, b): not touched. `STExpHierAtgL`, `STExpDuhamelZ/QAtgL`, `STImproveExpAvergL` are texts here; their proofs are rows b, c.

## (c) Verified Mathlib names (compiled; `#check` of all 21 in `names.lean`, 0 errors; none searched and found absent)
`Real.rpow_nonneg`, `Real.one_le_rpow`, `Real.rpow_neg_one`, `Real.rpow_one_add'`, `inv_lt_one_of_one_lt₀`, `ENNReal.ofReal_lt_ofReal_iff`, `ENNReal.ofReal_mul`, `ENNReal.ofReal_natCast`, `ENNReal.ofReal_le_ofReal`, `MeasureTheory.measure_univ`, `MeasureTheory.measure_iUnion_fintype_le`, `pi_norm_le_iff_of_nonneg`, `norm_le_pi_norm`, `Finset.sum_add_distrib`, `Filter.eventually_all`, `Filter.not_eventually`, `Filter.Eventually.of_forall`, `Fintype.ofFinite`, `mul_self_nonneg`, `le_div_iff₀`, `norm_add_le` (all as ported from the band proofs).

## (d) Open issues and paper-delta candidates
1. Size: the row ends exactly at its stop line (2,150) after compaction; the true cost to quote for V1s2' is about 2,150-2,200 against 1,535 bottom-up (×1.40-1.43).
2. `hK1` (row 15) is a new family premise. The BA discharge `baKsol_one` is a candidate only: `baFM.K` is `BAKloop` (`BA/FlowPins:298`), i.e. `BAKsol` at `PropSpin (BAmF …)`, and `baKsol_one` (`BA/KInduct:77`) needs `BAReal`, `3 ≤ L` and `t ∈ [0,1)`; V1-BA confirms. The premise is stated at `0 ≤ τ < 1` for that reason.
3. `hKer`/`hAof`: at BA, U3-BA must supply `STEKKer` at `κm` and R1 at `Aof κm`; the ticket (row 6) names R1 of `baIniTermGen_kerFacts` with `A = (κ+1)/κ` and `Aof κ = (κ+1)/κ` for U3-BA, so `κm = κ` would be the BA choice; I did not open `Step5KerBA:161`, V1-BA confirms.
4. The wrappers read the unprimed generic pins `STExpIniIgL`, `STExpIntIgL` (the band unprimed ones are in `supersededProps`); the primed texts are V1s2'/V1s3'. The registry owner text says so; the dispatcher decides whether the generic unprimed pins should be superseded as well.
5. `STStep6gL` is registered as superseded (as the band `STStep6`), not owed; the dispatcher may reclassify.
6. Public one-direction bridges not named by the ticket (`STExpDuhamelZ_to_gL`, `STExpDuhamelQ_to_gL`, `bandFM_STExpDuhEq_to_gL`, `STExpInt*_of_gL`) follow the ticket's "one direction" rule for the eventual twins; flagged for the auditor.
7. `open private` of two private lemmas of the merged `Chain/Step5CasesGen` (`Step5CasesGen_prec_mono`, `_prec_cover`); `Step6Gen` copies `expDuh_STthetaOp_eq_ThetaN` privately (`Step6Gen_STthetaOp_eq`) to keep the ticket's layering. `st6_mollifier_familyg` is the band `st6_mollifier_family` (size level), restated as the ticket lists it.
8. Paper-delta candidates: none required (`6:12-21` covers `H₀ ≠ 0`). Optional `T2502a`: the eventual (`∀ᶠ n`) form of `STExpDuhEqgL`, `STExpDuhamelZ/QgL` against the band `∀ n` (already DECISIONS §314 (5)).
