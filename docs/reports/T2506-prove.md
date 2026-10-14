Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 09:54:31 UTC 2026

Row a only (targets 1–5, `Chain/ExpEtermsAGen` → `ExpEtermsBGen`). Notation: `N=(WL)^d`, `B=Bctl n u=W^{-d}B_{u,0}`, `R_u=(1-u)^{-1}(N(1-u))^{-3}`. Sources: band `Induction/ExpEtermsA` / `ExpEtermsB` (file:line below), paper `6:61` (eq:Exp(L-K)1), `6:65` (eq:Exp(L-K)2), `6:77` (eq:ExpLWn=2_smalleta), `3_5:1634` (deccA0).

### (i) Exponent table
| # | quantity | value | constraint it must satisfy | slack |
|---|---|---|---|---|
| 1 | exponent of `B` in T1/T2 | 11/5 = 2 + 1/5 | `STLKUgL` `k=2` gives `B²`, `STGdecayWgL … 0` gives `B^{1/5}`; `B²·B^{1/5}=B^{11/5}` (`expLK_det_core`, ExpEtermsA:294-370) | 0 (identity) |
| 2 | zero-mode term | `B²·N·W^{-D} ≤ B^{11/5}` | `W^{-D} ≤ N^{-2}` then `N^{-1} ≤ B^{1/5}` (`B ≥ N^{-1}`, `N^{-1} ≤ 1`) | factor `N^{4/5}` |
| 3 | `D` in `STGdecayWgL` | `2/𝔠 = 12` (𝔠 = 1/6) | `W^{-D} ≤ N^{-2}` from `W ≥ N^𝔠` (ExpEtermsA:`hWD`) | 0 exactly (n=0: `W^6 = N = 4096`) |
| 4 | loss split | `τ' = τ/3`, 3 factors | `N^{τ'}·N^{τ'}·(C∞(3)+1) ≤ N^τ` iff `C∞(3)+1 ≤ N^{τ/3}`; `C∞(3)=KDecay_tailC 3 = 403108609` (script) | threshold `N ≥ (4.03·10^8)^{3/τ}` (τ=1/10: 10^{258}); proof-side only, conclusion is `∀ᶠ n` for every τ>0 |
| 5 | lattice-sum constant | `C∞(d)/(1-u)`, `d=3` | `KDecay_sum_tailT_le` needs `2 ≤ d`, `g ≥ 0`, `u<1` (`[NeZero L]`; no `ε`) | n/a |
| 6 | envelope exponent `Kenv` (W-a) | 6 | `N·(η⁻²W^{-d}+‖K^{(2)}‖)² ≤ N⁶`. Generic bounds (derived here): `‖C.L^{(2)}‖ ≤ η⁻²(W^d)⁻¹` (`CltRepg` + `RBM.Ind.norm_gloop_le_of_le_abs_im`, Split:757, `Im ztOf = (1-u)Im m`); `‖C.K^{(2)}‖ ≤ N·B ≤ 2N·(1-u)⁻¹` (row 17 `stKbound_timeIccgL` KDecayGen:92 at τ=1, `B ≤ 2(1-u)⁻¹` ExpEtermsB:109). With `η⁻¹ ≤ N`, `(1-u)⁻¹ ≤ N`: `M ≤ N²+2N² = 3N²`, envelope `≤ 9N⁵ ≤ N⁶` (band: `4N⁵`, uses the band-only `‖K^{(2)}‖ ≤ (1-u)⁻¹`) | `N ≥ 9` (n=0: `N/9 = 455`) |
| 7 | `η⁻¹ ≤ N`, `(1-u)⁻¹ ≤ N` (row 9′) | `κ' = cltCk(min(κ/2,2)) = 0.2222`, `δ = ε/2 = 0.05` | `η = (1-u)Im m ≥ κ'N^{-1+δ}` (since `1-u ≥ 1-T0 ≥ N^{-1+δ}`, `κ' ≤ Im m`), so `η⁻¹ ≤ N^{1-δ}/κ' ≤ N` iff `N^δ ≥ 1/κ'`; `(1-u)⁻¹ ≤ N^{1-δ} ≤ N` | `N ≥ 1.16·10^{13}` (proof-side; actual `η⁻¹ = 33` at `u=31/32`, n=0) |
| 8 | tail probability exponent, T1 | `|Kenv|+3 = 9` | `N^{Kenv-9} = N^{-3} ≤ N^{-11/5}` (floor `R ≥ N^{-11/5}`, ExpEtermsA `hfloor`) | exponent 4/5 |
| 9 | regime (iv) exponent | 3 in `R_u`; `N B⁴ ≤ 16 R_u` | `B ≤ 2(N(1-u))⁻¹` iff `L^d(1-u) ≤ λ²` (`STReg5IV`, ExpEtermsB:81); `2⁴ = 16`; 3 terms ⇒ `48 ≤ N^{τ/2}` | threshold `N ≥ 48^{2/τ}` (τ=1/10: 10^{33.6}); window slack in instance `1-s = 1/16` vs `λ²/L³ = 0.0977` |
| 10 | floor / tail, T3–T4 | `Kf = 3`: `N^{-3} ≤ N B⁴` (`B ≥ N⁻¹`); tail exponent `|Kenv|+|Kf|+1 = 10`, `6-10 = -4 ≤ -3` | `expDr_expect`, ExpEtermsB:553 | floor 0 (equality at `B=N⁻¹`); tail 1 |
| 11 | E-term decay level, T5 | `W^{-(D+1)}`, prob `N^{-(D+7)}` | `Kenv + (D+1) = D+7`: first moment `N⁶·N^{-(D+7)} = N^{-(D+1)} ≤ W^{-(D+1)}` (`W ≤ N`, ExpEtermsB:916); `4W^{-(D+1)} ≤ W^{-D}` iff `W ≥ 4` (from `N^𝔠 ≥ 4`) | 0 (both); instance `W = 4` at n=0 |
| 12 | `𝔠d` (inside each pin) | `1/100` | pin shape `0 < 𝔠d ≤ 1/100` (`STIngR6gL`, Step6Gen:100); unused by the proofs (`STConStInd` premise unused, band `stExpLKLKHi_holds`) | 0 (value at the cap) |
| 13 | kernel row/column sums (row 20) | `Σ_y‖C.S n x y‖ ≤ 1`, `Σ_x‖C.S n x y‖ ≤ 1` | `expLK_window_le` needs the column sum; band `=1` (`sum_norm_SB_row` Defs/Block:118, `SB_transpose` :58) | 0 |
| 14 | windows | T2: `STDriftHi`: `λ²/L^d ≤ 1-t`; T4: `STReg5IV`: `1-s ≤ λ²/L^d`; T5: `STReg5I` (declared by the pin shape, **not used** by the proof, ExpEtermsB:967 docstring) | instance below | see (ii) |

Row-17/20/9′/18 premises are guarded family rows (ticket table); `R1` is never used in row a (UBA-C1). No `sz.withLam` outside row 9′'s `CltRepg`.

**W-a decided:** envelope from row 9′ (`CltRepg`, `H₀` Hermitian, `κ' ≤ Im m`, `N^{-1+δ} ≤ 1-T0`) and row 17; exponent 6 kept, constant 9 not 4 (row 6). Pattern `ExpHierGen_Good_loopL` ExpHierGen:101 (private, `open private`).
**W-d decided (no gate):** the merged text `stEtermDecaygL` (SEforLnGen2:865, `k ≥ 2`, four conjuncts) is at `Step2Mat` labels `STegtg`/`STelklkg`; the FlowFM labels `STEGtg` (Step2Gen:455) and `STELKLKg` (Step5Gen:74) are linked to them by merged term-level bridges `Step2EventsGen_STEGtMg_eq` (Step2EventsGen:409), `STEGtMg_eq_STegtMg` (Step2CloseGen:125), `STELKLKMg_eq_STelklkMg` (:102), under `Step2IterGen_ListLink` + `Step34Gen_LCompat` (both in the merged class `SEforLnGen_Facts`, SEforLnGen:57: `LCompat ∧ KCompat ∧ Σ‖S‖ ≤ 1 ∧ …`); `LM = LIM(KLloopOf) = C.L` gives the `hLM` of the bridge. So row 18's E-term premise may be stated at the FlowFM labels (k=2, `STEKDecaygL μ s t` of `STEGtg C`, `STELKLKg C`), discharged at BA by `baEtermDecaygL` (SEforLnBA:271) + these bridges. No new mathematics.

### (ii) One concrete nondegenerate instance
Data: `d=3`, `L_n=4`, `W_n=n+4`, `λ_n=5/2` (all n), `z_n=1/2+i/64`, `κ=ε=𝔡=1/10`, `𝔠=1/6`, `n=0`: `N=4096`; band carrier `bandFM sz (STflowE z)`, law `seqP`, `T0=lemT z`, `E=lemE z`. Windows (n-independent): **W1** `(s,t)=(1/2, 9/16)` for T1, T2, T5; **W2** `(s,t)=(15/16, 31/32)` for T3, T4. (Band data `szG`/`szB` of the band instances give regime (iv)/(i) separately; one `λ` serving all three regimes is the above.) Stay hypotheses of the compiled examples (stochastic premises of the pins, as in the band instances): `STLKUgL`, `STGdecayWgL … 0`, `STExpAvgUgL`, the E-term decay premise; discharged deterministically: `Flow`, window predicates, `0≤s<t≤T0<1`, row 9′ range, row 20. No `False` premise, no empty index (`Zd 3 4` has 64 points, W1/W2 nonempty), no collapsed window.
```
python3 scratchpad/T2506/inst_a.py
lemT=0.983992 lemE=0.499984 ImmE=0.968248  |E|<=2-kappa:True
Lemma 2.8 quant: (1-T0) Im mE = sqrt(T0) Im z : True  Re:  True
n=0 N=4096 locDomain:True Bandwidth(1/6): N<=W^6 True (4096<=4096) WO:True
n=1 N=8000 locDomain:True Bandwidth(1/6): N<=W^6 True (8000<=15625) WO:True
n=2 N=13824 locDomain:True Bandwidth(1/6): N<=W^6 True (13824<=46656) WO:True
n=3 N=21952 locDomain:True Bandwidth(1/6): N<=W^6 True (21952<=117649) WO:True
T1,T2,T5 (s,t)=(1/2,9/16) 0<=s<t: True  t<=T0: True t<1: True {'DriftHi': True, 'Reg5IV': False, 'Reg5I': True}
T3,T4   (s,t)=(15/16,31/32) 0<=s<t: True  t<=T0: True t<1: True {'DriftHi': False, 'Reg5IV': True, 'Reg5I': False}
lam^2/L^3=0.09766  lam^2/L^2=0.39062
kappa'=0.22220 <= Im mE=0.96825 : True ; delta=0.050
 n=0 N^(-1+delta)=3.700e-04 <= 1-T0=0.0160 : True
 n=1 N^(-1+delta)=1.959e-04 <= 1-T0=0.0160 : True
 n=10 N^(-1+delta)=1.042e-05 <= 1-T0=0.0160 : True
u=0.93750 B=6.38150e-03 <= 2/(N(1-u))=7.81250e-03 : True
u=0.96875 B=1.03001e-02 <= 2/(N(1-u))=1.56250e-02 : True
u=0.5625 eta^-1=2.36 (<=N:True) band env=2.530e+05 generic env(M=eta^-2+2N^2)=4.612e+18  9N^5=1.038e+19  N^6=4.722e+21 ok=True
u=0.9688 eta^-1=33.05 (<=N:True) band env=5.177e+09 generic env(M=eta^-2+2N^2)=4.612e+18  9N^5=1.038e+19  N^6=4.722e+21 ok=True
D=12 W^-D=5.960e-08 <= N^-2=5.960e-08: True ; B^2*N*W^-D=2.045e-09 <= B^(11/5)=2.603e-06 : True
KDecay_tailC 3 = 403108609  (+1 = 403108610 )  log10 N-threshold (C+1)^(3/tau), tau=1/10: 258.1626622305421
threshold N^delta>=1/kappa' : N>=1.161e+13 ; 48 <= N^(tau/2): N>=48^(2/tau), tau=1/10: 10^33.6
2+1/5 = 11/5 | T1 tail exp Kenv-(|Kenv|+3)=-3 vs floor -11/5: slack 4/5
T4 tail exp Kenv-(|Kenv|+|Kf|+1)=-4 vs floor -Kf=-3: slack 1
N at n=0: 4096 ; N^6/(9N^5)=N/9=455.1 ; 4N^5<=N^6 iff N>=4 ; 9N^5<=N^6 iff N>=9
```
**Reading of the output.** `STFlow`/`Admissible`: `locDomain` (`|Re z|=1/2 ≤ 2-κ`, `N^{-1+ε} ≤ Im z = 1/64 ≤ 1`), `Bandwidth` (`N ≤ W^6`, exact integers, equality at n=0), `WO` (`W^{-1.4} ≤ 5/2 ≤ 10`) hold for n=0..3 and for all n (`(4(n+4))³ ≤ (n+4)⁶` iff `(n+4)³ ≥ 64`). `T0 = lemT z = 0.98399 ≥ 31/32 = 0.96875`; Lemma 2.8 relation `(1-T0)Im m_E = √T0 Im z` checked (the `lemT`/`lemE` reading is the paper's). W1: `STDriftHi` ✓, `STReg5I` ✓ (`λ²/L²=0.390625 ≤ 7/16`, `1-s ≤ λ²`), `STReg5IV` ✗ (not needed there). W2: `STReg5IV` ✓ (`1/16 ≤ 0.0977`), `t=31/32 ≤ T0` ✓.
**Row 9′ range, concrete limit (external-style hypothesis `N^{-1+δ} ≤ 1-T0`):** `1-T0 = 0.0160` is constant in n (`z_n` constant) while `N_n^{-1+δ} = ((4(n+4))³)^{-0.95} ↓ 0` (3.7·10⁻⁴, 1.96·10⁻⁴, 1.04·10⁻⁵ at n=0,1,10) ⇒ holds for all n. `κ' = 0.2222 ≤ Im m_E = 0.9682` for all n (E constant). The thresholds of table rows 4, 7, 9 are in the proof of the eventual conclusions only; no instance hypothesis needs them.
**Not checked by script (read from files):** `Σ‖S‖ ≤ 1` is the band lemma `sum_norm_SB_row`; the instance `λ=5/2` needs a new `Sizes 3` value (`szB` with `lam := fun _ => 5/2`; the band pattern `szG := { szB with lam := … }`, Step5Pins:497), whose `Admissible` is the script's `locDomain/Bandwidth/WO` lines.

### Verdicts
- T1 (kit `expLK_*g`, `expLK_precg`, `expLK_expectg`): PASS (rows 1–8, 13; W-a).
- T2 (`STExpLKLKHiConclgL_of_LKU`, `stExpLKLKHigL_of`): PASS (W1 instance; pin shape `STIngR6gL` with `STDriftHi`).
- T3 (split/kit, `expDr_EGtK_precg`): PASS (rows 9–10; `STExpAvgUgL` per-flow, no `STImproveExpAvergL`).
- T4 (`STExpDriftLoConclgL_of_LKU`, `stExpDriftLogL_of`): PASS (W2 instance; `λ²/L³` slack 0.035).
- T5 (`STExpDriftDecayConclgL_of_GdecayW`, `stExpDriftDecaygL_of`): PASS; W-d decided without a gate (row 11, decision above).
No change to rows, layout or any binding text; no W-d gate; no 1a-audit needed.

## (a′) Preflight corrections — Wed Oct 14 12:34:49 UTC 2026
1. (a) row 6 derives `Kenv = 6` for ℰ^{LK×LK} (`‖𝓛^{(2)}‖`, `‖𝒦^{(2)}‖`) and row 10 reuses it for T3–T4.  The envelope of ℰ^{G̃} also carries the factor `avg = 𝓛^{(1)} - m_σ`: the band reads `avg = (𝓛-𝒦)^{(1)}` (`expDr_avg_eq`, ExpEtermsB:193) and `‖m_σ‖ = 1` (`norm_mSigma`, ExpEtermsB:217).  Over a carrier row 9′ gives `FlowFM.m` only `κ' ≤ Im m`; no class named in (a) gives `avg ≺ B` or `‖m‖ ≤ poly(N)`.  Both follow from the first conjunct of row 19 (`∀ᶠ n, ∀ u ∈ [0,1), 𝒦^{(1)}_{σ,a} = m_σ`; band `ST_Kloop_one`, BA `baKsol_oneLoop` `BA/SEforLnBA:113`) with row 17 at `k = 1` (`‖m‖ ≤ N`).  That conjunct (only it) is therefore a guarded inline family premise `hK1` of targets 4 and 5; the ticket's table lists row 19 for WardI only.  Exponent table unchanged: envelopes `4N⁵` (ℰ^{G̃}) and `20N⁵` (X_B) `≤ N⁶` for `N ≥ 20` (`ExpEtermsBGen_env_poly`, B:281).
2. Row 18 (W-d, decided in (a) at the `FlowFM` labels) is stated as `hDec : 3 ≤ d → ∀ sz κ ε 𝔠 𝔡 z, 0 < κ → 0 < ε → Flow → ∀ s t, …`: the merged BA forms `baDecayLoopU_of` (`BA/DecayLoopBA:60`) and `baEtermDecaygL` (`BA/SEforLnBA:271`) take `3 ≤ d` first, the band `stDecayLoopU_of_step2` takes `0 < ε` (ExpEtermsB:973); the guards only weaken the hypothesis.
Verdict of (a) unchanged: PASS for T1–T5 (no row, layout or binding text of the ticket changes; no W-d gate).  The premise `hK1` is reported in (d).

## (b) Script output

S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/da3c2172-ff96-4010-81cd-6590580d0877/scratchpad/T2506   # scratch directory of this ticket; commands run in /Users/junyin/Lean_proof/RBM3D-wt/T2506
$ date -u
Wed Oct 14 12:34:35 UTC 2026
$ git log --format='%h %s' d3104f3b..t/T2506 | cut -c1-100
a990102c T2506 row a: instances of expLK_precg and expLK_expectg
3ca3ff12 T2506 row a: Chain/ExpEtermsBGen (targets 3-5), registry owner texts, import lines
9a537c32 T2506 row a: Chain/ExpEtermsAGen (targets 1-2, (eq:Exp(L-K)1) over the carrier)
$ lake build RBM3D.Chain.ExpEtermsAGen RBM3D.Chain.ExpEtermsBGen 2>&1 | tail -n 1
Build completed successfully (3911 jobs).
$ lake build 2>&1 | grep -E 'Build completed|error'
Build completed successfully (4392 jobs).
$ wc -l RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean   # bottom-up figures: A 595, B 1000; row stop 2,250
     688 RBM3D/Chain/ExpEtermsAGen.lean
    1027 RBM3D/Chain/ExpEtermsBGen.lean
    1715 total
$ lake env lean $S/axioms.lean | sed -E "s/'RBM.BA.([^']*)' depends on axioms: /\1\t/" | awk -F'\t' '{n[$2]=n[$2] (n[$2]==""?"":", ") $1; c[$2]++} END {for (k in n) print c[k] " declarations with axioms " k ": " n[k]}'
18 declarations with axioms [propext, Classical.choice, Quot.sound]: expLK_window_leg, expLK_envg, expLK_env_polyg, expLK_precg, expLK_expectg, STExpLKLKHiConclgL_of_LKU, stExpLKLKHigL_of, stExpLKLKHi_of_gL, ExpEtermsAGen_Bctl_le_two, ExpEtermsAGen_ctrl, ExpEtermsAGen_norm_L_le, expDr_EGtK_precg, STExpDriftLoConclgL_of_LKU, stExpDriftLogL_of, STExpDriftDecayConclgL_of_GdecayW, stExpDriftDecaygL_of, stExpDriftLo_of_gL, stExpDriftDecay_of_gL
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | wc -l
       0
--- the endpoint statements (extracted by script: text up to ':=', joined on one line)
$ python3 $S/extract.py stmts
ExpEtermsAGen.lean:53: theorem expLK_window_leg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (M : ℝ) (f : Zd d (sz.L n) → ℝ) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hM : ∀ x, ‖C.L n u σ ![x, a 1] ω - C.K n u σ ![x, a 1]‖ ≤ M) (hf : ∀ y, ‖C.L n u σ ![a 0, y] ω - C.K n u σ ![a 0, y]‖ ≤ f y) : ‖STELKLKg C n u σ a ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * M * ∑ y : Zd d (sz.L n), f y
ExpEtermsAGen.lean:93: theorem expLK_envg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (cL cK : ℝ) (hcol : ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hL : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.L n u σ b ω‖ ≤ cL) (hK : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.K n u σ b‖ ≤ cK) : ‖STELKLKg C n u σ a ω‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * (cL + cK) ^ 2
ExpEtermsAGen.lean:193: theorem expLK_env_polyg (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im) {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1) (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) : ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ), ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (6 : ℝ)
ExpEtermsAGen.lean:333: theorem expLK_precg (μ : Measure sz.SeqΩ) (hd : 2 ≤ d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hLKU : STLKUgL C μ s t) (hGd : STGdecayWgL C μ s t 0) : PrecL sz μ (U := STIdx2 sz s t) (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))
ExpEtermsAGen.lean:409: theorem expLK_expectg (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) {s t : ℕ → ℝ} {Kenv : ℝ} (hsz : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (henv : ∀ᶠ n in atTop, ∀ (p : STIdx2 sz s t n) (ω : sz.SeqΩ), ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv) (hprec : PrecL sz μ (U := STIdx2 sz s t) (fun n p ω => ‖STELKLKg C n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (11 / 5 : ℝ))) : STExpLKLKHiConclgL C μ s t
ExpEtermsAGen.lean:498: theorem STExpLKLKHiConclgL_of_LKU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im) {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1) (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hLKU : STLKUgL C μ s t) (hGd : STGdecayWgL C μ s t 0) : STExpLKLKHiConclgL C μ s t
ExpEtermsAGen.lean:516: theorem stExpLKLKHigL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz)) (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0) (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1) : STExpLKLKHigL d law Flow mk T0
ExpEtermsBGen.lean:555: theorem expDr_EGtK_precg (hμ : IsProbabilityMeasure μ) (hsz : sz.SizeTendsto) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hKb : STKboundgL C μ) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hAvg : STExpAvgUgL C μ s t) : PrecL sz μ (U := STIdx2 sz s t) (fun n p _ => ‖ExpEtermsBGen_EGtK C μ n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ 4)
ExpEtermsBGen.lean:622: theorem STExpDriftLoConclgL_of_LKU {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im) {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1) (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)), C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n)) (hR : STReg5IV sz s t) (hLKU : STLKUgL C μ s t) (hAvg : STExpAvgUgL C μ s t) : STExpDriftLoConclgL C μ s t
ExpEtermsBGen.lean:717: theorem stExpDriftLogL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz)) (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0) (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1) (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)), (mk sz z).K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)) : STExpDriftLogL d law Flow mk T0
ExpEtermsBGen.lean:745: theorem STExpDriftDecayConclgL_of_GdecayW {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hμ : IsProbabilityMeasure μ) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hadm : sz.Admissible 𝔠 𝔡) {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ} (hrep : CltRepg C μ H₀ g' E) {κ' δ : ℝ} (hκ' : 0 < κ') (hδ : 0 < δ) (hm : ∀ n, κ' ≤ (C.m n).im) {s t T : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T n) (hT1 : ∀ n, T n < 1) (hrange : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - T n) (hKb : STKboundgL C μ) (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖C.S n x y‖ ≤ 1) (hK1 : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)), C.K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then C.m n else (starRingEnd ℂ) (C.m n)) (hGd : STGdecayWgL C μ s t 0) (hDL : ∀ Cd : ℝ, STGdecayWgL C μ s t Cd → STDecayLoopUgL C μ s t) (hDE : STDecayLoopUgL C μ s t → ∀ σ : Fin 2 → Bool, STEKDecaygL μ s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STELKLKg C n (v : ℝ) σ a ω) ∧ STEKDecaygL μ s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STEGtg C n (v : ℝ) σ a ω)) : STExpDriftDecayConclgL C μ s t
ExpEtermsBGen.lean:831: theorem stExpDriftDecaygL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hμ : ∀ sz : Sizes d, IsProbabilityMeasure (law sz)) (hFl : Step2EventsGen_Flow d Flow T0) (hClt : IniTermGen_CltFlow d law Flow mk T0) (hK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) (hS : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n), ‖(mk sz z).S n x y‖ ≤ 1) (hK1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (τ : Bool) (x : Zd d (sz.L n)), (mk sz z).K n u (fun _ : Fin 1 => τ) (fun _ => x) = if τ then (mk sz z).m n else (starRingEnd ℂ) ((mk sz z).m n)) (hDec : 3 ≤ d → ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ T0 sz z n) → (∀ Cd : ℝ, STGdecayWgL (mk sz z) (law sz) s t Cd → STDecayLoopUgL (mk sz z) (law sz) s t) ∧ (STDecayLoopUgL (mk sz z) (law sz) s t → ∀ σ : Fin 2 → Bool, STEKDecaygL (law sz) s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STELKLKg (mk sz z) n (v : ℝ) σ a ω) ∧ STEKDecaygL (law sz) s t (fun n v ω (a : Fin 2 → Zd d (sz.L n)) => STEGtg (mk sz z) n (v : ℝ) σ a ω))) : STExpDriftDecaygL d law Flow mk T0
--- compiled nonempty instances: every example of both files (header up to ':=', cut at 200 chars)
$ python3 $S/extract.py ex
ExpEtermsAGen.lean:569: example (ω : szB.SeqΩ) : ‖STELKLKg (bandFM szB (STflowE zB)) 0 (7 / 8) ![true, false] ![(0 : Zd 3 (szB.L 0)), 0] ω‖ ≤ ((szB.W 0 : ℕ) : ℝ) ^ 3 * (∑ x : Zd 3 (szB.L 0), ‖(bandFM 
ExpEtermsAGen.lean:585: example (ω : szB.SeqΩ) (cK : ℝ) (hK : ∀ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖ ≤ cK) : ‖STELKLKg (bandFM szB (STflowE zB)) 0 (7 / 
ExpEtermsAGen.lean:595: example : ∀ᶠ n in atTop, 20 ≤ ((szB.size n : ℕ) : ℝ) ∧ ∀ u : ℝ, u ≤ 15 / 16 → 0 < 1 - u ∧ (etaOf ((bandFM szB (STflowE zB)).m n) u)⁻¹ ≤ ((szB.size n : ℕ) : ℝ) ∧ (1 - u)⁻¹ ≤ ((s
ExpEtermsAGen.lean:605: example : ∀ᶠ n in atTop, ∀ (p : STIdx2 szB (fun _ => 7 / 8) (fun _ => 15 / 16) n) (ω : szB.SeqΩ), ‖STELKLKg (bandFM szB (STflowE zB)) n (p.1 : ℝ) p.2.1 p.2.2 ω‖ ≤ ((szB.size n 
ExpEtermsAGen.lean:617: example (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) (hGd : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 
ExpEtermsAGen.lean:627: example (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) (hGd : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 
ExpEtermsAGen.lean:645: example (hLKU : STLKUgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) (hGd : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 
ExpEtermsAGen.lean:657: example : STExpLKLKHigL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
ExpEtermsAGen.lean:664: example {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : S
ExpEtermsAGen.lean:677: example : InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
ExpEtermsAGen.lean:680: example : InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32)
ExpEtermsAGen.lean:683: example : InstIng6Concl (fun sz E s t => STExpLKLKHiConcl sz E s t) sz0 z0 sInst tInst
ExpEtermsBGen.lean:944: example (hAvg : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4)) : PrecL szG (Sizes.seqP szG) (U := STIdx2 szG (fun _ => 5 / 8) (fun _ 
ExpEtermsBGen.lean:954: example (hLKU : STLKUgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5 / 8) (fun _ => 3 / 4)) (hAvg : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.seqP szG) (fun _ => 5
ExpEtermsBGen.lean:967: example : STExpDriftLogL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
ExpEtermsBGen.lean:976: example (hGd : STGdecayWgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) 0) : STExpDriftDecayConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB)
ExpEtermsBGen.lean:991: example : STExpDriftDecaygL 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
ExpEtermsBGen.lean:1000: example {d : ℕ} {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop} {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : 
ExpEtermsBGen.lean:1017: example : InstIng6Concl (fun sz E s t => STExpAvgU sz E s t → STExpDriftLoConcl sz E s t) szG zB (fun _ => 5 / 8) (fun _ => 3 / 4)
ExpEtermsBGen.lean:1022: example : InstIng6Concl (fun sz E s t => STExpDriftDecayConcl sz E s t) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16)
--- scan before (standalone RBM3D.lean of main d3104f3b, no new imports) and after (lake env lean RBM3D.lean at t/T2506 HEAD)
$ grep -E 'premises found by scanning|^registry' $S/scan_before.out $S/audit_final.out | sed 's#.*/##' | cut -c1-175
scan_before.out:premises found by scanning: 143 (borrowed 1, owed 64, structural 58, refuted 6, superseded 14).
scan_before.out:registry: 2 borrowed + 118 owed + 138 structural + 7 refuted + 19 superseded; 141 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
audit_final.out:premises found by scanning: 137 (borrowed 1, owed 61, structural 55, refuted 6, superseded 14).
audit_final.out:registry: 2 borrowed + 118 owed + 138 structural + 7 refuted + 19 superseded; 147 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
$ grep -hE '^  RBM.BA.(STExpLKLKHigL|STExpDriftLogL|STExpDriftDecaygL):' $S/scan_before.out $S/audit_final.out | sed 's/ \[no certificate\]//' | paste -sd' ' -
  RBM.BA.STExpLKLKHigL: 4   RBM.BA.STExpDriftLogL: 2   RBM.BA.STExpDriftDecaygL: 2   RBM.BA.STExpLKLKHigL: 5   RBM.BA.STExpDriftLogL: 3   RBM.BA.STExpDriftDecaygL: 3
$ python3 $S/scandelta.py $S/scan_before.out $S/audit_final.out
newly carry nothing: STExpDriftDecayConclgL, STExpDriftDecaygL, STExpDriftLoConclgL, STExpDriftLogL, STExpLKLKHiConclgL, STExpLKLKHigL | no longer carry nothing: []
$ git diff d3104f3b..t/T2506 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep -E '^[+-][^+-]' | cut -c1-90
+import RBM3D.Chain.ExpEtermsAGen
+import RBM3D.Chain.ExpEtermsBGen
-   -- T2502 (BA-V V1s1, DECISIONS §314): the generic Step-6 pins that the public theorems
+   -- T2502 (BA-V V1s1, DECISIONS §314): the generic Step-6 pins that the public theorems
-   `RBM.BA.STExpLKLKHigL, -- `(eq:Exp(L-K)1)` over the tuple (`Chain/Step6Gen.lean`): hyp
-   `RBM.BA.STExpDriftLogL, -- `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` over the tuple: 
-   `RBM.BA.STExpDriftDecaygL, -- `(deccA0)` of the expected drift over the tuple: hypothe
+   `RBM.BA.STExpLKLKHigL, -- `(eq:Exp(L-K)1)` over the tuple (`Chain/Step6Gen.lean`): hyp
+   `RBM.BA.STExpDriftLogL, -- `(eq:Exp(L-K)2)`, `(eq:ExpLWn=2_smalleta)` over the tuple: 
+   `RBM.BA.STExpDriftDecaygL, -- `(deccA0)` of the expected drift over the tuple: hypothe
--- diff scope, layering, check file
$ git diff --stat d3104f3b..t/T2506 | cat
 RBM3D.lean                     |    2 +
 RBM3D/Chain/ExpEtermsAGen.lean |  688 +++++++++++++++++++++++++++
 RBM3D/Chain/ExpEtermsBGen.lean | 1027 ++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean         |    8 +-
 4 files changed, 1721 insertions(+), 4 deletions(-)
$ git diff d3104f3b..t/T2506 -- RBM3D/Induction RBM3D/Graph RBM3D/BA RBM3D/Chain/Step6Gen.lean RBM3D/Chain/Step6KitGen.lean | wc -l
       0
$ grep -nE '^import' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | sed 's#RBM3D/Chain/##' | paste -sd' ' -
ExpEtermsAGen.lean:6:import RBM3D.Chain.Step6KitGen ExpEtermsAGen.lean:7:import RBM3D.Induction.ExpEtermsA ExpEtermsAGen.lean:8:import RBM3D.Chain.KDecayGen ExpEtermsAGen.lean:9:import RBM3D.Chain.CltFarUGen ExpEtermsBGen.lean:6:import RBM3D.Chain.ExpEtermsAGen ExpEtermsBGen.lean:7:import RBM3D.Induction.ExpEtermsB ExpEtermsBGen.lean:8:import RBM3D.Chain.DecayGen ExpEtermsBGen.lean:9:import RBM3D.Chain.SEforLnGen2
$ grep -rln 'import RBM3D.Chain.ExpEtermsAGen\|import RBM3D.Chain.ExpEtermsBGen' RBM3D RBM3D.lean | paste -sd' ' -
RBM3D/Chain/ExpEtermsBGen.lean RBM3D.lean
$ grep -hE '^import' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | grep -cE 'RBM3D.BA|Step2Kern|ExpAvgGen'
0
$ lake env lean docs/tickets/checks/T2506-check.lean > $S/check.out 2>&1; echo exit=$? errors=$(grep -c error $S/check.out)
exit=0 errors=0
--- hypothesis rules
$ grep -nE '^(noncomputable )?(def|abbrev|structure) ' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | wc -l   # X1-C4: public defs
       0
$ grep -nE '^private (noncomputable )?def' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | cut -c1-60 | paste -sd' ' -   # private twins
RBM3D/Chain/ExpEtermsBGen.lean:103:private def ExpEtermsBGen RBM3D/Chain/ExpEtermsBGen.lean:112:private def ExpEtermsBGen
$ python3 $S/stmtgrep.py 'mE|zt E|zt \(|\|E\||2 - κ|etaT|lemT|STFlow|STflowE|STKloop|Lloop|loopFine|Ugen|uKer d|mSigma|seqHflow|seqP|withLam|lam0|BAflowLam0|norm_mE|Prec sz|ThetaN d|STthetaOp|HflowBlock|PF d|STLKM|STELKLKM|SB d' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | awk '{print $2}' | sort | uniq -c | paste -sd' ' -   # C1/X1-C1 regex over declaration statements, by kind
  34 [example    9 [private
$ python3 $S/stmtgrep.py 'mE|zt E|zt \(|\|E\||2 - κ|etaT|lemT|STFlow|STflowE|STKloop|Lloop|loopFine|Ugen|uKer d|mSigma|seqHflow|seqP|withLam|lam0|BAflowLam0|norm_mE|Prec sz|ThetaN d|STthetaOp|HflowBlock|PF d|STLKM|STELKLKM|SB d' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | grep -vE '\[example' | awk '{print $1,$2,$3}' | sort -u -k2,3 | paste -sd' ' -   # non-example hits
ExpEtermsBGen.lean:877: [private ExpEtermsBGen_band_decay]
$ grep -nE 'STImproveExpAver|st6_expAvgU_of_pin|hAvg :' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | cut -c1-96
RBM3D/Chain/ExpEtermsBGen.lean:554:(V1L-C1: no global `STImproveExpAvergL`). -/
RBM3D/Chain/ExpEtermsBGen.lean:557:    (hcol : ∀ (n : ℕ) (y : Zd d (sz.L n)), ∑ x : Zd d (sz.L n
RBM3D/Chain/ExpEtermsBGen.lean:631:    (hR : STReg5IV sz s t) (hLKU : STLKUgL C μ s t) (hAvg : S
RBM3D/Chain/ExpEtermsBGen.lean:944:example (hAvg : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.
RBM3D/Chain/ExpEtermsBGen.lean:955:    (hAvg : STExpAvgUgL (bandFM szG (STflowE zB)) (Sizes.seqP
$ grep -nE '∀ \(sz : Sizes d\)' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | cut -d: -f1,2 | sed 's#RBM3D/Chain/##' | paste -sd' ' -   # U5S-C3 hits
ExpEtermsAGen.lean:517 ExpEtermsAGen.lean:518 ExpEtermsAGen.lean:520 ExpEtermsAGen.lean:521 ExpEtermsAGen.lean:664 ExpEtermsAGen.lean:665 ExpEtermsAGen.lean:668 ExpEtermsBGen.lean:718 ExpEtermsBGen.lean:719 ExpEtermsBGen.lean:721 ExpEtermsBGen.lean:722 ExpEtermsBGen.lean:724 ExpEtermsBGen.lean:832 ExpEtermsBGen.lean:833 ExpEtermsBGen.lean:835 ExpEtermsBGen.lean:836 ExpEtermsBGen.lean:838 ExpEtermsBGen.lean:842 ExpEtermsBGen.lean:1000 ExpEtermsBGen.lean:1001 ExpEtermsBGen.lean:1004 ExpEtermsBGen.lean:1007
$ grep -nE 'withLam|gK' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | cut -d: -f1,2 | sed 's#RBM3D/Chain/##' | paste -sd' ' -   # UBA hits
ExpEtermsAGen.lean:181 ExpEtermsAGen.lean:182 ExpEtermsBGen.lean:133 ExpEtermsBGen.lean:136 ExpEtermsBGen.lean:137
$ grep -cE 'ExpAvgGen|AzumaProxy|STGridRepNgL|import RBM3D.BA' RBM3D/Chain/ExpEtermsAGen.lean RBM3D/Chain/ExpEtermsBGen.lean | sed 's#RBM3D/Chain/##' | paste -sd' ' -
ExpEtermsAGen.lean:0 ExpEtermsBGen.lean:0

Narrative (row a only; `t/T2506` from `main` d3104f3b; rows b is `t/T2506b`, not covered).
* Layout: `ExpEtermsAGen` (targets 1–2; kit `expLK_*g`, W-a at A:193) and `ExpEtermsBGen` (targets 3–5).  No band or merged file is in the diff; no `Probe` file (the W-d gate did not run).
* B sections (`## n` headers): 1 cuts B:48 (private twins `ExpEtermsBGen_EGtLK`, `_EGtK`; `bilin_le`, `cuts_le` over `C.S`, column sums ≤ 1), 2 measurability, integrability, envelope of ℰ^{G̃} from `CltRepg` B:121, 3 split B:190, 4 polynomial envelopes (W-a) B:272, 5 `≺ → 𝔼` and the three estimates B:372 (`expDr_EGtK_precg` B:555), 6 target 4 B:616, 7 target 5 B:738, 8 band re-derivations B:859, 9 instances B:932; end B:1027.  A: 1 kit A:45, 2 control and envelope (W-a) A:109, 3 decay A:240, 4 `≺ → 𝔼` A:404, 5 target 2 A:492, 6 band A:533, 7 instances A:557.
* Reused from the band by name or `open private` (no `private` deleted): `expDr_Bctl_le_IV`, `expDr_floor`, `expDr_first_moment`, `expDr_decay_step`, `expDr_W_le_size` (B); `expLK_Bctl_ge`, `expLK_first_moment`, `expLK_latticeSum` (A).  Merged texts used: `stKbound_timeIccgL`, `st6_prec_det_iffg`, `CltRepg`, `IniTermGen_CltFlow`, `STEKDecaygL`, `STDecayLoopUgL`, `walk_measurable_loopFine`.
* W-a: `‖C.L^{(k+1)}‖ ≤ η⁻¹ ^ (k+1)` from `CltRepg` and `norm_loopM_le` (A:172); `η⁻¹ ≤ N`, `(1-u)⁻¹ ≤ N` from row 9′ (`ExpEtermsAGen_ctrl`, A:139); `‖𝒦^{(k)}‖` from row 17; `‖m‖ ≤ N` from row 19 K1 and row 17 at `k = 1` ((a′) 1).  No new class beyond the named texts except `hK1`.
* W-d: no gate.  Target 5 takes row 18 as `hDL`, `hDE` (E-term decays at `STELKLKg C`, `STEGtg C`, `k = 2`); the band discharge is `ExpEtermsBGen_band_decay` (B:876: `stDecayLoopU_of_step2`, `stEtermDecay`, term bridges `STEGtM_eq_STegtM`, `STELKLKM_eq_STelklkM`).  The BA bridge from `baEtermDecaygL` to these labels is V1-BA's (open issue 2).
* Family premises as used: rows 1 (`law` probability), 2 (`Step2EventsGen_Flow`), 9′ (`IniTermGen_CltFlow`), 17 (`STKboundgL`), 20 (column sums only) in A and B; row 19 (K1 conjunct) and, in target 5, row 18 in B; row 3 unused.  R1 never used (UBA-C1); `withLam` occurs only in proofs that unpack `CltRepg` (A:181-182, B:133-137), with no comparison of `lam` and `g'`.  V1L-C1: the only average premise is `STExpAvgUgL` (B:554-557, 631); no `Chain/ExpAvgGen`, `BA/*`, `Step2Kern` import.
* Instances: `d = 3`, band data `szB`/`szG`, flow `zB`, windows `[7/8, 15/16]` (A, target 5) and `[5/8, 3/4]` (target 4); left as hypotheses: the stochastic premises `STLKUgL`, `STExpAvgUgL`, `STGdecayWgL … 0`; discharged: flow, admissibility, ranges, row 9′ (`iniTermGen_cltFlow_band`), `STKboundgL`, column sums, K1, and row 18 for target 5.  No `N = 0`, empty index or `False` premise.
* Statement diff (ticket item 3): row a has no binding `T2506_*` text.  Shape `T2506_RowAOf` (check file, non-binding): conjunct 1 is applied in the example A:664 (bundled `T2506_FamBase`); conjuncts 2–3 differ by `hK1` and the guards of `hDec` ((a′), open issue 3); example B:1000 applies `stExpDriftLogL_of` to the bundle plus `hOne`.
* Registry: header `:224` of the T2502 block and the owner texts of `STExpLKLKHigL`, `STExpDriftLogL`, `STExpDriftDecaygL` updated (the T2502 c pattern: entries stay, text names the producer); the scan found no new unregistered premise (the audit passes); the three pins and three conclusion `Prop`s are now concluded by theorems, so `found` drops by 6 (143 → 137) and "carry nothing" rises by 6.
* Stop rule (`wc -l` at each commit): 660 (9a537c32), 660 + 1027 (3ca3ff12), 688 + 1027 (a990102c); row stop 2,250, per-file 2,000.
* Ports: none from RBM1D/RBM2D (the conversion restates the band files of this project), so no RBM1D/RBM2D diff-stat.  Name-clash grep of the new public names on `main`, `t/T2506b`, `t/T2505`, `t/T2505b`, `t/T2502c`: see below.

--- name-clash grep of the new public names (git grep over RBM3D/, my two files excluded; ports from RBM1D/RBM2D: none, so no diff-stat)
$ git grep -nE <18 public names + ExpEtermsAGen_*/ExpEtermsBGen_* stems> <ref> -- RBM3D ':!RBM3D/Chain/ExpEtermsAGen.lean' ':!RBM3D/Chain/ExpEtermsBGen.lean' | wc -l
main (3e514c5c):        0
t/T2506b (5d0d47e4):        0
t/T2505 (2a7ddae2):        0
t/T2505b (29c0faf2):        0
t/T2502c (7cf02a5f):        0
worktree t/T2506 outside my two files:        3 lines, in: RBM3D/Test/Axioms.lean (the registry owner texts I wrote)

## (c) Verified Mathlib names used (each compiled in the new files; `#check` ok)
`MeasureTheory.Integrable.of_bound`, `integral_sub`, `integral_add`, `integral_const_mul`, `integral_mul_const`, `integral_finsetSum`, `integral_const`, `norm_integral_le_integral_norm`, `measure_empty`;
`ENNReal.toReal_le_of_le_ofReal`, `Finset.measurable_sum`, `Measurable.const_mul`, `Measurable.sub_const`, `Measurable.mul_const`, `Measurable.comp`, `Continuous.measurable`;
`Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_exponent_ge`, `Real.rpow_le_rpow_of_nonpos`, `Real.inv_rpow`, `tendsto_rpow_atTop`;
`inv_anti₀`, `pow_le_pow_left₀`, `one_le_pow₀`, `inv_le_one_of_one_le₀`, `one_le_inv₀`, `Complex.norm_natCast`, `ite_true`.
Verified deprecated: `if_true` (compiler: "`if_true` has been deprecated: Use `ite_true` instead"); the new files use `ite_true`.  Names verified absent: none searched.

## (d) Open issues and paper-delta candidates
1. **Row 19 K1 premise (needs dispatcher sign-off).**  `hK1` ((a′) 1) is a premise of `STExpDriftLoConclgL_of_LKU`, `stExpDriftLogL_of`, `STExpDriftDecayConclgL_of_GdecayW`, `stExpDriftDecaygL_of`; it is not in the ticket's table for these files.  The pin `STExpDriftDecaygL` has no average premise (`STIngR6gL`, `Step6Gen:100-112`), so target 5 has no other source of `‖m‖`; for target 4 a derivation from `STAvgUgL` and `STExpAvgUgL` instead of `hK1` might exist (not attempted).  Named discharges: band `ExpEtermsBGen_band_K1` (B:864), BA `baKsol_oneLoop` (`BA/SEforLnBA:113`, in the check file).
2. **Row 18 at BA.**  `hDec` ((a′) 2) is at the `FlowFM` labels `STELKLKg`, `STEGtg`; `baEtermDecaygL` is at `STegtg`/`STelklkg` of `baStep2Mat`; the bridge terms named in (a) W-d (`Step2EventsGen_STEGtMg_eq`, `STEGtMg_eq_STegtMg`, `STELKLKMg_eq_STelklkMg`) are V1-BA's to apply; not proved here.
3. The check file shapes `T2506_RowAOf` (conjuncts 2–3) and `T2506_FamDecay` differ from the proved wrappers by `hK1` and the guards of `hDec`; both are non-binding in the ticket.
4. Registry bookkeeping: the three pins now carry nothing in the scan (text updated as T2502 c did); the dispatcher decides whether they leave `owedProps`.  `RBM3D.lean` and `Test/Axioms.lean` lines are a union with row b and T2505 at merge.
5. Paper-delta candidates: none.  The constants (`9N⁵`/`20N⁵` against the band `4N⁵`) and `hK1` are Lean-internal; no Lean/paper statement differs.

## Repair (audit round 1, defect 1) — Wed Oct 14 13:12:46 UTC 2026

Repairer model: claude-opus-5-5. Scope: `docs/tickets/T2506-amend-1.md` (repair (1) of `docs/reports/T2506-audit.md`); only the `expLK_envg` instance changed; no target statement changed.
```
$ git diff a990102c 6d6dde16 --stat
 RBM3D/Chain/ExpEtermsAGen.lean | 16 ++++++++++------
 1 file changed, 10 insertions(+), 6 deletions(-)
$ sed -n 583,596p RBM3D/Chain/ExpEtermsAGen.lean
set_option maxRecDepth 20000 in
/-- Target 1: the envelope `expLK_envg` at `(szB, n = 0, u = 7/8)` with the loop bound of the band (`norm_Lloop_le`, `η⁻²`) and a bound of `𝒦^{(2)}` by `1/(1-u)` (`norm_kTwo_le`
through the band `STKloop`; here the `K` bound is `cK := Σ_b ‖K b‖`, by `Finset.single_le_sum`). -/
example (ω : szB.SeqΩ) :
    ‖STELKLKg (bandFM szB (STflowE zB)) 0 (7 / 8) ![true, false] ![(0 : Zd 3 (szB.L 0)), 0] ω‖ ≤
      ((szB.W 0 : ℕ) : ℝ) ^ 3 * ((szB.L 0 : ℕ) : ℝ) ^ 3 * ((etaT (STflowE zB 0) (7 / 8))⁻¹ ^ 2 +
        ∑ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖) ^ 2 :=
  expLK_envg (bandFM szB (STflowE zB)) 0 (7 / 8) ω ![true, false] ![0, 0] ((etaT (STflowE zB 0) (7 / 8))⁻¹ ^ 2)
    (∑ b : Fin 2 → Zd 3 (szB.L 0), ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖)
    (fun y => ExpEtermsAGen_band_col szB _ 0 y)
    (fun b => szB.norm_Lloop_le 0 (st6_flowE_lt_two szB (κ := 1 / 10) (by norm_num) flow_zB 0)
      (by norm_num : (7 / 8 : ℝ) < 1) (k := 1) ![true, false] b ω)
    (fun b => Finset.single_le_sum (f := fun b : Fin 2 → Zd 3 (szB.L 0) =>
      ‖(bandFM szB (STflowE zB)).K 0 (7 / 8) ![true, false] b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b))
$ lake build RBM3D.Chain.ExpEtermsAGen RBM3D.Chain.ExpEtermsBGen > repair_build.out 2>&1; echo exit=$?; tail -1 repair_build.out; grep -c error repair_build.out
exit=0
Build completed successfully (3911 jobs).
0
$ grep -nwE "sorry|admit|native_decide|axiom" RBM3D/Chain/ExpEtermsAGen.lean | wc -l
       0
$ git log --oneline -1
6d6dde16 T2506 row a repair (audit 1, defect 1): discharge hK in the expLK_envg instance
```
The instance of `expLK_envg` now has no open hypothesis: `cK := ∑ b, ‖K 0 (7/8) ![true,false] b‖`, `hK` by `Finset.single_le_sum`, under `set_option maxRecDepth 20000 in`. Mathlib name used: `Finset.single_le_sum` (compiled above).
