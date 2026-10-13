Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 00:17:58 UTC 2026

Base: `main` d34419a0 (docs-only commit after d1eb95ac), worktree `t/T2480` at d1eb95ac. `ls RBM3D/Chain | grep -c Step2Iter` prints 0 and `docs/queue/T2478.state` says `state: proving`, so T1 has not merged: answer (3), the one-loop fact is inline (target 3 last conjunct). Scripts in `scratchpad/T2480/` (`inst.py`, `lines.py`, `fsem.py`, `spans.py`). Instance = merged `sz0` (`Defs/Sizes.lean:260`), `z0` (`Induction/Defs.lean:413`), `sInst/tInst` (`:439-440`).

### (i) Exponent table (n = 0 is the worst index unless stated; "slack" = measured min over n = 0..39, 10^3, 10^5)

| # | quantity | value | constraint | slack |
|---|---|---|---|---|
| 1 | d, L_n, W_n, lam_n | 3; 4(n+1); (2(n+1))^5; (2(n+1))^-6 | 3 ≤ d, 3 ≤ L, N=(WL)^d → ∞ (N_0 = 2,097,152) | L-3 = 1 |
| 2 | 𝔠 (bandwidth) | 1/6 | W ≥ N^𝔠 | W/N^𝔠 ≥ 2.828 |
| 3 | 𝔡 (WO) | 1/10 | W^(-d/2+𝔡) ≤ lam ≤ 𝔡⁻¹ | lam/W^-1.4 ≥ 2; 10/lam ≥ 640 |
| 4 | κ, ε | 1/10, 1/10 | \|E_n\| ≤ 2-κ; N^(-1+ε) ≤ Im z_n ≤ 1 | E_0 = 0.5, slack 1.4; Im z/N^-0.9 ≥ 4.287 |
| 5 | window s, t | 0, 1/16 | 0 ≤ s < t ≤ lemT(z_n) < 1 (Lemma 2.8: lemT ≥ 1/16) | lemT_0 = 0.999991, slack 0.9375; 1-t = 15/16 |
| 6 | κm (DecayGen_Spec) | √(2κ)/2 = 0.2236 | κm ≤ Im m_n, η = (1-t) Im m | Im m_0 = 0.9682, slack 0.745 |
| 7 | Im m ≤ 1 (target 3 field) | Im mE = √(4-E²)/2 | ≤ 1 for every E | 0.0318 at E = 0.5 (exact for all E) |
| 8 | \|m_σ\| and K^(1) | \|mE\| = 1 (err 0) | K^(1)_σ = m_σ for every t (`KLK_one`, `Loop/KLTree.lean:206`) | K^(1)/Bctl^0 = 1 |
| 9 | Cd, 𝔠d | 4; min(1/100, 1/(30 Cd)) = 1/120 | 𝔠d·Cd ≤ 1/30 (`stSEforLn_holds`, `SEforLn2:1287`) | 0 (equal; for Cd < 10/3, 𝔠d = 1/100 and slack > 0) |
| 10 | (con_st_ind) | Bctl(t)^𝔠d, t = 1/16 | ≤ (1-t)/(1-s) = 15/16 < 1 | 0.01989 (n = 0; larger n smaller) |
| 11 | S = SB(lam_n) | doubly stochastic, 7 nonzeros | row, column sums ≤ 1; support \|a-b\|_∞ ≤ 1 | rowsum 1.000000 (slack 0), max coordinate distance 1 |
| 12 | C₆ (target 7) | 1 | row sums of thetaKer and \|column sum\| ≤ C₆/(1-t) | (1-t)·max = 1.000000: sharp (pair (+,-)), slack 0 |
| 13 | 𝒦^(2) = W^-d μ Θ_{tμ} (`KLK_two`, `KLTree:211`) | Kbound k=2: max\|K2\|/Bctl; Kward: Σ_x\|K2\|·W^dη | ≤ 1 (so ≺ holds with constant 1) | 0.98485 (n=0) → 0.99988 (n=4); 0.96825 = Im m |
| 14 | Ξ̂ orders | STn12E k: n1+n2 = 2k; STn12 n': 2n'-2 | part 3 order sum (k+2-n')+(n'-1) = k+1 for every n' | identity, asserted k = 2..8 |
| 15 | part-4 B exponent | 2k - 1/(2q) | k ≥ 2, q ≥ 1 | 3.5 at (2,1); 7.75 at (4,2) |
| 16 | regime R (targets 5, 9) | not read | `stSEforLn_holds` binds R among `_` (`SEforLn2:1291`); `stWardTypePPin_holds`, `stB45Pin_holds` bind `_hR` | grep below: one docstring hit (`SEforLn2:1286`, "regime `STAny` not used"), no use in a proof |
| 17 | C6 f_sem(KDecay) | 262/1141 whole file = 0.230; §1-§8: 260/791 = 0.329; §9-§11 (restated): 0/338 | tripwire: f_sem > 0.30 outside §1-§8 | outside §1-§8: 0.000 (slack 0.30); §1-§8 not restated |
| 18 | stop / split / reserve lines | 2,000 per file; 1,950 split; 1,800 reserve; 3,375 = 1.5×2,250 | see lines below | see lines below |

Items (iii) hypothesis table, (iv) bridge/`open private` table, (vii) premise-scan preview and (viii) alignment with T2473 are name-level and are left to 1b (stage 1a does no name checks).

### (ii) One concrete instance and external-hypothesis limits

Instance: d = 3, sz0, κ = ε = 1/10, 𝔠 = 1/6, 𝔡 = 1/10, z_n = 1/2 + i N_n^(-4/5), s ≡ 0, t ≡ 1/16 (and k ≥ 2, q ≥ 1, 𝔠d = 1/120, Cd = 4, κm = 0.2236). Target by target: 1 SizeTendsto, window 0 ≤ s ≤ t < 1 (rows 1, 5); 3 loop-form data `Im m > 0`, η = (1-t) Im m, S row/column sums and support, Im m ≤ 1, K^(1) = m (rows 6-8, 11); 4, 5, 6 additionally 𝔠d·Cd ≤ 1/30, s < t, `STConStInd` (rows 9, 10), `DecayGen_Spec` (row 6), `Admissible` (rows 2, 3); 7, 9 flow facts (rows 3-6), C₆ = 1 (row 12). Hermitian `seqHflow`, `IsProbabilityMeasure (seqP sz0)`, LCompat/KCompat, WardCls, LoopForm are Lean facts at the band (merged `bandStep34_*`, `zeroModeGen_wardCls_band`, `stepDecompGen_loopForm_band`), not recomputed here.

```
$ python3 scratchpad/T2480/inst.py
cd=0.008333 cd*Cd=0.033333 (<=1/30=0.033333)
min_n adm_bandwidth W/N^c                             = 2.82843
min_n adm_WO lam/W^(-d/2+dl)                          = 2
min_n adm_lam<=1/dl                                   = 640
min_n E: (2-kap)-|E|                                  = 1.4
min_n locDom: (Im z)/N^(-1+eps) = N^(0.1)             = 4.28709
min_n lemT-1/16                                       = 0.937491
min_n Im mE - sqrt(2kap)/2 (kappa_m)                  = 0.744639
min_n 1-Im mE                                         = 0.0317542
min_n |mE|=1 err                                      = -0
min_n conStInd 15/16 - Bctl^cd(t=1/16)                = 0.0198861
min_n conStInd 1 - Bctl^cd(t=0)... (1-t)/(1-s)=1 strict = 0.0828793
n=0: N=2097152 z=0.5000+8.764e-06i m_sc=-0.2500+0.9682i lemE=0.500000 lemT=0.999991
n=0: S rowsum=1.000000 nnz=7 maxdist=1 | C6row=1.000000 C6col=1.000000 | max|K2|/Bctl=0.984852 | max SumK2*W^d*eta=0.968246
n=1: S rowsum=1.000000 nnz=7 maxdist=1 | C6row=1.000000 C6col=1.000000 | max|K2|/Bctl=0.998051 | max SumK2*W^d*eta=0.968246
n=4: S rowsum=1.000000 nnz=7 maxdist=1 | C6row=1.000000 C6col=1.000000 | max|K2|/Bctl=0.999875 | max SumK2*W^d*eta=0.968246
K1: |m_sigma|=1 vs Bctl^0=1 -> ratio 1.0 (all n above: |mE|=1 err ~0)
assert n12 identities k=2..8: ok; part4 B-exp k=2,q=1: 3.5  k=4,q=2: 7.75
```
(`inst.py` prints n = 0..4 rows; rows n = 2, 3 omitted above, identical in every column but `max|K2|/Bctl` = 0.999422, 0.999756. `C6row/C6col` are `max_t,σσ' (1-t)·Σ|thetaKer|` and `(1-t)|Σ_a thetaKer(a,b)|` over t ∈ {0, 1/32, 1/16, 1/2, 0.9}, `thetaKer = μ S (1-tμS)⁻¹`, `Mss = μ·I` at the band, `KLK_two` for `K2`, via FFT of the circulant `sbKernel`, `Defs/Block.lean:35`.)

External hypotheses (TEAM §8 lesson 14), concrete limits: `STKboundgL` k = 1: |K^(1)| = |m| = 1 = Bctl^0 (ratio 1); k = 2: |K^(2)|/Bctl ≤ 0.99988, increasing to 1 with n; `STKwardgL` k = 2: Σ_x|K^(2)| (W^d η) = Im m = 0.968 ≤ 1. `STKcalDecaygL` k = 2 (pair (+,-), μ = 1, D = 3, 1-u log-spaced from 1 to 1e-50; "0" = far set empty):
```
$ python3 scratchpad/T2480/far.py | grep -E "tau=0.1 D=3 n=(0|5):|tau=0.5 D=3 n=(0|1|8):"    # (path filter shortened)
tau=0.5 D=3 n=0: |K2|/W^-3 on far set = 1.279e+01 (at 1-u=3.2e-04)
tau=0.5 D=3 n=1: |K2|/W^-3 on far set = 0.000e+00 (at 1-u=-)
tau=0.5 D=3 n=8: |K2|/W^-3 on far set = 0.000e+00 (at 1-u=-)
tau=0.1 D=3 n=0: |K2|/W^-3 on far set = 1.407e+14 (at 1-u=1.0e-32)
tau=0.1 D=3 n=5: |K2|/W^-3 on far set = 2.557e+10 (at 1-u=5.6e-14)
```
So at τ = 1/2 the premise is vacuous from n = 1 (ℓ_u W^τ > max ℓ¹ distance), and at τ = 1/10 its eventual threshold is far beyond the computable n (ratio ≫ 1 for n ≤ 5, maximal at 1-u between 2e-9 and 2e-14 for n = 1..5): it is NOT confirmed numerically and is not used by the instance; it rests on the merged band theorem `inst_stKcalDecay_admissible` (`KDecay:976`) and stays an explicit premise. Not computable at a finite index (stochastic Step 2 / loop objects, other gates' pins that stay hypotheses): `STStep2ConclgL` (`STAvgUgL`, `STGdecayWgL`), `STDecayLoopUgL`.

Regime and C6 evidence:
```
$ grep -nE "STCaseI|STAny|STCaseII" RBM3D/Induction/{B45,SEforLn1,SEforLn2,DecayLoopB}.lean
RBM3D/Induction/SEforLn2.lean:1286:other hypotheses of the pin (`STKbound`, `STKward`, `STLK s`, the regime `STAny`) are not used. -/
$ grep -cE "KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP" RBM3D/Induction/{SEforLn1,SEforLn2,B45}.lean
SEforLn1.lean:0   SEforLn2.lean:0   B45.lean:0
$ python3 -I scratchpad/T2480/fsem.py RBM3D/Induction/KDecay.lean | head -5
whole KDecay.lean 1 1436 code 1141 class-(t) 262 f_sem=0.230
S1-S8  KDecay.lean 52 998 code 791 class-(t) 260 f_sem=0.329
S9     KDecay.lean 1001 1100 code 76 class-(t) 0 f_sem=0.000
S10    KDecay.lean 1103 1356 code 211 class-(t) 0 f_sem=0.000
S11 inst KDecay.lean 1358 1436 code 51 class-(t) 0 f_sem=0.000
```
Class-(t) segments (start line, code lines): 88/22, 111/48, 160/4, 166/21, 202/89, 473/7, 482/38, 531/31. T2379's 258/825 is not reproduced (script: 262/1141; the denominator differs, numerators 258 vs 262).

Lines (row 18). Method as T2474 (`T2474-prove.md:68`): raw band lines of declarations that mention a band object (`spans.py` token list; B45 kernel lemmas 670-887 forced in; model-free blocks reused by `open private`; blocks replaced by a class field dropped) × factor f + instances × 0.6 + itemised new material.
```
$ python3 -I scratchpad/T2480/lines.py
restated band raw lines: SEforLn1 456, SEforLn2 14+747, DecayLoopB 460, B45 core 289, B45 2236-2926 559, KDecay S9 85
factor   KDecay  SEforLn  SEf(t6)   B45Gen |  total    U2a    U2b
0.80        150     1305      596     1007 |   3058   2051   1007
0.88        157     1402      633     1075 |   3267   2192   1075
1.00        167     1548      688     1176 |   3580   2404   1176
central(0.88): SEforLnGen with t6 in file = 2035 (> 1800 reserve rule: True); 2.6x: KD 408 SE 3645 SE+t6 5291 B45 2794 total 8494
ticket central 150/1250/850 = 2250 (split rule >1950); mine total 3267; U2a(no t6) 1559; U2a+SEforLnGen2 2192; U2b alone 1075; U2b+SEforLnGen2 1708
C6 REQ test: row + U2-BA twin 937 = 4204 vs 1.5*2250 = 3375  (ticket central: 3187)
```
Reading: central (f = 0.88, T2453 683/778): `KDecayGen` 157, `SEforLnGen` (targets 3-5) 1,402, target 6 (`SEforLnGen2` if reserved) 633, `B45Gen` 1,075; total 3,267 against the ticket's 2,250 (ratio 1.45; T2474's own ratio was 1.45). Every file central is below the stop line 2,000; the 2.6× reference (TLC-4) is above it for `SEforLnGen` (3,645) and `B45Gen` (2,794), so the reserve files are likely needed.

### Verdicts

| target | verdict | reason |
|---|---|---|
| 1 `stKbound_timeIccgL`, `stKward_timeIccgL` | PASS | rows 5, 13; band `KDecay:1017-1100` uses only `P(univ) = 1` and `perTime_timeIcc_of_forall_seq` |
| 2 C6 (no restate) | PASS | outside §1-§8 f_sem = 0 (row 17); the 0.30 test is not triggered; §1-§8 whole-segment 0.329 > 0.30 is the already planned U2-BA twin |
| 3 `SEforLnGen_Facts` | PASS | every field has a numeric or exact band witness (rows 6-8, 11); the one-loop value holds for every t |
| 4 parts 1-4, `stSEforLnConclgL_of` | PASS | rows 9, 10, 14, 15; `𝔠d·Cd ≤ 1/30` is tight but satisfiable |
| 5 `stSEforLngL_of` | PASS, for every R | row 16: `STIngRgL` takes `R sz s t` only as a hypothesis, the band proof drops it |
| 6 Eterm decays | PASS | rows 6, 11, 13; band hypotheses `hE`, `Admissible`, `0 ≤ s ≤ t < 1` become `DecayGen_Spec`, `Admissible`, the window |
| 7 `B45Gen_Facts` | PASS | row 12: C₆ = 1 witnesses both sums, sharp |
| 8 generic B45 core | PASS | restated, 848 raw band lines |
| 9 pins `stWardTypePPingL_of`, `stB45PingL_of` | PASS, for every R | row 16 (`_hR` unused at `B45:2938, 2946`) |
| 10 instances | PASS | rows 1-12 give a nonempty data set; STStep2ConclgL and `STKcalDecaygL` stay hypotheses |
| 11 G1 | PASS | no band statement needs changing; privates by `open private` |

Decision inputs (non-blocking for 1b of U2a, reported per the ticket's stop rules):
1. Split applies: 3,267 > 1,950 (sensitivity 3,058 to 3,580 for f = 0.80 to 1.00). The pre-signed file boundary is confirmed: U2a = `KDecayGen` + `SEforLnGen` (targets 1-5 and their instances, central 1,559) / U2b = `B45Gen` (1,075).
2. The reserve rule fires: `SEforLnGen` with target 6 in the file is 2,035 > 1,800, so target 6 goes to `SEforLnGen2` (633). With it U2a is 2,192 (> 1,950, below any file stop line); with it in U2b, U2b is 1,708 and U2a 1,559, both below 1,950. Recommendation: `SEforLnGen2` in U2b (it imports `SEforLnGen`, stacked after U2a); if the dispatcher keeps the ticket's text (U2a = targets 1-6), U2a is 2,192.
3. C6 REQ line: row 3,267 + U2-BA twin 937 = 4,204 > 3,375 (the ticket's own central gives 3,187). The REQ test of `T2480.md` is exceeded by the 1a's central; this is a notice (G3 for `KDecay` §1-§8 is already the design), no stop at 1a.

## (a′) Preflight corrections — Tue Oct 13 01:08:03 UTC 2026
1. Hypothesis shapes of targets 4 and 6. The verdicts of (a) stand (PASS), but the check file's hypothesis lists (marked "shapes fixed in 1a (iii)", an item (a) left to 1b) omit one field of target 3's class each:
   target 4 needs `support` (`S n a b ≠ 0 → zdistInf (a - b) ≤ 1`): the second contraction inequality sums over the bounded set `{y : |x - y|_∞ ≤ 1}` (band `SEforLn2_SB_sum`, through `DecayLoopB_SB_eq_zero`);
   target 6 needs the one-loop value `hone` (`STavgErr = (𝓛-𝒦)^{(1)}` is `DecayLoopB_avgErr_eq`, which uses `KLK_one`; no listed fact bounds `|m_σ|`). Both fields are in `SEforLnGen_Facts` and witnessed in (a) rows 8 and 11.
2. Lines: shipped 244 / 1718 / 975 (`KDecayGen` / `SEforLnGen` / `SEforLnGen2`, instances included) against the central readings 157 / 1,402 / 633 of (a) row 18 (which include 0.6 x the instances). The reserve rule fired as predicted: target 6 is in `SEforLnGen2`, inside U2a.

## (b) Script output

### B1. Lines, builds
$ wc -l RBM3D/Chain/KDecayGen.lean RBM3D/Chain/SEforLnGen.lean RBM3D/Chain/SEforLnGen2.lean
     244 RBM3D/Chain/KDecayGen.lean
    1718 RBM3D/Chain/SEforLnGen.lean
     975 RBM3D/Chain/SEforLnGen2.lean
    2937 total
$ lake build RBM3D.Chain.KDecayGen RBM3D.Chain.SEforLnGen RBM3D.Chain.SEforLnGen2 | tail -1
Build completed successfully (3808 jobs).
$ lake build   # whole library; RBM3D.lean imports the three modules and runs #assert_rbm_axioms
Build completed successfully (4323 jobs).
$ lake env lean docs/tickets/checks/T2480-check.lean
exit code 0

### B2. `#print axioms` of the 18 new public declarations (ax_all.lean = one line per declaration: stKbound_timeIccgL, stKward_timeIccgL, stKbound_timeIcc_gen_band, KDecayGen_band_STKwardgL, stKward_timeIcc_gen_band, SEforLnGen_Facts, seforLnGen_facts_band, stSEforLn_part1g, stSEforLn_part2g, stSEforLn_part3g, stSEforLn_part4g, stSEforLnConclgL_of, stSEforLngL_of, stEtermDecaygL_egt, stEtermDecaygL_ksim, stEtermDecaygL_elklk, stEtermDecaygL_ee, stEtermDecaygL)
$ lake env lean ax_all.lean | sed "s/.*depends on axioms: //" | sort | uniq -c
  18 [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" <the three files>
RBM3D/Chain/KDecayGen.lean:0 RBM3D/Chain/SEforLnGen.lean:0 RBM3D/Chain/SEforLnGen2.lean:0

### B3. Target statements, extracted by script from the files (whitespace collapsed)
stKbound_timeIccgL (KDecayGen.lean):
  theorem stKbound_timeIccgL {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hN : sz.SizeTendsto) (hK : STKboundgL C μ) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
  (ht1 : ∀ n, t n < 1) : ∀ k : ℕ, 1 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (fun n p _ => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))
stKward_timeIccgL (KDecayGen.lean):
  theorem stKward_timeIccgL {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hN : sz.SizeTendsto) (hK : STKwardgL C μ) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
  (ht1 : ∀ n, t n < 1) : ∀ k : ℕ, 2 ≤ k → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n))) (fun n p _ => ∑ x : Zd d (sz.L n), ‖C.K n (p.1 : ℝ) p.2.1 (fun i : Fin k => if h : (i
  : ℕ) < k - 1 then p.2.2 ⟨i, h⟩ else x)‖) (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (k - 2))
SEforLnGen_Facts (SEforLnGen.lean):
  def SEforLnGen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L
  n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop := ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → (∃ E : ℕ → ℝ, StepDecompGen_LoopForm (mkM sz z) E) ∧ (∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf
  sz z n τ ω).IsHermitian) ∧ Step34Gen_LCompat (mkM sz z) (Hf sz z) ∧ Step34Gen_KCompat (mkM sz z) ∧ ZeroModeGen_WardCls sz (mkM sz z).toFlowFM ∧ (∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a
  b‖ ≤ 1) ∧ (∀ (n : ℕ) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1) ∧ (∀ (n : ℕ) (a b : Zd d (sz.L n)), (mkM sz z).S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) ∧ (∀ n : ℕ, ((mkM sz z).m n).im
  ≤ 1) ∧ ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)), (mkM sz z).K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg (mkM sz z) n σ
stSEforLnConclgL_of (SEforLnGen.lean):
  theorem stSEforLnConclgL_of {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz) (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (μ : Measure sz.SeqΩ)
  [IsProbabilityMeasure μ] (κm 𝔠 𝔡 Cd 𝔠d : ℝ) (E s t : ℕ → ℝ) (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E) (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ
  ω).IsHermitian) (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) (hcol : ∀ (n : ℕ)
  (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) (him : ∀ n : ℕ, (Cm.m n).im ≤ 1) (hone : ∀ᶠ n in atTop, ∀ u :
  ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)), Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ) (hCd : 0 < Cd) (h𝔠d : 0 < 𝔠d) (hcc : 𝔠d * Cd ≤ 1 / 30) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
  (ht1 : ∀ n, t n < 1) (hcon : sz.STConStInd 𝔠d s t) (hKw : STKwardgL Cm.toFlowFM μ) (hStep2 : STStep2ConclgL Cm.toFlowFM μ s t Cd) : STSEforLnConclgL Cm Hf μ s t
stSEforLngL_of (SEforLnGen.lean):
  theorem stSEforLngL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ →
  ℂ), Step2Mat sz) (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hlaw : ∀ sz : Sizes d,
  IsProbabilityMeasure (law sz)) (hflow : Step5CasesGen_FlowFacts d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hfacts : SEforLnGen_Facts d Flow mkM Hf) : STSEforLngL d R law Flow mkM Hf T0
stEtermDecaygL (SEforLnGen2.lean):
  theorem stEtermDecaygL (hd : 3 ≤ d) (sz : Sizes d) (Cm : Step2Mat sz) (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (κm 𝔠 𝔡
  : ℝ) (E s t : ℕ → ℝ) (hspec : DecayGen_Spec Cm.toFlowFM κm) (hA : sz.Admissible 𝔠 𝔡) (hloop : StepDecompGen_LoopForm Cm E) (hherm : ∀ (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ), (Hf n τ ω).IsHermitian) (hs0 : ∀ n, 0 ≤ s n) (hst
  : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hL : Step34Gen_LCompat Cm Hf) (hK : Step34Gen_KCompat Cm) (hrow : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1) (hsupp : ∀ (n : ℕ) (a b : Zd d (sz.L
  n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) (hone : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)), Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ) (hKb : STKboundgL
  Cm.toFlowFM μ) (hKcal : STKcalDecaygL Cm.toFlowFM) (hU : STDecayLoopUgL Cm.toFlowFM μ s t) : ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool, STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) => STegtg Cm Hf n
  (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧ (∀ l : ℕ, STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) => STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧ STEKDecaygL μ s t (m := k) (fun n v
  ω (a : Fin k → Zd d (sz.L n)) => STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧ STEKDecaygL μ s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) => STeeg Cm Hf n (v : ℝ) ω σ (fun i => b
  (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))
(`stSEforLn_part1g` ... `part4g` and `stEtermDecaygL_egt/_ksim/_elklk/_ee` carry the same hypothesis lists, conclusion = one conjunct; their statements are in the files.)

### B4. Statements against the `T2480_*` pins (check file, Part 2)
Compiled in the scratch file pins2.lean (= check-file Part 2 + the lines below): `example : T2480_KboundTimeIcc := @stKbound_timeIccgL`, `example : T2480_KwardTimeIcc := @stKward_timeIccgL`, `example (d) : T2480_SEforLnFacts d = SEforLnGen_Facts d := rfl`,
`example : T2480_SEforLngLOf := @stSEforLngL_of`, `example : T2480_SEforLnConclOf_supp := @stSEforLnConclgL_of`, `example : T2480_EtermDecaygL_one := @stEtermDecaygL`, and `example ... (h : <the four conjuncts of the bundle>) : T2480_EtermDecay Cm Hf μ s t k σ := h`.
$ lake env lean pins2.lean | grep -c error
0
Text diff of the two pins whose hypothesis list changed (`_supp`, `_one` = pin plus the one field of (a′) 1; everything else, conclusions included, identical):
$ diff T2480_SEforLnConclOf{,_supp}; diff T2480_EtermDecaygL{,_one}
9a10
>     (∀ (n : ℕ) (a b : Zd d (sz.L n)), Cm.S n a b ≠ 0 → zdistInf d (sz.L n) (a - b) ≤ 1) →
10a11,12
>     (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
>       Cm.K n u (fun _ : Fin 1 => σ) (fun _ => a) = STmsigg Cm n σ) →

### B5. Eterm decay against T2473's hypothesis (b)
Script: `git show t/T2473:RBM3D/Chain/GridGoodGen.lean` (commit 21dafaa9), `hEK` of `gridGoodNConclg_of` (line 816), against the conclusion of `stEtermDecaygL`, whitespace-normalised: equal = True

### B6. Compiled nonempty instances and band re-derivations (`example`s; deterministic premises discharged, Step 2 outputs `hStep2`/`hU` stay hypotheses)
KDecayGen.lean:208 example  The index set of the instances is nonempty at every size index: th
KDecayGen.lean:213 example  `stKbound_timeIccgL` at the band carrier, `d = 3`, `sz0`, `[0, 1/16]`
KDecayGen.lean:223 example  `stKward_timeIccgL` at the band carrier, `d = 3`, `sz0`, `[0, 1/16]`
KDecayGen.lean:236 example  The band re-derivation `stKbound_timeIcc_gen_band` at the same dat
SEforLnGen.lean:1567 example  Band `stSEforLn_part1` (`SEforLn1:466`) re-derived from `stSEforLn
SEforLnGen.lean:1579 example  Band `stSEforLn_part2` (`SEforLn1:702`) re-derived from `stSEforLn
SEforLnGen.lean:1599 example  Band `stSEforLn_part3` (`SEforLn2:1007`) re-derived from `stSEforL
SEforLnGen.lean:1624 example  Band `stSEforLn_part4` (`SEforLn2:1264`) re-derived from `stSEforL
SEforLnGen.lean:1638 example  Band `STSEforLn d`
SEforLnGen.lean:1667 example  The index set of the instances is nonempty at every size index (wi
SEforLnGen.lean:1672 example  Target 3 (`SEforLnGen_Facts`) at the band flow `(sz0, z0)`
SEforLnGen.lean:1688 example  Target 4 (`stSEforLnConclgL_of`) at `(sz0, z0, [0, 1/16])`
SEforLnGen.lean:1705 example  Target 5 (`stSEforLngL_of`) at the band family, `d = 3`, regime `STAny`
SEforLnGen.lean:1712 example  The same pin at the regime `STCaseI` (the proof reads no regime). 
SEforLnGen2.lean:909 example  Band `stEtermDecay`
SEforLnGen2.lean:946 example  Target 6 at `(sz0, z0, [0, 1/16])`, `k = 2`

### B7. Greps
$ grep -n '^import RBM3D.BA' RBM3D/Chain/KDecayGen.lean RBM3D/Chain/SEforLnGen*.lean
(exit 1: no match)
$ importers of KDecayGen / SEforLnGen / SEforLnGen2
RBM3D/Chain/SEforLnGen.lean RBM3D.lean
RBM3D/Chain/SEforLnGen2.lean RBM3D.lean
RBM3D.lean
$ U-C4: grep -nE "^(noncomputable )?(private )?def" <new files>   # a Prop class, two private Props, one private Finset; no kernel
RBM3D/Chain/SEforLnGen.lean:57:def SEforLnGen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ)
RBM3D/Chain/SEforLnGen.lean:823:private def SEforLnGen_SumOK (Cm : Step2Mat sz) (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → M
RBM3D/Chain/SEforLnGen.lean:1224:private def SEforLnGen_nbhd {L : ℕ} [NeZero L] (x : Zd d L) : Finset (Zd d L)
RBM3D/Chain/SEforLnGen2.lean:368:private def SEforLnGen2_Good (C : FlowFM sz) (s t : ℕ → ℝ) (K : ℕ) (τ' D'' : 
RBM3D/Chain/SEforLnGen2.lean:411:private def SEforLnGen2_KDec (C : FlowFM sz) (K : ℕ) (τ D : ℝ) (n : ℕ) : Prop
$ TN-C4 grep (STGridRepNgL|ST_gridMart_of_repN) counts; UBA-C1 grep (gK) counts
RBM3D/Chain/KDecayGen.lean:0 RBM3D/Chain/SEforLnGen.lean:0 RBM3D/Chain/SEforLnGen2.lean:0
RBM3D/Chain/KDecayGen.lean:0 RBM3D/Chain/SEforLnGen.lean:0 RBM3D/Chain/SEforLnGen2.lean:0
$ name-clash grep -rnw <18 new public names> RBM3D (hits outside the three files; the other 15 names: 0 hits)
RBM3D/Test/Axioms.lean:195:   `RBM.BA.STKcalDecaygL, -- the far decay of
RBM3D/Test/Axioms.lean:222:   `RBM.BA.STAvgUgL, -- `(Gt_avgbound_flow)` 
RBM3D/Test/Axioms.lean:223:   `RBM.BA.STStep2ConclgL, -- the three Step 
RBM3D/Chain/Step34Gen.lean:515:T7/U2 (`stEtermDecaygL`) read it unchange
per-name hit counts in the order of B2: 0 0 0 0 0 0 0 1 0 0 0 1 0 0 0 0 0 2
Those hits are registry comment text (`Test/Axioms.lean`) and the planned-name docstring `Chain/Step34Gen.lean:515`, no declaration. Ports: none from RBM1D/RBM2D (nothing copied from outside this repository); the restated proofs are from the RBM3D band files `SEforLn1/2`, `DecayLoopB`, `KDecay`, `Contract`.
$ git diff --stat main...t/T2480
 RBM3D.lean                   |    3 +
 RBM3D/Chain/KDecayGen.lean   |  244 ++++++
 RBM3D/Chain/SEforLnGen.lean  | 1718 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/SEforLnGen2.lean |  975 ++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean       |    5 +-
 5 files changed, 2944 insertions(+), 1 deletion(-)
$ G1: git diff main...t/T2480 -- RBM3D/Induction RBM3D/Loop RBM3D/BA and the merged Chain files | wc -l
       0

### B8. X1-C1 grep: hits classified by region (band bridge/discharge, band re-derivation, band instance, doc)
$ python3 x1c1.py <the three files>   # pattern of the ticket; each matching line classified by the enclosing declaration or region
KDecayGen.lean     band bridge/discharge 11, band instance 12, doc 4   (no OTHER hit: none in a generic statement or proof)
SEforLnGen.lean    band bridge/discharge 13, band instance 24, band re-derivation 38, doc 7   (no OTHER hit: none in a generic statement or proof)
SEforLnGen2.lean   band instance 17, doc 1, false positive (substring of hlam0) 2   (no OTHER hit: none in a generic statement or proof)

### B9. Shared files and registry (`git diff main...t/T2480 -- RBM3D.lean RBM3D/Test/Axioms.lean`, changed lines)
$ git diff main...t/T2480 -- RBM3D.lean RBM3D/Test/Axioms.lean | grep "^[+-]"
+import RBM3D.Chain.KDecayGen
+import RBM3D.Chain.SEforLnGen
+import RBM3D.Chain.SEforLnGen2
-   `RBM.BA.STKcalDecaygL, -- the far decay of `𝒦` over a flow carrier, without the energy (`Chain/DecayGen.lean`): hypothesis of `stDecayLoopAtgL_of`, `stDecayLoopP
+   `RBM.BA.STKcalDecaygL, -- the far decay of `𝒦` over a flow carrier, without the energy (`Chain/DecayGen.lean`): hypothesis of `stDecayLoopAtgL_of`, `stDecayLoopP
+   -- T2480 (BA-U U2a, DECISIONS §280): the Step 2 outputs that the public theorems of `RBM3D/Chain/SEforLnGen.lean` take as hypotheses and nothing concludes
+   `RBM.BA.STAvgUgL, -- `(Gt_avgbound_flow)` uniformly in `u ∈ [s,t]` over a flow carrier (`Chain/Step2Gen.lean:487`): hypothesis of `stSEforLn_part1g` (T2480); ban
+   `RBM.BA.STStep2ConclgL, -- the three Step 2 conclusions that Steps 3-4 consume (`STLocalEntryUgL ∧ STAvgUgL ∧ STGdecayWgL`, `Chain/Step2Gen.lean:499`): hypothesi
Premise scan before the two `STAvgUgL`/`STStep2ConclgL` lines (tool log of the first full build): `error: RBM3D.lean:555:0: axiom audit: 2 premise(s) that no theorem of this development proves are in none of ...: [RBM.BA.STStep2ConclgL, RBM.BA.STAvgUgL]`; with the lines B1 shows the build passing.

### B10. C6 (supervisor 1155 `:182-187`)
f_sem of `KDecay`: (a) row 17 (`fsem.py`): whole file 0.230; §1-§8 0.329 (not restated here: the premise `STKcalDecaygL`, the planned U2-BA twin); outside §1-§8 0.000 (§9 restated in `KDecayGen`; §10-§11 not needed).
$ grep -cE "KLtreeValW|KLSigmaPi|kTwo|KLIsTSP|KLK_two|KLnodes|TSP" SEforLn1 SEforLn2 B45 <the new files>
Induction/SEforLn1.lean:0 Induction/SEforLn2.lean:0 Induction/B45.lean:0 Chain/KDecayGen.lean:0 Chain/SEforLnGen.lean:0 Chain/SEforLnGen2.lean:0
REQ test of the ticket (this row + U2-BA twin 937 against 1.5 x 2,250 = 3,375): U2a alone 2,937 + 937 = 3,874; with the 1a's `B45Gen` 1,075: 4,949.

### Narrative
- Delivered: U2a = targets 1-6 and their part of 10-11. `KDecayGen` (target 1; the class-(t) segment of `KDecay` is not restated, C6), `SEforLnGen` (targets 3-5, parts (1)-(4), band re-derivations and instances), `SEforLnGen2` (target 6; reserve file: `SEforLnGen` + target 6 = 2693 lines > 1,800). Targets 7-9 (`B45Gen`, U2b) are not in this delivery.
- Method: the deterministic cores of `SEforLn1/2` and `DecayLoopB` §7-§9 are restated over `Cm : Step2Mat sz`, `Hf`, `μ` with the band objects replaced as in (a′) and the file header; the facts reach them through private bundles `SEforLnGen_Hyp`, `SEforLnGen2_Hyp` whose fields are the public hypotheses (no new public `Prop`).
- Loop form -> `stContractM_holds` at `ztOf (Cm.m n) (E n) τ` (`SEforLnGen_contract1/2`); `ZeroModeGen_WardCls` -> rotation of `𝒦` (`SEforLnGen_KI_rotate`); row/column sums of `‖S‖` -> the glue sums; `Im m ≤ 1` -> `η ≤ 1 - u` in `(eq:sumtwoloop)`.
- Part (4): the support is in `|·|_∞` (class field), so the neighbourhood has at most `3^d` points (`DecayLoopB_card_ball`, `R = 1`) instead of `2d + 1`; the constant is absorbed by `N^τ`.
- Target 6: `Γ = 1 + κm⁻¹` replaces `2/√κ`; `STKcalDecaygL` replaces `inst_stKcalDecay_admissible`; the good event is `STDecayLoopUgL` and `stKbound_timeIccgL` through `HighProbAt.inter/biInter`; the four theorems differ only in the conjunct taken.
- Band private lemmas are reused by `open private` (SEforLnGen: 24 names, SEforLnGen2: 14; counted by script from the `open private` lines); the ones mentioning band objects are restated under the stems `SEforLnGen_`, `SEforLnGen2_`.
- `hspec : DecayGen_Spec` of target 4 is unused by the proof (the loop form already gives `0 < Im m` and `η`); kept so that the statement is the pin plus (a′) 1.
- Registry: owner text of `STKcalDecaygL` and two new lines (`STAvgUgL`, `STStep2ConclgL`, owner T1 / T1-BA); no T2473 lines for `STSEforLngL`, `STSEforLnConclgL`, `STEKDecaygL` exist on main (this row concludes them).

## (c) Verified Mathlib names (all `#check`ed in the scratch file names.lean on the branch; 18 of 18 resolve)
`Finset.sup'_congr`, `Finset.single_le_sum`, `Finset.sum_subset`, `Filter.eventually_all_finset`, `Filter.eventually_all`, `MeasureTheory.measure_univ`, `MeasureTheory.measure_mono`, `ENNReal.ofReal_lt_one`, `inv_lt_one_of_one_lt₀`, `inv_anti₀`, `Real.rpow_neg_one`, `Real.one_le_rpow`,
`mul_le_of_le_one_left`, `mul_le_mul_of_nonneg_left`, `Nat.cast_nonneg`, `Nat.card_Icc`, `Fintype.card_coe`, `List.rotate_cons_succ`. Verified absent: none needed.

## (d) Open issues and paper-delta candidates
1. Pin shapes (a′) 1: the check file's `T2480_SEforLnConclOf` lacks the `support` hypothesis, `T2480_EtermDecaygL` the `hone` hypothesis; both are fields of `SEforLnGen_Facts`, the class hypothesis of target 5. The band proofs use them (`SEforLn2_SB_sum`, `DecayLoopB_avgErr_eq`) and I found no proof without them; no negative statement was compiled (a counterexample needs a `Step2Mat` instance). Dispatcher: confirm the two additions.
2. C6 REQ test (B10): this row's U2a already gives 3,874 against 3,375 with the U2-BA twin; the ticket's rule asks for a report (amend G3), REQ only past the 1.5x line, which is passed.
3. T1a merged on main (`6039f7ed`, committed 2026-10-13 00:40:56 UTC) during this 1b (its first command ran at 2026-10-13 00:20:44 UTC); `Chain/Step2IterGen.lean` with `Step2IterGen_OneLoop` is now on main.
       Answer (3) fixed the choice at the start of the 1a (inline), so `hone` is the inline exact-type conjunct (`STmsigg Cm n σ` unfolds to the `if σ then m else conj m` of its first conjunct); a one-line bridge could switch to the class later.
4. `RBM3D.lean` (3 import lines) and `RBM3D/Test/Axioms.lean` (the `STKcalDecaygL` owner text and 2 lines before `STExp2U`) were also changed on main since `d1eb95ac` (`git diff --stat d1eb95ac main`: RBM3D.lean             |  5 +++++ / RBM3D/Test/Axioms.lean | 12 ++++++++++--): the hub unions these lines at merge.
5. U2b (`B45Gen`, targets 7-9 and their part of 10) is not delivered here; it imports `KDecayGen` and stacks on this branch.
6. Paper-delta candidates: `T2480a` (`lem:SEforLn` and the Eterm decays over the carrier, with the `𝒦` rotation, the `S` facts and the one-loop value as carrier inputs, the far decay of `𝒦` as a model premise); `T2480b` (the support of `S` is used in `|·|_∞`: at most `3^d` neighbours instead of `2d + 1`, absorbed by `N^τ`).
