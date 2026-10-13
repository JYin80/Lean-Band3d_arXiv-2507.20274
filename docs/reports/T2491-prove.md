Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 06:16:53 UTC 2026
Stage 1a design gate D1-D5 of T2491 (mathematics only; no Lean written). Tree: worktree `t/T2491` = `main` 7be99aae. `S` = scratchpad `T2491/` (python3+numpy: `kerD1.py`, `expo.py`, `thresh.py`, `size.py`, `census{2,3,4}.py`, `hand.py`). `d=3`; band = `bandFM`, `gK=sz.lam`; BA = `baFMz`, `gK=BAflowLam0`, `z=0.3+i`; `A` = R1 constant; `szB` = `L=4, W_n=n+4, lam=1` (T2484-prove (ii) data); flow `(κ,ε,𝔠,𝔡)=(1/10,1/10,1/6,1/10)`; `e0=ε₀'=1/2`.
Math fixed here. **(M1)** `ekSumDecayNAL_holds` (SumDecay:420) and BA `baEKSumDecayNAL_holds` (EKSum:290) put `∃ C` before `(L,g,W,ε,D,s,t,m,σ,A)`, `C` depends on `(d,k,Λ,κ)` only: this is the `∃ Ck` slot of `T2491_KerNALFam`. **(M2)** R1: `ℓ_lam ≤ √A ℓ_gK` (Step34Gen:741), `r_gK^{k-1} ≤ A^{k-1} r_lam^{k-1}` (:711); the ℓ∞ clause of `GoodSetNg` at `lam` gives `EKFastDecay gK s W ε D` iff `d√A·W^{τ'} ≤ W^ε`, and `hker_of_case1Ng` at `lam` carries `A^{k-1} ≤ W^{ε'}`, so the vocabulary constant is `Ck_voc ≥ Ck + ε'/ε` (band `A=1`: `ε'=0`, `Ck_voc=nqGood1C`, exact bridge; BA: `ε'=ε`, `Ck_voc=Ck+1`). **(M3)** `ztOf m E u = E+(1-u)m` (GLoopFlow:55): `‖z_u-z_u'‖=|u-u'|‖m‖`, `η_u=(1-u)Im m`; the shift layer (NQGood1:718-760) needs only `‖m‖≤1` (so `Im m≤1`, `η≤1`) and `0<Im m` (LoopForm). **(M4)** `gridDriftNg_envelope` (GridEnvelopeGen:62) uses `hGD` only at the index `n` of its last `filter_upwards` (:123), so `hGD` may be `∀ᶠ n`; `hKK`, `hη` stay `∀ n` (BA: `HierDriftGen_KLink` unguarded; `η=(1-v)Im m∈(0,1-v]`).
### (i) Exponent table (values from the outputs in (ii); `k=2` unless stated)
| # | quantity | constraint | value / slack |
|---|---|---|---|
| 1 | `Ck` of D1 (`∃` before `(sz,z)`; band `nqGood1C d k 𝔡⁻¹ min κ 4/5`, NQEndLin:1105; BA `baEKSumDecayNAL_holds d k 𝔡⁻¹ κ`) | `Ck ≥ Ck_need` at the data | least valid `Ck` at finite L, E=0: band 0 / 0.82 / 2.20 and E=1.9: 0.11 / 1.11 / 1.49 at g=1/64, 1, 10; BA 0 / 0 / 0.51; EK-6 gives `C=m'+2k-2≥2` (SumDecay:427); the g=10 band needs ≥ 2.198 |
| 2 | `Ck_voc` (NQGood2 vocabulary) | `Ck_voc ε ≥ Ck ε + ε'`, `A^{k-1} ≤ W^{ε'}` | band `nqGood1C` (`ε'=0`); BA `Ck+1` |
| 3 | `ε = min(e0/(8 Ck_voc), 1/2)`, `Ck_voc ε ≤ e0/8` | `0<ε<1` | 0.0208 (`Ck_voc=3`), 0.0156 (`=4`); `Ck_voc ε = e0/8` by definition (slack 0); E1 slack 0.375 |
| 4 | `τ'=ε/2`; crossing `d√A W^{τ'} ≤ W^ε` | `log10 W ≥ (2/ε) log10(d√A)` | band 45.8; BA 88.1 / 99.7 / 147.9 (g=1/64, 1, 10): eventual only |
| 5 | `A^{k-1} ≤ W^ε` (k=4) | `log10 W ≥ (3/ε) log10 A` | band 0; BA 80.9 / 115.8 / 260.4: eventual only |
| 6 | `4 ≤ W^ε` (EK-6) | `log10 W ≥ log10(4)/ε` | 28.9 (band), 38.5 (BA): eventual only |
| 7 | `D''=Ck_voc+k+2+(4k+2)/𝔠`, `D'=D''+1` | `k+1<D''` | 67 / 68 (k=2), 92 / 93 (k=3); slack `D''-(k+1)` = 64 / 88 |
| 8 | NQEndArith E1-E4, F1-F3, G1-G3, H1-H2 (NQEndLin:662-683) | 18 inequalities, plus `0<ε<1`, `Ck ε ≤ e0/8` | all 20 hold at (k,Ck_voc) = (2,3), (3,3), (2,4); tightest after the definitional equality: `0<ε<1` slack 0.016-0.021, then E2/E3 slack 0.312 |
| 9 | `C_K = D₁+2C_P*+6k+20+D''` (`D₁=3`, `C_P*=4` placeholder) | `hC1`-`hC6` (NQEndLin:1147-1156; `sum_weighted_stepErrNg_le` rows) | 110 (k=2), 141 (k=3), 111 (BA k=2); all hold |
| 10 | `𝔠_d = min(𝔠G, 𝔠L, 1/(2d))`, `𝔠G,𝔠L ≤ 1/100` | `d 𝔠_d < 1` (`st_window`, NQEndFlow:941) | `𝔠_d ≤ 1/100 ≤ 1/6`; `d 𝔠_d ≤ 0.030` |
| 11 | R1 `A = Aof κ` | `1≤A`, `gK²≤lam²≤A gK²` | band 1; BA `(κ+1)/κ = g²/g0²` exactly: 2.640 / 4.008 / 22.711 (L=32, Im z=1) |
| 12 | D3 `‖m‖≤1` | `Im m≤‖m‖≤1` | band 1 (equality); BA `‖m0‖` = 0.9997 / 0.667 / 0.220 |
| 13 | D2 exponent `2k+2` (NQEndFlowLift:588, 674) | `k+4 ≤ 2k+2`; `(1-t)⁻¹ ≤ N` | slack `k-2` (0 at k=2); `62.5 ≤ 4096` (n=0, T0 of zB) |
| 14 | `RangeCond τ=ε/2` | `N^{-1+τ} ≤ 1-T0` | `3.7e-4 ≤ 1.6e-2` (43×, n=0); `5.4e-11` at n=1000 |
| 15 | window `W⁻¹ ≤ (1-t)/(1-s)`, `t ≤ 1-gK²/L²` | for every `(s,t)` of D1's grid | asserted in `kerD1.py` (35 windows per case); `gK²/L²` ≤ 0.098 |
| 16 | `WO`, `Bandwidth` at szB | `W^{-d/2+𝔡}≤lam≤𝔡⁻¹`, `N^𝔠≤W` | `0.1436 ≤ 1 ≤ 10`; `N^{1/6}=4.000 ≤ W=4` (equality, n=0); 0 violations n≤1999, 1e4, 1e6 |
### (ii) One concrete nondegenerate instance
Data: `d=3`, `k=2`, `σ=(+,+)` (non-alternating). D1 kernel at `L=32` (torus, FFT), `W=5, ε=9/10, D=2, κ=1/10` (`4 ≤ W^ε=4.257`); band `E=0, 1.9` (`|E|≤2-κ`), BA `z=0.3+i`, `g=1/64, 1, 10` (`g0<g`); `(s,t)` on a 5×7 grid with `0≤s≤t≤min(1-gK²/L², 1-(1-s)/W)` (asserted). `Ck_need = ln((Σ|u|)²/r)/(ε ln W)` is the least `Ck` for which D1's bound holds for every `‖A‖≤1` (second term dropped), `u=(1-sX)/(1-tX)`, `r=(gK²+1-s)/(gK²+1-t)`. Exponent bookkeeping: `Ck_voc ∈ {3,4}`, `k∈{2,3}`. Eventual hypotheses (`Admissible`, `STConStInd`, R1 crossings, `RangeCond`): the limit lines of `thresh.py` (`T0=0.98399229` copied from T2484-prove (ii)). Other gates' pins (`STSEforLngL`, `STKcalDecaygL`, `STStep2ConclgL`, `STLKgL`, `STKboundgL`, `IsProbabilityMeasure`) stay hypotheses of the example.
`$ cd $S && python3 kerD1.py && python3 expo.py && python3 thresh.py` (output; long lines kept)
```
data: d=3 L=32 W=5.0 eps=0.9 D=2.0 (4<=W^eps: 4.257), kappa=0.1; sigma=(+,+) (nonalternating), k=2
BAND X=m(E)^2 SB(g), gK=g=lam:
  band E=0.0 |m|=1.000 Im m=1.000 (D3)         gK= 0.0156 gK^2/L^2=0.0000 max Ck_need=0.000 @(s,t)=(0.9,0.90) (sum|u|)^2=1.000 r=1.000 [35 windows]
  band E=0.0 |m|=1.000 Im m=1.000 (D3)         gK= 1.0000 gK^2/L^2=0.0010 max Ck_need=0.817 @(s,t)=(0,0.80) (sum|u|)^2=5.444 r=1.667 [35 windows]
  band E=0.0 |m|=1.000 Im m=1.000 (D3)         gK=10.0000 gK^2/L^2=0.0977 max Ck_need=2.198 @(s,t)=(0,0.80) (sum|u|)^2=24.347 r=1.008 [35 windows]
  band E=1.9 |m|=1.000 Im m=0.312 (D3)         gK= 0.0156 gK^2/L^2=0.0000 max Ck_need=0.105 @(s,t)=(0,0.40) (sum|u|)^2=1.939 r=1.666 [35 windows]
  band E=1.9 |m|=1.000 Im m=0.312 (D3)         gK= 1.0000 gK^2/L^2=0.0010 max Ck_need=1.114 @(s,t)=(0,0.80) (sum|u|)^2=8.364 r=1.667 [35 windows]
  band E=1.9 |m|=1.000 Im m=0.312 (D3)         gK=10.0000 gK^2/L^2=0.0977 max Ck_need=1.492 @(s,t)=(0,0.80) (sum|u|)^2=8.752 r=1.008 [35 windows]
BA z=0.3+i, X=M.M entrywise, M=(g0 Psi-Ef-m0)^-1, gK=g0:
  BA g=0.0156 g0=0.0096 A=2.640=g^2/g0^2:True |m0|=1.000 Im m0=0.991>=kap=0.610:True gK= 0.0096 gK^2/L^2=0.0000 max Ck_need=0.000 @(s,t)=(0.9,0.90) (sum|u|)^2=1.000 r=1.000 [35 windows]
  BA g=1.0000 g0=0.4995 A=4.008=g^2/g0^2:True |m0|=0.667 Im m0=0.666>=kap=0.332:True gK= 0.4995 gK^2/L^2=0.0002 max Ck_need=0.000 @(s,t)=(0.9,0.90) (sum|u|)^2=1.000 r=1.000 [35 windows]
  BA g=10.0000 g0=2.0984 A=22.711=g^2/g0^2:True |m0|=0.220 Im m0=0.220>=kap=0.046:True gK= 2.0984 gK^2/L^2=0.0043 max Ck_need=0.506 @(s,t)=(0,0.80) (sum|u|)^2=2.443 r=1.174 [35 windows]
k=2 Ck_voc=3.0: eps=0.0208 tau'=0.0104 D''=67.00 D'=68.00 C_K=110.00 all 20 hold: True; tightest: Ck*eps<=e0/8 slack 0.000; 0<eps<1 slack 0.021; E2 slack 0.312; E3 slack 0.312
k=3 Ck_voc=3.0: eps=0.0208 tau'=0.0104 D''=92.00 D'=93.00 C_K=141.00 all 20 hold: True; tightest: Ck*eps<=e0/8 slack 0.000; 0<eps<1 slack 0.021; E2 slack 0.312; E3 slack 0.312
k=2 Ck_voc=4.0: eps=0.0156 tau'=0.0078 D''=68.00 D'=69.00 C_K=111.00 all 20 hold: True; tightest: Ck*eps<=e0/8 slack 0.000; 0<eps<1 slack 0.016; E2 slack 0.312; E3 slack 0.312
c_d<=1/100 <= 1/(2d)=0.1667: d c_d <= 0.030 < 1 (st_window)
instance data: d=3 szB: L=4, W_n=n+4, lam=1, N_n=(4 W_n)^3; flow (kappa,eps,c,dd)=(1/10,1/10,1/6,1/10); e0=eps0'=1/2; Ck=3
  band  A=1        C=3.0 eps=0.0208: log10 W thresholds: d*sqrtA*W^(eps/2)<=W^eps   45.8; A^(k-1)<=W^eps (k=4)    0.0; 4<=W^eps  28.9
  BA g=1/64 A=2.640 C=4.0 eps=0.0156: log10 W thresholds: d*sqrtA*W^(eps/2)<=W^eps   88.1; A^(k-1)<=W^eps (k=4)   80.9; 4<=W^eps  38.5
  BA g=1    A=4.008 C=4.0 eps=0.0156: log10 W thresholds: d*sqrtA*W^(eps/2)<=W^eps   99.7; A^(k-1)<=W^eps (k=4)  115.8; 4<=W^eps  38.5
  BA g=10   A=22.71 C=4.0 eps=0.0156: log10 W thresholds: d*sqrtA*W^(eps/2)<=W^eps  147.9; A^(k-1)<=W^eps (k=4)  260.4; 4<=W^eps  38.5
WO (W^{-d/2+dd}<=lam<=1/dd), Bandwidth (N^c<=W), n<=1999 and 1e4,1e6: violations [] ; n=0: N^c=4.000<=W=4
  n=0: 1-T0=1.6008e-02 >= N^(-1+eps/2)=3.700e-04 (RangeCond tau=eps/2); (1-T0)^-1=62.5 <= N=4.096e+03 (D2 htN); lam^2/L^2=0.0625<=1-t for t<=T0
  n=1000: 1-T0=1.6008e-02 >= N^(-1+eps/2)=5.360e-11 (RangeCond tau=eps/2); (1-T0)^-1=62.5 <= N=6.477e+10 (D2 htN); lam^2/L^2=0.0625<=1-t for t<=T0
```
### Decisions D1-D5 (mathematics; texts of the check file are kept unless stated)
**D1 PASS, text `T2491_KerNAL`/`T2491_KerNALFam` unchanged** (the per-index class has no `0<gK n≤Λ` or `3≤L` hypothesis, so it is used only inside `∀ᶠ n`). Sources: band (M1) with `Ck = nqGood1C` and `Step2Gen_UN (bandFM sz E) = Ugen` (GridDuhamelGen:181); BA `baEKSumDecayNAL_holds` (EKSum:290) at `g=BAflowLam0` via `Step2Kern_UN_BA` (Step2Kern:124), `BAflow_real` (GreenSchur:59), `BAflow_lam0_window` (:72): no missing BA source. **A1:** the scan needs a band theorem with head `NQGoodGen_KerNAL` (`..._band_at`) next to the one for `..._Fam`. **A2:** (M2).
**D2 PASS, text `T2491_KLip`/`KLipFam` unchanged**: it is the conclusion of `stKloop_lip` (NQEndFlowLift:581) with `STKloop` read as `C.K`; hypotheses come from `v3_premises_of_stFlow` (Pins:1049: `|E|<2-κ/2`, `t<1`, `RangeCond (ε/2)`, hence `(1-t)⁻¹≤N`). Premise of no target here; BA twin = U3-BA (`BAKsol_isKLoopS` KSolve:606, `baKbound_holds` KBound:245).
**D3 PASS, inline `∀ n, ‖Cm.m n‖ ≤ 1`**, no name, no registry line; band `norm_mE`, BA `ba_G_data` (GreenLDE:55) + `BAm_norm_le_one` (Ward:136); `EMn2BA_mF_data` (EMn2BA:125) gives `κ ≤ Im m ≤ 1`.
**D4:** lift dropped (no reader outside `NQEndFlow*`: `grep "OeqNQ''"` over `RBM3D/` outside it finds only the superseded note Axioms:406); `nqFlowSharp` by name. Scope in the table below; sizes in (xii): three rows kept.
**D5 PASS (new, A3):** `gridDriftNg_envelope_ev` = `gridDriftNg_envelope` with `hGD : ∀ᶠ n, GridDriftNgAt Cm s t K n` (`GridDriftNgAt` = the body of `GridDriftNg` at `n`: HierDriftGen:628-640 after `∀ n`), same conclusion; concluder `gridDriftNgAt_of_classes` from `gridDriftNg_at` (HierDriftGen:818); merged form = `Eventually.of_forall`. Only reader: `nqEndLin_assembly` (NQEndLin:816), so it lives in `NQEndLinGen`. Row-9 premises then read `∀ᶠ n, KLoop ∧ KTwo ∧ UStep`, `∀ᶠ n, ∀ s t K, Expand`, `∀ n, KLink`, row sums `∀ n` (`S=1` at BA).
### Fill-in table (CONTROL H250 (4))
| item | content |
|---|---|
| (i) | the exponent table above (16 rows) |
| (ii) | the instance and scripts above (band E=0, 1.9 and BA g0<g, g=1/64, 1, 10) |
| (iii) | fact → field → band discharge → BA: EK-6 + `nqGood1C` (NQGood1:261, 310) → `∃ Ck` of KerNALFam → `nqGoodGen_kerNAL_band` (`nqGood1_mE_im_ge` NQGood1:404, `bandStep2_Ugen`) → `baEKSumDecayNAL_holds` + `BAflow_real`; R1 `A=1` → `T2491_R1Fam` (inline) → `TwistStep2_lam0_sq` (TwistStep2:740); `stKloop_lip` → KLipFam → U3-BA twin; `norm_mE` → D3 → `BAm_norm_le_one`; `gridDriftN_envelope` → D5 → T2492 classes `∀ᶠ n`; `v3_premises_of_stFlow` → `∃ τ>0, RangeCond τ (T0 sz z)` → `EMn2BA_one_sub_T0` (EMn2BA:111) |
| (iv) | D1 decided (A1, A2); probe lines (≤400): D1/D2/D3/D5 texts and band discharges at szB/zB ≈160, BA readings ≈60, one `hker_of_case1Ng` instance ≈120, scan ≈40 |
| (v), (vi) | D2, D3 decided (above) |
| (vii) | rows 1-12 checked against the statements: 1 `STSEforLngL` (Step34Gen:404) pin; 2 `Step2EventsGen_Flow` (Step2EventsGen:68; `Step2EventsGenTw_baFlow` :53); 3-4 `stepDecompGen_loopForm_band`/`_walkForm_band` (StepDecompGen:459, 465); 5 `Step2EventsGenTw_baLaw` (:63), `bandStep34_LCompat` (Step34Gen:194); 6 `DecayGen_bandSpec` (DecayGen:142), κm=√κ/2 band, κ BA; 8 `gridRepTailGen_ker_BA` (GridRepTailBA:60); 9 `hierDriftGen_*_band` (HierDriftGen:1197-); 10 EK-6 / R1; 11 `RangeCond`; 12 `DecayGenTw_baWardPair` (:44). Pinned `∃` before `(sz,z)`: `𝔠d`, `Ck`, `Aof κ`; `κm` only feeds proofs; `ε₁ τ' D' C_K` stay after the carrier (they use the carrier's `C_P*`) |
| (viii) | decls of the band files (script `hand.py`): regenerated 20 / 21 / 13 / 23 / 9 / 17 (NQGood1 / 2 / Budget / Lin / EndLin / EndFlow; 580 / 471 / 678 / 778 / 647 / 479 lines); reused by name: `loopShiftErrN`, `norm_loopL_zshiftN_le`, `loopMax_zshiftN_le`, `nqGood1_ellT_mono`, `nonAltClsN`, `nqGood2_ratio_mul_Bctl_le`, `nqLinPhi1-3`, `nqFlowLam/PhiC/Sharp`, scalar `nqBudget_*`; band only: `UgenPairN`, `nqGood1C`, `nqGood1_mE_im_ge` (discharge), the 4 `zt`/`etaT` helpers (replaced by a 3-line private lemma), the lift, the §2 bridges of NQEndFlow |
| (ix) | UBA-C1 as planned: R1 enters only in `hker_of_case1Ng` ((a) `winK_of_cmp` Step34Gen:683, (c) `ratio_pow_le` :711, ℓ-crossing :785; (e) `decayK_of_cmp` :805 for the ℰ-decays) and, via row 10, target 14; targets 3-13, 15 never |
| (x) | scan preview: new Prop defs assumed by public theorems = `NQGoodGen_KerNAL`, `..._Fam` (A1), `GridDriftNgAt` (concluder above); `NQLinGoodgL`, `STOeqNQPTgL''` are concluded here; `T2491_HQg`, `KLip(Fam)`, the 9 other R2* texts are assumed by no public theorem here; rows 1-12 are concluded by the merged theorems of (vii) or registered (`STSEforLngL` Axioms:235, `STKcalDecaygL` :195, `STStep2ConclgL` :232, `STLKgL` :135, `STKboundgL` :134); expected new `owedProps` lines: 0; edit the owner text of `GoodSetNg` (Axioms:237, "(U3s2-U3s3)" → `hQ_nonAltNg` concluded); `stOeqNQ''_holds` is not named in `Test/Axioms.lean` |
| (xi) | `open private` (model-free privates, both regexes): NQGood1 9 decls / 179 lines, NQGood2 3 / 38, NQBudget 5 / 59, NQLin 20 / 226, NQEndLin 25 / 398, NQEndFlow §4 12 / 144 (`nqFlow_lam_sqrt` … `four_pow_le`); **finding F1:** the other 2 of the 14 privates of NQEndFlow:337-585 are band-specific (`nqFlow_one_le_STXiL` :348 copied with `STXiLg`; `nqFlow_hQ` :430 regenerated); GridGoodGen `_precL_whp`, `_whp_uniform`, `_grid` (:510, 543, 727); names at the 1b start |
| (xii) | next block |
| (xiii) | `git grep -w -F` of 57 final names (six modules, D1/D2/D5 names and band theorems, the `g`/`gL` vocabulary, the ten R2* texts, `stOeqNQPTgL''_of`) on `main` 7be99aae, `t/T2482b`, `t/T2484b`, `t/T2486`, `t/T2489`, `t/T2490`, `t/T2492`, `t/T2491`: 0 hits; no `NQ*Gen*` file in `RBM3D/Chain` of `main` or `t/T2492` |
### (xii) Lines per file, split, C6 (`python3 $S/size.py`; ticket formula `1.24(0.85B+0.6P+0.05M)` on this census with the X1-C1 regex / widened by the band classes; central = regenerated band lines (docstrings included) ×1.05 + itemised extras + 80 header)
```
file          band nonInst  ticket formula pure/wide regen*1.05 extras  hdr  CENTRAL x1.38 hi   x2.6
NQGood1Gen            1054     810      722/751             609    215   80      904     1248   2350
NQGood2Gen             611     360      356/471             495    155   80      730     1007   1898
NQBudgetGen            858     620      696/708             712     60   80      852     1176   2215
NQLinGen              1238     900      688/874             817    160   80     1057     1459   2748
NQEndLinGen           1276     700      818/844             679    220   80      979     1351   2545
NQEndFlowGen           954     710      460/586             503    255   80      838     1156   2179
total                         4100     3740/4234                                5360
row U3s2a: 1634 (cap 1950, headroom 316); ticket-formula rows 1078-1222
row U3s2b: 1909 (cap 1950, headroom 41); ticket-formula rows 1384-1582
row U3s2c: 1817 (cap 1950, headroom 133); ticket-formula rows 1278-1430
two-row packing <=1950 needs total <=3900: central 5360 > 3900 -> third row; fourth row iff central >5850: margin 490 ; C6: edit+twin = 5710 vs 6150
```
Extras (lines): G1 215 = D1 texts 35 + band discharge 80 + R1 plumbing 30 + D3 lemma 10 + 3 instances 60; G2 155 = HQg 15 + `GridAssemblyHypNg` builder 40 + `hQ` band re-derivation 40 + 3 instances 60; Budget 60; Lin 160 = band re-derivation 40 + family wrapper 60 + 3 instances 60; EndLin 220 = D5 110 + band re-derivation 60 + 2 instances 50; EndFlow 255 = D2 85 + 10 R2* bridges 50 + PT re-derivation 60 + 3 instances 60. The ticket formula reproduces only 3,740-4,234 on my census (the census script is not in the ticket), the bottom-up central is 5,360: I use it. T2484 precedent: its 1a central 2,438, landed 3,825 (IniTermIIGen 1,113, CltFarUGen 715, IniTermIGen 1,210 + IniTermIGen2 787). Reserve rule (central >1,800): none (max NQLinGen 1,057); at the 2.6× stress NQLinGen 2,748, NQEndLinGen 2,545, NQGood1Gen 2,350 pass 2,300: proposed reserves `NQLinGen2`, `NQEndLinGen2`, `NQGood1Gen2` for the 1a-audit to ratify. Row b is the risk (headroom 41).
### Verdict (per target)
T1 (D1) **PASS** (A1, A2). T2 `hker_of_case1Ng` **PASS** (A2: extra hypothesis `A^{k-1} ≤ W^{ε'}`, `d√A W^{τ'} ≤ W^ε`). T3 shift layer **PASS** under D3 (M3). T4, T5, T6 **PASS** (`T2491_HQg` is verbatim the `hQ` of `azumaProxy_subG_goodExitg`, AzumaProxyGen:237-238). T7, T8, T9, T10 **PASS** (T9 hypotheses = rows 1-5; exponent order: no `∃` after `(sz,z)`). T11, T12 **PASS** (D5 added, A3; exponents of target 12 after the carrier, table rows 3-9). T13 **PASS** (texts only). T14 **PASS** (`𝔠_d = min(𝔠G, 𝔠L, 1/(2d))`, row 10). T15 (D2) **PASS**. T16 **PASS**. D1-D5 **PASS**; no BA source missing, no stop rule fired. Central 5,360 < 5,850: no fourth row (REQ not needed); three rows 1,634 / 1,909 / 1,817; T2484's 1.57× miss applied to the ticket's 4,100 gives about 6,440 > 5,850, so the 1a-audit should weigh which reading binds.

## (a″) Probe compile — Tue Oct 13 06:41:55 UTC 2026
Probe step of T2491 (prover-hard, `claude-sonnet-5-5`). File `RBM3D/Probe/T2491Pins.lean` (397 lines, never merged, no root import), committed on `t/T2491` as 9b4bc546 (parent e6ea965e, the first version; worktree base `main` 7be99aae; `main` is 5fbefff2 at the end of the step: it adds `BA/B45BA`, `Graph/BAExp14a2`, `Graph/BAExp14b2` and 3 import lines in `RBM3D.lean`, none imported by the probe; the probe also compiles against `main`'s oleans, block 2). Section (a) is unchanged. Everything below is script output (scratchpad `T2491/`: `asm.sh`, `diffdefs.py`, `final_greps.sh`, `d5_ev.lean`, `op_*.lean`); the narrative is the findings list.
### Block 1: compile (command, exit code, output)
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2491 && date -u; lake env lean RBM3D/Probe/T2491Pins.lean; echo "exit code: $?"; date -u
Tue Oct 13 06:39:24 UTC 2026
new premises found by the scan: [RBM.BA.T2491_EnvelopeEv]; with probe_kerNAL_band_at withheld: [RBM.BA.T2491_EnvelopeEv,
 RBM.BA.T2491_KerNAL]
RBM.BA.probe_kerNAL_band_at: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerNALFam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kLipFam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_shiftSpec_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_r1Fam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerNALFam_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_shiftSpec_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_r1Fam_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_hkerNg: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_hker_instance: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_band_szB: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_ba_sz0: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_envelope_of_ev: [propext, Classical.choice, Quot.sound]
exit code: 0
Tue Oct 13 06:39:39 UTC 2026
```
### Block 2: greps, diff stats, class texts against the check, other compiles (script `final_greps.sh`, run at 06:39:47 UTC)
```
$ wc -l RBM3D/Probe/T2491Pins.lean; git rev-parse --short HEAD; git status --short; grep -cE "sorry|admit|native_decide|^axiom" (file)
     397 RBM3D/Probe/T2491Pins.lean
9b4bc546
0
$ grep -n "^import RBM3D.BA" RBM3D/Probe/T2491Pins.lean | tr "
" " "
11:import RBM3D.BA.EKSum 12:import RBM3D.BA.GreenSchur 13:import RBM3D.BA.Step2BA 14:import RBM3D.BA.TwistStep2 
$ git diff --stat main...t/T2491 | tail -2
 RBM3D/Probe/T2491Pins.lean | 397 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 397 insertions(+)
$ git diff --stat 7be99aae main -- RBM3D RBM3D.lean   (main = 5fbefff2 )
 RBM3D.lean                 |    3 +
 RBM3D/BA/B45BA.lean        |  399 ++++++++++
 RBM3D/Graph/BAExp14a2.lean |  406 ++++++++++
 RBM3D/Graph/BAExp14b2.lean | 1794 ++++++++++++++++++++++++++++++++++++++++++++
 4 files changed, 2602 insertions(+)
$ python3 -I diffdefs.py   (the six def blocks of the check, lines 339-388, against the probe)
KerNAL 10/10 lines, diff 0; KerNALFam 5/5 lines, diff 0; KLip 4/4 lines, diff 0; KLipFam 4/4 lines, diff 0; ShiftSpec 3/3 lines, diff 0; R1Fam 6/6 lines, diff 0
$ LEAN_PATH=<main build lib, read-only> lean RBM3D/Probe/T2491Pins.lean
Tue Oct 13 06:39:48 UTC 2026
exit code: 0, error lines: 0, same 15 output lines as above: yes
Tue Oct 13 06:40:03 UTC 2026
$ lake env lean docs/tickets/checks/T2491-check.lean
exit code: 0, error lines: 0
$ lake env lean scratch/d5_ev.lean   (T2491_EnvelopeEv proved: the proof of gridDriftNg_envelope with two edits)
'RBM.BA.scratch_envelope_ev' depends on axioms: [propext, Classical.choice, Quot.sound]
$ lake env lean scratch/op_<F>.lean   (open private of every private decl of F)
NQGood1 39|NQGood2 30|NQBudget 55|NQLin 77|NQEndLin 36|NQEndFlow 29|NQEndFlowLift 24|GridGoodGen 22|
$ name clash: git grep -w -F <18 final names> <ref> -- RBM3D (probe excluded) | wc -l
main (5fbefff2) 0|t/T2482b (49b2de45) 0|t/T2484b (c61ae3b4) 0|t/T2486 (19c7f4c7) 0|t/T2486b (3b47302c) 0|t/T2489 (2f825d5e) 0|t/T2489b (8dae485c) 0|t/T2490 (b10f2c9f) 0|t/T2492 (e1526c59) 0|t/T2491 (9b4bc546) 0|
NQ*Gen files in RBM3D/Chain of main: 0
```
### Fill-in table (H250 (4)), final: 13 of 13 rows
| # | deliverable | line / result |
|---|---|---|
| (i) | exponent table | (a) lines 6-24; the probe adds no exponent. `Ck` of D1 is existential; band `nqGood1C d k 𝔡⁻¹ (min κ (4/5))` does not depend on `ε` (probe 171-180). The crossings of (a) rows 4-5 are the hypotheses `hdW : d √A W^{τ'} ≤ W^ε` and `hAk : A^{k-1} ≤ W^{(Cv-Ck)ε}` of `probe_hkerNg` (259-328) |
| (ii) | instance + script | (a) lines 25-53 (numeric, L = 32; BA `g₀ < g`). Lean: `probe_hker_instance` (343-360: band, `szB`, `n = 12`, `L = 4`, `W = 16`, `lam = 1`, `k = 2`, `ε = 1/2`, `τ' = 0`, `D = 2`, `(s,t) = (7/8, 15/16)`, `X = 1_{b₀=b₁}`, `M = 1`, `δ = W^{-2}`); `probe_band_szB` (363-372: D1, D2, D3, R1 at `flow_zB`); `probe_ba_sz0` (375-379: BA, D1 and D3 at the merged `(sz0, zSeq)`, `flow_sz0`, `κ = 1/2`, `BA/FlowPins.lean:1214`) |
| (iii) | hypothesis table | (a) line 65; compiled: EK-6 + `nqGood1C` → `probe_kerNAL_band_at` (153-163), `_Fam_band` (171-180) → `probe_kerNALFam_ba` (217-229: `baEKSumDecayNAL_holds`, `Step2Kern_UN_BA`, `BAflow_real`, `BAflow_lam0_window`); `stKloop_lip` → `probe_kLipFam_band` (183-196), BA twin typechecked (246-248); `norm_mE` → `probe_shiftSpec_band` (199-202), BA `probe_shiftSpec_ba` (232-234: `BAflow_real` + `BAm_norm_le_one`; `ba_G_data` is not needed); R1 → `probe_r1Fam_band` (205-208), `probe_r1Fam_ba` (237-243: `TwistStep2_lam0_sq`); `GridDriftNg` → D5 (row (v)) |
| (iv) | D1 decided; probe lines | D1 PASS, check text kept (diff 0, block 2); A1 confirmed by the scan (block 1: `T2491_KerNAL` is a new premise exactly when `probe_kerNAL_band_at` is withheld); A2 compiled as `probe_hkerNg`. Probe lines: texts 30-81, D5 83-145, band 147-210, BA 212-250, target 2 252-330, instances 332-381, scan 383-395 |
| (v) | D2 (and D5) | D2 PASS, text kept (diff 0); band 183-196; BA twin typechecked 246-248 (owner U3-BA); premise of no target here. D5: `GridDriftNg` is `∀ n, T2491_GridDriftNgAt` by `Iff.rfl` (107-109); `probe_envelope_of_ev` (142-143) recovers the merged envelope by `Eventually.of_forall`; `T2491_EnvelopeEv` (122-128) proved in `d5_ev.lean` (block 2) |
| (vi) | D3 | PASS, inline `∀ n, ‖Cm.m n‖ ≤ 1`: band 199-202, BA 232-234, instances 363-379 |
| (vii) | family-premise table | (a) line 68; rows 6 (D3) and 10 (D1 family, R1 family) compiled at band and BA; the existing BA names of rows 2, 5, 6, 8, 10, 11, 12 (`Step2EventsGenTw_baFlow/_baLaw`, `DecayGenTw_baWardPair`, `gridRepTailGen_ker_BA`, `EMn2BA_mF_data`, `EMn2BA_one_sub_T0`, `ba_G_data`, `BAm_norm_le_one`, `TwistStep2_lam0_sq`, `BAflow_real`, `BAflow_lam0_window`) are `#check`ed by the check file (exit 0, 0 error lines, block 2); rows 1, 3, 4, 9 name results of T2486 / T5-BA, not compiled here |
| (viii) | scope table | (a) line 69, unchanged |
| (ix) | UBA-C1 as used | R1 enters `probe_hkerNg` in: `hcmp` at `n` as the window (279), `step34Gen_ratio_pow_le` (281), `step34Gen_ellT_ge` (282, the ℓ crossing) and the hypotheses `hdW`, `hAk`. No hypothesis `0 < gK n`, guard (g) or `3 ≤ L` appears in its signature. The ticket's row (e) route (`step34Gen_decayK_of_cmp`, `τ' ≤ ε/2`) is not used: `hdW` follows from it (`d W^{τ'} ≤ W^{ε/2}`, `√A ≤ W^{ε/2}`). Targets 3-13, 15: (a) line 70 |
| (x) | premise scan, registry | block 1: new premises `[T2491_EnvelopeEv]` (the D5 text, assumed by `probe_envelope_of_ev`, proved in `d5_ev.lean`, so the 1b can conclude it); `T2491_KerNAL` appears iff the band result is withheld (A1); expected new `owedProps` lines stay 0 as in (a) line 71 |
| (xi) | `open private` | `op_<F>.lean` (block 2): every private decl of NQGood1 39, NQGood2 30, NQBudget 55, NQLin 77, NQEndLin 36, NQEndFlow 29, NQEndFlowLift 24 and GridGoodGen 22 opens (exit 0); the model-free subsets of (a) line 72 are among them; the probe opens none (target 2 uses only public names) |
| (xii) | lines per file | (a) lines 75-90 unchanged. Measured in the probe: D1 band discharge 25 lines (153-180, helpers included) against the 80 planned for `NQGood1Gen`; D2 band discharge 14; generic target 2 with the fast-decay step and the δ-argument 70 lines (band `hker_of_case1N` 66 + `nqGood1_fast_of_cls` 22 lines, `NQGood1.lean:310-376`, `:278-300`); D5 statement 30 lines (90-128) and its scratch proof 49 body lines against the 110 planned for `NQEndLinGen`. No split changes |
| (xiii) | name-clash | block 2, last lines: 0 hits for 18 final names on `main` and nine sibling refs; no `NQ*Gen` file on `main` |
### Findings
1. **D1 compiles at band (all `d`) and at BA.** Band `Ck = nqGood1C d k 𝔡⁻¹ (min κ (4/5))`; `0 < lam n ≤ 𝔡⁻¹` is `WO` and `|E| ≤ 2 - κ` is `abs_lemE_le` + `locDomain`, both eventual, so the per-index class is used only inside `∀ᶠ n`, as the 1a said. No BA source is missing (`baEKSumDecayNAL_holds` at `g = BAflowLam0`); no stop rule fires.
2. **Target 2 from D1 and R1 (A2) compiles generically** (`probe_hkerNg`): hypotheses beyond the band's are `hcmp`, `1 ≤ A`, `Ck ≤ Cv`, `hdW`, `hAk`; the band is `A = 1`, `Cv = Ck`, where `hdW`, `hAk` become the band's `hdW` and `1 ≤ W^0`. The `szB` instance uses the diagonal tensor: `ℓ_s W^{τ'} ≤ diam_∞ → ‖X‖ ≤ δ` holds because `diam_∞ = 0` on the diagonal (`probe_diam_zero`, 337-339) and `X` vanishes off it.
3. **D2** band discharge takes `κ/2` and `gmax = 𝔡⁻¹` in `stKloop_lip` and `RangeCond (ε/2)` for `(1 - t)⁻¹ ≤ N`; `0 < κ`, `0 < ε`, `3 ≤ d` are all used.
4. **D3, R1 at BA** need `BAflow_real` + `BAm_norm_le_one` and `TwistStep2_lam0_sq` + `g₀ g = √t₀ g² ≥ 0`; no `ba_G_data`.
5. The probe imports four `BA` modules (EKSum, GreenSchur, Step2BA, TwistStep2) for the BA readings; the 1b files import none.
6. Paper-delta candidates: none new beyond (a) (`T2491a`).
### Probe verdict
Probe compiles (exit 0, no `sorry`, standard three axioms for all 13 printed declarations); (a″) written; the fill-in table is complete (13 of 13). No stop rule of the ticket fires. Open for the 1a-audit: D5 as an added text (`T2491_GridDriftNgAt`, `T2491_EnvelopeEv`), the hypotheses `hdW`, `hAk` of target 2 against the ticket's UBA-C1 row (e), and the three-row split with the measured sizes of row (xii).
(a″) finalized: Tue Oct 13 06:41:55 UTC 2026 (probe commit 9b4bc546 unchanged since the compile in block 1).

## (b) Script output — Tue Oct 13 07:28 UTC 2026 (written after the commands below)
Row delivered: **U3s2a** = `Chain/NQGood1Gen` (targets 1-3) + `Chain/NQGood2Gen` (targets 4-6), the row fixed by the 1a-audit (`T2491-1a-audit.md`: pre-signed three rows confirmed). Rows b, c not started. Branch `t/T2491` HEAD `ae93f0a2` (base `main` 7be99aae; `main` is 0a68e61d at 07:22 UTC). Scratch scripts: scratchpad `T2491/rep/`.
```
$ date -u; lake build RBM3D.Chain.NQGood1Gen RBM3D.Chain.NQGood2Gen | tail -1          # 07:24:01 UTC
Build completed successfully (3877 jobs).
$ lake build        # full library, import lines of both modules in RBM3D.lean, HEAD ae93f0a2; 07:24:23 -> 07:25:35 UTC, exit 0
Build completed successfully (4354 jobs).     (`#assert_rbm_axioms` ran: "premises found by scanning: 128 (borrowed 1, owed 61, structural 46, refuted 6, superseded 14)")
$ wc -l RBM3D/Chain/NQGood1Gen.lean RBM3D/Chain/NQGood2Gen.lean         # stop line 2,000 per file; 1a central 904 / 730
 836 NQGood1Gen   687 NQGood2Gen   (1,523 in all; no reserve file `<file>2`)
$ lake env lean axioms.lean     # collectAxioms over the 55 public declarations of the two files (names.txt from grep ^(theorem|def|abbrev))
declarations checked: 55; exactly the three standard axioms [propext, Classical.choice, Quot.sound]: 55; a proper subset: 0 []; outside the three: []
$ grep -cE "sorry|admit|native_decide|^axiom|withLam" NQGood1Gen.lean NQGood2Gen.lean   ->  0, 0
$ lake env lean docs/tickets/checks/T2491-check.lean   -> exit 0, error lines 0
$ git diff --stat main...HEAD   -> RBM3D.lean 2+, NQGood1Gen 836, NQGood2Gen 687, Probe/T2491Pins 397 (never merged), Test/Axioms.lean 2 +- ; 5 files, 1923 insertions(+), 1 deletion(-)
$ git diff 7be99aae...HEAD -- RBM3D/Induction RBM3D/Path RBM3D/BA RBM3D/Chain (excluding the two new files) | wc -l   ->  0        (G1: band and merged files untouched)
```
Public declarations by script (`index.py`, `X@n` = line n; the 55 names are in `names.txt`; targets 1-3 = NQGood1Gen, 4-6 = NQGood2Gen):
```
NQGood1Gen (20): NQGoodGen_KerNAL@54 NQGoodGen_KerNALFam@67 nqGoodGen_kerNAL_band_at@79 nqGoodGen_kerNAL_band@101 driftTensorNg@123 driftTensorNg_norm_le_of_goodSetNg@131
  driftTensorNg_far_of_goodSetNg@156 hker_of_case1Ng@177 NQGood1Gen_pair_le@300 NQGood1Gen_qvFormNg_le_of_bounds@369 qvFormNg_le_of_goodSetNg@395 etaT_inv_shiftNg_le@460
  loopFine_shiftNg_le@488 STXiLMg_shiftNg_le@529 goodSetNg_dec_shiftNg@551 norm_loopFine_crudeNg@581 STmaxLKMg_crudeNg@602 STXiLKMg_crudeNg@618 eeShiftErrNg@637 norm_STeeMg_shiftNg_le@642 (+ 8 file-stem helpers, public, used by NQGood2Gen)
NQGood2Gen (27): kappaNonAltNg@54 epsNonAltNg@58 dDriftNonAltNg@62 qvBdNonAltNg@67 cQVNonAltNg@75 {kappa,eps,dDrift,qvBd,cQV}..Ng_band@80-92 kappaNonAltNg_mul_Bctl_pow_le@103
  kappaNonAltNg_succ_mul_Bctl_pow_le@118 nonAlt_hkerNg@142 goodSetNg_A0clsNg@168 nonAlt_hA0clsNg@182 nonAlt_hdriftNg@191 goodSetNg_driftClsNg@200 nonAlt_hDclsNg@211 nonAlt_hκ0Ng@223
  nonAlt_hε0Ng@228 nonAlt_hdDrift0Ng@233 qvBdNonAltNg_pos@257 qvFormNg_le_of_goodSetNg_shift@282 hQ_nonAltNg@345 subGaussStop_nonAltNg@382 cQVNonAltNg_sum_pos@403 hQ_nonAltN_of_Ng@429
```
Statements by script (`stmts.py`: line, name, conclusion with whitespace collapsed, cut at 215 characters; the full text is in the files):
```
G1:101 nqGoodGen_kerNAL_band : NQGoodGen_KerNALFam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam)
G1:131 driftTensorNg_norm_le_of_goodSetNg : ‖driftTensorNg Cm n u M σ a‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / Cm.eta n u) * (((k : ℝ) - 1) + (k : ℝ) * (Γ * Φ))
G1:177 hker_of_case1Ng : ‖Step2Gen_UN C n σ s t X a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - s|) / (sz.lam n ^ 2 + |1 - t|)) ^ (k - 1) * M + ((sz.W n : ℕ) : ℝ) ^ Cv * δ
G1:395 qvFormNg_le_of_goodSetNg : qvFormNg Cm n u w σ M a ≤ (((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 - u|) / (sz.lam n ^ 2 + |1 - w|)) ^ (k - 1)) * ((((sz.W n : ℕ) : ℝ) ^ (Cv * ε) * ((sz.lam n ^ 2 + |1 -
G1:488 loopFine_shiftNg_le : ‖Cm.LM n u' M σ a‖ ≤ ‖Cm.LM n u M σ a‖ + loopShiftErrN d (sz.W n) (Cm.eta n u') ℓ (u' - u)
G1:551 goodSetNg_dec_shiftNg : ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)), ellT (sz.L n) (sz.lam n) u' * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) → ‖Cm.LM n u' M σ a‖ ≤ ((sz
G1:642 norm_STeeMg_shiftNg_le : ‖STeeMg Cm n u' M σ a a' - STeeMg Cm n u M σ a a'‖ ≤ eeShiftErrNg Cm n k u u'
G2:142 nonAlt_hkerNg : ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ → (∀ b, ‖X b‖ ≤ M) → nonAltClsN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) τ' Dc u i δ X → ∀ a : Fin k → Zd d 
G2:282 qvFormNg_le_of_goodSetNg_shift : qvFormNg Cm n u' w σ M a ≤ qvBdNonAltNg Cm n k Cv ε Γ Λ D'' u' w
G2:345 hQ_nonAltNg : ∀ M, GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' M → M.IsHermitian → gridStep s v K n * ((k : ℝ) * qvFormNg Cm n (gridTime s v K n (j + 1)) (gridTime s v K n m) σ M a) ≤ (cQVNo
G2:382 subGaussStop_nonAltNg : SubGaussStopNg Cm σ (gridTime s v K n) (goodExitTauNg Cm s v K k Γ Λ Φ τ' D' n) (fun j ω => ZvecNg Cm s v K n j σ ω) m a j (cQVNonAltNg Cm s v K n k Cv ε Γ Λ D'' m a j)
```
Pins (script diff against `docs/tickets/checks/T2491-check.lean`; `rep/pindiff.py`; `rep/pins.lean` = the three check defs `T2491_HQg`, `T2491_KerNAL(Fam)` copied verbatim by script + `isDefEq` on the telescope of `hQ_nonAltNg`):
```
T2491_KerNAL vs NQGoodGen_KerNAL: 10/10 lines, differing lines: 0      T2491_KerNALFam vs NQGoodGen_KerNALFam: 5/5 lines, differing lines: 0
example : @T2491_KerNAL = @NQGoodGen_KerNAL := rfl ; example : @T2491_KerNALFam = @NQGoodGen_KerNALFam := rfl         (compile, no output)
T2491_HQg (cQVNonAltNg ..) =?= conclusion of hQ_nonAltNg: true            (D2 and D5 are rows b, c; D3 is the inline hypothesis `hm : ‖Cm.m n‖ ≤ 1`)
```
Compiled nonempty instances (same files, `section Inst`, band carrier `bandStep2Mat sz0 Einst`, `d = 3`, `n = 0`, `k = 3`, `σ = (+,-,+)`, `H_0 = 0 ∈ GoodSetNg`, far label `aFar` with `diam_∞ = 2 = ℓ_0 W^{τ'}`; `index.py`): `NQGood1Gen`: 13 examples at lines 738 (D1 family at the flow `(szB, zB)`), 743, 749, 757 (`hker_of_case1Ng` at `Xinst`, `M = 1`, `δ = W^{-6}`), 768, 792-828 (the eight shift lemmas) and the private theorem `NQGood1Gen_kerNAL0` (D1 at one index); `NQGood2Gen`: 16 examples at 528-674 (targets 4-6, incl. `subGaussStop_nonAltNg` at 659 with `azumaSubGNg`, `qvPropagatedNg`, `delta_shift_ok`, no open hypothesis, and `hQ_nonAltN_of_Ng` at 674). Nondegeneracy: `Xinst` is nonzero and vanishes beyond `ℓ_0 W^{τ'}`; `W = 32`, `lam = 1/64`, `ε = 4/5`, `D' = 6 > k+1` (docstring of each section).
Greps and layering (`rep/greps.sh`, `rep/x1c1.py`; hypothesis rules of the ticket):
```
U-C4 `def .*[Kk]er\b|def Ugen`: 0, 0     TN-C4 `STGridRepNgL|ST_gridMart_of_repN`: 0, 0     X1-C4 (def|abbrev|structure of the merged pins): 0, 0     `^import RBM3D.BA` in NQ*Gen*.lean: no output
U5S-C3 `∀ \(sz : Sizes d\)`: NQGood1Gen:67, 68, 70 only = the D1 family text `NQGoodGen_KerNALFam` (row 10 of the family table: binder types of `Flow mk gK` and the guarded `∀ (sz) (𝔠) (z), Flow … → ∀ᶠ n`)
importers: RBM3D.lean:582-583 and NQGood2Gen.lean:6 (imports NQGood1Gen); imports of NQGood1Gen: Chain.AzumaProxyGen, GridEnvelopeGen, GridRepTailGen, Induction.NQGood1; of NQGood2Gen: Chain.NQGood1Gen, StepDecompGen, Induction.NQGood2
X1-C1/C1 regex on the two files, 78 hits: NQGood1Gen 55 = {doc 18, D1 band discharge 13, instance 18, lemma names `loopFine_shiftNg_le`, `norm_loopFine_crudeNg` 6};
  NQGood2Gen 23 = {doc 7, instance 7, `open RBM.Ind (.. nqGood1C ..)`, the five `_band` bridges and the band re-derivation `hQ_nonAltN_of_Ng` (statement and proof at `bandStep2Mat`) 9}; no hit in a generic statement
name clash: git grep -w -F of the 55 public names, RBM3D minus the two files: main 0a68e61d 0 | t/T2494 0 | t/T2493 0 | t/T2492 0 | t/T2489b 0  (07:15 UTC, 55 names: also t/T2489, T2490, T2486b, T2484b, T2482b: 0)
```
Name-level tables (0149 `:98`). **Hypothesis table (D1-D3):** EK-6 `ekSumDecayNAL_holds` + `nqGood1C` (`NQGood1:261,310`) -> `NQGoodGen_KerNAL … Ck` -> band `nqGoodGen_kerNAL_band_at/_band` (`bandStep2_Ugen`, `nqGood1_mE_im_ge`, `norm_mE`, `abs_lemE_le`, `WO`) -> BA `baEKSumDecayNAL_holds` + `Step2Kern_UN_BA` + `BAflow_real` + `BAflow_lam0_window` (U3-BA; typechecked by the probe, (a″) block 1); `norm_mE` -> `hm : ‖Cm.m n‖ ≤ 1` (D3, inline, per index) -> BA `BAm_norm_le_one` + `BAflow_real`; row sums `hS` -> band `sum_norm_SB_row` -> BA `S = 1`. D2 is NQEndFlowGen (row c).
**Family-premise rows as used here** (rows 1-5, 9, 11, 12 enter rows b, c): row 6 `hm` (pointwise, from `∀ n`), row 7 `hS` (pointwise), row 8 `hRow : GridRepTailGen_Ker Cm.toFlowFM n` (per index), row 10 D1 family (guarded, `∃ Ck` before `(sz, z)`) and R1 inline as `hcmp`; no public statement takes `GridDriftNg`/`HierarchyNg`.
**UBA-C1 as used:** R1 (`hcmp`, `hA`, `hdW`, `hAk`, `Ck ≤ Cv`) enters `hker_of_case1Ng` only (`step34Gen_ratio_pow_le`, `step34Gen_ellT_ge`, the window read off `hcmp` inline) and through it `NQGood1Gen_pair_le`, `qvFormNg_le_of_goodSetNg`, `nonAlt_hkerNg`, `qvFormNg_le_of_goodSetNg_shift`, `hQ_nonAltNg`, `subGaussStop_nonAltNg`; `step34Gen_winK_of_cmp`, `step34Gen_decayK_of_cmp` and `sz.withLam` do not occur (grep: `step34Gen_` only at NQGood1Gen:175 (docstring), 199, 200); the shift layer, the vocabulary, the fields other than `hker`, `qvBdNonAltNg_pos`, `cQVNonAltNg_sum_pos` never see R1.
**Scope (band public declarations of NQGood1/NQGood2 before the instance sections, script):** 52 = 37 regenerated + 7 reused by name (`loopShiftErrN`, `nqGood1_loopShiftErrN_nonneg`, `norm_loopL_zshiftN_le`, `loopMax_zshiftN_le`, `nqGood1_ellT_mono`, `nonAltClsN`, `nqGood2_ratio_mul_Bctl_le`) + 5 inlined/private (`UgenPairN`, `qvFormN_eq_re_UgenPairN` [not needed: `qvFormNg` is `Re STeeUMg`, K4 is not used], the pair identity, two `STmaxLM` helpers) + 3 band only (`nqGood1C`, `nqGood1C_pos`, `nqGood1_mE_im_ge`); unmapped or missing: 0.
**`open private`:** NQGood1Gen:38 `nqGood1_STdiamInf_one`; NQGood2Gen:34 `nqGood2_pow_aux nqGood2_gridTime_le nqGood2_gridTime_nonneg`; instance-only: NQGood1Gen:716 `W0 lam0 rpow32_fifth ell0 im_mE_half hW_inst hWε_inst hdW_inst hWt_inst hwL_inst hσ_inst hδ_inst Bctl0_le`, NQGood2Gen:477 `W0 lam0 rpow32_fifth im_mE_half hσ3 hW1 hW1' hW0 hWε hdW u_nonneg u_lt_one u_mono hwL hvL hWt ell_u0 ell_u1`. No `private` deleted.
**Registry:** `Test/Axioms.lean` line 237 (owner text of `GoodSetNg`) now reads "the majorant `hQ` is the generic `hQ_nonAltNg` (T2491, `Chain/NQGood2Gen.lean`; band re-derivation `hQ_nonAltN_of_Ng`; U3s3 reads it)"; no `owedProps` line added (the full build's `#assert_rbm_axioms` passes; `NQGoodGen_KerNAL(Fam)` are concluded by the band theorems, so the scan does not list them).
Narrative (all else is in the files). (1) Each theorem of targets 1-6 ports its band theorem to `Cm : Step2Mat sz`: `etaT E` -> `Cm.eta n`, `zt E` -> `ztOf (Cm.m n) (E n)` under `StepDecompGen_LoopForm`, `Ugen` -> `Step2Gen_UN`, `norm_UN_apply_le` -> the K2 row sums of `GridRepTailGen_Ker`; the shift layer needs `‖m‖ ≤ 1` and `Σ_b‖S_{ab}‖ ≤ 1` (D3). (2) `hQ_nonAltNg` drops the band's `|E n| < 2`, `0 < lam n`, `0 ≤ Γ n` and adds `hKer`, `hRow`, `hcmp`, `hA`, `hCv`, `hdW`, `hAk`, `hm`, `hS`, `hL`; the D1 texts equal the check (0 differing lines). (3) No stop rule fired: files 836 / 687 < 2,000; no BA source missing; no `∃` after `(sz, z)`; no `BA/*` import; no band or merged file edited; no new kernel, carrier field or `STGridRepNgL` premise. (4) Not in this row: the `GridAssemblyHypNg` bundle (the fields are the theorems; U3s3 builds it), D2 and D5 (rows b, c), BA instances (U3-BA).

## (c) Mathlib names (all occur in the two files and compile)
`Finset.sum_le_card_nsmul Nat.card_Icc pi_norm_le_iff_of_nonneg norm_le_pi_norm Real.rpow_logb Real.logb_le_iff_le_rpow Real.rpow_le_rpow_of_exponent_le inv_le_of_inv_le₀ inv_anti₀ div_le_div₀ div_le_div_of_nonneg_left div_le_div_of_nonneg_right pow_le_pow_left₀ pow_le_pow_right₀ pow_le_one₀ inv_le_one_of_one_le₀ one_le_pow₀ one_le_inv₀ pow_le_pow_of_le_one Finset.sup'_le Finset.le_sup' Finset.le_sup'_of_le Finset.prod_univ_sum Fintype.piFinset_univ Finset.prod_le_prod₀ Complex.re_le_norm Complex.abs_im_le_norm Complex.norm_real Real.coe_toNNReal Real.le_coe_toNNReal Finset.single_le_sum NNReal.coe_nonneg Matrix.isHermitian_zero Real.sqrt_one norm_add₃_le norm_sub_le norm_sum_le Real.rpow_add Real.rpow_nonneg Real.rpow_natCast`. Names verified absent: none needed (no name was invented).

## (d) Open issues and paper-delta candidates
1. **T2491a** (Lean/paper, D1 and R1): the kernel estimate `(sum_res_2_NAL)` is a class with an explicit constant `Ck`, uniform over the flow carrier (`∃ Ck` after `(k, κ, ε, 𝔡)`, before `(sz, z)`); target 2 and its consumers carry the vocabulary constant `Cv ≥ Ck` and two crossings `d√A W^{τ'} ≤ W^ε`, `A^{k-1} ≤ W^{(Cv-Ck)ε}` (band: `A = 1`, `Cv = Ck`, both trivial); for BA they are eventual limit conditions ((a) (i) rows 4-5; 1a-audit O3).
2. **T2491b** (Lean/paper, D3): the shift layer uses `‖z_{u'} - z_u‖ ≤ |u' - u| ‖m‖` with `‖m‖ ≤ 1` (band: equality, `|m| = 1`), `η_u = (1-u) Im m` through `LoopForm`, and the row sums `Σ_b ‖S_{ab}‖ ≤ 1` (band: `= 1`); `eeShiftErrNg` carries the same bound `W^d k L^d (2k+2) η^{-(2k+3)} (W^{-d})^{2k+1} (u'-u)` with `Cm.eta`. No other statement difference: `qvFormNg` is `Re STeeUMg` by definition, so the band's conjugation step (K4) is not used in target 2.
3. Closed: T2473c-audit O1 (`hQ` open at `Cm0`): `subGaussStop_nonAltNg` has a compiled instance at `Cm0 = bandStep2Mat sz0 Einst`, with `hQ` from `hQ_nonAltNg` (example at NQGood2Gen:659).
4. For the hub: `RBM3D/Probe/T2491Pins.lean` is on `t/T2491` and must not be merged; the merge brings `Chain/NQGood1Gen.lean`, `Chain/NQGood2Gen.lean`, the two import lines of `RBM3D.lean` and the one-line text change in `Test/Axioms.lean` (union of lines with other tickets). Row b (`NQBudgetGen`, `NQLinGen`) reads `kappaNonAltNg_mul_Bctl_pow_le`, `NQGoodGen_KerNAL`, `driftTensorNg`, `eeShiftErrNg`, `NQGood1Gen_eta_*` by name.
5. Observation: the module docstrings of both files carry 20 long-line warnings (as the merged `Induction/NQGood2.lean`); no other warning in the two files.
