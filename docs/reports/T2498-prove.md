Prover model: claude-sonnet-5-5

## (a) Math preflight — Wed Oct 14 02:07:53 UTC 2026
Basis: worktree `t/T2498` = `main` 3f945e60 (`main` 086d9091 differs in `RBM3D/` only by T2499: `RBM3D.lean`, `Test/Axioms.lean`, new `BA/Step5IIITargets`); targets are the primed chain of `lem:STOeq_Qt`/`(eq:alternatecase1)` (`3_5:1676-1714`), no new mathematics. Scripts and outputs: scratchpad `T2498/` (`$S`). No Lean written. Constants: `Cv` = vocabulary constant, `C4` = D1 constant (band `Cv = C4`).
### (i) Exponent table (`N=(WL)^d`, `r=(gK²+|1-s|)/(gK²+|1-t|)`, `A` = R1 constant, `k=m+2`)
| # | quantity | constraint | value / slack (from the output below) |
|---|---|---|---|
| 1 | D1 `C4` (`∃` after `(k,κ,ε,𝔡,KL)`, before `(sz,z)`) | `‖UN A‖ ≤ W^{C4 ε} r^k ‖A‖ + W^{-D+C4}`, every `σ`, sum-zero decayed `A`, `s ≤ t ≤ 1-gK²/L²`, `W⁻¹ ≤ (1-t)/(1-s)` | needed `C4`, k=2: crude ≤ 2.22 (W=5, ε=.9), ≤ 3.91 (W=64, ε=.5; band g=1; BA g=10: 3.90); sum-zero test class ≤ 2.57; every `C4 ≥ 3.91` closes both data sets; the proved constant is `Classical.choose` (band `qProxy4C`) / `baEKSumDecay2_holds` (BA): no numeric value claimed |
| 2 | `Cv` against `C4` | `A^k ≤ W^{(Cv-C4)ε}` (`step34Gen_ratio_pow_le`, Step34Gen:711); band `A=1`, `Cv=C4` | W=64, ε=.9: least `Cv-C4` (k=2,3,4) = 0.52/0.78/1.04 (g=1/64), 0.74/1.11/1.48 (g=1), 1.67/2.50/3.34 (g=10); instance `Cv-C4=4`; eventual (ε=.0125): log10 W ≥ 67.5/101/135 (A=2.64) … 217/326/434 (A=22.7) |
| 3 | ℓ-crossing | `d√A W^{τ'} ≤ W^{ε}` (`step34Gen_ellT_ge`, :785) | W=64, τ'=.2, ε=.9: 11.2/13.8/32.8 ≤ 42.2 (slack 3.8×/3.1×/1.29×); eventual, τ'=ε/4: log10 W ≥ 220/249/370 (BA), 122 (band) |
| 4 | EK-4 window | `1<W`, `0<ε<1`, `4 ≤ W^ε`, `log L ≤ W^ε`, `L^d ≤ W^KL`, `1<D` | W=64: 42.2 ≥ 4, 3.47 ≤ 42.2, 32768 ≤ 262144 (KL=3); W=5, ε=.9: 4.26 ≥ 4 (slack .26), 32768 ≤ 78125; eventual log10 W ≥ 48.2 |
| 5 | R1 `A = Aof κ = (κ+1)/κ` | `1 ≤ A`, `0 ≤ gK·lam`, `gK² ≤ lam² ≤ A gK²`; window `t ≤ 1-lam²/L²` implies `t ≤ 1-gK²/L²` | `A = g²/g0²` exactly (2.640/4.008/22.711 at κ = Im m = .610/.333/.046), slack 0 (extremal `t0=κ/(κ+1)`); g=10: gK²/L² = .0043 ≤ lam²/L² = .098 |
| 6 | budget exponents `altBudgetExpQN` (QBudgetB:92) with `Cv` | `ε = min(e₂/(8 max(Cv,Cn)), ½)`, `e₂=ε₀'/2`, `ε'=ε/2`, `τ'=min(ε/4, e₂/(40 d (m+1)))`, `D''=2Cn+2+2Cv+k+(4k+1)/𝔠`, `D'=D''+2`: 20 conditions | all hold in the scan (m=0,1,2; 5 pairs `(C4,Cn)`; 𝔠 ∈ {1/100,1/6}; `Cv ∈ {C4,C4+1}`); tightest non-positivity slack .039; k=2: ε = .0156 (Cv=4), .0125 (Cv=5), D'' = 920/922 (𝔠=1/100); `τ'>0` at m=0 |
| 7 | range of `k` | EK-4 needs `2 ≤ k`; `qProxy4C d (m+2)`, `qProxyCn d (m+1)` | `m ≥ 0` covers `n_ ≥ 2`; `k=2` at m=0 is in every scan |
| 8 | D2 `hη`, D3 `‖m‖ ≤ 1` | `0 < eta ≤ 1-v` (`Im m ≤ 1`), `‖m0‖ ≤ 1`, `κ ≤ Im m0` | Im m = .610/.333/.046 (slack .39/.67/.95); `‖m0‖` = .9997/.667/.220 (slack 3e-4/.33/.78); Im m0 ≥ κ in all three |
| 9 | `sz0` windows (`Defs/Sizes.lean:260`) | WO `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`, Bandwidth `N^𝔠 ≤ W` | n=0: 7.8e-3 ≤ 1.56e-2 ≤ 10 (factor 2(n+1) in general); max 𝔠 = .2381 → 5/18; 𝔠d ≤ 1/100: slack ×24 |
| 10 | pinned `∃` | `𝔠d`, `C4` (`KL=1/𝔠`), `∃ C₆` after κ, `Aof κ` all before `(sz,z)`; `ε₁ τ' D' C_K` after the carrier | none after `(sz,z)`; check Part 2's BA reading has `∃ C₆` before κ, the table row 9 and `B45Gen_Facts` have it after κ, and the BA tail constant `Q₀` of `NewKLKBA_tail` (:270) depends on `(d, Λ, κ)`: use after κ (A4) |
### (ii) One concrete nondegenerate instance
`d=3`; per-index targets and D1: `L=32`, `W=5` (ε=.9, KL=7) and `W=64` (ε=.5, KL=2.5; ε=.9, τ'=.2, KL=3 for `alt_hker`), `k=2,3,4`, `C4=4`, `Cv=8`, 35 windows `(s,t)`; kernels: band `S_g` at E=0, 1.9 (|m|=1) and BA `|M|²`, `z=0.3+i`, `g0<g`, `g = 1/64, 1, 10`; endpoint (targets 10-12) at `sz0`, `𝔡 = 1/10`: hypotheses are eventual in `n`, so the limit lines of `d2.py` and the thresholds of rows 2-4 are the nonvacuity evidence; other gates' pins (`STSEforLngL`, `STKcalDecaygL`, `STStep2ConclgL`, `STLKgL`, `STKboundgL`) stay hypotheses.
```
$ bash $S/rep.sh; bash $S/rep2.sh      # each `# ...` line names the script and its filter
# d1.py L W eps KL: EK-4 constant needed, C4_lb on the sum-zero test class / C4_ub crude; sigma=(+,-), k=2, 35 (s,t) windows
data: d=3 L=32 W=5.0 eps=0.9 D=2.0 KL=7.0 (4<=W^eps: 4.257, log L=3.466<=W^eps, L^d=32768<=W^KL=78125); sigma=(+,-), k=2
  band E=0          gK= 0.0156 C4_lb= 0.013 C4_ub= 0.013 @(s,t)=(0.9,0.98) r=4.952
  band E=0          gK= 1.0000 C4_lb= 1.628 C4_ub= 2.118 @(s,t)=(0.9,0.98) r=1.078
  band E=0          gK=10.0000 C4_lb= 2.216 C4_ub= 2.217 @(s,t)=(0.5,0.90) r=1.004
  BA g=0.0156 g0=0.0096 A=2.640 gK= 0.0096 C4_lb= 0.005 C4_ub= 0.005 @(s,t)=(0.9,0.98) r=4.982
  BA g=1.0000 g0=0.4995 A=4.008 gK= 0.4995 C4_lb= 0.220 C4_ub= 1.863 @(s,t)=(0.9,0.98) r=1.297
  BA g=10.0000 g0=2.0984 A=22.711 gK= 2.0984 C4_lb= 0.156 C4_ub= 2.197 @(s,t)=(0.9,0.98) r=1.018
W=64 eps=.5 KL=2.5  band E=0          gK= 1.0000 C4_lb= 2.571 C4_ub= 3.910 @(s,t)=(0.9,1.00) r=1.098
W=64 eps=.5 KL=2.5  BA g=1.0000 g0=0.4995 A=4.008 gK= 0.4995 C4_lb= 0.844 C4_ub= 3.682 @(s,t)=(0.9,1.00) r=1.392
W=64 eps=.5 KL=2.5  BA g=10.0000 g0=2.0984 A=22.711 gK= 2.0984 C4_lb= 0.341 C4_ub= 3.898 @(s,t)=(0.5,0.99) r=1.112
# d1b.py: hypotheses and conclusion of the generic alt_hker at g0<g=lam
data d=3 L=32 W=64.0 eps=0.9 tau'=0.2 KL=3.0 C4=4.0 Cv=8.0; W^eps=42.22 W^tau'=2.297 L^d=32768<=W^KL=262144; (Cv-C4) eps ln W=14.972
 g=0.0156 g0=0.0096 A=2.640: d*sqrtA*W^tau'=11.2<=W^eps=42.2:True; A^k<=W^((Cv-C4)eps) k=2,3,4:[True, True, True]; least Cv-C4=0.52,0.78,1.04; Cv_need(crude)=0.08,0.11,0.15 <= Cv=8.0: True
 g=1.0000 g0=0.4995 A=4.008: d*sqrtA*W^tau'=13.8<=W^eps=42.2:True; A^k<=W^((Cv-C4)eps) k=2,3,4:[True, True, True]; least Cv-C4=0.74,1.11,1.48; Cv_need(crude)=2.17,3.26,4.34 <= Cv=8.0: True
 g=10.0000 g0=2.0984 A=22.711: d*sqrtA*W^tau'=32.8<=W^eps=42.2:True; A^k<=W^((Cv-C4)eps) k=2,3,4:[True, True, True]; least Cv-C4=1.67,2.50,3.34; Cv_need(crude)=1.24,1.86,2.48 <= Cv=8.0: True
# expo.py: 20 conditions of altBudgetExpQN at Cv; R1 thresholds (log10 W)
 k=2 C4= 4 Cn= 4 c=0.0100 Cv= 4: eps=0.01562 D''= 920.00 #conds=20 violated=[] tightest='0<=Cn*eps'' slack=0.0312
 k=2 C4= 4 Cn= 4 c=0.0100 Cv= 5: eps=0.01250 D''= 922.00 #conds=20 violated=[] tightest='0<=Cn*eps'' slack=0.0250
all scanned (m=0,1,2; 5 constant pairs; c in {1/100,1/6}; Cv in {C4,C4+1}) satisfy all 20 conditions: True ; tightest non-positivity condition over the scan: (0.038750000000000284, "2k+c(2C4eps-(D''-2Cn-2))<=xi") at (m,C4,Cn,c,shift)= (0, 1, 1, 0.01, 0)
 A= 2.640 C4=4 Cv=5 eps=0.01250: log10 W >= A^k:   67.5(k=2)   101.2(k=3)   134.9(k=4) | d sqrtA W^(eps/4)<=W^eps:   220.1 | 4<=W^eps:   48.2
 A=22.711 C4=4 Cv=5 eps=0.01250: log10 W >= A^k:  217.0(k=2)   325.5(k=3)   434.0(k=4) | d sqrtA W^(eps/4)<=W^eps:   369.7 | 4<=W^eps:   48.2
# d2.py: BA spectral data; sz0 windows
 g=0.0156: Im m=0.6097 (0<Im m<=1: True)  eta_v=(1-v)Im m<=1-v ok; |m0|=0.9997<=1:True  Im m0=0.9907>=kappa:=Im m:True  g0=0.0096<g  A=(kappa+1)/kappa=2.640  g^2/g0^2=2.640
 g=1.0000: Im m=0.3325 (0<Im m<=1: True)  eta_v=(1-v)Im m<=1-v ok; |m0|=0.6669<=1:True  Im m0=0.6656>=kappa:=Im m:True  g0=0.4995<g  A=(kappa+1)/kappa=4.008  g^2/g0^2=4.008
 g=10.0000: Im m=0.0461 (0<Im m<=1: True)  eta_v=(1-v)Im m<=1-v ok; |m0|=0.2197<=1:True  Im m0=0.2195>=kappa:=Im m:True  g0=2.0984<g  A=(kappa+1)/kappa=22.711  g^2/g0^2=22.711
 n=            0: WO  W^(-d/2+delta)=7.813e-03 <= lam=1.562e-02 <= 1/delta=10: True;  Bandwidth N^c=1.157 <= W=3.200e+01: True; max admissible c=0.2381
 n=1000000000000: WO  W^(-d/2+delta)=7.812e-87 <= lam=1.562e-74 <= 1/delta=10: True;  Bandwidth N^c=167.192 <= W=3.200e+61: True; max admissible c=0.2766
limit: log N = log 8 + 18 log x, log W = 5 log x  =>  c_max(n) = 5 log x/(log 8 + 18 log x) -> 5/18 = 0.2778 from below, min at n=0: 0.2381
# size2.py: lines per file (T2496 method), rows b, c (T2491 method)
file      old  moved  tok  extras | added at c1=1.2 / 2.0 / 3.0 | final size (old-moved+(c1-1)tok+extras) 1.2 / 2.0 / 3.0
QProxy    2261   774  123    190 |   338 /  436 /  559 |  1702 / 1800 / 1923
QDriftA   1341     0   70    140 |   224 /  280 /  350 |  1495 / 1551 / 1621
QDriftB    951     0   38     60 |   106 /  136 /  174 |  1019 / 1049 / 1087
QLevelsA   687     0   86     55 |   158 /  227 /  313 |   759 /  828 /  914
QLevelsB   586     0    5     10 |    16 /   20 /   25 |   597 /  601 /  606
QBudgetA  1339     0  128     90 |   244 /  346 /  474 |  1455 / 1557 / 1685
QBudgetB  1142     0   46     90 |   145 /  182 /  228 |  1241 / 1278 / 1324
QEndA     2056  1041  163    355 |   551 /  681 /  844 |  1403 / 1533 / 1696
siblings QProxy2 130 + QEndA2 70 = 200; U3s3a total added = 1981 / 2508 / 3167  (cut 1,950)
split at QLevelsB|QBudgetA: a1 = 971 / 1229 / 1551 ; a2 = 1009 / 1279 / 1616
row b QEndGridGen: regen 915 x1.05 + extras 130 + hdr 80 = 1171 ; row c QEndB1Gen: regen 829 x1.05 + extras 170 + hdr 80 = 1120  (ticket 1,700 / 1,250)
total a+b+c central 4799 (lo 3814, hi 6375); ticket 4,830; UP-C3 line 5,850
landing at the per-file T2496 factors (LemDecCalELip 643/479=1.34, DuhamelII 420/322=1.30): row a 3311 (ticket sensitivity 3,271); at the T2496 total factor 1.60: 4023; a+b+c at 1.32: 5602, at 1.60: 6314
QProxy final: 1900 at 1.32, 1989 at 1.60 (stop line 2,000); QEndA in place 899 at 1.32 vs new-file price 950
# git grep -w -F of the 63 proposed names: main (086d9091), t/T2498, t/T2499
HEAD: total hits 0 t/T2498: total hits 0 t/T2499: total hits 0
# import cycles: Q-chain files reached by the Chain modules the in-place files add
SUMMARY ticket list (15 Chain modules): reaching a Q file: {'QGridGen': ['QGridA'], 'QGridGen2': ['QGridA', 'QGridB']} ; reaching a BA module: [] ; QGridA reaches Q files: [] ; QGridB reaches: ['QGridA']
# scope closure (decl lines, in-scope per file), G1 and open private
QProxy 1257, QDriftA 389, QDriftB 364, QLevelsA 420, QLevelsB 15, QBudgetA 706, QBudgetB 699, QEndA 777, QEndGrid 1458, QEndB1 1079, total 7164
Part 3 in-place names: 32 = defs/abbrevs (unedited, twins beside) 10 + theorems converted (need a band corollary) 20 + model-free/unchanged 2 (qProxy4C_pos, altEnd_stronglyMeasurable_zVecQN); corollaries per file: {'QProxy': 1, 'QLevelsA': 1, 'QBudgetA': 2, 'QBudgetB': 2, 'QEndA': 14}
  Induction/QEndGrid 40 ['Mx', 'QDriftA_W0', 'altBudgetExpQN', 'altBudgetExpQN_of_choice', 'altBudgetNumQN_eventually', 'altClsQN', 'altEnd_aFroz_eq_aTrue', 'altEnd_driftSup', 'altEnd_hexp', 'altEnd_stronglyMeasurable_zVecQN', 'altEnd_unQ', 'altExitMeasN', 'altExitTauN', 'altYSetN', 'alt_hA0clsGridQN', 'alt_hDclsGridQN', 'alt_hdriftGridQN', 'alt_hkerGridQN', 'assembledRHSAltQN', 'assembledRHSAltQN_qErr_le', 'budgetAltQN', 'cQVAltQN', 'dDriftAltLinQN', 'dDriftAltLinQN_le_shape', 'dDriftAltLinQN_nonneg', 'epsAltQN', "gridDriftQN_envelope'", 'kappaAltQN', 'mem_of_lt_altExitTauN', 'qProxy4C', 'qProxy4C_pos', 'qProxyCQ', 'qProxyCn', 'qProxyCn_pos', 'qProxyW0', 'qvBdAltQN', 'subGaussStop_altQN', '
QEndGrid {'priv_free': (34, 502), 'priv_tok': (9, 442), 'pub_free': (1, 39), 'pub_tok': (1, 475)} (decls, lines) in D4 scope
QEndB1 {'priv_free': (22, 232), 'priv_tok': (14, 779), 'pub_free': (2, 18), 'pub_tok': (1, 50)} (decls, lines) in D4 scope
# premise-scan preview and registry lines (main 086d9091; base 3f945e60: :229, :236)
Step5KerGen_ThDecay -> concluded by NO THEOREM (scan would report it if assumed) 
B45Gen_Facts -> concluded by ['Chain/B45Gen.lean:82 b45Gen_facts_band', 'BA/B45BA.lean:205 baB45Gen_facts'] 
228:   `RBM.BA.STXiBootgL', -- `(am;asoi222)` at
235:   `RBM.BA.GoodSetNg, -- the good set of the
```
### Fill-in table (§269 (5))
| item | content |
|---|---|
| (i) | rows 1-10 above |
| (ii) | the instance above: band E=0 (E=1.9 gives the same numbers in the unfiltered run: `(+,-)` sees `‖m‖²=1`), BA `g0<g`, `g=1/64,1,10`; `alt_hker` hypotheses and conclusion at BA data in `d1b.py` |
| (iii) | EK-4 `(sum_res_2)` → `T2498_KerEK4` → band `ekSumDecay2_holds` (`Λg=𝔡⁻¹`, `κ'=min κ 4/5` by `nqGood1_mE_im_ge`, `0<lam≤Λg` from WO `∀ᶠ`, `3≤L`) → BA `baEKSumDecay2_holds` (EKSum:1772) at `g=BAflowLam0` via `Step2Kern_UN_BA`, `BAflow_real`, `BAflow_lam0_window`; `Step5KerGen_ThDecay` → `step5KerGen_thDecay_band` (Step5KerGen:242) → U4-BA (a) (`NewKLKBA:269`, `baComp_row_le`); `B45Gen_Facts` → `b45Gen_facts_band` (B45Gen:82) → `baB45Gen_facts` (B45BA:205); D2 classes → `hierDriftGen_{expand,kLoop,kTwo,uStep,kLink}_band` → `baHierDrift_*` (GridDriftBA:102-622), `baStep2Mat_KI`, `ba_G_data` |
| (iv) | D1 PASS, check text kept (it has no `0<gK`, `3≤L`, `κ≤Im m`: used only under `∀ᶠ n`). **A1:** `hker_altQNg`, `alt_hkerQNg` and the vocabulary carry two constants, `C4` (D1) and `Cv` with hypothesis `A^k ≤ W^{(Cv-C4)ε}` (row 2); band `Cv=C4`, `A=1`; family `Cv=C4+1` (the ticket's "vocabulary takes `C4`" reads `Cv`, as T2491's `Ck_voc = Ck+1`) |
| (v) | D2 decided, no new Prop def (**A2**): `gridDriftQNg_envelope_ev` = `gridDriftQNg` (QGridGen:759) with `hExp hKL hKT hU` per index under `∀ᶠ n` (as `stOeqNQPTgL''_of`, NQEndFlowGen:673-757), `hS hKK hm hη` for all `n`, `0<lam n` eventual from R1 guard (g); wing envelope `exists_norm_KI_le_wing` (HierDriftGen:1083) at length `m+2`; conclusion `∀ᶠ n, ∀ᵐ ω ∂Cm.Pp, ∀ j<K n, ∀ a, ‖rGridQNg …(QopAlgebra_mollifier d (L n) (m+1) (lam n)) σ j ω a‖ ≤ qErrQNg … (N^τK η^{-(m+2)}) j` (D5's `GridDriftNgAt` was needed because `GridDriftNg` is a pin; `gridDriftQNg` is a theorem on classes) |
| (vi) | D3: check text of `T2498_XiRoundPTgL''`, `T2498_OeqQtRoundPTgL''` = band `STXiRoundPT''` (QEndB1:100: `STbootRHS 1`, `n_ ≥ 2`) with `Prec→PrecL`, `STXiL(K)→STXiL(K)g`; bundle of target 12 = the 22 hypotheses of `stOeqNQPTgL''_of` plus D1 `QProxyG_KerEK4Fam`, `∀ κ ∃ C₆ … Step5KerGen_ThDecay` (after κ, **A4**), `B45Gen_Facts`. Probe (≤400): D1 text + band discharge at `szB/zB` ~160, ThDecay concluder ~20, D2 text + classes ~90, one `alt_hker` instance at the BA data of `d1b.py` ~60, round-pin bridge `bandFM_STIngR` (the check's `example` at :237) ~40, scan ~30 |
| (vii) | rows 1-7, 10-12 = hypotheses of `stOeqNQPTgL''_of` unchanged (`hSE hFlow hL hm hW hLaw hC hSpec hWard hKcal hEK hRow hR1 hT0`); new: row 8 `QProxyG_KerEK4Fam` next to `NQGoodGen_KerNALFam`, row 9 ThDecay + `B45Gen_Facts`; row 11 (D2) = `hExp hKL hKT hU` (`∀ᶠ n`) + `hKK` (`∀ n`) already present; no `∀ n` drift premise |
| (viii) | in-scope declaration lines (closure of `stOeqQtRoundPT''_holds` minus the D4 exclusions, `closure.py`, docstrings counted): QProxy 1257, QDriftA 389, QDriftB 364, QLevelsA 420, QLevelsB 15, QBudgetA 706, QBudgetB 699, QEndA 777, QEndGrid 1458, QEndB1 1079 = 7,164 (ticket 6,693). **A5:** Part 3 names read from `QEndGrid`/`QEndB1`: 32 in the eight files (ticket 33): 10 defs unedited, 20 theorems need a band corollary (20×15 = 300, ticket 495), 2 model-free; `QEndGrid` also reads 9 model-free names unchanged (`QDriftA_W0`, `altBudgetExpQN(_of_choice)`, `altClsQN`, `qProxy4C`, `qProxyCQ/Cn/Cn_pos/W0`, output above) |
| (ix) | R1 only at `ugenPairQNg_le_of_bounds` (3), `hker_altQNg` (4), `altB4Ng_fastDecay` (5) (steps (a) :683, (c) :711, ℓ-crossing :785), passed on by `alt_hkerGridQNg` (8) and the guard (g) of targets 10, 12; never in 2, 6, 7, `hQ_altQNg` (`NQGood1Gen_eta_anti`) |
| (x) | scan: `QProxyG_KerEK4` (targets 3, 4) and `…Fam` (target 12) need band concluders with those heads (`qProxyG_kerEK4_band_at`, `qProxyG_kerEK4_band`). **A3:** `Step5KerGen_ThDecay` becomes an outer hypothesis with row a's `altB4Ng_fastDecay` (target 5, as planned) and no theorem has it as head (`step5KerGen_thDecay_band` concludes an `∃`, output above): add a band concluder with head ThDecay (≈10 lines, `Classical.choose` constant) in a row-a file. Concluded by merged theorems: `B45Gen_Facts`, `DecayGen_Spec`, `DecayGen_WardPair`, `GridRepTailGen_Ker`, `HierDriftGen_*`, `StepDecompGen_*`, `Step2EventsGen_*`, `Step34Gen_LCompat`. Registered: `STSEforLngL`, `STKcalDecaygL`, `STStep2ConclgL`, `STLKgL`, `STKboundgL`. Registry lines: `GoodSetNg` owner text (ticket `:237`; `:236` at 3f945e60, `:235` now, T2499 removed a line above) as the ticket; `STXiBootgL'` `(proofs: U3s3, U3s4)` (:229, now :228) is stale after decision (4): same edit proposed; no new `owedProps` line |
| (xi) | `open private`: QEndGridGen ← QEndGrid §0-§5 34 private decls / 502 lines (regenerated: 9 private + `altGridEndQN'`, 917 lines); QEndB1Gen ← QEndB1 22 / 232 lines (regenerated 14 + 1, 829 lines); QProxy2, QEndA2 ← 774 / 1,041 lines moved verbatim; imports: no cycle (output above), no BA module reached |
| (xii) | **U3s3a central 2,508 (lo 1,981, hi 3,167) > 1,950 even at the low end: the pre-signed split fires**: U3s3a (QProxy…QLevelsB, QProxy2) 1,229 (971-1,551), U3s3a′ (QBudgetA, QBudgetB, QEndA, QEndA2) 1,279 (1,009-1,616); row b 1,171, row c 1,120 (ticket 1,700 / 1,250); total 4,799 (3,814-6,375) against the ticket's 4,830 and the UP-C3 line 5,850. Landing at the per-file T2496 factors (×1.32: `LemDecCalELip` 643/479, `DuhamelII` 420/322): row a 3,311 (ticket sensitivity 3,271), total 5,602; at the T2496 total factor ×1.60: 4,023 / 6,314 (> 5,850). `QProxy` final 1,800 (1,702-1,923), 1,900 / 1,989 at ×1.32 / ×1.60 against 2,000: relief = move the D1 band discharge (~100 lines, needs no reader) to `QProxy2`; `QEndA` in place 899 (×1.32) vs new-file 950, 1,092 at ×1.60. numstat forecast = "added" above, `moved` = 774 + 1,041 |
| (xiii) | 0 hits (output above) |
### Verdicts
Targets 1-9 (U3s3a) **PASS** (D1: A1, A3; D2: A2; vocabulary, kernel, budget, R1 steps: rows 1-9; G1: A5), target 10 (`altGridEndQNg`, row b) **PASS** (exponents after the carrier, rows 6, 10), targets 11-13 **PASS** (A4; texts equal the band; BA sources exist for D1/D2/ThDecay/B45). No stop rule fires; the split of (xii) makes U3s3 four rows (a, a′, b, c); at ×1.60 the total passes the UP-C3 line. **Overall PASS.**

## (a″) Probe compile — Wed Oct 14 02:27:21 UTC 2026
Basis: worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2498`, branch `t/T2498`, probe commits `feb5c020` and `3118c1d0` (parent `3f945e60` = the basis of (a); `main` is `086d9091`). Section (a) is not edited. Probe file `RBM3D/Probe/T2498Pins.lean`: 397 lines, git blob `4ad09a0d9c1c`, no root import. Scripts and outputs: scratchpad `T2498/`.
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2498 && lake env lean RBM3D/Probe/T2498Pins.lean; echo "exit code: $?"   # stdout+stderr; started/ended (date -u) below
Wed Oct 14 02:26:39 UTC 2026
Wed Oct 14 02:26:46 UTC 2026
RBM.BA.probe_kerEK4_band_at: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerEK4Fam_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerEK4Fam_ba: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_hker_altQNg: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_alt_hkerQNg: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_ba_type_data: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_kerEK4_ba_at: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_alt_hker_ba_type: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_alt_hker_ba_three: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_D1_flows: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_round_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_gridDriftQ_step: [propext, Classical.choice, Quot.sound]
exit code: 0
$ grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Probe/T2498Pins.lean | wc -l
0
$ grep -n Probe RBM3D.lean | wc -l
0
$ grep -rn "T2498_\|probe_szG\|probe_X" RBM3D --include=*.lean | grep -v RBM3D/Probe/ | wc -l   # name clash
0
$ git diff --stat 3f945e60 086d9091 -- RBM3D RBM3D.lean   # basis of (a) vs main; the probe imports none of these three files
 RBM3D.lean                    |   1 +
 RBM3D/BA/Step5IIITargets.lean | 112 ++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean        |   3 +-
 3 files changed, 114 insertions(+), 2 deletions(-)
$ grep -n "^import" RBM3D/Probe/T2498Pins.lean | cut -d: -f2 | tr "
" " "
import RBM3D.Induction.QEndB1 import RBM3D.Induction.NQEndFlowLift import RBM3D.Chain.QGridGen2 import RBM3D.Chain.GridEnvelopeGen import RBM3D.Chain.Step5KerGen import RBM3D.Chain.B45Gen import RBM3D.Chain.Step2Kern import RBM3D.BA.EKSum import RBM3D.BA.GreenSchur import RBM3D.BA.Step2BA import RBM3D.BA.TwistStep2 import RBM3D.BA.CouplingWindow 
$ python3 -I verb.py   # D1, D3 texts: probe against docs/tickets/checks/T2498-check.lean (comments stripped, whitespace collapsed)
T2498_KerEK4 IDENTICAL 683 683
T2498_KerEK4Fam IDENTICAL 394 394
T2498_XiRoundPTgL'' IDENTICAL 684 684
T2498_OeqQtRoundPTgL'' IDENTICAL 327 327
$ python3 -I rows3.py   # the 13 rows of the 1a fill-in table in section (a)
(i) row present=1, text chars=15 -> 10 exponent-table rows above: FILLED
(ii) row present=1, text chars=191: FILLED
(iii) row present=1, text chars=593: FILLED
(iv) row present=1, text chars=343: FILLED
(v) row present=1, text chars=579: FILLED
(vi) row present=1, text chars=564: FILLED
(vii) row present=1, text chars=318: FILLED
(viii) row present=1, text chars=618: FILLED
(ix) row present=1, text chars=256: FILLED
(x) row present=1, text chars=978: FILLED
(xi) row present=1, text chars=302: FILLED
(xii) row present=1, text chars=829: FILLED
(xiii) row present=1, text chars=21 -> 1 "total hits 0" output line(s) above: FILLED
all 13 rows of the 1a fill-in table filled: True
$ grep -nE "^(theorem|def|private theorem|private def|example) " RBM3D/Probe/T2498Pins.lean | cut -c1-110
36:def T2498_KerEK4 {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (KL C4 : ℝ) (n : ℕ) : Prop :=
47:def T2498_KerEK4Fam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
56:theorem probe_kerEK4_band_at {d k : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (hd : 3 ≤ d) (hk : 2 ≤ k) {Λ κ' KL : ℝ} (
67:private theorem probe_flow_im {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z) (n
69:private theorem probe_flow_E {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z) (n 
71:theorem probe_kerEK4Fam_band (d : ℕ) : T2498_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
85:theorem probe_kerEK4Fam_ba (d : ℕ) : T2498_KerEK4Fam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z 
112:def probe_kappaAltQNg (k : ℕ) (Cv lam W ε : ℝ) (u : ℕ → ℝ) (i m : ℕ) : ℝ :=
114:theorem probe_hker_altQNg {D : ℝ} (hD : 1 < D) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
181:theorem probe_alt_hkerQNg {Dc : ℝ} (hDc : 1 < Dc) {Kg : ℕ} {u : ℕ → ℝ} (hu0 : ∀ i ≤ Kg, 0 ≤ u i)
207:theorem probe_ba_type_data (L : ℕ) [NeZero L] {g : ℝ} (hg : 0 < g) :
238:theorem probe_kerEK4_ba_at {d k : ℕ} (sz : Sizes d) (g0 E κ Λ KL : ℝ) (m0 : ℂ) (hd : 3 ≤ d) (hk : 2 ≤ k) (
256:def probe_szG (g : ℝ) : Sizes 3 where
262:private def probe_b2 : Fin 2 → Zd 3 16 := fun i => if i = 1 then fun _ => 1 else 0
264:def probe_X : (Fin 2 → Zd 3 16) → ℂ := fun b => (if b = 0 then 1 else 0) - (if b = probe_b2 then 1 else 0)
265:private theorem probe_b2_ne : (0 : Fin 2 → Zd 3 16) ≠ probe_b2 := by
267:theorem probe_X_sumZero : EKSumZero probe_X := by
274:private theorem probe_X_norm (b : Fin 2 → Zd 3 16) : ‖probe_X b‖ ≤ 1 := by
279:private theorem probe_X_diam {b : Fin 2 → Zd 3 16} (hb : probe_X b ≠ 0) : STdiamInf b ≤ 1 := by
285:private theorem probe_W_rpow (q : ℝ) (n : ℕ) (h : 16 * q = n) : (65536 : ℝ) ^ q = 2 ^ n := by
288:def probe_AltHkerInst (g : ℝ) : Prop := ∃ g0 E C4 : ℝ, 0 < g0 ∧ g0 < g ∧ probe_X ≠ 0 ∧
292:theorem probe_alt_hker_ba_type {g : ℝ} (hg : 0 < g) (hg10 : g ≤ 10) : probe_AltHkerInst g := by
323:theorem probe_alt_hker_ba_three : probe_AltHkerInst (1 / 64) ∧ probe_AltHkerInst 1 ∧ probe_AltHkerInst 10 
331:theorem probe_D1_flows : (∃ C4 : ℝ, 0 < C4 ∧ ∀ᶠ n in atTop, T2498_KerEK4 (bandFM szB (STflowE zB)) szB.lam
338:def T2498_XiRoundPTgL'' {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop
348:def T2498_OeqQtRoundPTgL'' (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
352:theorem probe_round_band (d : ℕ) : STOeqQtRoundPT'' d ↔ T2498_OeqQtRoundPTgL'' d (fun sz => Sizes.seqP sz)
355:example : Prop := ∀ d : ℕ, T2498_OeqQtRoundPTgL'' d (fun sz => Sizes.seqP (sz.withLam 0))
361:def T2498_GridDriftQEv : Prop :=
377:theorem probe_gridDriftQ_step {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz} {E lam' : ℕ → ℝ}
$ sed -n "288,291p;323,326p" RBM3D/Probe/T2498Pins.lean   # the instance statement
def probe_AltHkerInst (g : ℝ) : Prop := ∃ g0 E C4 : ℝ, 0 < g0 ∧ g0 < g ∧ probe_X ≠ 0 ∧
  ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 16),
    ‖Step2Gen_UN (baFM (probe_szG g) (fun _ => g0) (fun _ => E)) 0 σ ((fun j : ℕ => (j : ℝ) / 2) 0) ((fun j : ℕ => (j : ℝ) / 2) 1) probe_X a‖ ≤
      probe_kappaAltQNg 2 (C4 + 4) g 65536 (7 / 8) (fun j : ℕ => (j : ℝ) / 2) 0 1 * 1 + 65536 ^ (C4 + 4) * 0
theorem probe_alt_hker_ba_three : probe_AltHkerInst (1 / 64) ∧ probe_AltHkerInst 1 ∧ probe_AltHkerInst 10 :=
  ⟨probe_alt_hker_ba_type (by norm_num) (by norm_num), probe_alt_hker_ba_type (by norm_num) (by norm_num),
    probe_alt_hker_ba_type (by norm_num) (by norm_num)⟩
end Inst
```
Result: the probe compiles (exit 0), has no `sorry`, and each of the 12 theorems listed in the `#eval` prints the standard three axioms. What it shows, by item of the ticket's Probe line:
- **D1 text:** `T2498_KerEK4`, `T2498_KerEK4Fam` are identical to the check (script). **Band discharge:** `probe_kerEK4_band_at` (one index, `C4 = qProxy4C d k Λ κ' KL` from `ekSumDecay2_holds`, through `bandStep2_Ugen`); `probe_kerEK4Fam_band` (general `d`, `Λ = 𝔡⁻¹`, `κ' = min κ (4/5)` by `nqGood1_mE_im_ge`, eventual `n` from the `WO` window of `STFlow`); at `(szB, zB)` (`flow_zB`, `d = 3`, `k = 2`, `KL = 3`): first conjunct of `probe_D1_flows`.
- **BA reading, discharged and not only typechecked:** `probe_kerEK4Fam_ba` (general `d`; `baEKSumDecay2_holds` at `g = BAflowLam0` through `Step2Kern_UN_BA`, `BAflow_real`, `BAflow_lam0_window`); at `(sz0, zSeq)` (`flow_sz0`): second conjunct of `probe_D1_flows`.
- **`alt_hkerQNg`:** `probe_hker_altQNg` (one index, any carrier `C : FlowFM sz`; D1 at the kernel coupling `gK`, the R1 comparison `hcmp`/`hA`, the two constants `C4 ≤ Cv` with `hAk : A^k ≤ W^{(Cv-C4)ε}` and `hdW : d√A W^τ' ≤ W^ε`, conclusion at the size level `sz.lam`) and its grid-time form `probe_alt_hkerQNg` (class `altClsQN`, as band `alt_hkerQN`, `QDriftA.lean:353`). **Instance** `probe_alt_hker_ba_three` = `probe_AltHkerInst` at `g = 1/64, 1, 10`: BA kernel `baFM (probe_szG g) g₀ E` with `g₀ = √t₀ g < g` from the S-point `(zS L g, mS L g)` (`probe_ba_type_data`: `BAzztE_data`, `BAdom_real`); D1 at that kernel from `baEKSumDecay2_holds` (`probe_kerEK4_ba_at`); R1 with `A = 36/25 + g² L³` (`t₀ ≥ 1/A` from `BASelf_subord`); `d = 3`, `L = 16`, `W = 2^16`, `ε = 7/8`, `τ' = 1/16`, `KL = 1`, `k = 2`, `Cv = C4 + 4`, `Dc = 2`, grid `u_j = j/2`, `(i, m) = (0, 1)`, `M = 1`, `δ = 0`, `X = probe_X ≠ 0` (sum-zero, `1_{b=0} - 1_{b=(0,e)}`), every `σ` and `a`; the only side conditions of `probe_alt_hker_ba_type` are `0 < g ≤ 10`.
- **D2 text:** `T2498_GridDriftQEv` (a `def`, not proved here) and `probe_gridDriftQ_step`, which gives the one-step bound from the merged `gridDriftQNg` (`Chain/QGridGen.lean:759`, T2497) at `m + 1`, with the wing bound `hB` as the only input besides the per-index classes. The eventual step (`exists_norm_KI_le_wing`, then `∀ᶠ n`, `∀ j < K n`) is not in the probe.
- **Round pin:** the two texts are identical to the check; `probe_round_band` proves `STOeqQtRoundPT'' d ↔ T2498_OeqQtRoundPTgL'' d …` by `bandFM_STIngR d STCaseI (fun sz E s t => STXiRoundPT'' sz E s t)` alone; the BA reading of the check (`example : Prop`) typechecks.
Observations against (a), none changes a verdict:
- The Lean instance does not use the numbers of (a)(ii) (`d1b.py`: `L = 32`, `W = 64`, `ε = .9`, `τ' = .2`, `z = 0.3 + i`, `A = 2.64 / 4.01 / 22.7`). `z = 0.3 + i` needs a Lean lower bound on `t₀` that the probe does not have; the S-point gives `A ≤ 36/25 + g² L³` (at most 4.1·10⁵ at `g = 10`, `L = 16`), and `d√A W^τ' ≤ W^ε` then needs `W = 2^16`.
- `δ = 0`: the window clause holds because the support of `probe_X` has `L^∞`-spread ≤ 1 < `ℓ W^{τ'}` (as in the band instance `alt_hkerQN_instance`, `QDriftA` §7).
- (a)(vi) and (x) list a band concluder with head `Step5KerGen_ThDecay` (A3) and a premise scan for the probe; they are not in this probe (the ticket's Probe line does not list them; the file is 397 of 400 lines). Those rows stand as written in (a).
- No (a′) section: the texts of (a)(iv)-(vi) compile as stated.

## (a′) Preflight corrections — Wed Oct 14 03:57:45 UTC 2026
- Amend 1 (`docs/tickets/T2498-amend-1.md`): `∃ C₆` after `κ`, per `(𝔡, κ)`. Section (a) A4 already says "after κ"; the probe's BA shape (`T2498-check.lean:254-258`, not binding) has it before `κ`. In 1b row a states `Step5KerGen_ThDecay` per carrier (`C₆` a real bound before the carrier, `altB4Ng_fastDecay`, `QDriftB:683`); the quantified family premise `∃ C₆` after `κ` belongs to row c and is read in the amended order. No statement changes.
- Design deviations from (a), none changes a verdict: (1) `ugenPairQNg_le_of_bounds`, `qvFormQNg_le_of_bounds` carry two radii `ε₁` (of `qqTensorBoundsN`) and `ε` (of D1) with `√A·W^ε₁ ≤ W^ε`; the band reading is `ε₁ = ε`, `A = 1`, `Cv = C4`. (2) `altB45Ng_levelM`, `startLevelQNg` read the sample-level `B45_det2g` at a Hermitian matrix through a private frozen carrier `QLevelsA_frozen Cm Hs` (hypotheses `LoopForm`, `ZeroModeGen_WardCls`, `ZeroModeGen_KerSums`, row/column sums `≤ K₆/(1-t)`). (3) Band text of `QDriftA/B`, `QLevelsA/B` is untouched (generic twins appended), so those files grow past the 1a forecast. (4) Added `qDriftB_thDecay_band_concl` (A3 of (x)); the `Test/Axioms.lean` edit of `T2498.md:90` is left to row a′ (the new `GoodSetNg` owner text names `hQ_altQNg` of `Induction/QEndA`, which row a′ writes).

## (b) Script output (stage 1b, U3s3a first part: `QProxy`, `QProxy2`, `QDriftA`, `QDriftB`, `QLevelsA`, `QLevelsB`; targets 1-6 and their part of 9)
Commits on `t/T2498` (`git log`, UTC): `7ea17490` 03:47:36, `5e8ef75a` 03:54:22. `QBudgetA/B`, `QEndA`, `QEndA2` (targets 7, 8, rest of 9) are U3s3a′ (`t/T2498a2`), not here; rows b, c later.
### Name-level tables (`tables.py`: declarations parsed from `git show 3118c1d0:` and `HEAD`, namespaces tracked)
```
file      lines old->new | public names at 3118c1d0: kept in file / moved to QProxy2 / removed | new public names: def thm inst
QProxy     2261-> 1644 |  44:  19 / 18 /  7 |  5 13  0
QProxy2       0->  838 |   0:   0 /  0 /  0 |  1  0  8
QDriftA    1341-> 1893 |  41:  41 /  0 /  0 |  5  9  7
QDriftB     951-> 1679 |  10:  10 /  0 /  0 |  0  6  6
QLevelsA    687->  914 |   6:   6 /  0 /  0 |  0  2  2
QLevelsB    586->  618 |  13:  13 /  0 /  0 |  0  1  1
removed (7): QProxyInst.azumaSubGQ_ugenN_instance QProxyInst.qv_at_propagatorQ_instance QProxyInst.ugenPairQN_le_of_bounds_instance QProxyInst.yMomentsQUnifN_instance_pos azumaSubGQ_ugenN qv_at_propagatorQ ugenPairQN_le_of_bounds
moved verbatim QProxy -> QProxy2 (matching blocks >= 3 lines): 681
```
Frozen names (public names that exist before and after: 107). `#check @name` with `pp.fieldNotation false`, run by `lake env lean` in the main worktree (main oleans) and in the branch:
```
main: exit 0, 1541 output lines; branch: exit 0, 1541 output lines; diff of the two outputs: 0 lines
$ git diff --stat 3118c1d0 HEAD -- QBudgetA QBudgetB QEndA QEndGrid QEndB1 QtXiRoundLift Test/Axioms.lean RBM3D.lean | wc -l   ->  0
$ git diff --name-only main...t/T2498    ->  QDriftA QDriftB QLevelsA QLevelsB QProxy QProxy2 (all RBM3D/Induction/) and RBM3D/Probe/T2498Pins.lean (stays on the branch)
```
### Builds (all times `date -u`)
```
$ lake build RBM3D.Induction.QProxy ... RBM3D.Induction.QLevelsB       # 03:56:18, exit 0: "Build completed successfully (3901 jobs)."
$ lake build   # whole library; RBM3D.lean carries a temporary `import RBM3D.Induction.QProxy2` (restored by `git checkout`, not committed: the hub's step)
  03:51:28 -> 03:54:09, exit 0; 0 lines matching ": error"; "axiom audit: 15002 theorems, 4642 definitions, 0 axioms in `RBM`"
  "premises found by scanning: 124 (borrowed 1, owed 57, structural 46, refuted 6, superseded 14)." (no new unregistered premise); "Build completed successfully (4377 jobs)."
$ lake env lean docs/tickets/checks/T2498-check.lean   # in the branch worktree: exit 0, 1705 output lines, 0 containing "error"
$ grep -c "sorry\|admit\|native_decide\|^axiom" <the six files>   ->  0
```
### Axioms (`#print axioms` of the 66 new public declarations and the 107 kept ones, 173 lines)
```
 172 [propext, Classical.choice, Quot.sound]
   1 [propext, Quot.sound]        (RBM.Ind.QDriftAInst.sigma_alt_and_nonalt, a kept band helper)
```
### Targets: file:first-last line of the statement (up to `:=`; defs to the blank line), and `[i file:line]` = its compiled instance (`theorem`, same file unless named)
```
QProxy: QProxyG_KerEK4 680-690; QProxyG_KerEK4Fam 692-696; qProxyG_kerEK4_band_at 698-700; qProxyG_kerEK4_band 718-719 [i QProxy2:44]; qvFormQNg 132-138; zVecQNg 140-143; yVecQNg 145-148; martIncQNg_ae_eq 320-325 [i QProxy2:50]; qv_at_propagatorQg 368-376 [i QProxy2:72]; azumaSubGQ_ugenNg 464-474 [i QProxy2:129]; azumaSubGQ_gridExitNg 515-527 [i QProxy2:147]; ugenPairQNg_le_of_bounds 1103-1125 [i QProxy2:414]; qvFormQNg_le_of_bounds 1192-1205 [i QProxy2:703]; yMomentsQUnifNg 1591-1598 [i QProxy2:223]
QDriftA: altB4Ng 121-127; altB5Ng 130-134; dFlowQNg 137-146; kappaAltQNg 149-150; epsAltQNg 153-154; dGridQNg_eq_dFlowQNg 255-257 [i :1645]; dFlowQNg_sumZero 262-268 [i :1652]; fastDecay_of_diamInfg 510-516 [i :1668]; hker_altQNg 541-555 [i :1695]; alt_hkerQNg 596-609 [i :1732]; goodSetNg_A0clsQNg 748-757 [i :1765]; alt_hA0clsQNg 777-785 [i :1824]
QDriftB: drift13_fastDecayg 458-463 [i :1485]; altB4Ng_fastDecay 683-693 [i :1505]; altB5Ng_fastDecay_moll 800-809 [i :1529]; dFlowQNg_clsQNg 854-866 [i :1550]; alt_hDclsQNg 899-921 [i :1600]; qDriftB_thDecay_band_concl 791-792 [i :1671]
QLevelsA: altB45Ng_levelM 455-478 [i :863]; startLevelQNg 511-534 [i :891]
QLevelsB: goodSetNg_LKM_far 128-134 [i :520]
```
Also in `QDriftA`: `qDriftA_kappaAltQNg_band`, `qDriftA_epsAltQNg_band` (`rfl`: `kappaAltQNg`, `epsAltQNg` at `qProxy4C` are the band `kappaAltQN`, `epsAltQN`). Defs (`QProxyG_KerEK4(Fam)`, `qvFormQNg`, `zVecQNg`, `yVecQNg`, `altB4Ng`, `altB5Ng`, `dFlowQNg`, `kappaAltQNg`, `epsAltQNg`) have no instance of their own; the instances unfold them. Bridges: `qProxy_qvFormQN_eq_g`, `qProxy_zVecQN_eq_g`, `qProxy_yVecQN_eq_g` (band `qvFormQN`, `zVecQN`, `yVecQN` = the generic at `bandStep2Mat`).
D1 text against the check, `diff -B` of `T2498-check.lean:213-224, 228-233` (names `T2498_KerEK4*` -> `QProxyG_KerEK4*`) and `QProxy.lean:680-690, 692-696`: IDENTICAL.
### Compiled nonempty instances (`d = 3`, nondegenerate: `L = 5` or `sz0`/`szB` windows, `W > 1`, `s < t`, nonzero sum-zero tensors, windows attained by a tuple; BA only in the check). Example, `QProxy2:41-48`:
```
open RBM.Gauss.Step34Inst in
/-- **Instance of D1** (`qProxyG_kerEK4_band`) at the band flow `(szB, zB)` of `Step34Pins` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `d = 3`, `k = 2`,
`KL = 3`: the constant `C4 > 0` exists and the class holds eventually in `n`. -/
theorem qProxyG_kerEK4_band_instance :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ᶠ n in atTop, QProxyG_KerEK4 (bandFM szB (STflowE zB)) szB.lam 2 3 C4 n :=
  (qProxyG_kerEK4_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 10) (1 / 10) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).imp
    fun _ h => ⟨h.1, h.2 szB (1 / 6) zB flow_zB⟩
```
The others (`QProxy2:50-703`, `QDriftA:1645-1824`, `QDriftB:1485-1671`, `QLevelsA:863-891`, `QLevelsB:520`) are the `[i]` entries above; each is a `theorem` in `QxxxInst` with every deterministic hypothesis discharged (D1 by `qProxyG_kerEK4_band_at`, `GoodSetNg` by `bandStep2_GoodSetN`, `ZeroModeGen_KerSums` by `zeroModeGen_kerSums_band`, `Step5KerGen_ThDecay` by `qDriftB_thDecay_band_concl`).
### Name clash (`git grep -w -F -l` of the 66 new final components in `RBM3D RBM3D.lean`)
```
66 distinct final components; names with a hit: main 5d4ea2ed 0, t/T2499 0c272838 0, t/T2501 0d98bc2b 0, t/T2501a2 3f8e9624 0, t/T2501b df731125 0
the 7 removed names (table) have no reader outside `QProxy.lean` on main (`git grep -w -l`: 0 each)
```
### Lines (`git diff --numstat 3118c1d0 HEAD`; moved = `difflib` blocks of >= 3 lines of old `QProxy` found in `QProxy2`)
```
added 2937 (in place: 1544 before the `Inst` namespaces + 555 instances; QProxy2: 838), removed 1177, moved 681; added - moved = 2256
forecast of (a)(xii): 1229 (971-1551), sensitivity price 1229 x 1.74 = 2138; net change of the six files: 5826 -> 7586 lines (+1760); largest file QDriftA 1893 < 2000
```
Narrative.
- Generic twins `...g` sit in namespace `RBM.Ind` with `open RBM.BA` and no `BA/*` import; `QProxy` keeps the band names read outside (`azumaSubGQ_gridExitN`, `qvFormQN_le_of_bounds`, `yMomentsQUnifN`, ...) with the same name and type, now corollaries of the generic theorems; band proofs without outside reader (`qv_at_propagatorQ`, `azumaSubGQ_ugenN`, `ugenPairQN_le_of_bounds`, the ConjKernel helpers) are removed for size (1173 lines out, 681 of them moved to `QProxy2`).
- D1 is the class `QProxyG_KerEK4` over `Step2Gen_UN` at the coupling `gK`, with `C4` explicit; the band constant is `qProxy4C`. R1 enters as `hcmp` (`gK² ≤ lam² ≤ A gK²`) and the two constants `C4 ≤ Cv` with `A^k ≤ W^((Cv-C4) ε)`.
- Calibration: added - moved is 2256, above the forecast central 1229 by 1027 and above the sensitivity price 2138 by 118 (5.5%); no file reaches 2000, so the stop rule did not fire. Realized / forecast central = 2256 / 1229 = 1.84.
- I changed no band reader and no frozen signature; whole-library build (above) compiles `QBudgetA/B`, `QEndA`, `QEndGrid`, `QEndB1`, `QtXiRoundLift` and `#assert_rbm_axioms` unchanged.

## (c) Verified Mathlib names
All 85 namespace-qualified names (prefixes Real, Complex, Finset, Fin, Nat, Filter, Matrix, Set, ZMod, Function, Pi; regex over the added lines, comments stripped) resolve: `#check @name` in a file importing the six modules, exit 0, 0 errors. None is absent.
`Complex.{norm_of_nonneg, re, re_le_norm}; Filter.Eventually.of_forall; Filter.eventually_ge_atTop; Fin.{addCases, append, append_left, append_right, ext, forall_fin_two, last, natAdd, sum_univ_three}`
`Finset.{Icc, card_univ, le_sup, mem_filter, mem_univ, mul_sum, prod_congr, sum_add_distrib, sum_congr, sum_const, sum_ite_eq', sum_le_sum, sum_mul, sum_sub_distrib, sup_const, sup_eq_bot_iff, univ_nonempty}; Function.update; Matrix.{cons_val, cons_val_one, cons_val_zero, isHermitian_zero}; Nat.{cast_nonneg, cast_pos, cast_zero, le_ceil, le_succ, mod_eq_of_lt, mul_le_mul_left, pos_of_ne_zero, zero_le}; Pi.{sub_apply, zero_apply}`
`Real.{exp, exp_add, exp_le_exp, exp_pos, le_coe_toNNReal, le_sqrt', le_sqrt_of_sq_le, log, log_le_sub_one_of_pos, log_mul, log_two_lt_d9, logb, logb_le_iff_le_rpow, mul_self_sqrt, one_le_rpow, rpow_add, rpow_le_rpow, rpow_le_rpow_of_exponent_le, rpow_le_rpow_of_nonpos, rpow_logb, rpow_mul, rpow_natCast, rpow_neg, rpow_neg_one, rpow_nonneg, rpow_one, rpow_pos_of_pos, rpow_two, sqrt, sqrt_eq_rpow, sqrt_nonneg, sqrt_one, sqrt_pos, sqrt_sq, toNNReal}; Set.mem_singleton_iff; ZMod.{val_natCast, val_zero}`

## (d) Open issues and paper-delta candidates
- Scope: row a is half done. U3s3a′ (`QBudgetA`, `QBudgetB`, `QEndA`, `QEndA2`: targets 7, 8, rest of 9) runs on `t/T2498a2`; rows b, c (`QEndGridGen`, `QEndB1Gen`) are untouched.
- `Test/Axioms.lean` is not edited: the registry text of `T2498.md:90` names `hQ_altQNg` of `QEndA`, which does not exist before row a′, so row a′ edits it with `QEndA`. The scan reported no new premise, so no `owedProps` line is added.
- `RBM3D.lean` is not edited (the hub adds `import RBM3D.Induction.QProxy2` after the last import line). The whole-library build above ran on base `3118c1d0`; `main` is `5d4ea2ed` and changed `BA/CltFlowBA`, `BA/Step5IIITargets`, `BA/Step5KerBA`, `BA/ZeroModeBA`, `Test/Axioms.lean` since the merge-base `3f945e60` (none of the six files): the merge-time build is the hub's.
- Band instance `yMomentsQUnifN_instance_pos` is replaced by `yMomentsQUnifNg_instance_pos`; the band theorem `yMomentsQUnifN` stays as a corollary without an instance of its own. The trailing `#print axioms` lines of the old `QProxy` (old 2217-2261) are dropped; the registry covers them.
- BA readings of the new statements are typechecked only in the check (compiles); no BA file reads the twins yet.
- Paper-delta candidates (Lean device, no paper statement changes): `T2498a` two radii `ε₁`, `ε` and two constants `C4 ≤ Cv` with `A^k ≤ W^((Cv-C4) ε)`, from the comparison R1 `gK² ≤ lam² ≤ A gK²` taken as an explicit hypothesis; `T2498b` `qvFormQNg` is defined with the `!σ`-product, the band bridge is `qProxy_qvFormQN_eq_g`; `T2498c` removal of seven unread band declarations of `QProxy` (Lean-only, size); `T2498d` frozen-carrier route for `altB45Ng_levelM` (`B45_det2g` read at a matrix); `T2498e` `Step5KerGen_ThDecay` constant `C₆` is `Classical.choose` of `step5KerGen_thDecay_band` at the band, per carrier before `κ` in row a (family form after `κ`, Amend 1, in row c).
- `T2498f` (D1, EK-4 as a carrier class): `(sum_res_2)` (`3_5_Loop_Hierarchy.tex:1659`) enters the generic Step 3 `Q*` layer as the class `QProxyG_KerEK4` / `QProxyG_KerEK4Fam` (`Induction/QProxy.lean:680`, `:692`) with an explicit constant `C4`: for `1 < W`, `L^d ≤ W^{KL}` (`KL` explicit), `0 < ε < 1`, `1 < D`, `4 ≤ W^ε`, `log L ≤ W^ε`, `0 ≤ s ≤ t ≤ 1 - gK²/L²`, `W⁻¹ ≤ (1-t)/(1-s)`, every `σ : Fin k → Bool` and every `A` with `EKFastDecay (gK n) s W ε D A` and `EKSumZero` (fast decay at the kernel coupling `gK`), `‖Step2Gen_UN C n σ s t A‖ ≤ W^{C4 ε} ((gK²+|1-s|)/(gK²+|1-t|))^k ‖A‖ + W^{-D+C4}`. Family order: `3 ≤ d → ∀ k ≥ 2, ∀ κ ε 𝔡 KL > 0, ∃ C4 > 0, ∀ (sz, 𝔠, z), Flow → ∀ᶠ n`, i.e. `∃ C4` after `(k, κ, ε, 𝔡, KL)` and before `(sz, z)`. Band discharge `qProxyG_kerEK4_band` (`QProxy.lean:718`) with `C4 = qProxy4C d k 𝔡⁻¹ (min κ (4/5)) KL`; BA source `baEKSumDecay2_holds` (`BA/EKSum.lean:1772`, owner U3-BA; read in the probe `T2498Pins.lean:88`, `:241`). Analogue of D717 (a) (`NQGoodGen_KerNAL`, `∃ Ck` after `(k, κ, ε, 𝔡)`) for EK-4; `T2498a` covers only the R1 constants on top of it.
## Repair — Wed Oct 14 04:11:28 UTC 2026
Repairer model: claude-opus-5-5. Report-only repair of `T2498-audit.md` round 1, Required item 1: candidate `T2498f` added to (d). No `.lean` file changed; branch `t/T2498` stays at `5e8ef75a`.
