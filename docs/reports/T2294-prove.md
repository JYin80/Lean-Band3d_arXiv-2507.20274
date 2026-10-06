Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 13:00:35 UTC 2026

### (i) Exponent table (d = 3 numbers; `k = m+2` indices, `m' = m+1` the mollifier index of `gridDriftQN`/`sum_weighted_qErrQN_le`; `C4 = qProxy4C`, `Cn = qProxyCn`, `CQ = 2Cn+2` are `Classical.choose` constants, only `> 0` is known, so they stay symbols)
| # | quantity | value / choice | constraint (source) | slack |
|---|---|---|---|---|
| 1 | `ε` of `altYGridN` (level `N^ε X`) | any `ε>0` | `Prec` at `τ=ε`; `‖STLKM‖ ≤ max ≤ (N^εX-1)B^l ≤ N^εXB^l` (`B>0`: `st_Bctl_pos`, `u≤v<1`) | none needed |
| 2 | `C`, `K` of `altYGridN` | `K n ≤ ⌈N^{C_K}⌉`, `C = C_K+1` | `K+1 ≤ N^C` eventually (`highProbAt_iInter` card; `max C 0` as `gridGood_grid`) | `N^{C_K}+2 ≤ N^{C_K+1}` for `N ≥ 3` (G1) |
| 3 | `ε₀` (final loss), `ε₁, εq, τN` | `ε₁ = ε₀/40`, `τN = ε₀/8` | `altBudgetExpQN_of_choice`: `ε₁, εq, τN ≤ ε₀/8` | `ε₁` slack `ε₀/10` |
| 4 | `ε, ε', τ'` chain | `ε = min(ε₀/(8·max(C4,Cn)), 1/2)`, `ε' = ε/2`, `τ' = min(ε/4, ε₀/(40dm))` | `C4ε, Cnε, Cnε' ≤ ε₀/8`; `d W^{τ'} ≤ W^{ε'}` (hdrift, hA0cls, hDcls); `d W^{ε'} ≤ W^{ε}` (hker, class exponent is `ε'`, see F3); eventual from `W ≥ N^𝔠` | `W^{ε'-τ'} ≥ d`, `W^{ε-ε'} ≥ d` once `N^{𝔠ε/4} ≥ d` |
| 5 | `ν`, `hMΛ` | `ν = N^{ε₁}W^{τ'dm}` | `(2m+5)·3·4^{dm}·(2/√κ)·C₁·ν² ≤ N^{τN}`, `C₁ = (1+40d(m+1))6^{d(m+1)}` | slope `τN-2ε₁-2τ'dm = 0.0025` (`ε₀=.1`, `W≤N`), `0.0058` (`W≤N^{1/3}`); eventual, crossover `log₁₀N ≈ 4192/5962/9427` (`m=1/2/4`) |
| 6 | `hνN`, `hνt` | `ν ≤ N`, `(W^{τ'})^{dm} ≤ ν` | `ε₁+τ'dm ≤ 1`; `ν ≥ W^{τ'dm}` by definition | `0.005 ≤ 1`; equality in `hνt` |
| 7 | `D'` (GoodSetN decay, `hFv`) | `D' = D''+2` | `D' ≥ C4+Cn+(2k+1)/𝔠`; `hFv`: `W^{-D'} ≤ νN^{-(2m+4)}` ⇐ `𝔠D' ≥ 2m+4` | `D' ≥ 36/48/72` for `m=1/2/4`, `𝔠=1/6` |
| 8 | `D''` (variance, shift depth) | `D'' = 2Cn+2+2C4+k+(4k+1)/𝔠` | `altBudgetExpQN_of_choice`; C2 `hD`: `(m+1)+2+CQ < D''+1` (F2) | `2C4+(4k+1)/𝔠-1 ≥ 77/101/149` (`+1` from F2) |
| 9 | shift `W^{-D'}+eeShiftErrN ≤ W^{-(D''+1)}` | `D' = D''+2`, `W ≥ 2` | `nqEnd_ev_hδ` at `D''+1`: `C_K ≥ D''+1+2k+5`, `Δ ≤ N^{-C_K}` | fine, `C_K` row 10 |
| 10 | `C_K` | `D₁+2C_P+6k+20+D''` (as `nqGridEndLinN`) | `≥ D''+2k+6`; `AssembledN`: `D₁+4D_Y+k+2C_P+8 ≤ C_K` (`D_Y=k`); `sum_weighted_qErrQN_le` `h1,h2,h3` | `h1,h2,h3 = 42,29,16` (`m=1`), all `≪ D'' ≥ 78`; G2 script |
| 11 | `D_Y, D_t` | `D_Y = D_t = k+1` | `k ≤ D_Y, D_t` (`altBudgetExpQN_of_choice`); C1b absorption `N^{-D_t} ≤ N^{ε₀/2}B_v^k/2` | `B_v ≥ (N(1-v))^{-1} ≥ N^{-1}` (`Params.lean:36`, `Sizes.lean:214`), so need `2 ≤ N^{1+ε₀/2}`; budget run at `ε₀/2` is monotone (only the `≤ε₀/8` rows scale) |
| 12 | regime | `v ≤ 1-g²/L²` (`STCaseI`, `v≤t`), `W⁻¹ ≤ (1-v)/(1-s)`, `N⁻¹ ≤ 1-v` | `(1-v)⁻¹ ≤ η_v⁻¹ ≤ N` from `nqEnd_ev_hη` + `Im m ≤ 1` (`st5_mE_im_le_one`); for `u_p, u_{j+1}` in `[s,v]`: `(1-v)/(1-s) ≤ (1-u_p)/(1-u_{j+1})` | eventual |
| 13 | `KL` | `L^d ≤ W^{KL}` | `qvFormQN_le_of_bounds`, `alt_hkerQN`, `alt_hDclsQN`; also `4 ≤ W^ε`, `log L ≤ W^ε` (C3) | instance: `8000 ≤ 10^{10}` |
| 14 | `C₁, C₂` of C1a | `(1+40d(m+1))6^{d(m+1)}`, `1000(1+d(m+1))²` | `gridDriftQN` at `m ↦ m+1` | constants only |

### (ii) Concrete instance: `sz0` (d=3, `L=4(n+1)`, `W=(2(n+1))^5`) at `n=4`, `m=2` (`k=4`), `E≡0`, `κ=1`, `s≡0`, `v≡1/2`, `K≡4`, `l=3`, `X≡1`, `ε=1/10`, `C=1`, `τ'=1/10`, `ε'=1/5`, `D'=40`, `ν=W`, `τN=2`, `KL=2` (data of `QBudgetBInst`). Eventual targets (`altYGridN`, C1a, C5e): same data with `K ≡ 4` and `sz0_tendsto` (`K+1 ≤ N`).
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2294/inst.py`
```
sz0 sizes: L,W,N -> (20, 100000, 8000000000000000000)
altYGridN: 0<=s<=v<1, K!=0, 1<=X, K+1<=N^C (C=1), eps=1/10>0 -> (True, True, True, True)
C2/C3 regime: v<=1-lam^2/L^2 ; 1/W<=(1-v)/(1-s) -> (True, True)
C4/C5d: N^-1<=1-v ; 1<W ; |E|<=2-kap -> (True, True, True)
hdrift: 1<D, 4<=W^eps', L^d<=W^KL, d W^tau'<=W^eps' -> (True, True, True, True)
hdrift: 1<=nu, (W^tau')^(dm)<=nu<=N -> (True, True, True)
hFv: W^-D' <= nu N^-(2m+4)  (log10 lhs, rhs) -> (-200.0, -146.2, True)
hMLambda: (2m+5)3*4^(dm)(2/sqrt kap)C nu^2 <= N^tauN (log10 lhs, rhs) -> (24.91, 37.81, True)
all 18 boolean hypotheses hold: True
Prec slice u=0 (STXiLK=1, azumaProxy_STXiLKM_zero): 1 <= N^eps*X = 77.6799609715734
```
External hypothesis of `altYGridN` = `Prec(STXiLK_l ≺ X)`, kept a hypothesis (it is `STLKU`-type, `Step34Pins.lean:184`, paper `(Eq:L-KGt-flow)`; `STXiLK = 1+max/B^l ≺ 1` follows from `max ≺ B^l` since `N^τ-1 ≥ N^{τ/2}` once `N^{τ/2} ≥ 2`). Limit check: at `u = 0`, `H = 0` the loops satisfy `𝓛 = 𝒦` (`azumaProxy_STXiLKM_zero`, `AzumaProxyN.lean:609`), `STXiLK = 1 ≤ N^ε X` for every `n` (line 10 shows `n=4`), consistent with `X ≡ 1`. For `u > 0` it is the owed Step 2 gate; I did not check it numerically.
C2 `hD` and the `C4, Cn` rows cannot be evaluated (opaque constants); only `qProxyCn_pos`, `qProxy4C_pos`, `qProxyCQ_pos` (`QProxy.lean:458-473`) are used.

### Gates
`python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2294/gates.py`
```
G1  (ceil(N^CK)+1)*N^-D2 <= N^-(D1+1), D2=D1+CK+2, K+1<=N^(CK+1): log10 of LHS / RHS (CK=100) and truth for CK in 60,100,150 x D1 in 1,2,5
 sz0 n=0 N=2097152: D1=1: -19.0 vs -12.6; D1=2: -25.3 vs -19.0; D1=5: -44.3 vs -37.9 | all 9 (CK,D1) true: True
 szB n=0 N=4096: D1=1: -10.8 vs -7.2; D1=2: -14.4 vs -10.8; D1=5: -25.3 vs -21.7 | all 9 (CK,D1) true: True
G2  eps1=e0/40, tau'=e0/(40dm), tauN=e0/8; K_c=(2m+5)3*4^(dm)*2*C1, C1=(1+40d(m+1))6^(d(m+1)); need K_c N^(2e1+2tau'dm*a)<=N^tauN
 m=1 k=3 K_c=3.02e+10 slope(W<=N)=0.0025 crossover log10N=4192 | slope(W<=N^(1/3))=0.0058 crossover=1797 | hnuN e1+tau'dm=0.005<=1 | hFv D'>=36
   D''-(m+1+2+CQ) at D''=CQ+2C4+k+(4k+1)/c : 77.0 + 2*C4 ; sum_weighted h1,h2,h3 (m'=m+1,D_t=k+1,theta<=1,tauK=1) = 42,29,16  (C_K>=D''+2k+6 dominates: D''>=78)
 m=2 k=4 K_c=8.05e+14 slope(W<=N)=0.0025 crossover log10N=5962 | slope(W<=N^(1/3))=0.0058 crossover=2555 | hnuN e1+tau'dm=0.005<=1 | hFv D'>=48
   D''-(m+1+2+CQ) at D''=CQ+2C4+k+(4k+1)/c : 101.0 + 2*C4 ; sum_weighted h1,h2,h3 (m'=m+1,D_t=k+1,theta<=1,tauK=1) = 50,36,20  (C_K>=D''+2k+6 dominates: D''>=102)
 m=4 k=6 K_c=3.70e+23 slope(W<=N)=0.0025 crossover log10N=9427 | slope(W<=N^(1/3))=0.0058 crossover=4040 | hnuN e1+tau'dm=0.005<=1 | hFv D'>=72
   D''-(m+1+2+CQ) at D''=CQ+2C4+k+(4k+1)/c : 149.0 + 2*C4 ; sum_weighted h1,h2,h3 (m'=m+1,D_t=k+1,theta<=1,tauK=1) = 66,50,28  (C_K>=D''+2k+6 dominates: D''>=150)
C5a hexp identity (cocycle algebra, dim 64, K=6, all tau,m): max relative error = 1.07e-14
C1b szB n=0 K=4: sum w*stepErrN = 1.2448e+35 ; sum w*qErrQN = 5.7332e+45 ; qErr_j >= (1+C Lp) stepErr_j >= 0 for all j: True ; 1+C*Lp=4.606e+10
  => AssembledN-rhs(qErr) - common5 = sum w qErr ; assembledRHSAltQN - common5 = sum w stepErr (>=0): lhs <= rhs + sum w qErr  (=N^-D_t after sum_weighted_qErrQN_le at m'=m+1)
```
- **§95 (3) level check: PASS.** Levels in the sets and in `T2294_altGridEndQN_shape`: `GoodSetN` at crude `Φc` (clauses used: Herm, Dec, (D4), (Vb); its (G2) is `m<k`, `GridGoodN.lean:124`, never length `k`), `GoodLinN` at `Φ₁,Φ₂,Φ₃` (`Φ₂` carries the current length only as the deterministic `B_v^{1/6}XLK n_`, an input), `altYSetN` at length `k-1` with `X(n_-1)`, `cQVAltQN` at `Λ`. `altYGridN`'s `Prec` is at `l` only. No set or hypothesis needs `Ξ̂` at length `k`.
- **§29 (1)-(7): PASS.** (1) `0≤s≤v<1` explicit in `altYGridN` (pin), C2, C3, C5. (2) case (i) only in C2 (`u_p ≤ 1-g²/L²`, `W⁻¹ ≤ (1-u_p)/(1-u_{j+1})`, row 12), C3 (`v ≤ 1-g²/L²`, `W⁻¹ ≤ (1-v)/(1-s)`), C4/C5d (`N⁻¹ ≤ 1-v`); derivation of the last: `(1-v)⁻¹ ≤ η_v⁻¹ ≤ N` eventually (`nqEnd_ev_hη` private, copy; `Im m ≤ 1`). (3) `L^d ≤ W^{KL}` explicit in C2, C3, C4. (4) eventual: C1a, C5e, `altYGridN` only. (5) `Prec` only in `altYGridN`, uniform in `u` inside `P` (`StochDomAt.badSetAt`). (6),(7) constants depend on `(d,m,Λg,κ',KL)`; levels at `B_{u_j}^l`.
- **G1 PASS** (table above; `highProbAt_iInter` needs `Fintype.card (Fin (K n+1)) ≤ N^C`, `hC0 : 0 ≤ C`: `max C 0`, as `gridGood_grid` `GridGoodN.lean:879`). **G2 PASS** (eventual crossover; `hνt` with equality). **C1b PASS** (`assembledRHSAltQN` last term is `stepErrN` at `QBudgetA.lean:117-119`; `gridDriftQN` bounds `rGridQN` by `qErrQN` at `QGridA.lean:2126-2128`; `grep -rn rGridQN RBM3D RBM3D.lean` outside `QGridA.lean`: 0 hits; `qErrQN = qStepErrN … (stepErrN …)`, `qStepErrN ≥ (1+C Lp)·S`, nonneg terms: script line "qErr_j >= ...").
- **G3 field table** (`GridAssemblyHypN` / `AssembledN` at the consumer data): `hE,hu0,hu1,hΔ0` merged gridTime facts; `hexp` C5a (script line, then Lean `stoppedDuhamelQN` `QGridA:2168` + `martIncQN_ae_eq` `QProxy:219`, needs `u_{j+1}<1`); `hκ0,hε0` **not in ticket targets**, `QBudgetA_kappa_nonneg/eps_nonneg` are private (`QBudgetA.lean:125,131`): copy; `hker` C3 `alt_hkerQN` `QDriftA:353` (+`log L ≤ W^ε`, `4 ≤ W^ε`, `d W^{ε'} ≤ W^ε`); `hδ0,hδD0` trivial; `hA0cls` C4 `alt_hA0clsQN` `QDriftA:473` (+crude sup, F1); `hdDrift0` `dDriftAltLinQN_nonneg` `QBudgetB:251`; `hdrift` `alt_hdriftLinQN` `QBudgetB:209` with `hY` from the third component of `altExitTauN`; `hDcls` `alt_hDclsQN` `QDriftB:379` (+two crude sups, F1); `hc_pos` `cQVAltQN` sum `>0`; `hv0,hw0,hY` `yMomentsQUnifN` `QProxy:1468` (C5e); `hstepErr0` `qErrQN ≥ 0` (copy private `nqEnd_stepErrN_nonneg` `NQEndLin:736`); `hR` C1a. `AssembledN` premises: `SubGaussStopN` C2 via `azumaSubGQ_gridExitN` `QProxy:409`, `{j<τ}` measurable `altExitMeasN`, `Z` measurability C5b, `K ≤ ⌈N^{C_K}⌉`.
- **C5d / consumer fit (iv),(v):** `altB45N_levelM` `QLevelsA:376` needs `hY` and `hF` at `u = v_n`: both in the shape's good-walk premise (`∀ j ≤ K n`, includes `j = K n`; `hF` from `goodSetN_LKM_far` at `j = K n`). `nqFlow_core` (`NQEndFlow.lean:642`) feeds `Prec` on `TimeIcc s v n` with constants `Y m n`, exactly the shape of `altYGridN`'s premise; `STXiBoot'` (`:95`) gives it for `m+1 ≤ n_`, i.e. `l = n_-1` with `n_ ≥ 2`. Note for S3-18b: `GridGoodNConcl`'s `hY` is for `m ≤ k` (`GridGoodN.lean:511`), so at `m = n_` its `Prec` at the crude `Φc` must come from the deterministic crude bound (`STXiLKM_crudeN` `NQGood1:959`, `STKbound`), not from `STXiBoot'`.

### Findings for stage 1b (ticket text corrected; none changes a target's truth)
- **F1 (C4 crude sups).** Design (f) takes `‖STLKM_{m+2}(H_j)‖ ≤ W^{C₀}` from `crudeLKM_of_level` on the crude `GoodSetN`; (G2) covers lengths `j<k` only (`goodSetN_LKM_le` has `j < k`), and `alt_hA0clsQN` (`hcrude`) and `alt_hDclsQN` (`hAcr`) need length `k = m+2`. Source: `norm_loopFine_crudeN` `NQGood1:916` (`η^{-k}`) + `STKbound` (`STmaxLKM_crudeN` `:941`), `H` Hermitian (`GoodSetN.1`), `η_u⁻¹ ≤ N`. Also `alt_hDclsQN` has a second premise `hDcr : ‖driftTensorN‖ ≤ W^{C₀}` (`QDriftB.lean:389-397`), absent from the ticket; no merged crude drift lemma (grep), `driftTensorN_norm_le_of_goodSet/_goodLin` need `Φ ≤ N^{C}` but `Φc, Φ₁, Φ₂, Φ₃` are arbitrary in the shape. Plan: C4 takes `hAcr`, `hDcr` as explicit premises; S3-18a2 splits per `n` on `Φ₁+Φ₂+Φ₃ ≤ N^{C₁}` (then `hDcr` from `driftTensorN_norm_le_of_goodLin`; otherwise the conclusion follows from the crude loop bound since `B_v^k ≥ N^{-k}`).
- **F2 (C2 shift depth).** `qvFormQN_le_of_bounds` at `Mee = G'+W^{-D}` returns `κ4(κ4(W^{2Cnε}G'+W^{2Cnε-D}+W^{-D+CQ})+…)`; `qvBdAltQN` (`QBudgetA:70`) lacks `W^{2Cnε-D}`, so the literal "shift `≤ W^{-D''}` ⇒ `≤ cQVAltQN … D''`" is not derivable. Fix: shift hypothesis `W^{-D'}+eeShiftErrN ≤ W^{-(D''+1)}`, `D = D''+1`, `2 ≤ W` (`2W^{-D+CQ} ≤ W^{-D''+CQ}`, `2Cnε ≤ CQ`); then `hQ_altQN ≤ cQVAltQN … D''` exactly. Rows 7-9 use `D' = D''+2`.
- **F3 (class exponent).** In `alt_hkerQN` the `τ'` slot is the class radius exponent of `altClsQN`, which `alt_hA0clsQN/alt_hDclsQN` call `ε'`; C3's `Cls` is `altClsQN … ε' Dc …` (not the `GoodSetN` `τ'`), with `Dc ≤ D'-1` (`4W^{-D'} ≤ W^{-Dc}`).
- **F4.** `hκ0`, `hε0` (G3) need copies of the private nonnegativity lemmas.

### Verdict per target
0 vocabulary: PASS. 1 `measurableAltYSetN`, `mem_of_lt_altExitTauN`, `altExitMeasN`: PASS. 2 `altYGridN` (statement true as pinned: the failure event at each `j` lies in the bad set of `Prec` at `τ=ε`, `map_pathH_eq` `Walk.lean:598` per `j ≤ K n`, `highProbAt_iInter`): PASS. 3 C1a, C1b: PASS. 4 C2: PASS with F2. 5 C3: PASS with F3. 6 C4: PASS with F1. 7 C5a-e: PASS (C5d from `altB45N_levelM` first conjunct; C5a identity checked).

### (a′) Preflight corrections — Tue Oct  6 13:47:03 UTC 2026
- G3 lists `yMomentsQUnifN` (`QProxy.lean:1468`) as the source of `hv0,hw0,hY` at the consumer data. Its premise is `∀ n, STMollifierProps (sz.lam n) C c (ϑ n)`, i.e. `∀ n, 0 < sz.lam n`; `T2294_altGridEndQN_shape` has only `sz.WO 𝔡` (eventual). C5e (`altEnd_yMomentsMax`) therefore carries `hlam : ∀ n, 0 < sz.lam n`. No verdict changes (target 7 stays PASS); the premise is S3-18a2's to meet or avoid (paper-delta candidate `T2294d`).

## (b) Script output (times from `date -u`; worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2294`, branch `t/T2294`)
```
$ git diff --name-only main...t/T2294 ; git rev-parse --short HEAD ; wc -l RBM3D/Induction/QEndA.lean
RBM3D/Induction/QEndA.lean
15d3389
    1967
$ lake build RBM3D.Induction.QEndA   # Tue Oct  6 13:44:25 UTC 2026, exit 0; lines mentioning QEndA.lean with warning/error: 0
info: RBM3D/Induction/QEndA.lean:1967:0: 'RBM.Ind.QEndAInst.altEnd_yMomentsMax_instance' depends on axioms: [propext, Classical.choice,
Build completed successfully (3864 jobs).
$ the 36 `#print axioms` lines at the file end (21 in RBM.Ind, 15 in RBM.Ind.QEndAInst), distinct axiom lists with counts:
  36 [propext, Classical.choice, Quot.sound]
$ grep -nE "sorry|admit|native_decide|maxHeartbeats|^axiom" RBM3D/Induction/QEndA.lean | wc -l   # no set_option maxHeartbeats anywhere (default 200000)
       0
$ registry pre-check (CLAUDE.md §20): `import RBM3D` [+ `import RBM3D.Induction.QEndA`] + `#assert_rbm_axioms`, `lake env lean`, Tue Oct  6 13:44:43-13:45:28 UTC 2026, both exit 0; diff of the two outputs (the trailing phrase ' in `RBM` (compiler-generated declarations excluded)' of line 1 elided):
1c1
< axiom audit: 8499 theorems, 2793 definitions, 0 axioms.
---
> axiom audit: 8533 theorems, 2795 definitions, 0 axioms.
premises found by scanning: 153 (borrowed 1, owed 94, structural 41, refuted 6, superseded 11).   # identical before and after; no registry line added
$ statement scripts (`stmt_diff.py`: definitions and `altYGridN` statement of QEndA.lean vs the check file §2, comments dropped, whitespace collapsed)
altYSetN IDENTICAL
altExitTauN IDENTICAL
altYGridN statement IDENTICAL
in-file T2294_altYGridN copy vs check file IDENTICAL
$ lake env lean stmt.lean  # §2 of the check file + `example : RBM.Ind.T2294Check.T2294_altYGridN := @RBM.Ind.altYGridN`  → exit 0
  (QEndA.lean:1424-1435 also compiles the same `example : T2294_altYGridN := @altYGridN` against an in-file verbatim copy)
$ name-clash grep: `grep -rnw --include=*.lean <name> RBM3D RBM3D.lean`, outside QEndA.lean, for the 36 public names (+ `QEndAInst`)
37 names checked, 0 hits
$ target statements (script `extract.py`: file line, signature up to `:= by`, whitespace collapsed, middle elided as [...] when longer than 300 chars)
L54 altYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n)
    (sz.W n)) ℂ)
L61 altExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ)
    (n : ℕ) : PathΩ sz → ℕ
L90 measurableAltYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) : MeasurableSet (altYSetN sz n E u l Y)
L100 mem_of_lt_altExitTauN {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} {k : ℕ} {Γ Λ Φc Φ [...] SetN n (E n)
    (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩ GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃
    n) ∩ altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n)
L110 altExitMeasN {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ)
    : MeasurableSet[filt sz j] {ω | j < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω}
L194 altYGridN : ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ), (∀ n, 0 ≤ s n) [...]  ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε → HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n, pathH sz s v K n j ω ∈ altYSetN sz n (E n)
    (gridTime s v K n j) l (((sz.size n : ℕ) : ℝ) ^ ε * X n)})
L247 gridDriftQN_envelope {d : ℕ} (sz : Sizes d) (κ : ℝ) (hκ : 0 < κ) (m : ℕ) (hm : 1 ≤ m) (τK : ℝ) (hτK  [...] ) ((1 + 40 *
    ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1000 * (1 + ((d * (m + 1) : ℕ) : ℝ)) ^ 2) (((sz.size n : ℕ) : ℝ) ^ τK *
    (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j
L350 assembledRHSAltQN_qErr_le {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (Λg κ' KL C c [...] : ℕ) : ℝ) ^ τK
    * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) j ≤ assembledRHSAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd
    δ0 δD D'' D_Y τK εq X0 a + ((sz.size n : ℕ) : ℝ) ^ (-D_t)
L442 hQ_altQN {d m : ℕ} (Λg κ' KL C c : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ') (hKL : 0 < KL) (hC  [...] mitian →
    gridStep s v K n * (((m + 1 + 1 : ℕ) : ℝ) * qvFormQN sz n ϑ (E n) (gridTime s v K n (j + 1)) (gridTime s v K n p) σ M
    a) ≤ (cQVAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ D'' p a j : ℝ)
L580 subGaussStop_altQN {d m : ℕ} (Λg κ' KL : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ') (hKL : 0 < KL [...]  s v K n j
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω) p a j (cQVAltQN sz E s v K n m Λg κ' KL ((1 + 40 * ((d * (m
    + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2) ε Γ Λ D'' p a j)
L632 alt_hkerGridQN {d m : ℕ} (Λg κ' KL : ℝ) (hd : 3 ≤ d) (hΛg : 0 < Λg) (hκ' : 0 < κ') (hKL : 0 < KL) (s [...]  n i) (gridTime
    s v K n m') X a‖ ≤ kappaAltQN d (m + 1 + 1) Λg κ' KL (sz.lam n) ((sz.W n : ℕ) : ℝ) ε (gridTime s v K n) i m' * M +
    epsAltQN d (m + 1 + 1) Λg κ' KL ((sz.W n : ℕ) : ℝ) i m' * δ
L665 alt_hdriftGridQN : ∀ (d m : ℕ) (Λg KL : ℝ), 3 ≤ d → 0 < Λg → 0 < KL → ∀ (sz : Sizes d) (n : ℕ) (σ :  [...] σ j ω b‖ ≤
    dDriftAltLinQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) (qProxyCn d (m + 1) Λg KL ((1 + 40 * ((d
    * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2)) ε' D' τN X
L709 alt_hA0clsGridQN {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) (m : ℕ) (K C₀ ε' D' : ℝ) (hε' : 0 < ε') {n : ℕ} [...] ClsQN d (sz.L
    n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) 0 (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (aTrueQN sz E s v Kg n
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ 0 ω)
L735 alt_hDclsGridQN : ∀ (d m : ℕ) (Λg K C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' → ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (s [...] d (sz.L n)
    (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dGridQN sz E s v Kg
    n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω)
L769 altEnd_crudeSup {d : ℕ} (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)  [...] )), ‖sz.STKloop
    n E u σ a‖ ≤ MK) (hη : (etaT E u)⁻¹ ^ k + MK ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) : ‖fun b : Fin k → Zd d
    (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀
L785 altEnd_driftSup {d : ℕ} (sz : Sizes d) (n : ℕ) {E u Γ Φ₁ Φ₂ Φ₃ C₀ : ℝ} {k : ℕ} (hk : 2 ≤ k) {H : Mat [...]  k Γ Φ₁ Φ₂ Φ₃)
    (hW : dDriftLinN sz n E u k Γ Φ₁ Φ₂ Φ₃ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) (σ : Fin k → Bool) : ‖fun b : Fin k → Zd d (sz.L n)
    => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀
L805 altEnd_hexp {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2) (hs0 : 0 ≤ [...] Time s v K n (j
    + 1)) (gridTime s v K n m') ((gridStep s v K n : ℂ) • dGridQN sz E s v K n ϑ σ j ω + zVecQN sz E s v K n j ϑ σ ω +
    yVecQN sz E s v K n j ϑ σ ω + rGridQN sz E s v K n ϑ σ j ω)
L836 altEnd_stronglyMeasurable_zVecQN {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ϑ : ℝ → (Fin (m + 1 + 1)
    → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool) : StronglyMeasurable[filt sz (j + 1)] (fun ω => zVecQN sz E s v K n
    j ϑ σ ω)
L851 altEnd_aFroz_eq_aTrue {d m : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| ≤ 2)  [...] (Fin (m + 1 +
    1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1 + 1) → Bool) (τ : PathΩ sz → ℕ) (ω : PathΩ sz) (hτ : K n ≤ τ ω) : aFrozQN sz
    E s v K n ϑ σ τ (K n) ω = aTrueQN sz E s v K n ϑ σ (K n) ω
L867 altEnd_unQ {d : ℕ} (hd : 3 ≤ d) (m : ℕ) (sz : Sizes d) (n : ℕ) (E u κ Γc Λc Φc τ' D' ν X τN C c : ℝ) [...]  Zd d (sz.L n))
    : ‖sz.STLKM n E u H σ a‖ ≤ ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a‖ +
    ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X)
L926 altEnd_yMomentsMax {d : ℕ} (sz : Sizes d) {κ τR : ℝ} {E s v : ℕ → ℝ} (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ [...] dTime s v K n)
    τ (K n) (fun j ω => yVecQN sz E s v K n j (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ ω) (fun _ => gridStep
    s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2)
$ compiled nonempty instances (file line:name; all in namespace RBM.Ind.QEndAInst): 1395:altYSetN_instance 1405:altYGridN_instance 1448:gridDriftQN_envelope_instance 1476:assembledRHSAltQN_qErr_le_instance 1555:hQ_altQN_subGaussStop_altQN_instance 1685:alt_hkerGridQN_instance 1706:alt_hdriftGridQN_instance 1733:alt_hA0clsGridQN_instance 1771:alt_hDclsGridQN_instance 1846:altExitMeasN_instance 1855:altEnd_hexp_instance 1878:altEnd_stronglyMeasurable_zVecQN_instance 1885:altEnd_aFroz_eq_aTrue_instance 1896:altEnd_unQ_instance 1913:altEnd_yMomentsMax_instance
  coverage: altYSetN, measurableAltYSetN (altYSetN_instance); altExitMeasN (altExitMeasN_instance); altYGridN; C1a; C1b; C2 hQ_altQN and subGaussStop_altQN (one instance);
  C3; C4a-c; C5a-e; mem_of_lt_altExitTauN is applied directly at QEndA.lean:1762, 1813, 1829 (alt_hA0clsGridQN_instance, alt_hDclsGridQN_instance); altEnd_crudeSup (via the
  private crude_u, :1138) and altEnd_driftSup (:1829) are applied in those two.  One instance in full (`altYGridN_instance`, QEndA.lean:1405-1411):
theorem altYGridN_instance
    (hP : Prec sz0 (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n)
      (fun n u ω => STXiLK sz0 n ((fun _ => (0 : ℝ)) n) (u : ℝ) 3 ω) (fun n _ _ => (fun _ => (1 : ℝ)) n)) :
    ∃ n : ℕ, pathP sz0 {ω | ∀ j ≤ 4, pathH sz0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j ω ∈
        altYSetN sz0 n 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j) 3
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1)}ᶜ ≤
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
```

## Narrative (facts from the files and the tool log above)
- **Delivered.** `RBM3D/Induction/QEndA.lean` (1967 lines, branch `t/T2294`, 4 commits, last `15d3389`; `git diff --name-only main...t/T2294` is that file only): 2 definitions, 19 theorems, 15 instances; no `sorry`, no `maxHeartbeats`, no registry change.
- **Target 2 `altYGridN`** has exactly the pinned statement (script diff, compiled `example`). Proof: `Prec.whp` at the exponent `ε`; `STXiLKM ≤ Z ⇒ ‖(𝓛-𝒦)^{(l)}‖ ≤ (Z-1)B^l ≤ Z B^l` (copy of `QLevelsB_norm_STLKM_le_of_XiLKM`, `B > 0` by `st_Bctl_pos`); transfer by `map_pathH_eq` at each `j ≤ K n`; `highProbAt_iInter` (pattern `gridGood_grid`, `GridGoodN.lean:879`; `nqLin_grid`, `NQLin.lean:541`).
- **C1.** C1a is `gridDriftQN` at `m ↦ m+1` per `j`, its `hB` from the worst-grid-index envelope block of `gridDriftN_envelope` (`GridEnvelopeN.lean:126-151`), premise `STKbound E` kept as in T2153. C1b is the bridge (`assembledRHSAltQN` carries `stepErrN`; AssembledN's right side with `stepErr := qErrQN` is bounded by it plus `N^{-D_t}`); the sup term is a variable `Xs ≤ X0` (kappa ≥ 0).
- **C2 departs from the ticket text in two premises.** (i) the literal shift `W^{-D'} + eeShiftErrN ≤ W^{-D''}` does not give `cQVAltQN … D''` (F2, preflight): the hypothesis is `W^{-D'} + eeShiftErrN ≤ W^{-(D''+1)}` with `2 ≤ W`, `qvFormQN_le_of_bounds` at `D := D''+1` (`T2294c`); (ii) `qvFormQN_le_of_bounds` needs `M_ee ≤ W^{C₀}`, so `hQ_altQN` has `hMee : Γ(ΓΛ)B_{u_{j+1}}^{2k}/η_{u_{j+1}} + W^{-(D''+1)} ≤ W^{C₀}` and `hW₀`, `hD` on the abstract `qProxyW0`, `qProxyCQ`.
- **C3** uses the class exponent `ε'` (F3): `d W^{ε'} ≤ W^ε`; regime premises `v n ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-v n)/(1-s n)` explicit.
- **C4** (F1): `(G2)` of `GoodSetN` covers lengths `< k`, so `alt_hA0clsGridQN`, `alt_hDclsGridQN` keep the merged crude-sup premises (`hcrude`; `hAcr`, `hDcr`); two public derivations are added, `altEnd_crudeSup` (Hermitian + `‖𝒦‖ ≤ M_K` + `η⁻¹^k + M_K ≤ W^{C₀}`, via `STmaxLKM_crudeN`) and `altEnd_driftSup` (`GoodLinN` + `dDriftLinN ≤ W^{C₀}`); `alt_hDclsGridQN_instance` discharges both premises for every grid time from the exit-family membership.
- **C5.** C5a: `stoppedDuhamelQN` + `martIncQN_ae_eq` (`ae_all_iff`); C5b: `gridAsm_stronglyMeasurable_ZvecN` ∘ continuous `STQop`; C5c: `GridDuhamelN_Ugen_self`; C5d `altEnd_unQ`: `altB45N_levelM` first conjunct, `hexp` of `ϑ` from `STMollifierProps` (copy of `QBudgetB.lean:178-193`); C5e: `yMomentsQUnifN` over `σ` with the sup of constants, premise `∀ n, 0 < sz.lam n` (`T2294d`).
- **Instances.** `Prec` is the only hypothesis left (`altYGridN_instance`, the owed `STLKU`-type gate; limit check at `u = 0`: `STXiLK = 1 ≤ N^ε X`, section (a)); C1a uses the proved `stKbound_holds`. The C2/`SubGaussStop` instance has abstract constants (`qProxyCQ`, `qProxyW0`): it takes `D'' = 5 + C_Q`, `n` from `exists_nat_ge` and the grid `K n = ⌈N^{D''+14}⌉`, window `[0, 1/2]` not collapsed (`Δ > 0` in the statement), `hδ` from a fixed-`n` copy of the body of `nqEnd_ev_hδ` (`NQEndLin.lean:558-647`). I found no fixed-grid way to discharge `hδ` for an abstract `C_Q`.
- **Size.** 1967 lines against the ticket's 1000/1200/1450: targets §0-§7 are lines 50-949; §8 is lines 950-1926: numeric helper copies 959-1226, fixed-`n` shift estimate 1227-1389, instance statements and proofs 1391-1926.
- **Provenance.** No RBM1D/RBM2D file was opened or copied (the ticket's RBM2D `AltEndCompose.lean` was not read; no RBM1D/RBM2D diff-stat applies). Patterns come from merged RBM3D files (last-commit hashes, `git log -1`): GridEnvelopeN a438a51, GridGoodN 2f246bf, NQLin d783ee3, NQGood2 cc96b69 (`hQ_nonAltN :519`, `qvFormN_le_of_goodSetN_shiftN :435`), NQGood1 691566a, NQEndLin cef761a (`nqEnd_stepErrN_nonneg :736`, `nqEnd_yMomentsMax :1028`, shift chain `:127-152, 459-482, 533-647`), QBudgetA b39ac53 (`QBudgetA_kappa_nonneg :125`), QBudgetB acb4f83, QDriftB c01b292 (instance helpers `:451-754`), QProxy 9a207a1.

## (c) Mathlib names used, each verified by `#check @name` (`lake env lean names.lean`, Tue Oct  6 13:47:37-13:47:40 UTC 2026, exit 0)
- `MeasurableSet.iInter`
- `measurableSet_le`
- `MeasureTheory.Measure.map_apply`
- `MeasureTheory.measure_mono`
- `Real.rpow_le_rpow_of_exponent_le`
- `Real.rpow_add_one`
- `Real.le_coe_toNNReal`
- `Real.rpow_le_one_of_one_le_of_nonpos`
- `MeasureTheory.ae_all_iff`
- `Nat.ceil_pos`
- `Nat.le_ceil`
- `continuous_finsetSum`
- `continuous_pi`
- `Measurable.stronglyMeasurable`
- `pi_norm_le_iff_of_nonneg`
- `MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt`
- `Set.indicator_of_notMem`
- `inv_anti₀`
- `div_le_div₀`
- `pow_le_pow_left₀`
- `one_le_pow₀`
- `inv_le_one_of_one_le₀`
- `exists_nat_ge`
- `Filter.Eventually.exists`
- `Real.one_le_rpow`
- `Nat.eq_zero_of_not_pos`
- `MeasurableSet.const`
- `Real.rpow_natCast`
- verified deprecated: `continuous_finset_sum` (warning: use `continuous_finsetSum`); verified absent: none other.

## (d) Open issues and paper-delta candidates
- `T2294a` (expected): the `hY` input of `(y27kasdfg)`/`(A4)`/`(A5)` at length `n_-1` is a separate w.h.p. event at the deterministic level `N^ε XLK(n_-1)` (`altYGridN`), transferred to the grid; the paper uses `≺` at every time implicitly.
- `T2294b` (expected): the alternating one-step remainder is the `𝒬`-error `qErrQN`, not `stepErrN`; bridge `assembledRHSAltQN_qErr_le`; `assembledRHSAltQN`/`budgetAltQN` (T2279) are unchanged. Flag for the T2279 audit trail.
- `T2294c`: `hQ_altQN`/`subGaussStop_altQN` need the shift `W^{-D'} + eeShiftErrN ≤ W^{-(D''+1)}` (not `W^{-D''}`), `2 ≤ W`, and `M_ee ≤ W^{C₀}` (polynomial growth of `Γ(ΓΛ)B^{2k}/η`). For S3-18a2: for a huge level `Λ` (arbitrary in the shape) split per `n` as in preflight F1; `D' = D''+2` makes the shift hypothesis `nqEnd_ev_hδ` at `D''+1` (its fixed-`n` body is `altEnd_shift_fixed`, private; copy it).
- `T2294d`: the merged `yMomentsQUnifN` needs `∀ n, STMollifierProps (lam n) …`, hence `∀ n, 0 < sz.lam n` (`altEnd_yMomentsMax` carries it); `T2294_altGridEndQN_shape` has only `sz.WO 𝔡` (eventual). S3-18a2 or the dispatcher must add the premise, or `yMomentsQUnifN` must become eventual in `lam`.
- `T2294e`: the crude sups `‖(𝓛-𝒦)^{(m+2)}(H_j)‖`, `‖driftTensorN‖ ≤ W^{C₀}` are not given by `(G2)` of `GoodSetN` (lengths `< k`): `alt_hA0clsGridQN`/`alt_hDclsGridQN` take them as premises; derivations `altEnd_crudeSup` (needs an `𝒦`-loop bound `M_K` at every grid time, e.g. from `exists_norm_Kcal_le_win` as in `crude_u`) and `altEnd_driftSup` (needs `dDriftLinN ≤ W^{C₀}`, a bound on `Φ₁,Φ₂,Φ₃`).
- `T2294f`: the kernel class of the alternating chain has radius exponent `ε'` (`altClsQN … ε' Dc`), distinct from the `τ'` of `GoodSetN`; the chain of premises is `d W^{τ'} ≤ W^{ε'}` (C4), `d W^{ε'} ≤ W^ε` (C3), `4W^{-D'} ≤ W^{-Dc}` (C4c), `2W^{-D'} ≤ W^{-Dc}` (C4b), `1 < Dc` (C3).
- For S3-18a2: the fields `hκ0`, `hε0` (nonnegativity of `kappaAltQN`, `epsAltQN`) need copies of the private `QBudgetA_kappa_nonneg`, `QBudgetA_eps_nonneg` (`QBudgetA.lean:125,131`; here only the kappa copy exists, private); `hc_pos` (`cQVAltQN` sum `> 0`) and `hstepErr0` (`qErrQN ≥ 0`) are not provided here; `N⁻¹ ≤ 1 - v_n` is a premise of C4a, C5d.
- Open: `Prec` of `altYGridN` is supplied by S3-18b from `STXiBoot'` at length `n_-1`; the owed `STLKU`-type gate stays owed.
