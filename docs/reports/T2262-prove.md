Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 06:41:23 UTC 2026

### (i) Exponent table
`N = sz.size n = (WL)^d`, `η_u = (1-u) Im m`, `B_u = Bctl n u = W^{-d}[(g²+1-u)⁻¹ + (L^d(1-u))⁻¹]` (`ContinuityNet.lean:691`, `cont_Bctl_eq`). Slack numbers are from the script in (ii) (`sz0`, `zSeq`, `d=3`).

| # | quantity | value / form | constraint | slack |
|---|---|---|---|---|
| 1 | `κ' = min κ 1` (S1Std `κ`) | instance 1/2 | `hκ: 0<κ'`; `hE` at `E≡0`: `\|0\| ≤ 2-κ'` iff `κ' ≤ 2` | `κ' ≤ 1 ≤ 2` always: slack ≥ 1 |
| 2 | `τ = ε/2` | 1/20 | `hτ: 0<τ` | — |
| 3 | `RangeCond (ε/2) t` | `1-t_n ≥ N^{-1+ε/2}` ev. | `1-t ≥ 1-t₀ = Im z/(Im m+Im z) ≥ Im z/2 ≥ N^{-1+ε}/2 ≥ N^{-1+ε/2}` iff `N^{ε/2} ≥ 2` iff `N ≥ 2^{2/ε}` (= 2^20); needs `Im m ≤ \|m\| ≤ 1`, `Im z ≤ 1` (`BAdom`; `Im m ≥ κ>0` forces a solution since `BAm = 0` otherwise, then `BAself_norm_le_one`) | `N_0 = 2^21`: `N^{ε/2} = 2.07` (n=0), `3.86` (n=1): factor 1.04 at n=0; direct `1-t = 1/3 ≥ N^{-0.95} = 9.9e-7` |
| 4 | `𝔠d` | 1/100 | `0 < 𝔠d ≤ 1/100` | 0 (equality allowed) |
| 5 | `STConStInd 𝔠d s t` | `B_t^{𝔠d} ≤ (1-t)/(1-s) < 1` ev. | `s<t<1`; at `s≡1/2, t≡2/3`: `B_t^{1/100} ≤ 2/3` | fails `n ≤ 7` (`n=7`: 0.6670 > 0.6667), holds for all `n ≥ 8` (`N_8 = 3.1e23`); at `s≡0.64`: holds from `n=0` (`N=2^21`) |
| 6 | window `t ≤ t₀` | `t≡2/3`, `t₀ = Im m/(Im m+Im z)` | `0 ≤ s ≤ t ≤ t₀ < 1` (`BAflow_T0_bounds`) | `t₀ = 0.69374` (n=0), `25/36` (n≥1): ≥ 0.027 |
| 7 | `hc,h𝔡,hN,hB,hWO` | from `BAFlow.1 = Admissible` | `0<𝔠`, `0<𝔡`, `N→∞`, `W ≥ N^𝔠`, `(eq:WO)` | merged `sz0_admissible` |
| 8 | T1 fields really read | `hκ` (`s1_c1_pos`, positivity only), `hτ,hc,h𝔡,h𝔠d,h𝔠d',hs0,hst,ht1,hN,hB,hWO,hCond,hR`; **not** `hE` | `hE` read only at `s1_h55:744`, `s1_LI:783,809,830` (replaced by `baBoot_LI`) | see (ii) grep |
| 9 | T2 | `Im ztOf m E v = (1-v) Im m` | `v ≤ b < 1`, `Im m>0`: clamp `z(min(v,b))`, `H_v = lam0·Ψ + √v X` Hermitian, continuous | `Im z ≥ (1-b) Im m > 0` |
| 10 | T3 constants | `C' = 2C+10` (depends on `C` only); `η_u⁻¹ ≤ N/κ`; `‖z_u-z_{u'}‖ = \|u-u'\| \|m\| ≤ \|u-u'\|` | `(N/κ)²(2N²+1)\|Δ\|^{1/2} ≤ 3κ⁻²N⁴ N^{-C'/2} = 3κ⁻²N^{-1}N^{-C} ≤ N^{-C}` iff `N ≥ 3κ⁻²` (band: `η⁻¹ ≤ N²`, `C' = 2C+14`; BA bound is better, any `C' ≥ 2C+10` works) | `κ=1/2`: `N ≥ 12` vs `N_0 = 2^21` |
| 11 | T3 range | `0 ≤ u,u' ≤ 1-N⁻¹`; `Δ ≤ N^{-C'} ≤ 1`; `\|√u-√u'\| ≤ √Δ` | `η_u ≥ κ/N` (`1-u ≥ N⁻¹`, `Im m ≥ κ`) | — |
| 12 | T3 good event | `contGood (sz.withLam 0)`, `P(Ξᶜ) ≤ 4N²e^{-N²/2} ≤ N^{-D}` ev. | `cont_good_compl`, `cont_highProbAt_good` are stated for every `Sizes` (variance ≤ 1 uses only `sum_sbKernelR`, no hypothesis on `lam`); `seqHflowBA lam0 n u ω = lam0·Ψ + of(seqHflow (sz.withLam 0) n u ω)` (`BlockAnderson.lean:83`) so `H_u-H_{u'} = (√u-√u')X`, `‖X‖ ≤ 2N²` | — |
| 13 | T4 | `C₁ ≤ C₂ ⇒ 1(∀‖G‖≤C₁) ≤ 1(∀‖G‖≤C₂)` | by cases on the two `if`s | trivial |
| 14 | T5 constant | `2·9^d+1 = 1459` (`d=3`) | diag `Nτ·Nτg`; off-diag `Nτ(2·9^d Nτg + W^{-d})`, `W^{-d} ≤ g ≤ Nτg` (`Nτ ≥ 1`); `#ball ≤ 3^d` (`s1_near_card`), 2 orientations | off-diagonal: **zero slack** (equals `(2·9^d+1)Nτ²g`); diagonal slack factor 1459 |
| 15 | T5 events | `‖GM‖ ≤ 2a ≤ W^{-c'}` gives `indMax=1`; `‖G‖ ≤ C₀` gives `omegaC=1` | S2b2b: `C₀ = 1+κ⁻¹`: `‖G_xy‖ ≤ ‖M_xy‖+‖GM_xy‖ ≤ (Im m)⁻¹ + 1` (`baM_entry_le`), `2a ≤ 1` | `1+1/Im m = 2.0005 ≤ 3` (n=0) |
| 16 | T6 loops | `A = 6k+16`, `Cv = k+1`, `ε_n = N^{-k}`, `V = (σ,a)`, `#V ≤ N^{k+1}` | `N ≥ max(6k, 2^k, 1/κ)`; `η_t⁻¹ ≤ N/κ ≤ N²` (so the band constants of `cont_LP_close` apply) | `N_0 = 2^21` vs `6k=36` (k=6) |
| 17 | T6 weak law | `A = 40`, `Cv = 2`, `ε_n = N^{-1/4}`; `1+N^{1-40} ≤ 11/10`; `3N⁶N^{-20} ≤ N^{-1/4}` | `(1-t)⁻¹ ≤ N` from `RangeCond τ t`, `τ>0` | `τ = 1/2`: `N^{-1/2} = 6.9e-4 ≤ 1/3` |
| 18 | T6 lower bounds | `ε_n ≤ ζ`: `B_s^{k-1} ≥ N^{-k}`, `B_u^{1/4} ≥ N^{-1/4}` | `cont_inv_size_le_Bctl` (`0 ≤ s<1`), `(1-s)/(1-u) ≥ 1`; no energy anywhere | `N⁻¹ = 4.8e-7 ≤ B_s = 6.2e-5` (n=0) |
| 19 | T6 helper status (P4) | public in `ContinuityNet`: `cont_core`, `cont_good_compl`, `cont_highProbAt_good`, `cont_green_diff`, `cont_green_flow_diff`, `cont_abs_sqrt_sub_sqrt_le`, `cont_norm_Xmat_le`, `cont_norm_blockMat_Xmat_le`, `cont_blockMat_sub/smul`, `cont_inv_size_le_Bctl`, `cont_Bctl_ratio`, `cont_inv_add_one_sub_ratio`, `cont_sqrt_abs_le`, `cont_gap`, `cont_pow_mul_rpow`, `cont_eventually_tail`, `cont_Gres_true/false_eq_green`, `cont_norm_green_le` | **private in `Continuity.lean`, to copy as `BASetup_*`**: `cont_entry_diff:66`, `contWord:89`, `contWord_cons:95`, `cont_word_norm:100`, `cont_word_diff:119`, `cont_loopFine_eq:158`, `cont_loopAbs_diff:170`, `cont_one_add_pow_le:230`, `cont_LP_zeta_ratio:249`, `cont_LP_low:286`, `cont_WL_low:307`, `cont_LP_eventually:315`, `cont_eta_inv_le:346` (BA: `≤ N/κ ≤ N²`), `cont_LP_close:365`, `cont_STGM_eq:423` (BA: unnecessary, `GM` is `G-M` by definition), `cont_WL_close:438` | the energy-bound helpers `cont_bulk`, `cont_eta_le_abs_im`, `cont_norm_spectralZ_sub` (`ContinuityNet:772, 618, 626`, public) are replaced by `κ ≤ Im m`, `\|m\| ≤ 1` |

Findings. **P1** (T1): confirmed, see (ii) grep. **P2**: the BA bound is `η⁻¹ ≤ N/κ` (row 10); the good-event lemmas hold for every `Sizes`, applied at `sz.withLam 0` (`SeqΩ`, `size`, `slice` do not depend on `lam`); `seqHflowBA` is `lam0·Ψ + seqHflow (withLam 0)` entrywise (`BlockAnderson.lean:83-85`). **P3**: hand count in rows 14-15; scalar path `H_u-H_{u'}` has no `M`, since `M = BAMfine` is time independent (`FlowPins.lean:253`), so `GM_u - GM_{u'} = G_u - G_{u'}`. **P4**: row 16-19. **P5**: no further interface lemma is needed in this ticket; S2b2b needs two private ≈15-line facts derived from targets 2 and 3 (sup over entries of `‖GM‖` is continuous by T2 and a finite sup; `‖GM_u‖_max ≤ ‖GM_{u'}‖_max + δ` from `∀ x y, ‖BAGt_u-BAGt_{u'}‖ ≤ δ`, band `s1xM_le_add`, `Step1Setup.lean:954`) and `‖BAmF‖ ≤ 1` from `BAself_norm_le_one` at real `z=E` (`Im BAmF ≥ κ>0` gives a solution). Paper-delta candidates for the report (d): T2262a, T2262b as in the ticket.

### (ii) One concrete nondegenerate instance
Data: `d=3`, `sz0` (`L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^{-6}`, `N_0 = 2^21`), `zSeq = zS` (`w = 6i/5`, `z+m = w`), `κ=1/2`, `ε=𝔡=1/10`, `𝔠=1/6`, `𝔠d=1/100`, `s≡1/2`, `t≡2/3`, `τ=1/2` (T6), `lam0 = BAflowLam0`, `E = BAflowEs`. `(F)` is the limit computation for the external hypothesis `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)`; the stochastic premises of T6 (`PerTimeDomAt`) and `STConStInd` are the other hypotheses (`STConStInd` by merged `s1Setup_conStInd_const`; the sequence-level statement is `∀ᶠ`).
```
$ grep/awk (P1): enclosing declaration of every read of S1Std.hE / .hκ in RBM3D/Induction/Step1Setup.lean
Step1Setup.lean:617: theorem s1_c1_pos
Step1Setup.lean:744: theorem s1_h55
Step1Setup.lean:783: theorem s1_LI
Step1Setup.lean:809: theorem s1_LI
Step1Setup.lean:830: theorem s1_LI
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2262/inst.py
== (A) flow data of sz0, zSeq (BAdom at kappa=1/2, eps=1/10), target 1 fields
n=0 N=2.097e+06 Im m(z)=0.8325 |m|=0.8325 Im z=0.3675 t0=0.69374 | 1-t=0.3333 >= 1-t0=0.3063 >= Imz/2=0.1838 >= N^-0.9/2=1.02e-06 >= N^-0.95=9.87e-07 ; N^(eps/2)=2.07>=2
n=1 N=5.498e+11 Im m(z)=0.8333 |m|=0.8333 Im z=0.3667 t0=0.69444 | 1-t=0.3333 >= 1-t0=0.3056 >= Imz/2=0.1833 >= N^-0.9/2=1.36e-11 >= N^-0.95=7.03e-12 ; N^(eps/2)=3.86>=2
n=5 N=2.130e+20 Im m(z)=0.8333 |m|=0.8333 Im z=0.3667 t0=0.69444 | 1-t=0.3333 >= 1-t0=0.3056 >= Imz/2=0.1833 >= N^-0.9/2=2.53e-19 >= N^-0.95=4.88e-20 ; N^(eps/2)=10.4>=2
RangeCond threshold: N^(eps/2)>=2 <=> N>=2^(2/eps) = 2^20 ; N_0=2^21.0
== (B) STConStInd sz0 (1/100) (s=1/2) (t=2/3): Bctl(t)^cd <= (1-t)/(1-s)=2/3 < 1 ; first n:
   n=0 Bctl^0.01=0.9113 ok=False
   n=5 Bctl^0.01=0.6965 ok=False
   n=7 Bctl^0.01=0.6670 ok=False
   n=8 W=1889568 N=3.148e+23 Bctl=4.447e-19 Bctl^0.01=0.6554<=0.6667 : first n
   holds for all n in [8,200)
== (C) target 3: C'=2C+10, Q=eta^-1<=N/kappa, N>=3/kappa^2
n=0 Im m(E,g0)=0.99949 |m|=0.99949 ; C=1,C'=12: (N/k)^2(2N^2+1)N^-6=1.82e-12 <= N^-1=4.77e-07
n=1 Im m(E,g0)=1.00000 |m|=1.00000 ; C=1,C'=12: (N/k)^2(2N^2+1)N^-6=2.65e-23 <= N^-1=1.82e-12
n=5 Im m(E,g0)=1.00000 |m|=1.00000 ; C=1,C'=12: (N/k)^2(2N^2+1)N^-6=1.76e-40 <= N^-1=4.70e-21
toy BA flow (L=4,W=1,N=64, g0=0.3,E=0.1, Im m=0.8272): 300 random (X,u,u'): max ||G_u-G_u'||/[eta^-2(|sqrt u-sqrt u'| ||X||+|u-u'||m|)] = 0.428 <= 1
== (D) target 5 constants: 2*9^d+1 = 1459
generic Ntau=3,g=2: diag 18.0, offdiag 26244.0 <= 26262.0
u=0 n=0: max|G_0-M|=0.0 (=0<=2a=1/32<=W^-1/20=0.841); max|G_0|=0.9995<=C0=1+1/Im m=2.0005<=3 ; loop bound eta^-2 W^-3=3.055e-05 <= Ntau*g=2W^-3=6.104e-05
u=0 n=1: max|G_0-M|=0.0 (=0<=2a=1/32<=W^-1/20=0.707); max|G_0|=1.0000<=C0=1+1/Im m=2.0000<=3 ; loop bound eta^-2 W^-3=9.313e-10 <= Ntau*g=2W^-3=1.863e-09
== (E) target 6 eventual numerics (N=N_n, k fixed), band constants A=6k+16 (loops), A=40 (weak law)
n=0 N=2.097e+06: RangeCond tau=1/2: N^-1/2=6.9e-04<=1-t=1/3; (1-t)^-1=3<=N; eta_t^-1=3/Im m<=N/kappa<=N^2 ; loops k=1,2,3,6 and weak-law A=40 inequalities hold ; N^-1<=Bctl_s=6.196e-05
n=1 N=5.498e+11: RangeCond tau=1/2: N^-1/2=1.3e-06<=1-t=1/3; (1-t)^-1=3<=N; eta_t^-1=3/Im m<=N/kappa<=N^2 ; loops k=1,2,3,6 and weak-law A=40 inequalities hold ; N^-1<=Bctl_s=1.866e-09
== (F) hwin = BAWinBulk sz0 zSeq (1/3) (1/2): min_{g' in [sqrt(1-c1) g0, g0]} Im m(E_n,g') >= 1/2, and the limit n->oo (g'->0: m^2+E m+1=0, E_n=-Re m_S/sqrt(t0)->0, Im m->sqrt(4-E^2)/2->1)
n=0 g0=1.30e-02 E_n=3.12e-18 min Im m on window=0.99949 (>=1/2); free limit Im m(E_n,0)=1.00000000
n=1 g0=2.03e-04 E_n=2.44e-20 min Im m on window=1.00000 (>=1/2); free limit Im m(E_n,0)=1.00000000
n=5 g0=2.79e-07 E_n=1.22e-22 min Im m on window=1.00000 (>=1/2); free limit Im m(E_n,0)=1.00000000
```

Checks done by the script and what they show: (A) rows 1-3, 6 at `n=0,1,5` (all assertions passed); (B) row 5, the first admissible `n` for `STConStInd` at `s≡1/2` is 8 (`N=3.1e23`), so the compiled instance uses `STConStInd` as the merged `∀ᶠ` statement, not a value at small `n`; the same statement at `s≡0.64` holds from `n=0` (`alt.py`: `n0 = 0`, `N = 2.097e+06`), a smaller-`N` choice if a pointwise check is wanted (the ticket pins `s≡1/2`, left as is); (C) row 10 and a toy Hermitian check of `‖G_u-G_{u'}‖ ≤ η⁻²(|√u-√u'|‖X‖+|u-u'||m|)` with BA `H = g₀Ψ+√uX`, `z_u=E+(1-u)m` (ratio at most 0.428); (D) row 14-15 at `u=0`, where `G_0 = M` exactly (`GM = 0`); the loop premise is the proved bound `‖𝓛^{(2)}_0‖ ≤ (Im m)⁻² W^{-d}` (`baFM_loop_det`, `Step1Trivial.lean:119`) against `Nτ g = 2W^{-3}`; (E) rows 16-18; (F) `hwin`: `min_{g'} Im m(E_n,g') = 0.99949, 1.00000, 1.00000` and `E_n → 0`, `Im m → 1 ≥ 1/2` in the limit (`m² + E m + 1 = 0` at `g' = 0`; `E_n = -Re m_S/√t₀` because `Re z = -Re m_S`).

### Verdicts
- Target 1 `baS1Std`: **PASS**. Every `S1Std` field is supplied (rows 1-7), `hE` holds at `E≡0`, no scale fact reads `hE` (row 8), `RangeCond` closes eventually with factor `N^{ε/2}/2 → ∞`.
- Target 2 `baG_continuousOn`: **PASS** (row 9; band `s1x_continuousOn`, `Step1.lean:372`, with `ztOf` and `seqHflowBA`).
- Target 3 `baGopbound`: **PASS** (rows 10-12; constants `C' = 2C+10`, `N ≥ 3κ⁻²`, `|m| ≤ 1` and `κ ≤ Im m` for all `n` are the premises).
- Target 4 `flowFM_omegaC_mono`: **PASS** (row 13).
- Target 5 `flowFM_wl_det`: **PASS** (rows 14-15; the `(2·9^d+1)` bound is exact with zero slack off the diagonal; `G-M` in place of `G-m`, `C₀` free).
- Target 6 `baNetLift`: **PASS** (rows 16-19; all inputs of `cont_core` are energy free; Q-bound `N/κ ≤ N²` for `N ≥ 1/κ`).

```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2262/alt.py
s=0.50 t=2/3 ratio=0.6667 first n=8 N=3.148e+23
s=0.64 t=2/3 ratio=0.9259 first n=0 N=2.097e+06
```

## (a′) Preflight corrections — Tue Oct  6 07:14:30 UTC 2026
1. (a)(ii)(F), rows 4, 6: the instances of targets 3 and 6 do not need the window hypothesis `hwin : BAWinBulk sz0 zSeq (1/3) (1/2)`.  `inst_im_m_ge` proves `Im m(E_n, g₀_n) ≥ 1/2` for every `n` from `mS_im_half` (`4/5 ≤ Im m_S`), `BAmF_sz0_eq` (`m = m_S/√t₀`) and `0 < √t₀ ≤ 1`.  No verdict of (a) changes.

## (b) Script output (`RBM3D/BA/Step1Setup.lean`, branch `t/T2262`; commands run from `../RBM3D-wt/T2262`; scratch files in `scratchpad/T2262/`)
```
$ date -u; git log -1 --format="%h %s" t/T2262
Tue Oct  6 07:07:29 UTC 2026
abfd0c6 T2262: BA-S2b2a Step1Setup (baS1Std, baG_continuousOn, baGopbound, flowFM_omegaC_mono, flowFM_wl_det, 
$ lake build RBM3D.BA.Step1Setup 2>&1 | grep -E "Step1Setup|Build completed|error"
Build completed successfully (3755 jobs).
$ lake build 2>&1 | tail -1   # whole library (the module is not yet imported by RBM3D.lean: the hub adds the import at merge)
Build completed successfully (4070 jobs).
$ wc -l RBM3D/BA/Step1Setup.lean; grep -cE "sorry|admit|native_decide|^axiom" RBM3D/BA/Step1Setup.lean; git diff --stat main...t/T2262
    1279 RBM3D/BA/Step1Setup.lean
0
 RBM3D/BA/Step1Setup.lean | 1279 ++++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 1279 insertions(+)
$ lake env lean scratchpad/T2262/stmtcheck.lean   # imports RBM3D.BA.Step1Setup + the check file section 1; six `example (d : ℕ) : T2262Check.X_stmt d := RBM.BA.X d`, then #print axioms
'RBM.BA.baS1Std': [propext, Classical.choice, Quot.sound]
'RBM.BA.baG_continuousOn': [propext, Classical.choice, Quot.sound]
'RBM.BA.baGopbound': [propext, Classical.choice, Quot.sound]
'RBM.BA.flowFM_omegaC_mono': [propext, Classical.choice, Quot.sound]
'RBM.BA.flowFM_wl_det': [propext, Classical.choice, Quot.sound]
'RBM.BA.baNetLift': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baS1Std': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baG_continuousOn': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baGopbound': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_baNetLift': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_flowFM_wl_det': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_flowFM_omegaC_mono': [propext, Classical.choice, Quot.sound]
'RBM.BA.Step1SetupInst.inst_omegaC_three': [propext, Classical.choice, Quot.sound]
exit=0
$ lake env lean scratchpad/T2262/precheck.lean   # registry pre-check (DECISIONS §20 (2)): import RBM3D; import RBM3D.BA.Step1Setup; #assert_rbm_axioms
exit=0
axiom audit: 7737 theorems, 2575 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
premises found by scanning: 154 (borrowed 1, owed 98, structural 38, refuted 6, superseded 11).
$ python3 scratchpad/T2262/extract.py diff   # statement text of each target vs the check-file pin (whitespace-normalised)
baS1Std identical to check-file pin text: True
baG_continuousOn identical to check-file pin text: True
baGopbound identical to check-file pin text: True
flowFM_omegaC_mono identical to check-file pin text: True
flowFM_wl_det identical to check-file pin text: True
baNetLift identical to check-file pin text: True
$ python3 scratchpad/T2262/extract.py stmts   # target statements extracted from RBM3D/BA/Step1Setup.lean
theorem RBM.BA.baS1Std (d : ℕ) :
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n,
  s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STConStInd sz 𝔠d s t → RBM.Ind.S1Std sz (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d (fun _ => 0) s t
theorem RBM.BA.baG_continuousOn (d : ℕ) :
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im → ∀ a b : ℝ, b < 1 → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)), ContinuousOn (fun v : ℝ =>
  (baFM sz lam0 E).GM n v ω x y) (Set.Icc a b)
theorem RBM.BA.baGopbound (d : ℕ) :
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ), 0 < κ → (∀ n, κ ≤ (BAmF sz lam0 E n).im) → (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → sz.SizeTendsto → ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀
  D > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Sizes.seqP (sz.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧ u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ |u -
  u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧ ∃ x y : Idx d (sz.L n) (sz.W n), ((sz.size n : ℕ) : ℝ) ^ (-C) < ‖BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y‖} ≤
  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))
theorem RBM.BA.flowFM_omegaC_mono (d : ℕ) :
  ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (t C₁ C₂ : ℝ) (ω : sz.SeqΩ), C₁ ≤ C₂ → C.omegaC n t C₁ ω ≤ C.omegaC n t C₂ ω
theorem RBM.BA.flowFM_wl_det (d : ℕ) :
  ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (ω : sz.SeqΩ) (u a c' g Nτ C₀ : ℝ), 0 < c' → (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ 2 * a) → 2 * a ≤ ((sz.W n :
  ℕ) : ℝ) ^ (-c') → 1 ≤ Nτ → 0 ≤ g → (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ g → (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n u ω x y‖ ≤ C₀) → (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d
  (sz.L n)), C.omegaC n u C₀ ω * ‖C.L n u σ b ω‖ ≤ Nτ * g) → (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM
  n u ω p.1 p.2‖ ^ 2 ≤ Nτ * STmaxLoop2g C n u ω) → (∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2}, C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c'))
  ω * ‖C.GM n u ω p.1.1 p.1.2‖ ^ 2 ≤ Nτ * C.gexRHS n u ω (STblk sz n p.1.1) (STblk sz n p.1.2)) → ∀ i j : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1)
  * Nτ ^ 2 * g
theorem RBM.BA.baNetLift (d : ℕ) :
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), 0 < κ → (∀ n, κ ≤ (BAmF sz lam0 E n).im) → (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → 0 < τ → (∀ n, 0 ≤ s n) → (∀ n, s n
  ≤ t n) → (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t → ((∀ k : ℕ, 1 ≤ k → PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × (Fin k
  → Bool) × (Fin k → Zd d (sz.L n))) (fun n p ω => ‖(baFM sz lam0 E).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s
  n)) ^ (k - 1))) → STStep1LoopgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) ∧ (PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun n => TimeIcc s t n × Idx
  d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n p ω => ‖(baFM sz lam0 E).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) →
  STStep1WeakgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t)
$ python3 scratchpad/T2262/extract.py inst    # statements of the compiled instances (namespace RBM.BA.Step1SetupInst)
theorem inst_baS1Std:
  : RBM.Ind.S1Std sz0 (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (fun _ => 0) sI tI
theorem inst_baG_continuousOn:
  : ContinuousOn (fun v : ℝ => (baFMz sz0 zSeq).GM 0 v (fun _ => (1 : ℝ)) 0 0) (Set.Icc 0 (2 / 3))
theorem inst_baGopbound:
  : ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Sizes.seqP (sz0.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧ u ≤ 1 - ((sz0.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz0.size
  n : ℕ) : ℝ)⁻¹ ∧ |u - u'| ≤ ((sz0.size n : ℕ) : ℝ) ^ (-C') ∧ ∃ x y : Idx 3 (sz0.L n) (sz0.W n), ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) < ‖BAGt sz0 (BAflowLam0 sz0 zSeq)
  (BAflowEs sz0 zSeq) n u ω x y - BAGt sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n u' ω x y‖} ≤ ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-D))
theorem inst_baNetLift:
  (hpt : ∀ k : ℕ, 1 ≤ k → PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size (U := fun n => TimeIcc sI tI n × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n))) (fun n p ω =>
  ‖(baFMz sz0 zSeq).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => ((1 - sI n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz0.Bctl n (sI n)) ^ (k - 1))) (hptw : PerTimeDomAt
  (Sizes.seqP (sz0.withLam 0)) sz0.size (U := fun n => TimeIcc sI tI n × Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n)) (fun n p ω => ‖(baFMz sz0 zSeq).GM n (p.1
  : ℝ) ω p.2.1 p.2.2‖) (fun n p _ => (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))) : STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧ STStep1WeakgL (baFMz sz0
  zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI
theorem inst_flowFM_wl_det:
  (ω : sz0.SeqΩ) : ∀ i j : Idx 3 (sz0.L 0) (sz0.W 0), ‖(baFMz sz0 zSeq).GM 0 0 ω i j‖ ^ 2 ≤ (2 * 9 ^ 3 + 1) * (4 : ℝ) ^ 2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹
theorem inst_flowFM_omegaC_mono:
  (ω : sz0.SeqΩ) : (baFMz sz0 zSeq).omegaC 0 0 1 ω ≤ (baFMz sz0 zSeq).omegaC 0 0 3 ω
theorem inst_omegaC_three:
  (ω : sz0.SeqΩ) : (baFMz sz0 zSeq).omegaC 0 0 3 ω = 1
$ name clash: per new public name, occurrences (word match) in RBM3D/ outside Step1Setup.lean / ../RBM2D / ../RBM1D (read-only grep)
baS1Std:0/0/0  baG_continuousOn:0/0/0  baGopbound:0/0/0  flowFM_omegaC_mono:0/0/0  flowFM_wl_det:0/0/0  baNetLift:0/0/0  inst_im_m_ge:0/0/0  inst_norm_m_le:0/0/0  inst_baS1Std:0/0/0  inst_baG_continuousOn:0/0/0  inst_baGopbound:0/0/0  inst_rangeCond:0/0/0  inst_baNetLift:0/0/0  inst_GM_zero:0/0/0  inst_flowFM_wl_det:0/0/0  inst_flowFM_omegaC_mono:0/0/0  inst_omegaC_three:0/0/0  
$ grep -rnE "(def|abbrev) +(sI|tI)( |$)" RBM3D   # sI, tI: the others are private in other files
RBM3D/BA/Step1Setup.lean:1094:def sI : ℕ → ℝ := fun _ => 1 / 2
RBM3D/BA/Step1Setup.lean:1096:def tI : ℕ → ℝ := fun _ => 2 / 3
RBM3D/Induction/Step2Core.lean:1314:private def sI : ℕ → ℝ := fun _ => 0
RBM3D/Induction/Step2Core.lean:1315:private def tI : ℕ → ℝ := fun _ => 1 / 16
$ P1 (dummy energy soundness): reads of S1Std.hE / .hκ in RBM3D/Induction/Step1Setup.lean, each with its enclosing declaration
617: theorem s1_c1_pos (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) : 0
744: theorem s1_h55 (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (hIK :
783: theorem s1_LI (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : 
809: theorem s1_LI (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : 
830: theorem s1_LI (h : S1Std sz κ 𝔠 𝔡 τ 𝔠d E s t) (h55 : 
$ ports: git log -1 --format=%h of the band sources (RBM3D files; no RBM1D/RBM2D file is copied, so no git -C ../RBM2D diff is run)
RBM3D/Induction/Step1Setup.lean 4f186cf
RBM3D/Induction/Continuity.lean a51b69e
RBM3D/Induction/Step1.lean b969625
RBM3D/Induction/ContinuityNet.lean 5b6cbc1
$ lake env lean scratchpad/T2262/names.lean   # #check of every Mathlib name of section (c)
exit=0 output-lines=      61 errors=0
```

Narrative (what the script output does not show):
- Cut: all six targets are proved in one new file; the statements are the check file's `_stmt` texts (script diff above, and the six `example (d : ℕ) : T2262Check.X_stmt d := RBM.BA.X d` compile, `stmtcheck.lean`).  No hypothesis added, no target weakened, no pinned or frozen signature changed; the only edited file is `RBM3D/BA/Step1Setup.lean`; `RBM3D/Test/Axioms.lean` and `RBM3D.lean` are untouched (no new `Prop`-valued definition; pre-check exit 0).
- Target 1 (`baS1Std`): `S1Std` at the dummy energy `E ≡ 0`, `κ' = min κ 1`; the P1 grep above shows `hE` is read only in `s1_h55`, `s1_LI` (replaced by `baBoot_LI`) and `hκ` only for positivity (`s1_c1_pos`).  `RangeCond (ε/2) t` is proved from `BAdom` and `Im m ≤ 1` (private `BASetup_BAm_im_le_one`: `BAm_spec` + `BAself_norm_le_one`, or `m = 0`), eventually `N^{ε/2} ≥ 2` (`eventually_le_rpow`).
- Target 2: `continuous_green_of_isHermitian_moving` on the clamped path `ztOf m E (min v b)`, `H_v = g₀Ψ + √v X` (private `BASetup_herm`, `BASetup_continuous_H`); `Im z_v = (1 - v) Im m` (`ztOf_im`).
- Target 3: `C' = 2C + 10`; good event `contGood (sz.withLam 0)` (`cont_good_compl`, `cont_eventually_tail`, applied at `sz.withLam 0`: the definitions are `rfl`-equal at the common data); `η = κ N⁻¹`, `Q = N κ⁻¹`; the bound `(N/κ)²(2N²+1)√Δ ≤ 3κ⁻² N⁴ N^{-C'/2} = 3κ⁻² N⁻¹ N^{-C} ≤ N^{-C}` needs `N ≥ 3κ⁻²` (eventually, together with `N ≥ 3`).  The band constant `2C+14` came from `η⁻¹ ≤ N²`.
- Targets 4, 5: target 5 is `s1_wl_det` with `STGM`, `STindMax`, `STomegaC`, `STmaxLoop2`, `STgexRHS` replaced by `C.GM`, `C.indMax`, `C.omegaC`, `STmaxLoop2g`, `C.gexRHS`; the threshold `2` is the hypothesis `‖G‖_max ≤ C₀` (`omegaC = 1` by `simp`), the off-diagonal premise is on `GM` (no `hGM` rewrite).  As in (a) row 14 the off-diagonal bound has zero slack.
- Target 6: copies with prefix `BASetup_` of the private band helpers `contWord`, `cont_word_norm`, `cont_word_diff`, `cont_loopFine_eq`, `cont_one_add_pow_le`, `cont_LP_zeta_ratio`, `cont_LP_low`, `cont_WL_low`, `cont_LP_eventually`.  `cont_entry_diff`, `cont_loopAbs_diff`, `cont_LP_close`, `cont_WL_close` are re-stated for two Hermitian matrices with `H - H' = c X` (`BASetup_entry_diff`, `BASetup_loopAbs_diff`, `BASetup_LP_close`, `BASetup_WL_close`; `BASetup_H_sub` is the cancellation of `g₀Ψ`); `cont_eta_inv_le` becomes `BASetup_eta_inv_le` (`(1-t)⁻¹ ≤ N`, `1/κ ≤ N` give `η_t⁻¹ ≤ N²`); `cont_STGM_eq` is not needed (`GM = G - M`, `M` time independent).  `cont_core` is applied as in `step1NetLift`, with `contGood (sz.withLam 0)`.
- Instances: `sz0`, `zSeq`, `lam0 = BAflowLam0 sz0 zSeq`, `E = BAflowEs sz0 zSeq`, `κ = 1/2`, `s ≡ 1/2`, `t ≡ 2/3`, `τ = 1/2`.  Every deterministic hypothesis is discharged, including `STConStInd` (merged `s1Setup_conStInd_const`), `RangeCond (1/2) t` (`inst_rangeCond`) and `Im m ≥ 1/2`, `|m| ≤ 1` (`inst_im_m_ge`, `inst_norm_m_le`).  Only the two `PerTimeDomAt` hypotheses of `inst_baNetLift` stay (the BA analogue of `STStep1LoopPT`/`STStep1WeakPT`: BA-S2b2b).
- `inst_flowFM_wl_det`: `u = 0`, so `G_0 = M` (`BASetup_GM_zero`, a copy of T2256's private `Boot_GM_zero`); data `a = 1/64`, `c' = 1/20`, `g = (W^3)⁻¹`, `Nτ = 4`, `C₀ = 3`; the loop premise is `baFM_loop_det` (`‖𝓛^{(2)}_0‖ ≤ (Im m)⁻² W^{-3} ≤ 4g`), `‖G_0‖_max ≤ (Im m)⁻¹ ≤ 2` by `baM_entry_le`, and the two `GEX` premises hold because `G_0 - M = 0`.  The conclusion is then `0 ≤ …`, as the ticket prescribes (`G - M = 0`); `inst_omegaC_three` shows `Ω_3` has indicator `1` there (`Step1BootInst.inst_baOmegaC_eq_one` and `flowFM_omegaC_mono`).

## (c) Verified Mathlib names (`#check` in `scratchpad/T2262/names.lean`, exit 0, 0 errors; names verified absent: none looked for)
`Complex.div_ofReal_im`, `Real.sqrt_le_one`, `Real.sqrt_pos`, `le_div_self`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_neg_one`, `inv_anti₀`, `norm_le_norm_sub_add`, `abs_norm_sub_norm_le`, `mul_le_of_le_one_left`, `mul_le_of_le_one_right`, `continuous_matrix`, `Continuous.matrix_elem`, `Complex.norm_real`, `Complex.conj_im`, `Complex.norm_conj`, `Finset.sup'_le`, `Finset.le_sup'`, `tendsto_rpow_neg_atTop`, `tendsto_natCast_atTop_iff`, `Real.mul_rpow`, `Real.rpow_le_rpow`, `div_le_div_iff₀`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `pow_le_pow_of_le_one`, `one_le_pow₀`, `one_le_div`, `Matrix.trace_sub`, `Matrix.sub_apply`, `Matrix.smul_apply`, `Matrix.nonsing_inv_eq_ringInverse`, `Real.rpow_natCast`, `Real.rpow_add`, `Real.rpow_zero`, `Real.inv_rpow`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `gt_mem_nhds`, `Finset.card_le_two` (all elaborate; the file builds).

## (d) Open issues and paper-delta candidates
- **T2262a**: time continuity of `G_t` for the block Anderson flow (the `Gopboundu` analogue, `baGopbound`, `baG_continuousOn`) has no statement in `7_8` (`7_8:1987-1990` says "same as [RBSO1D, §7.1]"); same status as T2015e for the band.
- **T2262b**: "same as [RBSO1D, §7.1]" (`7_8:1987-1990`) is read as the band weak-law core with `G - M` in place of `G - m` and the event threshold `C₀` free (`flowFM_wl_det`; BA-S2b2b is to use `C₀ = 1 + κ⁻¹`, via `baM_entry_le`) in place of the band's `2`.
- **T2262c**: `S1Std` is used at the dummy energy `E ≡ 0` with `κ' = min κ 1` (`baS1Std`): the block Anderson chain domain `BAdom` has no bulk condition `|E| ≤ 2 - κ` (`7_8:1797` states `|Re z| ≤ 2 - κ` for `zztE_BA`; the ticket reads it as typo T2001g); Lean-side bridging only, no mathematics changes.
- **T2262d**: the net lift (`baNetLift`) and `baGopbound` replace the bulk premise `|E| ≤ 2 - κ` by `κ ≤ Im m`, `|m| ≤ 1`; `C' = 2C + 10` (band `2C + 14`, since `‖G_u‖ ≤ N/κ` replaces `N²`); eventual conditions `N ≥ 3κ⁻²`, `1/κ ≤ N`.
- Observations: (1) as in (a)(ii)(B), `STConStInd` at `s ≡ 1/2`, `t ≡ 2/3` holds only for `n ≥ 8`; the instance uses the merged eventual lemma, no pointwise claim.  (2) `inst_baNetLift` is an implication from the two `PerTimeDomAt` hypotheses (other gate); `STStep1LoopgL`, `STStep1WeakgL` are not asserted unconditionally.  (3) P5: no further interface lemma is needed; S2b2b may copy the private `BASetup_norm_BAmF_le_one`, `BASetup_BAm_im_le_one` if it needs `|m| ≤ 1`, `Im m ≤ 1`.  (4) The file is 1279 lines (ticket estimate 900 / 1200 / 1500).
