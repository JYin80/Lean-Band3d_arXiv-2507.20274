Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct 12 17:26:08 UTC 2026
Stage 1a design gate D1-D4 of T2462 (mathematics only; no Lean written). Tree `main` a1628b9 (code = 62eed82). UBA-C1 text = H252 (2) / DECISIONS §271 (4): `Cmp(A) := ∀ n, 0 ≤ gK n ∧ gK n ≤ sz.lam n ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`. Notation: `θ_t = Step2Gen_thetaKer = XΘ_t(X)`, `X = M^{(σσ')}S`, `Θ_t = (1-tX)⁻¹`; `T^g_t = tailT d L g t`. `S` = scratchpad `T2462/` (python3 + numpy; my scripts, not Lean).
Math fixed here: `(eq:decompUalt)` (A_deterministic_estimates.tex:100): `uKer_{s,t} = 1 + (t-s)θ_t` follows from `uKer_{t,t}=1` alone: `(1-tX)Θ_t = 1` gives `Θ_t = 1 + tθ_t`, so `(1-sX)Θ_t = 1 + (t-s)θ_t` (target 8, no invertibility argument).
### (i) Exponent table
| # | quantity | value / constraint | slack |
|---|---|---|---|
| 1 | `κm` (T1) | band `√(2κ)/2` (`st5_mE_im_ge`, Step5Cases:409) ≤ `Im m(E)` for `|E| ≤ 2-κ`; BA `κm = κ` (`BAdom`, MFixedPoint:436) | κ=1/10: κm=0.2236 vs inf Im m=√(4κ-κ²)/2=0.3122: 0.0886; E=1/2: 0.9682 |
| 2 | `T0<1`, `η_t=(1-t)Im m` (T1) | needs `Im z>0`; BA `t0=Im m/(Im m+Im z)`; `η` is `etaT` (GLoop:75) | ε=1/5, n=1: Im z=N^{-1+ε}>0, 1-t0≈4.2e-10 (inst.py) |
| 3 | `A` (Cmp) | band 1, `gK=lam`; BA `(κ+1)/κ` from `t0 ≥ κ/(κ+1)` (TwistStep2:731) and `TwistStep2_lam0_sq` (:740, squares form); `A ≥ 1` | κ=1/10: A=11, equality at the worst `t0=1/11`; instance `t0≈1`: lam²/gK²≈1+4e-10 |
| 4 | crossing `T^{gK}_t ≤ A·T^{lam}_t` (T9) | `ellT(L,g,t)=min(max(g/√|1-t|,1),L)` is nondecreasing in `g`, so `exp(-√(r/ell))` only improves; `B^{gK}/B^{lam} ≤ (lam²+b)/(gK²+b) ≤ lam²/gK² ≤ A`, `b=|1-t|`, needs `0<gK≤lam` | measured max ratio/A: 1.000 (A=1), 0.692 (A=11, lam=1/2) |
| 5 | `Λ` (T9) | `0<gK≤Λ`; `C₆=C₆(d,Λ)`; `Λ=𝔡⁻¹` | 𝔡=1/4: Λ=4 vs lam=1/2, 2.4e-4 |
| 6 | `C₆` (T9 band) | `θ(a,b)=μΣ_c S(a,c)Θ_{tμ}(c,b)`, `S` supported on `zdistD≤1`, row sum 1; `prop5Decay` (C₅,c₅) at `K=zdistD(b-c) ≥ zdistD(b-a)-1`: `B_{t,K} ≤ 2^{d-2}B_{t,K'}`, `e^{-c₅K/ℓ} ≤ e^{c₅}e^{-c₅K'/ℓ}`, then `e^{-c₅x} ≤ e^{1/(4c₅)}e^{-√x}` (as `step5Kernel_theta_decay`): `C₆ = max(1, C₅ 2^{d-2} e^{c₅} e^{1/(4c₅)})` | measured sup `|θ|/tailT` = 1.948 (g=1/2; kernel.py) ≤ any valid C₆ |
| 7 | row sum (T9) | `Σ_b|θ_t(a,b)| ≤ 1/(1-t)`, constant 1 at band (`B45_row_thetaKer`, B45:657) and BA (`baComp_row_le`, EMn2BA:386) | measured max `(1-t)Σ` = 1.000000: tight |
| 8 | `Cp` (T9) | `max(C₆·A·C_T, C₆)` (with row-sum constant 1: `max(C₆ A C_T, 1)`), `C_T` of `ekPropTInf_holds` (any `g>0`) | measured needed Cp ≥ 17.55 (lam=1/2, t=0.996, u=0) |
| 9 | window (T9) | `lam²/L² ≤ 1-t ∨ 1-u ≤ lam²/L²` at `sz.lam` (no crossing) | lam=1/2, L=8: 0.003906 vs 1-t=0.004 (slack 9.4e-5); vs 1-u=1e-3 (0.0029) |
| 10 | floor `(1-u)/(1-t)·W^{-D}` (T9) | row sum × `(1-u)W^{-D}`; `W>0` real, `D` any | u=0,t=.996,W=1024,D=2: 2.384e-4 |
| 11 | Ward (T7) | `|E|<2`, `0≤u<1`, `η_u=(1-u)Im m>0`, `N=(WL)^d` | E=1/2: 2-|E|=1.5; Nη=5.32e11 |
| 12 | NewKLKL (T10) | `δ₀=κ/2`, domain `κ ≤ Im m`; `C=2(4+C_K)+C_sC_T`, `C_s=2^{d-2}e`; band `C_K=1` (10+C_sC_T) | C_s=5.4366; H=0,E=0,u=δ₀/(1+δ₀): ‖G-M‖=δ₀ (equality) |
| 13 | `Admissible` along `sz0` | `W^{-d/2+𝔡} ≤ lam ≤ 𝔡⁻¹`, `N^𝔠 ≤ W`, `N→∞` | n=1: 1.73e-4 ≤ 2.44e-4 (1.41×); 222.9 ≤ 1024 (4.6×); no failure for n ≤ 200000 |
| 14 | case (iv) route (T5) | `Bctl(u) ≤ Bctl(t) < 1` for `u ≤ t`: `STBctl_mono` + `(Bctl t)^{𝔠d} ≤ (1-t)/(1-s) < 1`, `𝔠d=1/100` (Bctl_le_one_of_conStInd, Step1Fam:382) | n=1: 0.8128 ≤ 0.9375; n=200000: 0.1445 |
### (ii) One concrete nondegenerate instance (all hypotheses of T1-T11 at once)
Data: `d=3`, `sz0` at `n=1` (Defs/Sizes.lean:255-263): `L=8, W=1024, lam=2.44e-4, N=(WL)^3=2^39`; κ=1/10, 𝔡=1/4, 𝔠=ε=1/5, E=1/2, D=2, (t,u)=(0.996, 0); kernel stress at `lam=1/2` (same L, W; WO holds) with both window disjuncts ((t,u)=(0.9999, 0.999)); Cmp at `gK=lam, A=1` and `gK=lam/√11, A=11`; Ward identity on `L=3, W=2` (its hypotheses `|E|<2`, `0≤u<1`, Hermitian, `σ₀≠σ₁` carry no size; at `N=2^39` the matrix cannot be formed). External (eventual) hypotheses `Admissible`, `STConStInd`: limit computation along all of `sz0` in the last two output lines of `inst.py`.
`$ cd $S && python3 inst.py`
```
sz0(n=1): L=8 W=1024 lam=2.441406e-04 N=(WL)^d=549755813888=2^39; kappa=0.1 dd=0.25 cc=0.2 E=0.5
target-hypothesis checks (n=1):
 3<=d: True  3<=L: True  WO: W^(-d/2+dd)<=lam<=1/dd: 0.00017263349150062197 <= 0.000244140625 <= 4.0 True
 Bandwidth N^cc<=W: 222.86 <= 1024 True
 limit/all n=0..200000 failing WO or Bandwidth along sz0: [] count 0 ; N_n -> inf: N_1=549755813888 N_200000=5.498e+101
 flow facts: |E|<=2-kappa:True; Im m(E)=0.9682; kappa_m=sqrt(2kappa)/2=0.2236<=Im m:True; inf over |E|<=2-kappa of Im m = sqrt(4k-k^2)/2=0.3122 >= kappa_m:True
 eta_u=(1-u)Im m=0.9682; N*eta_u=5.3230e+11; Ward needs |E|<2:True, 0<=u<1:True
 domain: Im z=N^(-1+eps)=4.054e-10>0 (eps=0.2); BA t0=Im m/(Im m+Im z)=0.999999999581<1, 1-t0=4.187e-10
 comparison: band gK=lam,A=1: 0<=gK<=lam & lam^2<=1*gK^2: True; BA kappa=0.1: A=(kappa+1)/kappa=11.0, t0>=kappa/(kappa+1)=0.0909, gK=sqrt(t0)lam=7.3611e-05: gK<=lam & lam^2<=A gK^2 (equality): True
 window (lam=0.5, L=8): lam^2/L^2=0.003906; (t,u)=(0.996,0.0): lam^2/L^2<=1-t:True or 1-u<=lam^2/L^2:False; 0<=u<=t<1:True
 window (lam=0.5, L=8): lam^2/L^2=0.003906; (t,u)=(0.9999,0.999): lam^2/L^2<=1-t:False or 1-u<=lam^2/L^2:True; 0<=u<=t<1:True
 floor (1-u)/(1-t) W^-D at u=0,t=0.996,W=1024,D=2: 2.384e-04; C_s=2^(d-2)e=5.4366; NewKLKL C=2(4+C_K)+C_s C_T, C_K=1 -> 10+C_s C_T
 NewKLKL domain: kappa=0.1 dd=1/4: 0<lam=0.000244140625<=1/dd=4; kappa<=Im m(E=0)=1; H=0,E=0,u=d0/(1+d0)=0.047619: ||G-M||=u/(1-u)=0.0500<=kappa/2=0.05
 (con_st_ind) cd=1/100, s=0, t=1/16: Bctl^cd<=(1-t)/(1-s)<1 fails for n in 0..200000: [] count 0; n=1: 0.8128<=0.9375, n=200000: 0.1445
```
`$ python3 kernel.py` (D2 band decay, `d=3, L=8`, 8 values of t incl. 0, 4 phases μ)
```
D2 band decay: max_b |thetaKer(0,b)|/tailT(|b|_inf) and max (1-t)*rowsum over t,mu (d=3,L=8)
g=5.000e-01: max ratio 1.9483 at (t,mu)=(0.9999, 1); max (1-t)*rowsum 1.000000 (<=1)
g=5.000e-02: max ratio 0.9858 at (t,mu)=(0, 1); max (1-t)*rowsum 1.000000 (<=1)
g=1.508e-01: max ratio 1.3993 at (t,mu)=(0.9999, 1); max (1-t)*rowsum 1.000000 (<=1)
g=2.441e-04: max ratio 0.9981 at (t,mu)=(0, 1); max (1-t)*rowsum 1.000000 (<=1)
```
`$ python3 profile.py` (Cmp, crossing, `Cp` needed; `θ` built at `gK`, tails at `lam`, `a₁=0`, all 512 `a₂`)
```
UBA-C1 crossing tailT^{gK}_t(r) <= A tailT^{lam}_t(r), then ProfileK needed Cp (d=3,L=8,W=1024,D=2)
lam=5.000e-01 A= 1.0 gK=5.000e-01 comparison(0<=gK<=lam, lam^2<=A gK^2): True; crossing max ratio/A=1.0000; windows tested 21; needed Cp=17.552 at (t,u)=(0.996, 0)
lam=5.000e-01 A=11.0 gK=1.508e-01 comparison(0<=gK<=lam, lam^2<=A gK^2): True; crossing max ratio/A=0.6917; windows tested 21; needed Cp=17.151 at (t,u)=(0.996, 0)
lam=2.441e-04 A= 1.0 gK=2.441e-04 comparison(0<=gK<=lam, lam^2<=A gK^2): True; crossing max ratio/A=1.0000; windows tested 33; needed Cp=1.003 at (t,u)=(0.9999, 0.9)
lam=2.441e-04 A=11.0 gK=7.361e-05 comparison(0<=gK<=lam, lam^2<=A gK^2): True; crossing max ratio/A=0.0910; windows tested 33; needed Cp=1.001 at (t,u)=(0.9999, 0.9)
```
`$ python3 ward.py` (`(zYU1)` at the band: L-side from a random Hermitian `H`, K-side `K^{(2)}=W^{-d}Θ_u`, `K^{(1)}_±=m_±`, `z_u=E+(1-u)m(E)`)
```
d=3 L=3 W=2 N=216 E=0.5 u=0.3 eta=0.6778: max |LHS-RHS| of (zYU1) over both mixed orders, 6 values of a2: 3.25e-18
Ward-family L-side check |sum_c L - kappa(L1+ - L1-)|: 3.2545410429785603e-18
conjugation L1- = conj L1+: 2.482534153247273e-16
```
### Decisions and tables (mathematics)
**D1 (Ward term).** Default kept: carrier datum `T2462_WardIdent` (text unchanged; the pin's `∀ ω` is sound: only Hermitian `H`, `|E|<2` enter, ward.py). T2463 is `state: held`, no branch (docs/queue/T2463.state), not merged: the alternative is unavailable (T2462.md D1 requires a re-check at the start of 1b); T2457 (a‴) fixed only `STNewPQgL` (H251 (2)), so this row fixes the Ward text first. Bridge T2463 owes (math, ward.py last two lines): `ZeroModeGen_WardCls` (T2463-check.lean:228, `κ=(2iW^dη)⁻¹`) gives by cyclic rotation `Σ_c T⟨[s,¬s],[c,a₁]⟩ = κ(X₊-X₋)`; with `X₋ = conj X₊` for the one-index loops (not part of `WardCls`: an extra hypothesis) this is `2iκ Im X₊`, and `L^{-d}Σ_c` gives `Im X₊/(Nη)`. Third option (from the resolvent form) not used.
**D2 (kernel facts).** Decision: pins `T2462_ThDecayK`, `_band`, `_ProfileK` accepted, with **E1** (required, §271 (4)): the hypothesis of `ProfileK` is `Cmp(A)` above (adds `0 ≤ gK n`; the proof at index n uses only its own `0<gK n`, `gK n ≤ lam n`, `lam n² ≤ A gK n²`; `lam n=0` would force `gK n=0`, contradicting `0<gK n`: vacuous), and **R1** (recommended): row-sum clause `≤ 1/(1-t)` (constant 1, both sources give it; row 7). Proof of `ProfileK`: `‖θ‖ ≤ C₆T^{gK}_t ≤ C₆A T^{lam}_t` (row 4), `tailW ≤ T^{lam}_u + W^{-D}`, `(1-u)Σ_b T^{lam}_u T^{lam}_t ≤ C_T T^{lam}_t` (TTT2, any `g>0`, window at `lam`), floor by the row sum: `Cp` row 8. Sources: band `θ = μSΘ_{tμ}` (row 6); BA `NewKLKBA_tail` (NewKLKBA:269, private): `‖(Θ_BA M^{(σσ')})_{ab}‖ ≤ Q₀ T^g_u` all charges, all `u∈[0,1)`, under `BAReal` (κ ≤ Im m) at the family's `g` (= `lam0` after `withLam`), `baComp_row_le`; F7 of `baNewKLKGenHyp` (NewKLKBA:446) is a different statement (tailW convolution at `u=t`, `ℓ',D'` free, no floor) from the same two facts, not an input of target 9. Readers: IniTermI:306, IniTermII:332, DuhamelI:525 read `Σ‖Θ_t(a₁,b)‖ tailW`: from `Θ=1+tθ` (needs `Step2Gen_USemigroup`) `≤ Cp+1` times the same RHS (`(1-u)T_u ≤ T_t` for `u≤t`, `T^g_t` nondecreasing in `t`); IniTermI:2139 (Θ decay) from `1 ≤ (Λ²+1)T_t(0)`; IniTermI:2201 from decay twice + (TTT2); IniTermI:487, IniTermII:940, DuhamelI:600, 628 (decomposition) are target 8 (`(w-v)/w ≤ 2(1-v)` becomes `(w-v) ≤ (1-v)`); DuhamelI:591 uses the band positivity `‖Θ‖=Re Θ` (band only; the generic reader takes the row sum). X1a (merged 62eed82): `STThg` = `Θ_t` (CltGen:30), `STThPropsg` (CltGen:126) = Prop5 form (`zdistD`, linear exponent `c₅r/ℓ`, mixed charges, eventually, at `lam`): not implied by D2's `√`-tail, and not needed by it; X1b reads `STThPropsg`, U4s2/U4s3 read D2. A form fed by band and BA exists: no REQ.
**D3 (NewKLKL).** Facts of `newKLKL_at` (NewKLKL:732) / its privates against `NewKLKGenHyp` (NewKLKGen:383): S-support `zdistInf≤1` (:145) → F5(a); `Σ_y‖S‖≤1` (conv_two :165, far sums) and symmetry (column sums) → F5(b), F5(c); Ward-K marginals (:456) → F8 (`C_K`); Ward-L (:379, :496; Hermitian `blockMat H`, `Im G_xx ≤ Im m+κ/2` from `‖GMM‖≤κ/2`) → model-free `ward_L` + F9 (`LM`=`loopFine` at ζ, `Im ζ=(1-u)Im m`, GMM diagonal); (TTT2) `hTTT` → `ekPropTInf_holds`; near/far split (:595), `bound2` (:606) → model-free; spectral `|E|≤2-κ ⇒ Im m ≥ κ/2` → hypothesis `κ ≤ Im m` (then `2(Im m+κ/2)/((1-u)Im m) ≤ 3/(1-u)`). F6, F7 are not read. Extra fact needed: none. D3 PASS.
**D4 (split).** Mathematically the file groups are independent: targets 8-11 use none of targets 1-7 (T8 needs only `USemigroup`, T9 only `ThDecayK`, T10 only `NewKLKGenHyp`); the ticket's pre-signed split at the file boundary is clean. Line counts: probe step.
**(viii) hypothesis table** (premise → band discharge → BA / owner): FlowFacts → row 1-2, `hflow.1`, `st5_t_lt_one`, `etaT_eq_etaOf` → `BAFlow.1`, `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, U4-BA (b); `STEtermsMidgL, STDuhamelIgL, STDuhamelIIgL` → `stEtermsMid_of_LWT`, `stDuhamelI/II_holds` via `*_iff_gL` → owner U4s3; `STIniTermIgL, STIniTermIIgL` → `stIniTermI/II_holds` → U4s2; `STPfStep5gL` → `stPfStep5_holds` → U5; `STStep5ConclgL` (T6 premise) → concluded by T2-T5 → registry (as band `STStep5Concl`); `WardIdent` → `stWardII_identity` → `baK_ward`, `BAKsol_rotate`, conj. (U4-BA (b)) or T2463 `WardCls` + conj.; `Step2Gen_USemigroup` → `step2Gen_USemigroup_band` → `BAuKer_self/_comp`; `ThDecayK` + `Cmp(A)` → D2 band proof, `A=1` → `NewKLKBA_tail`+`baComp_row_le` at `lam0`, `TwistStep2_lam0_sq`, U4-BA (a); `NewKLKGenHyp` → `newKLKGenHyp_band` → `baNewKLKGenHyp`; `STTailtoTail` → `stTailtoTail_holds` → U5.
**(ix) UBA-C1 table** (size-level `sz.lam` / kernel `gK` / where `Cmp` enters): T1 none / none / never; T2-T6 `sz.lam` only (U6 text: regimes, `Bctl`, `STAI`, `ellT`, windows) / none / never; T7 none (`N`, `C.eta`) / none / never; T8 none / kernel through `C.S`, `Mss`, no coupling / never; T9 tails, window, (TTT2) at `lam` / `ThDecayK` at `gK` / once: row 4 and `lam n>0` from `0<gK n≤lam n`; T10 family's `lam` (BA: `withLam lam0`) / none / never (F7 unused by NewKLKL); T11 `sz.lam` / none / never.
**Observations.** O1: neither `STFlow` nor `BAFlow` gives `∀ n, 0 ≤ sz.lam n` (`Sizes.lam` has no sign, Defs/Sizes.lean:138-146; `WO` is eventual), so `Cmp(A)` at band (`gK=lam`) and BA needs `∀ n, 0 ≤ sz.lam n` as an input of the consumer; the targets' proofs do not. O2: the ticket's band route for T9 lists only `norm_Theta_apply_le`, `sum_norm_Theta_row_le`, `Step2Kern_*_band`; the decay clause also needs `prop5Decay_holds` and the S-convolution of row 6 (merged `QopDecay_thetaKer_decay` has the weaker form `C(1-u)⁻¹e^{-c·}`, not ≤ tailT). O3: `T2462.md:74` literal is superseded by §271 (4) (E1); paper-delta candidate `T2462a`: generic kit takes `FlowFacts`, `WardIdent`, `USemigroup`, `ThDecayK` as carrier data and states `(eq:decompUalt)` in the `1+(t-s)θ` form.
### Fill-in table (H250 (4)); rows owed to the probe step are stage-1a-forbidden checks (names, cones, sizes)
| # | deliverable | line / n/a |
|---|---|---|
| (i) | exponent table | line 6 |
| (ii) | instance + scripts | line 23 |
| (iii) | layout, cones, no `BA/*` | n/a, because cone and import checks are module-graph checks, not stage-1a mathematics: probe step. Math side: no target needs `BA/*` (D2 sources are hypotheses) |
| (iv) | D1 | line 65 (probe lines: probe step) |
| (v) | D2, reader table, X1a | line 66 (probe lines: probe step) |
| (vi) | D3 table | line 67 |
| (vii) | scope table of the 74 band names | n/a, because it is a name enumeration (forbidden at 1a): probe step; targets in (viii) |
| (viii) | hypothesis table | line 69 |
| (ix) | UBA-C1 table | line 70 |
| (x) | premise scan, registry | n/a at 1a, because the scan runs on Lean text: probe step; the premises that nothing concludes are in (viii) (T2462.md Registry: 7 lines) |
| (xi) | `open private` list, copies | n/a, because it is Lean-level: probe step |
| (xii) | lines per file, split | line 68 (math independence only; counts: probe step; ticket's central 2,000 > 1,950 pre-signs the split) |
| (xiii) | name-clash grep | n/a, because a name check (forbidden at 1a): probe step |
### Verdict
T1 PASS (rows 1-2). T2-T4 PASS (case proofs need only T1 + the named pins; no spectral datum beyond T1). T5 PASS (size-level route, row 14). T6 PASS (precomposition at `u=t`). T7 PASS (D1; identity verified, ward.py). T8 PASS (algebra above). T9 PASS with E1, R1 (D2; rows 4-8, kernel.py, profile.py). T10 PASS (D3). T11 PASS (band instance only). No stop rule of the ticket fires in the mathematics. Open for the probe step and 1a-audit: E1 text, R1, O1-O3, rows (iii), (vii), (x)-(xiii).

## (a″) Probe compile — Mon Oct 12 17:59:33 UTC 2026
Probe step (ticket Process and Probe line; H250 (4)). Branch `t/T2462`, commits `bae738a`, `0a1203e` on `62eed82`; sole file `RBM3D/Probe/T2462Pins.lean`, 359 lines (limit 400), no root import; `grep -cE 'sorry|admit|native_decide|^axiom'` on it: 0. Section (a) is unedited. Pin texts are those of `docs/tickets/checks/T2462-check.lean`, with E1 (DECISIONS §271 (4)). Scripts named below are in the scratchpad `T2462/` of this session (evidence.sh reruns all of them).
`$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2462 && lake env lean RBM3D/Probe/T2462Pins.lean; echo "exit=$?"` (started 17:53:14 UTC by `date -u`)
```
@T2462_WardIdent : {d : ℕ} → {sz : Sizes d} → FlowFM sz → Prop
@probe_wardIdent_band : T2462_WardIdent_band
probe_thDecayK_band : T2462_ThDecayK_band
probe_profileK : ∀ (d : ℕ), T2462_ProfileK d
@probe_uKer_eq : ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2462_uKerDecomp C n
'RBM.BA.probe_wardIdent_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_thDecayK_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_profileK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_uKer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.BA.probe_thDecay_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
exit=0
```
`$ cd /Users/junyin/Lean_proof/RBM3D && lake env lean /Users/junyin/Lean_proof/RBM3D-wt/T2462/RBM3D/Probe/T2462Pins.lean; echo "exit=$?"` (main HEAD `e288560e`): last line `exit=0`; `diff` of the two outputs: empty.
`$ git diff --stat 62eed82 main -- RBM3D RBM3D.lean`: RBM3D.lean, RBM3D/BA/NetLiftBA.lean, RBM3D/Graph/BALocReg1.lean, RBM3D/Graph/BALocReg1B.lean (`4 files changed, 2651 insertions(+)`); the probe's import closure (105 modules, probecone.py) contains none of them.
`$ python3 pins_diff.py` (probe pins against the check file): T2462_WardIdent = check text; T2462_WardIdent_band = check text; T2462_ThDecayK = check text; T2462_ThDecayK_band = check text; T2462_ProfileK : DIFFERS: check has '' | probe has '0 ≤ gK n ∧ ' (context: 'ecayK C gK Λ C₆ → (∀ n, ' )
**Probe lines.** D1: `T2462_WardIdent`, `_band`, `probe_wardIdent_band` (one `exact stWardII_identity …`) 42-56; instance at `sz0`, E=0, n=0, u=1/2, σ=(+,-) 259-269.
D2: defs 61-81; `probe_tailT_cross` (`gK ≤ lam`, `lam² ≤ A gK²`) 85-110; `ThDecayK` band 115-172; `probe_profileK` 177-250 (the comparison is used once, line 203); instances 271-329: band (`gK = sz0.lam`, A=1, Λ=4, W=32, D=2, u=0, t=1/2, `lam²/L²` = 1/65536 ≤ 1/2) 276-293, non-band (`probeSz1.lam = 2·sz0.lam`, `gK = sz0.lam`, A=4) 295-329. T8 `probe_uKer_eq` (`uKer = 1 + (t−s)•thetaKer` from `uKer t t = 1` alone) 333-346.
**Findings** (each backed by the output above or by the script named).
F1 (E1) `probe_profileK` binds `0 ≤ gK n` and never uses it (line 182, `obtain ⟨_, hc1, hc2⟩ := hcmp n`); it uses `0 < gK n` (a hypothesis of the statement), `gK n ≤ lam n`, `lam n² ≤ A gK n²`. The band instance discharges `0 ≤ sz0.lam n` separately (line 290, `unfold sz0; positivity`), as O1 of (a) says a consumer must. R1 is not probed; the pinned row-sum clause `C₆/(1−t)` compiles.
F2 (O2, Lean level) `ThDecayK` band, 115-172: `step5Kernel_theta_decay` (μ=1) + `‖Θ(tμ)‖ ≤ ‖Θ(t)‖` (`norm_Theta_apply_le`, `step5Kernel_norm_Theta_eq_re`) + `θ = Σ_z μ S(a,z) Θ(tμ)(z,b)` + `|a−z|_∞ ≤ 1` (`newKLKL_SB_support`) + `𝒯(r') ≤ 2^{d-2}e·𝒯(r)` for `r ≤ r'+1` (`newKLKL_tailT_shift`) + row sum `B45_row_thetaKer`; `C₆ = max(C₁·2^{d-2}e, 1)`.
The probe imports `Induction/NewKLKL` and `Induction/B45`, which are not in the layout of `Step5KerGen` (`Step5Gen`, `Step5Kernel`): copy the helpers under the stem (97 lines, counted in (xii)) or amend the import list; for the 1a-audit.
F3 (premise scan; scan2.lean on the probe plus four probe-shaped theorems, three shown; verbatim, each line cut before `; top-level binder …`) the head of the conclusion decides whether a pin counts as concluded:
```
RBM.BA.scanA: conclusion head = some (RBM.BA.T2462_WardIdent_band)
RBM.BA.scanB: conclusion head = some (RBM.BA.T2462_WardIdent)
RBM.BA.scanC: conclusion head = some (Exists)
```
So the 1b states `step5CasesGen_wardIdent_band` and `_flowFacts_band` in the telescope form (head = the pin), or the pins need registry lines. `T2462_ProfileK` has `ThDecayK` under `∃ Cp`, where the scan does not look (`scanC` lists no top-level binder constants), so `Step5KerGen_ThDecay` needs no line.
F4 (cones.py) `Chain/NewKLKGen` is not in the certificate cone (forward closure of the six `Graph/LWExpCert*`: 168 modules; `Chain/NewKLKGen` False, `Induction/Step5Kit` True), so the leaf move of the T2462 dispatcher notes (`Chain/NewKLKGenBA.lean`) is allowed; its reverse cone is 1 module (`BA/NewKLKBA`). `NewKLKLGen` reaches `BA.FlowPins`, `BA.MFixedPoint` only through `NewKLKGen:8` (`import RBM3D.BA.FlowPins`; BA code at :838-841). Decision: dispatcher / 1a-audit; otherwise note (9) stands.
F5 (`cat docs/queue/T2463.state`, `git log --oneline -1 t/T2463`, `git diff --stat main...t/T2463`, run 17:53 UTC) `t/T2463` exists (= main `e288560e`, no commit of its own), state `proving` since 17:42:16 UTC; `git grep -c ZeroModeGen_WardCls main -- RBM3D RBM3D.lean` lists 0 files. Default D1 stands; the Ward text is fixed by whichever 1a-audit comes first (DECISIONS §270 note (7)).
F6 (CltGen:30, :126) X1a is merged. `STThg` = `Step2Gen_Theta (Mss·S) t` (Θ); `STThPropsg` = `∃ C₅ c₅ C₆ C₇, ∀ᶠ n`, mixed charges `σ 0 ≠ σ 1`, `zdistD`, linear `exp(−c₅|a|/ℓ)`, BD1, BD2, at `sz.lam n`. D2 reads `thetaKer`, all four charge pairs, `zdistInf`, the `√`-tail at `gK n`; X1b reads `STThPropsg`, not D2 ((a) line 66).
**(v) Reader table** (reader line ← object read ← feeder): IniTermI:306, IniTermII:332, DuhamelI:525 ← `Σ_b ‖Θ_u(a₁b)‖ 𝒯_s(b−a₂)` or its `STprof` form (`step5Kernel_profile_explicit_holds`) ← `ProfileK` with `Θ = 1 + uθ` ((a) line 66);
IniTermI:487, IniTermII:940, DuhamelI:600, :628 ← `step5Kernel_UN_decompU` ← T8 `Step5KerGen_UN_decomp`; IniTermI:2139 (`‖Θ x y‖` decay), :2201 (`Σ‖Θ‖‖Θ‖`: decay twice + `ekPropTInf_holds`) ← `ThDecayK`; DuhamelI:591 (`‖Θ(wμ)‖ ≤ ‖Θ(w)‖`) ← band positivity; the generic reader uses the row-sum clause.
**(vi) D3 table** (band fact with NewKLKL line → `NewKLKGenHyp` field with NewKLKGen line, or model-free): S support `newKLKL_SB_support` :145 (used :181) → F5(a) :387; row sums `sum_norm_SB_row` :207, :690, :704 → F5(b) :388; symmetry `SB_transpose` :699 → F5(c) :389; K marginals `newKLKL_ward_K` :456 (called :545) → F8 :399-404;
L marginals `newKLKL_ward_L` :379 (called :544) + `newKLKL_gres_blockMat_true` :496 → model-free, fed by F9 :405-411 (`LM = loopFine … ζ`, `GMM x x = Gres H ζ true x x − m`, `Im ζ = (1−u) Im m`) and the domain `κ ≤ Im m` (replaces `Ind.half_le_mE_im` :523); `(TTT2)` `hTTT` :769 → `ekPropTInf_holds`; `tailW_of_far` :595, `bound2` :606 (called :787) → model-free.
`Theta` and `mSigma` occur in NewKLKL only at :446-494 (`STKloop_eq`, `ward_K`), so F6 (:390) and F7 (:392-398) are not read by `newKLKL_at` :732-835. Extra fact needed: none; D3 passes.
**(vii) Scope table** (scope2.py: 74 public names, each in one class; the 20 size-level names have no law/model/spectral symbol in their signature, script check). Targets' band originals (17): T1 `st5_t_lt_one` Kit:192, `st5_mE_im_ge` Cases:409; T2 `ST_step5_caseI_of_pins` Kit:292; T3 `ST_step5_caseII_of_pins` Cases:542, `st5_compare_IIward` Cases:438; T4 `ST_step5_caseIII_of_pf` Cases:311; T5 `stStep5IV_holds` Kit:549; T6 `ST_step5_assembly` Kit:79;
T7 `stWardII_holds` WardII:269, `stWardII_identity` WardII:143; T8 `step5Kernel_decompU` :57, `_UN_decompU` :74; T9 `_theta_decay` :135, `_profile_explicit_holds` :199, `_norm_Theta_eq_re` :116; T10 `stNewKLKL_holds` NewKLKL:836; T11 `stTailtoTail_holds` TailtoTail:582. Reused size-level (20): Kit:96,101,120,144,149,182,187,200,215,436,444; Cases:57,84,100,120,146,175,281,418,532.
Law-level, restated at μ under the stem (4): Kit:45,63,280, Cases:39. Band only (2): Kit:351 `st5_mE_im_le_one`, Kit:362 `st5_Bctl_le_one`. Instance data (22): Kit:598-636 (8), Cases:707,713, Kernel:972-1068 (9), TailtoTail:597,612, TailtoTailSq:965. Other owner U5 (2): TailtoTailSq:906,932. No reader outside the file (7): Kernel:282,359,456,463,529,739,943.
**(iii) Layout** (cones.py, 521 modules). Reverse cones on main (ticket's 1debc23 value in brackets): Step5Kit 91 [86] (all six `LWExpCert*`), Step5Cases 45 [42], WardII 41 [38], TailtoTail 14 [14], Step5Kernel 7 [7], NewKLKL 6 [6], TailtoTailSq 6 [6]; the three new files 0.
Closures: Step5CasesGen 98 modules, Step5KerGen 97, NewKLKLGen 103; direct `BA/*` imports: none; transitive `BA/*`: 0, 0, 2 (`FlowPins`, `MFixedPoint`); no direct import is in the stop-rule list (the only stem match in the closures is `Path.Expansion`, reached through `Chain/Step5Gen` itself).
**(x) Premise scan** (scan.lean, `RBM.Audit.scanPremises` on this tree: 121 premises found, 0 unregistered). `STStep5ConclgL`, `STEtermsMidgL`, `STDuhamelIgL`, `STIniTermIgL`, `STDuhamelIIgL`, `STIniTermIIgL`, `STPfStep5gL` are Prop-valued, unregistered, concluded by no theorem and assumed by none today; they are the premises of the chains of `T2462_caseI/II/III` (check lines 215-228) and `T2462_assembly` (241) that nothing concludes.
To be concluded by this row: `FlowFacts` (T1 band), `WardIdent`, `STWardIIgL` (T7), `STStep5IgL`…`IVgL` (T2-T5). Already concluded: `STNewKLKLgL'` by `stNewKLKLgL'_band`, `STTailtoTailgL'` by `stTailtoTailgL'_band`, `Step2Gen_USemigroup` by `step2Gen_USemigroup_band`, `NewKLKGenHyp` by `newKLKGenHyp_band`, `baNewKLKGenHyp`.
Registry lines to append to `owedProps` (as the band `STStep5Concl`, `Test/Axioms.lean:208`): the seven names above; owners: U4-BA (b) for all, U4s3 for `STEtermsMidgL`/`STDuhamelIgL`/`STDuhamelIIgL`, U4s2 for `STIniTermIgL`/`STIniTermIIgL`, U5 for `STPfStep5gL`; shape rule F3.
**(xi) `open private` and copies** (priv.py; `lake env lean openpriv.lean`: exit=0, 14 names resolved). Step5CasesGen: `open private wardII_Bctl_le` (WardII:229), copy `wardII_prec_scale` (WardII:256, 11 lines, law-level); no other private is referenced by the nine band originals.
Step5KerGen: `open private step5Ker_zdistInf_sub_comm` (Step5Kernel:98), `step5Ker_tailW_eq` (:109) (both used by the probe, lines 27-29), `step5Ker_sq_aux` (:124) only if `step5Kernel_theta_decay` is re-proved; copies (F2): `newKLKL_tailT_shift` NewKLKL:56 (42 lines), `newKLKL_zdistInf_neg/_sub_comm/_add_le/_tri` :121-144 (23), `newKLKL_SB_support` :145 (19), `B45_row_thetaKer` B45:656 (13).
NewKLKLGen: copies `newKLKL_conv_two` :165 (57 lines), `_ward_LKM` :515 (75), `_bound2` :606 (130), `_at` :732 (103); `open private` of the model-free direct privates of those four: `_tailT_shift` :56, `_Cs_ge_one` :96, `_tailT_le_tailW` :102, `_tailW_eq_of_near` :107, `_zdistInf_sub_comm` :124, `_zdistInf_tri` :138, `_ward_L` :379, `_gres_blockMat_true` :496, `_zdistInf_le_L` :588, `_tailW_of_far` :595; `_SB_support` :145 and `_ward_K` :456 read band objects and are replaced by F5(a) and F8.
**(xii) Lines per file** (est2.py: `lines = r·(band spans) + fixed`; spans from spans.py: Step5CasesGen 586, NewKLKLGen 372; Step5KerGen is measured: 97 copied + 250 probe-measured + 80 assumed; assumed fixed parts: T1 FlowFacts 70, six band re-derivations 84, headers 50 per file, T8 `UN_decomp` 25, NewKLKLGen wrapper 80 + band result 35 + band example 40). Output:
```
low (r=1.0)      CasesGen   816  KerGen   427  NewKLKLGen   577  total  1820
central (r=1.2)  CasesGen   933  KerGen   427  NewKLKLGen   651  total  2011
high (r=1.6)     CasesGen  1168  KerGen   555  NewKLKLGen   800  total  2523
central total 2011 > 1950: True ; 2.6 x central total = 5229 ; per file 2.6 x central: [2426, 1110, 1693] ; stop line 2000 per file
split U4s1a = Step5CasesGen 933 ; U4s1b = Step5KerGen + NewKLKLGen 1078
```
Central 2011 > 1950: the pre-signed split applies (U4s1a = Step5CasesGen, U4s1b = Step5KerGen + NewKLKLGen); the 1a-audit confirms. Calibration: the probe's proofs of T8/T9 (12+58+74 lines) against their band originals (17+61+83) give 0.89.
**(xiii) Name clashes** (clash3.sh: `git grep -n -F -w` and `git ls-tree` for the 22 final names of the ticket and the 3 module stems over `main` and the 15 branches `t/T2450`-`t/T2461`, `t/T2463`, `t/T2464`, `t/T2466`): `TOTAL over all refs: 0`.
**Probe verdict.** Compiles, exit 0, standard three axioms; the D1 and D2 pins are provable as pinned (E1 text) and nonempty at `sz0` (band and non-band). Open for the 1a-audit: F2 (imports of `Step5KerGen`), F3 (band results in telescope form), F4 (leaf move), R1, the split of (xii).
### Completed fill-in table (rows owed to the probe step; numbers are lines of this file)
| # | deliverable | line / n/a |
|---|---|---|
| (i) | exponent table | line 6 |
| (ii) | instance + scripts | line 23; Lean-level instances: probe 259-329, lines 110-111 |
| (iii) | layout, cones, no `BA/*` | line 134; certificate cone and `NewKLKGen`: line 123 |
| (iv) | D1 decided, T2463 status, probe lines | line 65 (decision); probe 42-56, 259-269 (line 110); T2463: line 124 |
| (v) | D2 decided, probe lines, reader table, X1a | line 66 (decision); probe 61-250, 271-329 (line 111); readers line 126; X1a line 125; route and layout cost line 114 |
| (vi) | D3 table | line 67 (math); Lean-level table line 128 |
| (vii) | scope table, 74 band names | line 131 |
| (viii) | hypothesis table | line 69 |
| (ix) | UBA-C1 table | line 70; the comparison enters once, probe line 203 (line 111); E1: line 113 |
| (x) | premise scan, registry lines | line 136; shape rule line 116 |
| (xi) | `open private` list, copies (file:line) | line 139 |
| (xii) | lines per file against 2,000, 2.6×, split | line 142; math independence of the groups: line 68 |
| (xiii) | name-clash grep | line 151 |

## (a‴) Amend 1 (H254) — Mon Oct 12 18:22:45 UTC 2026
Stage 1b of U4s1a (this run) is bound by `docs/tickets/T2462-amend-1.md` (DECISIONS §273 (1)–(2)) and the check file as amended. The one comparison text is R1: `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`; it replaces E1 (§271 (4)) and the (a) line 4 text `Cmp(A)`. Split confirmed (Amend 1 item 6): this run = U4s1a = `Chain/Step5CasesGen` (targets 1–7) + seven registry lines in `RBM3D/Test/Axioms.lean`; U4s1b (`Step5KerGen`, `NewKLKLGen`, targets 8–11, the only statement of the comparison, target 9) runs on `t/T2462b`. Section (a) and (a″) are unedited; the parts of lines 4, 66, 111, 113, 152, 164 that state `Cmp(A)`, E1 or the probe instance `probeSz1.lam = 2·sz0.lam` concern target 9 only and are superseded for U4s1b by Amend 1 items 1, 3, 5.
State inherited from the stopped run: branch `t/T2462`, commit `ed45f1cd` (`Chain/Step5CasesGen`, targets 1–7); uncommitted: the instance section of `Step5CasesGen` and the seven `owedProps` lines. Check of that text against the Amend (script):
```
$ grep -nE "gK|withLam|lam0|BAflowLam0|seqHflowBA|Cmp|0 ≤ gK|A \* gK" RBM3D/Chain/Step5CasesGen.lean   (exit 1 = no hit)
$ grep -c "sz.lam" RBM3D/Chain/Step5CasesGen.lean  ->  28 at 18:22 UTC, 29 at HEAD d0aa6c00 (the docstring rewrap added mentions)
```
So no U4s1a declaration reads a coupling `gK` or states a comparison; every size-level read is `sz.lam` (UBA-C1: the case statements are U6's). Nothing written on the E1 text needs rework in this file. Stop rule: 2,000 lines (`wc -l` at each section commit).
D1 re-check at the start of this 1b (T2462.md D1 and note (7); 1a-audit §8 D1; Mon Oct 12 18:37:10 UTC 2026):
```
$ git log main -1 --format='%h %cd %s' --date=iso-strict -- RBM3D/Chain/ZeroModeGen.lean
01b4c521 2026-10-12T11:11:57-07:00 T2463: merge U U1s1 Chain/ZeroModeGen
$ git grep -n "def ZeroModeGen_WardCls" main -- RBM3D   ->   main:RBM3D/Chain/ZeroModeGen.lean:289:def ZeroModeGen_WardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) : Prop :=
$ grep -c "import.*ZeroModeGen" docs/tickets/checks/T2462-check.lean (Amend 1 version)   ->   0
$ git merge-base t/T2462 main   ->   62eed82c (62eed82 = the base of this branch, before the T2463 merge)
$ sed -n 289,296p RBM3D/Chain/ZeroModeGen.lean | grep -c 'conj\|starRingEnd'   (the lines of the class definition on main)   ->   0
```
Reading of the record: T2463 merged at 18:11:57 UTC, after the 1a-audit (18:07:20 UTC); DECISIONS §273 (2) keeps the 1a-audit D1 (`T2462_WardIdent` verbatim) and §273 (5) records T2463 as merged. So (a) line 65 ("T2463 held, not merged") is out of date. Decision taken here: the default D1 text is delivered unchanged (`Step5CasesGen_WardIdent`, `step5CasesGen_wardIdent_band`, `stWardIIgL_of` = the pins of the amended check); the amended check, the Layout import list and the registry list have no entry for a derivation from `ZeroModeGen_WardCls`, and Amend 1 item 7 keeps the 1a-audit decisions. The derivation (T2462.md D1 alternative) is not written: it needs an import of `Chain/ZeroModeGen` (not in the Layout list), a base that contains T2463, and a conjugation hypothesis for the one-index loops, which the class definition does not carry (grep above). It is listed in (d) for the dispatcher.
## (b) Script output (U4s1a) — Mon Oct 12 18:39:26 UTC 2026
Branch `t/T2462` at `d0aa6c00` (parent `ed45f1cd`); split: this report covers U4s1a only (`Chain/Step5CasesGen`, targets 1-7); scratch files are in the scratchpad subdirectory `T2462/`.
**Layout, build, line count, cones, siblings, diff.**
```
$ lake build RBM3D.Chain.Step5CasesGen | tail -1; warnings naming the file; wc -l; hygiene grep; imports; reverse cone (files importing it); clash.sh; git diff
Build completed successfully (3782 jobs). | warnings naming the file: 0 |      784 lines (stop line 2,000; 1a central 933, high 1,168) | sorry/admit/native_decide/axiom hits: 0
imports: Chain.Step5Gen Induction.Step5Cases Induction.WardII | files importing the module: 0 (reverse cone 0; the root import is the hub's)
closure: 5319 modules; RBM3D.BA.* in closure: []; stop-rule stem matches: [RBM3D.Path.Expansion, RBM3D.Induction.GridDuhamelN, RBM3D.Chain.GridDuhamelGen] 
clash.sh (git grep -F -w, 10 public names, main + 20 branches t/T2445..t/T2466 except t/T2462; git ls-tree for the module file): TOTAL over all refs: 0 module files: 0
git diff --name-only main...t/T2462: RBM3D/Chain/Step5CasesGen.lean RBM3D/Probe/T2462Pins.lean RBM3D/Test/Axioms.lean | diff lines on the ticket's no-edit list (Induction, Carrier, Step2Gen, Step2Kern, GridDuhamelGen, NewKLKGen, Step5Gen, BA): 0
diff of the file from its first `set_option` to the Instances heading, ed45f1cd vs HEAD: 663d662 < end RBM.BA 
$ lake env lean axclosure.lean  (#print axioms of the ten public declarations)
10 of 10 depend on [propext, Classical.choice, Quot.sound]: Step5CasesGen_FlowFacts step5CasesGen_flowFacts_band Step5CasesGen_WardIdent step5CasesGen_wardIdent_band stWardIIgL_of ST_step5_caseI_of_pinsgL ST_step5_caseII_of_pinsgL ST_step5_caseIII_of_pfgL stStep5IVgL_holds ST_step5_assemblygL 
```
**Statements against the pins** (`T2462_*`, amended check file Part 2, lines 181-245).
```
$ python3 -I defdiff.py;  lake env lean pins_u4s1a.lean   (check lines 181-245 verbatim + one typed example per pin: the theorem applied, `rfl` for the two defs)
T2462_FlowFacts -> Step5CasesGen_FlowFacts: identical (def text, whitespace-normalized, name substituted)
T2462_WardIdent -> Step5CasesGen_WardIdent: identical (def text, whitespace-normalized, name substituted)
pins: 10 defs, typed examples: 10; errors: 0; exit=0
$ python3 -I extract.py RBM3D/Chain/Step5CasesGen.lean   (`line: statement`, whitespace-normalized)
140: def Step5CasesGen_FlowFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop := ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧ ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → sz.Admissible 𝔠 𝔡 ∧ (∀ n, T0 sz z n < 1) ∧ (∀ n, κm ≤ ((mk sz z).m n).im) ∧ ∀ (n : ℕ) (t : ℝ), (mk sz z).eta n t = (1 - t) * ((mk sz z).m n).im
156: theorem step5CasesGen_flowFacts_band (d : ℕ) : Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
340: theorem ST_step5_caseI_of_pinsgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIgL d law Flow mk T0 → STIniTermIgL d law Flow mk T0 → STStep5IgL d law Flow mk T0
548: theorem ST_step5_caseII_of_pinsgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIIgL d law Flow mk T0 → STIniTermIIgL d law Flow mk T0 → STWardIIgL d law Flow mk T0 → STStep5IIgL d law Flow mk T0
406: theorem ST_step5_caseIII_of_pfgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → STPfStep5gL d law Flow mk T0 → STStep5IIIgL d law Flow mk T0
286: theorem stStep5IVgL_holds (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → STStep5IVgL d law Flow mk T0
169: theorem ST_step5_assemblygL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (hst : ∀ n, s n ≤ t n) (h : STStep5ConclgL C μ s t) : STDecaygL C μ t ∧ STDecayStronggL C μ t
187: def Step5CasesGen_WardIdent {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop := ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n), (C.L n u σ a ω - C.K n u σ a) - zeroModeSet d (sz.L n) {0} (fun a' => C.L n u σ a' ω - C.K n u σ a') a = (((C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω - C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) / ((((sz.size n : ℕ) : ℂ)) * (C.eta n u : ℂ))
198: theorem step5CasesGen_wardIdent_band {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| < 2) : Step5CasesGen_WardIdent (bandFM sz E)
205: theorem stWardIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → Step5CasesGen_WardIdent (mk sz z)) → STWardIIgL d law Flow mk T0
```
**Compiled nonempty instances and band re-derivations** (section `Instances`, `d = 3`, merged data `szB`/`szG`/`sz0`; deterministic hypotheses discharged by the merged `inst_*`; open: other gates' pins).
```
$ grep -nE "^example|^private theorem Step5CasesGen_wardIIgL_band" RBM3D/Chain/Step5CasesGen.lean  (first 58 chars) | band original re-derived
718:example : ∃ κm : ℝ, 0 < κm ∧ szB.Admissible (1 / 6) (1|T1  flow facts at (szB, zB): hflow.1, lemT_lt_one, st5_mE_im_ge, etaT_eq_etaOf
725:example : Step5CasesGen_WardIdent (bandFM szB (fun _ =|T7  WardIdent at bandFM szB (E = 0)
730:private theorem Step5CasesGen_wardIIgL_band (d : ℕ) :|T7  band tuple: stWardIIgL_of + stWardII_identity (private)
739:example (d : ℕ) : STWardII d := (STWardII_iff_gL d).2 |T7  = stWardII_holds (WardII:269) as STWardII d
742:example (Cd : ℝ) (hCd : 0 < Cd) :|T7  = inst_wardII (Step5Pins:988)
747:example (hE : STEtermsMid 3) (hD : STDuhamelI 3) (hI :|T2  = inst_skeletonI (Step5Kit:636)
754:example (hE : STEtermsMid 3) (hD : STDuhamelII 3) (hI |T3  = inst_skeletonII (Step5Cases:707), Ward pin discharged
761:example (hPf : STPfStep5 3) (Cd : ℝ) (hCd : 0 < Cd) :|T4  = inst_skeletonIII (Step5Cases:713)
767:example (Cd : ℝ) (hCd : 0 < Cd) :|T5  = inst_step5IV_proved (Step5Kit:618)
773:example (Cd : ℝ) (hCd : 0 < Cd) :|T6  after T5: (Eq:Gdecay), (Eq:Gdecay+s<g) at (szG, zB, 5/8, 3/4)
$ lake env lean inst_copy.lean  (examples renamed theorem scratchInst1..9, #print axioms): renamed 9, standard-three lines 9, errors 0
```
**Hypothesis table** (premise of a public result here | band discharge | BA source or owning row).
- `Step5CasesGen_FlowFacts` (T2-T7) | `step5CasesGen_flowFacts_band` (T1) | U4-BA (b): `BAFlow.1`, `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, the `eta` field of `baFM`.
- `STEtermsMidgL`, `STDuhamelIgL`, `STIniTermIgL` (T2); `STDuhamelIIgL`, `STIniTermIIgL` (T3) | U6 bridges `STEtermsMid_iff_gL`, `STDuhamelI/II_iff_gL`, `STIniTermI/II_iff_gL` with `stEtermsMid_of_LWT`, `stDuhamelI/II_holds`, `stIniTermI/II_holds` | owners U4s3 (`EtermsMid`, `Duhamel*`) and U4s2 (`IniTerm*`); BA: U4-BA (b).
- `STPfStep5gL` (T4) | `STPfStep5_iff_gL` with `stPfStep5_holds` | owner U5 (`PfStep5`); BA: U4-BA (b).
- `STStep5ConclgL` (T6) | the registered band `STStep5Concl` through `bandFM_STStep5Concl` | BA: U4-BA (b).
- `Step5CasesGen_WardIdent` (T7, hypothesis of `stWardIIgL_of`) | `step5CasesGen_wardIdent_band` (`stWardII_identity`) | BA: U4-BA (b) (`baK_ward`, `BAKsol_rotate`, `baKsol_one`); T2463's class: (d) 1.
- `STWardIIgL` (T3 premise) | concluded by T7 (`stWardIIgL_of`); band: private `Step5CasesGen_wardIIgL_band` | none.
**Greps of target 12 on `Step5CasesGen` (the U4s1a part; hits).**
```
(a) grep -cE 'withLam|lam0|BAflowLam0|seqHflowBA|gK|Cmp|A \* gK|sz.lam n \^ 2 ≤ A': 0
(c) grep -cE 'Ring.inverse|Matrix.of|cycProd' | '(def|theorem|lemma|abbrev) [A-Za-z_]*Ugen' | 'RBM.UN|\bUN d|uKer d|Theta d|thetaKer d|Ugen': 0 | 0 | 0
(b) grep -nE "mE|zt E|zt \(|2 - κ|\|E\||cltCk|etaT|norm_mE|PropSpin|EKsgn|Theta d|mSigma|STflowE|lemT|STFlow|seqHflow|seqP|SB d|‖m‖|Lloop|STKloop|KLK ", hits by label:
  total 27: band result T1 5; band result T7 2; band re-derivation T7 5; band-bridge helper flow_dom 2; instance T1 3; docstring T1 2; size-level helper compare_IIward (band lemma at E=0 inside the proof) 4; instance T6 4;
```
**Registry and pre-check** (seven `owedProps` lines: one per pin that a public result here assumes and nothing concludes).
```
$ git diff -U0 main...t/T2462 -- RBM3D/Test/Axioms.lean   (added names): STStep5ConclgL STEtermsMidgL STDuhamelIgL STDuhamelIIgL STIniTermIgL STIniTermIIgL STPfStep5gL 
$ lake env lean precheck.lean   (import RBM3D; import RBM3D.Chain.Step5CasesGen; #assert_rbm_axioms; then the premise scan with and without the seven lines)
exit=0 (started 18:29:34 UTC, tool log): axiom audit: 13379 theorems, 4253 definitions, 0 axioms in `RBM` (compil; scan: 128 premises found; seven names found: [true, true, true, true, true, true, true]; unregistered with the lines: []
unregistered if the seven lines were absent: [RBM.BA.STIniTermIIgL, RBM.BA.STDuhamelIIgL, RBM.BA.STEtermsMidgL, RBM.BA.STPfStep5gL, RBM.BA.STStep5ConclgL, RBM.BA.STIniTermIgL, RBM.BA.STDuhamelIgL] 
```
**Narrative.**
- Scope: U4s1a only (targets 1-7, `Chain/Step5CasesGen`). `Step5KerGen`, `NewKLKLGen` (targets 8-11) are U4s1b (Amend 1 item 6) and do not exist on this branch; `RBM3D/Probe/T2462Pins.lean` is unedited by this run.
- Amend 1 / R1: no declaration of the file reads a kernel coupling or states a comparison (greps (a), (c)), so R1 enters nowhere here. Its per-index lemma and the non-band instance (Amend 1 items 3, 5) belong to target 9 (U4s1b). The probe still holds the superseded texts (`T2462Pins.lean:74` E1, `:297` `sz0.withLam`); it is never merged.
- Stopped run: the code before the `Instances` heading equals `ed45f1cd` (diff line above: only the closing `end RBM.BA` moved below the new section). Stop-line counts at the section commits (`git show <commit>:<file> | wc -l`): `ed45f1cd` 697, `d0aa6c00` 784 (stop line 2,000). New in `d0aa6c00`: the `Instances` section (9 examples), the module docstring re-wrapped to 100 columns (no warning names the file) and the seven registry lines.
- Ports: all from RBM3D band files, cited by file:line in the module docstring; no RBM1D/RBM2D source. Last commits on main: `Step5Kit` 85e43dbe, `Step5Cases` 30ed55ad, `WardII` 8ec98a60, `BA/Step1Fam` 596a83a2 (route of target 5, `Bctl_le_one_of_conStInd`), `Induction/ScaleFacts` 5d1e6b13 (`STBctl_mono`, copied as private `Step5CasesGen_Bctl_mono`). One `open private` (`wardII_Bctl_le`, line 38); `wardII_prec_scale` is copied as `Step5CasesGen_prec_scale`.
- Instances: the nine examples apply targets 1-7 at the merged `d = 3` data and re-derive the merged band instances (table). Open hypotheses are other gates' pins (`STEtermsMid 3`, `STDuhamelI/II 3`, `STIniTermI/II 3`, `STPfStep5 3`) and the Steps 1-4 premises inside `InstIng5Concl`, as in the merged `inst_*`. No `N = 0`, empty index set or collapsed window: `szB` has `L = 4`, `W_n = n + 4`.
- Registry: without the seven lines the scan reports exactly these seven names as unregistered; with them none. `#assert_rbm_axioms` passes on `import RBM3D` + this module. The root `import` line is the hub's merge step and is not edited.
- D1: the default text is delivered; T2463 is merged, see (a‴) and (d) 1.
## (c) Verified Mathlib names
Each name occurs in `Chain/Step5CasesGen.lean`, resolves in a `run_cmd` over the module's environment (`env.getModuleIdxFor?`, module root `Mathlib`), and the file builds: `inv_anti₀`, `div_le_self`, `one_le_pow₀`, `Real.rpow_le_one_of_one_le_of_nonpos`, `Real.one_le_rpow`, `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_mul`, `Real.rpow_add`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_zero`, `Real.sqrt_sq`, `Complex.abs_im_le_norm`, `norm_div`, `Complex.norm_real`, `Complex.norm_natCast`, `Real.norm_of_nonneg`, `Filter.tendsto_atTop_mono'`, `tendsto_natCast_atTop_iff`, `tendsto_rpow_atTop`, `norm_add_le`, `lt_of_mul_lt_mul_left`. Names verified absent: none looked up (the bare `tendsto_atTop_mono'` is absent; the file uses it as `Filter.tendsto_atTop_mono'` under `open Filter`).
## (d) Open issues and paper-delta candidates
1. **D1 alternative and T2463 (dispatcher decision wanted; does not block this row's targets).** T2463 is merged (`01b4c521`); T2462.md D1 calls for deriving the identity from `ZeroModeGen_WardCls` in that case, while the 1a-audit D1, Amend 1 item 7 and the amended check keep the pinned default, which is what is delivered. If the derivation is wanted: a bridge `ZeroModeGen_WardCls sz C` plus conjugation of the one-index loops (`L^{(1)}_- = conj L^{(1)}_+`, same for `K`; not in the class) gives `Step5CasesGen_WardIdent C` by the rotation and Ward step of (a) line 65 (the Lean proof would parallel `stWardII_identity`, `WardII:143`). It needs an import of `Chain/ZeroModeGen`, a base containing T2463, and a decision on the conjugation hypothesis (a named `Prop` for it would, by the scan rule of the probe step F3, need an eighth registry line).
2. Paper-delta candidate `T2462a` (as (a) O3, restricted to this file): the generic kit takes `Step5CasesGen_FlowFacts` and `Step5CasesGen_WardIdent` as carrier data (hypotheses of targets 2-7, discharged at the band by targets 1 and 7). No other statement difference from the paper.
3. The proof of the private `Step5CasesGen_compare_IIward` uses the band lemma `st5_compare_IIward` at `E = 0` (grep (b) label); its statement is size-level with `η` and `κm`, so nothing in a public signature mentions the band energy.
