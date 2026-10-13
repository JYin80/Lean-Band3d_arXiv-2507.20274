Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct 13 02:31:34 UTC 2026
Stage 1a design gate D1-D4 of T2484 (mathematics only; no Lean written). Tree: worktree `t/T2484` = `main` 86eb22f2 (`main` is 1e73b1b8 at 02:31 UTC: T1b merge, touches only `OptL2Gen`, `Step2CloseGen`, `Test/Axioms.lean`, `RBM3D.lean`). `S` = scratchpad `T2484/` (python3+numpy, my scripts). `d=3`; `Θ=Step2Gen_Theta(X)`, `X=M^{(σσ')}S`, `θ=XΘ` (Step2Gen:164-192); `Λ=𝔡⁻¹`; "band" = `bandFM`, `gK=sz.lam`.
Math fixed here. **(M1)** `Step2Gen_USemigroup` gives `(1-vX)Θ_v=1`, hence (finite dimension) `Θ_v=1+vθ_v` and `Θ_v-Θ_w=(v-w)θ_vΘ_w`; with `(1-v)‖θ_v‖∞≤C₆` (ThDecay) `‖Θ_w‖∞≤(1+C₆)/(1-w)` and `|Θ_v-Θ_w|_{xy}≤|v-w|C₆(1+C₆)(1-t)⁻²` for `v,w≤t`: the band Lipschitz step (IniTermI:1628-1655) with `c*=C₆(1+C₆)²` in place of 1. **(M2)** `Step2Gen_UN` slots carry the pairs `(σ0,σ1)` and `(σ1,σ0)` (Step5KerGen:71-77); the band hides this (`m(σ0)m(σ1)=1`, IniTermI:1807). **(M3)** `iniTermI_ward` (IniTermI:2646) needs only the norm of the last-label sum.
### (i) Exponent table (values from the output in (ii); `κ=ε=𝔡=1/10`, `𝔠=1/6`)
| # | quantity | constraint | slack |
|---|---|---|---|
| 1 | `Λ=𝔡⁻¹=10`, guard `0<gK≤Λ` | eventually `0<gK≤lam≤Λ` from R1 and `Admissible` | band lam=1 vs 10 (10×); BA g=10: g₀=4.42 (2.3×) |
| 2 | `A` of R1 `lam²≤A gK²` | band 1; BA `(κ+1)/κ` from `κ/(κ+1)≤t₀` (TwistStep2:731) and `TwistStep2_lam0_sq` (:740) | BA with Im z=1: `g²/g₀²=A` exactly (2.640, 3.862, 5.113 at g=1/64,1,10) |
| 3 | `κm=√(2κ)/2` (Step5Cases:409); `κ'=cltCk(κ/2)≤min(1,Im m)` (CltResolvent:222,710) | `κm,κ'≤inf_{|E|≤2-κ}Im m=cltCk(κ)` | 0.2236, 0.2222 ≤ 0.3122 (inf); at zB: Im m=0.9682 |
| 4 | `δ=ε/2`: `N^{-1+δ}≤1-T0` eventually (Green/Pins:1049) | zB, `T0=0.98399` | n=0: 3.70e-4 vs 1.60e-2 (43×); n=1000: 3e8× |
| 5 | `Admissible 𝔠 𝔡`: WO `W^{-d/2+𝔡}≤lam≤Λ`, `N^𝔠≤W` | szB (L=4, W=n+4, lam=1) | 0.1436≤1≤10; `N^{1/6}=4.000≤W=4` (equality; n=1: 4.47≤5); 0 violations for n≤2e5 |
| 6 | regimes (i) `lam²/L²≤1-t, 1-s≤lam²`; (ii) `lam²/L^d≤1-t, 1-s≤lam²/L²` | s<t≤T0 | (i) (7/8,15/16): equality at 1-t; interior (0.895,0.9): 0.0625<0.1; (ii) (15/16,31/32): 1/64≤1/32, 1-s=lam²/L² (equality) |
| 7 | `𝔠d=1/100`, `(con_st_ind)` `Bctl^{𝔠d}≤(1-t)/(1-s)<1` (eventual) | `Bctl=W^{-d}Bparam(..,0)` | (0.895,0.9): iff n≥2; merged pattern (7/8,15/16): iff `W_n≥1.147e10` (astronomical, eventual only) |
| 8 | grid: `M_n=N^{14}` points, `|u-v|≤N^{-14}`, error `16c*N^{-5}≤N^{-3}` | `N²≥16c*`, `c*=C₆(1+C₆)²` (band: `N²≥16`) | C₆=1: N≥8, N=4096: 2.6e5×; C₆=3: N≥27.7 |
| 9 | `N^{-3}≤ζ`: `2(𝔡⁻²)^{6/5}≤N^{4/5}` (IniTermI:1879) | size level only | 502.4≤776.0 at N=4096 (1.54×), N≥2378 |
| 10 | `(1-t)⁻¹≤N²` (IniTermI:1846) | regime (i), `STAI≥1` | 16≤1.68e7; 10≤1.68e7 |
| 11 | `C₆` row sum `(1-v)‖θ_v‖∞` | ThDecay | measured 1.000000 (tight), band and BA |
| 12 | `C₈, Cs` (`c₀=1/2`) needed | `|Θ̊|(gK²+1-t)(|x|+1)^{d-2}`; `|Θ_σσ|/(δ+gK²e^{-c₀|x|})` | band C₈ 0.98/1.97/118.7, BA 0.98/1.24/252.4 at g=1/64,1,10 (t=0,a=b forces ≥99.4 at g=10); Cs≤4.23 (E=1.9) |
| 13 | Lipschitz (M1) | `|Θ_v-Θ_w|≤|v-w|C₆(1+C₆)Tm²` | measured/bound 0.0016 (band), 0.0017 (BA) |
| 14 | crossing `𝒯^{gK}≤A𝒯^{lam}` (Step5KerGen:275) | R1 | max ratio/A 0.66, 0.72, 0.49 at g=1/64,1,10 |
| 15 | swap `Θ^{(-+)}=Θ^{(+-)}` (finding E1) | not implied by `FlowFM` | band 0, BA 1e-18, `M` non-symmetric 7.2e-2 |
### (ii) One concrete nondegenerate instance (all hypotheses of T1-T11 at once; D1 fields at band and BA kernels)
Data: `d=3`; `szB` (Step34Pins:710) at n=0: `L=4, W=4, lam=1, N=4096`; `zB=1/2+i/64` (:765); `(κ,ε,𝔠,𝔡)=(1/10,1/10,1/6,1/10)`; case (i) `(s,t)=(0.895,0.9)` (interior) and the merged `(7/8,15/16)`; case (ii) `(15/16,31/32)`. Kernels: band `SB(g)` and the BA kernel at `g₀<g` (Im z=1, `L=4`), `g=1/64,1,10`, `t` up to `1-10⁻⁵` (finite `L`: constants and identities only). External (eventual) hypotheses `Admissible`, `STConStInd`, `N^{-1+δ}≤1-T0`: limit lines of `inst.py` (0 violations n≤2e5; thresholds of `STConStInd` in row 7). `IsProbabilityMeasure`, Steps 1-4 premises: other gates' pins, hypotheses of the example.
`$ cd /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2484 && for f in inst.py kerfacts.py d2.py swap.py; do echo "== python3 $f"; python3 $f; done`
```
== python3 inst.py
zB=(0.5+0.015625j): msc=-0.247983+0.960467j |msc|^2=T0=0.98399229 (>= 31/32=0.96875) E=lemE=0.499984 |E|<=2-kappa:True Im mE(E)=0.968248
kappa_m=sqrt(2k)/2=0.2236 <= Im m:True; kappa'=cltCk(k/2)=0.2222 <=Im m:True <=1:True; inf_{|E|<=2-k} Im m=cltCk(k)=0.3122; delta=eps/2=0.05
size/flow data at n (N=(WL)^3; WO; Bandwidth; N^(-1+eps)<=Im z; 1-T0 vs N^(-1+delta))
 n=0: N=4096 WO 0.1436<=1.0<=10.0:True; N^c=4.000<=W=4:True; N^(-1+eps)=5.61e-04<=Imz=0.0156:True; 1-T0=1.601e-02 vs N^(-1+delta)=3.700e-04: 43.3x
 n=1000: N=64771076096 WO 0.0001<=1.0<=10.0:True; N^c=63.372<=W=1004:True; N^(-1+eps)=1.86e-10<=Imz=0.0156:True; 1-T0=1.601e-02 vs N^(-1+delta)=5.360e-11: 2.99e+08x
n<=200000 violating WO, Bandwidth, N^(-1+eps)<=Im z, N^(-1+delta)<=1-T0: 0 ; N_n=(4(n+4))^3->inf
regime (ii) window (s,t)=(15/16,31/32): lam^2/L^d=0.01562<=1-t=0.03125: True; 1-s=0.0625<=lam^2/L^2=0.0625: True; s<t<=T0:True
regime (i) window (s,t)=(0.875,0.9375): lam^2/L^2=0.0625<=1-t=0.0625: True; 1-s=0.1250<=lam^2:True; s<t<=T0:True; (1-t)^-1=16<=N^2=1.68e+07
   con_st_ind Bctl^(1/100)<=(1-t)/(1-s)=0.5000<1: n=0 Bctl^cd=0.9609; holds iff W_n>=1.147e+10, i.e. n>=11472512971 (eventual hypothesis; Bctl decreasing in W)
regime (i) window (s,t)=(0.895,0.9): lam^2/L^2=0.0625<=1-t=0.1000: True; 1-s=0.1050<=lam^2:True; s<t<=T0:True; (1-t)^-1=10<=N^2=1.68e+07
   con_st_ind Bctl^(1/100)<=(1-t)/(1-s)=0.9524<1: n=0 Bctl^cd=0.9599; holds iff W_n>=5.194, i.e. n>=2 (eventual hypothesis; Bctl decreasing in W)
grid: 16 c* N^-5 <= N^-3 iff N^2>=16c*: C6=1.0 c*=4.0 -> N>=8.0; at N=4096 slack factor N^2/(16c*)=2.621e+05
grid: 16 c* N^-5 <= N^-3 iff N^2>=16c*: C6=3.0 c*=48.0 -> N>=27.7; at N=4096 slack factor N^2/(16c*)=2.185e+04
zeta_ge: 2(dd^-2)^(6/5)=502.4 <= N^(4/5): N>=2378; N(n=0)=4096: N^(4/5)=776.0; STAI=lam^2 W^d=64>=1
== python3 kerfacts.py
BAND d=3: X=mu*SB(g), mixed mu=m conj m=1, same mu=m^2; t in {0,.3,.9,.99,.999,.9999,.99999}; kappa=1/10 (|E|<=1.9)
  L=3 E=1.0 g=1 Imm=0.87         colsum relerr<=4e-12 C8_needed=   1.93 Cs_needed(c0=1/2)= 0.50
  L=4 E=0.0 g=0.01562 Imm=1.00   colsum relerr<=2e-12 C8_needed=   0.98 Cs_needed(c0=1/2)= 1.00
  L=4 E=0.0 g=1 Imm=1.00         colsum relerr<=1e-11 C8_needed=   1.97 Cs_needed(c0=1/2)= 0.50
  L=4 E=0.0 g=10 Imm=1.00        colsum relerr<=1e-11 C8_needed= 118.71 Cs_needed(c0=1/2)= 0.92
  L=4 E=1.9 g=0.01562 Imm=0.31   colsum relerr<=2e-12 C8_needed=   0.98 Cs_needed(c0=1/2)= 4.23
  L=5 E=1.0 g=1 Imm=0.87         colsum relerr<=4e-12 C8_needed=   1.98 Cs_needed(c0=1/2)= 0.50
BA d=3 L=4, z=0.3+i (Im z=1): m(z,g) from (self_m), t0=Im m/(Im m+Im z), g0=sqrt(t0) g, E_f=BAflowE, m0=m/sqrt(t0); X=BAMss at (g0,E_f,m0); kappa:=Im m(z,g)
  BA g=0.01562 g0=0.009616       colsum relerr<=3e-11 C8_needed=   0.98 Cs_needed(c0=1/2)= 1.00 | A=(k+1)/k=2.640=g^2/g0^2:True R1:True selfm-res=2e-16 Imm0=0.99>=k:True |rowsumK-1|=3e-15
  BA g=1 g0=0.5088               colsum relerr<=5e-11 C8_needed=   1.24 Cs_needed(c0=1/2)= 2.49 | A=(k+1)/k=3.862=g^2/g0^2:True R1:True selfm-res=2e-16 Imm0=0.69>=k:True |rowsumK-1|=1e-15
  BA g=10 g0=4.422               colsum relerr<=4e-11 C8_needed= 252.38 Cs_needed(c0=1/2)= 0.20 | A=(k+1)/k=5.113=g^2/g0^2:True R1:True selfm-res=1e-16 Imm0=0.55>=k:True |rowsumK-1|=2e-15
== python3 d2.py
  band mixed g=1 (X=S)       resolvent-identity err=1e-14; C6=max(1-v)||theta_v||_inf=1.000000; max entry |Th_v-Th_w|/(|v-w| C6(1+C6) Tm^2)=0.0016
  BA g=1.0 g0=0.5088 (X=K)   resolvent-identity err=1e-14; C6=max(1-v)||theta_v||_inf=1.000000; max entry |Th_v-Th_w|/(|v-w| C6(1+C6) Tm^2)=0.0017
  crossing g=0.01562 g0=0.009616 A=2.640: max tailT^g0/(A tailT^g)=0.6620
  crossing g=1 g0=0.5088 A=3.862: max tailT^g0/(A tailT^g)=0.7151
  crossing g=10 g0=4.422 A=5.113: max tailT^g0/(A tailT^g)=0.4924
== python3 swap.py
  band-like M=m*I, S=SB-like symmetric         |Th(+-)-Th(-+)|=0.0e+00  |Th(+-)-Th(+-)^T|=1.4e-17
  BA-like M symmetric, S=1                     |Th(+-)-Th(-+)|=1.2e-18  |Th(+-)-Th(+-)^T|=6.9e-18
  M non-symmetric, S=1                         |Th(+-)-Th(-+)|=7.2e-02  |Th(+-)-Th(+-)^T|=7.2e-02
```
### Decisions and tables (mathematics)
**D1 (kernel facts).** `T2484_KerFacts` kept, plus **E1** (required): a fourth conjunct, no guard: `∀ n t∈[0,1) σ, STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t`. Why: by (M2) the mixed `𝒰^{(2)}=K_A⊗K_B` has `K_B` built from `Θ^{(σ1σ0)}`, but `STfFarg` (CltGen:36, merged, X1-C4) uses `Θ^{(σ0σ1)}` in all its three places and `STThPropsg` gives symmetry, translation invariance and decay for each pair separately; target 8 (c) (`iniTermI_Sfull_decomp`, IniTermI:1302) needs `Θ^{(σ1σ0)}(a1,b2)=Θ^{(σ0σ1)}(b2,a1)`. Not implied by the `FlowFM` shape (swap.py row 3). Sources: band `bandFM_STThg` (CltGen:201), both sides `Theta d L lam (t·mσ mσ')`, `mul_comm`; BA `BATheta_swap` (KBase:350, unconditional) with `Step2Kern_Mss (baFM ..)=BAMss ..` (`Step2Kern_Mss_of_kron`, Step2Gen:238; U4-BA (a)). Case (ii) needs no swap (zero mode only on the first slot); with E1, `Θ_A(u)=Θ_B(u)` gives `1-uX_A=1-uX_B`, so `K_A=K_B` for `u>0` and the band's single-kernel lemmas (§4, §6) copy without a two-kernel rewrite. All other fields are true as stated (kerfacts.py: colsum, zero mode, short, R1 at band and BA; BA `BASelf` residual 2e-16 at `(g₀,E_f,m₀)`, so the scaling identity of MFixedPoint:295-352 is as read).
**D2 (wrapper).** PASS: table (v); `HCltOf` at `t'∈(s,t]` needs only `t`-free fields, `t'<1` (`t'≤t≤T0<1`), `N^{-1+δ}≤1-T0≤1-t'`, `STReg5I s t'` and `STLocalEntryUgL/STGdecayWgL` at `t'` (restriction, IniTermI:1573-1600; `STBctl_mono`, ScaleFacts:74).
**D3 (Ward).** `ZeroModeGen_WardCls` (ZeroModeGen:289), no conjugation: `iniTermI_ward` bounds `‖Σ_{b₂}‖≤(2W^dη)⁻¹(‖X₊‖+‖X₋‖)`, which is `|κ_W|(‖X₊‖+‖X₋‖)` from the rotated Ward family; `B45_ward_fing` (t/T2480b:B45Gen:117, 15 lines) is on `t/T2480b` (T2480 state `proving`), not on `main`: inline copy (~25 lines) unless merged at 1b start. `Step5CasesGen_WardIdent` (:187) is the index-0 average with `Im X₊`; for the last label it needs the cyclic swap of `L,K`, a field `FlowFM` does not have (Carrier:55-72).
**D4.** Split confirmed, row sizes in (xii). Ticket-text corrections: reader lines in the worktree are IniTermII 980-983 (col sum), 1060/1084 (zero mode), 1386 and IniTermI:1237 (short); `IniTermII` §3, §4, §6 are not model-free (`Theta d L g` in the statements: lines 330, 374-437, 669-787), so they are regenerated, not opened; target 7 reads `hLK 2` (`STLKgL .. s`, IniTermI:2050; `STLKUgL` at `u=s` implies it). Paper-delta candidates: `T2484a` (ticket), `T2484b` (`Θ^{(+-)}=Θ^{(-+)}` as carrier datum, E1).
**(iii) Hypothesis table** (band fact → class field → band discharge → BA source): USemigroup → T1 (i) → `step2Gen_USemigroup_band` (GridDuhamelGen:58) → `BAuKer_self/_comp`. ThDecay@gK → T1 (ii) → `step5KerGen_thDecay_band` (Step5KerGen:242) → `NewKLKBA_tail` (NewKLKBA:269) + `baComp_row_le` (EMn2BA:386). R1 → T1 (iii) → `A=1` → `TwistStep2_lam0_sq` (TwistStep2:740). col sum (IniTermII:980-983) → T1 (iv-a) → `sum_Theta_row_of_three_le`, `Theta_transpose_of_three_le` (Props4:114, 95) → `BATheta_row_sum_pm` (KBase:381), `BATheta_swap` (:350), `BATheta_isSymm` (:371). zero mode (:1060, 1084) → T1 (iv-b) → `prop8ZeroMode_holds` (Prop5Hold:1266), `Theta0_apply_eq` (Props4:243), shift (:100) → `baProp8_holds` (Prop6Path:1009), `baP8_BATheta_shift` (:497), `BATheta0` (MFixedPoint:519) = `Θ-L^{-d}(1-t)⁻¹` from the col sum. short (:1386, IniTermI:1237) → T1 (iv-c) → `prop5Short_holds` (Prop5Short:400) → `baProp5s_holds` (BA/Prop5Short:667). swap (E1) → T1 (v) → above. Ward → T9 premise → `zeroModeGen_wardCls_band` (ZeroModeGen:299) → UN-C3 owner.
**(v) D2 table** (wrapper field → `HCltOf` field → band line → BA): `κ'≤Im m` → (f) → CltFarG:937 (`cltCk_facts`) → `BAdom`, `Im m₀=Im m/√t₀≥κ`; `N^{-1+δ}≤1-T0` → (f), monotone in `t'≤T0` → :938 (`v3_premises_of_stFlow`) → `EMn2BA_T0_lt_one`; `CltRepg` → (g) → `cltRepg_band` (CltGen:176) → `H₀=g₀Ψ`, `g'=0`, `E=BAflowEs`; `Σ|M|²≤1` → (d) → `bandFM_M_le` (:183) → `BAK_row_sum` (KKernel:124, K=|M|²); per `s` under `STReg5I`: `STMfarg` → (e) → `bandFM_STMfarg` (:188) → `baOffDiag_holds`; `STGijDecgL`, `STKfargL` → (b), (c) → FarEntry:1724, 1731 → `baGbEXPij'_holds`, `baEMn2ExpHK`; `STThPropsg`, `STKpropsg`, `STExpInvgL` → premises of `STCltFargL` → CltFarG:911, 917, ExpInv:570 → U4-BA (C9). Closure `t↦t'`: all `s`-only fields unchanged; `t'`-fields in D2 above; `Cd` from the pin prefix, `𝔠d=1/100` (CltFarG:928).
**(vii) Readers** (object ← feeder): IniTermI:306, IniTermII:332 `(1-s)Σ_b‖Θ_u(a₁,b)‖𝒯_s(b-a₂)≤C𝒯_u(a₁-a₂)` (tails at lam) ← `step5KerGen_profile_holds` (Step5KerGen:308) on `θ`, `Θ=1+uθ` (constant `Cp+1`), windows (i) `lam²/L²≤1-u`, (ii) `1-s≤lam²/L²`; IniTermI:487, IniTermII:940 `𝒰^{(2)}=K_A⊗K_B`, `K=αI+βΘ_u` ← `Step5KerGen_UN_decomp` (:71) with M1; IniTermI:2139 `‖Θ_u(x,y)‖≤C(g²)⁻¹PI` ← ThDecay entry at gK, crossing, `1≤(Λ²+1)𝒯_u(0)`; IniTermI:2201 `Σ_b‖Θ‖‖Θ‖≤C(1-u)⁻¹𝒯_u` ← ThDecay twice, `ekPropTInf_holds`, crossing.
**(viii) Scope** (script classification by statement; names: probe step): `IniTermII` 64 decls: 43 private reused by `open private` (788 lines: §1, §2, §5, free parts of §6, §7, §9, §10), 16 regenerated (722 lines: §3, §4, §6 `Kf`/`bil`, §7, §8, §9 `core_same`, §10 lift, §11), 5 instance-section decls (57 lines) → T10 data; public 8: `iniTermII_core/_core_same` → T2, `iniTermII_concl` → T3, `stIniTermII_holds` → T4 (band, unchanged), 4 instances. `IniTermI` 121 decls: 71 public reused by name (1,550 lines: the free-statement decls of §1-§2', §5'-§6', §8', §10-§11, §13-§15, §17-§21), 41 regenerated (1,826 lines: §3'-§4, §7-§10, §12 → T8; §13 → T6; §14-§15 → T7; §16-§18, §20 → T8; §22 → T9), 9 instance-section decls (74 lines) → T10; `stCltFar_uniform`, `stIniTermI_holds` stay as bands.
**(ix) UBA-C1** as planned (ticket table): R1 enters inside `step5KerGen_profile_holds` and the crossing (rows 2-3, 8); `gK²≤lam²` also bounds the short-range term `gK²e^{-c₀r}≤lam²e^{-c₀r}`; targets 6-7 cross nothing (size level `lam`) but M1 reads the row-sum clause of ThDecay at gK, so they need the guard (g) (`0<lam n→0<gK n`, `gK n≤lam n≤Λ`, from R1) at the grid indices: the ticket's table entry "never" is "only (g)"; E1 is `t`-free, no R1.
**(x)** Lean-level scan: probe step. Premises nothing in `RBM` concludes: none expected (`ZeroModeGen_WardCls` ← ZeroModeGen:299; `FlowFacts` ← Step5CasesGen:156; KerFacts, CltFlow ← band results here with the class as conclusion head, T2462 F3); registry: owner text of `STIniTermIgL/IIgL` (Test/Axioms:211-212) only.
**(xi)** `open private … from RBM3D.Induction.IniTermII`: the 43 of (viii) (precedent Step5KerGen:39); copies under the stems: `Step5KerGen_cmp_pos` (:263), `Step5KerGen_tailT_cross` (:275), the 16 regenerated; names: probe step.
**(xii) Lines** (script `size.py`; `ρ=0.81` = T2462b new 927 / band model-bound 1,143; central = ρ·band model-bound lines + owed extras): IniTermIIGen 0.81·740+100 = **699** (2.6×: 1,818), CltFarUGen 0.81·443+190 = **549** (1,427), IniTermIGen 0.81·1,438+25 = **1,190** (3,093: reserve `IniTermIGen2` at 1,800). U4s2a 699; U4s2b 1,739 (cap 1,950; 2.6×: 4,520 over three files); total **2,438** < 3,900: no third row; the ticket's 2,300 is within 7%.
**(xiii)** `git grep -w` of the final names on `main`, `t/T2473`, `t/T2478b`, `t/T2480`, `t/T2480b`, `t/T2481`, `t/T2482`, `t/T2483` and the tickets T2473/T2480/T2482/T2483: 0 hits (also on `main` 1e73b1b8); `git ls-tree` finds no `IniTermIIGen`/`IniTermIGen`/`CltFarUGen` file on any of them.
### Fill-in table (H250 (4))
| # | deliverable | line |
|---|---|---|
| (i) | exponent table | line 6 |
| (ii) | instance + scripts | line 24 |
| (iii) | hypothesis table | line 71 |
| (iv) | D1 decided (E1); probe lines | line 67; probe lines: probe step |
| (v) | D2 table, closure | line 72 |
| (vi) | D3 decided | line 69 |
| (vii) | reader table | line 73 |
| (viii) | scope table | line 74 |
| (ix) | UBA-C1 | line 75 |
| (x) | premise scan, registry | line 76 (scan itself: probe step, Lean text) |
| (xi) | `open private`, copies | line 77 (names: probe step) |
| (xii) | lines per file, split | line 78 |
| (xiii) | name-clash grep | line 79 |
### Verdict (per target)
T1 **PASS with E1**: conjuncts (i)-(iv) have band and BA sources (iii) (the uniformity in `L` is the content of the merged pins `Prop5Hold:1266`, `Prop5Short:400`, `Prop6Path:1009`, `BA/Prop5Short:667`; kerfacts.py, d2.py are finite-`L` checks of the constants and identities); the check's text lacks the swap conjunct, which target 8 (c) needs. T2, T3 PASS: `Step5KerGen_UN_decomp` + KerFacts + `step5KerGen_profile_holds`; the lift is `of_subset` (`iniTermII_lift`, IniTermII:1567), so no `IsProbabilityMeasure`, as in the check's T4. T4 PASS (conclusion head `STIniTermIIgL`). T5 PASS (D2, closure shown). T6 PASS (`Iff` after `bandFM_STfFarg`, CltGen:208, and `Prec sz=PrecL sz (seqP sz)`). T7 PASS (stCltFargL at the worst grid time through D2; M1 for the Lipschitz step; thresholds rows 8-10 eventual in n). T8 **PASS with E1**. T9 PASS (T7 + the Ward step of D3; hypotheses of the check suffice). T10 PASS (data of (ii)). T11 PASS (the only outside readers `stIniTermI_holds`, `stIniTermII_holds` keep their statements; no band file edit is needed). No stop rule fires; central 2,438 < 3,900. Open for the probe step and the 1a-audit: E1 text, probe lines of (iv)-(vi), names for (x), (xi).

## (a″) Probe compile — Tue Oct 13 02:56:18 UTC 2026
Probe step of T2484 (prover-hard, `claude-sonnet-5-5`). File `RBM3D/Probe/T2484Pins.lean` (398 lines, never merged, no root import), committed on `t/T2484` as 354ff913 (worktree base `main` 86eb22f2; `main` is 78f4cc14 at the end of the step: it adds `Chain/B45Gen`, `OptL2Gen`, `Step2CloseGen`, `Graph/BAMomentExpGen`, 4 import lines in `RBM3D.lean` and changes 16 lines of `Test/Axioms.lean`; the probe imports none of the new modules, only `Test/Axioms.lean` among the changed files; diff stat below). Section (a) is unchanged. Everything below is script output; the narrative is the findings list at the end.
### Compile (command, exit code, output)
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2484 && date -u; lake env lean RBM3D/Probe/T2484Pins.lean; echo "exit code: $?"; date -u
Tue Oct 13 02:52:25 UTC 2026
new premises found by the scan: []; with the two band results withheld from the proofs: [RBM.BA.T2484_KerFacts,
 RBM.BA.T2484_CltFlow]
RBM.BA.iniTermGen_kerFacts_band: [propext, Classical.choice, Quot.sound]
RBM.BA.iniTermGen_cltFlow_band: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_cltFar_of_cltFlow: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_UN_rep: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_zero_bound: [propext, Classical.choice, Quot.sound]
RBM.BA.probe_core2_band: [propext, Classical.choice, Quot.sound]
exit code: 0
Tue Oct 13 02:52:37 UTC 2026
```
### Class texts against the check file (`docs/tickets/checks/T2484-check.lean`), by script
```
$ python3 -I diffdefs.py   (the `def T2484_KerFacts` / `def T2484_CltFlow` blocks of the check and of the probe)
== T2484_KerFacts: check 17 lines, probe 19 lines, diff lines 5
--- check:T2484_KerFacts
+++ probe:T2484_KerFacts
@@ -7,0 +8,2 @@
+      (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool,
+        STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t) ∧
== T2484_CltFlow: check 13 lines, probe 13 lines, diff lines 0
```
### Greps, diff stats, registry lines, name-clash (script `final_greps.sh`, run at 02:54:38 UTC)
```
$ wc -l RBM3D/Probe/T2484Pins.lean; git rev-parse --short HEAD; git status --short
     398 RBM3D/Probe/T2484Pins.lean
354ff913
$ grep -nE 'sorry|admit|native_decide|axiom' RBM3D/Probe/T2484Pins.lean   (rc below)
383:/-! ## Premise-scan preview (`RBM.Audit.scanPremises`, `Test/Axioms.lean`) and axioms -/
rc=0
$ grep -n '^import RBM3D.BA' RBM3D/Probe/T2484Pins.lean   (rc below)
rc=1
$ git diff --stat main...t/T2484
 RBM3D/Probe/T2484Pins.lean | 398 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 398 insertions(+)
$ git diff --stat 86eb22f2 main -- RBM3D RBM3D.lean   (main = 78f4cc14)
 RBM3D.lean                      |    4 +
 RBM3D/Chain/B45Gen.lean         | 1244 ++++++++++++++++++++++++++++++++++
 RBM3D/Chain/OptL2Gen.lean       | 1423 +++++++++++++++++++++++++++++++++++++++
 RBM3D/Chain/Step2CloseGen.lean  |  921 +++++++++++++++++++++++++
 RBM3D/Graph/BAMomentExpGen.lean | 1147 +++++++++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean          |   16 +-
 6 files changed, 4747 insertions(+), 8 deletions(-)
$ git show main:RBM3D/Test/Axioms.lean | grep -nE 'RBM.BA.STIniTermI(I)?gL,|def scanPremises' | cut -c1-70
211:   `RBM.BA.STIniTermIgL, -- the initial term of case (i) over a ca
212:   `RBM.BA.STIniTermIIgL, -- the initial terms of case (ii) over a
466:def scanPremises (env : Environment) (ignore : Name → Bool) (witne
$ name-clash: git grep -n -e IniTermGen_ -e iniTermGen_ -e STCltFarUConclgL -e bandFM_STCltFarUConcl -e stIngR5gL_hyps_restrict -e stCltFarUgL_of -e stIniTermIIgL_of -e stIniTermIgL_of -e iniTermIIGen_ -e iniTermIGen_ -e CltFarUGen_ <ref> -- RBM3D | wc -l; new-module files
main (78f4cc14): hits        0, module files 0
t/T2473 (de1b76b7): hits        0, module files 0
t/T2473b (ce109b72): hits        0, module files 0
t/T2478b (3166b5d9): hits        0, module files 0
t/T2480 (59c63b6d): hits        0, module files 0
t/T2480b (df3973e4): hits        0, module files 0
t/T2481 (a778b55f): hits        0, module files 0
t/T2482 (0ac2aab8): hits        0, module files 0
t/T2483 (77f7be5b): hits        0, module files 0
t/T2483b (5ed71f0a): hits        0, module files 0
```
The single hit of the first grep (`:383`) is the section comment "... and axioms", not a declaration; the names `probe_*` and `scratch_*` exist only in the probe and the scratch files.
### Scratch runs (not committed; files in the scratchpad `T2484/`: `op.lean`, `ba_e1.lean`, `d3.lean`)
```
Tue Oct 13 02:54:54 UTC 2026
$ lake env lean /Users/junyin/Lean_proof/RBM3D/docs/tickets/checks/T2484-check.lean | grep -c error
exit code: 0
0
$ lake env lean scratch/op.lean  (open private of the 43 names)
iniTermII_Kf : (d L : ℕ) → [NeZero L] → ℝ → ℝ → ℝ → ℝ → RBM.Zd d L → RBM.Zd d L → ℂ
exit code: 0
$ lake env lean scratch/ba_e1.lean
'scratch_E1_kron' depends on axioms: [propext, Classical.choice, Quot.sound]
BAMB_symm : ∀ (d L : ℕ) [inst : NeZero L] (g : ℝ) (z m : ℂ) (a b : Zd d L), BAMB d L g z m a b = BAMB d L g z m b a
$ LEAN_PATH=<main build lib, read-only> lean scratch/d3.lean
'scratch_ward' depends on axioms: [propext, Classical.choice, Quot.sound]
exit code: 0
Tue Oct 13 02:55:09 UTC 2026
```
`ba_e1.lean`: `theorem scratch_E1_kron (C : FlowFM sz) (n) (Bm) (hM : ∀ x y, C.M n x y = Bm (split ..x).1 (split ..y).1 * if (split ..x).2 = (split ..y).2 then 1 else 0) (hsym : ∀ a b, Bm a b = Bm b a) (σ σ' t) : STThg C n σ σ' t = STThg C n σ' σ t` (proof: `Step2Kern_Mss_of_kron` twice, `cases`, `simp`).
`d3.lean` (borrows `main`'s oleans through `LEAN_PATH`, read-only): `theorem scratch_ward (C) (hward : ZeroModeGen_WardCls sz C) (n) (hs0 : 0 ≤ s) (hs1 : s < 1) (hη : 0 < C.eta n s) (ω) (hσ : σ 0 ≠ σ 1) (b₁) : ‖∑ b₂, (C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂])‖ ≤ (2 * (W^d * C.eta n s))⁻¹ * (‖(L-K)^{(1)}_{+}‖ + ‖(L-K)^{(1)}_{-}‖)`, 26 lines (statement and proof), from `B45_ward_fing` (`m = 0`).
`op.lean`: `open private` of the 43 names of row (xi) from `RBM3D.Induction.IniTermII`.
### Probe line map
| lines | content |
|---|---|
| 24-25 | `open private` of `Step5KerGen_cmp_pos` (used at 259+), `Step5KerGen_tailT_cross` (accepted, unused), `iniTermII_sum_fin2` (used in `probe_UN_rep`), `iniTermII_Theta_shift` (used in the band discharge) |
| 33-51, 54-66 | `T2484_KerFacts` (check text plus E1 at 40-41), `T2484_CltFlow` (check text) |
| 71, 86-137 | `probe_flow_E`; band discharge `iniTermGen_kerFacts_band` (`A = 1`, `gK = sz.lam`, `κm = cltCk (min κ 2)`) |
| 141-166 | band discharge `iniTermGen_cltFlow_band` (`κ' = cltCk (min (κ/2) 2)`, `δ = ε/2`, `H₀ = 0`, `g' = sz.lam`, `E = STflowE z`) |
| 172-188 | D2 consumer `probe_cltFar_of_cltFlow`: class + `Step5CasesGen_FlowFacts` + restricted Step-2 premises at `t'` give `STCltFarConclgL .. s t'` through `stCltFargL_holds` |
| 194-211 | `Θ = 1 + tθ` (`probe_Theta_eq`), `1 + (u-s)θ = (s/u) 1 + ((u-s)/u) Θ` (`probe_Kmat`) |
| 214-252 | `𝒰 = K ⊗ K` (`probe_UN_rep`): `Step5KerGen_UN_decomp`, `Step2Gen_UN_self`, E1 once (`hE`, 244) |
| 259-281 | `Θ̊` bound at `lam` (`probe_zero_bound`): zero-mode field at `gK` and R1 (`Step5KerGen_cmp_pos`, `lam² ≤ A gK²`) |
| 283-291, 295-304 | `T2484_Core2` (shape of target 2, `σ₁ ≠ σ₂`), `probe_core2_band` (from `iniTermII_core` and `bandStep2_Ugen`) |
| 306-381 | instances at `szB`, `zB`: KerFacts, all five conjuncts (313), CltFlow window `(7/8, 15/16)` (336), far pin at `t' = 15/16` (353, the two Step-2 premises stay hypotheses), core at `n = 0`, `(s,u) = (15/16, 31/32)` with a tensor attaining the profile (363) |
| 383-396 | premise-scan preview and `collectAxioms` of the six public results |
### Fill-in table (H250 (4)), final
| # | deliverable | line / result |
|---|---|---|
| (i) | exponent table | (a) line 6; the probe adds no exponent (all constants are existential in the classes) |
| (ii) | instance + script | (a) line 24; Lean instances at `szB`, `zB`: probe 313, 336, 353, 363 (exit 0) |
| (iii) | hypothesis table | (a) line 71; band side compiled (probe 86, 141); BA names compile in the check (`lake env lean` exit 0, 0 errors, block above); E1's BA source: `BATheta_swap` (`BA/KBase.lean:350`, no hypothesis) and `scratch_E1_kron` with `BAMB_symm` (`BA/Ward.lean:83`) |
| (iv) | D1 decided; probe lines | E1 kept (4th conjunct, no guard), check text otherwise (diff +2 lines); probe 33-51, 86-137, 214-252, 259-281 |
| (v) | D2 | (a) line 72; closure under `t ↦ t'` compiled: probe 172-188, instance 353 |
| (vi) | D3 | changed since (a): `T2480` merged `78f4cc14` (state file `updated: Tue Oct 13 02:43:13 UTC 2026`); `B45_ward_fing` is on `main` (`Chain/B45Gen.lean:117`); `scratch_ward` compiles; 1b uses it (no inline copy, no conjugation), `hη : 0 < C.eta n s` from `Step5CasesGen_FlowFacts` (`eta n t = (1 - t) * Im m`, `κm ≤ Im m`, `t < 1`) |
| (vii) | reader table | (a) line 73; the probe compiles the reader `IniTermII:940` (`probe_UN_rep`) and the `hΘ` step of `IniTermII:1080-1090` (`probe_zero_bound`); `:332` is `step5KerGen_profile_holds` (merged) |
| (viii) | scope table | (a) line 74 (unchanged) |
| (ix) | UBA-C1 as used | R1 is produced at 86-137 (`A = 1`) and consumed only at 259-281 (guard `0 < lam`, `lam² ≤ A gK²`); `probe_UN_rep` and `probe_cltFar_of_cltFlow` read no R1 |
| (x) | premise scan, registry | scan output above: `[]` new premises with the band results as proofs; the two classes appear exactly when those two results are withheld; registry: owner text only at `Test/Axioms.lean:211-212` ("generic: `stIniTermIgL_of` / `stIniTermIIgL_of` (T2484); BA: U4-BA (b)"), no new line |
| (xi) | `open private`, copies | 43 names (below), all accepted (`op.lean`, exit 0); `Step5KerGen_cmp_pos`, `Step5KerGen_tailT_cross`, `iniTermII_sum_fin2`, `iniTermII_Theta_shift` opened in the probe, so no copy of them; regenerated under `IniTermIIGen_` (12 private + 4 public, below) |
| (xii) | lines per file | (a) line 78 unchanged: split U4s2a 699 / U4s2b 1,739 (cap 1,950), total 2,438 < 3,900 |
| (xiii) | name-clash | block above: 0 hits on `main` and nine sibling branches; no module file with the three new names |
`open private` (43, `IniTermII.lean:line`, prefix `iniTermII_` dropped): PD:66 PI:69 PD_nonneg:71 PI_nonneg:74 PI_pos:77 PI_le_one:80 PD_le_PI:84 PI_le_PD:90 zdistD_neg:107 zdistInf_neg:111 zdistInf_sub_comm:115 zdistD_sub_comm:119 PD_sub_comm:123 PI_sub_comm:127 zdistInf_add_le:131 zdistInf_le_L:141 zdistInf_zero:145 tri:150 sum_PD:161 sum_PI:169 conv_PD:179 tailT_le:261 tailT_ge:282 tailT_mono:297 sum_shift:460 S2:465 T_lower:530 S3:572 S3F:645 Kf:668 sum_fin2:898 Ts_le:1109 poly_exp_le:1184 sum_poly_exp:1200 bil_same:1231 Bctl_le:1430 lam_le:1452 rho_le:1470 N_le_W:1497 prem_eq:1505 prof_ge:1516 of_subset:1531 arith:1541.
Regenerated (statement mentions `Theta`/band objects; same script): stageA:327 ZA:369 Kf_norm_le:671 Kf_sub:681 Kf_sub_norm_le:690 bil:712 Ugen_rep:907 zms_rep:963 cyc_mixed:1022 Theta_shift:1037 lift:1567 im_ge:1650, and the public `core`:1051, `core_same`:1378, `concl`:1664, `holds`:1718. (`Theta_shift` is reachable by `open private` and is used at the band discharge, probe line 25.)
### Findings
1. **E1 compiles and is used.** `probe_UN_rep` needs it exactly where slot 1 carries `(σ₁,σ₀)`; the band class holds with it (`mul_comm`); BA source and generic reduction compile (`scratch_E1_kron`). Every BA name of (a) line 71 exists (the check compiles); the BA constants `(g₀, E_f, m₀)` and the shapes of `baProp8_holds`, `baProp5s_holds` stay with U4-BA (a) and were not compiled here.
2. **Class texts.** `T2484_CltFlow` equals the check (0 diff lines); `T2484_KerFacts` is the check plus the 2 E1 lines. The classes quantify over every `κ > 0`, while `cltCk κ > 0` needs `κ < 4`: the band discharges use `cltCk (min κ 2)` and `cltCk (min (κ/2) 2)` (proof level, no change of statement). `T2484_KerFacts` needs no `0 < ε` (probe 71 gives `|E| ≤ 2 - κ` from `locDomain`).
3. **D2 closes.** `HCltOf` at every `t' ∈ (s, t]` is assembled from the `t`-free fields of the class (applied at `(s, t')`), `FlowFacts` (admissible, `T0 < 1`) and `STReg5I`, `STLocalEntryUgL`, `STGdecayWgL` restricted to `[s, t']`; the far pin follows (probe 172-188, instance 353). `STMfarg`, `STGijDecgL`, `STKfargL`, `STKpropsg` depend on `s` only.
4. **Core.** The generic case-(ii) core is **not** proved in the probe: `T2484_Core2` (283) is a shape and its instance (363) is the band theorem `iniTermII_core` transported through `bandStep2_Ugen`. Compiled generically: `Θ = 1 + tθ`, `𝒰 = K ⊗ K`, the `Θ̊` bound with R1. Left to 1b: the bilinear estimates on a generic `Θ` (`bil` 177 lines, `bil_same`), `zms_rep` with the column-sum field, `lift`, and the short-range bound (its R1 clause is `gK² ≤ lam²`, not compiled).
5. **D3** as in row (vi): `B45_ward_fing` exists on `main`; the ticket's alternative (inline copy) is not needed.
6. **Base.** The probe was compiled on the worktree base 86eb22f2, not on 78f4cc14; the diff stat above lists what `main` added since; none of it is imported by the probe except `Test/Axioms.lean` (registry text; `scanPremises` at `:466` unchanged).
7. Paper-delta candidates: `T2484a` (ticket), `T2484b` (E1: `Θ^{(+-)} = Θ^{(-+)}` as carrier datum) as in (a); no new one.
### Probe verdict
Probe compiles (exit 0, no `sorry`, standard three axioms); (a″) written; the fill-in table above is complete (13 of 13 rows). No stop rule of the ticket fires. Open for the 1a-audit: the E1 text of target 1, the shape `T2484_Core2`, and row (vi) (`B45_ward_fing` now on `main`).
(a″) finalized: Tue Oct 13 02:57:26 UTC 2026 (probe commit 354ff913 unchanged since the compile above).

## (b) Script output — Tue Oct 13 03:34 UTC 2026 (stage 1b, U4s2a: targets 1-4 and their part of 10-11; branch `t/T2484` HEAD 8162591d; scripts `final.sh`, `stmts.py`, `inst.py`, `diff_t1.py`, `final_chk.lean` in the scratchpad `T2484/`)
```
$ lake build RBM3D.Chain.IniTermIIGen | tail -1   ->  Build completed successfully (3790 jobs).
$ lake build (whole library, RBM3D.lean with `import RBM3D.Chain.IniTermIIGen` added for the run only; 03:32:05 -> 03:33:07 UTC)  ->  axiom audit: 14339 theorems, 4516 definitions, 0 axioms in `RBM`; premises found by scanning: 125; Build completed successfully (4333 jobs).
$ lake env lean final_chk.lean  (exit code 0, 0 error lines): #print axioms of IniTermGen_KerFacts, iniTermGen_kerFacts_band, iniTermIIGen_core, iniTermIIGen_core_same, iniTermIIGen_concl, stIniTermIIgL_of, iniTermIIGen_band_holds, IniTermIIGen_Theta_eq, _UN_rep, _row_le, _cmp_pos'  ->  all [propext, Classical.choice, Quot.sound]
$ wc -l at each section commit (stop rule 2,000): fed8e82f 851 | 0df3a4e2 1006 | f64ce7a0 1116 | 9849adf7 1116 | 8162591d 1113 (`Chain/IniTermIIGen.lean`; 1a central 699, 2.6x reference 1,818)
$ python3 stmts.py   (target statements extracted from the file, whitespace collapsed; [line] declaration up to `:= by`)
[68] def IniTermGen_KerFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop := 3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → (∀ n : ℕ, Step2Gen_USemigroup (mk sz z) n) ∧ Step5KerGen_ThDecay (mk sz z) (gK sz z) 𝔡⁻¹ C₆ ∧ (∀ n : ℕ, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK sz z n ^ 2) ∧ (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool, STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t) ∧ ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ t : ℝ, 0 ≤ t → t < 1 → (∀ (σ : Bool) (b : Zd d (sz.L n)), ∑ a : Zd d (sz.L n), STThg (mk sz z) n σ (!σ) t a b = (((1 - t : ℝ) : ℂ))⁻¹) ∧ (∀ (σ : Bool) (a b : Zd d (sz.L n)), ‖STThg (mk sz z) n σ (!σ) t a b - (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (((1 - t : ℝ) : ℂ))⁻¹‖ ≤ C₈ * (gK sz z n ^ 2 + |1 - t|)⁻¹ * ((((zdistD d (sz.L n) (b - a) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) ∧ ∀ (σ : Bool) (a b : Zd d (sz.L n)), ‖STThg (mk sz z) n σ σ t a b‖ ≤ Cs * ((if a = b then (1 : ℝ) else 0) + gK sz z n ^ 2 * Real.exp (-(c₀ * ((zdistD d (sz.L n) (b - a) : ℕ) : ℝ))))
[107] theorem iniTermGen_kerFacts_band (d : ℕ) : IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam)
[746] theorem iniTermIIGen_core (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + W ^ (-D))) → ∀ a, ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN (mk sz z) n σ s u X) a‖ ≤ C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + (1 - s) / (1 - u) * W ^ (-D))
[800] theorem iniTermIIGen_core_same (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) : ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 → 1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam → ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + W ^ (-D))) → ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤ C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + W ^ (-D))
[942] theorem iniTermIIGen_concl (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hF : Step5CasesGen_FlowFacts d Flow mk T0) (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ} (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ T0 sz z n) (hR : STReg5II sz s t) (hDec : STDecaygL (mk sz z) (law sz) s) : STIniTermConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧ STIniTermConclgL (mk sz z) (law sz) ∅ STSigSame s t
[991] theorem stIniTermIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK → STIniTermIIgL d law Flow mk T0
[1006] theorem iniTermIIGen_band_holds (d : ℕ) : STIniTermII d
$ python3 diff_t1.py
== target 1 vs the 1a-audit text (probe lines 33-51, `def T2484_KerFacts`): 19 vs 19 lines, diff lines: 0
== target 1 vs the check's text: 17 vs 19 lines, the diff is the two E1 lines `(∀ n t, 0 ≤ t → t < 1 → ∀ σ, STThg .. σ (!σ) t = STThg .. (!σ) σ t) ∧`
== target 4 vs `T2484_IniTermIIOf` (KerFacts renamed): hypotheses and conclusion equal: True
$ lake env lean final_chk.lean : `example : T2484_IniTermIIOf' := stIniTermIIgL_of` (the check's text, KerFacts -> IniTermGen_KerFacts) and `example .. : T2484_Core2' d Flow mk gK := fun hKF hd κ 𝔡 hκ h𝔡 => iniTermIIGen_core ..` (the probe's shape of target 2, σ₁ ≠ σ₂) compile
$ python3 inst.py   (compiled nonempty instances, d = 3, data szB, zB, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; first 260 characters; the Step-5 premise `STDecaygL` at `s` of [1084] stays a hypothesis, another gate's pin)
[1017] example : ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧ (∀ n, Step2Gen_USemigroup (bandFM szB (STflowE zB)) n) ∧ Step5KerGen_ThDecay (bandFM szB (STflowE zB)) szB.lam (1 / 10 : ℝ)⁻¹ C₆ ∧ (∀ n, 0 ≤ szB.lam n * szB.lam n ∧ szB.lam n ^ 2 ≤ szB. …
[1043] example : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 (szB.L 0), ‖zeroModeSet 3 (szB.L 0) {0} (Step2Gen_UN (bandFM szB (STflowE zB)) 0 ![true, false] (15 / 16) (31 / 32) (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L …
[1063] example : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 (szB.L 0), ‖Step2Gen_UN (bandFM szB (STflowE zB)) 0 ![true, true] (15 / 16) (31 / 32) (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L 0) (b 0 - b 1) : ℕ) + (2 : ℝ) …
[1084] example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) : STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) {0} STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32) ∧ STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP …
[1095] example (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd
[1104] example (Cd : ℝ) (hCd : 0 < Cd) : InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd
$ git grep -n -e IniTermGen_KerFacts -e iniTermGen_kerFacts_band -e iniTermIIGen_ -e stIniTermIIgL_of -e IniTermIIGen_ <ref> -- RBM3D | wc -l   on main (5a060d90) and t/T2470, 2471, 2471b, 2472, 2472b, 2473, 2473b, 2474-2477, 2478, 2478b, 2479, 2479b, 2480, 2480b, 2481, 2482, 2483, 2483b, 2485: 0 hits, no `IniTermIIGen` file, on all 23 refs (final.out)
$ git diff --stat main...t/T2484  ->  Chain/IniTermIIGen.lean 1113, Probe/T2484Pins.lean 398 (never merged), Test/Axioms.lean 2 (1 line changed: the owner text of STIniTermIIgL); `git merge-tree --write-tree main t/T2484`: no conflict
$ G1: git diff main...t/T2484 -- RBM3D/Induction RBM3D/Evolution RBM3D/BA and the merged Chain files | wc -l  ->  0;  grep -n '^import RBM3D.BA' RBM3D/Chain/IniTerm*Gen*.lean | wc -l  ->  0
$ U-C4 `grep -nE '^(noncomputable )?def'`: one hit, `68:def IniTermGen_KerFacts` (Prop-valued; no matrix- or tensor-valued def).  TN-C4 `STGridRepNgL|ST_gridMart_of_repN`: 0.  X1-C4 (the 13 pin names after def/abbrev/structure): 0.  UBA-C1 `withLam`: 0.  `sorry|admit|native_decide|^axiom`: 0
$ X1-C1 grep, hit lines 40 88-153 187 1005-1008 1018-1084: 40, 187 are docstring port citations (`Ugen_rep`, `iniTermII_Ugen_rep`); 88-153 are the band helpers `IniTermIIGen_flow_E/_mixed/_ck_pos` and the band discharge `iniTermGen_kerFacts_band`; 1005-1008 the band re-derivation `iniTermIIGen_band_holds`; 1018-1084 the instances; no hit in a generic statement or proof
$ R1 (UBA-C1) is used in: stageA 264-267 (`step5KerGen_profile_holds` + guard), cross_inv 726-729 (Θ̊ bound), core 764-779, core_same 816-834 (`gK² ≤ lam²`, `lam ≤ A𝔡⁻¹`), guard (g) `IniTermIIGen_cmp_pos'` 930, used 962 (`0 < lam → 0 < gK`); nowhere else, no second comparison form
```
**Narrative.**
- Delivered: U4s2a = `Chain/IniTermIIGen.lean` (targets 1-4, the band parts of 10); U4s2b (targets 5-9: `CltFarUGen`, `IniTermIGen`) is not started. Section (a) and (a″) read; no correction found, so no (a′).
- Ports (project RBM3D, `Induction/IniTermII.lean`, last commit 69b10990; no RBM1D/RBM2D port, so no diff-stat): regenerated on the carrier `stageA` (`:327`), `ZA` (`:369`), `Kf` (`:668-704`, as two inline lemmas, no `def`), `bil` (`:712`), `Ugen_rep` (`:907`, now `IniTermIIGen_UN_rep`), `zms_rep` (`:963`), `core` (`:1051`), `core_same` (`:1378`), `lift` (`:1567`), `concl` (`:1664`), `holds` (`:1718`, now `iniTermIIGen_band_holds`); reused by `open private`: 22 names of IniTermII (+ `Step5KerGen_cmp_pos`), no copy. Imports: Step5CasesGen, Step5KerGen, CltGen, `Induction.IniTermII`, `Evolution.CltResolvent` (the ticket names `Induction/IniTermI`; it is not needed here).
- D1 as used: USemigroup -> `Theta_eq`, `UN_rep`; ThDecay at `gK` -> `stageA` (profile, `Cp+1`), `row_le`; R1 -> `stageA`, `cross_inv`, `core_same`; E1 -> `hpair` of `UN_rep` for σ₁ ≠ σ₂ (for σ₁ = σ₂ the two slot pairs coincide: no E1); column sum -> `zms_rep`; zero mode -> `cross_inv` -> `bil`; short range -> `core_same` -> `bil_same`. D2, D3 are target 5-9 and untouched.
- Differences from the band proof (not statement differences): `Θ = 1 + tθ` gives row sums `(1+C₆)/(1-t)` instead of `(1-t)⁻¹`, so `ZA`/`bil` carry `CR = 1 + C₆`; the Θ̊ bound is `C₈ A (lam²)⁻¹`; for σ₁ = σ₂, `lam ≤ A𝔡⁻¹` is derived from R1 and `bil_same` is applied at `Λ' = A𝔡⁻¹`; `cyc_mixed` and `im_ge` are not needed (E1; the margin lives in the class).
- Reader table (`IniTermII`): `:332` profile <- `step5KerGen_profile_holds` (via `stageA`); `:940` `𝒰 = K ⊗ K` <- `Step5KerGen_UN_decomp` (via `UN_rep`); the `IniTermI` readers (`:306, 487, 2139, 2201`) belong to U4s2b.
- Public under the file stem for U4s2b: `IniTermIIGen_Theta_eq` (M1), `_row_le` (takes the raw row-sum bound; a hypothesis `Step5KerGen_ThDecay` would be a new premise for the scan), `_UN_rep`, `_cmp_pos'`.
- Registry: `Test/Axioms.lean:212` owner text only; line 211 (`STIniTermIgL`) is left to U4s2b, whose `stIniTermIgL_of` it names. After this file `STIniTermIIgL` is concluded by `stIniTermIIgL_of`; the full build lists it under "registered premises that carry nothing yet"; no new registry line (125 premises found, no unregistered one).
- `RBM3D.lean` is unchanged on the branch (the hub adds the import at merge, §3 (A) step 4); the branch base is 86eb22f2, `main` is 5a060d90 at 03:34 UTC.

## (c) Verified Mathlib names (by compile in this tree)
`Finset.sum_ite_eq`, `Finset.sum_comm`, `Real.rpow_neg_one`, `inv_inv`, `le_div_self` (0 ≤ a, 0 < b, b ≤ 1), `one_le_inv₀`, `inv_anti₀`, `div_le_iff₀`, `div_le_one`, `one_le_div`, `mul_le_of_le_one_left`, `le_mul_of_one_le_left`, `Real.norm_of_nonneg`, `Complex.norm_real`, `Complex.norm_natCast`, `norm_inv`, `norm_pow`, `max_le`, `le_max_of_le_right`, `not_le`. Observed: `add_le_add_left h a : b + a ≤ c + a` in this Mathlib; `push_neg` is deprecated (`push Not`). Names verified absent: none looked for.

## (d) Open issues and paper-delta candidates
- `T2484a` (ticket, as in (a)): the initial terms over the carrier, with zero mode, short range and column sum of the propagator as carrier data at `gK`; `T2329b` carries over. `T2484b` (as in (a)): `Θ^{(σ,!σ)} = Θ^{(!σ,σ)}` (E1) as a carrier datum. No new candidate.
- The BA discharge of `IniTermGen_KerFacts` (E1 included) stays with U4-BA (a); here only the band is compiled (the 1a-audit compiled the BA source of E1).
- U4s2b imports `Chain/IniTermIIGen` (`IniTermGen_KerFacts`, `iniTermGen_kerFacts_band`, the four public helpers) and needs a base that contains `Chain/B45Gen` (merged in 78f4cc14) for `B45_ward_fing` (1a-audit observation 1).
