Prover model: claude-sonnet-5-5
## (a) Math preflight — Mon Oct 12 17:45:37 UTC 2026
Scratch `S=/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/000e860b-4f24-47be-83fa-df6f7c59f990/scratchpad/T2466`. Engines read only: T2450 `fold14.py`, T2433 `ba.py`, `tree.py`, `attach.py`, `l4s3/roots.py` (`T2464-prove.md` is not written yet, so no T2464 1a (v) census). Notation: `N=(WL)^d`, `B=Bctl`, `k=|E'⊕I'|=2+n_int`, `ord=n_S+2(n_W-n_A)`; the BA slot `n_V` holds `n_A`; every `K` below depends on `(d,Λ=𝔡⁻¹,κ,P)` only.
### (i) Exponent table (values at `sz0`, `n=0`, `t=1/2`, from `inst.py` in (ii); "ev." = eventually in `n`)
| # | quantity | value / formula | constraint | slack |
|---|---|---|---|---|
| 1 | `𝔠` | 1/6 | `W ≥ N^𝔠` | 32 ≥ 11.314 (2.83×) |
| 2 | `𝔡`, `λ` | 1/10, `λ=1/64` | `W^{-d/2+𝔡} ≤ λ ≤ 𝔡⁻¹` (WO); `λ²W^d ≥ W^{2𝔡}` | 2.00×, 640×; 8 ≥ 2 |
| 3 | `ε`, `κ` | 1/10, 1/2 | `N^{-1+ε} ≤ Im z ≤ 1`; `Im m_F ≥ κ` | 2.0e-6 ≤ 0.3675 ≤ 1; 0.9995 ≥ 0.5 |
| 4 | `t`, `T₀=t0` | 1/2, 0.69374 | `t ≤ T₀`; `1-t ≥ Im z/2` | 0.1937; 0.5 ≥ 0.184 |
| 5 | `c₀`, `ε₁` | `c₀=min(2𝔠𝔡,ε)/2=1/60`, `ε₁=d c₀/4=1/80` | `B ≤ (λ²W^d)⁻¹+(N(1-t))⁻¹ ≤ N^{-2𝔠𝔡}+2N^{-ε} ≤ 3N^{-2c₀} ≤ 2N^{-c₀}` ev. (`N^{c₀} ≥ 3/2`); `W^{dc₀/2} ≤ N^{c₀/2}` | `B=6.20e-5 ≤ 2N^{-c₀}=1.569` |
| 6 | `B ≤ 1`, floor | ev. from row 5 (`N^{c₀} ≥ 2`); `N⁻¹ ≤ B` | `B ≤ 1` (no BA `st5_Bctl_le_one`: only `B ≤ 2`, `BAExp14a_eventual_scalars`) | `N⁻¹=4.8e-7 ≤ B=6.2e-5 ≤ 1` |
| 7 | `η` | `η=(1-t)Im m_F`, `‖m_F‖ ≤ 1` (`BAAuxGraph2:655-658` proves `(1-t)Im m_F ≤ 1`) | `η ≤ 1`; `η⁻¹ ≤ N²` | 0.49975 ≤ 1; 2.001 ≤ 4.4e12 |
| 8 | window | `A=𝔡⁻²+1=101`, `Ψ=N^{τ'}√B` | `W^{-d} ≤ (λ²+1)B ≤ A B ≤ AΨ²` (`BAExp14a_Wd_le`, `N^{τ'} ≥ 1`) | 3.05e-5 ≤ 6.20e-5 (2.03×) |
| 9 | `ord` | 3..8 on the 4448 leaves (census) | `ord ≥ 0` (`BAG5Tgt`: `ord ≥ 5-2·1[x~y] ≥ 3`; target 3 also gives it via `auxOrd_le_scalingOrder`) | min 3 |
| 10 | `τ'` | `min(1,τ/(2T))`, `T=ord+2d+4 ≤ 18` | `τ'(ord+2d+3) ≤ τ/2` | `τ/(2T) ≥ τ/36` |
| 11 | `S2` (×`W^d`) | `cc²[2(2ρ+1)^{2d}η⁻¹(1+Ψ)+(2ρ+1)^d+N W^{-D₁}]`, `cc=N^{τ'}`, `A=Ψ` in `baZeta_ward_sum` | `≤ 4cc²(2ρ+1)^{2d}(1+Ψ)η⁻¹` (needs `(2ρ+1)^d ≤ X`, `N W^{-D₁} ≤ 1 ≤ X`); prefactor 4 (band `lwExpTerm3_Q_le` has 3), so `hK1N` reads `8·4^dK₁ ≤ N^{τ/2}` | closes: `4·N^{2τ'}·4^dN^{2dτ'}·2N^{τ'}`=`8·4^d N^{τ'(2d+3)}` |
| 12 | `D₁` | `2/𝔠=12` | `W^{D₁} ≥ N²`, so `N W^{-D₁} ≤ N⁻¹` | 1.15e18 ≥ 4.4e12 (2.6e5×); 1.8e-12 ≤ 4.8e-7 |
| 13 | `r,R,ρ` | `r=(log W)^{3/2}`, `R=k r`, `ρ=2R+r` | `ρ-2R=r ≥ K log W` ∀K ev. (BAGbyZeta `hsep`); `ρ+1=(2k+1)r+1 ≤ N^{τ'}` ev. (`lwXiRad_holds`, `C=2k+1`, `K=3/2`) | at `sz0` `k=6`: `2ρ+1=168.75`, `(2ρ+1)^{2d}=2.3e13`: asymptotic only |
| 14 | tail | `(C,c)` of G3; `m=n_M+n_S+n_A` | `e^{-c r/2} ≤ N^{-(D+m+1)}`: `lwTail_log32` at `D'=(D+m+1)/𝔠`, `W ≥ ⌈exp((2D'/c)²)⌉+2`, `W ≥ N^𝔠` | threshold in `W` only |
| 15 | envelope | target 3 at `Ψ=N²+1`, `ξ≡Ψ` (`cc=Ψ`, `S2=L^d`), `r=R=0` | `‖X‖ ≤ N^{K_env}`, `K_env=1+max(2ord+5, 2n_S+n_M+max(n_A-n_W,0))`; floor `N^{-K_f}`, `K_f=ord/2` | max `K_env=22` (ord 8), `K_f ≤ 4` |
| 16 | kernels of `D'_t` | `S'`: entries `W^{-d}`, rows 1, `lwBdist=0` on its support; `lift(ω_t)`: entries `≤ W^{-d}C_s(1+Λ²)`, rows/cols `≤ S`, decay `(C_s,c_s)` | `(C_s,c_s)` (`baProp5s_holds`, `FlowPins:184-191`) and `S` (`BAExp14a_theta_l1`) are `t`-uniform on `[0,1)`, existential: no numeric compare; `K₀ ≥ max(1,C_s(1+Λ²))`, `K₁ ≥ max(1,S)` | t-grid below: `W^d`·max entry ≤ 1, rows ≤ 1 |
| 17 | `hext` | not used | `BAAtom2:416,419,628,635` only; body 0 uses | see (ii) a |
### (ii) Concrete instance and checks (`d=3`, `W=32`, `L=4`, `N=2097152`, `zSeq`, `t=1/2`, `𝔡=1/10`, `κ=1/2`, `ε=1/10`, `𝔠=1/6`)
**a. `hext` audit and S5** — `bash $S/audit.sh`:
```
-- grep -n hext RBM3D/Graph/BAAtom2.lean | cut -c1-72
416:every circled solid edge, and the weighted kernels `S`, `S⁺`, `M`, `
419:  intro hd L W _ _ E I _ _ _ _ Γ hN hext D Ψ A K₀ K₁ Kd C c r R ξ hG
628:    fun L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 E' I' _ _ _ _ Γ hN hex
635:  exact baGtoAG_holds d hd L W Γ hN hext D Ψ A K₀ K₁ Kd C c r R ξ hG
-- 'hext' occurrences in the proof body BAAtom2:420-598: 0
-- project lemmas named in that body: 13 of 13 listed (BAAtom_fJ BAAtom_fJw BAAtom_fJw_nonneg BAAtom_nonneg_fJ BAAtom_main_sum BAAtom_tail_sum BAAtom_term_tail BAAtom_term_conf baClaimSize_E auxVal_nonneg scalingOrder_sub_auxOrd counters_le molSolid_length_le); private among them: 0
-- S5: diff T2465_Q1Need vs T2466_BAG5LeafPrec1 (names normalised, 11 lines each): exit 0
```
**b. Leaf census, `n_M=1` `BAG5LeafProps` leaves** (`cd $S; python3 census_sum.py`; engine: closure with fuel 2, all `BACtx` choices, both charges; the instance leaf from `python3 census.py | grep -A1 '^rep 1ext'`):
```
root      s   n_M=0  n_M=1 (1 ext mol / 2 ext mol)
MERGED    1   1487   1161 (53 / 1108)
MERGED    0   1427   1063 (53 / 1010)
T3C-tr_1  1   1378   1161 (53 / 1108)
T3C-tr_1  0   1318   1063 (53 / 1010)
D2X       1    109      0 (0 / 0)
D2X       0    109      0 (0 / 0)
class                          count  n_W    ord    |E+I|   min attach  #attach=4  n_M  #S+ edges
1 ext mol  x~y (tied)              212  2..5  3..5   6..12   2..2          0        1   0..2
2 ext mols x!~y                   4236  2..7  5..8   6..16   2..4       1052        1   0..3
total n_M=1 leaves: 4448 ; min ord 3 ; ord>=3 for tied, >=5 for untied: True
rep 1ext ('1ext', 'tied', 2, 3, 4, 2)
    G(n=4, solid=((True, True, ('e', 0), ('i', 0)), (True, True, ('i', 2), ('e', 1)), (True, True, ('i', 1), ('i', 3))), waved=((False, True, ('i', 1), ('i', 2)), (False, True, ('i', 0), ('i', 3))), mdot=((True, ('i', 3), ('i', 2)), (True, ('e', 1), ('e', 0)), (True, ('i', 0), ('i', 1))))
```
`leaf1` of target 7 = this 1-external-molecule leaf (`n_int=4`, `n_W=2`, `ord=3`, tied, 2 attachments, no `S⁺` edge): it needs the `hext` removal (of the 4448 leaf occurrences in the six lists, 212 have `x~y` in one molecule, the other 4236 have two molecules).
**c. `t`-scaling `val(BAlwData_t)=t^{n_W}val(D'_t)`** — `cd $S; python3 scale_run.py A; python3 scale_run.py B` (models A, B of T2433/T2434 `mc_cut.py`: `S'=1[block]/W^d`, `S⁺'=lift((1-tQ)⁻¹)`, `Q_ab=M_abM_ba`; the model's own `S=tS'`, `S⁺=S(1-M⁺S)⁻¹`; grid `t∈{0,1e-3,.1,.5,.9}`; the toy models have no `T₀`, so `0.9 < 1` stands in):
```
leaves: 1ext, 1 S+ edge, n=6 nW=3: nM=1 ord=3 ; 2ext, 2 S+ edges, n=8 nW=4: nM=1 ord=5 ; 2ext, 3 S+ edges, n=10 nW=5: nM=1 ord=5
  A | 1ext, 1 S+ edge, n=6 nW=3   | max rel err over t in {0,1e-3,.1,.5,.9}: 8.1e-16 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 3.3e-01, t^(nW-1) 5.0e-01
  A | 2ext, 2 S+ edges, n=8 nW=4  | max rel err over t in {0,1e-3,.1,.5,.9}: 1.3e-15 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 6.2e-01, t^(nW-1) 5.0e-01
  A | 2ext, 3 S+ edges, n=10 nW=5 | max rel err over t in {0,1e-3,.1,.5,.9}: 9.7e-16 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 8.2e-01, t^(nW-1) 5.0e-01
  B | 1ext, 1 S+ edge, n=6 nW=3   | max rel err over t in {0,1e-3,.1,.5,.9}: 1.8e-15 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 2.2e-01, t^(nW-1) 5.0e-01
  B | 2ext, 2 S+ edges, n=8 nW=4  | max rel err over t in {0,1e-3,.1,.5,.9}: 3.7e-15 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 4.0e-01, t^(nW-1) 5.0e-01
  B | 2ext, 3 S+ edges, n=10 nW=5 | max rel err over t in {0,1e-3,.1,.5,.9}: 3.2e-15 | |val|(t=0): 0e+00 | NEG(t=1/2): omega without t 5.4e-01, t^(nW-1) 5.0e-01
```
**d. `lift(ω_t)` at the `d=3`, `L=4` block model of the instance** (`python3 $S/kern.py`; `ω_t=(1-tQ)⁻¹`, decay column = fitted rate over distances 1..3):
```
instance: t0=0.693740 g0=0.013014 E=0.00e+00 Im m=0.999493 (>= kappa=1/2: True)  max_a sum_b |MB_ab|^2 = 1.000000000000
t        Wd*max entry  row l1   col l1   1/(1-t)  decay-rate fit (-slope of log|omega(0,a)| vs dist, offdiag)  max|omega_aa-1|
0.00000     1.0000    1.0000   1.0000   1.0000         n/a   0.000e+00
0.00100     0.9990    0.9990   0.9990   1.0010       6.895   9.980e-04
0.10000     0.9092    0.9093   0.9093   1.1111       6.925   9.083e-02
0.50000     0.6669    0.6671   0.6671   2.0000       7.009   3.331e-01
0.69374     0.5907    0.5909   0.5909   3.2652       7.035   4.093e-01
stress rows (Wd*max entry, row l1; col l1 equal, omega symmetric), t up to 0.999:
 g0=0.10 E=0.30 Im m=0.9617 (>= kappa: True): t=0.000 max=1.000 row=1.000 | t=0.500 max=0.686 row=0.698 | t=0.999 max=0.520 row=0.534
 g0=0.25 E=0.20 Im m=0.8639 (>= kappa: True): t=0.000 max=1.000 row=1.000 | t=0.500 max=0.729 row=0.790 | t=0.999 max=0.574 row=0.646
 g0=0.35 E=0.10 Im m=0.7891 (>= kappa: True): t=0.000 max=1.000 row=1.000 | t=0.500 max=0.763 row=0.860 | t=0.999 max=0.618 row=0.736
```
**e. Constants of the table rows (`R<n>` = row `n`) and the envelope** — `python3 $S/inst.py; python3 $S/env.py`:
```
N=2097152 W^d=32768 L^d=64 | t0=0.693740 > t=1/2 (slack 0.1937) | g0=0.013014 <= Lambda=1/dd=10 | E=0.0e+00 | Im m_F=0.999493 >= kappa (slack 0.4995), |m_F|=0.999493 <= 1
(self_m) residual 1.1e-16 ; Ward max_a|sum_b|MB_ab|^2-1| = 1.1e-15 ; max|MB_ab| = 0.9995
R1-2: W=32 >= N^c = 11.314 (slack 2.83x) ; lam=1/64=0.01562 in [W^(-d/2+dd)=0.00781, 1/dd=10] (slack 2.00x, 640x) ; lam^2 W^d=8.000 >= W^(2dd)=2.000
R3-4: N^(-1+eps)=2.044e-06 <= Im z=0.3675 <= 1 ; 1-t=0.500 >= Im z/2=0.1838
R5-6: B=Bctl(0,1/2)=6.1959e-05 ; N^-1=4.77e-07 <= B (floor) ; B<=(lam^2 W^d)^-1+(N(1-t))^-1 = 0.125001 ; B <= 2N^-c0 = 1.5692 (c0=min(2cd,eps)/2=0.01667, eps1=d c0/4=0.01250) ; B<=1: True ; B<=2: True
R7-8: eta=(1-t) Im m_F=0.49975 <= 1 ; eta^-1=2.0010 <= N^2=4.398e+12 ; Psi_env=N^2+1=4.3980e+12 ; window W^-d=3.052e-05 <= (lam^2+1)B=6.197e-05 (slack 2.03x) <= A B, A=dd^-2+1=101
R13 leaf1 (1ext, n=4): |E+I|=6 r=(log W)^(3/2)=6.4520 R=38.712 rho=2R+r=83.876 ; rho-2R=6.452 >= K log W=3.466 iff K <= 1.862 (eventually all K) ; 2rho+1=168.75 ; (2rho+1)^(2d)=2.309e+13
R13 max (n=14): |E+I|=16 r=(log W)^(3/2)=6.4520 R=103.232 rho=2R+r=212.915 ; rho-2R=6.452 >= K log W=3.466 iff K <= 1.862 (eventually all K) ; 2rho+1=426.83 ; (2rho+1)^(2d)=6.047e+15
R12: D1=2/c=12: W^D1=1.153e+18 >= N^2=4.398e+12 (slack 2.6e+05) ; W^d * L^d W^-D1 = N W^-D1 = 1.819e-12 <= N^-1 = 4.768e-07 <= 1
R10 (tau=1): ord=3: T=13 tau'=0.03846 tau'(ord+2d+3)=0.4615<=0.5 N^tau'=1.750 ; ord=5: T=15 tau'=0.03333 tau'(ord+2d+3)=0.4667<=0.5 N^tau'=1.625 ; ord=8: T=18 tau'=0.02778 tau'(ord+2d+3)=0.4722<=0.5 N^tau'=1.498
R16 kernels at t=1/2: S' entries = W^-d, rows = 1 (K0>=1, K1>=1) ; lift(omega_t): Wd*max entry=0.6669, row l1=0.6671, col l1=0.6671 (K0>=0.667, K1>=0.667) ; M: max entry 0.9995, row l1 (fine) = 1.0828, col = 1.0828 ; gPsi: entry g0=0.01301 row=2d g0=0.07809
R15/target 2 (deterministic Psi): sup_x |G_xy| <= eta^-1 = 2.0010 ; ||G-M|| <= Psi := eta^-1 + 1 = 3.0010 (deterministic) ; window W^-d=3.052e-05 <= A Psi^2 = 909.615
leaves 4448 distinct (ord,nS,nA,nW,2o+5,2nS+nM+max(nA-nW,0)): 43
max Kenv = 1 + max(2*ord+5, 2*nS+nM+max(nA-nW,0)) = 22  at (ord,nS,nA,nW,term1 exp,term2 exp) = (8, 4, 2, 4, 21, 9)
ord range over leaves: min 3 max 8 ; nW range: 2..7 ; nS range 2..7 ; |E+I| = 2+n range 6..16
Floor exponent Kf = |ord|/2 max = 4.0 ; T = |ord|+2d+4 at d=3: max 18 ; tau' = min(1,tau/(2T)) at tau=1: 0.02778
```
Hypotheses of the 1b targets at this data: target 1 at `0≤t=1/2<1`, `3≤L`, `BAReal` (`Im m_F=0.9995≥κ`, `(self_m)` residual 1.1e-16); target 2 at `d=3`, `Λ=10`, `κ=1/2`, `0<g0=0.013014≤Λ`, `Ψ=η⁻¹+1=3.001` (deterministic, `‖G‖≤η⁻¹`, `‖M‖≤1`), `ξ≡Ψ`, `r=R=0`, window and kernels as in rows 8, 16; target 4 at `flow_sz0` (`BAFlow` holds by `flow_sz0`, `half_lt_t0`); target 6 at `leaf1` with `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL`, `STLKgL`, `STDecaygL` kept as hypotheses (Step 1/2 pins of other gates; their limit computation is T2450's `instance.py`, 1a (ii)). The `≺` conclusions are asymptotic: the polylog factors of row 13 exceed `N^{τ'}` at `n=0` (no finite witness exists or is claimed).
### Verdict (stop rules S1-S5 do not occur)
- Target 1 (`dataT`, `val_scale`): PASS. S2 does not occur: identity holds to 4e-15 at both models, the negative controls fail (0.2-0.8), `lift(ω_t)` is `t`-uniform (rows ≤ 1 up to `t=0.999`).
- Target 2 (`BAGtoAGT`): PASS. S1 does not occur: `hext` is introduced at `BAAtom2:419` and never used in `:420-598`; all 13 named lemmas are public.
- Target 3 (`BAExp14d_det`, private): PASS. Needs only the private `lwExpTerm3_auxVal_zero/one` (`open private`, precedent `BAS3CloseC:41-50`), no `hext`, no `M=mI`; `hatt` is `BAG5Attached` read through `BAGraph.shadow_mol` (`BAAtom:86`) and `shadow.solid := Γ.solid` (`BAAtom:63-65`); `shadow_nM` (`BAAtom:94`).
- Target 4 (`Bctl_small`, `Entry`): PASS (rows 5, 6). Target 5 (private arithmetic): PASS, S4 does not occur (rows 6, 8, 9, 11, 12; the `S2` prefactor is 4, not the band's 3).
- Target 6 (`BAG5LeafPrec1`): PASS. S5 does not occur: `T2465_Q1Need` equals `T2466_BAG5LeafPrec1` after renaming (diff exit 0). S3 does not occur: `baGbyZeta_holds` takes the entry law alone (`BAAuxGraph2B:586-597`), the other ingredients take no Step 1/2 pin. Target 7: PASS (`leaf1` above). Target 8: PASS (no `inductive`).
## (a′) Preflight corrections — Mon Oct 12 18:52:32 UTC 2026
1. Row 15 (envelope): `BAExp14d_env` takes `Ψ₀ = N²+1`, `ξ₀ ≡ 1`, `cc = Ψ₀`, `S2 = L^d`, `r = R = 0` as planned; the exponent is `Kenv = 3·natAbs(ord)+8+n_M+3n_S+n_A`
   (any polynomial exponent serves `BAExp14a_prec_integral`), not `K_env = 22`. Row 8 (window): `W^{-d} ≤ (λ²+1)B ≤ (𝔡⁻²+1)N^{2τ'}B` from `BAExp14a_Wd_le`; `A = 𝔡⁻²+1`
   is folded into `C_Γ(K₀A, K₁, Kd)` (no eventual step `A ≤ N^{2τ'}`). Row 16: the `lift(ω_t)` decay is `BASizeClaim_theta_decay` (private, `open private`). No verdict change.

## (b) Script output — Mon Oct 12 18:52:32 UTC 2026; branch `t/T2466` at `cebb7791`
Stage 1b: targets 1-7 built and committed; the stop rules S1-S5 of the ticket did not occur (evidence below and in the narrative).
```
$ wc -l RBM3D/Graph/BAExp14d.lean RBM3D/Graph/BAExp14dB.lean   # stop line 2000 per file; BAExp14dC.lean not created
     620 RBM3D/Graph/BAExp14d.lean
     908 RBM3D/Graph/BAExp14dB.lean
    1528 total
$ git diff --name-only main...t/T2466 | tr "\n" " "
RBM3D/Graph/BAExp14d.lean RBM3D/Graph/BAExp14dB.lean 
$ lake build RBM3D.Graph.BAExp14d RBM3D.Graph.BAExp14dB 2>&1 | tail -1;  lake build 2>&1 | tail -1
Build completed successfully (4012 jobs).
Build completed successfully (4291 jobs).
$ lake env lean RBM3D/Graph/BAExp14d.lean 2>&1 | wc -l;  lake env lean RBM3D/Graph/BAExp14dB.lean 2>&1 | wc -l   # warnings + errors
0 0
$ lake env lean axcheck.lean   # import RBM3D + both modules; #assert_rbm_axioms (RBM3D.lean untouched; the hub adds the two imports at merge)
with both modules: 13468 theorems, 4285 definitions, 0 axioms, 121 premises found by scanning; exit 0   |   baseline (import RBM3D only): 13457 theorems, 4277 definitions, 0 axioms, 121 premises found by scanning
$ #print axioms <declaration>   # axprint.lean, the six target theorems and `leaf1_props`; the output lines are identical up to the name:
7 declarations; set of axiom lists = [propext, Classical.choice, Quot.sound]
```
Target statements by `python3 stmts2.py` (docstrings, proofs omitted; lines cut at 150 columns; elisions marked), then the text comparison with the pins of the check file:
```
theorem BAExp14d_dataT_eq : ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W),
    BAExp14d_dataT d L W g0 E t m ω =
      ({ G := .., M := .., S := .., Sp := .., gPsi := .. } : BALData (Idx d L W)) :=   -- fields as in T2466_dataT_eq
theorem BAExp14d_val_scale : ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m →
    0 ≤ t → t < 1 → ∀ (ω : Ω d L W) (P : BAPGraph (Fin 2)) (ℓ : Fin 2 → Idx d L W),
      P.val (BAlwData d L W g0 E t m ω) ℓ = (t : ℂ) ^ P.g.nW * P.val (BAExp14d_dataT d L W g0 E t m ω) ℓ := by
def BAGtoAGT (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
          ... (9 lines: hypotheses on D, Ψ, A, r, R, ξ; identical to T2466_BAGtoAGT, see below) ...
              ‖Γ.val D ℓe‖ ≤
                Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                    (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
                  Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                    Γ.scalingSize Ψ W d L
theorem baGtoAGT_holds (d : ℕ) : BAGtoAGT d := by
theorem BAExp14d_Bctl_small (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀) := by
def BAExp14dEntry (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁))
theorem baExp14dEntry_holds (d : ℕ) : BAExp14dEntry d := by
def BAG5LeafPrec1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) → P.g.nM = 1 →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))
theorem baG5LeafPrec1_holds (d : ℕ) : BAG5LeafPrec1 d := by
$ python3 stmtdiff.py   # pin text of T2466-check.lean vs the Lean statement, whitespace normalised, names substituted (DT := BAExp14d_dataT)
pins compared: 6; identical: 6; different: 0   (dataT_eq, val_scale, BAGtoAGT, Bctl_small, entry, BAG5LeafPrec1)
```
Compiled nonempty instances, each in the file of its theorem (`BAExp14dInst`; `d = 3`, `sz0` (`L = 4`, `W = 32`), `zSeq`, `flow_sz0`, `t ≡ 1/2`; `leaf1`: `n_M = 1`, one external molecule):
```
$ python3 ex.py   # statement + application of the instances of targets 2 (G3), 4, 6 and of `val_scale`; not printed: `dataT_eq`, `BAExp14d_det`, `BAExp14d_pw` (targets 1, 3, 5)
# D0 ω := BAExp14d_dataT 3 (sz0.L 0) (sz0.W 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1/2) ((baFMz sz0 zSeq).m 0) (BAExp14a_slc sz0 0 ω);  Ψ0 := ((baFMz sz0 zSeq).eta 0 (1/2))⁻¹ + 1
# lines of `leaf1_props` (BAG5LeafProps, n_M = 1, ord = 3 by `decide`) and of the examples: BAExp14d.lean: 495 524 536 582 599; BAExp14dB.lean: 864 881 887 895
example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    leaf1P.val (BAlwData 3 (sz0.L 0) (sz0.W 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (1 / 2)
        ((baFMz sz0 zSeq).m 0) (BAExp14a_slc sz0 0 ω)) ![x, y] =
      ((1 / 2 : ℝ) : ℂ) ^ leaf1P.g.nW * leaf1P.val (D0 ω) ![x, y] :=
  BAExp14d_val_scale 3 (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) _ (1 / 2) _ (1 / 2) _ hr0 (by norm_num) (by norm_num) _ leaf1P _
example (ω : sz0.SeqΩ) (ℓe : Fin 2 → Idx 3 (sz0.L 0) (sz0.W 0)) :
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ‖leaf1.val (D0 ω) ℓe‖ ≤ [bound of G3 at Ψ0, A = 1, r = R = 0, ξ ≡ Ψ0: 5 lines] := by   -- proof elided (constants from baGtoAGT_holds, hG and hw
  exact hK (sz0.L 0) (sz0.W 0) (sz0.three_le_L 0) _ _ (1 / 2) _ g0_bounds.1 g0_bounds.2 hr0 (by norm_num) (by norm_num)
    (Fin 2) (Fin 4) leaf1 (by unfold BAGraph.Normal; exact ⟨by decide, by decide⟩) _ rfl rfl rfl rfl
    Ψ0 1 0 0 (fun _ _ => Ψ0) hG zero_le_one hwin le_rfl (by simp) (fun _ _ => hΨ0) (fun x y a b _ _ => hG x y) ℓe
example : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n in atTop, sz0.Bctl n (1 / 2) ≤ 2 * ((sz0.size n : ℕ) : ℝ) ^ (-c₀) := by
  obtain ⟨c₀, hc₀, h⟩ := BAExp14d_Bctl_small 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq flow_sz0
  exact ⟨c₀, hc₀, h (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le)⟩
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧
      PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-ε₁)) :=
  baExp14dEntry_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE
example (hE : STLocalEntrygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hA : LWAvgLawgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hL : STLmaxgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) (hK : STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2))
    (hD : STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2)) :
    PrecL sz0 μ0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p _ => ‖∫ ω, leaf1P.val (BAlwData 3 (sz0.L n) (sz0.W n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n) (1 / 2)
        ((baFMz sz0 zSeq).m n) (BAExp14a_slc sz0 n ω)) ![p.1, p.2] ∂μ0‖)
      (fun n _ _ => (1 / 2 : ℝ) ^ leaf1P.g.nW * ((baFMz sz0 zSeq).eta n (1 / 2))⁻¹ *
        (sz0.Bctl n (1 / 2)) ^ ((leaf1P.scalingOrder : ℝ) / 2)) :=
  baG5LeafPrec1_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) hE hA hL hK hD leaf1P leaf1_props.1 leaf1_props.2.1
```
Scratch pin check (copy of the check file + imports of both modules + one term-mode `example` per pin, not committed; negative control: `T2466_entry` closed by `baGtoAGT_holds`):
```
$ lake env lean T2466-check-scratch.lean  -> exit=0, errors=0; negative control errors=1
example : T2466_dataT_eq BAExp14d_dataT := BAExp14d_dataT_eq
example : T2466_val_scale BAExp14d_dataT := BAExp14d_val_scale
example : ∀ d, T2466_BAGtoAGT d := baGtoAGT_holds
example : ∀ d, T2466_Bctl_small d := BAExp14d_Bctl_small
example : ∀ d, T2466_entry d := baExp14dEntry_holds
example : ∀ d, T2466_BAG5LeafPrec1 d := baG5LeafPrec1_holds
example : ∀ d, T2465_Q1Need d := baG5LeafPrec1_holds
$ clash.sh   # git grep of BAExp14d|BAG5LeafPrec1|baG5LeafPrec1|BAGtoAGT|baGtoAGT|BAExp14dEntry|baExp14dEntry on main and every other t/T24* branch
hits: 0 over 67 refs (main + other t/T24* branches)
$ grep -nwE 'mE|STGM|STKloop|etaT|STflowE|lwS|lwSplus|LWG5Data' <both files>; echo $?;  grep -c 'RBM1D\|RBM2D' <both files>
exit=1 (1 = no hit)
RBM3D/Graph/BAExp14d.lean:0 RBM3D/Graph/BAExp14dB.lean:0 
```
Copies inside RBM3D (no port from RBM1D/RBM2D): `BAExp14d_G3` = `BAAtom2.lean:420-526` without `hext` (file commit `32a1b699`); twins of `LWExpTerm3.lean` (`20de014b`): `lwExpTerm3_det` :596, `_entry_whp` :846,
`_hent` :872, `_pathwise` :954, `_Q_le` :1059, `_size_le` :1103, `_arith` :1130, `lwGraphPrec1` :1442; reused public: `lwExpTerm3_floor`, `lwExpTerm3_Psi_zpow`, `BAAuxGraph2_eta_le_one`; `open private`: `lwExpTerm3_auxVal_zero/_one`.
Narrative: target 1 is `baSp_eq` plus the factor `t` of every waved edge (`BAExp14d_term_scale`). Target 2 applies `BAExp14d_G3` to the decay and `LWKBound` of `S'` (`lwBdist = 0` on its support), `lift(ω_t)`
(`BASizeClaim_theta_decay`), `M`, `g₀Ψ` (`BAAtom_decay_E`, `baKBound_E`; `lwKBound_of_decay`). Target 3 (`BAExp14d_det`) takes `ξ = min(cc ξ₀, Ψ)` and the band's `auxVal_zero/_one` on `Γ.shadow`.
Target 5 (`BAExp14d_pw`, `_env`, `_prec`, `_arith`): Ward sum `baZeta_ward_sum`, events `BAExp14d_entry_whp` and `baGbyZeta_holds` (`D₁ = 2/𝔠`, `ρ = 2R+(log W)^{3/2}`, `R = |E'⊕I'|r`).
`baG5LeafPrec1_holds` uses `STLocalEntrygL` only: `hA hLmax hLK hDec` occur in its `intro` line and nowhere else; `T2465_Q1Need` and `T2466_BAG5LeafPrec1` are closed by the same term.

## (c) Verified Mathlib names (one line each; `#eval` of `getConstInfo`, `chk_names.lean`; every name compiled in the build above)
```
Real.rpow_le_rpow_of_nonpos : ∀ {x y z : ℝ}, 0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z
Real.abs_le_sqrt : ∀ {x y : ℝ}, x ^ 2 ≤ y → |x| ≤ √y
zpow_le_zpow_right₀ : ∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a :
Filter.tendsto_atTop_mono' : ∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β] (l : Filter α) ⦃f₁ f₂ : α → β⦄, f₁ ≤ᶠ
MeasureTheory.integral_congr_ae : ∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace 
```

## (d) Open issues and paper-delta candidates
- File split: `BAExp14dEntry` and `BAG5LeafPrec1` (statement defs of targets 4, 6) sit in part B beside their theorems, `BAGtoAGT` in part A (the ticket's file note puts the defs of 4, 6 in part A); no pin changed.
- `RBM3D.lean` not edited (CLAUDE.md §1: root imports are the hub's). `open private` dependencies, fragile under upstream renames: `lwExpTerm3_auxVal_zero/_one`, `BASizeClaim_theta_decay`, and between the parts `BAExp14d_det`, `BAExp14d_GM_le`.
- Conditional adapter (§5.6): `baG5LeafPrec1_holds` is the `n_M = 1` half of the leaf pin, conditional on `3 ≤ d`, `BAFlow` and the five Step 1/2 premises (only `STLocalEntrygL` used); it is not the general `(eq;I42inG)`.
  The five pins stay hypotheses of the entry and leaf instances (other gates'); the data-level checks of the preflight (a) (ii) are the only evidence offered for them.
- Observation: a call of `BAExp14a_t_lt_one` (stated for `Sizes (k+2)`) at a variable `d` ended in a `whnf` heartbeat timeout during the 1b; `ba_G_data` is used instead.
- Paper-delta candidates: `T2466a` `(G_by_auxG_BA)` `B:486-490` is stated and proved without "distinct external vertices in distinct molecules" (`hext` is never used; `BAAtom2:416-417` records `T2170f`).
  `T2466b` internal parameters of the BA route differ from the band's (`ρ = 2R+(log W)^{3/2}`, `D₁ = 2/𝔠`, `c₀ = min(2𝔠𝔡, ε)/2`, `ε₁ = d c₀/4`, Ward constant 4 for 3, window constant `𝔡⁻²+1`): no statement changes.
