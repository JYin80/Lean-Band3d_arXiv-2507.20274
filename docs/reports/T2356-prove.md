Prover model: claude-sonnet-5-5
## (a) Math preflight — Fri Oct  9 01:09:20 UTC 2026

Notation: `N=(WL)^d`, `c_κ=√(κ(4-κ))/2`, `η_Q = ouEtaQ sz 𝔡 n = W^(-𝔡/3) lam W^(d/2)/N` (`ZeroModeProfile.lean:84`), `z=E+iη_Q`, `t₀=lemT z=|m(z)|²`, `E'=lemE z`, `ζ=ouZeta(t_n)=1-e^(-t_n)`, `t₁=(1-ζ)t₀`, `η_u=etaT E' u=(1-u)Im m(E')`, `Λ_u=(Nη_u)^(-1)`, `X=(lam² W^d)^(-1/5)`, `Bctl(t)=W^(-d)(1/(lam²+1-t)+1/(L^d(1-t)))` (`Bparam` at `K=0`, `Params.lean:36`, `Sizes.lean:214`), `calB=calB sz n η_Q 0` (`Endpoints.lean:58`), `qdBoundExp=W^τ calB²(X+calB)` (`Endpoints.lean:101`). Hypotheses (WO) `W^(-d/2+𝔡) ≤ lam ≤ 𝔡⁻¹`, `W ≥ N^𝔠`, `N→∞` (`Defs/Sizes.lean:164-177`); `ouTStar=N^(-1+τ_U)` (`Pins.lean:142`).

### (i) Exponent table (`𝔠=1/6, 𝔡=1/10, κ=1/10`, target loss `τ=1/100`; all slacks are exponents of `N` unless marked; script `slack.py` below)
| quantity | value | constraint it must satisfy | slack |
|---|---|---|---|
| `τ_U` | `ouTauMax=min(𝔠/12,𝔠𝔡/12,1/100)=1/720` (`ZeroModeProfile.lean:78`) | `0<τ_U ≤ ouTauMax` (hypothesis of the target) | 0 (taken equal) |
| `ε_Q` (STFlow domain) | `𝔠(𝔡-𝔡/3)=1/90` (`QUEFromQDiff.lean:91`, `ε₀=𝔡/3<𝔡`) | `N^(-1+ε_Q) ≤ η_Q ≤ 1` eventually: `Nη_Q ≥ W^(2𝔡/3) ≥ N^(2𝔠𝔡/3)` from (WO),`W≥N^𝔠` | 0 in the exponent (equality at the (WO) edge); `η_Q ≤ 1` needs `W→∞` |
| `h730`: `t₀-t₁=ζt₀ ≤ N^(-τ_U) η_(t₀)` | `ζ ≤ t_n ≤ N^(-1+τ_U)`, `η_(t₀) ≥ η_Q/16 ≥ N^(-1+2𝔠𝔡/3)/16` | `2τ_U < 2𝔠𝔡/3` | `1/120` (absorbs the constant 16) |
| `hscale`: `Λ_(t₀) ≤ N^(-τ_U)` | `Λ_(t₀) ≤ 16/(Nη_Q) ≤ 16 N^(-2𝔠𝔡/3)` | `τ_U < 2𝔠𝔡/3` | `7/720` |
| `hell`: `L^d(1-t₁) ≤ lam²` (replaces `L²(1-t₁) ≤ 1`) | `1-t₁=(1-t₀)+ζt₀`; `(1-t₀) ≤ η_Q/c_κ`; `ζ L^d ≤ N^(τ_U)/W^d`; `lam² ≥ W^(-d+2𝔡)` | `ζ`-part `τ_U < 2𝔠𝔡`; `(1-t₀)`-part `2/c_κ ≤ W^(4𝔡/3)` (as `W^(-𝔡/3-d/2)·2/c_κ ≤ lam`) | `23/720` (in `N`); `4𝔡/3=2/15` (in `W`) |
| `Λ`-scale comparison | `η_Q/16 ≤ η_(t₀) ≤ 16η_Q` (`lemma28_quant`, `Semicircle.lean:359`), `1-t₀ ≥ η_Q/4` (`(1-t₀)Im m(E')=√t₀ η_Q`, `t₀ ≥ 1/16`, `Im m ≤ 1`), `(1-t₀)c_κ ≤ η_Q` | pure constants | none needed |
| (i) initial term at `t₁` | `Bctl(t₁) ≤ 2/(N(1-t₁))` **iff `hell`** (`lam²+(1-t₁) ≥ L^d(1-t₁)`), `≤ 8/(Nη_Q) ≤ 8 calB` (`calB ≥ 1/(Nη_Q)`) | `‖𝔼𝓛₂-𝒦₂‖(t₁) ≤ N^ε Bctl(t₁)²(X+Bctl(t₁)) ≤ 512 N^ε calB²(X+calB)` | constant 512; `X`-factor kept as is (`X ≤ W^(-2𝔡/5)=W^(-1/25)`) |
| Grönwall `t₁→t₀` (`eq729_one_step`: factor `(1+Δ·2NρΛ)` per step) | `ρ=N^(τ_g)`, `τ_g=min(δ'/4,τ_U)=1/4800`; `(1+Δ2NρΛ)^K ≤ exp(2ρ(t₀-t₁)/η_(t₀)) ≤ exp(2N^(τ_g-τ_U))` | `τ_g ≤ τ_U` (so the factor is `≤ e²`) | `17/14400` |
| (ii) GUE terms | `K·eq729c ≲ N^(-τ_U)ρ²Λ³ + 10⁴N^(10)(N+1)^(-(16n₀+32))`, `Δ=(t₀-t₁)/K`, `K=(N+1)^(32n₀+64)` (`Grid.lean:106`), `p=N^(-D)` from `GUEPathBounds` | remainder `≤ Λ³ ≥ N^(-3)`: `16n₀+32 ≥ 13`; with `n₀=3` | `67`; `size ≥ 3^d` (27 at `d=3`, 81 at `d=4`; source has `9 ≤ size`) |
| loss conversion | `δ'=𝔠τ/2=1/1200`, `N^(δ') ≤ W^(δ'/𝔠)=W^(τ/2)` (`size_rpow_le_W_rpow`), `N^(δ')N^(δ') ≥ 23N^(δ')` | `W^(τ/2) ≥` absolute constants (eventually) | any `τ>0` |
| (iii) (7.47) step | `t₀Λ_(t₀)³ ≤ 4(Nη_Q)^(-3) ≤ 4calB³`; `calB·Nη_Q ≤ 2` (`calB_le_two_inv`, `QUEFromQDiff.lean:166`, needs `η_Q ≤ lam²/L^d`, `etaQ_le:208`) | `calB³ ≤ calB²·calB ≤ calB²(X+calB)` | constant 4 |
| `STExp2` bridge | `STFlow` needs `locDomain` at **every** `n` (`Defs/Sizes.lean:186`, `Induction/Defs.lean:286`), `η_Q ≤ 1` only eventually | modify `z_n` (and `t₁≤lemT z_n`) at finitely many `n`; `≺` (`StochDomAt`: `∀τ D, ∀ᶠ n`) is unchanged | none (tail argument) |

Resulting form of (7.29) at `d ≥ 3`: `‖𝔼𝓛₂(t₀)-K̃₂(t₀)‖ ≤ N^δ [ (Nη_(t₀))^(-3) + Bctl(t₁)²(X+Bctl(t₁)) ]`; it is **not** `N^δ(Nη_(t₀))^(-3)`: the initial term is not of the form `Λ³` (the factor `X` comes from `STExp2`).

### (ii) Concrete nondegenerate instance (`d=3` and `d=4`, `n=0`; sequence of `Sizes.lean` check block: `L=4(n+1)`, `W=(2(n+1))^5`, `lam=(2(n+1))^(-6)`, `E=1/2`, `n₀=3`, `ζ` at `t_n=ouTStar`)
Command (scratch files in the scratchpad subdirectory `T2356/`, not in the repository; `mpmath` 1.4.1, 700 digits, `m(z)` from `m²+zm+1=0`, `|m|<1`):
`cd $SCRATCH/T2356 && python3 chain.py` (checks: all deterministic hypotheses of the three targets and the links of (i), list printed below) and `python3 slack.py` (exact `Fraction`s).
```
constants: c=1/6 dd=1/10 kappa=1/10 tauU=1.388889e-03 eps_Q=1.111111e-02 tau=0.0100 delta'=8.333333e-04 tau_g=2.083333e-04
--- d=3, n=0: L=4, W=32, lam=1.5625e-02, N=2097152
    eta_Q=1.2016e-06  N*eta_Q=2.5198  t0=0.9999987590  1-t0=1.2410e-06  E'=0.500000
    zeta=4.8658e-07  1-t1=1.7275e-06  eta_t0=1.2016e-06  lam^2/L^d=3.8147e-06  L^d(1-t1)=1.1056e-04
    Bctl(t1)=4.0014e-01  calB=5.2124e-01  X=6.5975e-01  I0/Tgt=0.529  t0Lam^3/Tgt=0.195
    Gronwall exponent=8.1237e-01 (rho=1.0030); log10 K=1011.5; K*c = 1.273e-01
    all 27 checks True
    checks: WO lower W^{-d/2+𝔡} <= lam; WO upper lam <= 1/𝔡; Bandwidth N^𝔠 <= W; |E|<=2-κ; locDomain N^{-1+ε}<=eta_Q<=1; |E'|<=2-κ; Lemma2.8 zt(E',t0)=sqrt(t0) z (err); 0<=t1<=t0<1; t1<=lemT z (STFlow bridge); hell L^d(1-t1)<=lam^2; h730 t0-t1<=N^{-tauU} eta_t0; hscale (N eta_t0)^-1<=N^{-tauU}; eta_Q<=lam^2/L^d (etaQ_le); (1/16)eta_Q<=eta_t0<=16 eta_Q; (1-t0)>=eta_Q/4; (1-t0)*c_k<=eta_Q; Bctl(t1)<=2/(N(1-t1)); 2/(N(1-t1))<=8/(N eta_Q); Bctl(t1)<=8 calB; N eta_Q calB<=2 (calB_le_two_inv); t0*(N eta_t0)^-3<=4 (N eta_Q)^-3; I0 <= 512 Target(tau=0); t0 Lam^3 <= 4*(2)^3... Target(tau=0); Gronwall exponent 2 rho (t0-t1)/eta_t0 <= 2 N^{taug-tauU}; rho*Lam<=1; N*Delta<=1; K*eq729c <= 40 rho^2 Lam^3 N^{-tauU} + 1e4 N^{-70}
--- d=4, n=0: L=4, W=32, lam=1.5625e-02, N=268435456
    eta_Q=5.3102e-08  N*eta_Q=14.2544  t0=0.9999999452  1-t0=5.4843e-08  E'=0.500000
    zeta=3.8271e-09  1-t1=5.8670e-08  eta_t0=5.3102e-08  lam^2/L^d=9.5367e-07  L^d(1-t1)=1.5020e-05
    Bctl(t1)=6.7401e-02  calB=7.4059e-02  X=3.2988e-01  I0/Tgt=0.815  t0Lam^3/Tgt=0.156
    Gronwall exponent=1.4473e-01 (rho=1.0041); log10 K=1348.6; K*c = 1.254e-04
    all 27 checks True
limit table (hypotheses and chain hold at every n; N eta_Q -> infinity, Bctl(t1) and calB -> 0; ratios stay bounded):
d=3 n=       1: log10 N=  11.74 N*eta_Q=     6.350 Bctl(t1)=1.473e-01 calB=1.731e-01 X=4.353e-01 (W^(-2dd/5)=7.579e-01) I0/Tgt=0.693 I0/Bctl(t1)=8.58e-02 fails=[]
d=3 n=      10: log10 N=  25.07 N*eta_Q=    61.645 Bctl(t1)=1.554e-02 calB=1.632e-02 X=1.565e-01 (W^(-2dd/5)=5.389e-01) I0/Tgt=0.903 I0/Bctl(t1)=2.67e-03 fails=[]
d=3 n=    1000: log10 N=  60.33 N*eta_Q= 25232.024 Bctl(t1)=3.837e-05 calB=3.963e-05 X=1.045e-02 (W^(-2dd/5)=2.186e-01) I0/Tgt=0.937 I0/Bctl(t1)=4.02e-07 fails=[]
d=3 n= 1000000: log10 N= 114.32 N*eta_Q=251984545.958 Bctl(t1)=3.842e-09 calB=3.968e-09 X=1.657e-04 (W^(-2dd/5)=5.493e-02) I0/Tgt=0.937 I0/Bctl(t1)=6.37e-13 fails=[]
d=4 n=       1: log10 N=  15.65 N*eta_Q=   203.187 Bctl(t1)=4.757e-03 calB=4.937e-03 X=1.088e-01 (W^(-2dd/5)=7.579e-01) I0/Tgt=0.927 I0/Bctl(t1)=5.40e-04 fails=[]
d=4 n=      10: log10 N=  33.42 N*eta_Q=139943.783 Bctl(t1)=6.919e-06 calB=7.146e-06 X=7.114e-03 (W^(-2dd/5)=5.389e-01) I0/Tgt=0.937 I0/Bctl(t1)=4.93e-08 fails=[]
d=4 n=    1000: log10 N=  80.44 N*eta_Q=4524934326622.246 Bctl(t1)=2.140e-13 calB=2.210e-13 X=5.220e-06 (W^(-2dd/5)=2.186e-01) I0/Tgt=0.937 I0/Bctl(t1)=1.12e-18 fails=[]
d=4 n= 1000000: log10 N= 152.43 N*eta_Q=1425443413211088399892480.000 Bctl(t1)=6.793e-25 calB=7.015e-25 X=8.286e-11 (W^(-2dd/5)=5.493e-02) I0/Tgt=0.937 I0/Bctl(t1)=5.63e-35 fails=[]
```
```
tauU 1/720 = ouTauMax; eps_Q 1/90 ; delta' 1/1200 ; tau_g 1/4800
N^-exp of eta_Q lower bound: N eta_Q >= W^(2dd/3) >= N^(2 c dd/3) = N^1/90 (= eps_Q)
h730 : need 2 tauU < 2c dd/3 : slack 1/120
hscale: need tauU < 2 c dd/3 : slack 7/720
hell zeta-part: need tauU < 2 c dd (N^tauU <= W^(2dd)/2): slack 23/720
hell (1-t0)-part: W-exponent slack 4dd/3 = 2/15
Gronwall: tau_g <= tauU : slack 17/14400
X <= W^(-2dd/5) = W^ -1/25  ; N^delta' <= W^(delta'/c) = W^ 1/200 = W^(tau/2)
remainder: K^(1/2)=(N+1)^80 vs N^4(1+N)^6 N^3 = N^13 : slack exponent 67
d=2: size >= 3^d = 9 (source uses 9 <= size)
d=3: size >= 3^d = 27 (source uses 9 <= size)
d=4: size >= 3^d = 81 (source uses 9 <= size)
```
External hypotheses (limit computation, TEAM §8 lesson 14): `STExp2` at `(E',t₁)` (via `UNMLOut`) and `GUEPathBounds`. For `k=2`, `E=1/2`: the pin gives error `I0=Bctl(t₁)²(X+Bctl(t₁))`, `STKbound` gives the size `Bctl(t₁)` of `𝒦₂(t₁)`; the table's last column `I0/Bctl(t₁)=Bctl(X+Bctl)` tends to `0` (`8.6e-2 → 6.4e-13` at `d=3`, `n=1 → 10^6`) so the error is of smaller order than the main term; `Bctl(t₁)/calB` stays `≤ 8` (`0.77` to `0.97` in the table); `Nη_Q → ∞` (`2.52 → 2.5e8` at `d=3`); the target bound `qdBoundExp` is `W^τ calB²(X+calB) → 0`. The grid size `K=(N+1)^160` (`log10 K = 1011.5` at `d=3`, `n=0`) is a proof device, not a witness; it only enters through `NΔ ≤ 1` and the printed `K·c = 1.3e-1`, `1.3e-4`. The conclusion of the three targets is an eventual statement (explicit constants `512, 4, e², 23` are absorbed by `W^(τ/2)`); only the hypotheses are instantiated at `n=0` (nondegenerate: `N=2097152`, `N η_Q=2.52`, `0<t₁<t₀<1`, `ζ=4.9e-7`).

### Verdicts
- `gueGrid_eq729` (RBM3D form): **PASS**. Every hypothesis holds at the instance; the chain (i)-(iii) closes with the shape above; `hell` (as `L^d(1-t₁) ≤ lam²`) is what turns `Bctl(t₁)` into `Λ`-scale and it is derived from `τ_U ≤ ouTauMax` (rows `h730`, `hscale`, `hell`).
- `Eq729B_eq747_of_eq729`: **PASS** (`t₀Λ³ ≤ 4(Nη_Q)^(-3)`; `calB ≥ 1/(Nη_Q)` converts to `qdBoundExp`; `W^τ` from `N^(δ')`).
- `Eq729B_eq747_of_inputs` (body of `UNOUEq747`): **PASS**, conditional only on the two bookkeeping facts of the table: the tail modification of `z_n` for `STFlow`, and the identification of `avg2` of `|G_xy|²`, `G_xy G_yx` with the loops (merged twin `loopFine_pm_formula` is `private`, `Green/Pins.lean:418`: re-derive); no new pin is needed for `STExp2 sz E' t₁` from `UNMLOut` at `z_n=E_n+iη_Q`, `t₁ ≤ lemT z_n=t₀`.

## (a′) Preflight corrections — Fri Oct  9 02:10:07 UTC 2026
Section (a) is not edited; verdicts are unchanged (PASS). Three statements of (a) are superseded by the stage-1a findings (`docs/reports/T2356-design.md` section 0):
1. Row (i) "initial term at `t₁`": "`Bctl(t₁) ≤ 2/(N(1-t₁))` **iff `hell`**". The comparison with `calB` needs no `hell`: `Bctl(t₁) ≤ 2𝓑_{η_Q,0}` follows from `η_Q ≤ 2(1 - t₁)` alone (`bctl_le_two_calB`, probe 192, compiled; `zRange`, `Main/ZTransfer.lean:79`: `1 - t₀ ≥ η_Q/2`). The constants of rows (i) and "Λ-scale" become: `1 - t₀ ≥ η_Q/2` (not `/4`), `Bctl(t₁) ≤ 2𝓑` (not `8 calB`), `I₀ ≤ 8·Target` (not `512`); `c_κ = √(κ(4-κ))/2` of row `hell` is `√(κ(4-κ))/8` in the merged `im_msc_ge` (`Main/ZTransfer.lean:130`). `hell` is needed only by the K̃ bounds of target 1 (`Hyp_Kt_detDom`).
2. Verdicts, `Eq729B_eq747_of_inputs`: "conditional only on the two bookkeeping facts" lacks a third, the `∀ n` facts of the flow data (`|E'| ≤ 2 - κ`, `0 ≤ t₁ ≤ t₀ < 1`), false at the finitely many `n` with `ilambda_n ≤ 0` (design F2); `goodFlow` (probe 177, proved) supplies good data. The bridge of the "tail modification" is proved (`bridge`, probe 182).
3. `gueGrid_loop_duhamel` is not an ingredient of `Eq729B` (design F4, B2); the ticket lists `DuhamelC` among the imports.
4. (stage 1b, Fri Oct  9 20:05:22 UTC 2026) Row "loss conversion": the constant is 12, not 23: `Eq729B_assembly_747` gives `t₀ N^{δ'}(Λ³ + I₀) ≤ 12 N^{δ'} 𝓑²(X + 𝓑)` (`4 + 8`, constants of item 1), absorbed by `W^τ` through `Eq729B_loss_absorb` (`12 ≤ N^{𝔠τ/2}`, eventually). Rows `(iii)`: `calB·Nη_Q ≤ 2` (`calB_le_two_inv`) and `etaQ_le` are not used (`grep` count 0 in the new file).

### (b) Script output — Fri Oct  9 20:05:22 UTC 2026 (stage 1b; the stage-1a sections (b)-(d) of this file are `git show 8d76de9:docs/reports/T2356-prove.md`; `$SC` is the scratchpad subdirectory `T2356/` of the session, not in the repository; its scripts are named in the commands)
**B1 build, hygiene, size** (worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2356`, branch `t/T2356`)
```
$ git log -1 --format='%h %s' | cut -c1-96; git status --short | wc -l | tr -d ' '; wc -l RBM3D/Universality/GUEPhase/Eq729B.lean
86cc4f2 T2356: gueGrid_eq729 closes the evolution factor with Eq729B_gronwall_factor (chain link
0
    1674 RBM3D/Universality/GUEPhase/Eq729B.lean
$ lake build RBM3D.Universality.GUEPhase.Eq729B 2>&1 | grep -n "Eq729B\|Build completed\|error"
401:Build completed successfully (3818 jobs).
$ lake env lean RBM3D/Universality/GUEPhase/Eq729B.lean; echo "exit=$?"   # no output: no warning
exit=0
$ lake build 2>&1 | tail -1   # full library; RBM3D.lean does not import the module yet (the hub adds it at merge), see B9
Build completed successfully (4170 jobs).
$ grep -cE "sorry|admit|native_decide|^ *axiom " RBM3D/Universality/GUEPhase/Eq729B.lean
0
$ grep -n "^import" RBM3D/Universality/GUEPhase/Eq729B.lean | sed "s/import RBM3D\.//" | tr "\n" " "; echo; grep -c "DuhamelC\|^import RBM3D$" RBM3D/Universality/GUEPhase/Eq729B.lean
6:Universality.GUEPhase.Eq729A 7:Universality.GUEPhase.OneLoop 8:Universality.GUEPhase.KPrim 9:Universality.GUEPhase.BootstrapAt 10:Universality.GUEPhase.HypA 11:Universality.ZeroModeProfile 12:Main.ZTransfer 13:Main.QUEFromQDiff 14:Loop.KLFinal 15:Loop.KLTree 
0
$ git diff --stat main...t/T2356 | cat
 RBM3D/Probe/T2356Pins.lean              |  398 ++++++++
 RBM3D/Universality/GUEPhase/Eq729B.lean | 1674 +++++++++++++++++++++++++++++++
 2 files changed, 2072 insertions(+)
$ for h in $(git log --reverse --format=%h -- RBM3D/Universality/GUEPhase/Eq729B.lean); do echo -n "$h $(git show $h:RBM3D/Universality/GUEPhase/Eq729B.lean | wc -l | tr -d " ") lines; "; done; echo   # stop rule: 2400
eeaf29c 834 lines; d066a24 1081 lines; d7787f6 1278 lines; a396d18 1667 lines; be22099 1675 lines; 17adae6 1677 lines; 86cc4f2 1674 lines; 
```
**B2 axioms** (`#print axioms` of the 56 public declarations of the file, listed by `decls.py`)
```
$ (echo "import RBM3D.Universality.GUEPhase.Eq729B"; python3 $SC/decls.py RBM3D/Universality/GUEPhase/Eq729B.lean pub | awk -F"\t" '{print "#print axioms " $3}') > $SC/ax.lean; lake env lean $SC/ax.lean > $SC/ax.out 2>&1; echo "exit=$?"; sed -E "s/.*depends on axioms: //" $SC/ax.out | sort | uniq -c
exit=0
  56 [propext, Classical.choice, Quot.sound]
$ grep -E "'RBM.Univ.GUEPhase.(gueGrid_eq729|Eq729B_eq747_of_eq729|Eq729B_eq747_of_inputs|Eq729B_goodFlow|Eq729B_bridge)'" $SC/ax.out | sed "s/RBM.Univ.GUEPhase.//"
'gueGrid_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'Eq729B_eq747_of_eq729' depends on axioms: [propext, Classical.choice, Quot.sound]
'Eq729B_eq747_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'Eq729B_goodFlow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Eq729B_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
```
**B3 the statements are the passed pins** (the probe `RBM3D/Probe/T2356Pins.lean` of design section 1, last commit `fe9888f`, against the file, checked by Lean in a scratch file that imports both; the only conversion is the probe's `FlowData` ↔ `Eq729B_FlowData`, two structures with the same three fields)
```
$ cat $SC/pincheck2.lean
import RBM3D.Probe.T2356Pins
import RBM3D.Universality.GUEPhase.Eq729B
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Univ.GUEPhase RBM.Endpoints
set_option linter.unusedVariables false
namespace RBM.Probe.T2356
theorem fdB {d} {sz : Sizes d} {𝔡 : ℝ} {E t E' t0 t1 : ℕ → ℝ} (h : FlowData sz 𝔡 E t E' t0 t1) : Eq729B_FlowData sz 𝔡 E t E' t0 t1 := ⟨h.hE', h.ht0, h.ht1⟩
theorem fdP {d} {sz : Sizes d} {𝔡 : ℝ} {E t E' t0 t1 : ℕ → ℝ} (h : Eq729B_FlowData sz 𝔡 E t E' t0 t1) : FlowData sz 𝔡 E t E' t0 t1 := ⟨h.hE', h.ht0, h.ht1⟩
example : PinGueGrid729 := @gueGrid_eq729
example : PinEq747OfEq729 := @fun d sz hd 𝔠 𝔡 hA κ hκ E t hE ht E' t0 t1 hF K hK H τ hτ => Eq729B_eq747_of_eq729 sz hd hA hκ hE ht (fdB hF) hK H τ hτ
example : PinEq747OfInputs := @fun d sz hd 𝔠 𝔡 hA κ τU hκ hτU hτUm n0 hn0 E t hE ht E' t0 t1 hF hg Kt h1 h2 h3 hB hP τ hτ => Eq729B_eq747_of_inputs sz hd hA hκ hτU hτUm n0 hn0 hE ht (fdB hF) hg Kt h1 h2 h3 hB hP τ hτ
example : PinSTExp2OfUNMLOut := @fun d hML hd sz 𝔠 𝔡 hA κ hκ E t hE ht E' t0 t1 hF => Eq729B_bridge hML hd sz hA hκ hE ht (fdB hF)
example : PinGoodFlow := @fun d sz 𝔠 𝔡 hA κ hκ E t hE ht => let ⟨E', t0, t1, hF, hg⟩ := Eq729B_goodFlow sz hA hκ hE ht; ⟨E', t0, t1, fdP hF, hg⟩
example : PinDerived := @fun d sz 𝔠 𝔡 hA κ τU hκ hτU hτUm E t hE ht E' t0 t1 hF => Eq729B_derived sz hA hκ hτU hτUm hE ht (fdB hF)
example : @Eq729Concl = @Eq729B_Concl ∧ @OUBody = @Eq729B_OUBody ∧ @initTerm = @Eq729B_initTerm ∧ @eqErr = @Eq729B_eqErr := ⟨rfl, rfl, rfl, rfl⟩
example : @bctl_le_two_calB = @Eq729B_bctl_le_two_calB ∧ @Ld_mul_etaQ = @Eq729B_Ld_mul_etaQ ∧ @hell_of_scales = @Eq729B_hell_of_scales ∧
    @claimA = @Eq729B_claimA ∧ @h730_hscale_real = @Eq729B_h730_hscale_real ∧ @qdBoundExp_eq = @Eq729B_qdBoundExp_eq ∧
    @assembly_747 = @Eq729B_assembly_747 ∧ @final_729 = @Eq729B_final_729 ∧ @gronwall_factor = @Eq729B_gronwall_factor :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end RBM.Probe.T2356
$ lake env lean $SC/pincheck2.lean; echo "exit=$?"
exit=0
$ lake env lean $SC/pincheck2_neg.lean 2>&1 | grep -c "error: Type mismatch"   # negative controls (a pin proved by the wrong theorem, two false equalities): must fail
3
```
**B4 target statements**, extracted from the file by `stmts.py` (`[a-b]` = lines of the file; theorems from `theorem NAME` to `:=`, definitions whole; whitespace joined)
```
$ python3 $SC/stmts.py RBM3D/Universality/GUEPhase/Eq729B.lean gueGrid_eq729 Eq729B_eq747_of_eq729 Eq729B_eq747_of_inputs Eq729B_goodFlow Eq729B_bridge Eq729B_Concl Eq729B_FlowData Eq729B_ueq747_iff
[622-638] theorem gueGrid_eq729 (sz : Sizes d) (hd : 3 ≤ d) {κ τU Λ : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 3 ≤ n0) {E t1 t0 : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop) (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (hE : ∀ n, |E n| ≤ 2 - κ) (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
  (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E n) (t0 n)) (hscale : ∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)) (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) (hKb : sz.STKbound E) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool)
  (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a) (hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) (hK2 : ∀ n, ∀ s ∈
  Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (t1 n) s σ₁ σ₂ a b) (hB : sz.STExp2 E t1) (hP : GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt) : Eq729B_Concl sz E t1 t0 (gueGridK sz n0)
[1077-1080] theorem Eq729B_eq747_of_eq729 (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ} (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) {K : ℕ → ℕ} (hK : ∀ n, K n ≠ 0) (H729 : Eq729B_Concl sz E' t1 t0 K) (τ : ℝ) (hτ : 0
  < τ) : Eq729B_OUBody sz 𝔡 E t τ
[1221-1235] theorem Eq729B_eq747_of_inputs (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) (n0 : ℕ) (hn0 : 3 ≤ n0) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) {E' t0 t1 : ℕ → ℝ} (hF : Eq729B_FlowData sz 𝔡 E t
  E' t0 t1) (hgood : ∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (hKinit : ∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a) (hK : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1
  ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) (hK2 : ∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E' n)) (t1 n) s σ₁ σ₂ a b) (hB
  : sz.STExp2 E' t1) (hP : GUEPathBounds sz E' t1 t0 (gueGridK sz n0) n0 Kt) (τ : ℝ) (hτ : 0 < τ) : Eq729B_OUBody sz 𝔡 E t τ
[1307-1309] theorem Eq729B_goodFlow (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) : ∃ E' t0 t1 : ℕ → ℝ, Eq729B_FlowData sz 𝔡 E t E' t0 t1 ∧ ∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1
[1316-1318] theorem Eq729B_bridge (hML : UNMLOut d) (hd : 3 ≤ d) (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) {E' t0 t1 : ℕ → ℝ} (hF : Eq729B_FlowData sz 𝔡 E t E' t0 t1) : sz.STExp2 E' t1
[104-106] def Eq729B_Concl (sz : Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) : Prop := ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ₂ : Bool) (a b : Zd d (sz.L n)), Eq729B_eqErr sz E t1 t0 K n σ₂ a b ≤ Nsz sz n ^ δ * ((gueScale sz E n (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n))
[87-90] structure Eq729B_FlowData (sz : Sizes d) (𝔡 : ℝ) (E t E' t0 t1 : ℕ → ℝ) : Prop where hE' : ∀ᶠ n in atTop, E' n = lemE (Eq729B_zQ sz 𝔡 E n) ht0 : ∀ᶠ n in atTop, t0 n = lemT (Eq729B_zQ sz 𝔡 E n) ht1 : ∀ᶠ n in atTop, t1 n = (1 - ouZeta (t n)) * t0 n
[126-128] theorem Eq729B_ueq747_iff (sz : Sizes d) (𝔡 τU : ℝ) : UNOUEq747 sz 𝔡 τU ↔ ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ → Eq729B_OUBody sz 𝔡 E t τ
```
**B5 compiled nonempty instances** (`Eq729BInst`, `insts.py`, `[n]` = line of the file; `sz0` = merged `SizesInst.sz0`, `d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`, `n = 0`: `L = 4`, `W = 32`, `N = 2097152`; `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/10`, `E = 0`)
```
$ python3 $SC/insts.py RBM3D/Universality/GUEPhase/Eq729B.lean
[1476] theorem inst_gueGrid_eq729 : ∃ Kt : (n : ℕ) → ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ, sz0.STExp2 Ei tw1 → GUEPathBounds sz0 Ei tw1 tw0 (gueGridK sz0 3) 3 Kt → Eq729B_Concl sz0 Ei tw1 tw0 (gueGridK sz0 3)
  := obtain ⟨Kt, h1, h2, h3⟩ := exists_Kt exact ⟨Kt, fun hB hP => gueGrid_eq729 sz0 (le_refl 3) (κ := 1 / 10) (τU := 1 / 30) (Λ := 1) (by norm_num) (by norm_num) 3 (le_refl 3) (Sizes.tendsto_size sz0 sz0_tendsto) hlam1 hE0 tw1_nonneg tw1_le_tw0 tw0_lt_one (Eventually.of_forall h730_at) (Eventually.of_forall hscale_at)
    (Eventually.of_forall hell_at) hKb0 Kt h1 h2 h3 hB hP⟩
[1529] theorem inst_claimA : 4 * Nsz sz0 7 ^ (2 * (1 / 240 : ℝ)) ≤ Nsz sz0 7 * ouEtaQ sz0 (3 / 10) 7
  := Eq729B_claimA sz0 7 (𝔠 := 1 / 6) (𝔡 := 3 / 10) (τU := 1 / 240) (by norm_num) (by norm_num)
[1535] theorem inst_hell_of_scales : ((sz0.L 7 : ℕ) : ℝ) ^ 3 * (1 - (1 - Nsz sz0 7 ^ (-1 + 1 / 240 : ℝ)) * (1 - ouEtaQ sz0 (3 / 10) 7)) ≤ sz0.lam 7 ^ 2
  := Eq729B_hell_of_scales sz0 7 (𝔡 := 3 / 10) (c := 1) (τU := 1 / 240) (ζ := Nsz sz0 7 ^ (-1 + 1 / 240 : ℝ))
[1544] theorem inst_assembly_747 : (1 / 2 : ℝ) * (1 * ((100 * (Real.sqrt (1 / 2) * (1 / 10)))⁻¹ ^ 3 + (1 / 5) ^ 2 * (1 / 10 + 1 / 5))) ≤ 12 * ((1 / 5) ^ 2 * (1 / 10 + 1 / 5))
  := Eq729B_assembly_747 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
[1562] theorem inst_goodFlow : ∃ E' t0 t1 : ℕ → ℝ, Eq729B_FlowData sz0 (1 / 10) Ei tU E' t0 t1 ∧ ∀ n, |E' n| ≤ 2 - 1 / 10 ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1
  := Eq729B_goodFlow sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1)
[1576] theorem inst_derived : (∀ᶠ n in atTop, T0c n - T1c n ≤ Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10)) * etaT (Ec n) (T0c n)) ∧ (∀ᶠ n in atTop, (gueScale sz0 Ec n (T0c n))⁻¹ ≤ Nsz sz0 n ^ (-ouTauMax (1 / 6) (1 / 10))) ∧ (∀ᶠ n in atTop, ((sz0.L n : ℕ) : ℝ) ^ 3 * (1 - T1c n) ≤ sz0.lam n ^ 2)
  := Eq729B_derived sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hτUi le_rfl hE0 tU_ok fdc
[1584] theorem inst_bridge (hML : UNMLOut 3) : sz0.STExp2 Ec T1c
  := Eq729B_bridge hML (le_refl 3) sz0 sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1) fdc
[1589] theorem inst_eq747_of_eq729 (H729 : Eq729B_Concl sz0 Ec T1c T0c (gueGridK sz0 3)) (τ : ℝ) (hτ : 0 < τ) : Eq729B_OUBody sz0 (1 / 10) Ei tU τ
  := Eq729B_eq747_of_eq729 sz0 (le_refl 3) sz0_admissible (κ := 1 / 10) (by norm_num) hE0 (fun n => (tU_ok n).1) fd
[1598] theorem inst_eq747_of_inputs (hML : UNMLOut 3) : ∃ (E' t0 t1 : ℕ → ℝ) (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (sz0.L n)) → ℂ), Eq729B_FlowData sz0 (1 / 10) Ei tU E' t0 t1 ∧ (∀ n, |E' n| ≤ 2 - 1 / 10 ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1) ∧ (GUEPathBounds sz0 E' t1 t0 (gueGridK sz0 3) 3 Kt → ∀ τ : ℝ, 0 < τ → Eq729B_OUBody sz0 (1 / 10)
  Ei tU τ)
  := obtain ⟨E', t0, t1, hF, hgood⟩ := inst_goodFlow choose Kt h1 h2 h3 using fun n => gueK_exists 3 (sz0.L n) (sz0.W n) (sz0.three_le_L n) (sz0.lam n) (E := E' n) (by linarith [(hgood n).1, abs_nonneg (E' n)] : |E' n| < 2) (hgood n).2.1 (hgood n).2.2.1 (hgood n).2.2.2 (4 * 3) refine ⟨E', t0, t1, Kt, hF, hgood, fun hP τ hτ =>
    ?_⟩ exact Eq729B_eq747_of_inputs sz0 (le_refl 3) sz0_admissible (κ := 1 / 10) (τU := ouTauMax (1 / 6) (1 / 10)) (by norm_num) hτUi le_rfl 3 (le_refl 3) hE0 tU_ok hF hgood Kt (fun n k σ a => h1 n _) (fun n t ht I hI h hl => h2 n t ht I hI h hl) h3 (Eq729B_bridge hML (le_refl 3) sz0 sz0_admissible (κ := 1 / 10) (by norm_num)
    hE0 (fun n => (tU_ok n).1) hF) hP τ hτ
-- plus 10 more (`inst_bctl_le_two_calB` and unnamed `example`s: real-variable lemmas, STExp2_congr, FlowData.ev_eq, bridge + congr)
```
**B6 limit check of the external hypotheses** `STExp2`, `GUEPathBounds`, `UNMLOut` of the instances (TEAM §8 lesson 14; `lim.py`, `mpmath` 600 digits; `inst_gueGrid_eq729` window and the OU window of `inst_eq747_*`): the sizes go to `0` and `Nη → ∞`, and `I₀/Bctl(t₁) = Bctl(X + Bctl) → 0` (the error is of smaller order than `‖𝒦₂(t₁)‖ ≲ Bctl(t₁)`)
```
$ python3 $SC/lim.py
instance inst_gueGrid_eq729 (E=0, y=lam^2/(2L^3), t0=1-y, t1=1-y-y/N): eta_t0=y, G=N*eta_t0 (gueScale)
  n        N*eta_t0     Lambda^3     Bctl(t1)     I0=Bctl^2(X+Bctl)   I0/Bctl(t1)
  0        4.0          0.01562      0.374        0.1446              0.3867
  1        32.0         3.052e-5     0.04686      0.001059            0.02259
  10       5324.0       6.627e-12    0.0002817    1.245e-8            4.418e-5
  1000     4.012e+9     1.549e-29    3.739e-10    1.461e-21           3.907e-12
  1000000  4.0e+18      1.562e-56    3.75e-19     2.33e-41            6.215e-23
instances inst_eq747_* (E=0, dd=1/10, tauU=ouTauMax=1/720, t_n=N^(-1+tauU), z=i*eta_Q):
  n        N*eta_Q      1-t0         zeta         Bctl(t1)     calB         Bctl(t1)/calB  qd(tau=0)=calB^2(X+calB)
  0        2.52         1.202e-6     4.866e-7     0.4066       0.5212       0.7801         0.3209
  1        6.35         1.155e-11    1.889e-12    0.151        0.1731       0.8721         0.01823
  10       61.64        5.287e-24    9.292e-26    0.01604      0.01632      0.9828         4.601e-5
  1000     2.523e+4     1.182e-56    5.68e-61     3.963e-5     3.963e-5     1.0            1.648e-11
  1000000  2.52e+8      1.202e-106   6.873e-115   3.968e-9     3.968e-9     1.0            2.61e-21
```
**B7 name clash and ports** (RBM2D read-only: `grep`/`git --no-optional-locks` only)
```
$ python3 $SC/decls.py RBM3D/Universality/GUEPhase/Eq729B.lean pub | awk -F"\t" '{n=split($3,a,"."); print a[n]}' | sort -u > $SC/pubnames.txt; python3 $SC/clash.py $SC/pubnames.txt
56 public short names checked, declaration-level hits outside Probe/ and outside the new file: 0
$ grep -rnE "\b(gueGrid_eq729|Eq729B_eq747_of_eq729|Eq729B_eq747_of_inputs|Eq729BInst|Eq729B_[A-Za-z0-9_]*)\b" RBM3D RBM3D.lean --include="*.lean" | grep -v "^RBM3D/Probe/" | grep -v "^RBM3D/Universality/GUEPhase/Eq729B.lean" | cut -c1-100
RBM3D/Universality/GUEPhase/Eq729A.lean:15:`gueGrid_eq729`) is UN-47 `Eq729B`.
$ grep -c "etaQ_le\|calB_le_two_inv" RBM3D/Universality/GUEPhase/Eq729B.lean
0
$ cd /Users/junyin/Lean_proof/RBM3D; git -C ../RBM2D --no-optional-locks log -1 --format=%h; git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/Eq729B.lean | wc -l | tr -d " "; git -C ../RBM2D --no-optional-locks status --short -- RBM2D/Universality/GUEPhase/Eq729B.lean | wc -l | tr -d " "; wc -l < ../RBM2D/RBM2D/Universality/GUEPhase/Eq729B.lean | tr -d " "   # main worktree, so that ../RBM2D is the sister project
9e0f275
0
0
1419
```
**B8 translation table** RBM2D `Eq729B.lean:line` (commit `9e0f275`, unchanged: diff-stat above is empty) → RBM3D (`name@line` in the new file, or `file:line` of the merged twin); `table2.py`; token similarity = `difflib` ratio of the Lean token sequences after the port-map renaming (`d.L`→`sz.L`, `Z2`→`Zd d`, `gloop`→`loopL d`, `spectralZ`→`zt`, `KLoop.mSig`→`mSigma`, …)
```
$ python3 $SC/table2.py
RBM2D Eq729B_c_nonneg:67, Eq729B_perN:75 -> Eq729B_c_nonneg@132, Eq729B_perN@140  [port; token similarity c_nonneg 0.99, perN 0.99]
RBM2D Eq729B_exp_two_lt:358, Eq729B_arith:368 -> Eq729B_exp_two_lt@214, Eq729B_arith@224  [port, N-only; token similarity exp_two_lt 0.99, arith 1.00]
RBM2D Eq729B_nine_le_size:183, Eq729B_gueScale_pos:191, Eq729B_gueScale_anti:196, Eq729B_inv_scale_le:201 -> Eq729B_nine_le_size@538, Eq729B_gueScale_pos@547, Eq729B_gueScale_anti@551, Eq729B_inv_scale_le@555  [port; nine_le_size adapted (9 <= N from 3^d <= (W L)^d, d >= 3), the others over sz, Nsz; token similarity nine_le_size 0.81, gueScale_pos 0.88, gueScale_anti 0.92, inv_scale_le 0.93]
RBM2D Eq729B_transfer:330, Eq729B_Bad:504, Eq729B_not_bad:513 -> Eq729B_transfer@569, Eq729B_Bad@594, Eq729B_not_bad@603  [port, renamed (gloop, Z2, blockMat); token similarity transfer 0.85, Bad 0.96, not_bad 0.96]
RBM2D gueGrid_eq729:531 -> gueGrid_eq729@622  [TARGET 1 (Hyp_Kt_* instead of Eq729B_Kt_one/_initial/_K_bounds; hB := STExp2; I0 term); token similarity gueGrid_eq729 0.87]
RBM2D Eq729B_size_pos:175, Eq729B_Kt_one:156, Eq729B_initial:224, Eq729B_K_bounds:264, Eq729B_loopOf_eq:212 -> Nsz_pos@Endpoints.lean:476, Hyp_Kt_one@Universality/GUEPhase/HypA.lean:712, Hyp_Kt_detDom@Universality/GUEPhase/HypA.lean:690, Hyp_exists_loopOf@Universality/GUEPhase/HypA.lean:299  [merged twins (T2352; T2352a = hell, hKb, hKinit); Eq729B_ofFn_getD:205 not needed]
RBM2D Eq729B_trGEGEmat_eq_gloop:787, Eq729B_spectralZ_eq:806 -> Eq729B_avg2_eq_loop@879, Eq729B_avg2_abs_sq@914  [re-derived: avg2 of Gres = loopL (b,a), |G|^2 = G G^-; spectralZ_eq:806 not needed (eq729_zt_im, zt_im_lemma28)]
RBM2D Eq729B_law726:822 -> Eq729B_law726@935  [port (avg2 of Gres, ouMat band carrier, map_gueH_last, GUEPhaseGrid_gloop_two_smul_lemT_eq); token similarity law726 0.77]
RBM2D Eq729B_etaQ_pos:890, Eq729B_etaQ_mul_size:899, Eq729B_etaQ_le_inv_sq:912 -> locDomain_im_pos@Endpoints.lean:481, Eq729B_Ld_mul_etaQ@377, etaQ_le@Main/QUEFromQDiff.lean:208  [queDomain/locDomain_im_pos (eta_Q > 0, <= 1); Ld_mul_etaQ re-derived (d >= 3 form); etaQ_le (twin) not used (no hell at 7.47)]
RBM2D Eq729B_meta_eq:938, Eq729B_meta_cmp:957 -> Eq729B_qdBoundExp_eq@484, Eq729B_bctl_le_two_calB@354  [re-derived: Meta -> calB, qdBoundExp; Bctl <= 2 calB from eta_Q <= 2(1-t1)]
RBM2D Eq729B_profile_eq:869, Eq729B_etaT_lemT:972, Eq729B_lemT_lt_one:979, Eq729B_one_sub_lemT_le:987 -> lemT_mul_kTwoGUE_pm_eq_profPMTilde@Universality/GUEPhase/KPrim.lean:275, Eq729B_kTwoGUE_symm@988, zt_im_lemma28@Defs/Semicircle.lean:344, lemT_lt_one@Defs/Semicircle.lean:209, zRange@Main/ZTransfer.lean:79, im_msc_ge@Main/ZTransfer.lean:130  [merged twins (profile_eq + 10 lines: Theta_transpose)]
RBM2D Eq729B_scale_747:1011 -> Eq729B_assembly_747@490  [re-derived with I0 and calB (constant 12)]
RBM2D Eq729B_eq747_of_eq729:1041 -> Eq729B_eq747_of_eq729@1077  [TARGET 2; token similarity eq747_of_eq729 0.24]
RBM2D Eq729B_pw:1139 -> Eq729B_goodFlow_aux@1274, Eq729B_goodFlow@1307, Eq729B_flowData_formulas@1258  [replaced by good data for every n (design F2, T2356c)]
RBM2D Eq729B_claimA:1163, Eq729B_Ntau_le_etaQ:1185 -> Eq729B_claimA@441  [re-derived at the new eta_Q (W^{-dd/3} ilambda W^{d/2}/N); token similarity claimA 0.47]
RBM2D Eq729B_good_pw:1207 -> Eq729B_h730_hscale_real@467, Eq729B_hell_of_scales@400  [re-derived (L^d (1-t1) <= ilambda^2)]
RBM2D Eq729B_derived:1339 -> Eq729B_derived@1125  [re-derived at the new eta_Q, L^d, ilambda^2; token similarity derived 0.34]
RBM2D Eq729B_eq747_of_inputs:1384 -> Eq729B_eq747_of_inputs@1221  [TARGET 3; token similarity eq747_of_inputs 0.61]
new in RBM3D (no RBM2D source): Eq729B_zQ, Eq729B_FlowData, Eq729B_initTerm, Eq729B_eqErr, Eq729B_Concl, Eq729B_OUBody, Eq729B_ueq747_iff, Eq729B_final_729, Eq729B_gronwall_factor, Eq729B_loss_absorb, Eq729B_core747, Eq729B_STExp2_congr, Eq729B_FlowData.ev_eq, Eq729B_bridge, Eq729B_flowData_formulas
```
**B9 registry pre-check** (scratch `reg.lean` = `import RBM3D` + `import RBM3D.Universality.GUEPhase.Eq729B` + `#assert_rbm_axioms`; `reg_base.lean` = the same without the new import; neither is committed)
```
$ lake env lean $SC/reg.lean > $SC/reg.out 2>&1; echo "exit=$?"; head -1 $SC/reg.out; grep -c error $SC/reg.out
exit=0
axiom audit: 10577 theorems, 3085 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
0
$ lake env lean $SC/reg_base.lean > $SC/reg_base.out 2>&1; echo "exit=$?"; diff $SC/reg_base.out $SC/reg.out | grep "^[<>]" | cut -c1-110
exit=0
< axiom audit: 10524 theorems, 3078 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
> axiom audit: 10577 theorems, 3085 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
<   RBM.Gauss.Sizes.STExp2: 18 [no certificate]
>   RBM.Gauss.Sizes.STExp2: 24 [no certificate]
<   RBM.Univ.UNMLOut: 26 [no certificate]
>   RBM.Univ.UNMLOut: 29 [no certificate]
<   RBM.Univ.GUEPhase.GUEPathBounds: 2 [no certificate]
>   RBM.Univ.GUEPhase.GUEPathBounds: 6 [no certificate]
```
**B10 reuse (E4)** the real-variable chain lemmas, the Grönwall/arithmetic ports, `final_729`, `assembly_747`, `STExp2_congr`, `FlowData.ev_eq` (`e4.py`)
```
$ python3 $SC/e4.py
E4 reuse lemmas: 13 of 13 public; statements mentioning UNModel: []
```
**Narrative** (prover `claude-sonnet-5-5`, stage 1b; every number is from B1-B10)
1. Result: `RBM3D/Universality/GUEPhase/Eq729B.lean` has 1674 lines (stop line 2400; sizes at its section commits `eeaf29c d066a24 d7787f6 a396d18 be22099 17adae6 86cc4f2`: 834 1081 1278 1667 1675 1677 1674); the three targets, `Eq729B_goodFlow`, `Eq729B_bridge` and the instances compile; `lake env lean` prints nothing (exit 0); the 56 public declarations depend on the three standard axioms only (B2); the registry pre-check exits 0 and the ledgers change only by `STExp2` 18 → 24, `UNMLOut` 26 → 29, `GUEPathBounds` 2 → 6 theorems resting on them (B9).
2. E3: no cut was taken and no 1b mathematical FAIL occurred. Chain link (i) is `Eq729B_perN` (discrete Grönwall), `Eq729B_gronwall_factor` (`exp((t₀ - t₁)·2NρΛ) ≤ e²` from `h730`, used in `gueGrid_eq729`) and the merged `gueGrid_expect_oneLoop`; (ii) is `Eq729B_arith` with `Eq729B_final_729`; (iii) is `Eq729B_bctl_le_two_calB`, `Eq729B_assembly_747`, `Eq729B_core747`; `PinDerived` is `Eq729B_derived`. All are proved (B2), so no RETURN condition of E3 holds.
3. Statements (B3, B4): each pin of design section 1 (`PinGueGrid729`, `PinEq747OfEq729`, `PinEq747OfInputs`, `PinSTExp2OfUNMLOut`, `PinGoodFlow`, `PinDerived`) is proved by the corresponding theorem of the file, the four vocabulary definitions are defeq to the probe's and the nine real-variable lemmas have identical statements; the negative controls fail. `Eq729B_OUBody` is the body of the merged pin `UNOUEq747` (`Eq729B_ueq747_iff` is `Iff.rfl`).
4. Hypotheses that stay: target 1 takes `hB := sz.STExp2 E t1` and `hP : GUEPathBounds` (pins of ST-6 and UN-49/50/51); targets 2 and 3 take the flow data `(E', t₀, t₁)` of `Eq729B_FlowData` (eventual formulas) and target 3 the `∀ n` facts `hgood` that `Eq729B_goodFlow` supplies (design F2); `Eq729B_bridge` takes `UNMLOut d` and modifies `z_n` at finitely many `n` (`Eq729B_goodFlow_aux`). Target 3 derives `h730`, `hscale`, `hell` (`Eq729B_derived`: all thresholds are `W`-only), `hlam` (from `(eq:WO)`) and `hKb` (`Sizes.stKbound_holds`).
5. Instances (E1, B5): `inst_gueGrid_eq729` discharges every deterministic hypothesis of target 1 at `sz0`, `E = 0`, `τ_U = 1/30`, `n₀ = 3` and the window `0 < t₀ - t₁ = y/N`, `1 - t₀ = y = ilambda²/(2 L³)` (`hKb` by `stKbound_holds`, `Kt` by `gueK_exists` at every `n`); `inst_eq747_of_inputs` does the same for target 3 at the data of `Eq729B_goodFlow`; `inst_derived`, `inst_bridge`, `inst_eq747_of_eq729` use the explicit formulas (`Eq729B_flowData_formulas`, `ζ(t_n) > 0`, so `t₁ < t₀`); `inst_goodFlow`, `inst_claimA`, `inst_hell_of_scales` (`n = 7`, `ζ = N^{-1+τ_U} > 0`), `inst_assembly_747` and the unnamed examples cover the rest. The pins `STExp2`, `GUEPathBounds`, `UNMLOut 3` and, for target 2, `Eq729B_Concl` remain hypotheses; B6 gives their sizes along the sequence.
6. Not instantiated: `Eq729B_perN` (its hypotheses are events of the GUE path), `Eq729B_core747`, `Eq729B_law726`, `Eq729B_transfer`, `Eq729B_avg2_*` (internal lemmas used by the targets). No instance witnesses a conclusion at a fixed `n`: `Eq729B_loss_absorb` needs `12 ≤ N^{𝔠τ/2}`, true eventually (design risk 3).
7. Premise scan: the audit scan of `#assert_rbm_axioms` lists a `Prop`-valued `def`/`structure` that some theorem assumes and no theorem concludes; `Eq729B_FlowData` (three defining equations) is such a structure, so `Eq729B_flowData_formulas` concludes it for the explicit formulas (without that theorem the pre-check printed `1 premise(s) ... [RBM.Univ.GUEPhase.Eq729B_FlowData]` and exit 1).
8. Ports (B8): `Eq729B_perN`, `Eq729B_arith`, `Eq729B_exp_two_lt`, `Eq729B_c_nonneg` are textual ports (token similarity 0.99-1.00); `Eq729B_transfer`, `Eq729B_Bad`, `Eq729B_not_bad`, `gueGrid_eq729` are renamed ports (0.85-0.96); `Eq729B_law726` is a port onto `avg2` of `Gres` (0.77); the rest are merged twins or re-derived. E4: the 13 reuse lemmas are public and state no `UNModel` (B10). E5: no action here.

### (c) Verified Mathlib names (run Fri Oct  9 20:07:49 UTC 2026)
`toks.py` + `resolve.lean` (each identifier token of the code with comments stripped, 782 tokens, resolved by `resolveGlobalName` under the file's `open` lines; the file compiles, so each name exists with the used signature): 118 Mathlib theorem names, one wrapped list:
Complex.conj_conj Complex.im_le_norm Complex.mul_conj Complex.normSq_eq_norm_sq Complex.norm_real Complex.star_def ENNReal.ofReal_add Filter.Eventually.of_forall Filter.eventually_ge_atTop Finset.sum_congr Matrix.conjTranspose_apply
Matrix.conjTranspose_nonsing_inv Matrix.conjTranspose_one Matrix.conjTranspose_smul Matrix.conjTranspose_sub Matrix.ext Matrix.mul_assoc Matrix.nonsing_inv_eq_ringInverse Matrix.smul_apply Matrix.submatrix_apply Matrix.transpose_apply
MeasureTheory.integral_congr_ae MeasureTheory.integral_const_mul MeasureTheory.integral_map MeasureTheory.measure_mono MeasureTheory.measure_union_le Nat.cast_nonneg Nat.cast_succ Nat.cast_zero Real.add_one_le_exp Real.exp_nat_mul
Real.exp_one_lt_d9 Real.exp_pos Real.mul_self_sqrt Real.norm_eq_abs Real.one_le_rpow Real.rpow_add Real.rpow_add' Real.rpow_le_one_of_one_le_of_nonpos Real.rpow_le_rpow Real.rpow_le_rpow_of_exponent_le Real.rpow_mul Real.rpow_natCast
Real.rpow_neg Real.rpow_neg_one Real.rpow_nonneg Real.rpow_one Real.rpow_pos_of_pos Real.sqrt_eq_rpow Real.sqrt_inv Real.sqrt_le_sqrt Real.sqrt_nonneg Real.sqrt_sq abs_nonneg abs_of_nonneg abs_of_pos add_le_add div_eq_mul_inv
div_le_div_iff₀ div_le_div_of_nonneg_left div_le_iff₀ div_le_one div_le_self div_mul_eq_mul_div div_nonneg div_pos inv_anti₀ inv_le_comm₀ inv_le_one_of_one_le₀ inv_mul_le_iff₀ inv_one inv_pow le_div_iff₀ le_mul_of_one_le_left le_of_eq
le_refl le_rfl le_self_pow₀ le_trans lt_min lt_of_le_of_lt lt_of_lt_of_le lt_of_not_ge min_le_left min_le_right mul_add mul_assoc mul_comm mul_div_assoc' mul_le_mul mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_right mul_le_of_le_one_right
mul_nonneg mul_one mul_one_div mul_pos mul_pow mul_sub neg_div norm_mul norm_nonneg one_div one_div_pow one_le_pow₀ one_mul one_pos one_pow pow_add pow_le_pow_left₀ pow_le_pow_right₀ pow_mul' pow_one pow_pos sq_nonneg tendsto_rpow_atTop
zero_add zero_le_one
Verified absent: none sought. Merged RBM3D names used (they elaborate): see B8 (twins) and the imports of B1.

### (d) Open issues and paper-delta candidates
* Paper deltas: no new candidate beyond the numbered ones. D628 (T2356a): (7.29) at `t₀` carries `I₀(t₁)` (`Eq729B_Concl`, `Eq729B_initTerm`); D629 (T2356b): (7.47) as `qdBoundExp` at `η_Q = W^{-𝔡/3} ilambda W^{d/2}/N` with profile `Θ̃_{ζ(t_n)}` (`Eq729B_OUBody` = body of `UNOUEq747`); D630 (T2356c): the `∀ n` facts of `(E', t₀, t₁)` by `Eq729B_goodFlow` and `hgood` in `Eq729B_eq747_of_inputs` (formal); D631 (T2352a): `hell`, `hKb`, `hKinit` of `gueGrid_eq729` as `Hyp_Kt_detDom`.
* Open 1 (UN-51): the consumer builds `Kt` and `hP : GUEPathBounds` for the data of `Eq729B_goodFlow` once (design risk 1; `gueK_exists` needs only `|E| < 2`, `0 ≤ t₁ ≤ t₀ < 1`). Open 2 (E5): the block Anderson kind `UNOUEq747k` needs its own target 3 or the kind's `Eq747k` producer as a premise of `UNG1Rowk`; the 13 lemmas of B10 are public for that reuse.
* Open 3: the instances witness hypotheses only (item 6); the registry ledger counts of B9 grow by the theorems that assume `STExp2`, `UNMLOut`, `GUEPathBounds`; no registry change is requested. Open 4: `Eq729B_FlowData` is a `Prop` structure that the premise scan flags unless a theorem concludes it (item 7): a later file that adds such a vocabulary structure needs the same.
