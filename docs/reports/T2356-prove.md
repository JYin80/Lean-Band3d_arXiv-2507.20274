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

### (b) Script output — Fri Oct  9 02:10:07 UTC 2026 (the scripts `chain2.py twins.py tokens.py rows.py decls.py extract.py echo_cites.py` are in the scratchpad subdirectory `T2356/`, not in the repository; their output is in `docs/reports/T2356-design.md` sections 4-6 and 8)
**B1 build** (stage 1a: the probe is on branch `t/T2356`, never in the library, so the acceptance command is `lake env lean`; the second command below is the cached re-run of `lake build` of the module)
```
$ cd /Users/junyin/Lean_proof/RBM3D-wt/T2356 && lake env lean RBM3D/Probe/T2356Pins.lean; echo "exit=$?"; wc -l RBM3D/Probe/T2356Pins.lean
exit=0
     398 RBM3D/Probe/T2356Pins.lean
$ touch RBM3D/Probe/T2356Pins.lean; lake build RBM3D.Probe.T2356Pins 2>&1 | grep -n "T2356Pins"; lake build RBM3D.Probe.T2356Pins 2>&1 | tail -1
Build completed successfully (3818 jobs).
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Probe/T2356Pins.lean
0
$ git log -1 --format=%h; git status --short | wc -l; git diff --stat main...t/T2356
fe9888f
       0
 RBM3D/Probe/T2356Pins.lean | 398 +++++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 398 insertions(+)
```
**B2 axioms** of the 16 declarations of the probe (`#print axioms` in a copy of the probe with the 16 lines appended)
```
ueq747_iff : [propext, Classical.choice, Quot.sound]
STExp2_congr : [propext, Classical.choice, Quot.sound]
FlowData.ev_eq : [propext, Classical.choice, Quot.sound]
goodFlow_aux : [propext, Classical.choice, Quot.sound]
goodFlow : [propext, Classical.choice, Quot.sound]
bridge : [propext, Classical.choice, Quot.sound]
bctl_le_two_calB : [propext, Classical.choice, Quot.sound]
Ld_mul_etaQ : [propext, Classical.choice, Quot.sound]
hell_of_scales : [propext, Classical.choice, Quot.sound]
claimA : [propext, Classical.choice, Quot.sound]
h730_hscale_real : [propext, Classical.choice, Quot.sound]
qdBoundExp_eq : [propext, Classical.choice, Quot.sound]
assembly_747 : [propext, Classical.choice, Quot.sound]
final_729 : [propext, Classical.choice, Quot.sound]
gronwall_factor : [propext, Classical.choice, Quot.sound]
pin3_of_pins : [propext, Classical.choice, Quot.sound]
```
**B3 statements**, extracted from the probe by `extract.py` (`lines: text`; pins and `Eq729Concl` in full, theorems up to `:=`)
```
53-55: def Eq729Concl (sz : Sizes d) (E t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) : Prop := ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ₂ : Bool) (a b : Zd d (sz.L n)), eqErr sz E t1 t0 K n σ₂ a b ≤ Nsz sz n ^ δ * ((gueScale sz E n (t0 n))⁻¹ ^ 3 + initTerm sz n (t1 n))
85-98: def PinGueGrid729 : Prop := ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ τU Λ : ℝ}, 0 < κ → 0 < τU → ∀ n0 : ℕ, 3 ≤ n0 → ∀ {E t1 t0 : ℕ → ℝ}, Tendsto sz.size atTop atTop → (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) → (∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E n) (t0 n)) → (∀ᶠ n in atTop, (gueScale sz E n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)) → (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2) → sz.STKbound E → ∀ Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ, (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E n) (t1 n) σ a) → (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) → (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E n)) (t1 n) s σ₁ σ₂ a b) → sz.STExp2 E t1 → GUEPathBounds sz E t1 t0 (gueGridK sz n0) n0 Kt → Eq729Concl sz E t1 t0 (gueGridK sz n0)
102-105: def PinEq747OfEq729 : Prop := ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {κ : ℝ}, 0 < κ → ∀ {E t : ℕ → ℝ}, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → ∀ {E' t0 t1 : ℕ → ℝ}, FlowData sz 𝔡 E t E' t0 t1 → ∀ {K : ℕ → ℕ}, (∀ n, K n ≠ 0) → Eq729Concl sz E' t1 t0 K → ∀ τ : ℝ, 0 < τ → OUBody sz 𝔡 E t τ
109-119: def PinEq747OfInputs : Prop := ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {κ τU : ℝ}, 0 < κ → 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → ∀ n0 : ℕ, 3 ≤ n0 → ∀ {E t : ℕ → ℝ}, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ {E' t0 t1 : ℕ → ℝ}, FlowData sz 𝔡 E t E' t0 t1 → (∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1) → ∀ Kt : ∀ n, ℝ → RBM.Loop.LoopIdx (Zd d (sz.L n)) → ℂ, (∀ n {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), Kt n (t1 n) (loopOf σ a) = sz.STKloop n (E' n) (t1 n) σ a) → (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : RBM.Loop.LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 → HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s) → (∀ n, ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUE d (sz.L n) (sz.W n) (sz.lam n) (mSigma (E' n)) (t1 n) s σ₁ σ₂ a b) → sz.STExp2 E' t1 → GUEPathBounds sz E' t1 t0 (gueGridK sz n0) n0 Kt → ∀ τ : ℝ, 0 < τ → OUBody sz 𝔡 E t τ
123-125: def PinSTExp2OfUNMLOut : Prop := ∀ {d : ℕ}, UNMLOut d → 3 ≤ d → ∀ sz : Sizes d, ∀ {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {κ : ℝ}, 0 < κ → ∀ {E t : ℕ → ℝ}, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → ∀ {E' t0 t1 : ℕ → ℝ}, FlowData sz 𝔡 E t E' t0 t1 → sz.STExp2 E' t1
128-130: def PinGoodFlow : Prop := ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {κ : ℝ}, 0 < κ → ∀ {E t : ℕ → ℝ}, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n) → ∃ E' t0 t1 : ℕ → ℝ, FlowData sz 𝔡 E t E' t0 t1 ∧ ∀ n, |E' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ t0 n ∧ t0 n < 1
376-381: def PinDerived : Prop := ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {κ τU : ℝ}, 0 < κ → 0 < τU → τU ≤ ouTauMax 𝔠 𝔡 → ∀ {E t : ℕ → ℝ}, (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ {E' t0 t1 : ℕ → ℝ}, FlowData sz 𝔡 E t E' t0 t1 → (∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaT (E' n) (t0 n)) ∧ (∀ᶠ n in atTop, (gueScale sz E' n (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU)) ∧ (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ sz.lam n ^ 2)
75-77: theorem ueq747_iff (sz : Sizes d) (𝔡 τU : ℝ) : UNOUEq747 sz 𝔡 τU ↔ ∀ κ : ℝ, 0 < κ → ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) → ∀ τ : ℝ, 0 < τ → OUBody sz 𝔡 E t τ := Iff.rfl
148-175: theorem goodFlow_aux (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E t : ℕ → ℝ} (hE : ∀ n, |E n| ≤ 2 - κ) (ht : ∀ n, 0 ≤ t n) : ∃ (ε : ℝ) (z' : ℕ → ℂ) (t1 : ℕ → ℝ), 0 < ε ∧ STFlow sz κ ε 𝔠 𝔡 z' ∧ FlowData sz 𝔡 E t (STflowE z') (fun n => lemT (z' n)) t1 ∧ ∀ n, |STflowE z' n| ≤ 2 - κ ∧ 0 ≤ t1 n ∧ t1 n ≤ lemT (z' n) ∧ lemT (z' n) < 1 
177-180: theorem goodFlow : PinGoodFlow 
182-187: theorem bridge : PinSTExp2OfUNMLOut 
384-393: theorem pin3_of_pins (P1 : PinGueGrid729) (P2 : PinEq747OfEq729) (P5 : PinDerived) : PinEq747OfInputs 
192-212: theorem bctl_le_two_calB (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {t η : ℝ} (hη : 0 < η) (h2 : η ≤ 2 * (1 - t)) : sz.Bctl n t ≤ 2 * calB sz n η 0 
215-234: theorem Ld_mul_etaQ (sz : Sizes d) (n : ℕ) (𝔡 : ℝ) : ((sz.L n : ℕ) : ℝ) ^ d * ouEtaQ sz 𝔡 n * ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) = sz.lam n * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) 
238-275: theorem hell_of_scales (sz : Sizes d) (n : ℕ) {𝔡 c τU ζ t0 : ℝ} (hc : 0 < c) (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) (h1t : 1 - t0 ≤ ouEtaQ sz 𝔡 n / c) (hζ : 0 ≤ ζ) (hζN : ζ ≤ Nsz sz n ^ (-1 + τU)) (ht01 : t0 ≤ 1) (hc4 : 2 / c ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3)) (hN : 2 * Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡)) : ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ζ) * t0) ≤ sz.lam n ^ 2 
279-302: theorem claimA (sz : Sizes d) (n : ℕ) {𝔠 𝔡 τU : ℝ} (h𝔡 : 0 < 𝔡) (hτU : τU ≤ 𝔠 * 𝔡 / 12) (hNW : Nsz sz n ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (h4 : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2)) (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) : 4 * Nsz sz n ^ (2 * τU) ≤ Nsz sz n * ouEtaQ sz 𝔡 n 
305-319: theorem h730_hscale_real {N ηQ s ζt τU : ℝ} (hN : 1 ≤ N) (hτ : 0 < τU) (hη : 0 < ηQ) (hs : 1 / 4 ≤ s) (hA : 4 * N ^ (2 * τU) ≤ N * ηQ) (hζ : ζt ≤ N ^ (-1 + τU)) : ζt ≤ N ^ (-τU) * (s * ηQ) ∧ (N * (s * ηQ))⁻¹ ≤ N ^ (-τU) 
322-324: theorem qdBoundExp_eq (sz : Sizes d) (n : ℕ) (τ η : ℝ) : qdBoundExp sz n τ η = ((sz.W n : ℕ) : ℝ) ^ τ * (calB sz n η 0 ^ 2 * ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + calB sz n η 0)) 
328-356: theorem assembly_747 {t0 N ηQ B X Bt M Wt : ℝ} (ht0 : 1 / 16 ≤ t0) (ht01 : t0 ≤ 1) (hN : 0 < N) (hη : 0 < ηQ) (hB : (N * ηQ)⁻¹ ≤ B) (hX : 0 ≤ X) (hBt0 : 0 ≤ Bt) (hBt : Bt ≤ 2 * B) (hM : 0 ≤ M) (hW : 12 * M ≤ Wt) : t0 * (M * ((N * (Real.sqrt t0 * ηQ))⁻¹ ^ 3 + Bt ^ 2 * (X + Bt))) ≤ Wt * (B ^ 2 * (X + B)) 
359-361: theorem final_729 {E ρ I0 Λ3 Kc : ℝ} (hρ : 0 ≤ ρ) (hI : 0 ≤ I0) (hΛ : 0 ≤ Λ3) (he : Real.exp E ≤ 7.4) (harith : Real.exp E * (ρ * Λ3 + Kc) ≤ 56 * ρ * Λ3) : Real.exp E * (ρ * I0 + Kc) ≤ 56 * ρ * (Λ3 + I0) 
364-370: theorem gronwall_factor {N η dt M ρ : ℝ} (hN : 0 < N) (hη : 0 < η) (hρ0 : 0 ≤ ρ) (h730 : dt ≤ M * η) (hρ : ρ * M ≤ 1) : Real.exp (dt * (2 * N * (ρ * (N * η)⁻¹))) ≤ Real.exp 2 
```
**B4 instance and name checks** (instance: `d = 3`, `n = 0`, `sz0`: `L = 4`, `W = 32`, `ilambda = 1/64`, `N = 2097152`, `η_Q = 1 - t₁ = 2^{-18}`; no `hell` is needed)
```
/-- Instance (`d = 3`, `n = 0`, `sz0`: `L = 4`, `W = 32`, `ilambda = 1/64`, `N = 2097152`, `η_Q = 1 - t₁ = 2^{-18}`). -/
example : SizesInst.sz0.Bctl 0 (1 - 1 / 262144) ≤ 2 * calB SizesInst.sz0 0 (1 / 262144) 0 :=
  bctl_le_two_calB SizesInst.sz0 0 (by norm_num) (by norm_num) (by norm_num)
$ lake env lean chk_mathlib.lean 2>&1 | grep -c error; wc -l < names_mathlib.txt   # chk_mathlib.lean = import RBM3D.Universality.GUEPhase.HypA + one `#check @NAME` per name of names_mathlib.txt
0
      48
$ for n in <the 28 names of the MISS list>; do grep -rnE "^\s*(private |noncomputable |protected )*(theorem|lemma|def|abbrev|structure|inductive) +([A-Za-z0-9_.]*\.)?$n( |$|\()" RBM3D --include="*.lean" | grep -v "^RBM3D/Probe/" | wc -l; done
Kbound_prec_uncond:0 Kcal:0 Kgen:0 Mt:0 Par:0 mSig:0 kloop_Mt_eq:0 scaleM:0 MLExpConcl:0 expLoopErr:0 ZRescale_lemT_pos:0 ZRescale_blockMat_mul:0 ZRescale_gsig_block:0 ZRescale_trace_block:0 ZRescale_blockMat_Epaper:0 ZRescale_rpow_neg_half:0 GoodEvent_measurable_gloop:0 GoodEvent_gridTime_zero:0 Gsig_true:0 Gsig_conjTranspose:0 gloop_two:0 trGEGEmat:0 profileTilde:0 Meta:0 ellz:0 mSC:0 eq_inv_sqrt_mul_spectralZ:0 zztE_quant:0 
```
The evaluations of the other lemmas at `d = 3, 4` (`n ∈ {0, 10, 2100, 10⁶}`, hypotheses `H` and conclusions `C`, no violation of `H ⇒ C`) are `docs/reports/T2356-design.md` B1; instances of the three targets are a stage-1b deliverable (design section 6).
**B5 name clash and ports** (run Fri Oct  9 02:10:07 UTC 2026)
```
$ grep -rnE "\b(gueGrid_eq729|Eq729B_eq747_of_eq729|Eq729B_eq747_of_inputs|Eq729BInst|Eq729B_[A-Za-z0-9_]*)\b" RBM3D RBM3D.lean --include="*.lean" | grep -v "^RBM3D/Probe/" | cut -c1-110
RBM3D/Universality/GUEPhase/Eq729A.lean:15:`gueGrid_eq729`) is UN-47 `Eq729B`.
$ (the same at declaration level) grep -rnE "^\s*(private |noncomputable )*(theorem|lemma|def|abbrev|structure|instance) +(RBM\.Univ\.GUEPhase\.)?(gueGrid_eq729|Eq729B_[A-Za-z0-9_]*|Eq729BInst[A-Za-z0-9_.]*)" RBM3D --include="*.lean" | wc -l
       0
$ ls RBM3D/Universality/GUEPhase/Eq729B.lean
ls: RBM3D/Universality/GUEPhase/Eq729B.lean: No such file or directory
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat 9e0f275 HEAD -- RBM2D/Universality/GUEPhase/Eq729B.lean | wc -l
       0
$ git -C ../RBM2D --no-optional-locks status --short -- RBM2D/Universality/GUEPhase/Eq729B.lean | wc -l
       0
(the one hit of the first grep is the docstring of Eq729A.lean:15, not a declaration; the source is unchanged since 9e0f275; no RBM2D proof text was copied at stage 1a: the pins are statements rewritten under the port map)
```
**Narrative** (prover `claude-sonnet-5-5`)
1. Stage 1a only (CONTROL H146): the deliverables are the probe `RBM3D/Probe/T2356Pins.lean` (398 lines, limit 400, commit `fe9888f`; `lake env lean` exit 0, no output; `lake build RBM3D.Probe.T2356Pins` after the last edit printed `✔ [3818/3818] Built RBM3D.Probe.T2356Pins (5.3s)` and no warning for the probe; the 16 declarations of B2 depend on the three standard axioms only) and `docs/reports/T2356-design.md` (items (1)-(6), verdict PASS). `RBM3D/Universality/GUEPhase/Eq729B.lean` was not written.
2. The probe has five parts: the vocabulary (`FlowData`, `initTerm`, `eqErr`, `Eq729Concl`, `OUBody`; `ueq747_iff` shows by `Iff.rfl` that `OUBody` is the body of the merged pin `UNOUEq747`); the Prop pins of the three targets and of the bridge (probe 85-130, statements only); `goodFlow` and `bridge`, proved (probe 132-187); nine real-variable lemmas of the exponent chain (probe 189-371); the pin `PinDerived` and `pin3_of_pins` (target 3 from targets 1 and 2 and the derived inputs, probe 373-393) with one example.
3. The chain lemmas are stated over `Sizes`, `calB`, `Bctl`, `ouEtaQ`, so that they are reused as they are in stage 1b; `Eq729B_arith` (RBM2D `:368`, `N`-only) is not re-proved: `final_729` takes its conclusion as hypothesis `harith`.
4. No RBM2D proof text was copied at this stage; RBM2D was read only (B5: `git status` of the source file empty, diff-stat 0 lines).
5. The statements and the numbers (the table of sizes, the twin table, the token table) are in the design report; its findings F1-F4 correct readings of (a) and of the ticket (see (a′)).
6. The stop rule of the ticket (probe over 400 lines: commit, stop, RETURN) was respected: the probe is 398 lines; the design report is within its limit.

### (c) Verified Mathlib names (run Fri Oct  9 02:10:07 UTC 2026)
48 names (B4: `#check @NAME` each, 0 errors): `Real.exp_le_exp` `Real.exp_pos` `Real.mul_self_sqrt` `Real.rpow_add` `Real.rpow_le_rpow` `Real.rpow_le_rpow_of_exponent_le` `Real.rpow_mul` `Real.rpow_natCast` `Real.rpow_neg` `Real.rpow_neg_one` `Real.rpow_nonneg` `Real.rpow_pos_of_pos` `Real.sqrt_pos` `Real.sqrt_le_sqrt` `Real.sqrt_sq` `Filter.Eventually.of_forall` `abs_nonneg` `abs_of_pos` `add_le_add` `div_le_iff₀` `le_div_iff₀` `div_mul_eq_mul_div` `inv_anti₀` `inv_le_comm₀` `inv_mul_le_iff₀` `inv_nonneg` `inv_pos` `inv_one` `le_trans` `lt_min` `lt_of_lt_of_le` `min_le_left` `min_le_right` `mul_add` `mul_le_mul_of_nonneg_left` `mul_le_mul_of_nonneg_right` `mul_nonneg` `mul_one` `mul_pos` `mul_pow` `neg_div` `one_pos` `one_pow` `pow_add` `pow_pos` `sq_nonneg` `zero_add` `Nat.cast_zero`.
Merged RBM3D names used (they elaborate in the probe, B1): `Sizes.stKbound_holds` (`Loop/KLFinal.lean:243`), `Sizes.tendsto_size` (`Defs/StochDomAt.lean:735`), `queDomain` (`Main/QUEFromQDiff.lean:91`), `locDomain_nonempty`, `locDomain_im_pos` (`Endpoints.lean:486, 481`), `lemma28_quant` (`Defs/Semicircle.lean:359`), `lemT_pos`, `lemT_lt_one`, `ZeroModeProfile_ouZeta_nonneg`, `ZeroModeProfile_ouZeta_le_one`, `gueGridK_ne_zero`, `SizesInst.sz0`.
Verified absent from RBM3D (B4, declaration-level grep, 0 each): `Kbound_prec_uncond` `Kcal` `Kgen` `Mt` `Par` `mSig` `kloop_Mt_eq` `scaleM` `MLExpConcl` `expLoopErr` `ZRescale_*` (6) `GoodEvent_*` (2) `Gsig_true` `Gsig_conjTranspose` `gloop_two` `trGEGEmat` `profileTilde` `Meta` `ellz` `mSC` `eq_inv_sqrt_mul_spectralZ` `zztE_quant`; twins in the design report section 4.

### (d) Open issues and paper-delta candidates
* Open issues: (1) targets 1 and 3 keep the `∀ n` hypotheses and the consumer uses `goodFlow` (design F2, open question 1); (2) `goodFlow` and `bridge` in `Eq729B.lean` or in UN-51 (47 proved lines); (3) the import of `HypA` (it imports `Proc`); (4) one row (central 1687 lines) with the pre-named cut at `:784` as fallback; (5) the block Anderson kind `UNOUEq747k` needs its own target 3. All five are in `docs/reports/T2356-design.md` section 7 for the REQ to the supervisor.
* Paper-delta candidates (temporary tags; the dispatcher numbers them): `T2356a` (7.29) at `t₀` carries the initial term `I₀(t₁)`: `N^δ[(Nη_{t₀})^{-3} + I₀(t₁)]` for `N^δ(Nη_{t₀})^{-3}` ([YY_25] (7.29); RBM2D `Eq729B.lean:531`; `1_2:1281`); `T2356b` (7.47): `W^δ Meta^{-3}` ↦ `W^τ𝓑²((ilambda²W^d)^{-1/5} + 𝓑)` at `η_Q = W^{-𝔡/3} ilambda W^{d/2}/N`, profile `Θ̃_{ζ(t_n)}` of the OU matrix (`1_2:504-512`, merged `UNOUEq747`); `T2356c` the `∀ n` facts replaced by data good for every `n` (formal, not a paper difference); `hell`, `hKb`, `hKinit` forms are T2352a.
