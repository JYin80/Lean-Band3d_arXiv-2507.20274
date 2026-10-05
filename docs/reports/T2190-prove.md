Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 15:14:45 UTC 2026

Notation: `a_i=(u_i-z-s m)^{-1}`, `X=N^{-1}Σ|a_i|²`, `σ=s^{-1/2}`, `ref(w)=σ·mref(σ(w+E₀))`, strip `S1={|Re w|≤c₁, c₀t/4≤Im w≤1/2}`,
rectangle `R={|Re ω|≤c₁/2, tc/4≤Im ω≤3/8}`, `F(ω)=iη+t·mV v(ω)`, `ω*=iη+t·ref(iη)`, `r=2t(ε+4LpKt)`. Scripts (scratchpad `T2190/`, Python, not Lean): `a_joint.py b_inst.py c_inst.py d_margins.py e_sweep.py`.

### (i) Exponent table

| Row | Value / identity | Constraint | Slack |
|---|---|---|---|
| T1 identity | `(m-m')(1-sP)=N⁻¹Σa_ia'_i(u'_i-u_i)+(z-z')P`, `P=N⁻¹Σa_ia'_i` (subtract the two equations, `a-a'=aa'[(u'-u)-(z'-z)-s(m'-m)]`) | needs `Im z>0` | — |
| T1 `X` | `Im a_i=(Im z+s Im m)|a_i|²`, so `X=Im m/(Im z+s Im m)`, `sX<1`, `|P|≤√(XX')<1/s` | `s>0`, `Im m>0` | `1-sX=Im z/(Im z+s Im m)>0` |
| T1 real part | `Re(aa')=(|a|²+|a'|²-|a-ā'|²)/2`; `Re(1-sP)≥(s/2)N⁻¹Σ|a-ā'|²≥(s/2)(Im m+Im m')²` (`Im(a-ā')=Im a+Im a'`, `N⁻¹ΣIm a=Im m`, Cauchy–Schwarz) | — | dropped term `1-s(X+X')/2>0` |
| T1 conclusion | `(s/2)(Im m+Im m')²‖m-m'‖ ≤ (r+‖z-z'‖)/s`, i.e. `s²(Im m+Im m')²‖m-m'‖≤2(r+‖z-z'‖)` (constant 2 exact) | `‖N⁻¹Σaa'(u'-u)‖≤r√(XX')<r/s` | sampled max ratio LHS/RHS `0.656` (below) |
| T2 | `‖m‖≤N⁻¹Σ|a_i|≤√X`, `s‖m‖²≤sX=s Im m/(Im z+s Im m)<1`; `s=0` trivial | `0≤s` | sampled max `s‖m‖²=0.982` |
| T3 `C` | `Im m≤‖m‖≤1` (T2 at `s=1`) | `C=1` | — |
| T3 `Lp` | T1 at `s=1,u=u',r=0`, `Im m,Im m'≥c`: `‖m-m'‖≤‖z-z'‖/(2c²)` | `Lp=1/(2c²)` | — |
| T3 modulus | same bound along `η`: `|m(E+iη)-m(E+iη')|≤|η-η'|/(2c²)`, `η,η'∈(0,10]`: Cauchy, limit `ρ_n`; `|Im m/π-ρ_n|≤η/(2πc²)≤η/c²` | window `|x-E|≤δ`, `c≤Im m` eventually | factor `2π` |
| T6 | `m n=msc+1_{Im z<h n}·i/2`: `c=9/100` (`un_dens_msc_zero`), `C=3/2`, Lipschitz unchanged (indicator depends on `Im z` only), limit `rhoSC 0+1/(2π)`, `rhoSC 0=√4/(2π)=1/π` | `h n>0` | — |
| `σ` | `σ-1≤t` for `0<t≤1/2` since `(1+t)²(1-t)=1+t-t²-t³≥1`; `σ²≤2`; use `σ≤1+t≤17/16` (`t≤1/16`) | `s=1-t` | script: `max((1-t)^{-1/2}-1-t)=-5.0e-10<0` |
| `K` vs `c` | `c≤Im mref(E₀+i)≤‖mref‖≤K` (the point `E₀+i` is in the box) | hypotheses of T4 | used inside the proof, `c₀` defined before `mref` |
| `c₁` | `min(δ/(4(1+A)), 1/4)` (ticket: `δ/(4(1+A))`; the cap `1/4` is needed for `Im` upper margin, `δ` large) | `c₁≤δ/(4(1+A))` | — |
| `c₀` | `min(c/64, c/(16KLp), c₁/(4(K+1)))` (ticket list: `c/64, 1/(8Lp), c₁/(4(K+1)), 1/16`) | below; `1/(8Lp)`, `1/16` are implied: `c₀≤c/(16KLp)≤1/(16Lp)`, `c₀≤c₁/8≤1/32` | the new term `c/(16KLp)` is the one missing in the ticket list |
| (a) strip→box | `|Re z-E₀|≤σc₁+tA≤(17/16)(1+A)c₁≤17δ/64`; `Im z≤σ/2≤17/32` | `<δ`, `≤1` | `47δ/64`; `15/32` |
| (b) Cauchy disc | radius `ρ_C=tc/8` about `ω∈R`; `tK≤c₁/4` so `tc/8≤c₁/32`; disc ⊂ S1: `Re:c₁/2+tc/8≤c₁`, `Im low: tc/8≥c₀t/4` iff `c₀≤c/2`, `Im up: 3/8+tc/8≤1/2` | | `c₀≤c/64` vs `c/2`: factor 32; `tc/8≤1/128` vs `1/8` |
| (b) derivative | `h=mV v-mV v(ω)` analytic; `‖h‖≤2ε+2Lpρ_C` on the sphere (`ref` is `σ²Lp≤2Lp`-Lipschitz on S1); `‖deriv mV v(ω)‖≤2ε/ρ_C+2Lp` | | |
| (b) contraction | `t(2ε/ρ_C+2Lp)=16ε/c+2Lp t ≤ 1/4+c/(8K) ≤ 3/8` (`ε≤c/64`, `t≤c/(16KLp)`, `c≤K`) | `≤1/2` | `1/8` (ticket's `1/(8Lp)` gives `1/2`, slack 0) |
| (c) `ω*` | `‖F(ω*)-ω*‖≤t(ε+2Lp·t‖ref(iη)‖)≤t(ε+4LpKt)`; ball radius `r=2t(ε+4LpKt)`; `iη` is in the box (`|Re z-E₀|=(σ-1)|E₀|≤tA`, `Im z≤17/64`) | `r/2+t(ε+4LpKt)=r` | exact |
| (c) ball Im low | `Im ω*≥tσc≥tc`; `r≤tc/32+8LpKt²≤tc/32+tc/2` (`8Lp t≤c/(2K)`) | `r≤3tc/4` | `7tc/32` |
| (c) ball Re / Im up | `(17/16)tK+r≤1.6tK≤0.4c₁`; `1/4+0.4c₁≤0.35` | `≤c₁/2`; `≤3/8` | `0.1c₁`; `0.025` |
| (d) | `‖freeConvST v t(iη)-ref(iη)‖=‖y-ω*‖/t≤2ε+8LpKt`; `‖ref(iη)-mref(E₀+iη)‖≤(σ-1)K+Lp(σ-1)(η+A)≤t(K+Lp(1/4+A))` | `η≤1/4` | |
| `C₀` | `2+K+Lp(8K+1/4+A)` (coefficient of `ε` is `2≤C₀`) | `‖·‖≤C₀(ε+t)` | |
| (e) limit | `y(η)` is `2`-Lipschitz in `η` (`‖y-y'‖≤|η-η'|+½‖y-y'‖`); `freeConvST` is `3/t`-Lipschitz; `mref(E₀+iη)` `Lp`-Lipschitz; `1/π≤1` | | factor `π` |
| T5 | `K=1` (T2, `s=1`), `Lp=1/(2c²)`; `c₀=min(c/64,c³/8,c₁/8)`, `C₀=3+(33/4+A)/(2c²)`, `c₁` as above; depends on `(c,δ,A)` only; `c>1` is vacuous | | `c₀~c³/8`, `C₀~4.1/c²` as `c→0`; `c₁~δ/(4A)`, `C₀` linear in `A` as `A→∞` |
| `u≡0` (band) | T4 gives `C₀(ε+t)`, weaker than `freeConv_stable_local`'s `2ε` | | e.g. (ii-a): `C₀(ε+t)=0.138` vs observed `1e-13` |

Margin script (`d_margins.py`, 400000 log-uniform draws of `(c≤K,Lp,δ,A)`, all margin inequalities of the rows above at `t=ε=c₀`; these are my sufficient conditions, not the theorem):
```
mine violations per constraint: none
ticket violations per constraint: {'ball Im low: r<=3tc/4': 125806, 'ball Im up: 1/4+sig tK+r<=3/8': 19247, 'Cauchy disc Im up: 3/8+tc/8<=1/2': 558}
example ('ticket', 'ball Im low: r<=3tc/4') (c,K,Lp,delta,A,c1,c0)= (1.707e-05, 0.1649, 646.2, 0.00592, 0.0, 0.00148, 2.667e-07)
```
So the ticket's `c₀`/`c₁` list does not close the `Im` margins of the route (b)-(c) for `K≫c` or `δ` large; the replacement above does. The route needs no stronger hypothesis than the box bounds of the pin.

### (ii) One concrete nondegenerate instance

**(ii-0) Target 1, 2 numerically** (`python3 a_joint.py`; `N∈{1..6}` random `u,u'`, `r`, `s∈(0.05,3)`, random `z,z'` with `Im≥0.02`, residual `<1e-10`):
```
target1: max LHS/RHS over 3000 draws = 0.6555480511569182
target2: max s|m|^2 over 3000 draws  = 0.9816725824237236
```
**(ii-a) Target 4, `mref=msc`** (`python3 b_inst.py`): `E₀=0,A=0,δ=1/2,K=1,c=0.58,Lp=1/(2c²)`, `v=√s γ`, `γ` the `N=10^6` semicircle quantiles:
```
grid min Im msc on box |x|<=1/2, 0<eta<=1: 0.5956802658472555  at -0.5 1.0
c=0.58 K=1.0 Lp=1/(2c^2)=1.486326 c1=0.125 c0=9.062500e-03 (c/64=9.062e-03, c/(16KLp)=2.439e-02, c1/(4(K+1))=1.562e-02) C0=15.2622
t=c0=9.062500e-03 s=0.990937500 sigma=1.004562283 sigma-1=4.562e-03 <= t: True; strip bottom c0*t/4=2.0532e-05
closeness: 2060 sample points, sup |m_v - ref| = 3.7390e-12 at w=(0.125+0.5j); eps=sup ; eps <= c0: True
eta=1e-06: |y-omega*|=4.135e-05 (<= r=9.766e-04); |freeConvST-msc(i eta)|=6.4837e-14 (<= C0(eps+t)=1.3831e-01); Im/pi=0.318310 vs 1/pi=0.318310
eta=2e-01: |y-omega*|=3.195e-05 (<= r=9.766e-04); |freeConvST-msc(i eta)|=2.0194e-12 (<= C0(eps+t)=1.3831e-01); Im/pi=0.280998 vs 1/pi=0.318310
```
(Here `v⊞sc_t` is exactly `msc` because `mV v(w)=σ m_γ(σw)`; the observed distance is round-off, the case `u≡0` of the table.)

**(ii-b) Target 5, `u=(1.2,0.6,-0.6,-1.2,-0.6,0.6)` (`0.6·2cos(πk/3)`, `‖u‖∞=1.2`)** (`python3 c_inst.py`): `ν_u=μ_u⊞sc_1`, `E₀=0.3=A`, `δ=1/2`, `c=0.49`, `K=1`,
`Lp=1/(2c²)`, `v=√s γ-E₀`, `γ` the `N=2·10^6` quantiles of `ν_u` (density from `m_{u⊞sc_1}` at `η=10^{-9}`, cdf inverted by interpolation):
```
box grid (4860 pts): max residual 3.56e-16, min Im m_u = 0.49514 at (0.8+1j), max|m_u| = 0.76348 (<= K=1: target 2)
c=0.49 K=1.0 Lp=2.0825 c1=0.09615 c0=7.6562e-03 (c/64=7.656e-03, c/(16KLp)=1.471e-02, c1/(4(K+1))=1.202e-02) C0=20.805
t=c0, s=0.99234375, sigma-1=3.850e-03 <= t: True; strip bottom c0 t/4 = 1.465e-05
closeness: N=2000000, 592 sample points, sup |m_v - ref| = 9.6803e-10 at w=(0.0641025641025641+1.4654541015624999e-05j); <= c0=7.656e-03: True
r=2t(eps+4LpKt)=9.766e-04; Re margin (17/16)tK+r=9.111e-03 <= c1/2=0.0481; Im low r<=3tc/4: 9.77e-04<=2.81e-03; Im up 0.2591<=0.375
eta=1e-06: |y-omega*|=1.080e-05 (<= r=9.77e-04); |freeConvST v t(i eta) - m_u(E0+i eta)| = 2.0225e-03 (<= C0(eps+t)=1.5929e-01); t*U/c^2 scale = 3.827e-02
eta=2e-01: |y-omega*|=7.943e-06 (<= r=9.77e-04); |freeConvST v t(i eta) - m_u(E0+i eta)| = 1.4812e-03 (<= C0(eps+t)=1.5929e-01); t*U/c^2 scale = 3.827e-02
rho(eta=1e-6 proxy) = 0.22522030, rho0 = Im m_u(E0+i1e-6)/pi = 0.22468133, |rho-rho0| = 5.390e-04 <= C0(eps+t) = 1.593e-01
```
(The printed `eta=2e-01` line is `η=0.25`, format `.0e`.) All hypotheses of T4/T5 hold at once: `|E₀|=0.3≤A`, box bounds `c=0.49≤0.495`, `‖m_u‖≤0.763≤1`
(Lipschitz `Lp=1/(2c²)` is T1, not sampled), `0<t=c₀≤c₀`, `s=1-t`, `ε=9.7e-10≤c₀`, closeness on the sampled strip (592 points, not a proof), `c₀≤c₁`.
Limit computation for the closeness hypothesis (external, TEAM §8 lesson 14; `python3 e_sweep.py`, same strip, same sample):
```
N=100000: sup over 592 sampled strip points of |m_v - ref| = 2.064e-01  (<= c0=7.656e-03: False)
N=200000: sup over 592 sampled strip points of |m_v - ref| = 2.413e-02  (<= c0=7.656e-03: False)
N=500000: sup over 592 sampled strip points of |m_v - ref| = 5.326e-05  (<= c0=7.656e-03: True)
N=1000000: sup over 592 sampled strip points of |m_v - ref| = 2.496e-09  (<= c0=7.656e-03: True)
N=2000000: sup over 592 sampled strip points of |m_v - ref| = 9.680e-10  (<= c0=7.656e-03: True)
```
So the closeness hypothesis holds only for `N≳5·10^5` at these constants (as in T2176 (a)(ii-c), `docs/reports/T2176-prove.md:75`); in the Lean example it stays a hypothesis (ticket, DECISIONS §56).

**(ii-c) Ticket's compiled-instance numbers** (`python3 d_margins.py`, last lines): constants of the table at the ticket's data,
```
A: mref=msc, c=9/100, Lp=62: c1=0.125; c0(mine)=9.0726e-05 strip bottom c0^2/4=2.058e-09; c0(ticket list)=1.4062e-03 bottom=4.944e-07
B: u=uI, c=1/20, Lp=200: c1=0.125; c0(mine)=1.5625e-05 strip bottom c0^2/4=6.104e-11; c0(ticket list)=6.2500e-04 bottom=9.766e-08
9/100 - 2e-4/(9/100)^2 = 0.06530864197530864 >= 1/20: True
1/(2c^2) at c=9/100: 61.7283950617284  <= 62: True
```
The ticket's `c≥1/20` for `uI` and `Lp=62` for `msc` hold. The closeness strip at these `c₀` is far below the `N≳5·10^5` resolution of (ii-b), so the example's `hyp` stays a hypothesis, as the ticket says; the nondegenerate witness for T4/T5 is (ii-b) (and (ii-a)). The T3 instance `uI`, `c=1/20`, `δ=1/2` needs no closeness hypothesis.

### Verdicts
- T1 `freeConvST_sub_le`: PASS (identity and both bounds derived above; numerics consistent).
- T2 `freeConvST_norm_sq_le`: PASS.
- T3 `unDens_freeConvST`: PASS (`C=1`, `Lp=1/(2c²)`, modulus `η/(2πc²)≤η/c²`).
- T4 `freeConv_stable_lip`: PASS with the constants `c₁=min(δ/(4(1+A)),1/4)`, `c₀=min(c/64,c/(16KLp),c₁/(4(K+1)))`, `C₀=2+K+Lp(8K+1/4+A)`; the ticket's `c₀`, `c₁` list is insufficient for the margins of (c) (only the existential constants differ from the ticket's list; the statement is unchanged). Needs no hypothesis beyond the pin.
- T5 `freeConv_stable_freeConvST`: PASS (consequence of T4, T1, T2).
- T6 `unDens_not_eta_determined`: PASS.

## (b) Script output — Mon Oct  5 16:01:42 UTC 2026; branch `t/T2190`, worktree `/Users/junyin/Lean_proof/RBM3D-wt/T2190`

```text
$ git log -1 --format='%h %an <%ae> %s'; git diff --stat main...t/T2190
75aa08e Jun Yin <321276894+JYin80@users.noreply.github.com> T2190: UN-07 Universality/FreeConvRegular (free convolution against a regular reference)
 RBM3D/Universality/FreeConvRegular.lean | 1491 +++++++++++++++++++++++++++++++
 1 file changed, 1491 insertions(+)
$ lake build RBM3D.Universality.FreeConvRegular 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.style.longLine false`
Build completed successfully (3336 jobs).
$ lake env lean RBM3D/Universality/FreeConvRegular.lean; echo "exit=$?"   # no warnings, no output
exit=0
$ wc -l RBM3D/Universality/FreeConvRegular.lean; grep -c 'sorry\|admit\|native_decide\|axiom' RBM3D/Universality/FreeConvRegular.lean
    1491 RBM3D/Universality/FreeConvRegular.lean
0
$ lake env lean <scratchpad>/T2190/axioms.lean   # #print axioms: the 6 targets, then 4 theorems of the instance namespace
'RBM.Univ.freeConvST_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConvST_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConv_stable_lip' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.freeConv_stable_freeConvST' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.unDens_not_eta_determined' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.freeConvST_zero_eq_msc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.uI_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.stable_lip_msc' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.FreeConvRegularInst.stable_freeConvST_uI' depends on axioms: [propext, Classical.choice, Quot.sound]
axioms exit=0
$ python3 <scratchpad>/T2190/stmt_diff.py   # target statements vs the `..._stmt` bodies of docs/tickets/checks/T2190-check.lean (whitespace-normalised, Type* -> Type)
freeConvST_sub_le: True; freeConvST_norm_sq_le: True; unDens_freeConvST: True; freeConv_stable_lip: True; freeConv_stable_freeConvST: True; unDens_not_eta_determined: True  =>  ALL IDENTICAL
$ lake env lean <scratchpad>/T2190/stmt_defeq.lean; echo "exit=$?"   # Lean-level check (non-committed): Section 2 of the check file + `example : NAME_stmt := @RBM.Univ.NAME.{0}` for the six targets
exit=0
$ lake env lean <scratchpad>/T2190/stmt_defeq_neg.lean 2>&1 | head -2; ...   # negative control: one extra wrong example `freeConvST_sub_le_stmt := @RBM.Univ.freeConvST_norm_sq_le.{0}`
stmt_defeq_neg.lean:83:36: error: Type mismatch
  @freeConvST_norm_sq_le
exit=1
$ python3 <scratchpad>/T2190/extract_stmts.py   # the six target statements as they stand in the file (whitespace-normalised)
-- freeConvST_sub_le  (FreeConvRegular.lean:298)
theorem freeConvST_sub_le : ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (u u' : ι → ℝ) (r s : ℝ), 0 < s → (∀ i, |u i - u' i| ≤ r) → ∀ z z' : ℂ, 0 < z.im → 0 < z'.im → s ^
    2 * ((freeConvST u s z).im + (freeConvST u' s z').im) ^ 2 * ‖freeConvST u s z - freeConvST u' s z'‖ ≤ 2 * (r + ‖z - z'‖)
-- freeConvST_norm_sq_le  (FreeConvRegular.lean:309)
theorem freeConvST_norm_sq_le : ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (s : ℝ), 0 ≤ s → ∀ z : ℂ, 0 < z.im → s * ‖freeConvST u s z‖ ^ 2 ≤ 1
-- unDens_freeConvST  (FreeConvRegular.lean:387)
theorem unDens_freeConvST : ∀ {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ), 0 < δ → 0 < c → (∀ᶠ n in atTop, ∀ x η : ℝ,
    |x - E| ≤ δ → 0 < η → η ≤ 10 → c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) → ∃ ρ : ℕ → ℝ, UNDens (fun n => freeConvST (u n) 1) E ρ δ ∧ ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η
    ≤ 10 → |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2
-- freeConv_stable_lip  (FreeConvRegular.lean:1234)
theorem freeConv_stable_lip : ∀ c K Lp δ A : ℝ, 0 < c → 0 < K → 0 < Lp → 0 < δ → 0 ≤ A → ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧ ∀ (mref
    : ℂ → ℂ) (E₀ : ℝ), |E₀| ≤ A → (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (mref z).im ∧ ‖mref z‖ ≤ K) → (∀ z z' : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im
    ≤ 1 → |z'.re - E₀| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mref z - mref z'‖ ≤ Lp * ‖z - z'‖) → ∀ {n : Type*} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t
    ≤ c₀ → s = 1 - t → 0 ≤ ε → ε ≤ c₀ → (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 → ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mref ((Real.sqrt s : ℂ)⁻¹ * (w +
    E₀))‖ ≤ ε) → ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧ Tendsto (fun η : ℝ => (mref ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0)
    (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (ε + t) ∧ ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤ C₀ * (ε + t)
-- freeConv_stable_freeConvST  (FreeConvRegular.lean:1262)
theorem freeConv_stable_freeConvST : ∀ c δ A : ℝ, 0 < c → 0 < δ → 0 ≤ A → ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧ ∀ {ι : Type*} [Fintype
    ι] [Nonempty ι] (u : ι → ℝ) (E₀ : ℝ), |E₀| ≤ A → (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (freeConvST u 1 z).im) → ∀ {n : Type*} [Fintype n]
    [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t → 0 ≤ ε → ε ≤ c₀ → (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 → ‖mV v w -
    (Real.sqrt s : ℂ)⁻¹ * freeConvST u 1 ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) → ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝
    ρ) ∧ Tendsto (fun η : ℝ => (freeConvST u 1 ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (ε + t) ∧ ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v t ⟨0,
    η⟩ - freeConvST u 1 ⟨E₀, η⟩‖ ≤ C₀ * (ε + t)
-- unDens_not_eta_determined  (FreeConvRegular.lean:470)
theorem unDens_not_eta_determined : ∀ h : ℕ → ℝ, (∀ n, 0 < h n) → ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧ (∀ n (z : ℂ), h n ≤ z.im → m n z = msc z) ∧ ∀
    n, ρ n = rhoSC 0 + 1 / (2 * Real.pi)
$ python3 <scratchpad>/T2190/extract_inst.py   # the compiled nonempty instances (namespace RBM.Univ.FreeConvRegularInst): statement, and proof when short
-- FreeConvRegular.lean:1311-1325  (14 proof lines)
theorem freeConvST_zero_eq_msc {ι : Type*} [Fintype ι] [Nonempty ι] {z : ℂ} (hz : 0 < z.im) : freeConvST (fun _ : ι => (0 : ℝ)) 1 z = msc z
-- FreeConvRegular.lean:1328-1330  (2 proof lines)
example : (∀ z : ℂ, 0 < z.im → freeConvST (fun _ : Fin 1 => (0 : ℝ)) 1 z = msc z) ∧ (∀ z : ℂ, 0 < z.im → freeConvST (fun _ : Fin 2 => (0 : ℝ)) 1 z = msc z)
  := ⟨fun _ hz => freeConvST_zero_eq_msc hz, fun _ hz => freeConvST_zero_eq_msc hz⟩
-- FreeConvRegular.lean:1333-1340  (3 proof lines)
example : (1 : ℝ) ^ 2 * ((freeConvST (![-1, 1] : Fin 2 → ℝ) 1 Complex.I).im + (freeConvST (![-1, 1 / 2] : Fin 2 → ℝ) 1 (1 + Complex.I)).im) ^ 2 * ‖freeConvST (![-1, 1] : Fin 2 → ℝ) 1 Complex.I - freeConvST
    (![-1, 1 / 2] : Fin 2 → ℝ) 1 (1 + Complex.I)‖ ≤ 2 * ((1 / 2 : ℝ) + ‖(Complex.I : ℂ) - (1 + Complex.I)‖)
  := freeConvST_sub_le (![-1, 1] : Fin 2 → ℝ) (![-1, 1 / 2] : Fin 2 → ℝ) (1 / 2) 1 one_pos (by intro i; fin_cases i <;> norm_num) Complex.I (1 + Complex.I) (by simp) (by simp)
-- FreeConvRegular.lean:1343-1345  (3 proof lines)
example : (1 / 2 : ℝ) * ‖freeConvST (![-1, 0, 1] : Fin 3 → ℝ) (1 / 2) (Complex.I / 10)‖ ^ 2 ≤ 1
  := freeConvST_norm_sq_le (![-1, 0, 1] : Fin 3 → ℝ) (1 / 2) (by norm_num) (Complex.I / 10) (by simp)
-- FreeConvRegular.lean:1348-1348  (1 proof lines)
def uI : Fin 2 → ℝ
  := ![-1 / 10000, 1 / 10000]
-- FreeConvRegular.lean:1353-1376  (23 proof lines)
theorem uI_lower {z : ℂ} (hre : |z.re| ≤ 1 / 2) (hz : 0 < z.im) (hz10 : z.im ≤ 10) : 1 / 20 ≤ (freeConvST uI 1 z).im
-- FreeConvRegular.lean:1380-1386  (5 proof lines)
example : ∃ ρ : ℕ → ℝ, UNDens (fun _ : ℕ => freeConvST uI 1) 0 ρ (1 / 2) ∧ ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 → |(freeConvST uI 1 ⟨0, η⟩).im / Real.pi - ρ n| ≤ η / (1 / 20 : ℝ) ^ 2
-- FreeConvRegular.lean:1394-1421  (18 proof lines)
theorem stable_lip_msc : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧ ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ), (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im → w.im
    ≤ 1 / 2 → ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ * msc ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) → ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝
    ρ) ∧ Tendsto (fun η : ℝ => (msc ⟨((0 : ℝ)), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧ ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v c₀ ⟨0, η⟩ - msc ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2
    + c₀)
-- FreeConvRegular.lean:1424-1436  (Fin 3 corollary of the instance above: same statement with `∀ v : Fin 3 → ℝ`, proof `exact ⟨c₀, c₁, C₀, h0, h1, h2, h3, fun v hv => H v hv⟩`)
-- FreeConvRegular.lean:1441-1458  (7 proof lines)
theorem stable_freeConvST_uI : ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ (1 / 2 : ℝ) / (4 * (1 + 0)) ∧ 0 < C₀ ∧ ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ), (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * c₀ / 4 ≤ w.im →
    w.im ≤ 1 / 2 → ‖mV v w - (Real.sqrt (1 - c₀) : ℂ)⁻¹ * freeConvST uI 1 ((Real.sqrt (1 - c₀) : ℂ)⁻¹ * (w + ((0 : ℝ) : ℂ)))‖ ≤ c₀ / 2) → ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v c₀ ⟨0, η⟩).im /
    Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧ Tendsto (fun η : ℝ => (freeConvST uI 1 ⟨(0 : ℝ), η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧ |ρ - ρ₀| ≤ C₀ * (c₀ / 2 + c₀) ∧ ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v c₀ ⟨0, η⟩ -
    freeConvST uI 1 ⟨(0 : ℝ), η⟩‖ ≤ C₀ * (c₀ / 2 + c₀)
-- FreeConvRegular.lean:1461-1473  (Fin 3 corollary of the instance above: same statement with `∀ v : Fin 3 → ℝ`, proof `exact ⟨c₀, c₁, C₀, h0, h1, h2, h3, fun v hv => H v hv⟩`)
-- FreeConvRegular.lean:1478-1487  (8 proof lines)
example : ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧ UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1 / 2) ∧ (∀ (n : ℕ) (z : ℂ), 1 / ((n : ℝ) + 1) ≤ z.im → m n z = msc z) ∧ ρ 0 ≠ rhoSC 0
$ lake env lean <scratchpad>/T2190/precheck.lean   # registry pre-check: `import RBM3D`, `import RBM3D.Universality.FreeConvRegular`, `#assert_rbm_axioms` (non-committed file)
axiom audit: 5548 theorems, 1978 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext, Classical.choice, Quot.sound]; no project axioms: what the paper cites rather  ...
... [the report is 219 lines in total (the standard ledger listing); rest omitted] ...
exit=0; lines mentioning FreeConvRegular: 0; new registry lines: 0 (RBM3D/Test/Axioms.lean untouched)
$ lake build   # whole library (root RBM3D.lean does not import the new module; the pre-check above does)
Build completed successfully (3993 jobs).
$ for n in NAMES; do git grep -nw -e $n main -- RBM3D RBM3D.lean | wc -l; grep -rnw -e $n docs/tickets (excluding T2190.md and T2190-check.lean) | wc -l; done   # in /Users/junyin/Lean_proof/RBM3D at main = 6f8b2e2
name: hits in RBM3D/ at main / hits in docs/tickets:  freeConvST_sub_le: 0/0; freeConvST_norm_sq_le: 0/0; unDens_freeConvST: 0/0; freeConv_stable_lip: 0/0; freeConv_stable_freeConvST: 0/0;
unDens_not_eta_determined: 0/0; FreeConvRegularInst: 0/0; stable_lip_msc: 0/0; stable_freeConvST_uI: 0/0; freeConvST_zero_eq_msc: 0/0; uI_lower: 0/0; uI: 0/0; FreeConvRegular: 0/0
$ ports: no file of ../RBM1D or ../RBM2D was read or copied for this ticket (no diff-stat applies); the adapted private lemmas are RBM3D's own (T2176):
52c856e T2176: merge UN-06 Universality/FreeConv + FreeConvStability
$ python3 <scratchpad>/T2190/consts.py   # the constants of the three private defs (lines 1149-1156 of the file) at the instance data and at extreme inputs
private def FreeConvRegular_c₁ (δ A : ℝ) : ℝ := min (δ / (4 * (1 + A))) (1 / 8)
private def FreeConvRegular_c₀ (c K Lp δ A : ℝ) : ℝ :=
  min (min (c / 64) (c / (16 * K * Lp))) (FreeConvRegular_c₁ δ A / (8 * (K + 1)))
private def FreeConvRegular_C₀ (K Lp A : ℝ) : ℝ := 2 + 8 * Lp * K + K + Lp * (A + 1 / 4)
case                                                               c1           c0           C0  c0/(c^3/8)    C0*c^2
msc instance (c,K,Lp,delta,A)=(9/100,1,62,1/2,0)           1.2500e-01   9.0726e-05     514.5000      0.9956    4.1674
uI instance  (c,K,Lp,delta,A)=(1/20,1,200,1/2,0)           1.2500e-01   1.5625e-05    1653.0000      1.0000    4.1325
c=1/10, Lp=1/(2c^2)                                        1.2500e-01   1.2500e-04     415.5000      1.0000    4.1550
c=1/100, Lp=1/(2c^2)                                       1.2500e-01   1.2500e-07   41253.0000      1.0000    4.1253
c=1/1000, Lp=1/(2c^2)                                      1.2500e-01   1.2500e-10 4125003.0000      1.0000    4.1250
A=10  (c=1/20,Lp=200)                                      1.1364e-02   1.5625e-05    3653.0000      1.0000    9.1325
A=100 (c=1/20,Lp=200)                                      1.2376e-03   1.5625e-05   21653.0000      1.0000   54.1325
freeConv_stable_local (band, kappa=1): c0 = min(kappa,1)/240 = 4.1667e-03, C0 = 2
```

### Narrative (facts; the evidence is the script output above)
1. All six targets are proved in one new file, `RBM3D/Universality/FreeConvRegular.lean` (1491 lines, commit 75aa08e); the statements equal the check-file bodies except `Type` → `Type*` (no
   hypothesis added or weakened); only the three standard axioms; no `sorry`/`admit`/`native_decide`/`axiom`; `RBM3D/Test/Axioms.lean` untouched (pre-check exit 0, nothing listed; the one
   `Prop`-valued declaration is the private structure `FreeConvRegular_Par`, a bundle of hypotheses of private lemmas, outside the `RBM` scan).
2. Layout (file lines): §1 `:70` one-point facts (`N Im m = (Im z + s Im m) Σ|a_i|²`, `s Σ|a_i|² ≤ N`, `N|m|² ≤ Σ|a_i|²`) and the two-point identity `(m − m')(N − sP) = Q + (z − z')P` give
   targets 1, 2; §2 `:320` generic helpers (limit along `η ↓ 0` from a Lipschitz bound); §3 `:382` target 3 (`ρ_n = limUnder` of `Im m_n(E + iη)/π`, `C = 1`, `Lp = 1/(2c²)`); §4 `:464`
   target 6; §5 `:506` targets 4, 5; §6 `:1291` instances.
3. Target 4 follows the ticket's route: the Cauchy estimate on discs of radius `tc/8` uses only `‖m_v ζ − m_v ω‖ ≤ 2ε + 2Lp·tc/8` (no analyticity of `mref`), so `t·m_v` is `1/2`-Lipschitz on
   `|Re| ≤ c₁/2`, `tc/4 ≤ Im ≤ 3/8` when `16ε/c + 2Lp t ≤ 1/2`; Banach on the ball of radius `2t(ε + 4LpKt)` about `iη + t·ref(iη)`; identification with `freeConvST` by the uniqueness half
   of `freeConv_existsUnique`; fixed points `2`-Lipschitz in `η`; `‖ref(iη) − mref(E₀ + iη)‖ ≤ t(K + Lp(A + 1/4))`; `c ≤ K` is derived from the box hypothesis at `E₀ + i`.
4. Constants (the last command of (b) prints them): `c₁ = min(δ/(4(1+A)), 1/8)`, `c₀ = min(c/64, c/(16KLp), c₁/(8(K+1)))`, `C₀ = 2 + 8LpK + K + Lp(A + 1/4)`. (a) lists the cap `1/4` and
   `c₁/(4(K+1))`; the terms `c/64`, `c/(16KLp)` and `C₀` are (a)'s. The halved cap and denominator are slack for the cruder Lean bounds `‖ref‖ ≤ 2K`, `σ ≤ 65/64`; they are existential
   witnesses, the statement is unchanged and (a)'s verdict is not affected, so there is no (a′).
5. Instances: the closeness hypothesis on the strip stays a hypothesis (ticket; DECISIONS §56), every other hypothesis is discharged. `stable_lip_msc` and `stable_freeConvST_uI` quantify
   over every index type `n : Type` and `v : n → ℝ` (a generalisation of the ticket's `Fin 3`, so the hypothesis is not refuted at one small `n`; (a)(ii-b) needs `N ≳ 5·10^5` already at `c₀
   = 7.66e-3`, and the instance constants (last command of (b)) are smaller, (a)(ii-c)); the `Fin 3` corollaries asked by the ticket are the examples at `:1424`, `:1461`. The bound `1/20`
   for `uI` is target 1 against `0 ⊞ sc_1 = msc` (bridge `freeConvST_zero_eq_msc`, any index type) and `un_msc_im_ge` (`9/100`); `un_dens_msc_zero` hides its constants in `∃ c C Lp`, so it
   is used for target 6 (proof and example) only.
6. Extreme inputs (same command): `c → 0`: `c₀ = c³/8` (ratio 1.0000), `C₀c² → 4.125`, i.e. `C₀ ~ c^{-2}`, `1/c₀ ~ 8c^{-3}`; `A` large: `c₁ ≈ δ/(4A)`, `C₀` linear in `A`, `c₀` unchanged at
   `A = 10, 100` (the term `c/(16KLp)` binds); band `u ≡ 0`: `C₀(ε + t)` with `C₀ = 514.5` at the `msc` instance against `2ε` of `freeConv_stable_local` (`c₀ = 1/240`, `C₀ = 2`): weaker, as
   the ticket says.
7. Ports and names: no RBM1D/RBM2D file was read or copied; the adapted private lemmas are RBM3D's own (T2176, `52c856e`), listed with file:line in the module docstring. Every helper is
   `private` with the prefix `FreeConvRegular_`, except the instance-namespace declarations `FreeConvRegularInst.{freeConvST_zero_eq_msc, uI, uI_lower, stable_lip_msc, stable_freeConvST_uI}`
   (namespace per the ticket).

## (c) Verified Mathlib names (`names.lean`: constants used by the new declarations ∩ names written in the file, module from the environment; `absent.lean`: `env.find?` and the deprecation attribute)
Complex.norm_deriv_le_of_forall_mem_sphere_norm_le  [Mathlib.Analysis.Complex.Liouville]
Convex.norm_image_sub_le_of_norm_deriv_le  [Mathlib.Analysis.Calculus.MeanValue]
ContractingWith.exists_fixedPoint'  [Mathlib.Topology.MetricSpace.Contracting]
DifferentiableOn.diffContOnCl_ball  [Mathlib.Analysis.Calculus.DiffContOnCl]
deriv_sub_const  [Mathlib.Analysis.Calculus.Deriv.Add]
sq_sum_le_card_mul_sum_sq  [Mathlib.Algebra.Order.Chebyshev]
tendsto_nhds_limUnder  [Mathlib.Topology.Basic]
LipschitzWith.of_dist_le_mul  [Mathlib.Topology.MetricSpace.Lipschitz]
present, same check: IsClosed.isComplete, Metric.cauchy_iff, CompleteSpace.complete, le_of_tendsto, Ioo_mem_nhdsGT, Ioc_mem_nhdsGT, Filter.Tendsto.congr', Filter.Tendsto.div_const,
Filter.Eventually.exists, ExistsUnique.unique, Finset.sum_le_sum, norm_sum_le, DifferentiableAt.sub_const, DifferentiableAt.fun_sum, DifferentiableAt.inv, Complex.im_ofReal_mul, Complex.re_ofReal_mul,
Complex.inv_im, Complex.normSq_inv, Complex.im_sum, Complex.re_sum, Complex.sq_norm, Complex.re_le_norm, Complex.im_le_norm, Complex.abs_re_le_norm, Complex.abs_im_le_norm, Complex.ofReal_inv,
Complex.normSq_apply, Real.le_sqrt_of_sq_le, Real.sqrt_le_one, inv_anti₀, inv_le_iff_one_le_mul₀, inv_mul_cancel_left₀, mul_inv_cancel_left₀, Real.pi_gt_three, div_le_self
`absent.lean` output: Finset.sq_sum_le_card_mul_sum_sq: ABSENT; sq_sum_le_card_mul_sum_sq: present; Filter.Tendsto.limUnder_eq: present; if_true: present (DEPRECATED); ite_true: present.  So `Finset.sq_sum_le_card_mul_sum_sq` does not exist: the lemma is the root-namespace `sq_sum_le_card_mul_sum_sq`, whose module `RBM3D.Universality.FreeConvStability` does not import (the file adds `import Mathlib.Algebra.Order.Chebyshev`); `ite_true` replaces the deprecated `if_true`.

## (d) Open issues and paper-delta candidates
- d.1 The closeness hypothesis of targets 4–5 has no Lean witness (ticket, DECISIONS §56); (a)(ii-b) is a numerical witness at its own data (`c = 0.49`, `c₀ = 7.66e-3`, `N`-point quantiles
  with `N ≥ 5·10^5`); the instance constants (last command of (b)) are smaller, so they need a larger `N` (a)(ii-c).
- d.2 **T2190a** (finding; compiled part = target 6 and its example): two `UNDens` data `(m, ρ)`, `(msc, ρ_sc(0))` agree on `Im z ≥ 1/(n+1)` while `ρ 0 = ρ_sc(0) + 1/(2π) ≠ ρ_sc(0)`, so the
  limit `ρ_n` of the merged pin `UNDens` is not determined by `m_n` at heights `Im z ≥ h_n` (any `h_n > 0`); `UNTrLocal` sees `m_n` only at `Im z ≥ N^{-1+ε}`. Target 3 shows data of the form
  `m_{u_n ⊞ sc_1}` (the ticket: the form of the block Anderson density) with `Im ≥ c` satisfy `UNDens` and the extra uniform modulus `η/c²`. NOT compiled or examined here: the ticket's
  claims that `UNStep1Good` and `UNCore` as pinned contradict the band rows `UNTrLocalBandRow`, `UNNormBandRow` (the dispatcher's argument). D-item for the dispatcher (outside this ticket):
  primed successors of `UNDens`, `UNStep1Good`, `UNCore` (CLAUDE.md §5.3).
- d.3 **T2190b** (paper-delta candidate, design): `paper/tex/7_8_light_weight.tex:1835` says the delocalization, QUE and "the bulk universality \eqref{eq:universality} then follow as
  consequences, as shown in \Cref{subsec:main}" (quoted from the TeX); against `m(·, λ)` instead of `msc` the Step 1 stability carries the `O(t*)` term of targets 4–5, `C₀(ε + t)` with `C₀`
  a function of `(c, K, Lp, δ, A)` only (ticket: a variant of T2173c). No other Lean/paper statement difference: targets 1–6 are new mathematics without a paper statement.
- d.4 Consumer note for UN-12 (not checked here): target 4 needs `t ≤ c₀`, `ε ≤ c₀` with `c₀` fixed before `v, t, ε`, and closeness down to `Im w = c₀ t/4`, i.e. `UNTrLocal` at heights `≳
  N^{-1+ε'}` with `ε' < τ_s`.
