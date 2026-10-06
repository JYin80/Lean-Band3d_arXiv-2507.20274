Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 10:18:06 UTC 2026

Setting: `d = 3`, `𝔠 = 1/6`, `𝔡 = 1/10`, `κ = 1/2`, `E = 1`, `nf = 2`, `τ = τ_U = 10⁻⁴`, `C₀ = 1`; `c := 2𝔠𝔡` (RBM2D `Uyw_fixed_time` parameter, c9a24cf `Uyw.lean:553`); `N = (WL)^d`; `K := 2d+1 = 7`. Scripts (stdlib Python, no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/{pre,inst,tok}.py`.

### (i) Exponent table
| quantity | value (setting) | constraint | slack |
|---|---|---|---|
| `c = 2𝔠𝔡` | `1/30` | `0 < c ≤ 1` (`c ≤ 1` from `un_cd_le_half`: `𝔠𝔡 ≤ 1/2`, `Jak.lean:451`) | `𝔠𝔡 = 1/60` vs `1/2` |
| `Uyw_o_le` (`c ≤ 1`, was `c ≤ 1/2`) | `E₁ = 1-c/6+2τ+δ = 0.9947` | proof uses only `E₁ ≥ 0` (RBM2D `:118-155`: `f1,f2` use `-c/3 ≤ -c/6`, `2τ ≥ 0`; `hXE` uses `E₁ ≥ 0`); `hc2` is used nowhere else (`grep -n "hc2\b"` at c9a24cf `Uyw.lean:119,497,530,556,809`; math code of the file at c9a24cf equals the RBM2D working copy except the removed `UywCheck` instances, checked by a comment-stripped diff) | `E₁ ≥ 5/6` for any `c ≤ 1`; true for `c < 6` |
| `θ` (good threshold) | `N^{-c/36} = N^{-𝔠𝔡/18}`, `1/1080` | off bad block `‖blockM2‖ < W^{-𝔡/6} ≤ N^{-𝔠𝔡/6} ≤ θ` (`un_W_neg_le` `Pins.lean:929`, `N ≥ 1`) | `𝔠𝔡/6 − 𝔠𝔡/18 = 1/540` |
| window `w'` | `N^{-1+c/6}/2`, `c/6 = 𝔠𝔡/3 = 1/180` | `w'+C₀/N ≤ N^{-1}N^{𝔠𝔡/3} ≤ N^{-1}W^{𝔡/3}`: `2C₀ ≤ N^{c/6}` (ev2), `(N^𝔠)^{𝔡/3} ≤ W^{𝔡/3}` (`Bandwidth`); equals the fixed window of `measure_bad2_le_of_queBadMat` (`UywKernel.lean:1061`) | eventual; ev2 needs `log10 N ≥ 54.19` |
| QUE params `(ε₀, c_Q)` | `(𝔡/3, 𝔡/6)` | `0<ε₀<𝔡/2`, `0<c_Q<ε₀∧𝔡/5` | `c_Q` vs `𝔡/5`: `1/300`; vs `ε₀`: `1/60` |
| `τ_Q` / `queBound` | `𝔡/30`; `-min(2ε₀,2𝔡/5)+2c_Q+τ_Q = -𝔡/30 = -1/300` | `UNOUQUE` is for every `τ_Q>0`; `queBound … = ofReal(W^{-𝔡/30})` (`Uyw_queBound_eq`) | equality |
| `ℙ(Bm a0)` | `≤ K W^{-𝔡/30} ≤ K N^{-𝔠𝔡/30}` | `measure_bad2…` gives `(2d+1)p`; `un_W_neg_le` at `x = 𝔡/30` | — |
| `c'` (pin exponent) | `𝔠𝔡/30 = 1/1800` | `c' ≤ c/36 = 𝔠𝔡/18`; `c' ≤ 2` (crude) | binding term `ℙ(𝓑)`: `c/36 − c' = 1/2700` |
| `δ` | `τ/(nf+5) = 1.43e-5` | `(m+3)δ ≤ τ`, `m = nf ≥ |s|` | `τ−(nf+3)δ = 2.86e-5` |
| `D` (`UNOUDiag` exponent) | `(1+τ)(nf+4)+3 = 9.0006` | `D ≥ (1+τ)(m+4)+3`; crude exponent `(1+τ)(sc+4)+2−D ≤ −1` | equality at `sc = m` |
| `η̃` | `N^{-1+2τ}` | `τ ≤ 1/4` ⇒ `η̃→0` (ev3) | `1−2τ ≥ 1/2` |
| `A_good` | `(193+256/κ²)N^{3−c/36+8τ+2δ}` = `1217·N^{…}` | `Uyw_Ag_le` (RBM2D `:156`): `θ`-term exp `3−c/36+8τ+2δ`; out-terms exp `3−c/6+6τ+2δ` | `2.9951 ≤ 2.9999` |
| `A_bad` | `4N^{3+8τ+2δ}` | `Uyw_Ab_le` (RBM2D `:200`), unchanged | — |
| good total | `a+e−1`, `a=(3τ+δ)sc`, `e=3−c/36+8τ+2δ` | `≤ T−6τ`, `T = 2−c'+(3sc+16)τ`: margin `(c/36−c')+2τ−(sc+2)δ ≥ 0` | `≥ 5.13e-4` (sc=nf) |
| bad total | `a+f+g−1`, `f=3+8τ+2δ`, `g=−c'` | margin `2τ−(sc+2)δ ≥ 0` | `≥ 1.43e-4` (sc=nf) |
| `ev5` | `2(C₁+4K) ≤ N^{6τ}`, `C₁=1217`, `4K=28`, const `2490` (RBM2D `2(C₁+20)`; `d` fixed before `n`) | `(C₁+4K)X^{T−6τ} ≤ ½X^T` | eventual: `log10 N ≥ 5660.33` (binding of ev1-ev5) |
| crude total | `4N^{(1+τ)(sc+4)}·(4+m)N·2N·N^{-D} ≤ 8(4+m)N⁻¹` | `16(4+m) ≤ N` (ev1), `T ≥ 0` (`c' ≤ 2`) | `≤ ½`; at `N*` `10^{-5658.65}` |
| `C`, `τ₀` | `C = 3nf+16 = 22`, `τ₀ = min τ₁ (1/4)` | `|s| ≤ nf` (`N ≥ 1`); `UNOUClaims` gives `τ₁`; `τ_U ≤ 1/4` | — |

Truth of the three private redo statements of the check file, by hand: `Uyw_o_le`: `8/w' = 16N^{1-c/6}`, `8η̃/w'² = 32N^{1+2τ-c/3}`, both with `X^δ` below `N^{E₁}`; `((2^{K'}w')²)⁻¹ ≤ 64/κ²` from `κ/8 < 2^{K'}w'`, and `1 ≤ N^{E₁}`. `Uyw_good_total_le`: margins above (they use `c' ≤ c/36` and `(sc+3)δ ≤ τ`), then `(C₁+4K) ≤ ½X^{6τ}`. `Uyw_crude_total_le`: LHS `= 8(4+m)X^{(1+τ)(sc+4)+2−D} ≤ 8(4+m)X⁻¹ ≤ ½ ≤ ½X^T` (`T ≥ 0` if `c' ≤ 2`; `c'` unused otherwise). Random float check of all three (hypotheses sampled) is the last line of the script output. `Uyw_queBound_eq`: exponent `-2𝔡/5+𝔡/3+𝔡/30 = -𝔡/30` (printed `-1/300`).

Consumer token check and bad-block/grid shapes (`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/tok.py`, reads `Pins.lean`, `Jak.lean`, the check file; `cut -c1-175`):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/tok.py | grep -E '^[0-9]|^   UNOUQUE' | cut -c1-175
1. row: hypotheses/quantifiers identical (prefix after 'def X : Prop :='): True
2. target 3 is `UNJakUywRow` verbatim: True
3. unUyw_of_ouClaims vs unJak_of_ouClaims (UNJak->UNUyw, ':= by' stripped) identical: True
4. UNClaimRow has 'UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)': True ; target 1 conclusion has 'UNUyw sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)': True
5. integrand of UNUyw (renamed Hr ω, z k->w k, z i->u₁, z j->u₂, sz.L n,sz.W n,sz.lam n -> L W lam) == fixed_time integrand: True
6a. hdiag set == UNOUDiag set (renamed): True
6b. hque set == UNOUQUE set: True | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E a (Hr ω) | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)
   UNOUQUE bound: queBound (sz.W n) 𝔡 (𝔡 / 3) (𝔡 / 6) τQ ; fixed_time hque bound: ENNReal.ofReal ((W : ℝ) ^ (-(𝔡 / 30)))  [= queBound W 𝔡 (𝔡/3) (𝔡/6) (𝔡/30) by Uyw_queBound_eq
```
Chain (ii of the ticket): `measure_bad2_le_of_queBadMat` at `P = ouP`, `Hr = ouMat … t`, `lam = sz.lam n`, `a0 = siteBlock d L W y`, `p = ofReal(W^{-𝔡/30})`; `hp` = `UNOUQUE` at `(κ, 𝔡/30)`, energy `E` (same `queBadMat … (𝔡/3) (𝔡/6) E b` set, line 6b); result `≤ (2d+1)p`, `toReal` and `un_W_neg_le` give `≤ (2d+1)N^{-𝔠𝔡/30}`. Both `w'`-windows lie in `N⁻¹W^{𝔡/3}` (row `window w'`). Grid: `UNOUDiag` at `(κ/2, δ, D)`; grid energies `|e| < 2−κ/2` (RBM2D `Uyw_grid_energy_lt` from ev3). `#S ≤ (4+nf)N` (two dyadic families `K'+1 ≤ 2^{K'} ≤ N` each, 2 single-scale, `nf` weights), `≤ 2N` energies each.

### (ii) Concrete nondegenerate instance
Instance of the theorems: `sz0` (`d = 3`, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `Admissible (1/6) (1/10)` is `sz0_admissible`, `Sizes.lean:331`), data above, `t = 0 ≤ t*`; `inst_window`: two distinct points `z 0 = 1 + i/N`, `z 1 = 1 + 1/N + i/N` (`C₀ = 1`).
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/pre.py
cd = 1/60 | c=2cd = 1/30 | cd<=1/2: True | c<=1: True | c'=cd/30 = 1/1800 | c'<=2: True
theta exp c/36 = cd/18 = 1/1080 ; block thr cd/6 = 1/360 ; window w' exp c/6 = cd/3 = 1/180
order c' < c/36 <= cd/6 < cd/3: True ; slack c/36-c' = 1/2700 ; cd/6-c/36 = 1/540
QUE: eps0=dd/3 in (0,dd/2): True | cQ=dd/6<eps0,dd/5: True True | slack to dd/5: 1/300
queBound exp tauQ=dd/30: -min(2dd/3,2dd/5)+2(dd/6)+dd/30 = -1/300  ; -dd/30 = -1/300
delta = tau/(nf+5) = 1.4286e-05 ; (nf+3)delta<=tau: True ; slack tau-(nf+3)delta=2.857e-05 ; D=(1+tau)(nf+4)+3=9.0006
--- good/bad exponents, T=2-c'+(3sc+16)tau, margin vs T-6tau (>=0)
sc=0 good 5.418e-04 bad 1.714e-04 ; closed form good (c/36-c')+2tau-(sc+2)delta=5.418e-04 bad 2tau-(sc+2)delta=1.714e-04
sc=1 good 5.275e-04 bad 1.571e-04 ; closed form good (c/36-c')+2tau-(sc+2)delta=5.275e-04 bad 2tau-(sc+2)delta=1.571e-04
sc=2 good 5.132e-04 bad 1.429e-04 ; closed form good (c/36-c')+2tau-(sc+2)delta=5.132e-04 bad 2tau-(sc+2)delta=1.429e-04
crude exponent (1+tau)(sc+4)+2-D at sc=nf: -1.0  (<=-1) ; T(sc=0)=2.0010 >=0
Uyw_o_le: E1=1-c/6+2tau+delta=0.9947 >=0: True ; out-term exp 3-c/6+6tau+2delta=2.9951 <= Ag exp 3-c/36+8tau+2delta=2.9999: True
   largest c with E1>=0 at tau=delta=0: c<=6 ; hypothesis c<=1 leaves E1>=0.8333
C1=193+256/kappa^2=1217 ; 4(2d+1)=28 ; ev5 const 2(C1+4(2d+1))=2490
log10 N thresholds: ev1 16(4+nf)<=N 1.98 ; ev2 2C0<=N^(c/6) 54.19 ; ev3 1.39 ; ev4 0.61 ; ev5 5660.33 (binding)
at N*=10^5660.33: log10 N^T=11329.97 good 11326.76 bad 11327.21 crude -5658.65 ; (good+bad)/N^T=2.3554e-03 ; (good+bad+crude)/N^T=2.3554e-03 (<=1/2: True)
--- sz0, n=0
L,W,N = 4 32 2097152 N^(1/6)=11.3137<=W: True ; W^(-d/2+dd)=0.007813 <= lam=1/64=0.015625 <= 1/dd=10 ; W^d<N: True ; L>=3
window z0: |Re-E|=0.000e+00<=C0/N=4.768e-07 ; N^(-1-tU)=4.7614e-07<=Im=4.7684e-07<=N^(-1+tU)=4.7753e-07: True
window z1: |Re-E|=4.768e-07<=C0/N=4.768e-07 ; N^(-1-tU)=4.7614e-07<=Im=4.7684e-07<=N^(-1+tU)=4.7753e-07: True
z0 != z1: True ; t*=N^(-1+tU)=4.7753e-07>0 (t=0 ok); |E|=1<=2-kappa=1.5
n=0 window inclusion w'+C0/N=7.353e-07 <= N^-1 W^(dd/3)=5.352e-07 : False (eventual: needs 2C0<=N^(c/6) i.e. log10 N>=54.2; n=0 has log10 N=6.32)
sz0: N_n>=N* once log10(n+1)>=314.1
--- external pins (limits at sz0): bad-block bound (2d+1)W^(-dd/30), W_n=(2(n+1))^5
log10(n+1)=0: log10 W=1.5 log10[(2d+1)W^(-dd/30)]=0.840 ; log10 N^-D(D=9.001)=-56.9
log10(n+1)=1: log10 W=6.5 log10[(2d+1)W^(-dd/30)]=0.823 ; log10 N^-D(D=9.001)=-218.9
log10(n+1)=3: log10 W=16.5 log10[(2d+1)W^(-dd/30)]=0.790 ; log10 N^-D(D=9.001)=-542.9
log10(n+1)=30: log10 W=151.5 log10[(2d+1)W^(-dd/30)]=0.340 ; log10 N^-D(D=9.001)=-4917.2
log10(n+1)=260: log10 W=1301.5 log10[(2d+1)W^(-dd/30)]=-3.493 ; log10 N^-D(D=9.001)=-42179.7
random tests (o_le, good_total_le, crude_total_le) sampled: [13580, 7549, 13291] violations: 0
```
Reading: at `n = 0` (`N = 2097152`): `N^{1/6} = 11.31 ≤ W = 32`, `W^{-d/2+𝔡} = 0.0078 ≤ lam = 1/64 ≤ 10`, `L = 4 ≥ 3`, both window points in `InWindow`, `0 ≠ 1` in `Fin 2`, `0 ≤ t*`. The `False` on the window-inclusion line is the eventual ev2 (needs `log10 N ≥ 54.2`), not a hypothesis of any target (`UNUyw` is `∀ᶠ n`); no witness of a target is taken at an astronomical size, the instances apply the `∀ᶠ`-statements. The deterministic hypotheses of private `Uyw_fixed_time` do hold together at `n = 0` for a larger `τ_U` (allowed: `τ_U ≤ 1/4`):
```
$ python3 /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/inst.py
X=(W L)^d, 3<=L, W>=1                      True
X^cc<=W (Bandwidth)                        True
0<cc, 0<dd, c=2cc*dd, cc*dd<=1/2           True
W^(-d/2+dd)<=lam                           True
0<kap<=2, 0<tau, 0<delta                   True
(m+3)delta<=tau                            True
(1+tau)(m+4)+3<=D                          True
|E|<=2-kap                                 True
16(4+m)<=X                                 True
2C0<=X^(c/6)                               True
C0/X+2X^(-1+2tau)<kap/4                    True
X^(-1+c/6)<kap/2                           True
2((193+256/kap^2)+4(2d+1))<=X^(6tau)       True
values: X=2097152  X^cc=11.314  X^(6tau)=3.037e+09  vs 2490 ; X^(c/6)=1.0842 ; D=10.5000 ; delta=3.5714e-02
u1/w0 |Re-E|=0.000e+00<=C0/X=2.384e-07 ; X^(-1-tau)=1.253e-08<=Im=4.768e-07<=X^(-1+tau)=1.815e-05 : True
u2/w1 |Re-E|=2.384e-07<=C0/X=2.384e-07 ; X^(-1-tau)=1.253e-08<=Im=4.768e-07<=X^(-1+tau)=1.815e-05 : True
all deterministic hypotheses: True
(hdiag, hque are the external probability pins UNOUDiag/UNOUQUE; not asserted at n=0)
```
External hypotheses (TEAM §8 lesson 14): `UNOUQUE`, `UNOUDiag` (target 1, `inst_unUyw`), `UNLocAvgBand`, `UNOUClaims` (targets 2, 3, `inst_row`, `inst_uywRow`) stay hypotheses (pins of other rows). Limits of the bounds they assert at `sz0`: `UNOUDiag`: `N_n^{-D} → 0` (`D = 9.0006`, `N_n = (4(n+1)(2(n+1))^5)^3 → ∞`; printed `log10 N^{-D} = -56.9 … -42179.7`); `UNOUQUE`: `W_n^{-𝔡/15+τ_Q} = W_n^{-1/300} → 0`, `W_n = (2(n+1))^5 → ∞` (printed `log10[(2d+1)W^{-𝔡/30}]` from `0.840` at `n=0` to `-3.493` at `log10(n+1) = 260`: non-trivial only for `log10 W > 253`, consistent with the `∀ᶠ n`). QUE parameter constraints hold with slacks `1/60`, `1/300`, `1/60`. `sz0` reaches `log10 N ≥ 5660.33` at `log10(n+1) ≥ 314.1`.

### Verdicts
- `unUyw_of_ouClaims` (1a): PASS. Exponents close at `c = 2𝔠𝔡`: good `𝔠𝔡/18`, bad `𝔠𝔡/30` (binding), crude `N⁻¹`; `C = 3nf+16`; only constant changes vs RBM2D: `20 → 4(2d+1)` in ev5, `c ≤ 1/2 → c ≤ 1` in `Uyw_o_le`, `c/36 → c'` in good/crude totals. Statement token-identical to `unJak_of_ouClaims` with `UNJak → UNUyw` (line 3).
- `uywRow` (1b): PASS. Hypotheses/quantifiers identical to the first-conjunct form of `UNJakUywRow` (line 1); `τ₀ = min τ₁ (1/4)`.
- `jakUywRow` (1c): PASS. Is `UNJakUywRow` verbatim (line 2); both conjuncts at the common `C = 3nf+16`, `τ₀ = min τ₁ (1/4)` via `unJak_of_ouClaims` and target 1 (no mono lemma needed).
- `Uyw_o_le`, `Uyw_good_total_le`, `Uyw_crude_total_le`, `Uyw_queBound_eq`, `Uyw_fixed_time` (private): PASS (true as stated; integrand and `hdiag`/`hque` sets token-identical to the pins, lines 5, 6a, 6b).
- `inst_row`, `inst_uywRow`, `inst_unUyw`, `inst_window`: PASS (`sz0` admissible; deterministic hypotheses hold at the printed data; pins stay hypotheses).

## (b) Script output — Tue Oct  6 10:29 UTC 2026 (stage 1b; branch `t/T2280`, commit `2ab9373`)

No section (a′): no mistake found in (a). Port source: RBM2D `Universality/Uyw.lean` at `c9a24cf` (1021 lines;
the RBM2D working copy of the same file has 946 lines and the same Lean code, checked below).
```
$ git log -1 --format='%h %an <%ae>' ; git diff --stat main...t/T2280
2ab9373 Jun Yin <321276894+JYin80@users.noreply.github.com>
 RBM3D/Test/Axioms.lean      |   4 +-
 RBM3D/Universality/Uyw.lean | 968 ++++++++++++++++++++++++++++++++++++++++++++
 2 files changed, 969 insertions(+), 3 deletions(-)
$ lake build RBM3D.Universality.Uyw 2>&1 | tail   (long-line linter warnings of the module doc elided)
⚠ [3335/3335] Replayed RBM3D.Universality.Uyw
info: RBM3D/Universality/Uyw.lean:960:0: 'RBM.Univ.unUyw_of_ouClaims' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:961:0: 'RBM.Univ.uywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:962:0: 'RBM.Univ.jakUywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:963:0: 'RBM.Univ.UywInst.inst_row' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:964:0: 'RBM.Univ.UywInst.inst_uywRow' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:965:0: 'RBM.Univ.UywInst.inst_unUyw' depends on axioms: [propext, Classical.choice, Quot.sound]
info: RBM3D/Universality/Uyw.lean:966:0: 'RBM.Univ.UywInst.inst_window' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (3335 jobs).
$ grep -nE "\bsorry\b|\badmit\b|native_decide|^axiom" RBM3D/Universality/Uyw.lean ; echo "grep exit $?"
grep exit 1
```
Full library (root import added temporarily and reverted, as the hub does at merge; `git status --short` afterwards lists only the two files):
```
$ sed -i '' '320a import RBM3D.Universality.Uyw' RBM3D.lean ; lake build   (before the import line: error "premise(s) ... [RBM.Univ.UNJakUywRow]" in none of the registries, because no theorem concluded it)
Build completed successfully (4087 jobs).
$ lake env lean RBM3D.lean   (audit summary, first lines)
axiom audit: 8110 theorems, 2641 definitions, 0 axioms in `RBM` ... All within [propext, Classical.choice, Quot.sound]
premises found by scanning: 156 (borrowed 1, owed 98, structural 40, refuted 6, superseded 11).
registry: 2 borrowed + 147 owed + 103 structural + 7 refuted + 12 superseded
$ owed lines of owedProps: base HEAD~1 / this commit
148
146
$ git diff HEAD~1 HEAD -- RBM3D/Test/Axioms.lean | grep '^[-+]' | cut -c1-170
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNOUClaims, -- bulk universality pin, the two 𝐇_t claims (T2273, UN-21: owed; owner UNOURow)
-   `RBM.Univ.UNUyw, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
+   `RBM.Univ.UNOUClaims, -- bulk universality pin, the two 𝐇_t claims (T2273, UN-21: owed; owner `ouRow_of_pins` (`ZeroModeProfile.lean:719`) + the consumed inputs `UNG1
-   `RBM.Univ.UNJakUywRow, -- bulk universality pin (T2162 portmap P.4; T2174, UN-01: owed)
```
Registry pre-check (CLAUDE.md §20 (2)) as the temporary root import above, not as a separate `import RBM3D` file: `import RBM3D` does not build on the branch without the import (the audit error above), so the check is the full `lake build` with the import added. Owed count 148 -> 146 (-2).

Target statements, extracted by script (python regex on the file):
```
theorem unUyw_of_ouClaims : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE sz 𝔡 τU → UNOUDiag sz τU →
        UNUyw sz E nf τU (3 * (nf : ℝ) + 16) (𝔠 * 𝔡 / 30)
theorem uywRow :
    UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
      ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
        ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)
theorem jakUywRow : UNJakUywRow
```
Statement check against the check file: scratch module = `Uyw.lean` with `private` removed + check sections 2.1, 2.2, 3 + one `example : T2280_x := x` per name
(`/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2280/scratch_check.lean`, 1095 lines):
```
$ lake env lean scratch_check.lean > scratch.out 2>&1 ; echo "exit $?" ; grep -c error scratch.out
exit 0
0
$ grep -n "^example" scratch_check.lean | cut -c1-120
1082:example : T2280_unUyw_of_ouClaims := RBM.Univ.unUyw_of_ouClaims
1083:example : T2280_uywRow := RBM.Univ.uywRow
1084:example : T2280_jakUywRow := RBM.Univ.jakUywRow
1085:example : T2280_inst_row := RBM.Univ.UywInst.inst_row
1086:example : T2280_inst_uywRow := RBM.Univ.UywInst.inst_uywRow
1087:example : T2280_inst_unUyw := RBM.Univ.UywInst.inst_unUyw
1088:example : T2280_inst_window := RBM.Univ.UywInst.inst_window
1089:example : T2280_Uyw_o_le := @RBM.Univ.Uyw_o_le
1090:example : T2280_Uyw_good_total_le := @RBM.Univ.Uyw_good_total_le
1091:example : T2280_Uyw_crude_total_le := @RBM.Univ.Uyw_crude_total_le
1092:example : T2280_Uyw_queBound_eq := RBM.Univ.Uyw_queBound_eq
1093:example : T2280_Uyw_fixed_time := @RBM.Univ.Uyw_fixed_time
```
So the three targets, the four instances and the five private statements (`Uyw_o_le`, `Uyw_good_total_le`, `Uyw_crude_total_le`, `Uyw_queBound_eq`, `Uyw_fixed_time`) elaborate against the check-file statements as the terms `@Uyw_..` / `..` with no change of statement (`Ω : Type` generalised to `Type*`).

Compiled nonempty instances (namespace `RBM.Univ.UywInst`, same file; `sz0`, d = 3, 𝔠 = 1/6, 𝔡 = 1/10, κ = 1/2, E = 1, nf = 2; every deterministic hypothesis discharged: `sz.Admissible` by `UNInst.sz0_adm`, `3 ≤ d`, `|E| ≤ 2 - κ`; the pins `UNLocAvgBand`, `UNOUClaims`, `UNOUQUE`, `UNOUDiag` stay hypotheses):
```
namespace UywInst

theorem inst_row :
    UNLocAvgBand → UNOUClaims →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNJak SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) ∧
          UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun hloc hOU =>
    jakUywRow hloc hOU 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2

theorem inst_uywRow :
    UNLocAvgBand → UNOUClaims →
      ∃ C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
        UNUyw SizesInst.sz0 1 2 τU C ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun hloc hOU =>
    uywRow hloc hOU 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2

/-- `unUyw_of_ouClaims` at `sz0`, `κ = 1/2`, `E = 1`, `nf = 2`, any `τ_U ∈ (0, 1/4]`; the two `𝐇_t` claims
at `τ_U` are hypotheses (pins of other gates). -/
theorem inst_unUyw :
    ∀ τU : ℝ, 0 < τU → τU ≤ 1 / 4 →
      UNOUQUE SizesInst.sz0 (1 / 10) τU → UNOUDiag SizesInst.sz0 τU →
        UNUyw SizesInst.sz0 1 2 τU (3 * ((2 : ℕ) : ℝ) + 16) ((1 / 6 : ℝ) * (1 / 10) / 30) :=
  fun τU hτ hτ4 hQUE hDiag =>
    unUyw_of_ouClaims 3 le_rfl (1 / 6) (1 / 10) SizesInst.sz0 UNInst.sz0_adm (1 / 2) (by norm_num) 1
      (by norm_num) 2 τU hτ hτ4 hQUE hDiag
theorem inst_window :
    ∀ (n : ℕ) (τU : ℝ), 0 < τU →
      ∃ z : Fin 2 → ℂ, (∀ i, InWindow SizesInst.sz0 1 1 τU n (z i)) ∧ z 0 ≠ z 1 ∧
        (0 : Fin 2) ≠ 1 ∧ 0 ≤ ouTStar SizesInst.sz0 τU n := by
  intro n τU hτU
  [proof: two points z 0 = ⟨1, N⁻¹⟩, z 1 = ⟨1 + N⁻¹, N⁻¹⟩ in InWindow sz0 1 1 τU n, z 0 ≠ z 1 (real parts), (0 : Fin 2) ≠ 1 by decide, 0 ≤ ouTStar]
```
Name-clash grep (new public names `unUyw_of_ouClaims uywRow jakUywRow UywInst` against `RBM3D RBM3D.lean` outside the new file, and `Uyw_` prefix; and against `main` 596a83a by `git grep`): all four greps and the `Uyw_` grep print nothing.
```
grep -rnw unUyw_of_ouClaims: 0 hits
grep -rnw uywRow: 0 hits
grep -rnw jakUywRow: 0 hits
grep -rnw UywInst: 0 hits
grep -rn Uyw_: 0 hits
git grep on main:        0 hits
```
Ports (RBM2D read-only; `git -C ../RBM2D --no-optional-locks log -1 --format=%h` = 9e0f275; source commit `c9a24cf`):
```
$ python3 strip.py <c9a24cf Uyw.lean> > a.txt ; python3 strip.py <RBM2D working Uyw.lean> > b.txt ; diff a.txt b.txt   (comments, blanks, UywCheck instances stripped)
807a808
> end RBM.Univ
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Uyw.lean RBM2D/Universality/Jak.lean
 RBM2D/Universality/Jak.lean | 133 ++++++++++-----------------------
 RBM2D/Universality/Uyw.lean | 175 +++++++++++++-------------------------------
 2 files changed, 90 insertions(+), 218 deletions(-)
```
(The RBM2D `Uyw.lean` working copy has no uncommitted change per `git status --short -- RBM2D/Universality/Uyw.lean`; its Lean code equals the code at c9a24cf, first diff above.)
Port map (RBM2D line numbers at c9a24cf; RBM3D file lines): `Uyw_rpow_mul` :81, `_exists_dyadic` :84, `_q_le` :102, `_o_le` :118 (`c ≤ 1/2` -> `c ≤ 1`), `_Ag_le` :156, `_Ab_le` :200, `_prod_row_le` :298, `_prod_crude_le` :318, `_grid_energy_lt` :354: copied; `_good_total_le` :213 and `_crude_total_le` :264 redone with `(c, c', K)` (`5 N^{-c/18}` -> `K N^{-c'}`, `20` -> `4K`, `c' ≤ c/36`, `c' ≤ 2`); `_integral_le_of_majorant` :376 copied; `_measure_grid_fail` :408 with `RBM.green` -> `Gres · · true` (copy of `Jak.lean:408`); `_gSel_eq_Gsig`, `_integrand_eq`, `_c_le_half` dropped (`un_cd_le_half`); `_queBound_eq` new (copy of `Jak_queBound_eq`, `Jak.lean:546`); `_pointwise_good_norm` :494 with `lam`, `d`, `blockM2 d L W lam`, merged `uyw_pointwise_good`; `_fixed_time` :553 rewritten around `measure_bad2_le_of_queBadMat` (template `Jak.lean:561-845`); `Uyw_main` :845 -> `unUyw_of_ouClaims`; `uywRow` :914 and `jakUywRow` :951 (RBM2D `Uyw_jak_mono`, `Uyw_uyw_mono` :926-949 not ported).

Narrative (as filed):
* One new file, 968 lines, 3 public targets, 4 public instances, 16 private lemmas (7 public theorems in all); every public name pinned by the ticket. The first build reported two errors (a set-builder bracket typo, one step of the `inst_window` proof), fixed without any change of a statement.
* Exponent redo at `c = 2𝔠𝔡` as in the ticket and (a): `Uyw_o_le` at `c ≤ 1`; good total with `c' = 𝔠𝔡/30 ≤ c/36 = 𝔠𝔡/18`; bad part `(2d+1)N^{-𝔠𝔡/30}` through `measure_bad2_le_of_queBadMat`, `Uyw_queBound_eq`, `un_W_neg_le`; window `w' + C₀/N ≤ N⁻¹W^{𝔡/3}` from `ev2` and `Bandwidth`; threshold `W^{-𝔡/6} ≤ N^{-𝔠𝔡/6} ≤ θ`.
* `jakUywRow` takes the common `C = 3nf+16`, `τ₀ = min τ₁ (1/4)`; `unJak_of_ouClaims` and `unUyw_of_ouClaims` apply directly (no mono lemma).
* The index `i ≠ j` of `UNUyw` is unused (`_hij`), as in RBM2D.
* Not targets, untouched: `UNUywk`, `UNJakUywRowk`, `UNJakUywRowBA`, `UNClaimRow`, `UNUnivMainRow`; no merged file other than `Test/Axioms.lean` (registry lines only) changed.
* Registry: owed lines `UNUyw` and `UNJakUywRow` deleted; the comment of owed `UNOUClaims` updated as instructed (owner `ouRow_of_pins` + `UNG1Row`, `UNG2bRow`); nothing appended.

## (c) Verified Mathlib / project names used

All names compile in `lake build RBM3D.Universality.Uyw` (checked by the build, not invented): `Real.rpow_add`, `Real.rpow_sub`, `Real.rpow_neg`, `Real.rpow_neg_one`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.one_le_rpow`, `Real.rpow_one`, `pow_unbounded_of_one_lt`, `Nat.find`, `Nat.lt_two_pow_self`, `Nat.ceil_mono`, `Nat.ceil_lt_add_one`, `Finset.card_union_le`, `Finset.prod_le_prod₀`, `measure_biUnion_finset_le`, `measure_toMeasurable`, `subset_toMeasurable`, `integral_undef`, `integral_indicator_one`, `ENNReal.toReal_le_of_le_ofReal`, `ENNReal.ofReal_mul`, `tendsto_rpow_atTop`, `tendsto_rpow_neg_atTop`, `Filter.Tendsto.eventually_lt_const`, `mul_inv_le_iff₀`, `inv_le_comm₀`. Project: `un_cd_le_half`, `unJak_of_ouClaims`, `un_W_neg_le`, `un_que_exponent`, `measure_bad2_le_of_queBadMat`, `uyw_pointwise_good`, `uyw_pointwise_crude`, `blockM2`, `jakGridGood`, `siteBlock`, `scirc`, `Gres`, `UNInst.sz0_adm`. Names verified absent: none searched. Every name above occurs in `Uyw.lean` (grep) and the file builds.

## (d) Open issues and paper-delta candidates

* T2280a (design table, no paper statement), confirmed by the compiled port: `C = 3nf+16`, `τ₀ = min τ₁ (1/4)` at `d ≥ 3` for `UNUyw`; good exponent `𝔠𝔡/18`, bad exponent `𝔠𝔡/30` (`ℙ(𝓑)` binds); only constants change vs RBM2D: `20 -> 4(2d+1)`, `c ≤ 1/2 -> c ≤ 1` in `Uyw_o_le`; row `UNJakUywRow` closes at the common `C`, `τ₀`; registry -2.
* No T2280b: no statement difference found; no step needed a hypothesis the statement lacks.
* Observation: ticket text counts RBM2D `Uyw.lean` at 1021 lines (c9a24cf, true) and (a) used the working copy of 946 lines; the diff above shows the Lean code is identical.
* Observation: module-doc lines exceed 100 characters (11 linter warnings, as in `Jak.lean`); no error.
* Merge note for the hub: root import `import RBM3D.Universality.Uyw` after the last import line (verified: full `lake build` succeeds with it); `Axioms.lean` change is two deleted lines and one comment edit; branch base is 7a8a4eb, main is 596a83a (T2277 merged after the base): the `Axioms.lean` edits are other lines (union).
