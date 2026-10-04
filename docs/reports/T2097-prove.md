Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 01:49 UTC 2026

Sources: RBM2D `c9a24cf` (line numbers below are those of `git show c9a24cf:RBM2D/Path/<file>`), RBM3D `main` files named, paper `paper/tex/3_5_Loop_Hierarchy.tex` (cited `3_5:line`).

### (i) Table of every `W²` / `Z2` / d = 2 occurrence and its d ≥ 3 replacement

| # | d = 2 occurrence (c9a24cf) | d ≥ 3 replacement | why it holds | slack / status |
|---|---|---|---|---|
| 1 | `Z2 L` (lines containing it: UBounds 100, UTransport 58, KellStar 11); `SB L`, `Theta L`, `ukerMat L`, `Uop L` | `Zd d L`; `SB d L g`, `Theta d L g`, `ukerMat d L g`, `Uop d L g` (`Path/Kernel.lean:46,51`) | UBounds uses only `Theta_eq_tsum`, `norm_Theta_le`, `Theta_sub_Theta`, `‖SB‖=1`, `S1=1`, entries of `SB`; the merged `Block.lean:108,136`, `Props4.lean:118,218`, `Deriv.lean:57` give them for every `d`, real `g`, `3 ≤ L` | no constraint on `g`, `d`; `g` becomes an explicit parameter (`g = sz.lam n`) |
| 2 | UBounds:157-163, `SB_realNonneg`: "`sbKernel` is `1/5`" (`(5:ℝ)⁻¹`) | entries `a=(1+2dg²)⁻¹` (diagonal), `g²a` (the `2d` neighbours), else `0`: nonneg by `sbKernelR_nonneg` (`Block.lean:88`), `sbKernel_eq_ofReal` | `a>0`, `g²a≥0`; row sum `a+2d·g²a=1` (`sum_SB_row`, `Block.lean:108`, needs `3 ≤ L` for `2d` distinct neighbours) | exact (equality); `1/5 = 1/(1+2dg²)` only at `d=2,g=1` |
| 3 | constants `1` (`sumNdecay`), `4` (`uopBack`), `3` (`uopOneStep`) | unchanged | `sumNdecay`: row `ℓ¹` norm = row sum `(1-vξ)/(1-wξ)` (nonneg kernel `ukerNonneg` UBounds:424 + `ukerRowSum` :445), squared by two slots; `uopBack`: `1+(t-u)‖ξ‖/(1-u‖ξ‖) ≤ 2`, so `2²`; `uopOneStep`: `Δ(Δβ²+Δβ²)+Δ²β² = 3Δ²β²`, `β=(1-u-Δ)⁻¹` | all dimension-free; equality attained (instance: `A≡1` gives `4.000000 = 4.000000`) |
| 4 | `normSqSpectralMOne` (:416), `etaT E v/etaT E w = (1-v)/(1-w)` | `Complex.normSq (mE E)=1` for `|E|≤2` (`norm_spectralM`, `FlowCalculus.lean:96`); `etaT E t=(1-t)(mE E).im` (`GLoop.lean:75`), ratio `ScaleFacts.lean:342` (needs `(mE E).im>0`, `|E|<2`) | `d`-free; `ξ=|m|²=1` so `Uop … 1` | `sumNdecayEta` window: `0 ≤ v ≤ w < 1` (DECISIONS §29: no `w=1`, `v≥0`) |
| 5 | UTransport `L²` (lines 58, 72, 80, 139, 146, 183, 185, 223, 248, 250, 311, 326, 521): `card (Z2 L) = L²` (`ZMod.card`, `Fintype.card_prod`, :146) | `L^d = card (Zd d L)` (`card_Zd`, `Lattice.lean:67`): `uopLocalMax`: `2 L^d W^{-D'} r α`; `uopPairLocalMax`: `4 L^d W^{-D'} r³ α`; `tailtoTail` hypothesis `4 L^d W^{-D'} ≤ W^{-D}` | the far sum `Σ_c k(c)·1[far] ≤ #{c}·δ` is an exact count; `L²` is the d = 2 count and is not implied | instance below: RHS `19.98` (`L^d=27`) vs `9.33` (with `L²`); LHS `6.58` |
| 6 | `zdist2 L (a-b)` (lines containing it: UTransport 47, KellStar 11) | `zdistInf d L (a-b)` (`Sizes.lean:115`; ST1-COMMON item 3); triangle `|a₁-a₂| ≤ |a₁-b₁|+|b₁-b₂|+|a₂-b₂|` (UTransport:344-349) holds for the sup of coordinatewise `zdist` | sup of coordinatewise triangle; `‖` symmetric `zdist L (-u)=zdist L u` | none needed |
| 7 | `W²` in `KellStar`: `hN : 1 ≤ W²(L²(1-u))` (:149, with `hNeq : N = W²L²` :341, `hBW: ((W L)²)^c ≤ W` :145), prefactor `((1-u)ℓ_u²)⁻¹ ≤ W²` (:177), `1+log L ≤ 1+log W/(2c)` (:164-170), constant `180·40002²(1+log L)`, `20000` (:69) | `Θ` bound from `Prop5Decay d Λ` (`Propagator/Pins.lean:35`; **proved**: `prop5Decay_holds`, `Prop5Hold.lean:784`): `‖Θ_u(0,a)‖ ≤ C B_{u,|a|₁} e^{-c|a|₁/ℓ_u}`, `∃ C,c>0` (depend on `d,Λ`), `0<g≤Λ`, `m=1`. No `log L` factor at `d≥3`. Prefactor: `B_{u,0} ≤ (g²+1-u)⁻¹+(L^d(1-u))⁻¹ ≤ 2(1-u)⁻¹ ≤ 2N^{1-τ}` (`RangeCond τ`, `Green/Pins.lean:55`) `≤ 2W^{(1-τ)/𝔠}` (`Bandwidth 𝔠`: `N^𝔠 ≤ W`, `Sizes.lean:168`, `N=(WL)^d` `Sizes.lean:157`) | closure `2C W^{(1-τ)/𝔠} e^{-cδ(log W)^{3/2}} ≤ W^{-D}` ⇔ `cδ (log W)^{1/2} ≥ (1-τ)/𝔠 + D + log(2C)/log W`; `|a-b|₁ ≥ |a-b|_∞ ≥ δℓ*` gives `e^{-c|a|₁/ℓ} ≤ e^{-c|a|_∞/ℓ}` (only this direction used) | slack: any power of `log W` above `1` suffices (`3/2` leaves `(log W)^{1/2}→∞`, `W→∞` from `Bandwidth` + `SizeTendsto`); **new hypothesis**: `0<lam n ≤ Λ` eventually (take `sz.WO 𝔡`, `Λ=𝔡⁻¹`, `Sizes.lean:164`), absent in RBM2D |
| 8 | KellStar `kellStar_uker_offdiag` (:219): `u·ukerMat 1 s u (a,b) = (u-s)Θ_u(a,b)` for `a≠b` | unchanged (from `(1-uS)Θ_u=1`) | `d`-free; `u=0` case `ukerMat 1 0 0 = Θ_0` | none |
| 9 | UTransport `scaleM L W E t = W²ℓ_t²η_t` (Scales:44), `tailT = M_s⁻² e^{-√(r/ℓ_s)} + W^{-D}` (Scales:48), `ellStar = (log W)^{3/2}ℓ_t` (Scales:52), `ellT = min(1/√(1-u),L)` (`g=1`) | `ellT L g t=min(max(g/√|1-t|,1),L)` (`Params.lean:32`), `tailT d L g t r = B_{t,r}e^{-√(r/ℓ_t)}`, `B_{t,r}=(g²+|1-t|)⁻¹(r+1)^{-(d-2)}+(L^d|1-t|)⁻¹` (`Tail.lean:44,48`), `tailW` (`Tail.lean:52`) | amplitude is `∝ η⁻²` in d = 2 and `∝ θ_t⁻¹`, `θ_t=g²+1-t`, `∝ η⁻¹` at `d≥3` | **does not close, see row 10** |
| 10 | the d = 2 closure `hid` (UTransport:499-503): `r² M_s⁻² = (ℓ_t/ℓ_s)⁴ M_t⁻²`, `r=η_s/η_t=ρ_η`, absorbed by `uT_scalar` (`ρ⁴e^{-√((d-ℓ*/2)/ℓ_s)} ≤ 30000e^Y e^{-√(d/ℓ_t)}`) | needs `ρ_η² B_{s}/B_{t} ≲ ρ_ℓ⁴`, `ρ_ℓ=ℓ_t/ℓ_s`. With `B∝θ⁻¹` the factor is `ρ_η²θ_t/θ_s`: is compensated by the exponential only when `ℓ_s<ℓ_t` (`ℓ_t/ℓ_s` large) | regime (a) `1-t ≥ g²` (the paper's own hypothesis, `3_5:2351`): `ℓ_s=ℓ_t=1`, no exponential gain, ratio `≈ρ_η`; regime (b) `1-t ≤ g²/L²`: `ℓ_t=L`, zero-mode term `(L^d(1-t))⁻¹` gives growth `∝ρ_η`, linear in `L` at `d=3` (numerics) | numbers in (ii) part C: ratio `53.6` at `ρ_η=50` (a); `8.6e6` at `ρ_η=5e5` (b); **FAIL** |
| 11 | `uT_scalar` constants (`Y=(log W)^{3/4}`, `Y≥2`, `30000`) (:441-452) | unchanged | calculus only: `x⁸e^{-(7Y/10)x} ≤ 8!/(7/5)⁸` | `8!/(7/5)⁸=2732.10 ≤ 30000` (slack `×10.98`); `Y≥2` from `4 ≤ log W` (`W ≥ 55`: `e⁴=54.6`; `(log 55)^{3/4}=2.83`) |

Rows to drop (proposal; ticket: "port the rest, say which you drop"): `KpmBoundProp5`, `kpmBoundProp5` (ticket: superseded by `STK2decay`); `ThetaMaxNorm`, `thetaMaxNorm` (KellStar:46,280: constant `180·40002²(1+log L)` and `scaleM`, d = 2 only; `P.1` row 24 lists only `kellStarEv` as consumed). `EKSumNdecay` (`Evolution/Pins.lean:64`, proved by `ekSumNdecay_holds`, general `n`, any `m`) is not a hypothesis of any c9a24cf statement in these three files; `sumNdecay` stays an independent port.

### (ii) One concrete nondegenerate instance (numbers) and script

Part A (`d=3, L=3, W=2`, `g=1/2`, `E=0`, `ξ=|m|²=1`, `v=u=1/2`, `w=t=3/4`): `sumNdecayEta` both sides with `A≡1` and with a random `|A|≤1`; Part B `uopLocalMax` with `R=1`, `D'=3.7569` (`W^{-D'}=` largest off-diagonal entry, so `UkerFar` holds with a nonempty far set), `A=β=1` on the near set `{a}` (size 1) and `α=2` elsewhere, `a=((0,0,0),(0,1,2))`, second slot at `zdistInf=1`. Part C: `tailtoTail`-type ratio at `d=3`, exact `U`, `A=T_s(|b₁-b₂|)≥0`, `a=(0, r e₁)`.

Command: `cd scratchpad/T2097 && python3 chk.py && python3 chk2.py && python3 chk3.py` (numpy; `chk*.py` build `S`, `U=(1-vS)(1-wS)⁻¹` from the definitions of `sbKernel`, `Theta`, `ukerMat`, `Uop`, `etaT`, `zdistInf`).

```
n=L^d= 27  row sums S: 0.9999999999999999 1.0000000000000002  |m|^2= 1.0
min entry U= 0.010973379394432032  row sum range 1.9999999999999998 2.000000000000002  (1-v)/(1-w)= 2.0
sumNdecayEta A=1 : max_a |Uop A|=4.000000  <=  (eta_v/eta_w)^2*alpha=4.000000 True
sumNdecayEta A=random,|A|<=1 : max_a |Uop A|=1.434462  <=  (eta_v/eta_w)^2*alpha=4.000000 True
max offdiag |U_ab|= 0.07396870554765309 diag 1.190408453566349
R=1, far set = pairs with zdistInf>=1 nonempty: True  D'=3.7569 W^-D'=0.073969
UkerFar holds: True
near set size 1 (hyp |A b|<=beta on near, <=alpha everywhere: ok)
uopLocalMax: |Uop A (a)|=6.582928 <= r^2 beta + 2 L^d W^-D' r alpha = 19.977240 True
   same with L^2 in place of L^d: RHS=9.325747
g=0.01 1-t=0.01 1-s=0.5: ell_s=1.000 ell_t=1.000 rho_eta=50.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['53.62', '51.37', '50.94']
g=0.01 1-t=0.01 1-s=0.1: ell_s=1.000 ell_t=1.000 rho_eta=10.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['10.67', '10.25', '10.17']
g=0.01 1-t=0.01 1-s=0.02: ell_s=1.000 ell_t=1.000 rho_eta=2.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['2.08', '2.03', '2.02']
g=1 1-t=0.01 1-s=0.5: ell_s=1.414 ell_t=8.000 rho_eta=50.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['248.64', '374.95', '494.18']
g=1 1-t=0.01 1-s=0.1: ell_s=3.162 ell_t=8.000 rho_eta=10.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['22.64', '33.56', '43.81']
g=1 1-t=0.01 1-s=0.02: ell_s=7.071 ell_t=8.000 rho_eta=2.0  ratio (UxU T_s)(a)/T_t(r), r=1,2,3: ['2.10', '2.65', '3.17']
g=1 L=8 1-s=0.5 1-t=0.01 rho_eta=50 ell_t=8.00 ratio r=1,3: ['248.6', '494.2']
g=1 L=8 1-s=0.5 1-t=0.001 rho_eta=500 ell_t=8.00 ratio r=1,3: ['6857.4', '9888.4']
g=1 L=8 1-s=0.5 1-t=0.0001 rho_eta=5000 ell_t=8.00 ratio r=1,3: ['83941.9', '110112.3']
g=1 L=8 1-s=0.5 1-t=1e-06 rho_eta=500000 ell_t=8.00 ratio r=1,3: ['8606838.9', '11150720.6']
d=3 g=1 L=4 1-s=0.5 1-t=1e-6 (rho_eta=5e+05): ratio r=2 = 3.875e+06 ; ratio/rho_eta = 7.75
d=3 g=1 L=6 1-s=0.5 1-t=1e-6 (rho_eta=5e+05): ratio r=2 = 6.749e+06 ; ratio/rho_eta = 13.50
d=3 g=1 L=8 1-s=0.5 1-t=1e-6 (rho_eta=5e+05): ratio r=2 = 9.965e+06 ; ratio/rho_eta = 19.93
d=3 g=1 L=10 1-s=0.5 1-t=1e-6 (rho_eta=5e+05): ratio r=2 = 1.332e+07 ; ratio/rho_eta = 26.64
```

Reading of the output (script values only): every hypothesis of `sumNdecayEta`, `uopLocalMax` holds at this instance (no `N=0`, `27` points, far and near sets nonempty, `r=2`, `α=2≠β=1`), and both conclusions hold (`4.0 ≤ 4.0`; `6.58 ≤ 19.98`). External hypothesis (TEAM §8 lesson 14): the only external inputs are `Prop5Decay` (now proved, `prop5Decay_holds`) and `EKSumNdecay` (proved); `kellStarEv` needs the limits `N→∞`, `W ≥ N^𝔠`, `W→∞`: on `sz0` (`Sizes.lean:260`, `L=4(n+1)`, `W=(2(n+1))⁵`, `lam=(2(n+1))⁻⁶`) `Bandwidth (1/6)` holds (`sz0_bandwidth_at`, `Sizes.lean`) and `log W_n = 5 log(2(n+1)) → ∞`, so `(log W)^{3/2}` dominates `log W` eventually; the `kellStarEv` hypotheses `RangeCond τ`, `WO 𝔡` were not computed here (no concrete `t n` chosen).

### Verdict per target

- `thetaGenMat`, `thetaGen`, `normSqSpectralMOne` (UBounds:48,52,416): **PASS** (rows 1, 4).
- `ukerNonneg`, `ukerRowSum`, `sumNdecay`, `sumNdecayEta`, `uopBack`, `uopOneStep` (UBounds:424-553): **PASS** (rows 1-4); constants unchanged; `g` becomes an explicit real parameter.
- `uopLocalMax`, `uopPairLocalMax` (UTransport:170,235): **PASS** with `L²→L^d` (row 5).
- `kellStarEv` (KellStar:311): **PASS** with `Prop5Decay` discharged by `prop5Decay_holds`, `log L` factor gone, one added hypothesis `0<lam n≤Λ` eventually (row 7); `STK2decay` is not needed.
- `tailtoTail` (UTransport:422), as ported (amplitude `T_t`, `O(1)` constant `30000e^{(log W)^{3/4}}`, additive `2ρ_η²W^{-D}`): **FAIL**. The d = 2 identity `r²M_s⁻²=ρ_ℓ⁴M_t⁻²` (row 10) rests on amplitude `∝η⁻²`; at `d≥3` the amplitude `B_{t,r}∝(g²+1-t)⁻¹` (`3_5:313-325`) leaves a factor `ρ_η=(1-s)/(1-t)` (regime `1-t≥g²`, hypothesis of `3_5:2351`) or growth `∝ρ_η` and linear in `L` at `d=3` (`ℓ_t=L`) not absorbed by any `s,t,L`-independent constant. Numerically (part C, exact `U`, `A=T_s≥0` allowed by the hypothesis, `U≥0` by `ukerNonneg`): ratio `53.6` at `ρ_η=50`, `≈ρ_η`; at `ℓ_t=L=8` the ratio grows `∝ρ_η` (`6.9e3, 8.4e4, 8.6e6` at `ρ_η=5e2, 5e3, 5e5`) and with `L` (`7.75, 13.5, 19.9, 26.6` times `ρ_η` at `L=4,6,8,10`). Evidence limits: `r≤3`, `L≤10`, i.e. below the d = 2 threshold `r ≥ ℓ*_t=(log W)^{3/2}ℓ_t`; I did not run `L≥16` and did not prove the lower bound analytically. Needs a dispatcher decision on the `d≥3` statement (an explicit factor `ρ_η` and `L`-dependence, or a restricted regime `g²≥1-s`, where `ρ_η²θ_t/θ_s ≤ ρ_ℓ⁴` and the d = 2 closure carries over). Paper-delta candidate `T2097a`: `neiwuj` (`3_5:2351-2362`) with an `s,t,L`-uniform `≲` is not valid for `1-t ≥ g²`.

Overall: **FAIL** (one target, `tailtoTail`); the other five groups PASS.

## (a′) Preflight corrections — Sun Oct  4 02:30:49 UTC 2026
- Row 7 gives the exponent `(1-τ)/𝔠` for `N^{1-τ} ≤ W^{(1-τ)/𝔠}`; `Sizes.size_rpow_le_W_rpow` needs a nonnegative exponent, so the proof uses `A = max(1-τ, 0)` (case τ > 1 included). No verdict changes.
- Amend 1 (ticket, DECISIONS §33): `tailtoTail` (FAIL in (a)) is removed from the targets with `uT_scalar`, `uT_zdist_neg`, `uT_near_far`; the part-C script and output stay in (a) and are re-run in b.8.

## (b) Script output — Sun Oct  4 02:30:49 UTC 2026
### b.1 Build, registry pre-check, scope (branch `t/T2097`, commits `9f59e8c`, `1750a03`, `8587022`)
```
$ lake build RBM3D.Path.UBounds RBM3D.Path.UTransport RBM3D.Path.KellStar 2>&1 | tail -2
Note: This linter can be disabled with `set_option linter.unusedDecidableInType false`
Build completed successfully (3692 jobs).
$ lake build 2>&1 | tail -2    # full library incl. root #assert_rbm_axioms; the new modules are not root imports yet
non-vacuity certificates: 4 of 105 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (3839 jobs).
$ lake env lean pre.lean   # outside the repo: import RBM3D + the 3 new modules + #assert_rbm_axioms (DECISIONS §20)
pre_exit=0; axiom audit: 3099 theorems, 1158 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ lake env lean RBM3D/Path/<each of the 3 files>.lean   # empty output (no warning, no error)
$ grep -c 'sorry|admit|native_decide|^axiom' <the 3 files>   # 0, 0, 0
$ git diff --stat main...t/T2097
 RBM3D/Path/KellStar.lean   | 434 ++++++++++++++++++++++++++
 RBM3D/Path/UBounds.lean    | 746 +++++++++++++++++++++++++++++++++++++++++++++
 RBM3D/Path/UTransport.lean | 412 +++++++++++++++++++++++++
 RBM3D/Test/Axioms.lean     |   3 +-
 4 files changed, 1594 insertions(+), 1 deletion(-)
```
### b.2 `#print axioms` (ax.lean, one script, every public declaration of the three files)
```
24 declarations [propext, Classical.choice, Quot.sound] : thetaGenMat, thetaGen, UopOneStep, NormSqSpectralMOne, UkerNonneg, UkerRowSum, SumNdecay, SumNdecayEta, UopBack, normSqSpectralMOne, ukerNonneg, ukerRowSum, sumNdecay, sumNdecayEta, uopBack, uopOneStep, UkerFar, UopLocalMax, UopPairLocalMax, uopLocalMax, uopPairLocalMax, KellStarEv, kellStarEv, kellStarEv_instance
```
### b.3 Target statements extracted by script (`extract.py`; the other six Prop pins, `UopOneStep UkerNonneg UkerRowSum SumNdecay UopBack NormSqSpectralMOne`, are covered by the diff in b.4)
```
-- UBounds.lean: def thetaGenMat (ξ : ℂ) (u : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))
-- UBounds.lean: def SumNdecayEta (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ E v w : ℝ, |E| < 2 → 0 ≤ v → v ≤ w → w < 1 →
    ∀ (A : Zd d L × Zd d L → ℂ) (α : ℝ), (∀ b, ‖A b‖ ≤ α) → ∀ a : Zd d L × Zd d L,
      ‖Uop d L g (Complex.normSq (mE E) : ℂ) v w A a‖ ≤ (etaT E v / etaT E w) ^ 2 * α
-- UBounds.lean: theorem normSqSpectralMOne : NormSqSpectralMOne := by
-- UBounds.lean: theorem ukerNonneg (d : ℕ) (g : ℝ) : UkerNonneg d g := by
-- UBounds.lean: theorem ukerRowSum (d : ℕ) (g : ℝ) : UkerRowSum d g := by
-- UBounds.lean: theorem sumNdecay (d : ℕ) (g : ℝ) : SumNdecay d g := by
-- UBounds.lean: theorem sumNdecayEta (d : ℕ) (g : ℝ) : SumNdecayEta d g := by
-- UBounds.lean: theorem uopBack (d : ℕ) (g : ℝ) : UopBack d g := by
-- UBounds.lean: theorem uopOneStep (d : ℕ) (g : ℝ) : UopOneStep d g := by
-- UTransport.lean: def UkerFar (d L W : ℕ) [NeZero L] (g u v R D' : ℝ) : Prop :=
  ∀ a b : Zd d L, R ≤ (zdistInf d L (a - b) : ℝ) → ‖ukerMat d L g 1 u v a b‖ ≤ (W : ℝ) ^ (-D')
-- UTransport.lean: def UopLocalMax (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar d L W g u v R D' → ∀ (A : Zd d L × Zd d L → ℂ) (α β : ℝ) (a : Zd d L × Zd d L), 0 ≤ β →
      (∀ b, ‖A b‖ ≤ α) →
      (∀ b : Zd d L × Zd d L, (zdistInf d L (a.1 - b.1) : ℝ) < R → (zdistInf d L (a.2 - b.2) : ℝ) < R →
        ‖A b‖ ≤ β) →
      ‖Uop d L g 1 u v A a‖ ≤
        ((1 - u) / (1 - v)) ^ 2 * β + 2 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) * α
-- UTransport.lean: def UopPairLocalMax (d : ℕ) (g : ℝ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ u v R D' : ℝ, 0 ≤ u → u ≤ v → v < 1 →
    UkerFar d L W g u v R D' →
    ∀ (A : Zd d L × Zd d L → Zd d L × Zd d L → ℂ) (α β : ℝ) (a : Zd d L × Zd d L), 0 ≤ β →
      (∀ b b', ‖A b b'‖ ≤ α) →
      (∀ b b' : Zd d L × Zd d L, (zdistInf d L (a.1 - b.1) : ℝ) < R → (zdistInf d L (a.2 - b.2) : ℝ) < R →
        (zdistInf d L (a.1 - b'.1) : ℝ) < R → (zdistInf d L (a.2 - b'.2) : ℝ) < R → ‖A b b'‖ ≤ β) →
      ‖∑ b : Zd d L × Zd d L, ∑ b' : Zd d L × Zd d L,
          ukerMat d L g 1 u v a.1 b.1 * ukerMat d L g 1 u v a.2 b.2 *
            (starRingEnd ℂ) (ukerMat d L g 1 u v a.1 b'.1 * ukerMat d L g 1 u v a.2 b'.2) * A b b'‖ ≤
        ((1 - u) / (1 - v)) ^ 4 * β +
          4 * (L : ℝ) ^ d * (W : ℝ) ^ (-D') * ((1 - u) / (1 - v)) ^ 3 * α
-- UTransport.lean: theorem uopLocalMax (d : ℕ) (g : ℝ) : UopLocalMax d g := by
-- UTransport.lean: theorem uopPairLocalMax (d : ℕ) (g : ℝ) : UopPairLocalMax d g := by
-- KellStar.lean: def KellStarEv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (𝔠 Λ τ δ D : ℝ) (t : ℕ → ℝ), 3 ≤ d → 0 < 𝔠 → 0 < Λ → 0 < τ → 0 < δ →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.RangeCond τ t → (∀ n, t n < 1) →
    (∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) →
    ∀ᶠ n : ℕ in atTop, ∀ s u : ℝ, 0 ≤ s → s ≤ u → u ≤ t n →
      ∀ a b : Zd d (sz.L n),
        δ * (Real.log (sz.W n : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
            (zdistInf d (sz.L n) (a - b) : ℝ) →
        ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ (sz.W n : ℝ) ^ (-D) ∧
          ‖ukerMat d (sz.L n) (sz.lam n) 1 s u a b‖ ≤ (sz.W n : ℝ) ^ (-D)
-- KellStar.lean: theorem kellStarEv (d : ℕ) : KellStarEv d := by
-- KellStar.lean: theorem kellStarEv_instance :
    ∃ n : ℕ, ∃ a b : Zd 3 (sz0.L n), a ≠ b ∧
      (‖Theta 3 (sz0.L n) (sz0.lam n) (((1 / 2 : ℝ)) : ℂ) a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ)) ∧
        ‖ukerMat 3 (sz0.L n) (sz0.lam n) 1 (1 / 4) (1 / 2) a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ))) ∧
      (‖Theta 3 (sz0.L n) (sz0.lam n) (((0 : ℝ)) : ℂ) a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ)) ∧
        ‖ukerMat 3 (sz0.L n) (sz0.lam n) 1 0 0 a b‖ ≤ (sz0.W n : ℝ) ^ (-(1 : ℝ))) := by
```
### b.4 Script diff of the pinned statements against RBM2D `c9a24cf` (ST1-COMMON item 6; `<` RBM2D after renaming, `>` RBM3D)
Renaming applied to the RBM2D text first: `Z2 L→Zd d L`, `zdist2 L→zdistInf d L`, `ukerMat|Uop|thetaGen|thetaGenMat L→… d L g`, `spectralM→mE`, `(L:ℝ)^2→(L:ℝ)^d`, `UkerFar L W→UkerFar d L W g`. Every residual line:
```
<   ξ • (SB L * Theta L ((u : ℂ) * ξ))
>   ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))
< def UopOneStep : Prop :=
> def UopOneStep (d : ℕ) (g : ℝ) : Prop :=
< def UkerNonneg : Prop :=
> def UkerNonneg (d : ℕ) (g : ℝ) : Prop :=
< def UkerRowSum : Prop :=
> def UkerRowSum (d : ℕ) (g : ℝ) : Prop :=
< def SumNdecay : Prop :=
> def SumNdecay (d : ℕ) (g : ℝ) : Prop :=
< def SumNdecayEta : Prop :=
> def SumNdecayEta (d : ℕ) (g : ℝ) : Prop :=
< def UopBack : Prop :=
> def UopBack (d : ℕ) (g : ℝ) : Prop :=
< def UkerFar (L W : ℕ) [NeZero L] (u v R D' : ℝ) : Prop :=
> def UkerFar (d L W : ℕ) [NeZero L] (g u v R D' : ℝ) : Prop :=
< def UopLocalMax : Prop :=
> def UopLocalMax (d : ℕ) (g : ℝ) : Prop :=
< def UopPairLocalMax : Prop :=
> def UopPairLocalMax (d : ℕ) (g : ℝ) : Prop :=
```
Residual differences: the parameters `(d : ℕ) (g : ℝ)`, and `SB L * Theta L` → `SB d L g * Theta d L g` in `thetaGenMat`. `KellStarEv` is the pin of RBM2D `KellStar:53` over `sz : Sizes d`; its differences are in (d).
### b.5 Compiled nonempty instances (same files; data in the narrative)
```
UBounds.lean: 14 `example`s at lines 641,644,647,655,663,671,678,685,693,707,714,721,727,735
UTransport.lean: 3 `example`s at lines 349,365,386
KellStar.lean: 0 `example`s at lines -; named instance `kellStarEv_instance` at line 409
```
### b.6 Name-clash grep (`clash.sh`: `git grep` for a def/theorem/lemma/abbrev/structure/instance/axiom of the same name on `main`) and d = 2 tokens
```
main = 2b7cab5; 24 new public names checked; total same-name declarations on main: 0
$ grep -n -E 'Z2 |zdist2|spectralM|scaleM|tailT| L \^ 2|W \^ 2|[^k]ellStar' <3 files> | grep -v KellStar    # all hits are header comments
RBM3D/Path/UBounds.lean:17:Renaming (`docs/tickets/ST1-COMMON.md` item 2): `Z2 L` becomes `Zd d L`; `SB L`, `Theta L`,
RBM3D/Path/UBounds.lean:19:coupling `g` an explicit real parameter (for the model, `g = sz.lam n`); `spectralM` becomes the
RBM3D/Path/UTransport.lean:25:Renaming (`docs/tickets/ST1-COMMON.md` item 2, 3): `Z2 L` becomes `Zd d L`; `zdist2` becomes the
RBM3D/Path/UTransport.lean:28:far sites: `card (Zd d L) = L^d` replaces `card (Z2 L) = L²` (`UTransport:147`); the near-label
```
### b.7 Port source (CLAUDE.md §5.2)
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h c9a24cf
c9a24cf
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h   # HEAD
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Path/UBounds.lean RBM2D/Path/UTransport.lean RBM2D/Path/KellStar.lean
 RBM2D/Path/KellStar.lean   |  77 +++-------------------
 RBM2D/Path/UBounds.lean    | 147 ++++++++---------------------------------
 RBM2D/Path/UTransport.lean | 161 +++++----------------------------------------
 3 files changed, 55 insertions(+), 330 deletions(-)
```
RBM2D `HEAD` differs from `c9a24cf` in these files (the first hunk of `git diff c9a24cf HEAD -- RBM2D/Path/UBounds.lean` is a trimmed header docstring; I did not inspect the other hunks); the port is from `c9a24cf`, as the ticket says.
### b.8 Part C (DECISIONS §33): the preflight script re-run in this stage
```
$ cd scratchpad/T2097 && (python3 chk.py; python3 chk2.py; python3 chk3.py) > rerun.out; diff rerun.out <(sed -n 32,55p T2097-prove.md) && echo IDENTICAL
IDENTICAL   (24 lines; the part-C rows are lines 42-55 of this file)
fa85a915ccf99988ffa4b7edcf476319180e40aa3cb2a290e2dd0e45d752a199  chk.py
803e614fa9001f4a0fe1e5787b49574837adbd0fb4e2bb853a80b2b541e8eb90  chk2.py
be6f38f0d5b85c38ba37f60305fb7cbc969711a93140b6d81515ec49783bd754  chk3.py
$ cat chk3.py     # chk.py (69 lines: build, uker, Tt, parts 1-2) supplies build/Tt; the L-scan at rho_eta = 5e5
import numpy as np, math
exec(open('chk.py').read().split("# ---- Part 1")[0])
exec("def Tt"+open('chk.py').read().split("def Tt")[1].split("d,L=3,8")[0])
d,g,oms,omt=3,1.0,0.5,1e-6; s,t=1-oms,1-omt
for L in (4,6,8,10):
    pts,idx,S,zi=build(d,L,g); n=len(pts); w,V=np.linalg.eigh(S)
    U=(V*((1-s*w)/(1-t*w)))@V.T
    tab=np.array([Tt(d,L,g,s,k)[0] for k in range(L)]); Ts=tab[zi]
    rr=2; a2=idx[(rr,0,0)]; a1=idx[(0,0,0)]
    q=(U[a1][:,None]*U[a2][None,:]*Ts).sum()/Tt(d,L,g,t,rr)[0]
    print("d=3 g=1 L=%d 1-s=0.5 1-t=1e-6 (rho_eta=%.0e): ratio r=2 = %.4g ; ratio/rho_eta = %.2f"%(L,oms/omt,q,q/(oms/omt)))
```
### b.9 Narrative
- Delivered: `UBounds.lean` (`thetaGenMat`, `thetaGen`, `normSqSpectralMOne`, `ukerNonneg` (public; the merged `StepDecompLoop_ukerNonneg` duplicate stays), `ukerRowSum`, `sumNdecay`, `sumNdecayEta`, `uopBack`, `uopOneStep`), `UTransport.lean` (`UkerFar`, `uopLocalMax`, `uopPairLocalMax`), `KellStar.lean` (`KellStarEv`, `kellStarEv`), and the registry line `RBM.Path.UkerFar` (structural) in `Test/Axioms.lean`.
- Form: the RBM2D `Prop` pins keep their shape with parameters `(d g)`; theorems are `(d g) : Pin d g`. Proofs are ported with `Z2 L→Zd d L`; the `d = 2` facts are replaced by merged lemmas: `SB` entries `sbKernelR_nonneg` (was `1/5`), `Theta_real_eq/nonneg` (was a Neumann-series copy), `‖Θ_z‖ ≤ (1-‖z‖)⁻¹` for complex `z` from `norm_Theta_le` at `z = ‖z‖·(z/‖z‖)`.
- Dropped (not ported): `KpmBoundProp5`/`kpmBoundProp5`, `ThetaMaxNorm`/`thetaMaxNorm` (ticket; `d = 2` constants and `scaleM`; `P.1` lists only `kellStarEv`), `TailtoTail`/`tailtoTail`, `uT_scalar`, `uT_zdist_neg`, `uT_near_far`, the `uT_check_*` lemmas (Amend 1; replaced by the `example`s), `kellStar_Kpm_eq`, `kellStar_min_le` (used only by dropped statements). `STK2decay` is not needed by `kellStarEv`; `EKSumNdecay` is not used by any of these statements.
- `d ≥ 3` exponents (class b): far term `2 L² W^{-D'}` → `2 L^d W^{-D'}` and `4 L² → 4 L^d` (`card (Zd d L) = L^d`, `card_Zd`); the near weights `((1-u)/(1-v))^k` and the constants `1, 4, 3` are dimension free (row sums). `kellStarEv`: RBM2D's `180·40002²(1+log L)·W²` is replaced by `C·B_{u,K} ≤ 2C(1-u)⁻¹ ≤ 2C W^{A/𝔠}` (`A = max(1-τ,0)`), closed by `2C + A/𝔠 + |D| ≤ c δ √(log W)`: slack from the exponent `3/2` against `1`, eventually since `W → ∞` (`Bandwidth`, `SizeTendsto`); no `log L` factor.
- Added hypotheses of `KellStarEv` (vs RBM2D): `3 ≤ d`, `0 < Λ`, and `∀ᶠ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ` (the window of `Prop5Decay`; Amend 1). The far distance is `zdistInf`; `prop5Decay_holds` is in `zdistD` and `zdistInf ≤ zdistD`, so this is the stronger form. `ℓ*_u = (log W)^{3/2}·ellT L g u` is written inline, no public `ellStar`.
- Instance data. UBounds: `d = 3, L = 3, g = 1/2`, `ξ = 1`, `(v,w) = (1/2,3/4)`, `E = 0`, `u = 1/4, t = 3/4`, `Δ ∈ {1/4,1/2}`, tensor `1` at `(0,0)` and `1/2` elsewhere; boundary (DECISIONS §29): `v = w = 0`, `w = 999/1000`, `u = t = 0`, one step at `u = 0` with `Δ = 0, 999/1000`. UTransport: `W = 2`, `(u,v) = (1/2,3/4)`, `R = 1`, `D' = -1` (`UkerFar` proved from the row sum `2 = W^{-D'}`), `β = 1/2 ≠ α = 1`, near set `{a}`, far set (per slot) the other 26 sites; boundary `u = v = 0`, `D' = 0`. KellStar: `sz0`, `𝔠 = 1/6, Λ = 1, τ = 1/2, δ = 1/200, D = 1, t n = 3/4`; every hypothesis of `kellStarEv` discharged; the `∀ᶠ` conclusion is used at a witness `n` (`Eventually.exists`) on the pair `a = (k,k,k)`, `k = 2(n+1) = L/2`, `b = 0`, which is far for every `n` (`ks_far`: `δ ℓ*_u ≤ |a-b|_∞`, using `ℓ_u ≤ 1`), at `(s,u) = (1/4,1/2)` and at the boundary `(0,0)`.
- Limits: the compiled `UkerFar` instance uses `D' = -1` (row-sum bound), not the numerical `D' = 3.7569` of (a) part B (checked in Python only). `kellStarEv_instance` is the conclusion at some index, not at an explicit `n`. The bridge `sz.WO 𝔡 → ∀ᶠ 0 < lam ≤ 𝔡⁻¹` is not proved here. The full `lake build` does not import the new modules; the pre-check does (b.1).
- Citations: every `UBounds:n`, `UTransport:n`, `KellStar:n` in the file headers was re-checked against `grep -n` of the `c9a24cf` text (commit `8587022`); RBM1D file:line cites inside docstrings are copied from RBM2D's docstrings and not re-checked.
- Merge: this branch is based on `c5bbae7`; `main` was `2b7cab5` when the clash grep ran (b.6). The `Axioms.lean` change is one appended list line (§20: union on conflict).

## (c) Verified Mathlib names (resolved by the successful build, b.1)
`Real.log_le_rpow_div` (`Pow/Real.lean:885`), `Real.rpow_def_of_pos`, `Real.rpow_neg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_two`, `Real.sqrt_eq_rpow`, `Real.sqrt_le_sqrt`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.le_sqrt_of_sq_le`, `Real.log_two_gt_d9`, `Real.log_pow`, `Real.add_one_le_exp`, `Real.tendsto_log_atTop`, `tendsto_rpow_atTop`, `tendsto_atTop_mono'`, `inv_anti₀`, `inv_le_one_of_one_le₀`, `le_self_pow₀`, `one_le_pow₀`, `Nat.le_self_pow`, `Nat.pow_le_pow_left`, `Finset.single_le_sum`, `Finset.sup_const`, `Finset.le_sup`, `Matrix.linfty_opNNNorm_def`, `ZMod.val_natCast`. Merged RBM3D names used: `ukerMat`, `Uop` (`Path/Kernel.lean:46,51`), `norm_SB` (`Defs/Block.lean:136`), `SB_mulVec_one` (`:113`), `sbKernelR_nonneg` (`:88`), `sbKernel_eq_ofReal` (`:79`), `Theta_mulVec_one` (`Propagator/Basic.lean:186`), `mul_Theta_of_three_le` (`Props4:90`), `Theta_real_eq` (`:173`), `Theta_real_nonneg` (`:177`), `norm_Theta_le` (`:218`), `Theta_apply_add_right_of_three_le` (`:100`), `Theta_sub_Theta` (`Deriv:57`), `norm_mE` (`Defs/Semicircle:63`), `mE_im_pos` (`:56`), `etaT` (`Loop/GLoop:75`), `prop5Decay_holds` (`Propagator/Prop5Hold:784`), `Bparam`, `ellT`, `ellT_pos` (`Defs/Params:36,32,44`), `Sizes.RangeCond` (`Green/Pins:55`), `Sizes.size_rpow_le_W_rpow` (`Defs/Sizes:237`), `zdistInf_le_zdistD` (`Sizes:117`), `zdistD_neg`, `zdist_eq_zero_iff`, `card_Zd` (`Defs/Lattice:103,30,67`), `sz0`, `sz0_bandwidth`, `sz0_tendsto` (`Sizes:260,298,300`). Absent (b.6 grep on `main`): every new public name of this ticket; a `d ≥ 3` `ellStar` (only a docstring in `Induction/ScaleFacts.lean:43` mentions it).

## (d) Open issues and paper-delta candidates
- **T2097a** (from (a), DECISIONS §33): `neiwuj` (`3_5:2351-2362`) with an `s,t,L`-uniform `≲` is not valid for `1-t ≥ g²` (ratio ≈ `ρ_η = (1-s)/(1-t)`, and growth in `L` at `ℓ_t = L`; b.8 and (a) part C). `tailtoTail` is not in this ticket; the Step 5 consumer (ST-4) needs its own `d ≥ 3` statement.
- **T2097b**: `KellStarEv`: the scale `ℓ*_u = (log W)^{3/2} ℓ_u` is a Lean-side scale (the paper's definition is the commented line `3_5_Loop_Hierarchy.tex:2313`); added hypotheses `3 ≤ d`, `0 < Λ`, `0 < lam ≤ Λ` eventually, `0 < 𝔠`, `0 < τ`; far distance `zdistInf`.
- **T2097c**: `UopLocalMax`, `UopPairLocalMax`: the far count is `card (Zd d L) = L^d` (RBM2D: `L²`); a consumer must make `4 L^d W^{-D'}` small (e.g. `L^d ≤ W^K`, DECISIONS §21).
- Open: the `UkerFar` hypothesis is supplied by `kellStarEv` only at `R = δ ℓ*_u` and eventually in `n` (no explicit `n₀`); the assembly that connects them belongs to the consumer ticket. No `sorry`, no new axiom, no scope beyond the four writable files.
