Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 20:55:25 UTC 2026

Targets (math only): 1a-1d carrier-free helpers (|∫kPoint| ≤ N^k sup|P|; energy shift; worst-sequence argument; GUE count); 2 conditioning+shift; 3a `UNInfty1 sz M ρ E 0 k O τU` from `UNL32`, `UNGUELocal`, `UNDens'`, `UNTrLocal`, `UNNormBound`, `0<τU≤𝔠𝔡`; 3b `∃τ₁>0, ∀τU≤τ₁`, `τ₁=𝔠𝔡`; 4 instances. Sources read: ticket, check file, `Pins.lean:281-313, 440-560, 573, 822-848`, `PinsDens.lean:55-112`, `Step1Good.lean:207-240, 750-860`, `Step1Cond.lean:368, 531-545, 595, 695, 781-803`, `Defs/Sizes.lean:136-190`, RBM2D `Universality/Step1Band.lean` (c9a24cf layout, `:840-1000` read), supervisor 1651 §2.4, `T2208-prove.md`.

### (i) Exponent table
`τ := τU`, `N = Nsz sz n = (WL)^d ≥ 27` (`W ≥ 1`, `L ≥ 3`, `d ≥ 3`). Every exponent below depends on `τ, k` only (not on `d, W, L, lam`); `d` enters only via `τ ≤ 𝔠𝔡` (so `τ < 1/2`, `un_admissible_cd_lt_half`) and the carrier `Idx d L W`.

| quantity | value | constraint | slack |
|---|---|---|---|
| `t* = N^{-1+τ}`, `t = 1-e^{-t*}` | `t ∈ [t*/2, t*]` for `t* ≤ 1` | `UNL32` premises `g N^σ ≤ t ≤ N^{-3σ}` (`G=N^{-σ}`) | `N^{τ/2} ≥ 2` (`un_L32_arith`) |
| `σ = δ_L32 = min(τ/4,(1-τ)/3)`, `q=1/2`, `g=N^{-1+τ/4}`, `G=N^{-σ}`, `E_n=0` | `σ=τ/4` for `τ ≤ 4/7` | `σ ≤ τ/4` (`g N^σ ≤ N^{-1+τ/2}`), `3σ ≤ 1-τ`, `σ ≤ 1-τ/4` | `τ<1/2`: all strict |
| `UNL32` size threshold | `ln N ≥ (2/τ) ln 2` | `N^{τ/2} ≥ 2` | `83.18` at `τ=1/60`; `277.26` at `τ=1/200` |
| good-event prob. `D = k+1` | `μ(bad) ≤ N^{-k-1}` | one call of `step1Good'` at `(τs,D)=(τ,k+1)`; `τ<1` ✓ | nonempty: `N^{-k-1} ≤ 1/27 < 1 = μ(univ)` |
| bad-event contribution | `|F_n-GUE_n| ≤ 2 N^k sup|O|` on bad set | `2 sup|O| N^k N^{-k-1} = 2 sup|O|/N → 0` | rate `N^{-1}` |
| density range (`UNDens`) | `ρ_n ∈ [c_D/π, C_D/π]` (limit of `π⁻¹Im m_n(E+iη)` ∈ closed interval; `c_D ≤ C_D`) | `0<c_D` | — |
| `ρ'_n` (event of `UNStep1Good'`) | `|ρ'_n-ρ_n| ≤ N^{-3τ/8}` | want `ρ'_n ∈ [ρmin,ρmax] = [c_D/2π, 2C_D/π]` | needs `N^{-3τ/8} ≤ c_D/(2π)` and `c_D ≤ 2C_D` (true); `ρ'/ρ_n ∈ [1/2, 3/2]` then |
| `ρ`-threshold | `ln N ≥ (8/(3τ)) ln(2π/c_D)` | as above | `679.33` at `τ=1/60, c_D=9/100` |
| Lipschitz step (`Step1Cond_scaledPairing_lipschitz`) | statement is `|ρ^k A(ρ) - ρ'^k A(ρ')| ≤ C|ρ-ρ'| kPoint Q`, `A(ρ)=∫kPoint(O(ρ·))` | apply at `(ρ,ρ')=(ρ_n,ρ'_n) ∈ [ρmin,ρmax]²` (fixed `O`); extra term `(ρ'^k/ρ^k-1)A(ρ')`, `|ρ'^k/ρ^k-1| ≤ k (3/2)^{k-1} N^{-3τ/8}/ρ_n`, `|A(ρ')| ≤ |GUE_n| + |L32 diff|` | both are `N^{-3τ/8}×(count)` |
| domination | `Q(β) ≤ Q'(ρβ)`, `ρ∈[ρmin,ρmax]` (`exists_dominating_testFun`) | `kPoint Q ≤ kPoint Q'(ρ'_n ·)`, then `UNL32` at the fixed `Q'`: `→ GUE(Q'(ρ_sc(0)·))` | error `N^{-3τ/8}·count → 0` |
| GUE count (1d) | `a = τ/(8(k+1))`, `τ_G = a/2`, `z = iN^{-1+a}`, `D=k+1` | `UNGUELocal`: `N^{τ_G}/√(N Im z) = 1`, so `|m_N-msc| ≤ 1`, `Im msc ≤ 1`, `Im m_N ≤ 2`; `N^{-1+τ_G} ≤ Im z` ✓ (`τ_G ≤ a`); `#{|λ|≤η} ≤ 2Nη Im m_N ≤ 4N^a`, window `R/N ≤ η` eventually | `3τ/8 - ka ≥ τ/4` (`ka < τ/8`); bad part `N^k N^{-k-1}` |
| diagonal argument (1c) | worst sequence `f n := if h : bad n then h.choose else b n` | `∀ᶠ` for every `f` ⇒ `∀ᶠ ∀ z`; also `k=0` is consistent (`kPoint` const) | — |
| `d`-dependence | none in exponents | `𝔠d<1`, `𝔡 ≤ d/2` (merged `un_admissible_*`) ⇒ `𝔠𝔡 < 1/2` | `d=3`: `1/6·3=0.5<1` |

Order of constants: `O,k` → `c_D,C_D,Lp` (`UNDens'`) → `c,C` (`step1Good'` at `D=k+1`) → `ρmin,ρmax` → `Q,C_Lip` → `Q'` → `Qa` (|O| dominating) → `ε` → `n`. None depends on `W, L, lam, card, n`.

Consumer check (token by token, from the files): 3a's conclusion is `UNInfty1 sz M ρ E 0 k O τU` (`Pins.lean:552`: model side `kPoint(O(ρ_n·)) E (𝐇_{t*})` under `ouP`, GUE side `kPoint(O(ρ_sc(E')·)) E'` at `E'=0`); 3b has the binders of `UNInfty1Row'` (`PinsDens.lean:88-95`) with `∀E', |E'|<2` removed and `E'=0` (`|0|<2` ✓): `UNInfty1Row' ⇒ 3b` at `E'=0`. `UNL32` premises (`Pins.lean:281-296`) ⇔ event of `UNStep1Good'` (`PinsDens.lean:73-84`) at `τs=τ` with `g=N^{-1+τ/4}`, `G=N^{-σ}`, `IsRegular32 … c C (CV₀+1)`, `IsFreeConv32 … (1-e^{-ouTStar})`, density limit `ρ'`; arithmetic premises are `un_L32_arith` (`t = 1-e^{-N^{-1+τ}}` = `1-e^{-ouTStar}` since `ouTStar = N^{-1+τ}`, `Pins.lean:142`). Shift: `vOU = e^{-t*/2}λ(H) - E` (`Pins.lean:573`), `dbmMat(v-E) = dbmMat v - E·1` ⇒ `kPoint O 0 λ(A-E) = kPoint O E λ(A)`; conditioning `integral_kPoint_ouMat_cond` (`Step1Cond.lean:368`) at `t=t*`. Dilation: `UNL32` yields `O(ρ'_n·)`; target has `O(ρ_n·)`; difference handled by the two Lipschitz/count rows above.

Two data, one model (supervisor 1651 §2.4, read in file): `ρ_n-ρ̃_n → 0`, both in `[ρmin,ρmax]`; two conclusions differ by `ρ_n` vs `ρ̃_n` dilation, `→ 0` by the Lipschitz row: compatible (unlike refuted `UNInfty1Row`, whose `UNDens` did not force it). Model side reads `H` only through `λ(H)` in `vOU`; `UNNormBound` bounds `λ(H)` (no mean term).

Premises kept by the instances (band; docstring claims, not verified here): `UNLocAvgBand` (MA `G_bound_ave`), `UNTrLocalBandRow` (block average of it, `Pins.lean:842`), `UNNormBandRow` (`|λ| ≤ N‖entries‖`, entries `|h|≤1` w.h.p., `CV₀=1`), `UNDensBandRow` (`Im msc ≥ c>0` on the window: script below), `UNGUELocal` (GUE averaged law; `N^{τ_G}/√(N Im z)=1` exact at `z=iN^{-1+a}`), `UNL32` (LSY Thm 2.2; premises: script below). BA suppliers (not checked): `UNDensBARow'` BA-C2, `UNTrLocal`/`UNNormBound` BA-D1.

### (ii) Concrete nondegenerate instance
`d=3`, `sz0` (`N_n = 2097152 (n+1)^18`, `T2208-prove.md` (ii)), `(𝔠,𝔡)=(1/6,1/10)`, band model, `m=msc`, `k=1`, `O=bump` (`bump 0=1`, `bump 3=0`), `τU=1/60=𝔠𝔡`. Case E=0: `δ=1/2`, `c_D=9/100`, `C_D=1`, `ρ_n=1/π`. Case E=1: `κ=1/2`, `δ ≤ 1/4`, `ρ_n=ρ_sc(1)=0.27566 ≠ ρ_sc(0)`. All deterministic hypotheses hold (`3≤3`, `Admissible`, `0<τU≤𝔠𝔡`, `|E| ≤ 2-κ`, `0<δ≤κ/2`, `bump` test function); the conclusions are eventual (`Tendsto`), thresholds are not witnesses.
Commands (python3 + mpmath 60 digits; scratch `pf.py`, `e1.py`, `gue.py`; math only):
```
$ python3 pf.py
== exponent table (tau_U = c*d, k = 1, 2, 5) ==
c*d=0.016667 (<1/2: True) sigma=0.0041667 rate 3tU/8=0.0062500 L32 thr lnN>=83.18  rho-thr lnN>=679.33
   k=1: a=tU/(8(k+1))=0.0010417 tauG=a/2=0.0005208 k*a=0.0010417 slack 3tU/8-k*a=0.0052083 >= tU/4=0.0041667: True
   k=2: a=tU/(8(k+1))=0.0006944 tauG=a/2=0.0003472 k*a=0.0013889 slack 3tU/8-k*a=0.0048611 >= tU/4=0.0041667: True
   k=5: a=tU/(8(k+1))=0.0003472 tauG=a/2=0.0001736 k*a=0.0017361 slack 3tU/8-k*a=0.0045139 >= tU/4=0.0041667: True
   sigma<=tU/4: True, 3sigma<=1-tU: True, 1+bad-event: N^(k)*N^(-k-1)=1/N
c*d=0.005000 (<1/2: True) sigma=0.0012500 rate 3tU/8=0.0018750 L32 thr lnN>=277.26  rho-thr lnN>=2264.44
   k=1: a=tU/(8(k+1))=0.0003125 tauG=a/2=0.0001563 k*a=0.0003125 slack 3tU/8-k*a=0.0015625 >= tU/4=0.0012500: True
   k=2: a=tU/(8(k+1))=0.0002083 tauG=a/2=0.0001042 k*a=0.0004167 slack 3tU/8-k*a=0.0014583 >= tU/4=0.0012500: True
   k=5: a=tU/(8(k+1))=0.0001042 tauG=a/2=0.0000521 k*a=0.0005208 slack 3tU/8-k*a=0.0013542 >= tU/4=0.0012500: True
   sigma<=tU/4: True, 3sigma<=1-tU: True, 1+bad-event: N^(k)*N^(-k-1)=1/N
== density window: rho_n, rho', [rhomin,rhomax] at cD=9/100, CD=1 ==
rho_n=1/pi= 0.3183098861837907  in [cD/pi,CD/pi]: True ; [rmin,rmax]= 0.01432394487827058 0.6366197723675814 ; rho' range [cD/pi - cD/2pi, CD/pi + cD/2pi] inside: True (needs cD<=2CD: True )
== L32 six arithmetic premises, exact formulas, at sz0 N_n, tau=1/60 ==
L32 (N^(tau/2)>=2): least n=45, ln N_n=83.47, thr=83.18, N^(tau/2)=2.005, N^(-3tau/8)=0.5935 <= cD/2pi=0.0143: False; six premises [True, True, True, True, True, True]
rho (N^(-3tau/8)<=cD/2pi): least n=10948450013670327, ln N_n=679.33, thr=679.33, N^(tau/2)=287.464, N^(-3tau/8)=0.0143 <= cD/2pi=0.0143: True; six premises [True, True, True, True, True, True]
== msc Im on windows (grid): E=0 window |x|<=1/2 and E=1 window |x-1|<=1/4, 0<eta<=10 ==
E=0, delta=0.5: min Im msc=0.0988 (cD=9/100 ok at E=0: True), max=1.0000
E=1, delta=0.25: min Im msc=0.0976 (cD=9/100 ok at E=0: True), max=0.9270
rhoSC(0)= 0.3183098861837907 rhoSC(1)= 0.27566444771089604 ; sqrt3/(2pi)<2/(2pi): True
UNL32 / external: Tendsto size -> inf at sz0: ln N_n = ln 2097152 + 18 ln(n+1) -> 263.2352988351068 at n=1e6 (unbounded)
$ python3 e1.py
E=1: rho_n=rhoSC(1)=0.27566 in [cD/pi, CD/pi]=[0.03107, 0.29507]: True
E=1: [rhomin,rhomax]=[cD/2pi, 2CD/pi]=[0.01553, 0.59015] contains rho_n, rho_sc(1)-N^(-3tU/8)..+: True
dilation ratio rho_sc(0)/rho_sc(1)=1.15470 (!=1: dilations differ)
$ python3 gue.py    # GUE N=2000, E|h_ij|^2=1/N, 20 samples each, count #{|λ_i| ≤ η} vs 2Nη Im m_N(iη) vs 4N^a
a=0.1: eta=N^(-1+a)=0.0011  max count=2  max 2N eta Im m_N=5.06  4N^a=8.55  count<=2N eta Im m_N always: True
a=0.2: eta=N^(-1+a)=0.0023  max count=4  max 2N eta Im m_N=10.27  4N^a=18.29  count<=2N eta Im m_N always: True
```
External hypothesis `UNL32` (borrowed): arithmetic premises are verified at the first admissible `n` (45, `ln N=83.47`) by the first `pf.py` block (all six True); the regularity premises are the event of `step1Good'` (T2208 (a): thresholds `ln N ≳ 2·10^3`, so the instances are eventual in `n` only; the `ρ`-threshold needs `n ≈ 1.1·10^16` at `τ=1/60`: it is a threshold of an eventual statement, not a witness used by any instance). `size n → ∞` at `sz0` is the last line of `pf.py`.
Notes (not blockers): at `E=0` the table `Im msc` min `0.0988 ≥ 9/100` matches `un_dens_msc_zero`'s `c=9/100`; at `E=1` the grid min is `0.0976` (the instance uses the `c` supplied by `UNDensBandRow`).

### Verdict
- Targets 1a, 1b, 1c, 1d: PASS (exponent `3τ/8 - ka ≥ τ/4 > 0`, `a`-window and bad event close; 1c is pure logic).
- Target 2: PASS (merged conditioning at `t=t*`, shift identity above).
- Target 3a: PASS (all exponents of the table close; one call of `step1Good'` at `D=k+1` gives nonemptiness and the bad bound; `ρ'_n ∈ [ρmin,ρmax]` eventually; extra `ρ^k` term of the Lipschitz statement is `N^{-3τ/8}×count`).
- Target 3b: PASS (`τ₁ = 𝔠𝔡 > 0` from `Admissible`).
- Target 4 (three instances): PASS (hypotheses hold at the data; `ρ_sc(1) < ρ_sc(0)`; `UNL32`, `UNGUELocal`, band rows stay hypotheses).
- Design notes for 1b: T2214a (UN-11 is a UN-14 dependency only), T2214b (`UNStep1Good'` puts `∃ c C` after `D`: use one call at `D=k+1`) confirmed by the table above.

## (b) Script output — Mon Oct  5 21:23:37 UTC 2026
$ cd RBM3D-wt/T2214 && git log -1 --format='%h %an %s' && git diff --stat main...t/T2214 && grep -cE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/Step1Band.lean && wc -l RBM3D/Universality/Step1Band.lean
f04dcb7 Jun Yin T2214: UN-13 Universality/Step1Band: Step 1 of (1infyuniv) against the GUE at energy 0
 RBM3D/Universality/Step1Band.lean | 1240 +++++++++++++++++++++++++++++++++++++
 1 file changed, 1240 insertions(+)
0
    1240 RBM3D/Universality/Step1Band.lean
$ lake build RBM3D.Universality.Step1Band   # first compile of the module (build.log, tool log), then the up-to-date rerun
✔ [3362/3362] Built RBM3D.Universality.Step1Band (6.4s)
Build completed successfully (3362 jobs).
$ lake build 2>&1 | tail -1   # whole library incl. root `#assert_rbm_axioms` and Test/AuditNegative (the root does not import the new module yet: hub step)
Build completed successfully (4017 jobs).
$ lake env lean axioms.lean   # `#print axioms` of every new public declaration (grouped by axiom set)
16 declarations depend on exactly [propext, Classical.choice, Quot.sound]: step1Band_abs_integral_kPoint_le, step1Band_kPoint_shift,
  step1Band_eventually_forall, step1Band_gue_count, step1Band_integral_ouP, step1Band, step1Band_row,
  Step1BandInst.inst_step1Band_band, Step1BandInst.inst_step1Band_band_one, Step1BandInst.inst_rhoSC_one_lt_zero,
  Step1BandInst.inst_step1Band_row_band, Step1BandInst.inst_step1Band_abs_integral_kPoint_le,
  Step1BandInst.inst_step1Band_kPoint_shift, Step1BandInst.inst_step1Band_eventually_forall, Step1BandInst.inst_step1Band_gue_count,
  Step1BandInst.inst_step1Band_integral_ouP
$ python3 extract_statements.py   # target statements extracted from the file (whitespace-folded)
[:152] step1Band_abs_integral_kPoint_le : ∀ {Ω' : Type} [MeasurableSpace Ω'] (Pm : Measure Ω') [IsProbabilityMeasure Pm] {ι : Type} [Fintype
    ι] [DecidableEq ι] (Hm : Ω' → Matrix ι ι ℂ) (hH : ∀ ω, (Hm ω).IsHermitian) (k : ℕ) {P : (Fin k → ℝ) → ℝ} {B : ℝ}, (∀ x, |P x| ≤ B) → ∀ E
    : ℝ, |∫ ω, kPoint k P E (hH ω).eigenvalues ∂Pm| ≤ (Fintype.card ι : ℝ) ^ k * B
[:374] step1Band_kPoint_shift : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (c :
    ℝ), B = A - (c : ℂ) • (1 : Matrix ι ι ℂ) → ∀ (k : ℕ) (O : (Fin k → ℝ) → ℝ), kPoint k O 0 hB.eigenvalues = kPoint k O c hA.eigenvalues
[:395] step1Band_eventually_forall : ∀ {α : ℕ → Type} (A P : ∀ n, α n → Prop) (b : ∀ n, α n), (∀ᶠ n in atTop, A n (b n)) → (∀ f : ∀ n, α n,
    (∀ᶠ n in atTop, A n (f n)) → ∀ᶠ n in atTop, P n (f n)) → ∀ᶠ n in atTop, ∀ z : α n, A n z → P n z
[:428] step1Band_gue_count : UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop → ∀ τs : ℝ, 0 < τs → τs
    < 1 → ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ), IsTestFun Q → 0 ≤ Q → Tendsto (fun n => Nsz sz n ^ (-(3 * τs / 8)) * ∫ ω, kPoint k Q 0
    (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) atTop (𝓝 0)
[:643] step1Band_integral_ouP : ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τU E : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O → ∫
    ω, kPoint k O E (ouMat_isHermitian M n (ouTStar sz τU n) ω).eigenvalues ∂(ouP M n) = ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L
    n) (sz.W n) (vOU sz M n τU E ω) (1 - Real.exp (-(ouTStar sz τU n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) ∂M.μ
[:1006] step1Band : UNL32 → UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ)
    (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) → ∀ k : ℕ, ∀ O : (Fin
    k → ℝ) → ℝ, IsTestFun O → ∀ τU : ℝ, 0 < τU → τU ≤ 𝔠 * 𝔡 → UNInfty1 sz M ρ E 0 k O τU
[:1121] step1Band_row : UNL32 → UNGUELocal → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ →
    ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) → ∀ k : ℕ, ∀ O :
    (Fin k → ℝ) → ℝ, IsTestFun O → ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ → UNInfty1 sz M ρ E 0 k O τU
$ sed -n '1149,1160p' RBM3D/Universality/Step1Band.lean   # compiled nonempty instance of `step1Band` (target 4); `_band_one` (E = 1) and `inst_rhoSC_one_lt_zero` follow it
theorem inst_step1Band_band :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60) := by
  intro h32 hGL hLoc rT rN
  obtain ⟨CV₀, hCV, hN⟩ := rN 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm
  exact step1Band h32 hGL 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm (UNModel.band sz0) (fun _ => msc) 0
    (fun _ => rhoSC 0) (1 / 2) un_dens'_msc_zero
    (rT hLoc 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_adm 1 one_pos 0 (by norm_num) (1 / 2) (by norm_num)
      (by norm_num))
    ⟨CV₀, hCV, hN⟩ 1 bump bump_testFun (1 / 60) (by norm_num) (by norm_num)
[:1163] theorem inst_step1Band_band_one : UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → UNDensBandRow → UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 1) 1 0 1 (bump : (Fin 1 → ℝ) → ℝ) (1 / 60)
   := by  (obtains `δ ≤ 1/4`, `UNDens'` from `unDensBandRow'_of_row rD (1/2) _ 1 _`, `0 < δ` from `hD.1.1`, then `step1Band` at `E = 1`, `κ = 1/2`)
[:1176] theorem inst_rhoSC_one_lt_zero : rhoSC 1 < rhoSC 0   (unfold rhoSC; `div_lt_div_iff_of_pos_right`, `Real.sqrt_lt_sqrt`)
$ grep -n '^theorem inst_' RBM3D/Universality/Step1Band.lean | sed 's/ :.*//'   # the other instances: helper targets 1a-1d, 2, 3b, same file
1149:inst_step1Band_band 1163:inst_step1Band_band_one 1176:inst_rhoSC_one_lt_zero 1182:inst_step1Band_row_band
1195:inst_step1Band_abs_integral_kPoint_le 1203:inst_step1Band_kPoint_shift 1210:inst_step1Band_eventually_forall
1217:inst_step1Band_gue_count 1226:inst_step1Band_integral_ouP
$ python3 diff_check.py   # check section 2 (docs/tickets/checks/T2214-check.lean) against the library statements, whitespace-normalised
10 of 10 IDENTICAL: step1Band_abs_integral_kPoint_le step1Band_kPoint_shift step1Band_eventually_forall step1Band_gue_count
  step1Band_integral_ouP step1Band step1Band_row inst_step1Band_band inst_step1Band_band_one inst_rhoSC_one_lt_zero
$ lake env lean T2214-check-scratch.lean   # the check file with `import RBM3D.Universality.Step1Band`, plus `example : T2214_<name> := <name>` for all 10 statements, plus `example : UNInfty1Row' → T2214_step1Band_row`
exit=0   (negative control: `T2214_step1Band_row := step1Band` gives 1 error)
$ (main worktree at 14513ee) grep -rnF "$n" RBM3D RBM3D.lean | grep -v '^RBM3D/Probe/' | wc -l   # hits per new public name / helper prefix
step1Band_abs_integral_kPoint_le=0 step1Band_kPoint_shift=0 step1Band_eventually_forall=0 step1Band_gue_count=0
step1Band_integral_ouP=0 step1Band_row=0 Step1BandInst=0 inst_step1Band_band=0 inst_step1Band_band_one=0 inst_rhoSC_one_lt_zero=0
inst_step1Band_row_band=0 inst_step1Band_abs_integral_kPoint_le=0 inst_step1Band_kPoint_shift=0 inst_step1Band_eventually_forall=0
inst_step1Band_gue_count=0 inst_step1Band_integral_ouP=0 Step1Band_=0
$ grep -rnw step1Band RBM3D RBM3D.lean | grep -v '^RBM3D/Probe/' | wc -l ; grep -rnF 'Universality.Step1Band' RBM3D RBM3D.lean | wc -l
       0 ;        0
$ printf 'import RBM3D\nimport RBM3D.Universality.Step1Band\n\n#assert_rbm_axioms\n' > precheck.lean (uncommitted, scratch); lake env lean precheck.lean; echo exit=$?
exit=0   axiom audit: 6385 theorems, 2209 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 96, structural 25, refuted 4). | registry: 2 borrowed + 148 owed + 79 structural + 4 refuted
$ same file without the second import (the base of the branch, 0bc4633): exit=0   axiom audit: 6369 theorems, 2209 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 126 (borrowed 1, owed 96, structural 25, refuted 4). | registry: 2 borrowed + 148 owed + 79 structural + 4 refuted
$ premise counts that differ between the two pre-check outputs (theorems resting on the premise): UNL32 13->18, UNGUELocal 13->20, UNTrLocal 10->12, UNLocAvgBand 17->20, UNNormBound 9->11, UNNormBandRow 8->11, UNTrLocalBandRow 8->11, UNDensBandRow 7->8; 142 other premise lines equal
$ grep -cE "UNStep1Good[^']|UNInfty1Row[^']|UNStep1GoodC|UNCoreC|UNTrLocalInit|UNModelC|vOUC|UNCore[^']" RBM3D/Universality/Step1Band.lean   # refuted / C-form names consumed by the file
0
$ ports (source: RBM2D `RBM2D/Universality/Step1Band.lean` at c9a24cf, `git show c9a24cf:...`): declaration line in the source -> line in RBM3D/Universality/Step1Band.lean
Step1Band_abs_kPoint_le:118->Step1Band_abs_kPoint_le:99 Step1Band_abs_integral_kPoint_le:170->step1Band_abs_integral_kPoint_le:152
Step1Band_abs_integral_le_of_abs_le:188->Step1Band_abs_integral_le_of_abs_le:171
Step1Band_exists_abs_dominating:233->Step1Band_exists_abs_dominating:205
Step1Band_measurable_eigenvalue:268->Step1Band_measurable_eigenvalue:237 Step1Band_count_le_im:319->Step1Band_count_le_im:271
Step1Band_eigenvalues_shift:378->Step1Band_eigenvalues_shift:331 Step1Band_kPoint_shift:419->step1Band_kPoint_shift:374
Step1Band_integral_dbm_shift:449->Step1Band_integral_dbm_shift:630 Step1Band_gue_count:466->step1Band_gue_count:428
Step1Band_measurable_Hs:681->Step1Band_measurable_F:663 Step1Band_integral_ouP:711->step1Band_integral_ouP:643
Step1Band_core:747->Step1Band_core:719 Step1Band_eventually_forall:999->step1Band_eventually_forall:395
Step1Band_uniform:1025->Step1Band_uniform:959 step1Band:1072->step1Band:1006
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h ; git -C ../RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/Step1Band.lean | wc -l ; git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Step1Band.lean
9e0f275 ;     1259 ;  RBM2D/Universality/Step1Band.lean | 154 ++++++-------------------------------- ;  1 file changed, 24 insertions(+), 130 deletions(-)
$ grep -n '^import' RBM3D/Universality/Step1Band.lean   # dependencies by import lines (DECISIONS §54): UN-11 (`Step1RegularityGUE`) is not imported (T2214a)
6:import RBM3D.Universality.Step1Good ; 7:import RBM3D.Universality.Step1Cond

Narrative (route and facts; evidence is the script output above).
- New file `RBM3D/Universality/Step1Band.lean` (1240 lines), imports `Step1Good`, `Step1Cond` only. Layout: helpers and shift (1a `:152`, 1b `:374`),
  diagonal argument (1c `:395`), GUE count (1d `:428`), conditioning (2 `:643`), worst-sequence core (`:719`), uniformity and `step1Band`
  (3a `:1006`), `step1Band_row` (3b `:1121`), instances (`:1149-`). Port of RBM2D `Step1Band.lean` at `c9a24cf` (line map above).
- Statements: the ten statements of check section 2 are identical to the library (diff script); no hypothesis added, nothing weakened, no pinned or
  merged signature changed, only the one new file in `git diff --stat`.
- `step1Good'` is called once, at `(τs, D) = (τU, k+1)` (`:1024`); that one event gives both the nonemptiness (`N^{-1} < 1` since `N ≥ 27` from
  `3 ≤ d`, `L ≥ 3`, `W ≥ 1`) and the bad bound `N^{-(k+1)}` (T2214b). `UNDens` enters only through the range `c_D/π ≤ ρ_n ≤ C_D/π`
  (`Step1Band_density_range`, `:934`); `UNDens'` only through `step1Good'`. The constants order is that of section (a).
- Core: `UNL32` is applied at `(σ, σ, 1/2, c, C, CV₀+1)`, `E_n = 0`, `g = N^{-1+τ/4}`, `G = N^{-σ}`, `t = 1 - e^{-t*}`; `m_n`, `ρ'_n` are chosen from the
  event by `choose` (`:745`); the six arithmetic premises are `un_L32_arith` (`:770`), eventually in `n` (`N^{τ/2} ≥ 2`).
- The dilation `ρ'_n → ρ_n` is not normalised to `ρ_sc(E)` as in RBM2D: `Step1Cond_scaledPairing_lipschitz` is applied directly at the pair
  `(ρ_n, ρ'_n)` in `[a0/2, b0 + a0/2]` (`:797`), giving `|A(ρ_n) - A(ρ'_n)| ≤ K1 m_r corr + K2 m_r (|D| + G_a)`, `m_r = N^{-3τ/8}`; `corr ≤ G_Q + 1`
  from `UNL32` at the dominating `Q'` (`:800`); `m_r G_Q`, `m_r G_a → 0` by `step1Band_gue_count`. No factor `r^k` occurs.
- Uniformity over the good event by the worst-sequence argument (1c, carrier `Sizes.SeqΩ sz`); bad event: `|F_n|, |c| ≤ N^k sup|O|` times
  `μ ≤ N^{-(k+1)}`, i.e. `2 sup|O| / N → 0`.
- `d ≥ 3`: `d` enters only through `3 ≤ d` (`N ≥ 27`, `UNL32`, `step1Good'`) and `τU ≤ 𝔠𝔡` (`un_admissible_cd_lt_half`, `τU < 1/2`); the
  exponent table of (a) was used unchanged; no (a′) is needed.
- Registry: no line appended to `Test/Axioms.lean`; the pre-check exits 0, the scanned-premise and registry counts equal those of the base; the new
  theorems only raise the theorem counts under the eight registered premises listed above; no refuted or C-form name occurs in the file.
- Instances: every deterministic hypothesis is discharged (`3 ≤ 3`, `sz0_adm`, `un_dens'_msc_zero`, `|1| ≤ 2 - 1/2`, `0 < δ ≤ 1/4`, `0 < 1/60 ≤ 𝔠𝔡`,
  `bump_testFun`); `UNL32`, `UNGUELocal` and the band rows stay hypotheses (other gates' pins); conclusions are eventual in `n`, no concrete `n`.
- Not targets (as in the ticket): `UNInfty1Row'` and the GUE translation (UN-14), the C form, the refuted pins. Root import: hub step.
  The full `lake build` above does not yet contain the module (root import is added at merge); the module was built alone and with the pre-check.

## (c) Verified Mathlib names used
`#check @name` of every non-trivial Mathlib name used, run in `names.lean` with `import RBM3D.Universality.Step1Band` (exit 0); types truncated to one line; none checked absent.
@tendsto_natCast_atTop_iff : ∀ {α : Type u_1} {R : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [
@tendsto_natCast_atTop_atTop : ∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [IsOrderedRing
@tendsto_rpow_neg_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ (-y)) Filter.atTop (nhds 0)
@tendsto_rpow_atTop : ∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x ^ y) Filter.atTop Filter.atTop
@Real.rpow_le_rpow_of_exponent_le : ∀ {x y z : ℝ}, 1 ≤ x → y ≤ z → x ^ y ≤ x ^ z
@Real.rpow_le_one_of_one_le_of_nonpos : ∀ {x z : ℝ}, 1 ≤ x → z ≤ 0 → x ^ z ≤ 1
Real.rpow_neg_one : ∀ (x : ℝ), x ^ (-1) = x⁻¹
@Real.rpow_mul_natCast : ∀ {x : ℝ}, 0 ≤ x → ∀ (y : ℝ) (n : ℕ), x ^ (y * ↑n) = (x ^ y) ^ n
Real.sqrt_eq_rpow : ∀ (x : ℝ), √x = x ^ (1 / 2)
@abs_pow_sub_pow_le : ∀ {α : Type u_1} [inst : CommRing α] [inst_1 : LinearOrder α] (a b : α) (n : ℕ) [IsOrd
@Matrix.charpoly_sub_scalar : ∀ {R : Type u_1} [inst : CommRing R] {n : Type u_2} [inst_1 : DecidableEq n] [
@Polynomial.roots_comp_C_mul_X_add_C : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDomain R] (p : Polyn
@Equiv.ofFiberEquiv_map : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → γ} {g : β → γ} (e : (c : γ
@Fintype.equivOfCardEq : {α : Type u_1} → {β : Type u_2} → [inst : Fintype α] → [inst_1 : Fintype β] → Finty
@Fintype.card_embedding_eq : ∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] [emb : 
@MeasureTheory.norm_integral_le_of_norm_le_const : ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGrou
@MeasureTheory.integral_mono_of_nonneg : ∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGroup E] [inst
@MeasureTheory.integral_indicator_const : ∀ {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X} [inst : N
@ge_of_tendsto : ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Preorder α] [ClosedIc
@le_of_tendsto : ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Preorder α] [ClosedIi
@Ioo_mem_nhdsGT : ∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α
@squeeze_zero_norm' : ∀ {α : Type u_1} {E : Type u_2} [inst : SeminormedAddGroup E] {f : α → E} {a : α → ℝ} 
@squeeze_zero' : ∀ {α : Type u_1} {f g : α → ℝ} {t₀ : Filter α}, (∀ᶠ (t : α) in t₀, 0 ≤ f t) → (∀ᶠ (t : α) i
@MeasureTheory.StronglyMeasurable.integral_prod_right' : ∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [ins
@MeasureTheory.abs_integral_le_integral_abs : ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Me
@ContDiffBump.nonneg : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : H
@ContDiffBump.le_one : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : H
@Matrix.isHermitian_zero : ∀ {α : Type u_1} {n : Type u_2} [inst : AddMonoid α] [inst_1 : StarAddMonoid α], 
@Matrix.isHermitian_one : ∀ {α : Type u_1} {n : Type u_2} [inst : NonAssocSemiring α] [inst_1 : StarRing α] 
@div_lt_div_iff_of_pos_right : ∀ {G₀ : Type u_1} [inst : GroupWithZero G₀] [inst_1 : PartialOrder G₀] [MulPo
@Real.sqrt_lt_sqrt : ∀ {x y : ℝ}, 0 ≤ x → x < y → √x < √y
@MeasureTheory.measure_toMeasurable : ∀ {α : Type u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure
@Metric.tendsto_nhds : ∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] {f : Filter β} {u : β → 
@Filter.Frequently.and_eventually : ∀ {α : Type u_1} {p q : α → Prop} {f : Filter α}, (∃ᶠ (x : α) in f, p x)

## (d) Open issues and paper-delta candidates
- T2214a (design, no paper statement) confirmed: `Step1Band.lean` imports only `Step1Good` and `Step1Cond` (import lines above); UN-11 (`Step1RegularityGUE`) is a UN-14 dependency only.
- T2214b (Lean pin shape, no change) confirmed: `UNStep1Good'` quantifies `∃ c C` after `D`; the file uses one call at `D = k + 1` (`:1024`).
- T2214c: none; no Lean statement differs from the pin of `UNInfty1` or from check section 2.
- T2214d (proof route, no paper statement): RBM2D's normalisation `r = ρ'/ρ_sc(E)`, the factor `r^k` and the dilation `ρ_sc(0)/ρ_sc(E)` are absent; the density
  sequence `ρ_n` enters through its range only and the Lipschitz step is taken at `(ρ_n, ρ'_n)` (the abstract model has no fixed `ρ_sc(E)`).
- Observation: `UNL32`/`UNGUELocal` use `Tendsto (fun n => sz.size n)` in `ℕ`, `Admissible` stores `SizeTendsto` in `ℝ`; bridged by `tendsto_natCast_atTop_iff`
  (private `Step1Band_size_tendsto`); no statement change.
- Open: `UNL32` (borrowed), `UNGUELocal`, `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`, `UNDensBandRow` stay hypotheses of the instances; the instance conclusions
  are eventual (thresholds: `step1Good'` per T2208-prove (a), the `ρ`-threshold per section (a)). For UN-14: reuse targets 1a-1d, 2 and `step1Band_row`.
