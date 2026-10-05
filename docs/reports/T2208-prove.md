Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 19:43:51 UTC 2026 (`date -u`)

Notation: `N = Nsz sz n`, `a = e^{-t*/2}`, `t* = N^{-1+τs}`, `s = e^{-t*}`, `t = 1-s`, `ζ = a⁻¹(w+E)`, `ε' = τs/8`.
Scripts are in the scratchpad `T2208/` (`pf.py`, `inst.py`, `el.py`, `num.py`; Python only, no Lean).

### (i) Exponent table

| quantity | value | constraint | slack |
|---|---|---|---|
| `𝔠 d < 1` (2a) | `(1/6)·3 = 1/2`; `(1/10)·3 = 3/10` | `W ≥ N^𝔠`, `W^d < (WL)^d = N` (`L ≥ 3`), `N → ∞`, so `N^{𝔠d} ≤ W^d < N` | `1/2`; `7/10` |
| `𝔡 ≤ d/2` (2b) | `1/10 ≤ 3/2`; `1/20 ≤ 3/2` | `WO`: `W^{𝔡-d/2} ≤ lam ≤ 𝔡⁻¹` eventually and `W → ∞` (from `W ≥ N^𝔠`, `𝔠>0`) | `1.4`; `1.45` |
| `𝔠𝔡 < 1/2 < 8/11` (2c) | `τs = 𝔠𝔡 = 1/60`; `1/200` | `𝔠𝔡 ≤ 𝔠d/2 < 1/2`; also `𝔠 < 1/d ≤ 1/3 < 1` | `1/2-𝔠𝔡 = 0.4833`; `8/11-τs = 0.7106` (`8/11 = 0.7273`) |
| floor `W^{τs/8-2𝔡} ≤ N^{-15τs/16}` | `0.015625`; `0.0046875` (true rate `𝔠(2𝔡-τs/8)`: `0.032986`; `0.009938`) | `τs ≤ 𝔠𝔡`, `𝔠<1`: `𝔠(2𝔡-τs/8) ≥ 2τs-τs/8 = 15τs/16` | vs `3τs/8`: `0.009375`; `0.002812` |
| local-law term `W^{τs/8}(N Im ζ)⁻¹ ≤ N^{τs/8}·8c₀⁻¹N^{-τs}` (uses `W ≤ N`) | `N^{-7τs/8}`: `0.014583`; `0.004375` | `Im ζ ≥ c₀t*/8` | vs `3τs/8`: `0.008333`; `0.002500` |
| `t ≤ t* = N^{-(1-τs)}` term | `0.98333`; `0.995` | `1-τs > 3τs/8` iff `τs < 8/11` | `0.9771`; `0.9931` |
| target `N^{-3τs/8}` | `0.00625`; `0.001875` | min of the three above is larger | min slack `0.008333`; `0.0025` |
| `c₁ = min(δ/(4(1+|E|)), 1/8)` | `1/8` at `δ=1/2, E=0` | `c₁ ≤ δ/(4(1+|E|))` | `0` (equality, by definition) |
| `c₀ = min(c/64, c/(16KLp), c₁/(8(K+1)))` | `9/99200 = 9.0726e-05` at `c=9/100, K=1, Lp=62` | `0 < c₀ ≤ c₁` | `c₁/c₀ = 1377.8` |
| `C₀ = 2+8LpK+K+Lp(|E|+1/4)` | `514.5` | fixed before `n, v, t, ε` (`c,K,Lp,δ,|E|` only) | n/a |
| OU time | `t*/2 ≤ t ≤ t* ≤ min(c₀,1/2)`; `a⁻¹ ≤ √2`; `a⁻¹-1 ≤ t` | `t* ≤ 1/2`; `max (a⁻¹-1)/t = 0.7218` on `t* ∈ (0,1/2]`; `√(1-t) = a` (so `Real.sqrt s` of target 4 is `a` of `vOU`) | `0.28` in `(a⁻¹-1)/t ≤ 1` |
| strip ↦ window | `|Re ζ-E| ≤ √2c₁+|E|t < δ`; `Im ζ ∈ [c₀t*/8, √2/2] ⊂ [N^{-1+ε'}, 1]` | `c₀ ≤ c₁ ≤ δ/(4(1+|E|))`: `√2/4 δ + δ/4 < δ`; `t ≥ t*/2` | `0.396δ`; `ε' = τs/8 < τs` |
| (E3) `N^{7τs/8} ≥ 8/c₀` | `ln N ≥ 780.8` at `sz0` constants | gives `c₀t/4 ≥ c₀t*/8 ≥ N^{-1+ε'}` | eventual |
| (2.2), `η ∈ [g,1/2]`, `|x| ≤ G` | `Im mV ∈ [c/2, 2K+c]` with `m_N` error `≤ N^{-15τs/16}+N^{-τs/8} ≤ c/2` (E6) | `a⁻¹ ≥ 1`, `a⁻¹ ≤ √2`; `√2(K+c/2) ≤ 2K+c`; `|Re ζ-E| ≤ √2G+|E|t* ≤ δ` (E7) | `N^{-τs/8}` dominates |
| (2.2), `η ∈ (1/2,10]` | `Im mV ≤ 1/η ≤ 2`; `η Im mV` nondecreasing so `η Im mV ≥ c/4`, `Im mV ≥ c/(4η) ≥ c/40` | `Σ η/((v_i-x)²+η²)` termwise | pin: `c_pin = c_box/40`, `C_pin = 2K+c_box+2` |
| (2.3) | `|v_i| ≤ a|λ_i|+|E| ≤ N^{CV₀}+|E| ≤ N^{CV₀+1}` | `N^{CV₀}(N-1) ≥ N-1 ≥ |E|`, `CV₀ ≥ 0`; `card = N` | eventual (E1) |
| probability | `2N^{-D-1} ≤ N^{-D}` | `N ≥ 2`; bad set `⊆` `UNTrLocal`-bad `(ε,τ,D+1) = (τs/8,τs/8,D+1)` `∪` `UNNormBound`-bad `D+1` | factor `N⁻¹ ≤ 1/2` |
| density identification | `ρ₀ = ρ n` | `UNDens` clause 3 at `n` and target 4's `ρ₀` are limits along `𝓝[>] 0` (`NeBot`), `tendsto_nhds_unique` | exact |

Consumer check (target 4, `FreeConvRegular.lean:1234-1250`): `hbox`, `hlip` are the second conjunct of `UNDens'` at `n` with `mref = m n`, `E₀ = E`, `A = |E|`; `0 < t ≤ c₀` from `t ≤ t* ≤ c₀`; `s = 1-t = e^{-t*}`; `0 ≤ ε_n ≤ c₀`, `ε_n = √2(N^{-15τs/16}+8c₀⁻¹N^{-7τs/8})` (E4); strip closeness `‖mV v w - (√s)⁻¹ m n((√s)⁻¹(w+E))‖ ≤ ε_n` follows from `mV v w = a⁻¹ m_N(ζ)` (dictionary, `Im w > 0`) and `a⁻¹ ≤ √2`. Conclusion `|ρ'-ρ n| ≤ C₀(ε_n+t) ≤ C₀(ε_n+N^{-1+τs}) ≤ N^{-3τs/8}` (E5). The pin (`PinsDens.lean:73`) is read at `D = 1` by the consumer (RBM2D `Step1Band.lean` shape), no extra hypothesis.

"Two data, one model" test (O1): on a common `ω`, `|ρ_n-ρ̃_n| ≤ (Lp+L̃p)η/π + (2/π)W^{τs/8}Bctl(1-η)` at `η = N^{-1/2}` (the Lipschitz clause plus the limit clause of `UNDens'`; closeness needs `N^{-1/2} ≥ N^{-1+τs/8}`, true), `≤ (Lp+L̃p)N^{-1/2}/π+(2/π)(N^{-15τs/16}+N^{τs/8-1/2}) ≪ N^{-3τs/8}`: exponents `1/2`, `15τs/16`, `1/2-τs/8` all exceed `3τs/8` (`τs<1`): PASS. Model side: all `λ_i` are read through (2.3) by `UNNormBound`, and `v ⊞ sc_t` near `0` through `UNTrLocal` up to `O((Nη)⁻¹)` and `UNDens'`: PASS.

### (ii) One concrete nondegenerate instance and checks

Data: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = 2097152(n+1)^18`), `(𝔠,𝔡) = (1/6,1/10)`, band model, `m = msc`, `E = 0`, `ρ = rhoSC 0 = 1/π`, `δ = 1/2`, `CV₀ = 1`, `τs = 1/60 = 𝔠𝔡 < 1`, `D = 1`. All deterministic hypotheses hold (`3 ≤ 3`; `Admissible` via `sz0_admissible`; rows above); the band rows `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow` are other gates' pins (hypotheses of the instances). The conclusion is eventual in `n` (E1-E9); the thresholds below are not hypotheses and are not used as witnesses by the instances.

Command: `python3 pf.py` (exact `Fraction` arithmetic; first block of table (i)). Output (verbatim, pairs `(1/6,1/10)`, `(1/10,1/20)`):
```
(1/6,1/10) tau=1/60 d_dim=3: c*dim=1/2<1:True; d<=dim/2:True; c*d=1/60<1/2:True<8/11:True
   floor 0.015625 (true 0.032986); local 0.014583; t-term 0.98333; target 0.006250; slacks floor 0.009375 local 0.008333 t 0.977083; min 0.008333
(1/10,1/20) tau=1/200 d_dim=3: c*dim=3/10<1:True; d<=dim/2:True; c*d=1/200<1/2:True<8/11:True
   floor 0.004687 (true 0.009938); local 0.004375; t-term 0.99500; target 0.001875; slacks floor 0.002812 local 0.002500 t 0.993125; min 0.002500
```
Command: `python3 el.py` (grid of `2·10^6` points of `t* ∈ (0,1/2]`). Output:
```
t*/2<=t<=t*: True | a^-1-1<=t: True | a^-1<=sqrt2: True | sqrt(1-t)=a: True | max (a^-1-1)/t = 0.7218489158019431
```
Command: `python3 inst.py` (mpmath, 60 digits; thresholds by bisection in `ln N`, formulas as in the ticket). Output (verbatim, trimmed to the lines used):
```
c1 0.125 c0 9.072580645161291e-05 C0 514.5 pin c=cb/40 0.00225 pin C=2K+cb+2 4.09
eta 1e-09 Im msc(i eta)/pi = 0.3183098860246357 rhoSC(0)= 0.3183098861837907
box min Im msc 0.5956802658472555 >= 0.09;  max|msc| 0.9999500012499999 <=1
sampled max Lipschitz ratio 0.5163608957959528 <= 62
E1 N>=2, N-1>=|E|: lnN >= 1.0
E2 N^{-1+t}<=min(c0,1/2): lnN >= 9.5
E3 N^{-1+t/8}<=c0 N^{-1+t}/8: lnN >= 780.8
E4 eps_n<=c0: lnN >= 1442.8
E5 C0(eps_n+N^{-1+t})<=N^{-3t/8}: lnN >= 2157.2
E6 N^{-15t/16}+N^{-t/8}<=c/2: lnN >= 1488.5
E7 sqrt2 G+|E|N^{-1+t}<=delta: lnN >= 249.5
max threshold lnN 2157.2256722319576  first n+1 = exp((lnN-ln 2097152)/18) -> ln(n+1) = 119.03719896889993
chosen ln(n+1)=130: lnN= 2354.556090791759 lnW= 653.4657359027997 W>=N^{1/6}: True W<=N: True
A=W^{2dd} <= lam^2 W^3 : ln lam^2W^3 = 392.07944154167984 >= ln A = 130.69314718055995
all E-conditions at this n: True
t*/2<=t<=t*: True  t<=c0: True
eps_true 2.204152805478351e-12 <= eps_n 1.5254042086938058e-10 <=c0 9.072580645161291e-05
rho err bound C0(eps_true+t)= 1.1340366184186116e-09 <= N^{-3t/8}= 4.0638064494306687e-07
2-data bound 6.702127122549858e-17 <= N^{-3t/8} 4.0638064494306687e-07
```
External hypothesis `UNDens'` at `msc` (limit clause): `Im msc(iη) = (√(η²+4)-η)/2 → 1`, so `Im msc(iη)/π → 1/π = rhoSC 0 = √4/(2π)` (output line `eta 1e-09` above: `0.31830988602` against `0.31830988618`); box constants `c = 9/100`, `K = 1`, `Lp = 62` are those of `un_msc_box_zero` (`PinsDens.lean:536`; the grid values above are consistent: min `Im msc = 0.596`, max `‖msc‖ = 0.99995`, sampled Lipschitz ratio `0.52`). Remark: the thresholds of ticket (iv) differ from this script's for (E4)-(E6) (ticket `1490.4, 2289.1, 1821.2`; script `1442.8, 2157.2, 1488.5` for the formulas written in the ticket); both are `ln N ≳ 2·10^3` and the instances stay eventual.

Sanity at `N = 2000` GUE (`E[|h_ij|²] = 1/N`), `E = 0.3`, `τs = 0.3`, `python3 num.py`, strip heights restricted to `Im w ≥ 30/N` (below `1/N` no local law at this `N`; (E3) fails at this `N`, so this checks shape only):
```
N=2000 t*=0.00489 t=0.00488 a=0.997558; box (sampled) c=0.561 K=0.9995 Lp=0.545; c1=0.0962 c0=0.00601 C0=7.65
eps_obs (strip) = 0.0210  (c0=0.00601; eps<=c0 needs eps small: False)
rho'(eta=0.001) = 0.31676; rho_sc(E)=0.31471; |diff|=0.00205; C0(eps_obs+t)=0.20
g=0.00088 G=0.5655: min Im mV=0.0983 (c/40=0.0140), max Im mV=1.4818 (2K+c+2=4.560); max|v_i|=2.280 <= N^(CV0+1)
a=0.99: |msc(i/a)/a - msc(i)|/(1-a) = 0.3432
a=0.999: |msc(i/a)/a - msc(i)|/(1-a) = 0.3418
```
(`|msc(i/a)/a - msc(i)| ≈ 0.342(1-a)`: finding T2208b of the ticket, not a target.) At `N = 2000`, `ε_obs > c₀`, so target 4's hypothesis `ε ≤ c₀` is not met there, as expected below the thresholds.

### Verdicts

- Target 1 (a) `stieltjesN_eq_mV`, (b) `mV_vOU`, (c) `mV_eta_mul_im_mono`, (d) `mV_im_le_inv`: PASS (spectral formula; `a⁻¹ m_N(a⁻¹(w+E))` identity; `η/((v_i-x)²+η²)` termwise; `Im(v-z)⁻¹ ≤ 1/η`).
- Target 2 (a) `un_admissible_c_mul_lt_one`, (b) `un_admissible_d_le_half`, (c) `un_admissible_cd_lt_half`: PASS (derivations in table (i); (a) needs `N > 1` at one `n`, available since `N → ∞`; (b) needs `W → ∞`).
- Target 3 (a) `step1Good'_det`: PASS (all exponents close with slack `≥ 0.0025`; constants `c_box/40`, `2K+c_box+2` fixed before `∀ᶠ n`).
- Target 3 (b) `step1Good'`: PASS (`2N^{-D-1} ≤ N^{-D}` for `N ≥ 2`).
- Target 4 instances `inst_step1Good'_band`, `inst_step1Good'_det_band`, `inst_admissible_sz0`: PASS (nondegenerate data above; `1/6·3 = 1/2 < 1`, `1/10 ≤ 3/2`, `1/60 < 1/2`).

Overall verdict: PASS.

## (a′) Preflight corrections — Mon Oct  5 20:04:32 UTC 2026 (`date -u`)

No correction changes a verdict. One difference of constants, not a mistake of (a): the Lean file bounds `a⁻¹ = e^{t*/2} ≤ 1 + t* ≤ 3/2 ≤ 2` (`Step1Good_inv_le`) where table (i) writes `√2`;
so the strip error is `ε_n = 2 (N^{-15τs/16} + 8 c₀⁻¹ N^{-7τs/8})` (not `√2 (...)`), `Im m_V ≤ 2 (K + c_box/2) = 2K + c_box`, `|Re ζ − E| ≤ (1 + t*) G + t* |E|`. Exponents, the
final constants `c = c_box/40`, `C = 2K + c_box + 2` and every size condition are of the form `N^{-e} ≤ const`, `e > 0`, as in (a).

## (b) Script output

### b.1 Build, hygiene, size (branch t/T2208, commit 48637c5; `$SP` = the scratchpad directory `T2208/`)
```
$ lake build RBM3D.Universality.Step1Good 2>&1 | grep -v '^trace' > $SP/build.log; echo "lines of the log mentioning Step1Good.lean: $(grep -c 'Step1Good.lean' $SP/build.log)"; tail -1 $SP/build.log
lines of the log mentioning Step1Good.lean: 0
Build completed successfully (3342 jobs).
$ lake build 2>&1 | tail -2
non-vacuity certificates: 0 of 145 premises in the two ledgers; the rest are not known to be satisfiable (`RBM3D/Test/InterfaceShape.lean` says what each would take)
Build completed successfully (4010 jobs).
$ wc -l RBM3D/Universality/Step1Good.lean; grep -nE 'sorry|admit|native_decide|^axiom' RBM3D/Universality/Step1Good.lean; echo "hygiene grep exit=$?"
     862 RBM3D/Universality/Step1Good.lean
hygiene grep exit=1
$ git diff --stat main...t/T2208
 RBM3D/Test/Axioms.lean            |   1 -
 RBM3D/Universality/Step1Good.lean | 862 ++++++++++++++++++++++++++++++++++++++
 2 files changed, 862 insertions(+), 1 deletion(-)
$ git diff main...t/T2208 -- RBM3D/Test/Axioms.lean | grep '^[-+]' 
--- a/RBM3D/Test/Axioms.lean
+++ b/RBM3D/Test/Axioms.lean
-   `RBM.Univ.UNStep1Good', -- bulk universality pin, primed successor of the refuted UNStep1Good (T2201, UN-01c: owed; UN-12)
```

### b.2 `#print axioms` of every public declaration, and `example : UNStep1Good' := step1Good'` (scratch file, no error output)
```
$ lake env lean scratchpad/T2208/axcheck.lean
'RBM.Univ.stieltjesN_eq_mV' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_vOU' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_eta_mul_im_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.mV_im_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_c_mul_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_d_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.un_admissible_cd_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.step1Good'_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.step1Good'' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_step1Good'_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_step1Good'_det_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Univ.Step1GoodInst.inst_admissible_sz0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### b.3 Statement diff: check-file section 2 bodies against the file (`python3 stmtdiff.py`; whitespace and `Type*`/`Type` normalised)
```
IDENTICAL: 12 of 12 (after Type*->Type and whitespace normalisation): stieltjesN_eq_mV mV_vOU mV_eta_mul_im_mono mV_im_le_inv un_admissible_c_mul_lt_one un_admissible_d_le_half un_admissible_cd_lt_half step1Good'_det step1Good' inst_step1Good'_band inst_step1Good'_det_band inst_admissible_sz0
DIFFERENT: none
```

### b.4 Target statements, extracted from the file by script (whitespace collapsed, wrapped at 170)
```
L79 theorem stieltjesN_eq_mV : ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ}, 0 < z.im → stieltjesN H z = mV hH.eigenvalues z
L133 theorem mV_vOU : ∀ {d : ℕ} (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E : ℝ) (ω : Sizes.SeqΩ sz) {w : ℂ}, 0 < w.im → mV (vOU sz M n τs E ω) w = ((Real.exp (-(ouTStar sz
    τs n) / 2) : ℝ) : ℂ)⁻¹ * stieltjesN (M.H n ω) (((Real.exp (-(ouTStar sz τs n) / 2) : ℝ) : ℂ)⁻¹ * (w + E))
L161 theorem mV_eta_mul_im_mono : ∀ {ι : Type*} [Fintype ι] (v : ι → ℝ) (x η η' : ℝ), 0 < η → η ≤ η' → η * (mV v ⟨x, η⟩).im ≤ η' * (mV v ⟨x, η'⟩).im
L179 theorem mV_im_le_inv : ∀ {ι : Type*} [Fintype ι] (v : ι → ℝ) (x η : ℝ), 0 < η → (mV v ⟨x, η⟩).im ≤ 1 / η
L209 theorem un_admissible_c_mul_lt_one : ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * (d : ℝ) < 1
L218 theorem un_admissible_d_le_half : ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → 𝔡 ≤ (d : ℝ) / 2
L234 theorem un_admissible_cd_lt_half : ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, 0 < d → sz.Admissible 𝔠 𝔡 → 𝔠 * 𝔡 < 1 / 2
L657 theorem step1Good'_det : ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E : ℝ) (ρ : ℕ → ℝ) (δ : ℝ), UNDens' m E ρ δ →
    ∀ CV₀ : ℝ, 0 ≤ CV₀ → ∀ τs : ℝ, 0 < τs → τs < 1 → τs ≤ 𝔠 * 𝔡 → ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz, (∀ z : ℂ, |z.re - E| ≤ δ → Nsz sz n ^ (-1 + τs /
    8) ≤ z.im → z.im ≤ 1 → ‖stieltjesN (M.H n ω) z - m n z‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (τs / 8) * sz.Bctl n (1 - z.im)) → (∀ i, |(M.herm n ω).eigenvalues i| ≤ Nsz sz n ^ CV₀)
    → (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4)) (Nsz sz n ^ (-(min (τs / 4) ((1 - τs) / 3)))) c C (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs
    E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - ρ n| ≤ Nsz sz n ^ (-(3 * τs / 8)))
L757 theorem step1Good' : UNStep1Good'
L813 theorem inst_step1Good'_band : UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow → ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, (UNModel.band sz0).μ {ω | ¬
    (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4)) (Nsz sz0 n ^ (-(min ((1 / 60 : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C
    (CV₀ + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (1 - Real.exp (-(ouTStar sz0 (1 / 60) n))) mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ =>
    (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))} ≤ ENNReal.ofReal (Nsz sz0 n ^ (-(1 : ℝ)))
L835 theorem inst_step1Good'_det_band : ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ ω : Sizes.SeqΩ sz0, (∀ z : ℂ, |z.re - 0| ≤ 1 / 2 → Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 8) ≤ z.im →
    z.im ≤ 1 → ‖stieltjesN ((UNModel.band sz0).H n ω) z - msc z‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ ((1 / 60 : ℝ) / 8) * sz0.Bctl n (1 - z.im)) → (∀ i, |((UNModel.band sz0).herm n
    ω).eigenvalues i| ≤ Nsz sz0 n ^ (1 : ℝ)) → (IsRegular32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (Nsz sz0 n ^ (-1 + (1 / 60 : ℝ) / 4)) (Nsz sz0 n ^ (-(min ((1 / 60
    : ℝ) / 4) ((1 - (1 / 60 : ℝ)) / 3)))) c C (1 + 1) ∧ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz0 (UNModel.band sz0) n (1 / 60) 0 ω) (1 - Real.exp (-(ouTStar sz0 (1 / 60) n)))
    mfc ∧ ∃ ρ' : ℝ, Tendsto (fun η : ℝ => (mfc ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ') ∧ |ρ' - rhoSC 0| ≤ Nsz sz0 n ^ (-(3 * (1 / 60 : ℝ) / 8)))
L853 theorem inst_admissible_sz0 : (1 / 6 : ℝ) * ((3 : ℕ) : ℝ) < 1 ∧ (1 / 10 : ℝ) ≤ ((3 : ℕ) : ℝ) / 2 ∧ (1 / 6 : ℝ) * (1 / 10) < 1 / 2
```

### b.5 Registry pre-check (CLAUDE.md §20 (2)): temporary uncommitted `precheck.lean` = `import RBM3D`, `import RBM3D.Universality.Step1Good`, `#assert_rbm_axioms`
```
$ lake env lean scratchpad/T2208/precheck.lean   # exit code and selected lines of its output
axiom audit: 6106 theorems, 2163 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
premises found by scanning: 129 (borrowed 1, owed 100, structural 24, refuted 4).
registry: 2 borrowed + 143 owed + 79 structural + 4 refuted; 99 registered premise(s) carry nothing yet: [RBM.Loop.KLPT,
exit=0
$ grep -n 'UNStep1Good' /private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/85663390-cb91-4af2-a115-d95547c1e2fb/scratchpad/T2208/precheck.out | cut -c1-120
129:  RBM.Univ.UNStep1GoodC': 0 [no certificate]
195: RBM.Univ.UNStep1GoodC',
$ python3 scratchpad/T2208/regcount.py
owedProps entries: main cda3bb2 = 144  branch = 143
only on main: ["RBM.Univ.UNStep1Good'"]  only on branch: []
```

### b.6 Name-clash grep of the 13 new public names and the helper prefix `Step1Good_`
```
$ bash scratchpad/T2208/clash2.sh   # 14 names/prefixes: grep -rnF over RBM3D/, RBM3D.lean (non-Probe, outside the new file) and docs/tickets (outside T2208 files)
names/prefixes checked: 14; total hits in RBM3D/ and RBM3D.lean (non-Probe, outside Step1Good.lean): 0; total hits in docs/tickets outside T2208 files: 0
```

### b.7 Port from RBM2D (read-only; source commit as pinned by the ticket)
```
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/Step1RegularityB.lean
 RBM2D/Universality/Step1RegularityB.lean | 133 +++++++------------------------
 1 file changed, 28 insertions(+), 105 deletions(-)
$ git -C /Users/junyin/Lean_proof/RBM2D --no-optional-locks show c9a24cf:RBM2D/Universality/Step1RegularityB.lean | wc -l
     906
$ bash scratchpad/T2208/portmap.sh   # port map, line numbers of the c9a24cf blob and of the new file
RBM2D(c9a24cf) Step1RegularityB.lean:74 Step1RegularityB_exp_le_one  ->  Step1Good.lean:244 Step1Good_exp_le_one
RBM2D(c9a24cf) Step1RegularityB.lean:113 Step1RegularityB_sqrt_exp  ->  Step1Good.lean:280 Step1Good_sqrt_exp
RBM2D(c9a24cf) Step1RegularityB.lean:129 Step1RegularityB_stieltjesN_eq_mV  ->  Step1Good.lean:79 stieltjesN_eq_mV
RBM2D(c9a24cf) Step1RegularityB.lean:147 Step1RegularityB_mV_vOU  ->  Step1Good.lean:107 Step1Good_mV_affine
RBM2D(c9a24cf) Step1RegularityB.lean:178 Step1RegularityB_mV_norm_le  ->  Step1Good.lean:179 mV_im_le_inv
RBM2D(c9a24cf) Step1RegularityB.lean:657 Step1RegularityB_strip  ->  Step1Good.lean:333 Step1Good_strip
RBM2D(c9a24cf) Step1RegularityB.lean:531 Step1RegularityB_regular  ->  Step1Good.lean:423 Step1Good_regular
RBM2D(c9a24cf) Step1RegularityB.lean:728 Step1RegularityB_rpow_ev  ->  Step1Good.lean:283 Step1Good_rpow_ev
RBM2D(c9a24cf) Step1RegularityB.lean:737 Step1RegularityB_det  ->  Step1Good.lean:657 step1Good'_det
RBM2D(c9a24cf) Step1RegularityB.lean:817 step1Good_highProb  ->  Step1Good.lean:757 step1Good'
```

### b.8 Narrative

- Delivered: `RBM3D/Universality/Step1Good.lean` (new, 862 lines) and one deleted line in `RBM3D/Test/Axioms.lean`, commit 48637c5 on `t/T2208` (commit time 20:01:28 UTC by `git log`). All 12 public declarations of ticket targets 1-4
  compile; their statement bodies are identical to check section 2 (b.3); `step1Good'` has type exactly `UNStep1Good'` (b.2, the `example` compiles); axioms are the three standard ones.
- Proof shape (file sections): 1 dictionary and `mV` bounds; 2 `Admissible` arithmetic; 3 elementary facts on `a = e^{-T/2}`, `t = 1 - e^{-T}`; 4 `Step1Good_bctl` (local-law precision from `un_Bctl_le`, `un_step1_floor`),
  `Step1Good_strip` (closeness hypothesis of target 4), `Step1Good_regular` ((2.2), (2.3)), `Step1Good_rate`, `Step1Good_at_n` (all of Step 1 at one `n`, `ι` generic); 5 `step1Good'_det`, `step1Good'`; 6 instances.
- Mathematical content as in (a): `c₀ c₁ C₀` from `freeConv_stable_lip cb K Lp δ |E|` before `∀ᶠ n`; pin constants `c = cb/40`, `C = 2K + cb + 2`; `mfc := freeConvST v t` with `isFreeConv51_freeConvST`; `ρ₀ = ρ n` by
  `tendsto_nhds_unique` with the third clause of `UNDens`; `(2.3)` from `|v_i| ≤ N^{CV₀} + |E| ≤ N^{CV₀+1}` using `N ≥ |E| + 2`; probability: bad set `⊆` `UNTrLocal`-bad `(τs/8, τs/8, D+1)` `∪` `UNNormBound`-bad `(D+1)`,
  `measure_union_le`, `2 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 2`.
- The nine eventual size conditions are `N^{-e} ≤ const` (`Step1Good_rpow_ev`, `SizeTendsto`), plus `N ≥ |E| + 2`, `Bandwidth`, `WO` and the two `UNDens'` clauses at `n`; the three exponent gaps used in `Step1Good_rate` are
  `9τs/16`, `τs/2`, `1 − 11τs/8`; the last is positive iff `τs < 8/11`, which is where `un_admissible_cd_lt_half` (`𝔠𝔡 < 1/2`) is used. No concrete `n` is exhibited (DECISIONS §56; (a) ii gives `ln N ≳ 2·10^3`).
- Reuse: 2a uses the merged `un_dc_lt_one` (`Pins.lean:1011`) at one `n` from `Bandwidth`; 2b uses a private copy of the 4-line proof of `scaleFacts3_W_tendsto` (`ScaleFacts3.lean:410`, not imported);
  1a uses the public `InjSum_stieltjesN_eq_stieltjes` (`InjSum.lean:192`) and a private copy of `InjSum_green_eq_spectral` (`InjSum.lean:43`); only 3 of the 4 conjuncts of target 4 are used.
- Instances: `inst_step1Good'_band` applies `step1Good'` at `sz0`, `UNModel.band sz0`, `msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/2`, `τs = 1/60`, `D = 1`; discharged: `sz0_adm`, `un_dens'_msc_zero`, `3 ≤ 3`, `|0| ≤ 2 - 1`, `0 < 1/2 ≤ 1/2`,
  `0 < 1/60 < 1`, `1/60 ≤ (1/6)(1/10)`, `0 < 1`; left as hypotheses (other gates' pins): `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`. `inst_step1Good'_det_band` keeps the two `ω`-hypotheses of `step1Good'_det`.
  `inst_admissible_sz0` is proved from targets 2a-2c and `sz0_adm`, not by `norm_num` on the numbers. No `N = 0`, empty index, collapsed window or contradictory hypothesis.
- Not targets, not touched: `UNStep1GoodC'`, `vOUC`, `ouInit`, `UNInfty1Row'`, `step1Band`, the band rows, any merged file. The ticket's findings T2208a/T2208b were not examined here and nothing in this report supports or refutes them.
- Registry (b.5): `UNStep1Good'` is out of `owedProps` (144 → 143 entries, only that name differs) and out of the "carry nothing yet" list; the pre-check exits 0; the root import of `RBM3D.Universality.Step1Good` is the hub's at merge.
- Port: source text read with `git show c9a24cf:...` (906 lines, as pinned); RBM2D `HEAD` is 9e0f275 and the file differs there (b.7); nothing in RBM2D was written, built or imported. Scratch files (`axcheck.lean`, `precheck.lean`, `names.lean`, scripts) are in the scratchpad `T2208/`, uncommitted.

## (c) Verified Mathlib names used (all present in the import closure of `RBM3D.Universality.Step1Good`)

```
$ lake env lean scratchpad/T2208/names.lean   # `env.contains` of each name; 49 true, 0 false
Real.exp_half, Real.add_one_le_exp, Real.exp_lt_exp, Real.exp_le_one_iff, Real.rpow_le_rpow_of_exponent_le, Real.rpow_le_rpow, Real.rpow_add, Real.rpow_neg,
Real.rpow_neg_one, Real.rpow_one, Real.one_le_rpow, Real.rpow_pos_of_pos, Real.rpow_nonneg, Real.norm_of_nonneg, tendsto_rpow_atTop, tendsto_rpow_neg_atTop,
Filter.tendsto_atTop_mono', tendsto_nhds_unique, Filter.Tendsto.eventually_ge_atTop, Filter.Tendsto.eventually_gt_atTop, Filter.Eventually.exists,
MeasureTheory.measure_mono, MeasureTheory.measure_union_le, ENNReal.ofReal_add, ENNReal.ofReal_le_ofReal, Nat.le_self_pow, Nat.le_mul_of_pos_right, Complex.inv_im,
Complex.normSq_apply, Complex.im_ofReal_mul, Complex.re_ofReal_mul, Complex.im_sum, Complex.abs_im_le_norm, Complex.norm_real, Matrix.trace_mul_comm,
Matrix.trace_diagonal, Matrix.inv_eq_right_inv, Unitary.coe_star_mul_self, inv_anti₀, inv_le_iff_one_le_mul₀, one_le_inv₀, le_div_iff₀, div_le_div_iff₀, div_le_iff₀,
pow_le_pow_left₀, one_div_le_one_div_of_le, div_le_div_of_nonneg_left, Set.mem_ofPred_eq, Set.mem_setOf_eq
false: none
```
Note: `Set.mem_setOf_eq` is deprecated in this Mathlib (warning when `lake env lean` first compiled the file with it: "Use `Set.mem_ofPred_eq` instead"); the file uses `Set.mem_ofPred_eq`.

## (d) Open issues and paper-delta candidates

- No Lean/pin statement difference was needed: each statement is the check-file body and `step1Good'` is `UNStep1Good'` (b.3, b.2).
- **T2208c** (ticket text, docstring only; now compiled): the term `C₀ t`, `t ≤ N^{-1+τ_s}`, needs `τ_s < 8/11`; the pin's `τ_s < 1` does not give it, `Admissible` does: `un_admissible_cd_lt_half` gives `τ_s ≤ 𝔠𝔡 < 1/2`
  (from `un_admissible_c_mul_lt_one` `𝔠 d < 1` and `un_admissible_d_le_half` `𝔡 ≤ d/2`).
- Mathlib API note for `docs/mathlib-api.md`: `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`.
- Consumers: UN-13 reads `step1Good'` at `D = 1`; `step1Good'_det` is public for a deterministic form on a fixed `ω`; all other helpers are `private` or prefixed `Step1Good_` (b.6: 0 clashes).
- Open for the dispatcher: T2208a/T2208b and UN-12b (C form) are outside this ticket; root import by the hub; the instances stay eventual in `n`.
