Prover model: claude-sonnet-5-5

## (a) Math preflight — Tue Oct  6 03:41:36 UTC 2026

Notation: `W = sz.W n`, `λ = sz.lam n`, `N = (W L)^d`, `η = η_Q = W^{-ε₀} λ W^{d/2}/N`, `B = 𝓑_{η,0}`, `d ≥ 3`.
Paper: `1_2:406-420` (MR:QUE, `(eq:defIE)`), `1_2:512-545` (`(eq:BetaK)`, `(ssfa2)`, `(ssfa2_deter)`, final Markov).

### (i) Exponent table

Paper chain (`1_2:539-543`) read against the pinned `queChain`: `N²η² K = C W^{-2ε₀}` exactly (`(Nη)² = W^{-2ε₀} λ² W^d`, `K = C λ^{-2} W^{-d}`);
`16 N²η² ε ≤ 64 W^{τ/2}((λ²W^d)^{-1/5} + 2(Nη)^{-1})` (needs `B ≤ 2(Nη)^{-1}`, `B ≥ 0`); `(λ²W^d)^{-1/5} ≤ W^{-2𝔡/5}`
(`lam_sq_mul_pow_ge`); `(Nη)^{-1} = W^{ε₀}/(λ W^{d/2}) ≤ W^{ε₀-𝔡}` (`(eq:WO)`); total
`≤ W^{2c+τ/2}·max(16C,128)·(W^{-2ε₀}+W^{ε₀-𝔡}+W^{-2𝔡/5}) ≤ W^{2c+τ/2}·3max(16C,128)·W^{-min(2ε₀,2𝔡/5)} ≤ W^{-min+2c+τ}` once `W^{τ/2} ≥ 3max(16C,128)`.

| quantity | value (instance) | constraint | slack |
|---|---|---|---|
| `𝔠, 𝔡` | `1/6, 1/10` | `Admissible`: `0<𝔠,𝔡`, `N→∞`, `W ≥ N^𝔠`, `W^{-d/2+𝔡} ≤ λ ≤ 𝔡⁻¹` | `sz0_admissible` (merged) |
| `κ` | `1/10` | `0 < κ`; `|E| ≤ 2-κ` | n/a |
| `ε₀` | `1/30` | `0 < ε₀ < 𝔡/2` (QUE hyp.) | `1/60` |
| `ε₀` vs `3𝔡/5` | `1/30 ≤ 3/50` | `que_three_terms`: `ε₀ ≤ 3𝔡/5` (iff `ε₀-𝔡 ≤ -2𝔡/5`) | `2/75` (= `𝔡/10` at `ε₀ = 𝔡/2`) |
| `ε₀` vs `𝔡` | `1/30 < 1/10` | `queDomain`: `ε₀ < 𝔡` | `1/15` |
| `ε_Q = 𝔠(𝔡-ε₀)` | `1/90` | `0 < ε_Q` for `QDiff`'s `ε`; `η_Q N ≥ N^{ε_Q}` (`W^{𝔡-ε₀} ≥ N^{𝔠(𝔡-ε₀)}`) | `ε_Q > 0` since `𝔠>0, ε₀<𝔡` |
| `c` | `1/60` | QUE hyp. `0<c<ε₀∧𝔡/5`; **unused by `queChain`** (any real `c`, `W^{-2c}>0`) | `1/60` (to `ε₀`), `1/300` (to `𝔡/5`) |
| `τ` | `1/10` (`τ/2 = 1/20` into `QDiff`, `D = 1`) | `0 < τ` | n/a |
| `min(2ε₀, 2𝔡/5)` | `min(1/15, 1/25) = 1/25` | exponent of `queBound` | n/a |
| final exponent `-min+2c+τ` | `7/75 ≈ +0.0933` | matches merged `queBound` | positive: see remark (b) |
| 3 terms `ε₀-𝔡, -2𝔡/5, -2ε₀` | `-1/15, -1/25, -1/15` | each `≤ -min = -1/25` | `2/75, 0, 2/75` |
| `W^{τ/2} ≥ 3max(16C,128)` | `C=1`: `≥ 384`; at `sz0` (`W=(2(n+1))^5`): `n+1 ≥ 384⁴/2 ≈ 1.09·10^{10}` | eventual, from `tendsto_W` | conclusion only (`∀ᶠ n`) |
| `η ≤ 1` | `η_Q(n=0) = 1.2016·10⁻⁶` | `0<η≤1` for `queFixed`/`queDomain` | `≈ 10⁶` |
| `η ≤ λ²/L^d` | `etaQ_le`: `W^{-ε₀-d/2} ≤ λ` from `λ ≥ W^{-d/2+𝔡}` | `calB_le_two_inv` | factor `W^{𝔡+ε₀}` |
| `ΔΘ` bound | `C(3, 𝔡, κ)` from `thetaDiff`, `‖m‖² < 1` (`norm_msc_lt_one`, `Im z > 0`) | `K = C λ^{-2} W^{-d}`, `C` independent of `(sz,n)` | n/a |
| `QDiff` decay of `ε` at `sz0` | `ε_Q(n) ~ x^{-3.0167}`, `x = 2(n+1)` (`W = x⁵`: `W^{1/20}·x^{-8/3}·x^{-3/5}`) | `qdBoundExp → 0` | numerics below |

Pin truth, symbolic in `d ≥ 3`: `queRowDiff` true (`profPM a b - profPM a b' = |m|²(Θ_ab-Θ_ab')/W^d`, `‖profPP‖` factor `‖m²‖ = ‖m‖²`, `ThetaPM = Theta d L λ (‖m‖²)` by `rfl`, `L ≥ 3`). `queFixed` true: window `queWindow … x ↔ |x-E| ≤ η_Q` is the definitional unfolding (`Nsz sz n = ((W L)^d : ℕ)`); `queMarkov` with `f = 4N²η² X`, `s = W^{-2c}`, `T = 4N²η²·4(K+ε)` gives exactly the pinned `ofReal(4N²η²(4(K+ε))/W^{-2c})`; `queX_core` supplies `∫X ≤ 4(K+ε)`, `X ≥ 0` (its hypotheses are the pinned `hQ`, `hK`; `∑c = 1` for `δ_a` and `1_A/|A|`). `queChain` true (needs only `d ≥ 3`, `ε₀ ≤ 3𝔡/5`, `τ>0`, `C>0`, `WO`, `W→∞`).

### (ii) One concrete nondegenerate instance

Data: `d = 3`, `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`), `(𝔠,𝔡,κ) = (1/6,1/10,1/10)`, `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10`, `C = 1`; `queRowDiff`/`queFixed` at `n = 0` (`L=4, W=32, λ=1/64, N=2097152`, `z = zI = 1/2 + i N^{-4/5}` for `queRowDiff`; `z = η_Q i` for `queFixed`, `E=0`); `queChain`/`QUE_of_QDiff` at `n+1 = 10^11` (above the threshold `≈ 1.09·10^{10}`).

Command: `python3 .../scratchpad/T2248/inst.py` and `steps.py` (mpmath, 80 digits, exact formulas for `η, 𝓑_{η,0}, qdBoundExp`; `calB = (λ²+η)^{-1}/(W²(K+W)^{d-2}) + 1/(Nη)`, `K=0`).

```
e0 < fd/2: 1/30 < 1/20 slack 1/60
e0 <= 3fd/5: 1/30 <= 3/50 slack 2/75
c<e0: 1/60 1/30 slack 1/60  c<fd/5: 1/50 slack 1/300
eps_Q = fc(fd-e0) = 1/90
min(2e0,2fd/5)= 1/25  final exponent -min+2c+tau = 7/75 0.09333333333333334
max exponent of 3 terms: e0-fd, -2fd/5, -2e0 = -1/15 -1/25 -1/15  all <= -min: True
n= 0  W^(tau/2)= 1.18921  lhs= 57.76698  rhs= 1.3819129  lhs<=rhs: False  16N^2eta^2K/(16C W^-2e0)= 1.0
   hyps: {'WO_lo': True, 'WO_hi': True, 'etaQ_le': True, 'Wtau': False, 'Bineq': True, 'bw': True, 'dom': True}
n= 10000  W^(tau/2)= 11.8924  lhs= 5.6764815  rhs= 101.66409  lhs<=rhs: True  16N^2eta^2K/(16C W^-2e0)= 1.0
   hyps: {... 'Wtau': False, ...}
n= 99999999999  W^(tau/2)= 668.74  lhs= 0.34482718  rhs= 187851.21  lhs<=rhs: True  16N^2eta^2K/(16C W^-2e0)= 1.0
   hyps: {'WO_lo': True, 'WO_hi': True, 'etaQ_le': True, 'Wtau': True, 'Bineq': True, 'bw': True, 'dom': True}
n= 999999999999999  W^(tau/2)= 6687.4  lhs= 0.070133426  rhs= 13819129.0  lhs<=rhs: True  16N^2eta^2K/(16C W^-2e0)= 1.0
n=0: W,L,lam,N = 32.0 4 0.015625 2097152.0  eta_Q = 1.2015543e-6  0<eta<=1: True
slope of log eps_Q(sz0) vs log x: -3.0166667 (predicted -3.0167: 0.25-8/3-0.6)
--- steps.py at n+1 = 10^11 (each True) ---
16N2eta2*eps <= 64W^(t/2)((lam2W^d)^-1/5+2/(N eta)): True
<= 64W^(t/2)(W^(-2fd/5)+2W^(e0-fd)): True
W^(tau/2)(16C W^-2e0 + s3/W^(t/2)) <= W^(t/2) max(16C,128)(3 terms): True (s3 + 16C term): True
<= W^(t/2)*3max*W^-min: True  and 3max <= W^(t/2): True
total/Markov-chain value: 0.34482718 <= W^(-min+2c+tau)= 187851.21 True
```
(`hyps` keys: `WO_lo: W^{-3/2+𝔡} ≤ λ`, `WO_hi: λ ≤ 𝔡⁻¹ = 10`, `etaQ_le: η ≤ λ²/L^d`, `Wtau: W^{τ/2} ≥ 384`, `Bineq: B ≤ 2/(Nη)`, `bw: W ≥ N^{1/6}`, `dom: N^{-1+𝔠(𝔡-ε₀)} ≤ η ≤ 1`.)

Hypothesis check per target (all hold at the data above):
- `queRowDiff` (`d=3, 𝔡=κ=1/10`): `0<λ=1/64 ≤ 10`; `zI.im = N^{-4/5} ∈ (0,1]`, `|zI.re| = 1/2 ≤ 19/10` (merged `zI_im_pos, zI_im_le, zI_re_le`).
- `queFixed`: `0 < η_Q = 1.2016·10⁻⁶ ≤ 1`; `K ≥ 0`; the expectation half is another gate's pin (`QDiff`, owed), kept as hypothesis; the `hK` half is discharged by `queRowDiff` (`C` exists).
- `queChain`: `3 ≤ d`, `Admissible` (`sz0_admissible`), `ε₀ = 1/30 < 1/20`, `τ > 0`, `C = 1 > 0`; conclusion eventual, true from `n+1 ≳ 1.1·10^{10}`.
- `QUE_of_QDiff`: `QDiff` (owed, external hypothesis); `QDiff` instantiated at `(κ, ε, τ/2, D) = (1/10, 1/90, 1/20, 1)`: `ε>0`, `τ/2>0`, `D>0` hold.
- `queDomain`, `calB_le_two_inv`, `que_three_terms`, `etaQ_le`: compiled at `97d958e`; instances `inst_queDomain`, `inst_BetaK` (`η = 3·10⁻⁶ ≤ λ²/L^d = 3.81·10⁻⁶`), `inst_three_terms` (`W = 32`) are the probe's.

External hypothesis `QDiff` (TEAM §8 lesson 14), concrete limit computation at `sz0`: `Admissible` limits: `N = 8 x^{18} → ∞`; `W = x⁵ ≥ N^{1/6} = 2^{1/2} x³` for `x ≥ 2`; `W^{-7/5} = x^{-7} ≤ λ = x^{-6} ≤ 10`. The right side of `QDiff`'s expectation half at `z = E + iη_Q`, `τ → τ/2`: `ε_Q(n) = W^{τ/2}B²((λ²W^d)^{-1/5}+B) ~ x^{-3.0167} → 0` (slope printed above), so the hypothesis is not vacuous-by-blow-up and the chain value `16N²η²(K+ε)W^{2c}` (`0.345` at `n+1=10^{11}`, `0.070` at `n+1=10^{15}`) stays below `W^{7/75}`.

### Verdicts

- `MAQUE` / `QUE_of_QDiff`: PASS. The chain agrees with `1_2:539-543`: `W^{τ+2c}(W^{-𝔡+ε₀} + W^{-2𝔡/5} + W^{-2ε₀})`; no `T2248a` candidate (D500, D503, D504 are the consumers' deltas; the unused `0<c`, `c<ε₀`, `c<𝔡/5` are a remark).
- Verbatim probe pins `queDomain`, `calB_le_two_inv`, `que_three_terms`, `etaQ_le`: PASS (statements true; exponent rows above).
- `queRowDiff`: PASS (constant `C` of `thetaDiff`, independent of `(sz,n)`; `‖m‖² ≤ 1`).
- `queFixed`: PASS (Markov constant `4N²η²·4(K+ε)/W^{-2c}` and window identity as above).
- `queChain`: PASS (`ε₀ ≤ 3𝔡/5` suffices; `c` any real; symbolic in `d ≥ 3`; numerics above).
- Instances `inst_queRowDiff`, `inst_queChain`, `inst_queFixed`, `inst_QUE_of_QDiff`, probe four: PASS.

Remarks (observations, not defects):
(a) At the pinned instance data the chain inequality is **false at `n = 0`** (lhs `57.77 > rhs 1.38`) because `W^{τ/2} = 1.19 < 384`: `inst_queChain` must stay `∀ᶠ n` (as pinned); do not discharge it at `n = 0`.
(b) At `(c, τ) = (1/60, 1/10)` the exponent `-min+2c+τ = +7/75 > 0`, so `queBound > 1` and the QUE conclusion of `inst_QUE_of_QDiff` is a trivial bound at these numerals; it is the same data as the merged `inst_QUE` (`Endpoints.lean:575`). The statement of `QUE_of_QDiff` is not affected (`2c+τ < 2𝔡/5` is available to the general theorem; e.g. `c = 1/200, τ = 1/100` gives exponent `-1/50`).
(c) Registry: `MAQUE` is a new Prop-valued def used only as the type of `QUE_of_QDiff` (its hypotheses are `QDiff`, owed, and structural `Admissible`, `locDomain`, `queWindow`); the merged `MAThetaDiff` has no registry line either: expected none.

## (b) Script output — Tue Oct  6 03:50:17 UTC 2026

```
$ git log -1 --format="%h %an" ; git diff --stat main...t/T2248
f1fbd44 Jun Yin
 RBM3D/Main/QUEFromQDiff.lean | 664 +++++++++++++++++++++++++++++++++++++++++++
 1 file changed, 664 insertions(+)
$ lake build RBM3D.Main.QUEFromQDiff 2>&1 | tail -2   (warnings in this file: only longLine, lines 15-44 = the module docstring that precedes `set_option linter.style.longLine false`)
Build completed successfully (3728 jobs).
exit=0
non-longLine warnings in this file: 0
$ lake build   (whole library, incl. #assert_rbm_axioms; worktree t/T2248)
Build completed successfully (4051 jobs).
exit=0
$ python3 verb.py   # byte-equal blocks in RBM3D/Main/QUEFromQDiff.lean (git show 97d958e:Probe/T2192Pins.lean, main:Endpoints.lean)
Endpoints:218-227 True
probe:1864-2022 True
probe:2386-2393 True
probe:2447-2451 True
probe:2476-2488 True
$ lake env lean check_eq.lean   # check file + import QUEFromQDiff + 18 examples (etaQ, MAQUE_pin, 8 Y_pin, 8 Z_pin)
exit=0 ; error lines: 0 ; examples: 18
$ lake env lean reg.lean   # import RBM3D, RBM3D.Main.QUECore, RBM3D.Main.QUEFromQDiff, #assert_rbm_axioms
axiom audit: 7330 theorems, 2475 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
All within [propext,
 Classical.choice,
exit=0 (no new registry line needed)
$ lake env lean ax.lean   # #print axioms of every public declaration
'RBM.Endpoints.etaQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.calB_le_two_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.que_three_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.etaQ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queRowDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.queChain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.QUE_of_QDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.queDomain_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_BetaK' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_three_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queRowDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queChain' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_queFixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'RBM.Endpoints.Inst.inst_QUE_of_QDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
$ grep -cE "sorry|admit|native_decide|^axiom" RBM3D/Main/QUEFromQDiff.lean
0
$ clash grep: git grep -nE "(def|theorem|lemma|abbrev) +(<18 public names, queChain_real, queFromQDiff_inst_etaQ>)" main -- RBM3D/*.lean (not Probe/) | wc -l
       0
```

### Target statements (extracted by script: declaration line through the first `:=`)
```lean
theorem queDomain (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ κ : ℝ} (hε₀ : 0 < ε₀) (hε₀𝔡 : ε₀ < 𝔡) :
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
      sz.locDomain κ (𝔠 * (𝔡 - ε₀)) n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) := by

theorem calB_le_two_inv (sz : Sizes d) (n : ℕ) (hd : 2 ≤ d) {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K)
    (hηL : η ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d) (hlam : 0 < sz.lam n) :
    calB sz n η K ≤ 2 * (Nsz sz n * η)⁻¹ := by

theorem que_three_terms {x ε₀ 𝔡 : ℝ} (hx : 1 ≤ x) (hε₀ : 0 < ε₀) (h𝔡 : 0 < 𝔡) (hε : ε₀ ≤ 3 * 𝔡 / 5) :
    x ^ (ε₀ - 𝔡) + x ^ (-(2 * 𝔡 / 5)) + x ^ (-(2 * ε₀)) ≤ 3 * x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5))) := by

theorem etaQ_le (sz : Sizes d) (n : ℕ) {ε₀ 𝔡 : ℝ} (hε₀ : 0 < ε₀) (h𝔡 : 0 < 𝔡)
    (hW1 : 1 ≤ ((sz.W n : ℕ) : ℝ))
    (hlo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n) :
    etaQ sz n ε₀ ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by

def MAQUE : Prop := QDiff → QUE

theorem queRowDiff : ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d (sz.L n),
        ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
        ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by

theorem queFixed : ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ),
    z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I → 0 < etaQ sz n ε₀ →
    (∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε) →
    (∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K) →
    (∀ a : Zd d (sz.L n),
      Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) := by

theorem queChain : ∀ {d : ℕ}, 3 ≤ d → ∀ {𝔠 𝔡 : ℝ} (sz : Sizes d), sz.Admissible 𝔠 𝔡 →
    ∀ ε₀ c τ C : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < τ → 0 < C →
      ∀ᶠ n in atTop,
        4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
            (4 * (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d + qdBoundExp sz n (τ / 2) (etaQ sz n ε₀))) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ) := by

theorem QUE_of_QDiff : MAQUE := by

```

### Compiled nonempty instances (the four new ones; the four probe ones are byte-equal, see verb.py)
```lean
theorem inst_queRowDiff : ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Zd 3 (sz0.L 0),
    ‖profPM sz0 0 zI a b - profPM sz0 0 zI a b'‖ ≤ C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 ∧
    ‖profPP sz0 0 zI a b - profPP sz0 0 zI a b'‖ ≤ C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 := by

theorem inst_queChain :
    ∀ᶠ n in atTop,
      4 * Nsz sz0 n ^ 2 * etaQ sz0 n (1 / 30) ^ 2 *
          (4 * (1 * (sz0.lam n ^ 2)⁻¹ / ((sz0.W n : ℕ) : ℝ) ^ 3 +
            qdBoundExp sz0 n (1 / 10 / 2) (etaQ sz0 n (1 / 30)))) /
        ((sz0.W n : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))) ≤
      ((sz0.W n : ℕ) : ℝ) ^ (-(min (2 * (1 / 30 : ℝ)) (2 * (1 / 10 : ℝ) / 5)) + 2 * (1 / 60) + 1 / 10) :=

theorem inst_queFixed :
    ∀ (z : ℂ), z = ((0 : ℝ) : ℂ) + (etaQ sz0 0 (1 / 30) : ℂ) * Complex.I → ∀ ε : ℝ,
    (∀ a b : Zd 3 (sz0.L 0),
      ‖(∫ ω, avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
          profPM sz0 0 z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz0 0 (fun x y => sz0.Gn 0 z ω x y * sz0.Gn 0 z ω y x) a b ∂(Sizes.seqP sz0)) -
          profPP sz0 0 z a b‖ ≤ ε) →
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ a : Zd 3 (sz0.L 0),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 a (sz0.seqXmat 0 ω)} ≤
          ENNReal.ofReal (4 * Nsz sz0 0 ^ 2 * etaQ sz0 0 (1 / 30) ^ 2 * (4 * (K + ε)) /
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))))) ∧
      (∀ A : Finset (Zd 3 (sz0.L 0)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 A (sz0.seqXmat 0 ω)} ≤
          ENNReal.ofReal (4 * Nsz sz0 0 ^ 2 * etaQ sz0 0 (1 / 30) ^ 2 * (4 * (K + ε)) /
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))))) := by

theorem inst_QUE_of_QDiff : QDiff → ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
    (∀ a : Zd 3 (sz0.L n),
      Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
    (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
      Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) :=

```

Narrative (facts from the files above):
- New file `RBM3D/Main/QUEFromQDiff.lean`, 664 lines, one commit f1fbd44 on t/T2248; imports exactly `RBM3D.Main.QUECore`, `RBM3D.Green.LDE` (Targets 5); no other file touched; no Test/Axioms.lean line.
- Copied byte-equal (verb.py, five True): Endpoints `:218-227` (private scalars, in `section QUEScalars`), probe `:1864-2022` (`etaQ`, `queDomain`, `calB_le_two_inv`, `que_three_terms`, `etaQ_le`, `MAQUE`), probe `:2386-2393`, `:2447-2451`, `:2476-2488` (four instances, inside `namespace Inst` with `open RBM.Gauss.SizesInst RBM.Univ.UNInst`). `etaQ` and the 16 pinned names equal the check file's pins by `rfl`/term (18 examples, exit 0).
- New proofs: `queRowDiff` (from `thetaDiff`, `norm_msc_lt_one`; `ThetaPM`/`ThetaPP` unfold by `rfl`); `queFixed` (`queX_core` at `δ_a` and `1_A/|A|`, `queBad_sub`/`que2Bad_sub` at `η = etaQ` with window hypothesis `fun x hx => hx`, `queMarkov` at `f = 4N²η²·queX`); `queChain` (a private real-number core `queChain_real` plus the eventual wrapper; exponent chain as in section (a) (i)); `QUE_of_QDiff` (`QDiff` at `(κ, 𝔠(𝔡-ε₀), τ/2, 1)`).
- Imports added beyond the two named: none. `QUE_of_QDiff` does not use `0 < c`, `c < ε₀`, `c < 𝔡/5` (remark, not a delta). `queChain` uses `ε₀ < 𝔡/2` only through `ε₀ ≤ 3𝔡/5`; `c` is any real.
- Instances: `inst_queFixed` discharges `0 < η_Q ≤ 1` at `sz0`, `n = 0` (private `queFromQDiff_inst_etaQ`, re-proved) and `queRowDiff` at `z = η_Q i`; the expectation half of `QDiff` (another gate's pin, owed) stays a hypothesis. `inst_queChain` is `∀ᶠ n` as pinned (section (a) remark (a): false at `n = 0`). `inst_QUE_of_QDiff` takes `QDiff` as hypothesis and returns the merged `inst_QUE` statement; at `(c, τ) = (1/60, 1/10)` its bound `queBound` exceeds 1 (section (a) remark (b)), same data as merged `inst_QUE`.
- Registry: the pre-check (reg.lean) exits 0; `MAQUE` is the type of `QUE_of_QDiff`, not a hypothesis; `QUE`, `QDiff` stay owed, no line added or deleted.

## (c) Verified Mathlib names (all used in the compiling file)
- `Real.rpow_le_rpow_of_nonpos` (Pow/Real.lean:565: `0 < x → x ≤ y → z ≤ 0 → y ^ z ≤ x ^ z`), `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_neg`, `Real.rpow_natCast`, `Real.rpow_two`, `Real.rpow_pos_of_pos`, `Real.rpow_nonneg`, `Real.rpow_le_one_of_one_le_of_nonpos`, `tendsto_rpow_atTop`.
- `MeasureTheory.integral_const_mul`, `MeasureTheory.Integrable.const_mul`, `ENNReal.ofReal_le_ofReal`, `Finset.sum_ite_mem`, `Finset.univ_inter`, `Finset.sum_const`, `nsmul_eq_mul`, `mul_inv_cancel₀`, `inv_anti₀`, `div_le_iff₀`, `div_le_div_of_nonneg_right`, `le_mul_of_one_le_right`, `Complex.norm_real`, `Complex.norm_natCast`, `norm_div`, `norm_mul`, `norm_pow`. Names verified absent: none searched.

## (d) Open issues and paper-delta candidates — Tue Oct  6 03:50:38 UTC 2026
- No `T2248a` candidate: the statements of section (a) agree with `1_2:406-420, 512-545`; D500, D503, D504 are the consumers' deltas (not re-proposed).
- Consumer check (§45 O2) not compiled here: MA-06 is unwritten; `QUE_of_QDiff : MAQUE` has the probe's pin type (`:2020`), against which the probe consumers `:2079-2101` compiled.
- No section (a′) needed: no correction to section (a) was found.
