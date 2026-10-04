Prover model: claude-sonnet-5-5

## (a) Math preflight — Sun Oct  4 07:59:38 UTC 2026

Sources read: RBM2D `Green/Eq45Small` (505 lines) and `Green/FlucThreshold` (718 lines) via `git show c9a24cf:`; merged `RBM3D/Green/MinorDiffCond.lean` (`flucGainUpTo'_goodEvent` :909, `condEps` :779, `badBase` :706), `Green/LocalLaw.lean` (`LocalLawDetSeq` :104, pins :166-192), `Green/FlucIterGain.lean` (`FlucGainUpTo'` :727, `integral_norm_flucAvg_pow_le_iter_budget` :823), `Defs/Sizes.lean` (`sz0` :258, `size`, `Admissible`), `Defs/StochDomAt.lean` (`HighProbAt` :82, `PerTimeDomAt` :105, `highProbAt_iInter` :279). Scripts (Python, no Lean): `/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2123/inst.py`, `inst2.py`.
Notation: `N = sz.size n = (W L)^d`, `δ = detFlucDelta Ψ θ`, `Ψ' = 2δ`, `C_M = minorDiffC M`, `η = etaT E t = (1-t) Im mE E`, `ν = ln N / ln W`.

### (i) Exponent table

| # | Quantity | Value | Constraint | Slack |
|---|---|---|---|---|
| 1 | Floor on `Ψ` (paper `3_5:27`; pins `LocalLaw.lean:166-192`) | `W^{-d/2} ≤ Ψ n` (`d=3`: `W^{-3/2}`; RBM2D `W^{-1}` is the `d=2` case) | `flucGain_of_localLaw` takes this form as `hΨlo`, as the merged `FixedTimeFAThm` does | `W^{-3/2} ≤ W^{-1}`: the RBM2D premise `W⁻¹ ≤ Ψ` is strictly stronger than the pin gives; must not be kept |
| 2 | Ceiling `Ψ ≤ N^{-a}`, `a > 0` | needs `W^{-d/2} ≤ N^{-a}`, i.e. `a ≤ (d/2)/ν`; `L = W`: `ν = 2d`, `a ≤ 1/4`; `sz0`: `N = 8 W^{18/5}`, `a ≤ 5/12` (asymptotically) | `Admissible 𝔠`: `W ≥ N^𝔠` gives `ν ≤ 1/𝔠`, so some `a > 0` exists | instance `a = 1/3`: slack `5/12 - 1/3 = 1/12` |
| 3 | `θ = detFlucTheta a τ = min(a/8, τ/32, 1/8)` | `a = 1/3, τ = 1`: `θ = 1/32` | `0 < θ`, `θ ≤ a/4 = 1/12`, `θ ≤ 1/4` (hypotheses of every target) | `1/12 - 1/32 = 5/96` |
| 4 | Regularising floor `(N+4)^{-2}` in `detFlucDelta`/`detFlucControl` (`detFlucControl_floor`, `detFlucDelta_floor_le`) | dimension-free exponent `-2` | this is NOT a floor on `Ψ`; no `W^{-1}` or `W^{-d/2}` enters; `PolyLo` of `δ` at `D = 4`, `N ≥ 4` (`x^{-4} ≤ (x+4)^{-2}`) | none needed |
| 5 | Margin `N^{θ/2} · max(Ψ, (N+4)^{-2}) ≤ δ` (`detFlucDelta_margin`) | sufficient: `4 ≤ N^{min(a,1) - θ/2}`, i.e. `N ≥ 4^{1/(1/3 - 1/64)} ≈ 79` | needs `Ψ ≤ N^{-a}` and `θ ≤ a/4` | `sz0`, `n=0`: `ln(LHS/δ) = -0.227`; `n=3`: `-0.617`; `n=10^4`: `-2.818` (output below) |
| 6 | `PolyLo` / `PolyHi` rates (`Eq45Small:63-69`) | `δ`: `PolyLo`, `(C,D) = (1,4)`; `η⁻¹+1`: `PolyHi`, `(2, K_η)` from `N^{-K_η} ≤ η` | rates are in powers of `N = (WL)^d` (the size sequence), dimension enters only via `N` | none; `d=2` file has the same rates |
| 7 | `hsmall` from high probability (`hsmall_of_highProb`): `P(badTower(M+1)) · condEnv^K ≤ B₀^K (2Ψ')^{KM}` | `D_W := ln[condEnv^K ((ε+N)/ε)^{M+1} / (B₀^K (2Ψ')^{KM})] / ln W`, `ε = condEps = Ψ'(2Ψ')^M/((M+1) condEnv)`, `B₀ = 2 C_M Ψ' + Ψ'` (`condCost_condEps`) | suffices `P(Ω^c) ≤ W^{-D_W}`; `HighProbAt` is `∀ D > 0`, so one `D` beats it (`measureReal_compl_le_of_polyLo`) | limit `D_{W,∞} = (M+1)(ν + c'(M+1)) + c' K (M+1)` for `δ = W^{-c'}`; `L=W, c'=1, d=3` (ticket reference): `8, 9, 18, 20` for `(M,K) = (0,1),(0,2),(1,1),(1,2)`; `D_W` increases to the limit from below (output (A)) |
| 8 | Same on the merged `sz0`, `Ψ = W^{-3/2}` (`c_Ψ = d/2`), `a=1/3`, `θ=1/32`, `η=1/2` | `δ ≈ N^θ Ψ = W^{-c'}`, `ν = 18/5`, `c' = 3/2 - (18/5)/32 = 1.3875`; `D_{W,∞} = 6.375, 7.7625, 15.525, 18.3` (`D_{N,∞} = 1.77, 2.16, 4.31, 5.08`) | proof level (only `N^{-K_η} ≤ η` known): add `K_η (K+M+1)` to `D_N` | output (B); closes for each fixed `(M,K)`, all `n` large |
| 9 | Union bound in `highProbAt_detFlucDelta_of_localLaw` | `#(Idx × Idx) = N²` (`flucAvg_card_Idx_eq_size`), `C = 2`, spends `D → D+2` | per-pair `PerTimeDomAt` at `τ = θ/2 = 1/64` for all `D` | none (`∀ D`) |
| 10 | `hB1 = (2 C_M + 1) · 2δ ≤ 1` at `ε = condEps` (`condCost = Ψ'`) | `C_0 = 8`, `C_1 = 2^17`, `C_2 = 2^91`; thresholds `δ ≤ 1/34, 1/524290, 1/(9.9·10^27)` (output) | `∀ᶠ n` only; `δ ≤ N^{-min(a/2,1)}` (`detFlucDelta_le_rpow`) forces it | `sz0`: holds from `n = 0` (`M=0`), `n = 3` (`M=1`), `n = 5476` (`M=2`) (output) |
| 11 | Gain pair, endpoint | `B = 2(2 C_M Ψ' + Ψ')`, `ρ = 2 Ψ' = 4δ` | `ρ ≤ 1` (`hρ1` of the consumer) iff `δ ≤ 1/4` (`detFlucDelta_le_quarter`); `8Mδ ≤ 1` | `n=3`: `ρ = 2.3·10^{-6}` |
| 12 | Weight condition `c ≤ ρ²` of `integral_norm_flucAvg_pow_le_iter_budget` (D192: bounded weight, `c = W^{-d}`) | `(W^d)⁻¹ ≤ (4δ)²`; proof: `(W^{-d/2})² = (W^d)⁻¹ ≤ Ψ² ≤ (4δ)²` using `Ψ/4 ≤ δ`, `Ψ ≤ 1` | RBM2D form `(W⁻¹)² ≤ ρ²` is FALSE at `d=3` under the pin floor (instance `n=3`: `9.3·10^{-10} ≤ 5.4·10^{-12}` fails) | `4δ/Ψ = 6.3, 13.75, 1121` at `n = 0, 3, 10^4`; `W^{-d}/ρ² = 5.3·10^{-3}` at `n=3` |
| 13 | `d=2` tokens in the kept lines | `Eq45Small`: docstring only (`(W L)²`); `FlucThreshold`: `W⁻¹`, `W⁻²` in `flucThreshold_W_inv_sq_le_detFlucDelta_sq`, the endpoint conjunct, docstrings; `size²` pair count (dimension-free); `Z2` only in the unported `Checks` | all other exponents (`-2`, `1/4`, `θ`, `8Mδ`) are dimension-free | only row 12 (and the floor, row 1) change |
| 14 | §29 items | (1) `0 ≤ t` never used; `t < 1` gives `η > 0` (`etaT_pos`); `|E n| < 2`. (2) no `ilambda`, no window. (3) `L^d ≤ W^K` not used in any statement; `Admissible` only supplies `a` (row 2). (4) conclusions are `∀ᶠ n`; `∀ n` only on `|E n| < 2`, `t n < 1` (as the merged pins); `hsz : SizeTendsto` is needed for `4 ≤ N`, `N^{β} ≥ 4` eventually; `1 ≤ N` holds always (`Sizes.one_le_size`) | | none |

### (ii) One concrete nondegenerate instance

`d = 3`, `sz0` (`Defs/Sizes.lean:258`: `L = 4(n+1)`, `W = (2(n+1))^5`; `n=0`: `L=4, W=32, N=2097152`), `E ≡ 0` (`mE 0 = i`, `η = 1 - t`), `t ≡ 1/2` (`η = 1/2`), `K_η = 1/10`, `Ψ n = W^{-3/2}` (the floor, equality), `a = 1/3`, `θ = 1/32`, `(M,K) = (1,2)` (also `(0,1),(0,2),(1,1)`), `LocalLawDetSeq sz0 E t Ψ` the external premise. Commands: `python3 inst.py > out1.txt; python3 inst2.py > out2.txt`; the last line of the second block is an inline `python3 -` with `W = 32768`, `δ = 5.7948e-07` (the `n = 3` values).
```
minorDiffC M=0,1,2: 8? 8 2^17? True 2^91? True
hB1 at eps=condEps: (2C_M+1)*2*delta<=1 <=> delta<=1/34
hB1 at eps=condEps: (2C_M+1)*2*delta<=1 <=> delta<=1/524290
hB1 at eps=condEps: (2C_M+1)*2*delta<=1 <=> delta<=1/9903520314283042199192993794
== (A) d=3, L=W, N=W^6, delta=W^-c, c=1, eta=1/2
M=0 K=1 D_W: W=1e+06:7.954  W=1e+24:7.988  limit (M+1)(2d+c(M+1))+cK(M+1) = 8
M=0 K=2 D_W: W=1e+06:8.828  W=1e+24:8.957  limit (M+1)(2d+c(M+1))+cK(M+1) = 9
M=1 K=1 D_W: W=1e+06:17.436  W=1e+24:17.859  limit (M+1)(2d+c(M+1))+cK(M+1) = 18
M=1 K=2 D_W: W=1e+06:18.612  W=1e+24:19.653  limit (M+1)(2d+c(M+1))+cK(M+1) = 20
== (B) theta= 1/32  <=a/4: True  <=1/4: True
n=0: (4, 32, 2097152) size=2097152: True
n=0 W=32 N~1e6.3: floor:True ceil:True margin:True (ln ratio -0.227) suff:True delta=8.706e-03 4delta/Psi=6.30 4delta<=1:True W^-d<=(4delta)^2:True
n=3 W=32768 N~1e17.2: floor:True ceil:True margin:True (ln ratio -0.617) suff:True delta=5.795e-07 4delta/Psi=13.75 4delta<=1:True W^-d<=(4delta)^2:True
n=10000 W=3201600320032001600032 N~1e78.3: floor:True ceil:True margin:True (ln ratio -2.818) suff:True delta=1.547e-30 4delta/Psi=1121.08 4delta<=1:True W^-d<=(4delta)^2:True
M=0 first n with hB1 and 8M*delta<=1 on sz0: n=0 (W=32) monotone check at n+1000: True
M=1 first n with hB1 and 8M*delta<=1 on sz0: n=3 (W=32768) monotone check at n+1000: True
M=2 first n with hB1 and 8M*delta<=1 on sz0: n=5476 (W=157711616429494117024) monotone check at n+1000: True
== (B) hsmall threshold on sz0, E=0,t=1/2 (eta=1/2), delta=detFlucDelta
M=0 K=1  n=3:D_W=6.50,D_N=1.71 n=10000:D_W=6.40,D_N=1.76 n=1e+16:D_W=6.38,D_N=1.77  D_W,inf=6.3750 D_N,inf=1.7708
M=0 K=2  n=3:D_W=7.72,D_N=2.03 n=10000:D_W=7.75,D_N=2.13 n=1e+16:D_W=7.76,D_N=2.15  D_W,inf=7.7625 D_N,inf=2.1562
M=1 K=1  n=3:D_W=15.14,D_N=3.98 n=10000:D_W=15.44,D_N=4.24 n=1e+16:D_W=15.50,D_N=4.29  D_W,inf=15.5250 D_N,inf=4.3125
M=1 K=2  n=3:D_W=16.81,D_N=4.42 n=10000:D_W=17.99,D_N=4.94 n=1e+16:D_W=18.22,D_N=5.04  D_W,inf=18.3000 D_N,inf=5.0833
```
```
eta_t = (1-t)*Im mE(0) = 1/2 at E=0,t=1/2 (mE 0 = i); N^-Keta<=eta at n=0..: True ; n=0: 0.2333
instance n=3: L=16 W=32768 N=144115188075855872  Psi_n=W^-3/2=1.6859e-07  delta=5.7948e-07  2delta=1.1590e-06
  condEnv(M=1)=24  condEps=5.597e-14  condCost=Psi=1.1590e-06  B0=2C_1(2delta)+2delta=0.303813<=1:True
  endpoint pair: B=2*B0=0.607626  rho=2(2delta)=2.3179e-06<=1:True  8*M*delta=4.636e-06<=1:True  delta<=1/4:True
  weight: W^-d=2.8422e-14 <= rho^2=5.3727e-12 : True
  needed P(Omega^c)<= S/G: ln(G/S)=174.74  => D_W=16.81, D_N=4.42  (ln W=10.40, ln N=39.51)
  proof-level extra when only N^-Keta<=eta is known (Keta=1): + Keta*(K+M+1) in N-powers = 4
  local-law side: PerTimeDomAt tau=theta/2=0.01562 needs per-pair D+2 (N^2 pairs): need all D
d=2 form (W^-1)^2=9.313e-10 <= rho^2=5.373e-12 : False
```
At `n = 3` the slice is nondegenerate (`N = 1.4·10^17`, `δ = 5.8·10^{-7}`, `ε = 5.6·10^{-14}`, `B = 0.61`, `ρ = 2.3·10^{-6}`); no `N = 0`, empty index or collapsed window; `t = 1/2 > 0`, so `G_t ≠ m` (not the `t = 0` collapse). The floor holds with equality at `Ψ = W^{-3/2}`, the ceiling `Ψ ≤ N^{-1/3}` and the margin hold from `n = 0`, `hB1` from `n = 3` (`M = 1`).

External hypothesis `LocalLawDetSeq sz0 E t Ψ` (`≺` at `Ψ = W^{-d/2}`, `3_5:30`, `asGMcSeq_iff` at `c = d/2`), concrete limit computation (TEAM §8 lesson 14): the proof needs `P(|G_ij - m 1_{i=j}| > N^{θ/2} Ψ) ≤ N^{-D}` for every `D` at `θ/2 = 1/64`; the deterministic chain around it closes at the sampled slices `n = 3, 10^4, 10^16` (margin, `hB1`, weight, `D_W < D_{W,∞}`; outputs (B)) and `hB1` is monotone from its first `n` (output), and the scale is the true size of the entries: `docs/reports/T2117-prove.md` (a) (iii) measured `rms|G_kk - m| ∝ W^{-1.494}` at `d = 3`, predicted `W^{-d/2} = W^{-1.5}`, constant `≈ 0.52 < 1`. So `N^{1/64} Ψ` exceeds the measured typical entry by the factor `N^{1/64}/0.52 = 2.41` at `n = 0` (`N^{1/64} = 1.255`); the premise is the owed paper input (`GavLGEX`, `Acta:4564`), not derived here.

### Verdict per target
- `hsmall_of_highProb` (Eq45Small:248): **PASS**. Dimension enters only through `N = (WL)^d`; `D_W` is finite and bounded (rows 7, 8); `HighProbAt` is `∀ D`; `hs`/`hsz` supplies `N → ∞`.
- `flucGain_of_localLaw` (FlucThreshold:436): **PASS** with one forced change: floor `W^{-d/2} ≤ Ψ` (not `W⁻¹`) and conclusion `(W^d)⁻¹ ≤ (2(2δ))²` (not `(W⁻¹)²`); the RBM2D conjunct is false at `d = 3` (row 12, output). The change is a paper-delta candidate `T2123a` (`d=2` token replaced by the pin's `d/2` floor and `D192` weight `c = W^{-d}`). `PolyLo`, `PolyHi`, closure lemmas, `measureReal_compl_le_of_polyLo`, `detFlucDelta/Control/Theta` and their bounds (including `detFlucControl_floor`, `detFlucDelta_floor_le`, rows 4-5): **PASS**, statements unchanged (no `W⁻¹` floor needed).
- `hsmall` debt of S1-26 and `hB1`: `hsmall` is discharged from `HighProbAt` (premise `LocalLawDetSeq` via `highProbAt_detFlucDelta_of_localLaw`); `hB1` is discharged eventually from `detFlucDelta_moment_small` (row 10, `δ ≤ 2^{-19}` at `M = 1` from `n = 3` on `sz0`).

## (b) Script output (stage 1b started Sun Oct  4 08:00:17 UTC 2026; `date -u` before the final rerun of the scripts below: Sun Oct  4 08:20:01 UTC 2026)

### b.1 Build, scope, commit
```
$ cd RBM3D-wt/T2123 && lake build RBM3D.Green.FlucThreshold | tail -2        (exit 0)
✔ [3343/3343] Built RBM3D.Green.FlucThreshold (3.9s)
Build completed successfully (3343 jobs).
$ lake build | tail -1                                                       (exit 0)
Build completed successfully (3869 jobs).
$ git diff --name-only main...t/T2123 ; git log --oneline -1
RBM3D/Green/FlucThreshold.lean
58b18a1 T2123: port Green/Eq45Small and Green/FlucThreshold (hsmall_of_highProb, flucGain_of_localLaw)
$ grep -c "sorry\|admit\|native_decide" RBM3D/Green/FlucThreshold.lean        -> 0     (file: 1295 lines)
```
The full `lake build` does not import the new module (root import is added by the hub at merge); the registry pre-check below does.

### b.2 Registry pre-check (DECISIONS §20; scratch file outside the repository)
```
$ cat scratchpad/T2123/precheck.lean
import RBM3D
import RBM3D.Green.FlucThreshold

#assert_rbm_axioms
$ lake env lean scratchpad/T2123/precheck.lean | head -1                      (exit 0)
axiom audit: 3806 theorems, 1314 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
$ (same with `import RBM3D` only) | head -1
axiom audit: 3774 theorems, 1309 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
```
Difference `+32 theorems, +5 definitions` = the 32 public theorems and 5 public defs of the file; no
"premise(s) that no theorem of this development proves" error: `PolyLo`, `PolyHi` are concluded by
`polyLo_const`, `polyHi_const`, `detFlucDelta_polyLo`; `LocalLawDetSeq`, `FlucGainUpTo'` were already registered or
concluded.  `RBM3D/Test/Axioms.lean` is not modified.

### b.3 Axioms (`#print axioms` of every `def`/`theorem` of the file, private ones included, in a copy of the file)
```
$ lake env lean scratchpad/T2123/FlucThresholdAx.lean     (exit 0; python summary of the output)
75 declarations printed; 75 depend on exactly {propext, Classical.choice, Quot.sound}; no sorryAx
sorryAx occurrences: 0   "does not depend on any axioms": 0
```
(75 = 37 public + 38 private; the 37 public: `PolyLo PolyHi polyLo_const polyHi_const PolyLo.{mono,mul,pow,inv,div}
PolyHi.{mono,mul,add,pow,inv} measureReal_compl_le_of_polyLo hsmall_of_highProb detFlucDelta detFlucControl
detFlucTheta detFlucTheta_specs detFlucControl_{pos,ge_psi,floor,le_rpow} detFlucDelta_{pos,le_quarter,floor_le,
polyLo,le_rpow,margin,eventually_mul_le_one,moment_small,quarter_psi_le} flucThreshold_etaInv_le_rpow_of_lower
flucThreshold_etaPolyHi_of_lower highProbAt_detFlucDelta_of_localLaw flucGain_of_localLaw`.)

### b.4 Target statements, extracted by script (`python3 extract.py <name>`; `d` is the file's `variable {d : ℕ}`)
```
-- FlucThreshold.lean:270
theorem hsmall_of_highProb :
  ∀ (sz : Sizes d) {E t δ : ℕ → ℝ}, sz.SizeTendsto → (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    (∀ n, 0 < δ n) → PolyLo sz.size δ →
    PolyHi sz.size (fun n => (etaT (E n) (t n))⁻¹ + 1) →
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤ δ n}) →
    ∀ M K : ℕ, ∀ᶠ n : ℕ in atTop,
      condEnv (E n) (t n) M ^ K
          * (Sizes.seqP sz).real (badTower sz n (condEps (E n) (t n) M (2 * δ n))
              (badBase sz E t δ n) (M + 1))
        ≤ (2 * minorDiffC M * (2 * δ n)
            + condCost (E n) (t n) M (2 * δ n) (condEps (E n) (t n) M (2 * δ n))) ^ K
          * (2 * (2 * δ n)) ^ (K * M)
-- FlucThreshold.lean:856
theorem flucGain_of_localLaw :
  ∀ (sz : Sizes d) {E t Ψ : ℕ → ℝ} {a Kη θ : ℝ}, sz.SizeTendsto →
    (∀ n, |E n| < 2) → (∀ n, t n < 1) →
    0 < a → 0 ≤ Kη → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ (-Kη) ≤ etaT (E n) (t n)) →
    (∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ → ∀ M K : ℕ,
    (∀ᶠ n : ℕ in atTop,
      FlucGainUpTo' sz n (t n) (zt (E n) (t n)) (mE (E n))
        (2 * (2 * minorDiffC M * (2 * detFlucDelta sz Ψ θ n) + 2 * detFlucDelta sz Ψ θ n))
        (2 * (2 * detFlucDelta sz Ψ θ n)) M K) ∧
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * (2 * detFlucDelta sz Ψ θ n)) ^ 2)
-- FlucThreshold.lean:798
theorem highProbAt_detFlucDelta_of_localLaw :
  ∀ (sz : Sizes d) {E t Ψ : ℕ → ℝ} {a θ : ℝ}, sz.SizeTendsto →
    0 < a → 0 < θ → θ ≤ a / 4 → θ ≤ 1 / 4 →
    (∀ᶠ n : ℕ in atTop, Ψ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-a)) →
    LocalLawDetSeq sz E t Ψ →
    HighProbAt (Sizes.seqP sz) sz.size (fun n => {ω : Sizes.SeqΩ sz | ∀ i j : Idx d (sz.L n) (sz.W n),
      llErrMat d (sz.L n) (sz.W n) (E n) (t n) (Sizes.seqHflow sz n (t n) ω) i j ≤
        detFlucDelta sz Ψ θ n})
-- FlucThreshold.lean:221
theorem measureReal_compl_le_of_polyLo :
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ),
    Tendsto (fun n => ((size n : ℕ) : ℝ)) atTop atTop →
    ∀ {Ξ : ℕ → Set Ω}, HighProbAt P size Ξ → ∀ {f : ℕ → ℝ}, PolyLo size f →
      ∀ᶠ n : ℕ in atTop, P.real (Ξ n)ᶜ ≤ f n
-- defs (FlucThreshold.lean:82, 87, 432, 437, 442)
def PolyLo (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop := ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, C * ((size n : ℕ) : ℝ) ^ (-D) ≤ f n
def PolyHi (size : ℕ → ℕ) (f : ℕ → ℝ) : Prop := ∃ C > (0 : ℝ), ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, f n ≤ C * ((size n : ℕ) : ℝ) ^ D
def detFlucDelta (sz : Sizes d) (Ψ : ℕ → ℝ) (θ : ℝ) (n : ℕ) : ℝ :=
  min (1 / 4 : ℝ) ((((sz.size n : ℕ) : ℝ) + 4) ^ θ * max (Ψ n) ((((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ))))
def detFlucControl (sz : Sizes d) (Ψ : ℕ → ℝ) (n : ℕ) : ℝ := max (Ψ n) ((((sz.size n : ℕ) : ℝ) + 4) ^ (-(2 : ℝ)))
def detFlucTheta (a τ : ℝ) : ℝ := min (a / 8) (min (τ / 32) (1 / 8))
```

### b.5 Statement diff against RBM2D `c9a24cf` after the renaming R1-R3 (`python3 stmtdiff.py`)
The script cuts every public declaration of the kept region of `Green/Eq45Small.lean:59-404`, `Green/FlucThreshold.lean:60-465`
at the first `:=`, applies the renaming (`d`→`sz`, `(d : Sizes)`→`(sz : Sizes d)`, `SizeTendsto d`→`sz.SizeTendsto`,
`Idx (…)`→`Idx d (…)`, `llErrMat (…)`→`llErrMat d (…)`, `RBM.Path.etaT`→`etaT`, `spectralZ/M`→`zt/mE`) and compares tokens.
```
DIFF flucGain_of_localLaw
    replace RBM2D->renamed: ℝ))⁻¹  | RBM3D: ℕ) : ℝ) ^ (-(d : ℝ) / 2)
    replace RBM2D->renamed: ((sz.W n : ℝ))⁻¹ ^ 2  | RBM3D: (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
36 of 37 public statements identical after renaming; differing: ['flucGain_of_localLaw']
RBM2D public decls (kept region) without an RBM3D counterpart: []
```
Residual differences (all): the two lines above (floor `W⁻¹ ≤ Ψ` → `W^{-d/2} ≤ Ψ`; conjunct `(W⁻¹)² ≤ ρ²` → `W^{-d} ≤ ρ²`);
private `flucThreshold_W_inv_sq_le_detFlucDelta_sq` → `flucThreshold_W_pow_inv_le_detFlucDelta_sq` (same change);
`AvgPins_one_le_size` → private `flucThreshold_one_le_size`; the consumer check uses `BoundedWeight`; RBM2D's private `Checks` replaced.

### b.6 Compiled nonempty instances (`private theorem`s at the end of the file; data `sz0 : Sizes 3`, `E ≡ 0`, `Ψ n = W n^{-3/2}`, `a = 1/4`, `θ = detFlucTheta (1/4) 1`)
`sz0`: `L n = 4(n+1)`, `W n = (2(n+1))^5`, `n = 0`: `L = 4, W = 32, N = 2097152` (`sz0_values`); `n = 3`: `W = 2^15`, `N = 2^57`.
Instance A has `t ≡ 1/2` (`η = 1/2`, `etaT 0 (1/2) = 1/2` proved), keeps `hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1/2) flucThresholdPsi`
(other gates' owed pin, limit check in (a)); every other hypothesis is discharged (floor with equality, ceiling `N ≤ W^6`, `η` input `N^{-1} ≤ 1/2`
eventually, `θ ≤ a/4`, `|E| < 2`, `t < 1`).  Instance B has `t ≡ 0`, no hypothesis left (`localLawDetSeq_time_zero`).
```
FlucThreshold.lean:1137  flucThreshold_inst_flucGain_half (hll : LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1 / 2) flucThresholdPsi) :
    (∀ᶠ n in atTop, FlucGainUpTo' sz0 n (1 / 2) (zt 0 (1 / 2)) (mE 0)
        (2 * (2 * minorDiffC 1 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)
          + 2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n))
        (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) 1 2) ∧
    (∀ᶠ n in atTop, (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) n)) ^ 2)
  := flucGain_of_localLaw sz0 (E := fun _ => 0) (t := fun _ => 1 / 2) (Ψ := flucThresholdPsi) (a := 1 / 4) (Kη := 1)
      (θ := detFlucTheta (1 / 4) 1) sz0_tendsto flucThreshold_inst_hE (fun _ => by norm_num) (by norm_num) zero_le_one
      flucThreshold_inst_theta.1 flucThreshold_inst_theta.2.1 flucThreshold_inst_theta.2.2 flucThreshold_inst_eta_half
      flucThreshold_inst_floor flucThreshold_inst_ceiling hll 1 2
```
Other instances (statements in the file; `M = 1, K = 2` unless stated):

| target | instance (line) | hypothesis kept |
|---|---|---|
| `flucGain_of_localLaw`, `t ≡ 0` | `flucThreshold_inst_flucGain_zero` (1154) | none |
| `hsmall_of_highProb`, `t ≡ 1/2` | `flucThreshold_inst_hsmall_half` (1094) | `hll` |
| `hsmall_of_highProb`, `t ≡ 0` | `flucThreshold_inst_hsmall_zero` (1115) | none |
| `highProbAt_detFlucDelta_of_localLaw` | `flucThreshold_inst_highProb_half` / `_zero` | `hll` / none |
| `measureReal_compl_le_of_polyLo` | `flucThreshold_inst_measureReal` (`P(Ωᶜ) ≤ δ n` eventually) | `hll` |
| `detFlucControl_le_rpow`, `detFlucDelta_le_rpow`, `_margin`, `_eventually_mul_le_one`, `_moment_small` (`M = 1`) | `flucThreshold_inst_bounds` | none |
| `detFlucDelta_polyLo`, `flucThreshold_etaPolyHi_of_lower`, `detFlucTheta_specs` | `_inst_polyLo`, `_inst_polyHi_half`, `_inst_theta` | none |
| `PolyLo.{mul,pow,div,inv}`, `PolyHi.{mul,add,pow,inv}`, `polyLo_const`, `polyHi_const` | `flucThreshold_inst_poly` | none |
| `detFlucDelta_moment_small` at `M = 1`, slice `n = 3` | `flucThreshold_inst_slice3` (1283): `8·1·δ ≤ 1 ∧ 2·minorDiffC 1·(2δ) + 2δ ≤ 1` | none |
| `detFlucControl_floor`, `detFlucDelta_floor_le` at the floor `W^{-d/2}` | `flucThreshold_control_eq_psi` (733, generic in `sz`, `d`): `W^{-d/2} ≤ Ψ n → detFlucControl sz Ψ n = Ψ n` (the floor `(N+4)^{-2}` is below `W^{-d/2}`, as `N ≥ W^d`) | generic |
| consumer fit | `flucThreshold_check_consumer` (896; generic, proved from the endpoint and `integral_norm_flucAvg_pow_le_iter_budget`) | generic |

Compiled negative (`flucThreshold_literal_false`, line 1263, same data, slice `n = 3`; paper-delta candidate `T2123a`):
```
private theorem flucThreshold_literal_false :
    ¬ ((((sz0.W 3 : ℕ) : ℝ))⁻¹ ^ 2 ≤ (2 * (2 * detFlucDelta sz0 flucThresholdPsi (detFlucTheta (1 / 4) 1) 3)) ^ 2)
```
(`δ ≤ (N+4)^{1/32} W^{-3/2} ≤ 4 W^{-3/2} ≤ 4 W⁻¹/181`, so `4δ < W⁻¹`.)

### b.7 `d = 2` token accounting (script over the RBM2D sources and the new file; counts of occurrences, docstrings included)
```
token                       RBM2D Eq45Small.lean   RBM2D FlucThreshold.lean   RBM3D FlucThreshold.lean
W⁻¹/W⁻² forms               0                      25                         21
d = 2 / two-dimensional     2                      5                          0
(W L)² (size)               1                      1                          0
Z2                          0                      1                          0
size² (pair count)          0                      3                          4
```
RBM2D code lines carrying `W⁻¹` in the kept region: `FT:333, 335, 338, 441, 448` (the floor premise and the weight conjunct, replaced);
`Z2` at `FT:658` (consumer check) → `Zd d (sz.L n)`; `(W L)²`, `d = 2` only in docstrings (rewritten).  The 21 RBM3D hits are docstrings
quoting the RBM2D forms and `W⁻¹/181` in `flucThreshold_neg_aux`; `size²` is the dimension-free pair count `#(Idx × Idx) = size²`.
`L⁻` and `1/5`: 0 occurrences in the three files; `scal` occurs only inside the word `scale`.

### b.8 Name clash (CLAUDE.md §5.2)
```
$ git -C ../RBM3D grep -nwF -e PolyLo -e PolyHi … <the 37 public names> main -- 'RBM3D/*.lean' | wc -l      (main = 45ca385)
0
$ same on 5c69cb4 (the base of t/T2123)
0
```

### b.9 Ports
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h
9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Green/Eq45Small.lean RBM2D/Green/FlucThreshold.lean
 RBM2D/Green/Eq45Small.lean     | 143 ++---------------
 RBM2D/Green/FlucThreshold.lean | 345 +++++------------------------------------
 2 files changed, 53 insertions(+), 435 deletions(-)
```
The port is from `c9a24cf` (ticket); RBM2D `HEAD` has since changed both files (not read).  RBM1D: not ported from.  Sources: RBM2D
`Green/Eq45Small.lean:59-404`, `Green/FlucThreshold.lean:60-465` at `c9a24cf` (`git show c9a24cf:RBM2D/Green/…`).

### b.10 Narrative
1. **Ported.** 37 public declarations (5 defs, 32 theorems) with their RBM2D names; 36 statements equal RBM2D's after R1-R3 (b.5); none dropped.
   The private `Checks` of both RBM2D files are replaced by the instances at `sz0` (b.6).  No statement takes `hd : 3 ≤ d`.
2. **The debt of S1-26.**  `hsmall_of_highProb` proves the `hsmall` premise of `flucGainUpTo'_goodEvent` at `ε = condEps` from `HighProbAt` of the
   per-time good event, for every `M, K`, eventually; `hB1` is `detFlucDelta_moment_small`.  `flucGain_of_localLaw` composes
   them, so `hsmall` is not a named hypothesis of the endpoint; the one external hypothesis is `LocalLawDetSeq` (the output of `localLawDetThm`).
3. **`D_W`.**  Lean needs no value: `HighProbAt` is `∀ D > 0` and `measureReal_compl_le_of_polyLo` takes `D' = max(D+1, 1)`.  The `d = 3` numbers are
   (a) rows 7, 8, 10 (script output there): `D_W → (M+1)(ν + c'(M+1)) + c'K(M+1)` with `ν = 2d` at `L = W`; on `sz0`, `D_{W,∞} = 6.375, 7.7625, 15.525, 18.3`
   for `(M,K) = (0,1),(0,2),(1,1),(1,2)` (sampled values at `n = 3, 10^4, 10^16` in the output (B) of (a)).  Closure with the merged `δ = detFlucDelta`: Instances A/B compile for `sz0`, and
   `hB1`, `8Mδ ≤ 1` at `M = 1` are compiled at the slice `n = 3` (`flucThreshold_inst_slice3`); that they hold for all `n ≥ 3` is the numerical monotonicity of (a) row 10.
4. **The floor.**  `detFlucControl_floor`, `detFlucDelta_floor_le` take the regularising floor `(size + 4)^{-2}` of the control, not a floor on `Ψ`; they need no
   `W⁻¹` and are stated exactly as in RBM2D; checked at `W^{-d/2}`: `flucThreshold_control_eq_psi` (compiled) shows that under the pin floor the control
   `max(Ψ, (N+4)^{-2})` is `Ψ` itself, the regularising floor lying below `W^{-d/2}`.  The only statements that took `W⁻¹ ≤ Ψ` were RBM2D's `flucGain_of_localLaw` and its private weight lemma;
   they now take `W^{-d/2} ≤ Ψ` (`3_5:27`, D213) and conclude `W^{-d} ≤ (4δ)²`.  The ticket's stop rule is for a statement that *needs* `W⁻¹`: the conjunct
   `(W⁻¹)² ≤ ρ²` is the `d = 2` exponent (rule R3: `W⁻²`-type → `W^{-d}`), derived from the pin's floor, and the literal form fails at `n = 3` (compiled), so
   I made the R3 replacement and propose `T2123a` instead of stopping; the consumer (`integral_norm_flucAvg_pow_le_iter_budget`, `c = W^{-d}`, D192) takes it.
5. **Exponents that change with `d`** (RBM2D → here): floor `W⁻¹` → `W^{-d/2}`; weight `W⁻²` → `W^{-d}`; `size = (W L)²` → `(W L)^d` (`sz.size n`);
   `Z2` → `Zd d`.  Unchanged, dimension-free: `(N+4)^{-2}`, the cap `1/4`, `θ = min(a/8, τ/32, 1/8)`, `8Mδ ≤ 1`, `PolyLo` `(C,D) = (1,4)` of `δ`, the pair count `N²`.
6. **Instance data.**  `a = 1/4` (not `1/3` of (a)) so that `Ψ ≤ N^{-a}` is `N ≤ W^6` (`sz0_size_le_W_pow`); `K_η = 1`.  These are parameter choices inside (a)'s
   constraints (a) rows 2, 3, not corrections of (a).
7. **Registry.**  No new unregistered premise (b.2); `Test/Axioms.lean` unchanged.  `LocalLawDetSeq` in A is the concrete-limit-checked external hypothesis of (a).

## (c) Verified Mathlib names (new proofs of this ticket; `#check` in a scratch file over the file's own `open`s, Mathlib `v4.34.0`; the ported proofs reuse RBM2D's names, all resolved by the build)
`Real.sqrt_eq_rpow`, `Real.le_sqrt_of_sq_le`, `Real.sqrt_sq`, `Real.rpow_add`, `Real.rpow_mul`, `Real.rpow_natCast`, `Real.rpow_neg`, `Real.rpow_neg_one`,
`Real.rpow_zero`, `Real.rpow_nonneg`, `Real.rpow_pos_of_pos`, `Real.rpow_le_rpow`, `Real.rpow_le_rpow_of_exponent_le`, `Real.rpow_le_rpow_of_nonpos`,
`inv_le_comm₀`, `inv_anti₀`, `pow_le_pow_left₀`, `le_of_sq_le_sq`, `max_eq_left`, `min_le_right`, `mul_le_mul_of_nonneg_left`, `Complex.ext`, `Nat.cast_nonneg`,
`Filter.Eventually.of_forall`.  Verified absent: a public general `Sizes.seqHflow_zero` in RBM3D (private copies at `LocalLaw.lean:315`, `MinorDiff.lean:966`,
`MinorGoodLe.lean:1196`, `EntryDom.lean:1378`, `Pins.lean:1371`; a public one only for `sz0`, `Induction/Step1Setup.lean:1339`); not needed (`localLawDetSeq_time_zero` is used).

## (d) Open issues and paper-delta candidates
1. **External hypothesis of Instance A**: `LocalLawDetSeq sz0 (fun _ => 0) (fun _ => 1/2) Ψ` (owed; `localLawDetThm` from `AsGMcSeq`, `LoopDetSeq`); limit check in (a).
2. **`flucThreshold_literal_false` is compiled at the slice `n = 3` only**; the eventual (`∀ᶠ`) failure of the RBM2D conjunct is not compiled.
3. **`hB1` at larger `M`**: (a) row 10 gives `δ ≤ 1/(9.9·10^27)` at `M = 2` (`n ≥ 5476` on `sz0`), numerical, not compiled.
4. **For S1-30 (`fixedTimeFAThm`)**: `hΨlo`, `hΨhi` of `flucGain_of_localLaw` come from the `∀ᶠ … ∧ …` of the FA pin by `Eventually.mono`; `hη` (`K_η = 1`)
   from `eta_lower_of_rangeCond` (stated for `(zt …).im`; `etaT_eq_zt_im` converts); `|E n| < 2` from `|E n| < 2 - κ`.
5. **Hub**: add `import RBM3D.Green.FlucThreshold` after the last `import` line of `RBM3D.lean` at merge.
6. **Paper-delta candidate `T2123a`** (continues `T2108a`): the floor and the weight in the fluctuation-gain threshold lemma are the paper's `W^{-d/2} ≤ Ψ` (`3_5:27`)
   and `c = W^{-d} ≤ ρ²` (bounded weight, D192), not RBM2D's `W⁻¹ ≤ Ψ`, `c = W⁻²`; the RBM2D conjunct is false at `d = 3` (b.6).  No other Lean/paper difference
   is introduced here (`PolyLo/PolyHi`, `hsmall`, `detFlucDelta` have no counterpart in the paper; they are Lean's passage from `Ω(t,c)` to the moment bound, as in S1-26).
