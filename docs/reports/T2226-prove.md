Prover model: claude-sonnet-5-5

## (a) Math preflight — Mon Oct  5 23:36:46 UTC 2026

Notation: `N = Nsz sz n = (WL)^d ≥ 27`; `τs = 1/2` (fixed by the ticket); `t* = ouTStar = N^{-1+τs} = N^{-1/2}`; `t = 1 - e^{-t*} ∈ [t*/2, t*]`; `κ' = min κ 1`; `ρ0 = ρ_sc(0)`, `ρE = ρ_sc(E0)`. Math only; no Lean written.
Targets (math): T1 conditioning `GUE_{E0}(O) = E_ω ∫ kPoint O 0 λ(diag vGUE(ω) + √t X) dgueP`; T2 for `ω_n ∈ GUEGoodAt` the DBM functional of `O` minus the GUE functional of `O(ρ0/ρE ·)` at energy 0 tends to 0 (then uniformly on the event, `step1Band_eventually_forall`); T3 `UNGUETranslation` (bad event `N^{-k-1}` via `step1Band_abs_integral_kPoint_le`); T4 `UNInfty1Row'` = `step1Band_row` (`E'=0`) + T3 at `E:=E'`, `O ↦ O(ρ_sc(E')·)`; T5 instances.

### (i) Exponent table
| quantity | value | constraint | slack |
|---|---|---|---|
| internal time | `τs = 1/2`, `t* = N^{-1/2} ∈ (0,1]`, `t ∈ [t*/2,t*]` | `UNL32` needs `g N^σ ≤ t ≤ N^{-σ}G²`; `un_L32_arith` needs `N ≥ 1`, `0<τs<1`, `N^{τs/2} ≥ 2` | `N^{1/4} ≥ 2` iff `ln N ≥ 2.77` |
| `σ = δ_L32 = min(τs/4,(1-τs)/3)` | `min(1/8,1/6) = 1/8`; `g = N^{-7/8}`, `G = N^{-1/8}`, `q = 1/2`, `E_n = 0` | `gue_l32_exponents` rows: `-1+δ ≤ -1+τs/4`, `-1+τs/4 ≤ -δ`, `-1+τs/4+δ ≤ -1+τs/2`, `-1+τs ≤ -3δ` | `0, 0.75, 0, 0.125` (script; two are equalities, allowed) |
| `UNL32` regularity datum | `c = κ'/960 > 0`, `C = CV = 2` | pinned in `GUEGoodAt`; token-equal to `UNL32` premises (`IsRegular32 (v n) (g n) (G n) c C CV`) | none needed |
| `UNL32` free-conv / density datum | `m n := mfc`, `ρ n := ρ'` (`Classical.choose` of `∃ mfc`, `∃ ρ'` in `GUEGoodAt`) | `E n = 0` gives `m n ⟨0,η⟩`, same as `mfc ⟨0,η⟩`; `t n = 1 - Real.exp (-(ouTStar sz τs n))`; `Nsz` is an `abbrev` of `((sz.size n:ℕ):ℝ)` (`Pins.lean:372`) | token-equal (read from `Step1RegularityGUE.lean:66-71`, `Pins.lean:281-298`) |
| GUE good event | `gueGoodHighProb` at `(κ,1/2,E0,D)`, composed at `τ = τs/16 = 1/32` (`Step1RegularityGUE.lean:925-926`) | `τ ≤ τs/4`, `τ-τs/8 = -1/32 < 0`, `τ-τs/2 = -7/32 < -3τs/8 = -6/32`, `τ < τs` | `3/32`, `1/32`, `1/32`, `15/32` |
| `UNGUELocal` limit computation at `Im z = N^{-1+τs/4}` | `N^{τ}/√(N Im z) = N^{1/32}/N^{1/16} = N^{-1/32} → 0` | the regularity error exponent `τ-τs/8` | same `1/32` |
| bad event | `D = k+1` | `gueP(Good_nᶜ) ≤ N^{-k-1}`; `|F_n|, |G_n| ≤ N^k sup|O|` (`step1Band_abs_integral_kPoint_le`) | contribution `2 sup|O|/N → 0`; nonempty event: `N^{-k-1} ≤ 27^{-1} < 1` (`D = 1`) |
| `ρ'_n` in Lipschitz window | `|ρ'-ρE| ≤ N^{-3τs/8} = N^{-3/16}` | `N^{-3/16} ≤ ρE/2` so `ρ' ∈ [ρE/2, 2ρE]` (`ρE > 0` from `|E0| ≤ 2-κ`, `κ>0`) | at `E0=1`: `ln N ≥ 10.57` |
| Lipschitz step (`Step1Cond_scaledPairing_lipschitz`, form `ρ^k A(ρ)`) | `A(ρ) = ∫ kPoint (O''(ρ·))`, `O'' = O(ρE^{-1}·)`, at `(ρE, ρ')`; extra term `(ρ'^k/ρE^k - 1) A(ρ')` | `|ρ'^k-ρE^k| ≤ k (2ρE)^{k-1} N^{-3/16}`; both error terms `N^{-3/16}×(GUE count)` | → 0 by `step1Band_gue_count` (below) |
| GUE count (`step1Band_gue_count`) | `a = τs/(8(k+1))`, `τ_G = a/2` | `3τs/8 - k a ≥ τs/4` | `k=1,2,5`: `0.15625, 0.14583, 0.13542` vs `0.125`: slack `0.031, 0.021, 0.010` (script `cnt.py`) |
| composition | `κ = (2-|E'|)/2 > 0`; `|E'| ≤ 2-κ = (2+|E'|)/2` iff `|E'| ≤ 2` | `|E'| < 2` (pin) | script rows; `ρ_sc(E')·(ρ0/ρE') = ρ0` (`ρE' ≠ 0`) |
| `τ_U` | only through `step1Band_row`: `τ₁ = 𝔠𝔡`, `0<τ_U≤𝔠𝔡`, `𝔠𝔡 < 1/2` (`un_admissible_cd_lt_half`) | no `τ_U ≤ ·` relation on the GUE side | `d=3`: `𝔠𝔡 = 1/60` at the instance |
| `d ≥ 3` | `d` only in `Idx d`, `Ω d`, `gueP d`; `N ≥ 27` from `3 ≤ d`, `L ≥ 3` (`Step1Band_size_ge`, `Step1Band.lean:51`) | all exponents in `τs, k` | — |
| constants order | `O,k` → `κ` → `c,C,CV` (`GUEGoodAt`) → `ρmin = ρE/2, ρmax = 2ρE` → `Q, C_Lip` → `Q'` (dominating) → `ε` → `n` | none depends on `W, L, lam, n` | — |

Consumer check (token by token, from the files): `UNInfty1 sz M ρ E E' k O τU` = `model(O(ρ_n·)) - GUE_{E'}(O(ρ_sc(E')·))` (`Pins.lean:552-559`). `step1Band_row` (`E'=0`): `model(O(ρ_n·)) - GUE_0(O(ρ0·)) → 0`. T3 at `E:=E'`, `O' = O(ρ_sc(E')·)`: `GUE_0(O'((ρ0/ρE')·)) - GUE_{E'}(O') → 0`, where `O'((ρ0/ρE')α) = O(ρE'·(ρ0/ρE')·α) = O(ρ0 α)` (`smul_smul`). Sum: `(model - GUE_0^{dil}) + (GUE_0^{dil} - GUE_{E'}^{dil}) = model - GUE_{E'}^{dil}`; so `Tendsto.add` + `add_zero` + `ring`. T2 vs `UNL32`: with `O'' = O(ρE^{-1}·)` (`isTestFun_comp_smul`), `UNL32` gives `∫kPoint O''(ρ'_n·) 0 λ(DBM) - ∫kPoint O''(ρ0·) 0 λ(GUE) → 0`, and `O''(ρ0 α) = O((ρ0/ρE)α)` is exactly the GUE term of T2; `A(ρE) = ∫kPoint O` is the DBM term of T2. Dilation direction check (numerics (vi)): `GUE_0(O(ρ0/ρE ·)) ≈ ρE ∫O ≈ GUE_E(O)`.
Two data, one model (supervisor 1651 1.3, O1): `UNInfty1Row'` is not refuted by that argument. Two data `(m,ρ),(m̃,ρ̃)` with `UNDens'` + `UNTrLocal` for the same `M` have `ρ_n, ρ̃_n` both within `N^{-3τ_U/8}` of the density of the free convolution of the same `vOU` (`UNStep1Good'` event, `PinsDens.lean:73-84`), so `ρ_n - ρ̃_n → 0` and the two conclusions `A_n(ρ_n,O) - G_n(O) → 0`, `A_n(ρ̃_n,O) - G_n(O) → 0` are consistent. The 1.3 counterexample is `unDensShift`, which is never `UNDens'` (`not_unDens'_unDensShift`, T2201). `UNInfty1Row'` itself consumes `step1Band_row` (already a theorem), so no new claim about two data enters T2226.
Premises kept by the instances (O3): `UNL32` (borrowed; GUE side: six arithmetic premises hold by the script at `n=0`, regularity/free-conv/density from `GUEGoodAt`); `UNGUELocal` (owed UN-09/UN-10: averaged GUE local law, limit computation row above); `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`, `UNDensBandRow` (band model rows of other gates; the T2214 report records grid min `Im msc = 0.0988` on the `E=0` window; the other rows are docstring claims, not verified here).

### (ii) One concrete nondegenerate instance
`d = 3`, `sz0` (`N_n = 2097152 (n+1)^18`, `L = 4(n+1)`, `W = (2(n+1))^5`; `sz0_values`), `(𝔠,𝔡) = (1/6,1/10)`, `k = 1`, `O = bump` (`1` on `|x| ≤ 1`, support `|x| < 2`, `∫ bump = 3` in the script), band model, `m = msc`, `E = 0`, `ρ = rhoSC 0`, `δ = 1/2`, `E' = 1`, `τ_U = 1/60 = 𝔠𝔡`. Translation instance `κ = 1, E = 1` (`|1| ≤ 2-1`, boundary equality allowed); row instance `κ = (2-1)/2 = 1/2`. All deterministic hypotheses hold (`3 ≤ 3`, `Admissible`, `UNDens'`, `|E'| < 2`, `|E| ≤ 2-κ`, `0<δ≤κ/2`, `IsTestFun bump`, `size → ∞` at `sz0`). Statements are `Tendsto`; thresholds below are not witnesses (DECISIONS §56). Nondegenerate: `ρ0/ρ1 = 1.1547 ≠ 1`, `E' = 1 ≠ E = 0`, `N_0 = 2^21`.
Commands (scratch dir `scratchpad/T2226/`: `python3 pre.py` (mpmath), `python3 cnt.py`, `python3 gue.py`). `pre.py` output verbatim:
```
tau_s=1/2: delta=min(1/8,1/6)=0.125  t*=N^(-1/2)  g=N^(-7/8) G=N^(-1/8) c=min(kappa,1)/960 C=CV=2
L32 exponent rows (lhs <= rhs): [(-0.875, -0.875, True, 0.0), (-0.875, -0.125, True, 0.75), (-0.75, -0.75, True, 0.0), (-0.5, -0.375, True, 0.125)]
gue_window at tau=tau_s/16=0.03125: tau<=ts/4 True, tau-ts/8=-0.03125<0, tau-ts/2=-0.21875 < -3ts/8=-0.1875, tau<ts
--- kappa=1 E0=1  rho_sc(E0)=0.27566444771089604  kappa'=1
  GUE good-event rows (T2220 (a) formulas) ln N >= {'eg': 0.79, 'eG': 11.09, 'eT': 10.96, 'eerr': 165.32, 'eedge': 16.13, 'eeps': 25.53}
  translation rows ln N >= {'L32': 2.77, 'Lipschitz': 10.57}
  binding ln N = 165.32 ; sz0: ln N_0 = 14.556 ; least n = 4341 (n+1 >= 4.34e+03)
--- kappa=0.5 E0=1  rho_sc(E0)=0.27566444771089604  kappa'=0.5
  GUE good-event rows (T2220 (a) formulas) ln N >= {'eg': 0.79, 'eG': 16.64, 'eT': 12.35, 'eerr': 176.41, 'eedge': 17.61, 'eeps': 29.23}
  translation rows ln N >= {'L32': 2.77, 'Lipschitz': 10.57}
  binding ln N = 176.41 ; sz0: ln N_0 = 14.556 ; least n = 8038 (n+1 >= 8.04e+03)
step1Band_row thresholds at tau_U=1/60 (quoted from T2208/T2214 reports): ln N >= 2157.2 (step1Good'), 679.3 (rho), 83.2 (L32)
=> row instance binding ln N = max(2157.2, translation binding)
n=0: N=2097152 N^(1/4)=38.055 >=2: True ; N^(-3/16)=0.0653 <= rho_sc(1)/2=0.1378 : True ; t*=N^(-1/2)=0.000691 t=1-exp(-t*)=0.000690 in [t*/2,t*]: True
six UNL32 premises at n=0: [True, True, True, True, True, True]
bad-event bound 2*sup|O|*N^k*N^(-k-1)=2supO/N at n=0: 9.537e-07 (sup bump=1)
bad-event bound 2*sup|O|*N^k*N^(-k-1)=2supO/N at n=1000: 9.367e-61 (sup bump=1)
E=1 rho_sc=0.27566  rho_sc(E)*(rho_sc(0)/rho_sc(E))=0.31831 == rho_sc(0)=0.31831 ; ratio rho0/rhoE=1.15470
E=1.9 rho_sc=0.09939  rho_sc(E)*(rho_sc(0)/rho_sc(E))=0.31831 == rho_sc(0)=0.31831 ; ratio rho0/rhoE=3.20256
E'=0 kappa=1.0000 2-kappa=1.0000 |E'|<=2-kappa: True kappa>0: True
E'=1 kappa=0.5000 2-kappa=1.5000 |E'|<=2-kappa: True kappa>0: True
E'=1.999 kappa=0.0005 2-kappa=1.9995 |E'|<=2-kappa: True kappa>0: True
```
`cnt.py` output verbatim:
```
k=1 a=ts/(8(k+1))=0.031250 tauG=a/2=0.015625  3ts/8-k*a=0.156250 >= ts/4=0.1250: True ; N^(-k-1)*N^k=1/N
k=2 a=ts/(8(k+1))=0.020833 tauG=a/2=0.010417  3ts/8-k*a=0.145833 >= ts/4=0.1250: True ; N^(-k-1)*N^k=1/N
k=5 a=ts/(8(k+1))=0.010417 tauG=a/2=0.005208  3ts/8-k*a=0.135417 >= ts/4=0.1250: True ; N^(-k-1)*N^k=1/N
```
`gue.py` (GUE `N = 1000`, 800 samples, `E|h_ij|² = 1/N`, `kPoint 1 O E λ = Σ_i O(N(λ_i - E))`; stderr over samples) output verbatim:
```
N=1000 samples=800  int bump = 3.00000 ; max|lam| over samples = 2.020
E=0 undilated kPoint1 bump E = 0.9807 +- 0.0189 ; rho_sc(E)*int bump = 0.9549
E=1 undilated kPoint1 bump E = 0.8300 +- 0.0186 ; rho_sc(E)*int bump = 0.8270
E=0 dilated  kPoint1 bump(rho_sc(E) .) E = 3.0167 +- 0.0194 ; int bump = 3.0000
E=1 dilated  kPoint1 bump(rho_sc(E) .) E = 2.9989 +- 0.0200 ; int bump = 3.0000
translation E=1: GUE_0(bump(rho0/rho1 .)) = 0.8596 +- 0.0188 ; GUE_1(bump) = 0.8300 +- 0.0186 ; diff = 0.0295 (se ~ 0.0264); undilated GUE_0(bump)-GUE_1(bump) = 0.1507 (factor 2/sqrt3 = 1.1547)
```
Reading. (1) At `τs = 1/2` every exponent row closes (`gue_l32_exponents` slacks `0, 0.75, 0, 0.125`; window slack `1/32`; count slack `0.031, 0.021, 0.010` at `k=1,2,5`). (2) Thresholds (formulas of rows eg..eeps are those of `T2220-prove.md` (a), recomputed at `τs = 1/2`, not re-derived from RBM2D): the translation needs `ln N ≥ 165.32` (`κ=1`) or `176.41` (`κ=1/2`), i.e. `n ≥ 4341` resp. `8038` at `sz0`; the `step1Band_row` thresholds quoted from `T2208/T2214` reports (`ln N ≥ 2157.2`) bind the row instance. Thresholds of `step1Band_gue_count` are not computed (eventual, `R/N ≤ η`, depends on supp `O`). (3) Numerics: dilated one-point functionals are `≈ ∫bump = 3` at both energies (within `1σ`); the undilated ones differ by the factor `2/√3` (`0.15` gap at `E=0` vs `1`), so the dilation of the translation is visible; the translation difference `0.030 ± 0.026` is consistent with `0` (a sampling check at finite `N`, not a proof).

### Verdict
- Target 1 (`guetranslation_integral_gue`): PASS (Gaussian conditioning at `t = t*` plus the energy shift; both merged).
- Target 2a/2b (`guetranslation_core`, `guetranslation_uniform`): PASS (`UNL32` premises token-equal to `GUEGoodAt` at `τs = 1/2`; Lipschitz window and `N^{-3/16}×count → 0` close; nonempty good event by `D=1`).
- Target 3a/3b (`guetranslationRow`, `guetranslation`): PASS (bad event `2 sup|O|/N → 0`).
- Target 4a/4b/4c (`un_infty1Row'_of_translation`, `un_infty1Row'`, `un_core'_of_univMainRow`): PASS (composition above; `κ = (2-|E'|)/2` is admissible; `UNInfty1Row'` is true as stated).
- Target 5 (four instances): PASS (hypothesis set nonempty at `sz0`; `UNL32`, `UNGUELocal`, band rows stay hypotheses).
- Design note T2226a (portmap UN-08 is transitive only) not contradicted by anything read.

## (b) Script output — written Mon Oct  5 23:58:37 UTC 2026

### b.1 Commit and scope
```
$ git log --oneline -1 t/T2226 ; git diff --stat main...t/T2226
e8d327b T2226: UN-14 GUE translation 0 -> E' and the row UNInfty1Row' (RBM3D/Universality/GUETranslation.lean)
 RBM3D/Test/Axioms.lean                 |   2 +-
 RBM3D/Universality/GUETranslation.lean | 958 +++++++++++++++++++++++++++++++++
 2 files changed, 959 insertions(+), 1 deletion(-)
$ git status --short   -> (empty)
```
### b.2 Module build (`lake build RBM3D.Universality.GUETranslation`; touch, then build)
```
Mon Oct  5 23:56:45 UTC 2026 ; exit=0
$ grep -c "GUETranslation.lean" modbuild.out   -> 0
$ tail -1 modbuild.out   -> Build completed successfully (3368 jobs).
$ wc -l RBM3D/Universality/GUETranslation.lean  -> 958 lines
$ grep -nE '\bsorry\b|\badmit\b|native_decide|^ *axiom ' RBM3D/Universality/GUETranslation.lean  -> (no output)
$ grep -nE "UNInfty1Row([^']|$)|UNStep1Good([^'C]|$)|UNStep1GoodC|UNCoreC|UNTrLocalInit" RBM3D/Universality/GUETranslation.lean  -> (no output: no refuted name in the file)
```
### b.3 `#print axioms` of the 21 public declarations (file `axioms.lean` = `import RBM3D.Universality.GUETranslation` + one `#print axioms` per name; `lake env lean`)
```
21 of 21 declarations: [propext, Classical.choice, Quot.sound]
```
### b.4 Target statements (extracted by `extract.py` from the file; bodies of the proofs omitted)
```
-- RBM3D/Universality/GUETranslation.lean:55
def UNGUETranslation : Prop :=
  UNL32 → UNGUELocal →
    ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
      ∀ k : ℕ, ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ →
        ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
          Tendsto (fun n =>
            (∫ ω, kPoint k (fun α => O ((rhoSC 0 / rhoSC E) • α)) 0
                (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
            (∫ ω, kPoint k O E (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues
                ∂(gueP d (sz.L n) (sz.W n))))
            atTop (𝓝 0)
-- RBM3D/Universality/GUETranslation.lean:69
def UNGUETranslationRow : Prop := UNGUEGoodHighProb → UNGUETranslation
-- RBM3D/Universality/GUETranslation.lean:337
theorem guetranslation_integral_gue :
    ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (τs E₀ : ℝ) (k : ℕ) (O : (Fin k → ℝ) → ℝ), IsTestFun O →
      ∫ ω, kPoint k O E₀ (Xmat_isHermitian d (sz.L n) (sz.W n) ω).eigenvalues ∂(gueP d (sz.L n) (sz.W n)) =
        ∫ ω, (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
            (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
          ∂(gueP d (sz.L n) (sz.W n)) :=
-- RBM3D/Universality/GUETranslation.lean:576
theorem guetranslation_core :
    UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
        ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O →
            ∀ ω : ∀ n, Ω d (sz.L n) (sz.W n), (∀ᶠ n in atTop, GUEGoodAt sz n κ τs E₀ (ω n)) →
              Tendsto (fun n =>
                (∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ (ω n))
                    (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
                ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                  (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n)))
                atTop (𝓝 0) :=
-- RBM3D/Universality/GUETranslation.lean:634
theorem guetranslation_uniform :
    UNGUEGoodHighProb → UNL32 → UNGUELocal →
      ∀ d : ℕ, 3 ≤ d → ∀ sz : Sizes d, Tendsto (fun n => sz.size n) atTop atTop →
        ∀ κ : ℝ, 0 < κ → ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ E₀ : ℝ, |E₀| ≤ 2 - κ →
          ∀ k : ℕ, ∀ O : (Fin k → ℝ) → ℝ, IsTestFun O → ∀ ε : ℝ, 0 < ε →
            ∀ᶠ n in atTop, ∀ ω : Ω d (sz.L n) (sz.W n), GUEGoodAt sz n κ τs E₀ ω →
              |(∫ y, kPoint k O 0 (dbmMat_isHermitian d (sz.L n) (sz.W n) (vGUE sz n τs E₀ ω)
                  (1 - Real.exp (-(ouTStar sz τs n))) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))) -
                ∫ y, kPoint k (fun α => O ((rhoSC 0 / rhoSC E₀) • α)) 0
                  (Xmat_isHermitian d (sz.L n) (sz.W n) y).eigenvalues ∂(gueP d (sz.L n) (sz.W n))| ≤ ε :=
-- RBM3D/Universality/GUETranslation.lean:665
theorem guetranslationRow : UNGUETranslationRow :=
-- RBM3D/Universality/GUETranslation.lean:754
theorem guetranslation : UNGUETranslation := ...
-- RBM3D/Universality/GUETranslation.lean:763
theorem un_infty1Row'_of_translation : UNGUETranslation → UNInfty1Row' :=
-- RBM3D/Universality/GUETranslation.lean:787
theorem un_infty1Row' : UNInfty1Row' := ...
-- RBM3D/Universality/GUETranslation.lean:791
theorem un_core'_of_univMainRow : UNUnivMainRow → UNCore' := ...
```
Compiled nonempty instances at `d = 3`, `sz0`, `k = 1`, `bump` (target 5; `UNL32`, `UNGUELocal`, band rows stay hypotheses):
```
-- RBM3D/Universality/GUETranslation.lean:809
theorem inst_dilation_ne_one : rhoSC 0 / rhoSC 1 ≠ 1 :=
-- RBM3D/Universality/GUETranslation.lean:814
theorem inst_guetranslation_sz0 :
    UNL32 → UNGUELocal →
      Tendsto (fun n =>
        (∫ ω, kPoint 1 (fun α => (bump : (Fin 1 → ℝ) → ℝ) ((rhoSC 0 / rhoSC 1) • α)) 0
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))) -
        (∫ ω, kPoint 1 (bump : (Fin 1 → ℝ) → ℝ) 1
            (Xmat_isHermitian 3 (sz0.L n) (sz0.W n) ω).eigenvalues ∂(gueP 3 (sz0.L n) (sz0.W n))))
        atTop (𝓝 0) :=
-- RBM3D/Universality/GUETranslation.lean:911
theorem inst_un_infty1Row'_band_zero :
    UNL32 → UNGUELocal → UNLocAvgBand → UNTrLocalBandRow → UNNormBandRow →
      ∃ τ₁ : ℝ, 0 < τ₁ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₁ →
        UNInfty1 sz0 (UNModel.band sz0) (fun _ => rhoSC 0) 0 1 1 (bump : (Fin 1 → ℝ) → ℝ) τU :=
```
The other eight instances (namespace `RBM.Univ.GUETranslationInst`): `inst_un_infty1Row'_band_one` (`E = E' = 1`, `κ = 1/2`), `inst_guetranslationRow_sz0` (3a), `inst_guetranslation_integral_gue_sz0` (1, `n = 0`), `inst_good_nonempty_sz0`, `inst_guetranslation_core_sz0` (2a: `∃ ω` in the good event and the limit), `inst_guetranslation_uniform_sz0` (2b, `ε = 1`, `UNGUEGoodHighProb` discharged by `gueGoodHighProb`), `inst_un_infty1Row'_of_translation_band_zero` (4a), `inst_un_core'_band_zero` (4c).
### b.5 Check-file diff (`diffcheck.py`: check sections 2.1-2.5 against the file; whitespace-normalised, `RBM.Univ.UNInst.bump` -> `bump`, `RBM.Gauss.SizesInst.sz0` -> `sz0`)
```
IDENTICAL 14: UNGUETranslation, UNGUETranslationRow, guetranslation_integral_gue, guetranslation_core, guetranslation_uniform, guetranslationRow, guetranslation, un_infty1Row'_of_translation, un_infty1Row', un_core'_of_univMainRow, inst_dilation_ne_one, inst_guetranslation_sz0, inst_un_infty1Row'_band_zero, inst_un_infty1Row'_band_one
DIFFERENT 0. ALL IDENTICAL (whitespace-normalised; bump/sz0 qualifiers normalised)
$ lake env lean checkscratch.lean   (= the check file + 12 `example : T2226_<name> := RBM.Univ.<name>` lines and 2 `rfl` lines for the two Props)  -> exit 0, 0 lines containing 'error'
```
### b.6 Name-clash grep of every new public name against `main` (`git grep -nF <name> main -- RBM3D RBM3D.lean`, main = e1fec21)
```
25 names/strings checked (21 public names, `GUETranslationInst`, `Universality.GUETranslation`, `GUETranslation_`, `T2226`); names with hits on main: none (0 hits each)
```
### b.7 Port citations and RBM2D diff-stat (read-only)
```
$ git -C ../RBM2D --no-optional-locks log -1 --format=%h  -> 9e0f275
$ git -C ../RBM2D --no-optional-locks diff --stat c9a24cf HEAD -- RBM2D/Universality/GUETranslation.lean
 RBM2D/Universality/GUETranslation.lean | 239 +++++++--------------------------
 1 file changed, 46 insertions(+), 193 deletions(-)
(the port is of `c9a24cf`: `git show c9a24cf:RBM2D/Universality/GUETranslation.lean` has 1303 lines)
$ grep -c 'gueP_map_unitary_conj\|GUEInvariance' <that file at c9a24cf>  -> 0
$ grep -n '^import' RBM3D/Universality/Step1Cond.lean  -> 6:import RBM3D.Universality.GUEInvariance ; 7:import RBM3D.Universality.EigenMeasurable ; 8:import RBM3D.Universality.OU
```
### b.8 Registry pre-check (CLAUDE.md §20 (2)) and full builds
```
$ git diff main...t/T2226 -- RBM3D/Test/Axioms.lean | grep '^[-+] '   (text cut to 100 columns)
-   `RBM.Univ.UNInfty1Row', -- bulk universality pin, primed successor of the refuted UNInfty1Row (T
+   `RBM.Univ.GUEGoodAt, -- bulk universality: the GUE-side good event (`vGUE` is [32]-regular, a so
# branch state (HEAD e8d327b, RBM3D.lean without the new import): Mon Oct  5 23:56:38 UTC 2026 ; exit=1
$ lake build 2>&1 | grep -n '^error' -A1  ->
2543:error: RBM3D.lean:269:0: axiom audit: 1 premise(s) that no theorem of this development proves are in none of `borrowedProps`, `owedProps`, `structuralProps`, `refutedProps`:
2544-  [RBM.Univ.UNInfty1Row']
--
2548:error: build failed
# the same with `import RBM3D.Universality.GUETranslation` added after the last import of RBM3D.lean (temporary, uncommitted; reverted by `git checkout RBM3D.lean`; `git status --short` empty afterwards):
Mon Oct  5 23:54:30 UTC 2026 ; exit=0 ; Build completed successfully (4030 jobs). ; AuditNegative: 1 line
# pre-check file (scratch, uncommitted): `import RBM3D` / `import RBM3D.Universality.GUETranslation` / `#assert_rbm_axioms`; `lake env lean precheck.lean`:
Mon Oct  5 23:55:11 UTC 2026 ; exit=0
axiom audit: 6614 theorems, 2243 definitions, 0 axioms in `RBM` (compiler-generated declarations excluded).
  RBM.Univ.UNL32: 29 [no certificate] ;   RBM.Univ.UNGUELocal: 38 [no certificate]
lines of precheck.out containing `UNInfty1Row'`: 0 ; non-vacuity certificates: 0 of 143 premises in the two ledgers; the rest are not known to 
list lengths main: {'borrowedProps': 1, 'owedProps': 141, 'structuralProps': 82, 'refutedProps': 6}
list lengths t/T2226: {'borrowedProps': 1, 'owedProps': 140, 'structuralProps': 83, 'refutedProps': 6}
```
### b.9 Narrative
- Delivered (commit e8d327b on t/T2226): new file `RBM3D/Universality/GUETranslation.lean` with targets 1, 2a, 2b, 3a, 3b, 4a, 4b, 4c and target 5. `un_infty1Row' : UNInfty1Row'` is proved as stated (`PinsDens.lean:88`, unchanged); no successor `UNInfty1Row''`, no statement changed, no hypothesis added (b.5).
- Ports (RBM2D `Universality/GUETranslation.lean` at c9a24cf -> this file): Props :52-73 -> :55, :69; `_Hs` :681, `_measurable_Hs` :688 -> `GUETranslation_F` :289, `_measurable_F` :295; `_integral_gue` :720 with `_integral_dbm_shift` :478 -> target 1 :337; `_core` :736 -> `GUETranslation_core_aux` :361 and `guetranslation_core` :576; `_uniform` :1015 -> :634; `guetranslationRow` :1057-1144 -> :665; `infty1Row_of_translation` :1151 -> :763; `_eventually_forall` :988 -> merged `step1Band_eventually_forall`; `_gue_count` :494-680 with its helpers -> merged `step1Band_gue_count`; `_rhoSC_pos` :122 -> merged `rhoSC_pos`.
- The 22 private helpers `GUETranslation_*` (:73-287) are copies of private helpers of RBM3D `Step1Band.lean` (lines 51-84, 97-148, 164-219, 223-267, 615-637) with the prefix renamed. `GUETranslation_core_aux` is `Step1Band_core` (`Step1Band.lean:719-929`) with `ρ n` the constant `ρ_sc(E₀)` (so `a0 = b0 = ρ_sc(E₀)` and the Lipschitz interval is `[ρ_sc(E₀)/2, 3ρ_sc(E₀)/2]`, not the ticket's `[ρ_sc(E₀)/2, 2ρ_sc(E₀)]`: internal choice), `vOU` -> `vGUE`, `Step1Band_good` -> `GUEGoodAt` (`c = min κ 1 / 960`, `C = CV = 2`), the `UNL32` data chosen by `choose` on the `∃ mfc`, `∃ ρ'` of `GUEGoodAt` (six premises by `un_L32_arith`, three token-equal to the components of `GUEGoodAt`). `guetranslation_core` applies it to `O(ρ_sc(E₀)⁻¹ ·)`; `smul_smul` gives `O` and `O((ρ_sc(0)/ρ_sc(E₀)) ·)`. `guetranslationRow`: `τs = 1/2`, `D = k + 1`, bad event `2 sup|O| / N`.
- 4a: `step1Band_row` (`E' = 0`, `τ₁ = 𝔠𝔡`) plus `UNGUETranslation` at `κ = (2 - |E'|)/2`, `E := E'`, `O(ρ_sc(E') ·)`, added in ℝ. The proof compares no two densities of one model: the model side is `step1Band_row` under `UNDens'`, the translation involves the GUE alone.
- Not targets (ticket): `UNGUELocal` (owed; hypothesis), `UNL32` (borrowed), `UNUnivMainRow` and the band/claim rows (other tickets), the C form, the refuted pins (b.2: the file names none), any change to merged files (b.1: two files).
- Instances: deterministic hypotheses discharged (`3 ≤ 3`, `sz0_adm`, `UNDens'` by `un_dens'_msc_zero` / `unDensBandRow'_of_row`, `|E'| < 2`, `|E| ≤ 2 - κ`, `IsTestFun bump`, `size → ∞` by `inst_sz0_size_tendsto`); kept as hypotheses (other gates' pins): `UNL32`, `UNGUELocal`, `UNLocAvgBand`, `UNTrLocalBandRow`, `UNNormBandRow`, `UNDensBandRow`, and in `inst_un_core'_band_zero` also `UNUnivMainRow`, `UNGreenCorrAll`, `UNClaimAll`. Nondegenerate: `inst_dilation_ne_one`, `E' = 1 ≠ E = 0`, `inst_good_nonempty_sz0`, and `inst_guetranslation_core_sz0` produces the sequence in the good event. Conclusions are eventual in `n` (DECISIONS §56); no concrete `n`, no threshold recomputed (those of (a) stand).
- Registry: the owed line of `UNInfty1Row'` is deleted (owed 141 -> 140). The pre-check flagged `RBM.Univ.GUEGoodAt` (before only a conclusion, now a hypothesis of `guetranslation_core`, `guetranslation_uniform`), so one line was appended to `structuralProps` next to `Step1LocalEventGUE` (82 -> 83). `UNGUETranslation`, `UNGUETranslationRow` are proved (conclusion heads), not registered.
- Root: at the branch commit alone the full `lake build` fails at the root audit (`UNInfty1Row'` is no longer owed and `RBM3D.lean` does not yet import the module; b.8); with the import line added temporarily it exits 0. The hub's merge step 4 adds the line. `main` moved to e1fec21 after the base 0d5868e; `git diff 0d5868e main --stat -- RBM3D/Test/Axioms.lean RBM3D.lean` -> RBM3D.lean | 3 +++ (so `Test/Axioms.lean` is unchanged on main since the base).

## (c) Verified Mathlib names (`env.contains`, script `names.lean`)
one_lt_div, inv_mul_cancel₀, smul_smul, div_eq_inv_mul, Filter.Tendsto.neg, Filter.Tendsto.add, Metric.tendsto_nhds,
tendsto_natCast_atTop_iff, tendsto_natCast_atTop_atTop, tendsto_rpow_neg_atTop, tendsto_rpow_atTop,
squeeze_zero_norm', Filter.Tendsto.div_atTop, Real.rpow_neg_one, inv_lt_one_of_one_lt₀, ENNReal.ofReal_lt_one,
MeasureTheory.measure_toMeasurable, MeasureTheory.toMeasurable, MeasureTheory.integral_indicator_const,
MeasureTheory.integral_mono_of_nonneg, MeasureTheory.abs_integral_le_integral_abs, MeasureTheory.Integrable.of_bound,
Set.eq_univ_of_forall, Real.rpow_natCast, Real.rpow_neg, ENNReal.toReal_le_of_le_ofReal,
MeasureTheory.measureReal_def, abs_pow_sub_pow_le, Real.rpow_nonneg, Real.rpow_le_rpow_of_exponent_le,
MeasureTheory.integral_sub, MeasureTheory.integral_add, MeasureTheory.integral_const, MeasureTheory.probReal_univ,
MeasureTheory.integral_congr_ae, Continuous.measurable, Measurable.prodMk, abs_add_le, inv_anti₀, pow_le_pow_left₀,
mul_le_mul_of_nonneg_left, Filter.Eventually.exists, Filter.Frequently.and_eventually, Filter.not_eventually,
Real.add_one_le_exp, Real.dist_eq, Matrix.IsHermitian.eigenvalues
`env.contains` is false for two spellings used in the file: `measure_univ` (with `open MeasureTheory`) is the `export` alias of `MeasureTheory.IsProbabilityMeasure.measure_univ` (`Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:65-67`); the root name `integral_sub` is not a declaration, the used `integral_sub` is `MeasureTheory.integral_sub` (listed). No name was verified absent.

## (d) Open issues and paper-delta candidates
- No blocker and no stop condition: `UNL32`'s premises are token-equal to `GUEGoodAt` at `τs = 1/2` (compiled `hprem`), `UNInfty1Row'` is true as stated. No (a′): nothing in (a) contradicted the Lean proofs.
- T2226a (design table, no paper statement): the portmap row UN-14 (`docs/reports/T2162-portmap.md:208`, column deps: `UN-08, UN-11, UN-13`) lists UN-08 as a dependency; by the imports it is transitive only (b.7: 0 uses of a `GUEInvariance` name in the RBM2D file; `Step1Cond.lean:6` imports `GUEInvariance`).
- T2226b (proof-internal; no Lean/paper statement difference): the internal time of `UNGUETranslation` is `τs = 1/2`, independent of `τ_U`, without `τs ≤ 𝔠𝔡` (as RBM2D paper-delta #139); the statement carries no `τs`. The dispatcher decides whether RBM3D's ledger needs an entry.
- T2226c (registry): `RBM.Univ.GUEGoodAt` registered as structural (b.8); the dispatcher may reclassify.
- Hub (merge note, §20 (3)): add `import RBM3D.Universality.GUETranslation` after the last import of `RBM3D.lean`; the thresholds of (a) (`ln N >= 165.32` / `176.41` translation; `2157.2` row, from `step1Good'`) were not recomputed.
