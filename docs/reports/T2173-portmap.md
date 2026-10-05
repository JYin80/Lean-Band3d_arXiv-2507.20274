# T2173 port map: the block Anderson form of Claim (417) (BA-DS design supplement, ticket T2173; Amend 1: the group label is BA-DS)

Regenerated Mon Oct  5 06:30:17 UTC 2026 (`date -u`) by the scripts of P.6 for the probe `RBM3D/Probe/T2173Pins.lean` (branch `t/T2173`, commit `a543154`, base `7738afa`, 4045 lines, 149 `#print axioms` lines, `lake env lean` exit 0).  RBM2D is read at `c9a24cf` (read-only, through `git show`).  T2162 and T2161 are read at their branch heads (`73b451c`, `82e72b3`).  Main was at `3e22603` (UN-01 = T2174, `RBM3D/Universality/Pins.lean`, merged) when the probe was written and is at `a52eb85` now: UN-08 (T2175, `GUEInvariance`) and UN-02a (T2177, `OU`, `EigenMeasurable`) are merged too; P.7 compiles the amendment against them.

## P.1 The pins of the probe and the T2162 pin each one modifies (script `pin_diff.py`)

Columns of the script: T2162 pin and its line in `RBM3D/Probe/T2162Pins.lean` (= the merged `Universality/Pins.lean` up to line numbers); the probe pin and its line in `T2173Pins.lean`; the number of whitespace-normalised lines of the declaration that differ.
```
T2162 pin              line   | probe pin              line   | differing lines of the declaration (whitespace-normalised)
UNOUQUE                636    | UNOUQUEk               2275   | 4 of 7 lines differ
UNOUDiag               647    | UNOUDiagk              2284   | 4 of 8 lines differ
UNEMCTE2               668    | UNEMCTE2k              2296   | 10 of 18 lines differ
UNJak                  693    | UNJakk                 2316   | 7 of 11 lines differ
UNUyw                  707    | UNUywk                 2329   | 8 of 12 lines differ
UNQueBand              403    | UNQuek                 2378   | 3 of 6 lines differ
UNLocAvgBand           415    | UNLocAvgk              2390   | 4 of 8 lines differ
UNMLOut                431    | UNMLOutBA              2414   | 5 of 5 lines differ
UNOUClaims             658    | UNOUClaimsk            2426   | 2 of 3 lines differ
UNOURow                792    | UNOURowk               2433   | 1 of 1 lines differ
UNEMCTE2Row            796    | UNEMCTE2Rowk           2441   | 3 of 4 lines differ
UNJakUywRow            804    | UNJakUywRowk           2448   | 4 of 5 lines differ
UNClaimRow             814    | UNClaimRowk            2456   | 6 of 6 lines differ
UNTrLocal              446    | UNTrLocalInit          2544   | 4 of 5 lines differ
vOU                    572    | vOUC                   2535   | 2 of 3 lines differ
UNStep1Good            583    | UNStep1GoodC           2553   | 4 of 12 lines differ
UNCore                 759    | UNCoreC                2570   | 3 of 8 lines differ
UNModel                103    | UNModel                119    | 4 of 8 lines differ
ouMat                  149    | ouMat                  179    | 2 of 3 lines differ
un_claimAll_of_rows    848    | un_claimAll_of_rowsk   2467   | 4 of 12 lines differ
```
What changes, pin by pin (read off the diff; the literal changed lines of all 20 pairs follow the table):

| pin | change against T2162 | exponents, window, thresholds |
|---|---|---|
| `UNModel` (A1) | field `mean`, `mean_herm`; `UNModel.band`: `mean = 0`; `UNModel.ba`: `mean = lam Psi` | - |
| `ouMat` (A1) | `mean + e^{-t/2}(H - mean) + sqrt(1 - e^{-t}) H'` (centred; `= ouMatNC` for `mean = 0`: `ouMat_band`) | `t*`, `ouTStar` unchanged |
| `UNOUQUEk` / `UNOUDiagk` | `UNModel.band sz` -> `K.M sz`; `|E| <= 2 - kappa` -> `K.bulk sz kappa E n` (BA: `ρ_N(E) >= kappa`) | window `W^{-ε₀} lam W^{d/2}/N` with `lam = sz.lam` in both models; `(ε₀, c) = (𝔡/3, 𝔡/6)`; `W^{-𝔡/15+τ}` unchanged |
| `UNEMCTE2k`, `UNJakk`, `UNUywk` | model `K.M sz`; profile coupling of `L1t, L2t, scirc`: `sz.lam n` -> `K.lamV sz n` (BA: `0`, `S^{(B)}(0) = I`) | `c' = 𝔠𝔡/30`, `C_n' = C_n + C + 1`, `N^{1-c'+Cτ_U}`: unchanged; BA `𝓑(y)` is one block (`unBadYBA_subset`) |
| `UNQuek` / `UNLocAvgk` | law `(K.M sz).μ`, matrix `(K.M sz).H`, bulk `K.bulk`, `msc` -> `K.mdet` (BA: `m(., lam)`) | `∩_z` and the block inside the probability (T2001b) as in T2162 |
| `UNMLOutBA` | `STFlow -> BAFlow`, `lemT -> BAflowT0`, `STLK.. -> STLKgL..` over the carrier `baFMz` **under `seqP (sz.withLam 0)`** | times `t_n <= t0_n` |
| `UNTrLocalInit`, `vOUC`, `UNStep1GoodC`, `UNCoreC` (A2) | read the DBM initial matrix `ouInit = μ + e^{-t*/2}(H - μ)`; `UNCoreC` has both `UNTrLocal` (H, a priori bound) and `UNTrLocalInit` (A, Step 1) | `τ_s <= 𝔠𝔡`, `N^{-3τ_s/8}` unchanged |
| BA rows `UNDensBARow`, `UNTrLocalBARow`, `UNTrLocalInitBARow`, `UNNormBARow`, `UNOURowBA`, ... | new (BA gate) | `κ/2`-bulk stability of the window; `𝔡/2` at `lam e^{t*/2}` (`admissible_lamHat`) |

Extreme inputs tried (compiled): `lam = 0` (`ba_zero_H`, `ba_zero_mean`, `ouMat_ba_zero`: the BA model is the band model of `sz.withLam 0`; `UNEMCTE2k_ba_zero`, `UNJakk_ba_zero`, `UNUywk_ba_zero`: the three bulk-free pins are equal; `BASelf_msc`: `(self_m)` at `g = 0` is the semicircle equation); `t = 0` (`UNOUQUEk_zero_of_UNQuek`: the OU claim is the consumed QUE; `ouMat_zero`); `mean = 0` (`ouMat_band`, `UNOUQUEk_band` ... `Iff.rfl`); the drift direction is nonzero (`inst_ba_mean_ne_zero`, `inst_drift_ne_zero`).

Literal changed lines (`pin_diff_lines.py`; `-` = T2162, `+` = probe, whitespace-normalised, cut at 150 characters):
```
== UNOUQUE (T2162 :636) -> UNOUQUEk (:2275)
- def UNOUQUE (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
+ def UNOUQUEk (K : UNKind d) (sz : Sizes d) (𝔡 τU : ℝ) : Prop :=
- ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
- ouP (UNModel.band sz) n
+ ∀ E : ℝ, K.bulk sz κ E n → ∀ a : Zd d (sz.L n),
+ ouP (K.M sz) n
- (ouMat (UNModel.band sz) n t ω)} ≤
+ (ouMat (K.M sz) n t ω)} ≤
== UNOUDiag (T2162 :647) -> UNOUDiagk (:2284)
- def UNOUDiag (sz : Sizes d) (τU : ℝ) : Prop :=
+ def UNOUDiagk (K : UNKind d) (sz : Sizes d) (τU : ℝ) : Prop :=
- ∀ E : ℝ, |E| ≤ 2 - κ →
- ouP (UNModel.band sz) n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
+ ∀ E : ℝ, K.bulk sz κ E n →
+ ouP (K.M sz) n {ω | ∃ x : Idx d (sz.L n) (sz.W n),
- ‖Gres (ouMat (UNModel.band sz) n t ω)
+ ‖Gres (ouMat (K.M sz) n t ω)
== UNEMCTE2 (T2162 :668) -> UNEMCTE2k (:2296)
- def UNEMCTE2 (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop :=
+ def UNEMCTE2k (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU Cn : ℝ) : Prop :=
- (stieltjesN (ouMat (UNModel.band sz) n s ω) (z j)).im) *
- L1t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z u)
- ∂(ouP (UNModel.band sz) n) ≤ B) →
+ (stieltjesN (ouMat (K.M sz) n s ω) (z j)).im) *
+ L1t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMat (K.M sz) n s ω) (z u)
+ ∂(ouP (K.M sz) n) ≤ B) →
- (stieltjesN (ouMat (UNModel.band sz) n s ω) (z k)).im) *
- L2t d (sz.L n) (sz.W n) (sz.lam n) (ouMat (UNModel.band sz) n s ω) (z u) (z v)
- ∂(ouP (UNModel.band sz) n) ≤ B) →
+ (stieltjesN (ouMat (K.M sz) n s ω) (z k)).im) *
+ L2t d (sz.L n) (sz.W n) (K.lamV sz n) (ouMat (K.M sz) n s ω) (z u) (z v)
+ ∂(ouP (K.M sz) n) ≤ B) →
- |(∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z i)).im ∂(ouP (UNModel.band sz) n)) -
- ∫ ω, ∏ i, (stieltjesN (ouMat (UNModel.band sz) n (ouTStar sz τU n) ω) (z i)).im
- ∂(ouP (UNModel.band sz) n)| ≤
+ |(∫ ω, ∏ i, (stieltjesN (ouMat (K.M sz) n t ω) (z i)).im ∂(ouP (K.M sz) n)) -
+ ∫ ω, ∏ i, (stieltjesN (ouMat (K.M sz) n (ouTStar sz τU n) ω) (z i)).im
+ ∂(ouP (K.M sz) n)| ≤
== UNJak (T2162 :693) -> UNJakk (:2316)
- def UNJak (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
+ def UNJakk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
- ∫ ω, (∏ j ∈ s, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z j)).im) *
- ‖∑ x, (Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁ *
- Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁) x x *
- scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
- Gres (ouMat (UNModel.band sz) n t ω) (z i) b₂ y y‖
- ∂(ouP (UNModel.band sz) n) ≤
+ ∫ ω, (∏ j ∈ s, (stieltjesN (ouMat (K.M sz) n t ω) (z j)).im) *
+ ‖∑ x, (Gres (ouMat (K.M sz) n t ω) (z i) b₁ *
+ Gres (ouMat (K.M sz) n t ω) (z i) b₁) x x *
+ scirc d (sz.L n) (sz.W n) (K.lamV sz n) x y *
+ Gres (ouMat (K.M sz) n t ω) (z i) b₂ y y‖
+ ∂(ouP (K.M sz) n) ≤
== UNUyw (T2162 :707) -> UNUywk (:2329)
- def UNUyw (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
+ def UNUywk (K : UNKind d) (sz : Sizes d) (E : ℝ) (nf : ℕ) (τU C c' : ℝ) : Prop :=
- ∫ ω, (∏ k ∈ s, (stieltjesN (ouMat (UNModel.band sz) n t ω) (z k)).im) *
- ‖∑ x, (Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁ *
- Gres (ouMat (UNModel.band sz) n t ω) (z i) b₁) x y *
- scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
- (Gres (ouMat (UNModel.band sz) n t ω) (z j) b₂ *
- Gres (ouMat (UNModel.band sz) n t ω) (z j) b₂) y x‖
- ∂(ouP (UNModel.band sz) n) ≤
+ ∫ ω, (∏ k ∈ s, (stieltjesN (ouMat (K.M sz) n t ω) (z k)).im) *
+ ‖∑ x, (Gres (ouMat (K.M sz) n t ω) (z i) b₁ *
+ Gres (ouMat (K.M sz) n t ω) (z i) b₁) x y *
+ scirc d (sz.L n) (sz.W n) (K.lamV sz n) x y *
+ (Gres (ouMat (K.M sz) n t ω) (z j) b₂ *
+ Gres (ouMat (K.M sz) n t ω) (z j) b₂) y x‖
+ ∂(ouP (K.M sz) n) ≤
== UNQueBand (T2162 :403) -> UNQuek (:2378)
- def UNQueBand : Prop :=
+ def UNQuek (K : ∀ d, UNKind d) : Prop :=
- ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ → ∀ a : Zd d (sz.L n),
- Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (Sizes.seqXmat sz n ω)} ≤
+ ∀ᶠ n in atTop, ∀ E : ℝ, (K d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
+ ((K d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((K d).M sz).H n ω)} ≤
== UNLocAvgBand (T2162 :415) -> UNLocAvgk (:2390)
- def UNLocAvgBand : Prop :=
+ def UNLocAvgk (K : ∀ d, UNKind d) : Prop :=
- Sizes.seqP sz {ω | ∃ z : ℂ, sz.locDomain κ ε n z ∧ ∃ a : Zd d (sz.L n),
+ ((K d).M sz).μ {ω | ∃ z : ℂ, ((K d).bulk sz κ z.re n ∧ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1) ∧
+ ∃ a : Zd d (sz.L n),
- Gres (Sizes.seqXmat sz n ω) z true x x - msc z‖} ≤
+ Gres (((K d).M sz).H n ω) z true x x - (K d).mdet sz n z‖} ≤
== UNMLOut (T2162 :431) -> UNMLOutBA (:2414)
- def UNMLOut (d : ℕ) : Prop :=
+ def UNMLOutBA (d : ℕ) : Prop :=
- STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
- STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
- STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t
+ BAFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
+ STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
+ STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STExp2gL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
+ STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t
== UNOUClaims (T2162 :658) -> UNOUClaimsk (:2426)
- def UNOUClaims : Prop :=
+ def UNOUClaimsk (K : ∀ d, UNKind d) : Prop :=
- ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUE sz 𝔡 τU ∧ UNOUDiag sz τU
+ ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNOUQUEk (K d) sz 𝔡 τU ∧ UNOUDiagk (K d) sz τU
== UNOURow (T2162 :792) -> UNOURowk (:2433)
- def UNOURow : Prop := (∀ d : ℕ, UNMLOut d) → UNLocAvgBand → UNQueBand → UNOUClaims
+ def UNOURowk (K : ∀ d, UNKind d) (ML Loc Que : Prop) : Prop := ML → Loc → Que → UNOUClaimsk K
== UNEMCTE2Row (T2162 :796) -> UNEMCTE2Rowk (:2441)
- def UNEMCTE2Row : Prop :=
+ def UNEMCTE2Rowk (K : ∀ d, UNKind d) : Prop :=
- ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
- ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2 sz E nf τU Cn
+ ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn τ₀ : ℝ, 0 < τ₀ ∧
+ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ → UNEMCTE2k (K d) sz E nf τU Cn
== UNJakUywRow (T2162 :804) -> UNJakUywRowk (:2448)
- def UNJakUywRow : Prop :=
- UNLocAvgBand → UNOUClaims → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
- ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
+ def UNJakUywRowk (K : ∀ d, UNKind d) (Loc : Prop) : Prop :=
+ Loc → UNOUClaimsk K → ∀ d : ℕ, 3 ≤ d → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
+ ∀ κ : ℝ, 0 < κ → ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ C τ₀ : ℝ, 0 < τ₀ ∧
- UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)
+ UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)
== UNClaimRow (T2162 :814) -> UNClaimRowk (:2456)
- def UNClaimRow : Prop :=
+ def UNClaimRowk (K : ∀ d, UNKind d) : Prop :=
- ∀ E : ℝ, |E| ≤ 2 - κ → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
- UNEMCTE2 sz E nf τU Cn ∧ UNJak sz E nf τU C (𝔠 * 𝔡 / 30) ∧ UNUyw sz E nf τU C (𝔠 * 𝔡 / 30)) →
+ ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → ∀ nf : ℕ, ∃ Cn C τ₀ : ℝ, 0 < τ₀ ∧
+ ∀ τU : ℝ, 0 < τU → τU ≤ τ₀ →
+ UNEMCTE2k (K d) sz E nf τU Cn ∧ UNJakk (K d) sz E nf τU C (𝔠 * 𝔡 / 30) ∧
+ UNUywk (K d) sz E nf τU C (𝔠 * 𝔡 / 30)) →
- ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E
+ ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAll sz ((K d).M sz) E
== UNTrLocal (T2162 :446) -> UNTrLocalInit (:2544)
- def UNTrLocal (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
- ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
+ def UNTrLocalInit (sz : Sizes d) (M : UNModel sz) (m : ℕ → ℂ → ℂ) (E δ : ℝ) : Prop :=
+ ∀ τs : ℝ, 0 < τs → τs < 1 → ∀ ε τ D : ℝ, 0 < ε → 0 < τ → 0 < D → ∀ᶠ n in atTop,
- ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) < ‖stieltjesN (M.H n ω) z - m n z‖} ≤
+ ((sz.W n : ℕ) : ℝ) ^ τ * sz.Bctl n (1 - z.im) <
+ ‖stieltjesN (ouInit M n (ouTStar sz τs n) ω) z - m n z‖} ≤
== vOU (T2162 :572) -> vOUC (:2535)
- def vOU (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) :
+ def vOUC (sz : Sizes d) (M : UNModel sz) (n : ℕ) (τs E₀ : ℝ) (ω : Sizes.SeqΩ sz) :
- fun i => Real.exp (-(ouTStar sz τs n) / 2) * (M.herm n ω).eigenvalues i - E₀
+ fun i => (ouInit_isHermitian M n (ouTStar sz τs n) ω).eigenvalues i - E₀
== UNStep1Good (T2162 :583) -> UNStep1GoodC (:2553)
- def UNStep1Good : Prop :=
+ def UNStep1GoodC : Prop :=
- UNDens m E ρ δ → UNTrLocal sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
+ UNDens m E ρ δ → UNTrLocalInit sz M m E δ → ∀ CV₀ : ℝ, 0 ≤ CV₀ → UNNormBound sz M CV₀ →
- M.μ {ω | ¬ (IsRegular32 (vOU sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
+ M.μ {ω | ¬ (IsRegular32 (vOUC sz M n τs E ω) (Nsz sz n ^ (-1 + τs / 4))
- ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOU sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
+ ∃ mfc : ℂ → ℂ, IsFreeConv32 (vOUC sz M n τs E ω) (1 - Real.exp (-(ouTStar sz τs n))) mfc ∧
== UNCore (T2162 :759) -> UNCoreC (:2570)
- def UNCore : Prop :=
+ def UNCoreC : Prop :=
- UNDens m E ρ δ → UNTrLocal sz M m E δ → (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) →
- UNClaimAll sz M E →
+ UNDens m E ρ δ → UNTrLocal sz M m E δ → UNTrLocalInit sz M m E δ →
+ (∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz M CV₀) → UNClaimAll sz M E →
== UNModel (T2162 :103) -> UNModel (:119)
- structure UNModel {d : ℕ} (sz : Sizes d) where
+ @[ext] structure UNModel {d : ℕ} (sz : Sizes d) where
+ /-- **(A1)** the deterministic mean `E H` -/
+ mean : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ
+ mean_herm : ∀ n, (mean n).IsHermitian
== ouMat (T2162 :149) -> ouMat (:179)
- Real.exp (-t / 2) • M.H n ω.1 + Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
+ M.mean n + Real.exp (-t / 2) • (M.H n ω.1 - M.mean n) +
+ Real.sqrt (1 - Real.exp (-t)) • Xmat d (sz.L n) (sz.W n) ω.2
== un_claimAll_of_rows (T2162 :848) -> un_claimAll_of_rowsk (:2467)
- theorem un_claimAll_of_rows (rC : UNClaimRow) (rE : UNEMCTE2Row) (rJ : UNJakUywRow) (rO : UNOURow)
- (hML : ∀ d : ℕ, UNMLOut d) (hLoc : UNLocAvgBand) (hQ : UNQueBand) :
+ theorem un_claimAll_of_rowsk (K : ∀ d, UNKind d) {ML Loc Que : Prop}
+ (rC : UNClaimRowk K) (rE : UNEMCTE2Rowk K) (rJ : UNJakUywRowk K Loc) (rO : UNOURowk K ML Loc Que)
+ (hML : ML) (hLoc : Loc) (hQ : Que) :
- ∀ E : ℝ, |E| ≤ 2 - κ → UNClaimAll sz (UNModel.band sz) E := by
+ ∀ E : ℝ, (∀ᶠ n in atTop, (K d).bulk sz κ E n) → UNClaimAll sz ((K d).M sz) E := by
```

## P.2 The 25 `GUEPhase/*` files, `ZeroModeProfile`, `QUEFlow` (RBM2D `c9a24cf`): which port once the model is a parameter, which need a BA twin

Method (script `declinv.py`, P.6): every top-level declaration of each file is split into signature and body (comments removed); a declaration is **T** if its signature mentions a deterministic-data token of the band chain (`msc`, `mE`, `mSig`, `Theta*`, `KLoop*`, `Kgen`, `kTwo*`, `Kcal`, `svar*`, `Spaper`, `sbSupport`, `Smix`, `Snorm`, `scirc`, `SB`, `mixVar`), **P** if it mentions only the scalar spectral flow or the primitive family as a parameter (`spectralZ`, `spectralM`, `lemT`, `lemE`, `etaT`, `zt`, `gueScale`, `gridTime`, `gueK*`, `Kt`), else clean.  `W_T = sigT + ½ bodyT`, `W_P = sigP + ½ bodyP` (lines, scaled to the kept lines of T2162 P.1).  Class: **T** if `W_T >= 15%` of the code lines; **P** if some `W_T` or `W_P >= 10%`; **G** otherwise.  Columns: `lines` = non-comment code lines at `c9a24cf`; `kept` = lines at RBM2D `0c1330a` (T2162 P.1).  The classification is from tokens, headers and imports, not from reading every proof: each UN preflight must re-check its file.

| file (RBM2D `Universality/`) | UN ticket | lines | kept | W_T | W_P | %T | %P | class | what is model-dependent (evidence: header, imports, declaration-level tokens) |
|---|---|---|---|---|---|---|---|---|---|
| AuxCarrier | UN-25 | 900 | 1082 | 55 | 0 | 6 | 0 | **P** | aux carrier `auxSizes` and `svar_aux_pos` use the band profile (`sbSupport`); BA `S^V = I` is positive on one block; chaos tails take any variance family |
| Bootstrap | UN-26 | 1207 | 595 | 0 | 71 | 0 | 6 | **G** | abstract ODE bootstraps with `SBgue = 1/L^d` (GUE profile): no matrix model, no `m` |
| BootstrapAt | UN-26 | 733 | 754 | 0 | 42 | 0 | 6 | **G** | size-scale form of `Bootstrap` |
| BoundsA | UN-33 | 691 | 746 | 0 | 454 | 0 | 66 | **P** | pathwise unfreezing; the scalar flow `spectralZ E u`, `spectralM` (`m = mE E`) becomes a parameter `m(E, lam)` |
| Drift | UN-34/35 | 1765 | 2093 | 0 | 390 | 0 | 22 | **P** | one GUE increment on any Hermitian `M`: only `spectralZ` (scalar `m`) enters, as a parameter |
| DuhamelA | UN-36/37 | 1897 | 2052 | 0 | 146 | 0 | 8 | **G** | Duhamel tail of loops of Hermitian matrices on the grid; no `m`, `Theta`, `S` |
| DuhamelB | UN-38 | 1070 | 1064 | 0 | 196 | 0 | 18 | **P** | dyadic stopping and Azuma on the grid; `spectralZ` as a parameter |
| DuhamelC | UN-39/40 | 1371 | 1543 | 74 | 682 | 5 | 50 | **P** | `gueGrid_loop_duhamel`; `spectralZ` as a parameter, imports `Green.Pins` |
| EntryDet | UN-30 | 1099 | 837 | 631 | 124 | 57 | 11 | **T** | deterministic core at the mixture profile `S_u = aS + b/N`: `stable_mix` (`1 - u m^2 S`), `mix_offdiag_det`; BA: `1 - u M^{(+,+)} S` with matrix `M` |
| EntryGrid | UN-43 | 809 | 925 | 0 | 294 | 0 | 36 | **P** | one-time law `map_gueH_eq_mixMat`; scalar `spectralM = m I` in the entry event, BA: `G - M` |
| EntryTail | UN-41/42 | 1312 | 1519 | 360 | 40 | 27 | 3 | **T** | `GUEEntryMix` at the mixture profile (`MixProfOK`, `mix_det`); LDE tails generic, interface with `EntryDet` is T |
| Eq729A | UN-44 | 1117 | 1087 | 405 | 161 | 36 | 14 | **T** | 2-loop algebra and `eq729_Kdisc` for `K~` with `msc`, `SBgue`, `KLoop.mSig` |
| Eq729B | UN-47 | 1350 | 1442 | 596 | 318 | 44 | 24 | **T** | Gronwall, `kTwoGUE_eq_ThetaTilde`, Lemma 2.8 (`lemT`, `lemE` at `msc`), `KLoop.Kcal` |
| Generator | UN-28 | 943 | 1152 | 0 | 157 | 0 | 17 | **P** | `genMatGUE`, `egtNGUE` on any Hermitian `M`: scalar spectral flow as a parameter; `m`-cancellation uses column sums of `SBgue` |
| Grid | UN-27 | 690 | 768 | 0 | 64 | 0 | 9 | **G** | carrier `Pgue` (band field at step 0, unit GUE steps): BA step-0 field `seqP (sz.withLam 0)` plus the mean; Lemma 2.8 homogeneity (`lemT`) |
| HypA | UN-48 | 1220 | 1032 | 218 | 657 | 18 | 54 | **T** | `Hyp_Kt_detDom`, `Hyp_Kt_disc`: `K~` bounds via Combes-Thomas (`CombesThomasFixedGap`), `msc`, `Theta` |
| HypB | UN-49 | 1451 | 1063 | 115 | 894 | 8 | 62 | **P** | pathwise assembly; entry bound `||G - m||_max` becomes `||G - M||_max` (matrix `M`) |
| KPrim | UN-29 | 719 | 799 | 473 | 7 | 66 | 1 | **T** | 2-loop primitive `kTwoGUE = W^{-d} mu (Theta_{t1 mu} + beta J)`, `mu = m(s1) m(s2)`; BA: matrix `M^{(s1,s2)}`, `Theta^{BA}`; the ODE existence `gueK_exists` is generic |
| LLTransfer | UN-50 | 452 | 467 | 10 | 242 | 2 | 54 | **P** | `oull_of_pathBounds`: `lemT`, `lemE` at `msc` |
| Markov | UN-32 | 908 | 923 | 0 | 0 | 0 | 0 | **G** | `Pgue` Markov toolkit (freezing, conditional sub-Gaussianity): no model data |
| OneLoop | UN-45/46 | 1541 | 1750 | 745 | 18 | 48 | 1 | **T** | Lemma 5.15 for 1-loops: stability of `1 - m^2 S^`, `Theta_{t1 m^2}` row sum (d=2: `1 + c(1+log L)`); BA: matrix `1 - M^{(+,+)} S^`, d>=3 no `log` |
| PathBounds | UN-50 | 495 | 566 | 314 | 65 | 63 | 13 | **T** | `gueGrid_pathBounds`, `gueBds_h745E/h746`: statements carry `KLoop.mSig`/`Kcal` |
| Proc | UN-31 | 1473 | 1440 | 288 | 674 | 20 | 46 | **T** | process layer; `gueKproc_detDom` (running maximum of `K~` from `KLoop.Kcal`, `mSig`); loop maxima generic |
| RandomLayerA | UN-51 | 604 | 549 | 27 | 129 | 4 | 21 | **P** | rows S1-S6, Lemma 2.8 at `z = e + i eta`: `lemE`, `lemT` with `msc`; BA: `BAt0`, `BAflowE` (T2161) |
| RandomLayerB | UN-51 | 156 | 180 | 0 | 37 | 0 | 24 | **P** | `g1Row`: OULL, OUEq747 from the ML outputs; Lemma 2.8 parameters |
| ZeroModeProfile | UN-51 | 928 | 566 | 248 | 0 | 27 | 0 | **T** | `Theta~ = Theta_T + alpha J`, oscillation `norm_ThetaTilde_sub_le` (d=2: `90(1+log L)`; d>=3: `lam^{-2}` from `Prop8ZeroMode`); BA: `BAProp8` |
| QUEFlow | UN-52 | 783 | 925 | 8 | 0 | 1 | 0 | **P** | QUE of `H_t` from (7.47) at the QUE scale, Markov step; reads the `Theta~` bound of `ZeroModeProfile` |

Sums (kept lines): T 10 files / 11038 lines, `W_T` 4277; P 12 files / 11789 lines, `W_T` 277, `W_P` 3511; G 5 files / 5092 lines, `W_P` 307; all 27: 27919 lines, `W_T` 4554, `W_P` 5772.

Reading.  The GUE-phase flow is `H~_u = sqrt(t₁) X + sqrt(u - t₁) Y` (`Grid.lean:83`): the band field `X` at step 0 and unit GUE increments `Y`.  For block Anderson the same flow holds with `X ↦ λΨ + V` (the paper's `(MBM)`, `1_2:686`, `H_0 = ilambda Ψ`; merged `seqHflowBA`), i.e. the centred flow.  Everything that sees only the increments (Markov, Drift, Duhamel, Bootstrap, Generator) is generic in the model once `spectralZ E u = E + (1 - u) m` takes `m = m(E, lam)` as a parameter (class G/P).  What changes is the deterministic data: `M ≠ m I` in the loops, the primitive `K~` (`Theta^{BA}` and `M^{(σ₁,σ₂)}` instead of `Theta` and `m(σ₁)m(σ₂)`), the mixture-profile stability, `Theta~` and its oscillation (class T).  These are exactly the objects T2161 re-proves for the BA chain (groups P, K); the BA twin of the T declarations reuses `BAProp5to8`, `BAKsolve`, `BAKbound` (T2161).

## P.3 Split table (target 5): new tickets, rows of T2161 that grow, totals

Estimated lines follow the convention of T2161 b.9: twin lines = α (sig-hw + ½ body-only) with α = 0.5 / 0.7 / 1.0 (lo / central / hi), 600-1500 lines per ticket.  Rows marked (probe) are priced from the new text of this probe.

| id | gate | RBM3D files | statements and sources | lo | central | hi | role | depends on |
|---|---|---|---|---|---|---|---|---|
| UN-01b | UN | `Universality/Pins.lean` (amend the merged T2174), `Universality/OU.lean` (3 lines, merged T2177), `Test/Axioms.lean` | A1, A2, `UNKind`, `UN*k`, generic rows, `un_claimAll_of_rowsk`, centred-flow lemmas (`ouMat_band`, `drift_entry`), `unBadY_subset'` (probe sections 1, 3a-3d, 4; instances) | 600 | 850 | 1100 | prover-hard | T2174, T2177 |
| BA-C1 | BA | `BA/UNPins` | `UNKind.ba`, `UNMLOutBA`, `UNLocAvgBA`, `UNQueBA`, `BAEnd_QUEL`, `UNQueBA_of_BAEnd_QUEL`, `ouMat_ba_eq_band_add`, `ouP_ba_eq_band`, the BA rows, `PrecL`/`STLKgL..` (law-corrected carrier), `ouMat_ba_eq_ouMatNC`, `ouInit_ba`, `admissible_lamHat`, `unBadYBA_*`, `baBUniv_of_rows`, class-sequence instances (probe sections 2-3, 4, 5) | 700 | 950 | 1300 | prover-hard | BA-D1, UN-01b |
| BA-C2 | BA | `BA/MReg` | uniform regularity of `(z, λ) ↦ m(z, λ)` on the bulk (rows `UNDensBARow`: Lipschitz in `Re z` uniformly in `η ∈ (0,10]`, `L`, `λ`; bulk stability `κ → κ/2`), the shift `|m(z, λ e^{t/2}) - m(z, λ)| <= C t` (for `UNTrLocalInitBARow`); sources: T2161 `BAoffDiag` (`:631`, the stability constant `ε <= |1 - t m²|` on the real axis, `(E : ℂ)` in its statement) and `BAPropM` (`:612`, propagator bounds at real `E`); the modulus off the real axis is in no T2161 pin, and RBM2D has no source (its `m` is `msc`) | 800 | 1100 | 1600 | prover-max | BA-D2, D3, D4, D6, D7 |
| BA-C3 | BA | `BA/GUEKPrim`, `BA/GUEEntry` | T declarations of KPrim, ZeroModeProfile, EntryDet, EntryTail (UN-29, 30, 41, 42, 51): matrix `K~`, `Theta~^{BA}`, mixture-profile stability and entry bounds with `M`; sources RBM2D `KPrim:64-77`, `ZeroModeProfile:391`, `EntryDet:102,278`, `EntryTail:82,112` | 788 | 1102 | 1575 | prover-max | BA-P8, BA-K1, C1 |
| BA-C4 | BA | `BA/GUEOneLoop` | T declarations of OneLoop, Eq729A (UN-44, 45, 46): Lemma 5.15 with `1 - M^{(+,+)} S^`, 2-loop algebra, `eq729_Kdisc`; sources `OneLoop:1660`, `Eq729A:274,722` | 620 | 868 | 1240 | prover-max | BA-K4, C3 |
| BA-C5 | BA | `BA/GUEHyp` | T declarations of Eq729B, HypA, Proc, PathBounds and the T bits of the P files (UN-31, 47, 48, 50): `kTwoGUE_eq_ThetaTilde`, `Hyp_Kt_detDom`, `gueKproc_detDom`, `gueGrid_pathBounds` with `M`, `zztE_BA`; sources `Eq729B:541,1051`, `HypA:775,892`, `Proc:59`, `PathBounds:437` | 870 | 1217 | 1739 | prover-max | BA-T4, T5, C4 |
| BA-N1 (T2161) | BA | `BA/UNStep1` | grows by about 300 lines (UNTrLocalBARow, UNTrLocalInitBARow via `BAEnd_locSC` at `sz.withLam (lamHat ..)`, `UNNormBARow`, BA instance of `UNStep1GoodC`): 1200 -> 1500 (hi: +1 ticket) | | | | prover-hard | BA-D6, M1, C2 |
| BA-N2 (T2161) | BA | `BA/UNBUniv` | grows by about 200 lines: `BAGlueUniv` re-pinned with `BAEnd_QUE`, `UNMLOutBA` (T2173b), instantiation of the generic rows at `UNKind.ba`, `baBUniv_of_rows`: 800 -> 1000 | | | | prover | BA-N1, C5 |

```
W_T (lines, scaled to kept lines): T-class files 4277, T-bits in the other files 277, total 4554
W_P (parametrisation, UN gate): total 5772

BA twin group (declarations whose statements mention the deterministic data)    W_T |    lo   cen    hi
G1 KPrim+ZeroModeProfile+EntryDet+EntryTail (UN-29,30,41,42,51)            1575 |   788  1102  1575
G2 OneLoop+Eq729A (UN-44,45,46)                                            1240 |   620   868  1240
G3 Eq729B+HypA+Proc+PathBounds (+T-bits of P files) (UN-31,47,48,50)       1739 |   870  1217  1739
total twin lines                                                                |  2278  3187  4554
tickets (greedy packing, cap 1500): {'lo': 2, 'cen': 3, 'hi': 5}

band-only UN design: twin of all 28 GUE-phase tickets, kept lines 27919 x alpha:
  lo: 13960 lines -> 12 tickets at 1250 lines
  cen: 19543 lines -> 16 tickets at 1250 lines
  hi: 27919 lines -> 23 tickets at 1250 lines

UN gate overhead of the model-generic design (parametrisation W_P x beta):  {'lo': 577, 'cen': 1154, 'hi': 1732} lines in the 28 GUE-phase tickets
BA total, model-generic UN design:  {'lo': 61, 'cen': 62, 'hi': 66}  (new BA tickets {'lo': 4, 'cen': 5, 'hi': 9} )
BA total, band-only UN design:      {'lo': 71, 'cen': 75, 'hi': 82}  (C1,C2 + full twin {'lo': 12, 'cen': 16, 'hi': 23} )
UN total with UN-01b: 52 + 1 = 53 (cap 60, DECISIONS 50)
```

**BA total = 57 (T2161) + 5 new (BA-C1..C5; lo 4, hi 9) - 0 replaced = 62 (61..66) ≤ 70, if the UN GUE-phase tickets UN-25..52 are written model-generic (P.4); UN becomes 52 + 1 (UN-01b) = 53 ≤ 60 (DECISIONS §50; 52 is T2162's count, splits made since, e.g. UN-02a, are not counted).  If UN-25..52 are written band-only, BA must twin all 28: 57 + 2 + 16 (12..23) = 75 (71..82) > 70.**  No T2161 row is replaced: BA-N1, BA-N2 grow.  UN-07 (800 lines, prover-max, T2162 P.3) stays: the abstract Step 1 uses the Lipschitz clause of `UNDens` for `ν ⊞ sc_t` against `ρ_n`, and with the centred flow the shift between the deterministic equivalent of `A` and `m(., λ)` is `O(t*)`.

## P.4 UN tickets (UN-01..52) that must be written model-generic so that BA reuses them

| UN tickets | what is generic | parameter | extra lines (est.) |
|---|---|---|---|
| UN-01 (merged, T2174) | amend: `UNModel.mean`, centred `ouMat`, `ouInit`, `UNKind`, `UN*k`, A2 pins, `UNCoreC`; repair 3 lines of the merged `OU.lean` (P.7) | `mean`, `K` | new ticket UN-01b, 850 |
| UN-02 (UN-02a merged, T2177: `OU.lean`, `EigenMeasurable.lean`) | `OU.lean`: 2 lemmas repaired for the centred `ouMat` (3 lines, in UN-01b); BA carrier: `ouMat (ba sz) - λΨ = ouMat (band (sz.withLam 0))` and the same `ouP`, so the merged `ouSample_law` applies at `sz.withLam 0` (`ouSample_law_ba`, compiled against the merged file, P.7); `EigenMeasurable.lean` unchanged; the conditioning part (`Step1Cond`) reads `ouInit` (`ouMat_eq_ouInit_add`) | `mean` | 0 (UN-02a), +100 (conditioning) |
| UN-03, 04, 05 | already model-abstract (`UNModel`) | - | 0 |
| UN-06 | band exact route `m = msc`; the BA stability is BA-C2 | - | 0 |
| UN-07 | stays (Lipschitz stability of `ν ⊞ sc_t`) | `UNDens` | 0 |
| UN-08..11 | GUE only (UN-08 merged, T2175 `GUEInvariance`: compiles unchanged, P.7) | - | 0 |
| UN-10 | band rows `UNTrLocalBandRow`, `UNNormBandRow`; BA rows are BA-N1/C2 | - | 0 |
| UN-12, 13, 14 | `vOUC`, `UNTrLocalInit`, `UNStep1GoodC`, `UNInfty1Row` reading `ouInit` | `ouInit` | +150 each |
| UN-15, 16, 17 | generator, Hessian, contraction for the Gaussian carrier with profile `svarF lamV` and a deterministic mean (`Φ_μ(Y) = Φ(μ + Y)` is `TestFunH`; the BA identity is the band identity at `Φ_μ`) | `lamV`, `mean` | +100 (UN-15) |
| UN-18 | `UNEMCTE2k`, a priori bound | `lamV`, bulk | +50 |
| UN-19..23 | Jak/Uyw spectral expansion, kernels, `𝓑(y)`: weights `SBR lamV`, window `lamQ` (`unBadY_subset'`) | `lamV`, `lamQ` | +100 (UN-19, 22) |
| UN-24 | UnivMain | - | 0 |
| UN-25..52 | class G (UN-26, 27, 32, 36, 37): nothing; class P (UN-25, 28, 33, 34, 35, 38, 39, 40, 43, 49, 50, 51, 52): `spectralZ`, `lemT`, `lemE` take `m(E, lam)` as a parameter, the carrier has the mean; class T (UN-29, 30, 31, 41, 42, 44, 45, 46, 47, 48, 50, 51): state the T declarations over a record of deterministic data (`m`, `K~`, `Theta~` bounds, mixture-profile constants); the band instance is proved in the UN ticket, the BA instance in BA-C3..C5 | `m`, `GUEDet` | `beta W_P` = 577 / 1154 / 1732 in total |

## P.5 Exponent table: rows added to (a)(i) (script `shift.py`; d = 3, `(𝔠, 𝔡) = (1/6, 1/10), (1/10, 1/20)`, `L = 4, 5`, `W = 32`)

```
c      dd     L  W   lam   N          c'        tau_U       t*=N^(-1+tU)  lamHat-lam   floor N^(-ts/4)  t*/floor    req N^(-c'+C tU)  naive(d lam Im m)
0.1667 0.100  4  32  0.3   2097152    5.556e-04 1.2626e-05  4.7692e-07    7.154e-08    9.4115e-01       5.067e-07   0.99578           0.745 
0.1667 0.100  4  32  10    2097152    5.556e-04 1.2626e-05  4.7692e-07    2.385e-06    9.4115e-01       5.067e-07   0.99578           16.800
0.1000 0.050  5  32  0.3   4096000    1.667e-04 3.7879e-06  2.4415e-07    3.662e-08    9.8115e-01       2.488e-07   0.99867           0.745 
0.1000 0.050  5  32  10    4096000    1.667e-04 3.7879e-06  2.4415e-07    1.221e-06    9.8115e-01       2.488e-07   0.99867           16.800
log10 N at which naive drift K = d*lam*Im m drops below N^(-a), a = c'-C tU  (K<1 only):
  c=0.1667 lam=0.3  K=0.745 a=2.904e-04 -> N > 10^440
  c=0.1667 lam=10   K=16.800 a=2.904e-04 -> never (K >= 1 >= N^(-a))
  c=0.1000 lam=0.3  K=0.745 a=8.712e-05 -> N > 10^1466
  c=0.1000 lam=10   K=16.800 a=8.712e-05 -> never (K >= 1 >= N^(-a))
```

| row | value | constraint | slack |
|---|---|---|---|
| `ℙ(𝓑)` (BA) | `≤ 1 · W^{-𝔡/15+τ}` (`unBadYBA_measure_le`); band `(2d+1) W^{-𝔡/15+τ}` | `c' = 𝔠𝔡/30` binds in both | exponent unchanged |
| local law at `λ̂ = λ e^{t*/2}` | admissible at `(𝔠, 𝔡/2)` (`admissible_lamHat`, `inst_admissible_lamHat`) | `0 <= t*_n <= 1`, `λ̂ <= 2 𝔡⁻¹` | `𝔡 -> 𝔡/2` in the constants of BA-N1 |
| shift `|λ̂ - λ| ≈ λ t*/2` | `7e-8` (λ = 0.3), `2.4e-6` (λ = 10) at `N = 2097152` | below the tolerance floor `N^{-τ_s/4}` of `UNTrLocalInit` by the factor `t*/floor = 5e-7` (`un_shift_absorb`, `inst_shift_absorb`) | `N^{-1+τ_U+τ_s/4}` |
| drift of the non-centred flow, naive `∫₀^{t*} <= d λ Im m` | `0.745` (λ = 0.3), `16.8` (λ = 10) (N-independent) vs the requirement `N^{-c'+C τ_U}` (`C = C_max = 21`, (a)), `c' - C τ_U = 23 c'/44` | fails for every `N` at λ = 10 (`K >= 1`); for λ = 0.3 only for `N > 10^{440}` (`10^{1466}` at `(1/10, 1/20)`) (`drift_not_absorbable`) | the centred flow has no drift (`drift_entry`, `ouMat_eq_ouMatNC_add`) |
| `κ`-dependence of constants (D403) | exponents `κ`-free, constants not: (a)(i) rows `κ-dependence`, `UNDens data`; `c` of `UNDens` is not `πκ` | fixed `κ` in every pin | unchanged |

## P.6 Scripts (verbatim; `$S` = the scratchpad `T2173/`)

### declinv.py (P.2)
```python
import re,os,collections,json
base='/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2173/r2d'
files=[('GUEPhase/'+f) for f in sorted(os.listdir(base+'/GUEPhase'))]+['ZeroModeProfile.lean','QUEFlow.lean']
T=re.compile(r'\b(msc|mE|mSig|mSigma|Theta\w*|PropTheta\w*|KLoop\w*|Kgen|kTwo\w*|Kcal|svar\w*|Spaper|sbSupport|Smix|Snorm|scirc|SB|centeredVariance\w*|mixVar)\b')
P=re.compile(r'\b(spectralZ|spectralM|lemT|lemE|etaT|zt|zt_re|gueScale|gridTime|gueK\w*|Kt)\b')
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe )*(theorem|lemma|def|abbrev|instance|structure|class|inductive|example)\b')
def strip_comments(lines):
    out=[];incom=False
    for l in lines:
        s=l
        if incom:
            if '-/' in s:
                s=s.split('-/',1)[1]; incom=False
            else:
                out.append(''); continue
        # remove complete /- ... -/ on the line
        while '/-' in s:
            a=s.index('/-')
            if '-/' in s[a+2:]:
                b=s.index('-/',a+2)
                s=s[:a]+s[b+2:]
            else:
                s=s[:a]; incom=True; break
        if '--' in s: s=s.split('--',1)[0]
        out.append(s)
    return out
tot=collections.OrderedDict()
print('%-30s %6s | %6s %6s %6s | %6s %6s' % ('file','code','sigT','bodyT','sigP','bodyP','clean'))
for f in files:
    raw=open(base+'/'+f).read().split('\n')
    L=strip_comments(raw)
    starts=[i for i,l in enumerate(L) if decl.match(l)]
    bounds=starts+[len(L)]
    cl=sum(1 for l in L if l.strip())
    sigT=bodyT=sigP=bodyP=clean=0
    for a,b in zip(bounds,bounds[1:]):
        seg=[l for l in L[a:b] if l.strip() and not re.match(r'^\s*(end |namespace|section|open |variable|set_option|omit)',l)]
        n=len(seg); text='\n'.join(seg)
        m=re.search(r':=|\bwhere\b|\n\s*\|',text)
        sig=text[:m.start()] if m else text
        if T.search(sig): sigT+=n
        elif T.search(text): bodyT+=n
        elif P.search(sig): sigP+=n
        elif P.search(text): bodyP+=n
        else: clean+=n
    tot[f]=(cl,sigT,bodyT,sigP,bodyP,clean)
    print('%-30s %6d | %6d %6d %6d | %6d %6d' % (f,cl,sigT,bodyT,sigP,bodyP,clean))
json.dump(tot,open('declinv.json','w'))
S=[sum(v[i] for v in tot.values()) for i in range(6)]
print('%-30s %6d | %6d %6d %6d | %6d %6d' % ('TOTAL',*S))
```

### split_total.py (P.3)
```python
import json,math
rows=json.load(open('classes.json'))   # name,ticket,code,kept,W_T,W_P,%T,%P,cls,scaledT,scaledP
alpha={'lo':0.5,'cen':0.7,'hi':1.0}
beta={'lo':0.1,'cen':0.2,'hi':0.3}
def pack(sizes,cap=1500,minimum=600):
    # greedy consecutive packing; a ticket may not exceed cap (a single group above cap is split in equal parts)
    tickets=0;cur=0
    for s in sizes:
        if s>cap:
            if cur>0: tickets+=1;cur=0
            tickets+=math.ceil(s/cap); continue
        if cur+s<=cap: cur+=s
        else: tickets+=1;cur=s
    if cur>0: tickets+=1
    return tickets
by={r[0]:r for r in rows}
groups={'G1 KPrim+ZeroModeProfile+EntryDet+EntryTail (UN-29,30,41,42,51)':['KPrim','ZeroModeProfile','EntryDet','EntryTail'],
        'G2 OneLoop+Eq729A (UN-44,45,46)':['OneLoop','Eq729A'],
        'G3 Eq729B+HypA+Proc+PathBounds (+T-bits of P files) (UN-31,47,48,50)':['Eq729B','HypA','Proc','PathBounds']}
others=[r for r in rows if r[0] not in sum(groups.values(),[])]
tbits=sum(r[9] for r in others)    # scaled W_T of the remaining 17 files (P/G classes)
print('W_T (lines, scaled to kept lines): T-class files %d, T-bits in the other files %d, total %d'%(sum(r[9] for r in rows if r[8]=='T'),tbits,sum(r[9] for r in rows)))
print('W_P (parametrisation, UN gate): total %d'%sum(r[10] for r in rows))
print()
print('%-72s %6s | %5s %5s %5s'%('BA twin group (declarations whose statements mention the deterministic data)','W_T','lo','cen','hi'))
tot={k:0 for k in alpha}; tick={k:[] for k in alpha}
for g,fs in groups.items():
    w=sum(by[f][9] for f in fs)
    if g.startswith('G3'): w+=tbits
    vals={k:round(alpha[k]*w) for k in alpha}
    for k in alpha: tot[k]+=vals[k]; tick[k].append(vals[k])
    print('%-72s %6d | %5d %5d %5d'%(g,w,vals['lo'],vals['cen'],vals['hi']))
print('%-72s %6s | %5d %5d %5d'%('total twin lines','',tot['lo'],tot['cen'],tot['hi']))
nt={k:pack(tick[k]) for k in alpha}
print('tickets (greedy packing, cap 1500):',nt)
print()
kept=sum(r[3] for r in rows)
print('band-only UN design: twin of all 28 GUE-phase tickets, kept lines %d x alpha:'%kept)
bo={}
for k in alpha:
    lines=alpha[k]*kept
    bo[k]=math.ceil(lines/1250)
    print('  %s: %d lines -> %d tickets at 1250 lines'%(k,round(lines),bo[k]))
print()
print('UN gate overhead of the model-generic design (parametrisation W_P x beta): ',{k:round(beta[k]*sum(r[10] for r in rows)) for k in beta},'lines in the 28 GUE-phase tickets')
# totals
base=57
newBA={'lo':2+nt['lo'],'cen':2+nt['cen'],'hi':2+1+nt['hi']+1}   # C1, C2 (hi: C2 split), twins, N1 growth (hi)
print('BA total, model-generic UN design: ',{k:base+newBA[k] for k in alpha}, ' (new BA tickets',newBA,')')
print('BA total, band-only UN design:     ',{k:base+2+bo[k] for k in alpha}, ' (C1,C2 + full twin',bo,')')
print('UN total with UN-01b: 52 + 1 = 53 (cap 60, DECISIONS 50)')
```

### shift.py (P.5)
```python
# T2173 target 4: sizes of the extra terms of the centred route at t <= t* = N^{-1+tau_U}, d = 3.
# exponents: c' = c*d/30 (P(B) binds), tau_U = c'/(2(Cmax+1)), Cmax = 21 (RBM2D constants, T2162 (a)), tau_s = c*d (Step 1).
import math
d=3
rows=[(1/6,1/10,4,32,0.3),(1/6,1/10,4,32,10.0),(1/10,1/20,5,32,0.3),(1/10,1/20,5,32,10.0)]
print("c      dd     L  W   lam   N          c'        tau_U       t*=N^(-1+tU)  lamHat-lam   floor N^(-ts/4)  t*/floor    req N^(-c'+C tU)  naive(d lam Im m)")
for c,dd,L,W,lam in rows:
    N=(W*L)**d
    cp=c*dd/30; tU=cp/(2*(21+1)); ts=c*dd
    ts_=N**(-1+tU)
    lh=lam*(math.exp(ts_/2)-1)
    floor=N**(-ts/4)
    req=N**(-cp+21*tU)
    imm=0.828 if lam==0.3 else 0.56   # Im m(E) at E=0, L=4 (T2173 (a) rows: rho_N*pi = 0.828, 0.559)
    naive=d*lam*imm
    print("%-6.4f %-6.3f %d  %d  %-5g %-10d %-9.3e %-11.4e %-13.4e %-12.3e %-16.4e %-11.3e %-17.5f %-6.3f"%(c,dd,L,W,lam,N,cp,tU,ts_,lh,floor,ts_/floor,req,naive))
print("log10 N at which naive drift K = d*lam*Im m drops below N^(-a), a = c'-C tU  (K<1 only):")
for c,dd,L,W,lam in rows:
    cp=c*dd/30; tU=cp/44; a=cp-21*tU
    imm=0.828 if lam==0.3 else 0.56
    K=d*lam*imm
    print("  c=%.4f lam=%-4g K=%.3f a=%.3e -> %s"%(c,lam,K,a, ("N > 10^%.0f"%(math.log10(1/K)/a)) if K<1 else "never (K >= 1 >= N^(-a))"))
```

### verify_verbatim.py (report b.1)
```python
# Check that every block of the probe that claims to be verbatim is identical to the branch file (git object, not a copy).
import json, subprocess
S='/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2173/'
R='/Users/junyin/Lean_proof/RBM3D'
probe=open('/Users/junyin/Lean_proof/RBM3D-wt/T2173/RBM3D/Probe/T2173Pins.lean').read().split('\n')
def show(br): return subprocess.run(['git','--no-optional-locks','show',br+':RBM3D/Probe/'+('T2162Pins.lean' if '62' in br else 'T2161Pins.lean')],capture_output=True,text=True,cwd=R).stdout.split('\n')
src={'t62':show('t/T2162'),'t61':show('t/T2161')}
plan=json.load(open(S+'plan18.json'))
pos=0; tot={'t62':[0,0,0],'t61':[0,0,0]}; rows=[]
for seg in plan:
    if seg[0]=='text':
        n=len(open(S+'parts/'+seg[1]).read().split('\n'))-1
        pos+=n; continue
    k,a,b=seg
    blk=src[k][a-1:b]
    got=probe[pos:pos+len(blk)]
    same=sum(1 for x,y in zip(blk,got) if x==y)
    tot[k][0]+=1; tot[k][1]+=len(blk); tot[k][2]+=same
    rows.append((k,a,b,pos+1,len(blk),same))
    pos+=len(blk)+1
for k,(nb,nl,ns) in tot.items(): print('%s: %d blocks, %d lines, identical %d, differing %d'%(k,nb,nl,ns,nl-ns))
bad=[r for r in rows if r[4]!=r[5]]
print('differing blocks:',bad)
# which T2162 lines are not copied (gaps)
cov=set()
for k,a,b,_,_,_ in rows:
    if k=='t62': cov.update(range(a,b+1))
n62=len(src['t62'])
gaps=[];i=1
while i<=n62:
    if i not in cov:
        j=i
        while j+1<=n62 and (j+1) not in cov: j+=1
        gaps.append((i,j)); i=j+1
    else: i+=1
print('T2162 line ranges not in the probe (header, amended model/OU, unused sections):',gaps)
```

### pin_diff.py (P.1, report b.3)
```python
import re,difflib,subprocess
R='/Users/junyin/Lean_proof/RBM3D'
old=subprocess.run(['git','--no-optional-locks','show','t/T2162:RBM3D/Probe/T2162Pins.lean'],capture_output=True,text=True,cwd=R).stdout.split('\n')
new=open('/Users/junyin/Lean_proof/RBM3D-wt/T2173/RBM3D/Probe/T2173Pins.lean').read().split('\n')
kw=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |protected )*(def|structure|theorem|abbrev|instance|lemma)\s+(\S+)')
def block(lines,name,after=0):
    # first declaration with this name at or after line index `after`; returns (start line (1-based), body lines without docstring)
    for i in range(after,len(lines)):
        m=kw.match(lines[i])
        if m and m.group(2).split('{')[0]==name:
            j=i+1
            while j<len(lines) and lines[j].strip()!='' and not kw.match(lines[j]) and not lines[j].startswith('/--') and not lines[j].startswith('end ') and not lines[j].startswith('/-!'):
                j+=1
            return i+1,[l.rstrip() for l in lines[i:j]]
    return None,None
pairs=[('UNOUQUE','UNOUQUEk'),('UNOUDiag','UNOUDiagk'),('UNEMCTE2','UNEMCTE2k'),('UNJak','UNJakk'),('UNUyw','UNUywk'),
       ('UNQueBand','UNQuek'),('UNLocAvgBand','UNLocAvgk'),('UNMLOut','UNMLOutBA'),('UNOUClaims','UNOUClaimsk'),
       ('UNOURow','UNOURowk'),('UNEMCTE2Row','UNEMCTE2Rowk'),('UNJakUywRow','UNJakUywRowk'),('UNClaimRow','UNClaimRowk'),
       ('UNTrLocal','UNTrLocalInit'),('vOU','vOUC'),('UNStep1Good','UNStep1GoodC'),('UNCore','UNCoreC'),
       ('UNModel','UNModel'),('ouMat','ouMat'),('un_claimAll_of_rows','un_claimAll_of_rowsk')]
print('%-22s %-6s | %-22s %-6s | differing lines of the declaration (whitespace-normalised)'%('T2162 pin','line','probe pin','line'))
for a,b in pairs:
    ia,ba=block(old,a)
    # the amended/new probe versions come after the verbatim ones: take the LAST declaration with that name for same-name pairs
    ib,bb=None,None
    start=0
    while True:
        i,bl=block(new,b,start)
        if i is None: break
        ib,bb=i,bl; start=i
    if ba is None or bb is None: print(a,b,'missing',ia,ib); continue
    sm=difflib.SequenceMatcher(None,[re.sub(r'\s+',' ',x).strip() for x in ba],[re.sub(r'\s+',' ',x).strip() for x in bb])
    ch=0
    for tag,i1,i2,j1,j2 in sm.get_opcodes():
        if tag!='equal': ch+=max(i2-i1,j2-j1)
    print('%-22s %-6d | %-22s %-6d | %d of %d lines differ'%(a,ia,b,ib,ch,len(ba)))
```

### pin_diff_lines.py (P.1, report b.3)
```python
# Literal changed lines (old -> new) of selected pins against the T2162 pin they modify (whitespace-normalised).
import re,difflib,subprocess,sys
exec(open('pin_diff.py').read().split("print('%-22s")[0])      # reuse block(), old, new, pairs
want=sys.argv[1:] or [a for a,b in pairs]
for a,b in pairs:
    if a not in want: continue
    ia,ba=block(old,a)
    ib,bb=None,None; start=0
    while True:
        i,bl=block(new,b,start)
        if i is None: break
        ib,bb=i,bl; start=i
    A=[re.sub(r'\s+',' ',x).strip() for x in ba]; B=[re.sub(r'\s+',' ',x).strip() for x in bb]
    print('== %s (T2162 :%d) -> %s (:%d)'%(a,ia,b,ib))
    for tag,i1,i2,j1,j2 in difflib.SequenceMatcher(None,A,B).get_opcodes():
        if tag=='equal': continue
        for x in A[i1:i2]: print('-',x[:150])
        for x in B[j1:j2]: print('+',x[:150])
```

### clash.py (report b.1)
```python
# Name-clash check: every declared name of the probe against every non-Probe file of RBM3D (base worktree and main).
import re,os,subprocess,collections
R='/Users/junyin/Lean_proof/RBM3D'
P='/Users/junyin/Lean_proof/RBM3D-wt/T2173/RBM3D/Probe/T2173Pins.lean'
decl=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s:({\[]+)')
def names_of(text,keep_inst=False):
    st=[];out=[]
    for l in text.split('\n'):
        m=re.match(r'^namespace\s+(\S+)',l)
        if m: st.append(('ns',m.group(1))); continue
        m=re.match(r'^section(?:\s+(\S+))?\s*$',l)
        if m: st.append(('sec','')); continue
        m=re.match(r'^end(?:\s+(\S+))?\s*$',l)
        if m:
            if st: st.pop()
            continue
        m=decl.match(l)
        if m and (keep_inst or m.group(1)!='instance'):
            pre='.'.join(n for k,n in st if k=='ns')
            out.append(((pre+'.'+m.group(2)) if pre else m.group(2),os.path.basename(''),))
    return [n for n,_ in out]
def tree(root):
    D=collections.defaultdict(list)
    for dp,dn,fn in os.walk(root):
        if '/Probe' in dp: continue
        for f in fn:
            if f.endswith('.lean'):
                p=os.path.join(dp,f)
                for n in names_of(open(p,encoding='utf-8').read()): D[n].append(os.path.relpath(p,root))
    return D
git=lambda *a: subprocess.run(['git','--no-optional-locks',*a],capture_output=True,text=True,cwd=R).stdout
mine=set(names_of(open(P).read()))
n62=set(names_of(git('show','t/T2162:RBM3D/Probe/T2162Pins.lean')))
n61=set(names_of(git('show','t/T2161:RBM3D/Probe/T2161Pins.lean')))
new=mine-n62-n61
print('declared names of the probe: %d (in the T2162 probe %d, in the T2161 probe %d, new in T2173 %d)'%(len(mine),len(mine&n62),len(mine&n61),len(new)))
for label,root in (('worktree base %s'%git('rev-parse','--short','7738afa').strip(),'/Users/junyin/Lean_proof/RBM3D-wt/T2173/RBM3D'),('main %s'%git('rev-parse','--short','main').strip(),R+'/RBM3D')):
    D=tree(root); cl=sorted(n for n in mine if n in D)
    print('%s: clashes %d; files %s; of the new names %d; amended names %s'%(label,len(cl),dict(collections.Counter(f for n in cl for f in D[n])),len([n for n in cl if n in new]),[n.split('.')[-1] if n.count('.')<3 else '.'.join(n.split('.')[-2:]) for n in cl if n in ('RBM.Univ.UNModel','RBM.Univ.UNModel.band','RBM.Univ.UNModel.ba','RBM.Univ.ouMat','RBM.Univ.ouMat_isHermitian','RBM.Univ.ouMat_zero')]))
```

### statements.py (report b.2)
```python
import re,sys
P='/Users/junyin/Lean_proof/RBM3D-wt/T2173/RBM3D/Probe/T2173Pins.lean'
L=open(P).read().split('\n')
kw=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable |protected )*(def|structure|theorem|abbrev|instance|lemma)\s+(\S+)')
def stmt(name):
    out=[]
    for i,l in enumerate(L):
        m=kw.match(l)
        if m and m.group(2)==name:
            j=i
            body=[]
            while j<len(L):
                body.append(L[j])
                # statement ends at the line containing ':= by' / ':=' (theorems) or at a blank line (defs)
                if (m.group(1) in ('theorem','lemma','instance')) and (':=' in L[j]):
                    break
                if m.group(1) in ('def','structure','abbrev') and j+1<len(L) and L[j+1].strip()=='':
                    break
                j+=1
            out.append((i+1,body))
    return out
for n in sys.argv[1:]:
    for ln,b in stmt(n):
        print('-- %s:%d'%(P.split('/')[-1],ln))
        for x in b: print(x)
```

### drift.py (report b.5; the script of (a), unchanged)
```python
# T2173 (ii): OU generator identity for H_t = e^{-t/2} H + sqrt(1-e^{-t}) H', H = V + lam*Psi (block Anderson),
# d = 3, L = 3, W = 2, N = (W L)^d = 216.  Non-centred flow (the T2162 `ouMat`) vs centred flow (mean lam*Psi kept fixed).
import itertools, math, sys
import numpy as np

d, L, W = 3, 3, 2
nb = L ** d; bs = W ** d; N = nb * bs
rng = np.random.default_rng(20261005)

# Psi^B: adjacency of Z_L^d (|a-b|_1 = 1 on the torus), Psi = Psi^B (x) I_{W^d}
pts = list(itertools.product(range(L), repeat=d))
idx = {p: i for i, p in enumerate(pts)}
def tdist(a, b): return sum(min((x - y) % L, (y - x) % L) for x, y in zip(a, b))
PsiB = np.array([[1.0 if tdist(a, b) == 1 else 0.0 for b in pts] for a in pts])
Psi = np.kron(PsiB, np.eye(bs))
SV = np.kron(np.eye(nb), np.ones((bs, bs)) / bs)          # S_xy = W^{-d} 1(same block)  (S^(B)(0) = I)
Sc = SV - 1.0 / N                                         # S° = S - 1/N
print("N=%d, row sums of Psi: %s, row sums of S^V: %.3f, ||Psi||=%.3f" % (N, set(PsiB.sum(1)), SV.sum(1)[0], np.linalg.norm(Psi, 2)))

# ---------------- A. exact (Wick) check for f(H) = Tr H^4 ----------------
def S_t(t): return math.exp(-t) * SV + (1 - math.exp(-t)) / N * np.ones((N, N))
def F_wick(t, lam, centred):
    A = lam * (Psi if centred else math.exp(-t / 2) * Psi)
    s = S_t(t); r = s.sum(1)
    A2 = A @ A
    return np.trace(A2 @ A2).real + 4 * np.sum(np.diag(A2) * r) + 2 * np.sum(r ** 2) + np.sum(np.diag(s) ** 2)
def rhs_wick(t, lam, centred):
    A = lam * (Psi if centred else math.exp(-t / 2) * Psi)
    s = S_t(t); r = s.sum(1); R = np.diag(r)
    ETr_H3Psi = np.trace(A @ A @ A @ Psi) + np.trace(A @ R @ Psi) + np.trace(R @ A @ Psi)
    drift = 0.0 if centred else -0.5 * math.exp(-t / 2) * lam * 4 * ETr_H3Psi
    EH2 = np.diag(A @ A) + r                              # E (H^2)_ii
    # sum_ij (ds_ij/dt) * 4 [E(H^2)_ii + E(H^2)_jj + E H_ii H_jj],  E H_ii H_jj = delta_ij s_ii,  ds/dt = -e^{-t} S°
    dS = -math.exp(-t) * Sc
    gen = 0.5 * 4 * (np.sum(dS * (EH2[:, None] + EH2[None, :])) + np.sum(np.diag(dS) * np.diag(s)))
    return drift, gen
# check the formula D_ij D_ji Tr H^4 = 4[(H^2)_ii + (H^2)_jj + H_ii H_jj] by finite differences on a random 5x5 matrix
Hs = rng.normal(size=(5, 5)) + 1j * rng.normal(size=(5, 5)); Hs = Hs + Hs.conj().T
def tr4(M): return np.trace(np.linalg.matrix_power(M, 4))
h = 1e-3; i, j = 1, 3
def E(a, b):
    M = np.zeros((5, 5), complex); M[a, b] = 1; return M
fd = (tr4(Hs + h * E(i, j) + h * E(j, i)) - tr4(Hs + h * E(i, j) - h * E(j, i)) - tr4(Hs - h * E(i, j) + h * E(j, i)) + tr4(Hs - h * E(i, j) - h * E(j, i))) / (4 * h * h)
ex = 4 * ((Hs @ Hs)[i, i] + (Hs @ Hs)[j, j] + Hs[i, i] * Hs[j, j])
print("A0. D_ij D_ji Tr H^4: finite difference %.6f%+.6fj vs formula %.6f%+.6fj" % (fd.real, fd.imag, ex.real, ex.imag))
print("A. exact Wick, f = Tr H^4:  d/dt E f (central difference of closed form)  vs  generator RHS")
print("   lam   flow        t     LHS             RHS(drift+gen)   drift term       RHS w/o drift    LHS-RHS")
for lam in (0.0, 0.3):
    for centred in (False, True):
        for t in (0.7,):
            hh = 1e-5
            lhs = (F_wick(t + hh, lam, centred) - F_wick(t - hh, lam, centred)) / (2 * hh)
            dr, gen = rhs_wick(t, lam, centred)
            print("   %-5g %-11s %-4g %-15.8f %-16.8f %-16.8f %-16.8f %.2e" % (lam, "centred" if centred else "non-centred", t, lhs, dr + gen, dr, gen, lhs - dr - gen))

# ---------------- B. Monte Carlo, f = Im N^{-1} Tr (H - z)^{-1} ----------------
def sample_herm(n, scale_var, M):
    A = (rng.normal(size=(M, n, n)) + 1j * rng.normal(size=(M, n, n))) / math.sqrt(2)   # E|A_ij|^2 = 1
    X = (A + A.conj().transpose(0, 2, 1)) / 2                                            # E|X_ij|^2 = 1/2 (incl. diagonal)
    return X * math.sqrt(2 * scale_var)
def sample_V(M):
    A = (rng.normal(size=(M, nb, bs, bs)) + 1j * rng.normal(size=(M, nb, bs, bs))) / math.sqrt(2)
    X = (A + A.conj().transpose(0, 1, 3, 2)) / 2 * math.sqrt(2 / bs)
    V = np.zeros((M, N, N), complex)
    for b in range(nb): V[:, b * bs:(b + 1) * bs, b * bs:(b + 1) * bs] = X[:, b]
    return V
def mc(lam, t, z, M, chunk=500):
    out = {k: [] for k in ("lhs_nc", "rhs_nc", "gen_nc", "drift_nc", "lhs_c", "rhs_c")}
    et2 = math.exp(-t / 2); sq = math.sqrt(1 - math.exp(-t)); c2 = 0.5 * math.exp(-t) / sq
    for _ in range(M // chunk):
        V = sample_V(chunk); Hp = sample_herm(N, 1.0 / N, chunk)
        for centred in (False, True):
            H0 = V + lam * Psi
            Ht = (lam * Psi + et2 * V if centred else et2 * H0) + sq * Hp
            G = np.linalg.inv(Ht - z * np.eye(N))
            G2 = G @ G
            Hdot = (-0.5 * et2 * (V if centred else H0)) + c2 * Hp
            lhs = -np.einsum('mij,mji->m', G2, Hdot) / N              # pathwise d/dt (1/N) Tr G
            g = np.einsum('mii->mi', G); h2 = np.einsum('mii->mi', G2)
            gen = -0.5 * math.exp(-t) * (2 * np.einsum('mi,ij,mj->m', h2, Sc, g)) / N
            dr = 0.5 * et2 * lam * np.einsum('mij,ji->m', G2, Psi) / N * (0 if centred else 1)   # -0.5 e^{-t/2} lam D_Psi F, D_Psi F = -Tr(G^2 Psi)/N
            # use Im of everything (f = Im F)
            if centred:
                out["lhs_c"].append(lhs.imag); out["rhs_c"].append(gen.imag)
            else:
                out["lhs_nc"].append(lhs.imag); out["rhs_nc"].append((gen + dr).imag)
                out["gen_nc"].append(gen.imag); out["drift_nc"].append(dr.imag)
    return {k: np.concatenate(v) for k, v in out.items()}
def ms(x): return "%+.5f +- %.5f" % (x.mean(), x.std(ddof=1) / math.sqrt(len(x)))
if len(sys.argv) > 1 and sys.argv[1] == "mc":
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
    print("B. Monte Carlo (M=%d samples), f = Im N^{-1}Tr G(z), mean +- standard error" % M)
    for lam, z, t in ((0.3, 0.2 + 0.5j, 0.7), (0.0, 0.2 + 0.5j, 0.7)):
        r = mc(lam, t, z, M)
        print(" lam=%-4g z=%s t=%g" % (lam, z, t))
        print("   non-centred: LHS %s | gen %s | drift %s | LHS-(gen+drift) %s | LHS-gen %s" % (ms(r["lhs_nc"]), ms(r["gen_nc"]), ms(r["drift_nc"]), ms(r["lhs_nc"] - r["rhs_nc"]), ms(r["lhs_nc"] - r["gen_nc"])))
        print("   centred    : LHS %s | gen(=RHS) %s | LHS-RHS %s" % (ms(r["lhs_c"]), ms(r["rhs_c"]), ms(r["lhs_c"] - r["rhs_c"])))
```

### size.py (report b.5; reads `drift.py`)
```python
# T2173 (ii): size of the drift contribution at t* = N^{-1+tau_U}, N=216 (d=3, L=3, W=2), H_0 = V + lam*Psi
import math, numpy as np, sys
sys.argv = ["x"]; src=open("drift.py").read(); exec(src.split("# ---------------- A.")[0]); exec("def sample_herm"+src.split("def sample_herm")[1].split("def mc")[0])
c, dd = 1 / 6, 1 / 10; cprime = c * dd / 30 * 5 / 5   # placeholder, recomputed below
cprime = min(c * dd / 6, c * (dd / 15 - dd / 30)); tauU = cprime / (2 * 22)
tstar = N ** (-1 + tauU)
print("c'=%.6g tau_U=%.6g (1/79200=%.6g) t*=N^{-1+tau_U}=%.6g (1/N=%.6g)  N^{-c'+C tau_U}(C=21)=%.5f" % (cprime, tauU, 1 / 79200, tstar, 1 / N, N ** (-cprime + 21 * tauU)))
M = 300
for lam, E in ((0.3, 0.2), (10.0, 0.2)):
    V = sample_V(M); H0 = V + lam * Psi
    for eta in (tstar, 0.5):
        z = E + 1j * eta
        G = np.linalg.inv(H0 - z * np.eye(N)); G2 = G @ G
        tr = np.einsum('mij,ji->m', G2, Psi) / N            # N^{-1} Tr(Psi G^2) = -D_Psi F
        imm = np.einsum('mii->m', G).imag.mean() / N
        coef = 0.5 * lam * np.abs(tr.imag)                  # |drift of Im m| per unit time, t = 0
        naive = 0.5 * lam * 6.0 * imm / eta                 # (lam/2) ||Psi|| Im m / eta
        print("lam=%-4g E=%.1f eta=%.5f | Im m=%.3f | sample (lam/2)|Im N^-1 Tr Psi G^2|: mean %.4g max %.4g | naive (lam/2)||Psi|| Im m/eta = %.4g | x t*: sample %.3g, naive %.3g" % (lam, E, eta, imm, coef.mean(), coef.max(), naive, tstar * coef.mean(), tstar * naive))
```

### names.lean (report (c); `lake env lean names.lean > names.out`)
```lean
import RBM3D.Probe.T2173Pins
#check @Complex.coe_smul
#check @Complex.real_smul
#check @Matrix.inv_eq_right_inv
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Matrix.trace_smul
#check @Matrix.trace_one
#check @Matrix.smul_mul
#check @eq_inv_of_mul_eq_one_left
#check @HasDerivAt.ofReal_comp
#check @HasDerivAt.mul_const
#check @HasDerivAt.exp
#check @HasDerivAt.sub_const
#check @HasDerivAt.div_const
#check @hasDerivAt_id
#check @tendsto_rpow_neg_atTop
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.exp_one_lt_d9
#check @Real.exp_le_exp
#check @Real.one_le_exp
#check @MeasureTheory.Measure.prod_prod
#check @Equiv.apply_symm_apply
#check @mul_left_cancel₀
#check @Complex.ofReal_ne_zero
#check @le_mul_of_one_le_right
#check @MeasureTheory.measure_mono
#check @add_sub_cancel_left
#check @Filter.Eventually.mono
#check_failure @eq_inv_iff_mul_eq_one₀
#check_failure @Matrix.inv_one
#check_failure @Real.abs_sqrt_sub_sqrt_le
```

### shorten.py (report (c); `names.out` -> `names_short.txt`)
```python
# Shorten the raw `#check @name` output of names.out: drop implicit and instance binders, join continuation lines.
import re,sys
raw=open('names.out',encoding='utf-8').read().split('\n')
lines=[]
for l in raw:
    if not l.strip(): continue
    if l.startswith('  ') and lines: lines[-1]+=' '+l.strip()
    else: lines.append(l)
def drop_binders(s):
    out='';i=0
    while i<len(s):
        c=s[i]
        if c in '{[' and (i==0 or s[i-1] in ' ∀(' or True):
            close={'{':'}','[':']'}[c]; depth=0; j=i
            while j<len(s):
                if s[j]==c: depth+=1
                elif s[j]==close:
                    depth-=1
                    if depth==0: break
                j+=1
            # only drop binder groups that follow the ∀ prefix region (before the first top-level comma)
            grp=s[i:j+1]
            keep=(c=='[' and ' : ' not in grp)   # anonymous instance binders such as `[IsScalarTower R α α]` stay
            out+=(grp+' ') if keep else ''; i=j+1
            if keep: i+=0
            if i<len(s) and s[i]==' ': i+=1
            continue
        out+=c; i+=1
    return out
res=[]
for l in lines:
    if l.startswith('@'): l=l[1:]
    if ' : ' in l and not l.startswith(('Unknown','Real.exp_one_lt_d9')):
        name,ty=l.split(' : ',1)
        # binder prefix: up to the first ', ' after the last binder; apply only to the part after leading ∀
        if ty.startswith('∀ '):
            m=re.match(r'∀ ((?:[\{\[\(].*?[\}\]\)]\s*)*?),',ty) # fallback not used
            # binder region = text before the first ',' that is at bracket depth 0
            depth=0;k=0
            for k,ch in enumerate(ty):
                if ch in '{[(': depth+=1
                elif ch in '}])': depth-=1
                elif ch==',' and depth==0: break
            head,tail=ty[:k],ty[k:]
            head=drop_binders(head)
            ty=head+tail
        l=name+' : '+ty
    res.append(l)
res=[l.replace('] ,','],') for l in res]
open('names_short.txt','w',encoding='utf-8').write('\n'.join(res)+'\n')
```

### amend_check.py (report b.1a, P.7)
```python
# Amendment A1 (UNModel.mean, centred ouMat) against the merged Universality files of main (commit C).
# Splices the probe's amended block into the merged Pins.lean, then compiles the merged files that use the
# amended names against it (scratch modules PinsA, OUAraw, OUA, EigenMeasurableA, GUEInvarianceA).
import subprocess, re, os, difflib, sys
S = '/private/tmp/claude-501/-Users-junyin-Lean-proof-RBM3D/e2e8bc03-a5c7-4581-b49e-f30bd123d3b2/scratchpad/T2173/amend/'
R = '/Users/junyin/Lean_proof/RBM3D'
WT = '/Users/junyin/Lean_proof/RBM3D-wt/T2173'
C = sys.argv[1] if len(sys.argv) > 1 else 'a52eb85'
def git_show(path): return subprocess.run(['git', '--no-optional-locks', 'show', C + ':' + path], capture_output=True, text=True, cwd=R).stdout
def lean(mod, out_olean=True):
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], capture_output=True, text=True, cwd=WT).stdout.strip() + ':' + S
    cmd = ['lake', 'env', 'lean', '--root=' + S] + (['-o', S + mod + '.olean'] if out_olean else []) + [S + mod + '.lean']
    p = subprocess.run(cmd, capture_output=True, text=True, cwd=WT, env=dict(os.environ, LEAN_PATH=lp))
    errs = [l.split(S)[-1] for l in (p.stdout + p.stderr).split('\n') if ': error:' in l]
    return p.returncode, errs
g = subprocess.run(['git', '--no-optional-locks', 'grep', '-l', 'ouMat\\|UNModel\\|ouP\\b', C, '--', 'RBM3D'], capture_output=True, text=True, cwd=R).stdout.split('\n')
print('merged files that mention ouMat, UNModel or ouP at main %s: %s' % (C, [x.split(':', 1)[1] for x in g if x and 'Probe' not in x]))
probe = open(WT + '/RBM3D/Probe/T2173Pins.lean', encoding='utf-8').read().split('\n')
main = git_show('RBM3D/Universality/Pins.lean').split('\n')
ps = [i for i, l in enumerate(probe) if l.startswith('/-! ### The abstract model')][0]
pe = [i for i, l in enumerate(probe) if i > ps and l.strip() == 'end OU'][0]
ms = [i for i, l in enumerate(main) if l.startswith('/-! ### The abstract model')][0]
me = [i for i, l in enumerate(main) if i > ms and l.strip() == 'end OU'][0]
open(S + 'PinsA.lean', 'w', encoding='utf-8').write('\n'.join(main[:ms] + probe[ps:pe + 1] + main[me + 1:]))
print('main %s: Universality/Pins.lean lines %d-%d (UNModel .. end OU) replaced by T2173Pins.lean lines %d-%d' % (C, ms + 1, me + 1, ps + 1, pe + 1))
rc, errs = lean('PinsA'); print('PinsA (merged Pins.lean, %d lines): rc=%d, errors %d' % (open(S + 'PinsA.lean', encoding='utf-8').read().count('\n'), rc, len(errs)))
ou = git_show('RBM3D/Universality/OU.lean').replace('import RBM3D.Universality.Pins', 'import PinsA')
open(S + 'OUAraw.lean', 'w', encoding='utf-8').write(ou)
rc, errs = lean('OUAraw', False); print('OU.lean unchanged: rc=%d, errors %d' % (rc, len(errs)))
for e in errs: print('   ' + e[:150])
old1 = "  rw [h, Xmat_add, Xmat_smul, Xmat_smul]\n  rfl\n"
new1 = "  rw [h, Xmat_add, Xmat_smul, Xmat_smul]\n  simp [ouMat, UNModel.band, Sizes.seqXmat]\n"
old2 = ("  have h3 : (fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => ouMat M n t ω i j) = fun ω =>\n"
        "      (Real.exp (-t / 2) : ℂ) * M.H n ω.1 i j +\n")
new2 = ("  have h3 : (fun ω : SeqΩ sz × Ω d (sz.L n) (sz.W n) => ouMat M n t ω i j) = fun ω =>\n"
        "      M.mean n i j + (Real.exp (-t / 2) : ℂ) * (M.H n ω.1 i j - M.mean n i j) +\n")
old3 = "  exact (h1.const_mul _).add (h2.const_mul _)\n\nend U0"
new3 = "  exact (((h1.sub_const _).const_mul _).const_add _).add (h2.const_mul _)\n\nend U0"
assert ou.count(old1) == 1 and ou.count(old2) == 1 and ou.count(old3) == 1
oup = ou.replace(old1, new1).replace(old2, new2).replace(old3, new3)
open(S + 'OUA.lean', 'w', encoding='utf-8').write(oup)
d = [l for l in difflib.unified_diff(ou.split('\n'), oup.split('\n'), 'OU.lean', 'OU.lean (repaired)', lineterm='', n=0) if not l.startswith('@@')]
print('repair of OU.lean: %d lines removed, %d added' % (sum(1 for l in d if l.startswith('-') and not l.startswith('---')), sum(1 for l in d if l.startswith('+') and not l.startswith('+++'))))
open(S + 'OU_repair.diff', 'w', encoding='utf-8').write('\n'.join(d) + '\n')
rc, errs = lean('OUA'); print('OU.lean repaired: rc=%d, errors %d' % (rc, len(errs)))
for f, mod, imp in (('EigenMeasurable', 'EigenMeasurableA', 'import RBM3D.Universality.OU'), ('GUEInvariance', 'GUEInvarianceA', 'import RBM3D.Universality.Pins')):
    t = git_show('RBM3D/Universality/%s.lean' % f).replace(imp, 'import OUA' if f == 'EigenMeasurable' else 'import PinsA')
    open(S + mod + '.lean', 'w', encoding='utf-8').write(t)
    rc, errs = lean(mod, False); print('%s.lean unchanged: rc=%d, errors %d' % (f, rc, len(errs)))

# BA corollaries of the merged band facts: the probe's translation identity (extracted verbatim) + merged ouSample_law
a = [i for i, l in enumerate(probe) if l.startswith('/-- **Translation identity of the centred flow**')][0]
b = [i for i, l in enumerate(probe) if i > a and l.startswith('theorem ouP_ba_eq_band')][0]
lemma = '\n'.join(probe[a:b + 2])
cor = """import OUA

noncomputable section

namespace RBM.Univ

open MeasureTheory Matrix Filter Topology ProbabilityTheory
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal

variable {d : ℕ}

""" + lemma + """

theorem ouMat_ba_coord (sz : Sizes d) (n : ℕ) (t : ℝ) (ω : Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    ouMat (UNModel.ba sz) n t ω - ((sz.lam n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) =
      Xmat d (sz.L n) (sz.W n) (ouSample (sz.withLam 0) n t ω) := by
  rw [ouMat_ba_eq_band_add]
  exact ouMat_eq_Xmat_ouSample (sz.withLam 0) n t ω

theorem ouSample_law_ba (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (ouP (UNModel.ba sz) n).map (ouSample (sz.withLam 0) n t) =
      Measure.infinitePi (fun c => gaussianReal 0 (ouVar d (sz.L n) (sz.W n) 0 t c)) :=
  ouSample_law (sz.withLam 0) n ht

end RBM.Univ
"""
open(S + 'BAcor.lean', 'w', encoding='utf-8').write(cor)
rc, errs = lean('BAcor', False); print('BA corollaries (probe lemmas ouMat_ba_eq_band_add, ouP_ba_eq_band; ouMat_ba_coord; ouSample_law_ba = merged ouSample_law at sz.withLam 0): rc=%d, errors %d' % (rc, len(errs)))
```

### dep.lean (report (c); `lake env lean dep.lean`, output verbatim)
```lean
import RBM3D.Probe.T2173Pins
example (p : Prop) [Decidable p] (h : p) (a b : ℕ) : (if p then a else b) = a := by rw [if_pos h]
example (a b : ℕ) : (if True then a else b) = a := by rw [if_true]
example (a b : ℕ) : (if False then a else b) = b := by rw [if_false]
example (p : Prop) [Decidable p] (h : p) (f : p → ℕ) (g : ¬p → ℕ) : (if hp : p then f hp else g hp) = f h := by rw [dif_pos h]
```
```
dep.lean:2:88: warning: `if_pos` has been deprecated: Use `ite_eq_left` instead
dep.lean:3:58: warning: `if_true` has been deprecated: Use `ite_true` instead
dep.lean:4:59: warning: `if_false` has been deprecated: Use `ite_false` instead
dep.lean:5:116: warning: `dif_pos` has been deprecated: Use `dite_eq_left` instead
```

### Output of clash.py (verbatim, `clash.out`)
```
declared names of the probe: 326 (in the T2162 probe 83, in the T2161 probe 112, new in T2173 131)
worktree base 7738afa: clashes 0; files {}; of the new names 0; amended names []
main a52eb85: clashes 83; files {'Universality/Pins.lean': 83}; of the new names 0; amended names ['UNModel', 'UNModel.ba', 'UNModel.band', 'ouMat', 'ouMat_isHermitian', 'ouMat_zero']
```

## P.7 Amendment A1 against the merged files (script `amend_check.py`, output verbatim)

The probe's block `UNModel` .. `ouMat_zero` replaces the same block of the merged `Universality/Pins.lean` (main `a52eb85`); the merged files that use the amended names are compiled against it (scratch modules, `lake env lean --root`).
```
merged files that mention ouMat, UNModel or ouP at main a52eb85: ['RBM3D/Universality/EigenMeasurable.lean', 'RBM3D/Universality/OU.lean', 'RBM3D/Universality/Pins.lean']
main a52eb85: Universality/Pins.lean lines 97-164 (UNModel .. end OU) replaced by T2173Pins.lean lines 113-201
PinsA (merged Pins.lean, 1921 lines): rc=0, errors 0
OU.lean unchanged: rc=1, errors 2
   OUAraw.lean:69:2: error: Tactic `rfl` failed: The left-hand side
   OUAraw.lean:89:84: error: unsolved goals
repair of OU.lean: 3 lines removed, 3 added
OU.lean repaired: rc=0, errors 0
EigenMeasurable.lean unchanged: rc=0, errors 0
GUEInvariance.lean unchanged: rc=0, errors 0
BA corollaries (probe lemmas ouMat_ba_eq_band_add, ouP_ba_eq_band; ouMat_ba_coord; ouSample_law_ba = merged ouSample_law at sz.withLam 0): rc=0, errors 0
```
The two errors are `OU.lean:69` (`rfl` in `ouMat_eq_Xmat_ouSample`, the unfolding `ouMat (UNModel.band sz) = e^{-t/2} • Xmat + ...` needs `mean = 0`) and `OU.lean:89` (`h3` of `measurable_ouMat`, the entry formula needs the mean).  The repair (`OU_repair.diff`):
```
--- OU.lean
+++ OU.lean (repaired)
-  rfl
+  simp [ouMat, UNModel.band, Sizes.seqXmat]
-      (Real.exp (-t / 2) : ℂ) * M.H n ω.1 i j +
+      M.mean n i j + (Real.exp (-t / 2) : ℂ) * (M.H n ω.1 i j - M.mean n i j) +
-  exact (h1.const_mul _).add (h2.const_mul _)
+  exact (((h1.sub_const _).const_mul _).const_add _).add (h2.const_mul _)
```
