/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.GridDuhamelN
import RBM3D.Induction.LoopC2N

/-!
# The assembly of the stopped grid evolution (`d ≥ 3`): pins, the stopped Azuma bound for the
# first-chaos part, and the assembled pathwise bound

Ticket T2154 (ST2-33, stochastic layer ST-2).  Port of RBM2D `Induction/GridAssemblyN.lean` and of
the pins of `Induction/GridGoodN.lean` §3-4 (`:297-520`) at commit `c9a24cf` (cited
`GridAssemblyN:<line>`, `GridGoodN:<line>`), which are ports of RBM1D `Gauss/GridAssemblyV2.lean`
at `c06b103`.  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: the martingale term of
`int_K-L_ST` (`3_5:134`) and `alu9_STime` (`3_5:218-240`), with BDG replaced by Azuma-Hoeffding
(DECISIONS §10), and the assembly of the stopped grid evolution (DECISIONS §7: per-time laws,
stopping times only on the grid walk).

## What is here (namespace `RBM.Ind`)

* §1 the pins (statements): `StoppedAzumaZN`, `qvFormN`, `AzumaSubGN`, `YMomentBoundsN`,
  `YMomentsConclN`, `YMomentsN`, `GridAssemblyHypN`, `AssembledN`.  `AzumaSubGN` and `YMomentsN`
  are statements only (ST2-34/35 prove them); `stoppedAzumaZN` and `assembledN` below prove the
  pins `StoppedAzumaZN` and `AssembledN`.
* §2-4 helpers (private, prefix `gridAsm_`): the fourth-moment bound for real martingale
  differences, the complex Azuma step, the coarse row bound of the kernel `Ugen`.
* §5 `gridAsm_stronglyMeasurable_ZvecN`, `gridAsm_stronglyMeasurable_YvecN` (public): `ZvecN`,
  `YvecN` are `filt (j+1)`-strongly measurable for every `j` (RBM2D `GridGoodN:981-996`, not in the
  merged `GridGoodN`; needed for the `hZmeas` field of `AssembledN` and the first field of
  `YMomentBoundsN`).
* §6 the target `stoppedAzumaZN : StoppedAzumaZN sz E s t K`.
* §7-10 the probability budgets, the fourth-moment tail of `Y`, the single-scale core and the
  target `assembledN : AssembledN sz`.
* §11 compiled nonempty instances at `d = 3` on the merged `sz0` (namespace `GridAssemblyNInst`),
  §12 statement checks.

## Dictionary and `d`-dependent constants

`d : Sizes` becomes `sz : Sizes d`; `Z2 (d.L n)` becomes `Zd d (sz.L n)`; `Coord`, `gvar`,
`coordinateMatrix` become `CoordF d L W`, `gvarF d L W (sz.lam n)`, `coordinateMatrix d L W`;
RBM2D's `Ugen (d.L n) E σ` becomes the merged `Ugen d (sz.L n) (sz.lam n) E σ` (`= UN`, slot
parameter `m(σ_i) m(σ_{i+1})` via `cycProd`, `finRotate`);
`ukerMat L (m m')` is `uKer d L g (cycProd m i)`; `eeN` is `sz.STeeM n`;
`SizeTendsto d`, `RangeCond d τ' t` are `sz.SizeTendsto`, `sz.RangeCond τ' t`.
`[NeZero k]` is dropped from every pin and theorem (`Fin k → Zd d L` is nonempty for every `k`; the
statements are strictly stronger; paper-delta candidate `T2154a`).  The label count is
`(L^d)^k ≤ ((W L)^d)^k = N^k`, so the exponent count `D₁ + 4D + k + 2C_P + 8 ≤ C_K` of RBM2D is
unchanged: `d` enters only through `N = (W L)^d`.  The coarse row sum of `Ugen` is
`(1 + (1 - u_m)⁻¹)^k` (`d`-free); the RBM2D constant `729 = ((1 + 2)^3)^2` of the instance witness
is `k`- and `u_m`-dependent, not `d`-dependent (here `78 ≥ ((31/15)^3)^2` at `u_m ≤ 1/16`).

Every helper is `private` or carries the prefix `gridAsm_`; the public declarations other than the
pins and the two targets are `gridAsm_*` (the two measurability results and the instance data of
`GridAssemblyNInst`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-! ## 1. The pins (RBM2D `Induction/GridGoodN.lean:297-520` at `c9a24cf`) -/

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **Pin `StoppedAzumaZN`** (RBM2D `GridGoodN:297`): the merged `StoppedAzumaN` (`GridDuhamelN`)
with the first-chaos part `ZvecN` in place of `martIncN`.  The sharp sub-Gaussian proxy is
available only for `ZvecN` (`QVPropagatedN` gives the gradient at `H_j`, not on the segment
`[H_j, H_{j+1}]`), so the merged pin cannot be fed by `AzumaSubGN`.  Paper: `alu9_STime`
(`3_5:218-240`) with BDG replaced by Azuma (DECISIONS §10).  Dictionary: `Z2 (d.L n)` is
`Zd d (sz.L n)`, `Ugen` carries the coupling `sz.lam n`, `[NeZero k]` is dropped (paper-delta
candidate `T2154a`).  Proved below as `stoppedAzumaZN`. -/
def StoppedAzumaZN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (m : ℕ), m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < m, SubGaussStopN sz (E n) σ (gridTime s t K n) τ
        (fun j ω => ZvecN sz E s t K n j σ ω) m a j (c j)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (ZvecN sz E s t K n j σ ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- `Re Σ_{b,b'} κ_b conj(κ_{b'}) (𝓔⊗𝓔)_{b,b'}(M)` for the propagator weights
`κ_b = Π_i (𝒰-slot)(a_i, b_i)` of `𝒰_{v,w,σ}` and `𝓔⊗𝓔` at the spectral time `v`: the right-hand
side of the merged `QVPropagatedN` (`QVN.lean:799`) at `κ = κ_·` (without its factor `k`; paper
`(alu9_STime)`: `((𝒰_σ ⊗ 𝒰_σ̄) ∘ (𝓔⊗𝓔))_{a,a}`).  RBM2D `qvFormN` (`GridGoodN:313`);
`ukerMat L (m_i m_{i+1})` is the merged `uKer d L g (cycProd m i)`, `eeN` is `STeeM`. -/
def qvFormN (n : ℕ) (E v w : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Fin k → Zd d (sz.L n)) : ℝ :=
  (∑ b : Fin k → Zd d (sz.L n), ∑ b' : Fin k → Zd d (sz.L n),
    (∏ i : Fin k, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w
        (a i) (b i)) *
      (starRingEnd ℂ) (∏ i : Fin k, uKer d (sz.L n) (sz.lam n)
        (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b' i)) *
      sz.STeeM n E v M σ b b').re

/-- **Pin `AzumaSubGN`** (the Azuma proxies; RBM2D `GridGoodN:335`; statement only here, proved by
ST2-34/35): for a finite family `Φ` of observables in the Hermitian test class, weights `κ`, a
stopping family `{j<τ} ∈ F_j` on which the grid state lies in a set `G j`, and `Q` majorising the
conditional-variance form `Δ Σ_c gvar_c ‖Σ_b κ_b ∂_c Φ_b(M)‖²` on the Hermitian matrices of `G j`:
the stopped combination `1_{j<τ} Σ_b κ_b Z_b` of the first-chaos parts is conditionally
sub-Gaussian with proxy `Q` (real and imaginary parts).  Dictionary: `Coord ↦ CoordF`,
`gvar ↦ gvarF d L W (sz.lam n)`, `coordinateMatrix d L W`. -/
def AzumaSubGN (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) {ι : Type} [Fintype ι]
    (Φ : ι → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ),
    (∀ b, HermTestFun sz n (Φ b)) → ∀ (κ : ι → ℂ) (τ : PathΩ sz → ℕ)
    (G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    (∀ ω j, j < τ ω → pathH sz s t K n j ω ∈ G j) →
    ∀ (j : ℕ) (Q : ℝ≥0),
      (∀ M ∈ G j, M.IsHermitian →
        gridStep s t K n * ∑ c : CoordF d (sz.L n) (sz.W n),
          (gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ) *
          ‖∑ b, κ b * dirDerivN (Φ b) M (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤ (Q : ℝ)) →
      SubGaussFormN sz j τ (fun ω => ∑ b, κ b * ZfamN sz s t K n j Φ ω b) Q

/-- The moment inputs of the fourth-moment tail (RBM2D `YMomentBoundsN`, `GridGoodN:412`; RBM1D
`GridAssemblyHypPW` fields `hYmeas`, `hYmean*`, `hYint*`, `hYcond*`, `hY4*`,
`Gauss/GridAssemblyV2.lean:524`): `Y_j` is `F_{j+1}`-measurable; the stopped, propagated increment
has conditional mean zero, integrable fourth power, conditional second moment `≤ v_j` and fourth
moment `≤ w_j` (real and imaginary parts). -/
def YMomentBoundsN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (v w : ℕ → ℝ) : Prop :=
  (∀ j, StronglyMeasurable[filt sz (j + 1)] (Y j)) ∧
  ∀ m ≤ K, ∀ (b : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
    (pathP sz)[fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).re | filt sz j] =ᵐ[pathP sz] 0 ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).im | filt sz j] =ᵐ[pathP sz] 0 ∧
    Integrable (fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).re ^ 4) (pathP sz) ∧
    Integrable (fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).im ^ 4) (pathP sz) ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).re ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => v j) ∧
    (pathP sz)[fun ω => (stoppedEdgeN sz E σ u (u m) τ Y b j ω).im ^ 2 | filt sz j]
      ≤ᵐ[pathP sz] (fun _ => v j) ∧
    ∫ ω, (stoppedEdgeN sz E σ u (u m) τ Y b j ω).re ^ 4 ∂(pathP sz) ≤ w j ∧
    ∫ ω, (stoppedEdgeN sz E σ u (u m) τ Y b j ω).im ^ 4 ∂(pathP sz) ≤ w j

/-- The conclusion of `YMomentsN` at loop length `k` and signs `σ` (RBM2D `GridGoodN:429`; the
`∃ C_P` sits after `K`, so `C_P` may depend on `K`: see the report, (d)). -/
def YMomentsConclN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (σ : Fin k → Bool) : Prop :=
  ∃ C_P : ℝ, 0 ≤ C_P ∧
    ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsN sz (E n) σ (gridTime s t K n) τ (K n)
          (fun j ω => YvecN sz E s t K n j σ ω)
          (fun _ => gridStep s t K n ^ 2 * P) (fun _ => gridStep s t K n ^ 4 * P ^ 2)

/-- **Pin `YMomentsN`** (RBM2D `GridGoodN:445`; statement only here, proved by ST2-34/35): the `Y`
moment inputs hold for `YvecN` with the deterministic levels `v_j = Δ² P`, `w_j = Δ⁴ P²`,
`P ≤ N^{C_P}`, for every stopping family `{j<τ}`.  They use only the crude global second-derivative
bound of the loops (`HermTestFunLoopN`) and `RangeCond` (`η ≥ c_κ N^{-(1-τ')}`), not the good set.
`RangeCond d τ' t` is the merged `sz.RangeCond τ' t`, `SizeTendsto d` is `sz.SizeTendsto`. -/
def YMomentsN (κ τ' : ℝ) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  (∀ n, K n ≠ 0) → sz.SizeTendsto → sz.RangeCond τ' t →
  ∀ (k : ℕ) (σ : Fin k → Bool), YMomentsConclN sz E s t K k σ

/-- **The analytic hypothesis bundle of the assembly** (RBM2D `GridAssemblyHypN`, `GridGoodN:456`;
RBM1D `GridAssemblyHypPW`, `Gauss/GridAssemblyV2.lean:524`), step-indexed (`Z j`, `Y j` are the step
`j → j+1`), with an abstract kernel class `Cls`, on the path space.  `hexp` is a.e.
(`stoppedDuhamelN`), `hR` is a.e., `hdrift`/`hDcls` are pathwise on `{j < τ}` (from the `GoodSetN`
clauses), `hY` is `YMomentsN`, the sub-Gaussian input is `AzumaSubGN`. -/
structure GridAssemblyHypN {n k : ℕ} (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (Δ : ℝ) (K : ℕ)
    (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
    (A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
    (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ sz → ℝ)
    (c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) : Prop where
  hE : |E| ≤ 2
  hu0 : ∀ i ≤ K, 0 ≤ u i
  hu1 : ∀ i ≤ K, u i < 1
  hΔ0 : 0 ≤ Δ
  hexp : ∀ m ≤ K, ∀ᵐ ω ∂(pathP sz), A m ω =
    Ugen d (sz.L n) (sz.lam n) E σ (u 0) (u m) (A0 ω) +
    ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
      ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)
  hκ0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ κ i m
  hε0 : ∀ i m, i ≤ m → m ≤ K → 0 ≤ εK i m
  hker : ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
    (∀ b, ‖X b‖ ≤ M) → Cls i δ X →
    ∀ a, ‖Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) X a‖ ≤ κ i m * M + εK i m * δ
  hδ0 : 0 ≤ δ0
  hA0cls : ∀ ω, 0 < τ ω → Cls 0 δ0 (A0 ω)
  hdDrift0 : ∀ ω j, j < K → 0 ≤ dDrift j ω
  hδD0 : ∀ ω j, j < K → 0 ≤ δD j ω
  hdrift : ∀ ω j, j < K → j < τ ω → ∀ b, ‖Dr j ω b‖ ≤ dDrift j ω
  hDcls : ∀ ω j, j < K → j < τ ω → Cls (j + 1) (δD j ω) (Dr j ω)
  hc_pos : ∀ m, 1 ≤ m → m ≤ K → ∀ a, 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ)
  hv0 : ∀ j < K, 0 ≤ v j
  hw0 : ∀ j < K, 0 ≤ w j
  hY : YMomentBoundsN sz E σ u τ K Y v w
  hstepErr0 : ∀ j < K, 0 ≤ stepErr j
  hR : ∀ᵐ ω ∂(pathP sz), ∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j

/-- **Pin `AssembledN`, the assembled pathwise bound** (RBM2D `AssembledN`, `GridGoodN:500`; RBM1D
`grid_assembly_stopped_pathwise`, `Gauss/GridAssemblyV2.lean:891`), for `Ugen` on
`Fin k → Zd d L` (label count `(L^d)^k ≤ N^k`, `N = (W L)^d`).  Fixed `k, ε, D, D₁, C_P, C_K` with
`D₁ + 4D + k + 2C_P + 8 ≤ C_K`, then `∀ᶠ n`, uniformly over the grid `K ≤ ⌈N^{C_K}⌉`,
`Δ ≤ N^{-C_K}`, `KΔ ≤ 1`, and all data satisfying the bundle: one event `G`, `P(Gᶜ) ≤ N^{-D₁}`,
on which `0 < τ` gives the bound for every target `m ≤ K` and label `a`:
`‖A_m(a)‖ ≤ κ_{0m}‖A_0‖ + ε_{0m}δ₀ + Δ Σ_{j<m}(κ_{j+1,m} d_j + ε_{j+1,m} δD_j)
  + N^ε (Σ_{j<m} c)^{1/2} + N^{-D} + Σ_{j<m}(1 + (1-u_m)⁻¹)^k stepErr_j`.
The premise `sz.SizeTendsto` is necessary (H26, `W ≡ 1`, `L ≡ 3`): for a bounded size `N` the Azuma
tail `4 exp(-N^{2ε}/4)` is a positive constant while `D₁` is arbitrary. -/
def AssembledN : Prop :=
  sz.SizeTendsto → ∀ (k : ℕ) (ε : ℝ), 0 < ε → ∀ (D D₁ C_P C_K : ℝ), 0 ≤ C_K →
    D₁ + 4 * D + (k : ℝ) + 2 * C_P + 8 ≤ C_K →
    ∀ᶠ n : ℕ in atTop, ∀ (K : ℕ) (E : ℝ) (σ : Fin k → Bool) (u : ℕ → ℝ) (τ : PathΩ sz → ℕ)
      (Δ : ℝ) (Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop)
      (A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ)
      (κ εK : ℕ → ℕ → ℝ) (δ0 : ℝ) (dDrift δD : ℕ → PathΩ sz → ℝ)
      (c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0) (v w stepErr : ℕ → ℝ) (P : ℝ),
      1 ≤ K → K ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊ →
      Δ ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) → (K : ℝ) * Δ ≤ 1 →
      0 ≤ P → P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P →
      (∀ j < K, v j ≤ Δ ^ 2 * P) → (∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) →
      (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
      (∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j)) →
      (∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
        SubGaussStopN sz E σ u τ Z m a j (c m a j)) →
      GridAssemblyHypN sz E σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr →
      ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤
            κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) +
            εK 0 m * δ0 +
            Δ * ∑ j ∈ Finset.range m,
              (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) +
            ((sz.size n : ℕ) : ℝ) ^ ε * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) +
            ((sz.size n : ℕ) : ℝ) ^ (-D) +
            ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j

end Pins

/-! ## 2. The fourth-moment bound for real martingale differences (the `p = 2` Burkholder bound) -/

section Moment4

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ'}

private lemma gridAsm_abs_le_B1 (a b : ℝ) : |a| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (a - 1 / 2), sq_nonneg (a + 1 / 2),
      sq_nonneg (b ^ 2)]

private lemma gridAsm_abs_mul_le_B (a b : ℝ) : |a * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_le]; constructor <;>
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a ^ 2 - 1 / 2),
      sq_nonneg (b ^ 2 - 1 / 2), sq_nonneg (a ^ 2 - b ^ 2)]

private lemma gridAsm_abs_sq_le_B (a b : ℝ) : |a ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (sq_nonneg a)]
  nlinarith [sq_nonneg (a ^ 2 - 1 / 2), sq_nonneg (b ^ 2)]

private lemma gridAsm_abs_cube_mul_le_B (a b : ℝ) :
    |a ^ 3 * b| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  have h1 : |a ^ 3 * b| = a ^ 2 * |a * b| := by
    rw [show a ^ 3 * b = a ^ 2 * (a * b) by ring, abs_mul, abs_of_nonneg (sq_nonneg a)]
  have h2 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  rw [h1]
  have h3 : a ^ 2 * |a * b| ≤ a ^ 2 * ((a ^ 2 + b ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg a)
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg a, sq_nonneg b]

private lemma gridAsm_abs_sq_mul_sq_le_B (a b : ℝ) :
    |a ^ 2 * b ^ 2| ≤ 1 + 2 * (a ^ 4 + b ^ 4) := by
  rw [abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]

private lemma gridAsm_pow4_add_le (a b : ℝ) :
    (a + b) ^ 4 ≤ a ^ 4 + 4 * (a ^ 3 * b) + 8 * (a ^ 2 * b ^ 2) + 3 * b ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg (a - b))]

private lemma gridAsm_pow4_add_le_eight (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a ^ 2 - b ^ 2),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b)), sq_nonneg (a * b),
    mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a - b))]

/-- One step of the fourth-moment recursion: for an `ℱ m`-measurable `S` and a martingale
difference `d` with `E[d | ℱ m] = 0`, `E[d² | ℱ m] ≤ v`:
`E(S+d)² ≤ E S² + v` and `E(S+d)⁴ ≤ E S⁴ + 8 v E S² + 3 E d⁴` (RBM1D `moment4_step`,
`GridAssemblyV2.lean:103`). -/
private lemma gridAsm_moment4_step (m : ℕ) {S d : Ω' → ℝ} (hS : StronglyMeasurable[ℱ m] S)
    (hd : StronglyMeasurable d) (hS4 : Integrable (fun ω => S ω ^ 4) μ)
    (hd4 : Integrable (fun ω => d ω ^ 4) μ) (hmean : μ[d | ℱ m] =ᵐ[μ] 0) {v : ℝ}
    (hcond : μ[fun ω => d ω ^ 2 | ℱ m] ≤ᵐ[μ] fun _ => v) :
    Integrable (fun ω => (S ω + d ω) ^ 4) μ
      ∧ ∫ ω, (S ω + d ω) ^ 2 ∂μ ≤ ∫ ω, S ω ^ 2 ∂μ + v
      ∧ ∫ ω, (S ω + d ω) ^ 4 ∂μ
          ≤ ∫ ω, S ω ^ 4 ∂μ + 8 * v * ∫ ω, S ω ^ 2 ∂μ + 3 * ∫ ω, d ω ^ 4 ∂μ := by
  have hS0 : StronglyMeasurable S := hS.mono (ℱ.le m)
  set B : Ω' → ℝ := fun ω => 1 + 2 * (S ω ^ 4 + d ω ^ 4) with hBdef
  have hB : Integrable B μ := (integrable_const 1).add ((hS4.add hd4).const_mul 2)
  have hint : ∀ f : Ω' → ℝ, StronglyMeasurable f → (∀ ω, |f ω| ≤ B ω) → Integrable f μ :=
    fun f hf hfB => hB.mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB ω)
  have hid : Integrable d μ := hint d hd fun ω => by
    have := gridAsm_abs_le_B1 (d ω) (S ω); simp only [hBdef]; linarith
  have hid2 : Integrable (fun ω => d ω ^ 2) μ :=
    hint _ (hd.pow 2) fun ω => by
      have := gridAsm_abs_sq_le_B (d ω) (S ω); simp only [hBdef]; linarith
  have hiS2 : Integrable (fun ω => S ω ^ 2) μ :=
    hint _ (hS0.pow 2) fun ω => gridAsm_abs_sq_le_B (S ω) (d ω)
  have hiSd : Integrable (fun ω => S ω * d ω) μ :=
    hint _ (hS0.mul hd) fun ω => gridAsm_abs_mul_le_B (S ω) (d ω)
  have hiS3d : Integrable (fun ω => S ω ^ 3 * d ω) μ :=
    hint _ ((hS0.pow 3).mul hd) fun ω => gridAsm_abs_cube_mul_le_B (S ω) (d ω)
  have hiS2d2 : Integrable (fun ω => S ω ^ 2 * d ω ^ 2) μ :=
    hint _ ((hS0.pow 2).mul (hd.pow 2)) fun ω => gridAsm_abs_sq_mul_sq_le_B (S ω) (d ω)
  have hiSum4 : Integrable (fun ω => (S ω + d ω) ^ 4) μ := by
    refine ((hS4.add hd4).const_mul 8).mono' ((hS0.add hd).pow 4).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact gridAsm_pow4_add_le_eight (S ω) (d ω)
  -- `E[S^p d] = 0` for an `ℱ m`-measurable `S^p`
  have hzero : ∀ p : ℕ, Integrable (fun ω => S ω ^ p * d ω) μ →
      ∫ ω, S ω ^ p * d ω ∂μ = 0 := by
    intro p hp
    have h1 : μ[(fun ω => S ω ^ p) * d | ℱ m] =ᵐ[μ] (fun ω => S ω ^ p) * μ[d | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow p) hp hid
    calc ∫ ω, S ω ^ p * d ω ∂μ = ∫ ω, (μ[(fun ω => S ω ^ p) * d | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ p) * μ[d | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ = ∫ _ω, (0 : ℝ) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hmean] with ω hω
          simp [hω]
      _ = 0 := integral_zero _ _
  have hSd0 : ∫ ω, S ω * d ω ∂μ = 0 := by
    have := hzero 1 (by simpa using hiSd)
    simpa using this
  have hS3d0 : ∫ ω, S ω ^ 3 * d ω ∂μ = 0 := hzero 3 hiS3d
  -- `E[d²] ≤ v`
  have hd2v : ∫ ω, d ω ^ 2 ∂μ ≤ v := by
    calc ∫ ω, d ω ^ 2 ∂μ = ∫ ω, (μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ ≤ ∫ _ω, v ∂μ := integral_mono_ae integrable_condExp (integrable_const v) hcond
      _ = v := by simp
  -- `E[S² d²] ≤ v E[S²]`
  have hS2d2 : ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ ≤ v * ∫ ω, S ω ^ 2 ∂μ := by
    have h1 : μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]
        =ᵐ[μ] (fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m] :=
      condExp_mul_of_stronglyMeasurable_left (hS.pow 2) hiS2d2 hid2
    have hi1 : Integrable ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) μ :=
      (integrable_condExp (μ := μ) (m := ℱ m)
        (f := (fun ω => S ω ^ 2) * (fun ω => d ω ^ 2))).congr h1
    calc ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
        = ∫ ω, (μ[(fun ω => S ω ^ 2) * (fun ω => d ω ^ 2) | ℱ m]) ω ∂μ :=
          (integral_condExp (ℱ.le m)).symm
      _ = ∫ ω, ((fun ω => S ω ^ 2) * μ[fun ω => d ω ^ 2 | ℱ m]) ω ∂μ := integral_congr_ae h1
      _ ≤ ∫ ω, v * S ω ^ 2 ∂μ := by
          refine integral_mono_ae hi1 (hiS2.const_mul v) ?_
          filter_upwards [hcond] with ω hω
          simp only [Pi.mul_apply]
          nlinarith [sq_nonneg (S ω)]
      _ = v * ∫ ω, S ω ^ 2 ∂μ := integral_const_mul v _
  refine ⟨hiSum4, ?_, ?_⟩
  · have heq : (fun ω => (S ω + d ω) ^ 2)
        = fun ω => S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2 := by funext ω; ring
    rw [heq, integral_add (f := fun ω => S ω ^ 2 + 2 * (S ω * d ω))
        (hiS2.add (hiSd.const_mul 2)) hid2,
      integral_add (f := fun ω => S ω ^ 2) hiS2 (hiSd.const_mul 2), integral_const_mul, hSd0]
    linarith
  · calc ∫ ω, (S ω + d ω) ^ 4 ∂μ
        ≤ ∫ ω, (S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2) + 3 * d ω ^ 4) ∂μ :=
          integral_mono hiSum4
            (((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)).add (hd4.const_mul 3))
            fun ω => gridAsm_pow4_add_le (S ω) (d ω)
      _ = ∫ ω, S ω ^ 4 ∂μ + 4 * ∫ ω, S ω ^ 3 * d ω ∂μ + 8 * ∫ ω, S ω ^ 2 * d ω ^ 2 ∂μ
            + 3 * ∫ ω, d ω ^ 4 ∂μ := by
          rw [integral_add
              (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω) + 8 * (S ω ^ 2 * d ω ^ 2))
              ((hS4.add (hiS3d.const_mul 4)).add (hiS2d2.const_mul 8)) (hd4.const_mul 3),
            integral_add (f := fun ω => S ω ^ 4 + 4 * (S ω ^ 3 * d ω))
              (hS4.add (hiS3d.const_mul 4)) (hiS2d2.const_mul 8),
            integral_add (f := fun ω => S ω ^ 4) hS4 (hiS3d.const_mul 4), integral_const_mul,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by rw [hS3d0]; nlinarith [hS2d2]

/-- **The `p = 2` Burkholder bound for real martingale differences** (elementary; port of RBM1D
`mart_moment4`, `GridAssemblyV2.lean:204`).  For `d_j` `ℱ (j+1)`-measurable with
`E[d_j | ℱ j] = 0`, `d_j⁴` integrable, `E[d_j² | ℱ j] ≤ v_j` a.s. (`v_j ≥ 0`) and `E d_j⁴ ≤ w_j`,
the partial sum `S_m = Σ_{j<m} d_j` satisfies `E S_m² ≤ Σ_{j<m} v_j` and
`E S_m⁴ ≤ 8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j`. -/
private theorem gridAsm_mart_moment4 (d : ℕ → Ω' → ℝ) (v w : ℕ → ℝ) (m : ℕ)
    (hd : ∀ j, StronglyMeasurable[ℱ (j + 1)] (d j))
    (hmean : ∀ j < m, μ[d j | ℱ j] =ᵐ[μ] 0)
    (hint : ∀ j < m, Integrable (fun ω => d j ω ^ 4) μ)
    (hcond : ∀ j < m, μ[fun ω => d j ω ^ 2 | ℱ j] ≤ᵐ[μ] fun _ => v j)
    (hv0 : ∀ j < m, 0 ≤ v j)
    (hw : ∀ j < m, ∫ ω, d j ω ^ 4 ∂μ ≤ w j) :
    Integrable (fun ω => (∑ j ∈ Finset.range m, d j ω) ^ 4) μ
      ∧ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ ≤ ∑ j ∈ Finset.range m, v j
      ∧ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 4 ∂μ
          ≤ 8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨hI, h2, h4⟩ := ih (fun j hj => hmean j (by omega)) (fun j hj => hint j (by omega))
      (fun j hj => hcond j (by omega)) (fun j hj => hv0 j (by omega)) (fun j hj => hw j (by omega))
    have hSm : StronglyMeasurable[ℱ m] (fun ω => ∑ j ∈ Finset.range m, d j ω) := by
      refine Finset.stronglyMeasurable_fun_sum (Finset.range m)
        (fun j hj => (hd j).mono (ℱ.mono ?_))
      have := Finset.mem_range.mp hj; omega
    have hdm : StronglyMeasurable (d m) := (hd m).mono (ℱ.le (m + 1))
    obtain ⟨hI', h2', h4'⟩ := gridAsm_moment4_step (μ := μ) m hSm hdm hI
      (hint m (by omega)) (hmean m (by omega)) (hcond m (by omega))
    have hsum : ∀ ω, ∑ j ∈ Finset.range (m + 1), d j ω
        = (∑ j ∈ Finset.range m, d j ω) + d m ω := fun ω => Finset.sum_range_succ _ _
    simp only [hsum]
    have hV0 : 0 ≤ ∑ j ∈ Finset.range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hvm := hv0 m (by omega)
    have hwm := hw m (by omega)
    have hS2nn : 0 ≤ ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ :=
      integral_nonneg fun ω => sq_nonneg _
    refine ⟨hI', ?_, ?_⟩
    · rw [Finset.sum_range_succ]; linarith
    · rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have h8 : 8 * v m * ∫ ω, (∑ j ∈ Finset.range m, d j ω) ^ 2 ∂μ
          ≤ 8 * v m * ∑ j ∈ Finset.range m, v j :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith [mul_nonneg hvm hV0, sq_nonneg (v m)]

end Moment4

/-! ## 3. The complex Azuma step and the stopped `Ugen`-propagated sums -/

section AzumaStep

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

/-- Prepend a dummy zero term (RBM1D `prependZero`, `GridDuhamelTail.lean:54`). -/
private def gridAsm_prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

private theorem gridAsm_sum_range_succ_prependZero {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), gridAsm_prependZero f i = ∑ j ∈ Finset.range m, f j := by
  rw [Finset.sum_range_succ' (gridAsm_prependZero f) m]
  simp [gridAsm_prependZero]

/-- The complex Azuma tail for `Σ_{j<m} X_j` when `X_j` is `ℱ (j+1)`-strongly measurable and its
real and imaginary parts are conditionally sub-Gaussian given `ℱ j` with proxy `c j` (the process
`0, X_0, …, X_{m-1}, 0, …` fed to `azuma_complex` with horizon `m + 1`; the merged private
`GridDuhamelN_azuma_step`, `GridDuhamelN.lean:447`, re-proved here because it is private there). -/
private theorem gridAsm_azuma_step {X : ℕ → Ω' → ℂ} {m : ℕ}
    (hX : ∀ j < m, StronglyMeasurable[ℱ (j + 1)] (X j)) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := fun i => if i ≤ m then gridAsm_prependZero X i else 0 with hYdef
  set cc : ℕ → ℝ≥0 := gridAsm_prependZero c with hccdef
  have hYsucc : ∀ j, j + 1 ≤ m → Y (j + 1) = X j := by
    intro j hj
    simp only [hYdef, hj, ↓reduceIte]
    rfl
  have hYzero : Y 0 = 0 := by
    simp [hYdef, gridAsm_prependZero]
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).re)
        rw [hYsucc j hj]
        exact Complex.continuous_re.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).im)
        rw [hYsucc j hj]
        exact Complex.continuous_im.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYzero, hccdef, gridAsm_prependZero]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYzero, hccdef, gridAsm_prependZero]
  have hCR : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).1
  have hCI : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).2
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (m + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ Finset.range m, X j ω = ∑ i ∈ Finset.range (m + 1), Y i ω := by
    intro ω
    have h3 := gridAsm_sum_range_succ_prependZero (fun j => X j ω) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hYdef, him, ↓reduceIte]
    cases i <;> rfl
  have hsumeq : ∑ i ∈ Finset.range (m + 1), (cc i : ℝ) = ∑ j ∈ Finset.range m, (c j : ℝ) := by
    have h3 := gridAsm_sum_range_succ_prependZero (fun j => (c j : ℝ)) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases i <;> rfl
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖}
      = {ω | x ≤ ‖∑ i ∈ Finset.range (m + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

end AzumaStep

/-! ## 4. The kernel `Ugen`: strong measurability, sums of four, and the coarse row bound -/

section UgenBounds

/-- `A ↦ (𝒰_{v,w,σ} A)_a` is continuous, so it preserves strong measurability. -/
private theorem gridAsm_stronglyMeasurable_Ugen_apply {Ω' : Type*} {m : MeasurableSpace Ω'}
    (d L : ℕ) [NeZero L] (g E' : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    {W : Ω' → (Fin k → Zd d L) → ℂ} (hW : StronglyMeasurable[m] W) (a : Fin k → Zd d L) :
    StronglyMeasurable[m] (fun ω => Ugen d L g E' σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Zd d L) → ℂ => Ugen d L g E' σ v w A a) := by
    unfold Ugen UN
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

/-- `𝒰` of the four-term increment `Δ D + Z + Y + R`, at one label. -/
private theorem gridAsm_Ugen_four (d L : ℕ) [NeZero L] (g E : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (v w : ℝ) (Δ : ℂ) (D Z Y R : (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) :
    Ugen d L g E σ v w (Δ • D + Z + Y + R) a =
      Δ * Ugen d L g E σ v w D a + Ugen d L g E σ v w Z a + Ugen d L g E σ v w Y a
        + Ugen d L g E σ v w R a := by
  unfold Ugen UN
  set κ : (Fin k → Zd d L) → ℂ := fun b =>
    ∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i) with hκ
  have hterm : ∀ b : Fin k → Zd d L, κ b * ((Δ • D + Z + Y + R) b) =
      Δ * (κ b * D b) + κ b * Z b + κ b * Y b + κ b * R b := by
    intro b
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

open scoped Matrix.Norms.Operator in
/-- The `ℓ^∞` operator norm of the one-slot kernel: `‖uKer μ v w‖ ≤ 1 + (1 - w)⁻¹` for
`0 ≤ v, w < 1`, `‖μ‖ = 1`; no order between `v` and `w` (the merged `norm_uKer_le` needs
`v ≤ w`; here `|w - v| ≤ 1` replaces `w - v`). -/
private theorem gridAsm_norm_uKer_le {d L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {μ : ℂ}
    (hμ : ‖μ‖ = 1) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    ‖uKer d L g μ v w‖ ≤ 1 + (1 - w)⁻¹ := by
  have hξ : ‖(w : ℂ) * μ‖ < 1 := norm_t_mul_lt_one hw0 hw1 hμ
  rw [uKer_eq_one_add hL hξ]
  have hc : ‖((w : ℂ) - v) * μ‖ ≤ 1 := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_le]
    constructor <;> linarith
  have hΘ := norm_Theta_le (d := d) (g := g) hL hw0 hw1 hμ
  calc ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)
        + (((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
      ≤ ‖(1 : Matrix (Zd d L) (Zd d L) ℂ)‖
        + ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖ := norm_add_le _ _
    _ ≤ 1 + 1 * (1 - w)⁻¹ := by
        rw [norm_one]
        refine add_le_add le_rfl ?_
        calc ‖(((w : ℂ) - v) * μ) • (SB d L g * Theta d L g ((w : ℂ) * μ))‖
            ≤ ‖((w : ℂ) - v) * μ‖ * (‖SB d L g‖ * ‖Theta d L g ((w : ℂ) * μ)‖) :=
              (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _)
                (norm_nonneg _))
          _ ≤ 1 * (1 * (1 - w)⁻¹) := by
              rw [norm_SB d L g hL]
              exact mul_le_mul_of_nonneg' hc (by rw [one_mul, one_mul]; exact hΘ) (by positivity) zero_le_one
          _ = 1 * (1 - w)⁻¹ := by ring
    _ = 1 + (1 - w)⁻¹ := by rw [one_mul]

/-- **The coarse row-sum kernel bound of `Ugen`** (derived; port of RBM1D `norm_Uker_coarse`,
`GridAssemblyV2.lean:583`, and of the proof of the merged `norm_UN_apply_le`): for `|E| ≤ 2`,
`3 ≤ L`, `0 ≤ v, w < 1`, `‖(𝒰_{v,w,σ} X)_a‖ ≤ (1 + (1 - w)⁻¹)^k ‖X‖_max`. -/
private theorem gridAsm_norm_Ugen_coarse (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ}
    (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) {X : (Fin k → Zd d L) → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hX : ∀ b, ‖X b‖ ≤ M) (a : Fin k → Zd d L) :
    ‖Ugen d L g E σ v w X a‖ ≤ (1 + (1 - w)⁻¹) ^ k * M := by
  set K : Fin k → Matrix (Zd d L) (Zd d L) ℂ := fun i =>
    uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w with hK
  have hrow : ∀ i, ∑ c, ‖K i (a i) c‖ ≤ 1 + (1 - w)⁻¹ := fun i =>
    (sum_norm_row_le (K i) (a i)).trans
      (gridAsm_norm_uKer_le hL (norm_cycProd (fun i => norm_mSigma hE (σ i)) i) hv0 hv1 hw0 hw1)
  calc ‖Ugen d L g E σ v w X a‖
      ≤ ∑ b : Fin k → Zd d L, ‖(∏ i, K i (a i) (b i)) * X b‖ := norm_sum_le _ _
    _ ≤ ∑ b : Fin k → Zd d L, (∏ i, ‖K i (a i) (b i)‖) * M := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_left (hX b) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = (∏ i, ∑ c, ‖K i (a i) c‖) * M := by
        rw [← Finset.sum_mul, Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ ≤ (1 + (1 - w)⁻¹) ^ k * M := by
        refine mul_le_mul_of_nonneg_right ?_ hM
        calc ∏ i, ∑ c, ‖K i (a i) c‖ ≤ ∏ _i : Fin k, (1 + (1 - w)⁻¹) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun c _ => norm_nonneg _)
                fun i _ => hrow i
          _ = (1 + (1 - w)⁻¹) ^ k := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end UgenBounds

/-! ## 5. Measurability of the first-chaos part `ZvecN` and of the remainder `YvecN`

RBM2D proves both unconditionally in `GridGoodN` section 5 (`stronglyMeasurable_ZvecN`,
`stronglyMeasurable_YvecN`, `GridGoodN:981-996`); the merged `RBM3D/Induction/GridGoodN.lean`
(T2146) does not have them, so they are ported here (the Carathéodory argument of RBM2D
`GridGoodN:725-931`, with the merged `loopL`, `Gres`, `walk_measurable_loopL`), public with the
file prefix: `gridAsm_stronglyMeasurable_ZvecN`, `gridAsm_stronglyMeasurable_YvecN`.  The pin
`AssembledN` asks `∀ j, StronglyMeasurable[filt sz (j+1)] (Z j)`, so a consumer feeding
`Z = ZvecN` needs the unconditional form (also for `j ≥ K n`, where the spectral time may be `1`). -/

section DerivMeasurability

open scoped Topology

/-- A function on `ℝ` that is continuous on a punctured neighbourhood of `0` and whose limit of
difference quotients along the rationals exists has that limit as the limit along the reals (the
rationals are dense and the quotient is continuous near `0`, `0` excluded). -/
private theorem gridAsm_tendsto_of_rat {g : ℝ → ℂ} {c : ℂ}
    (hg : ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt g y)
    (h : Tendsto (fun r : ℚ => g (r : ℝ)) (𝓝[≠] (0 : ℚ)) (𝓝 c)) :
    Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hg
  obtain ⟨δ₀, hδ₀, hg⟩ := hg
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := h (ε / 2) (half_pos hε)
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun {y} hy0 hy => ?_⟩
  have hy0' : y ≠ 0 := hy0
  have hyabs : |y| < min δ₀ δ₁ := by simpa [Real.dist_eq] using hy
  have hcy : ContinuousAt g y := hg (by
    rw [Real.dist_eq, sub_zero]; exact hyabs.trans_le (min_le_left _ _)) hy0'
  obtain ⟨ρ, hρ, hρy⟩ := Metric.continuousAt_iff.1 hcy (ε / 2) (half_pos hε)
  have hypos : 0 < |y| := abs_pos.2 hy0'
  set ρ' := min ρ (min |y| (min δ₀ δ₁ - |y|)) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (lt_min hypos (sub_pos.2 hyabs))
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show y - ρ' < y + ρ' by linarith)
  have hrabs : |(r : ℝ) - y| < ρ' := by
    rw [abs_lt]; constructor <;> linarith
  have hr_ne : (r : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hrabs
    exact absurd (hrabs.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (lt_irrefl _)
  have hr_small : |(r : ℝ)| < min δ₀ δ₁ := by
    have h3 : |(r : ℝ)| ≤ |y| + |(r : ℝ) - y| := by
      calc |(r : ℝ)| = |y + ((r : ℝ) - y)| := by ring_nf
        _ ≤ |y| + |(r : ℝ) - y| := abs_add_le _ _
    have h4 : |(r : ℝ) - y| < min δ₀ δ₁ - |y| :=
      hrabs.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hcr : dist (g (r : ℝ)) c < ε / 2 := by
    refine h1 (x := r) (by simpa using hr_ne) ?_
    rw [Rat.dist_eq]; simp only [Rat.cast_zero, sub_zero]
    exact hr_small.trans_le (min_le_right _ _)
  have hgy : dist (g (r : ℝ)) (g y) < ε / 2 :=
    hρy (by rw [Real.dist_eq]; exact hrabs.trans_le (min_le_left _ _))
  calc dist (g y) c ≤ dist (g y) (g (r : ℝ)) + dist (g (r : ℝ)) c := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by rw [dist_comm]; exact add_lt_add hgy hcr
    _ = ε := by ring

/-- **Carathéodory-type measurability of the derivative at `0`**: if `a ↦ f a y` is measurable for
each `y` and each `f a` is continuous on a punctured neighbourhood of `0`, then
`a ↦ deriv (f a) 0` is measurable (no continuity in `a`; the derivative is `0` where `f a` is not
differentiable at `0`). -/
private theorem gridAsm_measurable_deriv_zero {α : Type*} [MeasurableSpace α]
    (f : α → ℝ → ℂ) (hf : ∀ y, Measurable fun a => f a y)
    (hreg : ∀ a, ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (f a) y) :
    Measurable fun a => deriv (f a) 0 := by
  classical
  let q : α → ℚ → ℂ := fun a r => slope (f a) 0 (r : ℝ)
  have hq : ∀ r : ℚ, Measurable fun a => q a r := fun r => by
    simp only [q, slope, vsub_eq_sub, sub_zero]
    exact ((hf r).sub (hf 0)).const_smul _
  have hqs : ∀ r : ℚ, StronglyMeasurable fun a => q a r := fun r => (hq r).stronglyMeasurable
  let T : Set α := {a | ∃ c, Tendsto (fun r : ℚ => q a r) (𝓝[≠] (0 : ℚ)) (𝓝 c)}
  have hT : MeasurableSet T :=
    StronglyMeasurable.measurableSet_exists_tendsto (l := 𝓝[≠] (0 : ℚ)) (f := fun r a => q a r) hqs
  have hΨ : StronglyMeasurable fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r) :=
    StronglyMeasurable.limUnder (l := 𝓝[≠] (0 : ℚ)) (f := fun r a => q a r) hqs
  have hcast : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[≠] (0 : ℚ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := (Rat.continuous_coe_real.tendsto (0 : ℚ)).mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℚ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact Rat.cast_ne_zero.2 hr
  have hslope_cont : ∀ a, ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (slope (f a) 0) y := by
    intro a
    filter_upwards [hreg a, self_mem_nhdsWithin] with y hy hy0
    have hy0' : y ≠ 0 := hy0
    have hs : slope (f a) 0 = fun x => x⁻¹ • (f a x - f a 0) := by
      funext x; simp [slope]
    rw [hs]
    exact (continuousAt_inv₀ hy0').smul (hy.sub continuousAt_const)
  have hderiv : ∀ a, deriv (f a) 0 =
      T.indicator (fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r)) a := by
    intro a
    by_cases haT : a ∈ T
    · obtain ⟨c, hc⟩ := haT
      have hreal : Tendsto (slope (f a) 0) (𝓝[≠] (0 : ℝ)) (𝓝 c) :=
        gridAsm_tendsto_of_rat (hslope_cont a) hc
      have hd : HasDerivAt (f a) c 0 := hasDerivAt_iff_tendsto_slope.2 hreal
      rw [Set.indicator_of_mem (show a ∈ T from ⟨c, hc⟩), hd.deriv]
      exact hc.limUnder_eq.symm
    · rw [Set.indicator_of_notMem haT]
      refine deriv_zero_of_not_differentiableAt fun hdiff => haT ?_
      exact ⟨_, (hasDerivAt_iff_tendsto_slope.1 hdiff.hasDerivAt).comp hcast⟩
  have : (fun a => deriv (f a) 0) =
      T.indicator (fun a => limUnder (𝓝[≠] (0 : ℚ)) (fun r => q a r)) := funext hderiv
  rw [this]
  exact hΨ.measurable.indicator hT

/-- The determinant along a line `y ↦ A + y B` (`y` real) is analytic in `y`. -/
private theorem gridAsm_det_line_analytic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (y₀ : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => (A + (y : ℂ) • B).det) y₀ := by
  have hent : ∀ i j : ι, AnalyticAt ℝ (fun y : ℝ => (A + (y : ℂ) • B) i j) y₀ := by
    intro i j
    have h1 : AnalyticAt ℝ (fun y : ℝ => (y : ℂ)) y₀ := Complex.ofRealCLM.analyticAt y₀
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact analyticAt_const.add (h1.mul analyticAt_const)
  simp only [Matrix.det_apply]
  refine Finset.analyticAt_fun_sum _ fun σ _ => ?_
  have hprod : AnalyticAt ℝ (fun y : ℝ => ∏ i, (A + (y : ℂ) • B) (σ i) i) y₀ :=
    Finset.analyticAt_fun_prod _ fun i _ => hent (σ i) i
  simp only [Units.smul_def, zsmul_eq_mul]
  exact analyticAt_const.mul hprod

/-- **Regularity of the matrix inverse along a line** (junk value `0` at singular matrices
included): `y ↦ (A + y B)⁻¹` is continuous on a punctured neighbourhood of `0`.  Either the
determinant vanishes identically near `0` (then the inverse is `0` there) or it has an isolated
zero at `0`. -/
private theorem gridAsm_inv_line_regular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    ∀ᶠ y in 𝓝[≠] (0 : ℝ), ContinuousAt (fun y : ℝ => (A + (y : ℂ) • B)⁻¹) y := by
  have hcont : Continuous (fun y : ℝ => A + (y : ℂ) • B) :=
    continuous_const.add ((Complex.continuous_ofReal).smul continuous_const)
  rcases (gridAsm_det_line_analytic A B 0).eventually_eq_zero_or_eventually_ne_zero with h0 | h1
  · have h0' : ∀ᶠ y : ℝ in 𝓝 (0 : ℝ), ∀ᶠ y' : ℝ in 𝓝 y, (A + (y' : ℂ) • B).det = 0 :=
      h0.eventually_nhds
    filter_upwards [h0'.filter_mono nhdsWithin_le_nhds] with y hy
    have hz : (fun y' : ℝ => (A + (y' : ℂ) • B)⁻¹) =ᶠ[𝓝 y] fun _ => (0 : Matrix ι ι ℂ) := by
      filter_upwards [hy] with y' hy'
      exact Matrix.nonsing_inv_apply_not_isUnit _ (by rw [hy']; exact not_isUnit_zero)
    exact continuousAt_const.congr hz.symm
  · filter_upwards [h1] with y hy
    have hinv : ContinuousAt Ring.inverse (A + (y : ℂ) • B).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hy
    exact ContinuousAt.comp (f := fun y : ℝ => A + (y : ℂ) • B) (x := y)
      (continuousAt_matrix_inv _ hinv) hcont.continuousAt

private theorem gridAsm_foldr_continuousAt {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (G : Bool → ℝ → Matrix ι ι ℂ) (Ea : α → Matrix ι ι ℂ) (y : ℝ)
    (hG : ∀ b, ContinuousAt (G b) y) (l : List (Bool × α)) :
    ContinuousAt (fun y => l.foldr (fun p Acc => G p.1 y * Ea p.2 * Acc) (1 : Matrix ι ι ℂ)) y := by
  induction l with
  | nil => exact continuousAt_const
  | cons p l ih =>
      simp only [List.foldr_cons]
      exact ((hG p.1).mul continuousAt_const).mul ih


/-- **Regularity of a loop observable along a line**: for every spectral parameter `z` (real or
not), loop `I` and matrices `M, X` (Hermitian or not), `y ↦ 𝓛_{z,I}(M + yX)` is continuous on a
punctured neighbourhood of `0` (RBM2D `GridGoodN_gloop_line_regular`, `GridGoodN:881`, with `gloop`
the merged `loopL`, `Gsig` the merged `Gres`, `Z2 L` the merged `Zd d L`). -/
private theorem gridAsm_loopL_line_regular (d L W : ℕ) [NeZero L] [NeZero W] (z : ℂ)
    (I : LoopIdx (Zd d L)) (M X : Matrix (Idx d L W) (Idx d L W) ℂ) :
    ∀ᶠ y in 𝓝[≠] (0 : ℝ),
      ContinuousAt (fun y : ℝ => loopL d L W (blockMat d L W (M + (y : ℂ) • X)) z I) y := by
  have hb : ∀ y : ℝ, blockMat d L W (M + (y : ℂ) • X)
      = blockMat d L W M + (y : ℂ) • blockMat d L W X := by
    intro y
    simp [blockMat, Matrix.submatrix_add, Matrix.submatrix_smul]
  have hinv : ∀ w : ℂ, ∀ᶠ y in 𝓝[≠] (0 : ℝ),
      ContinuousAt (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) w true) y := by
    intro w
    have h := gridAsm_inv_line_regular (blockMat d L W M - w • (1 : Matrix (Vtx d L W)
      (Vtx d L W) ℂ)) (blockMat d L W X)
    have hfun : (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) w true)
        = fun y : ℝ => ((blockMat d L W M - w • (1 : Matrix (Vtx d L W)
        (Vtx d L W) ℂ)) + (y : ℂ) • blockMat d L W X)⁻¹ := by
      funext y
      rw [hb y, Matrix.nonsing_inv_eq_ringInverse]
      simp only [Gres, ite_true]
      congr 1
      abel
    rw [hfun]
    exact h
  filter_upwards [hinv z, hinv ((starRingEnd ℂ) z)] with y hz hzc
  have hG : ∀ b : Bool, ContinuousAt
      (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) z b) y := by
    intro b
    cases b
    · have hc : (fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) z false)
          = fun y : ℝ => Gres (blockMat d L W (M + (y : ℂ) • X)) ((starRingEnd ℂ) z) true := by
        funext y; simp [Gres]
      rw [hc]; exact hzc
    · exact hz
  have hfold := gridAsm_foldr_continuousAt
    (fun (b : Bool) (y : ℝ) => Gres (blockMat d L W (M + (y : ℂ) • X)) z b)
    (fun a : Zd d L => Eblk d L W a) y hG (I.σ.zip I.a)
  exact (continuous_id.matrix_trace).continuousAt.comp hfold

/-- `(M, X) ↦ loopDerivN d L W E u M X σ b` is measurable on all pairs of matrices. -/
private theorem gridAsm_measurable_loopDerivN (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d L) :
    Measurable fun p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ =>
      loopDerivN d L W E u p.1 p.2 σ b := by
  unfold loopDerivN
  refine gridAsm_measurable_deriv_zero
    (fun (p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ) (y : ℝ) =>
      loopL d L W (blockMat d L W (p.1 + (y : ℂ) • p.2)) (zt E u) (loopOf σ b)) (fun y => ?_)
    (fun p => gridAsm_loopL_line_regular d L W (zt E u) (loopOf σ b) p.1 p.2)
  have hlin : Measurable fun p : Matrix (Idx d L W) (Idx d L W) ℂ × Matrix (Idx d L W) (Idx d L W) ℂ =>
      p.1 + (y : ℂ) • p.2 :=
    Measurable.of_eval_matrix _ fun i j => by
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact measurable_fst.eval_matrix.add (measurable_snd.eval_matrix.const_mul _)
  exact ((walk_measurable_loopL d L W (zt E u) (loopOf σ b)).comp
    (walk_measurable_blockMat d L W)).comp hlin

end DerivMeasurability


section ZYMeasurability

variable {d : ℕ} (sz : Sizes d)

/-- The draw `ω l` is `filt sz k`-measurable for `l ≤ k` (as in `pathH_adapted`, `Walk.lean`). -/
private theorem gridAsm_measurable_coord {k l : ℕ} (hl : l ≤ k) :
    Measurable[filt sz k] (fun ω : PathΩ sz => ω l) := by
  have : (fun ω : PathΩ sz => ω l)
      = (fun g : Set.Iic k → Sizes.SeqΩ sz => g ⟨l, hl⟩)
        ∘ (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k) := rfl
  rw [this]
  exact (measurable_pi_apply (⟨l, hl⟩ : Set.Iic k)).comp
    (comap_measurable (Preorder.restrictLe (π := fun _ : ℕ => Sizes.SeqΩ sz) k))

/-- The pair (grid state at step `j`, Gaussian increment `X_{j+1}`) is `filt sz (j+1)`-measurable. -/
private theorem gridAsm_measurable_pair (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
      (pathH sz s t K n j ω, Sizes.seqXmat sz n (ω (j + 1)))) := by
  have hH : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => pathH sz s t K n j ω) :=
    (pathH_measurable_filt sz s t K n j).mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  have hX : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => Sizes.seqXmat sz n (ω (j + 1))) :=
    ((continuous_Xmat d (sz.L n) (sz.W n)).measurable.comp (Sizes.measurable_slice sz n)).comp
      (gridAsm_measurable_coord sz le_rfl)
  exact hH.prodMk hX

/-- The `b`-th component of `ZvecN` is `filt sz (j + 1)`-measurable. -/
private theorem gridAsm_measurable_ZvecN_apply (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => ZvecN sz E s t K n j σ ω b) := by
  have hΨ := gridAsm_measurable_loopDerivN d (sz.L n) (sz.W n) (E n) (gridTime s t K n (j + 1)) σ b
  have hpair := gridAsm_measurable_pair sz s t K n j
  have h := hΨ.comp hpair
  exact h.const_mul _

/-- Every label of `A_j` is `filt sz j`-measurable (the merged private
`GridDuhamelN_measurable_AvecN`, re-proved). -/
private theorem gridAsm_measurable_AvecN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz j] (fun ω => AvecN sz E s t K n j σ ω a) :=
  ((walk_measurable_loopFine d (sz.L n) (sz.W n) (zt (E n) (gridTime s t K n j)) σ a).comp
    (pathH_measurable_filt sz s t K n j)).sub measurable_const

/-- The `b`-th component of `martIncN` is `filt sz (j + 1)`-measurable (`A_{j+1}` minus a
`filt sz j`-conditional expectation). -/
private theorem gridAsm_measurable_martIncN_apply (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    {k : ℕ} (σ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => martIncN sz E s t K n j σ ω b) := by
  have h1 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz => AvecN sz E s t K n (j + 1) σ ω b) :=
    gridAsm_measurable_AvecN sz E s t K n (j + 1) σ b
  have h2 : Measurable[filt sz (j + 1)] (fun ω : PathΩ sz =>
      (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' b | filt sz j] ω) :=
    (stronglyMeasurable_condExp.measurable).mono ((filt sz).mono (Nat.le_succ j)) le_rfl
  exact h1.sub h2

/-- **`ZvecN` is `filt sz (j + 1)`-strongly measurable** (the `hZmeas` input of `AssembledN`), for
every `E s t K n j σ` (no hypothesis); RBM2D `stronglyMeasurable_ZvecN`, `GridGoodN:981`. -/
theorem gridAsm_stronglyMeasurable_ZvecN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => ZvecN sz E s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz (j + 1)) _ _ fun b =>
    gridAsm_measurable_ZvecN_apply sz E s t K n j σ b

/-- **`YvecN = martIncN - ZvecN` is `filt sz (j + 1)`-strongly measurable** (the first field of
`YMomentBoundsN`), for every `E s t K n j σ` (no hypothesis); RBM2D `stronglyMeasurable_YvecN`,
`GridGoodN:990`. -/
theorem gridAsm_stronglyMeasurable_YvecN (E s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (fun ω => YvecN sz E s t K n j σ ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz (j + 1)) _ _ fun b =>
    (gridAsm_measurable_martIncN_apply sz E s t K n j σ b).sub
      (gridAsm_measurable_ZvecN_apply sz E s t K n j σ b)

end ZYMeasurability

/-! ## 6. Target 1: the stopped Azuma bound for the first-chaos part `ZvecN` -/

section StoppedAzuma

variable {d : ℕ} (sz : Sizes d)

/-- The label-weighted Azuma tail for a fixed target `m` and label `a` and an arbitrary
step-indexed increment `Z` (`Z j` is the step `j → j+1`, `ℱ (j+1)`-strongly measurable for
`j < m`): `sum_stopped` rewrites the stopped sum as `Σ_{j<m} 1{j<τ} (𝒰_{u_{j+1},u_m} Z_j)_a` and
`azuma_complex` (via `gridAsm_azuma_step`) gives the tail.  RBM1D
`stopped_duhamel_azuma_tail_fixed` route (`GridDuhamelTail.lean:313`), inside
`grid_assembly_stopped_core_pw`. -/
private theorem gridAsm_azuma_Ugen {n k : ℕ} (E : ℝ) (σ : Fin k → Bool)
    (u : ℕ → ℝ) {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    {Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} (m : ℕ)
    (hZ : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (Z j)) (a : Fin k → Zd d (sz.L n))
    (c : ℕ → ℝ≥0) (hsubG : ∀ j < m, SubGaussStopN sz E σ u τ Z m a j (c j)) {x : ℝ}
    (hx : 0 ≤ x) :
    (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set X : ℕ → PathΩ sz → ℂ := fun j => {ω' | j < τ ω'}.indicator (fun ω' =>
    Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω') a) with hXdef
  have hX : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (X j) := by
    intro j hj
    have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
      ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
    exact (gridAsm_stronglyMeasurable_Ugen_apply d (sz.L n) (sz.lam n) E σ _ _ (hZ j hj) a).indicator hset
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
      (fun i ω' => Ugen d (sz.L n) (sz.lam n) E σ (u i) (u m) (Z (i - 1) ω') a) τ m ω
    simp only [Nat.add_sub_cancel] at h
    rw [h]
  rw [hset]
  exact gridAsm_azuma_step (μ := pathP sz) (ℱ := filt sz) hX hsubG hx

/-- The grid spacing is nonnegative on `s n ≤ t n`. -/
private theorem gridAsm_gridStep_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

/-- The grid times are nonnegative. -/
private theorem gridAsm_gridTime_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hs0 : 0 ≤ s n)
    (hst : s n ≤ t n) (j : ℕ) : 0 ≤ gridTime s t K n j :=
  add_nonneg hs0 (mul_nonneg (Nat.cast_nonneg _) (gridAsm_gridStep_nonneg s t K n hst))

/-- The grid times up to the horizon are at most `t n`. -/
private theorem gridAsm_gridTime_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n)
    (hK : K n ≠ 0) {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j ≤ t n := by
  rw [← gridTime_last s t K n hK]
  unfold gridTime
  have hΔ := gridAsm_gridStep_nonneg s t K n hst
  have : (j : ℝ) ≤ (K n : ℝ) := Nat.cast_le.2 hj
  nlinarith

/-- **Target `stoppedAzumaZN`** (the pin `StoppedAzumaZN` above): the stopped Azuma bound for the
first-chaos part `ZvecN`, real and imaginary parts sub-Gaussian with the common proxy `c j` (input
`SubGaussStopN`).  The measurability input of `azuma_complex` is
`gridAsm_stronglyMeasurable_ZvecN` (unconditional, section 4); the hypotheses `|E n| < 2`,
`0 ≤ s n ≤ t n`, `t n < 1`, `K n ≠ 0`, `m ≤ K n` of the pin are not needed.
Template: the merged `stoppedAzumaN` (`GridDuhamelN.lean:598`) with `ZvecN` in place of `martIncN`.
This is a conditional adapter: the sub-Gaussian hypothesis is an input of the pin
(ST2-34/35 produce it). -/
theorem stoppedAzumaZN (E s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedAzumaZN sz E s t K := by
  intro _hE _hs0 _hst _ht1 _hK n k σ τ hτ m _hmK a c hsubG x hx
  exact gridAsm_azuma_Ugen sz (E n) σ (gridTime s t K n) hτ m
    (fun j _ => gridAsm_stronglyMeasurable_ZvecN sz E s t K n j σ) a c hsubG hx

end StoppedAzuma

/-! ## 7. The probability budget -/

section Budget

/-- `C N^A e^{-c N^{τ₁}} ≤ 1` eventually in the real variable `N`: the Gaussian tail beats every
power (RBM1D `SumZeroDyn.eventually_exp_small`, `Hierarchy/SumZeroDyn.lean:1485`, with a real
variable). -/
private theorem gridAsm_eventually_exp_small (C A c : ℝ) {τ₁ : ℝ} (hc : 0 < c)
    (hτ₁ : 0 < τ₁) :
    ∀ᶠ N : ℝ in atTop, C * N ^ A * Real.exp (-(c * N ^ τ₁)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / τ₁) c hc
  have hg : Tendsto (fun N : ℝ => N ^ τ₁) atTop atTop := tendsto_rpow_atTop hτ₁
  have h2 := h.comp hg
  have hpos : (0 : ℝ) < (|C| + 1)⁻¹ := by positivity
  filter_upwards [h2.eventually (gt_mem_nhds hpos), eventually_gt_atTop (0 : ℝ)] with N hN hN0
  simp only [Function.comp_apply] at hN
  have e : (N ^ τ₁) ^ (A / τ₁) = N ^ A := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  rw [e] at hN
  have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
  have hx : 0 ≤ N ^ A * Real.exp (-(c * N ^ τ₁)) := by positivity
  have hN' : N ^ A * Real.exp (-c * N ^ τ₁) < (|C| + 1)⁻¹ := hN
  rw [neg_mul] at hN'
  calc C * N ^ A * Real.exp (-(c * N ^ τ₁))
      = C * (N ^ A * Real.exp (-(c * N ^ τ₁))) := by ring
    _ ≤ (|C| + 1) * (N ^ A * Real.exp (-(c * N ^ τ₁))) := mul_le_mul_of_nonneg_right hC hx
    _ ≤ (|C| + 1) * (|C| + 1)⁻¹ := mul_le_mul_of_nonneg_left hN'.le (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

/-- **The Azuma budget** (RBM1D `assembly_prob_budget`, `GridAssembly.lean:70`): for every `k`,
`ε > 0`, `D₁` and `C_K ≥ 0`, eventually in the real `N`: `N ≥ 2` and, uniformly over
`K ≤ ⌈N^{C_K}⌉₊` and `0 ≤ Lc ≤ N^k` (`Lc` the number of labels, `(L^d)^k ≤ N^k`),
`4 K Lc exp(-(N^ε)²/4) ≤ N^{-D₁}/2`.  `SizeTendsto` is needed only to make this eventual in `n`. -/
private theorem gridAsm_zBudget (k : ℕ) {ε : ℝ} (hε : 0 < ε) (D₁ C_K : ℝ)
    (hCK : 0 ≤ C_K) :
    ∀ᶠ N : ℝ in atTop, (2 : ℝ) ≤ N ∧ ∀ (K : ℕ) (Lc : ℝ), K ≤ ⌈N ^ C_K⌉₊ → 0 ≤ Lc →
      Lc ≤ N ^ k → 4 * (K : ℝ) * Lc * Real.exp (-(N ^ ε) ^ 2 / 4) ≤ N ^ (-D₁) / 2 := by
  filter_upwards [gridAsm_eventually_exp_small 16 (C_K + k + D₁) (1 / 4) (by norm_num)
    (by linarith : (0 : ℝ) < 2 * ε), eventually_ge_atTop (2 : ℝ)] with N hexp hN2
  have hN0 : (0 : ℝ) < N := by linarith
  refine ⟨hN2, fun K Lc hK hLc0 hLc => ?_⟩
  have hNCK : 1 ≤ N ^ C_K := Real.one_le_rpow (by linarith) hCK
  have hK' : (K : ℝ) ≤ 2 * N ^ C_K := by
    have h1 : (K : ℝ) ≤ (⌈N ^ C_K⌉₊ : ℝ) := by exact_mod_cast hK
    have h2 : (⌈N ^ C_K⌉₊ : ℝ) < N ^ C_K + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hsq : (N ^ ε) ^ 2 = N ^ (2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    ring_nf
  rw [hsq]
  set ex : ℝ := Real.exp (-N ^ (2 * ε) / 4) with hexdef
  have hex_eq : Real.exp (-(1 / 4 * N ^ (2 * ε))) = ex := by
    rw [hexdef]; congr 1; ring
  rw [hex_eq] at hexp
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have hsplit : N ^ (C_K + (k : ℝ) + D₁) = N ^ C_K * N ^ (k : ℕ) * N ^ D₁ := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_natCast]
  have hD : N ^ D₁ * N ^ (-D₁) = 1 := by
    rw [← Real.rpow_add hN0]; simp
  have hr : 0 < N ^ (-D₁) := Real.rpow_pos_of_pos hN0 _
  rw [hsplit] at hexp
  have hmul := mul_le_mul_of_nonneg_right hexp hr.le
  have e1 : 16 * (N ^ C_K * N ^ (k : ℕ) * N ^ D₁) * ex * N ^ (-D₁)
      = 16 * (N ^ C_K * N ^ (k : ℕ) * ex) * (N ^ D₁ * N ^ (-D₁)) := by ring
  rw [e1, hD, mul_one, one_mul] at hmul
  have hKL : 4 * (K : ℝ) * Lc * ex ≤ 4 * (2 * N ^ C_K) * N ^ (k : ℕ) * ex := by
    gcongr
  linarith

/-- The `ΔP`-form of the moment bound (RBM1D `moment4_budget_le`, `GridAssemblyV2.lean:449`):
under `v_j ≤ Δ²P`, `w_j ≤ Δ⁴P²`, `KΔ ≤ 1`, `1 ≤ K`, `P ≥ 0`, `Δ ≥ 0`, the budget
`(K+1)·4(8V²+3W) ≤ 88 Δ P²` (`Δ ≤ 1` follows from `1 ≤ K`, `KΔ ≤ 1`). -/
private theorem gridAsm_moment4_budget_le {K : ℕ} {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hP0 : 0 ≤ P)
    (hKΔ : (K : ℝ) * Δ ≤ 1) (hK1 : 1 ≤ K) {v w : ℕ → ℝ} (hv0 : ∀ j < K, 0 ≤ v j)
    (hw0 : ∀ j < K, 0 ≤ w j) (hv : ∀ j < K, v j ≤ Δ ^ 2 * P)
    (hw : ∀ j < K, w j ≤ Δ ^ 4 * P ^ 2) :
    (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
      ≤ 88 * Δ * P ^ 2 := by
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hΔ1 : Δ ≤ 1 := by nlinarith
  have hV : ∑ j ∈ Finset.range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := by
    have := Finset.sum_le_sum (s := Finset.range K) fun j hj => hv j (Finset.mem_range.mp hj)
    simpa using this
  have hV0 : 0 ≤ ∑ j ∈ Finset.range K, v j :=
    Finset.sum_nonneg fun j hj => hv0 j (Finset.mem_range.mp hj)
  have hW : ∑ j ∈ Finset.range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := by
    have := Finset.sum_le_sum (s := Finset.range K) fun j hj => hw j (Finset.mem_range.mp hj)
    simpa using this
  have hKΔ0 : 0 ≤ (K : ℝ) * Δ := by positivity
  have hV' : ∑ j ∈ Finset.range K, v j ≤ Δ * P := by
    calc ∑ j ∈ Finset.range K, v j ≤ (K : ℝ) * (Δ ^ 2 * P) := hV
      _ = ((K : ℝ) * Δ) * (Δ * P) := by ring
      _ ≤ 1 * (Δ * P) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ * P := one_mul _
  have hV2 : (∑ j ∈ Finset.range K, v j) ^ 2 ≤ (Δ * P) ^ 2 := pow_le_pow_left₀ hV0 hV' 2
  have hW' : ∑ j ∈ Finset.range K, w j ≤ Δ ^ 3 * P ^ 2 := by
    calc ∑ j ∈ Finset.range K, w j ≤ (K : ℝ) * (Δ ^ 4 * P ^ 2) := hW
      _ = ((K : ℝ) * Δ) * (Δ ^ 3 * P ^ 2) := by ring
      _ ≤ 1 * (Δ ^ 3 * P ^ 2) := mul_le_mul_of_nonneg_right hKΔ (by positivity)
      _ = Δ ^ 3 * P ^ 2 := one_mul _
  have hΔ3 : Δ ^ 3 * P ^ 2 ≤ (Δ * P) ^ 2 := by
    have : Δ ^ 3 ≤ Δ ^ 2 := pow_le_pow_of_le_one hΔ0 hΔ1 (by norm_num)
    have h2 : Δ ^ 3 * P ^ 2 ≤ Δ ^ 2 * P ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg P)
    nlinarith [h2]
  have hA : 4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)
      ≤ 44 * (Δ * P) ^ 2 := by
    nlinarith
  have hK2 : (K + 1 : ℝ) ≤ 2 * K := by linarith
  calc (K + 1 : ℝ) * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
      ≤ (2 * K) * (44 * (Δ * P) ^ 2) := by
        have hW0 : 0 ≤ ∑ j ∈ Finset.range K, w j :=
          Finset.sum_nonneg fun j hj => hw0 j (Finset.mem_range.mp hj)
        refine mul_le_mul hK2 hA (by positivity) (by positivity)
    _ = 88 * ((K : ℝ) * Δ) * Δ * P ^ 2 := by ring
    _ ≤ 88 * 1 * Δ * P ^ 2 := by
        have : 0 ≤ Δ * P ^ 2 := by positivity
        nlinarith
    _ = 88 * Δ * P ^ 2 := by ring

/-- **The fourth-moment `Y` budget** (deterministic; RBM1D `Ytail_budget`,
`GridAssemblyV2.lean:826`, with the label count `Lc ≤ N^k` in place of `L^n ≤ N^{nC_L}`): for
`N ≥ 2`, `0 ≤ Lc ≤ N^k`, `0 ≤ Δ ≤ N^{-C_K}`, `0 ≤ P ≤ N^{C_P}` and
`C_K ≥ D₁ + 4D + k + 2C_P + 8`: `Lc · 88 Δ P² / (N^{-D})⁴ ≤ N^{-D₁}/2`. -/
private theorem gridAsm_yBudget {N : ℝ} (hN2 : (2 : ℝ) ≤ N) (k : ℕ) {D D₁ C_P C_K : ℝ}
    (hCK : D₁ + 4 * D + k + 2 * C_P + 8 ≤ C_K) {Lc : ℝ} (hLc0 : 0 ≤ Lc) (hLc : Lc ≤ N ^ k)
    {Δ P : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ N ^ (-C_K)) (hP0 : 0 ≤ P) (hP : P ≤ N ^ C_P) :
    Lc * (88 * Δ * P ^ 2) / (N ^ (-D)) ^ 4 ≤ N ^ (-D₁) / 2 := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hLk : Lc ≤ N ^ (k : ℝ) := by rwa [Real.rpow_natCast]
  have hP2 : P ^ 2 ≤ N ^ (2 * C_P) := by
    have h1 : P ^ 2 ≤ (N ^ C_P) ^ 2 := pow_le_pow_left₀ hP0 hP 2
    have h2 : (N ^ C_P) ^ 2 = N ^ (2 * C_P) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
    linarith
  have hx : (N ^ (-D)) ^ 4 = N ^ (-(4 * D)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hxpos : 0 < (N ^ (-D)) ^ 4 := by positivity
  have key : Lc * (88 * Δ * P ^ 2) ≤ 88 * N ^ ((k : ℝ) + -C_K + 2 * C_P) := by
    calc Lc * (88 * Δ * P ^ 2) = 88 * (Lc * Δ * P ^ 2) := by ring
      _ ≤ 88 * (N ^ (k : ℝ) * N ^ (-C_K) * N ^ (2 * C_P)) := by gcongr
      _ = 88 * N ^ ((k : ℝ) + -C_K + 2 * C_P) := by
          rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hexp : (k : ℝ) + -C_K + 2 * C_P ≤ -D₁ + -(4 * D) + -8 := by linarith
  have hmono : N ^ ((k : ℝ) + -C_K + 2 * C_P) ≤ N ^ (-D₁ + -(4 * D) + -8) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have h8 : 88 * N ^ (-8 : ℝ) ≤ 1 / 2 := by
    have hN8 : (256 : ℝ) ≤ N ^ (8 : ℝ) := by
      rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ N ^ 8 := pow_le_pow_left₀ (by norm_num) hN2 8
    rw [Real.rpow_neg hN0.le]
    have hpos : 0 < N ^ (8 : ℝ) := by positivity
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    linarith
  rw [div_le_iff₀ hxpos, hx]
  have hsplit : N ^ (-D₁ + -(4 * D) + -8) = N ^ (-D₁) * N ^ (-(4 * D)) * N ^ (-8 : ℝ) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0]
  have hA : 0 ≤ N ^ (-D₁) * N ^ (-(4 * D)) := by positivity
  calc Lc * (88 * Δ * P ^ 2)
      ≤ 88 * N ^ (-D₁ + -(4 * D) + -8) := key.trans (by linarith)
    _ = (N ^ (-D₁) * N ^ (-(4 * D))) * (88 * N ^ (-8 : ℝ)) := by
        rw [hsplit]; ring
    _ ≤ (N ^ (-D₁) * N ^ (-(4 * D))) * (1 / 2) :=
        mul_le_mul_of_nonneg_left h8 hA
    _ = N ^ (-D₁) / 2 * N ^ (-(4 * D)) := by ring

end Budget

/-! ## 8. The fourth-moment tail of the second-order part `Y` -/

section YMoment

variable {d : ℕ} (sz : Sizes d)

private lemma gridAsm_norm_pow4_le_re_im (z : ℂ) : ‖z‖ ^ 4 ≤ 2 * (z.re ^ 4 + z.im ^ 4) := by
  have h : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
  have h4 : ‖z‖ ^ 4 = (z.re ^ 2 + z.im ^ 2) ^ 2 := by rw [← h]; ring
  rw [h4]
  nlinarith [sq_nonneg (z.re ^ 2 - z.im ^ 2)]

/-- `stoppedEdgeN … b j` is `filt sz (j+1)`-strongly measurable (RBM1D
`stronglyMeasurable_stoppedEdge_V2`, `GridAssemblyV2.lean:268`). -/
private theorem gridAsm_stronglyMeasurable_stoppedEdgeN {n k : ℕ} (E : ℝ)
    (σ : Fin k → Bool) (u : ℕ → ℝ) (t' : ℝ) {τ : PathΩ sz → ℕ}
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    (hY : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Y j)) (b : Fin k → Zd d (sz.L n)) (j : ℕ) :
    StronglyMeasurable[filt sz (j + 1)] (stoppedEdgeN sz E σ u t' τ Y b j) := by
  have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
    ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
  exact (gridAsm_stronglyMeasurable_Ugen_apply d (sz.L n) (sz.lam n) E σ _ _ (hY j) b).indicator hset

/-- The stopped sum at one label is the `m`-horizon sum of `stoppedEdgeN` (`sum_stopped`). -/
private theorem gridAsm_stopped_sum_eq {n k : ℕ} (E : ℝ) (σ : Fin k → Bool)
    (u : ℕ → ℝ) (t' : ℝ) (τ : PathΩ sz → ℕ)
    (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ) (ω : PathΩ sz)
    (b : Fin k → Zd d (sz.L n)) :
    ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) t' (Y j ω) b
      = ∑ j ∈ Finset.range m, stoppedEdgeN sz E σ u t' τ Y b j ω := by
  have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
    (fun i ω' => Ugen d (sz.L n) (sz.lam n) E σ (u i) t' (Y (i - 1) ω') b) τ m ω
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  rfl

/-- **The per-target fourth moment of the propagated, stopped `Y` sum** (RBM1D
`stopped_duhamel_moment4_fixed`, `GridAssemblyV2.lean:289`): from `YMomentBoundsN`,
`E‖(Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j)_b‖⁴ ≤ 4 (8 (Σ_{j<m} v_j)² + 3 Σ_{j<m} w_j)`; the fourth power is
integrable. -/
private theorem gridAsm_moment4_fixed {n k : ℕ} {E : ℝ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsN sz E σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) {m : ℕ} (hm : m ≤ K)
    (b : Fin k → Zd d (sz.L n)) :
    Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) (pathP sz)
      ∧ ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂(pathP sz)
        ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
  set W : ℕ → PathΩ sz → ℂ := stoppedEdgeN sz E σ u (u m) τ Y b with hWdef
  have hsum : ∀ ω, ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b = ∑ j ∈ Finset.range m, W j ω :=
    fun ω => gridAsm_stopped_sum_eq sz E σ u (u m) τ Y m ω b
  have hWm : ∀ j, StronglyMeasurable[filt sz (j + 1)] (W j) := fun j =>
    gridAsm_stronglyMeasurable_stoppedEdgeN sz E σ u (u m) hτ hY.1 b j
  have h8 : ∀ j < m, _ := fun j hj => hY.2 m hm b j hj
  have hre := gridAsm_mart_moment4 (μ := pathP sz) (ℱ := filt sz) (fun j ω => (W j ω).re) v w m
    (fun j => Complex.continuous_re.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).1) (fun j hj => (h8 j hj).2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.1)
  have him := gridAsm_mart_moment4 (μ := pathP sz) (ℱ := filt sz) (fun j ω => (W j ω).im) v w m
    (fun j => Complex.continuous_im.comp_stronglyMeasurable (hWm j))
    (fun j hj => (h8 j hj).2.1) (fun j hj => (h8 j hj).2.2.2.1)
    (fun j hj => (h8 j hj).2.2.2.2.2.1) (fun j hj => hv0 j (by omega))
    (fun j hj => (h8 j hj).2.2.2.2.2.2.2)
  have hpt : ∀ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4
        ≤ 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) := by
    intro ω
    rw [hsum ω]
    have := gridAsm_norm_pow4_le_re_im (∑ j ∈ Finset.range m, W j ω)
    rwa [Complex.re_sum, Complex.im_sum] at this
  have hsm : StronglyMeasurable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) := by
    have heq : (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4)
        = fun ω => ‖∑ j ∈ Finset.range m, W j ω‖ ^ 4 := funext fun ω => by rw [hsum ω]
    rw [heq]
    refine (Finset.stronglyMeasurable_fun_sum (Finset.range m) fun j _ =>
      (hWm j).mono ((filt sz).le (j + 1))).norm.pow 4
  have hdom : Integrable (fun ω =>
      2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4 + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4))
      (pathP sz) := (hre.1.add him.1).const_mul 2
  have hint : Integrable (fun ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4) (pathP sz) :=
    hdom.mono' hsm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) b‖ ^ 4 ∂(pathP sz)
      ≤ ∫ ω, 2 * ((∑ j ∈ Finset.range m, (W j ω).re) ^ 4
          + (∑ j ∈ Finset.range m, (W j ω).im) ^ 4) ∂(pathP sz) := integral_mono hint hdom hpt
    _ = 2 * (∫ ω, (∑ j ∈ Finset.range m, (W j ω).re) ^ 4 ∂(pathP sz)
          + ∫ ω, (∑ j ∈ Finset.range m, (W j ω).im) ^ 4 ∂(pathP sz)) := by
        rw [integral_const_mul, integral_add hre.1 him.1]
    _ ≤ 4 * (8 * (∑ j ∈ Finset.range m, v j) ^ 2 + 3 * ∑ j ∈ Finset.range m, w j) := by
        linarith [hre.2.2, him.2.2]

/-- **Markov + union (the moment `Y` tail)** (RBM1D `stopped_duhamel_moment4_union`,
`GridAssemblyV2.lean:360`): over all targets `m ≤ K` and all labels,
`P{∃ m ≤ K, ∃ a, x ≤ ‖Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Y_j‖_a} ≤ (K+1) Lc · 4 (8 V² + 3 W) / x⁴` with
`Lc` the number of labels, `V = Σ_{j<K} v_j`, `W = Σ_{j<K} w_j`. -/
private theorem gridAsm_moment4_union {n k : ℕ} {E : ℝ} {σ : Fin k → Bool}
    {u : ℕ → ℝ} {τ : PathΩ sz → ℕ} (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) {K : ℕ}
    {Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {v w : ℕ → ℝ}
    (hY : YMomentBoundsN sz E σ u τ K Y v w) (hv0 : ∀ j < K, 0 ≤ v j) (hw0 : ∀ j < K, 0 ≤ w j)
    {x : ℝ} (hx : 0 < x) :
    (pathP sz).real {ω | ∃ m ≤ K, ∃ a : Fin k → Zd d (sz.L n), x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) a‖} ≤
      (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / x ^ 4 := by
  set F : ℕ → (Fin k → Zd d (sz.L n)) → PathΩ sz → ℝ := fun m a ω => ‖∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) a‖ with hFdef
  set Bd : ℝ := 4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)
    with hBd
  have hx4 : 0 < x ^ 4 := by positivity
  have hone : ∀ m ≤ K, ∀ a, (pathP sz).real {ω | x ≤ F m a ω} ≤ Bd / x ^ 4 := by
    intro m hm a
    obtain ⟨hI, hM⟩ := gridAsm_moment4_fixed sz hτ hY hv0 hm a
    have hV : ∑ j ∈ Finset.range m, v j ≤ ∑ j ∈ Finset.range K, v j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hv0 j (Finset.mem_range.mp hj))
    have hV0 : 0 ≤ ∑ j ∈ Finset.range m, v j := Finset.sum_nonneg fun j hj =>
      hv0 j (by have := Finset.mem_range.mp hj; omega)
    have hW : ∑ j ∈ Finset.range m, w j ≤ ∑ j ∈ Finset.range K, w j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        (fun j hj _ => hw0 j (Finset.mem_range.mp hj))
    have hMk : ∫ ω, F m a ω ^ 4 ∂(pathP sz) ≤ Bd := by
      refine hM.trans ?_
      rw [hBd]
      have : (∑ j ∈ Finset.range m, v j) ^ 2 ≤ (∑ j ∈ Finset.range K, v j) ^ 2 :=
        pow_le_pow_left₀ hV0 hV 2
      linarith
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun ω => by positivity) hI (x ^ 4)
    have hset : {ω | x ≤ F m a ω} = {ω | x ^ 4 ≤ F m a ω ^ 4} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h; exact pow_le_pow_left₀ hx.le h 4
      · intro h
        exact (pow_le_pow_iff_left₀ hx.le (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp h
    rw [hset, le_div_iff₀ hx4]
    calc (pathP sz).real {ω | x ^ 4 ≤ F m a ω ^ 4} * x ^ 4
        = x ^ 4 * (pathP sz).real {ω | x ^ 4 ≤ F m a ω ^ 4} := by ring
      _ ≤ ∫ ω, F m a ω ^ 4 ∂(pathP sz) := hmark
      _ ≤ Bd := hMk
  have hincl : {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ⊆ ⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω} := by
    rintro ω ⟨m, hm, a, ha⟩
    simp only [Set.mem_iUnion]
    exact ⟨m, Finset.mem_range.mpr (by omega), a, ha⟩
  calc (pathP sz).real {ω | ∃ m ≤ K, ∃ a, x ≤ F m a ω}
      ≤ (pathP sz).real (⋃ m ∈ Finset.range (K + 1), ⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω}) :=
        measureReal_mono hincl (measure_ne_top _ _)
    _ ≤ ∑ m ∈ Finset.range (K + 1), (pathP sz).real
          (⋃ a : Fin k → Zd d (sz.L n), {ω | x ≤ F m a ω}) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ m ∈ Finset.range (K + 1), ∑ a : Fin k → Zd d (sz.L n),
          (pathP sz).real {ω | x ≤ F m a ω} :=
        Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
    _ ≤ ∑ _m ∈ Finset.range (K + 1), ∑ _a : Fin k → Zd d (sz.L n), Bd / x ^ 4 := by
        refine Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => ?_
        exact hone m (by have := Finset.mem_range.mp hm; omega) a
    _ = (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Bd / x ^ 4 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul,
          nsmul_eq_mul]
        push_cast
        ring

end YMoment

/-! ## 9. The single-scale core -/

section Core

variable {d : ℕ} (sz : Sizes d)

/-- **The single-scale core of `assembledN`** (port of RBM1D `grid_assembly_stopped_core_pw`,
`GridAssemblyV2.lean:635`), with free thresholds `lam ≥ 0` (Azuma, for the first-chaos part `Z`)
and `xY > 0` (fourth-moment tail, for the second-order part `Y`).  The sharp restricted `κ, ε` act
only on `A0` and the drift; the remainder `R` uses the derived coarse `(1 + (1 - u_m)⁻¹)^k`.
`Lc = (L^d)^k` is the number of labels.  The `Z`-event is the union over `(m, a)`,
`1 ≤ m ≤ K`, of the Azuma events (RBM1D `stopped_duhamel_azuma_union`,
`GridDuhamelTail.lean:347`); the `Y`-event is `gridAsm_moment4_union`. -/
private theorem gridAsm_core {n k : ℕ} {E : ℝ} {σ : Fin k → Bool} {u : ℕ → ℝ}
    {τ : PathΩ sz → ℕ} {Δ : ℝ} {K : ℕ}
    {Cls : ℕ → ℝ → ((Fin k → Zd d (sz.L n)) → ℂ) → Prop}
    {A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {A : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ}
    {Dr Z Y R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ} {κ εK : ℕ → ℕ → ℝ} {δ0 : ℝ}
    {dDrift δD : ℕ → PathΩ sz → ℝ} {c : ℕ → (Fin k → Zd d (sz.L n)) → ℕ → ℝ≥0}
    {v w stepErr : ℕ → ℝ}
    (hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j))
    (hsubG : ∀ m ≤ K, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopN sz E σ u τ Z m a j (c m a j))
    (h : GridAssemblyHypN sz E σ u τ Δ K Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr)
    {lam : ℝ} (hlam : 0 ≤ lam) {xY : ℝ} (hxY : 0 < xY) :
    ∃ G : Set (PathΩ sz), (pathP sz).real Gᶜ ≤
        4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4)
        + (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4
      ∧ ∀ ω ∈ G, 0 < τ ω → ∀ m ≤ K, ∀ a : Fin k → Zd d (sz.L n),
          ‖A m ω a‖ ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖))
            + εK 0 m * δ0
            + Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω)
            + lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))
            + xY
            + ∑ j ∈ Finset.range m, (1 + (1 - u m)⁻¹) ^ k * stepErr j := by
  -- the Azuma event: targets `1 ≤ m ≤ K` (the `m = 0` sum is empty)
  set GZ : Set (PathΩ sz) := {ω | ∃ m ∈ Finset.Icc 1 K, ∃ a : Fin k → Zd d (sz.L n),
      lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω) a‖} with hGZdef
  have hGZbound : (pathP sz).real GZ ≤
      4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
    set E' : ℕ → (Fin k → Zd d (sz.L n)) → Set (PathΩ sz) := fun m a =>
      {ω | lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min m (τ ω)),
          Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω) a‖} with hE'def
    have hincl : GZ ⊆ ⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Zd d (sz.L n), E' m a := by
      rintro ω ⟨m, hm, a, ha⟩
      simp only [Set.mem_iUnion]
      exact ⟨m, hm, a, ha⟩
    have hone : ∀ m ∈ Finset.Icc 1 K, ∀ a : Fin k → Zd d (sz.L n),
        (pathP sz).real (E' m a) ≤ 4 * Real.exp (-lam ^ 2 / 4) := by
      intro m hm a
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
      have hmK : m ≤ K := (Finset.mem_Icc.mp hm).2
      have hcpos : 0 < ∑ j ∈ Finset.range m, (c m a j : ℝ) := h.hc_pos m hm1 hmK a
      have hx0 : 0 ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by positivity
      have hax := gridAsm_azuma_Ugen sz E σ u hτmeas m (fun j _ => hZmeas j) a (c m a)
        (hsubG m hmK a) hx0
      have hxsq : (lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ))) ^ 2
          = lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ) := by
        rw [mul_pow, Real.sq_sqrt hcpos.le]
      rw [hxsq] at hax
      have hexp : -(lam ^ 2 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) /
          (4 * ∑ j ∈ Finset.range m, (c m a j : ℝ)) = -lam ^ 2 / 4 := by
        field_simp
      rw [hexp] at hax
      exact hax
    calc (pathP sz).real GZ
        ≤ (pathP sz).real (⋃ m ∈ Finset.Icc 1 K, ⋃ a : Fin k → Zd d (sz.L n), E' m a) :=
          measureReal_mono hincl (measure_ne_top _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 K, (pathP sz).real (⋃ a : Fin k → Zd d (sz.L n), E' m a) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 K, ∑ a : Fin k → Zd d (sz.L n), (pathP sz).real (E' m a) :=
          Finset.sum_le_sum fun m _ => measureReal_iUnion_fintype_le _
      _ ≤ ∑ _m ∈ Finset.Icc 1 K, ∑ _a : Fin k → Zd d (sz.L n), 4 * Real.exp (-lam ^ 2 / 4) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun a _ => hone m hm a
      _ = 4 * (K : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * Real.exp (-lam ^ 2 / 4) := by
          rw [Finset.sum_const, Finset.sum_const, Nat.card_Icc, Finset.card_univ, nsmul_eq_mul,
            nsmul_eq_mul]
          have hcard : K + 1 - 1 = K := by omega
          rw [hcard]
          ring
  -- the fourth-moment `Y` event
  set GY : Set (PathΩ sz) := {ω | ∃ m ≤ K, ∃ a : Fin k → Zd d (sz.L n), xY ≤
      ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) a‖} with hGYdef
  have hGYbound : (pathP sz).real GY ≤ (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j)) / xY ^ 4 :=
    gridAsm_moment4_union sz hτmeas h.hY h.hv0 h.hw0 hxY
  -- the full-measure events `hexp`, `hR`
  have hexpAll : ∀ᵐ ω ∂(pathP sz), ∀ m, m ≤ K → A m ω = Ugen d (sz.L n) (sz.lam n) E σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) := by
    refine ae_all_iff.mpr fun m => ?_
    by_cases hm : m ≤ K
    · filter_upwards [h.hexp m hm] with ω hω _ using hω
    · exact ae_of_all _ fun ω hm' => absurd hm' hm
  have hAllAE := hexpAll.and h.hR
  set Ω0c : Set (PathΩ sz) := {ω | ¬ ((∀ m, m ≤ K → A m ω = Ugen d (sz.L n) (sz.lam n) E σ (u 0) (u m) (A0 ω)
      + ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
          ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
      (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j))} with hΩ0cdef
  have hΩ0cnull : (pathP sz).real Ω0c = 0 := by
    have h0 : (pathP sz) Ω0c = 0 := (MeasureTheory.ae_iff).mp hAllAE
    simp [Measure.real, h0]
  refine ⟨(GZ ∪ GY ∪ Ω0c)ᶜ, ?_, ?_⟩
  · rw [compl_compl]
    calc (pathP sz).real (GZ ∪ GY ∪ Ω0c)
        ≤ (pathP sz).real (GZ ∪ GY) + (pathP sz).real Ω0c := measureReal_union_le _ _
      _ ≤ ((pathP sz).real GZ + (pathP sz).real GY) + (pathP sz).real Ω0c := by
          have h1 := measureReal_union_le (μ := pathP sz) GZ GY
          linarith
      _ ≤ _ := by rw [hΩ0cnull]; linarith
  · intro ω hω hτpos m hmK a
    have hωGZ : ω ∉ GZ := fun h' => hω (Or.inl (Or.inl h'))
    have hωGY : ω ∉ GY := fun h' => hω (Or.inl (Or.inr h'))
    have hωΩ0 : ω ∉ Ω0c := fun h' => hω (Or.inr h')
    have hAllω : (∀ m, m ≤ K → A m ω = Ugen d (sz.L n) (sz.lam n) E σ (u 0) (u m) (A0 ω)
        + ∑ j ∈ Finset.range (min m (τ ω)), Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
            ((Δ : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω)) ∧
        (∀ j, j < K → j < τ ω → ∀ b, ‖R j ω b‖ ≤ stepErr j) := by
      by_contra hc
      exact hωΩ0 hc
    obtain ⟨hAll, hRall⟩ := hAllω
    set INIT : ℂ := Ugen d (sz.L n) (sz.lam n) E σ (u 0) (u m) (A0 ω) a with hINITdef
    set S1 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Dr j ω) a with hS1def
    set S2 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Z j ω) a with hS2def
    set S3 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Y j ω) a with hS3def
    set S4 : ℂ := ∑ j ∈ Finset.range (min m (τ ω)),
      Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (R j ω) a with hS4def
    have hAeq : A m ω a = INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4) := by
      rw [hAll m hmK, Pi.add_apply, Finset.sum_apply]
      congr 1
      rw [Finset.sum_congr rfl (fun j _ => gridAsm_Ugen_four d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m)
        (Δ : ℂ) (Dr j ω) (Z j ω) (Y j ω) (R j ω) a), Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hINITle : ‖INIT‖
        ≤ κ 0 m * (Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖)) + εK 0 m * δ0 := by
      obtain ⟨b0⟩ := (inferInstance : Nonempty (Fin k → Zd d (sz.L n)))
      have hA0nn : (0 : ℝ) ≤ Finset.univ.sup' Finset.univ_nonempty (fun b => ‖A0 ω b‖) :=
        le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b0))
      exact h.hker 0 m (Nat.zero_le m) hmK (A0 ω) _ δ0 hA0nn h.hδ0
        (fun b => Finset.le_sup' (fun b => ‖A0 ω b‖) (Finset.mem_univ b)) (h.hA0cls ω hτpos) a
    have hS1le : ‖S1‖ ≤ ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (Dr j ω) a‖
            ≤ κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact h.hker (j + 1) m hjm hmK (Dr j ω) (dDrift j ω) (δD j ω)
          (h.hdDrift0 ω j (by omega)) (h.hδD0 ω j (by omega)) (h.hdrift ω j (by omega) hjτ)
          (h.hDcls ω j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      exact add_nonneg (mul_nonneg (h.hκ0 (j + 1) m hjm hmK) (h.hdDrift0 ω j (by omega)))
        (mul_nonneg (h.hε0 (j + 1) m hjm hmK) (h.hδD0 ω j (by omega)))
    have hS1le' : ‖(Δ : ℂ) * S1‖
        ≤ Δ * ∑ j ∈ Finset.range m, (κ (j + 1) m * dDrift j ω + εK (j + 1) m * δD j ω) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h.hΔ0]
      exact mul_le_mul_of_nonneg_left hS1le h.hΔ0
    have hS2le : ‖S2‖ ≤ lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
      by_cases hm0 : m = 0
      · subst hm0
        simp [hS2def]
      · have hlt : ‖S2‖ < lam * Real.sqrt (∑ j ∈ Finset.range m, (c m a j : ℝ)) := by
          by_contra hc
          push Not at hc
          exact hωGZ ⟨m, Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, hmK⟩, a, hc⟩
        exact hlt.le
    have hS3le : ‖S3‖ ≤ xY := by
      by_contra hc
      push Not at hc
      exact hωGY ⟨m, hmK, a, hc.le⟩
    have hS4le : ‖S4‖ ≤ ∑ j ∈ Finset.range m, (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
      have hm0 := h.hu0 m hmK
      have hm1 := h.hu1 m hmK
      have h2 : ∀ j ∈ Finset.range (min m (τ ω)),
          ‖Ugen d (sz.L n) (sz.lam n) E σ (u (j + 1)) (u m) (R j ω) a‖
            ≤ (1 + (1 - u m) ⁻¹) ^ k * stepErr j := by
        intro j hj
        have hjm : j < m := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_left _ _)
        have hjτ : j < τ ω := lt_of_lt_of_le (Finset.mem_range.mp hj) (min_le_right _ _)
        exact gridAsm_norm_Ugen_coarse d (sz.L n) (sz.lam n) (sz.three_le_L n) h.hE σ
          (h.hu0 (j + 1) (by omega)) (h.hu1 (j + 1) (by omega)) hm0 hm1
          (h.hstepErr0 j (by omega)) (hRall j (by omega) hjτ) a
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum h2).trans ?_)
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_left _ _)) ?_
      intro j hj _
      have hjm : j < m := Finset.mem_range.mp hj
      have hpos : 0 < 1 - u m := by linarith
      exact mul_nonneg (by positivity) (h.hstepErr0 j (by omega))
    rw [hAeq]
    calc ‖INIT + ((Δ : ℂ) * S1 + S2 + S3 + S4)‖
        ≤ ‖INIT‖ + ‖(Δ : ℂ) * S1‖ + ‖S2‖ + ‖S3‖ + ‖S4‖ := by
          have e1 := norm_add_le INIT ((Δ : ℂ) * S1 + S2 + S3 + S4)
          have e2 := norm_add_le ((Δ : ℂ) * S1 + S2 + S3) S4
          have e3 := norm_add_le ((Δ : ℂ) * S1 + S2) S3
          have e4 := norm_add_le ((Δ : ℂ) * S1) S2
          linarith
      _ ≤ _ := by linarith

/-- The number of labels `|Fin k → Zd d L| = (L^d)^k` is at most `N^k`, `N = (W L)^d` (RBM1D:
`card_loopArg_V2`, `L^n ≤ N^{nC_L}`; here `L^d ≤ (W L)^d` since `W ≥ 1`; `d` enters only through
the base, so the exponent count `D₁ + 4D + k + 2C_P + 8 ≤ C_K` is the same as in RBM2D). -/
private theorem gridAsm_card_label (n k : ℕ) :
    Fintype.card (Fin k → Zd d (sz.L n)) ≤ (sz.size n) ^ k := by
  rw [Fintype.card_fun, Fintype.card_fin]
  have h : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
    simp [Zd, ZMod.card]
  rw [h]
  refine Nat.pow_le_pow_left ?_ k
  rw [Sizes.size]
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

end Core

/-! ## 10. Target 2: the assembled pathwise bound -/

section Assembled

variable {d : ℕ} (sz : Sizes d)

/-- **Target `assembledN`** (the pin `AssembledN` of §1; RBM2D `GridAssemblyN:1140`): RBM1D
`grid_assembly_stopped_pathwise` (`GridAssemblyV2.lean:891`) for `Ugen` on `Fin k → Zd d L`.
Route: `SizeTendsto` turns the real-variable Azuma budget (`gridAsm_zBudget`) into an
eventual statement in `n`; the single-scale core (`gridAsm_core`) at `lam = N^ε`,
`xY = N^{-D} > 0` gives an event `G` with `P(Gᶜ) ≤ 4 K Lc exp(-N^{2ε}/4) +
(K+1) Lc · 4 (8 V² + 3 W) / xY⁴`; the first term is `≤ N^{-D₁}/2` by the Azuma budget and the
second is `≤ N^{-D₁}/2` by `moment4_budget_le` and the `Y` budget (exponent
`D₁ + 4D + k + 2C_P + 8 ≤ C_K`, label count `Lc ≤ N^k`).  The pathwise bound is the core's.  The
probability budget is the only place where `sz.SizeTendsto` is used. -/
theorem assembledN : AssembledN sz := by
  intro hSize k ε hε D D₁ C_P C_K hCK0 hCK
  filter_upwards [hSize.eventually (gridAsm_zBudget k hε D₁ C_K hCK0)] with n hn
  obtain ⟨hN2, hbudZ⟩ := hn
  intro K E σ u τ Δ Cls A0 A Dr Z Y R κ εK δ0 dDrift δD c v w stepErr P hK1 hK hΔ hKΔ hP0 hP hv
    hw hτmeas hZmeas hsubG h
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hx : 0 < ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨G, hG, hbd⟩ := gridAsm_core sz hτmeas hZmeas hsubG h
    (Real.rpow_nonneg hN0.le ε) hx
  refine ⟨G, hG.trans ?_, hbd⟩
  have hLc0 : (0 : ℝ) ≤ (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) := Nat.cast_nonneg _
  have hLc : (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ k := by
    exact_mod_cast gridAsm_card_label sz n k
  have hZ := hbudZ K _ hK hLc0 hLc
  have hbud := gridAsm_moment4_budget_le h.hΔ0 hP0 hKΔ hK1 h.hv0 h.hw0 hv hw
  have hY := gridAsm_yBudget hN2 k hCK hLc0 hLc h.hΔ0 hΔ hP0 hP
  have hx4 : 0 < (((sz.size n : ℕ) : ℝ) ^ (-D)) ^ 4 := by positivity
  have hYle : (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
      * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        / (((sz.size n : ℕ) : ℝ) ^ (-D)) ^ 4 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) / 2 := by
    refine le_trans ?_ hY
    rw [show (K + 1 : ℝ) * (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ)
        * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))
        = (Fintype.card (Fin k → Zd d (sz.L n)) : ℝ) * ((K + 1 : ℝ)
          * (4 * (8 * (∑ j ∈ Finset.range K, v j) ^ 2 + 3 * ∑ j ∈ Finset.range K, w j))) by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbud hLc0) hx4.le
  linarith

end Assembled

/-! ## 11. Compiled nonempty instances (`d = 3`)

Data (all on the merged `sz0`: `L_n = 4 (n+1)`, `W_n = (2 (n+1))^5`, `lam_n = (2 (n+1))^{-6}`; at
`n = 0`: `L = 4`, `W = 32`, `N = 2097152 = 2^21`), energy `E ≡ 1/2`:
* `stoppedAzumaZN`: the merged grid `(s, v, K) = (sInst, vg, Kg) = (0, 1/32, 4)` of `GridGoodNInst`
  (`Δ = 1/128`), `k = 3`, `σ = (+,+,-)`, `τ ≡ m ≡ 4`, proxy `c ≡ 1`, `x = 8`; only the
  sub-Gaussian family for `ZvecN` stays a hypothesis (the output of `AzumaSubGN`, ST2-34/35), and a
  second instance with a genuinely random `Z` proves it;
* `assembledN`: the window `(s, t) = (sInst, tInst) = (0, 1/16)` and the grid size `K_n = N_n^{17}`
  (`C_K = 17`; the merged `Kg ≡ 4` has `Δ = 1/128`, which violates `Δ ≤ N^{-C_K}` for `C_K ≥ 8 + k`),
  `k = 3`, `ε = 1`, `D = D₁ = 1`, `C_P = 0` (exponent count `1 + 4 + 3 + 0 + 8 = 16 ≤ 17`), the first
  chaos increment `Z_j = √Δ · Re tr X_{j+1}` (not zero, see `gridAsm_witZ_ne_zero`), for which
  `SubGaussStopN` is proved (`gridAsm_witSubGaussStop`), `A_0 ≡ 1`, `Y = R = Dr = 0`,
  `v = Δ²`, `w = Δ⁴`, `P = 1`.  The size hypothesis is `sz0_tendsto`. -/

namespace GridAssemblyNInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst

/-- The energy `E ≡ 1/2`. -/
def gridAsm_E : ℕ → ℝ := fun _ => 1 / 2

theorem gridAsm_E_abs_lt (n : ℕ) : |gridAsm_E n| < 2 := by
  simp only [gridAsm_E]
  rw [abs_of_pos (by norm_num)]
  norm_num

/-! ### The instance of `stoppedAzumaZN` on the merged grid `Kg ≡ 4`, `vg ≡ 1/32` -/

/-- **Instance of `stoppedAzumaZN`** at `sz0`, the merged grid `(sInst, vg, Kg)`, `E ≡ 1/2`, any
size index `n`, signs `σ` and label `a`, `τ ≡ m ≡ Kg n`, a constant proxy `C` and any `x ≥ 0`.  The
hypotheses of the theorem are discharged (`|E| < 2`, `0 ≤ s ≤ v < 1`, `Kg ≠ 0`, the constant
stopping time, `m ≤ Kg n`); only the sub-Gaussian family for `ZvecN` (`AzumaSubGN`'s output,
ST2-34/35) stays a hypothesis, at an arbitrary proxy `C` (so that no numerical value of the proxy is
asserted). -/
theorem gridAsm_stoppedAzumaZN_instance (n : ℕ) (σ : Fin 3 → Bool) (a : Fin 3 → Zd 3 (sz0.L n))
    (C : ℝ≥0)
    (hsub : ∀ j < Kg n, SubGaussStopN sz0 (gridAsm_E n) σ (gridTime sInst vg Kg n)
      (fun _ => Kg n) (fun j ω => ZvecN sz0 gridAsm_E sInst vg Kg n j σ ω) (Kg n) a j C)
    (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min (Kg n) (Kg n)),
        Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst vg Kg n (j + 1))
          (gridTime sInst vg Kg n (Kg n)) (ZvecN sz0 gridAsm_E sInst vg Kg n j σ ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ((Kg n : ℝ) * (C : ℝ)))) := by
  have h := stoppedAzumaZN sz0 gridAsm_E sInst vg Kg gridAsm_E_abs_lt
    (fun n => by simp [sInst]) (fun n => by norm_num [sInst, vg]) (fun n => by norm_num [vg])
    (fun n => by simp [Kg]) n 3 σ (fun _ => Kg n) (fun j => MeasurableSet.const _)
    (Kg n) le_rfl a (fun _ => C) hsub x hx
  simpa using h

/-- The bound has content: at `x = 4 √(Kg n · C)` (`C > 0`) its right side is `4 e^{-4} < 1`. -/
theorem gridAsm_stoppedAzumaZN_bound_lt_one (n : ℕ) {C : ℝ≥0} (hC : 0 < C) :
    4 * Real.exp (-(4 * Real.sqrt ((Kg n : ℝ) * (C : ℝ))) ^ 2 / (4 * ((Kg n : ℝ) * (C : ℝ)))) <
      1 := by
  have hK : (0 : ℝ) < (Kg n : ℝ) * (C : ℝ) := mul_pos (by simp [Kg]) (NNReal.coe_pos.2 hC)
  have h1 : (4 * Real.sqrt ((Kg n : ℝ) * (C : ℝ))) ^ 2 = 16 * ((Kg n : ℝ) * (C : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hK.le]; ring
  have h2 : -(4 * Real.sqrt ((Kg n : ℝ) * (C : ℝ))) ^ 2 / (4 * ((Kg n : ℝ) * (C : ℝ))) = -4 := by
    rw [h1]
    have hK0 : (Kg n : ℝ) ≠ 0 := by simp [Kg]
    have hC0 : (C : ℝ) ≠ 0 := (NNReal.coe_pos.2 hC).ne'
    field_simp
    norm_num
  rw [h2]
  have h3 : (4 : ℝ) + 1 < Real.exp 4 := Real.add_one_lt_exp (by norm_num)
  have h4 : Real.exp (-4) = (Real.exp 4)⁻¹ := Real.exp_neg 4
  rw [h4]
  have h5 : 0 < Real.exp 4 := Real.exp_pos 4
  rw [mul_inv_lt_iff₀ h5]
  linarith

/-- **Concrete instance of `stoppedAzumaZN`**: `n = 0` (`L = 4`, `W = 32`, `N = 2097152`,
`E = 1/2`, `Δ = 1/128`, `Kg 0 = 4` grid steps), `k = 3`, `σ = (+,+,-)`, label `a = 0`, `τ ≡ m ≡ 4`,
a constant proxy `C > 0`, threshold `x = 4 √(4 C)`: the tail is at most `4 e^{-4} < 1`
(`gridAsm_stoppedAzumaZN_bound_lt_one`).  Only `hsub` stays a hypothesis. -/
theorem gridAsm_stoppedAzumaZN_instance_concrete (C : ℝ≥0) (hC : 0 < C)
    (hsub : ∀ j < Kg 0, SubGaussStopN sz0 (gridAsm_E 0) ![true, true, false]
      (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => ZvecN sz0 gridAsm_E sInst vg Kg 0 j ![true, true, false] ω) (Kg 0)
      (fun _ => 0) j C) :
    (pathP sz0).real {ω | 4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ)) ≤
        ‖∑ j ∈ Finset.range (min (Kg 0) (Kg 0)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (gridAsm_E 0) ![true, true, false]
            (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 (Kg 0))
            (ZvecN sz0 gridAsm_E sInst vg Kg 0 j ![true, true, false] ω) (fun _ => 0)‖} ≤
      4 * Real.exp (-4) := by
  have h := gridAsm_stoppedAzumaZN_instance 0 ![true, true, false] (fun _ => 0) C hsub
    (4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ))) (by positivity)
  have hK : (0 : ℝ) < (Kg 0 : ℝ) * (C : ℝ) := mul_pos (by simp [Kg]) (NNReal.coe_pos.2 hC)
  have h1 : (4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ))) ^ 2 = 16 * ((Kg 0 : ℝ) * (C : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hK.le]; ring
  have h2 : -(4 * Real.sqrt ((Kg 0 : ℝ) * (C : ℝ))) ^ 2 / (4 * ((Kg 0 : ℝ) * (C : ℝ))) = -4 := by
    rw [h1]
    have hK0 : (Kg 0 : ℝ) ≠ 0 := by simp [Kg]
    have hC0 : (C : ℝ) ≠ 0 := (NNReal.coe_pos.2 hC).ne'
    field_simp
    norm_num
  rw [h2] at h
  exact h

/-! ### The grid `K_n = N_n^{17}` on the window `(0, 1/16)` -/

/-- The grid size `K_n = N_n^{17}` (`N_n = sz0.size n`), so that `Δ = 1/(16 K_n) ≤ N_n^{-17}`. -/
def gridAsm_K (n : ℕ) : ℕ := (sz0.size n) ^ 17

theorem gridAsm_size_pos (n : ℕ) : 0 < sz0.size n := by
  unfold Sizes.size
  exact pow_pos (Nat.mul_pos (sz0.W_pos n) (by have := sz0.three_le_L n; omega)) 3

theorem gridAsm_K_pos (n : ℕ) : 0 < gridAsm_K n := pow_pos (gridAsm_size_pos n) 17

theorem gridAsm_K_ne (n : ℕ) : gridAsm_K n ≠ 0 := (gridAsm_K_pos n).ne'

theorem gridAsm_sInst_le_tInst (n : ℕ) : sInst n ≤ tInst n := by norm_num [sInst, tInst]

theorem gridAsm_tInst_lt_one (n : ℕ) : tInst n < 1 := by norm_num [tInst]

theorem gridAsm_step (n : ℕ) :
    gridStep sInst tInst gridAsm_K n = 1 / (16 * (gridAsm_K n : ℝ)) := by
  have hK : (gridAsm_K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (gridAsm_K_ne n)
  simp only [gridStep, sInst, tInst]
  field_simp
  ring

theorem gridAsm_step_pos (n : ℕ) : 0 < gridStep sInst tInst gridAsm_K n := by
  rw [gridAsm_step]
  have : (0 : ℝ) < (gridAsm_K n : ℝ) := Nat.cast_pos.2 (gridAsm_K_pos n)
  positivity

/-- The grid data of the instance: `1 ≤ K ≤ ⌈N^{17}⌉`, `Δ ≤ N^{-17}`, `K Δ = 1/16`. -/
theorem gridAsm_grid_data (n : ℕ) :
    1 ≤ gridAsm_K n ∧
    gridAsm_K n ≤ ⌈((sz0.size n : ℕ) : ℝ) ^ (17 : ℝ)⌉₊ ∧
    gridStep sInst tInst gridAsm_K n ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(17 : ℝ)) ∧
    (gridAsm_K n : ℝ) * gridStep sInst tInst gridAsm_K n = 1 / 16 := by
  have hK : (0 : ℝ) < (gridAsm_K n : ℝ) := Nat.cast_pos.2 (gridAsm_K_pos n)
  have hpow : ((sz0.size n : ℕ) : ℝ) ^ (17 : ℝ) = (gridAsm_K n : ℝ) := by
    rw [show (17 : ℝ) = ((17 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact (Nat.cast_pow (sz0.size n) 17).symm
  refine ⟨gridAsm_K_pos n, ?_, ?_, ?_⟩
  · rw [hpow, Nat.ceil_natCast]
  · rw [Real.rpow_neg (Nat.cast_nonneg _), hpow, gridAsm_step]
    rw [← one_div, div_le_div_iff₀ (by positivity) hK]
    nlinarith
  · rw [gridAsm_step]
    field_simp

/-- The grid times of the instance are in `[0, 1/16]`. -/
theorem gridAsm_gridTime_bounds (n : ℕ) {m : ℕ} (hm : m ≤ gridAsm_K n) :
    0 ≤ gridTime sInst tInst gridAsm_K n m ∧ gridTime sInst tInst gridAsm_K n m ≤ 1 / 16 := by
  refine ⟨gridAsm_gridTime_nonneg sInst tInst gridAsm_K n (by simp [sInst])
    (gridAsm_sInst_le_tInst n) m, ?_⟩
  have h := gridAsm_gridTime_le sInst tInst gridAsm_K n (gridAsm_sInst_le_tInst n)
    (gridAsm_K_ne n) hm
  simpa [tInst] using h

/-! ### A nondegenerate witness: a genuinely random first-chaos increment

`Z_j = √Δ · Re tr X_{j+1}` (the same real Gaussian linear form at every label; direction `A = 1`) is
`filt (j+1)`-measurable, not identically zero (the coordinate `⟨n, (0,0,true)⟩` of `X_{j+1}` enters
`Re tr X_{j+1}` with coefficient `1`), and conditionally sub-Gaussian with proxy
`Δ · linTrVar n 1` (`hasCondSubgaussianMGF_linear`, `Path/Markov.lean:636`); its propagated stopped
image `1_{j<τ} (𝒰 Z_j)_a = ρ_a · Z_j` (`ρ_a` a deterministic complex number of modulus at most
`(1 + (1 - u_m)⁻¹)^3 ≤ (31/15)^3` for `u_m ≤ 1/16`) has real and imaginary parts that are
conditionally sub-Gaussian with the common proxy `78 Δ · linTrVar n 1 + 1`
(`((31/15)^3)^2 = 77.92 ≤ 78`; RBM2D has `729 = ((1 + 2)^3)^2` at `u_m ≤ 1/2`: the constant is
`k`- and `u_m`-dependent, not `d`-dependent).  So `SubGaussStopN` is proved, not assumed. -/

/-- The witness first-chaos increment `√Δ · Re tr X_{j+1}` (a real Gaussian linear form). -/
def gridAsm_witZ (n j : ℕ) (ω : PathΩ sz0) : ℝ :=
  Real.sqrt (gridStep sInst tInst gridAsm_K n) *
    linTr (sz := sz0) n
      (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
      (Sizes.seqXmat sz0 n (ω (j + 1)))

/-- The witness increment as a label vector (the same value at every label). -/
def gridAsm_witZvec (n j : ℕ) (ω : PathΩ sz0) : (Fin 3 → Zd 3 (sz0.L n)) → ℂ :=
  fun _ => ((gridAsm_witZ n j ω : ℝ) : ℂ)

open scoped Matrix.Norms.L2Operator in
theorem gridAsm_measurable_witZ (n j : ℕ) :
    Measurable[filt sz0 (j + 1)] (fun ω => gridAsm_witZ n j ω) := by
  have hX : Measurable[filt sz0 (j + 1)]
      (fun ω : PathΩ sz0 => Sizes.seqXmat sz0 n (ω (j + 1))) :=
    ((continuous_Xmat 3 (sz0.L n) (sz0.W n)).measurable.comp (Sizes.measurable_slice sz0 n)).comp
      (gridAsm_measurable_coord sz0 le_rfl)
  have hlin : Measurable (fun X : Matrix (Idx 3 (sz0.L n) (sz0.W n))
      (Idx 3 (sz0.L n) (sz0.W n)) ℂ => linTr (sz := sz0) n 1 X) := by
    unfold linTr
    exact (Complex.continuous_re.comp
      (Continuous.matrix_trace (continuous_const.matrix_mul continuous_id))).measurable
  exact (hlin.comp hX).const_mul _

theorem gridAsm_stronglyMeasurable_witZvec (n j : ℕ) :
    StronglyMeasurable[filt sz0 (j + 1)] (fun ω => gridAsm_witZvec n j ω) := by
  refine Measurable.stronglyMeasurable ?_
  exact @Measurable.of_eval _ _ _ (filt sz0 (j + 1)) _ _ fun _ =>
    Complex.measurable_ofReal.comp (gridAsm_measurable_witZ n j)

/-- The base proxy `Δ · linTrVar n 1`. -/
def gridAsm_witC0 (n : ℕ) : ℝ≥0 :=
  ⟨gridStep sInst tInst gridAsm_K n * linTrVar (sz := sz0) n
    (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ),
    mul_nonneg (gridAsm_gridStep_nonneg sInst tInst gridAsm_K n (gridAsm_sInst_le_tInst n))
      (linTrVar_nonneg n _)⟩

/-- The common proxy `78 Δ · linTrVar n 1 + 1 > 0` of the propagated witness. -/
def gridAsm_witProxy (n : ℕ) : ℝ≥0 := 78 * gridAsm_witC0 n + 1

theorem gridAsm_witProxy_pos (n : ℕ) : 0 < gridAsm_witProxy n := by
  unfold gridAsm_witProxy
  exact lt_of_lt_of_le zero_lt_one le_add_self

/-- The witness increment is conditionally sub-Gaussian with proxy `Δ · linTrVar n 1`. -/
theorem gridAsm_witZ_subG (n j : ℕ) :
    HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j) (fun ω => gridAsm_witZ n j ω)
      (gridAsm_witC0 n) (pathP sz0) := by
  have h := hasCondSubgaussianMGF_linear (sz := sz0) sInst tInst gridAsm_K n j
    (A := fun _ => (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
    measurable_const Set.univ MeasurableSet.univ
    (gridStep sInst tInst gridAsm_K n * linTrVar (sz := sz0) n
      (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ))
    (gridAsm_witC0 n).2 (fun _ _ => le_rfl)
  have hfun : (fun ω : PathΩ sz0 => (Set.univ : Set (PathΩ sz0)).indicator
      (fun ω => Real.sqrt (gridStep sInst tInst gridAsm_K n) *
        linTr (sz := sz0) n
          (1 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ)
          (Sizes.seqXmat sz0 n (ω (j + 1)))) ω) = fun ω => gridAsm_witZ n j ω := by
    funext ω
    simp [gridAsm_witZ]
  rw [hfun] at h
  exact h

/-- Sub-Gaussianity is monotone in the proxy. -/
private theorem gridAsm_hasCondSubG_mono {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {hm : m ≤ mΩ} [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    {c c' : ℝ≥0} (h : HasCondSubgaussianMGF m hm X c μ) (hcc : c ≤ c') :
    HasCondSubgaussianMGF m hm X c' μ := by
  change Kernel.HasSubgaussianMGF X c' (condExpKernel μ m) (μ.trim hm)
  change Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm) at h
  refine ⟨h.integrable_exp_mul, ?_⟩
  filter_upwards [h.mgf_le] with ω hω t
  refine (hω t).trans (Real.exp_le_exp.mpr ?_)
  have hc : (c : ℝ) ≤ c' := hcc
  have ht : 0 ≤ t ^ 2 := sq_nonneg t
  nlinarith

/-- Scaling by a constant `r` multiplies the proxy by `r²`. -/
private theorem gridAsm_hasCondSubG_const_mul {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {hm : m ≤ mΩ} [StandardBorelSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasCondSubgaussianMGF m hm X c μ) (r : ℝ) :
    HasCondSubgaussianMGF m hm (fun ω => r * X ω) ((r ^ 2).toNNReal * c) μ := by
  change Kernel.HasSubgaussianMGF (fun ω => r * X ω) ((r ^ 2).toNNReal * c) (condExpKernel μ m)
    (μ.trim hm)
  change Kernel.HasSubgaussianMGF X c (condExpKernel μ m) (μ.trim hm) at h
  refine ⟨fun t => ?_, ?_⟩
  · simp_rw [← mul_assoc]
    exact h.integrable_exp_mul (t * r)
  · filter_upwards [h.mgf_le] with ω hω t
    rw [mgf_const_mul, mul_comm]
    refine (hω (t * r)).trans_eq ?_
    congr 1
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg r)]
    ring

/-- `𝒰` of a label-constant tensor `z` is `ρ_a · z` with `ρ_a = 𝒰(1)_a`. -/
private theorem gridAsm_Ugen_const (d L : ℕ) [NeZero L] (g E : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (v w : ℝ) (a : Fin k → Zd d L) (z : ℂ) :
    Ugen d L g E σ v w (fun _ => z) a = Ugen d L g E σ v w (fun _ => (1 : ℂ)) a * z := by
  unfold Ugen UN
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The witness satisfies `SubGaussStopN`** (proved, not assumed) at `τ ≡ K n`, for every
`m ≤ K n`, label `a`, signs `σ` and `j < m`, with the constant proxy `witProxy n`. -/
theorem gridAsm_witSubGaussStop (n : ℕ) (σ : Fin 3 → Bool) (m : ℕ) (hm : m ≤ gridAsm_K n)
    (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ) (hj : j < m) :
    SubGaussStopN sz0 (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n) (fun _ => gridAsm_K n)
      (fun j ω => gridAsm_witZvec n j ω) m a j (gridAsm_witProxy n) := by
  have hjK : j < gridAsm_K n := lt_of_lt_of_le hj hm
  have hu0 : ∀ i, 0 ≤ gridTime sInst tInst gridAsm_K n i := fun i =>
    gridAsm_gridTime_nonneg sInst tInst gridAsm_K n (by simp [sInst]) (gridAsm_sInst_le_tInst n) i
  have hu1 : ∀ i ≤ gridAsm_K n, gridTime sInst tInst gridAsm_K n i < 1 := fun i hi =>
    (gridAsm_gridTime_bounds n hi).2.trans_lt (by norm_num)
  have hum : gridTime sInst tInst gridAsm_K n m ≤ 1 / 16 := (gridAsm_gridTime_bounds n hm).2
  set ρ : ℂ := Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
    (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
    (fun _ => (1 : ℂ)) a with hρ
  -- `‖ρ‖ ≤ (31/15)^3`
  have hρn : ‖ρ‖ ≤ (31 / 15 : ℝ) ^ 3 := by
    have h1 := gridAsm_norm_Ugen_coarse 3 (sz0.L n) (sz0.lam n) (sz0.three_le_L n)
      (gridAsm_E_abs_lt n).le σ (hu0 (j + 1)) (hu1 (j + 1) (by omega)) (hu0 m) (hu1 m hm)
      (X := fun _ => (1 : ℂ)) (M := 1) zero_le_one (fun b => by simp) a
    have h2 : (1 - gridTime sInst tInst gridAsm_K n m)⁻¹ ≤ 16 / 15 := by
      have hpos : (15 : ℝ) / 16 ≤ 1 - gridTime sInst tInst gridAsm_K n m := by linarith
      calc (1 - gridTime sInst tInst gridAsm_K n m)⁻¹ ≤ ((15 : ℝ) / 16)⁻¹ :=
            inv_anti₀ (by norm_num) hpos
        _ = 16 / 15 := by norm_num
    have h3 : 0 ≤ (1 - gridTime sInst tInst gridAsm_K n m)⁻¹ :=
      inv_nonneg.mpr (by linarith [hu1 m hm])
    have h4 : (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 ≤ (31 / 15 : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 3
    calc ‖ρ‖ ≤ (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 * 1 := h1
      _ ≤ (31 / 15 : ℝ) ^ 3 := by rw [mul_one]; exact h4
  have hre2 : ρ.re ^ 2 ≤ 78 := by
    have h1 : |ρ.re| ≤ ‖ρ‖ := Complex.abs_re_le_norm ρ
    have h2 : |ρ.re| ≤ (31 / 15 : ℝ) ^ 3 := h1.trans hρn
    have h3 : |ρ.re| ^ 2 ≤ ((31 / 15 : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at h3
    refine h3.trans ?_
    norm_num
  have him2 : ρ.im ^ 2 ≤ 78 := by
    have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
    have h2 : |ρ.im| ≤ (31 / 15 : ℝ) ^ 3 := h1.trans hρn
    have h3 : |ρ.im| ^ 2 ≤ ((31 / 15 : ℝ) ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [sq_abs] at h3
    refine h3.trans ?_
    norm_num
  have hind : {ω' : PathΩ sz0 | j < (fun _ : PathΩ sz0 => gridAsm_K n) ω'} = Set.univ := by
    ext ω'; simp [hjK]
  have hUeq : ∀ ω' : PathΩ sz0, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
      (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
      (gridAsm_witZvec n j ω') a = ρ * ((gridAsm_witZ n j ω' : ℝ) : ℂ) := by
    intro ω'
    exact gridAsm_Ugen_const 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ _ _ a _
  have hC : ∀ r : ℝ, r ^ 2 ≤ 78 →
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => r * gridAsm_witZ n j ω) (gridAsm_witProxy n) (pathP sz0) := by
    intro r hr
    refine gridAsm_hasCondSubG_mono
      (gridAsm_hasCondSubG_const_mul (gridAsm_witZ_subG n j) r) ?_
    have hr' : (r ^ 2).toNNReal ≤ 78 := by
      rw [Real.toNNReal_le_iff_le_coe]
      simpa using hr
    calc (r ^ 2).toNNReal * gridAsm_witC0 n
        ≤ 78 * gridAsm_witC0 n := mul_le_mul_of_nonneg_right hr' zero_le
      _ ≤ gridAsm_witProxy n := le_self_add
  unfold SubGaussStopN SubGaussFormN
  simp only [hind, hUeq, Set.indicator_univ]
  refine ⟨?_, ?_⟩
  · have := hC ρ.re hre2
    convert this using 2
    simp
  · have := hC ρ.im him2
    convert this using 2
    simp

/-- **The Azuma tail (the mechanism of `stoppedAzumaZN`) for the witness**, all hypotheses proved:
`SubGaussStopN` is `gridAsm_witSubGaussStop`, the measurability is
`gridAsm_stronglyMeasurable_witZvec`, `τ ≡ K n`.  (The target `stoppedAzumaZN` is about `ZvecN`,
whose `SubGaussStopN` is ST2-34/35's output; here the same tail is checked with no hypothesis on a
genuinely random `Z`.) -/
theorem gridAsm_witAzuma (n : ℕ) (σ : Fin 3 → Bool) (m : ℕ) (hm : m ≤ gridAsm_K n)
    (a : Fin 3 → Zd 3 (sz0.L n)) (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (gridAsm_K n)),
        Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n (j + 1))
          (gridTime sInst tInst gridAsm_K n m) (gridAsm_witZvec n j ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ((m : ℝ) * (gridAsm_witProxy n : ℝ)))) := by
  have h := gridAsm_azuma_Ugen sz0 (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n)
    (τ := fun _ => gridAsm_K n) (fun j => MeasurableSet.const _) (Z := gridAsm_witZvec n) m
    (fun j _ => gridAsm_stronglyMeasurable_witZvec n j) a
    (fun _ => gridAsm_witProxy n)
    (fun j hj => gridAsm_witSubGaussStop n σ m hm a j hj) hx
  simpa using h

/-! ### The instance bundle with an arbitrary first-chaos increment -/

set_option linter.flexible false in
/-- The bundle `GridAssemblyHypN` at the instance data with an **arbitrary** first-chaos increment
`Z` (no field constrains `Z`): nonzero initial tensor `A_0 ≡ 1` (all labels), the trivial kernel
class, `κ_{im} = (1 + (1 - u_m)⁻¹)^3`, `εK = 0`, vanishing drift, second-order part and remainder,
and the process `A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j<m∧τ} 𝒰_{u_{j+1},u_m} Z_j` (so `hexp` holds by
definition).  The proxy `cc > 0` is constant, the moment levels `v, w ≥ 0` are free. -/
theorem gridAsm_bundle (n : ℕ) (σ : Fin 3 → Bool)
    (Z : ℕ → PathΩ sz0 → (Fin 3 → Zd 3 (sz0.L n)) → ℂ) (cc : ℝ≥0) (hcc : 0 < cc)
    (u : ℕ → ℝ) (E : ℝ) (hE : |E| ≤ 2) (hu0 : ∀ i ≤ gridAsm_K n, 0 ≤ u i)
    (hu1 : ∀ i ≤ gridAsm_K n, u i < 1) (τ : PathΩ sz0 → ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (v w : ℕ → ℝ) (hv : ∀ j, 0 ≤ v j) (hw : ∀ j, 0 ≤ w j) :
    GridAssemblyHypN sz0 (n := n) (k := 3) E σ u τ Δ (gridAsm_K n) (fun _ _ _ => True)
      (fun _ _ => 1)
      (fun m ω => Ugen 3 (sz0.L n) (sz0.lam n) E σ (u 0) (u m) (fun _ => (1 : ℂ)) +
        ∑ j ∈ Finset.range (min m (τ ω)),
          Ugen 3 (sz0.L n) (sz0.lam n) E σ (u (j + 1)) (u m) (Z j ω))
      (fun _ _ _ => 0) Z (fun _ _ _ => 0) (fun _ _ _ => 0)
      (fun _ m => (1 + (1 - u m)⁻¹) ^ 3) (fun _ _ => 0) 0 (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ _ => cc) v w (fun _ => 0) where
  hE := hE
  hu0 := hu0
  hu1 := hu1
  hΔ0 := hΔ
  hexp := fun m _ => Eventually.of_forall fun ω => by
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext b
    simp
  hκ0 := fun i m _ hm => by
    have h3 : 0 ≤ (1 - u m)⁻¹ := inv_nonneg.mpr (by linarith [hu1 m hm])
    positivity
  hε0 := fun _ _ _ _ => le_rfl
  hker := fun i m him hm X M δ hM hδ hX _ a => by
    have h := gridAsm_norm_Ugen_coarse 3 (sz0.L n) (sz0.lam n) (sz0.three_le_L n) hE σ
      (hu0 i (him.trans hm)) (hu1 i (him.trans hm)) (hu0 m hm) (hu1 m hm) hM hX a
    simpa using h
  hδ0 := le_rfl
  hA0cls := fun _ _ => trivial
  hdDrift0 := fun _ _ _ => le_rfl
  hδD0 := fun _ _ _ => le_rfl
  hdrift := fun _ _ _ _ b => by simp
  hDcls := fun _ _ _ _ => trivial
  hc_pos := fun m hm _ a => by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.2 hm) (NNReal.coe_pos.2 hcc)
  hv0 := fun j _ => hv j
  hw0 := fun j _ => hw j
  hY := by
    refine ⟨fun j => stronglyMeasurable_const, fun m _ b j _ => ?_⟩
    have h0 : ∀ ω, stoppedEdgeN sz0 E σ u (u m) τ (fun _ _ _ => (0 : ℂ)) b j ω = 0 := by
      intro ω; simp [stoppedEdgeN, Ugen, UN]
    simp only [h0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp
    all_goals first
      | exact Filter.Eventually.of_forall fun _ => rfl
      | exact Filter.Eventually.of_forall fun _ => le_rfl
      | exact Filter.Eventually.of_forall fun _ => hv j
      | exact hw j
  hstepErr0 := fun _ _ => le_rfl
  hR := Eventually.of_forall fun ω j _ _ b => by simp


/-! ### The instances of `assembledN` -/

/-- **`assembledN` at the instance data, with an arbitrary first-chaos increment `Z`**: `k = 3`,
any `ε > 0`, `D`, `D₁`, `C_P` with `D₁ + 4D + 3 + 2C_P + 8 ≤ C_K = 17`, the window `(0, 1/16)`, the
grid `K_n = N_n^{17}` with `τ ≡ K n`, `Δ = gridStep`, `P = 1` (`v = Δ²`, `w = Δ⁴`).  Given any
strongly measurable `Z` and a constant positive proxy `cc` for which `SubGaussStopN` holds (the
inputs `hZmeas`, `hsubG` of the pin), the theorem `assembledN` gives eventually in `n` an event `G`
of probability at least `1 - N^{-D₁}` on which, for every `m ≤ K n` and label `a`,
`‖(𝒰_{u_0,u_m} 1 + Σ_{j<m} 𝒰_{u_{j+1},u_m} Z_j)_a‖ ≤ κ_{0m} + N^ε (m cc)^{1/2} + N^{-D}`,
`κ_{0m} = (1 + (1 - u_m)⁻¹)^3`.  Discharged in the proof: `SizeTendsto` (`sz0_tendsto`), the grid
`1 ≤ K n ≤ ⌈N^{17}⌉`, `Δ ≤ N^{-17}`, `K n · Δ = 1/16 ≤ 1`, `P = 1 ≤ N^0`, the stopping-time
measurability and the bundle.  Not discharged here: the numeric exponent count `hCK`. -/
theorem gridAsm_assembledN_instance_gen (ε : ℝ) (hε : 0 < ε) (D D₁ C_P : ℝ)
    (hCK : D₁ + 4 * D + ((3 : ℕ) : ℝ) + 2 * C_P + 8 ≤ 17) (hCP : 0 ≤ C_P) :
    ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool)
      (Z : ℕ → PathΩ sz0 → (Fin 3 → Zd 3 (sz0.L n)) → ℂ) (cc : ℝ≥0), 0 < cc →
      (∀ j, StronglyMeasurable[filt sz0 (j + 1)] (Z j)) →
      (∀ m ≤ gridAsm_K n, ∀ (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ), j < m →
        SubGaussStopN sz0 (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n)
          (fun _ => gridAsm_K n) Z m a j cc) →
      ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
          ‖Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
              (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) a +
            ∑ j ∈ Finset.range m, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
              (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
              (Z j ω) a‖ ≤
            (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
              ((sz0.size n : ℕ) : ℝ) ^ ε * Real.sqrt (m * cc) +
              ((sz0.size n : ℕ) : ℝ) ^ (-D) := by
  filter_upwards [assembledN sz0 sz0_tendsto 3 ε hε D D₁ C_P 17 (by norm_num) hCK] with n hn
  intro σ Z cc hcc hZmeas hsub
  have hΔ0 : 0 ≤ gridStep sInst tInst gridAsm_K n := (gridAsm_step_pos n).le
  obtain ⟨hK1, hK, hΔ, hKΔ⟩ := gridAsm_grid_data n
  have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast gridAsm_size_pos n
  have hu0 : ∀ i ≤ gridAsm_K n, 0 ≤ gridTime sInst tInst gridAsm_K n i := fun i hi =>
    (gridAsm_gridTime_bounds n hi).1
  have hu1 : ∀ i ≤ gridAsm_K n, gridTime sInst tInst gridAsm_K n i < 1 := fun i hi =>
    (gridAsm_gridTime_bounds n hi).2.trans_lt (by norm_num)
  obtain ⟨G, hG, hb⟩ := hn (gridAsm_K n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n)
    (fun _ => gridAsm_K n) (gridStep sInst tInst gridAsm_K n) (fun _ _ _ => True)
    (fun _ _ => 1)
    (fun m ω => Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
        (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) +
      ∑ j ∈ Finset.range (min m ((fun _ : PathΩ sz0 => gridAsm_K n) ω)),
        Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n (j + 1))
          (gridTime sInst tInst gridAsm_K n m) (Z j ω))
    (fun _ _ _ => 0) Z (fun _ _ _ => 0) (fun _ _ _ => 0)
    (fun _ m => (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3) (fun _ _ => 0) 0
    (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => cc)
    (fun _ => gridStep sInst tInst gridAsm_K n ^ 2) (fun _ => gridStep sInst tInst gridAsm_K n ^ 4)
    (fun _ => 0) 1 hK1 hK hΔ (by rw [hKΔ]; norm_num) zero_le_one
    (Real.one_le_rpow hN1 hCP)
    (fun _ _ => by simp) (fun _ _ => by simp)
    (fun j => MeasurableSet.const _) hZmeas hsub
    (gridAsm_bundle n σ Z cc hcc (gridTime sInst tInst gridAsm_K n) (gridAsm_E n)
      (gridAsm_E_abs_lt n).le hu0 hu1 (fun _ => gridAsm_K n) _ hΔ0
      (fun _ => gridStep sInst tInst gridAsm_K n ^ 2) (fun _ => gridStep sInst tInst gridAsm_K n ^ 4)
      (fun _ => by positivity) (fun _ => by positivity))
  refine ⟨G, hG, fun ω hω m hm a => ?_⟩
  have := hb ω hω (gridAsm_K_pos n) m hm a
  simpa [min_eq_left hm] using this

/-- **Nondegenerate instance of `assembledN`** (all hypotheses discharged, no unproved pin): the
witness `Z_j = √Δ · Re tr X_{j+1}` (a genuinely random Gaussian increment, see
`gridAsm_witZ_ne_zero`), with `SubGaussStopN` proved (`gridAsm_witSubGaussStop`), `d = 3`, `sz0`,
`k = 3`, `σ = (+,+,-)`, `E ≡ 1/2`, `ε = 1`, `D = D₁ = 1`, `C_P = 0`, `C_K = 17` (exponent count
`1 + 4 + 3 + 0 + 8 = 16 ≤ 17`), the window `(0, 1/16)` and the grid `K_n = N_n^{17}`.  Eventually in
`n`, on an event of probability at least `1 - N^{-1}`, for every `m ≤ K n` and label `a`,
`‖(𝒰_{u_0,u_m} 1 + Σ_{j<m} 𝒰_{u_{j+1},u_m} Z_j)_a‖ ≤ κ_{0m} + N (m · proxy)^{1/2} + N^{-1}`. -/
theorem gridAsm_assembledN_instance_random :
    ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz0),
      (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
      ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
        ‖Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) ![true, true, false]
            (gridTime sInst tInst gridAsm_K n 0) (gridTime sInst tInst gridAsm_K n m)
            (fun _ => (1 : ℂ)) a +
          ∑ j ∈ Finset.range m, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) ![true, true, false]
            (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
            (gridAsm_witZvec n j ω) a‖ ≤
          (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * Real.sqrt (m * gridAsm_witProxy n) +
            ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [gridAsm_assembledN_instance_gen 1 one_pos 1 1 0 (by norm_num) le_rfl] with n hn
  exact hn ![true, true, false] (gridAsm_witZvec n) (gridAsm_witProxy n)
    (gridAsm_witProxy_pos n) (fun j => gridAsm_stronglyMeasurable_witZvec n j)
    (fun m hm a j hj => gridAsm_witSubGaussStop n _ m hm a j hj)

/-- `Re tr` of the standard basis matrix of the diagonal coordinate `⟨n, (0,0,true)⟩` is `1` (as
in the proof of `markov_linTrVar_one_pos`, `Path/Markov.lean:694`). -/
private theorem gridAsm_linTr_one_single {d : ℕ} (sz : Sizes d) (n : ℕ) :
    linTr n (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Sizes.seqXmat sz n (Pi.single (⟨n, (0, 0, true)⟩ : Sizes.SeqCoord sz) 1)) = 1 := by
  classical
  set c0 : Sizes.SeqCoord sz := ⟨n, (0, 0, true)⟩ with hc0
  unfold linTr
  rw [Matrix.one_mul, Matrix.trace, Complex.re_sum]
  have hdiag : ∀ j : Idx d (sz.L n) (sz.W n),
      (Matrix.diag (Sizes.seqXmat sz n (Pi.single c0 1)) j).re = if j = 0 then 1 else 0 := by
    intro j
    simp only [Matrix.diag_apply]
    change (Xentry d (sz.L n) (sz.W n) (Sizes.slice sz n (Pi.single c0 1)) j j).re = _
    unfold Xentry
    simp only [lt_self_iff_false, ite_false, Sizes.slice]
    by_cases hj : j = 0
    · subst hj; simp [hc0]
    · have hne : (⟨n, (j, j, true)⟩ : Sizes.SeqCoord sz) ≠ c0 := by
        intro h
        apply hj
        rw [hc0] at h
        simp only [Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and, and_true] at h
        exact h.1
      simp [hne, hj]
  rw [Finset.sum_congr rfl fun j _ => hdiag j]
  simp

/-- **The witness is genuinely random**: `Z_j` vanishes at `ω = 0` and equals `√Δ ≠ 0` at the draw
`ω_{j+1} = e_{⟨n,(0,0,true)⟩}` (so it is neither identically zero nor constant). -/
theorem gridAsm_witZ_ne_zero (n j : ℕ) :
    ∃ ω : PathΩ sz0, gridAsm_witZ n j ω ≠ 0 := by
  classical
  refine ⟨fun i => if i = j + 1 then Pi.single (⟨n, (0, 0, true)⟩ : Sizes.SeqCoord sz0) 1 else 0,
    ?_⟩
  unfold gridAsm_witZ
  simp only [ite_true]
  rw [gridAsm_linTr_one_single sz0 n, mul_one]
  exact (Real.sqrt_pos.2 (gridAsm_step_pos n)).ne'

theorem gridAsm_witZ_zero (n j : ℕ) :
    gridAsm_witZ n j (fun _ => 0) = 0 := by
  unfold gridAsm_witZ
  have h : Sizes.seqXmat sz0 n (0 : Sizes.SeqΩ sz0) = 0 := by
    have h := Xmat_smul 3 (sz0.L n) (sz0.W n) 0 (0 : CoordF 3 (sz0.L n) (sz0.W n) → ℝ)
    simp only [zero_smul] at h
    exact h
  change Real.sqrt (gridStep sInst tInst gridAsm_K n) * linTr (sz := sz0) n 1
    (Sizes.seqXmat sz0 n 0) = 0
  rw [h]
  simp [linTr]

/-- **The process of the random instance is genuinely random**: at `m = 1` the quantity bounded in
`gridAsm_assembledN_instance_random` takes different values at `ω = 0` and at the draw
`ω_1 = e_{⟨n,(0,0,true)⟩}` (`𝒰_{u_1,u_1} = id`, and `Z_0` is `0` resp. `√Δ ≠ 0`). -/
theorem gridAsm_witA_ne (n : ℕ) (σ : Fin 3 → Bool) (a : Fin 3 → Zd 3 (sz0.L n)) :
    ∃ ω ω' : PathΩ sz0,
      Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
          (gridTime sInst tInst gridAsm_K n 1) (fun _ => (1 : ℂ)) a +
        ∑ j ∈ Finset.range 1, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
          (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n 1)
          (gridAsm_witZvec n j ω) a ≠
      Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
          (gridTime sInst tInst gridAsm_K n 1) (fun _ => (1 : ℂ)) a +
        ∑ j ∈ Finset.range 1, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
          (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n 1)
          (gridAsm_witZvec n j ω') a := by
  obtain ⟨ω, hω⟩ := gridAsm_witZ_ne_zero n 0
  refine ⟨ω, fun _ => 0, ?_⟩
  have hK1 : 1 ≤ gridAsm_K n := gridAsm_K_pos n
  have hbd := gridAsm_gridTime_bounds n hK1
  have hself : ∀ ω'' : PathΩ sz0, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
      (gridTime sInst tInst gridAsm_K n (0 + 1)) (gridTime sInst tInst gridAsm_K n 1)
      (gridAsm_witZvec n 0 ω'') a = ((gridAsm_witZ n 0 ω'' : ℝ) : ℂ) := by
    intro ω''
    have h := GridDuhamelN_Ugen_self (d := 3) (L := sz0.L n) (g := sz0.lam n)
      (sz0.three_le_L n) (gridAsm_E_abs_lt n).le σ
      (v := gridTime sInst tInst gridAsm_K n 1) hbd.1 (hbd.2.trans_lt (by norm_num))
      (gridAsm_witZvec n 0 ω'')
    simpa [gridAsm_witZvec] using congrFun h a
  intro h
  rw [Finset.sum_range_one, Finset.sum_range_one, hself, hself, gridAsm_witZ_zero] at h
  have h' := add_left_cancel h
  exact hω (by exact_mod_cast h')

/-- **Instance of `assembledN` with `Z = ZvecN`** (the paper's first-chaos part, `hZmeas` from
`gridAsm_stronglyMeasurable_ZvecN`, unconditional) at the same data, `ε = 1/100`, `D = D₁ = 1`,
`C_P = 0`: the sub-Gaussian family `SubGaussStopN` for `ZvecN` (`AzumaSubGN`'s output, ST2-34/35)
stays a hypothesis, at an arbitrary constant proxy `cc > 0`. -/
theorem gridAsm_assembledN_instance_zvec :
    ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 3 → Bool) (cc : ℝ≥0), 0 < cc →
      (∀ m ≤ gridAsm_K n, ∀ (a : Fin 3 → Zd 3 (sz0.L n)) (j : ℕ), j < m →
        SubGaussStopN sz0 (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n)
          (fun _ => gridAsm_K n) (fun j ω => ZvecN sz0 gridAsm_E sInst tInst gridAsm_K n j σ ω)
          m a j cc) →
      ∃ G : Set (PathΩ sz0), (pathP sz0).real Gᶜ ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G, ∀ m ≤ gridAsm_K n, ∀ a : Fin 3 → Zd 3 (sz0.L n),
          ‖Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ (gridTime sInst tInst gridAsm_K n 0)
              (gridTime sInst tInst gridAsm_K n m) (fun _ => (1 : ℂ)) a +
            ∑ j ∈ Finset.range m, Ugen 3 (sz0.L n) (sz0.lam n) (gridAsm_E n) σ
              (gridTime sInst tInst gridAsm_K n (j + 1)) (gridTime sInst tInst gridAsm_K n m)
              (ZvecN sz0 gridAsm_E sInst tInst gridAsm_K n j σ ω) a‖ ≤
            (1 + (1 - gridTime sInst tInst gridAsm_K n m)⁻¹) ^ 3 +
              ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * Real.sqrt (m * cc) +
              ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  filter_upwards [gridAsm_assembledN_instance_gen (1 / 100) (by norm_num) 1 1 0 (by norm_num)
    le_rfl] with n hn
  intro σ cc hcc hsub
  exact hn σ (fun j ω => ZvecN sz0 gridAsm_E sInst tInst gridAsm_K n j σ ω) cc hcc
    (fun j => gridAsm_stronglyMeasurable_ZvecN sz0 gridAsm_E sInst tInst gridAsm_K n j σ) hsub

end GridAssemblyNInst

/-! ## 12. Statement checks

The bodies of the anonymous `example`s below are the pins (`StoppedAzumaZN`, `AssembledN`); they
compile only if the theorems have exactly these types. -/

section StatementChecks

variable {d : ℕ} (sz : Sizes d)

example : ∀ (E s t : ℕ → ℝ) (K : ℕ → ℕ), StoppedAzumaZN sz E s t K := stoppedAzumaZN sz

example : AssembledN sz := assembledN sz

/-- The theorems at `d = 3`, `sz0` (the same statements as the pins at the merged sequence). -/
example : AssembledN RBM.Gauss.SizesInst.sz0 := assembledN _

end StatementChecks

end RBM.Ind

end

#print axioms RBM.Ind.stoppedAzumaZN
#print axioms RBM.Ind.assembledN
#print axioms RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#print axioms RBM.Ind.gridAsm_stronglyMeasurable_YvecN
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_bound_lt_one
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_stoppedAzumaZN_instance_concrete
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_grid_data
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_witSubGaussStop
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_witAzuma
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_bundle
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_gen
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_random
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_witZ_ne_zero
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_witZ_zero
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_witA_ne
#print axioms RBM.Ind.GridAssemblyNInst.gridAsm_assembledN_instance_zvec
