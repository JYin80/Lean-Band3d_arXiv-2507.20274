/-
Release check for T2251 (dispatcher V1, Tue Oct  6 03:21 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B).
UN-19: the deterministic spectral layer of `(jaklsdufowe)` (the `y`-term of the pin `UNJak`): port of RBM2D
`Universality/JakSpectral.lean` (c9a24cf, 720 lines; `spectralPole` `:57`, `spectralGsigPole` `:62`,
`green_sq_apply_self` `:78`, `Gsig_apply_self_spectral` `:110`, `Gsig_sq_apply_self_spectral` `:122`,
`spectralGsigPole_norm_eq_spectralPole` `:132`, `isOrthoEigenbasis_eigenvectorBasis` `:146`, `siteBlock` `:180`,
`blockM` `:185`, `blockM_eq` `:226`, `green_spectral_identity_blockM` `:322`,
`norm_green_spectral_identity_blockM_le` `:339`, `sum_norm_blockM_le` `:490`, `measure_bad_le_of_queBadMat` `:537`)
to `Idx d L W`, `svarF d L W lam` (through the merged `scirc`), `N = (W L)^d`, `Gres` (the resolvent of the merged
pins) and the `2d + 1` weights `SBR d L lam` of `S^(B)` (RBM2D: five equal weights `1/5`); new file
`RBM3D/Universality/JakSpectral.lean`.  Deterministic, plus one union bound that is a corollary of the merged
`unBadY_measure_le`: no pin is proved, stated or registered.  The prime is the ASCII `'` of `main` (no primed name
occurs here).
Section 1: the merged names the new file builds on (and the Mathlib names of the RBM2D route).
Section 2: the new vocabulary (2.1, bodies copied verbatim into namespace `RBM.Univ`), the statements of the
theorems of T2251 as `def T2251_<name> : Prop` (2.2-2.6) and the instances (2.7); the library states the theorem
`<name>` (namespace `RBM.Univ`, instances in `RBM.Univ.JakSpectralInst` with `T2251_H1`, `T2251_y0`, `T2251_a0`
renamed `H1`, `y0`, `a0`) with exactly this body (binder names may be added; `Type*` for the check's `Type`).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2251-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Star.Unitary

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.IsOrthoEigenbasis    -- :53 (same body as RBM2D `RBM.Endpoints.IsOrthoEigenbasis`, `Endpoints.lean:56`)
#check @RBM.Univ.ouMat                -- :150
#check @RBM.Univ.ouMat_isHermitian    -- :154
#check @RBM.Univ.queBadMat            -- :392 (overlap `∑ x ∈ Iblk d L W a, star (ψ i x) * ψ j x`)
#check @RBM.Univ.InWindow             -- :501 (`N^{-1-τ_U} ≤ Im z`: positive imaginary part)
#check @RBM.Univ.scirc                -- :612 (`svarF d L W lam - ((W L)^d)⁻¹`, in `ℂ`; RBM2D `Scirc`)
#check @RBM.Univ.UNJak                -- :694 (integrand `(Gres M z b₁ * Gres M z b₁) x x * scirc … x y * Gres M z b₂ y y`)
#check @RBM.Univ.UNUyw                -- :708
#check @RBM.Univ.UNJakUywRow          -- :805 (owed; stays owed: UN-21, UN-23)
#check @RBM.Univ.un_window_sub        -- :908
#check @RBM.Univ.unMy                 -- :1140 (`M_{y,α}` of a vector, real)
#check @RBM.Univ.UNBadY               -- :1147 (window `N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`)
#check @RBM.Univ.unMy_eq              -- :1156 (the `SBR`-weighted block average, `3 ≤ L`, unit vector)
#check @RBM.Univ.unBadY_subset        -- :1205
#check @RBM.Univ.unBadY_card_le       -- :1298 (`≤ 2d + 1` blocks)
#check @RBM.Univ.unBadY_measure_le    -- :1320 (`ℙ(𝓑(y)) ≤ (2d+1) p`)
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0): the model-generic pin (same integrand at `lam = K.lamV sz n`)
#check @RBM.Univ.UNJakk               -- :365
-- the fine lattice, blocks and the variance profile (namespace `RBM.Gauss`; `Zd`, `SBR`, `sbKernelR` in `RBM`)
#check @RBM.Zd                        -- `Defs/Lattice.lean:63` (51f1a17; `Fin d → ZMod L`)
#check @RBM.Gauss.Vtx                 -- `Gauss/Model.lean:60` (a722f63; `Zd d L × Fin (W ^ d)`)
#check @RBM.Gauss.Idx                 -- `Defs/Sizes.lean:46` (0a873f1; `Zd d (W * L)`)
#check @RBM.Gauss.split               -- `Defs/Sizes.lean:64` (block label `.1`, offset `.2`)
#check @RBM.Gauss.split_bijective     -- `Defs/Sizes.lean:79` (a site in every block: `sum_norm_blockM_le`)
#check @RBM.Gauss.Iblk                -- `Defs/Sizes.lean:92` (`univ.filter (split · ).1 = a`)
#check @RBM.Gauss.card_Iblk           -- `Defs/Sizes.lean:95` (`W ^ d`)
#check @RBM.Gauss.card_Idx            -- `Defs/Sizes.lean:107` (`(W * L) ^ d`; replaces RBM2D `JakSpectral_card_idx` `:424`)
#check @RBM.Gauss.Sizes.neZeroL       -- `Defs/Sizes.lean:152` (instance)
#check @RBM.Gauss.Sizes.neZeroW       -- `Defs/Sizes.lean:153` (instance)
#check @RBM.Gauss.svarF               -- `Gauss/FineModel.lean:47` (0a873f1; `W^{-d} SBR d L lam (split x).1 (split y).1`)
#check @RBM.Gauss.svarF_nonneg        -- `Gauss/FineModel.lean:51`
#check @RBM.Gauss.svarF_comm          -- `Gauss/FineModel.lean:54`
#check @RBM.SBR                       -- `Propagator/Props4.lean:48` (892334b)
#check @RBM.sum_SBR_row               -- `Propagator/Gap.lean:206` (24cf61d; `3 ≤ L`)
#check @RBM.SBR_comm                  -- `Propagator/Gap.lean:230`
#check @RBM.sbKernelR                 -- `Defs/Block.lean:74` (a722f63)
#check @RBM.sbKernelR_nonneg          -- `Defs/Block.lean:88` (every `lam`)
-- resolvents
#check @RBM.Gauss.Gres                -- `Loop/GLoopFlow.lean:74` (868b3b4; `Ring.inverse (H - z_σ • 1)`; RBM2D `Gsig`)
#check @RBM.isUnit_sub_smul_of_isHermitian   -- `Analysis/Resolvent.lean:132` (6f9e0ba; in the import closure of `Pins`)
-- templates only (not imported by the new file)
#check @RBM.Endpoints.Gres_apply_self -- `Main/FixedZ.lean:552` (0d5868e; `Gres H z true x x` through an `IsOrthoEigenbasis`)
#check @RBM.Ind.Gres_eq_green_zSig    -- `Induction/ConArgDet.lean:367` (bbd22a5; `Gres H z s = green H (zSig z s)`)
-- Mathlib (same Mathlib revision as RBM2D c9a24cf: lake-manifest rev 5ed2965…)
#check @Matrix.IsHermitian.eigenvalues            -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.eigenvectorBasis       -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.eigenvectorUnitary_apply  -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.spectral_theorem       -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.mulVec_eigenvectorBasis  -- Mathlib.Analysis.Matrix.Spectrum
#check @orthonormal_iff_ite                       -- Mathlib.Analysis.InnerProductSpace.Orthonormal
#check @MeasureTheory.measure_biUnion_finset_le   -- Mathlib.MeasureTheory.OuterMeasure.Basic
#check @Matrix.nonsing_inv_eq_ringInverse         -- Mathlib.LinearAlgebra.Matrix.NonsingularInverse
#check @Matrix.inv_eq_right_inv                   -- Mathlib.LinearAlgebra.Matrix.NonsingularInverse
#check @Matrix.isHermitian_one                    -- Mathlib.LinearAlgebra.Matrix.Hermitian
#check @Unitary.coe_star_mul_self                 -- Mathlib.Algebra.Star.Unitary

namespace RBM.Univ.T2251Check

open Matrix
open RBM.Gauss
open scoped ENNReal NNReal

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvalue coefficient of the resolvent with spectral parameter `w` (RBM2D `:57`, verbatim). -/
noncomputable def spectralPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (w : ℂ) (α : n) : ℂ :=
  ((hH.eigenvalues α : ℂ) - w)⁻¹

/-- The eigenvalue coefficient of `Gres H z σ`: the sign `σ = false` uses `z̄` (RBM2D `:62`, verbatim; the
spectral parameter is the one of the merged `Gres`, `Loop/GLoopFlow.lean:74`). -/
noncomputable def spectralGsigPole {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (α : n) : ℂ :=
  spectralPole hH (if σ then z else (starRingEnd ℂ) z) α

end Generic

section Block

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The block `a ∈ Z_L^d` of a site `y` (RBM2D `:180`; `Z2 L` ↦ `Zd d L`). -/
def siteBlock (y : Idx d L W) : Zd d L := (split d L W y).1

/-- `M_{y,α}` for `y ∈ [a₀]`, `d ≥ 3` form: the `S^{(B)}(lam)`-weighted average (weights `SBR d L lam b a₀`, sum `1`,
support `≤ 2d + 1` blocks) of the block QUE quantities `(N/W^d) ∑_{x∈[b]} |ψ_α(x)|² - 1`, written with the overlap of
the merged `queBadMat` (`Pins.lean:392`).  RBM2D `:185` is the equal-weight `1/5` average over `a₀ + sbSupport L`;
`blockM_eq` identifies it with `N ∑_x |ψ_α(x)|² S°_{xy}`, `blockM_eq_unMy` with the merged `unMy`. -/
noncomputable def blockM (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian)
    (a0 : Zd d L) (α : Idx d L W) : ℂ :=
  ∑ b : Zd d L, ((SBR d L lam b a0 : ℝ) : ℂ) *
    ((((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
        (∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis α x) * hH.eigenvectorBasis α x) - 1)

end Block

/-! ### 2.2 Target 1: the eigenbasis expansion of the resolvent (RBM2D `:51-171`; any finite index type) -/

/-- `Gres_sq_apply_self` (RBM2D `green_sq_apply_self` `:78`; `green H w ^ 2` ↦ `Gres H w true * Gres H w true`, the
form of the pins; target 1a). -/
def T2251_Gres_sq_apply_self : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {w : ℂ},
    (∀ α, (hH.eigenvalues α : ℂ) ≠ w) → ∀ x : n,
      (Gres H w true * Gres H w true) x x =
        ∑ α, spectralPole hH w α * spectralPole hH w α *
          (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)

/-- `Gres_apply_self_spectral` (RBM2D `Gsig_apply_self_spectral` `:110`; `Gsig` ↦ `Gres`; target 1b). -/
def T2251_Gres_apply_self_spectral : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ},
    0 < z.im → ∀ (σ : Bool) (y : n),
      Gres H z σ y y =
        ∑ β, spectralGsigPole hH z σ β * (Complex.normSq (hH.eigenvectorBasis β y) : ℂ)

/-- `Gres_sq_apply_self_spectral` (RBM2D `Gsig_sq_apply_self_spectral` `:122`; `Gsig H z σ ^ 2` ↦
`Gres H z σ * Gres H z σ`; target 1c). -/
def T2251_Gres_sq_apply_self_spectral : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ},
    0 < z.im → ∀ (σ : Bool) (x : n),
      (Gres H z σ * Gres H z σ) x x =
        ∑ α, spectralGsigPole hH z σ α * spectralGsigPole hH z σ α *
          (Complex.normSq (hH.eigenvectorBasis α x) : ℂ)

/-- `spectralGsigPole_norm_eq_spectralPole` (RBM2D `:132`, verbatim; target 1d). -/
def T2251_spectralGsigPole_norm_eq_spectralPole : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) (z : ℂ) (σ : Bool) (α : n),
    ‖spectralGsigPole hH z σ α‖ = ‖spectralPole hH z α‖

/-- `isOrthoEigenbasis_eigenvectorBasis` (RBM2D `:146`; `RBM.Endpoints.IsOrthoEigenbasis` ↦ the merged
`RBM.Univ.IsOrthoEigenbasis`, same body; target 1e). -/
def T2251_isOrthoEigenbasis_eigenvectorBasis : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian),
    RBM.Univ.IsOrthoEigenbasis H hH.eigenvalues (fun k x => hH.eigenvectorBasis k x)

/-! ### 2.3 Target 2: the block quantity `M_{y,α}` with the `2d + 1` weights (RBM2D `:175-256`) -/

/-- `blockM_eq` (RBM2D `:226`; `Scirc L W` ↦ `scirc d L W lam`, `(W L)^2` ↦ `(W L)^d`; target 2a). -/
def T2251_blockM_eq : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y α : Idx d L W),
      blockM d L W lam hH (siteBlock d L W y) α =
        (((W * L) ^ d : ℕ) : ℂ) *
          ∑ x, ((‖hH.eigenvectorBasis α x‖ ^ 2 : ℝ) : ℂ) * RBM.Univ.scirc d L W lam x y

/-- `blockM_eq_unMy` (new: the bridge to the merged `unMy`, `Pins.lean:1140`, of the merged bad event `UNBadY`;
target 2b). -/
def T2251_blockM_eq_unMy : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y α : Idx d L W),
      blockM d L W lam hH (siteBlock d L W y) α =
        ((RBM.Univ.unMy d L W lam (fun x => hH.eigenvectorBasis α x) y : ℝ) : ℂ)

/-! ### 2.4 Target 3: the exact spectral expansion of the `y`-term of `UNJak` (RBM2D `:260-416`) -/

/-- `green_spectral_identity_blockM` (RBM2D `:322`; `Gsig Hm z σ₁ ^ 2` ↦ `Gres Hm z σ₁ * Gres Hm z σ₁`, the integrand
of `UNJak`, `Pins.lean:700-703`, token for token; target 3a). -/
def T2251_green_spectral_identity_blockM : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : Hm.IsHermitian) (y : Idx d L W) {z : ℂ}, 0 < z.im → ∀ σ₁ σ₂ : Bool,
      (∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * RBM.Univ.scirc d L W lam x y *
          Gres Hm z σ₂ y y) =
        ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ γ : Idx d L W,
          spectralGsigPole hH z σ₁ α * spectralGsigPole hH z σ₁ α *
            spectralGsigPole hH z σ₂ γ * blockM d L W lam hH (siteBlock d L W y) α *
            (Complex.normSq (hH.eigenvectorBasis γ y) : ℂ)

/-- `norm_green_spectral_identity_blockM_le` (RBM2D `:339`; target 3b). -/
def T2251_norm_green_spectral_identity_blockM_le : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {Hm : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : Hm.IsHermitian) (y : Idx d L W) {z : ℂ}, 0 < z.im → ∀ σ₁ σ₂ : Bool,
      ‖∑ x : Idx d L W, (Gres Hm z σ₁ * Gres Hm z σ₁) x x * RBM.Univ.scirc d L W lam x y *
          Gres Hm z σ₂ y y‖ ≤
        ((((W * L) ^ d : ℕ) : ℝ))⁻¹ *
          (∑ α : Idx d L W, ‖spectralGsigPole hH z σ₁ α‖ ^ 2 *
            ‖blockM d L W lam hH (siteBlock d L W y) α‖) *
          (∑ γ : Idx d L W, ‖spectralGsigPole hH z σ₂ γ‖ *
            Complex.normSq (hH.eigenvectorBasis γ y))

/-! ### 2.5 Target 4: the mass bound `∑_α |M_{a₀,α}| ≤ 2N` (RBM2D `:420-522`) -/

/-- `sum_norm_blockM_le` (RBM2D `:490`; column sum `∑_x S_{xy} = 1` from `card_Iblk`, `sum_SBR_row`, `SBR_comm`;
`|S°_{xy}| ≤ S_{xy} + N⁻¹` from `svarF_nonneg`; target 4). -/
def T2251_sum_norm_blockM_le : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (a0 : Zd d L),
      ∑ α : Idx d L W, ‖blockM d L W lam hH a0 α‖ ≤ 2 * (((W * L) ^ d : ℕ) : ℝ)

/-! ### 2.6 Target 5: the bad event through the merged `UNBadY` and `unBadY_measure_le` (RBM2D `:526-589`) -/

/-- `unBadY_of_blockM` (new: the eigenbasis event of RBM2D `measure_bad_le_of_queBadMat` at the window and threshold
of the merged `UNBadY`, `Pins.lean:1147`, is contained in `UNBadY`; target 5a). -/
def T2251_unBadY_of_blockM : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ {lam 𝔡 E : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : M.IsHermitian) (y α : Idx d L W),
      |hH.eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) →
      (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam hH (siteBlock d L W y) α‖ →
        RBM.Univ.UNBadY d L W lam 𝔡 E y M

/-- `measure_bad_le_of_queBadMat` (RBM2D `:537`, restated at the `d ≥ 3` data: the merged `queBadMat` at
`(ε₀, c) = (𝔡/3, 𝔡/6)` (`1_2:575-577`), `2d + 1` blocks instead of `5`; a corollary of `unBadY_of_blockM` and the
merged `unBadY_measure_le`, `Pins.lean:1320`, with the same hypotheses; target 5b). -/
def T2251_measure_bad_le_of_queBadMat : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {Ω : Type} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω),
    3 ≤ L → ∀ {lam 𝔡 E : ℝ}, 1 ≤ (W : ℝ) → 0 < 𝔡 → (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam →
      ∀ (y : Idx d L W) {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian)
        (p : ℝ≥0∞),
        (∀ b : Zd d L, P {ω | RBM.Univ.queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) →
          P {ω | ∃ α, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
              (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM d L W lam (hH ω) (siteBlock d L W y) α‖} ≤
            ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

/-! ### 2.7 Target 6: instances (namespace `RBM.Univ.JakSpectralInst`; `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`lam = 1/2` (`lam = 1` in the measure instance), `H = 1`, `y = 0`, `a₀ = 0`, `z = I`, `σ₁ = true`, `σ₂ = false`;
the Hermitian witness is quantified (`∀ hH`), the library instances take `Matrix.isHermitian_one`) -/

/-- The data (the library defines `JakSpectralInst.H1`, `y0`, `a0` with these bodies). -/
noncomputable abbrev T2251_H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def T2251_y0 : Idx 3 3 2 := 0

def T2251_a0 : Zd 3 3 := 0

/-- `inst_spectral` (targets 1a-1e at the data; RBM2D `:607-631`). -/
def T2251_inst_spectral : Prop :=
  ∀ hH : T2251_H1.IsHermitian,
    (Gres T2251_H1 Complex.I true * Gres T2251_H1 Complex.I true) T2251_y0 T2251_y0 =
        ∑ α, spectralPole hH Complex.I α * spectralPole hH Complex.I α *
          (Complex.normSq (hH.eigenvectorBasis α T2251_y0) : ℂ) ∧
      Gres T2251_H1 Complex.I false T2251_y0 T2251_y0 =
        ∑ β, spectralGsigPole hH Complex.I false β *
          (Complex.normSq (hH.eigenvectorBasis β T2251_y0) : ℂ) ∧
      (Gres T2251_H1 Complex.I false * Gres T2251_H1 Complex.I false) T2251_y0 T2251_y0 =
        ∑ α, spectralGsigPole hH Complex.I false α * spectralGsigPole hH Complex.I false α *
          (Complex.normSq (hH.eigenvectorBasis α T2251_y0) : ℂ) ∧
      ‖spectralGsigPole hH Complex.I false T2251_y0‖ = ‖spectralPole hH Complex.I T2251_y0‖ ∧
      RBM.Univ.IsOrthoEigenbasis T2251_H1 hH.eigenvalues (fun k x => hH.eigenvectorBasis k x)

/-- `inst_block` (targets 2a, 2b at `lam = 1/2`; RBM2D `:633`). -/
def T2251_inst_block : Prop :=
  ∀ hH : T2251_H1.IsHermitian,
    blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 T2251_y0) T2251_y0 =
        (((2 * 3) ^ 3 : ℕ) : ℂ) *
          ∑ x, ((‖hH.eigenvectorBasis T2251_y0 x‖ ^ 2 : ℝ) : ℂ) * RBM.Univ.scirc 3 3 2 (1 / 2) x T2251_y0 ∧
      blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 T2251_y0) T2251_y0 =
        ((RBM.Univ.unMy 3 3 2 (1 / 2) (fun x => hH.eigenvectorBasis T2251_y0 x) T2251_y0 : ℝ) : ℂ)

/-- `inst_identity` (targets 3a, 3b at `z = I`, `σ₁ = true`, `σ₂ = false`; RBM2D `:639-660`). -/
def T2251_inst_identity : Prop :=
  ∀ hH : T2251_H1.IsHermitian,
    (∑ x, (Gres T2251_H1 Complex.I true * Gres T2251_H1 Complex.I true) x x *
          RBM.Univ.scirc 3 3 2 (1 / 2) x T2251_y0 * Gres T2251_H1 Complex.I false T2251_y0 T2251_y0) =
        ((((2 * 3) ^ 3 : ℕ) : ℂ))⁻¹ * ∑ α, ∑ γ,
          spectralGsigPole hH Complex.I true α * spectralGsigPole hH Complex.I true α *
            spectralGsigPole hH Complex.I false γ *
            blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 T2251_y0) α *
            (Complex.normSq (hH.eigenvectorBasis γ T2251_y0) : ℂ) ∧
      ‖∑ x, (Gres T2251_H1 Complex.I true * Gres T2251_H1 Complex.I true) x x *
          RBM.Univ.scirc 3 3 2 (1 / 2) x T2251_y0 * Gres T2251_H1 Complex.I false T2251_y0 T2251_y0‖ ≤
        ((((2 * 3) ^ 3 : ℕ) : ℝ))⁻¹ *
          (∑ α, ‖spectralGsigPole hH Complex.I true α‖ ^ 2 *
            ‖blockM 3 3 2 (1 / 2) hH (siteBlock 3 3 2 T2251_y0) α‖) *
          (∑ γ, ‖spectralGsigPole hH Complex.I false γ‖ *
            Complex.normSq (hH.eigenvectorBasis γ T2251_y0))

/-- `inst_mass` (target 4 at `a₀ = 0`; RBM2D `:661`). -/
def T2251_inst_mass : Prop :=
  ∀ hH : T2251_H1.IsHermitian,
    ∑ α, ‖blockM 3 3 2 (1 / 2) hH T2251_a0 α‖ ≤ 2 * (((2 * 3) ^ 3 : ℕ) : ℝ)

/-- `inst_bad` (target 5b at `Ω = Unit`, `P = δ_()`, `Hr ≡ 1`, `lam = 1`, `𝔡 = 1/10`, `E = 1`, `p = 1`; every
hypothesis of `measure_bad_le_of_queBadMat` discharged: `3 ≤ 3`, `1 ≤ 2`, `0 < 1/10`,
`2^{-3/2 + 1/10} ≤ 1`, `δ(·) ≤ 1`; RBM2D `:667-679`). -/
def T2251_inst_bad : Prop :=
  ∀ hH : ∀ _ω : Unit, T2251_H1.IsHermitian,
    (MeasureTheory.Measure.dirac ()) {ω : Unit | ∃ α, |(hH ω).eigenvalues α - 1| ≤
        (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
      ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM 3 3 2 1 (hH ω) (siteBlock 3 3 2 T2251_y0) α‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1

/-! ## 3. Downstream shapes (not targets of T2251; information) -/

-- the owed pins this file serves (all stay owed; `Test/Axioms.lean:205, 206, 213, 225, 226, 231, 241` on b35643d)
#check @RBM.Univ.UNJak                -- Pins.lean:694 (UN-21: the split on `UNBadY`; target 3b bounds the integrand)
#check @RBM.Univ.UNUyw                -- Pins.lean:708 (UN-22/UN-23: the pair kernel; RBM2D `UywKernel` uses targets 1, 3a)
#check @RBM.Univ.UNJakUywRow          -- Pins.lean:805
#check @RBM.Univ.UNJakk               -- PinsK.lean:365 (model-generic: `lam = K.lamV sz n`)

-- consumer shape (UN-21, token check of preflight (i)): the `UNJak` integrand at the band data is the left side of
-- target 3b at `Hm = ouMat (UNModel.band sz) n t ω`, `lam = sz.lam n`, `z = z i` (`0 < Im z` from `InWindow`)
example : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (t : ℝ)
    (ω : RBM.Gauss.Sizes.SeqΩ sz × RBM.Gauss.Ω d (sz.L n) (sz.W n)) (z : ℂ)
    (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool)
    (hH : (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω).IsHermitian),
    0 < z.im →
      ‖∑ x, (Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) z b₁ *
            Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) z b₁) x x *
          RBM.Univ.scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
            Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) z b₂ y y‖ ≤
        ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ))⁻¹ *
          (∑ α, ‖spectralGsigPole hH z b₁ α‖ ^ 2 *
            ‖blockM d (sz.L n) (sz.W n) (sz.lam n) hH (siteBlock d (sz.L n) (sz.W n) y) α‖) *
          (∑ γ, ‖spectralGsigPole hH z b₂ γ‖ * Complex.normSq (hH.eigenvectorBasis γ y))

end RBM.Univ.T2251Check
