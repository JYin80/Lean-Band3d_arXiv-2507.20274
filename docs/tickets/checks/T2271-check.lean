/-
Release check for T2271 (dispatcher V1, Tue Oct  6 07:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B, §88 (2)).
UN-22: the deterministic pair kernel layer of `(uywy7723r3rf)` (the weighted `y`-term of the pin `UNUyw`): port of
RBM2D `Universality/UywKernel.lean` (c9a24cf, 1372 lines; `blockM2` `:760`, `blockM2_self` `:769`, `blockM2_eq`
`:800`, `green_spectral_identity_blockM2` `:877`, `measure_bad2_le_of_queBadMat` `:909`, `uyw_pointwise_good`
`:1055`, `uyw_pointwise_crude` `:1127`, instances `UywKernelCheck` `:1174-1363`) to `Idx d L W`, `scirc d L W lam`,
`N = (W L)^d`, the merged `Gres`, the merged UN-19/UN-20 layers (`blockM d L W lam`, `siteBlock d L W`,
`jakGridGood`, `im_Gres_apply_self`, `sum_mass_window_le_of_im_green_le`) and the `d ≥ 3` pair moment (the `2d+1`
weights `SBR d L lam b a₀` in place of RBM2D's `1/5` average over `a₀ + sbSupport L`); new file
`RBM3D/Universality/UywKernel.lean`.  Deterministic only (the one probability statement is the union bound from
a hypothesised `queBadMat` bound): no pin is proved, stated or registered.  No primed name occurs here.
Section 1: the merged names the new file builds on.
Section 2: the new vocabulary (2.1, body copied verbatim into namespace `RBM.Univ`), the statements of the
theorems of T2271 as `def T2271_<name> : Prop` (2.2-2.4) and the instances (2.5); the library states the theorem
`<name>` (namespace `RBM.Univ`; instances in `RBM.Univ.UywKernelInst` with `T2271_H1`, `T2271_y0` renamed `H1`,
`y0`) with exactly this body (binder names may be added; `Type*` for the check's `Type`).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2271-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-! ## 1. Merged names -/

-- UN-20 (`Universality/JakKernel.lean`, T2267, merged c77e68c; namespace `RBM.Univ`)
#check @RBM.Univ.im_Gres_apply_self                        -- :48 (replaces RBM2D `RBM.im_green_apply_self`, 1 use, `0 < η`)
#check @RBM.Univ.sum_mass_window_le_im_green               -- :93
#check @RBM.Univ.sum_mass_window_le_of_im_green_le         -- :147 (1 use in RBM2D UywKernel)
#check @RBM.Univ.jakGridGood                               -- :167 (10 uses)
#check @RBM.Univ.jak_pointwise_good                        -- :854 (shape template of target 4a)
#check @RBM.Univ.jak_pointwise_crude                       -- :933 (shape template of target 4b)
#check @RBM.Univ.JakKernelInst.im_Gres_le_inv              -- :984
#check @RBM.Univ.JakKernelInst.gridGood_one                -- :1005 (RBM2D `JakKernelCheck.gridGood_one`; instances)
#check @RBM.Univ.JakKernelInst.blockM_le_432               -- :1012 (template of `blockM2_le_432`)
-- UN-19 (`Universality/JakSpectral.lean`, T2251, merged 88183b6; namespace `RBM.Univ`)
#check @RBM.Univ.spectralPole                              -- :48
#check @RBM.Univ.spectralGsigPole                          -- :53
#check @RBM.Univ.isOrthoEigenbasis_eigenvectorBasis        -- :69
#check @RBM.Univ.Gres_sq_apply_self                        -- :125
#check @RBM.Univ.Gres_apply_self_spectral                  -- :155
#check @RBM.Univ.Gres_sq_apply_self_spectral               -- :173
#check @RBM.Univ.spectralGsigPole_norm_eq_spectralPole     -- :185
#check @RBM.Univ.siteBlock                                 -- :220
#check @RBM.Univ.blockM                                    -- :227 (`lam` after `d L W`; `SBR` weights; `blockM2_self` target)
#check @RBM.Univ.blockM_eq_unMy                            -- :251
#check @RBM.Univ.blockM_eq                                 -- :268 (template of `blockM2_eq`)
#check @RBM.Univ.green_spectral_identity_blockM            -- :339 (template of target 2; product form `p * p`)
#check @RBM.Univ.norm_green_spectral_identity_blockM_le    -- :357
#check @RBM.Univ.sum_norm_blockM_le                        -- :509
#check @RBM.Univ.unBadY_of_blockM                          -- :545
#check @RBM.Univ.measure_bad_le_of_queBadMat               -- :559 (the `d ≥ 3` one-index form; template of target 3)
-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.IsOrthoEigenbasis    -- :53
#check @RBM.Univ.stieltjesN           -- :88
#check @RBM.Univ.ouMat                -- :150
#check @RBM.Univ.ouMat_isHermitian    -- :154
#check @RBM.Univ.queWindow            -- :380
#check @RBM.Univ.queBadMat            -- :392 (pair `i, j`, `if i = j`; `(ε₀, c) = (𝔡/3, 𝔡/6)` in target 3)
#check @RBM.Univ.InWindow             -- :501
#check @RBM.Univ.scirc                -- :612
#check @RBM.Univ.UNUyw                -- :708 (integrand `:712-716`; owed, stays owed)
#check @RBM.Univ.UNJakUywRow          -- :805 (owed, stays owed: UN-23)
#check @RBM.Univ.un_window_sub        -- :908 (window of target 3 inside `𝓘_E(𝔡/3)`)
#check @RBM.Univ.unMy                 -- :1140
#check @RBM.Univ.UNBadY               -- :1147
#check @RBM.Univ.unMy_eq              -- :1156 (template of `blockM2_eq`: the `SBR`-weighted block sum)
#check @RBM.Univ.unBadY_subset        -- :1205 (template of the averaging step of target 3)
#check @RBM.Univ.unBadY_card_le       -- :1298 (`≤ 2d + 1` blocks; replaces RBM2D `Finset.card_le_five`)
#check @RBM.Univ.unBadY_measure_le    -- :1320
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0)
#check @RBM.Univ.UNUywk               -- :378 (same integrand at `lam = K.lamV sz n`)
-- the fine lattice, blocks and the variance profile
#check @RBM.Zd                        -- `Defs/Lattice.lean:63` (51f1a17)
#check @RBM.Gauss.Idx                 -- `Defs/Sizes.lean:46` (0a873f1)
#check @RBM.Gauss.split               -- `Defs/Sizes.lean:64`
#check @RBM.Gauss.Iblk                -- `Defs/Sizes.lean:92`
#check @RBM.Gauss.card_Iblk           -- `Defs/Sizes.lean:95`
#check @RBM.Gauss.card_Idx            -- `Defs/Sizes.lean:107` (replaces `UywKernel_card_idx` `:699`)
#check @RBM.Gauss.Sizes.neZeroL       -- `Defs/Sizes.lean:152`
#check @RBM.Gauss.Sizes.neZeroW       -- `Defs/Sizes.lean:153`
#check @RBM.Gauss.svarF               -- `Gauss/FineModel.lean:47` (`W^{-d} SBR(blk x, blk y)`)
#check @RBM.Gauss.svarF_nonneg        -- `Gauss/FineModel.lean:51`
#check @RBM.Gauss.svarF_comm          -- `Gauss/FineModel.lean:54`
#check @RBM.SBR                       -- `Propagator/Props4.lean:48` (892334b)
#check @RBM.sum_SBR_row               -- `Propagator/Gap.lean:206` (24cf61d; `3 ≤ L`)
#check @RBM.SBR_comm                  -- `Propagator/Gap.lean:230`
-- resolvent
#check @RBM.Gauss.Gres                -- `Loop/GLoopFlow.lean:74` (868b3b4)
-- Mathlib
#check @Matrix.IsHermitian.eigenvalues          -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.eigenvectorBasis     -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.isHermitian_one                  -- Mathlib.LinearAlgebra.Matrix.Hermitian
#check @MeasureTheory.measure_biUnion_finset_le -- Mathlib.MeasureTheory.OuterMeasure.Basic
#check @MeasureTheory.Measure.dirac             -- Mathlib.MeasureTheory.Measure.Dirac

namespace RBM.Univ.T2271Check

open Matrix MeasureTheory
open RBM.Gauss
open scoped ENNReal

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

/-- The pair moment `M_{a₀,α,β}` (`d ≥ 3` form of RBM2D `blockM2` `:760`): the `S^{(B)}(lam)`-weighted average
(weights `SBR d L lam b a₀`, sum `1`, support `≤ 2d + 1` blocks) of the pair block QUE quantities
`(N/W^d) ∑_{x∈[b]} conj ψ_β(x) ψ_α(x) - δ_{αβ}` (the overlap of the merged `queBadMat` at `i = β`, `j = α`).
At `α = β` it is the merged `blockM` (`blockM2_self`). -/
noncomputable def blockM2 (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) (a0 : Zd d L) (α β : Idx d L W) : ℂ :=
  ∑ b : Zd d L, ((SBR d L lam b a0 : ℝ) : ℂ) *
    ((((W * L) ^ d : ℕ) : ℂ) / (W : ℂ) ^ d *
        (∑ x ∈ Iblk d L W b, star (hH.eigenvectorBasis β x) * hH.eigenvectorBasis α x) -
      (if α = β then 1 else 0))

/-! ### 2.2 Target 1: the pair moment (RBM2D `:753-830`) -/

/-- `blockM2_self` (1a; RBM2D `:769`, there `rfl`; here `simp [blockM2, blockM]`). -/
def T2271_blockM2_self : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (a0 : Zd d L) (α : Idx d L W),
    blockM2 d L W lam hH a0 α α = blockM d L W lam hH a0 α

/-- `blockM2_eq` (1b; RBM2D `:800`): `M_{y,α,β} = N ∑_x ψ_α(x) conj ψ_β(x) S°_{xy}`; `3 ≤ L`. -/
def T2271_blockM2_eq : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y α β : Idx d L W),
    blockM2 d L W lam hH (siteBlock d L W y) α β =
      (((W * L) ^ d : ℕ) : ℂ) *
        ∑ x, (hH.eigenvectorBasis α x * star (hH.eigenvectorBasis β x)) * scirc d L W lam x y

/-! ### 2.3 Targets 2, 3: the spectral expansion of the `y`-term of `L₂` and the pair bad event -/

/-- `green_spectral_identity_blockM2` (2; RBM2D `:877`; `Gsig H z σ ^ 2` ↦ `Gres H z σ * Gres H z σ`,
`spectralGsigPole … ^ 2` ↦ `p * p` as the merged `green_spectral_identity_blockM`). -/
def T2271_green_spectral_identity_blockM2 : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (y : Idx d L W) (z₁ z₂ : ℂ), 0 < z₁.im → 0 < z₂.im → ∀ σ₁ σ₂ : Bool,
    (∑ x : Idx d L W, (Gres H z₁ σ₁ * Gres H z₁ σ₁) x y * scirc d L W lam x y *
        (Gres H z₂ σ₂ * Gres H z₂ σ₂) y x) =
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * ∑ α : Idx d L W, ∑ β : Idx d L W,
        spectralGsigPole hH z₁ σ₁ α * spectralGsigPole hH z₁ σ₁ α *
          (spectralGsigPole hH z₂ σ₂ β * spectralGsigPole hH z₂ σ₂ β) *
            blockM2 d L W lam hH (siteBlock d L W y) α β *
              star (hH.eigenvectorBasis α y) * hH.eigenvectorBasis β y

/-- `measure_bad2_le_of_queBadMat` (3; RBM2D `:909`, `d ≥ 3` data of the merged `measure_bad_le_of_queBadMat`
(`JakSpectral.lean:559`): `queBadMat` at `(ε₀, c) = (𝔡/3, 𝔡/6)`, window `N⁻¹ W^{𝔡/3}`, threshold `W^{-𝔡/6}`,
`2d + 1` blocks instead of `5`; per block `a₀`). -/
def T2271_measure_bad2_le_of_queBadMat : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω), 3 ≤ L →
    ∀ {lam 𝔡 E : ℝ}, 1 ≤ (W : ℝ) → 0 < 𝔡 → (W : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ lam → ∀ (a0 : Zd d L)
    {Hr : Ω → Matrix (Idx d L W) (Idx d L W) ℂ} (hH : ∀ ω, (Hr ω).IsHermitian) (p : ℝ≥0∞),
    (∀ b : Zd d L, P {ω | queBadMat d L W lam (𝔡 / 3) (𝔡 / 6) E b (Hr ω)} ≤ p) →
    P {ω | ∃ α β, |(hH ω).eigenvalues α - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        |(hH ω).eigenvalues β - E| ≤ (((W * L) ^ d : ℕ) : ℝ)⁻¹ * (W : ℝ) ^ (𝔡 / 3) ∧
        (W : ℝ) ^ (-(𝔡 / 6)) ≤ ‖blockM2 d L W lam (hH ω) a0 α β‖} ≤
      ((2 * d + 1 : ℕ) : ℝ≥0∞) * p

/-! ### 2.4 Target 4: the pointwise bounds of the weighted `y`-term of `L₂` (RBM2D `:967-1163`; `Idx L W` ↦
`Idx d L W`, `Z2 L` ↦ `Zd d L`, `(W * L) ^ 2` ↦ `(W * L) ^ d`, new explicit `lam` after `hL`; the other binders
as RBM2D) -/

/-- `uyw_pointwise_good` (4a; RBM2D `:1055`; constants `Ag`, `Ab` of RBM2D shape). -/
def T2271_uyw_pointwise_good : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (m : ℕ) (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ)
    (ηt Cb w' θ Ag Ab : ℝ),
    0 < u₁.im → u₁.im ≤ ηt → 0 < u₂.im → u₂.im ≤ ηt →
    (∀ j, 0 < (w j).im) → (∀ j, (w j).im ≤ ηt) → 0 ≤ Cb → 0 < w' → 0 ≤ θ → ∀ K' : ℕ,
    (∀ k ≤ K', RBM.Univ.jakGridGood H ηt Cb u₁.re (2 ^ k * w')) →
    (∀ k ≤ K', RBM.Univ.jakGridGood H ηt Cb u₂.re (2 ^ k * w')) →
    RBM.Univ.jakGridGood H ηt Cb u₁.re 0 → RBM.Univ.jakGridGood H ηt Cb u₂.re 0 →
    (∀ j, RBM.Univ.jakGridGood H ηt Cb (w j).re 0) →
    ∀ (Bad : Zd d L → Prop) [DecidablePred Bad],
    (∀ a0, ¬ Bad a0 → ∀ α β, |hH.eigenvalues α - u₁.re| ≤ w' →
      |hH.eigenvalues β - u₂.re| ≤ w' → ‖blockM2 d L W lam hH a0 α β‖ ≤ θ) →
    θ / 2 * ((ηt / u₁.im ^ 2 * Cb) * ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₂.im ^ 2 * Cb)) +
        ((((W * L) ^ d : ℕ) : ℝ) * (ηt / u₁.im ^ 2 * Cb)) * (ηt / u₂.im ^ 2 * Cb)) +
      2 * (((W * L) ^ d : ℕ) : ℝ) *
        ((Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹) * (ηt / u₂.im ^ 2 * Cb) +
          (ηt / u₁.im ^ 2 * Cb) * (Cb * (8 / w' + 8 * ηt / w' ^ 2) + ((2 ^ K' * w') ^ 2)⁻¹)) ≤ Ag →
    4 * (((W * L) ^ d : ℕ) : ℝ) * ((ηt / u₁.im ^ 2 * Cb) * (ηt / u₂.im ^ 2 * Cb)) ≤ Ab →
    ∀ (y : Idx d L W) (σ₁ σ₂ : Bool),
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (ηt / (w j).im * Cb)) *
        ((((W * L) ^ d : ℕ) : ℝ)⁻¹ * (Ag + (if Bad (siteBlock d L W y) then Ab else 0)))

/-- `uyw_pointwise_crude` (4b; RBM2D `:1127`), valid for every Hermitian matrix. -/
def T2271_uyw_pointwise_crude : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ) {H : Matrix (Idx d L W) (Idx d L W) ℂ},
    H.IsHermitian → ∀ (m : ℕ) (s : Finset (Fin m)) (w : Fin m → ℂ) (u₁ u₂ : ℂ),
    0 < u₁.im → 0 < u₂.im → (∀ j, 0 < (w j).im) → ∀ (y : Idx d L W) (σ₁ σ₂ : Bool),
    (∏ j ∈ s, (stieltjesN H (w j)).im) *
        ‖∑ x, (Gres H u₁ σ₁ * Gres H u₁ σ₁) x y * scirc d L W lam x y *
          (Gres H u₂ σ₂ * Gres H u₂ σ₂) y x‖ ≤
      (∏ j ∈ s, (w j).im⁻¹) * (4 * ((u₁.im⁻¹) ^ 2 * (u₂.im⁻¹) ^ 2))

/-! ### 2.5 Target 5: instances (namespace `RBM.Univ.UywKernelInst`; `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`H = 1`, `y = 0`, `u₁ = u₂ = w 0 = I`, `ηt = Cb = w' = 1`, `K' = 1`, `Bad ≡ False`, `θ = 2N = 432`,
`Ag = 107352 = 432·216 + 432·(65/2)`, `Ab = 864 = 4·216`; target 3 at `Measure.dirac ()`, `𝔡 = 1/10`, `lam = 1`,
`E = 0`, `a₀ = 0`, `p = 1`) -/

/-- The data (the library defines `UywKernelInst.H1`, `y0` with these bodies). -/
noncomputable abbrev T2271_H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def T2271_y0 : Idx 3 3 2 := 0

/-- `blockM2_le_432` (RBM2D `blockM2_le_72` `:1201`; `2N = 432`, every `lam`, every `a₀`). -/
def T2271_blockM2_le_432 : Prop :=
  ∀ {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ) (a0 : Zd 3 3)
    (α β : Idx 3 3 2), ‖blockM2 3 3 2 lam hH a0 α β‖ ≤ 432

/-- `inst_self` (target 1a at `H = 1`, `lam = 1/2`, `a₀ = 0`, `α = y0`). -/
def T2271_inst_self : Prop :=
  ∀ hH : T2271_H1.IsHermitian,
    blockM2 3 3 2 (1 / 2) hH 0 T2271_y0 T2271_y0 = blockM 3 3 2 (1 / 2) hH 0 T2271_y0

/-- `inst_bad2` (target 3 at the data above; every hypothesis discharged: `prob_le_one`,
`(2:ℝ)^(-3/2 + 1/10) ≤ 1`). -/
def T2271_inst_bad2 : Prop :=
  ∀ hH : ∀ _ω : Unit, T2271_H1.IsHermitian,
    (Measure.dirac ()) {ω : Unit | ∃ α β,
        |(hH ω).eigenvalues α - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        |(hH ω).eigenvalues β - 0| ≤ (((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((2 : ℕ) : ℝ) ^ ((1 / 10 : ℝ) / 3) ∧
        ((2 : ℕ) : ℝ) ^ (-((1 / 10 : ℝ) / 6)) ≤ ‖blockM2 3 3 2 1 (hH ω) 0 α β‖} ≤
      ((2 * 3 + 1 : ℕ) : ℝ≥0∞) * 1

/-- `inst_good` (target 4a at the data above, every `y`, `σ₁`, `σ₂`; RBM2D `:1290`). -/
def T2271_inst_good : Prop :=
  ∀ (y : Idx 3 3 2) (σ₁ σ₂ : Bool),
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN T2271_H1 Complex.I).im) *
        ‖∑ x, (Gres T2271_H1 Complex.I σ₁ * Gres T2271_H1 Complex.I σ₁) x y *
          scirc 3 3 2 (1 / 2) x y * (Gres T2271_H1 Complex.I σ₂ * Gres T2271_H1 Complex.I σ₂) y x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * (107352 + (if False then (864 : ℝ) else 0)))

/-- `inst_crude` (target 4b at `H = 1`, `s = {0}`, `w 0 = u₁ = u₂ = I`, `y = y0`, every `σ₁`, `σ₂`). -/
def T2271_inst_crude : Prop :=
  ∀ σ₁ σ₂ : Bool,
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN T2271_H1 Complex.I).im) *
        ‖∑ x, (Gres T2271_H1 Complex.I σ₁ * Gres T2271_H1 Complex.I σ₁) x T2271_y0 *
          scirc 3 3 2 (1 / 2) x T2271_y0 *
            (Gres T2271_H1 Complex.I σ₂ * Gres T2271_H1 Complex.I σ₂) T2271_y0 x‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) *
        (4 * ((Complex.I.im⁻¹) ^ 2 * (Complex.I.im⁻¹) ^ 2))

/-! ## 3. Downstream shapes (not targets of T2271; information) -/

-- the owed pins this file serves (all stay owed; `Test/Axioms.lean:206, 212, 225, 230, 240` on f515695)
#check @RBM.Univ.UNUyw                -- Pins.lean:708 (UN-23 `Uyw`: `uyw_pointwise_good` (4), `_crude` (1), `blockM2` (3), `jakGridGood` (12))
#check @RBM.Univ.UNUywk               -- PinsK.lean:378 (model-generic: `lam = K.lamV sz n`)

-- consumer shape (UN-23, token check of preflight (i)): the left side of targets 4a/4b at
-- `H = ouMat (UNModel.band sz) n t ω`, `lam = sz.lam n`, `w = z`, `u₁ = z i`, `u₂ = z j`, `(σ₁, σ₂) = (b₁, b₂)`
-- is the integrand of `UNUyw` (`Pins.lean:712-716`) token for token
example : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n nf : ℕ) (t : ℝ)
    (ω : RBM.Gauss.Sizes.SeqΩ sz × RBM.Gauss.Ω d (sz.L n) (sz.W n)) (z : Fin nf → ℂ)
    (s : Finset (Fin nf)) (i j : Fin nf) (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
    (∀ k, 0 < (z k).im) →
      (∏ k ∈ s, (stieltjesN (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z k)).im) *
          ‖∑ x, (Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z i) b₁ *
              Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z i) b₁) x y *
            scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
              (Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z j) b₂ *
                Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z j) b₂) y x‖ ≤
        (∏ k ∈ s, (z k).im⁻¹) * (4 * (((z i).im⁻¹) ^ 2 * ((z j).im⁻¹) ^ 2))

end RBM.Univ.T2271Check
