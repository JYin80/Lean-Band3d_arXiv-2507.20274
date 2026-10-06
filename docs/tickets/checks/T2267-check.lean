/-
Release check for T2267 (dispatcher V1, Tue Oct  6 07:05 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §48, §50, §54, §56, §57 (1)-(2), §64 (4), §65, §66, §69 B).
UN-20: the deterministic kernel layer of `(jaklsdufowe)` (the weighted `y`-term of the pin `UNJak`): port of RBM2D
`Universality/JakKernel.lean` (c9a24cf, 1121 lines; `sum_mass_window_le_im_green` `:81`,
`sum_mass_window_le_of_im_green_le` `:135`, `jakGridGood` `:155`, `jak_pointwise_good` `:848`,
`jak_pointwise_crude` `:927`, instances `JakKernelCheck` `:970-1114`) to `Idx d L W`, `scirc d L W lam`,
`N = (W L)^d`, the merged `Gres` (RBM2D `RBM.green` / `Gsig`; `RBM.green` is outside the closure of `JakSpectral`)
and the merged UN-19 layer (`blockM d L W lam`, `siteBlock d L W`, `norm_green_spectral_identity_blockM_le`,
`sum_norm_blockM_le`); new file `RBM3D/Universality/JakKernel.lean`.  Deterministic only: no pin is proved,
stated or registered.  No primed name occurs here.
Section 1: the merged names the new file builds on (and the Mathlib names of the RBM2D route).
Section 2: the new vocabulary (2.1, body copied verbatim into namespace `RBM.Univ`), the statements of the
theorems of T2267 as `def T2267_<name> : Prop` (2.2-2.3) and the instances (2.4); the library states the theorem
`<name>` (namespace `RBM.Univ`; instances in `RBM.Univ.JakKernelInst` with `T2267_H1`, `T2267_y0` renamed `H1`,
`y0`) with exactly this body (binder names may be added; `Type*` for the check's `Type`).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2267-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! ## 1. Merged names -/

-- UN-19 (`Universality/JakSpectral.lean`, T2251, merged 88183b6; namespace `RBM.Univ`)
#check @RBM.Univ.spectralPole                              -- :48
#check @RBM.Univ.spectralGsigPole                          -- :53
#check @RBM.Univ.isOrthoEigenbasis_eigenvectorBasis        -- :69
#check @RBM.Univ.Gres_sq_apply_self                        -- :125
#check @RBM.Univ.Gres_apply_self_spectral                  -- :155 (route of `im_Gres_apply_self`, `0 < Im z`)
#check @RBM.Univ.Gres_sq_apply_self_spectral               -- :173
#check @RBM.Univ.spectralGsigPole_norm_eq_spectralPole     -- :185
#check @RBM.Univ.siteBlock                                 -- :220
#check @RBM.Univ.blockM                                    -- :227 (`lam` after `d L W`; `SBR` weights)
#check @RBM.Univ.blockM_eq_unMy                            -- :251
#check @RBM.Univ.blockM_eq                                 -- :268 (`N ∑_x |ψ_α(x)|² S°_{xy}`, `3 ≤ L`)
#check @RBM.Univ.green_spectral_identity_blockM            -- :339
#check @RBM.Univ.norm_green_spectral_identity_blockM_le    -- :357 (the `y`-term triangle bound)
#check @RBM.Univ.sum_norm_blockM_le                        -- :509 (`∑_α |M| ≤ 2N`)
#check @RBM.Univ.unBadY_of_blockM                          -- :545 (UN-21, not used here)
#check @RBM.Univ.measure_bad_le_of_queBadMat               -- :559 (UN-21, not used here)
-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.IsOrthoEigenbasis    -- :53
#check @RBM.Univ.stieltjesN           -- :88 (`(card ι)⁻¹ * (Gres M z true).trace`)
#check @RBM.Univ.ouMat                -- :150
#check @RBM.Univ.ouMat_isHermitian    -- :154
#check @RBM.Univ.InWindow             -- :501
#check @RBM.Univ.scirc                -- :612 (`svarF d L W lam - ((W L)^d)⁻¹`, in `ℂ`; RBM2D `Scirc`)
#check @RBM.Univ.UNJak                -- :694 (integrand `(∏ Im m) * ‖∑ x, (Gres M z b₁ * Gres M z b₁) x x * scirc … x y * Gres M z b₂ y y‖`)
#check @RBM.Univ.UNUyw                -- :708
#check @RBM.Univ.UNJakUywRow          -- :805 (owed; stays owed)
-- UN-01b (`Universality/PinsK.lean`, T2187, fdbb6f0)
#check @RBM.Univ.UNJakk               -- :365 (same integrand at `lam = K.lamV sz n`)
-- UN-03a (`Universality/InjSum.lean`, T2178, 4c52041): templates only, NOT imported (InjSum imports `Green/EntryCore`)
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight   -- :196 (template of private `JakKernel_stieltjesN_im_eq`)
#check @RBM.Univ.stieltjesN_eta_mul_im_mono               -- :203 (template of private `JakKernel_stieltjesN_eta_mul_im_mono`)
-- the fine lattice, blocks and the variance profile
#check @RBM.Zd                        -- `Defs/Lattice.lean:63` (51f1a17)
#check @RBM.Gauss.Idx                 -- `Defs/Sizes.lean:46` (0a873f1; `Zd d (W * L)`)
#check @RBM.Gauss.split               -- `Defs/Sizes.lean:64`
#check @RBM.Gauss.Iblk                -- `Defs/Sizes.lean:92`
#check @RBM.Gauss.card_Iblk           -- `Defs/Sizes.lean:95` (`W ^ d`)
#check @RBM.Gauss.card_Idx            -- `Defs/Sizes.lean:107` (`(W * L) ^ d`; replaces RBM2D `JakKernel_card_idx` `:620`)
#check @RBM.Gauss.Sizes.neZeroL       -- `Defs/Sizes.lean:152` (instance)
#check @RBM.Gauss.Sizes.neZeroW       -- `Defs/Sizes.lean:153` (instance)
#check @RBM.Gauss.svarF               -- `Gauss/FineModel.lean:47` (0a873f1)
#check @RBM.Gauss.svarF_nonneg        -- `Gauss/FineModel.lean:51` (replaces `Spaper_indicator` route)
#check @RBM.Gauss.svarF_comm          -- `Gauss/FineModel.lean:54` (replaces `Spaper_transpose`)
#check @RBM.SBR                       -- `Propagator/Props4.lean:48` (892334b)
#check @RBM.sum_SBR_row               -- `Propagator/Gap.lean:206` (24cf61d; `3 ≤ L`; replaces `sum_Spaper_row`)
#check @RBM.SBR_comm                  -- `Propagator/Gap.lean:230`
-- resolvent
#check @RBM.Gauss.Gres                -- `Loop/GLoopFlow.lean:74` (868b3b4; RBM2D `RBM.green` (σ = true) and `Gsig`)
-- Mathlib
#check @Matrix.IsHermitian.eigenvalues          -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.IsHermitian.eigenvectorBasis     -- Mathlib.Analysis.Matrix.Spectrum
#check @Matrix.isHermitian_one                  -- Mathlib.LinearAlgebra.Matrix.Hermitian
#check @Nat.le_ceil                             -- Mathlib.Algebra.Order.Floor.Semiring
#check @Nat.ceil_lt_add_one                     -- Mathlib.Algebra.Order.Floor.Semiring
#check @Finset.prod_le_prod₀                    -- Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

namespace RBM.Univ.T2267Check

open Matrix
open RBM.Gauss

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

/-- The single-scale grid event (RBM2D `jakGridGood` `:155`; `RBM.green H w` ↦ `Gres H w true`):
`Im G_xx ≤ Cb` on the covering grid `E₀ - r + 2ηj + iη`, `j ≤ ⌈r/η⌉₊`, for every site `x`. -/
def jakGridGood {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (η Cb E₀ r : ℝ) : Prop :=
  ∀ j ∈ Finset.range (⌈r / η⌉₊ + 1), ∀ x : n,
    (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im ≤ Cb

/-! ### 2.2 Target 1: the imaginary part of the resolvent diagonal and the covering lemma (generic index type;
RBM2D `:49-160`) -/

/-- `im_Gres_apply_self` (new public form of RBM2D `RBM.im_green_apply_self`, `Delocalization.lean:89`, which
is outside the closure; `η ≠ 0` ↦ `0 < η`; route `Gres_apply_self_spectral` at `σ = true`; target 1a; UN-22
`UywKernel` uses it once). -/
def T2267_im_Gres_apply_self : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) (E : ℝ) {η : ℝ},
    0 < η → ∀ x : n,
      (Gres H (E + η * Complex.I) true x x).im =
        ∑ l, η * Complex.normSq (hH.eigenvectorBasis l x) / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)

/-- `sum_mass_window_le_im_green` (RBM2D `:81`; `RBM.green H w` ↦ `Gres H w true`; target 1b). -/
def T2267_sum_mass_window_le_im_green : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r : ℝ},
    0 < η → 0 ≤ r → ∀ (E₀ : ℝ) (x : n),
      ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
          ‖hH.eigenvectorBasis l x‖ ^ 2 ≤
        2 * η * ∑ j ∈ Finset.range (⌈r / η⌉₊ + 1),
          (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im

/-- `sum_mass_window_le_of_im_green_le` (RBM2D `:135`; target 1c). -/
def T2267_sum_mass_window_le_of_im_green_le : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.IsHermitian) {η r Cb : ℝ},
    0 < η → 0 ≤ r → 0 ≤ Cb → ∀ (E₀ : ℝ) (x : n),
      (∀ j ∈ Finset.range (⌈r / η⌉₊ + 1),
        (Gres H (((E₀ - r + 2 * η * j : ℝ) : ℂ) + η * Complex.I) true x x).im ≤ Cb) →
      ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - E₀| ≤ r),
          ‖hH.eigenvectorBasis l x‖ ^ 2 ≤ 2 * (r + 2 * η) * Cb

/-! ### 2.3 Target 2: the pointwise bounds of the weighted `y`-term (RBM2D `:836-959`; `Idx L W` ↦ `Idx d L W`,
`Z2 L` ↦ `Zd d L`, `(W L)^2` ↦ `(W L)^d`, `Gsig H u σ ^ 2` ↦ `Gres H u σ * Gres H u σ`, `Scirc L W` ↦
`scirc d L W lam`, `blockM L W hH` ↦ `blockM d L W lam hH`, `siteBlock L W` ↦ `siteBlock d L W`; `lam` after `hL`) -/

/-- `jak_pointwise_good` (RBM2D `:848`; the constants are unchanged in form: `2N` from `sum_norm_blockM_le`, the
weight sum `∑_x (S_{xy} + N⁻¹) = 2`, `card (Idx d L W) = N`; target 2a). -/
def T2267_jak_pointwise_good : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ} (hH : H.IsHermitian) {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ) {ηt Cb w' θ α₁ α₂ Qb : ℝ},
    0 < u.im → u.im ≤ ηt → (∀ j, 0 < (w j).im) → (∀ j, (w j).im ≤ ηt) → 0 ≤ Cb → 0 < w' →
    0 ≤ θ → ∀ K K' : ℕ,
    (∀ k ≤ K, jakGridGood H ηt Cb u.re (2 ^ k * ηt)) →
    (∀ k ≤ K', jakGridGood H ηt Cb u.re (2 ^ k * w')) →
    jakGridGood H ηt Cb u.re 0 →
    (∀ j, jakGridGood H ηt Cb (w j).re 0) →
    ∀ (Bad : Zd d L → Prop) [DecidablePred Bad],
    (∀ a0, ¬ Bad a0 → ∀ α, |hH.eigenvalues α - u.re| ≤ w' → ‖blockM d L W lam hH a0 α‖ ≤ θ) →
    θ * (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) +
        4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
          (2 * (((W * L) ^ d : ℕ) : ℝ) * Cb * (4 / w' + 4 * ηt / w' ^ 2)) +
        ((2 ^ K' * w') ^ 2)⁻¹ * (2 * (((W * L) ^ d : ℕ) : ℝ)) ≤ α₁ →
    4 * (((W * L) ^ d : ℕ) : ℝ) * ηt * Cb *
        (ηt / u.im ^ 2 * ((((W * L) ^ d : ℕ) : ℝ) * Cb)) ≤ α₂ →
    6 * (ηt / u.im) * Cb + 8 * K * Cb + (2 ^ K * ηt)⁻¹ ≤ Qb →
    ∀ (y : Idx d L W) (σ₁ σ₂ : Bool),
      (∏ j ∈ s, (stieltjesN H (w j)).im) *
          ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
        (∏ j ∈ s, (ηt / (w j).im * Cb)) *
          ((((W * L) ^ d : ℕ) : ℝ)⁻¹ *
            ((α₁ + (if Bad (siteBlock d L W y) then α₂ else 0)) * Qb))

/-- `jak_pointwise_crude` (RBM2D `:927`; valid for every Hermitian matrix; target 2b). -/
def T2267_jak_pointwise_crude : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W], 3 ≤ L → ∀ (lam : ℝ)
    {H : Matrix (Idx d L W) (Idx d L W) ℂ}, H.IsHermitian → ∀ {m : ℕ} (s : Finset (Fin m))
    (w : Fin m → ℂ) (u : ℂ), 0 < u.im → (∀ j, 0 < (w j).im) → ∀ (y : Idx d L W) (σ₁ σ₂ : Bool),
      (∏ j ∈ s, (stieltjesN H (w j)).im) *
          ‖∑ x, (Gres H u σ₁ * Gres H u σ₁) x x * scirc d L W lam x y * Gres H u σ₂ y y‖ ≤
        (∏ j ∈ s, (w j).im⁻¹) * (2 * (u.im⁻¹) ^ 3)

/-! ### 2.4 Target 3: instances (namespace `RBM.Univ.JakKernelInst`; `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`lam = 1/2`, `H = 1`, `y = 0`, `u = w 0 = I`, `ηt = Cb = w' = 1`, `K = K' = 1`, `Bad ≡ False`, `θ = 2N = 432`,
`α₁ = 3079404 = 432·216 + 864·3456 + 108`, `α₂ = 186624 = 4·216²`, `Qb = 29/2`) -/

/-- The data (the library defines `JakKernelInst.H1`, `y0` with these bodies). -/
noncomputable abbrev T2267_H1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ := 1

def T2267_y0 : Idx 3 3 2 := 0

/-- `im_Gres_le_inv` (RBM2D `JakKernelCheck.im_green_le_inv` `:978`; generic). -/
def T2267_im_Gres_le_inv : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}, H.IsHermitian → ∀ {η : ℝ}, 0 < η →
    ∀ (E : ℝ) (x : n), (Gres H ((E : ℂ) + η * Complex.I) true x x).im ≤ η⁻¹

/-- `gridGood_one` (RBM2D `:999`; generic: `ηt = Cb = 1` at every centre and radius). -/
def T2267_gridGood_one : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}, H.IsHermitian →
    ∀ E₀ r : ℝ, jakGridGood H 1 1 E₀ r

/-- `blockM_le_432` (RBM2D `blockM_le_72` `:1024`; `2N = 432`, every `lam`). -/
def T2267_blockM_le_432 : Prop :=
  ∀ {H : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ} (hH : H.IsHermitian) (lam : ℝ) (a0 : Zd 3 3) (α : Idx 3 3 2),
    ‖blockM 3 3 2 lam hH a0 α‖ ≤ 432

/-- `inst_window` (target 1c at `H = 1`, `η = r = Cb = 1`, `E₀ = 0`, `x = 0`; RBM2D `:1019`). -/
def T2267_inst_window : Prop :=
  ∀ hH : T2267_H1.IsHermitian,
    ∑ l ∈ Finset.univ.filter (fun l => |hH.eigenvalues l - 0| ≤ 1),
        ‖hH.eigenvectorBasis l T2267_y0‖ ^ 2 ≤ 2 * (1 + 2 * 1) * 1

/-- `inst_good` (target 2a at the data above, every `y`, `σ₁`, `σ₂`; RBM2D `:1050`). -/
def T2267_inst_good : Prop :=
  ∀ (y : Idx 3 3 2) (σ₁ σ₂ : Bool),
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN T2267_H1 Complex.I).im) *
        ‖∑ x, (Gres T2267_H1 Complex.I σ₁ * Gres T2267_H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x y * Gres T2267_H1 Complex.I σ₂ y y‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), (1 / Complex.I.im * 1)) *
        ((((2 * 3) ^ 3 : ℕ) : ℝ)⁻¹ * ((3079404 + (if False then (186624 : ℝ) else 0)) * (29 / 2)))

/-- `inst_crude` (target 2b at `H = 1`, `s = {0}`, `w 0 = u = I`, `y = 0`, every `σ₁`, `σ₂`; RBM2D `:1076`). -/
def T2267_inst_crude : Prop :=
  ∀ σ₁ σ₂ : Bool,
    (∏ _j ∈ ({0} : Finset (Fin 1)), (stieltjesN T2267_H1 Complex.I).im) *
        ‖∑ x, (Gres T2267_H1 Complex.I σ₁ * Gres T2267_H1 Complex.I σ₁) x x *
          scirc 3 3 2 (1 / 2) x T2267_y0 * Gres T2267_H1 Complex.I σ₂ T2267_y0 T2267_y0‖ ≤
      (∏ _j ∈ ({0} : Finset (Fin 1)), Complex.I.im⁻¹) * (2 * (Complex.I.im⁻¹) ^ 3)

/-! ## 3. Downstream shapes (not targets of T2267; information) -/

-- the owed pins this file serves (all stay owed; `Test/Axioms.lean:206, 207, 214, 226, 227, 232, 242` on c01b292)
#check @RBM.Univ.UNJak                -- Pins.lean:694 (UN-21 `Jak`: `jak_pointwise_good` (4 uses), `_crude` (1), `jakGridGood` (12))
#check @RBM.Univ.UNUyw                -- Pins.lean:708 (UN-22 `UywKernel`: `jakGridGood` (11), `sum_mass_window_le_of_im_green_le` (1))
#check @RBM.Univ.UNJakk               -- PinsK.lean:365 (model-generic: `lam = K.lamV sz n`)

-- consumer shape (UN-21, token check of preflight (i)): the left side of targets 2a/2b at
-- `H = ouMat (UNModel.band sz) n t ω`, `lam = sz.lam n`, `w = z`, `u = z i`, `(σ₁, σ₂) = (b₁, b₂)` is the
-- integrand of `UNJak` (`Pins.lean:700-704`) token for token
example : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n nf : ℕ) (t : ℝ)
    (ω : RBM.Gauss.Sizes.SeqΩ sz × RBM.Gauss.Ω d (sz.L n) (sz.W n)) (z : Fin nf → ℂ)
    (s : Finset (Fin nf)) (i : Fin nf) (y : Idx d (sz.L n) (sz.W n)) (b₁ b₂ : Bool),
    (∀ j, 0 < (z j).im) →
      (∏ j ∈ s, (stieltjesN (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z j)).im) *
          ‖∑ x, (Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z i) b₁ *
              Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z i) b₁) x x *
            scirc d (sz.L n) (sz.W n) (sz.lam n) x y *
              Gres (RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω) (z i) b₂ y y‖ ≤
        (∏ j ∈ s, (z j).im⁻¹) * (2 * ((z i).im⁻¹) ^ 3)

end RBM.Univ.T2267Check
