/-
Release check for T2247 (dispatcher V1, Tue Oct  6 02:47 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §50, §54, §56, §57 (1)-(2), §64 (4), §66, §69 B).
UN-16: the pointwise Hessian structure of the centred-variance Green comparison (the deterministic part of
`(EMCTE2)`): port of RBM2D `Universality/OUHessian.lean` (c9a24cf, 1242 lines; `coordD1` `:127`, `coordD2` `:133`,
`wirtSecond` `:141`, `fderiv_fderiv_stieltjesImProduct_hermitianLine` `:706`,
`wirtSecond_stieltjesImProduct_expansion` `:770`, `stieltjesImWirtingerFirst_entry_formula` `:880`,
`wirtSecond_stieltjesIm_entry_formula` `:947`, `paperL1Kernel` `:1032`, `paperL2Kernel` `:1041`,
`paperL1Kernel_eq_L1t` `:1079`, `paperL2Kernel_eq_L2t` `:1086`) to `Idx d L W`, `svarF d L W lam`, `N = (W L)^d`;
new file `RBM3D/Universality/OUHessian.lean`.  Deterministic and finite-dimensional: no pin is proved, stated or
registered; the bridges land on the merged `scirc`, `L1t`, `L2t` (`Universality/Pins.lean:612, 617, 624`, f8ad4b4,
unchanged).  The prime is the ASCII `'` of `main` (no primed name occurs here).
Section 1: the merged names the new file builds on (and the Mathlib names of the RBM2D route).
Section 2: the new vocabulary (2.1, bodies copied verbatim into namespace `RBM.Univ`, under
`open scoped Matrix.Norms.L2Operator`), the statements of the theorems of T2247 as `def T2247_<name> : Prop`
(2.2-2.5) and the instances (2.6); the library states the theorem `<name>` (namespace `RBM.Univ`, instances in
`RBM.Univ.OUHessianInst`) with exactly this body (binder names may be added; `Type*` for the check's `Type`; the
`[NeZero L] [NeZero W]` binders may be dropped by `omit … in` where the statement elaborates without them).
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2247-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! ## 1. Merged names -/

-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.stieltjesN           -- :88 (`(card)⁻¹ * (Gres M z true).trace`: through `Gres`, not `green`)
#check @RBM.Univ.scirc                -- :612 (`svarF d L W lam - ((W L)^d)⁻¹`, in `ℂ`; RBM2D `Scirc`)
#check @RBM.Univ.L1t                  -- :617 (`Gres M z b`, both signs; RBM2D `L1t` through `gSel`)
#check @RBM.Univ.L2t                  -- :624 (`(N⁻¹)^2`)
-- the fine lattice and the variance profile (T2006, 0a873f1; namespace `RBM.Gauss`, `Zd` in `RBM`)
#check @RBM.Zd                        -- `Defs/Lattice.lean:63` (51f1a17; `Fin d → ZMod L`)
#check @RBM.Gauss.Idx                 -- `Defs/Sizes.lean:46` (`Zd d (W * L)`)
#check @RBM.Gauss.card_Idx            -- `Defs/Sizes.lean:107` (`(W * L) ^ d`; replaces RBM2D `card_Idx_eq` `:1051`)
#check @RBM.Gauss.CoordF              -- `Gauss/FineModel.lean:80` (RBM2D `Coord`)
#check @RBM.Gauss.svarF               -- `Gauss/FineModel.lean:47` (RBM2D `svar L W`)
#check @RBM.Gauss.svarF_comm          -- `Gauss/FineModel.lean:54` (RBM2D `svar_comm`)
#check @RBM.Gauss.idxKey              -- `Gauss/FineModel.lean:73`
#check @RBM.Gauss.idxKey_lt_or_eq_or_lt  -- `Gauss/FineModel.lean:116`
#check @RBM.Gauss.usedCoords          -- `Hierarchy/ContractionBasic.lean:394` (e318c24)
-- the coordinate directions (`Green/FlucVanish.lean`, 40f70b9; namespace `RBM.Green`; RBM2D `Green/GreenDeriv`)
#check @RBM.Green.Bmat                -- :382 (no `NeZero` instance argument)
#check @RBM.Green.GreenDeriv_Bmat_apply      -- :389
#check @RBM.Green.GreenDeriv_mem_usedCoords  -- :396
#check @RBM.Green.GreenDeriv_Bmat_isHermitian  -- :482
-- resolvents
#check @RBM.green                     -- `Green/EntryCore.lean:34` (890a89f; `(H - z • 1)⁻¹`)
#check @RBM.Gauss.Gres                -- `Loop/GLoopFlow.lean:74` (868b3b4; `Ring.inverse (H - z_σ • 1)`)
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero  -- `Induction/ConArgDet.lean:380` (bbd22a5; RBM2D `Gauss.` same name)
#check @RBM.isUnit_sub_smul_of_isHermitian   -- `Analysis/Resolvent.lean:132` (6f9e0ba; same statement, alternative)
#check @RBM.Gauss.hasDerivAt_green_moving    -- `Gauss/FlowCalculus.lean:374` (6f99812; `Gres … true` along a moving matrix; alternative for target 2b)
#check @RBM.Graph.lwWx_Gres_conjTranspose    -- `Graph/LWWeightExp.lean:115` (975f4ff; template of the private conj bridge only; do not import `Graph`)
-- Mathlib (same Mathlib revision as RBM2D c9a24cf: lake-manifest rev 3d42585…)
#check @HasDerivAt.fun_finsetProd     -- Mathlib.Analysis.Calculus.Deriv.Mul
#check @HasDerivAt.sum                -- Mathlib.Analysis.Calculus.Deriv.Add
#check @hasFDerivAt_ringInverse       -- Mathlib.Analysis.Calculus.FDeriv.Mul
#check @analyticAt_inverse            -- Mathlib.Analysis.Analytic.Constructions
#check @Finset.analyticAt_fun_prod    -- Mathlib.Analysis.Analytic.Constructions
#check @Complex.imCLM                 -- Mathlib.Analysis.Complex.Basic
#check @Complex.ofRealCLM             -- Mathlib.Analysis.Complex.Basic
#check @ContinuousLinearMap.mulLeftRight  -- Mathlib.Analysis.Normed.Operator.Mul
#check @Matrix.nonsing_inv_eq_ringInverse  -- Mathlib.LinearAlgebra.Matrix.NonsingularInverse
#check @Matrix.isHermitian_one

namespace RBM.Univ.T2247Check

open Matrix
open RBM.Gauss
open scoped Matrix.Norms.L2Operator

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

section CoordDeriv

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- `∂_c Φ (M)`: the first directional derivative of `Φ` at `M` along `Bmat c` (RBM2D `:127`). -/
noncomputable def coordD1 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (c : CoordF d L W) : ℂ :=
  fderiv ℝ Φ M (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)

/-- `∂_c ∂_c Φ (M)`: the second directional derivative, twice along `Bmat c` (RBM2D `:133`). -/
noncomputable def coordD2 (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (c : CoordF d L W) : ℂ :=
  fderiv ℝ (fderiv ℝ Φ) M (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)
    (RBM.Green.Bmat d L W c.1 c.2.1 c.2.2)

/-- `∂_ij ∂_ji Φ` in the Wirtinger convention: `(∂_a² + ∂_b²)/4` off the diagonal, `∂_a²` on it (RBM2D `:141`). -/
noncomputable def wirtSecond (Φ : Matrix (Idx d L W) (Idx d L W) ℂ → ℂ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (i j : Idx d L W) : ℂ :=
  if i = j then coordD2 d L W Φ M (i, i, true)
  else (1 / 4 : ℝ) • (coordD2 d L W Φ M (i, j, true) + coordD2 d L W Φ M (i, j, false))

end CoordDeriv

section LineVocab

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Stieltjes factor along a Hermitian line (RBM2D `:677`, D1). -/
noncomputable def stieltjesImAlong (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (RBM.Univ.stieltjesN (H + (t : ℂ) • A) z).im

/-- Its first derivative (RBM2D `:682`, D2). -/
noncomputable def stieltjesImLineFirst (H A : Matrix n n ℂ) (z : ℂ) (t : ℝ) : ℝ :=
  (-((Fintype.card n : ℂ)⁻¹) *
    (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace).im

/-- Its second derivative at the base point (RBM2D `:688`, D3). -/
noncomputable def stieltjesImLineSecond (H A : Matrix n n ℂ) (z : ℂ) : ℝ :=
  (2 * (Fintype.card n : ℂ)⁻¹ *
    (RBM.green H z * A * RBM.green H z * A * RBM.green H z).trace).im

/-- The finite-product second line variation (RBM2D `:694`, D4). -/
noncomputable def stieltjesImProductLineSecond {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ) (z : ι → ℂ) : ℝ :=
  ∑ i ∈ s,
    ((∏ j ∈ s.erase i, stieltjesImAlong H A (z j) 0) *
        stieltjesImLineSecond H A (z i) +
      (∑ j ∈ s.erase i,
        (∏ k ∈ (s.erase i).erase j, stieltjesImAlong H A (z k) 0) *
          stieltjesImLineFirst H A (z j) 0) *
        stieltjesImLineFirst H A (z i) 0)

/-- The signed resolvent family `{G, G*}` (RBM2D `:1017`, D5). -/
noncomputable def signedGreen (H : Matrix n n ℂ) (z : ℂ) (σ : Bool) : Matrix n n ℂ :=
  if σ then RBM.green H z else RBM.green H ((starRingEnd ℂ) z)

end LineVocab

section IdxVocab

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The first Wirtinger derivative of `Im m` through the real-coordinate derivatives along `Bmat`
(RBM2D `:865`, D9). -/
noncomputable def stieltjesImWirtingerFirst (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (i j : Idx d L W) : ℂ :=
  if i = j then
    (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
      (RBM.Green.Bmat d L W i i true) : ℝ)
  else
    (2⁻¹ : ℂ) *
      ((fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
          (RBM.Green.Bmat d L W i j true) : ℝ) -
        Complex.I *
          (fderiv ℝ (fun K : Matrix (Idx d L W) (Idx d L W) ℂ => (RBM.Univ.stieltjesN K z).im) H
            (RBM.Green.Bmat d L W i j false) : ℝ))

/-- `S°_{ab} = S_{ab} - N⁻¹` with `S = svarF d L W lam` (RBM2D `:1028`, D10: `svar L W` ↦ `svarF d L W lam`;
`lam = sz.lam n` for the band model, `lam = K.lamV sz n` model-generic, `0` for block Anderson). -/
noncomputable def centeredVarianceEntry (lam : ℝ) (a b : Idx d L W) : ℝ :=
  svarF d L W lam a b - (Fintype.card (Idx d L W) : ℝ)⁻¹

/-- The pointwise `L₁` kernel of (2.25) (RBM2D `:1032`, D11). -/
noncomputable def paperL1Kernel (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx d L W) : ℂ)⁻¹ *
      ∑ a : Idx d L W, ∑ b : Idx d L W,
        ((signedGreen H z σ * signedGreen H z σ) a a) *
          (centeredVarianceEntry d L W lam a b : ℂ) * (signedGreen H z τ) b b‖

/-- The pointwise `L₂` kernel of (2.25) (RBM2D `:1041`, D12). -/
noncomputable def paperL2Kernel (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) : ℝ :=
  ∑ σ : Bool, ∑ τ : Bool,
    ‖(Fintype.card (Idx d L W) : ℂ)⁻¹ *
      (Fintype.card (Idx d L W) : ℂ)⁻¹ *
      ∑ a : Idx d L W, ∑ b : Idx d L W,
        ((signedGreen H z₁ σ * signedGreen H z₁ σ) a b) *
          (centeredVarianceEntry d L W lam a b : ℂ) *
          ((signedGreen H z₂ τ * signedGreen H z₂ τ) b a)‖

end IdxVocab

/-! ### 2.2 Target 1: the coordinate directions (RBM2D `:52-117`) -/

/-- `Bmat_swap_true` (RBM2D `:59`; `omit [NeZero L] [NeZero W]`). -/
def T2247_Bmat_swap_true : Prop :=
  ∀ (d L W : ℕ) (i j : Idx d L W),
    RBM.Green.Bmat d L W j i true = RBM.Green.Bmat d L W i j true

/-- `Bmat_swap_false` (RBM2D `:74`; `omit [NeZero L] [NeZero W]`). -/
def T2247_Bmat_swap_false : Prop :=
  ∀ (d L W : ℕ) {i j : Idx d L W}, i ≠ j →
    RBM.Green.Bmat d L W j i false = -RBM.Green.Bmat d L W i j false

/-- `Bmat_isHermitian_of_ne_or` (RBM2D `:92`). -/
def T2247_Bmat_isHermitian_of_ne_or : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {i j : Idx d L W} {b : Bool}, (i ≠ j ∨ b = true) →
    (RBM.Green.Bmat d L W i j b).IsHermitian

/-! ### 2.3 Target 2: the Hessian along a Hermitian line (RBM2D `:150-762`; any finite index type) -/

/-- `hasDerivAt_deriv_finset_product_expansion` (RBM2D `:156`; target 2a). -/
def T2247_hasDerivAt_deriv_finset_product_expansion : Prop :=
  ∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (f fp : ι → ℝ → ℝ) (fpp : ι → ℝ),
    (∀ i ∈ s, ∀ t, HasDerivAt (f i) (fp i t) t) →
    (∀ i ∈ s, HasDerivAt (fp i) (fpp i) 0) →
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => ∏ i ∈ s, f i u) t)
      (∑ i ∈ s,
        ((∏ j ∈ s.erase i, f j 0) * fpp i +
          (∑ j ∈ s.erase i,
            (∏ k ∈ (s.erase i).erase j, f k 0) * fp j 0) * fp i 0)) 0

/-- `hasDerivAt_green_hermitianLine` (RBM2D `:603`; target 2b). -/
def T2247_hasDerivAt_green_hermitianLine : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ},
    H.IsHermitian → A.IsHermitian → ∀ (z : ℂ), z.im ≠ 0 → ∀ (t : ℝ),
    HasDerivAt (fun s : ℝ => RBM.green (H + (s : ℂ) • A) z)
      (-(RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z)) t

/-- `hasDerivAt_stieltjesN_hermitianLine` (RBM2D `:628`; target 2c; the merged `stieltjesN` is `Gres`-based, so the
RBM2D `rfl` at `:640` becomes the bridge `OUHessian_Gres_true`). -/
def T2247_hasDerivAt_stieltjesN_hermitianLine : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ},
    H.IsHermitian → A.IsHermitian → ∀ (z : ℂ), z.im ≠ 0 → ∀ (t : ℝ),
    HasDerivAt (fun s : ℝ => RBM.Univ.stieltjesN (H + (s : ℂ) • A) z)
      (-((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z).trace) t

/-- `hasDerivAt_stieltjesFirstVariation` (RBM2D `:646`; target 2d). -/
def T2247_hasDerivAt_stieltjesFirstVariation : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {H A : Matrix n n ℂ},
    H.IsHermitian → A.IsHermitian → ∀ (z : ℂ), z.im ≠ 0 → ∀ (t : ℝ),
    HasDerivAt
      (fun s : ℝ => -((Fintype.card n : ℂ)⁻¹) *
        (RBM.green (H + (s : ℂ) • A) z * A * RBM.green (H + (s : ℂ) • A) z).trace)
      (2 * (Fintype.card n : ℂ)⁻¹ *
        (RBM.green (H + (t : ℂ) • A) z * A * RBM.green (H + (t : ℂ) • A) z * A *
          RBM.green (H + (t : ℂ) • A) z).trace) t

/-- `fderiv_fderiv_stieltjesImProduct_hermitianLine` (RBM2D `:706`; target 2e). -/
def T2247_fderiv_fderiv_stieltjesImProduct_hermitianLine : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] {ι : Type} [DecidableEq ι]
    (s : Finset ι) (H A : Matrix n n ℂ), H.IsHermitian → A.IsHermitian →
    ∀ (z : ι → ℂ), (∀ i ∈ s, (z i).im ≠ 0) →
      fderiv ℝ (fderiv ℝ (fun K : Matrix n n ℂ =>
        ((∏ i ∈ s, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ))) H A A =
        ((stieltjesImProductLineSecond s H A z : ℝ) : ℂ)

/-! ### 2.4 Target 3: the Wirtinger Hessian and the first Wirtinger derivative (RBM2D `:764-1006`) -/

/-- `wirtSecond_stieltjesImProduct_expansion` (RBM2D `:770`; target 3a). -/
def T2247_wirtSecond_stieltjesImProduct_expansion : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {ι : Type} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ι → ℂ), (∀ i ∈ s, (z i).im ≠ 0) → ∀ (a b : Idx d L W),
    wirtSecond d L W
        (fun K => ((∏ i ∈ s, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) H a b =
      if a = b then
        (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a a true) z : ℂ)
      else
        (1 / 4 : ℝ) •
          ((stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b true) z : ℂ) +
            (stieltjesImProductLineSecond s H (RBM.Green.Bmat d L W a b false) z : ℂ))

/-- `stieltjesImWirtingerFirst_entry_formula` (RBM2D `:880`; target 3b). -/
def T2247_stieltjesImWirtingerFirst_entry_formula : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ℂ), z.im ≠ 0 → ∀ (i j : Idx d L W),
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (starRingEnd ℂ) ((RBM.green H z * RBM.green H z) i j))

/-- `stieltjesImWirtingerFirst_adjoint_formula` (RBM2D `:935`; target 3c; the RBM2D `Gsig_conjTranspose` at
`:924` becomes the private bridge `OUHessian_green_conj`). -/
def T2247_stieltjesImWirtingerFirst_adjoint_formula : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ℂ), z.im ≠ 0 → ∀ (i j : Idx d L W),
    stieltjesImWirtingerFirst d L W H z i j =
      (Complex.I * (Fintype.card (Idx d L W) : ℂ)⁻¹ / 2) *
        ((RBM.green H z * RBM.green H z) j i -
          (RBM.green H ((starRingEnd ℂ) z) * RBM.green H ((starRingEnd ℂ) z)) j i)

/-- `wirtSecond_stieltjesIm_entry_formula` (RBM2D `:947`; target 3d). -/
def T2247_wirtSecond_stieltjesIm_entry_formula : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ℂ), z.im ≠ 0 → ∀ (i j : Idx d L W),
    wirtSecond d L W (fun K => ((RBM.Univ.stieltjesN K z).im : ℂ)) H i j =
      ((((Fintype.card (Idx d L W) : ℂ)⁻¹) *
        ((RBM.green H z * RBM.green H z) i i * (RBM.green H z) j j +
          (RBM.green H z * RBM.green H z) j j * (RBM.green H z) i i)).im : ℂ)

/-! ### 2.5 Target 4: the kernels and the bridges to the merged `scirc`, `L1t`, `L2t` (RBM2D `:1010-1093`) -/

/-- `centeredVarianceEntry_symm` (RBM2D `:1055`; `svar_comm` ↦ `svarF_comm`; target 4a). -/
def T2247_centeredVarianceEntry_symm : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (a b : Idx d L W),
    centeredVarianceEntry d L W lam a b = centeredVarianceEntry d L W lam b a

/-- `centeredVarianceEntry_cast` (RBM2D `:1061`; `Scirc L W` ↦ the merged `scirc d L W lam`, `Pins.lean:612`;
`card_Idx` + `push_cast`; target 4b). -/
def T2247_centeredVarianceEntry_cast : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (a b : Idx d L W),
    ((centeredVarianceEntry d L W lam a b : ℝ) : ℂ) = RBM.Univ.scirc d L W lam a b

/-- `signedGreen_eq_Gres` (replaces RBM2D `signedGreen_eq_gSel` `:1069`: RBM3D has no `gSel`, the merged `L1t`/`L2t`
read `Gres M z b`; true for every `H`: both sides are the nonsingular inverse of `H - z` resp. `H - z̄`,
`Matrix.nonsing_inv_eq_ringInverse`; target 4c). -/
def T2247_signedGreen_eq_Gres : Prop :=
  ∀ {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) (σ : Bool),
    signedGreen H z σ = RBM.Gauss.Gres H z σ

/-- `paperL1Kernel_eq_L1t` (RBM2D `:1079`; the RBM2D `IsHermitian` hypothesis is not needed and is dropped;
target 4d). -/
def T2247_paperL1Kernel_eq_L1t : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ),
    paperL1Kernel d L W lam H z = RBM.Univ.L1t d L W lam H z

/-- `paperL2Kernel_eq_L2t` (RBM2D `:1086`; `L2t` writes `(N⁻¹)^2`, `sq`; target 4e). -/
def T2247_paperL2Kernel_eq_L2t : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ),
    paperL2Kernel d L W lam H z₁ z₂ = RBM.Univ.L2t d L W lam H z₁ z₂

/-! ### 2.6 Target 5: instances (namespace `RBM.Univ.OUHessianInst`; `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`lam = 1/2`, `H = 1`, `z = I`, `2I`, sites `x0 = 0`, `x1 = Pi.single 0 1`) -/

/-- The two sites (the library defines `OUHessianInst.x0`, `OUHessianInst.x1` with these bodies). -/
def T2247_x0 : Idx 3 3 2 := 0

def T2247_x1 : Idx 3 3 2 := Pi.single 0 1

/-- `inst_directions` (RBM2D `:1182`). -/
def T2247_inst_directions : Prop :=
  T2247_x0 ≠ T2247_x1 ∧
    RBM.Green.Bmat 3 3 2 T2247_x1 T2247_x0 true = RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x1 true ∧
    RBM.Green.Bmat 3 3 2 T2247_x1 T2247_x0 false = -RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x1 false ∧
    (RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x1 false).IsHermitian ∧
    (RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x0 true).IsHermitian

/-- `inst_entry` (RBM2D `:1104`): `paperL1Kernel = L1t` and the Hessian entry formula at `(x0, x1)`. -/
def T2247_inst_entry : Prop :=
  paperL1Kernel 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I =
      RBM.Univ.L1t 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I ∧
    wirtSecond 3 3 2 (fun K => ((RBM.Univ.stieltjesN K Complex.I).im : ℂ))
        (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) T2247_x0 T2247_x1 =
      ((((Fintype.card (Idx 3 3 2) : ℂ)⁻¹) *
        ((RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
            RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) T2247_x0 T2247_x0 *
          (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) T2247_x1 T2247_x1 +
         (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
            RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) T2247_x1 T2247_x1 *
          (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) T2247_x0 T2247_x0)).im : ℂ)

/-- `inst_product` (RBM2D `:1124`, the `if` evaluated at `x0 ≠ x1`): the Wirtinger Hessian of `Im m(I) · Im m(2I)`. -/
def T2247_inst_product : Prop :=
  wirtSecond 3 3 2
      (fun K => ((∏ i ∈ (Finset.univ : Finset (Fin 2)),
        (RBM.Univ.stieltjesN K (![Complex.I, 2 * Complex.I] i)).im : ℝ) : ℂ))
      (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) T2247_x0 T2247_x1 =
    (1 / 4 : ℝ) •
      ((stieltjesImProductLineSecond (Finset.univ : Finset (Fin 2))
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          (RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x1 true) ![Complex.I, 2 * Complex.I] : ℂ) +
        (stieltjesImProductLineSecond (Finset.univ : Finset (Fin 2))
          (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ)
          (RBM.Green.Bmat 3 3 2 T2247_x0 T2247_x1 false) ![Complex.I, 2 * Complex.I] : ℂ))

/-- `inst_wirtFirst` (RBM2D `:1194-1200`): the adjoint form of the first Wirtinger derivative at `(x0, x1)`. -/
def T2247_inst_wirtFirst : Prop :=
  stieltjesImWirtingerFirst 3 3 2 (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I T2247_x0 T2247_x1 =
    (Complex.I * (Fintype.card (Idx 3 3 2) : ℂ)⁻¹ / 2) *
      ((RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I *
          RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I) T2247_x1 T2247_x0 -
        (RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) ((starRingEnd ℂ) Complex.I) *
          RBM.green (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) ((starRingEnd ℂ) Complex.I)) T2247_x1 T2247_x0)

/-- `inst_kernels` (RBM2D `:1204-1216`): the size, `S°` symmetric and equal to `scirc`, the conjugate tag, `L₂`. -/
def T2247_inst_kernels : Prop :=
  Fintype.card (Idx 3 3 2) = 216 ∧
    centeredVarianceEntry 3 3 2 (1 / 2) T2247_x0 T2247_x1 =
      centeredVarianceEntry 3 3 2 (1 / 2) T2247_x1 T2247_x0 ∧
    ((centeredVarianceEntry 3 3 2 (1 / 2) T2247_x0 T2247_x1 : ℝ) : ℂ) =
      RBM.Univ.scirc 3 3 2 (1 / 2) T2247_x0 T2247_x1 ∧
    signedGreen (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I false =
      RBM.Gauss.Gres (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I false ∧
    paperL2Kernel 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I (2 * Complex.I) =
      RBM.Univ.L2t 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I (2 * Complex.I)

/-- `inst_green_line` (RBM2D `:1157`): the resolvent line derivative at `n = Fin 2`, `H = A = 1`, `z = I`, `t = 0`. -/
def T2247_inst_green_line : Prop :=
  HasDerivAt
    (fun s : ℝ => RBM.green
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) Complex.I)
    (-(RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I))
    0

/-- `inst_stieltjes_line` (RBM2D `:1162`): the Stieltjes line derivative at the same data (the `Gres` bridge
at a concrete matrix). -/
def T2247_inst_stieltjes_line : Prop :=
  HasDerivAt
    (fun s : ℝ => RBM.Univ.stieltjesN
      ((1 : Matrix (Fin 2) (Fin 2) ℂ) + (s : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) Complex.I)
    (-((Fintype.card (Fin 2) : ℂ)⁻¹) *
      (RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I *
        (1 : Matrix (Fin 2) (Fin 2) ℂ) *
        RBM.green ((1 : Matrix (Fin 2) (Fin 2) ℂ) + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          Complex.I).trace)
    0

/-! ## 3. Downstream shapes (not targets of T2247; information) -/

-- the owed pins this file serves (all stay owed; `Test/Axioms.lean:199, 205-208` on 8256045)
#check @RBM.Univ.UNEMCTE2             -- Pins.lean:669 (hypotheses on `L1t d … (sz.lam n) (ouMat …)`, `L2t`; UN-15, UN-17, UN-18)
#check @RBM.Univ.UNEMCTE2Row          -- Pins.lean:797 (UN-18)
#check @RBM.Univ.UNJakUywRow          -- Pins.lean:805 (UN-21, UN-23: `signedGreen_eq_Gres` once each)
#check @RBM.Univ.UNUnivMainRow        -- Pins.lean:745 (UN-24)
#check @RBM.Univ.UNEMCTE2k            -- PinsK.lean:345 (model-generic: `L1t d … (K.lamV sz n) (ouMatC …)`)

-- consumer shape (UN-18, token check of preflight (i)): the kernel bridge at the band data
example : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (z : ℂ), paperL1Kernel d (sz.L n) (sz.W n) (sz.lam n) H z = RBM.Univ.L1t d (sz.L n) (sz.W n) (sz.lam n) H z

end RBM.Univ.T2247Check
