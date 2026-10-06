/-
Release check for T2253 (dispatcher V1, Tue Oct  6 03:42 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §17, §20,
§29, §45 (O2), §50, §54, §56, §57 (1)-(2), §64 (4), §66, §69 B).
UN-17: the centred contraction of the Wirtinger Hessian of `∏ Im m(z_i)` against `S° = S - N⁻¹` and its bound
through the positive kernels `L₁`, `L₂` of `(EMCTE2)` (RBM2D paper 1-2:364-376): port of RBM2D
`Universality/OUContraction.lean` (c9a24cf, 1109 lines; `paperK1Contraction` `:49`, `paperK2Contraction` `:56`,
`centeredVariance_single_contraction_eq` `:65`, `centeredVariance_wirtingerFirst_product_eq` `:202`,
`centeredVariance_wirtProduct_contraction_eq` `:803`, `centeredVariance_wirtProduct_kernel_bound` `:985`) to
`Idx d L W`, `svarF d L W lam` (through the merged `centeredVarianceEntry d L W lam`), on top of the merged UN-16
vocabulary (`Universality/OUHessian.lean`, T2247, 398ebe4).  New file `RBM3D/Universality/OUContraction.lean`.
Deterministic and finite-dimensional: no pin is proved, stated or registered.  The prime is the ASCII `'` of
`main` (no primed name occurs here).
Section 1: the merged names the new file builds on (and the Mathlib names of the RBM2D route).
Section 2: the new vocabulary (2.1, bodies copied verbatim into namespace `RBM.Univ`), the statement bodies
`T2253_<name>_at` (2.2, Prop-valued vocabulary), the statements of the theorems of T2253 as
`def T2253_<name> : Prop` (2.3-2.5) and the instances (2.6).  The library states the theorem `<name>` (namespace
`RBM.Univ`; instances in `RBM.Univ.OUContractionInst`) with exactly this statement after unfolding the `_at` bodies
(binder names may be added; `Type*` for the check's `Type`); acceptance: the defeq examples
`example : RBM.Univ.T2253Check.T2253_<name> := @RBM.Univ.<name>` in the prove report's scratch check.
Section 3: downstream shapes (not targets; information).
Definitions, statements and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2253-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! ## 1. Merged names -/

-- UN-16 (`Universality/OUHessian.lean`, T2247, merged 398ebe4; namespace `RBM.Univ`)
#check @RBM.Univ.Bmat_swap_true                -- :134 (RBM2D OUContraction `:526`)
#check @RBM.Univ.Bmat_swap_false               -- :149 (`:528`)
#check @RBM.Univ.Bmat_isHermitian_of_ne_or     -- :167
#check @RBM.Univ.coordD2                       -- :208
#check @RBM.Univ.wirtSecond                    -- :216
#check @RBM.Univ.stieltjesImAlong              -- :757 (`stieltjesN`-based; unfolded only at `t = 0`, RBM2D `:705, :740`)
#check @RBM.Univ.stieltjesImLineFirst          -- :762 (`RBM.green`-based)
#check @RBM.Univ.stieltjesImLineSecond         -- :768
#check @RBM.Univ.stieltjesImProductLineSecond  -- :774
#check @RBM.Univ.wirtSecond_stieltjesImProduct_expansion  -- :850
#check @RBM.Univ.stieltjesImWirtingerFirst     -- :945
#check @RBM.Univ.stieltjesImWirtingerFirst_entry_formula   -- :960
#check @RBM.Univ.stieltjesImWirtingerFirst_adjoint_formula -- :1015
#check @RBM.Univ.wirtSecond_stieltjesIm_entry_formula      -- :1027
#check @RBM.Univ.signedGreen                   -- :1097 (`if σ then green H z else green H (conj z)`)
#check @RBM.Univ.signedGreen_eq_Gres           -- :1102 (every `H`)
#check @RBM.Univ.centeredVarianceEntry         -- :1115 (`lam` after `d L W`)
#check @RBM.Univ.paperL1Kernel                 -- :1119
#check @RBM.Univ.paperL2Kernel                 -- :1128
#check @RBM.Univ.centeredVarianceEntry_symm    -- :1138
#check @RBM.Univ.centeredVarianceEntry_cast    -- :1143
#check @RBM.Univ.paperL1Kernel_eq_L1t          -- :1150 (no `IsHermitian` argument)
#check @RBM.Univ.paperL2Kernel_eq_L2t          -- :1157 (no `IsHermitian` argument)
#check @RBM.Univ.OUHessianInst.x0              -- :1176 (`Idx 3 3 2`, `0`)
#check @RBM.Univ.OUHessianInst.x1              -- :1179 (`Pi.single 0 1`)
#check @RBM.Univ.OUHessianInst.x0_ne_x1        -- :1181
-- UN-03a (`Universality/InjSum.lean`, T2178, merged 4c52041; namespace `RBM.Univ`)
#check @RBM.Univ.stieltjesN_im_eq_normalized_specWeight  -- :196 (same statement as RBM2D; RBM2D OUContraction `:887`)
-- UN-01 (`Universality/Pins.lean`, T2174, merged f8ad4b4; namespace `RBM.Univ`)
#check @RBM.Univ.stieltjesN                    -- :88 (`(card)⁻¹ * (Gres M z true).trace`)
#check @RBM.Univ.scirc                         -- :612
#check @RBM.Univ.L1t                           -- :617 (`ℝ`-valued)
#check @RBM.Univ.L2t                           -- :624
-- model vocabulary (T2006, 0a873f1; T2061, 40f70b9; T2029, 890a89f; T2013, 868b3b4)
#check @RBM.Gauss.Idx                          -- `Defs/Sizes.lean:46` (`Zd d (W * L)`, `Zd` an `abbrev`, `Defs/Lattice.lean:63`)
#check @RBM.Gauss.card_Idx                     -- `Defs/Sizes.lean:107` (`(W * L) ^ d`)
#check @RBM.Gauss.svarF                        -- `Gauss/FineModel.lean:47`
#check @RBM.Gauss.svarF_comm                   -- `Gauss/FineModel.lean:54`
#check @RBM.Green.Bmat                         -- `Green/FlucVanish.lean:382`
#check @RBM.green                              -- `Green/EntryCore.lean:34`
#check @RBM.Gauss.Gres                         -- `Loop/GLoopFlow.lean:74`
-- Mathlib (lake-manifest mathlib `v4.34.0`, as T2247)
#check @Complex.abs_im_le_norm                 -- Mathlib.Analysis.Complex.Norm
#check @norm_sum_le                            -- Mathlib.Analysis.Normed.Group.Basic
#check @Finset.prod_nonneg                     -- Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
#check @Matrix.isHermitian_diagonal_of_self_adjoint  -- Mathlib.LinearAlgebra.Matrix.Hermitian
#check @Matrix.isHermitian_one                 -- Mathlib.LinearAlgebra.Matrix.Hermitian
#check @Matrix.trace_single_mul                -- Mathlib.LinearAlgebra.Matrix.Trace
#check @Matrix.conjTranspose_mul               -- Mathlib.LinearAlgebra.Matrix.ConjTranspose
#check @Matrix.conjTranspose_nonsing_inv       -- Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace RBM.Univ.T2253Check

open RBM.Gauss

/-! ## 2. New vocabulary and statements (namespace `RBM.Univ` in the library) -/

/-! ### 2.1 Vocabulary (copied verbatim into the library, namespace `RBM.Univ`) -/

section Defs

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The `K₁` contraction of (2.25) (RBM2D `:49`; `lam` after `d L W`). -/
noncomputable def paperK1Contraction (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (σ τ : Bool) : ℂ :=
  (Fintype.card (Idx d L W) : ℂ)⁻¹ *
    ∑ a : Idx d L W, ∑ b : Idx d L W,
      ((RBM.Univ.signedGreen H z σ * RBM.Univ.signedGreen H z σ) a a) *
        (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) * (RBM.Univ.signedGreen H z τ) b b

/-- The `K₂` contraction of (2.25) (RBM2D `:56`; `lam` after `d L W`). -/
noncomputable def paperK2Contraction (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ)
    (σ τ : Bool) : ℂ :=
  (Fintype.card (Idx d L W) : ℂ)⁻¹ * (Fintype.card (Idx d L W) : ℂ)⁻¹ *
    ∑ a : Idx d L W, ∑ b : Idx d L W,
      ((RBM.Univ.signedGreen H z₁ σ * RBM.Univ.signedGreen H z₁ σ) a b) *
        (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
          ((RBM.Univ.signedGreen H z₂ τ * RBM.Univ.signedGreen H z₂ τ) b a)

end Defs

/-! ### 2.2 Statement bodies (Prop-valued vocabulary of this check only; not library names) -/

/-- Body of target 1 (RBM2D `:65-71`). -/
def T2253_single_at (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) : Prop :=
  (∑ a : Idx d L W, ∑ b : Idx d L W,
    (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
      RBM.Univ.wirtSecond d L W (fun K => ((RBM.Univ.stieltjesN K z).im : ℂ)) H a b) =
    ((2 * (paperK1Contraction d L W lam H z true true).im : ℝ) : ℂ)

/-- Body of target 2 (RBM2D `:202-212`). -/
def T2253_wirtingerFirst_product_at (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ) : Prop :=
  (∑ a : Idx d L W, ∑ b : Idx d L W,
    (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
      RBM.Univ.stieltjesImWirtingerFirst d L W H z₁ a b *
        RBM.Univ.stieltjesImWirtingerFirst d L W H z₂ b a) =
    -(1 / 4 : ℂ) *
      (paperK2Contraction d L W lam H z₁ z₂ true true -
        paperK2Contraction d L W lam H z₁ z₂ true false -
        paperK2Contraction d L W lam H z₁ z₂ false true +
        paperK2Contraction d L W lam H z₁ z₂ false false)

/-- Body of target 3 (RBM2D `:803-822`). -/
def T2253_contraction_at (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ι → ℂ) : Prop :=
  (∑ a : Idx d L W, ∑ b : Idx d L W,
    (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
      RBM.Univ.wirtSecond d L W
        (fun K => ((∏ i ∈ s, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) H a b) =
    (∑ i ∈ s,
      ((∏ j ∈ s.erase i, (RBM.Univ.stieltjesN H (z j)).im : ℝ) : ℂ) *
        ((2 * (paperK1Contraction d L W lam H (z i) true true).im : ℝ) : ℂ)) +
    ∑ i ∈ s, ∑ j ∈ s.erase i,
      ((∏ k ∈ (s.erase i).erase j, (RBM.Univ.stieltjesN H (z k)).im : ℝ) : ℂ) *
        (-(1 / 4 : ℂ) *
          (paperK2Contraction d L W lam H (z i) (z j) true true -
            paperK2Contraction d L W lam H (z i) (z j) true false -
            paperK2Contraction d L W lam H (z i) (z j) false true +
            paperK2Contraction d L W lam H (z i) (z j) false false))

/-- Body of target 4 (RBM2D `:985-997`; `paperL1Kernel`, `paperL2Kernel` of UN-16). -/
def T2253_kernel_bound_at (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ι → ℂ) : Prop :=
  ‖∑ a : Idx d L W, ∑ b : Idx d L W,
      (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
        RBM.Univ.wirtSecond d L W
          (fun K => ((∏ i ∈ s, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
    (∑ i ∈ s,
      (∏ j ∈ s.erase i, (RBM.Univ.stieltjesN H (z j)).im) *
        RBM.Univ.paperL1Kernel d L W lam H (z i)) +
    ∑ i ∈ s, ∑ j ∈ s.erase i,
      (∏ k ∈ (s.erase i).erase j, (RBM.Univ.stieltjesN H (z k)).im) *
        RBM.Univ.paperL2Kernel d L W lam H (z i) (z j)

/-- Body of target 5 (new; target 4 rewritten with `paperL1Kernel_eq_L1t`, `paperL2Kernel_eq_L2t`: the merged
`L1t`, `L2t` of `UNEMCTE2`, `Pins.lean:676, 681`). -/
def T2253_kernel_bound_Lt_at (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι]
    (s : Finset ι) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ι → ℂ) : Prop :=
  ‖∑ a : Idx d L W, ∑ b : Idx d L W,
      (RBM.Univ.centeredVarianceEntry d L W lam a b : ℂ) *
        RBM.Univ.wirtSecond d L W
          (fun K => ((∏ i ∈ s, (RBM.Univ.stieltjesN K (z i)).im : ℝ) : ℂ)) H a b‖ ≤
    (∑ i ∈ s,
      (∏ j ∈ s.erase i, (RBM.Univ.stieltjesN H (z j)).im) *
        RBM.Univ.L1t d L W lam H (z i)) +
    ∑ i ∈ s, ∑ j ∈ s.erase i,
      (∏ k ∈ (s.erase i).erase j, (RBM.Univ.stieltjesN H (z k)).im) *
        RBM.Univ.L2t d L W lam H (z i) (z j)

/-! ### 2.3 Targets 1-3: the contraction identities (RBM2D `:65-882`) -/

/-- `centeredVariance_single_contraction_eq` (RBM2D `:65`; target 1). -/
def T2253_centeredVariance_single_contraction_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ),
    H.IsHermitian → ∀ (z : ℂ), z.im ≠ 0 → T2253_single_at d L W lam H z

/-- `centeredVariance_wirtingerFirst_product_eq` (RBM2D `:202`; target 2). -/
def T2253_centeredVariance_wirtingerFirst_product_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ),
    H.IsHermitian → ∀ (z₁ z₂ : ℂ), z₁.im ≠ 0 → z₂.im ≠ 0 →
      T2253_wirtingerFirst_product_at d L W lam H z₁ z₂

/-- `centeredVariance_wirtProduct_contraction_eq` (RBM2D `:803`; target 3). -/
def T2253_centeredVariance_wirtProduct_contraction_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ι → ℂ), (∀ i ∈ s, (z i).im ≠ 0) → T2253_contraction_at d L W lam s H z

/-! ### 2.4 Intermediate statements (RBM2D private `OUContraction_K1_conj_eq_false_false` `:900`,
`OUContraction_K1_im_abs_le` `:924`, `OUContraction_K2_abs_le` `:948`; public here, names as spelled) -/

/-- `paperK1Contraction_conj` (RBM2D `:900`; `RBM.Gsig_conjTranspose` ↦ private conj bridge; target 4a). -/
def T2253_paperK1Contraction_conj : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ),
    H.IsHermitian → ∀ (z : ℂ),
      (starRingEnd ℂ) (paperK1Contraction d L W lam H z true true) =
        paperK1Contraction d L W lam H z false false

/-- `paperK1Contraction_im_abs_le` (RBM2D `:924`; target 4b). -/
def T2253_paperK1Contraction_im_abs_le : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ),
    H.IsHermitian → ∀ (z : ℂ),
      ‖((2 * (paperK1Contraction d L W lam H z true true).im : ℝ) : ℂ)‖ ≤
        RBM.Univ.paperL1Kernel d L W lam H z

/-- `paperK2Contraction_abs_le` (RBM2D `:948`; no Hermitian hypothesis, as RBM2D; target 4c). -/
def T2253_paperK2Contraction_abs_le : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z₁ z₂ : ℂ),
    ‖-(1 / 4 : ℂ) *
        (paperK2Contraction d L W lam H z₁ z₂ true true -
          paperK2Contraction d L W lam H z₁ z₂ true false -
          paperK2Contraction d L W lam H z₁ z₂ false true +
          paperK2Contraction d L W lam H z₁ z₂ false false)‖ ≤
      RBM.Univ.paperL2Kernel d L W lam H z₁ z₂

/-! ### 2.5 Targets 4-5: the kernel bound (RBM2D `:985`) and its `L1t`/`L2t` form (new) -/

/-- `centeredVariance_wirtProduct_kernel_bound` (RBM2D `:985`; target 4d). -/
def T2253_centeredVariance_wirtProduct_kernel_bound : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ι → ℂ), (∀ i ∈ s, 0 < (z i).im) → T2253_kernel_bound_at d L W lam s H z

/-- `centeredVariance_wirtProduct_kernel_bound_Lt` (new; target 4d + `paperL1Kernel_eq_L1t`,
`paperL2Kernel_eq_L2t`; target 5). -/
def T2253_centeredVariance_wirtProduct_kernel_bound_Lt : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (lam : ℝ) {ι : Type} [DecidableEq ι] (s : Finset ι)
    (H : Matrix (Idx d L W) (Idx d L W) ℂ), H.IsHermitian →
    ∀ (z : ι → ℂ), (∀ i ∈ s, 0 < (z i).im) → T2253_kernel_bound_Lt_at d L W lam s H z

/-! ### 2.6 Target 6: instances (namespace `RBM.Univ.OUContractionInst`; `d = 3`, `L = 3`, `W = 2` (`N = 216`),
`lam = 1/2`, `H = 1` and the non-scalar `diagH`, `z = I`, `2I`, `ι = Fin 2`, `s = univ`) -/

/-- The non-scalar real diagonal matrix (the library defines `OUContractionInst.diagH` with this body; RBM2D
`:1056` at `Idx 3 3` used `k.1.val % 7`). -/
noncomputable def T2253_diagH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.diagonal (fun k : Idx 3 3 2 => ((((ZMod.val (k 0) : ℕ) : ℝ) / 3 : ℝ) : ℂ))

/-- `diagH_herm` (RBM2D `:1059`). -/
def T2253_diagH_herm : Prop := Matrix.IsHermitian T2253_diagH

/-- `diagH_nonscalar` (RBM2D `:1064`, at the UN-16 sites `x0 = 0`, `x1 = Pi.single 0 1`). -/
def T2253_diagH_nonscalar : Prop :=
  T2253_diagH RBM.Univ.OUHessianInst.x0 RBM.Univ.OUHessianInst.x0 ≠
    T2253_diagH RBM.Univ.OUHessianInst.x1 RBM.Univ.OUHessianInst.x1

/-- `inst_single` (RBM2D `:1085`): target 1 at `H = 1`, `z = I`. -/
def T2253_inst_single : Prop :=
  T2253_single_at 3 3 2 (1 / 2) (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I

/-- `inst_single_diag` (RBM2D `:1090`): target 1 at `H = diagH`, `z = I`. -/
def T2253_inst_single_diag : Prop :=
  T2253_single_at 3 3 2 (1 / 2) T2253_diagH Complex.I

/-- `inst_wirtFirst_product` (RBM2D `:1094` at `H = 1`; here at `diagH`): target 2, `z₁ = I`, `z₂ = 2I`. -/
def T2253_inst_wirtFirst_product : Prop :=
  T2253_wirtingerFirst_product_at 3 3 2 (1 / 2) T2253_diagH Complex.I (2 * Complex.I)

/-- `inst_contraction` (RBM2D `:1077` at `H = 1`; here at `diagH`): target 3. -/
def T2253_inst_contraction : Prop :=
  T2253_contraction_at 3 3 2 (1 / 2) (Finset.univ : Finset (Fin 2)) T2253_diagH
    ![Complex.I, 2 * Complex.I]

/-- `inst_kernel_bound` (RBM2D `:1069`): target 4d at `H = 1`. -/
def T2253_inst_kernel_bound : Prop :=
  T2253_kernel_bound_at 3 3 2 (1 / 2) (Finset.univ : Finset (Fin 2))
    (1 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) ![Complex.I, 2 * Complex.I]

/-- `inst_kernel_bound_Lt` (new): target 5 at `H = diagH`. -/
def T2253_inst_kernel_bound_Lt : Prop :=
  T2253_kernel_bound_Lt_at 3 3 2 (1 / 2) (Finset.univ : Finset (Fin 2)) T2253_diagH
    ![Complex.I, 2 * Complex.I]

/-! ## 3. Downstream shapes (not targets of T2253; information) -/

-- the owed pins this file serves (all stay owed; `Test/Axioms.lean:204, 210, 212, 230` on e362f4b)
#check @RBM.Univ.UNEMCTE2             -- Pins.lean:669 (integrands `(∏ …).im * L1t d … (sz.lam n) (ouMat …) (z u)` `:675-676`, `L2t` `:680-681`; UN-18)
#check @RBM.Univ.UNEMCTE2Row          -- Pins.lean:797 (UN-18)
#check @RBM.Univ.UNEMCTE2k            -- PinsK.lean:345 (model-generic, `lam = K.lamV sz n`)
#check @RBM.Univ.UNUnivMainRow        -- Pins.lean:745 (UN-24)
#check @RBM.Univ.ouMat                -- Pins.lean:150
#check @RBM.Univ.ouMat_isHermitian    -- Pins.lean:154 (the `hH` of targets 4d, 5 at `H = ouMat …`)
#check @RBM.Univ.InWindow             -- Pins.lean:501 (`Nsz ^ (-1 - τU) ≤ z.im`: the `0 < (z i).im` of targets 4d, 5)

-- consumer shape (UN-18, token check of preflight (i)): target 5 at the band data, `s = univ : Finset (Fin nf)`;
-- its summands are the integrands of `UNEMCTE2` (`Pins.lean:675-676, 680-681`) token for token
example : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n nf : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (z : Fin nf → ℂ),
    H.IsHermitian → (∀ i ∈ (Finset.univ : Finset (Fin nf)), 0 < (z i).im) →
    T2253_kernel_bound_Lt_at d (sz.L n) (sz.W n) (sz.lam n) (Finset.univ : Finset (Fin nf)) H z

end RBM.Univ.T2253Check
