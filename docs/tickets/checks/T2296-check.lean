/-
T2296 (BA-G1, `BA/GreenSchur`) check file.  Dispatcher draft, Tue Oct  6 2026.
Only imports of merged modules, `open`/`namespace`, pin texts (`def … : Prop`), one vocabulary def, `#check`s of
merged names.  No proofs.  Compiles on `main` (1ba63a2) as is.
-/
import RBM3D.BA.CombesThomas
import RBM3D.BA.ImmLower
import RBM3D.BA.FlowPins
import RBM3D.Green.EntryCore
import RBM3D.Defs.RadialSum
import RBM3D.Analysis.Resolvent

open Filter Matrix

/-! ## 1. Merged names used (full namespaces from the enclosing `namespace … end` blocks) -/

-- `RBM3D/BA/MFixedPoint.lean` (ae63e74), namespace `RBM.BA`
#check @RBM.BA.BAMB                 -- :190 (section Det, `variable (d L : ℕ) [NeZero L]`)
#check @RBM.BA.BASelf               -- :193
#check @RBM.BA.BAm                  -- :379
#check @RBM.BA.BAReal               -- :432
#check @RBM.BA.BAdom                -- :435
#check @RBM.BA.BAdom_real           -- :479 (`variable {d L}`)
#check @RBM.BA.BAzztE_data          -- :297
#check @RBM.BA.BAm_self             -- :809
#check @RBM.BA.BAm_real_eq_of_self  -- :824
#check @RBM.BA.BAPropM              -- :567
-- `RBM3D/BA/Ward.lean` (b4fb28b), namespace `RBM.BA`, section `Ward` `variable (d L : ℕ) [NeZero L]`
#check @RBM.BA.BAMB_ward_row        -- :108
#check @RBM.BA.BAm_norm_le_one      -- :136
-- `RBM3D/BA/CombesThomas.lean` (1ba63a2, BA-D4 = T2290), namespace `RBM.BA`
#check @RBM.BA.BAct_C               -- :42
#check @RBM.BA.BAct_rate            -- :45
#check @RBM.BA.BAct_rate_pos        -- :52
#check @RBM.BA.BAMB_resolvent_row   -- :81
#check @RBM.BA.BAMB_ct_core         -- :288
#check @RBM.BA.BAMB_decay_large     -- :509
#check @RBM.BA.baPropM_holds        -- :562
-- `RBM3D/BA/ImmLower.lean` (30f7ef8, BA-D7 = T2291), namespace `RBM.BA`
#check @RBM.BA.BASelf_sub_le        -- :252
#check @RBM.BA.BAm_im_lower         -- :391
#check @RBM.BA.baImmLower_holds     -- :414
#check @RBM.BA.BAm_im_lower_of_bulk -- :424
-- `RBM3D/BA/FlowPins.lean` (b750bf3), namespace `RBM.BA`
#check @RBM.BA.BAMres_fine_apply    -- :100
#check @RBM.BA.BAmF                 -- :250
#check @RBM.BA.BAMfine              -- :253
#check @RBM.BA.BAGt                 -- :257
#check @RBM.BA.BAGM                 -- :303
#check @RBM.BA.BAflowT0             -- :537
#check @RBM.BA.BAflowEs             -- :540
#check @RBM.BA.BAflowLam0           -- :543
#check @RBM.BA.BAFlow               -- :546
#check @RBM.BA.baFMz                -- :550
-- `RBM3D/Gauss/BlockAnderson.lean` (868b3b4), `RBM3D/Gauss/FineModel.lean` (0a873f1), `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.PsiB              -- BlockAnderson :45
#check @RBM.Gauss.PsiI              -- BlockAnderson :52
#check @RBM.Gauss.PsiI_isHermitian  -- BlockAnderson :65
#check @RBM.Gauss.Sizes.seqHflowBA  -- BlockAnderson :83
#check @RBM.Gauss.Sizes.seqHflow    -- FineModel :225
#check @RBM.Gauss.Sizes.seqXmat     -- FineModel :218
#check @RBM.Gauss.Gres              -- GLoopFlow :74
#check @RBM.Gauss.Mres              -- GLoopFlow :81
#check @RBM.Gauss.ztOf              -- GLoopFlow :55
#check @RBM.Gauss.split             -- Defs/Sizes :64
#check @RBM.Gauss.Sizes.WO          -- Defs/Sizes :164
#check @RBM.zdistD                  -- Defs/Lattice :71
-- `RBM3D/Green/EntryCore.lean` (890a89f)
#check @RBM.green                   -- :34 (namespace `RBM`)
#check @RBM.Green.minorGreen        -- :59
#check @RBM.Green.green_off_diag_paper -- :242
#check @RBM.Green.green_diag_paper  -- :255
-- `RBM3D/Defs/RadialSum.lean` (320f7b0), `RBM3D/Analysis/Resolvent.lean` (6f9e0ba), namespace `RBM`
#check @RBM.expC                    -- :271
#check @RBM.sum_radial_exp_decay_le -- :275
#check @RBM.isUnit_sub_smul_of_isHermitian -- :132
-- instances
#check @RBM.BA.CouplingWindowInst.flowP_real -- CouplingWindow :878
#check @RBM.BA.CouplingWindowInst.g0P_pos    -- CouplingWindow :874

/-! ## 2. Target statements (`*_pin`; the theorem `Y` must satisfy `example : Y_pin := @Y`) -/

namespace RBM.BA.T2296Check

open RBM RBM.Gauss RBM.BA

/-- Target 1 `BAflow_real`: the chain domain gives real-axis bulk data at the flow parameters, every `n`. -/
def BAflow_real_pin (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ,
    BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)

/-- Target 2 `BAflow_lam0_window`: `(eq:WO)` at the flow coupling, eventually `0 < g₀ ≤ 𝔡⁻¹`. -/
def BAflow_lam0_window_pin (d : ℕ) : Prop :=
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ᶠ n in atTop, 0 < BAflowLam0 sz z n ∧ BAflowLam0 sz z n ≤ 𝔡⁻¹

/-- Target 3 `BAMfine_eq`: `M = M^{(B)} ⊗ I_{W^d}` entrywise at the flow data. -/
def BAMfine_eq_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
    ∀ x y : Idx d (sz.L n) (sz.W n),
      BAMfine sz lam0 E n x y =
        if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then
          BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)
            (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1
        else 0

/-- Target 4 `BAMfine_norm_le_one`: `‖M‖_max ≤ 1` (real-axis Ward row identity). -/
def BAMfine_norm_le_one_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ),
    BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
      ∀ x y : Idx d (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ ≤ 1

/-- Target 5 `BAMfine_decay`: `(Mbound_AO2)` on the fine lattice, every `0 < g₀ ≤ Λ`, rate `BAct_rate d Λ κ`. -/
def BAMfine_decay_pin (d : ℕ) : Prop :=
  0 < d → ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ →
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 3 ≤ sz.L n → 0 < lam0 n → lam0 n ≤ Λ →
      BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
        ∀ x y : Idx d (sz.L n) (sz.W n),
          ‖BAMfine sz lam0 E n x y‖ ≤ (BAct_rate d Λ κ)⁻¹ *
            Real.exp (-BAct_rate d Λ κ *
              (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1) : ℝ))

/-- Target 6 `BAMB_row_l1`: the `ℓ¹` row bound of `M^{(B)}`, uniform in `L` (`d = k + 2`). -/
def BAMB_row_l1_pin : Prop :=
  ∀ (k L : ℕ) [NeZero L], 3 ≤ L → ∀ (Λ g κ E : ℝ) (m : ℂ), 0 < Λ → 0 < g → g ≤ Λ → 0 < κ →
    BAReal (k + 2) L g κ E m → ∀ a : Zd (k + 2) L,
      ∑ b : Zd (k + 2) L, ‖BAMB (k + 2) L g (E : ℂ) m a b‖ ≤
        (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ)

/-- Target 7 `BAMfine_row_l1`: the same on the fine lattice, `∑_y ‖M_xy‖`. -/
def BAMfine_row_l1_pin : Prop :=
  ∀ (k : ℕ) (sz : Sizes (k + 2)) (lam0 E : ℕ → ℝ) (n : ℕ) (Λ κ : ℝ), 3 ≤ sz.L n → 0 < Λ → 0 < lam0 n →
    lam0 n ≤ Λ → 0 < κ → BAReal (k + 2) (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) →
      ∀ x : Idx (k + 2) (sz.L n) (sz.W n),
        ∑ y : Idx (k + 2) (sz.L n) (sz.W n), ‖BAMfine sz lam0 E n x y‖ ≤
          (BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ)

/-- New vocabulary (public def in the target file, `noncomputable`): `√t V + t m`, so that
`G_t⁻¹ - M⁻¹ = BAflowPert` (`H_t = g₀ Ψ + √t V`, `z_t = E + (1 - t) m`, `M = (g₀ Ψ - E - m)⁻¹`). -/
noncomputable def BAflowPert {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  (Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam 0) n t ω i j) +
    ((t : ℂ) * BAmF sz lam0 E n) • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- Target 8 `BAGt_sub_BAMfine`: the resolvent identity with the deterministic hopping, both orders. -/
def BAGt_sub_BAMfine_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ), t < 1 → 0 < (BAmF sz lam0 E n).im →
    BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAMfine sz lam0 E n * BAflowPert sz lam0 E n t ω * BAGt sz lam0 E n t ω) ∧
      BAGt sz lam0 E n t ω - BAMfine sz lam0 E n =
        -(BAGt sz lam0 E n t ω * BAflowPert sz lam0 E n t ω * BAMfine sz lam0 E n)

/-- Target 9 `BAPsiI_inBlock`: `Ψ` has no in-block entries (`Ψ^{(B)}_{aa} = 0`). -/
def BAPsiI_inBlock_pin : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], ∀ x y : Idx d L W,
    (split d L W x).1 = (split d L W y).1 → PsiI d L W x y = 0

/-- Target 10 `green_diag_split`: Schur `(4.8)` with `H = D + X`, `X` in-block, `D` off-block (the BA structure:
`D = g₀ Ψ`, `X = √t V`); the quadratic form splits into the random-random, the two mixed and the deterministic part. -/
def green_diag_split_pin : Prop :=
  ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β) (D X : Matrix ι ι ℂ) (z : ℂ),
    (∀ i k, b i = b k → D i k = 0) → (∀ i k, b i ≠ b k → X i k = 0) →
    IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det → ∀ i : ι, RBM.green (D + X) z i i ≠ 0 →
      RBM.green (D + X) z i i =
        (X i i - z -
          ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
              ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
                X i k.1 * Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
           (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
              ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
                X i k.1 * Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i) +
           (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
              ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 = b i),
                D i k.1 * Green.minorGreen (RBM.green (D + X) z) i k l * X l.1 i) +
           (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
              ∑ l ∈ Finset.univ.filter (fun l : {a : ι // a ≠ i} => b l.1 ≠ b i),
                D i k.1 * Green.minorGreen (RBM.green (D + X) z) i k l * D l.1 i)))⁻¹

/-- Target 11 `green_off_split`: Schur `(4.7)` with the same split (one random, one deterministic row sum). -/
def green_off_split_pin : Prop :=
  ∀ {ι β : Type} [Fintype ι] [DecidableEq ι] [DecidableEq β] (b : ι → β) (D X : Matrix ι ι ℂ) (z : ℂ),
    (∀ i k, b i = b k → D i k = 0) → (∀ i k, b i ≠ b k → X i k = 0) →
    IsUnit (D + X - z • (1 : Matrix ι ι ℂ)).det → ∀ i : ι, RBM.green (D + X) z i i ≠ 0 →
      ∀ j : {a : ι // a ≠ i},
        RBM.green (D + X) z i j.1 = -RBM.green (D + X) z i i *
          ((∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 = b i),
              X i k.1 * Green.minorGreen (RBM.green (D + X) z) i k j) +
           (∑ k ∈ Finset.univ.filter (fun k : {a : ι // a ≠ i} => b k.1 ≠ b i),
              D i k.1 * Green.minorGreen (RBM.green (D + X) z) i k j))

end RBM.BA.T2296Check
