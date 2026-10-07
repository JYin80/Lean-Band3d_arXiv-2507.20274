/-
Release check for T2278 (dispatcher V1, Tue Oct  6 09:00 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §29,
§45 O2, §54, §57 (2), §66, §91 (1)).
UN-30 (bulk universality, GUE phase): the deterministic entry layer at the mixture profile `S_u = a S(g) + b N⁻¹`,
port of RBM2D `Universality/GUEPhase/EntryDet.lean` at `c9a24cf` (lines 1-891; the instance section `:893-1337` is
rewritten at `d = 3`) to `d ≥ 3`: `stable_mix` (stability of `1 - u m² S'`, constant `Kstab3 d Λ κ (1 + 1/gapK κ)`,
L-free; RBM2D `Kstab2 κ L ∝ 1 + log L`), the normalised profile `Snorm`, `mix_offdiag_det` / `mix_diag_det`
((4.2) / (4.3) of Lemma 4.1 at `S'`), Ward (`ward_col`, `ward_row`), `inv_N_le_maxLoopPM` (`N = (W L)^d`),
`sum_Snorm_le`, the constants `mixC`, `mixK`, `mixDelta`, `mixCdet` (arguments `d Λ κ` instead of `κ L`) and the
main deterministic bound `mix_det`.  Class T of T2173 (`docs/reports/T2173-portmap.md:242`, `:321`): band instance
here (`0 < g ≤ Λ`, `m = mE E`); the BA form (`lamV = 0`, matrix `M^{(+,+)}`) is BA-C3 (`T2173-portmap.md:275`).
Section 1: the merged names the new file builds on.
Section 2: vocabulary (`SnormV`, `mixCV`, `mixKV`, `mixDeltaV`, `mixCdetV`, `rfl`-equal to the library `Snorm`,
`mixC`, `mixK`, `mixDelta`, `mixCdet`) and the pinned statements as `def … : Prop` in the temporary namespace
`RBM.Univ.T2278Check`.  The library states each pin as a theorem in `RBM.Univ` whose type is exactly this body after
unfolding the vocabulary (only `Type` → `Type*` in `ν` may differ: instance as `@name.{0}`).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2278-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- `RBM3D/Universality/GUEPhase/AuxCarrier.lean` (9eb0502, UN-25 = T2196): the mixture profile
#check @RBM.Univ.Smix
#check @RBM.Univ.Smix_symm
#check @RBM.Univ.Smix_nonneg
#check @RBM.Univ.sum_Smix_row
#check @RBM.Univ.sum_Smix_col
-- `RBM3D/Gauss/FineModel.lean` (0a873f1), `RBM3D/Gauss/Model.lean` (a722f63), `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.svarF
#check @RBM.Gauss.svarF_nonneg
#check @RBM.Gauss.svarF_comm
#check @RBM.Gauss.svarF_eq_svar
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.svar
#check @RBM.Gauss.Idx
#check @RBM.Gauss.split
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.card_Idx
-- `RBM3D/Defs/Semicircle.lean` (fbc9870; RBM2D `spectralM ↦ mE`, `spectralZ ↦ zt`)
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.zt
#check @RBM.zt_im
-- `RBM3D/Green/EntryCore.lean` (890a89f): the profile-generic core of Lemma 4.1
#check @RBM.green
#check @RBM.Green.GoodEvent
#check @RBM.Green.GoodEvent.norm_diag_sub_le
#check @RBM.Green.GoodEvent.norm_diag_le
#check @RBM.Green.ldeRowLHS
#check @RBM.Green.ldeColLHS
#check @RBM.Green.ldeRowRHS
#check @RBM.Green.ldeColRHS
#check @RBM.Green.ldeQuadLHS
#check @RBM.Green.ldeQuadRHS
#check @RBM.Green.LDERow
#check @RBM.Green.LDECol
#check @RBM.Green.LDEQuad
#check @RBM.Green.norm_sq_green_offdiag_le
#check @RBM.Green.Stable
#check @RBM.Green.norm_sq_green_diag_sub_le
-- `RBM3D/Green/LDE.lean` (7c7652e)
#check @RBM.Green.im_green_diag
-- `RBM3D/Green/Stability.lean` (ea63565): the `d ≥ 3` stability constant (RBM2D `Kstab2 κ L`)
#check @RBM.Green.Kstab3
#check @RBM.Green.one_le_Kstab3
#check @RBM.Green.stable_svar_bulk
-- `RBM3D/Loop/KLSumZero.lean` (cb7d4ba; RBM2D `RBM.KLoop.gapK`)
#check @RBM.Loop.gapK
#check @RBM.Loop.gapK_le_norm
-- `RBM3D/Green/Pins.lean` (64bdfd3)
#check @RBM.Green.loopPM
#check @RBM.Green.greenBlk
#check @RBM.Green.maxLoopPM
#check @RBM.Green.maxLoopPM_nonneg
#check @RBM.Green.norm_loopPM_eq
-- `RBM3D/Green/EntryDom.lean` (a68a954): the RBM3D port of RBM2D `Green/EntryBlock` (`Sblk2 ↦ svar` on `Vtx`)
#check @RBM.Green.green_mul_sub_of_im
#check @RBM.Green.sub_mul_green_of_im
#check @RBM.Green.zt_im_ne_zero
#check @RBM.Green.mE_mul_add_zt
#check @RBM.Green.sum_svar_row
#check @RBM.Green.sum_svar_col
#check @RBM.Green.svar_le_inv_Wd
#check @RBM.Green.sum_sum_svar_le_maxLoopPM
#check @RBM.Green.inv_Wd_le_maxLoopPM
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `RBM3D/Green/IBP.lean` (382b6d9)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.blockMat
#check @RBM.Green.IBP_sum_svarF_row
-- consumer side only (not imported): the model class and its coupling
#check @RBM.Univ.UNKind
#check @RBM.Univ.UNKind.band
#check @RBM.Gauss.Sizes.WO
-- Mathlib names of the route (same Mathlib revision as RBM2D `c9a24cf`)
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Matrix.transpose_nonsing_inv
#check @Equiv.sum_comp
#check @Finset.sum_mul_sq_le_sq_mul_sq

/-! ## 2. Vocabulary and pinned statements -/

noncomputable section

namespace RBM.Univ.T2278Check

open RBM.Gauss RBM.Green

/-- The normalised mixture profile `S' = S_u / (a + b)` (library `Snorm`, `rfl`). -/
def SnormV (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (x y : Idx d L W) : ℝ :=
  RBM.Univ.Smix d L W g a b x y / (a + b)

/-- `c_κ = √(2κ)/2` (library `mixC`, `rfl`). -/
def mixCV (κ : ℝ) : ℝ := Real.sqrt (2 * κ) / 2

/-- The stability constant of `stable_mix` (library `mixK`, `rfl`): `Kstab3 d Λ κ (1 + 1/gapK κ)`. -/
def mixKV (d : ℕ) (Λ κ : ℝ) : ℝ := Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)

/-- The smallness threshold for `δ` (library `mixDelta`, `rfl`). -/
def mixDeltaV (d : ℕ) (Λ κ : ℝ) : ℝ := min (1 / 2) (min (1 / (2 * mixKV d Λ κ)) (mixCV κ / 2))

/-- The constant of `mix_det` (library `mixCdet`, `rfl`). -/
def mixCdetV (d : ℕ) (Λ κ : ℝ) : ℝ := (2160 * mixKV d Λ κ ^ 2 + 162) * (1 + 3 / mixCV κ)

/-- Target 1, `stable_mix` (RBM2D `:102`; `+ hd`, `hg`, `hgΛ`; `Kstab2 κ L ↦ Kstab3 d Λ κ`). -/
def T2278_stable_mix : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ d → 3 ≤ L → ∀ {g Λ κ E a b : ℝ}, 0 < g → g ≤ Λ →
    0 < κ → |E| ≤ 2 - κ → 0 ≤ a → 0 ≤ b → 0 < a + b → a + b < 1 →
      RBM.Green.Stable (fun x y : Idx d L W => RBM.Univ.Smix d L W g a b x y / (a + b))
        (((a + b : ℝ) : ℂ) * RBM.mE E ^ 2) (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ))

/-- Target 2, `svarF_le` (new name; RBM2D `svar_le` `:234`, `S ≤ W⁻²/5`). -/
def T2278_svarF_le : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ), 3 ≤ L → ∀ x y : Idx d L W,
    svarF d L W g x y ≤ ((W : ℝ) ^ d)⁻¹

/-- Target 2, `Snorm_le` (RBM2D `:239`, `W⁻² ↦ W^{-d}`). -/
def T2278_Snorm_le : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ {g a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b →
    ∀ x y : Idx d L W, SnormV d L W g a b x y ≤ ((W : ℝ) ^ d)⁻¹

/-- Target 2, `Snorm_zero_left` (RBM2D `:268`, `(W L)^2 ↦ (W L)^d`). -/
def T2278_Snorm_zero_left : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {b : ℝ}, 0 < b → ∀ x y : Idx d L W,
    SnormV d L W g 0 b x y = 1 / (((W * L) ^ d : ℕ) : ℝ)

/-- Target 3, `mix_offdiag_det` (RBM2D `:278`; profile-generic, any `g`). -/
def T2278_mix_offdiag_det : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ {g a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b →
    ∀ {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {z m : ℂ} {δ Φ Λ : ℝ},
      G * (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) = 1 →
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1 → ‖m‖ = 1 →
      GoodEvent G m δ → δ ≤ 1 / 2 → 1 ≤ Φ → 36 * Φ * δ ^ 2 ≤ 1 →
      LDERow H G (SnormV d L W g a b) Φ → LDECol H G (SnormV d L W g a b) Φ →
      (∀ i j, ∑ k, ∑ l, SnormV d L W g a b i k * ‖G k l‖ ^ 2 * SnormV d L W g a b l j ≤ Λ) →
      (∀ i j, SnormV d L W g a b i j ≤ Λ) → ∀ {i j : Idx d L W}, i ≠ j →
        ‖G i j‖ ^ 2 ≤ 162 * Φ ^ 2 * Λ

/-- Target 3, `mix_diag_det` (RBM2D `:296`; `+ hd`, `hg`, `hgΛ`; the loop bound is `Λ'`, the coupling bound `Λ`). -/
def T2278_mix_diag_det : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ d → 3 ≤ L → ∀ {g Λ κ E a b : ℝ}, 0 < g → g ≤ Λ →
    0 < κ → |E| ≤ 2 - κ → 0 ≤ a → 0 ≤ b → 0 < a + b → a + b < 1 →
    ∀ {H G : Matrix (Idx d L W) (Idx d L W) ℂ} {δ Φ Λ' : ℝ},
      G * (H - RBM.zt E (a + b) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) = 1 →
      (H - RBM.zt E (a + b) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) * G = 1 →
      GoodEvent G (RBM.mE E) δ → δ ≤ 1 / 2 → 1 ≤ Φ → 36 * Φ * δ ^ 2 ≤ 1 →
      LDERow H G (SnormV d L W g a b) Φ → LDECol H G (SnormV d L W g a b) Φ →
      LDEQuad H G (SnormV d L W g a b) (a + b) Φ →
      (∀ i, ‖H i i‖ ^ 2 ≤ Φ * SnormV d L W g a b i i) →
      (∀ i j, ∑ k, ∑ l, SnormV d L W g a b i k * ‖G k l‖ ^ 2 * SnormV d L W g a b l j ≤ Λ') →
      (∀ i j, SnormV d L W g a b i j ≤ Λ') →
      (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) * δ ≤ 1 / 2 → ∀ i : Idx d L W,
        ‖G i i - RBM.mE E‖ ^ 2 ≤
          2160 * (Kstab3 d Λ κ * (1 + 1 / RBM.Loop.gapK κ)) ^ 2 * Φ ^ 2 * Λ'

/-- Target 4, `ward_col` (RBM2D `:335`, verbatim; any index type). -/
def T2278_ward_col : Prop :=
  ∀ {ν : Type} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}, H.IsHermitian → ∀ {z : ℂ}, z.im ≠ 0 →
    ∀ i : ν, ∑ x, ‖RBM.green H z x i‖ ^ 2 = (RBM.green H z i i).im / z.im

/-- Target 4, `ward_row` (RBM2D `:441`, verbatim; any index type). -/
def T2278_ward_row : Prop :=
  ∀ {ν : Type} [Fintype ν] [DecidableEq ν] {H : Matrix ν ν ℂ}, H.IsHermitian → ∀ {z : ℂ}, z.im ≠ 0 →
    ∀ k : ν, ∑ l, ‖RBM.green H z k l‖ ^ 2 = (RBM.green H z k k).im / z.im

/-- Target 4, `im_diag_le` (RBM2D `:462`, verbatim). -/
def T2278_im_diag_le : Prop :=
  ∀ {ν : Type} [Fintype ν] [DecidableEq ν] {G : Matrix ν ν ℂ} {m : ℂ}, ‖m‖ = 1 → ∀ {δ : ℝ}, GoodEvent G m δ →
    δ ≤ 1 / 2 → ∀ x : ν, (G x x).im ≤ 3 / 2

/-- Target 5, `inv_N_le_maxLoopPM` (RBM2D `:354`; `N = (W L)^2 ↦ (W L)^d`; consumer UN-31 `Proc`). -/
def T2278_inv_N_le_maxLoopPM : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {E u : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ},
    M.IsHermitian → 0 < (RBM.zt E u).im → ∀ {m : ℂ} {δ : ℝ},
      GoodEvent (greenBlk d L W E u M true) m δ → δ ≤ m.im / 2 →
        m.im / (2 * ((((W * L) ^ d : ℕ) : ℝ) * (RBM.zt E u).im)) ≤ maxLoopPM d L W E u M

/-- Target 6, `sum_Snorm_le` (RBM2D `:491`; `BlockIndex L W ↦ Vtx d L W`, any `g`). -/
def T2278_sum_Snorm_le : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ {g E s : ℝ} {M : Matrix (Idx d L W) (Idx d L W) ℂ},
    M.IsHermitian → 0 < (RBM.zt E s).im → ∀ {m : ℂ}, ‖m‖ = 1 → 0 < m.im → ∀ {δ : ℝ},
      GoodEvent (greenBlk d L W E s M true) m δ → δ ≤ 1 / 2 → δ ≤ m.im / 2 →
      ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ p q : Vtx d L W,
        ∑ k, ∑ l, SnormV d L W g a b ((splitEquiv d L W).symm p) ((splitEquiv d L W).symm k) *
            ‖greenBlk d L W E s M true k l‖ ^ 2 *
            SnormV d L W g a b ((splitEquiv d L W).symm l) ((splitEquiv d L W).symm q)
          ≤ (1 + 3 / m.im) * maxLoopPM d L W E s M

/-- Target 7, constants (RBM2D `:623-651`; `mixK_one_le` needs no `L`). -/
def T2278_mixC_pos : Prop := ∀ {κ : ℝ}, 0 < κ → 0 < mixCV κ

def T2278_mixK_one_le : Prop :=
  ∀ {κ : ℝ}, 0 < κ → κ ≤ 2 → ∀ (d : ℕ) (Λ : ℝ), 1 ≤ mixKV d Λ κ

def T2278_mixDelta_pos : Prop :=
  ∀ {κ : ℝ}, 0 < κ → κ ≤ 2 → ∀ (d : ℕ) (Λ : ℝ), 0 < mixDeltaV d Λ κ

def T2278_mixCdet_nonneg : Prop :=
  ∀ {κ : ℝ}, 0 < κ → ∀ (d : ℕ) (Λ : ℝ), 0 ≤ mixCdetV d Λ κ

/-- Target 8, **`mix_det`** (RBM2D `:715`; the main deterministic bound; consumer UN-41/42 `EntryTail`). -/
def T2278_mix_det : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ d → 3 ≤ L →
    ∀ {M : Matrix (Idx d L W) (Idx d L W) ℂ}, M.IsHermitian →
    ∀ {g Λ κ E a b : ℝ}, 0 < g → g ≤ Λ → 0 < κ → |E| ≤ 2 - κ → 0 ≤ a → 0 ≤ b → 0 < a + b →
      a + b < 1 → ∀ {δ Φ : ℝ},
      GoodEvent (greenBlk d L W E (a + b) M true) (RBM.mE E) δ → δ ≤ mixDeltaV d Λ κ → 1 ≤ Φ →
      36 * Φ * δ ^ 2 ≤ 1 →
      LDERow (blockMat d L W M) (greenBlk d L W E (a + b) M true)
        (fun x y => RBM.Univ.Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ →
      LDECol (blockMat d L W M) (greenBlk d L W E (a + b) M true)
        (fun x y => RBM.Univ.Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) Φ →
      LDEQuad (blockMat d L W M) (greenBlk d L W E (a + b) M true)
        (fun x y => RBM.Univ.Smix d L W g a b ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y)) 1 Φ →
      (∀ i, ‖blockMat d L W M i i‖ ^ 2 ≤
        Φ * RBM.Univ.Smix d L W g a b ((splitEquiv d L W).symm i) ((splitEquiv d L W).symm i)) →
      ∀ p q : Vtx d L W,
        ‖(greenBlk d L W E (a + b) M true - RBM.mE E • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) p q‖ ^ 2
          ≤ mixCdetV d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M

/-- The consumer's coupling window (UN-41/42 `EntryTail`, band kind): `WO` gives `0 < sz.lam n ≤ 𝔡⁻¹`
eventually, i.e. `g := sz.lam n`, `Λ := 𝔡⁻¹` in targets 1, 3, 8 (statement only). -/
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (𝔡 : ℝ) : Prop :=
  sz.WO 𝔡 → ∀ n : ℕ, 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → T2278_mix_det

/-- The `d = 3` instance shape (statement only): `L = 3`, `W = 2`, `N = 216`, `g = Λ = κ = 1`, `E = 0`. -/
example : Prop :=
  RBM.Green.Stable (fun x y : Idx 3 3 2 => RBM.Univ.Smix 3 3 2 1 (1 / 2) (1 / 4) x y / (1 / 2 + 1 / 4))
    (((1 / 2 + 1 / 4 : ℝ) : ℂ) * RBM.mE 0 ^ 2) (mixKV 3 1 1)

end RBM.Univ.T2278Check

end
