/-
Release check for T2293 (UN-41) and T2293b (UN-42) (dispatcher V1, Tue Oct  6 11:50 UTC 2026; CLAUDE.md §4 step 0;
DECISIONS §16, §20, §29, §36, §45 O2, §54, §57 (1)(2), §91 (1), §92 (2), §95 (4)).
UN-41/42 (bulk universality, GUE phase): the probabilistic half of Lemma 4.1 at the mixture profile
`S_u = a S(g) + b N⁻¹`, port of RBM2D `Universality/GUEPhase/EntryTail.lean` at `c9a24cf` (lines 1-1525; the
instance section `:1527-1653` is rewritten at `d = 3`) to `d ≥ 3`, split at the section boundary `:874/876`:
* T2293 (UN-41, `RBM3D/Universality/GUEPhase/EntryTail.lean`, source `:1-874`): the mixture matrix `mixMat` on the
  band OU carrier `ouP (UNModel.band sz) n` (`SeqΩ sz × Ω d (L n) (W n)`), `ouMat_eq_mixMat`, the pin `GUEEntryMix d`
  (statement), the mixture sample and its Gaussian law, the profile identities, `MixProfOK`, the four LDE tails,
  `mixEntry_greenBlk_eq` and the deterministic bridge `mixEntry_det` (`mix_det` on `Idx`).
* T2293b (UN-42, `RBM3D/Universality/GUEPhase/EntryTailMain.lean`, source `:876-1525`): `mixCq`, `mixBad`,
  `mixBad_tail`, `mixEntry_event_subset`, `mixEntry_union`, the scale arithmetic and `gueEntryMix : GUEEntryMix d`
  for `3 ≤ d`.
Class T of T2173 (`docs/reports/T2173-portmap.md:244`): band here (`g = sz.lam n`, `0 < g ≤ 𝔡⁻¹` from `Sizes.WO`); the
BA form (`lamV = 0`, matrix `M^{(+,+)}`) is BA-C3 `BA/GUEEntry` (`:275`).
Section 1: the merged names the new files build on.
Section 2: vocabulary (`mixMatV`, `mixSampleV`, `MixProfOKV`, `mixCqV`, `mixBadV`, `GUEEntryMixV`) and the pinned
statements as `def … : Prop` in the temporary namespace `RBM.Univ.T2293Check`.  The library states each pin as a
theorem in `RBM.Univ` whose type is exactly this body after unfolding the vocabulary.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2293-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- `RBM3D/Universality/GUEPhase/AuxCarrier.lean` (9eb0502, UN-25 = T2196)
#check @RBM.Univ.gaussLaw
#check @RBM.Univ.gueP_eq_gaussLaw
#check @RBM.Univ.PF_eq_gaussLaw
#check @RBM.Univ.mixVar
#check @RBM.Univ.Smix
#check @RBM.Univ.Smix_symm
#check @RBM.Univ.mixVar_exp_eq_ouVar
#check @RBM.Univ.TagFree
#check @RBM.Univ.mixVar_tagFree
#check @RBM.Univ.sigRow
#check @RBM.Univ.rowCoordF
#check @RBM.Univ.Xentry_eq_rowCoordF
#check @RBM.Univ.sigRow_gueVar
#check @RBM.Univ.svarF_pos_of_block_eq
#check @RBM.Univ.quadVqS
#check @RBM.Univ.quadQS
#check @RBM.Univ.gaussLaw_quad_tail
#check @RBM.Univ.auxMinorRes
#check @RBM.Univ.norm_auxMinorRes_le
#check @RBM.Univ.continuous_auxMinorRes
#check @RBM.Univ.auxOffRow
#check @RBM.Univ.auxMinorRes_congr
#check @RBM.Univ.auxLinChaos
#check @RBM.Univ.auxLin_chaos
#check @RBM.Univ.auxLin_Vq
#check @RBM.Univ.aux_lin_tail
#check @RBM.Univ.auxT_law
#check @RBM.Univ.continuous_Xmat_apply
#check @RBM.Univ.continuous_green_minorS
-- `RBM3D/Universality/GUEPhase/EntryDet.lean` (7a8a4eb, UN-30 = T2278)
#check @RBM.Univ.mix_det
#check @RBM.Univ.mixC
#check @RBM.Univ.mixK
#check @RBM.Univ.mixDelta
#check @RBM.Univ.mixCdet
#check @RBM.Univ.mixC_pos
#check @RBM.Univ.mixK_one_le
#check @RBM.Univ.mixDelta_pos
#check @RBM.Univ.mixCdet_nonneg
-- `RBM3D/Universality/Pins.lean` (f8ad4b4, UN-01 = T2174), `RBM3D/Universality/OU.lean` (a52eb85, T2177)
#check @RBM.Univ.gueVar
#check @RBM.Univ.gueP
#check @RBM.Univ.UNModel
#check @RBM.Univ.UNModel.band
#check @RBM.Univ.ouP
#check @RBM.Univ.ouMat
#check @RBM.Univ.ouMat_isHermitian
#check @RBM.Univ.ouSample
#check @RBM.Univ.ouVar
#check @RBM.Univ.ouMat_eq_Xmat_ouSample
#check @RBM.Univ.measurable_ouSample
#check @RBM.Univ.measurable_ouMat
#check @RBM.Univ.ouSample_law
#check @RBM.Univ.isProbabilityMeasure_ouP
-- `RBM3D/Gauss/FineModel.lean` (0a873f1), `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.svarF
#check @RBM.Gauss.svarF_diag
#check @RBM.Gauss.svarF_comm
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.PF
#check @RBM.Gauss.CoordF
#check @RBM.Gauss.Ω
#check @RBM.Gauss.Xmat
#check @RBM.Gauss.Xentry
#check @RBM.Gauss.Xmat_isHermitian
#check @RBM.Gauss.Xmat_add
#check @RBM.Gauss.Xmat_smul
#check @RBM.Gauss.measurable_Xentry
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.slice
#check @RBM.Gauss.Sizes.measurable_slice
#check @RBM.Gauss.Sizes.seqP_map_slice
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Idx
#check @RBM.Gauss.splitEquiv
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Green/Pins.lean` (64bdfd3), `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `RBM3D/Defs/Semicircle.lean` (fbc9870)
#check @RBM.Green.llErrMat
#check @RBM.Green.greenBlk
#check @RBM.Green.maxLoopPM
#check @RBM.Green.maxLoopPM_nonneg
#check @RBM.Gauss.Gres
#check @RBM.Gauss.blockMat
#check @RBM.mE
#check @RBM.zt
-- `RBM3D/Green/EntryCore.lean` (890a89f), `RBM3D/Green/EntryDom.lean` (a68a954), `RBM3D/Green/IBPPoly.lean` (3b8c687)
#check @RBM.green
#check @RBM.Green.inv_minor_resolvent
#check @RBM.Green.greenMinor
#check @RBM.Green.GoodEvent
#check @RBM.Green.ldeRowLHS
#check @RBM.Green.ldeRowRHS
#check @RBM.Green.ldeColLHS
#check @RBM.Green.ldeColRHS
#check @RBM.Green.ldeQuadLHS
#check @RBM.Green.ldeQuadRHS
#check @RBM.Green.entryDom_goodEvent_of_llErr
#check @RBM.Green.hwConst
#check @RBM.Green.hwConst_pos
-- `RBM3D/Defs/Domination.lean` (4c5302f)
#check @RBM.eventually_le_rpow
-- Mathlib (used by the source; imported through `RBM3D`)
#check @Matrix.inv_submatrix_equiv
#check @Matrix.nonsing_inv_eq_ringInverse
#check @MeasureTheory.Measure.map_prod_map
#check @Real.pow_div_factorial_le_exp

/-! ## 2. Vocabulary and pins -/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ.T2293Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM.Gauss RBM.Green
open scoped NNReal ENNReal

/-- `mixMat sz n a b ω = √a H_band(ω₁) + √b H_GUE(ω₂)` on the band OU carrier (RBM2D `:75`; d ≥ 3: the band
matrix is `seqXmat sz n ω.1`, coupling `sz.lam n`). -/
def mixMatV {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ)
    (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Real.sqrt a • RBM.Gauss.Sizes.seqXmat sz n ω.1 + Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2

/-- The coordinates `√a (slice ω₁) + √b ω₂` (RBM2D `:142`). -/
def mixSampleV {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ)
    (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)) : Ω d (sz.L n) (sz.W n) :=
  fun c => Real.sqrt a * RBM.Gauss.Sizes.slice sz n ω.1 c + Real.sqrt b * ω.2 c

/-- The profile hypothesis (RBM2D structure `MixProfOK`, `:349`, fields `symm`, `off`, `diag`) as a conjunction. -/
def MixProfOKV (d L W : ℕ) [NeZero L] [NeZero W] (v : CoordF d L W → ℝ≥0)
    (S : Idx d L W → Idx d L W → ℝ) : Prop :=
  (∀ x y, S x y = S y x) ∧ (∀ x y, x ≠ y → RBM.Univ.sigRow d L W v x y = S x y) ∧
    ∀ x, (v (x, x, true) : ℝ) = S x x

/-- RBM2D `mixCq` (`:884`), verbatim. -/
def mixCqV (q : ℕ) : ℝ := 4 ^ (q + 1) * hwConst q + 2 ^ (q + 2) * ((q + 1).factorial : ℝ)

/-- The union of the four LDE failure events (RBM2D `mixBad`, `:954`), profile `Smix d L W g a b`. -/
def mixBadV (d L W : ℕ) [NeZero L] [NeZero W] (g a b : ℝ) (z : ℂ) (Λ : ℝ) : Set (Ω d L W) :=
  (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W | p.1 ≠ p.2 ∧
      Λ * ldeRowRHS (RBM.Univ.Smix d L W g a b) (RBM.green (Xmat d L W s) z) p.1 p.2 <
        ldeRowLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) p.1 p.2}) ∪
  (⋃ p : Idx d L W × Idx d L W, {s : Ω d L W | p.1 ≠ p.2 ∧
      Λ * ldeColRHS (RBM.Univ.Smix d L W g a b) (RBM.green (Xmat d L W s) z) p.1 p.2 <
        ldeColLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) p.1 p.2}) ∪
  (⋃ i : Idx d L W, {s : Ω d L W | Λ * ldeQuadRHS (RBM.Univ.Smix d L W g a b) (RBM.green (Xmat d L W s) z) i <
      ldeQuadLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) (RBM.Univ.Smix d L W g a b) 1 i}) ∪
  (⋃ i : Idx d L W, {s : Ω d L W | Λ * RBM.Univ.Smix d L W g a b i i < ‖Xmat d L W s i i‖ ^ 2})

/-- **Pin text `GUEEntryMix d`** (RBM2D `:112`; d ≥ 3: `sz : Sizes d` with `sz.Admissible 𝔠 𝔡` (contains `0 < 𝔠`,
`0 < 𝔡`, `WO 𝔡`), carrier `ouP (UNModel.band sz) n`, `W⁻² ↦ W^{-d}`). -/
def GUEEntryMixV (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : RBM.Gauss.Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
  ∀ E : ℕ → ℝ, (∀ n, |E n| ≤ 2 - κ) → ∀ n0 : ℕ, ∀ K : ℕ → ℕ,
  (∀ n, K n ≤ (sz.size n) ^ n0) → ∀ a b : ∀ n, Fin (K n + 1) → ℝ,
  (∀ n k, 0 ≤ a n k ∧ 0 ≤ b n k ∧ 0 < a n k + b n k ∧ a n k + b n k < 1) →
  ∀ (c₀ : ℝ) (δ : ℕ → ℝ), 0 < c₀ → (∀ n, 0 ≤ δ n) →
  (∀ᶠ n in atTop, δ n ≤ ((sz.size n : ℕ) : ℝ) ^ (-c₀)) →
  ∀ τ D : ℝ, 0 < τ → 0 < D → ∀ᶠ n in atTop,
    RBM.Univ.ouP (RBM.Univ.UNModel.band sz) n
      {ω | ∃ (k : Fin (K n + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        ((sz.size n : ℕ) : ℝ) ^ τ *
            (maxLoopPM d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                (mixMatV sz n (a n k) (b n k) ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                (mixMatV sz n (a n k) (b n k) ω) x y ≤ δ n
            then llErrMat d (sz.L n) (sz.W n) (E n) (a n k + b n k)
                  (mixMatV sz n (a n k) (b n k) ω) i j ^ 2
            else 0)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-! ### T2293 (UN-41) pins -/

def T2293_mixMat_isHermitian : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ) (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    (mixMatV sz n a b ω).IsHermitian

def T2293_ouMat_eq_mixMat : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (t : ℝ) (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    RBM.Univ.ouMat (RBM.Univ.UNModel.band sz) n t ω = mixMatV sz n (Real.exp (-t)) (1 - Real.exp (-t)) ω

def T2293_mixMat_zero_right : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (a : ℝ) (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    mixMatV sz n a 0 ω = Real.sqrt a • RBM.Gauss.Sizes.seqXmat sz n ω.1

def T2293_mixMat_zero_left : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (b : ℝ) (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    mixMatV sz n 0 b ω = Real.sqrt b • Xmat d (sz.L n) (sz.W n) ω.2

def T2293_mixMat_eq_Xmat_mixSample : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ) (ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n)),
    mixMatV sz n a b ω = Xmat d (sz.L n) (sz.W n) (mixSampleV sz n a b ω)

def T2293_measurable_mixSample : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ), Measurable (mixSampleV sz n a b)

def T2293_measurable_mixMat : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (a b : ℝ), Measurable (mixMatV sz n a b)

/-- The one-time Gaussian law of the mixture, every `a, b ≥ 0` (RBM2D `:202`; coupling `sz.lam n`). -/
def T2293_mixSample_law : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) {a b : ℝ}, 0 ≤ a → 0 ≤ b →
    (RBM.Univ.ouP (RBM.Univ.UNModel.band sz) n).map (mixSampleV sz n a b) =
      RBM.Univ.gaussLaw d (sz.L n) (sz.W n) (RBM.Univ.mixVar d (sz.L n) (sz.W n) (sz.lam n) a b)

def T2293_ouP_mixSample_preimage : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) {a b : ℝ}, 0 ≤ a → 0 ≤ b →
    ∀ {A : Set (Ω d (sz.L n) (sz.W n))}, MeasurableSet A →
      RBM.Univ.ouP (RBM.Univ.UNModel.band sz) n (mixSampleV sz n a b ⁻¹' A) =
        RBM.Univ.gaussLaw d (sz.L n) (sz.W n) (RBM.Univ.mixVar d (sz.L n) (sz.W n) (sz.lam n) a b) A

def T2293_mixEntry_mixVar_coe : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b → ∀ c : CoordF d L W,
    (RBM.Univ.mixVar d L W g a b c : ℝ) = a * (gvarF d L W g c : ℝ) + b * (RBM.Univ.gueVar d L W c : ℝ)

/-- RBM2D `mixEntry_sigRow_gvar` (`:286`), renamed: `sigRow (gvarF g) i k = svarF g i k` for `k ≠ i`. -/
def T2293_mixEntry_sigRow_gvarF : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {i k : Idx d L W}, k ≠ i →
    RBM.Univ.sigRow d L W (gvarF d L W g) i k = svarF d L W g i k

def T2293_mixEntry_sigRow_mixVar : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b → ∀ {i k : Idx d L W}, k ≠ i →
    RBM.Univ.sigRow d L W (RBM.Univ.mixVar d L W g a b) i k = RBM.Univ.Smix d L W g a b i k

def T2293_mixEntry_mixVar_diag : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b → ∀ i : Idx d L W,
    (RBM.Univ.mixVar d L W g a b (i, i, true) : ℝ) = RBM.Univ.Smix d L W g a b i i

def T2293_mixEntry_Smix_diag_pos : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ i : Idx d L W,
    0 < RBM.Univ.Smix d L W g a b i i

def T2293_mixProfOK : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b →
    MixProfOKV d L W (RBM.Univ.mixVar d L W g a b) (RBM.Univ.Smix d L W g a b)

def T2293_mixEntry_quad_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ},
    RBM.Univ.TagFree d L W v → MixProfOKV d L W v S → ∀ {z : ℂ}, z.im ≠ 0 → ∀ (i : Idx d L W) {lam : ℝ},
    0 < lam → ∀ q : ℕ,
    RBM.Univ.gaussLaw d L W v {s | lam * ldeQuadRHS S (RBM.green (Xmat d L W s) z) i <
        ldeQuadLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) S 1 i}
      ≤ ENNReal.ofReal (hwConst q / lam ^ (q + 1))

def T2293_mixEntry_row_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ},
    RBM.Univ.TagFree d L W v → MixProfOKV d L W v S → ∀ {z : ℂ}, z.im ≠ 0 → ∀ {i j : Idx d L W}, i ≠ j →
    ∀ {Λ : ℝ}, 1 < Λ → ∀ q : ℕ,
    RBM.Univ.gaussLaw d L W v {s | Λ * ldeRowRHS S (RBM.green (Xmat d L W s) z) i j <
        ldeRowLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) i j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1))

def T2293_mixEntry_col_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ},
    RBM.Univ.TagFree d L W v → MixProfOKV d L W v S → ∀ {z : ℂ}, z.im ≠ 0 → ∀ {k j : Idx d L W}, k ≠ j →
    ∀ {Λ : ℝ}, 1 < Λ → ∀ q : ℕ,
    RBM.Univ.gaussLaw d L W v {s | Λ * ldeColRHS S (RBM.green (Xmat d L W s) z) k j <
        ldeColLHS (Xmat d L W s) (RBM.green (Xmat d L W s) z) k j}
      ≤ ENNReal.ofReal (hwConst q / ((Λ - 1) ^ 2) ^ (q + 1))

def T2293_mixEntry_diag_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] {v : CoordF d L W → ℝ≥0} {S : Idx d L W → Idx d L W → ℝ},
    MixProfOKV d L W v S → ∀ i : Idx d L W, 0 < S i i → ∀ {Λ : ℝ}, 0 < Λ →
    RBM.Univ.gaussLaw d L W v {s | Λ * S i i < ‖Xmat d L W s i i‖ ^ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-Λ / 2))

/-- Consumer UN-48 (`HypA`, RBM2D `:389`, `:399`). -/
def T2293_mixEntry_greenBlk_eq : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ) (M : Matrix (Idx d L W) (Idx d L W) ℂ),
    greenBlk d L W E u M true =
      (RBM.green M (RBM.zt E u)).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm

/-- The deterministic step on the fine lattice (RBM2D `:827`), `mix_det` with `3 ≤ d`, `0 < g ≤ Λ`. -/
def T2293_mixEntry_det : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ d → 3 ≤ L →
    ∀ {M : Matrix (Idx d L W) (Idx d L W) ℂ}, M.IsHermitian →
    ∀ {g Λ κ E a b : ℝ}, 0 < g → g ≤ Λ → 0 < κ → |E| ≤ 2 - κ → 0 ≤ a → 0 ≤ b → 0 < a + b →
      a + b < 1 → ∀ {δ Φ : ℝ}, (∀ x y, llErrMat d L W E (a + b) M x y ≤ δ) →
      δ ≤ RBM.Univ.mixDelta d Λ κ → 1 ≤ Φ → 36 * Φ * δ ^ 2 ≤ 1 →
      (∀ i j, i ≠ j → ldeRowLHS M (RBM.green M (RBM.zt E (a + b))) i j ≤
        Φ * ldeRowRHS (RBM.Univ.Smix d L W g a b) (RBM.green M (RBM.zt E (a + b))) i j) →
      (∀ k j, k ≠ j → ldeColLHS M (RBM.green M (RBM.zt E (a + b))) k j ≤
        Φ * ldeColRHS (RBM.Univ.Smix d L W g a b) (RBM.green M (RBM.zt E (a + b))) k j) →
      (∀ i, ldeQuadLHS M (RBM.green M (RBM.zt E (a + b))) (RBM.Univ.Smix d L W g a b) 1 i ≤
        Φ * ldeQuadRHS (RBM.Univ.Smix d L W g a b) (RBM.green M (RBM.zt E (a + b))) i) →
      (∀ i, ‖M i i‖ ^ 2 ≤ Φ * RBM.Univ.Smix d L W g a b i i) →
      ∀ i j : Idx d L W,
        llErrMat d L W E (a + b) M i j ^ 2 ≤ RBM.Univ.mixCdet d Λ κ * Φ ^ 2 * maxLoopPM d L W E (a + b) M

/-! ### T2293b (UN-42) pins -/

def T2293b_mixCq_pos : Prop := ∀ q : ℕ, 0 < mixCqV q

def T2293b_mixBad_tail : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) {a b : ℝ}, 0 ≤ a → 0 ≤ b → 0 < a + b → ∀ {z : ℂ}, z.im ≠ 0 →
    ∀ {Λ : ℝ}, 2 ≤ Λ → ∀ q : ℕ,
    RBM.Univ.gaussLaw d L W (RBM.Univ.mixVar d L W g a b) (mixBadV d L W g a b z Λ)
      ≤ ENNReal.ofReal (4 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * (mixCqV q / Λ ^ (q + 1)))

def T2293b_mixEntry_event_subset : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (sz : RBM.Gauss.Sizes d) (n : ℕ) {Λ κ E a b δ Φ T : ℝ},
    0 < sz.lam n → sz.lam n ≤ Λ → 0 < κ → |E| ≤ 2 - κ → 0 ≤ a → 0 ≤ b → 0 < a + b → a + b < 1 →
    δ ≤ RBM.Univ.mixDelta d Λ κ → 1 ≤ Φ → 36 * Φ * δ ^ 2 ≤ 1 → RBM.Univ.mixCdet d Λ κ * Φ ^ 2 ≤ T →
    {ω : RBM.Gauss.Sizes.SeqΩ sz × Ω d (sz.L n) (sz.W n) | ∃ i j : Idx d (sz.L n) (sz.W n),
      T * (maxLoopPM d (sz.L n) (sz.W n) E (a + b) (mixMatV sz n a b ω) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
        (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMatV sz n a b ω) x y ≤ δ
          then llErrMat d (sz.L n) (sz.W n) E (a + b) (mixMatV sz n a b ω) i j ^ 2 else 0)}
      ⊆ mixSampleV sz n a b ⁻¹' mixBadV d (sz.L n) (sz.W n) (sz.lam n) a b (RBM.zt E (a + b)) Φ

def T2293b_mixEntry_union : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ (sz : RBM.Gauss.Sizes d) (n : ℕ) {Λ κ E δ Φ T : ℝ},
    0 < sz.lam n → sz.lam n ≤ Λ → 0 < κ → |E| ≤ 2 - κ → ∀ {K : ℕ} {a b : Fin (K + 1) → ℝ},
    (∀ k, 0 ≤ a k ∧ 0 ≤ b k ∧ 0 < a k + b k ∧ a k + b k < 1) →
    δ ≤ RBM.Univ.mixDelta d Λ κ → 2 ≤ Φ → 36 * Φ * δ ^ 2 ≤ 1 → RBM.Univ.mixCdet d Λ κ * Φ ^ 2 ≤ T →
    ∀ q : ℕ,
    RBM.Univ.ouP (RBM.Univ.UNModel.band sz) n
      {ω | ∃ (k : Fin (K + 1)) (i j : Idx d (sz.L n) (sz.W n)),
        T * (maxLoopPM d (sz.L n) (sz.W n) E (a k + b k) (mixMatV sz n (a k) (b k) ω) +
            (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) <
          (if ∀ x y, llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMatV sz n (a k) (b k) ω) x y ≤ δ
            then llErrMat d (sz.L n) (sz.W n) E (a k + b k) (mixMatV sz n (a k) (b k) ω) i j ^ 2 else 0)}
      ≤ ENNReal.ofReal (((K : ℝ) + 1) * (4 * ((sz.size n : ℕ) : ℝ) ^ 2 * (mixCqV q / Φ ^ (q + 1))))

/-- **The main pin** (T2293b): `gueEntryMix (hd : 3 ≤ d) : GUEEntryMix d`. -/
def T2293b_gueEntryMix : Prop := ∀ d : ℕ, 3 ≤ d → GUEEntryMixV d

/-- The coupling window the proof uses (statement only): `Admissible` contains `WO 𝔡`, which gives
`0 < sz.lam n ≤ 𝔡⁻¹` eventually, i.e. `g := sz.lam n`, `Λ := 𝔡⁻¹` in `mixEntry_det`, `mixEntry_union`. -/
example {d : ℕ} (sz : RBM.Gauss.Sizes d) (𝔠 𝔡 : ℝ) : Prop :=
  sz.Admissible 𝔠 𝔡 → (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹) → T2293b_mixEntry_union

/-- The `d = 3` sequence instance shape (statement only): `sz0` (`L n = 4(n+1)`, `W n = (2(n+1))^5`,
`lam n = (2(n+1))^{-6}`), admissible at `(𝔠, 𝔡) = (1/6, 1/10)`, three mixtures at `u = 1/2`. -/
example : Prop :=
  RBM.Gauss.SizesInst.sz0.Admissible (1 / 6) (1 / 10) → GUEEntryMixV 3

end RBM.Univ.T2293Check

end
