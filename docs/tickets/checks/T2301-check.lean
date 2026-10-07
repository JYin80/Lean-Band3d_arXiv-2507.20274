/-
Release check for T2301 (UN-29) (dispatcher V1, Tue Oct  6 13:40 UTC 2026; CLAUDE.md §4 step 0;
DECISIONS §16, §20, §29, §45 O2, §54, §57 (1)(2), §90, §91 (1), §93 (1), §95 (4)).
UN-29 (bulk universality, GUE phase): port of RBM2D `Universality/GUEPhase/KPrim.lean` at `c9a24cf`
(909 lines; `:1-797` ported, the instance namespace `KPrimCheck` `:799-907` rewritten at `d = 3`) to `d ≥ 3`:
the zero-mode coefficient `gueShift`, the 2-loop primitive `kTwoGUE = W^{-d} μ (Θ_{t₁μ}(g) + β(t) J)`
(`μ = m(σ₁) m(σ₂)`, band coupling `g`), its loop form `kTwoGUELoop`, (7.25) `kTwoGUE_eq_ThetaTilde`, (7.33) at
`n = 2`, `t K` at the spectral parameter of Lemma 2.8, the bridges to the band OU profile `profPMTilde`/`profPPTilde`
(= `UNOUProfile.band`), and `gueK_exists` (global existence of the primitive loops on `[t₁, t₀]`).
Class T of T2173 (`docs/reports/T2173-portmap.md:251`): band here; the BA form (matrix `M^{(σ₁,σ₂)}`, `Θ^{BA}`) is BA-C3
`BA/GUEKPrim` (`:275`).  New file `RBM3D/Universality/GUEPhase/KPrim.lean`, namespace `RBM.Univ.GUEPhase`.
Section 1: the merged names the new file builds on (full namespaces).
Section 2: vocabulary (`gueShiftV`, `kTwoGUEV`, `kTwoGUELoopV`) and the pinned statements as `def … : Prop` in the
temporary namespace `RBM.Univ.GUEPhase.T2301Check`.  The library states each pin as a theorem in `RBM.Univ.GUEPhase`
whose type is exactly this body after unfolding the vocabulary.
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2301-check.lean`.
-/
import RBM3D
import Mathlib.Analysis.ODE.ExistUnique

/-! ## 1. Merged names -/

-- `RBM3D/Universality/GUEPhase/Bootstrap.lean` (98e6d5b, UN-26a = T2202)
#check @RBM.Univ.GUEPhase.SBgue
#check @RBM.Univ.GUEPhase.SBgue_apply
#check @RBM.Univ.GUEPhase.sum_SBgue_col
#check @RBM.Univ.GUEPhase.sum_SBgue_row
#check @RBM.Univ.GUEPhase.primBilGUE
#check @RBM.Univ.GUEPhase.primRhsGUE
#check @RBM.Univ.GUEPhase.finite_loopIdx
-- `RBM3D/Universality/ZeroModeProfile.lean` (66cddb4, UN-51a = T2276)
#check @RBM.Univ.Jmat
#check @RBM.Univ.SBtilde
#check @RBM.Univ.ThetaTilde
#check @RBM.Univ.ThetaTilde_eq
#check @RBM.Univ.profPMTilde
#check @RBM.Univ.profPPTilde
-- `RBM3D/Universality/OUInterfaceK.lean` (5b55824, UN-51g = T2282)
#check @RBM.Univ.UNOUProfile
#check @RBM.Univ.UNOUProfile.band
-- `RBM3D/Propagator/Basic.lean` (020ec7a), `Propagator/Props4.lean` (892334b), `Defs/Block.lean` (a722f63)
#check @RBM.Theta
#check @RBM.Theta_transpose_of_three_le
#check @RBM.sum_Theta_row_of_three_le
#check @RBM.SB
#check @RBM.sum_SB_row
#check @RBM.norm_SB
-- `RBM3D/Loop/Primitive.lean` (58329b9), `Loop/KLTree.lean` (b06ff9b), `Loop/TreeRep.lean` (b06ff9b)
#check @RBM.Loop.kTwo
#check @RBM.Loop.KLgen
#check @RBM.Loop.KLK
#check @RBM.Loop.KLK_two_eq_kTwo
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.WF
#check @RBM.Loop.LoopIdx.length
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
#check @RBM.Loop.LoopIdx.length_cutGlueL
#check @RBM.Loop.LoopIdx.length_cutGlueR
#check @RBM.Loop.LoopIdx.length_cutGlueL_le
#check @RBM.Loop.LoopIdx.length_cutGlueR_le
#check @RBM.Loop.LoopIdx.wf_cutGlueL
#check @RBM.Loop.LoopIdx.wf_cutGlueR
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `Defs/Lattice.lean` (51f1a17), `Defs/Sizes.lean` (0a873f1)
#check @RBM.mE
#check @RBM.norm_mE
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.lemE
#check @RBM.lemT
#check @RBM.lemT_pos
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
#check @RBM.msc_eq_sqrt_mul_mE
#check @RBM.Zd
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.lam
#check @RBM.Gauss.Sizes.three_le_L
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.Gauss.SizesInst.sz0
-- Mathlib (rev 5ed2965, same as RBM2D `c9a24cf`)
#check @IsPicardLindelof
#check @IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
#check @LipschitzWith.of_dist_le_mul

/-! ## 2. Vocabulary and pins -/

namespace RBM.Univ.GUEPhase.T2301Check

open RBM RBM.Loop RBM.Univ RBM.Univ.GUEPhase

/-- `gueShift`: `β(t) = (t - t₁) μ / (L^d (1 - t₁ μ)(1 - t μ))` (RBM2D `:64`, `L² ↦ L^d`). -/
noncomputable def gueShiftV (d L : ℕ) (μ : ℂ) (t1 t : ℝ) : ℂ :=
  ((t : ℂ) - t1) * μ / ((L : ℂ) ^ d * (1 - (t1 : ℂ) * μ) * (1 - (t : ℂ) * μ))

/-- `kTwoGUE`: `W^{-d} μ (Θ_{t₁μ}(g) + β(t) J)_{ab}` (RBM2D `:71`, `W² ↦ W^d`, `Θ ↦ Θ(g)`). -/
noncomputable def kTwoGUEV (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ)
    (σ₁ σ₂ : Bool) (a b : Zd d L) : ℂ :=
  ((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂) *
    (Theta d L g ((t1 : ℂ) * (m σ₁ * m σ₂)) a b + gueShiftV d L (m σ₁ * m σ₂) t1 t)

/-- `kTwoGUELoop`: `kTwoGUE` on loop indices, `0` off the 2-loops (RBM2D `:77`). -/
noncomputable def kTwoGUELoopV (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ)
    (I : LoopIdx (Zd d L)) : ℂ :=
  match I.σ, I.a with
  | [σ₁, σ₂], [a₁, a₂] => kTwoGUEV d L W g m t1 t σ₁ σ₂ a₁ a₂
  | _, _ => 0

/-- Target 1 `kTwoGUE_self` (RBM2D `:84`). -/
def T2301_kTwoGUE_self : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ) (m : Bool → ℂ) (t1 : ℝ) (σ₁ σ₂ : Bool) (a b : Zd d L),
    kTwoGUEV d L W g m t1 t1 σ₁ σ₂ a b = kTwo d L W g m t1 σ₁ σ₂ a b

/-- Target 2 `kTwoGUE_eq_ThetaTilde` ((7.25), RBM2D `:92`). -/
def T2301_kTwoGUE_eq_ThetaTilde : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) (g : ℝ), 3 ≤ L → ∀ (m : Bool → ℂ) (ζ t0 : ℝ) (σ₁ σ₂ : Bool),
    ‖(t0 : ℂ) * (m σ₁ * m σ₂)‖ < 1 → 0 ≤ ζ → ζ ≤ 1 → ∀ a b : Zd d L,
      kTwoGUEV d L W g m ((1 - ζ) * t0) t0 σ₁ σ₂ a b
        = ((W : ℂ) ^ d)⁻¹ * (m σ₁ * m σ₂) * ThetaTilde d L g ζ ((t0 : ℂ) * (m σ₁ * m σ₂)) a b

/-- Target 3 `primRhsGUE_two` (RBM2D `:111`). -/
def T2301_primRhsGUE_two : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L),
    primRhsGUE d L W K ⟨[σ₁, σ₂], [a₁, a₂]⟩
      = (W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          K ⟨[σ₁, σ₂], [a₁, a]⟩ * SBgue d L a b * K ⟨[σ₁, σ₂], [b, a₂]⟩

/-- Target 4 `kTwoGUE_deriv_identity` (RBM2D `:132`; the source's scalar `d = t - t₁` is renamed `s`,
`W² ↦ W^d`, `L² ↦ L^d`). -/
def T2301_kTwoGUE_deriv_identity : Prop :=
  ∀ (d : ℕ) (W μ p q s L : ℂ), q + s * μ = p → p ≠ 0 → q ≠ 0 → L ≠ 0 →
    (W ^ d)⁻¹ * μ * ((μ * (L ^ d * p * q) - s * μ * (L ^ d * p * -μ)) / (L ^ d * p * q) ^ 2)
      = (W ^ d)⁻¹ * μ ^ 2 * (L ^ d)⁻¹ *
        ((p⁻¹ + L ^ d * (s * μ / (L ^ d * p * q))) * (p⁻¹ + L ^ d * (s * μ / (L ^ d * p * q))))

/-- Target 5 `hasDerivAt_kTwoGUE` ((7.33) at `n = 2`, RBM2D `:151`). -/
def T2301_hasDerivAt_kTwoGUE : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool), 3 ≤ L →
    ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1 → (t : ℂ) * (m σ₁ * m σ₂) ≠ 1 → ∀ a₁ a₂ : Zd d L,
      HasDerivAt (fun s : ℝ => kTwoGUEV d L W g m t1 s σ₁ σ₂ a₁ a₂)
        ((W : ℂ) ^ d * ∑ a : Zd d L, ∑ b : Zd d L,
          kTwoGUEV d L W g m t1 t σ₁ σ₂ a₁ a * SBgue d L a b * kTwoGUEV d L W g m t1 t σ₁ σ₂ b a₂) t

/-- Target 6 `hasDerivAt_kTwoGUELoop` (RBM2D `:210`). -/
def T2301_hasDerivAt_kTwoGUELoop : Prop :=
  ∀ (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (m : Bool → ℂ) (t1 t : ℝ) (σ₁ σ₂ : Bool), 3 ≤ L →
    ‖(t1 : ℂ) * (m σ₁ * m σ₂)‖ < 1 → (t : ℂ) * (m σ₁ * m σ₂) ≠ 1 → ∀ a₁ a₂ : Zd d L,
      HasDerivAt (fun s : ℝ => kTwoGUELoopV d L W g m t1 s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
        (primRhsGUE d L W (kTwoGUELoopV d L W g m t1 t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t

/-- Target 7 `lemT_mul_kTwoGUE_pm` (RBM2D `:267`). -/
def T2301_lemT_mul_kTwoGUE_pm : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (g : ℝ), 3 ≤ L → ∀ z : ℂ, 0 < z.im → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
    ∀ a b : Zd d L,
      (lemT z : ℂ) * kTwoGUEV d L W g (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true false a b
        = ((W : ℂ) ^ d)⁻¹ * ((‖msc z‖ ^ 2 : ℝ) : ℂ) * ThetaTilde d L g ζ ((‖msc z‖ ^ 2 : ℝ) : ℂ) a b

/-- Target 8 `lemT_mul_kTwoGUE_pp` (RBM2D `:284`). -/
def T2301_lemT_mul_kTwoGUE_pp : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (g : ℝ), 3 ≤ L → ∀ z : ℂ, 0 < z.im → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
    ∀ a b : Zd d L,
      (lemT z : ℂ) * kTwoGUEV d L W g (mSigma (lemE z)) ((1 - ζ) * lemT z) (lemT z) true true a b
        = ((W : ℂ) ^ d)⁻¹ * msc z ^ 2 * ThetaTilde d L g ζ (msc z ^ 2) a b

/-- Target 9 (new) `lemT_mul_kTwoGUE_pm_eq_profPMTilde`: the band OU profile (`UNOUProfile.band`'s `pm`) is
`t K^{(+,-)}` of the GUE phase at the band coupling `sz.lam n`. -/
def T2301_lemT_mul_kTwoGUE_pm_eq_profPMTilde : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
    ∀ a b : Zd d (sz.L n),
      (lemT z : ℂ) * kTwoGUEV d (sz.L n) (sz.W n) (sz.lam n) (mSigma (lemE z)) ((1 - ζ) * lemT z)
          (lemT z) true false a b
        = profPMTilde sz n ζ z a b

/-- Target 10 (new) `lemT_mul_kTwoGUE_pp_eq_profPPTilde` (`UNOUProfile.band`'s `pp`). -/
def T2301_lemT_mul_kTwoGUE_pp_eq_profPPTilde : Prop :=
  ∀ (d : ℕ) (sz : RBM.Gauss.Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ζ : ℝ, 0 ≤ ζ → ζ ≤ 1 →
    ∀ a b : Zd d (sz.L n),
      (lemT z : ℂ) * kTwoGUEV d (sz.L n) (sz.W n) (sz.lam n) (mSigma (lemE z)) ((1 - ζ) * lemT z)
          (lemT z) true true a b
        = profPPTilde sz n ζ z a b

/-- Target 11 `gueK_exists` ((7.33), RBM2D `:762`): initial value `KLgen d L g W (mSigma E) t₁`
(`= KLK d L g W E t₁` by `rfl`). -/
def T2301_gueK_exists : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g E t1 t0 : ℝ) (n0 : ℕ), 3 ≤ L → |E| < 2 → 0 ≤ t1 →
    t1 ≤ t0 → t0 < 1 →
    ∃ Kt : ℝ → LoopIdx (Zd d L) → ℂ,
      (∀ I : LoopIdx (Zd d L), Kt t1 I = KLgen d L g W (mSigma E) t1 I) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ I : LoopIdx (Zd d L), I.WF → 1 ≤ I.length → I.length ≤ n0 →
        HasDerivWithinAt (fun s : ℝ => Kt s I) (primRhsGUE d L W (Kt t) I) (Set.Icc t1 t0) t) ∧
      (∀ t ∈ Set.Icc t1 t0, ∀ σ₁ σ₂ : Bool, ∀ a b : Zd d L,
        Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEV d L W g (mSigma E) t1 t σ₁ σ₂ a b)

/-! Shape checks at the instance data (`d = 3`, `L = 3`, `W = 2`, `g = 1`, `E = 0`): statements only. -/

example : Prop :=
  ∀ (σ₁ σ₂ : Bool) (a b : Zd 3 3),
    kTwoGUEV 3 3 2 1 (mSigma 0) (7 / 20) (7 / 20) σ₁ σ₂ a b = kTwo 3 3 2 1 (mSigma 0) (7 / 20) σ₁ σ₂ a b

example : Prop :=
  ∀ I : LoopIdx (Zd 3 3), KLK 3 3 1 2 0 (7 / 20) I = KLgen 3 3 1 2 (mSigma 0) (7 / 20) I

example : Prop :=
  ∀ a b : Zd 3 (RBM.Gauss.SizesInst.sz0.L 0),
    (lemT Complex.I : ℂ) * kTwoGUEV 3 (RBM.Gauss.SizesInst.sz0.L 0) (RBM.Gauss.SizesInst.sz0.W 0)
        (RBM.Gauss.SizesInst.sz0.lam 0) (mSigma (lemE Complex.I)) ((1 - 1 / 2) * lemT Complex.I)
        (lemT Complex.I) true false a b
      = profPMTilde RBM.Gauss.SizesInst.sz0 0 (1 / 2) Complex.I a b

end RBM.Univ.GUEPhase.T2301Check
