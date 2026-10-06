/-
T2240 check file (MA-05a, `RBM3D/Main/QUECore.lean`): compiles on `main` (e5b944a) as is.
Only imports of merged modules, `open`/`namespace`, `def … : Prop` pin texts, vocabulary
`noncomputable def`s and `#check`s of merged names.  No proofs, no `sorry`, no tactic blocks.
-/
import RBM3D.Endpoints
import RBM3D.Propagator.Prop6Hold
import RBM3D.Propagator.Pins
import RBM3D.Green.EntryCore
import RBM3D.Induction.ContinuityNet

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal ComplexConjugate

/-! ## 1. Merged names used (exact namespaces) -/

-- `RBM3D/Endpoints.lean` (8a43715)
#check @RBM.Endpoints.avg2
#check @RBM.Endpoints.profPM
#check @RBM.Endpoints.profPP
#check @RBM.Endpoints.ThetaPM
#check @RBM.Endpoints.ThetaPP
#check @RBM.Endpoints.que2BadMat
#check @RBM.Endpoints.QUE
#check @RBM.Endpoints.QDiff
#check @RBM.Endpoints.Nsz_pos
#check @RBM.Endpoints.Inst.zI
#check @RBM.Endpoints.Inst.zI_im_pos
#check @RBM.Endpoints.Inst.zI_im_le
#check @RBM.Endpoints.Inst.zI_re_le
-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.IsOrthoEigenbasis
#check @RBM.Univ.UNInst.isOrthoEigenbasis_zero
#check @RBM.Univ.queWindow
#check @RBM.Univ.queBadMat
#check @RBM.Univ.queBound
#check @RBM.Univ.Nsz
-- `RBM3D/Loop/GLoopFlow.lean` (868b3b4), `RBM3D/Gauss/FineModel.lean`, `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Gn
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqXmat_isHermitian
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.card_Iblk
#check @RBM.Gauss.SizesInst.sz0
-- `RBM3D/Green/EntryCore.lean` (890a89f), `RBM3D/Induction/ContinuityNet.lean` (5b6cbc1)
#check @RBM.green
#check @RBM.Ind.ContinuityNet.cont_Gres_true_eq_green
-- Propagator (`Basic` 020ec7a, `Pins` b06ff9b, `Prop6Hold` 6cc5032), `Defs/Block` (a722f63)
#check @RBM.Theta
#check @RBM.Theta0
#check @RBM.Theta0_apply
#check @RBM.Theta_apply_add_right
#check @RBM.prop5to8_holds
#check @RBM.PropSpin
#check @RBM.norm_SB
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.msc
#check @RBM.mE_im
#check @RBM.mE_lemE
#check @RBM.norm_mE
#check @RBM.norm_msc_pos
#check @RBM.norm_msc_lt_one
#check @RBM.lemT_pos
#check @RBM.lemT_lt_one
#check @RBM.abs_lemE_lt_two
#check @RBM.lemma28_quant
#check @RBM.zdistD
#check @RBM.Zd

namespace RBM.Endpoints.T2240Check

/-! ## 2. Vocabulary (the new file declares these in `RBM.Endpoints`, bodies byte-equal) -/

/-- `Im G = (G - G†)/(2i)` (RBM2D `QUEFromQDiff_imG`, `QUEFromQDiff.lean:44`). -/
noncomputable def queImG {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ) :
    Matrix ι ι ℂ :=
  ((2 : ℂ) * Complex.I)⁻¹ • (RBM.green H z - (RBM.green H z)ᴴ)

/-- `E_a = W^{-d} 1_{[a]}` (diagonal; RBM2D `Epaper`). -/
noncomputable def queBlk (d L W : ℕ) [NeZero L] [NeZero W] (a : Zd d L) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  Matrix.diagonal fun x => if x ∈ Iblk d L W a then (((W : ℂ) ^ d)⁻¹) else 0

/-- `B_c = ∑_u (c_u - L^{-d}) E_u` (RBM2D `QUEFromQDiff_B`, `:345`, `L²` → `L^d`). -/
noncomputable def queObs (d L W : ℕ) [NeZero L] [NeZero W] (c : Zd d L → ℝ) :
    Matrix (Idx d L W) (Idx d L W) ℂ :=
  ∑ u, (((c u - ((L : ℝ) ^ d)⁻¹ : ℝ)) : ℂ) • queBlk d L W u

/-- `X_c(ω) = Re tr(Im G B_c Im G B_c)` at `H = seqXmat n ω` (RBM2D `QUEFromQDiff_X`, `:510`). -/
noncomputable def queX {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (c : Zd d (sz.L n) → ℝ) (ω : sz.SeqΩ) : ℝ :=
  (Matrix.trace (queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c *
    queImG (sz.seqXmat n ω) z * queObs d (sz.L n) (sz.W n) c)).re

/-! ## 3. Pins (owned pin verbatim from the probe; intermediate statements: dispatcher's) -/

/-- Probe `97d958e:RBM3D/Probe/T2192Pins.lean:677-684` verbatim, except that the instance proof
`⟨by omega⟩` is written as the term `NeZero.of_pos (lt_of_lt_of_le three_pos hL)` (check-file rule: no
tactic blocks; `NeZero L` is a `Prop`, so the two texts are equal by `rfl`). -/
def MAThetaDiff_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d L,
        haveI : NeZero L := NeZero.of_pos (lt_of_lt_of_le three_pos hL)
        ‖Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b - Theta d L g (((‖msc z‖ ^ 2 : ℝ)) : ℂ) a b'‖ ≤
            C * (g ^ 2)⁻¹ ∧
        ‖Theta d L g (msc z ^ 2) a b - Theta d L g (msc z ^ 2) a b'‖ ≤ C * (g ^ 2)⁻¹

/-- `thetaDiff : MAThetaDiff` (compiled in the probe, `:706-770`). -/
def thetaDiff_pin : Prop := MAThetaDiff_pin

/-- `(ssfa2)` (`1_2:524-530`; RBM2D `QUEFromQDiff_normSq_le`, `:204`): for eigenvalues within `η` of `E`,
`|ψ_k^* B ψ_{k'}|² ≤ 4η² Re tr(Im G B Im G B)` at `z = E + iη`, any Hermitian `B`. -/
def normSq_le_trace_pin : Prop :=
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (μ : ι → ℝ) (ψ : ι → ι → ℂ),
    IsOrthoEigenbasis H μ ψ → ∀ E η : ℝ, 0 < η → ∀ B : Matrix ι ι ℂ, Bᴴ = B → ∀ k k' : ι,
      |μ k - E| ≤ η → |μ k' - E| ≤ η →
        Complex.normSq (star (ψ k) ⬝ᵥ (B *ᵥ ψ k')) ≤
          4 * η ^ 2 * (Matrix.trace (queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B *
            queImG H ((E : ℂ) + (η : ℂ) * Complex.I) * B)).re

/-- Markov (RBM2D `QUEFromQDiff_markov`, `:798`). -/
def queMarkov_pin : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ),
    Integrable f P → (∀ ω, 0 ≤ f ω) → ∀ {s T : ℝ}, 0 < s → ∫ ω, f ω ∂P ≤ T →
      ∀ S : Set Ω, S ⊆ {ω | s ≤ f ω} → P S ≤ ENNReal.ofReal (T / s)

/-- **The core** (`(que0)`, `1_2:531-537`; RBM2D `QUEFromQDiff_core`, `:564`): if the expectation half of
`QDiff` holds at `z` with error `ε` and the profiles vary along rows by at most `K`, then for every
probability vector `c` on the blocks, `X_c ≥ 0`, `X_c` is integrable and `E X_c ≤ 4 (K + ε)`. -/
def queX_core_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ε K : ℝ,
    (∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε) →
    (∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K) →
    ∀ c : Zd d (sz.L n) → ℝ, (∀ u, 0 ≤ c u) → ∑ u, c u = 1 →
      Integrable (queX sz n z c) (Sizes.seqP sz) ∧ (∀ ω, 0 ≤ queX sz n z c ω) ∧
        ∫ ω, queX sz n z c ω ∂(Sizes.seqP sz) ≤ 4 * (K + ε)

/-- `(Meq:QUE)` event `⊆ {W^{-2c} ≤ 4N²η² X_{δ_a}}` (RBM2D `QUEFromQDiff_queBad_sub`, `:671`), when the
window `𝓘_E(ε₀)` lies in `[E - η, E + η]`. -/
def queBad_sub_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ), 0 < η →
    (∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η) →
    ∀ a : Zd d (sz.L n),
      {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ⊆
        {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
          4 * Nsz sz n ^ 2 * η ^ 2 *
            queX sz n ((E : ℂ) + (η : ℂ) * Complex.I) (fun u => if u = a then 1 else 0) ω}

/-- `(Meq:QUE2)` event `⊆ {W^{-2c} ≤ 4N²η² X_{1_A/|A|}}` (RBM2D `QUEFromQDiff_que2Bad_sub`, `:704`). -/
def que2Bad_sub_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E η : ℝ), 0 < η →
    (∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η) →
    ∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ⊆
        {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
          4 * Nsz sz n ^ 2 * η ^ 2 *
            queX sz n ((E : ℂ) + (η : ℂ) * Complex.I)
              (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) ω}

end RBM.Endpoints.T2240Check

/-! ## 4. Instances (`d = 3`, `sz0`; namespace `RBM.Endpoints.Inst`) -/

namespace RBM.Endpoints.Inst.T2240Check

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- Probe `:2440-2443` (statement of `inst_thetaDiff`), verbatim. -/
def inst_thetaDiff_pin : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ b b' : Zd 3 4,
    ‖Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b - Theta 3 4 (1 / 64) (((‖msc zI‖ ^ 2 : ℝ)) : ℂ) 0 b'‖ ≤
        C * ((1 / 64 : ℝ) ^ 2)⁻¹ ∧
      ‖Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b - Theta 3 4 (1 / 64) (msc zI ^ 2) 0 b'‖ ≤ C * ((1 / 64 : ℝ) ^ 2)⁻¹

/-- `queBad_sub` at `sz0`, `n = 0`, `ε₀ = 1/30`, `c = 1/60`, `E = 0`, `η = 1` (the window hypothesis is
discharged: `32^{-1/30} · (1/64) · 32^{3/2} / 2097152 ≤ 1`). -/
def inst_queBad_sub_pin : Prop :=
  ∀ a : Zd 3 (sz0.L 0),
    {ω | queBadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 a (sz0.seqXmat 0 ω)} ⊆
      {ω | ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))) ≤
        4 * Nsz sz0 0 ^ 2 * (1 : ℝ) ^ 2 *
          RBM.Endpoints.T2240Check.queX sz0 0 (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)
            (fun u => if u = a then 1 else 0) ω}

end RBM.Endpoints.Inst.T2240Check

end
