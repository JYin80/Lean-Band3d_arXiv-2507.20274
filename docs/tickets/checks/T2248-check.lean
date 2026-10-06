/-
T2248 check file (MA-05b, `RBM3D/Main/QUEFromQDiff.lean`): compiles on `main` (8256045) as is.
Only imports of merged modules, `open`/`namespace`, `def … : Prop` pin texts, the vocabulary `def etaQ`
(probe text) and `#check`s of merged names.  No proofs, no `sorry`, no tactic blocks; no Mathlib lemma is
checked.  `RBM3D.Green.LDE` (`tendsto_W`) is not in the import closure of `RBM3D.Main.QUECore`.
-/
import RBM3D.Main.QUECore
import RBM3D.Green.LDE

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal ComplexConjugate

/-! ## 1. Merged names used (exact namespaces) -/

-- `RBM3D/Main/QUECore.lean` (389ad9e)
#check @RBM.Endpoints.MAThetaDiff
#check @RBM.Endpoints.thetaDiff
#check @RBM.Endpoints.queX
#check @RBM.Endpoints.queX_core
#check @RBM.Endpoints.queBad_sub
#check @RBM.Endpoints.que2Bad_sub
#check @RBM.Endpoints.queMarkov
#check @RBM.Endpoints.Inst.inst_thetaDiff
-- `RBM3D/Endpoints.lean` (8a43715)
#check @RBM.Endpoints.calB
#check @RBM.Endpoints.avg2
#check @RBM.Endpoints.ThetaPM
#check @RBM.Endpoints.ThetaPP
#check @RBM.Endpoints.profPM
#check @RBM.Endpoints.profPP
#check @RBM.Endpoints.qdBoundExp
#check @RBM.Endpoints.que2BadMat
#check @RBM.Endpoints.QUE
#check @RBM.Endpoints.QDiff
#check @RBM.Endpoints.calB_nonneg
#check @RBM.Endpoints.Nsz_pos
#check @RBM.Endpoints.locDomain_im_pos
#check @RBM.Endpoints.Inst.zI
#check @RBM.Endpoints.Inst.zI_im_pos
#check @RBM.Endpoints.Inst.zI_im_le
#check @RBM.Endpoints.Inst.zI_re_le
#check @RBM.Endpoints.Inst.inst_QUE
-- `RBM3D/Universality/Pins.lean` (f8ad4b4)
#check @RBM.Univ.Nsz
#check @RBM.Univ.queWindow
#check @RBM.Univ.queBound
#check @RBM.Univ.queBadMat
-- `RBM3D/Defs/Sizes.lean` (0a873f1)
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Bandwidth
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.locDomain
#check @RBM.Gauss.Sizes.lam_sq_mul_pow_ge
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.SizesInst.sz0_values
#check @RBM.Gauss.SizesInst.sz0_admissible
-- `RBM3D/Green/LDE.lean` (7c7652e)
#check @RBM.Green.tendsto_W
-- `RBM3D/Gauss/FineModel.lean` (0a873f1), `RBM3D/Loop/GLoopFlow.lean` (868b3b4)
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.isProbabilityMeasure_seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.Gn
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `RBM3D/Propagator/Basic.lean` (020ec7a), `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.msc
#check @RBM.norm_msc_lt_one
#check @RBM.Theta
#check @RBM.Zd

namespace RBM.Endpoints.T2248Check

/-! ## 2. Vocabulary (the new file declares it in `RBM.Endpoints`, body byte-equal: probe `:1870-1872`) -/

/-- The QUE scale `η_Q = W^{-ε₀} ilambda W^{d/2} / N` of `1_2:524-525`, the half-width of `𝓘_E(ε₀)` (`(eq:defIE)`). -/
def etaQ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (-ε₀) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n)

/-! ## 3a. Pins copied from the probe (`97d958e:RBM3D/Probe/T2192Pins.lean`), statements verbatim -/

/-- Probe `:1877-1879` (`queDomain`). -/
def queDomain_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ}, sz.Admissible 𝔠 𝔡 → ∀ {ε₀ κ : ℝ}, 0 < ε₀ → ε₀ < 𝔡 →
    ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - κ →
      sz.locDomain κ (𝔠 * (𝔡 - ε₀)) n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I)

/-- Probe `:1952-1954` (`calB_le_two_inv`, `(eq:BetaK)`). -/
def calB_le_two_inv_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ), 2 ≤ d → ∀ {η K : ℝ}, 0 < η → 0 ≤ K →
    η ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d → 0 < sz.lam n →
      calB sz n η K ≤ 2 * (Nsz sz n * η)⁻¹

/-- Probe `:1982-1983` (`que_three_terms`). -/
def que_three_terms_pin : Prop :=
  ∀ {x ε₀ 𝔡 : ℝ}, 1 ≤ x → 0 < ε₀ → 0 < 𝔡 → ε₀ ≤ 3 * 𝔡 / 5 →
    x ^ (ε₀ - 𝔡) + x ^ (-(2 * 𝔡 / 5)) + x ^ (-(2 * ε₀)) ≤ 3 * x ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)))

/-- Probe `:1994-1997` (`etaQ_le`). -/
def etaQ_le_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) {ε₀ 𝔡 : ℝ}, 0 < ε₀ → 0 < 𝔡 → 1 ≤ ((sz.W n : ℕ) : ℝ) →
    ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n →
      etaQ sz n ε₀ ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d

/-- Probe `:2020` (the pin `MAQUE`), verbatim; owned here. -/
def MAQUE_pin : Prop := QDiff → QUE

/-- `QUE_of_QDiff : MAQUE` (RBM2D `QUE_of_QDiff`, `RBM2D/Main/QUEFromQDiff.lean:1048`). -/
def QUE_of_QDiff_pin : Prop := MAQUE_pin

/-! ## 3b. Intermediate statements of the `d = 3` chain (dispatcher's; not in the probe) -/

/-- **Row differences of the profiles** (`1_2:534-537` into `(ssfa2_deter)`): from `thetaDiff`, with the same
constant for every `(sz, n)`: `K = C ilambda^{-2} W^{-d}` (the factor `‖m‖² < 1` absorbed). -/
def queRowDiff_pin : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ → ∀ a b b' : Zd d (sz.L n),
        ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
        ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d

/-- **QUE at one `(sz, n, E)`** (`(ssfa2)` + `(ssfa2_deter)` + Markov, at `z = E + iη_Q`): `queX_core` with
`c = δ_a` and `c = 1_A/|A|`, `queBad_sub`/`que2Bad_sub` (the window is `[E - η_Q, E + η_Q]`), `queMarkov` with
`s = W^{-2c}`, `f = 4N²η_Q² X_c`, `T = 4N²η_Q² · 4(K + ε)`. -/
def queFixed_pin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ),
    z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I → 0 < etaQ sz n ε₀ →
    (∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz)) -
          profPM sz n z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b ∂(Sizes.seqP sz)) -
          profPP sz n z a b‖ ≤ ε) →
    (∀ a b b' : Zd d (sz.L n),
      ‖profPM sz n z a b - profPM sz n z a b'‖ ≤ K ∧ ‖profPP sz n z a b - profPP sz n z a b'‖ ≤ K) →
    (∀ a : Zd d (sz.L n),
      Sizes.seqP sz {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      Sizes.seqP sz {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqXmat n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))))

/-- **The `d ≥ 3` exponent chain** (`1_2:539-543`): with `K = C ilambda^{-2} W^{-d}` and `ε = qdBoundExp` at
`τ/2`, `η_Q`, the Markov bound of `queFixed` is eventually below `W^{-(2ε₀)∧(2𝔡/5)+2c+τ}`
(`N²η_Q²K = C W^{-2ε₀}`; `Nη_Q 𝓑_{η_Q,0} ≤ 2`; `(ilambda² W^d)^{-1/5} ≤ W^{-2𝔡/5}`; `(Nη_Q)⁻¹ ≤ W^{ε₀-𝔡}`;
`que_three_terms`; the constant `3 max(16C, 128)` absorbed into `W^{τ/2}`). -/
def queChain_pin : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ {𝔠 𝔡 : ℝ} (sz : Sizes d), sz.Admissible 𝔠 𝔡 →
    ∀ ε₀ c τ C : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < τ → 0 < C →
      ∀ᶠ n in atTop,
        4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
            (4 * (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d + qdBoundExp sz n (τ / 2) (etaQ sz n ε₀))) /
          ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(min (2 * ε₀) (2 * 𝔡 / 5)) + 2 * c + τ)

end RBM.Endpoints.T2248Check

/-! ## 4. Instances (`d = 3`, `sz0`; namespace `RBM.Endpoints.Inst`) -/

namespace RBM.Endpoints.Inst.T2248Check

open RBM.Gauss.SizesInst RBM.Univ.UNInst

/-- Probe `:2387-2391` (`queDomain_edge`), verbatim except `etaQ` written with its check-file path. -/
def queDomain_edge_pin : Prop :=
  ∀ᶠ n in atTop, sz0.locDomain (1 / 10) (1 / 6 * (1 / 10 - 1 / 30)) n
      (((19 / 10 : ℝ) : ℂ) + (RBM.Endpoints.T2248Check.etaQ sz0 n (1 / 30) : ℂ) * Complex.I) ∧
    sz0.locDomain (1 / 10) (1 / 6 * (1 / 10 - 1 / 30)) n
      (((-(19 / 10) : ℝ) : ℂ) + (RBM.Endpoints.T2248Check.etaQ sz0 n (1 / 30) : ℂ) * Complex.I)

/-- Probe `:2448-2450` (`inst_queDomain`), same convention. -/
def inst_queDomain_pin : Prop :=
  ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
    sz0.locDomain (1 / 10) (1 / 6 * (1 / 10 - 1 / 30)) n
      ((E : ℂ) + (RBM.Endpoints.T2248Check.etaQ sz0 n (1 / 30) : ℂ) * Complex.I)

/-- Probe `:2477-2478` (`inst_BetaK`). -/
def inst_BetaK_pin : Prop :=
  calB sz0 0 (3 / 1000000) 0 ≤ 2 * (((sz0.size 0 : ℕ) : ℝ) * (3 / 1000000))⁻¹

/-- Probe `:2485-2487` (`inst_three_terms`). -/
def inst_three_terms_pin : Prop :=
  (32 : ℝ) ^ ((1 / 30 : ℝ) - 1 / 10) + (32 : ℝ) ^ (-(2 * (1 / 10 : ℝ) / 5)) + (32 : ℝ) ^ (-(2 * (1 / 30 : ℝ))) ≤
    3 * (32 : ℝ) ^ (-(min (2 * (1 / 30 : ℝ)) (2 * (1 / 10 : ℝ) / 5)))

/-- `queRowDiff` at `d = 3`, `𝔡 = κ = 1/10`, `sz0`, `n = 0` (`ilambda = 1/64 ≤ 10`), `z = zI`. -/
def inst_queRowDiff_pin : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Zd 3 (sz0.L 0),
    ‖profPM sz0 0 zI a b - profPM sz0 0 zI a b'‖ ≤ C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3 ∧
    ‖profPP sz0 0 zI a b - profPP sz0 0 zI a b'‖ ≤ C * (sz0.lam 0 ^ 2)⁻¹ / ((sz0.W 0 : ℕ) : ℝ) ^ 3

/-- `queChain` at `sz0` (`(𝔠, 𝔡) = (1/6, 1/10)`), `ε₀ = 1/30`, `c = 1/60`, `τ = 1/10`, `C = 1`. -/
def inst_queChain_pin : Prop :=
  ∀ᶠ n in atTop,
    4 * Nsz sz0 n ^ 2 * RBM.Endpoints.T2248Check.etaQ sz0 n (1 / 30) ^ 2 *
        (4 * (1 * (sz0.lam n ^ 2)⁻¹ / ((sz0.W n : ℕ) : ℝ) ^ 3 +
          qdBoundExp sz0 n (1 / 10 / 2) (RBM.Endpoints.T2248Check.etaQ sz0 n (1 / 30)))) /
      ((sz0.W n : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))) ≤
    ((sz0.W n : ℕ) : ℝ) ^ (-(min (2 * (1 / 30 : ℝ)) (2 * (1 / 10 : ℝ) / 5)) + 2 * (1 / 60) + 1 / 10)

/-- `queFixed` at `sz0`, `n = 0`, `ε₀ = 1/30`, `c = 1/60`, `E = 0`: the expectation half (another gate's pin) stays a
hypothesis; the row-difference hypothesis is discharged (`queRowDiff`; `0 < η_Q = 1.2·10⁻⁶ ≤ 1`). -/
def inst_queFixed_pin : Prop :=
  ∀ (z : ℂ), z = ((0 : ℝ) : ℂ) + (RBM.Endpoints.T2248Check.etaQ sz0 0 (1 / 30) : ℂ) * Complex.I → ∀ ε : ℝ,
    (∀ a b : Zd 3 (sz0.L 0),
      ‖(∫ ω, avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP sz0)) -
          profPM sz0 0 z a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz0 0 (fun x y => sz0.Gn 0 z ω x y * sz0.Gn 0 z ω y x) a b ∂(Sizes.seqP sz0)) -
          profPP sz0 0 z a b‖ ≤ ε) →
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ a : Zd 3 (sz0.L 0),
        Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 a (sz0.seqXmat 0 ω)} ≤
          ENNReal.ofReal (4 * Nsz sz0 0 ^ 2 * RBM.Endpoints.T2248Check.etaQ sz0 0 (1 / 30) ^ 2 * (4 * (K + ε)) /
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))))) ∧
      (∀ A : Finset (Zd 3 (sz0.L 0)), A.Nonempty →
        Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (1 / 30) (1 / 60) 0 A (sz0.seqXmat 0 ω)} ≤
          ENNReal.ofReal (4 * Nsz sz0 0 ^ 2 * RBM.Endpoints.T2248Check.etaQ sz0 0 (1 / 30) ^ 2 * (4 * (K + ε)) /
            ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ)))))

/-- `QUE_of_QDiff` at the instance: the statement of the merged `inst_QUE` (`Endpoints.lean:575-582`) from `QDiff`. -/
def inst_QUE_of_QDiff_pin : Prop :=
  QDiff → ∀ᶠ n in atTop, ∀ E : ℝ, |E| ≤ 2 - 1 / 10 →
    (∀ a : Zd 3 (sz0.L n),
      Sizes.seqP sz0 {ω | queBadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E a (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10)) ∧
    (∀ A : Finset (Zd 3 (sz0.L n)), A.Nonempty →
      Sizes.seqP sz0 {ω | que2BadMat 3 (sz0.L n) (sz0.W n) (sz0.lam n) (1 / 30) (1 / 60) E A (sz0.seqXmat n ω)} ≤
        queBound (sz0.W n) (1 / 10) (1 / 30) (1 / 60) (1 / 10))

end RBM.Endpoints.Inst.T2248Check

end
