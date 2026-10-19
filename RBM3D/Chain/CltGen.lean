/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.Step5Pins

/-!
# The generic CLT hypotheses of Step 5, case (i), over a flow carrier

Definitions over a carrier `C : FlowFM sz`, a law `μ` and a base matrix `H₀`: the conclusions
`STCltIsoConclgL`, `STCltFarConclgL`, `STExpInvgL` (with `STfFarg`, `STcltBg`, `STcltXg`); the inputs
`STGijDecgL`, `STKfargL`, `STMfarg`, `STThPropsg`, `STKpropsg`; the representation `CltRepg` and the
invariance `CltInvg`; the hypothesis block `HCltOf`; and the statements `STCltIsogL`
((5.36) `eq:bound_isolated`) and `STCltFargL` (Lemma 5.1, `lem;CLT`).  Spectral reading:
`ztOf (C.m n) (E n) u` with `κ ≤ (C.m n).im`; neither `|E| ≤ 2 - κ` nor `‖m‖ = 1` is assumed.
Every size-level quantity reads `sz.lam`; `STThPropsg`, `STKpropsg` are stated at `sz.lam`, and a
`Θ`-profile proved at a kernel coupling `gK` reaches them through the comparison
`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`, which is not a
hypothesis of any statement here.  The band case is treated at the end.
-/
set_option linter.style.longLine false
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal
noncomputable section
namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- The carrier propagator `Θ^{(σσ')}_t = (1 - t M^{(σσ')} S)⁻¹`. -/
def STThg (n : ℕ) (σ σ' : Bool) (t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ)

open Classical in
/-- `f^{far}` over the carrier: the band `STfFar` with `C.L - C.K` and the carrier propagator `Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) t`. -/
def STfFarg (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ : Zd d (sz.L n),
      Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) (a 0) b₁ *
        (C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) *
        (Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) b₂ (a 1) -
          Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) b₁ (a 1))

/-- Conclusion of `STCltFargL`. -/
def STCltFarConclgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p ω => ‖STfFarg C n (s n) (t n) p.1.1.1 p.1.2 ω‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) / (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))

/-- `𝗕_b` over the carrier. -/
def STcltBg (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) * (C.L n s σ b ω - C.K n s σ b)

/-- The centred factor. -/
def STcltXg (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (cj : Bool) (ω : sz.SeqΩ) : ℂ :=
  if cj then (starRingEnd ℂ) (STcltBg C n s σ b ω - ∫ ω', STcltBg C n s σ b ω' ∂μ)
  else STcltBg C n s σ b ω - ∫ ω', STcltBg C n s σ b ω' ∂μ

/-- Conclusion of `STCltIsogL`. -/
def STCltIsoConclgL (s : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
    ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
      (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n)) →
      (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), STcltXg C μ n (s n) σ (b k) (decide (p ≤ k.val)) ω ∂μ‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- The invariance of the expected loops `𝔼 𝓛^{(2)}` under translations and the reflection. -/
def STExpInvgL : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
    (∫ ω, C.L n u σ (fun i => a i + c) ω ∂μ = ∫ ω, C.L n u σ a ω ∂μ) ∧
    (∫ ω, C.L n u σ (fun i => -a i) ω ∂μ = ∫ ω, C.L n u σ a ω ∂μ)

/-- `C` represents `H₀ + H_u` of the law `seqP (sz.withLam g')` at `ztOf (C.m n) (E n) u`: the Green function and all loops are those of the
Hermitian matrix `H₀ n + seqHflow` (band: `H₀ = 0`, `g' = sz.lam`; block Anderson: `H₀ = λ₀Ψ`, `g' = 0`). -/
def CltRepg (g' E : ℕ → ℝ) : Prop :=
  μ = Sizes.seqP (sz.withLam g') ∧ (∀ n, (H₀ n).IsHermitian) ∧ ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
    (∀ x y, C.G n u ω x y = Gres (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)
        (ztOf (C.m n) (E n) u) true x y) ∧
    ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      C.L n u σ a ω = loopFine d (sz.L n) (sz.W n)
        (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)
        (ztOf (C.m n) (E n) u) σ a

/-- Off-diagonal Green input: the shape of (8.10) `GijGEX_BA` (`BAGbEXPij'`), with the loop hypothesis for both mixed charges (`STgexRHSg` sums both). -/
def STGijDecgL (t : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
    ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
      (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
      (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (t n) p.1.1 ![p.2.1, p.2.2] ω‖)
        (fun n p _ => Φ n p.2.1 p.2.2 ^ 2) →
      PrecL sz μ
        (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1.1 p.1.2‖)
        (fun n p _ =>
          (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), Φ n a' b' *
              Real.exp (-c * ((zdistInf d (sz.L n) (a' - STblk sz n p.1.1) : ℝ) +
                (zdistInf d (sz.L n) (b' - STblk sz n p.1.2) : ℝ)))) +
            Ψ n * Real.exp (-c * (zdistInf d (sz.L n) (STblk sz n p.1.1 - STblk sz n p.1.2) : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- The far field of `𝒦^{(2)}` for mixed charges: the `𝒦`-level hypothesis `emn2ExpHK` at the carrier `C` and the time `t`,
`ℓ* = (log W)^{3/2} ℓ_t`; neither `Θ` nor `m(σ)m(-σ) = 1` is used.  Band: `emn2Exp2_bandHK`; block Anderson: `baEMn2ExpHK`. -/
def STKfargL (t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ (x x' : Zd d (sz.L n)) (s : Bool),
    Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) (t n) ≤ (zdistInf d (sz.L n) (x - x') : ℝ) →
      ‖C.K n (t n) ![s, !s] ![x, x']‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ)))

/-- The entries of `M` across far blocks are small (band: `M` diagonal; block Anderson: `baSTMfarg_holds`). -/
def STMfarg (τ : ℕ → ℝ) : Prop :=
  ∀ c D : ℝ, 0 < c → 0 < D → ∀ᶠ n in atTop, ∀ x y : Idx d (sz.L n) (sz.W n),
    c * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (τ n) ≤
      ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) → ‖C.M n x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- Shift invariance, symmetry, (2.66) `prop:ThfadC`, (2.68) `prop:BD1` and (2.69) `prop:BD2` (`c = 1/2`) of the mixed-charge carrier
propagator. -/
def STThPropsg : Prop :=
  ∃ C₅ c₅ C₆ C₇ : ℝ, 0 < C₅ ∧ 0 < c₅ ∧ 0 < C₆ ∧ 0 < C₇ ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t → t < 1 →
    ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → let Θ := STThg C n (σ 0) (σ 1) t
      (∀ x y, Θ x y = Θ 0 (y - x)) ∧ (∀ x y, Θ x y = Θ y x) ∧
      (∀ a, ‖Θ 0 a‖ ≤ C₅ * Bparam d (sz.L n) (sz.lam n) t (zdistD d (sz.L n) a) *
        Real.exp (-c₅ * (zdistD d (sz.L n) a : ℝ) / ellT (sz.L n) (sz.lam n) t)) ∧
      (∀ a r, (zdistD d (sz.L n) r : ℝ) ≤ 1 / 2 * (zdistD d (sz.L n) a : ℝ) →
        ‖Θ 0 (a + r) - Θ 0 a‖ ≤ C₆ * (sz.lam n ^ 2 + |1 - t|)⁻¹ * (zdistD d (sz.L n) r : ℝ) * (((zdistD d (sz.L n) a : ℝ) + 1) ^ (d - 1))⁻¹) ∧
      (∀ a r, (zdistD d (sz.L n) r : ℝ) ≤ 1 / 2 * (zdistD d (sz.L n) a : ℝ) →
        ‖Θ 0 (a + r) + Θ 0 (a - r) - 2 * Θ 0 a‖ ≤ C₇ * (sz.lam n ^ 2 + |1 - t|)⁻¹ * (zdistD d (sz.L n) r : ℝ) ^ 2 * (((zdistD d (sz.L n) a : ℝ) + 1) ^ d)⁻¹)

/-- `𝒦^{(2)}` (mixed charges) is invariant under translations and the reflection, and `≤ c₁/A` at the time `s` (read by
`meanFar_B_tr`, `meanFar_B_sym`, `meanFar_n_K`; band: `KLK_two`, `W^{-d}Θ`; block Anderson: `BAKsolve`). -/
def STKpropsg (s : ℕ → ℝ) : Prop :=
  (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
    C.K n t σ (fun i => a i + c) = C.K n t σ a ∧ C.K n t σ (fun i => -a i) = C.K n t σ a) ∧
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a b : Zd d (sz.L n),
    ‖C.K n (s n) σ ![a, b]‖ ≤ c₁ / STAI sz n

/-- `H₀ n` is invariant under the lift to the fine lattice of the block translations and of the reflection. -/
def CltInvg : Prop :=
  ∀ (n : ℕ) (T : Zd d (sz.L n) ≃ Zd d (sz.L n)), (T = Equiv.neg _ ∨ ∃ c, T = Equiv.addRight c) →
    let lift := (splitEquiv d (sz.L n) (sz.W n)).trans ((Equiv.prodCongr T (Equiv.refl _)).trans (splitEquiv d (sz.L n) (sz.W n)).symm)
    ∀ x y, H₀ n (lift x) (lift y) = H₀ n x y

/-- **Hypothesis block** of the CLT statements at the time `s` (carrier `C`): `3 ≤ d`; `0 < κ ≤ Im m`, `0 < δ`, admissible sizes,
`0 ≤ s < t < 1`, `N^{-1+δ} ≤ 1 - t`, `κ ≤ 1`; `CltRepg`; the Ward row bound `Σ_y |M_xy|² ≤ 1`; `STMfarg`; `STLocalEntryUgL`, `STGdecayWgL`;
`STGijDecgL`; `STKfargL`. -/
def HCltOf (g' E : ℕ → ℝ) (κ δ 𝔠 𝔡 Cd : ℝ) (s t : ℕ → ℝ) : Prop :=
  3 ≤ d ∧ 0 < κ ∧ κ ≤ 1 ∧ 0 < δ ∧ sz.Admissible 𝔠 𝔡 ∧ (∀ n, κ ≤ (C.m n).im) ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n < t n) ∧
    (∀ n, t n < 1) ∧ (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 + δ) ≤ 1 - t n) ∧ CltRepg C μ H₀ g' E ∧
    (∀ n x, ∑ y, ‖C.M n x y‖ ^ 2 ≤ 1) ∧ STMfarg C s ∧ STLocalEntryUgL C μ s t ∧ STGdecayWgL C μ s t Cd ∧
    STGijDecgL C μ s ∧ STKfargL C s

/-- (5.36) `eq:bound_isolated` over the carrier, case (i): the generic form of `STCltIso` (`stCltIsogL_holds`). -/
def STCltIsogL (d : ℕ) : Prop :=
  ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STCltIsoConclgL C μ s

/-- Lemma 5.1 (`lem;CLT`) over the carrier, case (i): the generic form of `STCltFar`. -/
def STCltFargL (d : ℕ) : Prop :=
  ∀ (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ),
    HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STReg5I sz s t → STThPropsg C → STKpropsg C s → STExpInvgL C μ →
      STCltFarConclgL C μ s t

/-! ## The band case -/

/-- `CltRepg` at the band: `H₀ = 0`, `g' = sz.lam`. -/
theorem cltRepg_band (sz : Sizes d) (E : ℕ → ℝ) : CltRepg (bandFM sz E) (Sizes.seqP sz) (fun _ => 0) sz.lam E :=
  ⟨rfl, fun _ => Matrix.isHermitian_zero, fun n u ω => by
    have h : (0 + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam sz.lam) n u ω i j :
        Matrix _ _ ℂ) = Sizes.seqHflow sz n u ω := by ext i j; simp; rfl
    exact ⟨fun _ _ => by simp only [h]; rfl, fun _ _ _ => by simp only [h]; rfl⟩⟩

/-- At the band, `M = m(E) I` has row sum `Σ_y |M_xy|² = |m|² = 1` for `|E| ≤ 2`, and no entry across far blocks once `log W > 0`. -/
theorem bandFM_M_le (sz : Sizes d) (E : ℕ → ℝ) (hE : ∀ n, |E n| ≤ 2) (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) :
    ∑ y, ‖(bandFM sz E).M n x y‖ ^ 2 ≤ 1 := by
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [bandFM, Ne.symm hy]) (fun h => absurd (Finset.mem_univ x) h)]
  simp [bandFM, norm_mE (hE n)]

theorem bandFM_STMfarg (sz : Sizes d) (E : ℕ → ℝ) (hW : ∀ᶠ n in atTop, 0 < Real.log ((sz.W n : ℕ) : ℝ))
    (τ : ℕ → ℝ) : STMfarg (bandFM sz E) τ := by
  intro c D hc hD
  filter_upwards [hW] with n hWn x y hfar
  by_cases hxy : x = y
  · have h0 := mul_pos (mul_pos hc (pow_pos hWn 3)) (ellT_pos (L := sz.L n) (g := sz.lam n) (t := τ n)
      (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)))
    have h0' : zdistInf d (sz.L n) 0 = 0 := Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp [zdist])
    rw [hxy, sub_self, h0', Nat.cast_zero] at hfar
    linarith
  · simp [bandFM, hxy]; positivity

/-- The carrier propagator at `bandFM` is the band `Theta` (through `Step2Kern_Mss_band`). -/
theorem bandFM_STThg (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (σ σ' : Bool) (t : ℝ) :
    Step2Gen_Theta (Step2Kern_Mss (bandFM sz E) n σ σ' * (bandFM sz E).S n) (t : ℂ) =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ')) := by
  unfold Step2Gen_Theta Theta
  rw [Step2Kern_Mss_band, show (bandFM sz E).S n = SB d (sz.L n) (sz.lam n) from rfl, smul_mul_assoc, one_mul, smul_smul]

end RBM.BA
