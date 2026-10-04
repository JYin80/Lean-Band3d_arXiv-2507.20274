/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.StepDecompLoop
import RBM3D.Path.DriftAlgebra
import RBM3D.Path.LoopStep
import RBM3D.Path.Kernel
import RBM3D.Kernel.Evolution

/-!
# The one-step expansion of `A_k = (𝓛 - 𝒦)_{u_k,(+,-)}` along the walk (`d ≥ 3`)

Ticket T2098 (ST2-26).  Port of `RBM2D/Path/Expansion.lean` at commit `c9a24cf` (cited
`Expansion:<line>`; RBM2D ticket T2095).  Paper: arXiv:2507.20274, `LK_SDE` (`3_5`),
`def_Ustz`, `DefTHUST`.

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` becomes
`Zd d L`, `W^2 → W^d`, `(W L)^2 → (W L)^d = sz.size n`.  Merged vocabulary:
`gloop (blockMat H) z (pmLoop a b) - Kpm` is `sz.STLKM n E u H ![true, false] ![a, b]`
(`= loopFine … - STKloop`), `Kpm = W^{-d} Θ_u` is `STKloop` at `σ = (+,-)` (`kTwo`),
`ELKLK + EGt` are `STELKLKM + STEGtM`, `thetaGen` is `STthetaOp`, `spectralM` is `mE`.

* the pins `Avec`, `martInc`, `predInc`, `StoppedDuhamel105` and `stoppedDuhamel105`;
* the drift split `Dgrid`, `Rgrid`, `condExp_A_succ`;
* the expansion with the split `grid_expansion`, `grid_expansion_all`;
* the martingale part in decomposition form: `gridDelta`, `stepZ_eq_sum_gridDelta`,
  `stepZ_ukerMat_eq_Uker`, `stepXi_eq_sum_gridDelta_ae`, `stepY_eq_sum_gridDelta_ae`,
  `stepY_ukerMat_eq_Uker_ae`, `Zvec`, `Yvec`, `grid_expansion'`, `grid_expansion_all'`.

The helpers of RBM2D `Path/UBounds` (`uopOneStep`, `ukerNonneg`, `normSqSpectralMOne`) are re-proved
here as `private` `Expansion_` helpers (T2097 = ST2-25 is not merged).  Every other helper is
`private` or carries the prefix `Expansion_`.
-/

noncomputable section

namespace RBM.Path

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Loop
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

variable {d : ℕ} (sz : Sizes d)

/-! ### 1. The four pins (`Expansion:45-80`) -/

/-- `A_k = (𝓛 - 𝒦)_{u_k,(+,-)}` along the walk, as a two-index tensor (`Expansion:48`). -/
def Avec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    Zd d (sz.L n) × Zd d (sz.L n) → ℂ :=
  fun a => sz.STLKM n E (gridTime s t K n k) (pathH sz s t K n k ω) ![true, false] ![a.1, a.2]

/-- The martingale difference `ξ_{j+1} = A_{j+1} - E[A_{j+1} | F_j]` (label-wise;
`Expansion:55`). -/
def martInc (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz) :
    Zd d (sz.L n) × Zd d (sz.L n) → ℂ :=
  fun a => Avec sz E s t K n (j + 1) ω a -
    (pathP sz)[fun ω' => Avec sz E s t K n (j + 1) ω' a | filt sz j] ω

/-- The predictable part `E[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1}} A_j` (`Expansion:61`). -/
def predInc (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz) :
    Zd d (sz.L n) × Zd d (sz.L n) → ℂ :=
  fun a => (pathP sz)[fun ω' => Avec sz E s t K n (j + 1) ω' a | filt sz j] ω -
    Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n j)
      (gridTime s t K n (j + 1)) (Avec sz E s t K n j ω) a

/-- **Pin (105), grid form** (`int_K-L_ST`; `Expansion:71`): for every stopping index `τ` and
target `k`, `A_{k∧τ} = 𝒰_{u_0,u_{k∧τ}} A_0 + Σ_{j<k∧τ} 𝒰_{u_{j+1},u_{k∧τ}} (P_j + ξ_{j+1})`. -/
def StoppedDuhamel105 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  |E| < 2 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n : ℕ) (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz), min k (τ ω) ≤ K n →
      Avec sz E s t K n (min k (τ ω)) ω =
        Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω) +
          ∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
              (gridTime s t K n (j + 1)) (gridTime s t K n (min k (τ ω)))
              (predInc sz E s t K n j ω + martInc sz E s t K n j ω)

/-! ### 2. Grid-time arithmetic (`Expansion:83-118`) -/

section GridArith

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

private theorem Expansion_gridStep_nonneg (hst : s n ≤ t n) : 0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem Expansion_gridTime_succ (k : ℕ) :
    gridTime s t K n (k + 1) = gridTime s t K n k + gridStep s t K n := by
  unfold gridTime; push_cast; ring

private theorem Expansion_gridTime_zero : gridTime s t K n 0 = s n := by
  simp [gridTime]

private theorem Expansion_gridTime_mono (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

private theorem Expansion_gridTime_nonneg (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) :
    0 ≤ gridTime s t K n j := by
  have h := Expansion_gridTime_mono s t K n hst (Nat.zero_le j)
  rw [Expansion_gridTime_zero] at h
  linarith

private theorem Expansion_gridTime_lt_one (hst : s n ≤ t n) (hK : K n ≠ 0) (ht1 : t n < 1)
    {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have h := Expansion_gridTime_mono s t K n hst hj
  rw [gridTime_last s t K n hK] at h
  linarith

end GridArith

/-! ### 3. The stopped Duhamel formula (105) in grid form (`Expansion:120-141`) -/

/-- `|m|² = 1` for `|E| ≤ 2` (RBM2D `normSqSpectralMOne`, `UBounds:416`; from `norm_mE`). -/
private theorem Expansion_normSq_mE {E : ℝ} (hE : |E| ≤ 2) : Complex.normSq (mE E) = 1 := by
  rw [Complex.normSq_eq_norm_sq, norm_mE hE]
  norm_num

/-- **The stopped Duhamel formula at one size index** (hypotheses only at `n`, DECISIONS §29 (4)),
from `Uop_duhamel_telescope_stopped` at `ξ = |m|² = 1`: `A_{j+1} - 𝒰 A_j = predInc_j + martInc_j`
label by label (the conditional expectation cancels). -/
theorem stoppedDuhamel105_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz) (hkτ : min k (τ ω) ≤ K n) :
    Avec sz E s t K n (min k (τ ω)) ω =
      Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
          (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω) +
        ∑ j ∈ Finset.range (min k (τ ω)),
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
            (gridTime s t K n (j + 1)) (gridTime s t K n (min k (τ ω)))
            (predInc sz E s t K n j ω + martInc sz E s t K n j ω) := by
  have hξ : ‖((Complex.normSq (mE E) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Expansion_normSq_mE hE.le]; simp
  have hu0 : ∀ j ≤ min k (τ ω), 0 ≤ gridTime s t K n j :=
    fun j _ => Expansion_gridTime_nonneg s t K n hs0 hst j
  have hu1 : ∀ j ≤ min k (τ ω), gridTime s t K n j < 1 :=
    fun j hj => Expansion_gridTime_lt_one s t K n hst hK ht1 (hj.trans hkτ)
  have h := Uop_duhamel_telescope_stopped d (sz.L n) (sz.lam n) (sz.three_le_L n) hξ
    (Ω' := PathΩ sz) (gridTime s t K n) τ ω k hu0 hu1 (fun j => Avec sz E s t K n j ω)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext a
  simp only [predInc, martInc, Pi.add_apply, Pi.sub_apply]
  ring

/-- The pin `StoppedDuhamel105` holds (`Expansion:124`). -/
theorem stoppedDuhamel105 (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedDuhamel105 sz E s t K :=
  fun hE hs0 hst ht1 hK n τ k ω hkτ =>
    stoppedDuhamel105_at sz E s t K n hE (hs0 n) (hst n) (ht1 n) (hK n) τ k ω hkτ

/-! ### 4. Integrability of a Hermitian-test observable along the walk (`Expansion:143-203`) -/

section Integrable

open scoped Matrix.Norms.L2Operator

private def Expansion_herm {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (1 / 2 : ℝ) • (A + Aᴴ)

private theorem Expansion_herm_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : (Expansion_herm A).IsHermitian :=
  (isHermitian_add_transpose_self A).smul (star_trivial (1 / 2 : ℝ))

private theorem Expansion_herm_of_isHermitian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) : Expansion_herm A = A := by
  unfold Expansion_herm
  rw [hA.eq, ← two_smul ℝ A, smul_smul]
  norm_num

private theorem Expansion_continuous_herm {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Continuous (Expansion_herm : Matrix ι ι ℂ → _) := by
  unfold Expansion_herm
  have h1 : Continuous fun A : Matrix ι ι ℂ => Aᴴ := continuous_id.matrix_conjTranspose
  exact Continuous.const_smul (continuous_id.add h1) (1 / 2 : ℝ)

/-- `Ψ ∘ herm` is continuous when `Ψ` is `C²` at every Hermitian point. -/
private theorem Expansion_continuous_comp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ψ : Matrix ι ι ℂ → ℂ} (h : ∀ M, M.IsHermitian → ContDiffAt ℝ 2 Ψ M) :
    Continuous (fun M : Matrix ι ι ℂ => Ψ (Expansion_herm M)) :=
  continuous_iff_continuousAt.2 fun M =>
    ((h _ (Expansion_herm_isHermitian M)).continuousAt).comp
      Expansion_continuous_herm.continuousAt

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `Ψ` along the walk is measurable. -/
private theorem Expansion_measurable_phi
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Measurable fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω) := by
  have heq : (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω))
      = fun ω => Ψ (Expansion_herm (pathH sz s t K n k ω)) := funext fun ω => by
    rw [Expansion_herm_of_isHermitian (pathH_isHermitian sz s t K n k ω)]
  rw [heq]
  exact (Expansion_continuous_comp hΨ.contDiffAt).measurable.comp
    ((pathH_measurable_filt sz s t K n k).mono ((filt sz).le k) le_rfl)

/-- `Ψ` along the walk is integrable: measurable and bounded by (H2). -/
private theorem Expansion_integrable_phi
    {Ψ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΨ : HermTestFun sz n Ψ) (k : ℕ) :
    Integrable (fun ω : PathΩ sz => Ψ (pathH sz s t K n k ω)) (pathP sz) := by
  obtain ⟨C, hC⟩ := hΨ.bdd₀
  exact (memLp_top_of_bound (Expansion_measurable_phi sz s t K n hΨ k).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => hC _ (pathH_isHermitian sz s t K n k ω))).integrable
    le_top

end Integrable

/-! ### 5. The second-order step of `𝒦` (`Expansion:205-305`; new proof from the resolvent
identity, counterpart of RBM1D `K_step`, `Gauss/GridDriftAlgebra.lean:159`) -/

section KpmStep

open scoped Matrix.Norms.Operator

private theorem Expansion_mSigma_mul {E : ℝ} (hE : |E| ≤ 2) :
    mSigma E true * mSigma E false = 1 := by
  simp only [mSigma, ite_true, Bool.false_eq_true, ite_false]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]
  simp

/-- `Kpm = STKloop` at `σ = (+,-)` is `W^{-d} Θ_u` (`Expansion:212`, `Expansion_Kpm_eq`; `d = 2`:
`W^{-2}`; here `kTwo = (W^d)⁻¹ (m m) Θ_{t (m m)}`, `Loop/Primitive.lean:46`, `m(+) m(-) = 1`). -/
private theorem Expansion_STKloop_eq (n : ℕ) {E : ℝ} (hE : |E| < 2) (v : ℝ)
    (x y : Zd d (sz.L n)) :
    sz.STKloop n E v ![true, false] ![x, y]
      = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * Theta d (sz.L n) (sz.lam n) (v : ℂ) x y := by
  have hI : KLloopOf d (sz.L n) ![true, false] ![x, y] = ⟨[true, false], [x, y]⟩ := by
    simp [KLloopOf]
  unfold Sizes.STKloop
  rw [hI, KLK_two_eq_kTwo d (sz.L n) (sz.lam n) (sz.W n) E v true false x y, kTwo,
    Expansion_mSigma_mul hE.le, mul_one, mul_one]

private theorem Expansion_norm_Theta_real {L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) {v : ℝ}
    (h0 : 0 ≤ v) (h1 : v < 1) : ‖Theta d L g (v : ℂ)‖ ≤ (1 - v)⁻¹ := by
  have h := norm_Theta_le (d := d) (g := g) hL h0 h1 (m := 1) norm_one
  simpa using h

private theorem Expansion_norm_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ)
    (x y : ι) : ‖M x y‖ ≤ ‖M‖ :=
  le_trans (Finset.single_le_sum (f := fun j => ‖M x j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ y)) (sum_norm_row_le M x)

private theorem Expansion_norm_ofReal_lt_one {v : ℝ} (h0 : 0 ≤ v) (h1 : v < 1) :
    ‖(v : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1

private theorem Expansion_norm_mul5 {R : Type*} [NormedRing R] (a b c d e : R) :
    ‖a * b * c * d * e‖ ≤ ‖a‖ * ‖b‖ * ‖c‖ * ‖d‖ * ‖e‖ := by
  have h1 := norm_mul_le (a * b * c * d) e
  have h2 := norm_mul_le (a * b * c) d
  have h3 := norm_mul_le (a * b) c
  have h4 := norm_mul_le a b
  calc ‖a * b * c * d * e‖ ≤ ‖a * b * c * d‖ * ‖e‖ := h1
    _ ≤ (‖a * b * c‖ * ‖d‖) * ‖e‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ ((‖a * b‖ * ‖c‖) * ‖d‖) * ‖e‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
          (norm_nonneg _)
    _ ≤ (((‖a‖ * ‖b‖) * ‖c‖) * ‖d‖) * ‖e‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)

/-- `‖c Θ_{u'} - c Θ_u - Δ ∂_u (c Θ_u)‖ ≤ ‖c‖ (1-u')⁻¹ (1-u)⁻² Δ²` entrywise (`u' = u + Δ`): twice
the resolvent identity `Θ_{u'} - Θ_u = Δ Θ_{u'} S Θ_u`, then `‖Θ‖ ≤ (1-u)⁻¹`, `‖S‖ = 1`
(`Expansion:244`, `Expansion_Kpm_step`, with the constant `W^{-2}` replaced by a general `c`, here
`W^{-d}`). -/
private theorem Expansion_K_step {L : ℕ} [NeZero L] {g : ℝ} (hL : 3 ≤ L) (c : ℂ)
    {u u' Δ : ℝ} (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hu' : u' = u + Δ) (hu1 : u' < 1)
    (a b : Zd d L) :
    ‖c * Theta d L g (u' : ℂ) a b - c * Theta d L g (u : ℂ) a b
        - (Δ : ℂ) * deriv (fun v : ℝ => c * Theta d L g (v : ℂ) a b) u‖
      ≤ ‖c‖ * (1 - u')⁻¹ * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by
  have hu0' : 0 ≤ u' := by rw [hu']; linarith
  have hu1' : u < 1 := by linarith
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  have hnu : ‖(u : ℂ)‖ < 1 := Expansion_norm_ofReal_lt_one hu0 hu1'
  have hnu' : ‖(u' : ℂ)‖ < 1 := Expansion_norm_ofReal_lt_one hu0' hu1
  have hderiv : deriv (fun v : ℝ => c * Theta d L g (v : ℂ) a b) u
      = c * (Theta d L g (u : ℂ) * SB d L g * Theta d L g (u : ℂ)) a b :=
    (((hasDerivAt_Theta_apply d L g hS hnu a b).comp_ofReal).const_mul c).deriv
  set T := Theta d L g (u : ℂ) with hT
  set T' := Theta d L g (u' : ℂ) with hT'
  set e : ℂ := (Δ : ℂ) with he
  have hcu : (u' : ℂ) - (u : ℂ) = e := by rw [hu']; push_cast; ring
  have h1 : T' - T = e • (T' * SB d L g * T) := by
    have h := Theta_sub_Theta d L g hS hnu hnu'
    rw [hcu] at h
    exact h
  have h3 : T' - T - e • (T * SB d L g * T) = e • (e • (T' * SB d L g * T * SB d L g * T)) := by
    have e1 : T' * SB d L g * T - T * SB d L g * T
        = e • (T' * SB d L g * T * SB d L g * T) := by
      rw [← sub_mul, ← sub_mul, h1, smul_mul_assoc, smul_mul_assoc]
    rw [h1, ← smul_sub, e1]
  have hentry : c * T' a b - c * T a b - e * deriv (fun v : ℝ => c * Theta d L g (v : ℂ) a b) u
      = c * (e * (e * (T' * SB d L g * T * SB d L g * T) a b)) := by
    have h := congrFun (congrFun h3 a) b
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    rw [hderiv]
    linear_combination c * h
  have hM : ‖T' * SB d L g * T * SB d L g * T‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ := by
    have e1 : ‖T'‖ ≤ (1 - u')⁻¹ := Expansion_norm_Theta_real hL hu0' hu1
    have e2 : ‖T‖ ≤ (1 - u)⁻¹ := Expansion_norm_Theta_real hL hu0 hu1'
    have p1 : 0 < (1 - u')⁻¹ := inv_pos.2 (by linarith)
    have p2 : 0 < (1 - u)⁻¹ := inv_pos.2 (by linarith)
    have e4 := Expansion_norm_mul5 T' (SB d L g) T (SB d L g) T
    rw [hS] at e4
    calc ‖T' * SB d L g * T * SB d L g * T‖ ≤ ‖T'‖ * 1 * ‖T‖ * 1 * ‖T‖ := e4
      _ = ‖T'‖ * (‖T‖ * ‖T‖) := by ring
      _ ≤ (1 - u')⁻¹ * ((1 - u)⁻¹ * (1 - u)⁻¹) :=
          mul_le_mul e1 (mul_le_mul e2 e2 (norm_nonneg _) p2.le)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) p1.le
      _ = (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ := by ring
  rw [hentry, norm_mul, norm_mul, norm_mul]
  have hcn : ‖e‖ = Δ := by rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
  rw [hcn]
  have hc0 : 0 ≤ ‖c‖ := norm_nonneg _
  have hent : ‖(T' * SB d L g * T * SB d L g * T) a b‖ ≤ (1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹ :=
    (Expansion_norm_entry_le (T' * SB d L g * T * SB d L g * T) a b).trans hM
  calc ‖c‖ * (Δ * (Δ * ‖(T' * SB d L g * T * SB d L g * T) a b‖))
      ≤ ‖c‖ * (Δ * (Δ * ((1 - u')⁻¹ * (1 - u)⁻¹ * (1 - u)⁻¹))) := by gcongr
    _ = ‖c‖ * (1 - u')⁻¹ * ((1 - u)⁻¹) ^ 2 * Δ ^ 2 := by ring

end KpmStep

/-! ### 6. The `𝒰` helpers of RBM2D `Path/UBounds` (re-proved, private): the sign of the kernel
and one step of `𝒰` (`UBounds:424`, `:553`; RBM1D `Uker_step`, `Gauss/GridDriftAlgebra.lean:325`) -/

section UBounds

open scoped Matrix.Norms.Operator

variable {L : ℕ} [NeZero L] {g : ℝ}

/-- The per-slot generator `ξ S^{(B)} Θ^{(B)}_{uξ}` of `𝒰` (`UBounds:52`, `thetaGenMat`). -/
private def Expansion_thetaGenMat (L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  ξ • (SB d L g * Theta d L g ((u : ℂ) * ξ))

/-- `Θ_{u,(+,-)} ∘ A`, acting on the left in each slot (`UBounds:56`, `thetaGen`). -/
private def Expansion_thetaGen (L : ℕ) [NeZero L] (g : ℝ) (ξ : ℂ) (u : ℝ)
    (A : Zd d L × Zd d L → ℂ) : Zd d L × Zd d L → ℂ :=
  fun a => ∑ b : Zd d L,
    (Expansion_thetaGenMat (d := d) L g ξ u a.1 b * A (b, a.2)
      + Expansion_thetaGenMat (d := d) L g ξ u a.2 b * A (a.1, b))

/-- `z` is a nonnegative real number, viewed inside `ℂ` (the method of RBM2D `RealNonneg`,
`UBounds:105`). -/
private def Expansion_RealNonneg (z : ℂ) : Prop := ∃ r : ℝ, 0 ≤ r ∧ z = (r : ℂ)

private theorem Expansion_RN_zero : Expansion_RealNonneg 0 := ⟨0, le_refl _, by simp⟩

private theorem Expansion_RN_one : Expansion_RealNonneg 1 := ⟨1, zero_le_one, by simp⟩

private theorem Expansion_RN_add {z w : ℂ} (hz : Expansion_RealNonneg z)
    (hw : Expansion_RealNonneg w) : Expansion_RealNonneg (z + w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 + r2, by positivity, by rw [e1, e2]; push_cast; ring⟩

private theorem Expansion_RN_mul {z w : ℂ} (hz : Expansion_RealNonneg z)
    (hw : Expansion_RealNonneg w) : Expansion_RealNonneg (z * w) := by
  obtain ⟨r1, hr1, e1⟩ := hz
  obtain ⟨r2, hr2, e2⟩ := hw
  exact ⟨r1 * r2, mul_nonneg hr1 hr2, by rw [e1, e2]; push_cast; ring⟩

private theorem Expansion_RN_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, Expansion_RealNonneg (f i)) : Expansion_RealNonneg (∑ i ∈ s, f i) :=
  Finset.sum_induction f Expansion_RealNonneg (fun _ _ ha hb => Expansion_RN_add ha hb)
    Expansion_RN_zero h

private theorem Expansion_SB_RN (a b : Zd d L) : Expansion_RealNonneg (SB d L g a b) := by
  rw [SB_apply, sbKernel_eq_ofReal]
  exact ⟨_, sbKernelR_nonneg d L g _, rfl⟩

private theorem Expansion_Theta_RN (hL : 3 ≤ L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (a b : Zd d L) : Expansion_RealNonneg (Theta d L g (t : ℂ) a b) :=
  ⟨(Theta d L g (t : ℂ) a b).re, Theta_real_nonneg hL ht0 ht1 a b,
    Theta_real_eq hL ht0 ht1 a b⟩

/-- The exact form `𝒰`-kernel `= 1 + (w - v) · (ξ S Θ_{wξ})`, from `(1 - wξS) Θ_{wξ} = 1`
(`UBounds:238`, `ukerMat_eq`). -/
private theorem Expansion_ukerMat_eq (hL : 3 ≤ L) {ξ : ℂ} {v w : ℝ}
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v w = 1 + ((w : ℂ) - (v : ℂ)) • Expansion_thetaGenMat (d := d) L g ξ w := by
  have h := mul_Theta_of_three_le (d := d) (L := L) (g := g) hL hw
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  unfold ukerMat Expansion_thetaGenMat
  rw [sub_mul, one_mul, smul_mul_assoc, smul_smul, ← h]
  module

/-- **Sign of the kernel** (`UBounds:424`, `ukerNonneg`): for real `ξ ≥ 0`, `0 ≤ v ≤ w`,
`wξ < 1`, `ukerMat` is entrywise a nonnegative real. -/
private theorem Expansion_ukerNonneg (hL : 3 ≤ L) {ξ v w : ℝ} (hξ : 0 ≤ ξ) (hv : 0 ≤ v)
    (hvw : v ≤ w) (hwξ : w * ξ < 1) (a b : Zd d L) :
    (ukerMat d L g (ξ : ℂ) v w a b).im = 0 ∧ 0 ≤ (ukerMat d L g (ξ : ℂ) v w a b).re := by
  have hw0 : 0 ≤ w := hv.trans hvw
  have hwξ0 : 0 ≤ w * ξ := mul_nonneg hw0 hξ
  have hnorm : ‖(w : ℂ) * (ξ : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_of_nonneg hwξ0]; exact hwξ
  have hz : ((w : ℂ) * (ξ : ℂ)) = ((w * ξ : ℝ) : ℂ) := by push_cast; ring
  have h1 : Expansion_RealNonneg ((1 : Matrix (Zd d L) (Zd d L) ℂ) a b) := by
    rw [Matrix.one_apply]
    split_ifs
    · exact Expansion_RN_one
    · exact Expansion_RN_zero
  have hc : Expansion_RealNonneg ((w : ℂ) - (v : ℂ)) :=
    ⟨w - v, by linarith, by push_cast; ring⟩
  have hξc : Expansion_RealNonneg (ξ : ℂ) := ⟨ξ, hξ, rfl⟩
  have hgen : Expansion_RealNonneg ((Expansion_thetaGenMat (d := d) L g (ξ : ℂ) w) a b) := by
    unfold Expansion_thetaGenMat
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
    refine Expansion_RN_mul hξc (Expansion_RN_sum _ _ fun c _ => ?_)
    rw [hz]
    exact Expansion_RN_mul (Expansion_SB_RN a c) (Expansion_Theta_RN hL hwξ0 hwξ c b)
  rw [Expansion_ukerMat_eq hL hnorm]
  have hres := Expansion_RN_add h1 (Expansion_RN_mul hc hgen)
  obtain ⟨r, hr, hreq⟩ := hres
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at hreq ⊢
  rw [hreq]
  simpa using hr

/-- A matrix with row `ℓ¹` norms `≤ R` maps a max-norm bounded vector to a max-norm bounded one
(`UBounds:376`). -/
private theorem Expansion_norm_sum_mul_le {B : Matrix (Zd d L) (Zd d L) ℂ} {R α : ℝ}
    (hB : ∀ x : Zd d L, ∑ c : Zd d L, ‖B x c‖ ≤ R) (x : Zd d L) {f : Zd d L → ℂ}
    (hf : ∀ b, ‖f b‖ ≤ α) : ‖∑ b : Zd d L, B x b * f b‖ ≤ R * α := by
  have hα : 0 ≤ α := (norm_nonneg _).trans (hf x)
  calc ‖∑ b : Zd d L, B x b * f b‖ ≤ ∑ b : Zd d L, ‖B x b * f b‖ := norm_sum_le _ _
    _ = ∑ b : Zd d L, ‖B x b‖ * ‖f b‖ := by simp only [norm_mul]
    _ ≤ ∑ b : Zd d L, ‖B x b‖ * α :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) (norm_nonneg _)
    _ = (∑ b : Zd d L, ‖B x b‖) * α := (Finset.sum_mul _ _ _).symm
    _ ≤ R * α := mul_le_mul_of_nonneg_right (hB x) hα

/-- The two-slot sum over `Zd d L × Zd d L` as an iterated sum (`UBounds:390`). -/
private theorem Expansion_sum_prod_eq_iter (P Q : Matrix (Zd d L) (Zd d L) ℂ)
    (A : Zd d L × Zd d L → ℂ) (a : Zd d L × Zd d L) :
    ∑ b : Zd d L × Zd d L, P a.1 b.1 * Q a.2 b.2 * A b =
      ∑ b₁ : Zd d L, P a.1 b₁ * ∑ b₂ : Zd d L, Q a.2 b₂ * A (b₁, b₂) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b₂ _ => by ring

/-- Row `ℓ¹` bound for the generator `ξ S Θ_{sξ}`, `‖ξ‖ = 1` (`UBounds:309`,
`sum_norm_thetaGenMat_row_le`; RBM1D `row_bound_edge`, `Gauss/GridDriftAlgebra.lean:310`). -/
private theorem Expansion_row_thetaGenMat (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖Expansion_thetaGenMat (d := d) L g ξ s x c‖ ≤ (1 - s)⁻¹ := by
  have hentry : ∀ c : Zd d L, ‖Expansion_thetaGenMat (d := d) L g ξ s x c‖ =
      ‖(SB d L g * Theta d L g ((s : ℂ) * ξ)) x c‖ := fun c => by
    simp only [Expansion_thetaGenMat, Matrix.smul_apply, smul_eq_mul, norm_mul, hξ, one_mul]
  simp_rw [hentry]
  refine (sum_norm_row_le _ x).trans ?_
  calc ‖SB d L g * Theta d L g ((s : ℂ) * ξ)‖
      ≤ ‖SB d L g‖ * ‖Theta d L g ((s : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta d L g ((s : ℂ) * ξ)‖ := by rw [norm_SB d L g hL, one_mul]
    _ ≤ (1 - s)⁻¹ := norm_Theta_le (d := d) (g := g) hL hs0 hs1 hξ

/-- Row `ℓ¹` bound for the difference of generators at times `u + Δ` and `u`: by the resolvent
identity, `ξ S Θ_{(u+Δ)ξ} - ξ S Θ_{uξ} = Δ ξ² S Θ_{(u+Δ)ξ} S Θ_{uξ}` (`UBounds:322`). -/
private theorem Expansion_row_thetaGenMat_diff (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ}
    (hu0 : 0 ≤ u) (hΔ : 0 ≤ Δ) (hd : u + Δ < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖(Expansion_thetaGenMat (d := d) L g ξ (u + Δ)
        - Expansion_thetaGenMat (d := d) L g ξ u) x c‖
      ≤ Δ * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹) := by
  have hu1 : u < 1 := by linarith
  have hS : ‖SB d L g‖ = 1 := norm_SB d L g hL
  have hu : ‖(u : ℂ) * ξ‖ < 1 := norm_t_mul_lt_one hu0 hu1 hξ
  have hd' : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := norm_t_mul_lt_one (by linarith) hd hξ
  have hTsub := Theta_sub_Theta d L g hS (ξ := (u : ℂ) * ξ) (ζ := ((u + Δ : ℝ) : ℂ) * ξ) hu hd'
  have hcast : ((u + Δ : ℝ) : ℂ) * ξ - (u : ℂ) * ξ = ((Δ : ℝ) : ℂ) * ξ := by
    push_cast; ring
  rw [hcast] at hTsub
  have hM : Expansion_thetaGenMat (d := d) L g ξ (u + Δ) - Expansion_thetaGenMat (d := d) L g ξ u =
      (((Δ : ℝ) : ℂ) * ξ ^ 2) •
        (SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g
          * Theta d L g ((u : ℂ) * ξ))) := by
    unfold Expansion_thetaGenMat
    rw [← smul_sub, ← Matrix.mul_sub, hTsub, Matrix.mul_smul, smul_smul]
    congr 1
    ring
  have hnormeq : ∀ c : Zd d L, ‖(Expansion_thetaGenMat (d := d) L g ξ (u + Δ)
        - Expansion_thetaGenMat (d := d) L g ξ u) x c‖ =
      Δ * ‖(SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g *
        Theta d L g ((u : ℂ) * ξ))) x c‖ := by
    intro c
    rw [hM, Matrix.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hΔ, norm_pow, hξ]
    ring
  simp_rw [hnormeq]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_norm_row_le _ x).trans ?_) hΔ
  calc ‖SB d L g * (Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ))‖
      ≤ ‖SB d L g‖ * ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g
          * Theta d L g ((u : ℂ) * ξ)‖ := norm_mul_le _ _
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g * Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [hS, one_mul]
    _ ≤ ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ) * SB d L g‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        norm_mul_le _ _
    _ ≤ (‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖SB d L g‖) * ‖Theta d L g ((u : ℂ) * ξ)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = ‖Theta d L g (((u + Δ : ℝ) : ℂ) * ξ)‖ * ‖Theta d L g ((u : ℂ) * ξ)‖ := by
        rw [hS, mul_one]
    _ ≤ (1 - (u + Δ))⁻¹ * (1 - u)⁻¹ :=
        mul_le_mul (norm_Theta_le (d := d) (g := g) hL (by linarith) hd hξ)
          (norm_Theta_le (d := d) (g := g) hL hu0 hu1 hξ) (norm_nonneg _)
          (inv_nonneg.mpr (by linarith))

/-- **One step of `𝒰`** (`UBounds:553`, `uopOneStep`; port of RBM1D `Uker_step`,
`Gauss/GridDriftAlgebra.lean:325`, at `n = 2` with the same kernel in both slots), `‖ξ‖ = 1`:
`‖𝒰_{u,u+Δ}A - A - Δ Θ_u A‖_max ≤ 3 Δ² (1-u-Δ)^{-2} ‖A‖_max`. -/
private theorem Expansion_uopOneStep (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ = 1) {u Δ : ℝ}
    (hu : 0 ≤ u) (hΔ : 0 ≤ Δ) (huΔ : u + Δ < 1) (A : Zd d L × Zd d L → ℂ) (α : ℝ)
    (hA : ∀ b, ‖A b‖ ≤ α) (a : Zd d L × Zd d L) :
    ‖Uop d L g ξ u (u + Δ) A a - A a - (Δ : ℂ) * Expansion_thetaGen (d := d) L g ξ u A a‖ ≤
      3 * Δ ^ 2 * ((1 - (u + Δ))⁻¹) ^ 2 * α := by
  have hu1 : u < 1 := by linarith
  have hd' : ‖((u + Δ : ℝ) : ℂ) * ξ‖ < 1 := norm_t_mul_lt_one (by linarith) huΔ hξ
  set G' : Matrix (Zd d L) (Zd d L) ℂ := Expansion_thetaGenMat (d := d) L g ξ (u + Δ) with hG'
  set G : Matrix (Zd d L) (Zd d L) ℂ := Expansion_thetaGenMat (d := d) L g ξ u with hG
  have hK : ∀ x y : Zd d L, ukerMat d L g ξ u (u + Δ) x y =
      (1 : Matrix (Zd d L) (Zd d L) ℂ) x y + (Δ : ℂ) * G' x y := by
    intro x y
    rw [Expansion_ukerMat_eq hL hd']
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    congr 2
    push_cast; ring
  have hin : ∀ b₁ : Zd d L, ∑ b₂ : Zd d L, ukerMat d L g ξ u (u + Δ) a.2 b₂ * A (b₁, b₂) =
      A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    intro b₁
    simp only [hK, add_mul, Finset.sum_add_distrib, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]
  have hexp : Uop d L g ξ u (u + Δ) A a = A a
      + (Δ : ℂ) * (∑ b : Zd d L, G' a.1 b * A (b, a.2) + ∑ b : Zd d L, G' a.2 b * A (a.1, b))
      + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    change ∑ b : Zd d L × Zd d L, ukerMat d L g ξ u (u + Δ) a.1 b.1
        * ukerMat d L g ξ u (u + Δ) a.2 b.2 * A b = _
    rw [Expansion_sum_prod_eq_iter (ukerMat d L g ξ u (u + Δ)) (ukerMat d L g ξ u (u + Δ)) A a]
    simp only [hin]
    have hterm : ∀ b₁ : Zd d L, ukerMat d L g ξ u (u + Δ) a.1 b₁ *
        (A (b₁, a.2) + (Δ : ℂ) * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)) =
        (1 : Matrix (Zd d L) (Zd d L) ℂ) a.1 b₁ * A (b₁, a.2)
        + (Δ : ℂ) * ((1 : Matrix (Zd d L) (Zd d L) ℂ) a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂))
        + (Δ : ℂ) * (G' a.1 b₁ * A (b₁, a.2))
        + (Δ : ℂ) ^ 2 * (G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)) := by
      intro b₁
      rw [hK]; ring
    simp only [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hgen : Expansion_thetaGen (d := d) L g ξ u A a =
      ∑ b : Zd d L, G a.1 b * A (b, a.2) + ∑ b : Zd d L, G a.2 b * A (a.1, b) := by
    unfold Expansion_thetaGen
    rw [Finset.sum_add_distrib]
  have hdiff : Uop d L g ξ u (u + Δ) A a - A a - (Δ : ℂ) * Expansion_thetaGen (d := d) L g ξ u A a =
      (Δ : ℂ) * (∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂) := by
    rw [hexp, hgen]
    simp only [Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have hβ : 0 < 1 - (u + Δ) := by linarith
  set β : ℝ := (1 - (u + Δ))⁻¹ with hβdef
  have hβ0 : 0 ≤ β := inv_nonneg.mpr hβ.le
  have hR1 : ∀ x : Zd d L, ∑ c : Zd d L, ‖G' x c‖ ≤ β := fun x =>
    Expansion_row_thetaGenMat hL hξ (by linarith) huΔ x
  have hR2 : ∀ x : Zd d L, ∑ c : Zd d L, ‖(G' - G) x c‖ ≤ Δ * β ^ 2 := by
    intro x
    refine (Expansion_row_thetaGenMat_diff hL hξ hu hΔ huΔ x).trans ?_
    have h2 : (1 - u)⁻¹ ≤ β := inv_anti₀ hβ (by linarith)
    calc Δ * ((1 - (u + Δ))⁻¹ * (1 - u)⁻¹) ≤ Δ * (β * β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul le_rfl h2 (inv_nonneg.mpr (by linarith)) hβ0) hΔ
      _ = Δ * β ^ 2 := by ring
  have hDA : ‖∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)‖ ≤ Δ * β ^ 2 * α :=
    Expansion_norm_sum_mul_le hR2 a.1 (fun b => hA (b, a.2))
  have hDB : ‖∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b)‖ ≤ Δ * β ^ 2 * α :=
    Expansion_norm_sum_mul_le hR2 a.2 (fun b => hA (a.1, b))
  have hS3 : ‖∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)‖ ≤ β * (β * α) :=
    Expansion_norm_sum_mul_le hR1 a.1
      (fun b₁ => Expansion_norm_sum_mul_le hR1 a.2 (fun b₂ => hA (b₁, b₂)))
  rw [hdiff]
  have hnΔ : ‖(Δ : ℂ)‖ = Δ := by rw [Complex.norm_real, Real.norm_of_nonneg hΔ]
  calc ‖(Δ : ℂ) * (∑ b : Zd d L, (G' - G) a.1 b * A (b, a.2)
          + ∑ b : Zd d L, (G' - G) a.2 b * A (a.1, b))
        + (Δ : ℂ) ^ 2 * ∑ b₁ : Zd d L, G' a.1 b₁ * ∑ b₂ : Zd d L, G' a.2 b₂ * A (b₁, b₂)‖
      ≤ Δ * (Δ * β ^ 2 * α + Δ * β ^ 2 * α) + Δ ^ 2 * (β * (β * α)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, hnΔ]
          exact mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add hDA hDB)) hΔ
        · rw [norm_mul, norm_pow, hnΔ]
          exact mul_le_mul_of_nonneg_left hS3 (by positivity)
    _ = 3 * Δ ^ 2 * β ^ 2 * α := by ring

end UBounds

/-! ### 7. The drift split: `Dgrid`, `Rgrid` (`Expansion:307-331`) -/

/-- **`D_j`**: the drift `𝓔^{(LK×LK)} + 𝓔^{(G̃)}` at the grid time `u_j` and the walk `H_j`, as a
function of the label `a = (a₁, a₂)` (RBM1D `Dgrid`, `Gauss/GridExpansion.lean:271`, commit
`86573b9`; `ELKLK` is `STELKLKM`, `EGt` is `STEGtM`; `n = 2` has no `l_𝒦 > 2` term).  The factor
`Δ` is not inside `Dgrid`. -/
def Dgrid (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz) :
    Zd d (sz.L n) × Zd d (sz.L n) → ℂ :=
  fun a => sz.STELKLKM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false] ![a.1, a.2]
    + sz.STEGtM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false] ![a.1, a.2]

/-- **`R_j`**: the discretization remainder of the predictable part, named by subtraction
(RBM1D `Rgrid`, `Gauss/GridExpansion.lean:283`): `predInc_j = Δ · D_j + R_j`. -/
def Rgrid (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) : ℂ :=
  predInc sz E s t K n j ω a - (gridStep s t K n : ℂ) * Dgrid sz E s t K n j ω a

/-- `predInc_j = Δ · D_j + R_j` (every `ω`, every label; definitional). -/
theorem Expansion_predInc_eq_Dgrid_add_Rgrid (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    predInc sz E s t K n j ω a
      = (gridStep s t K n : ℂ) * Dgrid sz E s t K n j ω a + Rgrid sz E s t K n j ω a := by
  unfold Rgrid; ring

/-- `Avec` read through the list-based loop `loopL` (`Expansion:48`: `gloop … (pmLoop a₁ a₂) - Kpm`). -/
private theorem Expansion_Avec_eq (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    Avec sz E s t K n k ω a
      = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n k ω))
          (zt E (gridTime s t K n k)) (loopOf ![true, false] ![a.1, a.2])
        - sz.STKloop n E (gridTime s t K n k) ![true, false] ![a.1, a.2] := by
  simp only [Avec, Sizes.STLKM, Sizes.STLM, loopFine, loopM_eq_loopL]

/-- The two-loop observable `loopPM` is the list-based loop at `loopOf ![+,-] ![a,b]`. -/
private theorem Expansion_loopPM_eq (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (a b : Zd d L) :
    Green.loopPM d L W E u M a b
      = loopL d L W (blockMat d L W M) (zt E u) (loopOf ![true, false] ![a, b]) := by
  simp only [Green.loopPM, loopFine, loopM_eq_loopL]

open scoped Matrix.Norms.Operator in
/-- The crude bound of `A_j` at the grid time `u_j` (`u_j < 1`): `‖𝓛‖ ≤ N (η_u⁻¹ W^{-d})²` by
`norm_gloop_le_crude` (loop length 2, `N = (L W)^d`) and `‖𝒦‖ ≤ W^{-d} (1-u)⁻¹` by
`‖Θ‖ ≤ (1-u)⁻¹` (`Expansion:332`; `W^{-2}`, `(L W)^2` there). -/
private theorem Expansion_norm_Avec_le (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E| < 2) (ω : PathΩ sz) (hu0 : 0 ≤ gridTime s t K n j) (hu1 : gridTime s t K n j < 1)
    (b : Zd d (sz.L n) × Zd d (sz.L n)) :
    ‖Avec sz E s t K n j ω b‖
      ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ)
            * ((etaT E (gridTime s t K n j))⁻¹ * (((sz.W n : ℝ) ^ d)⁻¹)) ^ 2
          + ((sz.W n : ℝ) ^ d)⁻¹ * (1 - gridTime s t K n j)⁻¹ := by
  have hη : 0 < etaT E (gridTime s t K n j) := etaT_pos hE hu1
  have hpos : 0 < (1 - gridTime s t K n j) * (mE E).im :=
    mul_pos (by linarith) (mE_im_pos hE)
  have hz : etaT E (gridTime s t K n j) ≤ |(zt E (gridTime s t K n j)).im| := by
    rw [zt_im, abs_of_pos hpos]
    exact le_of_eq rfl
  have hH : (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω)).IsHermitian :=
    (pathH_isHermitian sz s t K n j ω).submatrix _
  have h1 := norm_gloop_le_crude (d := d) (L := sz.L n) (W := sz.W n) hH hη hz
    (loopOf ![true, false] ![b.1, b.2]) rfl
  have hlen : (loopOf ![true, false] ![b.1, b.2]).a.length = 2 := rfl
  rw [hlen] at h1
  have h2 : ‖sz.STKloop n E (gridTime s t K n j) ![true, false] ![b.1, b.2]‖
      ≤ ((sz.W n : ℝ) ^ d)⁻¹ * (1 - gridTime s t K n j)⁻¹ := by
    rw [Expansion_STKloop_eq sz n hE, norm_mul, norm_inv, norm_pow]
    have hW : ‖((sz.W n : ℕ) : ℂ)‖ = ((sz.W n : ℕ) : ℝ) := by simp
    rw [hW]
    have h4 : ‖Theta d (sz.L n) (sz.lam n) ((gridTime s t K n j : ℝ) : ℂ) b.1 b.2‖
        ≤ (1 - gridTime s t K n j)⁻¹ :=
      (Expansion_norm_entry_le _ b.1 b.2).trans
        (Expansion_norm_Theta_real (sz.three_le_L n) hu0 hu1)
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  rw [Expansion_Avec_eq]
  calc ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
          (zt E (gridTime s t K n j)) (loopOf ![true, false] ![b.1, b.2])
        - sz.STKloop n E (gridTime s t K n j) ![true, false] ![b.1, b.2]‖
      ≤ ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
          (zt E (gridTime s t K n j)) (loopOf ![true, false] ![b.1, b.2])‖
        + ‖sz.STKloop n E (gridTime s t K n j) ![true, false] ![b.1, b.2]‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- The real inequality behind the remainder bound (`Expansion:365`): with `w = W^{-d}`,
`a = (1-u')⁻¹`, `b = (1-u)⁻¹`, `c = η_u⁻¹` all `≤ x = η_{u'}⁻¹`, `1 ≤ x`, `1 ≤ N`. -/
private theorem Expansion_arith {w N a b c x Δ : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hax : a ≤ x) (hbx : b ≤ x) (hcx : c ≤ x) (hx1 : 1 ≤ x)
    (hN : 1 ≤ N) :
    w * a * b ^ 2 * Δ ^ 2 + 3 * Δ ^ 2 * a ^ 2 * (N * (c * w) ^ 2 + w * b)
      ≤ 7 * N * x ^ 4 * Δ ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hΔ2 : 0 ≤ Δ ^ 2 := sq_nonneg Δ
  have h1 : w * a * b ^ 2 ≤ x ^ 3 := by
    calc w * a * b ^ 2 ≤ 1 * a * b ^ 2 := by gcongr
      _ ≤ x * x ^ 2 := by rw [one_mul]; gcongr
      _ = x ^ 3 := by ring
  have h2 : (c * w) ^ 2 ≤ x ^ 2 := by
    have : c * w ≤ x := by nlinarith
    exact pow_le_pow_left₀ (mul_nonneg hc0 hw0) this 2
  have h3 : w * b ≤ x := by nlinarith
  have h4 : N * (c * w) ^ 2 + w * b ≤ N * x ^ 2 + x := by
    have : N * (c * w) ^ 2 ≤ N * x ^ 2 := mul_le_mul_of_nonneg_left h2 (by linarith)
    linarith
  have h5 : a ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ ha0 hax 2
  have h6 : a ^ 2 * (N * (c * w) ^ 2 + w * b) ≤ x ^ 2 * (N * x ^ 2 + x) := by
    have hnn : 0 ≤ N * (c * w) ^ 2 + w * b := by
      have : 0 ≤ N := by linarith
      positivity
    exact mul_le_mul h5 h4 hnn (sq_nonneg x)
  have hx3 : x ^ 3 ≤ N * x ^ 4 := by
    have : x ^ 3 ≤ x ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    have h44 : x ^ 4 ≤ N * x ^ 4 := by nlinarith [pow_pos (show 0 < x by linarith) 4]
    linarith
  have hfin : w * a * b ^ 2 + 3 * (a ^ 2 * (N * (c * w) ^ 2 + w * b)) ≤ 7 * N * x ^ 4 := by
    have : x ^ 2 * (N * x ^ 2 + x) = N * x ^ 4 + x ^ 3 := by ring
    nlinarith
  calc w * a * b ^ 2 * Δ ^ 2 + 3 * Δ ^ 2 * a ^ 2 * (N * (c * w) ^ 2 + w * b)
      = (w * a * b ^ 2 + 3 * (a ^ 2 * (N * (c * w) ^ 2 + w * b))) * Δ ^ 2 := by ring
    _ ≤ 7 * N * x ^ 4 * Δ ^ 2 := mul_le_mul_of_nonneg_right hfin hΔ2

/-- `Θ^{(2)}` of `Step2Defs` at `σ = (+,-)` is the slot-wise generator `thetaGen` acting on the
tensor `p ↦ A ![p.1, p.2]` (`m(+) m(-) = |m|²`; `UBounds:56`). -/
private theorem Expansion_STthetaOp_eq (n : ℕ) (E u : ℝ) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    sz.STthetaOp n E u ![true, false] A ![a.1, a.2]
      = Expansion_thetaGen (d := d) (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) u
          (fun p => A ![p.1, p.2]) a := by
  have hm : Sizes.STmsig E true * Sizes.STmsig E false = ((Complex.normSq (mE E) : ℝ) : ℂ) := by
    simp only [Sizes.STmsig, ite_true, Bool.false_eq_true, ite_false]
    exact Complex.mul_conj _
  have e0 : Function.update (![a.1, a.2] : Fin 2 → Zd d (sz.L n)) 0 = fun b => ![b, a.2] := by
    funext b; ext i; fin_cases i <;> simp
  have e1 : Function.update (![a.1, a.2] : Fin 2 → Zd d (sz.L n)) 1 = fun b => ![a.1, b] := by
    funext b; ext i; fin_cases i <;> simp
  unfold Sizes.STthetaOp Expansion_thetaGen Expansion_thetaGenMat
  rw [Fin.sum_univ_two, e0, e1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hm, Matrix.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]

/-- **The drift split** (RBM1D `condExp_A_succ`, `Gauss/GridExpansion.lean:292`, commit `86573b9`;
`Expansion:406`).  For `j < K n`: `predInc_j = Δ · (ELKLK + EGt)_{u_j}(H_j) + R_j` for every `ω`,
and a.e. `‖R_j‖ ≤ envConst · Δ^{3/2} + 7 N η_{u_{j+1}}⁻⁴ Δ²`, `N = (W L)^d = sz.size n`
(`d = 2`: `N = (W L)²`).  Route: `R_j = r₁ - r₂ - r₃` with `r₁` the drift error of
`condExp_loop_drift`, `r₂` the second-order step of `𝒦` (`Expansion_K_step`), `r₃` the
second-order step of `𝒰` (`Expansion_uopOneStep`), and the cancellation
`genMat - ∂_u 𝒦 - Θ(𝓛 - 𝒦) = ELKLK + EGt` of `hierarchyN2`. -/
theorem condExp_A_succ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j < K n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    (∀ (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)),
        predInc sz E s t K n j ω a
          = (gridStep s t K n : ℂ) * Dgrid sz E s t K n j ω a + Rgrid sz E s t K n j ω a) ∧
      ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
        ‖Rgrid sz E s t K n j ω a‖
          ≤ envConst d (sz.L n) (sz.W n) E 2 (gridTime s t K n (j + 1))
                * gridStep s t K n ^ ((3 : ℝ) / 2)
            + 7 * (sz.size n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4
                * gridStep s t K n ^ 2 := by
  refine ⟨Expansion_predInc_eq_Dgrid_add_Rgrid sz E s t K n j, ?_⟩
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  have hu' := Expansion_gridTime_succ s t K n j
  have hu0 : 0 ≤ gridTime s t K n j := Expansion_gridTime_nonneg s t K n hs0 hst j
  have hu0' : 0 ≤ gridTime s t K n (j + 1) := by rw [hu']; linarith
  have hu1j : gridTime s t K n j < 1 := by rw [hu'] at hu1; linarith
  have hξ : ‖((Complex.normSq (mE E) : ℝ) : ℂ)‖ = 1 := by
    rw [Expansion_normSq_mE hE.le]; simp
  have hdrift : ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      ‖(pathP sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
              (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2])
              | filt sz j] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
              (zt E (gridTime s t K n j)) (loopOf ![true, false] ![a.1, a.2])
          - (gridStep s t K n : ℂ) *
              genMat d (sz.L n) (sz.W n) (sz.lam n) E (gridTime s t K n j)
                (pathH sz s t K n j ω) (loopOf ![true, false] ![a.1, a.2])‖
        ≤ envConst d (sz.L n) (sz.W n) E (loopOf ![true, false] ![a.1, a.2]).length
            (gridTime s t K n (j + 1)) * gridStep s t K n ^ ((3 : ℝ) / 2) :=
    ae_all_iff.2 fun a =>
      condExp_loop_drift sz s t K n j E hE (I := loopOf ![true, false] ![a.1, a.2]) rfl hs0 hst hK
        hj hu1
  have hce : ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      (pathP sz)[fun ω' => Avec sz E s t K n (j + 1) ω' a | filt sz j] ω
        = (pathP sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
              (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2])
              | filt sz j] ω
          - sz.STKloop n E (gridTime s t K n (j + 1)) ![true, false] ![a.1, a.2] := by
    refine ae_all_iff.2 fun a => ?_
    have hint0 := Expansion_integrable_phi sz s t K n
      (hermTestFun_loopPM sz n E _ hu0' hu1 hE a).1 (j + 1)
    have hint : Integrable (fun ω' : PathΩ sz =>
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
          (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2])) (pathP sz) := by
      have hfun : (fun ω' : PathΩ sz =>
          loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
            (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2]))
          = fun ω' => Green.loopPM d (sz.L n) (sz.W n) E (gridTime s t K n (j + 1))
              (pathH sz s t K n (j + 1) ω') a.1 a.2 :=
        funext fun ω' => (Expansion_loopPM_eq (d := d) (sz.L n) (sz.W n) E _ _ a.1 a.2).symm
      rw [hfun]
      exact hint0
    have h := condExp_sub hint
      (integrable_const (sz.STKloop n E (gridTime s t K n (j + 1)) ![true, false] ![a.1, a.2]))
      (filt sz j)
    have hfg : (fun ω' => Avec sz E s t K n (j + 1) ω' a)
        = (fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
              (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2]))
          - fun _ => sz.STKloop n E (gridTime s t K n (j + 1)) ![true, false] ![a.1, a.2] :=
      funext fun ω' => Expansion_Avec_eq sz E s t K n (j + 1) ω' a
    rw [hfg]
    filter_upwards [h] with ω hω
    rw [hω, Pi.sub_apply, condExp_const ((filt sz).le j)]
  filter_upwards [hdrift, hce] with ω h1 h2 a
  have hier := hierarchyN2 d sz n E hE (gridTime s t K n j) hu0 hu1j
    (pathH sz s t K n j ω) (pathH_isHermitian sz s t K n j ω) a.1 a.2
  have hθ : sz.STthetaOp n E (gridTime s t K n j) ![true, false]
        (sz.STLKM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false]) ![a.1, a.2]
      = Expansion_thetaGen (d := d) (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
          (gridTime s t K n j) (Avec sz E s t K n j ω) a := by
    rw [Expansion_STthetaOp_eq]
    congr 1
  have hA : Avec sz E s t K n j ω a
      = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
          (zt E (gridTime s t K n j)) (loopOf ![true, false] ![a.1, a.2])
        - sz.STKloop n E (gridTime s t K n j) ![true, false] ![a.1, a.2] :=
    Expansion_Avec_eq sz E s t K n j ω a
  have h3 := Expansion_uopOneStep (d := d) (g := sz.lam n) (sz.three_le_L n) hξ hu0 hΔ
    (by rw [← hu']; exact hu1) (Avec sz E s t K n j ω) _
    (fun b => Expansion_norm_Avec_le sz E s t K n j hE ω hu0 hu1j b) a
  rw [← hu'] at h3
  have h4 := Expansion_K_step (d := d) (g := sz.lam n) (sz.three_le_L n)
    ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) hu0 hΔ hu' hu1 a.1 a.2
  have h5 := h1 a
  have hlen : (loopOf ![true, false] ![a.1, a.2]).length = 2 := rfl
  rw [hlen] at h5
  have hK' : ∀ v : ℝ, sz.STKloop n E v ![true, false] ![a.1, a.2]
      = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * Theta d (sz.L n) (sz.lam n) (v : ℂ) a.1 a.2 :=
    fun v => Expansion_STKloop_eq sz n hE v a.1 a.2
  have hKfun : (fun v : ℝ => sz.STKloop n E v ![true, false] ![a.1, a.2])
      = fun v : ℝ => ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * Theta d (sz.L n) (sz.lam n) (v : ℂ) a.1 a.2 :=
    funext hK'
  have hid : Rgrid sz E s t K n j ω a
      = ((pathP sz)[fun ω' : PathΩ sz =>
            loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n (j + 1) ω'))
              (zt E (gridTime s t K n (j + 1))) (loopOf ![true, false] ![a.1, a.2])
              | filt sz j] ω
          - loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (pathH sz s t K n j ω))
              (zt E (gridTime s t K n j)) (loopOf ![true, false] ![a.1, a.2])
          - (gridStep s t K n : ℂ) *
              genMat d (sz.L n) (sz.W n) (sz.lam n) E (gridTime s t K n j)
                (pathH sz s t K n j ω) (loopOf ![true, false] ![a.1, a.2]))
        - ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Theta d (sz.L n) (sz.lam n) ((gridTime s t K n (j + 1) : ℝ) : ℂ) a.1 a.2
            - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Theta d (sz.L n) (sz.lam n) ((gridTime s t K n j : ℝ) : ℂ) a.1 a.2
            - (gridStep s t K n : ℂ) * deriv (fun v : ℝ =>
                (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * Theta d (sz.L n) (sz.lam n) (v : ℂ) a.1 a.2)
                (gridTime s t K n j))
        - (Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n j)
              (gridTime s t K n (j + 1)) (Avec sz E s t K n j ω) a
            - Avec sz E s t K n j ω a
            - (gridStep s t K n : ℂ) * Expansion_thetaGen (d := d) (sz.L n) (sz.lam n)
                ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n j) (Avec sz E s t K n j ω) a) := by
    have hier' : genMat d (sz.L n) (sz.W n) (sz.lam n) E (gridTime s t K n j)
          (pathH sz s t K n j ω) (loopOf ![true, false] ![a.1, a.2])
        - deriv (fun v : ℝ => sz.STKloop n E v ![true, false] ![a.1, a.2]) (gridTime s t K n j)
        = sz.STthetaOp n E (gridTime s t K n j) ![true, false]
              (sz.STLKM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false])
              ![a.1, a.2]
            + sz.STELKLKM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false]
              ![a.1, a.2]
            + sz.STEGtM n E (gridTime s t K n j) (pathH sz s t K n j ω) ![true, false]
              ![a.1, a.2] := hier
    rw [hθ, hKfun] at hier'
    rw [hK'] at hA
    unfold Rgrid Dgrid predInc
    rw [h2 a, hK']
    linear_combination (gridStep s t K n : ℂ) * hier' - hA
  rw [hid]
  have hη := etaT_pos hE hu1
  have hι : 0 < (mE E).im := mE_im_pos hE
  have hι1 : (mE E).im ≤ 1 := by
    have h := Complex.abs_im_le_norm (mE E)
    rw [norm_mE hE.le] at h
    exact (le_abs_self _).trans h
  have hη1 : etaT E (gridTime s t K n (j + 1)) ≤ 1 - gridTime s t K n (j + 1) := by
    unfold etaT
    nlinarith
  have hηu : etaT E (gridTime s t K n (j + 1)) ≤ etaT E (gridTime s t K n j) := by
    unfold etaT
    rw [hu']
    nlinarith
  have hηu0 : 0 < etaT E (gridTime s t K n j) := etaT_pos hE hu1j
  have hu'1 : 0 < 1 - gridTime s t K n (j + 1) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWd : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hW0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hWle : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd
  have hN1 : (1 : ℝ) ≤ (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) := by
    have : 1 ≤ (sz.L n * sz.W n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (sz.W_pos n))
    exact_mod_cast this
  have key := Expansion_arith (w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
    (N := (((sz.L n * sz.W n) ^ d : ℕ) : ℝ)) (a := (1 - gridTime s t K n (j + 1))⁻¹)
    (b := (1 - gridTime s t K n j)⁻¹) (c := (etaT E (gridTime s t K n j))⁻¹)
    (x := (etaT E (gridTime s t K n (j + 1)))⁻¹) (Δ := gridStep s t K n) hW0 hWle
    (inv_nonneg.2 hu'1.le) (inv_nonneg.2 (by linarith)) (inv_nonneg.2 hηu0.le)
    (inv_anti₀ hη hη1) (inv_anti₀ hη (hη1.trans (by linarith))) (inv_anti₀ hη hηu)
    ((one_le_inv₀ hη).2 (hη1.trans (by linarith))) hN1
  have hNsize : (sz.size n : ℝ) = (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) := by
    rw [Sizes.size, mul_comm]
  have hnc : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    rw [norm_inv, norm_pow]; simp
  rw [hnc] at h4
  have gen : ∀ (r1 r2 r3 : ℂ) (b1 b2 b3 : ℝ), ‖r1‖ ≤ b1 → ‖r2‖ ≤ b2 → ‖r3‖ ≤ b3 →
      ‖r1 - r2 - r3‖ ≤ b1 + b2 + b3 := fun r1 r2 r3 b1 b2 b3 e1 e2 e3 =>
    (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add e1 e2)) e3)
  refine (gen _ _ _ _ _ _ h5 h4 h3).trans ?_
  rw [hNsize]
  linarith [key]

/-- `condExp_A_succ` with `t n < 1` in place of `u_{j+1} < 1` (`u_{j+1} ≤ u_{K n} = t n` for
`j < K n`). -/
theorem Expansion_condExp_A_succ_of_lt_one (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (hj : j < K n) :
    (∀ (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)),
        predInc sz E s t K n j ω a
          = (gridStep s t K n : ℂ) * Dgrid sz E s t K n j ω a + Rgrid sz E s t K n j ω a) ∧
      ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
        ‖Rgrid sz E s t K n j ω a‖
          ≤ envConst d (sz.L n) (sz.W n) E 2 (gridTime s t K n (j + 1))
                * gridStep s t K n ^ ((3 : ℝ) / 2)
            + 7 * (sz.size n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4
                * gridStep s t K n ^ 2 :=
  condExp_A_succ sz E s t K n j hE hs0 hst hK hj
    (Expansion_gridTime_lt_one s t K n hst hK ht1 (by omega))

/-- The same bound in the `O(Δ^{3/2})` form: `‖R_j‖ ≤ (envConst + 7 N η_{u_{j+1}}⁻⁴) Δ^{3/2}`
(`Δ ≤ u_{j+1} < 1`, so `Δ² ≤ Δ^{3/2}`). -/
theorem Expansion_condExp_A_succ_rpow (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)
    (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (hK : K n ≠ 0) (hj : j < K n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      ‖Rgrid sz E s t K n j ω a‖
        ≤ (envConst d (sz.L n) (sz.W n) E 2 (gridTime s t K n (j + 1))
            + 7 * (sz.size n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4)
          * gridStep s t K n ^ ((3 : ℝ) / 2) := by
  have hΔ := Expansion_gridStep_nonneg s t K n hst
  have hu' := Expansion_gridTime_succ s t K n j
  have hu0 : 0 ≤ gridTime s t K n j := Expansion_gridTime_nonneg s t K n hs0 hst j
  have hΔ1 : gridStep s t K n ≤ 1 := by linarith
  have hsq : gridStep s t K n ^ 2 ≤ gridStep s t K n ^ ((3 : ℝ) / 2) := by
    rcases hΔ.eq_or_lt with h0 | hpos
    · rw [← h0]; norm_num
    · have h := Real.rpow_le_rpow_of_exponent_ge hpos hΔ1 (show (3 : ℝ) / 2 ≤ 2 by norm_num)
      rwa [Real.rpow_two] at h
  filter_upwards [(condExp_A_succ sz E s t K n j hE hs0 hst hK hj hu1).2] with ω h a
  refine (h a).trans ?_
  have hpos : 0 ≤ 7 * (sz.size n : ℝ) * (etaT E (gridTime s t K n (j + 1)))⁻¹ ^ 4 := by
    have : 0 ≤ (etaT E (gridTime s t K n (j + 1)))⁻¹ := inv_nonneg.2 (etaT_pos hE hu1).le
    positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq hpos]

/-! ### 7. The expansion with the split (ticket target 2; RBM1D `grid_expansion`,
`grid_expansion_all`) -/

/-- **The stopped expansion with the drift split at one size index** (105): `StoppedDuhamel105`
with `predInc_j` replaced by `Δ • D_j + R_j` (exact, every `ω`, every stopping index `τ`, every
`k`); the bound on `R_j` is `condExp_A_succ`.  Hypotheses only at `n` (DECISIONS §29 (4)). -/
theorem grid_expansion_all_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz) (hkτ : min k (τ ω) ≤ K n) :
    Avec sz E s t K n (min k (τ ω)) ω
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω)
        + ∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n (min k (τ ω)))
              ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
                + martInc sz E s t K n j ω) := by
  rw [stoppedDuhamel105_at sz E s t K n hE hs0 hst ht1 hK τ k ω hkτ]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext a
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Expansion_predInc_eq_Dgrid_add_Rgrid]

/-- **The stopped expansion with the drift split** (105; `Expansion:588`): the hypotheses of
`stoppedDuhamel105` (for all `n`). -/
theorem grid_expansion_all (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n : ℕ) (τ : PathΩ sz → ℕ) (k : ℕ) (ω : PathΩ sz) (hkτ : min k (τ ω) ≤ K n) :
    Avec sz E s t K n (min k (τ ω)) ω
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n (min k (τ ω))) (Avec sz E s t K n 0 ω)
        + ∑ j ∈ Finset.range (min k (τ ω)),
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n (min k (τ ω)))
              ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
                + martInc sz E s t K n j ω) :=
  grid_expansion_all_at sz E s t K n hE (hs0 n) (hst n) (ht1 n) (hK n) τ k ω hkτ

/-- **The expansion with the split at a fixed `k ≤ K n`, hypotheses at `n`** (RBM1D
`grid_expansion`; the stopping index is the constant `k`). -/
theorem grid_expansion_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0)
    (k : ℕ) (hk : k ≤ K n) (ω : PathΩ sz) :
    Avec sz E s t K n k ω
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n k) (Avec sz E s t K n 0 ω)
        + ∑ j ∈ Finset.range k,
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n k)
              ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
                + martInc sz E s t K n j ω) := by
  have h := grid_expansion_all_at sz E s t K n hE hs0 hst ht1 hK (fun _ => k) k ω
    (by rw [min_self]; exact hk)
  simpa only [min_self] using h

/-- **The expansion with the split at a fixed `k ≤ K n`** (RBM1D `grid_expansion`; the
stopping index is the constant `k`). -/
theorem grid_expansion (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n k : ℕ) (hk : k ≤ K n) (ω : PathΩ sz) :
    Avec sz E s t K n k ω
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
            (gridTime s t K n k) (Avec sz E s t K n 0 ω)
        + ∑ j ∈ Finset.range k,
            Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
              (gridTime s t K n k)
              ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
                + martInc sz E s t K n j ω) :=
  grid_expansion_at sz E s t K n hE (hs0 n) (hst n) (ht1 n) (hK n) k hk ω

/-! ### 8. The martingale part in decomposition form (ticket target 3)

`d = 2` changes (CLAUDE.md §5.2): RBM1D's real `ukerMat` on `LoopArg L 2` (and `Uker_eq_sum_ukerMat`)
is replaced by the merged complex `ukerMat`, `Uop` at `ξ = |m|²`; the weight of the `Z`/`Y` bridges is
`Wt_{v,w}(b, a) = (𝒰_{v,w}(b₁,a₁) 𝒰_{v,w}(b₂,a₂)).re`, the one of `stepDecomp_loopPM`, and the
identification of the complex product with the real weight is `ukerNonneg` (`im = 0`).  RBM1D's
`Φgrid`, `testFun_sub_const`, `Band` are dropped: the loop family is that of
`hermTestFun_loopPM`, and `𝒦` cancels in `martInc` (no reality of `𝒦` is used). -/

section Bridge

/-- **`gridDelta`**: the identity kernel on labels, `δ b a := if b = a then 1 else 0`
(RBM1D `gridDelta`, `Gauss/GridExpansion.lean:685`, commit `86573b9`). -/
def gridDelta (d L : ℕ) (b a : Zd d L × Zd d L) : ℝ := if b = a then 1 else 0

/-- The two-loop observable family at time `u`: `Φ^{(u)}_a(M) = 𝓛_{u,(+,-),(a₁,a₂)}(M)`, the
family of `hermTestFun_loopPM`, `stepDecomp_loopPM`. -/
def Expansion_loopObs (n : ℕ) (E u : ℝ) :
    Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ :=
  fun a M => Green.loopPM d (sz.L n) (sz.W n) E u M a.1 a.2

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ)

/-- `linTr` of `Ab` is the `U`-weighted sum of the per-label `linTr`s (real-linearity in `U`;
RBM1D `lin_Ab_eq_sum'`, `Gauss/GridExpansion.lean:690`). -/
private theorem Expansion_linTr_Ab
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) (X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    linTr n (Ab sz s t K n j Φ U b ω) X
      = ∑ a : Zd d (sz.L n) × Zd d (sz.L n), U b a * linTr n (gradMat (Φ a) (pathH sz s t K n j ω)) X := by
  unfold linTr Ab
  rw [Matrix.sum_mul, Matrix.trace_sum]
  have hstep : ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      Matrix.trace ((U b a : ℂ) • gradMat (Φ a) (pathH sz s t K n j ω) * X)
        = (U b a : ℂ) * Matrix.trace (gradMat (Φ a) (pathH sz s t K n j ω) * X) := by
    intro a
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun a _ => hstep a, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- `stepZ` at the identity kernel is the single-label linear term (RBM1D `stepZ_gridDelta`,
`Gauss/GridExpansion.lean:707`). -/
private theorem Expansion_stepZ_gridDelta
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) (ω : PathΩ sz) :
    stepZ sz s t K n j Φ (gridDelta d (sz.L n)) a ω
      = Real.sqrt (gridStep s t K n)
          * linTr n (gradMat (Φ a) (pathH sz s t K n j ω)) (Sizes.seqXmat sz n (ω (j + 1))) := by
  unfold stepZ
  rw [Expansion_linTr_Ab]
  congr 1
  rw [Finset.sum_eq_single a]
  · simp [gridDelta]
  · intro c _ hc
    simp [gridDelta, Ne.symm hc]
  · simp

/-- **`stepZ` is linear in the real kernel `U`** (pointwise, every `ω`):
`stepZ U b ω = Σ_a U(b,a) · stepZ δ a ω` (RBM1D `stepZ_eq_sum_gridDelta`,
`Gauss/GridExpansion.lean:723`). -/
theorem stepZ_eq_sum_gridDelta
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) (b : Zd d (sz.L n) × Zd d (sz.L n))
    (ω : PathΩ sz) :
    stepZ sz s t K n j Φ U b ω
      = ∑ a : Zd d (sz.L n) × Zd d (sz.L n), U b a * stepZ sz s t K n j Φ (gridDelta d (sz.L n)) a ω := by
  rw [show stepZ sz s t K n j Φ U b ω = Real.sqrt (gridStep s t K n)
      * linTr n (Ab sz s t K n j Φ U b ω) (Sizes.seqXmat sz n (ω (j + 1))) from rfl,
    Expansion_linTr_Ab, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_stepZ_gridDelta]
  ring

/-- The entries of `𝒰_{v,w}` at `ξ = |m|²` are real (`ukerNonneg`, `|E| ≤ 2`), so the complex
product of two entries is the complex number of its real part. -/
private theorem Expansion_ukerMat_mul_eq (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v)
    (hvw : v ≤ w) (hw1 : w < 1) (b a : Zd d (sz.L n) × Zd d (sz.L n)) :
    (((ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re : ℝ) : ℂ)
      = ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
        * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2 := by
  have hξ : Complex.normSq (mE E) = 1 := Expansion_normSq_mE hE
  have h1 := Expansion_ukerNonneg (g := sz.lam n) (sz.three_le_L n)
    (Complex.normSq_nonneg (mE E)) hv0 hvw (by rw [hξ]; linarith) b.1 a.1
  have h2 := Expansion_ukerNonneg (g := sz.lam n) (sz.three_le_L n)
    (Complex.normSq_nonneg (mE E)) hv0 hvw (by rw [hξ]; linarith) b.2 a.2
  apply Complex.ext
  · simp
  · simp [Complex.mul_im, h1.1, h2.1]

/-- **(R1) `stepZ_ukerMat_eq_Uker`**: for every `ω` and `0 ≤ v ≤ w < 1`, `|E| ≤ 2`, the kernel
folded into the label weight equals `𝒰_{v,w}` applied to the `w`-independent label vector
`a ↦ stepZ δ a ω` (RBM1D `stepZ_ukerMat_eq_Uker`, `Gauss/GridExpansion.lean:737`). -/
theorem stepZ_ukerMat_eq_Uker
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (b : Zd d (sz.L n) × Zd d (sz.L n)) (ω : PathΩ sz) :
    (stepZ sz s t K n j Φ
        (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
          * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω : ℂ)
      = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w
          (fun a => (stepZ sz s t K n j Φ (gridDelta d (sz.L n)) a ω : ℂ)) b := by
  rw [stepZ_eq_sum_gridDelta]
  push_cast
  unfold Uop
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_ukerMat_mul_eq sz n E hE hv0 hvw hw1 b a]

/-- The label-`a` step of `stepXi` at the identity kernel: `Φ_a(H_{j+1}) - E[Φ_a(H_{j+1}) | F_j]`. -/
private theorem Expansion_stepXi_delta
    (Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) (ω : PathΩ sz) :
    stepXi sz s t K n j Φ (gridDelta d (sz.L n)) a ω
      = Φ a (pathH sz s t K n (j + 1) ω)
        - (pathP sz)[fun ω' => Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω := by
  have hfun : (fun ω' : PathΩ sz => ∑ c : Zd d (sz.L n) × Zd d (sz.L n),
        ((gridDelta d (sz.L n) a c : ℝ) : ℂ) * Φ c (pathH sz s t K n (j + 1) ω'))
      = fun ω' => Φ a (pathH sz s t K n (j + 1) ω') := by
    funext ω'
    rw [Finset.sum_eq_single a]
    · simp [gridDelta]
    · intro c _ hc
      simp [gridDelta, Ne.symm hc]
    · simp
  have h1 := congrFun hfun ω
  unfold stepXi
  rw [h1, hfun]

/-- **`stepXi` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`
(RBM1D `stepXi_eq_sum_gridDelta_ae`, `Gauss/GridExpansion.lean:747`; `TestFun` is replaced by
`HermTestFun`, the integrability by `Expansion_integrable_phi`). -/
theorem stepXi_eq_sum_gridDelta_ae
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      stepXi sz s t K n j Φ U b ω
        = ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * stepXi sz s t K n j Φ (gridDelta d (sz.L n)) a ω := by
  refine ae_all_iff.mpr fun b => ?_
  have hint_a : ∀ a ∈ (Finset.univ : Finset (Zd d (sz.L n) × Zd d (sz.L n))),
      Integrable (fun ω : PathΩ sz => (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω)) (pathP sz) :=
    fun a _ => (Expansion_integrable_phi sz s t K n (hΦ a) (j + 1)).const_mul (U b a : ℂ)
  have hcondsum := condExp_finsetSum hint_a (filt sz j)
  have hsmul_ae : ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      (pathP sz)[fun ω' => (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω
        = (U b a : ℂ) * (pathP sz)[fun ω' => Φ a (pathH sz s t K n (j + 1) ω') | filt sz j] ω :=
    ae_all_iff.mpr fun a => condExp_smul (U b a : ℂ)
      (fun ω' => Φ a (pathH sz s t K n (j + 1) ω')) (filt sz j)
  have hsum_fn : (∑ a : Zd d (sz.L n) × Zd d (sz.L n),
        fun ω' : PathΩ sz => (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω'))
      = (fun ω' : PathΩ sz => ∑ a : Zd d (sz.L n) × Zd d (sz.L n),
          (U b a : ℂ) * Φ a (pathH sz s t K n (j + 1) ω')) := by
    funext ω'; simp only [Finset.sum_apply]
  rw [hsum_fn] at hcondsum
  filter_upwards [hcondsum, hsmul_ae] with ω hω1 hω2
  simp_rw [Expansion_stepXi_delta]
  unfold stepXi
  rw [hω1]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => hω2 a]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **`stepY` is linear in the real kernel `U`**, a.e., simultaneously for all labels `b`
(RBM1D `stepY_eq_sum_gridDelta_ae`, `Gauss/GridExpansion.lean:793`). -/
theorem stepY_eq_sum_gridDelta_ae
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (U : Zd d (sz.L n) × Zd d (sz.L n) → Zd d (sz.L n) × Zd d (sz.L n) → ℝ) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      stepY sz s t K n j Φ U b ω
        = ∑ a : Zd d (sz.L n) × Zd d (sz.L n), (U b a : ℂ) * stepY sz s t K n j Φ (gridDelta d (sz.L n)) a ω := by
  filter_upwards [stepXi_eq_sum_gridDelta_ae sz s t K n j hΦ U] with ω hω b
  unfold stepY
  rw [hω b, stepZ_eq_sum_gridDelta sz s t K n j Φ U b ω]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- **(R2) `stepY_ukerMat_eq_Uker_ae`**: for `0 ≤ v ≤ w < 1`, `|E| ≤ 2`, a.e. `ω`, for every label
`b`, the kernel folded into the label weight equals `𝒰_{v,w}` applied to the `w`-independent label
vector `a ↦ stepY δ a ω` (RBM1D `stepY_ukerMat_eq_Uker_ae`, `Gauss/GridExpansion.lean:807`). -/
theorem stepY_ukerMat_eq_Uker_ae
    {Φ : Zd d (sz.L n) × Zd d (sz.L n) → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ}
    (hΦ : ∀ a, HermTestFun sz n (Φ a))
    (E : ℝ) (hE : |E| ≤ 2) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      stepY sz s t K n j Φ
          (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
            * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w
            (fun a => stepY sz s t K n j Φ (gridDelta d (sz.L n)) a ω) b := by
  filter_upwards [stepY_eq_sum_gridDelta_ae sz s t K n j hΦ
    (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
      * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)] with ω hω b
  rw [hω b]
  unfold Uop
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Expansion_ukerMat_mul_eq sz n E hE hv0 hvw hw1 b a]

end Bridge

/-! ### 9. `Zvec`, `Yvec`, the identification `martInc = Zvec + Yvec` and the primed expansion -/

section ExpansionPrime

/-- **`Zvec`**: the `k`-independent label vector of the martingale (`Z`) part of the grid step
ending at index `i` (step `i-1 → i`, loop family at `u_i`, identity kernel):
`Zvec (j+1) ω a = stepZ j (Φ^{(u_{j+1})}) δ a ω` (RBM1D `Zvec`, `Gauss/GridExpansion.lean:825`). -/
noncomputable def Zvec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) : ℂ :=
  (stepZ sz s t K n (i - 1) (Expansion_loopObs sz n E (gridTime s t K n i))
    (gridDelta d (sz.L n)) a ω : ℂ)

/-- **`Yvec`**: the `k`-independent label vector of the quadratic (`Y`) part of the grid step
ending at index `i` (RBM1D `Yvec`, `Gauss/GridExpansion.lean:831`). -/
noncomputable def Yvec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n i : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) : ℂ :=
  stepY sz s t K n (i - 1) (Expansion_loopObs sz n E (gridTime s t K n i))
    (gridDelta d (sz.L n)) a ω

theorem Zvec_succ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    Zvec sz E s t K n (j + 1) ω a
      = (stepZ sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
          (gridDelta d (sz.L n)) a ω : ℂ) := rfl

theorem Yvec_succ (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz)
    (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    Yvec sz E s t K n (j + 1) ω a
      = stepY sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
          (gridDelta d (sz.L n)) a ω := rfl

/-- **The martingale increment is `Z + Y`** (label-wise, a.e.): `martInc_j = Zvec_{j+1} +
Yvec_{j+1}`.  `𝒦` is a constant in `ω'` and cancels in `A_{j+1} - E[A_{j+1} | F_j]`, which is the
identity-kernel `stepXi`; then `stepXi = stepZ + stepY` by the definition of `stepY`. -/
theorem Expansion_martInc_eq_Zvec_add_Yvec (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hu1 : gridTime s t K n (j + 1) < 1) :
    ∀ᵐ ω ∂(pathP sz), ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      martInc sz E s t K n j ω a = Zvec sz E s t K n (j + 1) ω a + Yvec sz E s t K n (j + 1) ω a := by
  have hu0' : 0 ≤ gridTime s t K n (j + 1) :=
    Expansion_gridTime_nonneg s t K n hs0 hst (j + 1)
  refine ae_all_iff.2 fun a => ?_
  have hΦ : HermTestFun sz n (Expansion_loopObs sz n E (gridTime s t K n (j + 1)) a) :=
    (hermTestFun_loopPM sz n E _ hu0' hu1 hE a).1
  have hint := Expansion_integrable_phi sz s t K n hΦ (j + 1)
  have h := condExp_sub hint
    (integrable_const (sz.STKloop n E (gridTime s t K n (j + 1)) ![true, false] ![a.1, a.2]))
    (filt sz j)
  have hfg : (fun ω' => Avec sz E s t K n (j + 1) ω' a)
      = (fun ω' : PathΩ sz => Expansion_loopObs sz n E (gridTime s t K n (j + 1)) a
          (pathH sz s t K n (j + 1) ω'))
        - fun _ => sz.STKloop n E (gridTime s t K n (j + 1)) ![true, false] ![a.1, a.2] := rfl
  filter_upwards [h] with ω hω
  have hmart : martInc sz E s t K n j ω a
      = Expansion_loopObs sz n E (gridTime s t K n (j + 1)) a (pathH sz s t K n (j + 1) ω)
        - (pathP sz)[fun ω' => Expansion_loopObs sz n E (gridTime s t K n (j + 1)) a
            (pathH sz s t K n (j + 1) ω') | filt sz j] ω := by
    unfold martInc
    rw [hfg, hω, Pi.sub_apply, condExp_const ((filt sz).le j)]
    simp only [Avec, Sizes.STLKM, Sizes.STLM, Expansion_loopObs, Green.loopPM]
    ring
  rw [hmart, Zvec_succ, Yvec_succ]
  unfold stepY
  rw [Expansion_stepXi_delta]
  ring

/-- **`𝒰 martInc = Z + Y` (a.e.)**: for `0 ≤ v ≤ w < 1` and `|E| < 2`, a.e. `ω`, for every
label `b`, `𝒰_{v,w} (martInc_j) (b) = stepZ (Wt_{v,w}) b + stepY (Wt_{v,w}) b`, with the family
`Φ^{(u_{j+1})}` and the weights of `stepDecomp_loopPM`.  Here `stepZ` is the linear part
(conditionally sub-Gaussian: `stepDecomp_Z_subG_loopPM`) and `stepY` the quadratic part
(`stepDecomp_Y_sq`); this is the form consumed by the stopped Azuma step. -/
theorem Expansion_uop_martInc_eq (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (n j : ℕ) (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n)
    (hu1 : gridTime s t K n (j + 1) < 1) {v w : ℝ} (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w (martInc sz E s t K n j ω) b
        = (stepZ sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re)
            b ω : ℂ)
          + stepY sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) v w b.2 a.2).re) b ω := by
  have hu0' : 0 ≤ gridTime s t K n (j + 1) :=
    Expansion_gridTime_nonneg s t K n hs0 hst (j + 1)
  have hΦ : ∀ a, HermTestFun sz n (Expansion_loopObs sz n E (gridTime s t K n (j + 1)) a) :=
    fun a => (hermTestFun_loopPM sz n E _ hu0' hu1 hE a).1
  filter_upwards [Expansion_martInc_eq_Zvec_add_Yvec sz E s t K n j hE hs0 hst hu1,
    stepY_ukerMat_eq_Uker_ae sz s t K n j hΦ E hE.le hv0 hvw hw1] with ω hm hy b
  have hm' : martInc sz E s t K n j ω = (fun a => Zvec sz E s t K n (j + 1) ω a)
      + fun a => Yvec sz E s t K n (j + 1) ω a := funext hm
  have hz := stepZ_ukerMat_eq_Uker sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
    E hE.le hv0 hvw hw1 b ω
  rw [hm', Uop_add, Pi.add_apply, hz, hy b]
  rfl

/-- **`𝒰 martInc = Z + Y` at every grid pair, one null set**: a.e. `ω`, for every `j < m ≤ K n`
(so at the random index `m = min k (τ ω)` of a stopped sum) and every label `b`,
`𝒰_{u_{j+1},u_m} (martInc_j) (b) = stepZ (Wt_{u_{j+1},u_m}) b + stepY (Wt_{u_{j+1},u_m}) b` with the
family `Φ^{(u_{j+1})}`; `Expansion_uop_martInc_eq` at `v = u_{j+1}`, `w = u_m`, over the countable
index set (`ae_all_iff`). -/
theorem Expansion_uop_martInc_eq_all (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)
    (hE : |E| < 2) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) :
    ∀ᵐ ω ∂(pathP sz), ∀ j m : ℕ, j < m → m ≤ K n → ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
          (gridTime s t K n m) (martInc sz E s t K n j ω) b
        = (stepZ sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
                (gridTime s t K n (j + 1)) (gridTime s t K n m) b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
                (gridTime s t K n (j + 1)) (gridTime s t K n m) b.2 a.2).re) b ω : ℂ)
          + stepY sz s t K n j (Expansion_loopObs sz n E (gridTime s t K n (j + 1)))
            (fun b a => (ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
                (gridTime s t K n (j + 1)) (gridTime s t K n m) b.1 a.1
              * ukerMat d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ)
                (gridTime s t K n (j + 1)) (gridTime s t K n m) b.2 a.2).re) b ω := by
  refine ae_all_iff.2 fun j => ae_all_iff.2 fun m => ?_
  by_cases hjm : j < m ∧ m ≤ K n
  · have hu1 : gridTime s t K n (j + 1) < 1 :=
      Expansion_gridTime_lt_one s t K n hst hK ht1 (by omega)
    filter_upwards [Expansion_uop_martInc_eq sz E s t K n j hE hs0 hst hu1
      (v := gridTime s t K n (j + 1)) (w := gridTime s t K n m)
      (Expansion_gridTime_nonneg s t K n hs0 hst (j + 1))
      (Expansion_gridTime_mono s t K n hst (by omega))
      (Expansion_gridTime_lt_one s t K n hst hK ht1 hjm.2)] with ω hω _ _ b
    exact hω b
  · exact Filter.Eventually.of_forall fun _ h1 h2 => absurd ⟨h1, h2⟩ hjm

/-- **(T3′) `grid_expansion'` at one size index** (hypotheses only at `n`, DECISIONS §29 (4)): the primed successor of `grid_expansion`.  For a fixed `k ≤ K n`,
a.e. `ω`, for every label `b`, with the `Z` and `Y` sums in the applied-vector shape
`(Σ_{j<k} 𝒰_{u_{j+1},u_k} (Zvec_{j+1} ω)) b`, `(Σ_{j<k} 𝒰_{u_{j+1},u_k} (Yvec_{j+1} ω)) b`
(label vectors independent of `k`), the drift sum `(Σ_{j<k} Δ • 𝒰_{u_{j+1},u_k} (D_j ω)) b` and the
remainder sum `(Σ_{j<k} 𝒰_{u_{j+1},u_k} (R_j ω)) b` (RBM1D `grid_expansion'`,
`Gauss/GridExpansion.lean:882`). -/
theorem grid_expansion'_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) (k : ℕ) (hk : k ≤ K n) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Avec sz E s t K n k ω b
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec sz E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid sz E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid sz E s t K n j ω)) b := by
  have hae : ∀ᵐ ω ∂(pathP sz), ∀ j : ℕ, j < k → ∀ a : Zd d (sz.L n) × Zd d (sz.L n),
      martInc sz E s t K n j ω a
        = Zvec sz E s t K n (j + 1) ω a + Yvec sz E s t K n (j + 1) ω a := by
    refine ae_all_iff.2 fun j => ?_
    by_cases hjk : j < k
    · have hu1 : gridTime s t K n (j + 1) < 1 :=
        Expansion_gridTime_lt_one s t K n hst hK ht1 (by omega)
      filter_upwards [Expansion_martInc_eq_Zvec_add_Yvec sz E s t K n j hE hs0 hst hu1]
        with ω hω _
      exact hω
    · exact Filter.Eventually.of_forall fun _ h => absurd h hjk
  filter_upwards [hae] with ω hω b
  rw [grid_expansion_at sz E s t K n hE hs0 hst ht1 hK k hk ω]
  have hsum : ∑ j ∈ Finset.range k,
        Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
          (gridTime s t K n k)
          ((gridStep s t K n : ℂ) • Dgrid sz E s t K n j ω + Rgrid sz E s t K n j ω
            + martInc sz E s t K n j ω)
      = (∑ j ∈ Finset.range k,
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Zvec sz E s t K n (j + 1) ω))
        + (∑ j ∈ Finset.range k,
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Yvec sz E s t K n (j + 1) ω))
        + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Dgrid sz E s t K n j ω))
        + (∑ j ∈ Finset.range k,
          Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
            (gridTime s t K n k) (Rgrid sz E s t K n j ω)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hmj : martInc sz E s t K n j ω
        = (Zvec sz E s t K n (j + 1) ω) + (Yvec sz E s t K n (j + 1) ω) :=
      funext (hω j (Finset.mem_range.1 hj))
    rw [hmj]
    simp only [Uop_add, Uop_smul]
    abel
  rw [hsum]
  simp only [Pi.add_apply]
  ring

/-- **(T3′) `grid_expansion'`** (`Expansion:958`): `grid_expansion'_at` under the hypotheses for
all `n`. -/
theorem grid_expansion' (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n k : ℕ) (hk : k ≤ K n) :
    ∀ᵐ ω ∂(pathP sz), ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Avec sz E s t K n k ω b
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec sz E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid sz E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid sz E s t K n j ω)) b :=
  grid_expansion'_at sz E s t K n hE (hs0 n) (hst n) (ht1 n) (hK n) k hk

/-- **(T4′) `grid_expansion_all'` at one size index** (hypotheses only at `n`): the statement of `grid_expansion'` a.e. simultaneously for
every `k ≤ K n` and every label `b` (one null set; RBM1D `grid_expansion_all'`,
`Gauss/GridExpansion.lean:928`). -/
theorem grid_expansion_all'_at (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) :
    ∀ᵐ ω ∂(pathP sz), ∀ k : ℕ, k ≤ K n → ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Avec sz E s t K n k ω b
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec sz E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid sz E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid sz E s t K n j ω)) b := by
  refine ae_all_iff.mpr fun k => ?_
  by_cases hk : k ≤ K n
  · filter_upwards [grid_expansion'_at sz E s t K n hE hs0 hst ht1 hK k hk] with ω hω _
    exact hω
  · exact Filter.Eventually.of_forall fun _ h => absurd h hk

/-- **(T4′) `grid_expansion_all'`** (`Expansion:1022`): `grid_expansion_all'_at` under the
hypotheses for all `n`. -/
theorem grid_expansion_all' (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (hE : |E| < 2)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hK : ∀ n, K n ≠ 0)
    (n : ℕ) :
    ∀ᵐ ω ∂(pathP sz), ∀ k : ℕ, k ≤ K n → ∀ b : Zd d (sz.L n) × Zd d (sz.L n),
      Avec sz E s t K n k ω b
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n 0)
              (gridTime s t K n k) (Avec sz E s t K n 0 ω) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Zvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Yvec sz E s t K n (j + 1) ω)) b
          + (∑ j ∈ Finset.range k, (gridStep s t K n : ℂ) •
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Dgrid sz E s t K n j ω)) b
          + (∑ j ∈ Finset.range k,
              Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) (gridTime s t K n (j + 1))
                (gridTime s t K n k) (Rgrid sz E s t K n j ω)) b :=
  grid_expansion_all'_at sz E s t K n hE (hs0 n) (hst n) (ht1 n) (hK n)

end ExpansionPrime

/-! ### 8. Compiled nonempty instances at the admissible sequence `sz0`

`RBM.Gauss.SizesInst.sz0` (`RBM3D/Defs/Sizes.lean`): `d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`,
`N = (W L)^3 = 2097152`.  Data: size index `n = 0`, energy `E = 0` (`|E| = 0 < 2`), `s = 1/10`,
`t = 1/2`, `K = 4` (`Δ = 1/10`, `u_j = 1/10 + j/10`, `u_4 = 1/2 < 1`), a stopping index `τ = 3` and
target `k = 4` (`min k τ = 3 ≤ K`).  Every deterministic hypothesis is discharged; the examples
apply the theorems, not only their hypotheses. -/

section Instances

open RBM.Gauss.SizesInst

private def Expansion_instS : ℕ → ℝ := fun _ => 1 / 10
private def Expansion_instT : ℕ → ℝ := fun _ => 1 / 2
private def Expansion_instK : ℕ → ℕ := fun _ => 4

private theorem Expansion_inst_gridStep :
    gridStep Expansion_instS Expansion_instT Expansion_instK 0 = 1 / 10 := by
  norm_num [gridStep, Expansion_instS, Expansion_instT, Expansion_instK]

private theorem Expansion_inst_gridTime (j : ℕ) :
    gridTime Expansion_instS Expansion_instT Expansion_instK 0 j = 1 / 10 + (j : ℝ) / 10 := by
  rw [gridTime, Expansion_inst_gridStep]
  simp only [Expansion_instS]
  ring

private theorem Expansion_inst_lt_one {j : ℕ} (hj : j ≤ 4) :
    gridTime Expansion_instS Expansion_instT Expansion_instK 0 j < 1 := by
  rw [Expansion_inst_gridTime]
  have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  linarith

private theorem Expansion_inst_s0 : ∀ n, 0 ≤ Expansion_instS n := fun _ => by
  norm_num [Expansion_instS]

private theorem Expansion_inst_st : ∀ n, Expansion_instS n ≤ Expansion_instT n := fun _ => by
  norm_num [Expansion_instS, Expansion_instT]

private theorem Expansion_inst_t1 : ∀ n, Expansion_instT n < 1 := fun _ => by
  norm_num [Expansion_instT]

private theorem Expansion_inst_K : ∀ n, Expansion_instK n ≠ 0 := fun _ => by
  norm_num [Expansion_instK]

private theorem Expansion_inst_E : |(0 : ℝ)| < 2 := by norm_num

/-- **`stoppedDuhamel105` at `sz0`**: the stopped Duhamel formula (105) with `τ = 3`, `k = 4`
(`min k τ = 3 ≤ K = 4`), for every sample `ω`. -/
example (ω : PathΩ sz0) :
    Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0
        (min 4 ((fun _ : PathΩ sz0 => 3) ω)) ω
      = Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0 0)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0
              (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω)
        + ∑ j ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
            Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0 (j + 1))
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0
                (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
              (predInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω
                + martInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω) :=
  stoppedDuhamel105 sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0 (fun _ => 3) 4 ω
    (by norm_num [Expansion_instK])

/-- **`grid_expansion_all` at `sz0`**: the stopped expansion with the drift split, `τ = 3`,
`k = 4`, for every sample `ω`. -/
example (ω : PathΩ sz0) :
    Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0
        (min 4 ((fun _ : PathΩ sz0 => 3) ω)) ω
      = Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0 0)
            (gridTime Expansion_instS Expansion_instT Expansion_instK 0
              (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (Avec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω)
        + ∑ j ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
            Uop 3 (sz0.L 0) (sz0.lam 0) ((Complex.normSq (mE 0) : ℝ) : ℂ)
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0 (j + 1))
              (gridTime Expansion_instS Expansion_instT Expansion_instK 0
                (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
              ((gridStep Expansion_instS Expansion_instT Expansion_instK 0 : ℂ)
                  • Dgrid sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω
                + Rgrid sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω
                + martInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 j ω) :=
  grid_expansion_all sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0 (fun _ => 3) 4 ω
    (by norm_num [Expansion_instK])

/-- **`grid_expansion` at `sz0`**, `k = 4 = K`. -/
example (ω : PathΩ sz0) :=
  grid_expansion sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0 4
    (by norm_num [Expansion_instK]) ω

/-- **`condExp_A_succ` at `sz0`**, `n = 0`, `j = 0`: all hypotheses hold together
(`|E| = 0 < 2`, `0 ≤ s = 1/10`, `s ≤ t = 1/2`, `K = 4 ≠ 0`, `j = 0 < 4`, `u_1 = 1/5 < 1`) and the
split `predInc = Δ D + R` and the bound on `R` are the conclusion. -/
example :
    (∀ (ω : PathΩ sz0) (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)),
        predInc sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω a
          = (gridStep Expansion_instS Expansion_instT Expansion_instK 0 : ℂ)
              * Dgrid sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω a
            + Rgrid sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω a) ∧
      ∀ᵐ ω ∂(pathP sz0), ∀ a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0),
        ‖Rgrid sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 ω a‖
          ≤ envConst 3 (sz0.L 0) (sz0.W 0) 0 2
                  (gridTime Expansion_instS Expansion_instT Expansion_instK 0 (0 + 1))
                * gridStep Expansion_instS Expansion_instT Expansion_instK 0 ^ ((3 : ℝ) / 2)
            + 7 * (sz0.size 0 : ℝ)
                * (etaT 0 (gridTime Expansion_instS Expansion_instT Expansion_instK 0 (0 + 1)))⁻¹ ^ 4
                * gridStep Expansion_instS Expansion_instT Expansion_instK 0 ^ 2 :=
  condExp_A_succ sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_K 0) (by norm_num [Expansion_instK])
    (Expansion_inst_lt_one (by norm_num))

/-- `Expansion_condExp_A_succ_of_lt_one` and `Expansion_condExp_A_succ_rpow` at the same data. -/
example :=
  Expansion_condExp_A_succ_of_lt_one sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_E (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0)
    (Expansion_inst_K 0) (by norm_num [Expansion_instK])

example :=
  Expansion_condExp_A_succ_rpow sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_E (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_K 0)
    (by norm_num [Expansion_instK]) (Expansion_inst_lt_one (by norm_num))

/-- The test class at the instance: the two-loop family at `u = 1/10`. -/
private theorem Expansion_inst_herm (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) :
    HermTestFun sz0 0 (Expansion_loopObs sz0 0 0 (1 / 10) a) :=
  (hermTestFun_loopPM sz0 0 0 (1 / 10) (by norm_num) (by norm_num) Expansion_inst_E a).1

/-- The bridge lemmas at `sz0`, `j = 0`, `E = 0`, `(v, w) = (1/10, 1/5)`. -/
example (a : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0)) (ω : PathΩ sz0) :=
  stepZ_ukerMat_eq_Uker sz0 Expansion_instS Expansion_instT Expansion_instK 0 0
    (Expansion_loopObs sz0 0 0 (1 / 10)) 0 (by norm_num) (v := 1 / 10) (w := 1 / 5)
    (by norm_num) (by norm_num) (by norm_num) a ω

example (U : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0) → Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0) → ℝ) :=
  stepXi_eq_sum_gridDelta_ae sz0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_herm U

example (U : Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0) → Zd 3 (sz0.L 0) × Zd 3 (sz0.L 0) → ℝ) :=
  stepY_eq_sum_gridDelta_ae sz0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_herm U

example :=
  stepY_ukerMat_eq_Uker_ae sz0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_herm 0 (by norm_num) (v := 1 / 10) (w := 1 / 5) (by norm_num) (by norm_num)
    (by norm_num)

example :=
  Expansion_martInc_eq_Zvec_add_Yvec sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_E (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_lt_one (by norm_num))

example :=
  Expansion_uop_martInc_eq sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 0
    Expansion_inst_E (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_lt_one (by norm_num))
    (v := 1 / 5) (w := 1 / 2) (by norm_num) (by norm_num) (by norm_num)

example :=
  Expansion_uop_martInc_eq_all sz0 0 Expansion_instS Expansion_instT Expansion_instK 0
    Expansion_inst_E (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0)
    (Expansion_inst_K 0)

/-- **`grid_expansion'` and `grid_expansion_all'` at `sz0`** (`k = 4 = K`; all `k ≤ K`). -/
example :=
  grid_expansion' sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0 4
    (by norm_num [Expansion_instK])

example :=
  grid_expansion_all' sz0 0 Expansion_instS Expansion_instT Expansion_instK Expansion_inst_E
    Expansion_inst_s0 Expansion_inst_st Expansion_inst_t1 Expansion_inst_K 0

/-! The hypotheses-at-`n` forms (DECISIONS §29 (4)) and the window boundaries (DECISIONS §29 (1)):
`s = 0` (`H_0 = 0`, `u_0 = 0`), `t = 99/100` (`η_t` small), and `Δ = 0` (`s = t`, all grid times
equal), each at `sz0`, `n = 0`, `E = 0`, `K = 4`. -/

example (ω : PathΩ sz0) :=
  stoppedDuhamel105_at sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0) (Expansion_inst_K 0)
    (fun _ => 3) 4 ω (by norm_num [Expansion_instK])

example (ω : PathΩ sz0) :=
  grid_expansion_all_at sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0) (Expansion_inst_K 0)
    (fun _ => 3) 4 ω (by norm_num [Expansion_instK])

example (ω : PathΩ sz0) :=
  grid_expansion_at sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0) (Expansion_inst_K 0)
    4 (by norm_num [Expansion_instK]) ω

example :=
  grid_expansion'_at sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0) (Expansion_inst_K 0)
    4 (by norm_num [Expansion_instK])

example :=
  grid_expansion_all'_at sz0 0 Expansion_instS Expansion_instT Expansion_instK 0 Expansion_inst_E
    (Expansion_inst_s0 0) (Expansion_inst_st 0) (Expansion_inst_t1 0) (Expansion_inst_K 0)

/-- Boundary `s = 0` (`u_0 = 0`, `Δ = 1/8`): the stopped expansion. -/
example (ω : PathΩ sz0) :=
  grid_expansion_all_at sz0 0 (fun _ => 0) (fun _ => 1 / 2) (fun _ => 4) 0 Expansion_inst_E
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => 3) 4 ω (by norm_num)

/-- Boundary `s = t = 1/2` (`Δ = 0`, all grid times `1/2`): the stopped expansion. -/
example (ω : PathΩ sz0) :=
  grid_expansion_all_at sz0 0 (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 4) 0 Expansion_inst_E
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ => 3) 4 ω (by norm_num)

/-- Boundary `s = 0`, `t = 99/100` (`u_4 = 0.99`), last step `j = 3`: the drift split. -/
example :=
  condExp_A_succ sz0 0 (fun _ => 0) (fun _ => 99 / 100) (fun _ => 4) 0 3 Expansion_inst_E
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [gridTime, gridStep])

/-- Boundary `Δ = 0` (`s = t = 1/2`), `j = 0`: the drift split. -/
example :=
  condExp_A_succ sz0 0 (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 4) 0 0 Expansion_inst_E
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [gridTime, gridStep])

end Instances

end RBM.Path

end
