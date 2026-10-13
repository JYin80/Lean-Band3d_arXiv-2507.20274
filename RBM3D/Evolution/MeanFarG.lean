/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Evolution.MeanFar
import RBM3D.Chain.CltGen

/-!
# The mean part `𝔼 f^{far}` of the CLT step of case (i) over the carrier (ticket T2479, X1b-1, target 4)

Additive restatement of `Evolution/MeanFar.lean:839-1111, 1248-1915, 1954-2137` (the expectation kernel `𝔼 𝓑`, its
invariances and decay, the assembly at one index `n`, and `meanFar_eventually`) over a flow carrier `C : FlowFM sz` and a law
`μ`; none of the four band files is edited.  Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem;CLT`,
`(eq:boundEfar)` (`3_5:2192-2212`), `(eq:propcalB)` (`3_5:2139-2150`).  Mixed charges `σ 0 ≠ σ 1` only (the range of
`STThPropsg`, `STKpropsg`); the propagator is the carrier's `STThg` (U-C4); the energy enters through `κ ≤ Im (C.m n)`
(X1-C1), no `|E| ≤ 2 - κ`, `‖m‖ = 1`, `PropSpin`, `Theta`, `seqP`, `STLKM` in any generic statement (the
instance section, section 3, is at the band data); no coupling comparison (UBA-C1).

* **Target 4.** `meanFar_eventuallyg` (band `meanFar_eventually` `MeanFar:1980`): for every `τ > 0`, eventually in `n`, for every
  mixed `σ` and `a`, `‖𝔼 f^{far}_{σ,a}‖ ≤ N^τ A^{-6/5} / (|a₁-a₂|^{d-2} + 1)`.
  Premises (those of the pin `STCltFargL` that the mean part reads): admissibility `(𝔠, 𝔡)`, `κ ≤ Im (C.m n)`, `0 ≤ s < t < 1`,
  `CltRepg` (for the loop envelope), `STGdecayWgL` (the three of `HCltOf` it carries), `STReg5I`, `STThPropsg`, `STKpropsg`,
  `STExpInvgL`.  Route: `𝔼𝓑` is translation invariant and symmetric by `STExpInvgL` and `STKpropsg` conjunct 1
  (`meanFarG_B_tr`, `_sym`); `‖𝒦‖ ≤ c₁/A` is `STKpropsg` conjunct 2; the propagator profile is `STThPropsg` conjuncts 1, 3, 5;
  `meanFar_core`, `meanFar_T1`, `meanFar_T2` are used by name.

Reused by name or by `open private` from `MeanFar.lean`: `meanFar_core`, `meanFar_T1`, `meanFar_T2`, `meanFar_Cd`, `meanFar_norm_integral_le`,
`meanFar_zdistInf_le`, `meanFar_zdistInf_neg`, `meanFar_ell_sq`, `meanFar_c3`, `meanFar_c0`, `meanFar_c3_pos`, `meanFar_BctlSTWB`,
`meanFar_Cd_nonneg`, `meanFar_numeric_main`, `meanFar_tiny`, `meanFar_eta_bound`, `meanFar_eps_bound`, `meanFar_pureN`,
`meanFar_inv_pow_eq`, `meanFar_three_halves`.  Restated under the stem `meanFarG_`: what mentions the model (`meanFar_B`,
`meanFar_B_tr`, `_sym`, `meanFar_bad_le`, `meanFar_B_bound`, `meanFar_integral_fFar`, `meanFar_assemble`, `meanFar_n_kernel`,
`meanFar_at_n`, `meanFar_eventually`).  Ported also from the probe text
`t/T2455:RBM3D/Probe/T2455Meas.lean:103-231` (X1-C5 measurement, never merged).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private meanFar_norm_integral_le meanFar_zdistInf_le meanFar_zdistInf_neg meanFar_ell_sq meanFar_c3
  meanFar_c0 meanFar_c3_pos meanFar_BctlSTWB meanFar_Cd_nonneg meanFar_numeric_main meanFar_tiny
  meanFar_eta_bound meanFar_eps_bound meanFar_pureN meanFar_inv_pow_eq meanFar_three_halves
  meanFar_T_le meanFar_n_K
  from RBM3D.Evolution.MeanFar

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The expectation kernel `𝔼 𝓑` and its invariances -/

section Expect

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- The loop envelope at one `(n, u)`: the loops `𝓛^{(2)}_{u,σ,a}` of the carrier are measurable and bounded by `η_u^{-2}`
(generic `walk_measurable_Lloop`, `norm_Lloop_le`; replaces `|E| < 2`, `u < 1`; same text as `cltMom2G_LEnv`). -/
def meanFarG_LEnv (n : ℕ) (u : ℝ) : Prop := ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
  Measurable (fun ω => C.L n u σ a ω) ∧ ∀ ω, ‖C.L n u σ a ω‖ ≤ (etaOf (C.m n) u)⁻¹ ^ 2

/-- `CltRepg` and `κ ≤ Im (C.m n)` give the loop envelope for every `u < 1` (probe `lenv_of_rep`, `T2455Meas:72`). -/
theorem meanFarG_lenv_of_rep {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    (hrep : CltRepg C μ H₀ g' E) {κ : ℝ} (hκ : 0 < κ) (n : ℕ) (hm : κ ≤ (C.m n).im) {u : ℝ} (hu : u < 1) :
    meanFarG_LEnv C n u := by
  intro σ a
  have hη : 0 < etaOf (C.m n) u := mul_pos (sub_pos.2 hu) (lt_of_lt_of_le hκ hm)
  have hmeas : Measurable fun ω : sz.SeqΩ => H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) =>
      Sizes.seqHflow (sz.withLam g') n u ω i j :=
    Measurable.of_eval_matrix _ fun i j => measurable_const.add (Sizes.measurable_seqHflow_entry (sz.withLam g') n u i j)
  refine ⟨?_, fun ω => ?_⟩
  · rw [funext fun ω => (hrep.2.2 n u ω).2 2 σ a]
    exact (walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (C.m n) (E n) u) σ a).comp hmeas
  · rw [(hrep.2.2 n u ω).2 2 σ a]
    exact norm_loopM_le d (sz.L n) (sz.W n) (((hrep.2.1 n).add (Sizes.seqHflow_isHermitian (sz.withLam g') n u ω)).submatrix _)
      hη (by rw [ztOf_im, abs_of_pos hη]) (n := 1) σ a

/-- The first conjunct of `STKpropsg` at one `n`: invariance of `𝒦^{(2)}` (mixed charges, `0 ≤ t < 1`) under translations and
the reflection. -/
def meanFarG_KInv (n : ℕ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
    C.K n t σ (fun i => a i + c) = C.K n t σ a ∧ C.K n t σ (fun i => -a i) = C.K n t σ a

/-- **The mean kernel** `𝔼 𝓑_{ab}`, `𝓑 = (𝓛 - 𝒦)^{(2)}_{s,σ}` (`3_5:2139`; band `meanFar_B`). -/
private def meanFarG_B (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) : ℂ :=
  ∫ ω, (C.L n s σ ![a, b] ω - C.K n s σ ![a, b]) ∂μ

private theorem meanFarG_B_eq [IsProbabilityMeasure μ] (n : ℕ) {s : ℝ} (hL : meanFarG_LEnv C n s) (σ : Fin 2 → Bool)
    (a b : Zd d (sz.L n)) :
    meanFarG_B C μ n s σ a b = (∫ ω, C.L n s σ ![a, b] ω ∂μ) - C.K n s σ ![a, b] := by
  unfold meanFarG_B
  rw [integral_sub (Integrable.of_bound (hL σ ![a, b]).1.aestronglyMeasurable ((etaOf (C.m n) s)⁻¹ ^ 2)
    (Filter.Eventually.of_forall fun ω => (hL σ ![a, b]).2 ω)) (integrable_const _), integral_const]
  simp

/-- **Translation invariance of `𝔼 𝓑`** (`3_5:2196`): `𝔼𝓛` by `STExpInvgL`, `𝒦` by `STKpropsg` conjunct 1
(band `meanFar_B_tr`). -/
private theorem meanFarG_B_tr [IsProbabilityMeasure μ] (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) (hL : meanFarG_LEnv C n s)
    (hX : STExpInvgL C μ) (hK : meanFarG_KInv C n) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a b c : Zd d (sz.L n)) :
    meanFarG_B C μ n s σ (a + c) (b + c) = meanFarG_B C μ n s σ a b := by
  rw [meanFarG_B_eq C μ n hL, meanFarG_B_eq C μ n hL]
  have h := (hX n s hs0 hs σ ![a, b] c).1
  have hk := (hK s hs0 hs σ hσ ![a, b] c).1
  have e : (fun i => (![a, b] : Fin 2 → Zd d (sz.L n)) i + c) = ![a + c, b + c] := by
    funext i; fin_cases i <;> simp
  rw [e] at h hk
  rw [h, hk]

/-- **Symmetry of `𝔼 𝓑`** (`3_5:2196`): reflection and the translation by `a + b` (band `meanFar_B_sym`). -/
private theorem meanFarG_B_sym [IsProbabilityMeasure μ] (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < 1) (hL : meanFarG_LEnv C n s)
    (hX : STExpInvgL C μ) (hK : meanFarG_KInv C n) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a b : Zd d (sz.L n)) :
    meanFarG_B C μ n s σ a b = meanFarG_B C μ n s σ b a := by
  rw [meanFarG_B_eq C μ n hL, meanFarG_B_eq C μ n hL]
  have hr := (hX n s hs0 hs σ ![a, b] 0).2
  have ht := (hX n s hs0 hs σ ![-a, -b] (a + b)).1
  have kr := (hK s hs0 hs σ hσ ![a, b] 0).2
  have kt := (hK s hs0 hs σ hσ ![-a, -b] (a + b)).1
  have e1 : (fun i => -((![a, b] : Fin 2 → Zd d (sz.L n)) i)) = ![-a, -b] := by
    funext i; fin_cases i <;> simp
  have e2 : (fun i => (![-a, -b] : Fin 2 → Zd d (sz.L n)) i + (a + b)) = ![b, a] := by
    funext i; fin_cases i <;> simp
  rw [e1] at hr kr
  rw [e2] at ht kt
  rw [← hr, ← ht, ← kr, ← kt]

/-- The `≺` bound of `(Eq:Gdecay_w)` at `u = s` (`STGdecayWgL`) for the entry `𝓑_{ab}` holds off an event of probability
`≤ N^{-D₁}`, by taking the witness `u = (s, σ, (a,b))` in the union inside `PrecL` (band `meanFar_bad_le`; probe text). -/
private theorem meanFarG_bad_le {s t : ℕ → ℝ} {Cd : ℝ} (hs1 : ∀ n, s n < 1) (hst : ∀ n, s n ≤ t n)
    (hG : STGdecayWgL C μ s t Cd) {Dw : ℝ} (hDw : 0 < Dw) {τ D₁ : ℝ} (hτ : 0 < τ) (hD₁ : 0 < D₁) :
    ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)),
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ (1 / 5 : ℝ) * STWB sz n (s n) (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖C.L n (s n) σ ![a, b] ω - C.K n (s n) σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
  filter_upwards [hG Dw hDw τ hτ D₁ hD₁] with n hn σ a b
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  refine ⟨(⟨s n, le_rfl, hst n⟩, σ, ![a, b]), ?_⟩
  have h1 : (1 - s n) ≠ 0 := (sub_pos.2 (hs1 n)).ne'
  simp only [div_self h1, Real.one_rpow, one_mul]
  have e : (![a, b] : Fin 2 → Zd d (sz.L n)) 0 - (![a, b] : Fin 2 → Zd d (sz.L n)) 1 = a - b := by simp
  rw [e]
  exact hω

/-- The pointwise bound of `‖𝔼 𝓑_{ab}‖` from the `≺` bound off an event of probability `≤ N^{-D₁}`:
`‖𝔼𝓑_{ab}‖ ≤ N^τ Z + (η_s^{-2} + |𝒦_{ab}|) N^{-D₁}` (a.s. envelope of `meanFarG_LEnv`; band `meanFar_B_bound`). -/
private theorem meanFarG_B_bound [IsProbabilityMeasure μ] (n : ℕ) {s : ℝ} (hL : meanFarG_LEnv C n s) (σ : Fin 2 → Bool)
    (a b : Zd d (sz.L n)) {τ Z D₁ : ℝ} (hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z)
    (hP : μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z < ‖C.L n s σ ![a, b] ω - C.K n s σ ![a, b]‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))) :
    ‖meanFarG_B C μ n s σ a b‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Z +
      ((etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![a, b]‖) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
  have hmeas : Measurable fun ω => C.L n s σ ![a, b] ω - C.K n s σ ![a, b] :=
    (hL σ ![a, b]).1.sub measurable_const
  have hall : ∀ ω, ‖C.L n s σ ![a, b] ω - C.K n s σ ![a, b]‖ ≤ (etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![a, b]‖ :=
    fun ω => (norm_sub_le _ _).trans (add_le_add ((hL σ ![a, b]).2 ω) le_rfl)
  have h := meanFar_norm_integral_le μ (fun ω => C.L n s σ ![a, b] ω - C.K n s σ ![a, b]) hmeas _ _ hZ hall
  have hreal : μ.real {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z < ‖C.L n s σ ![a, b] ω - C.K n s σ ![a, b]‖} ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    rw [Measure.real]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hP
    rwa [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at this
  have hC : 0 ≤ (etaOf (C.m n) s)⁻¹ ^ 2 + ‖C.K n s σ ![a, b]‖ := by positivity
  unfold meanFarG_B
  refine h.trans ?_
  gcongr

open Classical in
/-- **The mean of `f^{far}`**: `𝔼 f^{far}_{σ,a}` is `f^{far}` with `𝓑` replaced by `𝔼𝓑` (`3_5:2192`; band
`meanFar_integral_fFar`; probe text). -/
private theorem meanFarG_integral_fFar [IsProbabilityMeasure μ] (n : ℕ) {s t : ℝ} (hL : meanFarG_LEnv C n s)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ∫ ω, STfFarg C n s t σ a ω ∂μ =
      (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
          Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
        ∑ b₂ : Zd d (sz.L n),
          STThg C n (σ 0) (σ 1) t (a 0) b₁ * meanFarG_B C μ n s σ b₁ b₂ *
            (STThg C n (σ 0) (σ 1) t b₂ (a 1) - STThg C n (σ 0) (σ 1) t b₁ (a 1)) := by
  unfold STfFarg
  have hX : ∀ b₁ b₂ : Zd d (sz.L n), Integrable (fun ω => C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) μ :=
    fun b₁ b₂ => (Integrable.of_bound (hL σ ![b₁, b₂]).1.aestronglyMeasurable ((etaOf (C.m n) s)⁻¹ ^ 2)
      (Filter.Eventually.of_forall fun ω => (hL σ ![b₁, b₂]).2 ω)).sub (integrable_const _)
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun b₁ _ => integrable_finsetSum _
    (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _))]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [integral_finsetSum _ (fun b₂ _ => ((hX b₁ b₂).const_mul _).mul_const _)]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [integral_mul_const, integral_const_mul]
  rfl

/-- **The assembly at one size index**: `‖𝔼 f^{far}_{σ,a}‖ ≤ (1-s)² [C_d K₁K₂K (1+log(L+1)) (dw+1)⁴ / (|a₁-a₂|+1)^{d-2} +
2K₁²K' L^{2d}]` from the decay of the propagator (`hT1`, `hT2`; the shift `hsh` is `STThPropsg` conjunct 1) and of the mean kernel
(`hBx` everywhere, `hBy` beyond the window `w`), with `K = P₀ + ε₁ (dw+1)^{d-2}`, `K' = ε₂` (band `meanFar_assemble`). -/
private theorem meanFarG_assemble [IsProbabilityMeasure μ] (n : ℕ) {s t : ℝ} (hd : 3 ≤ d) (hL : meanFarG_LEnv C n s)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hX : STExpInvgL C μ) (hK : meanFarG_KInv C n) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1)
    (a : Fin 2 → Zd d (sz.L n))
    (hsh : ∀ x y, STThg C n (σ 0) (σ 1) t x y = STThg C n (σ 0) (σ 1) t 0 (y - x))
    (w K₁ K₂ P₀ ε₁ ε₂ : ℝ) (hw : 0 ≤ w) (hK₂ : 0 ≤ K₂) (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂)
    (hT1 : ∀ x : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t 0 x‖ ≤
        K₁ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2))
    (hT2 : ∀ a' r : Zd d (sz.L n), ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ (d : ℝ) * w →
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) a' : ℕ) : ℝ) →
      ‖STThg C n (σ 0) (σ 1) t 0 (a' + r) + STThg C n (σ 0) (σ 1) t 0 (a' - r) -
          2 * STThg C n (σ 0) (σ 1) t 0 a'‖ ≤
        K₂ * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 / (((zdistInf d (sz.L n) a' : ℕ) : ℝ) + 1) ^ d)
    (hBx : ∀ x : Zd d (sz.L n), ‖meanFarG_B C μ n s σ 0 x‖ ≤
      P₀ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ε₁)
    (hBy : ∀ x : Zd d (sz.L n), w < ((zdistInf d (sz.L n) x : ℕ) : ℝ) → ‖meanFarG_B C μ n s σ 0 x‖ ≤ ε₂) :
    ‖∫ ω, STfFarg C n s t σ a ω ∂μ‖ ≤ (1 - s) ^ 2 *
      (meanFar_Cd d * K₁ * K₂ * (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) *
          (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1)) * ((d : ℝ) * w + 1) ^ 4 /
          (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) +
        2 * K₁ ^ 2 * ε₂ * ((((sz.L n : ℕ) : ℝ)) ^ d) ^ 2) := by
  classical
  rw [meanFarG_integral_fFar C μ n hL σ a, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  set T : Zd d (sz.L n) → ℂ := fun x => STThg C n (σ 0) (σ 1) t 0 x with hT
  have hrw : ∀ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
      STThg C n (σ 0) (σ 1) t (a 0) b₁ * meanFarG_B C μ n s σ b₁ b₂ *
        (STThg C n (σ 0) (σ 1) t b₂ (a 1) - STThg C n (σ 0) (σ 1) t b₁ (a 1)) =
      ∑ b₂ : Zd d (sz.L n), T (b₁ - a 0) * meanFarG_B C μ n s σ b₁ b₂ * (T (a 1 - b₂) - T (a 1 - b₁)) := by
    intro b₁
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [hsh (a 0) b₁, hsh b₂ (a 1), hsh b₁ (a 1)]
  rw [Finset.sum_congr rfl fun b₁ _ => hrw b₁]
  set ρ : ℝ := Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s with hρ
  have hw₁ : 0 ≤ (d : ℝ) * w := by positivity
  have hcore := meanFar_core (d := d) (L := sz.L n) hd T (meanFarG_B C μ n s σ)
    (meanFarG_B_tr C μ n hs0 hs1 hL hX hK σ hσ) (meanFarG_B_sym C μ n hs0 hs1 hL hX hK σ hσ)
    ρ ((d : ℝ) * w) K₁ K₂ (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) ε₂ hw₁ hK₂ hε₂ hT1 hT2
    (fun x hx => ?_) (fun x hx => ?_) a
    (Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      ρ < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧ ρ < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)))
    (fun b hb => (Finset.mem_filter.1 hb).2)
  · exact hcore
  · -- `hB1`
    have hxinf : ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * w := by
      have : ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ ((zdistD d (sz.L n) x : ℕ) : ℝ) := by
        exact_mod_cast zdistInf_le_zdistD d (sz.L n) x
      linarith
    have hY : 0 < (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := by positivity
    have hYle : (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) ≤ ((d : ℝ) * w + 1) ^ (d - 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc ‖meanFarG_B C μ n s σ 0 x‖
        ≤ P₀ / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ε₁ := hBx x
      _ ≤ (P₀ + ε₁ * ((d : ℝ) * w + 1) ^ (d - 2)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := by
          rw [add_div]
          gcongr
          rw [le_div_iff₀ hY]
          nlinarith
  · -- `hB2`
    refine hBy x ?_
    by_contra hcon
    push Not at hcon
    have h1 : ((zdistD d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * ((zdistInf d (sz.L n) x : ℕ) : ℝ) := by
      exact_mod_cast zdistD_le_mul_zdistInf d (sz.L n) x
    have h2 : (d : ℝ) * ((zdistInf d (sz.L n) x : ℕ) : ℝ) ≤ (d : ℝ) * w :=
      mul_le_mul_of_nonneg_left hcon (Nat.cast_nonneg d)
    linarith

/-- **The decay of `𝔼 𝓑`** (`(eq:propcalB)`, `3_5:2139-2150`, in expectation): from the `≺` bound off an
event of probability `≤ N^{-D₁}` (`hP`) and the a.s. envelope, for every `x`
`‖𝔼𝓑_{0x}‖ ≤ P₀/(|x|+1)^{d-2} + ε₁` and, beyond the window `w = (log W)³ ℓ_s`, `‖𝔼𝓑_{0x}‖ ≤ ε₂`
(band `meanFar_n_kernel`; one fixed charge `σ`). -/
private theorem meanFarG_n_kernel [IsProbabilityMeasure μ] (n : ℕ) (hd : 3 ≤ d) {s : ℝ} (hL' : meanFarG_LEnv C n s)
    (hs : s < 1) (hg : 0 < sz.lam n) (hreg : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s)
    {τ₁ D₁ Dw Kmax : ℝ} (σ : Fin 2 → Bool)
    (hP : ∀ (a b : Zd d (sz.L n)),
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖C.L n s σ ![a, b] ω - C.K n s σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)))
    (hK : ∀ (a b : Zd d (sz.L n)), ‖C.K n s σ ![a, b]‖ ≤ Kmax) :
    (∀ x : Zd d (sz.L n), ‖meanFarG_B C μ n s σ 0 x‖ ≤
        (((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)))) /
            (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) +
          (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
            ((etaOf (C.m n) s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) ∧
    (∀ x : Zd d (sz.L n), Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) s <
        ((zdistInf d (sz.L n) x : ℕ) : ℝ) → ‖meanFarG_B C μ n s σ 0 x‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
            Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) +
          (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
            ((etaOf (C.m n) s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁))) := by
  have hL := sz.three_le_L n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hNn : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) s := ellT_pos (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  -- the general pointwise bound for `x`
  have hpt : ∀ x : Zd d (sz.L n), ‖meanFarG_B C μ n s σ 0 x‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
          Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) +
        ((etaOf (C.m n) s)⁻¹ ^ 2 + Kmax) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) := by
    intro x
    have hz : zdistInf d (sz.L n) ((0 : Zd d (sz.L n)) - x) = zdistInf d (sz.L n) x := by
      rw [zero_sub, meanFar_zdistInf_neg]
    have hP' := hP 0 x
    rw [hz] at hP'
    have hZ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ *
        (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
          Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
      have hB0 : 0 ≤ sz.Bctl n s := by
        unfold Sizes.Bctl Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]; positivity
      have hS0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) x) := by
        unfold STWB Bparam
        have : 0 < 1 - s := by linarith
        rw [abs_of_pos this]; positivity
      positivity
    have h := meanFarG_B_bound C μ n hL' σ 0 x hZ hP'
    refine h.trans ?_
    have hK' := hK 0 x
    have hDD : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := Real.rpow_nonneg hNn _
    have hη : 0 ≤ (etaOf (C.m n) s)⁻¹ ^ 2 := by positivity
    gcongr
  have hBW : ∀ x : Zd d (sz.L n), sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) ≤
      meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    fun x => meanFar_BctlSTWB sz n hd hs hg hreg _ (meanFar_zdistInf_le x)
  have hexp1 : ∀ x : Zd d (sz.L n), Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) /
      ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤ 1 := by
    intro x
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) hℓ0.le) _
  have hBW0 : ∀ x : Zd d (sz.L n), 0 ≤ sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) := by
    intro x
    have hB0 : 0 ≤ sz.Bctl n s := by
      unfold Sizes.Bctl Bparam
      have : 0 < 1 - s := by linarith
      rw [abs_of_pos this]; positivity
    have hS0 : 0 ≤ STWB sz n s (zdistInf d (sz.L n) x) := by
      unfold STWB Bparam
      have : 0 < 1 - s := by linarith
      rw [abs_of_pos this]; positivity
    positivity
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · refine (hpt x).trans ?_
    have h1 : sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
        Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
      calc _ ≤ sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) * 1 :=
            mul_le_mul_of_nonneg_left (hexp1 x) (hBW0 x)
        _ ≤ _ := by rw [mul_one]; exact hBW x
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (((sz.W n : ℕ) : ℝ) ^ (-Dw)))
      (Real.rpow_nonneg hNn τ₁)
    have e : ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) /
        (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) =
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ))) /
            (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) +
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring
    rw [e] at h2
    linarith
  · refine (hpt x).trans ?_
    -- beyond the window the exponential is `≤ exp(-(log W)^{3/2})`
    have hxℓ : Real.log ((sz.W n : ℕ) : ℝ) ^ 3 ≤
        ((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s := by
      rw [le_div_iff₀ hℓ0]; exact hx.le
    have hlw0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
    have hpow : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤
        (((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) := by
      have h1 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) ≤
          (((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (pow_nonneg hlw0 3) hxℓ (by norm_num)
      have h2 : (Real.log ((sz.W n : ℕ) : ℝ) ^ 3) ^ (1 / 2 : ℝ) = Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlw0]; norm_num
      rwa [h2] at h1
    have hexp2 : Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) :=
      Real.exp_le_exp.2 (neg_le_neg hpow)
    have h1 : sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) x) *
        Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) ≤
        meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) * Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
      have hY : 1 ≤ (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
        one_le_pow₀ (by have : (0 : ℝ) ≤ ((zdistInf d (sz.L n) x : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
      have hc0 : 0 ≤ meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) := by
        unfold meanFar_c0
        have := meanFar_c3_pos d
        have hA : 0 < STAI sz n := by unfold STAI; positivity
        positivity
      calc _ ≤ (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2)) *
              Real.exp (-(((zdistInf d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hBW x) (Real.exp_pos _).le
        _ ≤ (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ))) * Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) := by
            refine mul_le_mul ?_ hexp2 (Real.exp_pos _).le hc0
            exact div_le_self hc0 hY
    have h2 := mul_le_mul_of_nonneg_left (add_le_add_left h1 (((sz.W n : ℕ) : ℝ) ^ (-Dw)))
      (Real.rpow_nonneg hNn τ₁)
    have e : ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
          Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) =
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * (meanFar_c0 d * STAI sz n ^ (-(6 / 5 : ℝ)) *
            Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) +
          ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-Dw) := by ring
    rw [e] at h2
    linarith
/-- **`‖𝔼 f^{far}‖` at one index `n`** (band `meanFar_at_n`): every numeric fact about the size sequence is a hypothesis
(`hA1`, `h2d`, `hexp`, `hWdw`, `hP`, the pure facts about `N`); the propagator enters through `STThPropsg` conjuncts 1, 3, 5 at
`(σ, t)` (`hsh`, `h5n`, `h7n`), the kernel through `STKpropsg` (`hKinv`, `hKb`); one fixed mixed charge `σ`. -/
private theorem meanFarG_at_n [IsProbabilityMeasure μ] (n : ℕ) (hd : 3 ≤ d)
    {s t τ κ' Λ C₅ c₅ C₇ cK Dw : ℝ}
    (hLE : meanFarG_LEnv C n s) (hX : STExpInvgL C μ) (hKinv : meanFarG_KInv C n)
    (hκ'0 : 0 < κ') (hκ' : κ' ≤ (C.m n).im)
    (hs0 : 0 ≤ s) (hst : s < t) (ht : t < 1)
    (hΛ : 0 < Λ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λ)
    (hreg1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t) (hreg2 : 1 - s ≤ sz.lam n ^ 2)
    (hC₅ : 0 < C₅) (hC₇ : 0 < C₇) (hcK : 0 ≤ cK) (σ : Fin 2 → Bool) (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n))
    (hsh : ∀ x y, STThg C n (σ 0) (σ 1) t x y = STThg C n (σ 0) (σ 1) t 0 (y - x))
    (h5n : ∀ x : Zd d (sz.L n), ‖STThg C n (σ 0) (σ 1) t 0 x‖ ≤
      C₅ * Bparam d (sz.L n) (sz.lam n) t (zdistD d (sz.L n) x) *
        Real.exp (-c₅ * ((zdistD d (sz.L n) x : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) t))
    (hc₅ : 0 < c₅)
    (h7n : ∀ a r : Zd d (sz.L n),
      ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ 1 / 2 * ((zdistD d (sz.L n) a : ℕ) : ℝ) →
      ‖STThg C n (σ 0) (σ 1) t 0 (a + r) + STThg C n (σ 0) (σ 1) t 0 (a - r) -
          2 * STThg C n (σ 0) (σ 1) t 0 a‖ ≤
        C₇ * (sz.lam n ^ 2 + |1 - t|)⁻¹ * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 *
          ((((zdistD d (sz.L n) a : ℕ) : ℝ) + 1) ^ d)⁻¹)
    (hKb : ∀ a b : Zd d (sz.L n), ‖C.K n s σ ![a, b]‖ ≤ cK / STAI sz n)
    (hτ1 : τ ≤ 1)
    (hA1 : 1 ≤ STAI sz n)
    (h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hexp : Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ≤
      (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹)
    (hWdw : ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹)
    (hP : ∀ a b : Zd d (sz.L n),
      μ {ω | ((sz.size n : ℕ) : ℝ) ^ (τ / 4) *
          (sz.Bctl n s ^ (1 / 5 : ℝ) * STWB sz n s (zdistInf d (sz.L n) (a - b)) *
            Real.exp (-(((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) s) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)) <
          ‖C.L n s σ ![a, b] ω - C.K n s σ ![a, b]‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-((5 * d + 19 : ℕ) : ℝ))))
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ))
    (hN2 : 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hlogN : 1 ≤ Real.log ((sz.size n : ℕ) : ℝ))
    (hpolyN : meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) * 3 *
      Real.log ((sz.size n : ℕ) : ℝ) ^ 13 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4))
    (hM4 : 1 / κ' ^ 2 + cK ≤ ((sz.size n : ℕ) : ℝ))
    (hM5 : (3 * meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * ((d : ℝ) + 1) ^ (d + 2) +
        2 * (C₅ * meanFar_c3 d) ^ 2) * (meanFar_c0 d + 2) * Λ ^ 4 * 2 ^ (d - 2) ≤ ((sz.size n : ℕ) : ℝ)) :
    ‖∫ ω, STfFarg C n s t σ a ω ∂μ‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
  have hL := sz.three_le_L n
  have hs1 : s < 1 := hst.trans ht
  have ht0 : 0 ≤ t := hs0.trans hst.le
  have hregs : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s := hreg1.trans (by linarith)
  -- basic real quantities
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL
  have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega : 0 < sz.L n)) d
    exact_mod_cast h
  have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.L n) ^ d ≤ sz.size n :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    exact_mod_cast h
  have hLNn : ((sz.L n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (le_self_pow₀ (by linarith) (by omega : d ≠ 0)).trans hLN
  have hWNn : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (le_self_pow₀ hW1 (by omega : d ≠ 0)).trans hWN
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have hAe : STAI sz n = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := rfl
  have hg2N : 1 ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    calc (1 : ℝ) ≤ STAI sz n := hA1
      _ = sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hAe
      _ ≤ sz.lam n ^ 2 * ((sz.size n : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hWN (by positivity)
  have hAΛ : STAI sz n ≤ Λ ^ 2 * ((sz.size n : ℕ) : ℝ) := by
    rw [hAe]
    exact mul_le_mul (pow_le_pow_left₀ hg.le hgΛ 2) hWN (by positivity) (by positivity)
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) s := one_le_ellT (by linarith)
  have hℓL : ellT (sz.L n) (sz.lam n) s ≤ ((sz.L n : ℕ) : ℝ) := ellT_le_L
  have hlw3 : (6 : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hlwN : Real.log ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < ((sz.W n : ℕ) : ℝ))
    linarith
  have hlwlogN : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) :=
    Real.log_le_log (by linarith) hWNn
  -- the constants
  set c₃ : ℝ := meanFar_c3 d with hc₃
  set c₁ : ℝ := C₅ * c₃ with hc₁
  have hc₃0 : 0 < c₃ := meanFar_c3_pos d
  have hc₁0 : 0 < c₁ := by positivity
  have hc₀0 : 0 ≤ meanFar_c0 d := by unfold meanFar_c0; have := meanFar_c3_pos d; positivity
  -- the bound of `𝒦` and the kernel
  have hKbound : ∀ a' b' : Zd d (sz.L n), ‖C.K n s σ ![a', b']‖ ≤ cK := fun a' b' => (hKb a' b').trans (div_le_self hcK hA1)
  have hker := meanFarG_n_kernel C μ n hd hLE hs1 hg hregs (τ₁ := τ / 4) (D₁ := ((5 * d + 19 : ℕ) : ℝ))
    (Dw := Dw) (Kmax := cK) σ hP hKbound
  -- the propagator at the time `t`, the window and the far threshold
  have hT1 : ∀ x : Zd d (sz.L n),
      ‖STThg C n (σ 0) (σ 1) t 0 x‖ ≤
        (c₁ / sz.lam n ^ 2) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) :=
    fun x => meanFar_T1 hd hL hg ht hreg1 hC₅.le hc₅ (fun x => STThg C n (σ 0) (σ 1) t 0 x) h5n x
  set lw : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hlw
  set ℓ : ℝ := ellT (sz.L n) (sz.lam n) s with hℓ
  set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
  have hlw0 : 0 ≤ lw := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hρ0 : 0 ≤ lw ^ 4 * ℓ := by positivity
  have hwρ : 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) ≤ ((⌊lw ^ 4 * ℓ⌋₊ : ℕ) : ℝ) + 1 := by
    have h1 : 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) ≤ lw ^ 4 * ℓ := by
      calc 2 * ((d : ℝ) * (lw ^ 3 * ℓ)) = (2 * d) * (lw ^ 3 * ℓ) := by ring
        _ ≤ lw * (lw ^ 3 * ℓ) := mul_le_mul_of_nonneg_right h2d (by positivity)
        _ = lw ^ 4 * ℓ := by ring
    have h2 := Nat.lt_floor_add_one (lw ^ 4 * ℓ)
    linarith
  have hT2 : ∀ a' r : Zd d (sz.L n), ((zdistD d (sz.L n) r : ℕ) : ℝ) ≤ (d : ℝ) * (lw ^ 3 * ℓ) →
      lw ^ 4 * ℓ < ((zdistInf d (sz.L n) a' : ℕ) : ℝ) →
      ‖STThg C n (σ 0) (σ 1) t 0 (a' + r) +
          STThg C n (σ 0) (σ 1) t 0 (a' - r) -
          2 * STThg C n (σ 0) (σ 1) t 0 a'‖ ≤
        (C₇ / sz.lam n ^ 2) * ((zdistD d (sz.L n) r : ℕ) : ℝ) ^ 2 /
          (((zdistInf d (sz.L n) a' : ℕ) : ℝ) + 1) ^ d :=
    fun a' r hr ha => meanFar_T2 hg hC₇.le hρ0 hwρ
      (fun x => STThg C n (σ 0) (σ 1) t 0 x)
      (fun a r h => h7n a r h) a' r hr ha
  -- the small quantities
  have hNn0 : 0 < Nn := by linarith
  set A' : ℝ := STAI sz n ^ (-(6 / 5 : ℝ)) with hA'
  have hA'0 : 0 ≤ A' := Real.rpow_nonneg hA0.le _
  have hA'1 : A' ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  set ε₁ : ℝ := Nn ^ (τ / 4) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) +
      ((etaOf (C.m n) s)⁻¹ ^ 2 + cK) * Nn ^ (-((5 * d + 19 : ℕ) : ℝ)) with hε₁
  set ε₂ : ℝ := Nn ^ (τ / 4) * (meanFar_c0 d * A' * Real.exp (-(lw ^ (3 / 2 : ℝ)))) + ε₁ with hε₂
  have hNτ0 : 0 ≤ Nn ^ (τ / 4) := Real.rpow_nonneg hNn0.le _
  have hε₁0 : 0 ≤ ε₁ := by positivity
  have hε₂0 : 0 ≤ ε₂ := by positivity
  have hε12 : ε₁ ≤ ε₂ := by
    have : 0 ≤ Nn ^ (τ / 4) * (meanFar_c0 d * A' * Real.exp (-(lw ^ (3 / 2 : ℝ)))) := by positivity
    linarith
  have hη7 : (etaOf (C.m n) s)⁻¹ ^ 2 + cK ≤ Nn ^ 7 := by
    have h1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 * κ' ≤ etaOf (C.m n) s := by
      have : etaOf (C.m n) s = (1 - s) * (C.m n).im := rfl
      rw [this]
      exact mul_le_mul hregs hκ' hκ'0.le (by linarith)
    exact meanFar_eta_bound hN1 hg hg2N hL3 hLNn hκ'0 h1 hcK hM4
  have hD1 : Nn ^ (-((5 * d + 19 : ℕ) : ℝ)) = (Nn ^ (5 * d + 19))⁻¹ := by
    rw [Real.rpow_neg hNn0.le, Real.rpow_natCast]
  have hε₂bd : ε₂ ≤ (meanFar_c0 d + 2) * (Nn ^ (5 * d + 12))⁻¹ := by
    rw [hε₂, hε₁, hD1]
    exact meanFar_eps_bound d hN1 hτ1 hc₀0 hA'0 hA'1 (Real.exp_pos _).le hexp
      (Real.rpow_nonneg (by linarith) _) hWdw hη7
  -- logarithmic and polynomial facts
  have hLr0 : 0 ≤ ((sz.L n : ℕ) : ℝ) := by linarith
  have hLg0 : 0 ≤ Real.log (((sz.L n : ℕ) : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hLg1 : Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ 1 + Real.log Nn := by
    have h1 : ((sz.L n : ℕ) : ℝ) + 1 ≤ 2 * Nn := by linarith
    calc Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ Real.log (2 * Nn) := Real.log_le_log (by linarith) h1
      _ = Real.log 2 + Real.log Nn := Real.log_mul (by norm_num) hNn0.ne'
      _ ≤ 1 + Real.log Nn := by have := Real.log_two_lt_d9; linarith
  have hlogNN : Real.log Nn ≤ Nn := by
    have := Real.log_le_sub_one_of_pos hNn0
    linarith
  have hLg' : 1 + Real.log (((sz.L n : ℕ) : ℝ) + 1) ≤ 3 * Nn := by linarith
  have hpoly : meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) *
      (lw ^ 12 * (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1))) ≤ Nn ^ (τ / 4) := by
    have h1 : lw ^ 12 * (1 + Real.log (((sz.L n : ℕ) : ℝ) + 1)) ≤ 3 * Real.log Nn ^ 13 := by
      have : lw ^ 12 ≤ Real.log Nn ^ 12 := pow_le_pow_left₀ hlw0 hlwlogN 12
      calc _ ≤ Real.log Nn ^ 12 * (3 * Real.log Nn) :=
            mul_le_mul this (by linarith) (by linarith) (by positivity)
        _ = 3 * Real.log Nn ^ 13 := by ring
    have hCd0 := meanFar_Cd_nonneg d
    calc _ ≤ (meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4)) * (3 * Real.log Nn ^ 13) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = meanFar_Cd d * c₁ * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4) * 3 * Real.log Nn ^ 13 := by ring
      _ ≤ _ := hpolyN
  have hDn0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDnN : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ Nn := by
    have : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast meanFar_zdistInf_le _
    linarith
  have hlw1 : 1 ≤ lw := by linarith
  have htiny := meanFar_tiny d hd (Nn := Nn) (g := sz.lam n) (ℓ := ℓ) (lw := lw) (A := STAI sz n)
    (Dn := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (Lr := ((sz.L n : ℕ) : ℝ))
    (Lg := Real.log (((sz.L n : ℕ) : ℝ) + 1)) (Λ := Λ) (c₀ := meanFar_c0 d) (c₁ := c₁) (c₂ := C₇)
    (ε₂ := ε₂) hN1 hg2N hA1 hAΛ hΛ hℓ1 hℓL hLNn hLN hlw1 hlwN hDn0 hDnN hLg0 hLg' hc₀0 hc₁0.le hC₇.le
    hε₂0 hε₂bd hM5
  have hass := meanFarG_assemble C μ n hd hLE hs0 hs1 hX hKinv σ hσ a hsh (lw ^ 3 * ℓ) (c₁ / sz.lam n ^ 2)
    (C₇ / sz.lam n ^ 2) (Nn ^ (τ / 4) * (meanFar_c0 d * A')) ε₁ ε₂ (by positivity) (by positivity)
    hε₁0 hε₂0 hT1 hT2 hker.1 hker.2
  refine hass.trans ?_
  have hreg' : (1 - s) ^ 2 * ℓ ^ 4 ≤ sz.lam n ^ 4 := by
    have h := meanFar_ell_sq (L := sz.L n) hg hs1 hreg2
    have h0 : 0 ≤ (1 - s) * ℓ ^ 2 := by
      have : 0 < 1 - s := by linarith
      positivity
    calc (1 - s) ^ 2 * ℓ ^ 4 = ((1 - s) * ℓ ^ 2) ^ 2 := by ring
      _ ≤ (sz.lam n ^ 2) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = sz.lam n ^ 4 := by ring
  have hmain := meanFar_numeric_main d hd (τ := τ) (Nn := Nn) (g := sz.lam n) (ℓ := ℓ) (lw := lw)
    (s := s) (Dn := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (A := STAI sz n)
    (Lr := ((sz.L n : ℕ) : ℝ)) (Lg := Real.log (((sz.L n : ℕ) : ℝ) + 1)) (c₀ := meanFar_c0 d)
    (c₁ := c₁) (c₂ := C₇) (ε₁ := ε₁) (ε₂ := ε₂) hN2 hN1 hg hℓ1 hlw1 hs0 hs1.le hDn0 hA0 hLg0
    hc₀0 hc₁0.le hC₇.le hε₁0 hε12 hreg' hpoly htiny
  refine hmain.trans ?_
  have hpa : ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 ≤
      (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + 1) ^ (d - 2) := by
    have := pow_add_pow_le hDn0 (zero_le_one' ℝ) (n := d - 2) (by omega)
    simpa using this
  have hposD : 0 < ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1 := by positivity
  have hNτ : 0 ≤ Nn ^ τ := Real.rpow_nonneg hNn0.le _
  refine mul_le_mul_of_nonneg_left ?_ hNτ
  exact div_le_div_of_nonneg_left hA'0 hposD hpa
end Expect

/-! ## 2. The eventual statement (target 4) -/

section Eventually

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **Target 4: the mean part of `f^{far}`, eventually in `n`** (`(eq:boundEfar)`, `3_5:2192-2212`; band `meanFar_eventually`,
`MeanFar:1980`): for every `τ > 0`, eventually in `n`, for every mixed charge `σ` and `a`,
`‖𝔼 f^{far}_{σ,a}‖ ≤ N^τ (g² W^d)^{-6/5} / (|a₁-a₂|^{d-2} + 1)`.  Premises: the admissibility, `κ ≤ Im (C.m n)`,
`0 ≤ s < t < 1`, `CltRepg` and `STGdecayWgL` (of `HCltOf`), `STReg5I`, and the three pins `STThPropsg`, `STKpropsg`,
`STExpInvgL`; the energy enters only through `κ ≤ Im (C.m n)` (X1-C1). -/
theorem meanFar_eventuallyg {H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} {g' E : ℕ → ℝ}
    {κ 𝔠 𝔡 Cd : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hAdm : sz.Admissible 𝔠 𝔡) (hm : ∀ n, κ ≤ (C.m n).im)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n < 1)
    (hrep : CltRepg C μ H₀ g' E) (hreg : STReg5I sz s t) (hG : STGdecayWgL C μ s t Cd)
    (hTh : STThPropsg C) (hKp : STKpropsg C s) (hX : STExpInvgL C μ) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      ‖∫ ω, STfFarg C n (s n) (t n) σ a ω ∂μ‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
  have : IsProbabilityMeasure μ := by rw [hrep.1]; exact Sizes.isProbabilityMeasure_seqP (sz.withLam g')
  obtain ⟨h𝔠, h𝔡, hSz, hBw, hWO⟩ := hAdm
  -- reduce to `τ ≤ 1`
  obtain ⟨τ', hτ'0, hτ'1, hτ'⟩ : ∃ τ' : ℝ, 0 < τ' ∧ τ' ≤ 1 ∧ τ' ≤ τ :=
    ⟨min τ 1, lt_min hτ one_pos, min_le_right _ _, min_le_left _ _⟩
  set Λ : ℝ := 𝔡⁻¹ with hΛdef
  have hΛ : 0 < Λ := inv_pos.2 h𝔡
  obtain ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, H⟩ := hTh
  obtain ⟨hKinv, cK, hcK, hKb⟩ := hKp
  set Dw : ℝ := ((5 * d + 13 : ℕ) : ℝ) / 𝔠 with hDw
  have hDw0 : 0 < Dw := by positivity
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans (ht n)
  have hbad := meanFarG_bad_le C μ hs1 (fun n => (hst n).le) hG hDw0 (τ := τ' / 4)
    (D₁ := ((5 * d + 19 : ℕ) : ℝ)) (by positivity) (by positivity)
  have hpure := meanFar_pureN (τ := τ') (𝔠 := 𝔠) hτ'0 h𝔠
    (meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * meanFar_c0 d * (16 * (d : ℝ) ^ 4))
    (1 / κ ^ 2 + cK)
    ((3 * meanFar_Cd d * (C₅ * meanFar_c3 d) * C₇ * ((d : ℝ) + 1) ^ (d + 2) +
        2 * (C₅ * meanFar_c3 d) ^ 2) * (meanFar_c0 d + 2) * Λ ^ 4 * 2 ^ (d - 2))
    (max (2 * (d : ℝ)) ((((5 * d + 13 : ℕ) : ℝ) / 𝔠) ^ 2))
  have hpure' := hSz.eventually hpure
  filter_upwards [hWO, hBw, hbad, hpure', H, hKb] with n hWOn hBwn hbadn hpn hHn hKbn
  obtain ⟨hN1, hN2, hlogN, hpolyN, hM4, hM5, hM6⟩ := hpn
  have hL := sz.three_le_L n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨hWO1, hWO2⟩ := hWOn
  have hg : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hWO1
  have hA1 : 1 ≤ STAI sz n :=
    le_trans (Real.one_le_rpow hW1 (by positivity)) (sz.lam_sq_mul_pow_ge n hWO1)
  -- the logarithmic lower bound `log W ≥ 𝔠 log N`
  have hlw𝔠 : 𝔠 * Real.log ((sz.size n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hN0 𝔠) hBwn
    rwa [Real.log_rpow hN0] at this
  have hM6' : max (2 * (d : ℝ)) ((((5 * d + 13 : ℕ) : ℝ) / 𝔠) ^ 2) ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    hM6.trans hlw𝔠
  have h2d : 2 * (d : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hM6'
  have hexp : Real.exp (-(Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))) ≤
      (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
    rw [meanFar_inv_pow_eq hN0]
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hB : 0 < (((5 * d + 13 : ℕ) : ℝ) / 𝔠) := by positivity
    have h3 := meanFar_three_halves hB ((le_max_right _ _).trans hM6')
    calc ((5 * d + 13 : ℕ) : ℝ) * Real.log ((sz.size n : ℕ) : ℝ)
        = (((5 * d + 13 : ℕ) : ℝ) / 𝔠) * (𝔠 * Real.log ((sz.size n : ℕ) : ℝ)) := by field_simp
      _ ≤ (((5 * d + 13 : ℕ) : ℝ) / 𝔠) * Real.log ((sz.W n : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hlw𝔠 hB.le
      _ ≤ _ := h3
  have hWdw : ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
    calc ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-Dw) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hN0 𝔠) hBwn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (-Dw)) := (Real.rpow_mul hN0.le _ _).symm
      _ = ((sz.size n : ℕ) : ℝ) ^ (-((5 * d + 13 : ℕ) : ℝ)) := by
          congr 1; rw [hDw]; field_simp
      _ = (((sz.size n : ℕ) : ℝ) ^ (5 * d + 13))⁻¹ := by
          rw [Real.rpow_neg hN0.le, Real.rpow_natCast]
  intro σ hσ a
  obtain ⟨hsh, -, h5n, -, h7n⟩ := hHn (t n) ((hs0 n).trans (hst n).le) (ht n) σ hσ
  have hmain := meanFarG_at_n C μ n hd (s := s n) (t := t n) (τ := τ') (κ' := κ) (Λ := Λ)
    (C₅ := C₅) (c₅ := c₅) (C₇ := C₇) (cK := cK) (Dw := Dw) (meanFarG_lenv_of_rep C μ hrep hκ n (hm n) (hs1 n)) hX
    (hKinv n) hκ (hm n) (hs0 n) (hst n) (ht n) hΛ hg hWO2 (hreg n).1 (hreg n).2 hC₅ hC₇ hcK.le σ hσ a hsh h5n hc₅ h7n
    (hKbn σ hσ) hτ'1 hA1 h2d hexp hWdw (hbadn σ) hN1 hN2 hlogN hpolyN hM4 hM5
  refine hmain.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hτ') ?_)
  have hA0 : 0 < STAI sz n := lt_of_lt_of_le one_pos hA1
  have : 0 ≤ STAI sz n ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg hA0.le _
  positivity

end Eventually

/-! ## 3. Compiled nonempty instance (`d = 3`, band data of `Step5Inst`: `szCL`, `bandFM szCL (STflowE zCL)`, `seqP szCL`, `sCL`, `tCL`)

Every deterministic premise is discharged: the admissibility `(1/6, 1/10)`, `κ = 1/2 ≤ Im m`, `0 ≤ sCL < tCL < 1`, `CltRepg`
(`cltRepg_band`), `STReg5I` (`szCL_reg5I`), `STExpInvgL` (`stExpInvgL_band`), and the band producers `STThPropsg`, `STKpropsg` by the
private `meanFarG_chk_Th`, `meanFarG_chk_K` (the statements of the second row's targets 7a, 7b, proved here for the instance only).  The
one hypothesis of the example is the Step 2 pin `STGdecayWgL` (another gate). -/

section Instances

open RBM.Gauss.Step5Inst

/-- The band producer of `STThPropsg` (the statement of the second row's target 7a), proved here for the instance only (private). -/
private theorem meanFarG_chk_Th {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E : ℕ → ℝ) (hd : 3 ≤ d) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) : STThPropsg (bandFM sz E) := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hκ'0 : 0 < min κ (1 / 2) := lt_min hκ (by norm_num)
  obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd hΛ
  obtain ⟨C₆, hC₆, H6⟩ := prop6Diff1_holds d 𝔡⁻¹ (min κ (1 / 2)) (1 / 2) hd hΛ hκ'0 (by norm_num) (by norm_num)
  obtain ⟨C₇, hC₇, H7⟩ := prop7Diff2_holds d 𝔡⁻¹ (min κ (1 / 2)) (1 / 2) hd hΛ hκ'0 (by norm_num) (by norm_num)
  refine ⟨C₅, c₅, C₆, C₇, hC₅, hc₅, hC₆, hC₇, ?_⟩
  filter_upwards [hWO] with n hWOn t ht0 ht1 σ hσ
  obtain ⟨hWO1, hWO2⟩ := hWOn
  have hL := sz.three_le_L n
  have hg : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hWO1
  have hEn : |E n| < 2 := by have := hE n; linarith
  have hκ' : min κ (1 / 2) ≤ (mE (E n)).im := by
    rw [mE_im]
    have hE2 : (E n) ^ 2 ≤ (2 - min κ (1 / 2)) ^ 2 := by
      have h1 := abs_le.1 (hE n)
      have h2 : min κ (1 / 2) ≤ κ := min_le_left _ _
      exact sq_le_sq' (by linarith [h1.1]) (by linarith [h1.2])
    have hκ'1 : min κ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have h4 : (2 * min κ (1 / 2)) ^ 2 ≤ 4 - (E n) ^ 2 := by nlinarith
    have h5 : 2 * min κ (1 / 2) ≤ Real.sqrt (4 - (E n) ^ 2) := by
      calc 2 * min κ (1 / 2) = Real.sqrt ((2 * min κ (1 / 2)) ^ 2) := (Real.sqrt_sq (by linarith)).symm
        _ ≤ _ := Real.sqrt_le_sqrt h4
    linarith
  have hm : ‖mE (E n)‖ = 1 := norm_mE hEn.le
  have hξ := norm_mul_mSigma_lt_one hEn.le ht0 ht1 (σ 0) (σ 1)
  have hΘ : ∀ x y, STThg (bandFM sz E) n (σ 0) (σ 1) t x y =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) x y :=
    fun x y => congr_fun (congr_fun (bandFM_STThg sz E n (σ 0) (σ 1) t) x) y
  have hsh : ∀ x y : Zd d (sz.L n), Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) x y =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 (y - x) := fun x y => by
    have := Theta_apply_add_right_of_three_le (d := d) (g := sz.lam n) hL hξ 0 (y - x) x
    rwa [zero_add, sub_add_cancel] at this
  have hT := fun x y => congr_fun (congr_fun (Theta_transpose_of_three_le (d := d) (L := sz.L n) (g := sz.lam n) hL hξ) x) y
  simp only [hΘ]
  refine ⟨hsh, fun x y => (hT x y).symm, ?_, ?_, ?_⟩
  · exact fun a => H5 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm (σ 0) (σ 1) a
  · exact fun a r h => H6 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm hκ' (σ 0) (σ 1) a r h
  · exact fun a r h => H7 (sz.L n) hL (sz.lam n) hg hWO2 t ht0 ht1 (mE (E n)) hm hκ' (σ 0) (σ 1) a r h

/-- The band producer of `STKpropsg` (the statement of the second row's target 7b: invariance by `KLK_two` and the `Θ` shift and
symmetry, `‖𝒦‖ ≤ c₁/A` by `meanFar_T1`, `meanFar_n_K`), proved here for the instance only (private; probe `bandFM_KInv`,
`T2455Meas:373`). -/
private theorem meanFarG_chk_K {d : ℕ} (sz : Sizes d) (κ 𝔡 : ℝ) (E s t : ℕ → ℝ) (hd : 3 ≤ d) (h𝔡 : 0 < 𝔡)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ) (hκ : 0 < κ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht : ∀ n, t n < 1) (hreg : STReg5I sz s t) : STKpropsg (bandFM sz E) s := by
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  refine ⟨fun n t' ht0 ht1 σ hσ a c => ?_, ?_⟩
  · have hL := sz.three_le_L n
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hξ := norm_mul_mSigma_lt_one hEn.le ht0 ht1 (σ 0) (σ 1)
    have hK : ∀ b : Fin 2 → Zd d (sz.L n), (bandFM sz E).K n t' σ b = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        (mSigma (E n) (σ 0) * mSigma (E n) (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((t' : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) (b 0) (b 1) := fun b => by
      change STKloop sz n (E n) t' σ b = _
      unfold STKloop
      have h : KLloopOf d (sz.L n) σ b = ⟨[σ 0, σ 1], [b 0, b 1]⟩ := by simp [KLloopOf, List.ofFn_succ]
      rw [h, KLK_two]
    have hs : ∀ x y : Zd d (sz.L n), Theta d (sz.L n) (sz.lam n) ((t' : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) x y =
        Theta d (sz.L n) (sz.lam n) ((t' : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 (y - x) := fun x y => by
      have := Theta_apply_add_right_of_three_le (d := d) (g := sz.lam n) hL hξ 0 (y - x) x
      rwa [zero_add, sub_add_cancel] at this
    have hT := fun x y => congr_fun (congr_fun (Theta_transpose_of_three_le (d := d) (L := sz.L n) (g := sz.lam n) hL hξ) x) y
    refine ⟨?_, ?_⟩
    · rw [hK, hK]; simp only [hs (a 0 + c), hs (a 0), add_sub_add_right_eq_sub]
    · rw [hK, hK]; simp only [hs (-a 0), neg_sub_neg]; rw [← hs (a 1) (a 0)]; exact congrArg _ (hT (a 0) (a 1))
  · obtain ⟨C₅, hC₅, c₅, hc₅, H5⟩ := prop5Decay_holds d 𝔡⁻¹ hd hΛ
    refine ⟨C₅ * (1 + 2 ^ (d - 1)), by positivity, ?_⟩
    filter_upwards [hWO] with n hWOn σ hσ a b
    obtain ⟨hWO1, hWO2⟩ := hWOn
    have hL := sz.three_le_L n
    have hg : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hWO1
    have hEn : |E n| < 2 := by have := hE n; linarith
    have hs1 : s n < 1 := (hst n).trans_lt (ht n)
    have hreg1 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - s n := (hreg n).1.trans (by linarith [hst n])
    have hm : ‖mE (E n)‖ = 1 := norm_mE hEn.le
    have hT1 : ∀ x : Zd d (sz.L n), ‖Theta d (sz.L n) (sz.lam n) ((s n : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 x‖ ≤
        (C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) / (((zdistInf d (sz.L n) x : ℕ) : ℝ) + 1) ^ (d - 2) := fun x =>
      meanFar_T1 hd hL hg hs1 hreg1 hC₅.le hc₅
        (fun x => Theta d (sz.L n) (sz.lam n) ((s n : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 x)
        (fun x => H5 (sz.L n) hL (sz.lam n) hg hWO2 (s n) (hs0 n) hs1 (mE (E n)) hm (σ 0) (σ 1) x) x
    have hTs : ∀ x : Zd d (sz.L n), ‖Theta d (sz.L n) (sz.lam n) ((s n : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 x‖ ≤
        C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2 := fun x =>
      meanFar_T_le (fun x => Theta d (sz.L n) (sz.lam n) ((s n : ℂ) * (mSigma (E n) (σ 0) * mSigma (E n) (σ 1))) 0 x) hT1 x
    refine (meanFar_n_K sz n hEn (hs0 n) hs1 σ a b hTs).trans (le_of_eq ?_)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by have := sz.W_pos n; positivity
    change (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C₅ * (1 + 2 ^ (d - 1)) / sz.lam n ^ 2) =
      C₅ * (1 + 2 ^ (d - 1)) / (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    field_simp

private theorem meanFarG_chk_m (n : ℕ) : 1 / 2 ≤ ((bandFM szCL (STflowE zCL)).m n).im := by
  have hL := szCL_two_le_L n
  have hL0 : 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  have hz : 0 < (zCL n).im := by
    change 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2; positivity
  have hE : |STflowE zCL n| ≤ 1 / 2 := (abs_lemE_le hz).trans (by simp [zCL])
  change 1 / 2 ≤ (mE (STflowE zCL n)).im
  rw [mE_im]
  have h1 : (1 : ℝ) ≤ Real.sqrt (4 - STflowE zCL n ^ 2) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith [abs_le.1 hE])
  linarith

private theorem meanFarG_chk_t1 (n : ℕ) : tCL n < 1 := by
  have hL := szCL_two_le_L n
  change 1 - (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ < 1
  have : 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  linarith

private theorem meanFarG_chk_E (n : ℕ) : |STflowE zCL n| ≤ 2 - 1 / 2 := by
  have hz : 0 < (zCL n).im := by
    have := szCL_two_le_L n
    change 0 < (((szCL.L n : ℕ) : ℝ) ^ 2)⁻¹ / 2
    positivity
  exact (abs_lemE_le hz).trans (by simp [zCL]; norm_num)

/-- Target 4 at the band data (`κ = 1/2`, `τ = 1/2`); `STThPropsg`, `STKpropsg` are the private band producers above. -/
example (hG : STGdecayWgL (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) sCL tCL 1) :
    ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd 3 (szCL.L n),
      ‖∫ ω, STfFarg (bandFM szCL (STflowE zCL)) n (sCL n) (tCL n) σ a ω ∂(Sizes.seqP szCL)‖ ≤
        ((szCL.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
          (STAI szCL n ^ (-(6 / 5 : ℝ)) / (((zdistInf 3 (szCL.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (3 - 2) + 1)) :=
  meanFar_eventuallyg (bandFM szCL (STflowE zCL)) (Sizes.seqP szCL) (g' := szCL.lam) (E := STflowE zCL)
    (H₀ := fun _ => 0) (κ := 1 / 2) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (Cd := 1) (by norm_num) (by norm_num)
    szCL_admissible meanFarG_chk_m sCL tCL (fun _ => le_rfl) szCL_hst meanFarG_chk_t1 (cltRepg_band szCL _)
    szCL_reg5I hG
    (meanFarG_chk_Th szCL (1 / 2) (1 / 10) (STflowE zCL) (by norm_num) (by norm_num) (by norm_num) szCL_WO meanFarG_chk_E)
    (meanFarG_chk_K szCL (1 / 2) (1 / 10) (STflowE zCL) sCL tCL (by norm_num) (by norm_num) szCL_WO meanFarG_chk_E
      (by norm_num) (fun _ => le_rfl) (fun n => (szCL_hst n).le) meanFarG_chk_t1 szCL_reg5I)
    (stExpInvgL_band szCL _) (1 / 2) (by norm_num)

/-- The proposal of the ticket's check file (`T2479_MeanFarg`: the five pin premises `HCltOf`, `STReg5I`, `STThPropsg`,
`STKpropsg`, `STExpInvgL`) follows from `meanFar_eventuallyg`: the premises used are fields of `HCltOf`. -/
example {d : ℕ} (κ δ 𝔠 𝔡 Cd : ℝ) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s t : ℕ → ℝ) :
    HCltOf C μ H₀ g' E κ δ 𝔠 𝔡 Cd s t → STReg5I sz s t → STThPropsg C → STKpropsg C s → STExpInvgL C μ →
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ a : Fin 2 → Zd d (sz.L n),
      ‖∫ ω, STfFarg C n (s n) (t n) σ a ω ∂μ‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (STAI sz n ^ (-(6 / 5 : ℝ)) / (((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (d - 2) + 1)) := by
  intro hH hreg hTh hKp hX τ hτ
  obtain ⟨hd, hκ, -, -, hAdm, hm, hs0, hst, ht1, -, hrep, -, -, -, hG, -, -⟩ := hH
  exact meanFar_eventuallyg C μ hd hκ hAdm hm s t hs0 hst ht1 hrep hreg hG hTh hKp hX τ hτ

#print axioms meanFarG_lenv_of_rep
#print axioms meanFar_eventuallyg

end Instances

end RBM.BA
