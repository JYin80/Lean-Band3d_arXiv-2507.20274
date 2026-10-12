/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Induction.Step5Kernel

/-!
# The kernel facts of Step 5 over the carrier (T2462, U4s1b)

Additive restatement of the kernel facts of `Induction/Step5Kernel.lean` (not edited) for the one
kernel `Step2Gen_uKer`, `Step2Gen_thetaKer`, `Step2Gen_UN` of `Chain/Step2Gen.lean` over a carrier
`C : FlowFM sz` (supervisor 1152 U-C4: no kernel and no propagator is defined here).  Paper:
arXiv:2507.20274, `(eq:decompU)` is `3_5:1983`, `(uwp2-92kj)` is `3_5:2048-2053`, and
`(prop:ThfadC)` is Proposition 5.

* **Target 8.** `Step5KerGen_uKer_eq` and `Step5KerGen_UN_decomp`:
  `uKer_{s,t} = 1 + (t - s) thetaKer_t` (the form `(eq:decompUalt)`,
  `A_deterministic_estimates.tex:100`), from the semigroup law `Step2Gen_USemigroup` at the single
  fact `uKer_{t,t} = 1`.
* **Target 9.** `Step5KerGen_ThDecay` (decay and row sum of `thetaKer` for every charge pair, read
  at the kernel coupling `gK`), its band result `step5KerGen_thDecay_band` (`gK = sz.lam`) and
  `step5KerGen_profile_holds` (`(uwp2-92kj)` for the carrier kernel).  UBA-C1: the profile and the
  windows are read at `sz.lam`, the decay at `gK`, and the one comparison hypothesis (Amend 1, R1)
  crosses once, in `step5KerGen_profile_holds`, through `Step5KerGen_tailT_cross`.
* **Target 11.** `stTailtoTailgL'_holds_band`: the band instance of `STTailtoTailgL'` (no generic
  proof; U5).

Private helpers of `Induction/Step5Kernel.lean` are reached by `open private`.  The model-free
helpers of `Induction/NewKLKL.lean` and `Induction/B45.lean` that lie outside the imports of this
file are copied under the stem `Step5KerGen_`: `newKLKL_tailT_shift`,
`newKLKL_zdistInf_{add_le,tri}`, `newKLKL_SB_support`, `B45_row_thetaKer` (RBM3D, no RBM1D or RBM2D
text).
-/

set_option linter.style.longLine false

open private step5Ker_tailW_eq step5Ker_zdistInf_sub_comm from RBM3D.Induction.Step5Kernel

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 8: the decomposition `uKer_{s,t} = 1 + (t - s) thetaKer_t` -/

section Decomp

variable {d : ℕ} {sz : Sizes d}

/-- **Target 8** (`(eq:decompUalt)`, `A_deterministic_estimates.tex:100`; band `step5Kernel_decompU`, `Step5Kernel:57`):
under the semigroup law, `uKer_{s,t} = 1 + (t - s) thetaKer_t`.  Only `uKer_{t,t} = 1` is used:
`(1 - sX) Θ_t = (1 - tX) Θ_t + (t - s) X Θ_t = 1 + (t - s) thetaKer_t`. -/
theorem Step5KerGen_uKer_eq (C : FlowFM sz) (n : ℕ) :
    Step2Gen_USemigroup C n → ∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 →
      Step2Gen_uKer C n σ σ' s t = 1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n σ σ' t := by
  intro hU σ σ' s t ht0 ht1
  have h1 : Step2Gen_uKer C n σ σ' t t = 1 := (hU σ σ' t t t ht0 ht1 ht0 ht1).1
  unfold Step2Gen_uKer Step2Gen_thetaKer at *
  have e : (1 - (s : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) =
      (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) +
        ((t - s : ℝ) : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n) := by
    push_cast; module
  rw [e, add_mul, h1, smul_mul_assoc]

/-- **Target 8, inside `UN`** (band `step5Kernel_UN_decompU`, `Step5Kernel:74`): every index factor of
`Step2Gen_UN C n σ s t` is `1 + (t - s) thetaKer_t` at the charge pair `(σ_i, σ_{i+1})`. -/
theorem Step5KerGen_UN_decomp (C : FlowFM sz) (n : ℕ) :
    Step2Gen_USemigroup C n → ∀ {k : ℕ} (σ : Fin k → Bool) (s t : ℝ), 0 ≤ t → t < 1 →
      ∀ (A : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)),
        Step2Gen_UN C n σ s t A a =
          ∑ b : Fin k → Zd d (sz.L n),
            (∏ i, (1 + ((t - s : ℝ) : ℂ) • Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t) (a i) (b i)) * A b := by
  intro hU k σ s t ht0 ht1 A a
  unfold Step2Gen_UN
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Step5KerGen_uKer_eq C n hU _ _ s t ht0 ht1]

end Decomp

/-! ## 2. Copies of model-free helpers (outside the imports of this file) -/

section Helpers

variable {d L : ℕ} {g t : ℝ}

/-- **Shift** (copy of `newKLKL_tailT_shift`, `Induction/NewKLKL.lean:56`): `𝒯_t(r') ≤ 2^{d-2} e 𝒯_t(r)` whenever
`0 ≤ r`, `0 ≤ r'`, `r ≤ r' + 1`. -/
private theorem Step5KerGen_tailT_shift (hL : 1 ≤ (L : ℝ)) {r r' : ℝ} (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (h : r ≤ r' + 1) :
    tailT d L g t r' ≤ (2 ^ (d - 2) * Real.exp 1) * tailT d L g t r := by
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL
  have hℓ : 0 < ellT L g t := lt_of_lt_of_le one_pos hℓ1
  have h2 : (1 : ℝ) ≤ 2 ^ (d - 2) := one_le_pow₀ (by norm_num)
  have hB : BparamR d L g t r' ≤ 2 ^ (d - 2) * BparamR d L g t r := by
    unfold BparamR
    have hA : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.mpr (by positivity)
    have hp : (r + 1) ^ (d - 2) ≤ 2 ^ (d - 2) * (r' + 1) ^ (d - 2) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hq : ((r' + 1) ^ (d - 2))⁻¹ ≤ 2 ^ (d - 2) * ((r + 1) ^ (d - 2))⁻¹ := by
      have hrp : 0 < (r + 1) ^ (d - 2) := pow_pos (by linarith) _
      have hrp' : 0 < (r' + 1) ^ (d - 2) := pow_pos (by linarith) _
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hrp' hrp]
      linarith
    have h3 := mul_le_mul_of_nonneg_left hq hA
    nlinarith [mul_nonneg hA (inv_nonneg.mpr (pow_pos (by linarith : (0 : ℝ) < r + 1) (d - 2)).le)]
  have hsq : Real.sqrt (r / ellT L g t) ≤ Real.sqrt (r' / ellT L g t) + 1 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    have h0 : 0 ≤ r' / ellT L g t := div_nonneg hr' hℓ.le
    have hr1 : r / ellT L g t ≤ r' / ellT L g t + 1 := by
      rw [div_le_iff₀ hℓ, add_mul, div_mul_cancel₀ _ hℓ.ne']
      nlinarith
    nlinarith [Real.sq_sqrt h0, Real.sqrt_nonneg (r' / ellT L g t)]
  have hE : Real.exp (-Real.sqrt (r' / ellT L g t)) ≤
      Real.exp 1 * Real.exp (-Real.sqrt (r / ellT L g t)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  unfold tailT
  calc BparamR d L g t r' * Real.exp (-Real.sqrt (r' / ellT L g t))
      ≤ (2 ^ (d - 2) * BparamR d L g t r) * (Real.exp 1 * Real.exp (-Real.sqrt (r / ellT L g t))) :=
        mul_le_mul hB hE (Real.exp_pos _).le (by
          have := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hr
          positivity)
    _ = _ := by ring

open scoped Matrix.Norms.Operator

variable [NeZero L]

/-- Triangle inequality `|a - c|_∞ ≤ |a - b|_∞ + |b - c|_∞` (copy of `newKLKL_zdistInf_add_le`, `_tri`,
`Induction/NewKLKL.lean:127-141`). -/
private theorem Step5KerGen_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have h : zdistInf d L ((a - b) + (b - c)) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
    unfold zdistInf
    refine Finset.sup_le fun i _ => ?_
    calc zdist L (((a - b) + (b - c)) i) = zdist L ((a - b) i + (b - c) i) := rfl
      _ ≤ zdist L ((a - b) i) + zdist L ((b - c) i) := zdist_add_le L _ _
      _ ≤ _ := Nat.add_le_add
          (Finset.le_sup (f := fun j => zdist L ((a - b) j)) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => zdist L ((b - c) j)) (Finset.mem_univ i))
  rwa [sub_add_sub_cancel] at h

omit [NeZero L] in
/-- The support of `S^{(B)}` (copy of `newKLKL_SB_support`, `Induction/NewKLKL.lean:145`). -/
private theorem Step5KerGen_SB_support (g : ℝ) {a b : Zd d L} (h : SB d L g a b ≠ 0) :
    zdistInf d L (a - b) ≤ 1 := by
  rw [SB_apply] at h
  by_cases h0 : a - b = 0
  · rw [h0]
    simp [zdistInf, zdist]
  · by_cases h1 : zdistD d L (a - b) = 1
    · exact (zdistInf_le_zdistD d L _).trans h1.le
    · exact absurd (by simp [sbKernel, h0, h1]) h

/-- Row sums of the band one-index kernel (copy of `B45_row_thetaKer`, `Induction/B45.lean:656`):
`Σ_c |thetaKer μ t (x,c)| ≤ (1-t)⁻¹` for `|μ| = 1`. -/
private theorem Step5KerGen_row_thetaKer (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (x : Zd d L) :
    ∑ c : Zd d L, ‖thetaKer d L g μ t x c‖ ≤ (1 - t)⁻¹ := by
  refine (sum_norm_row_le (thetaKer d L g μ t) x).trans ?_
  unfold thetaKer
  calc ‖(μ • SB d L g) * Theta d L g ((t : ℂ) * μ)‖
      ≤ ‖μ • SB d L g‖ * ‖Theta d L g ((t : ℂ) * μ)‖ := norm_mul_le _ _
    _ ≤ (‖μ‖ * ‖SB d L g‖) * (1 - t)⁻¹ := by
        gcongr
        · exact norm_smul_le _ _
        · exact norm_Theta_le (g := g) hL ht0 ht1 hμ
    _ = (1 - t)⁻¹ := by rw [hμ, norm_SB d L g hL]; ring

end Helpers

/-! ## 3. Target 9: decay and profile of the carrier kernel `thetaKer` -/

section Decay

/-- **Target 9, the decay** (D2 default; band `step5Kernel_theta_decay`, `Step5Kernel:135`): for every charge pair `(σ, σ')`
and `0 ≤ t < 1`, at an index `n` with `0 < gK n ≤ Λ`, the entries of the carrier kernel `thetaKer` are bounded by
`C₆ 𝒯_t(|b - a|_∞)` read at the kernel coupling `gK n`, and its row sums by `C₆/(1 - t)`.  Band: `gK = sz.lam`
(`step5KerGen_thDecay_band`). -/
def Step5KerGen_ThDecay {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (Λ C₆ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < gK n → gK n ≤ Λ → ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
    (∀ a b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤
        C₆ * tailT d (sz.L n) (gK n) t ((zdistInf d (sz.L n) (b - a) : ℕ) : ℝ)) ∧
      ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t)

/-- The band decay for the one-index kernel `thetaKer μ t = μ S Θ_{tμ}` with `‖μ‖ = 1`: `|θ(a,b)| ≤ C 𝒯_t(|b - a|_∞)`.
`θ(a,b) = Σ_z μ S(a,z) Θ_{tμ}(z,b)`, `|a - z|_∞ ≤ 1` on the support of `S`, the decay of `Θ`
(`step5Kernel_theta_decay`, `‖Θ_{tμ}‖ ≤ ‖Θ_t‖`) and the shift of `𝒯` by one lattice step. -/
private theorem Step5KerGen_theta_decay_band (d : ℕ) (Λ : ℝ) (hd : 3 ≤ d) (hΛ : 0 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g t : ℝ, 0 < g → g ≤ Λ → 0 ≤ t → t < 1 →
      ∀ μ : ℂ, ‖μ‖ = 1 → ∀ a b : Zd d L,
        ‖thetaKer d L g μ t a b‖ ≤ C * tailT d L g t ((zdistInf d L (b - a) : ℕ) : ℝ) := by
  obtain ⟨C₁, hC₁, H1⟩ := step5Kernel_theta_decay d Λ hd hΛ
  refine ⟨C₁ * (2 ^ (d - 2) * Real.exp 1), by positivity, ?_⟩
  intro L _ hL g t hg hgΛ ht0 ht1 μ hμ a b
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hsum : thetaKer d L g μ t a b =
      ∑ z : Zd d L, μ * SB d L g a z * Theta d L g ((t : ℂ) * μ) z b := by
    unfold thetaKer
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun z _ => by rw [Matrix.smul_apply, smul_eq_mul]
  rw [hsum]
  refine (norm_sum_le _ _).trans ?_
  have hz : ∀ z : Zd d L, ‖μ * SB d L g a z * Theta d L g ((t : ℂ) * μ) z b‖ ≤
      ‖SB d L g a z‖ * (C₁ * (2 ^ (d - 2) * Real.exp 1) *
        tailT d L g t ((zdistInf d L (b - a) : ℕ) : ℝ)) := by
    intro z
    by_cases hS : SB d L g a z = 0
    · simp [hS]
    rw [norm_mul, norm_mul, hμ, one_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : ‖Theta d L g ((t : ℂ) * μ) z b‖ ≤ ‖Theta d L g (t : ℂ) z b‖ := by
      rw [step5Kernel_norm_Theta_eq_re hL ht0 ht1]
      exact norm_Theta_apply_le hL ht0 ht1 hμ z b
    have h2 := H1 L hL g t hg hgΛ ht0 ht1 z b
    have hsup : zdistInf d L (a - z) ≤ 1 := Step5KerGen_SB_support g hS
    have htri := Step5KerGen_zdistInf_tri b z a
    rw [step5Ker_zdistInf_sub_comm z a] at htri
    have hsh := Step5KerGen_tailT_shift (d := d) (g := g) (t := t) hL1
      (Nat.cast_nonneg (zdistInf d L (b - a))) (Nat.cast_nonneg (zdistInf d L (b - z)))
      (by exact_mod_cast (by omega : zdistInf d L (b - a) ≤ zdistInf d L (b - z) + 1))
    calc ‖Theta d L g ((t : ℂ) * μ) z b‖ ≤ C₁ * tailT d L g t ((zdistInf d L (b - z) : ℕ) : ℝ) := h1.trans h2
      _ ≤ C₁ * ((2 ^ (d - 2) * Real.exp 1) * tailT d L g t ((zdistInf d L (b - a) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsh hC₁.le
      _ = _ := by ring
  calc ∑ z : Zd d L, ‖μ * SB d L g a z * Theta d L g ((t : ℂ) * μ) z b‖
      ≤ ∑ z : Zd d L, ‖SB d L g a z‖ * (C₁ * (2 ^ (d - 2) * Real.exp 1) *
        tailT d L g t ((zdistInf d L (b - a) : ℕ) : ℝ)) := Finset.sum_le_sum fun z _ => hz z
    _ = _ := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL a, one_mul]

/-- **Target 9, band result** (D2 default; `gK = sz.lam`): at `bandFM sz E` with `|E n| ≤ 2` the decay and row sum hold
with a constant `C₆ = C₆(d, Λ)`.  The proof goes through `Step2Kern_thetaKer_band`, `step5Kernel_theta_decay`,
`norm_Theta_apply_le`, and the row sum of the band kernel (`Step5KerGen_row_thetaKer`). -/
theorem step5KerGen_thDecay_band :
    ∀ (d : ℕ) (Λ : ℝ), 3 ≤ d → 0 < Λ → ∃ C₆ : ℝ, 0 < C₆ ∧
      ∀ (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| ≤ 2) → Step5KerGen_ThDecay (bandFM sz E) sz.lam Λ C₆ := by
  intro d Λ hd hΛ
  obtain ⟨C, hC, H⟩ := Step5KerGen_theta_decay_band d Λ hd hΛ
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro sz E hE n hg hgΛ σ σ' t ht0 ht1
  have hμ : ‖mSigma (E n) σ * mSigma (E n) σ'‖ = 1 := by
    rw [norm_mul, norm_mSigma (hE n), norm_mSigma (hE n), one_mul]
  have hker := Step2Kern_thetaKer_band sz E n σ σ' t
  refine ⟨fun a b => ?_, fun a => ?_⟩
  · rw [hker]
    exact (H (sz.L n) (sz.three_le_L n) _ _ hg hgΛ ht0 ht1 _ hμ a b).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (tailT_nonneg (Nat.cast_nonneg _)))
  · simp only [hker]
    refine (Step5KerGen_row_thetaKer _ (sz.three_le_L n) hμ ht0 ht1 a).trans ?_
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (le_max_right _ _) (by linarith)

/-- **The comparison, per index (R1)**: from `0 ≤ g l`, `g² ≤ l²` and the guard `0 < g`, `0 < l` and `g ≤ l`.  If `l < 0`,
`0 ≤ g l` forces `g ≤ 0`; if `l = 0`, `g² ≤ 0` forces `g = 0`; so `0 < l`, and `g² ≤ l²` gives `g ≤ l`. -/
private theorem Step5KerGen_cmp_pos {g l A : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hg : 0 < g) :
    0 < l ∧ g ≤ l := by
  obtain ⟨h1, h2, _⟩ := h
  have hl : 0 < l := by
    rcases lt_trichotomy l 0 with hl | hl | hl
    · nlinarith [mul_pos hg (neg_pos.2 hl)]
    · subst hl; nlinarith
    · exact hl
  exact ⟨hl, (sq_le_sq₀ hg.le hl.le).1 h2⟩

/-- **The crossing** `𝒯^{g₁}_t(r) ≤ A 𝒯^{g₂}_t(r)` for `0 < g₁ ≤ g₂`, `g₂² ≤ A g₁²` (UBA-C1: the one place where the
comparison hypothesis is used; `ℓ_t` is nondecreasing in the coupling, and `B^{g₁}/B^{g₂} ≤ (g₂² + b)/(g₁² + b) ≤ A`). -/
private theorem Step5KerGen_tailT_cross {d L : ℕ} {g₁ g₂ A t r : ℝ} (hL : 1 ≤ (L : ℝ)) (h0 : 0 < g₁) (h1 : g₁ ≤ g₂)
    (h2 : g₂ ^ 2 ≤ A * g₁ ^ 2) (hA : 1 ≤ A) (ht : t < 1) (hr : 0 ≤ r) :
    tailT d L g₁ t r ≤ A * tailT d L g₂ t r := by
  have hb : 0 < |1 - t| := abs_pos.2 (by linarith)
  have hℓ : ellT L g₁ t ≤ ellT L g₂ t := by
    unfold ellT
    gcongr
  have hℓ1 : 0 < ellT L g₁ t := ellT_pos hL
  have hB : BparamR d L g₁ t r ≤ A * BparamR d L g₂ t r := by
    unfold BparamR
    have hx : 0 ≤ (((r + 1) ^ (d - 2))⁻¹ : ℝ) := inv_nonneg.2 (pow_nonneg (by linarith) _)
    have hz : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := inv_nonneg.2 (by positivity)
    have hg : (g₁ ^ 2 + |1 - t|)⁻¹ ≤ A * (g₂ ^ 2 + |1 - t|)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hg hx, mul_le_mul_of_nonneg_right hA hz]
  have hE : Real.exp (-Real.sqrt (r / ellT L g₁ t)) ≤ Real.exp (-Real.sqrt (r / ellT L g₂ t)) := by
    refine Real.exp_le_exp.2 (neg_le_neg (Real.sqrt_le_sqrt ?_))
    exact div_le_div_of_nonneg_left hr hℓ1 hℓ
  unfold tailT
  calc BparamR d L g₁ t r * Real.exp (-Real.sqrt (r / ellT L g₁ t))
      ≤ (A * BparamR d L g₂ t r) * Real.exp (-Real.sqrt (r / ellT L g₂ t)) :=
        mul_le_mul hB hE (Real.exp_pos _).le (by
          have := BparamR_nonneg (d := d) (L := L) (g := g₂) (t := t) hr
          positivity)
    _ = _ := by ring

/-- **Target 9, the profile** `(uwp2-92kj)` (`3_5:2048-2053`) for the carrier kernel (D2 default; band
`step5Kernel_profile_explicit_holds`, `Step5Kernel:199`): the decay at the kernel coupling `gK`, the profile and the windows
at `sz.lam` (size level), and the one comparison hypothesis (R1, Amend 1; DECISIONS §273 (1)):
`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2`.
At an index with `0 < gK n` it gives `0 < sz.lam n`, `gK n ≤ sz.lam n` (`Step5KerGen_cmp_pos`).  The floor
`(1-u)/(1-t) W^{-D}` comes from the row sum, `(TTT2)` (`ekPropTInf_holds`, any positive coupling) is read at `sz.lam`. -/
theorem step5KerGen_profile_holds (d : ℕ) : 3 ≤ d → ∀ Λ C₆ A : ℝ, 0 < Λ → 0 < C₆ → 1 ≤ A → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ) (σ σ' : Bool) (W D u t : ℝ), 0 < gK n → gK n ≤ Λ → 0 < W → 0 ≤ u → u ≤ t → t < 1 →
        (sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) →
        ∀ a₁ a₂ : Zd d (sz.L n),
          (1 - u) * ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
              tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤
            Cp * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) +
              Cp * ((1 - u) / (1 - t) * W ^ (-D)) := by
  intro hd Λ C₆ A hΛ hC₆ hA
  obtain ⟨CT, hCT, hT⟩ := ekPropTInf_holds d hd
  refine ⟨C₆ * A * CT + C₆, by positivity, ?_⟩
  intro sz C gK hdec hcmp n σ σ' W D u t hg0 hgΛ hW hu hut ht hwin a₁ a₂
  obtain ⟨hlam, hc1⟩ := Step5KerGen_cmp_pos (hcmp n) hg0
  have hc2 := (hcmp n).2.2
  have hv : 0 < 1 - u := by linarith
  have hw : 0 < 1 - t := by linarith
  have ht0 : 0 ≤ t := hu.trans hut
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  obtain ⟨hθ, hrow⟩ := hdec n hg0 hgΛ σ σ' t ht0 ht
  have hpt : ∀ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
        tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤
      C₆ * A * (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) *
        tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ)) +
      W ^ (-D) * ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ := by
    intro b
    have hTu0 : 0 ≤ tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) :=
      tailT_nonneg (Nat.cast_nonneg _)
    have hmax : tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤
        tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) + W ^ (-D) := by
      rw [step5Ker_tailW_eq, step5Ker_zdistInf_sub_comm b a₂]
      exact max_le (le_add_of_nonneg_right hWD) (le_add_of_nonneg_left hTu0)
    have hcr := Step5KerGen_tailT_cross (d := d) (L := sz.L n) (t := t)
      (r := ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ)) hL1 hg0 hc1 hc2 hA ht (Nat.cast_nonneg _)
    have hθ' := (hθ a₁ b).trans (mul_le_mul_of_nonneg_left hcr hC₆.le)
    calc _ ≤ ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
          (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) + W ^ (-D)) :=
          mul_le_mul_of_nonneg_left hmax (norm_nonneg _)
      _ = ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
            tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) +
          W ^ (-D) * ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ := by ring
      _ ≤ C₆ * (A * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ)) *
            tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) +
          W ^ (-D) * ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ :=
          add_le_add_left (mul_le_mul_of_nonneg_right hθ' hTu0) _
      _ = _ := by ring
  have hsum : ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ *
        tailW d (sz.L n) (sz.lam n) u ((sz.L n : ℕ) : ℝ) W D ((zdistInf d (sz.L n) (b - a₂) : ℕ) : ℝ) ≤
      C₆ * A * ∑ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) *
          tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ) +
        W ^ (-D) * ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖ := by
    calc _ ≤ ∑ b : Zd d (sz.L n), (C₆ * A * (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) *
          tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ)) +
          W ^ (-D) * ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖) := Finset.sum_le_sum fun b _ => hpt b
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hS := hT (sz.L n) (sz.lam n) u t hlam hu hut ht hwin a₂ a₁
  rw [step5Ker_zdistInf_sub_comm a₂ a₁] at hS
  have hS' : (1 - u) * ∑ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) *
          tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ) ≤
      CT * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) := by
    calc _ ≤ (1 - u) * (CT / (1 - u) * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hS hv.le
      _ = _ := by field_simp
  have hT0 : 0 ≤ tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) :=
    tailT_nonneg (Nat.cast_nonneg _)
  have hF : 0 ≤ (1 - u) / (1 - t) * W ^ (-D) := by positivity
  calc _ ≤ (1 - u) * (C₆ * A * ∑ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a₂ - b) : ℕ) : ℝ) *
          tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (b - a₁) : ℕ) : ℝ) +
        W ^ (-D) * ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a₁ b‖) :=
        mul_le_mul_of_nonneg_left hsum hv.le
    _ ≤ C₆ * A * (CT * tailT d (sz.L n) (sz.lam n) t ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ)) +
          C₆ * ((1 - u) / (1 - t) * W ^ (-D)) := by
        have h1 := mul_le_mul_of_nonneg_left hS' (by positivity : 0 ≤ C₆ * A)
        have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hrow a₁) hWD) hv.le
        have e : (1 - u) * (W ^ (-D) * (C₆ / (1 - t))) = C₆ * ((1 - u) / (1 - t) * W ^ (-D)) := by
          field_simp
        nlinarith [h1, h2, e]
    _ ≤ _ := by nlinarith [mul_nonneg (by positivity : 0 ≤ C₆ * A * CT + C₆) hT0,
        mul_nonneg (by positivity : 0 ≤ C₆ * A * CT) hF, mul_nonneg hC₆.le hF,
        mul_nonneg (by positivity : 0 ≤ C₆ * A * CT) hT0]

end Decay

/-! ## 4. Target 11: `TailtoTail`, band instance only -/

/-- **Target 11** (U6's target 7 at the band family; no generic proof, note (5) of T2462): the band pin `stTailtoTail_holds`
(`TailtoTail:582`) read as `STTailtoTailgL'` at `bandFM`. -/
theorem stTailtoTailgL'_holds_band (d : ℕ) : STTailtoTailgL' d (fun sz E => bandFM sz E) :=
  stTailtoTailgL'_band d (stTailtoTail_holds d)

/-! ## 5. Compiled nonempty instances and band re-derivations (`d = 3`)

The data are the merged preflight sequence `sz0` (`L = 4`, `W = 32`, `lam = 1/64` at `n = 0`) and the band carrier
`bandFM sz0 (fun _ => 0)` (`E = 0`, `m = i`); the semigroup law is `step2Gen_USemigroup_band` (`|E n| = 0 ≤ 2`).  Every
deterministic hypothesis is discharged. -/

section Inst

open RBM.Gauss.SizesInst

/-- **Target 8 at the band** (`d = 3`, `n = 0`, charges `(+,-)`, `s = 1/4`, `t = 1/2`): the semigroup law is discharged. -/
example : Step2Gen_uKer (bandFM sz0 (fun _ => (0 : ℝ))) 0 true false (1 / 4) (1 / 2) =
    1 + ((((1 / 2 : ℝ) - 1 / 4 : ℝ)) : ℂ) • Step2Gen_thetaKer (bandFM sz0 (fun _ => (0 : ℝ))) 0 true false (1 / 2) :=
  Step5KerGen_uKer_eq _ 0 (step2Gen_USemigroup_band sz0 _ 0 (by norm_num)) true false (1 / 4) (1 / 2)
    (by norm_num) (by norm_num)

/-- **Target 8, inside `UN`, at the band** (`k = 2`, charges `(+,-)`, any tensor `A`, any index `a`). -/
example (A : (Fin 2 → Zd 3 (sz0.L 0)) → ℂ) (a : Fin 2 → Zd 3 (sz0.L 0)) :
    Step2Gen_UN (bandFM sz0 (fun _ => (0 : ℝ))) 0 ![true, false] (1 / 4) (1 / 2) A a =
      ∑ b : Fin 2 → Zd 3 (sz0.L 0),
        (∏ i, (1 + ((((1 / 2 : ℝ) - 1 / 4 : ℝ)) : ℂ) • Step2Gen_thetaKer (bandFM sz0 (fun _ => (0 : ℝ))) 0
          (![true, false] i) (![true, false] (finRotate 2 i)) (1 / 2)) (a i) (b i)) * A b :=
  Step5KerGen_UN_decomp _ 0 (step2Gen_USemigroup_band sz0 _ 0 (by norm_num)) ![true, false] (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) A a

/-- **Target 8, band re-derivation of `step5Kernel_decompU`** (`Step5Kernel:57`): for every band size sequence, energy
`|E n| ≤ 2`, charge pair and `0 < t < 1`, the band form `uKer = (s/t) + ((t-s)/t) Θ_t` follows from target 8 and
`Θ = 1 + t thetaKer` (`mul_Theta_of_three_le`). -/
example {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hE : |E n| ≤ 2) (σ σ' : Bool) {s t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) :
    RBM.uKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') s t =
      ((s / t : ℝ) : ℂ) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
        (((t - s) / t : ℝ) : ℂ) •
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ')) := by
  have h8 := Step5KerGen_uKer_eq (bandFM sz E) n (step2Gen_USemigroup_band sz E n hE) σ σ' s t ht0.le ht1
  rw [Step2Kern_uKer_band, Step2Kern_thetaKer_band] at h8
  have hμ : ‖mSigma (E n) σ * mSigma (E n) σ'‖ = 1 := by
    rw [norm_mul, norm_mSigma hE, norm_mSigma hE, one_mul]
  have hξ : ‖(t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ')‖ < 1 := norm_t_mul_lt_one ht0.le ht1 hμ
  have hΘ := mul_Theta_of_three_le (d := d) (g := sz.lam n) (sz.three_le_L n) hξ
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hΘ' : Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ')) =
      1 + (t : ℂ) • RBM.thetaKer d (sz.L n) (sz.lam n) (mSigma (E n) σ * mSigma (E n) σ') t := by
    unfold RBM.thetaKer
    rw [smul_mul_assoc, smul_smul]
    generalize Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (E n) σ * mSigma (E n) σ')) = Θ at hΘ ⊢
    rw [sub_mul, one_mul, smul_mul_assoc, sub_eq_iff_eq_add] at hΘ
    exact hΘ
  rw [h8, hΘ']
  match_scalars <;> (field_simp; try ring)

/-- **Target 9, the decay at the band, at `sz0`**: `Λ = 4 = 𝔡⁻¹` (`𝔡 = 1/4`), `E = 0`. -/
private theorem Step5KerGen_thDecay_sz0 :
    ∃ C₆ : ℝ, 0 < C₆ ∧ Step5KerGen_ThDecay (bandFM sz0 (fun _ => (0 : ℝ))) sz0.lam 4 C₆ := by
  obtain ⟨C₆, hC₆, h⟩ := step5KerGen_thDecay_band 3 4 le_rfl (by norm_num)
  exact ⟨C₆, hC₆, h sz0 _ (fun n => by norm_num)⟩

/-- **Target 9, the profile at the band** (`gK = sz0.lam`, `A = 1`; R1 holds at every `n`), `n = 0`, charges `(+,-)`,
`W = 32`, `D = 2`, `u = 0`, `t = 1/2` (window `lam²/L² = 1/65536 ≤ 1/2 = 1 - t`): every deterministic hypothesis is
discharged. -/
example : ∃ Cp : ℝ, 0 < Cp ∧ ∀ a₁ a₂ : Zd 3 (sz0.L 0),
    (1 - 0) * ∑ b : Zd 3 (sz0.L 0), ‖Step2Gen_thetaKer (bandFM sz0 (fun _ => (0 : ℝ))) 0 true false (1 / 2) a₁ b‖ *
        tailW 3 (sz0.L 0) (sz0.lam 0) 0 ((sz0.L 0 : ℕ) : ℝ) 32 2 ((zdistInf 3 (sz0.L 0) (b - a₂) : ℕ) : ℝ) ≤
      Cp * tailT 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ((zdistInf 3 (sz0.L 0) (a₁ - a₂) : ℕ) : ℝ) +
        Cp * ((1 - 0) / (1 - 1 / 2) * (32 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C₆, hC₆, hdec⟩ := Step5KerGen_thDecay_sz0
  obtain ⟨Cp, hCp, H⟩ := step5KerGen_profile_holds 3 le_rfl 4 C₆ 1 (by norm_num) hC₆ le_rfl
  refine ⟨Cp, hCp, ?_⟩
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have hL : sz0.L 0 = 4 := sz0_values.1
  have := H sz0 (bandFM sz0 (fun _ => 0)) sz0.lam hdec
    (fun n => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩) 0 true false 32 2 0 (1 / 2)
    (by rw [hl]; norm_num) (by rw [hl]; norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (Or.inl (by rw [hl, hL]; norm_num))
  simpa using this

/-- The half-coupling sequence `lam/2` of `sz0` (same `L`, `W`): the non-band instance reads the kernel at `gK = lam/2`. -/
private def Step5KerGen_szH : Sizes 3 where
  L := sz0.L
  W := sz0.W
  lam := fun n => sz0.lam n / 2
  three_le_L := sz0.three_le_L
  W_pos := sz0.W_pos

/-- The carrier over `sz0` whose kernel is the band kernel built at the coupling `lam/2`
(the fields of `bandFM Step5KerGen_szH E`, which has the same `L`, `W` as `sz0`). -/
private def Step5KerGen_carrierH (E : ℕ → ℝ) : FlowFM sz0 where
  L := (bandFM Step5KerGen_szH E).L
  K := (bandFM Step5KerGen_szH E).K
  G := (bandFM Step5KerGen_szH E).G
  M := (bandFM Step5KerGen_szH E).M
  S := (bandFM Step5KerGen_szH E).S
  eta := (bandFM Step5KerGen_szH E).eta
  m := (bandFM Step5KerGen_szH E).m

/-- **Target 9, the profile at a non-band coupling**: the kernel is the band kernel at `gK = sz0.lam/2`
(`Step5KerGen_carrierH`), the size-level sequence is `sz0.lam`, so `gK ≠ sz0.lam`, and R1 holds at every `n` with
`A = 4` (`0 ≤ (lam/2) lam`, `(lam/2)² ≤ lam²`, equality in `lam² ≤ 4 (lam/2)²`).  Same data as the band instance. -/
example : ∃ Cp : ℝ, 0 < Cp ∧ ∀ a₁ a₂ : Zd 3 (sz0.L 0),
    (1 - 0) * ∑ b : Zd 3 (sz0.L 0), ‖Step2Gen_thetaKer (Step5KerGen_carrierH (fun _ => (0 : ℝ))) 0 true false (1 / 2) a₁ b‖ *
        tailW 3 (sz0.L 0) (sz0.lam 0) 0 ((sz0.L 0 : ℕ) : ℝ) 32 2 ((zdistInf 3 (sz0.L 0) (b - a₂) : ℕ) : ℝ) ≤
      Cp * tailT 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ((zdistInf 3 (sz0.L 0) (a₁ - a₂) : ℕ) : ℝ) +
        Cp * ((1 - 0) / (1 - 1 / 2) * (32 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C₆, hC₆, hdecH⟩ := step5KerGen_thDecay_band 3 4 le_rfl (by norm_num)
  have hdec : Step5KerGen_ThDecay (Step5KerGen_carrierH (fun _ => (0 : ℝ))) (fun n => sz0.lam n / 2) 4 C₆ :=
    hdecH Step5KerGen_szH (fun _ => 0) (fun n => by norm_num)
  obtain ⟨Cp, hCp, H⟩ := step5KerGen_profile_holds 3 le_rfl 4 C₆ 4 (by norm_num) hC₆ (by norm_num)
  refine ⟨Cp, hCp, ?_⟩
  have hl : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have hL : sz0.L 0 = 4 := sz0_values.1
  have := H sz0 (Step5KerGen_carrierH (fun _ => 0)) (fun n => sz0.lam n / 2) hdec
    (fun n => by
      have h0 : 0 ≤ sz0.lam n := by unfold sz0; positivity
      exact ⟨by positivity, by nlinarith, by nlinarith⟩)
    0 true false 32 2 0 (1 / 2)
    (by rw [hl]; norm_num) (by rw [hl]; norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)
    (Or.inl (by rw [hl, hL]; norm_num))
  simpa using this

/-- **Target 11 at the band** (`d = 3`; `stTailtoTailgL'_holds_band` needs no pin): `n = 0` (`L = 4`, `W = 32`,
`lam = 1/64`), `E = 0` (`Im m(0) = 1 ≥ κ = 1/10`), `D = 2`, `s = 1/2`, `t = 3/4` (`lam² = 1/4096 ≤ 1/4 = 1 - t`),
`σ = (+,-)` and the extremal tensor `A_b = T_{s,D}(|b₁-b₂|)` (nonzero). -/
example : ∃ Cc : ℝ, 0 < Cc ∧ ∀ a : Fin 2 → Zd 3 (sz0.L 0),
    ‖Step2Gen_UN (bandFM sz0 (fun _ => (0 : ℝ))) 0 ![true, false] (1 / 2 : ℝ) (3 / 4 : ℝ)
        (fun b : Fin 2 → Zd 3 (sz0.L 0) =>
          ((tailTD 3 ((sz0.W 0 : ℕ) : ℝ) (1 / 2 : ℝ) 2 (zdistInf 3 (sz0.L 0) (b 0 - b 1) : ℕ) : ℝ) : ℂ)) a‖ ≤
      Cc * tailTD 3 ((sz0.W 0 : ℕ) : ℝ) (3 / 4 : ℝ) 2 (zdistInf 3 (sz0.L 0) (a 0 - a 1) : ℕ) +
        ((1 - 1 / 2 : ℝ) / (1 - 3 / 4 : ℝ)) ^ 2 * ((sz0.W 0 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  obtain ⟨Cc, hC, H⟩ := stTailtoTailgL'_holds_band 3 (by norm_num) (1 / 10) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam2 : sz0.lam 0 ^ 2 ≤ 1 - 3 / 4 := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  have hIm : (1 / 10 : ℝ) ≤ ((bandFM sz0 (fun _ => (0 : ℝ))).m 0).im := by
    change (1 / 10 : ℝ) ≤ (mE 0).im
    rw [mE_im]
    have h2 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
      rw [show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    rw [h2]; norm_num
  refine ⟨Cc, hC, fun a => ?_⟩
  exact H sz0 0 0 2 (1 / 2) (3 / 4) hlam hIm (by norm_num) (by norm_num) (by norm_num) hlam2
    ![true, false] _
    (fun b => by rw [Complex.norm_real, Real.norm_of_nonneg (tailTD_nonneg (by norm_num))]) a

end Inst

end RBM.BA

end
