/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14b2

/-!
# BA-L L4b2b (T2489), file B: the families `T3B`, `T3C-Ḡ` and the binding conclusion `baExp14bS2_holds`

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:7-121` (`(eq:ELW_term)`, `(eq:termI2)` `:43-49`,
`(eq:termI41)` `:57-70`), `GGGamma` `:393-405`.  File A (`Graph/BAExp14b2.lean`, merged) holds the twisted bridges, the sharp average
P3, the families `D1t, D2t, T2a, T2b` and the Ward sums; this file (L4b2b, targets 4-7) holds `T3B^{(k)}` (target 4),
`T3C-Ḡ^{(k)}` (target 5), the binding conclusion `baExp14bS2_holds : ∀ d, BAExp14bS2 d` (target 6) and the instances (target 7).

Stem `BAExp14b2B_`.  Helpers with a Step 1/2 or TL binder are `private` (`LWAvgLawgL` is not registered, ticket `T2489.md`); the
pin-free helpers are public with the stem.  The private theorems of file A are reached by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

open private BAExp14b2_base BAExp14b2_tl2 BAExp14b2_I1K from RBM3D.Graph.BAExp14b2

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Auxiliary calculus -/

section Aux

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `f ≺ g` gives `√f ≺ √g` (`(N^τ √g)² = N^{2τ} g`). -/
theorem BAExp14b2B_Dom_sqrt {μ : Measure sz.SeqΩ} {f : ∀ n : ℕ, sz.SeqΩ → ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n)
    (h : BAExp14a_Dom sz μ f g) : BAExp14a_Dom sz μ (fun n ω => Real.sqrt (f n ω)) (fun n => Real.sqrt (g n)) := by
  unfold BAExp14a_Dom PrecL at h ⊢
  refine BAExp14a_prec_of_bad h fun τ hτ => ⟨2 * τ, by positivity, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  refine ⟨(), ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ τ * Real.sqrt (g n) < Real.sqrt (f n ω) at hu
  change ((sz.size n : ℕ) : ℝ) ^ (2 * τ) * g n < f n ω
  have hN : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : (((sz.size n : ℕ) : ℝ) ^ τ * Real.sqrt (g n)) ^ 2 < (Real.sqrt (f n ω)) ^ 2 :=
    pow_lt_pow_left₀ hu (mul_nonneg hN (Real.sqrt_nonneg _)) two_ne_zero
  have hf0 : 0 ≤ f n ω := by
    by_contra hneg
    push Not at hneg
    rw [Real.sqrt_eq_zero_of_nonpos hneg.le] at hu
    exact absurd hu (not_lt.2 (mul_nonneg hN (Real.sqrt_nonneg _)))
  rw [mul_pow, Real.sq_sqrt (hg n), Real.sq_sqrt hf0, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)] at h1
  convert h1 using 3
  push_cast
  ring

/-- The weights `Σ_{a₁} |κ_{a₁c₁}| |MB_{c₁c₂}| h(c₁, c₂) ≤ S Σ_{c₁,c₂} |MB_{c₁c₂}| h(c₁, c₂)` (columns of `κ` are `≤ S`). -/
theorem BAExp14b2B_wsum12 {ι : Type*} [Fintype ι] (κm MB : ι → ι → ℂ) {S : ℝ} (hκ : ∀ c, ∑ a, ‖κm a c‖ ≤ S)
    (h : ι → ι → ℝ) (h0 : ∀ c₁ c₂, 0 ≤ h c₁ c₂) :
    ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * (‖MB c₁ c₂‖ * h c₁ c₂) ≤ S * ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * h c₁ c₂ := by
  calc ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * (‖MB c₁ c₂‖ * h c₁ c₂)
      = ∑ c₁, ∑ a₁, ∑ c₂, ‖κm a₁ c₁‖ * (‖MB c₁ c₂‖ * h c₁ c₂) := Finset.sum_comm
    _ = ∑ c₁, (∑ a₁, ‖κm a₁ c₁‖) * ∑ c₂, ‖MB c₁ c₂‖ * h c₁ c₂ := by
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ c₁, S * ∑ c₂, ‖MB c₁ c₂‖ * h c₁ c₂ :=
        Finset.sum_le_sum fun c₁ _ => mul_le_mul_of_nonneg_right (hκ c₁)
          (Finset.sum_nonneg fun c₂ _ => mul_nonneg (norm_nonneg _) (h0 c₁ c₂))
    _ = S * ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * h c₁ c₂ := (Finset.mul_sum _ _ _).symm

end Aux

/-! ## 2. The core: `Φ = Σ_{a₁} D_{a₁} X_{a₁} + R` against `(1 - t)⁻¹ 𝔟^{5/2}` -/

section Core

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **The core of the closing** (general form of `BAExp14b2_close`): a family `Φ = Σ_{a₁} D_{a₁} X_{a₁} + R` with the deterministic weights `D`
(`Σ_{a₁} |D_{a₁}| ≤ D_n ≺ g_D`) is paid with the sharp average P3 (`D_n g_D 𝔟^{3/2} ≲ ζ`), and the pathwise remainder `|R| ≤ Q ≺ g_Q ≲ ζ`
with the master lemma `BAExp14a_prec_int` (envelope `N^{K_y}`, floor `N^{-5/2} ≤ ζ`), `ζ = (1 - t)⁻¹ 𝔟^{5/2}`. -/
theorem BAExp14b2B_core (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hP3 : PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)))
    {V : ℕ → Type} (Φ : ∀ n, V n → sz.SeqΩ → ℂ) (Dd : ∀ n, V n → Zd (k + 2) (sz.L n) → ℂ) (Rr : ∀ n, V n → sz.SeqΩ → ℂ)
    (hΦ : ∀ n v ω, Φ n v ω = (∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) + Rr n v ω)
    (D gD : ℕ → ℝ) (hD0 : ∀ n, 0 ≤ D n) (hgD0 : ∀ n, 0 ≤ gD n) (hD : ∀ᶠ n in atTop, ∀ v, ∑ a₁, ‖Dd n v a₁‖ ≤ D n)
    (hDD : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => D n) gD)
    (Q : ∀ n, sz.SeqΩ → ℝ) (gQ : ℕ → ℝ)
    (hR : ∀ᶠ n in atTop, ∀ v ω, ‖Rr n v ω‖ ≤ Q n ω) (hDQ : BAExp14a_Dom sz (BAExp14a_μ sz) Q gQ)
    (Ky : ℕ) (henv : ∀ᶠ n in atTop, ∀ v ω, ‖Rr n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Ky)
    {K : ℝ} (hK : 0 < K)
    (hdet : ∀ᶠ n in atTop, gD n * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ) ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))
    (hrnd : ∀ᶠ n in atTop, gQ n ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :
    PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Φ n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hζ0 : ∀ n, 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := fun n =>
    mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg (hB n) _)
  set emax : ℕ → ℝ := fun n => BAExp14b2_sup (fun c : Zd (k + 2) (sz.L n) => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) with hem
  have hem0 : ∀ n, 0 ≤ emax n := fun n => BAExp14b2_sup_nonneg (f := fun c : Zd (k + 2) (sz.L n) => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) fun c => norm_nonneg _
  have hDe : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => emax n) (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) :=
    BAExp14b2_Dom_sup (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) _ hP3
  have hDet : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => D n * emax n) (fun n => gD n * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) :=
    BAExp14a_Dom.mul hsz (fun n _ => hem0 n) hgD0 hDD hDe
  have hDet' : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => D n * emax n) (fun n => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) :=
    BAExp14a_Dom.mono hsz hK hζ0 hdet hDet
  have hRprec : PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Rr n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    refine BAExp14a_prec_int (μ := BAExp14a_μ sz) hsz (V := V) Rr Q gQ _ (K := K) (Kenv := (Ky : ℝ)) (Kf := 5 / 2) hK hζ0 hR hDQ hrnd ?_ ?_
    · filter_upwards [henv] with n hn v ω
      rw [Real.rpow_natCast]; exact hn v ω
    · exact Eventually.of_forall fun n => BAExp14a_floor n (ht0 n) (ht1 n)
  have hsum := StochDomAt.add hsz (BAExp14a_Dom.index hsz (V := V) hDet') hRprec
  refine BAExp14a_prec_mono hsz (K := 2) two_pos (fun n _ _ => hζ0 n) (Eventually.of_forall fun n v ω => ?_)
    (BAExp14a_prec_of_le_ev (ξ₁ := fun n v ω => D n * emax n + ‖∫ ω, Rr n v ω ∂(BAExp14a_μ sz)‖) ?_ hsum)
  · simp only [Pi.add_apply]; linarith [hζ0 n]
  · filter_upwards [hfacts, hD] with n hn hDn v ω
    have hf := hn (t n) (ht0 n) (ht n)
    have hXi : ∀ a₁, Integrable (fun ω => BAExp14a_X sz z n (t n) ω a₁) (BAExp14a_μ sz) := fun a₁ =>
      BAExp14a_int_X hκ hflow n (ht0 n) (ht n) hf a₁
    have hF1 : Integrable (fun ω => ∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) (BAExp14a_μ sz) :=
      integrable_finsetSum _ fun a₁ _ => (hXi a₁).const_mul _
    have hI1 : ∫ ω, (∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) ∂(BAExp14a_μ sz) =
        ∑ a₁, Dd n v a₁ * ∫ ω, BAExp14a_X sz z n (t n) ω a₁ ∂(BAExp14a_μ sz) := by
      rw [integral_finsetSum _ fun a₁ _ => (hXi a₁).const_mul _]
      exact Finset.sum_congr rfl fun a₁ _ => integral_const_mul _ _
    have hdet' : ‖∑ a₁, Dd n v a₁ * ∫ ω, BAExp14a_X sz z n (t n) ω a₁ ∂(BAExp14a_μ sz)‖ ≤ D n * emax n := by
      calc _ ≤ ∑ a₁, ‖Dd n v a₁‖ * emax n := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (BAExp14b2_le_sup (fun c : Zd (k + 2) (sz.L n) =>
              ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) a₁) (norm_nonneg _)
        _ = (∑ a₁, ‖Dd n v a₁‖) * emax n := (Finset.sum_mul _ _ _).symm
        _ ≤ D n * emax n := mul_le_mul_of_nonneg_right (hDn v) (hem0 n)
    have hcongr : ∫ ω, Φ n v ω ∂(BAExp14a_μ sz) =
        ∫ ω, ((∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) + Rr n v ω) ∂(BAExp14a_μ sz) :=
      integral_congr_ae (Eventually.of_forall (hΦ n v))
    rw [hcongr]
    refine (BAExp14b2_norm_int_add hF1).trans ?_
    rw [hI1]
    linarith [hdet']

end Core

/-! ## 3. Target 4: the family `T3B^{(k)}` (I23K twin, `lwExpI23K_holds`, `Graph/LWExpTerm4.lean:1316`) -/

section T3B

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `s = 𝔟^{1/2}`: `𝔟 = s²`, `𝔟^{1/2} = √𝔟 = s`, `𝔟^{3/2} = s³`, `𝔟^{5/2} = s⁵` for `0 < 𝔟 ≤ 2`. -/
theorem BAExp14b2B_s {B : ℝ} (hB : 0 < B) (hB2 : B ≤ 2) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 2 ∧ B = s ^ 2 ∧ B ^ (1 / 2 : ℝ) = s ∧ Real.sqrt B = s ∧ B ^ (3 / 2 : ℝ) = s ^ 3 ∧ B ^ (5 / 2 : ℝ) = s ^ 5 := by
  obtain ⟨s, hs0, hs2, hBs, h32, h52⟩ := BAExp14b2_s hB hB2
  have h12 : B ^ (1 / 2 : ℝ) = s := by
    rw [hBs, ← Real.rpow_natCast, ← Real.rpow_mul hs0.le]; norm_num
  exact ⟨s, hs0, hs2, hBs, h12, by rw [Real.sqrt_eq_rpow, h12], h32, h52⟩

/-- The fluctuation sup `τ̂ = max |twTr|` (TL1 variable). -/
def BAExp14b2B_tw (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n t ω p.1 p.2‖)

/-- The sup of the 2-loops `max |𝓛^{(2)}|`. -/
def BAExp14b2B_Lm (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).L n t q.1 q.2 ω‖)

/-- `a ≤ η⁻¹ + 1`, `b ≤ η⁻¹ + 1`, `max |𝓛^{(2)}| ≤ η⁻²` pathwise. -/
theorem BAExp14b2B_a_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) : BAExp14a_a sz z n t ω ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
  Finset.sup'_le _ _ fun c _ => BAExp14a_X_le hκ hflow n ht0 ht hf ω c

theorem BAExp14b2B_b_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) : BAExp14a_b sz z n t ω ≤ ((baFMz sz z).eta n t)⁻¹ + 1 :=
  Finset.sup'_le _ _ fun p _ => BAExp14a_GM_le hκ hflow n ht0 ht hf ω p.1 p.2

theorem BAExp14b2B_Lm_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) : BAExp14b2B_Lm sz z n t ω ≤ (((baFMz sz z).eta n t)⁻¹) ^ 2 := by
  refine BAExp14b2_sup_le fun q => ?_
  have hL := BAExp14b2_L2_le hκ hflow ht0 ht (q.1 0) (q.1 1) (q.2 0) (q.2 1) ω
  rwa [← BAExp14b2_vec2 q.1, ← BAExp14b2_vec2 q.2] at hL

/-- `|G_{xx}| ≤ 1 + b`. -/
theorem BAExp14b2B_diag_le {n : ℕ} {t : ℝ} {CM S : ℝ} (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ)
    (x : Idx (k + 2) (sz.L n) (sz.W n)) : ‖(baFMz sz z).G n t ω x x‖ ≤ 1 + BAExp14a_b sz z n t ω := by
  have h : (baFMz sz z).G n t ω x x = (baFMz sz z).GM n t ω x x + (baFMz sz z).M n x x := by unfold FlowFM.GM; ring
  rw [h]
  exact (norm_add_le _ _).trans (by linarith [BAExp14a_le_b (sz := sz) (z := z) n t ω x x, hf.hM1 x x])

/-- **The pathwise bound of `T3B^{(k)}`** (twin of `lwExpTerm4_R23_le`, `Graph/LWExpTerm4.lean:1195`): `‖T3B‖ ≤ S C_M a τ̂ η⁻¹ A √Q`, from the block form,
TL1 variable `τ̂ ≥ |twTr|`, `a ≥ |X|`, `A ≥ |G_{xx}|`, `Q ≥ |𝓛^{(2)}_{(σ,-σ),(a,b)}|`, the kernel sums `BAExp14b2_wsum_c2` and the `𝓛^{(3)}` Ward sum. -/
theorem BAExp14b2B_T3B_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) {aa τ A Q : ℝ}
    (haa : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ aa) (hτ : ∀ c₁ c₂, ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ τ)
    (hA : ∀ x, ‖(baFMz sz z).G n t ω x x‖ ≤ A) (hQ : ‖(baFMz sz z).L n t ![σ, !σ] ![a, b] ω‖ ≤ Q) :
    ‖BAExp14b_FT3B sz z n t ω kb σ a b‖ ≤ S * CM * (aa * (τ * (((baFMz sz z).eta n t)⁻¹ * (A * Real.sqrt Q)))) := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have haa0 : 0 ≤ aa := (norm_nonneg _).trans (haa 0)
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans (hτ 0 0)
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  have hCM0 : 0 ≤ CM := hf.hCM
  rw [BAExp14b_FT3B_block hr ht0 hf.ht1 kb σ a b, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_pow,
    Complex.norm_natCast]
  have hL3 := BAExp14b2_L3_ward hκ hflow ht0 ht σ b a ω hA hQ
  have hsum : ‖∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ *
      twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ * (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖ ≤
      ∑ a₁, ∑ c₁, ∑ c₂, ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ *
        (aa * τ * ‖(baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₁ _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₂ _ => ?_)))
    simp only [norm_mul]
    have h1 := haa a₁
    have h2 : ‖twTrP n ((baFMz sz z).GM n t ω) c₁ c₂‖ ≤ τ := hτ c₂ c₁
    have := norm_nonneg (BAExp14b_kap sz z n t kb a₁ c₁)
    have := norm_nonneg (BAExp14b_MB sz z n c₁ c₂)
    have := norm_nonneg ((baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω)
    calc _ ≤ ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * aa * τ *
          ‖(baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖ := by gcongr
      _ = _ := by ring
  have hws := BAExp14b2_wsum_c2 (BAExp14b_kap sz z n t kb) (BAExp14b_MB sz z n) (S := S) (CM := CM)
    (fun c => BAExp14b2_kap_col hr hf kb c) (fun c => BAExp14b2_MB_col hr hf c)
    (fun c₂ => aa * τ * ‖(baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖) (fun c₂ => by positivity)
  have ht1 : t ≤ 1 := hf.ht1.le
  calc t * ((sz.W n : ℕ) : ℝ) ^ (k + 2) * ‖∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
        BAExp14a_X sz z n t ω a₁ * twTrP n ((baFMz sz z).GM n t ω) c₁ c₂ * (baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖
      ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (S * CM * ∑ c₂, aa * τ * ‖(baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖) := by
        gcongr
        exact hsum.trans hws
    _ = S * CM * (aa * τ) * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * ∑ c₂, ‖(baFMz sz z).L n t ![true, true, σ] ![c₂, b, a] ω‖) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ S * CM * (aa * τ) * (((baFMz sz z).eta n t)⁻¹ * A * Real.sqrt Q) := by gcongr
    _ = _ := by ring

end T3B

section T3Bmain

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **Target 4 (the I23K twin `T3B^{(k)}`, `j = 4, 5`)**: for the family `T3B^{(kb)}` of S2, every charge and block pair,
`‖𝔼 T3B‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}` over the carrier `baFMz sz z` and the law `BAExp14a_μ sz`, from `STLocalEntrygL`, `LWAvgLawgL`, `STLmaxgL` and
`BATwistAvgLaw` (zero slack in TL1: `a τ̂ η⁻¹ A √Q ≺ 𝔟 · 𝔟 · η⁻¹ · 1 · 𝔟^{1/2}`).  Pathwise, no P3.  Private: `LWAvgLawgL` is not registered. -/
private theorem BAExp14b2B_T3B (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hLm : STLmaxgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (kb : Bool) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FT3B sz z n (t n) ω kb p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hη : ∀ n, 0 < (baFMz sz z).eta n (t n) := fun n => BAExp14a_eta_pos hκ hflow n (ht0 n) (ht n)
  have hE0 : ∀ n, 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := fun n => inv_nonneg.2 (hη n).le
  have hζ0 : ∀ n, 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := fun n =>
    mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg (hB n) _)
  have hs0 : ∀ n, 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := fun n => Real.rpow_nonneg (hB n) _
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts (S * CM + 1)
  have hDb := BAExp14a_Dom_b (κ := κ) (ε := ε) (𝔠 := 𝔠) (𝔡 := 𝔡) (BAExp14a_μ sz) t ht1 hE
  have hDQ0 := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n))) ω => ‖(baFMz sz z).L n (t n) q.1 q.2 ω‖) _ (hLm 2 (by norm_num))
  have hDsq := BAExp14b2B_Dom_sqrt (fun n => pow_nonneg (hB n) (2 - 1)) hDQ0
  have d1 := BAExp14a_Dom.add hsz (BAExp14a_Dom.refl hsz (g := fun _ => (1 : ℝ)) fun _ => zero_le_one) hDb
  have d2 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => 1 + BAExp14a_b sz z n (t n) ω)
    (f₂ := fun n ω => Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω)) (fun n ω => Real.sqrt_nonneg _)
    (fun n => add_nonneg zero_le_one (hs0 n)) d1 hDsq
  have d3 := BAExp14a_Dom.mul hsz (f₁ := fun n _ => ((baFMz sz z).eta n (t n))⁻¹)
    (f₂ := fun n ω => (1 + BAExp14a_b sz z n (t n) ω) * Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω))
    (fun n ω => mul_nonneg (add_nonneg zero_le_one (BAExp14a_b_nonneg n (t n) ω)) (Real.sqrt_nonneg _)) hE0
    (BAExp14a_Dom.refl hsz (g := fun n => ((baFMz sz z).eta n (t n))⁻¹) hE0) d2
  have d4 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14b2B_tw sz z n (t n) ω)
    (f₂ := fun n ω => ((baFMz sz z).eta n (t n))⁻¹ * ((1 + BAExp14a_b sz z n (t n) ω) * Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω)))
    (fun n ω => mul_nonneg (hE0 n) (mul_nonneg (add_nonneg zero_le_one (BAExp14a_b_nonneg n (t n) ω)) (Real.sqrt_nonneg _))) hB hDτ d3
  have d5 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14a_a sz z n (t n) ω)
    (f₂ := fun n ω => BAExp14b2B_tw sz z n (t n) ω * (((baFMz sz z).eta n (t n))⁻¹ *
      ((1 + BAExp14a_b sz z n (t n) ω) * Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω))))
    (fun n ω => mul_nonneg (BAExp14b2_sup_nonneg fun p => norm_nonneg _) (mul_nonneg (hE0 n)
      (mul_nonneg (add_nonneg zero_le_one (BAExp14a_b_nonneg n (t n) ω)) (Real.sqrt_nonneg _)))) hB hDa d4
  have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
  have d6 := BAExp14a_Dom.const_mul hsz hSC (fun n => mul_nonneg (hB n) (mul_nonneg (hB n) (mul_nonneg (hE0 n)
    (mul_nonneg (add_nonneg zero_le_one (hs0 n)) (Real.sqrt_nonneg _))))) d5
  have hRQ : ∀ᶠ n in atTop, ∀ (v : Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ),
      ‖BAExp14b_FT3B sz z n (t n) ω kb v.1 v.2.1 v.2.2‖ ≤ S * CM * (BAExp14a_a sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω *
        (((baFMz sz z).eta n (t n))⁻¹ * ((1 + BAExp14a_b sz z n (t n) ω) * Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω))))) := by
    filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ ω
    exact BAExp14b2B_T3B_le hκ hflow (ht0 n) (ht n) (hn (t n) (ht0 n) (ht n)) kb σ a b ω (fun c => BAExp14a_le_a n (t n) ω c)
      (fun c₁ c₂ => BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (c₁, c₂))
      (fun x => BAExp14b2B_diag_le (hn (t n) (ht0 n) (ht n)) ω x)
      (BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).L n (t n) q.1 q.2 ω‖) (![σ, !σ], ![a, b]))
  refine BAExp14b2B_core hκ hflow ht0 ht hfacts hP3 (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FT3B sz z n (t n) ω kb v.1 v.2.1 v.2.2) (fun _ _ _ => 0)
    (fun n v ω => BAExp14b_FT3B sz z n (t n) ω kb v.1 v.2.1 v.2.2) (fun n v ω => by simp)
    (fun _ => 0) (fun _ => 0) (fun _ => le_rfl) (fun _ => le_rfl) (Eventually.of_forall fun n v => by simp)
    (BAExp14a_Dom.refl hsz (g := fun _ => (0 : ℝ)) fun _ => le_rfl)
    (fun n ω => S * CM * (BAExp14a_a sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω *
        (((baFMz sz z).eta n (t n))⁻¹ * ((1 + BAExp14a_b sz z n (t n) ω) * Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω))))))
    (fun n => sz.Bctl n (t n) * (sz.Bctl n (t n) * (((baFMz sz z).eta n (t n))⁻¹ *
        ((1 + (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) * Real.sqrt ((sz.Bctl n (t n)) ^ (2 - 1))))))
    hRQ d6 14 ?_ (K := 3 * κ⁻¹ + 1) (by positivity) (Eventually.of_forall fun n => by rw [zero_mul]; exact mul_nonneg (by positivity) (hζ0 n)) ?_
  · -- the envelope `‖T3B‖ ≤ N^14`
    filter_upwards [hRQ, hev, hτenv] with n hR hn hτn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    rintro v ω
    refine (hR v ω).trans ?_
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
    have hN4 : (4 : ℝ) ≤ N := h4
    have hN0 : 0 < N := by linarith
    have hN1 : 1 ≤ N := by linarith
    set E : ℝ := ((baFMz sz z).eta n (t n))⁻¹ with hEdef
    have hE0' : 0 ≤ E := hE0 n
    have hN23 : N ^ 2 + 2 ≤ N ^ 3 := by nlinarith [sq_nonneg N, mul_nonneg hN0.le (sq_nonneg N)]
    have ha : BAExp14a_a sz z n (t n) ω ≤ N ^ 3 := by
      linarith [BAExp14b2B_a_le hκ hflow (ht0 n) (ht n) hf ω]
    have hb : 1 + BAExp14a_b sz z n (t n) ω ≤ N ^ 3 := by
      linarith [BAExp14b2B_b_le hκ hflow (ht0 n) (ht n) hf ω]
    have hLm' : Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω) ≤ N ^ 2 := by
      refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
      refine (BAExp14b2B_Lm_le hκ hflow (ht0 n) (ht n) ω).trans ?_
      calc E ^ 2 ≤ (N ^ 2) ^ 2 := pow_le_pow_left₀ hE0' hηN 2
        _ = _ := by ring
    have hτ' : BAExp14b2B_tw sz z n (t n) ω ≤ N ^ 3 := hτn ω
    have hτ0 : 0 ≤ BAExp14b2B_tw sz z n (t n) ω := BAExp14b2_sup_nonneg fun p => norm_nonneg _
    have ha0 := BAExp14a_a_nonneg (sz := sz) (z := z) n (t n) ω
    have hb0 := BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω
    have hSCN : S * CM ≤ N := by linarith
    calc S * CM * (BAExp14a_a sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω * (E * ((1 + BAExp14a_b sz z n (t n) ω) *
          Real.sqrt (BAExp14b2B_Lm sz z n (t n) ω)))))
        ≤ N * (N ^ 3 * (N ^ 3 * (N ^ 2 * (N ^ 3 * N ^ 2)))) := by gcongr
      _ = N ^ 14 := by ring
  · -- the exponents: `𝔟 · 𝔟 · η⁻¹ (1 + 𝔟^{1/2}) 𝔟^{1/2} ≲ (1 - t)⁻¹ 𝔟^{5/2}`
    filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0', hs2, hBs, hB12, hBsq, h32, h52⟩ := BAExp14b2B_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    have hE1 : ((baFMz sz z).eta n (t n))⁻¹ ≤ κ⁻¹ * (1 - t n)⁻¹ := BAExp14a_eta_inv_le hκ hflow n ht1n
    simp only [Nat.reduceSub, pow_one]
    rw [hB12, hBsq, h52, hBs]
    have e6 : s ^ 6 ≤ 2 * s ^ 5 := by nlinarith [pow_pos hs0' 5]
    have hκ0 : 0 < κ⁻¹ := inv_pos.2 hκ
    calc s ^ 2 * (s ^ 2 * (((baFMz sz z).eta n (t n))⁻¹ * ((1 + s) * s)))
        = ((baFMz sz z).eta n (t n))⁻¹ * (s ^ 5 + s ^ 6) := by ring
      _ ≤ (κ⁻¹ * (1 - t n)⁻¹) * (s ^ 5 + s ^ 6) := mul_le_mul_of_nonneg_right hE1 (by positivity)
      _ ≤ (κ⁻¹ * (1 - t n)⁻¹) * (3 * s ^ 5) := by gcongr; linarith
      _ = (3 * κ⁻¹) * ((1 - t n)⁻¹ * s ^ 5) := by ring
      _ ≤ (3 * κ⁻¹ + 1) * ((1 - t n)⁻¹ * s ^ 5) := by
          have : 0 ≤ (1 - t n)⁻¹ * s ^ 5 := by positivity
          nlinarith

end T3Bmain

/-! ## 4. Target 5: the family `T3C-Ḡ^{(k)}` (I41K twin, `lwExpI41K_holds`, `Graph/LWExpTerm4.lean:1618`) -/

section T3CG

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The split of a three-fold sum `c Σ u X (Y_d + Y_r)` into the part linear in `X` with the weights `D_{a₁} = c Σ u Y_d` and the remainder. -/
theorem BAExp14b2B_split3 {ι : Type*} [Fintype ι] (c : ℂ) (u Yd Yr : ι → ι → ι → ℂ) (X : ι → ℂ) :
    c * ∑ a₁, ∑ c₁, ∑ c₂, u a₁ c₁ c₂ * X a₁ * (Yd a₁ c₁ c₂ + Yr a₁ c₁ c₂) =
      (∑ a₁, (c * ∑ c₁, ∑ c₂, u a₁ c₁ c₂ * Yd a₁ c₁ c₂) * X a₁) + c * ∑ a₁, ∑ c₁, ∑ c₂, u a₁ c₁ c₂ * X a₁ * Yr a₁ c₁ c₂ := by
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
  ring

/-- The deterministic factor of `T3C-Ḡ` after the circle and the splits `𝓛^{(2)} = 𝒦^{(2)} + (𝓛 - 𝒦)`, `L̃ = K̃ + (L̃ - K̃)`:
`𝒦^{(2)} (K̃ - ρ B)`, `ρ = W^{-d} M^{(B)}_{a c₁}`, `B = M^{(B)}`-part of `Tr(G^σ P_{a c₂})`. -/
def BAExp14b2B_Yd (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (σ : Bool) (a b c₁ c₂ : Zd (k + 2) (sz.L n)) : ℂ :=
  (baFMz sz z).K n t ![true, σ] ![b, c₂] * (twK (baFMz sz z) n t ![σ, true] a c₁ c₂ -
    (((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁ * BAExp14b2_Bs z n σ a c₂)

/-- The random factor: `𝒦^{(2)} (L̃ - K̃) + (𝓛 - 𝒦) L̃ - 𝒦^{(2)} ρ T̂ - (𝓛 - 𝒦) ρ Tr(G^σ P)`. -/
def BAExp14b2B_Yr (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a b c₁ c₂ : Zd (k + 2) (sz.L n)) : ℂ :=
  (baFMz sz z).K n t ![true, σ] ![b, c₂] * (twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ - twK (baFMz sz z) n t ![σ, true] a c₁ c₂) +
    ((baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]) * twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ -
    (baFMz sz z).K n t ![true, σ] ![b, c₂] * ((((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁) * BAExp14b2_Th z n t ω σ a c₂ -
    ((baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]) *
      ((((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁) * (BAExp14b2_Th z n t ω σ a c₂ + BAExp14b2_Bs z n σ a c₂)

/-- The weight of `X_{a₁}` in the deterministic part of `T3C-Ḡ`. -/
def BAExp14b2B_Dd (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (kb σ : Bool) (a b a₁ : Zd (k + 2) (sz.L n)) : ℂ :=
  (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ (k + 2)) * ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
    BAExp14b2B_Yd sz z n t σ a b c₁ c₂

/-- The remainder of `T3C-Ḡ`. -/
def BAExp14b2B_Rr (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) : ℂ :=
  (t : ℂ) * (((sz.W n : ℕ) : ℂ) ^ (k + 2)) * ∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
    BAExp14a_X sz z n t ω a₁ * BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂

/-- **The decomposition of `T3C-Ḡ^{(k)}`**: after the block form, the slot-2 circle (`twCirc_holds`) and `Tr(G^σ P) = T̂ + B` (target 1 (a)),
`T3C-Ḡ = Σ_{a₁} D_{a₁} X_{a₁} + R` with the deterministic weights `D` and the pathwise remainder `R`. -/
theorem BAExp14b2B_I41_eq {n : ℕ} (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) :
    BAExp14b_FT3CG sz z n t ω kb σ a b =
      (∑ a₁, BAExp14b2B_Dd sz z n t kb σ a b a₁ * BAExp14a_X sz z n t ω a₁) + BAExp14b2B_Rr sz z n t ω kb σ a b := by
  have hm := hr.1.1
  rw [BAExp14b_FT3CG_block hr ht0 ht1 kb σ a b]
  unfold BAExp14b2B_Dd BAExp14b2B_Rr
  have hpt : ∀ a₁ c₁ c₂ : Zd (k + 2) (sz.L n),
      BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ *
        (baFMz sz z).L n t ![true, σ] ![b, c₂] ω * twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂ =
      BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ *
        (BAExp14b2B_Yd sz z n t σ a b c₁ c₂ + BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂) := by
    intro a₁ c₁ c₂
    have hcirc := twCirc_holds sz n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) ((baFMz sz z).M n)
      (BAExp14b_MB sz z n) (BAExp14b2_M_tie n hm) a c₁ c₂
    have hLt : twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ = twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂ := by
      change twLoopX n (twChg ((baFMz sz z).G n t ω) σ) (twChg ((baFMz sz z).G n t ω) true) a c₁ c₂ = _
      rw [BAExp14b2_twChg_true]
    have hGM : twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).GM n t ω) a c₁ c₂ =
        twLoopX n (twChg ((baFMz sz z).G n t ω) σ) (fun x y => (baFMz sz z).G n t ω x y - (baFMz sz z).M n x y) a c₁ c₂ := rfl
    rw [hGM, hcirc, BAExp14b2_Tsplit n t ω σ a c₂ hm, ← hLt]
    unfold BAExp14b2B_Yd BAExp14b2B_Yr
    ring
  rw [Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => hpt a₁ c₁ c₂]
  exact BAExp14b2B_split3 _ (fun a₁ c₁ c₂ => BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂)
    (fun _ c₁ c₂ => BAExp14b2B_Yd sz z n t σ a b c₁ c₂) (fun _ c₁ c₂ => BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂) (BAExp14a_X sz z n t ω)

end T3CG

section T3CGb

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **The `ℓ¹` bound of the weights `D`** of `T3C-Ḡ` (the deterministic terms `𝔼X · K̃ · 𝒦` and `X · W^{-d}M^{(B)} B · 𝒦`):
`Σ_{a₁} |D_{a₁}| ≤ W^d S C_M C_{K̃} Σ_{c₂}|𝒦^{(2)}_{b c₂}| + S C_M² max|𝒦^{(2)}|`. -/
theorem BAExp14b2B_Dd_le (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) {Ckt yK yW : ℝ}
    (hCkt : ∀ c₁ c₂, ‖twK (baFMz sz z) n t ![σ, true] a c₁ c₂‖ ≤ Ckt)
    (hyK : ∀ c₂, ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yK)
    (hyW : ∑ c₂, ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yW) :
    ∑ a₁, ‖BAExp14b2B_Dd sz z n t kb σ a b a₁‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (S * CM * (Ckt * yW)) + S * CM * (CM * yK) := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hm := hr.1.1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set Wd : ℝ := ((sz.W n : ℕ) : ℝ) ^ (k + 2) with hWd
  have hCkt0 : 0 ≤ Ckt := (norm_nonneg _).trans (hCkt 0 0)
  have hyK0 : 0 ≤ yK := (norm_nonneg _).trans (hyK 0)
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  have hCM0 : 0 ≤ CM := hf.hCM
  have ht1 : t ≤ 1 := hf.ht1.le
  have hYd : ∀ c₁ c₂, ‖BAExp14b2B_Yd sz z n t σ a b c₁ c₂‖ ≤
      Ckt * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ + (yK * Wd⁻¹) * ‖BAExp14b_MB sz z n a c₁‖ := by
    intro c₁ c₂
    unfold BAExp14b2B_Yd
    rw [norm_mul]
    have h1 : ‖twK (baFMz sz z) n t ![σ, true] a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁ *
        BAExp14b2_Bs z n σ a c₂‖ ≤ Ckt + Wd⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ := by
      refine (norm_sub_le _ _).trans (add_le_add (hCkt c₁ c₂) ?_)
      rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
      calc Wd⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ * ‖BAExp14b2_Bs z n σ a c₂‖ ≤ Wd⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ * 1 := by
            gcongr; exact BAExp14b2_Bs_le hf hm σ a c₂
        _ = _ := mul_one _
    calc _ ≤ ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ * (Ckt + Wd⁻¹ * ‖BAExp14b_MB sz z n a c₁‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Ckt * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ + Wd⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ := by
          ring
      _ ≤ _ := by
          have := hyK c₂
          have := norm_nonneg (BAExp14b_MB sz z n a c₁)
          have : 0 ≤ Wd⁻¹ := by positivity
          nlinarith [mul_nonneg ‹0 ≤ Wd⁻¹› (norm_nonneg (BAExp14b_MB sz z n a c₁))]
  have hterm : ∀ a₁, ‖BAExp14b2B_Dd sz z n t kb σ a b a₁‖ ≤ Wd * ∑ c₁, ∑ c₂,
      (Ckt * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖) +
        (yK * Wd⁻¹) * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n a c₁‖)) := by
    intro a₁
    unfold BAExp14b2B_Dd
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_pow, Complex.norm_natCast]
    calc t * Wd * ‖∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14b2B_Yd sz z n t σ a b c₁ c₂‖
        ≤ 1 * Wd * ∑ c₁, ∑ c₂, ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b2B_Yd sz z n t σ a b c₁ c₂‖ := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₂ _ => ?_))
          rw [norm_mul, norm_mul]
      _ ≤ 1 * Wd * ∑ c₁, ∑ c₂, (Ckt * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ *
            ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖) +
          (yK * Wd⁻¹) * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n a c₁‖)) := by
          gcongr with c₁ _ c₂ _
          calc ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b2B_Yd sz z n t σ a b c₁ c₂‖
              ≤ ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ *
                (Ckt * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ + (yK * Wd⁻¹) * ‖BAExp14b_MB sz z n a c₁‖) := by
                gcongr; exact hYd c₁ c₂
            _ = _ := by ring
      _ = _ := by rw [one_mul]
  have hws2 := BAExp14b2_wsum_c2 (BAExp14b_kap sz z n t kb) (BAExp14b_MB sz z n) (S := S) (CM := CM)
    (fun c => BAExp14b2_kap_col hr hf kb c) (fun c => BAExp14b2_MB_col hr hf c)
    (fun c₂ => ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖) (fun c₂ => norm_nonneg _)
  have hws1 := BAExp14b2_wsum_c1 (BAExp14b_kap sz z n t kb) (BAExp14b_MB sz z n) (S := S) (CM := CM)
    (fun c => BAExp14b2_kap_col hr hf kb c) (fun c => BAExp14b2_MB_row hr hf c)
    (fun c₁ => ‖BAExp14b_MB sz z n a c₁‖) (fun c₁ => norm_nonneg _)
  have hrow := BAExp14b2_MB_row hr hf a
  calc ∑ a₁, ‖BAExp14b2B_Dd sz z n t kb σ a b a₁‖ ≤ ∑ a₁, Wd * ∑ c₁, ∑ c₂,
      (Ckt * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖) +
        (yK * Wd⁻¹) * (‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n a c₁‖)) :=
        Finset.sum_le_sum fun a₁ _ => hterm a₁
    _ = Wd * (Ckt * ∑ a₁, ∑ c₁, ∑ c₂, ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ +
        (yK * Wd⁻¹) * ∑ a₁, ∑ c₁, ∑ c₂, ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * ‖BAExp14b_MB sz z n a c₁‖) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ Wd * (Ckt * (S * CM * yW) + (yK * Wd⁻¹) * (S * CM * CM)) := by
        gcongr
        · exact hws2.trans (by gcongr)
        · exact hws1.trans (by gcongr)
    _ = _ := by field_simp

end T3CGb

section T3CGc

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `L̃_{(σ,+)} = Tr(G^σ E_a G P_{c₁c₂})` (`G^+ = G`). -/
theorem BAExp14b2B_Lt_eq {n : ℕ} (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a c₁ c₂ : Zd (k + 2) (sz.L n)) :
    twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ = twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂ := by
  change twLoopX n (twChg ((baFMz sz z).G n t ω) σ) (twChg ((baFMz sz z).G n t ω) true) a c₁ c₂ = _
  rw [BAExp14b2_twChg_true]

/-- **The pointwise bound of `Y_r`** (the four terms `𝒦^{(2)}(L̃ - K̃)`, `(𝓛 - 𝒦) L̃`, `𝒦^{(2)} ρ T̂`, `(𝓛 - 𝒦) ρ Tr(G^σ P)`). -/
theorem BAExp14b2B_Yr_le {n : ℕ} {t : ℝ} {CM S : ℝ} (hf : BAExp14a_Facts sz z n t CM S) (hm : 0 < ((baFMz sz z).m n).im)
    (σ : Bool) (a b c₁ c₂ : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) {lam yK yD τ : ℝ}
    (hlam : ‖twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ - twK (baFMz sz z) n t ![σ, true] a c₁ c₂‖ ≤ lam)
    (hyK : ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yK)
    (hyD : ‖(baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yD)
    (hτ : ‖BAExp14b2_Th z n t ω σ a c₂‖ ≤ τ) :
    ‖BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂‖ ≤ lam * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ +
      yD * ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂‖ +
        ((yK * τ + yD * (τ + 1)) * (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) * ‖BAExp14b_MB sz z n a c₁‖ := by
  unfold BAExp14b2B_Yr
  have hρ : ‖(((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁‖ = (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hThB : ‖BAExp14b2_Th z n t ω σ a c₂ + BAExp14b2_Bs z n σ a c₂‖ ≤ τ + 1 :=
    (norm_add_le _ _).trans (add_le_add hτ (BAExp14b2_Bs_le hf hm σ a c₂))
  have hr0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖ := by positivity
  have hyK0 : 0 ≤ yK := (norm_nonneg _).trans hyK
  have hyD0 : 0 ≤ yD := (norm_nonneg _).trans hyD
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans hτ
  have h1 : ‖(baFMz sz z).K n t ![true, σ] ![b, c₂] * (twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ -
      twK (baFMz sz z) n t ![σ, true] a c₁ c₂)‖ ≤ lam * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ := by
    rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hlam (norm_nonneg _)
  have h2 : ‖((baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]) *
      twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂‖ ≤
      yD * ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂‖ := by
    rw [norm_mul, BAExp14b2B_Lt_eq]; exact mul_le_mul_of_nonneg_right hyD (norm_nonneg _)
  have h3 : ‖(baFMz sz z).K n t ![true, σ] ![b, c₂] * ((((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁) *
      BAExp14b2_Th z n t ω σ a c₂‖ ≤ (yK * τ) * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖) := by
    rw [norm_mul, norm_mul, hρ]
    calc _ ≤ (yK * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖)) * τ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hyK hr0) hτ (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h4 : ‖((baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]) *
      ((((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n a c₁) *
      (BAExp14b2_Th z n t ω σ a c₂ + BAExp14b2_Bs z n σ a c₂)‖ ≤
      (yD * (τ + 1)) * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖) := by
    rw [norm_mul, norm_mul, hρ]
    calc _ ≤ (yD * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖BAExp14b_MB sz z n a c₁‖)) * (τ + 1) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hyD hr0) hThB (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc _ ≤ _ := (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring

/-- **The abstract triple sum of the kernels**: `Σ_{a₁,c₁,c₂} κ_{a₁c₁} M_{c₁c₂} (λ k_{c₂} + y ℓ_{c₁c₂} + c m_{c₁}) ≤ λ S C_M Σ k + y S F + c S C_M Σ m`
(`BAExp14b2_wsum_c2`, `BAExp14b2B_wsum12`, `BAExp14b2_wsum_c1`; columns of `κ` and of `M` and rows of `M` are `≤ S`, `C_M`). -/
theorem BAExp14b2B_sum3 {ι : Type*} [Fintype ι] [Nonempty ι] (κm MB : ι → ι → ℂ) (k2 ma : ι → ℝ) (lt : ι → ι → ℝ)
    {S CM yW F Cm lam yD cc : ℝ} (hκ : ∀ c, ∑ a, ‖κm a c‖ ≤ S) (hMc : ∀ b, ∑ c, ‖MB c b‖ ≤ CM) (hMr : ∀ b, ∑ c, ‖MB b c‖ ≤ CM)
    (hk2 : ∀ c, 0 ≤ k2 c) (hma : ∀ c, 0 ≤ ma c) (hlt : ∀ c₁ c₂, 0 ≤ lt c₁ c₂) (hyW : ∑ c, k2 c ≤ yW)
    (hF : ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * lt c₁ c₂ ≤ F) (hCm : ∑ c, ma c ≤ Cm) (hlam : 0 ≤ lam) (hyD : 0 ≤ yD) (hcc : 0 ≤ cc)
    (hS : 0 ≤ S) (hCM : 0 ≤ CM) :
    ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * (lam * k2 c₂ + yD * lt c₁ c₂ + cc * ma c₁) ≤
      lam * (S * CM * yW) + yD * (S * F) + cc * (S * CM * Cm) := by
  have h2 := BAExp14b2_wsum_c2 κm MB hκ hMc k2 hk2
  have h12 := BAExp14b2B_wsum12 κm MB hκ lt hlt
  have h1 := BAExp14b2_wsum_c1 κm MB hκ hMr ma hma
  have e : ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * (lam * k2 c₂ + yD * lt c₁ c₂ + cc * ma c₁) =
      lam * ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * k2 c₂ +
        yD * ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * (‖MB c₁ c₂‖ * lt c₁ c₂) +
          cc * ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * ma c₁ := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    ring
  rw [e]
  have a1 : ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * k2 c₂ ≤ S * CM * yW := h2.trans (by gcongr)
  have a2 : ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * (‖MB c₁ c₂‖ * lt c₁ c₂) ≤ S * F := h12.trans (by gcongr)
  have a3 : ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * ma c₁ ≤ S * CM * Cm := h1.trans (by gcongr)
  gcongr

end T3CGc

section T3CGd

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **The pathwise bound of the remainder `R` of `T3C-Ḡ`** (the terms (i), (ii) and the fluctuation parts of (iv)):
`‖R‖ ≤ a (S C_M λ̃ (W^d y_W) + S C_M y_Δ A η⁻¹ + S C_M² y_K τ̂ + S C_M² y_Δ (τ̂ + 1))`
for `|X| ≤ a`, `|L̃ - K̃| ≤ λ̃` (TL2 variable), `|𝒦^{(2)}| ≤ y_K`, `|𝓛^{(2)} - 𝒦^{(2)}| ≤ y_Δ`, `Σ_{c₂}|𝒦^{(2)}_{b c₂}| ≤ y_W`, `|G_{xx}| ≤ A`,
`|twTr| ≤ τ̂`: (ii) is the kernel sum `BAExp14b2_wsum_c2` against `y_W`, (i) the twisted fold-plus-Ward sum `BAExp14b2_fold_ward` after
`BAExp14b2B_wsum12`, (iv) the kernel sum `BAExp14b2_wsum_c1` against `W^d · W^{-d}`. -/
theorem BAExp14b2B_Rr_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (kb σ : Bool) (a b : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) {aa lam yK yD yW A τ : ℝ}
    (haa : ∀ c, ‖BAExp14a_X sz z n t ω c‖ ≤ aa)
    (hlam : ∀ c₁ c₂, ‖twL2' (baFMz sz z) n t ω ![σ, true] a c₁ c₂ - twK (baFMz sz z) n t ![σ, true] a c₁ c₂‖ ≤ lam)
    (hyK : ∀ c₂, ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yK)
    (hyD : ∀ c₂, ‖(baFMz sz z).L n t ![true, σ] ![b, c₂] ω - (baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yD)
    (hyW : ∑ c₂, ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ yW)
    (hA : ∀ x, ‖(baFMz sz z).G n t ω x x‖ ≤ A) (hτ : ∀ c₁ c₂, ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ τ) :
    ‖BAExp14b2B_Rr sz z n t ω kb σ a b‖ ≤ aa * (S * CM * (lam * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * yW)) +
      S * CM * (yD * (A * ((baFMz sz z).eta n t)⁻¹)) + S * CM * CM * (yK * τ) + S * CM * CM * (yD * (τ + 1))) := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hm := hr.1.1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have haa0 : 0 ≤ aa := (norm_nonneg _).trans (haa 0)
  have hlam0 : 0 ≤ lam := (norm_nonneg _).trans (hlam 0 0)
  have hyK0 : 0 ≤ yK := (norm_nonneg _).trans (hyK 0)
  have hyD0 : 0 ≤ yD := (norm_nonneg _).trans (hyD 0)
  have hτ0 : 0 ≤ τ := (norm_nonneg _).trans (hτ 0 0)
  have hS0 : 0 ≤ S := by linarith [hf.hS]
  have hCM0 : 0 ≤ CM := hf.hCM
  have ht1 : t ≤ 1 := hf.ht1.le
  have hTh : ∀ c₂, ‖BAExp14b2_Th z n t ω σ a c₂‖ ≤ τ := by
    intro c₂
    cases σ
    · simp only [BAExp14b2_Th, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]; exact hτ a c₂
    · simp only [BAExp14b2_Th, ↓reduceIte]; exact hτ c₂ a
  have hY := fun c₁ c₂ => BAExp14b2B_Yr_le hf hm σ a b c₁ c₂ ω (hlam c₁ c₂) (hyK c₂) (hyD c₂) (hTh c₂)
  have hsum := BAExp14b2B_sum3 (BAExp14b_kap sz z n t kb) (BAExp14b_MB sz z n)
    (fun c₂ => ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖) (fun c₁ => ‖BAExp14b_MB sz z n a c₁‖)
    (fun c₁ c₂ => ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂‖)
    (S := S) (CM := CM) (yW := yW) (lam := lam) (yD := yD)
    (cc := (yK * τ + yD * (τ + 1)) * (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹)
    (fun c => BAExp14b2_kap_col hr hf kb c) (fun c => BAExp14b2_MB_col hr hf c) (fun c => BAExp14b2_MB_row hr hf c)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ _ => norm_nonneg _) hyW
    (BAExp14b2_fold_ward hκ hflow ht0 ht σ a ω hA (BAExp14b_MB sz z n) (fun c => BAExp14b2_MB_row hr hf c) (fun c => BAExp14b2_MB_col hr hf c))
    (BAExp14b2_MB_row hr hf a) hlam0 hyD0 (by positivity) hS0 hCM0
  unfold BAExp14b2B_Rr
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0, norm_pow, Complex.norm_natCast]
  have hnorm : ‖∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ * BAExp14a_X sz z n t ω a₁ *
      BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂‖ ≤ aa * ∑ a₁, ∑ c₁, ∑ c₂, ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ *
        (lam * ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ +
          yD * ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂‖ +
          ((yK * τ + yD * (τ + 1)) * (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) * ‖BAExp14b_MB sz z n a c₁‖) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₁ _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₂ _ => ?_)
    rw [norm_mul, norm_mul, norm_mul]
    have h1 := haa a₁
    have h2 := hY c₁ c₂
    have h3 := norm_nonneg (BAExp14b_kap sz z n t kb a₁ c₁)
    have h4 := norm_nonneg (BAExp14b_MB sz z n c₁ c₂)
    calc _ ≤ ‖BAExp14b_kap sz z n t kb a₁ c₁‖ * ‖BAExp14b_MB sz z n c₁ c₂‖ * aa * _ :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h4)) h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc t * ((sz.W n : ℕ) : ℝ) ^ (k + 2) * ‖∑ a₁, ∑ c₁, ∑ c₂, BAExp14b_kap sz z n t kb a₁ c₁ * BAExp14b_MB sz z n c₁ c₂ *
        BAExp14a_X sz z n t ω a₁ * BAExp14b2B_Yr sz z n t ω σ a b c₁ c₂‖
      ≤ 1 * ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (aa * (lam * (S * CM * yW) + yD * (S * (CM * A * ((((sz.W n : ℕ) : ℝ) ^ (k + 2)) *
        ((baFMz sz z).eta n t))⁻¹)) + ((yK * τ + yD * (τ + 1)) * (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) * (S * CM * CM))) := by
        gcongr
        exact hnorm.trans (by gcongr)
    _ = _ := by
        rw [mul_inv]
        field_simp
        ring

end T3CGd

section T3CGe

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `max_σ |𝒦^{(2)}|` (the deterministic variable `y_K`). -/
def BAExp14b2B_yK (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℝ :=
  BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).K n t q.1 q.2‖)

/-- `max |𝓛^{(2)} - 𝒦^{(2)}|` (the variable `y_Δ`, `STLKgL`). -/
def BAExp14b2B_yD (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).L n t q.1 q.2 ω - (baFMz sz z).K n t q.1 q.2‖)

/-- `max_{σ,b} Σ_x |𝒦^{(2)}_{σ,(b,x)}|` (the variable `y_W`, `STKwardgL`). -/
def BAExp14b2B_yW (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℝ :=
  BAExp14b2_sup (fun p : (Fin 2 → Bool) × (Fin (2 - 1) → Zd (k + 2) (sz.L n)) =>
    ∑ x : Zd (k + 2) (sz.L n), ‖(baFMz sz z).K n t p.1 (fun i : Fin 2 => if h : (i : ℕ) < 2 - 1 then p.2 ⟨i, h⟩ else x)‖)

/-- `max |L̃ - K̃|` (the TL2 variable `λ̃`). -/
def BAExp14b2B_lam (sz : Sizes (k + 2)) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
    ‖twL2' (baFMz sz z) n t ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n t p.1 p.2.1 p.2.2.1 p.2.2.2‖)

/-- The row `(b, x)` of `𝒦^{(2)}` as the vector `![b, x]`. -/
theorem BAExp14b2B_vec_eq {n : ℕ} (b x : Zd (k + 2) (sz.L n)) :
    (fun i : Fin 2 => if h : (i : ℕ) < 2 - 1 then (fun _ : Fin (2 - 1) => b) ⟨i, h⟩ else x) = ![b, x] := by
  funext i; fin_cases i <;> simp

theorem BAExp14b2B_yW_ge {n : ℕ} {t : ℝ} (σ : Bool) (b : Zd (k + 2) (sz.L n)) :
    ∑ c₂, ‖(baFMz sz z).K n t ![true, σ] ![b, c₂]‖ ≤ BAExp14b2B_yW sz z n t := by
  have h := BAExp14b2_le_sup (fun p : (Fin 2 → Bool) × (Fin (2 - 1) → Zd (k + 2) (sz.L n)) =>
    ∑ x : Zd (k + 2) (sz.L n), ‖(baFMz sz z).K n t p.1 (fun i : Fin 2 => if h : (i : ℕ) < 2 - 1 then p.2 ⟨i, h⟩ else x)‖)
    (![true, σ], fun _ => b)
  simp only [BAExp14b2B_vec_eq] at h
  exact h

/-- Arithmetic of the deterministic part: `(𝔟 η⁻¹ + 𝔟) 𝔟^{3/2} ≲ (1 - t)⁻¹ 𝔟^{5/2}`. -/
theorem BAExp14b2B_arithD {B E κi ω1 : ℝ} (hB : 0 < B) (hB2 : B ≤ 2) (hE : E ≤ κi * ω1) (hE0 : 0 ≤ E) (hκi : 0 ≤ κi) (hω : 1 ≤ ω1) :
    (B * E + B ^ (2 - 1)) * B ^ (3 / 2 : ℝ) ≤ (κi + 1) * (ω1 * B ^ (5 / 2 : ℝ)) := by
  obtain ⟨s, hs0, hs2, hBs, hB12, hBsq, h32, h52⟩ := BAExp14b2B_s hB hB2
  simp only [Nat.reduceSub, pow_one]
  rw [h32, h52, hBs]
  have h5 : 0 < s ^ 5 := pow_pos hs0 5
  calc (s ^ 2 * E + s ^ 2) * s ^ 3 = E * s ^ 5 + s ^ 5 := by ring
    _ ≤ (κi * ω1) * s ^ 5 + s ^ 5 := by gcongr
    _ ≤ (κi + 1) * (ω1 * s ^ 5) := by nlinarith [mul_nonneg hκi h5.le, mul_le_mul_of_nonneg_right hω h5.le]

/-- Arithmetic of the random part. -/
theorem BAExp14b2B_arithQ {B E κi ω1 : ℝ} (hB : 0 < B) (hB2 : B ≤ 2) (hE : E ≤ κi * ω1) (hE0 : 0 ≤ E) (hκi : 0 ≤ κi) (hω : 1 ≤ ω1) :
    B * (B ^ (3 / 2 : ℝ) * E + B ^ 2 * ((1 + B ^ (1 / 2 : ℝ)) * E) + B ^ (2 - 1) * B + B ^ 2 * (B + 1)) ≤
      (7 * κi + 13) * (ω1 * B ^ (5 / 2 : ℝ)) := by
  obtain ⟨s, hs0, hs2, hBs, hB12, hBsq, h32, h52⟩ := BAExp14b2B_s hB hB2
  simp only [Nat.reduceSub, pow_one]
  rw [h32, h52, hB12, hBs]
  have h5 : 0 < s ^ 5 := pow_pos hs0 5
  have e6 : s ^ 6 ≤ 2 * s ^ 5 := by nlinarith
  have e7 : s ^ 7 ≤ 4 * s ^ 5 := by nlinarith [mul_nonneg hs0.le h5.le]
  have e8 : s ^ 8 ≤ 8 * s ^ 5 := by nlinarith [mul_nonneg hs0.le h5.le, mul_nonneg (mul_nonneg hs0.le hs0.le) h5.le]
  have hP : E * (s ^ 5 + s ^ 6 + s ^ 7) ≤ (κi * ω1) * (7 * s ^ 5) := by
    calc _ ≤ (κi * ω1) * (s ^ 5 + s ^ 6 + s ^ 7) := mul_le_mul_of_nonneg_right hE (by positivity)
      _ ≤ _ := by gcongr; linarith
  calc s ^ 2 * (s ^ 3 * E + (s ^ 2) ^ 2 * ((1 + s) * E) + s ^ 2 * s ^ 2 + (s ^ 2) ^ 2 * (s ^ 2 + 1))
      = E * (s ^ 5 + s ^ 6 + s ^ 7) + (2 * s ^ 6 + s ^ 8) := by ring
    _ ≤ (κi * ω1) * (7 * s ^ 5) + 12 * s ^ 5 := by linarith
    _ ≤ (7 * κi + 13) * (ω1 * s ^ 5) := by
        nlinarith [mul_nonneg hκi (mul_nonneg (by linarith : (0 : ℝ) ≤ ω1) h5.le), mul_le_mul_of_nonneg_right hω h5.le]

/-- The envelope of the remainder: all factors are polynomial in `N`. -/
theorem BAExp14b2B_envQ {N aa lam Wy yD A E yK τ c₁ c₂ : ℝ} (hN : 8 ≤ N) (haa0 : 0 ≤ aa) (hlam0 : 0 ≤ lam) (hWy0 : 0 ≤ Wy) (hyD0 : 0 ≤ yD)
    (hA0 : 0 ≤ A) (hE0 : 0 ≤ E) (hyK0 : 0 ≤ yK) (hτ0 : 0 ≤ τ) (hc₁0 : 0 ≤ c₁) (hc₂0 : 0 ≤ c₂) (hc₁ : c₁ ≤ N) (hc₂ : c₂ ≤ N)
    (haa : aa ≤ N ^ 3) (hlam : lam ≤ N ^ 5) (hWy : Wy ≤ N ^ 3) (hyD : yD ≤ N ^ 5) (hA : A ≤ N ^ 3) (hE : E ≤ N ^ 2) (hyK : yK ≤ N ^ 2)
    (hτ : τ ≤ N ^ 3) :
    aa * (c₁ * (lam * Wy) + c₁ * (yD * (A * E)) + c₂ * (yK * τ) + c₂ * (yD * (τ + 1))) ≤ N ^ 15 := by
  have hN0 : 0 < N := by linarith
  have h1 : 1 ≤ N := by linarith
  have p : ∀ m : ℕ, 1 ≤ N ^ m := fun m => one_le_pow₀ h1
  have hτ1 : τ + 1 ≤ N ^ 3 + 1 := by linarith
  calc aa * (c₁ * (lam * Wy) + c₁ * (yD * (A * E)) + c₂ * (yK * τ) + c₂ * (yD * (τ + 1)))
      ≤ N ^ 3 * (N * (N ^ 5 * N ^ 3) + N * (N ^ 5 * (N ^ 3 * N ^ 2)) + N * (N ^ 2 * N ^ 3) + N * (N ^ 5 * (N ^ 3 + 1))) := by
        gcongr
    _ ≤ N ^ 3 * (5 * N ^ 11) := by
        gcongr
        have a1 : N * (N ^ 5 * N ^ 3) = N ^ 9 := by ring
        have a2 : N * (N ^ 5 * (N ^ 3 * N ^ 2)) = N ^ 11 := by ring
        have a3 : N * (N ^ 2 * N ^ 3) = N ^ 6 := by ring
        have a4 : N * (N ^ 5 * (N ^ 3 + 1)) = N ^ 9 + N ^ 6 := by ring
        have b9 : N ^ 9 ≤ N ^ 11 := pow_le_pow_right₀ h1 (by norm_num)
        have b6 : N ^ 6 ≤ N ^ 11 := pow_le_pow_right₀ h1 (by norm_num)
        rw [a1, a2, a3, a4]
        linarith
    _ ≤ N ^ 3 * (N * N ^ 11) := by
        gcongr
        linarith
    _ = N ^ 15 := by ring

end T3CGe

section T3CGf

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ}

theorem BAExp14b2B_lam_ge {n : ℕ} {t : ℝ} (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd (k + 2) (sz.L n)) :
    ‖twL2' (baFMz sz z) n t ω σ a c₁ c₂ - twK (baFMz sz z) n t σ a c₁ c₂‖ ≤ BAExp14b2B_lam sz z n t ω :=
  BAExp14b2_le_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
    ‖twL2' (baFMz sz z) n t ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n t p.1 p.2.1 p.2.2.1 p.2.2.2‖) (σ, a, c₁, c₂)

theorem BAExp14b2B_yK_ge {n : ℕ} {t : ℝ} (σ : Fin 2 → Bool) (a : Fin 2 → Zd (k + 2) (sz.L n)) :
    ‖(baFMz sz z).K n t σ a‖ ≤ BAExp14b2B_yK sz z n t :=
  BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).K n t q.1 q.2‖) (σ, a)

theorem BAExp14b2B_yD_ge {n : ℕ} {t : ℝ} (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd (k + 2) (sz.L n)) :
    ‖(baFMz sz z).L n t σ a ω - (baFMz sz z).K n t σ a‖ ≤ BAExp14b2B_yD sz z n t ω :=
  BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).L n t q.1 q.2 ω - (baFMz sz z).K n t q.1 q.2‖) (σ, a)

theorem BAExp14b2B_tw_ge {n : ℕ} {t : ℝ} (ω : sz.SeqΩ) (c₁ c₂ : Zd (k + 2) (sz.L n)) :
    ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ BAExp14b2B_tw sz z n t ω :=
  BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n t ω p.1 p.2‖) (c₁, c₂)

end T3CGf

section T3CGmain

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **Target 5 (the I41K twin `T3C-Ḡ^{(k)}`, `j = 6, 7`)**: for the family `T3C-Ḡ^{(kb)}` of S2, every charge and block pair,
`‖𝔼 T3C-Ḡ‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}` over the carrier `baFMz sz z` and the law `BAExp14a_μ sz`, from `STLocalEntrygL`, `LWAvgLawgL`, `STLKgL`, `BATwistAvgLaw`,
`BATwistLoopLaw` (`STLmaxgL`, `STDecaygL` are not read).  The slot-2 circle (`twCirc_holds`) splits the family into `Σ_{a₁} D_{a₁} X_{a₁} + R`
(`BAExp14b2B_I41_eq`); `D` carries (iii) `𝔼X · K̃ · 𝒦` and the deterministic part of (iv), paid with the sharp P3 (`BAExp14b2B_core`, zero slack);
`R` carries (i) `X · L̃ · (𝓛 - 𝒦)` (fold + Ward), (ii) `X · (L̃ - K̃) · 𝒦` (TL2, `baKward_holds`, zero slack) and the TL1 part of (iv).  Private:
`LWAvgLawgL` is not registered. -/
private theorem BAExp14b2B_T3CG (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) (kb : Bool) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FT3CG sz z n (t n) ω kb p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  obtain ⟨C, hC, hKt, hDlt, hLtenv, hCb⟩ := BAExp14b2_tl2 hk hκ hε h𝔡 hflow ht0 ht hfacts hT2
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hη : ∀ n, 0 < (baFMz sz z).eta n (t n) := fun n => BAExp14a_eta_pos hκ hflow n (ht0 n) (ht n)
  have hE0 : ∀ n, 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := fun n => inv_nonneg.2 (hη n).le
  have hWd0 : ∀ n, 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (k + 2) := fun n => by positivity
  have hWdpos : ∀ n, 0 < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := fun n => by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hs0 : ∀ n, 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := fun n => Real.rpow_nonneg (hB n) _
  have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
  have hSCC : 0 ≤ S * CM * CM := mul_nonneg hSC hCM
  have hSCCs : 0 ≤ S * CM * C := mul_nonneg hSC hC.le
  have hyK0 : ∀ n, 0 ≤ BAExp14b2B_yK sz z n (t n) := fun n => BAExp14b2_sup_nonneg fun q => norm_nonneg _
  have hyW0 : ∀ n, 0 ≤ BAExp14b2B_yW sz z n (t n) := fun n => BAExp14b2_sup_nonneg fun q => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hyD0 : ∀ n ω, 0 ≤ BAExp14b2B_yD sz z n (t n) ω := fun n ω => BAExp14b2_sup_nonneg fun q => norm_nonneg _
  have hlam0 : ∀ n ω, 0 ≤ BAExp14b2B_lam sz z n (t n) ω := fun n ω => BAExp14b2_sup_nonneg fun q => norm_nonneg _
  have hτ0 : ∀ n ω, 0 ≤ BAExp14b2B_tw sz z n (t n) ω := fun n ω => BAExp14b2_sup_nonneg fun q => norm_nonneg _
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts (S * CM * CM + S * CM + 8)
  -- the deterministic variables `y_K`, `y_W` and their `≺`
  have hKb := baKbound_holds (k + 2) (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 2 (by norm_num)
  have hKw := baKward_holds (k + 2) (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 2 le_rfl
  have hDyK := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n))) (_ : sz.SeqΩ) => ‖(baFMz sz z).K n (t n) q.1 q.2‖) _ hKb
  have hDyW := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (p : (Fin 2 → Bool) × (Fin (2 - 1) → Zd (k + 2) (sz.L n))) (_ : sz.SeqΩ) =>
      ∑ x : Zd (k + 2) (sz.L n), ‖(baFMz sz z).K n (t n) p.1 (fun i : Fin 2 => if h : (i : ℕ) < 2 - 1 then p.2 ⟨i, h⟩ else x)‖) _ hKw
  have hDyD := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n))) ω => ‖(baFMz sz z).L n (t n) q.1 q.2 ω - (baFMz sz z).K n (t n) q.1 q.2‖) _
    (hK 2 (by norm_num))
  have hDb := BAExp14a_Dom_b (κ := κ) (ε := ε) (𝔠 := 𝔠) (𝔡 := 𝔡) (BAExp14a_μ sz) t ht1 hE
  have hdW := BAExp14a_Dom.mul hsz (f₁ := fun n _ => ((sz.W n : ℕ) : ℝ) ^ (k + 2)) (f₂ := fun n _ => BAExp14b2B_yW sz z n (t n))
    (fun n _ => hyW0 n) hWd0 (BAExp14a_Dom.refl hsz (g := fun n => ((sz.W n : ℕ) : ℝ) ^ (k + 2)) hWd0) hDyW
  have dWy : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => ((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))
      (fun n => ((baFMz sz z).eta n (t n))⁻¹) :=
    BAExp14a_Dom.mono hsz one_pos hE0 (Eventually.of_forall fun n => by
      have := hWdpos n
      have := hη n
      simp only [Nat.reduceSub, pow_zero, mul_one, one_mul]
      rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (hWdpos n).ne', one_mul]) hdW
  -- the Dom chain of the remainder
  have d1 := BAExp14a_Dom.add hsz (BAExp14a_Dom.refl hsz (g := fun _ => (1 : ℝ)) fun _ => zero_le_one) hDb
  have dT1 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14b2B_lam sz z n (t n) ω)
    (f₂ := fun n _ => ((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))
    (fun n _ => mul_nonneg (hWd0 n) (hyW0 n)) (fun n => Real.rpow_nonneg (hB n) _) hDlt dWy
  have dAE := BAExp14a_Dom.mul hsz (f₁ := fun n ω => 1 + BAExp14a_b sz z n (t n) ω) (f₂ := fun n _ => ((baFMz sz z).eta n (t n))⁻¹)
    (fun n _ => hE0 n) (fun n => add_nonneg zero_le_one (hs0 n)) d1 (BAExp14a_Dom.refl hsz (g := fun n => ((baFMz sz z).eta n (t n))⁻¹) hE0)
  have dT2 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14b2B_yD sz z n (t n) ω)
    (f₂ := fun n ω => (1 + BAExp14a_b sz z n (t n) ω) * ((baFMz sz z).eta n (t n))⁻¹)
    (fun n ω => mul_nonneg (add_nonneg zero_le_one (BAExp14a_b_nonneg n (t n) ω)) (hE0 n)) (fun n => pow_nonneg (hB n) _) hDyD dAE
  have dT3 := BAExp14a_Dom.mul hsz (f₁ := fun n _ => BAExp14b2B_yK sz z n (t n)) (f₂ := fun n ω => BAExp14b2B_tw sz z n (t n) ω)
    hτ0 (fun n => pow_nonneg (hB n) _) hDyK hDτ
  have dτ1 := BAExp14a_Dom.add hsz hDτ (BAExp14a_Dom.refl hsz (g := fun _ => (1 : ℝ)) fun _ => zero_le_one)
  have dT4 := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14b2B_yD sz z n (t n) ω) (f₂ := fun n ω => BAExp14b2B_tw sz z n (t n) ω + 1)
    (fun n ω => add_nonneg (hτ0 n ω) zero_le_one) (fun n => pow_nonneg (hB n) _) hDyD dτ1
  have dBr := BAExp14a_Dom.add hsz (BAExp14a_Dom.add hsz (BAExp14a_Dom.add hsz (BAExp14a_Dom.const_mul hsz hSC
    (fun n => mul_nonneg (Real.rpow_nonneg (hB n) _) (hE0 n)) dT1) (BAExp14a_Dom.const_mul hsz hSC
    (fun n => mul_nonneg (pow_nonneg (hB n) _) (mul_nonneg (add_nonneg zero_le_one (hs0 n)) (hE0 n))) dT2))
    (BAExp14a_Dom.const_mul hsz hSCC (fun n => mul_nonneg (pow_nonneg (hB n) _) (hB n)) dT3))
    (BAExp14a_Dom.const_mul hsz hSCC (fun n => mul_nonneg (pow_nonneg (hB n) _) (add_nonneg (hB n) zero_le_one)) dT4)
  have hBr0 : ∀ n ω, 0 ≤ S * CM * (BAExp14b2B_lam sz z n (t n) ω * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))) +
      S * CM * (BAExp14b2B_yD sz z n (t n) ω * ((1 + BAExp14a_b sz z n (t n) ω) * ((baFMz sz z).eta n (t n))⁻¹)) +
      S * CM * CM * (BAExp14b2B_yK sz z n (t n) * BAExp14b2B_tw sz z n (t n) ω) +
      S * CM * CM * (BAExp14b2B_yD sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω + 1)) := fun n ω => by
    have := hlam0 n ω; have := hyD0 n ω; have := hτ0 n ω; have := hyK0 n; have := hyW0 n; have := hE0 n
    have := BAExp14a_b_nonneg (sz := sz) (z := z) n (t n) ω; have := hWd0 n
    positivity
  have dQ := BAExp14a_Dom.mul hsz (f₁ := fun n ω => BAExp14a_a sz z n (t n) ω) hBr0 hB hDa dBr
  -- the deterministic part
  have dB := BAExp14a_Dom.mul hsz (f₁ := fun n _ => sz.Bctl n (t n))
    (f₂ := fun n _ => ((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))
    (fun n _ => mul_nonneg (hWd0 n) (hyW0 n)) hB (BAExp14a_Dom.refl hsz (g := fun n => sz.Bctl n (t n)) hB) dWy
  have dD := BAExp14a_Dom.add hsz (BAExp14a_Dom.const_mul hsz hSCCs (fun n => mul_nonneg (hB n) (hE0 n)) dB)
    (BAExp14a_Dom.const_mul hsz hSCC (fun n => pow_nonneg (hB n) _) hDyK)
  have hDD : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (S * CM * ((C * sz.Bctl n (t n)) *
      BAExp14b2B_yW sz z n (t n))) + S * CM * (CM * BAExp14b2B_yK sz z n (t n)))
      (fun n => sz.Bctl n (t n) * ((baFMz sz z).eta n (t n))⁻¹ + (sz.Bctl n (t n)) ^ (2 - 1)) :=
    BAExp14a_Dom.of_le hsz (fun n ω => le_of_eq (by unfold BAExp14b2B_yK; ring)) dD
  -- the pathwise bound `‖R‖ ≤ Q`
  have hRQ : ∀ᶠ n in atTop, ∀ (v : Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ),
      ‖BAExp14b2B_Rr sz z n (t n) ω kb v.1 v.2.1 v.2.2‖ ≤ BAExp14a_a sz z n (t n) ω *
        (S * CM * (BAExp14b2B_lam sz z n (t n) ω * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))) +
          S * CM * (BAExp14b2B_yD sz z n (t n) ω * ((1 + BAExp14a_b sz z n (t n) ω) * ((baFMz sz z).eta n (t n))⁻¹)) +
          S * CM * CM * (BAExp14b2B_yK sz z n (t n) * BAExp14b2B_tw sz z n (t n) ω) +
          S * CM * CM * (BAExp14b2B_yD sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω + 1))) := by
    filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ ω
    exact BAExp14b2B_Rr_le hκ hflow (ht0 n) (ht n) (hn (t n) (ht0 n) (ht n)) kb σ a b ω (fun c => BAExp14a_le_a n (t n) ω c)
      (fun c₁ c₂ => BAExp14b2B_lam_ge ω ![σ, true] a c₁ c₂) (fun c₂ => BAExp14b2B_yK_ge ![true, σ] ![b, c₂])
      (fun c₂ => BAExp14b2B_yD_ge ω ![true, σ] ![b, c₂]) (BAExp14b2B_yW_ge σ b)
      (fun x => BAExp14b2B_diag_le (hn (t n) (ht0 n) (ht n)) ω x) (fun c₁ c₂ => BAExp14b2B_tw_ge ω c₁ c₂)
  -- the deterministic `ℓ¹` bound
  have hDn : ∀ᶠ n in atTop, ∀ (v : Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)),
      ∑ a₁, ‖BAExp14b2B_Dd sz z n (t n) kb v.1 v.2.1 v.2.2 a₁‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (S * CM * ((C * sz.Bctl n (t n)) *
        BAExp14b2B_yW sz z n (t n))) + S * CM * (CM * BAExp14b2B_yK sz z n (t n)) := by
    filter_upwards [hfacts, hKt] with n hn hKtn
    rintro ⟨σ, a, b⟩
    exact BAExp14b2B_Dd_le hflow (ht0 n) (hn (t n) (ht0 n) (ht n)) kb σ a b (fun c₁ c₂ => hKtn ![σ, true] a c₁ c₂)
      (fun c₂ => BAExp14b2B_yK_ge ![true, σ] ![b, c₂]) (BAExp14b2B_yW_ge σ b)
  -- the envelopes
  have hyKN : ∀ᶠ n in atTop, BAExp14b2B_yK sz z n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
    have hdk := BAExp14b2_det_ev (y := fun n => BAExp14b2B_yK sz z n (t n)) hsz hDyK one_pos
    filter_upwards [hdk, hev] with n h1 hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    have hN : (8 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by nlinarith
    have hBn : 0 ≤ sz.Bctl n (t n) := hB n
    simp only [Real.rpow_one, Nat.reduceSub, pow_one] at h1
    nlinarith
  have hWyN : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    have hdw := BAExp14b2_det_ev (y := fun n => BAExp14b2B_yW sz z n (t n)) hsz hDyW one_pos
    filter_upwards [hdw, hev] with n h1 hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    simp only [Real.rpow_one, Nat.reduceSub, pow_zero, mul_one] at h1
    calc ((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n) ≤
          ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((sz.size n : ℕ) : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ (k + 2) * (baFMz sz z).eta n (t n))⁻¹)) :=
          mul_le_mul_of_nonneg_left h1 (hWd0 n)
      _ = ((sz.size n : ℕ) : ℝ) * ((baFMz sz z).eta n (t n))⁻¹ := by
          have := (hWdpos n).ne'
          have := (hη n).ne'
          field_simp
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hηN hN0.le
      _ = _ := by ring
  have hyDN : ∀ᶠ n in atTop, ∀ ω, BAExp14b2B_yD sz z n (t n) ω ≤ ((sz.size n : ℕ) : ℝ) ^ 5 := by
    filter_upwards [hyKN, hev] with n hyk hn ω
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    have hN : (8 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by nlinarith
    have hη0 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := hE0 n
    have hηsq : (((baFMz sz z).eta n (t n))⁻¹) ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hη0 hηN 2
    refine BAExp14b2_sup_le fun q => ?_
    have hL := BAExp14b2_L2_le hκ hflow (ht0 n) (ht n) (q.1 0) (q.1 1) (q.2 0) (q.2 1) ω
    rw [← BAExp14b2_vec2 q.1, ← BAExp14b2_vec2 q.2] at hL
    have hKq := BAExp14b2B_yK_ge (z := z) (t := t n) q.1 q.2
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h2 := pow_pos hN0 2
    have h3 := pow_pos hN0 3
    calc _ ≤ ‖(baFMz sz z).L n (t n) q.1 q.2 ω‖ + ‖(baFMz sz z).K n (t n) q.1 q.2‖ := norm_sub_le _ _
      _ ≤ (((baFMz sz z).eta n (t n))⁻¹) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 := add_le_add hL (hKq.trans hyk)
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ 2) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 := by linarith
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 5 := by nlinarith
  have henv : ∀ᶠ n in atTop, ∀ (v : Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ),
      ‖BAExp14b2B_Rr sz z n (t n) ω kb v.1 v.2.1 v.2.2‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 15 := by
    filter_upwards [hRQ, hev, hτenv, hLtenv, hyKN, hWyN, hyDN] with n hR hn hτn hLn hyk hWy hyd
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    intro v ω
    refine (hR v ω).trans ?_
    have hN8 : (8 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by nlinarith
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hN23 : ((sz.size n : ℕ) : ℝ) ^ 2 + 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
      nlinarith [sq_nonneg ((sz.size n : ℕ) : ℝ), mul_nonneg (sub_nonneg.2 hN8) (sq_nonneg ((sz.size n : ℕ) : ℝ))]
    exact BAExp14b2B_envQ hN8 (BAExp14a_a_nonneg n (t n) ω) (hlam0 n ω) (mul_nonneg (hWd0 n) (hyW0 n)) (hyD0 n ω)
      (add_nonneg zero_le_one (BAExp14a_b_nonneg n (t n) ω)) (hE0 n) (hyK0 n) (hτ0 n ω) hSC hSCC (by linarith) (by linarith)
      (by linarith [BAExp14b2B_a_le hκ hflow (ht0 n) (ht n) hf ω]) (hLn ω) hWy (hyd ω)
      (by linarith [BAExp14b2B_b_le hκ hflow (ht0 n) (ht n) hf ω]) hηN hyk (hτn ω)
  -- the exponents
  have hdet : ∀ᶠ n in atTop, (sz.Bctl n (t n) * ((baFMz sz z).eta n (t n))⁻¹ + (sz.Bctl n (t n)) ^ (2 - 1)) *
      (sz.Bctl n (t n)) ^ (3 / 2 : ℝ) ≤ (7 * κ⁻¹ + 13) * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    have hE1 : ((baFMz sz z).eta n (t n))⁻¹ ≤ κ⁻¹ * (1 - t n)⁻¹ := BAExp14a_eta_inv_le hκ hflow n ht1n
    have hκi : 0 < κ⁻¹ := inv_pos.2 hκ
    have hζ : 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (hB n) _)
    refine (BAExp14b2B_arithD (STBctl_pos sz n ht1n) hB2 hE1 (hE0 n) hκi.le hω).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hζ
  have hrnd : ∀ᶠ n in atTop, sz.Bctl n (t n) * ((sz.Bctl n (t n)) ^ (3 / 2 : ℝ) * ((baFMz sz z).eta n (t n))⁻¹ +
      (sz.Bctl n (t n)) ^ 2 * ((1 + (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) * ((baFMz sz z).eta n (t n))⁻¹) +
      (sz.Bctl n (t n)) ^ (2 - 1) * sz.Bctl n (t n) + (sz.Bctl n (t n)) ^ 2 * (sz.Bctl n (t n) + 1)) ≤
      (7 * κ⁻¹ + 13) * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0', hlam⟩, hK0⟩ := hn
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    exact BAExp14b2B_arithQ (STBctl_pos sz n ht1n) hB2 (BAExp14a_eta_inv_le hκ hflow n ht1n) (hE0 n) (inv_pos.2 hκ).le hω
  exact BAExp14b2B_core hκ hflow ht0 ht hfacts hP3 (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FT3CG sz z n (t n) ω kb v.1 v.2.1 v.2.2)
    (fun n v a₁ => BAExp14b2B_Dd sz z n (t n) kb v.1 v.2.1 v.2.2 a₁) (fun n v ω => BAExp14b2B_Rr sz z n (t n) ω kb v.1 v.2.1 v.2.2)
    (fun n v ω => BAExp14b2B_I41_eq (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) (ht0 n) (ht1 n) kb v.1 v.2.1 v.2.2 ω)
    (fun n => ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (S * CM * ((C * sz.Bctl n (t n)) * BAExp14b2B_yW sz z n (t n))) +
      S * CM * (CM * BAExp14b2B_yK sz z n (t n)))
    (fun n => sz.Bctl n (t n) * ((baFMz sz z).eta n (t n))⁻¹ + (sz.Bctl n (t n)) ^ (2 - 1))
    (fun n => add_nonneg (mul_nonneg (hWd0 n) (mul_nonneg hSC (mul_nonneg (mul_nonneg hC.le (hB n)) (hyW0 n))))
      (mul_nonneg hSC (mul_nonneg hCM (hyK0 n))))
    (fun n => add_nonneg (mul_nonneg (hB n) (hE0 n)) (pow_nonneg (hB n) _)) hDn hDD
    (fun n ω => BAExp14a_a sz z n (t n) ω *
        (S * CM * (BAExp14b2B_lam sz z n (t n) ω * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * BAExp14b2B_yW sz z n (t n))) +
          S * CM * (BAExp14b2B_yD sz z n (t n) ω * ((1 + BAExp14a_b sz z n (t n) ω) * ((baFMz sz z).eta n (t n))⁻¹)) +
          S * CM * CM * (BAExp14b2B_yK sz z n (t n) * BAExp14b2B_tw sz z n (t n) ω) +
          S * CM * CM * (BAExp14b2B_yD sz z n (t n) ω * (BAExp14b2B_tw sz z n (t n) ω + 1))))
    (fun n => sz.Bctl n (t n) * ((sz.Bctl n (t n)) ^ (3 / 2 : ℝ) * ((baFMz sz z).eta n (t n))⁻¹ +
      (sz.Bctl n (t n)) ^ 2 * ((1 + (sz.Bctl n (t n)) ^ (1 / 2 : ℝ)) * ((baFMz sz z).eta n (t n))⁻¹) +
      (sz.Bctl n (t n)) ^ (2 - 1) * sz.Bctl n (t n) + (sz.Bctl n (t n)) ^ 2 * (sz.Bctl n (t n) + 1)))
    hRQ dQ 15 henv (K := 7 * κ⁻¹ + 13) (by positivity) hdet hrnd

end T3CGmain

/-! ## 5. Targets 4-5 as the families `j = 4..7`, and target 6: the binding conclusion -/

section Assembly

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- **The eight families**: `‖𝔼 F_j‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}` uniformly in `(j, σ, a, b)`, from the seven premises of S2 (`STDecaygL` is not read). -/
private theorem BAExp14b2B_core8 (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hLm : STLmaxgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Fin 8 × Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  unfold PrecL
  refine BAExp14a_prec_fin (P := BAExp14a_μ sz) hsz (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (ξ := fun j n u (_ : sz.SeqΩ) => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω j u.1 u.2.1 u.2.2 ∂(BAExp14a_μ sz)‖)
    (ζ := fun n (_ : Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) (_ : sz.SeqΩ) =>
      (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) fun j => ?_
  fin_cases j
  · exact BAExp14b2_I1K hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 0 (by decide)
  · exact BAExp14b2_I1K hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 1 (by decide)
  · exact BAExp14b2_I1K hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 2 (by decide)
  · exact BAExp14b2_I1K hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 3 (by decide)
  · exact BAExp14b2B_T3B hk hκ hε h𝔡 hflow ht0 ht hE hA hLm hT1 false
  · exact BAExp14b2B_T3B hk hκ hε h𝔡 hflow ht0 ht hE hA hLm hT1 true
  · exact BAExp14b2B_T3CG hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 false
  · exact BAExp14b2B_T3CG hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1 hT2 true

end Assembly

/-- **Target 6, the binding conclusion** (`lem:LWterm_EXP` at BA, the twisted families; L4b2): `BAExp14bS2 d` for every `d`.  For the eight families
`D1t, D2t, T2a, T2b, T3B^{(k)}, T3C-Ḡ^{(k)}` (`BAExp14bS2Fam`), every charge pair and every block pair, `‖𝔼 F‖ ≺ (1 - t)⁻¹ (W^{-d} B_{t,0})^{5/2}`
on `U_n = {λ²/L^d ≤ 1 - t}`, over the carrier `baFMz sz z` and the law `seqP (sz.withLam 0)`, from the seven premises of `BALWCutExpTw` (the five
Step 1/2 pins, `BATwistAvgLaw`, `BATwistLoopLaw`), as pinned.  The red charge is the conjugate of the blue family at the swapped blocks and the
flipped tail charge (`BAExp14bS2Fam`); the blue families are `BAExp14b2B_core8` (file A for `D1t, D2t, T2a, T2b`, this file for the rest). -/
theorem baExp14bS2_holds (d : ℕ) : BAExp14bS2 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht μ hE hA hLm hK hDec hT1 hT2
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have hk : 1 ≤ k := by omega
  have core := BAExp14b2B_core8 hk hκ hε h𝔡 hflow ht0 ht hE hA hLm hK hT1 hT2
  unfold PrecL at core ⊢
  refine BAExp14a_prec_congr (fun n p ω => ?_) (fun n p ω => rfl)
    (StochDomAt.precomp_param core (fun n (p : {_p : Fin 8 × (Bool × Bool) × (Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ (k + 2) ≤ 1 - t n}) =>
      ((p.1.1, if p.1.2.1.1 then (p.1.2.1.2, p.1.2.2.2, p.1.2.2.1) else (!p.1.2.1.2, p.1.2.2.1, p.1.2.2.2)) :
        Fin 8 × Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))))
  obtain ⟨⟨j, ⟨σc, σo⟩, ⟨ac, ao⟩⟩, hp⟩ := p
  cases σc
  · dsimp only
    simp only [Bool.false_eq_true, ite_false]
    have e : ∀ ω : sz.SeqΩ, BAExp14bS2Fam sz z n (t n) ω j false σo ac ao =
        (starRingEnd ℂ) (BAExp14b_FS2 sz z n (t n) ω j (!σo) ac ao) := fun ω => by simp [BAExp14bS2Fam]
    change ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω j (!σo) ac ao ∂(BAExp14a_μ sz)‖ =
      ‖∫ ω, BAExp14bS2Fam sz z n (t n) ω j false σo ac ao ∂(BAExp14a_μ sz)‖
    simp only [e]
    rw [integral_conj, Complex.norm_conj]
  · dsimp only
    simp only [ite_true]
    rfl

/-! ## 6. Compiled instances (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `t ≡ 1/2`; target 7) -/

end RBM.BA

end
