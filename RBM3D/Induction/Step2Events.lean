/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Core
import RBM3D.Graph.LWPins

/-!
# The grid events, the light-weight premises at a time section, and the light-weight bridges

Paper: arXiv:2507.20274, the proof of Step 2 (Subsection 3.3, `subsec:step2_pf`).  The file
contains the good event of the grid walk (`ST_grid_whp_of_sections`, section 9), `STScaleInv`,
`ST_STprof_pos`, `ST_card_lab_le`, the size data and the premises of the light-weight lemmas at a
time section (`STBdata`, `ST_LW_sections`, the events (E1)-(E5), the closure inequality of the
engine, section 11), and the bridges `STLWB_of_LWterm`, `STLWT_of_LWtermExp` from the
light-weight lemmas to the statements `STLWB`, `STLWT` of Step 2 (section 12).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 9. The good event of the grid walk from single-time statements

`ST_grid_whp_of_sections` turns single-time domination statements of the model, available at
every time section `tt n ∈ [s_n, t_n]` (the shape of the light-weight and martingale statements at a
time `t`), into a `w.h.p.` statement of the grid walk simultaneously for all grid indices
`j ≤ K_n` and all labels (`ST_whp_grid` of section 5 with the per-time `≺` of `ST_PT_of_sections`). -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section GridWhp

variable {d : ℕ} (sz : Sizes d)

/-- Enlarging the control pointwise (eventually in `n`, for all sample points) preserves `Prec`. -/
theorem ST_prec_mono_eventually {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω) (h : sz.Prec ξ ζ) : sz.Prec ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hle] with n hn hle'
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨u, hu⟩
  exact ⟨u, lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hle' u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- Deterministic domination, eventually in `n`, implies `≺` (the eventual form of `prec_of_le`). -/
theorem ST_prec_of_le_ev {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (hle : ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ζ n u ω) :
    sz.Prec ξ ζ := by
  intro τ hτ D _
  filter_upwards [hle] with n hn
  have h1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ.le
  have hempty : badSetAt (sz.size) ξ ζ τ n = ∅ := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    nlinarith [hn u ω, hζ n u ω]
  rw [hempty, measure_empty]
  exact zero_le

/-- The supremum over a finite family of labels of a dominated family is dominated (the union over
the labels is inside `P`): `max_{a,b} 𝓛^{(2)}_{(−,+),(a,b)} ≺ Ψ²` from the entrywise statement. -/
theorem ST_prec_sup {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (ξ : ∀ n, V n → sz.SeqΩ → ℝ) (ζ : ℕ → ℝ) (h : sz.Prec (U := V) ξ (fun n _ _ => ζ n)) :
    sz.Prec (U := fun _ => Unit)
      (fun n _ ω => Finset.univ.sup' Finset.univ_nonempty (fun v : V n => ξ n v ω))
      (fun n _ _ => ζ n) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨_, hu⟩
  obtain ⟨v, -, hv⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).1 hu
  exact ⟨v, hv⟩

/-- **From single-time statements at every time section to the grid walk** (the
`w.h.p.` events of the Grönwall bootstrap in the proof of Step 2).  If, for every time section `tt n ∈ [s_n, t_n]`, the
labelled family `F ≺ Z` holds for the single-time model at `tt` (`Prec`, union over labels inside),
and `K_n · #labels ≤ N^C`, then for every `τ > 0` w.h.p. the grid walk satisfies `F ≤ N^τ Z` at all
grid indices `j ≤ K_n` and all labels simultaneously. -/
theorem ST_grid_whp_of_sections {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop,
      ((((K n + 1) * Fintype.card (V n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ) (hτ : 0 < τ)
    (h : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (U := V) (fun n v ω => F n v (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω))
        (fun n v ω => Z n v (tt n : ℝ) (sz.seqHflow n (tt n : ℝ) ω))) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ∈ Finset.range (K n + 1), ∀ v : V n,
      F n v (gridTime s t K n j) (pathH sz s t K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n j) (pathH sz s t K n j ω)}) := by
  have hPT := ST_PT_of_sections sz (V := V) hst
    (fun n p ω => F n p.2 (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω))
    (fun n p ω => Z n p.2 (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω)) h
  refine ST_whp_grid sz s t K hs hst hK (fun n => Finset.range (K n + 1)) hC0 ?_ F Z hF hZ τ ?_
  · filter_upwards [hcard] with n hn
    simpa using hn
  · intro D hD
    filter_upwards [hPT τ hτ D hD] with n hn j hj v
    exact hn (⟨gridTime s t K n j, ST_gridTime_mem s t K n j (hst n) (hK n)
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))⟩, v)

/-- **A single-time statement at the initial time `s_n` gives the grid walk at the index `0`.** -/
theorem ST_grid_whp_zero {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ) (hτ : 0 < τ)
    (h : sz.Prec (U := V) (fun n v ω => F n v (s n) (sz.seqHflow n (s n) ω))
        (fun n v ω => Z n v (s n) (sz.seqHflow n (s n) ω))) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ v : V n,
      F n v (gridTime s t K n 0) (pathH sz s t K n 0 ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n 0) (pathH sz s t K n 0 ω)}) := by
  have hmain := ST_whp_grid sz s t K hs hst hK (fun _ => {0}) hC0 (by
      filter_upwards [hcard] with n hn
      simpa using hn) F Z hF hZ τ (by
      intro D hD
      filter_upwards [h τ hτ D hD] with n hn j hj v
      have hj0 : j = 0 := by simpa using hj
      subst hj0
      have hg : gridTime s t K n 0 = s n := by simp [gridTime]
      rw [hg]
      refine le_trans (measure_mono ?_) hn
      intro ω hω
      exact ⟨v, hω⟩)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω v
  exact hω 0 (by simp) v

end GridWhp

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section ScaleMoved

variable {d : ℕ} (sz : Sizes d)

/-- `Inv(Kf)`: for every time section `tt` and every `D > 0`, `(eq:LW_assm_exp)` at the scales
`ℓ_n = K_{tt_n}`: `𝓛^{(2)}_{tt,σ,(a,b)} ≺ W^{-d} 𝒯̃^{ℓ}_{tt,D}(|a-b|)` for `σ ∈ {(+,-),(-,+)}`. -/
def STScaleInv (E s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ (tt : ∀ n, TimeIcc s t n) (D : ℝ), 0 < D →
    STLWassmExp sz E (fun n => (tt n : ℝ)) D (fun n => Kf n (tt n : ℝ))


/-- `STprof ≥ 0`, positivity of the profile. -/
theorem ST_STprof_pos (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)) : 0 < STprof sz n u D ℓ a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold STprof
  exact mul_pos (inv_pos.mpr (pow_pos hW d)) (tailW_pos hW _)


/-- The number of labels is polynomial in `N`: `#STLab ≤ N^3` as soon as `N ≥ 4`. -/
theorem ST_card_lab_le (n : ℕ) (hN : 4 ≤ sz.size n) :
    (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
  have hc : Fintype.card (STLab sz n) = 4 * (((sz.L n : ℕ)) ^ d) ^ 2 := by
    simp [STLab, Fintype.card_prod, Zd]
  have hL : (sz.L n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have h1 : (4 : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    have : (((sz.L n : ℕ) : ℝ) ^ d) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hL
    nlinarith [pow_nonneg (Nat.cast_nonneg (sz.L n) : (0 : ℝ) ≤ (sz.L n : ℝ)) d]
  have hN' : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN
  have h2 : 4 * ((sz.size n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by nlinarith [sq_nonneg ((sz.size n : ℕ) : ℝ)]
  rw [hc]
  have : (((4 * (sz.L n ^ d) ^ 2 : ℕ)) : ℝ) = 4 * (((sz.L n : ℕ) : ℝ) ^ d) ^ 2 := by push_cast; ring
  rw [this, show ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 3 by norm_cast]
  exact h1.trans h2

end ScaleMoved

end RBM.Gauss.Sizes

/-! ## 11. The size data and the premises of the light-weight lemmas at a time section

`STBdata` is the deterministic statement on `W^{-d}B_{u,0}` that the assembly needs
(proved as `ST_Bdata_holds` in `Step2Iterate.lean`): `W^{-d} B_{u,0} ≤ (ilambda² W^d)⁻¹ + (N (1-u))⁻¹` with `(eq:WO)`,
`(Main_DEL_COND)`, `Im z ≥ N^{-1+ε}` and `1 - lemT z ≥ Im z/(1+|z|)` (from `msc z + z = -(msc z)⁻¹`);
the lower bound is `B_{u,0} ≥ (ilambda² + 1)⁻¹ ≥ (𝔡^{-2}+1)⁻¹` for `u ∈ [0,1]`.  `ST_LW_sections` verifies, at a
time section, the premises of `STLWT`, `STEMn2Exp` (`(initialGT2)` from the weak law of Step 1
and `(eq:LW_assm_exp)` at the scale family) and returns their conclusions. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

/-- **Size data** (deterministic; `ST_Bdata_holds`; the proof of Step 2 uses it as `c_0 ≳ 1` after (3.38) `lokis2`): for every
flow `z` and time sequence `0 ≤ t_n ≤ lemT(z_n)`, eventually in `n`, for
`0 ≤ u ≤ t_n`: `cB W^{-d} ≤ W^{-d} B_{u,0} ≤ N^{-c}`; `cB` depends on `𝔡` only, `c` on `(𝔠, 𝔡, ε)`. -/
def STBdata (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ cB : ℝ, 0 < cB ∧ ∀ 𝔠 : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
          cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧
            sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section LWsec

variable {d : ℕ} (sz : Sizes d)

/-- `W^d ≤ N = (W L)^d`. -/
theorem ST_Wpow_le_size (n : ℕ) : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
    Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hL) d
  exact_mod_cast h

/-- `W → ∞` from `W ≥ N^𝔠` and `N → ∞`. -/
theorem ST_W_tendsto (hsz : sz.SizeTendsto) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hband : sz.Bandwidth 𝔠) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsz
  exact tendsto_atTop_mono' atTop (by filter_upwards [hband] with n hn using hn) h1

/-- `N^{-c} ≤ W^{-(d c)}` (`N ≥ W^d`). -/
theorem ST_size_rpow_neg_le (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1 := ST_Wpow_le_size sz n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have h2 := Real.rpow_le_rpow_of_nonpos hWd h1 (show -c ≤ 0 by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (-c) ≤ (((sz.W n : ℕ) : ℝ) ^ d) ^ (-c) := h2
    _ = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le]; congr 1; ring

/-- `x^{-d/2} = ((x^d)⁻¹)^{1/2}`. -/
theorem ST_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-(d : ℝ) / 2) = ((x ^ d)⁻¹) ^ (1 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_neg hx, ← Real.rpow_mul hx]
  congr 1; ring

end LWsec

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section LWsec2

variable {d : ℕ} (sz : Sizes d)

/-- `STprof ≤ (1 + cB⁻¹) W^{-d} B_{u,0}` at every `ρ`, for `ℓ ≥ 0` and `D > 0`
(`tailT` is non-increasing, `W^{-D} ≤ 1`, `W^{-d} ≤ cB⁻¹ W^{-d} B_{u,0}`). -/
theorem ST_prof_le_Bctl (n : ℕ) {u D ℓ cB : ℝ} (hcB : 0 < cB) (hℓ : 0 ≤ ℓ) (hD : 0 < D)
    (hb : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u) (a b : Zd d (sz.L n)) :
    STprof sz n u D ℓ a b ≤ (1 + cB⁻¹) * sz.Bctl n u := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hWd : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_pos.mpr (pow_pos hW d)
  have hT : tailT d (sz.L n) (sz.lam n) u (min ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ℓ) ≤
      Bparam d (sz.L n) (sz.lam n) u 0 := by
    rw [← tailT_zero]
    exact tailT_antitone (le_refl _) (le_min hρ0 hℓ)
  have hWD : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  have hmax : tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D
      ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ Bparam d (sz.L n) (sz.lam n) u 0 + 1 := by
    unfold tailW
    have hB0 : 0 ≤ Bparam d (sz.L n) (sz.lam n) u 0 := by
      rw [← tailT_zero]; exact tailT_nonneg (le_refl (0 : ℝ))
    exact max_le (by linarith) (by linarith)
  have hbB : sz.Bctl n u = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0 := rfl
  unfold STprof
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Bparam d (sz.L n) (sz.lam n) u 0 + 1) :=
        mul_le_mul_of_nonneg_left hmax hWd.le
    _ = sz.Bctl n u + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by rw [hbB]; ring
    _ ≤ sz.Bctl n u + cB⁻¹ * sz.Bctl n u := by
        have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * sz.Bctl n u := by
          rw [inv_mul_eq_div, le_div_iff₀ hcB]
          linarith
        linarith
    _ = (1 + cB⁻¹) * sz.Bctl n u := by ring

end LWsec2

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section LWsec3

variable {d : ℕ} (sz : Sizes d)

/-- A flow has `Im z_n > 0` (`Im z ≥ N^{-1+ε} > 0`). -/
theorem ST_flow_im_pos {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im := by
  have h := (hflow.2 n).2.1
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h

/-- `(x^a)^2 = x^{2a}`. -/
theorem ST_rpow_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

/-- `b ≤ N^{-c}` gives `b^{1/4} ≤ W^{-(d c/4)}`. -/
theorem ST_quarter_le (n : ℕ) {b c : ℝ} (hb0 : 0 ≤ b) (hc : 0 ≤ c)
    (hb : b ≤ ((sz.size n : ℕ) : ℝ) ^ (-c)) :
    b ^ (1 / 4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c / 4)) := by
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : b ^ (1 / 4 : ℝ) ≤ (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hb0 hb (by norm_num)
  rw [← Real.rpow_mul hN] at h1
  have h2 := ST_size_rpow_neg_le sz n (c := c / 4) (by linarith)
  have e : -c * (1 / 4 : ℝ) = -(c / 4) := by ring
  rw [e] at h1
  have e2 : -((d : ℝ) * c / 4) = -((d : ℝ) * (c / 4)) := by ring
  rw [e2]
  exact h1.trans h2

/-- **The premises of the light-weight lemmas at a time section, and their conclusions.**
At every time section `tt n ∈ [s_n, t_n]`: `(initialGT2)` follows from the weak law of Step 1
(`(Gtmwc)`, first part, `ε₀ = d c / 4`) and from `(eq:LW_assm_exp)` at the scale family `Kf`
(second part, with `Ψ_t² = (1 + cB⁻¹) W^{-d} B_{t,0}`); the light-weight term and the
quadratic variation obey `lem: EWGn2_N` and `lem: EMn2_N` (third estimate). -/
theorem ST_LW_sections (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (htT : ∀ n, t n ≤ lemT (z n))
    (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ)
    (hKcap : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
      Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u)
    (hinv : STScaleInv sz (STflowE z) s t Kf) (tt : ∀ n, TimeIcc s t n) :
    (∀ D : ℝ, 0 < D →
      sz.Prec (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEGt sz n (STflowE z n) (tt n : ℝ) p.1 p.2 ω‖)
        (fun n p _ => (etaT (STflowE z n) (tt n : ℝ))⁻¹ * (sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1))) ∧
    (∀ D : ℝ, 0 < D →
      sz.Prec (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (fun n p ω => ‖STEEk sz n (STflowE z n) (tt n : ℝ) p.1 p.2.1 p.2.2 ω‖)
        (fun n p ω => (etaT (STflowE z n) (tt n : ℝ))⁻¹ *
          ((sz.Bctl n (tt n : ℝ)) ^ (1 / 2 : ℝ) +
            (STJhat sz n (STflowE z n) D (Kf n (tt n : ℝ)) (tt n : ℝ) ω) ^ 3) *
          (STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2.2 0) (p.2.2 1)) ^ 2)) := by
  classical
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hWt := ST_W_tendsto sz hsz hflow.1.1 hflow.1.2.2.2.1
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hbd : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (tt n : ℝ) ∧
      sz.Bctl n (tt n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c) := by
    filter_upwards [hBd] with n hn
    exact hn (tt n : ℝ) ((hs n).trans (tt n).2.1) (tt n).2.2
  have hcap : ∀ᶠ n in atTop, 0 ≤ Kf n (tt n : ℝ) ∧ Kf n (tt n : ℝ) ≤
      (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) (tt n : ℝ) := by
    filter_upwards [hKcap] with n hn
    exact hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
  have hp : 0 < (d : ℝ) * c := mul_pos hd' hc
  -- the exponent `ε₀` and the control `Ψ`
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : ℝ, ε₀ = (d : ℝ) * c / 4 := ⟨_, rfl⟩
  have hε₀pos : 0 < ε₀ := by rw [hε₀]; positivity
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : ℕ → ℝ,
      Ψ = fun n => Real.sqrt ((1 + cB⁻¹) * sz.Bctl n (tt n : ℝ)) := ⟨_, rfl⟩
  have hbpos : ∀ n, 0 ≤ sz.Bctl n (tt n : ℝ) := fun n =>
    (STBctl_pos sz n (lt_of_le_of_lt (tt n).2.2 (lt_of_le_of_lt (htT n)
      (lemT_lt_one (ST_flow_im_pos sz hflow n))))).le
  have hΨsq : ∀ n, Ψ n ^ 2 = (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ) := by
    intro n
    rw [hΨdef]
    exact Real.sq_sqrt (mul_nonneg (by positivity) (hbpos n))
  have hWbig : ∀ᶠ n in atTop, (1 + cB⁻¹) ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c / 2)).comp hWt).eventually
      (eventually_ge_atTop _)
  have hΨ : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
      Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    filter_upwards [hbd, hWbig, hWt.eventually (eventually_ge_atTop 1)] with n hn hWb hW1
    obtain ⟨hlo, hhi⟩ := hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
    have hΨ0 : 0 ≤ Ψ n := by rw [hΨdef]; exact Real.sqrt_nonneg _
    constructor
    · rw [ST_rpow_neg_half hW.le]
      have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Ψ n ^ 2 := by
        rw [hΨsq]
        calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹
            ≤ (1 + cB⁻¹) * (cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := by
              have : (1 + cB⁻¹) * cB = cB + 1 := by field_simp
              nlinarith [inv_pos.mpr hWd]
          _ ≤ (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ) :=
              mul_le_mul_of_nonneg_left hlo (by positivity)
      calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) ≤ (Ψ n ^ 2) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (inv_nonneg.mpr hWd.le) h1 (by norm_num)
        _ = Ψ n := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_sq hΨ0]
    · have hsq : Ψ n ^ 2 ≤ (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ^ 2 := by
        rw [hΨsq, ST_rpow_sq hW.le]
        have hb' : sz.Bctl n (tt n : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
          hhi.trans (ST_size_rpow_neg_le sz n hc.le)
        calc (1 + cB⁻¹) * sz.Bctl n (tt n : ℝ)
            ≤ ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c / 2) * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) :=
              mul_le_mul hWb hb' (hbpos n) (Real.rpow_nonneg hW.le _)
          _ = ((sz.W n : ℕ) : ℝ) ^ (2 * -ε₀) := by
              rw [← Real.rpow_add hW, hε₀]; congr 1; ring
      exact (pow_le_pow_iff_left₀ hΨ0 (Real.rpow_nonneg hW.le _) (by norm_num)).1 hsq
  -- `(initialGT2)` at the section
  have hInit1 : sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (STflowE z n) (tt n : ℝ) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) := by
    have h1 := StochDomAt.precomp_param
      (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
      (fun n p => (tt n, p.1, p.2))
    refine ST_prec_mono_eventually sz ?_ h1
    filter_upwards [hbd] with n hn u ω
    have hb0 := hbpos n
    have := ST_quarter_le sz n hb0 hc.le hn.2
    rw [hε₀]
    exact this
  have hInit2 : sz.Prec (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2 sz n (STflowE z n) (tt n : ℝ) ω) (fun n _ _ => Ψ n ^ 2) := by
    have h1 := hinv tt 1 one_pos
    have h2 := StochDomAt.precomp_param (V := fun n => Zd d (sz.L n) × Zd d (sz.L n)) h1
      (fun n p => ((⟨![false, true], by simp⟩ : {σ : Fin 2 → Bool // σ 0 ≠ σ 1}), ![p.1, p.2]))
    have h3 : sz.Prec (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖Lloop sz n (STflowE z n) (tt n : ℝ) ![false, true] ![p.1, p.2] ω‖)
        (fun n _ _ => Ψ n ^ 2) := by
      refine ST_prec_mono_eventually sz ?_ h2
      filter_upwards [hbd, hcap] with n hn hcn u ω
      rw [hΨsq]
      exact ST_prof_le_Bctl sz n hcB hcn.1 one_pos hn.1 _ _
    exact ST_prec_sup sz _ _ h3
  have hinit : STInitialGT2 sz (STflowE z) (fun n => (tt n : ℝ)) ε₀ Ψ := ⟨hInit1, hInit2⟩
  have ht0 : ∀ n, 0 ≤ (tt n : ℝ) := fun n => (hs n).trans (tt n).2.1
  have htT' : ∀ n, (tt n : ℝ) ≤ lemT (z n) := fun n => (tt n).2.2.trans (htT n)
  refine ⟨fun D hD => ?_, fun D hD => ?_⟩
  · exact hLWT κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) ht0 htT' ε₀ hε₀pos Ψ hΨ hinit
      (fun n => Kf n (tt n : ℝ)) hcap (hinv tt) D hD
  · exact hEMe κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow (fun n => (tt n : ℝ)) ht0 htT' ε₀ hε₀pos Ψ hΨ hinit
      (fun n => Kf n (tt n : ℝ)) hcap (hinv tt) D hD

end LWsec3

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Infra

variable {d : ℕ} (sz : Sizes d)

/-- `N^a ≤ δ` eventually, for `a < 0`. -/
theorem ST_size_pow_small (hsize : Tendsto sz.size atTop atTop) {a δ : ℝ} (ha : a < 0)
    (hδ : 0 < δ) : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ a ≤ δ := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.2 hsize
  have h2 := (tendsto_rpow_neg_atTop (show 0 < -a by linarith)).comp h1
  filter_upwards [h2.eventually (gt_mem_nhds hδ)] with n hn
  simpa using hn.le

/-- `N^a ≥ M` eventually, for `a > 0`. -/
theorem ST_size_pow_big (hsize : Tendsto sz.size atTop atTop) {a M : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, M ≤ ((sz.size n : ℕ) : ℝ) ^ a := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.2 hsize
  exact ((tendsto_rpow_atTop ha).comp h1).eventually (eventually_ge_atTop M)

theorem ST_card_idx_prod (n : ℕ) :
    Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) = sz.size n ^ 2 := by
  rw [Fintype.card_prod, sz.card_Idx n]; ring

theorem ST_card_idx_prod_le (n : ℕ) (hN : 1 ≤ sz.size n) :
    (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) := by
  rw [ST_card_idx_prod]
  have hN' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN
  push_cast
  rw [show ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (4 : ℕ) by norm_cast]
  exact pow_le_pow_right₀ hN' (by norm_num)

theorem ST_card_fin2_lab_le (n : ℕ) (hN : 4 ≤ sz.size n) :
    (Fintype.card (Fin 2 × STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) := by
  have h1 := ST_card_lab_le sz n hN
  have hN' : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN
  rw [Fintype.card_prod, Fintype.card_fin]
  push_cast
  have e3 : ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (3 : ℕ) := by norm_cast
  have e4 : ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (4 : ℕ) := by norm_cast
  rw [e3] at h1
  rw [e4]
  calc 2 * (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 3 := by
        have : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
        nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (STLab sz n))]
    _ = ((sz.size n : ℕ) : ℝ) ^ 4 := by ring

/-- The grid size `K_n = ⌈N^{C}⌉` and polynomially many labels: `(K_n + 1) #V_n ≤ N^{C+5}`. -/
theorem ST_hcard {V : ℕ → Type} [∀ n, Fintype (V n)] (hsize : Tendsto sz.size atTop atTop)
    {CK : ℝ} (hCK : 0 ≤ CK) (K : ℕ → ℕ)
    (hK : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK⌉₊)
    (hV : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ)) :
    ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (V n) : ℕ)) : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ (CK + 5) := by
  have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.2 hsize
  filter_upwards [hV, h1.eventually (eventually_ge_atTop 3)] with n hn hN3
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hNC : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ CK := Real.one_le_rpow hN1 hCK
  have hKle : (K n : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ CK + 1 := by
    rw [hK n]; exact (Nat.ceil_lt_add_one (by linarith)).le
  push_cast
  have e5 : ((sz.size n : ℕ) : ℝ) ^ (CK + 5) =
      ((sz.size n : ℕ) : ℝ) ^ CK * ((sz.size n : ℕ) : ℝ) ^ (5 : ℝ) := Real.rpow_add (by linarith) _ _
  have e5' : ((sz.size n : ℕ) : ℝ) ^ (5 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 4 * ((sz.size n : ℕ) : ℝ) := by
    rw [show ((sz.size n : ℕ) : ℝ) ^ (5 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (5 : ℕ) by norm_cast]; ring
  have e4 : ((sz.size n : ℕ) : ℝ) ^ (4 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 4 := by norm_cast
  rw [e4] at hn
  rw [e5, e5']
  have hc0 : (0 : ℝ) ≤ (Fintype.card (V n) : ℝ) := Nat.cast_nonneg _
  have hP : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ CK := by linarith
  calc ((K n : ℝ) + 1) * (Fintype.card (V n) : ℝ)
      ≤ (((sz.size n : ℕ) : ℝ) ^ CK + 2) * (((sz.size n : ℕ) : ℝ) ^ 4) :=
        mul_le_mul (by linarith) hn hc0 (by linarith)
    _ ≤ (3 * ((sz.size n : ℕ) : ℝ) ^ CK) * (((sz.size n : ℕ) : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ CK * (((sz.size n : ℕ) : ℝ) ^ 4 * ((sz.size n : ℕ) : ℝ)) := by
        have h4 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 4 := by positivity
        nlinarith [mul_nonneg hP h4]

/-- `Im m(E) ≥ √κ/2` for `|E| ≤ 2 - κ`. -/
theorem ST_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) : Real.sqrt κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h := abs_le.mp hE
    nlinarith [h.1, h.2]
  have : κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- **From the grid endpoint back to the model**. -/
theorem ST_model_le_path (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (hK : ∀ n, K n ≠ 0) (n : ℕ)
    (F Z : ∀ n, ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n u, Measurable (F n u)) (hZ : ∀ n u, Measurable (Z n u)) (τ : ℝ)
    (Bad : Set (PathΩ sz))
    (hBad : {ω : PathΩ sz | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (pathH sz s t K n (K n) ω) <
      F n (t n) (pathH sz s t K n (K n) ω)} ⊆ Bad) :
    Sizes.seqP sz {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (sz.seqHflow n (t n) ω) <
      F n (t n) (sz.seqHflow n (t n) ω)} ≤ pathP sz Bad := by
  have hS : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) H < F n (t n) H} :=
    measurableSet_lt (measurable_const.mul (hZ _ _)) (hF _ _)
  have hlast := gridTime_last s t K n (hK n)
  have hq := ST_pathP_eq_seqP sz s t K n (K n) (hs n) (hst n) (hK n) hS
  rw [hlast] at hq
  exact le_trans (le_of_eq hq.symm) (measure_mono hBad)

end Infra

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Events

variable {d : ℕ} (sz : Sizes d)

/-- `gridTime` at the index `0` is the initial time. -/
theorem ST_gridTime_zero (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) : gridTime s t K n 0 = s n := by
  simp [gridTime]

/-- `Im m(E_n) (1 - u) > 0` for `u ≤ lemT(z_n)` along a flow. -/
theorem ST_flow_eta_pos {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ}
    (hu : u ≤ lemT (z n)) : 0 < (mE (STflowE z n)).im * (1 - u) := by
  have him := ST_flow_im_pos sz hflow n
  have h1 : (0 : ℝ) < (mE (STflowE z n)).im := mE_im_pos (abs_lemE_lt_two him)
  have h2 : u < 1 := lt_of_le_of_lt hu (lemT_lt_one him)
  exact mul_pos h1 (by linarith)

/-- **(E1) The weak local law on the grid** (`lem:newKLK` needs `‖G_u - M‖_max ≤ δ₀`): from
`(Gtmwc)` of Step 1 at every time section. -/
theorem ST_event_weak {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {s t T : ℕ → ℝ} (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hTt : ∀ n, T n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) *
      Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ C₁)
    (hS1W : STStep1Weak sz (STflowE z) s t) {ε₁ δ₀ : ℝ} (hε₁ : 0 < ε₁)
    (hsmall : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ x y,
      ‖STGMM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) x y‖ ≤ δ₀}) := by
  have hmain := ST_grid_whp_of_sections sz
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STGMM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => (sz.Bctl n u) ^ (1 / 4 : ℝ))
    (fun n v u => (STGMM_measurable sz n (STflowE z n) u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := StochDomAt.precomp_param
        (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hS1W
        (fun n p => (⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩, p.1, p.2))
      exact h)
  refine hmain.mono ?_
  filter_upwards [hsmall] with n hn ω hω j hj x y
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (x, y)
  exact h1.trans (hn _ hmem.1 (hmem.2.trans (hTt n)))

/-- **(E3) The light-weight term on the grid** (`lem: EWGn2_N` at every grid time). -/
theorem ST_event_lw (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t T : ℕ → ℝ} (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hTt : ∀ n, T n ≤ t n) (hK : ∀ n, K n ≠ 0)
    (htT : ∀ n, t n ≤ lemT (z n)) (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ}
    (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ)
    (hKcap : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
      Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u)
    (hinv : STScaleInv sz (STflowE z) s t Kf) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (STLab sz n) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) {Λ : ℕ → ℝ} (hΛ : ∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n)
    (D : ℝ) (hD : 0 < D) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (STflowE z n)).im * (1 - gridTime s T K n j)) *
          (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)}) := by
  have hmain := ST_grid_whp_of_sections sz (V := fun n => STLab sz n) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STEGtM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => (etaT (STflowE z n) u)⁻¹ * (sz.Bctl n u) ^ (1 / 2 : ℝ) *
      STprof sz n u D (Kf n u) (v.2 0) (v.2 1))
    (fun n v u => (STEGtM_measurable sz n (STflowE z n) u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (fun tt => by
      have h := (ST_LW_sections sz hLWT hEMe hd hκ hε h𝔡 hflow hs htT hS1W hcB hc hBd Kf hKcap hinv
        (fun n => ⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩)).1 D hD
      exact h)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) i
  refine h1.trans ?_
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have hpos := ST_flow_eta_pos sz hflow n (hmem.2.trans ((hTt n).trans (htT n)))
  have hlt : gridTime s T K n j < 1 := by
    have := lemT_lt_one (ST_flow_im_pos sz hflow n)
    have h3 := hmem.2.trans ((hTt n).trans (htT n))
    linarith
  have e : etaT (STflowE z n) (gridTime s T K n j) =
      (mE (STflowE z n)).im * (1 - gridTime s T K n j) := by unfold etaT; ring
  rw [e]
  have hb := (STBctl_pos sz n hlt).le
  have hnn : 0 ≤ ((mE (STflowE z n)).im * (1 - gridTime s T K n j))⁻¹ *
      (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
      STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le) (Real.rpow_nonneg hb _))
      (ST_STprof_pos sz _ _ _ _ _ _).le
  calc ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((mE (STflowE z n)).im * (1 - gridTime s T K n j))⁻¹ *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1))
      ≤ Λ n * (((mE (STflowE z n)).im * (1 - gridTime s T K n j))⁻¹ *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)) :=
        mul_le_mul_of_nonneg_right (hΛ n) hnn
    _ = Λ n / ((mE (STflowE z n)).im * (1 - gridTime s T K n j)) *
        (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
        STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) := by
        rw [div_eq_mul_inv]; ring

/-- `Ĵ ≥ 0`. -/
theorem ST_JhatM_nonneg (n : ℕ) (E D ℓ u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    0 ≤ STJhatM sz n E D ℓ u H := by
  unfold STJhatM
  refine le_trans ?_ (Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
    ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))
    (Finset.mem_univ ((fun _ => true), (fun _ => 0))))
  exact div_nonneg (norm_nonneg _) (ST_STprof_pos sz _ _ _ _ _ _).le

/-- **(E4) The quadratic variation on the grid** (`lem: EMn2_N`, third estimate, at every grid
time, with the random control `Ĵ` of the grid state). -/
theorem ST_event_mg (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hd : 0 < d)
    {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t T : ℕ → ℝ} (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hTt : ∀ n, T n ≤ t n) (hK : ∀ n, K n ≠ 0)
    (htT : ∀ n, t n ≤ lemT (z n)) (hS1W : STStep1Weak sz (STflowE z) s t) {cB c : ℝ}
    (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ)
    (hKcap : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
      Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u)
    (hinv : STScaleInv sz (STflowE z) s t Kf) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (Fin 2 × STLab sz n) : ℕ)) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) {Λ : ℕ → ℝ} (hΛ : ∀ n, 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n)
    (D : ℝ) (hD : 0 < D) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (STflowE z n)).im * (1 - gridTime s T K n j)) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatM sz n (STflowE z n) D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              (pathH sz s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2}) := by
  have hmain := ST_grid_whp_of_sections sz (V := fun n => Fin 2 × STLab sz n) s T K hs hsT hK hC₁
    hcard
    (fun n v u H => ‖STEEkM sz n (STflowE z n) u H v.1 v.2.1 v.2.2‖)
    (fun n v u H => (etaT (STflowE z n) u)⁻¹ *
      ((sz.Bctl n u) ^ (1 / 2 : ℝ) + (STJhatM sz n (STflowE z n) D (Kf n u) u H) ^ 3) *
      (STprof sz n u D (Kf n u) (v.2.2 0) (v.2.2 1)) ^ 2)
    (fun n v u => (STEEkM_measurable sz n (STflowE z n) u v.1 v.2.1 v.2.2).norm)
    (fun n v u => (((measurable_const.mul (measurable_const.add
      ((STJhatM_measurable sz n (STflowE z n) u D (Kf n u)).pow_const 3))).mul measurable_const)))
    ε₁ hε₁ (fun tt => by
      have h := (ST_LW_sections sz hLWT hEMe hd hκ hε h𝔡 hflow hs htT hS1W hcB hc hBd Kf hKcap hinv
        (fun n => ⟨(tt n : ℝ), (tt n).2.1, (tt n).2.2.trans (hTt n)⟩)).2 D hD
      exact h)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj i
  have h0 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (0, i)
  have h1 := hω j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (1, i)
  have hmem := ST_gridTime_mem s T K n j (hsT n) (hK n) hj
  have hpos := ST_flow_eta_pos sz hflow n (hmem.2.trans ((hTt n).trans (htT n)))
  have hlt : gridTime s T K n j < 1 := by
    have := lemT_lt_one (ST_flow_im_pos sz hflow n)
    have h3 := hmem.2.trans ((hTt n).trans (htT n))
    linarith
  have e : etaT (STflowE z n) (gridTime s T K n j) =
      (mE (STflowE z n)).im * (1 - gridTime s T K n j) := by unfold etaT; ring
  have hb := (STBctl_pos sz n hlt).le
  have hJ := ST_JhatM_nonneg sz n (STflowE z n) D (Kf n (gridTime s T K n j))
    (gridTime s T K n j) (pathH sz s T K n j ω)
  set Zv := ((mE (STflowE z n)).im * (1 - gridTime s T K n j))⁻¹ *
      ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
        (STJhatM sz n (STflowE z n) D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
          (pathH sz s T K n j ω)) ^ 3) *
      STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2 with hZv
  have hZnn : 0 ≤ Zv := mul_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le)
    (add_nonneg (Real.rpow_nonneg hb _) (pow_nonneg hJ 3))) (sq_nonneg _)
  rw [e] at h0 h1
  calc ‖STEEM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖
      ≤ ‖STEEkM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) 0 i.1 i.2‖ +
        ‖STEEkM sz n (STflowE z n) (gridTime s T K n j) (pathH sz s T K n j ω) 1 i.1 i.2‖ :=
        norm_add_le _ _
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * Zv + ((sz.size n : ℕ) : ℝ) ^ ε₁ * Zv := add_le_add h0 h1
    _ = (2 * ((sz.size n : ℕ) : ℝ) ^ ε₁) * Zv := by ring
    _ ≤ Λ n * Zv := mul_le_mul_of_nonneg_right (hΛ n) hZnn
    _ = Λ n / ((mE (STflowE z n)).im * (1 - gridTime s T K n j)) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatM sz n (STflowE z n) D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              (pathH sz s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2 := by
        rw [hZv, div_eq_mul_inv]; ring

/-- **(E2) The initial value on the grid** (`(Eq:Gdecay+IND)` at `s`, `STDecay`, with the floor
`D_i` of the induction hypothesis; the deterministic comparison `hcmp` turns its profile into the
profile of the scale family). -/
theorem ST_event_init {z : ℕ → ℂ} {s T : ℕ → ℝ} (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsT : ∀ n, s n ≤ T n) (hK : ∀ n, K n ≠ 0)
    (hDec : STDecay sz (STflowE z) s) {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C₁)
    {ε₁ : ℝ} (hε₁ : 0 < ε₁) {Di : ℝ} (hDi : 0 < Di) (D : ℝ) (Kf : ℕ → ℝ → ℝ) {a₀ : ℕ → ℝ}
    (hcmp : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
        STWB sz n (s n) (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1)) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ i : STLab sz n,
      ‖STgA sz s T K n (STflowE z n) i.1 i.2 0 ω‖ ≤
        a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)}) := by
  have hmain := ST_grid_whp_zero sz (V := fun n => STLab sz n) s T K hs hsT hK hC₁ hcard
    (fun n v u H => ‖STLKM sz n (STflowE z n) u H v.1 v.2‖)
    (fun n v u H => (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (v.2 0 - v.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (v.2 0 - v.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di))
    (fun n v u => (STLKM_measurable sz n (STflowE z n) u v.1 v.2).norm)
    (fun n v u => measurable_const) ε₁ hε₁ (hDec Di hDi)
  refine hmain.mono ?_
  filter_upwards [hcmp] with n hn ω hω i
  have h1 := hω i
  have e0 := ST_gridTime_zero s T K n
  show ‖STLKM sz n (STflowE z n) (gridTime s T K n 0) (pathH sz s T K n 0 ω) i.1 i.2‖ ≤
    a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)
  rw [e0] at h1 ⊢
  exact h1.trans (hn i)

end Events

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section GoodProb

variable {d : ℕ} (sz : Sizes d)

/-- Union bound over a finite family of labels: `P(B_v) ≤ N^{-D_m}` for all `v`, `#V ≤ N^C` and
`a + C ≤ D_m` give `P(⋃_v B_v) ≤ N^{-a}` (`N ≥ 1`). -/
theorem ST_union_prob {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {V : Type*} [Fintype V]
    (B : V → Set Ω) {N a C Dm : ℝ} (hN : 1 ≤ N) (hcard : (Fintype.card V : ℝ) ≤ N ^ C)
    (hDm : a + C ≤ Dm) (h : ∀ v, P (B v) ≤ ENNReal.ofReal (N ^ (-Dm))) :
    P (⋃ v, B v) ≤ ENNReal.ofReal (N ^ (-a)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hp : (0 : ℝ) ≤ N ^ (-Dm) := Real.rpow_nonneg hN0.le _
  calc P (⋃ v, B v) ≤ ∑ v, P (B v) := measure_iUnion_fintype_le P _
    _ ≤ ∑ _v : V, ENNReal.ofReal (N ^ (-Dm)) := Finset.sum_le_sum fun v _ => h v
    _ = ENNReal.ofReal (Fintype.card V * N ^ (-Dm)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (N ^ C * N ^ (-Dm)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard hp)
    _ ≤ ENNReal.ofReal (N ^ (-a)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Real.rpow_add hN0]
        exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- **The good event of one self-improving step holds with probability `≥ 1 - N^{-D'}`**: the
four `w.h.p.` events (E1)–(E4), the martingale event (E5, probability `N^{-D_m}` per label,
`#labels ≤ N^3`) and the a.e. identities (decomposition and remainder). -/
theorem ST_good_prob (hsize : Tendsto sz.size atTop atTop) (s T : ℕ → ℝ) (K : ℕ → ℕ)
    (E : ℕ → ℝ) (D : ℝ) (Kf : ℕ → ℝ → ℝ) {δ₀ : ℝ} {Λ a₀ r₀ ρ₁ : ℕ → ℝ}
    (Mart Rem : ∀ n, STLab sz n → ℕ → PathΩ sz → ℂ)
    (hw : Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ x y,
      ‖STGMM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) x y‖ ≤ δ₀}))
    (hi : Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ i : STLab sz n,
      ‖STgA sz s T K n (E n) i.1 i.2 0 ω‖ ≤
        a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)}))
    (hl : Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (E n)).im * (1 - gridTime s T K n j)) *
          (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)}))
    (hm : Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (E n)).im * (1 - gridTime s T K n j)) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatM sz n (E n) D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              (pathH sz s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2}))
    (hΔ : ∀ n, 0 ≤ gridStep s T K n)
    {D' Dm ε₁ : ℝ} (hD' : 0 < D') (hDm : D' + 1 + 3 ≤ Dm)
    (hmart : ∀ᶠ n in atTop, ∀ i : STLab sz n, pathP sz {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-Dm)))
    (hΛ : ∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n)
    (hρ : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤
      ρ₁ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) ^ 2)
    (hident : ∀ n (i : STLab sz n), ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
      STgA sz s T K n (E n) i.1 i.2 k ω =
        STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω)
    (hrem : ∀ᶠ n in atTop, ∀ i : STLab sz n, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1))
    (hcardLab : ∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ)) :
    ∀ᶠ n in atTop, pathP sz {ω | ¬ STGoodAt sz s T K n (E n) D
        (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀ (a₀ n) (r₀ n) (ρ₁ n) (Mart n) (Rem n) ω} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := by
  classical
  have h14 := Gauss.HighProbAt.inter hsize
    (Gauss.HighProbAt.inter hsize (Gauss.HighProbAt.inter hsize hw hi) hl) hm
  filter_upwards [h14 (D' + 1) (by linarith), hmart, hρ, hrem, hcardLab,
    hsize.eventually (eventually_two_mul_rpow_le D'), hsize.eventually (eventually_ge_atTop 1)]
    with n h14n hmartn hρn hremn hcardn h2 hN1
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  -- the martingale event
  set Nr : ℝ := ((sz.size n : ℕ) : ℝ) with hNr
  let G14 : Set (PathΩ sz) := {ω | ∀ j, j ≤ K n → ∀ x y,
      ‖STGMM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) x y‖ ≤ δ₀} ∩
    {ω | ∀ i : STLab sz n,
      ‖STgA sz s T K n (E n) i.1 i.2 0 ω‖ ≤
        a₀ n * STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} ∩
    {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEGtM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (E n)).im * (1 - gridTime s T K n j)) *
          (sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1)} ∩
    {ω | ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STEEM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ ≤
        Λ n / ((mE (E n)).im * (1 - gridTime s T K n j)) *
          ((sz.Bctl n (gridTime s T K n j)) ^ (1 / 2 : ℝ) +
            (STJhatM sz n (E n) D (Kf n (gridTime s T K n j)) (gridTime s T K n j)
              (pathH sz s T K n j ω)) ^ 3) *
          STprof sz n (gridTime s T K n j) D (Kf n (gridTime s T K n j)) (i.2 0) (i.2 1) ^ 2}
  let B : STLab sz n → Set (PathΩ sz) := fun i => {ω | ∃ k, k ≤ K n ∧
      Nr ^ ε₁ * (∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ +
        Nr ^ (-Dm)) ^ (1 / 2 : ℝ) < ‖Mart n i k ω‖}
  have hB : pathP sz (⋃ i, B i) ≤ ENNReal.ofReal (Nr ^ (-(D' + 1))) :=
    ST_union_prob (pathP sz) B hN1' hcardn hDm hmartn
  have hae : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (E n) i.1 i.2 k ω =
        STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) := by
    have h1 : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        STgA sz s T K n (E n) i.1 i.2 k ω =
          STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
            ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := ae_all_iff.2 fun i => hident n i
    have h2' : ∀ᵐ ω ∂(pathP sz), ∀ i : STLab sz n, ∀ k, k ≤ K n →
        ‖Rem n i k ω‖ ≤ r₀ n *
          STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) :=
      ae_all_iff.2 fun i => hremn i
    filter_upwards [h1, h2'] with ω a b i k hk
    exact ⟨a i k hk, b i k hk⟩
  have hnull : pathP sz {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (E n) i.1 i.2 k ω =
        STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} = 0 :=
    ae_iff.1 hae
  -- the bad event is contained in the union of the three bad events
  have hsub : {ω | ¬ STGoodAt sz s T K n (E n) D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀
        (a₀ n) (r₀ n) (ρ₁ n) (Mart n) (Rem n) ω} ⊆
      (G14ᶜ ∪ ⋃ i, B i) ∪ {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (E n) i.1 i.2 k ω =
        STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_or,
      not_not] at hcon
    obtain ⟨⟨hG14, hnB⟩, hid⟩ := hcon
    obtain ⟨⟨⟨hweak, hinit⟩, hlw⟩, hmg⟩ := hG14
    refine hω ⟨hweak, hinit, hlw, hmg, ?_, fun i k hk => (hid i k hk).2, fun i k hk => (hid i k hk).1⟩
    intro i k hk
    have hnB' : ω ∉ B i := fun h => hnB ⟨i, h⟩
    simp only [B, Set.mem_setOf_eq, not_exists, not_and, not_lt] at hnB'
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, gridStep s T K n *
        ‖STEEM sz n (E n) (gridTime s T K n j) (pathH sz s T K n j ω) i.1 i.2‖ :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hΔ n) (norm_nonneg _)
    have hρi := hρn i
    have hΛ0 : 0 ≤ Λ n := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans (hΛ n)
    refine (hnB' k hk).trans ?_
    refine mul_le_mul (hΛ n) (Real.rpow_le_rpow (by positivity) ?_ (by norm_num))
      (Real.rpow_nonneg (by positivity) _) hΛ0
    linarith
  have hmeas : pathP sz ((G14ᶜ ∪ ⋃ i, B i) ∪ {ω | ¬ ∀ i : STLab sz n, ∀ k, k ≤ K n →
      (STgA sz s T K n (E n) i.1 i.2 k ω =
        STgA sz s T K n (E n) i.1 i.2 0 ω + ((gridStep s T K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s T K n (E n) i.1 i.2 j ω +
            Rem n i k ω + Mart n i k ω) ∧
      ‖Rem n i k ω‖ ≤ r₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1)}) ≤
      ENNReal.ofReal (Nr ^ (-(D' + 1))) + ENNReal.ofReal (Nr ^ (-(D' + 1))) := by
    refine (measure_union_le _ _).trans ?_
    rw [hnull, add_zero]
    refine (measure_union_le _ _).trans ?_
    exact add_le_add h14n hB
  have hfin : ENNReal.ofReal (Nr ^ (-(D' + 1))) + ENNReal.ofReal (Nr ^ (-(D' + 1))) ≤
      ENNReal.ofReal (Nr ^ (-D')) := by
    have hp : (0 : ℝ) ≤ Nr ^ (-(D' + 1)) := Real.rpow_nonneg (by positivity) _
    rw [← ENNReal.ofReal_add hp hp]
    refine ENNReal.ofReal_le_ofReal ?_
    have := h2
    linarith
  exact (measure_mono hsub).trans (hmeas.trans hfin)

end GoodProb

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Arith

variable {d : ℕ} (sz : Sizes d)

theorem ST_log_le {q r : ℝ} (hq : 0 ≤ q) (hr : 1 ≤ r) : 1 + q + Real.log r ≤ (1 + q) * r := by
  have h := Real.log_le_sub_one_of_pos (show 0 < r by linarith)
  nlinarith

/-- **The closure inequality of the engine from the size data** (proof of Step 2, "`𝔠_d` small"):
`r ≤ b_t^{-𝔠_d}`, `(3C+1) 𝔠_d ≤ 1/60` and `c₁ Λ² (1+q) b_t^{1/60} < 1` give
`c₁ Λ² (1 + q + log r) r^{3C} b^{1/30} < 1` for every `b ≤ b_t`. -/
theorem ST_hsmall_aux {c₁ Λ q C r b bt 𝔠' : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hc₁ : 0 ≤ c₁)
    (hr1 : 1 ≤ r) (hrb : r ≤ bt ^ (-𝔠')) (hb : 0 < b) (hbt : b ≤ bt) (hbt1 : bt ≤ 1)
    (h𝔠 : (3 * C + 1) * 𝔠' ≤ 1 / 60) (hΛq : c₁ * Λ ^ 2 * (1 + q) * bt ^ (1 / 60 : ℝ) < 1) :
    c₁ * Λ ^ 2 * (1 + q + Real.log r) * r ^ (3 * C) * b ^ (1 / 30 : ℝ) < 1 := by
  have hbt0 : 0 < bt := hb.trans_le hbt
  have hlog := ST_log_le hq hr1
  have hrpow : r ^ (3 * C + 1) ≤ bt ^ (-((3 * C + 1) * 𝔠')) := by
    calc r ^ (3 * C + 1) ≤ (bt ^ (-𝔠')) ^ (3 * C + 1) :=
          Real.rpow_le_rpow (by linarith) hrb (by linarith)
      _ = bt ^ (-((3 * C + 1) * 𝔠')) := by
          rw [← Real.rpow_mul hbt0.le]; congr 1; ring
  have hr3 : r ^ (3 * C) * r = r ^ (3 * C + 1) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hb30 : b ^ (1 / 30 : ℝ) ≤ bt ^ (1 / 30 : ℝ) := Real.rpow_le_rpow hb.le hbt (by norm_num)
  have hprod : r ^ (3 * C + 1) * b ^ (1 / 30 : ℝ) ≤ bt ^ (1 / 60 : ℝ) := by
    calc r ^ (3 * C + 1) * b ^ (1 / 30 : ℝ)
        ≤ bt ^ (-((3 * C + 1) * 𝔠')) * bt ^ (1 / 30 : ℝ) :=
          mul_le_mul hrpow hb30 (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg hbt0.le _)
      _ = bt ^ (-((3 * C + 1) * 𝔠') + 1 / 30) := (Real.rpow_add hbt0 _ _).symm
      _ ≤ bt ^ (1 / 60 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hbt0 hbt1 (by linarith)
  have hr0 : 0 ≤ r ^ (3 * C) := Real.rpow_nonneg (by linarith) _
  have hb0 : 0 ≤ b ^ (1 / 30 : ℝ) := Real.rpow_nonneg hb.le _
  have hΛ2 : 0 ≤ c₁ * Λ ^ 2 := mul_nonneg hc₁ (sq_nonneg _)
  calc c₁ * Λ ^ 2 * (1 + q + Real.log r) * r ^ (3 * C) * b ^ (1 / 30 : ℝ)
      ≤ c₁ * Λ ^ 2 * ((1 + q) * r) * r ^ (3 * C) * b ^ (1 / 30 : ℝ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hΛ2) hr0) hb0
    _ = c₁ * Λ ^ 2 * (1 + q) * (r ^ (3 * C + 1) * b ^ (1 / 30 : ℝ)) := by
        rw [← hr3]; ring
    _ ≤ c₁ * Λ ^ 2 * (1 + q) * bt ^ (1 / 60 : ℝ) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hΛ2 (by linarith))
    _ < 1 := hΛq

/-- The engine bound `c₁ Λ² (1 + q + log r) b^{1/5} r^{3C}` is at most `M r^{C_d} b^{1/5}`
(`C_d = 3C + 1`) when `c₁ Λ² (1 + q) ≤ M`. -/
theorem ST_final_cmp {c₁ Λ q C r b M : ℝ} (hq : 0 ≤ q) (hc₁ : 0 ≤ c₁) (hr1 : 1 ≤ r)
    (hb : 0 ≤ b) (hM : c₁ * Λ ^ 2 * (1 + q) ≤ M) :
    c₁ * Λ ^ 2 * (1 + q + Real.log r) * b ^ (1 / 5 : ℝ) * r ^ (3 * C) ≤
      M * (r ^ (3 * C + 1) * b ^ (1 / 5 : ℝ)) := by
  have hlog := ST_log_le hq hr1
  have hr3 : r ^ (3 * C) * r = r ^ (3 * C + 1) := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  have hr0 : 0 ≤ r ^ (3 * C + 1) := Real.rpow_nonneg (by linarith) _
  have hb0 : 0 ≤ b ^ (1 / 5 : ℝ) := Real.rpow_nonneg hb _
  have hr30 : 0 ≤ r ^ (3 * C) := Real.rpow_nonneg (by linarith) _
  have hΛ2 : 0 ≤ c₁ * Λ ^ 2 := mul_nonneg hc₁ (sq_nonneg _)
  calc c₁ * Λ ^ 2 * (1 + q + Real.log r) * b ^ (1 / 5 : ℝ) * r ^ (3 * C)
      ≤ c₁ * Λ ^ 2 * ((1 + q) * r) * b ^ (1 / 5 : ℝ) * r ^ (3 * C) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog hΛ2) hb0) hr30
    _ = c₁ * Λ ^ 2 * (1 + q) * (r ^ (3 * C + 1) * b ^ (1 / 5 : ℝ)) := by
        rw [← hr3]; ring
    _ ≤ M * (r ^ (3 * C + 1) * b ^ (1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hM (mul_nonneg hr0 hb0)

/-- `STprof ≥ (W^d)⁻¹ W^{-D}`. -/
theorem ST_prof_lower (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ STprof sz n u D ℓ a b := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  unfold STprof
  exact mul_le_mul_of_nonneg_left (rpow_neg_le_tailW _) (inv_nonneg.mpr (pow_nonneg hW.le d))

/-- `STprof ≥ N^{-(1+D)}` (`W^d ≤ N`, `W ≤ N`). -/
theorem ST_prof_lower_N (hd : 0 < d) (n : ℕ) {D : ℝ} (hD : 0 ≤ D) (u ℓ : ℝ)
    (a b : Zd d (sz.L n)) : ((sz.size n : ℕ) : ℝ) ^ (-(1 + D)) ≤ STprof sz n u D ℓ a b := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    (le_self_pow₀ hW1 hd.ne').trans (ST_Wpow_le_size sz n)
  have h1 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
    inv_anti₀ (pow_pos hW d) (ST_Wpow_le_size sz n)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    Real.rpow_le_rpow_of_nonpos hW hWN (by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (-(1 + D)) = ((sz.size n : ℕ) : ℝ)⁻¹ * ((sz.size n : ℕ) : ℝ) ^ (-D) := by
        rw [neg_add, Real.rpow_add hN, Real.rpow_neg_one]
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hN.le _) (inv_nonneg.mpr (pow_nonneg hW.le d))
    _ ≤ _ := ST_prof_lower sz n u D ℓ a b

/-- **The product `b^{1/5} P` has a polynomial floor**: `W^{-d} B_{u,0} ≥ cB (W^d)⁻¹` and
`N^{-1} ≤ cB^{1/5}` give `N^{-(D+3)} ≤ (W^{-d}B_{u,0})^{1/5} W^{-d} 𝒯̃^ℓ_{u,D}`. -/
theorem ST_bP_lower (hd : 0 < d) (n : ℕ) {u D ℓ cB : ℝ} (hcB : 0 < cB) (hD : 0 ≤ D)
    (hb : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u)
    (hN : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ cB ^ (1 / 5 : ℝ)) (a b : Zd d (sz.L n)) :
    ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ a b := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
    inv_anti₀ (pow_pos hW d) (ST_Wpow_le_size sz n)
  have hb1 : cB * ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ sz.Bctl n u := by
    rw [Real.rpow_neg_one]
    exact le_trans (mul_le_mul_of_nonneg_left h1 hcB.le) hb
  have hb2 : (cB * ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ)) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow (mul_nonneg hcB.le (Real.rpow_nonneg hN0.le _)) hb1 (by norm_num)
  rw [Real.mul_rpow hcB.le (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le] at hb2
  have hP := ST_prof_lower_N sz hd n hD u ℓ a b
  have hb0 : 0 ≤ sz.Bctl n u :=
    (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg hW.le d))).trans hb
  have e1 : ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) *
      (((sz.size n : ℕ) : ℝ) ^ (-1 * (1 / 5 : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ (-(1 + D))) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  calc ((sz.size n : ℕ) : ℝ) ^ (-(D + 3))
      ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) *
        (((sz.size n : ℕ) : ℝ) ^ (-1 * (1 / 5 : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ (-(1 + D))) := e1
    _ ≤ cB ^ (1 / 5 : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (-1 * (1 / 5 : ℝ)) *
          ((sz.size n : ℕ) : ℝ) ^ (-(1 + D))) :=
        mul_le_mul_of_nonneg_right hN (mul_nonneg (Real.rpow_nonneg hN0.le _)
          (Real.rpow_nonneg hN0.le _))
    _ = (cB ^ (1 / 5 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-1 * (1 / 5 : ℝ))) *
          ((sz.size n : ℕ) : ℝ) ^ (-(1 + D)) := by ring
    _ ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ a b :=
        mul_le_mul hb2 hP (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hb0 _)

end Arith

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section More

variable {d : ℕ} (sz : Sizes d)

theorem ST_gridTime_mono (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n) {j k : ℕ}
    (hjk : j ≤ k) : gridTime s t K n j ≤ gridTime s t K n k := by
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (by linarith) (Nat.cast_nonneg _)
  unfold gridTime
  have : (j : ℝ) ≤ k := by exact_mod_cast hjk
  nlinarith [mul_le_mul_of_nonneg_right this hΔ]

theorem ST_gridStep_nonneg (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hst : s n ≤ t n) :
    0 ≤ gridStep s t K n := div_nonneg (by linarith) (Nat.cast_nonneg _)

/-- `√Δ ≤ N^{-C/2}` for the grid step `Δ = (t - s)/K ≤ 1/K` with `K ≥ N^C`. -/
theorem ST_sqrt_gridStep_le (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {N CK : ℝ} (hN : 1 ≤ N)
    (hts : t n - s n ≤ 1) (hK : N ^ CK ≤ (K n : ℝ)) :
    Real.sqrt (gridStep s t K n) ≤ N ^ (-CK / 2) := by
  have hN0 : 0 < N := by linarith
  have hKpos : 0 < (K n : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hK
  have h1 : gridStep s t K n ≤ N ^ (-CK) := by
    unfold gridStep
    calc (t n - s n) / (K n : ℝ) ≤ 1 / (K n : ℝ) := by gcongr
      _ ≤ 1 / N ^ CK := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) hK
      _ = N ^ (-CK) := by rw [Real.rpow_neg hN0.le, one_div]
  calc Real.sqrt (gridStep s t K n) ≤ Real.sqrt (N ^ (-CK)) := Real.sqrt_le_sqrt h1
    _ = N ^ (-CK / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; congr 1; ring

/-- `N^{-D_m} ≤ (q x)^2` from `N^{-(D+3)} ≤ x`, `q ≥ 1` and `D_m ≥ 2D + 6`. -/
theorem ST_floor_sq {x Dm D N q : ℝ} (hN : 1 ≤ N) (hq : 1 ≤ q) (hx : N ^ (-(D + 3)) ≤ x)
    (hDm : 2 * D + 6 ≤ Dm) : N ^ (-Dm) ≤ (q * x) ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 ≤ N ^ (-(D + 3)) := Real.rpow_nonneg hN0.le _
  have hxx : 0 ≤ x := hx0.trans hx
  calc N ^ (-Dm) ≤ N ^ (2 * (-(D + 3))) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = (N ^ (-(D + 3))) ^ 2 := (ST_rpow_sq hN0.le _).symm
    _ ≤ x ^ 2 := pow_le_pow_left₀ hx0 hx 2
    _ ≤ (q * x) ^ 2 := pow_le_pow_left₀ hxx (le_mul_of_one_le_left hxx hq) 2

/-- `3 + 3/Im m(E) ≤ 3 + 3/(√κ/2)` for `|E| ≤ 2 - κ`. -/
theorem ST_cstar_le {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    3 + 3 * ((mE E).im)⁻¹ ≤ 3 + 3 * (Real.sqrt κ / 2)⁻¹ := by
  have h := ST_mE_im_ge hκ hE
  have hpos : 0 < Real.sqrt κ / 2 := by have := Real.sqrt_pos.2 hκ; linarith
  have := inv_anti₀ hpos h
  linarith

/-- **The initial value, comparison of the profiles** (`(Eq:Gdecay+IND)` at `s` against the
profile of the scale family): `W^{-D_i} ≤ b^{1/5} P` gives
`X (b^{1/5} W^{-d}B_{s,ρ} e^{-(ρ/ℓ_s)^{1/2}} + W^{-D_i}) ≤ 2 X b^{1/5} P`. -/
theorem ST_init_cmp (n : ℕ) {u D ℓ Di X : ℝ} (hX : 0 ≤ X) (hℓ : 0 ≤ ℓ)
    (hb0 : 0 ≤ sz.Bctl n u) (i : STLab sz n)
    (hW : ((sz.W n : ℕ) : ℝ) ^ (-Di) ≤
      (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ (i.2 0) (i.2 1)) :
    X * ((sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      (2 * X * (sz.Bctl n u) ^ (1 / 5 : ℝ)) * STprof sz n u D ℓ (i.2 0) (i.2 1) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hTeq : STWB sz n u (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u
        ((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) := by
    unfold STWB tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]; ring
  have h1 : STWB sz n u (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
      Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) ≤ STprof sz n u D ℓ (i.2 0) (i.2 1) := by
    rw [hTeq]
    unfold STprof
    exact mul_le_mul_of_nonneg_left (le_trans (tailT_antitone (le_min hρ0 hℓ) (min_le_left _ _))
      (le_max_left _ _)) (inv_nonneg.mpr (pow_nonneg hW0.le d))
  have hb5 : 0 ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) := Real.rpow_nonneg hb0 _
  calc X * ((sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Di))
      = X * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * (STWB sz n u (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) + ((sz.W n : ℕ) : ℝ) ^ (-Di)) := by ring
    _ ≤ X * ((sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ (i.2 0) (i.2 1) +
          (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ (i.2 0) (i.2 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 hb5) hW) hX
    _ = (2 * X * (sz.Bctl n u) ^ (1 / 5 : ℝ)) * STprof sz n u D ℓ (i.2 0) (i.2 1) := by ring

end More

end RBM.Gauss.Sizes
/-! ## 12. The bridges from the light-weight lemmas

`STLWB_of_LWterm` and `STLWT_of_LWtermExp` derive the statements `STLWB`, `STLWT` of Step 2 from
the light-weight statements `LWterm`, `LWtermExp` (`Graph/LWPins.lean`).  The differences between
the two statements are:
(1) `STEGtM` and `LWE` differ by a cyclic rotation of the loop (cyclic invariance of the trace)
and the order of the two factors (`STB_EGt_eq_LWE`); (2) `STLWB` binds the control `Ψ` of
`(initialGT2)` to `Ψ_t(0)`, while `LWAssm` takes a separate `Ψ'`: it is `max (Ψ_t(0), W^{-d/2})`
(the window `LWWindow` is strict, `STPsiClass` (3) has a constant; closed with `W → ∞`, which
gives `ε₀ ≤ d/2`); (3) the range of `ℓ` is `∀ᶠ n` in `STLWT` and `∀ n` in `LWAssmExp`: `ℓ` is
replaced by `0` at the finitely many `n < N₀`; (4) `LWterm d` and `LWtermExp d` begin with
`3 ≤ d →`, so the bridges take `(hd : 3 ≤ d)`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Bridges

variable {d : ℕ} (sz : Sizes d)

/-- Transport of `≺` along a pointwise domination of the families (eventually in `n`): every
parameter `u'` of the target family is dominated by a parameter `u` of the source family. -/
private theorem STB_prec_dom {U U' : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    {ξ' ζ' : ∀ n, U' n → sz.SeqΩ → ℝ} (h : sz.Prec ξ ζ)
    (hdom : ∀ᶠ n in atTop, ∀ u' : U' n, ∃ u : U n, (∀ ω, ξ' n u' ω ≤ ξ n u ω) ∧
      ∀ ω, ζ n u ω ≤ ζ' n u' ω) : sz.Prec ξ' ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hdom] with n h1 hn
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨u', hu'⟩ := hω
  obtain ⟨u, h2, h3⟩ := hn u'
  refine ⟨u, ?_⟩
  have hr : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have := mul_le_mul_of_nonneg_left (h3 ω) hr
  linarith [h2 ω]

private theorem STB_trace_six {ι : Type*} [Fintype ι] (P Q R S T U : Matrix ι ι ℂ) :
    (P * (Q * (R * (S * (T * U))))).trace = (T * (U * (P * (Q * (R * S))))).trace := by
  have := Matrix.trace_mul_comm (P * (Q * (R * S))) (T * U)
  simp only [Matrix.mul_assoc] at this ⊢
  exact this

/-- The cyclic rotation of a loop of length three (cyclic invariance of the trace). -/
private theorem STB_loop_rot (n : ℕ) (E u : ℝ) (σ₀ σ₁ : Bool) (a₀ y a₁ : Zd d (sz.L n))
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    STLM sz n E u H ![σ₁, σ₁, σ₀] ![y, a₁, a₀] = STLM sz n E u H ![σ₀, σ₁, σ₁] ![a₀, y, a₁] := by
  unfold STLM loopFine loopM
  simp only [Nat.succ_eq_add_one, zero_add, Nat.reduceAdd, List.ofFn_succ, Fin.isValue,
    Fin.cast_eq_self, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
    List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_assoc]
  exact STB_trace_six _ _ _ _ _ _

/-- **`STEGt = LWE`** (difference (1) of the bridges): the two forms of the light-weight term agree
pointwise. -/
private theorem STB_EGt_eq_LWE (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : STEGt sz n E t σ a ω = LWE sz n E t σ a ω := by
  unfold STEGt STEGtM LWE LWcut
  have hm : ∀ s : Bool, STmsig E s = mSigma E s := fun s => rfl
  have h1 : ∀ s : Bool, (fun _ : Fin 1 => s) = ![s] := fun s => by
    funext i; fin_cases i; rfl
  have h1' : ∀ x : Zd d (sz.L n), (fun _ : Fin 1 => x) = ![x] := fun x => by
    funext i; fin_cases i; rfl
  simp only [STavgM, STLM_seqHflow, hm, h1, h1']
  have hA : ∀ x y : Zd d (sz.L n),
      (Lloop sz n E t ![σ 0] ![x] ω - mSigma E (σ 0)) * SB d (sz.L n) (sz.lam n) x y *
        Lloop sz n E t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω =
      SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E t ![σ 0] ![x] ω - mSigma E (σ 0)) *
        Lloop sz n E t ![σ 0, σ 0, σ 1] ![y, a 0, a 1] ω := fun x y => by ring
  have hB : ∀ x y : Zd d (sz.L n),
      (Lloop sz n E t ![σ 1] ![x] ω - mSigma E (σ 1)) * SB d (sz.L n) (sz.lam n) x y *
        Lloop sz n E t ![σ 0, σ 1, σ 1] ![a 0, y, a 1] ω =
      SB d (sz.L n) (sz.lam n) x y * (Lloop sz n E t ![σ 1] ![x] ω - mSigma E (σ 1)) *
        Lloop sz n E t ![σ 1, σ 1, σ 0] ![y, a 1, a 0] ω := fun x y => by
    have := STB_loop_rot sz n E t (σ 0) (σ 1) (a 0) y (a 1) (sz.seqHflow n t ω)
    simp only [STLM_seqHflow] at this
    rw [this]; ring
  simp only [Finset.sum_add_distrib, hA, hB]
  ring

/-- `W^{-d/2}` exceeds `W^{-ε₀}` only if `ε₀ ≤ d/2`: `STPsiClass` (3) at `C = 0` and `W → ∞`. -/
private theorem STB_eps_le {ε₀ : ℝ} {Ψ : ℕ → ℕ → ℝ} (hΨ : STPsiClass sz ε₀ Ψ)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop) : ε₀ ≤ (d : ℝ) / 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc, hev⟩ := hΨ.2.2.1 0
  have hδ : 0 < ε₀ - (d : ℝ) / 2 := by linarith
  have hlim := (tendsto_rpow_neg_atTop hδ).comp hW
  have hc' : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ - (d : ℝ) / 2)) < c :=
    hlim.eventually (gt_mem_nhds hc)
  have h1 : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hW.eventually_ge_atTop 1
  obtain ⟨n, h⟩ := (hev.and (hc'.and h1)).exists
  obtain ⟨⟨hn1, _⟩, hn2, hn3⟩ := h
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have ha : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos hWpos _
  have hΨ0 := (hΨ.1 n 0).2
  have hsplit : ((sz.W n : ℕ) : ℝ) ^ (-ε₀) = ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) *
      ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ - (d : ℝ) / 2)) := by
    rw [← Real.rpow_add hWpos]; congr 1; ring
  have h2 : c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n 0 := (le_inv_mul_iff₀ hc).1 hn1
  rw [hsplit] at hΨ0
  have h3 : c * ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ - (d : ℝ) / 2)) :=
    h2.trans hΨ0
  have h4 : c ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₀ - (d : ℝ) / 2)) := by
    by_contra hh
    push Not at hh
    nlinarith
  linarith

end Bridges

/-- **Bridge `lem:LWterm` ⇒ `STLWB`** (with `(hd : 3 ≤ d)`): with
`Φ_t(r) = Ψ_t(⌊r⌋₊)` and `Ψ' = max (Ψ_t(0), W^{-d/2})` the hypotheses of `LWAssm` follow from
`STPsiClass`, `STInitialGT2`, `STLWassm`, and the conclusion of `LWterm` is that of `STLWB` after
`STB_EGt_eq_LWE`. -/
theorem STLWB_of_LWterm {d : ℕ} (hd : 3 ≤ d) : LWterm d → STLWB d := by
  intro hLW κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hΨ hinit hassm
  have hWt := ST_W_tendsto sz hflow.1.2.2.1 hflow.1.1 hflow.1.2.2.2.1
  have hε₀d := STB_eps_le sz hΨ hWt
  obtain ⟨hΨ1, hΨ2, hΨ3, C₁, C₂, hC₁, hC₂, hΨ4⟩ := hΨ
  choose c hc hev using hΨ3
  set Ψ' : ℕ → ℝ := fun n => max (Ψ n 0) (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) with hΨ'
  set Φ : ℕ → ℝ → ℝ := fun n r => Ψ n ⌊r⌋₊ with hΦ
  have hΦ0 : ∀ n, Φ n 0 = Ψ n 0 := fun n => by simp [hΦ]
  have hΦk : ∀ n (k : ℕ), Φ n (k : ℝ) = Ψ n k := fun n k => by simp [hΦ]
  have hWge : ∀ᶠ n in atTop, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWt.eventually_ge_atTop 1
  have hwin : LWWindow sz ε₀ Ψ' := by
    filter_upwards [hWge] with n hn
    refine ⟨le_max_right _ _, max_le (hΨ1 n 0).2 ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)
  have hAssm : LWAssm sz (STflowE z) t ε₀ Ψ' Φ (C₁ * (2 : ℝ) ^ C₂) C₂ (c 0)⁻¹
      (fun C => (c ⌈C⌉₊)⁻¹) := by
    refine ⟨hε₀, hwin, ⟨hinit.1, ?_⟩, ⟨?_, inv_pos.mpr (hc 0), ?_⟩, ⟨?_, ?_, hC₂, ?_, ?_⟩, ?_⟩
    · refine STB_prec_dom sz hinit.2 (Eventually.of_forall fun n u' => ⟨u', fun ω => le_rfl, fun ω => ?_⟩)
      exact pow_le_pow_left₀ (hΨ1 n 0).1.le (le_max_left _ _) 2
    · exact Eventually.of_forall fun n r _ => hΨ1 n _
    · filter_upwards [hev 0] with n hn
      rw [hΦ0]; exact hn.1
    · intro n x _ y _ hxy
      exact hΨ2 n _ _ (Nat.floor_le_floor hxy)
    · have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ C₂ := Real.one_le_rpow (by norm_num) (by linarith)
      nlinarith
    · intro C _
      filter_upwards [hev ⌈C⌉₊] with n hn ℓ hℓ0 hℓC
      have hfl : ⌊ℓ⌋₊ ≤ ⌈C⌉₊ := (Nat.floor_le_floor hℓC).trans (Nat.floor_le_ceil C)
      have := hn.2 ⌊ℓ⌋₊ hfl
      rw [hΦ0]
      exact (le_inv_mul_iff₀ (hc _)).2 this
    · refine Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_
      have hr1 : 1 ≤ ⌊ℓ₁⌋₊ := Nat.le_floor (by simpa using h1)
      have hr12 : ⌊ℓ₁⌋₊ ≤ ⌊ℓ₂⌋₊ := Nat.floor_le_floor h12
      have hr1pos : (0 : ℝ) < (⌊ℓ₁⌋₊ : ℝ) := by exact_mod_cast hr1
      have hℓ₁pos : (0 : ℝ) < ℓ₁ := by linarith
      have hℓ₂pos : (0 : ℝ) < ℓ₂ := by linarith
      have hD := hΨ4 n ⌊ℓ₁⌋₊ ⌊ℓ₂⌋₊ hr1 hr12
      have hΨ2pos := (hΨ1 n ⌊ℓ₂⌋₊).1
      have hlow : ℓ₁ / 2 ≤ (⌊ℓ₁⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one ℓ₁
        have h1' : (1 : ℝ) ≤ (⌊ℓ₁⌋₊ : ℝ) := by exact_mod_cast hr1
        linarith
      have hup : (⌊ℓ₂⌋₊ : ℝ) ≤ ℓ₂ := Nat.floor_le hℓ₂pos.le
      have hq : (⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ) ≤ 2 * (ℓ₂ / ℓ₁) := by
        calc (⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ) ≤ ℓ₂ / (ℓ₁ / 2) := by
              exact div_le_div₀ hℓ₂pos.le hup (by linarith) hlow
          _ = 2 * (ℓ₂ / ℓ₁) := by field_simp
      have hpow : ((⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ)) ^ C₂ ≤ (2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂ := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hq (by linarith)
      rw [div_le_iff₀ hΨ2pos] at hD
      show Ψ n ⌊ℓ₁⌋₊ ≤ C₁ * (2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂ * Ψ n ⌊ℓ₂⌋₊
      calc Ψ n ⌊ℓ₁⌋₊ ≤ C₁ * (((⌊ℓ₂⌋₊ : ℝ) / (⌊ℓ₁⌋₊ : ℝ)) ^ C₂) * Ψ n ⌊ℓ₂⌋₊ := hD
        _ ≤ C₁ * ((2 : ℝ) ^ C₂ * (ℓ₂ / ℓ₁) ^ C₂) * Ψ n ⌊ℓ₂⌋₊ := by
          gcongr
        _ = _ := by ring
    · refine STB_prec_dom sz hassm (Eventually.of_forall fun n u' => ?_)
      refine ⟨(⟨![u'.1, !u'.1], by cases u'.1 <;> simp⟩, ![u'.2.1, u'.2.2]), fun ω => le_rfl, fun ω => ?_⟩
      simp [hΦk]
  have hmain := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ _ _ _ _ Ψ' Φ hAssm
  refine STB_prec_dom sz hmain (Eventually.of_forall fun n u' => ⟨u', fun ω => ?_, fun ω => ?_⟩)
  · rw [STB_EGt_eq_LWE]
  · rw [hΦ0, hΦk]

/-- **Bridge `lem: EWGn2_N` ⇒ `STLWT`** (difference (3); `(hd : 3 ≤ d)`): `ℓ` is replaced by `ℓ' = 0` at the finitely many `n < N₀` where the eventual range of `ℓ`
may fail (`0` is in the range since `(log W)^{10} ≥ 0` and `ellT ≥ 0`); `≺` does not see finitely
many `n` (`STB_prec_dom` with an eventual domination). -/
theorem STLWT_of_LWtermExp {d : ℕ} (hd : 3 ≤ d) : LWtermExp d → STLWT d := by
  intro hLW κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ hwin hinit ℓ hℓ hexp D hD
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hℓ
  set ℓ' : ℕ → ℝ := fun n => if n < N₀ then 0 else ℓ n with hℓ'
  have hℓ'eq : ∀ n, N₀ ≤ n → ℓ' n = ℓ n := fun n hn => by simp [hℓ', not_lt.2 hn]
  have hnn : ∀ n, 0 ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
      ellT (sz.L n) (sz.lam n) (t n) := fun n =>
    mul_nonneg (Even.pow_nonneg (by decide) _) ellT_nonneg
  have hAssm : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ' := by
    refine ⟨hε₀, hwin, hinit, ?_, ?_, ?_⟩
    · intro n
      by_cases h : n < N₀
      · simp [hℓ', h]
      · rw [hℓ'eq n (not_lt.1 h)]; exact (hN₀ n (not_lt.1 h)).1
    · intro n
      by_cases h : n < N₀
      · simpa [hℓ', h] using hnn n
      · rw [hℓ'eq n (not_lt.1 h)]; exact (hN₀ n (not_lt.1 h)).2
    · intro D' hD'
      refine STB_prec_dom sz (hexp D' hD') (Filter.eventually_atTop.2 ⟨N₀, fun n hn u' => ?_⟩)
      refine ⟨(⟨![u'.1, !u'.1], by cases u'.1 <;> simp⟩, ![u'.2.1, u'.2.2]), fun ω => le_rfl,
        fun ω => ?_⟩
      simp [STprof, hℓ'eq n hn]
  have hmain := hLW hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ' hAssm D hD
  refine STB_prec_dom sz hmain (Filter.eventually_atTop.2 ⟨N₀, fun n hn u' => ⟨u', fun ω => ?_,
    fun ω => ?_⟩⟩)
  · rw [STB_EGt_eq_LWE]
  · simp [STprof, hℓ'eq n hn]






end RBM.Gauss.Sizes
