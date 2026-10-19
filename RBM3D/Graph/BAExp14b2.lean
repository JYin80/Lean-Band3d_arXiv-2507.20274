/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14b
import RBM3D.BA.TwistFold2
import RBM3D.BA.KBound
import RBM3D.BA.TwistAvgB

/-!
# The twisted bridges, the sharp average and the families `D1t, D2t, T2a, T2b` (file A)

Paper: Subappendix B.1: (B.1) `eq:ELW_term`, (B.2) `eq:termI1`, (B.20) `GGGamma`.  The statement
`BAExp14bS2` (`Graph/BAExp14b.lean`) is proved in two files.  This file holds the twisted bridges
and sums, the sharp average `‖𝔼 X_c‖ ≺ 𝔟^{3/2}`, and the families `D1t, D2t, T2a, T2b`.  File B
(`Graph/BAExp14b2B.lean`) holds `T3B`, `T3C-Ḡ` and the conclusion.

Stem `BAExp14b2_`.  Helpers with a Step 1/2 or twisted-law binder are `private`; the helpers
without such a binder are public with the stem.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.setOption false

open private BAExp14a_q_prec BAExp14a_Dom_a from RBM3D.Graph.BAExp14aB

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The twisted bridges -/

section Bridges

variable {d : ℕ}

/-- **Bridge (a)**: `Tr(G P_{ac}) = Tr(Ǧ P_{ac}) + M^{(B)}_{ca}`, i.e. `twTrP n G a c = twTr c a + twMB c a` (`G = Ǧ + M`, `M_{(c,o),(a,o)} = M^{(B)}_{ca}`). -/
theorem BAExp14b2_twTrP_G (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a c : Zd d (sz.L n))
    (hm : 0 < ((baFMz sz z).m n).im) :
    twTrP n ((baFMz sz z).G n t ω) a c = twTr (baFMz sz z) n t ω c a + twMB (baFMz sz z) n c a := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hMB : twMB (baFMz sz z) n c a = BAExp14b_MB sz z n c a := by
    unfold twMB
    simp only [Matrix.of_apply]
    exact (BAExp14b_M_pt sz z n hm c a 0 0).trans (by simp)
  rw [twTr_eq, hMB, BAExp14b_twTrP_pt, BAExp14b_twTrP_pt]
  have hM : ∀ o : Fin (sz.W n ^ d), (baFMz sz z).M n (BAExp14b_pt c o) (BAExp14b_pt a o) = BAExp14b_MB sz z n c a :=
    fun o => (BAExp14b_M_pt sz z n hm c a o o).trans (by simp)
  simp only [FlowFM.GM, Finset.sum_sub_distrib, hM, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  field_simp
  ring

/-- **Bridge (a), charge `false`**: `Tr(G^* P_{ac}) = \overline{Tr(Ǧ P_{ca}) + M^{(B)}_{ac}}` (`twChg G false = G^*`). -/
theorem BAExp14b2_twTrP_G_false (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a c : Zd d (sz.L n))
    (hm : 0 < ((baFMz sz z).m n).im) :
    twTrP n (twChg ((baFMz sz z).G n t ω) false) a c =
      (starRingEnd ℂ) (twTr (baFMz sz z) n t ω a c + twMB (baFMz sz z) n a c) := by
  rw [← BAExp14b2_twTrP_G sz z n t ω c a hm, BAExp14b_twTrP_pt, BAExp14b_twTrP_pt]
  simp only [twChg, Bool.false_eq_true, ↓reduceIte, map_mul, map_sum, map_inv₀, map_pow, Complex.conj_natCast]

/-- **Bridge (a), both charges**: `Tr(G^σ P_{ac}) = Tr(Ǧ^σ P_{ac}) + M^{(B)}(σ)_{ca}` with the fluctuation
`twTr c a` (`σ = +`) or its conjugate (`σ = −`). -/
theorem BAExp14b2_twTrP_chg (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a c : Zd d (sz.L n))
    (hm : 0 < ((baFMz sz z).m n).im) :
    twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c =
      if σ then twTr (baFMz sz z) n t ω c a + twMB (baFMz sz z) n c a
      else (starRingEnd ℂ) (twTr (baFMz sz z) n t ω a c + twMB (baFMz sz z) n a c) := by
  cases σ
  · exact BAExp14b2_twTrP_G_false sz z n t ω a c hm
  · have : twChg ((baFMz sz z).G n t ω) true = (baFMz sz z).G n t ω := funext fun x => funext fun y => by simp [twChg]
    rw [this]; exact BAExp14b2_twTrP_G sz z n t ω a c hm

/-- **Bridge (b)**: the slot-1 circle relation (as `twCirc_holds`, slot 2): for a block-tied `M`,
`Tr((X₁ - M) E_a X₂ P_{c₁c₂}) = Tr(X₁ E_a X₂ P_{c₁c₂}) - W^{-d} M^{(B)}_{c₂a} Tr(X₂ P_{c₁a})`. -/
theorem BAExp14b2_twCirc1 (sz : Sizes d) (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hM : ∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) (a c₁ c₂ : Zd d (sz.L n)) :
    twLoopX n (fun x y => X₁ x y - M x y) X₂ a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB c₂ a * twTrP n X₂ c₁ a := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  rw [BAExp14b_twLoopX_pt, BAExp14b_twLoopX_pt, BAExp14b_twTrP_pt]
  have hMo : ∀ ox ow : Fin (sz.W n ^ d), M (BAExp14b_pt c₂ ow) (BAExp14b_pt a ox) = if ow = ox then MB c₂ a else 0 := by
    intro ox ow
    rw [hM, BAExp14b_split_pt, BAExp14b_split_pt]
  simp only [mul_sub, Finset.sum_sub_distrib, hMo, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul]
  ring

end Bridges

/-! ## 2. Infrastructure: suprema, block facts, envelopes -/

section Infra

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The supremum of a function on a finite nonempty type. -/
def BAExp14b2_sup {V : Type} [Fintype V] [Nonempty V] (f : V → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

theorem BAExp14b2_le_sup {V : Type} [Fintype V] [Nonempty V] (f : V → ℝ) (v : V) : f v ≤ BAExp14b2_sup f :=
  Finset.le_sup' f (Finset.mem_univ v)

theorem BAExp14b2_sup_le {V : Type} [Fintype V] [Nonempty V] {f : V → ℝ} {c : ℝ} (h : ∀ v, f v ≤ c) :
    BAExp14b2_sup f ≤ c := Finset.sup'_le _ _ fun v _ => h v

theorem BAExp14b2_sup_nonneg {V : Type} [Fintype V] [Nonempty V] {f : V → ℝ} (h : ∀ v, 0 ≤ f v) :
    0 ≤ BAExp14b2_sup f := (h (Classical.arbitrary V)).trans (BAExp14b2_le_sup f _)

/-- **A `≺` over a finite index is a `≺` of the supremum** (as `BAExp14a_Dom_a` in `Graph/BAExp14aB.lean`). -/
theorem BAExp14b2_Dom_sup {μ : Measure sz.SeqΩ} {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (f : ∀ n, V n → sz.SeqΩ → ℝ) (g : ℕ → ℝ) (h : PrecL sz μ (U := V) f (fun n _ _ => g n)) :
    BAExp14a_Dom sz μ (fun n ω => BAExp14b2_sup (fun v => f n v ω)) g := by
  unfold PrecL at h
  unfold BAExp14a_Dom PrecL
  refine BAExp14a_prec_of_bad h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨⟨⟩, hu⟩ := hω
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (V n)).Nonempty) (fun v => f n v ω)
  exact ⟨v, by
    change ((sz.size n : ℕ) : ℝ) ^ τ * g n < BAExp14b2_sup (fun v => f n v ω) at hu
    unfold BAExp14b2_sup at hu
    rw [hv] at hu
    exact hu⟩

/-- A deterministic `≺` is an eventual pointwise bound with the loss `N^τ`. -/
theorem BAExp14b2_det_ev {μ : Measure sz.SeqΩ} [IsProbabilityMeasure μ] (hsz : Tendsto sz.size atTop atTop) {y g : ℕ → ℝ}
    (h : BAExp14a_Dom sz μ (fun n _ => y n) g) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, y n ≤ ((sz.size n : ℕ) : ℝ) ^ τ * g n := by
  have := (BAExp14a_det_iff hsz (V := fun _ => Unit) (fun n _ => y n) (fun n _ => g n)).1 h τ hτ
  filter_upwards [this] with n hn using hn ()

section Block

variable {n : ℕ} {t CM S : ℝ}

/-- `|M^{(B)}_{cc'}| ≤ 1` (the fine entries `|M_{xy}| ≤ 1` at one offset). -/
theorem BAExp14b2_MB_le_one (hf : BAExp14a_Facts sz z n t CM S) (hm : 0 < ((baFMz sz z).m n).im) (c c' : Zd (k + 2) (sz.L n)) :
    ‖BAExp14b_MB sz z n c c'‖ ≤ 1 := by
  have h := hf.hM1 (BAExp14b_pt c 0) (BAExp14b_pt c' 0)
  simpa [BAExp14b_M_pt sz z n hm c c' 0 0] using h

/-- The block rows of `M^{(B)}`: `Σ_b |M^{(B)}_{cb}| ≤ C_M` (`BAExp14a_M_row_eq`, the fine row sum). -/
theorem BAExp14b2_MB_row (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (hf : BAExp14a_Facts sz z n t CM S) (c : Zd (k + 2) (sz.L n)) : ∑ b, ‖BAExp14b_MB sz z n c b‖ ≤ CM := by
  have h := BAExp14a_M_row_eq (W := sz.W n) hr.1 (BAExp14b_pt c 0)
  rw [BAExp14b_split_pt] at h
  exact h.symm.le.trans (hf.hMr (BAExp14b_pt c 0))

/-- The block columns of `M^{(B)}` (symmetry `BAMB_symm`). -/
theorem BAExp14b2_MB_col (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (hf : BAExp14a_Facts sz z n t CM S) (c : Zd (k + 2) (sz.L n)) : ∑ a, ‖BAExp14b_MB sz z n a c‖ ≤ CM := by
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_)) (BAExp14b2_MB_row hr hf c)
  unfold BAExp14b_MB
  rw [BAMB_symm]

/-- The block columns of `ω - 1` (`Σ_α |(W - 1)_{αβ}| ≤ S` at the fine level, `(W - 1)_{αβ} = W^{-d}(ω - 1)_{[α][β]}`). -/
theorem BAExp14b2_om1_col (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (hf : BAExp14a_Facts sz z n t CM S) (c : Zd (k + 2) (sz.L n)) :
    ∑ a₁, ‖(BAExp14b_om sz z n t - 1) a₁ c‖ ≤ S := by
  have h := hf.hWk true (BAExp14b_pt c 0)
  have hW : (((sz.W n : ℕ) : ℝ) ^ (k + 2)) ≠ 0 := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [BAExp14b_sum_idx (β := ℝ) (fun α => ‖BAExp14a_Wk sz z n t true α (BAExp14b_pt c 0)‖)] at h
  simp only [BAExp14b_Wk_pt_true hr hf.ht0 hf.ht1, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow] at h
  refine le_of_eq_of_le (Finset.sum_congr rfl fun c' _ => ?_) h
  field_simp

/-- `ω = Θ^{(+,+)}` has `ℓ¹` rows `≤ S + 1` (symmetry and `ω = (ω - 1) + 1`). -/
theorem BAExp14b2_om_row (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (hf : BAExp14a_Facts sz z n t CM S) (c : Zd (k + 2) (sz.L n)) : ∑ b, ‖BAExp14b_om sz z n t c b‖ ≤ S + 1 := by
  have hT := BATheta_isSymm (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) hr t hf.ht0 hf.ht1 true true
  have hs : ∀ b, BAExp14b_om sz z n t c b = BAExp14b_om sz z n t b c := fun b => by
    have := congrFun (congrFun hT b) c
    simpa [Matrix.transpose_apply] using this
  calc ∑ b, ‖BAExp14b_om sz z n t c b‖ = ∑ b, ‖BAExp14b_om sz z n t b c‖ := Finset.sum_congr rfl fun b _ => by rw [hs]
    _ ≤ ∑ b, (‖(BAExp14b_om sz z n t - 1) b c‖ + (if b = c then (1 : ℝ) else 0)) := by
        refine Finset.sum_le_sum fun b _ => ?_
        have : BAExp14b_om sz z n t b c = (BAExp14b_om sz z n t - 1) b c + (1 : Matrix (Zd (k + 2) (sz.L n)) (Zd (k + 2) (sz.L n)) ℂ) b c := by
          simp
        rw [this]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        simp only [Matrix.one_apply]
        split_ifs <;> simp
    _ = ∑ b, ‖(BAExp14b_om sz z n t - 1) b c‖ + 1 := by
        rw [Finset.sum_add_distrib]; simp
    _ ≤ S + 1 := by gcongr; exact BAExp14b2_om1_col hr hf c

end Block

section P3

variable {n : ℕ} {t CM S : ℝ}

/-- `‖R_c‖ ≤ C_M ε₂` when `‖q‖ ≤ ε₂` (the remainder of `BAExp14a_e_bound` in `Graph/BAExp14aB.lean`). -/
theorem BAExp14b2_R_le (hf : BAExp14a_Facts sz z n t CM S) {ε₂ : ℝ}
    (hq : ∀ c y w, ‖BAExp14a_q sz z n t c y w‖ ≤ ε₂) (c : Zd (k + 2) (sz.L n)) : ‖BAExp14a_R sz z n t c‖ ≤ CM * ε₂ := by
  have hε₂ : 0 ≤ ε₂ := (norm_nonneg _).trans (hq 0 0 0)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  unfold BAExp14a_R
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hf.ht0, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have h1 : ‖∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ α, (baFMz sz z).M n x α * BAExp14a_q sz z n t (STblk sz n α) α x‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (CM * ε₂) := by
    calc _ ≤ ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ α, ‖(baFMz sz z).M n x α‖ * ε₂ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun α _ => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hq _ _ _) (norm_nonneg _)
      _ ≤ ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, CM * ε₂ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [← Finset.sum_mul]
          exact mul_le_mul_of_nonneg_right (hf.hMr x) hε₂
      _ = _ := by rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; ring
  calc t * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ α, (baFMz sz z).M n x α *
          BAExp14a_q sz z n t (STblk sz n α) α x‖)
      ≤ 1 * ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (CM * ε₂))) :=
        mul_le_mul hf.ht1.le (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity) zero_le_one
    _ = CM * ε₂ := by field_simp

/-- **`e = ω R`** (`(1 - t M⁺) e = R`, `BAExp14a_e_eq`, inverted through `ω = Θ^{(+,+)} = (1 - t M⁺)⁻¹`). -/
theorem BAExp14b2_e_eq_om (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (hf : BAExp14a_Facts sz z n t CM S) (c : Zd (k + 2) (sz.L n)) :
    BAExp14a_e sz z n t c = ∑ b, BAExp14b_om sz z n t c b * BAExp14a_R sz z n t b := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hU := BATheta_isUnit (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) hr t ht0 hf.ht1 true true
  set Qm := BAMss (k + 2) (sz.L n) (BAMB (k + 2) (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) ((baFMz sz z).m n)) true true with hQm
  have h1 : (1 - (t : ℂ) • Qm) *ᵥ (BAExp14a_e sz z n t) = BAExp14a_R sz z n t := by
    funext c
    have := BAExp14a_e_eq hκ hflow n ht0 ht hf c
    have hQ : ∀ b, Qm c b = (BAExp14a_MB sz z n c b) ^ 2 := fun b => by
      simp only [hQm, BAMss, Matrix.of_apply, BAMsigma, ite_true, BAExp14a_MB]
      rw [BAMB_symm, sq]
      rfl
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, hQ]
    rw [this]; ring
  have h2 : BAExp14b_om sz z n t * (1 - (t : ℂ) • Qm) = 1 := Ring.inverse_mul_cancel _ hU
  have h3 : BAExp14a_e sz z n t = BAExp14b_om sz z n t *ᵥ (BAExp14a_R sz z n t) := by
    rw [← h1, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [h3]
  rfl

end P3

/-! ## 3. P3, the sharp average `‖𝔼 X_c‖ ≺ 𝔟^{3/2}` -/

section P3main

/-- **The sharp average (P3)**: `‖𝔼 X_c‖ ≺ (W^{-d} B_{t,0})^{3/2}` with **no** `(1 - t)⁻¹`, from `STLocalEntrygL` and `LWAvgLawgL` only:
`‖𝔼[X_c Ǧ_{yw}]‖ ≺ 𝔟^{3/2}` (`BAExp14a_q_prec`), `|R| ≤ C_M ε₂`, `e = ω R` with `Σ_b |ω_{cb}| ≤ S + 1` uniformly in `t ∈ [0, 1)`
(not the Neumann `BAExp14a_e_bound`, which carries `(1 - t)⁻¹`).  Zero slack: `3/2 = 3/2`. -/
private theorem BAExp14b2_P3 (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts⟩ := BAExp14a_facts_of_flow hk hκ h𝔡 hflow
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hq := BAExp14a_q_prec hκ hε h𝔡 hflow ht0 ht hCM hS hfacts hE hA
  have hDq := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (p : Zd (k + 2) (sz.L n) × Idx (k + 2) (sz.L n) (sz.W n) × Idx (k + 2) (sz.L n) (sz.W n)) (_ : sz.SeqΩ) =>
      ‖BAExp14a_q sz z n (t n) p.1 p.2.1 p.2.2‖) _ hq
  have hD := BAExp14a_Dom.const_mul hsz (c := (S + 1) * CM) (by positivity) (fun n => Real.rpow_nonneg (hB n) _) hDq
  refine BAExp14a_prec_of_le_ev ?_ (BAExp14a_Dom.index hsz (V := fun n => Zd (k + 2) (sz.L n)) hD)
  filter_upwards [hfacts] with n hn c _
  have hf := hn (t n) (ht0 n) (ht n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  set qm := BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Idx (k + 2) (sz.L n) (sz.W n) × Idx (k + 2) (sz.L n) (sz.W n) =>
    ‖BAExp14a_q sz z n (t n) p.1 p.2.1 p.2.2‖) with hqm
  have hq' : ∀ c y w, ‖BAExp14a_q sz z n (t n) c y w‖ ≤ qm := fun c y w => BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Idx (k + 2) (sz.L n) (sz.W n) × Idx (k + 2) (sz.L n) (sz.W n) =>
    ‖BAExp14a_q sz z n (t n) p.1 p.2.1 p.2.2‖) (c, y, w)
  have hR := BAExp14b2_R_le hf hq'
  have hqm0 : 0 ≤ qm := (norm_nonneg _).trans (hq' 0 0 0)
  change ‖BAExp14a_e sz z n (t n) c‖ ≤ (S + 1) * CM * qm
  rw [BAExp14b2_e_eq_om hκ hflow (ht0 n) (ht n) hf c]
  calc ‖∑ b, BAExp14b_om sz z n (t n) c b * BAExp14a_R sz z n (t n) b‖
      ≤ ∑ b, ‖BAExp14b_om sz z n (t n) c b‖ * (CM * qm) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hR b) (norm_nonneg _)
    _ = (∑ b, ‖BAExp14b_om sz z n (t n) c b‖) * (CM * qm) := (Finset.sum_mul _ _ _).symm
    _ ≤ (S + 1) * (CM * qm) := mul_le_mul_of_nonneg_right (BAExp14b2_om_row hr hf c) (mul_nonneg hCM hqm0)
    _ = (S + 1) * CM * qm := by ring

end P3main

/-! ## 4. Envelopes -/

section Env

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} {n : ℕ}

/-- `|Tr(X P_{c₁c₂})| ≤ Y` when all entries of `X` are `≤ Y`. -/
theorem BAExp14b2_twTrP_le {X : Idx (k + 2) (sz.L n) (sz.W n) → Idx (k + 2) (sz.L n) (sz.W n) → ℂ} {Y : ℝ}
    (hX : ∀ x y, ‖X x y‖ ≤ Y) (c₁ c₂ : Zd (k + 2) (sz.L n)) : ‖twTrP n X c₁ c₂‖ ≤ Y := by
  have hY : 0 ≤ Y := (norm_nonneg _).trans (hX 0 0)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [BAExp14b_twTrP_pt, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * ‖∑ o : Fin (sz.W n ^ (k + 2)), X (BAExp14b_pt c₂ o) (BAExp14b_pt c₁ o)‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * Y) := by
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
        calc ∑ o : Fin (sz.W n ^ (k + 2)), ‖X (BAExp14b_pt c₂ o) (BAExp14b_pt c₁ o)‖ ≤ ∑ _o : Fin (sz.W n ^ (k + 2)), Y :=
              Finset.sum_le_sum fun o _ => hX _ _
          _ = ((sz.W n : ℕ) : ℝ) ^ (k + 2) * Y := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
    _ = Y := by field_simp

/-- `|Tr(X₁ E_a X₂ P_{c₁c₂})| ≤ Y₁ Y₂` when the entries of `X_i` are `≤ Y_i`. -/
theorem BAExp14b2_twLoopX_le {X₁ X₂ : Idx (k + 2) (sz.L n) (sz.W n) → Idx (k + 2) (sz.L n) (sz.W n) → ℂ} {Y₁ Y₂ : ℝ}
    (h1 : ∀ x y, ‖X₁ x y‖ ≤ Y₁) (h2 : ∀ x y, ‖X₂ x y‖ ≤ Y₂) (a c₁ c₂ : Zd (k + 2) (sz.L n)) :
    ‖twLoopX n X₁ X₂ a c₁ c₂‖ ≤ Y₁ * Y₂ := by
  have hY1 : 0 ≤ Y₁ := (norm_nonneg _).trans (h1 0 0)
  have hY2 : 0 ≤ Y₂ := (norm_nonneg _).trans (h2 0 0)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [BAExp14b_twLoopX_pt, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have hs : ‖∑ ox : Fin (sz.W n ^ (k + 2)), ∑ ow : Fin (sz.W n ^ (k + 2)),
      X₂ (BAExp14b_pt a ox) (BAExp14b_pt c₁ ow) * X₁ (BAExp14b_pt c₂ ow) (BAExp14b_pt a ox)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (Y₂ * Y₁)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _ox : Fin (sz.W n ^ (k + 2)), ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (Y₂ * Y₁) := by
          refine Finset.sum_le_sum fun ox _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _ow : Fin (sz.W n ^ (k + 2)), Y₂ * Y₁ := by
                refine Finset.sum_le_sum fun ow _ => ?_
                rw [norm_mul]
                exact mul_le_mul (h2 _ _) (h1 _ _) (norm_nonneg _) hY2
            _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  calc ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 * ‖_‖ ≤ ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 *
        (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (Y₂ * Y₁))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = Y₁ * Y₂ := by field_simp

variable {t : ℝ}

/-- `‖G(σ)_{xy}‖ ≤ η⁻¹`. -/
theorem BAExp14b2_chg_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (σ : Bool)
    (ω : sz.SeqΩ) (x y : Idx (k + 2) (sz.L n) (sz.W n)) :
    ‖twChg ((baFMz sz z).G n t ω) σ x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ := by
  cases σ
  · simp only [twChg, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
    exact BAExp14a_G_le hκ hflow n ht0 ht ω y x
  · simp only [twChg, ↓reduceIte]
    exact BAExp14a_G_le hκ hflow n ht0 ht ω x y

/-- `‖𝓛^{(2)}‖ ≤ η⁻²` pathwise. -/
theorem BAExp14b2_L2_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (σ₁ σ₂ : Bool)
    (a b : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) :
    ‖(baFMz sz z).L n t ![σ₁, σ₂] ![a, b] ω‖ ≤ (((baFMz sz z).eta n t)⁻¹) ^ 2 := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  rw [BAExp14b_L2_eq, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have hs : ‖∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) a,
      twChg ((baFMz sz z).G n t ω) σ₁ x y * twChg ((baFMz sz z).G n t ω) σ₂ y x‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((baFMz sz z).eta n t)⁻¹ * ((baFMz sz z).eta n t)⁻¹)) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ _x ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((baFMz sz z).eta n t)⁻¹ * ((baFMz sz z).eta n t)⁻¹) := by
          refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
          calc _ ≤ ∑ _y ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, (((baFMz sz z).eta n t)⁻¹ * ((baFMz sz z).eta n t)⁻¹) := by
                refine Finset.sum_le_sum fun y _ => ?_
                rw [norm_mul]
                exact mul_le_mul (BAExp14b2_chg_le hκ hflow ht0 ht σ₁ ω x y) (BAExp14b2_chg_le hκ hflow ht0 ht σ₂ ω y x)
                  (norm_nonneg _) (inv_nonneg.2 hη.le)
            _ = _ := by rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; ring
      _ = _ := by rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; ring
  calc ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 * ‖_‖ ≤ ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 *
        (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((sz.W n : ℕ) : ℝ) ^ (k + 2) * (((baFMz sz z).eta n t)⁻¹ * ((baFMz sz z).eta n t)⁻¹))) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (((baFMz sz z).eta n t)⁻¹) ^ 2 := by field_simp

/-- `‖twLoopX (G(σ₁)) (G(σ₂))‖ ≤ η⁻²` pathwise (`L̃`). -/
theorem BAExp14b2_Lt_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (σ₁ σ₂ : Bool)
    (ω : sz.SeqΩ) (a c₁ c₂ : Zd (k + 2) (sz.L n)) :
    ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ₁) (twChg ((baFMz sz z).G n t ω) σ₂) a c₁ c₂‖ ≤ (((baFMz sz z).eta n t)⁻¹) ^ 2 := by
  rw [sq]
  exact BAExp14b2_twLoopX_le (fun x y => BAExp14b2_chg_le hκ hflow ht0 ht σ₁ ω x y)
    (fun x y => BAExp14b2_chg_le hκ hflow ht0 ht σ₂ ω x y) a c₁ c₂

/-- `‖twTr‖ ≤ η⁻¹ + 1` pathwise (TL1 variable). -/
theorem BAExp14b2_tw_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hf : BAExp14a_Facts sz z n t CM S) (ω : sz.SeqΩ) (c₁ c₂ : Zd (k + 2) (sz.L n)) :
    ‖twTr (baFMz sz z) n t ω c₁ c₂‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  rw [twTr_eq]
  exact BAExp14b2_twTrP_le (fun x y => BAExp14a_GM_le hκ hflow n ht0 ht hf ω x y) _ _

end Env

/-! ## 5. The closing lemma: `Σ_{a₁,c} u X (Y_det + Y_rnd)` against `(1 - t)⁻¹ 𝔟^{5/2}` -/

section Master

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The triangle inequality for the integral when the first summand is integrable (the second need not be). -/
theorem BAExp14b2_norm_int_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℂ} (hf : Integrable f P) :
    ‖∫ ω, (f ω + g ω) ∂P‖ ≤ ‖∫ ω, f ω ∂P‖ + ‖∫ ω, g ω ∂P‖ := by
  by_cases hg : Integrable g P
  · rw [integral_add hf hg]; exact norm_add_le _ _
  · have h1 : ¬ Integrable (fun ω => f ω + g ω) P := fun h => hg (by
      have := h.sub hf
      convert this using 1
      funext ω
      simp)
    rw [integral_undef h1, integral_undef hg]
    simp

/-- **The closing lemma** (the shape of every family of file A): `Φ = Σ_{a₁,c} u X_{a₁} (Y_det + Y_rnd)` with the deterministic weights `u`
(`ℓ¹` sum `≤ U₁`), `|Y_det| ≤ y_d ≺ g_d` deterministic, `|Y_rnd| ≤ y_r(ω) ≺ g_r`, `y_r ≤ N^{K_y}` pathwise, gives
`‖𝔼 Φ‖ ≺ ζ = (1 - t)⁻¹ 𝔟^{5/2}` as soon as `U₁ g_d 𝔟^{3/2} ≲ ζ` (the deterministic part is paid with the sharp average P3) and
`U₁ 𝔟 g_r ≲ ζ` (the random part with `a ≺ 𝔟`). -/
theorem BAExp14b2_close (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hDa : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)))
    (hP3 : PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)))
    {V : ℕ → Type} (Φ : ∀ n, V n → sz.SeqΩ → ℂ)
    (u Yd : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → ℂ)
    (Yr : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → sz.SeqΩ → ℂ)
    (hΦ : ∀ n v ω, Φ n v ω = ∑ a₁, ∑ c, u n v a₁ c * BAExp14a_X sz z n (t n) ω a₁ * (Yd n v a₁ c + Yr n v a₁ c ω))
    {U1 : ℝ} (hU1 : 0 ≤ U1) (hu : ∀ᶠ n in atTop, ∀ v, ∑ a₁, ∑ c, ‖u n v a₁ c‖ ≤ U1)
    (yd gyd : ℕ → ℝ) (hyd0 : ∀ n, 0 ≤ yd n) (hgyd0 : ∀ n, 0 ≤ gyd n)
    (hYd : ∀ᶠ n in atTop, ∀ v a₁ c, ‖Yd n v a₁ c‖ ≤ yd n) (hDyd : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => yd n) gyd)
    (yr : ∀ n, sz.SeqΩ → ℝ) (gy : ℕ → ℝ) (hyr0 : ∀ n ω, 0 ≤ yr n ω) (hgy0 : ∀ n, 0 ≤ gy n)
    (hYr : ∀ᶠ n in atTop, ∀ v a₁ c ω, ‖Yr n v a₁ c ω‖ ≤ yr n ω) (hDy : BAExp14a_Dom sz (BAExp14a_μ sz) yr gy)
    (Ky : ℕ) (hyenv : ∀ᶠ n in atTop, ∀ ω, yr n ω ≤ ((sz.size n : ℕ) : ℝ) ^ Ky)
    {K : ℝ} (hK : 0 < K)
    (hdet : ∀ᶠ n in atTop, U1 * (gyd n * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))
    (hrnd : ∀ᶠ n in atTop, U1 * (sz.Bctl n (t n) * gy n) ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :
    PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Φ n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hζ0 : ∀ n, 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := fun n =>
    mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg (hB n) _)
  -- the pieces
  set Rr : ∀ n, V n → sz.SeqΩ → ℂ := fun n v ω => ∑ a₁, ∑ c, u n v a₁ c * BAExp14a_X sz z n (t n) ω a₁ * Yr n v a₁ c ω with hRr
  set Dd : ∀ n, V n → Zd (k + 2) (sz.L n) → ℂ := fun n v a₁ => ∑ c, u n v a₁ c * Yd n v a₁ c with hDd
  set emax : ℕ → ℝ := fun n => BAExp14b2_sup (fun c : Zd (k + 2) (sz.L n) => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) with hem
  have hem0 : ∀ n, 0 ≤ emax n := fun n => BAExp14b2_sup_nonneg (f := fun c : Zd (k + 2) (sz.L n) => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) fun c => norm_nonneg _
  have hDe : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => emax n) (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) :=
    BAExp14b2_Dom_sup (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) _ hP3
  -- the deterministic part
  have hDet : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => U1 * (yd n * emax n)) (fun n => U1 * (gyd n * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ))) :=
    BAExp14a_Dom.mul hsz (fun n _ => mul_nonneg (hyd0 n) (hem0 n)) (fun n => hU1)
      (BAExp14a_Dom.refl hsz (g := fun _ => U1) fun _ => hU1)
      (BAExp14a_Dom.mul hsz (fun n _ => hem0 n) hgyd0 hDyd hDe)
  have hDet' : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => U1 * (yd n * emax n)) (fun n => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) :=
    BAExp14a_Dom.mono hsz hK hζ0 hdet hDet
  -- the random part
  have hQd : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n ω => U1 * (BAExp14a_a sz z n (t n) ω * yr n ω))
      (fun n => U1 * (sz.Bctl n (t n) * gy n)) :=
    BAExp14a_Dom.mul hsz (fun n ω => mul_nonneg (BAExp14a_a_nonneg n (t n) ω) (hyr0 n ω)) (fun n => hU1)
      (BAExp14a_Dom.refl hsz (g := fun _ => U1) fun _ => hU1)
      (BAExp14a_Dom.mul hsz hyr0 hB hDa hDy)
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts (2 * U1 + 1)
  have hRprec : PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Rr n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    refine BAExp14a_prec_int (μ := BAExp14a_μ sz) hsz (V := V) Rr (fun n ω => U1 * (BAExp14a_a sz z n (t n) ω * yr n ω)) _
      (fun n => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) (K := K) (Kenv := ((Ky + 3 : ℕ) : ℝ)) (Kf := 5 / 2) hK hζ0 ?_ hQd hrnd ?_ ?_
    · filter_upwards [hu, hYr] with n hun hYrn v ω
      have ha := fun a₁ => BAExp14a_le_a (z := z) n (t n) ω a₁
      calc ‖Rr n v ω‖ ≤ ∑ a₁, ∑ c, ‖u n v a₁ c‖ * (BAExp14a_a sz z n (t n) ω * yr n ω) := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_))
            rw [norm_mul, norm_mul, mul_assoc]
            exact mul_le_mul_of_nonneg_left (mul_le_mul (ha a₁) (hYrn v a₁ c ω) (norm_nonneg _) (BAExp14a_a_nonneg n (t n) ω))
              (norm_nonneg _)
        _ = (∑ a₁, ∑ c, ‖u n v a₁ c‖) * (BAExp14a_a sz z n (t n) ω * yr n ω) := by
            simp only [← Finset.sum_mul]
        _ ≤ U1 * (BAExp14a_a sz z n (t n) ω * yr n ω) :=
            mul_le_mul_of_nonneg_right (hun v) (mul_nonneg (BAExp14a_a_nonneg n (t n) ω) (hyr0 n ω))
    · filter_upwards [hev, hyenv, hu, hYr] with n hn hye hun hYrn v ω
      obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
      have haN : BAExp14a_a sz z n (t n) ω ≤ 2 * N ^ 2 := by
        refine Finset.sup'_le _ _ fun c _ => ?_
        have := BAExp14a_X_le hκ hflow n (ht0 n) (ht n) hf ω c
        nlinarith
      have hcalc : ‖Rr n v ω‖ ≤ U1 * (BAExp14a_a sz z n (t n) ω * yr n ω) := by
        have ha := fun a₁ => BAExp14a_le_a (z := z) n (t n) ω a₁
        calc ‖Rr n v ω‖ ≤ ∑ a₁, ∑ c, ‖u n v a₁ c‖ * (BAExp14a_a sz z n (t n) ω * yr n ω) := by
              refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_))
              rw [norm_mul, norm_mul, mul_assoc]
              exact mul_le_mul_of_nonneg_left (mul_le_mul (ha a₁) (hYrn v a₁ c ω) (norm_nonneg _) (BAExp14a_a_nonneg n (t n) ω))
                (norm_nonneg _)
          _ = (∑ a₁, ∑ c, ‖u n v a₁ c‖) * (BAExp14a_a sz z n (t n) ω * yr n ω) := by
              simp only [← Finset.sum_mul]
          _ ≤ U1 * (BAExp14a_a sz z n (t n) ω * yr n ω) :=
              mul_le_mul_of_nonneg_right (hun v) (mul_nonneg (BAExp14a_a_nonneg n (t n) ω) (hyr0 n ω))
      refine hcalc.trans ?_
      have hy := hye ω
      have ha0 := BAExp14a_a_nonneg (sz := sz) (z := z) n (t n) ω
      have hy0 := hyr0 n ω
      rw [Real.rpow_natCast]
      calc U1 * (BAExp14a_a sz z n (t n) ω * yr n ω) ≤ U1 * ((2 * N ^ 2) * N ^ Ky) :=
            mul_le_mul_of_nonneg_left (mul_le_mul haN hy hy0 (by positivity)) hU1
        _ = (2 * U1) * (N ^ 2 * N ^ Ky) := by ring
        _ ≤ N * (N ^ 2 * N ^ Ky) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = N ^ (Ky + 3) := by ring
    · filter_upwards [hev] with n hn
      exact BAExp14a_floor n (ht0 n) hn.2.2.2.2.2.1
  -- the sum
  have hsum := StochDomAt.add hsz (BAExp14a_Dom.index hsz (V := V) hDet') hRprec
  refine BAExp14a_prec_mono hsz (K := 2) two_pos (fun n _ _ => hζ0 n) (Eventually.of_forall fun n v ω => ?_)
    (BAExp14a_prec_of_le_ev (ξ₁ := fun n v ω => U1 * (yd n * emax n) + ‖∫ ω, Rr n v ω ∂(BAExp14a_μ sz)‖) ?_ hsum)
  · simp only [Pi.add_apply]; linarith [hζ0 n]
  · filter_upwards [hfacts, hYd, hu] with n hn hyd hun v ω
    have hf := hn (t n) (ht0 n) (ht n)
    have hXi : ∀ a₁, Integrable (fun ω => BAExp14a_X sz z n (t n) ω a₁) (BAExp14a_μ sz) := fun a₁ =>
      BAExp14a_int_X hκ hflow n (ht0 n) (ht n) hf a₁
    have hpt : ∀ ω, Φ n v ω = (∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) + Rr n v ω := by
      intro ω
      rw [hΦ]
      simp only [hRr, hDd, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a₁ _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hF1 : Integrable (fun ω => ∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) (BAExp14a_μ sz) :=
      integrable_finsetSum _ fun a₁ _ => (hXi a₁).const_mul _
    have hI1 : ∫ ω, (∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) ∂(BAExp14a_μ sz) =
        ∑ a₁, Dd n v a₁ * ∫ ω, BAExp14a_X sz z n (t n) ω a₁ ∂(BAExp14a_μ sz) := by
      rw [integral_finsetSum _ fun a₁ _ => (hXi a₁).const_mul _]
      exact Finset.sum_congr rfl fun a₁ _ => integral_const_mul _ _
    have hdd : ∑ a₁, ‖Dd n v a₁‖ ≤ U1 * yd n := by
      calc ∑ a₁, ‖Dd n v a₁‖ ≤ ∑ a₁, ∑ c, ‖u n v a₁ c‖ * yd n := by
            refine Finset.sum_le_sum fun a₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hyd v a₁ c) (norm_nonneg _)
        _ = (∑ a₁, ∑ c, ‖u n v a₁ c‖) * yd n := by simp only [← Finset.sum_mul]
        _ ≤ U1 * yd n := mul_le_mul_of_nonneg_right (hun v) (hyd0 n)
    have hdet' : ‖∑ a₁, Dd n v a₁ * ∫ ω, BAExp14a_X sz z n (t n) ω a₁ ∂(BAExp14a_μ sz)‖ ≤ U1 * (yd n * emax n) := by
      calc _ ≤ ∑ a₁, ‖Dd n v a₁‖ * emax n := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a₁ _ => ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (BAExp14b2_le_sup (fun c : Zd (k + 2) (sz.L n) =>
              ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) a₁) (norm_nonneg _)
        _ = (∑ a₁, ‖Dd n v a₁‖) * emax n := (Finset.sum_mul _ _ _).symm
        _ ≤ (U1 * yd n) * emax n := mul_le_mul_of_nonneg_right hdd (hem0 n)
        _ = U1 * (yd n * emax n) := by ring
    have hcongr : ∫ ω, Φ n v ω ∂(BAExp14a_μ sz) =
        ∫ ω, ((∑ a₁, Dd n v a₁ * BAExp14a_X sz z n (t n) ω a₁) + Rr n v ω) ∂(BAExp14a_μ sz) :=
      integral_congr_ae (Eventually.of_forall hpt)
    rw [hcongr]
    refine (BAExp14b2_norm_int_add hF1).trans ?_
    rw [hI1]
    linarith [hdet']

/-- The envelope arithmetic of Form A: `N ≥ 3`, `A ≤ N^p`, `B ≤ N^q`, `C ≤ N^r` give `A B + (A + 1) C ≤ N^{p+q+r+1}`. -/
theorem BAExp14b2_env3 {N A B C : ℝ} (hN : 3 ≤ N) (p q r : ℕ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hA : A ≤ N ^ p) (hB : B ≤ N ^ q) (hC : C ≤ N ^ r) : A * B + (A + 1) * C ≤ N ^ (p + q + r + 1) := by
  have hN1 : 1 ≤ N := by linarith
  have h1 : (1 : ℝ) ≤ N ^ p := one_le_pow₀ hN1
  have h2 : (1 : ℝ) ≤ N ^ q := one_le_pow₀ hN1
  have h3 : (1 : ℝ) ≤ N ^ r := one_le_pow₀ hN1
  have h4 : A * B ≤ N ^ p * N ^ q := mul_le_mul hA hB hB0 (by linarith)
  have h5 : (A + 1) * C ≤ (2 * N ^ p) * N ^ r := mul_le_mul (by linarith) hC hC0 (by linarith)
  have hp0 : (0 : ℝ) ≤ N ^ p := by linarith
  have hq0 : (0 : ℝ) ≤ N ^ q := by linarith
  have e1 : N ^ p * N ^ q ≤ N ^ p * N ^ q * N ^ r := by
    have := mul_nonneg (mul_nonneg hp0 hq0) (sub_nonneg.2 h3)
    nlinarith
  have e2 : N ^ p * N ^ r ≤ N ^ p * N ^ q * N ^ r := by
    have := mul_nonneg (mul_nonneg hp0 (sub_nonneg.2 h2)) (by linarith : (0 : ℝ) ≤ N ^ r)
    nlinarith
  calc A * B + (A + 1) * C ≤ N ^ p * N ^ q + (2 * N ^ p) * N ^ r := add_le_add h4 h5
    _ ≤ 3 * (N ^ p * N ^ q * N ^ r) := by nlinarith
    _ ≤ N * (N ^ p * N ^ q * N ^ r) := by
        have : 0 ≤ N ^ p * N ^ q * N ^ r := by positivity
        nlinarith
    _ = N ^ (p + q + r + 1) := by ring

/-- The envelope arithmetic of Form B: `N ≥ 2`, `C ≤ N^p`, `A ≤ N^q`, `B ≤ N^r` give `C + A B ≤ N^{p+q+r+1}`. -/
theorem BAExp14b2_env2 {N A B C : ℝ} (hN : 2 ≤ N) (p q r : ℕ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hC : C ≤ N ^ p) (hA : A ≤ N ^ q) (hB : B ≤ N ^ r) : C + A * B ≤ N ^ (p + q + r + 1) := by
  have hN1 : 1 ≤ N := by linarith
  have h1 : (1 : ℝ) ≤ N ^ p := one_le_pow₀ hN1
  have h2 : (1 : ℝ) ≤ N ^ q := one_le_pow₀ hN1
  have h3 : (1 : ℝ) ≤ N ^ r := one_le_pow₀ hN1
  have h4 : A * B ≤ N ^ q * N ^ r := mul_le_mul hA hB hB0 (by linarith)
  have hp0 : (0 : ℝ) ≤ N ^ p := by linarith
  have hq0 : (0 : ℝ) ≤ N ^ q := by linarith
  have hr0 : (0 : ℝ) ≤ N ^ r := by linarith
  have e1 : N ^ p ≤ N ^ p * N ^ q * N ^ r := by
    have := mul_nonneg (mul_nonneg hp0 (sub_nonneg.2 h2)) hr0
    have h6 := mul_nonneg hp0 (sub_nonneg.2 h3)
    nlinarith
  have e2 : N ^ q * N ^ r ≤ N ^ p * N ^ q * N ^ r := by
    have := mul_nonneg (mul_nonneg hq0 hr0) (sub_nonneg.2 h1)
    nlinarith
  calc C + A * B ≤ N ^ p + N ^ q * N ^ r := add_le_add hC h4
    _ ≤ 2 * (N ^ p * N ^ q * N ^ r) := by nlinarith
    _ ≤ N * (N ^ p * N ^ q * N ^ r) := by
        have : 0 ≤ N ^ p * N ^ q * N ^ r := by positivity
        nlinarith
    _ = N ^ (p + q + r + 1) := by ring

/-- **Form A** (`D1t`, `D2t`): `Φ = Σ_{a₁,c} u X (T̂ + B)(K + Δ)` with `T̂` the fluctuation of a twisted one-loop (`≤ τ̂ ≺ g_τ`),
`|B| ≤ 1`, `K` deterministic (`≤ y_k ≺ g_k`), `Δ` the fluctuation of the second loop (`≤ y_D ≺ g_D`). -/
theorem BAExp14b2_closeA (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hDa : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)))
    (hP3 : PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)))
    {V : ℕ → Type} (Φ : ∀ n, V n → sz.SeqΩ → ℂ)
    (u Bs Kq : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → ℂ)
    (Th Dq : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → sz.SeqΩ → ℂ)
    (hΦ : ∀ n v ω, Φ n v ω = ∑ a₁, ∑ c, u n v a₁ c * BAExp14a_X sz z n (t n) ω a₁ *
      ((Th n v a₁ c ω + Bs n v a₁ c) * (Kq n v a₁ c + Dq n v a₁ c ω)))
    {U1 : ℝ} (hU1 : 0 ≤ U1) (hu : ∀ᶠ n in atTop, ∀ v, ∑ a₁, ∑ c, ‖u n v a₁ c‖ ≤ U1)
    (τh : ∀ n, sz.SeqΩ → ℝ) (gτ : ℕ → ℝ) (hτ0 : ∀ n ω, 0 ≤ τh n ω) (hgτ0 : ∀ n, 0 ≤ gτ n)
    (hTh : ∀ᶠ n in atTop, ∀ v a₁ c ω, ‖Th n v a₁ c ω‖ ≤ τh n ω) (hBs : ∀ᶠ n in atTop, ∀ v a₁ c, ‖Bs n v a₁ c‖ ≤ 1)
    (hDτ : BAExp14a_Dom sz (BAExp14a_μ sz) τh gτ)
    (yk gk : ℕ → ℝ) (hyk0 : ∀ n, 0 ≤ yk n) (hgk0 : ∀ n, 0 ≤ gk n)
    (hKq : ∀ᶠ n in atTop, ∀ v a₁ c, ‖Kq n v a₁ c‖ ≤ yk n) (hDk : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => yk n) gk)
    (yD : ∀ n, sz.SeqΩ → ℝ) (gD : ℕ → ℝ) (hyD0 : ∀ n ω, 0 ≤ yD n ω) (hgD0 : ∀ n, 0 ≤ gD n)
    (hDq : ∀ᶠ n in atTop, ∀ v a₁ c ω, ‖Dq n v a₁ c ω‖ ≤ yD n ω) (hDD : BAExp14a_Dom sz (BAExp14a_μ sz) yD gD)
    (Kτ Kk KD : ℕ) (hτenv : ∀ᶠ n in atTop, ∀ ω, τh n ω ≤ ((sz.size n : ℕ) : ℝ) ^ Kτ)
    (hkenv : ∀ᶠ n in atTop, yk n ≤ ((sz.size n : ℕ) : ℝ) ^ Kk)
    (hDenv : ∀ᶠ n in atTop, ∀ ω, yD n ω ≤ ((sz.size n : ℕ) : ℝ) ^ KD)
    {K : ℝ} (hK : 0 < K)
    (hdet : ∀ᶠ n in atTop, U1 * (gk n * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))
    (hrnd : ∀ᶠ n in atTop, U1 * (sz.Bctl n (t n) * (gτ n * gk n + (gτ n + 1) * gD n)) ≤
      K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :
    PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Φ n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  refine BAExp14b2_close hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3 Φ u (fun n v a₁ c => Bs n v a₁ c * Kq n v a₁ c)
    (fun n v a₁ c ω => Th n v a₁ c ω * Kq n v a₁ c + (Th n v a₁ c ω + Bs n v a₁ c) * Dq n v a₁ c ω) ?_ hU1 hu yk gk hyk0 hgk0 ?_ hDk
    (fun n ω => τh n ω * yk n + (τh n ω + 1) * yD n ω) (fun n => gτ n * gk n + (gτ n + 1) * gD n)
    (fun n ω => add_nonneg (mul_nonneg (hτ0 n ω) (hyk0 n)) (mul_nonneg (by linarith [hτ0 n ω]) (hyD0 n ω)))
    (fun n => add_nonneg (mul_nonneg (hgτ0 n) (hgk0 n)) (mul_nonneg (by linarith [hgτ0 n]) (hgD0 n))) ?_
    (BAExp14a_Dom.add hsz (BAExp14a_Dom.mul hsz (fun n _ => hyk0 n) hgτ0 hDτ hDk)
      (BAExp14a_Dom.mul hsz hyD0 (fun n => by linarith [hgτ0 n]) (BAExp14a_Dom.add hsz hDτ
        (BAExp14a_Dom.refl hsz (g := fun _ => (1 : ℝ)) fun _ => zero_le_one)) hDD))
    (Kτ + Kk + KD + 1) ?_ hK hdet hrnd
  · intro n v ω
    rw [hΦ]
    exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => by ring
  · filter_upwards [hBs, hKq] with n hB hk v a₁ c
    rw [norm_mul]
    calc ‖Bs n v a₁ c‖ * ‖Kq n v a₁ c‖ ≤ 1 * yk n := mul_le_mul (hB v a₁ c) (hk v a₁ c) (norm_nonneg _) zero_le_one
      _ = yk n := one_mul _
  · filter_upwards [hBs, hKq, hTh, hDq] with n hB hk hT hD v a₁ c ω
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]; exact mul_le_mul (hT v a₁ c ω) (hk v a₁ c) (norm_nonneg _) (hτ0 n ω)
    · rw [norm_mul]
      refine mul_le_mul ((norm_add_le _ _).trans (add_le_add (hT v a₁ c ω) (hB v a₁ c))) (hD v a₁ c ω) (norm_nonneg _) (by linarith [hτ0 n ω])
  · filter_upwards [hτenv, hkenv, hDenv, hsz.eventually (eventually_ge_atTop 3)] with n h1 h2 h3 h4 ω
    exact BAExp14b2_env3 (by exact_mod_cast h4) Kτ Kk KD (hτ0 n ω) (hyk0 n) (hyD0 n ω) (h1 ω) h2 (h3 ω)

/-- **Form B** (`T2a`, `T2b`): `Φ = Σ_{a₁,c} u X ((K + Δ) - ρ (T̂ + B))` with `K` deterministic, `Δ` the fluctuation of the loop,
`ρ` deterministic (`≤ ρ_b ≺ g_ρ`; `ρ = W^{-d} M^{(B)}`), `T̂` the fluctuation of a twisted one-loop, `|B| ≤ 1`. -/
theorem BAExp14b2_closeB (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hDa : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)))
    (hP3 : PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
      (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)))
    {V : ℕ → Type} (Φ : ∀ n, V n → sz.SeqΩ → ℂ)
    (u Bs Kq ρ : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → ℂ)
    (Th Dq : ∀ n, V n → Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → sz.SeqΩ → ℂ)
    (hΦ : ∀ n v ω, Φ n v ω = ∑ a₁, ∑ c, u n v a₁ c * BAExp14a_X sz z n (t n) ω a₁ *
      ((Kq n v a₁ c + Dq n v a₁ c ω) - ρ n v a₁ c * (Th n v a₁ c ω + Bs n v a₁ c)))
    {U1 : ℝ} (hU1 : 0 ≤ U1) (hu : ∀ᶠ n in atTop, ∀ v, ∑ a₁, ∑ c, ‖u n v a₁ c‖ ≤ U1)
    (τh : ∀ n, sz.SeqΩ → ℝ) (gτ : ℕ → ℝ) (hτ0 : ∀ n ω, 0 ≤ τh n ω) (hgτ0 : ∀ n, 0 ≤ gτ n)
    (hTh : ∀ᶠ n in atTop, ∀ v a₁ c ω, ‖Th n v a₁ c ω‖ ≤ τh n ω) (hBs : ∀ᶠ n in atTop, ∀ v a₁ c, ‖Bs n v a₁ c‖ ≤ 1)
    (hDτ : BAExp14a_Dom sz (BAExp14a_μ sz) τh gτ)
    (yk gk : ℕ → ℝ) (hyk0 : ∀ n, 0 ≤ yk n) (hgk0 : ∀ n, 0 ≤ gk n)
    (hKq : ∀ᶠ n in atTop, ∀ v a₁ c, ‖Kq n v a₁ c‖ ≤ yk n) (hDk : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => yk n) gk)
    (rb gρ : ℕ → ℝ) (hrb0 : ∀ n, 0 ≤ rb n) (hgρ0 : ∀ n, 0 ≤ gρ n)
    (hρ : ∀ᶠ n in atTop, ∀ v a₁ c, ‖ρ n v a₁ c‖ ≤ rb n) (hDρ : BAExp14a_Dom sz (BAExp14a_μ sz) (fun n _ => rb n) gρ)
    (yD : ∀ n, sz.SeqΩ → ℝ) (gD : ℕ → ℝ) (hyD0 : ∀ n ω, 0 ≤ yD n ω) (hgD0 : ∀ n, 0 ≤ gD n)
    (hDq : ∀ᶠ n in atTop, ∀ v a₁ c ω, ‖Dq n v a₁ c ω‖ ≤ yD n ω) (hDD : BAExp14a_Dom sz (BAExp14a_μ sz) yD gD)
    (Kτ Kρ KD : ℕ) (hτenv : ∀ᶠ n in atTop, ∀ ω, τh n ω ≤ ((sz.size n : ℕ) : ℝ) ^ Kτ)
    (hrenv : ∀ᶠ n in atTop, rb n ≤ ((sz.size n : ℕ) : ℝ) ^ Kρ)
    (hDenv : ∀ᶠ n in atTop, ∀ ω, yD n ω ≤ ((sz.size n : ℕ) : ℝ) ^ KD)
    {K : ℝ} (hK : 0 < K)
    (hdet : ∀ᶠ n in atTop, U1 * ((gk n + gρ n) * (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) ≤
      K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))
    (hrnd : ∀ᶠ n in atTop, U1 * (sz.Bctl n (t n) * (gD n + gρ n * gτ n)) ≤ K * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :
    PrecL sz (BAExp14a_μ sz) (U := V) (fun n v _ => ‖∫ ω, Φ n v ω ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  refine BAExp14b2_close hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3 Φ u (fun n v a₁ c => Kq n v a₁ c - ρ n v a₁ c * Bs n v a₁ c)
    (fun n v a₁ c ω => Dq n v a₁ c ω - ρ n v a₁ c * Th n v a₁ c ω) ?_ hU1 hu (fun n => yk n + rb n) (fun n => gk n + gρ n)
    (fun n => add_nonneg (hyk0 n) (hrb0 n)) (fun n => add_nonneg (hgk0 n) (hgρ0 n)) ?_ (BAExp14a_Dom.add hsz hDk hDρ)
    (fun n ω => yD n ω + rb n * τh n ω) (fun n => gD n + gρ n * gτ n)
    (fun n ω => add_nonneg (hyD0 n ω) (mul_nonneg (hrb0 n) (hτ0 n ω)))
    (fun n => add_nonneg (hgD0 n) (mul_nonneg (hgρ0 n) (hgτ0 n))) ?_
    (BAExp14a_Dom.add hsz hDD (BAExp14a_Dom.mul hsz hτ0 hgρ0 hDρ hDτ)) (KD + Kρ + Kτ + 1) ?_ hK hdet hrnd
  · intro n v ω
    rw [hΦ]
    exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => by ring
  · filter_upwards [hBs, hKq, hρ] with n hB hk hr v a₁ c
    refine (norm_sub_le _ _).trans (add_le_add (hk v a₁ c) ?_)
    rw [norm_mul]
    calc ‖ρ n v a₁ c‖ * ‖Bs n v a₁ c‖ ≤ rb n * 1 := mul_le_mul (hr v a₁ c) (hB v a₁ c) (norm_nonneg _) (hrb0 n)
      _ = rb n := mul_one _
  · filter_upwards [hρ, hTh, hDq] with n hr hT hD v a₁ c ω
    refine (norm_sub_le _ _).trans (add_le_add (hD v a₁ c ω) ?_)
    rw [norm_mul]
    exact mul_le_mul (hr v a₁ c) (hT v a₁ c ω) (norm_nonneg _) (hrb0 n)
  · filter_upwards [hτenv, hrenv, hDenv, hsz.eventually (eventually_ge_atTop 2)] with n h1 h3 h4 h5 ω
    exact BAExp14b2_env2 (by exact_mod_cast h5) KD Kρ Kτ (hrb0 n) (hτ0 n ω) (h4 ω) h3 (h1 ω)

end Master

/-! ## 6. Arithmetic in `s = 𝔟^{1/2}` -/

section Arith

/-- `𝔟 = s²`, `𝔟^{3/2} = s³`, `𝔟^{5/2} = s⁵` with `0 < s ≤ 2` when `0 < 𝔟 ≤ 2`. -/
theorem BAExp14b2_s {B : ℝ} (hB : 0 < B) (hB2 : B ≤ 2) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 2 ∧ B = s ^ 2 ∧ B ^ (3 / 2 : ℝ) = s ^ 3 ∧ B ^ (5 / 2 : ℝ) = s ^ 5 := by
  refine ⟨B ^ (1 / 2 : ℝ), Real.rpow_pos_of_pos hB _, ?_, ?_, ?_, ?_⟩
  · have h1 : (B ^ (1 / 2 : ℝ)) ^ 2 = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]; norm_num
    have h0 : 0 < B ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hB _
    nlinarith
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]; norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]; norm_num

/-- A polynomial in `s` of order `≥ 5` against `ω₁ s⁵`: `s ≤ 2`, `ω₁ ≥ 1`. -/
theorem BAExp14b2_poly {s U ω1 : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hU : 0 ≤ U) (hω : 1 ≤ ω1) {c5 c6 c7 c8 : ℝ}
    (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) :
    U * (c5 * s ^ 5 + c6 * s ^ 6 + c7 * s ^ 7 + c8 * s ^ 8) ≤ (U * (c5 + 2 * c6 + 4 * c7 + 8 * c8)) * (ω1 * s ^ 5) := by
  have hs5 : 0 < s ^ 5 := pow_pos hs 5
  have e6 : s ^ 6 ≤ 2 * s ^ 5 := by nlinarith
  have e7 : s ^ 7 ≤ 4 * s ^ 5 := by nlinarith [mul_nonneg hs.le hs5.le]
  have e8 : s ^ 8 ≤ 8 * s ^ 5 := by nlinarith [mul_nonneg hs.le hs5.le, mul_nonneg (mul_nonneg hs.le hs.le) hs5.le]
  have hP : c5 * s ^ 5 + c6 * s ^ 6 + c7 * s ^ 7 + c8 * s ^ 8 ≤ (c5 + 2 * c6 + 4 * c7 + 8 * c8) * s ^ 5 := by
    nlinarith [mul_le_mul_of_nonneg_left e6 h6, mul_le_mul_of_nonneg_left e7 h7, mul_le_mul_of_nonneg_left e8 h8]
  have hc : 0 ≤ c5 + 2 * c6 + 4 * c7 + 8 * c8 := by positivity
  calc U * (c5 * s ^ 5 + c6 * s ^ 6 + c7 * s ^ 7 + c8 * s ^ 8) ≤ U * ((c5 + 2 * c6 + 4 * c7 + 8 * c8) * s ^ 5) :=
        mul_le_mul_of_nonneg_left hP hU
    _ = (U * (c5 + 2 * c6 + 4 * c7 + 8 * c8)) * (1 * s ^ 5) := by ring
    _ ≤ (U * (c5 + 2 * c6 + 4 * c7 + 8 * c8)) * (ω1 * s ^ 5) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hω hs5.le) (mul_nonneg hU hc)

/-- `BAExp14b2_poly` against a constant `K`. -/
theorem BAExp14b2_polyK {s U ω1 K : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) (hU : 0 ≤ U) (hω : 1 ≤ ω1) {c5 c6 c7 c8 : ℝ}
    (h5 : 0 ≤ c5) (h6 : 0 ≤ c6) (h7 : 0 ≤ c7) (h8 : 0 ≤ c8) (hK : U * (c5 + 2 * c6 + 4 * c7 + 8 * c8) ≤ K) :
    U * (c5 * s ^ 5 + c6 * s ^ 6 + c7 * s ^ 7 + c8 * s ^ 8) ≤ K * (ω1 * s ^ 5) :=
  (BAExp14b2_poly hs hs2 hU hω h5 h6 h7 h8).trans
    (mul_le_mul_of_nonneg_right hK (mul_nonneg (by linarith) (pow_pos hs 5).le))

end Arith

/-! ## 7. The families `D1t, D2t, T2a, T2b` -/

section Fam

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The fluctuation of `Tr(G^σ P_{ac})`: `twTr c a` (`σ = +`) or the conjugate of `twTr a c` (`σ = −`). -/
def BAExp14b2_Th (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a c : Zd (k + 2) (sz.L n)) : ℂ :=
  if σ then twTr (baFMz sz z) n t ω c a else (starRingEnd ℂ) (twTr (baFMz sz z) n t ω a c)

/-- The deterministic part of `Tr(G^σ P_{ac})`: `M^{(B)}_{ca}` (`σ = +`) or `\overline{M^{(B)}_{ac}}` (`σ = −`). -/
def BAExp14b2_Bs (z : ℕ → ℂ) (n : ℕ) (σ : Bool) (a c : Zd (k + 2) (sz.L n)) : ℂ :=
  if σ then BAExp14b_MB sz z n c a else (starRingEnd ℂ) (BAExp14b_MB sz z n a c)

/-- **Bridge (a), both charges, split form**: `Tr(G^σ P_{ac}) = Th + Bs`. -/
theorem BAExp14b2_Tsplit (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a c : Zd (k + 2) (sz.L n)) (hm : 0 < ((baFMz sz z).m n).im) :
    twTrP n (twChg ((baFMz sz z).G n t ω) σ) a c = BAExp14b2_Th z n t ω σ a c + BAExp14b2_Bs z n σ a c := by
  rw [BAExp14b2_twTrP_chg sz z n t ω σ a c hm, twMB_ba z n hm]
  cases σ <;> simp [BAExp14b2_Th, BAExp14b2_Bs, map_add] <;> rfl

theorem BAExp14b2_Bs_le {n : ℕ} {t CM S : ℝ} (hf : BAExp14a_Facts sz z n t CM S) (hm : 0 < ((baFMz sz z).m n).im) (σ : Bool)
    (a c : Zd (k + 2) (sz.L n)) : ‖BAExp14b2_Bs z n σ a c‖ ≤ 1 := by
  cases σ
  · simpa [BAExp14b2_Bs] using BAExp14b2_MB_le_one hf hm a c
  · simpa [BAExp14b2_Bs] using BAExp14b2_MB_le_one hf hm c a

/-- Any `σ : Fin 2 → α` is `![σ 0, σ 1]`. -/
theorem BAExp14b2_vec2 {α : Type*} (σ : Fin 2 → α) : σ = ![σ 0, σ 1] := by
  funext i; fin_cases i <;> rfl

/-- **The data shared by the four families**: the facts along the flow, `a ≺ 𝔟`, `P3`, and the TL1 variable `τ̂` with its `≺ 𝔟` and its envelope. -/
private theorem BAExp14b2_base (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    ∃ CM S : ℝ, 0 ≤ CM ∧ 1 ≤ S ∧
      (∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S) ∧
      BAExp14a_Dom sz (BAExp14a_μ sz) (fun n ω => BAExp14a_a sz z n (t n) ω) (fun n => sz.Bctl n (t n)) ∧
      PrecL sz (BAExp14a_μ sz) (U := fun n => Zd (k + 2) (sz.L n))
        (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂(BAExp14a_μ sz)‖) (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) ∧
      BAExp14a_Dom sz (BAExp14a_μ sz)
        (fun n ω => BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖))
        (fun n => sz.Bctl n (t n)) ∧
      (∀ᶠ n in atTop, ∀ ω, BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) ≤
        ((sz.size n : ℕ) : ℝ) ^ 3) := by
  obtain ⟨CM, S, hCM, hS, hfacts⟩ := BAExp14a_facts_of_flow hk hκ h𝔡 hflow
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  refine ⟨CM, S, hCM, hS, hfacts, BAExp14a_Dom_a (μ := BAExp14a_μ sz) t hflow hκ hA,
    BAExp14b2_P3 hk hκ hε h𝔡 hflow ht0 ht hE hA, BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
      (fun n (p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) ω => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) _ hT1, ?_⟩
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts 2
  filter_upwards [hev] with n hn ω
  obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
  refine BAExp14b2_sup_le fun p => ?_
  have h1 := BAExp14b2_tw_le hκ hflow (ht0 n) (ht n) hf ω p.1 p.2
  have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hK0
  calc _ ≤ ((baFMz sz z).eta n (t n))⁻¹ + 1 := h1
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 + 1 := by linarith
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by nlinarith [pow_pos (by linarith : (0 : ℝ) < ((sz.size n : ℕ) : ℝ)) 2]



/-- **`D1t`** (as `lwExpI1K_holds` in `Graph/LWExpTerm4.lean`): `‖𝔼 D1t‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}`, uniformly in `(σ, a, b)`.  Proof:
`D1t = t Σ_{a₁,c} M^{(B)}_{aa₁} M^{(B)}_{a₁c} X_{a₁} Tr(G^σ P_{ac}) 𝓛^{(2)}_{(+,σ),(b,c)}`, `Tr(G^σ P_{ac}) = T̂ + B` (bridge (a)),
`𝓛^{(2)} = 𝒦^{(2)} + (𝓛 - 𝒦)`: the term `B 𝒦^{(2)} X` is paid with P3 (`𝔟^{3/2} · 𝔟`, zero slack), `T̂ 𝒦^{(2)} X` (`𝔟³`) and
`(T̂ + B)(𝓛 - 𝒦) X` (`𝔟 · 𝔟²`) pathwise. -/
private theorem BAExp14b2_D1t (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω 0 p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hKb := baKbound_holds (k + 2) (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 2 (by norm_num)
  have hDk := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n))) (_ : sz.SeqΩ) => ‖(baFMz sz z).K n (t n) q.1 q.2‖) _ hKb
  have hDl := BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n))) ω =>
      ‖(baFMz sz z).L n (t n) q.1 q.2 ω - (baFMz sz z).K n (t n) q.1 q.2‖) _ (hK 2 (by norm_num))
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts 2
  have hdk := BAExp14b2_det_ev (y := fun n => BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) =>
    ‖(baFMz sz z).K n (t n) q.1 q.2‖)) hsz hDk one_pos
  have hykN : ∀ᶠ n in atTop, BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) =>
      ‖(baFMz sz z).K n (t n) q.1 q.2‖) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by
    filter_upwards [hdk, hev] with n h1 hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hBn : 0 ≤ sz.Bctl n (t n) := hB n
    simp only [Real.rpow_one, Nat.reduceSub, pow_one] at h1
    nlinarith
  refine BAExp14b2_closeA hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3
    (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FS2 sz z n (t n) ω 0 v.1 v.2.1 v.2.2)
    (fun n v a₁ c => (t n : ℂ) * (BAExp14b_MB sz z n v.2.1 a₁ * BAExp14b_MB sz z n a₁ c))
    (fun n v a₁ c => BAExp14b2_Bs z n v.1 v.2.1 c)
    (fun n v a₁ c => (baFMz sz z).K n (t n) ![true, v.1] ![v.2.2, c])
    (fun n v a₁ c ω => BAExp14b2_Th z n (t n) ω v.1 v.2.1 c)
    (fun n v a₁ c ω => (baFMz sz z).L n (t n) ![true, v.1] ![v.2.2, c] ω - (baFMz sz z).K n (t n) ![true, v.1] ![v.2.2, c])
    ?_ (U1 := CM * CM) (by positivity) ?_
    (fun n ω => BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖))
    (fun n => sz.Bctl n (t n)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _) hB ?_ ?_ hDτ
    (fun n => BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).K n (t n) q.1 q.2‖))
    (fun n => (sz.Bctl n (t n)) ^ (2 - 1)) (fun n => BAExp14b2_sup_nonneg fun q => norm_nonneg _) (fun n => pow_nonneg (hB n) _) ?_ hDk
    (fun n ω => BAExp14b2_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) =>
      ‖(baFMz sz z).L n (t n) q.1 q.2 ω - (baFMz sz z).K n (t n) q.1 q.2‖))
    (fun n => (sz.Bctl n (t n)) ^ 2) (fun n ω => BAExp14b2_sup_nonneg fun q => norm_nonneg _) (fun n => pow_nonneg (hB n) _) ?_ hDl
    3 2 5 hτenv ?_ ?_ (K := 12 * (CM * CM) + 1) (by positivity) ?_ ?_
  · intro n v ω
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hm := hr.1.1
    rw [BAExp14b_FS2_block hr (ht0 n) (ht1 n)]
    simp only [BAExp14b_BS2, Matrix.cons_val_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [BAExp14b2_Tsplit n (t n) ω v.1 v.2.1 c hm]
    ring
  · filter_upwards [hfacts] with n hn v
    have hf := hn (t n) (ht0 n) (ht n)
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    calc ∑ a₁, ∑ c, ‖(t n : ℂ) * (BAExp14b_MB sz z n v.2.1 a₁ * BAExp14b_MB sz z n a₁ c)‖
        ≤ ∑ a₁, ∑ c, ‖BAExp14b_MB sz z n v.2.1 a₁‖ * ‖BAExp14b_MB sz z n a₁ c‖ := by
          refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht0 n)]
          have : t n ≤ 1 := (ht1 n).le
          nlinarith [mul_nonneg (norm_nonneg (BAExp14b_MB sz z n v.2.1 a₁)) (norm_nonneg (BAExp14b_MB sz z n a₁ c))]
      _ = ∑ a₁, ‖BAExp14b_MB sz z n v.2.1 a₁‖ * ∑ c, ‖BAExp14b_MB sz z n a₁ c‖ := by simp only [Finset.mul_sum]
      _ ≤ ∑ a₁, ‖BAExp14b_MB sz z n v.2.1 a₁‖ * CM :=
          Finset.sum_le_sum fun a₁ _ => mul_le_mul_of_nonneg_left (BAExp14b2_MB_row hr hf a₁) (norm_nonneg _)
      _ = (∑ a₁, ‖BAExp14b_MB sz z n v.2.1 a₁‖) * CM := (Finset.sum_mul _ _ _).symm
      _ ≤ CM * CM := mul_le_mul_of_nonneg_right (BAExp14b2_MB_row hr hf _) hCM
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    cases σ
    · change ‖BAExp14b2_Th z n (t n) ω false a c‖ ≤ _
      simp only [BAExp14b2_Th, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (a, c)
    · change ‖BAExp14b2_Th z n (t n) ω true a c‖ ≤ _
      simp only [BAExp14b2_Th, ↓reduceIte]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (c, a)
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact BAExp14b2_Bs_le (hn (t n) (ht0 n) (ht n)) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1 σ a c
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c
    exact BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).K n (t n) q.1 q.2‖)
      (![true, σ], ![b, c])
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    exact BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) =>
      ‖(baFMz sz z).L n (t n) q.1 q.2 ω - (baFMz sz z).K n (t n) q.1 q.2‖) (![true, σ], ![b, c])
  · exact hykN
  · filter_upwards [hykN, hev] with n hyk hn ω
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hη := hf.hη
    refine BAExp14b2_sup_le fun q => ?_
    have hL := BAExp14b2_L2_le hκ hflow (ht0 n) (ht n) (q.1 0) (q.1 1) (q.2 0) (q.2 1) ω
    rw [← BAExp14b2_vec2 q.1, ← BAExp14b2_vec2 q.2] at hL
    have hKq := BAExp14b2_le_sup (fun q : (Fin 2 → Bool) × (Fin 2 → Zd (k + 2) (sz.L n)) => ‖(baFMz sz z).K n (t n) q.1 q.2‖) q
    have hη0 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := inv_nonneg.2 hη.le
    have hηsq : (((baFMz sz z).eta n (t n))⁻¹) ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hη0 hηN 2
    calc _ ≤ ‖(baFMz sz z).L n (t n) q.1 q.2 ω‖ + ‖(baFMz sz z).K n (t n) q.1 q.2‖ := norm_sub_le _ _
      _ ≤ (((baFMz sz z).eta n (t n))⁻¹) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 := add_le_add hL (hKq.trans hyk)
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ 2) ^ 2 + ((sz.size n : ℕ) : ℝ) ^ 2 := by linarith
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 5 := by
          have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
          have h2 := pow_pos hN0 2
          have h3 := pow_pos hN0 3
          nlinarith
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    simp only [Nat.reduceSub, pow_one]
    rw [h32, h52, hBs']
    calc CM * CM * (s ^ 2 * s ^ 3) = (CM * CM) * (1 * s ^ 5 + 0 * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 (by positivity) hω zero_le_one le_rfl le_rfl le_rfl (by nlinarith [mul_nonneg hCM hCM])
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    simp only [Nat.reduceSub, pow_one]
    rw [h52, hBs']
    calc CM * CM * (s ^ 2 * (s ^ 2 * s ^ 2 + (s ^ 2 + 1) * (s ^ 2) ^ 2)) =
          (CM * CM) * (0 * s ^ 5 + 2 * s ^ 6 + 0 * s ^ 7 + 1 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 (by positivity) hω le_rfl zero_le_two le_rfl zero_le_one (by nlinarith [mul_nonneg hCM hCM])

/-- A deterministic eventual bound `y ≤ g` is a deterministic `≺`. -/
theorem BAExp14b2_Dom_of_le_ev {μ : Measure sz.SeqΩ} {y g : ℕ → ℝ} (h : ∀ᶠ n in atTop, y n ≤ g n) (hg0 : ∀ n, 0 ≤ g n)
    (hsz : Tendsto sz.size atTop atTop) : BAExp14a_Dom sz μ (fun n _ => y n) g :=
  BAExp14a_prec_of_le_ev (h.mono fun n hn _ _ => hn) (BAExp14a_Dom.refl hsz (g := g) hg0)

theorem BAExp14b2_twChg_true {n : ℕ} (X : Idx (k + 2) (sz.L n) (sz.W n) → Idx (k + 2) (sz.L n) (sz.W n) → ℂ) :
    twChg X true = X := funext fun x => funext fun y => by simp [twChg]

/-- **The TL2 data of the families `D2t, T2a, T2b`**: `‖K̃‖ ≤ C 𝔟` (`twK_bound_holds`), the TL2 variable `λ̃ = max |L̃ - K̃|` with `λ̃ ≺ 𝔟^{3/2}`
and its envelope, and `C 𝔟 ≤ N`. -/
private theorem BAExp14b2_tl2 (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) {CM S : ℝ}
    (hfacts : ∀ᶠ n in atTop, ∀ t' : ℝ, 0 ≤ t' → t' ≤ BAflowT0 sz z n → BAExp14a_Facts sz z n t' CM S)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd (k + 2) (sz.L n)),
        ‖twK (baFMz sz z) n (t n) σ a c₁ c₂‖ ≤ C * sz.Bctl n (t n)) ∧
      BAExp14a_Dom sz (BAExp14a_μ sz)
        (fun n ω => BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
          ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖))
        (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) ∧
      (∀ᶠ n in atTop, ∀ ω, BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
          ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖) ≤
        ((sz.size n : ℕ) : ℝ) ^ 5) ∧
      (∀ᶠ n in atTop, C * sz.Bctl n (t n) ≤ ((sz.size n : ℕ) : ℝ) ^ 1) := by
  obtain ⟨C, hC, hKb⟩ := twK_bound_holds (k + 2) (by omega) κ ε 𝔡 hκ hε h𝔡
  have hKt := (hKb 𝔠 sz z hflow t ht0 ht)
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts (2 * C + 2)
  refine ⟨C, hC, hKt.mono fun n hn σ a c₁ c₂ => (hn σ c₁ c₂).1 a, BAExp14b2_Dom_sup (μ := BAExp14a_μ sz)
    (fun n (p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n)) ω =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖) _ hT2, ?_, ?_⟩
  · filter_upwards [hev, hKt] with n hn hK ω
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : 2 * C + 2 ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hη := hf.hη
    have hη0 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := inv_nonneg.2 hη.le
    have hηsq : (((baFMz sz z).eta n (t n))⁻¹) ^ 2 ≤ (((sz.size n : ℕ) : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ hη0 hηN 2
    refine BAExp14b2_sup_le fun p => ?_
    have hL := BAExp14b2_Lt_le hκ hflow (ht0 n) (ht n) (p.1 0) (p.1 1) ω p.2.1 p.2.2.1 p.2.2.2
    have hK1 := (hK p.1 p.2.2.1 p.2.2.2).1 p.2.1
    have hBn : sz.Bctl n (t n) ≤ 2 := hB2
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have h2 := pow_pos hN0 2
    have h3 := pow_pos hN0 3
    have h4' := pow_pos hN0 4
    calc ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖
        ≤ ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2‖ + ‖twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖ := norm_sub_le _ _
      _ ≤ (((baFMz sz z).eta n (t n))⁻¹) ^ 2 + 2 * C := add_le_add hL (hK1.trans (by nlinarith [(STBctl_pos sz n ht1n).le]))
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 4 + ((sz.size n : ℕ) : ℝ) := by nlinarith
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ 5 := by nlinarith
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : 2 * C + 2 ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hBn := (STBctl_pos sz n ht1n).le
    rw [pow_one]
    nlinarith

/-- **`D2t`** (as `lwExpI1K_holds`): `‖𝔼 D2t‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}`, uniformly in `(σ, a, b)`.  `D2t = t Σ_{a₁,c} M^{(B)}_{ac} M^{(B)}_{a₁b} X_{a₁}
Tr(G^σ P_{ac}) L̃_{(σ,+);(c;a₁,b)}` with `L̃ = K̃ + (L̃ - K̃)` (TL2, `3/2`) and `Tr(G^σ P_{ac}) = T̂ + B`: `B K̃ X` is paid with P3,
`T̂ K̃ X` (`𝔟³`) pathwise, `(T̂ + B)(L̃ - K̃) X` with TL2 (`𝔟^{3/2}` times `𝔟`, zero slack). -/
private theorem BAExp14b2_D2t (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω 1 p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  obtain ⟨C, hC, hKt, hDlt, hLtenv, hCb⟩ := BAExp14b2_tl2 hk hκ hε h𝔡 hflow ht0 ht hfacts hT2
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts 2
  refine BAExp14b2_closeA hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3
    (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FS2 sz z n (t n) ω 1 v.1 v.2.1 v.2.2)
    (fun n v a₁ c => (t n : ℂ) * (BAExp14b_MB sz z n v.2.1 c * BAExp14b_MB sz z n a₁ v.2.2))
    (fun n v a₁ c => BAExp14b2_Bs z n v.1 v.2.1 c)
    (fun n v a₁ c => twK (baFMz sz z) n (t n) ![v.1, true] c a₁ v.2.2)
    (fun n v a₁ c ω => BAExp14b2_Th z n (t n) ω v.1 v.2.1 c)
    (fun n v a₁ c ω => twL2' (baFMz sz z) n (t n) ω ![v.1, true] c a₁ v.2.2 - twK (baFMz sz z) n (t n) ![v.1, true] c a₁ v.2.2)
    ?_ (U1 := CM * CM) (by positivity) ?_
    (fun n ω => BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖))
    (fun n => sz.Bctl n (t n)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _) hB ?_ ?_ hDτ
    (fun n => C * sz.Bctl n (t n)) (fun n => C * sz.Bctl n (t n)) (fun n => mul_nonneg hC.le (hB n)) (fun n => mul_nonneg hC.le (hB n)) ?_
    (BAExp14a_Dom.refl hsz (g := fun n => C * sz.Bctl n (t n)) fun n => mul_nonneg hC.le (hB n))
    (fun n ω => BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖))
    (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _)
    (fun n => Real.rpow_nonneg (hB n) _) ?_ hDlt 3 1 5 hτenv hCb hLtenv (K := CM * CM * (2 * C + 5) + 1) (by positivity) ?_ ?_
  · intro n v ω
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hm := hr.1.1
    rw [BAExp14b_FS2_block hr (ht0 n) (ht1 n)]
    simp only [BAExp14b_BS2, Matrix.cons_val_one]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hLt : twL2' (baFMz sz z) n (t n) ω ![v.1, true] c a₁ v.2.2 =
        twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) ((baFMz sz z).G n (t n) ω) c a₁ v.2.2 := by
      change twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) (twChg ((baFMz sz z).G n (t n) ω) true) c a₁ v.2.2 = _
      rw [BAExp14b2_twChg_true]
    rw [BAExp14b2_Tsplit n (t n) ω v.1 v.2.1 c hm, ← hLt]
    ring
  · filter_upwards [hfacts] with n hn v
    have hf := hn (t n) (ht0 n) (ht n)
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    calc ∑ a₁, ∑ c, ‖(t n : ℂ) * (BAExp14b_MB sz z n v.2.1 c * BAExp14b_MB sz z n a₁ v.2.2)‖
        ≤ ∑ a₁, ∑ c, ‖BAExp14b_MB sz z n a₁ v.2.2‖ * ‖BAExp14b_MB sz z n v.2.1 c‖ := by
          refine Finset.sum_le_sum fun a₁ _ => Finset.sum_le_sum fun c _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ht0 n)]
          have : t n ≤ 1 := (ht1 n).le
          nlinarith [mul_nonneg (norm_nonneg (BAExp14b_MB sz z n a₁ v.2.2)) (norm_nonneg (BAExp14b_MB sz z n v.2.1 c))]
      _ = (∑ a₁, ‖BAExp14b_MB sz z n a₁ v.2.2‖) * ∑ c, ‖BAExp14b_MB sz z n v.2.1 c‖ := (Finset.sum_mul_sum _ _ _ _).symm
      _ ≤ CM * CM := mul_le_mul (BAExp14b2_MB_col hr hf _) (BAExp14b2_MB_row hr hf _) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hCM
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    cases σ
    · change ‖BAExp14b2_Th z n (t n) ω false a c‖ ≤ _
      simp only [BAExp14b2_Th, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (a, c)
    · change ‖BAExp14b2_Th z n (t n) ω true a c‖ ≤ _
      simp only [BAExp14b2_Th, ↓reduceIte]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (c, a)
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact BAExp14b2_Bs_le (hn (t n) (ht0 n) (ht n)) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1 σ a c
  · filter_upwards [hKt] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact hn _ _ _ _
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    exact BAExp14b2_le_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
      (![σ, true], c, a₁, b)
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    calc CM * CM * (C * s ^ 2 * s ^ 3) = (CM * CM) * (C * s ^ 5 + 0 * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 (by positivity) hω hC.le le_rfl le_rfl le_rfl
        (by nlinarith [mul_nonneg hCM hCM, mul_nonneg (mul_nonneg hCM hCM) hC.le])
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    calc CM * CM * (s ^ 2 * (s ^ 2 * (C * s ^ 2) + (s ^ 2 + 1) * s ^ 3)) =
          (CM * CM) * (1 * s ^ 5 + C * s ^ 6 + 1 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 (by positivity) hω zero_le_one hC.le zero_le_one le_rfl
        (by nlinarith [mul_nonneg hCM hCM, mul_nonneg (mul_nonneg hCM hCM) hC.le])

/-- The tie `M_{wγ} = 1[offsets equal] M^{(B)}_{[w][γ]}` of the carrier (`BAMfine_eq`). -/
theorem BAExp14b2_M_tie (n : ℕ) (hm : 0 < ((baFMz sz z).m n).im) (w γ : Idx (k + 2) (sz.L n) (sz.W n)) :
    (baFMz sz z).M n w γ = if (split (k + 2) (sz.L n) (sz.W n) w).2 = (split (k + 2) (sz.L n) (sz.W n) γ).2 then
      BAExp14b_MB sz z n (split (k + 2) (sz.L n) (sz.W n) w).1 (split (k + 2) (sz.L n) (sz.W n) γ).1 else 0 :=
  BAMfine_eq sz (BAflowLam0 sz z) (BAflowEs sz z) n hm w γ

/-- **`W^{-d} ≤ (𝔡⁻² + 1) 𝔟`** eventually (`twB0_ge_holds`). -/
theorem BAExp14b2_Wd_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ ≤ (𝔡⁻¹ ^ 2 + 1) * sz.Bctl n (t n) := by
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  filter_upwards [twB0_ge_holds sz 𝔡 hflow.1.2.2.2.2 t ht0 fun n => (ht1 n).le] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hc : 0 < 𝔡⁻¹ ^ 2 + 1 := by positivity
  rw [inv_le_iff_one_le_mul₀ hW]
  have := mul_le_mul_of_nonneg_left hn hc.le
  rw [mul_inv_cancel₀ hc.ne'] at this
  nlinarith

/-- **`T2a`** (as `lwExpI1K_holds`): `‖𝔼 T2a‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}`, uniformly in `(σ, a, b)`.  `T2a = Σ_{a₁,c} (ω-1)_{a₁c} M^{(B)}_{ac} X_{a₁} L̃(Ǧ, G^σ; b, a, c)`; the
slot-1 circle (bridge (b)) gives `L̃(Ǧ, G^σ) = L̃ - W^{-d} M^{(B)}_{cb} Tr(G^σ P_{ab})`, `L̃ = K̃ + (L̃ - K̃)`: `K̃ X` is paid with P3
(`𝔟 · 𝔟^{3/2}`), `W^{-d} B X` with P3 and `W^{-d} ≲ 𝔟` (`twB0_ge_holds`), `X (L̃ - K̃)` with TL2 (`𝔟 · 𝔟^{3/2}`), `X W^{-d} T̂` with TL1. -/
private theorem BAExp14b2_T2a (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω 2 p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  obtain ⟨C, hC, hKt, hDlt, hLtenv, hCb⟩ := BAExp14b2_tl2 hk hκ hε h𝔡 hflow ht0 ht hfacts hT2
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts 2
  have hWd := BAExp14b2_Wd_le hκ hflow ht0 ht
  have hc1 : 0 < 𝔡⁻¹ ^ 2 + 1 := by positivity
  refine BAExp14b2_closeB hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3
    (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FS2 sz z n (t n) ω 2 v.1 v.2.1 v.2.2)
    (fun n v a₁ c => (BAExp14b_om sz z n (t n) - 1) a₁ c * BAExp14b_MB sz z n v.2.1 c)
    (fun n v a₁ c => BAExp14b2_Bs z n v.1 v.2.1 v.2.2)
    (fun n v a₁ c => twK (baFMz sz z) n (t n) ![true, v.1] v.2.2 v.2.1 c)
    (fun n v a₁ c => (((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n c v.2.2)
    (fun n v a₁ c ω => BAExp14b2_Th z n (t n) ω v.1 v.2.1 v.2.2)
    (fun n v a₁ c ω => twL2' (baFMz sz z) n (t n) ω ![true, v.1] v.2.2 v.2.1 c - twK (baFMz sz z) n (t n) ![true, v.1] v.2.2 v.2.1 c)
    ?_ (U1 := S * CM) (by positivity) ?_
    (fun n ω => BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖))
    (fun n => sz.Bctl n (t n)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _) hB ?_ ?_ hDτ
    (fun n => C * sz.Bctl n (t n)) (fun n => C * sz.Bctl n (t n)) (fun n => mul_nonneg hC.le (hB n)) (fun n => mul_nonneg hC.le (hB n)) ?_
    (BAExp14a_Dom.refl hsz (g := fun n => C * sz.Bctl n (t n)) fun n => mul_nonneg hC.le (hB n))
    (fun n => (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) (fun n => (𝔡⁻¹ ^ 2 + 1) * sz.Bctl n (t n))
    (fun n => by positivity) (fun n => mul_nonneg hc1.le (hB n)) ?_
    (BAExp14b2_Dom_of_le_ev hWd (fun n => mul_nonneg hc1.le (hB n)) hsz)
    (fun n ω => BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖))
    (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _)
    (fun n => Real.rpow_nonneg (hB n) _) ?_ hDlt 3 1 5 hτenv ?_ hLtenv
    (K := S * CM * (C + 2 * (𝔡⁻¹ ^ 2 + 1) + 1) + 1) (by positivity) ?_ ?_
  · intro n v ω
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hm := hr.1.1
    rw [BAExp14b_FS2_block hr (ht0 n) (ht1 n)]
    simp only [BAExp14b_BS2, Matrix.cons_val_two]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => ?_
    have hcirc := BAExp14b2_twCirc1 sz n ((baFMz sz z).G n (t n) ω) (twChg ((baFMz sz z).G n (t n) ω) v.1) ((baFMz sz z).M n)
      (BAExp14b_MB sz z n) (BAExp14b2_M_tie n hm) v.2.2 v.2.1 c
    have hLt : twL2' (baFMz sz z) n (t n) ω ![true, v.1] v.2.2 v.2.1 c =
        twLoopX n ((baFMz sz z).G n (t n) ω) (twChg ((baFMz sz z).G n (t n) ω) v.1) v.2.2 v.2.1 c := by
      change twLoopX n (twChg ((baFMz sz z).G n (t n) ω) true) (twChg ((baFMz sz z).G n (t n) ω) v.1) v.2.2 v.2.1 c = _
      rw [BAExp14b2_twChg_true]
    have hGM : twLoopX n ((baFMz sz z).GM n (t n) ω) (twChg ((baFMz sz z).G n (t n) ω) v.1) v.2.2 v.2.1 c =
        twLoopX n (fun x y => (baFMz sz z).G n (t n) ω x y - (baFMz sz z).M n x y) (twChg ((baFMz sz z).G n (t n) ω) v.1) v.2.2 v.2.1 c := rfl
    rw [hGM, hcirc, BAExp14b2_Tsplit n (t n) ω v.1 v.2.1 v.2.2 hm, ← hLt]
    ring
  · filter_upwards [hfacts] with n hn v
    have hf := hn (t n) (ht0 n) (ht n)
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    simp only [norm_mul]
    rw [Finset.sum_comm]
    calc ∑ c, ∑ a₁, ‖(BAExp14b_om sz z n (t n) - 1) a₁ c‖ * ‖BAExp14b_MB sz z n v.2.1 c‖
        = ∑ c, (∑ a₁, ‖(BAExp14b_om sz z n (t n) - 1) a₁ c‖) * ‖BAExp14b_MB sz z n v.2.1 c‖ := by simp only [Finset.sum_mul]
      _ ≤ ∑ c, S * ‖BAExp14b_MB sz z n v.2.1 c‖ :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (BAExp14b2_om1_col hr hf c) (norm_nonneg _)
      _ = S * ∑ c, ‖BAExp14b_MB sz z n v.2.1 c‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ S * CM := mul_le_mul_of_nonneg_left (BAExp14b2_MB_row hr hf _) (by linarith)
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    cases σ
    · change ‖BAExp14b2_Th z n (t n) ω false a b‖ ≤ _
      simp only [BAExp14b2_Th, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (a, b)
    · change ‖BAExp14b2_Th z n (t n) ω true a b‖ ≤ _
      simp only [BAExp14b2_Th, ↓reduceIte]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (b, a)
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact BAExp14b2_Bs_le (hn (t n) (ht0 n) (ht n)) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1 σ a b
  · filter_upwards [hKt] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact hn _ _ _ _
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    have hf := hn (t n) (ht0 n) (ht n)
    have hm := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left (BAExp14b2_MB_le_one hf hm c b) (by positivity)
      _ = _ := mul_one _
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    exact BAExp14b2_le_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
      (![true, σ], b, a, c)
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (k + 2) := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
    rw [pow_one]
    linarith [inv_le_one_of_one_le₀ hW1]
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
    calc S * CM * ((C * s ^ 2 + (𝔡⁻¹ ^ 2 + 1) * s ^ 2) * s ^ 3) =
          (S * CM) * ((C + (𝔡⁻¹ ^ 2 + 1)) * s ^ 5 + 0 * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 hSC hω (by positivity) le_rfl le_rfl le_rfl
        (by nlinarith [mul_nonneg hSC hC.le, mul_nonneg hSC hc1.le])
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
    calc S * CM * (s ^ 2 * (s ^ 3 + (𝔡⁻¹ ^ 2 + 1) * s ^ 2 * s ^ 2)) =
          (S * CM) * (1 * s ^ 5 + (𝔡⁻¹ ^ 2 + 1) * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 hSC hω zero_le_one hc1.le le_rfl le_rfl
        (by nlinarith [mul_nonneg hSC hC.le, mul_nonneg hSC hc1.le])

/-- **`T2b`** (as `lwExpI1K_holds`): `‖𝔼 T2b‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}`, uniformly in `(σ, a, b)`.  `T2b = Σ_{a₁,c} (ω-1)_{a₁c} M^{(B)}_{cb} X_{a₁} L̃(G^σ, Ǧ; a, c, b)`; the
slot-2 circle (`twCirc_holds`) gives `L̃(G^σ, Ǧ) = L̃ - W^{-d} M^{(B)}_{ac} Tr(G^σ P_{ab})`, then as `T2a`. -/
private theorem BAExp14b2_T2b (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω 3 p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  obtain ⟨CM, S, hCM, hS, hfacts, hDa, hP3, hDτ, hτenv⟩ := BAExp14b2_base hk hκ hε h𝔡 hflow ht0 ht hE hA hT1
  obtain ⟨C, hC, hKt, hDlt, hLtenv, hCb⟩ := BAExp14b2_tl2 hk hκ hε h𝔡 hflow ht0 ht hfacts hT2
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := BAExp14a_t_lt_one hκ hflow ht
  have hB : ∀ n, 0 ≤ sz.Bctl n (t n) := fun n => (STBctl_pos sz n (ht1 n)).le
  have hev := BAExp14a_ev hκ hε h𝔡 hflow ht0 ht hfacts 2
  have hWd := BAExp14b2_Wd_le hκ hflow ht0 ht
  have hc1 : 0 < 𝔡⁻¹ ^ 2 + 1 := by positivity
  refine BAExp14b2_closeB hκ hε h𝔡 hflow ht0 ht hfacts hDa hP3
    (V := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
    (fun n v ω => BAExp14b_FS2 sz z n (t n) ω 3 v.1 v.2.1 v.2.2)
    (fun n v a₁ c => (BAExp14b_om sz z n (t n) - 1) a₁ c * BAExp14b_MB sz z n c v.2.2)
    (fun n v a₁ c => BAExp14b2_Bs z n v.1 v.2.1 v.2.2)
    (fun n v a₁ c => twK (baFMz sz z) n (t n) ![v.1, true] v.2.1 c v.2.2)
    (fun n v a₁ c => (((sz.W n : ℕ) : ℂ) ^ (k + 2))⁻¹ * BAExp14b_MB sz z n v.2.1 c)
    (fun n v a₁ c ω => BAExp14b2_Th z n (t n) ω v.1 v.2.1 v.2.2)
    (fun n v a₁ c ω => twL2' (baFMz sz z) n (t n) ω ![v.1, true] v.2.1 c v.2.2 - twK (baFMz sz z) n (t n) ![v.1, true] v.2.1 c v.2.2)
    ?_ (U1 := S * CM) (by positivity) ?_
    (fun n ω => BAExp14b2_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖))
    (fun n => sz.Bctl n (t n)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _) hB ?_ ?_ hDτ
    (fun n => C * sz.Bctl n (t n)) (fun n => C * sz.Bctl n (t n)) (fun n => mul_nonneg hC.le (hB n)) (fun n => mul_nonneg hC.le (hB n)) ?_
    (BAExp14a_Dom.refl hsz (g := fun n => C * sz.Bctl n (t n)) fun n => mul_nonneg hC.le (hB n))
    (fun n => (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) (fun n => (𝔡⁻¹ ^ 2 + 1) * sz.Bctl n (t n))
    (fun n => by positivity) (fun n => mul_nonneg hc1.le (hB n)) ?_
    (BAExp14b2_Dom_of_le_ev hWd (fun n => mul_nonneg hc1.le (hB n)) hsz)
    (fun n ω => BAExp14b2_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖))
    (fun n => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ)) (fun n ω => BAExp14b2_sup_nonneg fun p => norm_nonneg _)
    (fun n => Real.rpow_nonneg (hB n) _) ?_ hDlt 3 1 5 hτenv ?_ hLtenv
    (K := S * CM * (C + 2 * (𝔡⁻¹ ^ 2 + 1) + 1) + 1) (by positivity) ?_ ?_
  · intro n v ω
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    have hm := hr.1.1
    rw [BAExp14b_FS2_block hr (ht0 n) (ht1 n)]
    simp only [BAExp14b_BS2, Matrix.cons_val_three]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun c _ => ?_
    have hcirc := twCirc_holds sz n (twChg ((baFMz sz z).G n (t n) ω) v.1) ((baFMz sz z).G n (t n) ω) ((baFMz sz z).M n)
      (BAExp14b_MB sz z n) (BAExp14b2_M_tie n hm) v.2.1 c v.2.2
    have hLt : twL2' (baFMz sz z) n (t n) ω ![v.1, true] v.2.1 c v.2.2 =
        twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) ((baFMz sz z).G n (t n) ω) v.2.1 c v.2.2 := by
      change twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) (twChg ((baFMz sz z).G n (t n) ω) true) v.2.1 c v.2.2 = _
      rw [BAExp14b2_twChg_true]
    have hGM : twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) ((baFMz sz z).GM n (t n) ω) v.2.1 c v.2.2 =
        twLoopX n (twChg ((baFMz sz z).G n (t n) ω) v.1) (fun x y => (baFMz sz z).G n (t n) ω x y - (baFMz sz z).M n x y) v.2.1 c v.2.2 := rfl
    rw [hGM, hcirc, BAExp14b2_Tsplit n (t n) ω v.1 v.2.1 v.2.2 hm, ← hLt]
    ring
  · filter_upwards [hfacts] with n hn v
    have hf := hn (t n) (ht0 n) (ht n)
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    simp only [norm_mul]
    rw [Finset.sum_comm]
    calc ∑ c, ∑ a₁, ‖(BAExp14b_om sz z n (t n) - 1) a₁ c‖ * ‖BAExp14b_MB sz z n c v.2.2‖
        = ∑ c, (∑ a₁, ‖(BAExp14b_om sz z n (t n) - 1) a₁ c‖) * ‖BAExp14b_MB sz z n c v.2.2‖ := by simp only [Finset.sum_mul]
      _ ≤ ∑ c, S * ‖BAExp14b_MB sz z n c v.2.2‖ :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (BAExp14b2_om1_col hr hf c) (norm_nonneg _)
      _ = S * ∑ c, ‖BAExp14b_MB sz z n c v.2.2‖ := (Finset.mul_sum _ _ _).symm
      _ ≤ S * CM := mul_le_mul_of_nonneg_left (BAExp14b2_MB_col hr hf _) (by linarith)
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    cases σ
    · change ‖BAExp14b2_Th z n (t n) ω false a b‖ ≤ _
      simp only [BAExp14b2_Th, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (a, b)
    · change ‖BAExp14b2_Th z n (t n) ω true a b‖ ≤ _
      simp only [BAExp14b2_Th, ↓reduceIte]
      exact BAExp14b2_le_sup (fun p : Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) => ‖twTr (baFMz sz z) n (t n) ω p.1 p.2‖) (b, a)
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact BAExp14b2_Bs_le (hn (t n) (ht0 n) (ht n)) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1 σ a b
  · filter_upwards [hKt] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    exact hn _ _ _ _
  · filter_upwards [hfacts] with n hn
    rintro ⟨σ, a, b⟩ a₁ c
    have hf := hn (t n) (ht0 n) (ht n)
    have hm := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1.1
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹ * 1 := mul_le_mul_of_nonneg_left (BAExp14b2_MB_le_one hf hm a c) (by positivity)
      _ = _ := mul_one _
  · refine Eventually.of_forall fun n => ?_
    rintro ⟨σ, a, b⟩ a₁ c ω
    exact BAExp14b2_le_sup (fun p : (Fin 2 → Bool) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n) =>
      ‖twL2' (baFMz sz z) n (t n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK (baFMz sz z) n (t n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
      (![σ, true], a, c, b)
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    have hN : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hK0
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (k + 2) := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
    rw [pow_one]
    linarith [inv_le_one_of_one_le₀ hW1]
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
    calc S * CM * ((C * s ^ 2 + (𝔡⁻¹ ^ 2 + 1) * s ^ 2) * s ^ 3) =
          (S * CM) * ((C + (𝔡⁻¹ ^ 2 + 1)) * s ^ 5 + 0 * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 hSC hω (by positivity) le_rfl le_rfl le_rfl
        (by nlinarith [mul_nonneg hSC hC.le, mul_nonneg hSC hc1.le])
  · filter_upwards [hev] with n hn
    obtain ⟨hf, h1t, h4, hηN, hB2, ht1n, ⟨hlam0, hlam⟩, hK0⟩ := hn
    obtain ⟨s, hs0, hs2, hBs', h32, h52⟩ := BAExp14b2_s (STBctl_pos sz n ht1n) hB2
    have hω : 1 ≤ (1 - t n)⁻¹ := by rw [one_le_inv₀ (by linarith)]; linarith [ht0 n]
    rw [h32, h52, hBs']
    have hSC : 0 ≤ S * CM := mul_nonneg (by linarith) hCM
    calc S * CM * (s ^ 2 * (s ^ 3 + (𝔡⁻¹ ^ 2 + 1) * s ^ 2 * s ^ 2)) =
          (S * CM) * (1 * s ^ 5 + (𝔡⁻¹ ^ 2 + 1) * s ^ 6 + 0 * s ^ 7 + 0 * s ^ 8) := by ring
      _ ≤ _ := BAExp14b2_polyK hs0 hs2 hSC hω zero_le_one hc1.le le_rfl le_rfl
        (by nlinarith [mul_nonneg hSC hC.le, mul_nonneg hSC hc1.le])

/-- The block columns of `κ_k` (`κ_0 = 1`, `κ_1 = ω - 1`): `Σ_{a₁} |κ_k(a₁, c)| ≤ S` (the kernel sums read in `Graph/BAExp14b2B.lean`). -/
theorem BAExp14b2_kap_col {n : ℕ} {t CM S : ℝ}
    (hr : BAReal (k + 2) (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n))
    (hf : BAExp14a_Facts sz z n t CM S) (kb : Bool) (c : Zd (k + 2) (sz.L n)) :
    ∑ a₁, ‖BAExp14b_kap sz z n t kb a₁ c‖ ≤ S := by
  cases kb
  · simp only [BAExp14b_kap, Bool.false_eq_true, ↓reduceIte, Matrix.one_apply]
    calc _ ≤ ∑ a₁ : Zd (k + 2) (sz.L n), (if a₁ = c then (1 : ℝ) else 0) :=
          Finset.sum_le_sum fun a₁ _ => by split_ifs <;> simp
      _ = 1 := by simp
      _ ≤ S := hf.hS
  · simpa [BAExp14b_kap] using BAExp14b2_om1_col hr hf c

/-- **The families `D1t, D2t, T2a, T2b`** (`j < 4`): for the first four families of `BAExp14bS2`, every charge and block pair,
`‖𝔼 F_j‖ ≺ (1 - t)⁻¹ 𝔟^{5/2}` over the carrier `baFMz sz z` and the law `BAExp14a_μ sz` (the law of the block Anderson model), from `STLocalEntrygL`, `LWAvgLawgL`, `STLKgL`,
`BATwistAvgLaw`, `BATwistLoopLaw` (`STLmaxgL`, `STDecaygL` are not read).  Private, since `LWAvgLawgL` is a hypothesis of it. -/
private theorem BAExp14b2_I1K (hk : 1 ≤ k) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (ht0 : ∀ n, 0 ≤ t n) (ht : ∀ n, t n ≤ BAflowT0 sz z n) (hE : STLocalEntrygL (baFMz sz z) (BAExp14a_μ sz) t)
    (hA : LWAvgLawgL (baFMz sz z) (BAExp14a_μ sz) t) (hK : STLKgL (baFMz sz z) (BAExp14a_μ sz) t)
    (hT1 : BATwistAvgLaw (baFMz sz z) (BAExp14a_μ sz) t) (hT2 : BATwistLoopLaw (baFMz sz z) (BAExp14a_μ sz) t)
    (j : Fin 8) (hj : (j : ℕ) < 4) :
    PrecL sz (BAExp14a_μ sz) (U := fun n => Bool × Zd (k + 2) (sz.L n) × Zd (k + 2) (sz.L n))
      (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω j p.1 p.2.1 p.2.2 ∂(BAExp14a_μ sz)‖)
      (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
  fin_cases j
  · exact BAExp14b2_D1t hk hκ hε h𝔡 hflow ht0 ht hE hA hK hT1
  · exact BAExp14b2_D2t hk hκ hε h𝔡 hflow ht0 ht hE hA hT1 hT2
  · exact BAExp14b2_T2a hk hκ hε h𝔡 hflow ht0 ht hE hA hT1 hT2
  · exact BAExp14b2_T2b hk hκ hε h𝔡 hflow ht0 ht hE hA hT1 hT2
  all_goals exact absurd hj (by decide)

end Fam

end Infra

/-! ## 8. The Ward sums and the kernel sums read in `Graph/BAExp14b2B.lean` -/

section Ward

variable {k : ℕ} {sz : Sizes (k + 2)} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- `Σ_a Σ_{α ∈ [a]} F α = Σ_α F α`. -/
theorem BAExp14b2_sum_blocks {β : Type*} [AddCommMonoid β] {n : ℕ} (F : Idx (k + 2) (sz.L n) (sz.W n) → β) :
    ∑ a : Zd (k + 2) (sz.L n), ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, F x = ∑ x, F x := by
  simp only [BAExp14b_sum_blk]
  exact (BAExp14b_sum_idx F).symm

/-- **The vertex bound** (as `lwExpTerm4_vertex` in `Graph/LWExpTerm4.lean`): `Σ_y |G_{xy}||G_{yz}| ≤ A/η` from the row and column Ward
identities and Cauchy-Schwarz. -/
theorem BAExp14b2_vertex {ι : Type*} [Fintype ι] (G : ι → ι → ℂ) {η A : ℝ} (hη : 0 < η)
    (hrow : ∀ x, η * ∑ y, ‖G x y‖ ^ 2 = (G x x).im) (hcol : ∀ x, η * ∑ y, ‖G y x‖ ^ 2 = (G x x).im)
    (hA : ∀ x, ‖G x x‖ ≤ A) (x z : ι) : ∑ y, ‖G x y‖ * ‖G y z‖ ≤ A * η⁻¹ := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hS1 : 0 ≤ ∑ y, ‖G x y‖ ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ y, ‖G y z‖ ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
  have hs1 : ∑ y, ‖G x y‖ ^ 2 ≤ A * η⁻¹ := by
    rw [le_mul_inv_iff₀ hη]
    nlinarith [hrow x, Complex.im_le_norm (G x x), hA x]
  have hs2 : ∑ y, ‖G y z‖ ^ 2 ≤ A * η⁻¹ := by
    rw [le_mul_inv_iff₀ hη]
    nlinarith [hcol z, Complex.im_le_norm (G z z), hA z]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖G x y‖) (fun y => ‖G y z‖)
  have h3 : (∑ y, ‖G x y‖ * ‖G y z‖) ^ 2 ≤ (A * η⁻¹) ^ 2 := by
    refine hcs.trans ?_
    rw [sq]
    exact mul_le_mul hs1 hs2 hS2 (by positivity)
  exact (sq_le_sq₀ (Finset.sum_nonneg fun y _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)).1 h3

/-- `‖𝓛^{(2)}_{(σ,-σ),(c,b)}‖ = W^{-2d} Σ_{x ∈ [b]} Σ_{y ∈ [c]} |G(σ)_{xy}|²` (`G(-σ)_{yx} = \overline{G(σ)_{xy}}`). -/
theorem BAExp14b2_L2_norm {n : ℕ} (t : ℝ) (ω : sz.SeqΩ) (σ : Bool) (b c : Zd (k + 2) (sz.L n)) :
    ‖(baFMz sz z).L n t ![σ, !σ] ![c, b] ω‖ = ((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 *
      ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) c,
        ‖twChg ((baFMz sz z).G n t ω) σ x y‖ ^ 2 := by
  have hpt : ∀ x y : Idx (k + 2) (sz.L n) (sz.W n), twChg ((baFMz sz z).G n t ω) σ x y * twChg ((baFMz sz z).G n t ω) (!σ) y x =
      ((‖twChg ((baFMz sz z).G n t ω) σ x y‖ ^ 2 : ℝ) : ℂ) := by
    intro x y
    cases σ
    · simp only [twChg, Bool.false_eq_true, ↓reduceIte, Bool.not_false, RCLike.norm_conj]
      rw [mul_comm, Complex.mul_conj', Complex.ofReal_pow]
    · simp only [twChg, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
      rw [Complex.mul_conj', Complex.ofReal_pow]
  have h : (baFMz sz z).L n t ![σ, !σ] ![c, b] ω = (((((((sz.W n : ℕ) : ℝ) ^ (k + 2))⁻¹) ^ 2 *
      ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) c,
        ‖twChg ((baFMz sz z).G n t ω) σ x y‖ ^ 2 : ℝ)) : ℂ) := by
    rw [BAExp14b_L2_eq]
    simp only [hpt]
    push_cast
    rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  positivity

/-- **The `𝓛^{(3)}` Ward sum** (as `lwExpTerm4_L3` in `Graph/LWExpTerm4.lean`): `W^d Σ_a |𝓛^{(3)}_{(+,+,σ),(a,b,c)}| ≤ η⁻¹ A Q^{1/2}`
for `A ≥ max_x |G_{xx}|` and `Q ≥ |𝓛^{(2)}_{(σ,-σ),(c,b)}|`; pathwise, at the carrier. -/
theorem BAExp14b2_L3_ward (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (σ : Bool) (b c : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) {A Q : ℝ} (hA : ∀ x, ‖(baFMz sz z).G n t ω x x‖ ≤ A)
    (hQ : ‖(baFMz sz z).L n t ![σ, !σ] ![c, b] ω‖ ≤ Q) :
    (((sz.W n : ℕ) : ℝ) ^ (k + 2)) * ∑ a, ‖(baFMz sz z).L n t ![true, true, σ] ![a, b, c] ω‖ ≤
      ((baFMz sz z).eta n t)⁻¹ * A * Real.sqrt Q := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  obtain ⟨hrow, hcol⟩ : (∀ x, (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω x y‖ ^ 2 = ((baFMz sz z).G n t ω x x).im) ∧
      (∀ x, (baFMz sz z).eta n t * ∑ y, ‖(baFMz sz z).G n t ω y x‖ ^ 2 = ((baFMz sz z).G n t ω x x).im) :=
    ⟨fun x => (BAExp14a_G_ward hκ hflow n ht0 ht ω x).1, fun x => (BAExp14a_G_ward hκ hflow n ht0 ht ω x).2⟩
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set Wd : ℝ := ((sz.W n : ℕ) : ℝ) ^ (k + 2) with hWd
  set Gm := (baFMz sz z).G n t ω with hGm
  set Gs := twChg Gm σ with hGs
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hv := fun x z => BAExp14b2_vertex Gm hη hrow hcol hA x z
  -- the pointwise bound of one 3-loop
  have hpt : ∀ a : Zd (k + 2) (sz.L n), ‖(baFMz sz z).L n t ![true, true, σ] ![a, b, c] ω‖ ≤
      (Wd⁻¹) ^ 3 * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ α ∈ Iblk (k + 2) (sz.L n) (sz.W n) a,
        ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gm x α‖ * ‖Gm α y‖ * ‖Gs y x‖ := by
    intro a
    rw [BAExp14b_L3_eq, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ =>
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)))
    simp only [norm_mul]
    rw [BAExp14b2_twChg_true]
  have hsum : Wd * ∑ a, ‖(baFMz sz z).L n t ![true, true, σ] ![a, b, c] ω‖ ≤
      Wd * ((Wd⁻¹) ^ 3 * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b,
        ‖Gs y x‖ * (A * ((baFMz sz z).eta n t)⁻¹)) := by
    refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun a _ => hpt a).trans ?_) hW.le
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [BAExp14b2_sum_blocks (F := fun α => ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gm x α‖ * ‖Gm α y‖ * ‖Gs y x‖)]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun y _ => ?_
    calc ∑ α, ‖Gm x α‖ * ‖Gm α y‖ * ‖Gs y x‖ = (∑ α, ‖Gm x α‖ * ‖Gm α y‖) * ‖Gs y x‖ := (Finset.sum_mul _ _ _).symm
      _ ≤ (A * ((baFMz sz z).eta n t)⁻¹) * ‖Gs y x‖ := mul_le_mul_of_nonneg_right (hv x y) (norm_nonneg _)
      _ = ‖Gs y x‖ * (A * ((baFMz sz z).eta n t)⁻¹) := mul_comm _ _
  -- the sum of |G^σ| against the 2-loop
  set T : ℝ := ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gs y x‖ with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => norm_nonneg _
  have hcs : T ^ 2 ≤ Wd * Wd * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gs y x‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Iblk (k + 2) (sz.L n) (sz.W n) c ×ˢ Iblk (k + 2) (sz.L n) (sz.W n) b)
      (f := fun p => ‖Gs p.2 p.1‖)
    rw [Finset.sum_product, Finset.sum_product, Finset.card_product, card_Iblk, card_Iblk] at h
    simpa [hT, Wd] using h
  have hL2 := BAExp14b2_L2_norm (z := z) (n := n) t ω σ b c
  have hN2 : ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ‖Gs x y‖ ^ 2 =
      ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gs y x‖ ^ 2 := Finset.sum_comm
  rw [hN2] at hL2
  have hsq : ((Wd⁻¹) ^ 2 * T) ^ 2 ≤ Q := by
    calc ((Wd⁻¹) ^ 2 * T) ^ 2 = (Wd⁻¹) ^ 4 * T ^ 2 := by ring
      _ ≤ (Wd⁻¹) ^ 4 * (Wd * Wd * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gs y x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (Wd⁻¹) ^ 2 * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b, ‖Gs y x‖ ^ 2 := by
          field_simp
      _ = ‖(baFMz sz z).L n t ![σ, !σ] ![c, b] ω‖ := hL2.symm
      _ ≤ Q := hQ
  have hTs : (Wd⁻¹) ^ 2 * T ≤ Real.sqrt Q := Real.le_sqrt_of_sq_le hsq
  calc Wd * ∑ a, ‖(baFMz sz z).L n t ![true, true, σ] ![a, b, c] ω‖ ≤ _ := hsum
    _ = (Wd⁻¹) ^ 2 * T * (A * ((baFMz sz z).eta n t)⁻¹) := by
        have e : ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c, ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) b,
            ‖Gs y x‖ * (A * ((baFMz sz z).eta n t)⁻¹) = T * (A * ((baFMz sz z).eta n t)⁻¹) := by
          rw [hT]; simp only [← Finset.sum_mul]
        rw [e]
        field_simp
    _ ≤ Real.sqrt Q * (A * ((baFMz sz z).eta n t)⁻¹) := mul_le_mul_of_nonneg_right hTs (by positivity)
    _ = ((baFMz sz z).eta n t)⁻¹ * A * Real.sqrt Q := by ring

/-- **The twisted fold-plus-Ward sum** (`twFold_holds`, the fine Ward identities): for `A ≥ max_x |G_{xx}|` and a kernel
`MB` with `ℓ¹` rows and columns `≤ C_M`, `Σ_{c₁,c₂} |MB_{c₁c₂}| |L̃(G^σ, G; a, c₁, c₂)| ≤ C_M A (W^d η)⁻¹` (`|L̃|² ≤ twSq twSq`, AM-GM,
Schur against `MB`, and `Σ_{c₂} twSq(G^σ, c₂, a) = W^{-2d} Σ_{x ∈ [a]} Σ_y |G^σ_{yx}|² = W^{-2d} Σ_{x ∈ [a]} Im G_{xx}/η`). -/
theorem BAExp14b2_fold_ward (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    (σ : Bool) (a : Zd (k + 2) (sz.L n)) (ω : sz.SeqΩ) {A CM : ℝ} (hA : ∀ x, ‖(baFMz sz z).G n t ω x x‖ ≤ A)
    (MB : Zd (k + 2) (sz.L n) → Zd (k + 2) (sz.L n) → ℂ) (hMr : ∀ c, ∑ b, ‖MB c b‖ ≤ CM) (hMc : ∀ b, ∑ c, ‖MB c b‖ ≤ CM) :
    ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * ‖twLoopX n (twChg ((baFMz sz z).G n t ω) σ) ((baFMz sz z).G n t ω) a c₁ c₂‖ ≤
      CM * A * ((((sz.W n : ℕ) : ℝ) ^ (k + 2)) * (baFMz sz z).eta n t)⁻¹ := by
  have hη := BAExp14a_eta_pos hκ hflow n ht0 ht
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (k + 2) := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  set Wd : ℝ := ((sz.W n : ℕ) : ℝ) ^ (k + 2) with hWd
  set Gm := (baFMz sz z).G n t ω with hGm
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hMr 0)
  have hw := fun x => BAExp14a_G_ward hκ hflow n ht0 ht ω x
  -- the Ward sums
  have hrow : ∀ x, ∑ y, ‖Gm x y‖ ^ 2 ≤ A * ((baFMz sz z).eta n t)⁻¹ := fun x => by
    rw [le_mul_inv_iff₀ hη]
    nlinarith [(hw x).1, Complex.im_le_norm (Gm x x), hA x]
  have hcol : ∀ x, ∑ y, ‖Gm y x‖ ^ 2 ≤ A * ((baFMz sz z).eta n t)⁻¹ := fun x => by
    rw [le_mul_inv_iff₀ hη]
    nlinarith [(hw x).2, Complex.im_le_norm (Gm x x), hA x]
  have hchg : ∀ x, ∑ y, ‖twChg Gm σ y x‖ ^ 2 ≤ A * ((baFMz sz z).eta n t)⁻¹ := fun x => by
    cases σ
    · simpa [twChg] using hrow x
    · simpa [twChg] using hcol x
  have hblk : ∀ (c : Zd (k + 2) (sz.L n)), twBlk (sz := sz) n c = Iblk (k + 2) (sz.L n) (sz.W n) c := fun c => rfl
  -- `Σ_{c₂} twSq(G^σ, c₂, a)` and `Σ_{c₁} twSq(G, a, c₁)`
  have hP : ∑ c₂, twSq n (twChg Gm σ) c₂ a ≤ A * (Wd * (baFMz sz z).eta n t)⁻¹ := by
    unfold twSq
    simp only [hblk]
    rw [← Finset.mul_sum, BAExp14b2_sum_blocks (F := fun y => ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, ‖twChg Gm σ y x‖ ^ 2)]
    rw [Finset.sum_comm]
    calc (((Wd)⁻¹) ^ 2) * ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, ∑ y, ‖twChg Gm σ y x‖ ^ 2
        ≤ (((Wd)⁻¹) ^ 2) * ∑ _x ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, A * ((baFMz sz z).eta n t)⁻¹ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hchg x) (by positivity)
      _ = A * (Wd * (baFMz sz z).eta n t)⁻¹ := by
          rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; rw [hWd]; field_simp
  have hQ : ∑ c₁, twSq n Gm a c₁ ≤ A * (Wd * (baFMz sz z).eta n t)⁻¹ := by
    unfold twSq
    simp only [hblk]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have e : ∀ y, ∑ c₁, ∑ x ∈ Iblk (k + 2) (sz.L n) (sz.W n) c₁, ‖Gm y x‖ ^ 2 = ∑ x, ‖Gm y x‖ ^ 2 := fun y =>
      BAExp14b2_sum_blocks (F := fun x => ‖Gm y x‖ ^ 2)
    simp only [e]
    calc (((Wd)⁻¹) ^ 2) * ∑ y ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, ∑ x, ‖Gm y x‖ ^ 2
        ≤ (((Wd)⁻¹) ^ 2) * ∑ _y ∈ Iblk (k + 2) (sz.L n) (sz.W n) a, A * ((baFMz sz z).eta n t)⁻¹ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hrow y) (by positivity)
      _ = A * (Wd * (baFMz sz z).eta n t)⁻¹ := by
          rw [Finset.sum_const, card_Iblk, nsmul_eq_mul]; push_cast; rw [hWd]; field_simp
  have hP0 : ∀ c₂, 0 ≤ twSq n (twChg Gm σ) c₂ a := fun c₂ => by unfold twSq; positivity
  have hQ0 : ∀ c₁, 0 ≤ twSq n Gm a c₁ := fun c₁ => by unfold twSq; positivity
  have hbd : ∀ c₁ c₂, ‖twLoopX n (twChg Gm σ) Gm a c₁ c₂‖ ≤ (twSq n (twChg Gm σ) c₂ a + twSq n Gm a c₁) / 2 := by
    intro c₁ c₂
    have h := twFold_holds sz n (twChg Gm σ) Gm a c₁ c₂
    by_contra hcon
    push Not at hcon
    nlinarith [sq_nonneg (twSq n (twChg Gm σ) c₂ a - twSq n Gm a c₁), hP0 c₂, hQ0 c₁, norm_nonneg (twLoopX n (twChg Gm σ) Gm a c₁ c₂)]
  have h1 : ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * twSq n (twChg Gm σ) c₂ a ≤ CM * ∑ c₂, twSq n (twChg Gm σ) c₂ a := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum fun c₂ _ => ?_
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hMc c₂) (hP0 c₂))
  have h2 : ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * twSq n Gm a c₁ ≤ CM * ∑ c₁, twSq n Gm a c₁ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c₁ _ => ?_
    rw [← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hMr c₁) (hQ0 c₁))
  calc ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * ‖twLoopX n (twChg Gm σ) Gm a c₁ c₂‖
      ≤ ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * ((twSq n (twChg Gm σ) c₂ a + twSq n Gm a c₁) / 2) :=
        Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => mul_le_mul_of_nonneg_left (hbd c₁ c₂) (norm_nonneg _)
    _ = (∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * twSq n (twChg Gm σ) c₂ a + ∑ c₁, ∑ c₂, ‖MB c₁ c₂‖ * twSq n Gm a c₁) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        exact Finset.sum_congr rfl fun c₂ _ => by ring
    _ ≤ (CM * (A * (Wd * (baFMz sz z).eta n t)⁻¹) + CM * (A * (Wd * (baFMz sz z).eta n t)⁻¹)) / 2 := by
        gcongr
        · exact h1.trans (mul_le_mul_of_nonneg_left hP hCM0)
        · exact h2.trans (mul_le_mul_of_nonneg_left hQ hCM0)
    _ = CM * A * (Wd * (baFMz sz z).eta n t)⁻¹ := by ring

/-- **Kernel sums** (as `lwExpTerm4_wsum3K` in `Graph/LWExpTerm4.lean`): `Σ_{a₁,c₁,c₂} |κ_{a₁c₁}| |MB_{c₁c₂}| h(c₂) ≤ S C_M Σ_{c₂} h(c₂)`
for `h ≥ 0`, column sums of `κ` (`κ_k`, `BAExp14b2_kap_col`) `≤ S` and of `MB` `≤ C_M`. -/
theorem BAExp14b2_wsum_c2 {ι : Type*} [Fintype ι] [Nonempty ι] (κm MB : ι → ι → ℂ) {S CM : ℝ} (hκ : ∀ c, ∑ a, ‖κm a c‖ ≤ S)
    (hMc : ∀ b, ∑ c, ‖MB c b‖ ≤ CM) (h : ι → ℝ) (h0 : ∀ c, 0 ≤ h c) :
    ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₂ ≤ S * CM * ∑ c₂, h c₂ := by
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hκ (Classical.arbitrary ι))
  calc ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₂
      = ∑ c₁, ∑ a₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₂ := Finset.sum_comm
    _ = ∑ c₁, ∑ c₂, ∑ a₁, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₂ := Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm
    _ = ∑ c₂, ∑ c₁, ∑ a₁, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₂ := Finset.sum_comm
    _ = ∑ c₂, ∑ c₁, (∑ a₁, ‖κm a₁ c₁‖) * ‖MB c₁ c₂‖ * h c₂ := by simp only [Finset.sum_mul]
    _ ≤ ∑ c₂, S * CM * h c₂ := by
        refine Finset.sum_le_sum fun c₂ _ => ?_
        calc ∑ c₁, (∑ a₁, ‖κm a₁ c₁‖) * ‖MB c₁ c₂‖ * h c₂ ≤ ∑ c₁, S * ‖MB c₁ c₂‖ * h c₂ :=
              Finset.sum_le_sum fun c₁ _ => mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hκ c₁) (norm_nonneg _)) (h0 c₂)
          _ = S * (∑ c₁, ‖MB c₁ c₂‖) * h c₂ := by rw [Finset.mul_sum, Finset.sum_mul]
          _ ≤ S * CM * h c₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMc c₂) hS0) (h0 c₂)
    _ = S * CM * ∑ c₂, h c₂ := (Finset.mul_sum _ _ _).symm

/-- The same with the weight at `c₁` (rows of `MB` `≤ C_M`): `Σ_{a₁,c₁,c₂} |κ_{a₁c₁}| |MB_{c₁c₂}| h(c₁) ≤ S C_M Σ_{c₁} h(c₁)`. -/
theorem BAExp14b2_wsum_c1 {ι : Type*} [Fintype ι] [Nonempty ι] (κm MB : ι → ι → ℂ) {S CM : ℝ} (hκ : ∀ c, ∑ a, ‖κm a c‖ ≤ S)
    (hMr : ∀ b, ∑ c, ‖MB b c‖ ≤ CM) (h : ι → ℝ) (h0 : ∀ c, 0 ≤ h c) :
    ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₁ ≤ S * CM * ∑ c₁, h c₁ := by
  have hS0 : 0 ≤ S := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hκ (Classical.arbitrary ι))
  have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hMr (Classical.arbitrary ι))
  calc ∑ a₁, ∑ c₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₁
      = ∑ c₁, ∑ a₁, ∑ c₂, ‖κm a₁ c₁‖ * ‖MB c₁ c₂‖ * h c₁ := Finset.sum_comm
    _ = ∑ c₁, (∑ a₁, ‖κm a₁ c₁‖) * (∑ c₂, ‖MB c₁ c₂‖) * h c₁ := by
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_mul]
    _ ≤ ∑ c₁, S * CM * h c₁ := by
        refine Finset.sum_le_sum fun c₁ _ => mul_le_mul_of_nonneg_right ?_ (h0 c₁)
        exact mul_le_mul (hκ c₁) (hMr c₁) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hS0
    _ = S * CM * ∑ c₁, h c₁ := (Finset.mul_sum _ _ _).symm

end Ward


end RBM.BA

end
