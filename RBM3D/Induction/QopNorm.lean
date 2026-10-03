/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QopAlgebra
import RBM3D.Evolution.Pins

/-!
# S3-05 (ticket T2059): `lem_+Q`, the norm bound on `𝒬_t` and its decay clause

Paper: `paper/tex/3_5_Loop_Hierarchy.tex:1284-1289` (`(normQA)`), after `Def:QtPt` (`3_5:1204`).

* `stQopNorm_holds`: the merged pin `STQopNorm` (`Step34Pins.lean:528`), with
  `C_n = C + 2 d m + K m` (it depends on `(d, m, K, C)` only, not on `Λ, c, ε, D, L, g, W, t`).
  Route of RBM2D `Induction/QopBounds.lean:525` (`qopNorm`, commit `c9a24cf`): `𝒬_t 𝒜 = 𝒜 - (𝒫𝒜) ϑ_t`;
  the near part of `𝒫𝒜` (`|a_i - a₁| < W^ε ℓ_t`) has at most `((2 W^ε ℓ_t + 2)^d)^m` terms, the sup bound of `ϑ`
  gives `(ℓ_t^d)^{-m}`, so `W^{2 d m ε}`; the far part has `≤ (L^d)^m ≤ W^{K m}` terms of size `W^{-D}`;
  `4 ≤ W^ε` absorbs the mollifier constant `C`.
* `stQop_sub_fastDecay`: the decay clause (RBM2D `qopDecay`, `QopBounds.lean:622`): if `‖𝒜‖_∞ ≤ W^{C₀}` then
  `𝒜 - 𝒬_t 𝒜 = (𝒫𝒜) ϑ_t` is `(t, ε', D')`-decaying for `W ≥ W₀(d, m, K, C, c, C₀, ε', D')`, `L^d ≤ W^K`.
  The threshold depends on `K` (and the hypothesis `L^d ≤ W^K` is needed) and not on `Λ`: paper-delta
  candidate `T2059a`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Gauss.Sizes

open RBM Filter

/-! ## 1. Counting -/

/-- The cyclic ball: `#{z : ZMod L | zdist L z < R} ≤ 2R + 2`. -/
private theorem qn_card_zball (L : ℕ) [NeZero L] {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card : ℝ) ≤ 2 * R + 2 := by
  set n := ⌈R⌉₊ with hn
  have hsub : (Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R) ⊆
      (Finset.range n).image (fun k : ℕ => (k : ZMod L)) ∪
        (Finset.range n).image (fun k : ℕ => -(k : ZMod L)) := by
    intro z hz
    have hz' : (zdist L z : ℝ) < R := (Finset.mem_filter.1 hz).2
    have hv : z.val ≤ L := (ZMod.val_lt z).le
    simp only [zdist] at hz'
    rcases le_total z.val (L - z.val) with h | h
    · rw [min_eq_left h] at hz'
      have : z.val < n := Nat.lt_ceil.2 hz'
      exact Finset.mem_union_left _
        (Finset.mem_image.2 ⟨z.val, Finset.mem_range.2 this, ZMod.natCast_zmod_val z⟩)
    · rw [min_eq_right h] at hz'
      have : L - z.val < n := Nat.lt_ceil.2 hz'
      refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨L - z.val, Finset.mem_range.2 this, ?_⟩)
      rw [Nat.cast_sub hv, ZMod.natCast_self, ZMod.natCast_zmod_val]
      simp
  have hcard : (Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card ≤ n + n := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ n + n := by
        gcongr
        · exact Finset.card_image_le.trans (by simp)
        · exact Finset.card_image_le.trans (by simp)
  have hnR : (n : ℝ) < R + 1 := Nat.ceil_lt_add_one hR
  have : ((Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R).card : ℝ) ≤ (n : ℝ) + n := by
    exact_mod_cast hcard
  linarith

/-- The `ℓ¹` ball of radius `R` about `c` in `Z_L^d` has at most `(2R + 2)^d` points. -/
private theorem qn_card_ball (d L : ℕ) [NeZero L] (c : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun x : Zd d L => (zdistD d L (x - c) : ℝ) < R).card : ℝ) ≤ (2 * R + 2) ^ d := by
  set Z := Finset.univ.filter fun z : ZMod L => (zdist L z : ℝ) < R with hZ
  have hsub : (Finset.univ.filter fun x : Zd d L => (zdistD d L (x - c) : ℝ) < R) ⊆
      Fintype.piFinset (fun j : Fin d => Z.image (fun z => z + c j)) := by
    intro x hx
    have hx' : (zdistD d L (x - c) : ℝ) < R := (Finset.mem_filter.1 hx).2
    rw [Fintype.mem_piFinset]
    intro j
    refine Finset.mem_image.2 ⟨x j - c j, ?_, by ring⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, lt_of_le_of_lt ?_ hx'⟩
    have : zdist L (x j - c j) ≤ zdistD d L (x - c) :=
      Finset.single_le_sum (f := fun i => zdist L ((x - c) i)) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact_mod_cast this
  have h1 := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h1
  have h2 : (((Finset.univ.filter fun x : Zd d L => (zdistD d L (x - c) : ℝ) < R).card : ℕ) : ℝ) ≤
      ∏ j : Fin d, ((Z.image (fun z => z + c j)).card : ℝ) := by
    exact_mod_cast h1
  refine h2.trans ?_
  calc ∏ j : Fin d, ((Z.image (fun z => z + c j)).card : ℝ) ≤ ∏ _j : Fin d, (2 * R + 2) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity)
          (fun j _ => by
            have := (Nat.cast_le (α := ℝ)).2 (Finset.card_image_le (s := Z) (f := fun z => z + c j))
            exact this.trans (qn_card_zball L hR))
    _ = (2 * R + 2) ^ d := by simp

/-- The tensors with first index `a₁` and the other indices in `B` number `|B|^m`. -/
private theorem qn_card_pi (d L m : ℕ) [NeZero L] (a₁ : Zd d L) (B : Finset (Zd d L)) :
    (Fintype.piFinset (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L)) else B)).card
      = B.card ^ m := by
  rw [Fintype.card_piFinset, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero]

/-- **`‖𝒫𝒜‖` split into the near and the far part.**  If `|𝒜_b| ≤ F` whenever `b₁ = a₁` and some `|b_i - b₁| ≥ R`,
then `|(𝒫𝒜)_{a₁}| ≤ ((2R+2)^d)^m ‖𝒜‖ + (L^d)^m F`. -/
private theorem qn_Psum_le {d L m : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L)
    {R F : ℝ} (hR : 0 ≤ R) (hF0 : 0 ≤ F)
    (hF : ∀ b : Fin (m + 1) → Zd d L, b 0 = a₁ → (∃ i, R ≤ (zdistD d L (b i - b 0) : ℝ)) → ‖A b‖ ≤ F) :
    ‖STPsum (d := d) A a₁‖ ≤ ((2 * R + 2) ^ d) ^ m * ‖A‖ + ((L : ℝ) ^ d) ^ m * F := by
  classical
  unfold STPsum
  set fib := Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁) with hfib
  set P : (Fin (m + 1) → Zd d L) → Prop := fun b => ∀ i, (zdistD d L (b i - b 0) : ℝ) < R with hP
  have h1 : ‖∑ a ∈ fib, A a‖ ≤ ∑ a ∈ fib, ‖A a‖ := norm_sum_le _ _
  have h1' := Finset.sum_filter_add_sum_filter_not fib P (fun a => ‖A a‖)
  -- near part
  have hnear : ∑ a ∈ fib.filter P, ‖A a‖ ≤ ((2 * R + 2) ^ d) ^ m * ‖A‖ := by
    have hsub : fib.filter P ⊆ Fintype.piFinset
        (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L))
          else Finset.univ.filter fun x : Zd d L => (zdistD d L (x - a₁) : ℝ) < R) := by
      intro b hb
      rw [Finset.mem_filter, hfib, Finset.mem_filter] at hb
      obtain ⟨⟨_, hb0⟩, hbP⟩ := hb
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = 0
      · simp [hi, hb0]
      · simp only [hi, ite_false, Finset.mem_filter, Finset.mem_univ, true_and]
        have := hbP i
        rwa [hb0] at this
    have hcard : ((fib.filter P).card : ℝ) ≤ ((2 * R + 2) ^ d) ^ m := by
      have h2 := Finset.card_le_card hsub
      rw [qn_card_pi] at h2
      have h3 : ((fib.filter P).card : ℝ) ≤
          (((Finset.univ.filter fun x : Zd d L => (zdistD d L (x - a₁) : ℝ) < R).card : ℕ) : ℝ) ^ m := by
        exact_mod_cast h2
      exact h3.trans (pow_le_pow_left₀ (by positivity) (qn_card_ball d L a₁ hR) m)
    calc ∑ a ∈ fib.filter P, ‖A a‖ ≤ ∑ _a ∈ fib.filter P, ‖A‖ :=
          Finset.sum_le_sum fun a _ => norm_le_pi_norm A a
      _ = ((fib.filter P).card : ℝ) * ‖A‖ := by simp
      _ ≤ _ := by gcongr
  -- far part
  have hfar : ∑ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ ((L : ℝ) ^ d) ^ m * F := by
    have hbd : ∀ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ F := by
      intro b hb
      rw [Finset.mem_filter, hfib, Finset.mem_filter] at hb
      obtain ⟨⟨_, hb0⟩, hbP⟩ := hb
      refine hF b hb0 ?_
      simp only [hP, not_forall, not_lt] at hbP
      exact hbP
    have hsub : fib ⊆ Fintype.piFinset
        (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L)) else Finset.univ) := by
      intro b hb
      rw [hfib, Finset.mem_filter] at hb
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i = 0
      · simp [hi, hb.2]
      · simp [hi]
    have hcard : ((fib.filter (fun b => ¬ P b)).card : ℝ) ≤ ((L : ℝ) ^ d) ^ m := by
      have h2 := (Finset.card_le_card (Finset.filter_subset (fun b => ¬ P b) fib)).trans
        (Finset.card_le_card hsub)
      rw [qn_card_pi, Finset.card_univ, card_Zd] at h2
      exact_mod_cast h2
    calc ∑ a ∈ fib.filter (fun b => ¬ P b), ‖A a‖ ≤ ∑ _a ∈ fib.filter (fun b => ¬ P b), F :=
          Finset.sum_le_sum hbd
      _ = ((fib.filter (fun b => ¬ P b)).card : ℝ) * F := by simp
      _ ≤ _ := by gcongr
  linarith

/-- `|(𝒫𝒜)_{a₁}| ≤ (L^d)^m ‖𝒜‖`. -/
private theorem qn_Psum_le_card {d L m : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) :
    ‖STPsum (d := d) A a₁‖ ≤ ((L : ℝ) ^ d) ^ m * ‖A‖ := by
  classical
  unfold STPsum
  set fib := Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁) with hfib
  have hsub : fib ⊆ Fintype.piFinset
      (fun i : Fin (m + 1) => if i = 0 then ({a₁} : Finset (Zd d L)) else Finset.univ) := by
    intro b hb
    rw [hfib, Finset.mem_filter] at hb
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i = 0
    · simp [hi, hb.2]
    · simp [hi]
  have hcard : (fib.card : ℝ) ≤ ((L : ℝ) ^ d) ^ m := by
    have h2 := Finset.card_le_card hsub
    rw [qn_card_pi, Finset.card_univ, card_Zd] at h2
    exact_mod_cast h2
  calc ‖∑ a ∈ fib, A a‖ ≤ ∑ a ∈ fib, ‖A a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ fib, ‖A‖ := Finset.sum_le_sum fun a _ => norm_le_pi_norm A a
    _ = (fib.card : ℝ) * ‖A‖ := by simp
    _ ≤ _ := by gcongr

/-! ## 2. Real inequalities -/

/-- `1 + x ≤ X^x` for `X ≥ 4`, `x ≥ 0`. -/
private theorem qn_one_add_le {X x : ℝ} (hX : 4 ≤ X) (hx : 0 ≤ x) : 1 + x ≤ X ^ x := by
  have hX0 : 0 < X := by linarith
  have hln : 1 ≤ Real.log X := by
    have h1 : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9
      linarith
    have h2 : Real.exp 1 ≤ X := h1.trans hX
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos 1) h2
  rw [Real.rpow_def_of_pos hX0]
  have := Real.add_one_le_exp (Real.log X * x)
  nlinarith

/-- The arithmetic of the exponents, `C_n = C + 2dm + Km`. -/
private theorem qn_arith {W ε C K D : ℝ} (d m : ℕ) (hW : 1 < W) (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 < C)
    (hK : 0 < K) (h4 : 4 ≤ W ^ ε) :
    1 + C * (3 * W ^ ε) ^ (d * m) ≤ W ^ ((C + 2 * ((d : ℝ) * m) + K * m) * ε) ∧
    C * W ^ (K * m) * W ^ (-D) ≤ W ^ (-D + (C + 2 * ((d : ℝ) * m) + K * m)) := by
  have hW0 : 0 < W := by linarith
  set X := W ^ ε with hX
  have hX0 : 0 < X := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdm0 : (0 : ℝ) ≤ (d : ℝ) * m := by positivity
  have hX1 : 1 ≤ X := by linarith
  -- `(3X)^{dm} ≤ X^{2dm}`
  have h3X : (3 * X) ^ (d * m) ≤ X ^ (2 * (d * m) : ℕ) := by
    have : 3 * X ≤ X ^ 2 := by nlinarith
    calc (3 * X) ^ (d * m) ≤ (X ^ 2) ^ (d * m) := pow_le_pow_left₀ (by positivity) this _
      _ = X ^ (2 * (d * m) : ℕ) := by rw [← pow_mul]
  have hXn : X ^ (2 * (d * m) : ℕ) = X ^ (2 * ((d : ℝ) * m)) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have hXC' : 1 + C ≤ X ^ C := qn_one_add_le h4 hC.le
  have hpow1 : 1 ≤ X ^ (2 * ((d : ℝ) * m)) := Real.one_le_rpow hX1 (by positivity)
  refine ⟨?_, ?_⟩
  · calc 1 + C * (3 * X) ^ (d * m) ≤ 1 + C * X ^ (2 * ((d : ℝ) * m)) := by
          rw [← hXn]; gcongr
      _ ≤ (1 + C) * X ^ (2 * ((d : ℝ) * m)) := by nlinarith
      _ ≤ X ^ C * X ^ (2 * ((d : ℝ) * m)) := by gcongr
      _ = W ^ ((C + 2 * ((d : ℝ) * m)) * ε) := by
          rw [← Real.rpow_add hX0, hX, ← Real.rpow_mul hW0.le]
          ring_nf
      _ ≤ W ^ ((C + 2 * ((d : ℝ) * m) + K * m) * ε) := by
          refine Real.rpow_le_rpow_of_exponent_le hW.le ?_
          have : 0 ≤ K * m * ε := by positivity
          nlinarith
  · have hCW : C ≤ W ^ C := by
      have h1 : X ^ C ≤ W ^ C := by
        rw [hX, ← Real.rpow_mul hW0.le]
        refine Real.rpow_le_rpow_of_exponent_le hW.le ?_
        nlinarith
      linarith
    calc C * W ^ (K * m) * W ^ (-D) ≤ W ^ C * W ^ (K * m) * W ^ (-D) := by gcongr
      _ = W ^ (-D + (C + K * m)) := by
          rw [← Real.rpow_add hW0, ← Real.rpow_add hW0]; ring_nf
      _ ≤ W ^ (-D + (C + 2 * ((d : ℝ) * m) + K * m)) := by
          refine Real.rpow_le_rpow_of_exponent_le hW.le ?_
          linarith

/-! ## 3. The norm bound `(normQA)` -/

/-- **`lem_+Q`, `(normQA)`** (`3_5:1284-1289`): the merged pin `STQopNorm` with
`C_n = C + 2 d m + K m`. -/
theorem stQopNorm_holds (d : ℕ) : STQopNorm d := by
  intro _ m Λ K C c _ hK hC hc
  refine ⟨C + 2 * ((d : ℝ) * m) + K * m, by positivity, ?_⟩
  intro L hL g hg _ W ε D hW hε hε1 _ h4 hLW
  have : NeZero L := ⟨by omega⟩
  intro ϑ hϑ t ht0 ht1 A hA
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hW0 : 0 < W := by linarith
  obtain ⟨hA1, hA2⟩ := qn_arith (D := D) d m hW hε hε1 hC hK h4
  set ℓ := ellT L g t with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  have hX0 : 0 < W ^ ε := by linarith
  have hRnn : 0 ≤ W ^ ε * ℓ := by positivity
  have hWD : 0 ≤ W ^ (-D) := (Real.rpow_pos_of_pos hW0 _).le
  have hnn : 0 ≤ W ^ ((C + 2 * ((d : ℝ) * m) + K * m) * ε) * ‖A‖ + W ^ (-D + (C + 2 * ((d : ℝ) * m) + K * m)) := by
    positivity
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_
  -- pointwise
  have hPs := qn_Psum_le (d := d) A (a 0) hRnn hWD (R := W ^ ε * ℓ) (F := W ^ (-D)) (by
    intro b _ hb
    obtain ⟨i, hi⟩ := hb
    exact hA b ⟨i, 0, hi⟩)
  have hθ := hϑ.2.1 t ht0 ht1 a
  have hexp : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ℓ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have h2 : 0 ≤ c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ℓ := by
      positivity
    have h3 : -c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ℓ
        = -(c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ℓ) := by ring
    rw [h3]; linarith
  have hθ' : ‖ϑ t a‖ ≤ C * ((ℓ ^ d)⁻¹) ^ m := by
    refine hθ.trans ?_
    calc _ ≤ C * ((ℓ ^ d)⁻¹) ^ m * 1 := by gcongr
      _ = _ := mul_one _
  have hθ0 : 0 ≤ C * ((ℓ ^ d)⁻¹) ^ m := by positivity
  have hinv : ((ℓ ^ d)⁻¹) ^ m ≤ 1 := by
    have : (ℓ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1)
    exact pow_le_one₀ (by positivity) this
  -- near count against `ℓ^{-dm}`
  have hnear : ((2 * (W ^ ε * ℓ) + 2) ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ m ≤ (3 * W ^ ε) ^ (d * m) := by
    have h1 : ((2 * (W ^ ε * ℓ) + 2) ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ m
        = (((2 * (W ^ ε * ℓ) + 2) / ℓ) ^ d) ^ m := by
      rw [div_pow, div_pow, div_eq_mul_inv, inv_pow]
    rw [h1, ← pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have h2 : (2 * (W ^ ε * ℓ) + 2) / ℓ ≤ 3 * W ^ ε := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    exact h2
  have hLd : ((L : ℝ) ^ d) ^ m ≤ W ^ (K * m) := by
    calc ((L : ℝ) ^ d) ^ m ≤ (W ^ K) ^ m := pow_le_pow_left₀ (by positivity) hLW m
      _ = W ^ (K * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  -- assemble
  have hQ : ‖STQop (d := d) ϑ t A a‖ ≤ ‖A a‖ + ‖STPsum (d := d) A (a 0)‖ * ‖ϑ t a‖ := by
    unfold STQop
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hAa : ‖A a‖ ≤ ‖A‖ := norm_le_pi_norm A a
  have hsum : ‖STPsum (d := d) A (a 0)‖ * ‖ϑ t a‖ ≤
      (C * (3 * W ^ ε) ^ (d * m)) * ‖A‖ + C * W ^ (K * m) * W ^ (-D) := by
    have hPn : 0 ≤ ‖STPsum (d := d) A (a 0)‖ := norm_nonneg _
    calc ‖STPsum (d := d) A (a 0)‖ * ‖ϑ t a‖
        ≤ (((2 * (W ^ ε * ℓ) + 2) ^ d) ^ m * ‖A‖ + ((L : ℝ) ^ d) ^ m * W ^ (-D)) * (C * ((ℓ ^ d)⁻¹) ^ m) :=
          mul_le_mul hPs hθ' (norm_nonneg _) (by positivity)
      _ = C * (((2 * (W ^ ε * ℓ) + 2) ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ m) * ‖A‖
            + C * (((L : ℝ) ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ m) * W ^ (-D) := by ring
      _ ≤ C * (3 * W ^ ε) ^ (d * m) * ‖A‖ + C * W ^ (K * m) * W ^ (-D) := by
          gcongr
          calc ((L : ℝ) ^ d) ^ m * ((ℓ ^ d)⁻¹) ^ m ≤ ((L : ℝ) ^ d) ^ m * 1 := by gcongr
            _ ≤ W ^ (K * m) := by rw [mul_one]; exact hLd
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  calc ‖STQop (d := d) ϑ t A a‖ ≤ ‖A‖ + ((C * (3 * W ^ ε) ^ (d * m)) * ‖A‖ + C * W ^ (K * m) * W ^ (-D)) := by
        linarith
    _ = (1 + C * (3 * W ^ ε) ^ (d * m)) * ‖A‖ + C * W ^ (K * m) * W ^ (-D) := by ring
    _ ≤ W ^ ((C + 2 * ((d : ℝ) * m) + K * m) * ε) * ‖A‖ + W ^ (-D + (C + 2 * ((d : ℝ) * m) + K * m)) := by
        gcongr

/-! ## 4. The decay clause -/

/-- Growth: `C W^p ≤ exp (c W^{ε'} / 2)` for large `W`. -/
private theorem qn_growth {C c ε' p : ℝ} (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    ∃ W₁ : ℝ, 1 < W₁ ∧ ∀ W : ℝ, W₁ ≤ W → C * W ^ p ≤ Real.exp (c * W ^ ε' / 2) := by
  set q := p / ε' with hq
  have hκ : 0 < (C * (2 / c) ^ q)⁻¹ := by positivity
  have hlo := (isLittleO_rpow_exp_atTop q).def hκ
  have hT : Tendsto (fun W : ℝ => c * W ^ ε' / 2) atTop atTop := by
    have := (tendsto_rpow_atTop hε').const_mul_atTop hc
    exact this.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  have hev := hT.eventually hlo
  obtain ⟨W₁, hW₁⟩ := Filter.eventually_atTop.1 (hev.and (Filter.eventually_gt_atTop (1 : ℝ)))
  refine ⟨max W₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro W hW
  have hW2 : 2 ≤ W := (le_max_right _ _).trans hW
  obtain ⟨h1, h2⟩ := hW₁ W ((le_max_left _ _).trans hW)
  have hW0 : 0 < W := by linarith
  set y := c * W ^ ε' / 2 with hy
  have hy0 : 0 < y := by positivity
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _), Real.norm_of_nonneg (Real.exp_pos y).le] at h1
  -- `W^p = (2/c)^q y^q`
  have hWp : W ^ p = (2 / c) ^ q * y ^ q := by
    have h3 : W ^ p = (W ^ ε') ^ q := by
      rw [← Real.rpow_mul hW0.le, hq]; field_simp
    have h4 : W ^ ε' = 2 / c * y := by rw [hy]; field_simp
    rw [h3, h4, Real.mul_rpow (by positivity) hy0.le]
  rw [hWp]
  have hy1 : y ^ q ≤ (C * (2 / c) ^ q)⁻¹ * Real.exp y := h1
  have hpos : 0 < C * (2 / c) ^ q := by positivity
  calc C * ((2 / c) ^ q * y ^ q) = (C * (2 / c) ^ q) * y ^ q := by ring
    _ ≤ (C * (2 / c) ^ q) * ((C * (2 / c) ^ q)⁻¹ * Real.exp y) := by gcongr
    _ = Real.exp y := by field_simp

/-- **The decay clause of `lem_+Q`** (`3_5:1284-1289`, ported role of RBM2D `qopDecay`): if `‖𝒜‖_∞ ≤ W^{C₀}` then
`𝒜 - 𝒬_t 𝒜 = (𝒫𝒜) ϑ_t` is `(t, ε', D')`-decaying (`EKFastDecay`) for every `ε', D'` (`ε' > 0`) once `W ≥ W₀`, where
`W₀` depends on `(d, m, K, C, c, C₀, ε', D')` (not on `Λ`, `L`, `g`, `t`); it needs `L^d ≤ W^K` (paper-delta
candidate `T2059a`). -/
theorem stQop_sub_fastDecay (d m : ℕ) (K C c C₀ ε' D' : ℝ) (hC : 0 < C) (hc : 0 < c) (hε' : 0 < ε') :
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ A : (Fin (m + 1) → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D' (A - STQop (d := d) ϑ t A) := by
  obtain ⟨W₁, hW₁, hW₁'⟩ := qn_growth (p := C₀ + K * m + D') hC hc hε'
  refine ⟨W₁, hW₁, ?_⟩
  intro L hL g hg W hW hLW
  have : NeZero L := ⟨by omega⟩
  intro ϑ hϑ t ht0 ht1 A hA a ha
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hW1 : 1 < W := lt_of_lt_of_le hW₁ hW
  have hW0 : 0 < W := by linarith
  set ℓ := ellT L g t with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_ellT hL1
  obtain ⟨i, j, hij⟩ := ha
  have hR : 0 < W ^ ε' * ℓ := by positivity
  -- the sum `S ≥ W^{ε'} ℓ / 2`
  set S := ∑ k ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a k - a 0) : ℝ) with hS
  have hSge : W ^ ε' * ℓ / 2 ≤ S := by
    have htri : (zdistD d L (a i - a j) : ℝ) ≤ (zdistD d L (a i - a 0) : ℝ) + (zdistD d L (a j - a 0) : ℝ) := by
      have : a i - a j = (a i - a 0) + -(a j - a 0) := by ring
      have h2 := zdistD_add_le d L (a i - a 0) (-(a j - a 0))
      rw [← this, zdistD_neg] at h2
      exact_mod_cast h2
    have hmem : ∀ k : Fin (m + 1), (zdistD d L (a k - a 0) : ℝ) ≤ S := by
      intro k
      by_cases hk : k = 0
      · subst hk
        simp only [sub_self, zdistD_zero, Nat.cast_zero]
        exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      · exact Finset.single_le_sum (f := fun k => (zdistD d L (a k - a 0) : ℝ))
          (fun _ _ => Nat.cast_nonneg _) (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)
    have hi' := hmem i
    have hj' := hmem j
    linarith
  have hexp : Real.exp (-c * S / ℓ) ≤ Real.exp (-(c * W ^ ε' / 2)) := by
    refine Real.exp_le_exp.2 ?_
    have : c * W ^ ε' / 2 ≤ c * S / ℓ := by
      rw [le_div_iff₀ (by linarith)]
      have := mul_le_mul_of_nonneg_left hSge hc.le
      nlinarith
    have h2 : -c * S / ℓ = -(c * S / ℓ) := by ring
    rw [h2]; linarith
  have hθ := hϑ.2.1 t ht0 ht1 a
  have hθ' : ‖ϑ t a‖ ≤ C * Real.exp (-(c * W ^ ε' / 2)) := by
    have hinv : ((ℓ ^ d)⁻¹) ^ m ≤ 1 := by
      have : (ℓ ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hℓ1)
      exact pow_le_one₀ (by positivity) this
    refine hθ.trans ?_
    calc C * ((ℓ ^ d)⁻¹) ^ m * Real.exp (-c * S / ℓ) ≤ C * 1 * Real.exp (-(c * W ^ ε' / 2)) := by
          gcongr
      _ = _ := by ring
  -- `𝒫𝒜` is bounded by `L^{dm} W^{C₀}`
  have hLd : ((L : ℝ) ^ d) ^ m ≤ W ^ (K * m) := by
    calc ((L : ℝ) ^ d) ^ m ≤ (W ^ K) ^ m := pow_le_pow_left₀ (by positivity) hLW m
      _ = W ^ (K * m) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hPs : ‖STPsum (d := d) A (a 0)‖ ≤ W ^ (C₀ + K * m) := by
    refine (qn_Psum_le_card A (a 0)).trans ?_
    rw [Real.rpow_add hW0, mul_comm]
    exact mul_le_mul hA hLd (by positivity) (by positivity)
  have hsub : (A - STQop (d := d) ϑ t A) a = STPsum (d := d) A (a 0) * ϑ t a := by
    simp [STQop]
  rw [hsub, norm_mul]
  set y := c * W ^ ε' / 2 with hy
  set E := W ^ (C₀ + K * m) with hE
  set G := W ^ D' with hG
  have hE0 : 0 < E := Real.rpow_pos_of_pos hW0 _
  have hG0 : 0 < G := Real.rpow_pos_of_pos hW0 _
  have hgr := hW₁' W hW
  have hp : W ^ (C₀ + K * m + D') = E * G := by rw [Real.rpow_add hW0]
  rw [hp] at hgr
  have hWD : W ^ (-D') = G⁻¹ := Real.rpow_neg hW0.le D'
  rw [hWD]
  have hmain : ‖STPsum (d := d) A (a 0)‖ * ‖ϑ t a‖ ≤ E * (C * Real.exp (-y)) :=
    mul_le_mul hPs hθ' (norm_nonneg _) hE0.le
  refine hmain.trans ?_
  have h1 : E * (C * Real.exp (-y)) * G ≤ 1 := by
    calc E * (C * Real.exp (-y)) * G = (C * (E * G)) * Real.exp (-y) := by ring
      _ ≤ Real.exp y * Real.exp (-y) := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  calc E * (C * Real.exp (-y)) = E * (C * Real.exp (-y)) * G * G⁻¹ := by field_simp
    _ ≤ 1 * G⁻¹ := by gcongr
    _ = G⁻¹ := one_mul _

/-! ## 5. Compiled nonempty instances (`d = 3`, `m = 1`, `Λ = 1`, `K = 2`, `L = 5`, `g = 1`, `t = 1/2`) -/

/-- A nonzero tensor supported on the diagonal `b₀ = b₁` (all pair distances vanish on its support). -/
private def qnA : (Fin 2 → Zd 3 5) → ℂ := fun b => if b 0 = b 1 then 1 else 0

private theorem qnA_ne : qnA ≠ 0 := by
  intro h
  have := congrFun h (fun _ => 0)
  simp [qnA] at this

private theorem qnA_norm_le : ‖qnA‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun b => ?_
  unfold qnA
  split_ifs <;> simp

private theorem qnA_fastDecay (W ε D : ℝ) (hW : 0 < W) (_hε : 0 < ε) :
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W ε D qnA := by
  intro a ⟨i, j, hij⟩
  by_cases h : a 0 = a 1
  · exfalso
    have hz : zdistD 3 5 (a i - a j) = 0 := by
      have : a i - a j = 0 := by
        fin_cases i <;> fin_cases j <;> simp [h]
      rw [this]; simp
    have hpos : 0 < W ^ ε * ellT 5 1 (1 / 2) :=
      mul_pos (Real.rpow_pos_of_pos hW _) (lt_of_lt_of_le zero_lt_one (one_le_ellT (by norm_num)))
    rw [hz] at hij
    simp at hij
    linarith
  · simp [qnA, h, Real.rpow_nonneg hW.le]

/-- **Instance of `stQopNorm_holds`** at `d = 3`, `m = 1`, `Λ = 1`, `K = 2`, the mollifier of
`QopAlgebra_mollifier_props` (`C = 26136`, `c = 1/2`) at `L = 5`, `g = 1`, `t = 1/2`, `W = 16`, `ε = 1/2`
(`W^ε = 4`), `D = 4`, and the nonzero decaying tensor `qnA`. -/
example : ∃ Cn : ℝ, 0 < Cn ∧ qnA ≠ 0 ∧
    ‖STQop (d := 3) (QopAlgebra_mollifier 3 5 1 1) (1 / 2) qnA‖ ≤
      (16 : ℝ) ^ (Cn * (1 / 2 : ℝ)) * ‖qnA‖ + (16 : ℝ) ^ (-4 + Cn) := by
  obtain ⟨Cn, hCn, h⟩ := stQopNorm_holds 3 (le_refl 3) 1 1 2 ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1))
    (1 / 2) one_pos two_pos (by positivity) (by norm_num)
  have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine ⟨Cn, hCn, qnA_ne, ?_⟩
  exact h 5 (by norm_num) 1 one_pos le_rfl 16 (1 / 2) 4 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [h16]) (by rw [Real.rpow_two]; norm_num)
    (QopAlgebra_mollifier 3 5 1 1) (QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos)
    (1 / 2) (by norm_num) (by norm_num) qnA (qnA_fastDecay 16 (1 / 2) 4 (by norm_num) (by norm_num))

/-- **Instance of `stQop_sub_fastDecay`** at the same data with `ε' = D' = 1`, `C₀ = 0`: there is a `W` (any
`W ≥ max W₀ 16`) with `L^d = 125 ≤ W^2` and `‖qnA‖ ≤ W^0` at which `qnA - 𝒬_{1/2} qnA` is `(1/2, 1, 1)`-decaying.
For `L = 5` the diameter of the torus is `6`, so for large `W` the window `W^{ε'} ℓ_t` exceeds it and the
conclusion `EKFastDecay` is vacuous at this `L`: the content is in the proof (far bound for `L^d ≤ W^K`). -/
example : ∃ W : ℝ, 16 ≤ W ∧
    EKFastDecay (d := 3) (L := 5) (n := 2) 1 (1 / 2) W 1 1
      (qnA - STQop (d := 3) (QopAlgebra_mollifier 3 5 1 1) (1 / 2) qnA) := by
  obtain ⟨W₀, hW₀, h⟩ := stQop_sub_fastDecay 3 1 2 ((1 + 40 * ((3 * 1 : ℕ) : ℝ)) * 6 ^ (3 * 1))
    (1 / 2) 0 1 1 (by positivity) (by norm_num) one_pos
  have hW16 : (16 : ℝ) ≤ max W₀ 16 := le_max_right _ _
  refine ⟨max W₀ 16, hW16, ?_⟩
  refine h 5 (by norm_num) 1 one_pos (max W₀ 16) (le_max_left _ _) ?_
    (QopAlgebra_mollifier 3 5 1 1) (QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos)
    (1 / 2) (by norm_num) (by norm_num) qnA ?_
  · rw [Real.rpow_two]; norm_num; nlinarith [hW16]
  · rw [Real.rpow_zero]; exact qnA_norm_le

end RBM.Gauss.Sizes
