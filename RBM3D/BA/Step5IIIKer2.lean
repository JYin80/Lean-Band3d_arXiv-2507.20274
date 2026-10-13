/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIKer

/-!
# U5a, part 2: the BA `tailtoTailSq` of Step 5, case (iii) (ticket T2481)

Band twins: `tailtoTailSq_kernelGen` (`Induction/TailtoTailSq.lean:906`), `tailtoTailSq_kernel`
(`:932`); paper: the quadratic variation of the martingale term of `(int_K-L_ST)`
(`3_5:2364-2383`; paper-delta candidates `T2215a/b`, `T2459b`).

1. `BAStep5IIITailSq`, `baStep5IIITailSq_holds` (target 5): the squared-profile `TailtoTail` for a
   4-index tensor `X` on the BA kernel `Step2Gen_uKer` at `baFM`: near pairs
   `max_i |b_i - b'_i| ≤ 2ℓ*` (`ℓ* = (log W)^{3/2}`) carry the weight `W_2² ρ²` of
   `Step5IIIKer_uKer_weighted` (`k = 2`), far pairs are counted through (H3), `#Zd = L^d` and
   three row sums.  The premises (H1) near bound, (H2) crude bound, (H3) `uKer` far field are
   inline (band 7g pattern); (H3) is discharged at the flow by `baStep5III_uKer_far`.
2. `BAStep5IIITailSqQV`, `baStep5IIITailSqQV_holds`: the reading with `X = STeeMg` and left side
   `STeeUMg` (`baStep2Mat_toFlowFM` is definitional).
3. Compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0` (target 6).

Helpers carry the stem `Step5IIIKer2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Sums over two slots: the far indicator and the splitting of a double sum -/

section Generic

/-- Far slot: the indicator of `Q` on slot `i` against the product of rows. -/
theorem Step5IIIKer2_slot_far {Z : Type*} [Fintype Z] (f : Fin 2 → Z → ℝ) (hf : ∀ j x, 0 ≤ f j x) (i : Fin 2)
    (Q : Z → Prop) [DecidablePred Q] {ρ ε₀ : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε₀) (hrow : ∀ j, ∑ x, f j x ≤ ρ)
    (hQ : ∀ x, Q x → f i x ≤ ε₀) :
    ∑ b : Fin 2 → Z, (∏ j, f j (b j)) * (if Q (b i) then 1 else 0) ≤ Fintype.card Z * ε₀ * ρ := by
  classical
  set g : Fin 2 → Z → ℝ := fun j x => if j = i then (if Q x then f j x else 0) else f j x with hg
  have h1 : ∀ b : Fin 2 → Z, (∏ j, f j (b j)) * (if Q (b i) then 1 else 0) = ∏ j, g j (b j) := by
    intro b
    by_cases hq : Q (b i)
    · simp only [hq, ite_true, mul_one]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · subst hj; simp [hg, hq]
      · simp [hg, hj]
    · simp only [hq, ite_false, mul_zero]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hg, hq]
  simp_rw [h1]
  rw [Step5IIIKer_sum_prod g]
  have hg0 : ∀ j x, 0 ≤ g j x := by
    intro j x
    simp only [hg]
    split_ifs <;> first | exact hf j x | exact le_rfl
  have hgi : ∑ x, g i x ≤ Fintype.card Z * ε₀ := by
    calc ∑ x, g i x ≤ ∑ _x : Z, ε₀ := Finset.sum_le_sum fun x _ => by
          simp only [hg, ite_true]
          split_ifs with hq
          · exact hQ x hq
          · exact hε
      _ = Fintype.card Z * ε₀ := by simp
  have hgj : ∀ j, j ≠ i → ∑ x, g j x ≤ ρ := fun j hj => by
    simp only [hg, hj, ite_false]
    exact hrow j
  have hs0 : ∀ j, 0 ≤ ∑ x, g j x := fun j => Finset.sum_nonneg fun x _ => hg0 j x
  rw [Fin.prod_univ_two]
  fin_cases i
  · exact mul_le_mul hgi (hgj 1 (by decide)) (hs0 1) (by positivity)
  · calc _ ≤ ρ * (Fintype.card Z * ε₀) := mul_le_mul (hgj 0 (by decide)) hgi (hs0 1) hρ
      _ = _ := by ring

/-- Termwise splitting of a double sum with a near part (profile `N`) and a far part (indicators `Fa`, `Fb`). -/
theorem Step5IIIKer2_double_le {α β : Type*} [Fintype α] [Fintype β] (P : α → ℝ) (P' : β → ℝ)
    (hP : ∀ a, 0 ≤ P a) (hP' : ∀ b, 0 ≤ P' b) (N Fa : α → ℝ) (Fb : β → ℝ) {p Y : ℝ} (G : α → β → ℝ)
    (hG : ∀ a b, G a b ≤ p * N a + Y * (Fa a + Fb b)) :
    ∑ a, ∑ b, P a * P' b * G a b ≤
      p * (∑ a, P a * N a) * ∑ b, P' b + Y * ((∑ a, P a * Fa a) * ∑ b, P' b + (∑ a, P a) * ∑ b, P' b * Fb b) := by
  set S' : ℝ := ∑ b, P' b with hS'
  set T' : ℝ := ∑ b, P' b * Fb b with hT'
  have hin : ∀ a, ∑ b, P a * P' b * G a b ≤ P a * ((p * N a + Y * Fa a) * S' + Y * T') := by
    intro a
    calc ∑ b, P a * P' b * G a b ≤ ∑ b, P a * (P' b * (p * N a + Y * Fa a) + Y * (P' b * Fb b)) :=
          Finset.sum_le_sum fun b _ => by
            have := mul_le_mul_of_nonneg_left (hG a b) (mul_nonneg (hP a) (hP' b))
            nlinarith [this]
      _ = P a * ((p * N a + Y * Fa a) * S' + Y * T') := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hS', hT']
          ring
  calc ∑ a, ∑ b, P a * P' b * G a b ≤ ∑ a, P a * ((p * N a + Y * Fa a) * S' + Y * T') :=
        Finset.sum_le_sum fun a _ => hin a
    _ = p * (∑ a, P a * N a) * S' + Y * ((∑ a, P a * Fa a) * S' + (∑ a, P a) * T') := by
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring

end Generic

/-! ## 2. The abstract bound on `Zd d L`: two row kernels `U` (charges `σ`) and `U'` (charges `!σ`) -/

section Abstract

variable {d L : ℕ} [NeZero L]

/-- **The abstract `tailtoTailSq` bound.**  Kernels `U_i`, `U'_i` with row sums `≤ ρ`, `U` with the `e^{2√·}`-weighted row sums `≤ W₂ ρ`,
both small (`≤ ε₀`) beyond `ell`; a tensor `X` with the near bound `‖X(b,b')‖ ≤ p (A₀ e^{-√|b₀-b₁|} + D₀₀)²` on
`max_i |b_i - b'_i| ≤ 2 ell` and the crude bound `‖X‖ ≤ Y`. -/
theorem Step5IIIKer2_tailsq_abstract (U U' : Fin 2 → Matrix (Zd d L) (Zd d L) ℂ)
    {ρ W2 A0 D00 ell ε₀ p Y : ℝ} (hρ : 0 ≤ ρ) (hε : 0 ≤ ε₀) (hA0 : 0 ≤ A0) (hD00 : 0 ≤ D00) (hp : 0 ≤ p) (hY : 0 ≤ Y)
    (hrow : ∀ i a, ∑ x, ‖U i a x‖ ≤ ρ) (hrow' : ∀ i a, ∑ x, ‖U' i a x‖ ≤ ρ)
    (hw : ∀ i a, ∑ x, ‖U i a x‖ * Real.exp (2 * Real.sqrt (zdistInf d L (a - x))) ≤ W2 * ρ)
    (hfar : ∀ i x y, ell ≤ (zdistInf d L (x - y) : ℝ) → ‖U i x y‖ ≤ ε₀)
    (hfar' : ∀ i x y, ell ≤ (zdistInf d L (x - y) : ℝ) → ‖U' i x y‖ ≤ ε₀)
    (X : (Fin 2 → Zd d L) → (Fin 2 → Zd d L) → ℂ)
    (H1 : ∀ b b' : Fin 2 → Zd d L, (∀ i, (zdistInf d L (b i - b' i) : ℝ) ≤ 2 * ell) →
      ‖X b b'‖ ≤ p * (A0 * Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1))) + D00) ^ 2)
    (H2 : ∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ Y) (a : Fin 2 → Zd d L) :
    ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L, (∏ i, U i (a i) (b i)) * (∏ i, U' i (a i) (b' i)) * X b b'‖ ≤
      p * ((2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1)))) + 2 * D00 ^ 2 * ρ ^ 2) * ρ ^ 2) +
        Y * (2 * (Fintype.card (Zd d L) * ε₀ * ρ) * ρ ^ 2 + ρ ^ 2 * (2 * (Fintype.card (Zd d L) * ε₀ * ρ))) := by
  classical
  set P : (Fin 2 → Zd d L) → ℝ := fun b => ∏ i, ‖U i (a i) (b i)‖ with hPdef
  set P' : (Fin 2 → Zd d L) → ℝ := fun b => ∏ i, ‖U' i (a i) (b i)‖ with hP'def
  have hP : ∀ b, 0 ≤ P b := fun b => Finset.prod_nonneg fun i _ => norm_nonneg _
  have hP' : ∀ b, 0 ≤ P' b := fun b => Finset.prod_nonneg fun i _ => norm_nonneg _
  set Ib : Fin 2 → (Fin 2 → Zd d L) → ℝ := fun i b => if ell ≤ (zdistInf d L (a i - b i) : ℝ) then 1 else 0 with hIb
  set N : (Fin 2 → Zd d L) → ℝ := fun b => (A0 * Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1))) + D00) ^ 2 with hN
  set Fa : (Fin 2 → Zd d L) → ℝ := fun b => ∑ i, Ib i b with hFa
  have hIb0 : ∀ i b, 0 ≤ Ib i b := fun i b => by simp only [hIb]; split_ifs <;> norm_num
  have hFa0 : ∀ b, 0 ≤ Fa b := fun b => Finset.sum_nonneg fun i _ => hIb0 i b
  have hN0 : ∀ b, 0 ≤ N b := fun b => sq_nonneg _
  -- the pointwise bound on `‖X‖`
  have hG : ∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ p * N b + Y * (Fa b + Fa b') := by
    intro b b'
    by_cases hnear : ∀ i, (zdistInf d L (b i - b' i) : ℝ) ≤ 2 * ell
    · have h := H1 b b' hnear
      have := mul_nonneg hY (add_nonneg (hFa0 b) (hFa0 b'))
      simp only [hN]
      linarith
    · push Not at hnear
      obtain ⟨i, hi⟩ := hnear
      have htri := Step5IIIKer_zdistInf_tri d L (b i) (a i) (b' i)
      have hcomm := Step5IIIKer_zdistInf_sub_comm d L (b i) (a i)
      have hreal : (zdistInf d L (b i - b' i) : ℝ) ≤ (zdistInf d L (a i - b i) : ℝ) + (zdistInf d L (a i - b' i) : ℝ) := by
        have : zdistInf d L (b i - b' i) ≤ zdistInf d L (a i - b i) + zdistInf d L (a i - b' i) := by omega
        exact_mod_cast this
      have hone : 1 ≤ Fa b + Fa b' := by
        by_cases h1 : ell ≤ (zdistInf d L (a i - b i) : ℝ)
        · have h2 : Ib i b ≤ Fa b := Finset.single_le_sum (f := fun j => Ib j b) (fun j _ => hIb0 j b) (Finset.mem_univ i)
          have h3 : Ib i b = 1 := by simp only [hIb, h1, ite_true]
          linarith [hFa0 b']
        · have h1' : ell ≤ (zdistInf d L (a i - b' i) : ℝ) := by linarith
          have h2 : Ib i b' ≤ Fa b' := Finset.single_le_sum (f := fun j => Ib j b') (fun j _ => hIb0 j b') (Finset.mem_univ i)
          have h3 : Ib i b' = 1 := by simp only [hIb, h1', ite_true]
          linarith [hFa0 b]
      have hpN : 0 ≤ p * N b := mul_nonneg hp (hN0 b)
      have := mul_le_mul_of_nonneg_left hone hY
      have h4 := H2 b b'
      linarith
  have hdouble := Step5IIIKer2_double_le P P' hP hP' N Fa Fa (p := p) (Y := Y)
    (fun b b' => ‖X b b'‖) hG
  -- the norm of the double sum
  have hnorm : ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L, (∏ i, U i (a i) (b i)) * (∏ i, U' i (a i) (b' i)) * X b b'‖ ≤
      ∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L, P b * P' b' * ‖X b b'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
    rw [norm_mul, norm_mul, norm_prod, norm_prod]
  refine hnorm.trans (hdouble.trans ?_)
  -- the three ingredients
  have hS : ∑ b, P b ≤ ρ ^ 2 := Step5IIIKer_prod_sum_le U hrow a
  have hS' : ∑ b, P' b ≤ ρ ^ 2 := Step5IIIKer_prod_sum_le U' hrow' a
  have hS0 : 0 ≤ ∑ b, P b := Finset.sum_nonneg fun b _ => hP b
  have hS'0 : 0 ≤ ∑ b, P' b := Finset.sum_nonneg fun b _ => hP' b
  have hNb : ∑ b, P b * N b ≤ 2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1)))) + 2 * D00 ^ 2 * ρ ^ 2 := by
    have h := Step5IIIKer_two_slot U (c := 2) (ρ := ρ) (Wc := W2) (amp := 2 * A0 ^ 2) (D0 := 2 * D00 ^ 2) (by norm_num) hρ
      (by positivity) (by positivity) hrow hw N (fun b => by
        have e : Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1))) ^ 2 = Real.exp (-(2 * Real.sqrt (zdistInf d L (b 0 - b 1)))) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
        simp only [hN]
        nlinarith [sq_nonneg (A0 * Real.exp (-Real.sqrt (zdistInf d L (b 0 - b 1))) - D00), e]) a
    exact h
  have hFb : ∀ (Q : Fin 2 → Matrix (Zd d L) (Zd d L) ℂ), (∀ i a, ∑ x, ‖Q i a x‖ ≤ ρ) →
      (∀ i x y, ell ≤ (zdistInf d L (x - y) : ℝ) → ‖Q i x y‖ ≤ ε₀) →
      ∑ b : Fin 2 → Zd d L, (∏ i, ‖Q i (a i) (b i)‖) * Fa b ≤ 2 * (Fintype.card (Zd d L) * ε₀ * ρ) := by
    intro Q hQrow hQfar
    have h1 : ∀ i : Fin 2, ∑ b : Fin 2 → Zd d L, (∏ j, ‖Q j (a j) (b j)‖) * Ib i b ≤ Fintype.card (Zd d L) * ε₀ * ρ := by
      intro i
      have := Step5IIIKer2_slot_far (fun j x => ‖Q j (a j) x‖) (fun j x => norm_nonneg _) i
        (fun x => ell ≤ (zdistInf d L (a i - x) : ℝ)) hρ hε (fun j => hQrow j (a j)) (fun x hx => hQfar i (a i) x hx)
      simpa only [hIb] using this
    calc ∑ b : Fin 2 → Zd d L, (∏ i, ‖Q i (a i) (b i)‖) * Fa b
        = ∑ i : Fin 2, ∑ b : Fin 2 → Zd d L, (∏ j, ‖Q j (a j) (b j)‖) * Ib i b := by
          simp only [hFa, Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ _i : Fin 2, (Fintype.card (Zd d L) * ε₀ * ρ) := Finset.sum_le_sum fun i _ => h1 i
      _ = 2 * (Fintype.card (Zd d L) * ε₀ * ρ) := by simp
  have hFaB := hFb U hrow hfar
  have hFbB := hFb U' hrow' hfar'
  have e1 : ∑ b, P b * Fa b = ∑ b : Fin 2 → Zd d L, (∏ i, ‖U i (a i) (b i)‖) * Fa b := rfl
  have e2 : ∑ b, P' b * Fa b = ∑ b : Fin 2 → Zd d L, (∏ i, ‖U' i (a i) (b i)‖) * Fa b := rfl
  rw [e1, e2]
  have hNb0 : 0 ≤ ∑ b, P b * N b := Finset.sum_nonneg fun b _ => mul_nonneg (hP b) (hN0 b)
  have hbd0 : 0 ≤ 2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1)))) + 2 * D00 ^ 2 * ρ ^ 2 :=
    hNb0.trans hNb
  have hFa0' : 0 ≤ ∑ b : Fin 2 → Zd d L, (∏ i, ‖U i (a i) (b i)‖) * Fa b :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hP b) (hFa0 b)
  have hFb0' : 0 ≤ ∑ b : Fin 2 → Zd d L, (∏ i, ‖U' i (a i) (b i)‖) * Fa b :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hP' b) (hFa0 b)
  have hc0 : 0 ≤ 2 * (Fintype.card (Zd d L) * ε₀ * ρ) := (hFa0'.trans hFaB)
  have ha : p * (∑ b, P b * N b) * ∑ b, P' b ≤
      p * ((2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * Real.exp (-(2 * Real.sqrt (zdistInf d L (a 0 - a 1)))) + 2 * D00 ^ 2 * ρ ^ 2) * ρ ^ 2) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hNb hS' hS'0 hbd0) hp
  have hb1 : (∑ b : Fin 2 → Zd d L, (∏ i, ‖U i (a i) (b i)‖) * Fa b) * ∑ b, P' b ≤ 2 * (Fintype.card (Zd d L) * ε₀ * ρ) * ρ ^ 2 :=
    mul_le_mul hFaB hS' hS'0 hc0
  have hb2 : (∑ b, P b) * ∑ b : Fin 2 → Zd d L, (∏ i, ‖U' i (a i) (b i)‖) * Fa b ≤ ρ ^ 2 * (2 * (Fintype.card (Zd d L) * ε₀ * ρ)) :=
    mul_le_mul hS hFbB hFb0' (sq_nonneg ρ)
  have := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hY
  linarith

end Abstract

/-! ## 3. Target 5 -/

/-- The cardinality of the block lattice: `#Z_L^d = L^d`. -/
theorem Step5IIIKer2_card (d L : ℕ) [NeZero L] : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
  have h : Fintype.card (Zd d L) = L ^ d := by simp [Zd, ZMod.card]
  rw [h]; push_cast; rfl

/-- The final arithmetic: `A₀ ρ² = A_w` turns the abstract bound into the pinned right-hand side, `C_q = 2 W₂²`. -/
theorem Step5IIIKer2_arith {p ρ W2 A0 Aw D00 e1 : ℝ} (hp : 0 ≤ p) (hρ : 0 ≤ ρ) (hW2 : 1 ≤ W2) (hAw : 0 ≤ Aw) (he1 : 0 ≤ e1)
    (hD00 : 0 ≤ D00) (hkey : A0 * ρ ^ 2 = Aw) :
    p * ((2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * e1 ^ 2 + 2 * D00 ^ 2 * ρ ^ 2) * ρ ^ 2) ≤
      2 * W2 ^ 2 * p * ((Aw * e1 + D00) ^ 2 + ρ ^ 4 * D00 ^ 2) := by
  have e : (2 * A0 ^ 2 * W2 ^ 2 * ρ ^ 2 * e1 ^ 2 + 2 * D00 ^ 2 * ρ ^ 2) * ρ ^ 2 =
      2 * W2 ^ 2 * (Aw * e1) ^ 2 + 2 * ρ ^ 4 * D00 ^ 2 := by
    rw [← hkey]; ring
  rw [e]
  have h1 : (Aw * e1) ^ 2 ≤ (Aw * e1 + D00) ^ 2 := by
    have : 0 ≤ Aw * e1 := mul_nonneg hAw he1
    nlinarith
  have hW : 1 ≤ W2 ^ 2 := one_le_pow₀ hW2
  have h2 : 2 * ρ ^ 4 * D00 ^ 2 ≤ 2 * W2 ^ 2 * (ρ ^ 4 * D00 ^ 2) := by
    have : 0 ≤ ρ ^ 4 * D00 ^ 2 := by positivity
    nlinarith
  have h3 : 2 * W2 ^ 2 * (Aw * e1) ^ 2 + 2 * ρ ^ 4 * D00 ^ 2 ≤ 2 * W2 ^ 2 * ((Aw * e1 + D00) ^ 2 + ρ ^ 4 * D00 ^ 2) := by
    nlinarith
  calc _ ≤ p * (2 * W2 ^ 2 * ((Aw * e1 + D00) ^ 2 + ρ ^ 4 * D00 ^ 2)) := mul_le_mul_of_nonneg_left h3 hp
    _ = _ := by ring

/-- **Target 5** (BA `tailtoTailSq`; band twin `tailtoTailSq_kernelGen`, `Induction/TailtoTailSq.lean:906`): the squared-profile
`TailtoTail` for a 4-index tensor `X` on the BA kernel, near cut `2ℓ*` (paper-delta T2459b), `ρ = (1-v)/(1-w)`, `Cq = Cq(d, 𝔡⁻¹, κ)`.
(H1) near bound `‖X(b,b')‖ ≤ p T_{v,D}(|b₀-b₁|)²` where `max_i |b_i - b'_i| ≤ 2ℓ*`; (H2) crude bound `‖X‖ ≤ Y`;
(H3) `‖uKer_{v,w}(x,y)‖ ≤ W^{-D₂}` beyond `ℓ*`, every charge pair (target 4 (b) at the flow). -/
def BAStep5IIITailSq (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D D₂ v w p Y : ℝ),
      BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
      0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w → 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
      ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d (sz.L n)) → (Fin 2 → Zd d (sz.L n)) → ℂ),
        (∀ b b' : Fin 2 → Zd d (sz.L n),
          (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
          ‖X b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
        (∀ b b' : Fin 2 → Zd d (sz.L n), ‖X b b'‖ ≤ Y) →
        (∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
          Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
          ‖Step2Gen_uKer (baFM sz lam0 E) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
        ∀ a : Fin 2 → Zd d (sz.L n),
          ‖∑ b : Fin 2 → Zd d (sz.L n), ∑ b' : Fin 2 → Zd d (sz.L n),
              (∏ i, Step2Gen_uKer (baFM sz lam0 E) n (σ i) (σ (finRotate 2 i)) v w (a i) (b i)) *
                (∏ i, Step2Gen_uKer (baFM sz lam0 E) n (!σ i) (!σ (finRotate 2 i)) v w (a i) (b' i)) * X b b'‖ ≤
            Cq * p * (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
              4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂)

theorem baStep5IIITailSq_holds (d : ℕ) : BAStep5IIITailSq d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨W2, hW21, HW⟩ := Step5IIIKer_uKer_weighted d hd 𝔡⁻¹ κ (inv_pos.mpr h𝔡) hκ 2 (by norm_num)
  refine ⟨2 * W2 ^ 2, by positivity, ?_⟩
  intro sz lam0 E n D D₂ v w p Y hreal hpos hΛ hle hv hvw hw1 hreg hlog hp hY σ X H1 H2 H3 a
  have hIm := Step5IIIKer_hIm hκ hreal
  have hg2 := Step5IIIKer_sq_le hpos hle hreg
  have h1w : 0 < 1 - w := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hρ0 : 0 ≤ (1 - v) / (1 - w) := div_nonneg h1v.le h1w.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  simp only [Step2Kern_uKer_BA sz lam0 E n hIm] at H3 ⊢
  set Wn : ℝ := ((sz.W n : ℕ) : ℝ) with hWn
  have hWd : 0 < Wn ^ d := pow_pos hW0 d
  have hD00 : 0 ≤ Wn ^ (-D) := Real.rpow_nonneg hW0.le _
  have hε : 0 ≤ Wn ^ (-D₂) := Real.rpow_nonneg hW0.le _
  have habs := Step5IIIKer2_tailsq_abstract
    (fun i => BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) v w (σ i) (σ (finRotate 2 i)))
    (fun i => BAuKer d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) v w (!σ i) (!σ (finRotate 2 i)))
    (ρ := (1 - v) / (1 - w)) (W2 := W2) (A0 := ((Wn ^ d * |1 - v|)⁻¹) ^ 2) (D00 := Wn ^ (-D))
    (ell := Real.log Wn ^ (3 / 2 : ℝ)) (ε₀ := Wn ^ (-D₂)) (p := p) (Y := Y) hρ0 hε (by positivity) hD00 hp hY
    (fun i x => Step5IIIKer_uKer_row_le hreal hv hvw hw1 _ _ x)
    (fun i x => Step5IIIKer_uKer_row_le hreal hv hvw hw1 _ _ x)
    (fun i x => HW (sz.L n) (sz.three_le_L n) (lam0 n) hpos hΛ (E n) _ hreal v w hv hvw hw1 hg2 _ _ x)
    (fun i x y hxy => H3 _ _ x y hxy) (fun i x y hxy => H3 _ _ x y hxy) X
    (fun b b' hnear => H1 b b' hnear) H2 a
  refine habs.trans ?_
  rw [Step5IIIKer2_card]
  have habs1 : |1 - v| = 1 - v := abs_of_pos h1v
  have habs2 : |1 - w| = 1 - w := abs_of_pos h1w
  have hkey : ((Wn ^ d * |1 - v|)⁻¹) ^ 2 * ((1 - v) / (1 - w)) ^ 2 = ((Wn ^ d * |1 - w|)⁻¹) ^ 2 := by
    rw [habs1, habs2]
    field_simp
  have he : Real.exp (-(2 * Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1)))) = Real.exp (-Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1))) ^ 2 := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [he]
  have harith := Step5IIIKer2_arith (p := p) (ρ := (1 - v) / (1 - w)) (W2 := W2) (A0 := ((Wn ^ d * |1 - v|)⁻¹) ^ 2)
    (Aw := ((Wn ^ d * |1 - w|)⁻¹) ^ 2) (D00 := Wn ^ (-D)) (e1 := Real.exp (-Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1))))
    hp hρ0 hW21 (by positivity) (Real.exp_pos _).le hD00 hkey
  have hY' : Y * (2 * ((sz.L n : ℝ) ^ d * Wn ^ (-D₂) * ((1 - v) / (1 - w))) * ((1 - v) / (1 - w)) ^ 2 +
      ((1 - v) / (1 - w)) ^ 2 * (2 * ((sz.L n : ℝ) ^ d * Wn ^ (-D₂) * ((1 - v) / (1 - w))))) =
      4 * Y * (sz.L n : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * Wn ^ (-D₂) := by ring
  rw [hY']
  have hSTw : STtailTD sz n w D a = ((Wn ^ d * |1 - w|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1))) + Wn ^ (-D) := rfl
  rw [hSTw]
  have e3 : (2 * W2 ^ 2) * p * ((((Wn ^ d * |1 - w|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1))) + Wn ^ (-D)) ^ 2 +
      ((1 - v) / (1 - w)) ^ 4 * (Wn ^ (-D)) ^ 2) = 2 * W2 ^ 2 * p * ((((Wn ^ d * |1 - w|)⁻¹) ^ 2 * Real.exp (-Real.sqrt (zdistInf d (sz.L n) (a 0 - a 1))) + Wn ^ (-D)) ^ 2 +
      ((1 - v) / (1 - w)) ^ 4 * (Wn ^ (-D)) ^ 2) := rfl
  linarith

/-- **Target 5, the QV reading** (band twin `tailtoTailSq_kernel`, `:932`): target 5 at `X = STeeMg (baStep2Mat sz lam0 E) n v H σ`, the left
side being `STeeUMg` (`Chain/Step2Gen.lean:983`), the weight of clause 4 of `STGridRepNAtgL d 2`. -/
def BAStep5IIITailSqQV (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ Cq : ℝ, 0 < Cq ∧
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (D D₂ v w p Y : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
      BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n) → 0 < lam0 n → lam0 n ≤ 𝔡⁻¹ → lam0 n ≤ sz.lam n →
      0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w → 4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
      (∀ b b' : Fin 2 → Zd d (sz.L n),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz lam0 E) n v H σ b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
      (∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeMg (baStep2Mat sz lam0 E) n v H σ b b'‖ ≤ Y) →
      (∀ (τ τ' : Bool) (x y : Zd d (sz.L n)),
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ (zdistInf d (sz.L n) (x - y) : ℝ) →
        ‖Step2Gen_uKer (baFM sz lam0 E) n τ τ' v w x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
      ∀ a : Fin 2 → Zd d (sz.L n),
        ‖STeeUMg (baStep2Mat sz lam0 E) n v w H σ a‖ ≤
          Cq * p * (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
            4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂)

theorem baStep5IIITailSqQV_holds (d : ℕ) : BAStep5IIITailSqQV d := by
  intro hd κ 𝔡 hκ h𝔡
  obtain ⟨Cq, hCq, H⟩ := baStep5IIITailSq_holds d hd κ 𝔡 hκ h𝔡
  refine ⟨Cq, hCq, ?_⟩
  intro sz lam0 E n D D₂ v w p Y Hm σ hreal hpos hΛ hle hv hvw hw1 hreg hlog hp hY h1 h2 h3 a
  exact H sz lam0 E n D D₂ v w p Y hreal hpos hΛ hle hv hvw hw1 hreg hlog hp hY σ
    (STeeMg (baStep2Mat sz lam0 E) n v Hm σ) h1 h2 h3 a

/-! ## 4. Target 6: compiled nonempty instances at `d = 3`, `sz0`, `zSeq`, `flow_sz0`

`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `v = 1/10`, `w = 1/2` (`half_lt_t0`), `D = D₂ = 1`; the regime `sz0.lam² ≤ 1/2` holds from
`sz0.lam ≤ 1/64`.  Every deterministic premise is discharged: `BAReal` (`BAflow_real`), `0 < g₀ ≤ 𝔡⁻¹` (`BAflow_lam0_window`),
`g₀ ≤ sz0.lam` (`baStep5III_lam0_le_lam`), `4 ≤ log W` (`W_n → ∞`), and (H3) by `baStep5III_uKer_far`. -/

section Instances

/-- The tensor of the instance: `X(b,b') = T_{1/10,1}(|b₀-b₁|)²` (equality in (H1), `p = 1`). -/
def Step5IIIKer2_Xinst (n : ℕ) (b _b' : Fin 2 → Zd 3 (SizesInst.sz0.L n)) : ℂ :=
  ((STtailTD SizesInst.sz0 n (1 / 10) 1 b ^ 2 : ℝ) : ℂ)

/-- Its crude bound `Y = (τ_v² + W^{-1})²` (`e^{-√r} ≤ 1`, (H2)). -/
def Step5IIIKer2_Yinst (n : ℕ) : ℝ :=
  ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹ ^ 2 + ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2

theorem Step5IIIKer2_Xinst_near (n : ℕ) (b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n)) :
    ‖Step5IIIKer2_Xinst n b b'‖ ≤ 1 * STtailTD SizesInst.sz0 n (1 / 10) 1 b ^ 2 := by
  unfold Step5IIIKer2_Xinst
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), one_mul]

theorem Step5IIIKer2_Xinst_crude (n : ℕ) (b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n)) :
    ‖Step5IIIKer2_Xinst n b b'‖ ≤ Step5IIIKer2_Yinst n := by
  unfold Step5IIIKer2_Xinst Step5IIIKer2_Yinst
  rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have hW : (0 : ℝ) < ((SizesInst.sz0.W n : ℕ) : ℝ) := by exact_mod_cast SizesInst.sz0.W_pos n
  have hT : STtailTD SizesInst.sz0 n (1 / 10) 1 b =
      ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 *
        Real.exp (-Real.sqrt (zdistInf 3 (SizesInst.sz0.L n) (b 0 - b 1))) + ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := rfl
  rw [hT]
  have h0 : 0 ≤ ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 := by positivity
  have h1 : Real.exp (-Real.sqrt (zdistInf 3 (SizesInst.sz0.L n) (b 0 - b 1))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
  have h2 := Real.rpow_nonneg hW.le (-(1 : ℝ))
  have h3 : ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 *
      Real.exp (-Real.sqrt (zdistInf 3 (SizesInst.sz0.L n) (b 0 - b 1))) ≤ ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 := by
    calc _ ≤ ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  have h4 : 0 ≤ ((((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 * |1 - 1 / 10|)⁻¹) ^ 2 *
      Real.exp (-Real.sqrt (zdistInf 3 (SizesInst.sz0.L n) (b 0 - b 1))) := mul_nonneg h0 (Real.exp_pos _).le
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **Instance of target 5** (`p = 1`, `X = Step5IIIKer2_Xinst`, `Y = Step5IIIKer2_Yinst`; (H1)-(H3) all discharged, nonzero `X`):
eventually in `n`, every `σ` and `a`. -/
example : ∃ Cq : ℝ, 0 < Cq ∧ ∀ᶠ n in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (SizesInst.sz0.L n)),
    ‖∑ b : Fin 2 → Zd 3 (SizesInst.sz0.L n), ∑ b' : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        (∏ i, Step2Gen_uKer (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n (σ i) (σ (finRotate 2 i)) (1 / 10) (1 / 2) (a i) (b i)) *
          (∏ i, Step2Gen_uKer (baFMz SizesInst.sz0 FlowPinsInst.zSeq) n (!σ i) (!σ (finRotate 2 i)) (1 / 10) (1 / 2) (a i) (b' i)) *
            Step5IIIKer2_Xinst n b b'‖ ≤
      Cq * 1 * (STtailTD SizesInst.sz0 n (1 / 2) 1 a ^ 2 +
          ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 4 * (((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2) +
        4 * Step5IIIKer2_Yinst n * ((SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 * ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 3 *
          ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨Cq, hCq, H⟩ := baStep5IIITailSq_holds 3 le_rfl (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨Cq, hCq, ?_⟩
  have hWt := Step5IIIKer_W_tendsto FlowPinsInst.flow_sz0.1
  filter_upwards [BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0,
    baStep5III_uKer_far 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos (1 / 6)
      SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0,
    (Real.tendsto_log_atTop.comp hWt).eventually_ge_atTop 4] with n hn hfar hlog σ a
  have hY : 0 ≤ Step5IIIKer2_Yinst n := by unfold Step5IIIKer2_Yinst; positivity
  exact H SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n 1 1 (1 / 10) (1 / 2) 1
    (Step5IIIKer2_Yinst n) (BAflow_real _ _ _ _ _ _ FlowPinsInst.flow_sz0 n) hn.1 hn.2
    (baStep5III_lam0_le_lam (by norm_num) FlowPinsInst.flow_sz0 n hn.1) (by norm_num) (by norm_num) (by norm_num)
    (Step5IIIKer_sz0_reg n (by norm_num)) hlog (by norm_num) hY σ (Step5IIIKer2_Xinst n)
    (fun b b' _ => Step5IIIKer2_Xinst_near n b b') (Step5IIIKer2_Xinst_crude n)
    (fun τ τ' x y hxy => hfar (1 / 10) (1 / 2) (by norm_num) (by norm_num) (FlowPinsInst.half_lt_t0 n).le
      (Step5IIIKer_sz0_reg n (by norm_num)) τ τ' x y hxy) a

/-- **Instance of target 5, QV reading**, composed with target 4 (b) (the U5d reading): (H3) discharged eventually, `4 ≤ log W` too;
(H1)-(H2) stay premises (their sources are U5b's `dif` bound through U5c's good event, and U5d's crude bound). -/
example : ∃ Cq : ℝ, 0 < Cq ∧ ∀ᶠ n in atTop,
    ∀ (p Y : ℝ) (H : Matrix (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) (Idx 3 (SizesInst.sz0.L n) (SizesInst.sz0.W n)) ℂ)
      (σ : Fin 2 → Bool), 0 ≤ p → 0 ≤ Y →
      (∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        (∀ i : Fin 2, (zdistInf 3 (SizesInst.sz0.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) H σ b b'‖ ≤ p * STtailTD SizesInst.sz0 n (1 / 10) 1 b ^ 2) →
      (∀ b b' : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        ‖STeeMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) H σ b b'‖ ≤ Y) →
      ∀ a : Fin 2 → Zd 3 (SizesInst.sz0.L n),
        ‖STeeUMg (baStep2Mat SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq))
            n (1 / 10) (1 / 2) H σ a‖ ≤
          Cq * p * (STtailTD SizesInst.sz0 n (1 / 2) 1 a ^ 2 +
              ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 4 * (((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2) +
            4 * Y * ((SizesInst.sz0.L n : ℕ) : ℝ) ^ 3 * ((1 - 1 / 10) / (1 - 1 / 2) : ℝ) ^ 3 * ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨Cq, hCq, Hq⟩ := baStep5IIITailSqQV_holds 3 le_rfl (1 / 2) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨Cq, hCq, ?_⟩
  have hWt := Step5IIIKer_W_tendsto FlowPinsInst.flow_sz0.1
  filter_upwards [BAflow_lam0_window (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0,
    baStep5III_uKer_far 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 1 one_pos (1 / 6)
      SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0,
    (Real.tendsto_log_atTop.comp hWt).eventually_ge_atTop 4] with n hn hfar hlog p Y H σ hp hY h1 h2 a
  exact Hq SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) n 1 1 (1 / 10) (1 / 2) p Y
    _ σ (BAflow_real _ _ _ _ _ _ FlowPinsInst.flow_sz0 n) hn.1 hn.2
    (baStep5III_lam0_le_lam (by norm_num) FlowPinsInst.flow_sz0 n hn.1) (by norm_num) (by norm_num) (by norm_num)
    (Step5IIIKer_sz0_reg n (by norm_num)) hlog hp hY h1 h2
    (fun τ τ' x y hxy => hfar (1 / 10) (1 / 2) (by norm_num) (by norm_num) (FlowPinsInst.half_lt_t0 n).le
      (Step5IIIKer_sz0_reg n (by norm_num)) τ τ' x y hxy) a

end Instances

end RBM.BA

end
