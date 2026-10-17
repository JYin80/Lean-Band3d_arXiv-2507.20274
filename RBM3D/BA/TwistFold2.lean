/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistPins
import RBM3D.Induction.ConArgDet

/-!
# BA-L L4d2a (T2445), part A: the model-free two-insertion fold and the BA facts of `M` it uses

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:118` (the second `GG` step); design
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §2.2, §4, §5 (route (A'), supervisor
`2026-10-12-0851.md` Q2, S3A-C1 to S3A-C3).  Twin of `BA/TwistPins.lean` (`twLoopX`, `twTr_eq`,
`twFold`, `twWard`).

Contents (all deterministic, no stochastic premise):
* `twLoop2X`, `twLoop2X_trace`: `Σ_c ρ(c) Tr(E_a A P_{c₁c₂} X P_{c₃c₄} C)`, the `twTrP` convention;
* `twFold2_holds`, `twFold2_bound_holds`: one Cauchy-Schwarz over `(c₁, c₂, c₃, c₄, x, o, o')` with
  weight `|ρ|` and its bound by the three marginals `β, r₁, r₂` (root `W^{-5d}`: Fable §5 prints
  `W^{-3d/2}` for the root);
* `twVec_holds`: `‖(G - M)φ‖² ≤ 2 η⁻¹ Im⟨φ, Gφ⟩ + 2 ‖Mφ‖²` under `G - G^* = 2iη G^*G`;
* `twMrow_le_holds`, `twMblk_le_holds`: the upper bounds `‖M^* e_x‖² ≤ 1` and `‖Mφ‖² ≤ ‖φ‖²` (`φ`
  supported in `[b]`) from `BAMfine_eq` and the `M`-Ward identity;
* `twB0_ge_holds`, `twEta_ge_holds`: S3A-C2 (`W^d Bctl ≥ (𝔡⁻² + 1)⁻¹`) and S3A-C3
  (`η_t ≥ κ (1 - t)`).

The `≺` row is in `BA/TwistFold2B.lean`.  All private helpers carry the stem `TwistFold2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Block combinatorics (copies of the private helpers of `BA/TwistPins.lean:293-350`) -/

section Blocks
variable {d : ℕ} {sz : Sizes d}

theorem TwistFold2_split_shift (n : ℕ) (c : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    split d (sz.L n) (sz.W n) (twShift n c x) = (c, (split d (sz.L n) (sz.W n) x).2) :=
  (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _

theorem TwistFold2_mem_blk (n : ℕ) {c : Zd d (sz.L n)} {x : Idx d (sz.L n) (sz.W n)} :
    x ∈ twBlk n c ↔ (split d (sz.L n) (sz.W n) x).1 = c := by
  simp [twBlk]

theorem TwistFold2_shift_mem (n : ℕ) (c₂ : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    twShift n c₂ x ∈ twBlk n c₂ := by
  rw [TwistFold2_mem_blk, TwistFold2_split_shift]

/-- `w ↦ (c₂, o_w)` is a bijection `[c₁] → [c₂]`. -/
theorem TwistFold2_sum_shift {β : Type*} [AddCommMonoid β] (n : ℕ) (c₁ c₂ : Zd d (sz.L n))
    (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ w ∈ twBlk n c₁, F (twShift n c₂ w) = ∑ y ∈ twBlk n c₂, F y := by
  refine Finset.sum_nbij (twShift n c₂) (fun w _ => TwistFold2_shift_mem n c₂ w) ?_ ?_ (fun _ _ => rfl)
  · intro w hw w' hw' h
    have hw1 := (TwistFold2_mem_blk n).1 (Finset.mem_coe.1 hw)
    have hw2 := (TwistFold2_mem_blk n).1 (Finset.mem_coe.1 hw')
    have h2 := congrArg (split d (sz.L n) (sz.W n)) h
    rw [TwistFold2_split_shift, TwistFold2_split_shift] at h2
    apply split_injective d (sz.L n) (sz.W n)
    exact Prod.ext (hw1.trans hw2.symm) (Prod.mk.inj h2).2
  · intro y hy
    have hy1 := (TwistFold2_mem_blk n).1 (Finset.mem_coe.1 hy)
    have hs : split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (c₁, (split d (sz.L n) (sz.W n) y).2)) =
        (c₁, (split d (sz.L n) (sz.W n) y).2) := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply _
    refine ⟨(splitEquiv d (sz.L n) (sz.W n)).symm (c₁, (split d (sz.L n) (sz.W n) y).2), ?_, ?_⟩
    · rw [Finset.mem_coe, TwistFold2_mem_blk, hs]
    · apply split_injective d (sz.L n) (sz.W n)
      rw [TwistFold2_split_shift, hs]
      exact Prod.ext hy1.symm rfl

/-- The blocks partition the lattice (any additive monoid). -/
theorem TwistFold2_sum_blk {β : Type*} [AddCommMonoid β] (n : ℕ) (F : Idx d (sz.L n) (sz.W n) → β) :
    ∑ a : Zd d (sz.L n), ∑ x ∈ twBlk n a, F x = ∑ x, F x :=
  Finset.sum_fiberwise Finset.univ (fun x => (split d (sz.L n) (sz.W n) x).1) F

theorem TwistFold2_norm_inv_pow (n : ℕ) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  simp

theorem TwistFold2_card_blk (n : ℕ) (c : Zd d (sz.L n)) :
    ((twBlk n c).card : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d := by
  have : (twBlk n c).card = (sz.W n) ^ d := card_Iblk d (sz.L n) (sz.W n) c
  rw [this]; push_cast; rfl

end Blocks

/-! ## 2. Target 1: `twLoop2X` and its trace form -/

section Fold2
variable {d : ℕ} {sz : Sizes d}

/-- **Target 1** (`twLoop2X`, Fable §5; the two-insertion twin of `twLoopX`): `Σ_c ρ(c) Tr(E_a A P_{c₁c₂} X P_{c₃c₄} C)` in the `twTrP` convention
(`P_{c₁c₂} = W^{-d} Σ_o |(c₁,o)⟩⟨(c₂,o)|`; `w = (c₁,o) ∈ [c₁]`, `w' = (c₃,o') ∈ [c₃]`), i.e.
`W^{-3d} Σ_c ρ(c) Σ_{x∈[a]} Σ_{o,o'} A_{x,(c₁,o)} X_{(c₂,o),(c₃,o')} C_{(c₄,o'),x}`. -/
def twLoop2X (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)) : ℂ :=
  ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ρ c₁ c₂ c₃ c₄ * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 *
    ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x)

/-! ## 3. Target 2: `twFold2` -/

/-- Cauchy-Schwarz over a triple sum. -/
private theorem TwistFold2_cs3 {α β γ : Type*} (s : Finset α) (t : Finset β) (r : Finset γ) (f g : α → β → γ → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, f x y z * g x y z) ^ 2 ≤
      (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, f x y z ^ 2) * (∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ r, g x y z ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ (t ×ˢ r)) (fun p => f p.1 p.2.1 p.2.2) (fun p => g p.1 p.2.1 p.2.2)
  simp only [Finset.sum_product] at h
  exact h

/-- **Target 2** (`twFold2`, Fable §5; twin of `twFold`): one Cauchy-Schwarz over `(c₁, c₂, c₃, c₄, x, o, o')` with the weight `|ρ|`
(0851 Q2), split `[A_{x,(c₁,o)} X_{(c₂,o),(c₃,o')}] · [C_{(c₄,o'),x}]`; all matrices. -/
def twFold2 : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)),
    ‖twLoop2X n A X C ρ a‖ ^ 2 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 6 *
      (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2) *
      (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖C (twShift n c₄ w') x‖ ^ 2)

theorem twFold2_holds : twFold2 := by
  intro d sz n A X C ρ a
  set w : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  -- the inner sum and the two inner square sums at `c = (c₁, c₂, c₃, c₄)`
  let S : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun c₁ c₂ c₃ c₄ =>
    ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃, A x y * X (twShift n c₂ y) y' * C (twShift n c₄ y') x
  let F : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun c₁ c₂ c₃ c₄ =>
    ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃, ‖A x y‖ ^ 2 * ‖X (twShift n c₂ y) y'‖ ^ 2
  let G : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun c₁ c₂ c₃ c₄ =>
    ∑ x ∈ twBlk n a, ∑ _y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃, ‖C (twShift n c₄ y') x‖ ^ 2
  have hSFG : ∀ c₁ c₂ c₃ c₄, ‖S c₁ c₂ c₃ c₄‖ ^ 2 ≤ F c₁ c₂ c₃ c₄ * G c₁ c₂ c₃ c₄ := by
    intro c₁ c₂ c₃ c₄
    have h0 : ‖S c₁ c₂ c₃ c₄‖ ≤ ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃,
        (‖A x y‖ * ‖X (twShift n c₂ y) y'‖) * ‖C (twShift n c₄ y') x‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun y _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y' _ => ?_)))
      rw [norm_mul, norm_mul]
    calc ‖S c₁ c₂ c₃ c₄‖ ^ 2 ≤ (∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃,
          (‖A x y‖ * ‖X (twShift n c₂ y) y'‖) * ‖C (twShift n c₄ y') x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h0 2
      _ ≤ (∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃, (‖A x y‖ * ‖X (twShift n c₂ y) y'‖) ^ 2) *
          (∑ x ∈ twBlk n a, ∑ y ∈ twBlk n c₁, ∑ y' ∈ twBlk n c₃, ‖C (twShift n c₄ y') x‖ ^ 2) :=
          TwistFold2_cs3 _ _ _ (fun x y y' => ‖A x y‖ * ‖X (twShift n c₂ y) y'‖)
            (fun x y y' => ‖C (twShift n c₄ y') x‖)
      _ = F c₁ c₂ c₃ c₄ * G c₁ c₂ c₃ c₄ := by simp only [F, G, mul_pow]
  -- the outer sum
  have hL : ‖twLoop2X n A X C ρ a‖ ≤ ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, w ^ 3 * (‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖) := by
    unfold twLoop2X
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₁ _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun c₂ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₃ _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₄ _ => ?_))))
    rw [norm_mul, norm_mul, norm_pow, TwistFold2_norm_inv_pow]
    exact le_of_eq (by ring)
  have hsum : (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖) ^ 2 ≤
      (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * F c₁ c₂ c₃ c₄) * (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * G c₁ c₂ c₃ c₄) := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      (Finset.univ : Finset (Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (r := fun p => ‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ * ‖S p.1 p.2.1 p.2.2.1 p.2.2.2‖)
      (f := fun p => ‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ * F p.1 p.2.1 p.2.2.1 p.2.2.2)
      (g := fun p => ‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ * G p.1 p.2.1 p.2.2.1 p.2.2.2)
      (fun p _ => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
        Finset.sum_nonneg fun y' _ => by positivity))
      (fun p _ => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
        Finset.sum_nonneg fun y' _ => by positivity))
      (fun p _ => by
        have h1 := hSFG p.1 p.2.1 p.2.2.1 p.2.2.2
        have h2 := norm_nonneg (ρ p.1 p.2.1 p.2.2.1 p.2.2.2)
        calc (‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ * ‖S p.1 p.2.1 p.2.2.1 p.2.2.2‖) ^ 2
            = ‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 * ‖S p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 := mul_pow _ _ _
          _ ≤ ‖ρ p.1 p.2.1 p.2.2.1 p.2.2.2‖ ^ 2 * (F p.1 p.2.1 p.2.2.1 p.2.2.2 * G p.1 p.2.1 p.2.2.1 p.2.2.2) :=
              mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
          _ = _ := by ring)
    simpa only [Fintype.sum_prod_type] using h
  have h3 : (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, w ^ 3 * (‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖)) =
      w ^ 3 * ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖ := by
    simp only [Finset.mul_sum]
  rw [h3] at hL
  calc ‖twLoop2X n A X C ρ a‖ ^ 2 ≤ (w ^ 3 * ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hL 2
    _ = w ^ 6 * (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ‖S c₁ c₂ c₃ c₄‖) ^ 2 := by ring
    _ ≤ w ^ 6 * ((∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * F c₁ c₂ c₃ c₄) *
          (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * G c₁ c₂ c₃ c₄)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-! ## 4. Target 3: `twFold2_bound` -/

private theorem TwistFold2_sum4_comm {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ℝ) :
    ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, f c₁ c₂ c₃ c₄ = ∑ c₄, ∑ c₁, ∑ c₂, ∑ c₃, f c₁ c₂ c₃ c₄ := by
  calc ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, f c₁ c₂ c₃ c₄ = ∑ c₁, ∑ c₂, ∑ c₄, ∑ c₃, f c₁ c₂ c₃ c₄ :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c₁, ∑ c₄, ∑ c₂, ∑ c₃, f c₁ c₂ c₃ c₄ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c₄, ∑ c₁, ∑ c₂, ∑ c₃, f c₁ c₂ c₃ c₄ := Finset.sum_comm

/-- **Target 3** (`twFold2_bound`, Fable §4, §5): `β ≥ max_{u,c} Σ_{v∈[c]} |X_{uv}|²`, `r₁ ≥ max_{c₁} Σ_{c₂c₃c₄} |ρ|`,
`r₂ ≥ max_{c₄} Σ_{c₁c₂c₃} |ρ|` give `|twLoop2X|² ≤ W^{-5d} β r₁ r₂ (Σ_{x∈[a]} ‖A^* e_x‖²)(Σ_{x∈[a]} ‖C e_x‖²)`.  `W^{-5d}` is
`W^{-6d}` of target 2 times the `W^d` of the free `o`-sum (Fable §2.2 `F₂` step 1); Fable §5's `W^{-3d/2}` reads `W^{-5d/2}`. -/
def twFold2_bound : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)) (β r₁ r₂ : ℝ),
    (∀ (u : Idx d (sz.L n) (sz.W n)) (c : Zd d (sz.L n)), ∑ v ∈ twBlk n c, ‖X u v‖ ^ 2 ≤ β) →
    (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ ≤ r₁) → (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖ ≤ r₂) →
    ‖twLoop2X n A X C ρ a‖ ^ 2 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 * (β * r₁ * r₂) *
      (∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2)

theorem twFold2_bound_holds : twFold2_bound := by
  intro d sz n A X C ρ a β r₁ r₂ hβ hr₁ hr₂
  set u : ℝ := ((sz.W n : ℕ) : ℝ) ^ d with hu
  have hu0 : 0 < u := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hβ0 : 0 ≤ β := (Finset.sum_nonneg fun _ _ => by positivity).trans (hβ 0 a)
  have h2 := twFold2_holds d sz n A X C ρ a
  -- `F₁ ≤ β r₁ S_A`
  have hF1 : (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2) ≤ β * r₁ * ∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2 := by
    set Acol : Zd d (sz.L n) → ℝ := fun c₁ => ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ‖A x w‖ ^ 2 with hAcol
    have hAc0 : ∀ c₁, 0 ≤ Acol c₁ := fun c₁ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have hin : ∀ c₁ c₂ c₃ : Zd d (sz.L n), (∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2) ≤ β * Acol c₁ := by
      intro c₁ c₂ c₃
      calc (∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2)
          = ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ‖A x w‖ ^ 2 * ∑ w' ∈ twBlk n c₃, ‖X (twShift n c₂ w) w'‖ ^ 2 := by
            simp only [Finset.mul_sum]
        _ ≤ ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ‖A x w‖ ^ 2 * β :=
            Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun w _ =>
              mul_le_mul_of_nonneg_left (hβ _ _) (by positivity)
        _ = β * Acol c₁ := by
            simp only [hAcol, Finset.mul_sum]
            exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun w _ => by ring
    calc (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
            ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2)
        ≤ ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * (β * Acol c₁) :=
          Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ =>
            Finset.sum_le_sum fun c₄ _ => mul_le_mul_of_nonneg_left (hin c₁ c₂ c₃) (norm_nonneg _)
      _ = ∑ c₁, (β * Acol c₁) * ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ := by
          refine Finset.sum_congr rfl fun c₁ _ => ?_
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c₂ _ => Finset.sum_congr rfl fun c₃ _ =>
            Finset.sum_congr rfl fun c₄ _ => by ring
      _ ≤ ∑ c₁, (β * Acol c₁) * r₁ :=
          Finset.sum_le_sum fun c₁ _ => mul_le_mul_of_nonneg_left (hr₁ c₁) (mul_nonneg hβ0 (hAc0 c₁))
      _ = β * r₁ * ∑ c₁, Acol c₁ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c₁ _ => by ring
      _ = β * r₁ * ∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2 := by
          congr 1
          simp only [hAcol]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => TwistFold2_sum_blk n (fun v => ‖A x v‖ ^ 2)
  -- `F₂ ≤ W^d r₂ S_C`
  have hF2 : (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖C (twShift n c₄ w') x‖ ^ 2) ≤ u * r₂ * ∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2 := by
    set T : Zd d (sz.L n) → ℝ := fun c₄ => ∑ x ∈ twBlk n a, ∑ v ∈ twBlk n c₄, ‖C v x‖ ^ 2 with hT
    have hT0 : ∀ c₄, 0 ≤ T c₄ := fun c₄ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have hin : ∀ c₁ c₃ c₄ : Zd d (sz.L n), (∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖C (twShift n c₄ w') x‖ ^ 2) = u * T c₄ := by
      intro c₁ c₃ c₄
      calc (∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, ‖C (twShift n c₄ w') x‖ ^ 2)
          = ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ v ∈ twBlk n c₄, ‖C v x‖ ^ 2 :=
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun _ _ =>
              TwistFold2_sum_shift n c₃ c₄ (fun v => ‖C v x‖ ^ 2)
        _ = ∑ x ∈ twBlk n a, u * ∑ v ∈ twBlk n c₄, ‖C v x‖ ^ 2 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
        _ = u * T c₄ := by rw [hT, Finset.mul_sum]
    calc (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
            ‖C (twShift n c₄ w') x‖ ^ 2)
        = ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, u * (‖ρ c₁ c₂ c₃ c₄‖ * T c₄) :=
          Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => Finset.sum_congr rfl fun c₃ _ =>
            Finset.sum_congr rfl fun c₄ _ => by rw [hin c₁ c₃ c₄]; ring
      _ = u * ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * T c₄ := by simp only [Finset.mul_sum]
      _ = u * ∑ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖ * T c₄ := by
          rw [TwistFold2_sum4_comm (fun c₁ c₂ c₃ c₄ => ‖ρ c₁ c₂ c₃ c₄‖ * T c₄)]
      _ = u * ∑ c₄, (∑ c₁, ∑ c₂, ∑ c₃, ‖ρ c₁ c₂ c₃ c₄‖) * T c₄ := by
          congr 1
          refine Finset.sum_congr rfl fun c₄ _ => ?_
          simp only [Finset.sum_mul]
      _ ≤ u * ∑ c₄, r₂ * T c₄ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c₄ _ => mul_le_mul_of_nonneg_right (hr₂ c₄) (hT0 c₄))
            hu0.le
      _ = u * r₂ * ∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2 := by
          have hTsum : ∑ c₄, T c₄ = ∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2 := by
            simp only [hT]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun x _ => TwistFold2_sum_blk n (fun v => ‖C v x‖ ^ 2)
          rw [← Finset.mul_sum, hTsum, ← mul_assoc]
  have hF10 : 0 ≤ ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
        ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        by positivity)
  have hwu : (u⁻¹) * u = 1 := inv_mul_cancel₀ hu0.ne'
  calc ‖twLoop2X n A X C ρ a‖ ^ 2 ≤ (u⁻¹) ^ 6 * (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁,
          ∑ w' ∈ twBlk n c₃, ‖A x w‖ ^ 2 * ‖X (twShift n c₂ w) w'‖ ^ 2) * (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ *
          ∑ x ∈ twBlk n a, ∑ _w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, ‖C (twShift n c₄ w') x‖ ^ 2) := h2
    _ ≤ (u⁻¹) ^ 6 * (β * r₁ * ∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (u * r₂ * ∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2) := by
        have hpos : 0 ≤ (u⁻¹) ^ 6 := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hF1 hpos) hF2
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
            Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ =>
              Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))
          (mul_nonneg hpos (le_trans hF10 hF1))
    _ = (u⁻¹) ^ 5 * (β * r₁ * r₂) * (∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2) := by
        have : (u⁻¹) ^ 6 * u = (u⁻¹) ^ 5 := by
          calc (u⁻¹) ^ 6 * u = (u⁻¹) ^ 5 * (u⁻¹ * u) := by ring
            _ = (u⁻¹) ^ 5 := by rw [hwu, mul_one]
        calc (u⁻¹) ^ 6 * (β * r₁ * ∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (u * r₂ * ∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2)
            = ((u⁻¹) ^ 6 * u) * (β * r₁ * r₂) * (∑ x ∈ twBlk n a, ∑ v, ‖A x v‖ ^ 2) * (∑ x ∈ twBlk n a, ∑ v, ‖C v x‖ ^ 2) := by ring
          _ = _ := by rw [this]

/-! ## 5. Target 4: `twVec` -/

/-- `G(σ)^* = G(σ̄)` for a Hermitian `H` (copy of the private `BAExp14a_green_conj`, `Graph/BAExp14a.lean:321`). -/
theorem TwistFold2_green_conj {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian) (z : ℂ) :
    (green H z)ᴴ = green H ((starRingEnd ℂ) z) := by
  have hH' : Hᴴ = H := hH
  simp only [green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

/-- The resolvent identity in the `G^*G` form: `G - G^* = 2iη G^*G`, `η = Im z ≠ 0` (twin of the private `BAExp14a_ward_gram`). -/
theorem TwistFold2_gram_green {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    green H z - (green H z)ᴴ = (2 * (z.im : ℂ) * Complex.I) • ((green H z)ᴴ * green H z) := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH (z := (starRingEnd ℂ) z) (by simpa using hz)
  rw [TwistFold2_green_conj hH, green_sub_green_conj' hu hu']
  congr 1
  ring

/-- `Im⟨φ, Gφ⟩ = η ‖Gφ‖²` from `G - G^* = 2iη G^*G` (the quadratic form of the resolvent identity). -/
theorem TwistFold2_imQ {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (η : ℝ)
    (hG : G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G)) (φ : ι → ℂ) :
    (∑ u, star (φ u) * ∑ v, G u v * φ v).im = η * ∑ u, ‖∑ v, G u v * φ v‖ ^ 2 := by
  have hQ : ∑ u, star (φ u) * ∑ v, G u v * φ v = star φ ⬝ᵥ (G *ᵥ φ) := rfl
  have h := congrArg (fun A : Matrix ι ι ℂ => star φ ⬝ᵥ (A *ᵥ φ)) hG
  simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, ← Matrix.mulVec_mulVec] at h
  have hb : star φ ⬝ᵥ (G.conjTranspose *ᵥ φ) = star (star φ ⬝ᵥ (G *ᵥ φ)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, Matrix.star_dotProduct]
  have hc : star φ ⬝ᵥ (G.conjTranspose *ᵥ (G *ᵥ φ)) = ((∑ u, ‖∑ v, G u v * φ v‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun u _ => ?_
    exact Complex.conj_mul' _
  rw [hb, hc] at h
  rw [hQ]
  set Q := star φ ⬝ᵥ (G *ᵥ φ) with hQdef
  have h2 : (Q - star Q) = ((2 * Q.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.star_def]; exact Complex.sub_conj Q
  rw [h2, smul_eq_mul] at h
  have h3 : ((2 * Q.im : ℝ) : ℂ) = ((2 * η * ∑ u, ‖∑ v, G u v * φ v‖ ^ 2 : ℝ) : ℂ) := by
    refine mul_right_cancel₀ Complex.I_ne_zero ?_
    push_cast at h ⊢
    linear_combination h
  have h4 := Complex.ofReal_injective h3
  linarith

/-- **Target 4** (`twVec`, Fable §5; the vector twin of `twWard`), any finite index type: if `G - G^* = 2iη G^*G`, `η ≠ 0`, then
`‖(G - M)φ‖² ≤ 2η⁻¹ Im⟨φ, Gφ⟩ + 2‖Mφ‖²` (`‖Gφ‖² = η⁻¹ Im⟨φ, Gφ⟩`).  The `G^*G` form is the one `‖Gφ‖²` needs. -/
def twVec : Prop :=
  ∀ {ι : Type} [Fintype ι] (G M : Matrix ι ι ℂ) (η : ℝ), η ≠ 0 →
    G - G.conjTranspose = (2 * (η : ℂ) * Complex.I) • (G.conjTranspose * G) →
    ∀ φ : ι → ℂ, ∑ u, ‖∑ v, (G u v - M u v) * φ v‖ ^ 2 ≤
      2 * η⁻¹ * (∑ u, star (φ u) * ∑ v, G u v * φ v).im + 2 * ∑ u, ‖∑ v, M u v * φ v‖ ^ 2

theorem twVec_holds : twVec := by
  intro ι _ G M η hη hG φ
  rw [TwistFold2_imQ G η hG φ]
  have h2 : ∀ u, ‖∑ v, (G u v - M u v) * φ v‖ ^ 2 ≤ 2 * ‖∑ v, G u v * φ v‖ ^ 2 + 2 * ‖∑ v, M u v * φ v‖ ^ 2 := by
    intro u
    have e : ∑ v, (G u v - M u v) * φ v = ∑ v, G u v * φ v - ∑ v, M u v * φ v := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e]
    have h1 := norm_sub_le (∑ v, G u v * φ v) (∑ v, M u v * φ v)
    have h0 := norm_nonneg (∑ v, G u v * φ v - ∑ v, M u v * φ v)
    nlinarith [norm_nonneg (∑ v, G u v * φ v), norm_nonneg (∑ v, M u v * φ v),
      sq_nonneg (‖∑ v, G u v * φ v‖ - ‖∑ v, M u v * φ v‖)]
  calc ∑ u, ‖∑ v, (G u v - M u v) * φ v‖ ^ 2
      ≤ ∑ u, (2 * ‖∑ v, G u v * φ v‖ ^ 2 + 2 * ‖∑ v, M u v * φ v‖ ^ 2) := Finset.sum_le_sum fun u _ => h2 u
    _ = 2 * η⁻¹ * (η * ∑ u, ‖∑ v, G u v * φ v‖ ^ 2) + 2 * ∑ u, ‖∑ v, M u v * φ v‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        field_simp

/-! ## 6. Target 5: the BA facts of `M`, upper bounds only (0851 `:45`) -/

/-- The sum over the fine lattice of a function of the block coordinate, supported on one offset, is the sum over the blocks
(copy of the private `GreenSchur_fibre_sum`, `BA/GreenSchur.lean:161`). -/
private theorem TwistFold2_fibre_sum (d L W : ℕ) [NeZero L] [NeZero W] (x : Idx d L W) (f : Zd d L → ℝ) :
    ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ b : Zd d L, f b := by
  have h : ∑ y : Idx d L W, (if (split d L W x).2 = (split d L W y).2 then f (split d L W y).1 else 0) =
      ∑ y : Idx d L W, (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0)
        (splitEquiv d L W y) := rfl
  rw [h, Equiv.sum_comp (splitEquiv d L W) (fun p : Vtx d L W => if (split d L W x).2 = p.2 then f p.1 else 0),
    Fintype.sum_prod_type]
  simp

/-- **Target 5a** (`‖M^* e_x‖² ≤ 1`; `BAMfine_eq` and the `M`-Ward identity; an upper bound only, 0851 `:45`). -/
def twMrow_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
    ∀ x : Idx d (sz.L n) (sz.W n), ∑ v, ‖BAMfine sz lam0 E n x v‖ ^ 2 ≤ 1

theorem twMrow_le_holds : twMrow_le := by
  intro d sz lam0 E n h x
  have h1 : ∑ v, ‖BAMfine sz lam0 E n x v‖ ^ 2 =
      ∑ v : Idx d (sz.L n) (sz.W n), (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) v).2 then
        ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (split d (sz.L n) (sz.W n) x).1
          (split d (sz.L n) (sz.W n) v).1‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [BAMfine_eq sz lam0 E n h.1 x v]
    split_ifs <;> simp
  rw [h1, TwistFold2_fibre_sum d (sz.L n) (sz.W n) x
    (fun b => ‖BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) (split d (sz.L n) (sz.W n) x).1 b‖ ^ 2)]
  exact (BAMB_row_sq_real d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) h _).le

/-- **Target 5b** (`Π_b M^* M Π_b ≤ Π_b`, vector form, an upper bound only): `‖Mφ‖² ≤ ‖φ‖²` for `φ` supported in `[b]`. -/
def twMblk_le : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), BASelf d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) →
    ∀ (b : Zd d (sz.L n)) (φ : Idx d (sz.L n) (sz.W n) → ℂ), (∀ v, v ∉ twBlk n b → φ v = 0) →
      ∑ u, ‖∑ v, BAMfine sz lam0 E n u v * φ v‖ ^ 2 ≤ ∑ v, ‖φ v‖ ^ 2

theorem twMblk_le_holds : twMblk_le := by
  intro d sz lam0 E n h b φ hφ
  set MB := BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) with hMB
  -- `(Mφ)_u = M^{(B)}_{[u] b} φ_{(b, o(u))}`
  have hcol : ∀ u : Idx d (sz.L n) (sz.W n),
      ∑ v, BAMfine sz lam0 E n u v * φ v = MB (split d (sz.L n) (sz.W n) u).1 b * φ (twShift n b u) := by
    intro u
    rw [Finset.sum_eq_single (twShift n b u)]
    · rw [BAMfine_eq sz lam0 E n h.1 u (twShift n b u), TwistFold2_split_shift, ← hMB]
      simp
    · intro v _ hv
      by_cases hvb : v ∈ twBlk n b
      · have hne : (split d (sz.L n) (sz.W n) u).2 ≠ (split d (sz.L n) (sz.W n) v).2 := by
          intro heq
          apply hv
          apply split_injective d (sz.L n) (sz.W n)
          rw [TwistFold2_split_shift]
          exact Prod.ext ((TwistFold2_mem_blk n).1 hvb) heq.symm
        rw [BAMfine_eq sz lam0 E n h.1 u v]
        simp [hne]
      · rw [hφ v hvb, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hsplit : ∀ (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)),
      split d (sz.L n) (sz.W n) ((splitEquiv d (sz.L n) (sz.W n)).symm (c, o)) = (c, o) :=
    fun c o => (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply (c, o)
  have hwardcol : ∀ b' : Zd d (sz.L n), ∑ c, ‖MB c b'‖ ^ 2 = 1 := by
    intro b'
    rw [← BAMB_row_sq_real d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) h b']
    exact Finset.sum_congr rfl fun c _ => by rw [hMB, BAMB_symm d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n) c b']
  have hL : ∑ u, ‖∑ v, BAMfine sz lam0 E n u v * φ v‖ ^ 2 =
      ∑ o : Fin (sz.W n ^ d), ‖φ ((splitEquiv d (sz.L n) (sz.W n)).symm (b, o))‖ ^ 2 := by
    simp only [hcol, norm_mul, mul_pow]
    rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm, Fintype.sum_prod_type]
    have hsh : ∀ (c : Zd d (sz.L n)) (o : Fin (sz.W n ^ d)),
        twShift n b ((splitEquiv d (sz.L n) (sz.W n)).symm (c, o)) = (splitEquiv d (sz.L n) (sz.W n)).symm (b, o) := by
      intro c o
      unfold twShift
      rw [hsplit]
    simp only [hsplit, hsh]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.sum_mul, hwardcol, one_mul]
  have hR : ∑ v, ‖φ v‖ ^ 2 = ∑ o : Fin (sz.W n ^ d), ‖φ ((splitEquiv d (sz.L n) (sz.W n)).symm (b, o))‖ ^ 2 := by
    rw [← Equiv.sum_comp (splitEquiv d (sz.L n) (sz.W n)).symm, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · intro c _ hcb
      refine Finset.sum_eq_zero fun o _ => ?_
      have : (splitEquiv d (sz.L n) (sz.W n)).symm (c, o) ∉ twBlk n b := by
        rw [TwistFold2_mem_blk, hsplit]; exact hcb
      rw [hφ _ this]; simp
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hL, hR]

/-! ## 7. Target 6: S3A-C2 and S3A-C3 -/

/-- **Target 6a** (S3A-C2, `B_0 ≥ c` in the Lean frame): `(eq:WO)` gives eventually `W^d · W^{-d} B_{t,0} ≥ (𝔡^{-2} + 1)^{-1}` for
`0 ≤ t ≤ 1` (`Bctl` contains `W^{-d} (lam² + |1 - t|)⁻¹`; `BAFlow → Admissible → WO` is `h.1.2.2.2.2`). -/
def twB0_ge : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (𝔡 : ℝ), sz.WO 𝔡 → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ 1) →
    ∀ᶠ n in atTop, (𝔡⁻¹ ^ 2 + 1)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)

theorem twB0_ge_holds : twB0_ge := by
  intro d sz 𝔡 hWO t ht0 ht1
  filter_upwards [hWO] with n hn
  obtain ⟨hlo, hhi⟩ := hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hlo
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  have e : ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n) = Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
    unfold Sizes.Bctl
    rw [← mul_assoc, mul_inv_cancel₀ hWd.ne', one_mul]
  rw [e]
  unfold Bparam
  have h1 : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹ := inv_nonneg.mpr (by positivity)
  have h2 : (sz.lam n ^ 2 + |1 - t n|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = (sz.lam n ^ 2 + |1 - t n|)⁻¹ := by simp
  have hab : |1 - t n| ≤ 1 := abs_le.mpr ⟨by linarith [ht1 n], by linarith [ht0 n]⟩
  have hlam2 : sz.lam n ^ 2 ≤ 𝔡⁻¹ ^ 2 := pow_le_pow_left₀ hlam.le hhi 2
  have hpos : 0 < sz.lam n ^ 2 + |1 - t n| := by positivity
  have h3 : (𝔡⁻¹ ^ 2 + 1)⁻¹ ≤ (sz.lam n ^ 2 + |1 - t n|)⁻¹ := inv_anti₀ hpos (by linarith)
  rw [h2]
  linarith

/-- **Target 6b** (S3A-C3): `η_t = (1 - t) Im m ≥ κ (1 - t)` at the carrier (`etaOf`, `BAflow_real`; `GreenCond2.lean:321-345`). -/
def twEta_ge : Prop :=
  ∀ {d : ℕ} (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), t ≤ 1 → κ * (1 - t) ≤ (baFMz sz z).eta n t

theorem twEta_ge_holds : twEta_ge := by
  intro d κ ε 𝔠 𝔡 sz z h n t ht
  have hm : κ ≤ (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := (BAflow_real κ ε 𝔠 𝔡 sz z h n).2
  have e : (baFMz sz z).eta n t = (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
  rw [e, mul_comm κ]
  exact mul_le_mul_of_nonneg_left hm (by linarith)

/-! ## 8. Compiled nonempty instances of targets 1-6 -/

-- Target 1 (`twLoop2X`, `twLoop2X_trace`) at `sz0`, `n = 0`, `A = X = C = 1`: the value is `1 ≠ 0`
-- Target 2 (`twFold2`)
-- Target 3 (`twFold2_bound`): `β = W^d = 32768` (a block has `W^d` points), `r₁ = r₂ = 1`
-- Target 4 (`twVec`): the resolvent of `H = [[0,1],[1,0]]` at `z = i` (a nonzero Hermitian resolvent), `M = 1/2`, `φ = e₀`
-- Target 5a (`twMrow_le`) and 5b (`twMblk_le`) at `baFMz sz0 zSeq`, `n = 0`, `x = 0`, `φ = e₀`
-- Target 6a (`twB0_ge`) at `t ≡ 1/2`, `𝔡 = 1/10`, and a witness `n`
-- Target 6b (`twEta_ge`) at `n = 0`, `t = 1/2`
end Fold2

end RBM.BA

end
