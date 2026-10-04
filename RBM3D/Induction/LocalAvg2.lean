/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.LocalAvg1

/-!
# ST2-17 (ticket T2130, part 2): `(Gt_bound_flow)` and the pin `STLocalAvgOfL2`

The closing paragraph of Step 2 (`paper/tex/3_5_Loop_Hierarchy.tex:455–465`), second half:
`lem_GbEXP` (`stGbEXP_holds`, `(GiiGEX)`, `(GijGEX)`) together with `(eq:L2_decay)` gives
`(Gt_bound_flow)`, `|(G_u - M)_{xy}|² ≺ W^{-d} B_{u,|[x]-[y]|}` per time
(`stStep2LocalPT_of_L2decay`), and with part 1 (`stStep2AvgPT_of_L2decay`) the pin
`STLocalAvgOfL2` (`stLocalAvgOfL2_holds`, `3 ≤ d`: DECISIONS §36).

* The indicator `1(Ω(u, ε₀))` is removed because `Ω(u, ε₀) ⊇ {‖G_u - M‖_max ≤ N^{c/8}
  (W^{-d}B_{u,0})^{1/4}}` holds with high probability (weak law `(Gtmwc)`).
* The neighbour sums of `STgexRHS` (both charges): `𝓛_{(+,-),(a,b)} = 𝓛_{(-,+),(b,a)}` (trace
  cyclicity), then `(eq:L2_decay)` at `(b',a')`, `|[b'-a']| = |[a'-b']|`; the pairs `(a',b')`,
  `|a'-a| ≤ 1`, `|b'-b| ≤ 1` have `|a'-b'| ≥ |a-b| - 2`, and `B_{u,K'} ≤ 3^{d-2} B_{u,K}` for
  `K ≤ K' + 2` (`localAvg1_STWB_comp`).
* `W^{-d} 1_{|a-b| ≤ 1} ≤ 2^{d-2} cB⁻¹ W^{-d} B_{u,|a-b|}` from `cB W^{-d} ≤ W^{-d} B_{u,0}`
  (`localAvg1_STWB_ge`): the feared failure of the ticket does not occur.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 1. Deterministic toolbox (private) -/

section Toolbox

variable {d L W : ℕ} [NeZero L] [NeZero W]

private theorem la2_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem la2_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem la2_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

private theorem la2_zdist_le_one {y : ZMod L} (h : zdist L y ≤ 1) :
    y = 0 ∨ y = 1 ∨ y = -1 := by
  unfold zdist at h
  have hv : y.val < L := ZMod.val_lt y
  have hy : ((y.val : ℕ) : ZMod L) = y := ZMod.natCast_zmod_val y
  by_cases h1 : y.val ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h1'
    · left; rw [← hy, h0]; simp
    · right; left; rw [← hy, h1']; simp
  · right; right
    have h2 : L - y.val ≤ 1 := by omega
    have h3 : y.val = L - 1 := by omega
    rw [← hy, h3]
    have : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
    rw [Nat.cast_sub this]; simp

/-- The `L^∞` unit ball of `Z_L^d` has at most `3^d` points. -/
private theorem la2_card_ball_le (a : Zd d L) :
    (Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1).card ≤ 3 ^ d := by
  classical
  let T : Finset (ZMod L) := {0, 1, -1}
  have hT : T.card ≤ 3 := Finset.card_le_three
  have hsub : (Finset.univ.filter fun x : Zd d L => zdistInf d L (x - a) ≤ 1) ⊆
      (Fintype.piFinset fun _ : Fin d => T).image (fun f => f + a) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_image, Fintype.mem_piFinset]
    refine ⟨x - a, fun i => ?_, by simp⟩
    have h1 : zdist L ((x - a) i) ≤ 1 := by
      unfold zdistInf at hx
      exact le_trans (Finset.le_sup (f := fun j => zdist L ((x - a) j)) (Finset.mem_univ i)) hx
    rcases la2_zdist_le_one h1 with h | h | h <;> simp [T, h]
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => T).card := Finset.card_image_le
    _ = T.card ^ d := by simp [Fintype.card_piFinset]
    _ ≤ 3 ^ d := Nat.pow_le_pow_left hT d

/-- Trace cyclicity: `𝓛_{(-,+),(a,b)} = 𝓛_{(+,-),(b,a)}`. -/
private theorem la2_loopFine_mp_eq_pm (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)
    (a b : Zd d L) :
    loopFine d L W H z ![false, true] ![a, b] = loopFine d L W H z ![true, false] ![b, a] := by
  unfold loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  exact Matrix.trace_mul_comm _ _

end Toolbox

section Det

variable {d : ℕ} (sz : Sizes d)

/-- Trace cyclicity at the model level: `‖𝓛_{(+,-),(a,b)}‖ = ‖𝓛_{(-,+),(b,a)}‖`: this is how
the `(+,-)` charge of `STgexRHS` reduces to the `(-,+)` of `(eq:L2_decay)`. -/
private theorem la2_loop_pm (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) :
    sz.Lloop n E u ![true, false] ![a, b] ω = sz.Lloop n E u ![false, true] ![b, a] ω := by
  unfold Lloop
  rw [la2_loopFine_mp_eq_pm]

/-- **The right side of `(GijGEX)` is `≤ C · X · W^{-d} B_{u,|a-b|}`** when every
`𝓛^{(2)}_{(-,+),(a',b')}` is `≤ X W^{-d} B_{u,|a'-b'|}` (`X ≥ 1`) and `cB W^{-d} ≤ W^{-d}B_{u,0}`:
`C = 2 · 3^d · 3^d · 3^{d-2} + 2^{d-2} cB⁻¹` (two charges, two unit balls, the comparison
`B_{u,K'} ≤ 3^{d-2} B_{u,K}` for `K ≤ K'+2`, and the term `W^{-d} 1_{|a-b| ≤ 1}`). -/
theorem localAvg2_rhs_le (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) {X cB : ℝ}
    (hX : 1 ≤ X) (hcB : 0 < cB) (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u)
    (hL : ∀ a' b' : Zd d (sz.L n), ‖Lloop sz n E u ![false, true] ![a', b'] ω‖ ≤
      X * STWB sz n u (zdistInf d (sz.L n) (a' - b'))) :
    STgexRHS sz n E u ω a b ≤
      (2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * cB⁻¹) * X *
        STWB sz n u (zdistInf d (sz.L n) (a - b)) := by
  classical
  set r := zdistInf d (sz.L n) (a - b) with hr
  set T := STWB sz n u r with hT
  have hT0 : 0 ≤ T := by rw [hT]; unfold STWB Bparam; positivity
  have hX0 : 0 ≤ X := by linarith
  set M := X * 3 ^ (d - 2) * T with hM
  have hM0 : 0 ≤ M := by positivity
  -- the distance of a neighbouring pair
  have hdist : ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - a) ≤ 1 →
      zdistInf d (sz.L n) (b' - b) ≤ 1 → r ≤ zdistInf d (sz.L n) (a' - b') + 2 := by
    intro a' b' ha hb
    have e : a - b = (a' - b') + (-(a' - a)) + (b' - b) := by abel
    have h1 := la2_zdistInf_add_le (a' - b' + -(a' - a)) (b' - b)
    have h2 := la2_zdistInf_add_le (a' - b') (-(a' - a))
    rw [la2_zdistInf_neg] at h2
    rw [hr, e]
    omega
  have hLab : ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - a) ≤ 1 →
      zdistInf d (sz.L n) (b' - b) ≤ 1 →
      ‖Lloop sz n E u ![false, true] ![a', b'] ω‖ ≤ M := by
    intro a' b' ha hb
    refine (hL a' b').trans ?_
    have hc := localAvg1_STWB_comp sz n u (hdist a' b' ha hb)
    calc X * STWB sz n u (zdistInf d (sz.L n) (a' - b')) ≤ X * (3 ^ (d - 2) * T) :=
          mul_le_mul_of_nonneg_left hc hX0
      _ = M := by rw [hM]; ring
  have hLba : ∀ a' b' : Zd d (sz.L n), zdistInf d (sz.L n) (a' - a) ≤ 1 →
      zdistInf d (sz.L n) (b' - b) ≤ 1 →
      ‖Lloop sz n E u ![false, true] ![b', a'] ω‖ ≤ M := by
    intro a' b' ha hb
    refine (hL b' a').trans ?_
    have hneg : zdistInf d (sz.L n) (b' - a') = zdistInf d (sz.L n) (a' - b') := by
      rw [← neg_sub a' b', la2_zdistInf_neg]
    rw [hneg]
    have hc := localAvg1_STWB_comp sz n u (hdist a' b' ha hb)
    calc X * STWB sz n u (zdistInf d (sz.L n) (a' - b')) ≤ X * (3 ^ (d - 2) * T) :=
          mul_le_mul_of_nonneg_left hc hX0
      _ = M := by rw [hM]; ring
  -- the sum over a double unit ball of terms `≤ M`
  have hS : ∀ f : Zd d (sz.L n) → Zd d (sz.L n) → ℝ,
      (∀ a' b', zdistInf d (sz.L n) (a' - a) ≤ 1 → zdistInf d (sz.L n) (b' - b) ≤ 1 →
        f a' b' ≤ M) →
      ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
        ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
          f a' b' ≤ 3 ^ d * (3 ^ d * M) := by
    intro f hf
    have hAc := la2_card_ball_le (d := d) (L := sz.L n) a
    have hBc := la2_card_ball_le (d := d) (L := sz.L n) b
    have hAc' : (((Finset.univ.filter fun x : Zd d (sz.L n) => zdistInf d (sz.L n) (x - a) ≤ 1).card
        : ℕ) : ℝ) ≤ 3 ^ d := by exact_mod_cast hAc
    have hBc' : (((Finset.univ.filter fun x : Zd d (sz.L n) => zdistInf d (sz.L n) (x - b) ≤ 1).card
        : ℕ) : ℝ) ≤ 3 ^ d := by exact_mod_cast hBc
    calc _ ≤ ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
          ((Finset.univ.filter fun x : Zd d (sz.L n) => zdistInf d (sz.L n) (x - b) ≤ 1).card • M) :=
          Finset.sum_le_sum fun a' ha => Finset.sum_le_card_nsmul _ _ _ fun b' hb => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact hf a' b' ha hb
      _ = (Finset.univ.filter fun x : Zd d (sz.L n) => zdistInf d (sz.L n) (x - a) ≤ 1).card •
          ((Finset.univ.filter fun x : Zd d (sz.L n) => zdistInf d (sz.L n) (x - b) ≤ 1).card • M) :=
          Finset.sum_const _
      _ ≤ 3 ^ d * (3 ^ d * M) := by
          simp only [nsmul_eq_mul]
          gcongr
  -- the two charges
  have hne : (![true, false] : Fin 2 → Bool) ≠ ![false, true] := by decide
  unfold STgexRHS
  rw [Finset.sum_pair hne]
  have hS1 := hS (fun a' b' => ‖Lloop sz n E u ![true, false] ![a', b'] ω‖) fun a' b' ha hb => by
    simp only [la2_loop_pm sz n E u ω a' b']
    exact hLba a' b' ha hb
  have hS2 := hS (fun a' b' => ‖Lloop sz n E u ![false, true] ![a', b'] ω‖) hLab
  -- the term `W^{-d} 1_{|a-b| ≤ 1}`
  have hlast : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0) ≤
      2 ^ (d - 2) * cB⁻¹ * X * T := by
    by_cases hr1 : r ≤ 1
    · rw [← hr]
      simp only [hr1, ↓reduceIte, mul_one]
      have h1 := localAvg1_STWB_ge sz n u r
      have hr1' : ((r : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hr1
      have hpow : (((r : ℝ) + 1) ^ (d - 2)) ≤ 2 ^ (d - 2) := by
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      have hf : ((2 : ℝ) ^ (d - 2))⁻¹ ≤ (((r : ℝ) + 1) ^ (d - 2))⁻¹ :=
        inv_anti₀ (by positivity) hpow
      have hB : ((2 : ℝ) ^ (d - 2))⁻¹ * sz.Bctl n u ≤ T :=
        le_trans (mul_le_mul_of_nonneg_right hf (le_trans (by positivity) hlow)) h1
      have hB0 : 0 ≤ sz.Bctl n u := le_trans (by positivity) hlow
      have hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * sz.Bctl n u := by
        rw [le_inv_mul_iff₀ hcB]; linarith
      have h2 : sz.Bctl n u ≤ 2 ^ (d - 2) * T := by
        have h2p : (0 : ℝ) < 2 ^ (d - 2) := by positivity
        calc sz.Bctl n u = 2 ^ (d - 2) * (((2 : ℝ) ^ (d - 2))⁻¹ * sz.Bctl n u) := by
              field_simp
          _ ≤ 2 ^ (d - 2) * T := mul_le_mul_of_nonneg_left hB h2p.le
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB⁻¹ * sz.Bctl n u := hW
        _ ≤ cB⁻¹ * (2 ^ (d - 2) * T) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 ^ (d - 2) * cB⁻¹ * 1 * T := by ring
        _ ≤ 2 ^ (d - 2) * cB⁻¹ * X * T := by
            have : (0 : ℝ) ≤ 2 ^ (d - 2) * cB⁻¹ := by positivity
            nlinarith [mul_nonneg (mul_nonneg this (sub_nonneg.2 hX)) hT0]
    · rw [← hr]
      simp only [hr1, ↓reduceIte, mul_zero]; positivity
  have hsum := add_le_add (add_le_add hS1 hS2) hlast
  refine hsum.trans ?_
  have hK : (0 : ℝ) ≤ 2 ^ (d - 2) * cB⁻¹ := by positivity
  rw [hM]
  nlinarith [mul_nonneg hK (mul_nonneg hX0 hT0)]

/-- `STGM` off the diagonal is the resolvent entry. -/
private theorem la2_stGM_ne (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {x y : Idx d (sz.L n) (sz.W n)}
    (h : x ≠ y) : STGM sz n E τ ω x y = Gt sz n E τ true ω x y := by
  simp [STGM, h]

/-- **The pointwise bound `|(G_u - M)_{xy}|² ≤ Y · C X · W^{-d} B_{u,|[x]-[y]|}`** on the intersection
of the four events (`Ω`, `(GijGEX)`, `(GiiGEX)`, `(eq:L2_decay)`), the indicator being `1` on
`Ω`: off the diagonal by `(GijGEX)` and `localAvg2_rhs_le`, on the diagonal by `(GiiGEX)` and
`max_{a,b} ‖𝓛^{(2)}‖ ≤ X W^{-d} B_{u,0}`. -/
theorem localAvg2_entry_le (n : ℕ) (E u ε₀ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n))
    {X Y cB : ℝ} (hX : 1 ≤ X) (hY : 0 ≤ Y) (hcB : 0 < cB)
    (hlow : cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u)
    (hΩ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E u ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀))
    (hij : ∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2},
      STindMax sz n E u (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖Gt sz n E u true ω p.1.1 p.1.2‖ ^ 2 ≤
        Y * STgexRHS sz n E u ω (STblk sz n p.1.1) (STblk sz n p.1.2))
    (hii : ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      STindMax sz n E u (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖STGM sz n E u ω p.1 p.2‖ ^ 2 ≤
        Y * STmaxLoop2 sz n E u ω)
    (hL : ∀ a b : Zd d (sz.L n), ‖Lloop sz n E u ![false, true] ![a, b] ω‖ ≤
      X * STWB sz n u (zdistInf d (sz.L n) (a - b))) :
    ‖STGM sz n E u ω x y‖ ^ 2 ≤
      Y * ((2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * cB⁻¹) * X) *
        STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) := by
  have hind : STindMax sz n E u (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω = 1 := by
    unfold STindMax; simp [hΩ]
  have hX0 : 0 ≤ X := by linarith
  have hKc : (1 : ℝ) ≤ 2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * cB⁻¹ := by
    have h3d : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
    have h3p : (1 : ℝ) ≤ 3 ^ (d - 2) := one_le_pow₀ (by norm_num)
    have h2p : (0 : ℝ) ≤ 2 ^ (d - 2) * cB⁻¹ := by positivity
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 ^ d - 1) (by linarith : (0 : ℝ) ≤ 3 ^ d),
      mul_le_mul h3d h3d zero_le_one (by linarith : (0 : ℝ) ≤ 3 ^ d)]
  have hT0 : 0 ≤ STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) := by
    unfold STWB Bparam; positivity
  by_cases hxy : x = y
  · subst hxy
    have h1 := hii (x, x)
    rw [hind, one_mul] at h1
    have hmax := localAvg1_maxLoop2_le sz n E u ω hX0 hL
    have hz : zdistInf d (sz.L n) (STblk sz n x - STblk sz n x) = 0 := by
      rw [sub_self, la2_zdistInf_zero]
    rw [hz]
    have hB : sz.Bctl n u = STWB sz n u 0 := rfl
    rw [hz] at hT0
    calc ‖STGM sz n E u ω x x‖ ^ 2 ≤ Y * STmaxLoop2 sz n E u ω := h1
      _ ≤ Y * (X * STWB sz n u 0) := by
          rw [← hB]; exact mul_le_mul_of_nonneg_left hmax hY
      _ ≤ Y * ((2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * cB⁻¹) * X) *
            STWB sz n u 0 := by
          have hYX : 0 ≤ Y * X * STWB sz n u 0 := by positivity
          nlinarith [mul_nonneg hYX (by linarith : (0 : ℝ) ≤ 2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) +
            2 ^ (d - 2) * cB⁻¹ - 1)]
  · have h1 := hij ⟨(x, y), hxy⟩
    simp only at h1
    rw [hind, one_mul] at h1
    rw [la2_stGM_ne sz n E u ω hxy]
    have hrhs := localAvg2_rhs_le sz n E u ω (STblk sz n x) (STblk sz n y) hX hcB hlow hL
    calc ‖Gt sz n E u true ω x y‖ ^ 2 ≤ Y * STgexRHS sz n E u ω (STblk sz n x) (STblk sz n y) := h1
      _ ≤ Y * ((2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * cB⁻¹) * X *
            STWB sz n u (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y))) :=
          mul_le_mul_of_nonneg_left hrhs hY
      _ = _ := by ring

end Det

/-! ## 2. Item 3: `(Gt_bound_flow)` per time -/

section Item3

variable {d : ℕ}

/-- **`(Gt_bound_flow)` per time** (`3_5:455–460`): `|(G_u - M)_{xy}|² ≺ W^{-d} B_{u,|[x]-[y]|}`,
uniformly in `u ∈ [s,t]` (per time), from `(GiiGEX)`, `(GijGEX)` of `lem_GbEXP`
(`stGbEXP_holds`), `(eq:L2_decay)` (`STL2decayPT`) and the weak law `(Gtmwc)` (`STStep1Weak`, which
removes the indicator `1(Ω(u, ε₀))`).  At a time section `u` and `τ > 0` the four events (`Ω`,
`(GijGEX)`, `(GiiGEX)`, `(eq:L2_decay)`, the last three at the exponent `τ/3`) hold simultaneously
w.h.p.; on them `|(G_u - M)_{xy}|² ≤ N^{τ/3} (C N^{τ/3}) W^{-d} B_{u,|[x]-[y]|}` with the constant
`C = 2·3^d·3^d·3^{d-2} + 2^{d-2} cB⁻¹` of `localAvg2_rhs_le` (`localAvg2_entry_le`), which is
`≤ N^τ W^{-d} B_{u,|[x]-[y]|}` once `C ≤ N^{τ/3}`.  The hypothesis `3 ≤ d` is that of
`stGbEXP_holds` (DECISIONS §36). -/
theorem stStep2LocalPT_of_L2decay (hd : 3 ≤ d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {𝔠 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htl : ∀ n, t n ≤ lemT (z n))
    (hweak : STStep1Weak sz (STflowE z) s t) (hL2 : STL2decayPT sz (STflowE z) s t) :
    STStep2LocalPT sz (STflowE z) s t := by
  have hd0 : 0 < d := by omega
  obtain ⟨cB, c, hcB, hc, hdat⟩ := localAvg1_data hd0 hκ hε h𝔡 𝔠
  have hev := hdat sz z hflow t (fun n => (hs n).trans (hst n)) htl
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  have hε₀pos : 0 < min (1 / 2 : ℝ) (d * c / 8) :=
    lt_min (by norm_num) (by have : (0 : ℝ) < d := by exact_mod_cast hd0
                             positivity)
  set ε₀ := min (1 / 2 : ℝ) (d * c / 8) with hε₀
  refine Green.perTime_timeIcc_of_forall_seq sz.seqP sz.size hst
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (fun n => ⟨(0, 0)⟩)
    (fun n v q ω => ‖STGM sz n (STflowE z n) v ω q.1 q.2‖ ^ 2)
    (fun n v q _ => STWB sz n v (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2))) ?_
  intro u hu
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hs n).trans (hu n).1
  have hul : ∀ n, u n ≤ lemT (z n) := fun n => (hu n).2.trans (htl n)
  have hΩev : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (c / 8) * (sz.Bctl n (u n)) ^ (1 / 4 : ℝ) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
    filter_upwards [hev] with n hn
    obtain ⟨h1, h2⟩ := hn (u n) (hu0 n) (hu n).2
    exact (localAvg1_det sz n hd0 hcB hc (min_le_left _ _) (min_le_right _ _) h1 h2).1
  have hGii := (Green.stGbEXP_holds hd).1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀pos
  have hGij := (Green.stGbEXP_holds hd).2.1 κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow u hu0 hul ε₀ hε₀pos
  have hPrec : StochDomAt sz.seqP sz.size
      (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n q ω => ‖STGM sz n (STflowE z n) (u n) ω q.1 q.2‖ ^ 2)
      (fun n q _ => STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2))) := by
    refine localAvg1_stochDomAt_of_whp fun τ hτ => ?_
    have hτ3 : 0 < τ / 3 := by positivity
    refine ⟨_, (((localAvg1_whp_omega sz hweak hu hc hΩev).inter hsize
      (Prec.whp sz hGij hτ3)).inter hsize (Prec.whp sz hGii hτ3)).inter hsize
      (localAvg1_whp_L2 sz hL2 hu hτ3), ?_⟩
    filter_upwards [hev, hsize.eventually (eventually_le_rpow
      (2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) + 2 ^ (d - 2) * (cB⁻¹)) hτ3)] with n hn hKc ω hω q
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hω
    obtain ⟨hlow, -⟩ := hn (u n) (hu0 n) (hu n).2
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hX1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) :=
      Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ3.le
    have hX0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) := by linarith
    have h5 := localAvg2_entry_le sz n (STflowE z n) (u n) ε₀ ω q.1 q.2
      (X := ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) (Y := ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) hX1 hX0 hcB
      hlow h1 h2 h3 h4
    have hT0 : 0 ≤ STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)) := by
      unfold STWB Bparam; positivity
    refine h5.trans ?_
    have e : ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
        ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) = ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * ((2 * 3 ^ d * 3 ^ d * 3 ^ (d - 2) +
          2 ^ (d - 2) * cB⁻¹) * ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) *
        STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2))
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 3) * (((sz.size n : ℕ) : ℝ) ^ (τ / 3) *
          ((sz.size n : ℕ) : ℝ) ^ (τ / 3)) *
          STWB sz n (u n) (zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2)) := by
          gcongr
      _ = _ := by rw [e]
  exact localAvg1_perTime_of_stoch (hPrec.precomp_param
    (V := fun n => Unit × (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))) (fun n p => p.2))

end Item3

/-! ## 3. Item 4: the pin `STLocalAvgOfL2` -/

/-- **The closing paragraph of Step 2** (`3_5:455–465`; the pin `STLocalAvgOfL2` of
`Induction/Step2Defs.lean`): `(eq:L2_decay)` and `(Gtmwc)` give `(Gt_bound_flow)` and
`(Gt_avgbound_flow)` per time.  The hypothesis `3 ≤ d` comes from `stGbEXP_holds` (the T2126
`lem_GbEXP`, `(GbEXPHypV3)`), DECISIONS §36: both consumers (`ST_step2_of_pins`,
`ST_step2_of_pins'`) sit under `STStep2 d := 3 ≤ d → …`. -/
theorem stLocalAvgOfL2_holds {d : ℕ} (hd : 3 ≤ d) : STLocalAvgOfL2 d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htl hweak hL2
  exact ⟨stStep2LocalPT_of_L2decay hd hκ hε h𝔡 hflow hs hst htl hweak hL2,
    stStep2AvgPT_of_L2decay hd hκ hε h𝔡 hflow hs hst htl hweak hL2⟩

end RBM.Gauss.Sizes

/-! ## 4. Compiled nonempty instances at `d = 3`

As in `LocalAvg1.lean`: the merged flow instance `(sz0, z0)`, the window `s ≡ 0`, `t ≡ 1/16`; the
random hypotheses `STStep1Weak`, `STL2decayPT` stay hypotheses (other gates' outputs), and the other
pins of `ST_step2_of_pins'` stay hypotheses of the last example. -/

namespace RBM.Gauss.LocalAvg2Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2IterateInst RBM.Gauss.Step2DefsInst Filter

/-- **Item 3 at the data**: `(Gt_bound_flow)` per time on `[0, 1/16]`. -/
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2LocalPT sz0 (STflowE z0) sInst tInst :=
  stStep2LocalPT_of_L2decay (by norm_num : 3 ≤ 3) (by norm_num : (0 : ℝ) < 1 / 10)
    (by norm_num : (0 : ℝ) < 1 / 10) (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 hs0 hst htT hweak hL2

/-- **Item 4 at the data**: the pin `STLocalAvgOfL2 3` applied at `(sz0, z0, s ≡ 0, t ≡ 1/16)`. -/
example (hweak : STStep1Weak sz0 (STflowE z0) sInst tInst)
    (hL2 : STL2decayPT sz0 (STflowE z0) sInst tInst) :
    STStep2LocalPT sz0 (STflowE z0) sInst tInst ∧ STStep2AvgPT sz0 (STflowE z0) sInst tInst :=
  stLocalAvgOfL2_holds (by norm_num : 3 ≤ 3) (1 / 10) (1 / 10) (1 / 10) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 sInst tInst hs0 hst htT hweak hL2

/-- **`ST_step2_of_pins'` with `stLocalAvgOfL2_holds`** at `d = 3`: the pin `STLocalAvgOfL2` is no
longer a hypothesis of Step 2 (the other pins stay hypotheses). -/
example (hNew : STNewKLK 3) (hLWT : STLWT 3) (hEMe : STEMn2Exp 3) (hMart : STGridMart 3)
    (hOpt : STOptL2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) :=
  inst_step2 (ST_step2_of_pins' hNew hLWT hEMe hMart hOpt (stLocalAvgOfL2_holds (by norm_num)))

/-- The consumer is under `3 ≤ d` for every `d` (DECISIONS §36 (ii)): `STStep2 d := 3 ≤ d → …`. -/
example {d : ℕ} (hNew : STNewKLK d) (hLWT : STLWT d) (hEMe : STEMn2Exp d) (hMart : STGridMart d)
    (hOpt : STOptL2 d) : STStep2 d := fun hd3 =>
  ST_step2_of_pins' hNew hLWT hEMe hMart hOpt (stLocalAvgOfL2_holds hd3) hd3

end RBM.Gauss.LocalAvg2Inst
