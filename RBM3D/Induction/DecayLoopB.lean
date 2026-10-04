/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.DecayLoopA
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.HierAlgebra
import RBM3D.Induction.Split

/-!
# S3-07b (ticket T2135): decay through cuts and the label decay of the `ℰ`-terms

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`: `Def_decay` (`3_5:1115`),
`lem_decayLoop` (`3_5:1126`), `lem:SEforLn` (`3_5:1017-1065`).  The source is the `d = 2` file
`RBM2D/Induction/BcalEDecay.lean` (read at `c9a24cf`, 1314 lines there) with the replacements
`Z2 L → Zd d L`, `zdist2 → zdistInf`, window `(2R+1)^d`, `Σ_{a,b} |S^{(B)}_{ab}| = L^d`,
`W^2 → W^d`, `SB L → SB d L g`, `LLf, LKf, Kcal → STLI, STLKI, STKI`.

* §1-§7 (`RBM.Ind`, deterministic, target 1): `LoopDecay`, the anchors of `cutGlueL`/`cutGlueR`/
  `cutGlue`, `far_cutGlueL_or_far_cutGlueR`, the window sums `norm_sum_SB_le_left/right` (for the
  merged `S = SB d L g`), `glueTerm`, `norm_glueTerm_le_of_far`, the `STeeLoop` label lemmas, and
  the four deterministic bounds of the `ℰ`-terms of a loop with two far labels.
* §8 (`RBM.Gauss.Sizes`, target 3): `STDecayLoopU` (`STDecayLoopPT` with `Prec` in place of
  `PrecPT`, uniform over `u ∈ [s_n, t_n]`) and `stDecayLoopU_of_step2` from the uniform `STGdecayW`.
* §9 (target 2): `stEtermDecay`, `STEKDecay` for the four `ℰ`-terms of `lem:SEforLn`.
* §10: the compiled nonempty instances at `d = 3`.

Every helper that the ticket does not pin is `private` or prefixed `DecayLoopB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Decay of loop functions (`Def_decay`, `3_5:1115`) -/

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss

section Def

variable (d L : ℕ)

/-- `F` has `(R, δ)` decay on loops of length `≤ N`: `‖F J‖ ≤ δ` as soon as two labels of the
well-formed loop `J` are at `zdistInf`-distance `≥ R` (the paper's `l^∞` distance, T2002b).
Port of RBM2D `LoopDecay` (`BcalEDecay.lean:74` at `c9a24cf`). -/
def LoopDecay (N : ℕ) (R δ : ℝ) (F : LoopIdx (Zd d L) → ℂ) : Prop :=
  ∀ J : LoopIdx (Zd d L), J.WF → J.length ≤ N → ∀ x ∈ J.a, ∀ y ∈ J.a,
    R ≤ (zdistInf d L (x - y) : ℝ) → ‖F J‖ ≤ δ

variable {d L}

theorem LoopDecay.mono {N N' : ℕ} {R R' δ δ' : ℝ} {F : LoopIdx (Zd d L) → ℂ}
    (h : LoopDecay d L N R δ F) (hN : N' ≤ N) (hR : R ≤ R') (hδ : δ ≤ δ') :
    LoopDecay d L N' R' δ' F :=
  fun J hJ hJN x hx y hy hxy => (h J hJ (hJN.trans hN) x hx y hy (hR.trans hxy)).trans hδ

/-- The difference of two decaying loop functions decays. -/
theorem LoopDecay.sub {N : ℕ} {R δ δ' : ℝ} {F G : LoopIdx (Zd d L) → ℂ}
    (hF : LoopDecay d L N R δ F) (hG : LoopDecay d L N R δ' G) :
    LoopDecay d L N R (δ + δ') (F - G) := fun J hJ hJN x hx y hy hxy =>
  (norm_sub_le _ _).trans (add_le_add (hF J hJ hJN x hx y hy hxy) (hG J hJ hJN x hx y hy hxy))

end Def

/-! ## 2. Anchors: labels that survive cutting and gluing -/

section Anchor

variable {α : Type*} (x : LoopIdx α) (b : α) {k l : ℕ}

theorem mem_cutGlueL (k l : ℕ) : b ∈ (x.cutGlueL k l b).a := by
  simp [LoopIdx.cutGlueL]

theorem mem_cutGlueR (k l : ℕ) : b ∈ (x.cutGlueR k l b).a := by
  simp [LoopIdx.cutGlueR]

theorem mem_cutGlue (k : ℕ) : b ∈ (x.cutGlue k b).a := by
  simp [LoopIdx.cutGlue]

/-- Every label of the loop survives `cutGlue` (the new label is only inserted). -/
theorem mem_cutGlue_of_mem (k : ℕ) {c : α} (hc : c ∈ x.a) : c ∈ (x.cutGlue k b).a := by
  simp only [LoopIdx.cutGlue, List.mem_append, List.mem_cons]
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append] at hc
  tauto

/-- The left loop of the cut `(k, l)` keeps the label `a_l`, whatever the glued label is. -/
theorem exists_anchor_cutGlueL (hl1 : 1 ≤ l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueL k l b).a := by
  have h : 0 < (x.a.drop (l - 1)).length := by
    simp only [List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨(x.a.drop (l - 1))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueL, List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr (List.getElem_mem h))

/-- The right loop of the cut `(k, l)` keeps the label `a_k`. -/
theorem exists_anchor_cutGlueR (hk1 : 1 ≤ k) (hkl : k < l) (hl : l ≤ x.length) :
    ∃ c : α, ∀ b : α, c ∈ (x.cutGlueR k l b).a := by
  have h : 0 < ((x.a.drop (k - 1)).take (l - k)).length := by
    simp only [List.length_take, List.length_drop]; simp only [LoopIdx.length] at hl; omega
  refine ⟨((x.a.drop (k - 1)).take (l - k))[0], fun b => ?_⟩
  simp only [LoopIdx.cutGlueR, List.mem_append]
  exact Or.inl (List.getElem_mem h)

/-- Every label of the loop goes to the left or to the right loop of the cut `(k, l)`. -/
theorem mem_cutGlueL_or_mem_cutGlueR (hk : 1 ≤ k) (hkl : k < l) {c : α} (hc : c ∈ x.a) :
    (∀ b, c ∈ (x.cutGlueL k l b).a) ∨ (∀ b, c ∈ (x.cutGlueR k l b).a) := by
  rw [← List.take_append_drop (k - 1) x.a, List.mem_append,
    ← List.take_append_drop (l - k) (x.a.drop (k - 1)), List.mem_append, List.drop_drop] at hc
  have e : k - 1 + (l - k) = l - 1 := by omega
  rw [e] at hc
  rcases hc with h | h | h
  · left; intro b; simp [LoopIdx.cutGlueL, h]
  · right; intro b; simp [LoopIdx.cutGlueR, h]
  · left; intro b; simp [LoopIdx.cutGlueL, h]

/-- `cutGlue k b` has length `n + 1` for `1 ≤ k ≤ n` and a well-formed loop (the merged
`RBM.Loop.LoopIdx` has no such lemma for the single-edge cut). -/
theorem DecayLoopB_length_cutGlue (hk : 1 ≤ k) (hkn : k ≤ x.length) (hx : x.WF) :
    (x.cutGlue k b).length = x.length + 1 := by
  simp only [LoopIdx.length, LoopIdx.WF] at hkn hx ⊢
  simp only [LoopIdx.cutGlue, List.length_append, List.length_take, List.length_cons,
    List.length_drop]
  omega

theorem DecayLoopB_wf_cutGlue (hk : 1 ≤ k) (hkn : k ≤ x.length) (hx : x.WF) :
    (x.cutGlue k b).WF := by
  simp only [LoopIdx.length, LoopIdx.WF] at hkn hx ⊢
  simp only [LoopIdx.cutGlue, List.length_append, List.length_take, List.length_cons,
    List.length_drop]
  omega

end Anchor

/-! ## 3. The cut spread "up to one block" -/

section Spread

variable {d L : ℕ} [NeZero L]

private theorem DecayLoopB_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem DecayLoopB_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

private theorem DecayLoopB_zdistInf_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, DecayLoopB_zdistInf_neg]

private theorem DecayLoopB_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := DecayLoopB_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

/-- **The far pair after one cut** (the pointwise content of RBM1D `norm_mul_le_of_far_aux` in `d`
dimensions, RBM2D `far_cutGlueL_or_far_cutGlueR`, `BcalEDecay.lean:179` at `c9a24cf`): if two labels
of `I` are at `l^∞` distance `≥ 2R + 1` and the glued labels satisfy `|α - β|_∞ ≤ 1`, then the left
piece `I.cutGlueL k l α` or the right piece `I.cutGlueR k l β` has two labels at distance `≥ R`
(the triangle inequality of `zdistInf` along `x → α → β → y`). -/
theorem far_cutGlueL_or_far_cutGlueR (I : LoopIdx (Zd d L)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    {R : ℝ} {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) {α β : Zd d L}
    (hab : zdistInf d L (α - β) ≤ 1) :
    (∃ x' ∈ (I.cutGlueL k l α).a, ∃ y' ∈ (I.cutGlueL k l α).a,
        R ≤ (zdistInf d L (x' - y') : ℝ)) ∨
      (∃ x' ∈ (I.cutGlueR k l β).a, ∃ y' ∈ (I.cutGlueR k l β).a,
        R ≤ (zdistInf d L (x' - y') : ℝ)) := by
  have hR : R ≤ (zdistInf d L (x - y) : ℝ) := by
    have h0 : (0 : ℝ) ≤ (zdistInf d L (x - y) : ℝ) := Nat.cast_nonneg _
    rcases le_or_gt R 0 with h | h
    · linarith
    · linarith
  -- the triangle inequality through the glued labels
  have key : ∀ x y : Zd d L, 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ) →
      R ≤ (zdistInf d L (x - α) : ℝ) ∨ R ≤ (zdistInf d L (β - y) : ℝ) := by
    intro x y hxy
    by_contra hcon
    push Not at hcon
    have t1 := DecayLoopB_zdistInf_add_le (x - α) (α - β)
    have t2 := DecayLoopB_zdistInf_add_le (x - α + (α - β)) (β - y)
    have e : x - α + (α - β) + (β - y) = x - y := by abel
    rw [e] at t2
    have : (zdistInf d L (x - y) : ℝ) ≤
        zdistInf d L (x - α) + zdistInf d L (α - β) + zdistInf d L (β - y) := by
      exact_mod_cast t2.trans (Nat.add_le_add_right t1 _)
    have hab' : (zdistInf d L (α - β) : ℝ) ≤ 1 := by exact_mod_cast hab
    linarith
  rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hx with hxL | hxR <;>
    rcases mem_cutGlueL_or_mem_cutGlueR I hk hkl hy with hyL | hyR
  · exact Or.inl ⟨x, hxL α, y, hyL α, hR⟩
  · rcases key x y hxy with h | h
    · exact Or.inl ⟨x, hxL α, α, mem_cutGlueL I α k l, h⟩
    · exact Or.inr ⟨β, mem_cutGlueR I β k l, y, hyR β, h⟩
  · have hyx : 2 * R + 1 ≤ (zdistInf d L (y - x) : ℝ) := by
      rwa [DecayLoopB_zdistInf_comm]
    rcases key y x hyx with h | h
    · exact Or.inl ⟨y, hyL α, α, mem_cutGlueL I α k l, h⟩
    · exact Or.inr ⟨β, mem_cutGlueR I β k l, x, hxR β, h⟩
  · exact Or.inr ⟨x, hxR β, y, hyR β, hR⟩

end Spread

/-! ## 4. The window sums (`S = SB d L g`, windows `(2R+1)^d`) -/

section Window

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `Σ_{a,b} |S^{(B)}_{ab}| = L^d` (`d`-dimensional form of `Σ = L²`). -/
theorem DecayLoopB_sum_sum_norm_SB (hL : 3 ≤ L) :
    ∑ a : Zd d L, ∑ b : Zd d L, ‖SB d L g a b‖ = (L : ℝ) ^ d := by
  simp only [sum_norm_SB_row d L g hL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [card_Zd]; push_cast; rfl

variable {d L}

/-- The cycle `Z_L` has at most `2r + 1` points at distance `≤ r` from any point. -/
private theorem DecayLoopB_card_ball_one (r : ℕ) (c : ZMod L) :
    (Finset.univ.filter fun u : ZMod L => zdist L (c - u) ≤ r).card ≤ 2 * r + 1 := by
  classical
  have h1 : (Finset.univ.filter fun u : ZMod L => zdist L (c - u) ≤ r).card
      = (Finset.univ.filter fun w : ZMod L => zdist L w ≤ r).card := by
    refine Finset.card_bij (fun u _ => c - u) ?_ ?_ ?_
    · intro u hu; simpa using hu
    · intro u _ v _ h; simpa using h
    · intro w hw; exact ⟨c - w, by simpa using hw, by simp⟩
  rw [h1]
  have h2 : (Finset.univ.filter fun w : ZMod L => zdist L w ≤ r).card ≤
      (Finset.range (r + 1) ∪ Finset.Ico (L - r) L).card := by
    refine Finset.card_le_card_of_injOn (fun w : ZMod L => w.val) ?_ ?_
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
      have hv := ZMod.val_lt w
      simp only [zdist] at hw
      simp only [Finset.coe_union, Finset.coe_range, Finset.coe_Ico, Set.mem_union, Set.mem_Iio,
        Set.mem_Ico]
      omega
    · intro u _ v _ h; exact ZMod.val_injective L h
  refine h2.trans ((Finset.card_union_le _ _).trans ?_)
  rw [Finset.card_range, Nat.card_Ico]
  omega

/-- The `l^∞` ball of radius `r` about `c` in `Z_L^d` has at most `(2r+1)^d` points. -/
private theorem DecayLoopB_card_ball_nat (r : ℕ) (c : Zd d L) :
    (Finset.univ.filter fun u : Zd d L => zdistInf d L (c - u) ≤ r).card ≤ (2 * r + 1) ^ d := by
  classical
  have hsub : (Finset.univ.filter fun u : Zd d L => zdistInf d L (c - u) ≤ r) ⊆
      Fintype.piFinset (fun i : Fin d => Finset.univ.filter fun u : ZMod L => zdist L (c i - u) ≤ r) := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    refine le_trans ?_ hu.2
    exact Finset.le_sup (f := fun j => zdist L ((c - u) j)) (Finset.mem_univ i)
  refine (Finset.card_le_card hsub).trans ?_
  rw [Fintype.card_piFinset]
  calc ∏ i : Fin d, (Finset.univ.filter fun u : ZMod L => zdist L (c i - u) ≤ r).card
      ≤ ∏ _i : Fin d, (2 * r + 1) :=
        Finset.prod_le_prod fun i _ => DecayLoopB_card_ball_one r (c i)
    _ = (2 * r + 1) ^ d := by simp

/-- The ball count with a real radius: `#{u : |c - u|_∞ ≤ R} ≤ (2R+1)^d` (`R ≥ 0`). -/
theorem DecayLoopB_card_ball (c : Zd d L) {R : ℝ} (hR : 0 ≤ R) :
    (((Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ R).card : ℕ) : ℝ) ≤
      (2 * R + 1) ^ d := by
  classical
  have hfl : (Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ R) =
      Finset.univ.filter fun u : Zd d L => zdistInf d L (c - u) ≤ ⌊R⌋₊ := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Nat.le_floor_iff hR).symm
  rw [hfl]
  have h1 := DecayLoopB_card_ball_nat (d := d) (L := L) ⌊R⌋₊ c
  have h2 : (((2 * ⌊R⌋₊ + 1) ^ d : ℕ) : ℝ) ≤ (2 * R + 1) ^ d := by
    push_cast
    have : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR
    gcongr
  exact (Nat.cast_le.mpr h1).trans h2

/-- **The window sum, decay in the first variable** (RBM2D `norm_sum_SB_le_left`,
`BcalEDecay.lean:237` at `c9a24cf`, `d = 2`; RBM1D `Hierarchy/Decay.lean:164`): for `S = SB d L g`, if
`‖F_{ab}‖ ≤ M` and `‖F_{ab}‖ ≤ δ` once `|a - c|_∞ ≥ R`, then
`‖Σ_{a,b} S^{(B)}_{ab} F_{ab}‖ ≤ (2R+1)^d M + L^d δ`. -/
theorem norm_sum_SB_le_left (hL : 3 ≤ L) {R M δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (c : Zd d L)
    (F : Zd d L → Zd d L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, R ≤ (zdistInf d L (a - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : Zd d L, ∑ b : Zd d L, SB d L g a b * F a b‖ ≤ (2 * R + 1) ^ d * M + (L : ℝ) ^ d * δ := by
  classical
  have hM : 0 ≤ M := (norm_nonneg _).trans (hF 0 0)
  set win : Zd d L → ℝ := fun a => if (zdistInf d L (c - a) : ℝ) ≤ R then 1 else 0 with hwin
  have hrow : ∀ a, ∑ b : Zd d L, ‖SB d L g a b * F a b‖ ≤ win a * M + δ := by
    intro a
    by_cases h : (zdistInf d L (a - c) : ℝ) < R
    · have hw : win a = 1 := by
        simp [hwin, DecayLoopB_zdistInf_comm c a, h.le]
      calc ∑ b : Zd d L, ‖SB d L g a b * F a b‖ ≤ ∑ b : Zd d L, ‖SB d L g a b‖ * M :=
            Finset.sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hF a b) (norm_nonneg _)
        _ = M := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]
        _ ≤ win a * M + δ := by rw [hw]; linarith
    · push Not at h
      calc ∑ b : Zd d L, ‖SB d L g a b * F a b‖ ≤ ∑ b : Zd d L, ‖SB d L g a b‖ * δ :=
            Finset.sum_le_sum fun b _ => by
              rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hFd a b h) (norm_nonneg _)
        _ = δ := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL, one_mul]
        _ ≤ win a * M + δ := by
          have : 0 ≤ win a := by simp only [hwin]; split_ifs <;> norm_num
          nlinarith
  have hcount : ∑ a : Zd d L, win a ≤ (2 * R + 1) ^ d := by
    have e : ∑ a : Zd d L, win a =
        (((Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ R).card : ℕ) : ℝ) := by
      simp only [hwin]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [e]
    exact DecayLoopB_card_ball c hR
  calc ‖∑ a : Zd d L, ∑ b : Zd d L, SB d L g a b * F a b‖
      ≤ ∑ a : Zd d L, ∑ b : Zd d L, ‖SB d L g a b * F a b‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ a : Zd d L, (win a * M + δ) := Finset.sum_le_sum fun a _ => hrow a
    _ = (∑ a : Zd d L, win a) * M + (L : ℝ) ^ d * δ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, card_Zd]
        push_cast; rfl
    _ ≤ (2 * R + 1) ^ d * M + (L : ℝ) ^ d * δ := by gcongr

/-- **The window sum, decay in the second variable** (by the symmetry of `S^{(B)}`). -/
theorem norm_sum_SB_le_right (hL : 3 ≤ L) {R M δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (c : Zd d L)
    (F : Zd d L → Zd d L → ℂ) (hF : ∀ a b, ‖F a b‖ ≤ M)
    (hFd : ∀ a b, R ≤ (zdistInf d L (b - c) : ℝ) → ‖F a b‖ ≤ δ) :
    ‖∑ a : Zd d L, ∑ b : Zd d L, SB d L g a b * F a b‖ ≤ (2 * R + 1) ^ d * M + (L : ℝ) ^ d * δ := by
  have e : ∑ a : Zd d L, ∑ b : Zd d L, SB d L g a b * F a b
      = ∑ b : Zd d L, ∑ a : Zd d L, SB d L g b a * F a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [show SB d L g a b = SB d L g b a from congrFun (congrFun (SB_transpose d L g) b) a]
  rw [e]
  exact norm_sum_SB_le_left (g := g) hL hR hδ c (fun b a => F a b) (fun b a => hF a b)
    (fun b a h => hFd a b h)

end Window

/-! ## 5. One cut of a far loop -/

section Glue

variable {d L : ℕ} [NeZero L] (g : ℝ)

/-- The `(k, l)` summand `Σ_{a,b} F(I.cutGlueL k l a) S^{(B)}_{ab} G(I.cutGlueR k l b)` of the
two-edge cut terms (`S = SB d L g`).  Port of RBM1D `Decay.glueTerm`, RBM2D `glueTerm`
(`BcalEDecay.lean:302` at `c9a24cf`). -/
def glueTerm (F G : LoopIdx (Zd d L) → ℂ) (I : LoopIdx (Zd d L)) (k l : ℕ) : ℂ :=
  ∑ a : Zd d L, ∑ b : Zd d L, F (I.cutGlueL k l a) * SB d L g a b * G (I.cutGlueR k l b)

/-- `S^{(B)}_{ab}` vanishes unless `|a - b|_∞ ≤ 1` (it is supported on `zdistD ≤ 1 ` and
`zdistInf ≤ zdistD`). -/
private theorem DecayLoopB_SB_eq_zero {a b : Zd d L} (h : ¬ zdistInf d L (a - b) ≤ 1) :
    SB d L g a b = 0 :=
  SB_apply_eq_zero_of_one_lt (lt_of_not_ge h |>.trans_le (zdistInf_le_zdistD d L _))

variable {g}

/-- **One cut of a far loop, pointwise** (RBM2D `norm_mul_le_of_far_aux`, two decay levels): on the
support `|a - b|_∞ ≤ 1` of `S^{(B)}`, one factor of a cut of a far loop is small. -/
theorem DecayLoopB_norm_mul_le_of_far_aux {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)} (hI : I.WF)
    {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ))
    {a b : Zd d L} (hab : zdistInf d L (a - b) ≤ 1) :
    ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG + MF * δG := by
  have hMF : 0 ≤ MF := (norm_nonneg _).trans (hF a)
  have hMG : 0 ≤ MG := (norm_nonneg _).trans (hG b)
  rcases far_cutGlueL_or_far_cutGlueR I hk hkl hx hy hxy hab with
    ⟨x', hx', y', hy', h⟩ | ⟨x', hx', y', hy', h⟩
  · have h1 := hFd _ (LoopIdx.wf_cutGlueL I a hI hk hkl hl)
      (LoopIdx.length_cutGlueL_le I a hk hkl hl) x' hx' y' hy' h
    have h2 := hG b
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ δF * MG :=
      mul_le_mul h1 h2 (norm_nonneg _) hδF
    nlinarith [mul_nonneg hMF hδG]
  · have h1 := hGd _ (LoopIdx.wf_cutGlueR I b hI hk hkl hl)
      (LoopIdx.length_cutGlueR_le I b hk hkl hl) x' hx' y' hy' h
    have h2 := hF a
    have : ‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖ ≤ MF * δG :=
      mul_le_mul h2 h1 (norm_nonneg _) hMF
    nlinarith [mul_nonneg hδF hMG]

/-- **One cut of a far loop, summed norms**: `Σ_{a,b} ‖F(L_a)‖ ‖S_{ab}‖ ‖G(R_b)‖ ≤
L^d (δ_F M_G + M_F δ_G)` for a cut of a loop with two labels at distance `≥ 2R + 1`. -/
theorem DecayLoopB_sum_norm_glue_le_of_far (hL : 3 ≤ L) {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) :
    ∑ a : Zd d L, ∑ b : Zd d L, ‖F (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ *
        ‖G (I.cutGlueR k l b)‖ ≤ (L : ℝ) ^ d * (δF * MG + MF * δG) := by
  calc ∑ a : Zd d L, ∑ b : Zd d L, ‖F (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ *
        ‖G (I.cutGlueR k l b)‖
      ≤ ∑ a : Zd d L, ∑ b : Zd d L, ‖SB d L g a b‖ * (δF * MG + MF * δG) := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
        by_cases hab : zdistInf d L (a - b) ≤ 1
        · have := DecayLoopB_norm_mul_le_of_far_aux hI hk hkl hl hδF hδG hFd hGd hF hG hx hy hxy hab
          calc ‖F (I.cutGlueL k l a)‖ * ‖SB d L g a b‖ * ‖G (I.cutGlueR k l b)‖
              = ‖SB d L g a b‖ * (‖F (I.cutGlueL k l a)‖ * ‖G (I.cutGlueR k l b)‖) := by ring
            _ ≤ ‖SB d L g a b‖ * (δF * MG + MF * δG) :=
                mul_le_mul_of_nonneg_left this (norm_nonneg _)
        · rw [DecayLoopB_SB_eq_zero g hab]; simp
    _ = (L : ℝ) ^ d * (δF * MG + MF * δG) := by
        simp only [← Finset.sum_mul, DecayLoopB_sum_sum_norm_SB d L g hL]

/-- **One cut of a far loop** (RBM2D `norm_glueTerm_le_of_far`, `d = 2`; RBM1D `Hierarchy/Decay.lean:368`): if
two labels of the loop are at distance `≥ 2R + 1` and both factors have `R`-decay, the `(k, l)`
summand is `≤ L^d (δ_F M_G + M_F δ_G)`. -/
theorem norm_glueTerm_le_of_far (hL : 3 ≤ L) {F G : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)}
    (hI : I.WF) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l) (hl : l ≤ I.length) {R δF δG MF MG : ℝ}
    (hδF : 0 ≤ δF) (hδG : 0 ≤ δG)
    (hFd : LoopDecay d L I.length R δF F) (hGd : LoopDecay d L I.length R δG G)
    (hF : ∀ a, ‖F (I.cutGlueL k l a)‖ ≤ MF) (hG : ∀ b, ‖G (I.cutGlueR k l b)‖ ≤ MG)
    {x y : Zd d L} (hx : x ∈ I.a) (hy : y ∈ I.a)
    (hxy : 2 * R + 1 ≤ (zdistInf d L (x - y) : ℝ)) :
    ‖glueTerm g F G I k l‖ ≤ (L : ℝ) ^ d * (δF * MG + MF * δG) := by
  refine le_trans ?_ (DecayLoopB_sum_norm_glue_le_of_far (g := g) hL hI hk hkl hl hδF hδG hFd hGd hF hG hx hy hxy)
  unfold glueTerm
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun b _ => ?_))
  rw [norm_mul, norm_mul]

end Glue

/-! ## 6. The `(2n+2)`-loop of `ℰ⊗ℰ` keeps every label -/

section EE

open RBM.Gauss.Sizes (STeeLoop)

variable {α : Type*}

theorem length_eeLoop (σ : List Bool) (a a' : List α) {k : ℕ} (hk : k ≤ a.length + 1)
    (ha' : a'.length = a.length) (b b' : α) :
    (STeeLoop σ a a' k b b').length = 2 * a.length + 2 := by
  simp only [STeeLoop, LoopIdx.length, List.length_append, List.length_drop, List.length_take,
    List.length_reverse, List.length_singleton, ha']
  omega

theorem eeLoop_WF (σ : List Bool) (a a' : List α) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ a.length)
    (hσ : σ.length = a.length) (ha' : a'.length = a.length) (b b' : α) :
    (STeeLoop σ a a' k b b').WF := by
  simp only [STeeLoop, LoopIdx.WF, List.length_append, List.length_drop, List.length_take,
    List.length_reverse, List.length_map, List.length_singleton, hσ, ha']
  omega

theorem mem_eeLoop_left (σ : List Bool) (a a' : List α) (k : ℕ) (b b' : α) {c : α}
    (hc : c ∈ a) : c ∈ (STeeLoop σ a a' k b b').a := by
  rw [← List.take_append_drop (k - 1) a, List.mem_append] at hc
  simp only [STeeLoop, List.mem_append, List.mem_reverse, List.mem_singleton]
  tauto

theorem mem_eeLoop_right (σ : List Bool) (a a' : List α) (k : ℕ) (b b' : α) {c : α}
    (hc : c ∈ a') : c ∈ (STeeLoop σ a a' k b b').a := by
  rw [← List.take_append_drop (k - 1) a', List.mem_append] at hc
  simp only [STeeLoop, List.mem_append, List.mem_reverse, List.mem_singleton]
  tauto

end EE

/-! ## 7. Deterministic bounds on the four `ℰ`-terms of a loop with two far labels -/

section Det

open RBM.Gauss.Sizes (STdiamInf)

variable {d : ℕ} (sz : RBM.Gauss.Sizes d) (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ)

private theorem DecayLoopB_norm_W_pow : ‖(((sz.W n : ℕ) : ℂ)) ^ d‖ = ((sz.W n : ℕ) : ℝ) ^ d := by
  simp

private theorem DecayLoopB_size_eq :
    ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
  simp only [RBM.Gauss.Sizes.size]; push_cast; ring

variable {sz n E τ ω}

/-- A well-formed loop is `loopOf` of its entries. -/
private theorem DecayLoopB_loopOf_eq {α : Type*} (J : LoopIdx α) (h : J.WF) :
    loopOf (fun i : Fin J.a.length => J.σ[i.1]'(by rw [h]; exact i.2))
      (fun i : Fin J.a.length => J.a[i.1]) = J := by
  obtain ⟨σ, a⟩ := J
  simp only [LoopIdx.WF] at h
  simp only [loopOf, LoopIdx.mk.injEq]
  refine ⟨?_, List.ofFn_getElem⟩
  exact List.ext_getElem (by simp [h]) (fun i h1 h2 => by simp)

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` and `R ≤ diam_∞ a` to `LoopDecay`. -/
theorem DecayLoopB_loopDecay_of {L : ℕ} (F : LoopIdx (Zd d L) → ℂ) {K : ℕ} {R δ : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Zd d L),
      R ≤ (STdiamInf a : ℝ) → ‖F (loopOf σ a)‖ ≤ δ) :
    LoopDecay d L K R δ F := by
  intro J hJ hJK x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at hJK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1]) (by
      refine le_trans hxy ?_
      exact_mod_cast Finset.le_sup (f := fun q : Fin J.a.length × Fin J.a.length =>
        zdistInf d L (J.a[q.1.1] - J.a[q.2.1]))
        (Finset.mem_univ ((⟨i, hi⟩ : Fin J.a.length), (⟨j, hj⟩ : Fin J.a.length))))
  rwa [DecayLoopB_loopOf_eq J hJ] at this

/-- From bounds on `F (loopOf σ a)` for every length in `[1, K]` to all well-formed loops. -/
theorem DecayLoopB_bound_of {L : ℕ} (F : LoopIdx (Zd d L) → ℂ) {K : ℕ} {B : ℝ}
    (h : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Zd d L), ‖F (loopOf σ a)‖ ≤ B)
    (J : LoopIdx (Zd d L)) (hJ : J.WF) (h1 : 1 ≤ J.length) (hK : J.length ≤ K) : ‖F J‖ ≤ B := by
  have hm : J.a.length ∈ Finset.Icc 1 K := by
    simp only [Finset.mem_Icc]; simp only [LoopIdx.length] at h1 hK; omega
  have := h J.a.length hm (fun i : Fin J.a.length => J.σ[i.1]'(by rw [hJ]; exact i.2))
    (fun i : Fin J.a.length => J.a[i.1])
  rwa [DecayLoopB_loopOf_eq J hJ] at this

/-- `⟨(G_u(σ) - m(σ)) E_a⟩ = (𝓛 - 𝒦)_{u,(σ),(a)}`. -/
theorem DecayLoopB_avgErr_eq (σ : Bool) (a : Zd d (sz.L n)) :
    sz.STavgErr n E τ ω σ a = sz.STLKI n E τ ω ⟨[σ], [a]⟩ := by
  unfold RBM.Gauss.Sizes.STavgErr RBM.Gauss.Sizes.STLKI RBM.Gauss.Sizes.STKI
  rw [KLK_one]

private theorem DecayLoopB_norm_ite_le (p : Prop) [Decidable p] (x : ℂ) :
    ‖(if p then x else 0)‖ ≤ ‖x‖ := by
  split_ifs <;> simp

/-- `Σ_{1 ≤ k < l ≤ n} f(k, l) ≤ n² T`. -/
private theorem DecayLoopB_sum_pairs (n : ℕ) (f : ℕ → ℕ → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ k ∈ Finset.Icc 1 n, ∀ l ∈ Finset.Ioc k n, f k l ≤ T) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l ≤ (n : ℝ) ^ 2 * T := by
  calc ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, f k l
      ≤ ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, T :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l hl => hf k hk l hl
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (n : ℝ) * T := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
        gcongr
        exact_mod_cast Nat.sub_le n k
    _ = (n : ℝ) ^ 2 * T := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]; ring

private theorem DecayLoopB_length_loopOf {α : Type*} {m : ℕ} (σ : Fin m → Bool) (a : Fin m → α) :
    (loopOf σ a).length = m := by
  simp [loopOf, LoopIdx.length]

private theorem DecayLoopB_WF_loopOf {α : Type*} {m : ℕ} (σ : Fin m → Bool) (a : Fin m → α) :
    (loopOf σ a).WF := by
  simp [loopOf, LoopIdx.WF]

private theorem DecayLoopB_mem_loopOf {α : Type*} {m : ℕ} (σ : Fin m → Bool) (a : Fin m → α)
    (i : Fin m) : a i ∈ (loopOf σ a).a := by
  simp only [loopOf]
  exact List.mem_ofFn.2 ⟨i, rfl⟩

/-- One cut of a far loop, both orientations of `[𝒦 ∼ (𝓛 - 𝒦)]` (or `(𝓛-𝒦) × (𝓛-𝒦)`). -/
private theorem DecayLoopB_cut {L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L)
    {F G : LoopIdx (Zd d L) → ℂ} {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hFb : ∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ m → ‖F J‖ ≤ B)
    (hGb : ∀ J : LoopIdx (Zd d L), J.WF → 1 ≤ J.length → J.length ≤ m → ‖G J‖ ≤ B)
    (hFd : LoopDecay d L m R δ F) (hGd : LoopDecay d L m R δ G)
    (σ : Fin m → Bool) (a : Fin m → Zd d L) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d L (a i - a j) : ℝ)) {k l : ℕ} (hk : 1 ≤ k) (hkl : k < l)
    (hl : l ≤ m) :
    ∑ x : Zd d L, ∑ y : Zd d L, ‖F ((loopOf σ a).cutGlueL k l x)‖ * ‖SB d L g x y‖ *
        ‖G ((loopOf σ a).cutGlueR k l y)‖ ≤ (L : ℝ) ^ d * (δ * B + B * δ) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hI : I.WF := DecayLoopB_WF_loopOf σ a
  have hl' : l ≤ I.length := hlen ▸ hl
  refine DecayLoopB_sum_norm_glue_le_of_far (g := g) hL hI hk hkl hl' hδ hδ
    (LoopDecay.mono hFd (le_of_eq hlen) le_rfl le_rfl)
    (LoopDecay.mono hGd (le_of_eq hlen) le_rfl le_rfl) (fun x => ?_) (fun y => ?_)
    (DecayLoopB_mem_loopOf σ a i) (DecayLoopB_mem_loopOf σ a j) hfar
  · refine hFb _ (LoopIdx.wf_cutGlueL I x hI hk hkl hl') ?_
      ((LoopIdx.length_cutGlueL_le I x hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueL I x hk hkl hl']; omega
  · refine hGb _ (LoopIdx.wf_cutGlueR I y hI hk hkl hl') ?_
      ((LoopIdx.length_cutGlueR_le I y hk hkl hl').trans_eq hlen)
    rw [LoopIdx.length_cutGlueR I y hk hkl hl']; omega

/-- **`[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(m)}` of a loop with two far labels**: with `δ`-decay and the crude bound
`B` of `𝓛-𝒦` and `𝒦` on all loops of length `≤ m`, `‖ksimLK_l‖ ≤ W^d m² L^d 4 δ B`. -/
theorem DecayLoopB_det_ksimLK (hL : 3 ≤ sz.L n) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖sz.STLKI n E τ ω J‖ ≤ B)
    (hKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖sz.STKI n E τ J‖ ≤ B)
    (hdLK : LoopDecay d (sz.L n) m R δ (sz.STLKI n E τ ω))
    (hdK : LoopDecay d (sz.L n) m R δ (sz.STKI n E τ))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) (l : ℕ) :
    ‖sz.STksimLK n E τ ω l (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * ((((sz.L n : ℕ) : ℝ)) ^ d * (4 * (δ * B)))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hB : 0 ≤ B := (norm_nonneg _).trans
    (hLKb ⟨[true], [0]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
      (by have := i.2; simp [LoopIdx.length]; omega))
  unfold RBM.Gauss.Sizes.STksimLK
  rw [norm_mul, DecayLoopB_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine DecayLoopB_sum_pairs m _ (by positivity) fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  have h1 := DecayLoopB_cut (sz.lam n) hL hδ hLKb hKb hdLK hdK σ a hfar hk.1 hl'.1 hl'.2
  have h2 := DecayLoopB_cut (sz.lam n) hL hδ hKb hLKb hdK hdLK σ a hfar hk.1 hl'.1 hl'.2
  calc ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        ((if (I.cutGlueR k l' y).length = l then
            sz.STLKI n E τ ω (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STKI n E τ (I.cutGlueR k l' y)
          else 0) +
         (if (I.cutGlueL k l' x).length = l then
            sz.STKI n E τ (I.cutGlueL k l' x) * SB d (sz.L n) (sz.lam n) x y *
              sz.STLKI n E τ ω (I.cutGlueR k l' y)
          else 0))‖
      ≤ ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          (‖sz.STLKI n E τ ω (I.cutGlueL k l' x)‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
              ‖sz.STKI n E τ (I.cutGlueR k l' y)‖ +
            ‖sz.STKI n E τ (I.cutGlueL k l' x)‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
              ‖sz.STLKI n E τ ω (I.cutGlueR k l' y)‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => ?_))
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (DecayLoopB_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
        · refine (DecayLoopB_norm_ite_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ (((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ) + (((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ) := by
        simp only [Finset.sum_add_distrib]
        exact add_le_add h1 h2
    _ = (((sz.L n : ℕ) : ℝ)) ^ d * (4 * (δ * B)) := by ring

/-- **`ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}` of a loop with two far labels**: `‖elklk‖ ≤ W^d m² L^d (δB + Bδ)`. -/
theorem DecayLoopB_det_elklk (hL : 3 ≤ sz.L n) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ)
    (hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ m →
      ‖sz.STLKI n E τ ω J‖ ≤ B)
    (hdLK : LoopDecay d (sz.L n) m R δ (sz.STLKI n E τ ω))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : 2 * R + 1 ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) :
    ‖sz.STelklk n E τ ω (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) ^ 2 * ((((sz.L n : ℕ) : ℝ)) ^ d * (δ * B + B * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hB : 0 ≤ B := (norm_nonneg _).trans
    (hLKb ⟨[true], [0]⟩ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])
      (by have := i.2; simp [LoopIdx.length]; omega))
  unfold RBM.Gauss.Sizes.STelklk
  rw [norm_mul, DecayLoopB_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => norm_sum_le _ _) ?_
  refine DecayLoopB_sum_pairs m _ (by positivity) fun k hk l' hl' => ?_
  simp only [Finset.mem_Icc, Finset.mem_Ioc] at hk hl'
  refine le_trans ?_ (DecayLoopB_cut (sz.lam n) hL hδ hLKb hLKb hdLK hdLK σ a hfar hk.1 hl'.1 hl'.2)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun y _ => ?_))
  rw [norm_mul, norm_mul]

/-- **`ℰ^{G̃}` of a loop with two far labels**: `‖egt‖ ≤ W^d m L^d B δ` (`B` bounds `|G̃|`, `δ` is
the decay of `𝓛` on loops of length `≤ m + 1`). -/
theorem DecayLoopB_det_egt (hL : 3 ≤ sz.L n) {m : ℕ} {R δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (havg : ∀ s a, ‖sz.STavgErr n E τ ω s a‖ ≤ B)
    (hdLL : LoopDecay d (sz.L n) (m + 1) R δ (sz.STLI n E τ ω))
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) {i j : Fin m}
    (hfar : R ≤ (zdistInf d (sz.L n) (a i - a j) : ℝ)) :
    ‖sz.STegt n E τ ω (loopOf σ a)‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * (B * δ))) := by
  set I := loopOf σ a with hIdef
  have hlen : I.length = m := DecayLoopB_length_loopOf σ a
  have hI : I.WF := DecayLoopB_WF_loopOf σ a
  unfold RBM.Gauss.Sizes.STegt
  rw [norm_mul, DecayLoopB_norm_W_pow, hlen]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 1 m, ‖∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
        sz.STavgErr n E τ ω (I.σ.getD (k - 1) false) x * SB d (sz.L n) (sz.lam n) x y *
          sz.STLI n E τ ω (I.cutGlue k y)‖
      ≤ ∑ k ∈ Finset.Icc 1 m, ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
          ‖SB d (sz.L n) (sz.lam n) x y‖ * (B * δ) := by
        refine Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun y _ => ?_))
        simp only [Finset.mem_Icc] at hk
        have hkI : k ≤ I.length := hlen ▸ hk.2
        have hd : ‖sz.STLI n E τ ω (I.cutGlue k y)‖ ≤ δ := by
          refine hdLL _ (DecayLoopB_wf_cutGlue I y hk.1 hkI hI) ?_ (a i)
            (mem_cutGlue_of_mem I y k (DecayLoopB_mem_loopOf σ a i)) (a j)
            (mem_cutGlue_of_mem I y k (DecayLoopB_mem_loopOf σ a j)) hfar
          rw [DecayLoopB_length_cutGlue I y hk.1 hkI hI, hlen]
        rw [norm_mul, norm_mul]
        calc ‖sz.STavgErr n E τ ω (I.σ.getD (k - 1) false) x‖ * ‖SB d (sz.L n) (sz.lam n) x y‖ *
              ‖sz.STLI n E τ ω (I.cutGlue k y)‖
            = ‖SB d (sz.L n) (sz.lam n) x y‖ * (‖sz.STavgErr n E τ ω (I.σ.getD (k - 1) false) x‖ *
                ‖sz.STLI n E τ ω (I.cutGlue k y)‖) := by ring
          _ ≤ ‖SB d (sz.L n) (sz.lam n) x y‖ * (B * δ) := mul_le_mul_of_nonneg_left
              (mul_le_mul (havg _ _) hd (norm_nonneg _) hB) (norm_nonneg _)
    _ = (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * (B * δ)) := by
        simp only [← Finset.sum_mul, DecayLoopB_sum_sum_norm_SB d (sz.L n) (sz.lam n) hL,
          Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
        ring

/-- Every label of `a` and of `a'` is a label of the `(2m+2)`-loop at every cut. -/
private theorem DecayLoopB_mem_eeLoop {L m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d L) (k : ℕ)
    (b b' : Zd d L) (i : Fin (m + m)) :
    Fin.append a a' i ∈ (RBM.Gauss.Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b').a := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [Fin.append_left]
    exact mem_eeLoop_left _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)
  · rw [Fin.append_right]
    exact mem_eeLoop_right _ _ _ _ _ _ (List.mem_ofFn.2 ⟨i, rfl⟩)

/-- **`(ℰ⊗ℰ)^M` of a pair of label vectors with two far labels**: `‖ee‖ ≤ m W^d L^d δ`. -/
theorem DecayLoopB_det_ee (hL : 3 ≤ sz.L n) {m : ℕ} {R δ : ℝ} (hδ : 0 ≤ δ)
    (hdLL : LoopDecay d (sz.L n) (2 * m + 2) R δ (sz.STLI n E τ ω))
    (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) {i j : Fin (m + m)}
    (hfar : R ≤ (zdistInf d (sz.L n) (Fin.append a a' i - Fin.append a a' j) : ℝ)) :
    ‖sz.STee n E τ ω σ a a'‖ ≤
      (m : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ)) ^ d) * δ := by
  unfold RBM.Gauss.Sizes.STee
  rw [norm_mul, DecayLoopB_norm_W_pow]
  have key : ‖∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
      SB d (sz.L n) (sz.lam n) b b' *
        sz.STLI n E τ ω (RBM.Gauss.Sizes.STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')‖ ≤
      (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ) := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
          ‖SB d (sz.L n) (sz.lam n) b b'‖ * δ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun b' _ => ?_)))
          simp only [Finset.mem_Icc] at hk
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hdLL _ (eeLoop_WF _ _ _ hk.1 (by simpa using hk.2) (by simp) (by simp) b b') ?_
            _ (DecayLoopB_mem_eeLoop σ a a' k b b' i) _ (DecayLoopB_mem_eeLoop σ a a' k b b' j) hfar
          rw [length_eeLoop _ _ _ (by simp; omega) (by simp) b b']
          simp
      _ = (m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ) := by
          simp only [← Finset.sum_mul, DecayLoopB_sum_sum_norm_SB d (sz.L n) (sz.lam n) hL,
            Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          ring
  calc ((sz.W n : ℕ) : ℝ) ^ d * ‖_‖
      ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((m : ℝ) * ((((sz.L n : ℕ) : ℝ)) ^ d * δ)) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (m : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ)) ^ d) * δ := by ring

end Det

end RBM.Ind

/-! ## 8. Target 3: `STDecayLoopU`, `lem_decayLoop` uniformly in `u ∈ [s_n, t_n]` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss
open RBM.Ind (symIdx norm_sq_gloop_le_symIdx exists_split_loopIdx norm_gloop_le_of_le_abs_im
  symIdx_a_length)

variable {d : ℕ}

/-- **`lem_decayLoop` uniformly in `u ∈ [s_n, t_n]`** (T2135 Amend 1, DECISIONS §39; paper-delta
candidate `T2135b`, the paper's "uniformly in `u`", `1_2:1371`): the conclusion of `STDecayLoopPT`
(`DecayLoopA.lean:106`) with `Prec` (the union over `u` inside `P`) in place of `PrecPT`
(the union outside), as `STSEforLnConcl` and `STEKDecay` are stated.  For every `k ≥ 1`, `τ', D' > 0`:
`(|𝓛^{(k)}_{u,σ,a}| + |(𝓛-𝒦)^{(k)}_{u,σ,a}|) 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}`, uniformly in
`(u, σ, a) ∈ [s_n,t_n] × {±}^k × (Z_L^d)^k`. -/
def STDecayLoopU (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D'))

section Adjacent

variable {d L : ℕ} [NeZero L]

private theorem DecayLoopB_zdistInf_add_le (x y : Zd d L) :
    zdistInf d L (x + y) ≤ zdistInf d L x + zdistInf d L y := by
  unfold zdistInf
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((x + y) i) = zdist L (x i + y i) := rfl
    _ ≤ zdist L (x i) + zdist L (y i) := zdist_add_le L (x i) (y i)
    _ ≤ _ := Nat.add_le_add
        (Finset.le_sup (f := fun j => zdist L (x j)) (Finset.mem_univ i))
        (Finset.le_sup (f := fun j => zdist L (y j)) (Finset.mem_univ i))

private theorem DecayLoopB_zdistInf_neg (x : Zd d L) : zdistInf d L (-x) = zdistInf d L x := by
  unfold zdistInf
  exact Finset.sup_congr rfl fun i _ => by simp [zdist_neg]

omit [NeZero L] in
private theorem DecayLoopB_zdistInf_zero : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  simp

private theorem DecayLoopB_zdistInf_comm (a b : Zd d L) :
    zdistInf d L (a - b) = zdistInf d L (b - a) := by
  rw [← neg_sub b a, DecayLoopB_zdistInf_neg]

private theorem DecayLoopB_zdistInf_tri (a b c : Zd d L) :
    zdistInf d L (a - c) ≤ zdistInf d L (a - b) + zdistInf d L (b - c) := by
  have := DecayLoopB_zdistInf_add_le (a - b) (b - c)
  rwa [sub_add_sub_cancel] at this

/-- `2 |x|_∞ ≤ L`: no two labels are farther than `L/2` on the torus. -/
private theorem DecayLoopB_two_mul_zdistInf_le (x : Zd d L) : 2 * zdistInf d L x ≤ L := by
  have h : zdistInf d L x ≤ L / 2 := by
    unfold zdistInf
    refine Finset.sup_le fun i _ => ?_
    unfold zdist
    omega
  omega

/-- `diam_∞ a ≤ L / 2`. -/
private theorem DecayLoopB_two_mul_diam_le {k : ℕ} (a : Fin k → Zd d L) :
    2 * STdiamInf a ≤ L := by
  have h : STdiamInf a ≤ L / 2 := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    have := DecayLoopB_two_mul_zdistInf_le (a p.1 - a p.2)
    omega
  omega

/-- `diam_∞ a ≤ KLmaxDist a` (`zdistInf ≤ zdistD`). -/
private theorem DecayLoopB_diam_le_KLmaxDist {k : ℕ} (a : Fin k → Zd d L) :
    STdiamInf a ≤ KLmaxDist d L a := by
  unfold STdiamInf
  refine Finset.sup_le fun p _ => ?_
  exact (zdistInf_le_zdistD d L _).trans
    (Finset.le_sup (f := fun q : Fin k × Fin k => zdistD d L (a q.1 - a q.2)) (Finset.mem_univ p))

/-- `diam_∞ a = 0` for a single label. -/
private theorem DecayLoopB_diam_one (a : Fin 1 → Zd d L) : STdiamInf a = 0 := by
  unfold STdiamInf
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun p _ => ?_
  have : p.1 = p.2 := Subsingleton.elim _ _
  simp [this, DecayLoopB_zdistInf_zero]

/-- **Some adjacent pair is far.**  `diam_∞ a ≤ (k-1) |a_m - a_{m+1}|_∞` for some `m + 1 < k`
(triangle inequality along the chain `a_i, a_{i+1}, …, a_j`, which has at most `k - 1` steps). -/
private theorem DecayLoopB_adjacent {k : ℕ} (hk : 2 ≤ k) (a : Fin k → Zd d L) :
    ∃ (m : ℕ) (h : m + 1 < k),
      STdiamInf a ≤ (k - 1) * zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, h⟩) := by
  classical
  let a' : ℕ → Zd d L := fun i => if h : i < k then a ⟨i, h⟩ else 0
  have ha' : ∀ i (h : i < k), a' i = a ⟨i, h⟩ := fun i h => by simp [a', h]
  let δ : ℕ → ℕ := fun i => zdistInf d L (a' i - a' (i + 1))
  have hne : (Finset.range (k - 1)).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨m, hm, hΔ⟩ := Finset.exists_mem_eq_sup (Finset.range (k - 1)) hne δ
  have hm' : m + 1 < k := by have := Finset.mem_range.mp hm; omega
  refine ⟨m, hm', ?_⟩
  set Δ := (Finset.range (k - 1)).sup δ with hΔdef
  have hδΔ : ∀ i, i + 1 < k → δ i ≤ Δ := fun i hi =>
    Finset.le_sup (f := δ) (Finset.mem_range.mpr (by omega))
  have hchain : ∀ e i, i + e < k → zdistInf d L (a' i - a' (i + e)) ≤ e * Δ := by
    intro e
    induction e with
    | zero =>
      intro i _
      simp [DecayLoopB_zdistInf_zero]
    | succ e ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hδΔ (i + e) (by omega)
      have h3 := DecayLoopB_zdistInf_tri (a' i) (a' (i + e)) (a' (i + (e + 1)))
      have h4 : δ (i + e) = zdistInf d L (a' (i + e) - a' (i + (e + 1))) := by
        simp only [δ]; rfl
      rw [h4] at h2
      calc zdistInf d L (a' i - a' (i + (e + 1)))
          ≤ zdistInf d L (a' i - a' (i + e)) + zdistInf d L (a' (i + e) - a' (i + (e + 1))) := h3
        _ ≤ e * Δ + Δ := by omega
        _ = (e + 1) * Δ := by ring
  have hmax : STdiamInf a ≤ (k - 1) * Δ := by
    unfold STdiamInf
    refine Finset.sup_le fun p _ => ?_
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := p
    simp only
    rcases le_total i j with hij | hij
    · have := hchain (j - i) i (by omega)
      rw [show i + (j - i) = j by omega, ha' i hi, ha' j hj] at this
      calc _ ≤ (j - i) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
    · have := hchain (i - j) j (by omega)
      rw [show j + (i - j) = i by omega, ha' i hi, ha' j hj] at this
      rw [DecayLoopB_zdistInf_comm]
      calc _ ≤ (i - j) * Δ := this
        _ ≤ (k - 1) * Δ := Nat.mul_le_mul_right _ (by omega)
  have hmm : Δ = zdistInf d L (a ⟨m, by omega⟩ - a ⟨m + 1, hm'⟩) := by
    rw [hΔ]
    simp only [δ]
    rw [ha' m (by omega), ha' (m + 1) hm']
  rw [← hmm]
  exact hmax

end Adjacent

section Cut

variable {d L W : ℕ} [NeZero L]

private theorem DecayLoopB_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W H z I
      = Matrix.trace (((I.σ.zip I.a).map fun p => Gres H z p.1 * Eblk d L W p.2).prod) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1
        = (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  unfold loopL
  rw [hfold]

/-- Cyclic invariance of `𝓛`: moving the first edge to the end (trace cyclicity). -/
private theorem DecayLoopB_loopL_rotate (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (s : Bool)
    (b : Zd d L) (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    loopL d L W H z ⟨s :: σ, b :: a⟩ = loopL d L W H z ⟨σ ++ [s], a ++ [b]⟩ := by
  rw [DecayLoopB_loopL_eq_prod, DecayLoopB_loopL_eq_prod]
  simp only [List.zip_cons_cons, List.map_cons, List.prod_cons]
  rw [List.zip_append h]
  simp only [List.map_append, List.prod_append, List.zip_cons_cons, List.zip_nil_left,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

/-- Rotating a loop by `j` positions does not change `𝓛`. -/
private theorem DecayLoopB_loopL_rotate_iter {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ} :
    ∀ (j : ℕ) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      loopL d L W H z ⟨σ.rotate j, a.rotate j⟩ = loopL d L W H z ⟨σ, a⟩ := by
  intro j
  induction j with
  | zero => intro σ a _; simp
  | succ j ih =>
    intro σ a h
    cases σ with
    | nil =>
      have : a = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst this; simp
    | cons s σ =>
      cases a with
      | nil => simp at h
      | cons b a =>
        have h' : σ.length = a.length := by simpa using h
        rw [List.rotate_cons_succ, List.rotate_cons_succ]
        rw [ih (σ ++ [s]) (a ++ [b]) (by simp [h'])]
        exact (DecayLoopB_loopL_rotate H z s b σ a h').symm

variable [NeZero W]

/-- **The cut.**  For a loop of length `k ≥ 2` and `m + 1 < k`, with `s = σ_{m+1}`,
`b' = a_{m+1}`, `b = a_m`: `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛 ⟨[s, !s], [b', b]⟩|`.  The loop is rotated by
`m + 1` so that `(a_{m+1}, a_m)` is (first label, last label), then cut into the one-`G` chain
`G_{σ_{m+1}}` and the `(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy-Schwarz) and
`norm_gloop_le_of_le_abs_im` (operator norm bound of the symmetric `(k-1)`-loop) finish. -/
private theorem DecayLoopB_cutOne
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} {η : ℝ}
    (hη : 0 < η) (hz : η ≤ |z.im|) {k : ℕ} (hk : 2 ≤ k) (σl : List Bool) (al : List (Zd d L))
    (hσ : σl.length = k) (ha : al.length = k) (m : ℕ) (hm : m + 1 < k) :
    ∃ (s : Bool) (b' b : Zd d L), σl[m + 1]? = some s ∧ al[m + 1]? = some b' ∧ al[m]? = some b ∧
      ‖loopL d L W H z ⟨σl, al⟩‖ ^ 2 ≤
        η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[s, !s], [b', b]⟩‖ := by
  have hlen : σl.length = al.length := by omega
  have hrot := DecayLoopB_loopL_rotate_iter (H := H) (z := z) (m + 1) σl al hlen
  obtain ⟨σA, σB, aA, aB, b', b, hσeq, haeq, hσA, haA, hσB, haB⟩ :=
    exists_split_loopIdx (k₁ := 1) (k₂ := k - 1) (by omega) (by omega)
      (σ := σl.rotate (m + 1)) (a := al.rotate (m + 1)) (by simp [hσ]; omega) (by simp [ha]; omega)
  have haA0 : aA = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨s, hs⟩ : ∃ s, σA = [s] := by
    match σA, hσA with
    | [s], _ => exact ⟨s, rfl⟩
  subst haA0
  subst hs
  refine ⟨s, b', b, ?_, ?_, ?_, ?_⟩
  · have h1 : (σl.rotate (m + 1))[0]? = some s := by
      rw [hσeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % σl.length = m + 1 := by
      rw [hσ]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[0]? = some b' := by
      rw [haeq]; simp
    rw [List.getElem?_rotate (by omega)] at h1
    have : (0 + (m + 1)) % al.length = m + 1 := by
      rw [ha]; simp only [zero_add]; exact Nat.mod_eq_of_lt hm
    rwa [this] at h1
  · have h1 : (al.rotate (m + 1))[k - 1]? = some b := by
      have : (al.rotate (m + 1)).getLast? = some b := by
        rw [haeq, List.nil_append, List.singleton_append, ← List.cons_append, List.getLast?_concat]
      rwa [List.getLast?_eq_getElem?, List.length_rotate, ha] at this
    rw [List.getElem?_rotate (by omega)] at h1
    have : (k - 1 + (m + 1)) % al.length = m := by
      rw [ha]
      have : k - 1 + (m + 1) = m + k := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rwa [this] at h1
  · rw [← hrot, hσeq, haeq]
    have h := norm_sq_gloop_le_symIdx (z := z) hH (σA := [s]) (σB := σB) (aA := []) (aB := aB)
      (by simp) (by omega) b' b
    refine h.trans ?_
    have hsym : symIdx [s] ([] : List (Zd d L)) b' b = ⟨[s, !s], [b', b]⟩ := by
      simp [symIdx]
    rw [hsym, mul_comm (η⁻¹ ^ (2 * (k - 1)))]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hB := norm_gloop_le_of_le_abs_im (z := z) (W := W) hH hη hz (symIdx σB aB b b')
      (by simp; omega) (by simp; omega)
    refine hB.trans ?_
    simp only [symIdx_a_length]
    have h2 : 2 * (aB.length + 1) = 2 * (k - 1) := by omega
    rw [h2]
    have hW : (((W : ℝ) ^ d)⁻¹) ≤ 1 := by
      have : (1 : ℝ) ≤ (W : ℝ) ^ d :=
        one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne W))
      exact inv_le_one_of_one_le₀ this
    have hW' : (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) hW
    calc η⁻¹ ^ (2 * (k - 1)) * (((W : ℝ) ^ d)⁻¹) ^ (2 * (k - 1) - 1)
        ≤ η⁻¹ ^ (2 * (k - 1)) * 1 := by gcongr
      _ = _ := mul_one _

/-- `⟨[s, !s], [b', b]⟩` is the `(+,-)` two-loop at `(b', b)` (`s = +`) or at `(b, b')`
(`s = -`, by one rotation). -/
private theorem DecayLoopB_loopL_two_sign {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (s : Bool) (b' b : Zd d L) :
    loopL d L W H z ⟨[s, !s], [b', b]⟩ =
      loopL d L W H z ⟨[true, false], [if s then b' else b, if s then b else b']⟩ := by
  cases s
  · have := DecayLoopB_loopL_rotate (L := L) (W := W) H z false b' [true] [b] rfl
    simpa using this
  · simp

/-- **The far pair and the loop bound, with the pair independent of the matrix.**  For `k ≥ 2` there
is `c = (c₀, c₁)` (a function of `σ`, `a` only) with `diam_∞ a ≤ (k-1) |c₀ - c₁|_∞` and, for
every Hermitian `H` and `η ≤ |Im z|`, `|𝓛_{σ,a}|² ≤ η^{-2(k-1)} |𝓛_{(+,-),c}|`. -/
private theorem DecayLoopB_pair {k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    ∃ c : Zd d L × Zd d L,
      ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d L (c.1 - c.2) : ℝ) ∧
      ∀ (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (η : ℝ), H.IsHermitian →
        0 < η → η ≤ |z.im| →
        ‖loopL d L W H z (loopOf σ a)‖ ^ 2 ≤
          η⁻¹ ^ (2 * (k - 1)) * ‖loopL d L W H z ⟨[true, false], [c.1, c.2]⟩‖ := by
  obtain ⟨m, hm, hmax⟩ := DecayLoopB_adjacent hk a
  obtain ⟨s, hs⟩ : ∃ s : Bool, s = σ ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : Zd d L, b' = a ⟨m + 1, hm⟩ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Zd d L, b = a ⟨m, by omega⟩ := ⟨_, rfl⟩
  refine ⟨(if s then b' else b, if s then b else b'), ?_, ?_⟩
  · have hcast : ((STdiamInf a : ℕ) : ℝ) ≤
        (((k - 1 : ℕ) : ℝ)) * (zdistInf d L (b - b') : ℝ) := by
      rw [hb, hb']
      exact_mod_cast hmax
    have hk1 : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hk1] at hcast
    cases s
    · simpa using hcast
    · simp only [ite_true]
      rw [DecayLoopB_zdistInf_comm]
      simpa using hcast
  · intro H z η hH hη hz
    obtain ⟨s', b'', b''', hs', hb'', hb''', hbound⟩ := DecayLoopB_cutOne (W := W) hH hη hz hk
      (List.ofFn σ) (List.ofFn a) (by simp) (by simp) m hm
    rw [List.getElem?_ofFn] at hs' hb'' hb'''
    simp only [hm, dite_true, show m < k by omega] at hs' hb'' hb'''
    have e1 : s' = s := by rw [hs]; exact (Option.some.inj hs').symm
    have e2 : b'' = b' := by rw [hb']; exact (Option.some.inj hb'').symm
    have e3 : b''' = b := by rw [hb]; exact (Option.some.inj hb''').symm
    rw [e1, e2, e3, DecayLoopB_loopL_two_sign] at hbound
    exact hbound

end Cut

/-! ## 8b. Scales and exponents of target 3 -/

section Scales

/-- `Im m(E) ≥ √κ / 2` for `|E| ≤ 2 - κ` (the same bound as `ST_mE_im_ge`, `Step2Events.lean:555`,
which is not imported here). -/
private theorem DecayLoopB_mE_im_ge {E κ : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    Real.sqrt κ / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h := abs_le.mp hE
    nlinarith [h.1, h.2]
  have : κ ≤ 4 - E ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

/-- **`1 - u ≥ N⁻¹` from the far premise.**  If `ℓ_u < L` (which the far premise
`ℓ_u W^{τ'} ≤ diam_∞ a ≤ L/2` gives) then `g² < L² (1 - u)`; with `g² ≥ W^{-d}` (`(eq:WO)`) and
`L² ≤ L^d` this is `1 - u > (W L)^{-d} = N⁻¹`. -/
private theorem DecayLoopB_one_sub_u {d L W : ℕ} (hd : 2 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W)
    {g u : ℝ} (hg : 0 < g) (hgW : ((W : ℝ) ^ d)⁻¹ ≤ g ^ 2) (hu : u < 1)
    (hℓ : ellT L g u < L) : ((((W * L) ^ d : ℕ) : ℝ))⁻¹ ≤ 1 - u := by
  have hv : 0 < 1 - u := by linarith
  have h1 : g / Real.sqrt |1 - u| < L := by
    unfold ellT at hℓ
    rcases min_lt_iff.mp hℓ with h | h
    · exact lt_of_le_of_lt (le_max_left _ _) h
    · exact absurd h (lt_irrefl _)
  rw [abs_of_pos hv] at h1
  have hs : 0 < Real.sqrt (1 - u) := Real.sqrt_pos.mpr hv
  have h2 : g < L * Real.sqrt (1 - u) := by rwa [div_lt_iff₀ hs] at h1
  have h3 : g ^ 2 < (L : ℝ) ^ 2 * (1 - u) := by
    have := pow_lt_pow_left₀ h2 hg.le (two_ne_zero)
    rwa [mul_pow, Real.sq_sqrt hv.le] at this
  have hW0 : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < W := by exact_mod_cast hW
    positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hL0 : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have h4 : 1 ≤ (W : ℝ) ^ d * g ^ 2 := by
    have := mul_le_mul_of_nonneg_left hgW hW0.le
    rwa [mul_inv_cancel₀ hW0.ne'] at this
  have hL2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ hL1 hd
  have hN : ((((W * L) ^ d : ℕ) : ℝ)) = (W : ℝ) ^ d * (L : ℝ) ^ d := by
    push_cast; ring
  have h5 : 1 ≤ ((((W * L) ^ d : ℕ) : ℝ)) * (1 - u) := by
    rw [hN]
    calc (1 : ℝ) ≤ (W : ℝ) ^ d * g ^ 2 := h4
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ 2 * (1 - u)) := by gcongr
      _ ≤ (W : ℝ) ^ d * ((L : ℝ) ^ d * (1 - u)) := by gcongr
      _ = _ := by ring
  have hNpos : (0 : ℝ) < (((W * L) ^ d : ℕ) : ℝ) := by rw [hN]; positivity
  calc ((((W * L) ^ d : ℕ) : ℝ))⁻¹ = ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((((W * L) ^ d : ℕ) : ℝ))⁻¹ * (((((W * L) ^ d : ℕ) : ℝ)) * (1 - u)) := by gcongr
    _ = 1 - u := by field_simp

/-- **`STWB ≤ 2` in the far regime**: `W^{-d} B_{u,K} ≤ (W^d g²)⁻¹ + (N (1-u))⁻¹ ≤ 2` once
`g² W^d ≥ 1` and `N (1-u) ≥ 1`. -/
private theorem DecayLoopB_STWB_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (K : ℕ) (hu : u < 1)
    (hg : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)
    (hN : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - u)) : STWB sz n u K ≤ 2 := by
  have hv : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by
    by_contra h
    push Not at h
    have : sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hW0.le
    linarith
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold STWB Bparam
  rw [abs_of_pos hv]
  have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤
      (sz.lam n ^ 2)⁻¹ := by
    have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    have hb : ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]))
    calc (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹
        ≤ (sz.lam n ^ 2)⁻¹ * 1 := mul_le_mul ha hb (by positivity) (by positivity)
      _ = _ := mul_one _
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((K : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
    _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ +
          (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hNe]; field_simp
    _ ≤ 1 + 1 := by
        gcongr <;> exact inv_le_one_of_one_le₀ ‹_›
    _ = 2 := by norm_num

/-- `STWB ≥ 0`. -/
private theorem DecayLoopB_STWB_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) (K : ℕ) :
    0 ≤ STWB sz n u K := by
  unfold STWB Bparam
  positivity

/-- The chain of inequalities for a far loop, in abstract real quantities: `Λ = |𝓛_{σ,a}|`,
`Lp = |𝓛_{(+,-),c}|`, `Kp = |𝒦_{(+,-),c}|`, `X = |(𝓛-𝒦)_{(+,-),c}|` bounded through the decay input
(`Pn` the prefactor, `Mi = STWB(u,|c₀-c₁|) ≤ Θ`, `ex = exp(-√(|c₀-c₁|_∞/ℓ_u))`), `Kc = |𝒦_{σ,a}|`,
`ηi = η_u⁻¹`; with `Q = 2D' + A(2(k-1) + 1 + C₀) + 1`, `A = 1/𝔠` and `N ≤ W^A`, then
`2Λ + Kc ≤ W^{-D'}` once `W ≥ max(2, 16 Γ^{2(k-1)}(2 + Θ))`.  (RBM2D `DecayLoop_alg`, `Induction/DecayLoop.lean`, with
`M_u^{-2} ≤ Γ²` replaced by the constant `Θ`.) -/
private theorem DecayLoopB_alg {W N Γ Θ A ηi Λ Kp X Kc Lp Pn Mi ex : ℝ} {k : ℕ} {D' C₀ Q : ℝ}
    (hk : 2 ≤ k) (hC₀ : 0 ≤ C₀) (hΓ : 0 ≤ Γ) (hΘ : 0 ≤ Θ)
    (hW : 2 ≤ W) (hWmin : 16 * Γ ^ (2 * (k - 1)) * (2 + Θ) ≤ W)
    (hN1 : 1 ≤ N) (hNW : N ≤ W ^ A)
    (hQ : Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1)
    (hηi0 : 0 ≤ ηi) (hηi : ηi ≤ Γ * N)
    (hΛ0 : 0 ≤ Λ) (hLp0 : 0 ≤ Lp) (hΛ : Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp)
    (hLp : Lp ≤ Kp + X) (hKp : Kp ≤ W ^ (-Q))
    (hX : X ≤ N * (Pn * Mi * ex + W ^ (-Q)))
    (hPn : Pn ≤ N ^ C₀) (hMi : Mi ≤ Θ) (hex : ex ≤ W ^ (-Q))
    (hMi0 : 0 ≤ Mi) (hex0 : 0 ≤ ex)
    (hKc : Kc ≤ W ^ (-(D' + 1))) :
    2 * Λ + Kc ≤ W ^ (-D') := by
  have hW0 : 0 < W := by linarith
  have hWQ : 0 < W ^ (-Q) := Real.rpow_pos_of_pos hW0 _
  have hN0 : 0 < N := by linarith
  set r : ℝ := 2 * ((k : ℝ) - 1) + 1 + C₀ with hr
  have hk1 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0 ≤ r := by rw [hr]; nlinarith
  -- Step 1: Kp + X ≤ W^{-Q} (2 + Θ) N^{1 + C₀}
  have hN1C : 1 ≤ N ^ (1 + C₀) := Real.one_le_rpow hN1 (by linarith)
  have hNN1C : N ≤ N ^ (1 + C₀) := by
    calc N = N ^ (1 : ℝ) := (Real.rpow_one N).symm
      _ ≤ N ^ (1 + C₀) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hPMe : Pn * Mi * ex ≤ N ^ C₀ * Θ * W ^ (-Q) := by
    have h1 : Pn * Mi ≤ N ^ C₀ * Θ := mul_le_mul hPn hMi hMi0 (by positivity)
    exact mul_le_mul h1 hex hex0 (mul_nonneg (by positivity) hΘ)
  have hX2 : X ≤ W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
    calc X ≤ N * (Pn * Mi * ex + W ^ (-Q)) := hX
      _ ≤ N * (N ^ C₀ * Θ * W ^ (-Q) + W ^ (-Q)) := by gcongr
      _ = W ^ (-Q) * (Θ * (N * N ^ C₀) + N) := by ring
      _ = W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := by
        rw [Real.rpow_add hN0, Real.rpow_one]
  have hKX : Kp + X ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
    calc Kp + X ≤ W ^ (-Q) + W ^ (-Q) * (Θ * N ^ (1 + C₀) + N) := add_le_add hKp hX2
      _ = W ^ (-Q) * (1 + (Θ * N ^ (1 + C₀) + N)) := by ring
      _ ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := by
        apply mul_le_mul_of_nonneg_left _ hWQ.le
        nlinarith
  -- Step 2: Λ² ≤ Γ^{2(k-1)} (2+Θ) N^r W^{-Q}
  have hηpow : ηi ^ (2 * (k - 1)) ≤ (Γ * N) ^ (2 * (k - 1)) := pow_le_pow_left₀ hηi0 hηi _
  have hLpb : Lp ≤ W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀)) := hLp.trans hKX
  have hexp : ((2 * (k - 1) : ℕ) : ℝ) = 2 * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  have hNr' : N ^ (2 * (k - 1)) * N ^ (1 + C₀) = N ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN0, hexp]
    congr 1; rw [hr]; ring
  have hΛ2 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by
    have hηnn : 0 ≤ ηi ^ (2 * (k - 1)) := by positivity
    calc Λ ^ 2 ≤ ηi ^ (2 * (k - 1)) * Lp := hΛ
      _ ≤ (Γ * N) ^ (2 * (k - 1)) * (W ^ (-Q) * ((2 + Θ) * N ^ (1 + C₀))) := by
        gcongr
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * ((N ^ (2 * (k - 1)) * N ^ (1 + C₀)) * W ^ (-Q)) := by
        rw [mul_pow]; ring
      _ = Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := by rw [hNr']
  -- Step 3: N^r ≤ W^{A r}, W^{A r} W^{-Q} = W^{-D'}² W⁻¹
  have hNr : N ^ r ≤ W ^ (A * r) := by
    calc N ^ r ≤ (W ^ A) ^ r := Real.rpow_le_rpow hN0.le hNW hr0
      _ = W ^ (A * r) := (Real.rpow_mul hW0.le A r).symm
  have ht0 : 0 < W ^ (-D') := Real.rpow_pos_of_pos hW0 _
  have hWQ' : W ^ (A * r) * W ^ (-Q) = (W ^ (-D')) ^ 2 * W⁻¹ := by
    rw [← Real.rpow_add hW0, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le,
      ← Real.rpow_neg_one, ← Real.rpow_add hW0]
    congr 1
    rw [hQ]; push_cast; ring
  have hΛ3 : Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹) := by
    have hc : 0 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) := mul_nonneg (by positivity) (by linarith)
    calc Λ ^ 2 ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (N ^ r * W ^ (-Q)) := hΛ2
      _ ≤ Γ ^ (2 * (k - 1)) * (2 + Θ) * (W ^ (A * r) * W ^ (-Q)) := by gcongr
      _ = _ := by rw [hWQ']
  -- Step 4: 2 Λ ≤ W^{-D'}/2
  have hcoef : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ ≤ 1 / 4 := by
    have h1 : 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹ =
        (16 * Γ ^ (2 * (k - 1)) * (2 + Θ)) / (4 * W) := by
      field_simp; ring
    rw [h1, div_le_iff₀ (by positivity)]
    nlinarith
  have h2Λ : 2 * Λ ≤ W ^ (-D') / 2 := by
    have hsq : (2 * Λ) ^ 2 ≤ (W ^ (-D') / 2) ^ 2 := by
      calc (2 * Λ) ^ 2 = 4 * Λ ^ 2 := by ring
        _ ≤ 4 * (Γ ^ (2 * (k - 1)) * (2 + Θ) * ((W ^ (-D')) ^ 2 * W⁻¹)) := by gcongr
        _ = (4 * (Γ ^ (2 * (k - 1)) * (2 + Θ)) * W⁻¹) * (W ^ (-D')) ^ 2 := by ring
        _ ≤ (1 / 4) * (W ^ (-D')) ^ 2 := by gcongr
        _ = (W ^ (-D') / 2) ^ 2 := by ring
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  -- Step 5: Kc ≤ W^{-D'}/2
  have hKc' : Kc ≤ W ^ (-D') / 2 := by
    have : W ^ (-(D' + 1)) = W ^ (-D') * W⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hW0]; congr 1; ring
    have h3 : W⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hW
    calc Kc ≤ W ^ (-(D' + 1)) := hKc
      _ = W ^ (-D') * W⁻¹ := this
      _ ≤ W ^ (-D') * (1 / 2) := by gcongr
      _ = W ^ (-D') / 2 := by ring
  linarith

/-- `exp(-√x) ≤ W^{-Q}` for `x ≥ (W^{τ'/2}/K)²`, eventually in `W` (`log W ≤ W^{τ'/4}/(τ'/4)`). -/
private theorem DecayLoopB_exp_small {τ' : ℝ} (hτ' : 0 < τ') {K Q : ℝ} (hK : 0 < K) (hQ : 0 ≤ Q) :
    ∀ᶠ w : ℝ in atTop, ∀ x : ℝ, (w ^ (τ' / 2) / K) ^ 2 ≤ x →
      Real.exp (-Real.sqrt x) ≤ w ^ (-Q) := by
  have hev : ∀ᶠ w : ℝ in atTop, 4 * Q * K / τ' ≤ w ^ (τ' / 4) :=
    (tendsto_rpow_atTop (by linarith : 0 < τ' / 4)).eventually_ge_atTop _
  filter_upwards [hev, eventually_gt_atTop 0] with w hw hw0
  intro x hx
  have hpos : 0 ≤ w ^ (τ' / 2) / K := by positivity
  have hsq : w ^ (τ' / 2) / K ≤ Real.sqrt x := by
    calc w ^ (τ' / 2) / K = Real.sqrt ((w ^ (τ' / 2) / K) ^ 2) := (Real.sqrt_sq hpos).symm
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hlog : Real.log w ≤ w ^ (τ' / 4) / (τ' / 4) :=
    Real.log_le_rpow_div hw0.le (by linarith)
  have hQlog : Q * Real.log w ≤ w ^ (τ' / 2) / K := by
    have h1 : Q * Real.log w ≤ Q * (w ^ (τ' / 4) / (τ' / 4)) := by gcongr
    have h2 : Q * (w ^ (τ' / 4) / (τ' / 4)) = (4 * Q / τ') * w ^ (τ' / 4) := by
      field_simp
    have h3 : w ^ (τ' / 2) = w ^ (τ' / 4) * w ^ (τ' / 4) := by
      rw [← Real.rpow_add hw0]; congr 1; ring
    have hw4 : 0 < w ^ (τ' / 4) := Real.rpow_pos_of_pos hw0 _
    have h4 : (4 * Q / τ') * w ^ (τ' / 4) ≤ w ^ (τ' / 2) / K := by
      rw [h3, le_div_iff₀ hK]
      have : 4 * Q / τ' * K ≤ w ^ (τ' / 4) := by
        have : 4 * Q * K / τ' = 4 * Q / τ' * K := by ring
        linarith
      nlinarith
    linarith
  calc Real.exp (-Real.sqrt x) ≤ Real.exp (-(Q * Real.log w)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ = w ^ (-Q) := by
        rw [Real.rpow_def_of_pos hw0]; congr 1; ring

/-- From `ℓ W^{τ'} ≤ (k-1) δ` and `k - 1 ≤ W^{τ'/2}`: `ℓ W^{τ'/2} ≤ δ` and
`(W^{τ'/2}/k)² ≤ δ/ℓ` (the two thresholds used for `STKcalDecay` at length `2` and for the
exponential). -/
private theorem DecayLoopB_real_geom {Wr ℓ δ τ' kk : ℝ} (hW : 0 < Wr) (hℓ : 0 < ℓ) (hδ0 : 0 ≤ δ)
    (hk : 2 ≤ kk) (hWk : kk - 1 ≤ Wr ^ (τ' / 2)) (hδ : ℓ * Wr ^ τ' ≤ (kk - 1) * δ) :
    ℓ * Wr ^ (τ' / 2) ≤ δ ∧ (Wr ^ (τ' / 2) / kk) ^ 2 ≤ δ / ℓ := by
  have hs : 0 < Wr ^ (τ' / 2) := Real.rpow_pos_of_pos hW _
  have h1 : Wr ^ τ' = Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by
    rw [← Real.rpow_add hW]; congr 1; ring
  have hk1 : 0 < kk - 1 := by linarith
  constructor
  · have h2 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ (kk - 1) * δ := by
      calc ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ ℓ * Wr ^ (τ' / 2) * Wr ^ (τ' / 2) := by gcongr
        _ = ℓ * Wr ^ τ' := by rw [h1]; ring
        _ ≤ _ := hδ
    have h3 : ℓ * Wr ^ (τ' / 2) * (kk - 1) ≤ δ * (kk - 1) := by linarith
    exact le_of_mul_le_mul_right h3 hk1
  · have hkk : 0 < kk := by linarith
    rw [div_pow, div_le_div_iff₀ (by positivity) hℓ, ← Real.rpow_natCast, ← Real.rpow_mul hW.le]
    have h4 : (τ' / 2) * ((2 : ℕ) : ℝ) = τ' := by push_cast; ring
    rw [h4]
    calc Wr ^ τ' * ℓ = ℓ * Wr ^ τ' := mul_comm _ _
      _ ≤ (kk - 1) * δ := hδ
      _ ≤ kk ^ 2 * δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith
      _ = δ * kk ^ 2 := mul_comm _ _

/-- `|a - b|_{ℓ¹} ≤ KLmaxDist ![a, b]`. -/
private theorem DecayLoopB_zdistD_le_KLmaxDist_two {d L : ℕ} [NeZero L] (a b : Zd d L) :
    zdistD d L (a - b) ≤ KLmaxDist d L (![a, b] : Fin 2 → Zd d L) :=
  Finset.le_sup (f := fun q : Fin 2 × Fin 2 =>
    zdistD d L ((![a, b] : Fin 2 → Zd d L) q.1 - (![a, b] : Fin 2 → Zd d L) q.2))
    (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))

end Scales

section Main

/-- **The uniform far-loop decay, `k ≥ 2`** (the pointwise chain of `DecayLoopA_main` at the time
`v ∈ [s_n,t_n]` of the index).  The input is `STGdecayW` at `D = Q` and the far pair `c(σ,a)`; the
prefactor `((1-s)/(1-v))^{Cd} Bctl_v^{1/5} ≤ N^{max Cd 0 + 1}` follows from the far premise alone
(`1 - v ≥ N⁻¹`, `0 ≤ s ≤ v`, `Bctl_v ≤ 2`).  The union over the index is the inclusion of failure
events `badSetAt` (`StochDomAt.of_subset`): it is pointwise in `(v, σ, a)`. -/
private theorem DecayLoopB_main_u (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 Cd : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hdec : STGdecayW sz E s t Cd)
    {k : ℕ} (hk : 2 ≤ k) {τ' : ℝ} (hτ' : 0 < τ') {D' : ℝ} (hD' : 0 < D') :
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω =>
        (‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ)
          then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  -- constants
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 / 𝔠 := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℝ, C₀ = max Cd 0 + 1 := ⟨_, rfl⟩
  have hC₀ : 0 ≤ C₀ := by rw [hC₀def]; have := le_max_right Cd 0; linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * D' + A * (2 * ((k : ℝ) - 1) + 1 + C₀) + 1 := ⟨_, rfl⟩
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hQpos : 0 < Q := by
    have : 0 ≤ A * (2 * ((k : ℝ) - 1) + 1 + C₀) := mul_nonneg hA0 (by nlinarith)
    rw [hQ]; linarith
  -- choice of the far pair
  have hpair : ∀ (n : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ∃ c : Zd d (sz.L n) × Zd d (sz.L n),
        ((STdiamInf a : ℕ) : ℝ) ≤ ((k : ℝ) - 1) * (zdistInf d (sz.L n) (c.1 - c.2) : ℝ) ∧
        ∀ (H : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ) (z : ℂ) (η : ℝ),
          H.IsHermitian → 0 < η → η ≤ |z.im| →
          ‖loopL d (sz.L n) (sz.W n) H z (loopOf σ a)‖ ^ 2 ≤
            η⁻¹ ^ (2 * (k - 1)) *
              ‖loopL d (sz.L n) (sz.W n) H z ⟨[true, false], [c.1, c.2]⟩‖ :=
    fun n σ a => DecayLoopB_pair hk σ a
  choose cp hcp using hpair
  -- the pulled-back source (the uniform Step-2 decay at the far pair)
  have hpb0 := StochDomAt.precomp_param (V := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (hdec Q hQpos)
    (fun n p => (p.1, ![true, false], ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]))
  have hpb : Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) ![true, false]
          ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2] ω -
        STKloop sz n (E n) (p.1 : ℝ) ![true, false] ![(cp n p.2.1 p.2.2).1, (cp n p.2.1 p.2.2).2]‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ)
            (zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2)) *
          Real.exp (-(((zdistInf d (sz.L n) ((cp n p.2.1 p.2.2).1 - (cp n p.2.1 p.2.2).2) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Q)) := hpb0
  refine StochDomAt.of_subset hpb ?_
  intro τ₀ hτ₀
  refine ⟨1, one_pos, ?_⟩
  -- eventual facts
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have hK2 := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := 2) (by norm_num)
    (τ := τ' / 2) (D := Q) (by linarith) hQpos
  have hKk := RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := k) (by omega)
    (τ := τ') (D := D' + 1) hτ' (by linarith)
  have hexp := hWtend.eventually
    (DecayLoopB_exp_small (τ' := τ') hτ' (K := (k : ℝ)) (Q := Q) (by linarith) hQpos.le)
  have hW2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop 2
  have hWΓ : ∀ᶠ n : ℕ in atTop,
      16 * Γ ^ (2 * (k - 1)) * (2 + 2) ≤ ((sz.W n : ℕ) : ℝ) := hWtend.eventually_ge_atTop _
  have hWk : ∀ᶠ n : ℕ in atTop, (k : ℝ) - 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (τ' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < τ' / 2)).comp hWtend).eventually_ge_atTop _
  have hN2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hN.eventually_ge_atTop 2
  filter_upwards [hK2, hKk, hexp, hW2, hWΓ, hWk, hB, hWO, hN2] with n hK2n hKkn hexpn hW2n
    hWΓn hWkn hbwn hwo hN2n
  rintro ω ⟨⟨v, σ, a⟩, hlt⟩
  refine ⟨⟨v, σ, a⟩, ?_⟩
  by_contra hnot
  dsimp only at hlt hnot
  have hu0 : 0 ≤ (v : ℝ) := (hs0 n).trans v.2.1
  have hu1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 n)
  -- basic facts at the index n
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  -- not far: trivial
  by_cases hfar : ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
  swap
  · simp only [hfar, ↓reduceIte, mul_zero] at hlt
    have : 0 < ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') := by positivity
    linarith
  simp only [hfar, ↓reduceIte, mul_one] at hlt
  -- the scales: `g`, `1 - v`, `η`
  have hlam0 : 0 < sz.lam n :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (v : ℝ) := one_le_ellT hL1r
  have hℓpos : 0 < ellT (sz.L n) (sz.lam n) (v : ℝ) := by linarith
  have hWτ : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW1r hτ'.le
  have hdiam : (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) / 2 := by
    have := DecayLoopB_two_mul_diam_le a
    have h2 : (2 : ℝ) * (STdiamInf a : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hℓL : ellT (sz.L n) (sz.lam n) (v : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have h3 : (3 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast hL3
    calc ellT (sz.L n) (sz.lam n) (v : ℝ)
        ≤ ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' :=
          le_mul_of_one_le_right hℓpos.le hWτ
      _ ≤ (STdiamInf a : ℝ) := hfar
      _ ≤ ((sz.L n : ℕ) : ℝ) / 2 := hdiam
      _ < _ := by linarith
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (v : ℝ) :=
    DecayLoopB_one_sub_u (by omega) hL3 hW1 hlam0 hgW hu1 hℓL
  have hv : 0 < 1 - (v : ℝ) := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - (v : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  have hμ : Real.sqrt κ / 2 ≤ (mE (E n)).im := DecayLoopB_mE_im_ge hκ (hE n)
  have hη : 0 < etaT (E n) (v : ℝ) := by
    have : 0 < (mE (E n)).im := lt_of_lt_of_le (by positivity) hμ
    exact mul_pos hv this
  have hηΓ : (etaT (E n) (v : ℝ))⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - (v : ℝ)) * (Real.sqrt κ / 2) ≤ etaT (E n) (v : ℝ) :=
      mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (etaT (E n) (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ :=
      inv_anti₀ (by positivity) h1
    have h3 : ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ = Γ * (1 - (v : ℝ))⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - (v : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (etaT (E n) (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ := h2
      _ = Γ * (1 - (v : ℝ))⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  have hMi : STWB sz n (v : ℝ) (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2)) ≤ 2 :=
    DecayLoopB_STWB_le sz n _ hu1 hg1 hN1u
  -- the prefactor `((1-s)/(1-v))^{Cd} Bctl_v^{1/5} ≤ N^{C₀}` from the far premise
  have hPn : ((1 - s n) / (1 - (v : ℝ))) ^ Cd * (sz.Bctl n (v : ℝ)) ^ (1 / 5 : ℝ) ≤
      ((sz.size n : ℕ) : ℝ) ^ C₀ := by
    have hB2 : sz.Bctl n (v : ℝ) ≤ 2 := DecayLoopB_STWB_le sz n 0 hu1 hg1 hN1u
    have hB0 : 0 ≤ sz.Bctl n (v : ℝ) := DecayLoopB_STWB_nonneg sz n _ 0
    have hB5 : (sz.Bctl n (v : ℝ)) ^ (1 / 5 : ℝ) ≤ 2 :=
      calc (sz.Bctl n (v : ℝ)) ^ (1 / 5 : ℝ) ≤ (2 : ℝ) ^ (1 / 5 : ℝ) :=
            Real.rpow_le_rpow hB0 hB2 (by norm_num)
        _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hratio1 : 1 ≤ (1 - s n) / (1 - (v : ℝ)) := by
      rw [le_div_iff₀ hv]; linarith [v.2.1]
    have hratioN : (1 - s n) / (1 - (v : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [div_le_iff₀ hv]
      linarith [hs0 n]
    have hpow : ((1 - s n) / (1 - (v : ℝ))) ^ Cd ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
      calc ((1 - s n) / (1 - (v : ℝ))) ^ Cd ≤ ((1 - s n) / (1 - (v : ℝ))) ^ (max Cd 0) :=
            Real.rpow_le_rpow_of_exponent_le hratio1 (le_max_left _ _)
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) :=
            Real.rpow_le_rpow (by linarith) hratioN (le_max_right _ _)
    have hNC : ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) =
        ((sz.size n : ℕ) : ℝ) ^ (max Cd 0 + 1) := by
      rw [Real.rpow_add hNpos, Real.rpow_one]
    rw [hC₀def]
    calc ((1 - s n) / (1 - (v : ℝ))) ^ Cd * (sz.Bctl n (v : ℝ)) ^ (1 / 5 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * 2 :=
          mul_le_mul hpow hB5 (Real.rpow_nonneg hB0 _) (by positivity)
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (max Cd 0) * ((sz.size n : ℕ) : ℝ) := by gcongr
      _ = _ := hNC
  -- the matrix and the far pair
  have hMh : (sz.seqHflow n (v : ℝ) ω).IsHermitian := Sizes.seqHflow_isHermitian sz n (v : ℝ) ω
  have hHh : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω)).IsHermitian :=
    hMh.submatrix _
  have hzim : etaT (E n) (v : ℝ) ≤ |(zt (E n) (v : ℝ)).im| := by
    rw [← etaT_eq_zt_im, abs_of_pos hη]
  obtain ⟨hcmax, hcb⟩ := hcp n σ a
  have hΛ := hcb (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω)) (zt (E n) (v : ℝ))
    (etaT (E n) (v : ℝ)) hHh hη hzim
  have hδ : ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
      ((k : ℝ) - 1) * (zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℝ) :=
    hfar.trans hcmax
  obtain ⟨hfar2, hexarg⟩ := DecayLoopB_real_geom hWpos hℓpos (Nat.cast_nonneg _) hk2 hWkn hδ
  -- the bounds on the far pair
  have hKp : ‖STKloop sz n (E n) (v : ℝ) ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    refine hK2n (E n) (hE n) (v : ℝ) hu0 hu1 ![true, false]
      ![(cp n σ a).1, (cp n σ a).2] (hfar2.trans ?_)
    exact_mod_cast (zdistInf_le_zdistD d (sz.L n) _).trans
      (DecayLoopB_zdistD_le_KLmaxDist_two (cp n σ a).1 (cp n σ a).2)
  have hKc : ‖STKloop sz n (E n) (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(D' + 1)) :=
    hKkn (E n) (hE n) (v : ℝ) hu0 hu1 σ a
      (hfar.trans (by exact_mod_cast DecayLoopB_diam_le_KLmaxDist a))
  have hex : Real.exp (-(((zdistInf d (sz.L n) ((cp n σ a).1 - (cp n σ a).2) : ℕ) : ℝ) /
        ellT (sz.L n) (sz.lam n) (v : ℝ)) ^ (1 / 2 : ℝ)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Q) := by
    have := hexpn _ hexarg
    rwa [Real.sqrt_eq_rpow] at this
  have hL2 : Lloop sz n (E n) (v : ℝ) ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω))
        (zt (E n) (v : ℝ)) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩ := by
    refine (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ ![true, false]
      ![(cp n σ a).1, (cp n σ a).2]).trans ?_
    simp [loopOf, List.ofFn_succ]
  have hLσ : Lloop sz n (E n) (v : ℝ) σ a ω =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω))
        (zt (E n) (v : ℝ)) (loopOf σ a) :=
    loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  have hLp : ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω))
        (zt (E n) (v : ℝ)) ⟨[true, false], [(cp n σ a).1, (cp n σ a).2]⟩‖ ≤
      ‖STKloop sz n (E n) (v : ℝ) ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ +
        ‖Lloop sz n (E n) (v : ℝ) ![true, false] ![(cp n σ a).1, (cp n σ a).2] ω -
          STKloop sz n (E n) (v : ℝ) ![true, false] ![(cp n σ a).1, (cp n σ a).2]‖ := by
    rw [← hL2]
    exact norm_le_norm_add_norm_sub' _ _
  have hX := not_lt.mp hnot
  rw [Real.rpow_one] at hX
  have hNW : ((sz.size n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ A := by
    calc ((sz.size n : ℕ) : ℝ) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (1 / 𝔠) := by
          rw [← Real.rpow_mul hNpos.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one]
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) := Real.rpow_le_rpow (by positivity) hbwn (by positivity)
      _ = ((sz.W n : ℕ) : ℝ) ^ A := by rw [hAdef]
  have key := DecayLoopB_alg (W := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ)) (Γ := Γ)
    (Θ := 2) (A := A) (k := k) (D' := D') (C₀ := C₀) (Q := Q)
    (Λ := ‖Lloop sz n (E n) (v : ℝ) σ a ω‖) hk hC₀ hΓ0 (by norm_num) hW2n
    hWΓn hN1 hNW hQ (inv_nonneg.mpr hη.le) hηΓ (norm_nonneg _) (norm_nonneg _)
    (by rw [hLσ]; exact hΛ) hLp hKp hX hPn hMi hex (DecayLoopB_STWB_nonneg sz n _ _)
    (Real.exp_pos _).le hKc
  have hlk : ‖Lloop sz n (E n) (v : ℝ) σ a ω - STKloop sz n (E n) (v : ℝ) σ a‖ ≤
      ‖Lloop sz n (E n) (v : ℝ) σ a ω‖ + ‖STKloop sz n (E n) (v : ℝ) σ a‖ := norm_sub_le _ _
  have hNτ : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ := Real.one_le_rpow hN1 hτ₀.le
  have hWD : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_pos_of_pos hWpos _
  have hle : ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.size n : ℕ) : ℝ) ^ τ₀ * ((sz.W n : ℕ) : ℝ) ^ (-D') :=
    le_mul_of_one_le_left hWD.le hNτ
  linarith

end Main

section Targets

/-- **Target 3: `lem_decayLoop` over the window `[s,t]`, uniformly in `u`, from the uniform Step-2
decay** (T2135 Amend 1; the uniform form of `stDecayLoopPT_of_step2`, `DecayLoopA.lean:970`, with the
same hypotheses except that the per-time `STStep2DecayPT` is replaced by the uniform
`STGdecayW`, `(Eq:Gdecay_w)` uniformly in `u ∈ [s,t]`, `Step34Pins.lean:208`).  Along the flow `STFlow`
(`E = lemE z`) and `0 ≤ s ≤ t ≤ lemT z`, every `k ≥ 1`, `τ', D' > 0`:
`(|𝓛| + |𝓛-𝒦|)_{u,σ,a} 1(ℓ_u W^{τ'} ≤ diam_∞ a) ≺ W^{-D'}`, uniformly in `(u, σ, a)`.  The decay input is
used on the one event where it holds for every `u ∈ [s_n,t_n]` and every far pair; the deterministic
chain of `DecayLoopA` is applied at each `u` (`DecayLoopB_main_u`). -/
theorem stDecayLoopU_of_step2 (hd : 3 ≤ d) (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (hκ : 0 < κ) (hε : 0 < ε) (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n ≤ lemT (z n)) (Cd : ℝ)
    (hD : STGdecayW sz (STflowE z) s t Cd) : STDecayLoopU sz (STflowE z) s t := by
  intro k hk τ' hτ' D' hD'
  have him : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _)
      (hflow.2 n).2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (lemT_lt_one (him n))
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ := fun n =>
    (abs_lemE_le (him n)).trans (hflow.2 n).1
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · obtain rfl : k = 1 := by omega
    refine sz.prec_of_le (fun n p ω => ?_) (fun n p ω => ?_)
    · exact (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _).le
    · have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
        have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
      have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hpos : 0 < ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' :=
        mul_pos (ellT_pos hL) (Real.rpow_pos_of_pos hW _)
      have hmax : (STdiamInf p.2.2 : ℝ) = 0 := by
        rw [DecayLoopB_diam_one]; simp
      have hnot : ¬ (ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤
          (STdiamInf p.2.2 : ℝ)) := by
        rw [hmax]; exact not_le.mpr hpos
      simp only [hnot, ↓reduceIte, mul_zero]
      exact (Real.rpow_pos_of_pos hW _).le
  · exact DecayLoopB_main_u hd sz hκ hE' hflow.1 hs ht1 hD hk2 hτ' hD'

end Targets

end RBM.Gauss.Sizes

/-! ## 9. Target 2: the label decay of the four `ℰ`-terms (`stEtermDecay`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ}

section Good

/-- **The good event of the label decay** at size `n` (loop lengths `1 … K`, the scale `ℓ_u W^{τ'}`,
the decay level `W^{-D''}`): for every `u ∈ [s_n,t_n]`, charges and labels, `(|𝓛| + |𝓛-𝒦|)` is at most
`N W^{-D''}` when `ℓ_u W^{τ'} ≤ diam_∞ a`, and `|𝒦| ≤ N (W^{-d}B_{u,0})^{m-1}`. -/
private def DecayLoopB_Good (sz : Sizes d) (E s t : ℕ → ℝ) (K : ℕ) (τ' D'' : ℝ) (n : ℕ)
    (ω : sz.SeqΩ) : Prop :=
  ∀ m ∈ Finset.Icc 1 K, ∀ (v : TimeIcc s t n) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
    ((‖Lloop sz n (E n) (v : ℝ) σ a ω‖ +
        ‖Lloop sz n (E n) (v : ℝ) σ a ω - STKloop sz n (E n) (v : ℝ) σ a‖) *
      (if ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ)
        then 1 else 0) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) ∧
    ‖STKloop sz n (E n) (v : ℝ) σ a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n (v : ℝ)) ^ (m - 1)

/-- **The good event holds with high probability**: the intersection over the `K` loop lengths of
`Prec.whp` of `STDecayLoopU` (at `τ', D''`) and of `stKbound_timeIcc` (both at the exponent `τ = 1`),
by `HighProbAt.biInter` over the finite index set `[1, K]`. -/
private theorem DecayLoopB_whp_good (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hU : STDecayLoopU sz E s t) (K : ℕ) {τ' D'' : ℝ} (hτ' : 0 < τ') (hD'' : 0 < D'') :
    Whp sz (fun n => {ω | DecayLoopB_Good sz E s t K τ' D'' n ω}) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hN
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith) _) hn.1, hn.2⟩
  have hΞ : ∀ m : ↥(Finset.Icc 1 K), Whp sz (fun n =>
      {ω | ∀ u : TimeIcc s t n × (Fin m.1 → Bool) × (Fin m.1 → Zd d (sz.L n)),
          (‖Lloop sz n (E n) (u.1 : ℝ) u.2.1 u.2.2 ω‖ +
            ‖Lloop sz n (E n) (u.1 : ℝ) u.2.1 u.2.2 ω - STKloop sz n (E n) (u.1 : ℝ) u.2.1 u.2.2‖) *
          (if ellT (sz.L n) (sz.lam n) (u.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf u.2.2 : ℝ)
            then 1 else 0) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')} ∩
      {ω | ∀ u : TimeIcc s t n × (Fin m.1 → Bool) × (Fin m.1 → Zd d (sz.L n)),
          ‖STKloop sz n (E n) (u.1 : ℝ) u.2.1 u.2.2‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * (sz.Bctl n (u.1 : ℝ)) ^ (m.1 - 1)}) := by
    intro m
    have hm1 : 1 ≤ m.1 := (Finset.mem_Icc.1 m.2).1
    refine HighProbAt.inter hsize ?_ ?_
    · exact Prec.whp sz (hU m.1 hm1 τ' hτ' D'' hD'') (τ := 1) one_pos
    · exact Prec.whp sz (stKbound_timeIcc sz hd hκ (inv_pos.2 h𝔡) hN (Eventually.of_forall hE) hlam
        hs0 hst ht1 m.1 hm1) (τ := 1) one_pos
  have hbi := HighProbAt.biInter (P := seqP sz) (size := sz.size)
    (K := fun _ => ↥(Finset.Icc 1 K)) (C := 1) zero_le_one
    (by
      filter_upwards [hN.eventually_ge_atTop (K : ℝ)] with n hn
      rw [Real.rpow_one, Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel]
      exact hn)
    (fun D hD => Filter.eventually_all.2 fun m => hΞ m D hD)
  refine HighProbAt.mono hbi (Eventually.of_forall fun n ω hω => ?_)
  intro m hm v σ a
  have := Set.mem_iInter.1 hω ⟨m, hm⟩
  exact ⟨this.1 (v, σ, a), this.2 (v, σ, a)⟩

end Good

section Ctx

open RBM.Ind (norm_gloop_le_of_le_abs_im LoopDecay DecayLoopB_loopDecay_of DecayLoopB_bound_of
  DecayLoopB_det_egt DecayLoopB_det_ksimLK DecayLoopB_det_elklk DecayLoopB_det_ee)

/-- `STLI` of a `loopOf` index is the loop `𝓛^{(m)}_{u,σ,a}`. -/
private theorem DecayLoopB_STLI_eq (sz : Sizes d) (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    sz.STLI n E τ ω (loopOf σ a) = Lloop sz n E τ σ a ω :=
  (loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a).symm

/-- `(𝓛-𝒦)` of a `loopOf` index. -/
private theorem DecayLoopB_STLKI_eq (sz : Sizes d) (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    sz.STLKI n E τ ω (loopOf σ a) = Lloop sz n E τ σ a ω - STKloop sz n E τ σ a := by
  unfold STLKI STKI STKloop
  rw [DecayLoopB_STLI_eq]; rfl

/-- `𝒦` of a `loopOf` index. -/
private theorem DecayLoopB_STKI_eq (sz : Sizes d) (n : ℕ) (E τ : ℝ) {m : ℕ}
    (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) :
    sz.STKI n E τ (loopOf σ a) = STKloop sz n E τ σ a := rfl

/-- **The `𝒦` decay bundle** at size `n`: `STKcalDecay` (`inst_stKcalDecay_admissible`) for every loop
length `1 … K`, at the exponents `(τ, D)`. -/
private def DecayLoopB_KDec (sz : Sizes d) (κ : ℝ) (K : ℕ) (τ D : ℝ) (n : ℕ) : Prop :=
  ∀ j ∈ Finset.Icc 1 K, ∀ E' : ℝ, |E'| ≤ 2 - κ → ∀ u : ℝ, 0 ≤ u → u < 1 →
    ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ ≤ (KLmaxDist d (sz.L n) a : ℝ) →
        ‖KLK d (sz.L n) (sz.lam n) (sz.W n) E' u (KLloopOf d (sz.L n) σ a)‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ (-D)

private theorem DecayLoopB_KDec_ev (hd : 3 ≤ d) (sz : Sizes d) {𝔠 𝔡 κ : ℝ}
    (hA : sz.Admissible 𝔠 𝔡) (hκ : 0 < κ) (K : ℕ) {τ D : ℝ} (hτ : 0 < τ) (hD : 0 < D) :
    ∀ᶠ n in atTop, DecayLoopB_KDec sz κ K τ D n := by
  unfold DecayLoopB_KDec
  rw [Filter.eventually_all_finset]
  intro j hj
  exact RBM.Gauss.KDecayInst.inst_stKcalDecay_admissible hd sz hA hκ (k := j)
    (Finset.mem_Icc.1 hj).1 hτ hD

/-- `W^{-(D' + e/c)} N^e ≤ W^{-D'}` from `N^c ≤ W` (RBM2D `bcalEDecay_WD`, `BcalEDecay.lean:748`). -/
private theorem DecayLoopB_WD {N W c D' e : ℝ} (hN : 0 ≤ N) (hW : 0 < W) (hc : 0 < c)
    (he : 0 ≤ e) (hNW : N ^ c ≤ W) : W ^ (-(D' + e / c)) * N ^ e ≤ W ^ (-D') := by
  have h1 : N ^ e ≤ W ^ (e / c) := by
    calc N ^ e = (N ^ c) ^ (e / c) := by
          rw [← Real.rpow_mul hN]; congr 1; field_simp
      _ ≤ W ^ (e / c) := Real.rpow_le_rpow (Real.rpow_nonneg hN _) hNW (div_nonneg he hc.le)
  have h2 : W ^ (-(D' + e / c)) = W ^ (-D') * (W ^ (e / c))⁻¹ := by
    rw [show -(D' + e / c) = -D' + -(e / c) by ring, Real.rpow_add hW, Real.rpow_neg hW.le (e / c)]
  rw [h2]
  have h3 : 0 < W ^ (e / c) := Real.rpow_pos_of_pos hW _
  have h4 : 0 ≤ W ^ (-D') * (W ^ (e / c))⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hW.le _) (inv_nonneg.2 h3.le)
  calc W ^ (-D') * (W ^ (e / c))⁻¹ * N ^ e ≤ W ^ (-D') * (W ^ (e / c))⁻¹ * W ^ (e / c) :=
        mul_le_mul_of_nonneg_left h1 h4
    _ = W ^ (-D') := by field_simp

/-- **The final count**: `4 k² N (δ B') ≤ W^{-D}` for `δ = N W^{-D''}`, `B' = 2 (2ΓN)^{2k+2}`,
`D'' = D + 1 + (2k+4)/𝔠`, `N^𝔠 ≤ W` and `8 k² (2Γ)^{2k+2} ≤ W`. -/
private theorem DecayLoopB_arith {N W Γ 𝔠 D D'' : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hΓ : 0 ≤ Γ) (hW : 0 < W)
    (h𝔠 : 0 < 𝔠) (hNW : N ^ 𝔠 ≤ W) (hCk : 8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2) ≤ W)
    (hD'' : D'' = D + 1 + ((2 * k + 4 : ℕ) : ℝ) / 𝔠) :
    4 * (k : ℝ) ^ 2 * N * ((N ^ (1 : ℝ) * W ^ (-D'')) * (2 * (2 * Γ * N) ^ (2 * k + 2))) ≤
      W ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hWD := DecayLoopB_WD (D' := D + 1) (e := ((2 * k + 4 : ℕ) : ℝ)) hN0.le hW h𝔠
    (Nat.cast_nonneg _) hNW
  rw [← hD'', Real.rpow_natCast] at hWD
  have hrew : 4 * (k : ℝ) ^ 2 * N * ((N ^ (1 : ℝ) * W ^ (-D'')) * (2 * (2 * Γ * N) ^ (2 * k + 2))) =
      (8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2)) * (W ^ (-D'') * N ^ (2 * k + 4)) := by
    rw [Real.rpow_one, mul_pow]
    ring
  rw [hrew]
  have hWp : 0 < W ^ (-(D + 1)) := Real.rpow_pos_of_pos hW _
  have hC0 : 0 ≤ 8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2) := by positivity
  calc (8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2)) * (W ^ (-D'') * N ^ (2 * k + 4))
      ≤ (8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2)) * W ^ (-(D + 1)) :=
        mul_le_mul_of_nonneg_left hWD hC0
    _ ≤ W * W ^ (-(D + 1)) := mul_le_mul_of_nonneg_right hCk hWp.le
    _ = W ^ (-D) := by
        rw [show -(D + 1) = -D + -1 by ring, Real.rpow_add hW, Real.rpow_neg_one]
        field_simp

/-- **From the `ℓ¹` far premise of `EKFastDecay` to the `l^∞` far pair**: if
`W^ε ℓ ≤ |x|_{ℓ¹}` with `W^ε = X²` and `X ≥ 3d`, `ℓ ≥ 1`, then `2 ℓ X + 1 ≤ |x|_∞` (since
`|x|_{ℓ¹} ≤ d |x|_∞`) and `ℓ < L` (since `2 |x|_∞ ≤ L`). -/
private theorem DecayLoopB_far_facts {L : ℕ} [NeZero L] (hd : 1 ≤ d) {X ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (hX : 3 * (d : ℝ) ≤ X) (x : Zd d L) (hx : X * X * ℓ ≤ (zdistD d L x : ℝ)) (hL : 3 ≤ L) :
    2 * (ℓ * X) + 1 ≤ (zdistInf d L x : ℝ) ∧ ℓ < (L : ℝ) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hX3 : 3 ≤ X := by linarith
  have hD : (zdistD d L x : ℝ) ≤ d * zdistInf d L x := by
    exact_mod_cast zdistD_le_mul_zdistInf d L x
  have hL2 : 2 * (zdistInf d L x : ℝ) ≤ L := by
    exact_mod_cast DecayLoopB_two_mul_zdistInf_le x
  have hXℓ : 0 ≤ X * ℓ := by positivity
  have h1 : 3 * (d : ℝ) * (X * ℓ) ≤ X * X * ℓ := by nlinarith
  have h2 : 3 * (X * ℓ) ≤ (zdistInf d L x : ℝ) := by
    have h3 : (d : ℝ) * (3 * (X * ℓ)) ≤ d * zdistInf d L x := by nlinarith
    exact le_of_mul_le_mul_left h3 hd0
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  constructor
  · nlinarith
  · nlinarith

/-- **The context at `(n, u, ω)` for a far label vector** (`ℓ_u < L`): from the good event and the
decay of `𝒦` (`DecayLoopB_KDec`), `𝓛`, `𝓛-𝒦`, `𝒦` have `(R, δ)` decay on loops of length `≤ K`
(`R = ℓ_u W^{τ'}`, `δ = N W^{-D''}`) and `𝓛`, `𝒦` are `≤ B_c = (2ΓN)^K` there (`η_u^{-1} ≤ ΓN` and
`W^{-d}B_{u,0} ≤ 2`, both from `ℓ_u < L`, i.e. `1 - u ≥ N⁻¹`). -/
private theorem DecayLoopB_ctx (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔡 : ℝ} {E s t : ℕ → ℝ} (hκ : 0 < κ)
    (hE : ∀ n, |E n| ≤ 2 - κ) (hs0 : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (h𝔡 : 0 < 𝔡)
    {K : ℕ} {τ' D'' : ℝ} {n : ℕ} (v : TimeIcc s t n) (ω : sz.SeqΩ)
    (hwo : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2 + 𝔡) ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹)
    (hKd : DecayLoopB_KDec sz κ K τ' D'' n) (hG : DecayLoopB_Good sz E s t K τ' D'' n ω)
    (hℓL : ellT (sz.L n) (sz.lam n) (v : ℝ) < ((sz.L n : ℕ) : ℝ))
    {R δ Bc : ℝ} (hR : R = ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ')
    (hδ : δ = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))
    (hBc : Bc = (2 * (2 / Real.sqrt κ) * ((sz.size n : ℕ) : ℝ)) ^ K) :
    LoopDecay d (sz.L n) K R δ (sz.STLI n (E n) (v : ℝ) ω) ∧
    LoopDecay d (sz.L n) K R δ (sz.STLKI n (E n) (v : ℝ) ω) ∧
    LoopDecay d (sz.L n) K R δ (sz.STKI n (E n) (v : ℝ)) ∧
    (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
      ‖sz.STLI n (E n) (v : ℝ) ω J‖ ≤ Bc) ∧
    (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ K →
      ‖sz.STKI n (E n) (v : ℝ) J‖ ≤ Bc) := by
  have hu0 : 0 ≤ (v : ℝ) := (hs0 n).trans v.2.1
  have hu1 : (v : ℝ) < 1 := v.2.2.trans_lt (ht1 n)
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast hW1
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (v : ℝ) :=
    DecayLoopB_one_sub_u (by omega) hL3 hW1 hlam0 hgW hu1 hℓL
  have hv : 0 < 1 - (v : ℝ) := by linarith
  have hN1u : 1 ≤ ((sz.size n : ℕ) : ℝ) * (1 - (v : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hNu hNpos.le
    rwa [mul_inv_cancel₀ hNpos.ne'] at this
  -- `Γ = 2/√κ ≥ 1`
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hκ2 : κ ≤ 2 := by have := hE n; have := abs_nonneg (E n); linarith
  have hsq2 : Real.sqrt κ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hΓ1 : 1 ≤ Γ := by
    rw [hΓ, le_div_iff₀ hsqκ]; linarith
  rw [← hΓ] at hBc
  have hμ : Real.sqrt κ / 2 ≤ (mE (E n)).im := DecayLoopB_mE_im_ge hκ (hE n)
  have hη : 0 < etaT (E n) (v : ℝ) := by
    have : 0 < (mE (E n)).im := lt_of_lt_of_le (by positivity) hμ
    exact mul_pos hv this
  have hηΓ : (etaT (E n) (v : ℝ))⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by
    have h1 : (1 - (v : ℝ)) * (Real.sqrt κ / 2) ≤ etaT (E n) (v : ℝ) :=
      mul_le_mul_of_nonneg_left hμ hv.le
    have h2 : (etaT (E n) (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ :=
      inv_anti₀ (by positivity) h1
    have h3 : ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ = Γ * (1 - (v : ℝ))⁻¹ := by
      rw [hΓ]; field_simp
    have h4 : (1 - (v : ℝ))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (etaT (E n) (v : ℝ))⁻¹ ≤ ((1 - (v : ℝ)) * (Real.sqrt κ / 2))⁻¹ := h2
      _ = Γ * (1 - (v : ℝ))⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  have hBctl : sz.Bctl n (v : ℝ) ≤ 2 := DecayLoopB_STWB_le sz n 0 hu1 hg1 hN1u
  have hBctl0 : 0 ≤ sz.Bctl n (v : ℝ) := DecayLoopB_STWB_nonneg sz n _ 0
  have hΘ : 2 ≤ 2 * Γ * ((sz.size n : ℕ) : ℝ) := by nlinarith
  have hWD0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact hN1
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  -- decay of `𝓛` and `𝓛 - 𝒦`
  have hgood : ∀ m ∈ Finset.Icc 1 K, ∀ (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
      R ≤ (STdiamInf a : ℝ) →
      ‖Lloop sz n (E n) (v : ℝ) σ a ω‖ + ‖Lloop sz n (E n) (v : ℝ) σ a ω -
        STKloop sz n (E n) (v : ℝ) σ a‖ ≤ δ := by
    intro m hm σ a hRa
    have h := (hG m hm v σ a).1
    have hRa' : ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) := by
      rw [← hR]; exact hRa
    simp only [hRa', ↓reduceIte, mul_one] at h
    rw [hδ]; exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [DecayLoopB_STLI_eq]
    have := hgood m hm σ a hRa
    linarith [norm_nonneg (Lloop sz n (E n) (v : ℝ) σ a ω - STKloop sz n (E n) (v : ℝ) σ a)]
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [DecayLoopB_STLKI_eq]
    have := hgood m hm σ a hRa
    linarith [norm_nonneg (Lloop sz n (E n) (v : ℝ) σ a ω)]
  · refine DecayLoopB_loopDecay_of _ fun m hm σ a hRa => ?_
    rw [DecayLoopB_STKI_eq]
    have hKm := hKd m hm (E n) (hE n) (v : ℝ) hu0 hu1 σ a (by
      rw [← hR]; exact hRa.trans (by exact_mod_cast DecayLoopB_diam_le_KLmaxDist a))
    have : ‖STKloop sz n (E n) (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := hKm
    rw [hδ]
    calc ‖STKloop sz n (E n) (v : ℝ) σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := this
      _ = 1 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hN1' hWD0
  · -- `‖𝓛_u(J)‖ ≤ η_u^{-|J|} ≤ (ΓN)^{|J|} ≤ B_c`
    intro J hJ hJ1 hJK
    have hMh : (sz.seqHflow n (v : ℝ) ω).IsHermitian := Sizes.seqHflow_isHermitian sz n (v : ℝ) ω
    have hHh : (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω)).IsHermitian :=
      hMh.submatrix _
    have hzim : etaT (E n) (v : ℝ) ≤ |(zt (E n) (v : ℝ)).im| := by
      rw [← etaT_eq_zt_im, abs_of_pos hη]
    have hg := norm_gloop_le_of_le_abs_im (z := zt (E n) (v : ℝ)) (W := sz.W n) hHh hη hzim J hJ hJ1
    have hWinv : (((((sz.W n : ℕ) : ℝ) ^ d)⁻¹)) ^ (J.a.length - 1) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW1r))
    have hΓN1 : 1 ≤ Γ * ((sz.size n : ℕ) : ℝ) := by nlinarith
    change ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω))
        (zt (E n) (v : ℝ)) J‖ ≤ Bc
    rw [hBc]
    calc ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflow n (v : ℝ) ω))
          (zt (E n) (v : ℝ)) J‖
        ≤ (etaT (E n) (v : ℝ))⁻¹ ^ J.a.length * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (J.a.length - 1) := hg
      _ ≤ (Γ * ((sz.size n : ℕ) : ℝ)) ^ J.a.length * 1 := by
          refine mul_le_mul (pow_le_pow_left₀ (inv_nonneg.2 hη.le) hηΓ _) hWinv (by positivity)
            (by positivity)
      _ ≤ (Γ * ((sz.size n : ℕ) : ℝ)) ^ K := by
          rw [mul_one]; exact pow_le_pow_right₀ hΓN1 hJK
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ K := by
          refine pow_le_pow_left₀ (by positivity) ?_ K
          nlinarith
  · -- `‖𝒦_u(J)‖ ≤ N (W^{-d}B_{u,0})^{|J|-1} ≤ N 2^{|J|-1} ≤ B_c`
    refine DecayLoopB_bound_of _ (K := K) fun m hm σ a => ?_
    rw [DecayLoopB_STKI_eq]
    have hm' := Finset.mem_Icc.1 hm
    have h := (hG m hm v σ a).2
    rw [Real.rpow_one] at h
    rw [hBc]
    have hΘ1 : (1 : ℝ) ≤ 2 * Γ * ((sz.size n : ℕ) : ℝ) := by linarith
    calc ‖STKloop sz n (E n) (v : ℝ) σ a‖
        ≤ ((sz.size n : ℕ) : ℝ) * (sz.Bctl n (v : ℝ)) ^ (m - 1) := h
      _ ≤ ((sz.size n : ℕ) : ℝ) * 2 ^ (m - 1) := by gcongr
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) * (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ (m - 1) := by
          refine mul_le_mul (by nlinarith) (pow_le_pow_left₀ (by norm_num) hΘ _) (by positivity)
            (by positivity)
      _ = (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ m := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ K := pow_le_pow_right₀ hΘ1 hm'.2

end Ctx

section Master

open RBM.Ind (LoopDecay DecayLoopB_det_egt DecayLoopB_det_ksimLK DecayLoopB_det_elklk
  DecayLoopB_det_ee DecayLoopB_avgErr_eq DecayLoopB_size_eq)

/-- **The four label-decay statements at once, with high probability.**  Parameters: `τ' = ε/2`,
`D'' = D + 1 + (2k+4)/𝔠`.  On the good event (`DecayLoopB_Good`, `K = 2k+2`) and eventually in `n`,
for every `u ∈ [s_n,t_n]`, every charge vector and every far label vector, the four `ℰ`-terms are
`≤ W^{-D}`:  `4 k² N (δ B') ≤ W^{-D}` with `δ = N W^{-D''}`, `B' = 2 (2ΓN)^{2k+2}`
(`DecayLoopB_arith`). -/
private theorem DecayLoopB_master (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hU : STDecayLoopU sz E s t) {k : ℕ} (hk : 2 ≤ k) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    Whp sz (fun n => {ω | ∀ v : TimeIcc s t n,
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          sz.STegt n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ (σ : Fin k → Bool) (l : ℕ), EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          sz.STksimLK n (E n) (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun a : Fin k → Zd d (sz.L n) =>
          sz.STelklk n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩)) ∧
      (∀ σ : Fin k → Bool, EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D
        (fun b : Fin (k + k) → Zd d (sz.L n) =>
          sz.STee n (E n) (v : ℝ) ω σ (fun i => b (Fin.castAdd k i))
            (fun i => b (Fin.natAdd k i))))}) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = 2 / Real.sqrt κ := ⟨_, rfl⟩
  obtain ⟨D'', hD''⟩ : ∃ D'' : ℝ, D'' = D + 1 + ((2 * k + 4 : ℕ) : ℝ) / 𝔠 := ⟨_, rfl⟩
  have hD''0 : 0 < D'' := by rw [hD'']; positivity
  have hτ' : 0 < ε / 2 := half_pos hε
  have hW := DecayLoopB_whp_good hd sz hκ hE hA hs0 hst ht1 hU (2 * k + 2) hτ' hD''0
  refine HighProbAt.mono hW ?_
  have hsqκ : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hWtend : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
      (tendsto_rpow_atTop h𝔠).comp hN
    exact tendsto_atTop_mono' _ hB h1
  have e1 : ∀ᶠ n in atTop, 3 * (d : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop hτ').comp hWtend).eventually_ge_atTop _
  have e2 := DecayLoopB_KDec_ev hd sz hA hκ (2 * k + 2) hτ' hD''0
  have e3 : ∀ᶠ n in atTop, 8 * (k : ℝ) ^ 2 * (2 * Γ) ^ (2 * k + 2) ≤ ((sz.W n : ℕ) : ℝ) :=
    hWtend.eventually_ge_atTop _
  filter_upwards [e1, e2, e3, hB, hWO] with n he1 he2 he3 hbw hwo
  intro ω hω v
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hX : ((sz.W n : ℕ) : ℝ) ^ ε = ((sz.W n : ℕ) : ℝ) ^ (ε / 2) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) (v : ℝ) := one_le_ellT hL1r
  -- the explicit constants
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ellT (sz.L n) (sz.lam n) (v : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
    ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
    ⟨_, rfl⟩
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ,
      Bc = (2 * (2 / Real.sqrt κ) * ((sz.size n : ℕ) : ℝ)) ^ (2 * k + 2) := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hBc1 : 1 ≤ Bc := by
    have hκ2 : κ ≤ 2 := by have := hE n; have := abs_nonneg (E n); linarith
    have hsq2 : Real.sqrt κ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
    have hΓ1 : 1 ≤ Γ := by rw [hΓ, le_div_iff₀ hsqκ]; linarith
    rw [hBc, ← hΓ]
    exact one_le_pow₀ (by nlinarith)
  -- the package at a far label vector
  have hpkg : ∀ x : Zd d (sz.L n),
      ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) (v : ℝ) ≤ (zdistD d (sz.L n) x : ℝ) →
      2 * R + 1 ≤ (zdistInf d (sz.L n) x : ℝ) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (sz.STLI n (E n) (v : ℝ) ω) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (sz.STLKI n (E n) (v : ℝ) ω) ∧
      LoopDecay d (sz.L n) (2 * k + 2) R δ (sz.STKI n (E n) (v : ℝ)) ∧
      (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
        ‖sz.STLI n (E n) (v : ℝ) ω J‖ ≤ Bc) ∧
      (∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ 2 * k + 2 →
        ‖sz.STKI n (E n) (v : ℝ) J‖ ≤ Bc) := by
    intro x hx
    have hff := DecayLoopB_far_facts (by omega : 1 ≤ d) hℓ1 he1 x (by rw [← hX]; exact hx) hL3
    refine ⟨by rw [hR]; exact hff.1, ?_⟩
    exact DecayLoopB_ctx hd sz hκ hE hs0 ht1 h𝔡 v ω hwo he2 hω hff.2 hR hδ hBc
  -- the final count
  have hfin : 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
      (δ * (2 * Bc)))) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    have := DecayLoopB_arith (N := ((sz.size n : ℕ) : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (Γ := Γ)
      (𝔠 := 𝔠) (D := D) (D'' := D'') (k := k) hN1 hΓ0 hWpos h𝔠 hbw he3 hD''
    have hNe := DecayLoopB_size_eq sz n
    have hprod : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) =
        ((sz.size n : ℕ) : ℝ) * (δ * (2 * Bc)) := by rw [← mul_assoc, ← hNe]
    rw [hprod, hδ, hBc, ← hΓ]
    calc _ = 4 * (k : ℝ) ^ 2 * ((sz.size n : ℕ) : ℝ) *
          ((((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) *
            (2 * (2 * Γ * ((sz.size n : ℕ) : ℝ)) ^ (2 * k + 2))) := by ring
      _ ≤ _ := this
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hMv0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) := by
    have : 0 ≤ Bc := by linarith
    positivity
  have hB'1 : 1 ≤ 2 * Bc := by linarith
  have hk4 : (k : ℝ) ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  have hk24 : 2 * (k : ℝ) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ℰ^{G̃}`
    intro σ a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have havg : ∀ (s' : Bool) (a' : Zd d (sz.L n)),
        ‖sz.STavgErr n (E n) (v : ℝ) ω s' a'‖ ≤ 2 * Bc := by
      intro s' a'
      rw [DecayLoopB_avgErr_eq]
      have hJ : (⟨[s'], [a']⟩ : LoopIdx (Zd d (sz.L n))).WF := by simp [LoopIdx.WF]
      have hl1 : (⟨[s'], [a']⟩ : LoopIdx (Zd d (sz.L n))).length = 1 := by simp [LoopIdx.length]
      have h1 := hLb _ hJ (by omega) (by omega)
      have h2 := hKb _ hJ (by omega) (by omega)
      unfold STLKI
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := DecayLoopB_det_egt (sz := sz) (n := n) (E := E n) (τ := (v : ℝ)) (ω := ω)
      hL3 (R := R) (δ := δ) (B := 2 * Bc) hδ0 (by linarith) havg
      (LoopDecay.mono hdLL (by omega) le_rfl le_rfl) σ a (i := i) (j := j) (by linarith)
    refine hdet.trans ?_
    calc _ = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc)))) := by
          ring
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk4 hMv0
      _ ≤ _ := hfin
  · -- `[𝒦^{(l)} ∼ (𝓛-𝒦)]`
    intro σ l a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
        ‖sz.STLKI n (E n) (v : ℝ) ω J‖ ≤ 2 * Bc := by
      intro J hJ h1 h2
      have a1 := hLb J hJ h1 (by omega)
      have a2 := hKb J hJ h1 (by omega)
      unfold STLKI
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := DecayLoopB_det_ksimLK (sz := sz) (n := n) (E := E n) (τ := (v : ℝ)) (ω := ω)
      hL3 (R := R) (δ := δ) (B := 2 * Bc) hδ0 hLKb
      (fun J hJ h1 h2 => (hKb J hJ h1 (by omega)).trans (by linarith))
      (LoopDecay.mono hdLK (by omega) le_rfl le_rfl) (LoopDecay.mono hdK (by omega) le_rfl le_rfl)
      σ a (i := i) (j := j) hfar l
    refine hdet.trans ?_
    calc _ = 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := by ring
      _ ≤ _ := hfin
  · -- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦)}`
    intro σ a ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (a i - a j) hij
    have hLKb : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 1 ≤ J.length → J.length ≤ k →
        ‖sz.STLKI n (E n) (v : ℝ) ω J‖ ≤ 2 * Bc := by
      intro J hJ h1 h2
      have a1 := hLb J hJ h1 (by omega)
      have a2 := hKb J hJ h1 (by omega)
      unfold STLKI
      refine (norm_sub_le _ _).trans ?_
      linarith
    have hdet := DecayLoopB_det_elklk (sz := sz) (n := n) (E := E n) (τ := (v : ℝ)) (ω := ω)
      hL3 (R := R) (δ := δ) (B := 2 * Bc) hδ0 hLKb
      (LoopDecay.mono hdLK (by omega) le_rfl le_rfl) σ a (i := i) (j := j) hfar
    refine hdet.trans ?_
    calc _ = 2 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := by ring
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk24 hMv0
      _ ≤ _ := hfin
  · -- `(ℰ⊗ℰ)^M`
    intro σ b ⟨i, j, hij⟩
    obtain ⟨hfar, hdLL, hdLK, hdK, hLb, hKb⟩ := hpkg (b i - b j) hij
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    have hb : Fin.append (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)) = b :=
      Fin.append_castAdd_natAdd
    have hdet := DecayLoopB_det_ee (sz := sz) (n := n) (E := E n) (τ := (v : ℝ)) (ω := ω)
      hL3 (R := R) (δ := δ) hδ0 hdLL σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))
      (i := i) (j := j) (by rw [hb]; linarith)
    refine hdet.trans ?_
    calc _ = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * δ := by ring
      _ ≤ (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc)))) := by
          have h1 : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ ≤
              ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (δ * (2 * Bc))) := by
            have h0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by positivity
            calc ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ
                = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ * 1 := (mul_one _).symm
              _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ * (2 * Bc) :=
                  mul_le_mul_of_nonneg_left hB'1 (by positivity)
              _ = _ := by ring
          calc (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * δ
              = (k : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d * δ) := by ring
            _ ≤ (k : ℝ) * _ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 4 * (k : ℝ) ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d *
            (δ * (2 * Bc)))) := mul_le_mul_of_nonneg_right hk4 hMv0
      _ ≤ _ := hfin

end Master

section Target2

/-- **Target 2: the label decay of the four `ℰ`-terms of `lem:SEforLn`** (`3_5:1017-1065`, `Def_decay`
`3_5:1115`, `lem_decayLoop`).  From the uniform decay of the loops `STDecayLoopU sz E s t` (S3-07a, in
the uniform form of target 3), the decay of `𝒦` (`inst_stKcalDecay_admissible`, `KDecay.lean`, for the far `𝒦` factors) and
`stKbound_timeIcc` (the crude bound of the other `𝒦` factor), for every loop length `k ≥ 2` and
charges `σ`, the tensors of labels of

* `ℰ^{G̃,(k)}` (`STegt`), `a ↦ STegt … ⟨σ, a⟩`;
* `[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(k)}` (`STksimLK`), every `l`;
* `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}` (`STelklk`);
* `(ℰ⊗ℰ)^{M,(k)}` (`STee`), as a tensor of the `2k` labels `(a, a')`, `b ↦ STee … (b ∘ castAdd) (b ∘ natAdd)`,

satisfy `STEKDecay sz s t 𝒜` (`Step34Pins.lean:595`, `(deccA0)` w.h.p. for every `ε, D > 0`, uniformly
in `v ∈ [s_n,t_n]`).  The `l¹` far premise `W^ε ℓ_v ≤ max |a_i - a_j|_{ℓ¹}` of `EKFastDecay` is converted to
the `l^∞` spread `≥ 2ℓ_v W^{ε/2} + 1` (`|x|_{ℓ¹} ≤ d |x|_∞`, `W^{ε/2} ≥ 3d` eventually), so `STDecayLoopU`
is used with `τ' = ε/2` and `D'' = D + 1 + (2k+4)/𝔠`.  The paper's range `3 ≤ l ≤ k` of the second term is
widened to every `l`.  Hypotheses: those of Step 3's setting that the decay needs (`|E| ≤ 2 - κ`,
`Admissible 𝔠 𝔡`, `0 ≤ s ≤ t < 1`); `3 ≤ d` enters through `STKcalDecay`. -/
theorem stEtermDecay (hd : 3 ≤ d) (sz : Sizes d) {κ 𝔠 𝔡 : ℝ} {E s t : ℕ → ℝ}
    (hκ : 0 < κ) (hE : ∀ n, |E n| ≤ 2 - κ) (hA : sz.Admissible 𝔠 𝔡)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hU : STDecayLoopU sz E s t) (k : ℕ) (hk : 2 ≤ k) (σ : Fin k → Bool) :
    STEKDecay sz s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        sz.STegt n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    (∀ l : ℕ, STEKDecay sz s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        sz.STksimLK n (E n) (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
    STEKDecay sz s t (m := k)
      (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
        sz.STelklk n (E n) (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    STEKDecay sz s t (m := k + k)
      (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) => sz.STee n (E n) (v : ℝ) ω σ (fun i => b (Fin.castAdd k i))
        (fun i => b (Fin.natAdd k i))) := by
  have key := fun ε D (hε : 0 < ε) (hD : 0 < D) =>
    DecayLoopB_master hd sz hκ hE hA hs0 hst ht1 hU hk hε hD
  refine ⟨fun ε D hε hD => ?_, fun l ε D hε hD => ?_, fun ε D hε hD => ?_, fun ε D hε hD => ?_⟩
  · exact HighProbAt.mono (key ε D hε hD) (Eventually.of_forall fun n ω hω v => (hω v).1 σ)
  · exact HighProbAt.mono (key ε D hε hD) (Eventually.of_forall fun n ω hω v => (hω v).2.1 σ l)
  · exact HighProbAt.mono (key ε D hε hD) (Eventually.of_forall fun n ω hω v => (hω v).2.2.1 σ)
  · exact HighProbAt.mono (key ε D hε hD) (Eventually.of_forall fun n ω hω v => (hω v).2.2.2 σ)

end Target2

end RBM.Gauss.Sizes

/-! ## 10. Compiled nonempty instances (`d = 3`)

Target 1 is applied on a concrete loop at `d = 3`, `L = 5`: `σ = (+,-,+)`, `a = (0, (2,2,2), 0)`, whose
labels `0` and `(2,2,2)` are at `l^∞` distance `2 = 2 (1/2) + 1`, with a concrete loop function of exact
`(1/2, 1/10)` decay (`1` on the constant loops, `1/10` elsewhere); every hypothesis is discharged.
Targets 3 and 2 are applied at the merged flow instance `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`,
`lam = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)`, `flow_z0`), window `[0, 1/16]`; the decay inputs
(`STGdecayW`, resp. `STDecayLoopU`) are other gates' outputs and stay hypotheses of the examples; every
deterministic hypothesis is discharged.  `DecayLoopB_sz0_far_nonempty_U` and `DecayLoopB_sz0_far_nonempty_EK` show that the
far set of `STDecayLoopU` and the far premise of `EKFastDecay` are nonempty at the data, for every `n`. -/

namespace RBM.Gauss.DecayLoopBInst

open Filter RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Ind RBM.Gauss.SizesInst
  RBM.Gauss.InductionDefsInst


private def DecayLoopB_I3 : LoopIdx (Zd 3 5) :=
  loopOf ![true, false, true] ![(0 : Zd 3 5), fun _ => 2, 0]

private theorem DecayLoopB_I3_WF : DecayLoopB_I3.WF := by simp [DecayLoopB_I3, loopOf, LoopIdx.WF]
private theorem DecayLoopB_I3_length : DecayLoopB_I3.length = 3 := by simp [DecayLoopB_I3, loopOf, LoopIdx.length]
private theorem DecayLoopB_I3_mem0 : (0 : Zd 3 5) ∈ DecayLoopB_I3.a := by simp [DecayLoopB_I3, loopOf]
private theorem DecayLoopB_I3_mem1 : (fun _ => 2 : Zd 3 5) ∈ DecayLoopB_I3.a := by simp [DecayLoopB_I3, loopOf]
private theorem DecayLoopB_I3_far : 2 * (1 / 2 : ℝ) + 1 ≤ (zdistInf 3 5 ((0 : Zd 3 5) - fun _ => 2) : ℝ) := by
  have : zdistInf 3 5 ((0 : Zd 3 5) - fun _ => 2) = 2 := by decide
  rw [this]; norm_num

open scoped Classical in
private def DecayLoopB_F3 : LoopIdx (Zd 3 5) → ℂ :=
  fun J => if ∀ x ∈ J.a, ∀ y ∈ J.a, x = y then 1 else (1 / 10 : ℂ)

private theorem DecayLoopB_F3_decay (N : ℕ) : LoopDecay 3 5 N (1 / 2) (1 / 10) DecayLoopB_F3 := by
  intro J hJ hJN x hx y hy hxy
  have hne : ¬ (∀ x ∈ J.a, ∀ y ∈ J.a, x = y) := by
    intro h
    have := h x hx y hy
    subst this
    have h0 : zdistInf 3 5 (x - x) = 0 := by simp [zdistInf]
    rw [h0] at hxy
    norm_num at hxy
  simp [DecayLoopB_F3, hne]

private theorem DecayLoopB_F3_bound (J : LoopIdx (Zd 3 5)) : ‖DecayLoopB_F3 J‖ ≤ 1 := by
  unfold DecayLoopB_F3; split_ifs <;> norm_num

example : ‖glueTerm (1 / 2) DecayLoopB_F3 DecayLoopB_F3 DecayLoopB_I3 1 2‖ ≤ ((5 : ℕ) : ℝ) ^ 3 * (1 / 10 * 1 + 1 * (1 / 10)) :=
  norm_glueTerm_le_of_far (g := 1 / 2) (R := 1 / 2) (by norm_num) DecayLoopB_I3_WF le_rfl (by norm_num)
    (by rw [DecayLoopB_I3_length]; norm_num) (by norm_num) (by norm_num) (DecayLoopB_F3_decay _) (DecayLoopB_F3_decay _)
    (fun a => DecayLoopB_F3_bound _) (fun b => DecayLoopB_F3_bound _) DecayLoopB_I3_mem0 DecayLoopB_I3_mem1 DecayLoopB_I3_far

example : ‖∑ a : Zd 3 5, ∑ b : Zd 3 5, SB 3 5 (1 / 2) a b * (if a = 0 then (1 : ℂ) else 1 / 10)‖ ≤
    (2 * 1 + 1) ^ 3 * 1 + ((5 : ℕ) : ℝ) ^ 3 * (1 / 10) :=
  norm_sum_SB_le_left (g := 1 / 2) (by norm_num) zero_le_one (by norm_num) 0
    (fun a b => if a = 0 then 1 else 1 / 10) (fun a b => by split_ifs <;> norm_num)
    (fun a b h => by
      by_cases ha : a = 0
      · subst ha
        have h0 : zdistInf 3 5 ((0 : Zd 3 5) - 0) = 0 := by simp [zdistInf]
        rw [h0] at h; norm_num at h
      · simp [ha])

private def DecayLoopB_eeσ : List Bool := [true, false, true]
private def DecayLoopB_eea : List (Zd 3 5) := [0, fun _ => 2, 0]
private def DecayLoopB_eea' : List (Zd 3 5) := [fun _ => 1, 0, fun _ => 3]

example (b b' : Zd 3 5) :
    (STeeLoop DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' 2 b b').length = 8 ∧ (STeeLoop DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' 2 b b').WF ∧
    (fun _ => 3 : Zd 3 5) ∈ (STeeLoop DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' 2 b b').a :=
  ⟨length_eeLoop DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' (k := 2) (by simp [DecayLoopB_eea]) (by simp [DecayLoopB_eea, DecayLoopB_eea']) b b',
    eeLoop_WF DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' (k := 2) (by norm_num) (by simp [DecayLoopB_eea]) (by simp [DecayLoopB_eeσ, DecayLoopB_eea])
      (by simp [DecayLoopB_eea, DecayLoopB_eea']) b b',
    mem_eeLoop_right DecayLoopB_eeσ DecayLoopB_eea DecayLoopB_eea' 2 b b' (by simp [DecayLoopB_eea'])⟩

example : (∃ c : Zd 3 5, ∀ b, c ∈ (DecayLoopB_I3.cutGlueL 1 3 b).a) ∧ (∃ c : Zd 3 5, ∀ b, c ∈ (DecayLoopB_I3.cutGlueR 1 3 b).a) :=
  ⟨exists_anchor_cutGlueL DecayLoopB_I3 (by norm_num) (by rw [DecayLoopB_I3_length]),
    exists_anchor_cutGlueR DecayLoopB_I3 le_rfl (by norm_num) (by rw [DecayLoopB_I3_length])⟩



/-- `2(n+1) ≤ |c|_∞` for `c = (2(n+1), 2(n+1), 2(n+1))` on `Z_L^3`, `L = 4(n+1)`. -/
private theorem sz0_zdistInf (n : ℕ) :
    2 * (n + 1) ≤ zdistInf 3 (sz0.L n) (fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) := by
  have hL : sz0.L n = 4 * (n + 1) := rfl
  have hv : ((2 * (n + 1) : ℕ) : ZMod (sz0.L n)).val = 2 * (n + 1) := by
    rw [ZMod.val_natCast_of_lt]
    rw [hL]; omega
  unfold zdistInf
  refine le_trans ?_ (Finset.le_sup (f := fun i : Fin 3 => zdist (sz0.L n)
    (((fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n)) : Zd 3 (sz0.L n))) i))
    (Finset.mem_univ (0 : Fin 3)))
  simp only [zdist, hv, hL]
  omega

/-- `ℓ_0 ≤ 1` at `sz0`: `ilambda ≤ 1/64`. -/
private theorem sz0_ell_zero (n : ℕ) : ellT (sz0.L n) (sz0.lam n) 0 ≤ 1 := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hg : sz0.lam n ≤ 1 / 64 := by
    have h6 : (64 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ (2 * ((n : ℝ) + 1)) ^ 6 := pow_le_pow_left₀ (by norm_num) hx 6
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]; exact inv_anti₀ (by norm_num) h6
  calc ellT (sz0.L n) (sz0.lam n) 0 ≤ max (sz0.lam n / Real.sqrt |1 - (0 : ℝ)|) 1 := min_le_left _ _
    _ = 1 := by
        rw [show |1 - (0 : ℝ)| = 1 by norm_num, Real.sqrt_one, div_one]
        exact max_eq_right (by linarith)

/-- `W^{1/10} ≤ 2(n+1)` at `sz0` (`W = (2(n+1))^5`). -/
private theorem sz0_W_rpow (n : ℕ) : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx0 : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by linarith
  have hWe : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
  rw [hWe, ← Real.rpow_natCast (2 * ((n : ℝ) + 1)) 5, ← Real.rpow_mul hx0.le]
  calc (2 * ((n : ℝ) + 1)) ^ (((5 : ℕ) : ℝ) * (1 / 10 : ℝ))
      ≤ (2 * ((n : ℝ) + 1)) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    _ = 2 * ((n : ℝ) + 1) := Real.rpow_one _

/-- **The far set of `STDecayLoopU` is nonempty at the window point `u = 0 ∈ [s_n,t_n]`, every `n`**:
`a = (0, 0, c)`, `c = L/2 (1,1,1)`, `ℓ_0 W^{1/10} ≤ diam_∞ a` (`W^{1/10} ≤ 2(n+1) = L/2`). -/
theorem DecayLoopB_sz0_far_nonempty_U (n : ℕ) :
    ∃ (v : TimeIcc sInst tInst n) (a : Fin 3 → Zd 3 (sz0.L n)),
      ellT (sz0.L n) (sz0.lam n) (v : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
        (STdiamInf a : ℝ) := by
  refine ⟨⟨0, by simp [sInst], by simp [tInst]⟩, ![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))], ?_⟩
  have hℓ := sz0_ell_zero n
  have hW := sz0_W_rpow n
  have hdiam : 2 * (n + 1) ≤ STdiamInf
      (![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 3 → Zd 3 (sz0.L n)) := by
    unfold STdiamInf
    refine le_trans ?_ (Finset.le_sup (f := fun p : Fin 3 × Fin 3 => zdistInf 3 (sz0.L n)
      ((![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 3 → Zd 3 (sz0.L n)) p.1 -
        (![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 3 → Zd 3 (sz0.L n)) p.2))
      (Finset.mem_univ ((2 : Fin 3), (0 : Fin 3))))
    simpa using sz0_zdistInf n
  have hdiamR : (2 * ((n : ℝ) + 1)) ≤ (STdiamInf
      (![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 3 → Zd 3 (sz0.L n)) : ℝ) := by
    have h1 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf
        (![0, 0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 3 → Zd 3 (sz0.L n)) : ℝ) := by
      exact_mod_cast hdiam
    have h2 : ((2 * (n + 1) : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
    linarith
  have hWnn : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ellT (sz0.L n) (sz0.lam n) ((⟨0, by simp [sInst], by simp [tInst]⟩ : TimeIcc sInst tInst n) : ℝ) *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ)
      ≤ 1 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := by gcongr
    _ ≤ _ := by linarith


/-- `|E_n| ≤ 2 - 1/10` along the merged flow `z0`. -/
private theorem inst_hE (n : ℕ) : |STflowE z0 n| ≤ 2 - 1 / 10 := by
  have him : 0 < (z0 n).im :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz0.one_le_size n) _)
      (flow_z0.2 n).2.1
  exact (abs_lemE_le him).trans (flow_z0.2 n).1

/-- **Target 3 at `d = 3`** on the merged flow instance (`sz0`, `z0`, `flow_z0`, `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`), window `[0, 1/16]` (`1/16 ≤ lemT z0`), arbitrary `Cd`; the uniform Step-2 decay `STGdecayW`
stays the hypothesis. -/
example (Cd : ℝ) (hD : STGdecayW sz0 (STflowE z0) sInst tInst Cd) :
    STDecayLoopU sz0 (STflowE z0) sInst tInst :=
  stDecayLoopU_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
    (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => sixteenth_le_lemT n) Cd hD

/-- **Target 3, applied at `k = 3`, `τ' = 1/10`, `D' = 1`.** -/
example (Cd : ℝ) (hD : STGdecayW sz0 (STflowE z0) sInst tInst Cd) :
    Prec sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p ω =>
        (‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω‖ +
          ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz0.L n) (sz0.lam n) (p.1 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
            (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h : STDecayLoopU sz0 (STflowE z0) sInst tInst :=
    stDecayLoopU_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
      (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
      (fun n => sixteenth_le_lemT n) Cd hD
  exact h 3 (by norm_num) (1 / 10) (by norm_num) 1 (by norm_num)

/-- **Target 2 at `d = 3`** on the same data, `k = 2`, charges `(+,-)`: the four statements
`STEKDecay` for `STegt`, `STksimLK` (every `l`), `STelklk`, `STee` (the `2k = 4` labels of `(a, a')`);
the decay of the loops `STDecayLoopU` (another gate's output, `stDecayLoopU_of_step2`) stays the
hypothesis, every deterministic hypothesis is discharged. -/
example (hU : STDecayLoopU sz0 (STflowE z0) sInst tInst) :
    STEKDecay sz0 sInst tInst (m := 2)
      (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
        sz0.STegt n (STflowE z0 n) (v : ℝ) ω ⟨List.ofFn ![true, false], List.ofFn a⟩) ∧
    (∀ l : ℕ, STEKDecay sz0 sInst tInst (m := 2)
      (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
        sz0.STksimLK n (STflowE z0 n) (v : ℝ) ω l ⟨List.ofFn ![true, false], List.ofFn a⟩)) ∧
    STEKDecay sz0 sInst tInst (m := 2)
      (fun n v ω (a : Fin 2 → Zd 3 (sz0.L n)) =>
        sz0.STelklk n (STflowE z0 n) (v : ℝ) ω ⟨List.ofFn ![true, false], List.ofFn a⟩) ∧
    STEKDecay sz0 sInst tInst (m := 2 + 2)
      (fun n v ω (b : Fin (2 + 2) → Zd 3 (sz0.L n)) =>
        sz0.STee n (STflowE z0 n) (v : ℝ) ω ![true, false] (fun i => b (Fin.castAdd 2 i))
          (fun i => b (Fin.natAdd 2 i))) :=
  stEtermDecay (d := 3) (by norm_num) sz0 (κ := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num)
    inst_hE sz0_admissible (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => by norm_num [tInst]) hU 2 le_rfl ![true, false]

/-- **Targets 3 and 2 chained at `d = 3`**: the only hypothesis left is the uniform Step-2 decay
`STGdecayW` (another gate's output); `STDecayLoopU` is derived by `stDecayLoopU_of_step2`, and
`stEtermDecay` is applied to it (`k = 3`, charges `(+,-,+)`, first term `STegt`). -/
example (Cd : ℝ) (hD : STGdecayW sz0 (STflowE z0) sInst tInst Cd) :
    STEKDecay sz0 sInst tInst (m := 3)
      (fun n v ω (a : Fin 3 → Zd 3 (sz0.L n)) =>
        sz0.STegt n (STflowE z0 n) (v : ℝ) ω ⟨List.ofFn ![true, false, true], List.ofFn a⟩) :=
  (stEtermDecay (d := 3) (by norm_num) sz0 (κ := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num)
    inst_hE sz0_admissible (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
    (fun n => by norm_num [tInst])
    (stDecayLoopU_of_step2 (d := 3) (by norm_num) sz0 (by norm_num) (by norm_num) flow_z0
      (fun _ => le_rfl) (fun n => by norm_num [sInst, tInst])
      (fun n => sixteenth_le_lemT n) Cd hD) 3 (by norm_num) ![true, false, true]).1

/-- **The far premise of `EKFastDecay` is nonempty at the instance**: at `v = 0`, `ε = 1/10`, for every
`n` the pair `a = (0, c)` has `W^{ε} ℓ_0 ≤ |a_1 - a_0|_{ℓ¹}`. -/
theorem DecayLoopB_sz0_far_nonempty_EK (n : ℕ) :
    ∃ (v : TimeIcc sInst tInst n) (a : Fin 2 → Zd 3 (sz0.L n)) (i j : Fin 2),
      ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ellT (sz0.L n) (sz0.lam n) (v : ℝ) ≤
        (zdistD 3 (sz0.L n) (a i - a j) : ℝ) := by
  refine ⟨⟨0, by simp [sInst], by simp [tInst]⟩,
    ![0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))], 1, 0, ?_⟩
  have hℓ := sz0_ell_zero n
  have hW := sz0_W_rpow n
  have h1 : 2 * (n + 1) ≤ zdistD 3 (sz0.L n)
      (fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) :=
    (sz0_zdistInf n).trans (zdistInf_le_zdistD 3 (sz0.L n) _)
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (zdistD 3 (sz0.L n)
      (fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) : ℝ) := by exact_mod_cast h1
  have h3 : ((2 * (n + 1) : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by push_cast; ring
  have hWnn : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : ((![0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 2 → Zd 3 (sz0.L n)) 1 -
      (![0, fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))] : Fin 2 → Zd 3 (sz0.L n)) 0) =
      (fun _ => ((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) := by simp
  rw [hsub]
  calc ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) *
        ellT (sz0.L n) (sz0.lam n) ((⟨0, by simp [sInst], by simp [tInst]⟩ : TimeIcc sInst tInst n) : ℝ)
      ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1 := by gcongr
    _ ≤ _ := by linarith


end RBM.Gauss.DecayLoopBInst

end
