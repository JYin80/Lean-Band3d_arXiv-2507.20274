/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.AuxGraph2
import RBM3D.Induction.ScaleFacts
import RBM3D.Green.IBPPoly

/-!
# LW-14c (T2255): `(eq;I42inG)`, `(eq;EGxy:x=y)`, part c

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-110` (`B:line`): `(eq;I42inG)`, `(eq;EGxy:x=y)`, the bound
`(Gammamuxy)` of a graph with `q ≤ 1` internal molecules (`GtoAG` and Cauchy-Schwarz, `B:84-90`), and the assembly of the
`x = y` count; `paper/tex/7_8_light_weight.tex:873-930` (`(eq:Gbyxi2)`, `GtoAG`).  No port (RBM2D has no light-weight layer).

## What is proved (the pins are the check file `docs/tickets/checks/T2255-check.lean`, section 2, without the suffix `Pin`)

* §1 the vocabulary `LWG5Graph k s` (`𝒢_xy`), `LWG5Data` (`lwSampleData` at `z_t`, `M = m I`, `S = lwS`, `S⁺ = lwSplus`), `LWAttached`.
* §2 **bridge** `lwExpTerm3_bridge : ∀ d, LwExpTerm3Bridge d`: `t^{1 or 2} · W^d Σ_{a₁a₂a₃} K S^{(B)} 𝔼 𝓛^{(5)} = W^{-2d} Σ_{x∈[a], y∈[b]} 𝔼 𝒢_xy`
  (the fine-lattice expansion of `Lloop` (`lwExpTerm2_Lloop5`), `S = t W^{-d} Lift S^{(B)}`, `S⁺ = W^{-d} K⁺`; block resummation
  `lwExpTerm3_alg`).
* §3 **`(Gammamuxy)` for `q ≤ 1`** `lwGraphPrec1 : ∀ d, LwGraphPrec1 d`: `S⁺ = O(t)` (`lwExpTerm3_Sp_decay`, from `S⁺ = S + m² S⁺ S`),
  the auxiliary graph (`lwExpTerm3_auxVal_zero`, `lwExpTerm3_auxVal_one`: Cauchy-Schwarz on the two attached edges, `lwXi_ward_sum`),
  `ξ = min (N^τ lwXiVar, Ψ)` in `lwGtoAG_holds` (`lwExpTerm3_det`), the pathwise bound (`lwExpTerm3_pathwise`), its arithmetic
  (`lwExpTerm3_arith`), and `≺ → 𝔼` (`lwExpTerm_prec_integral`) applied to `t^{-n_W} Γ` (the floor `N^{-K} ≤ R` fails for `t^{n_W} R`).
* §4 **assembly** `lwExpG5'_of_expand : ∀ d, LwExpG5'OfExpand d` (`LWG5Expand d → LWExpG5' d`): `t = 0` (`G_0 = m I`,
  `lwExpTerm3_Lloop5_zero`, `lwExpTerm3_T4zero`), `t > 0` (bridge, `LWG5Expand`, `lwGraphPrec1` for the finite list, the `x = y` count
  with `STBctl_ge`: `lwExpTerm3_T4pos`).
* §5 conditionals `lwCutExp_of_expand`, `lwTermEXP_of_expand`, and the compiled instances (`lwExpTerm3_inst_*`, `d = 3`).

`LWG5Expand` (the expansion of `𝒢_xy` into graphs with `n_M ≤ 1`, `n_W ≥ 2`, `ord ≥ 4·1_{x=y} + 5·1_{x≠y}`) is the premise owed by LW-14e.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

/-! ## 1. Vocabulary (the pins of the check file `docs/tickets/checks/T2255-check.lean`, section 2, without the suffix `Pin`) -/

def LWG5Graph (k s : Bool) : LGraph (Fin 2) (Fin 3) where
  solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inr 1),
    SEdge.mk true false (Sum.inr 1) (Sum.inr 2), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
    if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
  waved := [WEdge.mk k true (Sum.inr 1) (Sum.inr 0), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1

noncomputable def LWG5Data {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) :
    LData (Idx d (sz.L n) (sz.W n)) :=
  lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω

def LWAttached (P : PGraph (Fin 2)) : Prop :=
  ∀ v : P.I', (∀ w ∈ P.g.mol (Sum.inr v), w.isRight = true) →
    2 ≤ (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧
      (P.g.mol e.src = P.g.mol (Sum.inr v) ∨ P.g.mol e.dst = P.g.mol (Sum.inr v)))).length

theorem lwExpTerm3_val_expand (k s : Bool) {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) :
    (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] =
      ∑ α, ∑ γ, ∑ β, (if k then lwSplus sz n t (mE E) γ α else lwS sz n t γ α) * lwS sz n t α β *
        (Gt sz n E t true ω x α * Gt sz n E t true ω α γ * Gt sz n E t true ω γ β *
          Gt sz n E t true ω β y * Gt sz n E t s ω y x) := by
  unfold LGraph.val
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [sum_pi_fin_zero]
  simp only [LGraph.term, LWG5Graph, LWG5Data, lwSampleData, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, SEdge.val, WEdge.val, DEdge.val, Sum.elim_inl, Sum.elim_inr]
  cases s
  · rw [lwExpTerm2_Gt_false]
    cases k <;> simp [lwGm, Gt] <;> ring
  · cases k <;> simp [lwGm, Gt] <;> ring


theorem lwExpTerm3_collapse {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
    (bl : ι → B) (c₀ : ℂ) (K SBm : B → B → ℂ) (α γ β : ι) :
    ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * SBm a₂ a₃ * lwExpTerm2_dw bl c₀ a₂ α * lwExpTerm2_dw bl c₀ a₁ γ *
      lwExpTerm2_dw bl c₀ a₃ β = c₀ ^ 3 * K (bl γ) (bl α) * SBm (bl α) (bl β) := by
  have h3 : ∀ a₂, ∑ a₃, lwExpTerm2_dw bl c₀ a₃ β * SBm a₂ a₃ = c₀ * SBm a₂ (bl β) :=
    fun a₂ => lwExpTerm2_dw_blocks bl c₀ β (SBm a₂)
  have h1 : ∀ a₂, ∑ a₁, lwExpTerm2_dw bl c₀ a₁ γ * K a₁ a₂ = c₀ * K (bl γ) a₂ :=
    fun a₂ => lwExpTerm2_dw_blocks bl c₀ γ (fun a₁ => K a₁ a₂)
  have h2 := lwExpTerm2_dw_blocks bl c₀ α (fun a₂ => (c₀ * K (bl γ) a₂) * (c₀ * SBm a₂ (bl β)))
  rw [Finset.sum_comm]
  calc _ = ∑ a₂, lwExpTerm2_dw bl c₀ a₂ α * ((∑ a₁, lwExpTerm2_dw bl c₀ a₁ γ * K a₁ a₂) *
        (∑ a₃, lwExpTerm2_dw bl c₀ a₃ β * SBm a₂ a₃)) := by
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₃ _ => ?_
        ring
    _ = ∑ a₂, lwExpTerm2_dw bl c₀ a₂ α * ((c₀ * K (bl γ) a₂) * (c₀ * SBm a₂ (bl β))) := by
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [h1, h3]
    _ = _ := by rw [h2]; ring


theorem lwExpTerm3_move5 {A X₁ X₂ X₃ X₄ X₅ : Type*} [Fintype A] [Fintype X₁] [Fintype X₂] [Fintype X₃]
    [Fintype X₄] [Fintype X₅] (f : A → X₁ → X₂ → X₃ → X₄ → X₅ → ℂ) :
    ∑ a, ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f a x y α γ β =
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, ∑ a, f a x y α γ β := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]

theorem lwExpTerm3_move3 {A₁ A₂ A₃ X₁ X₂ X₃ X₄ X₅ : Type*} [Fintype A₁] [Fintype A₂] [Fintype A₃] [Fintype X₁]
    [Fintype X₂] [Fintype X₃] [Fintype X₄] [Fintype X₅]
    (f : A₁ → A₂ → A₃ → X₁ → X₂ → X₃ → X₄ → X₅ → ℂ) :
    ∑ a₁, ∑ a₂, ∑ a₃, ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f a₁ a₂ a₃ x y α γ β =
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, ∑ a₁, ∑ a₂, ∑ a₃, f a₁ a₂ a₃ x y α γ β := by
  have h3 : ∀ a₁ a₂, ∑ a₃, ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f a₁ a₂ a₃ x y α γ β =
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, ∑ a₃, f a₁ a₂ a₃ x y α γ β := fun a₁ a₂ =>
    lwExpTerm3_move5 (fun a₃ => f a₁ a₂ a₃)
  simp_rw [h3]
  have h2 : ∀ a₁, ∑ a₂, ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, ∑ a₃, f a₁ a₂ a₃ x y α γ β =
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, ∑ a₂, ∑ a₃, f a₁ a₂ a₃ x y α γ β := fun a₁ =>
    lwExpTerm3_move5 (fun a₂ x y α γ β => ∑ a₃, f a₁ a₂ a₃ x y α γ β)
  simp_rw [h2]
  exact lwExpTerm3_move5 (fun a₁ x y α γ β => ∑ a₂, ∑ a₃, f a₁ a₂ a₃ x y α γ β)


theorem lwExpTerm3_alg {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]
    (bl : ι → B) (c₀ : ℂ) (K SBm : B → B → ℂ) (a b : B) (F : ι → ι → ι → ι → ι → ℂ) :
    ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * SBm a₂ a₃ * (∑ x, ∑ y, ∑ α, ∑ γ, ∑ β,
        lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y * lwExpTerm2_dw bl c₀ a₂ α *
          lwExpTerm2_dw bl c₀ a₁ γ * lwExpTerm2_dw bl c₀ a₃ β * F x y α γ β) =
      c₀ ^ 3 * ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y *
        K (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β := by
  simp_rw [Finset.mul_sum]
  rw [lwExpTerm3_move3]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun γ _ => ?_
  refine Finset.sum_congr rfl fun β _ => ?_
  have h := lwExpTerm3_collapse bl c₀ K SBm α γ β
  calc _ = (lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y * F x y α γ β) *
        ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * SBm a₂ a₃ * lwExpTerm2_dw bl c₀ a₂ α * lwExpTerm2_dw bl c₀ a₁ γ *
          lwExpTerm2_dw bl c₀ a₃ β := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a₃ _ => ?_
        ring
    _ = _ := by rw [h]; ring


theorem lwExpTerm3_perm {ι : Type*} [Fintype ι] (f : ι → ι → ι → ι → ι → ℂ) :
    ∑ x, ∑ α, ∑ β, ∑ y, ∑ γ, f x α β y γ = ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, f x α β y γ := by
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : ∀ α, ∑ β, ∑ y, ∑ γ, f x α β y γ = ∑ γ, ∑ y, ∑ β, f x α β y γ := by
    intro α
    calc ∑ β, ∑ y, ∑ γ, f x α β y γ = ∑ β, ∑ γ, ∑ y, f x α β y γ :=
          Finset.sum_congr rfl fun β _ => Finset.sum_comm
      _ = ∑ γ, ∑ β, ∑ y, f x α β y γ := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun γ _ => Finset.sum_comm
  simp_rw [h1]
  have h2 : ∀ α, ∑ γ, ∑ y, ∑ β, f x α β y γ = ∑ y, ∑ γ, ∑ β, f x α β y γ := fun α => Finset.sum_comm
  simp_rw [h2]
  exact Finset.sum_comm

theorem lwExpTerm3_Lloop5_expand {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (s : Bool)
    (a₂ a₁ a₃ b a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω =
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, lwExpTerm2_w sz n a x * lwExpTerm2_w sz n b y * lwExpTerm2_w sz n a₂ α *
        lwExpTerm2_w sz n a₁ γ * lwExpTerm2_w sz n a₃ β *
        (Gt sz n E t true ω x α * Gt sz n E t true ω α γ * Gt sz n E t true ω γ β *
          Gt sz n E t true ω β y * Gt sz n E t s ω y x) := by
  rw [lwExpTerm2_Lloop5]
  unfold lwExpTerm2_L4
  rw [← lwExpTerm3_perm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun y _ => ?_
  have hm : ∀ α β : Idx d (sz.L n) (sz.W n), (Gt sz n E t true ω * Matrix.diagonal (lwExpTerm2_w sz n a₁) *
      Gt sz n E t true ω) α β = ∑ γ, Gt sz n E t true ω α γ * lwExpTerm2_w sz n a₁ γ * Gt sz n E t true ω γ β := by
    intro α β
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  rw [hm]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  ring


theorem lwExpTerm3_dw_filter {ι B : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq B] (bl : ι → B) (c₀ : ℂ)
    (a b : B) (g : ι → ι → ℂ) :
    ∑ x, ∑ y, lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y * g x y =
      c₀ ^ 2 * ∑ x ∈ Finset.univ.filter (fun x => bl x = a), ∑ y ∈ Finset.univ.filter (fun y => bl y = b),
        g x y := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : bl x = a
  · simp only [hx, ite_true, lwExpTerm2_dw]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : bl y = b
    · simp only [hy, ite_true]; ring
    · simp only [hy, ite_false]; ring
  · simp [hx, lwExpTerm2_dw]


theorem lwExpTerm3_bridge_pt {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (k s : Bool) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω) =
      ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
        ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
          ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
            (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] := by
  set c₀ : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hc₀
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hWc : (((sz.W n : ℕ) : ℂ) ^ d) * c₀ = 1 := mul_inv_cancel₀ hW
  set bl := lwExpTerm2_bl d (sz.L n) (sz.W n) with hbl
  set F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) →
      Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ := fun x y α γ β =>
    Gt sz n E t true ω x α * Gt sz n E t true ω α γ * Gt sz n E t true ω γ β *
      Gt sz n E t true ω β y * Gt sz n E t s ω y x with hF
  set Kk : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun a₁ a₂ =>
    if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) with hKk
  set SBm : Zd d (sz.L n) → Zd d (sz.L n) → ℂ := fun a₁ a₂ => (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) with hSBm
  have h1 : ∑ a₁, ∑ a₂, ∑ a₃, Kk a₁ a₂ * SBm a₂ a₃ *
      Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω =
      c₀ ^ 3 * ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y *
        Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β := by
    simp_rw [lwExpTerm3_Lloop5_expand]
    exact lwExpTerm3_alg bl c₀ Kk SBm a b F
  have h2 : ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b y *
        Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β =
      c₀ ^ 2 * ∑ x ∈ Finset.univ.filter (fun x => bl x = a), ∑ y ∈ Finset.univ.filter (fun y => bl y = b),
        ∑ α, ∑ γ, ∑ β, Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β := by
    rw [← lwExpTerm3_dw_filter bl c₀ a b]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  have hS : ∀ γ α, lwS sz n t γ α = c₀ * ((t : ℂ) * SBm (bl γ) (bl α)) := fun γ α => lwExpTerm2_hS sz n t γ α
  have hterm : ∀ (x y α γ β : Idx d (sz.L n) (sz.W n)),
      (if k then lwSplus sz n t (mE E) γ α else lwS sz n t γ α) * lwS sz n t α β * F x y α γ β =
        c₀ ^ 2 * (t : ℂ) ^ (if k then 1 else 2) * (Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β) := by
    intro x y α γ β
    cases k
    · simp only [hKk, hSBm, Bool.false_eq_true, ite_false, hS]
      ring
    · simp only [hKk, hSBm, ite_true, lwExpTerm2_hSp sz n E t hE ht0 ht1, hS]
      ring
  have hval : ∀ x y : Idx d (sz.L n) (sz.W n),
      (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] =
        c₀ ^ 2 * (t : ℂ) ^ (if k then 1 else 2) *
          ∑ α, ∑ γ, ∑ β, Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β := by
    intro x y
    rw [lwExpTerm3_val_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact (hterm x y α γ β).trans (by ring)
  rw [h1, h2]
  simp_rw [hval, ← Finset.mul_sum]
  have hinv : ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ = c₀ ^ 2 := by rw [hc₀, inv_pow]
  rw [hinv]
  linear_combination (((t : ℂ) ^ (if k then 1 else 2)) * c₀ ^ 4 *
    ∑ x ∈ Finset.univ.filter (fun x => bl x = a), ∑ y ∈ Finset.univ.filter (fun y => bl y = b),
        ∑ α, ∑ γ, ∑ β, Kk (bl γ) (bl α) * SBm (bl α) (bl β) * F x y α γ β) * hWc


section BMGt

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

theorem lwExpTerm3_BM_Gt {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool) (i j : Idx d (sz.L n) (sz.W n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => Gt sz n E t σ ω i j) := by
  have hz : (zt E t).im ≠ 0 := by
    rw [← etaT_eq_zt_im]; exact (etaT_pos hE ht).ne'
  have hT : ∀ i j : Idx d (sz.L n) (sz.W n), lwExpTerm2_BM (fun ω : sz.SeqΩ => Gt sz n E t true ω i j) := fun i j =>
    ⟨walk_measurable_Gt_apply sz n E t true i j, |(zt E t).im|⁻¹, fun ω =>
      lwStein_norm_lwG_le sz n hz t i j ω⟩
  cases σ
  · have : (fun ω : sz.SeqΩ => Gt sz n E t false ω i j) = fun ω => star (Gt sz n E t true ω j i) :=
      funext fun ω => lwExpTerm2_Gt_false sz n E t ω i j
    rw [this]
    obtain ⟨hm, C, hC⟩ := hT j i
    exact ⟨Complex.continuous_conj.measurable.comp hm, C, fun ω => by
      simpa [Complex.norm_conj] using hC ω⟩
  · exact hT i j

theorem lwExpTerm3_BM_val {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (k s : Bool) (x y : Idx d (sz.L n) (sz.W n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y]) := by
  have : (fun ω : sz.SeqΩ => (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y]) = fun ω =>
      ∑ α, ∑ γ, ∑ β, (if k then lwSplus sz n t (mE E) γ α else lwS sz n t γ α) * lwS sz n t α β *
        (Gt sz n E t true ω x α * Gt sz n E t true ω α γ * Gt sz n E t true ω γ β *
          Gt sz n E t true ω β y * Gt sz n E t s ω y x) :=
    funext fun ω => lwExpTerm3_val_expand k s sz n E t ω x y
  rw [this]
  refine lwExpTerm2_BM_sum _ fun α _ => lwExpTerm2_BM_sum _ fun γ _ => lwExpTerm2_BM_sum _ fun β _ =>
    lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) ?_
  have g := lwExpTerm3_BM_Gt sz n hE ht
  exact lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (g true x α) (g true α γ))
    (g true γ β)) (g true β y)) (g s y x)

end BMGt

def LwExpTerm3Bridge (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool) (a b : Zd d (sz.L n)),
    (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)) =
      ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
        ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
          ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
            ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)

theorem lwExpTerm3_bridge (d : ℕ) : LwExpTerm3Bridge d := by
  intro sz n E t hE ht0 ht1 k s a b
  have hint : ∀ a₁ a₂ a₃ : Zd d (sz.L n), Integrable (fun ω : sz.SeqΩ =>
      (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω) (sz.seqP) := fun a₁ a₂ a₃ =>
    ((lwExpTerm2_BM_integrable (lwExpTerm2_BM_Lloop sz n hE ht1 (k := 4) _ _)).const_mul _)
  have hpt := fun ω => lwExpTerm3_bridge_pt sz n E t hE ht0.le ht1 k s a b ω
  have hL : ∫ ω, (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω) ∂(sz.seqP) =
      (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)) := by
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ (fun a₁ _ =>
      integrable_finsetSum _ fun a₂ _ => integrable_finsetSum _ fun a₃ _ => hint a₁ a₂ a₃)]
    congr 2
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [integral_finsetSum _ (fun a₂ _ => integrable_finsetSum _ fun a₃ _ => hint a₁ a₂ a₃)]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    rw [integral_finsetSum _ (fun a₃ _ => hint a₁ a₂ a₃)]
    refine Finset.sum_congr rfl fun a₃ _ => ?_
    rw [integral_const_mul]
  have hval : ∀ x y : Idx d (sz.L n) (sz.W n), Integrable (fun ω : sz.SeqΩ =>
      (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y]) (sz.seqP) := fun x y =>
    lwExpTerm2_BM_integrable (lwExpTerm3_BM_val sz n hE ht1 k s x y)
  rw [← hL]
  simp_rw [hpt]
  rw [integral_const_mul, integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => hval x y)]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ (fun y _ => hval x y)]



/-! ## 3. `(Gammamuxy)` for graphs with at most one internal molecule -/

section AuxBound

private theorem lwExpTerm3_list_prod_le {α : Type*} (l : List α) (g : α → ℝ) (Ψ : ℝ)
    (h : ∀ e ∈ l, 0 ≤ g e ∧ g e ≤ Ψ) : (l.map g).prod ≤ Ψ ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    have ha := h a (List.mem_cons_self)
    have hl := ih fun e he => h e (List.mem_cons_of_mem a he)
    have hprod : 0 ≤ (l.map g).prod := List.prod_nonneg fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      exact (h e (List.mem_cons_of_mem a he)).1
    calc g a * (l.map g).prod ≤ Ψ * Ψ ^ l.length :=
          mul_le_mul ha.2 hl hprod ((ha.1).trans ha.2)
      _ = _ := by ring

private theorem lwExpTerm3_list_prod_two {α : Type*} (l : List α) (g : α → ℝ) (Ψ : ℝ)
    (h : ∀ e ∈ l, 0 ≤ g e ∧ g e ≤ Ψ) (a b : α) (rest : List α) (hp : l.Perm (a :: b :: rest)) :
    (l.map g).prod ≤ g a * g b * Ψ ^ rest.length := by
  have hperm : (l.map g).Perm ((a :: b :: rest).map g) := hp.map g
  rw [hperm.prod_eq]
  have hmem : ∀ e ∈ a :: b :: rest, 0 ≤ g e ∧ g e ≤ Ψ := fun e he => h e (hp.symm.subset he)
  simp only [List.map_cons, List.prod_cons]
  have hr := lwExpTerm3_list_prod_le rest g Ψ fun e he => hmem e (by simp [he])
  have ha := hmem a (by simp)
  have hb := hmem b (by simp)
  have hprod : 0 ≤ (rest.map g).prod := List.prod_nonneg fun x hx => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    exact (hmem e (by simp [he])).1
  calc g a * (g b * (rest.map g).prod) ≤ g a * (g b * Ψ ^ rest.length) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hb.1) ha.1
    _ = _ := by ring

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem lwExpTerm3_sum_empty_fun {α κ : Type} [IsEmpty α] {hI : Fintype (α → κ)} (f : (α → κ) → ℝ)
    (B : ℝ) (h : ∀ b, f b ≤ B) : @Finset.sum (α → κ) ℝ _ (@Finset.univ _ hI) f ≤ B := by
  have : Unique (α → κ) := Pi.uniqueOfIsEmpty _
  rw [Finset.sum_eq_single (default : α → κ) (fun b _ hb => absurd (Subsingleton.elim b _) hb)
    (fun h => absurd (@Finset.mem_univ _ hI _) h)]
  exact h _

/-- `q = 0`: the auxiliary graph without internal molecules is a single product of `ξ`'s. -/
private theorem lwExpTerm3_auxVal_zero {κ : Type} [Fintype κ] (Γ : LGraph E I) (hnM : Γ.nM = 0)
    (ξ : κ → κ → ℝ) (be : E → κ) {Ψ : ℝ} (h0 : ∀ a b, 0 ≤ ξ a b) (hΨ : ∀ a b, ξ a b ≤ Ψ) :
    Γ.auxVal ξ be ≤ Ψ ^ Γ.molSolid.length := by
  classical
  have hcard : Nat.card (LGraph.AuxIMol Γ) = 0 := by rw [← LGraph.nM_eq_card]; exact hnM
  have key : ∀ b : LGraph.AuxIMol Γ → κ, (Γ.molSolid.map fun e =>
      ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)).prod ≤ Ψ ^ Γ.molSolid.length :=
    fun b => lwExpTerm3_list_prod_le Γ.molSolid (fun e => ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)) Ψ
      (fun e _ => ⟨h0 _ _, hΨ _ _⟩)
  have hE : IsEmpty (LGraph.AuxIMol Γ) := by
    rcases Nat.card_eq_zero.1 hcard with h | h
    · exact h
    · exact absurd h (not_infinite_iff_finite.2 inferInstance)
  unfold LGraph.auxVal
  exact lwExpTerm3_sum_empty_fun _ _ key

private theorem lwExpTerm3_mol_eq_iff (Γ : LGraph E I) (u w : E ⊕ I) :
    Γ.mol u = Γ.mol w ↔ Γ.molOf u = Γ.molOf w := by
  constructor
  · intro h
    have h1 : w ∈ Γ.mol w := (Γ.molOf_eq_iff w w).1 rfl
    rw [← h] at h1
    exact (Γ.molOf_eq_iff u w).2 h1
  · intro h
    ext x
    rw [← Γ.molOf_eq_iff, ← Γ.molOf_eq_iff, h]

open Classical in
private theorem lwExpTerm3_molSolid_touch (Γ : LGraph E I) (c : Γ.Mol) (v : I) (hv : Γ.molOf (Sum.inr v) = c) :
    (Γ.solid.filter fun e => decide (Γ.mol e.src ≠ Γ.mol e.dst ∧
      (Γ.mol e.src = Γ.mol (Sum.inr v) ∨ Γ.mol e.dst = Γ.mol (Sum.inr v)))).length =
    (Γ.molSolid.filter fun e => decide (e.src = c ∨ e.dst = c)).length := by
  classical
  unfold LGraph.molSolid
  rw [List.filter_map, List.length_map, List.filter_filter]
  congr 1
  refine List.filter_congr fun e _ => ?_
  simp only [LGraph.InsideMol, Function.comp, SEdge.map, ne_eq, lwExpTerm3_mol_eq_iff, hv]
  by_cases h1 : Γ.molOf e.src = Γ.molOf e.dst <;> by_cases h2 : Γ.molOf e.src = c ∨ Γ.molOf e.dst = c <;> simp [h1, h2]

open Classical in
private theorem lwExpTerm3_molSolid_ne (Γ : LGraph E I) {e : SEdge Γ.Mol} (he : e ∈ Γ.molSolid) : e.src ≠ e.dst := by
  unfold LGraph.molSolid at he
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
  have h3 := of_decide_eq_true (List.mem_filter.1 he₀).2
  simpa [LGraph.InsideMol, SEdge.map] using h3

private theorem lwExpTerm3_sum_funUnique {α κ : Type} [Unique α] {hI : Fintype (α → κ)} [Fintype κ] (F : κ → ℝ) :
    @Finset.sum (α → κ) ℝ _ (@Finset.univ _ hI) (fun b => F (b default)) = ∑ v, F v := by
  refine Finset.sum_bij (fun b _ => b default) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro b _ b' _ h
    funext a
    rw [Subsingleton.elim a default]; exact h
  · intro v _
    exact ⟨fun _ => v, @Finset.mem_univ _ hI _, rfl⟩
  · intro b _; rfl

open Classical in
/-- `q = 1`: one internal molecule, two attached solid edges, Cauchy-Schwarz (`B:84-90`). -/
private theorem lwExpTerm3_auxVal_one {κ : Type} [Fintype κ] (Γ : LGraph E I) (hnM : Γ.nM = 1)
    (hatt : ∀ v : I, (∀ w ∈ Γ.mol (Sum.inr v), w.isRight = true) →
      2 ≤ (Γ.solid.filter fun e => decide (Γ.mol e.src ≠ Γ.mol e.dst ∧
        (Γ.mol e.src = Γ.mol (Sum.inr v) ∨ Γ.mol e.dst = Γ.mol (Sum.inr v)))).length)
    (ξ : κ → κ → ℝ) (be : E → κ) {Ψ S2 : ℝ} (hΨ0 : 0 ≤ Ψ) (h0 : ∀ a b, 0 ≤ ξ a b) (hΨ : ∀ a b, ξ a b ≤ Ψ)
    (hrow : ∀ a, ∑ v, ξ a v ^ 2 ≤ S2) (hcol : ∀ a, ∑ v, ξ v a ^ 2 ≤ S2) :
    ∃ k : ℕ, k + 2 = Γ.molSolid.length ∧ Γ.auxVal ξ be ≤ Ψ ^ k * S2 := by
  have hcard : Nat.card (LGraph.AuxIMol Γ) = 1 := by rw [← LGraph.nM_eq_card]; exact hnM
  obtain ⟨hsub, ⟨c₀⟩⟩ := Nat.card_eq_one_iff_unique.1 hcard
  have hU : Unique (LGraph.AuxIMol Γ) := ⟨⟨c₀⟩, fun a => Subsingleton.elim _ _⟩
  -- a vertex of the internal molecule
  obtain ⟨w, hw⟩ := c₀.1.exists_rep
  have hw' : Γ.molOf w = c₀.1 := hw
  obtain ⟨v, rfl⟩ : ∃ v : I, w = Sum.inr v := by
    rcases w with a | v
    · exact absurd ⟨a, hw'⟩ c₀.2
    · exact ⟨v, rfl⟩
  have hint : ∀ u ∈ Γ.mol (Sum.inr v), u.isRight = true := (Γ.forall_mol_isRight_iff _).2 (by rw [hw']; exact c₀.2)
  have h2 := hatt v hint
  rw [lwExpTerm3_molSolid_touch Γ c₀.1 v hw'] at h2
  -- the two touching edges
  set T : SEdge Γ.Mol → Bool := fun e => decide (e.src = c₀.1 ∨ e.dst = c₀.1) with hT
  obtain ⟨a, b', r, hab⟩ : ∃ a b' r, Γ.molSolid.filter T = a :: b' :: r := by
    rcases hl : Γ.molSolid.filter T with _ | ⟨a, _ | ⟨b', r⟩⟩
    · rw [hl] at h2; simp at h2
    · rw [hl] at h2; simp at h2
    · exact ⟨a, b', r, rfl⟩
  have hperm : Γ.molSolid.Perm (a :: b' :: (r ++ Γ.molSolid.filter fun e => !T e)) := by
    have := List.filter_append_perm T Γ.molSolid
    rw [hab] at this
    simpa using this.symm
  have haT : a ∈ Γ.molSolid ∧ (a.src = c₀.1 ∨ a.dst = c₀.1) := by
    have : a ∈ Γ.molSolid.filter T := by rw [hab]; simp
    simpa [hT, List.mem_filter] using this
  have hbT : b' ∈ Γ.molSolid ∧ (b'.src = c₀.1 ∨ b'.dst = c₀.1) := by
    have : b' ∈ Γ.molSolid.filter T := by rw [hab]; simp
    simpa [hT, List.mem_filter] using this
  set f : (LGraph.AuxIMol Γ → κ) → SEdge Γ.Mol → ℝ := fun b e =>
    ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst) with hf
  have hlab : ∀ b : LGraph.AuxIMol Γ → κ, LGraph.auxLab Γ be b c₀.1 = b c₀ := by
    intro b; unfold LGraph.auxLab; simp only [c₀.2, not_false_eq_true, dite_false]
  have hEdge : ∀ e ∈ Γ.molSolid, (e.src = c₀.1 ∨ e.dst = c₀.1) →
      ∃ u : κ, (∀ b, f b e = ξ (b c₀) u) ∨ (∀ b, f b e = ξ u (b c₀)) := by
    intro e he hT'
    have hne := lwExpTerm3_molSolid_ne Γ he
    -- the other end is external
    have hext : ∀ c : Γ.Mol, c ≠ c₀.1 → Γ.IsExtMol c := by
      intro c hc
      by_contra hn
      exact hc (congrArg Subtype.val (Subsingleton.elim (⟨c, hn⟩ : LGraph.AuxIMol Γ) c₀))
    rcases hT' with hs | hd
    · have hd' : e.dst ≠ c₀.1 := fun h => hne (hs.trans h.symm)
      have hed := hext _ hd'
      refine ⟨be (Classical.choose hed), Or.inl fun b => ?_⟩
      simp only [hf]
      rw [hs, hlab, LGraph.auxLab]; simp only [hed, dite_true]
    · have hs' : e.src ≠ c₀.1 := fun h => hne (h.trans hd.symm)
      have hed := hext _ hs'
      refine ⟨be (Classical.choose hed), Or.inr fun b => ?_⟩
      simp only [hf]
      rw [hd, hlab, LGraph.auxLab]; simp only [hed, dite_true]
  have hsq : ∀ {hI : Fintype (LGraph.AuxIMol Γ → κ)}, ∀ e ∈ Γ.molSolid, (e.src = c₀.1 ∨ e.dst = c₀.1) →
      @Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b => f b e ^ 2) ≤ S2 := by
    intro hI e he hT'
    obtain ⟨u, hu | hu⟩ := hEdge e he hT'
    · have := lwExpTerm3_sum_funUnique (α := LGraph.AuxIMol Γ) (hI := hI) (fun v => ξ v u ^ 2)
      simp only [hu]
      have hdef : (default : LGraph.AuxIMol Γ) = c₀ := Subsingleton.elim _ _
      simp only [hdef] at this
      rw [this]; exact hcol u
    · have := lwExpTerm3_sum_funUnique (α := LGraph.AuxIMol Γ) (hI := hI) (fun v => ξ u v ^ 2)
      simp only [hu]
      have hdef : (default : LGraph.AuxIMol Γ) = c₀ := Subsingleton.elim _ _
      simp only [hdef] at this
      rw [this]; exact hrow u
  have hbound : ∀ b : LGraph.AuxIMol Γ → κ, ∀ e ∈ Γ.molSolid, 0 ≤ f b e ∧ f b e ≤ Ψ :=
    fun b e _ => ⟨h0 _ _, hΨ _ _⟩
  refine ⟨(r ++ Γ.molSolid.filter fun e => !T e).length, ?_, ?_⟩
  · rw [hperm.length_eq]; simp only [List.length_cons]
  · have gen : ∀ {hI : Fintype (LGraph.AuxIMol Γ → κ)},
        @Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b => (Γ.molSolid.map (f b)).prod) ≤
          Ψ ^ (r ++ Γ.molSolid.filter fun e => !T e).length * S2 := by
      intro hI
      have hk : 0 ≤ Ψ ^ (r ++ Γ.molSolid.filter fun e => !T e).length := pow_nonneg hΨ0 _
      calc @Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b => (Γ.molSolid.map (f b)).prod)
          ≤ @Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b =>
              (1 / 2 * (f b a ^ 2 + f b b' ^ 2)) * Ψ ^ (r ++ Γ.molSolid.filter fun e => !T e).length) := by
            refine Finset.sum_le_sum fun b _ => ?_
            refine (lwExpTerm3_list_prod_two Γ.molSolid (f b) Ψ (hbound b) a b' _ hperm).trans ?_
            refine mul_le_mul_of_nonneg_right ?_ hk
            nlinarith [sq_nonneg (f b a - f b b')]
        _ = (1 / 2 * (@Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b => f b a ^ 2) +
              @Finset.sum _ ℝ _ (@Finset.univ _ hI) (fun b => f b b' ^ 2))) *
              Ψ ^ (r ++ Γ.molSolid.filter fun e => !T e).length := by
            rw [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ (1 / 2 * (S2 + S2)) * Ψ ^ (r ++ Γ.molSolid.filter fun e => !T e).length := by
            refine mul_le_mul_of_nonneg_right ?_ hk
            have h1 := hsq (hI := hI) a haT.1 haT.2
            have h2 := hsq (hI := hI) b' hbT.1 hbT.2
            linarith
        _ = _ := by ring
    unfold LGraph.auxVal
    exact gen

open Classical in
/-- **`(Gammamuxy)` deterministic form, `q ≤ 1`** (`B:84-90`): `GtoAG` (`lwGtoAG_holds`) with `ξ = min (cc ξ₀, Ψ)`,
then the auxiliary graph is `≤ Ψ^{auxOrd}` (`q = 0`) or `≤ Ψ^{auxOrd} · cc² · S2` (`q = 1`, Cauchy-Schwarz). -/
theorem lwExpTerm3_det (d : ℕ) (hd : 3 ≤ d) (L W : ℕ) [NeZero L] [NeZero W] (Γ : LGraph E I) (hN : Γ.Normal)
    (hnM : Γ.nM ≤ 1)
    (hatt : ∀ v : I, (∀ w ∈ Γ.mol (Sum.inr v), w.isRight = true) →
      2 ≤ (Γ.solid.filter fun e => decide (Γ.mol e.src ≠ Γ.mol e.dst ∧
        (Γ.mol e.src = Γ.mol (Sum.inr v) ∨ Γ.mol e.dst = Γ.mol (Sum.inr v)))).length)
    (hext : ∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b)
    (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R cc S2 : ℝ) (ξ0 : Zd d L → Zd d L → ℝ)
    (hM : ∀ x y, D.M x y = if x = y then m else 0) (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ)
    (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hwin : (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ) (hΨ : 0 < Ψ) (hr : 0 ≤ r) (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R)
    (hcc : 0 ≤ cc) (h0 : ∀ a b, 0 ≤ ξ0 a b)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ cc * ξ0 a b)
    (hrow : ∀ a, ∑ v, ξ0 a v ^ 2 ≤ S2) (hcol : ∀ a, ∑ v, ξ0 v a ^ 2 ≤ S2) (ℓe : E → Idx d L W) :
    0 ≤ Γ.scalingOrder ∧
    ‖Γ.val D ℓe‖ ≤ Γ.sizeConst C (C * expC (d - 2) c) *
        (Ψ ^ Γ.scalingOrder * (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 * S2) else 1)) +
      Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L := by
  set ξ : Zd d L → Zd d L → ℝ := fun a b => min (cc * ξ0 a b) Ψ with hξdef
  have hξ0 : ∀ a b, 0 ≤ ξ a b := fun a b => le_min (mul_nonneg hcc (h0 a b)) hΨ.le
  have hξΨ : ∀ a b, ξ a b ≤ Ψ := fun a b => min_le_right _ _
  have hξ1 : ∀ a b, ξ a b ≤ cc * ξ0 a b := fun a b => min_le_left _ _
  have hξ' : ∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ ξ a b :=
    fun x y a b hxy h1 h2 => le_min (hξ x y a b hxy h1 h2) (hG x y hxy)
  have hmain := lwGtoAG_holds d hd L W Γ hN hext D m Ψ C c r R ξ hM hG hGd hC hc hS hSp hwin hr hRr hξ0 hξ' ℓe
  have hord := Γ.auxOrd_le_scalingOrder hN
  set be : E → Zd d L := fun a => (split d L W (ℓe a)).1 with hbe
  have hΨne : Ψ ≠ 0 := hΨ.ne'
  have hsq : ∀ a b, ξ a b ^ 2 ≤ cc ^ 2 * ξ0 a b ^ 2 := fun a b => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (hξ0 a b) (hξ1 a b) 2
  have hrow' : ∀ a, ∑ v, ξ a v ^ 2 ≤ cc ^ 2 * S2 := fun a =>
    (Finset.sum_le_sum fun v _ => hsq a v).trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrow a) (sq_nonneg _))
  have hcol' : ∀ a, ∑ v, ξ v a ^ 2 ≤ cc ^ 2 * S2 := fun a =>
    (Finset.sum_le_sum fun v _ => hsq v a).trans (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hcol a) (sq_nonneg _))
  have hexp : 0 ≤ expC (d - 2) c := by unfold expC; positivity
  have hK : 0 ≤ Γ.sizeConst C (C * expC (d - 2) c) :=
    LGraph.sizeConst_nonneg Γ hC (mul_nonneg hC hexp)
  have hzp : ∀ n : ℤ, 0 ≤ Ψ ^ n := fun n => zpow_nonneg hΨ.le n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hnM with h1 | h1
  · -- q = 0
    have hav := lwExpTerm3_auxVal_zero Γ h1 ξ be hξ0 hξΨ
    have hao : Γ.auxOrd = (Γ.molSolid.length : ℤ) := by
      simp [LGraph.auxOrd, ord, h1]
    refine ⟨by omega, ?_⟩
    refine hmain.trans (add_le_add ?_ le_rfl)
    rw [h1]
    simp only [pow_zero, one_mul, zero_ne_one, ite_false, mul_one]
    calc Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Γ.auxVal ξ be
        ≤ Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ Γ.molSolid.length :=
          mul_le_mul_of_nonneg_left hav (mul_nonneg hK (hzp _))
      _ = Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ Γ.scalingOrder := by
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hΨne, hao]; congr 2; ring
  · -- q = 1
    obtain ⟨k, hk, hav⟩ := lwExpTerm3_auxVal_one Γ h1 hatt ξ be hΨ.le hξ0 hξΨ hrow' hcol'
    have hao : Γ.auxOrd = (k : ℤ) := by
      simp only [LGraph.auxOrd, ord, h1]; omega
    refine ⟨by omega, ?_⟩
    refine hmain.trans (add_le_add ?_ le_rfl)
    rw [h1]
    simp only [pow_one, ite_true]
    calc Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * ((W : ℝ) ^ d * Γ.auxVal ξ be)
        ≤ Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
            ((W : ℝ) ^ d * (Ψ ^ k * (cc ^ 2 * S2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hav (by positivity))
            (mul_nonneg hK (hzp _))
      _ = Γ.sizeConst C (C * expC (d - 2) c) * (Ψ ^ Γ.scalingOrder * ((W : ℝ) ^ d * (cc ^ 2 * S2))) := by
          have : Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ k = Ψ ^ Γ.scalingOrder := by
            rw [← zpow_natCast, ← zpow_add₀ hΨne, hao]; congr 1; ring
          calc _ = Γ.sizeConst C (C * expC (d - 2) c) * (Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ k) *
                ((W : ℝ) ^ d * (cc ^ 2 * S2)) := by ring
            _ = _ := by rw [this]; ring

end AuxBound

section SpDecay

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem lwExpTerm3_sbR_le_one (g : ℝ) (x : Zd d (sz.L n)) : sbKernelR d (sz.L n) g x ≤ 1 := by
  rw [← sum_sbKernelR d (sz.L n) g (sz.three_le_L n)]
  exact Finset.single_le_sum (f := fun y => sbKernelR d (sz.L n) g y) (fun y _ => sbKernelR_nonneg d (sz.L n) g y)
    (Finset.mem_univ x)

private theorem lwExpTerm3_sbR_support (g : ℝ) {x : Zd d (sz.L n)} (h : sbKernelR d (sz.L n) g x ≠ 0) :
    zdistD d (sz.L n) x ≤ 1 := by
  unfold sbKernelR at h
  by_cases h0 : x = 0
  · simp [h0, zdistD]
  · by_cases h1 : zdistD d (sz.L n) x = 1
    · exact h1.le
    · exfalso; apply h; simp [h0, h1]

/-- `‖S^{(u)}_{xy}‖ = u · svarF` (`u ≥ 0`). -/
private theorem lwExpTerm3_lwS_norm {u : ℝ} (hu : 0 ≤ u) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖lwS sz n u x y‖ = u * svarF d (sz.L n) (sz.W n) (sz.lam n) x y := by
  simp only [lwS, Matrix.of_apply, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg hu (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) x y))]

private theorem lwExpTerm3_svarF_le (x y : Idx d (sz.L n) (sz.W n)) :
    svarF d (sz.L n) (sz.W n) (sz.lam n) x y ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  unfold svarF
  have h := lwExpTerm3_sbR_le_one sz n (sz.lam n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1)
  have h' : SBR d (sz.L n) (sz.lam n) (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 ≤ 1 := by
    simpa [SBR] using h
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  nlinarith

private theorem lwExpTerm3_svarF_support (x y : Idx d (sz.L n) (sz.W n))
    (h : svarF d (sz.L n) (sz.W n) (sz.lam n) x y ≠ 0) : lwBdist d (sz.L n) (sz.W n) x y ≤ 1 := by
  unfold svarF at h
  have h2 : SBR d (sz.L n) (sz.lam n) (split d (sz.L n) (sz.W n) x).1 (split d (sz.L n) (sz.W n) y).1 ≠ 0 := by
    intro h0; apply h; rw [h0, mul_zero]
  have h3 : sbKernelR d (sz.L n) (sz.lam n) ((split d (sz.L n) (sz.W n) x).1 - (split d (sz.L n) (sz.W n) y).1) ≠ 0 := by
    simpa [SBR] using h2
  exact lwExpTerm3_sbR_support sz n (sz.lam n) h3

private theorem lwExpTerm3_svarF_col (u : ℝ) (y : Idx d (sz.L n) (sz.W n)) :
    ∑ w, u * svarF d (sz.L n) (sz.W n) (sz.lam n) w y = u := by
  have h := lwS_row_sum (sz := sz) (n := n) u y
  have h2 : ∑ w, (u * svarF d (sz.L n) (sz.W n) (sz.lam n) y w : ℝ) = u := by
    have : ((∑ w, (u * svarF d (sz.L n) (sz.W n) (sz.lam n) y w : ℝ) : ℝ) : ℂ) = (u : ℂ) := by
      rw [Complex.ofReal_sum]; simpa [lwS] using h
    exact_mod_cast this
  simpa [svarF_comm] using h2

/-- **`S^{(u)}`, `S^±` are `O(u)`** (`(eq:estSpm-W)` with the factor `u` that `lwSplus_decay` does not carry):
from `S⁺ = S + m² S⁺ S` (`lwSplus_spec`) and `lwSplus_decay`: `|S⁺_{xy}| ≤ |S_{xy}| + Σ_w |S⁺_{xw}| |S_{wy}|`,
`S` has support `d_B ≤ 1` and column sums `u`. -/
theorem lwExpTerm3_Sp_decay (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ Λ →
      ∀ u E : ℝ, 0 ≤ u → u < 1 → |E| ≤ 2 - κ → ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖lwS sz n u x y‖ ≤ u * C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ∧
        ‖lwSplus sz n u (mE E) x y‖ ≤ u * C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
            Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) := by
  obtain ⟨C₀, c, hC₀, hc, hdec⟩ := lwSplus_decay d hd Λ κ hΛ hκ
  refine ⟨Real.exp c * (1 + C₀), c, by positivity, hc, fun sz n hl hlΛ u E hu0 hu1 hE x y => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  have hm : ‖mE E‖ = 1 := norm_mE hE2
  set Wd : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 ≤ Wd := by positivity
  set bd : ℝ := (lwBdist d (sz.L n) (sz.W n) x y : ℝ) with hbd
  have hex : (1 : ℝ) ≤ Real.exp c * Real.exp (-(c * 1)) := by
    rw [← Real.exp_add]; simp
  -- the entry of `S`
  have hS : ‖lwS sz n u x y‖ ≤ u * Wd * (Real.exp c * Real.exp (-(c * bd))) := by
    rw [lwExpTerm3_lwS_norm sz n hu0]
    by_cases h0 : svarF d (sz.L n) (sz.W n) (sz.lam n) x y = 0
    · rw [h0, mul_zero]; positivity
    · have hb : bd ≤ 1 := by rw [hbd]; exact_mod_cast lwExpTerm3_svarF_support sz n x y h0
      have h1 : Real.exp c * Real.exp (-(c * 1)) ≤ Real.exp c * Real.exp (-(c * bd)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos c).le
        nlinarith [hc]
      calc u * svarF d (sz.L n) (sz.W n) (sz.lam n) x y ≤ u * Wd :=
            mul_le_mul_of_nonneg_left (lwExpTerm3_svarF_le sz n x y) hu0
        _ ≤ u * Wd * (Real.exp c * Real.exp (-(c * bd))) := by
            have : 0 ≤ u * Wd := mul_nonneg hu0 hWd0
            nlinarith [hex, h1]
  have hspec := lwSplus_spec (sz := sz) (n := n) hu0 (m := mE E) (by rw [hm]; simpa using hu1) x y
  have hsp : lwSplus sz n u (mE E) x y = lwS sz n u x y +
      mE E ^ 2 * ∑ w, lwSplus sz n u (mE E) x w * lwS sz n u w y := by
    linear_combination hspec
  have hsum : ‖∑ w, lwSplus sz n u (mE E) x w * lwS sz n u w y‖ ≤
      u * (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ w, ‖lwSplus sz n u (mE E) x w * lwS sz n u w y‖
        ≤ ∑ w, (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) *
            (u * svarF d (sz.L n) (sz.W n) (sz.lam n) w y) := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [norm_mul, lwExpTerm3_lwS_norm sz n hu0]
          by_cases h0 : svarF d (sz.L n) (sz.W n) (sz.lam n) w y = 0
          · rw [h0, mul_zero, mul_zero, mul_zero]
          · have hwy : lwBdist d (sz.L n) (sz.W n) w y ≤ 1 := lwExpTerm3_svarF_support sz n w y h0
            have htri := auxGraph_bdist_triangle x w y
            have hxw : bd ≤ (lwBdist d (sz.L n) (sz.W n) x w : ℝ) + 1 := by
              have : lwBdist d (sz.L n) (sz.W n) x y ≤ lwBdist d (sz.L n) (sz.W n) x w + 1 := by omega
              rw [hbd]; exact_mod_cast this
            have hdw := hdec sz n hl hlΛ u E hu0 hu1 hE x w
            have h1 : Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x w : ℝ))) ≤
                Real.exp c * Real.exp (-(c * bd)) := by
              rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [hc]
            have h2 : ‖lwSplus sz n u (mE E) x w‖ ≤ C₀ * Wd * (Real.exp c * Real.exp (-(c * bd))) :=
              hdw.trans (mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₀.le hWd0))
            exact mul_le_mul_of_nonneg_right h2 (mul_nonneg hu0 (svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) w y))
      _ = (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) * ∑ w, u * svarF d (sz.L n) (sz.W n) (sz.lam n) w y := by
          rw [Finset.mul_sum]
      _ = _ := by rw [lwExpTerm3_svarF_col sz n u y]; ring
  have hmm : ‖mE E ^ 2‖ = 1 := by rw [norm_pow, hm]; simp
  have hSp : ‖lwSplus sz n u (mE E) x y‖ ≤ u * Wd * (Real.exp c * Real.exp (-(c * bd))) +
      u * (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) := by
    rw [hsp]
    refine (norm_add_le _ _).trans (add_le_add hS ?_)
    rw [norm_mul, hmm, one_mul]; exact hsum
  have hfin : u * Wd * (Real.exp c * Real.exp (-(c * bd))) + u * (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) =
      u * (Real.exp c * (1 + C₀)) * Wd * Real.exp (-(c * bd)) := by ring
  constructor
  · calc ‖lwS sz n u x y‖ ≤ u * Wd * (Real.exp c * Real.exp (-(c * bd))) := hS
      _ ≤ u * (Real.exp c * (1 + C₀)) * Wd * Real.exp (-(c * bd)) := by
          rw [← hfin]
          have : 0 ≤ u * (C₀ * Wd * (Real.exp c * Real.exp (-(c * bd)))) :=
            mul_nonneg hu0 (mul_nonneg (mul_nonneg hC₀.le hWd0) (by positivity))
          linarith
  · rw [← hfin]; exact hSp

end SpDecay

section Pathwise

variable {d : ℕ} (sz : Sizes d)

theorem lwExpTerm3_Data_G (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    (LWG5Data sz n E t ω).G x y = Gt sz n E t true ω x y := rfl

theorem lwExpTerm3_Data_M (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    (LWG5Data sz n E t ω).M x y = if x = y then mE E else 0 := by
  simp [LWG5Data, lwSampleData, Matrix.diagonal_apply]

theorem lwExpTerm3_sizeConst_smul {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I) (hΓ : Γ.nV - Γ.nM ≤ Γ.nW) (t C₁ e : ℝ) :
    Γ.sizeConst (t * C₁) (t * C₁ * e) = t ^ Γ.nW * Γ.sizeConst C₁ (C₁ * e) := by
  unfold LGraph.sizeConst
  obtain ⟨b, hb⟩ : ∃ b, Γ.nW = (Γ.nV - Γ.nM) + b := ⟨Γ.nW - (Γ.nV - Γ.nM), by omega⟩
  have hb' : Γ.nW - (Γ.nV - Γ.nM) = b := by omega
  rw [hb', hb, pow_add]
  have : (t * C₁ * e) = t * (C₁ * e) := by ring
  rw [this, mul_pow, mul_pow, mul_pow]
  ring

end Pathwise

section PrecPieces

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{u,K} ≤ W^{-d} B_{u,0} = Bctl` (copy of `localAvg1_STWB_le`, `Induction/LocalAvg1.lean:94`, not among the imports). -/
private theorem lwExpTerm3_STWB_le (n : ℕ) (u : ℝ) (K : ℕ) : STWB sz n u K ≤ sz.Bctl n u := by
  unfold STWB Sizes.Bctl Bparam
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : (1 : ℝ) ≤ ((K : ℝ) + 1) ^ (d - 2) :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)])
  have h2 : (((K : ℝ) + 1) ^ (d - 2))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have hA : 0 ≤ (sz.lam n ^ 2 + |1 - u|)⁻¹ := by positivity
  have h3 : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ = 1 := by simp
  rw [h3]
  nlinarith [mul_le_mul_of_nonneg_left h2 hA]

/-- **`E₁`**: the entries `‖(G_t - M)_{xy}‖ ≤ N^{τ'} (W^{-d}B_{t,0})^{1/2}` w.h.p. (`STLocalEntry`). -/
theorem lwExpTerm3_entry_whp {E t : ℕ → ℝ} (hLE : STLocalEntry sz E t) {τ' : ℝ} (hτ' : 0 < τ') :
    sz.Whp (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖STGM sz n (E n) (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))}) := by
  refine HighProbAt.mono (Sizes.Prec.whp sz hLE (τ := 2 * τ') (by positivity)) (Eventually.of_forall fun n ω hω x y => ?_)
  have h1 := hω (x, y)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hB : STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) ≤ sz.Bctl n (t n) :=
    lwExpTerm3_STWB_le sz n _ _
  have hpow : 0 < ((sz.size n : ℕ) : ℝ) ^ (2 * τ') := Real.rpow_pos_of_pos hN0 _
  have h2 : ‖STGM sz n (E n) (t n) ω x y‖ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n) :=
    h1.trans (mul_le_mul_of_nonneg_left hB hpow.le)
  have hB0 : 0 ≤ sz.Bctl n (t n) := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hpow hneg
    nlinarith [sq_nonneg ‖STGM sz n (E n) (t n) ω x y‖]
  have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 * τ') = (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have h3 : ‖STGM sz n (E n) (t n) ω x y‖ ^ 2 ≤
      (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB0, ← e1]; exact h2
  exact le_of_sq_le_sq h3 (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.sqrt_nonneg _))

/-- **The entry law `‖G_t - M‖_max ≺ W^{-ε₁}`** (premise of `lwGbyXi_holds`) from `STLocalEntry` and the
smallness `W^{-d}B_{t,0} ≤ 2 N^{-c₀}` (`scaleFacts_R1`), `ε₁ = d c₀ / 4`. -/
theorem lwExpTerm3_hent {E t : ℕ → ℝ} (hsz : sz.SizeTendsto) (hd : 0 < d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hB : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀)) (hLE : STLocalEntry sz E t) :
    Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 4))) := by
  refine StochDomAt.of_subset hLE fun τ hτ => ⟨τ, hτ, ?_⟩
  have hc2 : 0 < c₀ / 2 := by positivity
  filter_upwards [hB, (tendsto_rpow_atTop hc2).comp hsz |>.eventually (eventually_ge_atTop (2 : ℝ))] with n hBn hN2
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN2' : (2 : ℝ) ≤ N ^ (c₀ / 2) := hN2
  have hu' : N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 4)) < ‖STGM sz n (E n) (t n) ω u.1 u.2‖ := hu
  have hWp : 0 < ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 4)) := Real.rpow_pos_of_pos hW0 _
  have hNτ : 0 < N ^ τ := Real.rpow_pos_of_pos hN0 _
  have hsq := pow_lt_pow_left₀ hu' (mul_nonneg hNτ.le hWp.le) two_ne_zero
  -- `N^{-c₀/2} ≤ W^{-d c₀/4}`... precisely `W^{d c₀/2} ≤ N^{c₀/2}`
  have hWN : ((sz.W n : ℕ) : ℝ) ^ (d * c₀ / 2) ≤ N ^ (c₀ / 2) := by
    have := sz.W_rpow_le hd n (τ := d * c₀ / 2) (by positivity)
    have e : d * c₀ / 2 / d = c₀ / 2 := by field_simp
    rwa [e] at this
  have hWinv : N ^ (-(c₀ / 2)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2)) := by
    rw [Real.rpow_neg hN0.le, Real.rpow_neg hW0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) hWN
  have e2 : (((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 4))) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have e3 : (N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 4))) ^ 2 = N ^ τ * (N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2))) := by
    rw [mul_pow, e2]
    have : (N ^ τ) ^ 2 = N ^ τ * N ^ τ := sq _
    rw [this]; ring
  have hN1τ : (1 : ℝ) ≤ N ^ τ := Real.one_le_rpow hN1 hτ.le
  -- `N^τ STWB ≤ N^τ · 2 N^{-c₀} ≤ N^τ N^τ W^{-d c₀/2}`
  have hB2 : 2 * N ^ (-c₀) ≤ N ^ (-(c₀ / 2)) := by
    have : N ^ (-c₀) = N ^ (-(c₀ / 2)) * N ^ (-(c₀ / 2)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h2' : N ^ (-(c₀ / 2)) * 2 ≤ 1 := by
      have : N ^ (-(c₀ / 2)) = (N ^ (c₀ / 2))⁻¹ := Real.rpow_neg hN0.le _
      rw [this]
      have hp : 0 < N ^ (c₀ / 2) := Real.rpow_pos_of_pos hN0 _
      rw [inv_mul_le_iff₀ hp]; linarith
    have hp : 0 < N ^ (-(c₀ / 2)) := Real.rpow_pos_of_pos hN0 _
    nlinarith
  have hSTWB : STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) ≤ sz.Bctl n (t n) :=
    lwExpTerm3_STWB_le sz n _ _
  show N ^ τ * STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) <
    ‖STGM sz n (E n) (t n) ω u.1 u.2‖ ^ 2
  refine lt_of_le_of_lt ?_ hsq
  rw [e3]
  refine mul_le_mul_of_nonneg_left ?_ hNτ.le
  calc STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) ≤ sz.Bctl n (t n) := hSTWB
    _ ≤ 2 * N ^ (-c₀) := hBn
    _ ≤ N ^ (-(c₀ / 2)) := hB2
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2)) := hWinv
    _ ≤ N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2)) := by
        have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-(d * c₀ / 2)) := Real.rpow_nonneg hW0.le _
        nlinarith

end PrecPieces

section XiHelp

variable {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ)

theorem lwExpTerm3_xiSq_nonneg (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) : 0 ≤ lwXiSq sz E t ρ n a₁ a₂ ω := by
  unfold lwXiSq
  positivity

theorem lwExpTerm3_xiVar_sq (a₁ a₂ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwXiVar sz E t ρ n a₁ a₂ ω ^ 2 = lwXiSq sz E t ρ n a₁ a₂ ω :=
  Real.sq_sqrt (lwExpTerm3_xiSq_nonneg sz E t ρ n a₁ a₂ ω)

end XiHelp

section PathwiseA

variable {d : ℕ} (sz : Sizes d)

/-- **Pathwise bound of one graph value** (`(Gammamuxy)`, `B:84-90`): on the good event, `|Γ_{xy}|` is `t^{n_W}` times
`K₁ Ψ^{ord} (q = 1 ? W^d cc² S2 : 1) + e^{-c r/2} K₂ size(Γ)`. -/
theorem lwExpTerm3_pathwise (hd : 3 ≤ d) (P : PGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM ≤ 1)
    (hatt : LWAttached P) (hext : ∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b)
    (Es ts ρs : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (C₁ c₁ : ℝ) (hC₁ : 0 ≤ C₁) (hc₁ : 0 < c₁)
    (hE : |Es n| < 2) (ht0 : 0 ≤ ts n) (ht1 : ts n < 1)
    (hS : ∀ x y, ‖lwS sz n (ts n) x y‖ ≤ ts n * C₁ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      Real.exp (-(c₁ * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))))
    (hSp : ∀ x y, ‖lwSplus sz n (ts n) (mE (Es n)) x y‖ ≤ ts n * C₁ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      Real.exp (-(c₁ * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))))
    (Ψ cc r : ℝ) (hΨ : 0 < Ψ) (hcc : 0 ≤ cc) (hr : 0 ≤ r)
    (hρ : ρs n = 2 * ((Fintype.card (P.E' ⊕ P.I') : ℝ) * r) + 1)
    (hwin : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ)
    (hE1 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (Es n) (ts n) ω x y‖ ≤ Ψ)
    (hE2 : ∀ (x y : Idx d (sz.L n) (sz.W n)) (a b : Zd d (sz.L n)), x ≠ y →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) x).1 - a) : ℝ) ≤ (Fintype.card (P.E' ⊕ P.I') : ℝ) * r →
      (zdistD d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - b) : ℝ) ≤ (Fintype.card (P.E' ⊕ P.I') : ℝ) * r →
      ‖Gt sz n (Es n) (ts n) true ω x y‖ ≤ cc * lwXiVar sz Es ts ρs n a b ω)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) :
    ‖P.val (LWG5Data sz n (Es n) (ts n) ω) ![v.1, v.2]‖ ≤ (ts n) ^ P.g.nW *
      (P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) *
          (Ψ ^ P.g.scalingOrder * (if P.g.nM = 1 then (((sz.W n : ℕ) : ℝ) ^ d) * (cc ^ 2 *
            (2 * (2 * ρs n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (Es n) (ts n))⁻¹ * (1 + Ψ)) +
              (2 * ρs n + 1) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹))) else 1)) +
        Real.exp (-(c₁ * r / 2)) * P.g.sizeConst C₁ (C₁ * expC (d - 2) (c₁ / 2)) *
          P.g.scalingSize Ψ (sz.W n) d (sz.L n)) := by
  classical
  set D := LWG5Data sz n (Es n) (ts n) ω with hD
  have hcnt := P.g.counters_le hN.1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hK1 : 0 ≤ P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) :=
    LGraph.sizeConst_nonneg P.g hC₁ (mul_nonneg hC₁ (by unfold expC; positivity))
  have hK2 : 0 ≤ P.g.sizeConst C₁ (C₁ * expC (d - 2) (c₁ / 2)) :=
    LGraph.sizeConst_nonneg P.g hC₁ (mul_nonneg hC₁ (by
      have h2 : 0 < c₁ / 2 := by positivity
      unfold expC
      positivity))
  have hρ0 : 0 ≤ ρs n := by rw [hρ]; positivity
  have hrhs : 0 ≤ (ts n) ^ P.g.nW *
      (P.g.sizeConst C₁ (C₁ * expC (d - 2) c₁) *
          (Ψ ^ P.g.scalingOrder * (if P.g.nM = 1 then (((sz.W n : ℕ) : ℝ) ^ d) * (cc ^ 2 *
            (2 * (2 * ρs n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (Es n) (ts n))⁻¹ * (1 + Ψ)) +
              (2 * ρs n + 1) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹))) else 1)) +
        Real.exp (-(c₁ * r / 2)) * P.g.sizeConst C₁ (C₁ * expC (d - 2) (c₁ / 2)) *
          P.g.scalingSize Ψ (sz.W n) d (sz.L n)) := by
    have hη : 0 < etaT (Es n) (ts n) := etaT_pos hE ht1
    have hsz : 0 ≤ P.g.scalingSize Ψ (sz.W n) d (sz.L n) := by
      unfold LGraph.scalingSize Counters.scalingSize
      positivity
    refine mul_nonneg (pow_nonneg ht0 _) (add_nonneg (mul_nonneg hK1 (mul_nonneg (zpow_nonneg hΨ.le _) ?_))
      (mul_nonneg (mul_nonneg (Real.exp_pos _).le hK2) hsz))
    split_ifs
    · positivity
    · exact zero_le_one
  by_cases hf : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![v.1, v.2] = ℓ' ∘ P.ext
  swap
  · rw [P.val_of_not D hf, norm_zero]
    exact hrhs
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [P.val_of_factor D hℓ']
  have hm : ‖mE (Es n)‖ = 1 := norm_mE hE.le
  have hxi : ∀ a, ∑ v, lwXiVar sz Es ts ρs n a v ω ^ 2 ≤
      2 * (2 * ρs n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (Es n) (ts n))⁻¹ * (1 + Ψ)) +
        (2 * ρs n + 1) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := fun a => by
    have := lwXi_ward_sum sz Es ts ρs n hE ht1 hρ0 ω hE1 a
    simpa only [lwExpTerm3_xiVar_sq] using this
  have hcol : ∀ a, ∑ v, lwXiVar sz Es ts ρs n v a ω ^ 2 ≤
      2 * (2 * ρs n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * etaT (Es n) (ts n))⁻¹ * (1 + Ψ)) +
        (2 * ρs n + 1) ^ d * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) := fun a => by
    simp only [lwXiVar_symm sz Es ts ρs n _ a ω]; exact hxi a
  have hdet := lwExpTerm3_det d hd (sz.L n) (sz.W n) P.g hN hnM hatt hext D (mE (Es n)) Ψ (ts n * C₁) c₁ r
    ((Fintype.card (P.E' ⊕ P.I') : ℝ) * r) cc _ (fun a b => lwXiVar sz Es ts ρs n a b ω)
    (lwExpTerm3_Data_M sz n _ _ ω)
    (fun x y hxy => by
      have h := hE1 x y
      simp only [STGM, hxy, ite_false, sub_zero] at h
      rw [hD, lwExpTerm3_Data_G]
      exact h)
    (fun x => by
      have h := hE1 x x
      simp only [STGM, ite_true] at h
      rw [hD, lwExpTerm3_Data_G]
      exact h)
    (mul_nonneg ht0 hC₁) hc₁ hS hSp hwin hΨ hr le_rfl hcc
    (fun a b => lwXiVar_nonneg sz Es ts ρs n a b ω)
    (fun x y a b hxy h1 h2 => hE2 x y a b hxy h1 h2) hxi hcol ℓ'
  obtain ⟨-, hdet⟩ := hdet
  rw [lwExpTerm3_sizeConst_smul P.g hcnt.2 (ts n) C₁ (expC (d - 2) c₁),
    lwExpTerm3_sizeConst_smul P.g hcnt.2 (ts n) C₁ (expC (d - 2) (c₁ / 2))] at hdet
  refine hdet.trans (le_of_eq ?_)
  ring

end PathwiseA

section Arith

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `Ψ^o` as powers of `N` and `B`, for `Ψ = N^{τ'} √B`. -/
theorem lwExpTerm3_Psi_zpow {N B τ' : ℝ} (hN : 0 < N) (hB : 0 < B) (o : ℤ) :
    (N ^ τ' * Real.sqrt B) ^ o = N ^ (τ' * (o : ℝ)) * B ^ ((o : ℝ) / 2) := by
  rw [mul_zpow, ← Real.rpow_intCast (N ^ τ') o, ← Real.rpow_mul hN.le, Real.sqrt_eq_rpow,
    ← Real.rpow_intCast (B ^ (1 / 2 : ℝ)) o, ← Real.rpow_mul hB.le]
  congr 2
  ring

/-- **The `q = 1` factor** `W^d cc² S2` is `≤ 3 cc² (2ρ+1)^{2d} (1+Ψ) η⁻¹`; the `q = 0` factor `1` as well. -/
theorem lwExpTerm3_Q_le (Γ : LGraph E I) (d : ℕ) (W : ℕ) (hW : 0 < W) {ρ cc Ψ η : ℝ} (hρ : 0 ≤ ρ) (hcc : 1 ≤ cc)
    (hΨ : 0 ≤ Ψ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) else 1) ≤
      3 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by positivity
  have hM1 : 1 ≤ 2 * ρ + 1 := by linarith
  have hMd : (2 * ρ + 1) ^ d ≤ (2 * ρ + 1) ^ (2 * d) := pow_le_pow_right₀ hM1 (by omega)
  have hη' : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  have hcc2 : 1 ≤ cc ^ 2 := one_le_pow₀ hcc
  have hM2 : 1 ≤ (2 * ρ + 1) ^ (2 * d) := one_le_pow₀ hM1
  have h1Ψ : 1 ≤ 1 + Ψ := by linarith
  have hpos : 0 ≤ cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by positivity
  split_ifs with h
  · have e : ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) =
        cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * (η⁻¹ * (1 + Ψ)) + (2 * ρ + 1) ^ d) := by
      field_simp
    rw [e]
    have : 2 * (2 * ρ + 1) ^ (2 * d) * (η⁻¹ * (1 + Ψ)) + (2 * ρ + 1) ^ d ≤
        3 * ((2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹) := by
      have h3 : (2 * ρ + 1) ^ d ≤ (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by
        calc (2 * ρ + 1) ^ d ≤ (2 * ρ + 1) ^ (2 * d) := hMd
          _ = (2 * ρ + 1) ^ (2 * d) * 1 * 1 := by ring
          _ ≤ (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by gcongr
      nlinarith
    calc cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * (η⁻¹ * (1 + Ψ)) + (2 * ρ + 1) ^ d)
        ≤ cc ^ 2 * (3 * ((2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  · calc (1 : ℝ) ≤ cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by
          calc (1 : ℝ) = 1 * 1 * 1 * 1 := by ring
            _ ≤ _ := by gcongr
      _ ≤ 3 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by nlinarith

end Arith

section Arith2

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The size term: `size(Γ) ≤ N^{n_M + n_S + n_V}` (`Ψ ≤ N`, `L^d, W^d ≤ N`, `W ≥ 1`). -/
theorem lwExpTerm3_size_le (Γ : LGraph E I) (d L W : ℕ) (hW : 0 < W) {N Ψ : ℝ} (hN : 1 ≤ N) (hΨ0 : 0 < Ψ) (hΨN : Ψ ≤ N)
    (hLN : (L : ℝ) ^ d ≤ N) (hWN : (W : ℝ) ^ d ≤ N) :
    Γ.scalingSize Ψ W d L ≤ N ^ (Γ.nM + Γ.nS + Γ.nV) := by
  unfold LGraph.scalingSize Counters.scalingSize LGraph.counters
  simp only
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hN0 : 0 < N := by linarith
  have h1 : ((L : ℝ) ^ d) ^ Γ.nM ≤ N ^ Γ.nM := pow_le_pow_left₀ (by positivity) hLN _
  have h2 : Ψ ^ Γ.nS ≤ N ^ Γ.nS := pow_le_pow_left₀ hΨ0.le hΨN _
  have h3 : (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ))) ≤ N ^ Γ.nV := by
    have h4 : (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ))) ≤ (W : ℝ) ^ ((d : ℤ) * Γ.nV) :=
      zpow_le_zpow_right₀ hW1 (by nlinarith [(Nat.cast_nonneg Γ.nW : (0 : ℤ) ≤ Γ.nW), (Nat.cast_nonneg d : (0 : ℤ) ≤ d)])
    refine h4.trans ?_
    rw [_root_.zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hWN _
  have hpos3 : 0 ≤ (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ))) := by positivity
  calc ((L : ℝ) ^ d) ^ Γ.nM * Ψ ^ Γ.nS * (W : ℝ) ^ (-(d : ℤ) * ((Γ.nW : ℤ) - (Γ.nV : ℤ)))
      ≤ N ^ Γ.nM * N ^ Γ.nS * N ^ Γ.nV := by gcongr
    _ = _ := by rw [pow_add, pow_add]

end Arith2

section Arith3

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The arithmetic of the pathwise bound**: `F ≤ N^τ η⁻¹ B^{ord/2} + N^{-D}`. -/
theorem lwExpTerm3_arith (Γ : LGraph E I) (d L W : ℕ) (hW : 0 < W)
    {N B η ρ r Ψ cc K₁ K₂ τ τ' D c₁ : ℝ}
    (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hΨ : Ψ = N ^ τ' * Real.sqrt B) (hcc : cc = N ^ τ') (hτ'0 : 0 < τ') (hτ'1 : τ' ≤ 1)
    (hτ' : τ' * ((|Γ.scalingOrder| : ℤ) + 2 * d + 3) ≤ τ / 2)
    (hρ0 : 0 ≤ ρ) (hρN : ρ + 1 ≤ N ^ τ')
    (hK1 : 0 ≤ K₁) (hK1N : 6 * 4 ^ d * K₁ ≤ N ^ (τ / 2)) (hK2 : 0 ≤ K₂) (hK2N : K₂ ≤ N)
    (hexp : Real.exp (-(c₁ * r / 2)) ≤ N ^ (-(D + ((Γ.nM + Γ.nS + Γ.nV : ℕ) : ℝ) + 1)))
    (hLN : (L : ℝ) ^ d ≤ N) (hWN : (W : ℝ) ^ d ≤ N) :
    K₁ * (Ψ ^ Γ.scalingOrder * (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) else 1)) +
      Real.exp (-(c₁ * r / 2)) * K₂ * Γ.scalingSize Ψ W d L ≤
    N ^ τ * (η⁻¹ * B ^ ((Γ.scalingOrder : ℝ) / 2)) + N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hNτ' : 1 ≤ N ^ τ' := Real.one_le_rpow hN hτ'0.le
  have hsB : Real.sqrt B ≤ 1 := Real.sqrt_le_one.2 hB1 |>.trans' le_rfl
  have hsB0 : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
  have hΨ0 : 0 < Ψ := by rw [hΨ]; positivity
  have hΨ1 : Ψ ≤ N ^ τ' := by
    rw [hΨ]; calc N ^ τ' * Real.sqrt B ≤ N ^ τ' * 1 := by gcongr
      _ = _ := mul_one _
  have hNτ'N : N ^ τ' ≤ N := by
    calc N ^ τ' ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hτ'1
      _ = N := Real.rpow_one N
  have hη' : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  -- the second term
  have hF2 : Real.exp (-(c₁ * r / 2)) * K₂ * Γ.scalingSize Ψ W d L ≤ N ^ (-D) := by
    have hsz := lwExpTerm3_size_le Γ d L W hW hN hΨ0 (hΨ1.trans hNτ'N) hLN hWN
    have hsz0 : 0 ≤ Γ.scalingSize Ψ W d L := by
      unfold LGraph.scalingSize Counters.scalingSize; positivity
    set m : ℕ := Γ.nM + Γ.nS + Γ.nV with hm
    have e1 : N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m = N ^ (-D) := by
      rw [show N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m = N ^ (-(D + (m : ℝ) + 1)) * N ^ (1 : ℝ) * N ^ (m : ℝ) by
        rw [Real.rpow_one, Real.rpow_natCast], ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    calc Real.exp (-(c₁ * r / 2)) * K₂ * Γ.scalingSize Ψ W d L
        ≤ N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m := by
          gcongr
      _ = N ^ (-D) := e1
  -- the first term
  set o : ℤ := Γ.scalingOrder with ho
  have hQ := lwExpTerm3_Q_le Γ d W hW hρ0 (hcc ▸ hNτ') hΨ0.le hη0 hη1
  have hQ0 : 0 ≤ (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) else 1) := by
    split_ifs
    · have : 0 < cc := by rw [hcc]; positivity
      positivity
    · exact zero_le_one
  have hMbd : 2 * ρ + 1 ≤ 2 * N ^ τ' := by linarith
  have hΨ2 : 1 + Ψ ≤ 2 * N ^ τ' := by linarith
  have hM2 : (2 * ρ + 1) ^ (2 * d) ≤ (2 * N ^ τ') ^ (2 * d) := pow_le_pow_left₀ (by linarith) hMbd _
  have hQb : 3 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ ≤
      6 * 4 ^ d * N ^ (τ' * (2 * d + 3)) * η⁻¹ := by
    have hccN : cc ^ 2 = N ^ (2 * τ') := by
      rw [hcc, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hpow : (2 * N ^ τ') ^ (2 * d) = 4 ^ d * N ^ (τ' * (2 * d)) := by
      have h4 : (2 : ℝ) ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
      have h5 : (N ^ τ') ^ (2 * d) = N ^ (τ' * (2 * d)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
      rw [mul_pow, h4, h5]
    have hN3 : N ^ (2 * τ') * N ^ (τ' * (2 * d)) * N ^ τ' = N ^ (τ' * (2 * d + 3)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    calc 3 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹
        ≤ 3 * N ^ (2 * τ') * (4 ^ d * N ^ (τ' * (2 * d))) * (2 * N ^ τ') * η⁻¹ := by
          rw [hccN, ← hpow]; gcongr
      _ = 6 * 4 ^ d * (N ^ (2 * τ') * N ^ (τ' * (2 * d)) * N ^ τ') * η⁻¹ := by ring
      _ = _ := by rw [hN3]
  have hΨo : Ψ ^ o = N ^ (τ' * (o : ℝ)) * B ^ ((o : ℝ) / 2) := by
    rw [hΨ]; exact lwExpTerm3_Psi_zpow hN0 hB0 o
  have hΨo0 : 0 ≤ Ψ ^ o := zpow_nonneg hΨ0.le o
  have hexp1 : N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3)) ≤ N ^ (τ / 2) := by
    have h1 : (o : ℝ) ≤ ((|o| : ℤ) : ℝ) := by exact_mod_cast le_abs_self o
    calc N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3)) = N ^ (τ' * (o : ℝ) + τ' * (2 * d + 3)) :=
          (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ (τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3)) :=
          Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [hτ'0])
      _ ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hN hτ'
  have hF1 : K₁ * (Ψ ^ o * (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) else 1)) ≤ N ^ τ * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
    have hBo : 0 ≤ B ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
    calc K₁ * (Ψ ^ o * (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 *
          (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
            (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)))) else 1))
        ≤ K₁ * (Ψ ^ o * (6 * 4 ^ d * N ^ (τ' * (2 * d + 3)) * η⁻¹)) := by
          gcongr
          exact hQ.trans hQb
      _ = (6 * 4 ^ d * K₁) * (N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3))) * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          rw [hΨo]; ring
      _ ≤ N ^ (τ / 2) * N ^ (τ / 2) * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          gcongr
      _ = N ^ τ * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  exact add_le_add hF1 hF2

end Arith3

section ValLemmas

variable {d : ℕ} (sz : Sizes d)

theorem lwExpTerm3_lwS_zero (n : ℕ) : lwS sz n 0 = 0 := by
  ext x y; simp [lwS]

theorem lwExpTerm3_lwSplus_zero (n : ℕ) (m : ℂ) : lwSplus sz n 0 m = 0 := by
  unfold lwSplus
  rw [lwExpTerm3_lwS_zero, Matrix.zero_mul]

/-- At `t = 0` every waved edge vanishes, so the value of a graph with a waved edge is `0`. -/
theorem lwExpTerm3_val_zero (P : PGraph (Fin 2)) (hnW : P.g.nW ≠ 0) (n : ℕ) (E : ℝ) (ω : sz.SeqΩ)
    (ℓe : Fin 2 → Idx d (sz.L n) (sz.W n)) : P.val (LWG5Data sz n E 0 ω) ℓe = 0 := by
  classical
  unfold PGraph.val
  split_ifs with h
  · unfold LGraph.val
    refine Finset.sum_eq_zero fun ℓi _ => ?_
    unfold LGraph.term
    have hW : (P.g.waved.map (WEdge.val (LWG5Data sz n E 0 ω) (Sum.elim h.choose ℓi))).prod = 0 := by
      apply List.prod_eq_zero
      obtain ⟨e, he⟩ : ∃ e, e ∈ P.g.waved := List.exists_mem_of_length_pos (by
        have : P.g.waved.length ≠ 0 := hnW
        omega)
      refine List.mem_map.2 ⟨e, he, ?_⟩
      simp [WEdge.val, LWG5Data, lwSampleData, lwExpTerm3_lwS_zero, lwExpTerm3_lwSplus_zero]
    rw [hW]; ring
  · rfl

end ValLemmas

section ValBound

private theorem lwExpTerm3_norm_list_prod_le {α : Type*} (l : List α) (f : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ e ∈ l, ‖f e‖ ≤ B) : ‖(l.map f).prod‖ ≤ B ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ]
    refine (norm_mul_le _ _).trans ?_
    calc ‖f a‖ * ‖(l.map f).prod‖ ≤ B * B ^ l.length :=
          mul_le_mul (h a (List.mem_cons_self)) (ih fun e he => h e (List.mem_cons_of_mem a he))
            (norm_nonneg _) hB
      _ = _ := by ring

variable {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The envelope of a graph value: every solid edge `≤ g1 + m1`, every waved edge `≤ s`, every dotted edge `≤ 1`,
`|ι|^{n_V}` labellings. -/
theorem lwExpTerm3_val_norm_le (Γ : LGraph E I) (D : LData ι) {g1 m1 s : ℝ}
    (hg : ∀ x y, ‖D.G x y‖ ≤ g1) (hm : ∀ x y, ‖D.M x y‖ ≤ m1) (hs : ∀ x y, ‖D.S x y‖ ≤ s)
    (hsp : ∀ x y, ‖D.Sp x y‖ ≤ s) (hg0 : 0 ≤ g1) (hm0 : 0 ≤ m1) (hs0 : 0 ≤ s) (ℓe : E → ι) :
    ‖Γ.val D ℓe‖ ≤ ‖Γ.coeff‖ * (Fintype.card ι : ℝ) ^ Γ.nV * ((g1 + m1) ^ Γ.nS * s ^ Γ.nW) := by
  classical
  unfold LGraph.val
  have hterm : ∀ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * ((g1 + m1) ^ Γ.nS * s ^ Γ.nW) := by
    intro ℓi
    unfold LGraph.term
    have h1 := lwExpTerm3_norm_list_prod_le Γ.solid (SEdge.val D (Sum.elim ℓe ℓi)) (g1 + m1) (by linarith)
      (fun e _ => by
        unfold SEdge.val
        simp only
        split_ifs with hσ hc hc
        · exact (norm_sub_le _ _).trans (add_le_add (hg _ _) (hm _ _))
        · simpa using (hg _ _).trans (by linarith : g1 ≤ g1 + m1)
        · rw [norm_star]; exact (norm_sub_le _ _).trans (add_le_add (hg _ _) (hm _ _))
        · rw [norm_star]; simpa using (hg _ _).trans (by linarith : g1 ≤ g1 + m1))
    have h2 := lwExpTerm3_norm_list_prod_le Γ.waved (WEdge.val D (Sum.elim ℓe ℓi)) s hs0
      (fun e _ => by
        unfold WEdge.val
        split_ifs with hc hσ
        · exact hsp _ _
        · rw [norm_star]; exact hsp _ _
        · exact hs _ _)
    have h3 := lwExpTerm3_norm_list_prod_le Γ.dotted (DEdge.val (Sum.elim ℓe ℓi)) 1 zero_le_one
      (fun e _ => by
        unfold DEdge.val
        split_ifs <;> simp)
    rw [norm_mul, norm_mul, norm_mul]
    have hn1 : 0 ≤ ‖(Γ.solid.map (SEdge.val D (Sum.elim ℓe ℓi))).prod‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖(Γ.waved.map (WEdge.val D (Sum.elim ℓe ℓi))).prod‖ := norm_nonneg _
    have hn3 : 0 ≤ ‖(Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod‖ := norm_nonneg _
    have hS' : (g1 + m1) ^ Γ.solid.length = (g1 + m1) ^ Γ.nS := rfl
    have hW' : s ^ Γ.waved.length = s ^ Γ.nW := rfl
    rw [hS'] at h1; rw [hW'] at h2
    rw [one_pow] at h3
    calc ‖Γ.coeff‖ * ‖(Γ.solid.map (SEdge.val D (Sum.elim ℓe ℓi))).prod‖ *
          ‖(Γ.waved.map (WEdge.val D (Sum.elim ℓe ℓi))).prod‖ *
          ‖(Γ.dotted.map (DEdge.val (Sum.elim ℓe ℓi))).prod‖
        ≤ ‖Γ.coeff‖ * (g1 + m1) ^ Γ.nS * s ^ Γ.nW * 1 := by
          gcongr
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun ℓi _ => hterm ℓi).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  push_cast
  have : Γ.nV = Fintype.card I := rfl
  rw [this]
  ring_nf
  exact le_rfl

end ValBound

theorem lwExpTerm3_floor {N B η : ℝ} (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hNB : N⁻¹ ≤ B) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (o : ℤ) : N ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ η⁻¹ * B ^ ((o : ℝ) / 2) := by
  have hN0 : 0 < N := by linarith
  have hη' : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  have hB' : N ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ B ^ ((o : ℝ) / 2) := by
    rcases le_or_gt 0 o with ho | ho
    · have h1 : (|o| : ℤ) = o := abs_of_nonneg ho
      rw [h1]
      have ho' : (0 : ℝ) ≤ (o : ℝ) / 2 := by positivity
      calc N ^ (-((o : ℝ) / 2)) = (N⁻¹) ^ ((o : ℝ) / 2) := by
            rw [Real.inv_rpow hN0.le, Real.rpow_neg hN0.le]
        _ ≤ B ^ ((o : ℝ) / 2) := Real.rpow_le_rpow (by positivity) hNB ho'
    · have h1 : (o : ℝ) / 2 ≤ 0 := by
        have : (o : ℝ) < 0 := by exact_mod_cast ho
        linarith
      have h2 : 1 ≤ B ^ ((o : ℝ) / 2) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hB0 hB1 h1
      have h3 : N ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hN (by
          have : (0 : ℝ) ≤ ((|o| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg o
          linarith)
      exact h3.trans h2
  have hBo : 0 ≤ B ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  calc N ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤ B ^ ((o : ℝ) / 2) := hB'
    _ = 1 * B ^ ((o : ℝ) / 2) := (one_mul _).symm
    _ ≤ η⁻¹ * B ^ ((o : ℝ) / 2) := by gcongr

section XBound

variable {d : ℕ} (sz : Sizes d)

theorem lwExpTerm3_etaT_le_one {E t : ℝ} (hE : |E| < 2) (h0 : 0 ≤ t) (_ht : t < 1) : etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have h2 : 0 < (mE E).im := mE_im_pos hE
  unfold etaT
  nlinarith

/-- **The envelope of the rescaled value** `X = t^{-n_W} · Γ_{xy}`: `‖X‖ ≤ ‖coeff‖ N^{n_V} (η⁻¹ + 1)^{n_S} C^{n_W}`. -/
theorem lwExpTerm3_X_norm_le (P : PGraph (Fin 2)) (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {Cs : ℝ} (hCs : 0 ≤ Cs) (hS : ∀ x y, ‖lwS sz n t x y‖ ≤ t * Cs)
    (hSp : ∀ x y, ‖lwSplus sz n t (mE E) x y‖ ≤ t * Cs) (ω : sz.SeqΩ)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) :
    ‖((((t ^ P.g.nW : ℝ)⁻¹ : ℝ) : ℂ)) * P.val (LWG5Data sz n E t ω) ![v.1, v.2]‖ ≤
      ‖P.g.coeff‖ * ((sz.size n : ℕ) : ℝ) ^ P.g.nV * ((((etaT E t)⁻¹ + 1) ^ P.g.nS) * Cs ^ P.g.nW) := by
  classical
  have hη0 : 0 < etaT E t := etaT_pos hE ht1
  have hbound0 : 0 ≤ ‖P.g.coeff‖ * ((sz.size n : ℕ) : ℝ) ^ P.g.nV * ((((etaT E t)⁻¹ + 1) ^ P.g.nS) * Cs ^ P.g.nW) := by
    positivity
  by_cases h : t ^ P.g.nW = 0
  · rw [h]; simpa using hbound0
  · rw [norm_mul, Complex.norm_real, norm_inv, Real.norm_of_nonneg (pow_nonneg ht0 _)]
    have hpos : 0 < t ^ P.g.nW := lt_of_le_of_ne (pow_nonneg ht0 _) (Ne.symm h)
    by_cases hf : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![v.1, v.2] = ℓ' ∘ P.ext
    swap
    · rw [P.val_of_not _ hf, norm_zero, mul_zero]; exact hbound0
    obtain ⟨ℓ', hℓ'⟩ := hf
    rw [P.val_of_factor _ hℓ']
    have hz : (zt E t).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη0.ne'
    have hG : ∀ x y, ‖(LWG5Data sz n E t ω).G x y‖ ≤ (etaT E t)⁻¹ := fun x y => by
      have := lwStein_norm_lwG_le sz n hz t x y ω
      rwa [← etaT_eq_zt_im, abs_of_pos hη0] at this
    have hM : ∀ x y, ‖(LWG5Data sz n E t ω).M x y‖ ≤ 1 := fun x y => by
      rw [lwExpTerm3_Data_M]
      split_ifs
      · rw [norm_mE hE.le]
      · simp
    have hbd := lwExpTerm3_val_norm_le P.g (LWG5Data sz n E t ω) hG hM hS hSp (inv_nonneg.2 hη0.le) zero_le_one
      (mul_nonneg ht0 hCs) ℓ'
    have hcard : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = ((sz.size n : ℕ) : ℝ) := by
      simp [Sizes.size, Idx, card_Zd, mul_comm]
    rw [hcard] at hbd
    calc (t ^ P.g.nW)⁻¹ * ‖P.g.val (LWG5Data sz n E t ω) ℓ'‖
        ≤ (t ^ P.g.nW)⁻¹ * (‖P.g.coeff‖ * ((sz.size n : ℕ) : ℝ) ^ P.g.nV *
          ((((etaT E t)⁻¹ + 1) ^ P.g.nS) * (t * Cs) ^ P.g.nW)) :=
          mul_le_mul_of_nonneg_left hbd (inv_nonneg.2 hpos.le)
      _ = _ := by
          rw [mul_pow]
          field_simp

end XBound

theorem lwExpTerm3_poly {N η cn Cw : ℝ} (hN : 2 ≤ N) (hη : η⁻¹ ≤ N) (hη0 : 0 ≤ η⁻¹) (hcn : cn ≤ N)
    (hCw : Cw ≤ N) (hCw0 : 0 ≤ Cw) (nV nS : ℕ) :
    cn * N ^ nV * ((η⁻¹ + 1) ^ nS * Cw) ≤ N ^ (nV + 2 * nS + 2) := by
  have h1 : η⁻¹ + 1 ≤ N ^ 2 := by nlinarith
  have h2 : (η⁻¹ + 1) ^ nS ≤ (N ^ 2) ^ nS := pow_le_pow_left₀ (by linarith) h1 _
  have hN0 : 0 ≤ N := by linarith
  calc cn * N ^ nV * ((η⁻¹ + 1) ^ nS * Cw) ≤ N * N ^ nV * ((N ^ 2) ^ nS * N) := by gcongr
    _ = N ^ (nV + 2 * nS + 2) := by
        rw [← pow_mul]; ring

/-- **Target 3 (`(Gammamuxy)`, `q ∈ {0,1}`, `B:84-90`)**: for a normal packed graph with at most one internal
molecule, distinct external vertices in distinct molecules, and every internal molecule attached to two solid
edges, `|𝔼 Γ_{xy}| ≺ t^{n_W} η_t⁻¹ (W^{-d}B_{t,0})^{ord(Γ)/2}` (charge-blind; `t^{n_W}` from `S, S⁺ = O(t)`). -/
def LwGraphPrec1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → STLmax sz (STflowE z) t →
        ∀ P : PGraph (Fin 2), P.g.Normal → P.g.nM ≤ 1 → LWAttached P →
          (∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p _ => ‖∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
            (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
              (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

theorem lwGraphPrec1 (d : ℕ) : LwGraphPrec1 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLmax P hN hnM hAtt hext
  classical
  obtain ⟨hA, -, ht1, hRange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hz htz
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hA
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hEκ : ∀ n, |STflowE z n| ≤ 2 - κ := st6_flowE_le sz hz
  have hd0 : 0 < d := by omega
  have hsize := sz.tendsto_size hsz
  obtain ⟨Cs, cs, hCs, hcs, hSd⟩ := lwExpTerm3_Sp_decay d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  set c₀ : ℝ := min (2 * 𝔠 * 𝔡) (ε / 2) with hc₀def
  have hc₀ : 0 < c₀ := lt_min (by positivity) (by linarith)
  have hBsm := RBM.Ind.scaleFacts_R1 sz 𝔠 𝔡 (ε / 2) t h𝔡 hbw hWO hRange
  have hent := lwExpTerm3_hent sz hsz hd0 hc₀ (hBsm.mono fun n h => h (t n) le_rfl) hLE
  have hε₁ : 0 < (d : ℝ) * c₀ / 4 := by positivity
  set kk : ℝ := (Fintype.card (P.E' ⊕ P.I') : ℝ) with hkk
  set rr : ℕ → ℝ := fun n => Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hrr
  set RR : ℕ → ℝ := fun n => kk * rr n with hRR
  set ρρ : ℕ → ℝ := fun n => 2 * RR n + 1 with hρρ
  have hrr0 : ∀ n, 0 ≤ rr n := fun n => Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast sz.W_pos n)) _
  have hRR0 : ∀ n, 0 ≤ RR n := fun n => mul_nonneg (Nat.cast_nonneg _) (hrr0 n)
  have hGbyXi := lwGbyXi_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz ((d : ℝ) * c₀ / 4) hε₁ hent ρρ RR hRR0
    (fun n => le_rfl)
  -- the random statement
  set o : ℤ := P.g.scalingOrder with ho
  set X : ∀ n, (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) → sz.SeqΩ → ℂ := fun n v ω =>
    (((t n) ^ P.g.nW : ℝ)⁻¹ : ℝ) * P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] with hX
  have hB1 := st5_Bctl_le_one sz hκ hε hz htz
  have hηev := expAvg_eta_inv_le sz hκ hε hz
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (((P.g.nV + 2 * P.g.nS + 2 : ℕ)) : ℝ) := by
    filter_upwards [hηev, hlam, hsz.eventually_ge_atTop (max (max ‖P.g.coeff‖ (Cs ^ P.g.nW)) 2)] with n hηn hlamn hNn
    intro v ω
    obtain ⟨hS1, hS2⟩ : (∀ x y, ‖lwS sz n (t n) x y‖ ≤ t n * Cs) ∧
        (∀ x y, ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤ t n * Cs) := by
      have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hWi : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
      have hdrop : ∀ x y : Idx d (sz.L n) (sz.W n), t n * Cs * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
          Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ≤ t n * Cs := fun x y => by
        have he : Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ))) ≤ 1 :=
          Real.exp_le_one_iff.2 (by have := Nat.cast_nonneg (α := ℝ) (lwBdist d (sz.L n) (sz.W n) x y); nlinarith)
        have h0 : 0 ≤ t n * Cs := mul_nonneg (ht0 n) hCs.le
        calc t n * Cs * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(cs * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))
            ≤ t n * Cs * 1 * 1 := by gcongr
          _ = _ := by ring
      exact ⟨fun x y => ((hSd sz n hlamn.1 hlamn.2 (t n) (STflowE z n) (ht0 n) (ht1 n) (hEκ n) x y).1).trans (hdrop x y),
        fun x y => ((hSd sz n hlamn.1 hlamn.2 (t n) (STflowE z n) (ht0 n) (ht1 n) (hEκ n) x y).2).trans (hdrop x y)⟩
    have hbd := lwExpTerm3_X_norm_le sz P n (hE2 n) (ht0 n) (ht1 n) hCs.le hS1 hS2 ω v
    have hpoly := lwExpTerm3_poly (N := ((sz.size n : ℕ) : ℝ)) (η := etaT (STflowE z n) (t n))
      (cn := ‖P.g.coeff‖) (Cw := Cs ^ P.g.nW) ((le_max_right _ _).trans hNn)
      (hηn (t n) (htz n)) (inv_nonneg.2 (etaT_pos (hE2 n) (ht1 n)).le)
      (((le_max_left _ _).trans (le_max_left _ _)).trans hNn)
      (((le_max_right _ _).trans (le_max_left _ _)).trans hNn) (pow_nonneg hCs.le _) P.g.nV P.g.nS
    refine hbd.trans (hpoly.trans (le_of_eq ?_))
    rw [← Real.rpow_natCast]
  have hfloor : ∀ᶠ n in atTop, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤
        (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2) := by
    filter_upwards [hB1] with n hBn v
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact lwExpTerm3_floor hN1 (STBctl_pos sz n (ht1 n)) (hBn (t n) le_rfl) (expAvg_Bctl_ge sz n (ht0 n) (ht1 n))
      (etaT_pos (hE2 n) (ht1 n)) (lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)) o
  have hprecX : Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n v ω => ‖X n v ω‖)
      (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) := by
    refine StochDomAt.of_highProbAt_add_rpow_neg (P := sz.seqP) (size := sz.size) hsize
      (b := ((|o| : ℤ) : ℝ) / 2) ?_ ?_
    · refine HighProbAt.of_eventually_univ ?_
      filter_upwards [hfloor] with n hn ω v
      exact hn v
    · intro τ hτ D hD
      set T : ℝ := ((|o| : ℤ) : ℝ) + 2 * d + 4 with hT
      have habs0 : (0 : ℝ) ≤ ((|o| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg o
      have hT0 : 0 < T := by positivity
      set τ' : ℝ := min 1 (τ / (2 * T)) with hτ'def
      have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
      have hτ'1 : τ' ≤ 1 := min_le_left _ _
      have hτ'2 : τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3) ≤ τ / 2 := by
        have h1 : τ' ≤ τ / (2 * T) := min_le_right _ _
        calc τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3) ≤ τ / (2 * T) * T :=
              mul_le_mul h1 (by linarith) (by positivity) (by positivity)
          _ = τ / 2 := by field_simp
      have hE₁ := lwExpTerm3_entry_whp sz hLE hτ'0
      have hE₂ := Sizes.Prec.whp sz hGbyXi hτ'0
      refine HighProbAt.mono (HighProbAt.inter hsize hE₁ hE₂) ?_
      set K₁ : ℝ := P.g.sizeConst Cs (Cs * expC (d - 2) cs) with hK₁
      set K₂ : ℝ := P.g.sizeConst Cs (Cs * expC (d - 2) (cs / 2)) with hK₂
      set m : ℕ := P.g.nM + P.g.nS + P.g.nV with hm
      have hτ2 : 0 < τ / 2 := by positivity
      have hev1 : ∀ᶠ n in atTop, 6 * 4 ^ d * K₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
      have hev2 : ∀ᶠ n in atTop, K₂ ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually_ge_atTop _
      have hτ'2' : 0 < 2 * τ' := by positivity
      have hev3 : ∀ᶠ n in atTop, (𝔡⁻¹) ^ 2 + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') :=
        ((tendsto_rpow_atTop hτ'2').comp hsz).eventually_ge_atTop _
      have hev4 : ∀ᶠ n in atTop, ρρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by
        filter_upwards [lwXiRad_holds sz hsz (2 * kk) 1 (3 / 2) (by positivity) zero_le_one (by norm_num) τ' hτ'0]
          with n hn
        simp only [hρρ, hRR, hrr]
        linarith
      have hev5 : ∀ᶠ n in atTop, Real.exp (-(cs * rr n / 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + (m : ℝ) + 1)) := by
        obtain ⟨W₀, hW₀⟩ := lwTail_log32 hcs ((D + (m : ℝ) + 1) / 𝔠)
        have hWlarge : ∀ᶠ n in atTop, (W₀ : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
          have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
            (tendsto_rpow_atTop h𝔠).comp hsz
          filter_upwards [hbw, h1.eventually_ge_atTop (W₀ : ℝ)] with n hn1 hn2
          exact hn2.trans hn1
        filter_upwards [hWlarge, hbw] with n hn1 hn2
        have hWn : W₀ ≤ sz.W n := by exact_mod_cast hn1
        refine (hW₀ (sz.W n) hWn).trans ?_
        have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
        have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
        have hDm : 0 ≤ (D + (m : ℝ) + 1) / 𝔠 := by positivity
        calc ((sz.W n : ℕ) : ℝ) ^ (-((D + (m : ℝ) + 1) / 𝔠))
            ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-((D + (m : ℝ) + 1) / 𝔠)) :=
              Real.rpow_le_rpow_of_nonpos hNc hn2 (by linarith)
          _ = ((sz.size n : ℕ) : ℝ) ^ (-(D + (m : ℝ) + 1)) := by
              rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
      filter_upwards [hlam, hB1, hev1, hev2, hev3, hev4, hev5] with n hlamn hBn hK1n hK2n hwinn hradn htailn
      rintro ω ⟨hω1, hω2⟩ v
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
      have hB1' : sz.Bctl n (t n) ≤ 1 := hBn (t n) le_rfl
      have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (ht1 n)
      have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hΨ0 : 0 < ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) :=
        mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 hB0)
      -- the window `W^{-d/2} ≤ Ψ`
      have hwindow : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) := by
        rw [one_le_pow_mul_sq_iff (sz.W n) d hW0 hΨ0.le]
        have hsq : (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) ^ 2 =
            ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n) := by
          rw [mul_pow, Real.sq_sqrt hB0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
          congr 2; push_cast; ring
        rw [hsq]
        have hBge := STBctl_ge sz n (ht0 n) (ht1 n)
        have hl2 : sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
          have := pow_le_pow_left₀ hlamn.1.le hlamn.2 2
          linarith
        have hl0 : 0 < sz.lam n ^ 2 + 1 := by positivity
        have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * (sz.lam n ^ 2 + 1)⁻¹ := by
          rw [← div_eq_mul_inv, one_le_div hl0]; exact hl2.trans hwinn
        calc (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * (sz.lam n ^ 2 + 1)⁻¹ := h1
          _ = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ (2 * τ') *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹)) := by
              field_simp
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n)) := by
              gcongr
      obtain ⟨hS1, hS2⟩ := hSd sz n hlamn.1 hlamn.2 (t n) (STflowE z n) (ht0 n) (ht1 n) (hEκ n) |> fun h => (⟨fun x y => (h x y).1, fun x y => (h x y).2⟩ : _ ∧ _)
      have hpath := lwExpTerm3_pathwise sz hd P hN hnM hAtt hext (STflowE z) t ρρ n ω Cs cs hCs.le hcs (hE2 n)
        (ht0 n) (ht1 n) hS1 hS2 (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)))
        (((sz.size n : ℕ) : ℝ) ^ τ') (rr n) hΨ0 (Real.rpow_nonneg hN0.le _) (hrr0 n) rfl hwindow hω1
        (fun x y a b hxy h1 h2 => hω2 ⟨((x, y), (a, b)), hxy, h1, h2⟩) v
      have hLpos : 0 < sz.L n := by have := sz.three_le_L n; omega
      have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
        have h : (sz.L n) ^ d ≤ sz.size n :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
        exact_mod_cast h
      have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
        have h : (sz.W n) ^ d ≤ sz.size n :=
          Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hLpos) d
        exact_mod_cast h
      have hρ0 : 0 ≤ ρρ n := by simp only [hρρ, hRR]; have := hrr0 n; positivity
      have hK1nn : 0 ≤ K₁ := LGraph.sizeConst_nonneg P.g hCs.le (mul_nonneg hCs.le (by unfold expC; positivity))
      have hK2nn : 0 ≤ K₂ := LGraph.sizeConst_nonneg P.g hCs.le (mul_nonneg hCs.le (by
        have h2 : 0 < cs / 2 := by positivity
        unfold expC; positivity))
      have harith := lwExpTerm3_arith P.g d (sz.L n) (sz.W n) (sz.W_pos n) hN1 hB0 hB1' hη0 hη1 rfl rfl hτ'0 hτ'1 hτ'2
        hρ0 hradn hK1nn hK1n hK2nn hK2n htailn hLN hWN
      show ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) +
        ((sz.size n : ℕ) : ℝ) ^ (-D)
      simp only [hX]
      by_cases h : (t n) ^ P.g.nW = 0
      · rw [h]
        simp only [_root_.inv_zero, Complex.ofReal_zero, zero_mul, norm_zero]
        have hη' : 0 < (etaT (STflowE z n) (t n))⁻¹ := inv_pos.2 hη0
        positivity
      · rw [norm_mul, Complex.norm_real, norm_inv, Real.norm_of_nonneg (pow_nonneg (ht0 n) _)]
        have hpos : 0 < (t n) ^ P.g.nW := lt_of_le_of_ne (pow_nonneg (ht0 n) _) (Ne.symm h)
        calc ((t n) ^ P.g.nW)⁻¹ * ‖P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2]‖
            ≤ ((t n) ^ P.g.nW)⁻¹ * ((t n) ^ P.g.nW * (K₁ * (_ * _) + _)) :=
              mul_le_mul_of_nonneg_left hpath (inv_nonneg.2 hpos.le)
          _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
          _ ≤ _ := harith
  have hint := lwExpTerm_prec_integral sz X (fun n v => (etaT (STflowE z n) (t n))⁻¹ *
    (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) hsz henv hfloor hprecX
  have hdet := (st6_prec_det_iff sz hsz (fun n (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) =>
      ‖∫ ω, X n v ω ∂(sz.seqP)‖) (fun n v => (etaT (STflowE z n) (t n))⁻¹ *
      (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))).1 hint
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [hdet τ hτ] with n hn v
  have h1 := hn v
  have hval : ∀ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] =
      (((t n) ^ P.g.nW : ℝ) : ℂ) * X n v ω := by
    intro ω
    simp only [hX]
    by_cases h : (t n) ^ P.g.nW = 0
    · have hnW : P.g.nW ≠ 0 := by
        intro h0; rw [h0, pow_zero] at h; exact one_ne_zero h
      have ht : t n = 0 := (pow_eq_zero_iff hnW).1 h
      have h0 : P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] = 0 := by
        rw [ht]; exact lwExpTerm3_val_zero sz P hnW n _ ω _
      rw [h0, h]; simp
    · rw [Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast h)]
  have hI : ∫ ω, P.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP) =
      (((t n) ^ P.g.nW : ℝ) : ℂ) * ∫ ω, X n v ω ∂(sz.seqP) := by
    simp_rw [hval]; exact integral_const_mul _ _
  rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ht0 n) _)]
  calc (t n) ^ P.g.nW * ‖∫ ω, X n v ω ∂(sz.seqP)‖
      ≤ (t n) ^ P.g.nW * (((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))) := mul_le_mul_of_nonneg_left h1 (pow_nonneg (ht0 n) _)
    _ = _ := by ring




/-! ## 4. Target 4: the assembly `LWExpG5'` from the expansion pin -/

section ZeroCase

theorem lwExpTerm3_wprod {ι B : Type*} [DecidableEq B] (bl : ι → B) (c₀ : ℂ) (a₂ a₁ a₃ b a : B) (x : ι) :
    lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b x * lwExpTerm2_dw bl c₀ a₂ x * lwExpTerm2_dw bl c₀ a₁ x *
      lwExpTerm2_dw bl c₀ a₃ x = if (a₂ = a ∧ a₁ = a ∧ a₃ = a ∧ b = a) ∧ bl x = a then c₀ ^ 5 else 0 := by
  unfold lwExpTerm2_dw
  split_ifs <;> simp_all <;> ring


variable {d : ℕ} (sz : Sizes d) (n : ℕ)

theorem lwExpTerm3_Gt_zero {E : ℝ} (hE : |E| < 2) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) :
    Gt sz n E 0 true ω i j = if i = j then mE E else 0 := by
  have hm0 : mE E ≠ 0 := lwWx_mE_ne E hE
  have hz : zt E 0 = -(mE E)⁻¹ := by
    have hm := mE_mul hE.le
    simp only [zt, Complex.ofReal_zero, sub_zero, one_mul]
    field_simp
    linear_combination hm
  have hH : sz.seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
  have hz0 : zt E 0 ≠ 0 := by rw [hz]; exact neg_ne_zero.2 (inv_ne_zero hm0)
  have hG : Gres (sz.seqHflow n 0 ω) (zt E 0) true = mE E • (1 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := by
    rw [hH, lwWx_gres_zero hz0, hz, neg_neg, inv_inv]
  show Gres (sz.seqHflow n 0 ω) (zt E 0) true i j = _
  rw [hG]
  simp [Matrix.one_apply]

theorem lwExpTerm3_Gt_zero_s {E : ℝ} (hE : |E| < 2) (s : Bool) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) :
    Gt sz n E 0 s ω i j = if i = j then mSigma E s else 0 := by
  cases s
  · rw [lwExpTerm2_Gt_false, lwExpTerm3_Gt_zero sz n hE]
    by_cases h : j = i
    · subst h; simp [mSigma]
    · simp [h, Ne.symm h, mSigma]
  · rw [lwExpTerm3_Gt_zero sz n hE]; simp [mSigma]

theorem lwExpTerm3_Lloop5_zero {E : ℝ} (hE : |E| < 2) (s : Bool) (a₂ a₁ a₃ b a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E 0 ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω =
      if a₂ = a ∧ a₁ = a ∧ a₃ = a ∧ b = a then
        (mE E) ^ 4 * mSigma E s * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹)) ^ 4 else 0 := by
  classical
  rw [lwExpTerm3_Lloop5_expand]
  simp only [lwExpTerm3_Gt_zero sz n hE, lwExpTerm3_Gt_zero_s sz n hE s]
  have hWd : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have hcollapse : ∀ (u₁ u₂ u₃ u₄ u₅ : Idx d (sz.L n) (sz.W n) → ℂ) (m ms : ℂ),
      ∑ x, ∑ y, ∑ α, ∑ γ, ∑ β, u₁ x * u₂ y * u₃ α * u₄ γ * u₅ β *
        ((((((if x = α then m else 0) * if α = γ then m else 0) * if γ = β then m else 0) *
          if β = y then m else 0) * if y = x then ms else 0)) =
      m ^ 4 * ms * ∑ x, u₁ x * u₂ x * u₃ x * u₄ x * u₅ x := by
    intro u₁ u₂ u₃ u₄ u₅ m ms
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single x]
        · rw [Finset.sum_eq_single x]
          · simp only [ite_true]; ring
          · intro γ _ hγ; simp [hγ]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro α _ hα; simp [Finset.sum_eq_zero, hα]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro y _ hy; simp [Finset.sum_eq_zero, hy]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro y _ hy; simp [hy]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hcollapse (lwExpTerm2_w sz n a) (lwExpTerm2_w sz n b) (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n a₁)
    (lwExpTerm2_w sz n a₃) (mE E) (mSigma E s)]
  have hkey := lwExpTerm3_wprod (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) a₂ a₁ a₃ b a
  simp only [lwExpTerm2_w]
  rw [Finset.sum_congr rfl fun x _ => hkey x]
  by_cases hP : a₂ = a ∧ a₁ = a ∧ a₃ = a ∧ b = a
  · simp only [hP, true_and, and_self, ite_true]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := lwExpTerm2_hc sz n a
    have e : (((Finset.univ.filter fun x : Idx d (sz.L n) (sz.W n) =>
        lwExpTerm2_bl d (sz.L n) (sz.W n) x = a).card : ℕ) : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 5 =
        ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 4 := by
      calc _ = ((((Finset.univ.filter fun x : Idx d (sz.L n) (sz.W n) =>
            lwExpTerm2_bl d (sz.L n) (sz.W n) x = a).card : ℕ) : ℂ) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹)) *
            ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 4 := by ring
        _ = _ := by rw [hc, one_mul]
    rw [e]
  · simp only [hP, false_and, ite_false, Finset.sum_const_zero, mul_zero]

end ZeroCase
section PairSum

theorem lwExpTerm3_list_norm_sum_le {α : Type*} (l : List α) (f : α → ℂ) (G : ℝ) (h : ∀ q ∈ l, ‖f q‖ ≤ G) :
    ‖(l.map f).sum‖ ≤ l.length * G := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine (norm_add_le _ _).trans ?_
    have h1 := h a (List.mem_cons_self)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem a hq)
    linarith

/-- The sum of a function over `A × B'` with `g x y ≤ G₁ + 1[x = y] G₂`: at most `M² G₁ + M G₂`. -/
theorem lwExpTerm3_pairsum {ι : Type*} [DecidableEq ι] (A B' : Finset ι) {M : ℕ} (hA : A.card = M) (hB : B'.card = M)
    (g : ι → ι → ℝ) {G₁ G₂ : ℝ} (hG₂ : 0 ≤ G₂) (hg : ∀ x y, g x y ≤ G₁ + if x = y then G₂ else 0) :
    ∑ x ∈ A, ∑ y ∈ B', g x y ≤ (M : ℝ) ^ 2 * G₁ + M * G₂ := by
  calc ∑ x ∈ A, ∑ y ∈ B', g x y ≤ ∑ x ∈ A, ∑ y ∈ B', (G₁ + if x = y then G₂ else 0) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hg x y
    _ = ∑ x ∈ A, ((B'.card : ℝ) * G₁ + ∑ y ∈ B', if x = y then G₂ else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ A, ((B'.card : ℝ) * G₁ + G₂) := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine add_le_add le_rfl ?_
        rw [Finset.sum_ite_eq]
        split_ifs <;> simp [hG₂]
    _ = (M : ℝ) ^ 2 * G₁ + M * G₂ := by
        rw [Finset.sum_const, nsmul_eq_mul, hA, hB]; ring

end PairSum

def LWG5Expand (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List (ℕ × PGraph (Fin 2)),
    (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttached q.2 ∧
        (∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∧
        (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧
    ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
      (x y : Idx d (sz.L n) (sz.W n)),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        ((Ls k s).map fun q =>
          (mE E) ^ q.1 * ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum

section T4pos

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- A packed graph with merged external vertices vanishes at distinct labels. -/
theorem lwExpTerm3_val_ext_ne (P : PGraph (Fin 2)) (h : P.ext 0 = P.ext 1) {x y : Idx d (sz.L n) (sz.W n)}
    (hxy : x ≠ y) (D : LData (Idx d (sz.L n) (sz.W n))) : P.val D ![x, y] = 0 := by
  classical
  refine P.val_of_not D ?_
  rintro ⟨ℓ', hℓ'⟩
  apply hxy
  have h0 := congrFun hℓ' 0
  have h1 := congrFun hℓ' 1
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [h0, h1, h]

/-- The per-graph bound at a pair `(x, y)`: `‖𝔼 Γ_{xy}‖ ≤ N^{τ'} t^e η⁻¹ (B^{5/2} + 1_{x=y} B²)`. -/
theorem lwExpTerm3_graph_pair_bound (P : PGraph (Fin 2)) {e : ℕ} (he : e ≤ 2) (hnW : 2 ≤ P.g.nW)
    (hord : (if P.ext 0 = P.ext 1 then (4 : ℤ) else 5) ≤ P.g.scalingOrder)
    {t N B η τ' : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η) (E : ℝ)
    (x y : Idx d (sz.L n) (sz.W n))
    (hI : ‖∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
      N ^ τ' * (t ^ P.g.nW * η⁻¹ * B ^ ((P.g.scalingOrder : ℝ) / 2))) :
    ‖∫ ω, P.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
      N ^ τ' * (t ^ e * η⁻¹ * (B ^ ((5 : ℝ) / 2) + if x = y then B ^ (2 : ℝ) else 0)) := by
  classical
  have hNτ : 0 ≤ N ^ τ' := Real.rpow_nonneg (by linarith) _
  have hη' : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
  have hte : t ^ P.g.nW ≤ t ^ e := pow_le_pow_of_le_one ht0.le ht1.le (by omega)
  have hB52 : 0 ≤ B ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hB2 : 0 ≤ B ^ (2 : ℝ) := Real.rpow_nonneg hB0.le _
  have hBo : 0 ≤ B ^ ((P.g.scalingOrder : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hte0 : 0 ≤ t ^ e := pow_nonneg ht0.le _
  by_cases hxy : x = y
  · subst hxy
    simp only [ite_true]
    have hord4 : (4 : ℝ) ≤ (P.g.scalingOrder : ℝ) := by
      have : (4 : ℤ) ≤ P.g.scalingOrder := by
        refine le_trans ?_ hord
        split_ifs <;> norm_num
      exact_mod_cast this
    have hB4 : B ^ ((P.g.scalingOrder : ℝ) / 2) ≤ B ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hB0 hB1 (by linarith)
    refine hI.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hNτ
    calc t ^ P.g.nW * η⁻¹ * B ^ ((P.g.scalingOrder : ℝ) / 2) ≤ t ^ e * η⁻¹ * B ^ (2 : ℝ) := by
          gcongr
      _ ≤ t ^ e * η⁻¹ * (B ^ ((5 : ℝ) / 2) + B ^ (2 : ℝ)) := by
          have : 0 ≤ t ^ e * η⁻¹ := mul_nonneg hte0 hη'
          nlinarith
  · simp only [hxy, ite_false, add_zero]
    by_cases hext : P.ext 0 = P.ext 1
    · have h0 : ∀ ω, P.val (LWG5Data sz n E t ω) ![x, y] = 0 := fun ω => lwExpTerm3_val_ext_ne sz n P hext hxy _
      simp only [h0, integral_zero, norm_zero]
      positivity
    · have hord5 : (5 : ℝ) ≤ (P.g.scalingOrder : ℝ) := by
        have : (5 : ℤ) ≤ P.g.scalingOrder := by simpa [hext] using hord
        exact_mod_cast this
      have hB5 : B ^ ((P.g.scalingOrder : ℝ) / 2) ≤ B ^ ((5 : ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hB0 hB1 (by linarith)
      refine hI.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hNτ
      gcongr


/-- **`t > 0` case of target 4**: the bridge, `LWG5Expand` and target 3 give
`‖W^d Σ K S^{(B)} 𝔼 𝓛^{(5)}‖ ≤ Λ N^{τ'} η⁻¹ (B^{5/2} + W^{-d} B²)`, `Λ = #Ls`. -/
theorem lwExpTerm3_T4pos (Lk : List (ℕ × PGraph (Fin 2)))
    (hLk : ∀ q ∈ Lk, 2 ≤ q.2.g.nW ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder)
    {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1) (k s : Bool) (a b : Zd d (sz.L n))
    (hexp : ∀ x y : Idx d (sz.L n) (sz.W n),
      ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) =
        (Lk.map fun q => (mE E) ^ q.1 * ∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)).sum)
    {N B η τ' : ℝ} (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η)
    (hqb : ∀ q ∈ Lk, ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
        N ^ τ' * (t ^ q.2.g.nW * η⁻¹ * B ^ ((q.2.g.scalingOrder : ℝ) / 2))) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)‖ ≤
      (Lk.length : ℝ) * N ^ τ' * η⁻¹ * (B ^ ((5 : ℝ) / 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * B ^ (2 : ℝ)) := by
  classical
  set e : ℕ := if k then 1 else 2 with he
  have he2 : e ≤ 2 := by rw [he]; split_ifs <;> norm_num
  have hb := lwExpTerm3_bridge d sz n E t hE ht0 ht1 k s a b
  set X : ℂ := (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP) with hXdef
  set M : ℕ := (sz.W n) ^ d with hM
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hMpos : (0 : ℝ) < (M : ℝ) := by rw [hM]; push_cast; positivity
  have hMc : (((sz.W n : ℕ) : ℂ) ^ d) = (M : ℂ) := by rw [hM]; push_cast; rfl
  have hMr : (((sz.W n : ℕ) : ℝ) ^ d) = (M : ℝ) := by rw [hM]; push_cast; rfl
  have hte : (0 : ℝ) < t ^ e := pow_pos ht0 _
  have hb' : ((t : ℂ) ^ e) * X = ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP) := hb
  have hXeq : ‖X‖ = (t ^ e)⁻¹ * ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ := by
    have h1 : ‖((t : ℂ) ^ e) * X‖ = t ^ e * ‖X‖ := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
    rw [hb'] at h1
    rw [h1]
    field_simp
  rw [hXeq]
  -- the pair sum
  set Gq : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℝ := fun x y =>
    N ^ τ' * (t ^ e * η⁻¹ * (B ^ ((5 : ℝ) / 2) + if x = y then B ^ (2 : ℝ) else 0)) with hGq
  have hpair : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤ (Lk.length : ℝ) * Gq x y := by
    intro x y
    rw [hexp]
    refine lwExpTerm3_list_norm_sum_le Lk _ _ (fun q hq => ?_)
    obtain ⟨hnW, hord⟩ := hLk q hq
    rw [norm_mul, norm_pow, norm_mE hE.le, one_pow, one_mul]
    exact lwExpTerm3_graph_pair_bound sz n q.2 he2 hnW hord ht0 ht1 hN hB0 hB1 hη0 E x y (hqb q hq x y)
  have hG₂ : 0 ≤ (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ))) := by
    have : 0 ≤ N ^ τ' := Real.rpow_nonneg (by linarith) _
    have : 0 ≤ η⁻¹ := inv_nonneg.2 hη0.le
    positivity
  have hcardA : (Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a)).card = M := by
    have h := card_Iblk d (sz.L n) (sz.W n) a
    exact h
  have hcardB : (Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b)).card = M := by
    have h := card_Iblk d (sz.L n) (sz.W n) b
    exact h
  have hsum := lwExpTerm3_pairsum (Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a))
    (Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b)) hcardA hcardB
    (fun x y => ‖∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖)
    (G₁ := (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2))))
    (G₂ := (Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ)))) hG₂
    (fun x y => by
      refine (hpair x y).trans (le_of_eq ?_)
      simp only [hGq]
      split_ifs <;> ring)
  have hnorm : ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖ ≤
      ((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) ^ 2 * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2)))) +
        M * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ))))) := by
    rw [norm_mul, hMc, norm_inv, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ hsum
    refine Finset.sum_le_sum fun x _ => ?_
    exact norm_sum_le _ _
  calc (t ^ e)⁻¹ * ‖((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
      ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
        ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
          ∫ ω, (LWG5Graph k s).val (LWG5Data sz n E t ω) ![x, y] ∂(sz.seqP)‖
      ≤ (t ^ e)⁻¹ * (((M : ℝ) ^ 2)⁻¹ * ((M : ℝ) ^ 2 * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ ((5 : ℝ) / 2)))) +
        M * ((Lk.length : ℝ) * (N ^ τ' * (t ^ e * η⁻¹ * B ^ (2 : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 hte.le)
    _ = _ := by
        rw [hMr]
        field_simp

end T4pos

section T4zero

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- **`t = 0` case of target 4**: `G_0 = m I`, so the 5-loop is `m⁴ m^{(s)} W^{-4d} 1[a₂ = a₁ = a₃ = b = a]`
and `‖W^d Σ K S^{(B)} 𝔼 𝓛^{(5)}‖ ≤ W^{-3d}` (`K = S^{(B)}`; for `K = K⁺` the kernel is `0`). -/
theorem lwExpTerm3_T4zero {E t : ℝ} (hE : |E| < 2) (ht : t = 0) (k s : Bool) (a b : Zd d (sz.L n)) :
    ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)‖ ≤
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 := by
  classical
  subst ht
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  cases k
  · simp only [Bool.false_eq_true, ite_false]
    simp_rw [lwExpTerm3_Lloop5_zero sz n hE s]
    simp only [integral_const, probReal_univ, one_smul]
    set c₀ : ℂ := (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ with hc₀
    have hsum : ∑ a₁, ∑ a₂, ∑ a₃, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        (if a₂ = a ∧ a₁ = a ∧ a₃ = a ∧ b = a then (mE E) ^ 4 * mSigma E s * c₀ ^ 4 else 0) =
        if b = a then (SB d (sz.L n) (sz.lam n) a a : ℂ) * (SB d (sz.L n) (sz.lam n) a a : ℂ) *
          ((mE E) ^ 4 * mSigma E s * c₀ ^ 4) else 0 := by
      by_cases hb : b = a
      · simp only [hb, and_true, ite_true]
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single a]
          · rw [Finset.sum_eq_single a]
            · simp
            · intro a₃ _ h; simp [h]
            · intro h; exact absurd (Finset.mem_univ _) h
          · intro a₂ _ h; simp [h]
          · intro h; exact absurd (Finset.mem_univ _) h
        · intro a₁ _ h; simp [h]
        · intro h; exact absurd (Finset.mem_univ _) h
      · simp [hb]
    rw [hsum]
    have hSB : ‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖ ≤ 1 := by
      have := lwExpTerm3_sbR_le_one sz n (sz.lam n) (0 : Zd d (sz.L n))
      have e : (SB d (sz.L n) (sz.lam n) a a : ℂ) = (sbKernelR d (sz.L n) (sz.lam n) 0 : ℂ) := by
        simp [SB_apply, sbKernel_eq_ofReal]
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sbKernelR_nonneg d (sz.L n) (sz.lam n) 0)]
      exact this
    by_cases hb : b = a
    · simp only [hb, ite_true]
      have h : ‖(((sz.W n : ℕ) : ℂ) ^ d) * ((SB d (sz.L n) (sz.lam n) a a : ℂ) * (SB d (sz.L n) (sz.lam n) a a : ℂ) *
          ((mE E) ^ 4 * mSigma E s * c₀ ^ 4))‖ =
          ((sz.W n : ℕ) : ℝ) ^ d * (‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖ * ‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖) *
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4 := by
        simp only [norm_mul, norm_pow, Complex.norm_natCast, norm_inv, hc₀, norm_mE hE.le, norm_mSigma hE.le,
          one_pow, mul_one]
        ring
      rw [h]
      have h1 : ‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖ * ‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖ ≤ 1 := by
        nlinarith [norm_nonneg (SB d (sz.L n) (sz.lam n) a a : ℂ)]
      have e : ((sz.W n : ℕ) : ℝ) ^ d * 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4 =
          ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 := by field_simp
      calc ((sz.W n : ℕ) : ℝ) ^ d * (‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖ * ‖(SB d (sz.L n) (sz.lam n) a a : ℂ)‖) *
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4
          ≤ ((sz.W n : ℕ) : ℝ) ^ d * 1 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 4 := by gcongr
        _ = _ := e
    · simp only [hb, ite_false, mul_zero, norm_zero]
      positivity
  · simp only [ite_true]
    have : ∀ a₁ a₂ : Zd d (sz.L n), sz.LWExpKp n E 0 a₁ a₂ = 0 := fun a₁ a₂ => by simp [LWExpKp]
    simp [this]

end T4zero

/-- **Target 4 (assembly)**: the expansion pin gives `LWExpG5'` (both branches, both charges). -/
def LwExpG5'OfExpand (d : ℕ) : Prop := LWG5Expand d → LWExpG5' d

theorem lwExpG5'_of_expand (d : ℕ) : LwExpG5'OfExpand d := by
  intro hexp hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  classical
  obtain ⟨Ls, hLs, hLexp⟩ := hexp
  obtain ⟨hA, -, ht1, hRange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hz htz
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hA
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩
  have hB1 := st5_Bctl_le_one sz hκ hε hz htz
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  have hτ2 : 0 < τ / 2 := by positivity
  have hq : ∀ k s : Bool, ∀ q ∈ Ls k s, ∀ᶠ n in atTop, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
          (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := by
    intro k s q hq
    obtain ⟨hn, hm, -, ha, he, -⟩ := hLs k s q hq
    have := lwGraphPrec1 d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLmax q.2 hn hm ha he
    exact (st6_prec_det_iff sz hsz _ _).1 this (τ / 2) hτ2
  have hq' : ∀ᶠ n in atTop, ∀ k s : Bool, ∀ q ∈ Ls k s, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
          (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := by
    have h1 : ∀ k s : Bool, ∀ᶠ n in atTop, ∀ q ∈ Ls k s, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        ‖∫ ω, q.2.val (LWG5Data sz n (STflowE z n) (t n) ω) ![v.1, v.2] ∂(sz.seqP)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((t n) ^ q.2.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
            (sz.Bctl n (t n)) ^ ((q.2.g.scalingOrder : ℝ) / 2)) := fun k s =>
      (Filter.eventually_all_finite (List.finite_toSet (Ls k s))).2 (hq k s)
    exact Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun s => h1 k s
  set Λ : ℝ := (((Ls false false).length + (Ls false true).length + (Ls true false).length +
    (Ls true true).length : ℕ) : ℝ) with hΛ
  have hΛk : ∀ k s : Bool, ((Ls k s).length : ℝ) ≤ Λ := by
    intro k s
    rw [hΛ]
    have : (Ls k s).length ≤ (Ls false false).length + (Ls false true).length + (Ls true false).length +
        (Ls true true).length := by
      cases k <;> cases s <;> omega
    exact_mod_cast this
  have hΛ0 : 0 ≤ Λ := Nat.cast_nonneg _
  have hev1 : ∀ᶠ n in atTop, Λ * (2 + (𝔡⁻¹) ^ 2) + ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
  filter_upwards [hq', hlam, hB1, hev1] with n hqn hlamn hBn hev1n
  rintro ⟨⟨⟨k, s⟩, av⟩, hg⟩
  show ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n (STflowE z n) (t n) a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, s] ![a₂, a₁, a₃, av 1, av 0] ω ∂(sz.seqP)‖ ≤
    ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
  have hB1' : sz.Bctl n (t n) ≤ 1 := hBn (t n) le_rfl
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE2 n) (ht1 n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwExpTerm3_etaT_le_one (hE2 n) (ht0 n) (ht1 n)
  have hη' : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hBge := STBctl_ge sz n (ht0 n) (ht1 n)
  have hl2 : sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
    have := pow_le_pow_left₀ hlamn.1.le hlamn.2 2
    linarith
  have hl0 : 0 < sz.lam n ^ 2 + 1 := by positivity
  have hWinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n) := by
    have h1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n (t n) := by
      have := mul_le_mul_of_nonneg_left hBge hl0.le
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (sz.lam n ^ 2 + 1) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + 1)⁻¹) := by
            field_simp
        _ ≤ _ := this
    exact h1.trans (mul_le_mul_of_nonneg_right hl2 hB0.le)
  have hB52 : 0 ≤ sz.Bctl n (t n) ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hB0.le _
  have hNτ2 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.one_le_rpow hN1 hτ2.le
  have hNτ : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  by_cases ht : t n = 0
  · -- `t = 0`
    refine (lwExpTerm3_T4zero sz n (hE2 n) ht k s (av 0) (av 1)).trans ?_
    have hw1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hWd1
    have hw0 : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_pos.2 hWd
    have h3 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 ≤ ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((5 : ℝ) / 2) := by
      rw [show ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 = ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((3 : ℕ) : ℝ) from
        (Real.rpow_natCast _ 3).symm]
      exact Real.rpow_le_rpow_of_exponent_ge hw0 hw1 (by norm_num)
    have h4 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ ((5 : ℝ) / 2) ≤
        (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n)) ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow hw0.le hWinv (by norm_num)
    have h5 : (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n)) ^ ((5 : ℝ) / 2) =
        ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) :=
      Real.mul_rpow (by positivity) hB0.le
    have hC : ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
      have : 0 ≤ Λ * (2 + (𝔡⁻¹) ^ 2) := by positivity
      linarith
    calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 3 ≤ ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) :=
          h3.trans (h4.trans (le_of_eq h5))
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * sz.Bctl n (t n) ^ ((5 : ℝ) / 2) := by gcongr
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ * sz.Bctl n (t n) ^ ((5 : ℝ) / 2)) := by
          gcongr
          nlinarith
  · -- `t > 0`
    have hpos : 0 < t n := lt_of_le_of_ne (ht0 n) (Ne.symm ht)
    have hLk : ∀ q ∈ Ls k s, 2 ≤ q.2.g.nW ∧ (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder :=
      fun q hq => by
        obtain ⟨-, -, hnW, -, -, hord⟩ := hLs k s q hq
        exact ⟨hnW, hord⟩
    have hmain := lwExpTerm3_T4pos sz n (Ls k s) hLk (hE2 n) hpos (ht1 n) k s (av 0) (av 1)
      (fun x y => hLexp sz n (STflowE z n) (t n) (hE2 n) hpos (ht1 n) k s x y)
      (N := ((sz.size n : ℕ) : ℝ)) (B := sz.Bctl n (t n)) (η := etaT (STflowE z n) (t n)) (τ' := τ / 2) hN1 hB0 hB1' hη0
      (fun q hq x y => hqn k s q hq (x, y))
    refine hmain.trans ?_
    set Bc : ℝ := sz.Bctl n (t n) with hBc
    set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
    set η : ℝ := etaT (STflowE z n) (t n) with hη
    have hB3 : Bc * Bc ^ (2 : ℝ) ≤ Bc ^ ((5 : ℝ) / 2) := by
      have e : Bc * Bc ^ (2 : ℝ) = Bc ^ (3 : ℝ) := by
        rw [show (3 : ℝ) = 1 + 2 by norm_num, Real.rpow_add hB0, Real.rpow_one]
      rw [e]
      exact Real.rpow_le_rpow_of_exponent_ge hB0 hB1' (by norm_num)
    have hB2p : 0 ≤ Bc ^ (2 : ℝ) := Real.rpow_nonneg hB0.le _
    have hW2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ) ≤ ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2) := by
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ) ≤ (((𝔡⁻¹) ^ 2 + 1) * Bc) * Bc ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right hWinv hB2p
        _ = ((𝔡⁻¹) ^ 2 + 1) * (Bc * Bc ^ (2 : ℝ)) := by ring
        _ ≤ ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2) := by gcongr
    have hΛ' : ((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2) ≤ Nn ^ (τ / 2) := by
      have := hΛk k s
      have h1 : ((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2) ≤ Λ * (2 + (𝔡⁻¹) ^ 2) :=
        mul_le_mul_of_nonneg_right this (by positivity)
      have : 0 ≤ ((𝔡⁻¹) ^ 2 + 1) ^ ((5 : ℝ) / 2) := by positivity
      linarith
    have hη0' : 0 < η⁻¹ := inv_pos.2 hη0
    calc ((Ls k s).length : ℝ) * Nn ^ (τ / 2) * η⁻¹ * (Bc ^ ((5 : ℝ) / 2) + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (2 : ℝ))
        ≤ ((Ls k s).length : ℝ) * Nn ^ (τ / 2) * η⁻¹ * (Bc ^ ((5 : ℝ) / 2) + ((𝔡⁻¹) ^ 2 + 1) * Bc ^ ((5 : ℝ) / 2)) := by
          gcongr
      _ = (((Ls k s).length : ℝ) * (2 + (𝔡⁻¹) ^ 2)) * Nn ^ (τ / 2) * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by ring
      _ ≤ Nn ^ (τ / 2) * Nn ^ (τ / 2) * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by
          gcongr
      _ = Nn ^ τ * (η⁻¹ * Bc ^ ((5 : ℝ) / 2)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring



/-! ## 5. Target 5 (conditionals) and the compiled instances -/

def LwCutExpOfExpand (d : ℕ) : Prop :=
  LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5Expand d → LWCutExp d

def LwTermEXPOfExpand (d : ℕ) : Prop :=
  LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5Expand d → LWtermEXP d

theorem lwCutExp_of_expand (d : ℕ) : LwCutExpOfExpand d := fun h1 h23 h41 hx =>
  lwCutExp_of_terms d h1 h23 h41 (lwExpG5'_of_expand d hx)

theorem lwTermEXP_of_expand (d : ℕ) : LwTermEXPOfExpand d := fun h1 h23 h41 hx =>
  lwTermEXP_of_cut d (lwCutExp_of_expand d h1 h23 h41 hx)

/-- The explicit normal graph of the preflight instance: external `x = inl 0`, `y = inl 1`, internal `α = inr 0`;
solid `G_{xα}, G_{αy}, Ḡ_{xy}, (G-M)_{αα}` twice; waved `S_{αα}` twice; `×`-dotted `(x,α), (α,y), (x,y)`. -/
def lwExpTerm3_instGraph : LGraph (Fin 2) (Fin 1) where
  solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inl 1),
    SEdge.mk false false (Sum.inl 0) (Sum.inl 1), SEdge.mk true true (Sum.inr 0) (Sum.inr 0),
    SEdge.mk true true (Sum.inr 0) (Sum.inr 0)]
  waved := [WEdge.mk false true (Sum.inr 0) (Sum.inr 0), WEdge.mk false true (Sum.inr 0) (Sum.inr 0)]
  dotted := [DEdge.mk false (Sum.inl 0) (Sum.inr 0), DEdge.mk false (Sum.inr 0) (Sum.inl 1),
    DEdge.mk false (Sum.inl 0) (Sum.inl 1)]
  coeff := 1

example : lwExpTerm3_instGraph.Normal := by decide
example : lwExpTerm3_instGraph.nM = 1 := by decide
example : LWAttached lwExpTerm3_instGraph.pack := by
  unfold LWAttached
  decide


/-- The instance graph has exactly one internal molecule, is normal, and its internal molecule is attached. -/
theorem lwExpTerm3_instGraph_nM : lwExpTerm3_instGraph.nM = 1 := by decide

theorem lwExpTerm3_instGraph_normal : lwExpTerm3_instGraph.Normal := by decide

theorem lwExpTerm3_instGraph_attached : LWAttached lwExpTerm3_instGraph.pack := by
  unfold LWAttached
  decide

theorem lwExpTerm3_instGraph_ext :
    ∀ a b : (lwExpTerm3_instGraph.pack).E', (lwExpTerm3_instGraph.pack).g.molOf (Sum.inl a) =
      (lwExpTerm3_instGraph.pack).g.molOf (Sum.inl b) → a = b := by
  intro a b h
  rw [LGraph.molOf_eq_iff] at h
  revert a b
  decide

end RBM.Gauss.Sizes

namespace RBM.Gauss.LWInst

open RBM RBM.Loop RBM.Graph RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- **Instance of target 3** at `d = 3`, `sz0`, `z0`, `tInst`: the explicit normal graph with one internal molecule
(`lwExpTerm3_instGraph`: `n_M = 1`, `Normal` and `LWAttached` by `decide`); `STLocalEntry`, `STLmax` are other gates' pins. -/
theorem lwExpTerm3_inst_prec1 (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p _ => ‖∫ ω, (lwExpTerm3_instGraph.pack).val (LWG5Data sz0 n (STflowE z0 n) (tInst n) ω) ![p.1, p.2] ∂(sz0.seqP)‖)
      (fun n _ _ => (tInst n) ^ (lwExpTerm3_instGraph.pack).g.nW * (etaT (STflowE z0 n) (tInst n))⁻¹ *
        (sz0.Bctl n (tInst n)) ^ (((lwExpTerm3_instGraph.pack).g.scalingOrder : ℝ) / 2)) :=
  lwGraphPrec1 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst tInst_range.1 tInst_range.2 hLE hLmax (lwExpTerm3_instGraph.pack) lwExpTerm3_instGraph_normal
    (le_of_eq lwExpTerm3_instGraph_nM) lwExpTerm3_instGraph_attached lwExpTerm3_instGraph_ext


/-- The graph `lwExpTerm3_instGraph` has `ord = 7` (`n_S = 5`, `n_W = 2`, `n_V = 1`). -/
theorem lwExpTerm3_inst_graph_order : lwExpTerm3_instGraph.scalingOrder = 7 := by
  simp [LGraph.scalingOrder, LGraph.counters, ord, LGraph.nS, LGraph.nW, LGraph.nV, lwExpTerm3_instGraph]

/-- **Instance of target 2** (the bridge) at `d = 3`, `n = 0`, `E = STflowE z0 0`, `t = 1/16`, both kernels and
both charges, all blocks `(a, b)`: no hypothesis. -/
theorem lwExpTerm3_inst_bridge (k s : Bool) (a b : Zd 3 (sz0.L 0)) :
    ((1 / 16 : ℝ) : ℂ) ^ (if k then 1 else 2) * ((((sz0.W 0 : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz0 0 (STflowE z0 0) (1 / 16) a₁ a₂
          else (SB 3 (sz0.L 0) (sz0.lam 0) a₁ a₂ : ℂ)) *
        (SB 3 (sz0.L 0) (sz0.lam 0) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz0 0 (STflowE z0 0) (1 / 16) ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz0.seqP)) =
      ((((sz0.W 0 : ℕ) : ℂ) ^ 3) ^ 2)⁻¹ *
        ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl 3 (sz0.L 0) (sz0.W 0) x = a),
          ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl 3 (sz0.L 0) (sz0.W 0) y = b),
            ∫ ω, (LWG5Graph k s).val (LWG5Data sz0 0 (STflowE z0 0) (1 / 16) ω) ![x, y] ∂(sz0.seqP) :=
  lwExpTerm3_bridge 3 sz0 0 (STflowE z0 0) (1 / 16)
    (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0) (by norm_num) (by norm_num) k s a b

/-- **Instance of target 4**: `LWG5Expand 3` (LW-14e) gives `LWExpG5'` at the instance data. -/
theorem lwExpTerm3_inst_G5 (hx : LWG5Expand 3) (hLE : STLocalEntry sz0 (STflowE z0) tInst)
    (hLW : LWAvgLaw sz0 (STflowE z0) tInst) (hLmax : STLmax sz0 (STflowE z0) tInst)
    (hLK : STLK sz0 (STflowE z0) tInst) (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖(((sz0.W n : ℕ) : ℂ) ^ 3) * ∑ a₁, ∑ a₂, ∑ a₃,
          (if p.1.1.1 then LWExpKp sz0 n (STflowE z0 n) (tInst n) a₁ a₂
            else (SB 3 (sz0.L n) (sz0.lam n) a₁ a₂ : ℂ)) *
          (SB 3 (sz0.L n) (sz0.lam n) a₂ a₃ : ℂ) *
          ∫ ω, Lloop sz0 n (STflowE z0 n) (tInst n) ![true, true, true, true, p.1.1.2]
            ![a₂, a₁, a₃, p.1.2 1, p.1.2 0] ω ∂(sz0.seqP)‖)
      (fun n _ _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwExpG5'_of_expand 3 hx le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
    flow_z0 tInst tInst_range.1 tInst_range.2 hLE hLW hLmax hLK hDec

/-- **Instance of target 5**: `LWCutExp` from the four expansion pins (`LWExpI1K`, `LWExpI23K`, `LWExpI41K` of LW-14d,
`LWG5Expand` of LW-14e) at the instance data. -/
theorem lwExpTerm3_inst_cut (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (hx : LWG5Expand 3)
    (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst)
    (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst)
    (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Bool × Bool) × (Zd 3 (sz0.L n) × Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWcut sz0 n (STflowE z0 n) (tInst n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  lwCutExp_of_expand 3 h1 h23 h41 hx le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 hLE hLW hLmax hLK hDec

/-- **Instance of target 5** (`LWtermEXP`, into the merged `inst_LWtermEXP`). -/
theorem lwExpTerm3_inst_term (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (hx : LWG5Expand 3)
    (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst)
    (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst)
    (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  inst_LWtermEXP (lwTermEXP_of_expand 3 h1 h23 h41 hx) hLE hLW hLmax hLK hDec

end RBM.Gauss.LWInst
