/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWSymm
import RBM3D.Graph.BAAtomic
import RBM3D.Graph.BAExpandW
import RBM3D.BA.CouplingWindow

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# BA-L L3a1 (T2425): the twists of a BA graph

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:286-387` (cited `B:line`: the BA graph, atoms, normal graphs).  Design:
`docs/reports/T2395-design.md` §6 (row L3a1 `BASymm1`), probe `t/T2395:RBM3D/Probe/T2395Pins.lean:70-104, 233-238, 271-273`.  The BA twin of
`Graph/LWSymm.lean` §1-§3 (`:79-575`): conjugation and transposition, the flip of the imaginary parts, the twists in expectation.

## Contents (namespace `RBM.Graph`, private prefix `BASymm1_`)

1. **The twist** (probe 71-104, verbatim): `BAMEdge.twist`, `BAPsiEdge.twist`, `BAGraph.twist` (`lwSymmTwistG` on the underlying graph, the
   twist of the dotted edges), `BAGraph.twist_atomAdj`, `ba_twist_counters`; and `BAGraph.BASymm1_twist_atom` (the atoms are those of the
   untwisted graph).
2. **`BAtwistInv`** (probe 272, verbatim) **proved**: `baTwistInv_holds`.  The twist keeps normality, `nExt`, `nLoops`, `nPairs`
   (`BAGraph.BASymm1_nShare_ends`: `nShare` reads the ends of an edge up to order; `BAGraph.BASymm1_pairsAux_twist`).
3. **The value of a twist** `BAGraph.BASymm1_val_twist : (Γ.twist c t).val D ℓe = (conj if c) (Γ.val (D transposed if t) ℓe)` for data with
   real `S` and real `gPsi` (twin of `lwSymmTwistG_val`, `LWSymm.lean:274`; `BASymm1_dataTr`, `BASymm1_psiEdge_val`, `BASymm1_mEdge_val`,
   `BASymm1_term_twist_L`, `BAGraph.BASymm1_term_twist`).
4. **The data at the flipped sample** `BASymm1_dataTr_flip`: the transposed data is the data at `lwSymmFlipF ω` (`Ψ` symmetric, `M` symmetric
   `baM_symm`, `S` symmetric `svarF_comm`, `S⁺ = S (1 - M⁺S)⁻¹` symmetric by the push-through identity `BASymm1_pushThrough`, which needs
   neither `BASelf` nor `t < 1`; `BASymm1_data_real`, `BASymm1_Sp_symm`, `BASymm1_H_flip`).
5. **The flip** (`BASymm1_flipEquiv`): `BASymm1_flip_measurePreserving`, the one-size twin of `lwSymm_flip_measurePreserving`
   (`LWSymm.lean:441`), for `PF d L W g`.
6. **`BAtwistIntegral d`** (probe 234, verbatim) **proved**: `baTwistIntegral_holds`.
7. Compiled instances (`BASymm1Inst`) at `d = 3`, `L = 4`, `W = 2` and the flow point `flowP` of `BA/CouplingWindow.lean` (`BASelf` and
   `0 < t₀ < 1` are `flowP_data`).

`lwSymm_twist_integral` (`LWSymm.lean:558`) is not called: it is stated for `LGraph.val`, `lwSampleData` and `Sizes.seqP`; the BA value has the
`Ψ`- and `M`-dotted factors and the law is `PF d L W 0` (T2425 preflight (a)).  Its ingredients are reused (`lwSymm_term_conj`,
`lwSymm_term_transpose`, `lwSymm_Xmat_flip`, `lwSymm_Gres_transpose`, `lwSymm_integral_cj`).  The proof of `baTwistIntegral_holds` uses neither
`BASelf`, nor `0 ≤ t < 1`, nor any smallness of `g₀` (C1).
-/

open private BAExpandW_PsiI_transpose from RBM3D.Graph.BAExpandW

noncomputable section

open MeasureTheory ProbabilityTheory
namespace RBM.Graph
open RBM RBM.Gauss RBM.Green

/-! ## 1. The twist of a BA graph (probe 71-104, verbatim) -/

section Twist

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- twist of an `M`-dotted edge: conjugation flips its colour, transposition swaps its ends (`M` is symmetric: `baM_symm`). -/
def BAMEdge.twist (c t : Bool) {V : Type*} (e : BAMEdge V) : BAMEdge V :=
  ⟨if c then !e.σ else e.σ, if t then e.y else e.x, if t then e.x else e.y⟩
/-- twist of a `Ψ`-dotted edge (`Ψ` is real and symmetric). -/
def BAPsiEdge.twist (t : Bool) {V : Type*} (e : BAPsiEdge V) : BAPsiEdge V := ⟨if t then e.y else e.x, if t then e.x else e.y⟩
/-- **the twist `(c, t)` of a BA graph** (L3a1): `lwSymmTwistG` on the underlying graph and the twist of the dotted edges. -/
def BAGraph.twist (c t : Bool) (Γ : BAGraph E I) : BAGraph E I :=
  { toLGraph := lwSymmTwistG c t Γ.toLGraph, psi := Γ.psi.map (BAPsiEdge.twist t), mdot := Γ.mdot.map (BAMEdge.twist c t) }
theorem BAGraph.twist_atomAdj (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).atomAdj = Γ.atomAdj := by
  funext u v
  have hp : ∀ e : BAPsiEdge (E ⊕ I), decide (((BAPsiEdge.twist t e).x = u ∧ (BAPsiEdge.twist t e).y = v) ∨
      ((BAPsiEdge.twist t e).x = v ∧ (BAPsiEdge.twist t e).y = u)) = decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    intro e; rw [decide_eq_decide]; cases t <;> simp [BAPsiEdge.twist] <;> tauto
  have hm : ∀ e : BAMEdge (E ⊕ I), decide (((BAMEdge.twist c t e).x = u ∧ (BAMEdge.twist c t e).y = v) ∨
      ((BAMEdge.twist c t e).x = v ∧ (BAMEdge.twist c t e).y = u)) = decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    intro e; rw [decide_eq_decide]; cases t <;> cases c <;> simp [BAMEdge.twist] <;> tauto
  simp only [BAGraph.atomAdj, BAGraph.twist, lwSymmTwistG_dotted, List.any_map, Function.comp_def, hp, hm]
/-- **L3a1, structural half: the twist keeps the four counters** (atoms and molecules are those of the untwisted graph). -/
theorem ba_twist_counters (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).counters = Γ.counters := by
  have h1 := BAGraph.twist_atomAdj c t Γ
  have h2 : (Γ.twist c t).adj = Γ.adj := by
    funext u v
    simp only [BAGraph.adj]
    rw [show (Γ.twist c t).toLGraph = lwSymmTwistG c t Γ.toLGraph from rfl, lwSymmTwistG_adj, h1]
  have hs : (Γ.twist c t).atomStep = Γ.atomStep := by funext s; simp only [BAGraph.atomStep, h1]
  have hs' : (Γ.twist c t).step = Γ.step := by funext s; simp only [BAGraph.step, h2]
  have hA : (Γ.twist c t).atom = Γ.atom := by funext v; simp only [BAGraph.atom, hs]
  have hM : (Γ.twist c t).mol = Γ.mol := by funext v; simp only [BAGraph.mol, hs']
  have hnA : (Γ.twist c t).nA = Γ.nA := by simp only [BAGraph.nA, hA]
  have hnM : (Γ.twist c t).nM = Γ.nM := by simp only [BAGraph.nM, hM]
  obtain ⟨h3, h4, -, -⟩ := lwSymmTwistG_counters c t Γ.toLGraph
  have hS : (Γ.twist c t).nS = Γ.nS := h3
  have hW : (Γ.twist c t).nW = Γ.nW := h4
  simp only [BAGraph.counters, hS, hW, hnA, hnM]

/-- **The atoms of a twist are those of the untwisted graph** (the twist keeps the three kinds of dotted-edge adjacency). -/
theorem BAGraph.BASymm1_twist_atom (c t : Bool) (Γ : BAGraph E I) : (Γ.twist c t).atom = Γ.atom := by
  have h1 := BAGraph.twist_atomAdj c t Γ
  have hs : (Γ.twist c t).atomStep = Γ.atomStep := by funext s; simp only [BAGraph.atomStep, h1]
  funext v; simp only [BAGraph.atom, hs]

theorem BAGraph.BASymm1_twist_sameAtom (c t : Bool) (Γ : BAGraph E I) (u v : E ⊕ I) :
    (Γ.twist c t).sameAtom u v = Γ.sameAtom u v := by
  simp only [BAGraph.sameAtom, BAGraph.BASymm1_twist_atom]

theorem BAGraph.BASymm1_twist_intAtom (c t : Bool) (Γ : BAGraph E I) (v : E ⊕ I) :
    (Γ.twist c t).intAtom v = Γ.intAtom v := by
  simp only [BAGraph.intAtom, BAGraph.BASymm1_twist_atom]

/-- The ends of a twisted solid edge are those of the edge, in the same or in the opposite order. -/
theorem BASymm1_twistS_ends (c t : Bool) {V : Type*} (e : SEdge V) :
    ((lwSymmTwistS c t e).src = e.src ∧ (lwSymmTwistS c t e).dst = e.dst) ∨
      ((lwSymmTwistS c t e).src = e.dst ∧ (lwSymmTwistS c t e).dst = e.src) := by
  cases c <;> cases t <;> simp [lwSymmTwistS, SEdge.conj, SEdge.transpose]

/-- `nShare` reads the two ends of each edge up to order. -/
theorem BAGraph.BASymm1_nShare_ends (Γ : BAGraph E I) {e₁ e₂ e₁' e₂' : SEdge (E ⊕ I)}
    (h : (e₁.src = e₂.src ∧ e₁.dst = e₂.dst) ∨ (e₁.src = e₂.dst ∧ e₁.dst = e₂.src))
    (h' : (e₁'.src = e₂'.src ∧ e₁'.dst = e₂'.dst) ∨ (e₁'.src = e₂'.dst ∧ e₁'.dst = e₂'.src)) :
    Γ.nShare e₁ e₁' = Γ.nShare e₂ e₂' := by
  have hP : [e₁.src, e₁.dst].Perm [e₂.src, e₂.dst] := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact List.Perm.swap _ _ _
  have hP' : [e₁'.src, e₁'.dst].Perm [e₂'.src, e₂'.dst] := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact List.Perm.swap _ _ _
  have hc : Γ.sameAtom e₁.src e₁.dst = Γ.sameAtom e₂.src e₂.dst := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, BAGraph.BAAtomic_sameAtom_comm]
  have hc' : Γ.sameAtom e₁'.src e₁'.dst = Γ.sameAtom e₂'.src e₂'.dst := by
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, BAGraph.BAAtomic_sameAtom_comm]
  have hl : ∀ u : E ⊕ I, ([e₁'.src, e₁'.dst].filter fun w => Γ.sameAtom u w = true ∧ Γ.intAtom u = true).length =
      ([e₂'.src, e₂'.dst].filter fun w => Γ.sameAtom u w = true ∧ Γ.intAtom u = true).length :=
    fun u => (hP'.filter _).length_eq
  unfold BAGraph.nShare
  rw [hc, hc']
  split_ifs
  · rfl
  · simp only [hl]
    exact (hP.map _).sum_eq

theorem BAGraph.BASymm1_twist_nShare (c t : Bool) (Γ : BAGraph E I) (e e' : SEdge (E ⊕ I)) :
    (Γ.twist c t).nShare e e' = Γ.nShare e e' := by
  simp only [BAGraph.nShare, BAGraph.BASymm1_twist_sameAtom, BAGraph.BASymm1_twist_intAtom]

theorem BAGraph.BASymm1_pairsAux_twist (c t : Bool) (Γ : BAGraph E I) (es : List (SEdge (E ⊕ I))) :
    (Γ.twist c t).pairsAux (es.map (lwSymmTwistS c t)) = Γ.pairsAux es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons, BAGraph.pairsAux, ih]
    congr 1
    rw [List.map_map]
    congr 1
    exact List.map_congr_left fun e' _ => by
      simp only [Function.comp_apply]
      rw [BAGraph.BASymm1_twist_nShare]
      exact Γ.BASymm1_nShare_ends (BASymm1_twistS_ends c t e) (BASymm1_twistS_ends c t e')

/-- **L3a1, twist invariance** (probe 272, verbatim): the twist keeps normality, the external atoms, the atom-level loops and pairs
(counters: `ba_twist_counters`). -/
def BAtwistInv : Prop := ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (c t : Bool) (Γ : BAGraph E I),
  (Γ.Normal → (Γ.twist c t).Normal) ∧ (Γ.twist c t).nExt = Γ.nExt ∧ (Γ.twist c t).nLoops = Γ.nLoops ∧ (Γ.twist c t).nPairs = Γ.nPairs

/-- **`BAtwistInv` holds** (L3a1). -/
theorem baTwistInv_holds : BAtwistInv := by
  intro E I _ _ _ _ c t Γ
  refine ⟨fun hN => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro e he
    rw [show (Γ.twist c t).dotted = Γ.dotted from lwSymmTwistG_dotted c t Γ.toLGraph] at he
    exact hN.1 e he
  · intro e he
    rw [show (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) from lwSymmTwistG_solid c t Γ.toLGraph,
      List.mem_map] at he
    obtain ⟨e', he', rfl⟩ := he
    rw [lwSymmTwistS_circ]
    exact hN.2 e' he'
  · simp only [BAGraph.nExt, BAGraph.BASymm1_twist_atom]
  · have hs : (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) := lwSymmTwistG_solid c t Γ.toLGraph
    simp only [BAGraph.nLoops, hs, List.countP_map]
    refine List.countP_congr fun e _ => ?_
    simp only [Function.comp_apply, BAGraph.BASymm1_twist_sameAtom]
    rcases BASymm1_twistS_ends c t e with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, BAGraph.BAAtomic_sameAtom_comm]
  · have hs : (Γ.twist c t).solid = Γ.solid.map (lwSymmTwistS c t) := lwSymmTwistG_solid c t Γ.toLGraph
    simp only [BAGraph.nPairs, hs]
    exact BAGraph.BASymm1_pairsAux_twist c t Γ Γ.solid

end Twist

/-! ## 3. The value of a twist -/

section Value

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]

/-- The BA data of `D`, transposed if `t` (`G`, `M`, `S`, `S⁺` and `gPsi` all transposed). -/
def BASymm1_dataTr (D : BALData ι) (t : Bool) : BALData ι := cond t ⟨D.toLData.transpose, Matrix.transpose D.gPsi⟩ D

theorem BASymm1_dataTr_toLData (D : BALData ι) (t : Bool) : (BASymm1_dataTr D t).toLData = lwSymmDataTr D.toLData t := by
  cases t <;> rfl

/-- The factor of a twisted `Ψ`-dotted edge (`gPsi` real). -/
theorem BASymm1_psiEdge_val (D : BALData ι) (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool) (ℓ : V → ι)
    (e : BAPsiEdge V) :
    BAPsiEdge.val D ℓ (BAPsiEdge.twist t e) = lwSymmCj c (BAPsiEdge.val (BASymm1_dataTr D t) ℓ e) := by
  have hP' : ∀ i j, starRingEnd ℂ (D.gPsi i j) = D.gPsi i j := fun i j => hP i j
  cases c <;> cases t <;> simp [BAPsiEdge.val, BAPsiEdge.twist, BASymm1_dataTr, lwSymmCj, hP']

/-- The factor of a twisted `M`-dotted edge (no hypothesis: the colour flips with the conjugation, the ends swap with the transposition). -/
theorem BASymm1_mEdge_val (D : BALData ι) (c t : Bool) (ℓ : V → ι) (e : BAMEdge V) :
    BAMEdge.val D ℓ (BAMEdge.twist c t e) = lwSymmCj c (BAMEdge.val (BASymm1_dataTr D t) ℓ e) := by
  cases c <;> cases t <;> cases hσ : e.σ <;>
    simp [BAMEdge.val, BAMEdge.twist, BASymm1_dataTr, lwSymmCj, LData.transpose, hσ]

theorem BASymm1_term_twist_L {E I : Type*} [Fintype I] [DecidableEq I] (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j)
    (c t : Bool) (Γ : LGraph E I) (ℓ : E ⊕ I → ι) :
    (lwSymmTwistG c t Γ).term D ℓ = lwSymmCj c (Γ.term (lwSymmDataTr D t) ℓ) := by
  cases c <;> cases t
  · rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, lwSymm_term_transpose]
    rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, lwSymm_term_conj D hS]
    rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, lwSymm_term_conj D hS, lwSymm_term_transpose]
    rfl

private theorem BASymm1_prod_cj (c : Bool) {α : Type*} (l : List α) (f g : α → ℂ) (h : ∀ a ∈ l, f a = lwSymmCj c (g a)) :
    (l.map f).prod = lwSymmCj c ((l.map g).prod) := by
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left h

/-- **The term of a twist**: `(Γ.twist c t).term D ℓ = (conj if c) (Γ.term (D transposed if t) ℓ)`, for real `S` and real `gPsi`. -/
theorem BAGraph.BASymm1_term_twist {E I : Type} [Fintype I] [DecidableEq I] (D : BALData ι) (hS : ∀ i j, star (D.S i j) = D.S i j)
    (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool) (Γ : BAGraph E I) (ℓ : E ⊕ I → ι) :
    (Γ.twist c t).term D ℓ = lwSymmCj c (Γ.term (BASymm1_dataTr D t) ℓ) := by
  have h1 := BASymm1_term_twist_L D.toLData hS c t Γ.toLGraph ℓ
  have h2 : ((Γ.psi.map (BAPsiEdge.twist t)).map (BAPsiEdge.val D ℓ)).prod =
      lwSymmCj c ((Γ.psi.map (BAPsiEdge.val (BASymm1_dataTr D t) ℓ)).prod) := by
    rw [List.map_map]
    exact BASymm1_prod_cj c _ _ _ fun e _ => BASymm1_psiEdge_val D hP c t ℓ e
  have h3 : ((Γ.mdot.map (BAMEdge.twist c t)).map (BAMEdge.val D ℓ)).prod =
      lwSymmCj c ((Γ.mdot.map (BAMEdge.val (BASymm1_dataTr D t) ℓ)).prod) := by
    rw [List.map_map]
    exact BASymm1_prod_cj c _ _ _ fun e _ => BASymm1_mEdge_val D c t ℓ e
  simp only [BAGraph.term, BAGraph.twist]
  rw [BASymm1_dataTr_toLData, h1, h2, h3, map_mul, map_mul]

/-- **The value of a twist**: `(Γ.twist c t).val D = (conj if c) (Γ.val (D transposed if t))` (twin of `lwSymmTwistG_val`, `LWSymm.lean:274`). -/
theorem BAGraph.BASymm1_val_twist {E I : Type} [Fintype I] [DecidableEq I] (D : BALData ι)
    (hS : ∀ i j, star (D.S i j) = D.S i j) (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool) (Γ : BAGraph E I)
    (ℓe : E → ι) : (Γ.twist c t).val D ℓe = lwSymmCj c (Γ.val (BASymm1_dataTr D t) ℓe) := by
  simp only [BAGraph.val, BAGraph.BASymm1_term_twist D hS hP, map_sum]

end Value

/-! ## 4. The data at the flipped sample -/

section Data

/-- **Push-through**: `b (1 - a b)⁻¹ = (1 - b a)⁻¹ b` for `Ring.inverse` (the non-unit case: `1 - a b` is a unit iff `1 - b a` is). -/
theorem BASymm1_pushThrough {R : Type*} [Ring R] (a b : R) :
    b * Ring.inverse (1 - a * b) = Ring.inverse (1 - b * a) * b := by
  have hu : ∀ x y : R, IsUnit (1 - x * y) → IsUnit (1 - y * x) := by
    refine fun x y h => ⟨⟨1 - y * x, 1 + y * h.unit.inv * x, ?_, ?_⟩, rfl⟩
    · calc
        (1 - y * x) * (1 + y * (IsUnit.unit h).inv * x) = 1 - y * x + y * ((1 - x * y) * h.unit.inv) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, mul_one, sub_add_cancel]
    · calc
        (1 + y * (IsUnit.unit h).inv * x) * (1 - y * x) = 1 - y * x + y * (h.unit.inv * (1 - x * y)) * x := by noncomm_ring
        _ = 1 := by simp only [Units.inv_eq_val_inv, IsUnit.val_inv_mul, mul_one, sub_add_cancel]
  by_cases h : IsUnit (1 - a * b)
  · have h' : IsUnit (1 - b * a) := hu a b h
    calc b * Ring.inverse (1 - a * b)
        = Ring.inverse (1 - b * a) * ((1 - b * a) * (b * Ring.inverse (1 - a * b))) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ h', one_mul]
      _ = Ring.inverse (1 - b * a) * b := by
          have : (1 - b * a) * (b * Ring.inverse (1 - a * b)) = b * ((1 - a * b) * Ring.inverse (1 - a * b)) := by
            noncomm_ring
          rw [this, Ring.mul_inverse_cancel _ h, mul_one]
  · have h' : ¬ IsUnit (1 - b * a) := fun h'' => h (hu b a h'')
    rw [Ring.inverse_non_unit _ h, Ring.inverse_non_unit _ h']
    simp

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The BA data has real `S` and real `gPsi` (`g₀`, `t` real; `Ψ` Hermitian and symmetric, hence real). -/
theorem BASymm1_data_real (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) :
    (∀ a b, star ((BAlwData d L W g0 E t m ω).S a b) = (BAlwData d L W g0 E t m ω).S a b) ∧
      ∀ a b, star ((BAlwData d L W g0 E t m ω).gPsi a b) = (BAlwData d L W g0 E t m ω).gPsi a b := by
  constructor
  · intro a b
    simp [BAlwData, BAlwS]
  · intro a b
    have h := (PsiI_isHermitian d L W).apply b a
    have hs : PsiI d L W b a = PsiI d L W a b := congrFun (congrFun (BAExpandW_PsiI_transpose d L W) a) b
    simp only [BAlwData, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.star_def, h, hs]

/-- `S⁺ = S (1 - M⁺ S)⁻¹` is symmetric, `Sᵀ = S` and `M⁺ᵀ = M⁺` (no `BASelf`, no `t < 1`). -/
theorem BASymm1_Sp_symm (g0 E t : ℝ) (m : ℂ) :
    (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m).transpose = Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m := by
  have hS : (Matrix.of (BAlwS d L W t)).transpose = Matrix.of (BAlwS d L W t) := by
    ext i j
    simp [BAlwS, svarF_comm d L W 0 i j]
  have hMp : (BAlwMp d L W g0 E m).transpose = BAlwMp d L W g0 E m := by
    ext i j
    simp [BAlwMp, mul_comm]
  unfold BAlwW
  rw [Matrix.transpose_mul, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, hS, hMp]
  simp only [Matrix.nonsing_inv_eq_ringInverse]
  exact (BASymm1_pushThrough (BAlwMp d L W g0 E m) (Matrix.of (BAlwS d L W t))).symm

/-- `H_t` at the flipped sample is the transpose of `H_t`. -/
theorem BASymm1_H_flip (g0 t : ℝ) (ω : Ω d L W) :
    BAlwH d L W g0 t (lwSymmFlipF L W ω) = (BAlwH d L W g0 t ω).transpose := by
  simp only [BAlwH, Hflow, lwSymm_Xmat_flip, Matrix.transpose_add, Matrix.transpose_smul, BAExpandW_PsiI_transpose]

/-- **The BA data at the flipped sample is the transposed data** (`G(ω') = G(ω)ᵀ`; `M`, `S`, `S⁺`, `gPsi` symmetric). -/
theorem BASymm1_dataTr_flip (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) :
    BASymm1_dataTr (BAlwData d L W g0 E t m ω) true = BAlwData d L W g0 E t m (lwSymmFlipF L W ω) := by
  have hG : (Matrix.of fun x y => BAlwG d L W g0 E t m ω x y).transpose =
      Matrix.of fun x y => BAlwG d L W g0 E t m (lwSymmFlipF L W ω) x y := by
    have : (Matrix.of fun x y => BAlwG d L W g0 E t m (lwSymmFlipF L W ω) x y) =
        Gres (BAlwH d L W g0 t (lwSymmFlipF L W ω)) (ztOf m E t) true := rfl
    rw [this, BASymm1_H_flip, lwSymm_Gres_transpose]
    rfl
  have hM : (BAlwM d L W g0 E m).transpose = BAlwM d L W g0 E m := by
    ext i j
    exact (baM_symm (d := d) (L := L) (W := W) g0 E m j i)
  have hS : (Matrix.of (BAlwS d L W t)).transpose = Matrix.of (BAlwS d L W t) := by
    ext i j
    simp [BAlwS, svarF_comm d L W 0 i j]
  have hPsi : (((g0 : ℂ) • PsiI d L W)).transpose = (g0 : ℂ) • PsiI d L W := by
    rw [Matrix.transpose_smul, BAExpandW_PsiI_transpose]
  simp only [BASymm1_dataTr, BAlwData, LData.transpose, Bool.cond_true]
  rw [hG, hM, hS, hPsi, BASymm1_Sp_symm]

end Data

/-! ## 5. The law `PF d L W 0` is invariant under the flip of the imaginary parts -/

section Flip

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The flip as a measurable involution of the one-size sample space. -/
def BASymm1_flipEquiv : Ω d L W ≃ᵐ Ω d L W where
  toFun := lwSymmFlipF L W
  invFun := lwSymmFlipF L W
  left_inv := fun ω => by funext c; simp only [lwSymmFlipF, ← mul_assoc, lwSymmSgn_mul_self, one_mul]
  right_inv := fun ω => by funext c; simp only [lwSymmFlipF, ← mul_assoc, lwSymmSgn_mul_self, one_mul]
  measurable_toFun := Measurable.of_eval fun c => (measurable_pi_apply c).const_mul _
  measurable_invFun := Measurable.of_eval fun c => (measurable_pi_apply c).const_mul _

/-- **`PF d L W g` is invariant under the flip of the imaginary parts** (a product of centred Gaussians; one-size twin of
`lwSymm_flip_measurePreserving`, `LWSymm.lean:441`). -/
theorem BASymm1_flip_measurePreserving (g : ℝ) :
    MeasurePreserving (BASymm1_flipEquiv d L W) (PF d L W g) (PF d L W g) := by
  refine ⟨(BASymm1_flipEquiv d L W).measurable, ?_⟩
  have h : ∀ c : CoordF d L W, (gaussianReal 0 (gvarF d L W g c)).map (fun x => lwSymmSgn c.2.2 * x) =
      gaussianReal 0 (gvarF d L W g c) := by
    intro c
    have key : ∀ b : Bool, (gaussianReal 0 (gvarF d L W g c)).map (fun x => lwSymmSgn b * x) =
        gaussianReal 0 (gvarF d L W g c) := by
      intro b
      cases b
      · have : (fun x : ℝ => lwSymmSgn false * x) = fun x => -x := by
          funext x; simp [lwSymmSgn]
        rw [this, gaussianReal_map_neg]
        simp
      · have : (fun x : ℝ => lwSymmSgn true * x) = id := by
          funext x; simp [lwSymmSgn]
        rw [this, Measure.map_id]
    exact key _
  have hmap := Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (gvarF d L W g c))
    (f := fun c (x : ℝ) => lwSymmSgn c.2.2 * x) (fun c => measurable_const.mul measurable_id)
  simp only [h] at hmap
  exact hmap

end Flip

/-! ## 6. `BAtwistIntegral` -/

/-- **L3a1: the twist integral at the BA law** (probe 234, verbatim; `lwSymm_twist_integral`, `LWSymm.lean`); `Ψ` real, `M` symmetric
(`baM_symm`). -/
def BAtwistIntegral (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (c t' : Bool) (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      ∫ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        (if c then (star : ℂ → ℂ) else id) (∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- **`BAtwistIntegral d` holds** (L3a1), for every `d`: pathwise `(Γ.twist c t').val (D ω) = (conj if c) (Γ.val (D (flip^t' ω)))`, then the
flip invariance of `PF d L W 0`.  `BASelf` and `0 ≤ t < 1` are not used (C1: no smallness of `g₀`). -/
theorem baTwistIntegral_holds (d : ℕ) : BAtwistIntegral d := by
  intro L W _ _ _ g0 Em t m _ _ _ Ex Ix _ _ _ _ c t' Γ ℓe
  have h1 : ∀ ω, (Γ.twist c t').val (BAlwData d L W g0 Em t m ω) ℓe =
      lwSymmCj c (Γ.val (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') ℓe) := fun ω =>
    BAGraph.BASymm1_val_twist _ (BASymm1_data_real d L W g0 Em t m ω).1 (BASymm1_data_real d L W g0 Em t m ω).2 c t' Γ ℓe
  have h2 : ∫ ω, Γ.val (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') ℓe ∂(PF d L W 0) =
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
    cases t'
    · rfl
    · simp only [BASymm1_dataTr_flip]
      exact (BASymm1_flip_measurePreserving d L W 0).integral_comp' (fun ω => Γ.val (BAlwData d L W g0 Em t m ω) ℓe)
  simp only [h1]
  rw [lwSymm_integral_cj, h2]
  cases c <;> simp [lwSymmCj]

/-! ## 7. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point `flowP`) -/

namespace BASymm1Inst

/-- The graph of the instances: external `v0 = inl 0`, `v1 = inl 1`, internal `u = inr 0`, `w = inr 1`, `x = inr 2`.  Solid edges (all circled,
so the graph is normal): `G_{v0 u}`, `Ḡ_{w v1}` between atoms and `G_{v1 x}` inside the atom `{v1, x}`; waved edges: the coloured `S⁺_{v0 v1}` and the
black `S_{v0 u}`; the `×`-dotted edge `v0 v1`; the `M`-dotted edge `M_{u w}` (the internal atom `{u, w}`); the `Ψ`-dotted edge `Ψ_{v1 x}`; the
coefficient `1 + i/2`. -/
def G0 : BAGraph (Fin 2) (Fin 3) where
  solid := [⟨true, true, Sum.inl 0, Sum.inr 0⟩, ⟨false, true, Sum.inr 1, Sum.inl 1⟩, ⟨true, true, Sum.inl 1, Sum.inr 2⟩]
  waved := [⟨true, true, Sum.inl 0, Sum.inl 1⟩, ⟨false, true, Sum.inl 0, Sum.inr 0⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inl 1⟩]
  coeff := 1 + (1 / 2 : ℂ) * Complex.I
  psi := [⟨Sum.inl 1, Sum.inr 2⟩]
  mdot := [⟨true, Sum.inr 0, Sum.inr 1⟩]

theorem G0_normal : G0.Normal := ⟨by decide, by decide⟩

/-- the three atom-level counters of `G0`: two external atoms (`{v0}`, `{v1, x}`), one loop (`G_{v1 x}`), one pair (`G_{v0 u}`, `Ḡ_{w v1}` share
the internal atom `{u, w}`). -/
theorem G0_counts : G0.nExt = 2 ∧ G0.nLoops = 1 ∧ G0.nPairs = 1 := by decide

/-- the labels: the blocks `(0,0,0)` and `(1,0,0)` (adjacent), offset `0`. -/
def ℓ0 : Fin 2 → Idx 3 4 2 := fun a => (splitEquiv 3 4 2).symm (if a = 0 then (0, 0) else (Pi.single 0 1, 0))

/-- the twist `(true, true)` of `G0` is not `G0`: the `M`-dotted edge becomes red and its ends swap, the `Ψ`-dotted edge swaps its ends. -/
example : (G0.twist true true).mdot.map (fun e => (e.σ, e.x, e.y)) = [(false, Sum.inr 1, Sum.inr 0)] ∧
    (G0.twist true true).psi.map (fun e => (e.x, e.y)) = [(Sum.inr 2, Sum.inl 1)] := by
  constructor <;> rfl

/-- **Target 1** at `G0`: `twist_atomAdj` and `ba_twist_counters` at the twist `(true, true)`. -/
example : (G0.twist true true).atomAdj = G0.atomAdj ∧ (G0.twist true true).counters = G0.counters :=
  ⟨BAGraph.twist_atomAdj true true G0, ba_twist_counters true true G0⟩

/-- **Target 2** at `G0`: `BAtwistInv` at the twist `(true, true)` (normal, `nExt = 2`, `nLoops = 1`, `nPairs = 1`). -/
example : (G0.twist true true).Normal ∧ (G0.twist true true).nExt = 2 ∧ (G0.twist true true).nLoops = 1 ∧
    (G0.twist true true).nPairs = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := baTwistInv_holds true true G0
  obtain ⟨c1, c2, c3⟩ := G0_counts
  exact ⟨h1 G0_normal, h2.trans c1, h3.trans c2, h4.trans c3⟩

open RBM.BA.CouplingWindowInst in
/-- **Target 3** at `G0`, `d = 3`, `L = 4`, `W = 2` and the flow point `(t₀, E, m₀, g₀) = (t0P, EP, m0P, g0P)` of `(L, g) = (4, 10)` (`BASelf` and
`0 < t₀ < 1` are `flowP_data`): the twist integral, for each of the four twists. -/
example (c t' : Bool) :
    ∫ ω, (G0.twist c t').val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, G0.val (BAlwData 3 4 2 g0P EP t0P m0P ω) ℓ0 ∂(PF 3 4 2 0)) :=
  baTwistIntegral_holds 3 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 c t' G0 ℓ0

end BASymm1Inst

end RBM.Graph

end
