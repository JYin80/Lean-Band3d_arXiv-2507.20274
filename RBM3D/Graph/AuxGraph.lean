/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular2
import RBM3D.Graph.LWSizeClaim

/-!
# LW-11a: `GtoAG`, the deterministic part (T2170)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `def: BM2`,
`def_auxgraph`, `(eq:ordGaux)`, `GtoAG` and its proof (`7_8:857-958`), and `(scalemole)`
(`7_8:171-193`).  No port from RBM1D/RBM2D (they have no light-weight graph layer).

## Contents (namespace `RBM.Graph`; helpers carry the prefix `auxGraph_`)

1. **Vocabulary** (target 1): `LGraph.AuxIMol`, `LGraph.auxLab`, `LGraph.auxVal`, `LGraph.auxOrd`,
   `LGraph.auxVal_nonneg`, `auxGraph_auxLab_ext`.
2. **The order comparison** (target 2, `7_8:926`): `LGraph.scalingOrder_sub_auxOrd`,
   `LGraph.molSolid_length_le`, `LGraph.auxOrd_le_scalingOrder`.
3. **`GtoAG`, deterministic form** (target 3): `LWGtoAG`, `lwGtoAG_holds`.  Steps (a)-(g) of
   `7_8:914-928`: confinement (`auxGraph_mol_dist`, `auxGraph_lab_close`), the molecular forest with
   its roots (`auxGraph_exists_forest`), the pointwise bound on a confined labelling
   (`auxGraph_term_conf`), the sum over the children with the roots as external labels
   (`auxGraph_forest_roots`, a use of the merged `lwForest_sum_le`) and over the root blocks
   (`auxGraph_sum_blocks`), the powers of `Ψ` from the window, the tail on a non-confined
   labelling (`auxGraph_term_tail`, `auxGraph_tail_sum`, a use of the merged
   `LGraph.waved_sum_le` on the weighted kernels).
4. **`scalemole` for two external vertices in one molecule** (target 4): `LWScalemole`,
   `lwScalemole_holds`.
5. **The nested form of `Γ^aux`** (target 5): `LWAuxNested`, `lwAuxNested_holds`: the walks of
   `lem:localregular` (3)-(5) moved into an `NGraph` (`auxGraph_ngraph`).
6. Compiled instances (the last sections), at `d = 3`, `L = 4`, `W = 2`.

`hext` of `LWGtoAG` is not used by the proof (T2170 report, paper-delta candidate `T2170f`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. The vocabulary of the auxiliary graph (target 1) -/

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The internal molecules** (`def_poly`, `7_8:172`): the vertices `[α_i]`, `i ∈ ⟦q⟧`, of the auxiliary graph
(`def_auxgraph`, `7_8:896`); `q = n_M` (`LGraph.nM_eq_card`). -/
abbrev LGraph.AuxIMol (Γ : LGraph E I) : Type := {c : Γ.Mol // ¬ Γ.IsExtMol c}

open Classical in
/-- **The block of a molecule in the auxiliary graph** (`def: BM2`, `def_auxgraph`, `7_8:863-869`, `7_8:896`): for an
external molecule `c`, `be a` at the chosen external vertex `a` with `molOf (inl a) = c` (the convention `α_x ≡ x`,
`α_y ≡ y`); for an internal molecule, the block `b c` of its centre. -/
def LGraph.auxLab {κ : Type} (Γ : LGraph E I) (be : E → κ) (b : LGraph.AuxIMol Γ → κ) (c : Γ.Mol) : κ :=
  if h : Γ.IsExtMol c then be (Classical.choose h) else b ⟨c, h⟩

open Classical in
/-- **The value of the auxiliary graph** (`def_auxgraph`, `7_8:894-903`): every solid edge between
different molecules (`molSolid`, the molecular graph `𝒢_ℳ` of `def_poly`) is an edge `ξ([α_i], [α_j])` between the blocks
of its two molecules; the blocks of the internal molecules are summed over `κ` (`κ = Zd d L` for `def: BM2`), the
external ones are `be`. -/
def LGraph.auxVal {κ : Type} [Fintype κ] (Γ : LGraph E I) (ξ : κ → κ → ℝ) (be : E → κ) : ℝ :=
  haveI : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  ∑ b : LGraph.AuxIMol Γ → κ,
    (Γ.molSolid.map fun e => ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)).prod

/-- **`(eq:ordGaux)`** (`7_8:902`): `ord(𝒢^aux) = #solid edges - 2 #internal vertices`, the merged `ord` with
`n_W = 0`, `n_V = n_M` (the form of `NGraph.ordN`). -/
def LGraph.auxOrd (Γ : LGraph E I) : ℤ := ord ⟨Γ.molSolid.length, 0, Γ.nM, 0, 0, 0⟩

/-- The auxiliary graph has a non-negative value for non-negative edge variables. -/
theorem LGraph.auxVal_nonneg {κ : Type} [Fintype κ] (Γ : LGraph E I) (ξ : κ → κ → ℝ)
    (hξ : ∀ u v, 0 ≤ ξ u v) (be : E → κ) : 0 ≤ Γ.auxVal ξ be := by
  unfold LGraph.auxVal
  exact Finset.sum_nonneg fun b _ => List.prod_nonneg fun x hx => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
    exact hξ _ _

/-- If distinct external vertices lie in distinct molecules, the block of the molecule of `inl a` is `be a`. -/
theorem auxGraph_auxLab_ext {κ : Type} (Γ : LGraph E I)
    (hext : ∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b)
    (be : E → κ) (b : LGraph.AuxIMol Γ → κ) (a : E) :
    LGraph.auxLab Γ be b (Γ.molOf (Sum.inl a)) = be a := by
  classical
  have h : Γ.IsExtMol (Γ.molOf (Sum.inl a)) := ⟨a, rfl⟩
  unfold LGraph.auxLab
  rw [dif_pos h]
  congr 1
  exact hext _ _ (Classical.choose_spec h)

end Vocab

/-! ## 2. The order comparison (target 2, `7_8:926`) -/

section Order

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`(eq:ordG)` against `(eq:ordGaux)`**: `ord(Γ) - ord(Γ^aux) = (n_S - |𝒢_ℳ|) + 2 (n_W - n_V + n_M)`. -/
theorem LGraph.scalingOrder_sub_auxOrd (Γ : LGraph E I) :
    Γ.scalingOrder - Γ.auxOrd =
      ((Γ.nS : ℤ) - (Γ.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nV : ℤ) + (Γ.nM : ℤ)) := by
  simp only [LGraph.scalingOrder, LGraph.auxOrd, LGraph.counters, ord]
  ring

/-- `|𝒢_ℳ| ≤ n_S`: the molecular graph keeps a sub-list of the solid edges. -/
theorem LGraph.molSolid_length_le (Γ : LGraph E I) : Γ.molSolid.length ≤ Γ.nS := by
  unfold LGraph.molSolid LGraph.nS
  rw [List.length_map]
  exact List.length_filter_le _ _

/-- `ord(Γ^aux) ≤ ord(Γ)` for a normal graph (`(eq:MolVW)` summed over the molecules: `n_V - n_M ≤ n_W`). -/
theorem LGraph.auxOrd_le_scalingOrder (Γ : LGraph E I) (hN : Γ.Normal) : Γ.auxOrd ≤ Γ.scalingOrder := by
  have h1 := Γ.scalingOrder_sub_auxOrd
  have h2 := Γ.molSolid_length_le
  obtain ⟨h3, h4⟩ := Γ.counters_le hN.1
  omega

end Order

/-! ## 3. Confinement (`(yixi)`, `7_8:874-877`): the molecules are connected by waved edges -/

section Confine

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The block distance satisfies the triangle inequality (`zdistD_add_le`). -/
theorem auxGraph_bdist_triangle (x y z : Idx d L W) :
    lwBdist d L W x z ≤ lwBdist d L W x y + lwBdist d L W y z := by
  unfold lwBdist
  have h := zdistD_add_le d L ((split d L W x).1 - (split d L W y).1) ((split d L W y).1 - (split d L W z).1)
  rwa [sub_add_sub_cancel] at h

theorem auxGraph_bdist_self (x : Idx d L W) : lwBdist d L W x x = 0 := by
  simp [lwBdist]

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Two vertices adjacent in the molecular graph of a graph without `=`-dotted edges are the ends of a waved edge. -/
theorem auxGraph_adj_waved (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) {u v : E ⊕ I}
    (h : Γ.molGraph.Adj u v) :
    ∃ e ∈ Γ.waved, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u) := by
  have h1 := ((owx_molGraph_adj Γ u v).1 h).2
  unfold LGraph.adj at h1
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · rw [List.any_eq_true] at h1
    obtain ⟨e, he, hd⟩ := h1
    exact ⟨e, he, of_decide_eq_true hd⟩
  · rw [List.any_eq_true] at h1
    obtain ⟨e, he, hd⟩ := h1
    have := hD e he
    simp [this] at hd

/-- **Confinement**: if every waved edge joins labels at block distance `≤ r`, two vertices of one molecule have labels at block distance
`≤ |E ⊕ I| r` (a path of the molecular graph has fewer than `|E ⊕ I|` steps; triangle inequality). -/
theorem auxGraph_mol_dist (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) (ℓ : E ⊕ I → Idx d L W)
    {r : ℝ} (hr : 0 ≤ r) (hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ) ≤ r)
    {u v : E ⊕ I} (huv : Γ.molOf u = Γ.molOf v) :
    (lwBdist d L W (ℓ u) (ℓ v) : ℝ) ≤ (Fintype.card (E ⊕ I) : ℝ) * r := by
  have hreach : Γ.molGraph.Reachable u v := SimpleGraph.ConnectedComponent.eq.1 huv
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : p.length ≤ Fintype.card (E ⊕ I) := hp.length_lt.le
  have key : ∀ {a b : E ⊕ I} (q : Γ.molGraph.Walk a b),
      (lwBdist d L W (ℓ a) (ℓ b) : ℝ) ≤ (q.length : ℝ) * r := by
    intro a b q
    induction q with
    | nil => simp [auxGraph_bdist_self]
    | @cons a' c b' hadj q ih =>
      obtain ⟨e, he, h⟩ := auxGraph_adj_waved Γ hD hadj
      have h1 : (lwBdist d L W (ℓ a') (ℓ c) : ℝ) ≤ r := by
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← h1, ← h2]; exact hconf e he
        · rw [← h1, ← h2, lwBdist_comm]; exact hconf e he
      have h2 : (lwBdist d L W (ℓ a') (ℓ b') : ℝ) ≤ lwBdist d L W (ℓ a') (ℓ c) + lwBdist d L W (ℓ c) (ℓ b') := by
        exact_mod_cast auxGraph_bdist_triangle (ℓ a') (ℓ c) (ℓ b')
      rw [SimpleGraph.Walk.length_cons]
      push_cast
      nlinarith
  calc (lwBdist d L W (ℓ u) (ℓ v) : ℝ) ≤ (p.length : ℝ) * r := key p
    _ ≤ (Fintype.card (E ⊕ I) : ℝ) * r := by
        apply mul_le_mul_of_nonneg_right _ hr
        exact_mod_cast hlen

end Confine

/-! ## 4. Small list lemmas -/

section Lists

theorem auxGraph_list_prod_le {α : Type*} (l : List α) (f g : α → ℝ) (h0 : ∀ x ∈ l, 0 ≤ f x)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).prod ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hx0 := h0 x (List.mem_cons_self ..)
    have hx := h x (List.mem_cons_self ..)
    have hl0 : 0 ≤ (l.map f).prod := List.prod_nonneg fun y hy => by
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
      exact h0 z (List.mem_cons_of_mem _ hz)
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    exact mul_le_mul hx ih' hl0 (hx0.trans hx)

/-- A product over a list split along a filter: `Ψ` on the edges that fail `P`, `X e` on the others. -/
theorem auxGraph_prod_filter {α : Type*} (l : List α) (P : α → Bool) (Ψ : ℝ) (X : α → ℝ) :
    (l.map fun e => if P e = true then X e else Ψ).prod =
      ((l.filter P).map X).prod * Ψ ^ (l.length - (l.filter P).length) := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hle : (l.filter P).length ≤ l.length := List.length_filter_le _ _
    by_cases hx : P x = true
    · simp only [List.map_cons, List.prod_cons, hx, ite_true, List.filter_cons_of_pos, List.length_cons, ih]
      have : l.length + 1 - ((l.filter P).length + 1) = l.length - (l.filter P).length := by omega
      rw [this]; ring
    · have hx' : P x = false := by simpa using hx
      have hf : (x :: l).filter P = l.filter P := by simp [hx']
      simp only [List.map_cons, List.prod_cons, hx', Bool.false_eq_true, ite_false, hf, List.length_cons, ih]
      have : l.length + 1 - (l.filter P).length = (l.length - (l.filter P).length) + 1 := by omega
      rw [this, pow_succ]; ring

end Lists

/-! ## 5. The pointwise bound on a confined labelling (`7_8:914-921`) -/

section Pointwise

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem auxGraph_norm_list_prod (l : List ℂ) : ‖l.prod‖ = (l.map fun z => ‖z‖).prod := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem auxGraph_list_prod_le_pow (l : List ℝ) (Ψ : ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h : ∀ x ∈ l, x ≤ Ψ) :
    l.prod ≤ Ψ ^ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons, List.length_cons, pow_succ]
    have hx0 := h0 x (List.mem_cons_self ..)
    have hx := h x (List.mem_cons_self ..)
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun y hy => h0 y (List.mem_cons_of_mem _ hy)
    have ih' := ih (fun y hy => h0 y (List.mem_cons_of_mem _ hy)) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have : 0 ≤ Ψ := hx0.trans hx
    calc x * l.prod ≤ Ψ * Ψ ^ l.length := mul_le_mul hx ih' hl0 this
      _ = _ := by ring

/-- The norm of a solid edge factor is the norm of `G - (M)` at the labels of its ends. -/
theorem auxGraph_sedge_norm {ι V : Type*} (D : LData ι) (ℓ : V → ι) (e : SEdge V) :
    ‖SEdge.val D ℓ e‖ = ‖D.G (ℓ e.src) (ℓ e.dst) - if e.circ then D.M (ℓ e.src) (ℓ e.dst) else 0‖ := by
  unfold SEdge.val
  dsimp only
  cases e.σ
  · simp only [Bool.false_eq_true, ite_false]; exact norm_star _
  · simp

/-- A solid edge factor is `≤ Ψ` when the entry bound holds and a non-loop edge has distinct labels at its ends. -/
theorem auxGraph_sedge_le {ι V : Type*} [DecidableEq ι] (D : LData ι) {m : ℂ} {Ψ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (ℓ : V → ι) (e : SEdge V) (hloop : e.src = e.dst → e.circ = true)
    (hgood : e.src ≠ e.dst → ℓ e.src ≠ ℓ e.dst) : ‖SEdge.val D ℓ e‖ ≤ Ψ := by
  rw [auxGraph_sedge_norm]
  by_cases hs : e.src = e.dst
  · rw [hloop hs, hs]
    simp only [ite_true, hM, ite_true]
    exact hGd _
  · have hne := hgood hs
    have : D.M (ℓ e.src) (ℓ e.dst) = 0 := by simp [hM, hne]
    split_ifs <;> simp [this] <;> exact hG _ _ hne

/-- A solid edge between two different molecules, at a good labelling, is bounded by `ξ` of the blocks of its molecules. -/
theorem auxGraph_sedge_xi {ι V : Type*} [DecidableEq ι] (D : LData ι) {m : ℂ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (ℓ : V → ι) (e : SEdge V) (hne : ℓ e.src ≠ ℓ e.dst) :
    ‖SEdge.val D ℓ e‖ = ‖D.G (ℓ e.src) (ℓ e.dst)‖ := by
  rw [auxGraph_sedge_norm]
  have : D.M (ℓ e.src) (ℓ e.dst) = 0 := by simp [hM, hne]
  split_ifs <;> simp [this]

/-- Every vertex has its label within `R` (block distance) of the block of its molecule in the auxiliary graph
(`(yixi)` and the confinement). -/
theorem auxGraph_lab_close (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false)
    (ℓe : E → Idx d L W) (ℓi : I → Idx d L W) (root : LGraph.AuxIMol Γ → I)
    (hroot : ∀ c, Γ.molOf (Sum.inr (root c)) = c.1) {r R : ℝ} (hr : 0 ≤ r)
    (hR : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R)
    (hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r) (v : E ⊕ I) :
    (zdistD d L ((split d L W (Sum.elim ℓe ℓi v)).1 -
      LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1)
        (Γ.molOf v)) : ℝ) ≤ R := by
  classical
  unfold LGraph.auxLab
  by_cases h : Γ.IsExtMol (Γ.molOf v)
  · rw [dif_pos h]
    have h0 : Γ.molOf (Sum.inl (Classical.choose h)) = Γ.molOf v := Classical.choose_spec h
    have := auxGraph_mol_dist Γ hD (Sum.elim ℓe ℓi) hr hconf h0.symm
    exact this.trans hR
  · rw [dif_neg h]
    have h0 : Γ.molOf (Sum.inr (root ⟨Γ.molOf v, h⟩)) = Γ.molOf v := hroot ⟨Γ.molOf v, h⟩
    have := auxGraph_mol_dist Γ hD (Sum.elim ℓe ℓi) hr hconf h0.symm
    exact this.trans hR

/-- **The pointwise bound on a confined labelling** (`7_8:914-921`): the solid edges inside a molecule cost `Ψ`, the solid edges between two
molecules cost `ξ` of the blocks of the molecules (`hξ` and the confinement), the dotted edges `≤ 1`:
`|term ℓ| ≤ |coeff| Ψ^{n_S - |𝒢_ℳ|} ∏_{𝒢_ℳ} ξ ∏_{waved} |w_e(ℓ)|`, the blocks of the internal molecules being those of the roots. -/
theorem auxGraph_term_conf (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W)) {m : ℂ} {Ψ R r : ℝ}
    {ξ : Zd d L → Zd d L → ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hξ0 : ∀ a b, 0 ≤ ξ a b)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y → (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y‖ ≤ ξ a b)
    (hr : 0 ≤ r) (hR : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R)
    (ℓe : E → Idx d L W) (ℓi : I → Idx d L W) (root : LGraph.AuxIMol Γ → I)
    (hroot : ∀ c, Γ.molOf (Sum.inr (root c)) = c.1)
    (hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r) :
    ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
      ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) := by
  classical
  set ℓ : E ⊕ I → Idx d L W := Sum.elim ℓe ℓi with hℓ
  set Lab : Γ.Mol → Zd d L :=
    LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) with hLab
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hGd (fun _ => 0))
  set Pn : SEdge (E ⊕ I) → Bool := fun e => decide (¬ Γ.InsideMol e.src e.dst) with hPn
  have hms : Γ.molSolid = (Γ.solid.filter Pn).map (SEdge.map Γ.molOf) := rfl
  set X : SEdge (E ⊕ I) → ℝ := fun e => ξ (Lab (Γ.molOf e.src)) (Lab (Γ.molOf e.dst)) with hX
  have hmsmap : (Γ.molSolid.map fun e => ξ (Lab e.src) (Lab e.dst)) = (Γ.solid.filter Pn).map X := by
    rw [hms, List.map_map]; rfl
  have hmslen : Γ.molSolid.length = (Γ.solid.filter Pn).length := by rw [hms, List.length_map]
  have hwn : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg _
  have hxn : 0 ≤ ((Γ.solid.filter Pn).map X).prod :=
    List.prod_nonneg fun x hx => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
      exact hξ0 _ _
  rw [hmsmap, hmslen]
  have hnn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - (Γ.solid.filter Pn).length) *
      (((Γ.solid.filter Pn).map X).prod * (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod) := by positivity
  by_cases hgood : ∀ e ∈ Γ.solid, e.src ≠ e.dst → ℓ e.src ≠ ℓ e.dst
  · unfold LGraph.term
    rw [norm_mul, norm_mul, norm_mul, auxGraph_norm_list_prod, auxGraph_norm_list_prod, auxGraph_norm_list_prod]
    simp only [List.map_map]
    have hB : (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod ≤
        (Γ.solid.map fun e => if Pn e = true then X e else Ψ).prod := by
      refine auxGraph_list_prod_le _ _ _ (fun e he => norm_nonneg _) (fun e he => ?_)
      have hee := hN.2.2 e he
      by_cases hin : Γ.InsideMol e.src e.dst
      · have : Pn e = false := by simp [hPn, hin]
        simp only [this, Bool.false_eq_true, ite_false, Function.comp]
        exact auxGraph_sedge_le D hM hG hGd ℓ e hee (hgood e he)
      · have : Pn e = true := by simp [hPn, hin]
        simp only [this, ite_true, Function.comp]
        have hne : e.src ≠ e.dst := fun h => hin (by rw [h]; rfl)
        have hl := hgood e he hne
        rw [auxGraph_sedge_xi D hM ℓ e hl]
        refine hξ _ _ _ _ hl ?_ ?_
        · exact auxGraph_lab_close Γ hN.1 ℓe ℓi root hroot hr hR hconf e.src
        · exact auxGraph_lab_close Γ hN.1 ℓe ℓi root hroot hr hR hconf e.dst
    rw [auxGraph_prod_filter] at hB
    have h3 : (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod ≤ 1 := by
      have := auxGraph_list_prod_le_pow (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)) 1 (by
          intro x hx
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
          exact norm_nonneg _) (by
          intro x hx
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
          simp only [Function.comp, DEdge.val]
          split_ifs <;> simp)
      simpa using this
    have h0d : 0 ≤ (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have h0s : 0 ≤ (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod :=
      List.prod_nonneg fun x hx => by
        obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have hw' : (Γ.waved.map ((fun z : ℂ => ‖z‖) ∘ WEdge.val D ℓ)).prod =
        (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod := rfl
    rw [hw']
    have hlen : Γ.solid.length = Γ.nS := rfl
    rw [hlen] at hB
    calc ‖Γ.coeff‖ * (Γ.solid.map ((fun z : ℂ => ‖z‖) ∘ SEdge.val D ℓ)).prod *
          (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod *
          (Γ.dotted.map ((fun z : ℂ => ‖z‖) ∘ DEdge.val ℓ)).prod
        ≤ ‖Γ.coeff‖ * (((Γ.solid.filter Pn).map X).prod * Ψ ^ (Γ.nS - (Γ.solid.filter Pn).length)) *
          (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod * 1 := by gcongr
      _ = _ := by ring
  · push Not at hgood
    obtain ⟨e, he, hne, heq⟩ := hgood
    have hxb : Γ.XBetween e.src e.dst := (hN.2.1 e.src e.dst hne).2 ⟨e, he, hne, Or.inl ⟨rfl, rfl⟩⟩
    obtain ⟨e', he', hf, hxy⟩ := hxb
    have hz : DEdge.val ℓ e' = 0 := by
      have : ℓ e'.x = ℓ e'.y := by
        rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2]; exact heq
        · rw [h1, h2]; exact heq.symm
      simp [DEdge.val, this, hf]
    have : (Γ.dotted.map (DEdge.val ℓ)).prod = 0 :=
      List.prod_eq_zero (List.mem_map.2 ⟨e', he', hz⟩)
    have h0 : Γ.term D ℓ = 0 := by unfold LGraph.term; rw [this, mul_zero]
    rw [h0, norm_zero]
    exact hnn

end Pointwise

/-! ## 6. The molecular forest with its roots (`7_8:922-925`; the proof of `LGraph.exists_forest` with the root map) -/

section Forest

/-- A rank function toward a target set (`lwExists_rank` of `Graph/LWSizeClaim`, copied). -/
private theorem auxGraph_exists_rank {V : Type*} (G : SimpleGraph V) (T : V → Prop)
    (hT : ∀ v, ∃ t, T t ∧ G.Reachable v t) :
    ∃ rk : V → ℕ, ∀ v, ¬ T v → ∃ w, G.Adj v w ∧ rk w < rk v := by
  classical
  have hex : ∀ v, ∃ n, ∃ t, T t ∧ ∃ p : G.Walk v t, p.length = n := fun v => by
    obtain ⟨t, ht, ⟨p⟩⟩ := hT v
    exact ⟨p.length, t, ht, p, rfl⟩
  refine ⟨fun v => Nat.find (hex v), fun v hv => ?_⟩
  obtain ⟨t, ht, p, hp⟩ := Nat.find_spec (hex v)
  cases p with
  | nil => exact absurd ht hv
  | @cons _ w _ hadj p' =>
    refine ⟨w, hadj, ?_⟩
    have h1 : Nat.find (hex w) ≤ p'.length := Nat.find_min' (hex w) ⟨t, ht, p', rfl⟩
    rw [SimpleGraph.Walk.length_cons] at hp
    change Nat.find (hex w) < Nat.find (hex v)
    omega

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The molecular forest with its roots**: a graph without `=`-dotted edges has a root `root c` in every internal molecule `c` (one each,
distinct), and every other internal vertex `i` has a parent `par i` (an external vertex or an internal vertex of smaller rank) joined to it by
a waved edge `edge i`, the waved edges being pairwise distinct.  (`LGraph.exists_forest` of `Graph/LWSizeClaim` states the count only.) -/
theorem auxGraph_exists_forest (Γ : LGraph E I) (hD : ∀ e ∈ Γ.dotted, e.eq = false) :
    ∃ (root : LGraph.AuxIMol Γ → I) (par : I → E ⊕ I) (edge : {i : I // i ∉ Set.range root} → Fin Γ.waved.length)
      (ρ : I → ℕ),
      Function.Injective root ∧ (∀ c, Γ.molOf (Sum.inr (root c)) = c.1) ∧
      (∀ i : {i : I // i ∉ Set.range root}, ∀ w, par i.1 = Sum.inr w → ρ w < ρ i.1) ∧
      (∀ i : {i : I // i ∉ Set.range root},
        (((Γ.waved.get (edge i)).x = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).y = par i.1) ∨
         ((Γ.waved.get (edge i)).y = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).x = par i.1))) ∧
      Function.Injective edge := by
  classical
  let Mi := {c : Γ.Mol // ¬ Γ.IsExtMol c}
  have hMi : ∀ c : Mi, ∃ i : I, Γ.molOf (Sum.inr i) = c.1 := by
    rintro ⟨c, hc⟩
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    rcases v with a | i
    · exact absurd ⟨a, rfl⟩ hc
    · exact ⟨i, rfl⟩
  choose rootI hroot using hMi
  let T : E ⊕ I → Prop := fun v => v.isLeft = true ∨ ∃ m : Mi, v = Sum.inr (rootI m)
  have hreach : ∀ v, ∃ t, T t ∧ Γ.molGraph.Reachable v t := by
    intro v
    by_cases h : Γ.IsExtMol (Γ.molOf v)
    · obtain ⟨a, ha⟩ := h
      exact ⟨Sum.inl a, Or.inl rfl, SimpleGraph.ConnectedComponent.eq.1 ha.symm⟩
    · refine ⟨Sum.inr (rootI ⟨Γ.molOf v, h⟩), Or.inr ⟨_, rfl⟩, ?_⟩
      exact SimpleGraph.ConnectedComponent.eq.1 (hroot ⟨Γ.molOf v, h⟩).symm
  obtain ⟨rk, hrk⟩ := auxGraph_exists_rank Γ.molGraph T hreach
  have hex : ∀ c : I, ¬ T (Sum.inr c) → ∃ (w : E ⊕ I) (j : Fin Γ.waved.length),
      (((Γ.waved.get j).x = Sum.inr c ∧ (Γ.waved.get j).y = w) ∨
        ((Γ.waved.get j).y = Sum.inr c ∧ (Γ.waved.get j).x = w)) ∧ rk w < rk (Sum.inr c) := by
    intro c hc
    obtain ⟨w, hadj, hlt⟩ := hrk _ hc
    refine ⟨w, ?_⟩
    obtain ⟨e, he, h⟩ := auxGraph_adj_waved Γ hD hadj
    obtain ⟨j, rfl⟩ := List.mem_iff_get.1 he
    refine ⟨j, ?_, hlt⟩
    rcases h with h | h
    · exact Or.inl ⟨h.1, h.2⟩
    · exact Or.inr ⟨h.2, h.1⟩
  choose! par' edge' hpe using hex
  have hnT : ∀ i : I, i ∉ Set.range rootI → ¬ T (Sum.inr i) := by
    intro i hi hT
    rcases hT with hT | ⟨m, hm⟩
    · simp at hT
    · exact hi ⟨m, (Sum.inr_injective hm).symm⟩
  have hnT' : ∀ i : I, ¬ T (Sum.inr i) → i ∉ Set.range rootI := by
    intro i hi ⟨m, hm⟩
    exact hi (Or.inr ⟨m, by rw [hm]⟩)
  refine ⟨rootI, par', fun i => edge' i.1 (hnT i.1 i.2), fun i => rk (Sum.inr i), ?_, ?_, ?_, ?_, ?_⟩
  · intro m m' h
    apply Subtype.ext
    rw [← hroot m, ← hroot m', h]
  · exact hroot
  · intro i w hw
    have := (hpe i.1 (hnT i.1 i.2)).2
    rw [hw] at this
    exact this
  · intro i
    simpa using (hpe i.1 (hnT i.1 i.2)).1
  · intro i₁ i₂ h
    apply Subtype.ext
    by_contra hne
    obtain ⟨e1, r1⟩ := hpe i₁.1 (hnT i₁.1 i₁.2)
    obtain ⟨e2, r2⟩ := hpe i₂.1 (hnT i₂.1 i₂.2)
    have h' : edge' i₁.1 (hnT i₁.1 i₁.2) = edge' i₂.1 (hnT i₂.1 i₂.2) := h
    rw [h'] at e1
    rcases e1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases e2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · exact hne (Sum.inr_injective (a1.symm.trans a2))
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · rw [a1] at b2
      rw [b1] at a2
      rw [a2] at r1
      rw [← b2] at r2
      omega
    · exact hne (Sum.inr_injective (a1.symm.trans a2))

end Forest

/-! ## 7. The sum over the children for fixed roots, and the sum over the root blocks (`7_8:922-925`) -/

section ForestSum

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **The sum over the children with the roots as external labels** (`7_8:922-925`): for a forest whose children are all internal vertices outside
the range of the injective root map `root : Rt → I`, and any non-negative weight `Φ` of the root labels,
`Σ_ℓ Φ(ℓ ∘ root) ∏_j f_j ≤ (Σ_ρ Φ ρ) · K^{|I| - |Rt|} a^{|J| - (|I| - |Rt|)}`
(the peeling bound `lwForest_sum_le` with the roots moved to the external vertices). -/
theorem auxGraph_forest_roots {E I Rt J : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    [Fintype Rt] [DecidableEq Rt] [Fintype J] [DecidableEq J]
    (ℓe : E → ι) (u v : J → E ⊕ I) (f : J → ι → ι → ℝ) (a K : ℝ) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hf0 : ∀ j x y, 0 ≤ f j x y) (hfa : ∀ j x y, f j x y ≤ a)
    (hrow : ∀ j x, ∑ y, f j x y ≤ K) (hcol : ∀ j y, ∑ x, f j x y ≤ K)
    (root : Rt → I) (hroot : Function.Injective root) (par : I → E ⊕ I)
    (edge : {i : I // i ∉ Set.range root} → J) (ρ : I → ℕ) (hinj : Function.Injective edge)
    (hedge : ∀ i : {i : I // i ∉ Set.range root},
      (u (edge i) = Sum.inr i.1 ∧ v (edge i) = par i.1) ∨ (v (edge i) = Sum.inr i.1 ∧ u (edge i) = par i.1))
    (hrank : ∀ i : {i : I // i ∉ Set.range root}, ∀ w, par i.1 = Sum.inr w → ρ w < ρ i.1)
    (Φ : (Rt → ι) → ℝ) (hΦ : ∀ x, 0 ≤ Φ x) :
    ∑ ℓ : I → ι, Φ (fun t => ℓ (root t)) * ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)) ≤
      (∑ x : Rt → ι, Φ x) *
        (K ^ (Fintype.card I - Fintype.card Rt) * a ^ (Fintype.card J - (Fintype.card I - Fintype.card Rt))) := by
  classical
  let Cc := {i : I // i ∉ Set.range root}
  let eI : Rt ⊕ Cc ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective root hroot) (Equiv.refl Cc)).trans (Equiv.sumCompl (· ∈ Set.range root))
  have heIl : ∀ t, eI (Sum.inl t) = root t := fun t => rfl
  have heIr : ∀ c : Cc, eI (Sum.inr c) = c.1 := fun c => rfl
  let e1 : (I → ι) ≃ (Rt → ι) × (Cc → ι) :=
    (Equiv.arrowCongr eI.symm (Equiv.refl ι)).trans (Equiv.sumArrowEquivProdArrow Rt Cc ι)
  have hsymm : ∀ (x : Rt → ι) (y : Cc → ι) (i : I), e1.symm (x, y) i = Sum.elim x y (eI.symm i) := fun _ _ _ => rfl
  have hcardI : Fintype.card Rt + Fintype.card Cc = Fintype.card I := by
    rw [← Fintype.card_sum]; exact Fintype.card_congr eI
  have hcC : Fintype.card Cc = Fintype.card I - Fintype.card Rt := by omega
  -- the relabelling of the vertices
  let φ : E ⊕ I → (E ⊕ Rt) ⊕ Cc := fun x => match x with
    | Sum.inl a => Sum.inl (Sum.inl a)
    | Sum.inr i => Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i)
  have hφ : ∀ (x : Rt → ι) (y : Cc → ι) (z : E ⊕ I),
      Sum.elim (Sum.elim ℓe x) y (φ z) = Sum.elim ℓe (e1.symm (x, y)) z := by
    intro x y z
    rcases z with a | i
    · rfl
    · rw [Sum.elim_inr, hsymm]
      change Sum.elim (Sum.elim ℓe x) y (Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i)) = _
      rcases eI.symm i with m | c <;> rfl
  have hroots : ∀ (x : Rt → ι) (y : Cc → ι) (t : Rt), e1.symm (x, y) (root t) = x t := by
    intro x y t
    rw [hsymm]
    have : eI.symm (root t) = Sum.inl t := by rw [Equiv.symm_apply_eq]; rfl
    rw [this]; rfl
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  -- the bound for fixed roots
  have hfix : ∀ x : Rt → ι, ∑ y : Cc → ι,
      ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) ≤
        K ^ (Fintype.card I - Fintype.card Rt) * a ^ (Fintype.card J - (Fintype.card I - Fintype.card Rt)) := by
    intro x
    have hmain := lwForest_sum_le (ι := ι) (E := E ⊕ Rt) (I := Cc) (J := J) (Sum.elim ℓe x)
      (fun j => φ (u j)) (fun j => φ (v j)) f a K ha hK hf0 hfa hrow hcol (Finset.univ : Finset Cc)
      (fun c => φ (par c.1)) edge (fun c => ρ c.1)
      (fun c₁ _ c₂ _ h => hinj h)
      (fun c _ => by
        have hc : eI.symm c.1 = Sum.inr c := by rw [Equiv.symm_apply_eq]; rfl
        have hφc : φ (Sum.inr c.1) = Sum.inr c := by
          change Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm c.1) = _
          rw [hc]; rfl
        rcases hedge c with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [h1, hφc], by rw [h2]⟩
        · exact Or.inr ⟨by rw [h1, hφc], by rw [h2]⟩)
      (fun c _ w hw => by
        rcases hpc : par c.1 with a' | i
        · rw [hpc] at hw
          exact absurd hw (by simp [φ])
        · rw [hpc] at hw
          change Sum.elim (fun m => Sum.inl (Sum.inr m)) Sum.inr (eI.symm i) = Sum.inr w at hw
          rcases hi : eI.symm i with m | c'
          · rw [hi] at hw; exact absurd hw (by simp)
          · rw [hi] at hw
            have hcw : c' = w := Sum.inr_injective hw
            have hi' : i = c'.1 := by rw [← heIr c', ← hi]; simp
            have := hrank c w.1 (by rw [hpc, hi', hcw])
            exact this)
    have h' : ∀ y : Cc → ι, ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) =
        ∏ j, f j (Sum.elim (Sum.elim ℓe x) y (φ (u j))) (Sum.elim (Sum.elim ℓe x) y (φ (v j))) := by
      intro y; simp only [hφ]
    simp only [h', Finset.card_univ, hcC] at hmain ⊢
    rw [← hcC] at hmain ⊢
    have hpos : 0 < (Fintype.card ι : ℝ) ^ Fintype.card Cc := pow_pos hN _
    refine le_of_mul_le_mul_left ?_ hpos
    calc (Fintype.card ι : ℝ) ^ Fintype.card Cc * ∑ y : Cc → ι,
          ∏ j, f j (Sum.elim (Sum.elim ℓe x) y (φ (u j))) (Sum.elim (Sum.elim ℓe x) y (φ (v j)))
        ≤ (Fintype.card ι : ℝ) ^ Fintype.card Cc * K ^ Fintype.card Cc * a ^ (Fintype.card J - Fintype.card Cc) := hmain
      _ = _ := by ring
  -- the sum over the roots
  calc ∑ ℓ : I → ι, Φ (fun t => ℓ (root t)) * ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j))
      = ∑ q : (Rt → ι) × (Cc → ι), Φ (fun t => e1.symm q (root t)) *
          ∏ j, f j (Sum.elim ℓe (e1.symm q) (u j)) (Sum.elim ℓe (e1.symm q) (v j)) :=
        (Equiv.sum_comp e1.symm (fun ℓ : I → ι => Φ (fun t => ℓ (root t)) *
          ∏ j, f j (Sum.elim ℓe ℓ (u j)) (Sum.elim ℓe ℓ (v j)))).symm
    _ = ∑ x : Rt → ι, ∑ y : Cc → ι, Φ x *
          ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [hroots]
    _ = ∑ x : Rt → ι, Φ x * ∑ y : Cc → ι,
          ∏ j, f j (Sum.elim ℓe (e1.symm (x, y)) (u j)) (Sum.elim ℓe (e1.symm (x, y)) (v j)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ x : Rt → ι, Φ x * (K ^ (Fintype.card I - Fintype.card Rt) *
          a ^ (Fintype.card J - (Fintype.card I - Fintype.card Rt))) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hfix x) (hΦ x)
    _ = _ := by rw [Finset.sum_mul]

end ForestSum

section Blocks

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The sum over the labels of `Rt` points of a function of their blocks: every block has `W^d` points (`card_Iblk`). -/
theorem auxGraph_sum_blocks {Rt : Type} [Fintype Rt] [DecidableEq Rt] (g : (Rt → Zd d L) → ℝ) :
    ∑ ρ : Rt → Idx d L W, g (fun t => (split d L W (ρ t)).1) =
      ((W : ℝ) ^ d) ^ Fintype.card Rt * ∑ b : Rt → Zd d L, g b := by
  let e2 : (Rt → Idx d L W) ≃ (Rt → Zd d L) × (Rt → Fin (W ^ d)) :=
    (Equiv.arrowCongr (Equiv.refl Rt) (splitEquiv d L W)).trans (Equiv.arrowProdEquivProdArrow _ _ _)
  rw [Fintype.sum_equiv e2 (fun ρ : Rt → Idx d L W => g (fun t => (split d L W (ρ t)).1))
    (fun y => g y.1) (fun ρ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  push_cast
  rfl

end Blocks

/-! ## 8. The tail on a non-confined labelling (`(yixi)`, `scalemole`, `7_8:190-193`) -/

section Tail

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The data with `S`, `S^±` multiplied by `e^{(c/2) d_B(x,y)}` (`7_8:255-258`, the weighted kernels of the tail). -/
def auxGraph_wdata (D : LData (Idx d L W)) (c : ℝ) : LData (Idx d L W) where
  G := D.G
  M := D.M
  S := fun x y => D.S x y * ((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)
  Sp := fun x y => D.Sp x y * ((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)

/-- A waved-edge factor of the weighted data is the waved-edge factor times `e^{(c/2) d_B}` of the labels of its ends. -/
theorem auxGraph_wval_weighted (D : LData (Idx d L W)) (c : ℝ) (ℓ : E ⊕ I → Idx d L W) (e : WEdge (E ⊕ I)) :
    ‖WEdge.val (auxGraph_wdata D c) ℓ e‖ =
      ‖WEdge.val D ℓ e‖ * Real.exp ((c / 2) * (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ)) := by
  have hE : ∀ x y : Idx d L W, ‖((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)‖ =
      Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) := fun x y => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  show ‖lwWVal (auxGraph_wdata D c) e (ℓ e.x) (ℓ e.y)‖ = ‖lwWVal D e (ℓ e.x) (ℓ e.y)‖ * _
  unfold lwWVal
  by_cases hc : e.col = true
  · by_cases hσ : e.σ = true
    · simp only [hc, hσ, ite_true, auxGraph_wdata, norm_mul, hE]
    · have hσ' : e.σ = false := by simpa using hσ
      simp only [hc, hσ', ite_true, Bool.false_eq_true, ite_false, norm_star, auxGraph_wdata, norm_mul, hE]
      rw [lwBdist_comm]
  · have hc' : e.col = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false, auxGraph_wdata, norm_mul, hE]

theorem auxGraph_one_le_prod (l : List ℝ) (h : ∀ x ∈ l, 1 ≤ x) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (h x (List.mem_cons_self ..))
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- A product of exponentials of non-negative numbers, one of which exceeds `r`, is at least `e^{t r}`. -/
theorem auxGraph_prod_exp_ge {α : Type*} (l : List α) (g : α → ℝ) {t r : ℝ} (ht : 0 ≤ t)
    (hg : ∀ x ∈ l, 0 ≤ g x) (hex : ∃ x ∈ l, r ≤ g x) :
    Real.exp (t * r) ≤ (l.map fun x => Real.exp (t * g x)).prod := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hex; simp at hx
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hone : 1 ≤ (l.map fun x => Real.exp (t * g x)).prod :=
      auxGraph_one_le_prod _ fun y hy => by
        obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
        exact Real.one_le_exp (mul_nonneg ht (hg z (List.mem_cons_of_mem _ hz)))
    have hxone : 1 ≤ Real.exp (t * g x) := Real.one_le_exp (mul_nonneg ht (hg x (List.mem_cons_self ..)))
    by_cases hx : r ≤ g x
    · calc Real.exp (t * r) ≤ Real.exp (t * g x) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx ht)
        _ = Real.exp (t * g x) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hone (Real.exp_pos _).le
    · have hex' : ∃ y ∈ l, r ≤ g y := by
        obtain ⟨y, hy, hry⟩ := hex
        rcases List.mem_cons.1 hy with rfl | hy
        · exact absurd hry hx
        · exact ⟨y, hy, hry⟩
      have ih' := ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) hex'
      calc Real.exp (t * r) ≤ (l.map fun x => Real.exp (t * g x)).prod := ih'
        _ = 1 * (l.map fun x => Real.exp (t * g x)).prod := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hxone (by linarith [Real.exp_pos (t * r)])

/-- **The pointwise tail bound**: if some waved edge has block distance `> r`, then
`|term ℓ| ≤ |coeff| Ψ^{n_S} e^{-cr/2} ∏_{waved} |w_e(ℓ)| e^{(c/2) d_B}` (the product over the weighted kernels). -/
theorem auxGraph_term_tail (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W)) {m : ℂ} {Ψ c r : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ) (hc : 0 < c)
    (ℓ : E ⊕ I → Idx d L W) (hbad : ∃ e ∈ Γ.waved, r < (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ)) :
    ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) ℓ e‖).prod) := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hGd (fun _ => 0))
  have h1 := Γ.term_norm_le hN D hM hG hGd ℓ
  set P : ℝ := (Γ.waved.map fun e => ‖WEdge.val D ℓ e‖).prod with hP
  have hP0 : 0 ≤ P := List.prod_nonneg fun x hx => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hx
    exact norm_nonneg _
  have hw : (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) ℓ e‖).prod =
      P * (Γ.waved.map fun e => Real.exp ((c / 2) * (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ))).prod := by
    rw [hP, ← List.prod_map_mul]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    exact auxGraph_wval_weighted D c ℓ e
  have hexp := auxGraph_prod_exp_ge Γ.waved (fun e => (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ)) (t := c / 2) (r := r)
    (by linarith) (fun e _ => by positivity) (by
      obtain ⟨e, he, h⟩ := hbad
      exact ⟨e, he, h.le⟩)
  set Q := (Γ.waved.map fun e => Real.exp ((c / 2) * (lwBdist d L W (ℓ e.x) (ℓ e.y) : ℝ))).prod with hQ
  have hQ0 : Real.exp (c / 2 * r) ≤ Q := hexp
  have h2 : 1 ≤ Real.exp (-(c * r / 2)) * Q := by
    calc (1 : ℝ) = Real.exp (-(c * r / 2)) * Real.exp (c / 2 * r) := by
          rw [← Real.exp_add]; ring_nf; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ0 (Real.exp_pos _).le
  rw [hw]
  calc ‖Γ.term D ℓ‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * P := h1
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS * (P * 1) := by rw [mul_one]
    _ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (P * (Real.exp (-(c * r / 2)) * Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hP0) (mul_nonneg (norm_nonneg _) (pow_nonneg hΨ _))
    _ = _ := by ring

private theorem auxGraph_size_alg (W d L nM nV nW : ℕ) (hW : (W : ℝ) ≠ 0) (h1 : nM ≤ nV) (h2 : nV - nM ≤ nW) (K₀ : ℝ) :
    ((((W * L) ^ d : ℕ) : ℝ)) ^ nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (nW - (nV - nM)) =
      K₀ ^ (nW - (nV - nM)) * (((L : ℝ) ^ d) ^ nM * (W : ℝ) ^ (-(d : ℤ) * ((nW : ℤ) - nV))) := by
  obtain ⟨t, ht⟩ : ∃ t, nW = (nV - nM) + t := ⟨nW - (nV - nM), by omega⟩
  have htt : nW - (nV - nM) = t := by omega
  have hexp : -(d : ℤ) * ((nW : ℤ) - nV) = ((d * nM : ℕ) : ℤ) - ((d * t : ℕ) : ℤ) := by
    have : (nW : ℤ) - nV = (t : ℤ) - nM := by omega
    rw [this]; push_cast; ring
  rw [htt, hexp, zpow_sub₀ hW, zpow_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [pow_mul (W : ℝ) d t]

/-- **The tail sum** (`7_8:255-258`): the weighted sum over all labellings of the internal vertices is `≤ e^{-cr/2} C'_Γ size(Γ)`
(the merged peeling bound `LGraph.waved_sum_le` on the data with the weighted kernels). -/
theorem auxGraph_tail_sum (hd : 3 ≤ d) (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W)) {m : ℂ} {Ψ C c r : ℝ}
    (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (ℓe : E → Idx d L W) :
    ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) ≤
        Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hGd (fun _ => 0))
  have hc2 : 0 < c / 2 := by linarith
  have hw : ∀ x y : Idx d L W, ‖(auxGraph_wdata D c).S x y‖ ≤
      C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) ∧
      ‖(auxGraph_wdata D c).Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) := by
    intro x y
    have hE : ‖((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)‖ =
        Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) := by
      rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have key : Real.exp (-(c * (lwBdist d L W x y : ℝ))) * Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) =
        Real.exp (-((c / 2) * (lwBdist d L W x y : ℝ))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hW0 : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ := by positivity
    constructor
    · show ‖D.S x y * ((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)‖ ≤ _
      rw [norm_mul, hE, ← key]
      exact mul_le_mul_of_nonneg_right (hS x y) (Real.exp_pos _).le |>.trans_eq (by ring)
    · show ‖D.Sp x y * ((Real.exp ((c / 2) * (lwBdist d L W x y : ℝ)) : ℝ) : ℂ)‖ ≤ _
      rw [norm_mul, hE, ← key]
      exact mul_le_mul_of_nonneg_right (hSp x y) (Real.exp_pos _).le |>.trans_eq (by ring)
  have hK1 := lwKBound_of_decay hd hC hc2 (K := (auxGraph_wdata D c).S) (fun x y => (hw x y).1)
  have hK2 := lwKBound_of_decay hd hC hc2 (K := (auxGraph_wdata D c).Sp) (fun x y => (hw x y).2)
  have hsum := Γ.waved_sum_le hN (auxGraph_wdata D c) hK1 hK2 ℓe
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hcard : (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) := by rw [card_Idx]
  rw [hcard] at hsum
  have hal := auxGraph_size_alg W d L Γ.nM Γ.nV Γ.nW hW h1 h2 C
  have hE0 : 0 ≤ Real.exp (-(c * r / 2)) := (Real.exp_pos _).le
  have hA0 : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2)) := by positivity
  calc ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod)
      = (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) * ∑ ℓi : I → Idx d L W,
          (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ℓi _ => ?_
        ring
    _ ≤ (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) *
          (((((W * L) ^ d : ℕ)) : ℝ) ^ Γ.nM * (C * expC (d - 2) (c / 2)) ^ (Γ.nV - Γ.nM) *
            (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) :=
        mul_le_mul_of_nonneg_left hsum hA0
    _ = (‖Γ.coeff‖ * Ψ ^ Γ.nS * Real.exp (-(c * r / 2))) * (C * expC (d - 2) (c / 2)) ^ (Γ.nV - Γ.nM) *
          (((((W * L) ^ d : ℕ)) : ℝ) ^ Γ.nM * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) := by ring
    _ = _ := by
        rw [hal]
        unfold LGraph.sizeConst LGraph.scalingSize Counters.scalingSize
        simp only [LGraph.counters]
        ring


end Tail

/-! ## 9. The main term: the sum over the labellings of the internal vertices (`7_8:922-926`) -/

section MainSum

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The value of the auxiliary graph for any instances on the internal molecules. -/
theorem auxGraph_auxVal_eq {κ : Type} [Fintype κ] (Γ : LGraph E I) (ξ : κ → κ → ℝ) (be : E → κ)
    [Fintype (LGraph.AuxIMol Γ)] [DecidableEq (LGraph.AuxIMol Γ)] :
    Γ.auxVal ξ be = ∑ b : LGraph.AuxIMol Γ → κ,
      (Γ.molSolid.map fun e => ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)).prod := by
  unfold LGraph.auxVal
  congr <;> exact Subsingleton.elim _ _

theorem auxGraph_card_aux (Γ : LGraph E I) [Fintype (LGraph.AuxIMol Γ)] :
    Fintype.card (LGraph.AuxIMol Γ) = Γ.nM := by
  rw [Γ.nM_eq_card, Nat.card_eq_fintype_card]

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] in
theorem auxGraph_prod_waved {E I : Type} (Γ : LGraph E I) (g : WEdge (E ⊕ I) → ℝ) :
    (Γ.waved.map g).prod = ∏ j : Fin Γ.waved.length, g (Γ.waved.get j) := by
  rw [← Fin.prod_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

/-- The three bounds on `S`, `S^±` give the three bounds on every waved-edge weight. -/
theorem auxGraph_wval_bound {ι : Type} [Fintype ι] {D : LData ι} {a K₁ : ℝ} (hS : LWKBound D.S a K₁)
    (hSp : LWKBound D.Sp a K₁) (e : WEdge (E ⊕ I)) :
    (∀ x y, ‖lwWVal D e x y‖ ≤ a) ∧ (∀ x, ∑ y, ‖lwWVal D e x y‖ ≤ K₁) ∧
      (∀ y, ∑ x, ‖lwWVal D e x y‖ ≤ K₁) := by
  unfold lwWVal
  by_cases hc : e.col = true
  · by_cases hσ : e.σ = true
    · simp only [hc, hσ, ite_true]; exact hSp
    · have hσ' : e.σ = false := by simpa using hσ
      simp only [hc, hσ', ite_true, Bool.false_eq_true, ite_false, norm_star]
      exact ⟨fun x y => hSp.1 y x, fun x => hSp.2.2 x, fun y => hSp.2.1 y⟩
  · have hc' : e.col = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ite_false]; exact hS

/-- **The main sum** (`7_8:922-926`): the sum over the labels of the internal vertices of the confined bound is
`≤ |coeff| Ψ^{n_S - |𝒢_ℳ|} (W^d)^{n_M} Γ^aux_{[ℓe]} K₁^{n_V - n_M} (C W^{-d})^{n_W - (n_V - n_M)}`. -/
theorem auxGraph_main_sum (hd : 3 ≤ d) (Γ : LGraph E I) (D : LData (Idx d L W)) {C c : ℝ} {ξ : Zd d L → Zd d L → ℝ}
    (hξ0 : ∀ a b, 0 ≤ ξ a b) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (ℓe : E → Idx d L W)
    (root : LGraph.AuxIMol Γ → I) (par : I → E ⊕ I) (edge : {i : I // i ∉ Set.range root} → Fin Γ.waved.length)
    (ρ : I → ℕ) (hrootinj : Function.Injective root)
    (hrank : ∀ i : {i : I // i ∉ Set.range root}, ∀ w, par i.1 = Sum.inr w → ρ w < ρ i.1)
    (hedge : ∀ i : {i : I // i ∉ Set.range root},
      (((Γ.waved.get (edge i)).x = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).y = par i.1) ∨
       ((Γ.waved.get (edge i)).y = Sum.inr i.1 ∧ (Γ.waved.get (edge i)).x = par i.1)))
    (hedgeinj : Function.Injective edge) :
    ∑ ℓi : I → Idx d L W,
      ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) ≤
      ((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
        ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) := by
  classical
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  have hK1 := lwKBound_of_decay hd hC hc (K := D.S) hS
  have hK2 := lwKBound_of_decay hd hC hc (K := D.Sp) hSp
  have ha : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ := by positivity
  have hK : 0 ≤ C * expC (d - 2) c := by
    have : 0 < expC (d - 2) c := by unfold expC; positivity
    positivity
  set f : Fin Γ.waved.length → Idx d L W → Idx d L W → ℝ :=
    fun j x y => ‖lwWVal D (Γ.waved.get j) x y‖ with hf
  have hsum : ∀ ℓi : I → Idx d L W, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod =
      ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) := by
    intro ℓi
    rw [auxGraph_prod_waved Γ (fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖)]
    rfl
  set Φ : (LGraph.AuxIMol Γ → Idx d L W) → ℝ := fun x =>
    (Γ.molSolid.map fun e => ξ
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (x c)).1) e.src)
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (x c)).1) e.dst)).prod with hΦ
  have hΦ0 : ∀ x, 0 ≤ Φ x := fun x => List.prod_nonneg fun y hy => by
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
    exact hξ0 _ _
  have hmain := auxGraph_forest_roots (ι := Idx d L W) (E := E) (I := I) (Rt := LGraph.AuxIMol Γ)
    (J := Fin Γ.waved.length) ℓe (fun j => (Γ.waved.get j).x) (fun j => (Γ.waved.get j).y) f
    (C * ((W : ℝ) ^ d)⁻¹) (C * expC (d - 2) c) ha hK (fun j x y => norm_nonneg _)
    (fun j x y => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).1 x y)
    (fun j x => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).2.1 x)
    (fun j y => (auxGraph_wval_bound hK1 hK2 (Γ.waved.get j)).2.2 y)
    root hrootinj par edge ρ hedgeinj hedge hrank Φ hΦ0
  have hcardRt : Fintype.card (LGraph.AuxIMol Γ) = Γ.nM := auxGraph_card_aux Γ
  have hcardI : Fintype.card I = Γ.nV := rfl
  have hcardJ : Fintype.card (Fin Γ.waved.length) = Γ.nW := by simp [LGraph.nW]
  rw [hcardRt, hcardI, hcardJ] at hmain
  have hblocks := auxGraph_sum_blocks (d := d) (L := L) (W := W) (Rt := LGraph.AuxIMol Γ)
    (fun b => (Γ.molSolid.map fun e => ξ
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) b e.src)
        (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) b e.dst)).prod)
  rw [hcardRt] at hblocks
  have hav := auxGraph_auxVal_eq Γ ξ (fun a => (split d L W (ℓe a)).1)
  have hΦsum : ∑ x : LGraph.AuxIMol Γ → Idx d L W, Φ x = ((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) := by
    rw [hav]
    exact hblocks
  rw [hΦsum] at hmain
  calc _ = ∑ ℓi : I → Idx d L W, Φ (fun t => ℓi (root t)) *
          ∏ j : Fin Γ.waved.length, f j (Sum.elim ℓe ℓi (Γ.waved.get j).x) (Sum.elim ℓe ℓi (Γ.waved.get j).y) := by
        refine Finset.sum_congr rfl fun ℓi _ => ?_
        rw [hsum]
    _ ≤ _ := hmain

end MainSum

/-! ## 10. `GtoAG` and the `scalemole` tail (targets 3 and 4) -/

/-- **Target 3, `GtoAG`** (`7_8:907-928`, `(G_by_auxG)`), deterministic form: for a normal graph whose distinct external
vertices lie in distinct molecules, data with `M = m I`, entries `|G_{xy}| ≤ Ψ` (`x ≠ y`), `|G_{xx} - m| ≤ Ψ`, the decay
`(eq:estSpm-W)` of `S`, `S^±`, the window `W^{-d/2} ≤ Ψ`, and edge variables `ξ ≥ 0` on the blocks that dominate the
off-diagonal entries on the block balls of radius `R ≥ |E ⊕ I| r` (`(yixi)`, `(eq:Gbyxi)`):
`|Γ| ≤ C_Γ Ψ^{ord(Γ) - ord(Γ^aux)} (W^d)^{n_M} Γ^aux_{[ℓe]} + e^{-cr/2} C'_Γ size(Γ)`. -/
def LWGtoAG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ →
      0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R →
      (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y →
        (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R → (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R →
        ‖D.G x y‖ ≤ ξ a b) →
      ∀ ℓe : E → Idx d L W,
        ‖Γ.val D ℓe‖ ≤
          Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
              (((W : ℝ) ^ d) ^ Γ.nM * LGraph.auxVal Γ ξ (fun a => (split d L W (ℓe a)).1)) +
            Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L

/-- **Target 4, `scalemole` for two external vertices in one molecule** (`7_8:190-193`, deterministic): if `a`, `b` lie
in one molecule and their labels are at block distance `> |E ⊕ I| r`, the value is at most the tail
`e^{-cr/2} C'_Γ size(Γ)` (the outputs with `𝓜_x = 𝓜_y` under `(eq:far_ab)`, `7_8:96`). -/
def LWScalemole (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r : ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      0 ≤ r →
      ∀ (ℓe : E → Idx d L W) (a b : E), Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) →
        (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ) →
        ‖Γ.val D ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L

/-- **`GtoAG`, deterministic form** (target 3). -/
theorem lwGtoAG_holds (d : ℕ) : LWGtoAG d := by
  intro hd L W _ _ E I _ _ _ _ Γ hN hext D m Ψ C c r R ξ hM hG hGd hC hc hS hSp hwin hr hRr hξ0 hξ ℓe
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hGd (fun _ => 0))
  have hWpos : (0 : ℝ) < W := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  obtain ⟨root, par, edge, ρ, hrootinj, hroot, hrank, hedge, hedgeinj⟩ := auxGraph_exists_forest Γ hN.1
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hmS := Γ.molSolid_length_le
  have hmain := auxGraph_main_sum hd Γ D hξ0 hC hc hS hSp ℓe root par edge ρ hrootinj hrank hedge hedgeinj
  have htail := auxGraph_tail_sum hd Γ hN D (r := r) hGd hC hc hS hSp ℓe
  have hwin' : 1 ≤ (W : ℝ) ^ d * Ψ ^ 2 := (one_le_pow_mul_sq_iff W d hWpos hΨ).1 hwin
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hWpos d
  have hinv : ((W : ℝ) ^ d)⁻¹ ≤ Ψ ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hWd]; linarith
  have ha : C * ((W : ℝ) ^ d)⁻¹ ≤ C * Ψ ^ 2 := mul_le_mul_of_nonneg_left hinv hC
  have ha0 : 0 ≤ C * ((W : ℝ) ^ d)⁻¹ := by positivity
  have hapow : (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)) ≤ C ^ (Γ.nW - (Γ.nV - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nV - Γ.nM))) := by
    calc (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)) ≤ (C * Ψ ^ 2) ^ (Γ.nW - (Γ.nV - Γ.nM)) :=
          pow_le_pow_left₀ ha0 ha _
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm 2]
  have hexp : Γ.scalingOrder - LGraph.auxOrd Γ =
      (((Γ.nS - Γ.molSolid.length) + 2 * (Γ.nW - (Γ.nV - Γ.nM)) : ℕ) : ℤ) := by
    rw [Γ.scalingOrder_sub_auxOrd]
    unfold LGraph.nV at *
    omega
  rw [hexp, zpow_natCast]
  have hav0 := Γ.auxVal_nonneg ξ hξ0 (fun a => (split d L W (ℓe a)).1)
  have hK0 : 0 ≤ C * expC (d - 2) c := by
    have : 0 < expC (d - 2) c := by unfold expC; positivity
    positivity
  have hmain' : ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) ≤
      Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ ((Γ.nS - Γ.molSolid.length) + 2 * (Γ.nW - (Γ.nV - Γ.nM))) *
        (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) := by
    rw [← Finset.mul_sum]
    have hcn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) := by positivity
    calc ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) * ∑ ℓi : I → Idx d L W,
          ((Γ.molSolid.map fun e => ξ
            (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod)
        ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) * (C * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)))) :=
          mul_le_mul_of_nonneg_left hmain hcn
      _ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            ((C * expC (d - 2) c) ^ (Γ.nV - Γ.nM) *
              (C ^ (Γ.nW - (Γ.nV - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nV - Γ.nM)))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcn
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hav0)
          exact mul_le_mul_of_nonneg_left hapow (by positivity)
      _ = _ := by
          unfold LGraph.sizeConst
          rw [pow_add]
          ring
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤
      ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
    intro ℓi
    have hMn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) := by
      have h1 : 0 ≤ (Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact hξ0 _ _
      have h2 : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact norm_nonneg _
      positivity
    have hTl : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
      have h2 : 0 ≤ (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact norm_nonneg _
      positivity
    by_cases hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r
    · exact (auxGraph_term_conf Γ hN D hM hG hGd hξ0 hξ hr hRr ℓe ℓi root hroot hconf).trans
        (le_add_of_nonneg_right hTl)
    · push Not at hconf
      exact (auxGraph_term_tail Γ hN D hM hG hGd hc _ hconf).trans (le_add_of_nonneg_left hMn)
  unfold LGraph.val
  calc ‖∑ ℓi : I → Idx d L W, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓi : I → Idx d L W, (‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.molSolid.length) *
        ((Γ.molSolid.map fun e => ξ
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
          (LGraph.auxLab Γ (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
        (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod)) :=
        Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmain' htail

/-- **Target 4 (`scalemole`, two external vertices in one molecule)**: no labelling is confined, so the tail bound alone applies. -/
theorem lwScalemole_holds (d : ℕ) : LWScalemole d := by
  intro hd L W _ _ E I _ _ _ _ Γ hN D m Ψ C c r hM hG hGd hC hc hS hSp hr ℓe a b hab hfar
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have htail := auxGraph_tail_sum hd Γ hN D (r := r) hGd hC hc hS hSp ℓe
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
    intro ℓi
    refine auxGraph_term_tail Γ hN D hM hG hGd hc _ ?_
    by_contra hcon
    have hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r := by
      intro e he
      by_contra h
      exact hcon ⟨e, he, not_le.1 h⟩
    have := auxGraph_mol_dist Γ hN.1 (Sum.elim ℓe ℓi) hr hconf hab
    exact absurd hfar (not_lt.2 this)
  unfold LGraph.val
  calc ‖∑ ℓi : I → Idx d L W, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ ≤ _ := htail

/-! ## 11. The nested form of `Γ^aux` (target 5, `7_8:953-958`)

The walks `W i` of `lem:localregular` (3)-(5) are moved into an `NGraph`: the molecule `𝓜_x` becomes `a_i`, `𝓜_y` becomes `b_i` (on the
walk `i`), an internal molecule becomes the internal vertex `inr (e.symm c)`.  The edges are the steps of the walks, then the molecular edges
used by no walk (attached to the walk `0`).  The slots `(i, k)` and `r` are enumerated by `Fintype.equivFin`. -/

section Nested

open Classical

/-- Data for the construction: `0 < p`, the numbering `e` of the internal molecules, the walks and the unused molecular edges. -/
structure auxGraph_Data (Q : PGraph (Fin 2)) (p : ℕ) where
  hp : 0 < p
  e : Fin Q.g.nM ≃ LGraph.AuxIMol Q.g
  W : Fin p → List (Q.g.Mol × Q.g.Mol)
  rest : List (Q.g.Mol × Q.g.Mol)

variable {Q : PGraph (Fin 2)} {p : ℕ}

/-- The vertex of the nested graph of a molecule on the walk `i`. -/
def auxGraph_nodeV (Dt : auxGraph_Data Q p) (i : Fin p) (c : Q.g.Mol) : NV p Q.g.nM :=
  if c = Q.g.molOf (Sum.inl (Q.ext 0)) then Sum.inl (Sum.inl i)
  else if c = Q.g.molOf (Sum.inl (Q.ext 1)) then Sum.inl (Sum.inr i)
  else if h : ¬ Q.g.IsExtMol c then Sum.inr (Dt.e.symm ⟨c, h⟩) else Sum.inl (Sum.inl i)

/-- The slots: the steps `(i, k)` of the walks and the unused edges `r`. -/
abbrev auxGraph_Slots (Dt : auxGraph_Data Q p) : Type :=
  (Σ i : Fin p, Fin (Dt.W i).length) ⊕ Fin Dt.rest.length

/-- The edge of a slot. -/
def auxGraph_edgeOf (Dt : auxGraph_Data Q p) : auxGraph_Slots Dt → NEdge p Q.g.nM
  | Sum.inl ⟨i, k⟩ => ⟨false, auxGraph_nodeV Dt i ((Dt.W i).get k).1, auxGraph_nodeV Dt i ((Dt.W i).get k).2⟩
  | Sum.inr r => ⟨false, auxGraph_nodeV Dt ⟨0, Dt.hp⟩ (Dt.rest.get r).1, auxGraph_nodeV Dt ⟨0, Dt.hp⟩ (Dt.rest.get r).2⟩

/-- The edge list of the nested graph. -/
noncomputable def auxGraph_es (Dt : auxGraph_Data Q p) : List (NEdge p Q.g.nM) :=
  List.ofFn fun s : Fin (Fintype.card (auxGraph_Slots Dt)) =>
    auxGraph_edgeOf Dt ((Fintype.equivFin (auxGraph_Slots Dt)).symm s)

theorem auxGraph_es_length (Dt : auxGraph_Data Q p) : (auxGraph_es Dt).length = Fintype.card (auxGraph_Slots Dt) :=
  List.length_ofFn

/-- The position of a slot in the edge list. -/
noncomputable def auxGraph_pos (Dt : auxGraph_Data Q p) (s : auxGraph_Slots Dt) : Fin (auxGraph_es Dt).length :=
  Fin.cast (auxGraph_es_length Dt).symm (Fintype.equivFin (auxGraph_Slots Dt) s)

theorem auxGraph_es_get (Dt : auxGraph_Data Q p) (s : auxGraph_Slots Dt) :
    (auxGraph_es Dt).get (auxGraph_pos Dt s) = auxGraph_edgeOf Dt s := by
  have hlt : (Fintype.equivFin (auxGraph_Slots Dt) s).val <
      (List.ofFn fun s' : Fin (Fintype.card (auxGraph_Slots Dt)) =>
        auxGraph_edgeOf Dt ((Fintype.equivFin (auxGraph_Slots Dt)).symm s')).length := by
    rw [List.length_ofFn]; exact Fin.is_lt _
  have h := List.getElem_ofFn (f := fun s' : Fin (Fintype.card (auxGraph_Slots Dt)) =>
    auxGraph_edgeOf Dt ((Fintype.equivFin (auxGraph_Slots Dt)).symm s'))
    (i := (Fintype.equivFin (auxGraph_Slots Dt) s).val) hlt
  have h2 : (Fintype.equivFin (auxGraph_Slots Dt)).symm ⟨(Fintype.equivFin (auxGraph_Slots Dt) s).val, by
      rw [List.length_ofFn] at hlt; exact hlt⟩ = s := by simp
  rw [List.get_eq_getElem]
  exact h.trans (by rw [h2])

theorem auxGraph_pos_injective (Dt : auxGraph_Data Q p) : Function.Injective (auxGraph_pos Dt) := by
  intro s s' h
  unfold auxGraph_pos at h
  have := (Fin.cast_injective _ h)
  exact (Fintype.equivFin (auxGraph_Slots Dt)).injective this

/-- The nested graph. -/
noncomputable def auxGraph_ngraph (Dt : auxGraph_Data Q p) : NGraph p Q.g.nM where
  es := auxGraph_es Dt
  path := fun i => (List.finRange (Dt.W i).length).map fun k =>
    (auxGraph_pos Dt (Sum.inl ⟨i, k⟩), auxGraph_nodeV Dt i ((Dt.W i).get k).2)

end Nested

section Nested2

open Classical

variable {Q : PGraph (Fin 2)} {p : ℕ}

/-- Every external molecule is `𝓜_x` or `𝓜_y` (`ext` is onto). -/
theorem auxGraph_ext_mol (c : Q.g.Mol) (hc : Q.g.IsExtMol c) :
    c = Q.g.molOf (Sum.inl (Q.ext 0)) ∨ c = Q.g.molOf (Sum.inl (Q.ext 1)) := by
  obtain ⟨a, rfl⟩ := hc
  obtain ⟨j, rfl⟩ := Q.ext_surj a
  fin_cases j
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem auxGraph_mol_cls (c : Q.g.Mol) :
    c = Q.g.molOf (Sum.inl (Q.ext 0)) ∨ c = Q.g.molOf (Sum.inl (Q.ext 1)) ∨ ¬ Q.g.IsExtMol c := by
  by_cases hc : Q.g.IsExtMol c
  · rcases auxGraph_ext_mol c hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hc)

theorem auxGraph_nodeV_x (Dt : auxGraph_Data Q p) (i : Fin p) :
    auxGraph_nodeV Dt i (Q.g.molOf (Sum.inl (Q.ext 0))) = Sum.inl (Sum.inl i) := by
  unfold auxGraph_nodeV
  rw [if_pos rfl]

theorem auxGraph_nodeV_y (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (i : Fin p) :
    auxGraph_nodeV Dt i (Q.g.molOf (Sum.inl (Q.ext 1))) = Sum.inl (Sum.inr i) := by
  unfold auxGraph_nodeV
  rw [if_neg (Ne.symm hxy), if_pos rfl]

theorem auxGraph_nodeV_int (Dt : auxGraph_Data Q p) (i : Fin p) (c : Q.g.Mol) (h : ¬ Q.g.IsExtMol c) :
    auxGraph_nodeV Dt i c = Sum.inr (Dt.e.symm ⟨c, h⟩) := by
  have h1 : c ≠ Q.g.molOf (Sum.inl (Q.ext 0)) := fun hc => h (hc ▸ ⟨Q.ext 0, rfl⟩)
  have h2 : c ≠ Q.g.molOf (Sum.inl (Q.ext 1)) := fun hc => h (hc ▸ ⟨Q.ext 1, rfl⟩)
  unfold auxGraph_nodeV
  rw [if_neg h1, if_neg h2, dif_pos h]

theorem auxGraph_nodeV_inj (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (i : Fin p) : Function.Injective (auxGraph_nodeV Dt i) := by
  intro c c' h
  rcases auxGraph_mol_cls c with rfl | rfl | hc <;> rcases auxGraph_mol_cls c' with rfl | rfl | hc'
  · rfl
  · rw [auxGraph_nodeV_x, auxGraph_nodeV_y hxy] at h; simp at h
  · rw [auxGraph_nodeV_x, auxGraph_nodeV_int Dt i _ hc'] at h; simp at h
  · rw [auxGraph_nodeV_x, auxGraph_nodeV_y hxy] at h; simp at h
  · rfl
  · rw [auxGraph_nodeV_y hxy, auxGraph_nodeV_int Dt i _ hc'] at h; simp at h
  · rw [auxGraph_nodeV_x, auxGraph_nodeV_int Dt i _ hc] at h; simp at h
  · rw [auxGraph_nodeV_y hxy, auxGraph_nodeV_int Dt i _ hc] at h; simp at h
  · rw [auxGraph_nodeV_int Dt i _ hc, auxGraph_nodeV_int Dt i _ hc'] at h
    have := Dt.e.symm.injective (Sum.inr_injective h)
    exact congrArg Subtype.val this

/-- **The walk as a path of the nested graph**: if the entries `E` correspond to the steps of a walk `l` (the edge at the position of the
entry is the image of the step, and the entry carries the image of the end of the step), the entries form a walk from `φ u` to `φ v`. -/
theorem auxGraph_foldl_walk {q : ℕ} {Mol : Type} (es : List (NEdge p q)) (φ : Mol → NV p q)
    {l : List (Mol × Mol)} {E : List (Fin es.length × NV p q)}
    (hF : List.Forall₂ (fun (st : Mol × Mol) (ent : Fin es.length × NV p q) =>
      es.get ent.1 = ⟨false, φ st.1, φ st.2⟩ ∧ ent.2 = φ st.2) l E) :
    ∀ {u v : Mol}, localReg_StepWalk u v l →
      E.foldl (fun (acc : Option (NV p q)) st => acc.bind fun c =>
        if ((es.get st.1).u = c ∧ (es.get st.1).v = st.2) ∨ ((es.get st.1).v = c ∧ (es.get st.1).u = st.2)
        then some st.2 else none) (some (φ u)) = some (φ v) := by
  induction hF with
  | nil =>
    intro u v hw
    have huv : u = v := hw
    subst huv
    rfl
  | @cons st ent l E hst hF ih =>
    intro u v hw
    obtain ⟨hu, hw'⟩ := hw
    obtain ⟨h1, h2⟩ := hst
    simp only [List.foldl_cons, Option.bind_some]
    have hcond : ((es.get ent.1).u = φ u ∧ (es.get ent.1).v = ent.2) ∨
        ((es.get ent.1).v = φ u ∧ (es.get ent.1).u = ent.2) := by
      left
      rw [h1, h2, hu]
      exact ⟨rfl, rfl⟩
    rw [if_pos hcond, h2]
    exact ih hw'

end Nested2

section Nested3

open Classical

variable {Q : PGraph (Fin 2)} {p : ℕ}

theorem auxGraph_forall₂_finRange {α β : Type} (l : List α) (F : Fin l.length → β) (R : α → β → Prop)
    (h : ∀ k, R (l.get k) (F k)) : List.Forall₂ R l ((List.finRange l.length).map F) := by
  rw [List.forall₂_iff_get]
  refine ⟨by simp, fun i h1 h2 => ?_⟩
  simpa using h ⟨i, h1⟩

/-- No ghost edge. -/
theorem auxGraph_noGhost (Dt : auxGraph_Data Q p) : (auxGraph_ngraph Dt).NoGhost := by
  intro e he
  change e ∈ auxGraph_es Dt at he
  unfold auxGraph_es at he
  obtain ⟨s, rfl⟩ := List.mem_ofFn.1 he
  rcases (Fintype.equivFin (auxGraph_Slots Dt)).symm s with ⟨i, k⟩ | r <;> rfl

/-- No self-loop. -/
theorem auxGraph_noLoop (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (hnd : ∀ i, ∀ st ∈ Dt.W i, st.1 ≠ st.2) (hndr : ∀ st ∈ Dt.rest, st.1 ≠ st.2) :
    ∀ e ∈ (auxGraph_ngraph Dt).es, e.u ≠ e.v := by
  intro e he
  change e ∈ auxGraph_es Dt at he
  unfold auxGraph_es at he
  obtain ⟨s, rfl⟩ := List.mem_ofFn.1 he
  rcases (Fintype.equivFin (auxGraph_Slots Dt)).symm s with ⟨i, k⟩ | r
  · intro h
    exact hnd i _ (List.get_mem _ k) (auxGraph_nodeV_inj hxy Dt i h)
  · intro h
    exact hndr _ (List.get_mem _ r) (auxGraph_nodeV_inj hxy Dt ⟨0, Dt.hp⟩ h)

/-- Every path is a walk `a_i → b_i`. -/
theorem auxGraph_walkOK (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (hW : ∀ i, localReg_StepWalk (Q.g.molOf (Sum.inl (Q.ext 0)))
      (Q.g.molOf (Sum.inl (Q.ext 1))) (Dt.W i)) (i : Fin p) : (auxGraph_ngraph Dt).WalkOK i := by
  unfold NGraph.WalkOK
  have hF := auxGraph_forall₂_finRange (Dt.W i)
    (fun k => (auxGraph_pos Dt (Sum.inl ⟨i, k⟩), auxGraph_nodeV Dt i ((Dt.W i).get k).2))
    (fun (st : Q.g.Mol × Q.g.Mol) (ent : Fin (auxGraph_es Dt).length × NV p Q.g.nM) =>
      (auxGraph_es Dt).get ent.1 = ⟨false, auxGraph_nodeV Dt i st.1, auxGraph_nodeV Dt i st.2⟩ ∧
        ent.2 = auxGraph_nodeV Dt i st.2)
    (fun k => ⟨by rw [auxGraph_es_get]; rfl, rfl⟩)
  have := auxGraph_foldl_walk (auxGraph_es Dt) (auxGraph_nodeV Dt i) hF (hW i)
  rw [auxGraph_nodeV_x, auxGraph_nodeV_y hxy] at this
  exact this

theorem auxGraph_nodup (Dt : auxGraph_Data Q p) (i : Fin p) :
    (((auxGraph_ngraph Dt).path i).map Prod.fst).Nodup := by
  change (((List.finRange (Dt.W i).length).map fun k =>
    (auxGraph_pos Dt (Sum.inl ⟨i, k⟩), auxGraph_nodeV Dt i ((Dt.W i).get k).2)).map Prod.fst).Nodup
  rw [List.map_map]
  refine List.Nodup.map ?_ (List.nodup_finRange _)
  intro k k' h
  have := auxGraph_pos_injective Dt h
  simpa using this

theorem auxGraph_disjoint (Dt : auxGraph_Data Q p) :
    ∀ i j, i ≠ j → ∀ st ∈ (auxGraph_ngraph Dt).path i, ∀ st' ∈ (auxGraph_ngraph Dt).path j, st.1 ≠ st'.1 := by
  intro i j hij st hst st' hst' h
  change st ∈ (List.finRange (Dt.W i).length).map _ at hst
  change st' ∈ (List.finRange (Dt.W j).length).map _ at hst'
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hst
  obtain ⟨k', -, rfl⟩ := List.mem_map.1 hst'
  have := auxGraph_pos_injective Dt h
  exact hij (Sigma.mk.inj_iff.1 (Sum.inl.inj this)).1

/-- A step of the walk `i` landing at the internal molecule `(e α)` makes the path `i` visit the vertex `inr α`. -/
theorem auxGraph_visits (Dt : auxGraph_Data Q p) (i : Fin p) (α : Fin Q.g.nM)
    (h : ∃ st ∈ Dt.W i, st.2 = (Dt.e α).1) : (auxGraph_ngraph Dt).Visits i (Sum.inr α) := by
  obtain ⟨st, hst, hst2⟩ := h
  obtain ⟨k, hk⟩ := List.mem_iff_get.1 hst
  refine ⟨(auxGraph_pos Dt (Sum.inl ⟨i, k⟩), auxGraph_nodeV Dt i ((Dt.W i).get k).2), ?_, Or.inr ?_⟩
  · change _ ∈ (List.finRange (Dt.W i).length).map _
    exact List.mem_map.2 ⟨k, List.mem_finRange k, rfl⟩
  · change ((auxGraph_es Dt).get (auxGraph_pos Dt (Sum.inl ⟨i, k⟩))).v = _
    rw [auxGraph_es_get]
    change auxGraph_nodeV Dt i ((Dt.W i).get k).2 = _
    rw [hk, hst2, auxGraph_nodeV_int Dt i _ (Dt.e α).2]
    simp

/-- The path properties (1)-(6) of `IsNested` from the walks of `lem:localregular` (3)-(5). -/
theorem auxGraph_isNested (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p)
    (hW : ∀ i, localReg_StepWalk (Q.g.molOf (Sum.inl (Q.ext 0))) (Q.g.molOf (Sum.inl (Q.ext 1))) (Dt.W i))
    (hnd : ∀ i, ∀ st ∈ Dt.W i, st.1 ≠ st.2) (hndr : ∀ st ∈ Dt.rest, st.1 ≠ st.2)
    (h4 : ∀ c : Q.g.Mol, ¬ Q.g.IsExtMol c → ∃ i j : Fin p, i ≠ j ∧
      localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (Dt.W i) c ∧
      localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (Dt.W j) c)
    (h5 : ∀ A : Finset Q.g.Mol, (∀ c ∈ A, ¬ Q.g.IsExtMol c) →
      A.card ≤ (Finset.univ.filter fun i : Fin p =>
        ∃ c ∈ A, localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (Dt.W i) c).card) :
    (auxGraph_ngraph Dt).IsNested := by
  have hvis : ∀ (i : Fin p) (c : Q.g.Mol), ¬ Q.g.IsExtMol c →
      localReg_StepWalk.Visits (Q.g.molOf (Sum.inl (Q.ext 0))) (Dt.W i) c → ∃ st ∈ Dt.W i, st.2 = c := by
    intro i c hc hv
    rcases hv with rfl | h
    · exact absurd ⟨Q.ext 0, rfl⟩ hc
    · exact h
  refine ⟨auxGraph_noLoop hxy Dt hnd hndr, auxGraph_walkOK hxy Dt hW, auxGraph_nodup Dt,
    auxGraph_disjoint Dt, ?_, ?_⟩
  · intro α
    obtain ⟨i, j, hij, hi, hj⟩ := h4 (Dt.e α).1 (Dt.e α).2
    exact ⟨i, j, hij, auxGraph_visits Dt i α (hvis i _ (Dt.e α).2 hi),
      auxGraph_visits Dt j α (hvis j _ (Dt.e α).2 hj)⟩
  · intro A
    have hA' : ∀ c ∈ A.image (fun α => (Dt.e α).1), ¬ Q.g.IsExtMol c := by
      intro c hc
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hc
      exact (Dt.e α).2
    have h5' := h5 _ hA'
    rw [Finset.card_image_of_injective _ (fun α β h => Dt.e.injective (Subtype.ext h))] at h5'
    refine h5'.trans (Finset.card_le_card fun i hi => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨c, hc, hv⟩ := hi
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨α, hα, auxGraph_visits Dt i α (hvis i _ (Dt.e α).2 hv)⟩

end Nested3

section Nested4

open Classical

variable {Q : PGraph (Fin 2)} {p : ℕ}

theorem auxGraph_prod_fin_get {α : Type} (l : List α) (g : α → ℝ) :
    ∏ k : Fin l.length, g (l.get k) = (l.map g).prod := by
  calc ∏ k : Fin l.length, g (l.get k) = (List.ofFn fun k : Fin l.length => g (l.get k)).prod :=
        (List.prod_ofFn).symm
    _ = ((List.ofFn l.get).map g).prod := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [List.ofFn_get]

theorem auxGraph_prod_map_sum {α : Type} (Fm : α → ℝ) (m : Fin p → Multiset α) (s : Finset (Fin p)) :
    ((∑ i ∈ s, m i).map Fm).prod = ∏ i ∈ s, ((m i).map Fm).prod := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add, Multiset.prod_add, ih]

/-- The molecular edges as a multiset have the length of `molSolid`. -/
theorem auxGraph_molEdgeMS_card (Γ : LGraph Q.E' Q.I') : Multiset.card Γ.localReg_molEdgeMS = Γ.molSolid.length := by
  unfold LGraph.localReg_molEdgeMS
  rw [Multiset.coe_card, List.length_map]

/-- The non-diagonal property of the molecular edges. -/
theorem auxGraph_molEdgeMS_nd (Γ : LGraph Q.E' Q.I') {z : Sym2 Γ.Mol} (hz : z ∈ Γ.localReg_molEdgeMS) :
    ¬ z.IsDiag := by
  unfold LGraph.localReg_molEdgeMS at hz
  rw [Multiset.mem_coe, List.mem_map] at hz
  obtain ⟨e, he, rfl⟩ := hz
  unfold LGraph.molSolid at he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.1 he
  rw [List.mem_filter] at he0
  have := of_decide_eq_true he0.2
  rw [Sym2.mk_isDiag_iff]
  exact this

end Nested4

section Nested5

open Classical

variable {Q : PGraph (Fin 2)} {p : ℕ}

theorem auxGraph_card_sum (m : Fin p → Multiset (Sym2 Q.g.Mol)) (s : Finset (Fin p)) :
    Multiset.card (∑ i ∈ s, m i) = ∑ i ∈ s, Multiset.card (m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, Multiset.card_add, ih]

theorem auxGraph_card_cover (Dt : auxGraph_Data Q p) (hM : (∑ i, localReg_stepEdges (Dt.W i)) + (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS) :
    Fintype.card (auxGraph_Slots Dt) = Q.g.molSolid.length := by
  have h := congrArg Multiset.card hM
  rw [auxGraph_molEdgeMS_card, Multiset.card_add, auxGraph_card_sum] at h
  simp only [Multiset.coe_card, List.length_map, localReg_stepEdges] at h
  rw [← h]
  simp [Fintype.card_sum, Fintype.card_sigma]

theorem auxGraph_ordN (Dt : auxGraph_Data Q p) (hM : (∑ i, localReg_stepEdges (Dt.W i)) + (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS) :
    (auxGraph_ngraph Dt).ordN = LGraph.auxOrd Q.g := by
  have hns : (auxGraph_ngraph Dt).nSolid = Q.g.molSolid.length := by
    unfold NGraph.nSolid
    rw [List.filter_eq_self.2 (fun e he => by simp [auxGraph_noGhost Dt e he])]
    change (auxGraph_es Dt).length = _
    rw [auxGraph_es_length, auxGraph_card_cover Dt hM]
  unfold NGraph.ordN LGraph.auxOrd
  rw [hns]

end Nested5

section Nested6

open Classical

variable {Q : PGraph (Fin 2)} {p : ℕ}

theorem auxGraph_ext_inj (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1))) :
    ∀ a b : Q.E', Q.g.molOf (Sum.inl a) = Q.g.molOf (Sum.inl b) → a = b := by
  intro a b h
  obtain ⟨j, rfl⟩ := Q.ext_surj a
  obtain ⟨j', rfl⟩ := Q.ext_surj b
  fin_cases j <;> fin_cases j'
  · rfl
  · exact absurd h hxy
  · exact absurd h.symm hxy
  · rfl

/-- **The value of the nested graph** is the value of the auxiliary graph (for a symmetric `ξ`): the multiset of the unordered block pairs of
the edge list is that of `molSolid`. -/
theorem auxGraph_val_eq (hxy : Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)))
    (Dt : auxGraph_Data Q p) (hM : (∑ i, localReg_stepEdges (Dt.W i)) + (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS)
    {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ) (hsymm : ∀ u v, ξ u v = ξ v u) (be : Q.E' → κ) :
    (auxGraph_ngraph Dt).val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be := by
  have : Fintype (LGraph.AuxIMol Q.g) := Fintype.ofFinite _
  rw [auxGraph_auxVal_eq]
  unfold NGraph.val
  refine Fintype.sum_equiv (Dt.e.arrowCongr (Equiv.refl κ)) _ _ (fun ℓ => ?_)
  set bb : LGraph.AuxIMol Q.g → κ := (Dt.e.arrowCongr (Equiv.refl κ)) ℓ with hbb
  have hbbe : ∀ j, bb (Dt.e j) = ℓ j := by
    intro j; simp [hbb, Equiv.arrowCongr]
  -- the labels of the vertices of the nested graph are the blocks of the molecules
  have hlab : ∀ (i : Fin p) (c : Q.g.Mol),
      Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ (auxGraph_nodeV Dt i c) =
        LGraph.auxLab Q.g be bb c := by
    intro i c
    rcases auxGraph_mol_cls c with rfl | rfl | hc
    · rw [auxGraph_nodeV_x, auxGraph_auxLab_ext Q.g (auxGraph_ext_inj hxy)]
      rfl
    · rw [auxGraph_nodeV_y hxy, auxGraph_auxLab_ext Q.g (auxGraph_ext_inj hxy)]
      rfl
    · rw [auxGraph_nodeV_int Dt i c hc]
      unfold LGraph.auxLab
      rw [dif_neg hc]
      change ℓ (Dt.e.symm ⟨c, hc⟩) = bb ⟨c, hc⟩
      rw [← hbbe, Equiv.apply_symm_apply]
  let Fm : Sym2 Q.g.Mol → ℝ := Sym2.lift ⟨fun c c' => ξ (LGraph.auxLab Q.g be bb c) (LGraph.auxLab Q.g be bb c'),
    fun c c' => hsymm _ _⟩
  have hFm : ∀ c c', Fm s(c, c') = ξ (LGraph.auxLab Q.g be bb c) (LGraph.auxLab Q.g be bb c') := fun c c' => rfl
  set F : NEdge p Q.g.nM → ℝ := fun e => if e.ghost then (1 : ℝ) else
    ξ (Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ e.u)
      (Sum.elim (Sum.elim (fun _ : Fin p => be (Q.ext 0)) (fun _ : Fin p => be (Q.ext 1))) ℓ e.v) with hF
  have hFslot : ∀ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) =
      Sum.elim (fun ik : Σ i : Fin p, Fin (Dt.W i).length =>
          Fm s(((Dt.W ik.1).get ik.2).1, ((Dt.W ik.1).get ik.2).2))
        (fun r : Fin Dt.rest.length => Fm s((Dt.rest.get r).1, (Dt.rest.get r).2)) s := by
    intro s
    rcases s with ⟨i, k⟩ | r
    · simp only [hF, auxGraph_edgeOf, Bool.false_eq_true, ite_false, Sum.elim_inl, hFm, hlab]
    · simp only [hF, auxGraph_edgeOf, Bool.false_eq_true, ite_false, Sum.elim_inr, hFm, hlab]
  have h1 : ((auxGraph_ngraph Dt).es.map F).prod = ∏ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) := by
    change ((List.ofFn _).map F).prod = _
    rw [List.map_ofFn, List.prod_ofFn]
    exact Equiv.prod_comp (Fintype.equivFin (auxGraph_Slots Dt)).symm (fun s => F (auxGraph_edgeOf Dt s))
  have h2 : ∏ s : auxGraph_Slots Dt, F (auxGraph_edgeOf Dt s) =
      (∏ i : Fin p, ((localReg_stepEdges (Dt.W i)).map Fm).prod) *
        (((↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)).map Fm).prod) := by
    simp only [hFslot]
    rw [Fintype.prod_sum_type, Fintype.prod_sigma]
    simp only [Sum.elim_inl, Sum.elim_inr]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [auxGraph_prod_fin_get (Dt.W i) (fun st => Fm s(st.1, st.2))]
      unfold localReg_stepEdges
      rw [Multiset.map_coe, Multiset.prod_coe, List.map_map]
      rfl
    · rw [auxGraph_prod_fin_get Dt.rest (fun st => Fm s(st.1, st.2)), Multiset.map_coe, Multiset.prod_coe, List.map_map]
      rfl
  have h3 : ((Q.g.localReg_molEdgeMS).map Fm).prod =
      (Q.g.molSolid.map fun e => ξ (LGraph.auxLab Q.g be bb e.src) (LGraph.auxLab Q.g be bb e.dst)).prod := by
    unfold LGraph.localReg_molEdgeMS
    rw [Multiset.map_coe, Multiset.prod_coe, List.map_map]
    rfl
  rw [← h3, ← hM, Multiset.map_add, Multiset.prod_add, auxGraph_prod_map_sum, ← h2, ← h1]

end Nested6

/-- **Target 5, the nested form of `Γ^aux`** (`7_8:953-958`; the input of `LWAnp`): for a packed graph with the walks of
`lem:localregular` (3)-(5) and `𝓜_x ≠ 𝓜_y` (`(eq:far_ab)`, `7_8:792`), a nested graph with `p` paths and `q = n_M`
internal vertices, without ghost edges, of order `ord(Γ^aux)`, whose value at `a_i = [x]`, `b_i = [y]` is the value of
the auxiliary graph for every symmetric `ξ` (`7_8:898`). -/
def LWAuxNested : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be

/-- **The nested form of `Γ^aux`** (target 5): the walks of `lem:localregular` (3)-(5), the molecule `𝓜_x` read as `a_i`, `𝓜_y` as `b_i`, the
internal molecules as the internal vertices, and the molecular edges used by no walk attached to `a_0`, `b_0`. -/
theorem lwAuxNested_holds : LWAuxNested := by
  classical
  rintro p Q hp ⟨W, h3, h4, h5⟩ hxy
  have : Fintype (LGraph.AuxIMol Q.g) := Fintype.ofFinite _
  let e : Fin Q.g.nM ≃ LGraph.AuxIMol Q.g := (Fintype.equivFinOfCardEq (auxGraph_card_aux Q.g)).symm
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 h3.2
  let Dt : auxGraph_Data Q p := ⟨hp, e, W, R.toList.map fun z => Quot.out z⟩
  have hout : ∀ z : Sym2 Q.g.Mol, s((Quot.out z).1, (Quot.out z).2) = z := fun z => Quot.out_eq z
  have hcover : (∑ i, localReg_stepEdges (Dt.W i)) +
      (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = Q.g.localReg_molEdgeMS := by
    have : (↑(Dt.rest.map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R := by
      change (↑((R.toList.map fun z => Quot.out z).map fun st => s(st.1, st.2)) : Multiset (Sym2 Q.g.Mol)) = R
      rw [List.map_map]
      have h1 : ((fun st : Q.g.Mol × Q.g.Mol => s(st.1, st.2)) ∘ fun z : Sym2 Q.g.Mol => Quot.out z) = id := by
        funext z; exact hout z
      rw [h1, List.map_id, Multiset.coe_toList]
    rw [this]
    exact hR.symm
  have hnd : ∀ i, ∀ st ∈ Dt.W i, st.1 ≠ st.2 := by
    intro i st hst
    have h1 : s(st.1, st.2) ∈ localReg_stepEdges (W i) := localReg_mem_stepEdges.2 ⟨st, hst, rfl⟩
    have h2 : s(st.1, st.2) ∈ ∑ j, localReg_stepEdges (W j) := Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, h1⟩
    have h3' := auxGraph_molEdgeMS_nd Q.g (Multiset.mem_of_le h3.2 h2)
    rwa [Sym2.mk_isDiag_iff] at h3'
  have hndr : ∀ st ∈ Dt.rest, st.1 ≠ st.2 := by
    intro st hst
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hst
    have hzR : z ∈ R := Multiset.mem_toList.1 hz
    have hz' : z ∈ Q.g.localReg_molEdgeMS := by rw [hR]; exact Multiset.mem_add.2 (Or.inr hzR)
    have := auxGraph_molEdgeMS_nd Q.g hz'
    rw [← hout z] at this
    rwa [Sym2.mk_isDiag_iff] at this
  exact ⟨auxGraph_ngraph Dt, auxGraph_noGhost Dt, auxGraph_isNested hxy Dt h3.1 hnd hndr h4 h5,
    auxGraph_ordN Dt hcover, fun ξ hsymm be => auxGraph_val_eq hxy Dt hcover ξ hsymm be⟩

/-! ## 12. Compiled instances at `d = 3`, `L = 4`, `W = 2`, `g = t = 1/2`, `E = 0` -/

section Instances

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- `|𝒢_ℳ|` computed from the decidable closure `mol` (for the instances). -/
theorem auxGraph_molSolid_length (Γ : LGraph E I) :
    Γ.molSolid.length = (Γ.solid.filter fun e => decide (e.dst ∉ Γ.mol e.src)).length := by
  classical
  unfold LGraph.molSolid
  rw [List.length_map]
  congr 1
  refine List.filter_congr fun e _ => ?_
  rw [decide_eq_decide]
  simp only [LGraph.InsideMol, LGraph.molOf_eq_iff]

/-- The auxiliary graph with a constant edge variable: `|κ|^{n_M} c^{|𝒢_ℳ|}`. -/
theorem auxGraph_auxVal_const {κ : Type} [Fintype κ] (Γ : LGraph E I) (c : ℝ) (be : E → κ) :
    Γ.auxVal (fun _ _ => c) be = (Fintype.card κ : ℝ) ^ Γ.nM * c ^ Γ.molSolid.length := by
  classical
  have : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  rw [auxGraph_auxVal_eq]
  simp only [List.map_const', List.prod_replicate, List.length_map, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, nsmul_eq_mul, Nat.cast_pow]
  rw [auxGraph_card_aux]

/-- The concrete data `G = m(0) I + (1/2) J`, `M = m(0) I`, `S = lwSmat 3 4 2 (1/2) (1/2)`,
`S^± = lwSpOf 3 4 2 (1/2) (1/2) (m(0))` on `Z_8^3` (`lwSizeD0` with `1/2` in place of `1/100`). -/
def auxGraph_instD : LData (Idx 3 4 2) where
  G := fun x y => (if x = y then mE 0 else 0) + (1 / 2 : ℂ)
  M := fun x y => if x = y then mE 0 else 0
  S := lwSmat 3 4 2 (1 / 2) (1 / 2)
  Sp := lwSpOf 3 4 2 (1 / 2) (1 / 2) (mE 0)

theorem auxGraph_instD_hM : ∀ x y, auxGraph_instD.M x y = if x = y then mE 0 else 0 := fun _ _ => rfl

theorem auxGraph_instD_hG : ∀ x y, x ≠ y → ‖auxGraph_instD.G x y‖ ≤ 1 / 2 := by
  intro x y hxy
  simp [auxGraph_instD, hxy]

theorem auxGraph_instD_hGd : ∀ x, ‖auxGraph_instD.G x x - mE 0‖ ≤ 1 / 2 := by
  intro x
  simp [auxGraph_instD]

/-- The window `W^{-d/2} ≤ Ψ` at `W = 2`, `d = 3`, `Ψ = 1/2`. -/
theorem auxGraph_inst_window : ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ 1 / 2 := by
  have h1 : ((2 : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ ((2 : ℕ) : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rw [Real.rpow_neg_one] at h1
  norm_num at h1 ⊢
  exact h1

end Instances

section Instances2

theorem auxGraph_figGraph_molSolid : figGraph.molSolid.length = 6 := by
  rw [auxGraph_molSolid_length]; decide +kernel

theorem auxGraph_inst_Q_molSolid : localReg2_inst_Q.molSolid.length = 4 := by
  rw [auxGraph_molSolid_length]; decide +kernel

theorem auxGraph_inst_Q_counters :
    localReg2_inst_Q.nS = 4 ∧ localReg2_inst_Q.nW = 1 ∧ localReg2_inst_Q.nV = 2 ∧ localReg2_inst_Q.nM = 1 := by
  decide

/-- **Instance of target 2** at `figGraph` (`n_S, n_W, n_V, n_M, |𝒢_ℳ| = 8, 4, 6, 2, 6`: `ord = 4`, `ord(Γ^aux) = 2`) and at `localReg2_inst_Q`
(`4, 1, 2, 1, 4`: `ord = ord(Γ^aux) = 2`, the equality case). -/
example : figGraph.auxOrd = 2 ∧ figGraph.scalingOrder = 4 ∧ figGraph.auxOrd ≤ figGraph.scalingOrder ∧
    figGraph.scalingOrder - figGraph.auxOrd =
      ((figGraph.nS : ℤ) - (figGraph.molSolid.length : ℤ)) + 2 * ((figGraph.nW : ℤ) - (figGraph.nV : ℤ) + (figGraph.nM : ℤ)) ∧
    figGraph.molSolid.length ≤ figGraph.nS ∧
    localReg2_inst_Q.auxOrd = 2 ∧ localReg2_inst_Q.scalingOrder = 2 ∧
    localReg2_inst_Q.auxOrd ≤ localReg2_inst_Q.scalingOrder := by
  have h1 := figGraph_counters
  have h2 := auxGraph_inst_Q_counters
  refine ⟨?_, ?_, figGraph.auxOrd_le_scalingOrder (by decide), figGraph.scalingOrder_sub_auxOrd,
    figGraph.molSolid_length_le, ?_, ?_, localReg2_inst_Q.auxOrd_le_scalingOrder (by decide)⟩
  · unfold LGraph.auxOrd; rw [auxGraph_figGraph_molSolid, h1.2.2.2]; simp [ord]
  · unfold LGraph.scalingOrder LGraph.counters; rw [h1.1, h1.2.1, h1.2.2.1, h1.2.2.2]; simp [ord]
  · unfold LGraph.auxOrd; rw [auxGraph_inst_Q_molSolid, h2.2.2.2]; simp [ord]
  · unfold LGraph.scalingOrder LGraph.counters; rw [h2.1, h2.2.1, h2.2.2.1, h2.2.2.2]; simp [ord]

end Instances2

section Instances3

theorem auxGraph_figGraph_hext : ∀ a b : Fin 2, figGraph.molOf (Sum.inl a) = figGraph.molOf (Sum.inl b) → a = b := by
  have h : ∀ a b : Fin 2, (Sum.inl b : Fin 2 ⊕ Fin 6) ∈ figGraph.mol (Sum.inl a) → a = b := by decide +kernel
  intro a b hab
  exact h a b ((figGraph.molOf_eq_iff _ _).1 hab)

/-- The value of the auxiliary graph of `figGraph` at `ξ ≡ 1/2` and the block labels of `lwSizeEll`: `64² · 2^{-6} = 64`. -/
theorem auxGraph_figGraph_auxVal :
    figGraph.auxVal (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1) = 64 := by
  rw [auxGraph_auxVal_const, auxGraph_figGraph_molSolid, (figGraph_counters).2.2.2, card_Zd]
  norm_num

/-- **Instance of target 3 (`lwGtoAG_holds`)** at `figGraph` (`n_S, n_W, n_V, n_M = 8, 4, 6, 2`), `d = 3`, `L = 4`, `W = 2`, the data
`G = m(0) I + (1/2) J`, `Ψ = 1/2`, `r = 1`, `R = 8 = |E ⊕ I| r`, `ξ ≡ 1/2`, the labels `lwSizeEll`: every hypothesis is discharged
(the decay `(C, c)` is the merged `lwSpOf_decay_E`), the main term has `Γ^aux = 64`. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    figGraph.auxVal (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1) = 64 ∧
    ‖figGraph.val auxGraph_instD lwSizeEll‖ ≤
      figGraph.sizeConst C (C * expC (3 - 2) c) * (1 / 2 : ℝ) ^ (figGraph.scalingOrder - figGraph.auxOrd) *
          ((((2 : ℕ) : ℝ) ^ 3) ^ figGraph.nM *
            figGraph.auxVal (fun _ _ => (1 / 2 : ℝ)) (fun a => (split 3 4 2 (lwSizeEll a)).1)) +
        Real.exp (-(c * 1 / 2)) * figGraph.sizeConst C (C * expC (3 - 2) (c / 2)) *
          figGraph.scalingSize (1 / 2) 2 3 4 := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨h1, h2⟩ := h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C, c, hC, hc, auxGraph_figGraph_auxVal, ?_⟩
  exact lwGtoAG_holds 3 le_rfl 4 2 figGraph (by decide) auxGraph_figGraph_hext auxGraph_instD (mE 0) (1 / 2) C c 1 8
    (fun _ _ => 1 / 2) auxGraph_instD_hM auxGraph_instD_hG auxGraph_instD_hGd hC.le hc h1 h2 auxGraph_inst_window
    (by norm_num) (by simp) (fun _ _ => by norm_num)
    (fun x y a b hxy _ _ => (auxGraph_instD_hG x y hxy)) lwSizeEll

end Instances3

section Instances4

/-- A normal graph with two external vertices in one molecule (`target 4`): the solid edges `G_{xy}`, `Ḡ_{xy}`, the coloured waved edge
`S^+_{xy}`, one `×`-dotted edge `x ≠ y`, coefficient `1`. -/
def auxGraph_instXY : LGraph (Fin 2) (Fin 0) where
  solid := [⟨true, false, .inl 0, .inl 1⟩, ⟨false, false, .inl 0, .inl 1⟩]
  waved := [⟨true, true, .inl 0, .inl 1⟩]
  dotted := [⟨false, .inl 0, .inl 1⟩]
  coeff := 1

theorem auxGraph_instXY_normal : auxGraph_instXY.Normal := by decide

theorem auxGraph_instXY_mol : auxGraph_instXY.molOf (Sum.inl 0) = auxGraph_instXY.molOf (Sum.inl 1) :=
  (auxGraph_instXY.molOf_eq_iff _ _).2 (by decide +kernel)

/-- The labels of the target-4 instance: the blocks `(0,0,0)` and `(2,2,2)` of `Z_4^3`, at block distance `6`. -/
def auxGraph_instEll : Fin 2 → Idx 3 4 2 := ![0, fun _ => 4]

theorem auxGraph_instEll_dist : lwBdist 3 4 2 (auxGraph_instEll 0) (auxGraph_instEll 1) = 6 := by
  decide +kernel

/-- **Instance of target 4 (`lwScalemole_holds`)** at `auxGraph_instXY` (`x`, `y` in one molecule, `|E ⊕ I| = 2`), `r = 1`, the labels at block
distance `6 > 2`, the data `auxGraph_instD`: every hypothesis is discharged. -/
example : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ (Fintype.card (Fin 2 ⊕ Fin 0) : ℝ) * 1 < 6 ∧
    ‖auxGraph_instXY.val auxGraph_instD auxGraph_instEll‖ ≤
      Real.exp (-(c * 1 / 2)) * auxGraph_instXY.sizeConst C (C * expC (3 - 2) (c / 2)) *
        auxGraph_instXY.scalingSize (1 / 2) 2 3 4 := by
  obtain ⟨C, c, hC, hc, h⟩ := lwSpOf_decay_E 3 le_rfl 1 (1 / 2) one_pos (by norm_num)
  obtain ⟨h1, h2⟩ := h 4 2 (by norm_num) (1 / 2) (1 / 2) 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hfar : (Fintype.card (Fin 2 ⊕ Fin 0) : ℝ) * 1 < (lwBdist 3 4 2 (auxGraph_instEll 0) (auxGraph_instEll 1) : ℝ) := by
    rw [auxGraph_instEll_dist]; norm_num
  refine ⟨C, c, hC, hc, by norm_num, ?_⟩
  exact lwScalemole_holds 3 le_rfl 4 2 auxGraph_instXY auxGraph_instXY_normal auxGraph_instD (mE 0) (1 / 2) C c 1
    auxGraph_instD_hM auxGraph_instD_hG auxGraph_instD_hGd hC.le hc h1 h2 (by norm_num) auxGraph_instEll 0 1
    auxGraph_instXY_mol hfar

end Instances4

section Instances5

theorem auxGraph_inst_Q_hxy :
    localReg2_inst_Q.pack.g.molOf (Sum.inl (localReg2_inst_Q.pack.ext 0)) ≠
      localReg2_inst_Q.pack.g.molOf (Sum.inl (localReg2_inst_Q.pack.ext 1)) := by
  intro h
  have hisoX : ∀ w, localReg2_inst_Q.adj (Sum.inl 0) w = false := by decide
  have h' : localReg2_inst_Q.molOf (Sum.inl 0) = localReg2_inst_Q.molOf (Sum.inl 1) := h
  have := localReg2_inst_Q.localReg_molOf_isolated (Sum.inl 0) hisoX (Sum.inl 1) h'
  simp at this

theorem auxGraph_inst_Q_auxOrd : localReg2_inst_Q.auxOrd = 2 := by
  have h2 := auxGraph_inst_Q_counters
  unfold LGraph.auxOrd; rw [auxGraph_inst_Q_molSolid, h2.2.2.2]; simp [ord]

/-- **Instance of target 5 (`lwAuxNested_holds`)** at `localReg2_inst_Q.pack` (`p = 2`, one internal molecule, `q = n_M = 1 ≤ 2`): the nested graph
has no ghost edge, `IsNested`, `ordN = 2`, and its value at the constant edge variable `ξ ≡ 1/2` on `Z_4^3` is `64 · (1/2)^4 = 4`. -/
example : ∃ Γa : NGraph 2 localReg2_inst_Q.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = 2 ∧ localReg2_inst_Q.nM ≤ 2 ∧
    Γa.val (fun _ _ => (1 / 2 : ℝ)) (fun _ => (0 : Zd 3 4)) (fun _ => 0) = 4 := by
  obtain ⟨Γa, h1, h2, h3, h4⟩ := lwAuxNested_holds 2 localReg2_inst_Q.pack (by norm_num) localReg2_inst_Q_locReg345
    auxGraph_inst_Q_hxy
  refine ⟨Γa, h1, h2, h3.trans auxGraph_inst_Q_auxOrd, by rw [auxGraph_inst_Q_counters.2.2.2]; norm_num, ?_⟩
  have := h4 (κ := Zd 3 4) (fun _ _ => (1 / 2 : ℝ)) (fun _ _ => rfl) (fun _ => (0 : Zd 3 4))
  refine this.trans ?_
  rw [auxGraph_auxVal_const]
  change ((Fintype.card (Zd 3 4) : ℝ)) ^ localReg2_inst_Q.nM * (1 / 2 : ℝ) ^ localReg2_inst_Q.molSolid.length = 4
  rw [auxGraph_inst_Q_molSolid, auxGraph_inst_Q_counters.2.2.2, card_Zd]
  norm_num

/-- **The consumer chain at `p = 2`** (`lw_localregular_upto5 2 (m(0)) (1/4) _ 1 3 10`, as `localReg2_inst_expansion`): every output is a normal graph (the
hypothesis of targets 3 and 4); every output with `𝓜_x ≠ 𝓜_y` has distinct external vertices in distinct molecules (the hypothesis `hext` of
target 3) and a nested graph `Γa` of target 5 (the input of `LWAnp`). -/
example : ∃ outs : List (PGraph (Fin 2)),
    ∀ Q ∈ outs, Q.g.Normal ∧ 2 ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ 2 ∧
      (Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
        (∀ a b : Q.E', Q.g.molOf (Sum.inl a) = Q.g.molOf (Sum.inl b) → a = b) ∧
        ∃ Γa : NGraph 2 Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = Q.g.auxOrd) := by
  obtain ⟨outs, errs, h1, h2, h3, h4⟩ := localReg2_inst_expansion
  refine ⟨outs, fun Q hQ => ⟨(h1 Q hQ).1.1, (h1 Q hQ).2, (h4 Q hQ).2.1.1, fun hxy => ⟨auxGraph_ext_inj hxy, ?_⟩⟩⟩
  obtain ⟨Γa, ha1, ha2, ha3, -⟩ := lwAuxNested_holds 2 Q (by norm_num) (h4 Q hQ).2.2 hxy
  exact ⟨Γa, ha1, ha2, ha3⟩

end Instances5

end RBM.Graph

end
