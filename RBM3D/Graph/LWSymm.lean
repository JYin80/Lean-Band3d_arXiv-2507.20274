/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWVocab
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWWeightExp
import RBM3D.Graph.LWEdgeExp
import RBM3D.Graph.LWGGExp
import RBM3D.Gauss.FineModel
import RBM3D.Green.IBPPoly

/-!
# LW-08a: conjugation, transposition and `(Owx)` at an external vertex (T2131)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:290-345` (cited `7_8:line`): the expansions `(Owx)`, `(Oe1x)`,
`(Oe2x)`, with "the edge expansions with respect to `Ḡ_{xy'_i}`, `G_{w_i x}`, `Ḡ_{w'_i x}` can be defined similarly by taking
complex conjugates or matrix transpositions" (`7_8:329`) and "the `Ḡ Ḡ` expansion ... by taking the complex conjugate"
(`7_8:341`); `paper/tex/B_graphical_lemmas.tex:135-170` (`strat_local`).  Design: T2040 (split row LW-08), the missing inputs
found by the T2128 preflight (`docs/reports/T2128-prove.md` (a), rows C1-C4; DECISIONS §38).

## Contents (namespace `RBM.Graph`)

1. **(S1) Conjugation** (`§1`, `§2`): `LGraph.conj` (flip `σ` of every solid edge, `S^+_{xy} ↦ S^-_{yx}` on coloured waved edges,
   `m ↦ m̄`), `LGraph.val_conj : Γ.conj.val D ℓe = conj (Γ.val D ℓe)` for data with real `S` (the *same* `D`; the literal
   reading with the conjugate data is false, `lwSymm_conj_literal_false`), `lwSymm_conj_integral` (in expectation, `lwS` is real).
2. **(S2) Transposition** (`§2`, `§3`): `LGraph.transpose` (swap `src`/`dst` of every solid and waved edge),
   `LGraph.val_transpose : Γᵀ.val D = Γ.val Dᵀ`; the flip `lwSymmFlip` of the imaginary-part coordinates (`b = false`) preserves
   `seqP` (`lwSymm_flip_measurePreserving`) and gives `G(ω') = G(ω)ᵀ` (`lwSymm_lwGm_flip`); `lwSymm_transpose_integral :
   E Γᵀ.val = E Γ.val` for symmetric `M`, `S`, `S⁺`.  The twist `(c, t)` (`lwSymmTwistG`: conjugate if `c`, transpose if `t`) and
   `lwSymm_twist_integral : E (Γ^{(c,t)}).val = (conj if c) E Γ.val`; every twist keeps the counters (`lwSymmTwistG_counters`).
3. **(S3) `(Owx)` at any vertex of `E ⊕ I`** (`§4`): `owxET1 .. owxET4` (the terms of `owxT1 .. owxT4` at `x : E ⊕ I`), `owxE_term_integral`,
   `owxE_graph_E` (the identity of expectations of values; for `x = inl a` the label `ℓe a` is fixed), `owxET*_counters`,
   `owxET*_ord` (`n_M` unchanged for an external `x`).
4. **The forms for `strat_local`** (`§5`): `lwSymm_weight_graph_E` (a red or blue light-weight, internal or external),
   `lwSymm_oe1x_graph_E` (`(Oe1x)` at an edge of any colour and direction at an internal vertex), `lwSymm_oe2x_graph_E` (`(Oe2x)` at
   `G_{xy} G_{y'x}`, `Ḡ_{xy} Ḡ_{y'x}` and the transposed pairs), each with the counters and `ord` of every term
   (`lwSymm_weight_counters`, `lwSymm_oe1x_counters`, `lwSymm_oe2x_counters`).  All three have the one shape: the merged expansion
   of the *frame* `Γ' = (Γ with the selected edge uncircled)^{(c,t)}`, every output twisted back; the selector `(c, t)` makes the
   twisted selected edge the blue out-edge (`lwSymm_twist_out`, `lwSymm_twist_in`, `lwSymm_twist_pair_in`,
   `lwSymm_twist_pair_out`, `lwSymm_twist_weight`).
5. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2` (`§6`).

## Hypotheses

Those of the merged `owx_graph_E`, `oe1x_graph_E`, `oe2x_graph_E` (`GaussIBP` is the proved `gaussIBP`; `Im z > 0`, `u > 0`,
`m ≠ 0`, `z + u m = -m⁻¹`, `S⁺ (1 - m² S) = S`, `M_{aa} = m`) plus `M a b = 0` for `a ≠ b` (a circled selected edge, T2128 (a) C4)
and `S⁺ᵀ = S⁺` (`lwSymm_lwSplus_symm` proves it for `S⁺ = lwSplus`).  A circled selected non-loop edge `(G - M)_{xy}` is replaced by
`G_{xy}` on the support of a `×`-dotted edge between its ends (`lwSymmUncirc_val`); this is the hypothesis `hX`, which every normal
graph satisfies (`lwSymm_hX_of_normal`).

## Differences from the ticket's wording (delta candidates)

* `T2131a`: the flip negates the imaginary parts `(i, j, false)` (`Xentry`, `Gauss/FineModel.lean:105-109`); the ticket's
  `(if b then -1 else 1)` negates the real parts and gives `X(ω') = -X(ω)ᵀ` (`lwSymm_Xentry_flipLit`, `lwSymm_flipLit_ne`).
* `T2131b`: `Γ.conj.val D = conj (Γ.val D)` with the same `D`; the literal `Γ.conj.val D.conj` is false.
* `T2131c`: `WEdge.conj` swaps the ends of a coloured waved edge (`conj S^+_{xy} = S^-_{yx}`, `WEdge.val`).
* `T2131d`: `(Owx)` is stated for any vertex `x : E ⊕ I`; `owxT1 .. owxT4` are its internal instances (`owxET*_inr`).
* `T2131e`: circled non-loop selected edges (C4) by `M a b = 0` and `×`-dotted support, not by cancelling the `m δ_{xy}` term.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-! ## 1. Conjugation and transposition of graphs -/

section Twist

variable {V E I ι : Type*}

/-- Conjugate of a solid edge: the colour flips (`G_{xy} ↔ Ḡ_{xy}`), the circle and the ends stay. -/
def SEdge.conj (e : SEdge V) : SEdge V := ⟨!e.σ, e.circ, e.src, e.dst⟩

/-- Transpose of a solid edge: the ends swap (`G_{xy} ↦ G_{yx}`), the colour and the circle stay. -/
def SEdge.transpose (e : SEdge V) : SEdge V := ⟨e.σ, e.circ, e.dst, e.src⟩

/-- Conjugate of a waved edge: a coloured edge `S^+_{xy}` becomes `S^-_{yx}` (colour flips and the ends swap, since
`conj S^+_{xy} = S^-_{yx}`, `WEdge.val`); a black edge `S_{xy}` stays (`S` is real). -/
def WEdge.conj (e : WEdge V) : WEdge V := if e.col then ⟨true, !e.σ, e.y, e.x⟩ else e

/-- Transpose of a waved edge: the ends swap, colour and kind stay. -/
def WEdge.transpose (e : WEdge V) : WEdge V := ⟨e.col, e.σ, e.y, e.x⟩

/-- **(S1) The conjugate of a graph**: `σ` of every solid edge flips, `S^+ ↔ S^-` on coloured waved edges,
the coefficient `m ↦ m̄`; dotted edges stay. -/
def LGraph.conj (Γ : LGraph E I) : LGraph E I where
  solid := Γ.solid.map SEdge.conj
  waved := Γ.waved.map WEdge.conj
  dotted := Γ.dotted
  coeff := star Γ.coeff

/-- **The transpose of a graph** (`G ↦ Gᵀ`): `src` and `dst` of every solid and waved edge swap. -/
def LGraph.transpose (Γ : LGraph E I) : LGraph E I where
  solid := Γ.solid.map SEdge.transpose
  waved := Γ.waved.map WEdge.transpose
  dotted := Γ.dotted
  coeff := Γ.coeff

/-- The transposed data `(Gᵀ, Mᵀ, Sᵀ, S⁺ᵀ)`. -/
def LData.transpose (D : LData ι) : LData ι := ⟨D.Gᵀ, D.Mᵀ, D.Sᵀ, D.Spᵀ⟩

theorem lwSymm_sedge_conj_conj (e : SEdge V) : e.conj.conj = e := by
  cases e; simp [SEdge.conj]

theorem lwSymm_sedge_tr_tr (e : SEdge V) : e.transpose.transpose = e := by
  cases e; simp [SEdge.transpose]

theorem lwSymm_sedge_conj_tr (e : SEdge V) : e.conj.transpose = e.transpose.conj := by
  cases e; simp [SEdge.conj, SEdge.transpose]

theorem lwSymm_wedge_conj_conj (e : WEdge V) : e.conj.conj = e := by
  cases e with | mk col σ x y => cases col <;> simp [WEdge.conj]

theorem lwSymm_wedge_tr_tr (e : WEdge V) : e.transpose.transpose = e := by
  cases e; simp [WEdge.transpose]

theorem lwSymm_wedge_conj_tr (e : WEdge V) : e.conj.transpose = e.transpose.conj := by
  cases e with | mk col σ x y => cases col <;> simp [WEdge.conj, WEdge.transpose]

theorem lwSymm_conj_conj (Γ : LGraph E I) : Γ.conj.conj = Γ := by
  cases Γ with | mk s w d c =>
  simp only [LGraph.conj, List.map_map, star_star]
  congr 1
  · conv_rhs => rw [← List.map_id s]
    exact List.map_congr_left fun e _ => lwSymm_sedge_conj_conj e
  · conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left fun e _ => lwSymm_wedge_conj_conj e

theorem lwSymm_transpose_transpose (Γ : LGraph E I) : Γ.transpose.transpose = Γ := by
  cases Γ with | mk s w d c =>
  simp only [LGraph.transpose, List.map_map]
  congr 1
  · conv_rhs => rw [← List.map_id s]
    exact List.map_congr_left fun e _ => lwSymm_sedge_tr_tr e
  · conv_rhs => rw [← List.map_id w]
    exact List.map_congr_left fun e _ => lwSymm_wedge_tr_tr e

theorem lwSymm_conj_transpose (Γ : LGraph E I) : Γ.conj.transpose = Γ.transpose.conj := by
  cases Γ with | mk s w d c =>
  have hs : (s.map SEdge.conj).map SEdge.transpose = (s.map SEdge.transpose).map SEdge.conj := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_sedge_conj_tr e
  have hw : (w.map WEdge.conj).map WEdge.transpose = (w.map WEdge.transpose).map WEdge.conj := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_wedge_conj_tr e
  simp only [LGraph.conj, LGraph.transpose, hs, hw]


/-- The real or complex-conjugate part `c`: `z ↦ z̄` if `c`, the identity otherwise. -/
def lwSymmCj (c : Bool) : ℂ →+* ℂ := cond c (starRingEnd ℂ) (RingHom.id ℂ)

/-- The twist of a solid edge by `(c, t)`: conjugate (`c`) and transpose (`t`); the two commute. -/
def lwSymmTwistS (c t : Bool) (e : SEdge V) : SEdge V :=
  cond c (cond t e.transpose.conj e.conj) (cond t e.transpose e)

/-- The twist of a graph by `(c, t)`: conjugate if `c`, transpose if `t` (they commute). -/
def lwSymmTwistG (c t : Bool) (Γ : LGraph E I) : LGraph E I :=
  cond c (cond t Γ.transpose.conj Γ.conj) (cond t Γ.transpose Γ)

/-- The twist of a pair (an edge and the other edges). -/
def lwSymmTwistP (c t : Bool) (p : SEdge V × List (SEdge V)) : SEdge V × List (SEdge V) :=
  (lwSymmTwistS c t p.1, p.2.map (lwSymmTwistS c t))

theorem lwSymmTwistS_invol (c t : Bool) (e : SEdge V) : lwSymmTwistS c t (lwSymmTwistS c t e) = e := by
  cases c <;> cases t <;> simp [lwSymmTwistS, lwSymm_sedge_conj_conj, lwSymm_sedge_tr_tr, lwSymm_sedge_conj_tr]

theorem lwSymmTwistG_invol (c t : Bool) (Γ : LGraph E I) :
    lwSymmTwistG c t (lwSymmTwistG c t Γ) = Γ := by
  cases c <;> cases t <;>
    simp [lwSymmTwistG, lwSymm_conj_conj, lwSymm_transpose_transpose, lwSymm_conj_transpose]

theorem lwSymmTwistG_solid (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).solid = Γ.solid.map (lwSymmTwistS c t) := by
  cases c <;> cases t
  · exact (List.map_id _).symm
  all_goals simp [lwSymmTwistG, lwSymmTwistS, LGraph.conj, LGraph.transpose, Function.comp_def]

theorem lwSymmTwistG_dotted (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).dotted = Γ.dotted := by
  cases c <;> cases t <;> simp [lwSymmTwistG, LGraph.conj, LGraph.transpose]

theorem lwSymmTwistG_coeff (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).coeff = lwSymmCj c Γ.coeff := by
  cases c <;> cases t <;> simp [lwSymmTwistG, lwSymmCj, LGraph.conj, LGraph.transpose]


/-! ### The values -/

variable [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem lwSymm_sedge_val_conj (D : LData ι) (ℓ : V → ι) (e : SEdge V) :
    SEdge.val D ℓ e.conj = star (SEdge.val D ℓ e) := by
  cases hσ : e.σ <;> simp [SEdge.val, SEdge.conj, hσ]

theorem lwSymm_sedge_val_tr (D : LData ι) (ℓ : V → ι) (e : SEdge V) :
    SEdge.val D ℓ e.transpose = SEdge.val D.transpose ℓ e := rfl

/-- Conjugation of a waved edge: the coloured edges read `S^+`, `S^-` with `S^-_{xy} = conj S^+_{yx}`, and the black edges
`S` need `S` real. -/
theorem lwSymm_wedge_val_conj (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (ℓ : V → ι) (e : WEdge V) :
    WEdge.val D ℓ e.conj = star (WEdge.val D ℓ e) := by
  cases hc : e.col
  · simp [WEdge.val, WEdge.conj, hc, hS]
  · cases hσ : e.σ <;> simp [WEdge.val, WEdge.conj, hc, hσ]

theorem lwSymm_wedge_val_tr (D : LData ι) (ℓ : V → ι) (e : WEdge V) :
    WEdge.val D ℓ e.transpose = WEdge.val D.transpose ℓ e := by
  cases hc : e.col <;> cases hσ : e.σ <;> simp [WEdge.val, WEdge.transpose, LData.transpose, hc, hσ]

theorem lwSymm_dedge_val_star (ℓ : V → ι) (e : DEdge V) : star (DEdge.val ℓ e) = DEdge.val ℓ e := by
  unfold DEdge.val
  split_ifs <;> simp

private theorem lwSymm_star_listProd (l : List ℂ) : star l.prod = (l.map star).prod := by
  have := map_list_prod (starRingEnd ℂ) l
  simpa [Complex.star_def] using this

theorem lwSymm_term_conj (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (Γ : LGraph E I)
    (ℓ : E ⊕ I → ι) : Γ.conj.term D ℓ = star (Γ.term D ℓ) := by
  have h1 : ((Γ.solid.map SEdge.conj).map (SEdge.val D ℓ)) = (Γ.solid.map (SEdge.val D ℓ)).map star := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_sedge_val_conj D ℓ e
  have h2 : ((Γ.waved.map WEdge.conj).map (WEdge.val D ℓ)) = (Γ.waved.map (WEdge.val D ℓ)).map star := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_wedge_val_conj D hS ℓ e
  have h3 : (Γ.dotted.map (DEdge.val ℓ)) = (Γ.dotted.map (DEdge.val ℓ)).map star := by
    rw [List.map_map]
    exact (List.map_congr_left fun e _ => (lwSymm_dedge_val_star ℓ e).symm)
  simp only [LGraph.term, LGraph.conj, h1, h2, star_mul', lwSymm_star_listProd]
  rw [← h3]

theorem lwSymm_term_transpose (D : LData ι) (Γ : LGraph E I) (ℓ : E ⊕ I → ι) :
    Γ.transpose.term D ℓ = Γ.term D.transpose ℓ := by
  have h1 : ((Γ.solid.map SEdge.transpose).map (SEdge.val D ℓ)) = Γ.solid.map (SEdge.val D.transpose ℓ) := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_sedge_val_tr D ℓ e
  have h2 : ((Γ.waved.map WEdge.transpose).map (WEdge.val D ℓ)) = Γ.waved.map (WEdge.val D.transpose ℓ) := by
    simp only [List.map_map]
    exact List.map_congr_left fun e _ => lwSymm_wedge_val_tr D ℓ e
  simp only [LGraph.term, LGraph.transpose, h1, h2]

/-- **(S1) Conjugation of graphs.**  For data with a real variance matrix `S` (true for `lwS`; nothing is asked of `S⁺`),
`conj (Γ.val D ℓe) = Γ.conj.val D ℓe` -- the *same* data `D`: the conjugate graph reads `Ḡ` from `G` through the flipped `σ`
(the literal reading with the conjugate data `(Ḡ, M̄, S, S⁺)` is false, `lwSymm_conj_literal_false` below). -/
theorem LGraph.val_conj (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (Γ : LGraph E I)
    (ℓe : E → ι) : Γ.conj.val D ℓe = star (Γ.val D ℓe) := by
  simp only [LGraph.val, star_sum, lwSymm_term_conj D hS]

/-- **(S2), algebra**: `Γᵀ.val D = Γ.val Dᵀ`, any data. -/
theorem LGraph.val_transpose (D : LData ι) (Γ : LGraph E I) (ℓe : E → ι) :
    Γ.transpose.val D ℓe = Γ.val D.transpose ℓe := by
  simp only [LGraph.val, lwSymm_term_transpose]

/-! ### The four twists -/

/-- The data of `D` transposed or not. -/
def lwSymmDataTr (D : LData ι) (t : Bool) : LData ι := cond t D.transpose D

/-- **The value of a twist**: `Γ^{(c,t)}.val D = (conj if c) (Γ.val (D transposed if t))`. -/
theorem lwSymmTwistG_val (D : LData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (c t : Bool)
    (Γ : LGraph E I) (ℓe : E → ι) :
    (lwSymmTwistG c t Γ).val D ℓe = lwSymmCj c (Γ.val (lwSymmDataTr D t) ℓe) := by
  have hT : ∀ i j, star (D.transpose.S i j) = D.transpose.S i j := fun i j => hS j i
  cases c <;> cases t
  · rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, LGraph.val_transpose]
    rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, Bool.cond_false, LGraph.val_conj D hS]
    rfl
  · simp only [lwSymmTwistG, lwSymmCj, lwSymmDataTr, Bool.cond_true, LGraph.val_conj D hS, LGraph.val_transpose]
    rfl


/-! ### The counters are twist invariant -/

section TwistCounters

variable {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The molecule counter only reads the adjacency relation of the waved and `=`-dotted edges. -/
theorem lwSymm_nM_of_adj (Γ₁ Γ₂ : LGraph E I) (h : Γ₁.adj = Γ₂.adj) : Γ₁.nM = Γ₂.nM := by
  have hstep : Γ₁.step = Γ₂.step := by
    funext s
    simp only [LGraph.step, h]
  have hmol : Γ₁.mol = Γ₂.mol := by
    funext v
    simp only [LGraph.mol, hstep]
  simp only [LGraph.nM, hmol]

theorem lwSymm_adj_conj (Γ : LGraph E I) : Γ.conj.adj = Γ.adj := by
  funext u v
  have hw : ∀ e : WEdge (E ⊕ I), decide (((WEdge.conj e).x = u ∧ (WEdge.conj e).y = v) ∨
      ((WEdge.conj e).x = v ∧ (WEdge.conj e).y = u)) =
      decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    intro e
    rw [decide_eq_decide]
    cases hc : e.col
    · simp [WEdge.conj, hc]
    · simp only [WEdge.conj, hc, ↓reduceIte]
      tauto
  simp only [LGraph.adj, LGraph.conj, List.any_map, Function.comp_def, hw]

theorem lwSymm_adj_transpose (Γ : LGraph E I) : Γ.transpose.adj = Γ.adj := by
  funext u v
  have hw : ∀ e : WEdge (E ⊕ I), decide (((WEdge.transpose e).x = u ∧ (WEdge.transpose e).y = v) ∨
      ((WEdge.transpose e).x = v ∧ (WEdge.transpose e).y = u)) =
      decide ((e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) := by
    intro e
    rw [decide_eq_decide]
    simp only [WEdge.transpose]
    tauto
  simp only [LGraph.adj, LGraph.transpose, List.any_map, Function.comp_def, hw]

theorem lwSymmTwistG_adj (c t : Bool) (Γ : LGraph E I) : (lwSymmTwistG c t Γ).adj = Γ.adj := by
  cases c <;> cases t <;>
    simp [lwSymmTwistG, lwSymm_adj_conj, lwSymm_adj_transpose]

/-- **The twist keeps the four counters** `(n_S, n_W, n_V, n_M)`. -/
theorem lwSymmTwistG_counters (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).nS = Γ.nS ∧ (lwSymmTwistG c t Γ).nW = Γ.nW ∧
      (lwSymmTwistG c t Γ).nV = Γ.nV ∧ (lwSymmTwistG c t Γ).nM = Γ.nM := by
  refine ⟨?_, ?_, rfl, lwSymm_nM_of_adj _ _ (lwSymmTwistG_adj c t Γ)⟩
  · simp only [LGraph.nS, lwSymmTwistG_solid, List.length_map]
  · cases c <;> cases t <;> simp [LGraph.nW, lwSymmTwistG, LGraph.conj, LGraph.transpose]

theorem lwSymmTwistG_counters_eq (c t : Bool) (Γ : LGraph E I) :
    (lwSymmTwistG c t Γ).counters = Γ.counters := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmTwistG_counters c t Γ
  simp only [LGraph.counters, h1, h2, h3, h4]

/-- `ord` is twist invariant. -/
theorem lwSymmTwistG_ord (c t : Bool) (Γ : LGraph E I) :
    ord (lwSymmTwistG c t Γ).counters = ord Γ.counters := by
  rw [lwSymmTwistG_counters_eq]

end TwistCounters

end Twist

/-! ## 2. (S2) The flip of the imaginary parts

The coordinate `(i, j, b)` of `CoordF` carries the real part of `X_{ij}` for `b = true` and the imaginary part for
`b = false` (`Xentry`, `Gauss/FineModel.lean:105-109`: `ω (i, j, true) + I ω (i, j, false)`).  The flip negates the
coordinates with `b = false`: `X(ω') = X(ω)ᵀ`.  (The ticket's formula `(if b then -1 else 1)` negates the real part:
then `X(ω') = -X(ω)ᵀ`, not the transpose; delta candidate `T2131a`.) -/

section Flip

variable {d : ℕ}

/-- The sign of a coordinate: `-1` on the imaginary parts (`b = false`), `1` on the real parts. -/
def lwSymmSgn (b : Bool) : ℝ := if b then 1 else -1

/-- The flip on one size: the imaginary parts are negated. -/
def lwSymmFlipF (L W : ℕ) (ω : Ω d L W) : Ω d L W := fun c => lwSymmSgn c.2.2 * ω c

/-- The flip on the common sample space (all sizes): the imaginary parts are negated. -/
def lwSymmFlip (sz : Sizes d) (ω : Sizes.SeqΩ sz) : Sizes.SeqΩ sz := fun c => lwSymmSgn c.2.2.2 * ω c

theorem lwSymmSgn_mul_self (b : Bool) : lwSymmSgn b * lwSymmSgn b = 1 := by
  cases b <;> simp [lwSymmSgn]

theorem lwSymmFlip_invol (sz : Sizes d) (ω : Sizes.SeqΩ sz) : lwSymmFlip sz (lwSymmFlip sz ω) = ω := by
  funext c
  simp only [lwSymmFlip, ← mul_assoc, lwSymmSgn_mul_self, one_mul]

/-- The flipped coordinates give the transposed matrix: `X(ω')_{ij} = X(ω)_{ji}`. -/
theorem lwSymm_Xentry_flip (L W : ℕ) [NeZero L] [NeZero W] (ω : Ω d L W) (i j : Idx d L W) :
    Xentry d L W (lwSymmFlipF L W ω) i j = Xentry d L W ω j i := by
  unfold Xentry
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have h' : ¬ idxKey d L W j < idxKey d L W i := not_lt.mpr h.le
    simp only [h, h', ite_true, ite_false, lwSymmFlipF, lwSymmSgn, Bool.false_eq_true]
    push_cast
    ring
  · subst h
    simp [lwSymmFlipF, lwSymmSgn]
  · have h' : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr h.le
    simp only [h, h', ite_true, ite_false, lwSymmFlipF, lwSymmSgn, Bool.false_eq_true]
    push_cast
    ring

theorem lwSymm_Xmat_flip (L W : ℕ) [NeZero L] [NeZero W] (ω : Ω d L W) :
    Xmat d L W (lwSymmFlipF L W ω) = (Xmat d L W ω)ᵀ := by
  ext i j
  exact lwSymm_Xentry_flip L W ω i j

theorem lwSymm_Gres_transpose {κ : Type*} [Fintype κ] [DecidableEq κ] (H : Matrix κ κ ℂ) (z : ℂ) :
    Gres Hᵀ z true = (Gres H z true)ᵀ := by
  simp only [Gres, ↓reduceIte, ← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv,
    Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]

variable (sz : Sizes d) (n : ℕ)

theorem lwSymm_slice_flip (ω : Sizes.SeqΩ sz) :
    Sizes.slice sz n (lwSymmFlip sz ω) = lwSymmFlipF (sz.L n) (sz.W n) (Sizes.slice sz n ω) := rfl

theorem lwSymm_seqHflow_flip (u : ℝ) (ω : Sizes.SeqΩ sz) :
    sz.seqHflow n u (lwSymmFlip sz ω) = (sz.seqHflow n u ω)ᵀ := by
  simp only [Sizes.seqHflow, Sizes.seqXmat, lwSymm_slice_flip, lwSymm_Xmat_flip, Matrix.transpose_smul]

/-- **`G(ω') = G(ω)ᵀ`** for the resolvent of the flow. -/
theorem lwSymm_lwGm_flip (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ sz) :
    lwGm sz n z u (lwSymmFlip sz ω) = (lwGm sz n z u ω)ᵀ := by
  simp only [lwGm, lwSymm_seqHflow_flip, lwSymm_Gres_transpose]

variable {sz n}

/-- The data at the flipped sample is the transposed data, when `M`, `S`, `S⁺` are symmetric. -/
theorem lwSymm_data_flip {z : ℂ} {u : ℝ} {M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp) (ω : Sizes.SeqΩ sz) :
    (lwSampleData sz n z u M S Sp ω).transpose = lwSampleData sz n z u M S Sp (lwSymmFlip sz ω) := by
  simp only [LData.transpose, lwSampleData, lwSymm_lwGm_flip, hM, hS, hSp]

/-- The flip as a measurable involution. -/
def lwSymmFlipEquiv (sz : Sizes d) : Sizes.SeqΩ sz ≃ᵐ Sizes.SeqΩ sz where
  toFun := lwSymmFlip sz
  invFun := lwSymmFlip sz
  left_inv := lwSymmFlip_invol sz
  right_inv := lwSymmFlip_invol sz
  measurable_toFun := Measurable.of_eval fun c => (measurable_pi_apply c).const_mul _
  measurable_invFun := Measurable.of_eval fun c => (measurable_pi_apply c).const_mul _

/-- **The law `seqP` is invariant under the flip of the imaginary parts**: `seqP` is a product of centred Gaussians
(`gaussianReal 0 (seqGvar sz c)`) and a centred Gaussian is symmetric, so negating the coordinates `b = false` preserves it
(the variances `gvarF` do not depend on `b` in this model, but the argument does not use it). -/
theorem lwSymm_flip_measurePreserving (sz : Sizes d) :
    MeasurePreserving (lwSymmFlipEquiv sz) (Sizes.seqP sz) (Sizes.seqP sz) := by
  refine ⟨(lwSymmFlipEquiv sz).measurable, ?_⟩
  have h : ∀ c : Sizes.SeqCoord sz, (gaussianReal 0 (Sizes.seqGvar sz c)).map
      (fun x => lwSymmSgn c.2.2.2 * x) = gaussianReal 0 (Sizes.seqGvar sz c) := by
    intro c
    have key : ∀ b : Bool, (gaussianReal 0 (Sizes.seqGvar sz c)).map (fun x => lwSymmSgn b * x) =
        gaussianReal 0 (Sizes.seqGvar sz c) := by
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
  have hmap := Measure.infinitePi_map_pi (μ := fun c => gaussianReal 0 (Sizes.seqGvar sz c))
    (f := fun c (x : ℝ) => lwSymmSgn c.2.2.2 * x) (fun c => measurable_const.mul measurable_id)
  simp only [h] at hmap
  exact hmap

/-- The integral of a function of the sample is flip invariant. -/
theorem lwSymm_integral_flip (sz : Sizes d) (F : Sizes.SeqΩ sz → ℂ) :
    ∫ ω, F (lwSymmFlip sz ω) ∂(Sizes.seqP sz) = ∫ ω, F ω ∂(Sizes.seqP sz) :=
  (lwSymm_flip_measurePreserving sz).integral_comp' F

end Flip

/-! ### The ticket's literal formulas are false (compiled negations, delta candidates `T2131a`, `T2131b`)

* The flip `ω ↦ (if b then -1 else 1) · ω (i, j, b)` negates the **real** parts: `X(ω') = -X(ω)ᵀ`, not the transpose.
* `conj (Γ.val D ℓe) = Γ.conj.val D.conj ℓe` with the entrywise conjugate data `D.conj = (Ḡ, M̄, S, S⁺)` is false:
  `Γ.conj` already reads `Ḡ` from `G` through the flipped `σ`, so the conjugate data conjugates twice. -/

section Negations

/-- The ticket's flip: the coordinates with `b = true` (the real parts) are negated. -/
def lwSymmFlipLitF {d : ℕ} (L W : ℕ) (ω : Ω d L W) : Ω d L W := fun c => (if c.2.2 then -1 else 1) * ω c

theorem lwSymm_Xentry_flipLit {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (ω : Ω d L W) (i j : Idx d L W) :
    Xentry d L W (lwSymmFlipLitF L W ω) i j = -Xentry d L W ω j i := by
  unfold Xentry
  rcases idxKey_lt_or_eq_or_lt d L W i j with h | h | h
  · have h' : ¬ idxKey d L W j < idxKey d L W i := not_lt.mpr h.le
    simp only [h, h', ite_true, ite_false, lwSymmFlipLitF, Bool.false_eq_true]
    push_cast
    ring
  · subst h
    simp [lwSymmFlipLitF]
  · have h' : ¬ idxKey d L W i < idxKey d L W j := not_lt.mpr h.le
    simp only [h, h', ite_true, ite_false, lwSymmFlipLitF, Bool.false_eq_true]
    push_cast
    ring

/-- **The ticket's flip does not transpose**: at the constant sample `1` the diagonal entry of `X(ω')` is `-1`, that of `X(ω)ᵀ`
is `1`. -/
theorem lwSymm_flipLit_ne {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] :
    ∃ ω : Ω d L W, Xmat d L W (lwSymmFlipLitF L W ω) ≠ (Xmat d L W ω)ᵀ := by
  refine ⟨fun _ => 1, fun h => ?_⟩
  have h1 := congrFun (congrFun h 0) 0
  simp [Xmat, Xentry, lwSymmFlipLitF] at h1
  norm_num at h1

/-- The entrywise conjugate data `(Ḡ, M̄, S, S⁺)`: the ticket's reading of `D.conj`. -/
def lwSymmDataConj {ι : Type*} (D : LData ι) : LData ι := ⟨D.G.map star, D.M.map star, D.S, D.Sp⟩

/-- **The literal `conj (Γ.val D ℓe) = Γ.conj.val D.conj ℓe` is false** (one blue edge `G_{01} = i`: the left side is `-i`, the
right side `i`).  The true statement is `LGraph.val_conj`: the same data `D`. -/
theorem lwSymm_conj_literal_false :
    ¬ (∀ (Γ : LGraph (Fin 2) (Fin 0)) (D : LData (Fin 2)) (ℓe : Fin 2 → Fin 2),
        star (Γ.val D ℓe) = Γ.conj.val (lwSymmDataConj D) ℓe) := by
  intro h
  have := h ⟨[⟨true, false, Sum.inl 0, Sum.inl 1⟩], [], [], 1⟩ ⟨!![0, Complex.I; 0, 0], 0, 0, 0⟩ ![0, 1]
  simp [LGraph.val, LGraph.term, LGraph.conj, SEdge.conj, SEdge.val, lwSymmDataConj] at this
  have h2 := congrArg Complex.im this
  norm_num at h2

end Negations

/-! ## 3. The twists in expectation

For the sample data `lwSampleData sz n z u M S Sp` with `S` real (true for `lwS`), `Mᵀ = M`, `Sᵀ = S`, `S⁺ᵀ = S⁺`
(`M = m I`, `S = lwS`, `S⁺ = S (1 - m² S)⁻¹`): `E (Γᵀ).val = E Γ.val` and `E (Γ.conj).val = conj E Γ.val`. -/

section TwistE

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type*} [Fintype I] [DecidableEq I]
variable {z : ℂ} {u : ℝ} {M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}

/-- **(S2) Transposition invariance in expectation**: `∫ Γᵀ.val = ∫ Γ.val`, for symmetric `M`, `S`, `S⁺`. -/
theorem lwSymm_transpose_integral (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp) (Γ : LGraph E I)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.transpose.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) := by
  simp only [LGraph.val_transpose, lwSymm_data_flip hM hS hSp]
  exact lwSymm_integral_flip sz (fun ω => Γ.val (lwSampleData sz n z u M S Sp ω) ℓe)

/-- **(S1) in expectation**: `∫ Γ.conj.val = conj ∫ Γ.val`, for real `S`. -/
theorem lwSymm_conj_integral (hS : ∀ i j, star (S i j) = S i j) (Γ : LGraph E I)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.conj.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      star (∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz)) := by
  have h : ∀ ω, Γ.conj.val (lwSampleData sz n z u M S Sp ω) ℓe =
      (starRingEnd ℂ) (Γ.val (lwSampleData sz n z u M S Sp ω) ℓe) :=
    fun ω => LGraph.val_conj (lwSampleData sz n z u M S Sp ω) hS Γ ℓe
  simp only [h, Complex.star_def]
  exact integral_conj

theorem lwSymm_integral_cj (c : Bool) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℂ) :
    ∫ ω, lwSymmCj c (f ω) ∂P = lwSymmCj c (∫ ω, f ω ∂P) := by
  cases c
  · rfl
  · exact integral_conj

/-- **The twist in expectation**: `∫ (Γ.twist c t).val = (conj if c) ∫ Γ.val`. -/
theorem lwSymm_twist_integral (hSr : ∀ i j, star (S i j) = S i j) (hM : Mᵀ = M) (hS : Sᵀ = S) (hSp : Spᵀ = Sp)
    (c t : Bool) (Γ : LGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (lwSymmTwistG c t Γ).val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      lwSymmCj c (∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz)) := by
  have h1 : ∀ ω, (lwSymmTwistG c t Γ).val (lwSampleData sz n z u M S Sp ω) ℓe =
      lwSymmCj c (Γ.val (lwSymmDataTr (lwSampleData sz n z u M S Sp ω) t) ℓe) :=
    fun ω => lwSymmTwistG_val (lwSampleData sz n z u M S Sp ω) hSr c t Γ ℓe
  have h2 : ∫ ω, Γ.val (lwSymmDataTr (lwSampleData sz n z u M S Sp ω) t) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, Γ.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) := by
    cases t
    · rfl
    · simp only [lwSymmDataTr, Bool.cond_true, ← LGraph.val_transpose]
      exact lwSymm_transpose_integral hM hS hSp Γ ℓe
  simp only [h1]
  rw [lwSymm_integral_cj, h2]

end TwistE

/-! ## 4. (S3) `(Owx)` at a vertex of `E ⊕ I`, an external vertex included

`owx_graph_E` (T2107) treats the weight `Ǧ_{xx}` at an *internal* vertex `x : I`.  The Stein identity is pointwise in the
labels and only involves the label `ℓ x` of the vertex, so the same four terms work at any `x : E ⊕ I`; for an external
`x = inl a` the label `ℓe a` is fixed, not summed.  The terms `owxET1 .. owxET4` are those of the merged `owxT1 .. owxT4`
with the vertex `inr (inl x)` replaced by `owxEmb k x` (`owxT1 m Γ x = owxET1 m Γ (inr x)` by `rfl`); the leaves join the
molecule of `x`, so `n_M` is unchanged for an external `x` too. -/

section OwxE

variable {E I : Type*}

/-- **Term 1 of `(Owx)` at `x : E ⊕ I`**: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f` (`Γ` with a leaf `α` joined to `x`). -/
def owxET1 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) : LGraph E (I ⊕ Fin 1) :=
  Γ.owxExt (owxEmb 1) m [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, owxEmb 1 x, Sum.inr (Sum.inr 0)⟩]

/-- **Term 2 of `(Owx)` at `x`**: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ} f` (the weight `p.1` dropped, a path `x - α - β`). -/
def owxET2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := p.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, owxEmb 2 x, Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- **Term 3 of `(Owx)` at `x`, for the solid edge `q.1` of `f`**: `-m Σ_α S_{xα} G_{αx} ∂_{h_{αx}}` on `q.1`. -/
def owxET3 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [(owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 x⟩]
    [⟨false, true, owxEmb 1 x, Sum.inr (Sum.inr 0)⟩]

/-- **Term 4 of `(Owx)` at `x`, for the solid edge `q.1` of `f`**: `-m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}}` on `q.1`. -/
def owxET4 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)⟩]
    [⟨true, true, owxEmb 2 x, Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- At an internal vertex the new terms are the merged ones. -/
theorem owxET1_inr (m : ℂ) (Γ : LGraph E I) (x : I) : owxET1 m Γ (Sum.inr x) = owxT1 m Γ x := rfl

theorem owxET2_inr (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    owxET2 m Γ p (Sum.inr x) = owxT2 m Γ p x := rfl

theorem owxET3_inr (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    owxET3 m Γ (Sum.inr x) q = owxT3 m Γ x q := rfl

theorem owxET4_inr (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    owxET4 m Γ (Sum.inr x) q = owxT4 m Γ x q := rfl

end OwxE

section OwxENM

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The retraction of the vertices of a graph with `k` pendant vertices at `x`: the new vertices go to `x`. -/
def lwSymmRho (k : ℕ) (x : E ⊕ I) : E ⊕ (I ⊕ Fin k) → E ⊕ I :=
  Sum.elim Sum.inl (Sum.elim Sum.inr (fun _ => x))

theorem lwSymmRho_emb (k : ℕ) (x v : E ⊕ I) : lwSymmRho k x (owxEmb k v) = v := by
  rcases v with a | b <;> rfl

/-- `n_M` of `Γ.owxExt` is that of `Γ` when the appended waved edges only join vertices that the retraction
`lwSymmRho k x` identifies, and every new vertex is joined to `x`. -/
theorem lwSymmExt_nM (Γ : LGraph E I) (k : ℕ) (x : E ⊕ I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (hw : ∀ e ∈ w, lwSymmRho k x e.x = lwSymmRho k x e.y)
    (hc : ∀ v, (Γ.owxExt (owxEmb k) c s w).molGraph.Reachable v (owxEmb k (lwSymmRho k x v))) :
    (Γ.owxExt (owxEmb k) c s w).nM = Γ.nM := by
  refine owx_nM_eq Γ (Γ.owxExt (owxEmb k) c s w) (owxEmb k) (lwSymmRho k x) (lwSymmRho_emb k x)
    (fun e => rfl) (fun e => rfl) ?_ ?_ hc
  · intro u v h
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h ⊢
    rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
    · left
      refine ⟨WEdge.map (owxEmb k) e, ?_, ?_⟩
      · exact List.mem_append_left _ (List.mem_map_of_mem he)
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; simp [WEdge.map, h1, h2]
        · right; simp [WEdge.map, h1, h2]
    · right
      refine ⟨DEdge.map (owxEmb k) e, ?_, ?_, ?_⟩
      · exact List.mem_map_of_mem he
      · simpa [DEdge.map] using h1
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; simp [DEdge.map, h1, h2]
        · right; simp [DEdge.map, h1, h2]
  · intro u v h
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h
    rcases h with ⟨e', he', h⟩ | ⟨e', he', h1, h⟩
    · simp only [LGraph.owxExt, List.mem_append, List.mem_map] at he'
      rcases he' with ⟨e, he, rfl⟩ | he'
      · right
        simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
        left
        refine ⟨e, he, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          subst h1 h2
          simp [WEdge.map, lwSymmRho_emb]
        · right
          subst h1 h2
          simp [WEdge.map, lwSymmRho_emb]
      · left
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1 h2; exact hw e' he'
        · subst h1 h2; exact (hw e' he').symm
    · simp only [LGraph.owxExt, List.mem_map] at he'
      obtain ⟨e, he, rfl⟩ := he'
      right
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      right
      refine ⟨e, he, by simpa [DEdge.map] using h1, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        subst h1 h2
        simp [DEdge.map, lwSymmRho_emb]
      · right
        subst h1 h2
        simp [DEdge.map, lwSymmRho_emb]

theorem lwSymm_emb_ne (x : E ⊕ I) (k : ℕ) (j : Fin k) :
    (Sum.inr (Sum.inr j) : E ⊕ (I ⊕ Fin k)) ≠ owxEmb k x := by
  rcases x with a | b <;> simp [owxEmb]

/-- With one new vertex `α` joined to `x` by an appended waved edge, every vertex is joined to its retraction. -/
theorem lwSymmExt_reach1 (Γ : LGraph E I) (x : E ⊕ I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (col σ : Bool)
    (hw : (⟨col, σ, owxEmb 1 x, Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 1) c s w).molGraph.Reachable v (owxEmb 1 (lwSymmRho 1 x v)) := by
  intro v
  rcases v with a | b | j
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.refl _
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨lwSymm_emb_ne x 1 0, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw, Or.inr ⟨rfl, rfl⟩⟩

/-- With two new vertices (a path `x - α - β`), every vertex is joined to its retraction. -/
theorem lwSymmExt_reach2 (Γ : LGraph E I) (x : E ⊕ I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (col σ col' σ' : Bool)
    (hw : (⟨col, σ, owxEmb 2 x, Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w)
    (hw' : (⟨col', σ', Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable v (owxEmb 2 (lwSymmRho 2 x v)) := by
  have h1 : (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable (Sum.inr (Sum.inr 0)) (owxEmb 2 x) := by
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨lwSymm_emb_ne x 2 0, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw, Or.inr ⟨rfl, rfl⟩⟩
  have h2 : (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) := by
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw', Or.inr ⟨rfl, rfl⟩⟩
  intro v
  rcases v with a | b | j
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.refl _
  · fin_cases j
    · exact h1
    · exact h2.trans h1

end OwxENM

section OwxECounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem owxET1_counters (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) :
    (owxET1 m Γ x).nS = Γ.nS + 1 ∧ (owxET1 m Γ x).nW = Γ.nW + 1 ∧ (owxET1 m Γ x).nV = Γ.nV + 1 ∧
      (owxET1 m Γ x).nM = Γ.nM := by
  refine ⟨by simp [owxET1, LGraph.owxExt, LGraph.nS], by simp [owxET1, LGraph.owxExt, LGraph.nW],
    by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  refine lwSymmExt_nM Γ 1 x m _ _ ?_ (lwSymmExt_reach1 Γ x m _ _ false true (by simp))
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  exact lwSymmRho_emb _ _ _

theorem owxET2_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) :
    (owxET2 m Γ p x).nS = Γ.nS + 1 ∧ (owxET2 m Γ p x).nW = Γ.nW + 2 ∧ (owxET2 m Γ p x).nV = Γ.nV + 2 ∧
      (owxET2 m Γ p x).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  refine ⟨?_, by simp [owxET2, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxET2, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxET2 m Γ p x).nM = ({ Γ with solid := p.2 } : LGraph E I).nM := by
      refine lwSymmExt_nM _ 2 x (m ^ 3) _ _ ?_
        (lwSymmExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> first | rfl | exact lwSymmRho_emb _ _ _
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem owxET3_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    (owxET3 m Γ x q).nS = Γ.nS + 1 ∧ (owxET3 m Γ x q).nW = Γ.nW + 1 ∧ (owxET3 m Γ x q).nV = Γ.nV + 1 ∧
      (owxET3 m Γ x q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [owxET3, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxET3, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxET3 m Γ x q).nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine lwSymmExt_nM _ 1 x m _ _ ?_ (lwSymmExt_reach1 _ x m _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact lwSymmRho_emb _ _ _
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem owxET4_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    (owxET4 m Γ x q).nS = Γ.nS + 1 ∧ (owxET4 m Γ x q).nW = Γ.nW + 2 ∧ (owxET4 m Γ x q).nV = Γ.nV + 2 ∧
      (owxET4 m Γ x q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [owxET4, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxET4, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxET4 m Γ x q).nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine lwSymmExt_nM _ 2 x (m ^ 3) _ _ ?_
        (lwSymmExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> first | rfl | exact lwSymmRho_emb _ _ _
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem owxET1_ord (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) :
    ord (owxET1 m Γ x).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxET1_counters m Γ x
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxET2_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) : ord (owxET2 m Γ p x).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxET2_counters m Γ p hp x
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxET3_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) : ord (owxET3 m Γ x q).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxET3_counters m Γ p hp x q hq
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxET4_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) : ord (owxET4 m Γ x q).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxET4_counters m Γ p hp x q hq
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

end OwxECounters

section OwxETermVal

variable {E I : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The value of a term of `owxET1` at a labelling `ℓ'` extending `ℓ` (`ℓ' ∘ owxEmb 1 = ℓ`). -/
theorem owxET1_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (ℓ : E ⊕ I → ι)
    (ℓ' : E ⊕ (I ⊕ Fin 1) → ι) (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (owxET1 m Γ x).term D ℓ' = m * Γ.term D ℓ *
      (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0))) -
        D.M (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0)))) *
      D.S (ℓ x) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (owxEmb 1 x) = ℓ x := by
    rw [← hℓ]; rfl
  rw [owxET1, LGraph.term_owxExt, hℓ]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxET2` (the weight dropped: `Γ'` has the solid edges `p.2`). -/
theorem owxET2_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (x : E ⊕ I) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (owxET2 m Γ p x).term D ℓ' = m ^ 3 * ({ Γ with solid := p.2 } : LGraph E I).term D ℓ *
      ((D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0))) -
          D.M (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0)))) *
        (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1))) -
          D.M (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1))))) *
      (D.Sp (ℓ x) (ℓ' (Sum.inr (Sum.inr 0))) *
        D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1)))) := by
  have hx : ℓ' (owxEmb 2 x) = ℓ x := by
    rw [← hℓ]; rfl
  rw [owxET2, LGraph.term_owxExt, hℓ]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxET3`. -/
theorem owxET3_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 1) → ι)
    (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (owxET3 m Γ x q).term D ℓ' = m * ({ Γ with solid := q.2 } : LGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ x) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ x)) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ x)) *
      D.S (ℓ x) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (owxEmb 1 x) = ℓ x := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 1 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) q.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (owxEmb 1 x) (SEdge.map (owxEmb 1) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ x) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ x)) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq]
  rw [owxET3, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D ℓ' _)), h]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxET4`. -/
theorem owxET4_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι)
    (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (owxET4 m Γ x q).term D ℓ' = m ^ 3 * ({ Γ with solid := q.2 } : LGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 0)))) *
      (D.Sp (ℓ x) (ℓ' (Sum.inr (Sum.inr 0))) *
        D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1)))) := by
  have hx : ℓ' (owxEmb 2 x) = ℓ x := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 2 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq]
  rw [owxET4, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D ℓ' _)), h]
  simp [SEdge.val, WEdge.val, hx]

end OwxETermVal

section OwxEIdentity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **`(Owx)` at the vertex `x : E ⊕ I` for one labelling of the vertices of `Γ`** (expectations of terms): the weight
`Ǧ_{xx}` of `Γ` (`p.1`, `p.1 = ⟨true, true, x, x⟩`); for an external `x = inl a` the label is `ℓe a`.  The proof is that of
`owx_term_integral` with `ℓ x` for the label of the vertex.  Hypotheses: `GaussIBP` (proved: `gaussIBP sz`), `Im z > 0`,
`u > 0`, `m ≠ 0`, `z + u m = -m⁻¹`, `S⁺ (1 - m² S) = S`, `M_{aa} = m`. -/
theorem owxE_term_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I)
    (hx : p.1 = ⟨true, true, x, x⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (ℓi : I → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) =
      ∑ α, ∫ ω, (owxET1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)
          ∂(Sizes.seqP sz) +
      ∑ α, ∑ β, ∫ ω, (owxET2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
          (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) +
      ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  set ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n) := Sum.elim ℓe ℓi with hℓ
  set xl : Idx d (sz.L n) (sz.W n) := ℓ x with hxl
  set K : ℂ := lwK Γ M (lwS sz n u) Sp ℓ with hK
  set P := (p.2.map (owxEdgePoly sz n M ℓ)).prod with hPdef
  have hf : ∀ ω, lwPoly sz n z u P ω =
      (p.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod :=
    fun ω => lwPoly_owxEdgePoly_prod z u M (lwS sz n u) Sp ℓ p.2 ω
  have hP1 : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have hw : ∀ ω, SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ p.1 =
      lwG sz n z u xl xl ω - m := by
    intro ω
    rw [hx]
    simp [SEdge.val, lwSampleData, lwG, hM, hℓ, hxl]
  have hΓ : ∀ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω) := by
    intro ω
    rw [lwStein_term_eq, lwSplit_prod Γ.solid _ p hp, hw ω, hf ω]
  have hℓx : ℓ x = xl := rfl
  have hK' : ∀ s : List (SEdge (E ⊕ I)),
      lwK ({ Γ with solid := s } : LGraph E I) M (lwS sz n u) Sp ℓ = K := fun s => rfl
  have hT1 : ∀ α ω, (owxET1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω)) * (lwG sz n z u α α ω - m) *
        lwS sz n u xl α := by
    intro α ω
    rw [owxET1_term _ m Γ x ℓ _ (owxLab1_emb ℓe ℓi α), hΓ ω]
    simp [owxLab1, lwSampleData, lwG, hM, hℓx]
  have hT2 : ∀ α β ω, (owxET2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
      (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * lwPoly sz n z u P ω) * ((lwG sz n z u α α ω - m) * (lwG sz n z u β β ω - m)) *
        (Sp xl α * lwS sz n u α β) := by
    intro α β ω
    rw [owxET2_term _ m Γ p x ℓ _ (owxLab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := p.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * lwPoly sz n z u P ω := by
      rw [lwStein_term_eq, hf ω, hK']
    rw [this]
    simp [owxLab2, lwSampleData, lwG, hM, hℓx]
  have hT3 : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α ω,
      (owxET3 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        ((if q.1.σ then lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u xl (ℓ q.1.dst) ω
          else star (lwG sz n z u (ℓ q.1.src) xl ω) * star (lwG sz n z u α (ℓ q.1.dst) ω)) *
          lwG sz n z u α xl ω) * lwS sz n u xl α := by
    intro q α ω
    rw [owxET3_term _ m Γ x q ℓ _ (owxLab1_emb ℓe ℓi α)]
    have : ({ Γ with solid := q.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
      rw [lwStein_term_eq, hK']
    rw [this]
    simp [owxLab1, lwSampleData, lwG, hℓx]
  have hT4 : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α β ω,
      (owxET4 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        ((if q.1.σ then lwG sz n z u (ℓ q.1.src) β ω * lwG sz n z u α (ℓ q.1.dst) ω
          else star (lwG sz n z u (ℓ q.1.src) α ω) * star (lwG sz n z u β (ℓ q.1.dst) ω)) *
          lwG sz n z u β α ω) * (Sp xl α * lwS sz n u α β) := by
    intro q α β ω
    rw [owxET4_term _ m Γ x q ℓ _ (owxLab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := q.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
      rw [lwStein_term_eq, hK']
    rw [this]
    simp [owxLab2, lwSampleData, lwG, hℓx]
  have hdh : ∀ (α w : Idx d (sz.L n) (sz.W n)) ω, dhSample sz n u α w (lwPoly sz n z u P) ω =
      ((lwSplit p.2).map fun q =>
        (if q.1.σ then -(lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u w (ℓ q.1.dst) ω)
          else -(star (lwG sz n z u (ℓ q.1.src) w ω) * star (lwG sz n z u α (ℓ q.1.dst) ω))) *
        (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod).sum := by
    intro α w ω
    have hfun : lwPoly sz n z u P = fun ω => (p.2.map fun a =>
        SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ a).prod := funext hf
    rw [hfun, lwStein_dh_listProd p.2 (fun e _ => lwStein_sedge_val_tame1 hz e ℓ)]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [lwStein_dh_sedge_val hz hu q.1 α w ℓ ω]
  have hS3 : ∀ α ω, ((lwSplit p.2).map fun q => (owxET3 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum =
      -(K * (m * (lwS sz n u xl α * lwG sz n z u α xl ω)) *
        dhSample sz n u α xl (lwPoly sz n z u P) ω) := by
    intro α ω
    rw [hdh α xl ω]
    refine owx_list_aux _ _ _ _ fun q _ => ?_
    rw [hT3 q α ω]
    by_cases hσ : q.1.σ <;> simp [hσ] <;> ring
  have hS4 : ∀ α β ω, ((lwSplit p.2).map fun q => (owxET4 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum =
      -(K * (m ^ 3 * (Sp xl α * lwS sz n u α β * lwG sz n z u β α ω)) *
        dhSample sz n u β α (lwPoly sz n z u P) ω) := by
    intro α β ω
    rw [hdh β α ω]
    refine owx_list_aux _ _ _ _ fun q _ => ?_
    rw [hT4 q α β ω]
    by_cases hσ : q.1.σ <;> simp [hσ] <;> ring
  have hpath : ∀ ω, K * (m * ∑ α, lwS sz n u xl α * (lwG sz n z u xl xl ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u xl α * lwG sz n z u α xl ω * dhSample sz n u α xl (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω) =
      ∑ α, (owxET1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) +
      ∑ α, ∑ β, (owxET2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) +
      ∑ α, ((lwSplit p.2).map fun q => (owxET3 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => (owxET4 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum := by
    intro ω
    simp only [hT1, hT2, hS3, hS4]
    have hA : ∑ x, m * (K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω)) *
        (lwG sz n z u x x ω - m) * lwS sz n u xl x =
        K * (m * ∑ α, lwS sz n u xl α * (lwG sz n z u xl xl ω - m) * (lwG sz n z u α α ω - m) *
          lwPoly sz n z u P ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hB : ∑ x, ∑ x_1, m ^ 3 * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u x x ω - m) * (lwG sz n z u x_1 x_1 ω - m)) * (Sp xl x * lwS sz n u x x_1) =
        K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
          (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have hC : ∑ x, -(K * (m * (lwS sz n u xl x * lwG sz n z u x xl ω)) *
        dhSample sz n u x xl (lwPoly sz n z u P) ω) =
        -(K * (m * ∑ α, lwS sz n u xl α * lwG sz n z u α xl ω *
          dhSample sz n u α xl (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hD : ∑ x, ∑ x_1, -(K * (m ^ 3 * (Sp xl x * lwS sz n u x x_1 * lwG sz n z u x_1 x ω)) *
        dhSample sz n u x_1 x (lwPoly sz n z u P) ω) =
        -(K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β α ω *
          dhSample sz n u β α (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [hA, hB, hC, hD]
    ring
  have key := owx_integral hG hz hu hm0 hzm Sp hSp P xl
  have hint : ∀ {E' I' : Type} (T : LGraph E' I') (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have e1 : ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ ∂(Sizes.seqP sz) =
      K * ∫ ω, (lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω ∂(Sizes.seqP sz) := by
    simp_rw [hΓ]
    rw [integral_const_mul]
  rw [e1, key, ← integral_const_mul]
  simp_rw [hpath]
  set S1 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, (owxET1 m Γ x).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) with hS1
  set S2 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, (owxET2 m Γ p x).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) with hS2
  set S3 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ((lwSplit p.2).map fun q => (owxET3 m Γ x q).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum with hS3'
  set S4 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, ((lwSplit p.2).map fun q => (owxET4 m Γ x q).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum with hS4'
  have hi1 : Integrable S1 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => hint _ _
  have hi2 : Integrable S2 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _
  have hi3 : Integrable S3 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi4 : Integrable S4 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi12 : Integrable (fun ω => S1 ω + S2 ω) (Sizes.seqP sz) := hi1.add hi2
  have hi123 : Integrable (fun ω => S1 ω + S2 ω + S3 ω) (Sizes.seqP sz) := hi12.add hi3
  change ∫ ω, (S1 ω + S2 ω + S3 ω + S4 ω) ∂(Sizes.seqP sz) = _
  rw [integral_add hi123 hi4, integral_add hi12 hi3, integral_add hi1 hi2]
  have e1' : ∫ ω, S1 ω ∂(Sizes.seqP sz) = ∑ α, ∫ ω, (owxET1 m Γ x).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
    integral_finsetSum _ fun α _ => hint _ _
  have e2' : ∫ ω, S2 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ∫ ω, (owxET2 m Γ p x).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
    rw [hS2, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_finsetSum _ fun β _ => hint _ _
  have e3' : ∫ ω, S3 ω ∂(Sizes.seqP sz) = ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    rw [hS3', integral_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  have e4' : ∫ ω, S4 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    rw [hS4', integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  rw [e1', e2', e3', e4']


/-- **(S3) `(Owx)` at an external (or internal) vertex: the identity of expectations of values.**  For a graph `Γ` with the
light-weight `Ǧ_{xx}` at the vertex `x : E ⊕ I` (`p.1 = ⟨true, true, x, x⟩`, `p ∈ lwSplit Γ.solid`):
`E Γ.val = E (owxET1 m Γ x).val + E (owxET2 m Γ p x).val + Σ_q E (owxET3 m Γ x q).val + Σ_q E (owxET4 m Γ x q).val`,
`q` running over `lwSplit p.2`.  For `x = inr x'` the terms are those of `owx_graph_E` (`owxET1_inr`, ...); for
`x = inl a` the label `ℓe a` is fixed.  Counters: `owxET*_counters`, `owxET*_ord` (each `ord Γ + 1`). -/
theorem owxE_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I)
    (hx : p.1 = ⟨true, true, x, x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (owxET1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxET2 m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  classical
  have hint : ∀ ℓ', Integrable (fun ω => Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ')
      (Sizes.seqP sz) := fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz Γ ℓ').tame
  have hL : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _
  rw [hL, owx_integral_val1 hG hz M _ Sp, owx_integral_val2 hG hz M _ Sp]
  simp_rw [owxE_term_integral hG hz hu hm0 hzm Sp M hSp hM Γ p hp x hx ℓe]
  simp only [Finset.sum_add_distrib]
  have h3 : ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (owxET3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, (owxET3 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => owx_integral_val1 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  have h4 : ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (owxET4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, (owxET4 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => owx_integral_val2 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  rw [h3, h4]

end OwxEIdentity

/-! ## 5. The forms `strat_local` meets: the expansions at an arbitrary edge or weight

Each form is the merged expansion applied to the *frame* `Γ' = (Γ with the selected edges uncircled)^{(c,t)}` and carried
back by the twist (`lwSymm_twist_integral`): `(c, t)` is chosen so that the twisted selected edge is the blue out-edge of the
internal vertex `x` (resp. the blue pair `G_{xy} G_{y'x}`, the light-weight `Ǧ_{xx}`).  The selector is the pair `(c, t)`:
`c = true` iff the selected edge is red, `t = true` iff it is an in-edge of `x`.  Data: those of the merged `*_graph_E`, plus
`M a b = 0` for `a ≠ b` (circled selected edges, `lwSymmUncirc_val`) and `S⁺ᵀ = S⁺` (`lwSymm_transpose_integral`). -/

section Frame

variable {E I : Type*}

theorem lwSymm_lwSplit_map {κ κ' : Type*} (f : κ → κ') (l : List κ) :
    lwSplit (l.map f) = (lwSplit l).map (fun q => (f q.1, q.2.map f)) := by
  induction l with
  | nil => simp [lwSplit]
  | cons a l ih => simp [lwSplit, ih, List.map_map, Function.comp_def]

theorem lwSymmTwistS_circ (c t : Bool) {V : Type*} (e : SEdge V) :
    (lwSymmTwistS c t e).circ = e.circ := by
  cases c <;> cases t <;> rfl

theorem lwSymmTwistS_with_circ (c t : Bool) {V : Type*} (e : SEdge V) (b : Bool) :
    lwSymmTwistS c t { e with circ := b } = { lwSymmTwistS c t e with circ := b } := by
  cases c <;> cases t <;> rfl

/-- `Γ` with the selected edge `p.1` (`p ∈ lwSplit Γ.solid`) uncircled and put first. -/
def lwSymmUncirc (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E I :=
  { Γ with solid := { p.1 with circ := false } :: p.2 }

/-- `Γ` with the two selected edges `p.1`, `q.1` (`p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2`) uncircled and put first. -/
def lwSymmUncirc2 (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E I :=
  { Γ with solid := { p.1 with circ := false } :: { q.1 with circ := false } :: q.2 }

/-- The frame of the selected edge: the uncircled graph, twisted. -/
def lwSymmFrame (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E I :=
  lwSymmTwistG c t (lwSymmUncirc Γ p)

/-- The selected pair in the frame: `(twist p.1 uncircled, twist of the other edges)`. -/
def lwSymmFrameP (c t : Bool) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    SEdge (E ⊕ I) × List (SEdge (E ⊕ I)) :=
  (lwSymmTwistS c t { p.1 with circ := false }, p.2.map (lwSymmTwistS c t))

/-- The frame of the selected pair `(p.1, q.1)`. -/
def lwSymmFrame2 (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E I :=
  lwSymmTwistG c t (lwSymmUncirc2 Γ p q)

/-- `p` in the frame of two selected edges: `(twist p.1 uncircled, twist of (q.1 uncircled) :: q.2)`. -/
def lwSymmFrame2P (c t : Bool) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    SEdge (E ⊕ I) × List (SEdge (E ⊕ I)) :=
  (lwSymmTwistS c t { p.1 with circ := false },
    lwSymmTwistS c t { q.1 with circ := false } :: q.2.map (lwSymmTwistS c t))

/-- `q` in the frame of two selected edges. -/
def lwSymmFrame2Q (c t : Bool) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    SEdge (E ⊕ I) × List (SEdge (E ⊕ I)) :=
  (lwSymmTwistS c t { q.1 with circ := false }, q.2.map (lwSymmTwistS c t))

theorem lwSymmFrame_solid (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame c t Γ p).solid = (lwSymmFrameP c t p).1 :: (lwSymmFrameP c t p).2 := by
  unfold lwSymmFrame
  rw [lwSymmTwistG_solid]
  simp [lwSymmFrameP, lwSymmUncirc]

theorem lwSymmFrameP_mem (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmFrameP c t p ∈ lwSplit (lwSymmFrame c t Γ p).solid := by
  rw [lwSymmFrame_solid]
  simp [lwSplit]

theorem lwSymmFrame2_solid (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (lwSymmFrame2 c t Γ p q).solid =
      (lwSymmFrame2P c t p q).1 :: (lwSymmFrame2P c t p q).2 := by
  unfold lwSymmFrame2
  rw [lwSymmTwistG_solid]
  simp [lwSymmFrame2P, lwSymmUncirc2]

theorem lwSymmFrame2P_mem (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmFrame2P c t p q ∈ lwSplit (lwSymmFrame2 c t Γ p q).solid := by
  rw [lwSymmFrame2_solid]
  simp [lwSplit]

theorem lwSymmFrame2Q_mem (c t : Bool) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmFrame2Q c t q ∈ lwSplit (lwSymmFrame2P c t p q).2 := by
  simp [lwSplit, lwSymmFrame2P, lwSymmFrame2Q]

/-- The selected edge in the frame is the uncircled twisted edge. -/
theorem lwSymmFrameP_fst (c t : Bool) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x v : E ⊕ I)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, x, v⟩) :
    (lwSymmFrameP c t p).1 = ⟨true, false, x, v⟩ := by
  simp only [lwSymmFrameP, lwSymmTwistS_with_circ, hx]

end Frame


/-! ### The output graphs of the forms, as functions of the original data -/

section FormDefs

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Form (a), term 1: `(owxET1 m Γ' x)` twisted back, `Γ' = Γ^{(c,t)}`. -/
def lwSymmOwxT1 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (owxET1 m (lwSymmTwistG c t Γ) x)

/-- Form (a), term 2. -/
def lwSymmOwxT2 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I) :
    LGraph E (I ⊕ Fin 2) :=
  lwSymmTwistG c t (owxET2 m (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) x)

/-- Form (a), term 3 for the edge `q.1` of `f` (`q ∈ lwSplit p.2`, in the original orientation). -/
def lwSymmOwxT3 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (owxET3 m (lwSymmTwistG c t Γ) x (lwSymmTwistP c t q))

/-- Form (a), term 4. -/
def lwSymmOwxT4 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 2) :=
  lwSymmTwistG c t (owxET4 m (lwSymmTwistG c t Γ) x (lwSymmTwistP c t q))

/-- Form (b), term 1 (`m 1_{x = y₁}`, `x` merged into `y₁`). -/
def lwSymmOe1xT1 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (v : E ⊕ I) (hv : v ≠ Sum.inr x) : LGraph E {i : I // i ≠ x} :=
  lwSymmTwistG c t (oe1xT1 m (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) x v hv)

/-- Form (b), term 2 (`m Σ_α S_{xα} Ǧ_{αα} 𝒢`). -/
def lwSymmOe1xOwx (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (owxT1 m (lwSymmFrame c t Γ p) x)

/-- Form (b), the derivative terms for the edge `q.1` of the rest (`q ∈ lwSplit p.2`): the list `oe1xDs` of the frame, twisted back. -/
def lwSymmOe1xDs (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (LGraph E (I ⊕ Fin 1)) :=
  (oe1xDs m (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q)).map (lwSymmTwistG c t)

/-- Form (c), `R1` (`m δ_{xy} G_{y'x} f`, `x` merged into `y`). -/
def lwSymmOe2xR1 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y : E ⊕ I) (hy : y ≠ Sum.inr x) : LGraph E {i : I // i ≠ x} :=
  lwSymmTwistG c t (oe2xR1 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) x y hy)

/-- Form (c), `R2` (`m³ S⁺_{xy} G_{y'y} f`). -/
def lwSymmOe2xR2 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : LGraph E I :=
  lwSymmTwistG c t (oe2xR2 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y')

/-- Form (c), `R3 = owxT1` (`m Σ_α S_{xα} Ǧ_{αα} 𝒢`). -/
def lwSymmOe2xR3 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (owxT1 m (lwSymmFrame2 c t Γ p q) x)

/-- Form (c), `R4`. -/
def lwSymmOe2xR4 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : LGraph E (I ⊕ Fin 2) :=
  lwSymmTwistG c t (oe2xR4 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y')

/-- Form (c), `R5`. -/
def lwSymmOe2xR5 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe2xR5 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y')

/-- Form (c), `R6`. -/
def lwSymmOe2xR6 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : LGraph E (I ⊕ Fin 2) :=
  lwSymmTwistG c t (oe2xR6 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y')

/-- Form (c), `R7` for the edge `q'.1` of `f` (`q' ∈ lwSplit q.2`, original orientation). -/
def lwSymmOe2xR7 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 1) :=
  lwSymmTwistG c t (oe2xR7 m (lwSymmFrame2 c t Γ p q) x y y' (lwSymmTwistP c t q'))

/-- Form (c), `R8` for the edge `q'.1` of `f`. -/
def lwSymmOe2xR8 (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : LGraph E (I ⊕ Fin 2) :=
  lwSymmTwistG c t (oe2xR8 m (lwSymmFrame2 c t Γ p q) x y y' (lwSymmTwistP c t q'))

end FormDefs

section Uncirc

variable {E I ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- **A circled non-loop edge `(G-M)_{xy}` is `G_{xy}` on the support of a `×`-dotted edge joining its ends**, for `M a b = 0`
(`a ≠ b`): `x ≠ y` as labels there, and the circle only subtracts `M_{ab}`. -/
theorem lwSymmUncirc_edge (D : LData ι) (hM0 : ∀ a b, a ≠ b → D.M a b = 0) (ℓ : V → ι) (dots : List (DEdge V))
    (e : SEdge V)
    (hX : e.circ = true → ∃ d ∈ dots, d.eq = false ∧ ((d.x = e.src ∧ d.y = e.dst) ∨ (d.x = e.dst ∧ d.y = e.src))) :
    SEdge.val D ℓ { e with circ := false } * (dots.map (DEdge.val ℓ)).prod =
      SEdge.val D ℓ e * (dots.map (DEdge.val ℓ)).prod := by
  cases hc : e.circ
  · have : ({ e with circ := false } : SEdge V) = e := by cases e; simp_all
    rw [this]
  · obtain ⟨d, hd, hde, hdd⟩ := hX hc
    by_cases hl : ℓ e.src = ℓ e.dst
    · have hz : (dots.map (DEdge.val ℓ)).prod = 0 := by
        refine List.prod_eq_zero (List.mem_map.mpr ⟨d, hd, ?_⟩)
        have : ℓ d.x = ℓ d.y := by
          rcases hdd with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, hl]
        simp [DEdge.val, hde, this]
      rw [hz]
      simp
    · have h0 := hM0 _ _ hl
      have : SEdge.val D ℓ { e with circ := false } = SEdge.val D ℓ e := by
        simp [SEdge.val, hc, h0]
      rw [this]

variable {E : Type*}

theorem lwSymmUncirc_term (D : LData ι) (hM0 : ∀ a b, a ≠ b → D.M a b = 0) (Γ : LGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hX : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (ℓ : E ⊕ I → ι) : (lwSymmUncirc Γ p).term D ℓ = Γ.term D ℓ := by
  have hs := lwSplit_prod Γ.solid (SEdge.val D ℓ) p hp
  have h := lwSymmUncirc_edge D hM0 ℓ Γ.dotted p.1 hX
  unfold LGraph.term lwSymmUncirc
  simp only [List.map_cons, List.prod_cons, hs]
  linear_combination (Γ.coeff * (p.2.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod) * h

theorem lwSymmUncirc2_term (D : LData ι) (hM0 : ∀ a b, a ≠ b → D.M a b = 0) (Γ : LGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hX1 : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y = q.1.src)))
    (ℓ : E ⊕ I → ι) : (lwSymmUncirc2 Γ p q).term D ℓ = Γ.term D ℓ := by
  have hs := lwSplit_prod Γ.solid (SEdge.val D ℓ) p hp
  have hs' := lwSplit_prod p.2 (SEdge.val D ℓ) q hq
  have h1 := lwSymmUncirc_edge D hM0 ℓ Γ.dotted p.1 hX1
  have h2 := lwSymmUncirc_edge D hM0 ℓ Γ.dotted q.1 hX2
  unfold LGraph.term lwSymmUncirc2
  simp only [List.map_cons, List.prod_cons, hs, hs']
  linear_combination
    (Γ.coeff * (q.2.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod *
        SEdge.val D ℓ { q.1 with circ := false }) * h1 +
      (Γ.coeff * (q.2.map (SEdge.val D ℓ)).prod * (Γ.waved.map (WEdge.val D ℓ)).prod * SEdge.val D ℓ p.1) * h2

/-- **The uncircled graph has the same value**: `Γ.val D = (lwSymmUncirc Γ p).val D` when `M a b = 0` (`a ≠ b`) and a
circled selected edge has a `×`-dotted edge between its ends (as in a normal graph). -/
theorem lwSymmUncirc_val (D : LData ι) (hM0 : ∀ a b, a ≠ b → D.M a b = 0) (Γ : LGraph E I)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hX : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (ℓe : E → ι) : (lwSymmUncirc Γ p).val D ℓe = Γ.val D ℓe := by
  simp only [LGraph.val, lwSymmUncirc_term D hM0 Γ p hp hX]

theorem lwSymmUncirc2_val (D : LData ι) (hM0 : ∀ a b, a ≠ b → D.M a b = 0) (Γ : LGraph E I)
    (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hX1 : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y = q.1.src)))
    (ℓe : E → ι) : (lwSymmUncirc2 Γ p q).val D ℓe = Γ.val D ℓe := by
  simp only [LGraph.val, lwSymmUncirc2_term D hM0 Γ p q hp hq hX1 hX2]

/-- **A normal graph satisfies the support hypothesis `hX`** of every non-loop selected edge (`defnlvl0` (iii): a non-loop
solid edge has a `×`-dotted edge between its ends). -/
theorem lwSymm_hX_of_normal (Γ : LGraph E I) (hN : Γ.Normal) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hne : p.1.src ≠ p.1.dst) :
    p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)) := by
  intro _
  have hmem : p.1 ∈ Γ.solid := (lwSplit_perm Γ.solid p hp).mem_iff.mpr (List.mem_cons_self ..)
  exact (hN.2.1 _ _ hne).2 ⟨p.1, hmem, hne, Or.inl ⟨rfl, rfl⟩⟩

end Uncirc

section FrameCounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwSymmUncirc_counters (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) :
    (lwSymmUncirc Γ p).nS = Γ.nS ∧ (lwSymmUncirc Γ p).nW = Γ.nW ∧ (lwSymmUncirc Γ p).nV = Γ.nV ∧
      (lwSymmUncirc Γ p).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  exact ⟨by simp only [lwSymmUncirc, LGraph.nS, List.length_cons]; omega, rfl, rfl,
    lwStein_nM_congr _ _ rfl rfl⟩

theorem lwSymmUncirc2_counters (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (lwSymmUncirc2 Γ p q).nS = Γ.nS ∧ (lwSymmUncirc2 Γ p q).nW = Γ.nW ∧ (lwSymmUncirc2 Γ p q).nV = Γ.nV ∧
      (lwSymmUncirc2 Γ p q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  exact ⟨by simp only [lwSymmUncirc2, LGraph.nS, List.length_cons]; omega, rfl, rfl,
    lwStein_nM_congr _ _ rfl rfl⟩

/-- **The frame keeps the counters.** -/
theorem lwSymmFrame_counters (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) : (lwSymmFrame c t Γ p).counters = Γ.counters := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmUncirc_counters Γ p hp
  rw [lwSymmFrame, lwSymmTwistG_counters_eq]
  simp only [LGraph.counters, h1, h2, h3, h4]

theorem lwSymmFrame2_counters (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (lwSymmFrame2 c t Γ p q).counters = Γ.counters := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmUncirc2_counters Γ p q hp hq
  rw [lwSymmFrame2, lwSymmTwistG_counters_eq]
  simp only [LGraph.counters, h1, h2, h3, h4]

end FrameCounters

/-! ### The data hypotheses of the sample data -/

section DataFacts

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

theorem lwSymm_lwS_real (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    star (lwS sz n u i j) = lwS sz n u i j := by
  simp [lwS]

theorem lwSymm_lwS_symm (u : ℝ) : (lwS sz n u)ᵀ = lwS sz n u := by
  ext i j
  simp only [Matrix.transpose_apply, lwS, Matrix.of_apply]
  rw [svarF_comm]

variable {sz n}

/-- `M = m I`: the entries `M_{aa} = m`, `M_{ab} = 0` make `M` symmetric. -/
theorem lwSymm_M_symm {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hM0 : ∀ a b, a ≠ b → M a b = 0) : Mᵀ = M := by
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · simp [hM0 _ _ h, hM0 _ _ (Ne.symm h)]

/-- **`S⁺ = S (1 - m² S)⁻¹` is symmetric** (`S` symmetric, `|m|² u < 1`). -/
theorem lwSymm_lwSplus_symm {u : ℝ} (hu : 0 ≤ u) {m : ℂ} (hm : ‖m‖ ^ 2 * u < 1) :
    (lwSplus sz n u m)ᵀ = lwSplus sz n u m := by
  have hSs := lwSymm_lwS_symm sz n u
  set S := lwS sz n u with hS
  set A : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := 1 - m ^ 2 • S with hA
  have hU : IsUnit A := lwS_isUnit hu hm
  have hAT : Aᵀ = A := by
    simp only [hA, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hSs]
  have hcomm : S * A = A * S := by
    simp only [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hinvT : (Ring.inverse A)ᵀ = Ring.inverse A := by
    rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_nonsing_inv, hAT]
  unfold lwSplus
  rw [Matrix.transpose_mul, hinvT, hSs]
  calc Ring.inverse A * S = Ring.inverse A * S * (A * Ring.inverse A) := by
        rw [Ring.mul_inverse_cancel _ hU, Matrix.mul_one]
    _ = Ring.inverse A * (S * A) * Ring.inverse A := by simp only [Matrix.mul_assoc]
    _ = Ring.inverse A * (A * S) * Ring.inverse A := by rw [hcomm]
    _ = S * Ring.inverse A := by
        rw [← Matrix.mul_assoc (Ring.inverse A) A S, Ring.inverse_mul_cancel _ hU, Matrix.one_mul]

end DataFacts

/-! ### The twisted expansion of a list of terms -/

section Transport

theorem lwSymm_lwSplit_twistP {V : Type*} (c t : Bool) (l : List (SEdge V)) :
    lwSplit (l.map (lwSymmTwistS c t)) = (lwSplit l).map (lwSymmTwistP c t) :=
  lwSymm_lwSplit_map _ l

theorem lwSymm_cj_list_sum {κ : Type*} (c : Bool) (f : κ → ℂ) (l : List κ) :
    lwSymmCj c (l.map f).sum = (l.map fun a => lwSymmCj c (f a)).sum := by
  simpa [List.map_map, Function.comp_def] using map_list_sum (lwSymmCj c) (l.map f)

end Transport

/-! ### (a) The weight expansion at any light-weight, blue or red, internal or external -/

section FormWeight

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **Form (a): `(Owx)` at an arbitrary light-weight** (`7_8:294-306`; `strat_local` Step 1).  `p ∈ lwSplit Γ.solid`, `p.1` a
light-weight at `x : E ⊕ I` (internal or external), blue (`c = false`) or red (`c = true`): `lwSymmTwistS c t p.1 =
⟨true, true, x, x⟩` (`t` is immaterial for a loop).  With the frame `Γ' = Γ^{(c,t)}` (`Ḡ`-weight: conjugate graph):
`E Γ.val = E (owxET1 m Γ' x)^{(c,t)}.val + E (owxET2 m Γ' p' x)^{(c,t)}.val + Σ_q E (owxET3 m Γ' x q')^{(c,t)}.val + Σ_q
E (owxET4 m Γ' x q')^{(c,t)}.val`, `q` over `lwSplit p.2`, `q' = lwSymmTwistP c t q`.  Counters: `lwSymm_weight_ord`.  Data: those of
`owx_graph_E` plus `M a b = 0` and `S⁺ᵀ = S⁺`. -/
theorem lwSymm_weight_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I)
    (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (lwSymmOwxT1 c t m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOwxT2 c t m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ∫ ω, (lwSymmOwxT3 c t m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit p.2).map fun q => ∫ ω, (lwSymmOwxT4 c t m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  simp only [lwSymmOwxT1, lwSymmOwxT2, lwSymmOwxT3, lwSymmOwxT4]
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓe' : E' → Idx d (sz.L n) (sz.W n)),
      ∫ ω, (lwSymmTwistG c t T).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz) =
        lwSymmCj c (∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz)) :=
    fun T ℓe' => lwSymm_twist_integral (lwSymm_lwS_real sz n u) hMs (lwSymm_lwS_symm sz n u) hSpT c t T ℓe'
  have hp' : lwSymmTwistP c t p ∈ lwSplit (lwSymmTwistG c t Γ).solid := by
    rw [lwSymmTwistG_solid, lwSymm_lwSplit_twistP]
    exact List.mem_map_of_mem hp
  have key := owxE_graph_E hG hz hu hm0 hzm Sp M hSp hM (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) hp' x hx ℓe
  have e0 : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      lwSymmCj c (∫ ω, (lwSymmTwistG c t Γ).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t Γ]
    exact tw (lwSymmTwistG c t Γ) ℓe
  rw [e0, key, map_add, map_add, map_add, tw, tw, lwSymm_cj_list_sum, lwSymm_cj_list_sum]
  have hS : lwSplit (lwSymmTwistP c t p).2 = (lwSplit p.2).map (lwSymmTwistP c t) :=
    lwSymm_lwSplit_twistP c t p.2
  rw [hS, List.map_map, List.map_map]
  simp only [Function.comp_def, ← tw]

end FormWeight

/-! ### (b) The edge expansion `(Oe1x)` at an edge of any colour and direction -/

section FormEdge

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **Form (b): `(Oe1x)` at the selected edge `p.1` at the internal vertex `x`** (`7_8:309-330`; `strat_local` Step 2),
for an edge of any colour and direction.  The selector `(c, t)`: `lwSymmTwistS c t p.1 = ⟨true, p.1.circ, inr x, v⟩`, i.e.
`c = true` iff `p.1` is red, `t = true` iff `p.1` is an in-edge of `x`; `v ≠ inr x` is its far end.  The frame is
`Γ' = lwSymmFrame c t Γ p` (the selected edge uncircled, then twisted).  A circled selected edge needs `M a b = 0` and a
`×`-dotted edge between its ends (`hX`, as in a normal graph).
`E Γ.val = E (oe1xT1 m Γ' p' x v)^{(c,t)}.val + E (owxT1 m Γ' x)^{(c,t)}.val + Σ_q Σ_{T ∈ oe1xDs m Γ' x v q'} E T^{(c,t)}.val`,
`q ∈ lwSplit p.2`, `q' = lwSymmTwistP c t q`.  Counters: `lwSymm_oe1x_ord`. -/
theorem lwSymm_oe1x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (v : E ⊕ I) (hv : v ≠ Sum.inr x) (c t : Bool)
    (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩)
    (hX : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (lwSymmOe1xT1 c t m Γ p x v hv).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe1xOwx c t m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ((lwSymmOe1xDs c t m Γ p x v q).map fun T =>
        ∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum).sum := by
  simp only [lwSymmOe1xT1, lwSymmOe1xOwx, lwSymmOe1xDs, List.map_map, Function.comp_def]
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓe' : E' → Idx d (sz.L n) (sz.W n)),
      ∫ ω, (lwSymmTwistG c t T).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz) =
        lwSymmCj c (∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz)) :=
    fun T ℓe' => lwSymm_twist_integral (lwSymm_lwS_real sz n u) hMs (lwSymm_lwS_symm sz n u) hSpT c t T ℓe'
  have e00 : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (lwSymmUncirc Γ p).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact (lwSymmUncirc_val (lwSampleData sz n z u M (lwS sz n u) Sp ω) hM0 Γ p hp hX ℓe).symm
  have e0 : ∫ ω, (lwSymmUncirc Γ p).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      lwSymmCj c (∫ ω, (lwSymmFrame c t Γ p).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t (lwSymmUncirc Γ p)]
    exact tw (lwSymmFrame c t Γ p) ℓe
  have key := oe1x_graph_E hG hz hu hm0 hzm Sp M hM (lwSymmFrame c t Γ p) (lwSymmFrameP c t p)
    (lwSymmFrameP_mem c t Γ p) x v (lwSymmFrameP_fst c t p _ _ hx) hv ℓe
  rw [e00, e0, key, map_add, map_add, tw, tw, lwSymm_cj_list_sum]
  have hS : lwSplit (lwSymmFrameP c t p).2 = (lwSplit p.2).map (lwSymmTwistP c t) :=
    lwSymm_lwSplit_twistP c t p.2
  rw [hS, List.map_map]
  simp only [Function.comp_def, lwSymm_cj_list_sum, ← tw]

end FormEdge

/-! ### (c) The `GG` expansion `(Oe2x)` at a pair of edges `G_{xy} G_{y'x}`, `Ḡ_{xy} Ḡ_{y'x}` and their transposes -/

section FormGG

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **Form (c): `(Oe2x)` at the selected pair `p.1`, `q.1` at the internal vertex `x`** (`7_8:334-349`; `strat_local` Step 3):
two solid edges of the same colour at `x`, one out and one in, in either order of the list.  The selector `(c, t)`:
`lwSymmTwistS c t p.1 = ⟨true, p.1.circ, inr x, y⟩` and `lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', inr x⟩`, i.e.
`c = true` iff the pair is red (`Ḡ_{xy} Ḡ_{y'x}`), `t = true` iff `p.1` is the in-edge (`G_{yx} G_{xy'}`, the transposed pair);
`y ≠ inr x`.  The frame is `Γ' = lwSymmFrame2 c t Γ p q`.  `E Γ.val = Σ_{k=1}^8 E (R_k)^{(c,t)}.val` with the eight terms of
`oe2x_graph_E` for `Γ'` (`R7`, `R8` summed over `q'' ∈ lwSplit q.2`, `q''` twisted).  Counters: `lwSymm_oe2x_ord`. -/
theorem lwSymm_oe2x_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) (hSpT : Spᵀ = Sp)
    (hM : ∀ a, M a a = m) (hM0 : ∀ a b, a ≠ b → M a b = 0)
    (Γ : LGraph E I) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x)
    (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hq : q ∈ lwSplit p.2) (c t : Bool)
    (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
    (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩)
    (hX1 : p.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = p.1.src ∧ d.y = p.1.dst) ∨ (d.x = p.1.dst ∧ d.y = p.1.src)))
    (hX2 : q.1.circ = true → ∃ d ∈ Γ.dotted, d.eq = false ∧
      ((d.x = q.1.src ∧ d.y = q.1.dst) ∨ (d.x = q.1.dst ∧ d.y = q.1.src)))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (lwSymmOe2xR1 c t m Γ p q x y hy).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe2xR2 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe2xR3 c t m Γ p q x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe2xR4 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe2xR5 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (lwSymmOe2xR6 c t m Γ p q x y y').val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit q.2).map fun q' => ∫ ω, (lwSymmOe2xR7 c t m Γ p q x y y' q').val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit q.2).map fun q' => ∫ ω, (lwSymmOe2xR8 c t m Γ p q x y y' q').val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  simp only [lwSymmOe2xR1, lwSymmOe2xR2, lwSymmOe2xR3, lwSymmOe2xR4, lwSymmOe2xR5, lwSymmOe2xR6,
    lwSymmOe2xR7, lwSymmOe2xR8]
  have hMs := lwSymm_M_symm hM0
  have tw : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph E' I') (ℓe' : E' → Idx d (sz.L n) (sz.W n)),
      ∫ ω, (lwSymmTwistG c t T).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz) =
        lwSymmCj c (∫ ω, T.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe' ∂(Sizes.seqP sz)) :=
    fun T ℓe' => lwSymm_twist_integral (lwSymm_lwS_real sz n u) hMs (lwSymm_lwS_symm sz n u) hSpT c t T ℓe'
  have e00 : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (lwSymmUncirc2 Γ p q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    exact (lwSymmUncirc2_val (lwSampleData sz n z u M (lwS sz n u) Sp ω) hM0 Γ p q hp hq hX1 hX2 ℓe).symm
  have e0 : ∫ ω, (lwSymmUncirc2 Γ p q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      lwSymmCj c (∫ ω, (lwSymmFrame2 c t Γ p q).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe
        ∂(Sizes.seqP sz)) := by
    conv_lhs => rw [← lwSymmTwistG_invol c t (lwSymmUncirc2 Γ p q)]
    exact tw (lwSymmFrame2 c t Γ p q) ℓe
  have key := oe2x_graph_E hG hz hu hm0 hzm Sp M hSp hM (lwSymmFrame2 c t Γ p q) x y y' hy
    (lwSymmFrame2P c t p q) (lwSymmFrame2P_mem c t Γ p q) (lwSymmFrameP_fst c t p _ _ hp1)
    (lwSymmFrame2Q c t q) (lwSymmFrame2Q_mem c t p q) (lwSymmFrameP_fst c t q _ _ hq1) ℓe
  rw [e00, e0, key]
  have hS : lwSplit (lwSymmFrame2Q c t q).2 = (lwSplit q.2).map (lwSymmTwistP c t) :=
    lwSymm_lwSplit_twistP c t q.2
  rw [hS]
  simp only [map_add, lwSymm_cj_list_sum, List.map_map, Function.comp_def, ← tw]

end FormGG

/-! ### The counters and `ord` of every output of the forms

The twist keeps the counters (`lwSymmTwistG_counters`) and the frame keeps those of `Γ` (`lwSymmFrame_counters`), so the
counter changes of the merged terms hold for the twisted outputs.  `ord` is `n_S + 2 (n_W - n_V)`. -/

section FormCounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwSymm_ord_of_cnt {E' I' E'' I'' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    [Fintype E''] [DecidableEq E''] [Fintype I''] [DecidableEq I''] (T : LGraph E' I') (Γ : LGraph E'' I'')
    (a b e : ℕ) (hS : T.nS = Γ.nS + a) (hW : T.nW = Γ.nW + b) (hV : T.nV = Γ.nV + e) :
    ord T.counters = ord Γ.counters + ((a : ℤ) + 2 * ((b : ℤ) - (e : ℤ))) := by
  simp only [LGraph.counters, ord, hS, hW, hV]
  push_cast
  ring

/-- The twisted graph has the counter changes of the graph. -/
theorem lwSymm_cnt5 (c t : Bool) {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (T : LGraph E' I') (Γ : LGraph E I) (a b e : ℕ) (hS : T.nS = Γ.nS + a) (hW : T.nW = Γ.nW + b)
    (hV : T.nV = Γ.nV + e) (hM : T.nM = Γ.nM) :
    (lwSymmTwistG c t T).nS = Γ.nS + a ∧ (lwSymmTwistG c t T).nW = Γ.nW + b ∧
      (lwSymmTwistG c t T).nV = Γ.nV + e ∧ (lwSymmTwistG c t T).nM = Γ.nM ∧
      ord (lwSymmTwistG c t T).counters = ord Γ.counters + ((a : ℤ) + 2 * ((b : ℤ) - (e : ℤ))) := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmTwistG_counters c t T
  refine ⟨h1.trans hS, h2.trans hW, h3.trans hV, h4.trans hM, ?_⟩
  exact lwSymm_ord_of_cnt _ Γ a b e (h1.trans hS) (h2.trans hW) (h3.trans hV)

/-- **Form (a): the counters and `ord` of the four families**: `Δ(n_S, n_W, n_V, n_M) = (1, 1, 1, 0)`, `(1, 2, 2, 0)`,
`(1, 1, 1, 0)`, `(1, 2, 2, 0)`, so `ord + 1` each (as `owxT1_ord` ... `owxT4_ord`). -/
theorem lwSymm_weight_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : E ⊕ I) (c t : Bool) :
    ((lwSymmOwxT1 c t m Γ x).nS = Γ.nS + 1 ∧ (lwSymmOwxT1 c t m Γ x).nW = Γ.nW + 1 ∧
        (lwSymmOwxT1 c t m Γ x).nV = Γ.nV + 1 ∧ (lwSymmOwxT1 c t m Γ x).nM = Γ.nM ∧
        ord (lwSymmOwxT1 c t m Γ x).counters = ord Γ.counters + 1) ∧
      ((lwSymmOwxT2 c t m Γ p x).nS = Γ.nS + 1 ∧ (lwSymmOwxT2 c t m Γ p x).nW = Γ.nW + 2 ∧
        (lwSymmOwxT2 c t m Γ p x).nV = Γ.nV + 2 ∧ (lwSymmOwxT2 c t m Γ p x).nM = Γ.nM ∧
        ord (lwSymmOwxT2 c t m Γ p x).counters = ord Γ.counters + 1) ∧
      (∀ q ∈ lwSplit p.2, (lwSymmOwxT3 c t m Γ x q).nS = Γ.nS + 1 ∧ (lwSymmOwxT3 c t m Γ x q).nW = Γ.nW + 1 ∧
        (lwSymmOwxT3 c t m Γ x q).nV = Γ.nV + 1 ∧ (lwSymmOwxT3 c t m Γ x q).nM = Γ.nM ∧
        ord (lwSymmOwxT3 c t m Γ x q).counters = ord Γ.counters + 1) ∧
      (∀ q ∈ lwSplit p.2, (lwSymmOwxT4 c t m Γ x q).nS = Γ.nS + 1 ∧ (lwSymmOwxT4 c t m Γ x q).nW = Γ.nW + 2 ∧
        (lwSymmOwxT4 c t m Γ x q).nV = Γ.nV + 2 ∧ (lwSymmOwxT4 c t m Γ x q).nM = Γ.nM ∧
        ord (lwSymmOwxT4 c t m Γ x q).counters = ord Γ.counters + 1) := by
  obtain ⟨g1, g2, g3, g4⟩ := lwSymmTwistG_counters c t Γ
  have hp' : lwSymmTwistP c t p ∈ lwSplit (lwSymmTwistG c t Γ).solid := by
    rw [lwSymmTwistG_solid, lwSymm_lwSplit_twistP]
    exact List.mem_map_of_mem hp
  refine ⟨?_, ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := owxET1_counters m (lwSymmTwistG c t Γ) x
    have := lwSymm_cnt5 c t (owxET1 m (lwSymmTwistG c t Γ) x) Γ 1 1 1 (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOwxT1] using this
  · obtain ⟨a1, a2, a3, a4⟩ := owxET2_counters m (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) hp' x
    have := lwSymm_cnt5 c t (owxET2 m (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) x) Γ 1 2 2
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOwxT2] using this
  · have hq' : lwSymmTwistP c t q ∈ lwSplit (lwSymmTwistP c t p).2 := by
      rw [show (lwSymmTwistP c t p).2 = p.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
      exact List.mem_map_of_mem hq
    obtain ⟨a1, a2, a3, a4⟩ := owxET3_counters m (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) hp' x _ hq'
    have := lwSymm_cnt5 c t (owxET3 m (lwSymmTwistG c t Γ) x (lwSymmTwistP c t q)) Γ 1 1 1
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOwxT3] using this
  · have hq' : lwSymmTwistP c t q ∈ lwSplit (lwSymmTwistP c t p).2 := by
      rw [show (lwSymmTwistP c t p).2 = p.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
      exact List.mem_map_of_mem hq
    obtain ⟨a1, a2, a3, a4⟩ := owxET4_counters m (lwSymmTwistG c t Γ) (lwSymmTwistP c t p) hp' x _ hq'
    have := lwSymm_cnt5 c t (owxET4 m (lwSymmTwistG c t Γ) x (lwSymmTwistP c t q)) Γ 1 2 2
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOwxT4] using this


theorem lwSymmFrame_cnt (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) :
    (lwSymmFrame c t Γ p).nS = Γ.nS ∧ (lwSymmFrame c t Γ p).nW = Γ.nW ∧ (lwSymmFrame c t Γ p).nV = Γ.nV ∧
      (lwSymmFrame c t Γ p).nM = Γ.nM := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmUncirc_counters Γ p hp
  obtain ⟨g1, g2, g3, g4⟩ := lwSymmTwistG_counters c t (lwSymmUncirc Γ p)
  exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩

theorem lwSymmFrame2_cnt (c t : Bool) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (lwSymmFrame2 c t Γ p q).nS = Γ.nS ∧ (lwSymmFrame2 c t Γ p q).nW = Γ.nW ∧
      (lwSymmFrame2 c t Γ p q).nV = Γ.nV ∧ (lwSymmFrame2 c t Γ p q).nM = Γ.nM := by
  obtain ⟨h1, h2, h3, h4⟩ := lwSymmUncirc2_counters Γ p q hp hq
  obtain ⟨g1, g2, g3, g4⟩ := lwSymmTwistG_counters c t (lwSymmUncirc2 Γ p q)
  exact ⟨g1.trans h1, g2.trans h2, g3.trans h3, g4.trans h4⟩

/-- **Form (b): the counters and `ord` of the outputs.**  Term 1 (`x` merged into `y₁`): `Δ(n_S, n_W, n_V) = (-1, 0, -1)`,
`n_M` does not grow, `ord + 1`; the `owxT1` term `ord + 1`; the derivative terms: `n_W + 1`, `n_V + 1`, `n_M` kept, `n_S + 1`
except for the two graphs with a loop replaced by a constant, where `n_S` and `ord` stay: only if the twisted edge `q.1^{(c,t)}`
is a red out-edge or a blue in-edge of `x` (exactly one of the colour and the direction of `q.1` at `x` differs from that of the
selected edge, which is the blue out-edge in the frame). -/
theorem lwSymm_oe1x_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (v : E ⊕ I) (hv : v ≠ Sum.inr x) (c t : Bool) :
    ((lwSymmOe1xT1 c t m Γ p x v hv).nS + 1 = Γ.nS ∧ (lwSymmOe1xT1 c t m Γ p x v hv).nW = Γ.nW ∧
        (lwSymmOe1xT1 c t m Γ p x v hv).nV + 1 = Γ.nV ∧ (lwSymmOe1xT1 c t m Γ p x v hv).nM ≤ Γ.nM ∧
        ord (lwSymmOe1xT1 c t m Γ p x v hv).counters = ord Γ.counters + 1) ∧
      ((lwSymmOe1xOwx c t m Γ p x).nS = Γ.nS + 1 ∧ (lwSymmOe1xOwx c t m Γ p x).nW = Γ.nW + 1 ∧
        (lwSymmOe1xOwx c t m Γ p x).nV = Γ.nV + 1 ∧ (lwSymmOe1xOwx c t m Γ p x).nM = Γ.nM ∧
        ord (lwSymmOe1xOwx c t m Γ p x).counters = ord Γ.counters + 1) ∧
      (∀ q ∈ lwSplit p.2, ∀ T ∈ lwSymmOe1xDs c t m Γ p x v q,
        T.nW = Γ.nW + 1 ∧ T.nV = Γ.nV + 1 ∧ T.nM = Γ.nM ∧
        (T.nS = Γ.nS + 1 ∨ (T.nS = Γ.nS ∧
          (((lwSymmTwistS c t q.1).σ = false ∧ (lwSymmTwistS c t q.1).src = Sum.inr x) ∨
            ((lwSymmTwistS c t q.1).σ = true ∧ (lwSymmTwistS c t q.1).dst = Sum.inr x)))) ∧
        (ord T.counters = ord Γ.counters + 1 ∨ (ord T.counters = ord Γ.counters ∧
          (((lwSymmTwistS c t q.1).σ = false ∧ (lwSymmTwistS c t q.1).src = Sum.inr x) ∨
            ((lwSymmTwistS c t q.1).σ = true ∧ (lwSymmTwistS c t q.1).dst = Sum.inr x))))) := by
  obtain ⟨g1, g2, g3, g4⟩ := lwSymmFrame_cnt c t Γ p hp
  have hp' := lwSymmFrameP_mem c t Γ p
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := oe1xT1_counters m (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) hp' x v hv
    obtain ⟨b1, b2, b3, b4⟩ := lwSymmTwistG_counters c t (oe1xT1 m (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) x v hv)
    simp only [lwSymmOe1xT1, LGraph.counters, ord]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · obtain ⟨a1, a2, a3, a4⟩ := owxT1_counters m (lwSymmFrame c t Γ p) x
    have := lwSymm_cnt5 c t (owxT1 m (lwSymmFrame c t Γ p) x) Γ 1 1 1 (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe1xOwx] using this
  · intro q hq T hT
    have hq' : lwSymmTwistP c t q ∈ lwSplit (lwSymmFrameP c t p).2 := by
      rw [show (lwSymmFrameP c t p).2 = p.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
      exact List.mem_map_of_mem hq
    simp only [lwSymmOe1xDs, List.mem_map] at hT
    obtain ⟨T0, hT0, rfl⟩ := hT
    obtain ⟨a1, a2, a3, a4⟩ := oe1xDs_counters m (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) hp' x v
      (lwSymmTwistP c t q) hq' T0 hT0
    have a5 := oe1xDs_ord m (lwSymmFrame c t Γ p) (lwSymmFrameP c t p) hp' x v (lwSymmTwistP c t q) hq' T0 hT0
    obtain ⟨b1, b2, b3, b4⟩ := lwSymmTwistG_counters c t T0
    simp only [LGraph.counters, ord] at a5 ⊢
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rcases a4 with h | ⟨h, hc⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hc⟩
    · rcases a5 with h | ⟨h, hc⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hc⟩


/-- **Form (c): the counters and `ord` of the eight families** (`ord + 1` each, `oe2xR1_ord` ... `oe2xR8_ord`): `R1`
`Δ(n_S, n_W, n_V) = (-1, 0, -1)`, `R2` `(-1, 1, 0)`, both with `n_M` not growing; `R3`, `R5`, `R7` `(1, 1, 1, 0)`;
`R4`, `R6`, `R8` `(1, 2, 2, 0)`. -/
theorem lwSymm_oe2x_counters (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (x : I) (y y' : E ⊕ I) (hy : y ≠ Sum.inr x) (c t : Bool) :
    ((lwSymmOe2xR1 c t m Γ p q x y hy).nS + 1 = Γ.nS ∧ (lwSymmOe2xR1 c t m Γ p q x y hy).nW = Γ.nW ∧
        (lwSymmOe2xR1 c t m Γ p q x y hy).nV + 1 = Γ.nV ∧ (lwSymmOe2xR1 c t m Γ p q x y hy).nM ≤ Γ.nM ∧
        ord (lwSymmOe2xR1 c t m Γ p q x y hy).counters = ord Γ.counters + 1) ∧
      ((lwSymmOe2xR2 c t m Γ p q x y y').nS + 1 = Γ.nS ∧ (lwSymmOe2xR2 c t m Γ p q x y y').nW = Γ.nW + 1 ∧
        (lwSymmOe2xR2 c t m Γ p q x y y').nV = Γ.nV ∧ (lwSymmOe2xR2 c t m Γ p q x y y').nM ≤ Γ.nM ∧
        ord (lwSymmOe2xR2 c t m Γ p q x y y').counters = ord Γ.counters + 1) ∧
      ((lwSymmOe2xR3 c t m Γ p q x).nS = Γ.nS + 1 ∧ (lwSymmOe2xR3 c t m Γ p q x).nW = Γ.nW + 1 ∧
        (lwSymmOe2xR3 c t m Γ p q x).nV = Γ.nV + 1 ∧ (lwSymmOe2xR3 c t m Γ p q x).nM = Γ.nM ∧
        ord (lwSymmOe2xR3 c t m Γ p q x).counters = ord Γ.counters + 1) ∧
      ((lwSymmOe2xR4 c t m Γ p q x y y').nS = Γ.nS + 1 ∧ (lwSymmOe2xR4 c t m Γ p q x y y').nW = Γ.nW + 2 ∧
        (lwSymmOe2xR4 c t m Γ p q x y y').nV = Γ.nV + 2 ∧ (lwSymmOe2xR4 c t m Γ p q x y y').nM = Γ.nM ∧
        ord (lwSymmOe2xR4 c t m Γ p q x y y').counters = ord Γ.counters + 1) ∧
      ((lwSymmOe2xR5 c t m Γ p q x y y').nS = Γ.nS + 1 ∧ (lwSymmOe2xR5 c t m Γ p q x y y').nW = Γ.nW + 1 ∧
        (lwSymmOe2xR5 c t m Γ p q x y y').nV = Γ.nV + 1 ∧ (lwSymmOe2xR5 c t m Γ p q x y y').nM = Γ.nM ∧
        ord (lwSymmOe2xR5 c t m Γ p q x y y').counters = ord Γ.counters + 1) ∧
      ((lwSymmOe2xR6 c t m Γ p q x y y').nS = Γ.nS + 1 ∧ (lwSymmOe2xR6 c t m Γ p q x y y').nW = Γ.nW + 2 ∧
        (lwSymmOe2xR6 c t m Γ p q x y y').nV = Γ.nV + 2 ∧ (lwSymmOe2xR6 c t m Γ p q x y y').nM = Γ.nM ∧
        ord (lwSymmOe2xR6 c t m Γ p q x y y').counters = ord Γ.counters + 1) ∧
      (∀ q' ∈ lwSplit q.2, (lwSymmOe2xR7 c t m Γ p q x y y' q').nS = Γ.nS + 1 ∧
        (lwSymmOe2xR7 c t m Γ p q x y y' q').nW = Γ.nW + 1 ∧ (lwSymmOe2xR7 c t m Γ p q x y y' q').nV = Γ.nV + 1 ∧
        (lwSymmOe2xR7 c t m Γ p q x y y' q').nM = Γ.nM ∧
        ord (lwSymmOe2xR7 c t m Γ p q x y y' q').counters = ord Γ.counters + 1) ∧
      (∀ q' ∈ lwSplit q.2, (lwSymmOe2xR8 c t m Γ p q x y y' q').nS = Γ.nS + 1 ∧
        (lwSymmOe2xR8 c t m Γ p q x y y' q').nW = Γ.nW + 2 ∧ (lwSymmOe2xR8 c t m Γ p q x y y' q').nV = Γ.nV + 2 ∧
        (lwSymmOe2xR8 c t m Γ p q x y y' q').nM = Γ.nM ∧
        ord (lwSymmOe2xR8 c t m Γ p q x y y' q').counters = ord Γ.counters + 1) := by
  obtain ⟨g1, g2, g3, g4⟩ := lwSymmFrame2_cnt c t Γ p q hp hq
  have hp' := lwSymmFrame2P_mem c t Γ p q
  have hq' := lwSymmFrame2Q_mem c t p q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q' hq'' => ?_, fun q' hq'' => ?_⟩
  · obtain ⟨a1, a2, a3, a4⟩ := oe2xR1_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp' x y hy
    obtain ⟨b1, b2, b3, b4⟩ := lwSymmTwistG_counters c t (oe2xR1 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) x y hy)
    simp only [lwSymmOe2xR1, LGraph.counters, ord]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · obtain ⟨a1, a2, a3, a4⟩ := oe2xR2_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y'
    obtain ⟨b1, b2, b3, b4⟩ := lwSymmTwistG_counters c t (oe2xR2 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y')
    simp only [lwSymmOe2xR2, LGraph.counters, ord]
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  · obtain ⟨a1, a2, a3, a4⟩ := owxT1_counters m (lwSymmFrame2 c t Γ p q) x
    have := lwSymm_cnt5 c t (owxT1 m (lwSymmFrame2 c t Γ p q) x) Γ 1 1 1 (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR3] using this
  · obtain ⟨a1, a2, a3, a4⟩ := oe2xR4_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y'
    have := lwSymm_cnt5 c t (oe2xR4 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y') Γ 1 2 2
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR4] using this
  · obtain ⟨a1, a2, a3, a4⟩ := oe2xR5_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y'
    have := lwSymm_cnt5 c t (oe2xR5 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y') Γ 1 1 1
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR5] using this
  · obtain ⟨a1, a2, a3, a4⟩ := oe2xR6_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y'
    have := lwSymm_cnt5 c t (oe2xR6 m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2Q c t q) x y y') Γ 1 2 2
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR6] using this
  · have hq3 : lwSymmTwistP c t q' ∈ lwSplit (lwSymmFrame2Q c t q).2 := by
      rw [show (lwSymmFrame2Q c t q).2 = q.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
      exact List.mem_map_of_mem hq''
    obtain ⟨a1, a2, a3, a4⟩ := oe2xR7_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y' (lwSymmTwistP c t q') hq3
    have := lwSymm_cnt5 c t (oe2xR7 m (lwSymmFrame2 c t Γ p q) x y y' (lwSymmTwistP c t q')) Γ 1 1 1
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR7] using this
  · have hq3 : lwSymmTwistP c t q' ∈ lwSplit (lwSymmFrame2Q c t q).2 := by
      rw [show (lwSymmFrame2Q c t q).2 = q.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP]
      exact List.mem_map_of_mem hq''
    obtain ⟨a1, a2, a3, a4⟩ := oe2xR8_counters m (lwSymmFrame2 c t Γ p q) (lwSymmFrame2P c t p q) hp'
      (lwSymmFrame2Q c t q) hq' x y y' (lwSymmTwistP c t q') hq3
    have := lwSymm_cnt5 c t (oe2xR8 m (lwSymmFrame2 c t Γ p q) x y y' (lwSymmTwistP c t q')) Γ 1 2 2
      (by omega) (by omega) (by omega) (by omega)
    simpa [lwSymmOe2xR8] using this

end FormCounters

/-! ### The selector: which `(c, t)` for which edge -/

section Selector

variable {V : Type*}

theorem lwSymmTwistS_eq (c t : Bool) (e : SEdge V) :
    lwSymmTwistS c t e = ⟨if c then !e.σ else e.σ, e.circ, if t then e.dst else e.src,
      if t then e.src else e.dst⟩ := by
  cases e; cases c <;> cases t <;> rfl

/-- **Selector for an out-edge** `e` of `x`: `(c, t) = (red, false)` makes it the blue out-edge `G_{x e.dst}`. -/
theorem lwSymm_twist_out (e : SEdge V) (x : V) (hs : e.src = x) :
    lwSymmTwistS (!e.σ) false e = ⟨true, e.circ, x, e.dst⟩ := by
  rw [lwSymmTwistS_eq]
  cases hσ : e.σ <;> simp [hs]

/-- **Selector for an in-edge** `e` of `x`: `(c, t) = (red, true)` makes it the blue out-edge `G_{x e.src}`. -/
theorem lwSymm_twist_in (e : SEdge V) (x : V) (hd : e.dst = x) :
    lwSymmTwistS (!e.σ) true e = ⟨true, e.circ, x, e.src⟩ := by
  rw [lwSymmTwistS_eq]
  cases hσ : e.σ <;> simp [hd]

/-- The edge of the pair that is the blue in-edge `G_{y'x}` of `x` after the twist `(!p.σ, false)`: an in-edge of the same
colour. -/
theorem lwSymm_twist_pair_in (p e : SEdge V) (x : V) (hd : e.dst = x) (hσ : e.σ = p.σ) :
    lwSymmTwistS (!p.σ) false e = ⟨true, e.circ, e.src, x⟩ := by
  rw [lwSymmTwistS_eq, hσ]
  cases p.σ <;> simp [hd]

/-- The edge of the pair that is the blue in-edge after the twist `(!p.σ, true)`: an out-edge of the same colour. -/
theorem lwSymm_twist_pair_out (p e : SEdge V) (x : V) (hs : e.src = x) (hσ : e.σ = p.σ) :
    lwSymmTwistS (!p.σ) true e = ⟨true, e.circ, e.dst, x⟩ := by
  rw [lwSymmTwistS_eq, hσ]
  cases p.σ <;> simp [hs]

/-- A light-weight `⟨σ, true, x, x⟩` has the selector `(c, t) = (!σ, false)`. -/
theorem lwSymm_twist_weight (e : SEdge V) (x : V) (hs : e.src = x) (hd : e.dst = x) (hc : e.circ = true) :
    lwSymmTwistS (!e.σ) false e = ⟨true, true, x, x⟩ := by
  rw [lwSymm_twist_out e x hs, hc, hd]

/-- The twist keeps the ends of a solid edge as a set: loops stay loops, the degree of every vertex is unchanged (the
measure `(w, Φ, n_S)` of the termination argument of `strat_local` is twist invariant). -/
theorem lwSymmTwistS_loop (c t : Bool) (e : SEdge V) :
    (lwSymmTwistS c t e).src = (lwSymmTwistS c t e).dst ↔ e.src = e.dst := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [eq_comm]

theorem lwSymmTwistS_at (c t : Bool) (e : SEdge V) (x : V) :
    ((lwSymmTwistS c t e).src = x ∨ (lwSymmTwistS c t e).dst = x) ↔ (e.src = x ∨ e.dst = x) := by
  rw [lwSymmTwistS_eq]
  cases t <;> simp [or_comm]

/-- **A selector exists for every non-loop edge at `x`**: `(c, t) = (red, in-edge)` and the far end `v ≠ x`. -/
theorem lwSymm_selector_edge (e : SEdge V) (x : V) (h : (e.src = x ∧ e.dst ≠ x) ∨ (e.dst = x ∧ e.src ≠ x)) :
    ∃ (c t : Bool) (v : V), v ≠ x ∧ lwSymmTwistS c t e = ⟨true, e.circ, x, v⟩ := by
  rcases h with ⟨hs, hd⟩ | ⟨hd, hs⟩
  · exact ⟨!e.σ, false, e.dst, hd, lwSymm_twist_out e x hs⟩
  · exact ⟨!e.σ, true, e.src, hs, lwSymm_twist_in e x hd⟩

/-- **A selector exists for every pair of edges of one colour at `x`, one out and one in** (either order). -/
theorem lwSymm_selector_pair (p q : SEdge V) (x : V) (hσ : q.σ = p.σ)
    (h : (p.src = x ∧ p.dst ≠ x ∧ q.dst = x) ∨ (p.dst = x ∧ p.src ≠ x ∧ q.src = x)) :
    ∃ (c t : Bool) (y y' : V), y ≠ x ∧ lwSymmTwistS c t p = ⟨true, p.circ, x, y⟩ ∧
      lwSymmTwistS c t q = ⟨true, q.circ, y', x⟩ := by
  rcases h with ⟨hs, hd, hq⟩ | ⟨hd, hs, hq⟩
  · exact ⟨!p.σ, false, p.dst, q.src, hd, lwSymm_twist_out p x hs, lwSymm_twist_pair_in p q x hq hσ⟩
  · exact ⟨!p.σ, true, p.src, q.dst, hs, lwSymm_twist_in p x hd, lwSymm_twist_pair_out p q x hq hσ⟩

end Selector

/-! ## 6. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`

The size sequence `lwWxInstSz`, the flow data `z_{1/2} = i/2`, `m = i`, `M = m I`, `S = lwS`, `S⁺ = S (1 - m² S)⁻¹` of the merged
instances (`Graph/LWWeightExp.lean`); `gaussIBP` is the merged proof.  Every deterministic hypothesis is discharged, the
new ones (`M a b = 0`, `S⁺ᵀ = S⁺`) by `lwSymm_inst_hM0`, `lwSymm_inst_hSpT`. -/

section Instances

open RBM.Gauss.SizesInst

theorem lwSymm_inst_hM0 (a b : Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) (h : a ≠ b) : lwWxInstM a b = 0 := by
  simp [lwWxInstM, h]

theorem lwSymm_inst_hMs : lwWxInstMᵀ = lwWxInstM := lwSymm_M_symm lwSymm_inst_hM0

theorem lwSymm_inst_hSpT : lwWxInstSpᵀ = lwWxInstSp :=
  lwSymm_lwSplus_symm (sz := lwWxInstSz) (n := 0) (by norm_num) lwWx_inst_norm

/-- The labels of the two external vertices of the instances. -/
def lwSymmInstL : Fin 2 → Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0) := ![0, Pi.single 0 1]

/-! ### (1) Conjugation on a concrete record with both colours -/

/-- A graph with both colours, a circled weight of each colour, a black waved edge, both coloured waved edges, a `×`-dotted
edge and the complex coefficient `1 + i`; one internal vertex, two external. -/
def lwSymmInstGraph : LGraph (Fin 2) (Fin 1) where
  solid := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨false, false, Sum.inr 0, Sum.inl 1⟩,
    ⟨true, true, Sum.inr 0, Sum.inr 0⟩, ⟨false, true, Sum.inl 0, Sum.inl 0⟩]
  waved := [⟨false, true, Sum.inr 0, Sum.inl 0⟩, ⟨true, true, Sum.inl 0, Sum.inr 0⟩,
    ⟨true, false, Sum.inr 0, Sum.inl 1⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inl 1⟩]
  coeff := 1 + Complex.I

/-- Data on `Fin 3` with complex `G`, `M = i·1`, a real symmetric `S` and a non-symmetric complex `S⁺`. -/
def lwSymmInstD : LData (Fin 3) where
  G := !![1 + Complex.I, 2, Complex.I; -1, 1 - Complex.I, 1 / 2; Complex.I, 3, 2 + Complex.I]
  M := Matrix.of fun a b => if a = b then Complex.I else 0
  S := !![1 / 2, 1 / 4, 0; 1 / 4, 1 / 2, 1 / 4; 0, 1 / 4, 1 / 2]
  Sp := !![Complex.I, 1, 2; 0, 1, Complex.I; 1, 0, 1]

theorem lwSymmInstD_hS (i j : Fin 3) : star (lwSymmInstD.S i j) = lwSymmInstD.S i j := by
  fin_cases i <;> fin_cases j <;> simp [lwSymmInstD]

/-- **Target 1 at the concrete record**: `conj (Γ.val D ℓe) = Γ.conj.val D ℓe` (the same data `D`, real `S`). -/
example : lwSymmInstGraph.conj.val lwSymmInstD ![0, 1] = star (lwSymmInstGraph.val lwSymmInstD ![0, 1]) :=
  LGraph.val_conj lwSymmInstD lwSymmInstD_hS lwSymmInstGraph _

/-- The conjugate is a different graph (the colours of all solid edges flip), with the same counters. -/
example : lwSymmInstGraph.conj ≠ lwSymmInstGraph ∧ lwSymmInstGraph.conj.counters = lwSymmInstGraph.counters := by
  refine ⟨fun h => ?_, (lwSymmTwistG_counters_eq true false lwSymmInstGraph :)⟩
  have := congrArg LGraph.solid h
  simp [LGraph.conj, lwSymmInstGraph, SEdge.conj] at this

/-- `n_S, n_W, n_V, n_M` of the record and of its conjugate and transpose, computed. -/
example : (lwSymmInstGraph.nS, lwSymmInstGraph.nW, lwSymmInstGraph.nV, lwSymmInstGraph.nM) = (4, 3, 1, 0) ∧
    (lwSymmInstGraph.conj.nS, lwSymmInstGraph.conj.nW, lwSymmInstGraph.conj.nV, lwSymmInstGraph.conj.nM) = (4, 3, 1, 0) ∧
    (lwSymmInstGraph.transpose.nS, lwSymmInstGraph.transpose.nW, lwSymmInstGraph.transpose.nV,
      lwSymmInstGraph.transpose.nM) = (4, 3, 1, 0) := by
  decide

/-- The conjugate of the conjugate is the graph. -/
example : lwSymmInstGraph.conj.conj = lwSymmInstGraph := lwSymm_conj_conj _


/-! ### (2) Transposition on `p2Graph` -/

/-- **Target 2 on `p2Graph`** (`E|f_xy|²` of `(eq:p=2graph)`: both colours, black waved edges, `×`-dotted edges): `E Γᵀ.val =
E Γ.val` at the instance data, for the two external labels `0 ≠ Pi.single 0 1`.  `M`, `S`, `S⁺` symmetric. -/
example :
    ∫ ω, p2Graph.transpose.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
        (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      ∫ ω, p2Graph.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
        (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) :=
  lwSymm_transpose_integral lwSymm_inst_hMs (lwSymm_lwS_symm lwWxInstSz 0 (1 / 2)) lwSymm_inst_hSpT p2Graph _

/-- The same with conjugation: `E p2Graph.conj.val = conj E p2Graph.val`. -/
example :
    ∫ ω, p2Graph.conj.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
        (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      star (∫ ω, p2Graph.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
        (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)) :=
  lwSymm_conj_integral (lwSymm_lwS_real lwWxInstSz 0 (1 / 2)) p2Graph _

/-- The flip is not the identity (the imaginary-part coordinates of the constant sample `1` change sign) and it
transposes the resolvent at the instance, for every sample. -/
example : (∃ ω : Sizes.SeqΩ lwWxInstSz, lwSymmFlip lwWxInstSz ω ≠ ω) ∧
    ∀ ω : Sizes.SeqΩ lwWxInstSz, lwGm lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) (lwSymmFlip lwWxInstSz ω) =
      (lwGm lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) ω)ᵀ := by
  refine ⟨⟨fun _ => 1, fun h => ?_⟩, fun ω => lwSymm_lwGm_flip lwWxInstSz 0 _ _ ω⟩
  have := congrFun h ⟨0, (0, 0, false)⟩
  simp [lwSymmFlip, lwSymmSgn] at this
  linarith

/-! ### (3) `(Owx)` at an external vertex -/

/-- The graph `Ǧ_{aa} G_{ax}` with the **external** vertex `a = inl 0` carrying the light-weight, and the internal vertex
`x = inr 0`. -/
def lwSymmInstExtGraph (m : ℂ) : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, true, Sum.inl 0, Sum.inl 0⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := []
  coeff := m

theorem lwSymmInstExt_mem (m : ℂ) :
    ((⟨true, true, Sum.inl 0, Sum.inl 0⟩ : SEdge (Fin 1 ⊕ Fin 1)), [⟨true, false, Sum.inl 0, Sum.inr 0⟩]) ∈
      lwSplit (lwSymmInstExtGraph m).solid := by
  simp [lwSplit, lwSymmInstExtGraph]

/-- **Target 3 at an external vertex**: the identity of expectations of values for `Ǧ_{aa} G_{ax}`, the weight at the external
vertex `a = inl 0` (label `0`), at the instance data of T2107. -/
example := owxE_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwWx_inst_hM (lwSymmInstExtGraph (mE 0))
  (⟨true, true, Sum.inl 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩]) (lwSymmInstExt_mem _)
  (Sum.inl 0) rfl (fun _ => 0)

/-- The counters of `Γ` and of the four terms at the external vertex, computed: `Γ = (2, 0, 1, 1)`;
`owxET1 = (3, 1, 2, 1)`, `owxET2 = (3, 2, 3, 1)`, `owxET3 = (3, 1, 2, 1)`, `owxET4 = (3, 2, 3, 1)`: `n_M` is unchanged (the
leaves join the external molecule of `a`), `ord + 1`. -/
example :
    let Γ := lwSymmInstExtGraph 1
    let p : SEdge (Fin 1 ⊕ Fin 1) × List (SEdge (Fin 1 ⊕ Fin 1)) :=
      (⟨true, true, Sum.inl 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩])
    let q : SEdge (Fin 1 ⊕ Fin 1) × List (SEdge (Fin 1 ⊕ Fin 1)) := (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [])
    (Γ.nS, Γ.nW, Γ.nV, Γ.nM) = (2, 0, 1, 1) ∧
    ((owxET1 1 Γ (Sum.inl 0)).nS, (owxET1 1 Γ (Sum.inl 0)).nW, (owxET1 1 Γ (Sum.inl 0)).nV,
      (owxET1 1 Γ (Sum.inl 0)).nM) = (3, 1, 2, 1) ∧
    ((owxET2 1 Γ p (Sum.inl 0)).nS, (owxET2 1 Γ p (Sum.inl 0)).nW, (owxET2 1 Γ p (Sum.inl 0)).nV,
      (owxET2 1 Γ p (Sum.inl 0)).nM) = (3, 2, 3, 1) ∧
    ((owxET3 1 Γ (Sum.inl 0) q).nS, (owxET3 1 Γ (Sum.inl 0) q).nW, (owxET3 1 Γ (Sum.inl 0) q).nV,
      (owxET3 1 Γ (Sum.inl 0) q).nM) = (3, 1, 2, 1) ∧
    ((owxET4 1 Γ (Sum.inl 0) q).nS, (owxET4 1 Γ (Sum.inl 0) q).nW, (owxET4 1 Γ (Sum.inl 0) q).nV,
      (owxET4 1 Γ (Sum.inl 0) q).nM) = (3, 2, 3, 1) := by
  decide


/-- The theorems `owxET*_ord` and the flip at the instance. -/
example := owxET1_ord (mE 0) (lwSymmInstExtGraph (mE 0)) (Sum.inl 0)

example := owxET2_ord (mE 0) (lwSymmInstExtGraph (mE 0))
  (⟨true, true, Sum.inl 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩]) (lwSymmInstExt_mem _) (Sum.inl 0)

example := owxET3_ord (mE 0) (lwSymmInstExtGraph (mE 0))
  (⟨true, true, Sum.inl 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩]) (lwSymmInstExt_mem _) (Sum.inl 0)
  (⟨true, false, Sum.inl 0, Sum.inr 0⟩, []) (by simp [lwSplit])

example := owxET4_ord (mE 0) (lwSymmInstExtGraph (mE 0))
  (⟨true, true, Sum.inl 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩]) (lwSymmInstExt_mem _) (Sum.inl 0)
  (⟨true, false, Sum.inl 0, Sum.inr 0⟩, []) (by simp [lwSplit])

example := lwSymm_flip_measurePreserving lwWxInstSz

/-! ### (4a) A red light-weight, external or internal -/

/-- `Ḡ̊_{aa} Ḡ_{ax}`: a **red** light-weight at the external vertex `a = inl 0`. -/
def lwSymmInstRedGraph (m : ℂ) : LGraph (Fin 1) (Fin 1) where
  solid := [⟨false, true, Sum.inl 0, Sum.inl 0⟩, ⟨false, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := []
  coeff := star m

/-- **Form (a), a red light-weight at an external vertex**: selector `(c, t) = (true, false)`. -/
example := lwSymm_weight_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 (lwSymmInstRedGraph (mE 0))
  (⟨false, true, Sum.inl 0, Sum.inl 0⟩, [⟨false, false, Sum.inl 0, Sum.inr 0⟩])
  (by simp [lwSplit, lwSymmInstRedGraph]) (Sum.inl 0) true false rfl (fun _ => 0)

/-- `Ḡ̊_{xx} Ḡ_{ax}`: a red light-weight at the **internal** vertex `x = inr 0`. -/
def lwSymmInstRedIntGraph (m : ℂ) : LGraph (Fin 1) (Fin 1) where
  solid := [⟨false, true, Sum.inr 0, Sum.inr 0⟩, ⟨false, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := []
  coeff := star m

/-- **Form (a), a red light-weight at an internal vertex**; the counters of the four families by `lwSymm_weight_counters`. -/
example := lwSymm_weight_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 (lwSymmInstRedIntGraph (mE 0))
  (⟨false, true, Sum.inr 0, Sum.inr 0⟩, [⟨false, false, Sum.inl 0, Sum.inr 0⟩])
  (by simp [lwSplit, lwSymmInstRedIntGraph]) (Sum.inr 0) true false rfl (fun _ => 0)

example := lwSymm_weight_counters (mE 0) (lwSymmInstRedGraph (mE 0))
  (⟨false, true, Sum.inl 0, Sum.inl 0⟩, [⟨false, false, Sum.inl 0, Sum.inr 0⟩])
  (by simp [lwSplit, lwSymmInstRedGraph]) (Sum.inl 0) true false

/-! ### (4b) `(Oe1x)` at a circled red in-edge -/

/-- `x = inr 0` with the circled red in-edge `(Ḡ-M)_{ax}` (selected), the blue out-edge `G_{xb}`, the blue in-edge `G_{bx}`, the
red out-edge `Ḡ_{xw}`, the red edge `Ḡ_{wa}`, the waved edge `S⁺_{xw}` and the `×`-dotted edge between `a` and `x`. -/
def lwSymmInstEdgeGraph (m : ℂ) : LGraph (Fin 2) (Fin 2) where
  solid := [⟨false, true, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩,
    ⟨true, false, Sum.inl 1, Sum.inr 0⟩, ⟨false, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 1, Sum.inl 0⟩]
  waved := [⟨false, true, Sum.inr 0, Sum.inr 1⟩]
  dotted := [⟨false, Sum.inl 0, Sum.inr 0⟩]
  coeff := m

/-- The selected edge `(Ḡ-M)_{ax}` and the other four. -/
def lwSymmInstEdgeP : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨false, true, Sum.inl 0, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 1⟩,
    ⟨true, false, Sum.inl 1, Sum.inr 0⟩, ⟨false, false, Sum.inr 0, Sum.inr 1⟩,
    ⟨false, false, Sum.inr 1, Sum.inl 0⟩])

theorem lwSymmInstEdge_mem (m : ℂ) : lwSymmInstEdgeP ∈ lwSplit (lwSymmInstEdgeGraph m).solid := by
  simp [lwSymmInstEdgeP, lwSymmInstEdgeGraph, lwSplit]

theorem lwSymmInstEdge_hv : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0 := by simp

/-- **Form (b), a circled red in-edge** (`c = t = true`: conjugate and transpose): the identity of expectations of values at
the instance data.  The circle of the selected edge is removed by `M a b = 0` and the `×`-dotted edge `a ≠ x`. -/
example := lwSymm_oe1x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 (lwSymmInstEdgeGraph (mE 0))
  lwSymmInstEdgeP (lwSymmInstEdge_mem _) 0 (Sum.inl 0) lwSymmInstEdge_hv true true rfl
  (fun _ => ⟨⟨false, Sum.inl 0, Sum.inr 0⟩, by simp [lwSymmInstEdgeGraph], rfl, Or.inl ⟨rfl, rfl⟩⟩) lwSymmInstL

/-- The selector of the selected edge `(Ḡ-M)_{ax}`, derived by `lwSymm_selector_edge`. -/
example : ∃ (c t : Bool) (v : Fin 2 ⊕ Fin 2), v ≠ Sum.inr 0 ∧
    lwSymmTwistS c t lwSymmInstEdgeP.1 = ⟨true, lwSymmInstEdgeP.1.circ, Sum.inr 0, v⟩ :=
  lwSymm_selector_edge _ (Sum.inr 0) (Or.inr ⟨rfl, by simp [lwSymmInstEdgeP]⟩)

/-- The counters of the outputs at the instance (`lwSymm_oe1x_counters`). -/
example := lwSymm_oe1x_counters (mE 0) (lwSymmInstEdgeGraph (mE 0)) lwSymmInstEdgeP (lwSymmInstEdge_mem _) 0
  (Sum.inl 0) lwSymmInstEdge_hv true true

/-- The numbers of derivative graphs for the four edges of the rest, in the frame of the circled red in-edge: the blue out-edge
`G_{xb}` becomes a red in-edge (1 graph), the blue in-edge `G_{bx}` a red out-edge (the pair `oe1xP5`, `oe1xP3`: 2), the red
out-edge `Ḡ_{xw}` a blue in-edge (the pair `oe1xP6`, `oe1xP4`: 2), the red edge `Ḡ_{wa}` an edge not at `x` (1). -/
example : ((lwSplit lwSymmInstEdgeP.2).map fun q =>
    (lwSymmOe1xDs true true 1 (lwSymmInstEdgeGraph 1) lwSymmInstEdgeP 0 (Sum.inl 0) q).length) = [1, 2, 2, 1] := by
  decide

/-! ### (4c) `(Oe2x)` at a transposed blue pair and at a red pair -/

/-- The transposed pair `(G_{bx}, G_{xa})` (the in-edge first) of the merged instance graph `G_{xa} G_{bx} G_{aw} Ḡ_{wb}`,
`x = inr 0`: `y = b = inl 1`, `y' = a = inl 0`, selector `(c, t) = (false, true)`. -/
def lwSymmInstPairP : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨true, false, Sum.inl 1, Sum.inr 0⟩, [⟨true, false, Sum.inr 0, Sum.inl 0⟩,
    ⟨true, false, Sum.inl 0, Sum.inr 1⟩, ⟨false, false, Sum.inr 1, Sum.inl 1⟩])

def lwSymmInstPairQ : SEdge (Fin 2 ⊕ Fin 2) × List (SEdge (Fin 2 ⊕ Fin 2)) :=
  (⟨true, false, Sum.inr 0, Sum.inl 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 1⟩, ⟨false, false, Sum.inr 1, Sum.inl 1⟩])

theorem lwSymmInstPair_hp (m : ℂ) : lwSymmInstPairP ∈ lwSplit (oe2xInstGraph m).solid := by
  simp [lwSplit, oe2xInstGraph, lwSymmInstPairP]

theorem lwSymmInstPair_hq : lwSymmInstPairQ ∈ lwSplit lwSymmInstPairP.2 := by
  simp [lwSplit, lwSymmInstPairP, lwSymmInstPairQ]

theorem lwSymmInstPair_hy : (Sum.inl 1 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0 := by simp

/-- **Form (c), the transposed blue pair `G_{yx} G_{xy'}`**: `E Γ.val = Σ_{k = 1}^8 E R_k^{(c,t)}.val`. -/
example := lwSymm_oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 (oe2xInstGraph (mE 0)) 0
  (Sum.inl 1) (Sum.inl 0) lwSymmInstPair_hy lwSymmInstPairP (lwSymmInstPair_hp _) lwSymmInstPairQ lwSymmInstPair_hq
  false true rfl rfl (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) lwSymmInstL

example := lwSymm_oe2x_counters (mE 0) (oe2xInstGraph (mE 0)) lwSymmInstPairP lwSymmInstPairQ (lwSymmInstPair_hp _)
  lwSymmInstPair_hq 0 (Sum.inl 1) (Sum.inl 0) lwSymmInstPair_hy false true

/-- `Ḡ_{xa} Ḡ_{bx} G_{ab}`: the red pair at `x = inr 0`. -/
def lwSymmInstRedPairGraph (m : ℂ) : LGraph (Fin 2) (Fin 1) where
  solid := [⟨false, false, Sum.inr 0, Sum.inl 0⟩, ⟨false, false, Sum.inl 1, Sum.inr 0⟩,
    ⟨true, false, Sum.inl 0, Sum.inl 1⟩]
  waved := []
  dotted := []
  coeff := star m

def lwSymmInstRedPairP : SEdge (Fin 2 ⊕ Fin 1) × List (SEdge (Fin 2 ⊕ Fin 1)) :=
  (⟨false, false, Sum.inr 0, Sum.inl 0⟩, [⟨false, false, Sum.inl 1, Sum.inr 0⟩, ⟨true, false, Sum.inl 0, Sum.inl 1⟩])

def lwSymmInstRedPairQ : SEdge (Fin 2 ⊕ Fin 1) × List (SEdge (Fin 2 ⊕ Fin 1)) :=
  (⟨false, false, Sum.inl 1, Sum.inr 0⟩, [⟨true, false, Sum.inl 0, Sum.inl 1⟩])

theorem lwSymmInstRedPair_hp (m : ℂ) : lwSymmInstRedPairP ∈ lwSplit (lwSymmInstRedPairGraph m).solid := by
  simp [lwSplit, lwSymmInstRedPairGraph, lwSymmInstRedPairP]

theorem lwSymmInstRedPair_hq : lwSymmInstRedPairQ ∈ lwSplit lwSymmInstRedPairP.2 := by
  simp [lwSplit, lwSymmInstRedPairP, lwSymmInstRedPairQ]

/-- **Form (c), the red pair `Ḡ_{xy} Ḡ_{y'x}`**: selector `(c, t) = (true, false)`, `y = a`, `y' = b`. -/
example := lwSymm_oe2x_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM lwSymm_inst_hM0 (lwSymmInstRedPairGraph (mE 0)) 0
  (Sum.inl 0) (Sum.inl 1) (by simp) lwSymmInstRedPairP (lwSymmInstRedPair_hp _) lwSymmInstRedPairQ
  lwSymmInstRedPair_hq true false rfl rfl (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  lwSymmInstL

end Instances

end RBM.Graph
