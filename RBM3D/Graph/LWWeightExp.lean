/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Gauss.FineModel
import RBM3D.Green.IBPPoly
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# LW-05: the weight expansion `(Owx)` (T2107)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:294-306` (`7_8:294-306`, lemma `ssl`,
cited from `[yang2021]` Lemma 3.5).  Design: T2040 (split row LW-05).

## Contents (namespace `RBM.Graph`)

1. **The bridge** from the one-size law `PF d L W g` to the merged Stein layer on `Sizes.seqP`
   (`lwWxSizes` is the constant size sequence `(L, W, g)`; the section index is `n = 0`):
   `lwWx_integral` (a: `∫ F ∘ slice ∂seqP = ∫ F ∂PF`, through the section `lwWxSec` of `slice`),
   `lwWx_lwG`, `lwWx_lwS_apply`, `lwWx_lwSp`, `lwWx_hSp`, `lwWx_flow`, `lwWx_im_pos`,
   `lwWx_mE_ne` (b), the ring map `lwWxRename` of resolvent polynomials, with the swap
   `(false, a, b) ↦ (b, a, false)` (c: `lwWx_lwPoly`), and `lwWx_dh`, `lwWx_lwdf`,
   `lwWx_hasDerivAt` (d).
2. **The weight expansion on `PF`.**  `lwWeightExp_holds : ∀ d, LWweightExp d` (the pin of
   `Graph/LWPins.lean:106`, with `S⁺ = LWPins_lwSp d L W g E t`, the argument order of the
   definition of `LWPins_lwSp`, after the six-edit amendment of T2107, DECISIONS §34), for every
   `d`, from `owx_integral` through the bridge for `0 < t < 1`, and `t = 0` separately.
3. **`(Owx)` as a graph operation**: `owxT1`, `owxT2`, `owxT3 q`, `owxT4 q` (the four terms as
   graphs on `I ⊕ Fin k`), `owx_graph_E` (the identity of expectations of values),
   `owxT*_counters`, `owxT*_ord` (every term has `ord Γ + 1`; `n_S + 1`, `n_W + 1 or 2`,
   `n_V + 1 or 2`, `n_M` unchanged).
4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`.
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

/-! ## 1. The bridge `PF d L W g` ↔ `Sizes.seqP` -/

section Bridge

/-- The constant size sequence `(L n, W n, lam n) = (L, W, g)`; the bridge sits at `n = 0`. -/
abbrev lwWxSizes (d L W : ℕ) (g : ℝ) [NeZero W] (hL : 3 ≤ L) : Sizes d where
  L := fun _ => L
  W := fun _ => W
  lam := fun _ => g
  three_le_L := fun _ => hL
  W_pos := fun _ => Nat.pos_of_ne_zero (NeZero.ne W)

variable {d L W : ℕ} [NeZero L] [NeZero W] {g : ℝ} (hL : 3 ≤ L) (E t : ℝ)

/-- (b) `Im z_t > 0` for `|E| < 2` and `t < 1`. -/
theorem lwWx_im_pos (hE : |E| < 2) (ht1 : t < 1) : 0 < (zt E t).im := by
  rw [zt_im]
  exact mul_pos (by linarith) (mE_im_pos hE)

/-- (b) `m(E) ≠ 0` for `|E| < 2`. -/
theorem lwWx_mE_ne (hE : |E| < 2) : mE E ≠ 0 := by
  intro h
  have := mE_im_pos hE
  rw [h] at this
  simp at this

/-- (b) the flow relation `z_t + t m = -m⁻¹`. -/
theorem lwWx_flow (hE : |E| < 2) : zt E t + (t : ℂ) * mE E = -(mE E)⁻¹ := by
  have h0 := lwWx_mE_ne E hE
  have hm := mE_mul hE.le
  unfold zt
  field_simp
  linear_combination hm

/-- The resolvent `G^* = (H - z̄)⁻¹` is the conjugate transpose of `G = (H - z)⁻¹` at a Hermitian `H`. -/
theorem lwWx_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : (Gres H z true)ᴴ = Gres H z false := by
  have hH' : Hᴴ = H := hH
  simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH', Complex.star_def]

/-- (c) the swap: `(H - z̄)⁻¹_{ab} = conj ((H - z)⁻¹_{ba})` at a Hermitian `H`.  The plain reordering
`(false, a, b) ↦ (a, b, false)` is wrong for `a ≠ b`. -/
theorem lwWx_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (a b : ι) : Gres H z false a b = star (Gres H z true b a) := by
  rw [← lwWx_Gres_conjTranspose hH z]
  rfl

/-- (d) the matrix-level derivative of `G^σ_{ab}` in the direction `E_{αw}`: `-G^σ_{aα} G^σ_{wb}`
(`σ = +`: the merged `hasDerivAt_inverse_apply`; `σ = -` is the same for `A = H - z̄`). -/
theorem lwWx_hasDerivAt_Gres {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (α w a b : ι) :
    HasDerivAt (fun s : ℂ => Gres (H + s • single α w (1 : ℂ)) z σ a b)
      (-(Gres H z σ a α * Gres H z σ w b)) 0 := by
  have hz' : (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
    cases σ <;> simpa using hz
  have hU := isUnit_sub_smul_of_isHermitian hH hz'
  have h := hasDerivAt_inverse_apply hU α w a b
  have hfun : (fun s : ℂ => Gres (H + s • single α w (1 : ℂ)) z σ a b) = fun s : ℂ =>
      Ring.inverse ((H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ)) +
        s • single α w (1 : ℂ)) a b := by
    funext s
    simp only [Gres]
    rw [add_sub_right_comm]
  rw [hfun]
  exact h

variable (d L W) in
/-- (c) the variable map: the entry `(false, a, b)` of `G^* = (H - z̄)⁻¹` is `conj G_{ba}`, the variable
`(b, a, false)` of `lwVar`; the variable `(true, a, b)` is `(a, b, true)`. -/
def lwWxVar (v : Bool × Idx d L W × Idx d L W) : Idx d L W × Idx d L W × Bool :=
  if v.1 then (v.2.1, v.2.2, true) else (v.2.2, v.2.1, false)

variable (d L W) in
/-- (c) **the ring map** of resolvent polynomials `P ↦ P'`: `LWPins_resPoly`'s `Bool × Idx × Idx`
variables to `lwVar`'s `Idx × Idx × Bool` variables, `P' = rename (lwWxVar) P`. -/
def lwWxRename :
    MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ →ₐ[ℂ] MvPolynomial (Idx d L W × Idx d L W × Bool) ℂ :=
  MvPolynomial.rename (lwWxVar d L W)

/-- The entries of `lwS` and `LWPins_lwS` agree. -/
theorem lwWx_lwS_apply (x y : Idx d L W) :
    lwS (lwWxSizes d L W g hL) 0 t x y = LWPins_lwS d L W g t x y := by
  simp [lwS, LWPins_lwS]

/-! ### (a) the transport of the integral from `seqP` to `PF` -/

variable (g) in
/-- The section of `slice` at size `0`: the one-size sample, extended by `0` at the other sizes. -/
def lwWxSec (ω : Ω d L W) : Sizes.SeqΩ (lwWxSizes d L W g hL) :=
  Function.extend (fun c : CoordF d L W => (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL))) ω 0

theorem lwWx_sec_inj : Function.Injective
    (fun c : CoordF d L W => (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL))) := by
  intro c c' h
  simpa using h

variable (g) in
theorem lwWx_slice_sec (ω : Ω d L W) : Sizes.slice (lwWxSizes d L W g hL) 0 (lwWxSec g hL ω) = ω := by
  funext c
  exact (lwWx_sec_inj (g := g) hL).extend_apply ω 0 c

theorem lwWx_continuous_sec : Continuous (lwWxSec (d := d) (L := L) (W := W) g hL) := by
  classical
  refine continuous_pi fun b => ?_
  by_cases h : ∃ c : CoordF d L W, (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL)) = b
  · obtain ⟨c, rfl⟩ := h
    have : (fun ω : Ω d L W => lwWxSec g hL ω ⟨0, c⟩) = fun ω => ω c := by
      funext ω
      exact (lwWx_sec_inj (g := g) hL).extend_apply ω 0 c
    change Continuous (fun ω : Ω d L W => lwWxSec g hL ω ⟨0, c⟩)
    rw [this]
    exact continuous_apply c
  · have : (fun ω : Ω d L W => lwWxSec g hL ω b) = fun _ => 0 := by
      funext ω
      simp only [lwWxSec]
      rw [Function.extend_apply' _ _ _ h]
      rfl
    change Continuous (fun ω : Ω d L W => lwWxSec g hL ω b)
    rw [this]
    exact continuous_const

/-- **(a) the bridge of the integral**: `∫ F ∂seqP = ∫ G ∂PF` whenever `F = G ∘ slice` and `F` is
continuous (`Sizes.seqP_map_slice`). -/
theorem lwWx_integral {F : Sizes.SeqΩ (lwWxSizes d L W g hL) → ℂ} {G : Ω d L W → ℂ}
    (hF : Continuous F) (h : ∀ ω', G (Sizes.slice (lwWxSizes d L W g hL) 0 ω') = F ω') :
    ∫ ω, G ω ∂(PF d L W g) = ∫ ω', F ω' ∂(Sizes.seqP (lwWxSizes d L W g hL)) := by
  have hG : G = F ∘ lwWxSec g hL := by
    funext ω
    have := h (lwWxSec g hL ω)
    rw [lwWx_slice_sec] at this
    exact this
  have hGc : Continuous G := by rw [hG]; exact hF.comp (lwWx_continuous_sec hL)
  have hmap := Sizes.seqP_map_slice (lwWxSizes d L W g hL) 0
  have e : ∫ ω', F ω' ∂(Sizes.seqP (lwWxSizes d L W g hL)) =
      ∫ ω', G (Sizes.slice (lwWxSizes d L W g hL) 0 ω') ∂(Sizes.seqP (lwWxSizes d L W g hL)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω' => (h ω').symm)
  rw [e, ← integral_map (Sizes.measurable_slice (lwWxSizes d L W g hL) 0).aemeasurable
    hGc.aestronglyMeasurable, hmap]

end Bridge

/-! ## 2. The weight expansion on `PF` (the pin `LWweightExp`, `Graph/LWPins.lean:106`) -/

section PinProof

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro of
`Graph/LWStein.lean`, which is not exported). -/
local macro "lwx_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply lwStein_tame_lwG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- `G = (0 - z)⁻¹` at `H = 0` on the index type `Idx` (the merged `Gres_zero_eq_scalar` is on `Vtx`). -/
theorem lwWx_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ℂ} (hz : z ≠ 0) :
    Gres (0 : Matrix ι ι ℂ) z true = (-z)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [Gres]
  simp only [↓reduceIte]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hz)]

end PinProof



/-! ## 3. `(Owx)` as a graph operation (T2060d, design row LW-05)

For a graph `Γ` with the weight `Ǧ_{xx}` (the blue circled self-loop `⟨true, true, inr x, inr x⟩`) at an
internal vertex `x`, `p ∈ lwSplit Γ.solid` is the pair (this edge, the other solid edges).  The four terms of
`(Owx)` are graphs on `I ⊕ Fin k` (the `k` new internal vertices `α`, `β`): the old vertices are `inr (inl ·)`
(`owxEmb`), the new ones `inr (inr ·)`; the coefficients carry `m`, `m³` and the signs of `(Owx)`.

* `owxT1`: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f` (`Γ` plus a leaf `α`);
* `owxT2`: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ} f` (the weight dropped, a path `x - α - β`);
* `owxT3 q`, one graph for each solid edge `q.1` of `f` (`q ∈ lwSplit p.2`): `-m Σ_α S_{xα} G_{αx} ∂_{h_{αx}} f`
  (the weight dropped, a leaf `α`, the edge `q.1` replaced by the two edges of its derivative with `w = x`);
* `owxT4 q`: `-m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}} f` (path `x - α - β`, derivative with `(α, w) = (β, α)`).
-/

section OwxGraph

variable {E I : Type*}

/-- The inclusion of the vertices of `Γ` into those of a graph with `k` more internal vertices. -/
def owxEmb (k : ℕ) : E ⊕ I → E ⊕ (I ⊕ Fin k) := Sum.map id Sum.inl

/-- `Γ` with its vertices renamed by `emb`, the edges `s` (solid) and `w` (waved) appended, and the
coefficient multiplied by `c`. -/
def LGraph.owxExt {E' I' : Type*} (Γ : LGraph E I) (emb : E ⊕ I → E' ⊕ I') (c : ℂ)
    (s : List (SEdge (E' ⊕ I'))) (w : List (WEdge (E' ⊕ I'))) : LGraph E' I' where
  solid := Γ.solid.map (SEdge.map emb) ++ s
  waved := Γ.waved.map (WEdge.map emb) ++ w
  dotted := Γ.dotted.map (DEdge.map emb)
  coeff := c * Γ.coeff

/-- The edges replacing a solid edge `e` in its derivative `∂_{h_{αw}}` with the labels `α`, `w` given by the
vertices `a`, `w` (`lwDEdges` with the two new vertices replaced by `a`, `w`): `G_{ab} ↦ G_{aα} G_{wb}`,
`Ḡ_{ab} ↦ Ḡ_{aw} Ḡ_{αb}` (the circle is dropped, `M` is constant). -/
def owxDE {V : Type*} (a w : V) (e : SEdge V) : SEdge V × SEdge V :=
  if e.σ then (⟨true, false, e.src, a⟩, ⟨true, false, w, e.dst⟩)
  else (⟨false, false, e.src, w⟩, ⟨false, false, a, e.dst⟩)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem LGraph.term_owxExt {E' I' : Type*} (Γ : LGraph E I) (emb : E ⊕ I → E' ⊕ I') (c : ℂ)
    (s : List (SEdge (E' ⊕ I'))) (w : List (WEdge (E' ⊕ I'))) (D : LData ι) (ℓ : E' ⊕ I' → ι) :
    (Γ.owxExt emb c s w).term D ℓ =
      c * Γ.term D (ℓ ∘ emb) * (s.map (SEdge.val D ℓ)).prod * (w.map (WEdge.val D ℓ)).prod := by
  simp only [LGraph.term, LGraph.owxExt, List.map_append, List.prod_append, List.map_map]
  have h1 : (SEdge.val D ℓ) ∘ (SEdge.map emb) = SEdge.val D (ℓ ∘ emb) := funext fun e => rfl
  have h2 : (WEdge.val D ℓ) ∘ (WEdge.map emb) = WEdge.val D (ℓ ∘ emb) := funext fun e => rfl
  have h3 : (DEdge.val ℓ) ∘ (DEdge.map emb) = DEdge.val (ℓ ∘ emb) := funext fun e => rfl
  rw [h1, h2, h3]
  ring

/-- The product of the two derivative edge factors of `owxDE` is `-∂_{h_{aw}}` of the edge factor
(`G_{src a} G_{w dst}` for a blue edge, `\bar G_{src w} \bar G_{a dst}` for a red one). -/
theorem owxDE_val {V : Type*} (D : LData ι) (ℓ : V → ι) (a w : V) (e : SEdge V) :
    SEdge.val D ℓ (owxDE a w e).1 * SEdge.val D ℓ (owxDE a w e).2 =
      if e.σ then D.G (ℓ e.src) (ℓ a) * D.G (ℓ w) (ℓ e.dst)
      else star (D.G (ℓ e.src) (ℓ w)) * star (D.G (ℓ a) (ℓ e.dst)) := by
  unfold owxDE
  split_ifs <;> simp [SEdge.val]

end OwxGraph


/-! ### The molecule counter of a graph with pendant vertices -/

section PendantNM

variable {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I']
  [DecidableEq I']

private theorem owx_adj_comm (Γ : LGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [LGraph.adj, or_comm]

theorem owx_molGraph_adj (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.molGraph.Adj u v ↔ u ≠ v ∧ Γ.adj u v = true := by
  simp only [LGraph.molGraph, SimpleGraph.fromRel_adj, owx_adj_comm Γ v u, or_self]

/-- **Pendant vertices do not change `n_M`**: if `Γ'` has the vertices of `Γ` (`emb`, with a retraction
`ρ`), every edge of `Γ'` either comes from an edge of `Γ` or joins two vertices with the same `ρ`-image, and every
vertex of `Γ'` is joined to the image of its `ρ`-image, then `Γ` and `Γ'` have the same internal molecules. -/
theorem owx_nM_eq (Γ : LGraph E I) (Γ' : LGraph E I') (emb : E ⊕ I → E ⊕ I') (ρ : E ⊕ I' → E ⊕ I)
    (hρ : ∀ v, ρ (emb v) = v) (hemb : ∀ e : E, emb (Sum.inl e) = Sum.inl e)
    (hρe : ∀ e : E, ρ (Sum.inl e) = Sum.inl e)
    (ha : ∀ u v, Γ.adj u v = true → Γ'.adj (emb u) (emb v) = true)
    (hb : ∀ u v, Γ'.adj u v = true → ρ u = ρ v ∨ Γ.adj (ρ u) (ρ v) = true)
    (hc : ∀ w, Γ'.molGraph.Reachable w (emb (ρ w))) : Γ'.nM = Γ.nM := by
  classical
  have hinj : Function.Injective emb := fun u v h => by rw [← hρ u, ← hρ v, h]
  rw [Γ'.nM_eq_card, Γ.nM_eq_card]
  let f : Γ.molGraph →g Γ'.molGraph :=
    ⟨emb, fun {u v} h => by
      rw [owx_molGraph_adj] at h ⊢
      exact ⟨fun e => h.1 (hinj e), ha u v h.2⟩⟩
  have hstep : ∀ u v, Γ'.molGraph.Adj u v → Γ.molOf (ρ u) = Γ.molOf (ρ v) := by
    intro u v h
    rw [owx_molGraph_adj] at h
    rcases hb u v h.2 with h1 | h1
    · rw [h1]
    · by_cases h2 : ρ u = ρ v
      · rw [h2]
      · exact SimpleGraph.ConnectedComponent.eq.2
          (SimpleGraph.Adj.reachable ((owx_molGraph_adj Γ _ _).2 ⟨h2, h1⟩))
  have hwalk : ∀ {v w : E ⊕ I'} (p : Γ'.molGraph.Walk v w), Γ.molOf (ρ v) = Γ.molOf (ρ w) := by
    intro v w p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hstep _ _ h).trans ih
  let φ : Γ.Mol → Γ'.Mol := SimpleGraph.ConnectedComponent.map f
  let ψ : Γ'.Mol → Γ.Mol :=
    SimpleGraph.ConnectedComponent.lift (fun v => Γ.molOf (ρ v)) (fun _ _ p _ => hwalk p)
  have hψφ : ∀ c, ψ (φ c) = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    change Γ.molOf (ρ (emb v)) = Γ.molOf v
    rw [hρ]
  have hφψ : ∀ c, φ (ψ c) = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    exact SimpleGraph.ConnectedComponent.eq.2 (hc v).symm
  have hext : ∀ c, Γ.IsExtMol c ↔ Γ'.IsExtMol (φ c) := by
    intro c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by
        change _ = Γ'.molOf (emb (Sum.inl a))
        rw [hemb]⟩
    · rintro ⟨a, ha'⟩
      refine ⟨a, ?_⟩
      have := hψφ c
      rw [← ha'] at this
      rw [← this]
      change Γ.molOf (Sum.inl a) = Γ.molOf (ρ (Sum.inl a))
      rw [hρe]
  refine Nat.card_congr
    { toFun := fun c => ⟨ψ c.1, fun h => c.2 (by
        have := (hext (ψ c.1)).1 h
        rwa [hφψ] at this)⟩
      invFun := fun c => ⟨φ c.1, fun h => c.2 ((hext c.1).2 h)⟩
      left_inv := fun c => Subtype.ext (hφψ c.1)
      right_inv := fun c => Subtype.ext (hψφ c.1) }

end PendantNM


section OwxNM

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The retraction of the vertices of a graph with `k` pendant vertices: the new vertices go to `x`. -/
def owxRho (k : ℕ) (x : I) : E ⊕ (I ⊕ Fin k) → E ⊕ I :=
  Sum.elim Sum.inl (Sum.elim Sum.inr (fun _ => Sum.inr x))

theorem owxRho_emb (k : ℕ) (x : I) (v : E ⊕ I) : owxRho k x (owxEmb k v) = v := by
  rcases v with a | b <;> rfl

/-- `n_M` of `Γ.owxExt` is that of `Γ` when the appended waved edges only join vertices that the retraction
`owxRho k x` identifies, and every new vertex is joined to `x`. -/
theorem owxExt_nM (Γ : LGraph E I) (k : ℕ) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (hw : ∀ e ∈ w, owxRho k x e.x = owxRho k x e.y)
    (hc : ∀ v, (Γ.owxExt (owxEmb k) c s w).molGraph.Reachable v (owxEmb k (owxRho k x v))) :
    (Γ.owxExt (owxEmb k) c s w).nM = Γ.nM := by
  refine owx_nM_eq Γ (Γ.owxExt (owxEmb k) c s w) (owxEmb k) (owxRho k x) (owxRho_emb k x)
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
          simp [WEdge.map, owxRho_emb]
        · right
          subst h1 h2
          simp [WEdge.map, owxRho_emb]
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
        simp [DEdge.map, owxRho_emb]
      · right
        subst h1 h2
        simp [DEdge.map, owxRho_emb]

end OwxNM


section OwxTerms

variable {E I : Type*}

/-- **Term 1 of `(Owx)`**: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f` -- `Γ` (the weight kept) with a leaf `α` joined to
`x` by the waved edge `S_{xα}` and the light-weight `Ǧ_{αα}`; `coeff = m · coeff Γ`. -/
def owxT1 (m : ℂ) (Γ : LGraph E I) (x : I) : LGraph E (I ⊕ Fin 1) :=
  Γ.owxExt (owxEmb 1) m [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

end OwxTerms

section OwxCounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- With one new vertex `α` joined to `x` by an appended waved edge, every vertex is joined to its
retraction. -/
theorem owxExt_reach1 (Γ : LGraph E I) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (col σ : Bool)
    (hw : (⟨col, σ, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 1) c s w).molGraph.Reachable v (owxEmb 1 (owxRho 1 x v)) := by
  intro v
  rcases v with a | b | j
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.refl _
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp [owxEmb, owxRho], ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw, Or.inr ⟨rfl, rfl⟩⟩

/-- With two new vertices (a path `x - α - β`), every vertex is joined to its retraction. -/
theorem owxExt_reach2 (Γ : LGraph E I) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (col σ col' σ' : Bool)
    (hw : (⟨col, σ, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w)
    (hw' : (⟨col', σ', Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable v (owxEmb 2 (owxRho 2 x v)) := by
  have h1 : (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) := by
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp, ?_⟩)
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

theorem owxT1_counters (m : ℂ) (Γ : LGraph E I) (x : I) :
    (owxT1 m Γ x).nS = Γ.nS + 1 ∧ (owxT1 m Γ x).nW = Γ.nW + 1 ∧ (owxT1 m Γ x).nV = Γ.nV + 1 ∧
      (owxT1 m Γ x).nM = Γ.nM := by
  refine ⟨by simp [owxT1, LGraph.owxExt, LGraph.nS], by simp [owxT1, LGraph.owxExt, LGraph.nW],
    by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  refine owxExt_nM Γ 1 x m _ _ ?_ (owxExt_reach1 Γ x m _ _ false true (by simp))
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  rfl

end OwxCounters


section OwxTermVal

variable {E I : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The value of a term of `owxT1` at a labelling `ℓ'` extending `ℓ` (`ℓ' ∘ owxEmb 1 = ℓ`). -/
theorem owxT1_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I) (ℓ : E ⊕ I → ι)
    (ℓ' : E ⊕ (I ⊕ Fin 1) → ι) (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (owxT1 m Γ x).term D ℓ' = m * Γ.term D ℓ *
      (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0))) -
        D.M (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0)))) *
      D.S (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  rw [owxT1, LGraph.term_owxExt, hℓ]
  simp [SEdge.val, WEdge.val, hx]

end OwxTermVal


section OwxHelpers

/-- `lwSplit l` splits `l` into an element and the rest: `l ~ p.1 :: p.2`. -/
theorem lwSplit_perm {κ : Type*} (l : List κ) : ∀ p ∈ lwSplit l, l.Perm (p.1 :: p.2) := by
  induction l with
  | nil => intro p hp; simp [lwSplit] at hp
  | cons a l ih =>
    intro p hp
    simp only [lwSplit, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact List.Perm.refl _
    · exact ((ih q hq).cons a).trans (List.Perm.swap q.1 a q.2)

/-- The product over a list is that of the element split off times the product of the rest. -/
theorem lwSplit_prod {κ : Type*} {M : Type*} [CommMonoid M] (l : List κ) (f : κ → M)
    (p : κ × List κ) (hp : p ∈ lwSplit l) :
    (l.map f).prod = f p.1 * (p.2.map f).prod := by
  have := ((lwSplit_perm l p hp).map f).prod_eq
  simpa using this

/-- A list sum of integrable functions is integrable. -/
theorem owx_integrable_list_sum {Ω κ : Type*} [MeasurableSpace Ω] {P : Measure Ω} (L : List κ)
    (f : κ → Ω → ℂ) (hf : ∀ a ∈ L, Integrable (f a) P) :
    Integrable (fun ω => (L.map fun a => f a ω).sum) P := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (List.mem_cons_self ..)).add (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

/-- The integral of a list sum of integrable functions is the list sum of the integrals. -/
theorem owx_integral_list_sum {Ω κ : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : List κ)
    (f : κ → Ω → ℂ) (hf : ∀ a ∈ L, Integrable (f a) P) :
    ∫ ω, (L.map fun a => f a ω).sum ∂P = (L.map fun a => ∫ ω, f a ω ∂P).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := hf a (List.mem_cons_self ..)
    have h2 := owx_integrable_list_sum (P := P) L f fun b hb => hf b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add h1 h2, ih fun b hb => hf b (List.mem_cons_of_mem _ hb)]

/-- A list sum whose terms are `-c` times those of another list. -/
theorem owx_list_aux {κ : Type*} (L : List κ) (c : ℂ) (F G : κ → ℂ) (h : ∀ q ∈ L, G q = -c * F q) :
    (L.map G).sum = -(c * (L.map F).sum) := by
  have : L.map G = L.map fun q => -c * F q := List.map_congr_left h
  rw [this, List.sum_map_mul_left]
  ring

variable {I : Type*} {ι : Type*} [Fintype ι] [Fintype I] [DecidableEq I]

/-- A labelling of `I ⊕ Fin 1` is a labelling of `I` and a label `α`. -/
theorem owx_sum_fin1 (F : (I ⊕ Fin 1 → ι) → ℂ) :
    ∑ ℓ', F ℓ' = ∑ ℓi : I → ι, ∑ α : ι, F (Sum.elim ℓi fun _ => α) := by
  rw [← (Equiv.sumArrowEquivProdArrow I (Fin 1) ι).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  rfl

/-- A labelling of `I ⊕ Fin 2` is a labelling of `I` and two labels `α, β`. -/
theorem owx_sum_fin2 (F : (I ⊕ Fin 2 → ι) → ℂ) :
    ∑ ℓ', F ℓ' = ∑ ℓi : I → ι, ∑ α : ι, ∑ β : ι, F (Sum.elim ℓi ![α, β]) := by
  rw [← (Equiv.sumArrowEquivProdArrow I (Fin 2) ι).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [← (finTwoArrowEquiv ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

end OwxHelpers


section OwxEdgePoly

variable {d : ℕ} (sz : Sizes d) (n : ℕ) {V : Type*}

/-- The resolvent polynomial of a solid edge at a labelling `ℓ` (`G_{ab} - M_{ab}` or its conjugate; the
constant `M_{ab}` is `0` without the circle). -/
def owxEdgePoly (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (e : SEdge V) :
    MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ :=
  if e.σ then MvPolynomial.X (ℓ e.src, ℓ e.dst, true) -
      MvPolynomial.C (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0)
  else MvPolynomial.X (ℓ e.src, ℓ e.dst, false) -
      MvPolynomial.C (star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0))

variable {sz n}

theorem lwPoly_owxEdgePoly (z : ℂ) (u : ℝ) (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (e : SEdge V) (ω : Sizes.SeqΩ sz) :
    lwPoly sz n z u (owxEdgePoly sz n M ℓ e) ω = SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e := by
  cases hσ : e.σ
  · rw [lwStein_sedge_val_red e hσ ℓ ω]
    simp [owxEdgePoly, hσ, lwPoly, lwVar]
  · rw [lwStein_sedge_val_blue e hσ ℓ ω]
    simp [owxEdgePoly, hσ, lwPoly, lwVar]

theorem lwPoly_owxEdgePoly_prod (z : ℂ) (u : ℝ)
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (l : List (SEdge V)) (ω : Sizes.SeqΩ sz) :
    lwPoly sz n z u ((l.map (owxEdgePoly sz n M ℓ)).prod) ω =
      (l.map (SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ)).prod := by
  unfold lwPoly
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact lwPoly_owxEdgePoly z u M S Sp ℓ e ω

end OwxEdgePoly


section OwxIdentity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The labelling of `E ⊕ (I ⊕ Fin 1)` extending `(ℓe, ℓi)` by the label `α` of the new vertex. -/
def owxLab1 {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α : ι) : E ⊕ (I ⊕ Fin 1) → ι :=
  Sum.elim ℓe (Sum.elim ℓi fun _ => α)

/-- The labelling of `E ⊕ (I ⊕ Fin 2)` extending `(ℓe, ℓi)` by the labels `α, β` of the new vertices. -/
def owxLab2 {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α β : ι) : E ⊕ (I ⊕ Fin 2) → ι :=
  Sum.elim ℓe (Sum.elim ℓi ![α, β])

theorem owxLab1_emb {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α : ι) :
    owxLab1 ℓe ℓi α ∘ owxEmb 1 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

theorem owxLab2_emb {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    owxLab2 ℓe ℓi α β ∘ owxEmb 2 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

/-- The expectation of the value of a graph with one new internal vertex is the sum, over the labels of the
old internal vertices and of the new one, of the expectations of its terms. -/
theorem owx_integral_val1 (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ}
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T : LGraph E (I ⊕ Fin 1))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, T.term (lwSampleData sz n z u M S Sp ω)
        (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M S Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have h1 : ∀ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, T.term (lwSampleData sz n z u M S Sp ω) (owxLab1 ℓe ℓi α) :=
    fun ω => owx_sum_fin1 (fun ℓ' => T.term (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ℓ'))
  simp_rw [h1]
  rw [integral_finsetSum _ fun ℓi _ => integrable_finsetSum _ fun α _ => hint _]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  exact integral_finsetSum _ fun α _ => hint _

/-- The same for two new internal vertices. -/
theorem owx_integral_val2 (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ}
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T : LGraph E (I ⊕ Fin 2))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, T.term (lwSampleData sz n z u M S Sp ω)
        (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M S Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have h1 : ∀ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β,
        T.term (lwSampleData sz n z u M S Sp ω) (owxLab2 ℓe ℓi α β) :=
    fun ω => owx_sum_fin2 (fun ℓ' => T.term (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ℓ'))
  simp_rw [h1]
  rw [integral_finsetSum _ fun ℓi _ => integrable_finsetSum _ fun α _ =>
    integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact integral_finsetSum _ fun β _ => hint _

end OwxIdentity


/-! ## 4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`

(`N = (W L)^d = 27`; `m(0) = i`, `z_{1/2} = i/2`; `H_{1/2} = X / √2` on `27 × 27`.)  The constant size
sequence `lwWxSizes 3 3 1 (1/2)`; every deterministic hypothesis is discharged. -/

end RBM.Graph
