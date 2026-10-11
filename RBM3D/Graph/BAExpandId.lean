/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm5
import RBM3D.Graph.BAGGOp
import RBM3D.Graph.BAExpandW
import RBM3D.BA.MFixedPoint

/-!
# BA-L L4d (T2419): the BA identity half of `lem:LWterm_EXP`

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:393-405` (`GGGamma`, D402
coefficient `W - 1 = M⁺S⁺`); design `docs/reports/T2398-design.md` §4 (the identity in
expectation), probe `t/T2398:RBM3D/Probe/T2398Pins.lean:135-153, 490-494` (statements and
engine instance, copied).  The twin of the identity half of `Graph/LWExpTerm5.lean`
(`lwExpandIdentity_holds`, `:594`) without its leaf-side parts.

## Contents (namespace `RBM.Graph`; private prefix `BAExpandId_`)

1. **Vocabulary** (probe 135-153): `baG5Graph k s`, `BAG5Identity d Ls`.
1b. **The red charge** (Amend 1): `BAExpandId_flip` (the complex-conjugate graph),
   `BAExpandId_star_val` (`star (Γ.val) = (flip Γ).val`), `baExpFrame_gg_red` (the red `GG`
   identity as the conjugate of `baExpFrame_gg` at the conjugate graph, lists `BAExpandId_gg2r`,
   `BAExpandId_gg4r`),
   `BAExpandId_gg_identity` (either charge).
2. **The procedure**: `BAExpandId_pcomp`, `BAExpandId_outsOf` (the packing of the partitions
   of a list of terms through the external map of the parent), `BARCand` (a `GG` candidate:
   a charge `σ`, a vertex `v` and two circled solid edges `p = Ǧ_{vy}`, `q = Ǧ_{y'v}` of the
   charge `σ` of the same graph), `BARCand.kids` (the partitions of `gg2 ++ gg4`, the conjugate
   lists for `σ = false`, every exponent pair `(0, 0)`), `BASel`, `BAstep`, `BAexpand`
   (= `expandG` of `LWExpTerm5`), `BAexpandRoot`, `BAselClassical`.
3. **Normality** of the children: `BARCand.kids_normal` (`BAGraph.partition_normal`).
4. **Integrability and packing**: every graph value is integrable over `PF d L W 0`, the
   partition and the packed graph read through `P.ext`.
5. **The step**: `BARCand.kids_identity` (`BAExpandId_gg_identity` + `BAGraph.val_eq_partition` +
   packing), for both charges.
6. **The expansion**: `baExpandIdentity_holds`: `BAG5Identity d (BAexpandRoot sel fuel)` for
   every selector and fuel, from `expandG_sum` of `LWExpTerm5` (imported) with the weight
   `w = fun _ => 1`.
7. Compiled instances (`BAExpandIdInst`, `d = 3`): a blue candidate and a red candidate.

`LWG5Progress` (`LWExpTerm5:72`) is **not** claimed: it fails at BA (`baTwB_stuck`, probe 97);
the stop rule and the leaf property are L4e-C's.  The candidate rule has both charges: a blue pair
is the merged identity `baExpFrame_gg` (`Graph/BAGGOp.lean:785`), a red pair is its complex
conjugate (`baExpFrame_gg_red`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private BAWeightOp_val_tame BAWeightOp_sd from RBM3D.Graph.BAWeightOp
open private BAExpandW_integrable_PF from RBM3D.Graph.BAExpandW
open private BAVocab_val_of_factor BAVocab_val_of_not from RBM3D.Graph.BAVocab

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. Vocabulary (the probe, lines 135-153) -/

/-- `𝒢_{xy}` of `(eq;I42inG)` (`B:68-72`) as a BA graph, the twin of `LWG5Graph` (`LWExpTerm3.lean:54`), all solid edges
uncircled (`G = Ǧ + M` is `BAGraph.partition`, `BAVocab.lean:229`); `k` selects `S⁺` for the first waved edge, `s` the
closing edge's charge. -/
def baG5Graph (k s : Bool) : BAGraph (Fin 2) (Fin 3) where
  solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inr 1),
    SEdge.mk true false (Sum.inr 1) (Sum.inr 2), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
    if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
  waved := [WEdge.mk k true (Sum.inr 1) (Sum.inr 0), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := []

/-- **L4d, the BA identity half** (band: `LWG5Identity`, `LWExpTerm5.lean:76`).  For lists `Ls k s` of packed BA graphs the
expectation identity `𝔼 𝒢_{xy} = Σ_μ 𝔼 Γ_μ` at the BA data `BAlwData` (`BAExpandW.lean:98`) for all `0 ≤ t < 1`.  No exponent
pairs: the coefficients `m^j m̄^{j'}` of the band are `M`-dotted edges here, and `(1 + M⁺S⁺)` is the `S⁺`-waved chain
(`BAGGGamma`, D402). -/
def BAG5Identity (d : ℕ) (Ls : Bool → Bool → List (BAPGraph (Fin 2))) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (E : ℂ) m → 0 ≤ t → t < 1 →
    ∀ (k s : Bool) (x y : Idx d L W),
      ∫ ω, (baG5Graph k s).val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        ((Ls k s).map fun q => ∫ ω, q.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum

/-! ## 1b. The red charge: complex conjugation (Amend 1)

A red solid edge is the complex conjugate of the blue one at the same data and the same endpoints
(`SEdge.val`: `Ḡ_{xy} = star G_{xy}`), an `M`-dotted edge likewise (`BAMEdge.val`), a coloured waved edge `S^-_{xy} = star S^+_{yx}`
(`WEdge.val`) is the conjugate of `S^+_{yx}`, so conjugation swaps its endpoints, a black waved edge `S_{xy}` is real
(`BAlwS = t · svarF`), and a `Ψ`-dotted edge `g₀ Ψ_{xy}` goes to `g₀ Ψ_{yx}` (`Ψ` Hermitian).  `BAExpandId_flip Γ` is the graph
whose value is the complex conjugate (`BAExpandId_star_val`), so the red `GG` identity is the conjugate of the blue one for the
conjugate graph, with the conjugated output lists: no input beyond `baExpFrame_gg` (`Graph/BAGGOp.lean:788`) is used and no
invariance of the law under `H ↦ H̄` (the identity in expectation is conjugated directly, `integral_conj`). -/

section Conj

variable {V : Type*}

/-- The conjugate of a solid edge: the other charge, the same endpoints and circle. -/
def BAExpandId_flipS (e : SEdge V) : SEdge V := { e with σ := !e.σ }

/-- The conjugate of a waved edge: a black edge `S_{xy}` is real; a coloured one `S^σ_{xy}` becomes `S^{!σ}_{yx}`. -/
def BAExpandId_flipW (e : WEdge V) : WEdge V := if e.col then ⟨true, !e.σ, e.y, e.x⟩ else e

/-- The conjugate of an `M`-dotted edge: `M_{xy} ↔ M̄_{xy}`. -/
def BAExpandId_flipM (e : BAMEdge V) : BAMEdge V := { e with σ := !e.σ }

/-- The conjugate of a `Ψ`-dotted edge: `Ψ_{xy} ↦ Ψ_{yx}` (`Ψ` is Hermitian, `g₀` real). -/
def BAExpandId_flipPsi (e : BAPsiEdge V) : BAPsiEdge V := ⟨e.y, e.x⟩

/-- The conjugate of a split `(edge, rest)` (`lwSplit`). -/
def BAExpandId_flipP (p : SEdge V × List (SEdge V)) : SEdge V × List (SEdge V) :=
  (BAExpandId_flipS p.1, p.2.map BAExpandId_flipS)

/-- **The conjugate graph**: every solid, coloured waved and `M`-dotted edge conjugated, the coefficient conjugated; dotted
edges (`1_{x = y}`, real) kept. -/
def BAExpandId_flip {E I : Type} (Γ : BAGraph E I) : BAGraph E I where
  solid := Γ.solid.map BAExpandId_flipS
  waved := Γ.waved.map BAExpandId_flipW
  dotted := Γ.dotted
  coeff := star Γ.coeff
  psi := Γ.psi.map BAExpandId_flipPsi
  mdot := Γ.mdot.map BAExpandId_flipM

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem BAExpandId_star_prod {α : Type*} (l : List α) (f g : α → ℂ) (h : ∀ a ∈ l, star (f a) = g a) :
    star (l.map f).prod = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, star_mul']
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

private theorem BAExpandId_star_sum {α : Type*} (l : List α) (f g : α → ℂ) (h : ∀ a ∈ l, star (f a) = g a) :
    star (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, star_add]
    rw [h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

private theorem BAExpandId_star_flipS (D : LData ι) (ℓ : V → ι) (e : SEdge V) :
    star (SEdge.val D ℓ e) = SEdge.val D ℓ (BAExpandId_flipS e) := by
  obtain ⟨σ, c, x, y⟩ := e
  cases σ <;> simp [SEdge.val, BAExpandId_flipS]

private theorem BAExpandId_star_flipW (D : LData ι) (hS : ∀ a b, star (D.S a b) = D.S a b) (ℓ : V → ι) (e : WEdge V) :
    star (WEdge.val D ℓ e) = WEdge.val D ℓ (BAExpandId_flipW e) := by
  obtain ⟨c, σ, x, y⟩ := e
  cases c
  · simp [WEdge.val, BAExpandId_flipW, hS]
  · cases σ <;> simp [WEdge.val, BAExpandId_flipW]

private theorem BAExpandId_star_flipM (D : BALData ι) (ℓ : V → ι) (e : BAMEdge V) :
    star (BAMEdge.val D ℓ e) = BAMEdge.val D ℓ (BAExpandId_flipM e) := by
  obtain ⟨σ, x, y⟩ := e
  cases σ <;> simp [BAMEdge.val, BAExpandId_flipM]

private theorem BAExpandId_star_flipPsi (D : BALData ι) (hP : ∀ a b, star (D.gPsi a b) = D.gPsi b a) (ℓ : V → ι)
    (e : BAPsiEdge V) : star (BAPsiEdge.val D ℓ e) = BAPsiEdge.val D ℓ (BAExpandId_flipPsi e) :=
  hP _ _

private theorem BAExpandId_star_dotted (ℓ : V → ι) (e : DEdge V) : star (DEdge.val ℓ e) = DEdge.val ℓ e := by
  unfold DEdge.val
  split_ifs <;> simp

/-- Conjugation of a graph term: `star (Γ.term D ℓ) = (flip Γ).term D ℓ`, for data with real `S` and Hermitian `gPsi`. -/
theorem BAExpandId_star_term {E I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι)
    (hS : ∀ a b, star (D.S a b) = D.S a b) (hP : ∀ a b, star (D.gPsi a b) = D.gPsi b a) (ℓ : E ⊕ I → ι) :
    star (Γ.term D ℓ) = (BAExpandId_flip Γ).term D ℓ := by
  unfold BAGraph.term LGraph.term BAExpandId_flip
  simp only [star_mul']
  have h1 := BAExpandId_star_prod Γ.solid (SEdge.val D.toLData ℓ) (fun e => SEdge.val D.toLData ℓ (BAExpandId_flipS e))
    fun e _ => BAExpandId_star_flipS _ _ e
  have h2 := BAExpandId_star_prod Γ.waved (WEdge.val D.toLData ℓ) (fun e => WEdge.val D.toLData ℓ (BAExpandId_flipW e))
    fun e _ => BAExpandId_star_flipW _ hS _ e
  have h3 := BAExpandId_star_prod Γ.dotted (DEdge.val ℓ) (DEdge.val ℓ) fun e _ => BAExpandId_star_dotted _ e
  have h4 := BAExpandId_star_prod Γ.psi (BAPsiEdge.val D ℓ) (fun e => BAPsiEdge.val D ℓ (BAExpandId_flipPsi e))
    fun e _ => BAExpandId_star_flipPsi _ hP _ e
  have h5 := BAExpandId_star_prod Γ.mdot (BAMEdge.val D ℓ) (fun e => BAMEdge.val D ℓ (BAExpandId_flipM e))
    fun e _ => BAExpandId_star_flipM _ _ e
  rw [h1, h2, h3, h4, h5]
  simp only [List.map_map, Function.comp_def]

/-- Conjugation of a graph value: `star (Γ.val D ℓe) = (flip Γ).val D ℓe`. -/
theorem BAExpandId_star_val {E I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (D : BALData ι)
    (hS : ∀ a b, star (D.S a b) = D.S a b) (hP : ∀ a b, star (D.gPsi a b) = D.gPsi b a) (ℓe : E → ι) :
    star (Γ.val D ℓe) = (BAExpandId_flip Γ).val D ℓe := by
  unfold BAGraph.val
  rw [star_sum]
  exact Finset.sum_congr rfl fun ℓi _ => BAExpandId_star_term Γ D hS hP _

/-- Conjugation of the value of a list of terms. -/
theorem BAExpandId_star_baSum {E I κ : Type} [Fintype I] [DecidableEq I] [Fintype κ] [DecidableEq κ]
    (Ts : List (BAGraph E I)) (D : BALData κ)
    (hS : ∀ a b, star (D.S a b) = D.S a b) (hP : ∀ a b, star (D.gPsi a b) = D.gPsi b a) (ℓe : E → κ) :
    star (baSum Ts D ℓe) = baSum (Ts.map BAExpandId_flip) D ℓe := by
  unfold baSum
  rw [List.map_map]
  exact BAExpandId_star_sum Ts _ _ fun T _ => BAExpandId_star_val T D hS hP ℓe

private theorem BAExpandId_lwSplit_map {κ μ : Type*} (f : κ → μ) (l : List κ) :
    lwSplit (l.map f) = (lwSplit l).map (fun p => (f p.1, p.2.map f)) := by
  induction l with
  | nil => simp [lwSplit]
  | cons a l ih => simp [lwSplit, ih, List.map_map, Function.comp_def]

private theorem BAExpandId_flipP_mem {l : List (SEdge V)} {p : SEdge V × List (SEdge V)} (hp : p ∈ lwSplit l) :
    BAExpandId_flipP p ∈ lwSplit (l.map BAExpandId_flipS) := by
  rw [BAExpandId_lwSplit_map]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

end Conj

section Data

variable (d L W : ℕ) [NeZero L] [NeZero W]

/-- The BA data has real `S` (`BAlwS = t · svarF`) and Hermitian `gPsi` (`g₀` real, `PsiI_isHermitian`): the two facts that
conjugation of a graph needs. -/
theorem BAExpandId_data_real (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) :
    (∀ a b, star ((BAlwData d L W g0 E t m ω).S a b) = (BAlwData d L W g0 E t m ω).S a b) ∧
      ∀ a b, star ((BAlwData d L W g0 E t m ω).gPsi a b) = (BAlwData d L W g0 E t m ω).gPsi b a := by
  constructor
  · intro a b
    simp [BAlwData, BAlwS, Complex.star_def]
  · intro a b
    have h := (PsiI_isHermitian d L W).apply b a
    simp only [BAlwData, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.star_def, h]

end Data

section Red

variable {E I : Type}

/-- The red `gg2` list at a red pair `p = Ḡ_{xy}`, `q = Ḡ_{y'x}`: the conjugate of the blue list `gg2` of the conjugate graph at
the conjugate pair (`Graph/BAGGOp.lean`, T2410). -/
def BAExpandId_gg2r (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 2)) :=
  ((BAExpandId_flip Γ).gg2 (BAExpandId_flipP p) (BAExpandId_flipP q)).map BAExpandId_flip

/-- The red `gg4` list (as `BAExpandId_gg2r`). -/
def BAExpandId_gg4r (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 4)) :=
  ((BAExpandId_flip Γ).gg4 (BAExpandId_flipP p) (BAExpandId_flipP q)).map BAExpandId_flip

end Red

/-- **The red-charge `GG` identity** (`GGGamma`, `B:393-405`, D402, for a pair `p = Ḡ_{xy}`, `q = Ḡ_{y'x}` of red circled solid
edges): `𝔼 Γ.val = 𝔼 (Σ_{Δ ∈ gg2r} Δ.val + Σ_{Δ ∈ gg4r} Δ.val)` at the model data `BAlwData` over `PF d L W 0`, with the
conjugated lists `BAExpandId_gg2r`, `BAExpandId_gg4r`.  It is the complex conjugate of `baExpFrame_gg` (`Graph/BAGGOp.lean:788`) at the
conjugate graph `BAExpandId_flip Γ` (`BAExpandId_star_val`, `integral_conj`); the hypotheses are those of `baExpFrame_gg` with
`σ = false`. -/
theorem baExpFrame_gg_red (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ),
    RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
      (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = false → p.1.circ = true →
      q.1.σ = false → q.1.circ = true → p.1.src = q.1.dst →
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (BAExpandId_gg2r Γ p q) (BAlwData d L W g0 Em t m ω) ℓe +
          baSum (BAExpandId_gg4r Γ p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  intro L W _ _ hL g0 Em t m hSelf ht0 ht1 Ex Ix _ _ _ _ Γ ℓe p hp q hq hσp hcp hσq hcq hxy
  have hp' : BAExpandId_flipP p ∈ lwSplit (BAExpandId_flip Γ).solid := BAExpandId_flipP_mem hp
  have hq' : BAExpandId_flipP q ∈ lwSplit (BAExpandId_flipP p).2 := BAExpandId_flipP_mem hq
  have hb := baExpFrame_gg d L W hL g0 Em t m hSelf ht0 ht1 (BAExpandId_flip Γ) ℓe _ hp' _ hq'
    (by simp [BAExpandId_flipP, BAExpandId_flipS, hσp]) (by simp [BAExpandId_flipP, BAExpandId_flipS, hcp])
    (by simp [BAExpandId_flipP, BAExpandId_flipS, hσq]) (by simp [BAExpandId_flipP, BAExpandId_flipS, hcq])
    (by simpa [BAExpandId_flipP, BAExpandId_flipS] using hxy)
  have hd := fun ω => BAExpandId_data_real d L W g0 Em t m ω
  calc ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)
      = ∫ ω, starRingEnd ℂ ((BAExpandId_flip Γ).val (BAlwData d L W g0 Em t m ω) ℓe) ∂(PF d L W 0) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        have := BAExpandId_star_val Γ _ (hd ω).1 (hd ω).2 ℓe
        change Γ.val _ ℓe = star _
        rw [← this, star_star]
    _ = starRingEnd ℂ (∫ ω, (BAExpandId_flip Γ).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) :=
        integral_conj
    _ = starRingEnd ℂ (∫ ω, baSum ((BAExpandId_flip Γ).gg2 (BAExpandId_flipP p) (BAExpandId_flipP q))
          (BAlwData d L W g0 Em t m ω) ℓe + baSum ((BAExpandId_flip Γ).gg4 (BAExpandId_flipP p) (BAExpandId_flipP q))
          (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) := by rw [hb]
    _ = ∫ ω, starRingEnd ℂ (baSum ((BAExpandId_flip Γ).gg2 (BAExpandId_flipP p) (BAExpandId_flipP q))
          (BAlwData d L W g0 Em t m ω) ℓe + baSum ((BAExpandId_flip Γ).gg4 (BAExpandId_flipP p) (BAExpandId_flipP q))
          (BAlwData d L W g0 Em t m ω) ℓe) ∂(PF d L W 0) := integral_conj.symm
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        change star _ = _
        rw [star_add, BAExpandId_star_baSum _ _ (hd ω).1 (hd ω).2, BAExpandId_star_baSum _ _ (hd ω).1 (hd ω).2]
        rfl

section Dispatch

variable {E I : Type}

/-- The `gg2` list of the charge `σ` of the pair: the merged blue list for `σ = true`, the conjugate list for `σ = false`. -/
def BAExpandId_ggL2 (σ : Bool) (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 2)) :=
  if σ then Γ.gg2 p q else BAExpandId_gg2r Γ p q

/-- The `gg4` list of the charge `σ` of the pair. -/
def BAExpandId_ggL4 (σ : Bool) (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List (BAGraph E (I ⊕ Fin 4)) :=
  if σ then Γ.gg4 p q else BAExpandId_gg4r Γ p q

end Dispatch

/-- **The `GG` identity for a pair of either charge** (`baExpFrame_gg` for `σ = true`, `baExpFrame_gg_red` for `σ = false`). -/
theorem BAExpandId_gg_identity (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ),
    RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (σ : Bool) (Γ : BAGraph Ex Ix)
      (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = σ → p.1.circ = true →
      q.1.σ = σ → q.1.circ = true → p.1.src = q.1.dst →
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (BAExpandId_ggL2 σ Γ p q) (BAlwData d L W g0 Em t m ω) ℓe +
          baSum (BAExpandId_ggL4 σ Γ p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  intro L W _ _ hL g0 Em t m hSelf ht0 ht1 Ex Ix _ _ _ _ σ Γ ℓe p hp q hq hσp hcp hσq hcq hxy
  cases σ
  · exact baExpFrame_gg_red d L W hL g0 Em t m hSelf ht0 ht1 Γ ℓe p hp q hq hσp hcp hσq hcq hxy
  · exact baExpFrame_gg d L W hL g0 Em t m hSelf ht0 ht1 Γ ℓe p hp q hq hσp hcp hσq hcq hxy

/-! ## 2. The procedure -/

/-- A packed graph read through the external map of its parent (the twin of `pcomp`, `LWExpTerm5.lean:120`). -/
def BAExpandId_pcomp (P : BAPGraph (Fin 2)) (Q : BAPGraph P.E') : BAPGraph (Fin 2) :=
  { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g }

/-- The outputs of a step: the BA partition of every term, packed and read through `P.ext` (twin of `BAPGraph.outsOf`,
`t/T2395:RBM3D/Probe/T2395Pins.lean:154`), every exponent pair `(0, 0)` (`expandG`'s carrier). -/
def BAExpandId_outsOf (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) :
    List ((ℕ × ℕ) × BAPGraph (Fin 2)) :=
  Ts.flatMap fun T => T.partition.map fun Q => ((0, 0), BAExpandId_pcomp P Q)

/-- **A `GG` candidate** of a packed graph, as data: a charge `σ`, a vertex `v` and two solid edges of the same graph,
`p.1 = Ǧ_{vy}` and `q.1 = Ǧ_{y'v}`, both circled and of the charge `σ` (`σ = true`: blue, `baExpFrame_gg`,
`Graph/BAGGOp.lean:785`; `σ = false`: red, `baExpFrame_gg_red`; `p ∈ lwSplit P.g.solid`, `q ∈ lwSplit p.2`). -/
structure BARCand (P : BAPGraph (Fin 2)) where
  σ : Bool
  v : P.E' ⊕ P.I'
  p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  hp : p ∈ lwSplit P.g.solid
  hq : q ∈ lwSplit p.2
  hpσ : p.1.σ = σ
  hpc : p.1.circ = true
  hqσ : q.1.σ = σ
  hqc : q.1.circ = true
  hpv : p.1.src = v
  hqv : q.1.dst = v

/-- The children of a packed graph at a candidate: the partitions of the terms of `gg2` and `gg4` of the charge of the pair
(`GGGamma`, `B:393-405`, D402; the conjugate lists for a red pair), packed through `P.ext`; every exponent pair is `(0, 0)`. -/
def BARCand.kids {P : BAPGraph (Fin 2)} (c : BARCand P) : List ((ℕ × ℕ) × BAPGraph (Fin 2)) :=
  BAExpandId_outsOf P (BAExpandId_ggL2 c.σ P.g c.p c.q) ++ BAExpandId_outsOf P (BAExpandId_ggL4 c.σ P.g c.p c.q)

/-- A selection rule: a candidate or `none`. -/
abbrev BASel := (P : BAPGraph (Fin 2)) → Option (BARCand P)

/-- The step of the procedure (`none` = leaf): the children at the selected candidate. -/
def BAstep (sel : BASel) (P : BAPGraph (Fin 2)) : Option (List ((ℕ × ℕ) × BAPGraph (Fin 2))) :=
  (sel P).map BARCand.kids

/-- The expansion procedure with fuel: `expandG` (`LWExpTerm5.lean:189`, any carrier) along `BAstep`. -/
def BAexpand (sel : BASel) (fuel : ℕ) (P : BAPGraph (Fin 2)) : List ((ℕ × ℕ) × BAPGraph (Fin 2)) :=
  expandG (BAstep sel) fuel P

/-- The list of the root: the partition of `baG5Graph k s`, each term expanded (the exponent pairs dropped). -/
def BAexpandRoot (sel : BASel) (fuel : ℕ) (k s : Bool) : List (BAPGraph (Fin 2)) :=
  (baG5Graph k s).partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd

/-- The selection rule of the leaf side: some candidate when there is one. -/
def BAselClassical : BASel := fun P =>
  open Classical in if h : Nonempty (BARCand P) then some h.some else none

/-- A graph has a candidate iff it has a circled pair `p`, `q` of solid edges of one charge with `p.1.src = q.1.dst`. -/
theorem baRCand_nonempty_iff (P : BAPGraph (Fin 2)) :
    Nonempty (BARCand P) ↔ ∃ p ∈ lwSplit P.g.solid, ∃ q ∈ lwSplit p.2, p.1.σ = q.1.σ ∧ p.1.circ = true ∧
      q.1.circ = true ∧ p.1.src = q.1.dst := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.p, c.hp, c.q, c.hq, c.hpσ.trans c.hqσ.symm, c.hpc, c.hqc, c.hpv.trans c.hqv.symm⟩
  · rintro ⟨p, hp, q, hq, h1, h2, h3, h5⟩
    exact ⟨⟨p.1.σ, p.1.src, p, q, hp, hq, rfl, h2, h1.symm, h3, rfl, h5.symm⟩⟩

/-- `BAselClassical` returns a candidate whenever there is one. -/
theorem baSelClassical_isSome (P : BAPGraph (Fin 2)) (h : Nonempty (BARCand P)) : BAselClassical P ≠ none := by
  simp [BAselClassical, h]

/-! ## 3. Normality of the children -/

/-- Every child of a candidate is a normal graph (`BAGraph.partition_normal`, `BAVocab.lean:930`; `pcomp` keeps `g`). -/
theorem BARCand.kids_normal {P : BAPGraph (Fin 2)} (c : BARCand P) : ∀ r ∈ c.kids, r.2.g.Normal := by
  have h : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')),
      ∀ r ∈ BAExpandId_outsOf P Ts, r.2.g.Normal := by
    intro I' _ _ Ts r hr
    obtain ⟨T, _, hr⟩ := List.mem_flatMap.1 hr
    obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hr
    exact T.partition_normal Q hQ
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact h _ r hr
  · exact h _ r hr

/-! ## 4. Integrability and packing -/

section Identity

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- At `t = 0` the data does not depend on the sample (`Ǧ = 0`, `G = M`; `BAExpand_Gc_zero`). -/
private theorem BAExpandId_data_zero (g0 E : ℝ) (m : ℂ) (ω ω' : Ω d L W) :
    BAlwData d L W g0 E 0 m ω = BAlwData d L W g0 E 0 m ω' := by
  have h : ∀ ω : Ω d L W, (Matrix.of fun x y => BAlwG d L W g0 E 0 m ω x y : Matrix (Idx d L W) (Idx d L W) ℂ) =
      BAlwM d L W g0 E m := by
    intro ω
    ext x y
    have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 E m ω x y
    simpa [BAlwGc, sub_eq_zero] using this
  simp only [BAlwData, h]

/-- Every graph value is integrable over `PF d L W 0` at the data `BAlwData` (`0 < t`: a tame function of the sequence
space, `BAWeightOp_val_tame` through `BAExpandW_integrable_PF`; `t = 0`: constant). -/
private theorem BAExpandId_integrable_val (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (T : BAGraph Ex Ix)
    (ℓ : Ex → Idx d L W) :
    Integrable (fun ω => T.val (BAlwData d L W g0 E t m ω) ℓ) (PF d L W 0) := by
  rcases ht0.eq_or_lt with rfl | ht
  · have h : (fun ω : Ω d L W => T.val (BAlwData d L W g0 E 0 m ω) ℓ) =
        fun _ => T.val (BAlwData d L W g0 E 0 m 0) ℓ :=
      funext fun ω => by rw [BAExpandId_data_zero g0 E m ω 0]
    rw [h]
    exact integrable_const _
  · have hm : 0 < m.im := hSelf.1
    have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    exact BAExpandW_integrable_PF hL (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓ) fun ω' => rfl

/-- Every packed graph value is integrable. -/
private theorem BAExpandId_integrable_pval (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) {E0 : Type} (Q : BAPGraph E0) (ℓe : E0 → Idx d L W) :
    Integrable (fun ω => Q.val (BAlwData d L W g0 E t m ω) ℓe) (PF d L W 0) := by
  by_cases h : ∃ ℓ' : Q.E' → Idx d L W, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    simp_rw [BAVocab_val_of_factor Q _ hℓ]
    exact BAExpandId_integrable_val hL g0 E t m hSelf ht0 ht1 Q.g ℓ'
  · simp_rw [BAVocab_val_of_not Q _ h]
    exact integrable_zero _ _ _

/-- The value of a list of terms is integrable. -/
private theorem BAExpandId_integrable_baSum (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix]
    [DecidableEq Ix] (Ts : List (BAGraph Ex Ix)) (ℓ : Ex → Idx d L W) :
    Integrable (fun ω => baSum Ts (BAlwData d L W g0 E t m ω) ℓ) (PF d L W 0) := by
  unfold baSum
  exact owx_integrable_list_sum Ts (fun T ω => T.val (BAlwData d L W g0 E t m ω) ℓ)
    fun T _ => BAExpandId_integrable_val hL g0 E t m hSelf ht0 ht1 T ℓ

private theorem BAExpandId_sum_flatMap {α β : Type*} [AddCommMonoid β] (a : List α) (g : α → List β) :
    (a.flatMap g).sum = (a.map fun x => (g x).sum).sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- The expectation of a graph value is the sum of the expectations over its BA partition (`val_eq_partition`). -/
private theorem BAExpandId_integral_partition (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I']
    [DecidableEq I'] (T : BAGraph E' I') (ℓ' : E' → Idx d L W) :
    ∫ ω, T.val (BAlwData d L W g0 E t m ω) ℓ' ∂(PF d L W 0) =
      (T.partition.map fun Q => ∫ ω, Q.val (BAlwData d L W g0 E t m ω) ℓ' ∂(PF d L W 0)).sum := by
  have h1 : ∀ ω, T.val (BAlwData d L W g0 E t m ω) ℓ' =
      (T.partition.map fun Q => Q.val (BAlwData d L W g0 E t m ω) ℓ').sum :=
    fun ω => T.val_eq_partition _ ℓ'
  simp_rw [h1]
  exact owx_integral_list_sum _ T.partition (fun Q ω => Q.val (BAlwData d L W g0 E t m ω) ℓ')
    (fun Q _ => BAExpandId_integrable_pval hL g0 E t m hSelf ht0 ht1 Q ℓ')

/-- `pcomp` reads the child through the external map of the parent: the values agree on labels that factor. -/
private theorem BAExpandId_pcomp_val {ι : Type*} [Fintype ι] [DecidableEq ι] (P : BAPGraph (Fin 2))
    (Q : BAPGraph P.E') (D : BALData ι) {ℓe : Fin 2 → ι} {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) :
    (BAExpandId_pcomp P Q).val D ℓe = Q.val D ℓ' := by
  by_cases h : ∃ ℓ'' : Q.E' → ι, ℓ' = ℓ'' ∘ Q.ext
  · obtain ⟨ℓ'', hℓ''⟩ := h
    have h2 : ℓe = ℓ'' ∘ (BAExpandId_pcomp P Q).ext := by
      rw [hℓ, hℓ'']; rfl
    rw [BAVocab_val_of_factor _ D h2, BAVocab_val_of_factor Q D hℓ'']
    rfl
  · rw [BAVocab_val_of_not Q D h, BAVocab_val_of_not]
    rintro ⟨ℓ3, hℓ3⟩
    apply h
    refine ⟨ℓ3, ?_⟩
    apply P.ext_surj.injective_comp_right
    exact hℓ.symm.trans hℓ3

/-- If the labels do not factor through `P.ext`, every child read through `P.ext` has value `0`. -/
private theorem BAExpandId_pcomp_val_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (P : BAPGraph (Fin 2))
    (Q : BAPGraph P.E') (D : BALData ι) {ℓe : Fin 2 → ι} (hf : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) :
    (BAExpandId_pcomp P Q).val D ℓe = 0 := by
  apply BAVocab_val_of_not
  rintro ⟨ℓ3, hℓ3⟩
  exact hf ⟨ℓ3 ∘ Q.ext, hℓ3⟩

/-- The expectation of the value of a list of terms is the sum of the expectations of the packed partitions of the terms. -/
private theorem BAExpandId_integral_outsOf (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ)
    (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I']
    [DecidableEq I'] (Ts : List (BAGraph P.E' I')) {ℓe : Fin 2 → Idx d L W} {ℓ' : P.E' → Idx d L W}
    (hℓ : ℓe = ℓ' ∘ P.ext) :
    ∫ ω, baSum Ts (BAlwData d L W g0 E t m ω) ℓ' ∂(PF d L W 0) =
      ((BAExpandId_outsOf P Ts).map fun r => ∫ ω, r.2.val (BAlwData d L W g0 E t m ω) ℓe ∂(PF d L W 0)).sum := by
  unfold baSum
  rw [owx_integral_list_sum _ Ts (fun T ω => T.val (BAlwData d L W g0 E t m ω) ℓ')
    (fun T _ => BAExpandId_integrable_val hL g0 E t m hSelf ht0 ht1 T ℓ')]
  unfold BAExpandId_outsOf
  rw [List.map_flatMap, BAExpandId_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun T _ => ?_)
  rw [BAExpandId_integral_partition hL g0 E t m hSelf ht0 ht1 T ℓ', List.map_map]
  refine congrArg List.sum (List.map_congr_left fun Q _ => ?_)
  simp only [Function.comp_apply]
  simp_rw [BAExpandId_pcomp_val P Q _ hℓ]

/-! ## 5. The step -/

/-- **One step of the expansion is an identity in expectation** (`GGGamma` at a candidate of either charge, `B:393-405`, D402): for
a packed graph `P` and a candidate `c`, `𝔼 P.val = Σ_{kids} 𝔼 child.val` at the data `BAlwData` over `PF d L W 0` and the
external labels `![x, y]`.  `baExpFrame_gg` (blue) or `baExpFrame_gg_red` (red) for the graph `P.g`, then `val_eq_partition` on
every term of the lists; no term is dropped by value.  Hypotheses: `BASelf`, `0 ≤ t < 1` only (no smallness of `g₀`, no scalar `m`, no normality of `P`). -/
theorem BARCand.kids_identity (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {P : BAPGraph (Fin 2)} (c : BARCand P) (x y : Idx d L W) :
    ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
      (c.kids.map fun r => ∫ ω, r.2.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum := by
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ![x, y] = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have hL' : ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        ∫ ω, P.g.val (BAlwData d L W g0 E t m ω) ℓ' ∂(PF d L W 0) := by
      simp_rw [BAVocab_val_of_factor P _ hℓ]
    rw [hL', BAExpandId_gg_identity d L W hL g0 E t m hSelf ht0 ht1 c.σ P.g ℓ' c.p c.hp c.q c.hq c.hpσ c.hpc c.hqσ c.hqc
      (c.hpv.trans c.hqv.symm)]
    have i2 := BAExpandId_integrable_baSum hL g0 E t m hSelf ht0 ht1 (BAExpandId_ggL2 c.σ P.g c.p c.q) ℓ'
    have i4 := BAExpandId_integrable_baSum hL g0 E t m hSelf ht0 ht1 (BAExpandId_ggL4 c.σ P.g c.p c.q) ℓ'
    rw [integral_add i2 i4, BAExpandId_integral_outsOf hL g0 E t m hSelf ht0 ht1 P _ hℓ,
      BAExpandId_integral_outsOf hL g0 E t m hSelf ht0 ht1 P _ hℓ]
    simp only [BARCand.kids, List.map_append, List.sum_append]
  · have h0 : ∀ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] = 0 := fun ω => BAVocab_val_of_not P _ hf
    simp_rw [h0]
    rw [integral_zero]
    symm
    refine List.sum_eq_zero fun v hv => ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hv
    have hz : ∀ {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')),
        ∀ r ∈ BAExpandId_outsOf P Ts, ∀ ω, r.2.val (BAlwData d L W g0 E t m ω) ![x, y] = 0 := by
      intro I' _ _ Ts r hr ω
      obtain ⟨T, _, hr⟩ := List.mem_flatMap.1 hr
      obtain ⟨Q, _, rfl⟩ := List.mem_map.1 hr
      exact BAExpandId_pcomp_val_zero P Q _ hf
    have h1 : ∀ ω, r.2.val (BAlwData d L W g0 E t m ω) ![x, y] = 0 := by
      rcases List.mem_append.1 hr with hr | hr
      · exact hz _ r hr
      · exact hz _ r hr
    simp_rw [h1]
    simp

/-! ## 6. The expansion and its identity -/

/-- The weighted sum over `l.flatMap (g ·)` (outputs only) is the sum over `l`, if `Φ` is the sum over `g` at every member of
`l` (the weight is `1`; twin of `lwExpTerm5_flat_sum`, `LWExpTerm5.lean:215`). -/
private theorem BAExpandId_flat_sum {X : Type*} (Φ : X → ℂ) (l : List X) (g : X → List ((ℕ × ℕ) × X))
    (hg : ∀ r ∈ l, Φ r = ((g r).map fun t => Φ t.2).sum) :
    ((l.flatMap fun r => (g r).map Prod.snd).map Φ).sum = (l.map Φ).sum := by
  rw [List.map_flatMap, BAExpandId_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun r hr => ?_)
  rw [List.map_map, hg r hr]
  rfl

/-- **The identity half of LW-14e at BA, for every selection rule and every fuel** (`B:78-108`, `B:393-405`): the list of
`BAexpandRoot sel fuel` satisfies the expectation identity `𝔼 𝒢_{xy} = Σ_μ 𝔼 Γ_μ`.  `expandG_sum` (`LWExpTerm5.lean:234`, any
carrier) with `X := BAPGraph (Fin 2)`, the invariant `Normal`, the weight `w = fun _ => 1`, and the step lemma
`kids_normal` + `kids_identity`.  The stop rule and the leaf property are not claimed (`baTwB_stuck`, probe 97).  Hypotheses of
the statement: `BASelf` and `0 ≤ t < 1` (`BAG5Identity`). -/
theorem baExpandIdentity_holds (d : ℕ) (sel : BASel) (fuel : ℕ) : BAG5Identity d (BAexpandRoot sel fuel) := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 k s x y
  have hexp := expandG_sum (BAstep sel) (fun P : BAPGraph (Fin 2) => P.g.Normal)
    (fun P => ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)) (fun _ => 1) rfl
    (fun _ _ _ _ => (one_mul (1 : ℂ)).symm)
    (by
      intro P l hP hst
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hst
      refine ⟨c.kids_normal, ?_⟩
      simp only [one_mul]
      exact BARCand.kids_identity hL g0 E t m hSelf ht0 ht1 c x y) fuel
  rw [BAExpandId_integral_partition hL g0 E t m hSelf ht0 ht1 (baG5Graph k s) ![x, y]]
  unfold BAexpandRoot
  exact (BAExpandId_flat_sum (fun P : BAPGraph (Fin 2) => ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0))
    (baG5Graph k s).partition (fun P => BAexpand sel fuel P) (by
      intro P _
      have := (hexp P (BAGraph.partition_normal _ P ‹_›)).1
      simpa [BAexpand] using this)).symm

end Identity

/-! ## 7. Compiled instances (namespace `RBM.Graph.BAExpandIdInst`)

`d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i`, `t = 1/2` (`BASelf` is `BAExpandInst.baSelf_zero`, `BAExpand.lean:865`); `Idx 3 3 1`
has `27` points.  The packed graph is the shape of `baG5Graph true true` with every solid edge circled (a normal term of its
partition): `5` solid edges, `2` waved edges, `3` internal vertices, `E' = Fin 2`, `I' = Fin 3`, `ext = id`.  The candidate is at
`v = inr 0`: `p = Ǧ_{inr0 inr1}`, `q = Ǧ_{inl0 inr0}`. -/

namespace BAExpandIdInst

set_option maxRecDepth 100000

/-- `baG5Graph true true` with every solid edge circled. -/
def baG5Circ : BAGraph (Fin 2) (Fin 3) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 0) (Sum.inr 1),
    SEdge.mk true true (Sum.inr 1) (Sum.inr 2), SEdge.mk true true (Sum.inr 2) (Sum.inl 1),
    SEdge.mk true true (Sum.inl 1) (Sum.inl 0)]
  waved := [WEdge.mk true true (Sum.inr 1) (Sum.inr 0), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := []

theorem baG5Circ_normal : baG5Circ.Normal := ⟨by decide, by decide⟩

/-- The packed instance graph (external `x, y`, three internal vertices; normal). -/
abbrev instP : BAPGraph (Fin 2) :=
  { E' := Fin 2, I' := Fin 3, ext := id, ext_surj := Function.surjective_id, g := baG5Circ }

/-- A `GG` candidate of `instP` at `v = inr 0`: `p = Ǧ_{v,inr1}`, `q = Ǧ_{inl0,v}`. -/
def instCand : BARCand instP where
  σ := true
  v := Sum.inr 0
  p := (SEdge.mk true true (Sum.inr 0) (Sum.inr 1),
    [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 1) (Sum.inr 2),
      SEdge.mk true true (Sum.inr 2) (Sum.inl 1), SEdge.mk true true (Sum.inl 1) (Sum.inl 0)])
  q := (SEdge.mk true true (Sum.inl 0) (Sum.inr 0),
    [SEdge.mk true true (Sum.inr 1) (Sum.inr 2), SEdge.mk true true (Sum.inr 2) (Sum.inl 1),
      SEdge.mk true true (Sum.inl 1) (Sum.inl 0)])
  hp := by simp [lwSplit, instP, baG5Circ]
  hq := by simp [lwSplit]
  hpσ := rfl
  hpc := rfl
  hqσ := rfl
  hqc := rfl
  hpv := rfl
  hqv := rfl

/-- The step at `instCand` is not degenerate: `gg2` has `8` terms, `gg4` has `5`, and the children number `63`
(partition term counts), `instP` has a candidate, `BAselClassical` selects one. -/
theorem instCand_sizes : (instP.g.gg2 instCand.p instCand.q).length = 8 ∧
    (instP.g.gg4 instCand.p instCand.q).length = 5 ∧ instCand.kids.length = 63 := by
  decide

theorem instP_selected : BAselClassical instP ≠ none := baSelClassical_isSome _ ⟨instCand⟩

/-- The conjugate of `baG5Circ`: every solid edge red (`σ = false`, circled), the coloured waved edge conjugated
(`S⁺_{inr1 inr0} ↦ S⁻_{inr0 inr1}`, `BAExpandId_flipW`). -/
def baG5CircRed : BAGraph (Fin 2) (Fin 3) where
  solid := [SEdge.mk false true (Sum.inl 0) (Sum.inr 0), SEdge.mk false true (Sum.inr 0) (Sum.inr 1),
    SEdge.mk false true (Sum.inr 1) (Sum.inr 2), SEdge.mk false true (Sum.inr 2) (Sum.inl 1),
    SEdge.mk false true (Sum.inl 1) (Sum.inl 0)]
  waved := [WEdge.mk true false (Sum.inr 0) (Sum.inr 1), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := []

theorem baG5CircRed_normal : baG5CircRed.Normal := ⟨by decide, by decide⟩

/-- The packed red instance graph (the conjugate of `instP`; normal). -/
abbrev instPRed : BAPGraph (Fin 2) :=
  { E' := Fin 2, I' := Fin 3, ext := id, ext_surj := Function.surjective_id, g := baG5CircRed }

/-- A **red** `GG` candidate of `instPRed` at `v = inr 0`: `p = Ḡ̌_{v,inr1}`, `q = Ḡ̌_{inl0,v}` (both `σ = false`, circled). -/
def instCandRed : BARCand instPRed where
  σ := false
  v := Sum.inr 0
  p := (SEdge.mk false true (Sum.inr 0) (Sum.inr 1),
    [SEdge.mk false true (Sum.inl 0) (Sum.inr 0), SEdge.mk false true (Sum.inr 1) (Sum.inr 2),
      SEdge.mk false true (Sum.inr 2) (Sum.inl 1), SEdge.mk false true (Sum.inl 1) (Sum.inl 0)])
  q := (SEdge.mk false true (Sum.inl 0) (Sum.inr 0),
    [SEdge.mk false true (Sum.inr 1) (Sum.inr 2), SEdge.mk false true (Sum.inr 2) (Sum.inl 1),
      SEdge.mk false true (Sum.inl 1) (Sum.inl 0)])
  hp := by simp [lwSplit, instPRed, baG5CircRed]
  hq := by simp [lwSplit]
  hpσ := rfl
  hpc := rfl
  hqσ := rfl
  hqc := rfl
  hpv := rfl
  hqv := rfl

/-- The red step is not degenerate either: `gg2r` has `8` terms, `gg4r` has `5`, the children number `63`. -/
theorem instCandRed_sizes : (BAExpandId_gg2r instPRed.g instCandRed.p instCandRed.q).length = 8 ∧
    (BAExpandId_gg4r instPRed.g instCandRed.p instCandRed.q).length = 5 ∧ instCandRed.kids.length = 63 := by
  decide

theorem instPRed_selected : BAselClassical instPRed ≠ none := baSelClassical_isSome _ ⟨instCandRed⟩

/-- The root is not degenerate either: its partition has `2^5 = 32` terms for every `k`, `s` (each solid edge is circled or an
`M`-dotted edge). -/
theorem baG5Graph_partition_length : ∀ k s : Bool, (baG5Graph k s).partition.length = 32 := by
  decide

/-- **Instance of `BARCand.kids_identity`** (one step of the expansion) at `d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`,
`m = i`, `t = 1/2`, the packed instance graph and its candidate, all labels `x, y`: no hypothesis. -/
theorem baExpandId_inst_kids_identity (x y : Idx 3 3 1) :
    ∫ ω, instP.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      (instCand.kids.map fun r => ∫ ω, r.2.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
  BARCand.kids_identity (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    instCand x y

/-- **Instance of `BARCand.kids_normal`** at the same candidate. -/
theorem baExpandId_inst_kids_normal : ∀ r ∈ instCand.kids, r.2.g.Normal := instCand.kids_normal

/-- **Instance of the red-charge `GG` identity `baExpFrame_gg_red`** at `d = 3`, `L = 3`, `W = 1`, `g₀ = 0`, `E = 0`, `m = i`,
`t = 1/2`, the red graph `baG5CircRed` and the red pair of `instCandRed`, all external labels: only `BASelf`, `3 ≤ 3`,
`0 ≤ 1/2 < 1`, the candidate fields. -/
theorem baExpandId_inst_gg_red (ℓe : Fin 2 → Idx 3 3 1) :
    ∫ ω, baG5CircRed.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe ∂(PF 3 3 1 0) =
      ∫ ω, baSum (BAExpandId_gg2r baG5CircRed instCandRed.p instCandRed.q) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe +
        baSum (BAExpandId_gg4r baG5CircRed instCandRed.p instCandRed.q) (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ℓe
        ∂(PF 3 3 1 0) :=
  baExpFrame_gg_red 3 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    baG5CircRed ℓe instCandRed.p instCandRed.hp instCandRed.q instCandRed.hq rfl rfl rfl rfl rfl

/-- **Instance of `BARCand.kids_identity` at a red candidate**: the step at `instCandRed`, all labels `x, y`. -/
theorem baExpandId_inst_kids_identity_red (x y : Idx 3 3 1) :
    ∫ ω, instPRed.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      (instCandRed.kids.map fun r => ∫ ω, r.2.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
  BARCand.kids_identity (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero (by norm_num) (by norm_num)
    instCandRed x y

/-- **Instance of `BARCand.kids_normal` at a red candidate.** -/
theorem baExpandId_inst_kids_normal_red : ∀ r ∈ instCandRed.kids, r.2.g.Normal := instCandRed.kids_normal

/-- **Instance of `baExpandIdentity_holds`** at the root `baG5Graph true true`, fuel `1`, the rule `BAselClassical`, all external
labels `x, y`: no hypothesis (`BASelf` is `BAExpandInst.baSelf_zero`, `3 ≤ 3`, `0 ≤ 1/2 < 1`). -/
theorem baExpandId_inst_identity (k s : Bool) (x y : Idx 3 3 1) :
    ∫ ω, (baG5Graph k s).val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      ((BAexpandRoot BAselClassical 1 k s).map fun q =>
        ∫ ω, q.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
  baExpandIdentity_holds 3 BAselClassical 1 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero
    (by norm_num) (by norm_num) k s x y

/-- The same at fuel `2`. -/
example (k s : Bool) (x y : Idx 3 3 1) :
    ∫ ω, (baG5Graph k s).val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0) =
      ((BAexpandRoot BAselClassical 2 k s).map fun q =>
        ∫ ω, q.val (BAlwData 3 3 1 0 0 (1 / 2) Complex.I ω) ![x, y] ∂(PF 3 3 1 0)).sum :=
  baExpandIdentity_holds 3 BAselClassical 2 3 1 (by norm_num) 0 0 (1 / 2) Complex.I BAExpandInst.baSelf_zero
    (by norm_num) (by norm_num) k s x y

/-- The engine at the BA carrier with the weight `1` (probe 490-494). -/
example (st : BAPGraph (Fin 2) → Option (List ((ℕ × ℕ) × BAPGraph (Fin 2)))) (Inv : BAPGraph (Fin 2) → Prop)
    (Φ : BAPGraph (Fin 2) → ℂ) : ExpandGSum st Inv Φ (fun _ => 1) :=
  expandG_sum st Inv Φ (fun _ => 1)

end BAExpandIdInst

end RBM.Graph

end
