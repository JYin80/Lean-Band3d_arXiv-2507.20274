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

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:393-405` (`GGGamma`, D402 coefficient `W - 1 = M⁺S⁺`);
design `docs/reports/T2398-design.md` §4 (the identity in expectation), probe
`t/T2398:RBM3D/Probe/T2398Pins.lean:135-153, 490-494` (statements and engine instance, copied).  The twin of the identity half
of `Graph/LWExpTerm5.lean` (`lwExpandIdentity_holds`, `:594`) without its leaf-side parts.

## Contents (namespace `RBM.Graph`; private prefix `BAExpandId_`)

1. **Vocabulary** (probe 135-153): `baG5Graph k s`, `BAG5Identity d Ls`.
2. **The procedure**: `BAExpandId_pcomp`, `BAExpandId_outsOf` (the packing of the partitions of a list of terms through the
   external map of the parent), `BARCand` (a `GG` candidate: a vertex `v` and two **blue** circled solid edges
   `p = Ǧ_{vy}`, `q = Ǧ_{y'v}` of the same graph), `BARCand.kids` (the partitions of `gg2 ++ gg4`, every exponent pair
   `(0, 0)`), `BASel`, `BAstep`, `BAexpand` (= `expandG` of `LWExpTerm5`), `BAexpandRoot`, `BAselClassical`.
3. **Normality** of the children: `BARCand.kids_normal` (`BAGraph.partition_normal`).
4. **Integrability and packing**: every graph value is integrable over `PF d L W 0`, the partition and the packed
   graph read through `P.ext`.
5. **The step**: `BARCand.kids_identity` (`baExpFrame_gg` + `BAGraph.val_eq_partition` + packing).
6. **The expansion**: `baExpandIdentity_holds`: `BAG5Identity d (BAexpandRoot sel fuel)` for every selector and fuel, from
   `expandG_sum` of `LWExpTerm5` (imported) with the weight `w = fun _ => 1`.
7. Compiled instances (`BAExpandIdInst`, `d = 3`).

`LWG5Progress` (`LWExpTerm5:72`) is **not** claimed: it fails at BA (`baTwB_stuck`, probe 97); the stop rule and the leaf
property are L4e-C's.  The candidate rule is blue only, as the merged identity `baExpFrame_gg` (`Graph/BAGGOp.lean:785`) is.
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

/-! ## 2. The procedure -/

/-- A packed graph read through the external map of its parent (the twin of `pcomp`, `LWExpTerm5.lean:120`). -/
def BAExpandId_pcomp (P : BAPGraph (Fin 2)) (Q : BAPGraph P.E') : BAPGraph (Fin 2) :=
  { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g }

/-- The outputs of a step: the BA partition of every term, packed and read through `P.ext` (twin of `BAPGraph.outsOf`,
`t/T2395:RBM3D/Probe/T2395Pins.lean:154`), every exponent pair `(0, 0)` (`expandG`'s carrier). -/
def BAExpandId_outsOf (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) :
    List ((ℕ × ℕ) × BAPGraph (Fin 2)) :=
  Ts.flatMap fun T => T.partition.map fun Q => ((0, 0), BAExpandId_pcomp P Q)

/-- **A `GG` candidate** of a packed graph, as data: a vertex `v` and two solid edges of the same graph,
`p.1 = Ǧ_{vy}` and `q.1 = Ǧ_{y'v}`, both blue and circled (`p ∈ lwSplit P.g.solid`, `q ∈ lwSplit p.2`): exactly the
hypotheses of `baExpFrame_gg` (`Graph/BAGGOp.lean:785`).  Blue only: the merged identity (`BAGGGamma`) is for the
charge `σ = true`. -/
structure BARCand (P : BAPGraph (Fin 2)) where
  v : P.E' ⊕ P.I'
  p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))
  hp : p ∈ lwSplit P.g.solid
  hq : q ∈ lwSplit p.2
  hpσ : p.1.σ = true
  hpc : p.1.circ = true
  hqσ : q.1.σ = true
  hqc : q.1.circ = true
  hpv : p.1.src = v
  hqv : q.1.dst = v

/-- The children of a packed graph at a candidate: the partitions of the terms of `gg2` and `gg4`
(`GGGamma`, `B:393-405`, D402), packed through `P.ext`; every exponent pair is `(0, 0)`. -/
def BARCand.kids {P : BAPGraph (Fin 2)} (c : BARCand P) : List ((ℕ × ℕ) × BAPGraph (Fin 2)) :=
  BAExpandId_outsOf P (P.g.gg2 c.p c.q) ++ BAExpandId_outsOf P (P.g.gg4 c.p c.q)

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

/-- A graph has a candidate iff it has a blue circled pair `p`, `q` of solid edges with `p.1.src = q.1.dst`. -/
theorem baRCand_nonempty_iff (P : BAPGraph (Fin 2)) :
    Nonempty (BARCand P) ↔ ∃ p ∈ lwSplit P.g.solid, ∃ q ∈ lwSplit p.2, p.1.σ = true ∧ p.1.circ = true ∧
      q.1.σ = true ∧ q.1.circ = true ∧ p.1.src = q.1.dst := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.p, c.hp, c.q, c.hq, c.hpσ, c.hpc, c.hqσ, c.hqc, c.hpv.trans c.hqv.symm⟩
  · rintro ⟨p, hp, q, hq, h1, h2, h3, h4, h5⟩
    exact ⟨⟨p.1.src, p, q, hp, hq, h1, h2, h3, h4, rfl, h5.symm⟩⟩

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

/-- **One step of the expansion is an identity in expectation** (`GGGamma` at a candidate, `B:393-405`, D402): for a packed
graph `P` and a candidate `c`, `𝔼 P.val = Σ_{kids} 𝔼 child.val` at the data `BAlwData` over `PF d L W 0` and the external
labels `![x, y]`.  `baExpFrame_gg` for the graph `P.g`, then `val_eq_partition` on every term of `gg2`, `gg4`; no term is
dropped by value.  Hypotheses: `BASelf`, `0 ≤ t < 1` only (no smallness of `g₀`, no scalar `m`, no normality of `P`). -/
theorem BARCand.kids_identity (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {P : BAPGraph (Fin 2)} (c : BARCand P) (x y : Idx d L W) :
    ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
      (c.kids.map fun r => ∫ ω, r.2.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0)).sum := by
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ![x, y] = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have hL' : ∫ ω, P.val (BAlwData d L W g0 E t m ω) ![x, y] ∂(PF d L W 0) =
        ∫ ω, P.g.val (BAlwData d L W g0 E t m ω) ℓ' ∂(PF d L W 0) := by
      simp_rw [BAVocab_val_of_factor P _ hℓ]
    rw [hL', baExpFrame_gg d L W hL g0 E t m hSelf ht0 ht1 P.g ℓ' c.p c.hp c.q c.hq c.hpσ c.hpc c.hqσ c.hqc
      (c.hpv.trans c.hqv.symm)]
    have i2 := BAExpandId_integrable_baSum hL g0 E t m hSelf ht0 ht1 (P.g.gg2 c.p c.q) ℓ'
    have i4 := BAExpandId_integrable_baSum hL g0 E t m hSelf ht0 ht1 (P.g.gg4 c.p c.q) ℓ'
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

end Identity

end RBM.Graph

end
