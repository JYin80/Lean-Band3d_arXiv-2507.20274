/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALvl1C
import RBM3D.Graph.BAStepS

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# The BA engine at the start terms of `G = Ǧ + M` on `fxyPowGraph p`

Paper: Subappendix B.3 (Definition B.5 `def scalingBA`, Lemma B.6 `lanlw`, Lemma B.7
`lem_lweight`: the `lvl1` lemma at block Anderson) and (B.11) `eq:originGamma`.  This is the BA
counterpart of `Graph/LWEngine.lean`, reduced by the data-free recursion `baLvl1Lemma_holds`
(`Graph/BALvl1C`) and by `Graph/BAStepS` ((6) along `BAReach`): the `m`-tag half of the band engine
has no BA content (the coefficients `m^j m̄^{j'}` are `M`-dotted edges here, see `Graph/BAExpandId`).

## Contents (namespace `RBM.Graph`; private prefix `BAEngine_`)

1. **Black waved edges** (as `LWEngine` Section 5): `baStep_nWS`, `ba_nWS_ge`, `baStart_nWS`.
2. **The conclusion**: `BALocRegConcl`.
3. **The assembly**: `baEngine_assemble`.
4. **The BA `lem:localregular`**: `ba_localregularX`.
5. A locally standard graph `BAEngine_pL` (`BAEngine_pL_locStd`), a witness that the hypothesis
   `BAGraph.LocStd`, which `baEngine_assemble` carries inside a hypothesis, is satisfiable.

The data hypotheses are only `BASelf` and `0 ≤ t < 1`; no `m`-tag, no path properties (1)-(5).  The
first hypothesis of `baEngine_assemble` and `ba_localregularX` is the shape binder of `BALocReg6`
(`Graph/BAStepS.lean`, the three shapes `BAShape.e2`, `macroA`, `macroB`), verbatim; it is discharged
where the engine is used (`Graph/BAProvB.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. Black waved edges: the number of waved edges with `col = false` does not fall along `BAReach`
(as `lw_nWS_ge` in `Graph/LWEngine.lean`)

Every term of a frame step is `BAGraph.ext` / `BAGraph.lanlwExt` on the (twisted) parent: its waved edges are mapped (colour kept) and new ones appended;
`splitG` keeps `waved`, `merge` maps it, the twist maps it by `conj` / `transpose` (colour kept). -/

section NWS

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAEngine_col_conj {V : Type*} (e : WEdge V) : (WEdge.conj e).col = e.col := by
  cases h : e.col <;> simp [WEdge.conj, h]

private theorem BAEngine_col_transpose {V : Type*} (e : WEdge V) : (WEdge.transpose e).col = e.col := rfl

/-- the twist keeps the number of black waved edges -/
private theorem BAEngine_twist_nWS (c t : Bool) (Γ : BAGraph E I) :
    (Γ.twist c t).waved.countP (fun e => !e.col) = Γ.waved.countP (fun e => !e.col) := by
  cases c <;> cases t <;>
    simp [BAGraph.twist, lwSymmTwistG, LGraph.conj, LGraph.transpose, List.countP_map, Function.comp_def, BAEngine_col_conj,
      BAEngine_col_transpose]

/-- the terms of the partition have the black waved edges of the graph (`splitG` keeps `waved`, `merge` maps it keeping the colour) -/
private theorem BAEngine_partition_nWS (T : BAGraph E I) :
    ∀ Q ∈ T.partition, Q.g.waved.countP (fun e => !e.col) = T.waved.countP (fun e => !e.col) := by
  intro Q hQ
  simp only [BAGraph.partition, BAGraph.splitG, List.map_map, List.mem_map] at hQ
  obtain ⟨r, -, rfl⟩ := hQ
  simp [Function.comp_def, BAGraph.packMerge, BAGraph.merge, LGraph.merge, List.countP_map, WEdge.map]

/-- the outputs of a step in the frame: each is a term of the partition of a term of the list -/
private theorem BAEngine_outsOf_nWS {E : Type} (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I'))
    (n : ℕ) (h : ∀ T ∈ Ts, n ≤ T.waved.countP (fun e => !e.col)) :
    ∀ Q ∈ P.outsOf Ts, n ≤ Q.g.waved.countP (fun e => !e.col) := by
  intro Q hQ
  simp only [BAPGraph.outsOf, List.mem_flatMap, List.mem_map] at hQ
  obtain ⟨T, hT, Q0, hQ0, rfl⟩ := hQ
  change n ≤ Q0.g.waved.countP (fun e => !e.col)
  rw [BAEngine_partition_nWS T Q0 hQ0]
  exact h T hT

private theorem BAEngine_ext_ge (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    Γ.waved.countP (fun e => !e.col) ≤ (BAGraph.ext k Γ rest s w md).waved.countP (fun e => !e.col) := by
  simp [BAGraph.ext, LGraph.owxExt, List.countP_append, List.countP_map, Function.comp_def, WEdge.map]

private theorem BAEngine_lanlwExt_ge (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) :
    Γ.waved.countP (fun e => !e.col) ≤ (BAGraph.lanlwExt Γ rest c s w md).waved.countP (fun e => !e.col) := by
  simp [BAGraph.lanlwExt, LGraph.owxExt, List.countP_append, List.countP_map, Function.comp_def, WEdge.map]

private theorem BAEngine_lanlwD_ge (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.waved.countP (fun e => !e.col) ≤ (BAGraph.lanlwD Γ p q).waved.countP (fun e => !e.col) :=
  BAEngine_lanlwExt_ge _ _ _ _ _ _

private theorem BAEngine_lanlwT1_ge (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.waved.countP (fun e => !e.col) ≤ (BAGraph.lanlwT1 Γ p).waved.countP (fun e => !e.col) :=
  BAEngine_lanlwExt_ge _ _ _ _ _ _

private theorem BAEngine_lanlwD_map_ge (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (l : List (SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))) :
    ∀ T ∈ l.map (BAGraph.lanlwD Γ p), Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hT
  exact BAEngine_lanlwD_ge _ _ _

private theorem BAEngine_lw2_ge (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.lw2 p, Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  simp only [BAGraph.lw2, List.mem_cons] at hT
  rcases hT with rfl | hT
  · exact BAEngine_ext_ge _ _ _ _ _ _
  · exact BAEngine_lanlwD_map_ge _ _ _ T hT

private theorem BAEngine_lw4_ge (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.lw4 p, Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  simp only [BAGraph.lw4, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, -, rfl⟩ <;> exact BAEngine_ext_ge _ _ _ _ _ _

private theorem BAEngine_gg2_ge (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg2 p q, Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  simp only [BAGraph.gg2, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hT
  rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, -, rfl⟩ <;> exact BAEngine_ext_ge _ _ _ _ _ _

private theorem BAEngine_gg4_ge (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ Γ.gg4 p q, Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  simp only [BAGraph.gg4, List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hT
  rcases hT with (rfl | rfl) | ⟨r, -, rfl⟩ <;> exact BAEngine_ext_ge _ _ _ _ _ _

private theorem BAEngine_lanlwTerms_ge (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ BAGraph.lanlwTerms Γ p, Γ.waved.countP (fun e => !e.col) ≤ T.waved.countP (fun e => !e.col) := by
  intro T hT
  simp only [BAGraph.lanlwTerms, List.mem_cons] at hT
  rcases hT with rfl | hT
  · exact BAEngine_lanlwT1_ge _ _
  · exact BAEngine_lanlwD_map_ge _ _ _ T hT

/-- **A frame step does not lower the number of black waved edges** (the five kinds of `BAFrameStep` in `Graph/BASim.lean`; as `lwEngine_locStep_nWS` for the frame). -/
private theorem BAEngine_frame_nWS {E : Type} {P : BAPGraph E} {F : List (BAPGraph E)} (h : BAFrameStep P F) :
    ∀ Q ∈ F, P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) := by
  cases h with
  | weight p hp hh =>
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BAEngine_outsOf_nWS P _ _ (BAEngine_lw2_ge _ _) Q hQ
    · exact BAEngine_outsOf_nWS P _ _ (BAEngine_lw4_ge _ _) Q hQ
  | within p hp hh =>
    intro Q hQ
    simp only [BAPGraph.withinOuts, List.mem_append] at hQ
    rcases hQ with (hQ | hQ) | hQ
    · refine BAEngine_outsOf_nWS P _ _ (fun T hT => ?_) Q hQ
      rcases List.mem_cons.1 hT with rfl | hT
      · exact BAEngine_ext_ge _ _ _ _ _ _
      · exact BAEngine_lanlwD_map_ge _ _ _ T hT
    · exact BAEngine_outsOf_nWS P _ _ (fun T hT => (BAEngine_ext_ge _ _ _ _ _ _).trans (BAEngine_lw2_ge _ _ T hT)) Q hQ
    · exact BAEngine_outsOf_nWS P _ _ (fun T hT => (BAEngine_ext_ge _ _ _ _ _ _).trans (BAEngine_lw4_ge _ _ T hT)) Q hQ
  | edge p hp hh x hx hwf hv hint hbad =>
    exact BAEngine_outsOf_nWS P _ _ (BAEngine_lanlwTerms_ge _ _)
  | gg p hp q hq hh x hx hwf hint hnb =>
    intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · exact BAEngine_outsOf_nWS P _ _ (BAEngine_gg2_ge _ _ _) Q hQ
    · exact BAEngine_outsOf_nWS P _ _ (BAEngine_gg4_ge _ _ _) Q hQ
  | ggSplit p hp q j hj hh a a' hx hne hsame hwf hint hnb =>
    intro Q hQ
    simp only [BAPGraph.splitOuts, List.mem_append] at hQ
    rcases hQ with ((hQ | hQ) | hQ) | hQ
    · refine BAEngine_outsOf_nWS P _ _ (fun T hT => ?_) Q hQ
      rcases List.mem_cons.1 hT with rfl | hT
      · exact BAEngine_lanlwT1_ge _ _
      · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hT
        exact BAEngine_lanlwD_ge _ _ _
    · refine BAEngine_outsOf_nWS P _ _ (fun T hT => ?_) Q hQ
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl <;> exact BAEngine_ext_ge _ _ _ _ _ _
    · exact BAEngine_outsOf_nWS P _ _ (fun T hT => (BAEngine_ext_ge _ _ _ _ _ _).trans (BAEngine_gg2_ge _ _ _ T hT)) Q hQ
    · exact BAEngine_outsOf_nWS P _ _ (fun T hT => (BAEngine_ext_ge _ _ _ _ _ _).trans (BAEngine_gg4_ge _ _ _ T hT)) Q hQ

end NWS

/-- **A step does not lower the number of black waved edges** (as `lwEngine_locStep_nWS`; the twist keeps them, the frame step by `BAEngine_frame_nWS`). -/
theorem baStep_nWS : ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs →
    ∀ Q ∈ outs, P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) := by
  rintro E P outs ⟨c, t, F, hF, rfl⟩ Q hQ
  obtain ⟨Q', hQ', rfl⟩ := List.mem_map.1 hQ
  have h := BAEngine_frame_nWS hF Q' hQ'
  have e1 : (BAPGraph.twist c t P).g.waved.countP (fun e => !e.col) = P.g.waved.countP (fun e => !e.col) := BAEngine_twist_nWS c t P.g
  have e2 : (BAPGraph.twist c t Q').g.waved.countP (fun e => !e.col) = Q'.g.waved.countP (fun e => !e.col) := BAEngine_twist_nWS c t Q'.g
  rw [e2, ← e1]
  exact h

/-- **The number of black waved edges does not fall along `BAReach`** (as `lw_nWS_ge`). -/
theorem ba_nWS_ge : ∀ {E : Type} {K : ℤ} {P Q : BAPGraph E}, BAReach K P Q →
    P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) := by
  intro E K P Q h
  exact ba_lvl1_induction h (fun R => P.g.waved.countP (fun e => !e.col) ≤ R.g.waved.countP (fun e => !e.col)) le_rfl
    (fun A L hst hA B hB => hA.trans (baStep_nWS A L hst B hB))

/-- **Every start term has `p` black waved edges** (as `lwEngine_fxy_nWS`): `splitG` keeps the waved edges of `fxyPowGraph p`, `merge` maps them. -/
theorem baStart_nWS : ∀ (p : ℕ), ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, P0.g.waved.countP (fun e => !e.col) = p := by
  intro p P0 hP0
  rw [BAEngine_partition_nWS _ P0 hP0]
  simp [BAGraph.ofLGraph, fxyPowGraph, List.countP_map, Function.comp_def]

/-! ## 2. The conclusion `BALocRegConcl` (as `LWLocRegConcl`) -/

/-- **The six-conjunct conclusion of the BA engine** (as `LWLocRegConcl`).  At the start terms
`(BAGraph.ofLGraph (fxyPowGraph p)).partition`: (a) the outputs are locally standard at atoms with (6) in its BA form (`2p ≤ ord`, and `3p ≤ ord` at distinct
external atoms); (b) the errors have scaling size `≤ W^{-D}` in the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`; (c) every graph is reached from
a start term below that term's cutoff, normal, with the counters of `BAlvl1LemmaSize`; (d) the identity of expectations at `BAlwData` (`BASelf`, `0 ≤ t < 1` only).
No `m`-tags (BA steps carry no exponent pairs); no path properties (1)-(5). -/
def BALocRegConcl (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (BAPGraph (Fin 2))) : Prop :=
  (∀ Q ∈ outs, Q.g.LocStd ∧ 2 * (p : ℤ) ≤ Q.scalingOrder ∧
    (¬ atomSetoid Q.g (Sum.inl (Q.ext 0)) (Sum.inl (Q.ext 1)) → 3 * (p : ℤ) ≤ Q.scalingOrder)) ∧
  (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
  (∀ Q ∈ outs ++ errs, ∃ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
    BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
      Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ ℓe : Fin 2 → Idx d L W,
      ∫ ω, (BAGraph.ofLGraph (fxyPowGraph p)).val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-! ## 3. The assembly (as `lwEngine_assemble`) -/

section Assemble

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- the value of a packed graph at `BAlwData` is integrable (as the private `BALvl1C_integrable_pval` of `Graph/BALvl1C.lean`) -/
private theorem BAEngine_integrable_pval (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E : Type} (Q : BAPGraph E) (ℓe : E → Idx d L W) :
    Integrable (fun ω => Q.val (BAlwData d L W g0 Em t m ω) ℓe) (PF d L W 0) := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → Idx d L W, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have h : (fun ω => Q.val (BAlwData d L W g0 Em t m ω) ℓe) = fun ω => Q.g.val (BAlwData d L W g0 Em t m ω) ℓ' :=
      funext fun ω => BALvl1A_val_of_factor Q _ hℓ
    rw [h]
    exact BALvl1A_integrable_val hL g0 Em t m hSelf ht0 ht1 Q.g ℓ'
  · have h : (fun ω => Q.val (BAlwData d L W g0 Em t m ω) ℓe) = fun _ => 0 := funext fun ω => BALvl1A_val_of_not Q _ hf
    rw [h]
    exact integrable_zero _ _ _

/-- the integral of the value of a list of packed graphs is the list sum of the integrals (as the private `BALvl1C_integral_comb` of `Graph/BALvl1C.lean`) -/
private theorem BAEngine_integral_comb (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E : Type} (Ls : List (BAPGraph E)) (ℓe : E → Idx d L W) :
    ∫ ω, BAComb.val Ls (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      (Ls.map fun Q => ∫ ω, Q.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)).sum :=
  owx_integral_list_sum (PF d L W 0) Ls (fun Q ω => Q.val (BAlwData d L W g0 Em t m ω) ℓe)
    fun Q _ => BAEngine_integrable_pval hL g0 Em t m hSelf ht0 ht1 Q ℓe

end Assemble

/-- **The assembly** (as `lwEngine_assemble`): lists `fo P0`, `fe P0` with the conclusion of `BAlvl1LemmaSize` (`Graph/BALvl1C.lean`) at every
start term give `BALocRegConcl` for the concatenated lists.  (a) `LocStd` and the order from the hypothesis on `fo P0`, `2p ≤ ord` and `3p ≤ ord` by
`baLocReg6_reach` along the `BAReach` of the third conjunct; (b), (c) per start term; (d) `BAGraph.val_eq_partition` (pathwise), the integral of a list sum, the identity per start
term, `lvl1_sum_flatMap`.  The first hypothesis is the shape binder of `BALocReg6` (`Graph/BAStepS.lean`), verbatim. -/
theorem baEngine_assemble : (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
  ∀ (p : ℕ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (fo fe : BAPGraph (Fin 2) → List (BAPGraph (Fin 2))),
    (∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition,
      (∀ Q ∈ fo P0, Q.g.LocStd ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ fe P0, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
        (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
      (∀ Q ∈ fo P0 ++ fe P0, BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
        Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
        ∀ ℓe : Fin 2 → Idx d L W,
          ∫ ω, P0.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
            ∫ ω, BAComb.val (fo P0 ++ fe P0) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) →
    BALocRegConcl p c K0 d D (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fo)
      (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fe) := by
  intro hX p c K0 d D fo fe h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨P0, hP0, hQ'⟩ := List.mem_flatMap.1 hQ
    obtain ⟨hout, -, hreach, -⟩ := h P0 hP0
    have hLS := (hout Q hQ').1
    have h6 := baLocReg6_reach p P0 hP0 hX _ Q (hreach Q (List.mem_append_left _ hQ')).1
    exact ⟨hLS, (h6.2 hLS).1, (h6.2 hLS).2⟩
  · intro Q hQ
    obtain ⟨P0, hP0, hQ'⟩ := List.mem_flatMap.1 hQ
    exact (h P0 hP0).2.1 Q hQ'
  · intro Q hQ
    rcases List.mem_append.1 hQ with hQ | hQ
    · obtain ⟨P0, hP0, hQ'⟩ := List.mem_flatMap.1 hQ
      exact ⟨P0, hP0, (h P0 hP0).2.2.1 Q (List.mem_append_left _ hQ')⟩
    · obtain ⟨P0, hP0, hQ'⟩ := List.mem_flatMap.1 hQ
      exact ⟨P0, hP0, (h P0 hP0).2.2.1 Q (List.mem_append_right _ hQ')⟩
  · intro Lx W _ _ hLx g0 Em t m hSelf ht0 ht1 ℓe
    have hI := fun (F : List (BAPGraph (Fin 2))) =>
      BAEngine_integral_comb (d := d) (L := Lx) (W := W) hLx g0 Em t m hSelf ht0 ht1 F ℓe
    simp only [BAGraph.val_eq_partition (BAGraph.ofLGraph (fxyPowGraph p))]
    rw [hI, hI, List.map_append, List.sum_append,
      lvl1_sum_flatMap _ fo (fun Q => ∫ ω, Q.val (BAlwData d Lx W g0 Em t m ω) ℓe ∂(PF d Lx W 0)),
      lvl1_sum_flatMap _ fe (fun Q => ∫ ω, Q.val (BAlwData d Lx W g0 Em t m ω) ℓe ∂(PF d Lx W 0)), ← List.sum_map_add]
    refine congrArg List.sum (List.map_congr_left fun P0 hP0 => ?_)
    have h1 := (h P0 hP0).2.2.2 Lx W hLx g0 Em t m hSelf ht0 ht1 ℓe
    rw [hI, List.map_append, List.sum_append] at h1
    exact h1

/-! ## 4. The BA `lem:localregular` (as `lw_localregularX`) -/

/-- the conclusion of `BAlvl1LemmaSize` at a start term, for given lists (the specification that `lvl1_choose_list` chooses `fo`, `fe` for) -/
private def BAEngine_Spec (c : ℝ) (K0 d : ℕ) (D : ℝ) (P0 : BAPGraph (Fin 2)) (fo fe : List (BAPGraph (Fin 2))) : Prop :=
  (∀ Q ∈ fo, Q.g.LocStd ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder) ∧
  (∀ Q ∈ fe, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
  (∀ Q ∈ fo ++ fe, BAReach (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 Q ∧ Q.g.Normal ∧ P0.g.scalingOrder ≤ Q.g.scalingOrder ∧
    Q.g.nM ≤ P0.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P0.g.nA : ℤ) - P0.g.nW) ∧
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ ℓe : Fin 2 → Idx d L W,
      ∫ ω, P0.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, BAComb.val (fo ++ fe) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- the lists per start term of `baLvl1LemmaSize_holds`, chosen by `lvl1_choose_list` -/
private theorem BAEngine_lists (c : ℝ) (hc : 0 < c) (p K0 d : ℕ) (D : ℝ) : ∃ fo fe : BAPGraph (Fin 2) → List (BAPGraph (Fin 2)),
    ∀ P0 ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition, BAEngine_Spec c K0 d D P0 (fo P0) (fe P0) :=
  lvl1_choose_list (BAEngine_Spec c K0 d D) ((BAGraph.ofLGraph (fxyPowGraph p)).partition)
    (fun P0 hP0 => baLvl1LemmaSize_holds d c hc K0 D P0 (BAGraph.partition_normal _ P0 hP0))

/-- **The BA `lem:localregular`** (as `lw_localregularX`): one pair of data-free lists with `BALocRegConcl` and at least `p` black waved
edges in every graph.  The lists per start term are those of `baLvl1LemmaSize_holds` (`Graph/BALvl1C.lean`), chosen by `lvl1_choose_list`; then `baEngine_assemble`; the black
waved edges by `ba_nWS_ge` along the `BAReach` of the third conjunct and `baStart_nWS`.  The band's `∀ m ≠ 0` has no BA counterpart.  The
first hypothesis is the shape binder of `BALocReg6` (`Graph/BAStepS.lean`), verbatim. -/
theorem ba_localregularX : (∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN) →
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col) := by
  intro hX p c hc K0 d D
  obtain ⟨fo, fe, hfo⟩ := BAEngine_lists c hc p K0 d D
  have hconcl := baEngine_assemble hX p c K0 d D fo fe hfo
  refine ⟨_, _, hconcl, fun Q hQ => ?_⟩
  obtain ⟨P0, hP0, hreach, -⟩ := hconcl.2.2.1 Q hQ
  have h := ba_nWS_ge hreach
  rw [baStart_nWS p P0 hP0] at h
  exact h

/-! ## 5. A locally standard graph -/

section InstHelpers

/-- `baSplitSolid` never returns the empty list (every solid edge gives one or two choices) -/
private theorem BAEngine_baSplitSolid_ne {V : Type*} : ∀ l : List (SEdge V), baSplitSolid l ≠ []
  | [] => by simp [baSplitSolid]
  | e :: es => by
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ (BAEngine_baSplitSolid_ne es)
    intro h
    simp only [baSplitSolid, List.flatMap_eq_nil_iff] at h
    have := h r hr
    split_ifs at this

private theorem BAEngine_partition_ne_nil {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (T : BAGraph E I) :
    T.partition ≠ [] := by
  simp only [BAGraph.partition, BAGraph.splitG, List.map_map, ne_eq, List.map_eq_nil_iff]
  exact BAEngine_baSplitSolid_ne _

private theorem BAEngine_outsOf_ne_nil {E : Type} (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I'))
    (h : Ts ≠ []) : P.outsOf Ts ≠ [] := by
  obtain ⟨T, hT⟩ := List.exists_mem_of_ne_nil _ h
  simp only [BAPGraph.outsOf, ne_eq, List.flatMap_eq_nil_iff, not_forall]
  exact ⟨T, hT, by simpa using BAEngine_partition_ne_nil T⟩

/-- a frame step has at least one output -/
private theorem BAEngine_frame_ne_nil {E : Type} {P : BAPGraph E} {F : List (BAPGraph E)} (h : BAFrameStep P F) : F ≠ [] := by
  cases h with
  | weight p hp hh =>
    exact fun hF => BAEngine_outsOf_ne_nil P _ (by simp [BAGraph.lw2]) (List.append_eq_nil_iff.1 hF).1
  | within p hp hh =>
    simp only [BAPGraph.withinOuts]
    exact fun hF => BAEngine_outsOf_ne_nil P _ (List.cons_ne_nil _ _)
      (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 hF).1).1
  | edge p hp hh x hx hwf hv hint hbad =>
    exact BAEngine_outsOf_ne_nil P _ (by simp [BAGraph.lanlwTerms])
  | gg p hp q hq hh x hx hwf hint hnb =>
    exact fun hF => BAEngine_outsOf_ne_nil P _ (by simp [BAGraph.gg2]) (List.append_eq_nil_iff.1 hF).1
  | ggSplit p hp q j hj hh a a' hx hne hsame hwf hint hnb =>
    simp only [BAPGraph.splitOuts]
    exact fun hF => BAEngine_outsOf_ne_nil P _ (List.cons_ne_nil _ _)
      (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 hF).1).1).1

/-- a locally standard graph (`E = Fin 2`, `I = Fin 3`: blue `x → a`, red `y → a`, the atom `{b, c}` by an `M`-dot, five waved edges; as in `Graph/BAStepS.lean`) -/
def BAEngine_pL : BAGraph (Fin 2) (Fin 3) :=
  ⟨⟨[⟨true, true, .inl 0, .inr 0⟩, ⟨false, true, .inl 1, .inr 0⟩],
    [⟨false, true, .inl 0, .inr 1⟩, ⟨false, true, .inl 1, .inr 2⟩, ⟨false, true, .inr 0, .inr 1⟩, ⟨false, true, .inr 0, .inr 2⟩,
      ⟨false, true, .inl 0, .inl 1⟩], [], 1⟩, [], [⟨true, .inr 1, .inr 2⟩]⟩

/-- **A locally standard graph exists** (`BAGraph.LocStd` at `BAEngine_pL`, by `decide`): the hypothesis `BAGraph.LocStd`, which
`baEngine_assemble` carries inside a hypothesis (the outputs `fo P0` are locally standard), is satisfiable; the band counterpart is
`localReg2_inst_Q_locStd` (`Graph/LocalRegular2.lean`). -/
theorem BAEngine_pL_locStd : BAEngine_pL.LocStd := by decide

end InstHelpers

end RBM.Graph

end
