/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BASim3
import RBM3D.Graph.BASymm2

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
# BA-L L3a3 (T2440): the BA local step, packing and the step identity

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-409` (`lanlw`, `lem_lweight`, `GGGamma`, `lvl1 lemma`).  Design:
`docs/reports/T2395-design.md` §6 (row L3a3 `BALvl1A`), probe `t/T2395:RBM3D/Probe/T2395Pins.lean:150-209, 252-257, 274-279`.  The BA twin of
`Graph/LWLvl1.lean` §9-§11 (`:3077-3613`).  A BA step `BALocStep` runs one of R1's five frame steps `BAFrameStep` at `P.twist c t` and twists
every output back (probe 207); one step is an identity of expectations at the BA law (`BAlvl1StepIdentity`, probe 254), from the merged frame
identities (`lanlw_val`, `baExpFrameE_holds`), the BA partition (`BAGraph.val_eq_partition`) and the twist transport of L3a2 (`baTwistIntegral_gen`).

## Contents (namespace `RBM.Graph`; private prefix `BALvl1A_`)

1. **Vocabulary** (probe, verbatim): `BALocStep`, `BAReach` (with `BALvl1A_reach_refl`, which the axiom audit's premise scan needs); the statements `BAtwistComb`, `BAframeStepIdentity`, `BAlvl1StepIdentity`.
2. **Packing** (pathwise, no integrability): `BALvl1A_pack` (`BAComb.val (P.outsOf Ts) D ℓe = baSum Ts D ℓ'` when `ℓe = ℓ' ∘ P.ext`),
   `BALvl1A_pack_zero` (the non-factoring case: both sides `0`), `BALvl1A_comb_append`.
3. **Target 3**: `baTwistComb_holds` (the twist of a list of packed graphs in expectation).
4. **Integrability** (copies of `BAExpandId:422-467` under the stem): the value of a graph at `BAlwData` is integrable over `PF d L W 0`.
5. **The two macro identities**: `BALvl1A_macroA` (`within`), `BALvl1A_macroB` (`ggSplit`).
6. **Target 4**: `baFrameStepIdentity_holds` (the five kinds of `BAFrameStep`).
7. **Target 5**: `baLvl1StepIdentity_holds`.
8. Compiled instances (`BALvl1AInst`, `d = 3`, `L = 4`, `W = 2`, `flowP_data`).

`BASelf` and `0 ≤ t < 1` are the only hypotheses on the data (C1): no `M a a = m`, no `M a b = 0` (T2395 F5), no smallness of `g₀`.  Not here:
`BAMatchTw` and its bridges (L3b4'), `BAstepMono`, `BAlvl1StepGood` (L3a4), the existence of a step, the measure and `BAlvl1Lemma` (L3a5); the twins of the
band's `×`-dot zeros (`lvl1_val_zero_of_xself`, `lvl1_oe1xT1_zero`, `lvl1_oe2xR1_zero`, `lvl1_weight0/edge0/gg0_identity`, `LWLvl1:3373-3589`), which need
`hM`, `hM0` (false at BA).
-/

open private BAWeightOp_val_tame from RBM3D.Graph.BAWeightOp
open private BAExpandW_integrable_PF from RBM3D.Graph.BAExpandW

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. Vocabulary (the probe, verbatim) -/

section Vocab

variable {E : Type}

/-- **`BALocStep`** (the band's `LocStep`, `LWLvl1.lean:3260`): a frame step at the twisted graph, every output twisted back (L3a1, L3a2). -/
def BALocStep {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)) : Prop :=
  ∃ (c t : Bool) (F : List (BAPGraph E)), BAFrameStep (P.twist c t) F ∧ outs = F.map (BAPGraph.twist c t)

/-- reachability by the strategy below the cutoff `K` (`Lvl1Reach`, `LWLvl1.lean:3277`) -/
inductive BAReach (K : ℤ) : BAPGraph E → BAPGraph E → Prop
  | refl (P : BAPGraph E) : BAReach K P P
  | step (P Q R : BAPGraph E) (L : List (BAPGraph E)) : BAReach K P Q → Q.g.scalingOrder < K → ¬ Q.g.LocStd → BALocStep Q L → R ∈ L → BAReach K P R

/-- reflexivity of `BAReach` as a theorem (the constructor `BAReach.refl`): the axiom audit's scan of premises (`Test/Axioms.lean:391-445`) counts a theorem concluding `BAReach` as a proof of it -/
theorem BALvl1A_reach_refl (K : ℤ) (P : BAPGraph E) : BAReach K P P := BAReach.refl P

end Vocab

/-- **Target 3 (`BAtwistComb d`)**: the twist of a list of packed graphs in expectation at the BA law (no `BASelf`, no integrability). -/
def BAtwistComb (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (g0 Em t : ℝ) (m : ℂ) {E : Type} (c t' : Bool) (Ls : List (BAPGraph E)) (ℓe : E → Idx d L W),
    ∫ ω, BAComb.val (Ls.map (BAPGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      (if c then (star : ℂ → ℂ) else id) (∫ ω, BAComb.val Ls (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- **Target 4 (`BAframeStepIdentity d`)**: one frame step (five kinds) is an identity of expectations at the BA law; no normality. -/
def BAframeStepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (F : List (BAPGraph E)), BAFrameStep P F → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val F (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- **Target 5 (`BAlvl1StepIdentity d`)**: one step is an identity of expectations at the BA law (the BA `lvl1_step_identity`, `LWLvl1.lean:3590`; probe 254-257).
The band's hypotheses `M a a = m`, `M a b = 0` fail at BA. -/
def BAlvl1StepIdentity (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {E : Type} (P : BAPGraph E) (outs : List (BAPGraph E)), BALocStep P outs → P.g.Normal → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val outs (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-! ## 2. Packing (pathwise; `LWLvl1:3095-3133, 3252, 3439-3450`, `BAExpandId:489-512`) -/

section Pack

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type}

/-- the value of a packed graph at labels that factor through the external map -/
theorem BALvl1A_val_of_factor (P : BAPGraph E) (D : BALData ι) {ℓe : E → ι} {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) :
    P.val D ℓe = P.g.val D ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [BAPGraph.val, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

/-- the value of a packed graph at labels that do not factor through the external map is `0` -/
theorem BALvl1A_val_of_not (P : BAPGraph E) (D : BALData ι) {ℓe : E → ι} (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) :
    P.val D ℓe = 0 := by
  classical
  simp only [BAPGraph.val, h, ↓reduceDIte]

/-- a child of `P` (a packed graph over the external vertices of `P`), read through `P.ext` -/
def BALvl1A_pcomp (P : BAPGraph E) (Q : BAPGraph P.E') : BAPGraph E :=
  { E' := Q.E', I' := Q.I', ext := Q.ext ∘ P.ext, ext_surj := Q.ext_surj.comp P.ext_surj, g := Q.g }

/-- `pcomp` reads the child through the external map of the parent: the values agree on labels that factor. -/
theorem BALvl1A_pcomp_val (P : BAPGraph E) (Q : BAPGraph P.E') (D : BALData ι) {ℓe : E → ι} {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) :
    (BALvl1A_pcomp P Q).val D ℓe = Q.val D ℓ' := by
  by_cases h : ∃ ℓ'' : Q.E' → ι, ℓ' = ℓ'' ∘ Q.ext
  · obtain ⟨ℓ'', hℓ''⟩ := h
    have h2 : ℓe = ℓ'' ∘ (BALvl1A_pcomp P Q).ext := by
      rw [hℓ, hℓ'']; rfl
    rw [BALvl1A_val_of_factor _ D h2, BALvl1A_val_of_factor Q D hℓ'']
    rfl
  · rw [BALvl1A_val_of_not Q D h, BALvl1A_val_of_not]
    rintro ⟨ℓ3, hℓ3⟩
    apply h
    refine ⟨ℓ3, ?_⟩
    apply P.ext_surj.injective_comp_right
    exact hℓ.symm.trans hℓ3

/-- if the labels do not factor through `P.ext`, every child read through `P.ext` has value `0` -/
theorem BALvl1A_pcomp_val_zero (P : BAPGraph E) (Q : BAPGraph P.E') (D : BALData ι) {ℓe : E → ι}
    (hf : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : (BALvl1A_pcomp P Q).val D ℓe = 0 := by
  apply BALvl1A_val_of_not
  rintro ⟨ℓ3, hℓ3⟩
  exact hf ⟨ℓ3 ∘ Q.ext, hℓ3⟩

/-- the outputs of `outsOf` are the children of the partitions of the terms -/
theorem BALvl1A_outsOf_eq (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) :
    P.outsOf Ts = Ts.flatMap fun T => T.partition.map (BALvl1A_pcomp P) := rfl

/-- `BAComb.val` of an append -/
theorem BALvl1A_comb_append (A B : List (BAPGraph E)) (D : BALData ι) (ℓe : E → ι) :
    BAComb.val (A ++ B) D ℓe = BAComb.val A D ℓe + BAComb.val B D ℓe := by
  simp [BAComb.val, List.map_append, List.sum_append]

private theorem BALvl1A_sum_flatMap {α β : Type*} [AddCommMonoid β] (a : List α) (g : α → List β) :
    (a.flatMap g).sum = (a.map fun x => (g x).sum).sum := by
  induction a with
  | nil => simp
  | cons x a ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- **Packing (target 2)**: the value of the packed partitions of a list of terms `Ts` at labels `ℓe = ℓ' ∘ P.ext` is the value of the list at `ℓ'`
(`lvl1_pack_identity`, `LWLvl1:3450`, pathwise; from `BAGraph.val_eq_partition`, no data hypothesis, no integrability). -/
theorem BALvl1A_pack (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) (D : BALData ι) {ℓe : E → ι}
    {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) : BAComb.val (P.outsOf Ts) D ℓe = baSum Ts D ℓ' := by
  rw [BALvl1A_outsOf_eq]
  unfold BAComb.val baSum
  rw [List.map_flatMap, BALvl1A_sum_flatMap]
  refine congrArg List.sum (List.map_congr_left fun T _ => ?_)
  rw [List.map_map]
  have h1 := T.val_eq_partition D ℓ'
  unfold BAComb.val at h1
  refine Eq.trans (congrArg List.sum (List.map_congr_left fun Q _ => ?_)) h1.symm
  exact BALvl1A_pcomp_val P Q D hℓ

/-- **Packing, the non-factoring case**: if `ℓe` does not factor through `P.ext`, the packed partitions have value `0`, and so has `P` itself. -/
theorem BALvl1A_pack_zero (P : BAPGraph E) {I' : Type} [Fintype I'] [DecidableEq I'] (Ts : List (BAGraph P.E' I')) (D : BALData ι) {ℓe : E → ι}
    (hf : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : BAComb.val (P.outsOf Ts) D ℓe = 0 ∧ P.val D ℓe = 0 := by
  refine ⟨?_, BALvl1A_val_of_not P D hf⟩
  rw [BALvl1A_outsOf_eq]
  unfold BAComb.val
  rw [List.map_flatMap, BALvl1A_sum_flatMap]
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨T, _, rfl⟩ := List.mem_map.1 ha
  rw [List.map_map]
  refine List.sum_eq_zero fun b hb => ?_
  obtain ⟨Q, _, rfl⟩ := List.mem_map.1 hb
  exact BALvl1A_pcomp_val_zero P Q D hf

end Pack

/-! ## 3. Target 3: the twist of a list of packed graphs -/

section Twist

variable {ι : Type} [Fintype ι] [DecidableEq ι] {E : Type}

/-- the value of the twist of a packed graph: the conjugate (if `c`) of the value at the transposed (if `t`) data (`BAGraph.BASymm1_val_twist`, pathwise) -/
theorem BALvl1A_pval_twist (D : BALData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool)
    (Q : BAPGraph E) (ℓe : E → ι) : (Q.twist c t).val D ℓe = lwSymmCj c (Q.val (BASymm1_dataTr D t) ℓe) := by
  by_cases h : ∃ ℓ' : Q.E' → ι, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    have h1 : (Q.twist c t).val D ℓe = (Q.g.twist c t).val D ℓ' := BALvl1A_val_of_factor (Q.twist c t) D hℓ
    rw [h1, BALvl1A_val_of_factor Q _ hℓ]
    exact BAGraph.BASymm1_val_twist D hS hP c t Q.g ℓ'
  · have h2 : ¬ ∃ ℓ' : (Q.twist c t).E' → ι, ℓe = ℓ' ∘ (Q.twist c t).ext := h
    rw [BALvl1A_val_of_not _ D h2, BALvl1A_val_of_not Q _ h, map_zero]

/-- the value of the twist of a list of packed graphs, pathwise -/
theorem BALvl1A_comb_twist (D : BALData ι) (hS : ∀ i j, star (D.S i j) = D.S i j) (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool)
    (Ls : List (BAPGraph E)) (ℓe : E → ι) :
    BAComb.val (Ls.map (BAPGraph.twist c t)) D ℓe = lwSymmCj c (BAComb.val Ls (BASymm1_dataTr D t) ℓe) := by
  unfold BAComb.val
  rw [lwSymm_cj_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left fun Q _ => BALvl1A_pval_twist D hS hP c t Q ℓe

end Twist

/-- **`BAtwistComb d` holds**, for every `d` (target 3): pathwise `BALvl1A_comb_twist` at the real BA data (`BASymm1_data_real`), then `baTwistIntegral_gen`
(`BASymm2:104`) at the functional `F D = BAComb.val Ls D ℓe`.  No `BASelf`, no integrability. -/
theorem baTwistComb_holds (d : ℕ) : BAtwistComb d := by
  intro L W _ _ g0 Em t m E c t' Ls ℓe
  have h1 : ∀ ω, BAComb.val (Ls.map (BAPGraph.twist c t')) (BAlwData d L W g0 Em t m ω) ℓe =
      lwSymmCj c (BAComb.val Ls (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') ℓe) := fun ω =>
    BALvl1A_comb_twist _ (BASymm1_data_real d L W g0 Em t m ω).1 (BASymm1_data_real d L W g0 Em t m ω).2 c t' Ls ℓe
  simp only [h1]
  rw [baTwistIntegral_gen d L W g0 Em t m c t' (fun D => BAComb.val Ls D ℓe)]
  cases c <;> simp [lwSymmCj]

/-! ## 4. Integrability (copies of `BAExpandId:422-467` under the stem) -/

section Integrable

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- At `t = 0` the data does not depend on the sample (`Ǧ = 0`, `G = M`; `BAExpand_Gc_zero`). -/
private theorem BALvl1A_data_zero (g0 E : ℝ) (m : ℂ) (ω ω' : Ω d L W) :
    BAlwData d L W g0 E 0 m ω = BAlwData d L W g0 E 0 m ω' := by
  have h : ∀ ω : Ω d L W, (Matrix.of fun x y => BAlwG d L W g0 E 0 m ω x y : Matrix (Idx d L W) (Idx d L W) ℂ) =
      BAlwM d L W g0 E m := by
    intro ω
    ext x y
    have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 E m ω x y
    simpa [BAlwGc, sub_eq_zero] using this
  simp only [BAlwData, h]

/-- Every graph value is integrable over `PF d L W 0` at the data `BAlwData` (`0 < t`: a tame function of the sequence space, `BAWeightOp_val_tame`
through `BAExpandW_integrable_PF`; `t = 0`: constant). -/
theorem BALvl1A_integrable_val (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (T : BAGraph Ex Ix)
    (ℓ : Ex → Idx d L W) :
    Integrable (fun ω => T.val (BAlwData d L W g0 E t m ω) ℓ) (PF d L W 0) := by
  rcases ht0.eq_or_lt with rfl | ht
  · have h : (fun ω : Ω d L W => T.val (BAlwData d L W g0 E 0 m ω) ℓ) =
        fun _ => T.val (BAlwData d L W g0 E 0 m 0) ℓ :=
      funext fun ω => by rw [BALvl1A_data_zero g0 E m ω 0]
    rw [h]
    exact integrable_const _
  · have hm : 0 < m.im := hSelf.1
    have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    exact BAExpandW_integrable_PF hL (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓ) fun ω' => rfl

/-- The value of a list of terms is integrable. -/
theorem BALvl1A_integrable_baSum (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m) (ht0 : 0 ≤ t)
    (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Ts : List (BAGraph Ex Ix))
    (ℓ : Ex → Idx d L W) :
    Integrable (fun ω => baSum Ts (BAlwData d L W g0 E t m ω) ℓ) (PF d L W 0) := by
  unfold baSum
  exact owx_integrable_list_sum Ts (fun T ω => T.val (BAlwData d L W g0 E t m ω) ℓ)
    fun T _ => BALvl1A_integrable_val hL g0 E t m hSelf ht0 ht1 T ℓ

end Integrable

/-! ## 5. The two macro identities -/

section Macro

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- the last pair of `lwSplit` -/
private theorem BALvl1A_lwSplit_last {κ : Type*} (l : List κ) (x : κ) : (x, l) ∈ lwSplit (l ++ [x]) := by
  induction l with
  | nil => simp [lwSplit]
  | cons a l ih =>
    simp only [List.cons_append, lwSplit, List.mem_cons, List.mem_map]
    exact Or.inr ⟨(x, l), ih, rfl⟩

/-- a sum over a list is the term at a position plus the sum over the list without it -/
private theorem BALvl1A_sum_eraseIdx {κ : Type*} (f : κ → ℂ) : ∀ (l : List κ) (j : ℕ) (q : κ), l[j]? = some q →
    (l.map f).sum = f q + ((l.eraseIdx j).map f).sum
  | [], j, q, h => by simp at h
  | a :: l, 0, q, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    simp
  | a :: l, j + 1, q, h => by
    simp only [List.getElem?_cons_succ] at h
    have ih := BALvl1A_sum_eraseIdx f l j q h
    simp only [List.map_cons, List.sum_cons, List.eraseIdx_cons_succ, ih]
    ring

section MacroA

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Macro (a), pathwise** (`BAPGraph.withinOuts`): the sum of the values of `lanlwTerms` is the value of the list of the first term and the `lanlwD` terms,
plus the value of the transfer graph `tr` (`G_{αy} = Ǧ_{αy} + M_{αy}` in the first term of `lanlw`). -/
private theorem BALvl1A_macroA_val (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι) (ℓ' : E → ι) :
    baSum (BAGraph.lanlwTerms Γ p) D ℓ' =
      baSum (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)) D ℓ' +
        (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).val D ℓ' := by
  have hT1 : (BAGraph.lanlwT1 Γ p).val D ℓ' =
      (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0)]).val D ℓ' +
        (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).val D ℓ' := by
    unfold BAGraph.val
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    change (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0)]).term D _ = _
    rw [BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val, BAMEdge.val, bpS, bpW, bpM, bpv]
    simp
    ring
  simp only [baSum, BAGraph.lanlwTerms, List.map_cons, List.sum_cons, hT1]
  ring

/-- **Macro (a), graph level** (`BAPGraph.withinOuts`, `lem_lweight`'s transfer at `lanlw`'s first term): `lanlw_val` at `p`, the first term split pathwise
(`BALvl1A_macroA_val`), `baExpFrameE_holds`.1 at the transfer graph's loop. -/
private theorem BALvl1A_macroA_graph (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true) (ℓ' : E → Idx d L W) :
    ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓ' ∂(PF d L W 0) =
      ∫ ω, (baSum (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)) (BAlwData d L W g0 Em t m ω) ℓ' +
        baSum ((BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).lw2
            (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2)))) (BAlwData d L W g0 Em t m ω) ℓ' +
        baSum ((BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]).lw4
            (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2)))) (BAlwData d L W g0 Em t m ω) ℓ') ∂(PF d L W 0) := by
  set tr : BAGraph E (I ⊕ Fin 2) := BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)] with htr
  set A : List (BAGraph E (I ⊕ Fin 2)) := BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)]
    [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p) with hA
  set pp : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) := (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))) with hpp
  have hmem : pp ∈ lwSplit tr.solid := BALvl1A_lwSplit_last _ _
  have h1 := lanlw_val d L W hL g0 Em t m hSelf ht0 ht1 Γ p hp hσ hc ℓ'
  have h2 := (baExpFrameE_holds d L W hL g0 Em t m hSelf ht0 ht1 tr ℓ').1 pp hmem rfl rfl rfl
  have h3 : ∀ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 Em t m ω) ℓ').sum =
      baSum A (BAlwData d L W g0 Em t m ω) ℓ' + tr.val (BAlwData d L W g0 Em t m ω) ℓ' := fun ω =>
    BALvl1A_macroA_val Γ p _ ℓ'
  have iA := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 A ℓ'
  have itr := BALvl1A_integrable_val hL g0 Em t m hSelf ht0 ht1 tr ℓ'
  have i2 := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 (tr.lw2 pp) ℓ'
  have i4 := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 (tr.lw4 pp) ℓ'
  have key := integral_add iA (i2.add i4)
  rw [h1]
  simp_rw [h3]
  rw [integral_add iA itr, h2]
  refine Eq.trans key.symm (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
  simp only [Pi.add_apply]
  ring

/-- **Macro (a), the identity of expectations at a packed graph** (`BAFrameStep.within`; `BAPGraph.withinOuts`): `lanlw_val` at `p`, the first term split
pathwise, `baExpFrameE_holds`.1 at the transfer graph's loop, then the packing of the three lists.  Hypotheses: `BASelf` and `0 ≤ t < 1` (the
integrability of the four sums), `p.1` blue and circled. -/
theorem BALvl1A_macroA (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) {E : Type}
    (P : BAPGraph E) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid) (hσ : p.1.σ = true)
    (hc : p.1.circ = true) (ℓe : E → Idx d L W) :
    ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, BAComb.val (P.withinOuts p) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  by_cases h : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    have e1 : ∀ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe = P.g.val (BAlwData d L W g0 Em t m ω) ℓ' :=
      fun ω => BALvl1A_val_of_factor P _ hℓ
    simp_rw [e1]
    refine (BALvl1A_macroA_graph hL g0 Em t m hSelf ht0 ht1 P.g p hp hσ hc ℓ').trans
      (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
    simp only [BAPGraph.withinOuts, BALvl1A_comb_append, BALvl1A_pack P _ _ hℓ]
  · have e1 : ∀ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe = 0 := fun ω => BALvl1A_val_of_not P _ h
    have e2 : ∀ ω, BAComb.val (P.withinOuts p) (BAlwData d L W g0 Em t m ω) ℓe = 0 := fun ω => by
      simp only [BAPGraph.withinOuts, BALvl1A_comb_append, (BALvl1A_pack_zero P _ _ h).1, add_zero]
    simp_rw [e1, e2]

end MacroA

section MacroB

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- the graph `dq` of `BAPGraph.splitOuts`: `Γ` with the solid edges `q.2` and the new edges `s`, the waved edge `S_{αβ}` and the `M`-dotted edges `M_{aα}`, `md` -/
def BALvl1A_dq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 s [bpW false (bpv 0) (bpv 1)] (bpM (owxEmb 2 p.1.src) (bpv 0) :: md)

/-- **Macro (b), pathwise** (`BAPGraph.splitOuts`): the derivative term `lanlwD Γ p q` at the blue edge `q.1` is the sum of the four graphs `dq` and the transfer
graph `tr` (`G_{αa'} = Ǧ_{αa'} + M_{αa'}`, then `G_{y'β} G_{βy} = ǦǦ + ǦM + MǦ + MM`). -/
private theorem BALvl1A_macroB_val (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hσ : q.1.σ = true) (D : BALData ι) (ℓ' : E → ι) :
    (BAGraph.lanlwD Γ p q).val D ℓ' =
      (BALvl1A_dq Γ p q [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)] []).val D ℓ' +
      (BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)]).val D ℓ' +
      (BALvl1A_dq Γ p q [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)]).val D ℓ' +
      (BALvl1A_dq Γ p q [] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]).val D ℓ' +
      (BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst)]).val D ℓ' := by
  unfold BAGraph.val
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [BAGraph.lanlwD, BAExpandW_lanlwExt_term]
  unfold BALvl1A_dq
  rw [BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term]
  simp only [owxDE, SEdge.map, hσ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val, BAMEdge.val, bpS,
    bpW, bpM, bpv]
  simp
  ring

/-- **Macro (b), graph level** (`BAPGraph.splitOuts`, `GGGamma`'s transfer at `lanlw`'s `j`-th derivative term): `lanlw_val` at `p`, the `j`-th derivative term split
pathwise (`BALvl1A_macroB_val`), `baExpFrameE_holds`.2 at the transfer graph's pair `(Ǧ_{βy}, R ++ [Ǧ_{y'β}])`, `(Ǧ_{y'β}, R)`. -/
private theorem BALvl1A_macroB_graph (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (ℓ' : E → Idx d L W) :
    ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓ' ∂(PF d L W 0) =
      ∫ ω, (baSum (BAGraph.lanlwT1 Γ p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD Γ p)) (BAlwData d L W g0 Em t m ω) ℓ' +
        baSum [BALvl1A_dq Γ p q [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)] [],
          BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
          BALvl1A_dq Γ p q [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
          BALvl1A_dq Γ p q [] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]]
          (BAlwData d L W g0 Em t m ω) ℓ' +
        baSum ((BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst)]).gg2
          (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
          (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2)))) (BAlwData d L W g0 Em t m ω) ℓ' +
        baSum ((BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst)]).gg4
          (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])
          (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2)))) (BAlwData d L W g0 Em t m ω) ℓ') ∂(PF d L W 0) := by
  set tr : BAGraph E (I ⊕ Fin 2) := BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)]
    [bpM (bpv 0) (owxEmb 2 q.1.dst)] with htr
  set L1 : List (BAGraph E (I ⊕ Fin 2)) := BAGraph.lanlwT1 Γ p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD Γ p) with hL1
  set Q4 : List (BAGraph E (I ⊕ Fin 2)) := [BALvl1A_dq Γ p q [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)] [],
          BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
          BALvl1A_dq Γ p q [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
          BALvl1A_dq Γ p q [] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]] with hQ4
  set R : List (SEdge (E ⊕ (I ⊕ Fin 2))) := q.2.map (SEdge.map (owxEmb 2)) with hR
  set pp : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
    (bpS true (bpv 1) (owxEmb 2 p.1.dst), R ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) with hpp
  set qq : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) := (bpS true (owxEmb 2 q.1.src) (bpv 1), R) with hqq
  have hmem : pp ∈ lwSplit tr.solid := by
    have := BALvl1A_lwSplit_last (R ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) (bpS true (bpv 1) (owxEmb 2 p.1.dst))
    rw [List.append_assoc] at this
    exact this
  have hmem2 : qq ∈ lwSplit pp.2 := BALvl1A_lwSplit_last R _
  have h1 := lanlw_val d L W hL g0 Em t m hSelf ht0 ht1 Γ p hp h.1 h.2.1 ℓ'
  have h2 := (baExpFrameE_holds d L W hL g0 Em t m hSelf ht0 ht1 tr ℓ').2 pp hmem qq hmem2 rfl rfl rfl rfl rfl
  have h3 : ∀ ω, ((BAGraph.lanlwTerms Γ p).map fun Δ => Δ.val (BAlwData d L W g0 Em t m ω) ℓ').sum =
      baSum L1 (BAlwData d L W g0 Em t m ω) ℓ' + baSum Q4 (BAlwData d L W g0 Em t m ω) ℓ' + tr.val (BAlwData d L W g0 Em t m ω) ℓ' := fun ω => by
    have e := BALvl1A_sum_eraseIdx (fun q' => (BAGraph.lanlwD Γ p q').val (BAlwData d L W g0 Em t m ω) ℓ') (lwSplit p.2) j q hj
    have e2 := BALvl1A_macroB_val Γ p q h.2.2.1 (BAlwData d L W g0 Em t m ω) ℓ'
    simp only [BAGraph.lanlwTerms, baSum, hL1, hQ4, htr, List.map_cons, List.sum_cons, List.map_map, Function.comp_def, List.map_nil, List.sum_nil] at e ⊢
    rw [e, e2]
    ring
  have iL := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 L1 ℓ'
  have iQ := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 Q4 ℓ'
  have itr := BALvl1A_integrable_val hL g0 Em t m hSelf ht0 ht1 tr ℓ'
  have i2 := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 (tr.gg2 pp qq) ℓ'
  have i4 := BALvl1A_integrable_baSum hL g0 Em t m hSelf ht0 ht1 (tr.gg4 pp qq) ℓ'
  have key := integral_add (iL.add iQ) (i2.add i4)
  rw [h1]
  simp_rw [h3]
  refine (integral_add (iL.add iQ) itr).trans ?_
  rw [h2]
  refine Eq.trans key.symm (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
  simp only [Pi.add_apply]
  ring

/-- **Macro (b), the identity of expectations at a packed graph** (`BAFrameStep.ggSplit`; `BAPGraph.splitOuts`): `lanlw_val` at `p`, the `j`-th derivative term
split pathwise, `baExpFrameE_holds`.2 at the transfer graph's pair, then the packing of the four lists.  Hypotheses: `BASelf` and `0 ≤ t < 1`, `p.1` and
`q.1` blue and circled, `q` the `j`-th pair of `lwSplit p.2`. -/
theorem BALvl1A_macroB (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1) {E : Type}
    (P : BAPGraph E) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (ℓe : E → Idx d L W) :
    ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, BAComb.val (P.splitOuts p q j) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    have e1 : ∀ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe = P.g.val (BAlwData d L W g0 Em t m ω) ℓ' :=
      fun ω => BALvl1A_val_of_factor P _ hℓ
    simp_rw [e1]
    refine (BALvl1A_macroB_graph hL g0 Em t m hSelf ht0 ht1 P.g p q hp j hj h ℓ').trans
      (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
    simp only [BAPGraph.splitOuts, BALvl1A_comb_append, BALvl1A_pack P _ _ hℓ]
    rfl
  · have e1 : ∀ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe = 0 := fun ω => BALvl1A_val_of_not P _ hf
    have e2 : ∀ ω, BAComb.val (P.splitOuts p q j) (BAlwData d L W g0 Em t m ω) ℓe = 0 := fun ω => by
      simp only [BAPGraph.splitOuts, BALvl1A_comb_append, (BALvl1A_pack_zero P _ _ hf).1, add_zero]
    simp_rw [e1, e2]

end MacroB

end Macro

/-! ## 6. Target 4: one frame step is an identity of expectations -/

/-- **`BAframeStepIdentity d` holds**, for every `d` (target 4), one case per constructor of `BAFrameStep`: `weight` (`baExpFrameE_holds`.1), `edge` (`lanlw_val`), `gg`
(`baExpFrameE_holds`.2), each with the packing `BALvl1A_pack`; `within` (`BALvl1A_macroA`); `ggSplit` (`BALvl1A_macroB`).  `BASelf` and `0 ≤ t < 1` only; no
normality of `P`, no `M a a = m`, no `M a b = 0`. -/
theorem baFrameStepIdentity_holds (d : ℕ) : BAframeStepIdentity d := by
  intro L W _ _ hL g0 Em t m hSelf ht0 ht1 E P F hF
  cases hF with
  | weight p hp h =>
    intro ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp_rw [BALvl1A_val_of_factor P _ hℓ, BALvl1A_comb_append, BALvl1A_pack P _ _ hℓ]
      exact (baExpFrameE_holds d L W hL g0 Em t m hSelf ht0 ht1 P.g ℓ').1 p hp h.1 h.2.1 h.2.2
    · simp_rw [BALvl1A_val_of_not P _ hf, BALvl1A_comb_append, (BALvl1A_pack_zero P _ _ hf).1, add_zero]
  | within p hp h => exact fun ℓe => BALvl1A_macroA hL g0 Em t m hSelf ht0 ht1 P p hp h.1 h.2.1 ℓe
  | edge p hp h x hx hwf hv hint hbad =>
    intro ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp_rw [BALvl1A_val_of_factor P _ hℓ, BALvl1A_pack P _ _ hℓ]
      exact lanlw_val d L W hL g0 Em t m hSelf ht0 ht1 P.g p hp h.1 h.2 ℓ'
    · simp_rw [BALvl1A_val_of_not P _ hf, (BALvl1A_pack_zero P _ _ hf).1]
  | gg p hp q hq h x hx hwf hint hnb =>
    intro ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp_rw [BALvl1A_val_of_factor P _ hℓ, BALvl1A_comb_append, BALvl1A_pack P _ _ hℓ]
      exact (baExpFrameE_holds d L W hL g0 Em t m hSelf ht0 ht1 P.g ℓ').2 p hp q hq h.1 h.2.1 h.2.2.1 h.2.2.2 (hx.1.trans hx.2.symm)
    · simp_rw [BALvl1A_val_of_not P _ hf, BALvl1A_comb_append, (BALvl1A_pack_zero P _ _ hf).1, add_zero]
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    exact fun ℓe => BALvl1A_macroB hL g0 Em t m hSelf ht0 ht1 P p q hp j hj h ℓe

/-! ## 7. Target 5: one step is an identity of expectations -/

/-- the twist of a packed graph is an involution -/
theorem BALvl1A_twist_invol {E : Type} (c t : Bool) (P : BAPGraph E) : (P.twist c t).twist c t = P := by
  cases P
  simp only [BAPGraph.twist, BAGraph.twist_invol]

/-- **`BAlvl1StepIdentity d` holds**, for every `d` (target 5; twin of `lvl1_step_identity`, `LWLvl1:3590`, without `hM`, `hM0`): `E P = E (P.twist c t).twist` is the
conjugate of `E (P.twist c t)` (target 3 at `[P.twist c t]` and the involution), which is the conjugate of `E Σ F` (target 4 at `P.twist c t`), which is
`E Σ (F.map twist)` (target 3 at `F`).  `P.g.Normal` is not used. -/
theorem baLvl1StepIdentity_holds (d : ℕ) : BAlvl1StepIdentity d := by
  intro L W _ _ hL g0 Em t m hSelf ht0 ht1 E P outs hst hN ℓe
  obtain ⟨c, t', F, hF, rfl⟩ := hst
  have h1 := baTwistComb_holds d L W g0 Em t m c t' [P.twist c t'] ℓe
  have h2 := baFrameStepIdentity_holds d L W hL g0 Em t m hSelf ht0 ht1 (P.twist c t') F hF ℓe
  have h3 := baTwistComb_holds d L W g0 Em t m c t' F ℓe
  simp only [List.map_cons, List.map_nil, BALvl1A_twist_invol, BAComb.val, List.sum_cons, List.sum_nil, add_zero] at h1
  rw [h3, h1, h2]

/-! ## 8. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point `flowP`; `BASelf` and `0 < t₀ < 1` are `flowP_data`) -/

namespace BALvl1AInst

open BASimInst

theorem hFB : BAFrameStep (baPG baPB) ((baPG baPB).withinOuts pB) :=
  BAFrameStep.within (baPG baPB) pB (List.mem_cons_self ..) (by decide)
theorem hFW : BAFrameStep (baPG baPW) ((baPG baPW).outsOf (baPW.lw2 pW) ++ (baPG baPW).outsOf (baPW.lw4 pW)) :=
  BAFrameStep.weight (baPG baPW) pW (List.mem_cons_self ..) (by decide)
/-- **Target 1 and target 5 at `P_B`** (`within`), `(c, t) = (true, true)`: the twist of `P_B` is a graph `P` with a `BALocStep` (the frame step at `P.twist true true = P_B`,
every output twisted back); `P.g` is normal. -/
theorem locStepB : BALocStep ((baPG baPB).twist true true) (((baPG baPB).withinOuts pB).map (BAPGraph.twist true true)) :=
  ⟨true, true, (baPG baPB).withinOuts pB, by rw [BALvl1A_twist_invol]; exact hFB, rfl⟩

end BALvl1AInst

end RBM.Graph

end
