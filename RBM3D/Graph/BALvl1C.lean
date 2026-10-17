/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALvl1B2

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
# BA-L L3a5 (T2446): a step exists, the measure, the induction along `BAReach`, the BA `lvl1 lemma`

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-409` (`lvl1 lemma`, `B:407-409`).  Design: `docs/reports/T2395-design.md` §6 (row L3a5
`BALvl1C`), §3 Steps 2, 4-6; probe `t/T2395:RBM3D/Probe/T2395Pins.lean:274-288`.  The BA twin of `Graph/LWLvl1.lean` §12-§14 (`:3614-3963`) and of
`lvl1_lemma_size` (`:4047-4071`).

## Contents (namespace `RBM.Graph`; private prefix `BALvl1C_`)

1. **Vocabulary** (probe, verbatim): `BAlvl1ExistsStep`, `BAlvl1Lemma`; and the paper form `BAlvl1LemmaSize`.
2. **Measure and induction** (target 3): `BALvl1Mu`, `BALvl1Lt`, `baLvl1Lt_wf`, `ba_lvl1_mu_lt`, `BAReach.trans`, `ba_lvl1_induction`.
3. **The twist transport** (new): `atEdges`, `atCharge` and the hypotheses of the five frame steps read at `P.twist c t`.
4. **Target 2** `baLvl1ExistsStep_holds`: the case table (weight, within, edge, gg, ggSplit).
5. **Target 4** `baLvl1Lemma_holds`: strong induction on the measure; the identity of expectations by `baLvl1StepIdentity_holds` and integrability.
6. **Target 5** `baLvl1LemmaSize_holds`: the paper form at the cutoff `lvl1Cutoff`.
7. Compiled instances (`BALvl1CInst`).

`BASelf` and `0 ≤ t < 1` are the only hypotheses on the data (C1).  No new `inductive`, no hypothesis beyond the pins.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. Vocabulary (the probe, verbatim, and the paper form) -/

/-- L3a5: a normal graph that is not locally standard (at the atom level) has a step (`lvl1_exists_step`, `LWLvl1.lean:3655`). -/
def BAlvl1ExistsStep : Prop := ∀ {E : Type} (P : BAPGraph E), P.g.Normal → ¬ P.g.LocStd → ∃ outs, BALocStep P outs

/-- **L3a5: the BA `lvl1 lemma`** (`B:407-409`; `lvl1_lemma`, `LWLvl1.lean:3907`): the lists `outs`, `errs` do not depend on the data. -/
def BAlvl1Lemma (d : ℕ) : Prop :=
  ∀ {E : Type} (K : ℤ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, BAReach K P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- **The BA `lvl1 lemma` in the paper's form** (`lvl1_lemma_size`, `LWLvl1.lean:4047`; design §3 Step 5): at the cutoff
`K = lvl1Cutoff c K0 d D P.g.counters` the errors have scaling size `≤ W^{-D}` in the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`. -/
def BAlvl1LemmaSize (d : ℕ) : Prop :=
  ∀ {E : Type} (c : ℝ), 0 < c → ∀ (K0 : ℕ) (D : ℝ) (P : BAPGraph E), P.g.Normal → ∃ outs errs : List (BAPGraph E),
    (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
    (∀ Q ∈ outs ++ errs, BAReach (lvl1Cutoff c K0 d D P.g.counters : ℤ) P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧
      Q.g.nM ≤ P.g.nM ∧ (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : E → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-! ## 2. Measure and induction (target 3; twin of `LWLvl1` §13, `:3755-3809`) -/

section Induction

variable {E : Type}

/-- **Target 3** (`Lvl1Reach.trans`, `LWLvl1:3755`): reachability by the strategy below the cutoff is transitive. -/
theorem BAReach.trans {K : ℤ} {P Q R : BAPGraph E} (h1 : BAReach K P Q) (h2 : BAReach K Q R) : BAReach K P R := by
  induction h2 with
  | refl => exact h1
  | step Q1 R1 L _ hlt hn hst hmem ih => exact BAReach.step P Q1 R1 L ih hlt hn hst hmem

/-- **The induction principle of the strategy** (`lvl1_induction`, `LWLvl1:3763`): a predicate that holds at `P` and passes from the input of every
`BALocStep` to each of its outputs holds at every graph reached from `P`. -/
theorem ba_lvl1_induction {K : ℤ} {P Q : BAPGraph E} (h : BAReach K P Q) (Pred : BAPGraph E → Prop) (h0 : Pred P)
    (hstep : ∀ (A : BAPGraph E) (L : List (BAPGraph E)), BALocStep A L → Pred A → ∀ B ∈ L, Pred B) : Pred Q := by
  induction h with
  | refl => exact h0
  | step Q1 R1 L _ _ _ hst hmem ih => exact hstep Q1 L hst ih R1 hmem

/-- **The termination measure of the BA `lvl1 lemma`** (K3): the order deficit `(K - ord)⁺`, the number of external atoms, the atom-level loops, the number
of solid edges, and the atom-level pairs, compared lexicographically (the band's `Lvl1Mu` has no `nExt`). -/
def BALvl1Mu (K : ℤ) (P : BAPGraph E) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  ((K - P.g.scalingOrder).toNat, P.g.nExt, P.g.nLoops, P.g.nS, P.g.nPairs)

/-- the lexicographic order on the measure -/
def BALvl1Lt (a b : ℕ × ℕ × ℕ × ℕ × ℕ) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·)))) a b

theorem baLvl1Lt_wf : WellFounded BALvl1Lt :=
  (wellFounded_lt (α := ℕ)).prod_lex ((wellFounded_lt (α := ℕ)).prod_lex ((wellFounded_lt (α := ℕ)).prod_lex
    ((wellFounded_lt (α := ℕ)).prod_lex (wellFounded_lt (α := ℕ)))))

/-- **The measure falls along a good step** (below the cutoff; `lvl1_mu_lt`, `LWLvl1:3795`). -/
theorem ba_lvl1_mu_lt {K : ℤ} {Γ Q : BAPGraph E} (hK : Γ.g.scalingOrder < K) (hg : BALvl1Good Γ.g Q.g) :
    BALvl1Lt (BALvl1Mu K Q) (BALvl1Mu K Γ) := by
  obtain ⟨-, -, -, -, h⟩ := hg
  unfold BALvl1Lt BALvl1Mu
  simp only [Prod.lex_def]
  rcases h with h | ⟨h1, h2⟩
  · left; omega
  · right
    refine ⟨by rw [h1], ?_⟩
    rcases h2 with h2 | ⟨h2, h3⟩
    · left; exact h2
    · right
      refine ⟨h2, ?_⟩
      rcases h3 with h3 | ⟨h3, h4⟩
      · left; exact h3
      · right
        refine ⟨h3, ?_⟩
        rcases h4 with h4 | ⟨h4, h5⟩
        · left; exact h4
        · right; exact ⟨h4, h5⟩

end Induction

/-! ## 3. The twist transport (new): `atEdges`, `atCharge` and the hypotheses of the frame steps at `P.twist c t` -/

section Transport

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BALvl1C_twist_solid (c t : Bool) (G : BAGraph E I) : (G.twist c t).solid = G.solid.map (lwSymmTwistS c t) :=
  lwSymmTwistG_solid c t G.toLGraph

/-- the test `atEdges` applies to an edge reads its two ends up to order -/
private theorem BALvl1C_bne_twist (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) (e : SEdge (E ⊕ I)) :
    (G.sameAtom v (lwSymmTwistS c t e).src != G.sameAtom v (lwSymmTwistS c t e).dst) = (G.sameAtom v e.src != G.sameAtom v e.dst) := by
  rcases BASymm1_twistS_ends c t e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    cases G.sameAtom v e.src <;> cases G.sameAtom v e.dst <;> rfl

/-- **The non-loop solid edges at the atom of `v` of a twist are the twists of those of the graph.** -/
theorem BALvl1C_atEdges_twist (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) :
    (G.twist c t).atEdges v = (G.atEdges v).map (lwSymmTwistS c t) := by
  unfold BAGraph.atEdges
  rw [BALvl1C_twist_solid, List.filter_map]
  congr 1
  refine List.filter_congr fun e _ => ?_
  simp only [Function.comp_apply, BAGraph.BASymm1_twist_sameAtom]
  exact BALvl1C_bne_twist c t G v e

private theorem BALvl1C_charge_term (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) (e : SEdge (E ⊕ I))
    (he : (G.sameAtom v e.src != G.sameAtom v e.dst) = true) :
    (if G.sameAtom v (lwSymmTwistS c t e).src = true then (if (lwSymmTwistS c t e).σ then (-1 : ℤ) else 1)
      else (if (lwSymmTwistS c t e).σ then 1 else -1)) =
      ((if c then -1 else 1) * (if t then -1 else 1) : ℤ) *
        (if G.sameAtom v e.src = true then (if e.σ then (-1 : ℤ) else 1) else (if e.σ then 1 else -1)) := by
  rw [lwSymmTwistS_eq]
  cases c <;> cases t <;> cases ha : G.sameAtom v e.src <;> cases hb : G.sameAtom v e.dst <;> cases hs : e.σ <;> simp_all

/-- **The charge of the atom of `v` of a twist is the charge of the graph up to the sign `(-1)^(c + t)`.** -/
theorem BALvl1C_atCharge_twist (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) :
    (G.twist c t).atCharge v = ((if c then -1 else 1) * (if t then -1 else 1) : ℤ) * G.atCharge v := by
  unfold BAGraph.atCharge
  rw [BALvl1C_atEdges_twist, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e he => ?_
  have he' : (G.sameAtom v e.src != G.sameAtom v e.dst) = true := (List.mem_filter.1 he).2
  simp only [Function.comp_apply, BAGraph.BASymm1_twist_sameAtom]
  exact BALvl1C_charge_term c t G v e he'

theorem BALvl1C_atCharge_twist_eq_zero (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) :
    (G.twist c t).atCharge v = 0 ↔ G.atCharge v = 0 := by
  rw [BALvl1C_atCharge_twist]
  cases c <;> cases t <;> simp

theorem BALvl1C_atEdges_twist_length (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) :
    ((G.twist c t).atEdges v).length = (G.atEdges v).length := by
  rw [BALvl1C_atEdges_twist, List.length_map]

theorem BALvl1C_atEdges_twist_ne_nil (c t : Bool) (G : BAGraph E I) (v : E ⊕ I) :
    (G.twist c t).atEdges v ≠ [] ↔ G.atEdges v ≠ [] := by
  rw [BALvl1C_atEdges_twist]
  simp

/-- the `hbad` clause of `BAFrameStep.edge` at the twist -/
theorem BALvl1C_hbad_twist (c t : Bool) (G : BAGraph E I) (v : E ⊕ I)
    (h : G.atEdges v ≠ [] ∧ ((G.atEdges v).length ≠ 2 ∨ G.atCharge v ≠ 0)) :
    (G.twist c t).atEdges v ≠ [] ∧ (((G.twist c t).atEdges v).length ≠ 2 ∨ (G.twist c t).atCharge v ≠ 0) := by
  refine ⟨(BALvl1C_atEdges_twist_ne_nil c t G v).2 h.1, ?_⟩
  rw [BALvl1C_atEdges_twist_length]
  rcases h.2 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (fun h0 => h2 ((BALvl1C_atCharge_twist_eq_zero c t G v).1 h0))

/-- the `hnb` clause of `BAFrameStep.gg`, `BAFrameStep.ggSplit` at the twist -/
theorem BALvl1C_hnb_twist (c t : Bool) (G : BAGraph E I)
    (h : ∀ i : I, G.intAtom (Sum.inr i) = true → (G.atEdges (Sum.inr i)).length = 0 ∨
      ((G.atEdges (Sum.inr i)).length = 2 ∧ G.atCharge (Sum.inr i) = 0)) :
    ∀ i : I, (G.twist c t).intAtom (Sum.inr i) = true → ((G.twist c t).atEdges (Sum.inr i)).length = 0 ∨
      (((G.twist c t).atEdges (Sum.inr i)).length = 2 ∧ (G.twist c t).atCharge (Sum.inr i) = 0) := by
  intro i hi
  rw [BAGraph.BASymm1_twist_intAtom] at hi
  rw [BALvl1C_atEdges_twist_length, BALvl1C_atCharge_twist_eq_zero]
  exact h i hi

/-- the `hwf` clause at the twist -/
theorem BALvl1C_hwf_twist (c t : Bool) (G : BAGraph E I) (h : ∀ e ∈ G.solid, G.sameAtom e.src e.dst = false) :
    ∀ e ∈ (G.twist c t).solid, (G.twist c t).sameAtom e.src e.dst = false := by
  intro e he
  rw [BALvl1C_twist_solid, List.mem_map] at he
  obtain ⟨e', he', rfl⟩ := he
  rw [BAGraph.BASymm1_twist_sameAtom]
  rcases BASymm1_twistS_ends c t e' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact h e' he'
  · rw [h1, h2, BAGraph.BAAtomic_sameAtom_comm]; exact h e' he'

/-- vertices of one atom: the `sameAtom`, `intAtom`, `atEdges`, `atCharge` of two vertices with equal atoms agree -/
theorem BALvl1C_atom_congr {G : BAGraph E I} {u v : E ⊕ I} (h : G.atom u = G.atom v) :
    G.sameAtom u = G.sameAtom v ∧ G.intAtom u = G.intAtom v ∧ G.atEdges u = G.atEdges v ∧ G.atCharge u = G.atCharge v := by
  have h1 : G.sameAtom u = G.sameAtom v := by
    funext w; simp only [BAGraph.sameAtom, h]
  refine ⟨h1, by simp only [BAGraph.intAtom, h], ?_, ?_⟩
  · simp only [BAGraph.atEdges, h1]
  · simp only [BAGraph.atCharge, BAGraph.atEdges, h1]

/-- a vertex of an internal atom is an internal vertex -/
theorem BALvl1C_inr_of_mem {G : BAGraph E I} {v w : E ⊕ I} (hv : G.intAtom v = true) (hw : w ∈ G.atom v) : ∃ u : I, w = Sum.inr u := by
  have := (G.BAAtomic_intAtom_iff v).1 hv w hw
  cases w with
  | inl a => simp at this
  | inr u => exact ⟨u, rfl⟩

/-- an edge of `atEdges v` of an internal atom has exactly one end in the atom, an internal vertex `inr u`; that end is the source or the target -/
theorem BALvl1C_end_in_atom {G : BAGraph E I} {v : E ⊕ I} (hv : G.intAtom v = true) {e : SEdge (E ⊕ I)} (he : e ∈ G.atEdges v) :
    ∃ u : I, G.atom (Sum.inr u) = G.atom v ∧ ((e.src = Sum.inr u ∧ e.dst ≠ Sum.inr u) ∨ (e.dst = Sum.inr u ∧ e.src ≠ Sum.inr u)) := by
  have hF : (G.sameAtom v e.src != G.sameAtom v e.dst) = true := (List.mem_filter.1 he).2
  have hmem : ∀ w : E ⊕ I, G.sameAtom v w = true → G.atom w = G.atom v := fun w hw =>
    BALvl1B_atom_eq_of_mem G ((G.BAAtomic_sameAtom_iff v w).1 hw)
  rcases Bool.eq_false_or_eq_true (G.sameAtom v e.src) with ha | ha <;> rcases Bool.eq_false_or_eq_true (G.sameAtom v e.dst) with hb | hb
  · simp [ha, hb] at hF
  · obtain ⟨u, hu⟩ := BALvl1C_inr_of_mem hv ((G.BAAtomic_sameAtom_iff v e.src).1 ha)
    refine ⟨u, by rw [← hu]; exact hmem _ ha, Or.inl ⟨hu, fun h => ?_⟩⟩
    rw [h, ← hu] at hb
    simp [ha] at hb
  · obtain ⟨u, hu⟩ := BALvl1C_inr_of_mem hv ((G.BAAtomic_sameAtom_iff v e.dst).1 hb)
    refine ⟨u, by rw [← hu]; exact hmem _ hb, Or.inr ⟨hu, fun h => ?_⟩⟩
    rw [h, ← hu] at ha
    simp [hb] at ha
  · simp [ha, hb] at hF

end Transport

/-! ## 4. Target 2: a step exists at every normal graph that is not locally standard (`lvl1_exists_step`, `LWLvl1:3655`) -/

section Exists

/-- the selector of a pair at two vertices: after the twist `(c, t)` both edges are blue, the first starts at `u`, the second ends at `u'`
(`lwSymm_selector_pair` with two vertices) -/
theorem BALvl1C_pair_selector {V : Type*} (p q : SEdge V) (u u' : V) (hσ : q.σ = p.σ)
    (h : (p.src = u ∧ q.dst = u') ∨ (p.dst = u ∧ q.src = u')) :
    ∃ c t : Bool, (lwSymmTwistS c t p).σ = true ∧ (lwSymmTwistS c t p).src = u ∧ (lwSymmTwistS c t q).σ = true ∧
      (lwSymmTwistS c t q).dst = u' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨!p.σ, false, ?_⟩
    rw [lwSymmTwistS_eq, lwSymmTwistS_eq, hσ]
    cases p.σ <;> simp [h1, h2]
  · refine ⟨!p.σ, true, ?_⟩
    rw [lwSymmTwistS_eq, lwSymmTwistS_eq, hσ]
    cases p.σ <;> simp [h1, h2]

/-- case (1a): an atom-level loop that is a self-loop: `weight` at the twist `(!σ, false)` -/
private theorem BALvl1C_exists_weight {E : Type} (P : BAPGraph E) (hN : P.g.Normal) (hA : ¬ ∀ e ∈ P.g.solid, e.src ≠ e.dst) :
    ∃ outs, BALocStep P outs := by
  push Not at hA
  obtain ⟨e, he, hl⟩ := hA
  obtain ⟨p, hp, hpe⟩ := lvl1_exists_split_fst P.g.solid e he
  have hc : e.circ = true := hN.2 e he
  have h1 : lwSymmTwistS (!e.σ) false p.1 = ⟨true, true, e.src, e.src⟩ := by
    rw [hpe]; exact lwSymm_twist_weight e e.src rfl hl.symm hc
  refine ⟨_, !e.σ, false, _, BAFrameStep.weight (P.twist (!e.σ) false) (lwSymmTwistP (!e.σ) false p)
    (BASymm2_frame_mem _ _ P.g p hp) ?_, rfl⟩
  change (lwSymmTwistS (!e.σ) false p.1).σ = true ∧ (lwSymmTwistS (!e.σ) false p.1).circ = true ∧
    (lwSymmTwistS (!e.σ) false p.1).src = (lwSymmTwistS (!e.σ) false p.1).dst
  rw [h1]
  exact ⟨rfl, rfl, rfl⟩

/-- case (1b): a solid edge inside an atom, not a self-loop: `within` at the twist `(!σ, false)` -/
private theorem BALvl1C_exists_within {E : Type} (P : BAPGraph E) (hN : P.g.Normal) (hA : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
    (hwf : ¬ ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false) : ∃ outs, BALocStep P outs := by
  push Not at hwf
  obtain ⟨e, he, hs⟩ := hwf
  have hs' : P.g.sameAtom e.src e.dst = true := by simpa using hs
  obtain ⟨p, hp, hpe⟩ := lvl1_exists_split_fst P.g.solid e he
  have hc : e.circ = true := hN.2 e he
  have h1 : lwSymmTwistS (!e.σ) false p.1 = ⟨true, e.circ, e.src, e.dst⟩ := by
    rw [hpe]; exact lwSymm_twist_out e e.src rfl
  refine ⟨_, !e.σ, false, _, BAFrameStep.within (P.twist (!e.σ) false) (lwSymmTwistP (!e.σ) false p)
    (BASymm2_frame_mem _ _ P.g p hp) ?_, rfl⟩
  change (lwSymmTwistS (!e.σ) false p.1).σ = true ∧ (lwSymmTwistS (!e.σ) false p.1).circ = true ∧
    (lwSymmTwistS (!e.σ) false p.1).src ≠ (lwSymmTwistS (!e.σ) false p.1).dst ∧
    (P.g.twist (!e.σ) false).sameAtom (lwSymmTwistS (!e.σ) false p.1).src (lwSymmTwistS (!e.σ) false p.1).dst = true
  rw [h1, BAGraph.BASymm1_twist_sameAtom]
  exact ⟨rfl, hc, hA e he, hs'⟩

/-- case (2): an internal atom with an edge and a bad shape: `edge` at an edge of it, at its end in the atom -/
private theorem BALvl1C_exists_edge {E : Type} (P : BAPGraph E) (hN : P.g.Normal) (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hbad : ∃ j : P.I', P.g.intAtom (Sum.inr j) = true ∧ P.g.atEdges (Sum.inr j) ≠ [] ∧
      ((P.g.atEdges (Sum.inr j)).length ≠ 2 ∨ P.g.atCharge (Sum.inr j) ≠ 0)) : ∃ outs, BALocStep P outs := by
  obtain ⟨j, hjint, hjne, hjbad⟩ := hbad
  obtain ⟨e, he⟩ := List.exists_mem_of_length_pos (List.length_pos_iff.2 hjne)
  have heS : e ∈ P.g.solid := (List.mem_filter.1 he).1
  obtain ⟨u, hatom, hends⟩ := BALvl1C_end_in_atom hjint he
  obtain ⟨-, hintA, hedA, hchA⟩ := BALvl1C_atom_congr hatom
  obtain ⟨c, t, v, hv, hcv⟩ := lwSymm_selector_edge e (Sum.inr u) hends
  obtain ⟨p, hp, hpe⟩ := lvl1_exists_split_fst P.g.solid e heS
  have hec : e.circ = true := hN.2 e heS
  have hp1 : lwSymmTwistS c t p.1 = ⟨true, e.circ, Sum.inr u, v⟩ := by rw [hpe]; exact hcv
  have hp' : lwSymmTwistP c t p ∈ lwSplit (P.twist c t).g.solid := BASymm2_frame_mem c t P.g p hp
  have hwf' := BALvl1C_hwf_twist c t P.g hwf
  refine ⟨_, c, t, _, BAFrameStep.edge (P.twist c t) (lwSymmTwistP c t p) hp' ?_ u ?_ hwf' ?_ ?_ ?_, rfl⟩
  · change (lwSymmTwistS c t p.1).σ = true ∧ (lwSymmTwistS c t p.1).circ = true
    rw [hp1]; exact ⟨rfl, hec⟩
  · change (lwSymmTwistS c t p.1).src = Sum.inr u
    rw [hp1]
  · exact hwf' _ (lvl1_mem_split_fst _ _ hp')
  · change (P.g.twist c t).intAtom (Sum.inr u) = true
    rw [BAGraph.BASymm1_twist_intAtom, hintA]; exact hjint
  · change (P.g.twist c t).atEdges (Sum.inr u) ≠ [] ∧ (((P.g.twist c t).atEdges (Sum.inr u)).length ≠ 2 ∨ (P.g.twist c t).atCharge (Sum.inr u) ≠ 0)
    exact BALvl1C_hbad_twist c t P.g (Sum.inr u) (by rw [hedA, hchA]; exact ⟨hjne, hjbad⟩)

/-- case (3): every internal atom has no edge or two edges and charge `0`, and one has two edges of one colour, one out and one in: `gg` (one vertex) or
`ggSplit` (two vertices of the atom) -/
private theorem BALvl1C_exists_pair {E : Type} (P : BAPGraph E) (hN : P.g.Normal) (hn : ¬ P.g.LocStd)
    (hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false)
    (hbad : ¬ ∃ j : P.I', P.g.intAtom (Sum.inr j) = true ∧ P.g.atEdges (Sum.inr j) ≠ [] ∧
      ((P.g.atEdges (Sum.inr j)).length ≠ 2 ∨ P.g.atCharge (Sum.inr j) ≠ 0)) : ∃ outs, BALocStep P outs := by
  have hnb : ∀ i : P.I', P.g.intAtom (Sum.inr i) = true → (P.g.atEdges (Sum.inr i)).length = 0 ∨
      ((P.g.atEdges (Sum.inr i)).length = 2 ∧ P.g.atCharge (Sum.inr i) = 0) := by
    intro i hi
    by_cases h0 : P.g.atEdges (Sum.inr i) = []
    · left; rw [h0]; rfl
    · right
      by_contra hcon
      exact hbad ⟨i, hi, h0, not_and_or.1 hcon⟩
  have hex : ∃ i : P.I', P.g.intAtom (Sum.inr i) = true ∧ ¬ (P.g.atEdges (Sum.inr i) = [] ∨
      (((P.g.atEdges (Sum.inr i)).map SEdge.σ = [true, false] ∨ (P.g.atEdges (Sum.inr i)).map SEdge.σ = [false, true]) ∧
        P.g.atCharge (Sum.inr i) = 0)) := by
    by_contra hcon
    apply hn
    refine ⟨hN, hwf, fun i hi => ?_⟩
    by_contra hi'
    exact hcon ⟨i, hi, hi'⟩
  obtain ⟨i, hi, hi'⟩ := hex
  have hne : P.g.atEdges (Sum.inr i) ≠ [] := fun h => hi' (Or.inl h)
  obtain ⟨hlen, hch⟩ := (hnb i hi).resolve_left (fun h => hne (List.length_eq_zero_iff.1 h))
  obtain ⟨e1, e2, hE⟩ := List.length_eq_two.1 hlen
  have hσ : e1.σ = e2.σ := by
    by_contra hneq
    apply hi'
    right
    refine ⟨?_, hch⟩
    rw [hE]
    cases h1 : e1.σ <;> cases h2 : e2.σ <;> simp_all
  have hm1 : e1 ∈ P.g.atEdges (Sum.inr i) := by rw [hE]; simp
  have hm2 : e2 ∈ P.g.atEdges (Sum.inr i) := by rw [hE]; simp
  have hF1 : (P.g.sameAtom (Sum.inr i) e1.src != P.g.sameAtom (Sum.inr i) e1.dst) = true := (List.mem_filter.1 hm1).2
  have hF2 : (P.g.sameAtom (Sum.inr i) e2.src != P.g.sameAtom (Sum.inr i) e2.dst) = true := (List.mem_filter.1 hm2).2
  have hch' := hch
  unfold BAGraph.atCharge at hch'
  rw [hE] at hch'
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at hch'
  have key : (P.g.sameAtom (Sum.inr i) e1.src = true ∧ P.g.sameAtom (Sum.inr i) e2.dst = true) ∨
      (P.g.sameAtom (Sum.inr i) e1.dst = true ∧ P.g.sameAtom (Sum.inr i) e2.src = true) := by
    rcases Bool.eq_false_or_eq_true (P.g.sameAtom (Sum.inr i) e1.src) with a1 | a1 <;>
    rcases Bool.eq_false_or_eq_true (P.g.sameAtom (Sum.inr i) e1.dst) with b1 | b1 <;>
    rcases Bool.eq_false_or_eq_true (P.g.sameAtom (Sum.inr i) e2.src) with a2 | a2 <;>
    rcases Bool.eq_false_or_eq_true (P.g.sameAtom (Sum.inr i) e2.dst) with b2 | b2 <;>
    rcases Bool.eq_false_or_eq_true e2.σ with s | s <;> simp_all
  have hin : ∀ w : P.E' ⊕ P.I', P.g.sameAtom (Sum.inr i) w = true → ∃ a : P.I', w = Sum.inr a ∧ P.g.atom (Sum.inr a) = P.g.atom (Sum.inr i) := by
    intro w hw
    obtain ⟨a, ha⟩ := BALvl1C_inr_of_mem hi ((P.g.BAAtomic_sameAtom_iff _ w).1 hw)
    refine ⟨a, ha, ?_⟩
    rw [← ha]
    exact BALvl1B_atom_eq_of_mem P.g ((P.g.BAAtomic_sameAtom_iff _ w).1 hw)
  obtain ⟨p, hp, hp1, q, hq, hq1⟩ := lvl1_split_two P.g.solid (fun e => P.g.sameAtom (Sum.inr i) e.src != P.g.sameAtom (Sum.inr i) e.dst) e1 e2 hE
  obtain ⟨a, a', hends, hA, hA'⟩ : ∃ a a' : P.I', ((e1.src = Sum.inr a ∧ e2.dst = Sum.inr a') ∨ (e1.dst = Sum.inr a ∧ e2.src = Sum.inr a')) ∧
      P.g.atom (Sum.inr a) = P.g.atom (Sum.inr i) ∧ P.g.atom (Sum.inr a') = P.g.atom (Sum.inr i) := by
    rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · obtain ⟨a, ha, ha'⟩ := hin _ k1
      obtain ⟨a', hb, hb'⟩ := hin _ k2
      exact ⟨a, a', Or.inl ⟨ha, hb⟩, ha', hb'⟩
    · obtain ⟨a, ha, ha'⟩ := hin _ k1
      obtain ⟨a', hb, hb'⟩ := hin _ k2
      exact ⟨a, a', Or.inr ⟨ha, hb⟩, ha', hb'⟩
  obtain ⟨c, t, h1σ, h1s, h2σ, h2d⟩ := BALvl1C_pair_selector p.1 q.1 (Sum.inr a) (Sum.inr a') (by rw [hp1, hq1]; exact hσ.symm)
    (by rw [hp1, hq1]; exact hends)
  have hp' : lwSymmTwistP c t p ∈ lwSplit (P.twist c t).g.solid := BASymm2_frame_mem c t P.g p hp
  have hq' : lwSymmTwistP c t q ∈ lwSplit (lwSymmTwistP c t p).2 := BASymm2_pair_mem c t p q hq
  have hwf' := BALvl1C_hwf_twist c t P.g hwf
  have hint : (P.g.twist c t).intAtom (Sum.inr a) = true := by
    rw [BAGraph.BASymm1_twist_intAtom, (BALvl1C_atom_congr hA).2.1]; exact hi
  have hnb' := BALvl1C_hnb_twist c t P.g hnb
  have hpc : p.1.circ = true := hN.2 _ (lvl1_mem_split_fst _ _ hp)
  have hqc : q.1.circ = true := hN.2 _ (lvl1_mem_split _ p hp _ (lvl1_mem_split_fst _ _ hq))
  have hcirc : (lwSymmTwistP c t p).1.circ = true ∧ (lwSymmTwistP c t q).1.circ = true :=
    ⟨BASymm2_frame_circ c t p hpc, BASymm2_frame_circ c t q hqc⟩
  by_cases hax : a = a'
  · subst hax
    exact ⟨_, c, t, _, BAFrameStep.gg (P.twist c t) (lwSymmTwistP c t p) hp' (lwSymmTwistP c t q) hq'
      ⟨h1σ, hcirc.1, h2σ, hcirc.2⟩ a ⟨h1s, h2d⟩ hwf' hint hnb', rfl⟩
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hq
    have hj' : (lwSplit (lwSymmTwistP c t p).2)[j]? = some (lwSymmTwistP c t q) := by
      rw [show (lwSymmTwistP c t p).2 = p.2.map (lwSymmTwistS c t) from rfl, lwSymm_lwSplit_twistP, List.getElem?_map, hj]
      rfl
    have hsame : (P.g.twist c t).sameAtom (Sum.inr a) (Sum.inr a') = true := by
      rw [BAGraph.BASymm1_twist_sameAtom]
      exact (P.g.BAAtomic_sameAtom_iff_atom_eq _ _).2 (hA.trans hA'.symm)
    exact ⟨_, c, t, _, BAFrameStep.ggSplit (P.twist c t) (lwSymmTwistP c t p) hp' (lwSymmTwistP c t q) j hj'
      ⟨h1σ, hcirc.1, h2σ, hcirc.2⟩ a a' ⟨h1s, h2d⟩ hax hsame hwf' hint hnb', rfl⟩

/-- **Target 2: `baLvl1ExistsStep_holds`** (twin of `lvl1_exists_step`, `LWLvl1:3655`; design §3 Step 2): a normal packed BA graph that is not locally standard
admits a step of the strategy: a weight (a self-loop), a `within` step (a solid edge inside an atom), an `edge` step (an internal atom with an edge and
a bad shape), or a `gg`/`ggSplit` step (an internal atom with two solid edges of one colour, one out and one in, charge `0`). -/
theorem baLvl1ExistsStep_holds : BAlvl1ExistsStep := by
  intro E P hN hn
  classical
  by_cases hA : ∀ e ∈ P.g.solid, e.src ≠ e.dst
  · by_cases hwf : ∀ e ∈ P.g.solid, P.g.sameAtom e.src e.dst = false
    · by_cases hbad : ∃ j : P.I', P.g.intAtom (Sum.inr j) = true ∧ P.g.atEdges (Sum.inr j) ≠ [] ∧
          ((P.g.atEdges (Sum.inr j)).length ≠ 2 ∨ P.g.atCharge (Sum.inr j) ≠ 0)
      · exact BALvl1C_exists_edge P hN hwf hbad
      · exact BALvl1C_exists_pair P hN hn hwf hbad
    · exact BALvl1C_exists_within P hN hA hwf
  · exact BALvl1C_exists_weight P hN hA

end Exists

/-! ## 5. Target 4: the BA `lvl1 lemma` (`lvl1_exists_aux`, `lvl1_lemma`, `LWLvl1:3837-3938`) -/

section Lemma

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- the value of a packed graph at `BAlwData` is integrable (factoring labels: `BALvl1A_integrable_val`; otherwise the value is `0`) -/
private theorem BALvl1C_integrable_pval (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
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

/-- the integral of the value of a list of packed graphs is the list sum of the integrals (every graph value is integrable) -/
private theorem BALvl1C_integral_comb (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E : Type} (Ls : List (BAPGraph E)) (ℓe : E → Idx d L W) :
    ∫ ω, BAComb.val Ls (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      (Ls.map fun Q => ∫ ω, Q.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)).sum :=
  owx_integral_list_sum (PF d L W 0) Ls (fun Q ω => Q.val (BAlwData d L W g0 Em t m ω) ℓe)
    fun Q _ => BALvl1C_integrable_pval hL g0 Em t m hSelf ht0 ht1 Q ℓe

end Lemma

/-- the identity of expectations `E Γ = E Σ (outs ++ errs)` of the lemma, at all admissible data and external labels -/
private def BALvl1C_Ident (d : ℕ) {E : Type} (Γ : BAPGraph E) (outs errs : List (BAPGraph E)) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ ℓe : E → Idx d L W, ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
      ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- **the existence of the lists, by strong induction on the measure** (`lvl1_exists_aux`, `LWLvl1:3837`) -/
private theorem BALvl1C_aux (d : ℕ) {E : Type} (K : ℤ) (Γ : BAPGraph E) (hN : Γ.g.Normal) :
    ∃ outs errs : List (BAPGraph E), (∀ Q ∈ outs, Q.g.LocStd ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
      (∀ Q ∈ outs ++ errs, BAReach K Γ Q) ∧ BALvl1C_Ident d Γ outs errs := by
  classical
  induction Γ using (InvImage.wf (BALvl1Mu K) baLvl1Lt_wf).induction with
  | _ Γ ih =>
    by_cases hK : K ≤ Γ.g.scalingOrder
    · refine ⟨[], [Γ], by simp, by simpa using hK, by simpa using BALvl1A_reach_refl K Γ, ?_⟩
      intro L W _ _ _ g0 Em t m _ _ _ ℓe
      simp [BAComb.val]
    by_cases hL : Γ.g.LocStd
    · refine ⟨[Γ], [], by simpa using ⟨hL, by omega⟩, by simp, by simpa using BALvl1A_reach_refl K Γ, ?_⟩
      intro L W _ _ _ g0 Em t m _ _ _ ℓe
      simp [BAComb.val]
    obtain ⟨L, hst⟩ := baLvl1ExistsStep_holds Γ hN hL
    have hgood := baLvl1StepGood_holds Γ L hst hN
    have hlt : Γ.g.scalingOrder < K := not_le.1 hK
    obtain ⟨fo, fe, hfo⟩ := lvl1_choose_list
      (fun (Q : BAPGraph E) (o e : List (BAPGraph E)) => (∀ Q' ∈ o, Q'.g.LocStd ∧ Q'.g.scalingOrder < K) ∧
        (∀ Q' ∈ e, K ≤ Q'.g.scalingOrder) ∧ (∀ Q' ∈ o ++ e, BAReach K Q Q') ∧ BALvl1C_Ident d Q o e) L
      (fun Q hQ => ih Q (ba_lvl1_mu_lt hlt (hgood Q hQ).2) (hgood Q hQ).1)
    have hreach : ∀ Q ∈ L, BAReach K Γ Q := fun Q hQ => BAReach.step Γ Γ Q L (BAReach.refl Γ) hlt hL hst hQ
    refine ⟨L.flatMap fo, L.flatMap fe, ?_, ?_, ?_, ?_⟩
    · intro Q' hQ'
      obtain ⟨Q, hQ, hQ'⟩ := List.mem_flatMap.1 hQ'
      exact (hfo Q hQ).1 Q' hQ'
    · intro Q' hQ'
      obtain ⟨Q, hQ, hQ'⟩ := List.mem_flatMap.1 hQ'
      exact (hfo Q hQ).2.1 Q' hQ'
    · intro Q' hQ'
      rcases List.mem_append.1 hQ' with h | h
      · obtain ⟨Q, hQ, h⟩ := List.mem_flatMap.1 h
        exact (hreach Q hQ).trans ((hfo Q hQ).2.2.1 Q' (List.mem_append_left _ h))
      · obtain ⟨Q, hQ, h⟩ := List.mem_flatMap.1 h
        exact (hreach Q hQ).trans ((hfo Q hQ).2.2.1 Q' (List.mem_append_right _ h))
    · intro Lx W _ _ hLx g0 Em t m hSelf ht0 ht1 ℓe
      have hI := fun (F : List (BAPGraph E)) =>
        BALvl1C_integral_comb (d := d) (L := Lx) (W := W) hLx g0 Em t m hSelf ht0 ht1 F ℓe
      rw [baLvl1StepIdentity_holds d Lx W hLx g0 Em t m hSelf ht0 ht1 Γ L hst hN ℓe, hI, hI, List.map_append, List.sum_append,
        lvl1_sum_flatMap L fo (fun Q => ∫ ω, Q.val (BAlwData d Lx W g0 Em t m ω) ℓe ∂(PF d Lx W 0)),
        lvl1_sum_flatMap L fe (fun Q => ∫ ω, Q.val (BAlwData d Lx W g0 Em t m ω) ℓe ∂(PF d Lx W 0)), ← List.sum_map_add]
      refine congrArg List.sum (List.map_congr_left fun Q hQ => ?_)
      have h1 := (hfo Q hQ).2.2.2 Lx W hLx g0 Em t m hSelf ht0 ht1 ℓe
      rw [hI, List.map_append, List.sum_append] at h1
      exact h1

/-- **Target 4: `baLvl1Lemma_holds`** (the BA `lvl1 lemma`, twin of `lvl1_lemma`, `LWLvl1:3907`; design §3 Steps 4, 6): every normal packed BA graph `Γ` and every cutoff `K`
give finite lists `outs`, `errs`, independent of the data, with the pinned conclusions; the invariants (normal, `ord`, `n_M`, `n_A - n_W`) are carried along `BAReach` by
`ba_lvl1_induction` and `baLvl1StepGood_holds`; the identity of expectations is `baLvl1StepIdentity_holds` at each step and integrability of the values
(`BALvl1A_integrable_val`).  The only data hypotheses are `BASelf` and `0 ≤ t < 1` (C1). -/
theorem baLvl1Lemma_holds (d : ℕ) : BAlvl1Lemma d := by
  intro E K Γ hN
  obtain ⟨outs, errs, hout, herr, hreach, hid⟩ := BALvl1C_aux d K Γ hN
  have hinv : ∀ Q ∈ outs ++ errs, Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (Γ.g.nA : ℤ) - Γ.g.nW := by
    intro Q hQ
    refine ba_lvl1_induction (hreach Q hQ) (fun Q => Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧
        (Q.g.nA : ℤ) - Q.g.nW ≤ (Γ.g.nA : ℤ) - Γ.g.nW) ⟨hN, le_refl _, le_refl _, le_refl _⟩ ?_
    intro A L hst hA B hB
    obtain ⟨hBN, hg⟩ := baLvl1StepGood_holds A L hst hA.1 B hB
    obtain ⟨h1, h2, h3, -⟩ := hg
    exact ⟨hBN, le_trans hA.2.1 h1, le_trans h2 hA.2.2.1, by have := hA.2.2.2; omega⟩
  refine ⟨outs, errs, fun Q hQ => ⟨(hout Q hQ).1, (hinv Q (List.mem_append_left _ hQ)).2.1, (hout Q hQ).2⟩, fun Q hQ => herr Q hQ,
    fun Q hQ => ⟨hreach Q hQ, hinv Q hQ⟩, ?_⟩
  intro L W _ _ hL g0 Em t m hSelf ht0 ht1 ℓe
  exact hid L W hL g0 Em t m hSelf ht0 ht1 ℓe

/-! ## 6. Target 5: the paper form (`lvl1_lemma_size`, `LWLvl1:4047`) -/

/-- **Target 5: `baLvl1LemmaSize_holds`** (twin of `lvl1_lemma_size`, `LWLvl1:4047-4071`; design §3 Step 5): `baLvl1Lemma_holds` at the cutoff
`K = lvl1Cutoff c K0 d D P.g.counters` and the generic `lvl1_size_le` on the counters (`BAGraph.counters`: the slot `nV` is `n_A`): the errors have scaling size
`≤ W^{-D}` in the window `W^{-d/2} ≤ Ψ ≤ W^{-c}`, `L^d ≤ W^{K0}`. -/
theorem baLvl1LemmaSize_holds (d : ℕ) : BAlvl1LemmaSize d := by
  intro E c hc K0 D P hN
  obtain ⟨outs, errs, hout, herr, hall, hid⟩ := baLvl1Lemma_holds d (lvl1Cutoff c K0 d D P.g.counters : ℤ) P hN
  refine ⟨outs, errs, fun Q hQ => ⟨(hout Q hQ).1, (hout Q hQ).2.1⟩, ?_, hall, hid⟩
  intro Q hQ W L Ψ hW hL hLW hlow hup
  obtain ⟨-, -, -, hM, hV⟩ := hall Q (List.mem_append_right _ hQ)
  exact lvl1_size_le c hc K0 d D P.g.counters W L Ψ hW hL hLW hlow hup Q.g.counters (herr Q hQ) hM hV

/-! ## 7. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point of `BA/CouplingWindow.lean`; `BASelf` and `0 < t₀ < 1` are `flowP_data`) -/

end RBM.Graph

end
