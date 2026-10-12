/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BALvl1B

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
# BA-L L3a4 (T2442), part 2: the macro claims, `baStepMono_holds`, `baLvl1StepGood_holds`

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:353-409`.  Design: `docs/reports/T2395-design.md` §3 Step 3 (e) (the macro claims).  Part 1 is `Graph/BALvl1B`.

## Contents (namespace `RBM.Graph`; private prefix `BALvl1B_`)

1. **The terms of the macro steps**: `BALvl1B_d_mono` (the terms `W.first`, `X.d1`-`X.d4` at `T°`), `BALvl1B_trB_inv` (the invariants of the transfer graph of macro (b)),
   `BALvl1B_ord_d4` (the weak order of `X.d4`, R1 has only `BASim_d4`).
2. **The macro claims**: `BALvl1B_within` (macro (a), outputs of `BAPGraph.withinOuts`), `BALvl1B_ggSplit` (macro (b), outputs of `BAPGraph.splitOuts`): the first-stage terms over `P`, the second-stage terms
   (`lw2`, `lw4`, `gg2`, `gg4`) over the transfer graph, whose invariants are those of `P` (`BASim_inv_trA`, `BALvl1B_trB_inv`).
3. **Targets 4 and 5**: `baStepMono_holds : BAstepMono` (one case per constructor of `BAFrameStep`), `baLvl1StepGood_holds : BAlvl1StepGood` (the reduction `ba_lvl1StepGood_of_sim'` at `BAimg_holds`,
   `baSim'_holds m`, `baStepMono_holds`, `baTwistInv_holds`).
4. Compiled instances (the five R1 data of `BALvl1AInst`).
-/

noncomputable section

namespace RBM.Graph

open RBM

/-! ## 1. The terms of the macro steps -/

section Dterms

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The terms `ext 2 Γ rest s [S_{αβ}] (M_{xα} :: md)`** (`W.first` of macro (a), `X.d1`-`X.d4` of macro (b)): at `T°` `n_M` and `n_A - n_W` do not grow (they have the waved, dotted and `Ψ`-dotted edges of
`ext 2 Γ rest [] [S_{αβ}] [M_{xα}]`, which has `n_W + 1`, `n_A + 1`, `n_M` of `Γ`: `BALvl1B_ext1`; coarsening `BALvl1B_mono_of_ref`). -/
theorem BALvl1B_d_mono (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (x : E ⊕ I) :
    (BAWeightOp_circ (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] (bpM (owxEmb 2 x) (bpv 0) :: md))).nM ≤ Γ.nM ∧
      ((BAWeightOp_circ (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] (bpM (owxEmb 2 x) (bpv 0) :: md))).nA : ℤ) -
        (BAWeightOp_circ (BAGraph.ext 2 Γ rest s [bpW false (bpv 0) (bpv 1)] (bpM (owxEmb 2 x) (bpv 0) :: md))).nW ≤ (Γ.nA : ℤ) - Γ.nW := by
  have hB := BALvl1B_ext1 Γ rest [] x
  refine BALvl1B_mono_of_ref (B := BAGraph.ext 2 Γ rest [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 x) (bpv 0)]) (d := 1) rfl rfl rfl (fun e he => ?_)
    ⟨congrArg Counters.nW hB, congrArg Counters.nV hB, congrArg Counters.nM hB⟩
  simp only [BAGraph.ext, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he ⊢
  tauto

/-- **The transfer graph of macro (b) has the invariants of `Γ`** (the four that `BAstepMono` reads: order, `n_M`, `n_A - n_W`, `nExt`; the other three are `BASim_trB_facts`): `ext 2 Γ q.2 [S_{y'β}, S_{βy}] [S_{αβ}]
[M_{aα}, M_{αa'}]` with `[a] = [a']` has `n_W + 1`, `n_A + 1`, `n_M`, `n_S` of `Γ` (`BASim_counters_tr2`) and `nExt` of `Γ` (`BASim_cons_tr2`). -/
theorem BALvl1B_trB_inv (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    (BAGraph.BAScost_trB Γ p q).scalingOrder = Γ.scalingOrder ∧ (BAGraph.BAScost_trB Γ p q).nM = Γ.nM ∧
      ((BAGraph.BAScost_trB Γ p q).nA : ℤ) - (BAGraph.BAScost_trB Γ p q).nW = (Γ.nA : ℤ) - Γ.nW ∧ (BAGraph.BAScost_trB Γ p q).nExt = Γ.nExt := by
  have hC := BASim_cons_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] p.1.src q.1.dst hsame
  have hcnt := BASim_counters_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] p.1.src q.1.dst hsame
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  rw [show BAGraph.BAScost_trB Γ p q = BASim_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
    p.1.src q.1.dst from rfl]
  set tr := BASim_tr2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] p.1.src q.1.dst with htr
  have hnS : tr.nS = Γ.nS := by
    have := congrArg Counters.nS hcnt
    simp only [BAGraph.counters, List.length_cons, List.length_nil] at this
    simp only [BAGraph.nS] at this ⊢
    omega
  have hW : tr.nW = Γ.nW + 1 := congrArg Counters.nW hcnt
  have hA : tr.nA = Γ.nA + 1 := congrArg Counters.nV hcnt
  have hM : tr.nM = Γ.nM := congrArg Counters.nM hcnt
  refine ⟨?_, hM, ?_, hC.nExt⟩
  · simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hnS, hW, hA]
    push_cast
    ring
  · rw [hA, hW]
    push_cast
    ring

/-- **The weak order of the term `X.d4`** (`[y] ≠ [y']` or not; R1 has `BASim_d4`: the order rises or `nExt` falls when `[y] ≠ [y']`, and `BASim_inv_d4_A1` when `[y] = [y']`): `d4` is a conservative extension of
`Γ` with the `M`-edge `M_{y'y}` added, so `n_A (d4) ≤ n_A (Γ + M_{y'y}) ≤ n_A (Γ)`, and `ord d4 = ord Γ + 2 (n_A Γ - n_A d4)`. -/
theorem BALvl1B_ord_d4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    Γ.scalingOrder ≤ (BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]).scalingOrder := by
  classical
  set md : List (BAMEdge (E ⊕ (I ⊕ Fin 2))) := [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)] with hmd
  set T := BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)] md with hT
  have h3 : atomSetoid T (owxEmb 2 q.1.src) (bpv 1) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 q.1.src) (bpv 1)) (by simp [hmd])
  have h4 : atomSetoid T (bpv 1) (owxEmb 2 p.1.dst) := BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (bpv 1) (owxEmb 2 p.1.dst)) (by simp [hmd])
  have hyy : T.sameAtom (owxEmb 2 q.1.src) (owxEmb 2 p.1.dst) = true := by
    rw [BASim_sameAtom_iff]
    exact (atomSetoid T).trans h3 h4
  set d : BAMEdge (E ⊕ I) := bpM q.1.src p.1.dst with hd
  have hC := BASim_cons_of_md Γ (Γ.addM d) q.2 [] [bpW false (bpv 0) (bpv 1)] md (BAScost_rho2 p.1.src q.1.src) (BAScost_rho2_emb _ _)
    (fun a b h => BASim_sameAtom_of_adj _ (BASim_atomAdj_addM' Γ d a b h))
    (fun a b h => by
      rcases BASim_atomAdj_addM Γ d a b h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact BASim_sameAtom_of_adj _ (BASim_Ext_atomAdj (BASim_Ext_ext 2 Γ _ _ _ _) a b h)
      · simp only [hd, bpM] at h1 h2; rw [← h1, ← h2]; exact hyy
      · simp only [hd, bpM] at h1 h2; rw [← h1, ← h2]; exact BASim_sameAtom_symm' T hyy)
    (fun e he => by
      simp only [hmd, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp only [bpM, BAScost_rho2_emb, BASim_rho2_alpha, BASim_rho2_beta]
      · exact BAScost_sameAtom_self _ _
      · exact BASim_sameAtom_addM Γ d hsame
      · exact BAScost_sameAtom_self _ _
      · exact BASim_sameAtom_of_adj _ (BASim_atomAdj_addM_d Γ d))
  have hatt : ∀ w : E ⊕ (I ⊕ Fin 2), ∃ v, T.sameAtom (owxEmb 2 v) w = true := by
    rintro (a | i | j)
    · exact ⟨Sum.inl a, BAScost_sameAtom_self _ _⟩
    · exact ⟨Sum.inr i, BAScost_sameAtom_self _ _⟩
    · fin_cases j
      · refine ⟨p.1.src, ?_⟩
        rw [BASim_sameAtom_iff]
        exact BAScost_atomSetoid_ext_md Γ q.2 _ _ _ (bpM (owxEmb 2 p.1.src) (bpv 0)) (by simp [hmd])
      · refine ⟨q.1.src, ?_⟩
        rw [BASim_sameAtom_iff]
        exact h3
  have hA' := hC.nA_le hatt
  have hAd : (Γ.addM d).nA ≤ Γ.nA := by
    obtain ⟨hA1, hA2⟩ := BALvl1B_adj_mono Γ (Γ.addM d) rfl rfl rfl (fun e he => List.mem_cons_of_mem _ he)
    exact (BALvl1B_coarse Γ (Γ.addM d) hA1 hA2).1
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hS : Γ.nS = q.2.length + 2 := by simp only [BAGraph.nS]; omega
  rw [hT, BASim_ord_ext]
  simp only [BAGraph.scalingOrder, BAGraph.counters, ord, hS, List.length_nil, List.length_singleton]
  omega

end Dterms

end RBM.Graph

end
