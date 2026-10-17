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
   `BALvl1B_ord_d4` (the weak order of `X.d4`; R1 has only `BASim_d4`), `BALvl1B_inv4` (the four invariants that `BAstepMono` reads, from `BASim_inv`), `BALvl1B_within_mono`
   (the first group of macro (a)), `BALvl1B_dterms_ok` (the four terms `d1`-`d4` of macro (b), as `BALvl1B_TermOk`).
2. **The macro claims**: `BALvl1B_within` (macro (a), outputs of `BAPGraph.withinOuts`), `BALvl1B_ggSplit` (macro (b), outputs of `BAPGraph.splitOuts`): the first-stage terms over `P`, the second-stage terms
   (`lw2`, `lw4`, `gg2`, `gg4`) over the transfer graph, whose invariants are those of `P` (`BASim_inv_trA`, `BALvl1B_trB_inv`).
3. **Targets 4 and 5**: `baStepMono_holds : BAstepMono` (one case per constructor of `BAFrameStep`), `baLvl1StepGood_holds : BAlvl1StepGood` (the reduction `ba_lvl1StepGood_of_sim'` at `BAimg_holds`,
   `baSim'_holds 0`, `baStepMono_holds`, `baTwistInv_holds`).
4. Compiled instances (the five R1 data of `BALvl1AInst`; namespace `BALvl1BInst`).
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

/-- the four invariants that `BAstepMono` reads, from the equality of the invariant tuples `BASim_inv` -/
theorem BALvl1B_inv4 {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] {T : BAGraph E I} {G : BAGraph E' I'}
    (h : BASim_inv T = BASim_inv G) :
    T.scalingOrder = G.scalingOrder ∧ T.nM = G.nM ∧ (T.nA : ℤ) - T.nW = (G.nA : ℤ) - G.nW ∧ T.nExt = G.nExt := by
  simp only [BASim_inv, Prod.mk.injEq] at h
  obtain ⟨a, b, c, -, -, -, g⟩ := h
  exact ⟨a, b, c, g⟩

/-- the terms of the first group of macro (a): `W.first` (`BALvl1B_d_mono`) and the derivative terms (`BALvl1B_lanlw_mono`) -/
theorem BALvl1B_within_mono (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (h1 : p.1.σ = true) (h2 : p.1.circ = true) :
    ∀ T ∈ BASim_Fwithin p Γ, (BAWeightOp_circ T).nM ≤ Γ.nM ∧ ((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (Γ.nA : ℤ) - Γ.nW := by
  intro T hT
  simp only [BASim_Fwithin, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, hq, rfl⟩
  · exact BALvl1B_d_mono Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [] p.1.src
  · exact BALvl1B_lanlw_mono Γ p hp h1 h2 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hq))

/-- **The four terms `X.d1`-`X.d4` of macro (b) are `BALvl1B_TermOk`** over `Γ`: `d1` by `BASim_fam_d1`; `d2`, `d3` (circled, so `ordG = ord`) by `BASim_ord_d2/d3`; `d4` by `BALvl1B_ord_d4`; the counters at `T°`
by `BALvl1B_d_mono`. -/
theorem BALvl1B_dterms_ok (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2)
    (hsame : Γ.sameAtom p.1.src q.1.dst = true) :
    ∀ T ∈ [BAGraph.ext 2 Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)]
        [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)],
      BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
      BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
      BAGraph.ext 2 Γ q.2 [] [bpW false (bpv 0) (bpv 1)]
        [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]], BALvl1B_TermOk Γ T := by
  have hcirc : ∀ e ∈ q.2, e.circ = true := fun e he => BASim_hcirc hN hp e (lvl1_mem_split _ q hq e he)
  intro T hT
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl
  · have hm := BALvl1B_d_mono Γ q.2 [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)] [] p.1.src
    exact ⟨BASim_Ext_ext 2 Γ _ _ _ _, (BASim_fam_d1 Γ p q hp hq).hmono Γ hN rfl _ (List.mem_singleton_self _), hm.1, hm.2⟩
  · have hm := BALvl1B_d_mono Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)]
      [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)] p.1.src
    have hNT := BALvl1B_ext_normal 2 Γ hN q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)] hcirc (by simp [bpS])
    exact ⟨BASim_Ext_ext 2 Γ _ _ _ _, by rw [BAGraph.scalingOrderG_of_normal _ hNT]; exact WithTop.coe_le_coe.2 (BASim_ord_d2 Γ p q hp hq hsame).le, hm.1, hm.2⟩
  · have hm := BALvl1B_d_mono Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)]
      [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)] p.1.src
    have hNT := BALvl1B_ext_normal 2 Γ hN q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)] hcirc (by simp [bpS])
    exact ⟨BASim_Ext_ext 2 Γ _ _ _ _, by rw [BAGraph.scalingOrderG_of_normal _ hNT]; exact WithTop.coe_le_coe.2 (BASim_ord_d3 Γ p q hp hq hsame).le, hm.1, hm.2⟩
  · have hm := BALvl1B_d_mono Γ q.2 []
      [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)] p.1.src
    have hNT := BALvl1B_ext_normal 2 Γ hN q.2 [] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)] hcirc (by simp)
    exact ⟨BASim_Ext_ext 2 Γ _ _ _ _, by rw [BAGraph.scalingOrderG_of_normal _ hNT]; exact WithTop.coe_le_coe.2 (BALvl1B_ord_d4 Γ p q hp hq hsame), hm.1, hm.2⟩

end Dterms

section Macro

variable {E0 : Type}

/-- **Macro claim (a), `within`** (T2395 design §3 Step 3 (e)): the outputs of the first group (`W.first`, `lanlwD`: `BASim_fam_within`, `BALvl1B_within_mono`) and of the second stage at the transfer graph `tr`
(`lw2`, `lw4` at `Ǧ_{ββ}`: `tr` is normal and has the invariants of `P`, `BASim_inv_trA`; `lw_mono` at `tr`) are normal, their order does not fall, `n_M`, `n_A - n_W`, `nExt` do not grow. -/
theorem BALvl1B_within (P : BAPGraph E0) (hN : P.g.Normal) {p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (h1 : p.1.σ = true) (h2 : p.1.circ = true) (hxy : P.g.sameAtom p.1.src p.1.dst = true) : ∀ Q ∈ P.withinOuts p, BALvl1B_Mono P Q := by
  intro Q hQ
  have hNtr : (BAGraph.BAScost_trA P.g p).Normal :=
    BALvl1B_ext_normal 2 P.g hN _ _ _ _ (BASim_hcirc hN hp) (by simp [bpS])
  have hinv := BALvl1B_inv4 (BASim_inv_trA P.g p hp hxy)
  have hpp : (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2))) ∈ lwSplit (BAGraph.BAScost_trA P.g p).solid := lvl1_split_last _ _
  obtain ⟨m2, m4⟩ := lw_mono (BAGraph.BAScost_trA P.g p) _ hpp rfl rfl
  unfold BAPGraph.withinOuts at hQ
  simp only [List.mem_append] at hQ
  rcases hQ with (hQ | hQ) | hQ
  · exact BALvl1B_outs_fam P P.g (BASim_fam_within P.g p hp h1 h2) (BASim_Fwithin p P.g) (fun T hT => hT) hN ⟨rfl, rfl, rfl, rfl⟩
      (fun T hT => (BALvl1B_within_mono P.g p hp h1 h2 T hT).1) (fun T hT => (BALvl1B_within_mono P.g p hp h1 h2 T hT).2) Q hQ
  · exact BALvl1B_outs_fam P (BAGraph.BAScost_trA P.g p) (BASim_fam_lw2 _ _ hpp rfl rfl) _ (fun T hT => hT) hNtr hinv
      (fun T hT => (m2 T hT).1.le) (fun T hT => (m2 T hT).2.1.le) Q hQ
  · exact BALvl1B_outs_fam P (BAGraph.BAScost_trA P.g p) (BASim_fam_lw4 _ _ hpp rfl rfl) _ (fun T hT => hT) hNtr hinv
      (fun T hT => (m4 T hT).1.le) (fun T hT => (m4 T hT).2.1.le) Q hQ

/-- **Macro claim (b), `ggSplit`** (T2395 design §3 Step 3 (e)): the outputs of `lanlw` (`BASim_fam_lanlw`, `BALvl1B_lanlw_mono`), of the terms `d1`-`d4` (`BALvl1B_dterms_ok`) and of the second stage at the transfer graph `tr`
(`gg2`, `gg4` at the pair `Ǧ_{βy}`, `Ǧ_{y'β}`: `tr` is normal and has the invariants of `P`, `BALvl1B_trB_inv`; `gg_mono` at `tr`) are normal, their order does not fall, `n_M`, `n_A - n_W`, `nExt` do not grow. -/
theorem BALvl1B_ggSplit (P : BAPGraph E0) (hN : P.g.Normal) {p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))} (hp : p ∈ lwSplit P.g.solid)
    (hq : q ∈ lwSplit p.2) (j : ℕ) (h1 : p.1.σ = true) (h2 : p.1.circ = true) (hsame : P.g.sameAtom p.1.src q.1.dst = true) :
    ∀ Q ∈ P.splitOuts p q j, BALvl1B_Mono P Q := by
  intro Q hQ
  have hcirc : ∀ e ∈ q.2, e.circ = true := fun e he => BASim_hcirc hN hp e (lvl1_mem_split _ q hq e he)
  have hNtr : (BAGraph.BAScost_trB P.g p q).Normal := BALvl1B_ext_normal 2 P.g hN _ _ _ _ hcirc (by simp [bpS])
  have hinv := BALvl1B_trB_inv P.g p q hp hq hsame
  have hp2 : (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) ∈
      lwSplit (BAGraph.BAScost_trB P.g p q).solid := by
    have := lvl1_split_last (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) (bpS true (bpv 1) (owxEmb 2 p.1.dst))
    rwa [List.append_assoc] at this
  have hq2 : (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2))) ∈
      lwSplit (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) := lvl1_split_last _ _
  obtain ⟨m2, m4⟩ := gg_mono (BAGraph.BAScost_trB P.g p q) _ _ hp2 hq2
  unfold BAPGraph.splitOuts at hQ
  simp only [List.mem_append] at hQ
  rcases hQ with ((hQ | hQ) | hQ) | hQ
  · refine BALvl1B_outs_fam P P.g (BASim_fam_lanlw P.g p hp h1 h2) _ (fun T hT => ?_) hN ⟨rfl, rfl, rfl, rfl⟩
      (fun T hT => (BALvl1B_lanlw_mono P.g p hp h1 h2 T (?_)).1) (fun T hT => (BALvl1B_lanlw_mono P.g p hp h1 h2 T (?_)).2) Q hQ
    all_goals
      simp only [List.mem_cons, List.mem_map] at hT
      rcases hT with rfl | ⟨q', hq', rfl⟩
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_mem_eraseIdx hq'))
  · exact BALvl1B_outs_ok P P.g _ hN ⟨rfl, rfl, rfl, rfl⟩ (BALvl1B_dterms_ok P.g hN p q hp hq hsame) Q hQ
  · exact BALvl1B_outs_fam P (BAGraph.BAScost_trB P.g p q) (BASim_fam_gg2 _ _ _ hp2 hq2) _ (fun T hT => hT) hNtr hinv
      (fun T hT => (m2 T hT).1) (fun T hT => (m2 T hT).2.1) Q hQ
  · exact BALvl1B_outs_fam P (BAGraph.BAScost_trB P.g p q) (BASim_fam_gg4 _ _ _ hp2 hq2) _ (fun T hT => hT) hNtr hinv
      (fun T hT => (m4 T hT).1) (fun T hT => (m4 T hT).2.1) Q hQ

/-- **Target 4, the counter half of Lemma S** (D§3 Step 3 (a), (c), (e); T2395 probe 269-270): every output of a frame step at a normal BA graph is normal, its order does not fall, `n_M`, `n_A - n_W`
and the number of external atoms do not grow; one case per constructor of `BAFrameStep`. -/
theorem baStepMono_holds : BAstepMono := by
  intro E P outs hst hN Q hQ
  cases hst with
  | weight p hp h => exact BALvl1B_weight P hN hp h.1 h.2.1 Q hQ
  | within p hp h => exact BALvl1B_within P hN hp h.1 h.2.1 h.2.2.2 Q hQ
  | edge p hp h x hx hwf hv hint hbad => exact BALvl1B_edge P hN hp h.1 h.2 Q hQ
  | gg p hp q hq h x hx hwf hint hnb => exact BALvl1B_gg P hN hp hq Q hQ
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb =>
    exact BALvl1B_ggSplit P hN hp (List.mem_of_getElem? hj) j h.1 h.2.1 (by rw [hx.1, hx.2]; exact hsame) Q hQ

/-- **Target 5, `BAlvl1StepGood`** (the BA `lvl1_step_good`, L3a4): the reduction `ba_lvl1StepGood_of_sim'` at the image (`BAimg_holds`, R0), the simulation `baSim'_holds` (R1; `m` is free), `baStepMono_holds` and the twist
invariance `baTwistInv_holds` (L3a1). -/
theorem baLvl1StepGood_holds : BAlvl1StepGood :=
  ba_lvl1StepGood_of_sim' 0 BAimg_holds (baSim'_holds 0) baStepMono_holds baTwistInv_holds

end Macro

/-! ## 4. Compiled instances (the five data of `BALvl1AInst`: `gg` at `P_A`, `within` at `P_B`, `ggSplit` at `P_C`, `weight` at `P_W`, `edge` at `P_E`) -/

end RBM.Graph

end
