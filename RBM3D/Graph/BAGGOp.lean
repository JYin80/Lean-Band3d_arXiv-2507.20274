/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGExp

/-!
# BA-L2c2b: the GG expansion `(B.20)` as a graph operation and the frame identity (T2410)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:393-405` (cited `B:line`; `GGGamma`,
[yang2024Del, Lemma B.11]) with the corrected coefficient `(W - 1)_{xβ} = (M⁺S⁺)_{xβ}` in the first two
sums (paper delta D402, `ba_W_sub_one`).  `baGGGamma_holds` (`Graph/BAGGExp.lean:358`) is the identity of
expectations; this file is its graph form.  The term lists are those of the T2395 probe
(`t/T2395:RBM3D/Probe/T2395Pins.lean:129-148` at `4c1de4c`), copied verbatim.

## Contents (namespace `RBM.Graph`, private prefix `BAGGOp_`)

1. **Target 1**: `BAGraph.gg2`, `BAGraph.gg4` (the merged `BAGraph.ext`, `bpv`, `bpS`, `bpM`, `bpW`,
   `baSum` of `Graph/BAWeightOp.lean`).
2. **Target 2** (`baExpFrame_gg`, the second conjunct of `BAexpFrameE`): `𝔼 Γ.val = 𝔼 (baSum gg2 +
   baSum gg4)` at `BAlwData` over `PF d L W 0`, for circled blue `p ∈ lwSplit Γ.solid`,
   `q ∈ lwSplit p.2`, `p.1.src = q.1.dst`.  It follows from `baGGGamma_holds`, pathwise on the sequence
   space as `baExpFrame_lw` follows from `baLweight_holds`.
3. **Target 3**: `BAexpFrameE` (probe `:244-251`) and `baExpFrameE_holds : ∀ d, BAexpFrameE d`.
4. **Target 4** (counters and order of the terms, `BAstepMono`): see the section header.
5. Compiled instances (`RBM.Graph.BAGGOpInst`).

The private declarations of `Graph/BAWeightOp.lean` that the order bookkeeping reuses are reached with
`open private` (Batteries; precedent `Induction/DuhamelII.lean:42`) instead of being copied.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedDecidableInType false

open private BAWeightOp_ext4 BAWeightOp_ext4_ge BAWeightOp_val2 BAWeightOp_val4 BAWeightOp_sd
  BAWeightOp_edgePoly0 BAWeightOp_rename_edgePoly0 BAWeightOp_val_tame BAWeightOp_ext_normal
  BAWeightOp_ext4_counters BAWeightOp_ext4_atoms BAWeightOp_ext2_cnt BAWeightOp_nA_le BAWeightOp_nA_lt
  BAWeightOp_cnt BAWeightOp_mono_aux BAWeightOp_packMerge_counters BAWeightOp_split3 BAWeightOp_core4
  BAWeightOp_ext_atomAdj BAWeightOp_ext_adj BAWeightOp_ext4_nM BAWeightOp_nExt_add_nA
  from RBM3D.Graph.BAWeightOp

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green RBM.BA

/-! ## 1. Target 1: the term lists (verbatim from the T2395 probe) -/

section Ops
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- **`GGGamma`** with the D402 coefficient (`B:393-405`, probe `t/T2387` 328-339, L2c2) at `p = Ǧ_{xy}`, `q = Ǧ_{y'x}` (`q ∈ lwSplit p.2`): `gg2` is the
first two sums (`M⁺S⁺ = W - 1`, `u, β = bpv 0, 1`) and the third sum with `W = 1` (`α, β = bpv 0, 1`), `gg4` the third sum with `W - 1` (`u, w, α, β = bpv 0..3`). -/
def BAGraph.gg2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (BAGraph E (I ⊕ Fin 2)) :=
  let x := owxEmb 2 p.1.src; let y := owxEmb 2 p.1.dst; let y' := owxEmb 2 q.1.src
  let w1 : List (WEdge (E ⊕ (I ⊕ Fin 2))) := [bpW true (bpv 0) (bpv 1)]
  let d1 : List (BAMEdge (E ⊕ (I ⊕ Fin 2))) := [bpM x (bpv 0), bpM (bpv 0) x]
  let w3 : List (WEdge (E ⊕ (I ⊕ Fin 2))) := [bpW false (bpv 0) (bpv 1)]
  [BAGraph.ext 2 Γ q.2 [] w1 (d1 ++ [bpM (bpv 1) y, bpM y' (bpv 1)]),
   BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) y] w1 (d1 ++ [bpM y' (bpv 1)]),
   BAGraph.ext 2 Γ q.2 [bpS true y' (bpv 1)] w1 (d1 ++ [bpM (bpv 1) y]),
   BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) y, bpS true y' x] w3 [bpM x (bpv 0)],
   BAGraph.ext 2 Γ q.2 [bpS true (bpv 0) x, bpS false (bpv 1) y, bpS false y' (bpv 1)] w3 [bpM x (bpv 0)]] ++
  (lwSplit q.2).map fun r => BAGraph.ext 2 Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
    (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) y, bpS true y' x] w3 [bpM x (bpv 0)]
def BAGraph.gg4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (BAGraph E (I ⊕ Fin 4)) :=
  let x := owxEmb 4 p.1.src; let y := owxEmb 4 p.1.dst; let y' := owxEmb 4 q.1.src
  let w : List (WEdge (E ⊕ (I ⊕ Fin 4))) := [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
  let md : List (BAMEdge (E ⊕ (I ⊕ Fin 4))) := [bpM x (bpv 0), bpM (bpv 0) x, bpM (bpv 1) (bpv 2)]
  [BAGraph.ext 4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) y, bpS true y' (bpv 1)] w md,
   BAGraph.ext 4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) y, bpS false y' (bpv 3)] w md] ++
  (lwSplit q.2).map fun r => BAGraph.ext 4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
    (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) y, bpS true y' (bpv 1)] w md
end Ops

/-! ## 2. The terms by name -/

section TermForms

variable {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} M_{βy} M_{y'β} f` (the first sum, `W - 1`). -/
private def BAGGOp_A1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1)]

/-- `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} Ǧ_{βy} M_{y'β} f`. -/
private def BAGGOp_A2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)]

/-- `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} M_{βy} Ǧ_{y'β} f`. -/
private def BAGGOp_A3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)]

/-- `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x} f` (the third sum, `W = 1`). -/
private def BAGGOp_A4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β} f`. -/
private def BAGGOp_A5 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS false (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- The derivative term of `gg2` for the solid edge `r.1` of `f`. -/
private def BAGGOp_AD (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
    (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
    bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- `Σ M_{xu} M_{ux} S⁺_{uw} M_{wα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'w} f` (the third sum, `W - 1`). -/
private def BAGGOp_B1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst),
      bpS true (owxEmb 4 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

/-- `Σ M_{xu} M_{ux} S⁺_{uw} M_{wα} S_{αβ} Ǧ_{αw} G_{βy} G_{y'β} f`. -/
private def BAGGOp_B2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst),
      bpS false (owxEmb 4 q.1.src) (bpv 3)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

/-- The derivative term of `gg4` for the solid edge `r.1` of `f`. -/
private def BAGGOp_BD (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
    (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst),
    bpS true (owxEmb 4 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

private theorem BAGGOp_gg2_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.gg2 p q = [BAGGOp_A1 Γ p q, BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q, BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++
      (lwSplit q.2).map (BAGGOp_AD Γ p q) := rfl

private theorem BAGGOp_gg4_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.gg4 p q = [BAGGOp_B1 Γ p q, BAGGOp_B2 Γ p q] ++ (lwSplit q.2).map (BAGGOp_BD Γ p q) := rfl


/-! ### The values of the terms at a labelling -/

private theorem BAGGOp_lab2_emb {E I : Type} {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (u β : ι) (v : E ⊕ I) :
    owxLab2 ℓe ℓi u β (owxEmb 2 v) = Sum.elim ℓe ℓi v := by rcases v <;> rfl

private theorem BAGGOp_lab4_emb {E I : Type} {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) (v : E ⊕ I) :
    BAWeightOp_lab4 ℓe ℓi z y α β (owxEmb 4 v) = Sum.elim ℓe ℓi v := by rcases v <;> rfl

/-- The term of a `k = 2` extension. -/
private theorem BAGGOp_ext2_term (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 2)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 2))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (D : BALData ι) (ℓe : E → ι) (ℓi : I → ι) (u β : ι) :
    (BAGraph.ext 2 Γ rest s w md).term D (owxLab2 ℓe ℓi u β) =
      ({ Γ with solid := rest } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        (s.map (SEdge.val D.toLData (owxLab2 ℓe ℓi u β))).prod *
        (w.map (WEdge.val D.toLData (owxLab2 ℓe ℓi u β))).prod *
        (md.map (BAMEdge.val D (owxLab2 ℓe ℓi u β))).prod := by
  rw [BAWeightOp_ext_term, BAExpandW_lab2_emb]

/-- The term of a `k = 4` extension. -/
private theorem BAGGOp_ext4_term (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (w : List (WEdge (E ⊕ (I ⊕ Fin 4))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin 4)))) (D : BALData ι) (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) :
    (BAGraph.ext 4 Γ rest s w md).term D (BAWeightOp_lab4 ℓe ℓi z y α β) =
      ({ Γ with solid := rest } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        (s.map (SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z y α β))).prod *
        (w.map (WEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z y α β))).prod *
        (md.map (BAMEdge.val D (BAWeightOp_lab4 ℓe ℓi z y α β))).prod := by
  rw [BAWeightOp_ext_term, BAWeightOp_lab4_emb]

private theorem BAGGOp_bpS_val {V : Type} (D : BALData ι) (ℓ : V → ι) (c : Bool) (a b : V) :
    SEdge.val D.toLData ℓ (bpS c a b) = D.G (ℓ a) (ℓ b) - (if c then D.M (ℓ a) (ℓ b) else 0) := by
  cases c <;> simp [SEdge.val, bpS]

private theorem BAGGOp_bpWt_val {V : Type} (D : BALData ι) (ℓ : V → ι) (a b : V) :
    WEdge.val D.toLData ℓ (bpW true a b) = D.Sp (ℓ a) (ℓ b) := by
  simp [WEdge.val, bpW]

private theorem BAGGOp_bpWf_val {V : Type} (D : BALData ι) (ℓ : V → ι) (a b : V) :
    WEdge.val D.toLData ℓ (bpW false a b) = D.S (ℓ a) (ℓ b) := by
  simp [WEdge.val, bpW]

private theorem BAGGOp_bpM_val {V : Type} (D : BALData ι) (ℓ : V → ι) (a b : V) :
    BAMEdge.val D ℓ (bpM a b) = D.M (ℓ a) (ℓ b) := by
  simp [BAMEdge.val, bpM]

private theorem BAGGOp_A1_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (u β : ι) :
    (BAGGOp_A1 Γ p q).term D (owxLab2 ℓe ℓi u β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        (D.Sp u β * (D.M (Sum.elim ℓe ℓi p.1.src) u * D.M u (Sum.elim ℓe ℓi p.1.src) *
          D.M β (Sum.elim ℓe ℓi p.1.dst) * D.M (Sum.elim ℓe ℓi q.1.src) β)) := by
  have e0 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 0)) = u := rfl
  have e1 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAGGOp_A1, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1]
  ring


private theorem BAGGOp_A2_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (u β : ι) :
    (BAGGOp_A2 Γ p q).term D (owxLab2 ℓe ℓi u β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G β (Sum.elim ℓe ℓi p.1.dst) - D.M β (Sum.elim ℓe ℓi p.1.dst)) * D.Sp u β *
          (D.M (Sum.elim ℓe ℓi p.1.src) u * D.M u (Sum.elim ℓe ℓi p.1.src) * D.M (Sum.elim ℓe ℓi q.1.src) β)) := by
  have e0 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 0)) = u := rfl
  have e1 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAGGOp_A2, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1, ite_true]
  ring

private theorem BAGGOp_A3_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (u β : ι) :
    (BAGGOp_A3 Γ p q).term D (owxLab2 ℓe ℓi u β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G (Sum.elim ℓe ℓi q.1.src) β - D.M (Sum.elim ℓe ℓi q.1.src) β) * D.Sp u β *
          (D.M (Sum.elim ℓe ℓi p.1.src) u * D.M u (Sum.elim ℓe ℓi p.1.src) * D.M β (Sum.elim ℓe ℓi p.1.dst))) := by
  have e0 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 0)) = u := rfl
  have e1 : owxLab2 ℓe ℓi u β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAGGOp_A3, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1, ite_true]
  ring

private theorem BAGGOp_A4_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    (BAGGOp_A4 Γ p q).term D (owxLab2 ℓe ℓi α β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G β β - D.M β β) * D.G α (Sum.elim ℓe ℓi p.1.dst) *
          (D.G (Sum.elim ℓe ℓi q.1.src) (Sum.elim ℓe ℓi p.1.src) - D.M (Sum.elim ℓe ℓi q.1.src) (Sum.elim ℓe ℓi p.1.src)) *
          D.S α β * D.M (Sum.elim ℓe ℓi p.1.src) α) := by
  have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
  have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAGGOp_A4, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  ring

private theorem BAGGOp_A5_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    (BAGGOp_A5 Γ p q).term D (owxLab2 ℓe ℓi α β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G α (Sum.elim ℓe ℓi p.1.src) - D.M α (Sum.elim ℓe ℓi p.1.src)) * D.G β (Sum.elim ℓe ℓi p.1.dst) *
          D.G (Sum.elim ℓe ℓi q.1.src) β * D.S α β * D.M (Sum.elim ℓe ℓi p.1.src) α) := by
  have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
  have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAGGOp_A5, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  ring

private theorem BAGGOp_AD_term (Γ : BAGraph E I) (p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    (BAGGOp_AD Γ p q r).term D (owxLab2 ℓe ℓi α β) =
      ({ Γ with solid := r.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((if r.1.σ then D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst)
          else star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst))) *
          D.G β (Sum.elim ℓe ℓi p.1.dst) *
          (D.G (Sum.elim ℓe ℓi q.1.src) (Sum.elim ℓe ℓi p.1.src) - D.M (Sum.elim ℓe ℓi q.1.src) (Sum.elim ℓe ℓi p.1.src)) *
          D.S α β * D.M (Sum.elim ℓe ℓi p.1.src) α) := by
  have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
  have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
  have h : SEdge.val D.toLData (owxLab2 ℓe ℓi α β) (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1 *
      SEdge.val D.toLData (owxLab2 ℓe ℓi α β) (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2 =
      if r.1.σ then D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst)
        else star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, BAGGOp_lab2_emb, bpv, e0, e1]
  rw [BAGGOp_AD, BAGGOp_ext2_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc (SEdge.val D.toLData (owxLab2 ℓe ℓi α β) _), h]
  simp only [BAGGOp_bpS_val, BAGGOp_bpWt_val, BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab2_emb, e0, e1, ite_true,
    Bool.false_eq_true, ite_false, sub_zero]
  split_ifs <;> ring

private theorem BAGGOp_B1_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (z w α β : ι) :
    (BAGGOp_B1 Γ p q).term D (BAWeightOp_lab4 ℓe ℓi z w α β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G β β - D.M β β) * D.G α (Sum.elim ℓe ℓi p.1.dst) * (D.G (Sum.elim ℓe ℓi q.1.src) w - D.M (Sum.elim ℓe ℓi q.1.src) w) *
          (D.Sp z w * D.S α β) * (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M w α)) := by
  have e0 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 0)) = z := rfl
  have e1 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 1)) = w := rfl
  have e2 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 2)) = α := rfl
  have e3 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 3)) = β := rfl
  rw [BAGGOp_B1, BAGGOp_ext4_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab4_emb, e0, e1, e2, e3, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  ring

private theorem BAGGOp_B2_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (z w α β : ι) :
    (BAGGOp_B2 Γ p q).term D (BAWeightOp_lab4 ℓe ℓi z w α β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G α w - D.M α w) * D.G β (Sum.elim ℓe ℓi p.1.dst) * D.G (Sum.elim ℓe ℓi q.1.src) β *
          (D.Sp z w * D.S α β) * (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M w α)) := by
  have e0 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 0)) = z := rfl
  have e1 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 1)) = w := rfl
  have e2 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 2)) = α := rfl
  have e3 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 3)) = β := rfl
  rw [BAGGOp_B2, BAGGOp_ext4_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, BAGGOp_bpS_val, BAGGOp_bpWt_val,
    BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab4_emb, e0, e1, e2, e3, ite_true, Bool.false_eq_true, ite_false, sub_zero]
  ring

private theorem BAGGOp_BD_term (Γ : BAGraph E I) (p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (z w α β : ι) :
    (BAGGOp_BD Γ p q r).term D (BAWeightOp_lab4 ℓe ℓi z w α β) =
      ({ Γ with solid := r.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((if r.1.σ then D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst)
          else star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst))) *
          D.G β (Sum.elim ℓe ℓi p.1.dst) * (D.G (Sum.elim ℓe ℓi q.1.src) w - D.M (Sum.elim ℓe ℓi q.1.src) w) *
          (D.Sp z w * D.S α β) * (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M w α)) := by
  have e0 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 0)) = z := rfl
  have e1 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 1)) = w := rfl
  have e2 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 2)) = α := rfl
  have e3 : BAWeightOp_lab4 ℓe ℓi z w α β (Sum.inr (Sum.inr 3)) = β := rfl
  have h : SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z w α β) (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1 *
      SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z w α β) (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2 =
      if r.1.σ then D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst)
        else star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, BAGGOp_lab4_emb, bpv, e2, e3]
  rw [BAGGOp_BD, BAGGOp_ext4_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc (SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z w α β) _), h]
  simp only [BAGGOp_bpS_val, BAGGOp_bpWt_val, BAGGOp_bpWf_val, BAGGOp_bpM_val, bpv, BAGGOp_lab4_emb, e0, e1, e2, e3,
    ite_true, Bool.false_eq_true, ite_false, sub_zero]
  split_ifs <;> ring


section Alg

private theorem BAGGOp_alg {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℂ) (x : ι) (M Sp : ι → ι → ℂ)
    (Wm : Matrix ι ι ℂ) (hW : ∀ a b, Wm a b = (if a = b then 1 else 0) + ∑ z, M a z * M z a * Sp z b)
    (H : ι → ℂ) (Θ : ι → ι → ι → ℂ) :
    ∑ a, ∑ b, (K * ((M x a * M a x * Sp a b) * H b) + K * Θ x a b) +
      ∑ z, ∑ w, ∑ a, ∑ b, K * ((M x z * M z x * Sp z w) * Θ w a b) =
    K * (∑ b, (Wm - 1) x b * H b + ∑ w, ∑ a, ∑ b, Wm x w * Θ w a b) := by
  set W1 : ι → ℂ := fun b => ∑ a, M x a * M a x * Sp a b with hW1
  have hWm : ∀ w, Wm x w = (if x = w then 1 else 0) + W1 w := fun w => hW x w
  have hWm1 : ∀ b, (Wm - 1) x b = W1 b := by
    intro b
    rw [Matrix.sub_apply, Matrix.one_apply, hWm b]
    ring
  have e1 : ∑ a, ∑ b, (K * ((M x a * M a x * Sp a b) * H b) + K * Θ x a b) =
      K * ∑ b, W1 b * H b + K * ∑ a, ∑ b, Θ x a b := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    simp only [hW1, Finset.sum_mul]
  have e2 : ∑ z, ∑ w, ∑ a, ∑ b, K * ((M x z * M z x * Sp z w) * Θ w a b) =
      K * ∑ w, ∑ a, ∑ b, W1 w * Θ w a b := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_comm]
    simp only [hW1, Finset.sum_mul, ← Finset.mul_sum]
  have e3 : ∑ w, ∑ a, ∑ b, Wm x w * Θ w a b =
      ∑ a, ∑ b, Θ x a b + ∑ w, ∑ a, ∑ b, W1 w * Θ w a b := by
    have e3a : ∑ w, ∑ a, ∑ b, (if x = w then (1 : ℂ) else 0) * Θ w a b = ∑ a, ∑ b, Θ x a b := by
      rw [Finset.sum_eq_single x (fun w _ hw => by simp [Ne.symm hw]) (by simp)]
      simp
    simp only [hWm, add_mul, Finset.sum_add_distrib, e3a]
  simp only [hWm1, e1, e2, e3]
  ring

end Alg

section Pathwise

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integrand of the right side of `baExpFrame_gg` at the labelling `(ℓe, ℓi)` of the old vertices: the sum over the
labels of the new vertices of the terms of `gg2` and `gg4`. -/
private def BAGGOp_R (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι) (ℓe : E → ι)
    (ℓi : I → ι) : ℂ :=
  ∑ α, ∑ β, ((Γ.gg2 p q).map fun T => T.term D (owxLab2 ℓe ℓi α β)).sum +
    ∑ z, ∑ y, ∑ α, ∑ β, ((Γ.gg4 p q).map fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z y α β)).sum

/-- **The pathwise form of `GGGamma`**: the terms of `gg2` and `gg4` sum to `K` times the right side of `(B.20)` (D402 coefficient)
with `f` and `∂f` read off the edges of `q.2`. -/
private theorem BAGGOp_pathwise (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (Wm : Matrix ι ι ℂ) (hW : ∀ a b, Wm a b = (if a = b then 1 else 0) + ∑ z, D.M a z * D.M z a * D.Sp z b)
    (ℓe : E → ι) (ℓi : I → ι) (K f : ℂ) (df : ι → ι → ℂ)
    (hK : ∀ s : List (SEdge (E ⊕ I)), ({ Γ with solid := s } : BAGraph E I).term D (Sum.elim ℓe ℓi) =
      K * (s.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
    (hf : (q.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod = f)
    (hdf : ∀ β α, df β α = ((lwSplit q.2).map fun r =>
      (if r.1.σ then -(D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst))
        else -(star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst)))) *
      (r.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod).sum) :
    BAGGOp_R Γ p q D ℓe ℓi = K *
      (∑ β, (Wm - 1) (Sum.elim ℓe ℓi p.1.src) β * D.M β (Sum.elim ℓe ℓi p.1.dst) * D.M (Sum.elim ℓe ℓi q.1.src) β * f +
        ∑ β, (Wm - 1) (Sum.elim ℓe ℓi p.1.src) β *
          ((D.G β (Sum.elim ℓe ℓi p.1.dst) - D.M β (Sum.elim ℓe ℓi p.1.dst)) * D.M (Sum.elim ℓe ℓi q.1.src) β +
            D.M β (Sum.elim ℓe ℓi p.1.dst) * (D.G (Sum.elim ℓe ℓi q.1.src) β - D.M (Sum.elim ℓe ℓi q.1.src) β)) * f +
        ∑ w, ∑ α, ∑ β, Wm (Sum.elim ℓe ℓi p.1.src) w * D.M w α * D.S α β *
          ((D.G β β - D.M β β) * D.G α (Sum.elim ℓe ℓi p.1.dst) *
              (D.G (Sum.elim ℓe ℓi q.1.src) w - D.M (Sum.elim ℓe ℓi q.1.src) w) * f +
            (D.G α w - D.M α w) * D.G β (Sum.elim ℓe ℓi p.1.dst) * D.G (Sum.elim ℓe ℓi q.1.src) β * f -
            D.G β (Sum.elim ℓe ℓi p.1.dst) * (D.G (Sum.elim ℓe ℓi q.1.src) w - D.M (Sum.elim ℓe ℓi q.1.src) w) * df β α)) := by
  -- the sum of the derivative terms over `r`
  have hD : ∀ (c : ℂ) (β α : ι) (F : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)) → ℂ),
      (∀ r ∈ lwSplit q.2, F r = c * (K * (r.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
        (if r.1.σ then D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst)
          else star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst))))) →
      ((lwSplit q.2).map F).sum = -(c * K * df β α) := by
    intro c β α F hF
    have h := owx_list_aux (lwSplit q.2) (c * K) (fun r =>
      (if r.1.σ then -(D.G (Sum.elim ℓe ℓi r.1.src) β * D.G α (Sum.elim ℓe ℓi r.1.dst))
        else -(star (D.G (Sum.elim ℓe ℓi r.1.src) α) * star (D.G β (Sum.elim ℓe ℓi r.1.dst)))) *
          (r.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
      F (fun r hr => by
        rw [hF r hr]
        by_cases hσ : r.1.σ <;> simp [hσ] <;> ring)
    rw [h, hdf β α]
  set X := Sum.elim ℓe ℓi p.1.src with hX
  set Y := Sum.elim ℓe ℓi p.1.dst with hY
  set Y' := Sum.elim ℓe ℓi q.1.src with hY'
  set H : ι → ℂ := fun b => (D.M b Y * D.M Y' b + ((D.G b Y - D.M b Y) * D.M Y' b +
    D.M b Y * (D.G Y' b - D.M Y' b))) * f with hH
  set Θ : ι → ι → ι → ℂ := fun w a b => D.M w a * D.S a b * ((D.G b b - D.M b b) * D.G a Y *
    (D.G Y' w - D.M Y' w) * f + (D.G a w - D.M a w) * D.G b Y * D.G Y' b * f -
    D.G b Y * (D.G Y' w - D.M Y' w) * df b a) with hΘ
  have h2 : ∀ a b, ((Γ.gg2 p q).map fun T => T.term D (owxLab2 ℓe ℓi a b)).sum =
      K * ((D.M X a * D.M a X * D.Sp a b) * H b) + K * Θ X a b := by
    intro a b
    have hder : (((lwSplit q.2).map (BAGGOp_AD Γ p q)).map fun T => T.term D (owxLab2 ℓe ℓi a b)).sum =
        -(D.G b Y * (D.G Y' X - D.M Y' X) * D.S a b * D.M X a * K * df b a) := by
      rw [List.map_map]
      refine hD (D.G b Y * (D.G Y' X - D.M Y' X) * D.S a b * D.M X a) b a _ (fun r hr => ?_)
      simp only [Function.comp_apply]
      rw [BAGGOp_AD_term, hK]
      ring
    rw [BAGGOp_gg2_eq]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hder,
      BAGGOp_A1_term, BAGGOp_A2_term, BAGGOp_A3_term, BAGGOp_A4_term, BAGGOp_A5_term, hK, hf, hH, hΘ]
    ring
  have h4 : ∀ z w a b, ((Γ.gg4 p q).map fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z w a b)).sum =
      K * ((D.M X z * D.M z X * D.Sp z w) * Θ w a b) := by
    intro z w a b
    have hder : (((lwSplit q.2).map (BAGGOp_BD Γ p q)).map fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z w a b)).sum =
        -(D.G b Y * (D.G Y' w - D.M Y' w) * (D.Sp z w * D.S a b) * (D.M X z * D.M z X * D.M w a) * K * df b a) := by
      rw [List.map_map]
      refine hD (D.G b Y * (D.G Y' w - D.M Y' w) * (D.Sp z w * D.S a b) * (D.M X z * D.M z X * D.M w a)) b a _
        (fun r hr => ?_)
      simp only [Function.comp_apply]
      rw [BAGGOp_BD_term, hK]
      ring
    rw [BAGGOp_gg4_eq]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hder,
      BAGGOp_B1_term, BAGGOp_B2_term, hK, hf, hΘ]
    ring
  have key := BAGGOp_alg K X D.M D.Sp Wm hW H Θ
  unfold BAGGOp_R
  simp only [h2, h4]
  rw [key]
  congr 1
  congr 1
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hH]
    ring
  · refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hΘ]
    ring

end Pathwise

end TermForms

/-! ## 3. Target 2: the value identity -/

section Core

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro `bwo_tame` of `Graph/BAWeightOp.lean`). -/
local macro "bgo_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply BAExpand_tame_baG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply lwStein_tame_hflow
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- **One labelling of the old vertices** (the BA twin of `BAWeightOp_core` for `GGGamma`): for the circled blue edges
`p.1 = Ǧ_{xy}`, `q.1 = Ǧ_{y'x}` (`p.1.src = q.1.dst`), `𝔼 Γ.term` at the labelling `(ℓe, ℓi)` is the expectation of the sum, over
the labels of the new vertices, of the terms of `gg2` and `gg4` (`BAGGOp_R`), on the sequence space.  From `baGGGamma_holds`
through `lwWx_integral`; the pathwise identity is `BAGGOp_pathwise`. -/
private theorem BAGGOp_core (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht : 0 < t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]
    (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hσp : p.1.σ = true) (hcp : p.1.circ = true) (hσq : q.1.σ = true) (hcq : q.1.circ = true)
    (hxy : p.1.src = q.1.dst) (ℓe : Ex → Idx d L W) (ℓi : Ix → Idx d L W) :
    Integrable (fun ω' => BAGGOp_R Γ p q (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi)
        (Sizes.seqP (lwWxSizes d L W 0 hL)) ∧
      ∫ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi) ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
        ∫ ω', BAGGOp_R Γ p q (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
  classical
  have hm : 0 < m.im := hSelf.1
  have hz : (ztOf m E t).im ≠ 0 := by
    rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
  have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
  obtain ⟨x, hx⟩ : ∃ x : Idx d L W, Sum.elim ℓe ℓi p.1.src = x := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Idx d L W, Sum.elim ℓe ℓi p.1.dst = y := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : Idx d L W, Sum.elim ℓe ℓi q.1.src = y' := ⟨_, rfl⟩
  have hqd : Sum.elim ℓe ℓi q.1.dst = x := by rw [← hxy]; exact hx
  set K : ℂ := BAExpandW_K Γ (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t))
    (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) ((g0 : ℂ) • PsiI d L W) (Sum.elim ℓe ℓi) with hK
  set P0 : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
    (q.2.map (BAWeightOp_edgePoly0 (BAlwM d L W g0 E m) (Sum.elim ℓe ℓi))).prod with hP0
  have hP0r : lwWxRename d L W P0 = (q.2.map (owxEdgePoly (lwWxSizes d L W 0 hL) 0 (BAlwM d L W g0 E m)
      (Sum.elim ℓe ℓi))).prod := by
    rw [hP0, map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun e _ => BAWeightOp_rename_edgePoly0 hL _ _ e
  have hf : ∀ ω', baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' =
      (q.2.map (SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi))).prod := fun ω' => by
    rw [hP0r]; exact BAExpandW_baPoly_edgePoly_prod _ q.2 ω'
  have hP1 : Tame1 (lwWxSizes d L W 0 hL) 0
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) :=
    baPoly_tame1 hz g0 t _
  have tf : Tame (lwWxSizes d L W 0 hL) (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) :=
    hP1.tame
  have tD : ∀ α β : Idx d L W, Tame (lwWxSizes d L W 0 hL)
      (dhSample (lwWxSizes d L W 0 hL) 0 t α β (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0))) :=
    fun α β => lwStein_tame_dhSample hP1 t α β
  have tG : ∀ i j : Idx d L W, Tame (lwWxSizes d L W 0 hL) (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t i j) :=
    fun i j => BAExpand_tame_baG (lwWxSizes d L W 0 hL) 0 hz g0 t i j
  -- the two integrands on the sequence space
  set FL : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ := fun ω' =>
    (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t y' x ω' - BAlwM d L W g0 E m y' x) *
      (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t x y ω' - BAlwM d L W g0 E m x y) *
      baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' with hFL
  set FR : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ := fun ω' =>
    ∑ β, (BAlwW d L W g0 E t m - 1) x β * BAlwM d L W g0 E m β y * BAlwM d L W g0 E m y' β *
        baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' +
      ∑ β, (BAlwW d L W g0 E t m - 1) x β *
        ((baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β y ω' - BAlwM d L W g0 E m β y) * BAlwM d L W g0 E m y' β +
          BAlwM d L W g0 E m β y * (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t y' β ω' - BAlwM d L W g0 E m y' β)) *
        baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' +
      ∑ w, ∑ α, ∑ β, BAlwW d L W g0 E t m x w * BAlwM d L W g0 E m w α * BAlwS d L W t α β *
        ((baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β β ω' - BAlwM d L W g0 E m β β) *
            baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t α y ω' *
            (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t y' w ω' - BAlwM d L W g0 E m y' w) *
            baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' +
          (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t α w ω' - BAlwM d L W g0 E m α w) *
            baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β y ω' *
            baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t y' β ω' *
            baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' -
          baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β y ω' *
            (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t y' w ω' - BAlwM d L W g0 E m y' w) *
            dhSample (lwWxSizes d L W 0 hL) 0 t β α
              (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω') with hFR
  have tFL : Tame (lwWxSizes d L W 0 hL) FL := by
    rw [hFL]; bgo_tame
  have tFR : Tame (lwWxSizes d L W 0 hL) FR := by
    rw [hFR]; bgo_tame
  -- the pointwise relations
  have hw : ∀ (e : SEdge (Ex ⊕ Ix)), e.σ = true → e.circ = true → ∀ ω',
      SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) e =
        baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (Sum.elim ℓe ℓi e.src) (Sum.elim ℓe ℓi e.dst) ω' -
          BAlwM d L W g0 E m (Sum.elim ℓe ℓi e.src) (Sum.elim ℓe ℓi e.dst) := by
    intro e he hc ω'
    rw [BAExpandW_sedge_val_blue e he _ ω', hc]
    simp
  have hΓ : ∀ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi) = K * FL ω' := by
    intro ω'
    rw [BAExpandW_term_eq, lwSplit_prod Γ.solid _ p hp, lwSplit_prod p.2 _ q hq, hw p.1 hσp hcp ω',
      hw q.1 hσq hcq ω', hx, hy, hqd, hy']
    simp only [hFL]
    rw [hf ω']
    ring
  have hKs : ∀ s : List (SEdge (Ex ⊕ Ix)), BAExpandW_K ({ Γ with solid := s } : BAGraph Ex Ix)
      (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t)) (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m)
      ((g0 : ℂ) • PsiI d L W) (Sum.elim ℓe ℓi) = K := fun s => rfl
  have hsedge : ∀ e : SEdge (Ex ⊕ Ix), Tame1 (lwWxSizes d L W 0 hL) 0
      (fun ω' => SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) e) := fun e =>
    BAExpandW_sedge_val_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) (g0 := g0) (z := ztOf m E t) (u := t)
      (M := BAlwM d L W g0 E m) (S := Matrix.of (BAlwS d L W t))
      (Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (gPsi := (g0 : ℂ) • PsiI d L W) hz e _
  have hdh : ∀ (α w : Idx d L W) ω', dhSample (lwWxSizes d L W 0 hL) 0 t α w
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω' =
      ((lwSplit q.2).map fun r =>
        (if r.1.σ then -((BAWeightOp_sd hL g0 E t m ω').G (Sum.elim ℓe ℓi r.1.src) α *
            (BAWeightOp_sd hL g0 E t m ω').G w (Sum.elim ℓe ℓi r.1.dst))
          else -(star ((BAWeightOp_sd hL g0 E t m ω').G (Sum.elim ℓe ℓi r.1.src) w) *
            star ((BAWeightOp_sd hL g0 E t m ω').G α (Sum.elim ℓe ℓi r.1.dst)))) *
        (r.2.map (SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi))).prod).sum := by
    intro α w ω'
    have hfun : baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) = fun ω' =>
        (q.2.map fun a => SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) a).prod := funext hf
    rw [hfun, lwStein_dh_listProd q.2 (fun e _ => hsedge e)]
    congr 1
    refine List.map_congr_left fun r _ => ?_
    rw [BAExpandW_dh_sedge_val hz ht r.1 α w (Sum.elim ℓe ℓi) ω']
    rfl
  have hR : ∀ ω', BAGGOp_R Γ p q (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi = K * FR ω' := by
    intro ω'
    have h := BAGGOp_pathwise Γ p q (BAWeightOp_sd hL g0 E t m ω') (BAlwW d L W g0 E t m)
      (fun a b => BAWeightOp_W_sub_one hL g0 E t m hSelf ht.le ht1 a b) ℓe ℓi K
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω')
      (fun β α => dhSample (lwWxSizes d L W 0 hL) 0 t β α
        (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω')
      (fun s => by rw [BAExpandW_term_eq, hKs s]) (hf ω').symm
      (fun β α => hdh β α ω')
    rw [hx, hy, hy'] at h
    exact h
  -- transport to `PF` and `baGGGamma_holds`
  have hLint : ∫ ω, BAGGGammaL d L W g0 E t m P0 x y y' ω ∂(PF d L W 0) =
      ∫ ω', FL ω' ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    refine lwWx_integral hL tFL.cont fun ω' => ?_
    unfold BAGGGammaL BAlwGc
    rw [hFL, ← baWx_baPoly hL g0 E t m ω' P0]
    rfl
  have hRint : ∫ ω, BAGGGammaR d L W g0 E t m P0 x y y' ω ∂(PF d L W 0) =
      ∫ ω', FR ω' ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    refine lwWx_integral hL tFR.cont fun ω' => ?_
    have hdf : ∀ β α : Idx d L W, BAlwdf d L W g0 E t m P0 (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') β α =
        dhSample (lwWxSizes d L W 0 hL) 0 t β α
          (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω' :=
      fun β α => (baWx_dh hL hz ht g0 β α ω' P0).symm
    unfold BAGGGammaR BAlwGc
    simp only [hdf, ← baWx_baPoly hL g0 E t m ω' P0]
    rw [hFR]
    rfl
  have key := baGGGamma_holds d L W hL g0 E t m hSelf ht.le ht1 P0 x y y'
  refine ⟨?_, ?_⟩
  · have : (fun ω' => BAGGOp_R Γ p q (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi) = fun ω' => K * FR ω' := funext hR
    rw [this]
    exact (Tame.integrable hG tFR).const_mul K
  · simp_rw [hΓ, hR]
    rw [integral_const_mul, integral_const_mul, ← hLint, ← hRint, key]

end Core

section Assembly

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The value of the two lists is the sum over the labels of the old internal vertices of `BAGGOp_R`. -/
private theorem BAGGOp_baSum_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) :
    baSum (Γ.gg2 p q) D ℓe + baSum (Γ.gg4 p q) D ℓe = ∑ ℓi : I → ι, BAGGOp_R Γ p q D ℓe ℓi := by
  unfold BAGGOp_R baSum
  rw [Finset.sum_add_distrib]
  congr 1
  · have e : ((Γ.gg2 p q).map fun T => T.val D ℓe) =
        (Γ.gg2 p q).map fun T => ∑ ℓi : I → ι, ∑ α, ∑ β, T.term D (owxLab2 ℓe ℓi α β) :=
      List.map_congr_left fun T _ => BAWeightOp_val2 T D ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := ι)]
  · have e : ((Γ.gg4 p q).map fun T => T.val D ℓe) =
        (Γ.gg4 p q).map fun T => ∑ ℓi : I → ι, ∑ z, ∑ y, ∑ α, ∑ β, T.term D (BAWeightOp_lab4 ℓe ℓi z y α β) :=
      List.map_congr_left fun T _ => BAWeightOp_val4 T D ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := ι)]

/-- At `S = 0` and `S⁺ = 0` every term of a generic extension with a blue waved edge vanishes. -/
private theorem BAGGOp_ext_term_zero (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (D : BALData ι) (hS : D.S = 0) (hSp : D.Sp = 0)
    (hw : ∃ e ∈ w, e.σ = true) (ℓ' : E ⊕ (I ⊕ Fin k) → ι) :
    (BAGraph.ext k Γ rest s w md).term D ℓ' = 0 := by
  obtain ⟨e, he, hσ⟩ := hw
  have h0 : WEdge.val D.toLData ℓ' e = 0 := by
    cases hc : e.col <;> simp [WEdge.val, hc, hσ, hS, hSp]
  rw [BAWeightOp_ext_term, List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)]
  simp

/-- At `S = 0`, `S⁺ = 0` the values of all terms of `gg2` and `gg4` vanish. -/
private theorem BAGGOp_baSum_zero (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (hS : D.S = 0) (hSp : D.Sp = 0) (ℓe : E → ι) :
    baSum (Γ.gg2 p q) D ℓe + baSum (Γ.gg4 p q) D ℓe = 0 := by
  have h2 : ∀ T ∈ Γ.gg2 p q, T.val D ℓe = 0 := by
    intro T hT
    have hT' : ∀ ℓ' : E ⊕ (I ⊕ Fin 2) → ι, T.term D ℓ' = 0 := by
      rw [BAGGOp_gg2_eq] at hT
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
      rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, _, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW false (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW false (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 2 Γ _ _ _ _ D hS hSp ⟨bpW false (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
    unfold BAGraph.val
    exact Finset.sum_eq_zero fun ℓi _ => hT' _
  have h4 : ∀ T ∈ Γ.gg4 p q, T.val D ℓe = 0 := by
    intro T hT
    have hT' : ∀ ℓ' : E ⊕ (I ⊕ Fin 4) → ι, T.term D ℓ' = 0 := by
      rw [BAGGOp_gg4_eq] at hT
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
      rcases hT with (rfl | rfl) | ⟨r, _, rfl⟩
      · exact BAGGOp_ext_term_zero 4 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 4 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · exact BAGGOp_ext_term_zero 4 Γ _ _ _ _ D hS hSp ⟨bpW true (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
    unfold BAGraph.val
    exact Finset.sum_eq_zero fun ℓi _ => hT' _
  have e2 : baSum (Γ.gg2 p q) D ℓe = 0 := List.sum_eq_zero fun a ha => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha
    exact h2 T hT
  have e4 : baSum (Γ.gg4 p q) D ℓe = 0 := List.sum_eq_zero fun a ha => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha
    exact h4 T hT
  rw [e2, e4, add_zero]

end Assembly

section Final

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **`GGGamma` as a graph operation on the sequence space.** -/
private theorem BAGGOp_val_seq (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht : 0 < t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]
    (Γ : BAGraph Ex Ix) (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) (hσp : p.1.σ = true) (hcp : p.1.circ = true) (hσq : q.1.σ = true)
    (hcq : q.1.circ = true) (hxy : p.1.src = q.1.dst) (ℓe : Ex → Idx d L W) :
    ∫ ω', Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
      ∫ ω', (baSum (Γ.gg2 p q) (BAWeightOp_sd hL g0 E t m ω') ℓe +
        baSum (Γ.gg4 p q) (BAWeightOp_sd hL g0 E t m ω') ℓe) ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
  classical
  have hm : 0 < m.im := hSelf.1
  have hz : (ztOf m E t).im ≠ 0 := by
    rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
  have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
  have hcore := fun ℓi => BAGGOp_core hL g0 E t m hSelf ht ht1 Γ p q hp hq hσp hcp hσq hcq hxy ℓe ℓi
  have hL1 : ∫ ω', Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
      ∑ ℓi : Ix → Idx d L W, ∫ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi)
        ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    unfold BAGraph.val
    exact integral_finsetSum _ fun ℓi _ =>
      Tame.integrable hG (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz Γ _).tame
  simp_rw [BAGGOp_baSum_eq]
  rw [hL1, integral_finsetSum _ fun ℓi _ => (hcore ℓi).1]
  exact Finset.sum_congr rfl fun ℓi _ => (hcore ℓi).2

/-- **Target 2: `GGGamma` (B.20, D402) as a graph operation** (`B:393-405`; the second conjunct of `BAexpFrameE`, probe
`t/T2395:RBM3D/Probe/T2395Pins.lean:244-251`): for circled blue `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2` with `p.1.src = q.1.dst`
(`p.1 = Ǧ_{xy}`, `q.1 = Ǧ_{y'x}`), `𝔼 Γ.val = 𝔼 (Σ_{Δ ∈ gg2} Δ.val + Σ_{Δ ∈ gg4} Δ.val)` at the model data `BAlwData` over
`PF d L W 0`.  For `0 < t < 1`: `baGGGamma_holds` with `W = 1 + M⁺ (S W)` (`BAWeightOp_W_sub_one`), on the sequence space and
transported by `lwWx_integral`; for `t = 0` both sides vanish (`Ǧ = 0`, `S = S⁺ = 0`). -/
theorem baExpFrame_gg (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ),
    RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
      (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = true → p.1.circ = true →
      q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst →
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 Em t m ω) ℓe
          ∂(PF d L W 0) := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 Ex Ix _ _ _ _ Γ ℓe p hp q hq hσp hcp hσq hcq hxy
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · -- `t = 0`: `Ǧ = 0` on the left, `S = S⁺ = 0` on the right
    have hSz0 : Matrix.of (BAlwS d L W 0) = (0 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
      ext i j
      simp [BAlwS]
    have hSz : ∀ ω, (BAlwData d L W g0 E 0 m ω).S = 0 := fun ω => hSz0
    have hSpz : ∀ ω, (BAlwData d L W g0 E 0 m ω).Sp = 0 := fun ω => by
      change Matrix.of (BAlwS d L W 0) * BAlwW d L W g0 E 0 m = 0
      rw [hSz0, zero_mul]
    have hR : ∀ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 E 0 m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 E 0 m ω) ℓe = 0 :=
      fun ω => BAGGOp_baSum_zero Γ p q _ (hSz ω) (hSpz ω) ℓe
    have hLz : ∀ ω, Γ.val (BAlwData d L W g0 E 0 m ω) ℓe = 0 := by
      intro ω
      unfold BAGraph.val
      refine Finset.sum_eq_zero fun ℓi _ => ?_
      have h0 : SEdge.val (BAlwData d L W g0 E 0 m ω).toLData (Sum.elim ℓe ℓi) p.1 = 0 := by
        have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 E m ω
          (Sum.elim ℓe ℓi p.1.src) (Sum.elim ℓe ℓi p.1.dst)
        simp only [SEdge.val, hσp, hcp, BAlwData, ite_true]
        simpa [BAlwGc] using this
      simp only [BAGraph.term, LGraph.term, lwSplit_prod Γ.solid _ p hp, h0]
      simp
    simp [hLz, hR]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    have key := BAGGOp_val_seq hL g0 E t m hSelf ht ht1 Γ p q hp hq hσp hcp hσq hcq hxy ℓe
    have hF1 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) =>
        Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe) :=
      (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz Γ ℓe).cont
    have hF2 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) =>
        baSum (Γ.gg2 p q) (BAWeightOp_sd hL g0 E t m ω') ℓe + baSum (Γ.gg4 p q) (BAWeightOp_sd hL g0 E t m ω') ℓe) :=
      (continuous_list_sum _ fun T _ =>
        (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓe).cont).add
        (continuous_list_sum _ fun T _ =>
          (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓe).cont)
    exact (lwWx_integral hL hF1 fun ω' => rfl).trans (key.trans (lwWx_integral hL hF2 fun ω' => rfl).symm)

end Final

/-! ## 4. Target 3: `BAexpFrameE` and `baExpFrameE_holds` -/

/-- L2c1, L2c2 consumed by L3a: the frame identities of `lem_lweight` at a self-loop (`lw2`, `lw4`) and of `GGGamma` at a pair (`gg2`, `gg4`),
as `lanlw_val` (`BAExpandW.lean:908`) for `lanlw`.  Verbatim from the T2395 probe (`t/T2395:RBM3D/Probe/T2395Pins.lean:244-251`). -/
def BAexpFrameE (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      (∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) ∧
      (∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = true → p.1.circ = true → q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- **Target 3: the frame identity**, for every `d`: `baExpFrame_lw` (the self-loop) and `baExpFrame_gg` (the pair). -/
theorem baExpFrameE_holds (d : ℕ) : BAexpFrameE d := fun L W _ _ hL g0 Em t m hS h0 h1 _ _ _ _ _ _ Γ ℓe =>
  ⟨fun p hp hσ hc hxx => baExpFrame_lw d L W hL g0 Em t m hS h0 h1 Γ ℓe p hp hσ hc hxx,
    fun p hp q hq hσp hcp hσq hcq hxy => baExpFrame_gg d L W hL g0 Em t m hS h0 h1 Γ ℓe p hp q hq hσp hcp hσq hcq hxy⟩

end RBM.Graph

end
