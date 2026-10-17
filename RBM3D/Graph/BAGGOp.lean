/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAWeightOp
import RBM3D.Graph.BAGGExp

/-!
# The GG expansion (B.20) as a graph operation and the frame identity

Paper: (B.20) `GGGamma` (Lemma B.11 of [yang2024Del]) with the coefficient
`(W - 1)_{xβ} = (M⁺S⁺)_{xβ}` in the first two sums.  `baGGGamma_holds` (`Graph/BAGGExp.lean`)
is the identity of expectations; this file is its graph form.

## Contents (namespace `RBM.Graph`, private prefix `BAGGOp_`)

1. **The term lists**: `BAGraph.gg2`, `BAGraph.gg4` (with `BAGraph.ext`, `bpv`, `bpS`, `bpM`,
   `bpW`, `baSum` of `Graph/BAWeightOp.lean`) and the named terms `BAGGOp_A1 … A5, AD, B1, B2, BD`.
2. **The value identity** (`baExpFrame_gg`, the second conjunct of `BAexpFrameE`):
   `𝔼 Γ.val = 𝔼 (baSum gg2 + baSum gg4)` at `BAlwData` over `PF d L W 0`, for circled blue
   `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2`, `p.1.src = q.1.dst`.  It follows from
   `baGGGamma_holds`, pathwise on the sequence space (`BAGGOp_pathwise`, `BAGGOp_core`) as
   `baExpFrame_lw` follows from `baLweight_holds`, and `t = 0` is trivial
   (`Ǧ = 0`, `S = S⁺ = 0`).
3. **The frame identity** `BAexpFrameE` and `baExpFrameE_holds : ∀ d, BAexpFrameE d`.
4. **Counters and order** (Section 5, the counters of `BAstepMono`): `gg_counters`, `gg_raw`,
   `gg_scalingOrderG`, `gg_mono`; the table at the head of Section 5 says which terms keep the
   order (`A1` with `κ = 0`) and which gain.

The private declarations of `Graph/BAWeightOp.lean` and `Graph/BAExpandWOrd.lean` that the order
bookkeeping reuses (`BAWeightOp_ext4_ge`, `BAExpandWOrd_ext_ge`, the closure lemmas, ...) are
reached with `open private` (Batteries; as in `Induction/DuhamelII.lean`), not copied.
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
  BAWeightOp_ext4_counters BAWeightOp_ext4_atoms BAWeightOp_ext2_cnt BAWeightOp_nA_le
  BAWeightOp_cnt BAWeightOp_mono_aux BAWeightOp_packMerge_counters BAWeightOp_split3
  BAWeightOp_ext_atomAdj BAWeightOp_ext_adj BAWeightOp_nExt_add_nA
  BAWeightOp_circ_counters BAWeightOp_emb_ne BAWeightOp_D4_split BAWeightOp_atomAdj_comm BAWeightOp_adj_comm
  BAWeightOp_self_mem_atom BAWeightOp_atom_eq_of_mem BAWeightOp_cnt_ext BAWeightOp_isRight_emb BAWeightOp_rtg_symm
  from RBM3D.Graph.BAWeightOp
open private BAExpandWOrd_ext BAExpandWOrd_ext_counters BAExpandWOrd_ext_ge BAExpandWOrd_D_split
  BAExpandWOrd_emb_ne_β from RBM3D.Graph.BAExpandWOrd

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green RBM.BA

/-! ## 1. The term lists -/

section Ops
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- **`GGGamma`** ((B.20), with the coefficient `W - 1 = M⁺S⁺`) at `p = Ǧ_{xy}`, `q = Ǧ_{y'x}` (`q ∈ lwSplit p.2`): `gg2` is the
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
def BAGGOp_A1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst),
      bpM (owxEmb 2 q.1.src) (bpv 1)]

/-- `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} Ǧ_{βy} M_{y'β} f`. -/
def BAGGOp_A2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (owxEmb 2 q.1.src) (bpv 1)]

/-- `Σ_{u,β} M_{xu} M_{ux} S⁺_{uβ} M_{βy} Ǧ_{y'β} f`. -/
def BAGGOp_A3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.src), bpM (bpv 1) (owxEmb 2 p.1.dst)]

/-- `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'x} f` (the third sum, `W = 1`). -/
def BAGGOp_A4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{αx} G_{βy} G_{y'β} f`. -/
def BAGGOp_A5 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ q.2 [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS false (owxEmb 2 q.1.src) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- The derivative term of `gg2` for the solid edge `r.1` of `f`. -/
def BAGGOp_AD (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
    (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
    bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- `Σ M_{xu} M_{ux} S⁺_{uw} M_{wα} S_{αβ} Ǧ_{ββ} G_{αy} Ǧ_{y'w} f` (the third sum, `W - 1`). -/
def BAGGOp_B1 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst),
      bpS true (owxEmb 4 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

/-- `Σ M_{xu} M_{ux} S⁺_{uw} M_{wα} S_{αβ} Ǧ_{αw} G_{βy} G_{y'β} f`. -/
def BAGGOp_B2 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst),
      bpS false (owxEmb 4 q.1.src) (bpv 3)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

/-- The derivative term of `gg4` for the solid edge `r.1` of `f`. -/
def BAGGOp_BD (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
    (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst),
    bpS true (owxEmb 4 q.1.src) (bpv 1)] [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

theorem BAGGOp_gg2_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.gg2 p q = [BAGGOp_A1 Γ p q, BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q, BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++
      (lwSplit q.2).map (BAGGOp_AD Γ p q) := rfl

theorem BAGGOp_gg4_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
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

/-- **The pathwise form of `GGGamma`**: the terms of `gg2` and `gg4` sum to `K` times the right side of (B.20) (coefficient `W - 1 = M⁺S⁺`)
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

/-! ## 3. The value identity -/

section Core

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Closure of `Tame` under the operations of the expansion (as the local macro `bwo_tame` of `Graph/BAWeightOp.lean`). -/
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

/-- **One labelling of the old vertices** (as `BAWeightOp_core`, for `GGGamma`): for the circled blue edges
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

/-- **`GGGamma` (B.20) as a graph operation** (the second conjunct of `BAexpFrameE`): for circled blue `p ∈ lwSplit Γ.solid`, `q ∈ lwSplit p.2` with `p.1.src = q.1.dst`
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

/-! ## 4. `BAexpFrameE` and `baExpFrameE_holds` -/

/-- The frame identities of `lem_lweight` at a self-loop (`lw2`, `lw4`) and of `GGGamma` at a pair (`gg2`, `gg4`),
as `lanlw_val` (`Graph/BAExpandW.lean`) for `lanlw`. -/
def BAexpFrameE (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix) (ℓe : Ex → Idx d L W),
      (∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst → ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)) ∧
      (∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, p.1.σ = true → p.1.circ = true → q.1.σ = true → q.1.circ = true → p.1.src = q.1.dst →
        ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
          ∫ ω, baSum (Γ.gg2 p q) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.gg4 p q) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0))

/-- **The frame identity**, for every `d`: `baExpFrame_lw` (the self-loop) and `baExpFrame_gg` (the pair). -/
theorem baExpFrameE_holds (d : ℕ) : BAexpFrameE d := fun L W _ _ hL g0 Em t m hS h0 h1 _ _ _ _ _ _ Γ ℓe =>
  ⟨fun p hp hσ hc hxx => baExpFrame_lw d L W hL g0 Em t m hS h0 h1 Γ ℓe p hp hσ hc hxx,
    fun p hp q hq hσp hcp hσq hcq hxy => baExpFrame_gg d L W hL g0 Em t m hS h0 h1 Γ ℓe p hp q hq hσp hcp hσq hcq hxy⟩

/-! ## 5. Counters and order of the terms

`T°` is `T` with every solid edge circled (`BAWeightOp_circ`); `raw = ord T° - ord Γ`.  The terms of `gg2`, `gg4` are:

| term | solid edges (circled / uncircled) | `Δ n_S` | `Δ n_W` | `Δ n_A` | raw `Δ ord` |
|---|---|---|---|---|---|
| `A1` (first sum, `W - 1`) | none new (`p.1`, `q.1` gone) | `-2` | `+1` | `-κ` | `2κ` |
| `A2`, `A3` (second sum) | `Ǧ_{βy}` / `Ǧ_{y'β}` | `-1` | `+1` | `0` | `+1` |
| `A4`, `A5`, `AD` (third sum, `W = 1`) | `A4`: `Ǧ_{y'x}` / `G_{αy}`; `A5`: `G_{βy}, G_{y'β}`; `AD`: three | `+1` | `+1` | `+1` | `+1` |
| `B1`, `B2`, `BD` (third sum, `W - 1`) | as `A4`, `A5`, `AD` | `+1` | `+2` | `+2` | `+1` |

with `κ = BAGGOp_kappa Γ y y' ∈ {0, 1}` (`y = p.1.dst`, `y' = q.1.src`): `κ = 0` iff the atoms of `y`, `y'` coincide or
both contain an external vertex. -/

section Order

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- From the partition: if every term of `G = Ǧ + M` of `T` is normal with `ord ≥ k`, then `k ≤ ordG T`. -/
private theorem BAGGOp_ordG_of_split {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (T : BAGraph E' I') (k : ℤ) (h : ∀ Δs ∈ T.splitG, Δs.Normal ∧ k ≤ ord Δs.counters) :
    ((k : ℤ) : WithTop ℤ) ≤ T.scalingOrderG := by
  rw [BAGraph.le_scalingOrderG_iff]
  intro P hP
  simp only [BAGraph.partition, List.mem_map] at hP
  obtain ⟨Δs, hΔs, rfl⟩ := hP
  obtain ⟨hNs, hge⟩ := h Δs hΔs
  change k ≤ ord Δs.packMerge.counters
  rw [BAWeightOp_packMerge_counters Δs hNs]
  exact hge

/-- Splitting after a trailing circled edge: the `M`-edges are those of the split of the list without it. -/
private theorem BAGGOp_split_snoc {V : Type*} (c : SEdge V) (hc : c.circ = true) :
    ∀ es : List (SEdge V), ∀ r ∈ baSplitSolid (es ++ [c]), ∃ r' ∈ baSplitSolid es, r.2 = r'.2 := by
  intro es
  induction es with
  | nil =>
    intro r hr
    simp [baSplitSolid, hc] at hr
    exact ⟨([], []), by simp [baSplitSolid], by simp [hr]⟩
  | cons e es ih =>
    intro r hr
    simp only [List.cons_append, baSplitSolid, List.mem_flatMap] at hr
    obtain ⟨r0, hr0, hr⟩ := hr
    obtain ⟨r0', hr0', h0⟩ := ih r0 hr0
    by_cases he : e.circ = true
    · simp only [he, ↓reduceIte, List.mem_singleton] at hr
      subst hr
      exact ⟨(e :: r0'.1, r0'.2), List.mem_flatMap.2 ⟨r0', hr0', by simp [he]⟩, by simp [h0]⟩
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨(SEdge.mk e.σ true e.src e.dst :: r0'.1, r0'.2), List.mem_flatMap.2 ⟨r0', hr0', by simp [he]⟩,
          by simp [h0]⟩
      · exact ⟨(r0'.1, BAMEdge.mk e.σ e.src e.dst :: r0'.2), List.mem_flatMap.2 ⟨r0', hr0', by simp [he]⟩,
          by simp [h0]⟩


/-! ### The `M`-splits of the new solid edges -/

/-- `A4`, `B1`: one non-circled edge, so at most one `M`-edge. -/
private theorem BAGGOp_hs_one {V : Type} (a b c : SEdge V) (ha : a.circ = true) (hb : b.circ = false)
    (hc : c.circ = true) : ∀ r ∈ baSplitSolid [a, b, c], r.2.length ≤ 1 := by
  intro r hr
  simp only [baSplitSolid, ha, hb, hc, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append] at hr
  rcases hr with rfl | rfl <;> simp

/-- `A5`, `B2`: a circled edge and two non-circled ones at `b`: at most two `M`-edges, and two of them contain one at `b`. -/
private theorem BAGGOp_hs_two {V : Type} (a e2 e3 : SEdge V) (ha : a.circ = true) (h2 : e2.circ = false)
    (h3 : e3.circ = false) (b : V) (hb2 : (e2.src = b ∧ e2.dst ≠ b) ∨ (e2.dst = b ∧ e2.src ≠ b)) :
    ∀ r ∈ baSplitSolid [a, e2, e3], r.2.length ≤ 1 ∨
      (r.2.length ≤ 3 ∧ ∃ m ∈ r.2, (m.x = b ∧ m.y ≠ b) ∨ (m.y = b ∧ m.x ≠ b)) := by
  intro r hr
  simp only [baSplitSolid, ha, h2, h3, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
    List.mem_nil_iff, or_false, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · left; simp
  · left; simp
  · left; simp
  · right
    refine ⟨by simp, _, List.mem_cons_self, ?_⟩
    simpa using hb2


/-! ### `A4`, `A5`, `AD` (the shape `BAExpandWOrd_ext`) and `B1`, `B2`, `BD` (the shape `BAWeightOp_ext4`) -/

private theorem BAGGOp_A4_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_A4 Γ p q = BAExpandWOrd_ext Γ q.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] p.1.src := rfl

private theorem BAGGOp_A5_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_A5 Γ p q = BAExpandWOrd_ext Γ q.2 [bpS true (bpv 0) (owxEmb 2 p.1.src), bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS false (owxEmb 2 q.1.src) (bpv 1)] p.1.src := rfl

private theorem BAGGOp_AD_eq (Γ : BAGraph E I) (p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_AD Γ p q r = BAExpandWOrd_ext Γ r.2 [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).1,
      (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) r.1)).2, bpS false (bpv 1) (owxEmb 2 p.1.dst),
      bpS true (owxEmb 2 q.1.src) (owxEmb 2 p.1.src)] p.1.src := rfl

private theorem BAGGOp_B1_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_B1 Γ p q = BAWeightOp_ext4 Γ q.2 [bpS true (bpv 3) (bpv 3), bpS false (bpv 2) (owxEmb 4 p.1.dst),
      bpS true (owxEmb 4 q.1.src) (bpv 1)] p.1.src := rfl

private theorem BAGGOp_B2_eq (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_B2 Γ p q = BAWeightOp_ext4 Γ q.2 [bpS true (bpv 2) (bpv 1), bpS false (bpv 3) (owxEmb 4 p.1.dst),
      bpS false (owxEmb 4 q.1.src) (bpv 3)] p.1.src := rfl

private theorem BAGGOp_BD_eq (Γ : BAGraph E I) (p q r : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGGOp_BD Γ p q r = BAWeightOp_ext4 Γ r.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).1,
      (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) r.1)).2, bpS false (bpv 3) (owxEmb 4 p.1.dst),
      bpS true (owxEmb 4 q.1.src) (bpv 1)] p.1.src := rfl

/-- The counters and the number of atoms of the terms of the third sum with `W = 1` (`A4`, `A5`, `AD`). -/
private theorem BAGGOp_tail2_cnt (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ [BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q),
      T.counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩ ∧
        BAWeightOp_cnt (fun _ => true) T.atom = BAWeightOp_cnt (fun _ => true) Γ.atom + 1 := by
  intro T hT
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
  · refine ⟨?_, BAWeightOp_ext2_cnt Γ q.2 _ _ p.1.src⟩
    rw [BAGGOp_A4_eq, BAExpandWOrd_ext_counters]
    have : q.2.length + 3 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]
  · refine ⟨?_, BAWeightOp_ext2_cnt Γ q.2 _ _ p.1.src⟩
    rw [BAGGOp_A5_eq, BAExpandWOrd_ext_counters]
    have : q.2.length + 3 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]
  · have hl'' := lwSplit_snd_length q.2 r hr
    refine ⟨?_, BAWeightOp_ext2_cnt Γ r.2 _ _ p.1.src⟩
    rw [BAGGOp_AD_eq, BAExpandWOrd_ext_counters]
    have : r.2.length + 4 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]

/-- The counters and the number of atoms of the terms of the third sum with `W - 1` (`B1`, `B2`, `BD`). -/
private theorem BAGGOp_tail4_cnt (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ Γ.gg4 p q, T.counters = ⟨Γ.nS + 1, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩ ∧
        BAWeightOp_cnt (fun _ => true) T.atom = BAWeightOp_cnt (fun _ => true) Γ.atom + 2 := by
  intro T hT
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  rw [BAGGOp_gg4_eq] at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
  · refine ⟨?_, (BAWeightOp_ext4_atoms Γ q.2 _ p.1.src).2⟩
    rw [BAGGOp_B1_eq, BAWeightOp_ext4_counters]
    have : q.2.length + 3 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]
  · refine ⟨?_, (BAWeightOp_ext4_atoms Γ q.2 _ p.1.src).2⟩
    rw [BAGGOp_B2_eq, BAWeightOp_ext4_counters]
    have : q.2.length + 3 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]
  · have hl'' := lwSplit_snd_length q.2 r hr
    refine ⟨?_, (BAWeightOp_ext4_atoms Γ r.2 _ p.1.src).2⟩
    rw [BAGGOp_BD_eq, BAWeightOp_ext4_counters]
    have : r.2.length + 4 = Γ.nS + 1 := by simp only [BAGraph.nS]; omega
    simp only [List.length_cons, List.length_nil, this]


/-- The `M`-splits of the new solid edges of `AD`: the three non-circled edges of the derivative term of `lanlw` and a trailing circled edge. -/
private theorem BAGGOp_hs_AD (q : SEdge (E ⊕ I)) (y : E ⊕ I) (c : SEdge (E ⊕ (I ⊕ Fin 2))) (hc : c.circ = true) :
    ∀ r ∈ baSplitSolid [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q)).1,
        (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q)).2, bpS false (bpv 1) (owxEmb 2 y), c],
      r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2, (m.x = bpv 1 ∧ m.y ≠ bpv 1) ∨ (m.y = bpv 1 ∧ m.x ≠ bpv 1)) := by
  intro r hr
  obtain ⟨r', hr', h⟩ := BAGGOp_split_snoc c hc [(owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q)).1,
    (owxDE (bpv 1) (bpv 0) (SEdge.map (owxEmb 2) q)).2, bpS false (bpv 1) (owxEmb 2 y)] r hr
  rw [h]
  exact BAExpandWOrd_D_split q y r' hr'

/-- The `M`-splits of the three non-circled edges of `BD` before its trailing edge (`BAWeightOp_D4_split` with `G_{βy}` for
`y` an old vertex in place of `G_{βz}`). -/
private theorem BAGGOp_D4_split (q : SEdge (E ⊕ I)) (y : E ⊕ I) :
    ∀ r ∈ baSplitSolid [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).1,
        (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).2, bpS false (bpv 3) (owxEmb 4 y)],
      r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2,
        (m.x = bpv 3 ∧ m.y ≠ bpv 3) ∨ (m.y = bpv 3 ∧ m.x ≠ (bpv 3 : E ⊕ (I ⊕ Fin 4)))) := by
  by_cases hσ : q.σ = true
  · have h : owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q) =
        (⟨true, false, owxEmb 4 q.src, bpv 3⟩, ⟨true, false, bpv 2, owxEmb 4 q.dst⟩) := by
      simp [owxDE, SEdge.map, hσ]
    rw [h]
    exact BAWeightOp_split3 _ _ _ rfl rfl rfl _ (Or.inl ⟨rfl, BAWeightOp_emb_ne _ _⟩)
      (Or.inl (Or.inr ⟨rfl, BAWeightOp_emb_ne _ _⟩))
  · have hσ' : q.σ = false := by simpa using hσ
    have h : owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q) =
        (⟨false, false, owxEmb 4 q.src, bpv 2⟩, ⟨false, false, bpv 3, owxEmb 4 q.dst⟩) := by
      simp [owxDE, SEdge.map, hσ']
    rw [h]
    exact BAWeightOp_split3 _ _ _ rfl rfl rfl _ (Or.inl ⟨rfl, BAWeightOp_emb_ne _ _⟩)
      (Or.inr (Or.inl ⟨rfl, BAWeightOp_emb_ne _ _⟩))

/-- The same for `BD` (`β = bpv 3`). -/
private theorem BAGGOp_hs_BD (q : SEdge (E ⊕ I)) (y : E ⊕ I) (c : SEdge (E ⊕ (I ⊕ Fin 4))) (hc : c.circ = true) :
    ∀ r ∈ baSplitSolid [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).1,
        (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).2, bpS false (bpv 3) (owxEmb 4 y), c],
      r.2.length ≤ 1 ∨ (r.2.length ≤ 3 ∧ ∃ m ∈ r.2, (m.x = bpv 3 ∧ m.y ≠ bpv 3) ∨ (m.y = bpv 3 ∧ m.x ≠ bpv 3)) := by
  intro r hr
  obtain ⟨r', hr', h⟩ := BAGGOp_split_snoc c hc [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).1,
    (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q)).2, bpS false (bpv 3) (owxEmb 4 y)] r hr
  rw [h]
  exact BAGGOp_D4_split q y r' hr'

/-- `ord Γ ≤ ordG T` for the terms of the third sum with `W = 1`. -/
private theorem BAGGOp_tail2_ge (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ [BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q),
      ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG := by
  intro T hT
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hcirc : ∀ e ∈ p.2, e.circ = true := fun e he =>
    hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _ he))
  have hcirc' : ∀ e ∈ q.2, e.circ = true := fun e he =>
    hcirc e ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
  · rw [BAGGOp_A4_eq]
    refine BAGGOp_ordG_of_split _ _ (BAExpandWOrd_ext_ge Γ hN q.2 _ p.1.src hcirc'
      (by simp only [BAGraph.nS]; simp; omega) fun r hr => Or.inl (BAGGOp_hs_one _ _ _ rfl rfl rfl r hr))
  · rw [BAGGOp_A5_eq]
    refine BAGGOp_ordG_of_split _ _ (BAExpandWOrd_ext_ge Γ hN q.2 _ p.1.src hcirc'
      (by simp only [BAGraph.nS]; simp; omega) fun r hr => ?_)
    exact BAGGOp_hs_two _ _ _ rfl rfl rfl (bpv 1) (Or.inl ⟨rfl, BAExpandWOrd_emb_ne_β _⟩) r hr
  · have hl'' := lwSplit_snd_length q.2 r hr
    have hcirc'' : ∀ e ∈ r.2, e.circ = true := fun e he =>
      hcirc' e ((lwSplit_perm q.2 r hr).mem_iff.2 (List.mem_cons_of_mem _ he))
    rw [BAGGOp_AD_eq]
    exact BAGGOp_ordG_of_split _ _ (BAExpandWOrd_ext_ge Γ hN r.2 _ p.1.src hcirc''
      (by simp only [BAGraph.nS]; simp; omega) (BAGGOp_hs_AD r.1 p.1.dst _ rfl))

/-- `ord Γ ≤ ordG T` for the terms of the third sum with `W - 1`. -/
private theorem BAGGOp_tail4_ge (Γ : BAGraph E I) (hN : Γ.Normal) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ∀ T ∈ Γ.gg4 p q, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG := by
  intro T hT
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hcirc : ∀ e ∈ p.2, e.circ = true := fun e he =>
    hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _ he))
  have hcirc' : ∀ e ∈ q.2, e.circ = true := fun e he =>
    hcirc e ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))
  rw [BAGGOp_gg4_eq] at hT
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
  rcases hT with (rfl | rfl) | ⟨r, hr, rfl⟩
  · rw [BAGGOp_B1_eq]
    refine BAGGOp_ordG_of_split _ _ (BAWeightOp_ext4_ge Γ hN q.2 _ p.1.src hcirc'
      (by simp only [BAGraph.nS]; simp; omega) fun r hr => Or.inl (BAGGOp_hs_one _ _ _ rfl rfl rfl r hr))
  · rw [BAGGOp_B2_eq]
    refine BAGGOp_ordG_of_split _ _ (BAWeightOp_ext4_ge Γ hN q.2 _ p.1.src hcirc'
      (by simp only [BAGraph.nS]; simp; omega) fun r hr => ?_)
    exact BAGGOp_hs_two _ _ _ rfl rfl rfl (bpv 3) (Or.inl ⟨rfl, BAWeightOp_emb_ne _ _⟩) r hr
  · have hl'' := lwSplit_snd_length q.2 r hr
    have hcirc'' : ∀ e ∈ r.2, e.circ = true := fun e he =>
      hcirc' e ((lwSplit_perm q.2 r hr).mem_iff.2 (List.mem_cons_of_mem _ he))
    rw [BAGGOp_BD_eq]
    exact BAGGOp_ordG_of_split _ _ (BAWeightOp_ext4_ge Γ hN r.2 _ p.1.src hcirc''
      (by simp only [BAGraph.nS]; simp; omega) (BAGGOp_hs_BD r.1 p.1.dst _ rfl))


/-! ### `A1`, `A2`, `A3`: two new vertices, each joined to an old one

The new vertices `u = bpv 0`, `β = bpv 1` of `A1`, `A2`, `A3` carry `M`-dotted edges to the old vertices `x` (for `u`) and `c`
(for `β`; `c = y'` in `A2`, `c = y` in `A1`, `A3`), and `A1` has one more edge `M_{y'β}`.  So the atoms of `T` are those of
`Γ'` (`Γ` itself for `A2`, `A3`; `Γ` with one more `M`-edge `M_{y'y}` for `A1`) with `u`, `β` attached: `n_A`, the number of
atoms are those of `Γ'`. -/

/-- The retraction of the vertices of a `k = 2` extension onto the old ones: `u ↦ x`, `β ↦ c`. -/
private def BAGGOp_rho2 (x c : E ⊕ I) : E ⊕ (I ⊕ Fin 2) → E ⊕ I
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr j) => if j = 0 then x else c

private theorem BAGGOp_rho2_emb (x c a : E ⊕ I) : BAGGOp_rho2 x c (owxEmb 2 a) = a := by
  rcases a with a | a <;> rfl

private theorem BAGGOp_rho2_u (x c : E ⊕ I) : BAGGOp_rho2 x c (bpv 0 : E ⊕ (I ⊕ Fin 2)) = x := rfl

private theorem BAGGOp_rho2_b (x c : E ⊕ I) : BAGGOp_rho2 x c (bpv 1 : E ⊕ (I ⊕ Fin 2)) = c := rfl

/-- The classes of an extension whose new vertices are joined to old ones: a vertex is joined to the old vertex `ρ w`. -/
private theorem BAGGOp_rtg_pend {V V' : Type*} (r : V → V → Bool) (r' : V' → V' → Bool)
    (hs' : ∀ u v, r' u v = r' v u) (emb : V → V') (ρ : V' → V)
    (e1 : ∀ u w, r u w = true → Relation.ReflTransGen (fun a b => r' a b = true) (emb u) (emb w))
    (e2 : ∀ b c, r' b c = true → ρ b = ρ c ∨ r (ρ b) (ρ c) = true)
    (e3 : ∀ w, Relation.ReflTransGen (fun a b => r' a b = true) w (emb (ρ w))) (v w : V') :
    Relation.ReflTransGen (fun a b => r' a b = true) v w ↔
      Relation.ReflTransGen (fun a b => r a b = true) (ρ v) (ρ w) := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      rcases e2 b c hbc with h | h
      · rw [← h]; exact ih
      · exact ih.tail h
  · intro h
    have h1 : ∀ a b, Relation.ReflTransGen (fun a b => r a b = true) a b →
        Relation.ReflTransGen (fun a b => r' a b = true) (emb a) (emb b) := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hbc ih => exact ih.trans (e1 _ _ hbc)
    exact (e3 v).trans ((h1 _ _ h).trans (BAWeightOp_rtg_symm r' hs' (e3 w)))

/-- **The atoms of an extension by two joined vertices**: `n_A` and the number of atoms are those of `Γ'`. -/
private theorem BAGGOp_pend (Γ' : BAGraph E I) (T : BAGraph E (I ⊕ Fin 2)) (x c : E ⊕ I)
    (e1 : ∀ u w, Γ'.atomAdj u w = true →
      Relation.ReflTransGen (fun a b => T.atomAdj a b = true) (owxEmb 2 u) (owxEmb 2 w))
    (e2 : ∀ b b', T.atomAdj b b' = true →
      BAGGOp_rho2 x c b = BAGGOp_rho2 x c b' ∨ Γ'.atomAdj (BAGGOp_rho2 x c b) (BAGGOp_rho2 x c b') = true)
    (e3 : ∀ w, Relation.ReflTransGen (fun a b => T.atomAdj a b = true) w (owxEmb 2 (BAGGOp_rho2 x c w))) :
    T.nA = Γ'.nA ∧ BAWeightOp_cnt (fun _ => true) T.atom = BAWeightOp_cnt (fun _ => true) Γ'.atom := by
  classical
  have hcl : ∀ v : E ⊕ (I ⊕ Fin 2), True → ∀ w, w ∈ T.atom v ↔
      w = v ∨ (True ∧ BAGGOp_rho2 x c w ∈ Γ'.atom (BAGGOp_rho2 x c v)) := by
    intro v _ w
    rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
    rw [BAGGOp_rtg_pend (fun a b => Γ'.atomAdj a b) (fun a b => T.atomAdj a b) (BAWeightOp_atomAdj_comm _)
      (owxEmb 2) (BAGGOp_rho2 x c) e1 e2 e3 v w]
    constructor
    · intro h; exact Or.inr ⟨trivial, h⟩
    · rintro (rfl | ⟨_, h⟩)
      · exact Relation.ReflTransGen.refl
      · exact h
  have hi2 : ∀ w : E ⊕ (I ⊕ Fin 2), (BAGGOp_rho2 x c w).isRight = true → w.isRight = true := by
    intro w h
    rcases w with e | i | j
    · exact absurd h (by simp [BAGGOp_rho2])
    · rfl
    · rfl
  refine ⟨?_, ?_⟩
  · have key := BAWeightOp_cnt_ext (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 2) => w.isRight) Γ'.atom T.atom
      (owxEmb 2) (BAGGOp_rho2 x c) (fun _ => True) 0 (BAGGOp_rho2_emb x c) BAWeightOp_isRight_emb hi2
      (fun _ => trivial) (BAWeightOp_self_mem_atom Γ') hcl (by simp) (fun v hv => absurd trivial hv)
      (fun v hv => absurd trivial hv)
    exact key
  · have key := BAWeightOp_cnt_ext (fun _ => true) (fun _ => true) Γ'.atom T.atom (owxEmb 2) (BAGGOp_rho2 x c)
      (fun _ => True) 0 (BAGGOp_rho2_emb x c) (fun _ => rfl) (fun _ _ => rfl) (fun _ => trivial)
      (BAWeightOp_self_mem_atom Γ') hcl (by simp) (fun v hv => absurd trivial hv) (fun v hv => absurd trivial hv)
    exact key


/-- Every new vertex of an extension by `u`, `β` is joined to `emb (ρ w)`, given an `M`-edge at `u` and one at `β`. -/
private theorem BAGGOp_e3 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (x c : E ⊕ I)
    (hu : ∃ e ∈ md, (e.x = owxEmb 2 x ∧ e.y = bpv 0) ∨ (e.x = bpv 0 ∧ e.y = owxEmb 2 x))
    (hb : ∃ e ∈ md, (e.x = owxEmb 2 c ∧ e.y = bpv 1) ∨ (e.x = bpv 1 ∧ e.y = owxEmb 2 c)) (w' : E ⊕ (I ⊕ Fin 2)) :
    Relation.ReflTransGen (fun a b => (BAGraph.ext 2 Γ rest s w md).atomAdj a b = true) w'
      (owxEmb 2 (BAGGOp_rho2 x c w')) := by
  rcases w' with e | i | j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.refl
  · fin_cases j
    · obtain ⟨e, he, h⟩ := hu
      exact Relation.ReflTransGen.single ((BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inr ⟨e, he, h.symm⟩))
    · obtain ⟨e, he, h⟩ := hb
      exact Relation.ReflTransGen.single ((BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inr ⟨e, he, h.symm⟩))

/-- The classes of a graph: `w ∈ cl v` makes the classes equal (the molecules). -/
private theorem BAGGOp_mol_eq_of_mem {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']
    (Γ : BAGraph E' I') {v w : E' ⊕ I'} (h : w ∈ Γ.mol v) : Γ.mol w = Γ.mol v := by
  rw [BAGraph.mem_mol_iff] at h
  ext x
  rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx
    exact (BAWeightOp_rtg_symm (fun a b => Γ.adj a b) (BAWeightOp_adj_comm Γ) h).trans hx

/-- **The number of classes can only drop under an extension covered by the old vertices** (the injection of the proof of
`BAWeightOp_nA_le`): if every class of `V'` contains `emb (ρ v)` and the classes of `V` map into those of `V'`, then
`cnt' ≤ cnt`. -/
private theorem BAGGOp_cnt_le {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (i : V → Bool) (i' : V' → Bool) (cl : V → Finset V) (cl' : V' → Finset V') (emb : V → V') (ρ : V' → V)
    (hi : ∀ a, i' (emb a) = i a) (hself : ∀ v, v ∈ cl v) (h1 : ∀ a b, b ∈ cl a → emb b ∈ cl' (emb a))
    (h3 : ∀ v, emb (ρ v) ∈ cl' v) (hsym : ∀ v w, w ∈ cl' v → cl' w = cl' v) :
    BAWeightOp_cnt i' cl' ≤ BAWeightOp_cnt i cl := by
  classical
  unfold BAWeightOp_cnt
  set F : Finset V → Finset V' := fun A => if hA : A.Nonempty then cl' (emb hA.choose) else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : V' => ∀ w ∈ cl' v, i' w = true)).image cl' ⊆
      ((Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl).image F := by
    intro C hC
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    have hv1 : cl' (emb (ρ v)) = cl' v := hsym v _ (h3 v)
    have hne : (cl (ρ v)).Nonempty := ⟨ρ v, hself _⟩
    refine Finset.mem_image.2 ⟨cl (ρ v), Finset.mem_image.2 ⟨ρ v, ?_, rfl⟩, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro b hb
      have := hv _ (hv1 ▸ h1 _ b hb)
      rwa [hi] at this
    · simp only [hF, hne, ↓reduceDIte]
      have : emb hne.choose ∈ cl' (emb (ρ v)) := h1 _ _ hne.choose_spec
      rw [hsym _ _ this, hv1]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le


private theorem BAGGOp_A1_e3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (w' : E ⊕ (I ⊕ Fin 2)) :
    Relation.ReflTransGen (fun a b => (BAGGOp_A1 Γ p q).atomAdj a b = true) w'
      (owxEmb 2 (BAGGOp_rho2 p.1.src p.1.dst w')) :=
  BAGGOp_e3 Γ _ _ _ _ _ _ ⟨bpM (owxEmb 2 p.1.src) (bpv 0), by simp [BAGGOp_A1], Or.inl ⟨rfl, rfl⟩⟩
    ⟨bpM (bpv 1) (owxEmb 2 p.1.dst), by simp [BAGGOp_A1], Or.inr ⟨rfl, rfl⟩⟩ w'

private theorem BAGGOp_A2_e3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (w' : E ⊕ (I ⊕ Fin 2)) :
    Relation.ReflTransGen (fun a b => (BAGGOp_A2 Γ p q).atomAdj a b = true) w'
      (owxEmb 2 (BAGGOp_rho2 p.1.src q.1.src w')) :=
  BAGGOp_e3 Γ _ _ _ _ _ _ ⟨bpM (owxEmb 2 p.1.src) (bpv 0), by simp [BAGGOp_A2], Or.inl ⟨rfl, rfl⟩⟩
    ⟨bpM (owxEmb 2 q.1.src) (bpv 1), by simp [BAGGOp_A2], Or.inl ⟨rfl, rfl⟩⟩ w'

private theorem BAGGOp_A3_e3 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (w' : E ⊕ (I ⊕ Fin 2)) :
    Relation.ReflTransGen (fun a b => (BAGGOp_A3 Γ p q).atomAdj a b = true) w'
      (owxEmb 2 (BAGGOp_rho2 p.1.src p.1.dst w')) :=
  BAGGOp_e3 Γ _ _ _ _ _ _ ⟨bpM (owxEmb 2 p.1.src) (bpv 0), by simp [BAGGOp_A3], Or.inl ⟨rfl, rfl⟩⟩
    ⟨bpM (bpv 1) (owxEmb 2 p.1.dst), by simp [BAGGOp_A3], Or.inr ⟨rfl, rfl⟩⟩ w'

/-- `A2`: `u` joins the atom of `x`, `β` that of `y'`; the atoms are those of `Γ`. -/
private theorem BAGGOp_A2_atoms (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (BAGGOp_A2 Γ p q).nA = Γ.nA ∧
      BAWeightOp_cnt (fun _ => true) (BAGGOp_A2 Γ p q).atom = BAWeightOp_cnt (fun _ => true) Γ.atom := by
  refine BAGGOp_pend Γ _ p.1.src q.1.src (fun u w h => Relation.ReflTransGen.single
    ((BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩))) ?_
    (BAGGOp_A2_e3 Γ p q)
  intro b b' hbb'
  rcases (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ b b').1 hbb' with ⟨a, a', rfl, rfl, h⟩ | ⟨e, he, h⟩
  · right; rw [BAGGOp_rho2_emb, BAGGOp_rho2_emb]; exact h
  · left
    simp only [BAGGOp_A2, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]

/-- `A3`: `u` joins the atom of `x`, `β` that of `y`; the atoms are those of `Γ`. -/
private theorem BAGGOp_A3_atoms (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (BAGGOp_A3 Γ p q).nA = Γ.nA ∧
      BAWeightOp_cnt (fun _ => true) (BAGGOp_A3 Γ p q).atom = BAWeightOp_cnt (fun _ => true) Γ.atom := by
  refine BAGGOp_pend Γ _ p.1.src p.1.dst (fun u w h => Relation.ReflTransGen.single
    ((BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩))) ?_
    (BAGGOp_A3_e3 Γ p q)
  intro b b' hbb'
  rcases (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ b b').1 hbb' with ⟨a, a', rfl, rfl, h⟩ | ⟨e, he, h⟩
  · right; rw [BAGGOp_rho2_emb, BAGGOp_rho2_emb]; exact h
  · left
    simp only [BAGGOp_A3, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]


/-! ### Merging two atoms (`A1`): adding the `M`-edge `M_{y'y}` -/

/-- Reachability after adding one symmetric edge `a — b`: through the old edges, possibly crossing the new edge once. -/
private theorem BAGGOp_rtg_merge {V : Type*} (r : V → V → Bool) (a b v w : V) :
    Relation.ReflTransGen (fun x y => r x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) v w ↔
      Relation.ReflTransGen (fun x y => r x y = true) v w ∨
        ((Relation.ReflTransGen (fun x y => r x y = true) v a ∨ Relation.ReflTransGen (fun x y => r x y = true) v b) ∧
          (Relation.ReflTransGen (fun x y => r x y = true) a w ∨ Relation.ReflTransGen (fun x y => r x y = true) b w)) := by
  have R := fun x y : V => Relation.ReflTransGen (fun x y => r x y = true) x y
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | @tail c w' _ hcw ih =>
      rcases hcw with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with ih | ⟨ih1, ih2 | ih2⟩
        · exact Or.inl (ih.tail h)
        · exact Or.inr ⟨ih1, Or.inl (ih2.tail h)⟩
        · exact Or.inr ⟨ih1, Or.inr (ih2.tail h)⟩
      · rcases ih with ih | ⟨ih1, _⟩
        · exact Or.inr ⟨Or.inl ih, Or.inr Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨ih1, Or.inr Relation.ReflTransGen.refl⟩
      · rcases ih with ih | ⟨ih1, _⟩
        · exact Or.inr ⟨Or.inr ih, Or.inl Relation.ReflTransGen.refl⟩
        · exact Or.inr ⟨ih1, Or.inl Relation.ReflTransGen.refl⟩
  · have hab : ∀ x y, r x y = true → Relation.ReflTransGen
        (fun x y => r x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) x y := fun x y h =>
      Relation.ReflTransGen.single (Or.inl h)
    have hl : ∀ x y, Relation.ReflTransGen (fun x y => r x y = true) x y →
        Relation.ReflTransGen (fun x y => r x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) x y := fun x y h =>
      Relation.ReflTransGen.mono (fun _ _ h => Or.inl h) _ _ h
    have e1 : Relation.ReflTransGen (fun x y => r x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) a b :=
      Relation.ReflTransGen.single (Or.inr (Or.inl ⟨rfl, rfl⟩))
    have e2 : Relation.ReflTransGen (fun x y => r x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))) b a :=
      Relation.ReflTransGen.single (Or.inr (Or.inr ⟨rfl, rfl⟩))
    rintro (h | ⟨h1 | h1, h2 | h2⟩)
    · exact hl _ _ h
    · exact (hl _ _ h1).trans (hl _ _ h2)
    · exact (hl _ _ h1).trans (e1.trans (hl _ _ h2))
    · exact (hl _ _ h1).trans (e2.trans (hl _ _ h2))
    · exact (hl _ _ h1).trans (hl _ _ h2)

/-- **Merging two classes**: if the closure `cl₂` is that of `cl` with `a`, `b` joined, the number of classes without a bad
element drops by `1` unless `cl a = cl b` or both classes of `a`, `b` have a bad element. -/
private theorem BAGGOp_cnt_merge {V : Type*} [Fintype V] [DecidableEq V] (i : V → Bool) (cl cl₂ : V → Finset V)
    (a b : V) (hself : ∀ v, v ∈ cl v) (hsym : ∀ v w, w ∈ cl v → cl w = cl v)
    (hcl : ∀ v w, w ∈ cl₂ v ↔ w ∈ cl v ∨ ((a ∈ cl v ∨ b ∈ cl v) ∧ (w ∈ cl a ∨ w ∈ cl b))) :
    BAWeightOp_cnt i cl₂ + (if cl a = cl b ∨ (¬ (∀ w ∈ cl a, i w = true) ∧ ¬ (∀ w ∈ cl b, i w = true)) then 0 else 1) =
      BAWeightOp_cnt i cl := by
  classical
  unfold BAWeightOp_cnt
  have hmem : ∀ v, a ∈ cl v ↔ v ∈ cl a := fun v => ⟨fun h => by rw [hsym _ _ h]; exact hself _,
    fun h => by rw [hsym _ _ h]; exact hself _⟩
  have hmemb : ∀ v, b ∈ cl v ↔ v ∈ cl b := fun v => ⟨fun h => by rw [hsym _ _ h]; exact hself _,
    fun h => by rw [hsym _ _ h]; exact hself _⟩
  by_cases hab : cl a = cl b
  · have : cl₂ = cl := by
      funext v; ext w; rw [hcl]
      refine ⟨?_, Or.inl⟩
      rintro (h | ⟨h1 | h1, h2⟩)
      · exact h
      · rw [hsym _ _ ((hmem v).1 h1)]
        exact h2.elim id fun h2 => hab ▸ h2
      · rw [hsym _ _ ((hmemb v).1 h1), ← hab]
        exact h2.elim id fun h2 => hab ▸ h2
    simp [this, hab]
  · have hin : ∀ v, (v ∈ cl a ∨ v ∈ cl b) → cl₂ v = cl a ∪ cl b := by
      intro v hv; ext w; rw [hcl, Finset.mem_union]
      rcases hv with hv | hv
      · have h1 := hsym _ _ hv
        have h2 := (hmem v).2 hv
        rw [h1]
        exact ⟨fun h => h.elim Or.inl fun h => h.2, fun h => Or.inr ⟨Or.inl (hself a), h⟩⟩
      · have h1 := hsym _ _ hv
        have h2 := (hmemb v).2 hv
        rw [h1]
        exact ⟨fun h => h.elim Or.inr fun h => h.2, fun h => Or.inr ⟨Or.inr (hself b), h⟩⟩
    have hout : ∀ v, v ∉ cl a → v ∉ cl b → cl₂ v = cl v := by
      intro v ha hb; ext w; rw [hcl]
      refine ⟨?_, Or.inl⟩
      rintro (h | ⟨h1 | h1, _⟩)
      · exact h
      · exact absurd ((hmem v).1 h1) ha
      · exact absurd ((hmemb v).1 h1) hb
    set S₁ := (Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl with hS₁
    set S₂ := (Finset.univ.filter (fun v : V => ∀ w ∈ cl₂ v, i w = true)).image cl₂ with hS₂
    have hP : S₁.filter (fun C => ¬ (C = cl a ∨ C = cl b)) = S₂.filter (fun C => ¬ C = cl a ∪ cl b) := by
      ext C
      simp only [Finset.mem_filter, hS₁, hS₂, Finset.mem_image, Finset.mem_univ, true_and, not_or]
      constructor
      · rintro ⟨⟨v, hv, rfl⟩, hA, hB⟩
        have hva : v ∉ cl a := fun h => hA (hsym _ _ h)
        have hvb : v ∉ cl b := fun h => hB (hsym _ _ h)
        refine ⟨⟨v, by rwa [hout v hva hvb], hout v hva hvb⟩, ?_⟩
        intro h
        have := hself v
        rw [h, Finset.mem_union] at this
        exact this.elim hva hvb
      · rintro ⟨⟨v, hv, rfl⟩, hAB⟩
        have hva : v ∉ cl a := fun h => hAB (hin v (Or.inl h))
        have hvb : v ∉ cl b := fun h => hAB (hin v (Or.inr h))
        rw [hout v hva hvb] at hv hAB ⊢
        refine ⟨⟨v, hv, rfl⟩, fun h => hva ?_, fun h => hvb ?_⟩
        · rw [← h]; exact hself v
        · rw [← h]; exact hself v
    have hmem1 : cl a ∈ S₁ ↔ ∀ w ∈ cl a, i w = true := by
      simp only [hS₁, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨a, h, rfl⟩⟩
    have hmem2 : cl b ∈ S₁ ↔ ∀ w ∈ cl b, i w = true := by
      simp only [hS₁, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨v, hv, h⟩ => h ▸ hv, fun h => ⟨b, h, rfl⟩⟩
    have hmem3 : cl a ∪ cl b ∈ S₂ ↔ (∀ w ∈ cl a, i w = true) ∧ ∀ w ∈ cl b, i w = true := by
      simp only [hS₂, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨v, hv, h⟩
        rw [h] at hv
        exact ⟨fun w hw => hv w (Finset.mem_union_left _ hw), fun w hw => hv w (Finset.mem_union_right _ hw)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨a, ?_, hin a (Or.inl (hself a))⟩
        rw [hin a (Or.inl (hself a))]
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        exacts [h1 w hw, h2 w hw]
    have c1 : (S₁.filter (fun C => C = cl a ∨ C = cl b)).card +
        (S₁.filter (fun C => ¬ (C = cl a ∨ C = cl b))).card = S₁.card := Finset.card_filter_add_card_filter_not _
    have c2 : (S₂.filter (fun C => C = cl a ∪ cl b)).card + (S₂.filter (fun C => ¬ C = cl a ∪ cl b)).card = S₂.card :=
      Finset.card_filter_add_card_filter_not _
    have e1 : (S₁.filter (fun C => C = cl a ∨ C = cl b)).card =
        (if cl a ∈ S₁ then 1 else 0) + (if cl b ∈ S₁ then 1 else 0) := by
      rw [Finset.filter_or, Finset.card_union_of_disjoint, Finset.filter_eq', Finset.filter_eq']
      · split_ifs <;> simp
      · rw [Finset.disjoint_left]
        intro C h1 h2
        simp only [Finset.mem_filter] at h1 h2
        exact hab (h1.2.symm.trans h2.2)
    have e2 : (S₂.filter (fun C => C = cl a ∪ cl b)).card = if cl a ∪ cl b ∈ S₂ then 1 else 0 := by
      rw [Finset.filter_eq']; split_ifs <;> simp
    rw [hP, e1] at c1
    rw [e2] at c2
    simp only [hab, false_or, hmem1, hmem2, hmem3] at c1 c2 ⊢
    split_ifs at c1 c2 ⊢ <;> first | omega | (exfalso; tauto)


private theorem BAGGOp_addM_atomAdj (Γ : BAGraph E I) (a b u v : E ⊕ I) :
    (Γ.addM ⟨true, a, b⟩).atomAdj u v = true ↔ Γ.atomAdj u v = true ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by
  simp only [BAGraph.atomAdj, BAGraph.addM, List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
  tauto

private theorem BAGGOp_addM_atom (Γ : BAGraph E I) (a b v w : E ⊕ I) :
    w ∈ (Γ.addM ⟨true, a, b⟩).atom v ↔
      w ∈ Γ.atom v ∨ ((a ∈ Γ.atom v ∨ b ∈ Γ.atom v) ∧ (w ∈ Γ.atom a ∨ w ∈ Γ.atom b)) := by
  simp only [BAGraph.mem_atom_iff]
  have h : (fun x y => (Γ.addM ⟨true, a, b⟩).atomAdj x y = true) =
      fun x y => Γ.atomAdj x y = true ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x)) :=
    funext fun x => funext fun y => propext (BAGGOp_addM_atomAdj Γ a b x y)
  rw [h]
  exact BAGGOp_rtg_merge (fun x y => Γ.atomAdj x y) a b v w

/-- Adding the `M`-edge `M_{ab}` merges the atoms of `a`, `b`: the count of classes without a vertex `i = false` (`i = isRight`
for `n_A`, `i ≡ true` for the number of atoms) drops by `1`, unless the atoms coincide or both contain a vertex `i = false`. -/
private theorem BAGGOp_addM_cnt (Γ : BAGraph E I) (a b : E ⊕ I) (i : E ⊕ I → Bool) :
    BAWeightOp_cnt i (Γ.addM ⟨true, a, b⟩).atom +
      (if Γ.atom a = Γ.atom b ∨ (¬ (∀ w ∈ Γ.atom a, i w = true) ∧ ¬ (∀ w ∈ Γ.atom b, i w = true)) then 0 else 1) =
      BAWeightOp_cnt i Γ.atom :=
  BAGGOp_cnt_merge i Γ.atom _ a b (BAWeightOp_self_mem_atom Γ) (fun _ _ h => BAWeightOp_atom_eq_of_mem Γ h)
    (BAGGOp_addM_atom Γ a b)

/-- `A1`: `u` joins the atom of `x`, `β` that of `y` and, through `M_{y'β}`, that of `y'`: the atoms are those of `Γ` with the
atoms of `y`, `y'` merged (`Γ.addM (M_{y'y})`). -/
private theorem BAGGOp_A1_atoms (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (BAGGOp_A1 Γ p q).nA = (Γ.addM ⟨true, q.1.src, p.1.dst⟩).nA ∧
      BAWeightOp_cnt (fun _ => true) (BAGGOp_A1 Γ p q).atom =
        BAWeightOp_cnt (fun _ => true) (Γ.addM ⟨true, q.1.src, p.1.dst⟩).atom := by
  have a1 : (BAGGOp_A1 Γ p q).atomAdj (owxEmb 2 q.1.src) (bpv 1) = true :=
    (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inr ⟨bpM (owxEmb 2 q.1.src) (bpv 1), by simp [BAGGOp_A1],
      Or.inl ⟨rfl, rfl⟩⟩)
  have a2 : (BAGGOp_A1 Γ p q).atomAdj (bpv 1) (owxEmb 2 p.1.dst) = true :=
    (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inr ⟨bpM (bpv 1) (owxEmb 2 p.1.dst), by simp [BAGGOp_A1],
      Or.inl ⟨rfl, rfl⟩⟩)
  refine BAGGOp_pend _ _ p.1.src p.1.dst ?_ ?_
    (BAGGOp_A1_e3 Γ p q)
  · intro u w h
    rcases (BAGGOp_addM_atomAdj Γ _ _ u w).1 h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Relation.ReflTransGen.single ((BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩))
    · exact Relation.ReflTransGen.head a1 (Relation.ReflTransGen.single a2)
    · have a1' : (BAGGOp_A1 Γ p q).atomAdj (bpv 1) (owxEmb 2 q.1.src) = true :=
        (BAWeightOp_atomAdj_comm _ _ _).trans a1
      have a2' : (BAGGOp_A1 Γ p q).atomAdj (owxEmb 2 p.1.dst) (bpv 1) = true :=
        (BAWeightOp_atomAdj_comm _ _ _).trans a2
      exact Relation.ReflTransGen.head a2' (Relation.ReflTransGen.single a1')
  · intro b b' hbb'
    rcases (BAWeightOp_ext_atomAdj 2 Γ _ _ _ _ b b').1 hbb' with ⟨a, a', rfl, rfl, h⟩ | ⟨e, he, h⟩
    · right; rw [BAGGOp_rho2_emb, BAGGOp_rho2_emb]; exact (BAGGOp_addM_atomAdj Γ _ _ _ _).2 (Or.inl h)
    · simp only [BAGGOp_A1, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl
      · left; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]
      · left; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]
      · left; rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]
      · right
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp only [BAGGOp_rho2_emb, BAGGOp_rho2_u, BAGGOp_rho2_b, bpM]
        · exact (BAGGOp_addM_atomAdj Γ _ _ _ _).2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · exact (BAGGOp_addM_atomAdj Γ _ _ _ _).2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- `n_M` of an extension by two joined vertices does not exceed that of `Γ` (the new vertices join old molecules). -/
private theorem BAGGOp_nM_le (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin 2)))) (x c : E ⊕ I)
    (he3 : ∀ w', Relation.ReflTransGen (fun a b => (BAGraph.ext 2 Γ rest s w md).atomAdj a b = true) w'
      (owxEmb 2 (BAGGOp_rho2 x c w'))) : (BAGraph.ext 2 Γ rest s w md).nM ≤ Γ.nM := by
  have h1 : ∀ a b : E ⊕ I, b ∈ Γ.mol a → owxEmb 2 b ∈ (BAGraph.ext 2 Γ rest s w md).mol (owxEmb 2 a) := by
    intro a b hb
    rw [BAGraph.mem_mol_iff] at hb ⊢
    exact Relation.ReflTransGen.lift (owxEmb 2) (fun a b hab =>
      (BAWeightOp_ext_adj 2 Γ rest s w md _ _).2 (Or.inl ⟨a, b, rfl, rfl, hab⟩)) _ _ hb
  have h3 : ∀ v, owxEmb 2 (BAGGOp_rho2 x c v) ∈ (BAGraph.ext 2 Γ rest s w md).mol v := by
    intro v
    rw [BAGraph.mem_mol_iff]
    refine Relation.ReflTransGen.mono (fun a b h => ?_) _ _ (he3 v)
    simp only [BAGraph.adj, Bool.or_eq_true]
    exact Or.inr h
  have key := BAGGOp_cnt_le (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 2) => w.isRight) Γ.mol
    (BAGraph.ext 2 Γ rest s w md).mol (owxEmb 2) (BAGGOp_rho2 x c) BAWeightOp_isRight_emb
    (fun v => by rw [BAGraph.mem_mol_iff]) h1 h3 (fun v w h => BAGGOp_mol_eq_of_mem _ h)
  exact key


/-- `κ ∈ {0, 1}`: the internal atoms lost when the atoms of `a`, `b` are merged: none if they coincide or both contain an external
vertex (a vertex `inl _`), else one (`BAGGOp_addM_cnt`). -/
def BAGGOp_kappa (Γ : BAGraph E I) (a b : E ⊕ I) : ℕ :=
  if Γ.atom a = Γ.atom b ∨ (¬ (∀ w ∈ Γ.atom a, w.isRight = true) ∧ ¬ (∀ w ∈ Γ.atom b, w.isRight = true)) then 0 else 1

/-- The number of atoms with an external vertex. -/
def BAGGOp_nExt (Γ : BAGraph E I) : ℕ := ((Finset.univ.filter fun v : E ⊕ I => v.isLeft = true).image Γ.atom).card

private theorem BAGGOp_ext_nS (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    (BAGraph.ext k Γ rest s w md).nS = rest.length + s.length := by
  simp [BAGraph.nS, BAGraph.ext, LGraph.owxExt]

private theorem BAGGOp_ext_nW (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) :
    (BAGraph.ext k Γ rest s w md).nW = Γ.nW + w.length := by
  simp [BAGraph.nW, BAGraph.ext, LGraph.owxExt]

private theorem BAGGOp_addM_nA (Γ : BAGraph E I) (a b : E ⊕ I) :
    (Γ.addM ⟨true, a, b⟩).nA + BAGGOp_kappa Γ a b = Γ.nA :=
  BAGGOp_addM_cnt Γ a b (fun w => w.isRight)

private theorem BAGGOp_addM_cnt_all (Γ : BAGraph E I) (a b : E ⊕ I) :
    BAWeightOp_cnt (fun _ => true) (Γ.addM ⟨true, a, b⟩).atom + (if Γ.atom a = Γ.atom b then 0 else 1) =
      BAWeightOp_cnt (fun _ => true) Γ.atom := by
  have := BAGGOp_addM_cnt Γ a b (fun _ => true)
  simpa using this

private theorem BAGGOp_kappa_le (Γ : BAGraph E I) (a b : E ⊕ I) :
    BAGGOp_kappa Γ a b ≤ if Γ.atom a = Γ.atom b then 0 else 1 := by
  unfold BAGGOp_kappa; split_ifs <;> simp_all

/-- The counters of `A1`, `A2`, `A3` (the terms with `n_A` not raised). -/
private theorem BAGGOp_heads (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hq : q ∈ lwSplit p.2) :
    ((BAGGOp_A1 Γ p q).nS + 2 = Γ.nS ∧ (BAGGOp_A1 Γ p q).nW = Γ.nW + 1 ∧
      (BAGGOp_A1 Γ p q).nA + BAGGOp_kappa Γ q.1.src p.1.dst = Γ.nA ∧ (BAGGOp_A1 Γ p q).nM ≤ Γ.nM ∧
      BAGGOp_nExt (BAGGOp_A1 Γ p q) ≤ BAGGOp_nExt Γ) ∧
    (∀ T ∈ [BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q], T.nS + 1 = Γ.nS ∧ T.nW = Γ.nW + 1 ∧ T.nA = Γ.nA ∧ T.nM ≤ Γ.nM ∧
      BAGGOp_nExt T = BAGGOp_nExt Γ) := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  have hS : Γ.nS = q.2.length + 2 := by simp only [BAGraph.nS]; omega
  refine ⟨⟨?_, ?_, ?_, BAGGOp_nM_le Γ _ _ _ _ p.1.src p.1.dst (BAGGOp_A1_e3 Γ p q), ?_⟩, ?_⟩
  · simp [BAGGOp_A1, BAGGOp_ext_nS, hS]
  · simp [BAGGOp_A1, BAGGOp_ext_nW]
  · rw [(BAGGOp_A1_atoms Γ p q).1]
    exact BAGGOp_addM_nA Γ q.1.src p.1.dst
  · have e1 : BAGGOp_nExt (BAGGOp_A1 Γ p q) + (BAGGOp_A1 Γ p q).nA = BAWeightOp_cnt (fun _ => true) (BAGGOp_A1 Γ p q).atom :=
      BAWeightOp_nExt_add_nA _
    have e2 : BAGGOp_nExt Γ + Γ.nA = BAWeightOp_cnt (fun _ => true) Γ.atom := BAWeightOp_nExt_add_nA _
    have h1 := BAGGOp_A1_atoms Γ p q
    have h2 := BAGGOp_addM_nA Γ q.1.src p.1.dst
    have h3 := BAGGOp_addM_cnt_all Γ q.1.src p.1.dst
    have hk := BAGGOp_kappa_le Γ q.1.src p.1.dst
    rw [h1.2] at e1
    rw [h1.1] at e1
    split_ifs at h3 hk <;> omega
  · intro T hT
    have hl'' : ∀ T' : BAGraph E (I ⊕ Fin 2), T'.nS = 1 + q.2.length → T'.nS + 1 = Γ.nS := fun T' h => by omega
    have key : ∀ (T : BAGraph E (I ⊕ Fin 2)), T.nS = 1 + q.2.length → T.nW = Γ.nW + 1 → T.nA = Γ.nA →
        BAWeightOp_cnt (fun _ => true) T.atom = BAWeightOp_cnt (fun _ => true) Γ.atom → T.nM ≤ Γ.nM →
        T.nS + 1 = Γ.nS ∧ T.nW = Γ.nW + 1 ∧ T.nA = Γ.nA ∧ T.nM ≤ Γ.nM ∧ BAGGOp_nExt T = BAGGOp_nExt Γ := by
      intro T h1 h2 h3 h4 h5
      have e1 : BAGGOp_nExt T + T.nA = BAWeightOp_cnt (fun _ => true) T.atom := BAWeightOp_nExt_add_nA _
      have e2 : BAGGOp_nExt Γ + Γ.nA = BAWeightOp_cnt (fun _ => true) Γ.atom := BAWeightOp_nExt_add_nA _
      exact ⟨by omega, h2, h3, h5, by omega⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · exact key _ (by simp [BAGGOp_A2, BAGGOp_ext_nS]; omega) (by simp [BAGGOp_A2, BAGGOp_ext_nW])
        (BAGGOp_A2_atoms Γ p q).1 (BAGGOp_A2_atoms Γ p q).2 (BAGGOp_nM_le Γ _ _ _ _ p.1.src q.1.src (BAGGOp_A2_e3 Γ p q))
    · exact key _ (by simp [BAGGOp_A3, BAGGOp_ext_nS]; omega) (by simp [BAGGOp_A3, BAGGOp_ext_nW])
        (BAGGOp_A3_atoms Γ p q).1 (BAGGOp_A3_atoms Γ p q).2 (BAGGOp_nM_le Γ _ _ _ _ p.1.src p.1.dst (BAGGOp_A3_e3 Γ p q))


/-- The counters of `BAstepMono` at `T°`: `n_M`, `n_A - n_W` and the number of external
atoms of `T°` do not exceed those of `Γ`. -/
def BAGGOp_Mono {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E I)
    (T : BAGraph E' I') : Prop :=
  (BAWeightOp_circ T).nM ≤ Γ.nM ∧ (((BAWeightOp_circ T).nA : ℤ) - (BAWeightOp_circ T).nW ≤ (Γ.nA : ℤ) - Γ.nW) ∧
    BAGGOp_nExt (BAWeightOp_circ T) ≤ BAGGOp_nExt Γ

private theorem BAGGOp_gg2_tail (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (Γ.gg2 p q).tail = [BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q] ++
      ([BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q)) := rfl

/-- **Raw counters** (Definition B.5 `def scalingBA`).  `A1` (the first sum): `n_S - 2`, `n_W + 1`, `n_A - κ`
(`κ ∈ {0, 1}`, `BAGGOp_kappa`), `n_M` not raised; `A2`, `A3` (the second sum): `n_S - 1`, `n_W + 1`, `n_A`, `n_M` not raised; `A4`,
`A5`, `AD` (the third sum with `W = 1`) and `B1`, `B2`, `BD` (with `W - 1`): `n_S + 1`, `(n_W, n_A) + (1, 1)` resp. `(2, 2)`, `n_M`
(exact).  For every graph `Γ`, normal or not. -/
theorem gg_counters {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    ((BAGGOp_A1 Γ p q).nS + 2 = Γ.nS ∧ (BAGGOp_A1 Γ p q).nW = Γ.nW + 1 ∧
      (BAGGOp_A1 Γ p q).nA + BAGGOp_kappa Γ q.1.src p.1.dst = Γ.nA ∧ (BAGGOp_A1 Γ p q).nM ≤ Γ.nM) ∧
    (∀ T ∈ [BAGGOp_A2 Γ p q, BAGGOp_A3 Γ p q], T.nS + 1 = Γ.nS ∧ T.nW = Γ.nW + 1 ∧ T.nA = Γ.nA ∧ T.nM ≤ Γ.nM) ∧
    (∀ T ∈ [BAGGOp_A4 Γ p q, BAGGOp_A5 Γ p q] ++ (lwSplit q.2).map (BAGGOp_AD Γ p q),
      T.counters = ⟨Γ.nS + 1, Γ.nW + 1, Γ.nA + 1, Γ.nM, 0, 0⟩) ∧
    (∀ T ∈ Γ.gg4 p q, T.counters = ⟨Γ.nS + 1, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩) := by
  obtain ⟨⟨a, b, c, d, -⟩, h2⟩ := BAGGOp_heads Γ p q hp hq
  exact ⟨⟨a, b, c, d⟩, fun T hT => (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) (h2 T hT),
    fun T hT => (BAGGOp_tail2_cnt Γ p q hp hq T hT).1, fun T hT => (BAGGOp_tail4_cnt Γ p q hp hq T hT).1⟩

/-- **Raw order** (`raw = ord T° - ord Γ`): `A1` has `ord A1 = ord Γ + 2κ`, so it **keeps the
order of `Γ` iff `κ = 0`** (the atoms of `y = p.1.dst`, `y' = q.1.src` coincide or both contain an external vertex: the case of the first term of `gg2`) and gains `2` otherwise; every other term `T` of `gg2` and `gg4` has `ord T° = ord Γ + 1`. -/
theorem gg_raw {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (BAGGOp_A1 Γ p q).scalingOrder = Γ.scalingOrder + 2 * (BAGGOp_kappa Γ q.1.src p.1.dst : ℤ) ∧
    (∀ T ∈ (Γ.gg2 p q).tail, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) ∧
    (∀ T ∈ Γ.gg4 p q, (BAWeightOp_circ T).scalingOrder = Γ.scalingOrder + 1) := by
  obtain ⟨⟨a, b, c, -, -⟩, h2⟩ := BAGGOp_heads Γ p q hp hq
  obtain ⟨-, -, c3, c4⟩ := gg_counters Γ p q hp hq
  refine ⟨?_, fun T hT => ?_, fun T hT => ?_⟩
  · simp only [BAGraph.scalingOrder, BAGraph.counters, ord]
    omega
  · rw [BAGGOp_gg2_tail] at hT
    unfold BAGraph.scalingOrder
    rw [BAWeightOp_circ_counters]
    rcases List.mem_append.1 hT with hT | hT
    · obtain ⟨e1, e2, e3, -⟩ := h2 T hT
      simp only [BAGraph.counters, ord]
      omega
    · rw [c3 T hT]
      simp only [BAGraph.counters, ord]
      push_cast
      ring
  · unfold BAGraph.scalingOrder
    rw [BAWeightOp_circ_counters, c4 T hT]
    simp only [BAGraph.counters, ord]
    push_cast
    ring

/-- **The order of the partition** ((B.17) `eq:ordG_BA`, (B.9) `eq:GGraisesord` read with `n_A`): for a normal `Γ`,
`ord Γ ≤ ordG T` for every term `T` of `gg2` and `gg4`: `A1` (`ord = ord Γ + 2κ`), `A2`, `A3` are normal; for the others `ord T° = ord Γ + 1`
and a member with `j` `M`-splits has `ord = ord Γ + 1 - j + 2κ'`, `κ' ≥ 1` once `j ≥ 2` (the singleton atom `{β}` is merged). -/
theorem gg_scalingOrderG {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hN : Γ.Normal) :
    (∀ T ∈ Γ.gg2 p q, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) ∧
    (∀ T ∈ Γ.gg4 p q, ((Γ.scalingOrder : ℤ) : WithTop ℤ) ≤ T.scalingOrderG) := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hcirc' : ∀ e ∈ q.2, e.circ = true := fun e he =>
    hN.2 e ((lwSplit_perm Γ.solid p hp).mem_iff.2 (List.mem_cons_of_mem _
      ((lwSplit_perm p.2 q hq).mem_iff.2 (List.mem_cons_of_mem _ he))))
  obtain ⟨⟨a, b, c, -, -⟩, h2⟩ := BAGGOp_heads Γ p q hp hq
  refine ⟨fun T hT => ?_, BAGGOp_tail4_ge Γ hN p q hp hq⟩
  rw [BAGGOp_gg2_eq] at hT
  rcases List.mem_append.1 hT with hT | hT
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl | rfl | rfl | rfl
    · have hn : (BAGGOp_A1 Γ p q).Normal := BAWeightOp_ext_normal 2 Γ hN _ _ _ _ hcirc' (by simp [BAGGOp_A1])
      rw [BAGraph.scalingOrderG_of_normal _ hn]
      refine WithTop.coe_le_coe.2 ?_
      simp only [BAGraph.scalingOrder, BAGraph.counters, ord]
      omega
    · have hn : (BAGGOp_A2 Γ p q).Normal := BAWeightOp_ext_normal 2 Γ hN _ _ _ _ hcirc' (by simp [BAGGOp_A2, bpS])
      rw [BAGraph.scalingOrderG_of_normal _ hn]
      obtain ⟨e1, e2, e3, -⟩ := h2 _ (List.mem_cons_self)
      refine WithTop.coe_le_coe.2 ?_
      simp only [BAGraph.scalingOrder, BAGraph.counters, ord]
      omega
    · have hn : (BAGGOp_A3 Γ p q).Normal := BAWeightOp_ext_normal 2 Γ hN _ _ _ _ hcirc' (by simp [BAGGOp_A3, bpS])
      rw [BAGraph.scalingOrderG_of_normal _ hn]
      obtain ⟨e1, e2, e3, -⟩ := h2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
      refine WithTop.coe_le_coe.2 ?_
      simp only [BAGraph.scalingOrder, BAGraph.counters, ord]
      omega
    · exact BAGGOp_tail2_ge Γ hN p q hp hq _ (by simp)
    · exact BAGGOp_tail2_ge Γ hN p q hp hq _ (by simp)
  · exact BAGGOp_tail2_ge Γ hN p q hp hq _ (List.mem_append_right _ hT)

/-- **The counters of `BAstepMono` at `T°`** for the terms of `gg2` and `gg4`. -/
theorem gg_mono {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
    (p q : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) :
    (∀ T ∈ Γ.gg2 p q, BAGGOp_Mono Γ T) ∧ (∀ T ∈ Γ.gg4 p q, BAGGOp_Mono Γ T) := by
  obtain ⟨⟨a, b, c, d, e⟩, h2⟩ := BAGGOp_heads Γ p q hp hq
  have tail : ∀ {k : ℕ} (T : BAGraph Ex (Ix ⊕ Fin k)) (n : ℕ),
      T.counters = ⟨Γ.nS + 1, Γ.nW + n, Γ.nA + n, Γ.nM, 0, 0⟩ →
      BAWeightOp_cnt (fun _ => true) T.atom = BAWeightOp_cnt (fun _ => true) Γ.atom + n → BAGGOp_Mono Γ T := by
    intro k T n hc hn
    obtain ⟨m1, m2, m3⟩ := BAWeightOp_mono_aux Γ T n hc hn
    exact ⟨m1.le, m2.le, m3⟩
  refine ⟨fun T hT => ?_, fun T hT => ?_⟩
  · rw [BAGGOp_gg2_eq] at hT
    rcases List.mem_append.1 hT with hT | hT
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
      rcases hT with rfl | rfl | rfl | rfl | rfl
      · exact ⟨d, by change ((BAGGOp_A1 Γ p q).nA : ℤ) - (BAGGOp_A1 Γ p q).nW ≤ _; omega, e⟩
      · obtain ⟨e1, e2, e3, e4, e5⟩ := h2 _ (List.mem_cons_self)
        exact ⟨e4, by change ((BAGGOp_A2 Γ p q).nA : ℤ) - (BAGGOp_A2 Γ p q).nW ≤ _; omega, e5.le⟩
      · obtain ⟨e1, e2, e3, e4, e5⟩ := h2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
        exact ⟨e4, by change ((BAGGOp_A3 Γ p q).nA : ℤ) - (BAGGOp_A3 Γ p q).nW ≤ _; omega, e5.le⟩
      · exact tail _ 1 (BAGGOp_tail2_cnt Γ p q hp hq _ (by simp)).1 (BAGGOp_tail2_cnt Γ p q hp hq _ (by simp)).2
      · exact tail _ 1 (BAGGOp_tail2_cnt Γ p q hp hq _ (by simp)).1 (BAGGOp_tail2_cnt Γ p q hp hq _ (by simp)).2
    · exact tail _ 1 (BAGGOp_tail2_cnt Γ p q hp hq _ (List.mem_append_right _ hT)).1
        (BAGGOp_tail2_cnt Γ p q hp hq _ (List.mem_append_right _ hT)).2
  · exact tail _ 2 (BAGGOp_tail4_cnt Γ p q hp hq T hT).1 (BAGGOp_tail4_cnt Γ p q hp hq T hT).2

end Order

end RBM.Graph

end
