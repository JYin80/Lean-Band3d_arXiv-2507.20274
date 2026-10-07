/-
T2289 (LW-13c) check file: pins only.  No proofs, no `sorry`, no `by`.
Compiles on `main` (e7d495b) as is: merged imports only.
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Graph.AuxGraph

/-! ## Section 1: merged names used (namespace from the enclosing `namespace … end` blocks) -/

-- `Graph/LWVocab.lean` (37db678), namespace `RBM.Graph` / `RBM.Graph.NGraph` (`:315-373`)
#check @RBM.Graph.NV
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.val
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.NoGhost
#check @RBM.Graph.NGraph.GhostOK
#check @RBM.Graph.NGraph.nSolid
#check @RBM.Graph.NGraph.noGhostPath
#check @RBM.Graph.NGraph.nngh
#check @RBM.Graph.NGraph.ordN
#check @RBM.Graph.figAux
#check @RBM.Graph.figAux_nested
#check @RBM.Graph.PGraph
-- `Graph/AnpKey.lean` (e5b944a), namespace `RBM.Graph`
#check @RBM.Graph.AnpDetGhAt
#check @RBM.Graph.AnpDetGh
#check @RBM.Graph.anpKey_zdistInf_sub_comm
#check @RBM.Graph.NGraph.ghostify
#check @RBM.Graph.anpKey_gf_path
#check @RBM.Graph.anpKey_ghostify_nested
#check @RBM.Graph.anpKey_ghostify_ghostOK
#check @RBM.Graph.anpKey_ghostify_nSolid
#check @RBM.Graph.anpKey_ghostify_nngh
#check @RBM.Graph.anpKey_ghostify_ord
#check @RBM.Graph.anpKey_ghostOK_of_noGhost
#check @RBM.Graph.anpKey_noGhostPath_of_noGhost
#check @RBM.Graph.anpKey_nngh_of_noGhost
#check @RBM.Graph.anpKey_oneEdge
#check @RBM.Graph.anpKey_oneEdge_nested
-- `Graph/AnpKey2.lean` (e362f4b), namespace `RBM.Graph` (`valOn` inside `namespace NGraph`)
#check @RBM.Graph.NGraph.valOn
#check @RBM.Graph.anpKey2_val_eq_valOn
#check @RBM.Graph.anpKey2_ep
#check @RBM.Graph.anpKey2_ep_nonneg
#check @RBM.Graph.anpKey2_ep_ghostify
-- `Graph/AnpKey6.lean` (e2703ec), namespace `RBM.Graph`
#check @RBM.Graph.anpDetGh_holds
#check @RBM.Graph.anpKey6_w
#check @RBM.Graph.anpKey6_val_eq
#check @RBM.Graph.anpKey6_w_nonneg
-- `Kernel/PropT.lean` (c3f3d5d), namespace `RBM`, section `TTk`
#check @RBM.sfT
#check @RBM.sfT_nonneg
#check @RBM.sfT_zero
#check @RBM.sfT_antitone
-- `Defs/Sizes.lean` (0a873f1), namespace `RBM.Gauss`
#check @RBM.Gauss.zdistInf
-- `Graph/LWPins.lean` (975f4ff), namespace `RBM.Gauss.Sizes` (consumer, LW-13b)
#check @RBM.Gauss.Sizes.LWMomentExp
-- `Graph/LocalRegular.lean` (3bf20e1), namespace `RBM.Graph`
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.localReg_stepEdges
#check @RBM.Graph.localReg_mem_stepEdges
-- `Graph/AuxGraph.lean` (87cf70c), namespace `RBM.Graph`
#check @RBM.Graph.LGraph.auxOrd
#check @RBM.Graph.LGraph.auxVal
#check @RBM.Graph.auxGraph_Data
#check @RBM.Graph.auxGraph_nodeV
#check @RBM.Graph.auxGraph_ngraph
#check @RBM.Graph.auxGraph_noGhost
#check @RBM.Graph.auxGraph_isNested
#check @RBM.Graph.auxGraph_molEdgeMS_nd
#check @RBM.Graph.auxGraph_ordN
#check @RBM.Graph.auxGraph_val_eq
#check @RBM.Graph.auxGraph_card_aux
#check @RBM.Graph.LWAuxNested
#check @RBM.Graph.lwAuxNested_holds
#check @RBM.Graph.auxGraph_inst_Q_hxy
-- `Graph/LocalRegular2.lean` (32d895b), namespace `RBM.Graph`
#check @RBM.Graph.localReg2_inst_Q
#check @RBM.Graph.localReg2_inst_Q_locReg345

/-! ## Section 2: vocabulary and pins of T2289 (LW-13c) -/

noncomputable section

namespace RBM.Graph.T2289Check

open RBM RBM.Gauss RBM.Graph

/-- `𝐃^∧_{>ℓ}` (supervisor 1102 §2.2, option (c); replaces the "or" of `7_8:1636`): `|a_i - c|_∞ > ℓ` **and**
`|b_i - c|_∞ > ℓ` for every `i`. -/
def farDAnd (d L : ℕ) [NeZero L] {p : ℕ} (a b : Fin p → Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ∀ i : Fin p,
    ℓ < ((zdistInf d L (a i - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b i - c) : ℕ) : ℝ)

/-- The path `𝔓_i` meets no external vertex other than its own `a_i`, `b_i` (preflight (ii); the outputs of
`lwAuxNested_holds` have it: `auxGraph_nodeV Dt i` takes only the values `a_i`, `b_i`, internal). -/
def ownExt {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∀ i : Fin p, ∀ st ∈ Γ.path i,
    st.2 = Sum.inl (Sum.inl i) ∨ st.2 = Sum.inl (Sum.inr i) ∨ ∃ α : Fin q, st.2 = Sum.inr α

/-- The labellings `S` put the internal vertex reached by the first step of each path at `L^∞` distance `> ℓ`
from that path's `a_i`. -/
def HeadFar (d L : ℕ) [NeZero L] {p q : ℕ} (Γ : NGraph p q) (a : Fin p → Zd d L) (ℓ : ℝ)
    (S : Finset (Fin q → Zd d L)) : Prop :=
  ∀ lab ∈ S, ∀ (i : Fin p) (st : Fin Γ.es.length × NV p q) (α : Fin q),
    (Γ.path i).head? = some st → st.2 = Sum.inr α → ℓ < ((zdistInf d L (a i - lab α) : ℕ) : ℝ)

/-- **Far core** (`(adsuu33)`–`(adsuu44)` deterministic, `7_8:1637-1642`, corrected): truncated edges
`ξ ≤ 𝖳_t(|α-β|_∞ ∧ ℓ)`, row sums `≤ θ`; for every set `S` of internal labellings with `HeadFar`,
`Σ_{ℓ∈S} Π ≤ C θ^q 𝖳_t(0)^{ord - p} Π_i 𝖳_t(|a_i - b_i| ∧ ℓ)`; `C` depends on `Γ`, `d` only. -/
def AnpFarHeadAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ (a b : Fin p → Zd d L) (S : Finset (Fin q → Zd d L)), HeadFar d L Γ a ℓ S →
          Γ.valOn ξ a b S ≤
            C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
              ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)

def AnpFarHead (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → ownExt Γ → AnpFarHeadAt d Γ

/-- **Far pin, "and" domain** (supervisor 1102 O4): every internal label in `𝐃^∧_{>ℓ}`. -/
def AnpFarAndAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t θ ℓ : ℝ), 0 < W → t < 1 → 0 < θ → 0 ≤ ℓ →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        (∀ α, ∑ β, ξ α β ^ 2 ≤ θ) →
        ∀ a b : Fin p → Zd d L,
          Γ.valOn ξ a b (Fintype.piFinset fun _ : Fin q => farDAnd d L a b ℓ) ≤
            C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
              ∏ i, sfT d L W g t (min ((zdistInf d L (a i - b i) : ℕ) : ℝ) ℓ)

def AnpFarAnd (d : ℕ) : Prop :=
  ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → ownExt Γ → AnpFarAndAt d Γ

/-- **Supply for LW-13b** (preflight (ii)): the merged `LWAuxNested` (`AuxGraph.lean:1597-1604`) verbatim with
`ownExt Γa` added. -/
def LWAuxNestedOwn : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ ownExt Γa ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be

end RBM.Graph.T2289Check

end

/-! ## Section 3: instance shapes (Prop-valued, no proof obligation) -/

example : Prop := RBM.Graph.T2289Check.AnpFarHead 3
example : Prop := RBM.Graph.T2289Check.AnpFarAnd 3
example : Prop := RBM.Graph.T2289Check.AnpFarAndAt 3 RBM.Graph.figAux
example : Prop := RBM.Graph.T2289Check.AnpFarAndAt 3 RBM.Graph.anpKey_oneEdge
example : Prop := RBM.Graph.T2289Check.AnpFarHeadAt 3 RBM.Graph.figAux
example : Prop := RBM.Graph.T2289Check.ownExt RBM.Graph.figAux
example : Prop := RBM.Graph.T2289Check.LWAuxNestedOwn
example : Prop :=
  ∃ Γa : RBM.Graph.NGraph 2 RBM.Graph.localReg2_inst_Q.nM,
    Γa.NoGhost ∧ Γa.IsNested ∧ RBM.Graph.T2289Check.ownExt Γa ∧ RBM.Graph.T2289Check.AnpFarAndAt 3 Γa
