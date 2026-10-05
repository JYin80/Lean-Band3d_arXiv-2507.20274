/-
Release check for T2170 (dispatcher V1, Mon Oct  5 03:24 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §24, §29, §45 O2, §47).
LW-11a: `def: BM2`, `def_auxgraph`, `GtoAG` (`7_8:863-932`), deterministic part: the block-level auxiliary graph of a
normal graph, `(eq:ordGaux)` and `ord(Γ) - ord(Γ^aux) ≥ 0`, `(G_by_auxG)` in deterministic form, the `scalemole` tail for
two external vertices in one molecule, the nested form of `Γ^aux` that `LWAnp` takes.  Section 1: the merged names it
builds on (LW-03 `Graph/LWVocab`, LW-09 `Graph/LWSizeClaim`, LW-10a `Graph/LocalRegular`, LW-10b `Graph/LocalRegular2`,
the lattice and block vocabulary) and the downstream pins (LW-P `Graph/LWPins`).  Section 2: the pinned vocabulary (four
definitions) and the four pinned statements, in namespace `RBM.Graph.T2170Check` here; T2170 defines the vocabulary and
the three `Prop`s `LWGtoAG`, `LWScalemole`, `LWAuxNested` in `RBM.Graph` verbatim, proves them (`lwGtoAG_holds`,
`lwScalemole_holds`, `lwAuxNested_holds`) and proves `AuxOrdPin` as three theorems.
Statement and `#check` only: no proofs, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2170-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- LW-03 (`Graph/LWVocab`): records, values, molecules, counters, packed graphs, nested graphs
#check @RBM.Graph.LData
#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.term
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.counters
#check @RBM.Graph.LGraph.adj
#check @RBM.Graph.LGraph.molGraph
#check @RBM.Graph.LGraph.Mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.IsExtMol
#check @RBM.Graph.LGraph.InsideMol
#check @RBM.Graph.LGraph.molSolid
#check @RBM.Graph.LGraph.nM_eq_card
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.scalingSize
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.Counters
#check @RBM.Graph.ord
#check @RBM.Graph.one_le_pow_mul_sq_iff
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
#check @RBM.Graph.PGraph.val_of_factor
#check @RBM.Graph.LGraph.pack
#check @RBM.Graph.NGraph
#check @RBM.Graph.NGraph.WalkOK
#check @RBM.Graph.NGraph.Visits
#check @RBM.Graph.NGraph.IsNested
#check @RBM.Graph.NGraph.NoGhost
#check @RBM.Graph.NGraph.ordN
#check @RBM.Graph.NGraph.val
#check @RBM.Graph.figGraph
#check @RBM.Graph.figGraph_counters
#check @RBM.Graph.figGraph_ord
#check @RBM.Graph.figAux
#check @RBM.Graph.figAux_nested
#check @RBM.Graph.figAux_ord
-- LW-08 (`Graph/LWLvl1`), LW-05 (`Graph/LWWeightExp`)
#check @RBM.Graph.LGraph.LocStd
#check @RBM.Graph.PGraph.LocStd
#check @RBM.Graph.owx_molGraph_adj
-- LW-10a (`Graph/LocalRegular`)
#check @RBM.Graph.localReg_StepWalk
#check @RBM.Graph.localReg_StepWalk.Visits
#check @RBM.Graph.localReg_stepEdges
#check @RBM.Graph.LGraph.localReg_molEdgeMS
#check @RBM.Graph.LGraph.molNV_le_molNW_add_one
#check @RBM.Graph.PGraph.LocReg2
#check @RBM.Graph.PGraph.LocReg3
#check @RBM.Graph.PGraph.LocReg4
#check @RBM.Graph.PGraph.LocReg5
#check @RBM.Graph.PGraph.LocReg345
#check @RBM.Graph.PGraph.LocReg6 -- not used by T2170 (property (6), LW-10c pending; DECISIONS §47)
#check @RBM.Graph.LGraph.localReg_molOf_isolated
-- LW-10b (`Graph/LocalRegular2`)
#check @RBM.Graph.lw_localregular_upto5
#check @RBM.Graph.PGraph.PathInv2.locReg345
#check @RBM.Graph.localReg2_inst_Q
#check @RBM.Graph.localReg2_inst_Q_locStd
#check @RBM.Graph.localReg2_inst_Q_locReg345
#check @RBM.Graph.localReg2_inst_expansion
#check @RBM.Graph.lwSampleData
-- LW-09 (`Graph/LWSizeClaim`): decay of `S`, `S^±`, the peeling bound, the molecular forest, `claim:size`, tails, data
#check @RBM.Graph.lwSmat
#check @RBM.Graph.lwSpOf
#check @RBM.Graph.lwBdist
#check @RBM.Graph.lwBdist_comm
#check @RBM.Graph.lwSpOf_decay
#check @RBM.Graph.LWKBound
#check @RBM.Graph.lwKBound_of_decay
#check @RBM.Graph.lwSpOf_decay_E
#check @RBM.Graph.lwSplus_decay
#check @RBM.Graph.lwForest_sum_le
#check @RBM.Graph.LGraph.exists_forest
#check @RBM.Graph.lwWVal
#check @RBM.Graph.LGraph.term_norm_le
#check @RBM.Graph.LGraph.waved_sum_le
#check @RBM.Graph.LGraph.counters_le
#check @RBM.Graph.LGraph.sizeConst
#check @RBM.Graph.lwClaimSize
#check @RBM.Graph.lwKernel_tail
#check @RBM.Graph.lwTail_log32
#check @RBM.Graph.lwSpOf_tail_E
#check @RBM.Graph.lwSizeD0
#check @RBM.Graph.lwSizeEll
-- lattice, blocks (`def: BM2`), constants
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_add_le
#check @RBM.zdistD_neg
#check @RBM.Gauss.Idx
#check @RBM.Gauss.split
#check @RBM.Gauss.Iblk
#check @RBM.Gauss.card_Iblk
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.Sizes.STblk
#check @RBM.expC
#check @RBM.mE
-- downstream pins (LW-P `Graph/LWPins`): the consumers of the nested form and of `GtoAG`
#check @RBM.Gauss.Sizes.LWClass
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWLoop2
#check @RBM.Gauss.Sizes.LWAnpKey
#check @RBM.Gauss.Sizes.LWAnpKeyGh
#check @RBM.Gauss.Sizes.LWAnp
#check @RBM.Gauss.Sizes.LWMoment
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.LWtermEXP

/-! ## 2. Pinned vocabulary and statements (T2170 targets 1-5; defined in `RBM.Graph` verbatim) -/

noncomputable section

namespace RBM.Graph.T2170Check

open RBM RBM.Gauss RBM.Graph

section Vocab

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The internal molecules** (`def_poly`, `7_8:172`): the vertices `[α_i]`, `i ∈ ⟦q⟧`, of the auxiliary graph
(`def_auxgraph`, `7_8:896`); `q = n_M` (`LGraph.nM_eq_card`). -/
abbrev LGraph.AuxIMol (Γ : LGraph E I) : Type := {c : Γ.Mol // ¬ Γ.IsExtMol c}

open Classical in
/-- **The block of a molecule in the auxiliary graph** (`def: BM2`, `def_auxgraph`, `7_8:863-869`, `7_8:896`): for an
external molecule `c`, `be a` at the chosen external vertex `a` with `molOf (inl a) = c` (the convention `α_x ≡ x`,
`α_y ≡ y`); for an internal molecule, the block `b c` of its centre. -/
def LGraph.auxLab {κ : Type} (Γ : LGraph E I) (be : E → κ) (b : LGraph.AuxIMol Γ → κ) (c : Γ.Mol) : κ :=
  if h : Γ.IsExtMol c then be (Classical.choose h) else b ⟨c, h⟩

open Classical in
/-- **The value of the auxiliary graph** (`def_auxgraph`, `7_8:894-903`; `ValG` for `𝒢^aux`): every solid edge between
different molecules (`molSolid`, the molecular graph `𝒢_ℳ` of `def_poly`) is an edge `ξ([α_i], [α_j])` between the blocks
of its two molecules; the blocks of the internal molecules are summed over `κ` (`κ = Zd d L` for `def: BM2`), the
external ones are `be`. -/
def LGraph.auxVal {κ : Type} [Fintype κ] (Γ : LGraph E I) (ξ : κ → κ → ℝ) (be : E → κ) : ℝ :=
  haveI : Fintype (LGraph.AuxIMol Γ) := Fintype.ofFinite _
  ∑ b : LGraph.AuxIMol Γ → κ,
    (Γ.molSolid.map fun e => ξ (LGraph.auxLab Γ be b e.src) (LGraph.auxLab Γ be b e.dst)).prod

/-- **`(eq:ordGaux)`** (`7_8:902`): `ord(𝒢^aux) = #solid edges - 2 #internal vertices`, the merged `ord` with
`n_W = 0`, `n_V = n_M` (the form of `NGraph.ordN`). -/
def LGraph.auxOrd (Γ : LGraph E I) : ℤ := ord ⟨Γ.molSolid.length, 0, Γ.nM, 0, 0, 0⟩

end Vocab

/-- **Target 2** (`7_8:926`): the identity `ord(Γ) - ord(Γ^aux) = (n_S - |𝒢_ℳ|) + 2 (n_W - n_V + n_M)`,
`|𝒢_ℳ| ≤ n_S`, and `ord(Γ^aux) ≤ ord(Γ)` for a normal graph.  T2170 proves it as three theorems
(`LGraph.scalingOrder_sub_auxOrd`, `LGraph.molSolid_length_le`, `LGraph.auxOrd_le_scalingOrder`). -/
def AuxOrdPin : Prop :=
  ∀ {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I),
    Γ.scalingOrder - LGraph.auxOrd Γ =
        ((Γ.nS : ℤ) - (Γ.molSolid.length : ℤ)) + 2 * ((Γ.nW : ℤ) - (Γ.nV : ℤ) + (Γ.nM : ℤ)) ∧
      Γ.molSolid.length ≤ Γ.nS ∧ (Γ.Normal → LGraph.auxOrd Γ ≤ Γ.scalingOrder)

/-- **Target 3, `GtoAG`** (`7_8:907-928`, `(G_by_auxG)`), deterministic form: for a normal graph whose distinct external
vertices lie in distinct molecules, data with `M = m I`, entries `|G_{xy}| ≤ Ψ` (`x ≠ y`), `|G_{xx} - m| ≤ Ψ`, the decay
`(eq:estSpm-W)` of `S`, `S^±`, the window `W^{-d/2} ≤ Ψ`, and edge variables `ξ ≥ 0` on the blocks that dominate the
off-diagonal entries on the block balls of radius `R ≥ |E ⊕ I| r` (`(yixi)`, `(eq:Gbyxi)`):
`|Γ| ≤ C_Γ Ψ^{ord(Γ) - ord(Γ^aux)} (W^d)^{n_M} Γ^aux_{[ℓe]} + e^{-cr/2} C'_Γ size(Γ)`. -/
def LWGtoAG (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal → (∀ a b : E, Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) → a = b) →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ →
      0 ≤ r → (Fintype.card (E ⊕ I) : ℝ) * r ≤ R →
      (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), x ≠ y →
        (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R → (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R →
        ‖D.G x y‖ ≤ ξ a b) →
      ∀ ℓe : E → Idx d L W,
        ‖Γ.val D ℓe‖ ≤
          Γ.sizeConst C (C * expC (d - 2) c) * Ψ ^ (Γ.scalingOrder - LGraph.auxOrd Γ) *
              (((W : ℝ) ^ d) ^ Γ.nM * LGraph.auxVal Γ ξ (fun a => (split d L W (ℓe a)).1)) +
            Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L

/-- **Target 4, `scalemole` for two external vertices in one molecule** (`7_8:190-193`, deterministic): if `a`, `b` lie
in one molecule and their labels are at block distance `> |E ⊕ I| r`, the value is at most the tail
`e^{-cr/2} C'_Γ size(Γ)` (the outputs with `𝓜_x = 𝓜_y` under `(eq:far_ab)`, `7_8:96`). -/
def LWScalemole (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L W : ℕ) [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    (Γ : LGraph E I), Γ.Normal →
    ∀ (D : LData (Idx d L W)) (m : ℂ) (Ψ C c r : ℝ),
      (∀ x y, D.M x y = if x = y then m else 0) →
      (∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) → (∀ x, ‖D.G x x - m‖ ≤ Ψ) →
      0 ≤ C → 0 < c →
      (∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      (∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) →
      0 ≤ r →
      ∀ (ℓe : E → Idx d L W) (a b : E), Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b) →
        (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ) →
        ‖Γ.val D ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L

/-- **Target 5, the nested form of `Γ^aux`** (`7_8:953-958`; the input of `LWAnp`): for a packed graph with the walks of
`lem:localregular` (3)-(5) and `𝓜_x ≠ 𝓜_y` (`(eq:far_ab)`, `7_8:792`), a nested graph with `p` paths and `q = n_M`
internal vertices, without ghost edges, of order `ord(Γ^aux)`, whose value at `a_i = [x]`, `b_i = [y]` is the value of
the auxiliary graph for every symmetric `ξ` (`7_8:898`). -/
def LWAuxNested : Prop :=
  ∀ (p : ℕ) (Q : PGraph (Fin 2)), 0 < p → Q.LocReg345 p →
    Q.g.molOf (Sum.inl (Q.ext 0)) ≠ Q.g.molOf (Sum.inl (Q.ext 1)) →
    ∃ Γa : NGraph p Q.g.nM, Γa.NoGhost ∧ Γa.IsNested ∧ Γa.ordN = LGraph.auxOrd Q.g ∧
      ∀ {κ : Type} [Fintype κ] (ξ : κ → κ → ℝ), (∀ u v, ξ u v = ξ v u) → ∀ be : Q.E' → κ,
        Γa.val ξ (fun _ => be (Q.ext 0)) (fun _ => be (Q.ext 1)) = LGraph.auxVal Q.g ξ be

end RBM.Graph.T2170Check

end
