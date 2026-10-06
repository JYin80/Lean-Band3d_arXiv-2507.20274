/-
T2255 (LW-14c) check file: merged names (section 1) and the pin texts of the targets (section 2).
No proofs, no `sorry`, no `by`.  Compiles on `main` (9403c24) as is.
-/
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.AuxGraph2
import RBM3D.Induction.ScaleFacts
import RBM3D.Green.IBPPoly

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names (each in the namespace of its enclosing `namespace … end` block) -/

-- `Graph/LWExpTerm2.lean` (T2243, d6ebc39, `namespace RBM.Gauss.Sizes` `:63`)
#check @RBM.Gauss.Sizes.LWExpKer
#check @RBM.Gauss.Sizes.LWExpKp
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.lwExpTerm2_bl
#check @RBM.Gauss.Sizes.lwExpTerm2_Lloop5
#check @RBM.Gauss.Sizes.lwExpTerm2_Gt_eq_Gsm
#check @RBM.Gauss.Sizes.lwExpTerm2_hS
#check @RBM.Gauss.Sizes.lwExpTerm2_hSp
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_of_eventually
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_SB
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_Kp
#check @RBM.Gauss.Sizes.lwExpTerm2_cut_zero
#check @RBM.Gauss.Sizes.lwExpTerm2_eta_inv_le
#check @RBM.Gauss.Sizes.lwCutExp_of_terms
#check @RBM.Gauss.Sizes.lwExpG5_of_G5'
-- `Graph/LWExpTerm.lean` (T2236, 23d83c4, `namespace RBM.Gauss.Sizes` `:43-1210`)
#check @RBM.Gauss.Sizes.LWCutExp
#check @RBM.Gauss.Sizes.LWExpG5
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut
-- `Graph/LWPins.lean` (975f4ff)
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.Sizes.LWAvgLaw
-- `Graph/LWGGExp.lean` (T2120, 5c69cb4, `namespace RBM.Graph` `:56-1748`)
#check @RBM.Graph.oe2x_integral
#check @RBM.Graph.oe2x_graph_E
#check @RBM.Graph.oe2x_lwG_zero
#check @RBM.Graph.oe2xR1_ord
#check @RBM.Graph.oe2xR2_ord
#check @RBM.Graph.oe2xR4_ord
#check @RBM.Graph.oe2xR5_ord
#check @RBM.Graph.oe2xR6_ord
#check @RBM.Graph.oe2xR7_ord
#check @RBM.Graph.oe2xR8_ord
#check @RBM.Graph.oe2xR1_nM_ge
#check @RBM.Graph.oe2xR2_nM_ge
-- `Graph/LWVocab.lean` (T2050, 37db678, `namespace RBM.Graph` `:67`)
#check @RBM.Graph.LData
#check @RBM.Graph.SEdge
#check @RBM.Graph.WEdge
#check @RBM.Graph.LGraph
#check @RBM.Graph.LGraph.val
#check @RBM.Graph.LGraph.nW
#check @RBM.Graph.LGraph.nM
#check @RBM.Graph.LGraph.mol
#check @RBM.Graph.LGraph.molOf
#check @RBM.Graph.LGraph.Normal
#check @RBM.Graph.LGraph.scalingOrder
#check @RBM.Graph.LGraph.partition
#check @RBM.Graph.LGraph.val_eq_partition
#check @RBM.Graph.LGraph.partition_normal
#check @RBM.Graph.PGraph
#check @RBM.Graph.PGraph.val
-- `Graph/AuxGraph.lean` (T2170, 87cf70c, `namespace RBM.Graph` `:53`)
#check @RBM.Graph.LGraph.auxVal
#check @RBM.Graph.LGraph.auxOrd
#check @RBM.Graph.LWGtoAG
#check @RBM.Graph.lwGtoAG_holds
-- `Graph/AuxGraph2.lean` (T2185, fbaa460, `namespace RBM.Graph` `:56-1500`)
#check @RBM.Graph.lwXiSq
#check @RBM.Graph.lwXiVar
#check @RBM.Graph.lwXi_ward_sum
#check @RBM.Graph.LWGbyXi
#check @RBM.Graph.lwGbyXi_holds
#check @RBM.Graph.lwGbyXi_hxi
-- `Graph/LWSizeClaim.lean` (T2124, dd1748c, `namespace RBM.Graph` `:75`)
#check @RBM.Graph.lwSmat
#check @RBM.Graph.lwSmat_eq
#check @RBM.Graph.lwSpOf
#check @RBM.Graph.lwSpOf_eq
#check @RBM.Graph.LWKBound
#check @RBM.Graph.lwClaimSize
#check @RBM.Graph.lwSplus_decay
-- `Graph/LWStein.lean` (T2060, 89f29cf, `namespace RBM.Graph` `:82-1894`)
#check @RBM.Graph.lwGm
#check @RBM.Graph.lwS
#check @RBM.Graph.lwSplus
#check @RBM.Graph.lwSampleData
-- `Green/IBPPoly.lean` (3b8c687, `namespace RBM.Green` `:49-1157`)
#check @RBM.Green.gaussIBP
-- `Induction/Defs.lean` (64bdfd3, `namespace RBM.Gauss.Sizes` `:57-181`)
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STLocalEntry
-- `Induction/ScaleFacts.lean` (5d1e6b1, `namespace RBM.Gauss.Sizes` `:54-146`); `Defs/Sizes.lean` (`RBM.Gauss.Sizes` `:148-246`)
#check @RBM.Gauss.Sizes.STBctl_ge
#check @RBM.Gauss.Sizes.Bctl
-- `Induction/Step6Kit.lean` (9e0d6a7): downstream consumers of `LWtermEXP`
#check @RBM.Gauss.Sizes.st6_EGtHi_of_LW
#check @RBM.Gauss.Sizes.ST_step6_caseIII_of_pins
#check @RBM.Gauss.Sizes.ST_step6_caseII_of_pins

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

namespace T2255Check

/-! ## Section 2. Pin texts (the file `RBM3D/Graph/LWExpTerm3.lean` states them verbatim without the suffix `Pin`) -/

/-- Target 1 (vocabulary): **the graph `𝒢_xy` of `(eq;I42inG)`** (`B:68`), external vertices `x = inl 0`,
`y = inl 1`, internal `α = inr 0`, `γ = inr 1`, `β = inr 2`:
`S^{(k)}_{γα} S_{αβ} G_{xα} G_{αγ} G_{γβ} G_{βy} · (s ? G_{yx} : Ḡ_{xy})`; the first waved edge is `S` (`k = false`)
or `S⁺` (`k = true`, the `J₄₂` edge of T2243a), the last solid edge carries the charge `s` (`σ_o`, T2243b). -/
def LWG5GraphPin (k s : Bool) : LGraph (Fin 2) (Fin 3) where
  solid := [SEdge.mk true false (Sum.inl 0) (Sum.inr 0), SEdge.mk true false (Sum.inr 0) (Sum.inr 1),
    SEdge.mk true false (Sum.inr 1) (Sum.inr 2), SEdge.mk true false (Sum.inr 2) (Sum.inl 1),
    if s then SEdge.mk true false (Sum.inl 1) (Sum.inl 0) else SEdge.mk false false (Sum.inl 0) (Sum.inl 1)]
  waved := [WEdge.mk k true (Sum.inr 1) (Sum.inr 0), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1

/-- Target 1 (vocabulary): the sample data of `𝒢_xy` at `(E, t)`: `G = G_t` (`lwGm` at `z_t`), `M = m I`,
`S = t · svarF` (`lwS`), `S⁺ = lwSplus` (the data of `oe2x_graph_E`). -/
noncomputable def LWG5DataPin {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) (ω : sz.SeqΩ) :
    LData (Idx d (sz.L n) (sz.W n)) :=
  lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω

/-- Target 1 (vocabulary): every internal molecule of `P` is attached to at least two solid edges between
different molecules (the hypothesis of the Cauchy–Schwarz step `B:84-86`). -/
def LWAttachedPin (P : PGraph (Fin 2)) : Prop :=
  ∀ v : P.I', (∀ w ∈ P.g.mol (Sum.inr v), w.isRight = true) →
    2 ≤ (P.g.solid.filter fun e => decide (P.g.mol e.src ≠ P.g.mol e.dst ∧
      (P.g.mol e.src = P.g.mol (Sum.inr v) ∨ P.g.mol e.dst = P.g.mol (Sum.inr v)))).length

/-- Target 2 (**bridge**, `(eq;I42inG)`): the left side of `LWExpG5'` (before `‖·‖`) is, up to `t^{1}` (`k = true`)
or `t^{2}` (`k = false`), the block average `W^{-2d} Σ_{x∈[a], y∈[b]} 𝔼 𝒢_xy`. -/
def LwExpTerm3BridgePin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool) (a b : Zd d (sz.L n)),
    (t : ℂ) ^ (if k then 1 else 2) * ((((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
        (if k then LWExpKp sz n E t a₁ a₂ else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
        (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
        ∫ ω, Lloop sz n E t ![true, true, true, true, s] ![a₂, a₁, a₃, b, a] ω ∂(sz.seqP)) =
      ((((sz.W n : ℕ) : ℂ) ^ d) ^ 2)⁻¹ *
        ∑ x ∈ Finset.univ.filter (fun x => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a),
          ∑ y ∈ Finset.univ.filter (fun y => lwExpTerm2_bl d (sz.L n) (sz.W n) y = b),
            ∫ ω, (LWG5GraphPin k s).val (LWG5DataPin sz n E t ω) ![x, y] ∂(sz.seqP)

/-- Target 3 (**`(Gammamuxy)`, `q ∈ {0,1}`**, `B:84-90`): for a normal packed graph with at most one internal
molecule, distinct external vertices in distinct molecules, and every internal molecule attached to two solid
edges, `|𝔼 Γ_{xy}| ≺ t^{n_W} η_t⁻¹ (W^{-d}B_{t,0})^{ord(Γ)/2}` (charge-blind; `t^{n_W}` from `S, S⁺ = O(t)`). -/
def LwGraphPrec1Pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → STLmax sz (STflowE z) t →
        ∀ P : PGraph (Fin 2), P.g.Normal → P.g.nM ≤ 1 → LWAttachedPin P →
          (∀ a b : P.E', P.g.molOf (Sum.inl a) = P.g.molOf (Sum.inl b) → a = b) →
          Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p _ => ‖∫ ω, P.val (LWG5DataPin sz n (STflowE z n) (t n) ω) ![p.1, p.2] ∂(sz.seqP)‖)
            (fun n _ _ => (t n) ^ P.g.nW * (etaT (STflowE z n) (t n))⁻¹ *
              (sz.Bctl n (t n)) ^ ((P.g.scalingOrder : ℝ) / 2))

/-- **`LWG5Expand`** (owed, new row LW-14e; `(eq:sizeGammamu_E)`, `B:91-108`): a fixed finite list of packed
graphs (independent of `n`, `E`, `t`; coefficients `c · m^j`) with `𝔼 𝒢_xy = Σ m^j 𝔼 Γ_μ`, each `Γ_μ` normal,
`n_M ≤ 1`, `n_W ≥ 2`, attached, external molecules distinct, `ord ≥ 4·1_{x=y} + 5·1_{x≠y}`. -/
def LWG5ExpandPin (d : ℕ) : Prop :=
  ∃ Ls : Bool → Bool → List (ℕ × PGraph (Fin 2)),
    (∀ k s, ∀ q ∈ Ls k s, q.2.g.Normal ∧ q.2.g.nM ≤ 1 ∧ 2 ≤ q.2.g.nW ∧ LWAttachedPin q.2 ∧
        (∀ a b : q.2.E', q.2.g.molOf (Sum.inl a) = q.2.g.molOf (Sum.inl b) → a = b) ∧
        (if q.2.ext 0 = q.2.ext 1 then (4 : ℤ) else 5) ≤ q.2.g.scalingOrder) ∧
    ∀ (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → 0 < t → t < 1 → ∀ (k s : Bool)
      (x y : Idx d (sz.L n) (sz.W n)),
      ∫ ω, (LWG5GraphPin k s).val (LWG5DataPin sz n E t ω) ![x, y] ∂(sz.seqP) =
        ((Ls k s).map fun q =>
          (mE E) ^ q.1 * ∫ ω, q.2.val (LWG5DataPin sz n E t ω) ![x, y] ∂(sz.seqP)).sum

/-- Target 4 (assembly): the expansion pin gives `LWExpG5'` (both branches, both charges). -/
def LwExpG5'OfExpandPin (d : ℕ) : Prop := LWG5ExpandPin d → LWExpG5' d

/-- Target 5 (conditional, until LW-14d and LW-14e merge): `LWCutExp` and `LWtermEXP`. -/
def LwCutExpOfExpandPin (d : ℕ) : Prop :=
  LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5ExpandPin d → LWCutExp d
def LwTermEXPOfExpandPin (d : ℕ) : Prop :=
  LWExpI1K d → LWExpI23K d → LWExpI41K d → LWG5ExpandPin d → LWtermEXP d

/-! ## Section 3. Instance shapes (`d = 3`; Prop-valued, no proof obligations) -/

example : Prop := LwExpTerm3BridgePin 3
example : Prop := LwGraphPrec1Pin 3
example : Prop := LwExpG5'OfExpandPin 3
example : Prop := LwTermEXPOfExpandPin 3
example : Prop := LWG5ExpandPin 3

end T2255Check

end RBM.Gauss.Sizes
