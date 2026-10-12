/-
Release check for T2434 (dispatcher V3, Mon Oct 12 01:07 UTC 2026; DECISIONS §244).  BA-L L4b1 `BAExp14b`: the `GGGamma` expansion of the BA cut at `α` for
`f = tr(ǦE_{a₁}) G(σ)_{yx}`, the pins S2, S3 (supervisor 0951 L4-C6) and the identity `𝔼 LWcutg = Σ S1 + Σ S2 + Σ S3`.
Section 1: merged names.  Section 2: Prop-valued templates of the target shapes (prefix `T2434_`; the 1a fixes the index types,
integrands and premises; content binding).  Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2434-check.lean
-/
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAExp14a
import RBM3D.Chain.LWGen
import RBM3D.Chain.Carrier
import RBM3D.BA.TwistPins
import RBM3D.Graph.BAGGExp
import RBM3D.Graph.BAExpand
import RBM3D.Graph.BAExpandW
import RBM3D.Graph.BAExpandId
import RBM3D.BA.FlowPins
import RBM3D.BA.MFixedPoint
import RBM3D.BA.GreenSchur
import RBM3D.Defs.Sizes
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWExpTerm4
import RBM3D.Graph.LWExpTerm6

-- Section 1: merged names
-- L4a (T2418, `Graph/BAExp14a`, `BAExp14aB`): S1, its frame, the `W - 1` block form
#check @RBM.BA.BAExp14aS1
#check @RBM.BA.BAExp14aS1Fam
#check @RBM.BA.baExp14a_S1_holds
#check @RBM.BA.BAExp14a_F
#check @RBM.BA.BAExp14a_outer
#check @RBM.BA.BAExp14a_X
#check @RBM.BA.BAExp14a_lanlw_diag
#check @RBM.BA.BAExp14a_int_slice
#check @RBM.BA.BAExp14a_W_sub_one
#check @RBM.BA.BAExp14a_prec_fin
-- L2c2a (T2409, `Graph/BAGGExp`) and the BA expansions (`Graph/BAExpand`, `Graph/BAExpandW`)
#check @RBM.Graph.BAGGGamma
#check @RBM.Graph.BAGGGammaL
#check @RBM.Graph.BAGGGammaR
#check @RBM.Graph.baGGGamma_holds
#check @RBM.Graph.ba_W_sub_one
#check @RBM.Graph.BAlanlw
#check @RBM.Graph.baLanlw_holds
#check @RBM.Graph.BAlwW
#check @RBM.Graph.BAlwf
#check @RBM.Graph.BAlwdf
#check @RBM.Graph.BAExpand_dh_of_partial
#check @RBM.Graph.BAExpand_dh_star_of_partial
#check @RBM.Graph.BAlwData
-- L4d (T2419, `Graph/BAExpandId`): the root of S3's producers (design gate (iii))
#check @RBM.Graph.baG5Graph
#check @RBM.Graph.BAG5Identity
#check @RBM.Graph.baExpandIdentity_holds
-- the carrier, the Step 1/2 pins, TL0 (T2421, `BA/TwistPins`)
#check @RBM.BA.LWcutg
#check @RBM.BA.PrecL
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twTr
#check @RBM.BA.twTrP
#check @RBM.BA.twLoopX
#check @RBM.BA.twMB
#check @RBM.BA.twMB_ba
#check @RBM.BA.twCirc_holds
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BATheta
#check @RBM.BA.BAMfine_eq
-- instance data (as `Graph/BAExp14aB.lean:1741`)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
-- the band twin (`LWExpTerm2`) and the band proofs the producers of S2 (L4b2) and S3 (L4g) transcribe
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.lwExpTerm2_keyQ
#check @RBM.Gauss.Sizes.lwExpTerm2_triple
#check @RBM.Gauss.Sizes.lwExpTerm2_block
#check @RBM.Gauss.Sizes.lwExpTerm2_cut_expand
#check @RBM.Gauss.Sizes.lwExpTerm2_cut_conj
#check @RBM.Gauss.Sizes.lwCutExp_of_terms
#check @RBM.Gauss.Sizes.lwExpI1K_holds
#check @RBM.Gauss.Sizes.lwExpI23K_holds
#check @RBM.Gauss.Sizes.lwExpI41K_holds
#check @RBM.Gauss.Sizes.lwExpG5'_of_expand'

-- Section 2: Prop-valued templates (content binding; the 1a names the integrands `BAExp14bS2Fam`, `BAExp14bS3Fam` and the premises)
namespace T2434Check
open MeasureTheory RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-- The outer form of S2 and S3: that of `BAExp14aS1` (`Graph/BAExp14aB.lean:124`; L4-C6). Binders, range of `t`, law, carrier, `U` and
bound are fixed. `ι` indexes the families, `F` is the integrand (the `σc` convention of `BAExp14aS1Fam`), `Prem` the premises. -/
def T2434_FamShape (d : ℕ) (ι : Type)
    (F : ∀ (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → sz.SeqΩ → ι → Bool → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (Prem : ∀ (sz : Sizes d), (ℕ → ℂ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → Prem sz z t →
      PrecL sz (Sizes.seqP (sz.withLam 0))
        (U := fun n => {_p : ι × (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, F sz z n (t n) ω p.1.1 p.1.2.1.1 p.1.2.1.2 p.1.2.2.1 p.1.2.2.2 ∂(Sizes.seqP (sz.withLam 0))‖)
        (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- The seven premises of `BALWCutExpTw` (`t/T2398:RBM3D/Probe/T2398Pins.lean:434`), as one `Prem`: the most S2, S3 may assume
(L4a2's assembly consumes them under these premises). -/
def T2434_Prem7 {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) : Prop :=
  STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ LWAvgLawgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
    STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
    STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ BATwistAvgLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧
    BATwistLoopLaw (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- S1's integrand and its two premises fit the template (elaboration check only). -/
example (d : ℕ) : Prop :=
  T2434_FamShape d (Fin 6) (fun sz z n t ω k σc σo ac ao => BAExp14aS1Fam sz z n t ω k σc σo ac ao)
    (fun sz z t => STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ∧ LWAvgLawgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t)

/-- The seven premises fit the template as `Prem` (elaboration check only). -/
example (d : ℕ) : Prop :=
  T2434_FamShape d Unit (fun _ _ _ _ _ _ _ _ _ _ => (0 : ℂ)) (fun sz z t => T2434_Prem7 sz z t)

/-- The form of target 2, `BAExp14bExpand d` (quantified as `baExp14a_S1_holds`): the cut in expectation is the sum of the six S1
families and of the S2, S3 families, at every size `n`, time `t ∈ [0, BAflowT0]` and labelling `(σc, σo, ac, ao)`, both charges. -/
def T2434_ExpandShape (d : ℕ) (ι₂ ι₃ : Type) [Fintype ι₂] [Fintype ι₃]
    (F₂ : ∀ (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → sz.SeqΩ → ι₂ → Bool → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (F₃ : ∀ (sz : Sizes d), (ℕ → ℂ) → ∀ n : ℕ, ℝ → sz.SeqΩ → ι₃ → Bool → Bool → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (σc σo : Bool) (ac ao : Zd d (sz.L n)),
      ∫ ω, LWcutg (baFMz sz z) n t σc σo ac ao ω ∂(Sizes.seqP (sz.withLam 0)) =
        (∑ k : Fin 6, ∫ ω, BAExp14aS1Fam sz z n t ω k σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) +
        (∑ j : ι₂, ∫ ω, F₂ sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0))) +
        (∑ j : ι₃, ∫ ω, F₃ sz z n t ω j σc σo ac ao ∂(Sizes.seqP (sz.withLam 0)))

/-- The conjugation the identity uses for `σc = false` (`docs/reports/T2418-prove.md` (d) O4; band `lwExpTerm2_cut_conj`), pathwise. -/
def T2434_CutConj {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : ℝ) (σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ),
    LWcutg (baFMz sz z) n t false σo ac ao ω = star (LWcutg (baFMz sz z) n t true (!σo) ao ac ω)

end T2434Check
