/-
Release check for T2435 (dispatcher V3, Mon Oct 12 01:07 UTC 2026; DECISIONS §244).  BA-L L3c3a `BAAuxGraph2`: the BA edge variables ζ,
`(eq:Gbyxi2_BA)` and the bridge to G3/G4 (supervisor 0951 Q3, L4-C8, L4-C9 3; 2149 L6; 2254 G3; design gate "stage G").
Section 1: merged names only.  Section 2: the carrier form of `LWXi` (target 2, statement to be matched up to the name)
and Prop-valued shapes.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2435-check.lean
-/
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWPsi
import RBM3D.Graph.AnpKey6
import RBM3D.Chain.Carrier
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenCore
import RBM3D.BA.GreenOff
import RBM3D.BA.GreenLocal
import RBM3D.BA.Step1Boot
import RBM3D.BA.Ward
import RBM3D.BA.GreenSchur
import RBM3D.BA.EKPins
import RBM3D.BA.CombesThomas

-- Section 1: merged names
-- the band basis (`Graph/AuxGraph2`, T2185)
#check @RBM.Graph.lwXiSq
#check @RBM.Graph.lwXiVar
#check @RBM.Graph.lwXiVar_nonneg
#check @RBM.Graph.lwXiVar_symm
#check @RBM.Graph.lwXi_ward_sum
#check @RBM.Graph.LWXiClaim
#check @RBM.Graph.lwXiClaim_holds
#check @RBM.Graph.LWGbyXi
#check @RBM.Graph.lwGbyXi_holds
#check @RBM.Graph.lwGbyXi_hxi
#check @RBM.Graph.LWEntryPsi
#check @RBM.Graph.lwEntryPsi_holds
#check @RBM.Graph.LWXiRad
#check @RBM.Graph.lwXiRad_holds
#check @RBM.Gauss.Sizes.LWXi
#check @RBM.Gauss.Sizes.LWLoop2
#check @RBM.Gauss.Sizes.LWPsiAll
#check @RBM.Gauss.Sizes.LWAnp
#check @RBM.Graph.lwAnp_holds
-- L3c1 (T2420, `Graph/BAAtom2`): G3 and G4, the consumers of ζ
#check @RBM.Graph.BAGtoAG
#check @RBM.Graph.baGtoAG_holds
#check @RBM.Graph.baGtoAG_E
#check @RBM.Graph.baAuxNested_holds
#check @RBM.Graph.BAAnpAux
#check @RBM.Graph.baAnpAux_holds
-- the BA carrier and the generic light-weight pins (`Chain/Carrier`, `Chain/LWGen`, `BA/LWPinsBA`, `BA/FlowPins`)
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.LWLoop2gL
#check @RBM.BA.PinFam
#check @RBM.BA.bandPin
#check @RBM.BA.baPin
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAGt
-- stage G (`lem_GbEXP_BA`): primed off-diagonal pin and diagonal pin, proved; unprimed pin owed (G7)
#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.GreenCore_decayRHS
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGiiGEX
#check @RBM.BA.baGbEXPii_holds
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.BAGijGEX
-- the uniform `M` facts (C1) and the rate
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAMB_row_l1
#check @RBM.BA.BAMfine_decay
#check @RBM.BA.BAct_rate
-- name-clash witness: no new `BAXi*` name
#check @RBM.BA.BAXi

-- Section 2: target 2 (the carrier form of `LWXi`, `Graph/LWPins.lean:360`) and shapes
noncomputable section

namespace RBM.BA.T2435Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- Target 2 (proposal; the probe step fixes the name): `LWXi` over a carrier `C : FlowFM sz` and a law `μ` (`Prec sz` →
`PrecL sz μ`, `etaT (E n) (t n)` → `C.eta n (t n)`); the rest verbatim. -/
def T2435_LWXigL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n)) (fun n p ω => ξ n p.1 p.2 ω)
      (fun n p _ => Φ n ((zdistInf d (sz.L n) (p.1 - p.2) : ℕ) : ℝ)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)

/-- Target 2, bridge shape: at the band carrier the carrier form should be the merged `LWXi`. -/
example {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  T2435_LWXigL (bandFM sz E) (Sizes.seqP sz) t Φ ξ ↔ LWXi sz E t Φ ξ

/-- Target 3, conclusion shape: the carrier form at the BA data (law `seqP (sz.withLam 0)`, carrier `baFMz`). -/
example {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (Φ : ℕ → ℝ → ℝ)
    (ζ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  T2435_LWXigL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t Φ ζ

end RBM.BA.T2435Check

end
