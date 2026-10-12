/-
Release check for T2460 (dispatcher V3, Mon Oct 12 14:45 UTC 2026; DECISIONS §268).  Sub-stage T producer P1 (BA; U-D T2452, D3 (i)): the untwisted BA
grid pin `STGridMartgL` at `baStep2Mat`, from TL's `baTwistGridMart_holds` (`BA/TwistStep.lean:73`) and three identities at
`c₁ = c₂`, in the new file `BA/GridMartBA.lean` (outside the certificate lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2460_`; content binding).  `T2460_Bridge` is the
U-D probe's `T2452_Bridge` (`t/T2452:RBM3D/Probe/T2452Pins.lean:229-239`, commit 20d5f15) verbatim; `T2460_GridMart` is the
conclusion of the probe's `T2452_bridge_holds` (`:308-309`); `T2460_GridRepN2` is conditional (ticket target 4, dispatcher
note (3)).  Then shapes (not binding).  Part 3: the band twins and the `m = 2` readers.
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2460-check.lean
-/
import RBM3D.BA.TwistStep
import RBM3D.BA.EMn2BA
import RBM3D.BA.KInduct
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.OptL2b
import RBM3D.Induction.Step5Pins
import RBM3D.Induction.PfStep5
import RBM3D.Path.DifREP3

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the generic grid pins over a carrier (T8b) and their vocabulary
#check @RBM.BA.Step2Mat
#check @RBM.BA.Step2Data
#check @RBM.BA.FlowFM
#check @RBM.BA.STGridMartAtgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
#check @RBM.BA.STgAg
#check @RBM.BA.STgDriftg
#check @RBM.BA.STLKMg
#check @RBM.BA.STthetaOpg
#check @RBM.BA.STELKLKMg
#check @RBM.BA.STEGtMg
#check @RBM.BA.STEEkMg
#check @RBM.BA.STEEMg
#check @RBM.BA.STgANg
#check @RBM.BA.STgDriftNg
#check @RBM.BA.STLKIMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.bandStep2_STGridMartAt
#check @RBM.BA.bandStep2_STGridMart
#check @RBM.BA.bandStep2_STGridRepNAt
#check @RBM.BA.bandStep2_STGridRepN
#check @RBM.BA.AvecNg_two
#check @RBM.BA.Step2Gen_USemigroup
-- the BA carrier, data and flow
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baStep2Mat_Hpath
#check @RBM.BA.baStep2Mat_Pp
#check @RBM.BA.baStep2Data
#check @RBM.BA.baStep2Data_toFlowFM
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAmF
#check @RBM.BA.BAMfine
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAReal
#check @RBM.BA.BAMB
#check @RBM.BA.BAMss
#check @RBM.BA.BATheta
#check @RBM.BA.BAKsol
#check @RBM.BA.BAuKer
#check @RBM.BA.BAUN
-- TL's twisted grid pin (4 (b)) and its parts: the input
#check @RBM.BA.BATwistGridMartAt
#check @RBM.BA.BATwistGridMart
#check @RBM.BA.baTwistGridMart_holds
#check @RBM.BA.BATwistGridRem
#check @RBM.BA.BATwistGridTail
#check @RBM.BA.BATwistGridWTail
#check @RBM.BA.BATwistGridAssemble
#check @RBM.BA.baTwistGridRem_holds
#check @RBM.BA.baTwistGridTail_holds
#check @RBM.BA.baTwistGridWTail_holds
#check @RBM.BA.baTwistGridAssemble_holds
#check @RBM.BA.baTwistGrid_decomp
-- TL's twisted vocabulary (the left sides of H1-H3; the one-slot kernel of clause (iv))
#check @RBM.BA.twAk
#check @RBM.BA.twMartInc
#check @RBM.BA.twDriftk
#check @RBM.BA.twEEk
#check @RBM.BA.twEEUk
#check @RBM.BA.twMart
#check @RBM.BA.twRem
#check @RBM.BA.twL2M
#check @RBM.BA.twDriftM
#check @RBM.BA.twB1M
#check @RBM.BA.twB2M
#check @RBM.BA.twEGM
#check @RBM.BA.twDerM
#check @RBM.BA.twEEM
#check @RBM.BA.twU
#check @RBM.BA.twEEUM
#check @RBM.BA.twLoopX
#check @RBM.BA.twChg
#check @RBM.BA.twL2'
#check @RBM.BA.twK
#check @RBM.BA.twMB
#check @RBM.BA.twMB_ba
-- the kernel and `𝒦^{(2)}` facts for H1-H2
#check @RBM.BA.twTheta_eq_thetaKer
#check @RBM.BA.twU_eq_uKer
#check @RBM.BA.Step2Kern_thetaKer_BA
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.baKsol_two
#check @RBM.BA.EMn2BA_K_two
#check @RBM.Gauss.loopFine
#check @RBM.Loop.KLloopOf
-- the instance data (target 5)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
-- path vocabulary
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.pathH
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding): the three identities at `c₁ = c₂ = a 1` (H1 observable, H2 drift, H3′ quadratic variation, an inequality since Amend 1), for
the grid indices `k ≤ K n`, eventually in `n` along a BA flow.  The U-D probe's `T2452_Bridge`
(`t/T2452:RBM3D/Probe/T2452Pins.lean:229-239`) with its third conjunct amended (T2460 Amend 1): the equality H3 is false
(cross terms in `twEEk`), the inequality with the slot count 2 is sharp. -/
def T2460_Bridge (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
      ∀ᶠ n : ℕ in atTop, ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), ∀ k ≤ K n, ∀ ω : PathΩ sz,
        twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 1) (a 1) k ω (a 0) =
            STgAg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          twDriftk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω =
            STgDriftg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s t K n σ a k ω ∧
          ‖twEEk sz (BAflowLam0 sz z) (BAflowEs sz z) s t K n σ (a 0) (a 1) (a 1) k ω‖ ≤
            2 * ‖STEEMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s t K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s t K n k ω) σ a‖

/-- **Target 2** (content binding): the untwisted BA grid pin, `STGridMartgL` (`Chain/Step2Gen.lean:882`) at the BA matrix carrier
along the flow; the conclusion of the probe's `T2452_bridge_holds` (`:308-309`) and U-D D6's `baGridMart_holds` (`:193`).  For
every `d`. -/
def T2460_GridMart (d : ℕ) : Prop :=
  STGridMartgL d BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

/-- **Target 4** (content binding if the row keeps it; dispatcher note (3)): the loop-length-2 list form, all four clauses,
the shape U5 assumes (`docs/tickets/checks/T2459-check.lean:225`). -/
def T2460_GridRepN2 (d : ℕ) : Prop :=
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    STGridRepNAtgL d 2 C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

-- Shape (T1's reading, `Step2Iterate:289, 705, 1399`): the constant-level pin that T1 obtains from target 2.
example : Prop := ∀ d : ℕ, T2460_GridMart d →
  ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAtgL d C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

-- Shape (route of target 2; kept private in the new file, premise scan): the glue of the probe's `T2452_bridge` (`:241-306`).
example : Prop := ∀ (d : ℕ) (C₀ : ℝ), T2460_Bridge d → BATwistGridMartAt d C₀ →
  STGridMartAtgL d C₀ BAFlow (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

-- Shape (target 5 (c)): target 2 read at the projections of `baStep2Data` (`BA/Step2BA.lean:123-129`; definitional).
example : Prop := ∀ d : ℕ,
  STGridMartgL d (fun sz κ ε 𝔠 𝔡 z => (baStep2Data sz z).flowOK κ ε 𝔠 𝔡) (fun sz z => (baStep2Data sz z).toStep2Mat)
    (fun sz z => (baStep2Data sz z).T0)

-- Shapes (target 4 (a)): the loop-length-2 list identities at the BA carrier (twins of `STgA_eq_STgAN`, `STgDrift_eq_STgDriftN`,
-- `STEEM_eq_STeeM`, `Induction/Step2Iterate.lean:1602, 1709, 1698`).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz),
  STgAg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgANg (baStep2Mat sz lam0 E) s t K n σ a k ω

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz),
  STgDriftg (baStep2Mat sz lam0 E) s t K n σ a k ω = STgDriftNg (baStep2Mat sz lam0 E) s t K n σ a k ω

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
  STEEMg (baStep2Mat sz lam0 E) n u H σ a = STeeMg (baStep2Mat sz lam0 E) n u H σ a a

-- Shape (1a item (iv), target 4 (b); the comparison, not a claim): TL's clause (iv) weights the increments in one slot (`twU`,
-- `BA/TwistGrid.lean:105`; `BA/TwistGrid2.lean:214-221`), clause 4 of `STGridRepNAtgL` in both slots (`Step2Gen_UN`,
-- `Chain/Step2Gen.lean:202, 1017-1028`).  The equation below, at `c₁ = c₂ = a 1`, is what an identity route would need; the
-- dispatcher's reading is that it fails in general (the right side also moves slot 1).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (σ : Fin 2 → Bool) (v w : ℝ)
    (X : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)),
  (twU sz lam0 E n σ v w *ᵥ fun b => X ![b, a 1]) (a 0) = Step2Gen_UN (baFM sz lam0 E) n σ v w X a

-- Shape (target 5): the BA flow datum of the instances, the statements of `flow_sz0` and `half_lt_t0`.
open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst in
example : Prop := BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq ∧ ∀ n : ℕ, (1 / 2 : ℝ) < BAflowT0 sz0 zSeq n

-- Shape (target 5 (a), (b)): the two binding targets at `d = 3`.
example : Prop := T2460_Bridge 3 ∧ T2460_GridMart 3

end RBM.BA

end

/-! ## Part 3: the band twins and the `m = 2` readers (unchanged; not edited) -/

-- the band pins and their producers (`Path/DifREP2-3`)
#check @RBM.Gauss.Sizes.STGridMartAt
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Ind.stGridMart_holds
#check @RBM.Ind.stGridMartAt_holds
#check @RBM.Ind.stGridRepN_holds
#check @RBM.Ind.GridRepWTailNAt
#check @RBM.Ind.gridRepWTailN_holds
-- the loop-length-2 bridge and its identities (`Induction/Step2Iterate.lean:1586-1752`)
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.STLKM_eq_STLKIM
#check @RBM.Gauss.Sizes.STgA_eq_STgAN
#check @RBM.Gauss.Sizes.STgDrift_eq_STgDriftN
#check @RBM.Gauss.Sizes.STEEM_eq_STeeM
-- readers, all at `m = 2`: T1 (`hmart`, `hMart`), OptL2, U4s3's conclusion, U5's template
#check @RBM.Gauss.Sizes.ST_selfImprove_section
#check @RBM.Gauss.Sizes.ST_selfImprove
#check @RBM.Gauss.Sizes.ST_step2_of_pins
#check @RBM.Gauss.Sizes.stOptL2_of_pins
#check @RBM.Gauss.Sizes.STDuhamelConcl
#check @RBM.Gauss.Sizes.PfStep5_walk_pin
#check @RBM.Gauss.Sizes.pfStep5_walk
