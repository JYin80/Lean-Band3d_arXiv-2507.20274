/-
Release check for T2489 (dispatcher V3, 2026-10-13 04:47 UTC; DECISIONS §292).  BA-L L4b2 `Graph/BAExp14b2`, `BAExp14b2B`: the proof of the merged
pin S2 `BAExp14bS2` (L4b1 = T2434, `Graph/BAExp14b.lean:170`), the eight twisted families `D1t, D2t, T2a, T2b, T3B^{(k)}, T3C-Ḡ^{(k)}`
of `lem:LWterm_EXP` at BA; the twisted twin of `lwExpI1K_holds`, `lwExpI23K_holds`, `lwExpI41K_holds` (`Graph/LWExpTerm4.lean:903, 1316,
1618`) with `(twL2', twK, twTr)` for `(𝓛^{(2)}, 𝒦^{(2)}, Tr(G̊E))`.  No design gate, no probe step.
Part 1: merged names (band basis, the S2 pin and its block forms, the TL pins and their producers, K12, the L4a toolbox, the carrier,
the consumer's inputs, the instance data).  Part 2: the binding target (prefix `T2489_`; content binding up to the name), then shapes
(not binding; fixed at the 1a / start of the 1b).
Merged names only.  No proofs.
Run: lake env lean docs/tickets/checks/T2489-check.lean
-/
import RBM3D.Chain.Carrier
import RBM3D.Chain.LWGen
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenSchur
import RBM3D.BA.KBound
import RBM3D.BA.TwistPins
import RBM3D.BA.TwistFold2
import RBM3D.BA.TwistAvgB
import RBM3D.BA.TwistStep2
import RBM3D.BA.TwistLoop
import RBM3D.BA.TwistChain
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWExpTerm4
import RBM3D.Graph.BAExp14a
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAExp14b
import RBM3D.Graph.BAExp14bB
import RBM3D.Graph.BAExp14e

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band pins and proofs this row twins (`Graph/LWExpTerm2.lean:70-127`, `Graph/LWExpTerm4.lean` §3, §6-§9)
#check @RBM.Gauss.Sizes.LWExpKer
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.lwExpI1K_holds
#check @RBM.Gauss.Sizes.lwExpI23K_holds
#check @RBM.Gauss.Sizes.lwExpI41K_holds
#check @RBM.Gauss.Sizes.lwExpTerm4_ward2
#check @RBM.Gauss.Sizes.lwExpTerm4_L3
#check @RBM.Gauss.Sizes.lwExpTerm4_kward
-- L4b1 = T2434 (`Graph/BAExp14b`, `BAExp14bB`): the pin S2, its integrand, the eight block forms and the tools they read
#check @RBM.BA.BAExp14bS2
#check @RBM.BA.BAExp14bS2Fam
#check @RBM.BA.BAExp14b_FS2
#check @RBM.BA.BAExp14b_BS2
#check @RBM.BA.BAExp14b_FS2_block
#check @RBM.BA.BAExp14bS2Fam_block
#check @RBM.BA.BAExp14b_FD1t_block
#check @RBM.BA.BAExp14b_FD2t_block
#check @RBM.BA.BAExp14b_FT2a_block
#check @RBM.BA.BAExp14b_FT2b_block
#check @RBM.BA.BAExp14b_FT3B_block
#check @RBM.BA.BAExp14b_FT3CG_block
#check @RBM.BA.BAExp14b_twLoopX_twL2'
#check @RBM.BA.BAExp14b_Wk_blk
#check @RBM.BA.BAExp14b_twTie_ba
#check @RBM.BA.BAExp14b_L2_eq
#check @RBM.BA.BAExp14b_L3_eq
#check @RBM.BA.BAExp14b_MB
#check @RBM.BA.BAExp14b_om
#check @RBM.BA.BAExp14b_kap
-- the other inputs of the L4a2 assembly (merged; this row reads none of them)
#check @RBM.BA.BAExp14aS1
#check @RBM.BA.baExp14a_S1_holds
#check @RBM.BA.BAExp14bS3
#check @RBM.BA.baExp14bS3_holds
#check @RBM.BA.BAExp14bExpand
#check @RBM.BA.baExp14b_expand_holds
#check @RBM.BA.BAExp14bCutConj
#check @RBM.BA.baExp14b_cut_conj
-- TL0 = T2421 (`BA/TwistPins`): the twisted objects, TL1, TL2, the model-free lemmas (L4t absorbed into TL0)
#check @RBM.BA.twBlk
#check @RBM.BA.twShift
#check @RBM.BA.twChg
#check @RBM.BA.twTr
#check @RBM.BA.twTrP
#check @RBM.BA.twLoopX
#check @RBM.BA.twL2'
#check @RBM.BA.twMB
#check @RBM.BA.twK
#check @RBM.BA.twTr_eq
#check @RBM.BA.twMB_ba
#check @RBM.BA.twK_ba
#check @RBM.BA.BATwistAvgLaw
#check @RBM.BA.BATwistLoopLaw
#check @RBM.BA.twFold
#check @RBM.BA.twFold_holds
#check @RBM.BA.twWard
#check @RBM.BA.twWard_holds
#check @RBM.BA.twCirc
#check @RBM.BA.twCirc_holds
#check @RBM.BA.twK_bound
#check @RBM.BA.twK_bound_holds
#check @RBM.BA.twB0_ge_holds
#check @RBM.BA.twEta_ge_holds
-- stage TL (closed, §268): the producers of TL1 (fixed time) and of TL2 (one step, base, chain; per `u` inside BA-V)
#check @RBM.BA.BATwistAvgProd
#check @RBM.BA.baTwistAvgProd_holds
#check @RBM.BA.TwistStep2_tl1
#check @RBM.BA.twSteps
#check @RBM.BA.BATwistLoopStep
#check @RBM.BA.baTwistLoopStep_caseI
#check @RBM.BA.baTwistLoopStep_caseII
#check @RBM.BA.BATwistLoopBase
#check @RBM.BA.baTwistLoopBase_holds
#check @RBM.BA.STG0M
#check @RBM.BA.BAMainIndTL
#check @RBM.BA.BAMLOutTL
#check @RBM.BA.BAChainTL
#check @RBM.BA.baChainTL_holds
-- K12 = T2399 (`BA/KBound`): `𝒦` bound and `𝒦`-Ward at the carrier, unconditional (band `stKbound_of_flow`, `lwExpTerm4_kward`)
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.BAKbound
#check @RBM.BA.BAKward
#check @RBM.BA.baKbound_holds
#check @RBM.BA.baKward_holds
-- L4a = T2418 (`Graph/BAExp14a`, `BAExp14aB`): the `≺` toolbox, `X_c`, the averages `e`, `q`, `R`, the kernels
#check @RBM.BA.BAExp14a_det_iff
#check @RBM.BA.BAExp14a_prec_integral
#check @RBM.BA.BAExp14a_prec_fin
#check @RBM.BA.BAExp14a_floor
#check @RBM.BA.BAExp14a_eta_inv_le
#check @RBM.BA.BAExp14a_t_lt_one
#check @RBM.BA.BAExp14a_eventual_scalars
#check @RBM.BA.BAExp14a_facts_of_flow
#check @RBM.BA.BAExp14a_Facts
#check @RBM.BA.BAExp14a_X
#check @RBM.BA.BAExp14a_X_eq
#check @RBM.BA.BAExp14a_L1_eq
#check @RBM.BA.BAExp14a_e
#check @RBM.BA.BAExp14a_q
#check @RBM.BA.BAExp14a_R
#check @RBM.BA.BAExp14a_e_eq
#check @RBM.BA.BAExp14a_e_bound
#check @RBM.BA.BAExp14a_EGxx
#check @RBM.BA.BAExp14a_theta_l1
#check @RBM.BA.BAExp14a_M_row_l1
#check @RBM.BA.BAExp14a_W_sub_one
#check @RBM.BA.BAExp14a_Wsub_col
#check @RBM.BA.BAExp14a_G_ward
-- BA facts (`BA/GreenSchur`)
#check @RBM.BA.BAflow_real
#check @RBM.BA.BAflow_lam0_window
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAMB_row_l1
-- the carrier, the law-level pins (the seven premises of S2), the cut
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STLocalEntrygL
#check @RBM.BA.LWAvgLawgL
#check @RBM.BA.STLmaxgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STDecaygL
#check @RBM.BA.LWcutg
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baFMz
-- the instance data (`Defs/Sizes` §Inst, `BA/FlowPins` §Inst)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0

/-! ## Part 2: the binding target and shapes (not binding) -/

noncomputable section

namespace RBM.BA.T2489Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- **Target 6** (`baExp14bS2_holds`; content binding; the one conclusion of L4b2): S2 for every `d`, the merged pin `BAExp14bS2`
(`Graph/BAExp14b.lean:170`) unchanged (one text, X1-C4), with its seven premises (the five Step 1/2 pins, `BATwistAvgLaw`,
`BATwistLoopLaw`) inside the def.  This is exactly what the L4a2 assembly (T2490: antecedent of `BALWCutExpTwOfS2`, closure
`baLWCutExpTw_holds`) reads. -/
def T2489_S2 : Prop := ∀ d : ℕ, BAExp14bS2 d

/-- Statement level (not binding): S2 with the S1, S3 pins and the expansion identity (all merged) are the inputs of the L4a2 assembly;
its conclusion is the probe text `BALWCutExpTw` (`t/T2398:RBM3D/Probe/T2398Pins.lean:434-440`, not on `main`; owner T2490), written
out here.  The premise list of S2 is exactly the seven of `BALWCutExpTw`, same order. -/
example : Prop :=
  (∀ d : ℕ, BAExp14aS1 d) → T2489_S2 → (∀ d : ℕ, BAExp14bS3 d) → (∀ d : ℕ, BAExp14bExpand d) →
    ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
        STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
        STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
        PrecL sz μ (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWcutg (baFMz sz z) n (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂μ‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- Statement level (not binding; the TL1 evidence of the dispatcher note): `baTwistAvgProd_holds` gives TL1 at the same `t` from S2's
premises 2 and 3 (`LWAvgLawgL`, `STLmaxgL`), so TL1 is dischargeable through that name; TL2 has no unconditional producer (its producers need
`twSteps`, `STG0M`, `BAMainIndTL`, i.e. BA-V), so it stays an exact-type premise.  The merged S2 text keeps both. -/
example : Prop := (∀ d : ℕ, BATwistAvgProd d) ∧ (∀ d : ℕ, BATwistLoopBase d) ∧ (∀ d : ℕ, BAChainTL d) ∧ T2489_S2

/-- Shape (not binding; target 2, P3 of `T2434-prove.md` (i), T2434 Amend 1 item 4) of the sharp average of the light weight:
`‖𝔼 X_c‖ ≺ B^{3/2}` with **no** `(1 - t)⁻¹` (through `e = t M⁺ e + R`, `BAExp14a_e_eq`, inverted through `ω = Θ^{(+,+)}`, `BAExp14a_theta_l1`;
the Neumann form `BAExp14a_e_bound` carries `(1 - t)⁻¹` and is too weak for the `𝒦`-Ward terms).  Premises 1, 2 of S2 only.  The
helper stays private (the premise scan does not know `LWAvgLawgL`). -/
example : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t →
      PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n c _ => ‖∫ ω, BAExp14a_X sz z n (t n) ω c ∂μ‖)
        (fun n _ _ => (sz.Bctl n (t n)) ^ (3 / 2 : ℝ))

/-- Shape (not binding; target 1 (a)) of the uncircled twisted one-loop of `D1t`, `D2t` (`T2434-prove.md:241`): at the carrier,
`Tr(G P_{ac}) = Tr(Ǧ P_{ac}) + M^{(B)}_{ca}`, i.e. `twTrP n G a c = twTr c a + twMB c a` (`FlowFM.GM = G - M`, `BAMfine_eq`); the charge
`false` through `twChg` and `star`.  TL1 bounds the first summand, `M^{(B)}` is deterministic. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (a c : Zd d (sz.L n)), 0 < ((baFMz sz z).m n).im →
    twTrP n ((baFMz sz z).G n t ω) a c = twTr (baFMz sz z) n t ω c a + twMB (baFMz sz z) n c a

/-- Shape (not binding; target 1 (b)) of the slot-1 circle relation that `T2a` needs (its `Ǧ` sits in slot 1 of `twLoopX`,
`BAExp14b_FT2a_block`; the merged `twCirc` is the slot-2 relation that `T2b`, `T3C-Ḡ` read): for a block-tied `M`,
`Tr((X₁ - M) E_a X₂ P_{c₁c₂}) = Tr(X₁ E_a X₂ P_{c₁c₂}) - W^{-d} M^{(B)}_{c₂a} Tr(X₂ P_{c₁a})`.  The 1a checks the indices at random data
(as `T2398-design.md` §B `conv.py` did for `twCirc`); a different index pattern is a finding, not a stop. -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (X₁ X₂ M : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (MB : Zd d (sz.L n) → Zd d (sz.L n) → ℂ),
    (∀ w γ, M w γ = if (split d (sz.L n) (sz.W n) w).2 = (split d (sz.L n) (sz.W n) γ).2 then
      MB (split d (sz.L n) (sz.W n) w).1 (split d (sz.L n) (sz.W n) γ).1 else 0) →
    ∀ a c₁ c₂ : Zd d (sz.L n), twLoopX n (fun x y => X₁ x y - M x y) X₂ a c₁ c₂ =
      twLoopX n X₁ X₂ a c₁ c₂ - (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * MB c₂ a * twTrP n X₂ c₁ a

/-- Shape (not binding; targets 3-5) of one family of S2 at the blue charge `σc = true` (the red one is `star` of it,
`BAExp14bS2Fam_block`): `‖𝔼 F_j(σ, a, b)‖ ≺ (1 - t)⁻¹ B^{5/2}` for `j : Fin 8` in the order `D1t, D2t, T2a, T2b, T3B^{(0)}, T3B^{(1)},
T3C-Ḡ^{(0)}, T3C-Ḡ^{(1)}`, under the seven premises of S2.  These lemmas stay private; target 6 unions the eight tags
(`BAExp14a_prec_fin`) and adds the red charge. -/
example : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t → BATwistAvgLaw (baFMz sz z) μ t → BATwistLoopLaw (baFMz sz z) μ t →
      ∀ j : Fin 8, PrecL sz μ
        (U := fun n => {_p : Bool × (Zd d (sz.L n) × Zd d (sz.L n)) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
        (fun n p _ => ‖∫ ω, BAExp14b_FS2 sz z n (t n) ω j p.1.1 p.1.2.1 p.1.2.2 ∂μ‖)
        (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

end RBM.BA.T2489Check

end
