/-
Release check for T2444 (dispatcher V3, Mon Oct 12 07:09 UTC 2026; DECISIONS §254).  BA-L L3c3b `BAZetaExp`: `claim:xi` for the exp class at BA,
twin of `Graph/LWXiExp.lean` `:1-787` (supervisor 0951 Q3 `:113`, L4-C9 3 `:161`; 2149 L7; L3c3a = T2435 merged c43bdf1).
Section 1: merged names only.  Section 2: the carrier form of `LWXiE` (target 1) and the claim at BA (target 2), statements
to be matched up to the name, and Prop-valued shapes.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2444-check.lean
-/
import RBM3D.Graph.LWXiExp
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenLDE
import RBM3D.BA.EKPins

-- Section 1: merged names
-- the band basis (`Graph/LWXiExp`, T2359): statements, the model-free tail and class, the claim
#check @RBM.Graph.LWXiE
#check @RBM.Graph.LWXiExpClaim
#check @RBM.Graph.lwXiExpClaim_holds
#check @RBM.Graph.lwTail32
#check @RBM.Graph.lwXE_phi
#check @RBM.sfT
#check @RBM.tailW
#check @RBM.Gauss.Sizes.LWLoopExp
#check @RBM.Gauss.Sizes.LWAssmExp
-- L3c3a (T2435, `Graph/BAAuxGraph2`, `BAAuxGraph2B`): ζ, its facts, the Ward sum, `LWXigL`, the claim, `(eq:Gbyxi2_BA)`
#check @RBM.Graph.baZetaSq
#check @RBM.Graph.baZetaVar
#check @RBM.Graph.baZetaVar_nonneg
#check @RBM.Graph.baZetaVar_symm
#check @RBM.Graph.baZetaSq_ge_W
#check @RBM.Graph.baZeta_ward_sum
#check @RBM.Graph.LWXigL
#check @RBM.Graph.LWXigL_bandFM
#check @RBM.Graph.BAZetaClaim
#check @RBM.Graph.baZetaClaim_holds
#check @RBM.Graph.BAGbyZeta
#check @RBM.Graph.baGbyZeta_hxi
-- L3c3a's public helpers that replace the band's private copies (`LWXiExp.lean` §4)
#check @RBM.Graph.BAAuxGraph2_zdistInf_tri_real
#check @RBM.Graph.BAAuxGraph2_zdistInf_le_L
#check @RBM.Graph.BAAuxGraph2_zetaSq_nonneg
#check @RBM.Graph.BAAuxGraph2_zetaVar_sq
#check @RBM.Graph.BAAuxGraph2_pair_sum
#check @RBM.Graph.BAAuxGraph2_prec_of_imp
#check @RBM.Graph.BAAuxGraph2_whp_entry
#check @RBM.Graph.BAAuxGraph2_eta_le_one
#check @RBM.Graph.BAAuxGraph2_ev_poly
#check @RBM.Graph.BAAuxGraph2_card_ball
#check @RBM.Graph.BAAuxGraph2_pow_small
#check @RBM.Graph.BAAuxGraph2_rpow_nat
#check @RBM.Graph.BAAuxGraph2_num
#check @RBM.Graph.BAAuxGraph2_zetaSq_le
#check @RBM.Graph.BAAuxGraph2_floorL_le
-- the BA carrier and the generic light-weight pins (`Chain/Carrier`, `Chain/LWGen`, `BA/LWPinsBA`, `BA/FlowPins`)
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.eta
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.baPin
#check @RBM.BA.ba_G_data
#check @RBM.BA.STInitialGT2gL
#check @RBM.BA.LWLoopExpgL
#check @RBM.BA.LWAssmExpgL
#check @RBM.BA.band_LWAssmExp
-- the `d = 3` instance data (`BA/FlowPins.lean` §Inst, `BA/LWPinsBA.lean` §3)
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.BA.FlowPinsInst.flow_sz0
#check @RBM.BA.FlowPinsInst.half_lt_t0
-- name-clash witness: no new `BAXi*` name
#check @RBM.BA.BAXi

-- Section 2: target 1 (the carrier form of `LWXiE`, `Graph/LWXiExp.lean:57`), target 2 (the claim at BA) and shapes
noncomputable section

namespace RBM.BA.T2444Check

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph RBM.BA

/-- Target 1 (proposal): `LWXiE` over a carrier `C : FlowFM sz` and a law `μ` (`sz.Prec` → `PrecL sz μ`,
`etaT (E n) (t n)` → `C.eta n (t n)`); the rest verbatim (the subtype `λ²/L² < 1 - t`, the profile `𝖳_t(|·|_∞ ∧ ℓ) + W^{-D}`). -/
def T2444_LWXiEgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t ℓ : ℕ → ℝ) (D : ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)

/-- Target 1, bridge shape: at the band carrier and the band law the carrier form should be the merged `LWXiE`. -/
example {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  T2444_LWXiEgL (bandFM sz E) (Sizes.seqP sz) t ℓ D ξ ↔ LWXiE sz E t ℓ D ξ

/-- Target 2 (proposal): `claim:xi` for the exp class at the `baPin` data (law `seqP (sz.withLam 0)`, `BAFlow`, `baFMz`,
`BAflowT0`), twin of `LWXiExpClaim` (`LWXiExp.lean:68`): `LWAssmExpgL` in place of `LWAssmExp`, `baZetaVar` at the floor
exponent `D₁ ≥ max (2D) (1/𝔠)` in place of `lwXiVar`; the radius premise verbatim. -/
def T2444_BAZetaExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
            ∀ D₁ : ℝ, max (2 * D) (1 / 𝔠) ≤ D₁ →
              T2444_LWXiEgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ℓ D (baZetaVar sz z t ρ D₁)

/-- Target 2 beside its band original (`lwXiExpClaim_holds : LWXiExpClaim d`) at `d = 3`. -/
example : Prop := LWXiExpClaim 3 ∧ T2444_BAZetaExpClaim 3

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- Target 3, conclusion shape at the `d = 3` data of `BA/LWPinsBA.lean` §3 (`sz0`, `zSeq`, `t ≡ 1/2`, `ℓ ≡ 0`,
`D₁ = max (2D) 6`, `1/𝔠 = 6`). -/
example (D : ℝ) (ρ : ℕ → ℝ) : Prop :=
  T2444_LWXiEgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 0) D
    (baZetaVar sz0 zSeq (fun _ => 1 / 2) ρ (max (2 * D) 6))

/-- Target 3, the hypotheses kept at the instance: `(initialGT2)`, `(LW_assm_exp)` and the entry law. -/
example (Ψ : ℕ → ℝ) : Prop :=
  STInitialGT2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (1 / 10) Ψ ∧
    LWLoopExpgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2) (fun _ => 0) ∧
    PrecL sz0 (Sizes.seqP (sz0.withLam 0)) (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (1 / 2) ω p.1 p.2‖) (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))

end Inst

end RBM.BA.T2444Check

end
