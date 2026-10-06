/-
Release check for T2258 (dispatcher V1, Tue Oct  6 04:40 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §80 (2), §69 A,
§64 (4), §45 O2, §29, §20, §17, §16).  S3-12c2 (ST-3, non-alternating chain, fourth of four after the §80 split;
S3-12c1 = T2246 merged 0f60da2): the lift of the per-time R2* endpoint `RBM.Ind.stOeqNQPT''_holds` to the merged
uniform pin `RBM.Gauss.Sizes.STOeqNQ''` by the monotone envelope `X♯` of the controls, a one-sided continuity net
(floor net point) and a time modulus of `𝒦^{(k)}` (supervisor `docs/supervisor/2026-10-05-1955.md` A2, A3 G3, A4).
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 24b85cd).
Section 2: the vocabulary `nqFlowSharp` (the new file defines `RBM.Ind.nqFlowSharp` with exactly this body).
Section 3: the pinned statements (public and private theorems of the new file) as `Prop`s.
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2258-check.lean`.
-/
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.ContinuityNet
import RBM3D.Induction.LemDecCalELip
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins
import RBM3D.Gauss.Domination
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLTreeDeriv
import RBM3D.Loop.KBound
import RBM3D.Loop.TreeRep
import RBM3D.Loop.Unique
import Mathlib.Analysis.Calculus.MeanValue

/-! ## 1. Merged names -/

-- the pin being proved, the per-time input, and their vocabulary (`Induction/NQEndFlow` 0f60da2)
#check @RBM.Gauss.Sizes.STOeqNQ''
#check @RBM.Gauss.Sizes.STNQConcl''
#check @RBM.Gauss.Sizes.STNQConclPT''
#check @RBM.Gauss.Sizes.STOeqNQPT''
#check @RBM.Ind.stOeqNQPT''_holds
#check @RBM.Gauss.Sizes.stOeqNQ''_of_stOeqNQ'
#check @RBM.Ind.NQEndFlowInst.inst_OeqNQPT''
-- the setting (`Induction/Step34Pins` fc76526, `Induction/Defs` 64bdfd3, `Induction/ScaleFacts` 5d1e6b1)
#check @RBM.Gauss.Sizes.STIngR
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STPair
#check @RBM.Gauss.Sizes.STlenL
#check @RBM.Gauss.Sizes.STXiL
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STbootRHS
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.STBctl_mono
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Gauss.Sizes.ST_mE_im_ge
#check @RBM.Gauss.etaT
#check @RBM.norm_mSigma
-- `≺`, per-time `≺` (`Defs/StochDomAt` 9e2b00f)
#check @RBM.StochDomAt
#check @RBM.badSetAt
#check @RBM.StochDomAt.of_subset
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Path.stochDomAt_of_perTimeDomAt
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.PrecPT
#check @RBM.Gauss.Sizes.prec_of_le
#check @RBM.Gauss.Sizes.precPT_of_le
#check @RBM.Gauss.Sizes.tendsto_size
-- the net lift and its inputs (`Induction/ContinuityNet` 5b6cbc1, `Gauss/Domination` 1c2e756)
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.ContinuityNet.contGood
#check @RBM.Ind.ContinuityNet.cont_highProbAt_good
#check @RBM.Ind.ContinuityNet.cont_Bctl_eq
#check @RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl
#check @RBM.Ind.ContinuityNet.cont_Bctl_ratio
#check @RBM.Gauss.netSize
#check @RBM.Gauss.netSize_pos
#check @RBM.Gauss.rpow_le_netSize
#check @RBM.Gauss.netPt
#check @RBM.Gauss.netPt_mem_Icc
#check @RBM.Gauss.exists_netPt_close
#check @RBM.Gauss.card_net_le
-- the loop modulus on the good event (`Induction/LemDecCalELip` e4126a2)
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_norm
#check @RBM.Gauss.Sizes.LemDecCalELip_Lloop_sub
#check @RBM.Gauss.Sizes.LemDecCalELip_STKloop_two_sub
-- the `𝒦` modulus (G3): tree equations, the uniform crude bound, cut lengths (`Loop/KLTreeDeriv` e2aa5fe,
-- `Loop/KLFinal` 471b643, `Loop/KLInduct`, `Loop/KLTree`, `Loop/TreeRep`, `Loop/Unique` b06ff9b)
#check @RBM.Loop.KLK_isKLoop
#check @RBM.Loop.IsKLoop
#check @RBM.Loop.treeEqRhs
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLPar
#check @RBM.Loop.KLBoundAt
#check @RBM.Loop.KLbound_holds
#check @RBM.Loop.KLoopBound
#check @RBM.Loop.KLoopBound_KLK
#check @RBM.Loop.LoopIdx.length_cutGlueL
#check @RBM.Loop.LoopIdx.length_cutGlueR
#check @RBM.Loop.norm_SB_apply_le
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow
-- Mathlib: the mean value theorem (`Mathlib.Analysis.Calculus.MeanValue`)
#check @Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
-- instance data
#check @RBM.Gauss.Step34Inst.InstIngConcl
#check @RBM.Gauss.Step34Inst.inst_ing
#check @RBM.Gauss.Step34Inst.sz0_caseI
#check @RBM.Gauss.Step34Inst.sz0_hs0
#check @RBM.Gauss.Step34Inst.sz0_hst
#check @RBM.Gauss.Step34Inst.sz0_ht
#check @RBM.Gauss.Step34Inst.sz0_con
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst

/-! ## 2. Vocabulary

Inside `RBM.Gauss.Sizes.T2258Check`, so that every name resolves as in `Induction/NQEndFlow.lean`.  The new file
defines `RBM.Ind.nqFlowSharp` with exactly this body (script diff). -/

namespace RBM.Gauss.Sizes.T2258Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Path RBM.Gauss
open scoped NNReal ENNReal

/-- **The monotone envelope `X♯`** of a control (supervisor 1955 A2): `X♯(m,n,u) = inf_{u' ∈ [u, t_n]} X(m,n,u')`,
floored at `1` (the floor is inactive for `u ≤ t_n` when `X ≥ 1`; for `u > t_n` the set is empty and `X♯ = 1`).
`1 ≤ X♯ ≤ X`, non-decreasing in `u ≤ t_n`. -/
noncomputable def nqFlowSharp (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ) : ℝ :=
  max 1 (sInf (X m n '' Set.Icc u (t n)))

/-! ## 3. Pinned statements -/

/-- Envelope (a), private `nqLift_sharp_one_le`. -/
def T2258_sharp_one_le : Prop :=
  ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m n : ℕ) (u : ℝ), 1 ≤ nqFlowSharp t X m n u

/-- Envelope (b), private `nqLift_sharp_le`. -/
def T2258_sharp_le : Prop :=
  ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u : ℝ), nqFlowSharp t X m n u ≤ X m n u

/-- Envelope (c), private `nqLift_sharp_mono`. -/
def T2258_sharp_mono : Prop :=
  ∀ (t : ℕ → ℝ) (X : ℕ → ℕ → ℝ → ℝ), (∀ m n u, 1 ≤ X m n u) →
    ∀ (m n : ℕ) (u u' : ℝ), u ≤ u' → u' ≤ t n → nqFlowSharp t X m n u ≤ nqFlowSharp t X m n u'

/-- Envelope (d), private `nqLift_sharp_prec`: the pair hypotheses carry over (one `Prec` event; the left side depends
on the pair only through its first time `q.1.1`). -/
def T2258_sharp_prec : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (X : ℕ → ℕ → ℝ → ℝ) (m : ℕ),
    (∀ m n u, 1 ≤ X m n u) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => X m n q.1.2) →
    Prec sz (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => nqFlowSharp t X m n q.1.2)

/-- Monotonicity of the bootstrap right side in the controls, private `nqLift_bootRHS_mono`. -/
def T2258_bootRHS_mono : Prop :=
  ∀ (lo : ℕ) (XL XL' XLK XLK' : ℕ → ℝ) (B : ℝ) (n_ p : ℕ), 0 < B →
    (∀ m, 0 ≤ XL m) → (∀ m, 0 ≤ XLK m) → (∀ m, XL m ≤ XL' m) → (∀ m, XLK m ≤ XLK' m) →
    STbootRHS lo XL XLK B n_ p ≤ STbootRHS lo XL' XLK' B n_ p

/-- The floor net point, private `nqLift_netPt_floor` (`netPt` at `⌊x · netSize⌋`). -/
def T2258_netPt_floor : Prop :=
  ∀ (A : ℝ) (N : ℕ) (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∃ k : Fin (netSize A N + 1), netPt 1 A N k ≤ x ∧ x - netPt 1 A N k ≤ 1 / (netSize A N : ℝ)

/-- **The one-sided core**, private `nqLift_core_below`: the merged `cont_core` (`ContinuityNet.lean:142`) with
`hclose` asked only for `u' ≤ u` (the floor net point lies below `u`). -/
def T2258_core_below : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ), Tendsto size atTop atTop →
    ∀ (s t : ℕ → ℝ), (∀ n, s n ≤ t n) → (∀ n, t n - s n ≤ 1) →
    ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (ξ ζ : ∀ n, TimeIcc s t n × V n → Ω → ℝ) (A Cv : ℝ),
      0 ≤ A → 0 ≤ Cv →
      (∀ᶠ n : ℕ in atTop, (Fintype.card (V n) : ℝ) ≤ (size n : ℝ) ^ Cv) →
      PerTimeDomAt P size ξ ζ → ∀ Ξ : ℕ → Set Ω, HighProbAt P size Ξ →
      ∀ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) →
      (∀ᶠ n : ℕ in atTop, ∀ (p : TimeIcc s t n × V n) (ω : Ω), ε n ≤ ζ n p ω) →
      (∀ᶠ n : ℕ in atTop, ∀ ω ∈ Ξ n, ∀ u u' : TimeIcc s t n, (u' : ℝ) ≤ (u : ℝ) →
        (u : ℝ) - (u' : ℝ) ≤ (size n : ℝ) ^ (-A) → ∀ v : V n,
          ξ n (u, v) ω ≤ ξ n (u', v) ω + ε n ∧ ζ n (u', v) ω ≤ 2 * ζ n (u, v) ω) →
      StochDomAt P size ξ ζ

/-- **The `𝒦^{(k)}` time modulus (G3)**, public `RBM.Gauss.Sizes.stKloop_lip`: Lipschitz in time with a polynomial
constant, uniformly on `[0, t_n]` with `(1 - t_n)⁻¹ ≤ N`, for every `k ≥ 2` (tree equations `KLK_isKLoop`, mean
value theorem, the uniform crude bound `KLbound_holds`). -/
def T2258_stKloop_lip : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {κ gmax : ℝ}, 0 < κ → 0 < gmax → sz.SizeTendsto →
    ∀ (E t : ℕ → ℝ), (∀ᶠ n in atTop, |E n| ≤ 2 - κ) →
      (∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) → (∀ n, t n < 1) →
      (∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) →
      ∀ k : ℕ, 2 ≤ k → ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ t n → 0 ≤ u' → u' ≤ t n →
        ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
          ‖STKloop sz n (E n) u σ a - STKloop sz n (E n) u' σ a‖ ≤
            ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) * |u - u'|

/-- **Main target**: `RBM.Ind.stOeqNQ''_holds` has exactly this type
(`example : RBM.Gauss.Sizes.T2258Check.T2258_stOeqNQ''_holds := @RBM.Ind.stOeqNQ''_holds`). -/
def T2258_stOeqNQ''_holds : Prop := ∀ d : ℕ, STOeqNQ'' d

/-! ## 4. Well-formedness (Prop-valued, no proof obligation) -/

-- the lifted pin at the merged instance data fits `InstIngConcl` (instance (1))
example : Prop :=
  RBM.Gauss.Step34Inst.InstIngConcl (fun sz E s t => STNQConcl'' sz E s t) RBM.Gauss.SizesInst.sz0
    RBM.Gauss.InductionDefsInst.z0 RBM.Gauss.InductionDefsInst.sInst RBM.Gauss.InductionDefsInst.tInst 1
-- the envelope at the instance window (instance (2))
example : Prop := nqFlowSharp RBM.Gauss.InductionDefsInst.tInst (fun _ _ _ => 1) 0 0 0 = 1
example : Prop :=
  nqFlowSharp RBM.Gauss.InductionDefsInst.tInst (fun _ _ u => 2 + u) 0 0 0 = 2 ∧
    nqFlowSharp RBM.Gauss.InductionDefsInst.tInst (fun _ _ u => 2 + u) 0 0 1 = 1
-- the modulus at the instance flow (instance (3))
example : Prop :=
  ∀ᶠ n in atTop, ∀ u u' : ℝ, 0 ≤ u → u ≤ RBM.Gauss.InductionDefsInst.tInst n → 0 ≤ u' →
    u' ≤ RBM.Gauss.InductionDefsInst.tInst n →
    ∀ (σ : Fin 3 → Bool) (a : Fin 3 → Zd 3 ((RBM.Gauss.SizesInst.sz0).L n)),
      ‖STKloop RBM.Gauss.SizesInst.sz0 n (STflowE RBM.Gauss.InductionDefsInst.z0 n) u σ a -
          STKloop RBM.Gauss.SizesInst.sz0 n (STflowE RBM.Gauss.InductionDefsInst.z0 n) u' σ a‖ ≤
        (((RBM.Gauss.SizesInst.sz0).size n : ℕ) : ℝ) ^ (2 * 3 + 2) * |u - u'|
example : Prop :=
  T2258_sharp_one_le ∧ T2258_sharp_le ∧ T2258_sharp_mono ∧ T2258_sharp_prec ∧ T2258_bootRHS_mono ∧
    T2258_netPt_floor ∧ T2258_core_below ∧ T2258_stKloop_lip ∧ T2258_stOeqNQ''_holds

end RBM.Gauss.Sizes.T2258Check
