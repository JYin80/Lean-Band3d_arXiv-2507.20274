/-
Release check for T2463 (dispatcher V3, Mon Oct 12 15:53 UTC 2026; DECISIONS §270).  U U1s1 (ST side, additive): the zero-mode layer of
`Induction/ZeroModeCalc.lean`, `Induction/NewPQ.lean`, `Induction/QopAlgebra.lean` over the carrier, in the new file
`Chain/ZeroModeGen.lean` (reserve `Chain/ZeroModeGenB.lean`); the band files are not edited (outside the certificate lane);
`Induction/QopNorm.lean` is model-free and gets no generic text.  One kernel (supervisor 1152 U-C4): `Step2Gen_UN`,
`Step2Gen_ThetaN`; the `Ugen` bridge is T4s1's `bandStep2_Ugen`.  `lem: newPQ` enters as a model-free Ward expansion plus a
carrier class; T2457's `STNewPQgL` (not merged) is not restated here (ticket, dispatcher note (2)).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2463_`; content binding up to the name), then
shapes (not binding): band route, BA readings (U1-BA's, statement level).  Part 3 (G1): the public names of the four band
files, unchanged.  Part 4: not this row.
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2463-check.lean
-/
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step2Kern
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.QopNorm
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.GLoopFlow
import RBM3D.Loop.KLWard
import RBM3D.Loop.KLUnique
import RBM3D.BA.EKPins
import RBM3D.BA.FlowPins
import RBM3D.BA.KWard
import RBM3D.BA.KSolve
import RBM3D.BA.Ward
import RBM3D.BA.KKernel
import RBM3D.BA.KBase
import RBM3D.BA.EMn2BA
import RBM3D.BA.TwistGrid
import RBM3D.BA.TwistStep2

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier, T8b's one kernel (U-C4) and its band and BA readings
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.baFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.baStep2Mat
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Kern_Mss_band
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Gen_thetaKer
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_ThetaN
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_thetaKer_band
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.Step2Kern_ThetaN_band
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Kern_uKer_BA
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.BAUN
#check @RBM.BA.BAmF
#check @RBM.BA.BAReal
-- T4s1 (merged 4fad610): the semigroup law, the grid vocabulary, pin G1 at one size index, the `Ugen` bridge
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.Step2Gen_UN_add
#check @RBM.BA.Step2Gen_UN_duhamel_telescope
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.AvecNg
#check @RBM.BA.martIncNg
#check @RBM.BA.predIncNg
#check @RBM.BA.bandStep2_AvecN
#check @RBM.BA.bandStep2_martIncN
#check @RBM.BA.bandStep2_predIncN
#check @RBM.BA.stoppedDuhamelNg_at
#check @RBM.Path.PathΩ
#check @RBM.Path.gridTime
-- the zero-mode operators and the tensor-kernel tools (model-free, reused)
#check @RBM.zeroModeSet
#check @RBM.zeroModeOp
#check @RBM.avgOp
#check @RBM.projMat
#check @RBM.tensorKer
#check @RBM.UN_eq_tensorKer
#check @RBM.UN
#check @RBM.ThetaN
#check @RBM.uKer
#check @RBM.thetaKer
#check @RBM.cycProd
#check @RBM.Theta
#check @RBM.projMat_mul_SB_comm
#check @RBM.sum_SB_col
#check @RBM.sum_SB_row
-- target 1: the route through `Ring.inverse` (no window)
#check @Ring.inverse_unit
#check @Ring.inverse_non_unit
#check @Commute.units_inv_right
#check @Commute.ringInverse_ringInverse
-- target 4: loops on list indices, the G-loop and `𝒦` Ward facts (band and BA)
#check @RBM.Loop.LoopIdx
#check @RBM.Gauss.Vtx
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.loopL
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.loopM_eq_loopL
#check @RBM.sum_gloop_ward_last_div
#check @RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero
#check @RBM.Loop.KLK
#check @RBM.Loop.KLloopOf
#check @RBM.Loop.KLK_ward
#check @RBM.Loop.KLK_rotate
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.ztOf_im
-- the BA sources U1-BA reads (statement level here)
#check @RBM.BA.BALloop
#check @RBM.BA.BAKloop
#check @RBM.BA.BAKsol
#check @RBM.BA.baK_ward
#check @RBM.BA.BAKsol_rotate
#check @RBM.BA.BAMB_shift
#check @RBM.BA.BAK_row_sum
#check @RBM.BA.BAK_col_sum
#check @RBM.BA.BATheta_row_sum_pm
#check @RBM.BA.EMn2BA_seqHflowBA_herm
#check @RBM.BA.BAuKer_self
#check @RBM.BA.BAuKer_comp
-- UBA-C1 (DECISIONS §269 (2)): the merged comparison; no crossing is expected in this row
#check @RBM.BA.BAflowLam0
#check @RBM.BA.TwistStep2_lam0_sq
#check @RBM.BA.TwistStep2_T0_ge
-- the model-free vocabulary of `Step34Pins` the targets read
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STIdiff
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STQopNorm
#check @RBM.EKFastDecay

/-! ## Part 2: the target statements (content binding) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 1** (content binding): the one carrier fact of the zero-mode layer.  For every charge pair the generator
`X = M^{(σσ')} S` of the carrier kernels (`Step2Gen_uKer = (1 - sX) Θ_t(X)`, `Step2Gen_thetaKer = X Θ_t(X)`,
`Chain/Step2Gen.lean:188-195`) has all row sums and all column sums equal to one constant `c`.  It replaces `3 ≤ L`, the
symmetric `Theta` and `‖t μ‖ < 1` of `ZeroModeCalc.lean:305-330`, `QopAlgebra.lean:670-711` (supervisor 1457 Q1, U1-BA data:
constant row and column sums suffice). -/
def T2463_KerSums {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) : Prop :=
  ∀ σ σ' : Bool, ∃ c : ℂ,
    (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c) ∧
      ∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c

/-- **Target 1, band** (content binding): unconditional at `bandFM` (`X = m(σ) m(σ') S^{(B)}`, `Step2Kern_Mss_band`). -/
def T2463_KerSumsBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ), T2463_KerSums (bandFM sz E) n

/-- **Target 2** (content binding): `Q^{(A)}` commutes with the one kernel `Step2Gen_UN` (`zeroModeSet_UN`,
`ZeroModeCalc.lean:332`); every `s, t`, no window. -/
def T2463_ZeroModeSetUNg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2463_KerSums C n →
    ∀ {k : ℕ} (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
      zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ s t T) = Step2Gen_UN C n σ s t (zeroModeSet d (sz.L n) A T)

/-- **Target 2** (content binding): the same for `Step2Gen_ThetaN` (`zeroModeSet_ThetaN`, `ZeroModeCalc.lean:395`). -/
def T2463_ZeroModeSetThetaNg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2463_KerSums C n →
    ∀ {k : ℕ} (σ : Fin k → Bool) (t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
      zeroModeSet d (sz.L n) A (Step2Gen_ThetaN C n σ t T) = Step2Gen_ThetaN C n σ t (zeroModeSet d (sz.L n) A T)

/-- **Target 3** (content binding): `(iisuwjyys)` on the grid with `Q^{(A)}` inside the kernel
(`Ind.zeroModeCalc_duhamel_inside_at`, `ZeroModeCalc.lean:522`) over `Step2Mat`, with T4s1's `AvecNg`, `predIncNg`,
`martIncNg`; `Step2Gen_USemigroup` and target 1 in place of `|E n| < 2`. -/
def T2463_DuhamelInsideAtg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ),
    Step2Gen_USemigroup Cm.toFlowFM n → T2463_KerSums Cm.toFlowFM n →
    0 ≤ s n → s n ≤ t n → t n < 1 → K n ≠ 0 →
    ∀ {k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k)) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz),
      min j (τ ω) ≤ K n →
      zeroModeSet d (sz.L n) A (AvecNg Cm s t K n (min j (τ ω)) σ ω) =
        Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
            (zeroModeSet d (sz.L n) A (AvecNg Cm s t K n 0 σ ω)) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
              (zeroModeSet d (sz.L n) A (predIncNg Cm s t K n i σ ω)) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Step2Gen_UN Cm.toFlowFM n σ (gridTime s t K n (i + 1)) (gridTime s t K n (min j (τ ω)))
              (zeroModeSet d (sz.L n) A (martIncNg Cm s t K n i σ ω))

/-- **Target 4** (content binding): a Ward family on list indices with constant `κ`: cyclic rotation and the Ward identity
at the last index for both charge orders.  The content of the private `NPQFam` (`NewPQ.lean:257`); the conclusion shape of the
merged `KLK_rotate`, `KLK_ward`, `BAKsol_rotate`, `baK_ward`. -/
def T2463_WardFam (d L : ℕ) [NeZero L] (κ : ℂ) (T : LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)), σ.length = a.length →
      T ⟨s :: σ, b :: a⟩ = T ⟨σ ++ [s], a ++ [b]⟩) ∧
    ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, T ⟨s :: μ ++ [!s], a ++ [x]⟩ = κ * (T ⟨true :: μ, a⟩ - T ⟨false :: μ, a⟩)

/-- **Target 4** (content binding): G-loops of any Hermitian matrix at `Im z ≠ 0` form a Ward family with
`κ = (2 i W^d Im z)⁻¹` (the private `npq_loopL_rotate`, `npq_loopL_ward`, `NewPQ.lean:183, 211`, made public; model-free). -/
def T2463_LoopLWardFam : Prop :=
  ∀ {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ),
    H.IsHermitian → z.im ≠ 0 →
      T2463_WardFam d L ((2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ))⁻¹) (loopL d L W H z)

/-- **Target 4** (content binding): `lem: newPQ`, model-free (`(yurenAL)`, `(yurenAK)`; the private `npq_main`,
`NewPQ.lean:479`, with `npq_ward_of_fam`, `:404`): the data `(ℓ, k, ξ, σ', ι, A')` come before `L`, `κ`, `T`; the coefficient is
`(L^{-d} κ)^{m - k_α}`. -/
def T2463_NewPQExpansion (d : ℕ) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (L : ℕ) [NeZero L] (κ : ℂ) (T : LoopIdx (Zd d L) → ℂ), T2463_WardFam d L κ T →
        ∀ a : Fin m → Zd d L,
          zeroModeSet d L A (fun a' => T (loopOf σ a')) a =
            zeroModeSet d L (A ∪ STIdiff σ) (fun a' => T (loopOf σ a')) a +
              ∑ α : Fin ℓ, (ξ α : ℂ) * (((L : ℂ) ^ d)⁻¹ * κ) ^ (m - k α) *
                zeroModeSet d L (A' α) (fun a' => T (loopOf (σ' α) a')) (a ∘ ι α)

/-- **Target 5** (content binding): the carrier class of `lem: newPQ`.  At every size index, time `τ ∈ [0,1)` and sample,
`C.L` and `C.K` read through `loopOf` are Ward families with `κ = (2 i W^d η_τ)⁻¹`, `η_τ = C.eta n τ`. -/
def T2463_WardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 → ∀ ω : sz.SeqΩ,
    ∃ TL TK : LoopIdx (Zd d (sz.L n)) → ℂ,
      (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), C.L n τ σ a ω = TL (loopOf σ a)) ∧
      (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), C.K n τ σ a = TK (loopOf σ a)) ∧
      T2463_WardFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) TL ∧
      T2463_WardFam d (sz.L n) ((2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) TK

/-- **Target 5, band** (content binding): `bandFM` is in the class for `|E n| < 2` (target 4 at `seqHflow`, `zt`; `KLK_rotate`,
`KLK_ward`). -/
def T2463_WardClsBand : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ), (∀ n, |E n| < 2) → T2463_WardCls sz (bandFM sz E)

/-- **Target 5** (content binding): `(𝓛 − 𝒦)` through `lem: newPQ` (`Gauss.Sizes.zeroModeCalc_LK_expansion`,
`ZeroModeCalc.lean:563`) over the class; model-level `C.L - C.K` (as `Chain/Step5Gen`), `C.eta` for `etaT`. -/
def T2463_LKExpansiongL (d : ℕ) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (C : FlowFM sz), T2463_WardCls sz C → ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 →
        ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
          zeroModeSet d (sz.L n) A (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a =
            zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a +
              ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
                zeroModeSet d (sz.L n) (A' α) (fun a' => C.L n τ (σ' α) a' ω - C.K n τ (σ' α) a') (a ∘ ι α)

/-- **Target 5** (content binding): the case `A = ∅` (`Gauss.Sizes.zeroModeCalc_LK_expansion_empty`, `ZeroModeCalc.lean:595`). -/
def T2463_LKExpansionEmptygL (d : ℕ) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (C : FlowFM sz), T2463_WardCls sz C → ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 →
        ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
          C.L n τ σ a ω - C.K n τ σ a =
            zeroModeSet d (sz.L n) (STIdiff σ) (fun a' => C.L n τ σ a' ω - C.K n τ σ a') a +
              ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
                zeroModeSet d (sz.L n) (A' α) (fun a' => C.L n τ (σ' α) a' ω - C.K n τ (σ' α) a') (a ∘ ι α)

/-- **Target 6** (content binding): the column sums of `Step2Gen_thetaKer` (`QopAlgebra_col_sum_thetaKer`,
`QopAlgebra.lean:697`): column sums `c` of `X` and an invertible `1 - t X` give `c (1 - t c)⁻¹`. -/
def T2463_ColSumThetaKerg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (t : ℝ) (c : ℂ),
    (∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c) →
    IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) →
    ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t x y = c * (1 - (t : ℂ) * c)⁻¹

/-- **Target 6** (content binding): the same for `Step2Gen_uKer` (`QopAlgebra_col_sum_uKer`, `QopAlgebra.lean:704`). -/
def T2463_ColSumUKerg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (σ σ' : Bool) (s t : ℝ) (c : ℂ),
    (∀ b : Zd d (sz.L n), ∑ a : Zd d (sz.L n), (Step2Kern_Mss C n σ σ' * C.S n) a b = c) →
    IsUnit (1 - (t : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) →
    ∀ y : Zd d (sz.L n), ∑ x : Zd d (sz.L n), Step2Gen_uKer C n σ σ' s t x y = (1 - (s : ℂ) * c) * (1 - (t : ℂ) * c)⁻¹

/-- **Target 6** (content binding): `Θ^{(m+1)}` preserves sum-zero tensors (`QopAlgebra_ThetaN_sumZero`,
`QopAlgebra.lean:786`); target 1 only, no window. -/
def T2463_ThetaNSumZerog : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2463_KerSums C n →
    ∀ {m : ℕ} (σ : Fin (m + 1) → Bool) (t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ),
      (∀ a₁ : Zd d (sz.L n), STPsum (d := d) A a₁ = 0) →
        ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (Step2Gen_ThetaN C n σ t A) a₁ = 0

/-- **Target 6** (content binding): the same for `U^{(m+1)}` (`QopAlgebra_UN_sumZero`, `QopAlgebra.lean:821`). -/
def T2463_UNSumZerog : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ), T2463_KerSums C n →
    ∀ {m : ℕ} (σ : Fin (m + 1) → Bool) (s t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ),
      (∀ a₁ : Zd d (sz.L n), STPsum (d := d) A a₁ = 0) →
        ∀ a₁ : Zd d (sz.L n), STPsum (d := d) (Step2Gen_UN C n σ s t A) a₁ = 0

/-- **Target 6** (content binding): linearity (`QopAlgebra_ThetaN_sub`, `QopAlgebra.lean:860`). -/
def T2463_ThetaNSubg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (u : ℝ)
    (A B : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)),
    Step2Gen_ThetaN C n σ u (fun b => A b - B b) a = Step2Gen_ThetaN C n σ u A a - Step2Gen_ThetaN C n σ u B a

/-- **Target 6** (content binding): linearity (`QopAlgebra_UN_sub`, `QopAlgebra.lean:865`). -/
def T2463_UNSubg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {k : ℕ} (σ : Fin k → Bool) (s u : ℝ)
    (A B : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)),
    Step2Gen_UN C n σ s u (fun b => A b - B b) a = Step2Gen_UN C n σ s u A a - Step2Gen_UN C n σ s u B a

/-- **Target 6** (content binding): the commutator `[𝒬_t, Θ^{(m+1)}_{t,σ}]` (`QopAlgebra_commutator_ThetaN`,
`QopAlgebra.lean:871`). -/
def T2463_CommutatorThetaNg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)),
    STQop (d := d) ϑ t (Step2Gen_ThetaN C n σ t A) a - Step2Gen_ThetaN C n σ t (STQop (d := d) ϑ t A) a =
      Step2Gen_ThetaN C n σ t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (Step2Gen_ThetaN C n σ t A) (a 0) * ϑ t a

/-- **Target 6** (content binding): the commutator `[𝒬_t, U^{(m+1)}_{s,t,σ}]` (`QopAlgebra_commutator_UN`,
`QopAlgebra.lean:884`). -/
def T2463_CommutatorUNg : Prop :=
  ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) {m : ℕ} (σ : Fin (m + 1) → Bool)
    (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (s t : ℝ) (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (a : Fin (m + 1) → Zd d (sz.L n)),
    STQop (d := d) ϑ t (Step2Gen_UN C n σ s t A) a - Step2Gen_UN C n σ s t (STQop (d := d) ϑ t A) a =
      Step2Gen_UN C n σ s t (fun b => STPsum (d := d) A (b 0) * ϑ t b) a -
        STPsum (d := d) (Step2Gen_UN C n σ s t A) (a 0) * ϑ t a

/-- The parameterized targets as Prop values. -/
example : Prop := ∀ d : ℕ, T2463_NewPQExpansion d ∧ T2463_LKExpansiongL d ∧ T2463_LKExpansionEmptygL d
example : Prop := T2463_KerSumsBand ∧ T2463_WardClsBand ∧ T2463_LoopLWardFam
example : Prop := T2463_ZeroModeSetUNg ∧ T2463_ZeroModeSetThetaNg ∧ T2463_DuhamelInsideAtg
example : Prop := T2463_ColSumThetaKerg ∧ T2463_ColSumUKerg ∧ T2463_ThetaNSumZerog ∧ T2463_UNSumZerog
example : Prop := T2463_ThetaNSubg ∧ T2463_UNSubg ∧ T2463_CommutatorThetaNg ∧ T2463_CommutatorUNg

/-- Target 2, band route (not binding; target 7 (a)): through `bandStep2_Ugen` and target 1 at `bandFM`, the merged
`Ind.zeroModeSet_Ugen` (`ZeroModeCalc.lean:450`, there under `|E| ≤ 2`, `0 ≤ w < 1`). -/
example : Prop := T2463_ZeroModeSetUNg → T2463_KerSumsBand →
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (v w : ℝ) (A : Finset (Fin k))
    (T : (Fin k → Zd d (sz.L n)) → ℂ),
    zeroModeSet d (sz.L n) A (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w T) =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ v w (zeroModeSet d (sz.L n) A T)

/-- E-C1 (not binding): the BA reading of the one kernel is stage E's `BAUN` (the merged `Step2Kern_UN_BA`,
`Chain/Step2Kern.lean:124`, under its `Im` premise). -/
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ),
    Step2Gen_UN (baFM sz lam0 E) n σ s t A = BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t A

/-- U1-BA readings (not binding; U1-BA proves them): target 1 and the class of target 5 at `baFM`. -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), T2463_KerSums (baFM sz lam0 E) n
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ), T2463_WardCls sz (baFM sz lam0 E)

/-- U1-BA reading (not binding): `baZeroModeSet_UN` of the BA pin REQ (`REQ-2026-10-12-1418-UBA.md:35`) is target 2 at
`baFM`, read through `Step2Kern_UN_BA`. -/
example : Prop := T2463_ZeroModeSetUNg →
  ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k))
    (T : (Fin k → Zd d (sz.L n)) → ℂ),
    T2463_KerSums (baFM sz lam0 E) n → (((E n : ℝ) : ℂ) + BAmF sz lam0 E n).im ≠ 0 →
      zeroModeSet d (sz.L n) A (BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t T) =
        BAUN d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) σ s t (zeroModeSet d (sz.L n) A T)

end RBM.BA

end

/-! ## Part 3 (G1): the public names of the four band files (not edited; statements unchanged) -/
-- `Induction/ZeroModeCalc.lean` (36)
#check @RBM.ZeroModeCalc_zeroModeOp_add
#check @RBM.ZeroModeCalc_zeroModeOp_smul
#check @RBM.ZeroModeCalc_zeroModeOpLin
#check @RBM.ZeroModeCalc_zeroModeOp_sum
#check @RBM.zeroModeSet_add
#check @RBM.zeroModeSet_smul
#check @RBM.zeroModeSetLin
#check @RBM.zeroModeSet_zero
#check @RBM.zeroModeSet_sub
#check @RBM.zeroModeSet_sum
#check @RBM.zeroModeSet_empty
#check @RBM.norm_zeroModeOp_le
#check @RBM.norm_zeroModeSet_le
#check @RBM.ZeroModeCalc_tensorKer_zeroModeOp
#check @RBM.ZeroModeCalc_zeroModeOp_tensorKer_comm
#check @RBM.ZeroModeCalc_zeroModeSet_comm_of_comm
#check @RBM.ZeroModeCalc_zeroModeSet_tensorKer_comm
#check @RBM.ZeroModeCalc_projMat_comm_of_sums
#check @RBM.ZeroModeCalc_projMat_mul_Theta_comm
#check @RBM.ZeroModeCalc_projMat_mul_uKer_comm
#check @RBM.ZeroModeCalc_projMat_mul_thetaKer_comm
#check @RBM.zeroModeSet_UN
#check @RBM.zeroModeOp_UN
#check @RBM.zeroModeOp_ThetaN
#check @RBM.zeroModeSet_ThetaN
#check @RBM.ZeroModeCalc_mem_STIdiff
#check @RBM.ZeroModeCalc_STIdiff_subset_iff
#check @RBM.sameSignOutside_of_STIdiff_subset
#check @RBM.sameSignOutside_union_STIdiff
#check @RBM.Ind.Ugen_eq_UN_EKsgn
#check @RBM.Ind.zeroModeSet_Ugen
#check @RBM.Ind.zeroModeOp_Ugen
#check @RBM.Ind.zeroModeCalc_duhamel_at
#check @RBM.Ind.zeroModeCalc_duhamel_inside_at
#check @RBM.Gauss.Sizes.zeroModeCalc_LK_expansion
#check @RBM.Gauss.Sizes.zeroModeCalc_LK_expansion_empty
-- `Induction/NewPQ.lean` (1)
#check @RBM.Gauss.Sizes.stNewPQ_holds
-- `Induction/QopAlgebra.lean` (19)
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_sum
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_differentiableAt
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_Qop
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_of_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_Psum_deriv
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_hasDerivAt
#check @RBM.Gauss.Sizes.QopAlgebra_Qop_hasDerivAt_const
#check @RBM.Gauss.Sizes.QopAlgebra_col_sum_thetaKer
#check @RBM.Gauss.Sizes.QopAlgebra_col_sum_uKer
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_UN_sumZero
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sub
#check @RBM.Gauss.Sizes.QopAlgebra_UN_sub
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_UN
-- `Induction/QopNorm.lean` (2; model-free, no generic text)
#check @RBM.Gauss.Sizes.stQopNorm_holds
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay

/-! ## Part 4: not this row -/
-- T2457 (U3s1, held): target 7 `STNewPQgL` over a class is its generic form of this band pin; target 9 of T2463 is conditional
#check @RBM.Gauss.Sizes.STNewPQ
-- T2457 targets 2 and 6: `STLKtensorg`, `STXiLKg`, `STEKNonzerogL` (U1s1's band files mention `STEKNonzero` in a docstring only)
#check @RBM.Gauss.Sizes.STLKtensor
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.STEKNonzero
-- U1s2: `STContract` (matrix form `STContractM`, applied at a sample)
#check @RBM.Gauss.Sizes.STContract
