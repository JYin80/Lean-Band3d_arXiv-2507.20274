/-
Release check for T2455 (dispatcher V3, Mon Oct 12 13:13 UTC 2026; DECISIONS §265).  BA-U X1a (ST side, route G): the generic rewrite of the CLT
layer of Step 5 case (i), part a (`Evolution/CltSwap`, `CltResolvent`, `CltPath`, `FarEntry`, `CltGood`, `CltStep`, `ExpInv`,
in place; new vocabulary file `Chain/CltGen`), supervisor 1152 Q1 (X1-C1 … X1-C5), Q2.
Part 1: merged names (band X1 theorems and pins, carrier, T8b's kernels, Green / KellStar inputs, propagator facts, BA producers).
Part 2: the target statements as Prop values (prefix `T2455_`).  Content binding: `T2455_CltEtaLowerOf` (E4 restated, X1-C1),
`T2455_STfFarg`, `T2455_STCltFarConclgL`, `T2455_STcltBg`, `T2455_STcltXg`, `T2455_STCltIsoConclgL`, `T2455_STExpInvgL` (the
conclusions of the generic pins, X1-C4; restatable in the 1a with the change reported).  Proposals (not binding; fixed at the
1a-audit): `T2455_GijDecgL` (X1-C3), `T2455_KfargL`, `T2455_CltRepg`.  Then shapes (not binding): band routes, BA readings.
Part 3 (G1): the 100 public declarations of the seven files, unchanged; the auditor adds `example : <statement> := <name>`.
Part 4: not this row (X1b, U4s2).
Merged names only.  No proofs, no placeholders.
Run: lake env lean docs/tickets/checks/T2455-check.lean
-/
import RBM3D.Evolution.CltStep
import RBM3D.Evolution.ExpInv
import RBM3D.Evolution.CltFar
import RBM3D.Induction.IniTermI
import RBM3D.Chain.Step2Gen
import RBM3D.Chain.Step2Kern
import RBM3D.BA.Step2BA
import RBM3D.BA.GreenOff
import RBM3D.BA.Prop6Path
import RBM3D.BA.Ward
import RBM3D.BA.CombesThomas
import RBM3D.BA.MReg
import RBM3D.BA.GreenSchur
import RBM3D.BA.KSolve
import RBM3D.Gauss.BlockAnderson

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the band pins of Step 5 case (i) and their vocabulary (`Induction/Step5Pins.lean`, `Step34Pins.lean`)
#check @RBM.Gauss.Sizes.STCltFar
#check @RBM.Gauss.Sizes.STCltFarConcl
#check @RBM.Gauss.Sizes.STfFar
#check @RBM.Gauss.Sizes.STcltB
#check @RBM.Gauss.Sizes.STcltX
#check @RBM.Gauss.Sizes.STCltIsoConcl
#check @RBM.Gauss.Sizes.STCltIso
#check @RBM.Gauss.Sizes.STExpInv
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STAI
#check @RBM.Gauss.Sizes.STStep2Concl
#check @RBM.Gauss.Sizes.STLocalEntryU
#check @RBM.Gauss.Sizes.STGdecayW
#check @RBM.Gauss.Sizes.STAvgU
#check @RBM.Gauss.Sizes.STLK_of_STLKU
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Step5Inst.inst_cltIso
#check @RBM.Gauss.Step5Inst.inst_cltFar
#check @RBM.Gauss.Step5Inst.inst_expInv
#check @RBM.Gauss.Step5Inst.szCL
#check @RBM.Gauss.Step5Inst.zCL
#check @RBM.Gauss.Step5Inst.sCL
#check @RBM.Gauss.Step5Inst.tCL
#check @RBM.Gauss.Step5Inst.flow_zCL
-- the semicircle reading that the generic text drops (X1-C1), and its generic replacement
#check @RBM.mE
#check @RBM.mE_im
#check @RBM.norm_mE
#check @RBM.zt
#check @RBM.mSigma
#check @RBM.lemT
#check @RBM.ellT
#check @RBM.Gauss.etaT
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.ztOf_im
#check @RBM.Gauss.zt_eq_ztOf
#check @RBM.Gauss.etaT_eq_etaOf
#check @RBM.Gauss.Gres
#check @RBM.Gauss.loopFine
#check @RBM.Gauss.Hflow
#check @RBM.Gauss.PF
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.STKloop
-- the carrier, T8b's kernels (U-C4: one propagator), the generic Step 2 and GbEXP forms
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.PrecL
#check @RBM.BA.bandFM
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.baStep2Mat
#check @RBM.BA.Step2Gen_Theta
#check @RBM.BA.Step2Kern_Mss
#check @RBM.BA.Step2Kern_Mss_band
#check @RBM.BA.Step2Kern_thetaKer_band
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_UN_band
#check @RBM.BA.Step2Kern_UN_BA
#check @RBM.BA.STLKMg
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STLocalEntryUgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STAvgUgL
#check @RBM.BA.bandFM_STStep2Concl
#check @RBM.BA.STindMaxg
#check @RBM.BA.STgexRHSg
#check @RBM.BA.STGijGEXgL
#check @RBM.BA.bandFM_STGijGEX
-- X1-C3: the Green and KellStar inputs, band and BA
#check @RBM.Gauss.Sizes.STGbEXPij
#check @RBM.Gauss.Sizes.STGijGEX
#check @RBM.Gauss.Sizes.STindMax
#check @RBM.Gauss.Sizes.STgexRHS
#check @RBM.Green.stGbEXPij_of_v3
#check @RBM.Green.gbEXPV3
#check @RBM.Green.v3_premises_of_stFlow
#check @RBM.Path.KellStarEv
#check @RBM.Path.kellStarEv
#check @RBM.Loop.KLK_two
#check @RBM.Loop.KLmSigma_mul_not
#check @RBM.BA.BAGbEXPij'
#check @RBM.BA.baGbEXPij'_holds
#check @RBM.BA.GreenCore_loopPrem
#check @RBM.BA.GreenCore_decayRHS
#check @RBM.BA.GreenCore_decayConcl
#check @RBM.BA.FlowFM.indMax
-- X1-C2: the propagator facts (band) and their BA producers
#check @RBM.Theta
#check @RBM.prop5Decay_holds
#check @RBM.prop6Diff1_holds
#check @RBM.prop7Diff2_holds
#check @RBM.prop5to8_holds
#check @RBM.BA.BAProp5to8
#check @RBM.BA.baProp5to8_holds
#check @RBM.BA.BAPropM
#check @RBM.BA.baPropM_holds
#check @RBM.BA.baWard_holds
#check @RBM.BA.baOffDiag_holds
#check @RBM.BA.BAMB_ward_row
#check @RBM.BA.BAm_norm_le_one
#check @RBM.BA.BAMfine_eq
#check @RBM.BA.BAKsolve
-- the BA carrier, flow and domain (X1-C1 reading; BA instances are U4-BA's)
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAmF
#check @RBM.BA.BAMfine
#check @RBM.BA.BAGt
#check @RBM.BA.BALloop
#check @RBM.BA.BAKloop
#check @RBM.BA.BAFlow
#check @RBM.BA.BAdom
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAm_im_lower_window
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.PsiI

/-! ## Part 2: the target statements (content binding), proposals and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2, E4 restated** (content binding; X1-C1): the band pin `CltEtaLower` (`Evolution/CltResolvent.lean:182`) with the
spectral value `m` as data: `κ ≤ Im m` in place of `|E| ≤ 2 - κ`, `κ` in place of `c_κ = cltCk κ`, `ztOf m E u` in place of
`zt E u`.  Band corollary: `m = mE E`, `κ ↦ cltCk κ` (`cltres_ck_le_im`, `:585`). -/
def T2455_CltEtaLowerOf (d L W : ℕ) : Prop :=
  ∀ (κ δ : ℝ) (m : ℂ) (E u : ℝ), 0 < κ → 0 < δ → κ ≤ m.im →
    ((((W * L) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    κ / (((W * L) ^ d : ℕ) : ℝ) ≤ (ztOf m E u).im

open Classical in
/-- **Target 8, `f^{far}` over the carrier** (content binding): the band `STfFar` (`Induction/Step5Pins.lean:364`) with
`C.L - C.K` for `STLKM … (seqHflow …)` and T8b's propagator `Step2Gen_Theta (M^{(σ₀σ₁)} S) t` (U-C4) for
`Theta d L g (t m(σ₀) m(σ₁))` (at `bandFM` the two agree through `Step2Kern_Mss_band`). -/
def T2455_STfFarg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (s t : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ : Zd d (sz.L n),
      Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) (a 0) b₁ *
        (C.L n s σ ![b₁, b₂] ω - C.K n s σ ![b₁, b₂]) *
        (Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) b₂ (a 1) -
          Step2Gen_Theta (Step2Kern_Mss C n (σ 0) (σ 1) * C.S n) (t : ℂ) b₁ (a 1))

/-- **Target 8, the conclusion of `STCltFargL`** (content binding): the band `STCltFarConcl` (`Step5Pins:387`) with
`T2455_STfFarg` and `PrecL sz μ` for `Prec sz`. -/
def T2455_STCltFarConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p ω => ‖T2455_STfFarg C n (s n) (t n) p.1.1.1 p.1.2 ω‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) / (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))

/-- **Target 8, `𝗕_b` over the carrier** (content binding): the band `STcltB` (`Step5Pins:401`) with `C.L - C.K`. -/
def T2455_STcltBg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool)
    (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) * (C.L n s σ b ω - C.K n s σ b)

/-- **Target 8, the centred factor** (content binding): the band `STcltX` (`Step5Pins:406`) at the law `μ`. -/
def T2455_STcltXg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ) (s : ℝ) (σ : Fin 2 → Bool)
    (b : Fin 2 → Zd d (sz.L n)) (cj : Bool) (ω : sz.SeqΩ) : ℂ :=
  if cj then (starRingEnd ℂ) (T2455_STcltBg C n s σ b ω - ∫ ω', T2455_STcltBg C n s σ b ω' ∂μ)
  else T2455_STcltBg C n s σ b ω - ∫ ω', T2455_STcltBg C n s σ b ω' ∂μ

/-- **Targets 6, 8, the conclusion of `STCltIsogL`** (content binding): the band `STCltIsoConcl` (`Step5Pins:417`) at the
carrier and the law `μ`. -/
def T2455_STCltIsoConclgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
    ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
      (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n)) →
      (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), T2455_STcltXg C μ n (s n) σ (b k) (decide (p ≤ k.val)) ω ∂μ‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **Targets 7, 8, `STExpInvgL`** (content binding): the band `STExpInv` (`Step5Pins:443`) over the carrier and the law `μ`,
without `|E| < 2` (unused in the band proof, `ExpInv.lean:507`). -/
def T2455_STExpInvgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, C.L n u σ (fun i => a i + c) ω ∂μ = ∫ ω, C.L n u σ a ω ∂μ) ∧
      (∫ ω, C.L n u σ (fun i => -a i) ω ∂μ = ∫ ω, C.L n u σ a ω ∂μ)

/-- **X1-C3 proposal** (not binding; fixed at the 1a-audit): the loop premise of the generic Green input, the carrier form of
`GreenCore_loopPrem` (`BA/GreenCore.lean:1616`). -/
def T2455_GijDecPremgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) (ε₀ : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.L n (t n) ![false, true] ![p.1, p.2] ω‖)
    (fun n p _ => Φ n p.1 p.2 ^ 2)

/-- **X1-C3 proposal** (not binding): the off-diagonal Green input of the generic `FarEntry`, the primed `(GijGEX_BA)` shape
(`BAGbEXPij'`, `BA/GreenCore.lean:1644`) over the carrier, with the right side of `GreenCore_decayRHS` written inline (no `BA/*`
import in the generic files).  Required: `STGbEXPij` (band, compiled in X1a) and `BAGbEXPij'` (compiled in U4-BA) both imply it;
the 1a settles the charge of the loop premise (`STgexRHS` sums both mixed charges). -/
def T2455_GijDecgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
    ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
      (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
      (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
      T2455_GijDecPremgL C μ t ε₀ Φ →
      PrecL sz μ
        (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
        (fun n p ω => STindMaxg C n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω * ‖C.GM n (t n) ω p.1.1 p.1.2‖)
        (fun n p _ =>
          (∑ a' : Zd d (sz.L n), ∑ b' : Zd d (sz.L n), Φ n a' b' *
              Real.exp (-c * ((zdistInf d (sz.L n) (a' - STblk sz n p.1.1) : ℝ) +
                (zdistInf d (sz.L n) (b' - STblk sz n p.1.2) : ℝ)))) +
            Ψ n * Real.exp (-c * (zdistInf d (sz.L n) (STblk sz n p.1.1 - STblk sz n p.1.2) : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **X1-C3 proposal** (not binding): the far field of `𝒦^{(2)}` for mixed charges, the carrier form of conjunct 1 of
`KellStarEv` (`Path/KellStar.lean:54`) read through `KLK_two` (`FarEntry.lean:417-445`), without `m(σ)m(-σ) = 1`.  If
T2452's report is on `main`, D4's consumer form replaces it. -/
def T2455_KfargL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (t : ℕ → ℝ) : Prop :=
  ∀ δ D : ℝ, 0 < δ → 0 < D →
    ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
      ∀ a b : Zd d (sz.L n),
        δ * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
            (zdistInf d (sz.L n) (a - b) : ℝ) →
          ‖C.K n u σ ![a, b]‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **Input (g) proposal** (not binding): the carrier represents the matrix model `H₀ + seqHflow (sz.withLam g')` at the
spectral value `ztOf (C.m n) (E n) u`, with law `seqP (sz.withLam g')` (the shape of `seqHflowBA`,
`Gauss/BlockAnderson.lean:83-86`). -/
def T2455_CltRepg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (g' E : ℕ → ℝ)
    (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  μ = Sizes.seqP (sz.withLam g') ∧ (∀ n, (H₀ n).IsHermitian) ∧
    ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
      (∀ x y, C.G n u ω x y =
        Gres (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)
          (ztOf (C.m n) (E n) u) true x y) ∧
      ∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
        C.L n u σ a ω = loopFine d (sz.L n) (sz.W n)
          (H₀ n + Matrix.of fun i j : Idx d (sz.L n) (sz.W n) => Sizes.seqHflow (sz.withLam g') n u ω i j)
          (ztOf (C.m n) (E n) u) σ a

/-- The binding conclusions as Prop values. -/
example : Prop := ∀ d L W : ℕ, T2455_CltEtaLowerOf d L W
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ),
  T2455_STCltFarConclgL C μ s t ∧ T2455_STCltIsoConclgL C μ s ∧ T2455_STExpInvgL C μ

/-- E4, band route (target 2, G1): the generic pin gives the merged band pin. -/
example : Prop := (∀ d L W : ℕ, T2455_CltEtaLowerOf d L W) → ∀ d L W : ℕ, RBM.Evol.CltEtaLower d L W

/-- E4, BA reading (statement level; U4-BA). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (κ δ u : ℝ), 0 < κ → 0 < δ →
  κ ≤ (BAmF sz lam0 E n).im → ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) ^ (-1 + δ) ≤ 1 - u →
    κ / (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) ≤ (ztOf (BAmF sz lam0 E n) (E n) u).im

/-- Target 8, band routes (G1; definitional for the isolation form expected, through `Step2Kern_Mss_band` for `f^{far}`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  T2455_STCltFarConclgL (bandFM sz E) (Sizes.seqP sz) s t ↔ RBM.Gauss.Sizes.STCltFarConcl sz E s t
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  T2455_STCltIsoConclgL (bandFM sz E) (Sizes.seqP sz) s ↔ RBM.Gauss.Sizes.STCltIsoConcl sz E s t
example : Prop := ∀ {d : ℕ},
  (∀ (sz : Sizes d) (E : ℕ → ℝ), T2455_STExpInvgL (bandFM sz E) (Sizes.seqP sz)) → RBM.Gauss.Sizes.STExpInv d

/-- Target 8, BA readings (statement level; U4-BA). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ),
  T2455_STCltFarConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
    T2455_STCltIsoConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  T2455_STExpInvgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0))

/-- X1-C3, band implication (compiled in X1a) and BA implication (compiled in U4-BA), shapes. -/
example : Prop := ∀ {d : ℕ}, 3 ≤ d → STGbEXPij d →
  ∀ (κ ε 𝔡 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → STFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      T2455_GijDecgL (bandFM sz (STflowE z)) (Sizes.seqP sz) t
example : Prop := ∀ {d : ℕ}, BAGbEXPij' d →
  ∀ (κ ε 𝔡 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      T2455_GijDecgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t

/-- X1-C3, the `𝒦` far field: band implication from `KellStarEv` (compiled in X1a), shape. -/
example : Prop := RBM.Path.KellStarEv 3 →
  ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ) (t : ℕ → ℝ), 0 < κ → 0 < ε → STFlow sz κ ε 𝔠 𝔡 z →
    (∀ n, t n ≤ lemT (z n)) → T2455_KfargL (bandFM sz (STflowE z)) t

/-- Input (g), band and BA readings, shapes (band: `H₀ = 0`, `g' = sz.lam`; BA: `H₀ = λ₀Ψ`, `g' = 0`). -/
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ),
  T2455_CltRepg (bandFM sz E) (Sizes.seqP sz) sz.lam E (fun _ => 0)
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ),
  T2455_CltRepg (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) 0 E
    (fun n => ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n))

end RBM.BA

end

/-! ## Part 3 (G1): the 100 public declarations of the seven files (statements unchanged, none deleted or renamed) -/

-- CltSwap (20)
#check @RBM.Evol.cltSplit
#check @RBM.Evol.MeasurePreservingCltSplit
#check @RBM.Evol.cltHybSet
#check @RBM.Evol.cltHyb
#check @RBM.Evol.CltTelescope
#check @RBM.Evol.cltHyb_zero
#check @RBM.Evol.cltHyb_card
#check @RBM.Evol.cltTelescope
#check @RBM.Evol.cltHyb_succ
#check @RBM.Evol.cltHyb_eq_update_succ
#check @RBM.Evol.cltSwap
#check @RBM.Evol.MeasurePreservingCltSwap
#check @RBM.Evol.IntegralEqZeroOfCltSwapNeg
#check @RBM.Evol.cltHyb_cltSwap
#check @RBM.Evol.cltHyb_succ_cltSwap
#check @RBM.Evol.update_cltSwap_fst
#check @RBM.Evol.measurePreserving_cltSplit
#check @RBM.Evol.measurePreserving_cltSwap
#check @RBM.Evol.integral_eq_zero_of_cltSwap_neg
#check @RBM.Evol.cltTransfer
-- CltResolvent (29)
#check @RBM.Evol.gEntry
#check @RBM.Evol.LocalForm
#check @RBM.Evol.LocalForm.eval
#check @RBM.Evol.LocalForm.Local
#check @RBM.Evol.cltY
#check @RBM.Evol.cltCoordDir
#check @RBM.Evol.CltPertMaxLe
#check @RBM.Evol.CltPertSubLe
#check @RBM.Evol.CltDerivEntry
#check @RBM.Evol.CltDerivEvalMulti
#check @RBM.Evol.CltDerivEval
#check @RBM.Evol.cltCk
#check @RBM.Evol.CltEtaLower
#check @RBM.Evol.CltEvalDetLeMulti
#check @RBM.Evol.CltEvalDetLe
#check @RBM.Evol.CltFarGeomHalf
#check @RBM.Evol.CltFarGeomNear
#check @RBM.Evol.CltCoordAdj
#check @RBM.Evol.cltPert_max_le
#check @RBM.Evol.cltPert_sub_le
#check @RBM.Evol.cltDeriv_entry
#check @RBM.Evol.cltDeriv_evalMulti_le
#check @RBM.Evol.cltDeriv_eval_le
#check @RBM.Evol.cltEta_lower
#check @RBM.Evol.cltEval_detMulti_le
#check @RBM.Evol.cltEval_det_le
#check @RBM.Evol.cltFarGeomHalf
#check @RBM.Evol.cltFarGeomNear
#check @RBM.Evol.cltCoord_adj
-- CltPath (9)
#check @RBM.Evol.cltEvalAt
#check @RBM.Evol.cltYo
#check @RBM.Evol.cltCoefSumMulti
#check @RBM.Evol.cltCoefSum
#check @RBM.Evol.cltGoodAt
#check @RBM.Evol.CltPathBoundMulti
#check @RBM.Evol.CltPathBound
#check @RBM.Evol.cltPathMulti_bound
#check @RBM.Evol.cltPath_bound
-- FarEntry (7)
#check @RBM.Gauss.Sizes.prec_timeIcc_section
#check @RBM.Gauss.Sizes.STFarEntryAtLog
#check @RBM.Gauss.Sizes.stFarEntryAtLog
#check @RBM.Gauss.Sizes.farEntry_FarNonempty
#check @RBM.Gauss.Sizes.farEntry_farNonempty_of
#check @RBM.Gauss.Step5Inst.farEntry_szCL_far_nonempty
#check @RBM.Gauss.Step5Inst.farEntry_szCL_stFarEntryAtLog
-- CltGood (14)
#check @RBM.Evol.HClt
#check @RBM.Evol.CltCoordConcl
#check @RBM.Evol.CltCoordTail
#check @RBM.Evol.CltGmaxConcl
#check @RBM.Evol.CltGmaxWhp
#check @RBM.Evol.CltFarEntryConcl
#check @RBM.Evol.CltFarEntryWhp
#check @RBM.Evol.CltGoodConcl
#check @RBM.Evol.CltGoodWhp
#check @RBM.Evol.cltCoord_tail
#check @RBM.Evol.cltGmax_whp
#check @RBM.Evol.cltFarEntry_whp
#check @RBM.Evol.cltGood_whp
#check @RBM.Gauss.Step5Inst.cltGood_hclt_szCL
-- CltStep (20)
#check @RBM.Evol.cltStep_Xo
#check @RBM.Evol.cltStep_Gamma
#check @RBM.Evol.cltStep_win
#check @RBM.Evol.cltStep
#check @RBM.Evol.cltStep_pairForm
#check @RBM.Evol.cltStep_pairForm_eval
#check @RBM.Evol.cltStep_scale
#check @RBM.Evol.cltStep_c2
#check @RBM.Evol.cltStep_loopForm
#check @RBM.Evol.cltStep_loopForm_eval
#check @RBM.Evol.cltStep_loopForm_local
#check @RBM.Evol.cltStep_loopForm_coef_le
#check @RBM.Evol.cltStep_scale_le
#check @RBM.Evol.cltStep_loopForm_stcltB
#check @RBM.Evol.cltStep_loopForm_coef_le_eventually
#check @RBM.Gauss.Sizes.stCltIso_holds
#check @RBM.Gauss.Step5Inst.cltStep_yCL
#check @RBM.Gauss.Step5Inst.cltStep_zdistInf_yCL
#check @RBM.Gauss.Step5Inst.cltStep_szCL_witness
#check @RBM.Gauss.Step5Inst.cltStep_szCL_coef
-- ExpInv (1)
#check @RBM.Gauss.Sizes.stExpInv_holds

/-! ## Part 4: not this row (X1b: `CltMoments1`, `CltMoments2`, `MeanFar`, `CltFar`; U4s2: `IniTermI`) -/
#check @RBM.Gauss.Sizes.stCltFar_holds
#check @RBM.Gauss.Sizes.cltFar_off
#check @RBM.Gauss.Sizes.cltFar_fluc
#check @RBM.Gauss.Sizes.STMeanFar
#check @RBM.Gauss.Sizes.STMeanFarConcl
#check @RBM.Gauss.Sizes.stMeanFar
#check @RBM.Gauss.Sizes.meanFar_core
#check @RBM.Gauss.Sizes.meanFar_eventually
#check @RBM.Evol.cltMom1_weight_a1
#check @RBM.Evol.cltMom1_weight_a2
#check @RBM.Evol.cltMom2_decomp
#check @RBM.Gauss.Sizes.STCltFarUConcl
#check @RBM.Gauss.Sizes.stCltFar_uniform
