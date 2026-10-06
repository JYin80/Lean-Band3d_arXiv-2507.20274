/-
T2262 check file (BA-S2b2a, dispatcher V1, Tue Oct  6 06:06 UTC 2026).  Statements of the proof targets of
`RBM3D/BA/Step1Setup.lean` (the block Anderson analogue of the band `Induction/Step1Setup.lean` and the net
layer of `Induction/Continuity.lean`, consumed by BA-S2b2b `baBootstrap'_holds`).  Defs, `#check`s and
Prop-valued `example`s only: no proofs.  Compiles on `main` (193512b) as is.
-/
import RBM3D.BA.Step1Boot
import RBM3D.Induction.Step1

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## 0. Merged names used (each `#check` with its full namespace) -/

-- BA carrier, flow data, family (T2197 `FlowPins.lean`, T2189 `MFixedPoint.lean`, T2238 `Step1Trivial.lean`,
-- T2227 `CouplingWindow.lean`)
#check @RBM.BA.PrecL
#check @RBM.BA.FlowFM
#check @RBM.BA.FlowFM.GM
#check @RBM.BA.STmaxLoop2g
#check @RBM.BA.STStep1LoopgL
#check @RBM.BA.STStep1WeakgL
#check @RBM.BA.baFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAGt
#check @RBM.BA.BAmF
#check @RBM.BA.BAMfine
#check @RBM.BA.BAm
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAdom
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowEs
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAWinBulk
#check @RBM.BA.BAFamZ
#check @RBM.BA.BAFamZ_im_m_ge
#check @RBM.BA.BAflow_T0_bounds
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
-- BA-S1 (T2237 `ConArg.lean`) and BA-S2b1 (T2256 `Step1Boot.lean`)
#check @RBM.BA.FlowFM.omegaC
#check @RBM.BA.BAself_norm_le_one
#check @RBM.BA.FlowFM.indMax
#check @RBM.BA.FlowFM.gexRHS
#check @RBM.BA.BABootstrap'
#check @RBM.BA.BAFlowMember
#check @RBM.BA.BAGbEXPii
#check @RBM.BA.BAGbEXPij
#check @RBM.BA.baGii_member
#check @RBM.BA.baGij_member
#check @RBM.BA.baM_entry_le
#check @RBM.BA.baOmegaC_eq_one
#check @RBM.BA.baBoot_LI
#check @RBM.BA.BAFamZ_mono
#check @RBM.BA.PrecL_congr
-- band model: vocabulary, `S1Std`, scale facts, bridge, net (T2028, T2079, T2090, T2062, T2047, T2045, T2012)
#check @RBM.Gauss.Sizes.SizeTendsto
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.RangeCond
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STStep1LoopPT
#check @RBM.Gauss.Sizes.STStep1WeakPT
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.PerTimeDomAt
#check @RBM.Ind.S1Std
#check @RBM.Ind.s1_std_of_stFlow
#check @RBM.Ind.s1_F3
#check @RBM.Ind.s1_F4
#check @RBM.Ind.s1_F5
#check @RBM.Ind.s1_F6
#check @RBM.Ind.s1_F7
#check @RBM.Ind.s1_F8
#check @RBM.Ind.s1_near_card
#check @RBM.Ind.s1_wl_det
#check @RBM.Ind.s1_gexRHS_le
#check @RBM.Ind.s1_indMax_eq_one
#check @RBM.Ind.s1_omegaC_eq_one
#check @RBM.Ind.GopboundPin
#check @RBM.Ind.gopbound
#check @RBM.Ind.Step1NetLift
#check @RBM.Ind.step1NetLift
#check @RBM.Ind.ContinuityNet.cont_core
#check @RBM.Ind.PerTimeCalc.stepOneBootstrap
#check @RBM.Ind.step1TargetV3_holds
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.BA.FlowPinsInst.zSeq
#check @RBM.Ind.Step1SetupInst.s1Setup_conStInd_const

namespace RBM.BA.T2262Check

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 1. Statements of the proof targets (names in the new file without `_stmt`, namespace `RBM.BA`) -/

/-- Target 1 (`baS1Std`): the band standing hypotheses `S1Std` at the **dummy energy** `E ≡ 0` and the bulk
constant `min κ 1` hold along a block Anderson flow window `0 ≤ s ≤ t ≤ t₀(z)` (the scale facts `s1_F3`–`s1_F8`,
`s1_B_pos`, `s1_hsize` use no field but `hκ, hc, h𝔡, hτ, hs0, hst, ht1, hN, hB, hWO, hCond, hR`; `hE` is the
only energy field and holds at `0`).  `τ = ε/2`; `RangeCond (ε/2) t` from `BAdom` (`1 - t ≥ 1 - t₀(z) =
Im z/(Im m + Im z) ≥ Im z/2 ≥ N^{-1+ε}/2`, `|m| ≤ 1` by `BAm_spec`, `BAself_norm_le_one`). -/
def baS1Std_stmt (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          STConStInd sz 𝔠d s t →
          RBM.Ind.S1Std sz (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d (fun _ => 0) s t

/-- Target 2 (`baG_continuousOn`): `v ↦ (G_v - M)_{xy}` of the block Anderson carrier is continuous on
`[a, b]`, `b < 1`, for every sample (band `s1x_continuousOn`, `Induction/Step1.lean:372`; `Im z_v = (1 - v) Im m
> 0`, `H_v = g₀Ψ + √v X` Hermitian). -/
def baG_continuousOn_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
    ∀ a b : ℝ, b < 1 → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
      ContinuousOn (fun v : ℝ => (baFM sz lam0 E).GM n v ω x y) (Set.Icc a b)

/-- Target 3 (`baGopbound`): the time-Lipschitz bound of `BAGt` w.h.p. under the block Anderson law (the BA form of
`GopboundPin`, `Induction/ContinuityNet.lean:55`, proved for the band by `gopbound`, `Induction/Continuity.lean:527`):
the deterministic part `g₀Ψ` cancels in `H_u - H_{u'}`, `z_u - z_{u'} = (u' - u) m`, `‖G_u‖ ≤ ((1 - u) Im m)⁻¹`. -/
def baGopbound_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ), 0 < κ → (∀ n, κ ≤ (BAmF sz lam0 E n).im) →
    (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → sz.SizeTendsto →
    ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Sizes.seqP (sz.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
          u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
          |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
          ∃ x y : Idx d (sz.L n) (sz.W n),
            ((sz.size n : ℕ) : ℝ) ^ (-C) < ‖BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y‖} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- Target 4 (`flowFM_omegaC_mono`): `Ω_{C₁} ⊆ Ω_{C₂}` for `C₁ ≤ C₂` (T2256d: `baOmegaC_eq_one` has the
`n`-dependent threshold `1 + (Im m)⁻¹ ≤ 1 + κ⁻¹`). -/
def flowFM_omegaC_mono_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (t C₁ C₂ : ℝ) (ω : sz.SeqΩ), C₁ ≤ C₂ →
    C.omegaC n t C₁ ω ≤ C.omegaC n t C₂ ω

/-- Target 5 (`flowFM_wl_det`): the weak-law core at one sample over **any** carrier, with the non-scalar `M`
(band `s1_wl_det`, `Induction/Step1Setup.lean:1064`, with `s1_gexRHS_le` `:1015`, `s1_indMax_eq_one` `:1001`,
`s1_omegaC_eq_one` `:988`): the event threshold `2` of the band is a hypothesis `‖G‖_max ≤ C₀`, the off-diagonal
input is on `(G - M)_{xy}` (`BAGijGEX`, T2256 P2), the constant `2·9^d + 1` is the band's. -/
def flowFM_wl_det_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (ω : sz.SeqΩ) (u a c' g Nτ C₀ : ℝ), 0 < c' →
    (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ 2 * a) →
    2 * a ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') → 1 ≤ Nτ → 0 ≤ g → (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ g →
    (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n u ω x y‖ ≤ C₀) →
    (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), C.omegaC n u C₀ ω * ‖C.L n u σ b ω‖ ≤ Nτ * g) →
    (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1 p.2‖ ^ 2 ≤
        Nτ * STmaxLoop2g C n u ω) →
    (∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2},
      C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1.1 p.1.2‖ ^ 2 ≤
        Nτ * C.gexRHS n u ω (STblk sz n p.1.1) (STblk sz n p.1.2)) →
    ∀ i j : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g

/-- Target 6 (`baNetLift`): the net lift of the two Step 1 families of the block Anderson carrier (band
`Step1NetLift`/`step1NetLift`, `Induction/Continuity.lean:594/:605`; per-time forms = `STStep1LoopPT`,
`STStep1WeakPT` (`Induction/Defs.lean:248/:255`) over `baFM` at the law `seqP (sz.withLam 0)`; the bulk premise
`|E| ≤ 2 - κ` is replaced by `κ ≤ Im m`, `|m| ≤ 1`). -/
def baNetLift_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), 0 < κ →
    (∀ n, κ ≤ (BAmF sz lam0 E n).im) → (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → 0 < τ →
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
    ((∀ k : ℕ, 1 ≤ k →
        PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
          (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
          (fun n p ω => ‖(baFM sz lam0 E).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
          (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
      STStep1LoopgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) ∧
    (PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
        (fun n p ω => ‖(baFM sz lam0 E).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
        (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) →
      STStep1WeakgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t)

/-! ## 2. Prop-valued examples (no proof obligations) -/

example : Prop := baS1Std_stmt 3 ∧ baG_continuousOn_stmt 3 ∧ baGopbound_stmt 3
example : Prop := flowFM_omegaC_mono_stmt 3 ∧ flowFM_wl_det_stmt 3 ∧ baNetLift_stmt 3
example : Prop := BAFlowMember 3 → BAGbEXPii 3 → BAGbEXPij 3 → BABootstrap' 3

end RBM.BA.T2262Check
