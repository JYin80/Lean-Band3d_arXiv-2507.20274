/-
Release check for T2473 (dispatcher V3, Mon Oct 12 20:33 UTC 2026; DECISIONS §276).  ST T4s2 (sub-stage T, ST side): the grid good event, its exit
time and measurability, the envelope of the grid drift, the stopped assembly and the Azuma proxies over the carrier, in the new
files `Chain/GridGoodGen`, `Chain/GridEnvelopeGen`, `Chain/GridAssemblyGen`, `Chain/AzumaProxyGen`.  The band files
`Induction/GridGoodN`, `GridEnvelopeN`, `GridAssemblyN`, `AzumaProxyN`, `AzumaProxyN2` are not edited (outside the lane).
Part 1: merged names.  Part 2: the target statements as Prop values (prefix `T2473_`; content binding for targets 2-4), then
shapes (not binding; design gate D1-D2 fixes them): band bridges, BA readings, the walk fact W, the kernel class (T2471's text),
the per-carrier form of target 4, the UBA-C1 literal.  Part 3 (G1): the public band names that the U rows read (files not
edited).
Merged names only.  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2473-check.lean
-/
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.AzumaProxyN2
import RBM3D.Chain.GridDuhamelGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.BA.Step2BA

set_option linter.style.longLine false

/-! ## Part 1: merged names -/

-- the carrier, T8b's kernel (U-C4: the one kernel) and its matrix vocabulary
#check @RBM.BA.FlowFM
#check @RBM.BA.bandFM
#check @RBM.BA.PrecL
#check @RBM.BA.Step2Mat
#check @RBM.BA.bandStep2Mat
#check @RBM.BA.Step2Gen_uKer
#check @RBM.BA.Step2Gen_UN
#check @RBM.BA.Step2Kern_uKer_band
#check @RBM.BA.STLIMg
#check @RBM.BA.STksimLKMg
#check @RBM.BA.STelklkMg
#check @RBM.BA.STegtMg
#check @RBM.BA.STeeMg
#check @RBM.BA.STeeUMg
#check @RBM.BA.bandStep2_STksimLKM
#check @RBM.BA.bandStep2_STeeM
#check @RBM.BA.bandStep2_STeeUM
#check @RBM.BA.STKboundgL
#check @RBM.BA.STKwardgL
#check @RBM.BA.STLKgL
#check @RBM.BA.STStep2ConclgL
#check @RBM.BA.STGdecayWgL
#check @RBM.BA.STGridMartgL
#check @RBM.BA.STGridRepNAtgL
#check @RBM.BA.STGridRepNgL
-- T4s1 (`Chain/GridDuhamelGen`)
#check @RBM.BA.Step2Gen_USemigroup
#check @RBM.BA.step2Gen_USemigroup_band
#check @RBM.BA.Step2Gen_UN_self
#check @RBM.BA.Step2Gen_UN_comp
#check @RBM.BA.bandStep2_Ugen
#check @RBM.BA.AvecNg
#check @RBM.BA.martIncNg
#check @RBM.BA.predIncNg
#check @RBM.BA.bandStep2_predIncN
#check @RBM.BA.StoppedDuhamelNg
#check @RBM.BA.stoppedDuhamelNg
#check @RBM.BA.StoppedAzumaNg
#check @RBM.BA.stoppedAzumaNg
-- U3s1 (`Chain/Step34Gen`): the setting of the ingredient pins, the sample-level controls, the ℰ-term inputs
#check @RBM.BA.STIngRgL
#check @RBM.BA.bandFM_STIngR
#check @RBM.BA.STSEforLngL
#check @RBM.BA.STSEforLnConclgL
#check @RBM.BA.bandFM_STSEforLn
#check @RBM.BA.STmaxLg
#check @RBM.BA.STmaxLKg
#check @RBM.BA.STXiLg
#check @RBM.BA.STXiLKg
#check @RBM.BA.bandStep34_STXiLK
#check @RBM.BA.STegtg
#check @RBM.BA.STksimLKg
#check @RBM.BA.STelklkg
#check @RBM.BA.STeeg
#check @RBM.BA.Step34Gen_LCompat
#check @RBM.BA.Step34Gen_KCompat
#check @RBM.BA.bandStep34_LCompat
#check @RBM.BA.bandStep34_KCompat
#check @RBM.BA.STEKDecaygL
#check @RBM.BA.bandFM_STEKDecay
-- T7a (`Chain/DecayGen`)
#check @RBM.BA.DecayGen_Spec
#check @RBM.BA.DecayGen_bandSpec
#check @RBM.BA.DecayGen_WardPair
#check @RBM.BA.DecayGen_bandWardPair
#check @RBM.BA.STKcalDecaygL
#check @RBM.BA.STDecayLoopUgL
#check @RBM.BA.stDecayLoopUgL_of_step2
-- the BA carrier (statement level only; BA instances are T4-BA's)
#check @RBM.BA.baStep2Mat
#check @RBM.BA.baStep2Mat_toFlowFM
#check @RBM.BA.baFMz
#check @RBM.BA.BAFlow
#check @RBM.BA.BAflowT0
#check @RBM.BA.BAflowLam0
#check @RBM.BA.BAflowEs
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.PsiI
-- the walk, the law and the model-free tools (any `sz`; T2452 `:60`)
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.Sizes.seqXmat
#check @RBM.Gauss.Sizes.seqHflow
#check @RBM.Gauss.gvarF
#check @RBM.Gauss.coordinateMatrix
#check @RBM.Gauss.HighProbAt
#check @RBM.Gauss.loopOf
#check @RBM.Gauss.Sizes.STdiamInf
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.isProbabilityMeasure_pathP
#check @RBM.Path.pathH
#check @RBM.Path.filt
#check @RBM.Path.gridTime
#check @RBM.Path.gridStep
#check @RBM.Path.firstHit
#check @RBM.Path.TimeIcc
#check @RBM.Path.HermTestFun
#check @RBM.Path.map_pathH_eq
#check @RBM.Path.pathH_measurable_filt
#check @RBM.Path.envConst
#check @RBM.ellT
-- T5s2 band files that the five files read (note (1)): the seven vocabulary items, the per-step facts, the one-step drift
#check @RBM.Ind.loopFamN
#check @RBM.Ind.dirDerivN
#check @RBM.Ind.ZfamN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.stoppedEdgeN
#check @RBM.Ind.SubGaussFormN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.stepDecompCN
#check @RBM.Ind.stepDecompCN_Z_subG
#check @RBM.Ind.HermTestFunLoopN
#check @RBM.Ind.hermTestFunLoopN
#check @RBM.Ind.qvPropagatedN
#check @RBM.Ind.GridDriftN
#check @RBM.Ind.gridDriftN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.kStepC
#check @RBM.Ind.uStepC
#check @RBM.Ind.exists_norm_Kcal_le_win
#check @RBM.Ind.Ugen
-- U2 / T7 band inputs of `gridGoodN_holds` (`GridGoodN:930-956`)
#check @RBM.Gauss.Sizes.stSEforLn_holds
#check @RBM.Gauss.Sizes.stEtermDecay
#check @RBM.Gauss.Sizes.stDecayLoopU_of_step2

/-! ## Part 2: the target statements (content binding for targets 2-4) and shapes (not binding) -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **Target 2** (content binding): membership in the good set `GoodSetN` (`Induction/GridGoodN.lean:124`) over `Step2Mat`:
`loopFine H (zt E u)` is `Cm.LM n u H`, `STKloop` is `Cm.K`, `etaT E u` is `Cm.eta n u`; the controls `Ξ̂^{(𝓛-𝒦)}_m(H)` of
target 1 are written out (`STXiLKM`, `:82`); `ellT (sz.L n) (sz.lam n) u` and `sz.Bctl` stay (size level). -/
def T2473_GoodSetNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H.IsHermitian ∧
    (∀ m : ℕ, 1 ≤ m → m < k →
      1 + Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
          (fun p : (Fin m → Bool) × (Fin m → Zd d (sz.L n)) => ‖Cm.LM n u H p.1 p.2 - Cm.K n u p.1 p.2‖) /
        (sz.Bctl n u) ^ m ≤ Γ * Φ) ∧
    (∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 → ∀ (σ : Fin j → Bool) (a : Fin j → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖Cm.LM n u H σ a‖ + ‖Cm.LM n u H σ a - Cm.K n u σ a‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k → ∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STksimLKMg Cm n u H l (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STelklkMg Cm n u H (loopOf σ a)‖ ≤ Γ * ((k : ℝ) * (Γ * Φ) ^ 2) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ‖STegtMg Cm n u H (loopOf σ a)‖ ≤ Γ * (Γ * Φ) * ((sz.Bctl n u) ^ k / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ‖STeeMg Cm n u H σ a a'‖ ≤ Γ * (Γ * Λ) * ((sz.Bctl n u) ^ (2 * k) / Cm.eta n u)) ∧
    (∀ (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a : ℝ) →
        ‖∑ l ∈ Finset.Icc 3 k, STksimLKMg Cm n u H l (loopOf σ a)‖ +
          ‖STelklkMg Cm n u H (loopOf σ a)‖ + ‖STegtMg Cm n u H (loopOf σ a)‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (-D')) ∧
    (∀ (σ : Fin k → Bool) (a a' : Fin k → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf (Fin.append a a') : ℝ) →
        ‖STeeMg Cm n u H σ a a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'))

/-- **Target 3** (content binding): `GoodExitMeasN` (`GridGoodN:411`) over `Step2Mat`, with the exit time `goodExitTauNg`
written out (`gridExitTauN`, `:169`: `firstHit` of the indicator of the complement at the level `1/2`, horizon `K n`) on the
grid walk `Cm.Hpath`. -/
def T2473_GoodExitMeasNg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  ∀ (n k : ℕ) (Γ Λ Φ : ℕ → ℝ) (τ' D' : ℝ) (j : ℕ),
    MeasurableSet[filt sz j] {ω | j < firstHit (fun i (ω' : PathΩ sz) =>
      ({H | T2473_GoodSetNg Cm n (gridTime s v K n i) k (Γ n) (Λ n) (Φ n) τ' D' H}ᶜ).indicator
        (fun _ => (1 : ℝ)) (Cm.Hpath s v K n i ω')) (1 / 2) (K n) ω}

/-- **Target 4, conclusion** (content binding): `GridGoodNConcl` (`GridGoodN:505`) over `(Cm, μ)`: `Prec sz` is `PrecL sz μ`,
`STXiL`/`STXiLK` are U3s1's `STXiLg`/`STXiLKg`, `pathP`/`pathH` are `Cm.Pp`/`Cm.Hpath`, `GoodSetN` is target 2. -/
def T2473_GridGoodNConclg {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) : Prop :=
  ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) → ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) →
    ∀ k : ℕ, 2 ≤ k → ∀ Λ Φ : ℕ → ℝ, (∀ n, 1 ≤ Λ n) → (∀ n, 1 ≤ Φ n) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k + 1 →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n)
        (fun n u ω => STXiLKg Cm.toFlowFM n (u : ℝ) m ω) (fun n _ _ => Φ n)) →
    ∀ q : ℕ, 1 ≤ q →
    PrecL sz μ (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLg Cm.toFlowFM n (u : ℝ) (2 * k - 1) ω *
        (STXiLg Cm.toFlowFM n (u : ℝ) (4 * q) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (q : ℝ))))
      (fun n _ _ => Λ n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε → ∀ τ' : ℝ, 0 < τ' → ∀ D' : ℝ, 0 < D' →
      HighProbAt Cm.Pp sz.size (fun n => {ω | ∀ j ≤ K n,
        T2473_GoodSetNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε) (Λ n) (Φ n) τ' D'
          (Cm.Hpath s v K n j ω)})

/-- **Target 4, the pin** (content binding): `GridGoodN` (`GridGoodN:528`, `STIngR d STAny …`) over a carrier family
`(law, Flow, mkM, T0)` with `mkM` valued in `Step2Mat`, in the shape of `STSEforLngL` (`Chain/Step34Gen.lean:404`). -/
def T2473_GridGoodNgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d STAny law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => T2473_GridGoodNConclg (mkM sz z) (law sz) s t)

/-- Targets 2-4 as Prop values. -/
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ), T2473_GoodExitMeasNg Cm s v K
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ), T2473_GridGoodNConclg Cm μ s t

-- Shapes (band bridges of targets 2-4; the auditor proves them on the branch: target 2 and 3 definitional, target 4 through
-- `bandFM_STIngR`, `Chain/Step34Gen.lean:447`).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
  H ∈ sz.GoodSetN n (E n) u k Γ Λ Φ τ' D' ↔ T2473_GoodSetNg (bandStep2Mat sz E) n u k Γ Λ Φ τ' D' H

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ),
  RBM.Path.GoodExitMeasN sz E s v K ↔ T2473_GoodExitMeasNg (bandStep2Mat sz E) s v K

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ),
  RBM.Gauss.Sizes.GridGoodNConcl sz E s t ↔ T2473_GridGoodNConclg (bandStep2Mat sz E) (Sizes.seqP sz) s t

example : Prop := ∀ d : ℕ,
  RBM.Gauss.Sizes.GridGoodN d ↔
    T2473_GridGoodNgL d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n))

-- Shapes (BA readings, statement level; the BA instances are T4-BA's): targets 2-4 at `baStep2Mat`, along `BAFlow`
-- (the setting as `Chain/Step34GenTw.lean:89-90`).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
  T2473_GoodSetNg (baStep2Mat sz lam0 E) n u k Γ Λ Φ τ' D' H

example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E s v : ℕ → ℝ) (K : ℕ → ℕ),
  T2473_GoodExitMeasNg (baStep2Mat sz lam0 E) s v K

example : Prop :=
  T2473_GridGoodNgL 3 (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0

-- Shape (target 4 (a), per carrier, merged-name premises only; D2 adds W, the measurability compat and the inline form of
-- `DecayGen_Spec`'s use): from the ℰ-term estimates at the flow matrix `Hf`, the loop decay, and the four Eterm decays
-- (band `stEtermDecay`, `Induction/DecayLoopB.lean:2209`; generic owner U2).
example : Prop := ∀ {d : ℕ}, 3 ≤ d → ∀ {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (κm 𝔠 𝔡 : ℝ) (s t : ℕ → ℝ),
  DecayGen_Spec Cm.toFlowFM κm → sz.Admissible 𝔠 𝔡 → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
  (∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1) →
  Step34Gen_LCompat Cm Hf → Step34Gen_KCompat Cm →
  STSEforLnConclgL Cm Hf μ s t → STDecayLoopUgL Cm.toFlowFM μ s t →
  (∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
    STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
      STegtg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    (∀ l : ℕ, STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
      STksimLKg Cm Hf n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
    STEKDecaygL μ s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
      STelklkg Cm Hf n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
    STEKDecaygL μ s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
      STeeg Cm Hf n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i)))) →
  T2473_GridGoodNConclg Cm μ s t

-- Shape (D1 default (a), the walk fact W on explicit data `(g', H₀)`; band `g' = sz.lam`, `H₀ = 0`; BA `g' = 0`,
-- `H₀ = lam0 • PsiI`, `RBM3D/BA/Step2BA.lean:68-72`, `RBM3D/Gauss/BlockAnderson.lean:78-86`).
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ)
    (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (g' : ℕ → ℝ) (H₀ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
  (∀ n, (H₀ n).IsHermitian) ∧ Cm.Pp = pathP (sz.withLam g') ∧ μ = Sizes.seqP (sz.withLam g') ∧
    (∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz), Cm.Hpath s t K n j ω =
      H₀ n + (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from pathH (sz.withLam g') s t K n j ω)) ∧
    ∀ (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), Hf n u ω =
      H₀ n + (show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from Sizes.seqHflow (sz.withLam g') n u ω)

-- Shape (W at the BA carrier: the law conjunct is definitional at `baStep2Mat`).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ), (baStep2Mat sz lam0 E).Pp = pathP (sz.withLam 0)

-- Shape (D2 (2), one text with T2471: the kernel class K1-K4 as compiled in `docs/tickets/checks/T2471-check.lean:208-218`
-- and `t/T2471:RBM3D/Probe/T2471Pins.lean:40`; imported if merged, else this conjunction inline, never a second named Prop).
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ),
  Step2Gen_USemigroup C n ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ v → v ≤ w → w < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' v w a b‖ ≤ (1 - v) / (1 - w)) ∧
  (∀ (σ σ' : Bool) (s t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
    ∑ b, ‖Step2Gen_uKer C n σ σ' s t a b - (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ ≤ |t - s| * (1 - t)⁻¹) ∧
  (∀ (σ σ' : Bool) (v w : ℝ), 0 ≤ w → w < 1 → ∀ a b : Zd d (sz.L n),
    Step2Gen_uKer C n (!σ) (!σ') v w a b = starRingEnd ℂ (Step2Gen_uKer C n σ σ' v w a b))

-- Shape (target 6, `SubGaussFormNg`; target 6 is dropped by the dispatcher answers, T2474 target 4 owns it; kept as a reading):
-- `SubGaussFormN` (`Induction/StepDecompN.lean:206`) at the carrier law `Cm.Pp` (a probability measure, as `StoppedAzumaNg`).
example : Prop := ∀ {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) [IsProbabilityMeasure Cm.Pp] (j : ℕ) (τ : PathΩ sz → ℕ) (F : PathΩ sz → ℂ) (c : ℝ≥0),
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j) (fun ω => ({ω' | j < τ ω'}.indicator F ω).re) c Cm.Pp ∧
  HasCondSubgaussianMGF (filt sz j) ((filt sz).le j) (fun ω => ({ω' | j < τ ω'}.indicator F ω).im) c Cm.Pp

-- Shape (D2 (4), the default `qvFormNg := Re STeeUMg`; band bridge under K4, expected from `|E n| ≤ 2`, cf. the band
-- `qvFormN_eq_re_UgenPairN`, `Induction/NQGood1.lean:230`; the 1a confirms or picks the `conj` form).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (v w : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (a : Fin k → Zd d (sz.L n)),
  |E n| ≤ 2 → |w| < 1 →
    RBM.Ind.qvFormN sz n (E n) v w σ M a = (STeeUMg (bandStep2Mat sz E) n v w M σ a).re

-- Shape (UBA-C1, DECISIONS §273 (1)): the R1 literal, the only admissible comparison text if a statement here ever crosses
-- size level and kernel level (not expected).
example : Prop := ∀ {d : ℕ} (sz : Sizes d) (gK : ℕ → ℝ) (A : ℝ),
  ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2

end RBM.BA

end

/-! ## Part 3 (G1): the public band names that the U rows read (census of uses on `main`; files not edited) -/
-- `Induction/GridGoodN.lean` (targets 1-4)
#check @RBM.Gauss.Sizes.STmaxLM
#check @RBM.Gauss.Sizes.STmaxLKM
#check @RBM.Gauss.Sizes.STXiLM
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.gridGood_STXiLKM_seqHflow
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Path.gridExitTauN
#check @RBM.Path.goodExitTauN
#check @RBM.Path.gridExitTauN_le
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
#check @RBM.Path.gridExitTauN_measurableSet
#check @RBM.Gauss.Sizes.MeasurableGoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Path.GoodExitMeasN
#check @RBM.Path.goodExitMeasN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.GridGoodN
#check @RBM.Gauss.Sizes.gridGoodN_holds
-- `Induction/GridEnvelopeN.lean` (target 5)
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.sum_gridStep_div_etaT_le
#check @RBM.Ind.SumWeightedStepErrN_Stmt
#check @RBM.Ind.sum_weighted_stepErrN_le
-- `Induction/GridAssemblyN.lean` (target 7)
#check @RBM.Ind.StoppedAzumaZN
#check @RBM.Ind.qvFormN
#check @RBM.Ind.AzumaSubGN
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.YMomentsConclN
#check @RBM.Ind.YMomentsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.stoppedAzumaZN
#check @RBM.Ind.assembledN
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.gridAsm_stronglyMeasurable_YvecN
-- `Induction/AzumaProxyN.lean` (targets 8-9; the last one is band-only, its reader is `MainIndBase`)
#check @RBM.Ind.azumaSubGN
#check @RBM.Ind.azumaProxy_subG_ugen
#check @RBM.Ind.azumaProxy_subG_goodExit
#check @RBM.Ind.azumaProxy_pos_gridExitTauN
#check @RBM.Ind.azumaProxy_pathH_zero_of_s_zero
#check @RBM.Ind.zero_mem_goodSetN
#check @RBM.Ind.zero_mem_goodSetN_of_levels
#check @RBM.Ind.azumaProxy_loopFine_sub_STKloop
-- `Induction/AzumaProxyN2.lean` (target 10)
#check @RBM.Ind.AzumaProxyN_integral_normPow8_incr_le
#check @RBM.Ind.YMomentsUnifN
#check @RBM.Ind.yMomentsUnifN
#check @RBM.Ind.yMomentsN_of_unif
#check @RBM.Ind.yMomentsN
#check @RBM.Ind.AzumaProxyN_stopW
#check @RBM.Ind.AzumaProxyN_YfieldsW
#check @RBM.Ind.AzumaProxyN_c0_pos_pub
#check @RBM.Ind.AzumaProxyN_inv_one_sub_le_pub
#check @RBM.Ind.AzumaProxyN_etaT_inv_le_pub
#check @RBM.Ind.AzumaProxyN_P_le_pub
#check @RBM.Ind.AzumaProxyN_rowsum_Ugen_pub
