/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Evolution.Prec
import RBM3D.Induction.NewPQ
import RBM3D.Loop.GLoopFlow

/-!
# The Step 3-4 vocabulary over the flow carrier (BA-U row U3s1, ticket T2457)

Design gate `docs/reports/T2457-prove.md` (a)-(a⁵), probe `RBM3D/Probe/T2457Pins.lean` (branch `t/T2457`,
never merged).  The band files `Induction/Step34Pins.lean`, `Induction/Step34PinsP.lean` are **not** edited:
this file states the generic form of every declaration of theirs that reads a band object, over a carrier
`C : FlowFM sz` (resp. `Cm : Step2Mat sz`) and a law `μ`, and bridges the two.  There is no `BA/` import
(the TLF-C5 examples and the BA statement-level readings are in the leaf `Chain/Step34GenTw.lean`).

* **Names.** the band name plus `g` (data) or `gL` (a `Prop`); bridges `bandFM_<band>` (`Iff.rfl` or proved)
  and `bandStep34_<band>` (`rfl`).
* **D1** (list-indexed loops at a sample, target 3): `STLIg`, ..., `STeeg` are T8's matrix forms
  (`Chain/Step2Gen.lean:923-964`) at the flow matrix `Hf n τ ω`; the carrier facts `Step34Gen_LCompat`,
  `Step34Gen_KCompat` (not fields) tie `C.L`, `C.K` to `Cm.LIM ∘ Hf`, `Cm.KI`.
* **D2** (the settings of the ingredient pins, target 5): the shape `(law, Flow, mk, T0)` of `STStep2G`.
* **D3** (the `STEK` vocabulary, target 6): the five consumer forms read the kernel only as `Step2Gen_UN C`;
  the model class `Ker sz C gK κ` carries the kernel coupling `gK` (band `sz.lam`, BA `lam0`), which the
  window, the decay hypothesis, the ratio and the cutoff `ellT` of the forms read.  `STEKDecaygL` and
  `STEKLowgL` stay at `sz.lam` (the reading of conjunct 4 of `twSteps`).  The comparison hypothesis R1
  `∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (CONTROL H254 (2), (4), DECISIONS §273 (1), (3)),
  written inline in each lemma, converts the window (a), the ratio (c), `ellT` (d) and the decay (e) from `sz.lam` to `gK`
  (`step34Gen_*`).  `STEKNonzerogL` carries the parameter `Aof` of the threshold `(1 - s) L² ≤ Aof κ · gK²`.
* **Band instances** `stek_*gL_band`, `stNewPQgL_band` are premise-free (from `Evolution/Prec`, `Induction/NewPQ`).
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1 (TLF-C5): `STLmaxUgL`, `STLKUgL` -/

section Target1

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- **`(Eq:LGxb)`** uniformly in `u ∈ [s,t]` over a carrier: conjunct 2 of `twSteps` (`BA/TwistPins.lean:135-136`) verbatim; band
`STLmaxU` (`Induction/Step34Pins.lean:176`). -/
def STLmaxUgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))

/-- **`(Eq:L-KGt-flow)`** uniformly in `u ∈ [s,t]` over a carrier: conjunct 3 of `twSteps` (`BA/TwistPins.lean:137-138`) verbatim; band
`STLKU` (`Induction/Step34Pins.lean:184`). -/
def STLKUgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)

/-- The endpoint `u = t` of `STLmaxUgL` is `STLmaxgL` at `t` (band `STLmax_of_STLmaxU`, `Step34Pins.lean:284`). -/
theorem STLmaxgL_of_STLmaxUgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLmaxUgL C μ s t) : STLmaxgL C μ t := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- The endpoint `u = t` of `STLKUgL` is `STLKgL` at `t` (band `STLK_of_STLKU`, `Step34Pins.lean:291`). -/
theorem STLKgL_of_STLKUgL {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLKUgL C μ s t) : STLKgL C μ t := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

end Target1

/-! ## 2. Target 2: the loop maxima and the control parameters over a carrier -/

section Target2

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- `STmaxL` (`Step34Pins.lean:51`): `max_{σ,a} |𝓛^{(k)}_{v,σ,a}|`. -/
def STmaxLg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n v p.1 p.2 ω‖)

/-- `STmaxLK` (`Step34Pins.lean:56`): `max_{σ,a} |(𝓛 - 𝒦)^{(k)}_{v,σ,a}|`. -/
def STmaxLKg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n v p.1 p.2 ω - C.K n v p.1 p.2‖)

/-- `STXiL` (`Step34Pins.lean:63`): `Ξ̂^{(𝓛)}_{v,k}`. -/
def STXiLg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ := 1 + STmaxLg C n v k ω / (sz.Bctl n v) ^ (k - 1)

/-- `STXiLK` (`Step34Pins.lean:68`): `Ξ̂^{(𝓛-𝒦)}_{v,k}`. -/
def STXiLKg (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ := 1 + STmaxLKg C n v k ω / (sz.Bctl n v) ^ k

/-- `STLKtensor` (`Step34Pins.lean:538`): `(L - K)^{(m+1)}_{u,σ}` as a tensor of `m + 1` indices. -/
def STLKtensorg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin (m + 1) → Bool) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => C.L n u σ a ω - C.K n u σ a

end Target2

/-! ## 3. Target 3 (D1): the list-indexed loops and the ℰ-terms at a sample -/

section Target3

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
  (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)

/-- `STLI` (`Step34Pins.lean:107`) at the flow matrix `Hf n τ ω`: T8's `STLIMg`. -/
def STLIg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := STLIMg Cm n τ (Hf n τ ω) I
/-- `STKI` (`Step34Pins.lean:111`): `𝒦_{τ,I}` of the carrier. -/
def STKIg (n : ℕ) (τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := Cm.KI n τ I
/-- `STLKI` (`Step34Pins.lean:115`). -/
def STLKIg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := STLKIMg Cm n τ (Hf n τ ω) I
/-- `STksimLK` (`Step34Pins.lean:120`). -/
def STksimLKg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := STksimLKMg Cm n τ (Hf n τ ω) l I
/-- `STelklk` (`Step34Pins.lean:133`). -/
def STelklkg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := STelklkMg Cm n τ (Hf n τ ω) I
/-- `STavgErr` (`Step34Pins.lean:140`). -/
def STavgErrg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a : Zd d (sz.L n)) : ℂ := STavgErrMg Cm n τ (Hf n τ ω) σ a
/-- `STegt` (`Step34Pins.lean:144`). -/
def STegtg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ := STegtMg Cm n τ (Hf n τ ω) I
/-- `STee` (`Step34Pins.lean:159`). -/
def STeeg (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) : ℂ :=
  STeeMg Cm n τ (Hf n τ ω) σ a a'

/-- **Carrier fact (target 3), not a field**: `C.L` is the list-indexed loop value at the flow matrix, `𝓛^{(k)}_{t,σ,a} = 𝓛_{t, (σ,a)}(H_t(ω))`. -/
def Step34Gen_LCompat : Prop := ∀ (n : ℕ) (t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ),
  Cm.L n t σ a ω = Cm.LIM n t (Hf n t ω) (KLloopOf d (sz.L n) σ a)

/-- **Carrier fact (target 3), not a field**: `C.K` is the list-indexed `𝒦`, `𝒦^{(k)}_{t,σ,a} = 𝒦_{t,(σ,a)}`. -/
def Step34Gen_KCompat : Prop := ∀ (n : ℕ) (t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
  Cm.K n t σ a = Cm.KI n t (KLloopOf d (sz.L n) σ a)

end Target3

/-! ## 4. Target 4: the conclusions of the ingredient pins over a carrier -/

section Target4a

variable {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz)
  (Hf : ∀ n : ℕ, ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (μ : Measure sz.SeqΩ)

/-- `STSEforLnConcl` (`Step34Pins.lean:363`) over `(Cm, Hf, μ)` (the four estimates of the ℰ terms, `lem:SEforLn`); `etaT (E n) u` is
`Cm.eta n u`.  Reads target 3. -/
def STSEforLnConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegtg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).1 ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ)) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STksimLKg Cm Hf n (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k - l + 2) ω)) ∧
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklkg Cm Hf n (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / Cm.eta n (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLKg Cm.toFlowFM n (p.1 : ℝ) (k + 2 - n') ω *
              (STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').1 ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLKg Cm.toFlowFM n (p.1 : ℝ) k ω)) ∧
    (∀ q : ℕ, 1 ≤ q →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STeeg Cm Hf n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / Cm.eta n (p.1 : ℝ) *
          (STXiLg Cm.toFlowFM n (p.1 : ℝ) (2 * k - 1) ω * STXiLg Cm.toFlowFM n (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ))))))

end Target4a

section Target4

variable {d : ℕ} {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `STIterHyp` (`Step34Pins.lean:469`): `(eq:iteration_induc)` at `(r,l)` over a carrier; `etaT (E n) u` is `Cf.eta n u`. -/
def STIterHypgL (s t : ℕ → ℝ) (A : ℕ → ℝ) (r l : ℕ) : Prop :=
  PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 r ω)
    (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) r l)

end Target4

/-! ## 5. Target 5 (D2): Steps 3-4 per regime and the settings of the ingredient pins over a carrier family `(law, Flow, mk, T0)` -/

/-- **Step 3 per regime over a carrier** (content binding `T2457_Step3RgL`): `STStep3R` (`Induction/Step34Pins.lean:250`) in the shape of
`STStep2G` (`Chain/Step2Gen.lean:591`). -/
def STStep3RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t → STStep1LoopgL (mk sz z) (law sz) s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → STLmaxUgL (mk sz z) (law sz) s t

/-- **Step 4 per regime over a carrier** (content binding `T2457_Step4RgL`): `STStep4R` (`Induction/Step34Pins.lean:261`). -/
def STStep4RgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t → STStep1LoopgL (mk sz z) (law sz) s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → STLmaxUgL (mk sz z) (law sz) s t →
          STLKUgL (mk sz z) (law sz) s t

/-- **The setting of an ingredient pin over a carrier family** (D2; shape `T2457_IngRgL`): `STIngR` (`Step34Pins.lean:445`); the conclusion reads
`(sz, z)`, so an instance can read `mk sz z`, its `Step2Mat` extension and the flow matrix. -/
def STIngRgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STKwardgL (mk sz z) (law sz) →
          STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t →
          STStep2ConclgL (mk sz z) (law sz) s t Cd → Concl sz z s t

/-- `STSEforLn` (`Step34Pins.lean:456`): the ℰ-term instance.  `mkM` is `Step2Mat`-valued and `mk = (mkM sz z).toFlowFM` by construction (no
equation hypothesis); `Hf sz z` is the flow matrix. -/
def STSEforLngL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => STSEforLnConclgL (mkM sz z) (Hf sz z) (law sz) s t)

/-! ## 6. Target 6 (E-C1, D3): the `STEK` vocabulary over the carrier kernel `Step2Gen_UN C`

The class `Ker sz C gK κ` (D3 (a)) says which carriers the form applies to and carries the kernel coupling `gK` (D3 (b)); the form reads the kernel only as
`Step2Gen_UN C`. -/

section Target6

variable {d : ℕ}

/-- The window of `lem:sum_decay` (`Step34Pins.lean:607`) at the kernel coupling `gK` (band `sz.lam`): `STEKWin sz s t ↔ STEKWinKgL sz sz.lam s t`. -/
def STEKWinKgL (sz : Sizes d) (gK : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ t n) ∧ (∀ n, t n ≤ 1 - gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) ∧ (∀ n, t n < 1) ∧
    ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ)⁻¹ ≤ (1 - t n) / (1 - s n)

/-- `(deccA0)` w.h.p. at the kernel coupling `gK` (`EKFastDecay (gK n)`); `STEKDecay` is the case `gK = sz.lam`. -/
def STEKDecayKgL {sz : Sizes d} (gK : ℕ → ℝ) (μ : Measure sz.SeqΩ) {m : ℕ} (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    HighProbAt μ sz.size (fun n => {ω | ∀ v : TimeIcc s t n,
      EKFastDecay (gK n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D (𝒜 n v ω)})

/-- **Target 6, `STEKDecaygL`** (content binding `T2457_EKDecaygL`; `STEKDecay`, `Step34Pins.lean:595`) at a law `μ`: the coupling is `sz.lam`.
T7/U2 (`stEtermDecaygL`) read it unchanged (CONTROL H249 (2), decision (B)). -/
def STEKDecaygL {sz : Sizes d} (μ : Measure sz.SeqΩ) {m : ℕ} (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop :=
  STEKDecayKgL sz.lam μ s t 𝒜

/-- **Target 6, `STEKLowgL`** (content binding `T2457_EKLowgL`; `STEKLow`, `Step34Pins.lean:602`) at a law `μ`. -/
def STEKLowgL {sz : Sizes d} (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) : Prop :=
  ∃ b : ℝ, HighProbAt μ sz.size (fun n => {ω | ∀ v : TimeIcc s t n, ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω})

/-- The model class of the kernel pins (D3 (a)): `Ker sz C gK κ` says that the carrier `C` is of the model (its kernel `Step2Gen_UN C` is the
one of the stage-E theorem at the coupling `gK`, with the bulk parameter `κ`).  The band class is `STEKBandKer`; the BA class is U3-BA's. -/
abbrev STEKKer (d : ℕ) := ∀ sz : Sizes d, FlowFM sz → (ℕ → ℝ) → ℝ → Prop

/-- **`lem:sum_Ndecay`** `(sum_res_Ndecay)` (`Step34Pins.lean:613`) over `Step2Gen_UN C`. -/
def STEKSumNdecaygL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Ker : STEKKer d) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (C : FlowFM sz) (gK : ℕ → ℝ), Ker sz C gK κ → (∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ),
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v ω, 0 ≤ X n v ω) →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * X n v ω)

/-- **`(sum_res_2_NAL)`** (`Step34Pins.lean:637`) over `Step2Gen_UN C`, `σ` non-alternating. -/
def STEKSumRes2NALgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Ker : STEKKer d) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (C : FlowFM sz) (gK : ℕ → ℝ), Ker sz C gK κ → (∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) →
    ∀ s t : ℕ → ℝ, STEKWinKgL sz gK s t → ∀ σ : Fin n_ → Bool, (∃ k, σ k = σ (finRotate n_ k)) →
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecayKgL gK (law sz) s t 𝒜 →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLowgL (law sz) s t X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X n v ω)

/-- **`(sum_res_2)`** (`Step34Pins.lean:651`; shape `T2457_EKSumRes2gL`) over `Step2Gen_UN C`, sum-zero tensors. -/
def STEKSumRes2gL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Ker : STEKKer d) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (C : FlowFM sz) (gK : ℕ → ℝ), Ker sz C gK κ → (∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) →
    ∀ s t : ℕ → ℝ, STEKWinKgL sz gK s t → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecayKgL gK (law sz) s t 𝒜 →
    (∀ n v ω, EKSumZero (𝒜 n v ω)) → ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLowgL (law sz) s t X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)

/-- **`lem:sum_decay_nonzero`** (`Step34Pins.lean:666`), the **A-form** (UBA-C1 (b); CONTROL H250 (3)): the threshold `1 - lam²/L² ≤ s` of the band pin is
`(1 - s n) L² ≤ Aof κ · gK n²`; the band instance is `Aof = 1`, `gK = sz.lam`, the BA instance `Aof κ = (κ+1)/κ` is U3-BA's. -/
def STEKNonzerogL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Ker : STEKKer d) (Aof : ℝ → ℝ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → 1 ≤ Aof κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (C : FlowFM sz) (gK : ℕ → ℝ), Ker sz C gK κ → (∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) →
    ∀ s t : ℕ → ℝ, (∀ n, (1 - s n) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ Aof κ * gK n ^ 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → ∀ σ : Fin n_ → Bool, ∀ A : Finset (Fin n_), (∀ i, σ i ≠ σ (finRotate n_ i) → i ∈ A) →
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ),
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v ω, 0 ≤ X n v ω) →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω))‖) X

end Target6

section Target6Bridge

variable {d : ℕ}

/-- `0 < sz.lam n ≤ 𝔡⁻¹` eventually, from `Admissible` (the hypothesis `hg` of the five forms at the band class). -/
theorem step34Gen_band_hg {sz : Sizes d} {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [h.2.2.2.2] with n hn
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩

/-- `W_n → ∞` from `Admissible` (`Bandwidth` and `SizeTendsto`). -/
theorem step34Gen_W_tendsto {sz : Sizes d} {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hsize, hbw, -⟩ := h
  exact tendsto_atTop_mono' _ hbw ((tendsto_rpow_atTop h𝔠).comp hsize)

end Target6Bridge

/-! ### UBA-C1: the comparison `Cmp`, text R1 (CONTROL H254 (2), (4); DECISIONS §273 (1), (3)), written inline in each lemma

`∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2` (band: `gK = sz.lam`, `A = 1`; BA: `gK = BAflowLam0`, `A = (κ+1)/κ`).
The window step (a) reads only `gK n ^ 2 ≤ sz.lam n ^ 2`; the cutoff step (d) splits on the sign of `sz.lam n` (private per-index lemma). -/

section UBAC1

variable {d : ℕ}

private theorem step34Gen_cmp_idx {g l A : ℝ} (h1 : 0 ≤ g * l) (h2 : g ^ 2 ≤ l ^ 2) (h3 : l ^ 2 ≤ A * g ^ 2) :
    (0 < g → 0 < l ∧ g ≤ l) ∧ (l ≤ 0 → g ≤ 0) := by
  have key : 0 < g → 0 < l ∧ g ≤ l := by
    intro hg
    have hl0 : 0 ≤ l := by
      by_contra hneg
      exact absurd h1 (not_le.2 (mul_neg_of_pos_of_neg hg (not_le.1 hneg)))
    have hlpos : 0 < l := by
      rcases hl0.eq_or_lt with h | h
      · subst h; nlinarith
      · exact h
    exact ⟨hlpos, by nlinarith⟩
  exact ⟨key, fun hl => by by_contra hg; exact absurd (key (not_le.1 hg)).1 (not_lt.2 hl)⟩

/-- (a) The window at `sz.lam` is the window at `gK`: only `gK n ^ 2 ≤ sz.lam n ^ 2` is read, at every `n`. -/
theorem step34Gen_winK_of_cmp {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2)
    {s t : ℕ → ℝ} (hwin : STEKWinKgL sz sz.lam s t) : STEKWinKgL sz gK s t := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := hwin
  refine ⟨h0, h1, fun n => ?_, h3, h4⟩
  have : gK n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right (hcmp n).2.1 (by positivity)
  linarith [h2 n]

private theorem step34Gen_ratio_pt {X Y a b A : ℝ} (hX : 0 ≤ X) (hXY : X ≤ Y) (hYA : Y ≤ A * X) (hA : 1 ≤ A)
    (ha : 0 ≤ a) (hb : 0 < b) : (X + a) / (X + b) ≤ A * ((Y + a) / (Y + b)) := by
  have hY : 0 ≤ Y := hX.trans hXY
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : 0 ≤ (A - 1) * X * Y := mul_nonneg (mul_nonneg (sub_nonneg.2 hA) hX) hY
  have e0 : 0 ≤ (A - 1) * Y := mul_nonneg (sub_nonneg.2 hA) hY
  have e2 : 0 ≤ b * (A * Y - X) := mul_nonneg hb.le (by linarith)
  have e3 : 0 ≤ a * (A * X - Y) := mul_nonneg ha (by linarith)
  have e4 : 0 ≤ (A - 1) * a * b := mul_nonneg (mul_nonneg (sub_nonneg.2 hA) ha) hb.le
  nlinarith [e1, e2, e3, e4]

/-- (c) The ratio loss: `r(gK; v, t) ≤ A · r(sz.lam; v, t)` for `t < 1` (no relation between `v` and `t` is read). -/
theorem step34Gen_ratio_le {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A)
    (n : ℕ) {v t : ℝ} (ht : t < 1) :
    (gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - t|) ≤ A * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - t|)) :=
  step34Gen_ratio_pt (sq_nonneg _) (hcmp n).2.1 (hcmp n).2.2 hA (abs_nonneg _) (abs_pos.2 (by linarith))

/-- (c) The ratio loss to the power `n_`: `r(gK)^{n_} ≤ A^{n_} r(sz.lam)^{n_}`. -/
theorem step34Gen_ratio_pow_le {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A)
    (n : ℕ) {v t : ℝ} (ht : t < 1) (n_ : ℕ) :
    ((gK n ^ 2 + |1 - v|) / (gK n ^ 2 + |1 - t|)) ^ n_ ≤ A ^ n_ * ((sz.lam n ^ 2 + |1 - v|) / (sz.lam n ^ 2 + |1 - t|)) ^ n_ := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (step34Gen_ratio_le hcmp hA n ht) n_

private theorem step34Gen_min_aux {a M L c : ℝ} (hL : 0 ≤ L) (hc : 1 ≤ c) (ha : a ≤ c * M) : min a L ≤ c * min M L := by
  rcases le_total M L with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans ha
  · rw [min_eq_right h]; exact (min_le_right _ _).trans (le_mul_of_one_le_left hL hc)

/-- (d) `ellT` goes up by at most `√A`: `ellT L l u ≤ √A · ellT L g u` from R1 and `1 ≤ A`. -/
private theorem step34Gen_ellT_ge_pt {L : ℕ} {g l A : ℝ} (u : ℝ) (h1 : 0 ≤ g * l) (h2 : g ^ 2 ≤ l ^ 2) (h3 : l ^ 2 ≤ A * g ^ 2)
    (hA : 1 ≤ A) : ellT L l u ≤ Real.sqrt A * ellT L g u := by
  obtain ⟨hpos, hneg⟩ := step34Gen_cmp_idx h1 h2 h3
  have hs : 0 ≤ Real.sqrt |1 - u| := Real.sqrt_nonneg _
  have hc : 1 ≤ Real.sqrt A := Real.one_le_sqrt.2 hA
  have hL : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg _
  unfold ellT
  rcases le_or_gt l 0 with hl | hl
  · have hg := hneg hl
    have hq1 : g / Real.sqrt |1 - u| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hg hs
    have hq2 : l / Real.sqrt |1 - u| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hl hs
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    have : 0 ≤ min 1 (L : ℝ) := le_min zero_le_one hL
    exact le_mul_of_one_le_left this hc
  · have hg : 0 < g := by
      rcases lt_or_ge 0 g with hg | hg
      · exact hg
      · exfalso
        have hg0 : g = 0 := by
          by_contra hne
          have hgl' : g < 0 := lt_of_le_of_ne hg hne
          have := mul_neg_of_neg_of_pos hgl' hl
          linarith
        subst hg0
        nlinarith
    have hlg' : l ≤ Real.sqrt A * g := by
      have h0 : 0 ≤ Real.sqrt A * g := mul_nonneg (Real.sqrt_nonneg _) hg.le
      rw [← pow_le_pow_iff_left₀ hl.le h0 two_ne_zero, mul_pow, Real.sq_sqrt (by linarith)]
      exact h3
    refine step34Gen_min_aux hL hc ?_
    have hq : l / Real.sqrt |1 - u| ≤ Real.sqrt A * (g / Real.sqrt |1 - u|) := by
      rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hlg' hs
    refine max_le (hq.trans ?_) ?_
    · exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.sqrt_nonneg _)
    · calc (1 : ℝ) ≤ Real.sqrt A * 1 := by linarith
        _ ≤ Real.sqrt A * max (g / Real.sqrt |1 - u|) 1 := mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)

/-- (d) `ellT (sz.lam n) ≤ √A · ellT (gK n)`. -/
theorem step34Gen_ellT_ge {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A) (n : ℕ) (u : ℝ) :
    ellT (sz.L n) (sz.lam n) u ≤ Real.sqrt A * ellT (sz.L n) (gK n) u :=
  step34Gen_ellT_ge_pt u (hcmp n).1 (hcmp n).2.1 (hcmp n).2.2 hA

private theorem step34Gen_fastDecay_pt {d L m : ℕ} {g l A s W ε D : ℝ} {𝒜 : (Fin m → Zd d L) → ℂ}
    (h1 : 0 ≤ g * l) (h2 : g ^ 2 ≤ l ^ 2) (h3 : l ^ 2 ≤ A * g ^ 2) (hA : 1 ≤ A) (hW : 0 < W)
    (hsq : Real.sqrt A ≤ W ^ (ε / 2)) (h : EKFastDecay l s W (ε / 2) D 𝒜) : EKFastDecay g s W ε D 𝒜 := by
  intro a ⟨i, j, hij⟩
  refine h a ⟨i, j, le_trans ?_ hij⟩
  have hl := step34Gen_ellT_ge_pt (L := L) s h1 h2 h3 hA
  have hWe : W ^ ε = W ^ (ε / 2) * W ^ (ε / 2) := by rw [← Real.rpow_add hW]; ring_nf
  have hW0 : 0 ≤ W ^ (ε / 2) := Real.rpow_nonneg hW.le _
  have hE : 0 ≤ ellT L g s := le_min (le_trans zero_le_one (le_max_right _ _)) (Nat.cast_nonneg _)
  calc W ^ (ε / 2) * ellT L l s ≤ W ^ (ε / 2) * (Real.sqrt A * ellT L g s) := mul_le_mul_of_nonneg_left hl hW0
    _ ≤ W ^ (ε / 2) * (W ^ (ε / 2) * ellT L g s) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq hE) hW0
    _ = W ^ ε * ellT L g s := by rw [hWe]; ring

/-- (e) The decay hypothesis at `sz.lam` (the pinned `STEKDecaygL`) gives the decay hypothesis at `gK`: decay beyond `W^{ε/2} ℓ(sz.lam)` gives decay beyond
`W^ε ℓ(gK)` once `√A ≤ W^{ε/2}`, which holds eventually since `W_n → ∞` (`step34Gen_W_tendsto`). -/
theorem step34Gen_decayK_of_cmp {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (hA : 1 ≤ A)
    (hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop) (μ : Measure sz.SeqΩ) {m : ℕ} {s t : ℕ → ℝ}
    {𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ} (h : STEKDecayKgL sz.lam μ s t 𝒜) :
    STEKDecayKgL gK μ s t 𝒜 := by
  intro ε D hε hD
  refine Gauss.HighProbAt.mono (h (ε / 2) D (half_pos hε) hD) ?_
  have hev : ∀ᶠ n in atTop, Real.sqrt A ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hW).eventually (eventually_ge_atTop (Real.sqrt A))
  filter_upwards [hev] with n hn ω hω v
  exact step34Gen_fastDecay_pt (hcmp n).1 (hcmp n).2.1 (hcmp n).2.2 hA (by exact_mod_cast sz.W_pos n) hn (hω v)

end UBAC1

/-! ## 7. Target 7 (D3): `lem: newPQ` over a model class -/

/-! ## 8. Target 9: compiled nonempty instances at `d = 3`

Data of `Induction/Step34Pins.lean` §7 and `Evolution/Prec.lean` §4: `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)`),
`z0`, `s ≡ 0`, `t ≡ 1/16`, `κ = 1/10`, `n_ = 2`; `szB` (`L = 4`, `W = n + 4`, `lam = 1`) for case (ii).  Hypotheses that are other gates' unproved pins
(`STLmaxUgL`, `STStep3RgL`, ..., owed by U3s4 / U3-BA) stay hypotheses of the `example`s; every deterministic hypothesis is discharged. -/

/-! ### Targets 1 and 5: the endpoints and the Step 3-4 pins at the band reading -/

/-! ### Targets 2-4: the loops and the ℰ-terms at a sample, `sz0`, `n = 0` -/

/-! ### Target 6: the `STEK` vocabulary at `sz0`

The tensor family is `δ₀` (point mass at `0`, as in `Evolution/Prec.lean` §4), and `Az = δ₀ ⊗ (δ₀ - δ_e)` for the sum-zero form; the control is `X ≡ 1`. -/

/-! ### Target 7: `STNewPQgL` at the band class -/

/-! ### UBA-C1 (R1), (a), (c), (d), (e): band `gK = sz.lam`, `A = 1`; non-band `gK = sz.lam / 2`, `A = 4`; negative `lam` -/

end RBM.BA

end
