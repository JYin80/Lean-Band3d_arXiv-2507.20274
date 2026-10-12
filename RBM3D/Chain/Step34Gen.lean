/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.Step34PinsP
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

section Target1Bridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

theorem bandFM_STLmaxU : STLmaxU sz E s t ↔ STLmaxUgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STLKU : STLKU sz E s t ↔ STLKUgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl

end Target1Bridge

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

/-- `STsupXiLK` (`Step34Pins.lean:394`): `sup_{w ∈ [s,u]} Ξ̂^{(𝓛-𝒦)}_{w,k}`. -/
def STsupXiLKg (n : ℕ) (s u : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ := ⨆ w : Set.Icc s u, STXiLKg C n (w : ℝ) k ω

/-- `STLKtensor` (`Step34Pins.lean:538`): `(L - K)^{(m+1)}_{u,σ}` as a tensor of `m + 1` indices. -/
def STLKtensorg (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin (m + 1) → Bool) : (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => C.L n u σ a ω - C.K n u σ a

end Target2

section Target2Bridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (v : ℝ) (k : ℕ) (ω : sz.SeqΩ)

theorem bandStep34_STmaxL : STmaxL sz n (E n) v k ω = STmaxLg (bandFM sz E) n v k ω := rfl
theorem bandStep34_STmaxLK : STmaxLK sz n (E n) v k ω = STmaxLKg (bandFM sz E) n v k ω := rfl
theorem bandStep34_STXiL : STXiL sz n (E n) v k ω = STXiLg (bandFM sz E) n v k ω := rfl
theorem bandStep34_STXiLK : STXiLK sz n (E n) v k ω = STXiLKg (bandFM sz E) n v k ω := rfl
theorem bandStep34_STsupXiLK (s u : ℝ) : STsupXiLK sz n (E n) s u k ω = STsupXiLKg (bandFM sz E) n s u k ω := rfl
theorem bandStep34_STLKtensor {m : ℕ} (σ : Fin (m + 1) → Bool) :
    STLKtensor sz n (E n) v ω σ = STLKtensorg (bandFM sz E) n v ω σ := rfl

end Target2Bridge

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

section Target3Bridge

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (τ : ℝ) (ω : sz.SeqΩ)

theorem bandStep34_STLI (I : LoopIdx (Zd d (sz.L n))) :
    STLI sz n (E n) τ ω I = STLIg (bandStep2Mat sz E) (seqHflow sz) n τ ω I := rfl
theorem bandStep34_STKI (I : LoopIdx (Zd d (sz.L n))) : STKI sz n (E n) τ I = STKIg (bandStep2Mat sz E) n τ I := rfl
theorem bandStep34_STLKI (I : LoopIdx (Zd d (sz.L n))) :
    STLKI sz n (E n) τ ω I = STLKIg (bandStep2Mat sz E) (seqHflow sz) n τ ω I := rfl
theorem bandStep34_STksimLK (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) :
    STksimLK sz n (E n) τ ω l I = STksimLKg (bandStep2Mat sz E) (seqHflow sz) n τ ω l I := rfl
theorem bandStep34_STelklk (I : LoopIdx (Zd d (sz.L n))) :
    STelklk sz n (E n) τ ω I = STelklkg (bandStep2Mat sz E) (seqHflow sz) n τ ω I := rfl
theorem bandStep34_STavgErr (σ : Bool) (a : Zd d (sz.L n)) :
    STavgErr sz n (E n) τ ω σ a = STavgErrg (bandStep2Mat sz E) (seqHflow sz) n τ ω σ a := rfl
theorem bandStep34_STegt (I : LoopIdx (Zd d (sz.L n))) :
    STegt sz n (E n) τ ω I = STegtg (bandStep2Mat sz E) (seqHflow sz) n τ ω I := rfl
theorem bandStep34_STee {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    STee sz n (E n) τ ω σ a a' = STeeg (bandStep2Mat sz E) (seqHflow sz) n τ ω σ a a' := rfl

/-- The band carrier facts (`loopM_eq_loopL`, `GLoopFlow.lean:127`; `STKloop` is `KLK ∘ KLloopOf`). -/
theorem bandStep34_LCompat : Step34Gen_LCompat (bandStep2Mat sz E) (seqHflow sz) := by
  intro n t k σ a ω
  exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
theorem bandStep34_KCompat : Step34Gen_KCompat (bandStep2Mat sz E) := fun n t k σ a => rfl

end Target3Bridge

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

/-- `STXiBoot`(`Step34Pins.lean:414`): `(am;asoi222)`, the bootstrap of `lem:STOeq_Qt` over a carrier. -/
def STXiBootgL (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)

/-- `STNQConcl` (`Step34Pins.lean:428`): `lem:STOeq_NQ`, `(am;asoiuw)`, over a carrier. -/
def STNQConclgL (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q ω => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * STsupXiLKg Cf n (s n) (q.1 : ℝ) n_ ω +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

/-- `STNQConcl'` (`Step34PinsP.lean:53`): the primed `lem:STOeq_NQ` (deterministic self-term) over a carrier. -/
def STNQConclgL' (s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Cf.L n (q.1 : ℝ) q.2.1.1 q.2.2 ω - Cf.K n (q.1 : ℝ) q.2.1.1 q.2.2‖ / (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

/-- `STIterHyp` (`Step34Pins.lean:469`): `(eq:iteration_induc)` at `(r,l)` over a carrier; `etaT (E n) u` is `Cf.eta n u`. -/
def STIterHypgL (s t : ℕ → ℝ) (A : ℕ → ℝ) (r l : ℕ) : Prop :=
  PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 r ω)
    (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) r l)

/-- `STWardTypeP` (`Step34Pins.lean:549`): `(eq:Ward_typeP)` over a carrier.  The mollifier cutoff is the size-level `sz.lam n` (UBA-C1). -/
def STWardTypePgL (s t : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (C c : ℝ), 1 ≤ m →
    ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) →
      PrecL sz μ (U := fun n => TimeIcc s t n) (fun n u ω => STXiLKg Cf n (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) →
      PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n)))
        (fun n q ω => ‖STPsum (d := d) (STLKtensorg Cf n (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) * ϑ n (q.1 : ℝ) q.2.2‖)
        (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))

/-- `STB45` (`Step34Pins.lean:560`): `(y27kasdfg)` over a carrier; `ThetaN d L lam (EKsgn (mE E) σ)` is `Step2Gen_ThetaN Cf n σ`
(U-C4: no band `ThetaN`), `etaT (E n) u` is `Cf.eta n u`. -/
def STB45gL (s t : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (C c : ℝ), 1 ≤ m →
    ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) →
      PrecL sz μ (U := fun n => TimeIcc s t n) (fun n u ω => STXiLKg Cf n (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) →
      PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n)))
        (fun n q ω =>
          ‖(STQop (d := d) (ϑ n) (q.1 : ℝ)
              (Step2Gen_ThetaN Cf n q.2.1.1 (q.1 : ℝ) (STLKtensorg Cf n (q.1 : ℝ) ω q.2.1.1)) -
            Step2Gen_ThetaN Cf n q.2.1.1 (q.1 : ℝ)
              (STQop (d := d) (ϑ n) (q.1 : ℝ) (STLKtensorg Cf n (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
          ‖STPsum (d := d) (STLKtensorg Cf n (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) * deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
        (fun n q _ => (Cf.eta n (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))

end Target4

section Target4Bridge

variable {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ)

/-- `EKsgn (mE E) σ` of the band `ThetaN` is the charge vector `m(σ_i)` of `Step2Kern_ThetaN_band`; so the band `ThetaN` is
`Step2Gen_ThetaN (bandFM sz E)`. -/
theorem bandStep34_ThetaN (n k : ℕ) (σ : Fin k → Bool) (τ : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) σ) τ A = Step2Gen_ThetaN (bandFM sz E) n σ τ A :=
  (Step2Kern_ThetaN_band sz E n k σ τ A).symm

/-- Likewise the band `UN`. -/
theorem bandStep34_UN (n k : ℕ) (σ : Fin k → Bool) (s' t' : ℝ) (A : (Fin k → Zd d (sz.L n)) → ℂ) :
    UN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) σ) s' t' A = Step2Gen_UN (bandFM sz E) n σ s' t' A :=
  (Step2Kern_UN_band sz E n k σ s' t' A).symm

theorem bandFM_STSEforLnConcl :
    STSEforLnConcl sz E s t ↔ STSEforLnConclgL (bandStep2Mat sz E) (seqHflow sz) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STXiBoot : STXiBoot sz E s t ↔ STXiBootgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STNQConcl : STNQConcl sz E s t ↔ STNQConclgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STNQConcl' : STNQConcl' sz E s t ↔ STNQConclgL' (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STIterHyp (A : ℕ → ℝ) (r l : ℕ) :
    STIterHyp sz E s t A r l ↔ STIterHypgL (bandFM sz E) (Sizes.seqP sz) s t A r l := Iff.rfl
theorem bandFM_STWardTypeP : STWardTypeP sz E s t ↔ STWardTypePgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
/-- Not `Iff.rfl`: the band `ThetaN d L lam (EKsgn (mE E) σ)` is `Step2Gen_ThetaN (bandFM sz E)` by `Step2Kern_ThetaN_band`. -/
theorem bandFM_STB45 : STB45 sz E s t ↔ STB45gL (bandFM sz E) (Sizes.seqP sz) s t := by
  unfold STB45 STB45gL
  simp only [bandStep34_ThetaN]
  exact Iff.rfl

end Target4Bridge


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

/-- **`lem:iterations` over a carrier family** (`STIterR`, `Step34Pins.lean:478`); `Aof sz s` is the parameter `A` of `Ψ`. -/
def STIterRgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Aof : ∀ sz : Sizes d, (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ T0 sz z n) →
          R sz s t → STKboundgL (mk sz z) (law sz) → STLKgL (mk sz z) (law sz) s → sz.STConStInd 𝔠d s t →
          STStep1LoopgL (mk sz z) (law sz) s t → STStep2ConclgL (mk sz z) (law sz) s t Cd →
          STXiBootgL (mk sz z) (law sz) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL (mk sz z) (law sz) s t (Aof sz s) r (k - 1)) →
            STIterHypgL (mk sz z) (law sz) s t (Aof sz s) n_ k

/-- `STSEforLn` (`Step34Pins.lean:456`): the ℰ-term instance.  `mkM` is `Step2Mat`-valued and `mk = (mkM sz z).toFlowFM` by construction (no
equation hypothesis); `Hf sz z` is the flow matrix. -/
def STSEforLngL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
    (fun sz z s t => STSEforLnConclgL (mkM sz z) (Hf sz z) (law sz) s t)

/-- `STOeqNQ` (`Step34Pins.lean:459`). -/
def STOeqNQgL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d R law Flow mk T0 (fun sz z s t => STNQConclgL (mk sz z) (law sz) s t)

/-- `STWardTypePPin` (`Step34Pins.lean:577`). -/
def STWardTypePPingL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d R law Flow mk T0 (fun sz z s t => STWardTypePgL (mk sz z) (law sz) s t)

/-- `STB45Pin` (`Step34Pins.lean:580`). -/
def STB45PingL (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  STIngRgL d R law Flow mk T0 (fun sz z s t => STB45gL (mk sz z) (law sz) s t)

section Target5Bridge

/-- The band carrier family: law `seqP`, flow `STFlow`, carrier `bandFM sz (STflowE z)`, horizon `lemT (z n)`. -/
theorem bandFM_STStep3R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STStep3R d R ↔ STStep3RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  unfold STStep3R STStep3RgL
  simp only [bandFM_STKward]
  exact Iff.rfl

theorem bandFM_STStep4R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STStep4R d R ↔ STStep4RgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := by
  unfold STStep4R STStep4RgL
  simp only [bandFM_STKward]
  exact Iff.rfl

theorem bandFM_STIngR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STIngR d R Concl ↔ STIngRgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z s t => Concl sz (STflowE z) s t) := by
  unfold STIngR STIngRgL
  simp only [bandFM_STKward]
  exact Iff.rfl

theorem bandFM_STIterR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) :
    STIterR d R Aof ↔ STIterRgL d R (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz s n => Aof sz s n) := Iff.rfl

theorem bandFM_STSEforLn (d : ℕ) :
    STSEforLn d ↔ STSEforLngL d STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STAny (fun sz E s t => STSEforLnConcl sz E s t)

theorem bandFM_STOeqNQ (d : ℕ) :
    STOeqNQ d ↔ STOeqNQgL d STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STCaseI (fun sz E s t => STNQConcl sz E s t)

theorem bandFM_STWardTypePPin (d : ℕ) :
    STWardTypePPin d ↔ STWardTypePPingL d STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  bandFM_STIngR d STCaseI (fun sz E s t => STWardTypeP sz E s t)

private theorem step34Gen_ingR_congr {d : ℕ} {R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} {T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ}
    {Concl Concl' : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (h : ∀ sz z s t, Concl sz z s t ↔ Concl' sz z s t) :
    STIngRgL d R law Flow mk T0 Concl ↔ STIngRgL d R law Flow mk T0 Concl' := by
  unfold STIngRgL
  simp only [h]

/-- Not `Iff.rfl`: the conclusion `STB45` is `STB45gL` through `bandFM_STB45` (`Step2Kern_ThetaN_band`). -/
theorem bandFM_STB45Pin (d : ℕ) :
    STB45Pin d ↔ STB45PingL d STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  (bandFM_STIngR d STCaseI (fun sz E s t => STB45 sz E s t)).trans
    (step34Gen_ingR_congr (fun sz z s t => bandFM_STB45 sz (STflowE z) s t))

end Target5Bridge

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

/-- **`(sum_res_1)`** (`Step34Pins.lean:625`) over `Step2Gen_UN C`, cutoff `ellT (gK n)`, ratio at `gK n`. -/
def STEKSumRes1gL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Ker : STEKKer d) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ (C : FlowFM sz) (gK : ℕ → ℝ), Ker sz C gK κ → (∀ᶠ n in atTop, 0 < gK n ∧ gK n ≤ 𝔡⁻¹) →
    ∀ s t : ℕ → ℝ, STEKWinKgL sz gK s t → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecayKgL gK (law sz) s t 𝒜 →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLowgL (law sz) s t X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      PrecL sz (law sz) (U := fun n => TimeIcc s t n) (fun n v ω => ‖Step2Gen_UN C n σ (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => (ellT (sz.L n) (gK n) (t n) ^ 2 / ellT (sz.L n) (gK n) (v : ℝ) ^ 2) *
          ((gK n ^ 2 + |1 - (v : ℝ)|) / (gK n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)

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

/-- The band class (D3 (a)): `C = bandFM sz E`, coupling `gK = sz.lam`, `|E n| ≤ 2` and the bulk `κ ≤ Im m(E n)`. -/
def STEKBandKer {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ) (κ : ℝ) : Prop :=
  ∃ E : ℕ → ℝ, C = bandFM sz E ∧ gK = sz.lam ∧ ∀ n, |E n| ≤ 2 ∧ κ ≤ (mE (E n)).im

end Target6

section Target6Bridge

variable {d : ℕ}

theorem bandFM_STEKWin (sz : Sizes d) (s t : ℕ → ℝ) : STEKWin sz s t ↔ STEKWinKgL sz sz.lam s t := Iff.rfl

theorem bandFM_STEKDecay (sz : Sizes d) (m : ℕ) (s t : ℕ → ℝ) (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) :
    STEKDecay sz s t 𝒜 ↔ STEKDecaygL (Sizes.seqP sz) s t 𝒜 := Iff.rfl

theorem bandFM_STEKLow (sz : Sizes d) (s t : ℕ → ℝ) (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) :
    STEKLow sz s t X ↔ STEKLowgL (Sizes.seqP sz) s t X := Iff.rfl

/-- `0 < sz.lam n ≤ 𝔡⁻¹` eventually, from `Admissible` (the hypothesis `hg` of the five forms at the band class). -/
theorem step34Gen_band_hg {sz : Sizes d} {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [h.2.2.2.2] with n hn
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1, hn.2⟩

/-- `W_n → ∞` from `Admissible` (`Bandwidth` and `SizeTendsto`). -/
theorem step34Gen_W_tendsto {sz : Sizes d} {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) :
    Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop := by
  obtain ⟨h𝔠, -, hsize, hbw, -⟩ := h
  exact tendsto_atTop_mono' _ hbw ((tendsto_rpow_atTop h𝔠).comp hsize)

/-- The five band instances (premise-free, from the merged `stek_*_holds`, `Evolution/Prec.lean:215-422`): the pin at the band class.  One direction
only: the generic forms carry the class and the bulk parameter. -/
theorem stek_sumNdecaygL_band (d : ℕ) : STEKSumNdecaygL d (fun sz => Sizes.seqP sz) (@STEKBandKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hg, hE⟩ _ s t hs hst ht σ 𝒜 X hX hdom
  subst hC; subst hg
  simp only [Step2Kern_UN_band sz E]
  exact stek_sumNdecay_holds d hd n_ hn 𝔠 𝔡 sz hAdm s t hs hst ht (fun n => mE (E n)) (fun n => norm_mE (hE n).1) σ 𝒜 X hX hdom

theorem stek_sumRes1gL_band (d : ℕ) : STEKSumRes1gL d (fun sz => Sizes.seqP sz) (@STEKBandKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hg, hE⟩ _ s t hwin σ 𝒜 hdec X hlow hdom
  subst hC; subst hg
  simp only [Step2Kern_UN_band sz E]
  exact stek_sumRes1_holds d hd n_ hn 𝔠 𝔡 sz hAdm s t hwin (fun n => mE (E n)) (fun n => norm_mE (hE n).1) σ 𝒜 hdec X hlow hdom

theorem stek_sumRes2NALgL_band (d : ℕ) : STEKSumRes2NALgL d (fun sz => Sizes.seqP sz) (@STEKBandKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hg, hE⟩ _ s t hwin σ hσ 𝒜 hdec X hlow hdom
  subst hC; subst hg
  simp only [Step2Kern_UN_band sz E]
  exact stek_sumRes2NAL_holds d hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t hwin (fun n => mE (E n)) (fun n => norm_mE (hE n).1)
    (fun n => (hE n).2) σ hσ 𝒜 hdec X hlow hdom

theorem stek_sumRes2gL_band (d : ℕ) : STEKSumRes2gL d (fun sz => Sizes.seqP sz) (@STEKBandKer d) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ sz hAdm C gK ⟨E, hC, hg, hE⟩ _ s t hwin σ 𝒜 hdec hz X hlow hdom
  subst hC; subst hg
  simp only [Step2Kern_UN_band sz E]
  exact stek_sumRes2_holds d hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t hwin (fun n => mE (E n)) (fun n => norm_mE (hE n).1)
    (fun n => (hE n).2) σ 𝒜 hdec hz X hlow hdom

/-- The A-form with `Aof = 1`: the threshold `(1 - s) L² ≤ lam²` is the band `1 - lam²/L² ≤ s`. -/
theorem stek_nonzerogL_band (d : ℕ) : STEKNonzerogL d (fun sz => Sizes.seqP sz) (@STEKBandKer d) (fun _ => 1) := by
  intro hd n_ hn κ 𝔠 𝔡 hκ _ sz hAdm C gK ⟨E, hC, hg, hE⟩ _ s t hthr hs hst ht σ A hA 𝒜 X hX hdom
  subst hC; subst hg
  simp only [Step2Kern_UN_band sz E]
  refine stek_nonzero_holds d hd n_ hn κ 𝔠 𝔡 hκ sz hAdm s t (fun n => ?_) hs hst ht (fun n => mE (E n))
    (fun n => norm_mE (hE n).1) (fun n => (hE n).2) σ A hA 𝒜 X hX hdom
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
    positivity
  have h1 : 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
    rw [le_div_iff₀ hL]; simpa using hthr n
  linarith

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

/-- (d) `ellT` goes down with the coupling: `ellT L g u ≤ ellT L l u` from `0 ≤ g l` and `g² ≤ l²`; for `l ≤ 0` both are `min 1 L`. -/
private theorem step34Gen_ellT_le_pt {L : ℕ} {g l A : ℝ} (u : ℝ) (h1 : 0 ≤ g * l) (h2 : g ^ 2 ≤ l ^ 2) (h3 : l ^ 2 ≤ A * g ^ 2) :
    ellT L g u ≤ ellT L l u := by
  obtain ⟨hpos, hneg⟩ := step34Gen_cmp_idx h1 h2 h3
  unfold ellT
  have hs : 0 ≤ Real.sqrt |1 - u| := Real.sqrt_nonneg _
  rcases le_or_gt l 0 with hl | hl
  · have hg := hneg hl
    have hq1 : g / Real.sqrt |1 - u| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hg hs
    have hq2 : l / Real.sqrt |1 - u| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hl hs
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
  · rcases lt_or_ge 0 g with hg | hg
    · exact min_le_min_right _ (max_le_max_right _ (div_le_div_of_nonneg_right (hpos hg).2 hs))
    · have hq1 : g / Real.sqrt |1 - u| ≤ 0 := div_nonpos_of_nonpos_of_nonneg hg hs
      refine min_le_min_right _ (max_le_max_right _ ?_)
      exact hq1.trans (div_nonneg hl.le hs)

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

/-- (d) `ellT (gK n) ≤ ellT (sz.lam n)`. -/
theorem step34Gen_ellT_le {sz : Sizes d} {gK : ℕ → ℝ} {A : ℝ}
    (hcmp : ∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) (n : ℕ) (u : ℝ) :
    ellT (sz.L n) (gK n) u ≤ ellT (sz.L n) (sz.lam n) u :=
  step34Gen_ellT_le_pt u (hcmp n).1 (hcmp n).2.1 (hcmp n).2.2

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

/-- **`lem: newPQ`** (`Step34Pins.lean:330`) over a class `Cls` of carriers, with `η = C.eta n τ` (H251 (2): the class pin; the Ward-family text is
U1s1's, `Chain/ZeroModeGen`).  The band class is `∃ E, C = bandFM sz E ∧ ∀ n, |E n| < 2`. -/
def STNewPQgL (d : ℕ) (Cls : ∀ sz : Sizes d, FlowFM sz → Prop) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (C : FlowFM sz), Cls sz C → ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ) (a : Fin m → Zd d (sz.L n)),
        (zeroModeSet d (sz.L n) A (fun a' => C.L n τ σ a' ω) a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => C.L n τ σ a' ω) a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => C.L n τ (σ' α) a' ω) (a ∘ ι α)) ∧
        (zeroModeSet d (sz.L n) A (fun a' => C.K n τ σ a') a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => C.K n τ σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => C.K n τ (σ' α) a') (a ∘ ι α))

/-- The band instance (premise-free, from `stNewPQ_holds`, `Induction/NewPQ.lean:584`): `η = C.eta n τ` is `etaT (E n) τ` at `C = bandFM sz E`. -/
theorem stNewPQgL_band (d : ℕ) : STNewPQgL d (fun sz C => ∃ E : ℕ → ℝ, C = bandFM sz E ∧ ∀ n, |E n| < 2) := by
  intro m σ A
  obtain ⟨ℓ, k, ξ, σ', ι, A', h1, h2, h3⟩ := stNewPQ_holds d m σ A
  refine ⟨ℓ, k, ξ, σ', ι, A', h1, h2, ?_⟩
  rintro sz C ⟨E, rfl, hE⟩ n τ h0 h1' ω a
  exact h3 sz n (E n) τ (hE n) h0 h1' ω a

/-! ## 8. Target 9: compiled nonempty instances at `d = 3`

Data of `Induction/Step34Pins.lean` §7 and `Evolution/Prec.lean` §4: `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)`),
`z0`, `s ≡ 0`, `t ≡ 1/16`, `κ = 1/10`, `n_ = 2`; `szB` (`L = 4`, `W = n + 4`, `lam = 1`) for case (ii).  Hypotheses that are other gates' unproved pins
(`STLmaxUgL`, `STStep3RgL`, ..., owed by U3s4 / U3-BA) stay hypotheses of the `example`s; every deterministic hypothesis is discharged. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

private theorem step34Gen_lam0_nonneg (n : ℕ) : 0 ≤ sz0.lam n := by
  change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem step34Gen_mE_zero_im : (1 / 10 : ℝ) ≤ (mE 0).im := by
  rw [mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-! ### Targets 1 and 5: the endpoints and the Step 3-4 pins at the band reading -/

example (h : STLmaxUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STLmaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  STLmaxgL_of_STLmaxUgL _ _ (fun n => (sz0_hst n).le) h

example (h : STLKUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) :
    STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst :=
  STLKgL_of_STLKUgL _ _ (fun n => (sz0_hst n).le) h

/-- `STLmax_of_STLmaxU` (`Step34Pins.lean:284`) at `(sz0, z0, 0, 1/16)`, re-derived through the bridge `bandFM_STLmaxU`. -/
example (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst :=
  (Iff.rfl : STLmax sz0 (STflowE z0) tInst ↔ STLmaxgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst).2
    (STLmaxgL_of_STLmaxUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun n => (sz0_hst n).le)
      ((bandFM_STLmaxU sz0 (STflowE z0) sInst tInst).1 h))

/-- `STLK_of_STLKU` (`Step34Pins.lean:291`) at `(sz0, z0, 0, 1/16)`, re-derived through `bandFM_STLKU`. -/
example (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst :=
  (Iff.rfl : STLK sz0 (STflowE z0) tInst ↔ STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) tInst).2
    (STLKgL_of_STLKUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun n => (sz0_hst n).le)
      ((bandFM_STLKU sz0 (STflowE z0) sInst tInst).1 h))

/-- `inst_step3R` (`Step34Pins.lean:917`) re-derived through `bandFM_STStep3R`: the generic pin at the band reading, regime `STCaseI`, gives the
instance at `(sz0, z0, 0, 1/16)`. -/
example (h : STStep3RgL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz0 z0 sInst tInst Cd :=
  inst_step3R STCaseI ((bandFM_STStep3R 3 STCaseI).2 h) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con Cd hCd

/-- `inst_step4R` (`Step34Pins.lean:928`) re-derived through `bandFM_STStep4R`. -/
example (h : STStep4RgL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl sz0 z0 sInst tInst Cd :=
  inst_step4R STCaseI ((bandFM_STStep4R 3 STCaseI).2 h) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con Cd hCd

/-- The generic Step 3 pin applied directly (not through the band pin) at the concrete data: the constant `𝔠d` of the pin, then the stochastic premises
(other gates' pins), then `STLmaxUgL`. -/
example (h : STStep3RgL 3 STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKboundgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) → STKwardgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) →
        STLKgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst →
        STStep1LoopgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd →
        STLmaxUgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hKw ha h1' h2 =>
    H (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial hK hKw ha (sz0_con 𝔠d h0) h1' h2⟩

/-- `inst_SEforLn` (`Step34Pins.lean:988`) re-derived through `bandFM_STSEforLn` (`STSEforLngL` at the band carrier `bandStep2Mat`, flow matrix `seqHflow`). -/
example (h : STSEforLngL 3 STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STSEforLnConcl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_SEforLn ((bandFM_STSEforLn 3).2 h) Cd hCd

/-- `inst_OeqNQ` (`Step34Pins.lean:994`) through `bandFM_STOeqNQ`. -/
example (h : STOeqNQgL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STNQConcl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_OeqNQ ((bandFM_STOeqNQ 3).2 h) Cd hCd

/-- `inst_B45` (`Step34Pins.lean:1019`) through `bandFM_STB45Pin` (the proved, non-`Iff.rfl` bridge). -/
example (h : STB45PingL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STB45 sz E s t) sz0 z0 sInst tInst Cd :=
  inst_B45 ((bandFM_STB45Pin 3).2 h) Cd hCd

/-- `inst_WardTypeP` through `bandFM_STWardTypePPin`. -/
example (h : STWardTypePPingL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STWardTypeP sz E s t) sz0 z0 sInst tInst Cd :=
  inst_WardTypeP ((bandFM_STWardTypePPin 3).2 h) Cd hCd

/-- `inst_iterations` (`Step34Pins.lean:1025`) through `bandFM_STIterR` (`STIterRgL`, case (i) at `(szB, zB, 7/8, 15/16)`). -/
example (h : STIterRgL 3 STRegIterI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ n => STAI sz n)) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIterConcl (fun sz _ n => STAI sz n) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iterations ((bandFM_STIterR 3 STRegIterI (fun sz _ n => STAI sz n)).2 h) Cd hCd

/-! ### Targets 2-4: the loops and the ℰ-terms at a sample, `sz0`, `n = 0` -/

example (ω : sz0.SeqΩ) : STLI sz0 0 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ =
    STLIg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ :=
  bandStep34_STLI sz0 (fun _ => 0) 0 (1 / 2) ω _

example (ω : sz0.SeqΩ) : STegt sz0 0 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ =
    STegtg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ :=
  bandStep34_STegt sz0 (fun _ => 0) 0 (1 / 2) ω _

example (ω : sz0.SeqΩ) : STee sz0 0 0 (1 / 2) ω ![true, false] ![0, 0] ![0, 0] =
    STeeg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω ![true, false] ![0, 0] ![0, 0] :=
  bandStep34_STee sz0 (fun _ => 0) 0 (1 / 2) ω _ _ _

example (ω : sz0.SeqΩ) : STmaxL sz0 0 0 (1 / 2) 2 ω = STmaxLg (bandFM sz0 (fun _ => 0)) 0 (1 / 2) 2 ω :=
  bandStep34_STmaxL sz0 (fun _ => 0) 0 (1 / 2) 2 ω

example (ω : sz0.SeqΩ) : STmaxLK sz0 0 0 (1 / 2) 2 ω = STmaxLKg (bandFM sz0 (fun _ => 0)) 0 (1 / 2) 2 ω :=
  bandStep34_STmaxLK sz0 (fun _ => 0) 0 (1 / 2) 2 ω

example (ω : sz0.SeqΩ) : STXiL sz0 0 0 (1 / 2) 2 ω = STXiLg (bandFM sz0 (fun _ => 0)) 0 (1 / 2) 2 ω :=
  bandStep34_STXiL sz0 (fun _ => 0) 0 (1 / 2) 2 ω

example (ω : sz0.SeqΩ) : STXiLK sz0 0 0 (1 / 2) 2 ω = STXiLKg (bandFM sz0 (fun _ => 0)) 0 (1 / 2) 2 ω :=
  bandStep34_STXiLK sz0 (fun _ => 0) 0 (1 / 2) 2 ω

example (ω : sz0.SeqΩ) : STsupXiLK sz0 0 0 0 (1 / 2) 2 ω = STsupXiLKg (bandFM sz0 (fun _ => 0)) 0 0 (1 / 2) 2 ω :=
  bandStep34_STsupXiLK sz0 (fun _ => 0) 0 2 ω 0 (1 / 2)

example (ω : sz0.SeqΩ) : STLKtensor sz0 0 0 (1 / 2) ω (m := 2) ![true, false, true] =
    STLKtensorg (bandFM sz0 (fun _ => 0)) 0 (1 / 2) ω (m := 2) ![true, false, true] :=
  bandStep34_STLKtensor sz0 (fun _ => 0) 0 (1 / 2) ω ![true, false, true]

example : STKI sz0 0 0 (1 / 2) ⟨[true, false], [0, 0]⟩ = STKIg (bandStep2Mat sz0 (fun _ => 0)) 0 (1 / 2) ⟨[true, false], [0, 0]⟩ :=
  bandStep34_STKI sz0 (fun _ => 0) 0 (1 / 2) _

example (ω : sz0.SeqΩ) : STLKI sz0 0 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ =
    STLKIg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω ⟨[true, false], [0, 0]⟩ :=
  bandStep34_STLKI sz0 (fun _ => 0) 0 (1 / 2) ω _

example (ω : sz0.SeqΩ) : STksimLK sz0 0 0 (1 / 2) ω 3 ⟨[true, false, true], [0, 0, 0]⟩ =
    STksimLKg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω 3 ⟨[true, false, true], [0, 0, 0]⟩ :=
  bandStep34_STksimLK sz0 (fun _ => 0) 0 (1 / 2) ω 3 _

example (ω : sz0.SeqΩ) : STelklk sz0 0 0 (1 / 2) ω ⟨[true, false, true], [0, 0, 0]⟩ =
    STelklkg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω ⟨[true, false, true], [0, 0, 0]⟩ :=
  bandStep34_STelklk sz0 (fun _ => 0) 0 (1 / 2) ω _

example (ω : sz0.SeqΩ) : STavgErr sz0 0 0 (1 / 2) ω true 0 = STavgErrg (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) 0 (1 / 2) ω true 0 :=
  bandStep34_STavgErr sz0 (fun _ => 0) 0 (1 / 2) ω true 0

example : STIngR 3 STAny (fun sz E s t => STSEforLnConcl sz E s t) ↔
    STIngRgL 3 STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
      (fun _ z n => lemT (z n)) (fun sz z s t => STSEforLnConcl sz (STflowE z) s t) :=
  bandFM_STIngR 3 STAny (fun sz E s t => STSEforLnConcl sz E s t)

example : Step34Gen_LCompat (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) := bandStep34_LCompat sz0 _
example : Step34Gen_KCompat (bandStep2Mat sz0 (fun _ => 0)) := bandStep34_KCompat sz0 _

example : STSEforLnConcl sz0 (fun _ => 0) sInst tInst ↔
    STSEforLnConclgL (bandStep2Mat sz0 (fun _ => 0)) (seqHflow sz0) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STSEforLnConcl sz0 _ sInst tInst

example : STXiBoot sz0 (fun _ => 0) sInst tInst ↔ STXiBootgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STXiBoot sz0 _ sInst tInst

example : STNQConcl sz0 (fun _ => 0) sInst tInst ↔ STNQConclgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STNQConcl sz0 _ sInst tInst

example : STNQConcl' sz0 (fun _ => 0) sInst tInst ↔ STNQConclgL' (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STNQConcl' sz0 _ sInst tInst

example : STIterHyp sz0 (fun _ => 0) sInst tInst (fun n => ((sz0.W n : ℕ) : ℝ)) 2 1 ↔
    STIterHypgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst (fun n => ((sz0.W n : ℕ) : ℝ)) 2 1 :=
  bandFM_STIterHyp sz0 _ sInst tInst _ 2 1

example : STWardTypeP sz0 (fun _ => 0) sInst tInst ↔ STWardTypePgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STWardTypeP sz0 _ sInst tInst

/-- `STB45` is `STB45gL` through `Step2Kern_ThetaN_band` (U-C4: no band `ThetaN` in the generic form). -/
example : STB45 sz0 (fun _ => 0) sInst tInst ↔ STB45gL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STB45 sz0 _ sInst tInst

example : ThetaN 3 (sz0.L 0) (sz0.lam 0) (EKsgn (mE ((fun _ => (0 : ℝ)) 0)) ![true, false]) (1 / 2) (fun _ => 1) =
    Step2Gen_ThetaN (bandFM sz0 (fun _ => 0)) 0 ![true, false] (1 / 2) (fun _ => 1) :=
  bandStep34_ThetaN sz0 (fun _ => 0) 0 2 ![true, false] (1 / 2) (fun _ => 1)

example : UN 3 (sz0.L 0) (sz0.lam 0) (EKsgn (mE ((fun _ => (0 : ℝ)) 0)) ![true, false]) 0 (1 / 16) (fun _ => 1) =
    Step2Gen_UN (bandFM sz0 (fun _ => 0)) 0 ![true, false] 0 (1 / 16) (fun _ => 1) :=
  bandStep34_UN sz0 (fun _ => 0) 0 2 ![true, false] 0 (1 / 16) (fun _ => 1)

/-! ### Target 6: the `STEK` vocabulary at `sz0`

The tensor family is `δ₀` (point mass at `0`, as in `Evolution/Prec.lean` §4), and `Az = δ₀ ⊗ (δ₀ - δ_e)` for the sum-zero form; the control is `X ≡ 1`. -/

private theorem step34Gen_norm_delta0_le (n d L : ℕ) [NeZero L] : ‖ekDelta0 n d L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  unfold ekDelta0
  split_ifs <;> simp

private theorem step34Gen_prec_delta0 (sz : Sizes 3) (s t : ℕ → ℝ) :
    PrecL sz (Sizes.seqP sz) (U := fun n => TimeIcc s t n) (fun n _ _ => ‖ekDelta0 2 3 (sz.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  prec_of_le sz (fun _ _ _ => zero_le_one) (fun n _ _ => step34Gen_norm_delta0_le 2 3 (sz.L n))

private theorem step34Gen_decay_delta0 (sz : Sizes 3) (s t : ℕ → ℝ) :
    STEKDecayKgL sz.lam (Sizes.seqP sz) s t (fun n _ _ => ekDelta0 2 3 (sz.L n)) := by
  intro ε D hε hD
  refine Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v => ?_)
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n
      exact_mod_cast (by omega : 1 ≤ sz.L n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have := mul_pos (Real.rpow_pos_of_pos hW ε) (ellT_pos (g := sz.lam n) (t := (v : ℝ)) hL1)
    simp at hij
    linarith
  · simp only [ekDelta0, ha, ↓reduceIte, norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem step34Gen_low_one (sz : Sizes 3) (s t : ℕ → ℝ) : STEKLowgL (Sizes.seqP sz) s t (fun _ _ _ => (1 : ℝ)) :=
  ⟨0, Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun n ω v => by simp)⟩

private theorem step34Gen_win_sz0 : STEKWinKgL sz0 sz0.lam sInst tInst := by
  refine ⟨fun n => le_rfl, fun n => by simp only [sInst, tInst]; norm_num, fun n => ?_,
    fun n => by simp only [tInst]; norm_num, Eventually.of_forall fun n => ?_⟩
  · have := sz0_caseI n
    simp only [tInst] at this ⊢
    linarith
  · simp only [sInst, tInst]
    calc (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ 32⁻¹ := inv_anti₀ (by norm_num) (W_ge_32 n)
      _ ≤ (1 - 1 / 16) / (1 - 0) := by norm_num

/-- the sum-zero tensor `δ₀ ⊗ (δ₀ - δ_e)`, `e = (1,0,0)`. -/
private noncomputable def step34Gen_Az (L : ℕ) : (Fin 2 → Zd 3 L) → ℂ := fun b =>
  if b 0 = 0 then (if b 1 = 0 then 1 else 0) - (if b 1 = (Pi.single 0 1 : Zd 3 L) then 1 else 0) else 0

private theorem step34Gen_norm_Az_le (L : ℕ) [NeZero L] : ‖step34Gen_Az L‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun a => ?_
  unfold step34Gen_Az
  split_ifs <;> simp

private theorem step34Gen_Az_sumZero (L : ℕ) [NeZero L] : EKSumZero (step34Gen_Az L) := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  rw [Finset.sum_filter, ek_sum_fin_two]
  have e : ∀ x' y : Zd 3 L, (if (![x', y] : Fin 2 → Zd 3 L) 0 = x then step34Gen_Az L ![x', y] else 0)
      = if x' = x then (if x' = 0 then (if y = 0 then (1 : ℂ) else 0) -
          (if y = (Pi.single 0 1 : Zd 3 L) then 1 else 0) else 0) else 0 := by
    intro x' y
    simp [step34Gen_Az]
  simp only [e]
  by_cases hx : x = 0
  · subst hx
    simp [Finset.sum_ite_eq', Finset.sum_sub_distrib]
  · simp

private theorem step34Gen_Az_decay (L : ℕ) [NeZero L] (hL : 3 ≤ L) (g s W ε D : ℝ) (hW : 0 < W)
    (h : 1 < W ^ ε * ellT L g s) : EKFastDecay g s W ε D (step34Gen_Az L) := by
  intro a ⟨i, j, hij⟩
  by_cases hne : step34Gen_Az L a = 0
  · rw [hne]; simp only [norm_zero]; exact Real.rpow_nonneg hW.le _
  · exfalso
    have h0 : a 0 = 0 := by
      by_contra hc; simp [step34Gen_Az, hc] at hne
    have h1 : a 1 = 0 ∨ a 1 = (Pi.single 0 1 : Zd 3 L) := by
      by_contra hc
      rw [not_or] at hc
      simp [step34Gen_Az, h0, hc.1, hc.2] at hne
    have hE : ∀ y : Zd 3 L, y = 0 ∨ y = (Pi.single 0 1 : Zd 3 L) → zdistD 3 L y ≤ 1 := by
      rintro y (rfl | rfl)
      · simp
      · rw [zdistD_single, zdist_one hL]
    have hd : ∀ i j : Fin 2, zdistD 3 L (a i - a j) ≤ 1 := by
      refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · simp
      · rw [h0, zero_sub, zdistD_neg]; exact hE _ h1
      · rw [h0, sub_zero]; exact hE _ h1
      · simp
    have h2 : (zdistD 3 L (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast hd i j
    linarith

private theorem step34Gen_decay_Az (sz : Sizes 3) {𝔠 𝔡 : ℝ} (h : sz.Admissible 𝔠 𝔡) (s t : ℕ → ℝ) :
    STEKDecayKgL sz.lam (Sizes.seqP sz) s t (fun n _ _ => step34Gen_Az (sz.L n)) := by
  intro ε D hε hD
  refine Gauss.HighProbAt.of_eventually_univ ?_
  have h4s : ∀ᶠ n in atTop, (4 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp (step34Gen_W_tendsto h)).eventually (eventually_ge_atTop (4 : ℝ))
  filter_upwards [h4s] with n h4 ω v
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  refine step34Gen_Az_decay (sz.L n) (sz.three_le_L n) _ _ _ _ _ hW ?_
  have h1 := one_le_ellT (g := sz.lam n) (t := (v : ℝ)) hL1
  nlinarith

private theorem step34Gen_prec_Az (sz : Sizes 3) (s t : ℕ → ℝ) :
    PrecL sz (Sizes.seqP sz) (U := fun n => TimeIcc s t n) (fun n _ _ => ‖step34Gen_Az (sz.L n)‖) (fun _ _ _ => (1 : ℝ)) :=
  prec_of_le sz (fun _ _ _ => zero_le_one) (fun n _ _ => step34Gen_norm_Az_le (sz.L n))

/-- `STEKDecaygL` and `STEKLowgL` at `(seqP sz0, 0, 1/16)` (unconditional; the control `X ≡ 1`, the tensor `δ₀`). -/
example : STEKDecaygL (Sizes.seqP sz0) sInst tInst (fun n _ _ => ekDelta0 2 3 (sz0.L n)) := step34Gen_decay_delta0 sz0 sInst tInst
example : STEKLowgL (Sizes.seqP sz0) sInst tInst (fun _ _ _ => (1 : ℝ)) := step34Gen_low_one sz0 sInst tInst

/-- The bridges at `sz0`: the band pins `STEKWin`, `STEKDecay`, `STEKLow` hold at the data, through `Iff.rfl` bridges from the generic ones. -/
example : STEKWin sz0 sInst tInst := (bandFM_STEKWin sz0 sInst tInst).2 step34Gen_win_sz0
example : STEKDecay sz0 sInst tInst (fun n _ _ => ekDelta0 2 3 (sz0.L n)) :=
  (bandFM_STEKDecay sz0 2 sInst tInst _).2 (step34Gen_decay_delta0 sz0 sInst tInst)
example : STEKLow sz0 sInst tInst (fun _ _ _ => (1 : ℝ)) := (bandFM_STEKLow sz0 sInst tInst _).2 (step34Gen_low_one sz0 sInst tInst)

/-- The band class is inhabited at `bandFM sz0 (fun _ => 0)` (`E ≡ 0`: `mE 0 = i`, `Im = 1 ≥ κ = 1/10`, `|0| ≤ 2`, coupling `sz0.lam`). -/
example : STEKBandKer sz0 (bandFM sz0 (fun _ => 0)) sz0.lam (1 / 10) :=
  ⟨fun _ => 0, rfl, rfl, fun n => ⟨by simp, step34Gen_mE_zero_im⟩⟩
example : ∃ E : ℕ → ℝ, bandFM sz0 (fun _ => 0) = bandFM sz0 E ∧ ∀ n, |E n| < 2 := ⟨fun _ => 0, rfl, fun n => by simp⟩

private theorem step34Gen_ker0 : STEKBandKer sz0 (bandFM sz0 (fun _ => 0)) sz0.lam (1 / 10) :=
  ⟨fun _ => 0, rfl, rfl, fun n => ⟨by simp, step34Gen_mE_zero_im⟩⟩

/-- The five band instances at `d = 3`, `sz0`, `n_ = 2`, `κ = 1/10`, applied at the concrete tensor families (every deterministic hypothesis is discharged). -/
example := stek_sumNdecaygL_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (bandFM sz0 (fun _ => 0)) sz0.lam step34Gen_ker0 (step34Gen_band_hg sz0_admissible) sInst tInst (fun _ => le_rfl)
  (fun n => by simp only [sInst, tInst]; norm_num) (fun n => by simp only [tInst]; norm_num) ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (fun _ _ _ => (1 : ℝ)) (fun _ _ _ => zero_le_one) (step34Gen_prec_delta0 sz0 sInst tInst)

example := stek_sumRes1gL_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (bandFM sz0 (fun _ => 0)) sz0.lam step34Gen_ker0 (step34Gen_band_hg sz0_admissible) sInst tInst step34Gen_win_sz0 ![true, false]
  (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (step34Gen_decay_delta0 sz0 sInst tInst) (fun _ _ _ => (1 : ℝ)) (step34Gen_low_one sz0 sInst tInst)
  (step34Gen_prec_delta0 sz0 sInst tInst)

example := stek_sumRes2NALgL_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (bandFM sz0 (fun _ => 0)) sz0.lam step34Gen_ker0 (step34Gen_band_hg sz0_admissible) sInst tInst step34Gen_win_sz0
  ![true, true] ⟨0, by decide⟩ (fun n _ _ => ekDelta0 2 3 (sz0.L n)) (step34Gen_decay_delta0 sz0 sInst tInst) (fun _ _ _ => (1 : ℝ))
  (step34Gen_low_one sz0 sInst tInst) (step34Gen_prec_delta0 sz0 sInst tInst)

example := stek_sumRes2gL_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 6) (1 / 10) (by norm_num) sz0 sz0_admissible
  (bandFM sz0 (fun _ => 0)) sz0.lam step34Gen_ker0 (step34Gen_band_hg sz0_admissible) sInst tInst step34Gen_win_sz0 ![true, false]
  (fun n _ _ => step34Gen_Az (sz0.L n)) (step34Gen_decay_Az sz0 sz0_admissible sInst tInst) (fun n _ _ => step34Gen_Az_sumZero (sz0.L n))
  (fun _ _ _ => (1 : ℝ)) (step34Gen_low_one sz0 sInst tInst) (step34Gen_prec_Az sz0 sInst tInst)

/-- `lem:sum_decay_nonzero`, case (ii) at `(szB, 15/16, 31/32)` (`1 - s = lam²/L² = 1/16`), the A-form with `Aof = 1`. -/
example := stek_nonzerogL_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 6) (1 / 10) (by norm_num) le_rfl szB szB_admissible
  (bandFM szB (fun _ => 0)) szB.lam ⟨fun _ => 0, rfl, rfl, fun n => ⟨by simp, step34Gen_mE_zero_im⟩⟩ (step34Gen_band_hg szB_admissible)
  (fun _ => 15 / 16) (fun _ => 31 / 32) (fun n => by norm_num [szB]) (fun n => by norm_num) (fun n => by norm_num) (fun n => by norm_num)
  ![true, false] Finset.univ (fun i _ => Finset.mem_univ i) (fun n _ _ => ekDelta0 2 3 (szB.L n)) (fun _ _ _ => (1 : ℝ))
  (fun _ _ _ => zero_le_one) (step34Gen_prec_delta0 szB _ _)

/-! ### Target 7: `STNewPQgL` at the band class -/

example : STNewPQgL 3 (fun sz C => ∃ E : ℕ → ℝ, C = bandFM sz E ∧ ∀ n, |E n| < 2) := stNewPQgL_band 3

/-- `lem: newPQ` at `m = 3`, `σ = (+,-,+)`, `A = ∅`, applied at the class element `bandFM sz0 (fun _ => 0)`, `n = 0`, `τ = 1/2` (the identity for `𝓛`). -/
example (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin 3)
      (A' : ∀ α, Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧
      zeroModeSet 3 (sz0.L 0) ∅ (fun a' => (bandFM sz0 (fun _ => 0)).L 0 (1 / 2) ![true, false, true] a' ω) a =
        zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff ![true, false, true]) (fun a' => (bandFM sz0 (fun _ => 0)).L 0 (1 / 2) ![true, false, true] a' ω) a +
          ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) * ((bandFM sz0 (fun _ => 0)).eta 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
            zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => (bandFM sz0 (fun _ => 0)).L 0 (1 / 2) (σ' α) a' ω) (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', h1, -, h3⟩ := stNewPQgL_band 3 3 ![true, false, true] ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', h1, (h3 sz0 (bandFM sz0 (fun _ => 0)) ⟨fun _ => 0, rfl, fun n => by simp⟩ 0 (1 / 2) (by norm_num)
    (by norm_num) ω a).1⟩

/-! ### UBA-C1 (R1), (a), (c), (d), (e): band `gK = sz.lam`, `A = 1`; non-band `gK = sz.lam / 2`, `A = 4`; negative `lam` -/

private theorem step34Gen_cmp_band : ∀ n, 0 ≤ sz0.lam n * sz0.lam n ∧ sz0.lam n ^ 2 ≤ sz0.lam n ^ 2 ∧ sz0.lam n ^ 2 ≤ 1 * sz0.lam n ^ 2 :=
  fun n => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩

private theorem step34Gen_cmp_half : ∀ n, 0 ≤ (fun n => sz0.lam n / 2) n * sz0.lam n ∧ (fun n => sz0.lam n / 2) n ^ 2 ≤ sz0.lam n ^ 2 ∧
    sz0.lam n ^ 2 ≤ 4 * (fun n => sz0.lam n / 2) n ^ 2 := fun n => by
  have := step34Gen_lam0_nonneg n
  refine ⟨by dsimp only; positivity, by dsimp only; nlinarith, by dsimp only; nlinarith⟩

/-- the same for the sizes with the negative coupling `-sz0.lam`: `gK = -sz0.lam / 2`, `A = 4` (the sign branch of (d)). -/
private theorem step34Gen_cmp_neg : ∀ n, 0 ≤ (fun n => -sz0.lam n / 2) n * (sz0.withLam fun n => -sz0.lam n).lam n ∧
    (fun n => -sz0.lam n / 2) n ^ 2 ≤ (sz0.withLam fun n => -sz0.lam n).lam n ^ 2 ∧
    (sz0.withLam fun n => -sz0.lam n).lam n ^ 2 ≤ 4 * (fun n => -sz0.lam n / 2) n ^ 2 := fun n => by
  have := step34Gen_lam0_nonneg n
  refine ⟨by change 0 ≤ (-sz0.lam n / 2) * (-sz0.lam n); nlinarith, by change (-sz0.lam n / 2) ^ 2 ≤ (-sz0.lam n) ^ 2; nlinarith,
    by change (-sz0.lam n) ^ 2 ≤ 4 * (-sz0.lam n / 2) ^ 2; nlinarith⟩

example : STEKWinKgL sz0 sz0.lam sInst tInst := step34Gen_winK_of_cmp step34Gen_cmp_band step34Gen_win_sz0
example : STEKWinKgL sz0 (fun n => sz0.lam n / 2) sInst tInst := step34Gen_winK_of_cmp step34Gen_cmp_half step34Gen_win_sz0

example : (((fun n => sz0.lam n / 2) 1) ^ 2 + |1 - (0 : ℝ)|) / (((fun n => sz0.lam n / 2) 1) ^ 2 + |1 - (1 / 16 : ℝ)|) ≤
    4 * ((sz0.lam 1 ^ 2 + |1 - (0 : ℝ)|) / (sz0.lam 1 ^ 2 + |1 - (1 / 16 : ℝ)|)) :=
  step34Gen_ratio_le step34Gen_cmp_half (by norm_num) 1 (by norm_num)

example (v : ℝ) : ((((fun n => sz0.lam n / 2) 1) ^ 2 + |1 - v|) / (((fun n => sz0.lam n / 2) 1) ^ 2 + |1 - (1 / 16 : ℝ)|)) ^ 2 ≤
    4 ^ 2 * ((sz0.lam 1 ^ 2 + |1 - v|) / (sz0.lam 1 ^ 2 + |1 - (1 / 16 : ℝ)|)) ^ 2 :=
  step34Gen_ratio_pow_le step34Gen_cmp_half (by norm_num) 1 (by norm_num) 2

example : ellT (sz0.L 1) ((fun n => sz0.lam n / 2) 1) 0 ≤ ellT (sz0.L 1) (sz0.lam 1) 0 := step34Gen_ellT_le step34Gen_cmp_half 1 0
example : ellT (sz0.L 1) (sz0.lam 1) 0 ≤ Real.sqrt 4 * ellT (sz0.L 1) ((fun n => sz0.lam n / 2) 1) 0 :=
  step34Gen_ellT_ge step34Gen_cmp_half (by norm_num) 1 0
example : ellT ((sz0.withLam fun n => -sz0.lam n).L 1) ((fun n => -sz0.lam n / 2) 1) 0 ≤
    ellT ((sz0.withLam fun n => -sz0.lam n).L 1) ((sz0.withLam fun n => -sz0.lam n).lam 1) 0 :=
  step34Gen_ellT_le step34Gen_cmp_neg 1 0
example : ellT ((sz0.withLam fun n => -sz0.lam n).L 1) ((sz0.withLam fun n => -sz0.lam n).lam 1) 0 ≤
    Real.sqrt 4 * ellT ((sz0.withLam fun n => -sz0.lam n).L 1) ((fun n => -sz0.lam n / 2) 1) 0 :=
  step34Gen_ellT_ge step34Gen_cmp_neg (by norm_num) 1 0

/-- (e) at `sz0`: the pinned decay at `sz0.lam` for the `δ₀` family gives the decay at `gK = sz0.lam / 2` (`A = 4`). -/
example : STEKDecayKgL (fun n => sz0.lam n / 2) (Sizes.seqP sz0) sInst tInst (fun n _ _ => ekDelta0 2 3 (sz0.L n)) :=
  step34Gen_decayK_of_cmp step34Gen_cmp_half (by norm_num) (step34Gen_W_tendsto sz0_admissible) (Sizes.seqP sz0)
    (step34Gen_decay_delta0 sz0 sInst tInst)

end Instances

end RBM.BA

end
