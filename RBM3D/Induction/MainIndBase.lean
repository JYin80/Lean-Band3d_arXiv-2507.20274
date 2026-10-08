/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.Induction.AzumaProxyN
import RBM3D.Graph.LWExpTerm3

/-!
# ST-6 R1 (ticket T2340): the base case `t = 0` of the final assembly, over a carrier

Design `docs/reports/T2338-design.md` §2 (rows R1-R3 of §7), probe `RBM3D/Probe/T2338Pins.lean`
on `t/T2338` (lines 42-59, 81-139, 344-355).  Paper `1_2:1240-1243` (`G_0 = M`, `𝓛_0 = 𝒦_0`).

* the pins (`RBM.BA`, route G: over a carrier `(law, Flow, mk, T0)` as `STMainIndG`): `STConclgL`
  (the six conclusions of `lem:main_ind`), `STLK0` (`𝓛_0 = 𝒦_0`), `STG0M` (`G_0 = M`), `STBaseG`
  (the six conclusions at the zero sequence);
* `stBaseG_of_init`: `STBaseG` from `STLK0`, `STG0M` and `ML:Kbound` (`STKboundgL`) at every
  flow point;
* `stBase_band`: the band instance, with **no hypothesis** (the identity `𝓛_0 = 𝒦_0` is the now
  public `RBM.Ind.azumaProxy_loopFine_sub_STKloop`, whose keyword `private` is dropped in
  `Induction/AzumaProxyN.lean`).

`STLK0`, `STG0M`, `STBaseG` are owed for the block Anderson data (BA-V `GLoopAtT0`); the band
instances are proved here.

Imports: only what the file uses and what is not transitive (`Loop.KLFinal`, `stKbound_of_flow`,
comes with `Graph.LWExpTerm3`).
-/

set_option linter.unusedVariables false
set_option linter.style.longLine false

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Ind

namespace RBM.BA

variable {d : ℕ}

/-! ## 1. The pins -/

/-- The six conclusions of `lem:main_ind` at the time sequence `τ` over a carrier (the order of `STMainIndG`). -/
def STConclgL {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (τ : ℕ → ℝ) : Prop :=
  STLKgL C μ τ ∧ STLmaxgL C μ τ ∧ STDecaygL C μ τ ∧ STExp2gL C μ τ ∧ STLocalEntrygL C μ τ ∧
    STDecayStronggL C μ τ

/-- R1: `𝓛_0 = 𝒦_0` (`1_2:1240-1243`) for every loop length `k ≥ 1`. -/
def STLK0 {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ), 1 ≤ k → C.L n 0 σ a ω = C.K n 0 σ a

/-- R1: `G_0 = M` (`1_2:1240`). -/
def STG0M {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)), C.G n 0 ω x y = C.M n x y

/-- **R1 (base case)**: the six conclusions at the zero sequence, for every flow. -/
def STBaseG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 𝔠 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ),
    Flow sz κ ε 𝔠 𝔡 z → STConclgL (mk sz z) (law sz) (fun _ => 0)

/-! ## 2. The base case over a carrier (generic part) -/

section Base
variable {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `0 ≤ Bctl` (shared with `Induction/MainIndChain.lean`). -/
theorem mainIndBase_bctl_nonneg (n : ℕ) (t : ℝ) : 0 ≤ sz.Bctl n t := by unfold Sizes.Bctl Bparam; positivity

private theorem precL_of_zero {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (h0 : ∀ n u ω, ξ n u ω = 0)
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) : PrecL sz μ ξ ζ :=
  StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
    intro u
    rw [h0 n u ω]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ n u ω)

private theorem STLKgL_zero (h : STLK0 C) : STLKgL C μ (fun _ => 0) := fun k hk =>
  precL_of_zero μ (fun n p ω => by rw [h n k p.1 p.2 ω hk, sub_self, norm_zero])
    (fun n _ _ => pow_nonneg (mainIndBase_bctl_nonneg n _) _)

private theorem STLmaxgL_zero (h : STLK0 C) (hKb : STKboundgL C μ) : STLmaxgL C μ (fun _ => 0) := fun k hk =>
  StochDomAt.of_le_left (fun n p ω => by rw [h n k p.1 p.2 ω hk])
    (hKb (fun _ => 0) (fun _ => le_rfl) (fun _ => zero_lt_one) k hk)

private theorem STDecaygL_zero (h : STLK0 C) : STDecaygL C μ (fun _ => 0) := fun D hD =>
  precL_of_zero μ (fun n p ω => by rw [h n 2 p.1 p.2 ω (by norm_num), sub_self, norm_zero])
    (fun n p _ => add_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (mainIndBase_bctl_nonneg n _) _)
      (by unfold STWB Bparam; positivity)) (Real.exp_pos _).le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem STDecayStronggL_zero (h : STLK0 C) : STDecayStronggL C μ (fun _ => 0) := fun D hD =>
  precL_of_zero μ (fun n p ω => by rw [h n 2 p.1.1 p.1.2 ω (by norm_num), sub_self, norm_zero])
    (fun n p _ => add_nonneg (mul_nonneg (pow_nonneg (mainIndBase_bctl_nonneg n _) _) (Real.exp_pos _).le)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem STLocalEntrygL_zero (h : STG0M C) : STLocalEntrygL C μ (fun _ => 0) :=
  precL_of_zero μ (fun n p ω => by simp only [FlowFM.GM, h n ω, sub_self, norm_zero]; norm_num)
    (fun n p _ => by unfold STWB Bparam; positivity)

private theorem STExp2gL_zero [IsProbabilityMeasure μ] (h : STLK0 C) : STExp2gL C μ (fun _ => 0) :=
  precL_of_zero μ (fun n p ω => by
    have e : (fun ω => C.L n 0 p.1 p.2 ω) = fun _ => C.K n 0 p.1 p.2 := funext fun ω => h n 2 p.1 p.2 ω (by norm_num)
    simp [e, integral_const])
    (fun n _ _ => mul_nonneg (pow_nonneg (mainIndBase_bctl_nonneg n _) _) (add_nonneg (Real.rpow_nonneg (by positivity) _)
      (mainIndBase_bctl_nonneg n _)))

/-- **R1, generic**: the base case from the three carrier facts (`𝓛_0 = 𝒦_0`, `G_0 = M`, `ML:Kbound`). -/
theorem stBaseG_of_init {law : ∀ sz : Sizes d, Measure sz.SeqΩ} {Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop}
    {mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz} (hprob : ∀ sz, IsProbabilityMeasure (law sz))
    (hL : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STLK0 (mk sz z))
    (hG : ∀ κ ε 𝔠 𝔡 sz z, Flow sz κ ε 𝔠 𝔡 z → STG0M (mk sz z))
    (hK : 3 ≤ d → ∀ κ ε 𝔠 𝔡 sz z, 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKboundgL (mk sz z) (law sz)) : STBaseG d law Flow mk := by
  intro hd κ ε 𝔡 𝔠 hκ _ _ sz z hf
  have := hprob sz
  exact ⟨STLKgL_zero _ _ (hL _ _ _ _ _ _ hf), STLmaxgL_zero _ _ (hL _ _ _ _ _ _ hf) (hK hd _ _ _ _ _ _ hκ hf),
    STDecaygL_zero _ _ (hL _ _ _ _ _ _ hf), STExp2gL_zero _ _ (hL _ _ _ _ _ _ hf),
    STLocalEntrygL_zero _ _ (hG _ _ _ _ _ _ hf), STDecayStronggL_zero _ _ (hL _ _ _ _ _ _ hf)⟩

end Base

/-! ## 3. The band instance: no hypothesis -/

/-- **R1, band**: the base case for the band model (`Sizes.seqP`, `STFlow`, `bandFM`).  `𝓛_0 = 𝒦_0` is
`RBM.Ind.azumaProxy_loopFine_sub_STKloop` at `H_0 = 0` (`Sizes.seqHflow n 0 ω = 0`), `G_0 = M` is `lwExpTerm3_Gt_zero`,
`ML:Kbound` is `stKbound_of_flow`. -/
theorem stBase_band (d : ℕ) :
    STBaseG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) := by
  have hE : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z → ∀ n, |STflowE z n| < 2 := fun sz _ _ _ _ z hf n =>
    abs_lemE_lt_two (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hf.2 n).2.1)
  refine stBaseG_of_init (fun sz => inferInstance) (fun κ ε 𝔠 𝔡 sz z hf n k σ a ω hk => ?_)
    (fun κ ε 𝔠 𝔡 sz z hf n ω x y => lwExpTerm3_Gt_zero sz n (hE sz κ ε 𝔠 𝔡 z hf n) ω x y)
    (fun hd κ ε 𝔠 𝔡 sz z hκ hf => (bandFM_STKbound sz (STflowE z)).1 (stKbound_of_flow sz hd hκ hf))
  change Lloop sz n (STflowE z n) 0 σ a ω = sz.STKloop n (STflowE z n) 0 σ a
  unfold Lloop
  rw [show sz.seqHflow n 0 ω = 0 by simp [Sizes.seqHflow]]
  exact sub_eq_zero.1 (azumaProxy_loopFine_sub_STKloop sz n (hE sz κ ε 𝔠 𝔡 z hf n) hk σ a)

end RBM.BA

/-! ## 4. Compiled nonempty instances (`d = 3`, merged data `sz0`, `z0`, `zSeq`) -/

namespace RBM.Gauss.MainIndInst

open RBM.BA RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-- `stBase_band` at the merged band data `sz0`, `z0` (`d = 3`, `𝔠 = 1/6`, `κ = ε = 𝔡 = 1/10`): the six conclusions
at the zero sequence, no hypothesis. -/
example : STConclgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) (fun _ => 0) :=
  stBase_band 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (1 / 6) (by norm_num) (by norm_num) (by norm_num) sz0 z0 flow_z0

/-- `stBaseG_of_init` at the block Anderson data `sz0`, `zSeq` (`BAFlow` holds by `flow_sz0`): the three BA carrier
facts (`𝓛_0 = 𝒦_0`, `G_0 = M`, `ML:Kbound`; BA-V `GLoopAtT0`, BA-K) stay hypotheses; every other premise is
discharged. -/
example (hL : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STLK0 (baFMz sz z))
    (hG : ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, BAFlow sz κ ε 𝔠 𝔡 z → STG0M (baFMz sz z))
    (hK : 3 ≤ 3 → ∀ κ ε 𝔠 𝔡 (sz : Sizes 3) z, 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))) :
    STConclgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 0) :=
  stBaseG_of_init (law := fun sz => Sizes.seqP (sz.withLam 0)) (fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0)) hL hG hK (by norm_num) (1 / 2) (1 / 10) (1 / 10) (1 / 6) (by norm_num)
    (by norm_num) (by norm_num) sz0 zSeq flow_sz0

end RBM.Gauss.MainIndInst
