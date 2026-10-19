/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Carrier
import RBM3D.Induction.KDecay

/-!
# The time-uniform `𝒦` bounds over a flow carrier

The bounds `STKbound` and `STKward`, uniformly in `u ∈ [s_n, t_n]` as in `Induction/KDecay`, over a
carrier `C : FlowFM sz` and a probability law `μ`, from the per-time-sequence hypotheses
`STKboundgL C μ` and `STKwardgL C μ` (`Chain/Carrier`).  The left sides are deterministic, so the
per-sequence bound at every section `u n ∈ [s n, t n]` gives the bound over `TimeIcc s t`
(`Green.perTime_timeIcc_of_forall_seq`), and a per-time bound of a deterministic family is
eventually empty (`μ univ = 1`), hence a `PrecL`.

* `stKbound_timeIccgL`, `stKward_timeIccgL`: the two bounds uniformly in time.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The deterministic-family step and the section bridge -/

/-- A per-time bound of a deterministic family is a `PrecL` (restated for a probability law `μ`): each bad event is `∅` or the whole
space, and `μ univ = 1 > N^{-1}` for `N ≥ 2`.  Band form: `KDecay_prec_of_perTime_det`. -/
private theorem KDecayGen_prec_of_perTime_det {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hN : sz.SizeTendsto) {U : ℕ → Type*} (f g : ∀ n, U n → ℝ)
    (h : PerTimeDomAt μ sz.size (U := U) (fun n u _ => f n u) (fun n u _ => g n u)) :
    PrecL sz μ (fun n u _ => f n u) (fun n u _ => g n u) := by
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  have hsz := Sizes.tendsto_size sz hN
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_ge_atTop 2] with n hn hn2
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  by_contra hlt
  push Not at hlt
  have hset : {ω' : sz.SeqΩ | ((sz.size n : ℕ) : ℝ) ^ τ * g n u < f n u} = Set.univ := by
    ext ω'
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hlt
  have h1 := hn u
  rw [hset, measure_univ] at h1
  have hN2 : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn2
  have hlt1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  exact absurd h1 (not_le.2 (ENNReal.ofReal_lt_one.2 hlt1))

/-- The deterministic maximiser, as the bridge: sections `u n ∈ [s n, t n]` ⇒ the `PrecL` over `TimeIcc s t`.  Band form:
`KDecay_prec_timeIcc`. -/
private theorem KDecayGen_prec_timeIcc {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hN : sz.SizeTendsto) {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n)
    {V : ℕ → Type} (hV : ∀ n, Nonempty (V n)) (f g : ∀ n, ℝ → V n → ℝ)
    (h : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PrecL sz μ (U := V) (fun n v _ => f n (u n) v) (fun n v _ => g n (u n) v)) :
    PrecL sz μ (U := fun n => TimeIcc s t n × V n) (fun n p _ => f n (p.1 : ℝ) p.2)
      (fun n p _ => g n (p.1 : ℝ) p.2) := by
  refine KDecayGen_prec_of_perTime_det sz μ hN (U := fun n => TimeIcc s t n × V n)
    (fun n p => f n (p.1 : ℝ) p.2) (fun n p => g n (p.1 : ℝ) p.2) ?_
  refine Green.perTime_timeIcc_of_forall_seq μ sz.size hst hV
    (fun n u v _ => f n u v) (fun n u v _ => g n u v) fun u hu => ?_
  intro τ hτ D hD
  filter_upwards [h u hu τ hτ D hD] with n hn
  intro p
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  exact ⟨p.2, hω⟩

/-! ## 2. The bounds uniformly in time over a carrier -/

/-- `stKbound_timeIccgL` (band form `stKbound_timeIcc`): `max_{u ∈ [s,t], σ, a} |𝒦^{(k)}_{u,σ,a}| / (W^{-d}B_{u,0})^{k-1} ≺ 1`, every `k ≥ 1`,
from the per-sequence hypothesis `STKboundgL C μ` (Lemma 2.16, `ML:Kbound`), a probability law and the window `0 ≤ s ≤ t < 1`; the time is
inside the `≺`. -/
theorem stKbound_timeIccgL {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hN : sz.SizeTendsto) (hK : STKboundgL C μ) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 1 ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖C.K n (p.1 : ℝ) p.2.1 p.2.2‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)) := by
  intro k hk
  refine KDecayGen_prec_timeIcc sz μ hN hst (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n u p => ‖C.K n u p.1 p.2‖) (fun n u _ => (sz.Bctl n u) ^ (k - 1)) ?_
  intro u hu
  exact hK u (fun n => (hs0 n).trans (hu n).1) (fun n => (hu n).2.trans_lt (ht1 n)) k hk

/-- `stKward_timeIccgL` (band form `stKward_timeIcc`): Lemma 4.2 (`lem_wardineq_K`) uniformly in `u ∈ [s,t]`, in the label
convention of `STKwardgL` (`Chain/Carrier`). -/
theorem stKward_timeIccgL {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    (hN : sz.SizeTendsto) (hK : STKwardgL C μ) (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) :
    ∀ k : ℕ, 2 ≤ k →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
        (fun n p _ => ∑ x : Zd d (sz.L n),
          ‖C.K n (p.1 : ℝ) p.2.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2.2 ⟨i, h⟩ else x)‖)
        (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ (k - 2)) := by
  intro k hk
  refine KDecayGen_prec_timeIcc sz μ hN hst (V := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
    (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
    (fun n u p => ∑ x : Zd d (sz.L n),
      ‖C.K n u p.1 (fun i : Fin k => if h : (i : ℕ) < k - 1 then p.2 ⟨i, h⟩ else x)‖)
    (fun n u _ => (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * (sz.Bctl n u) ^ (k - 2)) ?_
  intro u hu
  exact hK u (fun n => (hs0 n).trans (hu n).1) (fun n => (hu n).2.trans_lt (ht1 n)) k hk

end RBM.BA
