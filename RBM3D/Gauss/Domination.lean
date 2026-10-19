/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Defs.StochDom
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moments and nets for stochastic domination

Two elementary tools for passing between moment bounds and bounds with high probability.

* Markov's inequality at a single scale (`meas_gt_le_of_moment`): a bound `M` on the `2p`-th
  moment of `Y` gives `P(Y > t) ≤ M / t^{2p}`.  Summed over a polynomially large parameter set
  (a union bound), moment bounds `C(ε,p) N^{εp} Φ^{2p}` for every `ε > 0` and `p` give
  stochastic domination by `Φ`, `(stoch_domination)`.
* The uniform time net on `[0, T]` with `⌈N^A⌉₊ + 1` subintervals (`netSize`, `netPt`,
  `exists_netPt_close`, `card_net_le`), which upgrades a bound at polynomially many points of
  an interval to a bound on the whole interval, for Hölder or Lipschitz families.  It is what
  lets a statement proved at each fixed time be quoted uniformly in `t`.

The mathematics is dimension-independent.
-/
namespace RBM.Gauss

open Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Markov's inequality -/

section Markov

variable (P : Measure Ω) [IsFiniteMeasure P]

/-- **Markov / Chebyshev at a single scale.**  A bound `M` on the `2p`-th moment of `Y` gives
`P(Y > t) ≤ M / t^{2p}` for every threshold `t > 0`. -/
theorem meas_gt_le_of_moment {Y : Ω → ℝ} {p : ℕ} {t M : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * p)) P)
    (hM : ∫ ω, |Y ω| ^ (2 * p) ∂P ≤ M) :
    P {ω | t < Y ω} ≤ ENNReal.ofReal (M / t ^ (2 * p)) := by
  have hnn : 0 ≤ᵐ[P] fun ω => |Y ω| ^ (2 * p) :=
    Filter.Eventually.of_forall fun ω => by positivity
  have htp : (0 : ℝ) < t ^ (2 * p) := by positivity
  -- the failure event sits inside the level set of the `2p`-th power
  have hsub : {ω | t < Y ω} ⊆ {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    exact pow_le_pow_left₀ ht.le ((le_abs_self (Y ω)).trans' hω.le) _
  -- Markov
  have hmark := mul_meas_ge_le_integral_of_nonneg hnn hint (t ^ (2 * p))
  have hreal : P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} ≤ M / t ^ (2 * p) := by
    rw [le_div_iff₀ htp, mul_comm]
    exact hmark.trans hM
  calc P {ω | t < Y ω} ≤ P {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | t ^ (2 * p) ≤ |Y ω| ^ (2 * p)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P _)]
    _ ≤ ENNReal.ofReal (M / t ^ (2 * p)) := ENNReal.ofReal_le_ofReal hreal

end Markov

/-! ### The time net -/

section Net

/-- The number of subintervals of the time net on `[0, T]`: `⌈N^A⌉₊ + 1` (the `+1` keeps it
positive for every `N` and every `A`). -/
noncomputable def netSize (A : ℝ) (N : ℕ) : ℕ := ⌈(N : ℝ) ^ A⌉₊ + 1

theorem netSize_pos (A : ℝ) (N : ℕ) : 0 < netSize A N := Nat.succ_pos _

theorem rpow_le_netSize (A : ℝ) (N : ℕ) : (N : ℝ) ^ A ≤ (netSize A N : ℝ) := by
  have := Nat.le_ceil ((N : ℝ) ^ A)
  have h : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) ≤ (netSize A N : ℝ) := by
    unfold netSize; push_cast; linarith
  linarith

/-- The `k`-th point `k T / m` of the uniform net with `m = netSize A N` subintervals
on `[0, T]`. -/
noncomputable def netPt (T A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) : ℝ :=
  (k : ℝ) * T / (netSize A N : ℝ)

theorem netPt_mem_Icc {T : ℝ} (hT : 0 ≤ T) (A : ℝ) (N : ℕ) (k : Fin (netSize A N + 1)) :
    netPt T A N k ∈ Set.Icc (0 : ℝ) T := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hk : (k : ℝ) ≤ (netSize A N : ℝ) := by
    have : (k : ℕ) ≤ netSize A N := Nat.lt_succ_iff.1 k.isLt
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  constructor
  · simp only [netPt]
    exact div_nonneg (mul_nonneg hk0 hT) hm.le
  · simp only [netPt]
    rw [div_le_iff₀ hm]
    nlinarith

/-- Every point of `[0, T]` is within `T / netSize A N` of a net point. -/
theorem exists_netPt_close {T : ℝ} (hT : 0 < T) (A : ℝ) (N : ℕ) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) T) :
    ∃ k : Fin (netSize A N + 1), |u - netPt T A N k| ≤ T / (netSize A N : ℝ) := by
  have hm : (0 : ℝ) < (netSize A N : ℝ) := by exact_mod_cast netSize_pos A N
  have hx0 : 0 ≤ u * (netSize A N : ℝ) / T := div_nonneg (mul_nonneg hu.1 hm.le) hT.le
  have hxm : u * (netSize A N : ℝ) / T ≤ (netSize A N : ℝ) := by
    rw [div_le_iff₀ hT]
    nlinarith [hu.2, hm.le]
  have hkm : ⌊u * (netSize A N : ℝ) / T⌋₊ ≤ netSize A N := Nat.floor_le_of_le hxm
  have hfl : ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) ≤ u * (netSize A N : ℝ) / T :=
    Nat.floor_le hx0
  have hfu : u * (netSize A N : ℝ) / T < ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩, ?_⟩
  have hnet : netPt T A N ⟨⌊u * (netSize A N : ℝ) / T⌋₊, Nat.lt_succ_of_le hkm⟩
      = ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := rfl
  have hkey : (u * (netSize A N : ℝ) / T - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ))
      * (T / (netSize A N : ℝ))
      = u - ((⌊u * (netSize A N : ℝ) / T⌋₊ : ℕ) : ℝ) * T / (netSize A N : ℝ) := by
    field_simp
  rw [hnet, ← hkey,
    abs_of_nonneg (mul_nonneg (by linarith) (div_pos hT hm).le)]
  exact mul_le_of_le_one_left (div_pos hT hm).le (by linarith)

theorem card_net_le {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ N : ℕ in atTop, (Fintype.card (Fin (netSize A N + 1)) : ℝ) ≤ (N : ℝ) ^ (A + 1) := by
  filter_upwards [eventually_ge_atTop 4] with N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ A := Real.one_le_rpow hN1 hA
  have hceil : ((⌈(N : ℝ) ^ A⌉₊ : ℝ)) < (N : ℝ) ^ A + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hcard : (Fintype.card (Fin (netSize A N + 1)) : ℝ) = (⌈(N : ℝ) ^ A⌉₊ : ℝ) + 2 := by
    rw [Fintype.card_fin, netSize]; push_cast; ring
  have hrpow : (N : ℝ) ^ (A + 1) = (N : ℝ) ^ A * (N : ℝ) := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  rw [hcard, hrpow]
  nlinarith

end Net

end RBM.Gauss


