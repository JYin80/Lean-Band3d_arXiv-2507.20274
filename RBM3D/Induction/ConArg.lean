/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.PerTimeCalc
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Defs

/-!
# `lem_ConArg` (`3_5:42-62`): the continuity argument, probabilistic part (ST-1, S1-32)

Ticket T2076.  Port of `RBM2D/Induction/ConArg.lean` at `c9a24cf` (807 lines; its `d = 2` checks,
lines 764-807, are replaced by the `d = 3` instances of section 7).
Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (cited `3_5:line`), Lemma `lem_ConArg`
(`3_5:42-62`), hypothesis `(eq:loopbound_s)` (`3_5:46`) and `(res_lo_bo_eta)` (`3_5:52`).

* `ConArgPin` (RBM2D `ConArg.lean:61`) and `conArg` (RBM2D `:613`): per time (`PrecPT`, the union
  over the loop parameter `(σ, a)` outside `P`), at general energy `E`, times `s ≤ t < 1`, constants
  `κ`, `c = ε₁`, `C₀`.  The right side is `(Bctl_s · η_s/η_t)^{k-1}` with `Bctl_s = W^{-d} B_{s,0}`
  (merged `Sizes.Bctl`); RBM2D's `(ℓ₂/ℓ₁)^{2(k-1)} M_{t₂}^{-(k-1)} = (W² ℓ₁² η₂)^{-(k-1)}` has
  no `d ≥ 3` reading (T2015 report b, row `STConArg`; T2045 `ScaleFacts`).  `Ω_t = {‖G_t‖_max ≤ C₀}`
  is the merged `STomegaC` (RBM2D: threshold `2`).
* `stConArg_holds` : `STConArg d` for every `d` (the merged pin, `Induction/Defs.lean:334`): the
  hypothesis `STLmax` (`Prec`) gives the per-time (55) by `Path.perTimeOfStochDomAt`; the per-time
  conclusion of `conArg` gives `Prec` by `Path.stochDomAt_of_perTimeDomAt` (`#U ≤ size^{2k}`).

## Route (ports from RBM2D, which cites RBM1D commit `86573b9`)

* section 1: the recursion of §6 under `PerTimeDomAt`
  (`RBM1D/Loop/ContinuityAssembly.lean:646-697`); the constant `2` of `Y_1 ≤ 2`
  (`E_a = W^{-2}1_{[a]}` and entries `≤ 2` on `Ω`) becomes a parameter `B ≥ 0` (here `B = C₀`).
* section 2: (6.1) on the common sample space, `G̃ = (H_t - z̃_s)⁻¹ = √(s/t) G_s` since
  `H_u = √u X` (`seqHflow_eq_smul`); every loop of `G̃` of length `j` is `(s/t)^{j/2} ≤ 1` times the
  loop of `G_s`.  The RBM2D list-based `gloop` is the merged `loopL` (`loopM_eq_loopL`,
  `GLoopFlow.lean:127`), `Gsig` is `Gres`.
* section 3: the base case (5.6): `Y_1 ≤ C₀` on `Ω_t` (`E_a = diag(bw a)`, `sum_bw`).
* section 4: from the parameter `(σ, a)` to `max_{σ,a}`
  (`#((Fin k → Bool) × (Fin k → Zd d L)) ≤ size^{2k}`).

## What changes from `d = 2` (rule R1-R3 of `docs/tickets/ST1-COMMON.md`)

`Sizes` (the `d = 2` size data) becomes `sz : Sizes d`; `Z2 L` becomes `Zd d L`;
`W⁻² 1_{𝓘_a}` becomes `W^{-d} 1_{[a]}` (the merged `Eblk`, `bw`); `size = (W L)^d`; `scaleM`,
`ellT` of the statement become `Bctl`, `etaT`.  The scale `a₁ = Bctl_s` enters only through
`a₁ > 0`, `a₁ ≤ a`, `a₁⁻¹ ≤ size` (`Bparam ≥ L^{-d}` for `0 < 1 - s ≤ 1`: any `d`, any `lam`,
any `L`) and `K a₁ ≤ C a`
(`ztTilde_arith`, constants depend on `ε₁, κ` only).  No step needs `d ≥ 3` or `W → ∞`.

All helpers are `private`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

/-! ## 1. The recursion of §6 under `PerTimeDomAt` -/

section Recursion

open PerTimeCalc.PerTime

/-- `(x^{pj-1})^{1/p} ≤ x^j M^{1/p}` for `x > 0`, `x⁻¹ ≤ M`: the loss `M_{t₁}^{1/p}` of (6.10).
Port of RBM1D `rpow_pow_mul_sub_one_le` (`ContinuityAssembly.lean:646`). -/
private theorem conArg_rpow_pow_mul_sub_one_le {x M : ℝ} (hx : 0 < x) (hM : x⁻¹ ≤ M) {p j : ℕ}
    (hp : 1 ≤ p) (hj : 1 ≤ j) :
    (x ^ (p * j - 1)) ^ (1 / (p : ℝ)) ≤ x ^ j * M ^ (1 / (p : ℝ)) := by
  have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : x ^ (p * j - 1) = (x ^ j) ^ p * x⁻¹ := by
    rw [← pow_mul, mul_comm j p]
    have : x ^ (p * j) = x ^ (p * j - 1) * x := by
      rw [← pow_succ]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  rw [e, Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM (by positivity))
    (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Multiplying both sides of `≺` by a deterministic non-negative factor.  Port of RBM1D
`StochDom.det_mul_of` (`ContinuityAssembly.lean:663`). -/
private theorem conArg_det_mul (hsize : Tendsto size atTop atTop) {f : ℕ → ℝ}
    (hf : ∀ N, 0 ≤ f N) {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun N u ω => f N * ξ N u ω) (fun N u ω => f N * ζ N u ω) :=
  perTimeCalc_mul (ξ₁ := fun N _ _ => f N) (ζ₁ := fun N _ _ => f N) hsize hξ
    (fun N _ _ => hf N) (perTimeCalc_refl hsize fun N _ _ => hf N) h

/-- A pointwise smaller left side. -/
private theorem conArg_of_le_left {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) (h : PerTimeDomAt P size ξ' ζ) :
    PerTimeDomAt P size ξ ζ :=
  stochDom_of_le_left_eventually (Eventually.of_forall hle) h

/-- **Odd loops from even ones** ((6.4) under `≺`).  Port of RBM1D `StochDom.odd_of_even`
(`ContinuityAssembly.lean:670`). -/
private theorem conArg_odd_of_even (hsize : Tendsto size atTop atTop)
    {Y : ℕ → ∀ N, U N → Ω → ℝ} {a : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N)
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) {l : ℕ} (hl : 1 ≤ l)
    (hodd : ∀ N u ω, Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (h1 : PerTimeDomAt P size (Y (2 * l)) (fun N _ _ => a N ^ (2 * l - 1)))
    (h2 : PerTimeDomAt P size (Y (2 * l + 2)) (fun N _ _ => a N ^ (2 * l + 1))) :
    PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
  have hm := perTimeCalc_mul hsize (hY0 _) (fun N _ _ => pow_nonneg (ha N) _) h1 h2
  have hs := sqrt_of (fun N u ω => mul_nonneg (hY0 _ N u ω) (hY0 _ N u ω))
    (fun N u ω => mul_nonneg (pow_nonneg (ha N) _) (pow_nonneg (ha N) _)) hm
  have e : ∀ N, Real.sqrt (a N ^ (2 * l - 1) * a N ^ (2 * l + 1)) = a N ^ (2 * l) := by
    intro N
    rw [← pow_add, show 2 * l - 1 + (2 * l + 1) = 2 * (2 * l) by omega, pow_mul',
      Real.sqrt_sq (pow_nonneg (ha N) _)]
  refine conArg_of_le_left (fun N u ω => Real.le_sqrt_of_sq_le (hodd N u ω)) ?_
  simpa only [e] using hs

/-- **The induction of §6, abstractly, per time.**  Port of RBM1D
`StochDom.continuity_recursion` (`ContinuityAssembly.lean:697`) with `N ↦ size N`:
for deterministic `0 < a₁ ≤ a`, `K ≥ 0`, `K a₁ ≤ C a`, `a₁⁻¹ ≤ size`, and families `Y_n, T_n ≥ 0`
with `T_n ≺ a₁^{n-1}`, `Y_1 ≤ B`, (6.4) and (6.11), one has `Y_n ≺ a^{n-1}` for every `n ≥ 1`. -/
private theorem conArg_continuity_recursion (hsize : Tendsto size atTop atTop)
    {Y T : ℕ → ∀ N, U N → Ω → ℝ} {a a1 K : ℕ → ℝ} {C B : ℝ}
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) (hT0 : ∀ n N u ω, 0 ≤ T n N u ω)
    (ha1 : ∀ N, 0 < a1 N) (ha1a : ∀ N, a1 N ≤ a N) (hK0 : ∀ N, 0 ≤ K N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ N, K N * a1 N ≤ C * a N) (hN : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ (size N : ℝ))
    (hT : ∀ n, 1 ≤ n → PerTimeDomAt P size (T n) (fun N _ _ => a1 N ^ (n - 1)))
    (hY1 : ∀ N u ω, Y 1 N u ω ≤ B)
    (hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ)))) :
    ∀ n, 1 ≤ n → PerTimeDomAt P size (Y n) (fun N _ _ => a N ^ (n - 1)) := by
  have ha0 : ∀ N, 0 < a N := fun N => (ha1 N).trans_le (ha1a N)
  have hY1' : PerTimeDomAt P size (Y 1) (fun N _ _ => a N ^ (2 * 0)) := by
    simp only [mul_zero, pow_zero]
    exact stochDom_of_le_const_mul hsize (hY0 1) (fun _ _ _ => zero_le_one) B
      (fun N u ω => by linarith [hY1 N u ω])
  -- the even lengths, by strong induction
  have hE : ∀ m, 1 ≤ m → PerTimeDomAt P size (Y (2 * m)) (fun N _ _ => a N ^ (2 * m - 1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hOdd : ∀ l, l < k → PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
      intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hY1'
      · refine conArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hl0 (hodd l hl0)
          (ih l (by omega) hl0) ?_
        have := ih (l + 1) (by omega) (by omega)
        rwa [show 2 * (l + 1) = 2 * l + 2 by ring, show 2 * l + 2 - 1 = 2 * l + 1 by omega]
          at this
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    refine of_forall_rpow_mul fun δ hδ => ?_
    obtain ⟨p0, hp0⟩ := exists_nat_one_div_lt (half_pos hδ)
    set p := p0 + 1 with hp_def
    have hp : 1 ≤ p := by omega
    set r : ℝ := 1 / (p : ℝ) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one (by positivity)]; exact_mod_cast hp
    have hrδ : r + r ≤ δ := by
      have : r < δ / 2 := by rw [hr, hp_def]; push_cast; exact hp0
      linarith
    set A : ℕ → ℝ := fun N => a N ^ (2 * k + 1) with hA
    have hA0 : ∀ N, 0 ≤ A N := fun N => pow_nonneg (ha0 N).le _
    have hNr : ∀ N : ℕ, 0 ≤ (size N : ℝ) ^ r := fun N => Real.rpow_nonneg (Nat.cast_nonneg _) r
    have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ (size N : ℝ) ^ r ∧ (a1 N)⁻¹ ≤ (size N : ℝ) := by
      filter_upwards [hN, hsize.eventually (eventually_ge_atTop 1)] with N hN1 hN2
      exact ⟨Real.one_le_rpow (by exact_mod_cast hN2) hr0.le, hN1⟩
    -- (R1): the `G̃` loop of length `2m`
    have hR1 : PerTimeDomAt P size (T (2 * (k + 1)))
        (fun N _ _ => A N * (size N : ℝ) ^ r) := by
      refine mono_right_eventually (hT (2 * (k + 1)) (by omega)) ?_
      filter_upwards [hev] with N hN u ω
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      calc a1 N ^ (2 * k + 1) ≤ A N := pow_le_pow_left₀ (ha1 N).le (ha1a N) _
        _ ≤ A N * (size N : ℝ) ^ r := le_mul_of_one_le_right (hA0 N) hN.1
    -- the `G̃` factors `T^{1/p}`
    have hTr : ∀ j, 1 ≤ j → PerTimeDomAt P size (fun N u ω => K N * T (p * j) N u ω ^ r)
        (fun N _ _ => C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r) := by
      intro j hj
      have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h1 := conArg_det_mul hsize hK0 (fun N u ω => Real.rpow_nonneg (hT0 _ N u ω) r)
        (rpow_of_le_one hr0 hr1 (hT0 (p * j)) (fun N _ _ => pow_nonneg (ha1 N).le _)
          (hT (p * j) hpj))
      refine mono_right_eventually h1 ?_
      filter_upwards [hev] with N hN u ω
      have h2 := conArg_rpow_pow_mul_sub_one_le (ha1 N) hN.2 hp hj
      calc K N * (a1 N ^ (p * j - 1)) ^ r ≤ K N * (a1 N ^ j * (size N : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left h2 (hK0 N)
        _ = (K N * a1 N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r := by
            rw [show a1 N ^ j = a1 N * a1 N ^ (j - 1) by
              rw [← pow_succ']; congr 1; omega]
            ring
        _ ≤ (C * a N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK N)
              (pow_nonneg (ha1 N).le _)) (hNr N)
        _ = C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r := by ring
    -- (R2): the terms `l < m - 1`
    have hR2 : PerTimeDomAt P size (fun N u ω => ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        (fun N _ _ => ∑ l ∈ Finset.range k, C * A N * (size N : ℝ) ^ r) := by
      refine finset_sum_of hsize _ fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      have hj : 1 ≤ 2 * (k + 1 - l) - 1 := by omega
      have h1 := perTimeCalc_mul hsize
        (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 _ N u ω) r))
        (fun N _ _ => pow_nonneg (ha0 N).le _) (hOdd l hl') (hTr _ hj)
      refine mono_right_eventually (conArg_of_le_left (fun N u ω => le_of_eq ?_) h1) ?_
      · ring
      · filter_upwards [hev] with N hN u ω
        have e : 2 * (k + 1 - l) - 1 - 1 = 2 * (k - l) := by omega
        rw [e]
        calc a N ^ (2 * l) * (C * a1 N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r)
            ≤ a N ^ (2 * l) * (C * a N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (ha1 N).le (ha1a N) _) hC) (ha0 N).le) (hNr N))
                (pow_nonneg (ha0 N).le _)
          _ = C * A N * (size N : ℝ) ^ r := by
              simp only [hA]
              rw [show 2 * k + 1 = 2 * l + 2 * (k - l) + 1 by omega, pow_succ, pow_add]
              ring
    -- (R3): the term `l = m - 1`
    have hR3 : PerTimeDomAt P size (fun N u ω => K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r))
        (fun N u ω => B * C * A N * (size N : ℝ) ^ r
          + C * (size N : ℝ) ^ r * Real.sqrt (A N * Y (2 * (k + 1)) N u ω)) := by
      have hT1 := hTr 1 le_rfl
      simp only [mul_one, Nat.sub_self, pow_zero] at hT1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · -- `m = 1`: the base case (5.6)
        have h1 := conArg_det_mul (f := fun _ => B) hsize (fun _ => hB)
          (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)) hT1
        refine mono_right_eventually (conArg_of_le_left (fun N u ω => ?_) h1) ?_
        · have hy := hY1 N u ω
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          simp only [mul_zero, zero_add]
          nlinarith
        · filter_upwards with N u ω
          simp only [hA, mul_zero, zero_add, pow_one]
          have h1 : 0 ≤ C * (size N : ℝ) ^ r * Real.sqrt (a N * Y (2 * 1) N u ω) :=
            mul_nonneg (mul_nonneg hC (hNr N)) (Real.sqrt_nonneg _)
          have h2 : 0 ≤ C * a N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)
          linarith
      · -- `m > 1`: (6.4) and the induction hypothesis for the `(2m-2)`-loops
        have hIH := sqrt_of (hY0 _) (fun N _ _ => pow_nonneg (ha0 N).le _)
          (ih k (by omega) hk0)
        have h1 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg _)
          (fun N _ _ => mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)) hT1 hIH
        have h2 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
          (fun N _ _ => mul_nonneg (mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N))
            (Real.sqrt_nonneg _)) h1
          (perTimeCalc_refl hsize fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
        refine mono_right_eventually (conArg_of_le_left (fun N u ω => ?_) h2) ?_
        · have hodd' := hodd k hk0 N u ω
          rw [show 2 * k + 2 = 2 * (k + 1) by ring] at hodd'
          have hy : Y (2 * k + 1) N u ω
              ≤ Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            rw [← Real.sqrt_mul (hY0 _ N u ω)]
            exact Real.le_sqrt_of_sq_le hodd'
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          calc K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)
              = (K N * T p N u ω ^ r) * Y (2 * k + 1) N u ω := by ring
            _ ≤ (K N * T p N u ω ^ r)
                * (Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω)) :=
                mul_le_mul_of_nonneg_left hy hk
            _ = _ := by ring
        · filter_upwards with N u ω
          have e : Real.sqrt (A N * Y (2 * (k + 1)) N u ω)
              = a N * Real.sqrt (a N ^ (2 * k - 1)) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            simp only [hA]
            rw [show 2 * k + 1 = 2 + (2 * k - 1) by omega, pow_add,
              Real.sqrt_mul (mul_nonneg (pow_nonneg (ha0 N).le _) (pow_nonneg (ha0 N).le _)),
              Real.sqrt_mul (pow_nonneg (ha0 N).le _), Real.sqrt_sq (ha0 N).le]
          rw [e]
          have : 0 ≤ B * C * A N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg (mul_nonneg hB hC) (hA0 N)) (hNr N)
          nlinarith [this]
    -- (6.13): assemble
    have hsum : ∀ N u ω, Y (2 * (k + 1)) N u ω ≤ ((k : ℝ) + 2) * ((T (2 * (k + 1)) N u ω
        + ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        + K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)) := by
      intro N u ω
      have h := hrec (k + 1) (by omega) p hp N u ω
      rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega,
        show p * (2 * 1 - 1) = p by ring, ← hr] at h
      refine h.trans (le_of_eq ?_)
      rw [mul_add (K N), Finset.mul_sum]
      push_cast
      ring
    have hR := conArg_det_mul (f := fun _ => (k : ℝ) + 2) hsize (fun _ => by positivity)
      (fun N u ω => add_nonneg (add_nonneg (hT0 _ N u ω) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
        (mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
      (perTimeCalc_add hsize (perTimeCalc_add hsize hR1 hR2) hR3)
    set D1 : ℝ := ((k : ℝ) + 2) * (1 + ((k : ℝ) + B) * C) with hD1
    set D2 : ℝ := ((k : ℝ) + 2) * C with hD2
    set D : ℝ := (D1 + D2 + 1) ^ 2 with hD
    have hD1_0 : 0 ≤ D1 := mul_nonneg (by positivity)
      (by have := mul_nonneg (add_nonneg (Nat.cast_nonneg k) hB) hC; linarith)
    have hD2_0 : 0 ≤ D2 := mul_nonneg (by positivity) hC
    have hD1D : D1 ≤ D := by nlinarith
    have hD2D : D2 ^ 2 ≤ D := by nlinarith
    have hD0 : 0 ≤ D := sq_nonneg _
    have hstep : PerTimeDomAt P size (Y (2 * (k + 1))) (fun N u ω =>
        D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
          + Real.sqrt (D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
            * Y (2 * (k + 1)) N u ω)) := by
      refine mono_right_eventually (conArg_of_le_left (fun N u ω => hsum N u ω) hR) ?_
      filter_upwards [hev] with N hN u ω
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      set x := (size N : ℝ) ^ r
      set y := Y (2 * (k + 1)) N u ω
      have hx1 : 1 ≤ x := hN.1
      have hy : 0 ≤ y := hY0 _ N u ω
      have hAy : 0 ≤ A N * y := mul_nonneg (hA0 N) hy
      have p1 : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
          ≤ D * (x * x * A N) := by
        have e : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
            = D1 * (A N * x) := by rw [hD1]; ring
        rw [e]
        have hAx : 0 ≤ A N * x := mul_nonneg (hA0 N) (by linarith)
        calc D1 * (A N * x) ≤ D * (A N * x) := mul_le_mul_of_nonneg_right hD1D hAx
          _ ≤ D * (A N * x * x) := mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hAx hx1) hD0
          _ = D * (x * x * A N) := by ring
      have p2 : ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
          ≤ Real.sqrt (D * (x * x * A N) * y) := by
        refine Real.le_sqrt_of_sq_le ?_
        have e : (((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))) ^ 2
            = D2 ^ 2 * (x ^ 2 * (A N * y)) := by
          rw [show ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
            = D2 * x * Real.sqrt (A N * y) by rw [hD2]; ring, mul_pow, mul_pow,
            Real.sq_sqrt hAy]
          ring
        rw [e]
        calc D2 ^ 2 * (x ^ 2 * (A N * y)) ≤ D * (x ^ 2 * (A N * y)) :=
              mul_le_mul_of_nonneg_right hD2D (mul_nonneg (sq_nonneg _) hAy)
          _ = D * (x * x * A N) * y := by ring
      calc ((k : ℝ) + 2) * (A N * x + k * (C * A N * x)
            + (B * C * A N * x + C * x * Real.sqrt (A N * y)))
          = ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
            + ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y)) := by ring
        _ ≤ _ := add_le_add p1 p2
    have hZ0 : ∀ N (u : U N) (ω : Ω), 0 ≤ (size N : ℝ) ^ r * (size N : ℝ) ^ r * A N :=
      fun N _ _ => mul_nonneg (mul_nonneg (hNr N) (hNr N)) (hA0 N)
    have hZ := of_le_add_sqrt_mul hsize (hY0 _) (fun N u ω => mul_nonneg hD0 (hZ0 N u ω))
      hstep
    refine perTimeCalc_mono hsize
      (fun N _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (hA0 N)) D ?_ hZ
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with N hN1 u ω
    have hN1' : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1' hrδ) (hA0 N)) hD0
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact hE m (by omega)
  · rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hY1'
    · refine conArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hm0 (hodd m hm0) (hE m hm0) ?_
      have := hE (m + 1) (by omega)
      rwa [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 - 1 = 2 * m + 1 by omega]
        at this

end Recursion

/-! ## 2. (6.1) on the common sample space: the loops of `G̃` -/

section Scaling

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar (no invertibility assumption on `A`).  Port of
RBM1D `inv_smul_of_ne_zero` (`Gauss/DistEq.lean:68`) through RBM2D `ConArg.lean:380`. -/
private theorem conArg_inv_smul {c : ℂ} (hc : c ≠ 0) (A : Matrix n n ℂ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- `G(cH, cz) = c⁻¹ G(H, z)`.  Port of RBM1D `green_smul_mul` (`Gauss/DistEq.lean:81`) through
RBM2D `ConArg.lean:394`. -/
private theorem conArg_green_smul_mul {c : ℂ} (hc : c ≠ 0) (H : Matrix n n ℂ) (z : ℂ) :
    green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold green
  rw [hsub, conArg_inv_smul hc]

/-- The same for `Gres` with a real scalar.  RBM2D `ConArg.lean:419` (`conArg_Gsig_smul_mul`),
`Gsig → Gres`. -/
private theorem conArg_Gres_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0) (H : Matrix n n ℂ) (z : ℂ)
    (σ : Bool) : Gres ((r : ℂ) • H) ((r : ℂ) * z) σ = ((r : ℂ))⁻¹ • Gres H z σ := by
  rw [Gres_eq_green_zSig, Gres_eq_green_zSig]
  cases σ with
  | true => simpa only [zSig_true] using conArg_green_smul_mul hr H z
  | false =>
    simp only [zSig_false]
    rw [map_mul, Complex.conj_ofReal]
    exact conArg_green_smul_mul hr H _

variable {d L W : ℕ} [NeZero L]

/-- The word of a list of `(σ, a)` pairs scales by `c⁻¹` per factor. -/
private theorem conArg_foldr_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (l : List (Bool × Zd d L)) :
    l.foldr (fun p M => Gres ((r : ℂ) • H) ((r : ℂ) * z) p.1 * Eblk d L W p.2 * M) 1
      = (((r : ℂ))⁻¹ ^ l.length) • l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih, conArg_Gres_smul_mul hr, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_succ']

/-- `L(cH, cz) = c⁻ⁿ L(H, z)`.  RBM2D `ConArg.lean:441` (`conArg_gloop_smul_mul`), the list-based
`gloop` being the merged `loopL`. -/
private theorem conArg_loopL_smul_mul {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * loopL d L W H z I := by
  unfold loopL
  rw [conArg_foldr_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

end Scaling

/-- **(6.1) pointwise, as a bound on `loopMax`**: for `0 < s ≤ t`, every loop of
`G̃ = (H_t - z̃_s)⁻¹` is `(s/t)^{k/2}` times the loop of `G_s` at the same sample point, hence
`max|L̃^{(k)}| ≤ max|L_s^{(k)}|`.  RBM2D `ConArg.lean:456` (`conArg_loopMax_tilde_le`); RBM1D
`gloop_Hflow_ztTilde_eq` (`Gauss/DistEq.lean:249`) and `loopScaling_gauss` (`:268`). -/
private theorem conArg_loopMax_tilde_le {d : ℕ} (sz : Sizes d) (n : ℕ) {E s t : ℝ}
    (h₁ : 0 < s) (h₁₂ : s ≤ t) (ω : sz.SeqΩ) (k : ℕ) :
    Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n t ω)) (ztTilde E s t) k
      ≤ Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n s ω)) (zt E s) k := by
  set r : ℝ := Real.sqrt (t / s) with hr_def
  have hr1 : 1 ≤ r := by
    rw [hr_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((one_le_div h₁).2 h₁₂)
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hmul : r * Real.sqrt s = Real.sqrt t := by
    have hdiv : (0 : ℝ) ≤ t / s := le_of_lt (div_pos (lt_of_lt_of_le h₁ h₁₂) h₁)
    rw [hr_def, ← Real.sqrt_mul hdiv s, div_mul_cancel₀ _ h₁.ne']
  have hH : blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n t ω)
      = (r : ℂ) • blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n s ω) := by
    ext i j
    simp only [blockMat, Matrix.submatrix_apply, Sizes.seqHflow_eq_smul, Matrix.smul_apply,
      smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hmul]
  refine Ind.loopMax_le fun I hσ ha => ?_
  rw [hH, ztTilde, ← hr_def, conArg_loopL_smul_mul hrC, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hle : r⁻¹ ^ (I.σ.zip I.a).length ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
  calc r⁻¹ ^ (I.σ.zip I.a).length * ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n s ω)) (zt E s) I‖
      ≤ 1 * ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n s ω)) (zt E s) I‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n s ω)) (zt E s) I‖ := one_mul _
    _ ≤ _ := Ind.norm_gloop_le_loopMax I hσ ha

/-! ## 3. The base case (5.6) -/

section BaseCase

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `|⟨M E_b⟩| ≤ K` if every diagonal entry of `M` has modulus `≤ K` (`E_b = diag(bw b)` has total
weight `1`, `sum_bw`).  RBM2D `ConArg.lean:505` (`conArg_norm_trace_mul_Eblk_le_of_diag`); RBM1D
`norm_trace_mul_Eblk_le_of_diag` (`ContinuityAssembly.lean:956`). -/
private theorem conArg_norm_trace_mul_Eblk_le_of_diag
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) {K : ℝ}
    (hM : ∀ p, ‖M p p‖ ≤ K) : ‖trace (M * Eblk d L W b)‖ ≤ K := by
  rw [Ind.Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((Ind.bw b p : ℝ) : ℂ)‖ ≤ ∑ p, K * Ind.bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Ind.bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (hM p) (Ind.bw_nonneg b p)
    _ = K := by rw [← Finset.mul_sum, Ind.sum_bw, mul_one]

omit [NeZero W] in
/-- `G(-) = G(+)ᴴ` for Hermitian `H` (copy of the private `gres_false` of `Green/Pins.lean:367`). -/
private theorem conArg_Gres_false {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

/-- **The base case (5.6)**: `|G_{ii}| ≤ K` for all `i` gives `max|L^{(1)}| ≤ K`.  RBM2D
`ConArg.lean:517` (`conArg_loopMax_one_le`); RBM1D `loopMax_one_le`
(`ContinuityAssembly.lean:969`). -/
private theorem conArg_loopMax_one_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) {K : ℝ} (hK : ∀ i, ‖Gres H z true i i‖ ≤ K) :
    Ind.loopMax d L W H z 1 ≤ K := by
  refine Ind.loopMax_le fun I hσ ha => ?_
  obtain ⟨σ, a⟩ := I
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hσ
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp ha
  have e : loopL d L W H z ⟨[s], [b]⟩ = trace (Gres H z s * Eblk d L W b) := by
    simp [loopL]
  rw [e]
  refine conArg_norm_trace_mul_Eblk_le_of_diag _ b fun p => ?_
  cases s
  · rw [conArg_Gres_false hH, conjTranspose_apply, norm_star]
    exact hK p
  · exact hK p

/-- The diagonal of the block-indexed Green function is the diagonal of the fine one: `blockMat` is
a relabelling by the equivalence `splitEquiv` (copy of the private `gres_blockMat_true` of
`Green/Pins.lean:350`). -/
private theorem conArg_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

end BaseCase

/-! ## 4. From the parameter `(σ, a)` to `max_{σ,a}` -/

/-- `‖𝓛^{(k)}_{s,σ,a}‖` is the norm of the list-based loop `loopL` of the block matrix. -/
private theorem conArg_norm_Lloop_eq {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Sizes.Lloop sz n E u σ a ω‖
      = ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n u ω))
          (zt E u) ⟨List.ofFn σ, List.ofFn a⟩‖ := by
  unfold Sizes.Lloop loopFine
  rw [loopM_eq_loopL]
  rfl

/-- `‖𝓛^{(k)}_{u,σ,a}‖ ≤ max_{σ,a}`. -/
private theorem conArg_norm_Lloop_le_loopMax {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖Sizes.Lloop sz n E u σ a ω‖ ≤ Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n u ω)) (zt E u) k := by
  rw [conArg_norm_Lloop_eq]
  exact Ind.norm_gloop_le_loopMax _ (by simp) (by simp)

/-- `#((Fin k → Bool) × (Fin k → Zd d L)) = 2^k L^{dk} ≤ size^{2k}` once `2 ≤ size`. -/
private theorem conArg_card_le {d : ℕ} (sz : Sizes d) (n k : ℕ) (h2 : 2 ≤ sz.size n) :
    (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ)
      ≤ ((sz.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hc : Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      = 2 ^ k * (sz.L n ^ d) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have h1 : sz.L n ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have key : 2 ^ k * (sz.L n ^ d) ^ k ≤ sz.size n ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left h2 k) (Nat.pow_le_pow_left h1 k)
  rw [hc]
  exact_mod_cast key

/-- A per-time bound for all loops of length `k` (parameter `(σ, a)`) is a per-time bound for their
maximum `loopMax` (the union over the `2^k L^{dk}` parameters is taken inside `P` by
`Path.stochDomAt_of_perTimeDomAt`).  RBM2D `ConArg.lean:582` (`conArg_loopMax_perTime`); RBM1D
`stochDom_loopMax_of_loopData` (`ContinuityAssembly.lean:996`). -/
private theorem conArg_loopMax_perTime {d : ℕ} (sz : Sizes d) {E s ζ : ℕ → ℝ} {k : ℕ}
    (hsz : ∀ᶠ n : ℕ in atTop, 2 ≤ sz.size n)
    (h : sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Sizes.Lloop sz n (E n) (s n) p.1 p.2 ω‖) (fun n _ _ => ζ n)) :
    Path.PerTimeDomAt (Sizes.seqP sz) sz.size (U := fun _ => Unit)
      (fun n _ ω => Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n (s n) ω)) (zt (E n) (s n)) k)
      (fun n _ _ => ζ n) := by
  have hU := stochDomAt_of_perTimeDomAt (Sizes.seqP sz) sz.size (C := ((2 * k : ℕ) : ℝ))
    (by positivity) (hsz.mono fun n hn => conArg_card_le sz n k hn) h
  intro τ hτ D hD
  filter_upwards [hU τ hτ D hD] with n hn u
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  unfold Ind.loopMax at hω
  obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hω
  refine ⟨x, ?_⟩
  beta_reduce
  rw [conArg_norm_Lloop_eq]
  exact hx

/-! ## 5. The pin `ConArgPin` and `lem_ConArg` per time -/

/-- `a₁⁻¹ ≤ size`: `W^{-d} B_{s,0} ≥ (W L)^{-d}` for `0 ≤ s < 1` (`B_{s,0} ≥ (L^d |1-s|)⁻¹ ≥ L^{-d}`
as `0 < 1 - s ≤ 1`; the first summand of `B` is `≥ 0`), for every `d`, every coupling `lam` and every
`L`: the scale `a₁` never beats the volume `N = (W L)^d`. -/
private theorem conArg_Bctl_inv_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : (sz.Bctl n s)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hx : 0 < 1 - s := by linarith
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size
    push_cast
    ring
  have hge : (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n s := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx]
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_of_le_one_right (by positivity) (by linarith))
    have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - s))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_left (h1.trans (le_add_of_nonneg_left h2)) (by positivity)
  rw [hsz]
  calc (sz.Bctl n s)⁻¹
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)⁻¹)⁻¹ := inv_anti₀ (by positivity) hge
    _ = _ := inv_inv _

/-- **Pin (`lem_ConArg`, `3_5:42-62`), per time.**  Constants `κ` (bulk), `c` (the time lower bound
`ε₁`), `C₀` (the threshold of `Ω_t`); energy sequence `E`; times `c ≤ s ≤ t < 1` (the paper allows
`t = 1`, where `η_t = 0`: paper-delta T2015b; `c ≤ s` replaces RBM2D's `c < t₁`).  If `(eq:loopbound_s)`
(`3_5:46`, "(55)") holds at `s` for every loop length, `max_{σ,a} |𝓛^{(k)}_{s,σ,a}| ≺ (W^{-d}B_{s,0})^{k-1}`,
then for every `k ≥ 1`, with `Ω_t = {‖G_t‖_max ≤ C₀}` (`STomegaC`),
`1_{Ω_t} max_{σ,a} |𝓛^{(k)}_{t,σ,a}| ≺ ((W^{-d}B_{s,0}) η_s/η_t)^{k-1}` (`(res_lo_bo_eta)`, first
form).  Both `≺` are per time (the union over `(σ, a)` outside `P`: `PrecPT`).  RBM2D `ConArg.lean:61`
(`ConArgPin`). -/
def ConArgPin {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t : ℕ → ℝ) : Prop :=
  0 < κ → (∀ n, |E n| ≤ 2 - κ) → 0 < c → 0 ≤ C₀ → (∀ n, c ≤ s n) → (∀ n, s n ≤ t n) →
    (∀ n, t n < 1) → sz.SizeTendsto →
    (∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖Sizes.Lloop sz n (E n) (s n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n)) ^ (k - 1))) →
    ∀ k : ℕ, 1 ≤ k →
      sz.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => Sizes.STomegaC sz n (E n) (t n) C₀ ω *
          ‖Sizes.Lloop sz n (E n) (t n) p.1 p.2 ω‖)
        (fun n _ _ => (sz.Bctl n (s n) *
          (Gauss.etaT (E n) (s n) / Gauss.etaT (E n) (t n))) ^ (k - 1))

/-- **`lem_ConArg` (`3_5:42-62`), per sequence, per time.**  Proof: RBM1D `lemma_5_1`/`lemma_5_1'`
(`ContinuityAssembly.lean:1032`, `:1163`) as ported in RBM2D `ConArg.lean:613`, with
`a₁ = Bctl_s`, `a = a₁ η_s/η_t`, `K = |z_t - z̃_s|²/(Im z_t Im z̃_s) ≤ C η_s/η_t` (`ztTilde_arith`,
`C = C(ε₁, κ)`), `Y_j = 1_{Ω_t} max|𝓛_t^{(j)}|`, `T_j = max|𝓛̃^{(j)}|`. -/
theorem conArg {d : ℕ} (sz : Sizes d) (κ c C₀ : ℝ) (E s t : ℕ → ℝ) :
    ConArgPin sz κ c C₀ E s t := by
  intro hκ hE hc hC₀ h₁ h₁₂ h₂ hsizeT h55 k hk
  have hsize : Tendsto sz.size atTop atTop := sz.tendsto_size hsizeT
  have hsz2 : ∀ᶠ n : ℕ in atTop, 2 ≤ sz.size n := hsize.eventually (eventually_ge_atTop 2)
  obtain ⟨C, hC0, hC⟩ := ztTilde_arith hc hκ
  have hE2 : ∀ n, |E n| < 2 := fun n => by linarith [hE n]
  have hs0 : ∀ n, 0 < s n := fun n => hc.trans_le (h₁ n)
  have hs1 : ∀ n, s n < 1 := fun n => (h₁₂ n).trans_lt (h₂ n)
  have hηs : ∀ n, 0 < Gauss.etaT (E n) (s n) := fun n => Gauss.etaT_pos (hE2 n) (hs1 n)
  have hηt : ∀ n, 0 < Gauss.etaT (E n) (t n) := fun n => Gauss.etaT_pos (hE2 n) (h₂ n)
  have hηts : ∀ n, Gauss.etaT (E n) (t n) ≤ Gauss.etaT (E n) (s n) := fun n => by
    unfold Gauss.etaT
    exact mul_le_mul_of_nonneg_right (by linarith [h₁₂ n]) (mE_im_pos (hE2 n)).le
  have ha1 : ∀ n, 0 < sz.Bctl n (s n) := fun n => sz.STBctl_pos n (hs1 n)
  -- the deterministic quantities
  set a1 : ℕ → ℝ := fun n => sz.Bctl n (s n) with ha1_def
  set a : ℕ → ℝ := fun n => sz.Bctl n (s n) *
    (Gauss.etaT (E n) (s n) / Gauss.etaT (E n) (t n)) with ha_def
  set zz : ℕ → ℂ := fun n => zt (E n) (t n) with hzz_def
  set zw : ℕ → ℂ := fun n => ztTilde (E n) (s n) (t n) with hzw_def
  set K : ℕ → ℝ := fun n => ‖zz n - zw n‖ ^ 2 * ((zz n).im * (zw n).im)⁻¹ with hK_def
  have hzz : ∀ n, (zz n).im = Gauss.etaT (E n) (t n) := fun n => Gauss.etaT_eq_zt_im.symm
  have harith := fun n => hC (E n) (s n) (t n) (h₁ n) (h₁₂ n) (h₂ n).le (hE n)
  have hzw : ∀ n, Gauss.etaT (E n) (s n) ≤ (zw n).im := fun n => (harith n).2.2.2.1
  have hzw0 : ∀ n, 0 < (zw n).im := fun n => (hηs n).trans_le (hzw n)
  have ha1a : ∀ n, a1 n ≤ a n := fun n => by
    simp only [ha1_def, ha_def]
    exact le_mul_of_one_le_right (ha1 n).le ((one_le_div (hηt n)).2 (hηts n))
  have hK0 : ∀ n, 0 ≤ K n := fun n =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hηt n).le)
      (hzw0 n).le))
  have hK : ∀ n, K n * a1 n ≤ C * a n := by
    intro n
    have hsq := (harith n).2.1
    have hx : ‖zz n - zw n‖ ^ 2 ≤ C * Gauss.etaT (E n) (s n) * (zw n).im := by
      calc ‖zz n - zw n‖ ^ 2 ≤ C * Gauss.etaT (E n) (s n) ^ 2 := hsq
        _ = C * Gauss.etaT (E n) (s n) * Gauss.etaT (E n) (s n) := by ring
        _ ≤ C * Gauss.etaT (E n) (s n) * (zw n).im :=
            mul_le_mul_of_nonneg_left (hzw n) (mul_nonneg hC0.le (hηs n).le)
    have hden : 0 < Gauss.etaT (E n) (t n) * (zw n).im := mul_pos (hηt n) (hzw0 n)
    simp only [hK_def, ha1_def, ha_def, hzz]
    calc ‖zz n - zw n‖ ^ 2 * (Gauss.etaT (E n) (t n) * (zw n).im)⁻¹ * sz.Bctl n (s n)
        ≤ (C * Gauss.etaT (E n) (s n) * (zw n).im) *
            (Gauss.etaT (E n) (t n) * (zw n).im)⁻¹ * sz.Bctl n (s n) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx
            (inv_nonneg.mpr hden.le)) (ha1 n).le
      _ = C * (sz.Bctl n (s n) * (Gauss.etaT (E n) (s n) / Gauss.etaT (E n) (t n))) := by
          have := hηs n; have := hηt n; have := hzw0 n
          field_simp
  have hNev : ∀ᶠ n : ℕ in atTop, (a1 n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    Eventually.of_forall fun n => conArg_Bctl_inv_le sz n (hs0 n).le (hs1 n)
  -- the random families: `Y_j = 1_Ω max|L_t^{(j)}|`, `T_j = max|L̃^{(j)}|`
  have hH : ∀ n u ω, (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n u ω)).IsHermitian :=
    fun n u ω => (Sizes.seqHflow_isHermitian sz n u ω).submatrix _
  set Y : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → sz.SeqΩ → ℝ := fun j n _ ω =>
    Sizes.STomegaC sz n (E n) (t n) C₀ ω *
      Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n (t n) ω)) (zz n) j with hY
  set T : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → sz.SeqΩ → ℝ := fun j n _ ω =>
    Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (Sizes.seqHflow sz n (t n) ω)) (zw n) j with hT
  have hind : ∀ n ω, 0 ≤ Sizes.STomegaC sz n (E n) (t n) C₀ ω := fun n ω => by
    unfold Sizes.STomegaC
    split_ifs <;> norm_num
  have hY0 : ∀ j n u ω, 0 ≤ Y j n u ω := fun j n u ω =>
    mul_nonneg (hind n ω) (Ind.loopMax_nonneg _)
  have hT0 : ∀ j n u ω, 0 ≤ T j n u ω := fun j n u ω => Ind.loopMax_nonneg _
  have hTd : ∀ j, 1 ≤ j → Path.PerTimeDomAt (Sizes.seqP sz) sz.size (T j)
      (fun n _ _ => a1 n ^ (j - 1)) := fun j hj =>
    conArg_of_le_left (fun n _ ω => conArg_loopMax_tilde_le sz n (hs0 n) (h₁₂ n) ω j)
      (conArg_loopMax_perTime sz hsz2 (h55 j hj))
  have hY1 : ∀ n u ω, Y 1 n u ω ≤ C₀ := by
    intro n u ω
    simp only [hY]
    unfold Sizes.STomegaC
    split_ifs with hω
    · rw [one_mul]
      refine conArg_loopMax_one_le (hH n _ ω) fun i => ?_
      rw [conArg_gres_blockMat_true]
      exact hω _ _
    · rw [zero_mul]; exact hC₀
  have hodd : ∀ l, 1 ≤ l → ∀ n u ω,
      Y (2 * l + 1) n u ω ^ 2 ≤ Y (2 * l) n u ω * Y (2 * l + 2) n u ω := by
    intro l hl n u ω
    simp only [hY]
    unfold Sizes.STomegaC
    split_ifs
    · simp only [one_mul]
      exact Ind.loopMax_odd_sq_le (hH n _ ω) hl
    · simp
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ n u ω, Y (2 * m) n u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) n u ω + K n * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) n u ω * T (p * (2 * (m - l) - 1)) n u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp n u ω
    simp only [hY, hT]
    unfold Sizes.STomegaC
    split_ifs with hω
    · simp only [one_mul]
      have hz : 0 < (zz n).im := by rw [hzz]; exact hηt n
      refine (Ind.loopMax_two_mul_le_tilde (hH n _ ω) hz (hzw0 n) hm hp).trans (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (Ind.loopMax_nonneg _)
  have hmain := conArg_continuity_recursion (P := Sizes.seqP sz) hsize hY0 hT0 ha1 ha1a hK0
    hC0.le hC₀ hK hNev hTd hY1 hodd hrec
  -- back to the parameter `(σ, a)`
  intro τ hτ D hD
  filter_upwards [hmain k hk τ hτ D hD] with n hn p
  refine (measure_mono ?_).trans (hn ())
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  refine hω.trans_le ?_
  simp only [hY]
  exact mul_le_mul_of_nonneg_left (conArg_norm_Lloop_le_loopMax sz n (E n) (t n) p.1 p.2 ω)
    (hind n ω)

end RBM.Ind

/-! ## 6. `STConArg d` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Path Filter

/-- **`lem_ConArg` (`3_5:42-62`), the merged pin `STConArg d`, for every `d`.**  From `conArg` at
`E = lemE z`, `c = ε₁`: the hypothesis `STLmax` (`Prec`, union inside `P`) gives the per-time (55) by
`Path.perTimeOfStochDomAt`; the bulk `|lemE z_n| ≤ 2 - κ` is `lemma28_quant` from
`z_n ∈ 𝐃_{κ,ε}`; `SizeTendsto` is the third clause of `Admissible`; the per-time conclusion gives
`Prec` by `Path.stochDomAt_of_perTimeDomAt` (`#((Fin k → Bool) × (Fin k → Zd d L)) ≤ size^{2k}`,
eventually, as `size → ∞`).  The constants `C = C(ε₁, κ)`, `D = D(k, C, C₀)` do not depend on `W`,
`L`, `lam` or `d`. -/
theorem stConArg_holds (d : ℕ) : STConArg d := by
  intro κ ε 𝔡 ε₁ C₀ hκ hε h𝔡 hε₁ hC₀ 𝔠 sz z hflow s t hs hst ht hL k hk
  have hz0 : ∀ n, 0 < (z n).im := fun n =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos (sz.STsize_pos n) _) (hflow.2 n).2.1
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := fun n =>
    (lemma28_quant hκ (hz0 n) (hflow.2 n).2.2 (hflow.2 n).1).1
  have hsizeT : sz.SizeTendsto := hflow.1.2.2.1
  have hcon := RBM.Ind.conArg sz κ ε₁ C₀ (STflowE z) s t hκ hE hε₁ hC₀.le hs hst ht hsizeT
    (fun j hj => Path.perTimeOfStochDomAt (seqP sz) sz.size _ _ (hL j hj)) k (by omega)
  have hsz2 : ∀ᶠ n : ℕ in atTop, 2 ≤ sz.size n :=
    (sz.tendsto_size hsizeT).eventually (eventually_ge_atTop 2)
  exact stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := ((2 * k : ℕ) : ℝ)) (by positivity)
    (hsz2.mono fun n hn => RBM.Ind.conArg_card_le sz n k hn) hcon

end RBM.Gauss.Sizes

/-! ## 7. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10`; `κ = ε = 1/10`; the flow points
`z_n = 1/2 + i N_n^{-4/5}` of `InductionDefsInst` (`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`);
`ε₁ = c = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`.  Every deterministic hypothesis (`STFlow`, the bulk,
the time range, `SizeTendsto`) is discharged; what stays a hypothesis of an instance is the loop bound
`(eq:loopbound_s)` at `s` (the pin `STLmax`, the ST-6 chain). -/

namespace RBM.Ind.ConArgInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Path Filter

/-- The bulk of the flow energies: `|lemE z0_n| ≤ 2 - 1/10` (`lemma28_quant`). -/
private theorem bulk_z0 (n : ℕ) : |STflowE z0 n| ≤ 2 - 1 / 10 :=
  (lemma28_quant (z := z0 n) (κ := 1 / 10) (by norm_num) (z0_im_pos n) (z0_im_le_one n)
    (z0_locDomain n).1).1

/-- **Instance of `conArg`** (`ConArgPin`): `d = 3`, `sz0`, `E = lemE z0`, `κ = 1/10`, `c = 1/16`,
`C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`, all deterministic hypotheses discharged; (55) at `s` is the
hypothesis `h55` (per time; it follows from `STLmax` by `perTimeOfStochDomAt`, below). -/
example (h55 : ∀ k : ℕ, 1 ≤ k →
      sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n)) ^ (k - 1))) :
    ∀ k : ℕ, 1 ≤ k →
      sz0.PrecPT (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) :=
  conArg sz0 (1 / 10) (1 / 16) 2 (STflowE z0) (fun _ => 1 / 16) (fun _ => 1 / 2)
    (by norm_num) bulk_z0 (by norm_num) (by norm_num) (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) sz0_tendsto h55

/-- **Instance of `stConArg_holds`**: `d = 3`, `sz0`, `z0`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`ε₁ = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`; the loop bound `(eq:loopbound_s)` at `s`
(`STLmax`) stays a hypothesis. -/
example (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            Gauss.etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) :=
  fun k hk => stConArg_holds 3 (1 / 10) (1 / 10) (1 / 10) (1 / 16) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 (fun _ => 1 / 16)
    (fun _ => 1 / 2) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num) hL k hk

end RBM.Ind.ConArgInst

end
