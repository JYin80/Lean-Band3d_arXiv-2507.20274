/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLWardIneq
import RBM3D.Loop.KBound
import RBM3D.Propagator.Prop6Hold
import RBM3D.Induction.Step34Pins
import RBM3D.Defs.StochDomAt

/-!
# KL14a: the `K`-loop bounds without the propagator hypothesis, and at the sequence level

Ticket T2125.  The gate PT proved the properties 5-8 of `lem_propTH` (`prop5to8_holds`), the gate KL
proved `ML:Kbound` and `lem_wardineq_K` conditional on the local shapes `KLPT d κ gmax`
(`KLboundPin_holds`, `KLwardIneqPin_holds`).  This file composes them.

## Contents

* `RBM.Loop.KLPT_holds` : `KLPT d κ gmax` for `3 ≤ d`, `0 < κ`, `0 < gmax`, from `prop5Decay_holds`,
  `prop5Short_holds`, `prop6Diff1_holds`, `prop7Diff2_holds`, `prop8ZeroMode_holds`.  The bridge
  for the five fields: `(+,-)` is `m = I` (`PropSpin I true * PropSpin I false = 1`), `KLShort` is
  the pin at `m = mE E` with `κ' = min κ 1 / 2 ≤ Im m(E)` on `|E| ≤ 2 - κ`, the `L^τ` of `KLDiffOne`,
  `KLDiffTwo`, `KLZero` is absorbed since `1 ≤ L^τ`.
* `RBM.Loop.KLbound_holds`, `RBM.Loop.KLwardIneq_holds` : `ML:Kbound` and `lem_wardineq_K` with no
  propagator hypothesis; `RBM.Loop.KLoopBound_KLK` : the owed `KLoopBound` for `K = KLK` at a fixed
  `(d, L, W, g, E)`.
* `RBM.Gauss.Sizes.L_rpow_le` : `L^τ ≤ N^{τ/d}` for `N = (W L)^d` (the `L`-version of
  `Sizes.W_rpow_le`; uses only `W ≥ 1`).
* `RBM.Gauss.Sizes.stKbound_holds`, `stKward_holds` : the sequence-level pins `STKbound`, `STKward`
  (`Induction/Defs.lean:174`, `Induction/Step34Pins.lean:224`) for every energy sequence with
  `|E n| ≤ 2 - κ`, `0 < lam n ≤ gmax` eventually and `N → ∞`; `stKbound_of_flow`, `stKward_of_flow`
  : the same from `STFlow sz κ ε 𝔠 𝔡 z` (the setting of the consumers) with `E = STflowE z`.

## The conditional form of `STKbound`, `STKward` (not an edit of the pins)

The pin `STKbound sz E` for arbitrary `(sz, E)` is false: `KLFinal_not_stKbound` (compiled below) is the
constant size sequence `L ≡ 3`, `W ≡ 1`, `lam ≡ 1/2` (`N ≡ 27`, so `N` does not tend to infinity) with
`E ≡ 0`, for which `STKbound` fails at `k = 2`.  So the proved form carries `N → ∞`
(`SizeTendsto`), and the parameter ranges `|E n| ≤ 2 - κ`, `0 < lam n ≤ gmax` (eventually) of the
`K`-loop pins (`KLPar`).  `STFlow sz κ ε 𝔠 𝔡 z` supplies all three for `E = STflowE z`
(`stKbound_of_flow`, `stKward_of_flow`, `gmax = 𝔡⁻¹`).  No claim is made that the bulk and `lam`
conditions are necessary.
-/

open Filter

namespace RBM.Loop

open RBM

/-! ## 1. `KLPT_holds` -/

section Bridge

private theorem KLFinal_PropSpin_I : PropSpin Complex.I true * PropSpin Complex.I false = 1 := by
  simp [PropSpin]

private theorem KLFinal_one_le_rpow {L : ℕ} (hL : 3 ≤ L) {τ : ℝ} (hτ : 0 < τ) :
    (1 : ℝ) ≤ (L : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) hτ.le

/-- `κ' = min κ 1 / 2 ≤ Im m(E)` on the bulk `|E| ≤ 2 - κ`. -/
private theorem KLFinal_mE_im_ge {κ E : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) :
    min κ 1 / 2 ≤ (mE E).im := by
  rw [mE_im]
  have hκ2 : κ ≤ 2 := by have := abs_nonneg E; linarith
  have hE2 : E ^ 2 ≤ (2 - κ) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg E) hE 2
    rwa [sq_abs] at h
  have h1 : min κ 1 ≤ κ := min_le_left _ _
  have h2 : min κ 1 ≤ 1 := min_le_right _ _
  have h0 : 0 ≤ min κ 1 := le_min hκ.le one_pos.le
  have hμ : (min κ 1) ^ 2 ≤ 4 - E ^ 2 := by
    have h3 : min κ 1 * min κ 1 ≤ κ * 1 := mul_le_mul h1 h2 h0 hκ.le
    nlinarith
  have := le_trans (le_abs_self _) (Real.abs_le_sqrt hμ)
  linarith

private theorem KLFinal_decay {d : ℕ} {gmax : ℝ} (hd : 3 ≤ d) (hg : 0 < gmax) :
    KLDecay d gmax := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Decay_holds d gmax hd hg
  refine ⟨C, hC, c, hc, fun L hL g hg0 hg1 t ht0 ht1 a => ?_⟩
  have h := H L hL g hg0 hg1 t ht0 ht1 Complex.I (by simp) true false a
  rw [KLFinal_PropSpin_I, mul_one] at h
  exact h

private theorem KLFinal_short {d : ℕ} {κ gmax : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
    KLShort d κ gmax := by
  obtain ⟨C, hC, c, hc, H⟩ := prop5Short_holds d gmax (min κ 1 / 2) hd hg
    (by have := lt_min hκ one_pos; linarith)
  refine ⟨C, hC, c, hc, fun L hL g hg0 hg1 E hE s t ht0 ht1 a => ?_⟩
  have hE2 : |E| ≤ 2 := by linarith
  exact H L hL g hg0 hg1 t ht0 ht1 (mE E) (norm_mE hE2) (KLFinal_mE_im_ge hκ hE) s a

private theorem KLFinal_diffOne {d : ℕ} {gmax : ℝ} (hd : 3 ≤ d) (hg : 0 < gmax) :
    KLDiffOne d gmax := by
  intro c hc0 hc1 τ hτ
  obtain ⟨C, hC, H⟩ := prop6Diff1_holds d gmax 1 c hd hg one_pos hc0 hc1
  refine ⟨C, hC, fun L hL g hg0 hg1 t ht0 ht1 a r hr => ?_⟩
  have h := H L hL g hg0 hg1 t ht0 ht1 Complex.I (by simp) (by simp) true false a r hr
  rw [KLFinal_PropSpin_I, mul_one] at h
  refine h.trans ?_
  have hnn : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) *
      (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹ := by positivity
  have h1 := KLFinal_one_le_rpow hL hτ
  have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le h1) hnn
  linarith

private theorem KLFinal_diffTwo {d : ℕ} {gmax : ℝ} (hd : 3 ≤ d) (hg : 0 < gmax) :
    KLDiffTwo d gmax := by
  intro c hc0 hc1 τ hτ
  obtain ⟨C, hC, H⟩ := prop7Diff2_holds d gmax 1 c hd hg one_pos hc0 hc1
  refine ⟨C, hC, fun L hL g hg0 hg1 t ht0 ht1 a r hr => ?_⟩
  have h := H L hL g hg0 hg1 t ht0 ht1 Complex.I (by simp) (by simp) true false a r hr
  rw [KLFinal_PropSpin_I, mul_one] at h
  refine h.trans ?_
  have hnn : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 *
      (((zdistD d L a : ℝ) + 1) ^ d)⁻¹ := by positivity
  have h1 := KLFinal_one_le_rpow hL hτ
  have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le h1) hnn
  linarith

private theorem KLFinal_zero {d : ℕ} {gmax : ℝ} (hd : 3 ≤ d) (hg : 0 < gmax) :
    KLZero d gmax := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := prop8ZeroMode_holds d gmax 1 hd hg one_pos
  refine ⟨C, hC, fun L hL g hg0 hg1 t ht0 ht1 a => ?_⟩
  have h := H L hL g hg0 hg1 t ht0 ht1 Complex.I (by simp) (by simp) true false a
  rw [KLFinal_PropSpin_I, mul_one] at h
  refine h.trans ?_
  have hnn : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have h1 := KLFinal_one_le_rpow hL hτ
  have := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le h1) hnn
  linarith

/-- **`KLPT d κ gmax` is proved** for `3 ≤ d`, `0 < κ`, `0 < gmax`: the five local propagator shapes
of the `K`-loop layer follow from the properties 5-8 of `lem_propTH` (`prop5to8_holds`).  The
constants depend on `(d, gmax)` (`KLDecay`), `(d, gmax, κ)` (`KLShort`), `(d, gmax, c, τ)`
(`KLDiffOne/Two`, `KLZero`), through `κ' = min κ 1 / 2` in the pin 5s and `κ'' = 1` (`m = I`) in
the pins 6, 7, 8. -/
theorem KLPT_holds {d : ℕ} {κ gmax : ℝ} (hd : 3 ≤ d) (hκ : 0 < κ) (hg : 0 < gmax) :
    KLPT d κ gmax :=
  ⟨KLFinal_decay hd hg, KLFinal_short hd hκ hg, KLFinal_diffOne hd hg, KLFinal_diffTwo hd hg,
    KLFinal_zero hd hg⟩

end Bridge

/-! ## 2. The unconditional `K`-loop bounds -/

/-- **`ML:Kbound`, `(eq:bcal_k)`, with no hypothesis beyond the parameter ranges**: `KLBoundAt d n κ gmax`
for every `n ≥ 1`. -/
theorem KLbound_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax →
    KLBoundAt d n κ gmax :=
  fun d n κ gmax hd hn hκ hg => KLboundPin_holds d n κ gmax hd hn hκ hg (KLPT_holds hd hκ hg)

/-- **`lem_wardineq_K`, `(wardineq_K)`, with no hypothesis beyond the parameter ranges**:
`KLwardIneqAt d n κ gmax` for every `n ≥ 2`. -/
theorem KLwardIneq_holds : ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 2 ≤ n → 0 < κ → 0 < gmax →
    KLwardIneqAt d n κ gmax :=
  fun d n κ gmax hd hn hκ hg => KLwardIneqPin_holds d n κ gmax hd hn hκ hg (KLPT_holds hd hκ hg)

/-- **`KLoopBound` (`Loop/KBound.lean:74`) for the `K`-loops `K t = 𝒦_t` (`KLK`)** at a fixed
`(d, L, W, g, E)` with `3 ≤ d`, `3 ≤ L`, `1 ≤ W`, `0 < g`, `|E| < 2`: the bridge from `KLBoundAt`
(`κ = 2 - |E|`, `gmax = g`) to lists.  This is the statement for the one family `KLK`, not the
premise `KLoopBound` for an arbitrary `K`. -/
theorem KLoopBound_KLK {d L W : ℕ} [NeZero L] {g E : ℝ} (hd : 3 ≤ d) (hL : 3 ≤ L) (hW : 1 ≤ W)
    (hg : 0 < g) (hE : |E| < 2) : KLoopBound d L W g (fun t => KLK d L g W E t) := by
  intro n hn τ hτ
  obtain ⟨C, hC, H⟩ := KLbound_holds d n (2 - |E|) g hd hn (by linarith) hg τ hτ
  refine ⟨C, hC, fun t ht0 ht1 σ a hσ ha => ?_⟩
  subst hσ
  let p : KLPar (2 - |E|) g := ⟨L, W, hL, hW, g, hg, le_rfl, E, le_of_eq (by ring), t, ht0, ht1⟩
  have h := H p σ.get (fun i => a.get (Fin.cast ha.symm i))
  have hσ' : List.ofFn σ.get = σ := List.ofFn_get σ
  have ha' : List.ofFn (fun i : Fin σ.length => a.get (Fin.cast ha.symm i)) = a := by
    apply List.ext_getElem <;> simp [ha]
  simp only [KLloopOf, hσ', ha'] at h
  exact h

end RBM.Loop

/-! ## 3. The scale: `L^τ ≤ N^{τ/d}` and the loss of a pin as a `≺` -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss MeasureTheory

variable {d : ℕ} (sz : Sizes d)

/-- `L^τ ≤ N^{τ/d}` for `N = (W L)^d` (`τ ≥ 0`, `d ≥ 1`): the `L`-version of `Sizes.W_rpow_le`; it
uses only `W ≥ 1` (a field of `Sizes`), neither `Bandwidth` nor `L^d ≤ W^K`. -/
theorem L_rpow_le (hd : 0 < d) (n : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((sz.L n : ℕ) : ℝ) ^ τ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / d) := by
  have hL : (0 : ℝ) ≤ sz.L n := Nat.cast_nonneg _
  have hW : 0 < sz.W n := sz.W_pos n
  have hle : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ hW) d
    exact_mod_cast h
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc ((sz.L n : ℕ) : ℝ) ^ τ = (((sz.L n : ℕ) : ℝ) ^ (d : ℝ)) ^ (τ / d) := by
        rw [← Real.rpow_mul hL]; congr 1; field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / d) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        rwa [Real.rpow_natCast]

/-- A loss `C L^s` (every `s > 0`, constant `C` fixed before `n`) is a `≺` at the scale `N`: if
`ξ ≤ C L^s ζ` eventually in `n`, for every `s > 0` with some `C > 0`, and `ζ ≥ 0`, then
`sz.Prec ξ ζ`.  Uses `N → ∞` (`C ≤ N^{τ/2}` eventually) and `L^s ≤ N^{s/d}`. -/
private theorem KLFinal_prec_of_loss (hd : 0 < d) (hN : sz.SizeTendsto) {U : ℕ → Type*}
    {ξ ζ : ∀ n, U n → SeqΩ sz → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (H : ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ u ω,
      ξ n u ω ≤ C * ((sz.L n : ℕ) : ℝ) ^ s * ζ n u ω) :
    sz.Prec ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C, hC, hH⟩ := H (d * (τ / 2)) (by positivity)
  have hlarge : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hN).eventually_ge_atTop C
  filter_upwards [hH, hlarge] with n hn hCn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  have hNn : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLN := sz.L_rpow_le hd n (by positivity : 0 ≤ d * (τ / 2))
  rw [show d * (τ / 2) / (d : ℝ) = τ / 2 by field_simp] at hLN
  calc ξ n u ω ≤ C * ((sz.L n : ℕ) : ℝ) ^ (d * (τ / 2)) * ζ n u ω := hn u ω
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n u ω := by
        refine mul_le_mul_of_nonneg_right ?_ (hζ n u ω)
        exact mul_le_mul hCn hLN (by positivity) (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
        rw [← Real.rpow_add' hNn (by linarith), add_halves]

/-! ## 4. `STKbound`, `STKward` -/

/-- **`STKbound sz E` (`ML:Kbound` at the sequence level, `Induction/Defs.lean:174`)** under the
hypotheses its consumers can supply: `3 ≤ d`, `N → ∞` (`SizeTendsto`), `|E n| ≤ 2 - κ` and
`0 < lam n ≤ gmax` eventually in `n`.  The pin as stated (no condition on `sz`, `E`) is false (module
docstring), so this is the conditional form; `stKbound_of_flow` derives the three conditions from
`STFlow`.  The constant of `KLBoundAt` depends on `(d, k, κ, gmax, τ)` only. -/
theorem stKbound_holds (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) : STKbound sz E := by
  intro τ hτ0 hτ1 k hk
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n =>
    mul_nonneg (by positivity) (KLIndStepA_Bparam_nonneg _ _)
  refine KLFinal_prec_of_loss sz (by omega) hN (fun n u ω => pow_nonneg (hB n) _) ?_
  intro s hs
  obtain ⟨C, hC, H⟩ := KLbound_holds d k κ gmax hd hk hκ hg s hs
  refine ⟨C, hC, ?_⟩
  filter_upwards [hE, hlam] with n hEn hlamn
  intro u ω
  exact H ⟨sz.L n, sz.W n, sz.three_le_L n, sz.W_pos n, sz.lam n, hlamn.1, hlamn.2, E n, hEn,
    τ n, hτ0 n, hτ1 n⟩ u.1 u.2

/-- **`STKward sz E` (`lem_wardineq_K` at the sequence level, `Induction/Step34Pins.lean:224`)**, same
hypotheses as `stKbound_holds` (same reason for the conditional form). -/
theorem stKward_holds (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) : STKward sz E := by
  intro τ hτ0 hτ1 k hk
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n =>
    mul_nonneg (by positivity) (KLIndStepA_Bparam_nonneg _ _)
  have hη : ∀ n, 0 ≤ etaT (E n) (τ n) := fun n => by
    unfold etaT
    exact mul_nonneg (by linarith [hτ1 n]) (by rw [mE_im]; positivity)
  refine KLFinal_prec_of_loss sz (by omega) hN
    (fun n u ω => mul_nonneg (inv_nonneg.2 (mul_nonneg (by positivity) (hη n)))
      (pow_nonneg (hB n) _)) ?_
  intro s hs
  obtain ⟨C, hC, H⟩ := KLwardIneq_holds d k κ gmax hd hk hκ hg s hs
  refine ⟨C, hC, ?_⟩
  filter_upwards [hE, hlam] with n hEn hlamn
  intro u ω
  have h := H ⟨sz.L n, sz.W n, sz.three_le_L n, sz.W_pos n, sz.lam n, hlamn.1, hlamn.2, E n, hEn,
    τ n, hτ0 n, hτ1 n⟩ u.1 u.2
  rw [mul_assoc (C * ((sz.L n : ℕ) : ℝ) ^ s)] at h
  exact h

/-! ### The flow form: `STFlow` supplies the three conditions -/

/-- The flow energies lie in the bulk: `|lemE (z n)| ≤ |Re z_n| ≤ 2 - κ` (`abs_lemE_le`, `Im z_n > 0`
from `N^{-1+ε} ≤ Im z_n`). -/
private theorem KLFinal_flowE {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    |STflowE z n| ≤ 2 - κ := by
  have h := hz.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h.2.1
  exact (abs_lemE_le him).trans h.1

/-- `(eq:WO)` gives `0 < lam n ≤ 𝔡⁻¹` eventually. -/
private theorem KLFinal_flowLam {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- **`STKbound sz (STflowE z)` from `STFlow`** (`3 ≤ d`, `0 < κ`): no hypothesis left; `gmax = 𝔡⁻¹`.
This is what the consumers of `STKbound` (`STStep3R`, `STStep1`, ...) have at hand. -/
theorem stKbound_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) : STKbound sz (STflowE z) :=
  stKbound_holds sz hd hκ (inv_pos.2 hz.1.2.1) hz.1.2.2.1
    (Eventually.of_forall (KLFinal_flowE sz hz)) (KLFinal_flowLam sz hz)

/-- **`STKward sz (STflowE z)` from `STFlow`** (`3 ≤ d`, `0 < κ`): no hypothesis left. -/
theorem stKward_of_flow (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hz : STFlow sz κ ε 𝔠 𝔡 z) : STKward sz (STflowE z) :=
  stKward_holds sz hd hκ (inv_pos.2 hz.1.2.1) hz.1.2.2.1
    (Eventually.of_forall (KLFinal_flowE sz hz)) (KLFinal_flowLam sz hz)

/-! ### `N → ∞` cannot be dropped: the pin `STKbound sz E` as stated is false

The constant size sequence `L ≡ 3`, `W ≡ 1`, `lam ≡ 1/2` (`N ≡ 27`) with the bulk energy `E ≡ 0`
satisfies every other hypothesis of `stKbound_holds` (`|E| ≤ 2 - 1`, `0 < lam ≤ 1`), yet `STKbound`
fails: at `k = 2`, `τ ≡ 0`, the loop `(+,-)` at `(a,a)` has `𝒦^{(2)} = 1` (`W^{-d} m(+) m(-)
Θ_0(a,a)`), while `W^{-d} B_{0,0} = 113/135`, and `27^{1/100} · 113/135 < 1`, so the bad event of
`Prec` is the whole space (probability `1 > 27^{-1}`). -/

noncomputable def KLFinal_szConst : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 1
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => one_pos

theorem KLFinal_szConst_size (n : ℕ) : KLFinal_szConst.size n = 27 := by
  simp [Sizes.size, KLFinal_szConst]

private theorem KLFinal_mSigma_mul (E : ℝ) (hE : |E| ≤ 2) :
    mSigma E true * mSigma E false = 1 := by
  have h : mSigma E true * mSigma E false = mE E * (starRingEnd ℂ) (mE E) := by
    simp [mSigma]
  rw [h, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mE hE]
  norm_num

private theorem KLFinal_Theta_zero (g : ℝ) : Theta 3 3 g (0 : ℂ) 0 0 = 1 := by
  simp [Theta]

theorem KLFinal_not_stKbound : ¬ STKbound KLFinal_szConst (fun _ => 0) := by
  intro h
  have hP := h (fun _ => 0) (fun _ => le_rfl) (fun _ => zero_lt_one) 2 (by norm_num)
    (1 / 100) (by norm_num) 1 one_pos
  obtain ⟨n, hn⟩ := hP.exists
  have hsz := KLFinal_szConst_size n
  have hnorm : ‖STKloop KLFinal_szConst n 0 0 ![true, false] ![0, 0]‖ = 1 := by
    have e : STKloop KLFinal_szConst n 0 0 ![true, false] ![0, 0]
        = KLK 3 3 (1 / 2) 1 0 0 ⟨[true, false], [0, 0]⟩ := by
      simp [STKloop, KLloopOf, KLFinal_szConst, List.ofFn_succ]
      rfl
    rw [e, KLK_two, KLFinal_mSigma_mul 0 (by norm_num)]
    simp [KLFinal_Theta_zero]
  have hB : KLFinal_szConst.Bctl n 0 = 113 / 135 := by
    simp only [Sizes.Bctl, Bparam, KLFinal_szConst]
    norm_num
  have hrpow : ((27 : ℕ) : ℝ) ^ (1 / 100 : ℝ) < 135 / 113 := by
    have h1 : ((27 : ℕ) : ℝ) < (135 / 113 : ℝ) ^ (100 : ℕ) := by norm_num
    have h2 := Real.rpow_lt_rpow (by positivity) h1 (by norm_num : (0 : ℝ) < 1 / 100)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
    norm_num at h2
    simpa using h2
  have huniv : badSetAt KLFinal_szConst.size
      (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (KLFinal_szConst.L n)))
        (_ : SeqΩ KLFinal_szConst) => ‖STKloop KLFinal_szConst n 0 0 p.1 p.2‖)
      (fun n (_ : (Fin 2 → Bool) × (Fin 2 → Zd 3 (KLFinal_szConst.L n)))
        (_ : SeqΩ KLFinal_szConst) => (KLFinal_szConst.Bctl n 0) ^ (2 - 1)) (1 / 100) n
      = (Set.univ : Set (SeqΩ KLFinal_szConst)) := by
    ext ω
    simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    refine ⟨(![true, false], ![0, 0]), ?_⟩
    simp only [Nat.add_one_sub_one, pow_one]
    rw [hsz, hB, hnorm]
    calc ((27 : ℕ) : ℝ) ^ (1 / 100 : ℝ) * (113 / 135) < 135 / 113 * (113 / 135) :=
          mul_lt_mul_of_pos_right hrpow (by norm_num)
      _ = 1 := by norm_num
  rw [huniv, measure_univ, hsz] at hn
  have : ENNReal.ofReal (((27 : ℕ) : ℝ) ^ (-1 : ℝ)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    norm_num
  exact absurd hn (not_le.2 this)

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instances at `d = 3`

`KLPT_holds`, `KLbound_holds`, `KLwardIneq_holds`, `KLoopBound_KLK`: the probe point `KLinstPar`
(`L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`, `κ = gmax = 1`), no hypothesis left.
`L_rpow_le`, `stKbound_holds`, `stKward_holds` and the flow forms: the merged size sequence `sz0`
(`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) with the flow `z0`
(`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, `z0_n = 1/2 + i N_n^{-4/5}`, so
`|lemE z0_n| ≤ |Re z0_n| = 1/2`); every hypothesis is discharged. -/

namespace RBM.Loop

section Instances

/-- Target 1 at `d = 3`, `κ = 1/10`, `gmax = 1`: no hypothesis left. -/
example : KLPT 3 (1 / 10) 1 := KLPT_holds (by norm_num) (by norm_num) one_pos

/-- The five fields of `KLPT_holds` applied at the probe data `L = 5`, `g = 1/2 ≤ gmax = 1`,
`t = 9/10`, `E = 0` (`|E| ≤ 2 - 1/10`): the decay (`a = (1,1,1)`), the short-range bound (`a = 0`),
the two differences (`a = (2,2,2)`, `r = (1,1,1)`, `|r| = 3 ≤ (1/2)·6 = (1/2)|a|`) and the zero mode
(`a = (1,1,1)`). -/
example :
    (∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ),
      ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 1)‖
        ≤ Cd * Bparam 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (KLinsta 1))
            * Real.exp (-cd * (zdistD 3 5 (KLinsta 1) : ℝ) / ellT 5 (1 / 2) (9 / 10))) ∧
    (∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ),
      ‖Theta 3 5 (1 / 2) ((((9 / 10 : ℝ)) : ℂ) * (mSigma 0 true * mSigma 0 true)) 0 0‖
        ≤ Cκ * ((if (0 : Zd 3 5) = 0 then (1 : ℝ) else 0)
            + (1 / 2 : ℝ) ^ 2 * Real.exp (-cκ * (zdistD 3 5 (0 : Zd 3 5) : ℝ)))) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 2 + KLinsta 1)
          - Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 2)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
            * (zdistD 3 5 (KLinsta 1) : ℝ) * (((zdistD 3 5 (KLinsta 2) : ℝ) + 1) ^ (3 - 1))⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 2 + KLinsta 1)
          + Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 2 - KLinsta 1)
          - 2 * Theta 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 2)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
            * (zdistD 3 5 (KLinsta 1) : ℝ) ^ 2 * (((zdistD 3 5 (KLinsta 2) : ℝ) + 1) ^ 3)⁻¹) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖Theta0 3 5 (1 / 2) (((9 / 10 : ℝ)) : ℂ) 0 (KLinsta 1)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)⁻¹
            * (((zdistD 3 5 (KLinsta 1) : ℝ) + 1) ^ (3 - 2))⁻¹) := by
  have hPT := KLPT_holds (d := 3) (κ := 1 / 10) (gmax := 1) (by norm_num) (by norm_num) one_pos
  have h3 : zdistD 3 5 (KLinsta 1) = 3 := by decide
  have h6 : zdistD 3 5 (KLinsta 2) = 6 := by decide
  have hr : (zdistD 3 5 (KLinsta 1) : ℝ) ≤ 1 / 2 * (zdistD 3 5 (KLinsta 2) : ℝ) := by
    rw [h3, h6]; norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Cd, hCd, cd, hcd, H⟩ := hPT.decay
    exact ⟨Cd, hCd, cd, hcd, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10)
      (by norm_num) (by norm_num) (KLinsta 1)⟩
  · obtain ⟨Cκ, hCκ, cκ, hcκ, H⟩ := hPT.short
    exact ⟨Cκ, hCκ, cκ, hcκ, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 0
      (by norm_num) true (9 / 10) (by norm_num) (by norm_num) 0⟩
  · obtain ⟨C, hC, H⟩ := hPT.diffOne (1 / 2) (by norm_num) (by norm_num) 1 one_pos
    exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
      (by norm_num) (KLinsta 2) (KLinsta 1) hr⟩
  · obtain ⟨C, hC, H⟩ := hPT.diffTwo (1 / 2) (by norm_num) (by norm_num) 1 one_pos
    exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
      (by norm_num) (KLinsta 2) (KLinsta 1) hr⟩
  · obtain ⟨C, hC, H⟩ := hPT.zeroMode 1 one_pos
    exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
      (by norm_num) (KLinsta 1)⟩

/-- Target 2, `KLbound_holds` at `n = 4`, every `τ > 0`, at the probe's `KLinstPar` data and the loop
`(+,+,-,-)` with spread labels: no hypothesis left (`KLPT 3 1 1` is `KLPT_holds`). -/
example (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLInduct_instσ KLInduct_insta)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ τ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := KLbound_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos τ hτ
  exact ⟨C, hC, H KLinstPar KLInduct_instσ KLInduct_insta⟩

/-- Target 2, `KLwardIneq_holds` at `n = 4`, every `τ > 0`: the sum over the last label. -/
example (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧
      ∑ x : Zd 3 5, ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLInduct_instσ,
            List.ofFn ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2] ++ [x]⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ τ * ((((2 : ℕ) : ℝ) ^ 3) * Gauss.etaT 0 (9 / 10))⁻¹ *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 2) := by
  obtain ⟨C, hC, H⟩ := KLwardIneq_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos τ hτ
  exact ⟨C, hC, H KLinstPar KLInduct_instσ
    ![KLInduct_insta 0, KLInduct_insta 1, KLInduct_insta 2]⟩

/-- Target 2, `KLoopBound_KLK` at `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`; applied at `n = 4`,
`τ = 1`, `t = 9/10` and the lists of the loop `(+,+,-,-)` with spread labels. -/
example :
    KLoopBound 3 5 2 (1 / 2) (fun t => KLK 3 5 (1 / 2) 2 0 t) :=
  KLoopBound_KLK (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    ∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10)
          ⟨List.ofFn KLInduct_instσ, List.ofFn KLInduct_insta⟩‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := KLoopBound_KLK (d := 3) (L := 5) (W := 2) (g := 1 / 2) (E := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 4 (by norm_num) 1 one_pos
  exact ⟨C, hC, H (9 / 10) (by norm_num) (by norm_num) _ _ (by simp) (by simp)⟩

end Instances

end RBM.Loop

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Gauss RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- `L_rpow_le` at `sz0`: `L_n^{3/2} ≤ N_n^{1/2}` for every `n`. -/
example (n : ℕ) :
    ((sz0.L n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ ((3 / 2 : ℝ) / (3 : ℕ)) :=
  sz0.L_rpow_le (by norm_num) n (by norm_num)

/-- Target 3, `stKbound_holds` at the merged `sz0` flow data, in the minimal form: `N → ∞`
(`sz0_tendsto`), `|E_n| = |lemE z0_n| ≤ 2 - 1/10` (`abs_lemE_le`, `z0_locDomain`), and
`0 < lam_n = (2(n+1))^{-6} ≤ 1`: every hypothesis discharged. -/
example : STKbound sz0 (STflowE z0) := by
  refine stKbound_holds sz0 (by norm_num) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos
    sz0_tendsto (Eventually.of_forall fun n => (abs_lemE_le (z0_im_pos n)).trans
      (z0_locDomain n).1) (Eventually.of_forall fun n => ?_)
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hlam]
  exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hx1)⟩

/-- Target 4, `stKward_holds` at the same data. -/
example : STKward sz0 (STflowE z0) := by
  refine stKward_holds sz0 (by norm_num) (κ := 1 / 10) (gmax := 1) (by norm_num) one_pos
    sz0_tendsto (Eventually.of_forall fun n => (abs_lemE_le (z0_im_pos n)).trans
      (z0_locDomain n).1) (Eventually.of_forall fun n => ?_)
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hlam]
  exact ⟨by positivity, inv_le_one_of_one_le₀ (one_le_pow₀ hx1)⟩

/-- The flow forms at `flow_z0`: the pins `STKbound`, `STKward` of the consumers hold at the flow
data with no hypothesis (`gmax = 𝔡⁻¹ = 10`). -/
example : STKbound sz0 (STflowE z0) ∧ STKward sz0 (STflowE z0) :=
  ⟨stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0,
    stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0⟩

/-- `STKbound` read at the time sequence `τ_n ≡ 1/2` and `k = 3`: `max |𝒦^{(3)}| ≺ (W^{-d}B_{τ,0})²`
at the scale `N_n`, the statement of the pin at concrete nondegenerate data. -/
example :
    Prec sz0 (U := fun n => (Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n)))
      (fun n p _ => ‖STKloop sz0 n (STflowE z0 n) (1 / 2) p.1 p.2‖)
      (fun n _ _ => (sz0.Bctl n (1 / 2)) ^ (3 - 1)) :=
  stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun _ => by norm_num) 3 (by norm_num)

end RBM.Gauss.Sizes
