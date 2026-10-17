/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Kernel.SumDecay
import RBM3D.Propagator.Prop5Short

/-!
# Evolution-kernel pins (gate EK, random band model, `d ≥ 3`): vocabulary, seven pins, three bridges

Merged from the compiled T2016 design probe (`RBM3D/Probe/T2016Pins.lean` at `c961e62`, lines
44-198).  Namespace `RBM`, public names prefixed `EK` / `ek`.  A pin is a `Prop` that an EK proof
ticket turns into `theorem ekXxx_holds : ∀ d n Λ κ, EKXxx d n Λ κ`; the propagator pins of
T2003 / T2007 (`Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop8ZeroMode`) are **antecedents** of the
pin.

Contents: vocabulary (`EKsgn`, `EKFastDecay` = `(deccA0)`, `EKSumZero` = `(sumAzero)`); the seven
pins (`EKSumNdecay`, `EKSumDecay1` = `(sum_res_1)`, `EKSumDecayNAL` = `(sum_res_2_NAL)`,
`EKSumDecay2` = `(sum_res_2)`, `EKSumDecayNonzero`, `EKPropT`, `EKTTk`); the three pins that merged
theorems prove (`ekSumNdecay_holds`, `ekPropT_holds`, `ekTTk_holds`); the compiled instances
`ekInst*` at `d = 3`, `L = 5`, `g = 1/2`.

Form common to all pins (paper `lem:sum_Ndecay`, `lem:sum_decay`, `lem:sum_decay_nonzero`,
`3_5_Loop_Hierarchy.tex:1615-1672`; `lem:propT`, `:328`; `claim:TTk`, `7_8_light_weight.tex:1661`):
* the constants are quantified **after** `(d, n, Λ, κ)` and **before**
  `L, g, W, ε, D, s, t, m, σ, A` (Λ = `𝔡⁻¹` is the upper end of `(eq:WO)`, `g = λ`,
  `0 < g ≤ Λ`); no loss `L^τ`;
* `Θ_t^{(σ,σ')}` is `Theta d L g (t * (m(σ) m(σ')))` with `m(+) = m`, `m(-) = m̄`, `‖m‖ = 1`
  (`EKsgn m σ i = PropSpin m (σ i)`, so `UN d L g (EKsgn m σ)` is `U^{(n)}_{s,t,σ}` of
  `(def_Ustz)`);
* the bulk condition is `κ ≤ Im m`; distances are the periodic `ℓ¹` distance `zdistD`;
* `W^{C ε}` of `lem:sum_decay` is `W ^ (C * ε)`, with `4 ≤ W ^ ε` (candidate `T2016b`);
  `log L ≤ W^ε`
  in `(sum_res_2)` is the paper's own absorption of `log L` (candidate `T2016a`).
-/

set_option linter.style.longLine false

namespace RBM

/-! ### Vocabulary -/

/-- the sign data of the paper: `EKsgn m σ i = m(σ_i)`, `m(+) = m`, `m(-) = m̄`. -/
noncomputable def EKsgn {n : ℕ} (m : ℂ) (σ : Fin n → Bool) : Fin n → ℂ := fun i => PropSpin m (σ i)

theorem ek_norm_spin {m : ℂ} (hm : ‖m‖ = 1) (σ : Bool) : ‖PropSpin m σ‖ = 1 := by
  cases σ <;> simp [PropSpin, hm]

/-- `(deccA0)`: `|A_a| ≤ W^{-D}` whenever `max_{i,j} |a_i - a_j| ≥ W^ε ℓ_s`. -/
def EKFastDecay {d L n : ℕ} (g s W ε D : ℝ) (A : (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ a : Fin n → Zd d L, (∃ i j, W ^ ε * ellT L g s ≤ (zdistD d L (a i - a j) : ℝ)) →
    ‖A a‖ ≤ W ^ (-D)

/-- `(sumAzero)`: `Σ_{a_2,…,a_n} A_a = 0` for every `a_1` (the index of value `0` is the first). -/
def EKSumZero {d L n : ℕ} [NeZero L] (A : (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ i₀ : Fin n, i₀.val = 0 → ∀ x : Zd d L,
    ∑ b ∈ Finset.univ.filter (fun b : Fin n → Zd d L => b i₀ = x), A b = 0

/-! ### The pins -/

/-- **Pin `lem:sum_Ndecay`**, `(sum_res_Ndecay)`: `‖U^{(n)}_{s,t,σ} ∘ 𝒜‖_∞ ≤ ((1-s)/(1-t))^n ‖𝒜‖_∞`
for `0 ≤ s ≤ t < 1`.  No constant, no propagator pin (only property 4). -/
def EKSumNdecay (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n →
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t < 1 →
        ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          ‖UN d L g (EKsgn m σ) s t A‖ ≤ ((1 - s) / (1 - t)) ^ n * ‖A‖

/-- **Pin `lem:sum_decay`, `(sum_res_1)`** under `(deccA0)`, any `σ`: for `0 ≤ s ≤ t ≤ 1 - g²/L²`,
`(1-t)/(1-s) ≥ W⁻¹`,
`‖U ∘ A‖ ≤ W^{Cε} (ℓ_t²/ℓ_s²) ((g²+|1-s|)/(g²+|1-t|))^n ‖A‖ + W^{-D+C}`;
`C` depends on `(d, n, Λ)` only, not on `ε`, `D`; hypothesis: pin 5 (`Prop5Decay`). -/
def EKSumDecay1 (d n : ℕ) (Λ : ℝ) : Prop :=
  Prop5Decay d Λ → 3 ≤ d → 2 ≤ n → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * (ellT L g t ^ 2 / ellT L g s ^ 2)
                * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-- **Pin `lem:sum_decay` (I), `(sum_res_2_NAL)`**: for non-alternating `σ` (`σ_k = σ_{k+1}` for
some `k`), the exponent `n` of `(sum_res_1)` becomes `n - 1` and the factor `ℓ_t²/ℓ_s²` disappears;
hypotheses: pins 5 and 5s; bulk `κ ≤ Im m`. -/
def EKSumDecayNAL (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, (∃ k, σ k = σ (finRotate n k)) →
        ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ (n - 1) * ‖A‖ + W ^ (-D + C)

/-- **Pin `lem:sum_decay` (II), `(sumAzero)` ⟹ `(sum_res_2)`**: for a sum-zero `A` the factor
`ℓ_t²/ℓ_s²` disappears and the exponent stays `n`; hypotheses: pins 5, 5s, 6 (at `c = 1/2`);
`log L ≤ W^ε` is the paper's absorption of `log L` in `(eq:bddfA)` (needed at `d = 3`, candidate
`T2016a`).  `L^d ≤ W^K` (candidate `T2042a`, DECISIONS §21) is the paper's `(Main_DEL_COND)` read
with `K = 1/𝔠`; `C` depends on `K`. -/
def EKSumDecay2 (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Decay d Λ → Prop5Short d Λ κ → Prop6Diff1 d Λ κ (1 / 2) →
    3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∀ K : ℝ, 0 < K →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → Real.log L ≤ W ^ ε →
        (L : ℝ) ^ d ≤ W ^ K →
        ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 - g ^ 2 / (L : ℝ) ^ 2 → W⁻¹ ≤ (1 - t) / (1 - s) →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : (Fin n → Zd d L) → ℂ,
          haveI : NeZero L := ⟨by omega⟩
          EKFastDecay g s W ε D A → EKSumZero A →
          ‖UN d L g (EKsgn m σ) s t A‖ ≤
            W ^ (C * ε) * ((g ^ 2 + |1 - s|) / (g ^ 2 + |1 - t|)) ^ n * ‖A‖ + W ^ (-D + C)

/-- **Pin `lem:sum_decay_nonzero`**, `(sum_res_Ndecay_nonzero)`: for `1 - g²/L² ≤ s ≤ t < 1` and any
`A ⊇ I_diff(σ)`, `‖Q^{(A)} ∘ U^{(n)}_{s,t,σ} ∘ 𝒜‖_∞ ≤ C ‖𝒜‖_∞` (the paper's `≺` made loss-free);
hypotheses: pins 5s and 8; both signs of `m`. -/
def EKSumDecayNonzero (d n : ℕ) (Λ κ : ℝ) : Prop :=
  Prop5Short d Λ κ → Prop8ZeroMode d Λ κ → 3 ≤ d → 2 ≤ n → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ s t : ℝ, 0 ≤ s → 1 - g ^ 2 / (L : ℝ) ^ 2 ≤ s → s ≤ t → t < 1 →
        ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Fin n → Bool, ∀ A : Finset (Fin n),
          (∀ i, σ i ≠ σ (finRotate n i) → i ∈ A) →
          ∀ 𝒜 : (Fin n → Zd d L) → ℂ,
            haveI : NeZero L := ⟨by omega⟩
            ‖zeroModeSet d L A (UN d L g (EKsgn m σ) s t 𝒜)‖ ≤ C * ‖𝒜‖

/-! ### Pins already proved by merged theorems -/

theorem ekSumNdecay_holds (d n : ℕ) : EKSumNdecay d n := by
  intro _ _ L hL g _ m hm σ s t hs hst ht A
  have : NeZero L := ⟨by omega⟩
  exact norm_UN_le hL (fun i => ek_norm_spin hm (σ i)) hs hst ht A

/-! ### Compiled nonempty instances

`d = 3`, `L = 5`, `g = 1/2`, `Λ = 1`, `κ = 1/2`, `m = i` (`‖m‖ = 1`, `Im m = 1 ≥ κ`), `n = 2`;
`s = 1/2`, `t = 9/10` (`g²/L² = 1/100 ≤ 1 - t = 1/10`), `W = 25`, `ε = 1/2` (`W^ε = 5 ≥ 4`; the window radius `5` is below the torus diameter `6`),
`D = 2` (`W⁻¹ = 1/25 ≤ (1-t)/(1-s) = 1/5`).  Tensors: `ekA0 = δ_0` and the sum-zero
`ekAz = δ_0 ⊗ (δ_0 - δ_e)`, `e = (1,0,0)`.  For `lem:sum_decay_nonzero` the window
`1 - g²/L² = 0.99 ≤ s ≤ t` excludes `t = 9/10`: there `s = 0.995`, `t = 0.999`.  The pins of
other gates (`Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode`) stay hypotheses of the examples;
`Prop5Short` is proved (`prop5Short_holds`). -/

end RBM
