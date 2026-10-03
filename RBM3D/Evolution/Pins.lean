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

/-- **Pin `lem:propT`**, `(TTT2)`: `Σ_c 𝒯_u(|a-c|) 𝒯_t(|c-b|) ≤ C_d/(1-u) · 𝒯_t(|a-b|)` for
`0 ≤ u ≤ t < 1` with (i) `1-t ≥ g²/L²` or (ii) `1-u ≤ g²/L²`; `C_d` depends on `d` only.  No
propagator pin. -/
def EKPropT (d : ℕ) : Prop :=
  3 ≤ d →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (g u t : ℝ), 0 < g → 0 ≤ u → u ≤ t → t < 1 →
        (g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t ∨ 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2) →
        ∀ a b : Zd d L,
          ∑ c : Zd d L, tailT d L g u (zdistD d L (a - c)) * tailT d L g t (zdistD d L (c - b))
            ≤ C / (1 - u) * tailT d L g t (zdistD d L (a - b))

/-- **Pin `claim:TTk`**, `(eq:key_T_reudce)`: for `1 - t ≥ g²/L²`, `n ≥ 2` pairs and
`1 ≤ ℓ ≤ Λ ℓ_t` (here `Λ` is the multiplier `(log W)^{10}` of the paper, not `𝔡⁻¹`), the paper's
`≺` made explicit:
`Σ_{α ∈ D} ∏_i 𝖳_t(|x_i-α|∧ℓ) 𝖳_t(|y_i-α|∧ℓ)`
`  ≤ C Λ² (W^d (1-t))⁻¹ Ψ_t^{n-2} ∏_i 𝖳_t(|x_i-y_i|∧ℓ)`. -/
def EKTTk (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
        ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
        ∀ (D : Finset (Zd d L)) (a : Zd d L), (∀ α ∈ D, (zdistD d L (a - α) : ℝ) ≤ ℓ) →
        ∀ x y : Fin n → Zd d L,
          ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistD d L (x i - α) : ℝ) ℓ)
                * sfT d L W g t (min (zdistD d L (y i - α) : ℝ) ℓ))
            ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
                (PsiT d L W g t ^ (n - 2) *
                  ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))

/-! ### Pins already proved by merged theorems -/

theorem ekSumNdecay_holds (d n : ℕ) : EKSumNdecay d n := by
  intro _ _ L hL g _ m hm σ s t hs hst ht A
  have : NeZero L := ⟨by omega⟩
  exact norm_UN_le hL (fun i => ek_norm_spin hm (σ i)) hs hst ht A

theorem ekPropT_holds (d : ℕ) : EKPropT d := by
  intro hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨C, hC, H⟩ := propT k
  exact ⟨C, hC, fun L _ g u t hg hu hut ht hreg a b => H L g u t hg hu hut ht hreg a b⟩

theorem ekTTk_holds (d n : ℕ) : EKTTk d n := by
  intro hd hn
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨3 * keyC k n, by
    have : 0 < keyC k n := by
      unfold keyC
      have := ballC_pos k
      positivity
    positivity, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt D a hD x y
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have h := key_T_reduce_absorbed (L := L) (W := W) (g := g) (t := t) hW (k := k) (n := n) hn
    (ℓ := ℓ) (Λ := Λ) hℓ hL1 hg ht hgL hℓt D a hD x y
  refine h.trans (le_of_eq ?_)
  ring


/-- the sum over `Fin 2 → X` as a double sum. -/
theorem ek_sum_fin_two {X M : Type*} [Fintype X] [AddCommMonoid M] (F : (Fin 2 → X) → M) :
    ∑ b : Fin 2 → X, F b = ∑ x : X, ∑ y : X, F ![x, y] := by
  rw [← Fintype.sum_prod_type' (fun x y => F ![x, y])]
  refine Fintype.sum_equiv (finTwoArrowEquiv X) _ _ fun b => ?_
  congr 1
  funext i
  fin_cases i <;> rfl



/-! ### Compiled nonempty instances

`d = 3`, `L = 5`, `g = 1/2`, `Λ = 1`, `κ = 1/2`, `m = i` (`‖m‖ = 1`, `Im m = 1 ≥ κ`), `n = 2`;
`s = 1/2`, `t = 9/10` (`g²/L² = 1/100 ≤ 1 - t = 1/10`), `W = 25`, `ε = 1/2` (`W^ε = 5 ≥ 4`; the window radius `5` is below the torus diameter `6`),
`D = 2` (`W⁻¹ = 1/25 ≤ (1-t)/(1-s) = 1/5`).  Tensors: `ekA0 = δ_0` and the sum-zero
`ekAz = δ_0 ⊗ (δ_0 - δ_e)`, `e = (1,0,0)`.  For `lem:sum_decay_nonzero` the window
`1 - g²/L² = 0.99 ≤ s ≤ t` excludes `t = 9/10`: there `s = 0.995`, `t = 0.999`.  The pins of
other gates (`Prop5Decay`, `Prop6Diff1`, `Prop8ZeroMode`) stay hypotheses of the examples;
`Prop5Short` is proved (`prop5Short_holds`). -/

section Instances

private abbrev ekE : Zd 3 5 := ![1, 0, 0]

private noncomputable def ekA0 : (Fin 2 → Zd 3 5) → ℂ := fun b => if b = 0 then 1 else 0

private noncomputable def ekAz : (Fin 2 → Zd 3 5) → ℂ := fun b =>
  if b 0 = 0 then (if b 1 = 0 then 1 else 0) - (if b 1 = ekE then 1 else 0) else 0

private theorem ek_zdistD_E : zdistD 3 5 ekE = 1 := by
  unfold zdistD
  simp only [zdist, ekE, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZMod.val_zero, tsub_zero, zero_le, inf_of_le_left, add_zero, Matrix.cons_val]
  decide

private theorem ekA0_zero : ekA0 0 = 1 := by simp [ekA0]

private theorem ek_zero_ne_E : (0 : Zd 3 5) ≠ ekE := by
  intro h
  have := congrFun h 0
  simp only [ekE, Pi.zero_apply, Matrix.cons_val_zero] at this
  exact absurd this (by decide)

private theorem ekAz_vals : ekAz ![0, 0] = 1 ∧ ekAz ![0, ekE] = -1 := by
  simp [ekAz, ek_zero_ne_E, ek_zero_ne_E.symm]

private theorem ek_sqrt25 : (25 : ℝ) ^ ((1 : ℝ) / 2) = 5 := by
  rw [← Real.sqrt_eq_rpow, show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private theorem ek_ellT_s : ellT 5 (1 / 2 : ℝ) (1 / 2) = 1 := by
  unfold ellT
  have hs : (1 / 2 : ℝ) ≤ Real.sqrt |1 - 1 / 2| := by
    rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by rw [abs_of_pos (by norm_num)]; norm_num]
    have h4 : (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
      exact (Real.sqrt_sq (by norm_num)).symm
    calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := h4
      _ ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt (by norm_num)
  have h : (1 / 2 : ℝ) / Real.sqrt |1 - 1 / 2| ≤ 1 := by
    rw [div_le_one (lt_of_lt_of_le (by norm_num) hs)]
    exact hs
  rw [max_eq_right h]
  norm_num

private theorem ek_zdistD_far : zdistD 3 5 (![2, 2, 1] : Zd 3 5) = 5 := by
  unfold zdistD
  simp only [Fin.sum_univ_three, zdist]
  decide

/-- the far premise of `(deccA0)` is not vacuous at the instance data -/
private theorem ek_far_point_exists :
    ∃ a : Fin 2 → Zd 3 5, ∃ i j, (25 : ℝ) ^ ((1 : ℝ) / 2) * ellT 5 (1 / 2 : ℝ) (1 / 2)
      ≤ (zdistD 3 5 (a i - a j) : ℝ) := by
  refine ⟨![0, ![2, 2, 1]], 0, 1, ?_⟩
  rw [ek_sqrt25, ek_ellT_s]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, zdistD_neg, ek_zdistD_far]
  norm_num

private theorem ek_fastDecay_A0 : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekA0 := by
  intro a ⟨i, j, hij⟩
  by_cases ha : a = 0
  · exfalso
    subst ha
    have hℓ : 1 ≤ ellT 5 (1 / 2 : ℝ) (1 / 2) := one_le_ellT (by norm_num)
    rw [ek_sqrt25] at hij
    simp at hij
    linarith
  · simp only [ekA0, ha, ↓reduceIte, norm_zero]
    positivity

private theorem ek_fastDecay_Az : EKFastDecay (1 / 2 : ℝ) (1 / 2) 25 (1 / 2) 2 ekAz := by
  intro a ⟨i, j, hij⟩
  by_cases h : ekAz a = 0
  · rw [h]; simp only [norm_zero]; positivity
  · exfalso
    have h0 : a 0 = 0 := by
      by_contra hc; simp [ekAz, hc] at h
    have h1 : a 1 = 0 ∨ a 1 = ekE := by
      by_contra hc
      rw [not_or] at hc
      simp [ekAz, h0, hc.1, hc.2] at h
    have hE : ∀ y : Zd 3 5, y = 0 ∨ y = ekE → zdistD 3 5 y ≤ 1 := by
      rintro y (rfl | rfl)
      · simp
      · rw [ek_zdistD_E]
    have hd : ∀ i j : Fin 2, zdistD 3 5 (a i - a j) ≤ 1 := by
      refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩,
        Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
      · simp
      · rw [h0, zero_sub, zdistD_neg]; exact hE _ h1
      · rw [h0, sub_zero]; exact hE _ h1
      · simp
    have hℓ : 1 ≤ ellT 5 (1 / 2 : ℝ) (1 / 2) := one_le_ellT (by norm_num)
    rw [ek_sqrt25] at hij
    have := hd i j
    have h2 : (zdistD 3 5 (a i - a j) : ℝ) ≤ 1 := by exact_mod_cast this
    linarith

private theorem ek_sumZero_Az : EKSumZero ekAz := by
  intro i₀ hi₀ x
  have hi : i₀ = 0 := Fin.ext hi₀
  subst hi
  rw [Finset.sum_filter, ek_sum_fin_two]
  have e : ∀ x' y : Zd 3 5, (if (![x', y] : Fin 2 → Zd 3 5) 0 = x then ekAz ![x', y] else 0)
      = if x' = x then (if x' = 0 then (if y = 0 then (1 : ℂ) else 0) - (if y = ekE then 1 else 0)
          else 0) else 0 := by
    intro x' y
    simp [ekAz]
  simp only [e]
  by_cases hx : x = 0
  · subst hx
    simp [Finset.sum_ite_eq', Finset.sum_sub_distrib]
  · simp

/-- the window hypotheses shared by the three `lem:sum_decay` instances. -/
private theorem ek_log5 : Real.log ((5 : ℕ) : ℝ) ≤ (25 : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [ek_sqrt25]
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < ((5 : ℕ) : ℝ))
  push_cast at this ⊢
  linarith

private theorem ekInstNdecay :
    ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekA0‖
    ≤ ((1 - 1 / 2) / (1 - 9 / 10)) ^ 2 * ‖ekA0‖ :=
  ekSumNdecay_holds 3 2 (by norm_num) le_rfl 5 (by norm_num) (1 / 2) (by norm_num) Complex.I
    Complex.norm_I ![true, false] (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) ekA0

/-- instance of `EKSumDecayNAL` (`(sum_res_2_NAL)`, `σ = (+,+)`). -/
private theorem ekInstNAL (h : EKSumDecayNAL 3 2 1 (1 / 2)) (h5 : Prop5Decay 3 1) : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, true]) (1 / 2) (9 / 10) ekA0‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) *
        (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ (2 - 1) * ‖ekA0‖
      + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := h h5 (prop5Short_holds 3 1 (1 / 2)) (by norm_num) le_rfl one_pos
    (by norm_num)
  refine ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ek_sqrt25]; norm_num)
    (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I
    Complex.norm_I (by norm_num [Complex.I_im]) ![true, true] ⟨0, by decide⟩ ekA0 ek_fastDecay_A0⟩

/-- instance of `EKSumDecay2` (`(sumAzero)` ⟹ `(sum_res_2)`, `σ = (+,-)`). -/
private theorem ekInstDecay2 (h : EKSumDecay2 3 2 1 (1 / 2)) (h5 : Prop5Decay 3 1)
    (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (1 / 2) (9 / 10) ekAz‖ ≤
      (25 : ℝ) ^ (C * (1 / 2)) *
        (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2 * ‖ekAz‖
      + (25 : ℝ) ^ (-2 + C) := by
  obtain ⟨C, hC, H⟩ := h h5 (prop5Short_holds 3 1 (1 / 2)) h6 (by norm_num) le_rfl one_pos
    (by norm_num) 2 two_pos
  refine ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 25 (1 / 2) 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by rw [ek_sqrt25]; norm_num)
    ek_log5 (by norm_num [Real.rpow_two]) (1 / 2) (9 / 10) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) Complex.I
    Complex.norm_I (by norm_num [Complex.I_im]) ![true, false] ekAz ek_fastDecay_Az ek_sumZero_Az⟩

/-- instance of `EKSumDecayNonzero` (`(sum_res_Ndecay_nonzero)`, `A = {0,1} ⊇ I_diff(+,-)`;
window `s = 0.995`, `t = 0.999`). -/
private theorem ekInstNonzero (h : EKSumDecayNonzero 3 2 1 (1 / 2))
    (h8 : Prop8ZeroMode 3 1 (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖zeroModeSet 3 5 Finset.univ
        (UN 3 5 (1 / 2) (EKsgn Complex.I ![true, false]) (995 / 1000) (999 / 1000) ekA0)‖
      ≤ C * ‖ekA0‖ := by
  obtain ⟨C, hC, H⟩ := h (prop5Short_holds 3 1 (1 / 2)) h8 (by norm_num) le_rfl one_pos
    (by norm_num)
  exact ⟨C, hC, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (995 / 1000) (999 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) Complex.I Complex.norm_I
    (by norm_num [Complex.I_im])
    ![true, false] Finset.univ (fun i _ => Finset.mem_univ i) ekA0⟩

/-- instance of `EKPropT` (`lem:propT`), regime (i), `u = 1/2`, `t = 9/10`. -/
private theorem ekInstPropT : ∃ C : ℝ, 0 < C ∧
    ∑ c : Zd 3 5, tailT 3 5 (1 / 2) (1 / 2) (zdistD 3 5 (0 - c)) *
        tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (c - ekE))
      ≤ C / (1 - 1 / 2) * tailT 3 5 (1 / 2) (9 / 10) (zdistD 3 5 (0 - ekE)) := by
  obtain ⟨C, hC, H⟩ := ekPropT_holds 3 (by norm_num)
  exact ⟨C, hC, H 5 (1 / 2) (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl (by norm_num)) 0 ekE⟩

/-- instance of `EKTTk` (`claim:TTk`), `n = 2`, `W = 25`, `ℓ = Λ = 1`, `D` the `ℓ¹`-ball of radius
`1` around `0`. -/
private theorem ekInstTTk : ∃ C : ℝ, 0 < C ∧
    ∑ α ∈ Finset.univ.filter (fun α : Zd 3 5 => (zdistD 3 5 (0 - α) : ℝ) ≤ 1),
        ∏ i, (sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![0, ekE] i - α) : ℝ) 1)
          * sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistD 3 5 (![ekE, 0] i - α) : ℝ) 1))
      ≤ C * (1 ^ 2 * (((25 : ℝ) ^ 3)⁻¹ / (1 - 9 / 10))) *
          (PsiT 3 5 25 (1 / 2) (9 / 10) ^ (2 - 2) *
            ∏ i, sfT 3 5 25 (1 / 2) (9 / 10)
              (min (zdistD 3 5 (![0, ekE] i - ![ekE, 0] i) : ℝ) 1)) := by
  obtain ⟨C, hC, H⟩ := ekTTk_holds 3 2 (by norm_num) le_rfl
  exact ⟨C, hC, H 5 25 (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 1
    le_rfl (by simpa using one_le_ellT (L := 5) (g := 1 / 2) (t := 9 / 10) (by norm_num)) _ 0
    (fun α hα => (Finset.mem_filter.mp hα).2) _ _⟩

end Instances



end RBM
