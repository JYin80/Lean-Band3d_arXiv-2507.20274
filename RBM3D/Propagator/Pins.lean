/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Interface

/-!
# Pins for properties 5-8 of `lem_propTH` (random band model, `d ≥ 3`)

Every pin is a `Prop` (namespace `RBM`, name prefix `Prop` + number); nothing here is asserted
except what is proved below.  Form common to all pins (paper `lem_propTH`,
`1_2_Intro_model_result.tex:1068-1185`):
* the constants are quantified **before** `L` and `g` (`g = λ` of the paper) and depend only on
  `d`, `Λ` (the upper end of `(eq:WO)`, `Λ = 𝔡⁻¹`), and where the paper says so on `κ`, `c`;
* `g ∈ (0, Λ]`, `L ≥ 3`, `t ∈ [0, 1)`, both sign pairs `(σ₁, σ₂)`: `Θ_t^{(σ₁,σ₂)}` is
  `Theta d L g (t * (m(σ₁) m(σ₂)))` with `m(+) = m`, `m(-) = m̄`, `‖m‖ = 1`;
* the bulk condition is `κ ≤ Im m`;
* `≺` of properties 6-8 is no loss; `|r| ≲ |a|` of properties 6, 7 is `|r| ≤ c |a|`, `0 < c < 1`.

Contents: the pins `PropSpin`, `Prop5Decay`, `Prop5Short`, `Prop6Diff1`, `Prop7Diff2`,
`Prop8ZeroMode`, `Prop5to8`, `PropThetaQ`, `Prop5DecayQ` (the statements are the ticket's pinned
text); the bridges to the merged consumer interfaces `ThetaDecay`, `ThetaDecayShort`,
`ThetaZeroMode`; and `Prop5_needs_Lambda`.
-/

namespace RBM

/-- `m(σ)` of the paper: `σ = true` is `+` (`m(+) = m`), `σ = false` is `-` (`m(-) = m̄`). -/
noncomputable def PropSpin (m : ℂ) : Bool → ℂ := fun σ => if σ then m else (starRingEnd ℂ) m

/-- **Pin 5** `(prop:ThfadC)`: `|Θ_t(0,a)| ≤ C_d B_{t,|a|} e^{-c_d |a| / ℓ_t}`; constants `(d, Λ)`;
all `m` with `‖m‖ = 1`, all sign pairs, no bulk condition. -/
def Prop5Decay (d : ℕ) (Λ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a)
                * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Pin 5s** `(prop:ThfadC_short)`, `σ₁ = σ₂ = σ`: `|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² e^{-c_κ|a|})`;
constants `(d, Λ, κ)`; bulk `κ ≤ Im m`. -/
def Prop5Short (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ * PropSpin m σ)) 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Pin 6** `(prop:BD1)`: `|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}` for
`|r| ≤ c |a|`, `0 < c < 1`; constants `(d, Λ, κ, c)`; no loss. -/
def Prop6Diff1 (d : ℕ) (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r)
              - Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ)
                * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Pin 7** `(prop:BD2)`:
`|Θ_t(0,a+r) + Θ_t(0,a-r) - 2Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r|² (|a|+1)^{-d}` for `|r| ≤ c |a|`,
`0 < c < 1`; constants `(d, Λ, κ, c)`; no loss. -/
def Prop7Diff2 (d : ℕ) (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a + r)
              + Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 (a - r)
              - 2 * Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2
                * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- **Pin 8** `(prop:ThfadC0)`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`; constants
`(d, Λ, κ)`; no loss. -/
def Prop8ZeroMode (d : ℕ) (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → κ ≤ m.im → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta0 d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-- The bundle: properties 5-8 of `lem_propTH` at one `(d, Λ, κ, c)`. -/
structure Prop5to8 (d : ℕ) (Λ κ c : ℝ) : Prop where
  /-- `(prop:ThfadC)` -/
  decay : Prop5Decay d Λ
  /-- `(prop:ThfadC_short)` -/
  short : Prop5Short d Λ κ
  /-- `(prop:BD1)` -/
  diffOne : Prop6Diff1 d Λ κ c
  /-- `(prop:BD2)` -/
  diffTwo : Prop7Diff2 d Λ κ c
  /-- `(prop:ThfadC0)` -/
  zeroMode : Prop8ZeroMode d Λ κ

/-! ### The constants of pin 5 must depend on `Λ` (candidate `T2003a`)

At `t = 0`, `Θ_0 = 1` and `B_{0,0} = (g²+1)⁻¹ + L⁻ᵈ`, so `|Θ_0(0,0)| = 1 ≤ C B_{0,0}` forces
`C ≥ (1+g²)/(1+(1+g²)L⁻ᵈ)`.  With `g` unbounded this has no uniform `C`: the paper's "constants
depending on `d`" is correct only with `g ≤ Λ`, `Λ = 𝔡⁻¹` of `(eq:WO)`, and `C ≥ 1 + Λ²`. -/

/-- Candidate `T2003a`: pin 5 without the bound `g ≤ Λ` has no uniform constants. -/
theorem Prop5_needs_Lambda (d : ℕ) (hd : 1 ≤ d) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta d L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a)
                * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t) := by
  rintro ⟨C, hC, c, hc, H⟩
  obtain ⟨L₀, hL₀⟩ := exists_nat_ge (4 * C)
  have hL3 : 3 ≤ L₀ + 3 := by omega
  have : NeZero (L₀ + 3) := ⟨by omega⟩
  have hg : (0 : ℝ) < 4 * C + 1 := by linarith
  have key := H (L₀ + 3) hL3 (4 * C + 1) hg 0 le_rfl zero_lt_one 1 (by simp) true true 0
  have hTh : Theta d (L₀ + 3) (4 * C + 1)
      (((0 : ℝ) : ℂ) * (PropSpin 1 true * PropSpin 1 true)) = 1 := by
    simp [Theta]
  simp only [hTh, zdistD_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one,
    Matrix.one_apply_eq, norm_one, Bparam, sub_zero, abs_one, zero_add, one_pow, inv_one] at key
  have hLd : (4 * C : ℝ) ≤ ((L₀ + 3 : ℕ) : ℝ) ^ d := by
    have h1 : ((L₀ + 3 : ℕ) : ℝ) ≤ ((L₀ + 3 : ℕ) : ℝ) ^ d := by
      have : (1 : ℝ) ≤ ((L₀ + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L₀ + 3)
      calc ((L₀ + 3 : ℕ) : ℝ) = ((L₀ + 3 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ ((L₀ + 3 : ℕ) : ℝ) ^ d := pow_le_pow_right₀ this hd
    have h2 : (L₀ : ℝ) ≤ ((L₀ + 3 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hg2 : (4 * C : ℝ) ≤ (4 * C + 1) ^ 2 + 1 := by nlinarith [sq_nonneg (4 * C)]
  have hA : ((4 * C + 1) ^ 2 + 1)⁻¹ ≤ (4 * C)⁻¹ := inv_anti₀ (by positivity) hg2
  have hB : (((L₀ + 3 : ℕ) : ℝ) ^ d)⁻¹ ≤ (4 * C)⁻¹ := inv_anti₀ (by positivity) hLd
  have hbound : C * (((4 * C + 1) ^ 2 + 1)⁻¹ + (((L₀ + 3 : ℕ) : ℝ) ^ d)⁻¹) ≤ 1 / 2 := by
    calc C * (((4 * C + 1) ^ 2 + 1)⁻¹ + (((L₀ + 3 : ℕ) : ℝ) ^ d)⁻¹)
        ≤ C * ((4 * C)⁻¹ + (4 * C)⁻¹) := by gcongr
      _ = 1 / 2 := by field_simp; ring
  linarith


/-! ### The new pins are at least as strong as what merged consumers assume

`Loop/*`, `Kernel/Evolution` take `ThetaDecayShort d g m`, `Kernel/SumDecay` takes
`ThetaDecay d g μ`, `Kernel/Evolution` takes `ThetaZeroMode d g μ` (constants after `g`, `m`; loss
`L^τ`).  Each follows
from the corresponding pin at `Λ = g`, `κ = Im m` (and `L^τ ≥ 1`); so the merged consumers need no
change when a pin is proved. -/

private theorem pins_exists_sq (μ : ℂ) (hμ : ‖μ‖ = 1) : ∃ n : ℂ, ‖n‖ = 1 ∧ n * n = μ := by
  refine ⟨Complex.exp (↑(Complex.arg μ / 2) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_add]
  have h2 : (↑(Complex.arg μ / 2) * Complex.I + ↑(Complex.arg μ / 2) * Complex.I : ℂ)
      = ↑(Complex.arg μ) * Complex.I := by push_cast; ring
  rw [h2]
  have h := Complex.norm_mul_exp_arg_mul_I μ
  rw [hμ] at h
  simpa using h

/-- Pin 5s at `Λ = g`, `κ = Im m` is the merged `ThetaDecayShort d g m`. -/
theorem Prop5Short.thetaDecayShort {d : ℕ} {g : ℝ} {m : ℂ} (h : Prop5Short d g m.im) :
    ThetaDecayShort d g m := by
  intro hd hg hm hmi
  obtain ⟨C, hC, c, hc, H⟩ := h hd hg hmi
  refine ⟨C, hC, c, hc, fun L hL t ht0 ht1 a => ?_⟩
  have := H L hL g hg le_rfl t ht0 ht1 m hm le_rfl true a
  simpa [PropSpin] using this

/-- Pin 5 at `Λ = g` gives the merged `ThetaDecay d g m` (square root of `m`). -/
theorem Prop5Decay.thetaDecay {d : ℕ} {g : ℝ} (h : Prop5Decay d g) (m : ℂ) : ThetaDecay d g m := by
  intro hd hg hm
  obtain ⟨C, hC, c, hc, H⟩ := h hd hg
  obtain ⟨n, hn, hnn⟩ := pins_exists_sq m hm
  refine ⟨C, hC, c, hc, fun L hL t ht0 ht1 a => ?_⟩
  have := H L hL g hg le_rfl t ht0 ht1 n hn true true a
  simpa [PropSpin, hnn] using this

/-- Pin 8 gives the merged `ThetaZeroMode` (the loss `L^τ ≥ 1` is absorbed). -/
theorem Prop8ZeroMode.thetaZeroMode {d : ℕ} {Λ κ g : ℝ} (h : Prop8ZeroMode d Λ κ) (hg : 0 < g)
    (hgΛ : g ≤ Λ) (hκ : 0 < κ) {m : ℂ} (hm : ‖m‖ = 1) (hmi : κ ≤ m.im) (σ₁ σ₂ : Bool) :
    ThetaZeroMode d g (PropSpin m σ₁ * PropSpin m σ₂) := by
  intro hd _ _ τ hτ
  obtain ⟨C, hC, H⟩ := h hd (hg.trans_le hgΛ) hκ
  refine ⟨C, hC, fun L hL t ht0 ht1 a => ?_⟩
  refine (H L hL g hg hgΛ t ht0 ht1 m hm hmi σ₁ σ₂ a).trans ?_
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast (by omega : 1 ≤ L)
  have hLτ : (1 : ℝ) ≤ (L : ℝ) ^ τ := Real.one_le_rpow hL1 hτ.le
  have hX : 0 ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  calc C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹
      = 1 * (C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) := (one_mul _).symm
    _ ≤ (L : ℝ) ^ τ * (C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹) :=
        mul_le_mul_of_nonneg_right hLτ hX
    _ = C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹ := by ring

/-! ### The shape gate BA reuses

In the block Anderson model `S^{(B)} = 1` and `M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)`
is a complex symmetric matrix with `|M^{(σ₁,σ₂)}_{ab}| ≤ M^{(+,-)}_{ab}` and unit row sums for
`(+,-)` (Ward).  `Θ_t^{(σ₁,σ₂)} = (1 - t Q)⁻¹` with `Q = M^{(σ₁,σ₂)} S^{(B)}`.  The statements of
properties 5-8 keep their form for any such family `Q`; only the proofs depend on `Q`
(the RBM family is `Q = (m(σ₁)m(σ₂)) • SB d L g`).  Pin 5 in this shape is below. -/

/-- `Θ_t = (1 - t Q)⁻¹` for an arbitrary transition matrix `Q = M^{(σ₁,σ₂)} S^{(B)}`. -/
noncomputable def PropThetaQ {d L : ℕ} [NeZero L] (Q : Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) :
    Matrix (Zd d L) (Zd d L) ℂ :=
  Ring.inverse (1 - (t : ℂ) • Q)

/-- The RBM propagator is `PropThetaQ` of the scalar multiple `μ • S^{(B)}`. -/
theorem PropThetaQ_Theta_eq (d L : ℕ) [NeZero L] (g : ℝ) (t : ℝ) (μ : ℂ) :
    Theta d L g ((t : ℂ) * μ) = PropThetaQ ((μ : ℂ) • SB d L g) t := by
  simp [Theta, PropThetaQ, smul_smul]


/-- Pin 5 for a model-indexed family `Q L g σ₁ σ₂`; the model is the family. -/
def Prop5DecayQ (d : ℕ) (Λ : ℝ)
    (Q : ∀ (L : ℕ) [NeZero L], ℝ → Bool → Bool → Matrix (Zd d L) (Zd d L) ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖PropThetaQ (Q L g σ₁ σ₂) t 0 a‖
          ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- Pin 5 specialises to the generalised shape at the RBM family (one `m` at a time). -/
theorem Prop5Decay.toQ {d : ℕ} {Λ : ℝ} (h : Prop5Decay d Λ) (hd : 3 ≤ d) (hΛ : 0 < Λ) (m : ℂ)
    (hm : ‖m‖ = 1) :
    Prop5DecayQ d Λ (fun L [NeZero L] g σ₁ σ₂ => (PropSpin m σ₁ * PropSpin m σ₂) • SB d L g) := by
  obtain ⟨C, hC, c, hc, H⟩ := h hd hΛ
  refine ⟨C, hC, c, hc, fun L hL g hg hgΛ t ht0 ht1 σ₁ σ₂ a => ?_⟩
  have := H L hL g hg hgΛ t ht0 ht1 m hm σ₁ σ₂ a
  simpa only [← PropThetaQ_Theta_eq] using this

/-! ### Nonempty instances of the theorems of this file

Each theorem is applied at `d = 3`, `Λ = 1` (or `g = 1/2`), `m = I`, with every deterministic
hypothesis discharged; a pin that is another gate's unproved statement stays a hypothesis of the
instance (`Prop5Short` is proved in `RBM3D/Propagator/Prop5Short.lean`, whose instances use it). -/

example : PropSpin Complex.I true = Complex.I ∧ PropSpin Complex.I false = -Complex.I := by
  simp [PropSpin]

example : Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * Complex.I)
    = PropThetaQ (Complex.I • SB 3 5 (1 / 2)) (9 / 10) :=
  PropThetaQ_Theta_eq 3 5 (1 / 2) (9 / 10) Complex.I

example (h : Prop5Decay 3 1) : ThetaDecay 3 1 Complex.I := h.thetaDecay Complex.I

example (h : Prop5Decay 3 1) :
    Prop5DecayQ 3 1 (fun L [NeZero L] g σ₁ σ₂ =>
      (PropSpin Complex.I σ₁ * PropSpin Complex.I σ₂) • SB 3 L g) :=
  h.toQ (by norm_num) one_pos Complex.I Complex.norm_I

example (h : Prop5Short 3 (1 / 2) Complex.I.im) : ThetaDecayShort 3 (1 / 2) Complex.I :=
  h.thetaDecayShort

example (h : Prop8ZeroMode 3 1 (1 / 2)) :
    ThetaZeroMode 3 (1 / 2) (PropSpin Complex.I true * PropSpin Complex.I false) :=
  h.thetaZeroMode (by norm_num) (by norm_num) (by norm_num) Complex.norm_I
    (by norm_num) true false

example (h5 : Prop5Decay 3 1) (h5s : Prop5Short 3 1 (1 / 2)) (h6 : Prop6Diff1 3 1 (1 / 2) (1 / 2))
    (h7 : Prop7Diff2 3 1 (1 / 2) (1 / 2)) (h8 : Prop8ZeroMode 3 1 (1 / 2)) :
    Prop5to8 3 1 (1 / 2) (1 / 2) :=
  ⟨h5, h5s, h6, h7, h8⟩

example : ¬ ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g →
        ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ m : ℂ, ‖m‖ = 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd 3 L,
          haveI : NeZero L := ⟨by omega⟩
          ‖Theta 3 L g ((t : ℂ) * (PropSpin m σ₁ * PropSpin m σ₂)) 0 a‖
            ≤ C * Bparam 3 L g t (zdistD 3 L a)
                * Real.exp (-c * (zdistD 3 L a : ℝ) / ellT L g t) :=
  Prop5_needs_Lambda 3 (by norm_num)

end RBM
