/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Defs.Tail
import RBM3D.Defs.Params
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# LW-15: the deterministic facts about the control parameter `Ψ_t` (T2051)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (cited `3_5:line`) and
`paper/tex/7_8_light_weight.tex` (`7_8:line`).  Design: T2040 (probe `RBM3D/Probe/T2040Graphs.lean`
at `eeda441` on `t/T2040`; DECISIONS §24).

* Section 1: the class predicates `LWWindow`, `LWClass`, `LWPsiRel`, `LWPsiAll`, copied from the
  probe (lines 918-920, 928-932, 934-941, 1076-1078) with their docstrings, and the B class
  `LWPhiB` (`Ψ_t(r) = (W^{-c₀} B_{t, ⌊r⌋∧K})^{1/2}`, the lambda of the probe's `LWtermB`, probe
  lines 970-973).  The sequence-level pins (`LWterm`, `LWtermExp`, ...) are not here.
* Section 2: `(eq:Psi)` for the B class (`LWPhiB_psiRel`, constants `(2^d, d)`; `(2, 2)` at
  `d = 3`), and `Ψ_t(c r) ≲ Ψ_t(r)` (`LWPsiAll.shift`, `LWPhiB_shift`).
* Section 3: the window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` (paper-delta T2040a): for
  `Ψ_t = max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})` and the class `LWClass` of the B class with
  `c₀ ≤ d`.
* Section 4: `W^{-d} 𝒯̃ ≍ [s𝒯]²` for `r ≤ L` (paper-delta T2040k), in the two regimes of
  `7_8:20-30`.
* Section 5: compiled nonempty instances at `d = 3` (merged `sz0`), `t ≡ 1/16` and `t = 1 - W^{-2}`.
-/

set_option linter.style.longLine false

noncomputable section

open Filter

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. The class predicates (probe `eeda441:RBM3D/Probe/T2040Graphs.lean`, copied verbatim) -/

/-- The window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` of the control parameter. -/
def LWWindow (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧ Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)

/-- The class `Ψ_t(·)` of `lem:LWterm` (`3_5:388-392`): positive, `≤ W^{-ε₀}`, and
`W^{-d/2} ≲ Ψ_t(0)` (with the constant `C₃`).  Its monotonicity and `(eq:Psi)` are in `LWPsiRel`. -/
def LWClass (ε₀ C₃ : ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → 0 < Φ n r ∧ Φ n r ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    0 < C₃ ∧ ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ C₃ * Φ n 0

/-- "Without loss of generality `Ψ_t(ℓ)` is monotonically decreasing" and `(eq:Psi)` (`3_5:391`):
`Ψ_t(0) ≍ Ψ_t(ℓ)` for `0 ≤ ℓ ≤ C` (constant `Cc C`, any `C > 1`) and `Ψ_t(ℓ₁)/Ψ_t(ℓ₂) ≤ C₁ (ℓ₂/ℓ₁)^{C₂}`
for `ℓ₂ ≥ ℓ₁ ≥ 1`, with `C₁, C₂ > 1`. -/
def LWPsiRel (C₁ C₂ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  (∀ n, AntitoneOn (Φ n) (Set.Ici 0)) ∧ 1 < C₁ ∧ 1 < C₂ ∧
    (∀ C : ℝ, 1 < C → ∀ᶠ n in atTop, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ C → Φ n 0 ≤ Cc C * Φ n ℓ) ∧
    ∀ᶠ n in atTop, ∀ ℓ₁ ℓ₂ : ℝ, 1 ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → Φ n ℓ₁ ≤ C₁ * (ℓ₂ / ℓ₁) ^ C₂ * Φ n ℓ₂


/-- The hypotheses on the class `Ψ_t(·)` shared by the graph lemmas: positivity and window, `(eq:Psi)`. -/
def LWPsiAll (ε₀ C₁ C₂ C₃ : ℝ) (Cc : ℝ → ℝ) (Φ : ℕ → ℝ → ℝ) : Prop :=
  0 < ε₀ ∧ LWClass sz ε₀ C₃ Φ ∧ LWPsiRel C₁ C₂ Cc Φ

/-- **The B class of `lem:LWterm`, "in particular"** (`(LW_conclusion2)`, `3_5:393-397`):
`Ψ_t(r) = (W^{-c₀} B_{t, ⌊r⌋∧K})^{1/2}` for a constant `c₀ > 0` and `0 ≤ K ≤ L`.  The argument is the
real `r = |a-b|` of `LWClass`/`LWPsiRel`; `B_{t,m}` is the merged `Bparam`.  This is the lambda that
the probe's `LWtermB` (probe lines 970-973) passes to `LWClass` and `LWLoop2`. -/
def LWPhiB (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  fun n r => (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
    Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) ^ (1 / 2 : ℝ)

/-! ## 2. `(eq:Psi)` for the B class, and `Ψ_t(c r) ≲ Ψ_t(r)`

`B_{t,m} = A (m+1)^{-(d-2)} + B₀'` with `A = (g²+|1-t|)⁻¹ ≥ 0`, `B₀' = (L^d|1-t|)⁻¹ ≥ 0`.  Then
`B_{t,m}` is non-increasing in `m`, and `B_{t,m₁} ≤ ((m₂+1)/(m₁+1))^{d-2} B_{t,m₂}` for `m₁ ≤ m₂`.
No hypothesis on `t`, `g`, `L`, `W`, `K`, `c₀` is needed: the relations hold for every `n`. -/

section BLemmas

variable {d L : ℕ} {g t : ℝ}

private theorem LWPsi_B_nonneg (m : ℕ) : 0 ≤ Bparam d L g t m := by
  unfold Bparam; positivity

private theorem LWPsi_B_pos (hg : 0 < g) (m : ℕ) : 0 < Bparam d L g t m := by
  unfold Bparam
  have h1 : 0 < (g ^ 2 + |1 - t|)⁻¹ := inv_pos.mpr (by positivity)
  have h2 : 0 < (((m : ℝ) + 1) ^ (d - 2))⁻¹ := inv_pos.mpr (by positivity)
  have h3 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  nlinarith [mul_pos h1 h2]

private theorem LWPsi_B_anti {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    Bparam d L g t m₂ ≤ Bparam d L g t m₁ := by
  unfold Bparam
  have hm : ((m₁ : ℝ) + 1) ≤ (m₂ : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  have hpow : ((m₁ : ℝ) + 1) ^ (d - 2) ≤ ((m₂ : ℝ) + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hm _
  have hinv : (((m₂ : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (((m₁ : ℝ) + 1) ^ (d - 2))⁻¹ :=
    inv_anti₀ (by positivity) hpow
  have hc : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  linarith [mul_le_mul_of_nonneg_left hinv hc]

private theorem LWPsi_B_ratio {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    Bparam d L g t m₁ ≤ (((m₂ : ℝ) + 1) / ((m₁ : ℝ) + 1)) ^ (d - 2) * Bparam d L g t m₂ := by
  unfold Bparam
  rw [div_pow]
  have hm : ((m₁ : ℝ) + 1) ≤ (m₂ : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ h
  have hp1 : 0 < ((m₁ : ℝ) + 1) ^ (d - 2) := by positivity
  have hp12 : ((m₁ : ℝ) + 1) ^ (d - 2) ≤ ((m₂ : ℝ) + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hm _
  have hp2 : 0 < ((m₂ : ℝ) + 1) ^ (d - 2) := by positivity
  have hρ : 1 ≤ ((m₂ : ℝ) + 1) ^ (d - 2) / ((m₁ : ℝ) + 1) ^ (d - 2) := (one_le_div hp1).2 hp12
  have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have e : ((m₂ : ℝ) + 1) ^ (d - 2) / ((m₁ : ℝ) + 1) ^ (d - 2) *
      ((g ^ 2 + |1 - t|)⁻¹ * (((m₂ : ℝ) + 1) ^ (d - 2))⁻¹) =
      (g ^ 2 + |1 - t|)⁻¹ * (((m₁ : ℝ) + 1) ^ (d - 2))⁻¹ := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_right hρ hZ]

private theorem LWPsi_B_zero_le (m : ℕ) :
    Bparam d L g t 0 ≤ ((m : ℝ) + 1) ^ (d - 2) * Bparam d L g t m := by
  have := LWPsi_B_ratio (d := d) (L := L) (g := g) (t := t) (Nat.zero_le m)
  simpa using this

end BLemmas

private theorem LWPsi_phi_eq (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    LWPhiB sz c₀ K t n r = Real.sqrt (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
      Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊r⌋₊ (K n))) := by
  simp only [LWPhiB]; rw [Real.sqrt_eq_rpow]

private theorem LWPsi_w_nonneg (c₀ : ℝ) (n : ℕ) : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem LWPhiB_nonneg (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) (r : ℝ) :
    0 ≤ LWPhiB sz c₀ K t n r := by
  rw [LWPsi_phi_eq]; exact Real.sqrt_nonneg _

/-- The B class is non-increasing on `[0, ∞)`. -/
private theorem LWPhiB_antitone (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) :
    AntitoneOn (LWPhiB sz c₀ K t n) (Set.Ici 0) := by
  intro r₁ _ r₂ _ h
  rw [LWPsi_phi_eq, LWPsi_phi_eq]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (LWPsi_B_anti (min_le_min_right _ (Nat.floor_mono h))) (LWPsi_w_nonneg sz c₀ n))

/-- `Ψ_t(0) ≤ (C+1)^{(d-2)/2} Ψ_t(ℓ)` for `0 ≤ ℓ ≤ C`: the clause `Ψ_t(0) ≍ Ψ_t(ℓ)` of `(eq:Psi)`. -/
private theorem LWPhiB_zero_le (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) {C ℓ : ℝ} (hC : 0 ≤ C)
    (hℓ : 0 ≤ ℓ) (hℓC : ℓ ≤ C) :
    LWPhiB sz c₀ K t n 0 ≤ Real.sqrt ((C + 1) ^ (d - 2)) * LWPhiB sz c₀ K t n ℓ := by
  rw [LWPsi_phi_eq, LWPsi_phi_eq, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hm : ((min ⌊ℓ⌋₊ (K n) : ℕ) : ℝ) + 1 ≤ C + 1 := by
    have : ((min ⌊ℓ⌋₊ (K n) : ℕ) : ℝ) ≤ ℓ :=
      ((Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le hℓ))
    linarith
  have h1 := LWPsi_B_zero_le (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) (min ⌊ℓ⌋₊ (K n))
  have h2 : ((min ⌊ℓ⌋₊ (K n) : ℕ) + 1 : ℝ) ^ (d - 2) ≤ (C + 1) ^ (d - 2) :=
    pow_le_pow_left₀ (by positivity) hm _
  have hB := LWPsi_B_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) (min ⌊ℓ⌋₊ (K n))
  have hw := LWPsi_w_nonneg sz c₀ n
  simp only [Nat.floor_zero, Nat.zero_min]
  calc ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0
      ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) * (((min ⌊ℓ⌋₊ (K n) : ℕ) + 1 : ℝ) ^ (d - 2) *
          Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ⌋₊ (K n))) :=
        mul_le_mul_of_nonneg_left h1 hw
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) * ((C + 1) ^ (d - 2) *
          Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ⌋₊ (K n))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hB) hw
    _ = (C + 1) ^ (d - 2) * (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
          Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ⌋₊ (K n))) := by ring

private theorem LWPsi_floor_ratio (K : ℕ) {ℓ₁ ℓ₂ : ℝ} (h1 : 1 ≤ ℓ₁) (h12 : ℓ₁ ≤ ℓ₂) :
    (((min ⌊ℓ₂⌋₊ K : ℕ) : ℝ) + 1) / (((min ⌊ℓ₁⌋₊ K : ℕ) : ℝ) + 1) ≤ 2 * (ℓ₂ / ℓ₁) := by
  have hℓ1 : 0 < ℓ₁ := by linarith
  have hx : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div hℓ1).2 h12
  by_cases hK : K ≤ ⌊ℓ₁⌋₊
  · rw [min_eq_right hK, min_eq_right (hK.trans (Nat.floor_mono h12))]
    rw [div_self (by positivity)]
    linarith
  · push Not at hK
    rw [min_eq_left hK.le]
    have hm2 : ((min ⌊ℓ₂⌋₊ K : ℕ) : ℝ) ≤ ℓ₂ :=
      (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (by linarith))
    have hlt : ℓ₁ < (⌊ℓ₁⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ℓ₁
    calc (((min ⌊ℓ₂⌋₊ K : ℕ) : ℝ) + 1) / ((⌊ℓ₁⌋₊ : ℝ) + 1) ≤ (2 * ℓ₂) / ℓ₁ :=
          div_le_div₀ (by linarith) (by linarith) hℓ1 hlt.le
      _ = 2 * (ℓ₂ / ℓ₁) := by ring

/-- The ratio bound of the B class: `Ψ_t(ℓ₁) ≤ ((2 ℓ₂/ℓ₁)^{d-2})^{1/2} Ψ_t(ℓ₂)` for `1 ≤ ℓ₁ ≤ ℓ₂`. -/
private theorem LWPhiB_ratio (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) {ℓ₁ ℓ₂ : ℝ} (h1 : 1 ≤ ℓ₁)
    (h12 : ℓ₁ ≤ ℓ₂) :
    LWPhiB sz c₀ K t n ℓ₁ ≤ Real.sqrt ((2 * (ℓ₂ / ℓ₁)) ^ (d - 2)) * LWPhiB sz c₀ K t n ℓ₂ := by
  have hℓ1 : 0 < ℓ₁ := by linarith
  have hx : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div hℓ1).2 h12
  rw [LWPsi_phi_eq, LWPsi_phi_eq, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have hm : min ⌊ℓ₁⌋₊ (K n) ≤ min ⌊ℓ₂⌋₊ (K n) := min_le_min_right _ (Nat.floor_mono h12)
  have hρ := LWPsi_floor_ratio (K n) h1 h12
  have hB : Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ₁⌋₊ (K n)) ≤
      (2 * (ℓ₂ / ℓ₁)) ^ (d - 2) * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ₂⌋₊ (K n)) :=
    (LWPsi_B_ratio hm).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) hρ _) (LWPsi_B_nonneg _))
  calc ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ₁⌋₊ (K n))
      ≤ ((sz.W n : ℕ) : ℝ) ^ (-c₀) * ((2 * (ℓ₂ / ℓ₁)) ^ (d - 2) *
          Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ₂⌋₊ (K n))) :=
        mul_le_mul_of_nonneg_left hB (LWPsi_w_nonneg sz c₀ n)
    _ = (2 * (ℓ₂ / ℓ₁)) ^ (d - 2) * (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
          Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊ℓ₂⌋₊ (K n))) := by ring

/-- **`(eq:Psi)` for the B class** (`3_5:391`), general `d ≥ 2` (in particular `d ≥ 3`): `Ψ_t` is non-increasing,
`Ψ_t(0) ≤ ((C+1)^{d-2})^{1/2} Ψ_t(ℓ)` for `0 ≤ ℓ ≤ C` (every `C > 1`), and
`Ψ_t(ℓ₁) ≤ 2^d (ℓ₂/ℓ₁)^d Ψ_t(ℓ₂)` for `ℓ₂ ≥ ℓ₁ ≥ 1`, with `C₁ = 2^d > 1`, `C₂ = d > 1`.  Deterministic:
no hypothesis on `t`, `g`, `L`, `W`, `K`, `c₀`; the relations hold for every `n`. -/
theorem LWPhiB_psiRel (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel ((2 : ℝ) ^ d) (d : ℝ) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) := by
  refine ⟨LWPhiB_antitone sz c₀ K t, one_lt_pow₀ (by norm_num) (by omega), ?_, fun C hC => ?_, ?_⟩
  · exact_mod_cast (by omega : 1 < d)
  · exact Eventually.of_forall fun n ℓ hℓ hℓC => LWPhiB_zero_le sz c₀ K t n (by linarith) hℓ hℓC
  · refine Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_
    have hℓ1 : 0 < ℓ₁ := by linarith
    have hx : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div hℓ1).2 h12
    refine (LWPhiB_ratio sz c₀ K t n h1 h12).trans (mul_le_mul_of_nonneg_right ?_
      (LWPhiB_nonneg sz c₀ K t n ℓ₂))
    rw [Real.rpow_natCast]
    have hy : 1 ≤ 2 * (ℓ₂ / ℓ₁) := by linarith
    have hy2 : 1 ≤ (2 * (ℓ₂ / ℓ₁)) ^ (d - 2) := one_le_pow₀ hy
    have h3 : Real.sqrt ((2 * (ℓ₂ / ℓ₁)) ^ (d - 2)) ≤ (2 * (ℓ₂ / ℓ₁)) ^ (d - 2) := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    calc Real.sqrt ((2 * (ℓ₂ / ℓ₁)) ^ (d - 2)) ≤ (2 * (ℓ₂ / ℓ₁)) ^ (d - 2) := h3
      _ ≤ (2 * (ℓ₂ / ℓ₁)) ^ d := pow_le_pow_right₀ hy (by omega)
      _ = 2 ^ d * (ℓ₂ / ℓ₁) ^ d := mul_pow _ _ _

/-- **`(eq:Psi)` for the B class with `(C₁, C₂) = (2, 2)` at `d = 3`** (the constants of the ticket;
`√(2 x) ≤ 2 x²` for `x ≥ 1`). -/
theorem LWPhiB_psiRel_three (hd : d = 3) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) :
    LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) := by
  refine ⟨LWPhiB_antitone sz c₀ K t, by norm_num, by norm_num, fun C hC => ?_, ?_⟩
  · exact Eventually.of_forall fun n ℓ hℓ hℓC => LWPhiB_zero_le sz c₀ K t n (by linarith) hℓ hℓC
  · refine Eventually.of_forall fun n ℓ₁ ℓ₂ h1 h12 => ?_
    have hℓ1 : 0 < ℓ₁ := by linarith
    have hx : 1 ≤ ℓ₂ / ℓ₁ := (one_le_div hℓ1).2 h12
    refine (LWPhiB_ratio sz c₀ K t n h1 h12).trans (mul_le_mul_of_nonneg_right ?_
      (LWPhiB_nonneg sz c₀ K t n ℓ₂))
    rw [Real.rpow_two, hd, show 3 - 2 = 1 from rfl, pow_one, Real.sqrt_le_left (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hx), pow_pos (by linarith : (0 : ℝ) < ℓ₂ / ℓ₁) 3,
      pow_pos (by linarith : (0 : ℝ) < ℓ₂ / ℓ₁) 2]

/-- The shift step, from the clauses of `(eq:Psi)` and `Ψ_t ≥ 0` (shared by `LWPsiAll.shift` and
`LWPhiB_shift`): `c ≥ 1` by monotonicity; `c < 1`, `c r ≥ 1` by the ratio bound with `C₁ c^{-C₂}`;
`c r < 1` by `Ψ_t(0) ≍ Ψ_t(ℓ)` for `ℓ ≤ max 2 c⁻¹`. -/
private theorem LWPsi_shift_aux {C₁ C₂ : ℝ} {Cc : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (hnn : ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → 0 ≤ Φ n r)
    (hanti : ∀ n, AntitoneOn (Φ n) (Set.Ici 0)) (hC₁ : 1 < C₁) (_hC₂ : 1 < C₂)
    (hrel1 : ∀ C : ℝ, 1 < C → ∀ᶠ n in atTop, ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ C → Φ n 0 ≤ Cc C * Φ n ℓ)
    (hrel2 : ∀ᶠ n in atTop, ∀ ℓ₁ ℓ₂ : ℝ, 1 ≤ ℓ₁ → ℓ₁ ≤ ℓ₂ → Φ n ℓ₁ ≤ C₁ * (ℓ₂ / ℓ₁) ^ C₂ * Φ n ℓ₂)
    {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ n (c * r) ≤ K * Φ n r := by
  by_cases hc1 : 1 ≤ c
  · refine ⟨1, one_pos, Eventually.of_forall fun n r hr => ?_⟩
    rw [one_mul]
    exact hanti n (Set.mem_Ici.mpr hr) (Set.mem_Ici.mpr (by positivity)) (by nlinarith)
  · push Not at hc1
    set C : ℝ := max 2 c⁻¹ with hCdef
    have hC1 : 1 < C := lt_of_lt_of_le one_lt_two (le_max_left _ _)
    have hK1 : 0 < C₁ * (c⁻¹) ^ C₂ := mul_pos (by linarith) (Real.rpow_pos_of_pos (inv_pos.mpr hc) _)
    refine ⟨max (C₁ * (c⁻¹) ^ C₂) (Cc C), lt_of_lt_of_le hK1 (le_max_left _ _), ?_⟩
    filter_upwards [hnn, hrel1 C hC1, hrel2] with n hp h1 h2
    intro r hr
    by_cases hcr : 1 ≤ c * r
    · have hr0 : 0 < r := by
        by_contra hr0; push Not at hr0
        have : r = 0 := le_antisymm hr0 hr
        rw [this] at hcr; simp at hcr; linarith
      have hle : c * r ≤ r := by nlinarith
      have := h2 (c * r) r hcr hle
      have hdiv : r / (c * r) = c⁻¹ := by field_simp
      rw [hdiv] at this
      calc Φ n (c * r) ≤ C₁ * (c⁻¹) ^ C₂ * Φ n r := this
        _ ≤ max (C₁ * (c⁻¹) ^ C₂) (Cc C) * Φ n r :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hp r hr)
    · push Not at hcr
      have hr1 : r ≤ C := by
        have : r < c⁻¹ :=
          calc r = c⁻¹ * (c * r) := by field_simp
            _ < c⁻¹ * 1 := mul_lt_mul_of_pos_left hcr (inv_pos.mpr hc)
            _ = c⁻¹ := mul_one _
        exact (this.le).trans (le_max_right _ _)
      calc Φ n (c * r) ≤ Φ n 0 := hanti n (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by positivity))
              (by positivity)
        _ ≤ Cc C * Φ n r := h1 r hr hr1
        _ ≤ max (C₁ * (c⁻¹) ^ C₂) (Cc C) * Φ n r :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hp r hr)

/-- **`(eq:Psi)` gives `Ψ_t(c r) ≲ Ψ_t(r)`** for every fixed `c > 0` (`7_8:86`, "the second step uses
the condition `(eq:Psi)`"): same statement as the probe's `LWPsiAll.shift` (probe line 1200). -/
theorem LWPsiAll.shift {ε₀ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h : LWPsiAll sz ε₀ C₁ C₂ C₃ Cc Φ) {c : ℝ} (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r → Φ n (c * r) ≤ K * Φ n r := by
  obtain ⟨-, ⟨hpos, -, -⟩, hanti, hC₁, hC₂, hrel1, hrel2⟩ := h
  exact LWPsi_shift_aux (hpos.mono fun n hn r hr => (hn r hr).1.le) hanti hC₁ hC₂ hrel1 hrel2 hc

/-- **`Ψ_t(c r) ≲ Ψ_t(r)` for the B class**, every fixed `c > 0`, with no hypothesis on the data and a
constant independent of `n`: `K_c = max(2^d c^{-d}, ((max 2 c⁻¹ + 1)^{d-2})^{1/2})` (`c < 1`) and `1` (`c ≥ 1`);
`d = 3`: `c = 1/4` gives `32`, `c = 1/2` gives `8`. -/
theorem LWPhiB_shift (hd : 2 ≤ d) (c₀ : ℝ) (K : ℕ → ℕ) (t : ℕ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz c₀ K t n (c * r) ≤ Kc * LWPhiB sz c₀ K t n r := by
  obtain ⟨-, hC₁, hC₂, hrel1, hrel2⟩ := LWPhiB_psiRel sz hd c₀ K t
  exact LWPsi_shift_aux (Eventually.of_forall fun n r _ => LWPhiB_nonneg sz c₀ K t n r)
    (LWPhiB_antitone sz c₀ K t) hC₁ hC₂ hrel1 hrel2 hc

/-! ## 3. The window `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` (paper-delta T2040a)

`7_8:65` takes `Ψ_t = (W^{-d}B_{t,0})^{1/2}`, but `W^{-d/2} ≤ (W^{-d}B_{t,0})^{1/2}` holds iff `B_{t,0} ≥ 1`
and `B_{t,0} < 1` happens (`g² + |1-t| > 1`).  Two repairs, both proved here: the control parameter
`Ψ_t := max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})`, and for the B class the constant `C₃ = (1+Λ²)^{1/2}` of
`LWClass`.  The upper side `Ψ_t ≤ W^{-ε₀}` is not deterministic (it fails for `W = 2`, `g = 0.1`,
`t = 1 - g²/(4L²)`): it is the data hypothesis `W^{-c₀} B_{t,0} ≤ W^{-2ε₀}` (eventually). -/

private theorem LWPsi_rpow_sq {x a : ℝ} (hx : 0 ≤ x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; congr 1; push_cast; ring

private theorem LWPsi_one_le_W (n : ℕ) : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) :=
  Nat.one_le_cast.2 (sz.W_pos n)

/-- **The window for `Ψ_t = max(W^{-d/2}, Φ(0))`**: for any `Φ(0) ≤ W^{-ε₀}` (eventually) and `ε₀ ≤ d/2`. -/
theorem LWWindow_max {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) {Φ₀ : ℕ → ℝ}
    (h : ∀ᶠ n in atTop, Φ₀ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ₀ n)) := by
  filter_upwards [h] with n hn
  refine ⟨le_max_left _ _, max_le ?_ hn⟩
  exact Real.rpow_le_rpow_of_exponent_le (LWPsi_one_le_W sz n) (by linarith)

/-- **The window of T2040a**: `Ψ_t = max(W^{-d/2}, (W^{-d}B_{t,0})^{1/2})` (`W^{-d}B_{t,0}` is the merged
`Bctl`) satisfies `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}` iff (given `ε₀ ≤ d/2`) `√Bctl ≤ W^{-ε₀}` eventually;
sufficient: `Bctl n (t n) ≤ W^{-2ε₀}` eventually. -/
theorem LWWindow_max_Bctl {ε₀ : ℝ} (hε : ε₀ ≤ (d : ℝ) / 2) (t : ℕ → ℝ)
    (h : ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWWindow sz ε₀ (fun n => max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) := by
  refine LWWindow_max sz hε ?_
  filter_upwards [h] with n hn
  rw [Real.sqrt_le_left (Real.rpow_nonneg (Nat.cast_nonneg _) _), LWPsi_rpow_sq (Nat.cast_nonneg _), show (2 : ℝ) * -ε₀ = -2 * ε₀ by ring]
  exact hn

/-- `Ψ_t ≍ Φ(0)`: with `LWClass` (the constant `C₃`), `max(W^{-d/2}, Φ(0)) ≤ max(1, C₃) Φ(0)`. -/
theorem LWPsiMax_asymp {ε₀ C₃ : ℝ} {Φ : ℕ → ℝ → ℝ} (h : LWClass sz ε₀ C₃ Φ) :
    ∀ᶠ n in atTop, Φ n 0 ≤ max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ n 0) ∧
      max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Φ n 0) ≤ max 1 C₃ * Φ n 0 := by
  obtain ⟨h1, -, h3⟩ := h
  filter_upwards [h1, h3] with n hn1 hn3
  have hp : 0 < Φ n 0 := (hn1 0 le_rfl).1
  refine ⟨le_max_right _ _, max_le ?_ ?_⟩
  · exact hn3.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le)
  · exact le_mul_of_one_le_left hp.le (le_max_left _ _)

/-- **The B class satisfies `LWClass` for `c₀ ≤ d`** (positivity, `Ψ_t ≤ W^{-ε₀}`, `W^{-d/2} ≤ C₃ Ψ_t(0)`):
with `0 ≤ t ≤ 1`, `0 < g ≤ Λ` (eventually) and the data hypothesis `W^{-c₀} B_{t,0} ≤ W^{-2ε₀}`
(eventually), the constant is `C₃ = (1+Λ²)^{1/2}`, independent of `W, L, K, t`. -/
theorem LWClass_B {ε₀ c₀ Λ : ℝ} (K : ℕ → ℕ) (t : ℕ → ℝ) (hc₀ : c₀ ≤ (d : ℝ))
    (hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ) (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1)
    (hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWClass sz ε₀ (Real.sqrt (1 + Λ ^ 2)) (LWPhiB sz c₀ K t) := by
  refine ⟨?_, Real.sqrt_pos.2 (by positivity), ?_⟩
  · filter_upwards [hg, hup] with n hn hu r hr
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by have := LWPsi_one_le_W sz n; linarith
    have hw : 0 < ((sz.W n : ℕ) : ℝ) ^ (-c₀) := Real.rpow_pos_of_pos hW0 _
    refine ⟨?_, ?_⟩
    · rw [LWPsi_phi_eq]
      exact Real.sqrt_pos.2 (mul_pos hw (LWPsi_B_pos hn.1 _))
    · calc LWPhiB sz c₀ K t n r ≤ LWPhiB sz c₀ K t n 0 :=
            LWPhiB_antitone sz c₀ K t n (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀) := by
            rw [LWPsi_phi_eq, Real.sqrt_le_left (Real.rpow_nonneg hW0.le _),
              LWPsi_rpow_sq hW0.le, show (2 : ℝ) * -ε₀ = -2 * ε₀ by ring]
            simpa using hu
  · filter_upwards [hg, ht] with n hn htn
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by have := LWPsi_one_le_W sz n; linarith
    have hw : 0 < ((sz.W n : ℕ) : ℝ) ^ (-c₀) := Real.rpow_pos_of_pos hW0 _
    have hB0 : Bparam d (sz.L n) (sz.lam n) (t n) 0 =
        (sz.lam n ^ 2 + |1 - t n|)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹ := by
      simp [Bparam]
    have habs : |1 - t n| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith [htn.1]
    have hg2 : sz.lam n ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hn.1.le hn.2 2
    have hpos : 0 < sz.lam n ^ 2 + |1 - t n| := by
      have := hn.1; positivity
    have hA : (1 + Λ ^ 2)⁻¹ ≤ (sz.lam n ^ 2 + |1 - t n|)⁻¹ := inv_anti₀ hpos (by linarith)
    have hZ : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹ := by positivity
    have hΛ : 0 < 1 + Λ ^ 2 := by positivity
    have hB1 : 1 ≤ (1 + Λ ^ 2) * Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
      rw [hB0]
      calc (1 : ℝ) = (1 + Λ ^ 2) * (1 + Λ ^ 2)⁻¹ := (mul_inv_cancel₀ hΛ.ne').symm
        _ ≤ (1 + Λ ^ 2) * ((sz.lam n ^ 2 + |1 - t n|)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹) :=
          mul_le_mul_of_nonneg_left (by linarith) hΛ.le
    have hsq : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Real.sqrt (((sz.W n : ℕ) : ℝ) ^ (-c₀)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hW0.le]
      exact Real.rpow_le_rpow_of_exponent_le (LWPsi_one_le_W sz n) (by linarith)
    calc ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Real.sqrt (((sz.W n : ℕ) : ℝ) ^ (-c₀)) := hsq
      _ ≤ Real.sqrt ((1 + Λ ^ 2) * (((sz.W n : ℕ) : ℝ) ^ (-c₀) *
            Bparam d (sz.L n) (sz.lam n) (t n) 0)) := by
          apply Real.sqrt_le_sqrt
          nlinarith [mul_le_mul_of_nonneg_left hB1 hw.le]
      _ = Real.sqrt (1 + Λ ^ 2) * LWPhiB sz c₀ K t n 0 := by
          rw [LWPsi_phi_eq, Real.sqrt_mul hΛ.le]
          simp

/-- **`LWPsiAll` for the B class**: positivity, window and `(eq:Psi)` of `lem:LWterm`, with
`(C₁, C₂, C₃, Cc) = (2^d, d, (1+Λ²)^{1/2}, C ↦ ((C+1)^{d-2})^{1/2})`; the hypotheses are the data conditions
of `LWClass_B`; `(eq:Psi)` is unconditional. -/
theorem LWPhiB_psiAll (hd : 2 ≤ d) {ε₀ c₀ Λ : ℝ} (K : ℕ → ℕ) (t : ℕ → ℝ) (hε : 0 < ε₀)
    (hc₀ : c₀ ≤ (d : ℝ)) (hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1)
    (hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-c₀) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₀)) :
    LWPsiAll sz ε₀ ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + Λ ^ 2))
      (fun C => Real.sqrt ((C + 1) ^ (d - 2))) (LWPhiB sz c₀ K t) :=
  ⟨hε, LWClass_B sz K t hc₀ hg ht hup, LWPhiB_psiRel sz hd c₀ K t⟩

end RBM.Gauss.Sizes

/-! ## 4. `W^{-d} 𝒯̃ ≍ [s𝒯]²` for `r ≤ L` (paper-delta T2040k)

`7_8:20-30`: `[s𝒯_t(r)]² = W^{-d} (g²+|1-t|)⁻¹ (r+1)^{-(d-2)} e^{-√(r/ℓ_t)}` (`sfT d L W g t r`, squared) and
`W^{-d} 𝒯_t(r) = W^{-d} (B_{t,r}) e^{-√(r/ℓ_t)}`.

* Regime `1 - t ≥ g²/L²`: for `0 ≤ r ≤ L`, `[s𝒯]² ≤ W^{-d} 𝒯 ≤ (1 + 2^{d-1}) [s𝒯]²`
  (the zero-mode term of `B` is dominated, merged `zeroMode_le_of_ge`); truncated:
  `W^{-d} wT^ℓ_{t,D}(r) ≍ [s𝒯_t(r ∧ ℓ)]² + W^{-d} W^{-D}` with constants `1/2` and `1 + 2^{d-1}`.
  The paper's `W^{-D}` is `W^{-d-D}` here (`D ↦ D + d`; `wT = max(𝒯, W^{-D})` carries no `W^{-d}`).
* Regime `1 - t ≤ g²/L²`: `ℓ_t = L`, and `e⁻¹ B_{t,r} ≤ 𝒯_t(r) ≤ B_{t,r}`; there `[s𝒯]²` is *not*
  comparable (the zero-mode term `(L^d|1-t|)⁻¹` of `B` is unbounded as `t → 1`), so the comparison is
  with `B_{t,r}`, as `lem:LWterm` needs. -/

namespace RBM

open Real

private theorem LWPsi_sfT_sq {d L : ℕ} {W g t : ℝ} (hW : 0 < W) {r : ℝ} (hr : 0 ≤ r) :
    sfT d L W g t r ^ 2 = (W ^ d)⁻¹ * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) *
      Real.exp (-Real.sqrt (r / ellT L g t)) := by
  unfold sfT
  have h1 : 0 ≤ (W ^ d)⁻¹ := by positivity
  have h2 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have h3 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
  have h4 : Real.exp (-(1 / 2) * √(r / ellT L g t)) ^ 2 = Real.exp (-√(r / ellT L g t)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h3, h4]
  ring

/-- **`W^{-d} 𝒯_t(r) ≍ [s𝒯_t(r)]²`**, regime `1 - t ≥ g²/L²`, `0 ≤ r ≤ L`: constants `1` and `1 + 2^{d-1}`
(`d = 3`: `5`), independent of `g`, `W`, `L`, `t`. -/
theorem tailT_regime1_bounds {d L : ℕ} {W g t : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1)
    (hW : 0 < W) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    sfT d L W g t r ^ 2 ≤ (W ^ d)⁻¹ * tailT d L g t r ∧
      (W ^ d)⁻¹ * tailT d L g t r ≤ (1 + 2 ^ (d - 1)) * sfT d L W g t r ^ 2 := by
  rw [LWPsi_sfT_sq hW hr0]
  have hz := zeroMode_le_of_ge hd hL ht hr0 hrL hgt
  have hV : 0 < (W ^ d)⁻¹ := by positivity
  have hE : 0 < Real.exp (-Real.sqrt (r / ellT L g t)) := Real.exp_pos _
  have hZ : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have h := mul_le_mul_of_nonneg_left hz (mul_nonneg hV.le hE.le)
  have h' := mul_nonneg (mul_nonneg hV.le hE.le) hZ
  simp only [tailT, BparamR]
  constructor <;> nlinarith [h, h']

/-- **Truncated form** (regime `1 - t ≥ g²/L²`, `0 ≤ ℓ ≤ L`, any `r ≥ 0`):
`½([s𝒯_t(r∧ℓ)]² + W^{-d}W^{-D}) ≤ W^{-d} wT^ℓ_{t,D}(r) ≤ (1+2^{d-1})([s𝒯_t(r∧ℓ)]² + W^{-d}W^{-D})`. -/
theorem tailW_regime1_bounds {d L : ℕ} {W g t ℓ D : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1)
    (hW : 0 < W) (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    (1 / 2) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) ≤
        (W ^ d)⁻¹ * tailW d L g t ℓ W D r ∧
      (W ^ d)⁻¹ * tailW d L g t ℓ W D r ≤
        (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r ℓ) ^ 2 + (W ^ d)⁻¹ * W ^ (-D)) := by
  obtain ⟨h1, h2⟩ := tailT_regime1_bounds (d := d) (L := L) (W := W) (g := g) (t := t) hd hL ht hW hgt
    (le_min hr hℓ0) ((min_le_right _ _).trans hℓL)
  have hV : 0 < (W ^ d)⁻¹ := by positivity
  have hb : 0 ≤ (W ^ d)⁻¹ * W ^ (-D) := mul_nonneg hV.le (Real.rpow_nonneg hW.le _)
  have hs : 0 ≤ sfT d L W g t (min r ℓ) ^ 2 := sq_nonneg _
  have hc : (1 : ℝ) ≤ 1 + 2 ^ (d - 1) := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (d - 1)]
  have e : (W ^ d)⁻¹ * tailW d L g t ℓ W D r =
      max ((W ^ d)⁻¹ * tailT d L g t (min r ℓ)) ((W ^ d)⁻¹ * W ^ (-D)) := by
    unfold tailW; exact mul_max_of_nonneg _ _ hV.le
  rw [e]
  constructor
  · linarith [le_max_left ((W ^ d)⁻¹ * tailT d L g t (min r ℓ)) ((W ^ d)⁻¹ * W ^ (-D)),
      le_max_right ((W ^ d)⁻¹ * tailT d L g t (min r ℓ)) ((W ^ d)⁻¹ * W ^ (-D))]
  · refine max_le ?_ ?_
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 ^ (d - 1)) hb]
    · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 ^ (d - 1) - 1) hb,
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 2 ^ (d - 1)) hs]

/-- Regime `1 - t ≤ g²/L²` (`ℓ_t = L`), `r ≤ L`: `e⁻¹ B_{t,r} ≤ 𝒯_t(r) ≤ B_{t,r}`. -/
theorem tailT_regime2_bounds {d L : ℕ} {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) {r : ℝ} (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    Real.exp (-1) * BparamR d L g t r ≤ tailT d L g t r ∧ tailT d L g t r ≤ BparamR d L g t r := by
  have hB := BparamR_nonneg (d := d) (L := L) (g := g) (t := t) hr0
  have hex := exp_tail_ge hg ht hL h hrL
  have hle : Real.exp (-Real.sqrt (r / ellT L g t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (Real.sqrt_nonneg _))
  unfold tailT
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hex hB]
  · nlinarith [mul_le_mul_of_nonneg_left hle hB]

/-- Truncated form of regime `1 - t ≤ g²/L²`, `0 ≤ ℓ ≤ L`, any `r ≥ 0`:
`max(e⁻¹ B_{t,r∧ℓ}, W^{-D}) ≤ wT^ℓ_{t,D}(r) ≤ max(B_{t,r∧ℓ}, W^{-D})`. -/
theorem tailW_regime2_bounds {d L : ℕ} {W g t ℓ D : ℝ} (hg : 0 ≤ g) (ht : t < 1) (hL : 1 ≤ (L : ℝ))
    (h : 1 - t ≤ g ^ 2 / (L : ℝ) ^ 2) (hℓ0 : 0 ≤ ℓ) (hℓL : ℓ ≤ L) {r : ℝ} (hr : 0 ≤ r) :
    max (Real.exp (-1) * BparamR d L g t (min r ℓ)) (W ^ (-D)) ≤ tailW d L g t ℓ W D r ∧
      tailW d L g t ℓ W D r ≤ max (BparamR d L g t (min r ℓ)) (W ^ (-D)) := by
  obtain ⟨h1, h2⟩ := tailT_regime2_bounds (d := d) (L := L) hg ht hL h (le_min hr hℓ0)
    ((min_le_right _ _).trans hℓL)
  exact ⟨max_le_max h1 le_rfl, max_le_max h2 le_rfl⟩

end RBM

/-! ## 5. Compiled nonempty instances at `d = 3`

The merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`,
`lam_n = (2(n+1))^{-6}`), `Λ = 1`, `c₀ = 3 = d`, `ε₀ = 1/5`, `K_n = L_n`, at the two times of the
ticket: `t ≡ 1/16` (`tInst`) and `t = 1 - W^{-2}` (`tW`).  Every deterministic hypothesis is discharged
(for all `n`).  The tail comparisons are applied at `r = 2`, `ℓ = 3`, `D = 1` (`≤ L_n`, `L_n ≥ 4`).  Regime 1
(`1 - t ≥ g²/L²`) holds at both times for all `n`; regime 2 (`1 - t ≤ g²/L²`) is empty at both
(`1 - t ≥ W^{-2} > g²/L²`), so its instance is at `n = 0` (`L = 4`, `g = 1/64`) with `t = 1 - 2^{-17}`. -/

namespace RBM.Gauss.LWPsiInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

/-- The second time of the ticket: `t_n = 1 - W_n^{-2}`. -/
def tW : ℕ → ℝ := fun n => 1 - (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹

theorem W_pos' (n : ℕ) : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by have := W_ge_32 n; linarith

theorem lam_pos (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity

theorem two_le_x (n : ℕ) : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
  have := Nat.cast_nonneg (α := ℝ) n; linarith

theorem lam_le_64 (n : ℕ) : sz0.lam n ≤ 1 / 64 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
  have h : (64 : ℝ) ≤ (2 * ((n : ℝ) + 1)) ^ 6 :=
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (two_le_x n) 6
  calc ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h
    _ = 1 / 64 := by norm_num

theorem lam_le_Winv (n : ℕ) : sz0.lam n ≤ ((sz0.W n : ℕ) : ℝ)⁻¹ := by
  have hW : ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 := by simp [sz0]
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ _
  rw [hW]
  exact inv_anti₀ (by have := two_le_x n; positivity)
    (pow_le_pow_right₀ (by have := two_le_x n; linarith) (by norm_num))

theorem L_ge_4 (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  have : 4 ≤ sz0.L n := by change 4 ≤ 4 * (n + 1); omega
  exact_mod_cast this

theorem Winv_sq_le (n : ℕ) : (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 / 1024 := by
  have h := W_ge_32 n
  calc (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ ((32 : ℝ) ^ 2)⁻¹ :=
        inv_anti₀ (by norm_num) (pow_le_pow_left₀ (by norm_num) h 2)
    _ = 1 / 1024 := by norm_num

/-- `0 ≤ t ≤ 1` and `W^{-2} ≤ |1-t|` at `t ≡ 1/16`. -/
theorem tInst_ok (n : ℕ) :
    0 ≤ tInst n ∧ tInst n ≤ 1 ∧ (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ |1 - tInst n| := by
  have := Winv_sq_le n
  refine ⟨by simp [tInst], by simp [tInst]; norm_num, ?_⟩
  simp only [tInst]; rw [abs_of_pos (by norm_num)]; linarith

/-- `0 ≤ t ≤ 1` and `W^{-2} ≤ |1-t|` at `t = 1 - W^{-2}` (equality). -/
theorem tW_ok (n : ℕ) :
    0 ≤ tW n ∧ tW n ≤ 1 ∧ (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ |1 - tW n| := by
  have := Winv_sq_le n
  have hp : 0 ≤ (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ := by have := W_pos' n; positivity
  refine ⟨by simp only [tW]; linarith, by simp only [tW]; linarith, ?_⟩
  simp only [tW, sub_sub_cancel]; rw [abs_of_nonneg hp]

theorem B0_le {d L : ℕ} {g t w : ℝ} (hL : 1 ≤ (L : ℝ)) (hw : 0 < w) (hu : w ≤ |1 - t|) :
    Bparam d L g t 0 ≤ 2 * w⁻¹ := by
  have hu0 : 0 < |1 - t| := hw.trans_le hu
  have h1 : (g ^ 2 + |1 - t|)⁻¹ ≤ w⁻¹ :=
    inv_anti₀ hw (by nlinarith [sq_nonneg g])
  have h2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ w⁻¹ :=
    inv_anti₀ hw (by nlinarith [one_le_pow₀ (n := d) hL])
  have : Bparam d L g t 0 = (g ^ 2 + |1 - t|)⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹ := by simp [Bparam]
  linarith

/-- `W^{-3} B_{t,0} ≤ W^{-2/5}` at `sz0`, for every `n` and every `t` with `W^{-2} ≤ |1-t|`. -/
theorem upper_core (n : ℕ) {t : ℝ} (hu : (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ ≤ |1 - t|) :
    ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) t 0 ≤
      ((sz0.W n : ℕ) : ℝ) ^ (-2 * (1 / 5 : ℝ)) := by
  have hW0 := W_pos' n
  have h32 := W_ge_32 n
  have hL : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by have := L_ge_4 n; linarith
  have hB := B0_le (d := 3) (g := sz0.lam n) hL (inv_pos.2 (pow_pos hW0 2)) hu
  rw [inv_inv] at hB
  have h35 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (3 / 5 : ℝ) :=
    calc (2 : ℝ) ≤ Real.sqrt 32 := Real.le_sqrt_of_sq_le (by norm_num)
      _ = (32 : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow 32
      _ ≤ (32 : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (3 / 5 : ℝ) := Real.rpow_le_rpow (by norm_num) h32 (by norm_num)
  have e : ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) * ((sz0.W n : ℕ) : ℝ) ^ 2 =
      ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_natCast ((sz0.W n : ℕ) : ℝ) 2, ← Real.rpow_add hW0]; norm_num
  have e2 : ((sz0.W n : ℕ) : ℝ) ^ (3 / 5 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) =
      ((sz0.W n : ℕ) : ℝ) ^ (-2 * (1 / 5 : ℝ)) := by
    rw [← Real.rpow_add hW0]; norm_num
  have hpos : 0 < ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos hW0 _
  calc ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) t 0
      ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) * (2 * ((sz0.W n : ℕ) : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hW0.le _)
    _ = 2 * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by rw [← e]; ring
    _ ≤ ((sz0.W n : ℕ) : ℝ) ^ (3 / 5 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
        mul_le_mul_of_nonneg_right h35 hpos.le
    _ = _ := e2

theorem Bctl_eq (n : ℕ) (t : ℝ) :
    sz0.Bctl n t = ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ)) * Bparam 3 (sz0.L n) (sz0.lam n) t 0 := by
  unfold Sizes.Bctl
  congr 1
  rw [Real.rpow_neg (W_pos' n).le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem hgt_tInst (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 - tInst n := by
  have hL := L_ge_4 n
  rw [div_le_iff₀ (by positivity)]
  have h1 : sz0.lam n ^ 2 ≤ 1 / 4096 := by nlinarith [lam_le_64 n, lam_pos n]
  have h2 : 16 ≤ ((sz0.L n : ℕ) : ℝ) ^ 2 := by nlinarith
  simp only [tInst]; nlinarith

theorem hgt_tW (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 - tW n := by
  have hL := L_ge_4 n
  have hW := W_pos' n
  rw [div_le_iff₀ (by positivity)]
  have h1 : sz0.lam n ^ 2 ≤ (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [← inv_pow]; exact pow_le_pow_left₀ (lam_pos n).le (lam_le_Winv n) 2
  have h2 : 1 ≤ ((sz0.L n : ℕ) : ℝ) ^ 2 := by nlinarith
  have hp : 0 ≤ (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  simp only [tW, sub_sub_cancel]; nlinarith

/-! ### `(eq:Psi)` for the B class (every `K`, every `t`) -/

theorem inst_psiRel (t : ℕ → ℝ) (K : ℕ → ℕ) :
    LWPsiRel ((2 : ℝ) ^ 3) ((3 : ℕ) : ℝ) (fun C => Real.sqrt ((C + 1) ^ (3 - 2)))
      (LWPhiB sz0 3 K t) :=
  LWPhiB_psiRel sz0 (by norm_num) 3 K t

theorem inst_psiRel_tInst : LWPsiRel ((2 : ℝ) ^ 3) ((3 : ℕ) : ℝ)
    (fun C => Real.sqrt ((C + 1) ^ (3 - 2))) (LWPhiB sz0 3 (fun n => sz0.L n) tInst) :=
  inst_psiRel tInst _

theorem inst_psiRel_tW : LWPsiRel ((2 : ℝ) ^ 3) ((3 : ℕ) : ℝ)
    (fun C => Real.sqrt ((C + 1) ^ (3 - 2))) (LWPhiB sz0 3 (fun n => sz0.L n) tW) :=
  inst_psiRel tW _

theorem inst_psiRel_three_tInst : LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (3 - 2)))
    (LWPhiB sz0 3 (fun n => sz0.L n) tInst) :=
  LWPhiB_psiRel_three sz0 rfl 3 _ tInst

theorem inst_psiRel_three_tW : LWPsiRel 2 2 (fun C => Real.sqrt ((C + 1) ^ (3 - 2)))
    (LWPhiB sz0 3 (fun n => sz0.L n) tW) :=
  LWPhiB_psiRel_three sz0 rfl 3 _ tW

/-- `Ψ_t(r/4) ≲ Ψ_t(r)`, `Ψ_t(2r) ≲ Ψ_t(r)` for the B class at both times. -/
theorem inst_shift_tInst :
    (∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz0 3 (fun n => sz0.L n) tInst n (1 / 4 * r) ≤
        Kc * LWPhiB sz0 3 (fun n => sz0.L n) tInst n r) ∧
    (∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz0 3 (fun n => sz0.L n) tInst n (2 * r) ≤
        Kc * LWPhiB sz0 3 (fun n => sz0.L n) tInst n r) :=
  ⟨LWPhiB_shift sz0 (by norm_num) 3 _ tInst (by norm_num),
    LWPhiB_shift sz0 (by norm_num) 3 _ tInst (by norm_num)⟩

theorem inst_shift_tW :
    (∃ Kc : ℝ, 0 < Kc ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
      LWPhiB sz0 3 (fun n => sz0.L n) tW n (1 / 2 * r) ≤
        Kc * LWPhiB sz0 3 (fun n => sz0.L n) tW n r) :=
  LWPhiB_shift sz0 (by norm_num) 3 _ tW (by norm_num)

/-! ### The window of T2040a -/

theorem inst_window_tInst : LWWindow sz0 (1 / 5) (fun n =>
    max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (Real.sqrt (sz0.Bctl n (tInst n)))) :=
  LWWindow_max_Bctl sz0 (by norm_num) tInst (Eventually.of_forall fun n => by
    rw [Bctl_eq]; exact upper_core n (tInst_ok n).2.2)

theorem inst_window_tW : LWWindow sz0 (1 / 5) (fun n =>
    max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (Real.sqrt (sz0.Bctl n (tW n)))) :=
  LWWindow_max_Bctl sz0 (by norm_num) tW (Eventually.of_forall fun n => by
    rw [Bctl_eq]; exact upper_core n (tW_ok n).2.2)

theorem inst_class_tInst : LWClass sz0 (1 / 5) (Real.sqrt (1 + 1 ^ 2))
    (LWPhiB sz0 3 (fun n => sz0.L n) tInst) :=
  LWClass_B sz0 _ tInst (by norm_num)
    (Eventually.of_forall fun n => ⟨lam_pos n, (lam_le_64 n).trans (by norm_num)⟩)
    (Eventually.of_forall fun n => ⟨(tInst_ok n).1, (tInst_ok n).2.1⟩)
    (Eventually.of_forall fun n => upper_core n (tInst_ok n).2.2)

theorem inst_class_tW : LWClass sz0 (1 / 5) (Real.sqrt (1 + 1 ^ 2))
    (LWPhiB sz0 3 (fun n => sz0.L n) tW) :=
  LWClass_B sz0 _ tW (by norm_num)
    (Eventually.of_forall fun n => ⟨lam_pos n, (lam_le_64 n).trans (by norm_num)⟩)
    (Eventually.of_forall fun n => ⟨(tW_ok n).1, (tW_ok n).2.1⟩)
    (Eventually.of_forall fun n => upper_core n (tW_ok n).2.2)

theorem inst_psiAll_tInst : LWPsiAll sz0 (1 / 5) ((2 : ℝ) ^ 3) ((3 : ℕ) : ℝ) (Real.sqrt (1 + 1 ^ 2))
    (fun C => Real.sqrt ((C + 1) ^ (3 - 2))) (LWPhiB sz0 3 (fun n => sz0.L n) tInst) :=
  LWPhiB_psiAll sz0 (by norm_num) _ tInst (by norm_num) (by norm_num)
    (Eventually.of_forall fun n => ⟨lam_pos n, (lam_le_64 n).trans (by norm_num)⟩)
    (Eventually.of_forall fun n => ⟨(tInst_ok n).1, (tInst_ok n).2.1⟩)
    (Eventually.of_forall fun n => upper_core n (tInst_ok n).2.2)

theorem inst_psiAll_tW : LWPsiAll sz0 (1 / 5) ((2 : ℝ) ^ 3) ((3 : ℕ) : ℝ) (Real.sqrt (1 + 1 ^ 2))
    (fun C => Real.sqrt ((C + 1) ^ (3 - 2))) (LWPhiB sz0 3 (fun n => sz0.L n) tW) :=
  LWPhiB_psiAll sz0 (by norm_num) _ tW (by norm_num) (by norm_num)
    (Eventually.of_forall fun n => ⟨lam_pos n, (lam_le_64 n).trans (by norm_num)⟩)
    (Eventually.of_forall fun n => ⟨(tW_ok n).1, (tW_ok n).2.1⟩)
    (Eventually.of_forall fun n => upper_core n (tW_ok n).2.2)

/-- `LWPsiAll.shift` (the probe's lemma) applied to the proved `LWPsiAll` of the B class. -/
theorem inst_shift_all_tInst : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
    LWPhiB sz0 3 (fun n => sz0.L n) tInst n (1 / 4 * r) ≤
      K * LWPhiB sz0 3 (fun n => sz0.L n) tInst n r :=
  LWPsiAll.shift sz0 inst_psiAll_tInst (c := 1 / 4) (by norm_num)

theorem inst_shift_all_tW : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ r : ℝ, 0 ≤ r →
    LWPhiB sz0 3 (fun n => sz0.L n) tW n (2 * r) ≤
      K * LWPhiB sz0 3 (fun n => sz0.L n) tW n r :=
  LWPsiAll.shift sz0 inst_psiAll_tW (c := 2) (by norm_num)

theorem inst_asymp_tInst : ∀ᶠ n in atTop,
    LWPhiB sz0 3 (fun n => sz0.L n) tInst n 0 ≤
        max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (LWPhiB sz0 3 (fun n => sz0.L n) tInst n 0) ∧
      max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (LWPhiB sz0 3 (fun n => sz0.L n) tInst n 0) ≤
        max 1 (Real.sqrt (1 + 1 ^ 2)) * LWPhiB sz0 3 (fun n => sz0.L n) tInst n 0 :=
  LWPsiMax_asymp sz0 inst_class_tInst

theorem inst_asymp_tW : ∀ᶠ n in atTop,
    LWPhiB sz0 3 (fun n => sz0.L n) tW n 0 ≤
        max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (LWPhiB sz0 3 (fun n => sz0.L n) tW n 0) ∧
      max (((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℕ) / 2 : ℝ)) (LWPhiB sz0 3 (fun n => sz0.L n) tW n 0) ≤
        max 1 (Real.sqrt (1 + 1 ^ 2)) * LWPhiB sz0 3 (fun n => sz0.L n) tW n 0 :=
  LWPsiMax_asymp sz0 inst_class_tW

/-! ### `W^{-d} 𝒯̃ ≍ [s𝒯]²` at `r = 2`, `ℓ = 3`, `D = 1` -/

theorem inst_tail1_tInst (n : ℕ) :
    sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n) 2 ^ 2 ≤
        (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tInst n) 2 ∧
      (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tInst n) 2 ≤
        (1 + 2 ^ (3 - 1)) * sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n) 2 ^ 2 :=
  tailT_regime1_bounds (by norm_num) (by have := L_ge_4 n; linarith) (by simp [tInst]; norm_num)
    (W_pos' n) (hgt_tInst n) (by norm_num) (by have := L_ge_4 n; linarith)

theorem inst_tail1_tW (n : ℕ) :
    sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tW n) 2 ^ 2 ≤
        (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tW n) 2 ∧
      (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailT 3 (sz0.L n) (sz0.lam n) (tW n) 2 ≤
        (1 + 2 ^ (3 - 1)) * sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tW n) 2 ^ 2 :=
  tailT_regime1_bounds (by norm_num) (by have := L_ge_4 n; linarith)
    (by have := W_pos' n; simp only [tW]; have : 0 < (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
        linarith)
    (W_pos' n) (hgt_tW n) (by norm_num) (by have := L_ge_4 n; linarith)

theorem inst_tailW1_tInst (n : ℕ) :
    (1 / 2) * (sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n) (min 2 3) ^ 2 +
        (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ≤
      (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tInst n) 3
        ((sz0.W n : ℕ) : ℝ) 1 2 :=
  (tailW_regime1_bounds (by norm_num) (by have := L_ge_4 n; linarith) (by simp [tInst]; norm_num)
    (W_pos' n) (hgt_tInst n) (by norm_num) (by have := L_ge_4 n; linarith) (by norm_num)).1

theorem inst_tailW1_tW (n : ℕ) :
    (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (tW n) 3 ((sz0.W n : ℕ) : ℝ) 1 2 ≤
      (1 + 2 ^ (3 - 1)) * (sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tW n) (min 2 3) ^ 2 +
        (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  (tailW_regime1_bounds (by norm_num) (by have := L_ge_4 n; linarith)
    (by have := W_pos' n; simp only [tW]; have : 0 < (((sz0.W n : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
        linarith)
    (W_pos' n) (hgt_tW n) (by norm_num) (by have := L_ge_4 n; linarith) (by norm_num)).2

/-- Regime 2 at `sz0`, `n = 0` (`L = 4`, `g = 1/64`), `t = 1 - 2^{-17}`, `r = 2`, `ℓ = 3`, `D = 1`. -/
theorem inst_tail2 :
    Real.exp (-1) * BparamR 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 2 ≤
        tailT 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 2 ∧
      tailT 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 2 ≤
        BparamR 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 2 :=
  tailT_regime2_bounds (lam_pos 0).le (by norm_num) (by have := L_ge_4 0; linarith)
    (by rw [sz0_values.1, sz0_values.2.2.2]; norm_num) (by norm_num)
    (by rw [sz0_values.1]; norm_num)

theorem inst_tailW2 :
    max (Real.exp (-1) * BparamR 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) (min 2 3))
        (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) ≤
      tailW 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 3 ((sz0.W 0 : ℕ) : ℝ) 1 2 ∧
    tailW 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) 3 ((sz0.W 0 : ℕ) : ℝ) 1 2 ≤
      max (BparamR 3 (sz0.L 0) (sz0.lam 0) (1 - 1 / 131072) (min 2 3))
        (((sz0.W 0 : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  tailW_regime2_bounds (lam_pos 0).le (by norm_num) (by have := L_ge_4 0; linarith)
    (by rw [sz0_values.1, sz0_values.2.2.2]; norm_num) (by norm_num)
    (by rw [sz0_values.1]; norm_num) (by norm_num)

end RBM.Gauss.LWPsiInst
