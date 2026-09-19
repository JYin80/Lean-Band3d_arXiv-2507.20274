/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.ScalingOrder

/-!
# The configuration split in `lem_scalingorder` is exhaustive

In the proof of `lem_scalingorder` (Appendix B, weight expansion of a distinguished
light-weight `Ǧ_ww`), the third term of `(Owx)` produces

  `m ∑_{β₁,β₂} ∑_α S_{wα} G_{αw} G_{β₁α} G_{wβ₂} 𝒢'(β₁, β₂)`,

and the proof splits into cases (i)–(vi) according to which of the three new solid edges

* `e₁ = G_{β₁α}`, `e₂ = G_{wβ₂}`, `e₃ = G_{αw}`

is diagonal after the dotted-edge partition, and whether `β₁ = β₂`.  An edge is diagonal
exactly when its two endpoints coincide, so a configuration is the equality pattern of the
four vertices along the cycle `β₁ — α — w — β₂ — β₁`: the three edges plus the closing
comparison `β₁ = β₂`.

## What this file proves

1. `Pattern.of_realizable`: equality is transitive, so on a 4-cycle it is impossible for
   exactly three of the four comparisons to hold.  Of the `2⁴ = 16` Boolean patterns,
   exactly the 12 others occur.
2. `Pattern.classify`: a single `match` assigning each of those 12 patterns to one of the
   paper's cases, and discharging the 4 impossible ones by `Pattern.of_realizable`.
   **The exhaustiveness of this `match` is checked by the compiler.**  Deleting the two
   lines that send patterns to `.vi` -- which is what the text looked like before the third
   proofreading round -- makes Lean reject the definition with `missing cases`.
3. `ord_weight_step`: in every configuration the scaling order rises by `Case.gain ≥ 1`,
   given the counter relations the paper states for that case (`Case.Rel`), via the
   arithmetic of `Graph/ScalingOrder.lean`.
4. `classify_eq_*_iff`: each case is characterised by exactly the vertex (in)equalities the
   paper uses to describe it, so the cases are the paper's cases and not a relabelling.

## What it does not prove

The counter relations in `Case.Rel` are taken from the text; they are statements about the
full graph (molecules, light-weights, the dotted-edge partition), which is not modelled
here.  For case (i) the paper states only the conclusion `ord(𝒢₁) ≥ ord(𝒢₀) + 1`, and
that is what `Case.Rel .i` records.  The bookkeeping of `n_lw` and `n_dv` behind
`(eq:relateG1G0)` is also not modelled.
-/

namespace RBM.Graph

/-- The six cases of `lem_scalingorder`, weight-expansion step. -/
inductive Case
  /-- (i) all of `G_{αw}`, `G_{β₁α}`, `G_{wβ₂}` off-diagonal -/
  | i
  /-- (ii) `β₁ ≠ β₂`, both `G_{β₁α}` and `G_{wβ₂}` diagonal -/
  | ii
  /-- (iii) `β₁ = β₂`, both `G_{β₁α}` and `G_{wβ₂}` diagonal -/
  | iii
  /-- (iv) exactly one of `G_{β₁α}`, `G_{wβ₂}` diagonal, `G_{αw}` off-diagonal -/
  | iv
  /-- (v) exactly one of `G_{β₁α}`, `G_{wβ₂}` diagonal, `G_{αw}` diagonal -/
  | v
  /-- (vi) `G_{αw}` diagonal, `G_{β₁α}` and `G_{wβ₂}` off-diagonal -/
  | vi
  deriving DecidableEq

/-- The equality pattern of a configuration: which of the three new edges are diagonal,
and whether `β₁ = β₂`. -/
structure Pattern where
  /-- `G_{β₁α}` is diagonal, i.e. `β₁ = α` -/
  d₁ : Bool
  /-- `G_{wβ₂}` is diagonal, i.e. `w = β₂` -/
  d₂ : Bool
  /-- `G_{αw}` is diagonal, i.e. `α = w` -/
  d₃ : Bool
  /-- `β₁ = β₂` -/
  same : Bool
  deriving DecidableEq

namespace Pattern

variable {V : Type*} [DecidableEq V]

/-- The pattern of the vertices `α w β₁ β₂`. -/
def of (α w β₁ β₂ : V) : Pattern :=
  ⟨decide (β₁ = α), decide (w = β₂), decide (α = w), decide (β₁ = β₂)⟩

/-- A pattern can occur: on the cycle `β₁ — α — w — β₂ — β₁`, not exactly three of the four
comparisons hold (the fourth would follow by transitivity). -/
def Realizable (p : Pattern) : Prop :=
  ¬ (p.d₁ && p.d₂ && p.d₃ && !p.same) ∧ ¬ (p.d₁ && p.d₂ && !p.d₃ && p.same) ∧
    ¬ (p.d₁ && !p.d₂ && p.d₃ && p.same) ∧ ¬ (!p.d₁ && p.d₂ && p.d₃ && p.same)

instance (p : Pattern) : Decidable p.Realizable := by
  unfold Realizable; infer_instance

/-- Every pattern that actually arises from four vertices is realizable. -/
theorem of_realizable (α w β₁ β₂ : V) : (of α w β₁ β₂).Realizable := by
  simp only [Realizable, of]
  by_cases h₁ : β₁ = α <;> by_cases h₂ : w = β₂ <;> by_cases h₃ : α = w <;>
    by_cases h₄ : β₁ = β₂ <;> simp_all

/-- All 16 patterns. -/
def all : List Pattern :=
  [false, true].flatMap fun a => [false, true].flatMap fun b =>
    [false, true].flatMap fun c => [false, true].map fun e => ⟨a, b, c, e⟩

theorem mem_all (p : Pattern) : p ∈ all := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;> decide

/-- Exactly 12 of the 16 patterns are realizable. -/
theorem card_realizable : (all.filter fun p => decide p.Realizable).length = 12 := by
  decide

/-- The case split of `lem_scalingorder`.  Each realizable pattern is sent to the case the
paper assigns it; the four unrealizable ones are discharged by the hypothesis.  Lean checks
that this `match` is exhaustive. -/
def classify : (p : Pattern) → p.Realizable → Case
  -- (i): all three edges off-diagonal
  | ⟨false, false, false, _⟩, _ => .i
  -- (ii): `β₁ ≠ β₂`, `e₁` and `e₂` diagonal (hence `β₁ = α ≠ w = β₂`, `e₃` off-diagonal)
  | ⟨true, true, false, false⟩, _ => .ii
  -- (iii): `β₁ = β₂`, `e₁` and `e₂` diagonal (hence all four vertices merge)
  | ⟨true, true, true, true⟩, _ => .iii
  -- (iv): exactly one of `e₁`, `e₂` diagonal, `e₃` off-diagonal
  | ⟨true, false, false, _⟩, _ => .iv
  | ⟨false, true, false, _⟩, _ => .iv
  -- (v): exactly one of `e₁`, `e₂` diagonal, `e₃` diagonal
  | ⟨true, false, true, false⟩, _ => .v
  | ⟨false, true, true, false⟩, _ => .v
  -- (vi): `e₃` diagonal, `e₁` and `e₂` off-diagonal -- added in the third proofreading round
  | ⟨false, false, true, _⟩, _ => .vi
  -- the four patterns with exactly three coincidences on the 4-cycle cannot occur
  | ⟨true, true, true, false⟩, h => absurd h (by decide)
  | ⟨true, true, false, true⟩, h => absurd h (by decide)
  | ⟨true, false, true, true⟩, h => absurd h (by decide)
  | ⟨false, true, true, true⟩, h => absurd h (by decide)

/-! Each case in terms of the pattern. -/

section Characterisation

variable (p : Pattern) (h : p.Realizable)
include h

theorem classify_eq_i_iff :
    p.classify h = .i ↔ p.d₃ = false ∧ p.d₁ = false ∧ p.d₂ = false := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

theorem classify_eq_ii_iff :
    p.classify h = .ii ↔ p.same = false ∧ p.d₁ = true ∧ p.d₂ = true := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

theorem classify_eq_iii_iff :
    p.classify h = .iii ↔ p.same = true ∧ p.d₁ = true ∧ p.d₂ = true := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

theorem classify_eq_iv_iff :
    p.classify h = .iv ↔ (p.d₁ = true ↔ p.d₂ = false) ∧ p.d₃ = false := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

theorem classify_eq_v_iff :
    p.classify h = .v ↔ (p.d₁ = true ↔ p.d₂ = false) ∧ p.d₃ = true := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

theorem classify_eq_vi_iff :
    p.classify h = .vi ↔ p.d₃ = true ∧ p.d₁ = false ∧ p.d₂ = false := by
  obtain ⟨_ | _, _ | _, _ | _, _ | _⟩ := p <;>
    first | (simp [Realizable] at h; done) | simp [classify]

end Characterisation

end Pattern

variable {V : Type*} [DecidableEq V]

/-- The case of `lem_scalingorder` that the vertices `α w β₁ β₂` fall into. -/
def classify (α w β₁ β₂ : V) : Case :=
  (Pattern.of α w β₁ β₂).classify (Pattern.of_realizable α w β₁ β₂)

/-! ### Each case is the paper's case -/

section Characterisation

variable (α w β₁ β₂ : V)

theorem classify_eq_i_iff :
    classify α w β₁ β₂ = .i ↔ α ≠ w ∧ β₁ ≠ α ∧ w ≠ β₂ := by
  rw [classify, Pattern.classify_eq_i_iff]
  simp [Pattern.of]

theorem classify_eq_ii_iff :
    classify α w β₁ β₂ = .ii ↔ β₁ ≠ β₂ ∧ β₁ = α ∧ w = β₂ := by
  rw [classify, Pattern.classify_eq_ii_iff]
  simp [Pattern.of]

theorem classify_eq_iii_iff :
    classify α w β₁ β₂ = .iii ↔ β₁ = β₂ ∧ β₁ = α ∧ w = β₂ := by
  rw [classify, Pattern.classify_eq_iii_iff]
  simp [Pattern.of]

theorem classify_eq_iv_iff :
    classify α w β₁ β₂ = .iv ↔ (β₁ = α ↔ w ≠ β₂) ∧ α ≠ w := by
  rw [classify, Pattern.classify_eq_iv_iff]
  simp [Pattern.of]

theorem classify_eq_v_iff :
    classify α w β₁ β₂ = .v ↔ (β₁ = α ↔ w ≠ β₂) ∧ α = w := by
  rw [classify, Pattern.classify_eq_v_iff]
  simp [Pattern.of]

/-- Case (vi) is exactly the configuration the paper describes: `α = w` with `G_{β₁α}` and
`G_{wβ₂}` both off-diagonal. -/
theorem classify_eq_vi_iff :
    classify α w β₁ β₂ = .vi ↔ α = w ∧ β₁ ≠ α ∧ w ≠ β₂ := by
  rw [classify, Pattern.classify_eq_vi_iff]
  simp [Pattern.of]

/-- Case (vi) does occur: `α = w` with `β₁`, `β₂` distinct from it. -/
theorem classify_vi_occurs : classify (0 : Fin 3) 0 1 2 = .vi := by decide

end Characterisation

/-! ### Scaling-order gain in each case -/

namespace Case

/-- The counter relations between `𝒢₀` and `𝒢₁` that the paper states in each case.
For case (i) the paper states only the resulting bound, which is recorded as is. -/
def Rel : Case → Counters → Counters → Prop
  | .i, c₀, c₁ => ord c₀ + 1 ≤ ord c₁
  | .ii, c₀, c₁ => c₁.nW = c₀.nW + 1 ∧ c₁.nV + 1 ≤ c₀.nV ∧ c₀.nS ≤ c₁.nS + 1
  | .iii, c₀, c₁ => c₁.nW = c₀.nW + 1 ∧ c₁.nV + 1 ≤ c₀.nV ∧ c₀.nS ≤ c₁.nS + 2
  | .iv, c₀, c₁ => c₁.nW = c₀.nW + 1 ∧ c₁.nV ≤ c₀.nV ∧ c₀.nS ≤ c₁.nS
  | .v, c₀, c₁ => c₁.nW = c₀.nW + 1 ∧ c₁.nV + 1 ≤ c₀.nV ∧ c₀.nS ≤ c₁.nS + 1
  | .vi, c₀, c₁ => c₁.nW = c₀.nW + 1 ∧ c₁.nV = c₀.nV ∧ c₀.nS ≤ c₁.nS

/-- The gain in scaling order the paper derives in each case. -/
def gain : Case → ℤ
  | .i => 1
  | .ii => 3
  | .iii => 2
  | .iv => 2
  | .v => 3
  | .vi => 2

theorem one_le_gain (c : Case) : 1 ≤ c.gain := by
  cases c <;> decide

/-- In each case the stated counter relations give the stated gain. -/
theorem ord_ge {c₀ c₁ : Counters} : (c : Case) → c.Rel c₀ c₁ → ord c₀ + c.gain ≤ ord c₁
  | .i, h => h
  | .ii, ⟨hW, hV, hS⟩ => ord_case_ii hW hV hS
  | .iii, ⟨hW, hV, hS⟩ => ord_case_iii hW hV hS
  | .iv, ⟨hW, hV, hS⟩ => ord_case_iv hW hV hS
  | .v, ⟨hW, hV, hS⟩ => ord_case_v hW hV hS
  | .vi, ⟨hW, hV, hS⟩ => ord_case_vi hW hV hS

end Case

/-- The weight-expansion step of `lem_scalingorder`: whatever configuration the vertices
`α w β₁ β₂` are in, the scaling order rises by the gain of its case, and so by at least 1. -/
theorem ord_weight_step (α w β₁ β₂ : V) {c₀ c₁ : Counters}
    (h : (classify α w β₁ β₂).Rel c₀ c₁) :
    ord c₀ + (classify α w β₁ β₂).gain ≤ ord c₁ ∧ ord c₀ + 1 ≤ ord c₁ := by
  have := Case.ord_ge _ h
  exact ⟨this, by have := Case.one_le_gain (classify α w β₁ β₂); omega⟩

end RBM.Graph
