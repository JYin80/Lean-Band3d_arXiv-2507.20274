/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Basic
import RBM3D.Defs.Domination

/-!
# The axiom interface: propagator estimates the paper does not prove

Properties 5–8 of `lem_propTH` are the analytic heart of the propagator layer, and
**this paper does not prove them.**  Appendix A.1 attributes them to earlier work:

| statement | paper label | attributed to |
|---|---|---|
| polynomial + exponential decay | `(prop:ThfadC)` | `[DYYY25]` Lemma 2.14, "we omit the details" |
| strong decay for `σ₁ = σ₂` | `(prop:ThfadC_short)` | proved, via `[bourgade2019random]` L. 4.2 |
| first-order difference | `(prop:BD1)` | "not stated explicitly in `[yang2024Del]`" |
| second-order difference | `(prop:BD2)` | `[yang2024Del]` (E.19) |
| propagator without zero mode | `(prop:ThfadC0)` | `[yang2024Del]` Lemma 3.1 |

Under this repository's rule that the paper being formalized is the only source, they
are therefore **axioms**, stated here and nowhere else.  `RBM3D.Test.Axioms` pins the
list down: nothing in `RBM` may depend on an axiom that is not on it, so a result that
comes to rest on a borrowed fact cannot do so silently.

Discharging any of these means importing the proof from the cited paper -- for
`(prop:BD1)`, `(prop:BD2)` and `(prop:ThfadC0)` that is the summation-by-parts argument
of `[RBSO1D]` Appendix B, which this paper says "extends directly to dimensions `d ≥ 3`",
and which the sister project `RBM2D` is formalizing for `d = 2`.  Each has its own
ticket in `docs/TASKS.md`.

## Form of the statements

The paper writes properties 6–8 with `≺`.  Rather than route them through
`RBM.UnifDetDom`, the three are written out here in the explicit
`∀ τ > 0, ∃ C > 0, ∀ L ≥ 3, ...` form that `≺` abbreviates.  For an axiom that is the
right trade: a reader checking these against the paper should not have to unfold a
definition to see what is being assumed.

Properties 5 and 5' carry explicit constants in the paper and need no `≺` at all.
-/

namespace RBM

open Matrix

/-- **`(prop:ThfadC)`**, property 5 of `lem_propTH`: polynomial and exponential decay.
There are constants `C_d, c_d > 0`, depending on `d`, with

  `|Θ_t(0,a)| ≤ C_d · B_{t,|a|} · exp(-c_d |a| / ℓ_t)`   for all `a ∈ Z_L^d`.

Appendix A.1 sketches this from the random-walk representation, a Bernstein large
deviation bound and the local CLT, then says "since the argument closely follows that
in `[DYYY25]` Section 8, we omit the details". -/
axiom theta_decay (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
    ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖ThetaRBM d L g m t 0 a‖
          ≤ Cd * Bparam d L g t (zdistD d L a)
              * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)

/-- **`(prop:ThfadC_short)`**, the `σ₁ = σ₂` half of property 5: much stronger decay,

  `|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² exp(-c_κ |a|))`.

Appendix A.1 does prove this, but through `[bourgade2019random]` Lemma 4.2, which is
outside the paper; hence it sits here rather than in `Props14.lean`. -/
axiom theta_decay_short (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1) :
    ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖ThetaRBM d L g m t 0 a‖
          ≤ Cκ * ((if a = 0 then 1 else 0)
              + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))

/-- **`(prop:BD1)`**, property 6 of `lem_propTH`: the first-order difference bound

  `|Θ_t(0,a+r) - Θ_t(0,a)| ≺ (g² + |1-t|)⁻¹ · |r| / (|a|+1)^(d-1)`   for `|r| ≲ |a|`.

The paper: "Although the bound `(prop:BD1)` is not stated explicitly in
`[yang2024Del]`, its proof proceeds analogously ... We therefore omit the details."
This is the one estimate in `lem_propTH` with no proof anywhere in the literature the
paper points to. -/
axiom theta_diff_one (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a r : Zd d L,
        zdistD d L r ≤ zdistD d L a →
        haveI : NeZero L := ⟨by omega⟩
        ‖ThetaRBM d L g m t 0 (a + r) - ThetaRBM d L g m t 0 a‖
          ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
              * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **`(prop:BD2)`**, property 7 of `lem_propTH`: the second-order difference bound

  `|Θ_t(0,a+r) + Θ_t(0,a-r) - 2 Θ_t(0,a)| ≺ (g² + |1-t|)⁻¹ · |r|² / (|a|+1)^d`.

`[yang2024Del]` equation (E.19). -/
axiom theta_diff_two (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a r : Zd d L,
        zdistD d L r ≤ zdistD d L a →
        haveI : NeZero L := ⟨by omega⟩
        ‖ThetaRBM d L g m t 0 (a + r) + ThetaRBM d L g m t 0 (a - r)
            - 2 * ThetaRBM d L g m t 0 a‖
          ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
              * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- **`(prop:ThfadC0)`**, property 8 of `lem_propTH`: the zero-mode-removed propagator

  `|Θ̊_t(0,a)| ≺ (g² + |1-t|)⁻¹ / (|a|+1)^(d-2)`.

`[yang2024Del]` Lemma 3.1. -/
axiom theta_zero_mode (d : ℕ) (hd : 3 ≤ d) (g : ℝ) (hg : 0 < g) (m : ℂ) (hm : ‖m‖ = 1)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ C > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖ThetaRBM0 d L g m t 0 a‖
          ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
              * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

end RBM
