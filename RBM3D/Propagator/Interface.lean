/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Basic
import RBM3D.Defs.Domination

/-!
# The interface: propagator estimates the paper does not prove

Properties 5 and 8 of `lem_propTH` are analytic estimates that **this paper does not prove.**
Appendix A.1 attributes them to earlier work:

| statement | paper label | attributed to |
|---|---|---|
| polynomial + exponential decay | `(prop:ThfadC)` | `[DYYY25]` Lemma 2.14, "we omit the details" |
| strong decay for `σ₁ = σ₂` | `(prop:ThfadC_short)` | proved, via `[bourgade2019random]` L. 4.2 |
| propagator without zero mode | `(prop:ThfadC0)` | `[yang2024Del]` Lemma 3.1 |

Under this repository's rule that the paper being formalized is the only source, the
development may not *prove* them.  They are therefore stated here as **`Prop`s** --
`RBM.ThetaDecay`, `RBM.ThetaDecayShort`, `RBM.ThetaZeroMode`.  A theorem that needs one
takes it as a hypothesis; nothing is asserted, so the axiom audit of `RBM3D.Test.Axioms`
admits **no** project axiom at all, exactly as in the sister projects `RBM1D` and `RBM2D`.

The first-order and second-order difference bounds `(prop:BD1)`, `(prop:BD2)` (properties 6
and 7) and the structure that bundled the four properties were **deleted** (DECISIONS §14,
ticket T2127): written for every `c > 0` with the loss `L^τ`, the two difference bounds were
false (at `t = 0`, `c = 1`), the bundle with them, and no merged result took any of the three as
a premise.  The pins `Prop6Diff1`, `Prop7Diff2`, `Prop5to8` of `Propagator/Pins.lean` (with
`c < 1`, no loss) replace them.

This is the form every borrowed statement in this repository takes: `Graph.Case.Rel` in
`Graph/Model.lean` and the hypotheses `hS`, `hone` that `Propagator/Basic.lean` carried
until `RBM.norm_SB` and `RBM.SB_mulVec_one` discharged them -- at which point no
downstream signature had to change.  Discharging one of them here means proving, say,
`theorem thetaDecay_of (hd : 3 ≤ d) ... : ThetaDecay d g m`; every statement that assumed
it keeps its wording, and the assumption is supplied rather than postulated.

## Form of the statements

Property 8 is written out in the explicit `∀ τ > 0, ∃ C > 0, ∀ L ≥ 3, ...` form that the
paper's `≺` abbreviates: a reader checking it against the paper should not have to unfold a
definition to see what is being assumed.

Each `Prop` carries the paper's standing assumptions `3 ≤ d`, `0 < g`, `‖m‖ = 1` as
hypotheses of its own, so that it can be stated, assumed and discharged on its own.

Properties 5 and 5' carry explicit constants in the paper and need no `≺` at all.

Note on the spectral parameter: `RBM.Theta` takes `ξ = t · m(σ₁)m(σ₂)` as a single
complex argument, so `Θ_t^(σ₁,σ₂)` appears below as `Theta d L g ((t : ℂ) * m)`.  The
hypothesis `‖m‖ = 1` together with `t < 1` gives `‖ξ‖ < 1`, which is what makes the
propagator well defined at all (`RBM.isUnit_one_sub_smul_SB`).
-/

namespace RBM

open Matrix

/-- **`(prop:ThfadC)`**, property 5 of `lem_propTH`: polynomial and exponential decay.
There are constants `C_d, c_d > 0`, depending on `d`, with

  `|Θ_t(0,a)| ≤ C_d · B_{t,|a|} · exp(-c_d |a| / ℓ_t)`   for all `a ∈ Z_L^d`.

Appendix A.1 sketches this from the random-walk representation, a Bernstein large
deviation bound and the local CLT, then says "since the argument closely follows that
in `[DYYY25]` Section 8, we omit the details". -/
def ThetaDecay (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
  3 ≤ d → 0 < g → ‖m‖ = 1 →
    ∃ Cd > (0 : ℝ), ∃ cd > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g ((t : ℂ) * m) 0 a‖
          ≤ Cd * Bparam d L g t (zdistD d L a)
              * Real.exp (-cd * (zdistD d L a : ℝ) / ellT L g t)

/-- **`(prop:ThfadC_short)`**, the `σ₁ = σ₂` half of property 5: much stronger decay,

  `|Θ_t(0,a)| ≤ C_κ (1_{a=0} + g² exp(-c_κ |a|))`.

Appendix A.1 does prove this, but through `[bourgade2019random]` Lemma 4.2, which is
outside the paper; hence it sits here rather than in `Props14.lean`.

**This is the only one of the five that is not a statement about an arbitrary spectral
parameter.**  It holds for `σ₁ = σ₂`, where the parameter is `m(σ)²`; here `m` is the
sign value `m(σ)` and the propagator is `Theta d L g (t · m * m)`.  The distinction
matters: for `σ₁ ≠ σ₂` the parameter is `m(+)m(-) = |m|² = 1`, and the bound is then
*false* -- its right-hand side is independent of `t`, while `Σ_b Θ_{t,0b} = (1-t)⁻¹`
diverges as `t → 1` (`RBM.sum_Theta_row`).  `0 < m.im` is the paper's standing
assumption `Im m > 0`, on which the constants `C_κ, c_κ` are allowed to depend (the paper
writes "depending on `d` and `κ`"); it is what keeps `m²` away from `1`. -/
def ThetaDecayShort (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
  3 ≤ d → 0 < g → ‖m‖ = 1 → 0 < m.im →
    ∃ Cκ > (0 : ℝ), ∃ cκ > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta d L g ((t : ℂ) * (m * m)) 0 a‖
          ≤ Cκ * ((if a = 0 then 1 else 0)
              + g ^ 2 * Real.exp (-cκ * (zdistD d L a : ℝ)))

/-- **`(prop:ThfadC0)`**, property 8 of `lem_propTH`: the zero-mode-removed propagator

  `|Θ̊_t(0,a)| ≺ (g² + |1-t|)⁻¹ / (|a|+1)^(d-2)`.

`[yang2024Del]` Lemma 3.1. -/
def ThetaZeroMode (d : ℕ) (g : ℝ) (m : ℂ) : Prop :=
  3 ≤ d → 0 < g → ‖m‖ = 1 → ∀ τ : ℝ, 0 < τ →
    ∃ C > (0 : ℝ),
      ∀ (L : ℕ) (hL : 3 ≤ L) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d L,
        haveI : NeZero L := ⟨by omega⟩
        ‖Theta0 d L g ((t : ℂ) * m) 0 a‖
          ≤ C * (L : ℝ) ^ τ * (g ^ 2 + |1 - t|)⁻¹
              * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

end RBM
