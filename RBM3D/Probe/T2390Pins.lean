/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1Boot
import RBM3D.BA.GreenLDE
import RBM3D.BA.Prop5Short
import RBM3D.BA.Step1
import RBM3D.BA.Step1Fam

/-!
# T2390 probe (BA-G3a design gate, Amend 1 D1; never merged, no root import)

The Lean form of the two pins of the design gate `docs/reports/T2390-prove.md` (section (G), G.7 and G.8):

* `BAGbEXPij'`: `lem_GbEXP_BA` (b), `(GijGEX_BA)` (`7_8:1940-1944`), in the paper's shape (deterministic
  `Φ_t(a,b)`, `Ψ_t`, all-pairs exponential weights, `W^{-D}`), with the event `Ω = {‖G_t - M‖_max ≤ W^{-ε₀}}`
  (`FlowFM.indMax`, `BA/Step1Boot.lean:54`) on the premise and the conclusion (DECISIONS §72 (5), D539);
* `BAStab`: the stability of the coupled system, the BA twin of `Stable S ξ K` (`Green/EntryCore.lean:911`).

`BAGbEXPii'` is not pinned (Amend 1 D2): the merged `BAGbEXPii` (`BA/Step1Boot.lean:108`) stands in for it;
`BAGbEXPav` stays as merged.  The file contains definitions, `#check` lines and `example`s for nonemptiness only
(no theorem, no placeholder proof).  Compile: `lake env lean RBM3D/Probe/T2390Pins.lean` in the T2390 worktree.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Matrix
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

namespace RBM.BA

/-! ## 1. `BAStab` -/

/-- **Stability of `1 - t M^{(+,+)}` in `max → max` norm, constant `K`** (G.2 (S1)): whenever
`|v_a - t Σ_b M^{(+,+)}_{ab} v_b| ≤ B` for all blocks `a`, then `|v_a| ≤ K B` for all `a`, where
`M^{(+,+)}_{ab} = M^{(B)}_{ba} M^{(B)}_{ab} = (M^{(B)}_{ab})²` (`BAMss`, `BA/MFixedPoint.lean:511`) at the real-axis data
`(g, E, m)` of `M^{(B)} = (g Ψ^{(B)} - E - m)⁻¹` (`BAMB`).  The BA twin of `Stable S ξ K`
(`Green/EntryCore.lean:911`, `S` real, `ξ = t m²`): the complex kernel `(M^{(B)}_{ab})²` replaces `m² S`.
The inverse of the stability operator `ℬ[R] = R - M 𝒮[R] M` of G.2 is `Θ_t = (1 - t M^{(+,+)})⁻¹ = BATheta … t true true`.
G3a (row R4) takes `BAStab … K` as a hypothesis; G3b proves it at `BAReal` data (G.2 (S1), G.8). -/
def BAStab (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ) (t K : ℝ) : Prop :=
  ∀ (v : Zd d L → ℂ) (B : ℝ),
    (∀ a, ‖v a - (t : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b * v b‖ ≤ B) →
      ∀ a, ‖v a‖ ≤ K * B

/-! ## 2. `BAGbEXPij'` -/

/-- The loop premise `(eq:def_Psit)` (`7_8:1924`) in the event form: `1_Ω 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Φ_t(a,b)²`,
uniformly in `(a, b) ∈ Z_L^d × Z_L^d`, `Ω = {‖G_t - M‖_max ≤ W^{-ε₀}}`, over the BA carrier `baFMz sz z` and the law
`seqP (sz.withLam 0)` (the premise of `BAGiiGEX` has no `Φ`; `BA/Step1Boot.lean:79`). -/
def GreenCore_loopPrem {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).L n (t n) ![false, true] ![p.1, p.2] ω‖)
    (fun n p _ => Φ n p.1 p.2 ^ 2)

/-- The right side of `(GijGEX_BA)` (`7_8:1942-1944`) at the block pair `(a, b)`:
`Σ_{a',b'} Φ(a',b') e^{-c(|a'-a| + |b'-b|)} + Ψ e^{-c|a-b|} + W^{-D}`; `|·|` is the periodic `L^∞` norm
`zdistInf` (`Defs/Sizes.lean:115`, the paper's `|x|`, `1_2:274`), as in `FlowFM.gexRHS` (`BA/Step1Boot.lean:59`). -/
def GreenCore_decayRHS (d L W : ℕ) [NeZero L] (c D : ℝ) (Φ : Zd d L → Zd d L → ℝ) (Ψ : ℝ) (a b : Zd d L) : ℝ :=
  (∑ a' : Zd d L, ∑ b' : Zd d L, Φ a' b' *
      Real.exp (-c * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ)))) +
    Ψ * Real.exp (-c * (zdistInf d L (a - b) : ℝ)) + (W : ℝ) ^ (-D)

/-- The conclusion of `(GijGEX_BA)` in the event form: `1_Ω |(G_t - M)_{xy}| ≺ decayRHS (Φ, Ψ, c, D) ([x], [y])`,
uniformly in the pairs `x ≠ y` of the fine lattice (the pairs of `BAGijGEX`, `BA/Step1Boot.lean:88`). -/
def GreenCore_decayConcl {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ D c : ℝ)
    (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0))
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => (baFMz sz z).indMax n (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z).GM n (t n) ω p.1.1 p.1.2‖)
    (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- **`lem_GbEXP_BA` (b), `(GijGEX_BA)`, in the paper's shape, event form** (`7_8:1916-1946`; G.7 of the T2390 design gate;
supervisor `2026-10-10-1155` C3).  `c = c_λ` is chosen after `(κ, ε, 𝔡)` and before the sizes and the flow
(the `c_λ` of the argument depends on `(d, κ, 𝔡)` only: G.4, G.5); for every deterministic `0 < Φ_t(a,b) ≤ W^{-ε₀}` and `W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`:
`1_Ω 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Φ_t(a,b)²` for all `(a,b)` implies, for every `D > 0` and all `x ≠ y`,
`1_Ω |(G_t - M)_{xy}| ≺ Σ_{a',b'} Φ_t(a',b') e^{-c(|a'-a|+|b'-b|)} + Ψ_t e^{-c|a-b|} + W^{-D}`, `a = [x]`, `b = [y]`.
Registry class: owed (G.8: the deterministic core is G4, consumed by G6a / G6b). -/
def BAGbEXPij' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ c : ℝ, 0 < c ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
            ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
              (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
              (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
              GreenCore_loopPrem sz z t ε₀ Φ →
              GreenCore_decayConcl sz z t ε₀ D c Φ Ψ

/-! ## 3. `#check` lines -/

#check @BAStab
#check @GreenCore_loopPrem
#check @GreenCore_decayRHS
#check @GreenCore_decayConcl
#check @BAGbEXPij'
-- the merged pins that stand (Amend 1 D2): `BAGbEXPii` stands in for `BAGbEXPii'`, `BAGbEXPav` is unchanged
#check @BAGbEXPii
#check @BAGbEXPav
#check @BAGbEXPij
-- the consumers read the merged `BAGbEXPii` and `BAGbEXPij` (primed successors: row G7)
#check @baBootstrap'_holds
#check @baStep1_holds
-- the data of the instance below (`sz0`, `n = 0`)
#check @SizesInst.sz0_values

/-! ## 4. Nonemptiness -/

/-- `BAStab` is not vacuous, at admissible block Anderson data `BAReal` (`BA/MFixedPoint.lean:432`): `d = 3`, `L = 4`,
zero coupling `g = 0`, `E = 0`, `m = i` (`M^{(B)} = i I`, `M^{(+,+)} = -I`), `t = 1/2`, `K = 1`.  Every hypothesis of the
statement is discharged (`κ = 1/2 ≤ Im m = 1`, `(self_m)`). -/
example : BAReal 3 4 0 (1 / 2) 0 Complex.I ∧ BAStab 3 4 0 0 Complex.I (1 / 2) 1 := by
  have hM : BAMB 3 4 0 ((0 : ℝ) : ℂ) Complex.I = Complex.I • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) := by
    unfold BAMB Mres
    have h : ((0 : ℝ) : ℂ) • PsiB 3 4 - (((0 : ℝ) : ℂ) + Complex.I) • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) =
        (-Complex.I) • (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) := by
      rw [Complex.ofReal_zero, zero_smul, zero_sub, zero_add, neg_smul]
    rw [h, ring_inverse_smul_one (by simp), inv_neg, Complex.inv_I, neg_neg]
  refine ⟨⟨⟨by simp, ?_⟩, by norm_num⟩, ?_⟩
  · rw [hM, Matrix.trace_smul, Matrix.trace_one, card_Zd]
    simp
    ring
  · intro v B hv a
    have hss : ∀ a b : Zd 3 4, BAMss 3 4 (BAMB 3 4 0 ((0 : ℝ) : ℂ) Complex.I) true true a b =
        if a = b then -1 else 0 := by
      intro a b
      rw [hM]
      simp only [BAMss, BAMsigma, Matrix.of_apply, ite_true, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    have h1 := hv a
    simp only [hss, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h1
    have h2 : v a - ((1 / 2 : ℝ) : ℂ) * -v a = ((3 / 2 : ℝ) : ℂ) * v a := by push_cast; ring
    rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)] at h1
    nlinarith [norm_nonneg (v a)]

/-- The data of `BAStab` at positive coupling is nonempty: `d = 3`, `L = 4` (`n = 0` of `SizesInst.sz0`), the flow
`flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`): `g₀ = √T₀ λ > 0` (`T₀ > 1/2`), `E = E₀`, `m = m₀` with
`BAReal 3 L g₀ (1/2) E₀ m₀` (`BAflow_real`, `BA/GreenSchur.lean:59`). -/
example : ∃ (g E : ℝ) (m : ℂ), 0 < g ∧ BAReal 3 (SizesInst.sz0.L 0) g (1 / 2) E m :=
  ⟨BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq 0, BAflowEs SizesInst.sz0 FlowPinsInst.zSeq 0,
    BAmF SizesInst.sz0 (BAflowLam0 SizesInst.sz0 FlowPinsInst.zSeq) (BAflowEs SizesInst.sz0 FlowPinsInst.zSeq) 0,
    mul_pos (Real.sqrt_pos.2 (by linarith [FlowPinsInst.half_lt_t0 0])) (FlowPinsInst.sz0_lam_pos 0),
    BAflow_real (1 / 2) (1 / 10) (1 / 6) (1 / 10) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 0⟩

/-- **A nonempty instance of `BAGbEXPij'`** at `d = 3`, `sz0` (`SizesInst.sz0_values`: `n = 0` has `L = 4`, `W = 32`,
`N = 2097152`, `λ = 1/64`), the flow `flow_sz0` (`κ = 1/2`, `ε = 1/10`, `𝔠 = 1/6`, `𝔡 = 1/10`), the time `t ≡ 1/2 ≤ T₀`
(`half_lt_t0`), `ε₀ = 1/10`, `Φ ≡ W^{-1/10}` and `Ψ = W^{-1}` (`W^{-3/2} ≤ Ψ ≤ W^{-1/10}`): every deterministic
hypothesis is discharged.  The pin `h` (owed) and the stochastic premise `1_Ω 𝓛 ≺ Φ²` (`(eq:def_Psit)`, `7_8:1924`)
stay hypotheses. -/
example (h : BAGbEXPij' 3) :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℝ, 0 < D →
      GreenCore_loopPrem SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10)
        (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ))) →
      GreenCore_decayConcl SizesInst.sz0 FlowPinsInst.zSeq (fun _ => 1 / 2) (1 / 10) D c
        (fun n _ _ => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)))
        (fun n => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) := by
  have h1 : ∀ n, (1 : ℝ) ≤ ((SizesInst.sz0.W n : ℕ) : ℝ) := fun n => by exact_mod_cast SizesInst.sz0.W_pos n
  obtain ⟨c, hc, hmain⟩ := h (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun D hD hL => hmain (1 / 6) SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2)
    (fun _ => by norm_num) (fun n => (FlowPinsInst.half_lt_t0 n).le) (1 / 10) (by norm_num) D hD _
    (fun n => ((SizesInst.sz0.W n : ℕ) : ℝ) ^ (-1 : ℝ)) ?_ ?_ ?_ hL⟩
  · exact Eventually.of_forall fun n a b => ⟨Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (h1 n)) _, le_rfl⟩
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num)
  · exact Eventually.of_forall fun n => Real.rpow_le_rpow_of_exponent_le (h1 n) (by norm_num)

end RBM.BA
