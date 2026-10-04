/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Batteries.Tactic.OpenPrivate
import RBM3D.Loop.KLIndStepB
import RBM3D.Loop.KLCut

/-!
# The `K`-loop layer, KL11: the induction over the cut, `(eq:K-pi-bound)`, `ML:Kbound`

Ticket T2115 (`paper/tex/A_deterministic_estimates.tex`, the induction after
`(eq:ind-step-bound)`), `d ≥ 3`.  Names are in `RBM.Loop`.

Pinned names: `KLBoundAt`, `KLboundPin`, `KLKpiBoundAt`, `KLKpiBoundPin` (verbatim from
`docs/tickets/checks/T2115-check.lean`, i.e. `64b58eb:RBM3D/Probe/T2004Pins.lean:504-514,
778-784, 798-808`), their proofs `KLKpiBoundPin_holds`, `KLboundPin_holds`, the targets
`KLKpi_cut`, `KLKpi_step`, and the lemmas of the probe's section 6 (`KLTheta_eq_zero`,
`KLedge_sup`, `KLedge_l1`, `KLstar_le`, `KLone_le_rpow`, `KLBoundAt_one`, `KLBoundAt_two`,
`KLBoundAt_three`).  Every other public declaration carries the file-stem prefix `KLInduct`,
every other helper is `private`.  The only hypothesis of the proved pins is `KLPT d κ gmax`;
no new `Prop` is defined, so `Test/Axioms.lean` is untouched.

* §1 the pins.
* §2 `(eq:bcal_k)` at `n ∈ {1, 2, 3}`: the probe's section 6, ported.  Its `KLBparam_nonneg`
  and `KLBparam_le_zero` are the merged `KLIndStepA_Bparam_nonneg`, `KLIndStepA_Bparam_le_zero`.
* §3-§4 the cut data `KLInduct_aIn`, `KLInduct_aOut` and the cut of a tree value at an internal
  edge, pointwise (port of `RBM2D/Loop/KBoundCut.lean:1528-1697` at `c9a24cf`), on top of
  `KLtreeValW_cut`, `KLgval_in_eq`, `KLgval_out_eq` of `KLCut.lean`.
* §5 `KLKpi_cut`: `K^{(π)} = t ∑_{u,w} A(u) S^{(B)}_{uw} K^{(π'')}(w)` at an innermost long edge
  (port of `RBM2D/Loop/KBoundCut.lean:1954`), summed with the cut bijection `KLsum_cut`;
  `A(u)` is the summand of the left side of `KLindStepAt` at the root `Fin.last`.
* §6 the layer `π = ∅` (`KLInduct_Kpi_empty_bound`).
* §7 the induction step `KLKpi_step` (port of `RBM2D/Loop/KBound.lean:316`), the induction
  `KLInduct_KpiBoundAt_holds`, the pins `KLKpiBoundPin_holds`, `KLboundPin_holds`.
* §8 the compiled instances at `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`.

**The induction.**  Strong induction on `n ≥ 3` (the number of polygon vertices) for
`P(n) := KLKpiBoundAt d n κ gmax`.  At `n`, given `P(n'')` for `3 ≤ n'' < n`, a layer `π`:

(a) `π = ∅`.  Equal charges: `|Σ^{(∅)}| ≤ C_Σ` (`KLmolecule_holds`) and the `ℓ¹` bound `S` of
property 5' (`KLedge_l1`) give `C_Σ S^n ≤ C_Σ S^n (1+gmax²)^{n-1} B^{n-1}`, since
`(1+gmax²) B ≥ 1`.  Some charge changes: a long leaf `Θ_t^{(+,-)}` is `≤ C_d B` pointwise
(property 5) and the root sum of `KLindStepPin_holds` is `≺ B^{n-2}`.
(b) `KLTSPlong n σ π = ∅`: `K^{(π)} = 0`.
(c) Otherwise cut at an innermost `J ∈ π` (`KLKpi_cut`).  The inner polygon has
`k = j - i + 1 ∈ [3, n-1]` vertices and its root sum is `≺ B^{k-2}` (`KLindStepPin_holds` at
`k`, loss `L^{τ/2}`).  The outer polygon has `n'' = n - (j - i) + 1 ∈ [3, n-1]` vertices and
`|∑_w S^{(B)}_{uw} K^{(π'')}(w)| ≤ sup_w |K^{(π'')}| ≺ B^{n''-1}` (`P(n'')`, loss `L^{τ/2}`,
`∑_w |S^{(B)}_{uw}| = 1`).  With `|t| ≤ 1`, `(k-2) + (n''-1) = n - 1` (`d`-free) and
`L^{τ/2} L^{τ/2} = L^τ` the step closes.

The constant is `C₀ + ∑_{w<n} C_in(w+1) C_out(n-w+1)` (the finitely many widths are handled by
`choose`).  It depends on `d, n, κ, gmax, τ` only, never on `L, W, g, t, E`: the pins are
uniform in `t ∈ [0,1)`, and the regimes `1 - t ≷ g², g²/L², g²/L^d` are absorbed in `B_{t,0}`
(DECISIONS §29).  `W` enters only through the prefactor `(W^d)⁻¹ ^ (n-1)` of `(eq_K-Kpi)` in
`KLInduct_BoundAt_of_Kpi`; the layer count `2^{|diagonals n|}` is absorbed in the constant.

**The `tSΘ` leaf (T2106a).**  The paper's leaf `Θ̃_t ∈ {Θ_t, t S^{(B)} Θ_t^{(+,-)}}` does not
occur here.  The cut edge `J` carries `Θ^{(σ_i,σ_j)} - I = ξ_J S^{(B)} Θ^{(σ_i,σ_j)}`
(`mul_Theta_of_three_le`), `ξ_J = t m(σ_i) m(σ_j)`.  `KLtreeValW_cut` with `P = ξ_J • I`,
`S = S^{(B)}`, `Q = Θ^{(σ_i,σ_j)}` makes `Q` the standard leaf of the outer polygon at the glue
vertex and the root leaf of the inner polygon the identity at the glued label `u`.  The inner
leaves are `Θ^{(σ_k,σ_{k+1})}` only, so the merged `KLindStepAt` (leaves
`Θ_t^{(σ_i,σ_{i+1})}` only) suffices.

**Differences from RBM2D** (`Loop/KBoundCut.lean:1522-2138`, `Loop/KBound.lean:316-577` at
`c9a24cf`).  The merged `KLKpi` carries the factor `∏_i m(σ_i)` (DECISIONS §23); over the two
polygons `∏_{in} m ∏_{out} m = (∏ m) m(σ_i) m(σ_j)` (`prod_leaves_cut`), so the prefactor of
the cut is exactly `t` for all charges (RBM2D: `ξ_J`).  RBM2D's `KpiEmptyAt` and `InnerSumAt`
(the `d = 2` sums with `log L`) are replaced by `KLInduct_Kpi_empty_bound` and the merged
`KLindStepPin_holds`.  The loss is `L^τ`, not `N^τ`; the layer count `2^{|diagonals n|}` is a
constant, not an `N^{τ/2}`.
-/

set_option linter.style.longLine false

open private sigmaIn sigmaOut Flong_eq_iff_cut prod_leaves_cut exists_innermost
  Flong_subset_diagonals Flong_subset from RBM3D.Loop.KLSumZeroWard

namespace RBM.Loop

open Finset

/-! ## 1. The pins (verbatim: `docs/tickets/checks/T2115-check.lean`) -/

/-- **`(eq:bcal_k)` at a fixed `n`** (the conclusion of `ML:Kbound`): `n`, `κ`, `gmax` and `τ`
are fixed before the constant `C`, which does not depend on `L`, `W`, `g ∈ (0, gmax]`, `E`,
`t ∈ [0,1)`, `σ`, `a`.  Loss `L^τ`, `τ > 0` arbitrary; since `L^τ ≤ N^{τ/d}` for
`N = (WL)^d` (`KL_rpow_le`) this implies the paper's `≺` (deterministic, `N = (WL)^d`). -/
def KLBoundAt (d n : ℕ) (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (a : Fin n → Zd d p.L),
    ‖KLK d p.L p.g p.W p.E p.t (KLloopOf d p.L σ a)‖
      ≤ C * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 1)



/-- **Pin `ML:Kbound`, `(eq:bcal_k)`**, for every `n ≥ 1`, conditional on the shapes of
`lem_propTH` (`KLPT`).  `(Kn2sol)`, `(Kn3sol)` are `KLK_two`, `KLK_three`. -/
def KLboundPin : Prop :=
  ∀ (d n : ℕ) (κ gmax : ℝ), 3 ≤ d → 1 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLBoundAt d n κ gmax


/-- **Pin `(eq:K-pi-bound)`**: `|K^{(π)}(t,σ,a)| ≺ B_{t,0}^{n-1}`, every `π`, `n ≥ 3`. -/
def KLKpiBoundAt (d n : ℕ) [NeZero n] (κ gmax : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool)
    (π : Finset (Fin n × Fin n)) (a : Fin n → Zd d p.L),
    ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
      ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1)

def KLKpiBoundPin : Prop :=
  ∀ (d n : ℕ) [NeZero n] (κ gmax : ℝ), 3 ≤ d → 3 ≤ n → 0 < κ → 0 < gmax → KLPT d κ gmax →
    KLKpiBoundAt d n κ gmax

/-! ## 2. `(eq:bcal_k)` at `n ∈ {1, 2, 3}` (port of the probe, section 6)

`KLBparam_nonneg`, `KLBparam_le_zero` of the probe are the merged `KLIndStepA_Bparam_nonneg`,
`KLIndStepA_Bparam_le_zero`.  The others are ported verbatim, except that `KLedge_sup`,
`KLBoundAt_two`, `KLBoundAt_three` take `KLPT d κ gmax` where the probe takes its field
`KLDecay d gmax` (and `KLShort`): a binder `KLDecay` would make `KLDecay` a premise that the
registry scan of `Test/Axioms.lean` finds assumed and not proved (`KLPT` is registered). -/

section Bound

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `Θ_ξ(a, b) = Θ_ξ(0, a - b)`: translation invariance and symmetry (properties 1, 2). -/
theorem KLTheta_eq_zero (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ < 1) (a b : Zd d L) :
    Theta d L g ξ a b = Theta d L g ξ 0 (a - b) := by
  have h := Theta_apply_add_right_of_three_le (g := g) hL hξ (a - b) 0 b
  have h2 := congrFun (congrFun (Theta_transpose_of_three_le (d := d) (g := g) hL hξ) 0) (a - b)
  simp only [Matrix.transpose_apply] at h2
  simp only [sub_add_cancel, zero_add] at h
  rw [h, h2]

/-- **Properties 4 + 5**: every entry of every `Θ^{(σ₁,σ₂)}_t` is `≤ C_d B_{t,0}`.  (Probe: the
hypothesis `KLDecay d gmax`, the field `KLPT.decay`; here `KLPT d κ gmax`, so that no new premise
`KLDecay` enters the registry of `Test/Axioms.lean`.) -/
theorem KLedge_sup {d : ℕ} {κ gmax : ℝ} (hPT : KLPT d κ gmax) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ gmax →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ μ : ℂ, ‖μ‖ = 1 → ∀ x y : Zd d L,
        ‖Theta d L g ((t : ℂ) * μ) x y‖ ≤ Cd * Bparam d L g t 0 := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := hPT.decay
  refine ⟨Cd, hCd, ?_⟩
  intro L _ hL g hg0 hg1 t ht0 ht1 μ hμ x y
  have hξ : ‖(t : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1
  refine (norm_Theta_apply_le hL ht0 ht1 hμ x y).trans ?_
  rw [KLTheta_eq_zero hL hξ x y]
  refine (Complex.re_le_norm _).trans ?_
  refine (hbd L hL g hg0 hg1 t ht0 ht1 (x - y)).trans ?_
  have hell : 0 < ellT L g t := ellT_pos (by exact_mod_cast (by omega : 1 ≤ L))
  have hz : (0 : ℝ) ≤ (zdistD d L (x - y) : ℝ) := Nat.cast_nonneg _
  have hexp : Real.exp (-cd * (zdistD d L (x - y) : ℝ) / ellT L g t) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    apply div_nonpos_of_nonpos_of_nonneg _ hell.le
    nlinarith
  have hB := KLIndStepA_Bparam_le_zero (d := d) (L := L) (g := g) t (zdistD d L (x - y))
  have hB0 := KLIndStepA_Bparam_nonneg (d := d) (L := L) (g := g) t (zdistD d L (x - y))
  calc Cd * Bparam d L g t (zdistD d L (x - y)) * Real.exp (-cd * (zdistD d L (x - y) : ℝ)
        / ellT L g t)
      ≤ Cd * Bparam d L g t (zdistD d L (x - y)) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Cd * Bparam d L g t (zdistD d L (x - y)) := mul_one _
    _ ≤ Cd * Bparam d L g t 0 := mul_le_mul_of_nonneg_left hB hCd.le

/-- **Property 5'** gives an `ℓ¹` bound for a short edge: `∑_b |Θ^{(σ,σ)}_t(x,b)| ≤ S`. -/
theorem KLedge_l1 {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hS : KLShort (k + 2) κ gmax) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ gmax →
      ∀ E : ℝ, |E| ≤ 2 - κ → ∀ s : Bool, ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ x : Zd (k + 2) L,
        ∑ b : Zd (k + 2) L,
          ‖Theta (k + 2) L g ((t : ℂ) * (mSigma E s * mSigma E s)) x b‖ ≤ S := by
  obtain ⟨Cκ, hCκ, cκ, hcκ, hbd⟩ := hS
  have hexpC : 0 ≤ expC k cκ := by unfold expC; positivity
  refine ⟨Cκ * (1 + gmax ^ 2 * expC k cκ), by positivity, ?_⟩
  intro L _ hL g hg0 hg1 E hE s t ht0 ht1 x
  have hE2 : |E| ≤ 2 := by linarith
  have hξ : ‖(t : ℂ) * (mSigma E s * mSigma E s)‖ < 1 :=
    norm_mul_mSigma_lt_one hE2 ht0 ht1 s s
  have hpt : ∀ b : Zd (k + 2) L,
      ‖Theta (k + 2) L g ((t : ℂ) * (mSigma E s * mSigma E s)) x b‖
        ≤ Cκ * ((if x - b = 0 then (1 : ℝ) else 0)
            + g ^ 2 * Real.exp (-(cκ * (zdistD (k + 2) L (x - b) : ℝ)))) := by
    intro b
    rw [KLTheta_eq_zero hL hξ x b]
    have := hbd L hL g hg0 hg1 E hE s t ht0 ht1 (x - b)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if x - b = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 := sum_exp_decay_centre k hcκ x
  calc ∑ b : Zd (k + 2) L,
        ‖Theta (k + 2) L g ((t : ℂ) * (mSigma E s * mSigma E s)) x b‖
      ≤ ∑ b : Zd (k + 2) L, Cκ * ((if x - b = 0 then (1 : ℝ) else 0)
            + g ^ 2 * Real.exp (-(cκ * (zdistD (k + 2) L (x - b) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cκ * (1 + g ^ 2 * ∑ b : Zd (k + 2) L,
          Real.exp (-(cκ * (zdistD (k + 2) L (x - b) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cκ * (1 + g ^ 2 * expC k cκ) := by
        gcongr
    _ ≤ Cκ * (1 + gmax ^ 2 * expC k cκ) := by
        have : g ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ hg0.le hg1 2
        gcongr

/-- The three-edge star: sup bounds on two factors, an `ℓ¹` bound on the third. -/
theorem KLstar_le {G : Type*} [Fintype G] (f₁ f₂ f₃ : G → ℂ) {A S : ℝ} (hA : 0 ≤ A)
    (h₂ : ∀ b, ‖f₂ b‖ ≤ A) (h₃ : ∀ b, ‖f₃ b‖ ≤ A) (h₁ : ∑ b, ‖f₁ b‖ ≤ S) :
    ‖∑ b, f₁ b * f₂ b * f₃ b‖ ≤ A ^ 2 * S := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖f₁ b * f₂ b * f₃ b‖ ≤ ∑ b, ‖f₁ b‖ * (A * A) := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, norm_mul]
        have := mul_le_mul (h₂ b) (h₃ b) (norm_nonneg _) hA
        nlinarith [norm_nonneg (f₁ b)]
    _ = (∑ b, ‖f₁ b‖) * (A * A) := by rw [Finset.sum_mul]
    _ ≤ S * (A * A) := mul_le_mul_of_nonneg_right h₁ (by positivity)
    _ = A ^ 2 * S := by ring

theorem KLone_le_rpow {L : ℕ} (hL : 3 ≤ L) {τ : ℝ} (hτ : 0 < τ) : (1 : ℝ) ≤ (L : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) hτ.le

/-- `(eq:bcal_k)` at `n = 1`: `𝒦^{(1)} = m(σ)`, `|m| = 1`. -/
theorem KLBoundAt_one (d : ℕ) {κ gmax : ℝ} (hκ : 0 < κ) : KLBoundAt d 1 κ gmax := by
  intro τ hτ
  refine ⟨1, one_pos, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hloop : KLloopOf d p.L σ a = ⟨[σ 0], [a 0]⟩ := by simp [KLloopOf, List.ofFn_succ]
  rw [hloop, KLK_one, norm_mSigma hE2, Nat.sub_self, pow_zero, mul_one, one_mul]
  exact KLone_le_rpow p.hL hτ

/-- `(eq:bcal_k)` at `n = 2`: `(Kn2sol)` and `(prop:ThfadC)` (properties 4, 5). -/
theorem KLBoundAt_two {d : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT d κ gmax) :
    KLBoundAt d 2 κ gmax := by
  obtain ⟨Cd, hCd, hsup⟩ := KLedge_sup hPT
  intro τ hτ
  refine ⟨Cd, hCd, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hloop : KLloopOf d p.L σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  have hμ : ‖mSigma p.E (σ 0) * mSigma p.E (σ 1)‖ = 1 := by
    rw [norm_mul, norm_mSigma hE2, norm_mSigma hE2, mul_one]
  have hT := hsup p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 _ hμ (a 0) (a 1)
  rw [hloop, KLK_two, norm_mul, norm_mul, hμ, mul_one, norm_inv, norm_pow,
    Complex.norm_natCast, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  have hW0 : 0 ≤ ((p.W : ℝ) ^ d)⁻¹ := by positivity
  have hB0 := KLIndStepA_Bparam_nonneg (d := d) (L := p.L) (g := p.g) p.t 0
  have hL1 := KLone_le_rpow p.hL hτ
  calc ((p.W : ℝ) ^ d)⁻¹ * ‖Theta d p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 0) * mSigma p.E (σ 1)))
        (a 0) (a 1)‖
      ≤ ((p.W : ℝ) ^ d)⁻¹ * (Cd * Bparam d p.L p.g p.t 0) :=
        mul_le_mul_of_nonneg_left hT hW0
    _ = Cd * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) := by ring
    _ ≤ Cd * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) := by
        have hX := mul_nonneg hW0 hB0
        calc Cd * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0)
            = (Cd * 1) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) := by ring
          _ ≤ (Cd * (p.L : ℝ) ^ τ) * (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 hCd.le) hX

/-- `(eq:bcal_k)` at `n = 3`: `(Kn3sol)`; two long edges pointwise `≤ C_d B_{t,0}` (properties 4, 5),
one short edge summed (property 5'); a triangle always has an equal-charge pair. -/
theorem KLBoundAt_three {k : ℕ} {κ gmax : ℝ} (hκ : 0 < κ) (hPT : KLPT (k + 2) κ gmax) :
    KLBoundAt (k + 2) 3 κ gmax := by
  obtain ⟨Cd, hCd, hsup⟩ := KLedge_sup hPT
  obtain ⟨S, hS0, hl1⟩ := KLedge_l1 hκ hPT.short
  intro τ hτ
  refine ⟨Cd ^ 2 * S, by positivity, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hloop : KLloopOf (k + 2) p.L σ a = ⟨[σ 0, σ 1, σ 2], [a 0, a 1, a 2]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  have hm1 : ∀ s : Bool, ‖mSigma p.E s‖ = 1 := norm_mSigma hE2
  have hμ : ∀ s s' : Bool, ‖mSigma p.E s * mSigma p.E s'‖ = 1 := fun s s' => by
    rw [norm_mul, hm1, hm1, mul_one]
  have hsupp : ∀ (s s' : Bool) (x y : Zd (k + 2) p.L),
      ‖Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s')) x y‖
        ≤ Cd * Bparam (k + 2) p.L p.g p.t 0 := fun s s' x y =>
    hsup p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 _ (hμ s s') x y
  have hshort : ∀ (s : Bool) (x : Zd (k + 2) p.L),
      ∑ b : Zd (k + 2) p.L,
        ‖Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E s * mSigma p.E s)) x b‖ ≤ S :=
    fun s x => hl1 p.L p.hL p.g p.hg0 p.hg1 p.E p.hE s p.t p.ht0 p.ht1 x
  have hA : 0 ≤ Cd * Bparam (k + 2) p.L p.g p.t 0 :=
    mul_nonneg hCd.le (KLIndStepA_Bparam_nonneg _ _)
  -- the star bound
  have hstar : ‖∑ b : Zd (k + 2) p.L,
      Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 0) * mSigma p.E (σ 1))) (a 0) b *
        Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 1) * mSigma p.E (σ 2))) (a 1) b *
          Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 2) * mSigma p.E (σ 0))) (a 2) b‖
      ≤ (Cd * Bparam (k + 2) p.L p.g p.t 0) ^ 2 * S := by
    by_cases h01 : σ 0 = σ 1
    · rw [h01] at *
      exact KLstar_le _ _ _ hA (fun b => hsupp _ _ _ _) (fun b => hsupp _ _ _ _) (hshort _ _)
    · by_cases h12 : σ 1 = σ 2
      · rw [h12] at *
        have := KLstar_le (fun b => Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 2) *
          mSigma p.E (σ 2))) (a 1) b) (fun b => Theta (k + 2) p.L p.g ((p.t : ℂ) *
            (mSigma p.E (σ 0) * mSigma p.E (σ 2))) (a 0) b) (fun b => Theta (k + 2) p.L p.g
              ((p.t : ℂ) * (mSigma p.E (σ 2) * mSigma p.E (σ 0))) (a 2) b) hA
          (fun b => hsupp _ _ _ _) (fun b => hsupp _ _ _ _) (hshort _ _)
        refine le_of_eq_of_le ?_ this
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
      · have h20 : σ 2 = σ 0 := by
          cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;> simp_all
        rw [h20] at *
        have := KLstar_le (fun b => Theta (k + 2) p.L p.g ((p.t : ℂ) * (mSigma p.E (σ 0) *
          mSigma p.E (σ 0))) (a 2) b) (fun b => Theta (k + 2) p.L p.g ((p.t : ℂ) *
            (mSigma p.E (σ 0) * mSigma p.E (σ 1))) (a 0) b) (fun b => Theta (k + 2) p.L p.g
              ((p.t : ℂ) * (mSigma p.E (σ 1) * mSigma p.E (σ 0))) (a 1) b) hA
          (fun b => hsupp _ _ _ _) (fun b => hsupp _ _ _ _) (hshort _ _)
        refine le_of_eq_of_le ?_ this
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        ring
  rw [hloop, KLK_three, norm_mul, norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast,
    norm_mul, norm_mul, hm1, hm1, hm1, mul_one, mul_one,
    show (3 : ℕ) - 1 = 2 from rfl]
  simp only [mul_one]
  have hW0 : 0 ≤ ((p.W : ℝ) ^ (k + 2))⁻¹ := by positivity
  have hB0 := KLIndStepA_Bparam_nonneg (d := k + 2) (L := p.L) (g := p.g) p.t 0
  have hL1 := KLone_le_rpow p.hL hτ
  calc (((p.W : ℝ) ^ (k + 2))⁻¹) ^ 2 * ‖∑ b : Zd (k + 2) p.L, _‖
      ≤ (((p.W : ℝ) ^ (k + 2))⁻¹) ^ 2 * ((Cd * Bparam (k + 2) p.L p.g p.t 0) ^ 2 * S) :=
        mul_le_mul_of_nonneg_left hstar (by positivity)
    _ = Cd ^ 2 * S * (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2 := by ring
    _ ≤ Cd ^ 2 * S * (p.L : ℝ) ^ τ * (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2 := by
        have h1 : 0 ≤ (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2 := by
          positivity
        calc Cd ^ 2 * S * (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2
            = (Cd ^ 2 * S * 1) * (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2 := by
              ring
          _ ≤ (Cd ^ 2 * S * (p.L : ℝ) ^ τ) *
              (((p.W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) p.L p.g p.t 0) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hL1 (by positivity)) h1

end Bound

/-! ## 3. The cut data of the inner and outer polygons -/

section CutData

variable {n : ℕ} [NeZero n]

/-- The labels of the inner polygon of the cut `J = (i, j)`: vertex `k` carries the label of the
vertex `i + k` (the root label, at `Fin.last`, is overwritten by the glue label in use).
Port of `RBM2D/Loop/KBoundCut.lean:49` (`aIn`) at `c9a24cf`. -/
def KLInduct_aIn {d L : ℕ} (J : Fin n × Fin n) (a : Fin n → Zd d L) :
    Fin (KLwIn J + 1) → Zd d L :=
  fun k => a ⟨min (J.1.val + k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The labels of the outer polygon of the cut `J`, with glue label `w` at the glue vertex.
Port of `RBM2D/Loop/KBoundCut.lean:66` (`aOut`). -/
def KLInduct_aOut {d L : ℕ} (J : Fin n × Fin n) (a : Fin n → Zd d L) (w : Zd d L) :
    Fin (n - KLwIn J + 1) → Zd d L :=
  Function.update (fun k => a ⟨min (KLunCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩)
    (KLglueV J) w

end CutData

/-! ## 4. The cut at an internal edge, pointwise (the decomposition `(3.75)`) -/

section LongCut

/-- Linearity in one leaf weight. -/
private theorem KLInduct_treeValW_leaf_smul {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]
    (F : Finset (Fin n × Fin n))
    (a : Fin n → Zd d L) (M : Fin n → Matrix (Zd d L) (Zd d L) ℂ)
    (E : ↥F → Matrix (Zd d L) (Zd d L) ℂ) (v : Fin n) (c : ℂ) (X : Matrix (Zd d L) (Zd d L) ℂ) :
    KLtreeValW d L F a (Function.update M v (c • X)) E
      = c * KLtreeValW d L F a (Function.update M v X) E := by
  simp only [KLtreeValW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [KLprod_update_eq (fun w => M w (a w) (b ⟨KLleafPar F w, KLleafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]),
    KLprod_update_eq (fun w => M w (a w) (b ⟨KLleafPar F w, KLleafPar_mem F w⟩)) _ v
      (fun w hw => by rw [Function.update_of_ne hw]),
    Function.update_self, Function.update_self, Matrix.smul_apply, smul_eq_mul]
  ring

variable {d L : ℕ} [NeZero L] {g : ℝ} {n : ℕ} [NeZero n]
variable (hL : 3 ≤ L) {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
  {J : Fin n × Fin n} (hJ : J ∈ F)
  (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
include hL hF hn hJ hm

/-- **The cut at an internal edge, pointwise.**  The tree value of `F ∋ J` is
`∑_{u,w} ξ_J · V_in(u) · S^{(B)}_{uw} · V_out(w)`, `ξ_J = t m(σ_i) m(σ_j)`, where `V_in(u)` is the inner tree
with the identity as root leaf at the label `u` and `V_out(w)` the outer tree with glue label `w`: the edge
`J` carries `Θ^{(σ_i,σ_j)} - I = ξ_J S^{(B)} Θ^{(σ_i,σ_j)}`, and `Θ^{(σ_i,σ_j)}` is the standard leaf of the
outer polygon at the glue vertex.  Port of `RBM2D/Loop/KBoundCut.lean:1550` (`treeValW_long_cut`). -/
private theorem KLInduct_treeValG_cut (σ : Fin n → Bool) (a : Fin n → Zd d L)
    (σi : Fin (KLwIn J + 1) → Bool) (ai : Zd d L → Fin (KLwIn J + 1) → Zd d L)
    (σo : Fin (n - KLwIn J + 1) → Bool) (ao : Zd d L → Fin (n - KLwIn J + 1) → Zd d L)
    (hσi : ∀ i : Fin (KLwIn J + 1), σi i = σ (KLunShift J (i, i)).1)
    (hσo : ∀ i : Fin (n - KLwIn J + 1), σo i = σ (KLunColP J (i, i)).1)
    (hai0 : ∀ u, ai u (Fin.last _) = u) (hai1 : ∀ u, ∀ v : KLLIn J, ai u (KLinV J v) = a v)
    (hao0 : ∀ w, ao w (KLglueV J) = w) (hao1 : ∀ w, ∀ v : KLLOut J, ao w (KLoutV J v) = a v) :
    KLtreeValG d L g m t σ a F
      = ∑ u : Zd d L, ∑ w : Zd d L,
          ((t : ℂ) * (m (σ J.1) * m (σ J.2)) *
            KLtreeValW d L (KLFIn F J) (ai u)
              (Function.update (fun v => thetaEdge d L g m t (σi v) (σi (v + 1))) (Fin.last _) 1)
              (fun e => thetaEdge d L g m t (σi e.1.1) (σi e.1.2) - 1))
            * SB d L g u w * KLtreeValG d L g m t σo (ao w) (KLFOut F J) := by
  have hJd := hF.1 J hJ
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  -- vertex / region bookkeeping
  have si : ∀ i : Fin (KLwIn J + 1), (KLunShift J (i, i)).1.val = i.val + J.1.val := fun i =>
    (KLunShift_val (i, i)).1
  have so : ∀ i : Fin (n - KLwIn J + 1), (KLunColP J (i, i)).1.val = KLunCol J i.val := fun i =>
    (KLunColP_val (i, i) hJ2).1
  have hσi' : ∀ (i : Fin (KLwIn J + 1)) (v : Fin n), v.val = i.val + J.1.val → σi i = σ v := by
    intro i v hv; rw [hσi i]; congr 1; exact Fin.ext (by rw [si i, hv])
  have hσo' : ∀ (i : Fin (n - KLwIn J + 1)) (v : Fin n), v.val = KLunCol J i.val → σo i = σ v := by
    intro i v hv; rw [hσo i]; congr 1; exact Fin.ext (by rw [so i, hv])
  have hone : (1 : Fin n).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hsucc : ∀ v : Fin n, v.val < n - 1 → (v + 1 : Fin n).val = v.val + 1 := by
    intro v hv; rw [Fin.val_add, hone, Nat.mod_eq_of_lt (by omega)]
  -- inside side conditions
  have hM1i : ∀ v : KLLIn J, thetaEdge d L g m t (σi (KLinV J v)) (σi (KLinV J v + 1))
      = thetaEdge d L g m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := KLinV_val v.2
    have hlt : (KLinV J v.1).val < KLwIn J := by rw [h1]; simp only [KLwIn]; omega
    have hvn : v.1.val < n - 1 := by omega
    rw [hσi' _ v.1 (by rw [h1]; omega), hσi' _ (v.1 + 1) (by
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      omega)]
  have hEi : ∀ e : KLEIn F J,
      thetaEdge d L g m t (σi (KLshiftIn J e.1.1).1) (σi (KLshiftIn J e.1.1).2) - 1
      = thetaEdge d L g m t (σ e.1.1.1) (σ e.1.1.2) - 1 := by
    intro e
    have hlt := (hF.1 e.1.1 e.1.2).1
    have hv := KLshiftIn_val e.2.1 (le_of_lt hlt)
    have hdJ := e.2.1
    simp only [KLArcLe, Fin.le_def] at hdJ
    rw [hσi' _ e.1.1.1 (by rw [hv.1]; omega),
      hσi' _ e.1.1.2 (by rw [hv.2]; omega)]
  -- outside side conditions
  have hg : (KLglueV J).val = J.1.val := by simp only [KLglueV, KLwIn]; omega
  have hM0o : thetaEdge d L g m t (σo (KLglueV J)) (σo (KLglueV J + 1))
      = thetaEdge d L g m t (σ J.1) (σ J.2) := by
    have hg1 : (KLglueV J + 1).val = J.1.val + 1 := by
      rw [Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last, hg]; simp only [KLwIn]; omega), hg]
    rw [hσo' _ J.1 (by rw [hg, KLunCol_of_le le_rfl]), hσo' _ J.2 (by
      rw [hg1, KLunCol_of_gt (by omega)]; simp only [KLwIn]; omega)]
  have hM1o : ∀ v : KLLOut J, thetaEdge d L g m t (σo (KLoutV J v)) (σo (KLoutV J v + 1))
      = thetaEdge d L g m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by
      have := v.2; simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this; omega
    have h1 := KLoutV_val v.1 hJ2
    rw [hσo' _ v.1 (by rw [h1, KLunCol_col (by omega) hJw])]
    congr 1
    by_cases hr : v.1.val = n - 1
    · have hlast : KLoutV J v.1 = Fin.last _ := by
        refine Fin.ext ?_
        rw [h1, Fin.val_last, KLcol_of_gt (by omega), hr]; simp only [KLwIn]; omega
      have hv1 : v.1 + 1 = 0 := by
        refine Fin.ext ?_
        rw [Fin.val_add, hone, hr, Nat.sub_add_cancel (by omega), Nat.mod_self]; rfl
      rw [hlast, Fin.last_add_one, hv1]
      exact hσo' 0 0 (by simp [KLunCol])
    · have hvn : v.1.val < n - 1 := by have := v.1.isLt; omega
      have hlt : (KLoutV J v.1).val < n - KLwIn J := by
        rw [h1]; rcases hvs with h | h
        · rw [KLcol_of_le (by omega)]; simp only [KLwIn]; omega
        · rw [KLcol_of_gt (by omega)]; simp only [KLwIn]; omega
      refine hσo' _ _ ?_
      rw [hsucc v.1 hvn, Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; exact hlt), h1]
      rcases hvs with h | h
      · rw [KLcol_of_le (by omega)]
        by_cases h' : v.1.val + 1 ≤ J.1.val
        · rw [KLunCol_of_le h']
        · have : v.1.val + 1 = J.1.val := by omega
          rw [this, KLunCol_of_le le_rfl]
      · rw [KLcol_of_gt (by omega), KLunCol_of_gt (by simp only [KLwIn]; omega)]
        simp only [KLwIn]; omega
  have hEo : ∀ e : KLEOut F J,
      thetaEdge d L g m t (σo (KLshiftOut J e.1.1).1) (σo (KLshiftOut J e.1.1).2) - 1
      = thetaEdge d L g m t (σ e.1.1.1) (σ e.1.1.2) - 1 := by
    intro e
    have hE := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem e.1.2) e.2
    have hv := KLshiftOut_val e.1.1 hJ2
    rw [hσo' _ e.1.1.1 (by rw [hv.1, KLunCol_col hE.1 hJw]),
      hσo' _ e.1.1.2 (by rw [hv.2, KLunCol_col hE.2.1 hJw])]
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  set Mi : Fin (KLwIn J + 1) → Matrix (Zd d L) (Zd d L) ℂ :=
    fun v => thetaEdge d L g m t (σi v) (σi (v + 1))
  have hM0i : Function.update Mi (Fin.last _) (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ)) (Fin.last _)
      = (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ)).transpose := by
    rw [Function.update_self, Matrix.transpose_smul, Matrix.transpose_one]
  have hM1i' : ∀ v : KLLIn J,
      Function.update Mi (Fin.last _) (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ)) (KLinV J v)
        = thetaEdge d L g m t (σ v.1) (σ (v.1 + 1)) := by
    intro v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
    have hne : KLinV J v.1 ≠ Fin.last _ := by
      intro h
      have h1 := KLinV_val v.2
      have := congrArg Fin.val h
      rw [h1, Fin.val_last] at this
      simp only [KLwIn] at this
      omega
    rw [Function.update_of_ne hne]
    exact hM1i v
  have hEJ : (fun e : ↥F => thetaEdge d L g m t (σ e.1.1) (σ e.1.2) - 1)
      = Function.update (fun e : ↥F => thetaEdge d L g m t (σ e.1.1) (σ e.1.2) - 1) ⟨J, hJ⟩
          (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ) * SB d L g * thetaEdge d L g m t (σ J.1) (σ J.2)) := by
    funext e
    by_cases hd : e = ⟨J, hJ⟩
    · subst hd
      rw [Function.update_self]
      have h := mul_Theta_of_three_le (d := d) (L := L) (g := g) hL (hm (σ J.1) (σ J.2))
      rw [sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
      change Theta d L g ξ - 1 = ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ) * SB d L g * Theta d L g ξ
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← h]
      abel
    · rw [Function.update_of_ne hd]
  rw [KLtreeValG, hEJ, KLtreeValW_cut d L hF hn hJ a _ _ (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ))
    (SB d L g) (thetaEdge d L g m t (σ J.1) (σ J.2))]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => ?_
  rw [KLgval_in_eq hF hn hJ d L a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
      (fun e : ↥F => thetaEdge d L g m t (σ e.1.1) (σ e.1.2) - 1) u _ (ai u)
        (Function.update Mi (Fin.last _) (ξ • (1 : Matrix (Zd d L) (Zd d L) ℂ)))
      (fun e => thetaEdge d L g m t (σi e.1.1) (σi e.1.2) - 1) (hai0 u) (hai1 u) hM0i hM1i' hEi,
    KLgval_out_eq hF hn hJ d L a (fun v => thetaEdge d L g m t (σ v) (σ (v + 1)))
      (fun e : ↥F => thetaEdge d L g m t (σ e.1.1) (σ e.1.2) - 1) w _ (ao w)
        (fun v => thetaEdge d L g m t (σo v) (σo (v + 1)))
      (fun e => thetaEdge d L g m t (σo e.1.1) (σo e.1.2) - 1) (hao0 w) (hao1 w) hM0o hM1o hEo,
    KLInduct_treeValW_leaf_smul]
  rfl

end LongCut


/-! ## 5. The decomposition `K^{(π)} = t ∑_{u,w} A(u) S^{(B)}_{uw} K^{(π'')}(w)` -/

section KpiCut

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- **The inner polygon is a root sum of `KLindStepAt`.**  For the inner polygon with identity root
leaf at `Fin.last` carrying the label `u`, `(∏ m) ∑_{H ∈ T_SP(k+1), long edges ∅} (tree value)` is the
summand `∑_{δ_{last} = u} Σ^{(∅)}(δ) ∏_{i ≠ last} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)` of the left side of
`KLindStepAt` at the root `r = Fin.last`. -/
private theorem KLInduct_inner_eq (m : Bool → ℂ) (t : ℝ) {k : ℕ} (σ' : Fin (k + 1) → Bool)
    (a' : Fin (k + 1) → Zd d L) (u : Zd d L) :
    (∏ i, m (σ' i)) * ∑ H ∈ KLTSPlong (k + 1) σ' ∅,
        KLtreeValW d L H (Function.update a' (Fin.last k) u)
          (Function.update (fun v => thetaEdge d L g m t (σ' v) (σ' (v + 1))) (Fin.last k) 1)
          (fun e => thetaEdge d L g m t (σ' e.1.1) (σ' e.1.2) - 1)
      = ∑ δ ∈ Finset.univ.filter (fun δ : Fin (k + 1) → Zd d L => δ (Fin.last k) = u),
          KLSigmaPi d L g m t σ' ∅ δ *
            ∏ i ∈ Finset.univ.erase (Fin.last k),
              thetaEdge d L g m t (σ' i) (σ' (i + 1)) (a' i) (δ i) := by
  have hleaf : ∀ (δ : Fin (k + 1) → Zd d L),
      ∏ v, Function.update (fun v => thetaEdge d L g m t (σ' v) (σ' (v + 1))) (Fin.last k) 1 v
          (Function.update a' (Fin.last k) u v) (δ v)
        = (if δ (Fin.last k) = u then (1 : ℂ) else 0) *
            ∏ i ∈ Finset.univ.erase (Fin.last k),
              thetaEdge d L g m t (σ' i) (σ' (i + 1)) (a' i) (δ i) := by
    intro δ
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (Fin.last k))]
    congr 1
    · simp only [Function.update_self, Matrix.one_apply]
      by_cases h : δ (Fin.last k) = u
      · simp [h]
      · simp [h, Ne.symm h]
    · refine Finset.prod_congr rfl fun i hi => ?_
      have hne : i ≠ Fin.last k := Finset.ne_of_mem_erase hi
      simp only [Function.update_of_ne hne]
  simp only [KLtreeValW_eq_sum_selfW, hleaf, KLSigmaPi, Finset.sum_filter, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun δ _ => ?_
  by_cases h : δ (Fin.last k) = u
  · simp only [h, ↓reduceIte, one_mul]
    refine Finset.sum_congr rfl fun H _ => ?_
    ring
  · simp [h]

/-- **The decomposition `(3.75)` at an innermost long edge** (`n ≥ 3`).  If `π = F_long(F₀, σ)` for a
tree `F₀` and `J = (i, j) ∈ π` is innermost (no other edge of `π` inside its arc), then
`K^{(π)}(t,σ,a) = t ∑_{u,w} A(u) S^{(B)}_{uw} K^{(π'')}(σ_out, a_out(w))`, where `π'' = π ∖ {J}` moved to
the outer polygon (`n - (j - i) + 1` vertices, glue vertex at `i`, charges `sigmaOut σ J`, labels
`KLInduct_aOut J a w`), and `A(u)` is the summand, at `b = u`, of the left side of `KLindStepAt` for
the inner polygon (`j - i + 1` vertices, charges `sigmaIn σ J`, root `Fin.last`, whose leaf is the
identity at the glue label `u`): the glued edge is `ξ_J S^{(B)}_{uw}` times the standard leaf
`Θ^{(σ_i,σ_j)}` of the outer polygon, `Θ^{(σ_i,σ_j)} - I = ξ_J S^{(B)} Θ^{(σ_i,σ_j)}` (`mul_Theta`), so no
`tSΘ`-leaf appears.  The prefactor is exactly `t` (not `ξ_J = t m(σ_i) m(σ_j)`): the factor
`∏ m(σ_i)` of `KLKpi` splits as `∏_{in} m ∏_{out} m = (∏ m) m(σ_i) m(σ_j)` over the two polygons
(`prod_leaves_cut`).  Port of `RBM2D/Loop/KBoundCut.lean:1954` (`Kpi_cut`) at `c9a24cf`.
`sigmaIn`, `sigmaOut` are the private charges of `KLSumZeroWard.lean:70, 75`. -/
theorem KLKpi_cut (d L : ℕ) [NeZero L] (g : ℝ) (hL : 3 ≤ L) {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (m : Bool → ℂ) (t : ℝ) (hm : ∀ s s' : Bool, ‖(t : ℂ) * (m s * m s')‖ < 1)
    (σ : Fin n → Bool) {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n)
    {π : Finset (Fin n × Fin n)} {J : Fin n × Fin n} (hπ : KLFlong F₀ σ = π) (hJπ : J ∈ π)
    (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) :
    KLKpi d L g m t σ a π
      = ∑ u : Zd d L, ∑ w : Zd d L,
          (t : ℂ) *
            (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
              KLSigmaPi d L g m t (sigmaIn σ J) ∅ δ *
                ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
                  thetaEdge d L g m t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
                    (KLInduct_aIn J a i) (δ i))
            * SB d L g u w *
          KLKpi d L g m t (sigmaOut σ J) (KLInduct_aOut J a w) ((π.erase J).image (KLshiftOut J)) := by
  have hn2 : 2 ≤ n := by omega
  have hF₀' := KLisTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  have hJw := KLwidth_of_isDiag hJd
  have hJ2 : J.1.val < J.2.val := by omega
  have hJn := J.2.isLt
  set π' := (π.erase J).image (KLshiftOut J) with hπ'
  set σi := sigmaIn σ J with hσidef
  set σo := sigmaOut σ J with hσodef
  set ξ : ℂ := (t : ℂ) * (m (σ J.1) * m (σ J.2)) with hξ
  set ai : Zd d L → Fin (KLwIn J + 1) → Zd d L :=
    fun u => Function.update (KLInduct_aIn J a) (Fin.last _) u with haidef
  set ao : Zd d L → Fin (n - KLwIn J + 1) → Zd d L := fun w => KLInduct_aOut J a w with haodef
  -- the side conditions of the cut
  have hσi : ∀ i : Fin (KLwIn J + 1), σi i = σ (KLunShift J (i, i)).1 := by
    intro i; simp only [σi, sigmaIn, KLunShift]; congr 2; omega
  have hσo : ∀ i : Fin (n - KLwIn J + 1), σo i = σ (KLunColP J (i, i)).1 := fun i => rfl
  have hai0 : ∀ u, ai u (Fin.last _) = u := fun u => Function.update_self _ _ _
  have hai1 : ∀ u, ∀ v : KLLIn J, ai u (KLinV J v) = a v := by
    intro u v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
    have h1 := KLinV_val v.2
    have hne : KLinV J v.1 ≠ Fin.last _ := by
      intro h
      have := congrArg Fin.val h
      rw [h1, Fin.val_last] at this
      simp only [KLwIn] at this
      omega
    simp only [ai, Function.update_of_ne hne, KLInduct_aIn]
    congr 1
    exact Fin.ext (by
      change min (J.1.val + (KLinV J v.1).val) (n - 1) = v.1.val
      rw [h1]; omega)
  have hao0 : ∀ w, ao w (KLglueV J) = w := fun w => Function.update_self _ _ _
  have hao1 : ∀ w, ∀ v : KLLOut J, ao w (KLoutV J v) = a v := by
    intro w v
    have hv := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv
    have hvs : v.1.val < J.1.val ∨ J.2.val ≤ v.1.val := by omega
    have hvn := v.1.isLt
    have h1 := KLoutV_val v.1 hJ2
    have hg : (KLglueV J).val = J.1.val := by simp only [KLglueV, KLwIn]; omega
    have hne : KLoutV J v.1 ≠ KLglueV J := by
      intro h
      have := congrArg Fin.val h
      rw [h1, hg] at this
      rcases hvs with h' | h'
      · rw [KLcol_of_le (by omega)] at this; omega
      · rw [KLcol_of_gt (by omega)] at this; simp only [KLwIn] at this; omega
    simp only [ao, KLInduct_aOut, Function.update_of_ne hne]
    congr 1
    exact Fin.ext (by
      change min (KLunCol J (KLoutV J v.1).val) (n - 1) = v.1.val
      rw [h1, KLunCol_col (by omega) hJw]; omega)
  -- the layer is cut along `J`
  have hlayer : KLTSPlong n σ π = ((TSP n).filter fun F => J ∈ F).filter fun F => KLFlong F σ = π := by
    ext F
    simp only [KLTSPlong, mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  set Vin : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → Zd d L → ℂ := fun H u =>
    KLtreeValW d L H (ai u)
      (Function.update (fun v => thetaEdge d L g m t (σi v) (σi (v + 1))) (Fin.last _) 1)
      (fun e => thetaEdge d L g m t (σi e.1.1) (σi e.1.2) - 1) with hVin
  set X : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → Zd d L → Zd d L → ℂ := fun G H u w =>
    (ξ * Vin H u) * SB d L g u w * KLtreeValG d L g m t σo (ao w) G with hX
  set f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ := fun G H =>
    (if KLFlong G σo = π' then 1 else 0) * (if KLFlong H σi = ∅ then 1 else 0) *
      ∑ u : Zd d L, ∑ w : Zd d L, X G H u w with hf
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if KLFlong F σ = π then KLtreeValG d L g m t σ a F else 0) = f (KLFOut F J) (KLFIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := mem_filter.1 hF
    have hF' := KLisTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn2 hJF σ hF₀' hπ hJπ hinner
    have hcut := KLInduct_treeValG_cut (g := g) hL hF' hn2 hJF m t hm σ a σi ai σo ao hσi hσo hai0
      hai1 hao0 hao1
    by_cases h : KLFlong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : KLFlong (KLFOut F J) σo = π' := h1
      have h2' : KLFlong (KLFIn F J) σi = ∅ := h2
      rw [ite_eq_left_iff.2 (fun h' => absurd h h'), hcut]
      simp only [f, X, Vin, h1', h2', ↓reduceIte, one_mul]
      rfl
    · simp only [f, h, ↓reduceIte]
      by_cases h1 : KLFlong (KLFOut F J) σo = π'
      · have h2 : ¬KLFlong (KLFIn F J) σi = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [h2]
      · simp [h1]
  have e2 : ∀ G, ∑ H ∈ TSP (KLwIn J + 1), f G H = if KLFlong G σo = π' then
      ∑ H ∈ KLTSPlong _ σi ∅, ∑ u : Zd d L, ∑ w : Zd d L, X G H u w else 0 := by
    intro G
    split_ifs with hG
    · rw [KLTSPlong, sum_filter]
      refine sum_congr rfl fun H _ => ?_
      simp only [f, hG, ↓reduceIte, one_mul]
      split_ifs <;> simp
    · exact sum_eq_zero fun H _ => by simp only [f, hG, ↓reduceIte, zero_mul]
  have hmain : ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F
      = ∑ u : Zd d L, ∑ w : Zd d L, ξ * (∑ H ∈ KLTSPlong _ σi ∅, Vin H u) * SB d L g u w *
          ∑ G ∈ KLTSPlong _ σo π', KLtreeValG d L g m t σo (ao w) G := by
    have h1 : ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F
        = ∑ F ∈ (TSP n).filter (fun F => J ∈ F), f (KLFOut F J) (KLFIn F J) := by
      rw [hlayer, sum_filter]
      exact sum_congr rfl hpt
    rw [h1, KLsum_cut hJd hn2 f, sum_congr rfl fun G _ => e2 G, ← sum_filter]
    change ∑ G ∈ KLTSPlong _ σo π', ∑ H ∈ KLTSPlong _ σi ∅, ∑ u : Zd d L, ∑ w : Zd d L, X G H u w = _
    calc ∑ G ∈ KLTSPlong _ σo π', ∑ H ∈ KLTSPlong _ σi ∅, ∑ u : Zd d L, ∑ w : Zd d L, X G H u w
        = ∑ G ∈ KLTSPlong _ σo π', ∑ u : Zd d L, ∑ H ∈ KLTSPlong _ σi ∅, ∑ w : Zd d L, X G H u w :=
          sum_congr rfl fun G _ => sum_comm
      _ = ∑ u : Zd d L, ∑ G ∈ KLTSPlong _ σo π', ∑ H ∈ KLTSPlong _ σi ∅, ∑ w : Zd d L, X G H u w :=
          sum_comm
      _ = ∑ u : Zd d L, ∑ G ∈ KLTSPlong _ σo π', ∑ w : Zd d L, ∑ H ∈ KLTSPlong _ σi ∅, X G H u w :=
          sum_congr rfl fun u _ => sum_congr rfl fun G _ => sum_comm
      _ = ∑ u : Zd d L, ∑ w : Zd d L, ∑ G ∈ KLTSPlong _ σo π', ∑ H ∈ KLTSPlong _ σi ∅, X G H u w :=
          sum_congr rfl fun u _ => sum_comm
      _ = _ := by
          refine sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
          simp only [X, mul_sum, sum_mul]
  -- the factor `∏ m`
  have hprod : (∏ i, m (σ i)) * ξ = (t : ℂ) * ((∏ k, m (σi k)) * ∏ k, m (σo k)) := by
    have h := prod_leaves_cut hJd σ (fun s _ => m s)
    rw [hξ]
    linear_combination (t : ℂ) * h
  have hA : ∀ u : Zd d L, (∏ k, m (σi k)) * ∑ H ∈ KLTSPlong _ σi ∅, Vin H u
      = ∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
          KLSigmaPi d L g m t σi ∅ δ *
            ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              thetaEdge d L g m t (σi i) (σi (i + 1)) (KLInduct_aIn J a i) (δ i) :=
    fun u => KLInduct_inner_eq m t σi (KLInduct_aIn J a) u
  change (∏ i, m (σ i)) * ∑ F ∈ KLTSPlong n σ π, KLtreeValG d L g m t σ a F = _
  rw [hmain, Finset.mul_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun w _ => ?_
  rw [← hA u]
  change _ = (t : ℂ) * ((∏ k, m (σi k)) * ∑ H ∈ KLTSPlong _ σi ∅, Vin H u) * SB d L g u w *
    ((∏ k, m (σo k)) * ∑ G ∈ KLTSPlong _ σo π', KLtreeValG d L g m t σo (ao w) G)
  linear_combination ((∑ H ∈ KLTSPlong _ σi ∅, Vin H u) * SB d L g u w *
    ∑ G ∈ KLTSPlong _ σo π', KLtreeValG d L g m t σo (ao w) G) * hprod

end KpiCut



/-! ## 6. The layer `π = ∅` -/

section Empty

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- **`K^{(∅)}` through a long root leaf**: `K^{(∅)}(σ,a) = ∑_b Θ^{(σ_r,σ_{r+1})}(a_r, b) X_b` with
`X_b = ∑_{δ_r = b} Σ^{(∅)}(δ) ∏_{i ≠ r} Θ^{(σ_i,σ_{i+1})}(a_i, δ_i)`, the summand of `KLindStepAt`. -/
private theorem KLInduct_Kpi_empty_slice (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n]
    (σ : Fin n → Bool) (a : Fin n → Zd d L) (r : Fin n) :
    KLKpi d L g m t σ a ∅
      = ∑ b : Zd d L, thetaEdge d L g m t (σ r) (σ (r + 1)) (a r) b *
          ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = b),
            KLSigmaPi d L g m t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase r, thetaEdge d L g m t (σ i) (σ (i + 1)) (a i) (δ i) := by
  rw [KLKpi_eq_sum_SigmaPi, ← Finset.sum_fiberwise Finset.univ (fun δ : Fin n → Zd d L => δ r)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  have hb : δ r = b := (Finset.mem_filter.1 hδ).2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), hb]
  ring

/-- **The layer `π = ∅` when every leaf has an `ℓ¹` bound**: `|K^{(∅)}| ≤ C_Σ S^n` from the molecule
bound `|Σ^{(∅)}| ≤ C_Σ` and `∑_b |Θ^{(σ_v,σ_{v+1})}(x, b)| ≤ S` for every leaf `v` and label `x` (used
when every leaf is short, `σ_v = σ_{v+1}`, by property 5'). -/
private theorem KLInduct_Kpi_empty_short (m : Bool → ℂ) (t : ℝ) {n : ℕ} [NeZero n]
    (σ : Fin n → Bool) (a : Fin n → Zd d L) {Cm S : ℝ}
    (hCm : ∀ δ, ‖KLSigmaPi d L g m t σ ∅ δ‖ ≤ Cm)
    (hS : ∀ (v : Fin n) (x : Zd d L),
      ∑ b, ‖thetaEdge d L g m t (σ v) (σ (v + 1)) x b‖ ≤ S) :
    ‖KLKpi d L g m t σ a ∅‖ ≤ Cm * S ^ n := by
  have hCm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 0)
  rw [KLKpi_eq_sum_SigmaPi]
  have hprod : ∑ δ : Fin n → Zd d L, ∏ v, ‖thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) (δ v)‖
      = ∏ v, ∑ b, ‖thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) b‖ := by
    have := (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Zd d L)))
      (fun v x => ‖thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) x‖)).symm
    rw [Fintype.piFinset_univ] at this
    exact this
  calc ‖∑ δ : Fin n → Zd d L, KLSigmaPi d L g m t σ ∅ δ *
          ∏ v, thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) (δ v)‖
      ≤ ∑ δ : Fin n → Zd d L, ‖KLSigmaPi d L g m t σ ∅ δ *
          ∏ v, thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) (δ v)‖ := norm_sum_le _ _
    _ ≤ ∑ δ : Fin n → Zd d L, Cm * ∏ v, ‖thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) (δ v)‖ := by
        refine Finset.sum_le_sum fun δ _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_right (hCm δ) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = Cm * ∏ v, ∑ b, ‖thetaEdge d L g m t (σ v) (σ (v + 1)) (a v) b‖ := by
        rw [← Finset.mul_sum, hprod]
    _ ≤ Cm * ∏ _v : Fin n, S := by
        exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun v _ => hS v (a v))) hCm0
    _ = Cm * S ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The layer `π = ∅`** (`n ≥ 3`): `|K^{(∅)}(t,σ,a)| ≺ B_{t,0}^{n-1}`, loss `L^τ`.  If every charge is
equal to the next one, `|Σ^{(∅)}| ≤ C_Σ` (`KLmolecule_holds`, `(eq:molecule-decay)`) and the `ℓ¹` bound of
property 5' (`KLedge_l1`) give `C_Σ S^n ≤ C_Σ S^n (1+gmax²)^{n-1} B^{n-1}` because `(1+gmax²) B ≥ 1`;
otherwise a long leaf `Θ_t^{(+,-)}` is bounded in sup norm by `C_d B` (property 5) and the root sum is
`KLindStepPin_holds`, `≺ B^{n-2}`. -/
theorem KLInduct_Kpi_empty_bound (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : KLPar κ gmax) (σ : Fin n → Bool) (a : Fin n → Zd d p.L),
      ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a ∅‖
        ≤ C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cm, hCm, c, hc, hmol⟩ := KLmolecule_holds (k + 2) n κ gmax hd hn hκ hg hPT.short
  obtain ⟨S, hS0, hS⟩ := KLedge_l1 hκ hPT.short
  obtain ⟨Cd, hCd, hTh⟩ := KLIndStepA_Theta_norm_le hPT
  obtain ⟨Ci, hCi, hind⟩ := KLindStepPin_holds (k + 2) n κ gmax hd hn hκ hg hPT τ hτ
  refine ⟨Cm * S ^ n * (1 + gmax ^ 2) ^ (n - 1) + Cd * Ci, by positivity, ?_⟩
  intro p σ a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hB0 : 0 ≤ Bparam (k + 2) p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hL1 := KLone_le_rpow p.hL hτ
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBn : 0 ≤ (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := pow_nonneg hB0 _
  have hextra : 0 ≤ Cd * Ci * (p.L : ℝ) ^ τ * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by
    positivity
  by_cases hσ : ∀ v, σ v = σ (v + 1)
  · -- equal charges: the molecule is bounded and every leaf is short
    have hcm : ∀ δ, ‖KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ‖ ≤ Cm := by
      intro δ
      refine (hmol p σ δ).trans ?_
      have h1 : Real.exp (-(c * (KLmaxDist (k + 2) p.L δ : ℝ))) ≤ 1 :=
        Real.exp_le_one_iff.2 (by
          have : 0 ≤ c * (KLmaxDist (k + 2) p.L δ : ℝ) := by positivity
          linarith)
      nlinarith
    have hS' : ∀ (v : Fin n) (x : Zd (k + 2) p.L),
        ∑ b, ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ v) (σ (v + 1)) x b‖ ≤ S := by
      intro v x
      unfold thetaEdge
      rw [← hσ v]
      exact hS p.L p.hL p.g p.hg0 p.hg1 p.E p.hE (σ v) p.t p.ht0 p.ht1 x
    have h1 := KLInduct_Kpi_empty_short (mSigma p.E) p.t σ a hcm hS'
    -- `(1 + gmax²) B ≥ 1`: `B ≥ (g² + |1-t|)⁻¹ ≥ (1 + gmax²)⁻¹`
    have hden : p.g ^ 2 + |1 - p.t| ≤ 1 + gmax ^ 2 := by
      have h1 : p.g ^ 2 ≤ gmax ^ 2 := pow_le_pow_left₀ p.hg0.le p.hg1 2
      have h2 : |1 - p.t| ≤ 1 := by
        rw [abs_of_pos (by linarith [p.ht1])]; linarith [p.ht0]
      linarith
    have hden0 : 0 < p.g ^ 2 + |1 - p.t| := by
      have := p.hg0; positivity
    have hinv : (1 + gmax ^ 2)⁻¹ ≤ Bparam (k + 2) p.L p.g p.t 0 :=
      (inv_anti₀ hden0 hden).trans (KLlat_inv_le_Bparam p.t)
    have hAB : 1 ≤ (1 + gmax ^ 2) * Bparam (k + 2) p.L p.g p.t 0 := by
      have h1pos : (0 : ℝ) < 1 + gmax ^ 2 := by positivity
      calc (1 : ℝ) = (1 + gmax ^ 2) * (1 + gmax ^ 2)⁻¹ := (mul_inv_cancel₀ h1pos.ne').symm
        _ ≤ (1 + gmax ^ 2) * Bparam (k + 2) p.L p.g p.t 0 :=
          mul_le_mul_of_nonneg_left hinv h1pos.le
    have hpow : 1 ≤ (1 + gmax ^ 2) ^ (n - 1) * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by
      rw [← mul_pow]; exact one_le_pow₀ hAB
    have hCS : 0 ≤ Cm * S ^ n := by positivity
    calc ‖KLKpi (k + 2) p.L p.g (mSigma p.E) p.t σ a ∅‖ ≤ Cm * S ^ n := h1
      _ = (Cm * S ^ n) * 1 * 1 := by ring
      _ ≤ (Cm * S ^ n) * ((1 + gmax ^ 2) ^ (n - 1) * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1))
            * (p.L : ℝ) ^ τ := by
          gcongr
      _ = Cm * S ^ n * (1 + gmax ^ 2) ^ (n - 1) * (p.L : ℝ) ^ τ
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by ring
      _ ≤ (Cm * S ^ n * (1 + gmax ^ 2) ^ (n - 1) + Cd * Ci) * (p.L : ℝ) ^ τ
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by
          nlinarith [hextra]
  · -- a long leaf: `Θ_t` in sup norm times the root sum of `KLindStepAt`
    obtain ⟨r, hr⟩ := not_forall.1 hσ
    have hlong : ∀ b : Zd (k + 2) p.L,
        ‖thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ r) (σ (r + 1)) (a r) b‖
          ≤ Cd * Bparam (k + 2) p.L p.g p.t 0 := by
      intro b
      rw [KLIndStepA_thetaEdge_long hE2 p.t hr]
      exact hTh p.L p.hL p.g p.hg0 p.hg1 p.t p.ht0 p.ht1 (a r) b
    have hroot := hind p σ r hr a
    rw [KLInduct_Kpi_empty_slice (mSigma p.E) p.t σ a r]
    calc ‖∑ b : Zd (k + 2) p.L, thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ r) (σ (r + 1)) (a r) b *
            ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) p.L => δ r = b),
              KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
                ∏ i ∈ Finset.univ.erase r,
                  thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
        ≤ ∑ b : Zd (k + 2) p.L, (Cd * Bparam (k + 2) p.L p.g p.t 0) *
            ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd (k + 2) p.L => δ r = b),
              KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
                ∏ i ∈ Finset.univ.erase r,
                  thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hlong b) (norm_nonneg _)
      _ = (Cd * Bparam (k + 2) p.L p.g p.t 0) *
            ∑ b : Zd (k + 2) p.L, ‖∑ δ ∈ Finset.univ.filter
                (fun δ : Fin n → Zd (k + 2) p.L => δ r = b),
              KLSigmaPi (k + 2) p.L p.g (mSigma p.E) p.t σ ∅ δ *
                ∏ i ∈ Finset.univ.erase r,
                  thetaEdge (k + 2) p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖ := by
          rw [Finset.mul_sum]
      _ ≤ (Cd * Bparam (k + 2) p.L p.g p.t 0) *
            (Ci * (p.L : ℝ) ^ τ * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 2)) :=
          mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = Cd * Ci * (p.L : ℝ) ^ τ * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by
          have : n - 1 = (n - 2) + 1 := by omega
          rw [this, pow_succ]; ring
      _ ≤ (Cm * S ^ n * (1 + gmax ^ 2) ^ (n - 1) + Cd * Ci) * (p.L : ℝ) ^ τ
            * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by
          have : 0 ≤ Cm * S ^ n * (1 + gmax ^ 2) ^ (n - 1) * (p.L : ℝ) ^ τ
              * (Bparam (k + 2) p.L p.g p.t 0) ^ (n - 1) := by positivity
          nlinarith [this]

end Empty

/-! ## 7. The induction step and `(eq:K-pi-bound)` for all `π` -/

section Step

variable {d L : ℕ} [NeZero L] {g : ℝ}

/-- `|∑_w S^{(B)}_{uw} B(w)| ≤ M` when `|B| ≤ M`: the rows of `S^{(B)}` have `ℓ¹` norm `1`. -/
private theorem KLInduct_norm_sum_SB_mul_le (hL : 3 ≤ L) (u : Zd d L) (B : Zd d L → ℂ) {M : ℝ}
    (hB : ∀ w, ‖B w‖ ≤ M) : ‖∑ w : Zd d L, SB d L g u w * B w‖ ≤ M := by
  calc ‖∑ w : Zd d L, SB d L g u w * B w‖ ≤ ∑ w : Zd d L, ‖SB d L g u w‖ * ‖B w‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ w : Zd d L, ‖SB d L g u w‖ * M :=
        Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hB w) (norm_nonneg _)
    _ = M := by rw [← Finset.sum_mul, sum_norm_SB_row d L g hL u, one_mul]

/-- **The final chain of the step**: `|∑_{u,w} ξ A(u) S_{uw} B(w)| ≤ |ξ| (∑_u |A(u)|) M` when `|B| ≤ M`. -/
private theorem KLInduct_norm_cut_le (hL : 3 ≤ L) (ξ : ℂ) (A B : Zd d L → ℂ) {M : ℝ}
    (hB : ∀ w, ‖B w‖ ≤ M) :
    ‖∑ u : Zd d L, ∑ w : Zd d L, ξ * A u * SB d L g u w * B w‖
      ≤ ‖ξ‖ * (∑ u : Zd d L, ‖A u‖) * M := by
  have hrw : ∀ u, ∑ w : Zd d L, ξ * A u * SB d L g u w * B w
      = ξ * A u * ∑ w : Zd d L, SB d L g u w * B w := fun u => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  simp_rw [hrw]
  calc ‖∑ u : Zd d L, ξ * A u * ∑ w : Zd d L, SB d L g u w * B w‖
      ≤ ∑ u : Zd d L, ‖ξ‖ * ‖A u‖ * ‖∑ w : Zd d L, SB d L g u w * B w‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        simp only [norm_mul]
    _ ≤ ∑ u : Zd d L, ‖ξ‖ * ‖A u‖ * M :=
        Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left
          (KLInduct_norm_sum_SB_mul_le hL u B hB) (by positivity)
    _ = ‖ξ‖ * (∑ u : Zd d L, ‖A u‖) * M := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]

/-- **The induction step** (strong induction on the number `n` of polygon vertices): the bound
`(eq:K-pi-bound)` at `n ≥ 3` follows from the bound at every `3 ≤ n'' < n` (outer polygons,
`n'' = n - (j - i) + 1`).  The layer `π = ∅` is `KLInduct_Kpi_empty_bound`; a layer `π ≠ ∅` is cut at an
innermost long edge (`KLKpi_cut`): the inner polygon has `k = j - i + 1 ∈ [3, n-1]` vertices and its root
sum is `≺ B^{k-2}` (`KLindStepPin_holds`), the outer average `∑_w S^{(B)}_{uw} K^{(π'')}(w)` is bounded by
`sup_w |K^{(π'')}|`, `≺ B^{n''-1}`; `(k-2) + (n''-1) = n - 1`, and the loss `L^τ` is split into
`L^{τ/2} L^{τ/2}`.  The constant depends on `d, n, κ, gmax, τ` only. -/
theorem KLKpi_step (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n) (hκ : 0 < κ)
    (hg : 0 < gmax) (hPT : KLPT d κ gmax)
    (hout : ∀ (n'' : ℕ) [NeZero n''], 3 ≤ n'' → n'' < n → KLKpiBoundAt d n'' κ gmax) :
    KLKpiBoundAt d n κ gmax := by
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  obtain ⟨C₀, hC₀, H₀⟩ := KLInduct_Kpi_empty_bound d n κ gmax hd hn hκ hg hPT τ hτ
  -- the inner constants (at `τ/2`) and the outer constants (at `τ/2`), one per width
  have hin : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → ∀ [NeZero k], ∀ (p : KLPar κ gmax)
      (σ : Fin k → Bool) (r : Fin k), σ r ≠ σ (r + 1) → ∀ a : Fin k → Zd d p.L,
        ∑ b : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin k → Zd d p.L => δ r = b),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t σ ∅ δ *
              ∏ i ∈ Finset.univ.erase r,
                thetaEdge d p.L p.g (mSigma p.E) p.t (σ i) (σ (i + 1)) (a i) (δ i)‖
          ≤ C * (p.L : ℝ) ^ (τ / 2) * (Bparam d p.L p.g p.t 0) ^ (k - 2)) := by
    intro k
    by_cases hk : 3 ≤ k
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := KLindStepPin_holds d k κ gmax hd hk hκ hg hPT (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ => H⟩
    · exact ⟨1, one_pos, fun hk' => absurd hk' hk⟩
  have hout' : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ (3 ≤ k → k < n → ∀ [NeZero k], ∀ (p : KLPar κ gmax)
      (σ : Fin k → Bool) (π : Finset (Fin k × Fin k)) (a : Fin k → Zd d p.L),
        ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
          ≤ C * (p.L : ℝ) ^ (τ / 2) * (Bparam d p.L p.g p.t 0) ^ (k - 1)) := by
    intro k
    by_cases hk : 3 ≤ k ∧ k < n
    · have : NeZero k := ⟨by omega⟩
      obtain ⟨C, hC, H⟩ := hout k hk.1 hk.2 (τ / 2) hτ2
      exact ⟨C, hC, fun _ _ _ => H⟩
    · exact ⟨1, one_pos, fun h3 hlt => absurd ⟨h3, hlt⟩ hk⟩
  choose Ci hCi0 hCi using hin
  choose Co hCo0 hCo using hout'
  have hsum0 : 0 ≤ ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le
  refine ⟨C₀ + ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1), by positivity, ?_⟩
  intro p σ π a
  have hE2 : |p.E| ≤ 2 := by linarith [p.hE]
  have hB0 : 0 ≤ Bparam d p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBn : 0 ≤ (Bparam d p.L p.g p.t 0) ^ (n - 1) := pow_nonneg hB0 _
  have hRHS : 0 ≤ (C₀ + ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1)) * (p.L : ℝ) ^ τ
      * (Bparam d p.L p.g p.t 0) ^ (n - 1) := by positivity
  by_cases hπ0 : π = ∅
  · -- the layer `π = ∅`
    subst hπ0
    refine (H₀ p σ a).trans ?_
    have : 0 ≤ (∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1)) * (p.L : ℝ) ^ τ
        * (Bparam d p.L p.g p.t 0) ^ (n - 1) := by positivity
    nlinarith [this]
  rcases (KLTSPlong n σ π).eq_empty_or_nonempty with hemp | ⟨F₀, hF₀⟩
  · -- no tree has the long edges `π`
    simp only [KLKpi, hemp, Finset.sum_empty, mul_zero, norm_zero]
    exact hRHS
  obtain ⟨hF₀T, hπ⟩ := Finset.mem_filter.1 hF₀
  have hsub : π ⊆ diagonals n := by rw [← hπ]; exact Flong_subset_diagonals hF₀T σ
  obtain ⟨J, hJ, hinner⟩ := exists_innermost hsub (Finset.nonempty_iff_ne_empty.2 hπ0)
  have hJd : IsDiag n J.1 J.2 := (Finset.mem_filter.1 (hsub hJ)).2
  have hJlong : σ J.1 ≠ σ J.2 := by
    have hJ' : J ∈ KLFlong F₀ σ := by rw [hπ]; exact hJ
    exact (Finset.mem_filter.1 hJ').2
  obtain ⟨hJ12, hJadj, hJwhole⟩ := hJd
  rw [Fin.lt_def] at hJ12
  have hJ2n := J.2.isLt
  have hw2 : 2 ≤ KLwIn J := by simp only [KLwIn]; omega
  have hwn : KLwIn J + 2 ≤ n := by
    simp only [KLwIn]
    by_cases h0 : J.1.val = 0
    · have : J.2.val ≠ n - 1 := fun h => hJwhole ⟨h0, h⟩
      omega
    · omega
  have hm : ∀ s s' : Bool, ‖(p.t : ℂ) * (mSigma p.E s * mSigma p.E s')‖ < 1 := fun s s' =>
    norm_mul_mSigma_lt_one hE2 p.ht0 p.ht1 s s'
  have hJd' : IsDiag n J.1 J.2 := ⟨by rw [Fin.lt_def]; exact hJ12, hJadj, hJwhole⟩
  rw [KLKpi_cut d p.L p.g p.hL hn (mSigma p.E) p.t hm σ hF₀T hπ hJ hinner a]
  -- the outer average
  have hB : ∀ w : Zd d p.L, ‖KLKpi d p.L p.g (mSigma p.E) p.t (sigmaOut σ J)
      (KLInduct_aOut J a w) ((π.erase J).image (KLshiftOut J))‖
        ≤ Co (n - KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
          (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1) := fun w =>
    hCo (n - KLwIn J + 1) (by omega) (by omega) p (sigmaOut σ J) _ (KLInduct_aOut J a w)
  -- the inner root sum
  have hroot : sigmaIn σ J (Fin.last (KLwIn J)) ≠ sigmaIn σ J (Fin.last (KLwIn J) + 1) := by
    rw [Fin.last_add_one]
    have e1 : sigmaIn σ J (Fin.last (KLwIn J)) = σ J.2 := by
      simp only [sigmaIn, Fin.val_last]
      congr 1
      ext
      simp only [KLwIn]
      omega
    have e2 : sigmaIn σ J 0 = σ J.1 := by
      simp only [sigmaIn, Fin.val_zero, add_zero]
      congr 1
      ext
      simp only
      omega
    rw [e1, e2]
    exact Ne.symm hJlong
  have hA := hCi (KLwIn J + 1) (by omega) p (sigmaIn σ J) (Fin.last (KLwIn J)) hroot
    (KLInduct_aIn J a)
  have hξ : ‖((p.t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg p.ht0]; exact p.ht1.le
  refine (KLInduct_norm_cut_le p.hL _ _ _ hB).trans ?_
  have hM0 : 0 ≤ Co (n - KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
      (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1) :=
    mul_nonneg (mul_nonneg (hCo0 _).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (pow_nonneg hB0 _)
  have hsum0 : 0 ≤ ∑ u : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter
      (fun δ : Fin (KLwIn J + 1) → Zd d p.L => δ (Fin.last (KLwIn J)) = u),
        KLSigmaPi d p.L p.g (mSigma p.E) p.t (sigmaIn σ J) ∅ δ *
          ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            thetaEdge d p.L p.g (mSigma p.E) p.t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
              (KLInduct_aIn J a i) (δ i)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hpow : (Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2) *
      (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1) = (Bparam d p.L p.g p.t 0) ^ (n - 1) := by
    rw [← pow_add]; congr 1; omega
  have hLL : (p.L : ℝ) ^ (τ / 2) * (p.L : ℝ) ^ (τ / 2) = (p.L : ℝ) ^ τ := by
    rw [← Real.rpow_add (by exact_mod_cast (by have := p.hL; omega : 0 < p.L)), add_halves]
  -- the single term of the constant
  have hterm : Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)
      ≤ ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1) :=
    Finset.single_le_sum (f := fun w => Ci (w + 1) * Co (n - w + 1))
      (fun w _ => mul_nonneg (hCi0 _).le (hCo0 _).le) (Finset.mem_range.2 (by omega))
  calc ‖((p.t : ℝ) : ℂ)‖ *
        (∑ u : Zd d p.L, ‖∑ δ ∈ Finset.univ.filter
          (fun δ : Fin (KLwIn J + 1) → Zd d p.L => δ (Fin.last (KLwIn J)) = u),
            KLSigmaPi d p.L p.g (mSigma p.E) p.t (sigmaIn σ J) ∅ δ *
              ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn J)),
                thetaEdge d p.L p.g (mSigma p.E) p.t (sigmaIn σ J i) (sigmaIn σ J (i + 1))
                  (KLInduct_aIn J a i) (δ i)‖) *
        (Co (n - KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
          (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1))
      ≤ 1 * (Ci (KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
            (Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2)) *
          (Co (n - KLwIn J + 1) * (p.L : ℝ) ^ (τ / 2) *
            (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hξ hA hsum0 zero_le_one) hM0
    _ = (Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)) *
          ((p.L : ℝ) ^ (τ / 2) * (p.L : ℝ) ^ (τ / 2)) *
          ((Bparam d p.L p.g p.t 0) ^ (KLwIn J + 1 - 2) *
            (Bparam d p.L p.g p.t 0) ^ (n - KLwIn J + 1 - 1)) := by ring
    _ = (Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)) * (p.L : ℝ) ^ τ *
          (Bparam d p.L p.g p.t 0) ^ (n - 1) := by rw [hLL, hpow]
    _ ≤ (C₀ + ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1)) * (p.L : ℝ) ^ τ *
          (Bparam d p.L p.g p.t 0) ^ (n - 1) := by
        have h1 : Ci (KLwIn J + 1) * Co (n - KLwIn J + 1)
            ≤ C₀ + ∑ w ∈ range n, Ci (w + 1) * Co (n - w + 1) := by linarith
        gcongr

/-- **`(eq:K-pi-bound)` is proved** for every `n ≥ 3`, every `π`: strong induction on `n` with `KLKpi_step`;
the only hypothesis is the local propagator shapes `KLPT d κ gmax`. -/
theorem KLInduct_KpiBoundAt_holds (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLKpiBoundAt d n κ gmax := by
  have key : ∀ n : ℕ, ∀ [NeZero n], 3 ≤ n → KLKpiBoundAt d n κ gmax := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro _ hn
      exact KLKpi_step d n κ gmax hd hn hκ hg hPT (fun n'' _ h3 hlt => ih n'' hlt h3)
  exact key n hn

/-- **The pin `(eq:K-pi-bound)` is proved**: `|K^{(π)}(t,σ,a)| ≺ B_{t,0}^{n-1}`, every `π`, `n ≥ 3`,
conditional only on `KLPT d κ gmax`. -/
theorem KLKpiBoundPin_holds : KLKpiBoundPin :=
  fun d n _ κ gmax hd hn hκ hg hPT => KLInduct_KpiBoundAt_holds d n κ gmax hd hn hκ hg hPT

/-- **`(eq:bcal_k)` for `n ≥ 3`, from the layers**: `(eq_K-Kpi)` (`KLK_eq_sum_Kpi`) gives the prefactor
`W^{-d(n-1)} = ((W^d)⁻¹) ^ (n-1)`, the same for every `π`, times the sum over the `2^{|diagonals n|}`
layers, each `≺ B^{n-1}` (`KLInduct_KpiBoundAt_holds`): the count is absorbed in the constant and the
loss `L^τ` is not split.  `KLboundPin_holds` uses it for `n ≥ 4`. -/
theorem KLInduct_BoundAt_of_Kpi (d n : ℕ) [NeZero n] (κ gmax : ℝ) (hd : 3 ≤ d) (hn : 3 ≤ n)
    (hκ : 0 < κ) (hg : 0 < gmax) (hPT : KLPT d κ gmax) : KLBoundAt d n κ gmax := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := KLInduct_KpiBoundAt_holds d n κ gmax hd hn hκ hg hPT τ hτ
  refine ⟨2 ^ (diagonals n).card * C, by positivity, ?_⟩
  intro p σ a
  have hB0 : 0 ≤ Bparam d p.L p.g p.t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (p.L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0 : 0 ≤ ((p.W : ℝ) ^ d)⁻¹ := by positivity
  rw [KLK_eq_sum_Kpi d p.L p.g p.W p.E p.t hn σ a, norm_mul, norm_pow, norm_inv, norm_pow,
    Complex.norm_natCast]
  have hsum : ‖∑ π ∈ (diagonals n).powerset, KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
      ≤ 2 ^ (diagonals n).card * (C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ π ∈ (diagonals n).powerset, ‖KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
        ≤ ∑ _π ∈ (diagonals n).powerset, C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1) :=
          Finset.sum_le_sum fun π _ => H p σ π a
      _ = 2 ^ (diagonals n).card * (C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1)) := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
          push_cast
          ring
  calc (((p.W : ℝ) ^ d)⁻¹) ^ (n - 1) *
        ‖∑ π ∈ (diagonals n).powerset, KLKpi d p.L p.g (mSigma p.E) p.t σ a π‖
      ≤ (((p.W : ℝ) ^ d)⁻¹) ^ (n - 1) *
        (2 ^ (diagonals n).card * (C * (p.L : ℝ) ^ τ * (Bparam d p.L p.g p.t 0) ^ (n - 1))) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg hW0 _)
    _ = 2 ^ (diagonals n).card * C * (p.L : ℝ) ^ τ *
        (((p.W : ℝ) ^ d)⁻¹ * Bparam d p.L p.g p.t 0) ^ (n - 1) := by
        rw [mul_pow]; ring

/-- **The pin `ML:Kbound`, `(eq:bcal_k)`, is proved** for every `n ≥ 1`, conditional only on `KLPT`:
`n = 1, 2, 3` by `KLBoundAt_one`, `KLBoundAt_two`, `KLBoundAt_three` (the star bounds of the probe), `n ≥ 4` by
`KLInduct_BoundAt_of_Kpi`. -/
theorem KLboundPin_holds : KLboundPin := by
  intro d n κ gmax hd hn hκ hg hPT
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | h4
  · exact KLBoundAt_one (k + 2) hκ
  · exact KLBoundAt_two hκ hPT
  · exact KLBoundAt_three hκ hPT
  · have : NeZero n := ⟨by omega⟩
    exact KLInduct_BoundAt_of_Kpi (k + 2) n κ gmax hd (by omega) hκ hg hPT

end Step

/-! ## 8. The compiled instances: `d = 3`, `L = 5`, `W = 2`, `g = 1/2`, `E = 0`, `t = 9/10`

The parameter point is `KLinstPar` of `KLTree.lean` (`κ = gmax = 1`); `KLPT 3 1 1` (the shapes of
`lem_propTH`, another gate's pin) stays a hypothesis of the examples, every other hypothesis is
discharged at the data.  The loops are on four vertices, charges `(+,+,-,-)`, with spread labels. -/

section Instances

/-- The charges `(+,+,-,-)` of the instances: the leaves `(1,2)` and `(3,0)` are long, and so are both
diagonals `(0,2)` (`σ_0 ≠ σ_2`) and `(1,3)` (`σ_1 ≠ σ_3`). -/
def KLInduct_instσ : Fin 4 → Bool := ![true, true, false, false]

/-- Spread labels in `Z_5^3`. -/
def KLInduct_insta : Fin 4 → Zd 3 5 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2]]

/-- Target 4, `KLKpiBoundPin_holds` at `n = 4` and the three layers `π = ∅`, `π = {(0,2)}`, `π = {(1,3)}`
of `σ = (+,+,-,-)`; one constant serves all of them.  `KLPT 3 1 1` is the only hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta
          {((0 : Fin 4), (2 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta
          {((1 : Fin 4), (3 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) := by
  obtain ⟨C, hC, H⟩ := KLKpiBoundPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    1 one_pos
  exact ⟨C, hC, H KLinstPar KLInduct_instσ ∅ KLInduct_insta,
    H KLinstPar KLInduct_instσ {((0 : Fin 4), (2 : Fin 4))} KLInduct_insta,
    H KLinstPar KLInduct_instσ {((1 : Fin 4), (3 : Fin 4))} KLInduct_insta⟩

/-- Target 4, `KLboundPin_holds` at `n = 4` (the `n ≥ 4` branch, `KLK_eq_sum_Kpi`) and at `n = 1, 2, 3`
(the branches `KLBoundAt_one`, `KLBoundAt_two`, `KLBoundAt_three`): the loops `(+,+,-,-)` with the labels
above, `(+)`, `(+,-)` and `(+,-,+)` with labels of `KLinsta`. -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLInduct_instσ KLInduct_insta)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLinstσ KLinsta)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false] ![KLinsta 0, KLinsta 1])‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true] ![KLinsta 1])‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (1 - 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLboundPin_holds 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
      1 one_pos
    exact ⟨C, hC, H KLinstPar KLInduct_instσ KLInduct_insta⟩
  · obtain ⟨C, hC, H⟩ := KLboundPin_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
      1 one_pos
    exact ⟨C, hC, H KLinstPar KLinstσ KLinsta⟩
  · obtain ⟨C, hC, H⟩ := KLboundPin_holds 3 2 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
      1 one_pos
    exact ⟨C, hC, H KLinstPar ![true, false] ![KLinsta 0, KLinsta 1]⟩
  · obtain ⟨C, hC, H⟩ := KLboundPin_holds 3 1 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
      1 one_pos
    exact ⟨C, hC, H KLinstPar ![true] ![KLinsta 1]⟩

/-- Target 1, `KLBoundAt_one`, `KLBoundAt_two`, `KLBoundAt_three` at the instance data (`n = 1, 2, 3`,
charges `(+)`, `(+,-)`, `(+,-,+)`, distinct labels). -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true] ![KLinsta 1])‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (1 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 ![true, false] ![KLinsta 0, KLinsta 1])‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (2 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLK 3 5 (1 / 2) 2 0 (9 / 10) (KLloopOf 3 5 KLinstσ KLinsta)‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) *
          ((((2 : ℕ) : ℝ) ^ 3)⁻¹ * Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (3 - 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLBoundAt_one 3 (κ := 1) (gmax := 1) one_pos 1 one_pos
    exact ⟨C, hC, H KLinstPar ![true] ![KLinsta 1]⟩
  · obtain ⟨C, hC, H⟩ := KLBoundAt_two (d := 3) (κ := 1) (gmax := 1) one_pos hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar ![true, false] ![KLinsta 0, KLinsta 1]⟩
  · obtain ⟨C, hC, H⟩ := KLBoundAt_three (k := 1) (κ := 1) (gmax := 1) one_pos hPT
      1 one_pos
    exact ⟨C, hC, H KLinstPar KLinstσ KLinsta⟩

/-- The innermost long diagonal `J = (0, 2)` of `σ = (+,+,-,-)`: the inner polygon is the triangle
`(0,1,2)`, the outer polygon the triangle `(0,2,3)`. -/
def KLInduct_instJ : Fin 4 × Fin 4 := (0, 2)

/-- Target 3, `KLKpi_step` (and `KLInduct_Kpi_empty_bound` for the layer `π = ∅`) at `n = 4`: the layers
`π = ∅`, `{(0,2)}` and `{(1,3)}`; the induction hypothesis at `n'' = 3` is the proved
`KLInduct_KpiBoundAt_holds`, so `KLPT 3 1 1` is the only hypothesis left. -/
example (hPT : KLPT 3 1 1) :
    ∃ C : ℝ, 0 < C ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta {KLInduct_instJ}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
      (‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta
          {((1 : Fin 4), (3 : Fin 4))}‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) := by
  obtain ⟨C, hC, H⟩ := KLKpi_step 3 4 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT
    (fun n'' _ h3 hlt => by
      have h : n'' = 3 := by omega
      subst h
      exact KLInduct_KpiBoundAt_holds 3 3 1 1 (by norm_num) (by norm_num) one_pos one_pos hPT)
    1 one_pos
  exact ⟨C, hC, H KLinstPar KLInduct_instσ ∅ KLInduct_insta,
    H KLinstPar KLInduct_instσ {KLInduct_instJ} KLInduct_insta,
    H KLinstPar KLInduct_instσ {((1 : Fin 4), (3 : Fin 4))} KLInduct_insta⟩

/-- Target 3, `KLInduct_Kpi_empty_bound` at `n = 4` and `n = 5`, `σ = (+,+,-,-)` resp. `(+,+,-,-,+)`. -/
example (hPT : KLPT 3 1 1) :
    (∃ C : ℝ, 0 < C ∧
      ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (4 - 1)) ∧
    (∃ C : ℝ, 0 < C ∧
      ‖KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) ![true, true, false, false, true]
          ![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2], ![3, 4, 0]] ∅‖
        ≤ C * ((5 : ℕ) : ℝ) ^ (1 : ℝ) * (Bparam 3 5 (1 / 2) (9 / 10) 0) ^ (5 - 1)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨C, hC, H⟩ := KLInduct_Kpi_empty_bound 3 4 1 1 (by norm_num) (by norm_num) one_pos
      one_pos hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar KLInduct_instσ KLInduct_insta⟩
  · obtain ⟨C, hC, H⟩ := KLInduct_Kpi_empty_bound 3 5 1 1 (by norm_num) (by norm_num) one_pos
      one_pos hPT 1 one_pos
    exact ⟨C, hC, H KLinstPar ![true, true, false, false, true]
      ![![0, 0, 0], ![1, 0, 0], ![0, 1, 2], ![2, 2, 2], ![3, 4, 0]]⟩

/-- Target 3, `KLKpi_cut` at `n = 4`: `σ = (+,+,-,-)`, `π = {(0,2)}`, `J = (0,2)` (a long edge, innermost,
`F₀ = {(0,2)}`), all hypotheses discharged: the layer `K^{({(0,2)})}` is `t ∑_{u,w} A(u) S^{(B)}_{uw}
K^{(∅)}(w)` with the inner triangle `(0,1,2)` and the outer triangle `(0,2,3)`. -/
example :
    KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) KLInduct_instσ KLInduct_insta {KLInduct_instJ}
      = ∑ u : Zd 3 5, ∑ w : Zd 3 5,
          ((9 / 10 : ℝ) : ℂ) *
            (∑ δ ∈ Finset.univ.filter
                (fun δ : Fin (KLwIn KLInduct_instJ + 1) → Zd 3 5 => δ (Fin.last _) = u),
              KLSigmaPi 3 5 (1 / 2) (mSigma 0) (9 / 10) (sigmaIn KLInduct_instσ KLInduct_instJ) ∅ δ *
                ∏ i ∈ Finset.univ.erase (Fin.last (KLwIn KLInduct_instJ)),
                  thetaEdge 3 5 (1 / 2) (mSigma 0) (9 / 10) (sigmaIn KLInduct_instσ KLInduct_instJ i)
                    (sigmaIn KLInduct_instσ KLInduct_instJ (i + 1))
                    (KLInduct_aIn KLInduct_instJ KLInduct_insta i) (δ i))
            * SB 3 5 (1 / 2) u w *
          KLKpi 3 5 (1 / 2) (mSigma 0) (9 / 10) (sigmaOut KLInduct_instσ KLInduct_instJ)
            (KLInduct_aOut KLInduct_instJ KLInduct_insta w)
            (((({KLInduct_instJ} : Finset (Fin 4 × Fin 4)).erase KLInduct_instJ).image
              (KLshiftOut KLInduct_instJ))) :=
  KLKpi_cut 3 5 (1 / 2) (by norm_num) (n := 4) (by norm_num) (mSigma 0) (9 / 10)
    (fun s s' => norm_mul_mSigma_lt_one (E := 0) (t := 9 / 10) (by norm_num) (by norm_num)
      (by norm_num) s s')
    KLInduct_instσ (F₀ := {KLInduct_instJ}) (by rw [TSP_four]; decide)
    (π := {KLInduct_instJ}) (J := KLInduct_instJ) (by decide) (by decide)
    (fun e he _ => Finset.mem_singleton.1 he) KLInduct_insta

/-- Target 1, the helpers of the `n ≤ 3` bounds at the instance data: the sup bound
`|Θ^{(σ_1,σ_2)}_t(a,b)| ≤ C_d B_{t,0}` (`KLedge_sup`) and the `ℓ¹` bound of a short edge (`KLedge_l1`). -/
example (hPT : KLPT 3 1 1) :
    (∃ Cd : ℝ, 0 < Cd ∧
      ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 false))
          (KLinsta 1) (KLinsta 2)‖ ≤ Cd * Bparam 3 5 (1 / 2) (9 / 10) 0) ∧
    (∃ S : ℝ, 0 < S ∧
      ∑ b : Zd 3 5, ‖Theta 3 5 (1 / 2) (((9 / 10 : ℝ) : ℂ) * (mSigma 0 true * mSigma 0 true))
          (KLinsta 1) b‖ ≤ S) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨Cd, hCd, H⟩ := KLedge_sup hPT
    refine ⟨Cd, hCd, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) (9 / 10) (by norm_num)
      (by norm_num) (mSigma 0 true * mSigma 0 false) ?_ (KLinsta 1) (KLinsta 2)⟩
    rw [norm_mul, norm_mSigma (by norm_num), norm_mSigma (by norm_num), mul_one]
  · obtain ⟨S, hS, H⟩ := KLedge_l1 (k := 1) (κ := 1) (gmax := 1) one_pos hPT.short
    exact ⟨S, hS, H 5 (by norm_num) (1 / 2) (by norm_num) (by norm_num) 0 (by norm_num) true
      (9 / 10) (by norm_num) (by norm_num) (KLinsta 1)⟩

/-- Target 1, `KLstar_le`, `KLone_le_rpow`, `KLTheta_eq_zero` at concrete data. -/
example :
    ‖∑ b : Fin 2, ((b : ℕ) + 1 : ℂ) * 1 * 1‖ ≤ (1 : ℝ) ^ 2 * 3 ∧
    (1 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (1 / 2 : ℝ) ∧
    Theta 3 5 (1 / 2) ((9 / 10 : ℝ) : ℂ) (KLinsta 1) (KLinsta 2)
      = Theta 3 5 (1 / 2) ((9 / 10 : ℝ) : ℂ) 0 (KLinsta 1 - KLinsta 2) := by
  refine ⟨?_, KLone_le_rpow (by norm_num) (by norm_num), ?_⟩
  · refine KLstar_le (fun b : Fin 2 => ((b : ℕ) + 1 : ℂ)) (fun _ => 1) (fun _ => 1) zero_le_one
      (fun _ => by simp) (fun _ => by simp) ?_
    simp [Fin.sum_univ_two]
    norm_num
  · exact KLTheta_eq_zero (by norm_num) (by
      rw [Complex.norm_real, Real.norm_of_nonneg (by norm_num)]; norm_num) _ _

end Instances

end RBM.Loop
