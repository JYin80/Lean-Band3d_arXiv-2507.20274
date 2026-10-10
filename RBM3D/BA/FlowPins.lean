/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MFixedPoint
import RBM3D.Induction.Defs
import RBM3D.Induction.Step2Defs
import RBM3D.Loop.KLTree

/-!
# The block Anderson chain pins over a law (BA-C1a = BA-D1b + the closure of D472)

Ticket T2197 (with Amend 1, Amend 2).  Sections:

1. the fine-lattice `M` of `(def_G0)` is `M^{(B)} ⊗ I_{W^d}`, and the two normalised traces
   agree (D472: `BASelf` is the paper's `(self_m)`, `1_2:626-633`);
2. the propagator pins `BAProp5 … BAProp5to8`, stated only (T2161 probe
   `RBM3D/Probe/T2161Pins.lean` on `t/T2161` at 82e72b3, section 4, `:661-736`);
3. the flow `H_t = g₀ Ψ + √t V` and its loops (probe section 5, `:744-811`);
4. the flow carrier `FlowFM` over a law `μ` (probe section 6, `:819-1008`, with the law parameter of
   `RBM3D/Probe/T2173Pins.lean` on `t/T2173` at a543154, `:1932-2055`), and the band bridges;
5. the flow data, `STMainIndG`, `lem_ConArg_BA` as `BAConArg'` (probe section 7,
   `:1016-1191`), with the law `Sizes.seqP (sz.withLam 0)`;
6. extra target (a): `(self_m)` has no solution beyond `2 + 2d|g|` (`baSelf_none_of_gt`);
7. `BAConArg'_premise_diag`;
8. extra target (b): the unrepaired `BAConArg` is refuted under data beyond the support
   (`not_BAConArg_of_data`);
9. compiled nonempty instances in `RBM.BA.FlowPinsInst`.

Not in this file (Amend 1, Amend 2): `BAMainInd`, `BAStep1`, `BAGbEXP`, `BAGbEXPpre`,
`BAGbEXPconcl`.
Paper: `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`),
`paper/tex/7_8_light_weight.tex` (`7_8:line`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 1. Target 1 (D472): the fine-lattice `M` and `(self_m)` with `N⁻¹ tr` -/

section Fine

/-- `(self_m)` as the paper writes it (`1_2:626-629`), on the fine lattice:
`m = N⁻¹ tr (gΨ - z - m)⁻¹`, `Ψ = Ψ^{(B)} ⊗ I_{W^d}` (`1_2:615`, merged `PsiI`), `N = (WL)^d`, `Im m > 0`. -/
def BASelfFine (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace

private theorem FlowPins_psiI_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) :
    ((g : ℂ) • PsiI d L W) =
      (((g : ℂ) • PsiB d L) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).submatrix
        (splitEquiv d L W) (splitEquiv d L W) := by
  unfold PsiI PsiV
  rw [smul_kronecker]
  rfl

/-- Target 1a: `(def_G0)` (`1_2:631-633`), `M = M^{(B)} ⊗ I_{W^d}` on the fine lattice (through the merged
bridge `splitEquiv`, as `PsiI` is built from `PsiV`). -/
theorem BAMres_fine_kron (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
      Mres ((g : ℂ) • PsiI d L W) z m =
        ((BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) : Matrix (Vtx d L W) (Vtx d L W) ℂ)).submatrix
          (splitEquiv d L W) (splitEquiv d L W) := by
  intro g z m hw
  set e := splitEquiv d L W with he
  set A : Matrix (Zd d L) (Zd d L) ℂ := ((g : ℂ) • PsiB d L) - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) with hA
  have hunit : IsUnit A := RBM.isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L g) hw
  have hBAMB : BAMB d L g z m = Ring.inverse A := rfl
  have hK : (A ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (((g : ℂ) • PsiB d L) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)) -
        (z + m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) := by
    rw [hA, sub_eq_add_neg, ← neg_smul, add_kronecker]
    simp only [smul_kronecker, Matrix.one_kronecker_one]
    rw [neg_smul, ← sub_eq_add_neg]
  have hdecomp : ((g : ℂ) • PsiI d L W) - (z + m) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) =
      (A ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).submatrix e e := by
    rw [hK, FlowPins_psiI_eq, Matrix.submatrix_sub, Matrix.submatrix_smul]
    simp only [Pi.sub_apply, Pi.smul_apply, Matrix.submatrix_one_equiv]
    rfl
  have hprod : (A ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).submatrix e e *
      ((Ring.inverse A) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul, Ring.mul_inverse_cancel _ hunit,
      mul_one, Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]
  unfold Mres
  rw [hdecomp, hBAMB, ← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.inv_eq_right_inv hprod

/-- Target 1b: the entrywise form, `M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}`. -/
theorem BAMres_fine_apply (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 → ∀ x y : Idx d L W,
      Mres ((g : ℂ) • PsiI d L W) z m x y =
        if (split d L W x).2 = (split d L W y).2 then BAMB d L g z m (split d L W x).1 (split d L W y).1 else 0 := by
  intro g z m hw x y
  rw [BAMres_fine_kron d L W g z m hw]
  simp only [Matrix.submatrix_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  have h1 : splitEquiv d L W x = split d L W x := rfl
  have h2 : splitEquiv d L W y = split d L W y := rfl
  rw [h1, h2]
  by_cases h : (split d L W x).2 = (split d L W y).2 <;> simp [h]

/-- Target 1c: the two normalised traces agree, `N⁻¹ tr M = L^{-d} tr M^{(B)}` (D472). -/
theorem BAfine_trace (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
      ((((W * L) ^ d : ℕ) : ℂ))⁻¹ * (Mres ((g : ℂ) • PsiI d L W) z m).trace =
        (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace := by
  intro g z m hw
  rw [BAMres_fine_kron d L W g z m hw]
  have htr : ((BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) :
      Matrix (Vtx d L W) (Vtx d L W) ℂ).submatrix (splitEquiv d L W) (splitEquiv d L W)).trace =
      (BAMB d L g z m).trace * ((W ^ d : ℕ) : ℂ) := by
    have h1 : ((BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) :
        Matrix (Vtx d L W) (Vtx d L W) ℂ).submatrix (splitEquiv d L W) (splitEquiv d L W)).trace =
        (BAMB d L g z m ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).trace := by
      unfold Matrix.trace
      exact Equiv.sum_comp (splitEquiv d L W) (fun j => (BAMB d L g z m ⊗ₖ
        (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).diag j)
    rw [h1, Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin]
  rw [htr]
  have hW : ((W : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have hL : ((L : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  push_cast
  field_simp
  rw [mul_pow]
  ring

/-- Target 1d: the block-lattice `(self_m)` of the merged `BASelf` is the paper's, for every `Im z ≥ 0` (real
axis included), every `W ≥ 1`. -/
theorem BASelf_iff_fine (d L W : ℕ) [NeZero L] [NeZero W] :
    ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im → (BASelfFine d L W g z m ↔ BASelf d L g z m) := by
  intro g z m hz
  unfold BASelfFine BASelf
  constructor
  · rintro ⟨hm, h⟩
    have hw : (z + m).im ≠ 0 := by
      rw [Complex.add_im]; linarith
    exact ⟨hm, by rw [← BAfine_trace d L W g z m hw]; exact h⟩
  · rintro ⟨hm, h⟩
    have hw : (z + m).im ≠ 0 := by
      rw [Complex.add_im]; linarith
    exact ⟨hm, by rw [BAfine_trace d L W g z m hw]; exact h⟩

end Fine


/-! ## 2. Target 2: the propagator pins of the block Anderson model: `lem_propTH` properties 5-8 for `Θ^{(σ₁,σ₂)}_t`

`1_2:1124-1167`, proof `A:1-70`; the BA remark `1_2:1150`: "constants may also depend on `λ⁻¹` when
`1 ≤ λ ≤ 𝔡⁻¹`".  The statements are those of `RBM3D/Propagator/Pins.lean` (`Prop5Decay`, `Prop5Short`,
`Prop6Diff1`, `Prop7Diff2`, `Prop8ZeroMode`: shape `PropThetaQ`), with the data `(g, E, m)` of the bulk
(`BAReal`) in place of `‖m‖ = 1`: constants `(d, Λ, κ)` (`(d, Λ, κ, c)` for 6, 7) fixed before `L, g, E, m`,
`g ∈ (0, Λ]`, `3 ≤ L`, `t ∈ [0, 1)`, both charge pairs, no loss (`≺` of 6-8 is no loss), `|r| ≤ c |a|`,
`0 < c < 1` (T2003b).  Registry class: owed (PT-BA tickets; the band pins are proved, the BA kernel
`M^{(+,-)}` is a general doubly stochastic kernel and needs its own route, report (b.6)). -/

section PTPins

variable (d : ℕ)

/-- **Property 5** `(prop:ThfadC)`: `|Θ_t(0,a)| ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}`. -/
def BAProp5 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 5, short form** `(prop:ThfadC_short)`, `σ₁ = σ₂`: `|Θ_t(0,a)| ≤ C_κ(1_{a=0} + g² e^{-c_κ|a|})`;
the BA proof is the Taylor expansion `(eq:expMLn)` with `(eq:off_diagM)` (`BAoffDiag`). -/
def BAProp5s (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ σ 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Property 6** `(prop:BD1)`: `|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}`, `|r| ≤ c|a|`. -/
def BAProp6 (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Property 7** `(prop:BD2)`: `|Θ_t(0,a+r) + Θ_t(0,a-r) - 2Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r|² (|a|+1)^{-d}`. -/
def BAProp7 (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) + BATheta d L g E m t σ₁ σ₂ 0 (a - r)
              - 2 * BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) ^ 2 * (((zdistD d L a : ℝ) + 1) ^ d)⁻¹

/-- **Property 8** `(prop:ThfadC0)`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`. -/
def BAProp8 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-- The bundle: properties 5-8 of `lem_propTH` for the block Anderson model at one `(d, Λ, κ, c)`. -/
structure BAProp5to8 (Λ κ c : ℝ) : Prop where
  decay : BAProp5 d Λ κ
  short : BAProp5s d Λ κ
  diffOne : BAProp6 d Λ κ c
  diffTwo : BAProp7 d Λ κ c
  zeroMode : BAProp8 d Λ κ

end PTPins

end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 3. Target 3: the flow of the block Anderson model along a size sequence, and the loops `𝓛`, `𝒦`

`H_t = g₀ Ψ + √t V` (`(MBM)`, `1_2:685`; merged `Sizes.seqHflowBA`, T2013) with `V` the model of `sz.withLam 0`
(`S^{(B)}(0) = I`); `z_t(E, g₀) = E + (1-t) m(E, g₀)` (`(eq:zt)`, `1_2:716`).  The flow parameters `(E, g₀)` are
arguments: `lem_ConArg_BA` (`7_8:1956`) compares two couplings `g`, `g_s = g √(s/t)` at the same `E`. -/

section Flow

variable {d : ℕ} (sz : Sizes d)

/-- `m(E_n, g₀_n)`: the real-axis solution of `(self_m)` at the flow parameters. -/
def BAmF (lam0 E : ℕ → ℝ) (n : ℕ) : ℂ := BAm d (sz.L n) (lam0 n) (E n : ℂ)

/-- `M(E, g₀)` on the fine lattice, `M = M^{(B)} ⊗ I_{W^d}` (`(def_G0)`, `1_2:631`); time independent. -/
def BAMfine (lam0 E : ℕ → ℝ) (n : ℕ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Mres ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz lam0 E n)

/-- `G_t(z_t)` entries of the block Anderson flow (`def_flow`, `(self_Gt)`, `1_2:725`). -/
def BAGt (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) true

/-- **`𝓛^{(k)}_{t,σ,a}`** of the block Anderson flow (`(Eq:defGLoop)`, `1_2:824`). -/
def BALloop (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) σ a

end Flow

section KLoops

variable (d L W : ℕ) [NeZero L]

/-- The block Anderson `M`-loop initial data `𝓜^{(k)}_{σ,a} = tr ∏_i (M(σ_i) E_{a_i}) = W^{-(k-1)d} ∏_i M(σ_i)_{a_{i-1} a_i}` (cyclic, `a_{-1} = a_{k-1}`: `σ_i` sits on the edge `(a_{i-1}, a_i)`; `(eq:KMloop)` `1_2:1003`,
`A:571`, merged `loopM`); `M = M^{(B)} ⊗ I_{W^d}`; the band case is `M(σ) = m(σ) I` (merged `MLoop`). -/
def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) *
    ((I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map fun p => M p.1 p.2.1 p.2.2).prod

/-- **The `𝒦`-loops of the block Anderson model**: the solution of the convolution tree equations with the
kernel `S^{(B)}(0) = I` and the initial data `𝓜` (`Def_Ktza` for `BA`, `1_2:1051`; the merged kernel-generic
`IsKLoopS`, `RBM3D/Loop/KLTree.lean:828`); `0` if there is none (pin `BAKexists`). -/
def BAKsol (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ) : ℝ → LoopIdx (Zd d L) → ℂ :=
  haveI := Classical.propDecidable
    (∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W M)
      (Set.Ico (0 : ℝ) 1) K)
  if h : ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m
      (BAMLoop d L W M) (Set.Ico (0 : ℝ) 1) K then h.choose else fun _ _ => 0

end KLoops

section Flow2

variable {d : ℕ} (sz : Sizes d)

/-- **`𝒦^{(k)}_{t,σ,a}`** of the block Anderson flow at `(E, g₀)`: `M(σ) = (M^{(B)}, (M^{(B)})^*)`,
`m(σ) = (m, m̄)`. -/
def BAKloop (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  BAKsol d (sz.L n) (sz.W n)
    (BAMsigma d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)))
    (PropSpin (BAmF sz lam0 E n)) t (KLloopOf d (sz.L n) σ a)

/-- `(G_t - M)_{xy}` of the block Anderson flow, with the non-scalar `M = M(E, g₀)` (the first change of
`lem:main_ind_BA`, `7_8:1825`). -/
def BAGM (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  BAGt sz lam0 E n t ω x y - BAMfine sz lam0 E n x y

end Flow2


end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 4. Target 4: one pin shape for both models, the flow carrier over a law

The stochastic pins of the chain (`STLK`, `STDecay`, ..., `STMainInd`; `RBM3D/Induction/Defs.lean`) mention the
model only through four objects: `𝓛` (`Lloop`), `𝒦` (`STKloop`), `G_t` (`Gt`) and `M` (`mE E · I`).  The carrier
`FlowFM` bundles them; the estimate-level predicates are restated over it (`STLKgL`, ...), with the law `μ` of the
sample space as an explicit argument right after the carrier (T2173a, DECISIONS §57 (3), §58 (3)): the band
instance is `μ = seqP sz` (the bridges below are `Iff.rfl`), the block Anderson instance is
`μ = seqP (sz.withLam 0)` (the law of `UNModel.ba`; `S^{(B)}(0) = I`, `bandcwV`, `1_2:606`).  The probe's
`Prec`-forms without a law are not ported.  This makes "the unchanged steps reuse the ST pins with `M` for `m`" a
compiled statement; it does **not** make the merged band *proofs* generic. -/

/-- `≺` of the chain at an arbitrary law `μ` on the common sample space (`Prec sz` is the case `μ = seqP sz`;
the block Anderson law is `seqP (sz.withLam 0)`). -/
def PrecL {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) {U : ℕ → Type*} (ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ) : Prop :=
  StochDomAt μ sz.size ξ ζ

/-- The four model objects of the stochastic estimates. -/
structure FlowFM {d : ℕ} (sz : Sizes d) where
  /-- `𝓛^{(k)}_{t,σ,a}` at size index `n` -/
  L : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → sz.SeqΩ → ℂ
  /-- `𝒦^{(k)}_{t,σ,a}` -/
  K : ∀ (n : ℕ) (t : ℝ) {k : ℕ}, (Fin k → Bool) → (Fin k → Zd d (sz.L n)) → ℂ
  /-- the entries of `G_t` -/
  G : ∀ (n : ℕ) (t : ℝ), sz.SeqΩ → Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
  /-- the entries of `M` -/
  M : ∀ n : ℕ, Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ
  /-- the block kernel `S^{(B)}` of the variance (`S^{(B)}(g)` for the band model, `S^{(B)}(0) = I` for `BA`) -/
  S : ∀ n : ℕ, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ
  /-- `η_t` (`(eta)`, `1_2:720`) -/
  eta : ∀ (n : ℕ) (t : ℝ), ℝ
  /-- the one-loop value `m` (`𝒦^{(1)}_{+} = m(E)`, `Def_Ktza`) -/
  m : ℕ → ℂ

section Generic

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ)

/-- `(G_t - M)_{xy}`. -/
def FlowFM.GM (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  C.G n t ω x y - C.M n x y

/-- `(Eq:L-KGt)` (a): `max |𝓛^{(k)} - 𝒦^{(k)}| ≺ (W^{-d}B_{τ,0})^k`. -/
def STLKgL (τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω - C.K n (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k)

/-- `(Eq:L-KGt2)`: `max |𝓛^{(k)}| ≺ (W^{-d}B_{τ,0})^{k-1}`. -/
def STLmaxgL (τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- `(Eq:Gdecay)`: the decay of `𝓛^{(2)} - 𝒦^{(2)}`. -/
def STDecaygL (τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (τ n) p.1 p.2 ω - C.K n (τ n) p.1 p.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ (1 / 5 : ℝ) *
          STWB sz n (τ n) (zdistInf d (sz.L n) (p.2 0 - p.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (τ n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `(Eq:Gdecay+s<g)`: only at the sizes with `1 - τ ≥ lam²`. -/
def STDecayStronggL (τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecL sz μ
      (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - τ n})
      (fun n p ω => ‖C.L n (τ n) p.1.1 p.1.2 ω - C.K n (τ n) p.1.1 p.1.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `(Gt_bound+IND)`: `‖G_τ - M‖_max ≺ (W^{-d}B_{τ,0})^{1/2}`. -/
def STLocalMaxgL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))

/-- `(Gt_bound)`: `|(G_τ - M)_{xy}|² ≺ W^{-d} B_{τ,|[x]-[y]|}`. -/
def STLocalEntrygL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))

/-- `(Eq:Gtlp_exp)`: `|𝔼 𝓛^{(2)} - 𝒦^{(2)}| ≺ (W^{-d}B_{τ,0})²((lam² W^d)^{-1/5} + W^{-d}B_{τ,0})`. -/
def STExp2gL (τ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, C.L n (τ n) p.1 p.2 ω ∂μ) - C.K n (τ n) p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))


/-- `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)}` (the control of `(GiiGEX)`, `3_5:21`). -/
def STmaxLoop2g (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖C.L n t ![false, true] ![p.1, p.2] ω‖)

/-- `(initialGT2)` (`3_5:28-30`): `‖G_t - M‖_max ≺ W^{-ε₀}` and `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Ψ_t²`. -/
def STInitialGT2gL (t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖C.GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    PrecL sz μ (U := fun _ => Unit) (fun n _ ω => STmaxLoop2g C n (t n) ω)
      (fun n _ _ => Ψ n ^ 2)

/-- `(Eq:L-KGt)`-type bound `max_{σ,a} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}` (`ML:Kbound`, `1_2:1056`). -/
def STKboundgL : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    ∀ k : ℕ, 1 ≤ k →
      PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖C.K n (τ n) p.1 p.2‖) (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- `(lRB1)`, uniform in `u ∈ [s,t]` (`1_2:1321`). -/
def STStep1LoopgL (s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- `(Gtmwc)`, uniform in `u ∈ [s,t]` (`1_2:1327`). -/
def STStep1WeakgL (s t : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖C.GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

/-- The random control `Ĵ^ℓ_{u,D}` (`(defCALJ)`, `3_5:365`): `max |(𝓛-𝒦)^{(2)}_{u,σ,a}| / [W^{-d} 𝒯̃^ℓ_{u,D}(|a₁-a₂|)]`. -/
def STJhatg (n : ℕ) (D ℓ u : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))

/-- `(eq:LW_assm_exp)` (`3_5:409`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)`, `σ ∈ {(+,-),(-,+)}`. -/
def STLWassmExpgL (t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
  PrecL sz μ (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖C.L n (t n) p.1.1 p.2 ω‖)
    (fun n p _ => STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))

/-- **The quadratic-variation loop `(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a}`** (`def:CALE`, `3_5:176-190`, `n = 2`):
`W^d Σ_{c,c'} S^{(B)}_{cc'} 𝓛^{(6)}_{(σ⊗σ̄)^{(k)}, (a⊗a)^{(k)}(c',c)}`, with the kernel `S` of the carrier
(`S^{(B)}(g)` for the band model, `I` for `BA`). -/
def STEEg (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n),
    C.S n c c' *
      (if k = 0 then
        C.L n u ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c] ω
      else
        C.L n u ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c', a 0, a 1, c] ω)

end Generic

/-- **The band carrier at the energy sequence `E`.** -/
def bandFM {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) : FlowFM sz where
  L := fun n t {_k} σ a ω => Lloop sz n (E n) t σ a ω
  K := fun n t {_k} σ a => STKloop sz n (E n) t σ a
  G := fun n t ω x y => Gt sz n (E n) t true ω x y
  M := fun n x y => if x = y then mE (E n) else 0
  S := fun n => SB d (sz.L n) (sz.lam n)
  eta := fun n t => etaT (E n) t
  m := fun n => mE (E n)

/-- **The block Anderson carrier at the flow parameters `(g₀, E)`.** -/
def baFM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : FlowFM sz where
  L := fun n t {_k} σ a ω => BALloop sz lam0 E n t σ a ω
  K := fun n t {_k} σ a => BAKloop sz lam0 E n t σ a
  G := fun n t ω x y => BAGt sz lam0 E n t ω x y
  M := fun n x y => BAMfine sz lam0 E n x y
  S := fun n => 1
  eta := fun n t => etaOf (BAmF sz lam0 E n) t
  m := fun n => BAmF sz lam0 E n

/-- *Proved (`Iff.rfl`).* The estimate-level pins of `lem:main_ind` over `bandFM` at the law `seqP sz` are the
merged band pins (`Prec sz` is `PrecL sz (seqP sz)`). -/
theorem bandFM_STLK {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STLK sz E τ ↔ STLKgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STLmax {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STLmax sz E τ ↔ STLmaxgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STDecay {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STDecay sz E τ ↔ STDecaygL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STDecayStrong {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STDecayStrong sz E τ ↔ STDecayStronggL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STLocalMax {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STLocalMax sz E τ ↔ STLocalMaxgL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STLocalEntry {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STLocalEntry sz E τ ↔ STLocalEntrygL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STExp2 {d : ℕ} (sz : Sizes d) (E τ : ℕ → ℝ) :
    STExp2 sz E τ ↔ STExp2gL (bandFM sz E) (Sizes.seqP sz) τ := Iff.rfl
theorem bandFM_STInitialGT2 {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) :
    STInitialGT2 sz E t ε₀ Ψ ↔ STInitialGT2gL (bandFM sz E) (Sizes.seqP sz) t ε₀ Ψ := Iff.rfl
theorem bandFM_STKbound {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
    STKbound sz E ↔ STKboundgL (bandFM sz E) (Sizes.seqP sz) := Iff.rfl
theorem bandFM_STStep1Loop {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
    STStep1Loop sz E s t ↔ STStep1LoopgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STStep1Weak {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) :
    STStep1Weak sz E s t ↔ STStep1WeakgL (bandFM sz E) (Sizes.seqP sz) s t := Iff.rfl
theorem bandFM_STLWassmExp {d : ℕ} (sz : Sizes d) (E t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) :
    STLWassmExp sz E t D ℓ ↔ STLWassmExpgL (bandFM sz E) (Sizes.seqP sz) t D ℓ := Iff.rfl
/-- The quadratic-variation loop of the band model is `STEEg` at the band carrier, for the model sample. -/
theorem bandFM_STEEk {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    STEEk sz n (E n) u k σ a ω = STEEg (bandFM sz E) n u k σ a ω := rfl

end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 5. Target 5: `lem:main_ind_BA` and the steps that change (flow data, `lem_ConArg_BA`)

The flow data along a sequence of spectral parameters `z` (`(eq:t0E0_BA)`, `7_8:1798`): `t₀`, `E`, `g₀ = √t₀ g`.
The setting `BAFlow` replaces `STFlow`: admissible sizes (`(Main_DEL_COND)`, `(eq:WO)`) and `z_n` in the chain
domain `BAdom` (`Im m(z_n, g_n) ≥ κ`, `N^{-1+ε} ≤ Im z_n ≤ 1`); there is no `|Re z| ≤ 2 - κ` (`7_8:1797` is a typo,
T2001g) and no `e_λ`. -/

section FlowData

variable {d : ℕ} (sz : Sizes d)

/-- `t₀_n` of `(eq:t0E0_BA)`. -/
def BAflowT0 (z : ℕ → ℂ) (n : ℕ) : ℝ := BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))

/-- `E_n` of `(eq:t0E0_BA)`. -/
def BAflowEs (z : ℕ → ℂ) (n : ℕ) : ℝ := BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n))

/-- `g₀_n = √t₀_n g_n` of `(eq:t0E0_BA)`. -/
def BAflowLam0 (z : ℕ → ℂ) (n : ℕ) : ℝ := Real.sqrt (BAflowT0 sz z n) * sz.lam n

/-- The setting of `MR:decol_BA`, `lem:main_ind_BA`, `zztE_BA` along a sequence (replaces `STFlow`). -/
def BAFlow (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)

/-- The block Anderson carrier at the flow parameters of `z`. -/
def baFMz (z : ℕ → ℂ) : FlowFM sz := baFM sz (BAflowLam0 sz z) (BAflowEs sz z)

end FlowData


/-! The law of every block Anderson statement of this section is `Sizes.seqP (sz.withLam 0)` (L3, §57 (3)).
`BAMainInd`, `BAStep1` (T2161 `:1071`, `:1170`) are not pinned here (Amend 1: BA-D3 redesigns Step 1 and the
induction), nor are `BAGbEXP`, `BAGbEXPpre`, `BAGbEXPconcl` (Amend 2, line 3). -/

section MainInd

/-- **`lem:main_ind`, one statement for every model** (`1_2:1256-1330`; `7_8:1825`): the pin `STMainInd` with the
law of the sample space `law`, the setting `Flow`, the carrier `mk` and the flow horizon `T0` as parameters (L2:
every predicate inside is stated at `law sz`).  Constants first (`κ, ε, 𝔡`, then `𝔠_d ∈ (0, 10^{-2}]`, then `𝔠`,
the sizes and `z`). -/
def STMainIndG (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ T0 sz z n) → (∀ n, s n < t n) →
          (∀ n, t n ≤ T0 sz z n) →
          (STLKgL (mk sz z) (law sz) s ∧ STDecaygL (mk sz z) (law sz) s ∧
            STDecayStronggL (mk sz z) (law sz) s ∧ STLocalMaxgL (mk sz z) (law sz) s ∧
            STExp2gL (mk sz z) (law sz) s) →
          STConStInd sz 𝔠d s t →
          STLKgL (mk sz z) (law sz) t ∧ STLmaxgL (mk sz z) (law sz) t ∧ STDecaygL (mk sz z) (law sz) t ∧
            STExp2gL (mk sz z) (law sz) t ∧ STLocalEntrygL (mk sz z) (law sz) t ∧
            STDecayStronggL (mk sz z) (law sz) t

/-- *Proved (`Iff.rfl`).* The merged band pin `STMainInd` is `STMainIndG` at the band law `seqP sz`, the band
setting, carrier and horizon. -/
theorem STMainInd_iff (d : ℕ) :
    STMainInd d ↔ STMainIndG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

end MainInd

section ConArg

/-- `Im G_{vv}` for unit vectors `v` of `ℂ^N` (`7_8:1976`): `v^* G v`. -/
def BAvecEntry {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star v ⬝ᵥ (A *ᵥ w)

/-- The scale-`s` coupling of `lem_ConArg_BA`: `g_s = g₀ √(s/t)`. -/
def BAlamS {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Real.sqrt (s n / t n) * BAflowLam0 sz z n

/-- `lem_ConArg_BA` (1), `(res_lo_bo_eta_BA)` (`7_8:1965`): `max |𝓛^{(k)}_{t,σ,a}(z_t, g₀)| ≺ ((η_s/η_t) W^{-d}B_{s,0})^{k-1}
max_a tr(Im G_t E_a)`, under the block Anderson law `seqP (sz.withLam 0)`. -/
def BAConArgLoop {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
    (fun n p ω => ((etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
          (baFMz sz z).eta n (t n)) * sz.Bctl n (s n)) ^ (k - 1) *
        Finset.univ.sup' ⟨(0 : Zd d (sz.L n)), Finset.mem_univ _⟩
          (fun a => ((baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω -
            (baFMz sz z).L n (t n) (fun _ : Fin 1 => false) (fun _ => a) ω).im / 2))

/-- `lem_ConArg_BA` (2), `(eq:ImGs)`, `(eq:ImGt)` (`7_8:1976-1979`): the vector bounds, for deterministic unit vectors,
w.h.p. under the block Anderson law `seqP (sz.withLam 0)` (`Whp sz Ξ` is `HighProbAt (seqP sz) sz.size Ξ`). -/
def BAConArgVec {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  ∀ v w : ∀ n, Idx d (sz.L n) (sz.W n) → ℂ,
    (∀ n, star (v n) ⬝ᵥ (v n) = 1) → (∀ n, star (w n) ⬝ᵥ (w n) = 1) →
    (∃ C₀ : ℝ, 0 < C₀ ∧ HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω |
      (BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) (v n) (v n)).im ≤ C₀ ∧
      (BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) (w n) (w n)).im ≤ C₀ ∧
      ‖BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) (v n) (w n)‖ ≤ C₀})) →
    ∃ C₁ : ℝ, 0 < C₁ ∧ HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω |
      (BAvecEntry (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω) (v n) (v n)).im ≤
        C₁ * (etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) / (baFMz sz z).eta n (t n)) ∧
      ‖BAvecEntry (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω) (v n) (w n)‖ ≤
        C₁ * (etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) / (baFMz sz z).eta n (t n))})

/-- **`lem_ConArg_BA`, repaired** (`7_8:1956-1981`; proof "exactly Lemma 7.1 of [RBSO1D]", `7_8:1987`), pinned as
`BAConArg'` (Amend 1, L5; DECISIONS §68; supervisor `2026-10-05-1806` §1.4: the unrepaired pin is false, because at
`g_s = √(s/t) g₀` the energy can leave the support of `ρ_N`, so `η_s = 0`).  For `ε₁ ≤ s ≤ t < 1`, the premise that
the energy is in the `κ`-bulk at the coupling `g_s` (`κ ≤ Im m(E_n, g_s)`), and the loop bound `(eq:loopbound_s)`
at time `s` for the loops at `(z_s, g_s)`: `BAConArgLoop` for every `k ≥ 2` (no indicator `Ω_t`) and
`BAConArgVec`, all under the law `seqP (sz.withLam 0)`.  Registry class: owed (BA-S1). -/
def BAConArg' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) →
        STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
        (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t

end ConArg

section Step1

/-- *Proved (`Iff.rfl`).* The band `STStep1` is the same pin at the band carrier and the band law `seqP sz`. -/
theorem STStep1_iff (d : ℕ) :
    STStep1 d ↔ ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
            (∀ n, t n ≤ lemT (z n)) →
            STKboundgL (bandFM sz (STflowE z)) (Sizes.seqP sz) →
            STLKgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s →
            STLocalMaxgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s → STConStInd sz 𝔠d s t →
              STStep1LoopgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t ∧
                STStep1WeakgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t := Iff.rfl

end Step1


end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 6. Extra target (a): no solution of `(self_m)` beyond the support (Amend 1, supervisor `2026-10-05-1806` §1.6)

The spectrum of `g Ψ^{(B)}` lies in `[-2d|g|, 2d|g|]`, and `(self_m)` forces `|m| ≤ 1` at real `z`; so for
`|E| > 2 + 2d|g|` it has no solution, `BAm = 0` (dite default) and `ρ_N = 0`. -/

private theorem FlowPins_zdist_one {L : ℕ} [NeZero L] {u : ZMod L} (h : zdist L u = 1) :
    u = 1 ∨ u = -1 := by
  have hu : u.val < L := ZMod.val_lt u
  unfold zdist at h
  have hL : 1 ≤ L := NeZero.pos L
  rcases (by omega : u.val = 1 ∨ L - u.val = 1) with h1 | h1
  · left
    rw [← ZMod.natCast_zmod_val u, h1]
    simp
  · right
    have h2 : u.val = L - 1 := by omega
    rw [← ZMod.natCast_zmod_val u, h2, Nat.cast_sub hL]
    simp

private theorem FlowPins_card_nbrs (d L : ℕ) [NeZero L] (a : Zd d L) :
    (Finset.univ.filter fun b : Zd d L => Adj d L a b).card ≤ 2 * d := by
  classical
  let f : Fin d × Bool → Zd d L := fun p => Pi.single p.1 (if p.2 then (1 : ZMod L) else -1)
  have hsub : (Finset.univ.filter fun b : Zd d L => Adj d L a b) ⊆
      Finset.univ.image (fun p => a - f p) := by
    intro b hb
    rw [Finset.mem_filter] at hb
    have hb' : zdistD d L (a - b) = 1 := hb.2
    set x : Zd d L := a - b with hx
    have hne : ∃ k, zdist L (x k) ≠ 0 := by
      by_contra hno
      push Not at hno
      have : zdistD d L x = 0 := Finset.sum_eq_zero fun i _ => hno i
      omega
    obtain ⟨k, hk⟩ := hne
    have hle : zdist L (x k) ≤ 1 := by
      rw [← hb']
      exact Finset.single_le_sum (f := fun j => zdist L (x j)) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
    have hk1 : zdist L (x k) = 1 := by omega
    have hrest : ∀ j ∈ (Finset.univ : Finset (Fin d)).erase k, zdist L (x j) = 0 := by
      have hs := Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun j => zdist L (x j)) (Finset.mem_univ k)
      have hs0 : ∑ j ∈ (Finset.univ : Finset (Fin d)).erase k, zdist L (x j) = 0 := by
        have : zdistD d L x = ∑ j, zdist L (x j) := rfl
        omega
      exact Finset.sum_eq_zero_iff.mp hs0
    have hxj : ∀ j, j ≠ k → x j = 0 := fun j hj =>
      (zdist_eq_zero_iff L).mp (hrest j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))
    rw [Finset.mem_image]
    rcases FlowPins_zdist_one hk1 with h1 | h1
    · refine ⟨(k, true), Finset.mem_univ _, ?_⟩
      have : f (k, true) = x := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [f, h1]
        · simp [f, hj, hxj j hj]
      rw [this, hx]; abel
    · refine ⟨(k, false), Finset.mem_univ _, ?_⟩
      have : f (k, false) = x := by
        funext j
        by_cases hj : j = k
        · subst hj; simp [f, h1]
        · simp [f, hj, hxj j hj]
      rw [this, hx]; abel
  calc (Finset.univ.filter fun b : Zd d L => Adj d L a b).card
      ≤ (Finset.univ.image (fun p : Fin d × Bool => a - f p)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [mul_comm]


/-- The eigenvalues of `Ψ^{(B)}` lie in `[-2d, 2d]` (maximal row sum, at most `2d` neighbours). -/
private theorem FlowPins_eig_le (d L : ℕ) [NeZero L] (j : Zd d L) :
    |(PsiB_isHermitian d L).eigenvalues j| ≤ 2 * d := by
  classical
  have hH := PsiB_isHermitian d L
  set v : Zd d L → ℂ := ⇑(hH.eigenvectorBasis j) with hv
  have hvne : ∃ k, v k ≠ 0 := by
    have h0 := (hH.eigenvectorBasis.orthonormal).ne_zero j
    by_contra hno
    push Not at hno
    apply h0
    ext k
    exact hno k
  have heq : PsiB d L *ᵥ v = ((hH.eigenvalues j : ℝ) : ℂ) • v := hH.mulVec_eigenvectorBasis j
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => ‖v k‖)
  obtain ⟨k0, hk0⟩ := hvne
  have hvi : v i ≠ 0 := by
    intro h
    apply hk0
    have := hi k0
    rw [h, norm_zero] at this
    exact norm_le_zero_iff.mp this
  have hrow := congrFun heq i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hrow
  have hnorm : ‖((hH.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ ≤ (2 * d : ℝ) * ‖v i‖ := by
    calc ‖((hH.eigenvalues j : ℝ) : ℂ)‖ * ‖v i‖ = ‖((hH.eigenvalues j : ℝ) : ℂ) * v i‖ := (norm_mul _ _).symm
      _ = ‖∑ b, PsiB d L i b * v b‖ := by rw [hrow]
      _ ≤ ∑ b, ‖PsiB d L i b * v b‖ := norm_sum_le _ _
      _ ≤ ∑ b, ‖PsiB d L i b‖ * ‖v i‖ := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hi b) (norm_nonneg _)
      _ = ((Finset.univ.filter fun b : Zd d L => Adj d L i b).card : ℝ) * ‖v i‖ := by
          rw [← Finset.sum_mul]
          congr 1
          simp only [PsiB, Matrix.of_apply]
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun b _ => ?_
          by_cases h : Adj d L i b <;> simp [h]
      _ ≤ (2 * d : ℝ) * ‖v i‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact_mod_cast FlowPins_card_nbrs d L i
  have hpos : 0 < ‖v i‖ := norm_pos_iff.mpr hvi
  have := le_of_mul_le_mul_right hnorm hpos
  simpa using this


/-- **Extra target (a)** (supervisor `2026-10-05-1806` §1.1): for real `g, E` with `|E| > 2 + 2d|g|`, `(self_m)` at
`(g, E)` has no solution.  Route: with `w_i = gλ_i - E - m` (`λ_i` the eigenvalues of `Ψ^{(B)}`, `|λ_i| ≤ 2d`,
`BAMB_trace_eq_sum`) the imaginary part of `(self_m)` gives `L^{-d} Σ |w_i|^{-2} = 1`; Cauchy-Schwarz gives
`|m| ≤ 1`, so `|Re m| ≤ 1`; for `|E| > 2 + 2d|g|`, `|Re w_i| > 1` for every `i`, so `L^{-d} Σ |w_i|^{-2} < 1`. -/
theorem baSelf_none_of_gt (d L : ℕ) [NeZero L] (g E : ℝ) (hE : 2 + 2 * d * |g| < |E|) :
    ∀ m : ℂ, ¬ BASelf d L g (E : ℂ) m := by
  intro m hself
  obtain ⟨hm, hmeq⟩ := hself
  have hw : ((E : ℂ) + m).im ≠ 0 := by simpa using hm.ne'
  rw [BAMB_trace_eq_sum d L g (E : ℂ) m hw] at hmeq
  set N : ℝ := (((L ^ d : ℕ) : ℝ)) with hNdef
  have hNpos : 0 < N := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    simpa [hNdef] using (by exact_mod_cast this : (0 : ℝ) < ((L ^ d : ℕ) : ℝ))
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((N⁻¹ : ℝ) : ℂ) := by
    rw [hNdef, Complex.ofReal_inv, Complex.ofReal_natCast]
  set w : Zd d L → ℂ := fun i => (BAspec d L g i : ℂ) - ((E : ℂ) + m) with hwdef
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by rw [Finset.card_univ, BAcard_Zd]
  have hwim : ∀ i, (w i).im = -m.im := by
    intro i; simp [hwdef]
  have hwre : ∀ i, (w i).re = g * (PsiB_isHermitian d L).eigenvalues i - E - m.re := by
    intro i; simp [hwdef, BAspec]; ring
  have hwne : ∀ i, w i ≠ 0 := by
    intro i h
    have := hwim i
    rw [h] at this
    simp at this
    exact hm.ne' (by linarith)
  -- (1) the imaginary part: `Σ_i normSq (w i)⁻¹ = N`
  have hsum2 : ∑ i, (Complex.normSq (w i))⁻¹ = N := by
    have him : m.im = N⁻¹ * ∑ i, m.im * (Complex.normSq (w i))⁻¹ := by
      conv_lhs => rw [hmeq]
      rw [hc, Complex.im_ofReal_mul, Complex.im_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      have := Complex.inv_im (w i)
      rw [hwim i] at this
      simp only [hwdef] at this ⊢
      rw [this]
      ring
    rw [← Finset.mul_sum] at him
    have h1 : N⁻¹ * ∑ i, (Complex.normSq (w i))⁻¹ = 1 := by
      have : m.im * (N⁻¹ * ∑ i, (Complex.normSq (w i))⁻¹) = m.im * 1 := by
        rw [mul_one]
        calc m.im * (N⁻¹ * ∑ i, (Complex.normSq (w i))⁻¹)
            = N⁻¹ * (m.im * ∑ i, (Complex.normSq (w i))⁻¹) := by ring
          _ = m.im := him.symm
      exact mul_left_cancel₀ hm.ne' this
    field_simp at h1
    simpa only [one_div] using h1
  -- (2) Cauchy-Schwarz: `|m| ≤ 1`
  have hCS : ∑ i, ‖w i‖⁻¹ ≤ N := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Zd d L)) (fun _ => (1 : ℝ)) (fun i => ‖w i‖⁻¹)
    have h2 : ∑ i, (‖w i‖⁻¹) ^ 2 = N := by
      rw [← hsum2]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inv_pow, Complex.sq_norm]
    simp only [one_mul, one_pow, Finset.sum_const, hcard, nsmul_eq_mul, mul_one, h2] at h
    have h3 : (∑ i, ‖w i‖⁻¹) ^ 2 ≤ N ^ 2 := by
      calc (∑ i, ‖w i‖⁻¹) ^ 2 ≤ ((L ^ d : ℕ) : ℝ) * N := h
        _ = N ^ 2 := by rw [hNdef]; ring
    exact le_of_sq_le_sq (by simpa using h3) hNpos.le |>.trans le_rfl
  have hmnorm : ‖m‖ ≤ 1 := by
    have : ‖m‖ ≤ N⁻¹ * ∑ i, ‖w i‖⁻¹ := by
      rw [hmeq, hc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNpos)]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hNpos).le
      calc ‖∑ i, (w i)⁻¹‖ ≤ ∑ i, ‖(w i)⁻¹‖ := norm_sum_le _ _
        _ = ∑ i, ‖w i‖⁻¹ := by simp
    calc ‖m‖ ≤ N⁻¹ * ∑ i, ‖w i‖⁻¹ := this
      _ ≤ N⁻¹ * N := mul_le_mul_of_nonneg_left hCS (inv_pos.mpr hNpos).le
      _ = 1 := inv_mul_cancel₀ hNpos.ne'
  have hmre : |m.re| ≤ 1 := (Complex.abs_re_le_norm m).trans hmnorm
  -- (3) every `|w_i| > 1`
  have hbig : ∀ i, 1 < Complex.normSq (w i) := by
    intro i
    have hev := FlowPins_eig_le d L i
    have h1 : |g * (PsiB_isHermitian d L).eigenvalues i| ≤ 2 * d * |g| := by
      rw [abs_mul]
      calc |g| * |(PsiB_isHermitian d L).eigenvalues i| ≤ |g| * (2 * d) :=
            mul_le_mul_of_nonneg_left hev (abs_nonneg g)
        _ = 2 * d * |g| := by ring
    have h2 : 1 < |(w i).re| := by
      rw [hwre i]
      have h3 : |E| ≤ |g * (PsiB_isHermitian d L).eigenvalues i - E - m.re| + |g * (PsiB_isHermitian d L).eigenvalues i| + |m.re| := by
        calc |E| = |-(g * (PsiB_isHermitian d L).eigenvalues i - E - m.re) + g * (PsiB_isHermitian d L).eigenvalues i - m.re| := by
              congr 1; ring
          _ ≤ |-(g * (PsiB_isHermitian d L).eigenvalues i - E - m.re) + g * (PsiB_isHermitian d L).eigenvalues i| + |m.re| := abs_sub _ _
          _ ≤ |-(g * (PsiB_isHermitian d L).eigenvalues i - E - m.re)| + |g * (PsiB_isHermitian d L).eigenvalues i| + |m.re| := by
              gcongr; exact abs_add_le _ _
          _ = _ := by rw [abs_neg]
      linarith
    have h4 : 1 < ‖w i‖ := lt_of_lt_of_le h2 (Complex.abs_re_le_norm _)
    rw [← Complex.sq_norm]
    nlinarith
  have hlt : ∑ i, (Complex.normSq (w i))⁻¹ < ∑ _i : Zd d L, (1 : ℝ) := by
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨0, Finset.mem_univ _, ?_⟩
    · exact (inv_lt_one_of_one_lt₀ (hbig i)).le
    · exact inv_lt_one_of_one_lt₀ (hbig 0)
  rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_one, hsum2] at hlt
  rw [hNdef] at hlt
  exact lt_irrefl _ hlt


/-- `BAm(g, E) = 0` beyond `2 + 2d|g|`: no solution of `(self_m)`, so the dite default (`BAm`). -/
theorem BAm_eq_zero_of_gt (d L : ℕ) [NeZero L] (g E : ℝ) (hE : 2 + 2 * d * |g| < |E|) :
    BAm d L g (E : ℂ) = 0 := by
  unfold BAm
  split_ifs with h
  · obtain ⟨m, hm⟩ := h
    exact absurd hm (baSelf_none_of_gt d L g E hE m)
  · rfl

/-- `ρ_N(E) = 0` beyond `2 + 2d|g|`. -/
theorem BArho_eq_zero_of_gt (d L : ℕ) [NeZero L] (g E : ℝ) (hE : 2 + 2 * d * |g| < |E|) :
    BArho d L g E = 0 := by
  unfold BArho
  rw [BAm_eq_zero_of_gt d L g E hE]
  simp

end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 7. `BAConArg'_premise_diag`: the added premise of `BAConArg'` on the diagonal `s = t`

On the diagonal `s ≡ t` the coupling is `g_s = g₀` (`BAlamS`), and `BAmF` at the flow parameters is
`m(z_n, g_n)/√t₀_n` (`BAzztE_data`, `BAm_real_eq_of_self`), whose imaginary part is at least `Im m(z_n, g_n) ≥ κ`
(`√t₀ < 1`, `BAt0_lt_one`). -/

/-- `m(E_n, g₀_n) = m(z_n, g_n)/√t₀_n` when `Im z_n > 0` (`(eq:zztE_BA)`, `7_8:1796-1801`). -/
private theorem FlowPins_BAmF_flow {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) :
    BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n =
      BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAflowT0 sz z n) : ℂ) := by
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  obtain ⟨-, -, hself, -, -⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz hm
  exact BAm_real_eq_of_self d (sz.L n) _ _ _ hself

/-- `Im m(E_n, g₀_n) = Im m(z_n, g_n)/√t₀_n > 0`. -/
private theorem FlowPins_BAmF_flow_im {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) :
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im =
      (BAm d (sz.L n) (sz.lam n) (z n)).im / Real.sqrt (BAflowT0 sz z n) := by
  rw [FlowPins_BAmF_flow sz z n hz, Complex.div_ofReal_im]

/-- `Im m(E_n, g₀_n) > 0` when `Im z_n > 0`. -/
private theorem FlowPins_BAmF_flow_im_pos {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) :
    0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := by
  rw [FlowPins_BAmF_flow_im sz z n hz]
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  exact div_pos hm.1 (Real.sqrt_pos.mpr (BAt0_pos hz hm.1))

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`, `N ≥ 1`). -/
private theorem FlowPins_zim_pos {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- **`BAConArg'_premise_diag`** (Amend 2, line 1): for any `z` with `BAFlow` and any `t > 0`, the added premise of
`BAConArg'` holds at `s = t`: `κ ≤ Im m(E_n, g_s)`, `g_s = g₀`. -/
theorem BAConArg'_premise_diag {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) :
    ∀ n, κ ≤ (BAmF sz (BAlamS sz z t t) (BAflowEs sz z) n).im := by
  intro n
  have hz := FlowPins_zim_pos sz h n
  have hs : BAlamS sz z t t = BAflowLam0 sz z := by
    funext k
    simp [BAlamS, div_self (ht k).ne']
  rw [hs, FlowPins_BAmF_flow_im sz z n hz]
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  have ht0 := BAt0_pos hz hm.1
  have ht1 := BAt0_lt_one hz hm.1
  have hspos : 0 < Real.sqrt (BAflowT0 sz z n) := Real.sqrt_pos.mpr ht0
  have hs1 : Real.sqrt (BAflowT0 sz z n) ≤ 1 := Real.sqrt_le_one.mpr ht1.le
  rw [le_div_iff₀ hspos]
  have := (h.2 n).1
  nlinarith [hm.1]

end RBM.BA


namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 8. Extra target (b): the unrepaired `BAConArg` is refuted under data beyond the support (Amend 2, line 2)

`BAConArg` (T2161 `:1160-1166`, after L1-L4) is **not** a pin of this ticket (Amend 1: `BAConArg'` replaces it); it is
defined here, `private`, only as the object of `not_BAConArg_of_data`, and no theorem takes it as a hypothesis (so it
is not registered).  Data with `2 + 2d|g_s| < |E_n|`: `m(E_n, g_s) = 0` (target (a)), so `η_s = 0` and the `k = 2` bound of
`BAConArgLoop` is `0`, while `𝓛^{(2)}_{t,(+,-),(a,a)} = Σ_{x,y ∈ [a]} W^{-2d} |G_{xy}|² > 0` surely (`Im z_t > 0`). -/

/-- The unrepaired pin `BAConArg` (T2161 `:1160-1166` after L1-L4), the object of `not_BAConArg_of_data`; **not** a
pin (superseded by `BAConArg'`, supervisor `2026-10-05-1806` §1.4), hence `private` (CLAUDE.md §3 (E)) and
unregistered. -/
private def BAConArg (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
        (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz z s t k) ∧ BAConArgVec sz z s t

/-- `G(-) = G(+)^*` for a Hermitian flow matrix. -/
private theorem FlowPins_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one]
  rfl

/-- `Im G_{ii} > 0` for the resolvent of a Hermitian matrix at `Im z > 0`. -/
private theorem FlowPins_Gii_im_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (i : ι) : 0 < (Gres H z true i i).im := by
  have h1 : Gres H z true = Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) := by simp [Gres]
  rw [h1, BAimInv_diag hH hz i]
  have h2 := BAcolSq_ge hH hz i
  have h3 : 0 < ∑ k, ‖Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) k i‖ ^ 2 := by
    by_contra hneg
    have hz0 : ∑ k, ‖Ring.inverse (H - z • (1 : Matrix ι ι ℂ)) k i‖ ^ 2 = 0 :=
      le_antisymm (not_lt.mp hneg) (Finset.sum_nonneg fun _ _ => by positivity)
    rw [hz0, mul_zero] at h2
    linarith
  exact mul_pos hz h3

private theorem FlowPins_trace_GDGD {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (c : ι → ℝ) :
    ((G * Matrix.diagonal (fun x => ((c x : ℝ) : ℂ))) * (Gᴴ * Matrix.diagonal (fun x => ((c x : ℝ) : ℂ)))).trace =
      ((∑ x, ∑ y, c x * c y * Complex.normSq (G x y) : ℝ) : ℂ) := by
  have h1 : ∀ (M : Matrix ι ι ℂ) i j, (M * Matrix.diagonal (fun x => ((c x : ℝ) : ℂ))) i j = M i j * (c j : ℂ) :=
    fun M i j => Matrix.mul_diagonal _ _ i j
  simp only [Matrix.trace, Matrix.diag]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [h1, h1, Matrix.conjTranspose_apply, ← Complex.mul_conj]
  simp only [Complex.star_def]
  ring

/-- The `k = 2` loop `𝓛^{(2)}_{(+,-),(a,a)}` of a Hermitian flow matrix at `Im z > 0` is nonzero: it is
`Σ_{x,y} E_x E_y |G_{xy}|²` with `E_x = W^{-d} 1(x ∈ [a])`, and the diagonal term `x = y = (a, 0)` is positive. -/
private theorem FlowPins_loop2_pos {d L W : ℕ} [NeZero L] [NeZero W]
    {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : 0 < z.im) (a : Zd d L) :
    0 < ‖loopM d L W H z ![true, false] ![a, a]‖ := by
  classical
  set G := Gres H z true with hG
  have hGf : Gres H z false = Gᴴ := FlowPins_Gres_false hH z
  set c : Vtx d L W → ℝ := fun x => if x.1 = a then (((W : ℝ) ^ d))⁻¹ else 0 with hc
  have hEc : Eblk d L W a = Matrix.diagonal (fun x => ((c x : ℝ) : ℂ)) := by
    unfold Eblk
    congr 1
    funext x
    simp only [hc]
    split_ifs <;> simp
  have hloop : loopM d L W H z ![true, false] ![a, a] =
      ((∑ x, ∑ y, c x * c y * Complex.normSq (G x y) : ℝ) : ℂ) := by
    have h2 : loopM d L W H z ![true, false] ![a, a] =
        (Gres H z true * Eblk d L W a * (Gres H z false * Eblk d L W a)).trace := by
      unfold loopM
      simp [List.ofFn_succ]
    rw [h2, hGf, hEc]
    exact FlowPins_trace_GDGD G c
  rw [hloop, Complex.norm_real, Real.norm_eq_abs]
  have hWd : 0 < W ^ d := Nat.pos_of_ne_zero (pow_ne_zero d (NeZero.ne W))
  set x0 : Vtx d L W := (a, ⟨0, hWd⟩) with hx0
  have hnn : ∀ x y, 0 ≤ c x * c y * Complex.normSq (G x y) := by
    intro x y
    have : ∀ w : Vtx d L W, 0 ≤ c w := fun w => by
      simp only [hc]; split_ifs <;> positivity
    exact mul_nonneg (mul_nonneg (this x) (this y)) (Complex.normSq_nonneg _)
  have hcx0 : 0 < c x0 := by
    simp only [hc, hx0, ite_true]
    have : (0 : ℝ) < W := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hG0 : 0 < Complex.normSq (G x0 x0) := by
    refine Complex.normSq_pos.mpr fun h => ?_
    have := FlowPins_Gii_im_pos hH hz x0
    rw [← hG, h] at this
    simp at this
  have hterm : 0 < c x0 * c x0 * Complex.normSq (G x0 x0) := by positivity
  have hsum : c x0 * c x0 * Complex.normSq (G x0 x0) ≤ ∑ x, ∑ y, c x * c y * Complex.normSq (G x y) := by
    calc c x0 * c x0 * Complex.normSq (G x0 x0)
        ≤ ∑ y, c x0 * c y * Complex.normSq (G x0 y) :=
          Finset.single_le_sum (f := fun y => c x0 * c y * Complex.normSq (G x0 y))
            (fun y _ => hnn x0 y) (Finset.mem_univ x0)
      _ ≤ ∑ x, ∑ y, c x * c y * Complex.normSq (G x y) :=
          Finset.single_le_sum (f := fun x => ∑ y, c x * c y * Complex.normSq (G x y))
            (fun x _ => Finset.sum_nonneg fun y _ => hnn x y) (Finset.mem_univ x0)
  rw [abs_of_nonneg (le_trans hterm.le hsum)]
  exact lt_of_lt_of_le hterm hsum

/-- The block Anderson flow matrix is Hermitian. -/
private theorem FlowPins_seqHflowBA_herm {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) : (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- **Extra target (b)** (Amend 2, line 2; supervisor `2026-10-05-1806` §1.4): for any data `(κ, ε, 𝔡, ε₁, 𝔠, sz, z, s, t)`
satisfying every hypothesis of `BAConArg` (`BAFlow`, the ranges, and `STLmaxgL` at the `g_s` carrier at `s`) together
with `2 + 2d |g_s| < |E_n|` for every `n` (`g_s = BAlamS`, `E_n = BAflowEs`; the absolute value because `lam n` is
unsigned), `BAConArg d` is false.  The unrepaired pin is therefore refuted wherever such data exist (the existence
of data is argued in supervisor `2026-10-05-1806` §1.4 and not claimed here); `BAConArg'` excludes them by its
added premise `κ ≤ Im m(E_n, g_s)`. -/
theorem not_BAConArg_of_data (d : ℕ) {κ ε 𝔡 ε₁ 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    (hε₁ : 0 < ε₁) (sz : Sizes d) (z : ℕ → ℂ) (hF : BAFlow sz κ ε 𝔠 𝔡 z) (s t : ℕ → ℝ)
    (hs : ∀ n, ε₁ ≤ s n) (hst : ∀ n, s n ≤ t n) (ht : ∀ n, t n < 1)
    (hL : STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s)
    (hE : ∀ n, 2 + 2 * d * |BAlamS sz z s t n| < |BAflowEs sz z n|) :
    ¬ BAConArg d := by
  intro hB
  have h2 := (hB κ ε 𝔡 ε₁ hκ hε h𝔡 hε₁ 𝔠 sz z hF s t hs hst ht hL).1 2 le_rfl
  have hsize : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) :=
    hF.1.2.2.1.eventually (eventually_ge_atTop 2)
  have hev := h2 1 one_pos 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hev.and hsize).exists
  -- `m(E_n, g_s) = 0` (target (a)), so `η_s = 0` and the bound of the `k = 2` loop is `0`
  have hm0 : BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n = 0 :=
    BAm_eq_zero_of_gt d (sz.L n) (BAlamS sz z s t n) (BAflowEs sz z n) (hE n)
  have heta : etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) = 0 := by
    rw [hm0]; simp [etaOf]
  -- the loop `𝓛^{(2)}_{t,(+,-),(0,0)}` is positive for every sample (`Im z_t > 0`)
  have hz := FlowPins_zim_pos sz hF n
  have hMpos := FlowPins_BAmF_flow_im_pos sz z n hz
  have hpos : ∀ ω : sz.SeqΩ,
      0 < ‖(baFMz sz z).L n (t n) ![true, false] ![0, 0] ω‖ := by
    intro ω
    change 0 < ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω)
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n)) ![true, false] ![0, 0]‖
    unfold loopFine
    refine FlowPins_loop2_pos ((FlowPins_seqHflowBA_herm sz _ n (t n) ω).submatrix _) ?_ 0
    rw [ztOf_im, etaOf]
    exact mul_pos (by linarith [ht n]) hMpos
  have : IsProbabilityMeasure ((sz.withLam 0).seqP) := inferInstance
  have hlt : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ)) < 1 := by
    rw [ENNReal.ofReal_lt_one, Real.rpow_neg_one]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  refine (not_lt.mpr hn1) ?_
  calc ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ)) < 1 := hlt
    _ = (sz.withLam 0).seqP Set.univ := measure_univ.symm
    _ ≤ _ := measure_mono ?_
  intro ω _
  refine ⟨(![true, false], ![0, 0]), ?_⟩
  simp only [heta, zero_div, zero_mul]
  simpa using hpos ω

end RBM.BA


namespace RBM.BA.FlowPinsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.BA.MFixedPointInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-! ## 9. Compiled nonempty instances at `d = 3`

(`P := RBM.BA.MFixedPointInst.P`, the flow point of `(L, g) = (4, 10)`.)  Every deterministic hypothesis is
discharged at concrete data (`N = 512` for target 1, `L = 4`, `g = 10`); the pins themselves (another ticket's
theorems) and the stochastic premises stay hypotheses. -/

/-! ### Target 1 at `(d, L, W) = (3, 4, 2)` (`N = 512`, 8 points per block) -/

/-- `Im (i + m(i, 10)) ≠ 0`, the hypothesis of target 1a-1c at the data. -/
theorem im_I_add_m : (Complex.I + BAm 3 4 10 Complex.I).im ≠ 0 := by
  have h := (BAm_self 3 4 10 Complex.I (by simp)).1
  rw [Complex.add_im, Complex.I_im]
  linarith

/-- 1a at `(3, 4, 2, 10, i)`. -/
theorem inst_kron : Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) =
    ((BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I) ⊗ₖ (1 : Matrix (Fin (2 ^ 3)) (Fin (2 ^ 3)) ℂ) :
      Matrix (Vtx 3 4 2) (Vtx 3 4 2) ℂ)).submatrix (splitEquiv 3 4 2) (splitEquiv 3 4 2) :=
  BAMres_fine_kron 3 4 2 10 Complex.I _ im_I_add_m

/-- 1b at the same data. -/
theorem inst_apply (x y : Idx 3 4 2) :
    Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) x y =
      if (split 3 4 2 x).2 = (split 3 4 2 y).2 then
        BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I) (split 3 4 2 x).1 (split 3 4 2 y).1 else 0 :=
  BAMres_fine_apply 3 4 2 10 Complex.I _ im_I_add_m x y

/-- 1b at two concrete pairs of points of `Z_8^3` (`W = 2`, `L = 4`): `x = 0`, `y = (1,0,0)` have different offsets,
so `M_{xy} = 0`; `x = 0`, `y = (2,0,0)` have the same offset in the blocks `0` and `e₁`, so `M_{xy} = M^{(B)}_{0 e₁}`. -/
theorem inst_apply_concrete :
    Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) 0 ![1, 0, 0] = 0 ∧
      Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I) 0 ![2, 0, 0] =
        BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I) 0 ![1, 0, 0] := by
  have h1 : (split 3 4 2 (0 : Idx 3 4 2)).2 ≠ (split 3 4 2 (![1, 0, 0] : Idx 3 4 2)).2 := by decide
  have h2 : (split 3 4 2 (0 : Idx 3 4 2)).2 = (split 3 4 2 (![2, 0, 0] : Idx 3 4 2)).2 := by decide
  have h3 : (split 3 4 2 (0 : Idx 3 4 2)).1 = 0 := by decide
  have h4 : (split 3 4 2 (![2, 0, 0] : Idx 3 4 2)).1 = ![1, 0, 0] := by decide
  refine ⟨?_, ?_⟩
  · rw [inst_apply]
    simp only [h1, ite_false]
  · rw [inst_apply]
    simp only [h2, h3, h4, ite_true]

/-- 1c at the same data. -/
theorem inst_trace :
    ((((2 * 4) ^ 3 : ℕ) : ℂ))⁻¹ * (Mres (((10 : ℝ) : ℂ) • PsiI 3 4 2) Complex.I (BAm 3 4 10 Complex.I)).trace =
      (((4 ^ 3 : ℕ) : ℂ))⁻¹ * (BAMB 3 4 10 Complex.I (BAm 3 4 10 Complex.I)).trace :=
  BAfine_trace 3 4 2 10 Complex.I _ im_I_add_m

/-- 1d at `z = i`: `m(i, 10)` solves the fine-lattice `(self_m)` with `N⁻¹ tr`, `N = 512`. -/
theorem inst_selfFine : BASelfFine 3 4 2 10 Complex.I (BAm 3 4 10 Complex.I) :=
  (BASelf_iff_fine 3 4 2 10 Complex.I _ (by simp)).mpr (BAm_self 3 4 10 Complex.I (by simp))

/-- 1d on the real axis, at the flow point `P` of `(L, g) = (4, 10)`. -/
theorem inst_selfFine_real : BASelfFine 3 4 2 P.g0 (P.E : ℂ) P.m0 :=
  (BASelf_iff_fine 3 4 2 P.g0 (P.E : ℂ) P.m0 (by simp)).mpr P.real.1

/-- 1a on the real axis, at the flow point `P` (`z = E` real, `m = m₀`, `Im (E + m₀) = Im m₀ > 0`). -/
theorem inst_kron_real : Mres (((P.g0 : ℝ) : ℂ) • PsiI 3 4 2) (P.E : ℂ) P.m0 =
    ((BAMB 3 4 P.g0 (P.E : ℂ) P.m0 ⊗ₖ (1 : Matrix (Fin (2 ^ 3)) (Fin (2 ^ 3)) ℂ) :
      Matrix (Vtx 3 4 2) (Vtx 3 4 2) ℂ)).submatrix (splitEquiv 3 4 2) (splitEquiv 3 4 2) :=
  BAMres_fine_kron 3 4 2 P.g0 (P.E : ℂ) P.m0 (by simpa using P.real.1.1.ne')


/-! ### Target 2: properties 5-8 of `Θ_BA` at the datum, `t = 1/2`, nondegenerate displacements

`a = (2,0,0)` and `r = (1,0,0)` in `Z_4^3` (`|a| = 2`, `|r| = 1 ≤ c|a|` for `c = 1/2`): the window of `(prop:BD1)`,
`(prop:BD2)` is not collapsed. -/

/-- `|(2,0,0)| = 2` in `Z_4^3`. -/
theorem zd_a : zdistD 3 4 (![2, 0, 0] : Zd 3 4) = 2 := by decide
/-- `|(1,0,0)| = 1` in `Z_4^3`. -/
theorem zd_r : zdistD 3 4 (![1, 0, 0] : Zd 3 4) = 1 := by decide

theorem inst_BAProp5 (h : BAProp5 3 10 P.m0.im) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
      C * Bparam 3 4 P.g0 (1 / 2) (zdistD 3 4 (![2, 0, 0] : Zd 3 4)) *
        Real.exp (-c * (zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) / ellT 4 P.g0 (1 / 2)) := by
  obtain ⟨C, hC, c, hc, H⟩ := h (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) true false _⟩

theorem inst_BAProp5s (h : BAProp5s 3 10 P.m0.im) : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]‖ ≤
      C * ((if (![1, 0, 0] : Zd 3 4) = 0 then (1 : ℝ) else 0) +
        P.g0 ^ 2 * Real.exp (-c * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ))) := by
  obtain ⟨C, hC, c, hc, H⟩ := h (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, c, hC, hc, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) true _⟩

theorem inst_BAProp6 (h : BAProp6 3 10 P.m0.im (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![2, 0, 0] + ![1, 0, 0]) -
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) *
        (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 1))⁻¹ := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) (by norm_num) P.real.1.1 (by norm_num) (by norm_num)
  refine ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) true false ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num

theorem inst_BAProp7 (h : BAProp7 3 10 P.m0.im (1 / 2)) : ∃ C : ℝ, 0 < C ∧
    ‖BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![2, 0, 0] + ![1, 0, 0]) +
        BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 (![2, 0, 0] - ![1, 0, 0]) -
        2 * BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (zdistD 3 4 (![1, 0, 0] : Zd 3 4) : ℝ) ^ 2 *
        (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ 3)⁻¹ := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) (by norm_num) P.real.1.1 (by norm_num) (by norm_num)
  refine ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) true false ![2, 0, 0] ![1, 0, 0] ?_⟩
  rw [zd_a, zd_r]
  norm_num

theorem inst_BAProp8 (h : BAProp8 3 10 P.m0.im) : ∃ C : ℝ, 0 < C ∧
    ‖BATheta0 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 ![2, 0, 0]‖ ≤
      C * (P.g0 ^ 2 + |1 - (1 / 2 : ℝ)|)⁻¹ * (((zdistD 3 4 (![2, 0, 0] : Zd 3 4) : ℝ) + 1) ^ (3 - 2))⁻¹ := by
  obtain ⟨C, hC, H⟩ := h (by norm_num) (by norm_num) P.real.1.1
  exact ⟨C, hC, H 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num)
    (by norm_num) true false _⟩




/-! ### Target 3, 4, 5 along `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`), `z_n = z_S(L_n, g_n)`

`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`.  The chain domain holds at every `n` (`Im m(z_n) ≥ 1/2`,
`11/30 ≤ Im z_n ≤ 7/10`), `t₀_n = Im m/Im w ≥ 2/3`.  Probe section 13.4 (`:2095-2199`) without the hypothesis
`BAmExists 3` (discharged by `baMExists_holds 3`). -/

private theorem FlowPins_wI_im : wI.im = 6 / 5 := rfl

private theorem FlowPins_mS_im_lower (L : ℕ) [NeZero L] (g : ℝ) :
    wI.im / (‖wI‖ ^ 2 + g ^ 2 * (L ^ 3 : ℕ)) ≤ (mS L g).im :=
  (BASelf_subord 3 L g one_lt_wI).2.1

private theorem FlowPins_mS_im_upper (L : ℕ) [NeZero L] (g : ℝ) : (mS L g).im ≤ wI.im⁻¹ :=
  (BASelf_subord 3 L g one_lt_wI).2.2.1

/-- `Im z_S + Im m_w = Im w`. -/
private theorem FlowPins_zS_add_mS_im (L : ℕ) [NeZero L] (g : ℝ) : (zS L g).im + (mS L g).im = wI.im := by
  simp [zS]

/-- `g_n² L_n³ ≤ 1/64` along `sz0` (`n = 0`: equality). -/
theorem sz0_lam_L (n : ℕ) : (sz0.lam n) ^ 2 * (((sz0.L n) ^ 3 : ℕ) : ℝ) ≤ 1 / 64 := by
  have hk : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hL : (((sz0.L n) ^ 3 : ℕ) : ℝ) = (4 * ((n : ℝ) + 1)) ^ 3 := by
    change (((4 * (n + 1)) ^ 3 : ℕ) : ℝ) = _
    push_cast; ring
  have hlam : sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := rfl
  rw [hL, hlam]
  have h1 : (((2 * ((n : ℝ) + 1)) ^ 6)⁻¹) ^ 2 * (4 * ((n : ℝ) + 1)) ^ 3 = (1 / 64) * (((n : ℝ) + 1)⁻¹) ^ 9 := by
    field_simp
    ring
  rw [h1]
  have h2 : (((n : ℝ) + 1)⁻¹) ^ 9 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hk)
  nlinarith

/-- `Im m_S ≥ 4/5` (so `≥ 1/2`) when `g² L³ ≤ 1/64` (`BASelf_subord`: `Im m_S ≥ (6/5)/(36/25 + g² L³)`; the probe
had `1/2`). -/
theorem mS_im_half (L : ℕ) [NeZero L] (g : ℝ) (h : g ^ 2 * (L ^ 3 : ℕ) ≤ 1 / 64) : 4 / 5 ≤ (mS L g).im := by
  refine le_trans ?_ (FlowPins_mS_im_lower L g)
  rw [FlowPins_wI_im, wI_norm, le_div_iff₀ (by positivity)]
  nlinarith

/-- `N_n ≥ 2^21` along `sz0`. -/
theorem size_ge (n : ℕ) : (2 : ℝ) ^ 21 ≤ ((sz0.size n : ℕ) : ℝ) := by
  have hW : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := W_ge_32 n
  have hL : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    change (4 : ℝ) ≤ ((4 * (n + 1) : ℕ) : ℝ)
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have h128 : (128 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) * ((sz0.L n : ℕ) : ℝ) := by nlinarith
  have : ((sz0.size n : ℕ) : ℝ) = (((sz0.W n : ℕ) : ℝ) * ((sz0.L n : ℕ) : ℝ)) ^ 3 := by
    change (((sz0.W n * sz0.L n) ^ 3 : ℕ) : ℝ) = _
    push_cast; ring
  rw [this]
  calc (2 : ℝ) ^ 21 = 128 ^ 3 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h128 3

/-- `N_n^{-1+1/10} ≤ 1/4` along `sz0`. -/
theorem size_rpow_le (n : ℕ) : (((sz0.size n : ℕ) : ℝ)) ^ (-1 + 1 / 10 : ℝ) ≤ 1 / 4 := by
  have h1 : ((2 : ℝ) ^ 21) ^ (-1 + 1 / 10 : ℝ) ≤ 1 / 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : ((21 : ℕ) : ℝ) * (-1 + 1 / 10) = -(189 / 10) := by norm_num
    rw [this]
    have h2 : (2 : ℝ) ^ (-(189 / 10 : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    refine h2.trans ?_
    rw [Real.rpow_neg (by norm_num)]
    norm_num
  exact le_trans (Real.rpow_le_rpow_of_nonpos (by positivity) (size_ge n) (by norm_num)) h1

/-- The spectral parameters `z_n = z_S(L_n, g_n)`. -/
def zSeq (n : ℕ) : ℂ := zS (sz0.L n) (sz0.lam n)

/-- `g_n > 0` along `sz0`. -/
theorem sz0_lam_pos (n : ℕ) : 0 < sz0.lam n := by
  change (0 : ℝ) < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

/-- `m(z_n, g_n)` is the subordination datum (uses `baMExists_holds 3`, not a hypothesis). -/
theorem BAm_zSeq (n : ℕ) : BAm 3 (sz0.L n) (sz0.lam n) (zSeq n) = mS (sz0.L n) (sz0.lam n) := by
  obtain ⟨m, hm, huniq⟩ := baMExists_holds 3 (sz0.L n) (sz0.three_le_L n) (sz0.lam n) (sz0_lam_pos n) (zSeq n)
    (zS_im_pos _ _)
  have h1 := huniq _ (BAm_spec ⟨_, hm⟩)
  have h2 := huniq _ (selfS (sz0.L n) (sz0.lam n))
  rw [h1, ← h2]

/-- `Im z_n ≤ 7/10`. -/
theorem zSeq_im_le (n : ℕ) : (zSeq n).im ≤ 7 / 10 := by
  have h := mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)
  have := FlowPins_zS_add_mS_im (sz0.L n) (sz0.lam n)
  rw [FlowPins_wI_im] at this
  unfold zSeq
  linarith

/-- `11/30 ≤ Im z_n`. -/
theorem zSeq_im_ge (n : ℕ) : 11 / 30 ≤ (zSeq n).im := by
  have h := FlowPins_mS_im_upper (sz0.L n) (sz0.lam n)
  have := FlowPins_zS_add_mS_im (sz0.L n) (sz0.lam n)
  rw [FlowPins_wI_im] at this h
  unfold zSeq
  have : ((6 / 5 : ℝ))⁻¹ = 5 / 6 := by norm_num
  linarith

/-- *Proved.* The setting `BAFlow` holds along `sz0` at `(1/2, 1/10, 1/6, 1/10)`. -/
theorem flow_sz0 : BAFlow sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq := by
  have hm : ∀ n, 4 / 5 ≤ (mS (sz0.L n) (sz0.lam n)).im := fun n => mS_im_half _ _ (sz0_lam_L n)
  refine ⟨sz0_admissible, fun n => ⟨?_, ?_, ?_⟩⟩
  · rw [BAm_zSeq n]
    linarith [hm n]
  · refine le_trans (size_rpow_le n) ?_
    have := zSeq_im_ge n
    linarith
  · have := zSeq_im_le n
    linarith

/-- `t₀_n = Im m/Im w`: `2/3 ≤ t₀_n < 1` (so `1/2 < t₀_n`, the times `s ≡ t ≡ 1/2` of `inst_BAConArg'` are in
`[0, t₀_n]`). -/
theorem t0_sz0 (n : ℕ) : 2 / 3 ≤ BAflowT0 sz0 zSeq n := by
  unfold BAflowT0 BAt0
  rw [BAm_zSeq n]
  have h1 := mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)
  have h2 := FlowPins_zS_add_mS_im (sz0.L n) (sz0.lam n)
  have h3 : (zSeq n).im + (mS (sz0.L n) (sz0.lam n)).im = 6 / 5 := by
    unfold zSeq; rw [h2, FlowPins_wI_im]
  have h4 : (mS (sz0.L n) (sz0.lam n)).im + (zSeq n).im = 6 / 5 := by linarith
  rw [h4, le_div_iff₀ (by norm_num)]
  linarith


/-! ### `BAConArg'` at `s ≡ t ≡ 1/2`, `κ = 1/2`, `ε₁ = 1/2` (Amend 2, line 1)

The added premise `κ ≤ Im m(E_n, g_s)` is discharged by `BAConArg'_premise_diag`; the pin `BAConArg' 3` and the
loop bound `(eq:loopbound_s)` at `s` (a stochastic premise, owed by BA-S1 and BA-K4) stay hypotheses. -/

theorem inst_BAConArg' (h : BAConArg' 3)
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    (∀ k : ℕ, 2 ≤ k → BAConArgLoop sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) k) ∧
      BAConArgVec sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  h (1 / 2) (1 / 10) (1 / 10) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 (fun _ => 1 / 2) (fun _ => 1 / 2) (fun n => le_rfl) (fun n => le_rfl) (fun n => by norm_num)
    (BAConArg'_premise_diag sz0 flow_sz0 (fun _ => 1 / 2) (fun n => by norm_num)) hL

/-- The times `s ≡ t ≡ 1/2` lie below the horizon `t₀_n ≥ 2/3`. -/
theorem half_lt_t0 (n : ℕ) : (1 / 2 : ℝ) < BAflowT0 sz0 zSeq n := by
  have := t0_sz0 n
  linarith

/-! ### `BAMfine` along the flow of `sz0` is the Kronecker matrix of target 1a -/

/-- `Im z_n > 0`. -/
theorem zSeq_im_pos (n : ℕ) : 0 < (zSeq n).im := zS_im_pos _ _

/-- `m(E_n, g₀_n) = m_S(L_n, g_n)/√t₀_n` along `sz0` (`BAm_zSeq`, `BAzztE_data`, `BAm_real_eq_of_self`). -/
theorem BAmF_sz0_eq (n : ℕ) :
    BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n =
      mS (sz0.L n) (sz0.lam n) / (Real.sqrt (BAflowT0 sz0 zSeq n) : ℂ) := by
  rw [FlowPins_BAmF_flow sz0 zSeq n (zSeq_im_pos n), BAm_zSeq n]

/-- `Im m(E_n, g₀_n) > 0` along `sz0`. -/
theorem BAmF_sz0_im_pos (n : ℕ) : 0 < (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n).im :=
  FlowPins_BAmF_flow_im_pos sz0 zSeq n (zSeq_im_pos n)

/-- For every `n`, `M(E_n, g₀_n)` on the fine lattice of size `(W_n L_n)^3` is `M^{(B)} ⊗ I_{W_n^3}` read through
`splitEquiv` (target 1a at the flow point of `sz0`). -/
theorem BAMfine_sz0_kron (n : ℕ) :
    BAMfine sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n =
      ((BAMB 3 (sz0.L n) (BAflowLam0 sz0 zSeq n) (BAflowEs sz0 zSeq n : ℂ)
          (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n) ⊗ₖ
        (1 : Matrix (Fin (sz0.W n ^ 3)) (Fin (sz0.W n ^ 3)) ℂ) : Matrix (Vtx 3 (sz0.L n) (sz0.W n))
          (Vtx 3 (sz0.L n) (sz0.W n)) ℂ)).submatrix (splitEquiv 3 (sz0.L n) (sz0.W n))
        (splitEquiv 3 (sz0.L n) (sz0.W n)) := by
  refine BAMres_fine_kron 3 (sz0.L n) (sz0.W n) _ _ _ ?_
  have := BAmF_sz0_im_pos n
  simpa using this.ne'


/-- `BAConArg'_premise_diag` at `sz0`, `s ≡ t ≡ 1/2`, `κ = 1/2`: `Im m(E_n, g_s) ≥ 1/2` for every `n`. -/
theorem inst_premise_diag :
    ∀ n, (1 / 2 : ℝ) ≤ (BAmF sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq) n).im :=
  BAConArg'_premise_diag sz0 flow_sz0 (fun _ => 1 / 2) (fun n => by norm_num)

/-! ### Extra target (a): no solution of `(self_m)` beyond `2 + 2d|g|` (`d = 3`, `L = 4`)

`g = 1`, `E = 9 > 2 + 6 = 8`; and `g = -1`, `E = -9` (negative couplings and energies are covered). -/

theorem inst_none_pos : ∀ m : ℂ, ¬ BASelf 3 4 1 ((9 : ℝ) : ℂ) m :=
  baSelf_none_of_gt 3 4 1 9 (by norm_num)

theorem inst_none_neg : ∀ m : ℂ, ¬ BASelf 3 4 (-1) ((-9 : ℝ) : ℂ) m :=
  baSelf_none_of_gt 3 4 (-1) (-9) (by norm_num [abs_of_neg])

theorem inst_BAm_zero : BAm 3 4 1 ((9 : ℝ) : ℂ) = 0 := BAm_eq_zero_of_gt 3 4 1 9 (by norm_num)

theorem inst_BArho_zero : BArho 3 4 1 9 = 0 := BArho_eq_zero_of_gt 3 4 1 9 (by norm_num)

/-- The flow point `P` of `(L, g) = (4, 10)` lies inside the threshold: the hypothesis of (a) fails there, as it must
(`(self_m)` has the solution `P.m0` at `(P.g0, P.E)`). -/
theorem inst_flowPt_inside : ¬ (2 + 2 * ((3 : ℕ) : ℝ) * |P.g0| < |P.E|) :=
  fun h => baSelf_none_of_gt 3 4 P.g0 P.E h P.m0 P.real.1

/-! ### The band bridges at `sz0` (`Iff.rfl` / `rfl`) and the carrier predicates at the block Anderson law -/

example : STMainInd 3 ↔ STMainIndG 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := STMainInd_iff 3

example : STStep1 3 ↔ ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
        ∀ (𝔠 : ℝ) (sz : Sizes 3) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
            (∀ n, t n ≤ lemT (z n)) →
            STKboundgL (bandFM sz (STflowE z)) (Sizes.seqP sz) →
            STLKgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s →
            STLocalMaxgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s → STConStInd sz 𝔠d s t →
              STStep1LoopgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t ∧
                STStep1WeakgL (bandFM sz (STflowE z)) (Sizes.seqP sz) s t := STStep1_iff 3

example : STLK sz0 (fun _ => 0) tInst ↔ STLKgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst :=
  bandFM_STLK sz0 (fun _ => 0) tInst
example : STLmax sz0 (fun _ => 0) tInst ↔ STLmaxgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst :=
  bandFM_STLmax sz0 (fun _ => 0) tInst
example : STDecay sz0 (fun _ => 0) tInst ↔ STDecaygL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst :=
  bandFM_STDecay sz0 (fun _ => 0) tInst
example : STDecayStrong sz0 (fun _ => 0) tInst ↔
    STDecayStronggL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst := bandFM_STDecayStrong sz0 (fun _ => 0) tInst
example : STLocalMax sz0 (fun _ => 0) tInst ↔
    STLocalMaxgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst := bandFM_STLocalMax sz0 (fun _ => 0) tInst
example : STLocalEntry sz0 (fun _ => 0) tInst ↔
    STLocalEntrygL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst := bandFM_STLocalEntry sz0 (fun _ => 0) tInst
example : STExp2 sz0 (fun _ => 0) tInst ↔ STExp2gL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst :=
  bandFM_STExp2 sz0 (fun _ => 0) tInst
example : STInitialGT2 sz0 (fun _ => 0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ↔
    STInitialGT2gL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst (1 / 20)
      (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  bandFM_STInitialGT2 sz0 (fun _ => 0) tInst (1 / 20) _
example : STKbound sz0 (fun _ => 0) ↔ STKboundgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) :=
  bandFM_STKbound sz0 (fun _ => 0)
example : STStep1Loop sz0 (fun _ => 0) sInst tInst ↔
    STStep1LoopgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STStep1Loop sz0 (fun _ => 0) sInst tInst
example : STStep1Weak sz0 (fun _ => 0) sInst tInst ↔
    STStep1WeakgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) sInst tInst :=
  bandFM_STStep1Weak sz0 (fun _ => 0) sInst tInst
example (D : ℝ) : STLWassmExp sz0 (fun _ => 0) tInst D (fun _ => 0) ↔
    STLWassmExpgL (bandFM sz0 (fun _ => 0)) (Sizes.seqP sz0) tInst D (fun _ => 0) :=
  bandFM_STLWassmExp sz0 (fun _ => 0) tInst D (fun _ => 0)
example (n : ℕ) (u : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L n)) (ω : sz0.SeqΩ) :
    STEEk sz0 n 0 u k σ a ω = STEEg (bandFM sz0 (fun _ => 0)) n u k σ a ω :=
  bandFM_STEEk sz0 (fun _ => 0) n u k σ a ω

/-- The block Anderson carrier of `sz0` at the law `seqP (sz0.withLam 0)` (the predicates of target 4 are
statements about it; their proofs are owed by the BA chain tickets). -/
example : Prop := STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tInst
example : Prop := STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tInst
example : Prop := STDecaygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tInst
example : Prop := STExp2gL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tInst
example : Prop := STLocalEntrygL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tInst
example : Prop := STKboundgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0))

/-! ### T2173a, compiled: `sz.seqP` is not the block Anderson law -/

/-- For `g ≠ 0` the variance between a point of block `0` and a point of the neighbouring block `e₁` differs from its value
at `g = 0` (`S^{(B)}(g)` has the weight `g²/(1+2dg²)` on neighbours, `S^{(B)}(0) = I` has none). -/
theorem svarF_ne_zero_profile {W : ℕ} [NeZero W] {g : ℝ} (hg : g ≠ 0) (i j : Idx 3 4 W)
    (hi : (split 3 4 W i).1 = 0) (hj : (split 3 4 W j).1 = ![1, 0, 0]) :
    svarF 3 4 W g i j ≠ svarF 3 4 W 0 i j := by
  have hz : zdistD 3 4 (-(![1, 0, 0] : Zd 3 4)) = 1 := by decide
  have hne : (-(![1, 0, 0] : Zd 3 4)) ≠ 0 := by decide
  have h1 : ∀ g' : ℝ, svarF 3 4 W g' i j = ((W : ℝ) ^ 3)⁻¹ * (g' ^ 2 * (1 + 2 * (3 : ℝ) * g' ^ 2)⁻¹) := by
    intro g'
    simp only [svarF, SBR, Matrix.of_apply, hi, hj, sbKernelR, zero_sub, hz, hne, ite_false, ite_true, zero_add]
    norm_num
  rw [h1, h1]
  intro h
  have hW : ((W : ℝ) ^ 3)⁻¹ ≠ 0 := by
    have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have h2 := mul_left_cancel₀ hW h
  have hpos : 0 < 1 + 2 * (3 : ℝ) * g ^ 2 := by positivity
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_mul] at h2
  have : g ^ 2 * (1 + 2 * (3 : ℝ) * g ^ 2)⁻¹ = 0 := by simpa using h2
  rcases mul_eq_zero.mp this with h3 | h3
  · exact hg (pow_eq_zero_iff (by norm_num) |>.mp h3)
  · exact absurd h3 (inv_ne_zero hpos.ne')

/-- **T2173a at `sz0`, `n = 0`** (`L = 4`, `W = 32`, `λ = 2^{-6}`): the coordinate laws of `sz0.seqP` (variance profile `S^{(B)}(λ)`) and of the block
Anderson law `(sz0.withLam 0).seqP` (`S^{(B)}(0) = I`) differ, so the law parameter of target 4 is not vacuous
(`sz0.lam 0 ≠ 0`; the proof is that of T2173 `seqGvar_ne_withLam_zero`, `:3851-3881`, at `sz0` and `n = 0`, where `sz0.L 0 = 4`). -/
theorem seqGvar_ne_withLam_zero :
    ∃ c : sz0.SeqCoord, sz0.seqGvar c ≠ (sz0.withLam 0).seqGvar c := by
  obtain ⟨i, j, hi, hj⟩ : ∃ i j : Idx 3 4 (sz0.W 0), (split 3 4 (sz0.W 0) i).1 = 0 ∧
      (split 3 4 (sz0.W 0) j).1 = ![1, 0, 0] := by
    refine ⟨(splitEquiv 3 4 (sz0.W 0)).symm (0, 0), (splitEquiv 3 4 (sz0.W 0)).symm (![1, 0, 0], 0), ?_, ?_⟩
    · exact congrArg Prod.fst ((splitEquiv 3 4 (sz0.W 0)).apply_symm_apply (0, 0))
    · exact congrArg Prod.fst ((splitEquiv 3 4 (sz0.W 0)).apply_symm_apply (![1, 0, 0], 0))
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    rw [hi] at hj
    exact absurd hj (by decide)
  refine ⟨⟨0, (i, j, true)⟩, fun heq => ?_⟩
  have hg : sz0.lam 0 ≠ 0 := (sz0_lam_pos 0).ne'
  have key := svarF_ne_zero_profile (W := sz0.W 0) hg i j hi hj
  apply key
  have hcoe : ∀ g' : ℝ, ((gvarF 3 4 (sz0.W 0) g' (i, j, true) : ℝ≥0) : ℝ) = svarF 3 4 (sz0.W 0) g' i j / 2 := by
    intro g'
    simp only [gvarF, hij, ite_false]
    rfl
  have e1 : ((sz0.seqGvar ⟨0, (i, j, true)⟩ : ℝ≥0) : ℝ) = svarF 3 4 (sz0.W 0) (sz0.lam 0) i j / 2 :=
    hcoe (sz0.lam 0)
  have e2 : (((sz0.withLam 0).seqGvar ⟨0, (i, j, true)⟩ : ℝ≥0) : ℝ) = svarF 3 4 (sz0.W 0) 0 i j / 2 :=
    hcoe 0
  have h1 := congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  have h3 : svarF 3 4 (sz0.W 0) (sz0.lam 0) i j / 2 = svarF 3 4 (sz0.W 0) 0 i j / 2 :=
    e1.symm.trans (h1.trans e2)
  linarith


end RBM.BA.FlowPinsInst

end
