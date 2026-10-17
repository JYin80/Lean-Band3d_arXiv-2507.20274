/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MFixedPoint
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Induction.Defs
import RBM3D.Induction.Step2Defs
import RBM3D.Loop.KLTree

/-!
# The block Anderson propagator statements, flow and loops over a law

Sections:

1. the fine-lattice `M` of (2.33) `def_G0` is `M^{(B)} ⊗ I_{W^d}`, and the two normalised traces
   agree (`BASelf` is the paper's (2.32) `self_m`);
2. the propagator statements `BAProp5 … BAProp5to8` (properties 5-8 of Lemma 2.19 `lem_propTH` at the block Anderson model),
   stated only;
3. the flow `H_t = g₀ Ψ + √t V` and its loops;
4. the flow carrier `baFM` over a law `μ`;
5. the flow data, `STMainIndG`, the vector part `BAConArgVec` of Lemma 8.5 (`lem_ConArg_BA`),
   with the law `Sizes.seqP (sz.withLam 0)`;
6. `(self_m)` has no solution beyond `2 + 2d|g|` (`baSelf_none_of_gt`);
7. `BAConArg'_premise_diag`: the premise `κ ≤ Im m(E_n, g_s)` of Lemma 8.5 on the diagonal `s = t`;
8. explicit data at `d = 3` in `RBM.BA.FlowPinsInst`.

Not in this file: the statements of the main induction, of Step 1 and of `GbEXP` at block Anderson.
Paper: Section 2 (the model, Lemma 2.19) and Section 8 (the block Anderson extension).
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

/-! ## 1. The fine-lattice `M` and `(self_m)` with `N⁻¹ tr` -/

section Fine

private theorem FlowPins_psiI_eq (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) :
    ((g : ℂ) • PsiI d L W) =
      (((g : ℂ) • PsiB d L) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)).submatrix
        (splitEquiv d L W) (splitEquiv d L W) := by
  unfold PsiI PsiV
  rw [smul_kronecker]
  rfl

/-- (2.33) `def_G0`: `M = M^{(B)} ⊗ I_{W^d}` on the fine lattice (through the
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

/-- The entrywise form, `M_{xy} = 1(x, y same offset) M^{(B)}_{[x][y]}`. -/
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

end Fine


/-! ## 2. The propagator statements of the block Anderson model: properties 5-8 of Lemma 2.19 (`lem_propTH`) for `Θ^{(σ₁,σ₂)}_t`

Lemma 2.19, proved in Subappendix A.1 (`sec:pf_propTH`); the block Anderson remark after (2.67): "constants may also depend on `λ⁻¹` when
`1 ≤ λ ≤ 𝔡⁻¹`".  The statements are those of `RBM3D/Propagator/Pins.lean` (`Prop5Decay`, `Prop5Short`,
`Prop6Diff1`, `Prop7Diff2`, `Prop8ZeroMode`: shape `PropThetaQ`), with the data `(g, E, m)` of the bulk
(`BAReal`) in place of `‖m‖ = 1`: constants `(d, Λ, κ)` (`(d, Λ, κ, c)` for 6, 7) fixed before `L, g, E, m`,
`g ∈ (0, Λ]`, `3 ≤ L`, `t ∈ [0, 1)`, both charge pairs, no loss (`≺` of 6-8 is no loss), `|r| ≤ c |a|`,
`0 < c < 1`.  The block Anderson kernel `M^{(+,-)}` is a general doubly stochastic kernel. -/

section PTPins

variable (d : ℕ)

/-- **Property 5**, (2.66) `prop:ThfadC`: `|Θ_t(0,a)| ≤ C B_{t,|a|} e^{-c|a|/ℓ_t}`. -/
def BAProp5 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * Bparam d L g t (zdistD d L a) * Real.exp (-c * (zdistD d L a : ℝ) / ellT L g t)

/-- **Property 5, short form**, (2.67) `prop:ThfadC_short`, `σ₁ = σ₂`: `|Θ_t(0,a)| ≤ C_κ(1_{a=0} + g² e^{-c_κ|a|})`;
the block Anderson proof is the Taylor expansion (A.3) `eq:expMLn` with (A.4) `eq:off_diagM`. -/
def BAProp5s (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ : Bool, ∀ a : Zd d L,
          ‖BATheta d L g E m t σ σ 0 a‖
            ≤ C * ((if a = 0 then (1 : ℝ) else 0) + g ^ 2 * Real.exp (-c * (zdistD d L a : ℝ)))

/-- **Property 6**, (2.68) `prop:BD1`: `|Θ_t(0,a+r) - Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r| (|a|+1)^{-(d-1)}`, `|r| ≤ c|a|`. -/
def BAProp6 (Λ κ c : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ → 0 < c → c < 1 →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a r : Zd d L,
          (zdistD d L r : ℝ) ≤ c * (zdistD d L a : ℝ) →
          ‖BATheta d L g E m t σ₁ σ₂ 0 (a + r) - BATheta d L g E m t σ₁ σ₂ 0 a‖
            ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (zdistD d L r : ℝ) * (((zdistD d L a : ℝ) + 1) ^ (d - 1))⁻¹

/-- **Property 7**, (2.69) `prop:BD2`: `|Θ_t(0,a+r) + Θ_t(0,a-r) - 2Θ_t(0,a)| ≤ C (g²+|1-t|)⁻¹ |r|² (|a|+1)^{-d}`. -/
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

/-- **Property 8**, (2.70) `prop:ThfadC0`: `|Θ̊_t(0,a)| ≤ C (g²+|1-t|)⁻¹ (|a|+1)^{-(d-2)}`. -/
def BAProp8 (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ σ₁ σ₂ : Bool, ∀ a : Zd d L,
          ‖BATheta0 d L g E m t σ₁ σ₂ 0 a‖ ≤ C * (g ^ 2 + |1 - t|)⁻¹ * (((zdistD d L a : ℝ) + 1) ^ (d - 2))⁻¹

/-- The bundle: properties 5-8 of Lemma 2.19 (`lem_propTH`) for the block Anderson model at one `(d, Λ, κ, c)`. -/
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

/-! ## 3. The flow of the block Anderson model along a size sequence, and the loops `𝓛`, `𝒦`

`H_t = g₀ Ψ + √t V` ((2.36) `MBM`; `Sizes.seqHflowBA`) with `V` the model of `sz.withLam 0`
(`S^{(B)}(0) = I`); `z_t(E, g₀) = E + (1-t) m(E, g₀)` ((2.37) `eq:zt`).  The flow parameters `(E, g₀)` are
arguments: Lemma 8.5 (`lem_ConArg_BA`) compares two couplings `g`, `g_s = g √(s/t)` at the same `E`. -/

section Flow

variable {d : ℕ} (sz : Sizes d)

/-- `m(E_n, g₀_n)`: the real-axis solution of `(self_m)` at the flow parameters. -/
def BAmF (lam0 E : ℕ → ℝ) (n : ℕ) : ℂ := BAm d (sz.L n) (lam0 n) (E n : ℂ)

/-- `M(E, g₀)` on the fine lattice, `M = M^{(B)} ⊗ I_{W^d}` ((2.33) `def_G0`); time independent. -/
def BAMfine (lam0 E : ℕ → ℝ) (n : ℕ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Mres ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (BAmF sz lam0 E n)

/-- `G_t(z_t)` entries of the block Anderson flow (Definition 2.8 `def_flow`, (2.39) `self_Gt`). -/
def BAGt (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) true

/-- **`𝓛^{(k)}_{t,σ,a}`** of the block Anderson flow ((2.44) `Eq:defGLoop`). -/
def BALloop (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω) (ztOf (BAmF sz lam0 E n) (E n) t) σ a

end Flow

section KLoops

variable (d L W : ℕ) [NeZero L]

/-- The block Anderson `M`-loop initial data `𝓜^{(k)}_{σ,a} = tr ∏_i (M(σ_i) E_{a_i}) = W^{-(k-1)d} ∏_i M(σ_i)_{a_{i-1} a_i}` (cyclic, `a_{-1} = a_{k-1}`: `σ_i` sits on the edge `(a_{i-1}, a_i)`; (2.53) `eq:KMloop`,
(A.35) `eq:Mloop_defgen`, `loopM`); `M = M^{(B)} ⊗ I_{W^d}`; the band case is `M(σ) = m(σ) I` (`MLoop`). -/
def BAMLoop (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) : ℂ :=
  (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) *
    ((I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map fun p => M p.1 p.2.1 p.2.2).prod

/-- **The `𝒦`-loops of the block Anderson model**: the solution of the convolution tree equations with the
kernel `S^{(B)}(0) = I` and the initial data `𝓜` (Definition 2.14 `Def_Ktza` for the block Anderson model, with (2.57) `WI_calK`; the kernel-generic
`IsKLoopS` of `RBM3D/Loop/KLTree.lean`); `0` if there is none. -/
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

end Flow2


end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 4. The block Anderson carrier

`PrecL`, `FlowFM`, `FlowFM.GM`, the generic predicates and the band carrier
`bandFM` are in `RBM3D/Chain/Carrier.lean`; `STJhatg` and `STLWassmExpgL` (they use `STprof` of `Induction/Step2Defs`) are in
`RBM3D/Chain/Step2Gen.lean`. -/

/-- **The block Anderson carrier at the flow parameters `(g₀, E)`.** -/
def baFM {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) : FlowFM sz where
  L := fun n t {_k} σ a ω => BALloop sz lam0 E n t σ a ω
  K := fun n t {_k} σ a => BAKloop sz lam0 E n t σ a
  G := fun n t ω x y => BAGt sz lam0 E n t ω x y
  M := fun n x y => BAMfine sz lam0 E n x y
  S := fun n => 1
  eta := fun n t => etaOf (BAmF sz lam0 E n) t
  m := fun n => BAmF sz lam0 E n

theorem bandFM_STKbound {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) :
    STKbound sz E ↔ STKboundgL (bandFM sz E) (Sizes.seqP sz) := Iff.rfl
end RBM.BA

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 5. Theorem 8.2 (`lem:main_ind_BA`) and the steps that change (flow data, Lemma 8.5 `lem_ConArg_BA`)

The flow data along a sequence of spectral parameters `z` ((8.1) `eq:t0E0_BA`): `t₀`, `E`, `g₀ = √t₀ g`.
The setting `BAFlow` replaces `STFlow`: admissible sizes (`(Main_DEL_COND)`, (2.10) `eq:WO`) and `z_n` in the chain
domain `BAdom` (`Im m(z_n, g_n) ≥ κ`, `N^{-1+ε} ≤ Im z_n ≤ 1`); there is no condition `|Re z| ≤ 2 - κ` and no `e_λ`. -/

section FlowData

variable {d : ℕ} (sz : Sizes d)

/-- `t₀_n` of (8.1) `eq:t0E0_BA`. -/
def BAflowT0 (z : ℕ → ℂ) (n : ℕ) : ℝ := BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))

/-- `E_n` of (8.1) `eq:t0E0_BA`. -/
def BAflowEs (z : ℕ → ℂ) (n : ℕ) : ℝ := BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n))

/-- `g₀_n = √t₀_n g_n` of (8.1) `eq:t0E0_BA`. -/
def BAflowLam0 (z : ℕ → ℂ) (n : ℕ) : ℝ := Real.sqrt (BAflowT0 sz z n) * sz.lam n

/-- The setting of `MR:decol_BA`, Theorem 8.2 (`lem:main_ind_BA`) and Lemma 8.1 (`zztE_BA`) along a sequence (replaces `STFlow`). -/
def BAFlow (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)

/-- The block Anderson carrier at the flow parameters of `z`. -/
def baFMz (z : ℕ → ℂ) : FlowFM sz := baFM sz (BAflowLam0 sz z) (BAflowEs sz z)

end FlowData


/-! The law of every block Anderson statement of this section is `Sizes.seqP (sz.withLam 0)`. -/

section MainInd

/-- **Theorem 2.24 (`lem:main_ind`) and Theorem 8.2 (`lem:main_ind_BA`), one statement for every model**: the statement `STMainInd` with the
law of the sample space `law`, the setting `Flow`, the carrier `mk` and the flow horizon `T0` as parameters (every predicate inside is
stated at `law sz`).  Constants first (`κ, ε, 𝔡`, then `𝔠_d ∈ (0, 10^{-2}]`, then `𝔠`,
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

/-- *Proved (`Iff.rfl`).* The band statement `STMainInd` is `STMainIndG` at the band law `seqP sz`, the band
setting, carrier and horizon. -/
theorem STMainInd_iff (d : ℕ) :
    STMainInd d ↔ STMainIndG d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := Iff.rfl

/-- **The block Anderson reading of Step 2** (`STStep2G` at the law `seqP (sz.withLam 0)`, the setting `BAFlow`, the carrier
`baFMz` and the horizon `BAflowT0`). -/
def BAStep2 (d : ℕ) : Prop :=
  STStep2G d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0

end MainInd

section ConArg

/-- `Im G_{vv}` for unit vectors `v` of `ℂ^N` ((8.12) `eq:ImGs`): `v^* G v`. -/
def BAvecEntry {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star v ⬝ᵥ (A *ᵥ w)

/-- The scale-`s` coupling of Lemma 8.5 (`lem_ConArg_BA`): `g_s = g₀ √(s/t)`. -/
def BAlamS {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : ℕ → ℝ :=
  fun n => Real.sqrt (s n / t n) * BAflowLam0 sz z n

/-- Lemma 8.5 (`lem_ConArg_BA`) (2), (8.12) `eq:ImGs`, (8.13) `eq:ImGt`: the vector bounds, for deterministic unit vectors,
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

end ConArg

end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss

/-! ## 6. No solution of `(self_m)` beyond the support

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


/-- **No solution beyond the support**: for real `g, E` with `|E| > 2 + 2d|g|`, `(self_m)` at
`(g, E)` has no solution.  Proof outline: with `w_i = gλ_i - E - m` (`λ_i` the eigenvalues of `Ψ^{(B)}`, `|λ_i| ≤ 2d`,
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

end RBM.BA

namespace RBM.BA

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 7. `BAConArg'_premise_diag`: the premise `κ ≤ Im m(E_n, g_s)` of Lemma 8.5 on the diagonal `s = t`

On the diagonal `s ≡ t` the coupling is `g_s = g₀` (`BAlamS`), and `BAmF` at the flow parameters is
`m(z_n, g_n)/√t₀_n` (`BAzztE_data`, `BAm_real_eq_of_self`), whose imaginary part is at least `Im m(z_n, g_n) ≥ κ`
(`√t₀ < 1`, `BAt0_lt_one`). -/

/-- `m(E_n, g₀_n) = m(z_n, g_n)/√t₀_n` when `Im z_n > 0` ((8.2) `eq:zztE_BA`). -/
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

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`, `N ≥ 1`). -/
private theorem FlowPins_zim_pos {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- **`BAConArg'_premise_diag`**: for any `z` with `BAFlow` and any `t > 0`, the premise of
Lemma 8.5 holds at `s = t`: `κ ≤ Im m(E_n, g_s)`, `g_s = g₀`. -/
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


namespace RBM.BA.FlowPinsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.BA.MFixedPointInst RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst

/-! ## 8. Explicit data at `d = 3`

(`P := RBM.BA.MFixedPointInst.P`, the flow point of `(L, g) = (4, 10)`.)  The data below are explicit:
the flow data along the sequence `sz0` and the diagonal premise at `sz0`. -/

/-! ### The flow datum along `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`), `z_n = z_S(L_n, g_n)`

`(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`.  The chain domain holds at every `n` (`Im m(z_n) ≥ 1/2`,
`11/30 ≤ Im z_n ≤ 7/10`), `t₀_n = Im m/Im w ≥ 2/3`, with `BAmExists 3` discharged by `baMExists_holds 3`. -/

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

/-- `Im m_S ≥ 4/5` (so `≥ 1/2`) when `g² L³ ≤ 1/64` (`BASelf_subord`: `Im m_S ≥ (6/5)/(36/25 + g² L³)`). -/
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

/-! ### The diagonal premise at `s ≡ t ≡ 1/2`, `κ = 1/2`

The premise `κ ≤ Im m(E_n, g_s)` of Lemma 8.5 is discharged by `BAConArg'_premise_diag`. -/


/-- `BAConArg'_premise_diag` at `sz0`, `s ≡ t ≡ 1/2`, `κ = 1/2`: `Im m(E_n, g_s) ≥ 1/2` for every `n`. -/
theorem inst_premise_diag :
    ∀ n, (1 / 2 : ℝ) ≤ (BAmF sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq) n).im :=
  BAConArg'_premise_diag sz0 flow_sz0 (fun _ => 1 / 2) (fun n => by norm_num)

end RBM.BA.FlowPinsInst

end
