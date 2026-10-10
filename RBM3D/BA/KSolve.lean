/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KBase
import RBM3D.BA.FlowPins
import RBM3D.BA.Ward
import RBM3D.Loop.Unique
import RBM3D.Loop.KLUnique

/-!
# Stage K, row K03: the levels `n ≤ 3` of the block Anderson `K`-loop equation

Ticket T2368 (design BA-DK, `docs/reports/T2360-design.md` §2 (`BAKsolve`), §4 rows K01 (BA part),
K03).

1. The pins `IsKLoopSLe` (the system of `IsKLoopS` on the loops of length `≤ N`), `BAKsolve`
   (existence of the BA `𝒦` on `[0,1)` with `(Kn2sol)`; K05b's target, a closing condition of
   stage K) and `BAKsolveLe3`.
2. `baKsolveLe3_holds : ∀ d, BAKsolveLe3 d`: `(Kn2sol)` and `(Kn3sol)` (`1_2:1175-1177`, D634)
   with the K00 convention (`BAMLoop` pairs `σ_i` with `(a_{i-1}, a_i)`; a leaf at `a_v` carries
   `Θ^{(σ_v, σ_{v+1})}`) solve the system on the levels `n ≤ 3`.  The `2`-loop is
   `W^{-d} Θ M^{(σσ')}`, the `3`-loop is the triple sum with the `M`-loop `BAMLoop` as weight; the
   cuts of a `3`-loop are `2`- and `3`-loops, and `∂_tΘ = ΘMΘ` on each leaf.
3. The BA instances of the generic K01 pins (`S = 1`, initial data `BAMLoop`): `baK_unique`,
   `baK_rotate`, `baK_translate`, with `BAMLoop_rot`, `BAMLoop_translate`, `BAMsigma_shift`; and
   `BAKsol_isKLoopS`, `BAKsol_rotate`, `BAKsol_translate` under the pin `BAKsolve d`.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix Filter Topology Finset

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss

/-! ## 1. The pins (verbatim from `docs/tickets/checks/T2368-check.lean`, Part 1) -/

/-- **`IsKLoopSLe`**: the system of `IsKLoopS` (`Loop/KLTree.lean:828`) on the loops of length `≤ N`.  Closed: the cuts of a
loop of length `n` have lengths in `[1, n]`, and length `1` is the third clause. -/
def IsKLoopSLe (d L W : ℕ) [NeZero L] (N : ℕ) (S : Matrix (Zd d L) (Zd d L) ℂ) (m : Bool → ℂ)
    (M : LoopIdx (Zd d L) → ℂ) (T : Set ℝ) (K : ℝ → LoopIdx (Zd d L) → ℂ) : Prop :=
  (∀ t ∈ T, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ N →
      HasDerivAt (fun s => K s I) (treeEqRhsS d L W S (K t) I) t) ∧
  (∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → I.length ≤ N → K 0 I = M I) ∧
  (∀ t ∈ T, ∀ (s : Bool) (a : Zd d L), K t ⟨[s], [a]⟩ = m s)

/-- **`BAKsolve`** (verbatim: probe `t/T2360:RBM3D/Probe/T2360Pins.lean:281`): existence of the BA `𝒦` on `[0,1)` with
`(Kn2sol)`; the target of K05b, a closing condition of stage K (supervisor 2051 Q5). -/
def BAKsolve (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m →
      ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
        IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
          (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂

/-- **`BAKsolveLe3`** (K03's target): the levels `n ≤ 3` of the BA system are solved by `(Kn2sol)` and `(Kn3sol)`
(`1_2:1175-1177`, D634), with the K00 convention (`BAMLoop` pairs `σ_i` with `(a_{i-1}, a_i)`; a leaf at `a_v` carries
`Θ^{(σ_v, σ_{v+1})}`). -/
def BAKsolveLe3 (d : ℕ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m →
      ∃ K : ℝ → LoopIdx (Zd d L) → ℂ,
        IsKLoopSLe d L W 3 (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
          (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K ∧
        (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
          K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
            (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd d L),
          K t ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ =
            ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, ∑ b₃ : Zd d L,
              BATheta d L g E m t σ₁ σ₂ a₁ b₁ * BATheta d L g E m t σ₂ σ₃ a₂ b₂ * BATheta d L g E m t σ₃ σ₁ a₃ b₃ *
                BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨[σ₁, σ₂, σ₃], [b₁, b₂, b₃]⟩

/-! ## 2. Calculus facts for `Θ^{(σσ')}` and `M^{(σσ')}` (only what `BA/KBase` does not export) -/

section Calc

variable {d L : ℕ} [NeZero L]

/-- `M(σ)` is symmetric (`M^{(B)}` is complex symmetric, `M(-) = M^*`). -/
private theorem BAKSolve_Msigma_symm (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b = BAMsigma d L (BAMB d L g (E : ℂ) m) σ b a := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply,
      BAMB_symm d L g (E : ℂ) m a b]
  · exact BAMB_symm d L g (E : ℂ) m a b

/-- `M^{(σ₁σ₂)}` is a symmetric matrix. -/
private theorem BAKSolve_Mss_symm (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ a b = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ b a := by
  simp only [BAMss, Matrix.of_apply]
  rw [BAKSolve_Msigma_symm g E m σ₁ b a, BAKSolve_Msigma_symm g E m σ₂ a b, mul_comm]

/-- `M^{(σ₁σ₂)} = M^{(σ₂σ₁)}`. -/
private theorem BAKSolve_Mss_swap (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) :
    BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ = BAMss d L (BAMB d L g (E : ℂ) m) σ₂ σ₁ := by
  ext a b
  simp only [BAMss, Matrix.of_apply]
  rw [BAKSolve_Msigma_symm g E m σ₁ b a, BAKSolve_Msigma_symm g E m σ₂ b a, mul_comm]

/-- `Θ_0 = 1`. -/
private theorem BAKSolve_Theta_zero (g E : ℝ) (m : ℂ) (σ₁ σ₂ : Bool) :
    BATheta d L g E m 0 σ₁ σ₂ = 1 := by
  simp [BATheta, PropThetaQ]

/-- `Θ` and `M^{(σσ')}` commute (`Θ` is a function of `M^{(σσ')}`). -/
private theorem BAKSolve_comm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ =
      BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂ := by
  obtain ⟨h1, h2⟩ := BATheta_resolvent d L g κ E m hr t ht0 ht1 σ₁ σ₂
  by_cases ht : (t : ℂ) = 0
  · have : BATheta d L g E m t σ₁ σ₂ = 1 := by rw [h1, ht]; simp
    rw [this, one_mul, mul_one]
  · have h := h1.symm.trans h2
    have h' := add_left_cancel h
    exact (smul_right_injective _ ht h').symm

/-- The matrix `Θ M^{(σσ')}` is symmetric. -/
private theorem BAKSolve_ThQ_symm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a b =
      (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) b a := by
  have hQ : (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)ᵀ = BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ := by
    ext x y
    exact (BAKSolve_Mss_symm g E m σ₁ σ₂ y x)
  have h := congrFun (congrFun (show (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)ᵀ =
      BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ by
    rw [Matrix.transpose_mul, hQ, BATheta_isSymm d L g κ E m hr t ht0 ht1,
      ← BAKSolve_comm g κ E m hr ht0 ht1]) a) b
  simpa [Matrix.transpose_apply] using h.symm

/-- `W^d (W^d)⁻¹ (W^d)⁻¹^(k+1) = (W^d)⁻¹^(k+1)`, also at `W^d = 0` (`0⁻¹ = 0`). -/
private theorem BAKSolve_wc_pow (w : ℂ) (k : ℕ) : w * w⁻¹ * (w⁻¹) ^ (k + 1) = (w⁻¹) ^ (k + 1) := by
  by_cases hw : w = 0
  · simp [hw]
  · rw [mul_inv_cancel₀ hw, one_mul]

/-- `W^d (W^d)⁻¹ 𝓜 = 𝓜` for an `M`-loop of length `≥ 2`. -/
private theorem BAKSolve_wc_BAMLoop (d L W : ℕ) [NeZero L] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (I : LoopIdx (Zd d L)) (h : 2 ≤ I.length) :
    ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * BAMLoop d L W M I = BAMLoop d L W M I := by
  obtain ⟨k, hk⟩ : ∃ k, I.length - 1 = k + 1 := ⟨I.length - 2, by omega⟩
  unfold BAMLoop
  rw [hk, ← mul_assoc, BAKSolve_wc_pow]

end Calc

/-! ## 3. The right-hand side of the tree equation at `S = 1`, `n = 2, 3` -/

section Rhs

variable {d L : ℕ} [NeZero L] (W : ℕ)

private theorem BAKSolve_sum_one (f g : Zd d L → ℂ) :
    ∑ a : Zd d L, ∑ b : Zd d L, f a * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * g b = ∑ a : Zd d L, f a * g a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

/-- `treeEqRhsS` at `S = 1`, `n = 2`: the only cut is `(1,2)`. -/
private theorem BAKSolve_rhs_two (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    treeEqRhsS d L W 1 K ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      ((W : ℂ) ^ d) * ∑ a : Zd d L, K ⟨[σ₁, σ₂], [a, a₂]⟩ * K ⟨[σ₁, σ₂], [a₁, a]⟩ := by
  have hlen : (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).length = 2 := rfl
  have h12 : Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hIoc1 : Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have hIoc2 : Ioc 2 2 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhsS, hlen, h12, Finset.sum_insert (by decide), Finset.sum_singleton, hIoc1, hIoc2,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  have hL : ∀ a : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueL 1 2 a = ⟨[σ₁, σ₂], [a, a₂]⟩ := by
    intro a; simp [LoopIdx.cutGlueL]
  have hR : ∀ b : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueR 1 2 b = ⟨[σ₁, σ₂], [a₁, b]⟩ := by
    intro b; simp [LoopIdx.cutGlueR]
  simp only [hL, hR]
  rw [BAKSolve_sum_one (fun a => K ⟨[σ₁, σ₂], [a, a₂]⟩) (fun b => K ⟨[σ₁, σ₂], [a₁, b]⟩)]

/-- `treeEqRhsS` at `S = 1`, `n = 3`: the cuts `(1,2)`, `(1,3)`, `(2,3)`. -/
private theorem BAKSolve_rhs_three (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd d L) :
    treeEqRhsS d L W 1 K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ =
      ((W : ℂ) ^ d) *
        ((∑ a : Zd d L, K ⟨[σ₁, σ₂, σ₃], [a, a₂, a₃]⟩ * K ⟨[σ₁, σ₂], [a₁, a]⟩) +
          (∑ a : Zd d L, K ⟨[σ₁, σ₃], [a, a₃]⟩ * K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a]⟩) +
          ∑ a : Zd d L, K ⟨[σ₁, σ₂, σ₃], [a₁, a, a₃]⟩ * K ⟨[σ₂, σ₃], [a₂, a]⟩) := by
  have hlen : (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).length = 3 := rfl
  have h13 : Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  have hIoc1 : Ioc 1 3 = ({2, 3} : Finset ℕ) := by decide
  have hIoc2 : Ioc 2 3 = ({3} : Finset ℕ) := by decide
  have hIoc3 : Ioc 3 3 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhsS, hlen, h13]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    hIoc1, hIoc2, hIoc3, Finset.sum_insert (by decide), Finset.sum_singleton,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  have hL12 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueL 1 2 a =
      ⟨[σ₁, σ₂, σ₃], [a, a₂, a₃]⟩ := fun a => by simp [LoopIdx.cutGlueL]
  have hR12 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueR 1 2 a =
      ⟨[σ₁, σ₂], [a₁, a]⟩ := fun a => by simp [LoopIdx.cutGlueR]
  have hL13 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueL 1 3 a =
      ⟨[σ₁, σ₃], [a, a₃]⟩ := fun a => by simp [LoopIdx.cutGlueL]
  have hR13 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueR 1 3 a =
      ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a]⟩ := fun a => by simp [LoopIdx.cutGlueR]
  have hL23 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueL 2 3 a =
      ⟨[σ₁, σ₂, σ₃], [a₁, a, a₃]⟩ := fun a => by simp [LoopIdx.cutGlueL]
  have hR23 : ∀ a : Zd d L, (⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ : LoopIdx (Zd d L)).cutGlueR 2 3 a =
      ⟨[σ₂, σ₃], [a₂, a]⟩ := fun a => by simp [LoopIdx.cutGlueR]
  simp only [hL12, hR12, hL13, hR13, hL23, hR23]
  rw [BAKSolve_sum_one (fun a => K ⟨[σ₁, σ₂, σ₃], [a, a₂, a₃]⟩) (fun b => K ⟨[σ₁, σ₂], [a₁, b]⟩),
    BAKSolve_sum_one (fun a => K ⟨[σ₁, σ₃], [a, a₃]⟩) (fun b => K ⟨[σ₁, σ₂, σ₃], [a₁, a₂, b]⟩),
    BAKSolve_sum_one (fun a => K ⟨[σ₁, σ₂, σ₃], [a₁, a, a₃]⟩) (fun b => K ⟨[σ₂, σ₃], [a₂, b]⟩)]

end Rhs

/-! ## 4. The triple sum `τ` and its calculus -/

section Tau

variable {d L : ℕ} [NeZero L]

/-- The triple sum of `(Kn3sol)`: `τ_ℬ(A,B,C)(a₁,a₂,a₃) = Σ_b A(a₁,b₁) B(a₂,b₂) C(a₃,b₃) ℬ(b₁,b₂,b₃)`. -/
private def BAKSolve_tau (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (A B C : Matrix (Zd d L) (Zd d L) ℂ)
    (a₁ a₂ a₃ : Zd d L) : ℂ :=
  ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, ∑ b₃ : Zd d L, A a₁ b₁ * B a₂ b₂ * C a₃ b₃ * ℬ b₁ b₂ b₃

/-- Product rule for the three legs. -/
private theorem BAKSolve_tau_hasDerivAt (ℬ : Zd d L → Zd d L → Zd d L → ℂ) {A B C : ℝ → Matrix (Zd d L) (Zd d L) ℂ}
    {A' B' C' : Matrix (Zd d L) (Zd d L) ℂ} {t : ℝ}
    (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (hB : ∀ a b, HasDerivAt (fun s => B s a b) (B' a b) t)
    (hC : ∀ a b, HasDerivAt (fun s => C s a b) (C' a b) t) (a₁ a₂ a₃ : Zd d L) :
    HasDerivAt (fun s => BAKSolve_tau ℬ (A s) (B s) (C s) a₁ a₂ a₃)
      (BAKSolve_tau ℬ A' (B t) (C t) a₁ a₂ a₃ + BAKSolve_tau ℬ (A t) B' (C t) a₁ a₂ a₃ +
        BAKSolve_tau ℬ (A t) (B t) C' a₁ a₂ a₃) t := by
  unfold BAKSolve_tau
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Zd d L))) (x := t)
    (A := fun b₁ s => ∑ b₂ : Zd d L, ∑ b₃ : Zd d L, A s a₁ b₁ * B s a₂ b₂ * C s a₃ b₃ * ℬ b₁ b₂ b₃)
    (A' := fun b₁ => ∑ b₂ : Zd d L, ∑ b₃ : Zd d L,
      ((A' a₁ b₁ * B t a₂ b₂ + A t a₁ b₁ * B' a₂ b₂) * C t a₃ b₃ + A t a₁ b₁ * B t a₂ b₂ * C' a₃ b₃) * ℬ b₁ b₂ b₃)
    fun b₁ _ => HasDerivAt.fun_sum fun b₂ _ => HasDerivAt.fun_sum fun b₃ _ =>
      ((((hA a₁ b₁).mul (hB a₂ b₂)).mul (hC a₃ b₃)).mul_const (ℬ b₁ b₂ b₃))
  convert h using 1
  simp only [← Finset.sum_add_distrib, add_mul]

/-- Left multiplication on the first leg. -/
private theorem BAKSolve_tau_leg1 (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (X A B C : Matrix (Zd d L) (Zd d L) ℂ)
    (a₁ a₂ a₃ : Zd d L) :
    ∑ a : Zd d L, X a₁ a * BAKSolve_tau ℬ A B C a a₂ a₃ = BAKSolve_tau ℬ (X * A) B C a₁ a₂ a₃ := by
  unfold BAKSolve_tau
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₃ _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

private theorem BAKSolve_tau_leg2 (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (X A B C : Matrix (Zd d L) (Zd d L) ℂ)
    (a₁ a₂ a₃ : Zd d L) :
    ∑ a : Zd d L, X a₂ a * BAKSolve_tau ℬ A B C a₁ a a₃ = BAKSolve_tau ℬ A (X * B) C a₁ a₂ a₃ := by
  unfold BAKSolve_tau
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₃ _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

private theorem BAKSolve_tau_leg3 (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (X A B C : Matrix (Zd d L) (Zd d L) ℂ)
    (a₁ a₂ a₃ : Zd d L) :
    ∑ a : Zd d L, X a₃ a * BAKSolve_tau ℬ A B C a₁ a₂ a = BAKSolve_tau ℬ A B (X * C) a₁ a₂ a₃ := by
  unfold BAKSolve_tau
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b₃ _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- `τ` at the identity legs is the weight. -/
private theorem BAKSolve_tau_one (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (a₁ a₂ a₃ : Zd d L) :
    BAKSolve_tau ℬ 1 1 1 a₁ a₂ a₃ = ℬ a₁ a₂ a₃ := by
  unfold BAKSolve_tau
  simp [Matrix.one_apply]

/-- A scalar factor `c` with `c = c·c'` absorbs into the weight. -/
private theorem BAKSolve_tau_smul (ℬ : Zd d L → Zd d L → Zd d L → ℂ) (c : ℂ) (A B C : Matrix (Zd d L) (Zd d L) ℂ)
    (a₁ a₂ a₃ : Zd d L) :
    c * BAKSolve_tau ℬ A B C a₁ a₂ a₃ = BAKSolve_tau (fun b₁ b₂ b₃ => c * ℬ b₁ b₂ b₃) A B C a₁ a₂ a₃ := by
  unfold BAKSolve_tau
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₃ _ => ?_
  ring

/-- `W^d (W^d)⁻¹` is absorbed by the `M`-loop weight (length `3`). -/
private theorem BAKSolve_tau_wc (W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (σ : List Bool)
    (A B C : Matrix (Zd d L) (Zd d L) ℂ) (x y z : Zd d L) :
    ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) *
        BAKSolve_tau (fun b₁ b₂ b₃ => BAMLoop d L W M ⟨σ, [b₁, b₂, b₃]⟩) A B C x y z =
      BAKSolve_tau (fun b₁ b₂ b₃ => BAMLoop d L W M ⟨σ, [b₁, b₂, b₃]⟩) A B C x y z := by
  rw [BAKSolve_tau_smul]
  unfold BAKSolve_tau
  refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₃ _ => ?_
  have h := BAKSolve_wc_BAMLoop d L W M ⟨σ, [b₁, b₂, b₃]⟩ (by simp [LoopIdx.length])
  beta_reduce
  linear_combination (A x b₁ * B y b₂ * C z b₃) * h

end Tau

/-! ## 5. The family `(Kn2sol)`, `(Kn3sol)` and its three properties -/

section Family

variable (d L W : ℕ) [NeZero L] (g E : ℝ) (m : ℂ)

/-- The family of the levels `n ≤ 3`: `PropSpin m` at length `1`, `(Kn2sol)` at length `2`, `(Kn3sol)` at length `3`,
`0` otherwise. -/
private def BAKSolve_K (t : ℝ) : LoopIdx (Zd d L) → ℂ
  | ⟨[s], [_]⟩ => PropSpin m s
  | ⟨[σ₁, σ₂], [a₁, a₂]⟩ =>
      (((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂
  | ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ =>
      BAKSolve_tau (fun b₁ b₂ b₃ => BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))
          ⟨[σ₁, σ₂, σ₃], [b₁, b₂, b₃]⟩)
        (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃) (BATheta d L g E m t σ₃ σ₁) a₁ a₂ a₃
  | _ => 0

variable {d L W g E m}

/-- `A ↦ A Q` is differentiable entrywise with derivative `A' Q`. -/
private theorem BAKSolve_mulRight_hasDerivAt {A : ℝ → Matrix (Zd d L) (Zd d L) ℂ} {A' : Matrix (Zd d L) (Zd d L) ℂ}
    {t : ℝ} (Q : Matrix (Zd d L) (Zd d L) ℂ) (hA : ∀ a b, HasDerivAt (fun s => A s a b) (A' a b) t)
    (a b : Zd d L) : HasDerivAt (fun s => (A s * Q) a b) ((A' * Q) a b) t := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun c _ => (hA a c).mul_const _

/-- The `2`-loop equation: `∂_t(W^{-d} Θ M) = W^{-d} Θ M Θ M = W^d (W^{-d} Θ M)(W^{-d} Θ M)`. -/
private theorem BAKSolve_two_hasDerivAt (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => BAKSolve_K d L W g E m s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (treeEqRhsS d L W 1 (BAKSolve_K d L W g E m t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  rw [BAKSolve_rhs_two]
  have h1 := (BAKSolve_mulRight_hasDerivAt (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂)
    (fun a b => BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₁ σ₂ a b) a₁ a₂).const_mul (((W : ℂ) ^ d)⁻¹)
  refine HasDerivAt.congr_deriv h1 ?_
  simp only [BAKSolve_K]
  have hYY : BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂ *
      BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ = (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) *
      (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) := Matrix.mul_assoc _ _ _
  rw [hYY, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := BAKSolve_wc_pow ((W : ℂ) ^ d) 0
  simp only [zero_add, pow_one] at h
  linear_combination (-((BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a *
    (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a a₂)) * h

/-- The `3`-loop equation: `∂_tΘ = ΘMΘ` on each leaf, against the three cuts `(1,2)`, `(1,3)`, `(2,3)`. -/
private theorem BAKSolve_three_hasDerivAt (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd d L) :
    HasDerivAt (fun s => BAKSolve_K d L W g E m s ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩)
      (treeEqRhsS d L W 1 (BAKSolve_K d L W g E m t) ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩) t := by
  rw [BAKSolve_rhs_three]
  set ℬ : Zd d L → Zd d L → Zd d L → ℂ := fun b₁ b₂ b₃ => BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))
    ⟨[σ₁, σ₂, σ₃], [b₁, b₂, b₃]⟩ with hℬ
  have hD := BAKSolve_tau_hasDerivAt ℬ
    (fun a b => BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₁ σ₂ a b)
    (fun a b => BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₂ σ₃ a b)
    (fun a b => BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₃ σ₁ a b) a₁ a₂ a₃
  refine HasDerivAt.congr_deriv hD ?_
  simp only [BAKSolve_K]
  have hwc : ∀ (A B C : Matrix (Zd d L) (Zd d L) ℂ) (x y z : Zd d L),
      ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * BAKSolve_tau ℬ A B C x y z = BAKSolve_tau ℬ A B C x y z :=
    BAKSolve_tau_wc W (BAMsigma d L (BAMB d L g (E : ℂ) m)) [σ₁, σ₂, σ₃]
  -- the three cuts
  have e1 : ((W : ℂ) ^ d) * ∑ a : Zd d L, BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
      (BATheta d L g E m t σ₃ σ₁) a a₂ a₃ * ((((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a) =
      BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂)
        (BATheta d L g E m t σ₂ σ₃) (BATheta d L g E m t σ₃ σ₁) a₁ a₂ a₃ := by
    calc _ = ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * ∑ a : Zd d L,
          (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a *
            BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
              (BATheta d L g E m t σ₃ σ₁) a a₂ a₃ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = _ := by rw [BAKSolve_tau_leg1, hwc]
  have e2 : ((W : ℂ) ^ d) * ∑ a : Zd d L, BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
      (BATheta d L g E m t σ₃ σ₁) a₁ a a₃ * ((((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ₂ σ₃ * BAMss d L (BAMB d L g (E : ℂ) m) σ₂ σ₃) a₂ a) =
      BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂)
        (BATheta d L g E m t σ₂ σ₃ * BAMss d L (BAMB d L g (E : ℂ) m) σ₂ σ₃ * BATheta d L g E m t σ₂ σ₃)
        (BATheta d L g E m t σ₃ σ₁) a₁ a₂ a₃ := by
    calc _ = ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * ∑ a : Zd d L,
          (BATheta d L g E m t σ₂ σ₃ * BAMss d L (BAMB d L g (E : ℂ) m) σ₂ σ₃) a₂ a *
            BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
              (BATheta d L g E m t σ₃ σ₁) a₁ a a₃ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          ring
      _ = _ := by rw [BAKSolve_tau_leg2, hwc]
  have e3 : ((W : ℂ) ^ d) * ∑ a : Zd d L, ((((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ₁ σ₃ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₃) a a₃) *
      BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
        (BATheta d L g E m t σ₃ σ₁) a₁ a₂ a =
      BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
        (BATheta d L g E m t σ₃ σ₁ * BAMss d L (BAMB d L g (E : ℂ) m) σ₃ σ₁ * BATheta d L g E m t σ₃ σ₁)
        a₁ a₂ a₃ := by
    have hsw : ∀ a : Zd d L, (BATheta d L g E m t σ₁ σ₃ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₃) a a₃ =
        (BATheta d L g E m t σ₃ σ₁ * BAMss d L (BAMB d L g (E : ℂ) m) σ₃ σ₁) a₃ a := fun a => by
      rw [BATheta_swap g E m t σ₁ σ₃, BAKSolve_Mss_swap g E m σ₁ σ₃]
      exact BAKSolve_ThQ_symm g κ E m hr ht0 ht1 σ₃ σ₁ a a₃
    calc _ = ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * ∑ a : Zd d L,
          (BATheta d L g E m t σ₃ σ₁ * BAMss d L (BAMB d L g (E : ℂ) m) σ₃ σ₁) a₃ a *
            BAKSolve_tau ℬ (BATheta d L g E m t σ₁ σ₂) (BATheta d L g E m t σ₂ σ₃)
              (BATheta d L g E m t σ₃ σ₁) a₁ a₂ a := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [hsw a]
          ring
      _ = _ := by rw [BAKSolve_tau_leg3, hwc, Matrix.mul_assoc]
  rw [mul_add, mul_add, e1, e2, e3]
  ring


omit [NeZero L] in
/-- A well-formed loop of length `3` is `⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩`. -/
private theorem BAKSolve_exists_eq_of_length_three {I : LoopIdx (Zd d L)} (hI : I.WF) (h3 : I.length = 3) :
    ∃ (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd d L), I = ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ := by
  obtain ⟨σ, a⟩ := I
  have ha : a.length = 3 := h3
  have hσ : σ.length = 3 := hI.trans ha
  obtain ⟨a₁, a₂, a₃, rfl⟩ := List.length_eq_three.mp ha
  obtain ⟨σ₁, σ₂, σ₃, rfl⟩ := List.length_eq_three.mp hσ
  exact ⟨σ₁, σ₂, σ₃, a₁, a₂, a₃, rfl⟩

/-- At `t = 0`, `Θ = 1`, so the family is the `M`-loop `BAMLoop` (`(eq:initial_K)`, K00 convention). -/
private theorem BAKSolve_zero (I : LoopIdx (Zd d L)) (hI : I.WF) (h2 : 2 ≤ I.length) (h3 : I.length ≤ 3) :
    BAKSolve_K d L W g E m 0 I = BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) I := by
  rcases (show I.length = 2 ∨ I.length = 3 by omega) with hl | hl
  · obtain ⟨σ₁, σ₂, a₁, a₂, rfl⟩ := exists_eq_of_length_two hI hl
    simp only [BAKSolve_K, BAKSolve_Theta_zero, Matrix.one_mul]
    simp [BAMLoop, BAMss, LoopIdx.length, List.rotate]
  · obtain ⟨σ₁, σ₂, σ₃, a₁, a₂, a₃, rfl⟩ := BAKSolve_exists_eq_of_length_three hI hl
    simp only [BAKSolve_K, BAKSolve_Theta_zero]
    exact BAKSolve_tau_one _ a₁ a₂ a₃


end Family

/-! ## 6. `baKsolveLe3_holds` -/

/-- **`baKsolveLe3_holds`** (K03's target): the levels `n ≤ 3` of the block Anderson `K`-loop equation are solved by
`(Kn2sol)` and `(Kn3sol)`, at every `d`, for every `BAReal` datum with `3 ≤ L`, every `W` and every `t ∈ [0,1)`.
No hypothesis beyond `BAReal` and `3 ≤ L`: `W` is arbitrary (`W^d (W^d)⁻¹ = 1` is used only against a factor
`(W^d)⁻¹`, so it also holds at `W^d = 0`). -/
theorem baKsolveLe3_holds : ∀ d, BAKsolveLe3 d := by
  intro d Λ κ hΛ hκ L hL W g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr
  refine ⟨BAKSolve_K d L W g E m, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro t ht I hI h2 h3
    rcases (show I.length = 2 ∨ I.length = 3 by omega) with hl | hl
    · obtain ⟨σ₁, σ₂, a₁, a₂, rfl⟩ := exists_eq_of_length_two hI hl
      exact BAKSolve_two_hasDerivAt hr ht.1 ht.2 σ₁ σ₂ a₁ a₂
    · obtain ⟨σ₁, σ₂, σ₃, a₁, a₂, a₃, rfl⟩ := BAKSolve_exists_eq_of_length_three hI hl
      exact BAKSolve_three_hasDerivAt hr ht.1 ht.2 σ₁ σ₂ σ₃ a₁ a₂ a₃
  · intro I hI h2 h3
    exact BAKSolve_zero I hI h2 h3
  · intro t ht s a
    rfl
  · intro t ht σ a₁ a₂
    rfl
  · intro t ht σ₁ σ₂ σ₃ a₁ a₂ a₃
    rfl

/-! ## 7. The BA instances of the generic K01 pins (`S = 1`, initial data `BAMLoop`) -/

section Instances01

/-- `(l ++ [x]).getD j = (x :: l).getD ((j+1) mod (|l|+1))` on `j ≤ |l|`: moving the head to the end. -/
private theorem BAKSolve_getD_snoc {α : Type*} (l : List α) (x d : α) (j : ℕ) (hj : j < l.length + 1) :
    (l ++ [x]).getD j d = (x :: l).getD ((j + 1) % (l.length + 1)) d := by
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
  · rw [Nat.mod_eq_of_lt (by omega), List.getD_append _ _ _ _ h, List.getD_cons_succ]
  · subst h
    rw [Nat.mod_self, List.getD_append_right _ _ _ _ le_rfl]
    simp

/-- A cyclic reindexing does not change a product over `range (n+1)`. -/
private theorem BAKSolve_prod_rot (f : ℕ → ℂ) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), f ((i + 1) % (n + 1)) = ∏ i ∈ Finset.range (n + 1), f i := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ' f, Nat.mod_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hi; omega)]

/-- **`BAMLoop` is cyclically invariant** (the hypothesis of `RotS` at `M = BAMLoop`): the K00 product
`W^{-(n-1)d} ∏_i M(σ_i)_{a_{i-1} a_i}` over the cyclic edges is a commutative product over the same factors. -/
theorem BAMLoop_rot (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) (hσa : σ.length = a.length) :
    BAMLoop d L W M ⟨s :: σ, b :: a⟩ = BAMLoop d L W M ⟨σ ++ [s], a ++ [b]⟩ := by
  have e1 := BAMLoop_apply d L W M ⟨s :: σ, b :: a⟩ (a.length + 1) (by omega) (by simp [hσa]) (by simp)
  have e2 := BAMLoop_apply d L W M ⟨σ ++ [s], a ++ [b]⟩ (a.length + 1) (by omega) (by simp [hσa]) (by simp)
  rw [e1, e2]
  congr 1
  rw [← BAKSolve_prod_rot (fun i => M ((s :: σ).getD i false)
    ((b :: a).getD ((i + (a.length + 1 - 1)) % (a.length + 1)) 0) ((b :: a).getD i 0)) a.length]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i < a.length + 1 := Finset.mem_range.1 hi
  have hj : (i + (a.length + 1 - 1)) % (a.length + 1) < a.length + 1 := Nat.mod_lt _ (by omega)
  have hσ' : i < σ.length + 1 := by omega
  dsimp only
  rw [BAKSolve_getD_snoc σ s false i hσ', BAKSolve_getD_snoc a b 0 i hi',
    BAKSolve_getD_snoc a b 0 _ hj, hσa]
  have e3 : (((i + (a.length + 1 - 1)) % (a.length + 1) + 1) % (a.length + 1)) =
      (((i + 1) % (a.length + 1) + (a.length + 1 - 1)) % (a.length + 1)) := by
    rw [Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega
  rw [e3]

/-- **`BAMLoop` is translation invariant** (the hypothesis of `TranslS` at `M = BAMLoop`) when every `M(σ)` is
(`M(σ)_{x+c, y+c} = M(σ)_{xy}`). -/
theorem BAMLoop_translate (d L W : ℕ) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ (σ : Bool) (x y c : Zd d L), M σ (x + c) (y + c) = M σ x y) (c : Zd d L) (I : LoopIdx (Zd d L)) :
    BAMLoop d L W M ⟨I.σ, I.a.map (· + c)⟩ = BAMLoop d L W M I := by
  unfold BAMLoop
  simp only [LoopIdx.length, List.length_map]
  congr 1
  rw [← List.map_rotate, List.zip_map, List.zip_map_right, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun p _ => ?_)
  simp only [Function.comp, Prod.map_fst, Prod.map_snd, id]
  exact hM _ _ _ _

/-- `M(σ)` of the block Anderson model is translation invariant (`BAMB_shift`, `BA/Ward.lean:53`; `M(-) = M^*`). -/
theorem BAMsigma_shift (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (σ : Bool) (x y c : Zd d L) :
    BAMsigma d L (BAMB d L g z m) σ (x + c) (y + c) = BAMsigma d L (BAMB d L g z m) σ x y := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, BAMB_shift]
  · exact BAMB_shift d L g z m x y c

variable {d L W : ℕ} [NeZero L] (m : Bool → ℂ) (Ms : Bool → Matrix (Zd d L) (Zd d L) ℂ)

/-- **Uniqueness of the BA `𝒦`** (`S = 1`, initial data `BAMLoop`): two families of `K`-loops on `[0,1)` agree on
every well-formed loop of length `≥ 2` (`uniqS_holds` with the `2`-loop bound `retireS_holds` of both). -/
theorem baK_unique {K K' : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K)
    (hK' : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K') :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ I : LoopIdx (Zd d L), I.WF → 2 ≤ I.length → K t I = K' t I := by
  intro t ht I hI h2
  obtain ⟨R, hR0, hR⟩ := retireS_holds d L W 1 m (BAMLoop d L W Ms) hK t ht.2
  obtain ⟨R', hR'0, hR'⟩ := retireS_holds d L W 1 m (BAMLoop d L W Ms) hK' t ht.2
  exact uniqS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.2.1 hK hK' (T₀ := t) (R := max R R')
    (fun r hr => ⟨hr.1, lt_of_le_of_lt hr.2 ht.2⟩) (le_trans hR0 (le_max_left _ _))
    (fun r hr J hJ hJ2 => ⟨(hR r hr J hJ hJ2).trans (le_max_left _ _),
      (hR' r hr J hJ hJ2).trans (le_max_right _ _)⟩) t ⟨ht.1, le_rfl⟩ I hI h2

/-- **Cyclic invariance of the BA `𝒦`** (the form of `KLK_rotate`): `rotS_holds` at `S = 1`, `M = BAMLoop`
(`kernel_one_rot_transl`, `BAMLoop_rot`). -/
theorem baK_rotate {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length → K t ⟨s :: σ, b :: a⟩ = K t ⟨σ ++ [s], a ++ [b]⟩ :=
  rotS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.1 kernel_one_rot_transl.2.1
    (fun s b σ a h => BAMLoop_rot d L W Ms s b σ a h) hK

/-- **Translation invariance of the BA `𝒦`** (the form of `KLK_translate`), for `M(σ)` translation invariant:
`translS_holds` at `S = 1`, `M = BAMLoop` (`kernel_one_rot_transl`, `BAMLoop_translate`). -/
theorem baK_translate (hMs : ∀ (σ : Bool) (x y c : Zd d L), Ms σ (x + c) (y + c) = Ms σ x y)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) m (BAMLoop d L W Ms) (Set.Ico (0 : ℝ) 1) K) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      K t ⟨I.σ, I.a.map (· + c)⟩ = K t I :=
  translS_holds d L W 1 m (BAMLoop d L W Ms) kernel_one_rot_transl.2.2 kernel_one_rot_transl.2.1
    (fun c I => BAMLoop_translate d L W Ms hMs c I) hK

end Instances01

/-! ## 8. `BAKsol` under the pin `BAKsolve d` -/

section BAKsolSection

/-- `BAKsol` is the solution that `BAKsolve` provides (probe `t/T2360:RBM3D/Probe/T2360Pins.lean:293`). -/
theorem BAKsol_isKLoopS {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1)
      (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m)) := by
  obtain ⟨K, hK, -⟩ := h Λ κ hΛ hκ L hL W g hg hgΛ E m hr
  have hex : ∃ K : ℝ → LoopIdx (Zd d L) → ℂ, IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K := ⟨K, hK⟩
  simp only [BAKsol, hex, ↓reduceDIte]
  exact hex.choose_spec

/-- **BA rotation**: `BAKsol` is cyclically invariant (the BA counterpart of `KLK_rotate`), under the pin
`BAKsolve d`. -/
theorem BAKsol_rotate {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (b : Zd d L) (σ : List Bool) (a : List (Zd d L)),
      σ.length = a.length →
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: σ, b :: a⟩ =
        BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨σ ++ [s], a ++ [b]⟩ :=
  baK_rotate _ _ (BAKsol_isKLoopS h hΛ hκ hL hg hgΛ hr)

/-- **BA translation**: `BAKsol` is translation invariant (the BA counterpart of `KLK_translate`), under the pin
`BAKsolve d` (`BAMsigma_shift`). -/
theorem BAKsol_translate {d : ℕ} (h : BAKsolve d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) {W : ℕ} {g : ℝ} (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (c : Zd d L) (I : LoopIdx (Zd d L)), I.WF →
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨I.σ, I.a.map (· + c)⟩ =
        BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t I :=
  baK_translate _ _ (fun σ x y c => BAMsigma_shift d L g (E : ℂ) m σ x y c) (BAKsol_isKLoopS h hΛ hκ hL hg hgΛ hr)

end BAKsolSection

/-! ## 9. Compiled nonempty instances

Data: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 (Im m₀) P.E m₀`,
`0 < P.g0 ≤ 10`, the data of `KBaseInst`), `W = 2` (`W^d = 8`), `Λ = 10`, `κ = Im m₀ > 0`.  Every deterministic hypothesis
is discharged.  `BAKsolve 3` (K05b's pin, not proved here) stays a hypothesis of the examples that need a family at all
lengths (`baK_*`, `BAKsol_*`). -/

namespace KSolveInst

open RBM.BA.MFixedPointInst

/-- `m₀ ≠ 0` (`Im m₀ > 0`). -/
private theorem m0_ne : P.m0 ≠ 0 := fun h => by
  have := P.real.1.1
  simp [h] at this

/-- **`baKsolveLe3_holds` at `P`, `W = 2`**: every deterministic hypothesis discharged. -/
example : ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
    IsKLoopSLe 3 4 2 3 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
      (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K ∧
    (∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd 3 4),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ =
        (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (BATheta 3 4 P.g0 P.E P.m0 t σ.1 σ.2 *
          BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ.1 σ.2) a₁ a₂) ∧
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ₁ σ₂ σ₃ : Bool) (a₁ a₂ a₃ : Zd 3 4),
      K t ⟨[σ₁, σ₂, σ₃], [a₁, a₂, a₃]⟩ =
        ∑ b₁ : Zd 3 4, ∑ b₂ : Zd 3 4, ∑ b₃ : Zd 3 4,
          BATheta 3 4 P.g0 P.E P.m0 t σ₁ σ₂ a₁ b₁ * BATheta 3 4 P.g0 P.E P.m0 t σ₂ σ₃ a₂ b₂ *
            BATheta 3 4 P.g0 P.E P.m0 t σ₃ σ₁ a₃ b₃ *
            BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) ⟨[σ₁, σ₂, σ₃], [b₁, b₂, b₃]⟩ :=
  baKsolveLe3_holds 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real

/-- **Nondegeneracy of the instance**: the family of `baKsolveLe3_holds` at `P`, `W = 2` solves the levels `n ≤ 3`
and its `2`-loop at `t = 0`, `σ = (+,-)`, `a = (0,0)` is `W^{-d} M^{(+-)}_{00} = 8⁻¹ |m₀|² ≠ 0`. -/
theorem le3_nondeg : ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
    IsKLoopSLe 3 4 2 3 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
      (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K ∧
    K 0 ⟨[true, false], [0, 0]⟩ = (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) ∧
    (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) ≠ 0 := by
  obtain ⟨K, hK, h2, -⟩ := baKsolveLe3_holds 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0
    P.g0_pos P.g0_le P.E P.m0 P.real
  have hval : K 0 ⟨[true, false], [0, 0]⟩ = (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) := by
    rw [show (⟨[true, false], [0, 0]⟩ : LoopIdx (Zd 3 4)) = ⟨[(true, false).1, (true, false).2], [0, 0]⟩ from rfl,
      h2 0 ⟨le_rfl, zero_lt_one⟩ (true, false) 0 0, BAKSolve_Theta_zero, Matrix.one_mul]
    simp only [BAMss, Matrix.of_apply, BAMsigma, ite_true, Bool.false_eq_true, ite_false,
      Matrix.conjTranspose_apply, BAMB_diag_eq 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1, Complex.star_def]
  refine ⟨K, hK, hval, ?_⟩
  refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num))) (mul_ne_zero m0_ne ?_)
  simpa using m0_ne

/-- `BAMLoop_rot` at the K00 witness `BAMLoop_witM` (`BA/KBase.lean:102`; the loop `(+,+,-)`, labels `(0,1,2)`, value
`15`): the rotated loop `(+,-,+)`, labels `(1,2,0)`, has the same value. -/
theorem rot_witness :
    BAMLoop 1 3 1 BAMLoop_witM ⟨true :: [true, false], (![0] : Zd 1 3) :: [![1], ![2]]⟩ =
      BAMLoop 1 3 1 BAMLoop_witM ⟨[true, false] ++ [true], [![1], ![2]] ++ [(![0] : Zd 1 3)]⟩ ∧
    BAMLoop 1 3 1 BAMLoop_witM ⟨[true, false] ++ [true], [![1], ![2]] ++ [(![0] : Zd 1 3)]⟩ = 15 :=
  ⟨BAMLoop_rot 1 3 1 BAMLoop_witM true ![0] [true, false] [![1], ![2]] rfl,
    (BAMLoop_rot 1 3 1 BAMLoop_witM true ![0] [true, false] [![1], ![2]] rfl).symm.trans BAMLoop_witness⟩

/-- `BAMsigma_shift` at `P` (`M(+) = M^{(B)}` and `M(-) = (M^{(B)})^*`, shift `e₁`). -/
example (σ : Bool) : BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ (![0, 1, 2] + ![1, 0, 0]) (![1, 0, 3] + ![1, 0, 0]) =
    BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ ![0, 1, 2] ![1, 0, 3] :=
  BAMsigma_shift 3 4 P.g0 (P.E : ℂ) P.m0 σ _ _ _

/-- `BAMLoop_translate` at the BA data of `P`, `W = 2`: the `3`-loop `(+,-,+)` with labels `(0,0,0), (1,0,0), (2,1,0)`
translated by `e₁`; and the nonvanishing `2`-loop `(+,-)` at `(0,0)`. -/
theorem translate_BAMLoop :
    BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨[true, false, true], ([![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] : List (Zd 3 4)).map (· + (![1, 0, 0] : Zd 3 4))⟩ =
      BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨[true, false, true], ([![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] : List (Zd 3 4))⟩ ∧
    BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) ⟨[true, false], [0, 0]⟩ ≠ 0 :=
  ⟨BAMLoop_translate 3 4 2 _ (fun σ x y c => BAMsigma_shift 3 4 P.g0 (P.E : ℂ) P.m0 σ x y c) ![1, 0, 0]
      ⟨[true, false, true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩, by
    have e : BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) ⟨[true, false], [0, 0]⟩ =
        (((2 : ℕ) : ℂ) ^ 3)⁻¹ * (P.m0 * starRingEnd ℂ P.m0) := by
      simp [BAMLoop, LoopIdx.length, List.rotate, BAMsigma, BAMB_diag_eq 3 4 P.g0 (P.E : ℂ) P.m0 P.real.1,
        Complex.star_def]
    rw [e]
    refine mul_ne_zero (inv_ne_zero (pow_ne_zero _ (by norm_num))) (mul_ne_zero m0_ne ?_)
    simpa using m0_ne⟩

/-- `baK_unique` at the BA data of `P`, `W = 2`, under `BAKsolve 3`: the witness `K` of the pin and `BAKsol` agree on a
`3`-loop at `t = 1/2`. -/
theorem unique_inst (h : BAKsolve 3) :
    ∃ K : ℝ → LoopIdx (Zd 3 4) → ℂ,
      IsKLoopS 3 4 2 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
        (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K ∧
      K (1 / 2) ⟨[true, false, true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩ =
        BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
          ⟨[true, false, true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩ := by
  obtain ⟨K, hK, -⟩ := h 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real
  exact ⟨K, hK, baK_unique _ _ hK (BAKsol_isKLoopS h (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real)
    (1 / 2) ⟨by norm_num, by norm_num⟩ _ (by simp [LoopIdx.WF]) (by simp [LoopIdx.length])⟩

/-- `baK_rotate` (through `BAKsol_rotate`) at the BA data of `P`, `W = 2`, `t = 1/2`, under `BAKsolve 3`: a `2`-loop and a
`3`-loop. -/
theorem rotate_inst (h : BAKsolve 3) :
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨true :: [false], (![0, 0, 0] : Zd 3 4) :: [![1, 0, 0]]⟩ =
      BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[false] ++ [true], [![1, 0, 0]] ++ [(![0, 0, 0] : Zd 3 4)]⟩ ∧
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨true :: [false, true], (![0, 0, 0] : Zd 3 4) :: [![1, 0, 0], ![2, 1, 0]]⟩ =
      BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[false, true] ++ [true], [![1, 0, 0], ![2, 1, 0]] ++ [(![0, 0, 0] : Zd 3 4)]⟩ :=
  ⟨BAKsol_rotate h (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real (1 / 2) ⟨by norm_num, by norm_num⟩
      true ![0, 0, 0] [false] [![1, 0, 0]] rfl,
    BAKsol_rotate h (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real (1 / 2) ⟨by norm_num, by norm_num⟩
      true ![0, 0, 0] [false, true] [![1, 0, 0], ![2, 1, 0]] rfl⟩

/-- `baK_translate` (through `BAKsol_translate`) at the BA data of `P`, `W = 2`, `t = 1/2`, shift `e₁`, under
`BAKsolve 3`: a `2`-loop and a `3`-loop. -/
theorem translate_inst (h : BAKsolve 3) :
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[true, false], ([![0, 0, 0], ![1, 0, 0]] : List (Zd 3 4)).map (· + (![1, 0, 0] : Zd 3 4))⟩ =
      BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[true, false], [![0, 0, 0], ![1, 0, 0]]⟩ ∧
    BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[true, false, true], ([![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] : List (Zd 3 4)).map (· + (![1, 0, 0] : Zd 3 4))⟩ =
      BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨[true, false, true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩ :=
  ⟨BAKsol_translate h (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real (1 / 2) ⟨by norm_num, by norm_num⟩
      ![1, 0, 0] ⟨[true, false], [![0, 0, 0], ![1, 0, 0]]⟩ rfl,
    BAKsol_translate h (by norm_num) P.real.1.1 (by norm_num) P.g0_pos P.g0_le P.real (1 / 2) ⟨by norm_num, by norm_num⟩
      ![1, 0, 0] ⟨[true, false, true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩ rfl⟩

end KSolveInst

end RBM.BA
