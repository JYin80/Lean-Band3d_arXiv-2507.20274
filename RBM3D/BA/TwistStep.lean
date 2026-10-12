/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistGridRem2
import RBM3D.BA.TwistGridTail2
import RBM3D.BA.TwistGridWTail2
import RBM3D.BA.TwistKer2
import RBM3D.BA.TwistQV
import RBM3D.BA.KBase
import RBM3D.BA.Ward
import RBM3D.BA.TwistGridTail
import RBM3D.Induction.Step2Events

/-!
# BA stage TL, row TL2d (T2441), part 1: the pin, the zero mode, the grid walk at one time

Ticket `docs/tickets/T2441.md`; probe `RBM3D/Probe/T2441Pins.lean` at `f459c7f`
(branch `t/T2441`, never merged); proofs `docs/tickets/T2398-TL-proofs.md` T.12', T.12'';
paper arXiv:2507.20274, (D.5), (D.8).

* **The pin** `BATwistStepFixed` (target 3, text of the probe): T.12' at one time sequence
  `τ ∈ [s,t]`, all four charges, in the frame `BATwFrame`; the bootstrap hypothesis is the `≺` form
  at a deterministic level `Ξ ≥ 1` over `TimeIcc s t` (the shape of `twSrc`).
* **Target 1** `baTwistGridMart_holds`: the three part pins of TL2a2-TL2a4 assembled.
* **Target 2** `baTwistZeroMode_holds` (T.12''): the row sums of `Θ^{(σ₁σ₂)}` and the matrix Ward
  identity `M^*M = (M - M^*)/(2i Im m)`.
* The pathwise estimate of the grid walk at the last grid point (the exact Duhamel/Abel identity,
  the bound of the five pieces), the six events of the walk transported from the model, the
  deterministic core at one size index, the transport back to the model for labels, the scale of the
  kernel `ℓ_v(g₀) ≥ √t₀ ℓ_v(lam)` (F1) and the comparability of `B_{v,0}` (4.18).

Every statement is for every `d` (the pin has `3 ≤ d` through `BATwFrame`).  Private helpers carry
the stem `TwistStep_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Target 3: the pin -/

/-- **T.12' at one fixed time** (TP:151-171, Proposition T.12', cases (A)-(C)): from TL2 at `s` and the bootstrap bound `‖Z_v‖ ≺ Ξ B_v^{3/2}` on `[s,t]` (`Z = L̃ - K̃`, deterministic `Ξ ≥ 1`),
for every time sequence `τ ∈ [s,t]` (per `τ`, all `σ`, `a`, `c₁`, `c₂`): `‖Z_τ‖ ≺ B_τ^{3/2} (1 + B_τ^{1/6} Ξ)`; the net and the iteration of `Ξ` are TL2e's. -/
def BATwistStepFixed (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  BATwFrame d R fun sz C μ s t =>
    BATwistLoopLaw C μ s → ∀ Ξ : ℕ → ℝ, (∀ n, 1 ≤ Ξ n) →
      PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
        (fun n p ω => ‖twL2' C n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK C n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖)
        (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ)) →
      ∀ τ : ℕ → ℝ, (∀ n, s n ≤ τ n) → (∀ n, τ n ≤ t n) →
        PrecL sz μ (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
          (fun n p ω => ‖twL2' C n (τ n) ω p.1 p.2.1 p.2.2.1 p.2.2.2 - twK C n (τ n) p.1 p.2.1 p.2.2.1 p.2.2.2‖)
          (fun n _ _ => sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ n))

/-! ## 2. Target 1: `baTwistGridMart_holds` (§242 (2): a three-line corollary) -/

/-- **Target 1**: the grid martingale pin 4 (b) at every `d`: `baTwistGridRem_holds`, `baTwistGridTail_holds`, `baTwistGridWTail_holds` assembled by `baTwistGridAssemble_holds`. -/
theorem baTwistGridMart_holds (d : ℕ) : BATwistGridMart d := by
  obtain ⟨C₀, hC₀, hR⟩ := baTwistGridRem_holds d
  exact ⟨C₀, hC₀, baTwistGridAssemble_holds d C₀ hC₀ hR (baTwistGridTail_holds d) (baTwistGridWTail_holds d)⟩

/-! ## 3. Target 2: `baTwistZeroMode_holds` (T.12'', TP:175) -/

/-- The matrix Ward identity `M^* - M = -2i (Im m) M^* M` and `M - M^* = 2i (Im m) M M^*` for `M = (gΨ - E - m)⁻¹`, `Im m > 0`. -/
theorem TwistStep_ward_mat {d L : ℕ} [NeZero L] (g E : ℝ) {m : ℂ} (hm : 0 < m.im) :
    (BAMB d L g (E : ℂ) m)ᴴ - BAMB d L g (E : ℂ) m = (-(2 * Complex.I * (m.im : ℂ))) • ((BAMB d L g (E : ℂ) m)ᴴ * BAMB d L g (E : ℂ) m) ∧
    BAMB d L g (E : ℂ) m - (BAMB d L g (E : ℂ) m)ᴴ = (2 * Complex.I * (m.im : ℂ)) • (BAMB d L g (E : ℂ) m * (BAMB d L g (E : ℂ) m)ᴴ) := by
  set A : Matrix (Zd d L) (Zd d L) ℂ := ((g : ℂ) • PsiB d L) - ((E : ℂ) + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) with hAdef
  have hw : 0 < (((E : ℂ) + m)).im := by simpa using hm
  have hA : IsUnit A := RBM.isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L g) hw.ne'
  have hM : BAMB d L g (E : ℂ) m = Ring.inverse A := rfl
  set M := BAMB d L g (E : ℂ) m with hMdef
  have h1 : A * M = 1 := by rw [hM]; exact Ring.mul_inverse_cancel _ hA
  have h2 : M * A = 1 := by rw [hM]; exact Ring.inverse_mul_cancel _ hA
  have hAH : Aᴴ = ((g : ℂ) • PsiB d L) - ((starRingEnd ℂ) ((E : ℂ) + m)) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    rw [hAdef, Matrix.conjTranspose_sub, (BAPsi_isHermitian d L g).eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    rfl
  have hdiff : A - Aᴴ = (-(2 * Complex.I * (m.im : ℂ))) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    rw [hAH, hAdef]
    have : ((E : ℂ) + m) - (starRingEnd ℂ) ((E : ℂ) + m) = 2 * Complex.I * (m.im : ℂ) := by
      refine Complex.ext (by simp) (by simp; ring)
    rw [sub_sub_sub_cancel_left, ← sub_smul, ← neg_sub, this, neg_smul]
  have h1H : Mᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  have h2H : Aᴴ * Mᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  constructor
  · calc Mᴴ - M = Mᴴ * (A * M) - (Mᴴ * Aᴴ) * M := by rw [h1, h1H]; simp
      _ = Mᴴ * (A - Aᴴ) * M := by noncomm_ring
      _ = _ := by rw [hdiff]; simp
  · calc M - Mᴴ = M * (Aᴴ * Mᴴ) - (M * A) * Mᴴ := by rw [h2H, h2]; simp
      _ = M * (Aᴴ - A) * Mᴴ := by noncomm_ring
      _ = _ := by
        have : Aᴴ - A = (2 * Complex.I * (m.im : ℂ)) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
          rw [← neg_sub, hdiff, neg_smul, neg_neg]
        rw [this]; simp

/-- **T.12''** (`TP:175`, `BATwistZeroMode`): for `σ₁ ≠ σ₂` the row sums of `Θ^{(σ₁σ₂)}` are `(1-t)⁻¹` (`BATheta_row_sum_pm`, with `BATheta_swap` for `(-,+)`)
and `M^*M = (M - M^*)/(2i Im m)` (`TwistStep_ward_mat`), so `Σ_a K̃ = (2i W^d η_t)⁻¹ (M_{c₂c₁} - (M^*)_{c₂c₁})`, `η_t = (1-t) Im m`. -/
theorem baTwistZeroMode_holds (d : ℕ) : BATwistZeroMode d := by
  intro hd κ ε 𝔡 𝔠 hκ hε h𝔡 sz z hflow t ht0 htT n σ hσ c₁ c₂
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hmF : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hr.1.1
  have ht1 : t n < 1 := (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  set g := BAflowLam0 sz z n with hg
  set E := BAflowEs sz z n with hE
  set m := BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n with hm
  obtain ⟨hw1, hw2⟩ := TwistStep_ward_mat (d := d) (L := sz.L n) g E hmF
  set M := BAMB d (sz.L n) g (E : ℂ) m with hMdef
  have hW : ((sz.W n : ℕ) : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (sz.W_pos n).ne')
  have hη : ((baFMz sz z).eta n (t n) : ℝ) = (1 - t n) * m.im := rfl
  have h1t : (1 - (t n : ℂ)) ≠ 0 := by
    have : (1 : ℝ) - t n ≠ 0 := by linarith
    exact_mod_cast this
  have hmi : (m.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hmF.ne'
  -- the row sum of `Θ^{(σ₁σ₂)}`
  have hrow : ∀ a' : Zd d (sz.L n), ∑ a, BATheta d (sz.L n) g E m (t n) (σ 0) (σ 1) a a' = (1 - (t n : ℂ))⁻¹ := by
    intro a'
    have hTT : ∀ b : Bool, BATheta d (sz.L n) g E m (t n) b (!b) = BATheta d (sz.L n) g E m (t n) true false := by
      intro b; cases b
      · exact BATheta_swap g E m (t n) false true
      · rfl
    have hσb : σ 1 = !σ 0 := by
      cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all
    rw [hσb, hTT]
    have hsym := BATheta_isSymm d (sz.L n) g κ E m hr (t n) (ht0 n) ht1 true false
    have : ∀ a : Zd d (sz.L n), BATheta d (sz.L n) g E m (t n) true false a a' = BATheta d (sz.L n) g E m (t n) true false a' a := by
      intro a
      have := congrFun (congrFun hsym a') a
      simpa [Matrix.transpose_apply] using this
    simp_rw [this]
    exact BATheta_row_sum_pm d (sz.L n) g κ E m hr (t n) (ht0 n) ht1 a'
  have hK : ∀ a, twK (baFMz sz z) n (t n) σ a c₁ c₂ = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ a', BATheta d (sz.L n) g E m (t n) (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) M (σ 0) c₂ a' * BAMsigma d (sz.L n) M (σ 1) a' c₁ := fun a => twK_ba z n hmF (t n) σ a c₁ c₂
  simp_rw [hK]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hcol : ∀ a' : Zd d (sz.L n), ∑ a, BATheta d (sz.L n) g E m (t n) (σ 0) (σ 1) a a' * BAMsigma d (sz.L n) M (σ 0) c₂ a' * BAMsigma d (sz.L n) M (σ 1) a' c₁ =
      (1 - (t n : ℂ))⁻¹ * (BAMsigma d (sz.L n) M (σ 0) c₂ a' * BAMsigma d (sz.L n) M (σ 1) a' c₁) := by
    intro a'
    rw [← hrow a', Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [hcol]
  rw [← Finset.mul_sum, twMB_ba z n hmF]
  have hprod : ∑ a', BAMsigma d (sz.L n) M (σ 0) c₂ a' * BAMsigma d (sz.L n) M (σ 1) a' c₁ =
      (2 * Complex.I * (m.im : ℂ))⁻¹ * (M c₂ c₁ - Mᴴ c₂ c₁) := by
    have hσb : (σ 0 = true ∧ σ 1 = false) ∨ (σ 0 = false ∧ σ 1 = true) := by
      cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all
    have h2i : (2 * Complex.I * (m.im : ℂ)) ≠ 0 := by simp [hmi]
    rcases hσb with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · rw [h0, h1]
      have e1 : ∑ a', BAMsigma d (sz.L n) M true c₂ a' * BAMsigma d (sz.L n) M false a' c₁ = (M * Mᴴ) c₂ c₁ := by
        rw [Matrix.mul_apply]; simp [BAMsigma]
      have e2 := congrFun (congrFun hw2 c₂) c₁
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at e2
      rw [e1, e2]; field_simp
    · rw [h0, h1]
      have e1 : ∑ a', BAMsigma d (sz.L n) M false c₂ a' * BAMsigma d (sz.L n) M true a' c₁ = (Mᴴ * M) c₂ c₁ := by
        rw [Matrix.mul_apply]; simp [BAMsigma]
      have e2 := congrFun (congrFun hw1 c₂) c₁
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, neg_mul] at e2
      rw [e1]
      rw [eq_comm, inv_mul_eq_iff_eq_mul₀ h2i]
      linear_combination (-1 : ℂ) * e2
  rw [hprod]
  simp only [BAMsigma, ite_true, Bool.false_eq_true, ite_false, hη]
  push_cast
  field_simp
  rfl

/-! ## 4. The exact discrete Duhamel / Abel identity of the grid walk at the last grid point (abstract algebra) -/

section Algebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exact identity at the last grid point (all vectors `ι → ℂ`): from the decomposition `A_k = A_0 + Δ Σ_{j<k} (Θ_j M A_j + S_j) + R_k + Mt_k` (clause (i) of 4 (b))
and the kernel relations `Ũ_{j,j+1} = 1 + Δ Θ_{j+1} M`, `U_j = U_{j+1} + Δ X`, `U_K = 1`, `U_{j+1} Ũ_j = U_j`: `A_K = U_0 A_0 + Δ Σ_j U_{j+1} S_j + (R_K + Δ X Σ_j R_j) +
(Σ_j U_j (Mt_{j+1} - Mt_j) - Δ X Mt_K) + Σ_j U_{j+1} Δ (Θ_j - Θ_{j+1}) M A_j` (the telescope, the summation by parts of `Rem`, and decision 4 of the T2428 report: the weights `U_j` against `U_{j+1}`). -/
theorem TwistStep_identity (Δ : ℂ) (K : ℕ) (X Mm : Matrix ι ι ℂ) (Θ U Ut : ℕ → Matrix ι ι ℂ)
    (hUK : U K = 1) (hcomp : ∀ j < K, U (j + 1) * Ut j = U j)
    (hUt : ∀ j < K, Ut j = 1 + Δ • (Θ (j + 1) * Mm)) (hUd : ∀ j < K, U j = U (j + 1) + Δ • X)
    (A S R Mt : ℕ → ι → ℂ) (hR0 : R 0 = 0) (hM0 : Mt 0 = 0)
    (hdec : ∀ k ≤ K, A k = A 0 + Δ • ∑ j ∈ Finset.range k, ((Θ j * Mm) *ᵥ A j + S j) + R k + Mt k) :
    A K = U 0 *ᵥ A 0 + Δ • ∑ j ∈ Finset.range K, U (j + 1) *ᵥ S j + (R K + Δ • (X *ᵥ ∑ j ∈ Finset.range K, R j)) +
      (∑ j ∈ Finset.range K, U j *ᵥ (Mt (j + 1) - Mt j) - Δ • (X *ᵥ Mt K)) +
      ∑ j ∈ Finset.range K, U (j + 1) *ᵥ (Δ • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j)) := by
  -- one step: `A_{j+1} - Ũ_j A_j`
  have hstep : ∀ j < K, A (j + 1) - Ut j *ᵥ A j = Δ • S j + Δ • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j) +
      (R (j + 1) - R j) + (Mt (j + 1) - Mt j) := by
    intro j hj
    have h1 := hdec (j + 1) hj
    have h0 := hdec j hj.le
    rw [Finset.sum_range_succ] at h1
    have e : Ut j *ᵥ A j = A j + Δ • ((Θ (j + 1) * Mm) *ᵥ A j) := by
      rw [hUt j hj, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    have e2 : ((Θ j - Θ (j + 1)) * Mm) *ᵥ A j = (Θ j * Mm) *ᵥ A j - (Θ (j + 1) * Mm) *ᵥ A j := by
      rw [Matrix.sub_mul, Matrix.sub_mulVec]
    rw [e, e2]
    have hA : A (j + 1) = A 0 + Δ • (∑ i ∈ Finset.range j, ((Θ i * Mm) *ᵥ A i + S i) + ((Θ j * Mm) *ᵥ A j + S j)) + R (j + 1) + Mt (j + 1) := h1
    rw [hA]
    have h0' : A j = A 0 + Δ • ∑ i ∈ Finset.range j, ((Θ i * Mm) *ᵥ A i + S i) + R j + Mt j := h0
    have : A 0 + Δ • (∑ i ∈ Finset.range j, ((Θ i * Mm) *ᵥ A i + S i) + ((Θ j * Mm) *ᵥ A j + S j)) + R (j + 1) + Mt (j + 1) - (A j + Δ • ((Θ (j + 1) * Mm) *ᵥ A j)) =
        (A 0 + Δ • ∑ i ∈ Finset.range j, ((Θ i * Mm) *ᵥ A i + S i) + R j + Mt j - A j) + Δ • S j + Δ • ((Θ j * Mm) *ᵥ A j - (Θ (j + 1) * Mm) *ᵥ A j) + (R (j + 1) - R j) + (Mt (j + 1) - Mt j) := by
      simp only [smul_add, smul_sub]; abel
    rw [this, ← h0', sub_self, zero_add]
  -- the telescoping identity
  have htel : ∀ k ≤ K, U k *ᵥ A k = U 0 *ᵥ A 0 + ∑ j ∈ Finset.range k, U (j + 1) *ᵥ (A (j + 1) - Ut j *ᵥ A j) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        rw [Finset.sum_range_succ, ← add_assoc, ← ih (Nat.le_of_succ_le hk), Matrix.mulVec_sub, Matrix.mulVec_mulVec,
          hcomp k (Nat.lt_of_succ_le hk)]
        abel
  have hK := htel K le_rfl
  rw [hUK, Matrix.one_mulVec] at hK
  rw [hK]
  -- Abel summation for the remainder and the martingale
  have hAbelR : ∀ k ≤ K, ∑ j ∈ Finset.range k, U (j + 1) *ᵥ (R (j + 1) - R j) = U k *ᵥ R k + Δ • (X *ᵥ ∑ j ∈ Finset.range k, R j) := by
    intro k
    induction k with
    | zero => intro _; simp [hR0]
    | succ k ih =>
        intro hk
        have hk' := Nat.lt_of_succ_le hk
        rw [Finset.sum_range_succ, ih hk'.le, Finset.sum_range_succ, Matrix.mulVec_add, Matrix.mulVec_sub, smul_add]
        have := hUd k hk'
        have e : U k *ᵥ R k = U (k + 1) *ᵥ R k + Δ • (X *ᵥ R k) := by
          rw [this, Matrix.add_mulVec, Matrix.smul_mulVec]
        rw [e]
        abel
  have hAbelM : ∀ k ≤ K, ∑ j ∈ Finset.range k, U (j + 1) *ᵥ (Mt (j + 1) - Mt j) = ∑ j ∈ Finset.range k, U j *ᵥ (Mt (j + 1) - Mt j) - Δ • (X *ᵥ Mt k) := by
    intro k
    induction k with
    | zero => intro _; simp [hM0]
    | succ k ih =>
        intro hk
        have hk' := Nat.lt_of_succ_le hk
        rw [Finset.sum_range_succ, ih hk'.le, Finset.sum_range_succ]
        have := hUd k hk'
        have e : U (k + 1) *ᵥ (Mt (k + 1) - Mt k) = U k *ᵥ (Mt (k + 1) - Mt k) - Δ • (X *ᵥ (Mt (k + 1) - Mt k)) := by
          rw [eq_sub_iff_add_eq, this, Matrix.add_mulVec, Matrix.smul_mulVec]
        rw [e]
        simp only [Matrix.mulVec_sub, smul_sub]
        abel
  have hsum : ∑ j ∈ Finset.range K, U (j + 1) *ᵥ (A (j + 1) - Ut j *ᵥ A j) =
      Δ • ∑ j ∈ Finset.range K, U (j + 1) *ᵥ S j + ∑ j ∈ Finset.range K, U (j + 1) *ᵥ (Δ • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j)) +
      ∑ j ∈ Finset.range K, U (j + 1) *ᵥ (R (j + 1) - R j) + ∑ j ∈ Finset.range K, U (j + 1) *ᵥ (Mt (j + 1) - Mt j) := by
    rw [Finset.smul_sum]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hstep j (Finset.mem_range.1 hj), Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hsum, hAbelR K le_rfl, hAbelM K le_rfl, hUK, Matrix.one_mulVec]
  abel

end Algebra

/-! ## 5. The pathwise estimate of the grid walk at the last grid point (BA objects) -/

open private TwistGrid_uKer_comm from RBM3D.BA.TwistGrid

section PathBA
open scoped Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

/-- The resolvent identity `Θ_u - Θ_{u'} = (u - u') Θ_u M Θ_{u'}`. -/
theorem TwistStep_theta_diff (hr : BAReal d L g κ E m) {u u' : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hu0' : 0 ≤ u') (hu1' : u' < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m u σ₁ σ₂ - BATheta d L g E m u' σ₁ σ₂ =
      ((u : ℂ) - u') • (BATheta d L g E m u σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m u' σ₁ σ₂) := by
  have h1 := (BATheta_resolvent d L g κ E m hr u hu0 hu1 σ₁ σ₂).2
  have h2 := (BATheta_resolvent d L g κ E m hr u' hu0' hu1' σ₁ σ₂).1
  set A := BATheta d L g E m u σ₁ σ₂
  set B := BATheta d L g E m u' σ₁ σ₂
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂
  have e1 : A * B = B + (u : ℂ) • (A * Q * B) := by
    calc A * B = (1 + (u : ℂ) • (A * Q)) * B := by rw [← h1]
      _ = B + (u : ℂ) • (A * Q * B) := by rw [add_mul, one_mul, smul_mul_assoc]
  have e2 : A * B = A + (u' : ℂ) • (A * Q * B) := by
    calc A * B = A * (1 + (u' : ℂ) • (Q * B)) := by rw [← h2]
      _ = A + (u' : ℂ) • (A * Q * B) := by rw [mul_add, mul_one, mul_smul_comm, mul_assoc]
  rw [sub_smul]
  linear_combination (norm := module) e1 - e2


end PathBA

section Algebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The estimate behind the identity: all five pieces bounded; `Pr` is a matrix with `‖Pr x‖ ≤ 2 ‖x‖`; the first two pieces are bounded after applying `Pr` (they carry
the kernel loss), the other three by `2 ×` the norm of the vector. -/
theorem TwistStep_bound (Δ : ℝ) (hΔ : 0 ≤ Δ) (K : ℕ) (X Mm Pr : Matrix ι ι ℂ) (Θ U Ut : ℕ → Matrix ι ι ℂ)
    (hUK : U K = 1) (hcomp : ∀ j < K, U (j + 1) * Ut j = U j)
    (hUt : ∀ j < K, Ut j = 1 + (Δ : ℂ) • (Θ (j + 1) * Mm)) (hUd : ∀ j < K, U j = U (j + 1) + (Δ : ℂ) • X)
    (A S R Mt : ℕ → ι → ℂ) (hR0 : R 0 = 0) (hM0 : Mt 0 = 0)
    (hdec : ∀ k ≤ K, A k = A 0 + (Δ : ℂ) • ∑ j ∈ Finset.range k, ((Θ j * Mm) *ᵥ A j + S j) + R k + Mt k)
    (hPr : ∀ x : ι → ℂ, ‖Pr *ᵥ x‖ ≤ 2 * ‖x‖)
    {L0 : ℝ} {Ls : ℕ → ℝ} (hini : ‖Pr *ᵥ (U 0 *ᵥ A 0)‖ ≤ L0) (hsrc : ∀ j < K, ‖Pr *ᵥ (U (j + 1) *ᵥ S j)‖ ≤ Ls j)
    {ρ ξX m1 m2 Rr dd Ā : ℝ} (hξ : 0 ≤ ξX) (hRr : 0 ≤ Rr) (hdd : 0 ≤ dd) (hR : ∀ j ≤ K, ‖R j‖ ≤ ρ) (hX : ∀ x : ι → ℂ, ‖X *ᵥ x‖ ≤ ξX * ‖x‖)
    (hMt : ‖Mt K‖ ≤ m1) (hms : ‖∑ j ∈ Finset.range K, U j *ᵥ (Mt (j + 1) - Mt j)‖ ≤ m2)
    (hU : ∀ j ≤ K, ∀ x : ι → ℂ, ‖U j *ᵥ x‖ ≤ Rr * ‖x‖)
    (hdisc : ∀ j < K, ∀ x : ι → ℂ, ‖((Θ j - Θ (j + 1)) * Mm) *ᵥ x‖ ≤ dd * ‖x‖) (hA : ∀ j < K, ‖A j‖ ≤ Ā) :
    ‖Pr *ᵥ A K‖ ≤ L0 + Δ * ∑ j ∈ Finset.range K, Ls j + 2 * (ρ + K * Δ * (ξX * ρ) + m2 + Δ * (ξX * m1) + K * Δ * (Rr * (dd * Ā))) := by
  have hid := TwistStep_identity (Δ : ℂ) K X Mm Θ U Ut hUK hcomp hUt hUd A S R Mt hR0 hM0 hdec
  rw [hid]
  have hΔn : ∀ v : ι → ℂ, ‖(Δ : ℂ) • v‖ = Δ * ‖v‖ := fun v => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hΔ]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add]
  have key : ∀ a b c d e : ι → ℂ, ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
    intro a b c d e
    calc ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖a + b + c‖ + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
  refine (key _ _ _ _ _).trans ?_
  have h2 : ‖Pr *ᵥ ((Δ : ℂ) • ∑ j ∈ Finset.range K, U (j + 1) *ᵥ S j)‖ ≤ Δ * ∑ j ∈ Finset.range K, Ls j := by
    rw [Matrix.mulVec_smul, hΔn, Matrix.mulVec_sum]
    exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hsrc j (Finset.mem_range.1 hj))) hΔ
  have h3 : ‖Pr *ᵥ (R K + (Δ : ℂ) • (X *ᵥ ∑ j ∈ Finset.range K, R j))‖ ≤ 2 * (ρ + K * Δ * (ξX * ρ)) := by
    refine (hPr _).trans ?_
    have hRsum : ‖∑ j ∈ Finset.range K, R j‖ ≤ K * ρ := by
      calc ‖∑ j ∈ Finset.range K, R j‖ ≤ ∑ j ∈ Finset.range K, ‖R j‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range K, ρ := Finset.sum_le_sum fun j hj => hR j (Finset.mem_range.1 hj).le
        _ = K * ρ := by simp
    have h3a : ‖(Δ : ℂ) • (X *ᵥ ∑ j ∈ Finset.range K, R j)‖ ≤ K * Δ * (ξX * ρ) := by
      rw [hΔn]
      calc Δ * ‖X *ᵥ ∑ j ∈ Finset.range K, R j‖ ≤ Δ * (ξX * (K * ρ)) :=
            mul_le_mul_of_nonneg_left ((hX _).trans (mul_le_mul_of_nonneg_left hRsum hξ)) hΔ
        _ = K * Δ * (ξX * ρ) := by ring
    have := (norm_add_le (R K) ((Δ : ℂ) • (X *ᵥ ∑ j ∈ Finset.range K, R j))).trans (add_le_add (hR K le_rfl) h3a)
    linarith
  have h4 : ‖Pr *ᵥ (∑ j ∈ Finset.range K, U j *ᵥ (Mt (j + 1) - Mt j) - (Δ : ℂ) • (X *ᵥ Mt K))‖ ≤ 2 * (m2 + Δ * (ξX * m1)) := by
    refine (hPr _).trans ?_
    have h4a : ‖(Δ : ℂ) • (X *ᵥ Mt K)‖ ≤ Δ * (ξX * m1) := by
      rw [hΔn]
      exact mul_le_mul_of_nonneg_left ((hX _).trans (mul_le_mul_of_nonneg_left hMt hξ)) hΔ
    have := (norm_sub_le (∑ j ∈ Finset.range K, U j *ᵥ (Mt (j + 1) - Mt j)) ((Δ : ℂ) • (X *ᵥ Mt K))).trans (add_le_add hms h4a)
    linarith
  have h5 : ‖Pr *ᵥ ∑ j ∈ Finset.range K, U (j + 1) *ᵥ ((Δ : ℂ) • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j))‖ ≤ 2 * (K * Δ * (Rr * (dd * Ā))) := by
    refine (hPr _).trans ?_
    have h5a : ‖∑ j ∈ Finset.range K, U (j + 1) *ᵥ ((Δ : ℂ) • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j))‖ ≤ K * Δ * (Rr * (dd * Ā)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ Finset.range K, ‖U (j + 1) *ᵥ ((Δ : ℂ) • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j))‖
          ≤ ∑ j ∈ Finset.range K, Δ * (Rr * (dd * Ā)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' := Finset.mem_range.1 hj
            calc ‖U (j + 1) *ᵥ ((Δ : ℂ) • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j))‖ ≤ Rr * ‖(Δ : ℂ) • (((Θ j - Θ (j + 1)) * Mm) *ᵥ A j)‖ :=
                  hU (j + 1) hj' _
              _ = Rr * (Δ * ‖((Θ j - Θ (j + 1)) * Mm) *ᵥ A j‖) := by rw [hΔn]
              _ ≤ Rr * (Δ * (dd * Ā)) := by
                  gcongr
                  exact (hdisc j hj' _).trans (mul_le_mul_of_nonneg_left (hA j hj') hdd)
              _ = Δ * (Rr * (dd * Ā)) := by ring
        _ = K * Δ * (Rr * (dd * Ā)) := by simp; ring
    linarith
  linarith [hini, h2, h3, h4, h5]


end Algebra

section PathBA2
open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (ω : PathΩ sz)

/-- `S_j = B̃₁ + B̃₂ + Ẽ^{G̊}` at the grid state `(u_j, H_j)`, as a vector in `a`. -/
def TwistStep_S (j : ℕ) : Zd d (sz.L n) → ℂ := fun a =>
  twB1M sz lam0 E n (gridTime s τ K n j) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂ +
    twB2M sz lam0 E n (gridTime s τ K n j) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂ +
    twEGM sz lam0 E n (gridTime s τ K n j) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂

/-- `Rem_k` and `Mart_k` (canonical) as vectors in `a`. -/
def TwistStep_R (k : ℕ) : Zd d (sz.L n) → ℂ := fun a => twRem sz lam0 E s τ K n σ a c₁ c₂ k ω
def TwistStep_Mt (k : ℕ) : Zd d (sz.L n) → ℂ := fun a => twMart sz lam0 E s τ K n σ a c₁ c₂ k ω

/-- **The decomposition (i) of 4 (b) as a vector identity** (`baTwistGrid_decomp`; the drift is `Θ_j M A_j + S_j`, `twDriftM`): `A_k = A_0 + Δ Σ_{j<k} (Θ_j M A_j + S_j) + Rem_k + Mart_k`. -/
theorem TwistStep_hdec (k : ℕ) :
    twAk sz lam0 E s τ K n σ c₁ c₂ k ω = twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω +
      ((gridStep s τ K n : ℝ) : ℂ) • ∑ j ∈ Finset.range k, (((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ j ω) +
        TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j) +
      TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω k + TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω k := by
  funext a
  have h := baTwistGrid_decomp sz lam0 E s τ K n σ a c₁ c₂ k ω
  have hsum : ∑ j ∈ Finset.range k, twDriftk sz lam0 E s τ K n σ a c₁ c₂ j ω =
      ∑ j ∈ Finset.range k, ((((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ j ω) a) +
        TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j a) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [twDriftk, twDriftM, TwistStep_S, add_assoc]
    rfl
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [h, hsum]
  rfl

/-- **The exact pathwise estimate of the grid walk at the last grid point** (BA objects; the identity `TwistStep_identity` and the bound `TwistStep_bound`): for every sample `ω`
of the grid walk of `baStep2Mat sz lam0 E` over `[s, τ]`, `‖Pr A_K‖ ≤ L0 + Δ Σ_j Ls_j + 2 (ρ + ...)` given the kernel-loss bounds on the initial term and the sources
(`hini`, `hsrc`), the bounds on `Rem` (`hR`), on `Mart_K` and the `Ũ`-weighted martingale sum (`hMt`, `hms`) and the a priori bound `hA` on `A_j`. -/
theorem TwistStep_path {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0)
    (Pr : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (hPr : ∀ x : Zd d (sz.L n) → ℂ, ‖Pr *ᵥ x‖ ≤ 2 * ‖x‖)
    {L0 ρ m1 m2 Ā : ℝ} {Ls : ℕ → ℝ}
    (hini : ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n 0) (τ n) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω)‖ ≤ L0)
    (hsrc : ∀ j < K n, ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n (j + 1)) (τ n) *ᵥ TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤ Ls j)
    (hR : ∀ j ≤ K n, ‖TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω j‖ ≤ ρ)
    (hMt : ‖TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (K n)‖ ≤ m1)
    (hms : ‖∑ j ∈ Finset.range (K n), twU sz lam0 E n σ (gridTime s τ K n j) (τ n) *ᵥ
      (TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (j + 1) - TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤ m2)
    (hA : ∀ j < K n, ‖twAk sz lam0 E s τ K n σ c₁ c₂ j ω‖ ≤ Ā) :
    ‖Pr *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω‖ ≤ L0 + gridStep s τ K n * ∑ j ∈ Finset.range (K n), Ls j +
      2 * (ρ + K n * gridStep s τ K n * ((1 - τ n)⁻¹ * ρ) + m2 + gridStep s τ K n * ((1 - τ n)⁻¹ * m1) +
        K n * gridStep s τ K n * ((1 - s n) / (1 - τ n) * (gridStep s τ K n * ((1 - τ n)⁻¹) ^ 2 * Ā))) := by
  have hΔ0 : 0 ≤ gridStep s τ K n := div_nonneg (sub_nonneg.2 hsτ) (Nat.cast_nonneg _)
  have hu_succ : ∀ k : ℕ, gridTime s τ K n (k + 1) - gridTime s τ K n k = gridStep s τ K n := by
    intro k; unfold gridTime; push_cast; ring
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hfirst : gridTime s τ K n 0 = s n := by simp [gridTime]
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  have hu0 : ∀ k, k ≤ K n → 0 ≤ gridTime s τ K n k := fun k _ => by
    have := hmono (Nat.zero_le k); rw [hfirst] at this; linarith
  have hu1 : ∀ k, k ≤ K n → gridTime s τ K n k < 1 := fun k hk => by
    have := hmono hk; rw [hlast] at this; linarith
  have hus : ∀ k, k ≤ K n → s n ≤ gridTime s τ K n k := fun k _ => by
    have := hmono (Nat.zero_le k); rw [hfirst] at this; exact this
  have huτ : ∀ k, k ≤ K n → gridTime s τ K n k ≤ τ n := fun k hk => by
    have := hmono hk; rw [hlast] at this; exact this
  have hτ0 : 0 ≤ τ n := hs.trans hsτ
  have hcomm : ∀ t : ℝ, 0 ≤ t → t < 1 → BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) *
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t (σ 0) (σ 1) =
      BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) t (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) :=
    fun t ht0 ht1 => (TwistGrid_uKer_comm hr ht0 ht1 (σ 0) (σ 1)).eq
  set Mm := BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1) with hMm
  set Θ : ℕ → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := fun j =>
    BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) with hΘ
  set X : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := Mm * BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (τ n) (σ 0) (σ 1) with hXdef
  have hUK : twU sz lam0 E n σ (gridTime s τ K n (K n)) (τ n) = 1 := by
    rw [hlast]; exact BAuKer_self hr hτ0 hτ1 (σ 0) (σ 1)
  have hcomp : ∀ j < K n, twU sz lam0 E n σ (gridTime s τ K n (j + 1)) (τ n) * twU sz lam0 E n σ (gridTime s τ K n j) (gridTime s τ K n (j + 1)) =
      twU sz lam0 E n σ (gridTime s τ K n j) (τ n) := fun j hj =>
    BAuKer_comp hr (hu0 (j + 1) hj) (hu1 (j + 1) hj) hτ0 hτ1 (σ 0) (σ 1)
  have hUt : ∀ j < K n, twU sz lam0 E n σ (gridTime s τ K n j) (gridTime s τ K n (j + 1)) = 1 + ((gridStep s τ K n : ℝ) : ℂ) • (Θ (j + 1) * Mm) := by
    intro j hj
    unfold twU
    rw [BAuKer_eq_one_add hr (hu0 (j + 1) hj) (hu1 (j + 1) hj) (σ 0) (σ 1), hcomm _ (hu0 (j + 1) hj) (hu1 (j + 1) hj)]
    have : ((gridTime s τ K n (j + 1) : ℝ) : ℂ) - (gridTime s τ K n j : ℝ) = ((gridStep s τ K n : ℝ) : ℂ) := by
      exact_mod_cast hu_succ j
    rw [this]
  have hUd : ∀ j < K n, twU sz lam0 E n σ (gridTime s τ K n j) (τ n) = twU sz lam0 E n σ (gridTime s τ K n (j + 1)) (τ n) + ((gridStep s τ K n : ℝ) : ℂ) • X := by
    intro j hj
    unfold twU
    rw [BAuKer_eq_one_add hr hτ0 hτ1 (σ 0) (σ 1), BAuKer_eq_one_add hr hτ0 hτ1 (σ 0) (σ 1)]
    have : ((τ n : ℝ) : ℂ) - (gridTime s τ K n j : ℝ) = (((τ n : ℝ) : ℂ) - (gridTime s τ K n (j + 1) : ℝ)) + ((gridStep s τ K n : ℝ) : ℂ) := by
      have h := hu_succ j
      have h' : ((gridTime s τ K n (j + 1) : ℝ) : ℂ) - (gridTime s τ K n j : ℝ) = ((gridStep s τ K n : ℝ) : ℂ) := by exact_mod_cast h
      rw [← h']; ring
    rw [this, add_smul]
    simp only [hXdef]
    abel
  have hR0 : TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω 0 = 0 := by
    funext a; simp [TwistStep_R, twRem]
  have hM0 : TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω 0 = 0 := by
    funext a; simp [TwistStep_Mt, twMart]
  have hdec : ∀ k ≤ K n, twAk sz lam0 E s τ K n σ c₁ c₂ k ω = twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω +
      ((gridStep s τ K n : ℝ) : ℂ) • ∑ j ∈ Finset.range k, ((Θ j * Mm) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ j ω + TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j) +
      TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω k + TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω k :=
    fun k _ => TwistStep_hdec sz lam0 E s τ K n σ c₁ c₂ ω k
  have h1τ : 0 < 1 - τ n := by linarith
  have hQ : ‖Mm‖ ≤ 1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have hΘn : ∀ j ≤ K n, ‖Θ j‖ ≤ (1 - gridTime s τ K n j)⁻¹ := fun j hj =>
    EKPins_norm_Theta_le hr (hu0 j hj) (hu1 j hj) (σ 0) (σ 1)
  have hΘτ : ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (τ n) (σ 0) (σ 1)‖ ≤ (1 - τ n)⁻¹ :=
    EKPins_norm_Theta_le hr hτ0 hτ1 (σ 0) (σ 1)
  have hXn : ‖X‖ ≤ (1 - τ n)⁻¹ := by
    refine (norm_mul_le _ _).trans ?_
    calc ‖Mm‖ * ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (τ n) (σ 0) (σ 1)‖ ≤ 1 * (1 - τ n)⁻¹ :=
          mul_le_mul hQ hΘτ (norm_nonneg _) zero_le_one
      _ = (1 - τ n)⁻¹ := one_mul _
  have hξ : 0 ≤ (1 - τ n)⁻¹ := inv_nonneg.2 h1τ.le
  have hX : ∀ x : Zd d (sz.L n) → ℂ, ‖X *ᵥ x‖ ≤ (1 - τ n)⁻¹ * ‖x‖ := fun x =>
    (Matrix.linfty_opNorm_mulVec X x).trans (mul_le_mul_of_nonneg_right hXn (norm_nonneg _))
  have hRr : 0 ≤ (1 - s n) / (1 - τ n) := div_nonneg (by linarith) h1τ.le
  have hU : ∀ j ≤ K n, ∀ x : Zd d (sz.L n) → ℂ, ‖twU sz lam0 E n σ (gridTime s τ K n j) (τ n) *ᵥ x‖ ≤ (1 - s n) / (1 - τ n) * ‖x‖ := by
    intro j hj x
    refine (Matrix.linfty_opNorm_mulVec _ x).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact (EKPins_norm_uKer_le hr (hu0 j hj) (huτ j hj) hτ1 (σ 0) (σ 1)).trans
      (div_le_div_of_nonneg_right (by linarith [hus j hj]) h1τ.le)
  have hdn : ∀ j < K n, ‖(Θ j - Θ (j + 1)) * Mm‖ ≤ gridStep s τ K n * ((1 - τ n)⁻¹) ^ 2 := by
    intro j hj
    have hd := TwistStep_theta_diff hr (hu0 j hj.le) (hu1 j hj.le) (hu0 (j + 1) hj) (hu1 (j + 1) hj) (σ 0) (σ 1)
    have e1 : (Θ j - Θ (j + 1)) * Mm = (-((gridStep s τ K n : ℝ) : ℂ)) • (Θ j * Mm * Θ (j + 1) * Mm) := by
      have h' : ((gridTime s τ K n j : ℝ) : ℂ) - (gridTime s τ K n (j + 1) : ℝ) = -((gridStep s τ K n : ℝ) : ℂ) := by
        have := hu_succ j
        have h'' : ((gridTime s τ K n (j + 1) : ℝ) : ℂ) - (gridTime s τ K n j : ℝ) = ((gridStep s τ K n : ℝ) : ℂ) := by exact_mod_cast this
        rw [← h'']; ring
      show (BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) -
        BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n (j + 1)) (σ 0) (σ 1)) * Mm = _
      rw [hd, h', smul_mul_assoc, mul_assoc (Θ j * Mm) (Θ (j + 1)) Mm]
    rw [e1, norm_smul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hΔ0]
    have hb : ‖Θ j * Mm * Θ (j + 1) * Mm‖ ≤ ((1 - τ n)⁻¹) ^ 2 := by
      have h1 : ‖Θ j‖ ≤ (1 - τ n)⁻¹ := (hΘn j hj.le).trans (inv_anti₀ h1τ (by linarith [huτ j hj.le]))
      have h2 : ‖Θ (j + 1)‖ ≤ (1 - τ n)⁻¹ := (hΘn (j + 1) hj).trans (inv_anti₀ h1τ (by linarith [huτ (j + 1) hj]))
      calc ‖Θ j * Mm * Θ (j + 1) * Mm‖ ≤ ‖Θ j‖ * ‖Mm‖ * ‖Θ (j + 1)‖ * ‖Mm‖ := by
            refine (norm_mul_le _ _).trans ?_
            gcongr
            refine (norm_mul_le _ _).trans ?_
            gcongr
            exact norm_mul_le _ _
        _ ≤ (1 - τ n)⁻¹ * 1 * (1 - τ n)⁻¹ * 1 := by gcongr
        _ = ((1 - τ n)⁻¹) ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left hb hΔ0
  have hdisc : ∀ j < K n, ∀ x : Zd d (sz.L n) → ℂ, ‖((Θ j - Θ (j + 1)) * Mm) *ᵥ x‖ ≤ gridStep s τ K n * ((1 - τ n)⁻¹) ^ 2 * ‖x‖ := fun j hj x =>
    (Matrix.linfty_opNorm_mulVec _ x).trans (mul_le_mul_of_nonneg_right (hdn j hj) (norm_nonneg _))
  have hdd : 0 ≤ gridStep s τ K n * ((1 - τ n)⁻¹) ^ 2 := by positivity
  exact TwistStep_bound (gridStep s τ K n) hΔ0 (K n) X Mm Pr Θ
    (fun j => twU sz lam0 E n σ (gridTime s τ K n j) (τ n)) (fun j => twU sz lam0 E n σ (gridTime s τ K n j) (gridTime s τ K n (j + 1)))
    hUK hcomp hUt hUd (fun j => twAk sz lam0 E s τ K n σ c₁ c₂ j ω) (TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω)
    (TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω) (TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω) hR0 hM0 hdec hPr hini hsrc hξ hRr hdd hR hX hMt hms hU hdisc hA


/-- **`Mart_K` from the decomposition** (so that the tail pin (iii) is not needed): `Mart_K = A_K - A_0 - Δ Σ_j (Θ_j M A_j + S_j) - Rem_K`, `‖Θ_j M‖ ≤ (1 - τ)⁻¹`. -/
theorem TwistStep_mt_bound {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0) {Ā b0 ρ Sm : ℝ}
    (hA0 : ‖twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω‖ ≤ b0) (hAK : ‖twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω‖ ≤ Ā)
    (hAj : ∀ j < K n, ‖twAk sz lam0 E s τ K n σ c₁ c₂ j ω‖ ≤ Ā) (hS : ∀ j < K n, ‖TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j‖ ≤ Sm)
    (hR : ‖TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω (K n)‖ ≤ ρ) :
    ‖TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (K n)‖ ≤
      Ā + b0 + (K n * gridStep s τ K n) * ((1 - τ n)⁻¹ * Ā + Sm) + ρ := by
  have hΔ0 : 0 ≤ gridStep s τ K n := div_nonneg (sub_nonneg.2 hsτ) (Nat.cast_nonneg _)
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hfirst : gridTime s τ K n 0 = s n := by simp [gridTime]
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  have hu0 : ∀ k, k ≤ K n → 0 ≤ gridTime s τ K n k := fun k _ => by
    have := hmono (Nat.zero_le k); rw [hfirst] at this; linarith
  have hu1 : ∀ k, k ≤ K n → gridTime s τ K n k < 1 := fun k hk => by
    have := hmono hk; rw [hlast] at this; linarith
  have huτ : ∀ k, k ≤ K n → gridTime s τ K n k ≤ τ n := fun k hk => by
    have := hmono hk; rw [hlast] at this; exact this
  have h1τ : 0 < 1 - τ n := by linarith
  have hQ : ‖BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)‖ ≤ 1 := EKPins_norm_Q_le hr (σ 0) (σ 1)
  have hd := TwistStep_hdec sz lam0 E s τ K n σ c₁ c₂ ω (K n)
  have hMt : TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (K n) = twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω - twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω -
      ((gridStep s τ K n : ℝ) : ℂ) • ∑ j ∈ Finset.range (K n), (((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ j ω) +
        TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j) - TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω (K n) := by
    rw [hd]; abel
  rw [hMt]
  have hsum : ‖∑ j ∈ Finset.range (K n), (((BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) *
        BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ j ω) +
        TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤ K n * ((1 - τ n)⁻¹ * Ā + Sm) := by
    refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.range (K n), ((1 - τ n)⁻¹ * Ā + Sm) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := Finset.mem_range.1 hj
          refine (norm_add_le _ _).trans (add_le_add ?_ (hS j hj'))
          refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
          have hΘ := EKPins_norm_Theta_le hr (hu0 j hj'.le) (hu1 j hj'.le) (σ 0) (σ 1)
          have hΘ' : ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1)‖ ≤ (1 - τ n)⁻¹ :=
            hΘ.trans (inv_anti₀ h1τ (by linarith [huτ j hj'.le]))
          have hΘM : ‖BATheta d (sz.L n) (lam0 n) (E n) (BAmF sz lam0 E n) (gridTime s τ K n j) (σ 0) (σ 1) *
              BAMss d (sz.L n) (BAMB d (sz.L n) (lam0 n) (E n : ℂ) (BAmF sz lam0 E n)) (σ 0) (σ 1)‖ ≤ (1 - τ n)⁻¹ := by
            refine (norm_mul_le _ _).trans ?_
            calc _ ≤ (1 - τ n)⁻¹ * 1 := mul_le_mul hΘ' hQ (norm_nonneg _) (inv_nonneg.2 h1τ.le)
              _ = _ := mul_one _
          exact mul_le_mul hΘM (hAj j hj') (norm_nonneg _) (inv_nonneg.2 h1τ.le)
      _ = _ := by simp; ring
  have hΔn : ∀ v : Zd d (sz.L n) → ℂ, ‖((gridStep s τ K n : ℝ) : ℂ) • v‖ = gridStep s τ K n * ‖v‖ := fun v => by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hΔ0]
  calc _ ≤ ‖twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω - twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω - ((gridStep s τ K n : ℝ) : ℂ) • ∑ j ∈ Finset.range (K n), _‖ +
        ‖TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω (K n)‖ := norm_sub_le _ _
    _ ≤ (‖twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω - twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω‖ + ‖((gridStep s τ K n : ℝ) : ℂ) • ∑ j ∈ Finset.range (K n), _‖) + ρ := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ ((Ā + b0) + gridStep s τ K n * (K n * ((1 - τ n)⁻¹ * Ā + Sm))) + ρ := by
        gcongr
        · exact (norm_sub_le _ _).trans (add_le_add hAK hA0)
        · rw [hΔn]; exact mul_le_mul_of_nonneg_left hsum hΔ0
    _ = Ā + b0 + (K n * gridStep s τ K n) * ((1 - τ n)⁻¹ * Ā + Sm) + ρ := by ring

end PathBA2

/-! ## 6. Analytic lemmas: the logarithmic sum, the transport from the model to the grid walk, measurability, the weighted quadratic variation -/

/-- The telescoping log bound: `Σ_{j<K} Δ/(1 - u_j) ≤ log((1 - s)/(1 - τ))` on the grid `u_j = s + jΔ`, `Δ = (τ - s)/K`, `τ < 1`
(`Δ/x ≤ log(x/(x - Δ))`). -/
theorem TwistStep_log_sum (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hK : K n ≠ 0) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) :
    ∑ j ∈ Finset.range (K n), gridStep s τ K n * (1 - gridTime s τ K n j)⁻¹ ≤ Real.log ((1 - s n) / (1 - τ n)) := by
  have hΔ0 : 0 ≤ gridStep s τ K n := div_nonneg (sub_nonneg.2 hsτ) (Nat.cast_nonneg _)
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hfirst : gridTime s τ K n 0 = s n := by simp [gridTime]
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  have hu1 : ∀ k, k ≤ K n → gridTime s τ K n k < 1 := fun k hk => by
    have := hmono hk; rw [hlast] at this; linarith
  have hsucc : ∀ k : ℕ, gridTime s τ K n (k + 1) = gridTime s τ K n k + gridStep s τ K n := by
    intro k; unfold gridTime; push_cast; ring
  have hpt : ∀ j ∈ Finset.range (K n), gridStep s τ K n * (1 - gridTime s τ K n j)⁻¹ ≤
      Real.log (1 - gridTime s τ K n j) - Real.log (1 - gridTime s τ K n (j + 1)) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hx : 0 < 1 - gridTime s τ K n j := by linarith [hu1 j hj'.le]
    have hy : 0 < 1 - gridTime s τ K n (j + 1) := by linarith [hu1 (j + 1) hj']
    have hxy : 1 - gridTime s τ K n (j + 1) = (1 - gridTime s τ K n j) - gridStep s τ K n := by rw [hsucc]; ring
    have hlog := Real.log_le_sub_one_of_pos (div_pos hy hx)
    rw [Real.log_div hy.ne' hx.ne'] at hlog
    have : (1 - gridTime s τ K n (j + 1)) / (1 - gridTime s τ K n j) - 1 = -(gridStep s τ K n * (1 - gridTime s τ K n j)⁻¹) := by
      rw [hxy]; field_simp; ring
    linarith
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_range_sub' (fun j => Real.log (1 - gridTime s τ K n j)), hfirst, hlast,
    ← Real.log_div (by linarith) (by linarith)]


/-- **Model to grid walk at all grid times** (a wrapper of `ST_grid_whp_of_sections` for `PrecL` over `TimeIcc s t × V`, `[s, τ] ⊆ [s, t]`): the grid walk of
`sz.withLam 0` over `[s, τ]` satisfies `F ≤ N^δ Zb` at every grid index `≤ K_n` and every label w.h.p. -/
theorem TwistStep_grid_whp {d : ℕ} (sz : Sizes d) (s t τ : ℕ → ℝ) (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (hK : ∀ n, K n ≠ 0)
    {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card (V n) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) (Zb : ∀ n, V n → ℝ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u))
    (h : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × V n)
      (fun n p ω => F n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω)) (fun n p _ => Zb n p.2 (p.1 : ℝ)))
    {δ : ℝ} (hδ : 0 < δ) :
    Gauss.HighProbAt (pathP (sz.withLam 0)) sz.size (fun n => {ω | ∀ j ∈ Finset.range (K n + 1), ∀ v : V n,
      F n v (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) ≤ ((sz.size n : ℕ) : ℝ) ^ δ * Zb n v (gridTime s τ K n j)}) := by
  refine (Sizes.ST_grid_whp_of_sections (sz.withLam 0) s τ K hs hsτ hK hC0 hcard F (fun n v u _ => Zb n v u) hF
    (fun _ _ _ => measurable_const) δ hδ ?_)
  intro tt
  exact StochDomAt.precomp_param h (fun n v => (⟨((tt n : ℝ)), (tt n).2.1, (tt n).2.2.trans (hτt n)⟩, v))


open private TwistGridTail_measurable_twChg TwistGridTail_measurable_twL2M TwistGridTail_measurable_twEEM from RBM3D.BA.TwistGridTail

section Meas

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

theorem TwistStep_measurable_twL3M (u : ℝ) (σ : Fin 3 → Bool) (a₁ a₂ c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twL3M sz lam0 E n u H σ a₁ a₂ c₁ c₂) := by
  unfold twL3M
  refine Measurable.const_mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun w _ => ?_) _
  exact ((TwistGridTail_measurable_twChg sz lam0 E n u (σ 0) (twShift n c₂ w) x).mul
    (TwistGridTail_measurable_twChg sz lam0 E n u (σ 1) x y)).mul (TwistGridTail_measurable_twChg sz lam0 E n u (σ 2) y w)

theorem TwistStep_measurable_LM (u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => (baStep2Mat sz lam0 E).LM n u H σ a) :=
  walk_measurable_loopFine d (sz.L n) (sz.W n) (ztOf (BAmF sz lam0 E n) (E n) u) σ a

theorem TwistStep_measurable_twEGM (u : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twEGM sz lam0 E n u H σ a c₁ c₂) := by
  unfold twEGM
  simp only []
  refine Measurable.const_mul (Finset.measurable_sum _ fun a' _ => ?_) _
  refine Measurable.add (Measurable.mul ?_ (TwistStep_measurable_twL3M sz lam0 E n u _ _ _ _ _)) (Measurable.mul ?_ (TwistStep_measurable_twL3M sz lam0 E n u _ _ _ _ _))
  · exact (TwistStep_measurable_LM sz lam0 E n u _ _).sub_const _
  · exact (TwistStep_measurable_LM sz lam0 E n u _ _).sub_const _

theorem TwistStep_measurable_twB1M (u : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twB1M sz lam0 E n u H σ a c₁ c₂) := by
  unfold twB1M
  refine Measurable.const_mul (Finset.measurable_sum _ fun b _ => ?_) _
  exact measurable_const.mul ((TwistStep_measurable_LM sz lam0 E n u _ _).sub_const _)

theorem TwistStep_measurable_twB2M (u : ℝ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => twB2M sz lam0 E n u H σ a c₁ c₂) := by
  unfold twB2M
  refine Measurable.const_mul (Finset.measurable_sum _ fun b _ => ?_) _
  exact ((TwistGridTail_measurable_twL2M sz lam0 E n u σ b c₁ c₂).sub_const _).mul ((TwistStep_measurable_LM sz lam0 E n u _ _).sub_const _)

end Meas


open private TwistQV_cs_weighted TwistQV_cs_diag from RBM3D.BA.TwistQV

section QV

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- Cauchy-Schwarz for the quadratic variation at a grid state (the matrix-argument twin of the private `TwistQV_cs`, `BA/TwistQV.lean:1351`; `S = 1` at the BA carrier):
`|(Ẽ⊗Ẽ)(b,b')|² ≤ (Ẽ⊗Ẽ)(b,b) (Ẽ⊗Ẽ)(b',b')`. -/
theorem TwistStep_cs_twEEM (u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (b b' c₁ c₂ : Zd d (sz.L n)) :
    ‖twEEM sz lam0 E n u H σ b b' c₁ c₂‖ ≤ √(‖twEEM sz lam0 E n u H σ b b c₁ c₂‖ * ‖twEEM sz lam0 E n u H σ b' b' c₁ c₂‖) := by
  have hS1 : ∀ a a' : Zd d (sz.L n), (baFM sz lam0 E).S n a a' = if a = a' then 1 else 0 := fun a a' => by
    show (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a a' = _
    rw [Matrix.one_apply]
  set ρ : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → ℝ := fun p =>
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if (split d (sz.L n) (sz.W n) p.1).1 = (split d (sz.L n) (sz.W n) p.2).1 then 1 else 0) with hρd
  have hρ : ∀ p, 0 ≤ ρ p := fun p => by
    rw [hρd]; dsimp only; split_ifs <;> positivity
  have hexp : ∀ b₁ b₂ : Zd d (sz.L n), twEEM sz lam0 E n u H σ b₁ b₂ c₁ c₂ =
      ∑ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), (ρ p : ℂ) *
        (twDerM sz lam0 E n u H σ b₁ c₁ c₂ p.1 p.2 * (starRingEnd ℂ) (twDerM sz lam0 E n u H σ b₂ c₁ c₂ p.1 p.2)) := by
    intro b₁ b₂
    unfold twEEM
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [hS1, hρd]
    push_cast
    split_ifs <;> simp
  rw [hexp b b', hexp b b, hexp b' b']
  have h1 := TwistQV_cs_weighted ρ hρ (fun p => twDerM sz lam0 E n u H σ b c₁ c₂ p.1 p.2) (fun p => twDerM sz lam0 E n u H σ b' c₁ c₂ p.1 p.2)
  rw [TwistQV_cs_diag ρ hρ (fun p => twDerM sz lam0 E n u H σ b c₁ c₂ p.1 p.2),
    TwistQV_cs_diag ρ hρ (fun p => twDerM sz lam0 E n u H σ b' c₁ c₂ p.1 p.2),
    Real.sqrt_mul (Finset.sum_nonneg fun p _ => mul_nonneg (hρ p) (sq_nonneg _))]
  exact h1

/-- The `Ũ`-weighted quadratic variation: `|((Ũ ⊗ Ũ^{σ̄}) ∘ (Ẽ⊗Ẽ))(a,a)| ≤ R² Q` if `Σ_b |Ũ(a,b)| ≤ R`, `Σ_b |Ũ^{σ̄}(a,b)| ≤ R` and `|(Ẽ⊗Ẽ)(b,b)| ≤ Q`. -/
theorem TwistStep_EEU_le (v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n))
    {Q Rv : ℝ} (hQ : ∀ b, ‖twEEM sz lam0 E n v H σ b b c₁ c₂‖ ≤ Q) (hQ0 : 0 ≤ Q)
    (hU1 : ∑ b, ‖twU sz lam0 E n σ v w a b‖ ≤ Rv) (hU2 : ∑ b, ‖twU sz lam0 E n (fun i => !σ i) v w a b‖ ≤ Rv) :
    ‖twEEUM sz lam0 E n v w H σ a c₁ c₂‖ ≤ Rv * Rv * Q := by
  have hb : ∀ b b', ‖twEEM sz lam0 E n v H σ b b' c₁ c₂‖ ≤ Q := fun b b' =>
    (TwistStep_cs_twEEM sz lam0 E n v H σ b b' c₁ c₂).trans (by
      calc √(‖twEEM sz lam0 E n v H σ b b c₁ c₂‖ * ‖twEEM sz lam0 E n v H σ b' b' c₁ c₂‖) ≤ √(Q * Q) :=
            Real.sqrt_le_sqrt (mul_le_mul (hQ b) (hQ b') (norm_nonneg _) hQ0)
        _ = Q := Real.sqrt_mul_self hQ0)
  unfold twEEUM
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖∑ b', twU sz lam0 E n σ v w a b * twU sz lam0 E n (fun i => !σ i) v w a b' * twEEM sz lam0 E n v H σ b b' c₁ c₂‖
      ≤ ∑ b, ∑ b', ‖twU sz lam0 E n σ v w a b‖ * ‖twU sz lam0 E n (fun i => !σ i) v w a b'‖ * Q := by
        refine Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b' _ => ?_)
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hb b b') (by positivity)
    _ = (∑ b, ‖twU sz lam0 E n σ v w a b‖) * ((∑ b', ‖twU sz lam0 E n (fun i => !σ i) v w a b'‖) * Q) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring
    _ ≤ Rv * (Rv * Q) := by
        refine mul_le_mul hU1 (mul_le_mul_of_nonneg_right hU2 hQ0) (by positivity) ((Finset.sum_nonneg fun _ _ => norm_nonneg _).trans hU1)
    _ = Rv * Rv * Q := by ring

end QV

/-! ## 7. The a priori pathwise level and `B̃₂` at a deterministic level -/

open private TwistKer2_Z_crude TwistKer2_eta_inv_le TwistKer2_Bctl_rpow_ge from RBM3D.BA.TwistKer2

/-- **The a priori pathwise level** `‖Z_v‖ ≤ Ξ₀ B_v^{3/2}`, `Ξ₀ = 2 (2/κ)² N⁴`, for every sample and every `v ∈ [0, T₀]` (`‖Z‖ ≤ 2 η⁻²`, `η⁻¹ ≤ (2/κ) N`, `B^{3/2} ≥ N⁻²`). -/
theorem TwistStep_zcrude {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    {v : ℝ} (hv0 : 0 ≤ v) (hvT : v ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖ ≤
      (2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4) * sz.Bctl n v ^ (3 / 2 : ℝ) := by
  have hv1 : v < 1 := hvT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have h1 := TwistKer2_Z_crude hκ hflow n hv0 hvT ω σ a c₁ c₂
  have h2 := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have h3 := TwistKer2_Bctl_rpow_ge (sz := sz) n hv0 hv1 (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hη0 : 0 ≤ ((baFMz sz z).eta n v)⁻¹ := inv_nonneg.2 (by
    have := EMn2BA_mF_data sz hflow n
    have h1v : 0 < 1 - v := by linarith
    show 0 ≤ (1 - v) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im
    exact mul_nonneg h1v.le (by linarith [this.1]))
  have hc : 0 ≤ 2 / κ := by positivity
  calc _ ≤ 2 * (((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹) := h1
    _ ≤ 2 * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ((2 / κ) * ((sz.size n : ℕ) : ℝ))) := by gcongr
    _ = (2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4) * (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ := by
        have : ((sz.size n : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

/-- **`B̃₂` at a deterministic level** (the passage of design (a) row 14): the pathwise level `Ξ̃` of `BATwistSrc4` is `N^{τ/2} Ξ_n` on the good event of the `≺`-bootstrap hypothesis at `(τ/2, D + 1)` and the
a priori level `Ξ₀` off it (`TwistStep_zcrude`), so `‖B̃₂‖ ≺ Ξ_n η⁻¹ B^{3/2 + 1/6}` with a deterministic `Ξ_n`. -/
theorem TwistStep_src4_det {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (h4 : ∀ γ : ℝ, 1 ≤ γ → γ ≤ 2 → ∀ Ξ' : ℕ → sz.SeqΩ → ℝ, (∀ n ω, 1 ≤ Ξ' n ω) →
      (∀ n ω (v : ℝ) σ a c₁ c₂, s n ≤ v → v ≤ t n → ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ Ξ' n ω * sz.Bctl n v ^ γ) →
      twSrc (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖) Ξ' (γ + 1 / 6))
    (Ξ : ℕ → ℝ) (hΞ : ∀ n, 1 ≤ Ξ n)
    (hB : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => ‖twL2' (baFMz sz z) n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖)
      (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ))) :
    twSrc (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖) (fun n _ => Ξ n) (3 / 2 + 1 / 6) := by
  classical
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hκ1 : κ ≤ 1 := by have := EMn2BA_mF_data sz hflow 0; linarith [this.1, this.2]
  have hΞ0 : ∀ n : ℕ, (1 : ℝ) ≤ 2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4 := fun n => by
    have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have h4N : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 4 := one_le_pow₀ hN
    have h2k : (1 : ℝ) ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith
    nlinarith [one_le_pow₀ (n := 2) h2k]
  intro τ hτ D hD
  have hτ2 : 0 < τ / 2 := half_pos hτ
  set ξB : ∀ n, (TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) → sz.SeqΩ → ℝ :=
    fun n p ω => ‖twL2' (baFMz sz z) n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 - twK (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2‖ with hξB
  set ζB : ∀ n, (TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) → sz.SeqΩ → ℝ :=
    fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ) with hζB
  let Ξt : ℕ → sz.SeqΩ → ℝ := fun n ω => if ω ∈ badSetAt sz.size ξB ζB (τ / 2) n then 2 * (2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 4 else ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Ξ n
  have hNpow : ∀ n : ℕ, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := fun n =>
    Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hτ2.le
  have hΞt1 : ∀ n ω, 1 ≤ Ξt n ω := fun n ω => by
    simp only [Ξt]
    split_ifs
    · exact hΞ0 n
    · nlinarith [hNpow n, hΞ n]
  have hΞtb : ∀ n ω (v : ℝ) σ a c₁ c₂, s n ≤ v → v ≤ t n →
      ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ Ξt n ω * sz.Bctl n v ^ (3 / 2 : ℝ) := by
    intro n ω v σ a c₁ c₂ hv1 hv2
    simp only [Ξt]
    split_ifs with hω
    · exact TwistStep_zcrude hκ hε hflow n ((hs n).trans hv1) (hv2.trans (htT n)) ω σ a c₁ c₂
    · simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hω
      have := hω (⟨v, hv1, hv2⟩, σ, a, c₁, c₂)
      simp only [hξB, hζB] at this
      calc _ ≤ _ := this
        _ = _ := by ring
  have h4' := h4 (3 / 2) (by norm_num) (by norm_num) Ξt hΞt1 hΞtb
  filter_upwards [h4' (τ / 2) hτ2 (D + 1) (by linarith), hB (τ / 2) hτ2 (D + 1) (by linarith),
    hsize.eventually (eventually_two_mul_rpow_le D)] with n hn4 hnB h2N
  have hp : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc Sizes.seqP (sz.withLam 0) (badSetAt sz.size _ _ τ n) ≤ Sizes.seqP (sz.withLam 0) (badSetAt sz.size _ _ (τ / 2) n ∪ badSetAt sz.size ξB ζB (τ / 2) n) := by
        refine measure_mono ?_
        intro ω hω
        obtain ⟨p, hp'⟩ := hω
        by_cases hωG : ω ∉ badSetAt sz.size ξB ζB (τ / 2) n
        · left
          refine ⟨p, ?_⟩
          have hΞeq : Ξt n ω = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Ξ n := ite_eq_right_of_eq_false _ _ (eq_false hωG)
          show ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Ξt n ω * (((baFMz sz z).eta n (p.1 : ℝ))⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 + 1 / 6 : ℝ))) < _
          rw [hΞeq]
          have h3 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * Ξ n * (((baFMz sz z).eta n (p.1 : ℝ))⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 + 1 / 6 : ℝ))) =
              ((sz.size n : ℕ) : ℝ) ^ τ * (Ξ n * (((baFMz sz z).eta n (p.1 : ℝ))⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 + 1 / 6 : ℝ))) := by
            have := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
            calc _ = (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) * (Ξ n * (((baFMz sz z).eta n (p.1 : ℝ))⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 + 1 / 6 : ℝ))) := by ring
              _ = _ := by rw [this]
          rw [h3]
          exact hp'
        · right
          exact not_not.1 hωG
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) + ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := add_le_add hn4 hnB
    _ = ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := by rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ _ := ENNReal.ofReal_le_ofReal h2N

/-! ## 8. The sums along the grid: `Σ_j Δ η_j⁻¹`, the weighted quadratic variation, the row sums of `Ũ` -/

section P12
open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `Δ Σ_j η_j⁻¹ ≤ (Im m)⁻¹ log((1-s)/(1-τ))` for `η_j = (1 - u_j) Im m`. -/
theorem TwistStep_eta_sum (hK : K n ≠ 0) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) {im : ℝ} (him : 0 < im) :
    gridStep s τ K n * ∑ j ∈ Finset.range (K n), ((1 - gridTime s τ K n j) * im)⁻¹ ≤ im⁻¹ * Real.log ((1 - s n) / (1 - τ n)) := by
  have h := TwistStep_log_sum s τ K n hK hsτ hτ1
  have e : gridStep s τ K n * ∑ j ∈ Finset.range (K n), ((1 - gridTime s τ K n j) * im)⁻¹ =
      im⁻¹ * ∑ j ∈ Finset.range (K n), gridStep s τ K n * (1 - gridTime s τ K n j)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_inv]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 him.le)

/-- The row sums of the evolution kernel: `Σ_b |Ũ_{v,w}(a,b)| ≤ (1-v)/(1-w)`. -/
theorem TwistStep_rowsum {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1)
    (σ : Fin 2 → Bool) (a : Zd d (sz.L n)) : ∑ b, ‖twU sz lam0 E n σ v w a b‖ ≤ (1 - v) / (1 - w) :=
  (sum_norm_row_le _ a).trans (EKPins_norm_uKer_le hr hv hvw hw (σ 0) (σ 1))

/-- **The weighted quadratic variation sum** (the right side of clause (iv) of 4 (b) at `k = K`): `Σ_j Δ |twEEUk_j| ≤ R² N^δ β^{13/4} (Im m)⁻¹ log R`. -/
theorem TwistStep_S2 {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n)) (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0)
    (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (ω : PathΩ sz) (a : Zd d (sz.L n)) {Nδ β R im : ℝ} (him : 0 < im) (hNδ : 0 ≤ Nδ)
    (hβ : ∀ j ≤ K n, sz.Bctl n (gridTime s τ K n j) ≤ β) (hR : (1 - s n) / (1 - τ n) ≤ R)
    (hqv : ∀ j < K n, ∀ b, ‖twEEM sz lam0 E n (gridTime s τ K n j) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ b b c₁ c₂‖ ≤
      Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ)) :
    ∑ j ∈ Finset.range (K n), gridStep s τ K n * ‖twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω‖ ≤
      R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (im⁻¹ * Real.log ((1 - s n) / (1 - τ n))) := by
  have hΔ0 : 0 ≤ gridStep s τ K n := div_nonneg (sub_nonneg.2 hsτ) (Nat.cast_nonneg _)
  have hmono : ∀ {i i' : ℕ}, i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hfirst : gridTime s τ K n 0 = s n := by simp [gridTime]
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  have hu0 : ∀ k, k ≤ K n → 0 ≤ gridTime s τ K n k := fun k _ => by
    have := hmono (Nat.zero_le k); rw [hfirst] at this; linarith
  have hus : ∀ k, k ≤ K n → s n ≤ gridTime s τ K n k := fun k _ => by
    have := hmono (Nat.zero_le k); rw [hfirst] at this; exact this
  have huτ : ∀ k, k ≤ K n → gridTime s τ K n k ≤ τ n := fun k hk => by
    have := hmono hk; rw [hlast] at this; exact this
  have h1τ : 0 < 1 - τ n := by linarith
  have hR1 : 0 ≤ R := (div_nonneg (by linarith) h1τ.le).trans hR
  have hβ0 : 0 ≤ β := (le_trans (le_of_lt (st_Bctl_pos sz (n := n) hτ1)) (by simpa [hlast] using hβ (K n) le_rfl))
  have hpt : ∀ j ∈ Finset.range (K n), gridStep s τ K n * ‖twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω‖ ≤
      R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (gridStep s τ K n * ((1 - gridTime s τ K n j) * im)⁻¹) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hu1j : 0 ≤ gridTime s τ K n j := hu0 j hj'.le
    have h1j : 0 < 1 - gridTime s τ K n j := by linarith [huτ j hj'.le]
    have hQ0 : 0 ≤ Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ) := by
      have := st_Bctl_pos sz (n := n) (u := gridTime s τ K n j) (by linarith [huτ j hj'.le])
      positivity
    have hRj : (1 - gridTime s τ K n j) / (1 - τ n) ≤ R :=
      (div_le_div_of_nonneg_right (by linarith [hus j hj'.le]) h1τ.le).trans hR
    have hRj0 : 0 ≤ (1 - gridTime s τ K n j) / (1 - τ n) := div_nonneg h1j.le h1τ.le
    have h1 := TwistStep_EEU_le sz lam0 E n (gridTime s τ K n j) (gridTime s τ K n (K n)) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂
      (hqv j hj') hQ0 (Rv := (1 - gridTime s τ K n j) / (1 - gridTime s τ K n (K n)))
      (by rw [hlast]; exact TwistStep_rowsum sz lam0 E n hr hu1j (huτ j hj'.le) hτ1 σ a)
      (by rw [hlast]; exact TwistStep_rowsum sz lam0 E n hr hu1j (huτ j hj'.le) hτ1 (fun i => !σ i) a)
    rw [hlast] at h1
    have e : twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω = twEEUM sz lam0 E n (gridTime s τ K n j) (τ n) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂ := by
      simp only [twEEUk]; rw [hlast]
    have hBj : sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ) ≤ β ^ (13 / 4 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt (st_Bctl_pos sz (n := n) (u := gridTime s τ K n j) (by linarith [huτ j hj'.le]))) (hβ j hj'.le) (by norm_num)
    have hη0 : 0 ≤ ((1 - gridTime s τ K n j) * im)⁻¹ := inv_nonneg.2 (mul_nonneg h1j.le him.le)
    calc gridStep s τ K n * ‖twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω‖ =
          gridStep s τ K n * ‖twEEUM sz lam0 E n (gridTime s τ K n j) (τ n) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ a c₁ c₂‖ := by rw [e]
      _ ≤ gridStep s τ K n *
          ((1 - gridTime s τ K n j) / (1 - τ n) * ((1 - gridTime s τ K n j) / (1 - τ n)) *
            (Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hΔ0
          exact h1
      _ ≤ gridStep s τ K n * (R * R * (Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ * β ^ (13 / 4 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hΔ0
          gcongr
      _ = R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (gridStep s τ K n * ((1 - gridTime s τ K n j) * im)⁻¹) := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  calc _ ≤ R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (im⁻¹ * Real.log ((1 - s n) / (1 - τ n))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact TwistStep_eta_sum s τ K n hK hsτ hτ1 him

end P12


/-- The weight against the source level: `(β/b') (2 b² + Ξ b^{5/3}) ≤ 2 β² + Ξ β^{5/3}` for `0 < b ≤ b' ≤ β`, `Ξ ≥ 0`. -/
theorem TwistStep_gamma_le {b b' β Ξ : ℝ} (hb : 0 < b) (hbb : b ≤ b') (hbβ : b' ≤ β) (hΞ : 0 ≤ Ξ) :
    β / b' * (2 * b ^ 2 + Ξ * b ^ (5 / 3 : ℝ)) ≤ 2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ) := by
  have hb' : 0 < b' := hb.trans_le hbb
  have hβ : 0 < β := hb'.trans_le hbβ
  have h23 : b ^ (5 / 3 : ℝ) = b * b ^ (2 / 3 : ℝ) := by
    rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num, Real.rpow_add hb, Real.rpow_one]
  have h23' : β ^ (5 / 3 : ℝ) = β * β ^ (2 / 3 : ℝ) := by
    rw [show (5 / 3 : ℝ) = 1 + 2 / 3 by norm_num, Real.rpow_add hβ, Real.rpow_one]
  have hr : b ^ (2 / 3 : ℝ) ≤ β ^ (2 / 3 : ℝ) := Real.rpow_le_rpow hb.le (hbb.trans hbβ) (by norm_num)
  have hr0 : 0 ≤ b ^ (2 / 3 : ℝ) := Real.rpow_nonneg hb.le _
  have hq : β / b' ≤ β / b := div_le_div_of_nonneg_left hβ.le hb hbb
  have hq0 : 0 ≤ β / b' := div_nonneg hβ.le hb'.le
  have e1 : β / b * b ^ 2 = β * b := by field_simp
  have e2 : β / b * b ^ (5 / 3 : ℝ) = β * b ^ (2 / 3 : ℝ) := by rw [h23]; field_simp
  calc β / b' * (2 * b ^ 2 + Ξ * b ^ (5 / 3 : ℝ)) ≤ β / b * (2 * b ^ 2 + Ξ * b ^ (5 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hq (by positivity)
    _ = 2 * (β * b) + Ξ * (β * b ^ (2 / 3 : ℝ)) := by
        have : β / b * (2 * b ^ 2 + Ξ * b ^ (5 / 3 : ℝ)) = 2 * (β / b * b ^ 2) + Ξ * (β / b * b ^ (5 / 3 : ℝ)) := by ring
        rw [this, e1, e2]
    _ ≤ 2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ) := by
        rw [h23']
        have h1 : β * b ≤ β ^ 2 := by nlinarith [hbb.trans hbβ]
        have h2 : β * b ^ (2 / 3 : ℝ) ≤ β * β ^ (2 / 3 : ℝ) := mul_le_mul_of_nonneg_left hr hβ.le
        nlinarith

/-! ## 9. The pathwise bound in real parameters -/

section PathReal
open scoped Matrix.Norms.Operator

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- The elementary facts on the grid `u_k = s + kΔ` over `[s, τ]` used by the pathwise estimates. -/
theorem TwistStep_grid_facts (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0) :
    0 ≤ gridStep s τ K n ∧ gridTime s τ K n 0 = s n ∧ gridTime s τ K n (K n) = τ n ∧ ((K n : ℕ) : ℝ) * gridStep s τ K n = τ n - s n ∧
    (∀ k, gridTime s τ K n (k + 1) - gridTime s τ K n k = gridStep s τ K n) ∧
    (∀ k, k ≤ K n → 0 ≤ gridTime s τ K n k ∧ gridTime s τ K n k < 1 ∧ s n ≤ gridTime s τ K n k ∧ gridTime s τ K n k ≤ τ n) ∧
    (∀ i i', i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i') := by
  have hΔ0 : 0 ≤ gridStep s τ K n := div_nonneg (sub_nonneg.2 hsτ) (Nat.cast_nonneg _)
  have hmono : ∀ i i' : ℕ, i ≤ i' → gridTime s τ K n i ≤ gridTime s τ K n i' := by
    intro i i' h
    unfold gridTime
    have : (i : ℝ) ≤ (i' : ℝ) := Nat.cast_le.2 h
    nlinarith
  have hfirst : gridTime s τ K n 0 = s n := by simp [gridTime]
  have hlast : gridTime s τ K n (K n) = τ n := gridTime_last s τ K n hK
  refine ⟨hΔ0, hfirst, hlast, ?_, fun k => by unfold gridTime; push_cast; ring, fun k hk => ⟨?_, ?_, ?_, ?_⟩, hmono⟩
  · have hK' : ((K n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
    unfold gridStep; field_simp
  · have := hmono 0 k (Nat.zero_le k); rw [hfirst] at this; linarith
  · have := hmono k (K n) hk; rw [hlast] at this; linarith
  · have := hmono 0 k (Nat.zero_le k); rw [hfirst] at this; exact this
  · have := hmono k (K n) hk; rw [hlast] at this; exact this

/-- `(β/b) (N b^{3/2}) ≤ N β^{3/2}` for `0 < b ≤ β`: the initial term's loss `β/B_s` against `B_s^{3/2}`. -/
theorem TwistStep_init_le {b β N : ℝ} (hb : 0 < b) (hbβ : b ≤ β) (hN : 0 ≤ N) : β / b * (N * b ^ (3 / 2 : ℝ)) ≤ N * β ^ (3 / 2 : ℝ) := by
  have hβ : 0 < β := hb.trans_le hbβ
  have h32 : b ^ (3 / 2 : ℝ) = b * b ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hb, Real.rpow_one]
  have h32' : β ^ (3 / 2 : ℝ) = β * β ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hβ, Real.rpow_one]
  have hr : b ^ (1 / 2 : ℝ) ≤ β ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hb.le hbβ (by norm_num)
  calc β / b * (N * b ^ (3 / 2 : ℝ)) = N * (β * b ^ (1 / 2 : ℝ)) := by rw [h32]; field_simp
    _ ≤ N * (β * β ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hβ.le) hN
    _ = N * β ^ (3 / 2 : ℝ) := by rw [h32']

variable (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (ω : PathΩ sz)

/-- **The pathwise bound in real parameters** (the good-event conditions of the grid walk, `N^δ = Nδ`, the kernel-loss bounds `hker0`, `hkerj`, the quadratic variation `hqv`, the martingale
tail `hwm` and the remainder `hrem`): `‖Pr A_K‖ ≤ Λ Nδ β^{3/2} + Λ Nδ (2β² + Ξ β^{5/3}) (Im m)⁻¹ log R + 2 Nδ (R² Nδ β^{13/4} (Im m)⁻¹ log R + Np)^{1/2} + (the terms of order Δ)`. -/
theorem TwistStep_pathreal {κ : ℝ} (hr : BAReal d (sz.L n) (lam0 n) κ (E n) (BAmF sz lam0 E n))
    (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0)
    (Pr : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (hPr : ∀ x : Zd d (sz.L n) → ℂ, ‖Pr *ᵥ x‖ ≤ 2 * ‖x‖)
    {Nδ Ξ Λ θ ρ Ā Np R : ℝ} (him : 0 < (BAmF sz lam0 E n).im) (hNδ : 1 ≤ Nδ) (hΞ : 1 ≤ Ξ) (hΛ : 0 ≤ Λ) (hθ : 0 ≤ θ) (hNp : 0 ≤ Np)
    (hβ1 : sz.Bctl n (τ n) ≤ 1) (hR : (1 - s n) / (1 - τ n) ≤ R)
    (hA0 : ‖twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω‖ ≤ Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ))
    (hAj : ∀ j ≤ K n, ‖twAk sz lam0 E s τ K n σ c₁ c₂ j ω‖ ≤ Ā)
    (hS : ∀ j < K n, ‖TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j‖ ≤ Nδ * ((1 - gridTime s τ K n j) * (BAmF sz lam0 E n).im)⁻¹ *
      (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ)))
    (hker0 : ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n 0) (τ n) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω)‖ ≤
      Λ * (sz.Bctl n (τ n) / sz.Bctl n (s n)) * ‖twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω‖ + θ)
    (hkerj : ∀ j < K n, ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n (j + 1)) (τ n) *ᵥ TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤
      Λ * (sz.Bctl n (τ n) / sz.Bctl n (gridTime s τ K n (j + 1))) * ‖TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j‖ + θ)
    (hqv : ∀ j < K n, ∀ b, ‖twEEM sz lam0 E n (gridTime s τ K n j) ((baStep2Mat sz lam0 E).Hpath s τ K n j ω) σ b b c₁ c₂‖ ≤
      Nδ * ((1 - gridTime s τ K n j) * (BAmF sz lam0 E n).im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ))
    (hwm : ∀ a, ‖(∑ j ∈ Finset.range (K n), twU sz lam0 E n σ (gridTime s τ K n j) (τ n) *ᵥ
        (TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (j + 1) - TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω j)) a‖ ≤
      Nδ * (∑ j ∈ Finset.range (K n), gridStep s τ K n * ‖twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω‖ + Np) ^ (1 / 2 : ℝ))
    (hrem : ∀ k ≤ K n, ‖TwistStep_R sz lam0 E s τ K n σ c₁ c₂ ω k‖ ≤ ρ) :
    ‖Pr *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ (K n) ω‖ ≤
      (Λ * Nδ * sz.Bctl n (τ n) ^ (3 / 2 : ℝ) + θ) +
      (Λ * Nδ * (2 * sz.Bctl n (τ n) ^ 2 + Ξ * sz.Bctl n (τ n) ^ (5 / 3 : ℝ)) * ((BAmF sz lam0 E n).im⁻¹ * Real.log ((1 - s n) / (1 - τ n))) + θ) +
      2 * (ρ + (τ n - s n) * ((1 - τ n)⁻¹ * ρ) +
        Nδ * (R ^ 2 * (Nδ * sz.Bctl n (τ n) ^ (13 / 4 : ℝ)) * ((BAmF sz lam0 E n).im⁻¹ * Real.log ((1 - s n) / (1 - τ n))) + Np) ^ (1 / 2 : ℝ) +
        gridStep s τ K n * ((1 - τ n)⁻¹ * (Ā + Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ) +
          (τ n - s n) * ((1 - τ n)⁻¹ * Ā + Nδ * (((1 - τ n) * (BAmF sz lam0 E n).im)⁻¹ * (2 + Ξ))) + ρ)) +
        (τ n - s n) * (R * (gridStep s τ K n * ((1 - τ n)⁻¹) ^ 2 * Ā))) := by
  obtain ⟨hΔ0, hfirst, hlast, hKΔ, hsucc, hgrid, hmono⟩ := TwistStep_grid_facts s τ K n hs hsτ hτ1 hK
  set Δ := gridStep s τ K n with hΔ
  set im := (BAmF sz lam0 E n).im with him_def
  set β := sz.Bctl n (τ n) with hβdef
  set ℓ := Real.log ((1 - s n) / (1 - τ n)) with hℓ
  have h1τ : 0 < 1 - τ n := by linarith
  have hKΔ' : (K n : ℝ) * Δ ≤ 1 := by rw [hKΔ]; linarith
  have hBpos : ∀ k ≤ K n, 0 < sz.Bctl n (gridTime s τ K n k) := fun k hk => st_Bctl_pos sz (hgrid k hk).2.1
  have hBle : ∀ k ≤ K n, sz.Bctl n (gridTime s τ K n k) ≤ β := fun k hk => STBctl_mono sz n (hgrid k hk).2.2.2 hτ1
  have hBmono : ∀ j < K n, sz.Bctl n (gridTime s τ K n j) ≤ sz.Bctl n (gridTime s τ K n (j + 1)) := fun j hj =>
    STBctl_mono sz n (hmono j (j + 1) (Nat.le_succ j)) (hgrid (j + 1) hj).2.1
  have hβ0 : 0 < β := st_Bctl_pos sz hτ1
  have hbs0 : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (by linarith)
  have hbsβ : sz.Bctl n (s n) ≤ β := STBctl_mono sz n hsτ hτ1
  have hR0 : 0 ≤ R := (div_nonneg (by linarith) h1τ.le).trans hR
  have hηinv : ∀ j ≤ K n, 0 ≤ ((1 - gridTime s τ K n j) * im)⁻¹ := fun j hj =>
    inv_nonneg.2 (mul_nonneg (by linarith [(hgrid j hj).2.1]) him.le)
  have hΓ0 : 0 ≤ 2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ) := by positivity
  -- the initial term
  have hini : ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n 0) (τ n) *ᵥ twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω)‖ ≤ Λ * Nδ * β ^ (3 / 2 : ℝ) + θ := by
    refine hker0.trans ?_
    have h1 : Λ * (β / sz.Bctl n (s n)) * ‖twAk sz lam0 E s τ K n σ c₁ c₂ 0 ω‖ ≤ Λ * (β / sz.Bctl n (s n)) * (Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hA0 (mul_nonneg hΛ (div_nonneg hβ0.le hbs0.le))
    have h2 := TwistStep_init_le hbs0 hbsβ (by linarith : 0 ≤ Nδ)
    nlinarith [mul_le_mul_of_nonneg_left h2 hΛ]
  -- the sources
  have hsrc : ∀ j < K n, ‖Pr *ᵥ (twU sz lam0 E n σ (gridTime s τ K n (j + 1)) (τ n) *ᵥ TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤
      Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ := by
    intro j hj
    refine (hkerj j hj).trans ?_
    have hj1 := hBpos j hj.le
    have hγ := TwistStep_gamma_le hj1 (hBmono j hj) (hBle (j + 1) hj) (by linarith : 0 ≤ Ξ)
    have hSj := hS j hj
    calc Λ * (β / sz.Bctl n (gridTime s τ K n (j + 1))) * ‖TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j‖ + θ ≤
          Λ * (β / sz.Bctl n (gridTime s τ K n (j + 1))) * (Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ *
            (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ))) + θ := by
          gcongr
          exact mul_nonneg hΛ (div_nonneg hβ0.le (hBpos (j + 1) hj).le)
      _ = Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (β / sz.Bctl n (gridTime s τ K n (j + 1)) *
            (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ)))) + θ := by ring
      _ ≤ Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ := by
          gcongr
          exact hηinv j hj.le
  -- a crude bound on the sources
  have hSm : ∀ j < K n, ‖TwistStep_S sz lam0 E s τ K n σ c₁ c₂ ω j‖ ≤ Nδ * (((1 - τ n) * im)⁻¹ * (2 + Ξ)) := by
    intro j hj
    refine (hS j hj).trans ?_
    have hB1 : sz.Bctl n (gridTime s τ K n j) ≤ 1 := (hBle j hj.le).trans hβ1
    have hBj := hBpos j hj.le
    have h2 : sz.Bctl n (gridTime s τ K n j) ^ 2 ≤ 1 := pow_le_one₀ hBj.le hB1
    have h53 : sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ) ≤ 1 := Real.rpow_le_one hBj.le hB1 (by norm_num)
    have hηle : ((1 - gridTime s τ K n j) * im)⁻¹ ≤ ((1 - τ n) * im)⁻¹ :=
      inv_anti₀ (mul_pos h1τ him) (mul_le_mul_of_nonneg_right (by linarith [(hgrid j hj.le).2.2.2]) him.le)
    have hpos : 0 ≤ ((1 - gridTime s τ K n j) * im)⁻¹ := hηinv j hj.le
    calc Nδ * ((1 - gridTime s τ K n j) * im)⁻¹ * (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ))
        ≤ Nδ * ((1 - τ n) * im)⁻¹ * (2 + Ξ) := by
          have : 2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ) ≤ 2 + Ξ := by nlinarith
          gcongr
      _ = _ := by ring
  have hMt := TwistStep_mt_bound sz lam0 E s τ K n σ c₁ c₂ ω hr hs hsτ hτ1 hK hA0 (hAj (K n) le_rfl) (fun j hj => hAj j hj.le) hSm (hrem (K n) le_rfl)
  rw [hKΔ] at hMt
  -- the martingale sum
  have hms : ‖∑ j ∈ Finset.range (K n), twU sz lam0 E n σ (gridTime s τ K n j) (τ n) *ᵥ
      (TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω (j + 1) - TwistStep_Mt sz lam0 E s τ K n σ c₁ c₂ ω j)‖ ≤
      Nδ * (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (im⁻¹ * ℓ) + Np) ^ (1 / 2 : ℝ) := by
    have hm20 : 0 ≤ Nδ * (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (im⁻¹ * ℓ) + Np) ^ (1 / 2 : ℝ) := by
      have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by
        rw [le_div_iff₀ h1τ]; linarith)
      positivity
    refine (pi_norm_le_iff_of_nonneg hm20).2 fun a => (hwm a).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (K n)) => mul_nonneg hΔ0 (norm_nonneg (twEEUk sz lam0 E s τ K n σ a c₁ c₂ j (K n) ω)))
      linarith) ?_ (by norm_num)) (by linarith)
    have := TwistStep_S2 sz lam0 E s τ K n hr hs hsτ hτ1 hK σ c₁ c₂ ω a (Nδ := Nδ) (β := β) (R := R) him (by linarith) hBle hR hqv
    linarith
  have hmain := TwistStep_path sz lam0 E s τ K n σ c₁ c₂ ω hr hs hsτ hτ1 hK Pr hPr (L0 := Λ * Nδ * β ^ (3 / 2 : ℝ) + θ)
    (Ls := fun j => Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ) (ρ := ρ)
    (m1 := Ā + Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ) + (τ n - s n) * ((1 - τ n)⁻¹ * Ā + Nδ * (((1 - τ n) * im)⁻¹ * (2 + Ξ))) + ρ)
    (m2 := Nδ * (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * (im⁻¹ * ℓ) + Np) ^ (1 / 2 : ℝ)) (Ā := Ā)
    hini hsrc hrem hMt hms (fun j hj => hAj j hj.le)
  -- the drift sum
  have hdrift : Δ * ∑ j ∈ Finset.range (K n), (Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ) ≤
      Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * (im⁻¹ * ℓ) + θ := by
    have h1 := TwistStep_eta_sum s τ K n hK hsτ hτ1 him
    calc Δ * ∑ j ∈ Finset.range (K n), (Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ)
        = Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * (Δ * ∑ j ∈ Finset.range (K n), ((1 - gridTime s τ K n j) * im)⁻¹) + (K n : ℝ) * Δ * θ := by
          have e : ∑ j ∈ Finset.range (K n), (Λ * Nδ * (((1 - gridTime s τ K n j) * im)⁻¹ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ))) + θ) =
              Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * ∑ j ∈ Finset.range (K n), ((1 - gridTime s τ K n j) * im)⁻¹ + (K n : ℝ) * θ := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by ring
          rw [e]
          ring
      _ ≤ Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * (im⁻¹ * ℓ) + 1 * θ := by
          gcongr
      _ = _ := by ring
  have hRr : (1 - s n) / (1 - τ n) ≤ R := hR
  have hK0 : (K n : ℝ) * Δ = τ n - s n := hKΔ
  refine hmain.trans ?_
  rw [hK0]
  have hτs : 0 ≤ τ n - s n := by linarith
  have hh1 : 0 ≤ (1 - τ n)⁻¹ := inv_nonneg.2 h1τ.le
  have hĀ : 0 ≤ Ā := (norm_nonneg _).trans (hAj 0 (Nat.zero_le _))
  have hterm : (τ n - s n) * ((1 - s n) / (1 - τ n) * (Δ * ((1 - τ n)⁻¹) ^ 2 * Ā)) ≤ (τ n - s n) * (R * (Δ * ((1 - τ n)⁻¹) ^ 2 * Ā)) := by
    gcongr
  linarith [hdrift]

end PathReal

/-! ## 10. The final arithmetic, the transport at the initial index, `ℓ_t` in the time, the number of labels -/

/-- `√(a + b) ≤ √a + √b`. -/
theorem TwistStep_sqrt_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- **The final arithmetic**: the terms of `TwistStep_pathreal` against `N^{τ'} β^{3/2}(1 + β^{1/6} Ξ)`.  `imℓ = (Im m)⁻¹ log R`, `Tiny` the terms of order `Δ`. -/
theorem TwistStep_arith {β Ξ Nτ Nδ Λ θ imℓ R Np Tiny Bound : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hΞ : 1 ≤ Ξ) (hNδ : 1 ≤ Nδ) (hΛ : Λ ≤ Nδ)
    (him0 : 0 ≤ imℓ) (himℓ : imℓ ≤ Nδ) (hR0 : 0 ≤ R) (hRβ : R * β ^ (13 / 8 : ℝ) ≤ β ^ (3 / 2 : ℝ)) (hNp0 : 0 ≤ Np)
    (hNτ : 40 * Nδ ^ 3 ≤ Nτ) (hθ : 16 * θ ≤ β ^ (3 / 2 : ℝ)) (hNp : 16 * Nδ * Real.sqrt Np ≤ β ^ (3 / 2 : ℝ))
    (hTiny : 16 * Tiny ≤ β ^ (3 / 2 : ℝ) + β ^ (5 / 3 : ℝ) * Ξ)
    (hBound : Bound ≤ (Λ * Nδ * β ^ (3 / 2 : ℝ) + θ) + (Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * imℓ + θ) +
      2 * (Nδ * (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ + Np) ^ (1 / 2 : ℝ)) + Tiny) :
    Bound ≤ Nτ * (β ^ (3 / 2 : ℝ) * (1 + β ^ (1 / 6 : ℝ) * Ξ)) := by
  have hb32 : 0 < β ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hβ0 _
  have hb53 : 0 < β ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hβ0 _
  have hid : β ^ (3 / 2 : ℝ) * (1 + β ^ (1 / 6 : ℝ) * Ξ) = β ^ (3 / 2 : ℝ) + β ^ (5 / 3 : ℝ) * Ξ := by
    have : β ^ (3 / 2 : ℝ) * β ^ (1 / 6 : ℝ) = β ^ (5 / 3 : ℝ) := by
      rw [← Real.rpow_add hβ0]; norm_num
    calc β ^ (3 / 2 : ℝ) * (1 + β ^ (1 / 6 : ℝ) * Ξ) = β ^ (3 / 2 : ℝ) + (β ^ (3 / 2 : ℝ) * β ^ (1 / 6 : ℝ)) * Ξ := by ring
      _ = _ := by rw [this]
  rw [hid]
  have hβ2 : β ^ 2 ≤ β ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hβ0 hβ1 (by norm_num)
  have hN1 : Nδ ^ 2 ≤ Nδ ^ 3 := pow_le_pow_right₀ hNδ (by norm_num)
  have hN0 : 0 ≤ Nδ := by linarith
  have hNτ1 : 1 ≤ Nτ := by nlinarith [one_le_pow₀ (n := 3) hNδ]
  -- the square-root term
  have hsq : Real.sqrt (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ + Np) ≤ Nδ * β ^ (3 / 2 : ℝ) + Real.sqrt Np := by
    refine (TwistStep_sqrt_add (by positivity) hNp0).trans (add_le_add ?_ le_rfl)
    have e : R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ = (R * β ^ (13 / 8 : ℝ)) ^ 2 * (Nδ * imℓ) := by
      have : (β ^ (13 / 8 : ℝ)) ^ 2 = β ^ (13 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hβ0.le]; norm_num
      calc R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ = R ^ 2 * (β ^ (13 / 8 : ℝ)) ^ 2 * (Nδ * imℓ) := by rw [this]; ring
        _ = _ := by ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    have h2 : Real.sqrt (Nδ * imℓ) ≤ Nδ := by
      rw [Real.sqrt_le_left hN0]
      nlinarith
    calc (R * β ^ (13 / 8 : ℝ)) * Real.sqrt (Nδ * imℓ) ≤ β ^ (3 / 2 : ℝ) * Nδ :=
          mul_le_mul hRβ h2 (Real.sqrt_nonneg _) hb32.le
      _ = Nδ * β ^ (3 / 2 : ℝ) := by ring
  have hsq' : (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ + Np) ^ (1 / 2 : ℝ) ≤ Nδ * β ^ (3 / 2 : ℝ) + Real.sqrt Np := by
    rw [← Real.sqrt_eq_rpow]; exact hsq
  have hP4 : 2 * (Nδ * (R ^ 2 * (Nδ * β ^ (13 / 4 : ℝ)) * imℓ + Np) ^ (1 / 2 : ℝ)) ≤ 2 * Nδ ^ 2 * β ^ (3 / 2 : ℝ) + 2 * (Nδ * Real.sqrt Np) := by
    nlinarith [mul_le_mul_of_nonneg_left hsq' hN0]
  have hP1 : Λ * Nδ * β ^ (3 / 2 : ℝ) ≤ Nδ ^ 3 * β ^ (3 / 2 : ℝ) := by
    have : Λ * Nδ ≤ Nδ ^ 3 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hb32.le
  have hP3 : Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * imℓ ≤ Nδ ^ 3 * (2 * β ^ (3 / 2 : ℝ) + Ξ * β ^ (5 / 3 : ℝ)) := by
    have h1 : Λ * Nδ * imℓ ≤ Nδ ^ 3 := by
      calc Λ * Nδ * imℓ ≤ Nδ * Nδ * Nδ := by gcongr
        _ = Nδ ^ 3 := by ring
    have h2 : 2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ) ≤ 2 * β ^ (3 / 2 : ℝ) + Ξ * β ^ (5 / 3 : ℝ) := by linarith
    calc Λ * Nδ * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) * imℓ = (Λ * Nδ * imℓ) * (2 * β ^ 2 + Ξ * β ^ (5 / 3 : ℝ)) := by ring
      _ ≤ Nδ ^ 3 * (2 * β ^ (3 / 2 : ℝ) + Ξ * β ^ (5 / 3 : ℝ)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
  have hNpt : 2 * (Nδ * Real.sqrt Np) ≤ β ^ (3 / 2 : ℝ) / 8 := by nlinarith
  have hcoef : Nδ ^ 3 ≤ Nτ / 40 := by linarith
  have h5 : 0 ≤ β ^ (5 / 3 : ℝ) * Ξ := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hcoef hb32.le, mul_le_mul_of_nonneg_right hcoef h5, mul_le_mul_of_nonneg_right hNδ hb32.le,
    mul_le_mul_of_nonneg_right hN1 hb32.le, mul_le_mul_of_nonneg_right hNτ1 hb32.le, mul_le_mul_of_nonneg_right hNτ1 h5,
    mul_le_mul_of_nonneg_right hNτ1 (by positivity : 0 ≤ β ^ (5 / 3 : ℝ) * Ξ)]


/-- **Model to grid walk at the initial index** (a wrapper of `ST_grid_whp_zero` for `PrecL` over the labels at the time `s_n`). -/
theorem TwistStep_grid_zero {d : ℕ} (sz : Sizes d) (s τ : ℕ → ℝ) (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hK : ∀ n, K n ≠ 0)
    {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)] {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) (Zb : ∀ n, V n → ℝ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u))
    (h : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := V)
      (fun n v ω => F n v (s n) ((sz.withLam 0).seqHflow n (s n) ω)) (fun n v _ => Zb n v (s n)))
    {δ : ℝ} (hδ : 0 < δ) :
    Gauss.HighProbAt (pathP (sz.withLam 0)) sz.size (fun n => {ω | ∀ v : V n,
      F n v (gridTime s τ K n 0) (pathH (sz.withLam 0) s τ K n 0 ω) ≤ ((sz.size n : ℕ) : ℝ) ^ δ * Zb n v (gridTime s τ K n 0)}) :=
  Sizes.ST_grid_whp_zero (sz.withLam 0) s τ K hs hsτ hK hC0 hcard F (fun n v u _ => Zb n v u) hF (fun _ _ _ => measurable_const) δ hδ h

/-- `ℓ_u ≤ ℓ_v` for `u ≤ v < 1` (`ℓ_t = min (max (g/√|1-t|) 1) L`). -/
theorem TwistStep_ellT_mono (L : ℕ) {g u v : ℝ} (hg : 0 ≤ g) (huv : u ≤ v) (hv : v < 1) : ellT L g u ≤ ellT L g v := by
  unfold ellT
  refine min_le_min (max_le_max ?_ le_rfl) le_rfl
  have h1 : |1 - v| ≤ |1 - u| := by
    rw [abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  have h2 : 0 < |1 - v| := abs_pos.2 (by linarith)
  exact div_le_div_of_nonneg_left hg (Real.sqrt_pos.2 h2) (Real.sqrt_le_sqrt h1)

/-- The number of labels `(σ, a, c₁, c₂)` is at most `4 N³`. -/
theorem TwistStep_card_V {d : ℕ} (sz : Sizes d) (n : ℕ) :
    (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤ 4 * ((sz.size n : ℕ) : ℝ) ^ 3 := by
  have hL : Fintype.card (Zd d (sz.L n)) = (sz.L n) ^ d := card_Zd d (sz.L n)
  have hle : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.L n) ^ d ≤ (sz.W n * sz.L n) ^ d := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    exact_mod_cast h
  simp only [Fintype.card_prod, Fintype.card_pi, hL, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  have h0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  calc 4 * (((sz.L n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) ≤ 4 * (((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ))) := by
        gcongr
    _ = 4 * ((sz.size n : ℕ) : ℝ) ^ 3 := by ring

/-- **The terms of order `Δ`** of `TwistStep_pathreal`: `Tiny ≤ 18 √Δ N^{C₀} Y³ N (1 + Ξ)`, `Y ≥ 1` a bound of `(1 - τ)⁻¹`, `R`, `η⁻¹`; `ρ = N^{C₀} √Δ`. -/
theorem TwistStep_tiny {Δ c X1 Rr im1 Nδ N bs Ξ ρ Ā Pn Y : ℝ} (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hY : 1 ≤ Y)
    (hX1 : 0 ≤ X1) (hX1Y : X1 ≤ Y) (hRr0 : 0 ≤ Rr) (hRrY : Rr ≤ Y) (him1 : 0 ≤ im1) (him1Y : im1 ≤ Y) (hNδ1 : 1 ≤ Nδ) (hNδN : Nδ ≤ N)
    (hbs0 : 0 ≤ bs) (hbs1 : bs ≤ 1) (hΞ : 1 ≤ Ξ) (hPn : 1 ≤ Pn) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ Real.sqrt Δ * Pn) (hĀ0 : 0 ≤ Ā) (hĀ : Ā ≤ N * Ξ) :
    2 * (ρ + c * (X1 * ρ) + Δ * (X1 * (Ā + Nδ * bs + c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) + ρ)) + c * (Rr * (Δ * X1 ^ 2 * Ā))) ≤
      18 * Real.sqrt Δ * Pn * Y ^ 3 * N * (1 + Ξ) := by
  have hN1 : 1 ≤ N := hNδ1.trans hNδN
  have hsΔ : Δ ≤ Real.sqrt Δ := by
    calc Δ = Real.sqrt (Δ ^ 2) := (Real.sqrt_sq hΔ0).symm
      _ ≤ Real.sqrt Δ := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 ≤ Real.sqrt Δ := Real.sqrt_nonneg _
  have hY0 : 0 ≤ Y := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hΞ0 : 0 ≤ Ξ := by linarith
  -- the bracket
  have hbr : Ā + Nδ * bs + c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) + ρ ≤ 5 * Y * N * (1 + Ξ) + ρ := by
    have h1 : Ā ≤ Y * N * (1 + Ξ) := by nlinarith [mul_nonneg hY0 hN0]
    have h2 : Nδ * bs ≤ Y * N * (1 + Ξ) := by nlinarith [mul_nonneg hY0 hN0, mul_nonneg hN0 hΞ0, mul_nonneg hY0 hΞ0]
    have h3 : X1 * Ā ≤ Y * (N * Ξ) := mul_le_mul hX1Y hĀ hĀ0 hY0
    have h4 : Nδ * (im1 * (2 + Ξ)) ≤ N * (Y * (2 + Ξ)) := by
      refine mul_le_mul hNδN (mul_le_mul him1Y le_rfl (by linarith) hY0) (by positivity) hN0
    have h5 : c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) ≤ 1 * (Y * (N * Ξ) + N * (Y * (2 + Ξ))) := by
      refine mul_le_mul hc1 (add_le_add h3 h4) (by positivity) (by norm_num)
    nlinarith [mul_nonneg hY0 hN0, mul_nonneg (mul_nonneg hY0 hN0) hΞ0]
  have hterm3 : Δ * (X1 * (Ā + Nδ * bs + c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) + ρ)) ≤ Δ * (Y * (5 * Y * N * (1 + Ξ) + ρ)) := by
    refine mul_le_mul_of_nonneg_left (mul_le_mul hX1Y hbr (by positivity) hY0) hΔ0
  have hterm4 : c * (Rr * (Δ * X1 ^ 2 * Ā)) ≤ Δ * (Y ^ 3 * (N * Ξ)) := by
    have h1 : Rr * (Δ * X1 ^ 2 * Ā) ≤ Y * (Δ * Y ^ 2 * (N * Ξ)) := by
      refine mul_le_mul hRrY (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX1 hX1Y 2) hΔ0) hĀ (by positivity) (by positivity))
        (by positivity) hY0
    calc c * (Rr * (Δ * X1 ^ 2 * Ā)) ≤ 1 * (Y * (Δ * Y ^ 2 * (N * Ξ))) := mul_le_mul hc1 h1 (by positivity) (by norm_num)
      _ = Δ * (Y ^ 3 * (N * Ξ)) := by ring
  have hterm2 : c * (X1 * ρ) ≤ Y * ρ := by
    calc c * (X1 * ρ) ≤ 1 * (Y * ρ) := mul_le_mul hc1 (mul_le_mul_of_nonneg_right hX1Y hρ0) (by positivity) (by norm_num)
      _ = Y * ρ := one_mul _
  have hsum : ρ + c * (X1 * ρ) + Δ * (X1 * (Ā + Nδ * bs + c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) + ρ)) + c * (Rr * (Δ * X1 ^ 2 * Ā)) ≤
      ρ * (1 + 2 * Y) + 6 * Δ * (Y ^ 3 * N * (1 + Ξ)) := by
    have e1 : Δ * (Y * ρ) ≤ Y * ρ := by nlinarith [mul_nonneg hY0 hρ0]
    nlinarith [mul_nonneg hY0 hρ0, mul_nonneg (mul_nonneg (mul_nonneg hY0 hY0) hY0) (mul_nonneg hN0 hΞ0), mul_nonneg hΔ0 (mul_nonneg (pow_nonneg hY0 3) hN0),
      mul_nonneg hΔ0 (mul_nonneg (pow_nonneg hY0 3) (mul_nonneg hN0 hΞ0)), mul_nonneg hΔ0 (mul_nonneg (pow_nonneg hY0 2) (mul_nonneg hN0 hΞ0)),
      mul_nonneg hΔ0 (mul_nonneg (mul_nonneg hY0 hY0) hN0), hY, mul_le_mul_of_nonneg_left hY hΔ0]
  set Q : ℝ := Y ^ 3 * N * (1 + Ξ) with hQ
  have hQ1 : 1 ≤ Q := by
    have h1 : 1 ≤ Y ^ 3 := one_le_pow₀ hY
    have h2 : 1 ≤ 1 + Ξ := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ Y ^ 3 * N * (1 + Ξ) := by gcongr
  have hYQ : Y ≤ Q := by
    have h1 : Y ≤ Y ^ 3 := by nlinarith [mul_nonneg hY0 hY0]
    calc Y ≤ Y ^ 3 := h1
      _ = Y ^ 3 * 1 * 1 := by ring
      _ ≤ Y ^ 3 * N * (1 + Ξ) := by gcongr; linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hP0 : 0 ≤ Real.sqrt Δ * Pn := mul_nonneg hs0 (by linarith)
  have h1 : ρ * (1 + 2 * Y) ≤ Real.sqrt Δ * Pn * (3 * Q) := by
    calc ρ * (1 + 2 * Y) ≤ (Real.sqrt Δ * Pn) * (1 + 2 * Y) := mul_le_mul_of_nonneg_right hρ (by linarith)
      _ ≤ (Real.sqrt Δ * Pn) * (3 * Q) := mul_le_mul_of_nonneg_left (by linarith) hP0
  have h2 : 6 * Δ * Q ≤ 6 * (Real.sqrt Δ * Pn) * Q := by
    have : Δ ≤ Real.sqrt Δ * Pn := hsΔ.trans (le_mul_of_one_le_right hs0 hPn)
    nlinarith
  calc 2 * (ρ + c * (X1 * ρ) + Δ * (X1 * (Ā + Nδ * bs + c * (X1 * Ā + Nδ * (im1 * (2 + Ξ))) + ρ)) + c * (Rr * (Δ * X1 ^ 2 * Ā))) ≤
        2 * (ρ * (1 + 2 * Y) + 6 * Δ * Q) := by rw [hQ]; linarith
    _ ≤ 2 * (Real.sqrt Δ * Pn * (3 * Q) + 6 * (Real.sqrt Δ * Pn) * Q) := by linarith
    _ = 18 * Real.sqrt Δ * Pn * Y ^ 3 * N * (1 + Ξ) := by rw [hQ]; ring

/-! ## 11. The good-event conditions of the grid walk and the deterministic core at one size index -/

open private TwistKer2_eta_inv_le TwistKer2_conU TwistKer2_Bctl_ge_inv from RBM3D.BA.TwistKer2

section Det

variable {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- **The good-event conditions of the grid walk at size index `n`, part 1** for the sample `ω` (all `σ`, `c₁`, `c₂`; `Nδ = N^δ`, `Dd` the decay exponent):
(1) `‖Z_s‖ ≤ Nδ B_s^{3/2}`, (2) `‖Z_{u_j}‖ ≤ Nδ Ξ`, (3) the sources `S_j`, (4) the quadratic variation, (5), (6) the decay of `Z_s` and `S_j` at the scale `3 W^{ε'} ℓ_{u_j}`. -/
def TwistStep_Good1 (Ξ Nδ ε' Dd : ℝ) (ω : PathΩ (sz.withLam 0)) : Prop :=
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ‖twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ 0 ω‖ ≤ Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ)) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ∀ j ≤ K n, ‖twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ j ω‖ ≤ Nδ * Ξ) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ∀ j < K n, ‖TwistStep_S sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j‖ ≤
    Nδ * ((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ *
      (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ))) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ∀ j < K n, ∀ b, ‖twEEM sz (BAflowLam0 sz z) (BAflowEs sz z) n (gridTime s τ K n j)
      ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s τ K n j ω) σ b b c₁ c₂‖ ≤
    Nδ * ((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ)) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)) (b : Zd d (sz.L n)), 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (gridTime s τ K n 0) ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) →
    ‖twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ 0 ω b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ∀ j < K n, ∀ b, 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (gridTime s τ K n j) ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) →
    ‖TwistStep_S sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd))

/-- The martingale tail (7) and the remainder (8) of `TwistStep_Good`. -/
def TwistStep_Good2 (Nδ Np ρ : ℝ) (ω : PathΩ (sz.withLam 0)) : Prop :=
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ a : Zd d (sz.L n)), ‖(∑ j ∈ Finset.range (K n), twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s τ K n j) (τ n) *ᵥ
        (TwistStep_Mt sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω (j + 1) - TwistStep_Mt sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j)) a‖ ≤
      Nδ * (∑ j ∈ Finset.range (K n), gridStep s τ K n * ‖twEEUk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ a c₁ c₂ j (K n) ω‖ + Np) ^ (1 / 2 : ℝ)) ∧
  (∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ∀ k ≤ K n, ‖TwistStep_R sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω k‖ ≤ ρ)

/-- `TwistStep_Good1 ∧ TwistStep_Good2` (private: a public `Prop` definition that a theorem assumes and no theorem proves would be a registry premise). -/
private def TwistStep_Good (Ξ Nδ Np ρ ε' Dd : ℝ) (ω : PathΩ (sz.withLam 0)) : Prop :=
  TwistStep_Good1 sz z s τ K n Ξ Nδ ε' Dd ω ∧ TwistStep_Good2 sz z s τ K n Nδ Np ρ ω

/-- **The deterministic core at one size index**: from the good-event conditions at `n` (`TwistStep_Good`), the kernel-loss bound `hKL` and the arithmetic facts, for every `σ`, `c₁`, `c₂`:
`‖Pr A_K‖ ≤ N^{τ'} B_τ^{3/2} (1 + B_τ^{1/6} Ξ)`. -/
theorem TwistStep_det_n {κ ε 𝔠 𝔡 𝔠d : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (h𝔠d : 0 < 𝔠d) (h𝔠d8 : 𝔠d ≤ 1 / 8)
    {t : ℕ → ℝ} (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτt : τ n ≤ t n) (htT : t n ≤ BAflowT0 sz z n) (hK : K n ≠ 0) (hlam0 : 0 ≤ sz.lam n)
    (hconn : (sz.Bctl n (t n)) ^ 𝔠d ≤ (1 - t n) / (1 - s n) ∧ (1 - t n) / (1 - s n) < 1)
    (Pr : (Fin 2 → Bool) → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (hPr : ∀ σ (x : Zd d (sz.L n) → ℂ), ‖Pr σ *ᵥ x‖ ≤ 2 * ‖x‖)
    {Ξ Nδ Nτ Λ θ Np ρ ε' Dd C₀ : ℝ} (hΞ : 1 ≤ Ξ) (hNδ1 : 1 ≤ Nδ) (hNδN : Nδ ≤ ((sz.size n : ℕ) : ℝ)) (hΛ : Λ ≤ Nδ) (hNp0 : 0 ≤ Np)
    (hNτ : 40 * Nδ ^ 3 ≤ Nτ) (him : (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im⁻¹ * Real.log ((1 - s n) / (1 - τ n)) ≤ Nδ)
    (hθ : 16 * θ ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ)) (hNp : 16 * Nδ * Real.sqrt Np ≤ sz.Bctl n (τ n) ^ (3 / 2 : ℝ))
    (hρ : ρ = ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s τ K n)) (hC₀ : 0 ≤ C₀)
    (hsmall : 16 * (18 * Real.sqrt (gridStep s τ K n) * ((sz.size n : ℕ) : ℝ) ^ C₀ * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) ^ 3 * ((sz.size n : ℕ) : ℝ) * (1 + Ξ)) ≤
      sz.Bctl n (τ n) ^ (3 / 2 : ℝ) + sz.Bctl n (τ n) ^ (5 / 3 : ℝ) * Ξ)
    (hKL : ∀ (σ : Fin 2 → Bool) (c₁ : Zd d (sz.L n)) (v : ℝ), s n ≤ v → v ≤ τ n → ∀ x : Zd d (sz.L n) → ℂ,
      (∀ b, 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) → ‖x b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) →
      ‖Pr σ *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ v (τ n) *ᵥ x)‖ ≤
        Λ * (sz.Bctl n (τ n) / sz.Bctl n v) * ‖x‖ + θ)
    (hΛ0 : 0 ≤ Λ) (hθ0 : 0 ≤ θ)
    (ω : PathΩ (sz.withLam 0)) (hG : TwistStep_Good sz z s τ K n Ξ Nδ Np ρ ε' Dd ω) :
    ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)), ‖Pr σ *ᵥ twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ (K n) ω‖ ≤
      Nτ * (sz.Bctl n (τ n) ^ (3 / 2 : ℝ) * (1 + sz.Bctl n (τ n) ^ (1 / 6 : ℝ) * Ξ)) := by
  obtain ⟨⟨g1, g2, g3, g4, g5, g6⟩, g8, g9⟩ := hG
  intro σ c₁ c₂
  obtain ⟨hΔ0, hfirst, hlast, hKΔ, hsucc, hgrid, hmono⟩ := TwistStep_grid_facts s τ K n hs hsτ ((hτt.trans htT).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)) hK
  have hτ1 : τ n < 1 := (hτt.trans htT).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hm := EMn2BA_mF_data sz hflow n
  have him0 : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ hm.1
  obtain ⟨h1s, hB1t, hBcon⟩ := TwistKer2_conU sz n h𝔠d hconn hτt ((htT).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))
  have h1τ : 0 < 1 - τ n := by linarith
  have hβ0 : 0 < sz.Bctl n (τ n) := st_Bctl_pos sz hτ1
  have hβ1 : sz.Bctl n (τ n) ≤ 1 := hB1t
  set im := (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im with him_def
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set β := sz.Bctl n (τ n) with hβdef
  set Δ := gridStep s τ K n with hΔdef
  have hNδ0 : 0 ≤ Nδ := by linarith
  -- the kernel-loss inputs
  have hker0 : ‖Pr σ *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s τ K n 0) (τ n) *ᵥ twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ 0 ω)‖ ≤
      Λ * (β / sz.Bctl n (s n)) * ‖twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ 0 ω‖ + θ := by
    have h := hKL σ c₁ (gridTime s τ K n 0) (by rw [hfirst]) (by rw [hfirst]; exact hsτ) (twAk sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ 0 ω)
      (fun b hb => g5 σ c₁ c₂ b hb)
    rw [hfirst] at h ⊢
    exact h
  have hkerj : ∀ j < K n, ‖Pr σ *ᵥ (twU sz (BAflowLam0 sz z) (BAflowEs sz z) n σ (gridTime s τ K n (j + 1)) (τ n) *ᵥ TwistStep_S sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j)‖ ≤
      Λ * (β / sz.Bctl n (gridTime s τ K n (j + 1))) * ‖TwistStep_S sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j‖ + θ := by
    intro j hj
    refine hKL σ c₁ (gridTime s τ K n (j + 1)) (hgrid (j + 1) hj).2.2.1 (hgrid (j + 1) hj).2.2.2 _ (fun b hb => g6 σ c₁ c₂ j hj b ?_)
    refine le_trans ?_ hb
    have hmw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' := Real.rpow_nonneg (Nat.cast_nonneg _) _
    exact mul_le_mul_of_nonneg_left (TwistStep_ellT_mono (sz.L n) hlam0 (hmono j (j + 1) (Nat.le_succ j)) (hgrid (j + 1) hj).2.1) (by positivity)
  have hR1 : 1 ≤ (1 - s n) / (1 - τ n) := by rw [le_div_iff₀ h1τ]; linarith
  set R := (1 - s n) / (1 - τ n) with hRdef
  have hℓ0 : 0 ≤ Real.log R := Real.log_nonneg hR1
  have himℓ0 : 0 ≤ im⁻¹ * Real.log R := mul_nonneg (inv_nonneg.2 him0.le) hℓ0
  have hpath := TwistStep_pathreal sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω hr hs hsτ hτ1 hK (Pr σ) (hPr σ)
    (Nδ := Nδ) (Ξ := Ξ) (Λ := Λ) (θ := θ) (ρ := ρ) (Ā := Nδ * Ξ) (Np := Np) (R := R) him0 hNδ1 hΞ hΛ0 hθ0 hNp0 hβ1 le_rfl
    (g1 σ c₁ c₂) (g2 σ c₁ c₂) (g3 σ c₁ c₂) hker0 hkerj (g4 σ c₁ c₂) (g8 σ c₁ c₂) (g9 σ c₁ c₂)
  -- the bounds by `Y = (2/κ) N`
  have hη := TwistKer2_eta_inv_le hκ hε hflow n (hs.trans hsτ) (hτt.trans htT)
  have hη' : (((1 - τ n) * im)⁻¹) ≤ (2 / κ) * N := hη
  have hY1 : 1 ≤ (2 / κ) * N := by
    have h2k : 1 ≤ 2 / κ := by rw [le_div_iff₀ hκ]; linarith only [hm.1, hm.2]
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (2 / κ) * N := mul_le_mul h2k hN1 zero_le_one (by linarith only [h2k])
  have hX1 : (1 - τ n)⁻¹ ≤ (2 / κ) * N := by
    refine le_trans ?_ hη'
    exact inv_anti₀ (mul_pos h1τ him0) (mul_le_of_le_one_right h1τ.le hm.2)
  have hRY : R ≤ (2 / κ) * N := by
    refine le_trans ?_ hX1
    rw [hRdef, div_eq_mul_inv]
    exact mul_le_of_le_one_left (inv_nonneg.2 h1τ.le) (by linarith)
  have hconR : R * β ^ (13 / 8 : ℝ) ≤ β ^ (3 / 2 : ℝ) := by
    have h1 : R * β ^ 𝔠d ≤ 1 := by
      calc R * β ^ 𝔠d ≤ R * ((1 - τ n) / (1 - s n)) := mul_le_mul_of_nonneg_left hBcon (by linarith)
        _ = 1 := by rw [hRdef]; field_simp
    have h2 : β ^ (13 / 8 : ℝ) = β ^ 𝔠d * β ^ (13 / 8 - 𝔠d) := by rw [← Real.rpow_add hβ0]; ring_nf
    have h3 : β ^ (13 / 8 - 𝔠d) ≤ β ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hβ0 hβ1 (by linarith)
    calc R * β ^ (13 / 8 : ℝ) = (R * β ^ 𝔠d) * β ^ (13 / 8 - 𝔠d) := by rw [h2]; ring
      _ ≤ 1 * β ^ (13 / 8 - 𝔠d) := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hβ0.le _)
      _ ≤ β ^ (3 / 2 : ℝ) := by rw [one_mul]; exact h3
  have hbsB : sz.Bctl n (s n) ≤ 1 := (STBctl_mono sz n hsτ hτ1).trans hβ1
  have hbs0 : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (by linarith only [hs, hsτ, hτ1])
  have hbs : sz.Bctl n (s n) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hbs0.le hbsB (by norm_num)
  have hKge : (1 : ℝ) ≤ (K n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hK
  have hΔ1 : Δ ≤ 1 := by
    have : Δ ≤ τ n - s n := by
      rw [hΔdef]; unfold gridStep
      exact div_le_self (by linarith only [hsτ]) hKge
    linarith only [this, hτ1, hs]
  have hc1 : τ n - s n ≤ 1 := by linarith only [hτ1, hs]
  have hPn : 1 ≤ N ^ C₀ := Real.one_le_rpow hN1 hC₀
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact mul_nonneg (Real.rpow_nonneg (by linarith only [hN1]) _) (Real.sqrt_nonneg _)
  have hĀ0 : 0 ≤ Nδ * Ξ := mul_nonneg hNδ0 (by linarith only [hΞ])
  have hĀ : Nδ * Ξ ≤ N * Ξ := mul_le_mul_of_nonneg_right hNδN (by linarith only [hΞ])
  have hX10 : 0 ≤ (1 - τ n)⁻¹ := inv_nonneg.2 h1τ.le
  have him10 : 0 ≤ ((1 - τ n) * im)⁻¹ := inv_nonneg.2 (mul_pos h1τ him0).le
  have htiny := TwistStep_tiny (Δ := Δ) (c := τ n - s n) (X1 := (1 - τ n)⁻¹) (Rr := R) (im1 := ((1 - τ n) * im)⁻¹) (Nδ := Nδ) (N := N) (bs := sz.Bctl n (s n) ^ (3 / 2 : ℝ))
    (Ξ := Ξ) (ρ := ρ) (Ā := Nδ * Ξ) (Pn := N ^ C₀) (Y := (2 / κ) * N) hΔ0 hΔ1 (by linarith only [hsτ]) hc1 hY1 hX10 hX1 (by linarith only [hR1]) hRY
    him10 hη' hNδ1 hNδN (Real.rpow_nonneg hbs0.le _) hbs hΞ hPn hρ0 (by rw [hρ]; exact le_of_eq (mul_comm _ _)) hĀ0 hĀ
  have hTiny : 16 * (2 * (ρ + (τ n - s n) * ((1 - τ n)⁻¹ * ρ) + Δ * ((1 - τ n)⁻¹ * (Nδ * Ξ + Nδ * sz.Bctl n (s n) ^ (3 / 2 : ℝ) +
      (τ n - s n) * ((1 - τ n)⁻¹ * (Nδ * Ξ) + Nδ * (((1 - τ n) * im)⁻¹ * (2 + Ξ))) + ρ)) + (τ n - s n) * (R * (Δ * ((1 - τ n)⁻¹) ^ 2 * (Nδ * Ξ))))) ≤
      β ^ (3 / 2 : ℝ) + β ^ (5 / 3 : ℝ) * Ξ := by
    refine le_trans ?_ hsmall
    have := mul_le_mul_of_nonneg_left htiny (by norm_num : (0 : ℝ) ≤ 16)
    refine le_trans this (le_of_eq ?_)
    ring
  refine TwistStep_arith (Λ := Λ) (θ := θ) (imℓ := im⁻¹ * Real.log R) (R := R) (Np := Np) hβ0 hβ1 hΞ hNδ1 hΛ himℓ0 him (by linarith only [hR1]) hconR hNp0 hNτ hθ hNp hTiny ?_
  have hp := hpath
  linarith only [hp]

end Det

/-! ## 12. The six events of the grid walk (the model-level statements transported to all grid times) -/

section Events

variable {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)

/-- The deterministic shift `H ↦ λ₀ Ψ + H` of the flow matrix is measurable. -/
theorem TwistStep_measurable_shift (c : ℂ) :
    Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ => c • PsiI d (sz.L n) (sz.W n) + H) :=
  Measurable.of_eval_matrix _ fun i j => by
    simp only [Matrix.add_apply]
    exact measurable_const.add measurable_id.eval_matrix

/-- `Z_u(H)(σ, a, c₁, c₂) = L̃ - K̃` of the flow matrix `λ₀ Ψ + H` (the grid walk without the deterministic shift), a function of the label `v = (σ, a, c₁, c₂)`. -/
def TwistStep_Fz (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  ‖twL2M sz lam0 E n u ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 v.2.1 v.2.2.1 v.2.2.2 -
    twK (baFM sz lam0 E) n u v.1 v.2.1 v.2.2.1 v.2.2.2‖

/-- `‖B̃₁‖ + ‖B̃₂‖ + ‖Ẽ^{G̊}‖` of the flow matrix, as a function of the label. -/
def TwistStep_Fs (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  ‖twB1M sz lam0 E n u ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 v.2.1 v.2.2.1 v.2.2.2‖ +
    ‖twB2M sz lam0 E n u ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 v.2.1 v.2.2.1 v.2.2.2‖ +
    ‖twEGM sz lam0 E n u ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 v.2.1 v.2.2.1 v.2.2.2‖

/-- `‖(Ẽ⊗Ẽ)(b,b)‖` of the flow matrix (`b = v.2.1`). -/
def TwistStep_Fq (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  ‖twEEM sz lam0 E n u ((lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + H) v.1 v.2.1 v.2.1 v.2.2.1 v.2.2.2‖

theorem TwistStep_measurable_Fz (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) :
    Measurable (TwistStep_Fz sz lam0 E n v u) := by
  unfold TwistStep_Fz
  exact (((TwistGridTail_measurable_twL2M sz lam0 E n u v.1 v.2.1 v.2.2.1 v.2.2.2).comp (TwistStep_measurable_shift sz n _)).sub_const _).norm

theorem TwistStep_measurable_Fs (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) :
    Measurable (TwistStep_Fs sz lam0 E n v u) := by
  unfold TwistStep_Fs
  have hs := TwistStep_measurable_shift sz n ((lam0 n : ℂ))
  exact (((TwistStep_measurable_twB1M sz lam0 E n u v.1 v.2.1 v.2.2.1 v.2.2.2).comp hs).norm.add
    ((TwistStep_measurable_twB2M sz lam0 E n u v.1 v.2.1 v.2.2.1 v.2.2.2).comp hs).norm).add
    ((TwistStep_measurable_twEGM sz lam0 E n u v.1 v.2.1 v.2.2.1 v.2.2.2).comp hs).norm

theorem TwistStep_measurable_Fq (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) :
    Measurable (TwistStep_Fq sz lam0 E n v u) := by
  unfold TwistStep_Fq
  have := TwistGridTail_measurable_twEEM sz lam0 E n u v.1 v.2.1 v.2.1 v.2.2.1 v.2.2.2
  exact (this.comp (TwistStep_measurable_shift sz n _)).norm

/-- `Z` times the indicator of the far region `3 W^{ε'} ℓ_u ≤ |a - c₁|_∞` (`twDec`, with the label `v = (σ, a, c₁, c₂)`). -/
def TwistStep_Fzd (ε' : ℝ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  TwistStep_Fz sz lam0 E n v u H * (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) u ≤ (zdistInf d (sz.L n) (v.2.1 - v.2.2.1) : ℝ) then 1 else 0)

/-- The sources times the indicator of the far region. -/
def TwistStep_Fsd (ε' : ℝ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  TwistStep_Fs sz lam0 E n v u H * (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) u ≤ (zdistInf d (sz.L n) (v.2.1 - v.2.2.1) : ℝ) then 1 else 0)

theorem TwistStep_measurable_Fzd (ε' : ℝ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) :
    Measurable (TwistStep_Fzd sz lam0 E n ε' v u) :=
  (TwistStep_measurable_Fz sz lam0 E n v u).mul measurable_const

theorem TwistStep_measurable_Fsd (ε' : ℝ) (v : (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) (u : ℝ) :
    Measurable (TwistStep_Fsd sz lam0 E n ε' v u) :=
  (TwistStep_measurable_Fs sz lam0 E n v u).mul measurable_const

variable (z : ℕ → ℂ) (s τ : ℕ → ℝ) (K : ℕ → ℕ)

/-- `|S_j(a)| ≤ ‖B̃₁‖ + ‖B̃₂‖ + ‖Ẽ^{G̊}‖`. -/
theorem TwistStep_S_le_Fs (σ : Fin 2 → Bool) (c₁ c₂ a : Zd d (sz.L n)) (ω : PathΩ (sz.withLam 0)) (j : ℕ) :
    ‖TwistStep_S sz (BAflowLam0 sz z) (BAflowEs sz z) s τ K n σ c₁ c₂ ω j a‖ ≤
      TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n (σ, a, c₁, c₂) (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) :=
  norm_add₃_le

/-- **The six events give the good conditions (part 1)** (a deterministic inclusion at a fixed size index; `Bctl ≤ 1` along the grid, `Nδ · 3 W^{-Da} ≤ W^{-Dd}`). -/
theorem TwistStep_good1_of_events (hs : 0 ≤ s n) (hsτ : s n ≤ τ n) (hτ1 : τ n < 1) (hK : K n ≠ 0) (hβ1 : sz.Bctl n (τ n) ≤ 1)
    (him : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im) {Ξ Nδ Da ε' Dd : ℝ} (hΞ : 0 ≤ Ξ) (hNδ : 0 ≤ Nδ)
    (hD : Nδ * (3 * ((sz.W n : ℕ) : ℝ) ^ (-Da)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd)) (ω : PathΩ (sz.withLam 0))
    (e1 : ∀ v, TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v (gridTime s τ K n 0) (pathH (sz.withLam 0) s τ K n 0 ω) ≤
      Nδ * sz.Bctl n (gridTime s τ K n 0) ^ (3 / 2 : ℝ))
    (e2 : ∀ j ∈ Finset.range (K n + 1), ∀ v, TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) ≤
      Nδ * (Ξ * sz.Bctl n (gridTime s τ K n j) ^ (3 / 2 : ℝ)))
    (e3 : ∀ j ∈ Finset.range (K n + 1), ∀ v, TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n v (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) ≤
      Nδ * (((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ *
        (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ))))
    (e4 : ∀ j ∈ Finset.range (K n + 1), ∀ v, TwistStep_Fq sz (BAflowLam0 sz z) (BAflowEs sz z) n v (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) ≤
      Nδ * (((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * sz.Bctl n (gridTime s τ K n j) ^ (13 / 4 : ℝ)))
    (e5 : ∀ v, TwistStep_Fzd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v (gridTime s τ K n 0) (pathH (sz.withLam 0) s τ K n 0 ω) ≤
      Nδ * ((sz.W n : ℕ) : ℝ) ^ (-Da))
    (e6 : ∀ j ∈ Finset.range (K n + 1), ∀ v, TwistStep_Fsd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v (gridTime s τ K n j) (pathH (sz.withLam 0) s τ K n j ω) ≤
      Nδ * (3 * ((sz.W n : ℕ) : ℝ) ^ (-Da))) :
    TwistStep_Good1 sz z s τ K n Ξ Nδ ε' Dd ω := by
  obtain ⟨hΔ0, hfirst, hlast, hKΔ, hsucc, hgrid, hmono⟩ := TwistStep_grid_facts s τ K n hs hsτ hτ1 hK
  have hBj : ∀ j ≤ K n, sz.Bctl n (gridTime s τ K n j) ≤ 1 := fun j hj => (STBctl_mono sz n (hgrid j hj).2.2.2 hτ1).trans hβ1
  have hBpos : ∀ j ≤ K n, 0 < sz.Bctl n (gridTime s τ K n j) := fun j hj => st_Bctl_pos sz (hgrid j hj).2.1
  have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-Da) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hηinv : ∀ j ≤ K n, 0 ≤ ((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ := fun j hj =>
    inv_nonneg.2 (mul_nonneg (by linarith [(hgrid j hj).2.1]) him.le)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ c₁ c₂
    rw [← hfirst]
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hNδ (Real.rpow_nonneg (hBpos 0 (Nat.zero_le _)).le _))).2 fun a => ?_
    exact e1 (σ, a, c₁, c₂)
  · intro σ c₁ c₂ j hj
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hNδ hΞ)).2 fun a => ?_
    refine (e2 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj)) (σ, a, c₁, c₂)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hNδ
    have := Real.rpow_le_one (hBpos j hj).le (hBj j hj) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  · intro σ c₁ c₂ j hj
    have hj' : j ≤ K n := hj.le
    have hnn : 0 ≤ Nδ * ((1 - gridTime s τ K n j) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ *
        (2 * sz.Bctl n (gridTime s τ K n j) ^ 2 + Ξ * sz.Bctl n (gridTime s τ K n j) ^ (5 / 3 : ℝ)) := by
      have := hBpos j hj'
      have := hηinv j hj'
      positivity
    refine (pi_norm_le_iff_of_nonneg hnn).2 fun a => ?_
    rw [mul_assoc]
    exact (TwistStep_S_le_Fs sz n z s τ K σ c₁ c₂ a ω j).trans (e3 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj')) (σ, a, c₁, c₂))
  · intro σ c₁ c₂ j hj b
    have hj' : j ≤ K n := hj.le
    rw [mul_assoc]
    exact e4 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj')) (σ, b, c₁, c₂)
  · intro σ c₁ c₂ b hb
    have h := e5 (σ, b, c₁, c₂)
    have hind : (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (gridTime s τ K n 0) ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) then (1 : ℝ) else 0) = 1 := by simp only [hb, ↓reduceIte]
    unfold TwistStep_Fzd at h
    simp only [hind, mul_one] at h
    refine le_trans ?_ (h.trans (le_trans (mul_le_mul_of_nonneg_left (by linarith [hW0]) hNδ) hD))
    exact le_of_eq rfl
  · intro σ c₁ c₂ j hj b hb
    have hj' : j ≤ K n := hj.le
    have h := e6 j (Finset.mem_range.2 (Nat.lt_succ_of_le hj')) (σ, b, c₁, c₂)
    have hind : (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) (gridTime s τ K n j) ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ) then (1 : ℝ) else 0) = 1 := by simp only [hb, ↓reduceIte]
    unfold TwistStep_Fsd at h
    simp only [hind, mul_one] at h
    exact (TwistStep_S_le_Fs sz n z s τ K σ c₁ c₂ b ω j).trans (h.trans hD)

/-- **The six events hold w.h.p.** (the model-level statements in the forms of the families `TwistStep_Fz`, `Fs`, `Fq`, `Fzd`, `Fsd`; the transports `TwistStep_grid_whp`, `TwistStep_grid_zero`, then the inclusion
`TwistStep_good1_of_events`). -/
theorem TwistStep_events_hp {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hτt : ∀ n, τ n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hK : ∀ n, K n ≠ 0)
    {C : ℝ} (hC0 : 0 ≤ C) (hcard : ∀ᶠ n in atTop, ((((K n + 1) * Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℕ)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (Ξ : ℕ → ℝ) (hΞ : ∀ n, 1 ≤ Ξ n) {δ ε' Da Dd : ℝ} (hδ : 0 < δ) (hβ1 : ∀ᶠ n in atTop, sz.Bctl n (τ n) ≤ 1)
    (hD : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ δ * (3 * ((sz.W n : ℕ) : ℝ) ^ (-Da)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dd))
    (hL0 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n v ω => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v (s n) ((sz.withLam 0).seqHflow n (s n) ω)) (fun n _ _ => sz.Bctl n (s n) ^ (3 / 2 : ℝ)))
    (hZ : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => Ξ n * sz.Bctl n (p.1 : ℝ) ^ (3 / 2 : ℝ)))
    (hS : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => ((1 - (p.1 : ℝ)) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ *
        (2 * sz.Bctl n (p.1 : ℝ) ^ 2 + Ξ n * sz.Bctl n (p.1 : ℝ) ^ (5 / 3 : ℝ))))
    (hQ : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fq sz (BAflowLam0 sz z) (BAflowEs sz z) n p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => ((1 - (p.1 : ℝ)) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * sz.Bctl n (p.1 : ℝ) ^ (13 / 4 : ℝ)))
    (hD0 : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n v ω => TwistStep_Fzd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v (s n) ((sz.withLam 0).seqHflow n (s n) ω))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-Da)))
    (hDS : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)))
      (fun n p ω => TwistStep_Fsd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' p.2 (p.1 : ℝ) ((sz.withLam 0).seqHflow n (p.1 : ℝ) ω))
      (fun n p _ => 3 * ((sz.W n : ℕ) : ℝ) ^ (-Da))) :
    Gauss.HighProbAt (pathP (sz.withLam 0)) sz.size (fun n => {ω | TwistStep_Good1 sz z s τ K n (Ξ n) (((sz.size n : ℕ) : ℝ) ^ δ) ε' Dd ω}) := by
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hflow.1.2.2.1
  have hcard0 : ∀ᶠ n in atTop, (Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := by
    filter_upwards [hcard] with n hn
    refine le_trans ?_ hn
    have : ((Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℕ) : ℝ) ≤ (((K n + 1) * Fintype.card ((Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    exact this
  have E1 := TwistStep_grid_zero sz s τ K hs hsτ hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard0
    (fun n v u H => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v u H) (fun n v u => sz.Bctl n u ^ (3 / 2 : ℝ))
    (fun n v u => TwistStep_measurable_Fz sz _ _ n v u) hL0 hδ
  have E2 := TwistStep_grid_whp sz s t τ K hs hsτ hτt hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard
    (fun n v u H => TwistStep_Fz sz (BAflowLam0 sz z) (BAflowEs sz z) n v u H) (fun n v u => Ξ n * sz.Bctl n u ^ (3 / 2 : ℝ))
    (fun n v u => TwistStep_measurable_Fz sz _ _ n v u) hZ hδ
  have E3 := TwistStep_grid_whp sz s t τ K hs hsτ hτt hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard
    (fun n v u H => TwistStep_Fs sz (BAflowLam0 sz z) (BAflowEs sz z) n v u H)
    (fun n v u => ((1 - u) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * (2 * sz.Bctl n u ^ 2 + Ξ n * sz.Bctl n u ^ (5 / 3 : ℝ)))
    (fun n v u => TwistStep_measurable_Fs sz _ _ n v u) hS hδ
  have E4 := TwistStep_grid_whp sz s t τ K hs hsτ hτt hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard
    (fun n v u H => TwistStep_Fq sz (BAflowLam0 sz z) (BAflowEs sz z) n v u H)
    (fun n v u => ((1 - u) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im)⁻¹ * sz.Bctl n u ^ (13 / 4 : ℝ))
    (fun n v u => TwistStep_measurable_Fq sz _ _ n v u) hQ hδ
  have E5 := TwistStep_grid_zero sz s τ K hs hsτ hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard0
    (fun n v u H => TwistStep_Fzd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v u H) (fun n v u => ((sz.W n : ℕ) : ℝ) ^ (-Da))
    (fun n v u => TwistStep_measurable_Fzd sz _ _ n ε' v u) hD0 hδ
  have E6 := TwistStep_grid_whp sz s t τ K hs hsτ hτt hK (V := fun n => (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n)) hC0 hcard
    (fun n v u H => TwistStep_Fsd sz (BAflowLam0 sz z) (BAflowEs sz z) n ε' v u H) (fun n v u => 3 * ((sz.W n : ℕ) : ℝ) ^ (-Da))
    (fun n v u => TwistStep_measurable_Fsd sz _ _ n ε' v u) hDS hδ
  have H := ((((E1.inter hsize E2).inter hsize E3).inter hsize E4).inter hsize E5).inter hsize E6
  refine H.mono ?_
  filter_upwards [hβ1, hD] with n hb hd ω hω
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hω
  have hτ1 : τ n < 1 := (hτt n).trans_lt ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))
  have him : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := lt_of_lt_of_le hκ (EMn2BA_mF_data sz hflow n).1
  exact TwistStep_good1_of_events sz n z s τ K (hs n) (hsτ n) hτ1 (hK n) hb him (by linarith [hΞ n]) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hd ω h1 h2 h3 h4 h5 h6

end Events

/-! ## 13. From the grid walk at the last index back to the model -/

/-- **Model to grid walk at the last grid index, for a family of labels** (a wrapper of `ST_model_le_path` for `F = sup` over the labels): if on the set `Good` every label satisfies
`F ≤ N^{τ'} Bd` at the last grid state, the model probability of `{∃ v, N^{τ'} Bd < F v}` is at most that of the complement of `Good`. -/
theorem TwistStep_model_le {d : ℕ} (sz : Sizes d) (s τ : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hsτ : ∀ n, s n ≤ τ n) (hK : ∀ n, K n ≠ 0) (n : ℕ)
    {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    (F : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ) (hF : ∀ n v u, Measurable (F n v u)) (τ' Bd : ℝ)
    (Good : Set (PathΩ sz)) (hgood : ∀ ω ∈ Good, ∀ v : V n, F n v (τ n) (pathH sz s τ K n (K n) ω) ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Bd) :
    Sizes.seqP sz {ω | ∃ v : V n, ((sz.size n : ℕ) : ℝ) ^ τ' * Bd < F n v (τ n) (sz.seqHflow n (τ n) ω)} ≤ pathP sz Goodᶜ := by
  classical
  have hm : ∀ n' u, Measurable (fun H : Matrix (Idx d (sz.L n') (sz.W n')) (Idx d (sz.L n') (sz.W n')) ℂ => Finset.univ.sup' Finset.univ_nonempty (fun v : V n' => F n' v u H)) := by
    intro n' u
    have := Finset.measurable_sup' (s := (Finset.univ : Finset (V n'))) Finset.univ_nonempty (fun v _ => hF n' v u)
    convert this using 1
    ext H
    simp [Finset.sup'_apply]
  have h := Sizes.ST_model_le_path sz s τ K hs hsτ hK n (fun n u H => Finset.univ.sup' Finset.univ_nonempty (fun v : V n => F n v u H)) (fun n u H => Bd)
    hm (fun n u => measurable_const) τ' Goodᶜ (by
      intro ω hω
      by_contra hno
      have hG : ω ∈ Good := not_not.1 hno
      have hω' : ((sz.size n : ℕ) : ℝ) ^ τ' * Bd < Finset.univ.sup' Finset.univ_nonempty (fun v : V n => F n v (τ n) (pathH sz s τ K n (K n) ω)) := hω
      obtain ⟨v, -, hv⟩ := (Finset.lt_sup'_iff Finset.univ_nonempty).1 hω'
      exact absurd (hgood ω hG v) (not_le.2 hv))
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [Finset.lt_sup'_iff]
  simp

/-! ## 14. The scale of the kernel against the control: `ℓ_v(g₀)` (F1) and the comparability of `B_{v,0}` (4.18) -/

/-- `c ℓ_v(g) ≤ ℓ_v(c g)` for `0 ≤ c ≤ 1`, `g ≥ 0` (F1 (a): `ℓ_v(g₀) ≥ √t₀ ℓ_v(lam)`). -/
theorem TwistStep_ellT_scale (L : ℕ) {g c v : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : c * ellT L g v ≤ ellT L (c * g) v := by
  unfold ellT
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  refine le_min ?_ ?_
  · calc c * min (max (g / Real.sqrt |1 - v|) 1) (L : ℝ) ≤ c * max (g / Real.sqrt |1 - v|) 1 :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hc0
      _ = max (c * (g / Real.sqrt |1 - v|)) c := by rw [mul_max_of_nonneg _ _ hc0, mul_one]
      _ ≤ max (c * g / Real.sqrt |1 - v|) 1 := by
          rw [mul_div_assoc]
          exact max_le_max le_rfl hc1
  · calc c * min (max (g / Real.sqrt |1 - v|) 1) (L : ℝ) ≤ c * L := mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
      _ ≤ 1 * L := mul_le_mul_of_nonneg_right hc1 hL
      _ = L := one_mul _

/-- The comparability of `B_{v,0}` with `(g² + 1 - v)⁻¹` in the regime `g² ≤ L² (1 - v)` (`d, L ≥ 3`; (4.18)). -/
theorem TwistStep_Bparam_cmp {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {g v : ℝ} (hv : v < 1) (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - v)) :
    1 ≤ (g ^ 2 + (1 - v)) * Bparam d L g v 0 ∧ (g ^ 2 + (1 - v)) * Bparam d L g v 0 ≤ 2 := by
  have hu : (0 : ℝ) < 1 - v := by linarith
  have habs : |1 - v| = 1 - v := abs_of_pos hu
  have hB : Bparam d L g v 0 = (g ^ 2 + (1 - v))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
    simp [Bparam, habs]
  have hgu : (0 : ℝ) < g ^ 2 + (1 - v) := by positivity
  have hL3 : (3 : ℝ) ≤ L := by exact_mod_cast hL
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hLd3 : (L : ℝ) ^ 3 ≤ (L : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
  have hL2 : (L : ℝ) ^ 2 + 1 ≤ (L : ℝ) ^ 3 := by nlinarith [sq_nonneg (L : ℝ)]
  have e : (g ^ 2 + (1 - v)) * Bparam d L g v 0 = 1 + (g ^ 2 + (1 - v)) / ((L : ℝ) ^ d * (1 - v)) := by
    rw [hB]; field_simp
  rw [e]
  refine ⟨by have : 0 ≤ (g ^ 2 + (1 - v)) / ((L : ℝ) ^ d * (1 - v)) := by positivity
             linarith, ?_⟩
  have : (g ^ 2 + (1 - v)) / ((L : ℝ) ^ d * (1 - v)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  linarith

/-- The kernel factor of T.10 (b) against the control: `(g² + (1-v))/(g² + (1-u)) ≤ 2 A B_{u,0}/B_{v,0}` for `g² ≤ lam² ≤ A g²`, `lam² ≤ L² (1 - u)`. -/
theorem TwistStep_ratio_le {d L : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) {g lam v u A : ℝ} (hA : 1 ≤ A) (hg2 : g ^ 2 ≤ lam ^ 2) (hlam2 : lam ^ 2 ≤ A * g ^ 2)
    (hvu : v ≤ u) (hu : u < 1) (hlu : lam ^ 2 ≤ (L : ℝ) ^ 2 * (1 - u)) :
    (g ^ 2 + |1 - v|) / (g ^ 2 + |1 - u|) ≤ 2 * A * (Bparam d L lam u 0 / Bparam d L lam v 0) := by
  have hv : v < 1 := lt_of_le_of_lt hvu hu
  have h1u : 0 < 1 - u := by linarith
  have h1v : 0 < 1 - v := by linarith
  have hlv : lam ^ 2 ≤ (L : ℝ) ^ 2 * (1 - v) := hlu.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  obtain ⟨-, hv2⟩ := TwistStep_Bparam_cmp hd hL hv hlv
  obtain ⟨hu1, -⟩ := TwistStep_Bparam_cmp hd hL hu hlu
  rw [abs_of_pos h1u, abs_of_pos h1v]
  set Bv := Bparam d L lam v 0 with hBv
  set Bu := Bparam d L lam u 0 with hBu
  have hBv0 : 0 < Bv := by
    by_contra hneg
    have : Bv ≤ 0 := not_lt.1 hneg
    have h2 : 0 < (lam ^ 2 + (1 - v)) := by positivity
    nlinarith [TwistStep_Bparam_cmp hd hL hv hlv |>.1]
  have hBu0 : 0 < Bu := by
    by_contra hneg
    have : Bu ≤ 0 := not_lt.1 hneg
    have h2 : 0 < (lam ^ 2 + (1 - u)) := by positivity
    nlinarith
  have hY0 : 0 < g ^ 2 + (1 - u) := by
    have : 0 ≤ g ^ 2 := sq_nonneg _
    linarith
  rw [div_le_iff₀ hY0]
  have hX : (g ^ 2 + (1 - v)) * Bv ≤ 2 := by
    refine le_trans ?_ hv2
    exact mul_le_mul_of_nonneg_right (by linarith) hBv0.le
  have hY : 1 ≤ A * Bu * (g ^ 2 + (1 - u)) := by
    have h3 : lam ^ 2 + (1 - u) ≤ A * (g ^ 2 + (1 - u)) := by nlinarith
    calc (1 : ℝ) ≤ (lam ^ 2 + (1 - u)) * Bu := hu1
      _ ≤ A * (g ^ 2 + (1 - u)) * Bu := mul_le_mul_of_nonneg_right h3 hBu0.le
      _ = A * Bu * (g ^ 2 + (1 - u)) := by ring
  calc g ^ 2 + (1 - v) = ((g ^ 2 + (1 - v)) * Bv) / Bv := by field_simp
    _ ≤ 2 / Bv := div_le_div_of_nonneg_right hX hBv0.le
    _ ≤ (2 / Bv) * (A * Bu * (g ^ 2 + (1 - u))) := le_mul_of_one_le_right (by positivity) hY
    _ = 2 * A * (Bu / Bv) * (g ^ 2 + (1 - u)) := by field_simp

end RBM.BA

end
