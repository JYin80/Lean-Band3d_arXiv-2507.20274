/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ExpHierGen
import RBM3D.Induction.ExpDuhamel
import RBM3D.Chain.GridDuhamelGen

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The two Duhamel formulas of Step 6 over the carrier (BA-V row V1s1, ticket T2502 row b, target 13)

Additive restatement of `Induction/ExpDuhamel.lean` (not edited) over a carrier `C : FlowFM sz`, on the one kernel `Step2Gen_UN` (`Chain/Step2Gen.lean`, `Chain/GridDuhamelGen.lean`).
Paper: arXiv:2507.20274, `(Eexpint_K-L)` `6:3-7`, `(iisuwjyys_exp)` `6:142-146`, `(int_K-L+QE)` `6:109-116`, `Def:QtPt` `3_5:1200-1260`.

**Route** (as `ExpDuhamel:26-35`, the band file's one-slot identities replaced by the single hypothesis `Step2Gen_USemigroup C n`, the semigroup law of `(def_Ustz)`).
`v ↦ (𝒰_{v,t,σ} Y_v)_a` has derivative `𝒰_{v,t}(Y'_v - Θ_v Y_v)`: `Step2Gen_uKer` is affine in its first time with `∂_r = -Step2Gen_thetaKer t` (`ExpDuhamelGen_uKer_eq`), and
the semigroup law at `u = 0, 1` gives `𝒰_{v,t} Θ_v = Θ_t` slot by slot (`ExpDuhamelGen_uKer_mul_thetaKer`).  With `Y` continuous on `[s,t]`, the derivative on `(s,t)`, `𝒰_{t,t} = id` (`Step2Gen_UN_self`),
the fundamental theorem of calculus gives `Y_t = 𝒰_{s,t} Y_s + ∫_s^t 𝒰_{u,t} D_u du` (`ExpDuhamelGen_duhamel`).  The plain form is `Y = f`, `D = STExpDriftg` (from the pin `STExpHierAtgL`);
the zero-mode form follows by linearity of `Q^{(A)}` (applied **outside** `𝒰`, as the pinned text `STExpDuhamelZAtgL` has it: `Q^{(A)} 𝒰 = 𝒰 Q^{(A)}` is not needed, and is false for a
carrier whose `X` does not commute with the all-ones matrix); the `𝒬` form is the engine at `Y_u = 𝒬_u f_u`, `D = STExpQsrcg`.

**Targets.** `stExpDuhamelZgL_at`, `stExpDuhamelQgL_at` (per index, from `STExpHierAtgL` and `Step2Gen_USemigroup`), `stExpDuhamelZgL_ev`, `stExpDuhamelQgL_ev` (the eventual family
pins `STExpDuhamelZgL`, `STExpDuhamelQgL`), band re-derivations `stExpDuhamelZ_of_gL`, `stExpDuhamelQ_of_gL`, instances.  No `def`, `abbrev` or `structure` is added.
-/

open private expDuh_continuousOn_Qop_gen expDuh_intervalIntegrable_deriv expDuh_sum_update_reindex from RBM3D.Induction.ExpDuhamel

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal Matrix.Norms.L2Operator

/-! ## 1. The kernel `𝒰_{v,t}` as a function of its first time, and the slot identity -/

section Kernel

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ)

/-- `uKer r t = Θ_t - r • thetaKer t` (band `expDuh_uKer_eq`, `ExpDuhamel:66`). -/
private theorem ExpDuhamelGen_uKer_eq (σ σ' : Bool) (t r : ℝ) :
    Step2Gen_uKer C n σ σ' r t =
      Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ) - (r : ℂ) • Step2Gen_thetaKer C n σ σ' t := by
  simp only [Step2Gen_uKer, Step2Gen_thetaKer, sub_mul, one_mul, smul_mul_assoc]

/-- `∂_r (uKer r t)_{xy} = -(thetaKer t)_{xy}` (band `expDuh_hasDerivAt_uKer`, `ExpDuhamel:71`). -/
private theorem ExpDuhamelGen_hasDerivAt_uKer (σ σ' : Bool) (t : ℝ) (x y : Zd d (sz.L n)) (v : ℝ) :
    HasDerivAt (fun r : ℝ => Step2Gen_uKer C n σ σ' r t x y) (-(Step2Gen_thetaKer C n σ σ' t x y)) v := by
  have h : (fun r : ℝ => Step2Gen_uKer C n σ σ' r t x y) = fun r : ℝ =>
      Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ) x y - (r : ℂ) * Step2Gen_thetaKer C n σ σ' t x y := by
    funext r
    rw [ExpDuhamelGen_uKer_eq]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
  exact ((hasDerivAt_const v (Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (t : ℂ) x y)).fun_sub
    (hid.mul_const (Step2Gen_thetaKer C n σ σ' t x y))).congr_deriv (by ring)

private theorem ExpDuhamelGen_continuous_uKer (σ σ' : Bool) (t : ℝ) (x y : Zd d (sz.L n)) :
    Continuous fun r : ℝ => Step2Gen_uKer C n σ σ' r t x y :=
  continuous_iff_continuousAt.2 fun v => (ExpDuhamelGen_hasDerivAt_uKer C n σ σ' t x y v).continuousAt

/-- **The one-slot identity** `𝒰_{v,t} Θ_v = Θ_t` (band `expDuh_uKer_mul_thetaKer`, `ExpDuhamel:89`, there from `Theta_sub_Theta`): from the semigroup law
`𝒰_{v,t} 𝒰_{u,v} = 𝒰_{u,t}` at `u = 0` and `u = 1`, `𝒰_{u,w} = Θ_w - u Θ_w'`, subtracted. -/
theorem ExpDuhamelGen_uKer_mul_thetaKer (h : Step2Gen_USemigroup C n) (σ σ' : Bool) {v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1)
    (hw0 : 0 ≤ w) (hw1 : w < 1) :
    Step2Gen_uKer C n σ σ' v w * Step2Gen_thetaKer C n σ σ' v = Step2Gen_thetaKer C n σ σ' w := by
  have h0 := (h σ σ' 0 v w hv0 hv1 hw0 hw1).2
  have h1 := (h σ σ' 1 v w hv0 hv1 hw0 hw1).2
  rw [ExpDuhamelGen_uKer_eq C n σ σ' v 0, ExpDuhamelGen_uKer_eq C n σ σ' w 0] at h0
  rw [ExpDuhamelGen_uKer_eq C n σ σ' v 1, ExpDuhamelGen_uKer_eq C n σ σ' w 1] at h1
  simp only [Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one, one_smul] at h0 h1
  rw [mul_sub, h0] at h1
  exact sub_right_inj.mp h1

/-- The tensor slot identity (band `expDuh_Uker_theta`, `ExpDuhamel:131`, for abstract one-index kernels with `U i * T' i = T i`). -/
private theorem ExpDuhamelGen_U_theta {k : ℕ} (U T T' : Fin k → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (hUT : ∀ i, U i * T' i = T i) (A : (Fin k → Zd d (sz.L n)) → ℂ) (a : Fin k → Zd d (sz.L n)) :
    ∑ b : Fin k → Zd d (sz.L n), (∏ i, U i (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Zd d (sz.L n), T' i (b i) c * A (Function.update b i c)) =
      ∑ b : Fin k → Zd d (sz.L n), (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i, U j (a j) (b j)) * T i (a i) (b i)) * A b := by
  classical
  have step1 : ∑ b : Fin k → Zd d (sz.L n), (∏ i, U i (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Zd d (sz.L n), T' i (b i) c * A (Function.update b i c))
      = ∑ i : Fin k, ∑ b : Fin k → Zd d (sz.L n), ∑ c : Zd d (sz.L n),
          (∏ j, U j (a j) (b j)) * (T' i (b i) c * A (Function.update b i c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum]
  have step2 : ∀ i : Fin k,
      (∑ b : Fin k → Zd d (sz.L n), ∑ c : Zd d (sz.L n), (∏ j, U j (a j) (b j)) *
            (T' i (b i) c * A (Function.update b i c)))
        = ∑ e : Fin k → Zd d (sz.L n),
            ((∏ j ∈ Finset.univ.erase i, U j (a j) (e j)) * T i (a i) (e i)) * A e := by
    intro i
    rw [expDuh_sum_update_reindex i (fun b c => (∏ j, U j (a j) (b j)) *
      (T' i (b i) c * A (Function.update b i c)))]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hkey : ∀ x : Zd d (sz.L n),
        (∏ j, U j (a j) (Function.update e i x j)) *
            (T' i (Function.update e i x i) (e i) * A (Function.update (Function.update e i x) i (e i)))
          = ((∏ j ∈ Finset.univ.erase i, U j (a j) (e j)) * A e) * (U i (a i) x * T' i x (e i)) := by
      intro x
      have hprod : (∏ j, U j (a j) (Function.update e i x j))
          = U i (a i) x * ∏ j ∈ Finset.univ.erase i, U j (a j) (e j) := by
        rw [← Finset.mul_prod_erase Finset.univ (fun j => U j (a j) (Function.update e i x j)) (Finset.mem_univ i)]
        congr 1
        · rw [Function.update_self]
        · exact Finset.prod_congr rfl fun j hj => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have hup : Function.update (Function.update e i x) i (e i) = e := by
        rw [Function.update_idem, Function.update_eq_self]
      rw [hprod, hup, Function.update_self]
      ring
    simp_rw [hkey]
    rw [← Finset.mul_sum]
    have hmul : ∑ x : Zd d (sz.L n), U i (a i) x * T' i x (e i) = (U i * T' i) (a i) (e i) :=
      (Matrix.mul_apply).symm
    rw [hmul, hUT i]
    ring
  rw [step1]
  simp_rw [step2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]

/-- **`∂_v (𝒰_{v,t} Y_v) = 𝒰_{v,t}(Y' - Θ_v Y_v)`** (band `expDuh_hasDerivAt_Ugen`, `ExpDuhamel:210`), under the semigroup law, `0 ≤ u, t < 1`. -/
theorem ExpDuhamelGen_hasDerivAt_UN (h : Step2Gen_USemigroup C n) {k : ℕ} (σ : Fin k → Bool) {u t : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) (ht0 : 0 ≤ t) (ht1 : t < 1) {Y : ℝ → (Fin k → Zd d (sz.L n)) → ℂ} {Y' : (Fin k → Zd d (sz.L n)) → ℂ}
    (hY : ∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) (a : Fin k → Zd d (sz.L n)) :
    HasDerivAt (fun v => Step2Gen_UN C n σ v t (Y v) a)
      (Step2Gen_UN C n σ u t (fun b => Y' b - Step2Gen_ThetaN C n σ u (Y u) b) a) u := by
  classical
  have hterm : ∀ b : Fin k → Zd d (sz.L n),
      HasDerivAt (fun r : ℝ => (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) r t (a i) (b i)) * Y r b)
        ((∑ i, (∏ j ∈ Finset.univ.erase i, Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
            (-(Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)))) * Y u b +
          (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) * Y' b) u := by
    intro b
    have hprod : HasDerivAt (fun r : ℝ => ∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) r t (a i) (b i))
        (∑ i, (∏ j ∈ Finset.univ.erase i, Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
            (-(Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)))) u := by
      have h' := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin k)))
        (f := fun (i : Fin k) (r : ℝ) => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) r t (a i) (b i))
        (f' := fun i => -(Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)))
        (fun i _ => ExpDuhamelGen_hasDerivAt_uKer C n (σ i) (σ (finRotate k i)) t (a i) (b i) u)
      simpa only [smul_eq_mul] using h'
    exact hprod.mul (hY b)
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k → Zd d (sz.L n)))) (fun b _ => hterm b)
  refine hsum.congr_deriv ?_
  have hθ := ExpDuhamelGen_U_theta n (fun i => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t)
    (fun i => Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t)
    (fun i => Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u)
    (fun i => ExpDuhamelGen_uKer_mul_thetaKer C n h (σ i) (σ (finRotate k i)) hu0 hu1 ht0 ht1) (Y u) a
  have hθ' : ∑ b : Fin k → Zd d (sz.L n), (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) *
      Step2Gen_ThetaN C n σ u (Y u) b = ∑ b : Fin k → Zd d (sz.L n), (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i, Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
          Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)) * Y u b := hθ
  calc ∑ b : Fin k → Zd d (sz.L n), ((∑ i, (∏ j ∈ Finset.univ.erase i,
            Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
            (-(Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)))) * Y u b +
          (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) * Y' b)
      = ∑ b : Fin k → Zd d (sz.L n), (-((∑ i,
            (∏ j ∈ Finset.univ.erase i, Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
              Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)) * Y u b) +
          (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) * Y' b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [mul_neg, Finset.sum_neg_distrib]
        ring
    _ = -(∑ b : Fin k → Zd d (sz.L n), (∑ i : Fin k,
            (∏ j ∈ Finset.univ.erase i, Step2Gen_uKer C n (σ j) (σ (finRotate k j)) u t (a j) (b j)) *
              Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)) * Y u b) +
          ∑ b : Fin k → Zd d (sz.L n), (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) * Y' b := by
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = Step2Gen_UN C n σ u t (fun b => Y' b - Step2Gen_ThetaN C n σ u (Y u) b) a := by
        rw [← hθ']
        unfold Step2Gen_UN
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring

/-- `u ↦ (𝒰_{u,t} Y_u)_a` is continuous on `S` when every entry of `Y` is (band `expDuh_continuousOn_Ugen`, `ExpDuhamel:265`; no hypothesis on the times). -/
theorem ExpDuhamelGen_continuousOn_UN {k : ℕ} (σ : Fin k → Bool) (t : ℝ) {S : Set ℝ}
    {Y : ℝ → (Fin k → Zd d (sz.L n)) → ℂ} (hY : ∀ b, ContinuousOn (fun v => Y v b) S) (a : Fin k → Zd d (sz.L n)) :
    ContinuousOn (fun v => Step2Gen_UN C n σ v t (Y v) a) S := by
  unfold Step2Gen_UN
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact (continuous_finsetProd _ fun i _ =>
    ExpDuhamelGen_continuous_uKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)).continuousOn.mul (hY b)

/-- `u ↦ (𝒰_{u,t} D_u)_a` is interval integrable when every entry of `D` is (band `expDuh_intervalIntegrable_Ugen`, `ExpDuhamel:276`). -/
theorem ExpDuhamelGen_intervalIntegrable_UN {k : ℕ} (σ : Fin k → Bool) (s t : ℝ)
    {D : ℝ → (Fin k → Zd d (sz.L n)) → ℂ}
    (hD : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) (a : Fin k → Zd d (sz.L n)) :
    IntervalIntegrable (fun u => Step2Gen_UN C n σ u t (D u) a) MeasureTheory.volume s t := by
  unfold Step2Gen_UN
  have h := IntervalIntegrable.sum (Finset.univ : Finset (Fin k → Zd d (sz.L n)))
    (f := fun (b : Fin k → Zd d (sz.L n)) (u : ℝ) =>
      (∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) * D u b)
    (a := s) (b := t) (μ := MeasureTheory.volume) (fun b _ => by
      have hc : ContinuousOn (fun u : ℝ =>
          ∏ i, Step2Gen_uKer C n (σ i) (σ (finRotate k i)) u t (a i) (b i)) (Set.uIcc s t) :=
        (continuous_finsetProd _ fun i _ =>
          ExpDuhamelGen_continuous_uKer C n (σ i) (σ (finRotate k i)) t (a i) (b i)).continuousOn
      exact (hD b).continuousOn_mul hc)
  convert h using 1
  funext u
  simp [Finset.sum_apply]

/-- **The Duhamel engine from `s`** (band `expDuh_duhamel`, `ExpDuhamel:299`): if `Y` is continuous on `[s,t]`, `D` is interval integrable and `∂_u Y = Θ_u Y + D` on `(s,t)`,
then `Y_t = 𝒰_{s,t} Y_s + ∫_s^t 𝒰_{u,t} D_u du`, under the semigroup law of the carrier kernel. -/
theorem ExpDuhamelGen_duhamel (h : Step2Gen_USemigroup C n) {k : ℕ} (σ : Fin k → Bool) {s t : ℝ} (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) {Y D : ℝ → (Fin k → Zd d (sz.L n)) → ℂ}
    (hYc : ∀ b, ContinuousOn (fun u => Y u b) (Set.Icc s t))
    (hDi : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t)
    (hYd : ∀ u ∈ Set.Ioo s t, ∀ b, HasDerivAt (fun v => Y v b) (Step2Gen_ThetaN C n σ u (Y u) b + D u b) u)
    (a : Fin k → Zd d (sz.L n)) :
    Y t a = Step2Gen_UN C n σ s t (Y s) a + ∫ u in s..t, Step2Gen_UN C n σ u t (D u) a := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hcont := ExpDuhamelGen_continuousOn_UN C n σ t hYc a
  have hderiv : ∀ u ∈ Set.Ioo s t,
      HasDerivAt (fun v => Step2Gen_UN C n σ v t (Y v) a) (Step2Gen_UN C n σ u t (D u) a) u := by
    intro u hu
    have h' := ExpDuhamelGen_hasDerivAt_UN C n h σ (hs0.trans hu.1.le) (hu.2.trans ht1) ht0 ht1 (hYd u hu) a
    refine h'.congr_deriv ?_
    congr 1
    funext b
    ring
  have hint := ExpDuhamelGen_intervalIntegrable_UN C n σ s t hDi a
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont hderiv hint
  have hgt : Step2Gen_UN C n σ t t (Y t) a = Y t a := by
    rw [Step2Gen_UN_self C n h σ ht0 ht1 (Y t)]
  rw [hFTC, hgt]
  ring

end Kernel

/-! ## 2. The plain and zero-mode Duhamel formulas (target 13) -/

section ZeroMode

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ)

/-- `Q^{(A)} T` is the finite sum of the entries of `T` against the entries of `Q^{(A)}` of the unit tensors (linearity of `zeroModeSet`). -/
private theorem ExpDuhamelGen_zeroMode_expand {k : ℕ} (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ)
    (a : Fin k → Zd d (sz.L n)) :
    zeroModeSet d (sz.L n) A T a = ∑ b, T b * zeroModeSet d (sz.L n) A (Pi.single b 1) a := by
  classical
  have hT : T = ∑ b, T b • (Pi.single b (1 : ℂ) : (Fin k → Zd d (sz.L n)) → ℂ) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hT]
  rw [zeroModeSet_sum]
  simp only [zeroModeSet_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- `Q^{(A)}` commutes with the interval integral of a family of tensors with interval integrable entries. -/
private theorem ExpDuhamelGen_zeroMode_integral {k : ℕ} (A : Finset (Fin k)) {s t : ℝ}
    {T : ℝ → (Fin k → Zd d (sz.L n)) → ℂ} (hT : ∀ b, IntervalIntegrable (fun u => T u b) MeasureTheory.volume s t)
    (a : Fin k → Zd d (sz.L n)) :
    zeroModeSet d (sz.L n) A (fun b => ∫ u in s..t, T u b) a = ∫ u in s..t, zeroModeSet d (sz.L n) A (T u) a := by
  have hu : ∀ u, zeroModeSet d (sz.L n) A (T u) a = ∑ b, T u b * zeroModeSet d (sz.L n) A (Pi.single b 1) a :=
    fun u => ExpDuhamelGen_zeroMode_expand n A (T u) a
  rw [ExpDuhamelGen_zeroMode_expand n A (fun b => ∫ u in s..t, T u b) a]
  simp only [hu]
  rw [intervalIntegral.integral_finsetSum (fun b _ => (hT b).mul_const _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [intervalIntegral.integral_mul_const]

/-- **Target 13, `stExpDuhamelZgL_at`** (= `T2502_ExpDuhamelZAtOf`; band `stExpDuhamelZ_holds`, `ExpDuhamel:385`): from the hierarchy `STExpHierAtgL` at the index `n` and the
kernel window `Step2Gen_USemigroup C n`, the Duhamel identity for `f_u = 𝔼 𝓛^{(2)}_u - 𝒦^{(2)}_u` and the drift `D_u`, plain (`A = ∅`) and zero-mode (`Q^{(A)}` outside `𝒰`),
for `0 ≤ s ≤ t < 1`. -/
theorem stExpDuhamelZgL_at (h : Step2Gen_USemigroup C n) (hH : STExpHierAtgL C μ n) : STExpDuhamelZAtgL C μ n := by
  intro s t hs0 hst ht1 σ A a
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  have hDi : ∀ b : Fin 2 → Zd d (sz.L n), IntervalIntegrable (fun u => (∫ ω, STELKLKg C n u σ b ω ∂μ) +
      ∫ ω, STEGtg C n u σ b ω ∂μ) MeasureTheory.volume s t := fun b =>
    ((hH σ b).2.1.mono hI).intervalIntegrable_of_Icc hst
  have hplain : ∀ a' : Fin 2 → Zd d (sz.L n),
      ((∫ ω, C.L n t σ a' ω ∂μ) - C.K n t σ a') =
        Step2Gen_UN C n σ s t (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b) a' +
        ∫ u in s..t, Step2Gen_UN C n σ u t (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ) a' :=
    fun a' => ExpDuhamelGen_duhamel C n h σ hs0 hst ht1
      (Y := fun u b => (∫ ω, C.L n u σ b ω ∂μ) - C.K n u σ b)
      (D := fun u b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ)
      (fun b => (hH σ b).1.mono hI) hDi
      (fun u hu b => (hH σ b).2.2 u ⟨hs0.trans_lt hu.1, hu.2.trans ht1⟩) a'
  have hfun : (fun b : Fin 2 → Zd d (sz.L n) => (∫ ω, C.L n t σ b ω ∂μ) - C.K n t σ b) =
      Step2Gen_UN C n σ s t (fun b => (∫ ω, C.L n s σ b ω ∂μ) - C.K n s σ b) +
        fun a' => ∫ u in s..t, Step2Gen_UN C n σ u t
          (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ) a' :=
    funext fun a' => hplain a'
  rw [hfun, zeroModeSet_add]
  simp only [Pi.add_apply]
  congr 1
  exact ExpDuhamelGen_zeroMode_integral n A
    (T := fun u => Step2Gen_UN C n σ u t (fun b => (∫ ω, STELKLKg C n u σ b ω ∂μ) + ∫ ω, STEGtg C n u σ b ω ∂μ))
    (fun b => ExpDuhamelGen_intervalIntegrable_UN C n σ s t hDi b) a

end ZeroMode

/-! ## 3. The `𝒬`-Duhamel formula (abstract mollifier `ϑ`, from `s`) -/

section QForm

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (n : ℕ)

/-- Under the semigroup law, `1 - uX` is a unit for `0 ≤ u < 1` (`uKer u u = 1` and `Θ_u = Ring.inverse (1 - uX)`: a non-unit has inverse `0`). -/
private theorem ExpDuhamelGen_isUnit (h : Step2Gen_USemigroup C n) (σ σ' : Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    IsUnit (1 - (u : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) := by
  by_contra hU
  have h1 := (h σ σ' 0 u u hu0 hu1 hu0 hu1).1
  simp only [Step2Gen_uKer, Step2Gen_Theta] at h1
  rw [Ring.inverse_non_unit _ hU, mul_zero] at h1
  have : Nonempty (Zd d (sz.L n)) := ⟨fun _ => 0⟩
  exact zero_ne_one h1

/-- `u ↦ Θ_u = (1 - uX)⁻¹` is continuous at `0 ≤ u < 1` (band `expDuh_continuousAt_Theta_entry`, `ExpDuhamel:498`). -/
private theorem ExpDuhamelGen_continuousAt_Theta (h : Step2Gen_USemigroup C n) (σ σ' : Bool) {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u < 1) :
    ContinuousAt (fun r : ℝ => Step2Gen_Theta (Step2Kern_Mss C n σ σ' * C.S n) (r : ℂ)) u := by
  have hU := ExpDuhamelGen_isUnit C n h σ σ' hu0 hu1
  have h1 : ContinuousAt (Ring.inverse (M₀ := Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ))
      (1 - (u : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) := by
    have hspec : ((hU.unit : (Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)ˣ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) =
        1 - (u : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n) := IsUnit.unit_spec _
    rw [← hspec]
    exact (hasFDerivAt_ringInverse (𝕜 := ℝ) hU.unit).continuousAt
  have h2 : ContinuousAt (fun r : ℝ => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) -
      (r : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) u :=
    continuousAt_const.sub (Complex.continuous_ofReal.continuousAt.smul continuousAt_const)
  exact ContinuousAt.comp (g := Ring.inverse (M₀ := Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ))
    (f := fun r : ℝ => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) - (r : ℂ) • (Step2Kern_Mss C n σ σ' * C.S n)) h1 h2

/-- The kernel `(thetaKer u)_{xy}` is continuous in `u` on `[0,1)` (band `expDuh_continuousOn_thetaKer`, `ExpDuhamel:508`). -/
private theorem ExpDuhamelGen_continuousOn_thetaKer (h : Step2Gen_USemigroup C n) (σ σ' : Bool) {S : Set ℝ}
    (hS : S ⊆ Set.Ico 0 1) (x y : Zd d (sz.L n)) :
    ContinuousOn (fun u : ℝ => Step2Gen_thetaKer C n σ σ' u x y) S := by
  simp only [Step2Gen_thetaKer, Matrix.mul_apply]
  refine continuousOn_finsetSum _ fun z _ => continuousOn_const.mul fun u hu => ?_
  have hc := ExpDuhamelGen_continuousAt_Theta C n h σ σ' (hS hu).1 (hS hu).2
  exact (((continuous_apply y).comp (continuous_apply z)).continuousAt.comp hc).continuousWithinAt

/-- `Θ^{(k)}_{u,σ}` preserves continuity in `u` on a window `S ⊆ [0,1)` (band `expDuh_continuousOn_ThetaN`, `ExpDuhamel:517`). -/
private theorem ExpDuhamelGen_continuousOn_ThetaN (h : Step2Gen_USemigroup C n) {k : ℕ} (σ : Fin k → Bool) {S : Set ℝ}
    (hS : S ⊆ Set.Ico 0 1) {Y : ℝ → (Fin k → Zd d (sz.L n)) → ℂ} (hY : ∀ b, ContinuousOn (fun u => Y u b) S)
    (a : Fin k → Zd d (sz.L n)) : ContinuousOn (fun u => Step2Gen_ThetaN C n σ u (Y u) a) S := by
  unfold Step2Gen_ThetaN
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun b _ => ?_
  exact (ExpDuhamelGen_continuousOn_thetaKer C n h (σ i) (σ (finRotate k i)) hS (a i) b).mul
    (hY (Function.update a i b))

/-- **Target 13, `stExpDuhamelQgL_at`** (band `stExpDuhamelQ_holds`, `ExpDuhamel:570`): the engine at `Y_u = 𝒬_u f_u`, whose source is `STExpQsrcg`
(`𝒬D + [𝒬,Θ] f - (𝒫 f) ∂_uϑ`, `6:109-116`): `𝒬` of a mollifier family `ϑ` with `STMollifierProps` at the coupling `sz.lam n`. -/
theorem stExpDuhamelQgL_at (h : Step2Gen_USemigroup C n) (hH : STExpHierAtgL C μ n) : STExpDuhamelQAtgL C μ n := by
  intro Cq c ϑ hϑ s t hs0 hst ht1 σ a
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  have hcf : ∀ b : Fin 2 → Zd d (sz.L n), ContinuousOn (fun u => (∫ ω, C.L n u σ b ω ∂μ) - C.K n u σ b)
      (Set.Icc s t) := fun b => (hH σ b).1.mono hI
  have hcD : ∀ b : Fin 2 → Zd d (sz.L n), ContinuousOn (fun u => (∫ ω, STELKLKg C n u σ b ω ∂μ) +
      ∫ ω, STEGtg C n u σ b ω ∂μ) (Set.Icc s t) := fun b => (hH σ b).2.1.mono hI
  -- continuity of the pieces of the source on `[s,t]`
  have hθf : ∀ b' : Fin 2 → Zd d (sz.L n), ContinuousOn (fun u => Step2Gen_ThetaN C n σ u
      (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') b') (Set.Icc s t) := fun b' =>
    ExpDuhamelGen_continuousOn_ThetaN C n h σ hI hcf b'
  have hQf : ∀ b' : Fin 2 → Zd d (sz.L n), ContinuousOn (fun u => STQop (d := d) ϑ u
      (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') b') (Set.Icc s t) := fun b' =>
    expDuh_continuousOn_Qop_gen hϑ hI hcf b'
  have hint : ∀ b : Fin 2 → Zd d (sz.L n), IntervalIntegrable (fun u =>
      STQop (d := d) ϑ u (fun c' => (∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ) b +
        (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b -
          Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) -
        STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') (b 0) * deriv (fun τ => ϑ τ b) u)
      MeasureTheory.volume s t := fun b => by
    have hQD : ContinuousOn (fun u => STQop (d := d) ϑ u (fun c' => (∫ ω, STELKLKg C n u σ c' ω ∂μ) +
        ∫ ω, STEGtg C n u σ c' ω ∂μ) b) (Set.Icc s t) := expDuh_continuousOn_Qop_gen hϑ hI hcD b
    have hQθf : ContinuousOn (fun u => STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u
        (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) (Set.Icc s t) :=
      expDuh_continuousOn_Qop_gen hϑ hI hθf b
    have hθQf : ContinuousOn (fun u => Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u
        (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) (Set.Icc s t) :=
      ExpDuhamelGen_continuousOn_ThetaN C n h σ hI hQf b
    have hPf : ContinuousOn (fun u => STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') (b 0))
        (Set.Icc s t) := by
      unfold STPsum
      exact continuousOn_finsetSum _ fun b' _ => hcf b'
    have hdv := expDuh_intervalIntegrable_deriv hϑ (by have := sz.three_le_L n; omega : 1 ≤ sz.L n) hs0 hst ht1 b
    have hprod : IntervalIntegrable (fun u => STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')
        (b 0) * deriv (fun τ => ϑ τ b) u) MeasureTheory.volume s t :=
      hdv.continuousOn_mul (by rwa [Set.uIcc_of_le hst])
    exact ((hQD.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst).add
      ((hQθf.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst).sub
        (hθQf.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst))).sub hprod
  exact ExpDuhamelGen_duhamel C n h σ hs0 hst ht1
    (Y := fun u b => STQop (d := d) ϑ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') b)
    (D := fun u b => STQop (d := d) ϑ u (fun c' => (∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ) b +
        (STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b -
          Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c')) b) -
        STPsum (d := d) (fun c' => (∫ ω, C.L n u σ c' ω ∂μ) - C.K n u σ c') (b 0) * deriv (fun τ => ϑ τ b) u)
    (fun b => expDuh_continuousOn_Qop_gen hϑ hI hcf b) hint
    (fun u hu b => by
      have hu0 : 0 < u := hs0.trans_lt hu.1
      have hu1 : u < 1 := hu.2.trans ht1
      have hA : ∀ c' : Fin 2 → Zd d (sz.L n), HasDerivAt (fun v => (∫ ω, C.L n v σ c' ω ∂μ) - C.K n v σ c')
          (Step2Gen_ThetaN C n σ u (fun b' => (∫ ω, C.L n u σ b' ω ∂μ) - C.K n u σ b') c' +
            ((∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ)) u := fun c' =>
        (hH σ c').2.2 u ⟨hu0, hu1⟩
      have hϑd : ∀ c' : Fin 2 → Zd d (sz.L n), HasDerivAt (fun τ => ϑ τ c') (deriv (fun τ => ϑ τ c') u) u := fun c' =>
        ((hϑ.2.2.1 c').differentiableAt (Ico_mem_nhds hu0 hu1)).hasDerivAt
      have hq := QopAlgebra_Qop_hasDerivAt (d := d) (ϑ := ϑ) (A := fun v c' => (∫ ω, C.L n v σ c' ω ∂μ) - C.K n v σ c')
        (A' := fun c' => Step2Gen_ThetaN C n σ u (fun b' => (∫ ω, C.L n u σ b' ω ∂μ) - C.K n u σ b') c' +
          ((∫ ω, STELKLKg C n u σ c' ω ∂μ) + ∫ ω, STEGtg C n u σ c' ω ∂μ))
        (ϑ' := fun c' => deriv (fun τ => ϑ τ c') u) hA hϑd b
      refine hq.congr_deriv ?_
      have e : ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ, STQop (d := d) ϑ u X = fun a' => X a' - STPsum (d := d) X (a' 0) * ϑ u a' :=
        fun X => rfl
      simp only [e, STPsum, Finset.sum_add_distrib]
      ring) a

end QForm

/-! ## 4. The eventual family forms and the band re-derivations (target 13) -/

section Family

/-- **Target 13, `stExpDuhamelZgL_ev`** (= `STExpDuhamelZgL d law Flow mk`; family-table rows 9-13, premises inline): the hypotheses of `stExpHiergL_ev` and the kernel window
`Step2Gen_USemigroup (mk sz z) n` eventually in `n` (row 13; BA: first conjunct of `baIniTermGen_kerFacts`, every `n`).  The eventual form is UP-C4 / answer (5). -/
theorem stExpDuhamelZgL_ev {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (hmk : ∀ (sz : Sizes d) (z : ℕ → ℂ), (mkM sz z).toFlowFM = mk sz z)
    (hrep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ StepDecompGen_LoopForm (mkM sz z) E ∧
          ∀ n, (mkM sz z).S n = SB d (sz.L n) (g' n))
    (hcls : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (mkM sz z) n ∧ HierDriftGen_KTwo (mkM sz z) n ∧
        HierDriftGen_KLink (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, Step2Gen_USemigroup (mk sz z) n) :
    STExpDuhamelZgL d law Flow mk := by
  intro sz κ ε 𝔠 𝔡 z hκ hf
  filter_upwards [stExpHiergL_ev law Flow mk mkM hmk hrep hcls sz κ ε 𝔠 𝔡 z hκ hf, hU sz κ ε 𝔠 𝔡 z hκ hf] with n hH hUn
  exact stExpDuhamelZgL_at (mk sz z) (law sz) n hUn hH

/-- **Target 13, `stExpDuhamelQgL_ev`** (= `STExpDuhamelQgL d law Flow mk`; same premises as `stExpDuhamelZgL_ev`). -/
theorem stExpDuhamelQgL_ev {d : ℕ} (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) (hmk : ∀ (sz : Sizes d) (z : ℕ → ℂ), (mkM sz z).toFlowFM = mk sz z)
    (hrep : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ (H₀ : ∀ n, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (g' E : ℕ → ℝ),
        CltRepg (mk sz z) (law sz) H₀ g' E ∧ StepDecompGen_LoopForm (mkM sz z) E ∧
          ∀ n, (mkM sz z).S n = SB d (sz.L n) (g' n))
    (hcls : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, HierDriftGen_KLoop (mkM sz z) n ∧ HierDriftGen_KTwo (mkM sz z) n ∧
        HierDriftGen_KLink (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, Step2Gen_USemigroup (mk sz z) n) :
    STExpDuhamelQgL d law Flow mk := by
  intro sz κ ε 𝔠 𝔡 z hκ hf
  filter_upwards [stExpHiergL_ev law Flow mk mkM hmk hrep hcls sz κ ε 𝔠 𝔡 z hκ hf, hU sz κ ε 𝔠 𝔡 z hκ hf] with n hH hUn
  exact stExpDuhamelQgL_at (mk sz z) (law sz) n hUn hH

/-- **Target 13, band re-derivation of `stExpDuhamelZ_holds`** (`ExpDuhamel:385`) from `stExpDuhamelZgL_at` at `bandFM sz (fun _ => E)`: the band window is
`step2Gen_USemigroup_band`, the hierarchy is `stExpHiergL_at` at the band classes, `Ugen = Step2Gen_UN` is `bandStep2_Ugen`. -/
theorem stExpDuhamelZ_of_gL (d : ℕ) : STExpDuhamelZ d := by
  intro _ sz n E hE s t hs0 hst ht1 σ A a
  have hH : STExpHierAtgL (bandFM sz (fun _ => E)) (Sizes.seqP sz) n :=
    stExpHiergL_at (bandStep2Mat sz (fun _ => E)) (Sizes.seqP sz) (fun _ => 0) sz.lam (fun _ => E) n
      (cltRepg_band sz _) (stepDecompGen_loopForm_band sz _ (fun _ => hE)) rfl
      (hierDriftGen_kLoop_band sz _ (fun _ => hE) n) (hierDriftGen_kTwo_band sz _ (fun _ => hE) n)
      (hierDriftGen_kLink_band sz _ n)
  have h := stExpDuhamelZgL_at (bandFM sz (fun _ => E)) (Sizes.seqP sz) n
    (step2Gen_USemigroup_band sz (fun _ => E) n hE.le) hH s t hs0 hst ht1 σ A a
  simp only [bandStep2_Ugen sz (fun _ => E) n]
  exact h

/-- **Target 13, band re-derivation of `stExpDuhamelQ_holds`** (`ExpDuhamel:570`), through `bandStep2_Ugen` and `bandFM_STExpQsrc`. -/
theorem stExpDuhamelQ_of_gL (d : ℕ) : STExpDuhamelQ d := by
  intro _ sz n E hE Cq c ϑ hϑ s t hs0 hst ht1 σ a
  have hH : STExpHierAtgL (bandFM sz (fun _ => E)) (Sizes.seqP sz) n :=
    stExpHiergL_at (bandStep2Mat sz (fun _ => E)) (Sizes.seqP sz) (fun _ => 0) sz.lam (fun _ => E) n
      (cltRepg_band sz _) (stepDecompGen_loopForm_band sz _ (fun _ => hE)) rfl
      (hierDriftGen_kLoop_band sz _ (fun _ => hE) n) (hierDriftGen_kTwo_band sz _ (fun _ => hE) n)
      (hierDriftGen_kLink_band sz _ n)
  have h := stExpDuhamelQgL_at (bandFM sz (fun _ => E)) (Sizes.seqP sz) n
    (step2Gen_USemigroup_band sz (fun _ => E) n hE.le) hH Cq c ϑ hϑ s t hs0 hst ht1 σ a
  simp only [bandStep2_Ugen sz (fun _ => E) n, bandFM_STExpQsrc sz (fun _ => E) n]
  exact h

end Family

/-! ## 5. Compiled nonempty instances (target 13)

Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `lam = 1/64`), the band carrier at `E = 1/2`, `H₀ = 0`, `g' = sz0.lam`, `[s,t] = [1/4, 1/2]`, `σ = (+,-)`, the loop label `a = (0, e₁)`,
`A = {0,1}` (both indices); the `𝒬` form for a mollifier of `stMollifierEx_holds`.  The kernel window is the band theorem `step2Gen_USemigroup_band`, the hierarchy is `stExpHiergL_at_inst`; nothing stays a hypothesis. -/

section Instances

open RBM.Gauss.SizesInst

theorem stExpDuhamelZgL_at_inst : STExpDuhamelZAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0 :=
  stExpDuhamelZgL_at _ _ 0 (step2Gen_USemigroup_band sz0 (fun _ => 1 / 2) 0 (by norm_num)) stExpHiergL_at_inst

theorem stExpDuhamelQgL_at_inst : STExpDuhamelQAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0 :=
  stExpDuhamelQgL_at _ _ 0 (step2Gen_USemigroup_band sz0 (fun _ => 1 / 2) 0 (by norm_num)) stExpHiergL_at_inst

/-- The zero-mode identity at the data above (both indices, `Q^{(A)}` outside `𝒰`), applied: a statement with concrete numbers, not a restatement of the pin. -/
example : zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
      (fun b => (∫ ω, (bandFM sz0 (fun _ => 1 / 2)).L 0 (1 / 2) ![true, false] b ω ∂(Sizes.seqP sz0)) -
        (bandFM sz0 (fun _ => 1 / 2)).K 0 (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
    zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
      (Step2Gen_UN (bandFM sz0 (fun _ => 1 / 2)) 0 ![true, false] (1 / 4) (1 / 2)
        (fun b => (∫ ω, (bandFM sz0 (fun _ => 1 / 2)).L 0 (1 / 4) ![true, false] b ω ∂(Sizes.seqP sz0)) -
          (bandFM sz0 (fun _ => 1 / 2)).K 0 (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
      ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (Step2Gen_UN (bandFM sz0 (fun _ => 1 / 2)) 0 ![true, false] u (1 / 2)
          (fun b => (∫ ω, STELKLKg (bandFM sz0 (fun _ => 1 / 2)) 0 u ![true, false] b ω ∂(Sizes.seqP sz0)) +
            ∫ ω, STEGtg (bandFM sz0 (fun _ => 1 / 2)) 0 u ![true, false] b ω ∂(Sizes.seqP sz0))) ![0, Pi.single 0 1] :=
  stExpDuhamelZgL_at_inst (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num) ![true, false] Finset.univ
    ![0, Pi.single 0 1]

/-- The `𝒬` form for some mollifier of `stMollifierEx_holds` at the same data. -/
example : ∃ (Cq c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) Cq c ϑ ∧
    STQop (d := 3) ϑ (1 / 2) (fun b => (∫ ω, (bandFM sz0 (fun _ => 1 / 2)).L 0 (1 / 2) ![true, false] b ω ∂(Sizes.seqP sz0)) -
        (bandFM sz0 (fun _ => 1 / 2)).K 0 (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
      Step2Gen_UN (bandFM sz0 (fun _ => 1 / 2)) 0 ![true, false] (1 / 4) (1 / 2)
        (STQop (d := 3) ϑ (1 / 4) (fun b => (∫ ω, (bandFM sz0 (fun _ => 1 / 2)).L 0 (1 / 4) ![true, false] b ω ∂(Sizes.seqP sz0)) -
          (bandFM sz0 (fun _ => 1 / 2)).K 0 (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
      ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), Step2Gen_UN (bandFM sz0 (fun _ => 1 / 2)) 0 ![true, false] u (1 / 2)
        (STExpQsrcg (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) 0 u ![true, false] ϑ) ![0, Pi.single 0 1] := by
  obtain ⟨C, c, hC, hc, hex⟩ := stMollifierEx_holds 3 (by norm_num) 1 1 one_pos
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ 1 := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  obtain ⟨ϑ, hϑ⟩ := hex (sz0.L 0) (sz0.three_le_L 0) (sz0.lam 0) hlam hlam'
  exact ⟨C, c, ϑ, hϑ, stExpDuhamelQgL_at_inst C c ϑ hϑ (1 / 4) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] ![0, Pi.single 0 1]⟩

/-- Target 13, the eventual forms at the band tuple, `Flow = True`, applied at `sz0`. -/
theorem stExpDuhamelZgL_ev_inst : STExpDuhamelZgL 3 (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True)
    (fun sz _ => bandFM sz (fun _ => 1 / 2)) :=
  stExpDuhamelZgL_ev (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True) (fun sz _ => bandFM sz (fun _ => 1 / 2))
    (fun sz _ => bandStep2Mat sz (fun _ => 1 / 2)) (fun _ _ => rfl)
    (fun sz _ _ _ _ _ _ _ => ⟨fun _ => 0, sz.lam, fun _ => 1 / 2, cltRepg_band sz _,
      stepDecompGen_loopForm_band sz _ (fun _ => by norm_num), fun _ => rfl⟩)
    (fun sz _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun n =>
      ⟨hierDriftGen_kLoop_band sz _ (fun _ => by norm_num) n, hierDriftGen_kTwo_band sz _ (fun _ => by norm_num) n,
        hierDriftGen_kLink_band sz _ n⟩)
    (fun sz _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun n => step2Gen_USemigroup_band sz (fun _ => 1 / 2) n (by norm_num))

theorem stExpDuhamelQgL_ev_inst : STExpDuhamelQgL 3 (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True)
    (fun sz _ => bandFM sz (fun _ => 1 / 2)) :=
  stExpDuhamelQgL_ev (fun sz => Sizes.seqP sz) (fun _ _ _ _ _ _ => True) (fun sz _ => bandFM sz (fun _ => 1 / 2))
    (fun sz _ => bandStep2Mat sz (fun _ => 1 / 2)) (fun _ _ => rfl)
    (fun sz _ _ _ _ _ _ _ => ⟨fun _ => 0, sz.lam, fun _ => 1 / 2, cltRepg_band sz _,
      stepDecompGen_loopForm_band sz _ (fun _ => by norm_num), fun _ => rfl⟩)
    (fun sz _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun n =>
      ⟨hierDriftGen_kLoop_band sz _ (fun _ => by norm_num) n, hierDriftGen_kTwo_band sz _ (fun _ => by norm_num) n,
        hierDriftGen_kLink_band sz _ n⟩)
    (fun sz _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun n => step2Gen_USemigroup_band sz (fun _ => 1 / 2) n (by norm_num))

/-- The consumer chain: row a's `st6_duhEq_of_ping` accepts `stExpDuhamelZgL_ev` (`STExpDuhEqgL` along the constant window `[1/4, 1/2]`, band tuple, `Flow = True`). -/
example : STExpDuhEqgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) (fun _ => 1 / 4) (fun _ => 1 / 2) :=
  st6_duhEq_of_ping stExpDuhamelZgL_ev_inst (sz := sz0) (κ := 1) (ε := 1) (𝔠 := 1) (𝔡 := 1) one_pos (z := fun _ => 0)
    trivial (fun _ => by norm_num) (fun _ => by norm_num)

example : ∃ n : ℕ, STExpDuhamelZAtgL (bandFM sz0 (fun _ => 1 / 2)) (Sizes.seqP sz0) n :=
  (stExpDuhamelZgL_ev_inst sz0 1 1 1 1 (fun _ => 0) one_pos trivial).exists

/-- The band re-derivations at `d = 3`: the band pins `STExpDuhamelZ 3`, `STExpDuhamelQ 3` from the generic proofs. -/
example : STExpDuhamelZ 3 ∧ STExpDuhamelQ 3 := ⟨stExpDuhamelZ_of_gL 3, stExpDuhamelQ_of_gL 3⟩

end Instances

end RBM.BA
