/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.KKernel
import RBM3D.Propagator.Deriv

/-!
# Stage K, row K00: the repaired `M`-loop carrier and the `Θ_BA` calculus

Ticket T2362 (design BA-DK, `docs/reports/T2360-design.md` §3 F1, §4 row K00).

1. `BAMLoop` (`BA/FlowPins.lean:272-276`) now pairs the charge `σ_i` with the edge
   `(a_{i-1}, a_i)` (cyclic), as `(eq:KMloop)` (`1_2:1003`), the tree rule `A:571`, `loopM`
   (`Loop/GLoopFlow.lean:92`) and `cutGlueL/R` (`Loop/TreeRep.lean:75-82`).  Here: its index form
   `BAMLoop_apply`, the agreement with the old pairing for `n ≤ 2` and symmetric `M(σ)`
   (`BAMLoop_le_two`), the witness `BAMLoop_witness` and the trace form `BAMLoop_trace`.
2. The `Θ_BA` calculus at real `t ∈ [0,1)` and every charge pair `(σ₁, σ₂)`: invertibility of
   `1 - t M^{(σ₁σ₂)}`, the resolvent identities, `∂_tΘ = ΘMΘ` (entrywise), the swap
   `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}`, `Θ^{(-,-)} = conj Θ^{(+,+)}`, symmetry, and the row sums of
   `Θ^{(+,-)}`.  The twin of `Propagator/{Basic,Deriv}.lean` with `Q = M^{(σ₁σ₂)}` in place of
   `μ S^{(B)}`; the only input is `‖Q‖_{∞→∞} ≤ 1` from `|Q_ab| = BAK_ab` and the Ward row sums of
   `BAK` (`KKernel.lean`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

noncomputable section

open Matrix Filter Topology
open scoped Kronecker

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss

/-! ## 1. The repaired carrier `BAMLoop` -/

section Loop

variable (d L W : ℕ) [NeZero L]

omit [NeZero L] in
/-- **Index form of `BAMLoop`** (`(eq:KMloop)`, `1_2:1003`).  Convention: for a loop index `I` with
`I.σ.length = I.a.length = n ≥ 1`, `σ_i = I.σ.getD i false` and `a_i = I.a.getD i 0` (`0 ≤ i < n`), and the
cyclic predecessor is `a_{i-1} = I.a.getD ((i + (n - 1)) % n) 0`, so that `a_{-1} = a_{n-1}`:
`BAMLoop = W^{-(n-1)d} ∏_{i<n} M(σ_i)_{a_{i-1} a_i}`. -/
theorem BAMLoop_apply (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (I : LoopIdx (Zd d L)) (n : ℕ)
    (hn : 1 ≤ n) (hσ : I.σ.length = n) (ha : I.a.length = n) :
    BAMLoop d L W M I = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
      ∏ i ∈ Finset.range n, M (I.σ.getD i false) (I.a.getD ((i + (n - 1)) % n) 0) (I.a.getD i 0) := by
  have hlen : I.length = n := ha
  have hl : (I.σ.zip ((I.a.rotate (I.length - 1)).zip I.a)).map (fun p => M p.1 p.2.1 p.2.2) =
      List.ofFn (fun i : Fin n =>
        M (I.σ.getD i false) (I.a.getD ((i + (n - 1)) % n) 0) (I.a.getD i 0)) := by
    refine List.ext_getElem (by simp [hσ, ha, hlen]) fun i h1 h2 => ?_
    have hi : i < n := by simpa using h2
    have hσi : i < I.σ.length := by omega
    have hai : i < I.a.length := by omega
    have hrot : i < (I.a.rotate (I.length - 1)).length := by simpa using hai
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, List.getElem_rotate,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hσi, List.getElem?_eq_getElem hai]
    have hmod : (i + (n - 1)) % n < I.a.length := by rw [ha]; exact Nat.mod_lt _ (by omega)
    rw [List.getElem?_eq_getElem hmod]
    have e1 : (i + (I.length - 1)) % I.a.length = (i + (n - 1)) % n := by rw [hlen, ha]
    simp only [Option.getD_some, e1]
  unfold BAMLoop
  rw [hl, List.prod_ofFn, hlen, Fin.prod_univ_eq_prod_range
    (fun i => M (I.σ.getD i false) (I.a.getD ((i + (n - 1)) % n) 0) (I.a.getD i 0)) n]

omit [NeZero L] in
/-- For `n ≤ 2` and symmetric `M(σ)` the repaired `BAMLoop` equals the old body of `BAMLoop`
(`σ_i` with `(a_i, a_{i+1})`, `I.a.zip (I.a.rotate 1)`): the merged `n ≤ 2` facts are untouched.
No relation between `I.σ.length` and `I.length = I.a.length` is needed. -/
theorem BAMLoop_le_two (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (hM : ∀ σ, (M σ)ᵀ = M σ)
    (I : LoopIdx (Zd d L)) (hn : I.length ≤ 2) :
    BAMLoop d L W M I = (((W : ℂ) ^ d)⁻¹) ^ (I.length - 1) *
      ((I.σ.zip (I.a.zip (I.a.rotate 1))).map fun p => M p.1 p.2.1 p.2.2).prod := by
  have hs : ∀ (s : Bool) (x y : Zd d L), M s x y = M s y x := fun s x y => by
    have := congrFun (congrFun (hM s) y) x
    simpa using this
  obtain ⟨σ, a⟩ := I
  unfold BAMLoop
  simp only [LoopIdx.length] at hn ⊢
  match a, hn with
  | [], _ => simp
  | [x], _ => simp
  | [x, y], _ =>
    match σ with
    | [] => simp
    | [s] => simp [List.rotate, hs s x y]
    | s :: t :: rest => simp [List.rotate, hs s x y, hs t x y]

/-- The witness of the repair: `M(+) = N`, `M(-) = N'` symmetric `3 × 3` matrices on `Z_3` (`d = 1`, `W = 1`)
with `N_{01} = 1, N_{12} = 2, N_{20} = 3` and `N'_{01} = 1, N'_{12} = 5, N'_{20} = 7`. -/
def BAMLoop_witM (σ : Bool) : Matrix (Zd 1 3) (Zd 1 3) ℂ :=
  Matrix.of fun x y => if σ then ![![0, 1, 3], ![1, 0, 2], ![3, 2, 0]] (x 0) (y 0)
    else ![![0, 1, 7], ![1, 0, 5], ![7, 5, 0]] (x 0) (y 0)

/-- The repaired value at the loop `(+,+,-)`, labels `(0,1,2)`: `σ_i` on the edge `(a_{i-1}, a_i)` gives
`N_{20} N_{01} N'_{12} = 3 · 1 · 5 = 15` (`(eq:KMloop)`; the old body gave `N_{01} N_{12} N'_{20} = 14`). -/
theorem BAMLoop_witness :
    BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ = 15 := by
  have e : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ =
      (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ 2 * (BAMLoop_witM true ![2] ![0] * (BAMLoop_witM true ![0] ![1] *
        (BAMLoop_witM false ![1] ![2] * 1))) := by
    unfold BAMLoop; rfl
  have h1 : BAMLoop_witM true (![2] : Zd 1 3) ![0] = 3 := rfl
  have h2 : BAMLoop_witM true (![0] : Zd 1 3) ![1] = 1 := rfl
  have h3 : BAMLoop_witM false (![1] : Zd 1 3) ![2] = 5 := rfl
  rw [e, h1, h2, h3]; norm_num

/-- The old pairing `(a_i, a_{i+1})` (the body of `BAMLoop` before T2362) gives `14` at the same data:
the repair changes the value for `n = 3`. -/
theorem BAMLoop_witness_old :
    (((((1 : ℕ) : ℂ) ^ 1)⁻¹) ^ (([true, true, false] : List Bool).length - 1) *
      ((([true, true, false] : List Bool).zip (([![0], ![1], ![2]] : List (Zd 1 3)).zip
        (([![0], ![1], ![2]] : List (Zd 1 3)).rotate 1))).map
          fun p => BAMLoop_witM p.1 p.2.1 p.2.2).prod) = 14 := by
  have e : (((((1 : ℕ) : ℂ) ^ 1)⁻¹) ^ (([true, true, false] : List Bool).length - 1) *
      ((([true, true, false] : List Bool).zip (([![0], ![1], ![2]] : List (Zd 1 3)).zip
        (([![0], ![1], ![2]] : List (Zd 1 3)).rotate 1))).map
          fun p => BAMLoop_witM p.1 p.2.1 p.2.2).prod) =
      (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ 2 * (BAMLoop_witM true ![0] ![1] * (BAMLoop_witM true ![1] ![2] *
        (BAMLoop_witM false ![2] ![0] * 1))) := by
    rfl
  have h1 : BAMLoop_witM true (![0] : Zd 1 3) ![1] = 1 := rfl
  have h2 : BAMLoop_witM true (![1] : Zd 1 3) ![2] = 2 := rfl
  have h3 : BAMLoop_witM false (![2] : Zd 1 3) ![0] = 7 := rfl
  rw [e, h1, h2, h3]; norm_num

end Loop

/-! ## 2. The `Θ_BA` calculus at real `t ∈ [0,1)` -/

/-! ### 2a. Generic `Q` with `‖Q‖_{∞→∞} ≤ 1` (the twin of `Propagator/{Basic,Deriv}.lean`) -/

section Generic

open scoped NNReal Matrix.Norms.Operator

variable {d L : ℕ} [NeZero L] {Q : Matrix (Zd d L) (Zd d L) ℂ}

/-- Row sums of `|Q|` at most `1` give `‖Q‖_{∞→∞} ≤ 1`. -/
private theorem BAKBase_norm_le (hQ : ∀ a, ∑ b, ‖Q a b‖ ≤ 1) : ‖Q‖ ≤ 1 := by
  have h : ‖Q‖₊ ≤ 1 := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun a _ => ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_sum, NNReal.coe_one]
    simpa using hQ a
  exact_mod_cast h

private theorem BAKBase_isUnit (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    IsUnit (1 - (t : ℂ) • Q) := by
  have h : ‖(t : ℂ) • Q‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖Q‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hQ (abs_nonneg t)
      _ < 1 := by rwa [mul_one]
  exact ⟨Units.oneSub _ h, Units.val_oneSub _ _⟩

private theorem BAKBase_mul (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    PropThetaQ Q t * (1 - (t : ℂ) • Q) = 1 :=
  Ring.inverse_mul_cancel _ (BAKBase_isUnit hQ ht)

private theorem BAKBase_mul' (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    (1 - (t : ℂ) • Q) * PropThetaQ Q t = 1 :=
  Ring.mul_inverse_cancel _ (BAKBase_isUnit hQ ht)

/-- A left inverse of a unit is its `Ring.inverse`. -/
private theorem BAKBase_eq_inverse {x y : Matrix (Zd d L) (Zd d L) ℂ} (hx : IsUnit x) (h : y * x = 1) :
    y = Ring.inverse x := by
  calc y = y * (x * Ring.inverse x) := by rw [Ring.mul_inverse_cancel x hx, mul_one]
    _ = (y * x) * Ring.inverse x := (mul_assoc _ _ _).symm
    _ = Ring.inverse x := by rw [h, one_mul]

private theorem BAKBase_resolvent_left (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    PropThetaQ Q t = 1 + (t : ℂ) • (Q * PropThetaQ Q t) := by
  have h := BAKBase_mul' hQ ht
  rw [sub_mul, one_mul, smul_mul_assoc] at h
  exact sub_eq_iff_eq_add.mp h

private theorem BAKBase_resolvent_right (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    PropThetaQ Q t = 1 + (t : ℂ) • (PropThetaQ Q t * Q) := by
  have h := BAKBase_mul hQ ht
  rw [mul_sub, mul_one, mul_smul_comm] at h
  exact sub_eq_iff_eq_add.mp h

private theorem BAKBase_transpose (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) (hs : Qᵀ = Q) :
    (PropThetaQ Q t)ᵀ = PropThetaQ Q t := by
  have hsym : (1 - (t : ℂ) • Q)ᵀ = 1 - (t : ℂ) • Q := by
    rw [transpose_sub, transpose_one, transpose_smul, hs]
  refine BAKBase_eq_inverse (BAKBase_isUnit hQ ht) ?_
  calc (PropThetaQ Q t)ᵀ * (1 - (t : ℂ) • Q)
      = (PropThetaQ Q t)ᵀ * (1 - (t : ℂ) • Q)ᵀ := by rw [hsym]
    _ = ((1 - (t : ℂ) • Q) * PropThetaQ Q t)ᵀ := (transpose_mul _ _).symm
    _ = 1 := by rw [BAKBase_mul' hQ ht, transpose_one]

/-- The Neumann/resolvent bound is the only input of continuity: `s ↦ Θ_s` is continuous at `t`, `|t| < 1`. -/
private theorem BAKBase_continuousAt (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) :
    ContinuousAt (fun s : ℝ => PropThetaQ Q s) t := by
  obtain ⟨u, hu⟩ := BAKBase_isUnit hQ ht
  have hinv : ContinuousAt (Ring.inverse : Matrix (Zd d L) (Zd d L) ℂ → _) (1 - (t : ℂ) • Q) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hlin : ContinuousAt (fun s : ℝ => 1 - (s : ℂ) • Q) t :=
    continuousAt_const.sub ((Complex.continuous_ofReal.continuousAt).smul continuousAt_const)
  exact ContinuousAt.comp (g := Ring.inverse) (f := fun s : ℝ => 1 - (s : ℂ) • Q) hinv hlin

/-- The resolvent identity `Θ_s - Θ_t = (s - t) Θ_s Q Θ_t`. -/
private theorem BAKBase_sub (hQ : ‖Q‖ ≤ 1) {s t : ℝ} (hs : |s| < 1) (ht : |t| < 1) :
    PropThetaQ Q s - PropThetaQ Q t = ((s - t : ℝ) : ℂ) • (PropThetaQ Q s * Q * PropThetaQ Q t) := by
  have hd : (1 - (t : ℂ) • Q) - (1 - (s : ℂ) • Q) = ((s - t : ℝ) : ℂ) • Q := by
    rw [sub_sub_sub_cancel_left, ← sub_smul]; push_cast; rfl
  calc PropThetaQ Q s - PropThetaQ Q t
      = PropThetaQ Q s * ((1 - (t : ℂ) • Q) * PropThetaQ Q t)
        - PropThetaQ Q s * (1 - (s : ℂ) • Q) * PropThetaQ Q t := by
        rw [BAKBase_mul' hQ ht, BAKBase_mul hQ hs, mul_one, one_mul]
    _ = PropThetaQ Q s * ((1 - (t : ℂ) • Q) - (1 - (s : ℂ) • Q)) * PropThetaQ Q t := by noncomm_ring
    _ = PropThetaQ Q s * (((s - t : ℝ) : ℂ) • Q) * PropThetaQ Q t := by rw [hd]
    _ = ((s - t : ℝ) : ℂ) • (PropThetaQ Q s * Q * PropThetaQ Q t) := by simp

/-- `∂_t (Θ_t)_{ab} = (Θ_t Q Θ_t)_{ab}` (entrywise; twin of `hasDerivAt_Theta_mul_apply`). -/
private theorem BAKBase_hasDerivAt (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1) (a b : Zd d L) :
    HasDerivAt (fun s : ℝ => PropThetaQ Q s a b)
      ((PropThetaQ Q t * Q * PropThetaQ Q t) a b) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hball : ∀ᶠ s : ℝ in 𝓝[≠] t, |s| < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((isOpen_lt continuous_abs continuous_const).mem_nhds ht)
  have hslope : ∀ᶠ s : ℝ in 𝓝[≠] t,
      (PropThetaQ Q s * Q * PropThetaQ Q t) a b = slope (fun s : ℝ => PropThetaQ Q s a b) t s := by
    filter_upwards [hball, self_mem_nhdsWithin] with s hs hmem
    have hne : s - t ≠ 0 := sub_ne_zero_of_ne hmem
    have hdiff : PropThetaQ Q s a b - PropThetaQ Q t a b
        = ((s - t : ℝ) : ℂ) * (PropThetaQ Q s * Q * PropThetaQ Q t) a b := by
      have h := congrFun (congrFun (BAKBase_sub hQ hs ht) a) b
      simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h
    rw [slope_def_module, hdiff, Complex.real_smul]
    have hne' : ((s - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    push_cast at hne' ⊢
    field_simp
  refine Tendsto.congr' hslope ?_
  have hM : Tendsto (fun s : ℝ => PropThetaQ Q s) (𝓝[≠] t) (𝓝 (PropThetaQ Q t)) :=
    (BAKBase_continuousAt hQ ht).tendsto.mono_left nhdsWithin_le_nhds
  have hmul : Tendsto (fun s : ℝ => PropThetaQ Q s * Q * PropThetaQ Q t) (𝓝[≠] t)
      (𝓝 (PropThetaQ Q t * Q * PropThetaQ Q t)) :=
    (hM.mul tendsto_const_nhds).mul tendsto_const_nhds
  exact ((continuous_matrix_entry d L a b).continuousAt.tendsto).comp hmul

/-- The row sums of `Θ` when `Q 1 = 1`: `Σ_b Θ_{ab} = (1 - t)⁻¹` (twin of `sum_Theta_row`). -/
private theorem BAKBase_row_sum (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1)
    (h1 : Q *ᵥ (1 : Zd d L → ℂ) = 1) (a : Zd d L) :
    ∑ b : Zd d L, PropThetaQ Q t a b = (1 - (t : ℂ))⁻¹ := by
  have hne : (1 : ℂ) - (t : ℂ) ≠ 0 :=
    one_sub_ne_zero (by rw [Complex.norm_real, Real.norm_eq_abs]; exact ht)
  have h1' : (1 - (t : ℂ) • Q) *ᵥ (1 : Zd d L → ℂ) = (1 - (t : ℂ)) • (1 : Zd d L → ℂ) := by
    rw [sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, h1, sub_smul, one_smul]
  have hv : PropThetaQ Q t *ᵥ (1 : Zd d L → ℂ) = (1 - (t : ℂ))⁻¹ • (1 : Zd d L → ℂ) := by
    calc PropThetaQ Q t *ᵥ (1 : Zd d L → ℂ)
        = (1 - (t : ℂ))⁻¹ • (PropThetaQ Q t *ᵥ ((1 - (t : ℂ)) • (1 : Zd d L → ℂ))) := by
          rw [Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = (1 - (t : ℂ))⁻¹ • (PropThetaQ Q t *ᵥ ((1 - (t : ℂ) • Q) *ᵥ (1 : Zd d L → ℂ))) := by rw [h1']
      _ = (1 - (t : ℂ))⁻¹ • ((PropThetaQ Q t * (1 - (t : ℂ) • Q)) *ᵥ (1 : Zd d L → ℂ)) := by
          rw [Matrix.mulVec_mulVec]
      _ = (1 - (t : ℂ))⁻¹ • (1 : Zd d L → ℂ) := by rw [BAKBase_mul hQ ht, Matrix.one_mulVec]
  have h := congrFun hv a
  simpa [Matrix.mulVec, dotProduct] using h

/-- Entrywise conjugation: `Q' = conj Q` (`t` real) gives `Θ'_t = conj Θ_t`. -/
private theorem BAKBase_conj (hQ : ‖Q‖ ≤ 1) {t : ℝ} (ht : |t| < 1)
    {Q' : Matrix (Zd d L) (Zd d L) ℂ} (h : ∀ a b, Q' a b = starRingEnd ℂ (Q a b)) (a b : Zd d L) :
    PropThetaQ Q' t a b = starRingEnd ℂ (PropThetaQ Q t a b) := by
  set φ : Matrix (Zd d L) (Zd d L) ℂ →+* Matrix (Zd d L) (Zd d L) ℂ :=
    (starRingEnd ℂ).mapMatrix with hφ
  have hx : 1 - (t : ℂ) • Q' = φ (1 - (t : ℂ) • Q) := by
    ext i j
    simp only [hφ, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, h, smul_eq_mul, map_sub, map_mul, Complex.conj_ofReal]
    split_ifs <;> simp
  have hE : PropThetaQ Q' t = φ (PropThetaQ Q t) := by
    change Ring.inverse (1 - (t : ℂ) • Q') = φ (PropThetaQ Q t)
    rw [hx]
    refine (BAKBase_eq_inverse ((BAKBase_isUnit hQ ht).map φ) ?_).symm
    rw [← map_mul, BAKBase_mul hQ ht, map_one]
  rw [hE]
  simp [hφ]

end Generic

/-! ### 2b. The calculus for `Q = M^{(σ₁σ₂)}` of the block Anderson model -/

section BACalculus

open scoped NNReal Matrix.Norms.Operator

variable (d L : ℕ) [NeZero L]

private theorem BAKBase_Msigma_symm (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b = BAMsigma d L (BAMB d L g (E : ℂ) m) σ b a := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply,
      BAMB_symm d L g (E : ℂ) m a b]
  · exact BAMB_symm d L g (E : ℂ) m a b

/-- `Q = M^{(σ₁σ₂)}` has `|Q_ab| = BAK_ab`, so its `∞→∞` norm is `≤ 1` (Ward row sums of `BAK`). -/
private theorem BAKBase_norm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) :
    ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂‖ ≤ 1 :=
  BAKBase_norm_le fun a => by
    simp only [BAMss_norm_eq_BAK]
    exact (BAK_row_sum d L g E m hr.1 a).le

private theorem BAKBase_abs (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : |t| < 1 :=
  abs_lt.mpr ⟨by linarith, ht1⟩

/-- **Invertibility of `1 - t M^{(σ₁σ₂)}`** at real `0 ≤ t < 1`, for all four charge pairs
(`‖M^{(σ₁σ₂)}‖_{∞→∞} ≤ 1`, `|M^{(σ₁σ₂)}_{ab}| = BAK_ab`, Ward row sums; only `BAReal.1 = BASelf` is used).
`t < 1` is binding: `‖M^{(+,-)}‖_{∞→∞} = 1` and `M^{(+,-)} 1 = 1`. -/
theorem BATheta_isUnit (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    IsUnit (1 - (t : ℂ) • BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
  BAKBase_isUnit (BAKBase_norm d L g κ E m hr σ₁ σ₂) (BAKBase_abs t ht0 ht1)

/-- **The resolvent identities** `Θ = 1 + t M Θ = 1 + t Θ M` (`(def_Thxi)`, `1_2:1073-1076`). -/
theorem BATheta_resolvent (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ = 1 + (t : ℂ) •
        (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂) ∧
      BATheta d L g E m t σ₁ σ₂ = 1 + (t : ℂ) •
        (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) :=
  ⟨BAKBase_resolvent_left (BAKBase_norm d L g κ E m hr σ₁ σ₂) (BAKBase_abs t ht0 ht1),
    BAKBase_resolvent_right (BAKBase_norm d L g κ E m hr σ₁ σ₂) (BAKBase_abs t ht0 ht1)⟩

/-- **`∂_tΘ = ΘMΘ`**, entrywise, at every `0 ≤ t < 1` (twin of `hasDerivAt_Theta_mul_apply`,
`Propagator/Deriv.lean:108`, with `μ S^{(B)}` replaced by `M^{(σ₁σ₂)}`). -/
theorem BATheta_hasDerivAt (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    HasDerivAt (fun s : ℝ => BATheta d L g E m s σ₁ σ₂ a b)
      ((BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
        BATheta d L g E m t σ₁ σ₂) a b) t :=
  BAKBase_hasDerivAt (BAKBase_norm d L g κ E m hr σ₁ σ₂) (BAKBase_abs t ht0 ht1) a b

/-- `M^{(σ₁σ₂)} = M^{(σ₂σ₁)}` for the symmetric `M^{(B)}`, hence `Θ^{(σ₁σ₂)} = Θ^{(σ₂σ₁)}` (`T2360c`; probe
`t/T2360:RBM3D/Probe/T2360Pins.lean:387`).  No hypothesis on the data and no restriction on `t`. -/
theorem BATheta_swap {d L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) :
    BATheta d L g E m t σ₁ σ₂ = BATheta d L g E m t σ₂ σ₁ := by
  have h : ∀ x y, BAMB d L g (E : ℂ) m x y = BAMB d L g (E : ℂ) m y x :=
    fun x y => BAMB_symm d L g (E : ℂ) m x y
  have e : BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ = BAMss d L (BAMB d L g (E : ℂ) m) σ₂ σ₁ := by
    ext a b
    cases σ₁ <;> cases σ₂ <;> simp [BAMss, BAMsigma, Matrix.conjTranspose_apply, h a b, mul_comm]
  unfold BATheta
  rw [e]

/-- **`Θ^{(-,-)} = conj Θ^{(+,+)}`**, entrywise, for real `0 ≤ t < 1` (`M(-) = M^* `, `M` symmetric;
false for complex `t`). -/
theorem BATheta_conj (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a b : Zd d L) :
    BATheta d L g E m t false false a b = starRingEnd ℂ (BATheta d L g E m t true true a b) :=
  BAKBase_conj (BAKBase_norm d L g κ E m hr true true) (BAKBase_abs t ht0 ht1)
    (fun a b => by
      simp only [BAMss, BAMsigma, Matrix.of_apply, Bool.false_eq_true, ite_false, ite_true,
        Matrix.conjTranspose_apply, map_mul, Complex.star_def, mul_comm]) a b

/-- **`Θ^{(σ₁σ₂)}` is symmetric**: `(M^{(σ₁σ₂)})ᵀ = M^{(σ₁σ₂)}` (symmetry of `M^{(B)}`), so `Θᵀ = Θ`. -/
theorem BATheta_isSymm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (σ₁ σ₂ : Bool) :
    (BATheta d L g E m t σ₁ σ₂)ᵀ = BATheta d L g E m t σ₁ σ₂ :=
  BAKBase_transpose (BAKBase_norm d L g κ E m hr σ₁ σ₂) (BAKBase_abs t ht0 ht1) (by
    ext a b
    simp only [Matrix.transpose_apply, BAMss, Matrix.of_apply]
    rw [BAKBase_Msigma_symm d L g E m σ₁ a b, BAKBase_Msigma_symm d L g E m σ₂ b a, mul_comm])

/-- **Row sums of `Θ^{(+,-)}`**: `Σ_b Θ^{(+,-)}_{t,ab} = (1-t)⁻¹` (twin of `sum_Theta_row`,
`Propagator/Basic.lean:203`; `M^{(+,-)} = BAK` by `BATheta_pm_eq`, `BA/KKernel.lean:107`, with unit row sums). -/
theorem BATheta_row_sum_pm (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (a : Zd d L) :
    ∑ b, BATheta d L g E m t true false a b = (1 - (t : ℂ))⁻¹ := by
  refine BAKBase_row_sum (BAKBase_norm d L g κ E m hr true false) (BAKBase_abs t ht0 ht1) ?_ a
  rw [BAMss_pm_eq]
  funext a
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.one_apply, mul_one]
  have h := BAK_row_sum d L g E m hr.1 a
  exact_mod_cast h

end BACalculus

/-! ## 3. The trace form of `(eq:KMloop)` (`1_2:1003`) -/

/-- The chain index `b_0 = x`, `b_{i+1} = a_i` (`a_{-1} = x`). -/
private def BAKBase_b {ι : Type*} (x : ι) (a : ℕ → ι) : ℕ → ι
  | 0 => x
  | i + 1 => a i

/-- `(∏_{i<n} A_i D_{a_i})_{xy} = 1(y = a_{n-1}) c^n ∏_{i<n} A_i(a_{i-1}, a_i)` for `D_a = c 1_{[a]}`. -/
private theorem BAKBase_chain {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ℂ) (A : ℕ → Matrix ι ι ℂ)
    (a : ℕ → ι) (x : ι) (n : ℕ) (y : ι) :
    (((List.range n).map fun i => A i * diagonal (fun z => if z = a i then c else 0)).prod) x y =
      if y = BAKBase_b x a n then
        c ^ n * ∏ i ∈ Finset.range n, A i (BAKBase_b x a i) (BAKBase_b x a (i + 1)) else 0 := by
  induction n generalizing y with
  | zero => simp [BAKBase_b, Matrix.one_apply, eq_comm]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [Matrix.mul_apply]
    simp only [ih, Matrix.mul_diagonal, Finset.prod_range_succ, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    by_cases h : y = a n
    · simp only [BAKBase_b, h, ite_true]; ring
    · simp [BAKBase_b, h]

/-- `E_a = (W^{-d} 1_{[a]}) ⊗ I_{W^d}` (`(Eq:defGLoop)`, `1_2:824`). -/
private theorem BAKBase_Eblk (d L W : ℕ) [NeZero L] (a : Zd d L) :
    Eblk d L W a = (diagonal (fun z : Zd d L => if z = a then ((W : ℂ) ^ d)⁻¹ else 0)) ⊗ₖ
      (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [Eblk_apply, Matrix.kroneckerMap_apply, diagonal_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- `A ↦ A ⊗ I_{W^d}` is multiplicative. -/
private def BAKBase_kron (d L W : ℕ) [NeZero L] : Matrix (Zd d L) (Zd d L) ℂ →* Matrix (Vtx d L W) (Vtx d L W) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, mul_one]

/-- **The trace form of `(eq:KMloop)`** (`1_2:1003`): `𝓜^{(n)}_{σ,a} = tr ∏_i (M(σ_i) ⊗ I_{W^d}) E_{a_i}`, in the
`List.ofFn` order of `loopM` (`Loop/GLoopFlow.lean:92`), for `n ≥ 1`, `W ≥ 1` (`STLKgL` at `τ = 0`). -/
theorem BAMLoop_trace (d L W : ℕ) [NeZero L] [NeZero W] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) {n : ℕ} (hn : 1 ≤ n)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAMLoop d L W M (loopOf σ a) =
      Matrix.trace (List.ofFn fun i : Fin n =>
        (M (σ i) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)) * Eblk d L W (a i)).prod := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set c : ℂ := ((W : ℂ) ^ d)⁻¹ with hc
  have hW : (W : ℂ) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  let σ' : ℕ → Bool := fun i => (List.ofFn σ).getD i false
  let a' : ℕ → Zd d L := fun i => (List.ofFn a).getD i 0
  have hσa : ∀ i : Fin (k + 1), σ' i = σ i ∧ a' i = a i := fun i => by
    simp only [σ', a', List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt, dite_true,
      Option.getD_some, Fin.eta, and_self]
  have hl : List.ofFn (fun i : Fin (k + 1) =>
      (M (σ i) ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)) * Eblk d L W (a i)) =
      (List.range (k + 1)).map fun i => BAKBase_kron d L W
        (M (σ' i) * diagonal (fun z => if z = a' i then c else 0)) := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    have hi : i < k + 1 := by simpa using h1
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
    have e : σ' i = σ ⟨i, hi⟩ ∧ a' i = a ⟨i, hi⟩ := hσa ⟨i, hi⟩
    rw [BAKBase_Eblk, map_mul, e.1, e.2]
    rfl
  rw [hl, show ∀ f : ℕ → Matrix (Zd d L) (Zd d L) ℂ, ((List.range (k + 1)).map fun i => BAKBase_kron d L W (f i)).prod =
    BAKBase_kron d L W (((List.range (k + 1)).map f).prod) from fun f => by rw [map_list_prod, List.map_map]; rfl]
  set P := ((List.range (k + 1)).map fun i =>
    M (σ' i) * diagonal fun z => if z = a' i then c else 0).prod with hP
  have htr : Matrix.trace (BAKBase_kron d L W P) = Matrix.trace P * (((W ^ d : ℕ)) : ℂ) := by
    change Matrix.trace (P ⊗ₖ (1 : Matrix (Fin (W ^ d)) (Fin (W ^ d)) ℂ)) = _
    rw [Matrix.trace_kronecker, Matrix.trace_one, Fintype.card_fin]
  have hPx : ∀ x, P x x = if x = a' k then c ^ (k + 1) * ∏ i ∈ Finset.range (k + 1),
      M (σ' i) (BAKBase_b x a' i) (BAKBase_b x a' (i + 1)) else 0 := fun x =>
    BAKBase_chain c (fun i => M (σ' i)) a' x (k + 1) x
  have hPt : Matrix.trace P = c ^ (k + 1) * ∏ i ∈ Finset.range (k + 1),
      M (σ' i) (BAKBase_b (a' k) a' i) (BAKBase_b (a' k) a' (i + 1)) := by
    unfold Matrix.trace
    simp only [Matrix.diag_apply, hPx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [htr, hPt, BAMLoop_apply d L W M (loopOf σ a) (k + 1) (by omega) (by simp [loopOf])
    (by simp [loopOf])]
  have hprod : ∏ i ∈ Finset.range (k + 1), M ((loopOf σ a).σ.getD i false)
      ((loopOf σ a).a.getD ((i + (k + 1 - 1)) % (k + 1)) 0) ((loopOf σ a).a.getD i 0) =
      ∏ i ∈ Finset.range (k + 1), M (σ' i) (BAKBase_b (a' k) a' i) (BAKBase_b (a' k) a' (i + 1)) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    change M (σ' i) (a' ((i + (k + 1 - 1)) % (k + 1))) (a' i) = _
    cases i with
    | zero => simp [BAKBase_b, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
    | succ j =>
      have : (j + 1 + (k + 1 - 1)) % (k + 1) = j := by
        rw [show j + 1 + (k + 1 - 1) = j + (k + 1) by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      rw [this]; rfl
  rw [hprod, Nat.add_sub_cancel, pow_succ, hc]
  push_cast
  field_simp

/-! ## 4. Compiled nonempty instances

Loop part: the witness data of `BAMLoop_witness` (`d = 1`, `L = 3`, `W = 1` resp. `W = 2`; `M(+) = N`,
`M(-) = N'` symmetric `3 × 3` with distinct entries, the loop `(+,+,-)` of length `3`).  Calculus part: the
merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`, `P.real : BAReal 3 4 P.g0 (Im m₀) P.E m₀`,
the data of `KKernelInst`), `t = 1/2`, all four charge pairs where the statement quantifies over them.  No
hypothesis other than `BAReal` (discharged by `P.real`) and `0 ≤ t < 1` is needed. -/

namespace KBaseInst

open RBM.BA.MFixedPointInst

/-- `BAMLoop_witM` is symmetric (the hypothesis of `BAMLoop_le_two`). -/
theorem witM_symm (σ : Bool) : (BAMLoop_witM σ)ᵀ = BAMLoop_witM σ := by
  ext x y
  simp only [Matrix.transpose_apply, BAMLoop_witM, Matrix.of_apply]
  generalize x 0 = i
  generalize y 0 = j
  cases σ <;> fin_cases i <;> fin_cases j <;> rfl

/-- `BAMLoop_apply` at the witness (`n = 3`). -/
example : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ =
    (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ (3 - 1) * ∏ i ∈ Finset.range 3, BAMLoop_witM
      (([true, true, false] : List Bool).getD i false)
      (([![0], ![1], ![2]] : List (Zd 1 3)).getD ((i + (3 - 1)) % 3) 0)
      (([![0], ![1], ![2]] : List (Zd 1 3)).getD i 0) :=
  BAMLoop_apply 1 3 1 BAMLoop_witM ⟨[true, true, false], [![0], ![1], ![2]]⟩ 3 (by norm_num) rfl rfl

/-- `BAMLoop_le_two` at the symmetric witness (`n = 2`, mixed charges, `a_0 ≠ a_1`). -/
example : BAMLoop 1 3 1 BAMLoop_witM ⟨[true, false], [![0], ![2]]⟩ =
    (((1 : ℕ) : ℂ) ^ 1)⁻¹ ^ (2 - 1) * ((([true, false] : List Bool).zip (([![0], ![2]] : List (Zd 1 3)).zip
      (([![0], ![2]] : List (Zd 1 3)).rotate 1))).map fun p => BAMLoop_witM p.1 p.2.1 p.2.2).prod :=
  BAMLoop_le_two 1 3 1 BAMLoop_witM witM_symm ⟨[true, false], [![0], ![2]]⟩ (by decide)

/-- `BAMLoop_trace` at the witness with `W = 2` (`W^d = 2`, so the block factor is nontrivial). -/
example : BAMLoop 1 3 2 BAMLoop_witM (loopOf ![true, true, false] ![![0], ![1], ![2]]) =
    Matrix.trace (List.ofFn fun i : Fin 3 => (BAMLoop_witM (![true, true, false] i) ⊗ₖ
      (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) ℂ)) * Eblk 1 3 2 (![![0], ![1], ![2]] i)).prod :=
  BAMLoop_trace 1 3 2 BAMLoop_witM (by norm_num) _ _

/-- `BATheta_isUnit` at `P`, `t = 1/2`, `(σ₁, σ₂) = (+, -)` and `(-, -)`. -/
example : IsUnit (1 - (((1 / 2 : ℝ)) : ℂ) • BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false) :=
  BATheta_isUnit 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true false

example : IsUnit (1 - (((1 / 2 : ℝ)) : ℂ) • BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) false false) :=
  BATheta_isUnit 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) false false

/-- `BATheta_resolvent` at `P`, `t = 1/2`, `(+, +)`. -/
example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true = 1 + (((1 / 2 : ℝ)) : ℂ) •
        (BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true * BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true) ∧
      BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true = 1 + (((1 / 2 : ℝ)) : ℂ) •
        (BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true true) :=
  BATheta_resolvent 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true true

/-- `BATheta_hasDerivAt` at `P`, `t = 1/2`, `(+, -)`, entry `(0, (1,0,0))`. -/
example : HasDerivAt (fun s : ℝ => BATheta 3 4 P.g0 P.E P.m0 s true false 0 ![1, 0, 0])
    ((BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) true false *
      BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false) 0 ![1, 0, 0]) (1 / 2) :=
  BATheta_hasDerivAt 3 4 P.g0 P.m0.im P.E P.m0 P.real (by norm_num) (by norm_num) true false 0 ![1, 0, 0]

/-- `BATheta_swap` at `P`, `t = 1/2`, `(+, -)`. -/
example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false = BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false true :=
  BATheta_swap P.g0 P.E P.m0 (1 / 2) true false

/-- `BATheta_conj` at `P`, `t = 1/2`, entry `(0, (1,0,0))`. -/
example : BATheta 3 4 P.g0 P.E P.m0 (1 / 2) false false 0 ![1, 0, 0] =
    starRingEnd ℂ (BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true 0 ![1, 0, 0]) :=
  BATheta_conj 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) 0 ![1, 0, 0]

/-- `BATheta_isSymm` at `P`, `t = 1/2`, `(+, +)`. -/
example : (BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true)ᵀ = BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true true :=
  BATheta_isSymm 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true true

/-- `BATheta_row_sum_pm` at `P`, `t = 1/2`, row `0`: the row sum is `2`. -/
example : ∑ b, BATheta 3 4 P.g0 P.E P.m0 (1 / 2) true false 0 b = (1 - (((1 / 2 : ℝ)) : ℂ))⁻¹ :=
  BATheta_row_sum_pm 3 4 P.g0 P.m0.im P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) 0

end KBaseInst

end RBM.BA
