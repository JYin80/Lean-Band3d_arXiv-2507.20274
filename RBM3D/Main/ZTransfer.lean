/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Endpoints

/-!
# MA-02: the `zztE` transfer and `(eq:BtBt)` (Theorems 2.1-2.5, assembly)

Ticket T2219 (MA-02 of the T2192 assembly split).  Moved verbatim from the compiled probe
`RBM3D/Probe/T2192Pins.lean` at `97d958e` (branch `t/T2192`, never merged); the probe
namespace `RBM.Probe.T2192` becomes `RBM.Endpoints`, its `Inst` becomes `RBM.Endpoints.Inst`.

Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited `1_2:line`).

* The `zztE` transfer at `t₀ = lemT z`, `E = lemE z` (`1_2:787-795`) as identities: `zRange`,
  `zGreen`, `zLocal`, `zAve`, `zTrace`, `zProfile`.  The loop indices `(b, a)` of `zTrace`
  are D506 (the docstrings' `T2192g`).
* `(eq:BtBt)` (`1_2:1111`) with the explicit constants `2` and `√(κ(4-κ))/8`: `btBt`, with
  its carrier-free scalar core `STWB_compare` and the bulk bound `im_msc_ge`.
* The private helpers `W_pos_real`, `L_pos_real` are re-declared here because those of MA-01
  (`RBM3D/Endpoints.lean`) are private.
* Consumers: MA-03 (`Main/FixedZ`), MA-04 (`Main/ZNet`).  Nothing is registered: every pin of
  this file is proved here.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Univ
open scoped NNReal ENNReal

namespace RBM.Endpoints

section Scalars

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem W_pos_real : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n

private theorem L_pos_real : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
  have := sz.three_le_L n
  exact_mod_cast (by omega : 0 < sz.L n)

end Scalars

/-! ## The `zztE` transfer and `(eq:BtBt)` -/

section Transfer

/-- `Im z |m|² = Im m (1 - |m|²)`, from `m (m + z) = -1` (`(eq:t0E0)`, `1_2:789`: `t₀ = Im m/(Im m + Im z)`);
RBM2D `ZRescale_im_identity` (`RBM2D/Main/ZRescale.lean:168`, commit `c9a24cf`) with the merged `msc`. -/
theorem im_identity {z : ℂ} (hz : 0 < z.im) :
    z.im * ‖msc z‖ ^ 2 = (msc z).im * (1 - ‖msc z‖ ^ 2) := by
  have hm0 : msc z ≠ 0 := norm_pos_iff.mp (norm_msc_pos hz)
  have h := msc_add_eq_neg_inv hz
  have hz' : z = -(msc z)⁻¹ - msc z := by linear_combination h
  have him := congrArg Complex.im hz'
  have hN : Complex.normSq (msc z) = ‖msc z‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have hN0 : 0 < Complex.normSq (msc z) := Complex.normSq_pos.2 hm0
  rw [Complex.sub_im, Complex.neg_im, Complex.inv_im, hN] at him
  rw [hN] at hN0
  field_simp at him ⊢
  linarith

/-- **Pin `MAZRange`** (`zztE`, `1_2:787-795`): for `0 < Im z ≤ 1`, `|Re z| ≤ 2 - κ`, the flow data
`(E, t₀) = (lemE z, lemT z)` is a bulk energy with `1/16 ≤ t₀ < 1` and `1 - t₀ = Im z / (Im m + Im z) ≥ Im z / 2`.
Merged: `lemma28_quant` (`|E| ≤ 2 - κ`, `t₀ ≥ 1/16`), `lemT_lt_one`; new: the identity.  Proved below (`zRange`). -/
def MAZRange : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → |z.re| ≤ 2 - κ →
    |lemE z| ≤ 2 - κ ∧ (1 / 16 : ℝ) ≤ lemT z ∧ lemT z < 1 ∧
      1 - lemT z = z.im / ((msc z).im + z.im) ∧ z.im / 2 ≤ 1 - lemT z

theorem zRange : MAZRange := by
  intro κ hκ z hz hz1 hre
  obtain ⟨hE, hu16, -, -⟩ := lemma28_quant hκ hz hz1 hre
  have hu1 := lemT_lt_one hz
  have hid := im_identity hz
  have hm1 := norm_msc_lt_one hz
  have hma : 0 < (msc z).im := msc_im_pos hz
  have hmaN : (msc z).im ≤ ‖msc z‖ := Complex.im_le_norm _
  have hpos : 0 < (msc z).im + z.im := by linarith
  have hT : lemT z = ‖msc z‖ ^ 2 := rfl
  have hform : 1 - lemT z = z.im / ((msc z).im + z.im) := by
    rw [hT, eq_div_iff hpos.ne']
    nlinarith [hid]
  refine ⟨hE, hu16, hu1, hform, ?_⟩
  rw [hform]
  have : (msc z).im + z.im ≤ 2 := by linarith
  rw [div_le_div_iff₀ (by norm_num) hpos]
  nlinarith

/-- **Pin `MAZGreen`** (`(eq:zztE)` third clause, `1_2:792`): `G(z) = √t₀ G_{t₀;E}` as an identity of random matrices
(one time only).  This is the merged `Sizes.Gt_lemT` (`Loop/GLoopFlow.lean:181`): RBM2D `ZGreen`
(`RBM2D/Main/ZRescale.lean:61`). -/
def MAZGreen : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ ω : sz.SeqΩ,
    (Real.sqrt (lemT z) : ℂ) • sz.Gt n (lemE z) (lemT z) true ω = sz.Gn n z ω

theorem zGreen : MAZGreen := fun sz n _ hz ω => Sizes.Gt_lemT sz n hz ω

/-- **Pin `MAZLocal`** (`(G_bound)` from `(Gt_bound)`, `1_2:1217`, `1_2:1226`): the entry of `G(z) - M(z)` is
`√t₀` times the entry of the flow quantity `STGM` at `(E, t) = (lemE z, lemT z)` (`m(z) = √t₀ m(E)`,
`msc_eq_sqrt_mul_mE`), so `|G_xy - M_xy|² = t₀ |(G_{t₀} - M)_{xy}|² ≤ |(G_{t₀} - M)_{xy}|²`.  Proved below. -/
def MAZLocal : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
    ‖sz.Gn n z ω x y - Mband sz n z x y‖ ^ 2 = lemT z * ‖STGM sz n (lemE z) (lemT z) ω x y‖ ^ 2

theorem zLocal : MAZLocal := by
  intro d sz n z hz ω x y
  have h1 := zGreen sz n z hz ω
  have h2 : sz.Gn n z ω x y - Mband sz n z x y =
      (Real.sqrt (lemT z) : ℂ) * STGM sz n (lemE z) (lemT z) ω x y := by
    unfold STGM Mband
    rw [← h1, msc_eq_sqrt_mul_mE hz]
    by_cases hxy : x = y <;> simp [hxy, Matrix.smul_apply]
    ring
  rw [h2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (lemT_pos hz).le]


/-- **`Im m(z) ≥ √(κ(4-κ))/8`** on `𝐃` (the bulk lower bound that `Prop8ZeroMode`, `κ' ≤ Im m'`, and `(eq:BtBt)`
need, row 12 of the preflight table): `m = √t₀ m(E)`, `t₀ ≥ 1/16`, `Im m(E) = √(4-E²)/2 ≥ √(κ(4-κ))/2` for
`|E| ≤ 2 - κ` (`lemma28_quant`, `msc_eq_sqrt_mul_mE`, `mE_im`). -/
theorem im_msc_ge {κ : ℝ} (hκ : 0 < κ) {z : ℂ} (hz : 0 < z.im) (hz1 : z.im ≤ 1)
    (hre : |z.re| ≤ 2 - κ) : Real.sqrt (κ * (4 - κ)) / 8 ≤ (msc z).im := by
  obtain ⟨hE, hu16, -, -⟩ := lemma28_quant hκ hz hz1 hre
  have hs4 : (1 / 4 : ℝ) ≤ Real.sqrt (lemT z) := by
    rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
      rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu16
  have hm : (msc z).im = Real.sqrt (lemT z) * (mE (lemE z)).im := by
    conv_lhs => rw [msc_eq_sqrt_mul_mE hz]
    rw [Complex.im_ofReal_mul]
  have hE2 : κ * (4 - κ) ≤ 4 - lemE z ^ 2 := by
    have h1 := abs_le.1 hE
    nlinarith [h1.1, h1.2]
  have hmE : Real.sqrt (κ * (4 - κ)) / 2 ≤ (mE (lemE z)).im := by
    rw [mE_im]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hE2) (by norm_num)
  rw [hm]
  have h0 : 0 ≤ Real.sqrt (κ * (4 - κ)) / 2 := by positivity
  calc Real.sqrt (κ * (4 - κ)) / 8 = (1 / 4) * (Real.sqrt (κ * (4 - κ)) / 2) := by ring
    _ ≤ Real.sqrt (lemT z) * (mE (lemE z)).im :=
        mul_le_mul hs4 hmE h0 (Real.sqrt_nonneg _)

/-- `A⁻¹ ≤ c B⁻¹` from `B ≤ c A`. -/
private theorem inv_le_mul_inv {A B c : ℝ} (hB : 0 < B) (hc : 0 < c) (h : B ≤ c * A) :
    A⁻¹ ≤ c * B⁻¹ := by
  have h1 : (c * A)⁻¹ ≤ B⁻¹ := inv_anti₀ hB h
  rw [mul_inv] at h1
  calc A⁻¹ = c * (c⁻¹ * A⁻¹) := by field_simp
    _ ≤ c * B⁻¹ := mul_le_mul_of_nonneg_left h1 hc.le

/-- **Pin `MABtBt`: `(eq:BtBt)` (`1_2:1107-1111`) at `t₀ = lemT z`, both directions, explicit constants**:
`W^{-d} B_{t₀,k} ≤ 2 𝓑_{η,Wk}` and `(√(κ(4-κ))/8) 𝓑_{η,Wk} ≤ W^{-d} B_{t₀,k}` for every block distance `k`
(`STWB sz n t k = W^{-d} B_{t,k}`, `calB_blk_eq_STWB`).  The two constants come from `Im z / 2 ≤ 1 - t₀ ≤ Im z / Im m`
(`zRange`, `im_msc_ge`).  Proved below (`btBt`). -/
def MABtBt : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (κ : ℝ), 0 < κ → ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
    |z.re| ≤ 2 - κ → ∀ k : ℕ,
      STWB sz n (lemT z) k ≤ 2 * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt (κ * (4 - κ)) / 8) * calB sz n z.im (((sz.W n : ℕ) : ℝ) * (k : ℝ)) ≤ STWB sz n (lemT z) k

/-- **The scalar core of `(eq:BtBt)`** (carrier-free: no `msc`, no band model; the block Anderson model reuses it with
`u = 1 - t₀^{BA}`): if `η > 0`, `u > 0` with `η ≤ 2u` and `u ≤ C η`, `C ≥ 1`, then `W^{-d} B_{1-u,k} ≤ 2 W^{-d} B_{1-η,k}`
and `W^{-d} B_{1-η,k} ≤ C W^{-d} B_{1-u,k}` for every block distance `k` (each of the two terms of `B` is monotone in
`|1 - t|`, `(g² + x)⁻¹` and `x⁻¹` change by at most the factor). -/
theorem STWB_compare (sz : Sizes d) (n : ℕ) {u η C : ℝ} (hη : 0 < η) (hu0 : 0 < u) (hu : η ≤ 2 * u)
    (hC1 : 1 ≤ C) (huC : u ≤ C * η) (k : ℕ) :
    STWB sz n (1 - u) k ≤ 2 * STWB sz n (1 - η) k ∧ STWB sz n (1 - η) k ≤ C * STWB sz n (1 - u) k := by
  have hW := W_pos_real sz n
  have hL := L_pos_real sz n
  have hLd : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hg2 : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have hc0 : 0 ≤ ((((k : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hWd : 0 < (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hC0 : 0 < C := by linarith
  have habs1 : |1 - (1 - u)| = u := by rw [sub_sub_cancel, abs_of_pos hu0]
  have habs2 : |1 - (1 - η)| = η := by rw [sub_sub_cancel, abs_of_pos hη]
  unfold STWB Bparam
  rw [habs1, habs2]
  set g2 := sz.lam n ^ 2 with hg2def
  set c := ((((k : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ with hcdef
  have hA1 : (g2 + u)⁻¹ ≤ 2 * (g2 + η)⁻¹ :=
    inv_le_mul_inv (by positivity) (by norm_num) (by linarith)
  have hA2 : (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹ ≤ 2 * (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ :=
    inv_le_mul_inv (by positivity) (by norm_num) (by nlinarith)
  have hB1 : (g2 + η)⁻¹ ≤ C * (g2 + u)⁻¹ :=
    inv_le_mul_inv (by positivity) hC0 (by nlinarith)
  have hB2 : (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ ≤ C * (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹ :=
    inv_le_mul_inv (by positivity) hC0 (by nlinarith)
  constructor
  · have h : (g2 + u)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹ ≤
        2 * ((g2 + η)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_right hA1 hc0]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((g2 + u)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 * ((g2 + η)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹)) :=
          mul_le_mul_of_nonneg_left h hWd.le
      _ = 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((g2 + η)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹)) := by ring
  · have h : (g2 + η)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹ ≤
        C * ((g2 + u)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_right hB1 hc0]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((g2 + η)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * η)⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (C * ((g2 + u)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹)) :=
          mul_le_mul_of_nonneg_left h hWd.le
      _ = C * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((g2 + u)⁻¹ * c + (((sz.L n : ℕ) : ℝ) ^ d * u)⁻¹)) := by ring

theorem btBt : MABtBt := by
  intro d hd sz n κ hκ z hz hz1 hre k
  have hd2 : 2 ≤ d := by omega
  have hmk := im_msc_ge hκ hz hz1 hre
  obtain ⟨-, -, hu1, hform, hhalf⟩ := zRange κ hκ z hz hz1 hre
  have hma : 0 < (msc z).im := msc_im_pos hz
  have hκ2 : κ ≤ 2 := by have := abs_nonneg z.re; linarith
  have hr0 : 0 < Real.sqrt (κ * (4 - κ)) := Real.sqrt_pos.2 (mul_pos hκ (by linarith))
  have hr2 : Real.sqrt (κ * (4 - κ)) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (κ - 2)])
  generalize Real.sqrt (κ * (4 - κ)) = r at hmk hr0 hr2 ⊢
  rw [calB_blk_eq_STWB sz n hd2 hz k]
  have hu0 : 0 < 1 - lemT z := by linarith
  have hC : 0 < 8 / r := by positivity
  have hC1 : 1 ≤ 8 / r := by rw [le_div_iff₀ hr0]; linarith
  have huC : 1 - lemT z ≤ 8 / r * z.im := by
    rw [hform, div_le_iff₀ (by linarith : 0 < (msc z).im + z.im)]
    have h1 : 8 / r * z.im * (r / 8) ≤ 8 / r * z.im * ((msc z).im + z.im) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : 8 / r * z.im * (r / 8) = z.im := by field_simp
    linarith
  obtain ⟨h1, h2⟩ := STWB_compare sz n hz hu0 (by linarith) hC1 huC k
  have e : 1 - (1 - lemT z) = lemT z := by ring
  rw [e] at h1 h2
  refine ⟨h1, ?_⟩
  have h8 : 0 < r / 8 := by positivity
  calc r / 8 * STWB sz n (1 - z.im) k ≤ r / 8 * (8 / r * STWB sz n (lemT z) k) :=
        mul_le_mul_of_nonneg_left h2 h8.le
    _ = STWB sz n (lemT z) k := by field_simp

end Transfer

/-! ### (a) `ZAve`, `ZTrace`: the block-average and the two-loop identities (note the order `(b, a)`) -/

section Loops

variable {d : ℕ}

theorem Gres_blockMat' {L W : ℕ} [NeZero L] [NeZero W]
    (M : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (s : Bool) :
    Gres (blockMat d L W M) z s =
      (Gres M z s).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
  unfold Gres
  generalize (if s then z else (starRingEnd ℂ) z) = w
  have h : blockMat d L W M - w • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (M - w • 1).submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    simp [blockMat, Matrix.submatrix_sub, Matrix.submatrix_smul]
  rw [h, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]

theorem sum_vtx {L W : ℕ} [NeZero L] [NeZero W] (F : Vtx d L W → ℂ) :
    ∑ p, F p = ∑ x : Idx d L W, F (splitEquiv d L W x) :=
  (Equiv.sum_comp (splitEquiv d L W) F).symm

theorem trace_four {L W : ℕ} [NeZero L] [NeZero W] (P Q : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a b : Zd d L) :
    Matrix.trace (P.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W a *
        Q.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W b) =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W b, ∑ y ∈ Iblk d L W a, P x y * Q y x := by
  set e := splitEquiv d L W with he
  have h1 : ∀ p : Vtx d L W, (P.submatrix e.symm e.symm * Eblk d L W a * Q.submatrix e.symm e.symm *
      Eblk d L W b) p p =
      (∑ q : Vtx d L W, P (e.symm p) (e.symm q) * (if q.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        Q (e.symm q) (e.symm p)) * (if p.1 = b then ((W : ℂ) ^ d)⁻¹ else 0) := by
    intro p
    unfold Eblk
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.mul_diagonal]
    rfl
  have h2 : ∀ x : Idx d L W,
      (∑ q : Vtx d L W, P (e.symm (e x)) (e.symm q) * (if q.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        Q (e.symm q) (e.symm (e x))) * (if (e x).1 = b then ((W : ℂ) ^ d)⁻¹ else 0) =
      ∑ y : Idx d L W, P x y * Q y x * ((if (split d L W y).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        (if (split d L W x).1 = b then ((W : ℂ) ^ d)⁻¹ else 0)) := by
    intro x
    rw [Finset.sum_mul, sum_vtx]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Equiv.symm_apply_apply, he]
    have hy : (splitEquiv d L W y).1 = (split d L W y).1 := rfl
    have hx : (splitEquiv d L W x).1 = (split d L W x).1 := rfl
    rw [hy, hx]
    ring
  calc Matrix.trace (P.submatrix e.symm e.symm * Eblk d L W a * Q.submatrix e.symm e.symm * Eblk d L W b)
      = ∑ p : Vtx d L W, (P.submatrix e.symm e.symm * Eblk d L W a * Q.submatrix e.symm e.symm *
          Eblk d L W b) p p := rfl
    _ = ∑ x : Idx d L W, ∑ y : Idx d L W, P x y * Q y x * ((if (split d L W y).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) *
        (if (split d L W x).1 = b then ((W : ℂ) ^ d)⁻¹ else 0)) := by
        refine (sum_vtx _).trans (Finset.sum_congr rfl fun x _ => ?_)
        rw [h1, h2]
    _ = (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ Iblk d L W b, ∑ y ∈ Iblk d L W a, P x y * Q y x := by
        rw [Finset.mul_sum]
        simp only [Iblk, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : (split d L W x).1 = b
        · simp only [hx, ite_true]
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          by_cases hy : (split d L W y).1 = a
          · simp only [hy, ite_true]; ring
          · simp [hy]
        · simp [hx]

theorem trace_two {L W : ℕ} [NeZero L] [NeZero W] (P : Matrix (Idx d L W) (Idx d L W) ℂ) (a : Zd d L) :
    Matrix.trace (P.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm * Eblk d L W a) =
      ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, P x x := by
  set e := splitEquiv d L W with he
  have h1 : ∀ p : Vtx d L W, (P.submatrix e.symm e.symm * Eblk d L W a) p p =
      P (e.symm p) (e.symm p) * (if p.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) := by
    intro p
    unfold Eblk
    rw [Matrix.mul_diagonal]
    rfl
  calc Matrix.trace (P.submatrix e.symm e.symm * Eblk d L W a)
      = ∑ p : Vtx d L W, (P.submatrix e.symm e.symm * Eblk d L W a) p p := rfl
    _ = ∑ x : Idx d L W, P x x * (if (split d L W x).1 = a then ((W : ℂ) ^ d)⁻¹ else 0) := by
        refine (sum_vtx _).trans (Finset.sum_congr rfl fun x _ => ?_)
        rw [h1]
        simp only [Equiv.symm_apply_apply, he]
        rfl
    _ = ((W : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d L W a, P x x := by
        rw [Finset.mul_sum]
        simp only [Iblk, Finset.sum_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases hx : (split d L W x).1 = a
        · simp only [hx, ite_true]; ring
        · simp [hx]

private theorem Gres_conjTranspose' {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (σ : Bool) : (Gres H z σ)ᴴ = Gres H z (!σ) := by
  have hH' : Hᴴ = H := hH
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte, Bool.not_true, Bool.false_eq_true,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def]
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
      ← Matrix.nonsing_inv_eq_ringInverse, Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH',
      Complex.star_def, Complex.conj_conj]


/-- **Pin `MAZAve`** (`(G_bound_ave)` from `ML:GLoop` at `n = 1`, `1_2:1226-1229`): the block average of the diagonal
of `G(z)` is `√t₀ 𝓛^{(1)}_{t₀,+,a}` (`E_a` has weight `W^{-d}`).  RBM2D `ZAve` (`RBM2D/Main/ZRescale.lean:79`,
proof `zAve` `:307`).  Proved below. -/
def MAZAve : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
    (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, sz.Gn n z ω x x =
      (Real.sqrt (lemT z) : ℂ) * sz.Lloop n (lemE z) (lemT z) (fun _ : Fin 1 => true) (fun _ => a) ω

theorem zAve : MAZAve := by
  intro d sz n z hz ω a
  have h1 := zGreen sz n z hz ω
  have hGn : ∀ x : Idx d (sz.L n) (sz.W n), sz.Gn n z ω x x =
      (Real.sqrt (lemT z) : ℂ) * (Gres (sz.seqHflow n (lemT z) ω) (zt (lemE z) (lemT z)) true) x x := by
    intro x
    rw [← h1]
    simp [Sizes.Gt, Matrix.smul_apply]
  unfold Sizes.Lloop loopFine loopM
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  rw [Gres_blockMat', trace_two]
  simp only [hGn, ← Finset.mul_sum]
  ring

/-- **Pin `MAZTrace`** (`(eq:diffu1)`, `(eq:diffu2)` from `ML:GLoop` at `n = 2`, `1_2:1226-1229`): the block sums of the
entries of `G(z)` are `t₀ 𝓛^{(2)}_{t₀,(+,σ),(b,a)}` -- **with the loop indices swapped**: `tr(G E_b G^σ E_a) =
W^{-2d} ∑_{x∈[a], y∈[b]} G_xy G^σ_yx`, since `E_b` multiplies the column index of the first factor.  `σ = true` is
`G_xy G_yx` (`(eq:diffu2)`), `σ = false` is `|G_xy|² = G_xy conj G_xy` (`(eq:diffu1)`).  RBM2D states the endpoint with
`trGEGE` (the trace form), so the swap never appears there.  Proved below. -/
def MAZTrace : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ (ω : sz.SeqΩ) (a b : Zd d (sz.L n)),
    avg2 sz n (fun x y => sz.Gn n z ω x y * sz.Gn n z ω y x) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, true] ![b, a] ω ∧
    avg2 sz n (fun x y => ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, false] ![b, a] ω

theorem zTrace : MAZTrace := by
  intro d sz n z hz ω a b
  have h1 := zGreen sz n z hz ω
  have hs : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (lemT_pos hz)).ne'
  have hs2 : (Real.sqrt (lemT z) : ℂ) * (Real.sqrt (lemT z) : ℂ) = (lemT z : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (lemT_pos hz).le]
  have hHerm := Sizes.seqHflow_isHermitian sz n (lemT z) ω
  have hGt : ∀ x y : Idx d (sz.L n) (sz.W n),
      sz.Gt n (lemE z) (lemT z) true ω x y = ((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω x y := by
    intro x y
    rw [← h1]
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp
  have hGf : ∀ x y : Idx d (sz.L n) (sz.W n),
      sz.Gt n (lemE z) (lemT z) false ω y x = star (sz.Gt n (lemE z) (lemT z) true ω x y) := by
    intro x y
    have h := congrFun (congrFun (Gres_conjTranspose' hHerm (zt (lemE z) (lemT z)) true) y) x
    simpa [Sizes.Gt, Matrix.conjTranspose_apply] using h.symm
  have hcore : ∀ (σ : Bool) (F : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ),
      (∀ x y, sz.Gt n (lemE z) (lemT z) true ω x y * sz.Gt n (lemE z) (lemT z) σ ω y x =
        ((lemT z : ℂ))⁻¹ * F x y) →
      avg2 sz n F a b = (lemT z : ℂ) * sz.Lloop n (lemE z) (lemT z) ![true, σ] ![b, a] ω := by
    intro σ F hF
    unfold Sizes.Lloop loopFine loopM
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
    have e0 : (![true, σ] : Fin 2 → Bool) 0 = true := rfl
    have e1 : (![true, σ] : Fin 2 → Bool) (Fin.succ 0) = σ := rfl
    have f0 : (![b, a] : Fin 2 → Zd d (sz.L n)) 0 = b := rfl
    have f1 : (![b, a] : Fin 2 → Zd d (sz.L n)) (Fin.succ 0) = a := rfl
    rw [e0, e1, f0, f1, Gres_blockMat', Gres_blockMat', ← Matrix.mul_assoc, trace_four]
    unfold avg2
    have ht : (lemT z : ℂ) ≠ 0 := by exact_mod_cast (lemT_pos hz).ne'
    have hrw : ∀ x y : Idx d (sz.L n) (sz.W n),
        (Gres (sz.seqHflow n (lemT z) ω) (zt (lemE z) (lemT z)) true) x y *
          (Gres (sz.seqHflow n (lemT z) ω) (zt (lemE z) (lemT z)) σ) y x = (lemT z : ℂ)⁻¹ * F x y := hF
    simp only [hrw]
    simp only [← Finset.mul_sum]
    field_simp
  refine ⟨hcore true _ ?_, hcore false _ ?_⟩
  · intro x y
    have hyx : sz.Gt n (lemE z) (lemT z) true ω y x = ((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω y x := hGt y x
    rw [hGt x y, hyx]
    have : (((Real.sqrt (lemT z) : ℂ))⁻¹ * ((Real.sqrt (lemT z) : ℂ))⁻¹) = (lemT z : ℂ)⁻¹ := by
      rw [← mul_inv, hs2]
    calc (((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω x y) * (((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω y x)
        = (((Real.sqrt (lemT z) : ℂ))⁻¹ * ((Real.sqrt (lemT z) : ℂ))⁻¹) *
            (sz.Gn n z ω x y * sz.Gn n z ω y x) := by ring
      _ = (lemT z : ℂ)⁻¹ * (sz.Gn n z ω x y * sz.Gn n z ω y x) := by rw [this]
  · intro x y
    rw [hGf x y, hGt x y]
    have hsr : star (((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω x y) =
        ((Real.sqrt (lemT z) : ℂ))⁻¹ * star (sz.Gn n z ω x y) := by
      rw [star_mul, Complex.star_def, map_inv₀, Complex.conj_ofReal]
      ring
    rw [hsr]
    have : (((Real.sqrt (lemT z) : ℂ))⁻¹ * ((Real.sqrt (lemT z) : ℂ))⁻¹) = (lemT z : ℂ)⁻¹ := by
      rw [← mul_inv, hs2]
    have hn : sz.Gn n z ω x y * star (sz.Gn n z ω x y) = ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    calc (((Real.sqrt (lemT z) : ℂ))⁻¹ * sz.Gn n z ω x y) *
          (((Real.sqrt (lemT z) : ℂ))⁻¹ * star (sz.Gn n z ω x y))
        = (((Real.sqrt (lemT z) : ℂ))⁻¹ * ((Real.sqrt (lemT z) : ℂ))⁻¹) *
            (sz.Gn n z ω x y * star (sz.Gn n z ω x y)) := by ring
      _ = (lemT z : ℂ)⁻¹ * ((‖sz.Gn n z ω x y‖ ^ 2 : ℝ) : ℂ) := by rw [this, hn]


open scoped Matrix.Norms.Operator in
/-- **Pin `MAZProfile`** (`(Kn2sol)`, `1_2:1175`): the deterministic profile of `(eq:diffu1)`, `(eq:diffu2)` is
`t₀ 𝒦^{(2)}_{t₀,(+,σ),(b,a)}` at `(E, t₀) = (lemE z, lemT z)`: `|m|² Θ^{(+,-)}_{ab} / W^d` and `m² Θ^{(+,+)}_{ab} / W^d`
(`m(z) = √t₀ m(E)`, `|m(E)| = 1`, `Θ` symmetric).  Merged: `KLK_two` (`Loop/KLTree.lean:211`), `mE_lemE`,
`Theta_transpose`.  RBM2D `ZProfile` (`RBM2D/Main/ZRescale.lean:99`, proof `zProfile` `:210`).  Proved below. -/
def MAZProfile : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ), 0 < z.im → ∀ a b : Zd d (sz.L n),
    profPM sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, false] ![b, a] ∧
    profPP sz n z a b = (lemT z : ℂ) * sz.STKloop n (lemE z) (lemT z) ![true, true] ![b, a]

open scoped Matrix.Norms.Operator in
open RBM.Loop in
theorem zProfile : MAZProfile := by
  intro d sz n z hz a b
  have hL := sz.three_le_L n
  have hS : ‖SB d (sz.L n) (sz.lam n)‖ = 1 := norm_SB d (sz.L n) (sz.lam n) hL
  have hmn : 0 < ‖msc z‖ := norm_msc_pos hz
  have hmn1 : ‖msc z‖ < 1 := norm_msc_lt_one hz
  have hE2 : |lemE z| ≤ 2 := (abs_lemE_lt_two hz).le
  have hm1 : ‖mE (lemE z)‖ = 1 := norm_mE hE2
  have hne : ((‖msc z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hmn.ne'
  have hn1 : ‖(((‖msc z‖ ^ 2 : ℝ)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith
  have hn2 : ‖msc z ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith
  have hsym : ∀ ξ : ℂ, ‖ξ‖ < 1 → Theta d (sz.L n) (sz.lam n) ξ b a = Theta d (sz.L n) (sz.lam n) ξ a b := by
    intro ξ hξ
    have h := Theta_transpose d (sz.L n) (sz.lam n) hS hξ
    exact congrFun (congrFun h a) b
  have hK1 : sz.STKloop n (lemE z) (lemT z) ![true, false] ![b, a] =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * (mSigma (lemE z) true * mSigma (lemE z) false) *
        Theta d (sz.L n) (sz.lam n) ((lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) false)) b a := by
    have hI : (KLloopOf d (sz.L n) (![true, false] : Fin 2 → Bool) (![b, a] : Fin 2 → Zd d (sz.L n))) =
        ⟨[true, false], [b, a]⟩ := by simp [KLloopOf, List.ofFn_succ]
    unfold Sizes.STKloop
    rw [hI]
    exact KLK_two d (sz.L n) (sz.lam n) (sz.W n) (lemE z) (lemT z) true false b a
  have hK2 : sz.STKloop n (lemE z) (lemT z) ![true, true] ![b, a] =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) * (mSigma (lemE z) true * mSigma (lemE z) true) *
        Theta d (sz.L n) (sz.lam n) ((lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true)) b a := by
    have hI : (KLloopOf d (sz.L n) (![true, true] : Fin 2 → Bool) (![b, a] : Fin 2 → Zd d (sz.L n))) =
        ⟨[true, true], [b, a]⟩ := by simp [KLloopOf, List.ofFn_succ]
    unfold Sizes.STKloop
    rw [hI]
    exact KLK_two d (sz.L n) (sz.lam n) (sz.W n) (lemE z) (lemT z) true true b a
  have hm1' : mSigma (lemE z) true * mSigma (lemE z) false = 1 := by
    simp only [mSigma, ite_true, Bool.false_eq_true, ite_false]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm1]; simp
  have hm2' : (lemT z : ℂ) * (mSigma (lemE z) true * mSigma (lemE z) true) = msc z ^ 2 := by
    simp only [mSigma, ite_true]
    rw [mE_lemE hz]
    simp only [lemT]
    push_cast
    field_simp
  have hξ1 : (lemT z : ℂ) * 1 = (((‖msc z‖ ^ 2 : ℝ)) : ℂ) := by simp [lemT]
  constructor
  · rw [hK1, hm1', hξ1, hsym _ hn1]
    unfold profPM ThetaPM
    simp only [mul_one, lemT]
    push_cast
    field_simp
  · rw [hK2, hm2', hsym _ hn2]
    unfold profPP ThetaPP
    have hm : ((lemT z : ℂ)) * (mSigma (lemE z) true * mSigma (lemE z) true) = msc z ^ 2 := hm2'
    have : mSigma (lemE z) true * mSigma (lemE z) true = msc z ^ 2 / (lemT z : ℂ) := by
      rw [eq_div_iff (by exact_mod_cast (lemT_pos hz).ne')]; rw [mul_comm]; exact hm
    rw [this]
    have ht : (lemT z : ℂ) ≠ 0 := by exact_mod_cast (lemT_pos hz).ne'
    field_simp

end Loops

namespace Inst

open RBM.Gauss.SizesInst RBM.Univ.UNInst
/-- `ZRange` at `z = zI`. -/
theorem inst_zRange :
    |lemE zI| ≤ 2 - 1 / 10 ∧ (1 / 16 : ℝ) ≤ lemT zI ∧ lemT zI < 1 ∧
      1 - lemT zI = zI.im / ((msc zI).im + zI.im) ∧ zI.im / 2 ≤ 1 - lemT zI :=
  zRange (1 / 10) (by norm_num) zI zI_im_pos zI_im_le zI_re_le

/-- `(eq:BtBt)` at `z = zI`, every block distance `k`: `2` and `√(κ(4-κ))/8` with `κ = 1/10`. -/
theorem inst_btBt (k : ℕ) :
    STWB sz0 0 (lemT zI) k ≤ 2 * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ∧
      (Real.sqrt ((1 / 10) * (4 - 1 / 10)) / 8) * calB sz0 0 zI.im (((sz0.W 0 : ℕ) : ℝ) * (k : ℝ)) ≤
        STWB sz0 0 (lemT zI) k :=
  btBt (d := 3) le_rfl sz0 0 (1 / 10) (by norm_num) zI zI_im_pos zI_im_le zI_re_le k

/-- `(G_bound)` transfer at `z = zI`. -/
theorem inst_zLocal (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    ‖sz0.Gn 0 zI ω x y - Mband sz0 0 zI x y‖ ^ 2 = lemT zI * ‖STGM sz0 0 (lemE zI) (lemT zI) ω x y‖ ^ 2 :=
  zLocal sz0 0 zI zI_im_pos ω x y

/-- `(G_bound_ave)` transfer at `z = zI`. -/
theorem inst_zAve (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)) :
    (((sz0.W 0 : ℕ) : ℂ) ^ 3)⁻¹ * ∑ x ∈ Iblk 3 (sz0.L 0) (sz0.W 0) a, sz0.Gn 0 zI ω x x =
      (Real.sqrt (lemT zI) : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) (fun _ : Fin 1 => true) (fun _ => a) ω :=
  zAve sz0 0 zI zI_im_pos ω a

/-- The two-loop transfer at `z = zI` (indices `(b, a)`). -/
theorem inst_zTrace (ω : sz0.SeqΩ) (a b : Zd 3 (sz0.L 0)) :
    avg2 sz0 0 (fun x y => sz0.Gn 0 zI ω x y * sz0.Gn 0 zI ω y x) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a] ω ∧
    avg2 sz0 0 (fun x y => ((‖sz0.Gn 0 zI ω x y‖ ^ 2 : ℝ) : ℂ)) a b =
        (lemT zI : ℂ) * sz0.Lloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ω :=
  zTrace sz0 0 zI zI_im_pos ω a b

/-- The profile identity `(Kn2sol)` at `z = zI`. -/
theorem inst_zProfile (a b : Zd 3 (sz0.L 0)) :
    profPM sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, false] ![b, a] ∧
    profPP sz0 0 zI a b = (lemT zI : ℂ) * sz0.STKloop 0 (lemE zI) (lemT zI) ![true, true] ![b, a] :=
  zProfile sz0 0 zI zI_im_pos a b

end Inst

end RBM.Endpoints
