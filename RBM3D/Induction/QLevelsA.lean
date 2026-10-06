/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QDriftB
import RBM3D.Induction.B45

/-!
# S3-16a (ticket T2268): the deterministic levels of the alternating start term and of `ℬ₄ + ℬ₅` at a matrix

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(eq:Ward_typeP)` `3_5:1264-1271`,
start term `3_5:1676-1690`, `(y27kasdfg)`, `(A5)`, `(A4)` `3_5:1692-1706`.

Re-scope (DECISIONS §83, §62 (4), §64 (4)): RBM2D `AltLevelsQ0` (`AltLevelsQ0.lean:55-64, 380-522` at `c9a24cf`)
is ported in its deterministic, per-matrix form, as the merged `B45_det`/`B45_det2` (S3-19, `B45.lean:2346, 2577`)
at a Hermitian matrix `H` on `altB4N`/`altB5N`/`STQop (STLKM … H …)` (`QDriftA.lean:59-91`).  `AltLevelsE` is
not ported (the Q/E split is gone, §83).  Nothing is lifted, no probability, no `≺`: every statement holds per
matrix `H`, from `H.IsHermitian` and deterministic rank-`(m+1)` levels alone.

* `QLevelsA_ward_finM`, `QLevelsA_Psum_LK_leM`: Ward's identity at the last index and the near/far split of `𝒫`
  at a matrix (copies of `B45_ward_fin` `B45.lean:200` and `B45_Psum_LK_le` `:414`; `ω` becomes `H` with
  `H.IsHermitian`, `STLKtensor sz n E u ω = sz.STLKM n E u (sz.seqHflow n u ω)` by `rfl`), with the private chain
  `QLevelsA_loopL_ward` (copy of the private `B45_loopL_ward` `B45.lean:78-149`, generic in `H`);
* `altB45N_levelM` (target 2): `B45_det2` at a Hermitian matrix, restated on `altB4N`, `altB5N`;
* `startLevelQN` (target 3): `‖𝒬_u(𝓛-𝒦)_{u,σ}(H)‖ ≤ Y + N^τ B_u^{m+2} X`;
* `crudeLKM_of_level` (target 4): the crude-sup form of the `hcrude` binders of `alt_hA0clsQN`/`alt_hDclsQN`;
* instances (namespace `QLevelsAInst`) at `sz0`, `d = 3`, `m = 1`, `E = 0`, `u = 0`, `H = 0`.

Unpinned helpers are `private` or prefixed `QLevelsA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Ward's identity at the last index at a matrix (target 1) -/

section Ward

variable {d L W : ℕ} [NeZero L]

private theorem QLevelsA_loopL_eq_prod (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (I : LoopIdx (Zd d L)) :
    loopL d L W H z I
      = Matrix.trace (((I.σ.zip I.a).map fun p => Gres H z p.1 * Eblk d L W p.2).prod) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1
        = (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  unfold loopL
  rw [hfold]

private theorem QLevelsA_Gres_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (z : ℂ)
    (s : Bool) : Gres H ((starRingEnd ℂ) z) (!s) = Gres H z s := by
  cases s <;> simp [Gres]

private theorem QLevelsA_loopL_conj (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ : List Bool)
    (a : List (Zd d L)) :
    loopL d L W H ((starRingEnd ℂ) z) ⟨σ.map not, a⟩ = loopL d L W H z ⟨σ, a⟩ := by
  rw [QLevelsA_loopL_eq_prod, QLevelsA_loopL_eq_prod]
  congr 2
  simp only [List.zip_map_left, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  simp [QLevelsA_Gres_conj]

/-- **`(WI_calL)` at the last index, both charge orders**: a copy of the private `B45_loopL_ward`
(`B45.lean:107`, ticket T2136, `1ef8fa7`); the proof uses `H.IsHermitian` and `Im z ≠ 0` only. -/
private theorem QLevelsA_loopL_ward [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (s : Bool) (μ : List Bool)
    (a : List (Zd d L)) (ha : a.length = μ.length + 1) :
    ∑ x : Zd d L, loopL d L W H z ⟨s :: μ ++ [!s], a ++ [x]⟩
      = (2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ))⁻¹ *
          (loopL d L W H z ⟨true :: μ, a⟩ - loopL d L W H z ⟨false :: μ, a⟩) := by
  obtain ⟨x0, a', rfl⟩ : ∃ x0 a', a = x0 :: a' := by
    cases a with
    | nil => simp at ha
    | cons x0 a' => exact ⟨x0, a', rfl⟩
  have hμ : μ.length = a'.length := by simpa using ha.symm
  have hz1 : IsUnit (H - z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hz2 : IsUnit (H - (starRingEnd ℂ) z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) :=
    isUnit_sub_smul_one_of_im_ne_zero hH (by simpa using hz)
  cases s
  · have hz3 : IsUnit (H - (starRingEnd ℂ) ((starRingEnd ℂ) z) •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) := by rwa [Complex.conj_conj]
    have h' := sum_gloop_ward_last_div d L W (z := (starRingEnd ℂ) z) hz2 hz3
      (by simpa using hz) (μ.map not) x0 a' (by simpa using hμ)
    have hA : ∀ x : Zd d L, loopL d L W H z ⟨false :: μ ++ [!false], x0 :: a' ++ [x]⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨true :: μ.map not ++ [false], x0 :: a' ++ [x]⟩ := by
      intro x
      have := QLevelsA_loopL_conj H z (false :: μ ++ [!false]) (x0 :: a' ++ [x])
      simpa [List.map_append] using this.symm
    have hB : loopL d L W H z ⟨true :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨false :: μ.map not, x0 :: a'⟩ := by
      have := QLevelsA_loopL_conj H z (true :: μ) (x0 :: a')
      simpa using this.symm
    have hC : loopL d L W H z ⟨false :: μ, x0 :: a'⟩
        = loopL d L W H ((starRingEnd ℂ) z) ⟨true :: μ.map not, x0 :: a'⟩ := by
      have := QLevelsA_loopL_conj H z (false :: μ) (x0 :: a')
      simpa using this.symm
    simp only [hA]
    rw [h', hB, hC, Complex.conj_im, Complex.ofReal_neg, div_eq_inv_mul]
    have hne : (2 * Complex.I * (W : ℂ) ^ d * -(z.im : ℂ)) = -(2 * Complex.I * (W : ℂ) ^ d * (z.im : ℂ)) := by
      ring
    rw [hne, inv_neg]
    ring
  · have h' := sum_gloop_ward_last_div d L W hz1 hz2 hz μ x0 a' hμ
    simp only [List.cons_append, Bool.not_true] at h' ⊢
    rw [h', div_eq_inv_mul]

end Ward

section WardM

variable {d : ℕ} (sz : Sizes d)

/-- **Ward's identities at the last index** for `𝓛 - 𝒦` at a Hermitian matrix `H` (`lem_WI_K`, `(WI_calL)`),
alternating `σ`: a copy of `B45_ward_fin` (`B45.lean:200`, ticket T2136, `1ef8fa7`) with `H.IsHermitian`
for `seqHflow_isHermitian`:
`Σ_x (𝓛-𝒦)^{(m+2)}_{σ,(a',x)}(H) = (2iW^d η)⁻¹ ((𝓛-𝒦)^{(m+1)}_{σ⁺,a'}(H) - (𝓛-𝒦)^{(m+1)}_{σ⁻,a'}(H))`. -/
private theorem QLevelsA_ward_finM (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (a' : Fin (m + 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), sz.STLKM n E u H σ (Fin.snoc (α := fun _ => Zd d (sz.L n)) a' x) =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (sz.STLKM n E u H (B45_sgnCons true σ) a' - sz.STLKM n E u H (B45_sgnCons false σ) a') := by
  have hL3 := sz.three_le_L n
  have hW1 := sz.W_pos n
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hzim : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hH' : (blockMat d (sz.L n) (sz.W n) H).IsHermitian := hH.submatrix _
  set μ : List Bool := List.ofFn (fun i : Fin m => σ (Fin.succ (Fin.castSucc i))) with hμ
  have hlen : (List.ofFn a').length = μ.length + 1 := by simp [hμ]
  have hlist := B45_ofFn_sigma σ hσ
  have hLw := QLevelsA_loopL_ward (W := sz.W n) hH' hzim (σ 0) μ (List.ofFn a') hlen
  have hKw := KLK_ward d (sz.L n) (sz.W n) (sz.lam n) E hL3 hW1 hE u hu0 hu1 (σ 0) μ (List.ofFn a') hlen
  have hLM : ∀ {k : ℕ} (τ : Fin k → Bool) (b : Fin k → Zd d (sz.L n)),
      sz.STLM n E u H τ b = loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u)
        ⟨List.ofFn τ, List.ofFn b⟩ := fun τ b => loopM_eq_loopL d (sz.L n) (sz.W n) _ _ τ b
  simp only [STLKM, Finset.sum_sub_distrib]
  simp only [hLM, B45_STKloop_eq, B45_ofFn_snoc, hlist, B45_ofFn_sgnCons, hμ.symm]
  rw [hLw, hKw, ← etaT_eq_zt_im]
  ring

/-- **`(jywiiwsoks)`, deterministic window step at a matrix**: a copy of `B45_Psum_LK_le` (`B45.lean:414`,
ticket T2136, `1ef8fa7`) with `sz.STLKM n E u H` for `STLKtensor sz n E u ω`. -/
private theorem QLevelsA_Psum_LK_leM (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a₁ : Zd d (sz.L n))
    {R Y F : ℝ} (hR : 0 ≤ R) (hF0 : 0 ≤ F)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ Y)
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)), a' 0 = a₁ →
      R ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ F) :
    ‖STPsum (d := d) (fun b => sz.STLKM n E u H σ b) a₁‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ *
        (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F) := by
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hP : ∀ b : Bool, ‖STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons b σ) c) a₁‖ ≤
      ((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F := fun b =>
    B45_Psum_le _ a₁ hR (hY _) hF0 (fun a' h0 hfar => hF _ a' h0 hfar)
  have hsum : STPsum (d := d) (fun b => sz.STLKM n E u H σ b) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons true σ) c) a₁ -
          STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons false σ) c) a₁) := by
    rw [B45_Psum_snoc]
    simp only [QLevelsA_ward_finM sz n hE hu0 hu1 hH σ hσ]
    unfold STPsum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, norm_mul, B45_norm_kappa sz n hE hu1]
  have hd := norm_sub_le (STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons true σ) c) a₁)
    (STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons false σ) c) a₁)
  have h2 := add_le_add (hP true) (hP false)
  have hpos : 0 ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ := by positivity
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ *
        ‖STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons true σ) c) a₁ -
          STPsum (d := d) (fun c => sz.STLKM n E u H (B45_sgnCons false σ) c) a₁‖
      ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * etaT E u))⁻¹ *
          (2 * (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = _ := by
        rw [mul_inv]; field_simp

end WardM

/-! ## 2. Target 2: `B45_det2` at a Hermitian matrix, on `altB4N`/`altB5N` -/

section Det

variable {d : ℕ}

/-- **The `𝒫`-bound and the exponent count at a matrix** (the first half of `B45_det`, `B45.lean:2370-2402`, ticket
T2136, `1ef8fa7`, at `H`; neither `ϑ` nor `σ`'s tensor beyond `𝒫` enters): there is `Π ≥ 0` with
`‖(𝒫(𝓛-𝒦)_{σ})_{b₁}‖ ≤ Π` for every `b₁` and `Π · Λ (ℓ^d)^{-(m+1)} ≤ M B^{m+2} X`, `M = 3·4^{dm} Γ Λ ν²`. -/
private theorem QLevelsA_PiM (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} {Γ ν X ωf Fv Λ : ℝ} (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) :
    ∃ Pi : ℝ, 0 ≤ Pi ∧
      (∀ b₁ : Zd d (sz.L n),
        ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) b₁‖ ≤ Pi) ∧
      Pi * (Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) ≤
        (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) := by
  have hL3 := sz.three_le_L n
  obtain ⟨hKB, hηN, hBN, hη, hηle⟩ := B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ
  have hΓ0 : 0 ≤ Γ := by
    rw [hΓ]; have := Real.sqrt_pos.mpr hκ; positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hNe]; positivity
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hBN
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) u := by linarith
  set R : ℝ := ellT (sz.L n) (sz.lam n) u * ωf with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set Pi : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * etaT E u)⁻¹ *
    (((2 * R + 2) ^ d) ^ m * (ν * X * sz.Bctl n u ^ (m + 1)) +
      (((sz.L n : ℕ) : ℝ) ^ d) ^ m * Fv) with hPi
  have hP : ∀ b₁ : Zd d (sz.L n),
      ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) b₁‖ ≤ Pi :=
    fun b₁ =>
      QLevelsA_Psum_LK_leM sz n (E := E) (by linarith [abs_nonneg E]) hu0 hu1 hH σ hσ b₁ hR0 hFv0 hY
        (fun σ' a' _ hfar => hF σ' a' hfar)
  have hPi0 : 0 ≤ Pi := (norm_nonneg _).trans (hP 0)
  set vs : ℝ := Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) with hvs
  have hvs0 : 0 ≤ vs := by rw [hvs]; positivity
  refine ⟨Pi, hPi0, hP, ?_⟩
  exact B45_master_real (d := d) (m := m) (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (Ld := ((sz.L n : ℕ) : ℝ) ^ d)
      (N := ((sz.size n : ℕ) : ℝ)) (η := etaT E u) (B := sz.Bctl n u)
      (ℓ := ellT (sz.L n) (sz.lam n) u) (X := X) (ν := ν) (ω := ωf) (Γ := Γ) (Λ := Λ) (ϑb := vs)
      (Pi := Pi) (Fv := Fv) (by linarith) hLd1 hNe hℓ1 hν hX hB0 hη hωf hωd hΓ0 hΛ hWd1 hKB hηN hBN
      hFv hFv0 hνN hPi0 hvs0 (by rw [hPi]) (le_of_eq hvs)

/-- `(2m+5) M ≤ N^τ` gives `M B^{m+2} X ≤ N^τ B^{m+2} X` (the absorption of `B45_det2`, `B45.lean:2603-2626`). -/
private theorem QLevelsA_absorb (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) {m : ℕ} {Γ ν X Λ τN : ℝ} (hΓ : Γ = 2 / Real.sqrt κ)
    (hX : 1 ≤ X) (hΛ : 0 ≤ Λ)
    (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN) :
    0 < etaT E u ∧ 0 ≤ sz.Bctl n u ^ (m + 2) * X ∧
      (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) ∧
      ((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) * (sz.Bctl n u ^ (m + 2) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    rw [hNe]
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have := one_le_pow₀ (n := d) hL1; positivity
  have hBN : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n u :=
    (B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ).2.2.1
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hBN
  have hη : 0 < etaT E u := (B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ).2.2.2.1
  have hZ : 0 ≤ sz.Bctl n u ^ (m + 2) * X := by
    have : 0 ≤ X := by linarith
    positivity
  have hM1 : 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 ≤ (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) := by
    have hΓ0 : 0 ≤ Γ := by rw [hΓ]; have := Real.sqrt_pos.mpr hκ; positivity
    have h0 : 0 ≤ 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 := by positivity
    have : (1 : ℝ) ≤ 2 * (m : ℝ) + 5 := by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    nlinarith
  exact ⟨hη, hZ, mul_le_mul_of_nonneg_right (hM1.trans hMΛ) hZ, mul_le_mul_of_nonneg_right hMΛ hZ⟩

/-- **The deterministic core of `(eq:Ward_typeP)` and `(y27kasdfg)` at a matrix** (a copy of `B45_det`,
`B45.lean:2346-2438`, ticket T2136, `1ef8fa7`; `STLKM … H` for `STLKtensor … ω`, `H.IsHermitian` for `ω`), with the
second conjunct stated on `altB4N`, `altB5N`: `|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ M B^{m+2} X` and
`‖ℬ₄‖ + ‖ℬ₅‖ ≤ η⁻¹ (2m+5) M B^{m+2} X`, `M = 3·4^{dm} Γ Λ ν²`, `Γ = 2/√κ`. -/
private theorem QLevelsA_detM (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) {E u κ : ℝ} (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} {Γ ν X ωf Fv Λ : ℝ} (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a, ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) * ϑ u a‖ ≤
        (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) ∧
      ‖altB4N sz n E u ϑ σ H a‖ + ‖altB5N sz n E u ϑ σ H a‖ ≤
        (etaT E u)⁻¹ * (((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
          (sz.Bctl n u ^ (m + 2) * X)) := by
  have hL3 := sz.three_le_L n
  obtain ⟨hKB, hηN, hBN, hη, hηle⟩ := B45_scales hd sz n hκ hE hu0 hu1 hg hNu hΓ
  obtain ⟨Pi, hPi0, hP, hM⟩ := QLevelsA_PiM hd sz n hκ hE hu0 hu1 hg hNu hH hΓ hν hX hωf hωd hνN hFv hFv0 hΛ
    hY hF σ hσ
  set vs : ℝ := Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) with hvs
  have hvs0 : 0 ≤ vs := by
    rw [hvs]
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
    have : 0 < ellT (sz.L n) (sz.lam n) u := by linarith [one_le_ellT (g := sz.lam n) (t := u) hL1]
    positivity
  have hv1 : 0 < 1 - u := by linarith
  -- (1)
  have h1 : ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
      ϑ u a‖ ≤ Pi * vs := by
    rw [norm_mul]
    exact mul_le_mul (hP (a 0)) (hϑ a) (norm_nonneg _) hPi0
  refine ⟨h1.trans hM, ?_⟩
  -- (2) `ℬ₄`
  have hμ : ∀ i, ‖(fun i => mSigma E (σ i)) i‖ = 1 := fun i =>
    B45_norm_EKsgn (by linarith [abs_nonneg E]) σ i
  have hB4 := B45_B4_le (d := d) (L := sz.L n) (m := m + 1) (sz.lam n) hL3 hμ hu0 hu1 ϑ
    (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) hP hϑ a
  -- `ℬ₅`
  have hB5 : ‖altB5N sz n E u ϑ σ H a‖ ≤ (1 - u)⁻¹ * (Pi * vs) := by
    have e : ‖altB5N sz n E u ϑ σ H a‖ =
        ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
          deriv (fun τ => ϑ τ a) u‖ := norm_neg _
    rw [e, norm_mul]
    calc ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0)‖ *
          ‖deriv (fun τ => ϑ τ a) u‖
        ≤ Pi * (Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) :=
          mul_le_mul (hP (a 0)) (hϑ' a) (norm_nonneg _) hPi0
      _ = (1 - u)⁻¹ * (Pi * vs) := by rw [hvs]; ring
  have hinv : (1 - u)⁻¹ ≤ (etaT E u)⁻¹ := inv_anti₀ hη hηle
  have hMZ := hM
  have hPV0 : 0 ≤ Pi * vs := mul_nonneg hPi0 hvs0
  set M' := (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) with hM'
  have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hB4
  have hi0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hv1.le
  have hB4' : ‖altB4N sz n E u ϑ σ H a‖ ≤ 2 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (Pi * vs) := hB4
  calc _ ≤ 2 * ((m : ℝ) + 2) * (1 - u)⁻¹ * (Pi * vs) + (1 - u)⁻¹ * (Pi * vs) := add_le_add hB4' hB5
    _ = (1 - u)⁻¹ * ((2 * (m : ℝ) + 5) * (Pi * vs)) := by ring
    _ ≤ (etaT E u)⁻¹ * ((2 * (m : ℝ) + 5) * M') := by
        have h2 : (2 * (m : ℝ) + 5) * (Pi * vs) ≤ (2 * (m : ℝ) + 5) * M' :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h3 : 0 ≤ (2 * (m : ℝ) + 5) * (Pi * vs) := by positivity
        exact mul_le_mul hinv h2 h3 (inv_nonneg.2 hη.le)
    _ = _ := by rw [hM']; ring

/-- **Target 2: `B45_det2` at a Hermitian matrix** (`(eq:Ward_typeP)`, `(y27kasdfg)`, `3_5:1264-1271, 1692-1706`),
restated on `altB4N`, `altB5N` (`QDriftA.lean:59, 71`): if `(𝓛-𝒦)^{(m+1)}_{σ'}(H)` is at most `ν X B^{m+1}` at every
label (`hY`), at most `Fv` at labels with `diam_∞ ≥ ℓ_u ω_f` (`hF`), `ϑ` obeys the mollifier bounds and
`(2m+5) M ≤ N^τ`, `M = 3·4^{dm} Γ Λ ν²`, then for alternating `σ`
`|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ N^τ B^{m+2} X` and `‖ℬ₄‖ + ‖ℬ₅‖ ≤ N^τ η⁻¹ B^{m+2} X`, `B = W^{-d}B_{u,0}`.
Per matrix, no probability, no good set (only `H.IsHermitian`); case (i) `N⁻¹ ≤ 1 - u` only, as `B45_det`. -/
theorem altB45N_levelM (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) (E u κ : ℝ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
    (m : ℕ) (Γ ν X ωf Fv Λ τN : ℝ) (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖deriv (fun t : ℝ => ϑ t a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
        ϑ u a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) ∧
    ‖altB4N sz n E u ϑ σ H a‖ + ‖altB5N sz n E u ϑ σ H a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X) := by
  obtain ⟨h1, h2⟩ := QLevelsA_detM hd sz n hκ hE hu0 hu1 hg hNu hH hΓ hν hX hωf hωd hνN hFv hFv0 hΛ hY hF ϑ
    hϑ hϑ' σ hσ a
  obtain ⟨hη, hZ, hA1, hA2⟩ := QLevelsA_absorb hd sz n hκ hE hu0 hu1 hg hNu hΓ hX hΛ hMΛ (ν := ν)
  refine ⟨h1.trans hA1, h2.trans ?_⟩
  calc (etaT E u)⁻¹ * (((2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
        (sz.Bctl n u ^ (m + 2) * X))
      ≤ (etaT E u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X)) :=
        mul_le_mul_of_nonneg_left hA2 (inv_nonneg.2 hη.le)
    _ = _ := by ring

end Det

/-! ## 3. Target 3: the start level of `𝒬_u(𝓛-𝒦)_{u,σ}(H)` -/

section Start

/-- **Target 3: the deterministic `AltLevelsQ0` at a matrix** (RBM2D `AltLevelsQ0_pointwise`,
`AltLevelsQ0.lean:380-522` at `c9a24cf`; start term `3_5:1676-1690`): with the hypotheses of `altB45N_levelM`
(without the derivative bound `hϑ'`, which only `ℬ₅` uses) and a rank-`(m+2)` level `Y` of `(𝓛-𝒦)_{u,σ}(H)`,
`‖𝒬_u(𝓛-𝒦)_{u,σ}(H)_a‖ ≤ Y + N^τ B_u^{m+2} X`: `𝒬_u 𝒜 = 𝒜 - (𝒫𝒜)_{a₀} ϑ_u`, `norm_sub_le`, and the
first conjunct of `altB45N_levelM`. -/
theorem startLevelQN (d : ℕ) (hd : 2 ≤ d) (sz : Sizes d) (n : ℕ) (E u κ : ℝ) (hκ : 0 < κ)
    (hE : |E| ≤ 2 - κ) (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hH : H.IsHermitian)
    (m : ℕ) (Γ ν X ωf Fv Λ τN Y : ℝ) (hΓ : Γ = 2 / Real.sqrt κ) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (hYtop : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a‖ ≤
      Y + ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) := by
  obtain ⟨Pi, hPi0, hP, hM⟩ := QLevelsA_PiM hd sz n hκ hE hu0 hu1 hg hNu hH hΓ hν hX hωf hωd hνN hFv hFv0 hΛ
    hY hF σ hσ
  obtain ⟨hη, hZ, hA1, hA2⟩ := QLevelsA_absorb hd sz n hκ hE hu0 hu1 hg hNu hΓ hX hΛ hMΛ (ν := ν)
  have h1 : ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
      ϑ u a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) := by
    refine le_trans ?_ (hM.trans hA1)
    rw [norm_mul]
    exact mul_le_mul (hP (a 0)) (hϑ a) (norm_nonneg _) hPi0
  have e : STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a =
      sz.STLKM n E u H σ a - STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        sz.STLKM n E u H σ b) (a 0) * ϑ u a := rfl
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hYtop a) h1)

end Start

/-! ## 4. Target 4: the crude-sup bridge -/

/-- **Target 4: the crude-sup form** of a level of `(𝓛-𝒦)_{u,σ}(H)`: `‖(𝓛-𝒦)_{u,σ}(H)_b‖ ≤ Y` for every `b` and
`Y ≤ W^{C₀}` give `‖(𝓛-𝒦)_{u,σ}(H)‖ ≤ W^{C₀}` in the sup norm: the shape of the `hcrude` binders of
`goodSetN_A0clsQN` (`QDriftA.lean:450`), `alt_hA0clsQN` (`:486`) and `alt_hDclsQN` (`QDriftB.lean:395-402`). -/
theorem crudeLKM_of_level (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ) (σ : Fin k → Bool)
    (Y C₀ : ℝ) (hY : ∀ b : Fin k → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y)
    (hW : Y ≤ ((sz.W n : ℕ) : ℝ) ^ C₀) :
    ‖fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ := by
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact (pi_norm_le_iff_of_nonneg (Real.rpow_nonneg hWpos.le C₀)).2 fun b => (hY b).trans hW

/-! ## 5. Compiled nonempty instances (namespace `QLevelsAInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at
`n = 0` (`L = 4`, `W = 32`, `lam = 1/64`, `N = 2097152`), `m = 1` (tensors of `m + 2 = 3` indices), `E = 0`,
`u = 0`, `κ = 1` (`Γ = 2`), `H = 0` (Hermitian), `ν = 8`, `ωf = W^{1/5} = 2`, `X = 1`, `Fv = W^{-36}`, `τN = 2`,
the explicit mollifier `QopAlgebra_mollifier 3 L 2 lam` with `Λ = (1 + 40·6)·6^6 = 11244096`.  The levels `hY`, `hF`,
`hYtop` are read off `0 ∈ GoodSetN` at `(Γ, Λ, Φ) = (4, 100, 1)`, `k = 4`, `τ' = 1/5`, `D' = 36`
(clause (G2) for `j = 2, 3`, clause (Dec) for `j = 2`), the merged `zero_mem_goodSetN_of_levels`.  The far labels
(`ℓ_0 ωf = 2 ≤ diam_∞`) exist, so `hF` is not vacuous.  Every deterministic hypothesis is discharged. -/

namespace QLevelsAInst

open RBM.Gauss.SizesInst

/-- The zero matrix of `sz0` at `n = 0`. -/
private abbrev H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ := 0

private theorem W0 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by exact_mod_cast sz0_values.2.1
private theorem N0 : ((sz0.size 0 : ℕ) : ℝ) = 2097152 := by exact_mod_cast sz0_values.2.2.1
private theorem lam0 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
private theorem L0r : ((sz0.L 0 : ℕ) : ℝ) = 4 := by exact_mod_cast sz0_values.1

private theorem lam_pos0 : 0 < sz0.lam 0 := by rw [lam0]; norm_num

private theorem ellT0 : ellT (sz0.L 0) (sz0.lam 0) 0 = 1 := by
  unfold ellT
  rw [sub_zero, abs_one, Real.sqrt_one, div_one, lam0, max_eq_right (by norm_num)]
  exact min_eq_left (by rw [L0r]; norm_num)

private theorem W15 : ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 := by
  rw [W0, show (32 : ℝ) = 2 ^ 5 by norm_num, show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

private theorem Wneg36 : ((sz0.W 0 : ℕ) : ℝ) ^ (-(36 : ℝ)) = ((32 : ℝ) ^ 36)⁻¹ := by
  rw [W0, Real.rpow_neg (by norm_num), show (36 : ℝ) = ((36 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- `B = Bctl 0 0 = W^{-3} B_{0,0} ∈ (0, 2]` at `n = 0`. -/
private theorem Bctl0 : 0 < sz0.Bctl 0 0 ∧ sz0.Bctl 0 0 ≤ 2 := by
  have hB : sz0.Bctl 0 0 = (((32 : ℝ) ^ 3)⁻¹) * (((1 / 64 : ℝ) ^ 2 + 1)⁻¹ * 1 + ((4 : ℝ) ^ 3)⁻¹) := by
    unfold Sizes.Bctl Bparam
    rw [W0, lam0, L0r]
    norm_num
  rw [hB]
  constructor <;> norm_num

/-- `0 ∈ GoodSetN` at `n = 0`, `E = 0`, `u = 0`, `k = 4`, levels `(4, 100, 1)`, every `τ'`, `D'`. -/
private theorem zero_mem0 (τ' D' : ℝ) : (H0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ∈
    sz0.GoodSetN 0 0 0 (3 + 1) 4 100 1 τ' D' := by
  refine zero_mem_goodSetN_of_levels sz0 0 (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  rw [lam0]
  norm_num

/-- Clause (G2) of `GoodSetN` read as an entry bound: `‖(𝓛-𝒦)^{(j)}_{σ,a}(H)‖ ≤ (ΓΦ - 1) B^j`. -/
private theorem norm_STLKM_le_of_XiLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (j : ℕ) {Z : ℝ}
    (hB : 0 < sz.Bctl n u) (h : sz.STXiLKM n E u j H ≤ Z) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) : ‖sz.STLKM n E u H σ a‖ ≤ (Z - 1) * sz.Bctl n u ^ j := by
  have hBj : 0 < sz.Bctl n u ^ j := pow_pos hB j
  unfold STXiLKM at h
  have h1 : ‖sz.STLKM n E u H σ a‖ ≤ STmaxLKM sz n E u j H :=
    Finset.le_sup' (fun p : (Fin j → Bool) × (Fin j → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖)
      (Finset.mem_univ (σ, a))
  have h2 : STmaxLKM sz n E u j H / sz.Bctl n u ^ j ≤ Z - 1 := by linarith
  rw [div_le_iff₀ hBj] at h2
  exact h1.trans h2

/-- The window of `hF`: `ℓ_0 ωf = 2 ≤ diam_∞` is attained by `(0, (2, 2, 2))`. -/
private def farv : Zd 3 (sz0.L 0) := fun _ => (((2 : ℕ) : ZMod (sz0.L 0)))

private theorem zdist_far0 : zdist (sz0.L 0) (((2 : ℕ) : ZMod (sz0.L 0))) = 2 := by
  have hL : sz0.L 0 = 4 := sz0_values.1
  have hv : (((2 : ℕ) : ZMod (sz0.L 0))).val = 2 := by
    rw [ZMod.val_natCast, hL]
  unfold zdist
  rw [hv, hL]
  omega

private theorem window0 :
    ∃ b : Fin (1 + 1) → Zd 3 (sz0.L 0), ellT (sz0.L 0) (sz0.lam 0) 0 * 2 ≤ (STdiamInf b : ℝ) := by
  refine ⟨![0, farv], ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (1 + 1) × Fin (1 + 1) =>
      zdistInf 3 (sz0.L 0) ((![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) q.1 -
        (![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) q.2))
    (Finset.mem_univ ((1 : Fin (1 + 1)), (0 : Fin (1 + 1))))
  have h1 : zdistInf 3 (sz0.L 0) (farv) = 2 := by
    unfold zdistInf farv
    simp only [zdist_far0]
    rw [Finset.sup_const (Finset.univ_nonempty)]
  have h2 : (2 : ℕ) ≤ STdiamInf (![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) := by
    have e : (![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) 1 - (![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) 0
        = farv := by simp
    rw [e, h1] at h
    exact h
  rw [ellT0]
  have : ((2 : ℕ) : ℝ) ≤ (STdiamInf (![0, farv] : Fin (1 + 1) → Zd 3 (sz0.L 0)) : ℝ) := by exact_mod_cast h2
  push_cast at this
  linarith

/-- The levels `hY`, `hF`, `hYtop` of `H = 0` (`ν X = 8`, `ωf = 2`, `Fv = W^{-36}`). -/
private theorem hY0 (σ' : Fin (1 + 1) → Bool) (a' : Fin (1 + 1) → Zd 3 (sz0.L 0)) :
    ‖sz0.STLKM 0 0 0 H0 σ' a'‖ ≤ 8 * 1 * sz0.Bctl 0 0 ^ (1 + 1) := by
  have h := norm_STLKM_le_of_XiLKM sz0 0 0 0 H0 2 Bctl0.1 ((zero_mem0 (1 / 5) 36).2.1 2 (by norm_num)
    (by norm_num)) σ' a'
  refine h.trans ?_
  have h0 : 0 ≤ sz0.Bctl 0 0 ^ 2 := by have := Bctl0.1; positivity
  have e : sz0.Bctl 0 0 ^ (1 + 1) = sz0.Bctl 0 0 ^ 2 := rfl
  rw [e]
  nlinarith

private theorem hF0 (σ' : Fin (1 + 1) → Bool) (a' : Fin (1 + 1) → Zd 3 (sz0.L 0))
    (h : ellT (sz0.L 0) (sz0.lam 0) 0 * 2 ≤ (STdiamInf a' : ℝ)) :
    ‖sz0.STLKM 0 0 0 H0 σ' a'‖ ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (-(36 : ℝ)) := by
  have h' : ellT (sz0.L 0) (sz0.lam 0) 0 * ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ (STdiamInf a' : ℝ) := by
    rw [W15]; exact h
  have := (zero_mem0 (1 / 5) 36).2.2.1 2 (by norm_num) (by norm_num) σ' a' h'
  have e : sz0.STLKM 0 0 0 H0 σ' a' =
      loopFine 3 (sz0.L 0) (sz0.W 0) H0 (zt 0 0) σ' a' - STKloop sz0 0 0 0 σ' a' := rfl
  rw [e]
  linarith [norm_nonneg (loopFine 3 (sz0.L 0) (sz0.W 0) H0 (zt 0 0) σ' a')]

private theorem hYtop0 (σ : Fin (1 + 1 + 1) → Bool) (b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
    ‖sz0.STLKM 0 0 0 H0 σ b‖ ≤ (4 * 1 - 1) * sz0.Bctl 0 0 ^ (1 + 1 + 1) :=
  norm_STLKM_le_of_XiLKM sz0 0 0 0 H0 3 Bctl0.1 ((zero_mem0 (1 / 5) 36).2.1 3 (by norm_num) (by norm_num)) σ b

/-- The explicit mollifier at `u = 0`: `‖ϑ_{0,a}‖ ≤ Λ (ℓ_0^3)^{-2}` (`exp ≤ 1`) with `Λ = (1 + 40·6)·6^6`. -/
private theorem moll_sup (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
    ‖QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0) 0 a‖ ≤
      ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) * (((ellT (sz0.L 0) (sz0.lam 0) 0 ^ 3)⁻¹) ^ (1 + 1)) := by
  have h := (QopAlgebra_mollifier_props 3 (sz0.L 0) 2 (sz0.three_le_L 0) lam_pos0).2.1 0 le_rfl
    (by norm_num) a
  refine h.trans ?_
  have hl : 0 < ellT (sz0.L 0) (sz0.lam 0) 0 := by rw [ellT0]; norm_num
  have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (2 + 1)),
      (zdistD 3 (sz0.L 0) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hexp : Real.exp (-(1 / 2 : ℝ) * (∑ i ∈ Finset.univ.erase (0 : Fin (2 + 1)),
      (zdistD 3 (sz0.L 0) (a i - a 0) : ℝ)) / ellT (sz0.L 0) (sz0.lam 0) 0) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hl.le
  have hC : 0 ≤ ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) * (((ellT (sz0.L 0) (sz0.lam 0) 0 ^ 3)⁻¹) ^ 2) := by
    positivity
  calc _ ≤ ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) * (((ellT (sz0.L 0) (sz0.lam 0) 0 ^ 3)⁻¹) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hexp hC
    _ = _ := by rw [mul_one]

private theorem moll_deriv (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
    ‖deriv (fun t : ℝ => QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0) t a) 0‖ ≤
      ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) * (1 - 0)⁻¹ *
        (((ellT (sz0.L 0) (sz0.lam 0) 0 ^ 3)⁻¹) ^ (1 + 1)) :=
  (QopAlgebra_mollifier_props 3 (sz0.L 0) 2 (sz0.three_le_L 0) lam_pos0).2.2.2 0 le_rfl (by norm_num) a

private theorem hNu0 : (((sz0.size 0 : ℕ) : ℝ))⁻¹ ≤ 1 - 0 := by
  rw [N0]; norm_num

private theorem hMΛ0 : (2 * ((1 : ℕ) : ℝ) + 5) * (3 * 4 ^ (3 * 1) * (2 : ℝ) *
    ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) * (8 : ℝ) ^ 2) ≤ ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [N0, Real.rpow_two]
  norm_num

private theorem hFv0' : ((sz0.W 0 : ℕ) : ℝ) ^ (-(36 : ℝ)) ≤ 8 * (((sz0.size 0 : ℕ) : ℝ) ^ (2 * 1 + 4))⁻¹ := by
  rw [Wneg36, N0]
  norm_num

/-- **Instance of target 2** (`altB45N_levelM`): `d = 3`, `sz0`, `n = 0`, `m = 1`, `E = 0`, `u = 0`, `κ = 1`,
`H = 0`, the explicit mollifier, every alternating `σ` and every label `a`; the far window of `hF` is attained
by a label, and every deterministic hypothesis is discharged (`hY`, `hF` from `0 ∈ GoodSetN`). -/
theorem altB45N_levelM_instance (σ : Fin (1 + 1 + 1) → Bool) (hσ : σ (Fin.last (1 + 1)) = !σ 0)
    (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
    (∃ b : Fin (1 + 1) → Zd 3 (sz0.L 0), ellT (sz0.L 0) (sz0.lam 0) 0 * 2 ≤ (STdiamInf b : ℝ)) ∧
    ‖STPsum (d := 3) (fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b) (a 0) *
        QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0) 0 a‖ ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 0 0 ^ (1 + 2) * 1) ∧
    ‖altB4N sz0 0 0 0 (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) σ H0 a‖ +
        ‖altB5N sz0 0 0 0 (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) σ H0 a‖ ≤
      ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * ((etaT 0 0)⁻¹ * sz0.Bctl 0 0 ^ (1 + 2) * 1) := by
  refine ⟨window0, ?_⟩
  exact altB45N_levelM 3 (by norm_num) sz0 0 0 0 1 one_pos (by norm_num) le_rfl one_pos lam_pos0 hNu0 H0
    Matrix.isHermitian_zero 1 2 8 1 2 (((sz0.W 0 : ℕ) : ℝ) ^ (-(36 : ℝ)))
    ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) 2 (by simp) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by rw [N0]; norm_num) hFv0' (by positivity) (by positivity) hMΛ0 hY0 hF0
    (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) moll_sup moll_deriv σ hσ a

/-- **Instance of target 3** (`startLevelQN`): the same data, with the rank-3 level `Y = (ΓΦ - 1) B^3 = 3 B^3` read
off `0 ∈ GoodSetN` (clause (G2), `j = 3`), every alternating `σ` and every label `a`. -/
theorem startLevelQN_instance (σ : Fin (1 + 1 + 1) → Bool) (hσ : σ (Fin.last (1 + 1)) = !σ 0)
    (a : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0)) :
    ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) 0
        (fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b) a‖ ≤
      (4 * 1 - 1) * sz0.Bctl 0 0 ^ (1 + 1 + 1) +
        ((sz0.size 0 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 0 0 ^ (1 + 2) * 1) :=
  startLevelQN 3 (by norm_num) sz0 0 0 0 1 one_pos (by norm_num) le_rfl one_pos lam_pos0 hNu0 H0
    Matrix.isHermitian_zero 1 2 8 1 2 (((sz0.W 0 : ℕ) : ℝ) ^ (-(36 : ℝ)))
    ((1 + 40 * ((3 * 2 : ℕ) : ℝ)) * 6 ^ (3 * 2)) 2 ((4 * 1 - 1) * sz0.Bctl 0 0 ^ (1 + 1 + 1))
    (by simp) (by norm_num) le_rfl (by norm_num)
    (by norm_num) (by rw [N0]; norm_num) hFv0' (by positivity) (by positivity) hMΛ0 hY0 hF0
    (QopAlgebra_mollifier 3 (sz0.L 0) 2 (sz0.lam 0)) moll_sup σ hσ (hYtop0 σ) a

/-- **Instance of target 4** (`crudeLKM_of_level`): `k = 3`, `Y = 3 B^3`, `C₀ = 1`: `3 B^3 ≤ 24 ≤ 32 = W^1`
(`B ≤ 2`), so the sup norm of `(𝓛-𝒦)_{0,σ}(0)` over the `4^9` labels is at most `W^1`, for every `σ`. -/
theorem crudeLKM_of_level_instance (σ : Fin (1 + 1 + 1) → Bool) :
    ‖fun b : Fin (1 + 1 + 1) → Zd 3 (sz0.L 0) => sz0.STLKM 0 0 0 H0 σ b‖ ≤
      ((sz0.W 0 : ℕ) : ℝ) ^ (1 : ℝ) := by
  refine crudeLKM_of_level 3 sz0 0 0 0 H0 (1 + 1 + 1) σ ((4 * 1 - 1) * sz0.Bctl 0 0 ^ (1 + 1 + 1)) 1
    (hYtop0 σ) ?_
  rw [Real.rpow_one, W0]
  have h0 := Bctl0.1
  have h2 := Bctl0.2
  have e : sz0.Bctl 0 0 ^ (1 + 1 + 1) = sz0.Bctl 0 0 ^ 3 := rfl
  rw [e]
  have h3 : sz0.Bctl 0 0 ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ h0.le h2 3
  nlinarith

end QLevelsAInst

end RBM.Ind

end
