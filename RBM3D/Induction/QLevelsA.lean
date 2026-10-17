/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QDriftB
import RBM3D.Induction.B45
import RBM3D.Chain.B45Gen

/-!
# The deterministic levels of the alternating start term and of `ℬ₄ + ℬ₅` at a matrix

Paper: (4.30) `eq:Ward_typeP`, the start term in Subsection 4.5 `subsec:support`, (4.59) `y27kasdfg`,
(4.60) `A5`, (4.61) `A4`.

RBM2D's `AltLevelsQ0` in its deterministic, per-matrix form, via the deterministic core of `Induction/B45` at a Hermitian matrix
`H` on `altB4N`/`altB5N`/`STQop (STLKM … H …)`.  Nothing is lifted, no probability, no `≺`: every statement
holds per matrix `H`, from `H.IsHermitian` and deterministic rank-`(m+1)` levels alone.

* `QLevelsA_ward_finM`, `QLevelsA_Psum_LK_leM`: Ward's identity at the last index and the near/far split of `𝒫`
  at a matrix (as `B45_ward_fin` and `B45_Psum_le`, with the sample `ω` replaced by a matrix `H` with
  `H.IsHermitian`, `STLKtensor sz n E u ω = sz.STLKM n E u (sz.seqHflow n u ω)` by `rfl`), with the private chain
  `QLevelsA_loopL_ward` (as the private `B45_loopL_ward`, generic in `H`);
* `altB45N_levelM`: the deterministic core of `Induction/B45` at a Hermitian matrix, restated on `altB4N`, `altB5N`;
* `startLevelQN`: `‖𝒬_u(𝓛-𝒦)_{u,σ}(H)‖ ≤ Y + N^τ B_u^{m+2} X`.

Helpers are `private` or prefixed `QLevelsA_`.

The generic twins over a carrier `Cm : Step2Mat sz` (namespace `RBM.Ind`, `open RBM.BA`): `altB45Ng_levelM`
(the sample-level `B45_det2g` of `Chain/B45Gen` read at a Hermitian matrix through the carrier with the matrices
fixed) and `startLevelQNg`.
-/

open private B45_norm_colsum from RBM3D.Induction.B45

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ## 1. Ward's identity at the last index at a matrix -/

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

/-- **(2.56) `WI_calL` at the last index, both charge orders**: as the private `B45_loopL_ward`;
the proof uses `H.IsHermitian` and `Im z ≠ 0` only. -/
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
alternating `σ`: as `B45_ward_fin` with `H.IsHermitian`
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

/-- **(4.31) `jywiiwsoks`, deterministic window step at a matrix**: as `B45_Psum_le` with `sz.STLKM n E u H` for `STLKtensor sz n E u ω`. -/
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

/-! ## 2. The deterministic core at a Hermitian matrix, on `altB4N`/`altB5N` -/

section Det

variable {d : ℕ}

/-- **The `𝒫`-bound and the exponent count at a matrix** (the first half of the deterministic core of `Induction/B45`, at `H`; neither `ϑ` nor `σ`'s tensor
beyond `𝒫` enters): there is `Π ≥ 0` with
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

/-- `(2m+5) M ≤ N^τ` gives `M B^{m+2} X ≤ N^τ B^{m+2} X` (the absorption in the deterministic core). -/
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

/-- **The deterministic core of `(eq:Ward_typeP)` and `(y27kasdfg)` at a matrix** (as in `Induction/B45`; `STLKM … H` for `STLKtensor … ω`, `H.IsHermitian` for `ω`), with the
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

/-- **The deterministic core at a Hermitian matrix** ((4.30) `eq:Ward_typeP`, (4.59) `y27kasdfg`),
restated on `altB4N`, `altB5N`: if `(𝓛-𝒦)^{(m+1)}_{σ'}(H)` is at most `ν X B^{m+1}` at every
label (`hY`), at most `Fv` at labels with `diam_∞ ≥ ℓ_u ω_f` (`hF`), `ϑ` obeys the mollifier bounds and
`(2m+5) M ≤ N^τ`, `M = 3·4^{dm} Γ Λ ν²`, then for alternating `σ`
`|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ N^τ B^{m+2} X` and `‖ℬ₄‖ + ‖ℬ₅‖ ≤ N^τ η⁻¹ B^{m+2} X`, `B = W^{-d}B_{u,0}`.
Per matrix, no probability, no good set (only `H.IsHermitian`); case (i) `N⁻¹ ≤ 1 - u` only, as in `Induction/B45`. -/
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

/-! ## 2g. `B45_det2g` at a Hermitian matrix, on `altB4Ng`/`altB5Ng` (over a carrier) -/

section DetG

variable {d : ℕ} {sz : Sizes d}

/-- The carrier with the matrices fixed at a family `Hs`: `L` is the matrix-level loop `Cm.LM n t (Hs n)` and does not read the sample; `K`, `M`, `S`, `η`, `m` are
those of `Cm`.  It carries the matrix-level statements of this section to the sample-level theorems of `Chain/B45Gen`. -/
private def QLevelsA_frozen (Cm : Step2Mat sz) (Hs : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :
    FlowFM sz :=
  { Cm.toFlowFM with L := fun n t _ σ a _ => Cm.LM n t (Hs n) σ a }

/-- The carrier with fixed matrices is in the Ward class (`ZeroModeGen_WardCls`): the loops of a Hermitian matrix form a Ward family
(`zeroModeGen_loopL_wardFam`, `LoopForm`), `K` is that of `Cm`. -/
private theorem QLevelsA_frozen_ward {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (Hs : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hHs : ∀ n, (Hs n).IsHermitian) : ZeroModeGen_WardCls sz (QLevelsA_frozen Cm Hs) := by
  intro n τ hτ0 hτ1 ω
  obtain ⟨-, TK, -, hK, -, hwK⟩ := hward n τ hτ0 hτ1 ω
  have hη : 0 < Cm.eta n τ := by
    rw [(hL n).2.2.2 τ]; exact mul_pos (by linarith) (hL n).1
  have hz : (ztOf (Cm.m n) (E n) τ).im ≠ 0 := by
    rw [ztOf_im, ← (hL n).2.2.2 τ]; exact hη.ne'
  refine ⟨loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (Hs n)) (ztOf (Cm.m n) (E n) τ), TK, fun k σ a => ?_, hK, ?_, hwK⟩
  · show Cm.LM n τ (Hs n) σ a = _
    rw [(hL n).2.1 τ (Hs n) k σ a]
    exact loopM_eq_loopL d (sz.L n) (sz.W n) _ _ σ a
  · have := zeroModeGen_loopL_wardFam (blockMat d (sz.L n) (sz.W n) (Hs n)) (ztOf (Cm.m n) (E n) τ) ((hHs n).submatrix _) hz
    rw [ztOf_im, ← (hL n).2.2.2 τ] at this
    exact this

/-- **`altB45Ng_levelM`** (band `altB45N_levelM`): `B45_det2g` at a Hermitian matrix `H` over a carrier ((4.30) `eq:Ward_typeP`, (4.59) `y27kasdfg`), restated on `altB4Ng`, `altB5Ng`: if `(𝓛-𝒦)^{(m+1)}_{σ'}(H)` is at most `ν X B^{m+1}` at every label (`hY`), at most `Fv` at labels
with `diam_∞ ≥ ℓ_u ω_f` (`hF`), `ϑ` obeys the mollifier bounds and `(2m+5) K₆ M ≤ N^τ`, `M = 3·4^{dm} Γ Λ ν²`, `Γ = κm⁻¹`, then for alternating `σ`
`|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ N^τ B^{m+2} X` and `‖ℬ₄‖ + ‖ℬ₅‖ ≤ N^τ η⁻¹ B^{m+2} X`, `B = W^{-d}B_{u,0}`, `η = Cm.eta n u`.  The carrier facts are the fields of
`B45Gen_Facts` and `DecayGen_Spec`; `LoopForm` reads `LM` at `H` as the loops of `H` (the sample-level theorem is read through the carrier with fixed matrices). -/
theorem altB45Ng_levelM (hd : 2 ≤ d) (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u κm K₆ : ℝ}
    (hκm : 0 < κm) (hmn : κm ≤ (Cm.m n).im) (him1 : (Cm.m n).im ≤ 1) (heta : ∀ t : ℝ, Cm.eta n t = (1 - t) * (Cm.m n).im)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n) (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} {Γ ν X ωf Fv Λ τ : ℝ} (hΓ : Γ = κm⁻¹) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKMg Cm n u H σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖deriv (fun t : ℝ => ϑ t a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) (a 0) * ϑ u a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) ∧
    ‖altB4Ng Cm n u ϑ σ H a‖ + ‖altB5Ng Cm n u ϑ σ H a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((Cm.eta n u)⁻¹ * sz.Bctl n u ^ (m + 2) * X) := by
  classical
  obtain ⟨Hs, hHs, hHn⟩ : ∃ Hs : ∀ n' : ℕ, Matrix (Idx d (sz.L n') (sz.W n')) (Idx d (sz.L n') (sz.W n')) ℂ,
      (∀ n', (Hs n').IsHermitian) ∧ Hs n = H := by
    refine ⟨fun n' => if h : n' = n then (by subst h; exact H) else 0, fun n' => ?_, by simp⟩
    by_cases h : n' = n
    · subst h; simpa using hH
    · simp [h]
  have hwH := QLevelsA_frozen_ward hL hward Hs hHs
  have hLK : ∀ {m' : ℕ} (σ' : Fin (m' + 1) → Bool) (a' : Fin (m' + 1) → Zd d (sz.L n)),
      STLKtensorg (QLevelsA_frozen Cm Hs) n u (fun _ => 0) σ' a' = STLKMg Cm n u H σ' a' := by
    intro m' σ' a'
    show Cm.LM n u (Hs n) σ' a' - Cm.K n u σ' a' = _
    rw [hHn]; rfl
  have key := B45_det2g hd sz (QLevelsA_frozen Cm Hs) n hκm hmn him1 heta hwH hker hK₆ hrow hcol hu0 hu1 hg hNu (fun _ => 0)
    hΓ hν hX hωf hωd hνN hFv hFv0 hΛ hMΛ (fun σ' a' => by rw [hLK]; exact hY σ' a')
    (fun σ' a' h => by rw [hLK]; exact hF σ' a' h) ϑ hϑ hϑ' σ hσ a
  have e : STLKtensorg (QLevelsA_frozen Cm Hs) n u (fun _ => 0) σ = fun b => STLKMg Cm n u H σ b := funext fun b => hLK σ b
  rw [e] at key
  obtain ⟨k1, k2⟩ := key
  refine ⟨k1, ?_⟩
  have e5 : altB5Ng Cm n u ϑ σ H a =
      -(STPsum (d := d) (fun b => STLKMg Cm n u H σ b) (a 0) * deriv (fun τ => ϑ τ a) u) := rfl
  rw [e5, norm_neg]
  exact k2


/-- **`startLevelQNg`** (band `startLevelQN`): RBM2D's deterministic `AltLevelsQ0` at a Hermitian matrix over a carrier: with the hypotheses of `altB45Ng_levelM`
(without the derivative bound, which only `ℬ₅` uses: the constant-in-time mollifier `fun _ b => ϑ u b` has derivative `0`) and a rank-`(m+2)` level `Y` of `(𝓛-𝒦)_{u,σ}(H)`,
`‖𝒬_u(𝓛-𝒦)_{u,σ}(H)_a‖ ≤ Y + N^τ B_u^{m+2} X`. -/
theorem startLevelQNg (hd : 2 ≤ d) (Cm : Step2Mat sz) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E) (n : ℕ) {u κm K₆ : ℝ}
    (hκm : 0 < κm) (hmn : κm ≤ (Cm.m n).im) (him1 : (Cm.m n).im ≤ 1) (heta : ∀ t : ℝ, Cm.eta n t = (1 - t) * (Cm.m n).im)
    (hward : ZeroModeGen_WardCls sz Cm.toFlowFM) (hker : ZeroModeGen_KerSums Cm.toFlowFM n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer Cm.toFlowFM n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n) (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {m : ℕ} {Γ ν X ωf Fv Λ τ Y : ℝ} (hΓ : Γ = κm⁻¹) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKMg Cm n u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKMg Cm n u H σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 1 + 1) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (hYtop : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖STLKMg Cm n u H σ b‖ ≤ Y)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n)) :
    ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) a‖ ≤
      Y + ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hℓ : 0 < ellT (sz.L n) (sz.lam n) u := lt_of_lt_of_le zero_lt_one (one_le_ellT hL1)
  have h1u : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  have h := (altB45Ng_levelM hd Cm hL n hκm hmn him1 heta hward hker hK₆ hrow hcol hu0 hu1 hg hNu hH hΓ hν hX hωf hωd hνN hFv
    hFv0 hΛ hMΛ hY hF (fun _ b => ϑ u b) hϑ (fun a' => by
      show ‖deriv (fun _ : ℝ => ϑ u a') u‖ ≤ _
      rw [deriv_const, norm_zero]
      exact mul_nonneg (mul_nonneg hΛ h1u) (pow_nonneg (inv_nonneg.2 (pow_nonneg hℓ.le _)) _)) σ hσ a).1
  have e : STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) a =
      STLKMg Cm n u H σ a - STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => STLKMg Cm n u H σ b) (a 0) *
        ϑ u a := rfl
  rw [e]
  exact (norm_sub_le _ _).trans (add_le_add (hYtop a) h)

end DetG


/-! ## 3. The start level of `𝒬_u(𝓛-𝒦)_{u,σ}(H)` -/

section Start

/-- **RBM2D's deterministic `AltLevelsQ0` at a matrix** (`AltLevelsQ0_pointwise`; the start term in Subsection 4.5): with the hypotheses of `altB45N_levelM`
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

end RBM.Ind

end
