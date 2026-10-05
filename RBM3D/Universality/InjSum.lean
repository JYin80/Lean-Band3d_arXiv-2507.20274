/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RBM3D.Universality.Pins
import RBM3D.Green.EntryCore

/-!
# Injective-sum decomposition and `η`-monotonicity of the Stieltjes transform (T2178, UN-03a)

Port of RBM2D `Universality/InjSum.lean` (commit `c9a24cf`, T2204 row R1b; ticket T2178), itself a port of RBM1D `c06b103`, `RBM1D/Flow/StieltjesEtaMonotone.lean` (monotonicity of
`η Im m(E + iη)` for a finite Hermitian matrix) and `RBM1D/Flow/InjectiveSumDecomp.lean`
(a sum over injections `Fin k ↪ n` of a test function is a signed combination of sums over all
maps), with `RBM` replaced by `RBM.Univ`.  The two public definitions `InjSum_IsTestFun` and `InjSum_stieltjes`
that those RBM1D files take from `RBM1D/Flow/Universality.lean` (lines 1542, 1518) are copied
here once, as in RBM1D; `InjSum_stieltjes` has the body of `stieltjesN` (`Universality/Pins.lean`), and
the corollaries `stieltjesN_…` restate the two Stieltjes theorems for `stieltjesN`.
-/

namespace RBM.Univ

open Function Set

/-- The test functions of Theorem 2.6: smooth with compact support (RBM1D
`Flow/Universality.lean:1542`). -/
def InjSum_IsTestFun {k : ℕ} (O : (Fin k → ℝ) → ℝ) : Prop := ContDiff ℝ (⊤ : ℕ∞) O ∧ HasCompactSupport O

/-- The Stieltjes transform `m(z) = N⁻¹ Tr (H - z)⁻¹` (RBM1D `Flow/Universality.lean:1518`). -/
noncomputable def InjSum_stieltjes {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (z : ℂ) :
    ℂ :=
  (Fintype.card n : ℂ)⁻¹ * (green H z).trace

section StieltjesEtaMonotone

open Matrix

/-- Spectral decomposition of the Green's function `(H - z)⁻¹` (RBM2D `Delocalization.lean:47`,
`green_eq_spectral`, commit `c9a24cf`; copied as a private helper because the RBM3D `RBM.green`
(`RBM3D/Green/EntryCore.lean:34`) has no such lemma). -/
private theorem InjSum_green_eq_spectral {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : ∀ l, (hH.eigenvalues l : ℂ) ≠ z) :
    green H z = (hH.eigenvectorUnitary : Matrix n n ℂ)
      * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)
      * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hz1 : (z • 1 : Matrix n n ℂ) = U * diagonal (fun _ => z) * star U := by
    rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hUU']
  have hsub : H - z • 1 = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U := by
    rw [hz1]
    conv_lhs => rw [hspec]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - z) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - z)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - z) * ((hH.eigenvalues l : ℂ) - z)⁻¹)
            = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hz l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- The merged `Gres H z true` (a `Ring.inverse`) is `RBM.green H z = (H - z)⁻¹`
(as `IBPRem_Gres_true` in `RBM3D/Green/IBPRem.lean:105`, private there). -/
private theorem InjSum_Gres_true {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (z : ℂ) : RBM.Gauss.Gres H z true = green H z := by
  simp only [green, RBM.Gauss.Gres, ↓reduceIte, Matrix.nonsing_inv_eq_ringInverse]

/-- For a finite Hermitian matrix, the paper-sign Stieltjes transform has the spectral formula
`Im m(E+iη) = |n|⁻¹ ∑ₗ η / ((λₗ-E)²+η²)`, for positive `η`. -/
theorem stieltjes_im_eq_normalized_specWeight {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    (InjSum_stieltjes H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
  classical
  let U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  let d : n → ℂ := fun l => ((hH.eigenvalues l : ℂ) - (E + η * Complex.I))⁻¹
  have hz (l : n) : (hH.eigenvalues l : ℂ) ≠ E + η * Complex.I := by
    intro h
    have him := congrArg Complex.im h
    have : 0 = η := by simpa using him
    exact (ne_of_gt hη) this.symm
  have hgreen : green H (E + η * Complex.I) = U * diagonal d * star U := by
    exact InjSum_green_eq_spectral hH hz
  have htrace : (green H (E + η * Complex.I)).trace = ∑ l : n, d l := by
    rw [hgreen]
    calc
      (U * diagonal d * star U).trace = (diagonal d * (star U * U)).trace := by
        calc
          (U * diagonal d * star U).trace = (U * (diagonal d * star U)).trace := by
            rw [Matrix.mul_assoc]
          _ = ((diagonal d * star U) * U).trace := by rw [Matrix.trace_mul_comm]
          _ = (diagonal d * (star U * U)).trace := by rw [Matrix.mul_assoc]
      _ = (diagonal d).trace := by rw [Unitary.coe_star_mul_self, Matrix.mul_one]
      _ = ∑ l : n, d l := Matrix.trace_diagonal d
  have himag (l : n) : (d l).im = η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2) := by
    have hn : Complex.normSq ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)) =
        (hH.eigenvalues l - E) ^ 2 + η ^ 2 := by
      rw [Complex.normSq_apply]
      simp
      ring
    have hi : ((hH.eigenvalues l : ℂ) - (E + η * Complex.I)).im = -η := by simp
    simp only [d, Complex.inv_im, hi, hn]
    ring
  rw [InjSum_stieltjes, htrace]
  rw [Complex.mul_im]
  simp [Complex.im_sum, himag]

/-- **Paper's monotonicity used between (2.27) and (2.28).** If `0 < η ≤ ηTilde`, then
`η Im m(E+iη) ≤ ηTilde Im m(E+iηTilde)` for the finite-Hermitian Stieltjes transform
`m(z) = |n|⁻¹ Tr (H-z)⁻¹`. This is the upper-half-plane sign convention of `RBM.InjSum_stieltjes`. -/
theorem stieltjes_eta_mul_im_mono {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ηTilde : ℝ)
    (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (InjSum_stieltjes H (E + η * Complex.I)).im ≤
      ηTilde * (InjSum_stieltjes H (E + ηTilde * Complex.I)).im := by
  have hformula := stieltjes_im_eq_normalized_specWeight H hH E η hη
  have hformulaT := stieltjes_im_eq_normalized_specWeight H hH E ηTilde (by linarith)
  rw [hformula, hformulaT]
  have hterm (l : n) :
      η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) ≤
        ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
    let x := (hH.eigenvalues l - E) ^ 2
    have hx : 0 ≤ x := sq_nonneg _
    have hy : 0 < x + η ^ 2 := by positivity
    have hηT : 0 < ηTilde := lt_of_lt_of_le hη hηTilde
    have hyt : 0 < x + ηTilde ^ 2 := by positivity
    have hsquares : η ^ 2 ≤ ηTilde ^ 2 := by nlinarith [sq_nonneg (ηTilde - η)]
    have hfrac : η ^ 2 / (x + η ^ 2) ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := by
      rw [div_le_div_iff₀ hy hyt]
      have hdiff : 0 ≤ ηTilde ^ 2 - η ^ 2 := by linarith
      nlinarith [mul_nonneg hx hdiff]
    calc
      η * (η / (x + η ^ 2)) = η ^ 2 / (x + η ^ 2) := by field_simp
      _ ≤ ηTilde ^ 2 / (x + ηTilde ^ 2) := hfrac
      _ = ηTilde * (ηTilde / (x + ηTilde ^ 2)) := by field_simp
  have hc : 0 ≤ (Fintype.card n : ℝ)⁻¹ := by positivity
  calc
    η * ((Fintype.card n : ℝ)⁻¹ * ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
        = (Fintype.card n : ℝ)⁻¹ *
            ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
          calc
            η * ((Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))
                = η * ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by rw [Finset.mul_sum]
            _ = ∑ l : n, η * ((Fintype.card n : ℝ)⁻¹ *
                    (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by rw [Finset.mul_sum]
            _ = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = (Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, η * (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) := by
                      rw [Finset.mul_sum]
    _ ≤ (Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun l _ => hterm l) hc
    _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
          ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
          calc
            (Fintype.card n : ℝ)⁻¹ *
                ∑ l : n, ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))
                = ∑ l : n, (Fintype.card n : ℝ)⁻¹ *
                    (ηTilde * (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      rw [Finset.mul_sum]
            _ = ∑ l : n, ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    (ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2))) := by
                      apply Finset.sum_congr rfl
                      intro l hl
                      ring
            _ = ηTilde * ((Fintype.card n : ℝ)⁻¹ *
                    ∑ l : n, ηTilde / ((hH.eigenvalues l - E) ^ 2 + ηTilde ^ 2)) := by
                      rw [Finset.mul_sum, Finset.mul_sum]


/-- `stieltjesN` has the body of `InjSum_stieltjes`. -/
theorem InjSum_stieltjesN_eq_stieltjes {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ)
    (z : ℂ) : stieltjesN H z = InjSum_stieltjes H z := by
  simp only [stieltjesN, InjSum_stieltjes, InjSum_Gres_true]

theorem stieltjesN_im_eq_normalized_specWeight {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η : ℝ) (hη : 0 < η) :
    (stieltjesN H (E + η * Complex.I)).im =
      (Fintype.card n : ℝ)⁻¹ * ∑ l : n,
        (η / ((hH.eigenvalues l - E) ^ 2 + η ^ 2)) :=
  by rw [InjSum_stieltjesN_eq_stieltjes]; exact stieltjes_im_eq_normalized_specWeight H hH E η hη

theorem stieltjesN_eta_mul_im_mono {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (E η ηTilde : ℝ)
    (hη : 0 < η) (hηTilde : η ≤ ηTilde) :
    η * (stieltjesN H (E + η * Complex.I)).im ≤
      ηTilde * (stieltjesN H (E + ηTilde * Complex.I)).im :=
  by simp only [InjSum_stieltjesN_eq_stieltjes]; exact stieltjes_eta_mul_im_mono H hH E η ηTilde hη hηTilde

end StieltjesEtaMonotone

section InjectiveSumDecomp

/-! ### Generic topology helper -/

private lemma hasCompactSupport_comp_of_retraction {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] {O : Y → ℝ} (hO : HasCompactSupport O)
    {Φ : X → Y} {Ψ : Y → X} (hΦ : Continuous Φ) (hΨ : Continuous Ψ)
    (hΨΦ : ∀ x, Ψ (Φ x) = x) : HasCompactSupport (O ∘ Φ) := by
  have hsupp : Function.support (O ∘ Φ) = Φ ⁻¹' Function.support O := by
    ext x; simp [Function.mem_support, Function.comp]
  have h2 : IsCompact (Φ ⁻¹' tsupport O) := by
    have hsub : Φ ⁻¹' tsupport O ⊆ Ψ '' (tsupport O) := fun x hx => ⟨Φ x, hx, hΨΦ x⟩
    exact (hO.image hΨ).of_isClosed_subset ((isClosed_tsupport O).preimage hΦ) hsub
  have h1 : closure (Φ ⁻¹' Function.support O) ⊆ Φ ⁻¹' (tsupport O) := by
    apply closure_minimal (preimage_mono subset_closure)
    exact (isClosed_tsupport O).preimage hΦ
  show IsCompact (closure (Function.support (O ∘ Φ)))
  rw [hsupp]
  exact h2.of_isClosed_subset isClosed_closure h1

/-! ### Extending an embedding `Fin k ↪ n` by one point -/

private noncomputable def embSnocEquiv {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) :
    (Fin (k + 1) ↪ n) ≃ Σ f : Fin k ↪ n, {a : n // a ∉ Set.range f} where
  toFun f := ⟨Fin.Embedding.init f, ⟨f (Fin.last k), by
    rintro ⟨j, hj⟩
    have hj' : f j.castSucc = f (Fin.last k) := hj
    have := f.injective hj'
    exact absurd this (Fin.castSucc_lt_last j).ne⟩⟩
  invFun p := Fin.Embedding.snoc p.1 p.2.2
  left_inv f := by
    apply DFunLike.ext
    intro i
    induction i using Fin.lastCases with
    | last => simp [Fin.Embedding.coe_snoc]
    | cast j =>
      show (Fin.Embedding.snoc (Fin.Embedding.init f) _) j.castSucc = f j.castSucc
      rw [Fin.Embedding.snoc_castSucc]
      rfl
  right_inv := by
    rintro ⟨f, a, ha⟩
    ext1
    · show Fin.Embedding.init (Fin.Embedding.snoc f ha) = f
      apply DFunLike.ext
      intro j
      show (Fin.Embedding.snoc f ha) j.castSucc = f j
      rw [Fin.Embedding.snoc_castSucc]
    · show (Fin.Embedding.snoc f ha) (Fin.last k) = a
      rw [Fin.Embedding.snoc_last]

private lemma sum_embedding_snoc_split {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (F : (Fin (k + 1) ↪ n) → ℝ) :
    ∑ f : Fin (k + 1) ↪ n, F f =
      ∑ f' : Fin k ↪ n, ∑ a : {a : n // a ∉ Set.range f'},
        F ((embSnocEquiv k).symm ⟨f', a⟩) := by
  rw [← Equiv.sum_comp (embSnocEquiv k).symm F, Fintype.sum_sigma]

private lemma sum_compl_range_split {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ)
    (f' : Fin k ↪ n) (G : n → ℝ) :
    ∑ a : {a : n // a ∉ Set.range f'}, G a.1 =
      ∑ a : n, G a - ∑ i : Fin k, G (f' i) := by
  have h1 : ∑ a ∈ (Finset.univ.image f' : Finset n)ᶜ, G a
      = ∑ a : {a : n // a ∉ Set.range f'}, G a.1 :=
    Finset.sum_subtype _ (by simp) G
  rw [← h1]
  have h2 : ∑ a ∈ (Finset.univ.image f' : Finset n)ᶜ, G a
      = ∑ a : n, G a - ∑ a ∈ (Finset.univ.image f' : Finset n), G a := by
    rw [eq_sub_iff_add_eq, Finset.sum_compl_add_sum]
  rw [h2]
  congr 1
  rw [Finset.sum_image]
  intro x _ y _ hxy
  exact f'.injective hxy

private lemma sum_cons_reindex {n : Type*} [Fintype n] [DecidableEq n] (m : ℕ)
    (G : n → (Fin m → n) → ℝ) :
    ∑ x : n, ∑ h : Fin m → n, G x h = ∑ z : Fin (m + 1) → n, G (z 0) (z ∘ Fin.succ) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => n))
    (fun p => G p.1 p.2) (fun z => G (z 0) (z ∘ Fin.succ)) (fun p => ?_)
  simp [Fin.consEquiv]

private lemma sum_unique_emb_zero {n : Type*} [Fintype n] [DecidableEq n]
    (F : (Fin 0 ↪ n) → ℝ) : ∑ f : Fin 0 ↪ n, F f = F Function.Embedding.ofIsEmpty := by
  have : Unique (Fin 0 ↪ n) := by
    refine ⟨⟨Function.Embedding.ofIsEmpty⟩, fun f => ?_⟩
    apply DFunLike.ext
    exact isEmptyElim
  rw [Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

private lemma comp_snoc {n : Type*} {k : ℕ} (lam : n → ℝ) (u : Fin k → n) (x : n) :
    lam ∘ (Fin.snoc u x : Fin (k + 1) → n) = Fin.snoc (lam ∘ u) (lam x) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

/-! ### The two-argument test-function class and its decomposition statement -/

private def IsTestFun2 {k m : ℕ} (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry O) ∧ HasCompactSupport (Function.uncurry O)

private def BddByR {k m : ℕ} (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∀ x y, O x y ≠ 0 → (∀ j, |x j| ≤ R) ∧ (∀ j, |y j| ≤ R)

private def Decomp2 (k m : ℕ) (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (kk : ι → ℕ) (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ),
    (∀ i, kk i ≤ k + m) ∧ (∀ i, InjSum_IsTestFun (Oj i)) ∧
    (∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ R) ∧
    ∀ (n : Type) [Fintype n] [DecidableEq n] (lam : n → ℝ),
      ∑ f : Fin k ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
        ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g)

/-! ### Base case `k = 0` -/

private lemma decomp2_zero (m : ℕ) (O : (Fin 0 → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ)
    (hO : IsTestFun2 O) (hR : BddByR O R) : Decomp2 0 m O R := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => m, fun _ => O Fin.elim0, ?_, ?_, ?_, ?_⟩
  · intro _; simp
  · intro _
    have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) :=
      contDiff_const.prodMk contDiff_id
    have hΨ : Continuous (fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) :=
      continuous_const.prodMk continuous_id
    refine ⟨hO.1.comp hΦ, ?_⟩
    have := hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2
      (Φ := fun z : Fin m → ℝ => ((Fin.elim0 : Fin 0 → ℝ), z)) (Ψ := Prod.snd)
      hΨ continuous_snd (fun z => rfl)
    exact this
  · intro _ x hx j
    exact (hR Fin.elim0 x hx).2 j
  · intro n _ _ lam
    rw [sum_unique_emb_zero]
    have hlam0 : lam ∘ (Function.Embedding.ofIsEmpty : Fin 0 ↪ n) = (Fin.elim0 : Fin 0 → ℝ) := by
      funext i; exact i.elim0
    rw [hlam0]
    simp

/-! ### The inductive step -/

private def mkO1 {k m : ℕ} (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) :
    (Fin k → ℝ) → (Fin (m + 1) → ℝ) → ℝ :=
  fun y z => O (Fin.snoc y (z 0)) (z ∘ Fin.succ)

private def mkO2 {k m : ℕ} (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) (i : Fin k) :
    (Fin k → ℝ) → (Fin m → ℝ) → ℝ :=
  fun y z => O (Fin.snoc y (y i)) z

private lemma isTestFun2_mkO1 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ}
    (hO : IsTestFun2 O) : IsTestFun2 (mkO1 O) := by
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        (Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ))).prodMk ?_
    · apply contDiff_pi'
      intro i
      induction i using Fin.lastCases with
      | last => simp only [Fin.snoc_last]; exact (contDiff_apply ℝ ℝ (0 : Fin (m + 1))).comp contDiff_snd
      | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
    · apply contDiff_pi'
      intro i
      exact (contDiff_apply ℝ ℝ (i.succ)).comp contDiff_snd
  have hΦc : Continuous
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := hΦcd.continuous
  have hΨcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) =>
        (Fin.init p.1, (Fin.cons (p.1 (Fin.last k)) p.2 : Fin (m + 1) → ℝ))) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) => Fin.init p.1)).prodMk ?_
    · apply contDiff_pi'
      intro j
      exact (contDiff_apply ℝ ℝ (j.castSucc)).comp contDiff_fst
    · apply contDiff_pi'
      intro i
      induction i using Fin.cases with
      | zero => simp only [Fin.cons_zero]; exact (contDiff_apply ℝ ℝ (Fin.last k)).comp contDiff_fst
      | succ j => simp only [Fin.cons_succ]; exact (contDiff_apply ℝ ℝ j).comp contDiff_snd
  have hΨc : Continuous
      (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) =>
        (Fin.init p.1, (Fin.cons (p.1 (Fin.last k)) p.2 : Fin (m + 1) → ℝ))) := hΨcd.continuous
  have hret : ∀ p : (Fin k → ℝ) × (Fin (m + 1) → ℝ),
      (Fin.init (Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ),
          (Fin.cons ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ) (Fin.last k)) (p.2 ∘ Fin.succ)
            : Fin (m + 1) → ℝ)) = p := by
    rintro ⟨y, z⟩
    have e1 : Fin.init (Fin.snoc y (z 0) : Fin (k + 1) → ℝ) = y := by simp
    have e2 : (Fin.snoc y (z 0) : Fin (k + 1) → ℝ) (Fin.last k) = z 0 := by simp
    simp only [e1, e2]
    congr 1
    exact Fin.cons_self_tail z
  have hEq : Function.uncurry (mkO1 O) = Function.uncurry O ∘
      (fun p : (Fin k → ℝ) × (Fin (m + 1) → ℝ) =>
        ((Fin.snoc p.1 (p.2 0) : Fin (k + 1) → ℝ), p.2 ∘ Fin.succ)) := by
    funext p; rfl
  rw [IsTestFun2, hEq]
  exact ⟨hO.1.comp hΦcd, hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2 hΦc hΨc hret⟩

private lemma isTestFun2_mkO2 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} (i : Fin k)
    (hO : IsTestFun2 O) : IsTestFun2 (mkO2 O i) := by
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) := by
    refine (?_ : ContDiff ℝ (⊤:ℕ∞) (fun p : (Fin k → ℝ) × (Fin m → ℝ) =>
        (Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ))).prodMk contDiff_snd
    apply contDiff_pi'
    intro j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
    | cast j => simp only [Fin.snoc_castSucc]; exact (contDiff_apply ℝ ℝ j).comp contDiff_fst
  have hΦc : Continuous
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) :=
    hΦcd.continuous
  have hΨc : Continuous (fun p : (Fin (k + 1) → ℝ) × (Fin m → ℝ) => (Fin.init p.1, p.2)) := by
    fun_prop
  have hret : ∀ p : (Fin k → ℝ) × (Fin m → ℝ),
      (Fin.init (Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2) = p := by
    rintro ⟨y, z⟩
    have e1 : Fin.init (Fin.snoc y (y i) : Fin (k + 1) → ℝ) = y := by simp
    rw [e1]
  have hEq : Function.uncurry (mkO2 O i) = Function.uncurry O ∘
      (fun p : (Fin k → ℝ) × (Fin m → ℝ) => ((Fin.snoc p.1 (p.1 i) : Fin (k + 1) → ℝ), p.2)) := by
    funext p; rfl
  rw [IsTestFun2, hEq]
  exact ⟨hO.1.comp hΦcd, hasCompactSupport_comp_of_retraction (O := Function.uncurry O) hO.2 hΦc hΨc hret⟩

private lemma bddByR_mkO1 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} {R : ℝ}
    (hR : BddByR O R) : BddByR (mkO1 O) R := by
  intro y z hz
  have hz' := hR (Fin.snoc y (z 0)) (z ∘ Fin.succ) hz
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := hz'.1 j.castSucc
    rwa [Fin.snoc_castSucc] at this
  · induction j using Fin.cases with
    | zero => have := hz'.1 (Fin.last k); rwa [Fin.snoc_last] at this
    | succ j => exact hz'.2 j

private lemma bddByR_mkO2 {k m : ℕ} {O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ} {R : ℝ} (i : Fin k)
    (hR : BddByR O R) : BddByR (mkO2 O i) R := by
  intro y z hz
  have hz' := hR (Fin.snoc y (y i)) z hz
  refine ⟨fun j => ?_, fun j => hz'.2 j⟩
  have := hz'.1 j.castSucc
  rwa [Fin.snoc_castSucc] at this

/-! ### The key combinatorial identity for the inductive step -/

private lemma key_identity {n : Type*} [Fintype n] [DecidableEq n] {k m : ℕ}
    (O : (Fin (k + 1) → ℝ) → (Fin m → ℝ) → ℝ) (lam : n → ℝ) :
    ∑ f : Fin (k + 1) ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
      (∑ f' : Fin k ↪ n, ∑ z : Fin (m + 1) → n, mkO1 O (lam ∘ f') (lam ∘ z)) -
        ∑ i : Fin k, ∑ f' : Fin k ↪ n, ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h) := by
  have step1 : ∑ f : Fin (k + 1) ↪ n, ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h) =
      ∑ f' : Fin k ↪ n, ∑ a : {a : n // a ∉ Set.range f'},
        ∑ h : Fin m → n, O (lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩)) (lam ∘ h) :=
    sum_embedding_snoc_split k (fun f => ∑ h : Fin m → n, O (lam ∘ f) (lam ∘ h))
  rw [step1]
  have step2 : ∀ (f' : Fin k ↪ n) (a : {a : n // a ∉ Set.range f'}),
      ∑ h : Fin m → n, O (lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩)) (lam ∘ h) =
        ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a.1)) (lam ∘ h) := by
    intro f' a
    have hco : lam ∘ ((embSnocEquiv k).symm ⟨f', a⟩ : Fin (k + 1) ↪ n) =
        Fin.snoc (lam ∘ (f' : Fin k → n)) (lam a.1) := by
      show lam ∘ (Fin.Embedding.snoc f' a.2 : Fin (k + 1) ↪ n) = _
      rw [show (⇑(Fin.Embedding.snoc f' a.2) : Fin (k + 1) → n) = Fin.snoc (⇑f') a.1 from
        Fin.Embedding.coe_snoc f' a.2]
      exact comp_snoc lam f' a.1
    rw [hco]
  simp_rw [step2]
  have step3 : ∀ f' : Fin k ↪ n,
      ∑ a : {a : n // a ∉ Set.range f'}, ∑ h : Fin m → n,
          O (Fin.snoc (lam ∘ f') (lam a.1)) (lam ∘ h) =
        (∑ a : n, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h)) -
          ∑ i : Fin k, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam (f' i))) (lam ∘ h) := by
    intro f'
    exact sum_compl_range_split k f'
      (fun a => ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h))
  simp_rw [step3]
  have step4 : ∀ f' : Fin k ↪ n,
      ∑ a : n, ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h) =
        ∑ z : Fin (m + 1) → n, mkO1 O (lam ∘ f') (lam ∘ z) := by
    intro f'
    rw [sum_cons_reindex m (fun a h => O (Fin.snoc (lam ∘ f') (lam a)) (lam ∘ h))]
    rfl
  simp_rw [step4]
  have step5 : ∀ (f' : Fin k ↪ n) (i : Fin k),
      ∑ h : Fin m → n, O (Fin.snoc (lam ∘ f') (lam (f' i))) (lam ∘ h) =
        ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h) := by
    intro f' i; rfl
  simp_rw [step5]
  rw [Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

/-! ### Main induction -/

private lemma decomp2_of_testFun2 : ∀ (k m : ℕ) (O : (Fin k → ℝ) → (Fin m → ℝ) → ℝ) (R : ℝ),
    IsTestFun2 O → BddByR O R → Decomp2 k m O R := by
  intro k
  induction k with
  | zero => exact decomp2_zero
  | succ k ih =>
    intro m O R hO hR
    obtain ⟨ι1, fι1, c1, kk1, Oj1, hkk1, hTest1, hBound1, heq1⟩ :=
      ih (m + 1) (mkO1 O) R (isTestFun2_mkO1 hO) (bddByR_mkO1 hR)
    have D2 : ∀ i : Fin k, Decomp2 k m (mkO2 O i) R := fun i =>
      ih m (mkO2 O i) R (isTestFun2_mkO2 i hO) (bddByR_mkO2 i hR)
    choose ι2 fι2 c2 kk2 Oj2 hkk2 hTest2 hBound2 heq2 using D2
    let _ := fι1
    let _ := fι2
    refine ⟨ι1 ⊕ (Σ i : Fin k, ι2 i), inferInstance,
      Sum.elim c1 (fun p => -(c2 p.1 p.2)),
      fun i => match i with
        | Sum.inl j => kk1 j
        | Sum.inr p => kk2 p.1 p.2,
      fun i => match i with
        | Sum.inl j => Oj1 j
        | Sum.inr p => Oj2 p.1 p.2,
      ?_, ?_, ?_, ?_⟩
    · rintro (j | ⟨i,j⟩)
      · dsimp only; have := hkk1 j; omega
      · dsimp only; have := hkk2 i j; omega
    · rintro (j | ⟨i,j⟩)
      · exact hTest1 j
      · exact hTest2 i j
    · rintro (j | ⟨i,j⟩) x hx
      · exact hBound1 j x hx
      · exact hBound2 i j x hx
    · intro n _ _ lam
      rw [key_identity O lam, heq1 n lam]
      have hsum2 : ∀ i : Fin k,
          ∑ f' : Fin k ↪ n, ∑ h : Fin m → n, mkO2 O i (lam ∘ f') (lam ∘ h)
            = ∑ j : ι2 i, (c2 i j : ℝ) * ∑ g : Fin (kk2 i j) → n, Oj2 i j (lam ∘ g) :=
        fun i => heq2 i n lam
      simp_rw [hsum2]
      rw [Fintype.sum_sum_type, Fintype.sum_sigma]
      simp only [Sum.elim_inl, Sum.elim_inr]
      push_cast
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring

/-! ### Top-level theorem -/

theorem injSum_decomp (k : ℕ) {O : (Fin k → ℝ) → ℝ} (hO : InjSum_IsTestFun O) {R : ℝ}
    (hR : ∀ x, O x ≠ 0 → ∀ j, |x j| ≤ R) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (kk : ι → ℕ)
      (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ),
      (∀ i, kk i ≤ k) ∧ (∀ i, InjSum_IsTestFun (Oj i)) ∧
      (∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ R) ∧
      ∀ (n : Type) [Fintype n] [DecidableEq n] (lam : n → ℝ),
        ∑ f : Fin k ↪ n, O (lam ∘ f) = ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g) := by
  have hO2 : IsTestFun2 (fun x (_ : Fin 0 → ℝ) => O x) := by
    refine ⟨hO.1.comp contDiff_fst, ?_⟩
    exact hasCompactSupport_comp_of_retraction (O := O) hO.2 continuous_fst
      (Ψ := fun x => (x, (Fin.elim0 : Fin 0 → ℝ)))
      (by fun_prop) (fun p => by ext <;> simp [Subsingleton.elim p.2 (Fin.elim0 : Fin 0 → ℝ)])
  have hR2 : BddByR (fun x (_ : Fin 0 → ℝ) => O x) R := by
    intro x y hx
    exact ⟨hR x hx, fun j => j.elim0⟩
  obtain ⟨ι, fι, c, kk, Oj, hkk, hTest, hBound, heq⟩ := decomp2_of_testFun2 k 0 _ R hO2 hR2
  refine ⟨ι, fι, c, kk, Oj, hkk, hTest, hBound, ?_⟩
  intro n _ _ lam
  have := heq n lam
  simp only [Fintype.sum_unique] at this
  exact this

end InjectiveSumDecomp

/-! ### Compiled nonempty instances (CLAUDE.md §4 step 2) -/

namespace InjSumCheck

/-- The `C_c^∞` bump of radius `2` (equal to `1` on the unit ball) on `ℝ^k`. -/
private noncomputable def bump (k : ℕ) : ContDiffBump (0 : Fin k → ℝ) := ⟨1, 2, one_pos, by norm_num⟩

private theorem bump_isTestFun (k : ℕ) : InjSum_IsTestFun (bump k) :=
  ⟨(bump k).contDiff, (bump k).hasCompactSupport⟩

/-- `diag(1,2,3)`. -/
private noncomputable def diag123 : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i : Fin 3 => (((i : ℕ) + 1 : ℝ) : ℂ))

private theorem diag123_herm : diag123.IsHermitian :=
  Matrix.isHermitian_diagonal_of_self_adjoint _ (by
    ext i; simp)

/-- `stieltjes_im_eq_normalized_specWeight` at `diag(1,2,3)`, `E = 0`, `η = 1/10`. -/
example :
    (InjSum_stieltjes diag123 (((0 : ℝ) : ℂ) + (((1 / 10 : ℝ)) : ℂ) * Complex.I)).im =
      (Fintype.card (Fin 3) : ℝ)⁻¹ * ∑ l : Fin 3,
        ((1 / 10 : ℝ) / ((diag123_herm.eigenvalues l - 0) ^ 2 + (1 / 10 : ℝ) ^ 2)) :=
  stieltjes_im_eq_normalized_specWeight diag123 diag123_herm 0 (1 / 10) (by norm_num)

/-- `stieltjes_eta_mul_im_mono` at `diag(1,2,3)`, `E = 0`, `η = 1/10 ≤ 1 = η̃`. -/
example :
    (1 / 10 : ℝ) * (InjSum_stieltjes diag123 (((0 : ℝ) : ℂ) + (((1 / 10 : ℝ)) : ℂ) * Complex.I)).im ≤
      (1 : ℝ) * (InjSum_stieltjes diag123 (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im :=
  stieltjes_eta_mul_im_mono diag123 diag123_herm 0 (1 / 10) 1 (by norm_num) (by norm_num)

/-- `stieltjesN_im_eq_normalized_specWeight` at `diag(1,2,3)`, `z = I/10`. -/
example :
    (stieltjesN diag123 (((0 : ℝ) : ℂ) + (((1 / 10 : ℝ)) : ℂ) * Complex.I)).im =
      (Fintype.card (Fin 3) : ℝ)⁻¹ * ∑ l : Fin 3,
        ((1 / 10 : ℝ) / ((diag123_herm.eigenvalues l - 0) ^ 2 + (1 / 10 : ℝ) ^ 2)) :=
  stieltjesN_im_eq_normalized_specWeight diag123 diag123_herm 0 (1 / 10) (by norm_num)

/-- `stieltjesN_eta_mul_im_mono` at `diag(1,2,3)`, `E = 0`, `η = 1/10 ≤ 1 = η̃`. -/
example :
    (1 / 10 : ℝ) * (stieltjesN diag123 (((0 : ℝ) : ℂ) + (((1 / 10 : ℝ)) : ℂ) * Complex.I)).im ≤
      (1 : ℝ) * (stieltjesN diag123 (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I)).im :=
  stieltjesN_eta_mul_im_mono diag123 diag123_herm 0 (1 / 10) 1 (by norm_num) (by norm_num)

/-- `injSum_decomp` at `k = 2` and the bump on `ℝ²` (`R = 2`; nondegenerate: `bump 2 0 = 1`). -/
example : (bump 2) 0 = 1 ∧
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℤ) (kk : ι → ℕ)
      (Oj : ∀ i, (Fin (kk i) → ℝ) → ℝ),
      (∀ i, kk i ≤ 2) ∧ (∀ i, InjSum_IsTestFun (Oj i)) ∧
      (∀ i x, Oj i x ≠ 0 → ∀ j, |x j| ≤ 2) ∧
      ∀ (n : Type) [Fintype n] [DecidableEq n] (lam : n → ℝ),
        ∑ f : Fin 2 ↪ n, (bump 2) (lam ∘ f) =
          ∑ i, (c i : ℝ) * ∑ g : Fin (kk i) → n, Oj i (lam ∘ g) := by
  refine ⟨(bump 2).one_of_mem_closedBall (Metric.mem_closedBall_self (bump 2).rIn_pos.le),
    injSum_decomp 2 (bump_isTestFun 2) (R := 2) ?_⟩
  intro x hx j
  have hx' : x ∈ Function.support (bump 2) := hx
  rw [(bump 2).support_eq, Metric.mem_ball, dist_zero_right] at hx'
  exact (norm_le_pi_norm x j).trans hx'.le

end InjSumCheck

end RBM.Univ
