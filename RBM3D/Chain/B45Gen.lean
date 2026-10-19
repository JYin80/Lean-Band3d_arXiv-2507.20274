/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.KDecayGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step5CasesGen
import RBM3D.Induction.B45

/-!
# (4.30) `eq:Ward_typeP` and (4.59) `y27kasdfg` over the flow carrier

Generic form of `Induction/B45` over a carrier `C : FlowFM sz` and a law `μ`.

* **The class `B45Gen_Facts`**: the carrier facts that replace the band objects of `B45`: the
  last-label Ward step (`ZeroModeGen_WardCls`, one Ward statement), the Ward pair
  (`DecayGen_WardPair`), and the row sums and column sums of `Step2Gen_thetaKer` (in place of
  `B45_row_thetaKer`, `QopAlgebra_col_sum_thetaKer`, `‖μ‖ = 1`).  Two further fields: `Im m ≤ 1`
  (the band `norm_mE`; it gives `η_u ≤ 1 - u`, hence `(1-u)⁻¹ ≤ η_u⁻¹` in `ℬ₅`) and
  `ZeroModeGen_KerSums` (it makes the column sums of `thetaKer` constant in the column, which the
  slots `i ≥ 1` of `𝒫 Θ 𝒜` need).
* **Generic versions of the band helpers**: `B45_ward_fing`, `B45_Psum_LK_leg`, `B45_norm_kappag`,
  `B45_norm_ThetaN_leg`, `B45Gen_Psum_ThetaN_le`, `B45_B4_leg`, `B45_scalesg`, `B45_detg`,
  `B45_det2g`.

The private helpers of `B45` that mention no band object are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private B45_slot_zero B45_slot_succ B45_norm_colsum from RBM3D.Induction.B45
open private ZeroModeGen_thetaKer_colConst from RBM3D.Chain.ZeroModeGen

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The class `B45Gen_Facts` -/

/-- **The class `B45Gen_Facts`**: for every `κ > 0` one `C₆ > 0` such that, along
every flow of the family, the carrier has the last-label Ward step (`ZeroModeGen_WardCls`), the Ward pair
(`DecayGen_WardPair`), `Im m ≤ 1` (band: `norm_mE`), constant row and column sums of the generator (`ZeroModeGen_KerSums`), and, for every charge pair and `0 ≤ t < 1`, row sums and column-sum moduli of `Step2Gen_thetaKer` at most
`C₆/(1 - t)`.  `STKcalDecaygL` is not a field: it stays an explicit hypothesis. -/
def B45Gen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ZeroModeGen_WardCls sz (mk sz z) ∧ DecayGen_WardPair (mk sz z) ∧ (∀ n : ℕ, ((mk sz z).m n).im ≤ 1) ∧
        (∀ n : ℕ, ZeroModeGen_KerSums (mk sz z) n) ∧
        ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
          (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧
          ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)

/-! ## 2. Ward at the last label, the window split, the kernel norms -/

section Ward

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **Ward's identity at the last index** for `𝓛 - 𝒦` over a carrier (Lemma 2.15 `lem_WI_K`, (2.56) `WI_calL`), alternating `σ` (`σ_last = ¬σ_0`):
`Σ_x (𝓛-𝒦)^{(m+2)}_{σ,(a',x)} = (2iW^d η)⁻¹ ((𝓛-𝒦)^{(m+1)}_{σ⁺,a'} - (𝓛-𝒦)^{(m+1)}_{σ⁻,a'})`, `η = C.eta n u`.  Band: `B45_ward_fin`;
the hypothesis is the one Ward statement `ZeroModeGen_WardCls`. -/
theorem B45_ward_fing (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz.SeqΩ)
    {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a' : Fin (m + 1) → Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), STLKtensorg C n u ω σ (Fin.snoc (α := fun _ => Zd d (sz.L n)) a' x) =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n u : ℂ))⁻¹ *
        (STLKtensorg C n u ω (B45_sgnCons true σ) a' - STLKtensorg C n u ω (B45_sgnCons false σ) a') := by
  obtain ⟨TL, TK, hL, hK, hwL, hwK⟩ := hward n u hu0 hu1 ω
  set μ : List Bool := List.ofFn (fun i : Fin m => σ (Fin.succ (Fin.castSucc i))) with hμ
  have hlen : (List.ofFn a').length = μ.length + 1 := by simp [hμ]
  have hlist := B45_ofFn_sigma σ hσ
  have h1 := hwL.2 (σ 0) μ (List.ofFn a') hlen
  have h2 := hwK.2 (σ 0) μ (List.ofFn a') hlen
  simp only [STLKtensorg, Finset.sum_sub_distrib, hL, hK, loopOf, B45_ofFn_snoc, hlist, B45_ofFn_sgnCons, hμ.symm]
  rw [h1, h2]
  ring

end Ward

/-- `‖(2 i W^d η)⁻¹‖ = (2 W^d η)⁻¹` for `η > 0` (band `B45_norm_kappa`; here `η` is a free positive real). -/
theorem B45_norm_kappag {d : ℕ} (sz : Sizes d) (n : ℕ) {η : ℝ} (hη : 0 < η) :
    ‖(2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (η : ℂ))⁻¹‖ = (2 * (((sz.W n : ℕ) : ℝ) ^ d * η))⁻¹ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  rw [norm_inv, norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hη.le]
  simp only [Complex.norm_natCast, Complex.norm_ofNat, mul_one]
  congr 1
  ring

section Window

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **(4.31) `jywiiwsoks`, deterministic window step over a carrier.**  For alternating `σ`, Ward's identity at the last label reduces
`𝒫(𝓛-𝒦)^{(m+2)}` to `(2iW^dη)⁻¹` times the difference of two `𝒫` of `(𝓛-𝒦)^{(m+1)}`, each split into the window `diam_∞ < R` and its
complement; `η = C.eta n u > 0` is a hypothesis. -/
theorem B45_Psum_LK_leg (hward : ZeroModeGen_WardCls sz C) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hη : 0 < C.eta n u) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0)
    (a₁ : Zd d (sz.L n)) {R Y F : ℝ} (hR : 0 ≤ R) (hF0 : 0 ≤ F)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)), ‖STLKtensorg C n u ω σ' a'‖ ≤ Y)
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)), a' 0 = a₁ →
      R ≤ (STdiamInf a' : ℝ) → ‖STLKtensorg C n u ω σ' a'‖ ≤ F) :
    ‖STPsum (d := d) (STLKtensorg C n u ω σ) a₁‖ ≤
      (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ *
        (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F) := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hP : ∀ b : Bool, ‖STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons b σ)) a₁‖ ≤
      ((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F := fun b =>
    B45_Psum_le _ a₁ hR (hY _) hF0 (fun a' h0 hfar => hF _ a' h0 hfar)
  have hsum : STPsum (d := d) (STLKtensorg C n u ω σ) a₁ =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n u : ℂ))⁻¹ *
        (STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons true σ)) a₁ -
          STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons false σ)) a₁) := by
    rw [B45_Psum_snoc]
    simp only [B45_ward_fing C hward n hu0 hu1 ω σ hσ]
    unfold STPsum
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum, norm_mul, B45_norm_kappag sz n hη]
  have hd := norm_sub_le (STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons true σ)) a₁)
    (STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons false σ)) a₁)
  have h2 := add_le_add (hP true) (hP false)
  have hpos : 0 ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u))⁻¹ := by positivity
  calc (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u))⁻¹ *
        ‖STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons true σ)) a₁ -
          STPsum (d := d) (STLKtensorg C n u ω (B45_sgnCons false σ)) a₁‖
      ≤ (2 * (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u))⁻¹ *
          (2 * (((2 * R + 2) ^ d) ^ m * Y + (((sz.L n : ℕ) : ℝ) ^ d) ^ m * F)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpos
    _ = _ := by
        rw [mul_inv]; field_simp

end Window

section ThetaNorm

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ)

/-- **`‖Θ^{(k)}_{u,σ} 𝒜‖_max ≤ k (K₆/(1-u)) ‖𝒜‖_max`** over a carrier: row sums of the one-index kernels `Step2Gen_thetaKer`
(`hrow`).  Band: `B45_norm_ThetaN_le` (`K₆ = 1`, `‖μ‖ = 1`). -/
theorem B45_norm_ThetaN_leg {K₆ : ℝ}
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {k : ℕ} (σ : Fin k → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {A : (Fin k → Zd d (sz.L n)) → ℂ} {M : ℝ}
    (hA : ∀ b, ‖A b‖ ≤ M) (a : Fin k → Zd d (sz.L n)) :
    ‖Step2Gen_ThetaN C n σ u A a‖ ≤ (k : ℝ) * (K₆ / (1 - u)) * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA a)
  unfold Step2Gen_ThetaN
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin k, ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b *
          A (Function.update a i b)‖
      ≤ ∑ _i : Fin k, K₆ / (1 - u) * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hr := hrow (σ i) (σ (finRotate k i)) u hu0 hu1 (a i)
        calc ‖∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b *
              A (Function.update a i b)‖
            ≤ ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b *
              A (Function.update a i b)‖ := norm_sum_le _ _
          _ ≤ ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖ * M :=
              Finset.sum_le_sum fun b _ => by
                rw [norm_mul]
                exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
          _ = (∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ i) (σ (finRotate k i)) u (a i) b‖) * M :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ K₆ / (1 - u) * M := mul_le_mul_of_nonneg_right hr hM
    _ = (k : ℝ) * (K₆ / (1 - u)) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **`‖𝒫(Θ_{t,σ}𝒜)‖_max ≤ (m+1)(K₆/(1-t)) ‖𝒫𝒜‖_max`** over a carrier: slot `0` gives `Σ_b K₀(a₁,b)(𝒫𝒜)_b` (row sums), every slot
`i ≥ 1` the constant column sum of the slot kernel times `(𝒫𝒜)_{a₁}` (the constancy is `ZeroModeGen_KerSums`, the modulus `hcol`).
Band: `B45_Psum_ThetaN_le`. -/
private theorem B45Gen_Psum_ThetaN_le {K₆ : ℝ} (hker : ZeroModeGen_KerSums C n)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {m : ℕ} (σ : Fin (m + 1) → Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ} {M : ℝ}
    (hA : ∀ b₁, ‖STPsum (d := d) A b₁‖ ≤ M) (a₁ : Zd d (sz.L n)) :
    ‖STPsum (d := d) (Step2Gen_ThetaN C n σ t A) a₁‖ ≤ ((m + 1 : ℕ) : ℝ) * (K₆ / (1 - t)) * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA a₁)
  unfold STPsum
  simp only [Step2Gen_ThetaN]
  rw [Finset.sum_comm]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin (m + 1), ‖∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁),
          ∑ b : Zd d (sz.L n), Step2Gen_thetaKer C n (σ i) (σ (finRotate (m + 1) i)) t (a i) b *
            A (Function.update a i b)‖
      ≤ ∑ _i : Fin (m + 1), K₆ / (1 - t) * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i = 0
        · subst hi
          rw [B45_slot_zero (d := d) (L := sz.L n)
            (fun x y => Step2Gen_thetaKer C n (σ 0) (σ (finRotate (m + 1) 0)) t x y) A a₁]
          refine (norm_sum_le _ _).trans ?_
          calc ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ 0) (σ (finRotate (m + 1) 0)) t a₁ b * STPsum (d := d) A b‖
              ≤ ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ 0) (σ (finRotate (m + 1) 0)) t a₁ b‖ * M :=
                Finset.sum_le_sum fun b _ => by
                  rw [norm_mul]
                  exact mul_le_mul_of_nonneg_left (hA b) (norm_nonneg _)
            _ = (∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n (σ 0) (σ (finRotate (m + 1) 0)) t a₁ b‖) * M :=
                (Finset.sum_mul _ _ _).symm
            _ ≤ K₆ / (1 - t) * M :=
                mul_le_mul_of_nonneg_right (hrow _ _ t ht0 ht1 a₁) hM
        · rw [B45_slot_succ (d := d) (L := sz.L n) hi
            (fun x y => Step2Gen_thetaKer C n (σ i) (σ (finRotate (m + 1) i)) t x y) A a₁]
          obtain ⟨κ, hκ⟩ := ZeroModeGen_thetaKer_colConst C n hker (σ i) (σ (finRotate (m + 1) i)) t
          have hκn : ‖κ‖ ≤ K₆ / (1 - t) := by
            have := hcol (σ i) (σ (finRotate (m + 1) i)) t ht0 ht1 0
            rwa [hκ 0] at this
          simp only [hκ]
          rw [← Finset.mul_sum]
          calc ‖κ * ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d (sz.L n) => a 0 = a₁), A a‖
              = ‖κ‖ * ‖STPsum (d := d) A a₁‖ := by rw [norm_mul]; rfl
            _ ≤ K₆ / (1 - t) * M := mul_le_mul hκn (hA a₁) (norm_nonneg _) ((norm_nonneg _).trans hκn)
    _ = ((m + 1 : ℕ) : ℝ) * (K₆ / (1 - t)) * M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **`‖ℬ₄‖` bound** over a carrier ((4.61) `A4`): `[𝒬_u, Θ] 𝒜 = Θ((𝒫𝒜) ϑ) - (𝒫Θ𝒜) ϑ` (`QopAlgebra_commutator_ThetaNg`), with
`‖Θ‖_{∞→∞} ≤ (m+1) K₆/(1-u)` and `‖𝒫Θ𝒜‖_max ≤ (m+1) K₆/(1-u) ‖𝒫𝒜‖_max`: if `‖𝒫𝒜‖_max ≤ Π` and `‖ϑ‖ ≤ ϑs` then
`‖ℬ₄‖ ≤ 2 (m+1) (K₆/(1-u)) Π ϑs`.  Band: `B45_B4_le`. -/
theorem B45_B4_leg {K₆ : ℝ} (hker : ZeroModeGen_KerSums C n)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {m : ℕ} (σ : Fin (m + 1) → Bool) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ)
    (A : (Fin (m + 1) → Zd d (sz.L n)) → ℂ) {Pi vs : ℝ}
    (hP : ∀ b₁, ‖STPsum (d := d) A b₁‖ ≤ Pi) (hϑ : ∀ b, ‖ϑ u b‖ ≤ vs) (a : Fin (m + 1) → Zd d (sz.L n)) :
    ‖STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u A) a - Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u A) a‖ ≤
      2 * ((m + 1 : ℕ) : ℝ) * (K₆ / (1 - u)) * (Pi * vs) := by
  have hPi : 0 ≤ Pi := (norm_nonneg _).trans (hP (a 0))
  have hvs : 0 ≤ vs := (norm_nonneg _).trans (hϑ a)
  rw [QopAlgebra_commutator_ThetaNg C n σ ϑ u A a]
  have hK0 : 0 ≤ K₆ / (1 - u) := by
    have h := hrow (σ 0) (σ (finRotate (m + 1) 0)) u hu0 hu1 (a 0)
    exact (Finset.sum_nonneg fun b _ => norm_nonneg _).trans h
  have h1 : ‖Step2Gen_ThetaN C n σ u (fun b => STPsum (d := d) A (b 0) * ϑ u b) a‖ ≤
      ((m + 1 : ℕ) : ℝ) * (K₆ / (1 - u)) * (Pi * vs) :=
    B45_norm_ThetaN_leg C n hrow σ hu0 hu1 (fun b => by
      rw [norm_mul]; exact mul_le_mul (hP _) (hϑ b) (norm_nonneg _) hPi) a
  have h2 : ‖STPsum (d := d) (Step2Gen_ThetaN C n σ u A) (a 0) * ϑ u a‖ ≤
      ((m + 1 : ℕ) : ℝ) * (K₆ / (1 - u)) * (Pi * vs) := by
    rw [norm_mul]
    have h3 := B45Gen_Psum_ThetaN_le C n hker hrow hcol σ hu0 hu1 hP (a 0)
    calc ‖STPsum (d := d) (Step2Gen_ThetaN C n σ u A) (a 0)‖ * ‖ϑ u a‖
        ≤ (((m + 1 : ℕ) : ℝ) * (K₆ / (1 - u)) * Pi) * vs := mul_le_mul h3 (hϑ a) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc _ ≤ ‖Step2Gen_ThetaN C n σ u (fun b => STPsum (d := d) A (b 0) * ϑ u b) a‖ +
        ‖STPsum (d := d) (Step2Gen_ThetaN C n σ u A) (a 0) * ϑ u a‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

end ThetaNorm

/-! ## 3. The scales, the deterministic core and its absorption -/

section Scales

variable {d : ℕ}

/-- The scale inputs of the exponent count over a carrier: `(W^d η)⁻¹ ℓ^{-d} ≤ 2Γ W^{-d}B_{u,0}` (`d ≥ 2`, `B45_scale`),
`η⁻¹ ≤ Γ N`, `N⁻¹ ≤ W^{-d}B_{u,0}`, `0 < η ≤ 1 - u`, with `Γ = κm⁻¹`, `η = C.eta n u = (1-u) Im m`, `κm ≤ Im m ≤ 1`.  Band:
`B45_scales` (`κm = √κ/2`, `Γ = 2/√κ`). -/
theorem B45_scalesg (hd : 2 ≤ d) (sz : Sizes d) (C : FlowFM sz) (n : ℕ) {u κm : ℝ} (hκm : 0 < κm)
    (hmn : κm ≤ (C.m n).im) (him1 : (C.m n).im ≤ 1) (heta : ∀ t : ℝ, C.eta n t = (1 - t) * (C.m n).im)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) {Γ : ℝ} (hΓ : Γ = κm⁻¹) :
    ((((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ≤ 2 * Γ * sz.Bctl n u) ∧
      (C.eta n u)⁻¹ ≤ Γ * ((sz.size n : ℕ) : ℝ) ∧ ((sz.size n : ℕ) : ℝ)⁻¹ ≤ sz.Bctl n u ∧
      0 < C.eta n u ∧ C.eta n u ≤ 1 - u := by
  have hv : 0 < 1 - u := by linarith
  have hμ0 : 0 < (C.m n).im := lt_of_lt_of_le hκm hmn
  have hη : 0 < C.eta n u := by rw [heta u]; exact mul_pos hv hμ0
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
      have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
    positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hNe]; positivity
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  refine ⟨?_, ?_, ?_, hη, ?_⟩
  · -- `(W^d η)⁻¹ ℓ^{-d} ≤ 2Γ B`
    have hsc := B45_scale (d := d) (L := sz.L n) hd (by have := sz.three_le_L n; omega) hg hu1
    have h1 : (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) =
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((C.m n).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹) := by
      rw [heta u]
      field_simp
    rw [h1]
    have h2 : ((C.m n).im)⁻¹ ≤ Γ := by
      rw [hΓ]
      exact inv_anti₀ hκm hmn
    unfold Sizes.Bctl
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((C.m n).im)⁻¹ * ((ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Γ * (2 * Bparam d (sz.L n) (sz.lam n) u 0) := by
          have hpos : 0 ≤ (ellT (sz.L n) (sz.lam n) u ^ d * (1 - u))⁻¹ := by
            have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := u) (by
              have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n))
            positivity
          gcongr
      _ = 2 * Γ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) u 0) := by ring
  · -- `η⁻¹ ≤ Γ N`
    have h1 : (1 - u) * κm ≤ C.eta n u := by
      rw [heta u]; exact mul_le_mul_of_nonneg_left hmn hv.le
    have h2 : (C.eta n u)⁻¹ ≤ ((1 - u) * κm)⁻¹ := inv_anti₀ (by positivity) h1
    have h3 : ((1 - u) * κm)⁻¹ = Γ * (1 - u)⁻¹ := by
      rw [hΓ, mul_inv]; ring
    have h4 : (1 - u)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
      have := inv_anti₀ (by positivity) hNu
      rwa [inv_inv] at this
    calc (C.eta n u)⁻¹ ≤ ((1 - u) * κm)⁻¹ := h2
      _ = Γ * (1 - u)⁻¹ := h3
      _ ≤ Γ * ((sz.size n : ℕ) : ℝ) := by gcongr
  · -- `N⁻¹ ≤ B`
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hv, hNe, mul_inv]
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ := by
      apply inv_anti₀ (by positivity)
      have : 1 - u ≤ 1 := by linarith
      calc ((sz.L n : ℕ) : ℝ) ^ d * (1 - u) ≤ ((sz.L n : ℕ) : ℝ) ^ d * 1 := by gcongr
        _ = _ := mul_one _
    have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    have key : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
            (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
      gcongr
      linarith
    exact key
  · rw [heta u]
    have := mul_le_mul_of_nonneg_left him1 hv.le
    linarith

end Scales

section Det

variable {d : ℕ}

/-- **The deterministic core of (4.30) `eq:Ward_typeP` and (4.59) `y27kasdfg`** at one `(n, u, ω)` over a carrier: from the bound `Ξ̂ ≤ ν X` on
the rank-`m+1` entries (`hY`), the far-entry bound `F` (`hF`) and the mollifier bounds (`hϑ`, `hϑ'`), for alternating `σ`
(`σ_last = ¬σ_0`), tensors of `m+2` indices: `|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ M (W^{-d}B_{u,0})^{m+2} X` and
`|ℬ₄| + |ℬ₅| ≤ η⁻¹ (2m+5) K₆ M (W^{-d}B_{u,0})^{m+2} X`, `M = 3·4^{dm} Γ Λ ν²`, `Γ = κm⁻¹`, `K₆ ≥ 1` the kernel constant.  The version with absorbed constants is `B45_det2g`. -/
theorem B45_detg (hd : 2 ≤ d) (sz : Sizes d) (C : FlowFM sz) (n : ℕ) {u κm K₆ : ℝ} (hκm : 0 < κm)
    (hmn : κm ≤ (C.m n).im) (him1 : (C.m n).im ≤ 1) (heta : ∀ t : ℝ, C.eta n t = (1 - t) * (C.m n).im)
    (hward : ZeroModeGen_WardCls sz C) (hker : ZeroModeGen_KerSums C n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (ω : sz.SeqΩ)
    {m : ℕ} {Γ ν X ωf Fv Λ : ℝ} (hΓ : Γ = κm⁻¹) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensorg C n u ω σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKtensorg C n u ω σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 2) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a, ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 2) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * ϑ u a‖ ≤
        (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) ∧
      ‖(STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (STLKtensorg C n u ω σ)) -
            Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (STLKtensorg C n u ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        (C.eta n u)⁻¹ * ((((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
          (sz.Bctl n u ^ (m + 2) * X)) := by
  obtain ⟨hKB, hηN, hBN, hη, hηle⟩ := B45_scalesg hd sz C n hκm hmn him1 heta hu0 hu1 hg hNu hΓ
  have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW1
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by rw [hNe]; positivity
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hBN
  have hℓ1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1
  have hℓ0 : 0 < ellT (sz.L n) (sz.lam n) u := by linarith
  -- the `𝒫`-bound, for every `a₁`
  set R : ℝ := ellT (sz.L n) (sz.lam n) u * ωf with hR
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  set Pi : ℝ := (((sz.W n : ℕ) : ℝ) ^ d * C.eta n u)⁻¹ *
    (((2 * R + 2) ^ d) ^ m * (ν * X * sz.Bctl n u ^ (m + 1)) +
      (((sz.L n : ℕ) : ℝ) ^ d) ^ m * Fv) with hPi
  have hP : ∀ b₁ : Zd d (sz.L n), ‖STPsum (d := d) (STLKtensorg C n u ω σ) b₁‖ ≤ Pi := fun b₁ =>
    B45_Psum_LK_leg C hward n hu0 hu1 hη ω σ hσ b₁ hR0 hFv0 hY (fun σ' a' _ hfar => hF σ' a' hfar)
  have hPi0 : 0 ≤ Pi := (norm_nonneg _).trans (hP (a 0))
  set vs : ℝ := Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) with hvs
  have hvs0 : 0 ≤ vs := by rw [hvs]; positivity
  -- the exponent count
  have hM : Pi * vs ≤ (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) :=
    B45_master_real (d := d) (m := m) (Wd := ((sz.W n : ℕ) : ℝ) ^ d) (Ld := ((sz.L n : ℕ) : ℝ) ^ d)
      (N := ((sz.size n : ℕ) : ℝ)) (η := C.eta n u) (B := sz.Bctl n u)
      (ℓ := ellT (sz.L n) (sz.lam n) u) (X := X) (ν := ν) (ω := ωf) (Γ := Γ) (Λ := Λ) (ϑb := vs)
      (Pi := Pi) (Fv := Fv) (by linarith) hLd1 hNe hℓ1 hν hX hB0 hη hωf hωd hΓ0 hΛ hWd1 hKB hηN hBN
      hFv hFv0 hνN hPi0 hvs0 (by rw [hPi]) (le_of_eq hvs)
  have hZ : 0 ≤ (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) := by
    have : 0 ≤ X := by linarith
    positivity
  have hv1 : 0 < 1 - u := by linarith
  -- (1)
  have h1 : ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * ϑ u a‖ ≤ Pi * vs := by
    rw [norm_mul]
    exact mul_le_mul (hP (a 0)) (hϑ a) (norm_nonneg _) hPi0
  refine ⟨h1.trans hM, ?_⟩
  -- (2) `ℬ₄`
  have hB4 := B45_B4_leg C n hker hrow hcol (m := m + 1) σ hu0 hu1 ϑ (STLKtensorg C n u ω σ) hP hϑ a
  -- `ℬ₅`
  have hB5 : ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
      (1 - u)⁻¹ * (Pi * vs) := by
    rw [norm_mul]
    calc ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0)‖ * ‖deriv (fun τ => ϑ τ a) u‖
        ≤ Pi * (Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) :=
          mul_le_mul (hP (a 0)) (hϑ' a) (norm_nonneg _) hPi0
      _ = (1 - u)⁻¹ * (Pi * vs) := by rw [hvs]; ring
  have hinv : (1 - u)⁻¹ ≤ (C.eta n u)⁻¹ := inv_anti₀ hη hηle
  have hPV0 : 0 ≤ Pi * vs := mul_nonneg hPi0 hvs0
  set M' := (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) * (sz.Bctl n u ^ (m + 2) * X) with hM'
  have hcast : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
  rw [hcast] at hB4
  have hi0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 hv1.le
  have hK0 : 0 ≤ K₆ := by linarith
  calc _ ≤ 2 * ((m : ℝ) + 2) * (K₆ / (1 - u)) * (Pi * vs) + (1 - u)⁻¹ * (Pi * vs) := add_le_add hB4 hB5
    _ ≤ (1 - u)⁻¹ * (((2 * (m : ℝ) + 5) * K₆) * (Pi * vs)) := by
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hkey : 2 * ((m : ℝ) + 2) * (K₆ / (1 - u)) * (Pi * vs) + (1 - u)⁻¹ * (Pi * vs) =
            (1 - u)⁻¹ * ((2 * ((m : ℝ) + 2) * K₆ + 1) * (Pi * vs)) := by
          rw [div_eq_mul_inv]; ring
        rw [hkey]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hPV0) hi0
        nlinarith
    _ ≤ (C.eta n u)⁻¹ * (((2 * (m : ℝ) + 5) * K₆) * M') := by
        have h2 : ((2 * (m : ℝ) + 5) * K₆) * (Pi * vs) ≤ ((2 * (m : ℝ) + 5) * K₆) * M' :=
          mul_le_mul_of_nonneg_left hM (by positivity)
        have h3 : 0 ≤ ((2 * (m : ℝ) + 5) * K₆) * (Pi * vs) := by positivity
        exact mul_le_mul hinv h2 h3 (inv_nonneg.2 hη.le)
    _ = _ := by rw [hM']; ring

/-- **`B45_detg` with the constants absorbed**: if `(2m+5) K₆ M ≤ N^τ` then `|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ N^τ (W^{-d}B_{u,0})^{m+2} X` and
`|ℬ₄| + |ℬ₅| ≤ N^τ η⁻¹ (W^{-d}B_{u,0})^{m+2} X`. -/
theorem B45_det2g (hd : 2 ≤ d) (sz : Sizes d) (C : FlowFM sz) (n : ℕ) {u κm K₆ : ℝ} (hκm : 0 < κm)
    (hmn : κm ≤ (C.m n).im) (him1 : (C.m n).im ≤ 1) (heta : ∀ t : ℝ, C.eta n t = (1 - t) * (C.m n).im)
    (hward : ZeroModeGen_WardCls sz C) (hker : ZeroModeGen_KerSums C n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hg : 0 < sz.lam n)
    (hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) (ω : sz.SeqΩ)
    {m : ℕ} {Γ ν X ωf Fv Λ τ : ℝ} (hΓ : Γ = κm⁻¹) (hν : 1 ≤ ν) (hX : 1 ≤ X)
    (hωf : 1 ≤ ωf) (hωd : ωf ^ (d * m) ≤ ν) (hνN : ν ≤ ((sz.size n : ℕ) : ℝ))
    (hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹) (hFv0 : 0 ≤ Fv) (hΛ : 0 ≤ Λ)
    (hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    (hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensorg C n u ω σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1))
    (hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖STLKtensorg C n u ω σ' a'‖ ≤ Fv)
    (ϑ : ℝ → (Fin (m + 2) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ a, ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (hϑ' : ∀ a, ‖deriv (fun τ => ϑ τ a) u‖ ≤
      Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)))
    (σ : Fin (m + 2) → Bool) (hσ : σ (Fin.last (m + 1)) = !σ 0) (a : Fin (m + 2) → Zd d (sz.L n)) :
    ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * ϑ u a‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) ∧
      ‖(STQop (d := d) ϑ u (Step2Gen_ThetaN C n σ u (STLKtensorg C n u ω σ)) -
            Step2Gen_ThetaN C n σ u (STQop (d := d) ϑ u (STLKtensorg C n u ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensorg C n u ω σ) (a 0) * deriv (fun τ => ϑ τ a) u‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((C.eta n u)⁻¹ * sz.Bctl n u ^ (m + 2) * X) := by
  obtain ⟨h1, h2⟩ := B45_detg hd sz C n hκm hmn him1 heta hward hker hK₆ hrow hcol hu0 hu1 hg hNu ω hΓ hν hX hωf hωd hνN
    hFv hFv0 hΛ hY hF ϑ hϑ hϑ' σ hσ a
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    rw [hNe]; have := one_le_pow₀ (n := d) hL1; positivity
  have hsc := B45_scalesg hd sz C n hκm hmn him1 heta hu0 hu1 hg hNu hΓ
  have hB0 : 0 < sz.Bctl n u := lt_of_lt_of_le (inv_pos.2 hNpos) hsc.2.2.1
  have hη : 0 < C.eta n u := hsc.2.2.2.1
  have hZ : 0 ≤ sz.Bctl n u ^ (m + 2) * X := by
    have : 0 ≤ X := by linarith
    positivity
  have hM1 : 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 ≤ ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) := by
    have hΓ0 : 0 ≤ Γ := by rw [hΓ]; positivity
    have h0 : 0 ≤ 3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2 := by positivity
    have : (1 : ℝ) ≤ (2 * (m : ℝ) + 5) * K₆ := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith
    nlinarith
  constructor
  · refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (hM1.trans hMΛ) hZ
  · refine h2.trans ?_
    have h3 : (((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) * (sz.Bctl n u ^ (m + 2) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X) :=
      mul_le_mul_of_nonneg_right hMΛ hZ
    calc (C.eta n u)⁻¹ * ((((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2)) *
          (sz.Bctl n u ^ (m + 2) * X))
        ≤ (C.eta n u)⁻¹ * (((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n u ^ (m + 2) * X)) :=
          mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hη.le)
      _ = _ := by ring

end Det

set_option maxHeartbeats 400000 in
/-! ## 4. End of the generic layer -/

end RBM.BA
