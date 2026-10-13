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
# `(eq:Ward_typeP)` and `(y27kasdfg)` over the flow carrier (BA-U row U2, ticket T2480, U2b)

Additive generic form of `Induction/B45.lean` (not edited): the two estimates `STWardTypePgL`, `STB45gL`
(`Chain/Step34Gen.lean:284, 295`) over a carrier `C : FlowFM sz` and a law `μ`, and the ingredient pins `STWardTypePPingL`,
`STB45PingL` (`Chain/Step34Gen.lean:419, 425`).

* **The class `B45Gen_Facts`** (target 7, `T2480_B45Facts`): the carrier facts that replace the band objects of `B45`: the last-label
  Ward step (`ZeroModeGen_WardCls`, one Ward text), the Ward pair of T7a (`DecayGen_WardPair`), and the row sums and column sums of
  `Step2Gen_thetaKer` (in place of `B45_row_thetaKer`, `QopAlgebra_col_sum_thetaKer`, `‖μ‖ = 1`).  Two fields are added to the pinned
  text, each with a named band discharge (`T2480.md` target 7: "binding up to fields added or dropped ... with a named band
  discharge"; see the report, (d) 1): `Im m ≤ 1` (the band `norm_mE`; it gives `η_u ≤ 1 - u`, hence `(1-u)⁻¹ ≤ η_u⁻¹` in `ℬ₅`)
  and `ZeroModeGen_KerSums` (merged, U1s1; the band `zeroModeGen_kerSums_band`; it makes the column sums of `thetaKer` constant in
  the column, which the slots `i ≥ 1` of `𝒫 Θ 𝒜` need).  `band`: `b45Gen_facts_band`, `C₆ = 1`.
* **Target 8 (a).**  `stWardTypePgL_of`, `stB45gL_of`: the far entries are T7a's `stDecayLoopUgL_of_step2` (from `STGdecayWgL`,
  `STKcalDecaygL`, `DecayGen_WardPair`, `DecayGen_Spec`), the commutator is `QopAlgebra_commutator_ThetaNg`, the mollifier is read at
  `sz.lam` (size level).  The condition `N⁻¹ ≤ 1 - t` that the band takes from `STFlow` (`v3_premises_of_stFlow`) is a hypothesis
  of the two theorems and, in the pins, a consequence of `(con_st_ind)` (`B45Gen_invN_of_conStInd`).
* **Target 8 (b).**  Public generic successors of the band helpers that other rows read: `B45_ward_fing`, `B45_Psum_LK_leg`,
  `B45_norm_kappag`, `B45_norm_ThetaN_leg`, `B45_B4_leg`, `B45_scalesg`, `B45_detg`, `B45_det2g`.
* **Target 9.**  `stWardTypePPingL_of`, `stB45PingL_of`: the regime `R` is an argument (the proofs read no regime, so the pins hold at
  every `R`, in particular the band regime `STCaseI`); band re-derivations `stWardTypePPin_gen_band`, `stB45Pin_gen_band` (`d = 3`).
* Private helpers of `B45` that mention no band object are reused by `open private`; the rest is restated under the stem `B45Gen_`.
  `Chain.KDecayGen` is imported by the layout of the ticket; no declaration of it is read here.
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

/-! ## 1. Target 7: the class `B45Gen_Facts` -/

/-- **Target 7, class `B45Gen_Facts`** (`T2480_B45Facts` with two named fields added): for every `κ > 0` one `C₆ > 0` such that, along
every flow of the family, the carrier has the last-label Ward step (`ZeroModeGen_WardCls`), the Ward pair of T7a
(`DecayGen_WardPair`), `Im m ≤ 1` (band: `norm_mE`), constant row and column sums of the generator (`ZeroModeGen_KerSums`; band:
`zeroModeGen_kerSums_band`), and, for every charge pair and `0 ≤ t < 1`, row sums and column-sum moduli of `Step2Gen_thetaKer` at most
`C₆/(1 - t)`.  `STKcalDecaygL` is not a field: it stays an explicit premise of the pins. -/
def B45Gen_Facts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ZeroModeGen_WardCls sz (mk sz z) ∧ DecayGen_WardPair (mk sz z) ∧ (∀ n : ℕ, ((mk sz z).m n).im ≤ 1) ∧
        (∀ n : ℕ, ZeroModeGen_KerSums (mk sz z) n) ∧
        ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
          (∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧
          ∀ b : Zd d (sz.L n), ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)

section Band

variable {d : ℕ} (sz : Sizes d)

/-- `Im z_n > 0` along an `STFlow`. -/
private theorem B45Gen_flow_im_pos {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (h.2 n).2.1

/-- **Band discharge of `B45Gen_Facts`** at `(STFlow, bandFM ∘ STflowE)`, `C₆ = 1`: `zeroModeGen_wardCls_band`, `DecayGen_bandWardPair`,
`norm_mE`, `zeroModeGen_kerSums_band`, and for the sums `Step2Kern_thetaKer_band` with `B45_row_thetaKer` (row sums) and
`QopAlgebra_col_sum_thetaKer` (column sums `μ(1 - tμ)⁻¹`, `‖μ‖ = 1`). -/
theorem b45Gen_facts_band (d : ℕ) :
    B45Gen_Facts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) := by
  intro κ hκ
  refine ⟨1, one_pos, ?_⟩
  intro sz ε 𝔠 𝔡 z hflow
  have him : ∀ n, 0 < (z n).im := B45Gen_flow_im_pos sz hflow
  have hE : ∀ n, |STflowE z n| < 2 := fun n => abs_lemE_lt_two (him n)
  refine ⟨zeroModeGen_wardCls_band sz (STflowE z) hE, DecayGen_bandWardPair sz (STflowE z), fun n => ?_,
    fun n => zeroModeGen_kerSums_band sz (STflowE z) n, fun n σ σ' t ht0 ht1 => ?_⟩
  · have := Complex.im_le_norm (mE (STflowE z n))
    rwa [norm_mE (hE n).le] at this
  · have hμ : ‖mSigma (STflowE z n) σ * mSigma (STflowE z n) σ'‖ = 1 := by
      rw [norm_mul, norm_mSigma (hE n).le, norm_mSigma (hE n).le, one_mul]
    have hker := Step2Kern_thetaKer_band sz (STflowE z) n σ σ' t
    have h1t : (1 - t)⁻¹ = 1 / (1 - t) := one_div (1 - t) ▸ rfl
    refine ⟨fun a => ?_, fun b => ?_⟩
    · simp only [bandFM, hker] at *
      rw [← h1t]
      exact B45_row_thetaKer (sz.lam n) (sz.three_le_L n) hμ ht0 ht1 a
    · simp only [bandFM, hker] at *
      rw [QopAlgebra_col_sum_thetaKer (sz.lam n) (sz.three_le_L n)
        (by rw [norm_mul, hμ, mul_one, Complex.norm_of_nonneg ht0]; exact ht1) b, ← h1t]
      exact B45_norm_colsum hμ ht0 ht1

end Band

/-! ## 2. Target 8 (b): Ward at the last label, the window split, the kernel norms -/

section Ward

variable {d : ℕ} {sz : Sizes d} (C : FlowFM sz)

/-- **Ward's identity at the last index** for `𝓛 - 𝒦` over a carrier (`lem_WI_K`, `(WI_calL)`), alternating `σ` (`σ_last = ¬σ_0`):
`Σ_x (𝓛-𝒦)^{(m+2)}_{σ,(a',x)} = (2iW^d η)⁻¹ ((𝓛-𝒦)^{(m+1)}_{σ⁺,a'} - (𝓛-𝒦)^{(m+1)}_{σ⁻,a'})`, `η = C.eta n u`.  Band: `B45_ward_fin`
(`Induction/B45.lean:200`); the hypothesis is the one Ward text `ZeroModeGen_WardCls` (UN-C3). -/
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

/-- `‖(2 i W^d η)⁻¹‖ = (2 W^d η)⁻¹` for `η > 0` (band `B45_norm_kappa`, `Induction/B45.lean:400`; here `η` is a free positive real). -/
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

/-- **`(jywiiwsoks)`, deterministic window step over a carrier.**  For alternating `σ`, Ward's identity at the last label reduces
`𝒫(𝓛-𝒦)^{(m+2)}` to `(2iW^dη)⁻¹` times the difference of two `𝒫` of `(𝓛-𝒦)^{(m+1)}`, each split into the window `diam_∞ < R` and its
complement.  Band: `B45_Psum_LK_le` (`Induction/B45.lean:414`); `η = C.eta n u > 0` is a hypothesis. -/
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
(`hrow`).  Band: `B45_norm_ThetaN_le` (`Induction/B45.lean:671`; `K₆ = 1`, `‖μ‖ = 1`). -/
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
`i ≥ 1` the constant column sum of `K_i` times `(𝒫𝒜)_{a₁}` (the constancy is `ZeroModeGen_KerSums`, the modulus `hcol`).
Band: `B45_Psum_ThetaN_le` (`Induction/B45.lean:794`). -/
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

/-- **`‖ℬ₄‖` bound** over a carrier (`(A4)`, `3_5:1700`): `[𝒬_u, Θ] 𝒜 = Θ((𝒫𝒜) ϑ) - (𝒫Θ𝒜) ϑ` (`QopAlgebra_commutator_ThetaNg`), with
`‖Θ‖_{∞→∞} ≤ (m+1) K₆/(1-u)` and `‖𝒫Θ𝒜‖_max ≤ (m+1) K₆/(1-u) ‖𝒫𝒜‖_max`: if `‖𝒫𝒜‖_max ≤ Π` and `‖ϑ‖ ≤ ϑs` then
`‖ℬ₄‖ ≤ 2 (m+1) (K₆/(1-u)) Π ϑs`.  Band: `B45_B4_le` (`Induction/B45.lean:862`). -/
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

/-! ## 3. Target 8 (b): the scales, the deterministic core and its absorption -/

section Scales

variable {d : ℕ}

/-- The scale inputs of the exponent count over a carrier: `(W^d η)⁻¹ ℓ^{-d} ≤ 2Γ W^{-d}B_{u,0}` (`d ≥ 2`, `B45_scale`),
`η⁻¹ ≤ Γ N`, `N⁻¹ ≤ W^{-d}B_{u,0}`, `0 < η ≤ 1 - u`, with `Γ = κm⁻¹`, `η = C.eta n u = (1-u) Im m`, `κm ≤ Im m ≤ 1`.  Band:
`B45_scales` (`Induction/B45.lean:2246`; `κm = √κ/2`, `Γ = 2/√κ`). -/
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

/-- **The deterministic core of `(eq:Ward_typeP)` and `(y27kasdfg)`** at one `(n, u, ω)` over a carrier: from the bound `Ξ̂ ≤ ν X` on
the rank-`m+1` entries (`hY`), the far-entry bound `F` (`hF`) and the mollifier bounds (`hϑ`, `hϑ'`), for alternating `σ`
(`σ_last = ¬σ_0`), tensors of `m+2` indices: `|𝒫(𝓛-𝒦)_{a₀} ϑ_a| ≤ M (W^{-d}B_{u,0})^{m+2} X` and
`|ℬ₄| + |ℬ₅| ≤ η⁻¹ (2m+5) K₆ M (W^{-d}B_{u,0})^{m+2} X`, `M = 3·4^{dm} Γ Λ ν²`, `Γ = κm⁻¹`, `K₆ ≥ 1` the kernel constant.  Band:
`B45_det` (`Induction/B45.lean:2346`). -/
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
`|ℬ₄| + |ℬ₅| ≤ N^τ η⁻¹ (W^{-d}B_{u,0})^{m+2} X`.  Band: `B45_det2` (`Induction/B45.lean:2577`). -/
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

/-! ## 4. The assembly: the near entries by the induction bound, the far entries by `lem_decayLoop` -/

section Assemble

variable {d : ℕ}

/-- `Ξ̂^{𝓛-𝒦}_{u,k} ≤ Y` bounds every entry: `|(𝓛-𝒦)^{(k)}_{σ,a}| ≤ Y (W^{-d}B_{u,0})^k` (band `B45_norm_le_XiLK`,
`Induction/B45.lean:2505`). -/
private theorem B45Gen_norm_le_XiLK {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) {k : ℕ}
    (hB : 0 < sz.Bctl n u) {Y : ℝ} (h : STXiLKg C n u k ω ≤ Y) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    ‖C.L n u σ a ω - C.K n u σ a‖ ≤ Y * sz.Bctl n u ^ k := by
  have hBk : 0 < sz.Bctl n u ^ k := pow_pos hB k
  unfold STXiLKg STmaxLKg at h
  have h1 : ‖C.L n u σ a ω - C.K n u σ a‖ ≤
      Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
        (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖) :=
    Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖)
      (Finset.mem_univ (σ, a))
  set S := Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
        (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖C.L n u p.1 p.2 ω - C.K n u p.1 p.2‖) with hS
  have h2 : S / sz.Bctl n u ^ k ≤ Y - 1 := by linarith
  have h3 : S ≤ (Y - 1) * sz.Bctl n u ^ k := by
    rw [div_le_iff₀ hBk] at h2; exact h2
  have h4 : (Y - 1) * sz.Bctl n u ^ k ≤ Y * sz.Bctl n u ^ k := by nlinarith
  exact (h1.trans h3).trans h4

/-- **The union bound of the assembly** at a law `μ` (band `B45_prec_assemble`, `Induction/B45.lean:2456`): if `ξ₁ ≺ ζ₁` and the far family
`ξ₂ ≺ W^{-D'}` (for every `τ_f, D'`) and, for every `τ > 0`, there are `τ₁, τ_f, D'` such that eventually the deterministic implication
"`ξ₁ ≤ N^{τ₁} ζ₁` and `ξ₂ ≤ N^{τ₁} W^{-D'}` everywhere ⟹ `ξ₃ ≤ N^τ ζ₃` everywhere" holds, then `ξ₃ ≺ ζ₃`. -/
private theorem B45Gen_prec_assemble (sz : Sizes d) (μ : Measure sz.SeqΩ) (hN : sz.SizeTendsto)
    {U₁ U₂ U₃ : ℕ → Type*} {ξ₁ ζ₁ : ∀ n, U₁ n → sz.SeqΩ → ℝ}
    {ξ₂ : ℝ → ∀ n, U₂ n → sz.SeqΩ → ℝ} {ξ₃ ζ₃ : ∀ n, U₃ n → sz.SeqΩ → ℝ}
    (h₁ : PrecL sz μ ξ₁ ζ₁)
    (h₂ : ∀ τf > (0 : ℝ), ∀ D' > (0 : ℝ), PrecL sz μ (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')))
    (hdet : ∀ τ > (0 : ℝ), ∃ τ₁ > (0 : ℝ), ∃ τf > (0 : ℝ), ∃ D' > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ ω : sz.SeqΩ,
        (∀ p, ξ₁ n p ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ζ₁ n p ω) →
        (∀ q, ξ₂ τf n q ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-D')) →
        ∀ r, ξ₃ n r ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₃ n r ω) :
    PrecL sz μ ξ₃ ζ₃ := by
  intro τ hτ D hD
  obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := hdet τ hτ
  filter_upwards [hev, h₁ τ₁ hτ₁ (D + 1) (by linarith), h₂ τf hτf D' hD' τ₁ hτ₁ (D + 1) (by linarith),
    (Sizes.tendsto_size sz hN).eventually (eventually_two_mul_rpow_le D)] with n hev1 h1 h2 h3
  have hp : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : badSetAt sz.size ξ₃ ζ₃ τ n ⊆
      badSetAt sz.size ξ₁ ζ₁ τ₁ n ∪ badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n := by
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno hω
    obtain ⟨r, hr⟩ := hω
    exact absurd (hev1 ω hno.1 hno.2 r) (not_le.2 hr)
  calc μ (badSetAt sz.size ξ₃ ζ₃ τ n)
      ≤ μ (badSetAt sz.size ξ₁ ζ₁ τ₁ n ∪
          badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n) := measure_mono hsub
    _ ≤ μ (badSetAt sz.size ξ₁ ζ₁ τ₁ n) +
          μ (badSetAt sz.size (ξ₂ τf) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')) τ₁ n) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ((sz.size n : ℕ) : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp]; ring_nf
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h3

/-- The far-entry observable `(|𝓛| + |𝓛-𝒦|)^{(k)}_{u,σ,a} · 1(ℓ_u W^{τ_f} ≤ diam_∞ a)` (band `B45_farXi`, `Induction/B45.lean:2677`);
it is the function of `STDecayLoopUgL`. -/
private def B45Gen_farXi {sz : Sizes d} (C : FlowFM sz) (s t : ℕ → ℝ) (k : ℕ) (τf : ℝ) (n : ℕ)
    (p : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))) (ω : sz.SeqΩ) : ℝ :=
  (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
    (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τf ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0)

end Assemble

/-! ## 5. The deterministic-eventual core of the pins -/

section Key

variable {d : ℕ}

set_option maxHeartbeats 400000 in
-- the pointwise chain of the far/near split elaborates a long `have` list: 200000 is not enough
/-- The deterministic-eventual core of `B45Gen_pins` (band `B45_key`, `Induction/B45.lean:2687`).  `Γ = κm⁻¹`; `K₆ ≥ 1` is the kernel constant;
the condition `N⁻¹ ≤ 1 - t_n` (eventually) replaces `v3_premises_of_stFlow`. -/
private theorem B45Gen_key (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) {κm 𝔠 𝔡 K₆ : ℝ} (hκm : 0 < κm)
    (hmn : ∀ n, κm ≤ (C.m n).im) (him1 : ∀ n, (C.m n).im ≤ 1) (heta : ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im)
    (hA : sz.Admissible 𝔠 𝔡) (hward : ZeroModeGen_WardCls sz C) (hker : ∀ n, ZeroModeGen_KerSums C n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n)
    {m : ℕ} (Cϑ c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ n, STMollifierProps (d := d) (sz.lam n) Cϑ c (ϑ n))
    (X : ℕ → ℝ → ℝ) (hX1 : ∀ n u, 1 ≤ X n u) :
    ∀ τ > (0 : ℝ), ∃ τ₁ > (0 : ℝ), ∃ τf > (0 : ℝ), ∃ D' > (0 : ℝ),
      ∀ᶠ n : ℕ in atTop, ∀ ω : sz.SeqΩ,
        (∀ u : TimeIcc s t n, STXiLKg C n (u : ℝ) (m + 1) ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * X n (u : ℝ)) →
        (∀ q : TimeIcc s t n × (Fin (m + 1) → Bool) × (Fin (m + 1) → Zd d (sz.L n)),
          B45Gen_farXi C s t (m + 1) τf n q ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-D')) →
        ∀ (u : TimeIcc s t n) (σ : Fin (m + 1 + 1) → Bool), STAlternating σ →
          ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖STPsum (d := d) (STLKtensorg C n (u : ℝ) ω σ) (a 0) * ϑ n (u : ℝ) a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (u : ℝ)) ^ (m + 1 + 1) * X n (u : ℝ)) ∧
          ‖(STQop (d := d) (ϑ n) (u : ℝ) (Step2Gen_ThetaN C n σ (u : ℝ) (STLKtensorg C n (u : ℝ) ω σ)) -
            Step2Gen_ThetaN C n σ (u : ℝ) (STQop (d := d) (ϑ n) (u : ℝ) (STLKtensorg C n (u : ℝ) ω σ))) a‖ +
          ‖STPsum (d := d) (STLKtensorg C n (u : ℝ) ω σ) (a 0) * deriv (fun τ => ϑ n τ a) (u : ℝ)‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ τ * ((C.eta n (u : ℝ))⁻¹ *
                (sz.Bctl n (u : ℝ)) ^ (m + 1 + 1) * X n (u : ℝ)) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have hdm : 1 ≤ d * (m + 1) := Nat.mul_pos (by omega) (by omega)
  intro τ hτ
  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : ℝ, τ₁ = min (τ / 6) (1 / 4) := ⟨_, rfl⟩
  have hτ₁ : 0 < τ₁ := by rw [hτ₁def]; exact lt_min (by linarith) (by norm_num)
  have hτ₁4 : τ₁ ≤ 1 / 4 := by rw [hτ₁def]; exact min_le_right _ _
  have hτ₁6 : τ₁ ≤ τ / 6 := by rw [hτ₁def]; exact min_le_left _ _
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine ⟨τ₁, hτ₁, τ₁ / ((m : ℝ) + 1), by positivity, ((2 * m + 4 : ℕ) : ℝ) / 𝔠, by positivity, ?_⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : ℝ, Γ = κm⁻¹ := ⟨_, rfl⟩
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ, Kc = Real.exp (|c| * (((m + 1 : ℕ) : ℝ) * d / 2)) := ⟨_, rfl⟩
  obtain ⟨K₂, hK₂def⟩ : ∃ K₂ : ℝ, K₂ = Cϑ * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) := ⟨_, rfl⟩
  obtain ⟨K₃, hK₃def⟩ : ∃ K₃ : ℝ, K₃ = ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * K₂) := ⟨_, rfl⟩
  have hK3ev : ∀ᶠ n : ℕ in atTop, K₃ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hN).eventually_ge_atTop K₃
  filter_upwards [hNt, hB, hWO, hK3ev, hN.eventually_ge_atTop 1] with n hNtn hbw hwo hK3 hN1'
  intro ω hyp1 hyp2 u σ hσalt a
  -- basic facts at the index `n`
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1r : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hL1r : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWdN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hNe]; exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1r)
  have hlpos : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hwo.1
  have hg1 : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d :=
    (Real.one_le_rpow hW1r (by linarith : (0 : ℝ) ≤ 2 * 𝔡)).trans
      (Sizes.lam_sq_mul_pow_ge sz n hwo.1)
  have hgN : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.lam n ^ 2 := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
    calc (((sz.size n : ℕ) : ℝ))⁻¹ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_anti₀ hW0 hWdN
      _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) := by gcongr
      _ = sz.lam n ^ 2 := by field_simp
  have hC : 0 ≤ Cϑ := B45_C_nonneg hL3 hlpos (hϑ n)
  have hu0 : 0 ≤ (u : ℝ) := (hs n).trans u.2.1
  have hut : (u : ℝ) ≤ t n := u.2.2
  have hu1 : (u : ℝ) < 1 := hut.trans_lt (ht1 n)
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - (u : ℝ) := hNtn.trans (by linarith)
  have hsc := B45_scalesg (by omega : 2 ≤ d) sz C n hκm (hmn n) (him1 n) (heta n) hu0 hu1 hlpos hNu hΓdef
  have hB0 : 0 < sz.Bctl n (u : ℝ) := lt_of_lt_of_le (inv_pos.2 hN0) hsc.2.2.1
  -- the constants
  have hdm0 : (0 : ℝ) < ((d * (m + 1) : ℕ) : ℝ) := by exact_mod_cast hdm
  have hKc0 : 0 < Kc := by rw [hKcdef]; exact Real.exp_pos _
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℝ, Λ = Cϑ * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) +
      2 * max 0 (-Real.log (sz.lam n))) := ⟨_, rfl⟩
  have hmax0 : 0 ≤ max 0 (-Real.log (sz.lam n)) := le_max_left _ _
  have hΛ0 : 0 ≤ Λ := by rw [hΛdef]; positivity
  have hlog := B45_log_le hlpos hN1' hgN hτ₁
  have hNτ₁ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.one_le_rpow hN1' hτ₁.le
  have hΛle : Λ ≤ K₂ * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
    rw [hΛdef, hK₂def]
    have h1 : Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 2 * max 0 (-Real.log (sz.lam n)) ≤
        (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by
      have h2 : 0 ≤ Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) := by positivity
      have h3 : (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ)) ≤
          (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ)) * ((sz.size n : ℕ) : ℝ) ^ τ₁ :=
        le_mul_of_one_le_right h2 hNτ₁
      have h4 : ((sz.size n : ℕ) : ℝ) ^ τ₁ / τ₁ = 1 / τ₁ * ((sz.size n : ℕ) : ℝ) ^ τ₁ := by ring
      nlinarith
    calc Cϑ * (Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 2 * max 0 (-Real.log (sz.lam n)))
        ≤ Cϑ * ((Kc + 2 / ((d * (m + 1) : ℕ) : ℝ) + 1 / τ₁) * ((sz.size n : ℕ) : ℝ) ^ τ₁) :=
          mul_le_mul_of_nonneg_left h1 hC
      _ = _ := by ring
  have hK₂0 : 0 ≤ K₂ := by rw [hK₂def]; positivity
  have hΓ0 : 0 ≤ Γ := by rw [hΓdef]; positivity
  have hK60 : 0 ≤ K₆ := by linarith
  have hK₃0 : 0 ≤ K₃ := by rw [hK₃def]; positivity
  -- `(2m+5) K₆ M ≤ N^τ`
  have hMΛ : ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    have hν2 : (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have h3 : ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) =
        ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h4 : ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
    have h5 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
        ((sz.size n : ℕ) : ℝ) ^ τ := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hν0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁) := (Real.rpow_pos_of_pos hN0 _).le
    calc ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * Λ * (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2)
        ≤ ((2 * (m : ℝ) + 5) * K₆) * (3 * 4 ^ (d * m) * Γ * (K₂ * ((sz.size n : ℕ) : ℝ) ^ τ₁) *
            (((sz.size n : ℕ) : ℝ) ^ τ₁) ^ 2) := by
          gcongr
      _ = K₃ * (((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.size n : ℕ) : ℝ) ^ (2 * τ₁)) := by
          rw [hK₃def, hν2]; ring
      _ = K₃ * ((sz.size n : ℕ) : ℝ) ^ (3 * τ₁) := by rw [h3]
      _ ≤ K₃ * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := mul_le_mul_of_nonneg_left h4 hK₃0
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
          mul_le_mul_of_nonneg_right hK3 (Real.rpow_pos_of_pos hN0 _).le
      _ = _ := h5
  have hσ := B45_alt_last hσalt
  have hτf0 : 0 < τ₁ / ((m : ℝ) + 1) := by positivity
  have hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖STLKtensorg C n (u : ℝ) ω σ' a'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * X n (u : ℝ) * sz.Bctl n (u : ℝ) ^ (m + 1) :=
    fun σ' a' => B45Gen_norm_le_XiLK C n (u : ℝ) ω hB0 (hyp1 u) σ' a'
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) (u : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (τ₁ / ((m : ℝ) + 1)) ≤
        (STdiamInf a' : ℝ) → ‖STLKtensorg C n (u : ℝ) ω σ' a'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.W n : ℕ) : ℝ) ^ (-(((2 * m + 4 : ℕ) : ℝ) / 𝔠)) := by
    intro σ' a' hfar'
    have h := hyp2 (u, σ', a')
    simp only [B45Gen_farXi, hfar', ite_true, mul_one] at h
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h
  have hKc1 : 1 ≤ Kc := by
    rw [hKcdef]; exact Real.one_le_exp (by positivity)
  have hϑ1 : ∀ a, ‖ϑ n (u : ℝ) a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    have := B45_vth_sup hL3 hlpos (hϑ n) hdm hu0 hu1 a
    rw [hΛdef, hKcdef]; exact this
  have hCΛ : Cϑ ≤ Λ := by
    rw [hΛdef]
    exact le_mul_of_one_le_right hC (by
      have : 0 ≤ 2 / ((d * (m + 1) : ℕ) : ℝ) := by positivity
      linarith)
  have hϑ2 : ∀ a, ‖deriv (fun τ => ϑ n τ a) (u : ℝ)‖ ≤
      Λ * (1 - (u : ℝ))⁻¹ * (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine ((hϑ n).2.2.2 (u : ℝ) hu0 hu1 a).trans ?_
    have hv : 0 < 1 - (u : ℝ) := by linarith
    have hQ0 : 0 ≤ (((ellT (sz.L n) (sz.lam n) (u : ℝ) ^ d)⁻¹) ^ (m + 1)) := by
      have := ellT_pos (L := sz.L n) (g := sz.lam n) (t := (u : ℝ)) hL1r
      positivity
    gcongr
  exact B45_det2g (by omega : 2 ≤ d) sz C n hκm (hmn n) (him1 n) (heta n) hward (hker n) hK₆ (hrow n) (hcol n)
    hu0 hu1 hlpos hNu ω hΓdef hNτ₁ (hX1 n (u : ℝ))
    (Real.one_le_rpow hW1r hτf0.le)
    (B45_window_pow_le hW1r hN1' hWdN hτf0.le m (by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm1]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      nlinarith))
    (by calc ((sz.size n : ℕ) : ℝ) ^ τ₁ ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
        _ = _ := Real.rpow_one _)
    (mul_le_mul_of_nonneg_left (B45_W_pow_neg_le h𝔠 hN1' hbw (2 * m + 4)) (by positivity))
    (by positivity) hΛ0 hMΛ hY hF (ϑ n) hϑ1 hϑ2 σ hσ a

end Key

/-! ## 6. Target 8 (a): `(eq:Ward_typeP)` and `(y27kasdfg)` over a carrier -/

section Pins

variable {d : ℕ}

/-- `(eq:Ward_typeP)` and `(y27kasdfg)` for tensors of `m + 2` indices (the pins' `m ≥ 1`, `m ↦ m+1`), both conclusions from the same
hypotheses (band `B45_pins`, `Induction/B45.lean:2872`): from the far entries (`STDecayLoopUgL`), the induction bound `Ξ̂ ≺ X` and the
mollifier `STMollifierProps` (any real constants), with the carrier facts. -/
private theorem B45Gen_pins (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {κm 𝔠 𝔡 K₆ : ℝ} (hκm : 0 < κm)
    (hmn : ∀ n, κm ≤ (C.m n).im) (him1 : ∀ n, (C.m n).im ≤ 1) (heta : ∀ (n : ℕ) (t : ℝ), C.eta n t = (1 - t) * (C.m n).im)
    (hA : sz.Admissible 𝔠 𝔡) (hward : ZeroModeGen_WardCls sz C) (hker : ∀ n, ZeroModeGen_KerSums C n) (hK₆ : 1 ≤ K₆)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ K₆ / (1 - t))
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hU : STDecayLoopUgL C μ s t)
    {m : ℕ} (Cϑ c : ℝ) (ϑ : ∀ n : ℕ, ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ)
    (hϑ : ∀ n, STMollifierProps (d := d) (sz.lam n) Cϑ c (ϑ n))
    (X : ℕ → ℝ → ℝ) (hX1 : ∀ n u, 1 ≤ X n u)
    (hXprec : PrecL sz μ (U := fun n => TimeIcc s t n)
      (fun n u ω => STXiLKg C n (u : ℝ) (m + 1) ω) (fun n u _ => X n (u : ℝ))) :
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin (m + 1 + 1) → Bool // STAlternating σ} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)))
      (fun n q ω => ‖STPsum (d := d) (STLKtensorg C n (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) * ϑ n (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (m + 1 + 1) * X n (q.1 : ℝ)) ∧
    PrecL sz μ (U := fun n => TimeIcc s t n × {σ : Fin (m + 1 + 1) → Bool // STAlternating σ} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)))
      (fun n q ω =>
        ‖(STQop (d := d) (ϑ n) (q.1 : ℝ)
            (Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ) (STLKtensorg C n (q.1 : ℝ) ω q.2.1.1)) -
          Step2Gen_ThetaN C n q.2.1.1 (q.1 : ℝ)
            (STQop (d := d) (ϑ n) (q.1 : ℝ) (STLKtensorg C n (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
        ‖STPsum (d := d) (STLKtensorg C n (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
            deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => (C.eta n (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ (m + 1 + 1) * X n (q.1 : ℝ)) := by
  obtain ⟨h𝔠, h𝔡, hN, hB, hWO⟩ := id hA
  have key := B45Gen_key hd sz C hκm hmn him1 heta hA hward hker hK₆ hrow hcol hs ht1 hNt Cϑ c ϑ hϑ X hX1
  refine ⟨?_, ?_⟩
  · refine B45Gen_prec_assemble sz μ hN hXprec (ξ₂ := fun τf => B45Gen_farXi C s t (m + 1) τf)
      (fun τf hτf D' hD' => hU (m + 1) (by omega) τf D' hτf hD') (fun τ hτ => ?_)
    obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := key τ hτ
    refine ⟨τ₁, hτ₁, τf, hτf, D', hD', ?_⟩
    filter_upwards [hev] with n hn ω h1 h2 r
    exact (hn ω h1 h2 r.1 r.2.1.1 r.2.1.2 r.2.2).1
  · refine B45Gen_prec_assemble sz μ hN hXprec (ξ₂ := fun τf => B45Gen_farXi C s t (m + 1) τf)
      (fun τf hτf D' hD' => hU (m + 1) (by omega) τf D' hτf hD') (fun τ hτ => ?_)
    obtain ⟨τ₁, hτ₁, τf, hτf, D', hD', hev⟩ := key τ hτ
    refine ⟨τ₁, hτ₁, τf, hτf, D', hD', ?_⟩
    filter_upwards [hev] with n hn ω h1 h2 r
    exact (hn ω h1 h2 r.1 r.2.1.1 r.2.1.2 r.2.2).2

/-- **`(eq:Ward_typeP)`** (`3_5:1264`, `jywiiwsoks` `3_5:1271`) over a carrier, case (i) (`N⁻¹ ≤ 1 - t_n` eventually), uniformly in
`u ∈ [s,t]`.  The far entries are `stDecayLoopUgL_of_step2` (from the uniform Step 2 decay `STGdecayWgL`, the far decay of `𝒦`
`STKcalDecaygL`, the Ward pair and `DecayGen_Spec`); the carrier facts are those of `B45Gen_Facts` (`C₆` the kernel constant).  The
Step 2 decay and the far decay of `𝒦` are other gates' outputs and stay hypotheses.  Band: `stWardTypePPin_holds` (`Induction/B45.lean:2935`)
through `bandFM_STWardTypeP`. -/
theorem stWardTypePgL_of (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {κm 𝔠 𝔡 C₆ Cd : ℝ}
    (hspec : DecayGen_Spec C κm) (him1 : ∀ n, (C.m n).im ≤ 1) (hA : sz.Admissible 𝔠 𝔡)
    (hward : ZeroModeGen_WardCls sz C) (hpair : DecayGen_WardPair C) (hker : ∀ n, ZeroModeGen_KerSums C n)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t))
    (hKcal : STKcalDecaygL C) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hD : STGdecayWgL C μ s t Cd) :
    STWardTypePgL C μ s t := by
  obtain ⟨hκm, hmn, heta⟩ := hspec
  have hU := stDecayLoopUgL_of_step2 hd sz C μ κm 𝔠 𝔡 s t Cd ⟨hκm, hmn, heta⟩ hA hs ht1 hpair hKcal hD
  intro m Cϑ c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45Gen_pins hd sz C μ hκm hmn him1 heta hA hward hker (le_max_right C₆ 1)
    (fun n σ σ' t h0 h1 a => (hrow n σ σ' t h0 h1 a).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)))
    (fun n σ σ' t h0 h1 b => (hcol n σ σ' t h0 h1 b).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)))
    hs ht1 hNt hU Cϑ c ϑ hϑ X hX1 hXprec).1

/-- **`(y27kasdfg)`** (`3_5:1692`) over a carrier, case (i): the same hypotheses as `stWardTypePgL_of`.  Band: `stB45Pin_holds`
(`Induction/B45.lean:2943`) through `bandFM_STB45`. -/
theorem stB45gL_of (hd : 3 ≤ d) (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {κm 𝔠 𝔡 C₆ Cd : ℝ}
    (hspec : DecayGen_Spec C κm) (him1 : ∀ n, (C.m n).im ≤ 1) (hA : sz.Admissible 𝔠 𝔡)
    (hward : ZeroModeGen_WardCls sz C) (hpair : DecayGen_WardPair C) (hker : ∀ n, ZeroModeGen_KerSums C n)
    (hrow : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
      ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t))
    (hcol : ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
      ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer C n σ σ' t a b‖ ≤ C₆ / (1 - t))
    (hKcal : STKcalDecaygL C) {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1)
    (hNt : ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) (hD : STGdecayWgL C μ s t Cd) :
    STB45gL C μ s t := by
  obtain ⟨hκm, hmn, heta⟩ := hspec
  have hU := stDecayLoopUgL_of_step2 hd sz C μ κm 𝔠 𝔡 s t Cd ⟨hκm, hmn, heta⟩ hA hs ht1 hpair hKcal hD
  intro m Cϑ c hm ϑ hϑ X hX1 hXprec
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact (B45Gen_pins hd sz C μ hκm hmn him1 heta hA hward hker (le_max_right C₆ 1)
    (fun n σ σ' t h0 h1 a => (hrow n σ σ' t h0 h1 a).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)))
    (fun n σ σ' t h0 h1 b => (hcol n σ σ' t h0 h1 b).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)))
    hs ht1 hNt hU Cϑ c ϑ hϑ X hX1 hXprec).2

end Pins

/-! ## 7. Target 9: the pins `stWardTypePPingL_of`, `stB45PingL_of` -/

section PinsOf

variable {d : ℕ}

/-- `(N (1 - t))⁻¹ ≤ W^{-d} B_{t,0}` for `t < 1`: the zero-mode term of `(eq_B_param)`. -/
private theorem B45Gen_Bctl_ge (sz : Sizes d) (n : ℕ) {t : ℝ} (ht : t < 1) :
    ((((sz.size n : ℕ) : ℝ)) * (1 - t))⁻¹ ≤ sz.Bctl n t := by
  have hv : 0 < 1 - t := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n; exact_mod_cast (by omega : 0 < sz.L n)
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hv]
  have e1 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [e1, inv_one, mul_one, mul_add]
  have t1 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.lam n ^ 2 + (1 - t))⁻¹ := by
    have : 0 < sz.lam n ^ 2 + (1 - t) := by positivity
    positivity
  have t2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - t))⁻¹ =
      ((((sz.size n : ℕ) : ℝ)) * (1 - t))⁻¹ := by
    rw [hN, ← mul_inv, mul_assoc]
  rw [t2]
  linarith

/-- `(con_st_ind)` with `𝔠_d > 0` gives `N⁻¹ ≤ 1 - t_n` eventually: `(N(1-t))⁻¹ ≤ B_t`, `B_t^{𝔠_d} ≤ (1-t)/(1-s) < 1`, so `B_t < 1`. -/
private theorem B45Gen_invN_of_conStInd (sz : Sizes d) {𝔠d : ℝ} (h𝔠d : 0 < 𝔠d) {s t : ℕ → ℝ}
    (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1) (hcon : sz.STConStInd 𝔠d s t) :
    ∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n := by
  filter_upwards [hcon] with n hn
  obtain ⟨h1, h2⟩ := hn
  have hv : 0 < 1 - t n := by linarith [ht1 n]
  have hB : sz.Bctl n (t n) < 1 := by
    by_contra hge
    push Not at hge
    have := Real.one_le_rpow hge h𝔠d.le
    linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hlt : ((((sz.size n : ℕ) : ℝ)) * (1 - t n))⁻¹ < 1 := lt_of_le_of_lt (B45Gen_Bctl_ge sz n (ht1 n)) hB
  have hgt : 1 < ((sz.size n : ℕ) : ℝ) * (1 - t n) := by
    by_contra hle
    push Not at hle
    have := (one_le_inv₀ (by positivity)).2 hle
    linarith
  have : ((sz.size n : ℕ) : ℝ)⁻¹ * 1 < ((sz.size n : ℕ) : ℝ)⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - t n)) :=
    mul_lt_mul_of_pos_left hgt (inv_pos.2 hN0)
  rw [← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul, mul_one] at this
  exact this.le

/-- The part of the proof of the two pins that does not depend on the conclusion: the data of the flow and of the facts at `(κ, sz, z)`. -/
private theorem B45Gen_pin_data (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hflow : Step5CasesGen_FlowFacts d Flow mk T0) (hfacts : B45Gen_Facts d Flow mk)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z))
    (Concl : ∀ (sz : Sizes d) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hmain : ∀ (sz : Sizes d) (z : ℕ → ℂ) (κ ε 𝔠 𝔡 Cd κm C₆ : ℝ), 3 ≤ d → 0 < κ →
      DecayGen_Spec (mk sz z) κm → (∀ n, ((mk sz z).m n).im ≤ 1) → sz.Admissible 𝔠 𝔡 →
      ZeroModeGen_WardCls sz (mk sz z) → DecayGen_WardPair (mk sz z) → (∀ n, ZeroModeGen_KerSums (mk sz z) n) →
      (∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ a : Zd d (sz.L n),
        ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) →
      (∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 → ∀ b : Zd d (sz.L n),
        ‖∑ a : Zd d (sz.L n), Step2Gen_thetaKer (mk sz z) n σ σ' t a b‖ ≤ C₆ / (1 - t)) →
      STKcalDecaygL (mk sz z) → ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
      (∀ᶠ n in atTop, (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - t n) → STGdecayWgL (mk sz z) (law sz) s t Cd →
      Concl sz z s t)
    (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) :
    STIngRgL d R law Flow mk T0 Concl := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hFlow s t hs0 hst ht _hR _hKb _hKw _hLK hcon hStep2
  obtain ⟨κm, hκm, H⟩ := hflow κ hκ
  obtain ⟨C₆, hC₆, G⟩ := hfacts κ hκ
  obtain ⟨hA, hT0, hmn, heta⟩ := H sz ε 𝔠 𝔡 z hFlow
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := G sz ε 𝔠 𝔡 z hFlow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  exact hmain sz z κ ε 𝔠 𝔡 Cd κm C₆ hd hκ ⟨hκm, hmn, heta⟩ him1 hA hward hpair hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2)
    (hKcal sz κ ε 𝔠 𝔡 z hκ hFlow) s t hs0 ht1
    (B45Gen_invN_of_conStInd sz (by norm_num) hst ht1 hcon) hStep2.2.2

/-- **Target 9, the pin `stWardTypePPingL_of`** (`T2480_WardTypePPinOf`): `(eq:Ward_typeP)` along a carrier family with the flow
facts and the facts of `B45Gen_Facts`; the far decay of `𝒦` (`STKcalDecaygL`) along the family stays an explicit premise.  The proof reads
neither the regime nor `STKbound`, `STKward`, `STLK` (1a (ix)), so the result holds for every regime `R`, in particular `STCaseI`.  Band:
`stWardTypePPin_holds` (`Induction/B45.lean:2935`) through `bandFM_STWardTypePPin`. -/
theorem stWardTypePPingL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hlaw : ∀ sz : Sizes d, IsProbabilityMeasure (law sz)) (hflow : Step5CasesGen_FlowFacts d Flow mk T0)
    (hfacts : B45Gen_Facts d Flow mk)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) :
    STWardTypePPingL d R law Flow mk T0 :=
  B45Gen_pin_data d law Flow mk T0 hflow hfacts hKcal (fun sz z s t => STWardTypePgL (mk sz z) (law sz) s t)
    (fun sz z κ ε 𝔠 𝔡 Cd κm C₆ hd hκ hspec him1 hA hward hpair hker hrow hcol hKc s t hs ht1 hNt hD =>
      stWardTypePgL_of hd sz (mk sz z) (law sz) hspec him1 hA hward hpair hker hrow hcol hKc hs ht1 hNt hD) R

/-- **Target 9, the pin `stB45PingL_of`** (`T2480_B45PinOf`): `(y27kasdfg)` along a carrier family, under the hypotheses of
`stWardTypePPingL_of` (for every regime `R`).  Band: `stB45Pin_holds` (`Induction/B45.lean:2943`) through `bandFM_STB45Pin`. -/
theorem stB45PingL_of (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (law : ∀ sz : Sizes d, Measure sz.SeqΩ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hlaw : ∀ sz : Sizes d, IsProbabilityMeasure (law sz)) (hflow : Step5CasesGen_FlowFacts d Flow mk T0)
    (hfacts : B45Gen_Facts d Flow mk)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → STKcalDecaygL (mk sz z)) :
    STB45PingL d R law Flow mk T0 :=
  B45Gen_pin_data d law Flow mk T0 hflow hfacts hKcal (fun sz z s t => STB45gL (mk sz z) (law sz) s t)
    (fun sz z κ ε 𝔠 𝔡 Cd κm C₆ hd hκ hspec him1 hA hward hpair hker hrow hcol hKc s t hs ht1 hNt hD =>
      stB45gL_of hd sz (mk sz z) (law sz) hspec him1 hA hward hpair hker hrow hcol hKc hs ht1 hNt hD) R

end PinsOf

/-! ## 8. Band re-derivations of the pins -/

section BandRederive

/-- The regime-free band flow facts and the far decay of `𝒦` along `STFlow` (`d = 3`): the premise of the pins at the band family. -/
private theorem B45Gen_band_kcal (sz : Sizes 3) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : STFlow sz κ ε 𝔠 𝔡 z) :
    STKcalDecaygL (bandFM sz (STflowE z)) :=
  bandFM_STKcalDecay (by norm_num) sz hκ hflow.1 fun n =>
    (abs_lemE_le (B45Gen_flow_im_pos sz hflow n)).trans (hflow.2 n).1

/-- **Band `STWardTypePPin` re-derived** (`d = 3`) from `stWardTypePPingL_of` through `bandFM_STWardTypePPin`. -/
theorem stWardTypePPin_gen_band : STWardTypePPin 3 :=
  (bandFM_STWardTypePPin 3).2 <|
    stWardTypePPingL_of 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz => inferInstance)
      (step5CasesGen_flowFacts_band 3) (b45Gen_facts_band 3) B45Gen_band_kcal

/-- **Band `STB45Pin` re-derived** (`d = 3`) from `stB45PingL_of` through `bandFM_STB45Pin`. -/
theorem stB45Pin_gen_band : STB45Pin 3 :=
  (bandFM_STB45Pin 3).2 <|
    stB45PingL_of 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz => inferInstance)
      (step5CasesGen_flowFacts_band 3) (b45Gen_facts_band 3) B45Gen_band_kcal

end BandRederive

end RBM.BA

/-! ## 9. Compiled nonempty instances (`d = 3`)

Data: the merged size sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), the flow
`flow_z0 : STFlow sz0 (1/10) (1/10) (1/6) (1/10) z0`, the window `s ≡ 0`, `t ≡ 1/16` (`1/16 ≤ lemT z0`, `N⁻¹ ≤ 15/16` eventually), the carrier
`bandFM sz0 (STflowE z0)`, the law `seqP sz0`, `m = 1` (tensors of two indices), the merged mollifier `QopAlgebra_mollifier`, `X ≡ 1`.  The class
`B45Gen_Facts` is applied to `(sz0, z0)` with all its facts; `stWardTypePgL_of`, `stB45gL_of` keep the Step 2 output `STGdecayWgL` (another gate's pin) as a
hypothesis, and the induction bound `Ξ̂ ≺ X`; every deterministic premise (`3 ≤ d`, admissibility, `DecayGen_Spec`, the carrier facts, the far decay of `𝒦`
`STKcalDecaygL` from `bandFM_STKcalDecay`, the window) is discharged.  The pins are applied at the whole band family with no hypothesis left. -/

namespace RBM.BA.B45GenInst

open Filter RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.BA

private theorem z0_abs_le'' (n : ℕ) : |STflowE z0 n| ≤ 2 - 1 / 10 :=
  (abs_lemE_le (z0_im_pos n)).trans (z0_locDomain n).1

private theorem inst_hN : ∀ᶠ n in atTop, (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - tInst n := by
  filter_upwards [(tendsto_natCast_atTop_iff.2 (Sizes.tendsto_size sz0 sz0_tendsto)).eventually_ge_atTop (2 : ℝ)] with n hn
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 2) hn
  norm_num [tInst] at this ⊢; linarith

/-- The index set of the instances is nonempty at every size index: the window point `0 ∈ [0, 1/16]`, the alternating charges `(+,-)`, labels `0`. -/
example (n : ℕ) :
    Nonempty (TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} × (Fin (1 + 1) → Zd 3 (sz0.L n))) :=
  ⟨⟨0, by simp [sInst, tInst]⟩, ⟨![true, false], fun i => by fin_cases i <;> decide⟩, fun _ => 0⟩

/-- **Target 7 (`B45Gen_Facts`) at the band flow `(sz0, z0)`**: all five facts with the kernel constant `C₆ > 0`, none stochastic. -/
example : ∃ C₆ : ℝ, 0 < C₆ ∧
    (ZeroModeGen_WardCls sz0 (bandFM sz0 (STflowE z0)) ∧ DecayGen_WardPair (bandFM sz0 (STflowE z0)) ∧
      (∀ n : ℕ, ((bandFM sz0 (STflowE z0)).m n).im ≤ 1) ∧ (∀ n : ℕ, ZeroModeGen_KerSums (bandFM sz0 (STflowE z0)) n) ∧
      ∀ (n : ℕ) (σ σ' : Bool) (t : ℝ), 0 ≤ t → t < 1 →
        (∀ a : Zd 3 (sz0.L n), ∑ b : Zd 3 (sz0.L n), ‖Step2Gen_thetaKer (bandFM sz0 (STflowE z0)) n σ σ' t a b‖ ≤ C₆ / (1 - t)) ∧
        ∀ b : Zd 3 (sz0.L n), ‖∑ a : Zd 3 (sz0.L n), Step2Gen_thetaKer (bandFM sz0 (STflowE z0)) n σ σ' t a b‖ ≤ C₆ / (1 - t)) := by
  obtain ⟨C₆, hC₆, H⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  exact ⟨C₆, hC₆, H sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0⟩

/-- **Target 8 (a), `stWardTypePgL_of` at `(sz0, z0, [0, 1/16])`**: the band `STWardTypeP` from the generic result; the Step 2 decay `STGdecayWgL`
is the hypothesis `hD`. -/
example (Cd : ℝ) (hD : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd) :
    STWardTypeP sz0 (STflowE z0) sInst tInst := by
  obtain ⟨C₆, hC₆, H⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := H sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0
  exact (bandFM_STWardTypeP sz0 _ _ _).2 <| stWardTypePgL_of (by norm_num) sz0 (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)
    (DecayGen_bandSpec sz0 (E := STflowE z0) (κ := 1 / 10) (by norm_num) z0_abs_le'') him1 sz0_admissible hward hpair hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible z0_abs_le'') sz0_hs0
    (fun n => by simp only [tInst]; norm_num) inst_hN hD

/-- **Target 8 (a), `stB45gL_of` at `(sz0, z0, [0, 1/16])`**: the band `STB45`; the Step 2 decay is the hypothesis `hD`. -/
example (Cd : ℝ) (hD : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd) :
    STB45 sz0 (STflowE z0) sInst tInst := by
  obtain ⟨C₆, hC₆, H⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := H sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0
  exact (bandFM_STB45 sz0 _ _ _).2 <| stB45gL_of (by norm_num) sz0 (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)
    (DecayGen_bandSpec sz0 (E := STflowE z0) (κ := 1 / 10) (by norm_num) z0_abs_le'') him1 sz0_admissible hward hpair hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible z0_abs_le'') sz0_hs0
    (fun n => by simp only [tInst]; norm_num) inst_hN hD

/-- **`stWardTypePgL_of` applied at `m = 1`** (two indices) on `(sz0, z0, [0, 1/16])` with the merged mollifier and `X ≡ 1`: the conclusion is a
`PrecL` over the nonempty index set above. -/
example (Cd : ℝ) (hD : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd)
    (hX : PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n)
      (fun n u ω => STXiLKg (bandFM sz0 (STflowE z0)) n (u : ℝ) 1 ω) (fun n _ _ => 1)) :
    PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
        (Fin (1 + 1) → Zd 3 (sz0.L n)))
      (fun n q ω => ‖STPsum (d := 3) (STLKtensorg (bandFM sz0 (STflowE z0)) n (q.1 : ℝ) ω q.2.1.1)
          (q.2.2 0) * QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) (q.1 : ℝ) q.2.2‖)
      (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1) := by
  obtain ⟨C₆, hC₆, H⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := H sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0
  exact stWardTypePgL_of (by norm_num) sz0 (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)
    (DecayGen_bandSpec sz0 (E := STflowE z0) (κ := 1 / 10) (by norm_num) z0_abs_le'') him1 sz0_admissible hward hpair hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible z0_abs_le'') sz0_hs0
    (fun n => by simp only [tInst]; norm_num) inst_hN hD 1 _ _ le_rfl
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (RBM.Gauss.B45Inst.B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **`stB45gL_of` applied at `m = 1`** (two indices) on `(sz0, z0, [0, 1/16])` with the merged mollifier and `X ≡ 1`. -/
example (Cd : ℝ) (hD : STGdecayWgL (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0) sInst tInst Cd)
    (hX : PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n)
      (fun n u ω => STXiLKg (bandFM sz0 (STflowE z0)) n (u : ℝ) 1 ω) (fun n _ _ => 1)) :
    PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
        (Fin (1 + 1) → Zd 3 (sz0.L n)))
      (fun n q ω =>
        ‖(STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n)) (q.1 : ℝ)
            (Step2Gen_ThetaN (bandFM sz0 (STflowE z0)) n q.2.1.1 (q.1 : ℝ)
              (STLKtensorg (bandFM sz0 (STflowE z0)) n (q.1 : ℝ) ω q.2.1.1)) -
          Step2Gen_ThetaN (bandFM sz0 (STflowE z0)) n q.2.1.1 (q.1 : ℝ)
            (STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n)) (q.1 : ℝ)
              (STLKtensorg (bandFM sz0 (STflowE z0)) n (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
        ‖STPsum (d := 3) (STLKtensorg (bandFM sz0 (STflowE z0)) n (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
            deriv (fun τ => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) τ q.2.2) (q.1 : ℝ)‖)
      (fun n q _ => ((bandFM sz0 (STflowE z0)).eta n (q.1 : ℝ))⁻¹ * (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1) := by
  obtain ⟨C₆, hC₆, H⟩ := b45Gen_facts_band 3 (1 / 10) (by norm_num)
  obtain ⟨hward, hpair, him1, hker, hsums⟩ := H sz0 (1 / 10) (1 / 6) (1 / 10) z0 flow_z0
  exact stB45gL_of (by norm_num) sz0 (bandFM sz0 (STflowE z0)) (Sizes.seqP sz0)
    (DecayGen_bandSpec sz0 (E := STflowE z0) (κ := 1 / 10) (by norm_num) z0_abs_le'') him1 sz0_admissible hward hpair hker
    (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).1) (fun n σ σ' t h0 h1 => (hsums n σ σ' t h0 h1).2)
    (bandFM_STKcalDecay (by norm_num) sz0 (by norm_num) sz0_admissible z0_abs_le'') sz0_hs0
    (fun n => by simp only [tInst]; norm_num) inst_hN hD 1 _ _ le_rfl
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (RBM.Gauss.B45Inst.B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **Target 9 (`stWardTypePPingL_of`) at the band family, `d = 3`, regime `STCaseI`**: a theorem, nonempty by construction (no hypothesis left). -/
example : STWardTypePPingL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stWardTypePPingL_of 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (b45Gen_facts_band 3) B45Gen_band_kcal

/-- The same pin at the regime `STAny` (the proof reads no regime). -/
example : STWardTypePPingL 3 STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stWardTypePPingL_of 3 STAny (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (b45Gen_facts_band 3) B45Gen_band_kcal

/-- **Target 9 (`stB45PingL_of`) at the band family, `d = 3`, regime `STCaseI`**. -/
example : STB45PingL 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) :=
  stB45PingL_of 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz => inferInstance)
    (step5CasesGen_flowFacts_band 3) (b45Gen_facts_band 3) B45Gen_band_kcal

/-- **`stWardTypePPin_gen_band` applied at `(sz0, z0, 0, 1/16)`, `m = 1`** (the band instance of `STWardTypePPin`, `Induction/B45.lean:2979`,
from the generic pin). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKbound sz0 (STflowE z0) → STKward sz0 (STflowE z0) → STLK sz0 (STflowE z0) sInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n)
          (fun n u ω => STXiLK sz0 n (STflowE z0 n) (u : ℝ) 1 ω) (fun n _ _ => 1) →
        Prec sz0 (U := fun n => TimeIcc sInst tInst n × {σ : Fin (1 + 1) → Bool // STAlternating σ} ×
            (Fin (1 + 1) → Zd 3 (sz0.L n)))
          (fun n q ω => ‖STPsum (d := 3) (STLKtensor sz0 n (STflowE z0 n) (q.1 : ℝ) ω q.2.1.1)
              (q.2.2 0) * QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n) (q.1 : ℝ) q.2.2‖)
          (fun n q _ => (sz0.Bctl n (q.1 : ℝ)) ^ (1 + 1) * 1)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := inst_WardTypeP stWardTypePPin_gen_band Cd hCd
  refine ⟨𝔠d, h0, h1, fun hK hKw hLK h2 hX => ?_⟩
  exact H hK hKw hLK h2 1 _ _ le_rfl (fun n => QopAlgebra_mollifier 3 (sz0.L n) 1 (sz0.lam n))
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 1 (sz0.three_le_L n) (RBM.Gauss.B45Inst.B45_sz0_lam_pos n))
    (fun _ _ => 1) (fun _ _ => le_rfl) hX

/-- **Target 8 (b): `B45_ward_fing` at the band carrier is the band `B45_ward_fin`** (`Induction/B45.lean:200`), and `B45_scalesg` is `B45_scales`
(`κm = √κ/2`, `Γ = 2/√κ`, `κ = 1/10`). -/
example (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ω : sz0.SeqΩ) {m : ℕ} (σ : Fin (m + 2) → Bool)
    (hσ : σ (Fin.last (m + 1)) = !σ 0) (a' : Fin (m + 1) → Zd 3 (sz0.L n)) :
    ∑ x : Zd 3 (sz0.L n), STLKtensor sz0 n (STflowE z0 n) u ω σ (Fin.snoc (α := fun _ => Zd 3 (sz0.L n)) a' x) =
      (2 * Complex.I * ((sz0.W n : ℕ) : ℂ) ^ 3 * (etaT (STflowE z0 n) u : ℂ))⁻¹ *
        (STLKtensor sz0 n (STflowE z0 n) u ω (B45_sgnCons true σ) a' -
          STLKtensor sz0 n (STflowE z0 n) u ω (B45_sgnCons false σ) a') :=
  B45_ward_fing (bandFM sz0 (STflowE z0)) (zeroModeGen_wardCls_band sz0 (STflowE z0)
    (fun n => abs_lemE_lt_two (z0_im_pos n))) n hu0 hu1 ω σ hσ a'

example (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (hNu : (((sz0.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u) :
    ((((sz0.W n : ℕ) : ℝ) ^ 3 * etaT (STflowE z0 n) u)⁻¹ * ((ellT (sz0.L n) (sz0.lam n) u ^ 3)⁻¹) ≤
        2 * (Real.sqrt (1 / 10) / 2)⁻¹ * sz0.Bctl n u) ∧
      (etaT (STflowE z0 n) u)⁻¹ ≤ (Real.sqrt (1 / 10) / 2)⁻¹ * ((sz0.size n : ℕ) : ℝ) ∧
      ((sz0.size n : ℕ) : ℝ)⁻¹ ≤ sz0.Bctl n u ∧ 0 < etaT (STflowE z0 n) u ∧ etaT (STflowE z0 n) u ≤ 1 - u := by
  have hE := z0_abs_le'' n
  have hmn := DecayGen_bandSpec sz0 (E := STflowE z0) (κ := 1 / 10) (by norm_num) z0_abs_le''
  have him1 : ((bandFM sz0 (STflowE z0)).m n).im ≤ 1 := by
    have := Complex.im_le_norm (mE (STflowE z0 n))
    rwa [norm_mE (by linarith [abs_nonneg (STflowE z0 n)])] at this
  exact B45_scalesg (by norm_num) sz0 (bandFM sz0 (STflowE z0)) n (u := u) (by have := hmn.1; exact this) (hmn.2.1 n) him1
    (hmn.2.2 n) hu0 hu1 (RBM.Gauss.B45Inst.B45_sz0_lam_pos n) hNu rfl

end RBM.BA.B45GenInst
