/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5CasesGen
import RBM3D.Chain.Step5KerGen
import RBM3D.Chain.CltGen
import RBM3D.Induction.IniTermII
import RBM3D.Evolution.CltResolvent

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The initial terms of Step 5, case (ii), over the carrier (T2484, U4s2a)

Additive generic form of `Induction/IniTermII.lean` (not edited) over a carrier tuple `(law, Flow, mk, T0)` of
`Chain/Step5Gen.lean`, on the one kernel `Step2Gen_UN` and the one propagator `STThg` (U-C4: no kernel, no propagator and no
bridge is defined here).  Paper: arXiv:2507.20274, case (ii) is `(zYU2)`, `3_5:2268-2281`; `(eq:decompU)` is `3_5:1983`;
`(prop:ThfadC0)`, `(prop:ThfadC_short)` are Proposition 5.  No new mathematics.

* **Target 1.** The class `IniTermGen_KerFacts d Flow mk gK`: the semigroup law (T4s1), the decay and row sums of `thetaKer` at
  the kernel coupling `gK` (`Step5KerGen_ThDecay`, one text), the one comparison hypothesis R1 (UBA-C1, DECISIONS §273 (1)),
  the swap `Θ^{(σ,!σ)} = Θ^{(!σ,σ)}` (E1), and, at each index with `0 < gK ≤ 𝔡⁻¹`, the column sum, the zero mode and the
  short range of `STThg` at `gK`; its band result `iniTermGen_kerFacts_band` (`gK = sz.lam`, `A = 1`).
* **Targets 2-3.** The deterministic cores `iniTermIIGen_core` (`σ₁ ≠ σ₂`, `Q^{(1)}`) and `iniTermIIGen_core_same`
  (`σ₁ = σ₂`) and the `Prec` lift `iniTermIIGen_concl`.
* **Target 4.** The pin `stIniTermIIgL_of`, and the band re-derivation `iniTermIIGen_band_holds` of `stIniTermII_holds`.

Coupling (UBA-C1): the decay, zero mode and short range are read at `gK`; every size-level quantity (`tailT`, `Bctl`, the windows)
at `sz.lam`; the one comparison R1 `0 ≤ gK lam ∧ gK² ≤ lam² ∧ lam² ≤ A gK²` crosses in `IniTermIIGen_stageA` (the profile) and
`IniTermIIGen_zero_bound` (the `Θ̊` bound), and the per-index guard is `IniTermIIGen_cmp_pos`.

Ported from `Induction/IniTermII.lean` of this project (commit `78f4cc14`): the private lattice and tail lemmas of §1, §2, §5,
§6 (`bil_same`), §9, §10 by `open private`; §3 `stageA` (`:327`), §4 `ZA` (`:369`), §6 `Kf` and `bil` (`:668-723`), §7
`Ugen_rep` (`:907`), `zms_rep` (`:963`), §8-§9 cores (`:1051`, `:1378`), §10 `lift` (`:1567`) and §11 `concl` (`:1664`),
`holds` (`:1718`) regenerated for the carrier.  The d = 1 and d = 2 projects are not used.
-/

open private iniTermII_PD iniTermII_PI iniTermII_PD_nonneg iniTermII_zdistInf_sub_comm iniTermII_zdistInf_le_L iniTermII_sum_PD
  iniTermII_sum_PI iniTermII_conv_PD iniTermII_tailT_mono iniTermII_S2 iniTermII_S3 iniTermII_S3F iniTermII_sum_fin2
  iniTermII_bil_same iniTermII_lam_le iniTermII_rho_le iniTermII_N_le_W iniTermII_prem_eq iniTermII_prof_ge
  iniTermII_of_subset iniTermII_arith iniTermII_Theta_shift from RBM3D.Induction.IniTermII
open private Step5KerGen_cmp_pos from RBM3D.Chain.Step5KerGen

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Evol

/-! ## 1. Target 1: the kernel facts of the initial terms -/

/-- **Target 1, the class `IniTermGen_KerFacts d Flow mk gK`** (D1; `T2484_KerFacts` of the 1a-audit, with the swap E1): the kernel
facts of a flow family that the initial terms read beyond `Step5CasesGen_FlowFacts`.  The semigroup law (T4s1), the decay and row
sums of `thetaKer` at the kernel coupling `gK` (`Step5KerGen_ThDecay`, one text), the one comparison R1 (UBA-C1), the swap E1
`Θ^{(σ,!σ)} = Θ^{(!σ,σ)}` (the slot `1` of `𝒰^{(2)}` carries `(σ₁,σ₀)`, `STfFarg` and `STThPropsg` read `(σ₀,σ₁)`), and, at each
index with `0 < gK ≤ 𝔡⁻¹`, three entrywise facts of `STThg` at `gK`: the mixed column sum `(1 - t)⁻¹` (band `IniTermII:963`), the
mixed zero mode `(prop:ThfadC0)` (band `prop8ZeroMode_holds`, `IniTermII:1051`), the same-charge short range
`(prop:ThfadC_short)` (band `prop5Short_holds`, `IniTermII:1378`).  Band `gK = sz.lam`, `A = 1`; BA `gK` is the stage-P coupling `g₀`,
`A = (κ+1)/κ` (U4-BA (a)). -/
def IniTermGen_KerFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      (∀ n : ℕ, Step2Gen_USemigroup (mk sz z) n) ∧
      Step5KerGen_ThDecay (mk sz z) (gK sz z) 𝔡⁻¹ C₆ ∧
      (∀ n : ℕ, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK sz z n ^ 2) ∧
      (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool,
        STThg (mk sz z) n σ (!σ) t = STThg (mk sz z) n (!σ) σ t) ∧
      ∀ n : ℕ, 0 < gK sz z n → gK sz z n ≤ 𝔡⁻¹ → ∀ t : ℝ, 0 ≤ t → t < 1 →
        (∀ (σ : Bool) (b : Zd d (sz.L n)),
          ∑ a : Zd d (sz.L n), STThg (mk sz z) n σ (!σ) t a b = (((1 - t : ℝ) : ℂ))⁻¹) ∧
        (∀ (σ : Bool) (a b : Zd d (sz.L n)),
          ‖STThg (mk sz z) n σ (!σ) t a b - (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (((1 - t : ℝ) : ℂ))⁻¹‖ ≤
            C₈ * (gK sz z n ^ 2 + |1 - t|)⁻¹ * ((((zdistD d (sz.L n) (b - a) : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹) ∧
        ∀ (σ : Bool) (a b : Zd d (sz.L n)),
          ‖STThg (mk sz z) n σ σ t a b‖ ≤
            Cs * ((if a = b then (1 : ℝ) else 0) +
              gK sz z n ^ 2 * Real.exp (-(c₀ * ((zdistD d (sz.L n) (b - a) : ℕ) : ℝ))))

/-- `|E_n| ≤ 2 - κ` along a band flow (`Im z_n > 0` from `N^{-1+ε} ≤ Im z_n`). -/
private theorem IniTermIIGen_flow_E {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (h : sz.STFlow κ ε 𝔠 𝔡 z)
    (n : ℕ) : |STflowE z n| ≤ 2 - κ := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact (abs_lemE_le (lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) (h.2 n).2.1)).trans (h.2 n).1

private theorem IniTermIIGen_mixed {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) : mSigma E σ * mSigma E (!σ) = 1 := by
  have hm := norm_mE hE
  cases σ <;> simp only [mSigma, Bool.not_true, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
  · rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]; simp
  · rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]; simp

private theorem IniTermIIGen_ck_pos {κ : ℝ} (h0 : 0 < κ) (h2 : κ ≤ 2) : 0 < cltCk κ := by
  unfold cltCk
  exact div_pos (Real.sqrt_pos.2 (mul_pos h0 (by linarith))) two_pos

/-- **Target 1, band result** (`gK = sz.lam`, `A = 1`): the class holds at `(STFlow, bandFM ∘ STflowE, sz.lam)`.  Producers:
`step2Gen_USemigroup_band`, `step5KerGen_thDecay_band`, `bandFM_STThg`, `prop8ZeroMode_holds` with `Theta0_apply_eq`,
`prop5Short_holds`, `sum_Theta_row_of_three_le`, `Theta_transpose_of_three_le`; the band margin is `κm = cltCk (min κ 2)`. -/
theorem iniTermGen_kerFacts_band (d : ℕ) : IniTermGen_KerFacts d (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun sz _ => sz.lam) := by
  intro hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  have hκ2 : 0 < min κ 2 := lt_min hκ two_pos
  have hκm : 0 < cltCk (min κ 2) := IniTermIIGen_ck_pos hκ2 (min_le_right κ 2)
  obtain ⟨C₆, hC₆, hdec⟩ := step5KerGen_thDecay_band d 𝔡⁻¹ hd hΛ
  obtain ⟨C₈, hC₈, H8⟩ := prop8ZeroMode_holds d 𝔡⁻¹ (cltCk (min κ 2)) hd hΛ hκm
  obtain ⟨Cs, hCs, c₀, hc₀, H5⟩ := prop5Short_holds d 𝔡⁻¹ (cltCk (min κ 2)) hd hΛ hκm
  refine ⟨C₆, C₈, Cs, c₀, 1, hC₆, hC₈, hCs, hc₀, le_rfl, ?_⟩
  intro sz ε 𝔠 z hflow
  have hE : ∀ n, |STflowE z n| ≤ 2 - κ := IniTermIIGen_flow_E hflow
  have hE2 : ∀ n, |STflowE z n| ≤ 2 := fun n => (hE n).trans (by linarith)
  have hT : ∀ n σ σ' (t : ℝ), STThg (bandFM sz (STflowE z)) n σ σ' t =
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (mSigma (STflowE z n) σ * mSigma (STflowE z n) σ')) :=
    fun n σ σ' t => bandFM_STThg sz (STflowE z) n σ σ' t
  refine ⟨fun n => step2Gen_USemigroup_band sz _ n (hE2 n), hdec sz _ hE2,
    fun n => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩, ?_, ?_⟩
  · intro n t _ _ σ
    rw [hT, hT, mul_comm (mSigma _ σ)]
  intro n hg hgΛ t ht0 ht1
  have hμ := IniTermIIGen_mixed (hE2 n)
  have hL := sz.three_le_L n
  have hξm : ∀ σ σ' : Bool, ‖(t : ℂ) * (mSigma (STflowE z n) σ * mSigma (STflowE z n) σ')‖ < 1 :=
    fun σ σ' => norm_mul_mSigma_lt_one (hE2 n) ht0 ht1 σ σ'
  have hIm : cltCk (min κ 2) ≤ (mE (STflowE z n)).im :=
    (cltCk_facts hκ2 ((hE n).trans (by have := min_le_left κ 2; linarith))).2.1
  refine ⟨fun σ b => ?_, fun σ a b => ?_, fun σ a b => ?_⟩
  · rw [hT, hμ, mul_one]
    have hξ := hξm σ (!σ); rw [hμ, mul_one] at hξ
    have hcol : ∀ a, Theta d (sz.L n) (sz.lam n) (t : ℂ) a b = Theta d (sz.L n) (sz.lam n) (t : ℂ) b a := fun a => by
      simpa [Matrix.transpose_apply] using
        congrFun (congrFun (Theta_transpose_of_three_le (d := d) (g := sz.lam n) hL hξ) b) a
    rw [Finset.sum_congr rfl fun a _ => hcol a, sum_Theta_row_of_three_le hL hξ b]
    push_cast; rfl
  · have hξ := hξm σ (!σ)
    have h8 := H8 (sz.L n) hL (sz.lam n) hg hgΛ t ht0 ht1 (mE (STflowE z n)) (norm_mE (hE2 n)) hIm σ (!σ) (b - a)
    have hps : ∀ σ, PropSpin (mE (STflowE z n)) σ = mSigma (STflowE z n) σ := fun _ => rfl
    rw [hps, hps, Theta0_apply_eq hL hξ, ← iniTermII_Theta_shift hL hξ] at h8
    rw [hT]
    have e : (1 - (t : ℂ) * (mSigma (STflowE z n) σ * mSigma (STflowE z n) (!σ))) = (((1 - t : ℝ) : ℂ)) := by
      rw [hμ]; push_cast; ring
    rw [e] at h8
    exact h8
  · have hξ := hξm σ σ
    have h5 := H5 (sz.L n) hL (sz.lam n) hg hgΛ t ht0 ht1 (mE (STflowE z n)) (norm_mE (hE2 n)) hIm σ (b - a)
    have hps : ∀ σ, PropSpin (mE (STflowE z n)) σ = mSigma (STflowE z n) σ := fun _ => rfl
    rw [hps, ← iniTermII_Theta_shift hL hξ a b] at h5
    have hif : (if b - a = 0 then (1 : ℝ) else 0) = if a = b then 1 else 0 := if_congr (sub_eq_zero.trans eq_comm) rfl rfl
    rw [hif, neg_mul] at h5
    rw [hT]
    exact h5


/-! ## 2. The propagator and the kernel on two indices -/

section Kernel

variable {d : ℕ} {sz : Sizes d}

/-- `Θ_t = 1 + t θ_t` from the semigroup law at the single fact `uKer_{t,t} = 1`. -/
theorem IniTermIIGen_Theta_eq (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n)
    (p q : Bool) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    STThg C n p q t = 1 + (t : ℂ) • Step2Gen_thetaKer C n p q t := by
  have h1 := (hU p q t t t ht0 ht1 ht0 ht1).1
  unfold Step2Gen_uKer at h1
  unfold STThg Step2Gen_thetaKer
  rw [sub_mul, one_mul, smul_mul_assoc] at h1
  exact sub_eq_iff_eq_add.mp h1

/-- `1 + (u - s) θ_u = (s/u) 1 + ((u-s)/u) Θ_u` for `u > 0`. -/
private theorem IniTermIIGen_Kmat (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n)
    (p q : Bool) {s u : ℝ} (hu0 : 0 < u) (hu : u < 1) :
    1 + ((u - s : ℝ) : ℂ) • Step2Gen_thetaKer C n p q u =
      ((s / u : ℝ) : ℂ) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) + (((u - s) / u : ℝ) : ℂ) • STThg C n p q u := by
  rw [IniTermIIGen_Theta_eq C n hU p q hu0.le hu]
  have : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  push_cast
  match_scalars <;> (field_simp; try ring)

/-- **`𝒰_{s,u,σ} = K ⊗ K`** (`(eq:decompU)`, `3_5:1983`; band `iniTermII_Ugen_rep`, `IniTermII:907`) for `σ`,
`K = α I + β Θ^{(σ₀σ₁)}_u`: the semigroup law gives `Θ = 1 + uθ`; slot `1` carries the pair `(σ₁,σ₀)`
(`finRotate 2 1 = 0`), identified with `(σ₀,σ₁)` by `hpair` (E1 for mixed `σ`, `σ₀ = σ₁` for same `σ`).  For `u = 0`
(so `s = 0`), `K = I`. -/
theorem IniTermIIGen_UN_rep (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n)
    {σ : Fin 2 → Bool} (hpair : ∀ u : ℝ, 0 < u → u < 1 → STThg C n (σ 1) (σ 0) u = STThg C n (σ 0) (σ 1) u)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1) :
    ∃ α β : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ β ∧ β ≤ 1 - s ∧ α + β * (1 - u)⁻¹ = (1 - s) / (1 - u) ∧
      ∀ (X : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)),
        Step2Gen_UN C n σ s u X a = ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
          ((if a 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * STThg C n (σ 0) (σ 1) u (a 0) b₁) *
            ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * STThg C n (σ 0) (σ 1) u (a 1) b₂) * X ![b₁, b₂] := by
  have hu0' : 0 < 1 - u := by linarith
  rcases eq_or_lt_of_le (hs.trans hsu) with hu0 | hupos
  · have hs0 : s = 0 := le_antisymm (hu0 ▸ hsu) hs
    refine ⟨1, 0, zero_le_one, le_rfl, le_rfl, by linarith, by rw [← hu0, hs0]; simp, ?_⟩
    intro X a
    rw [← hu0, hs0, Step2Gen_UN_self C n hU σ (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) < 1) X]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero]
    rw [Finset.sum_eq_single (a 0)]
    · rw [Finset.sum_eq_single (a 1)]
      · simp only [ite_true, one_mul]
        congr 1; funext i; fin_cases i <;> simp
      · intro b _ hb; simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro b _ hb; simp [Ne.symm hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hu0 : 0 < u := hupos
    refine ⟨s / u, (u - s) / u, div_nonneg hs hu0.le, (div_le_one hu0).2 hsu, div_nonneg (by linarith) hu0.le,
      (div_le_iff₀ hu0).2 (by nlinarith), by field_simp; ring, ?_⟩
    intro X a
    have hdec := Step5KerGen_UN_decomp C n hU σ s u hu0.le hu X a
    have hE := hpair u hu0 hu
    have hf0 : finRotate 2 0 = 1 := by decide
    have hf1 : finRotate 2 1 = 0 := by decide
    rw [hdec, iniTermII_sum_fin2]
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => ?_
    rw [Fin.prod_univ_two]
    simp only [hf0, hf1, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [IniTermIIGen_Kmat C n hU (σ 0) (σ 1) hu0 hu, IniTermIIGen_Kmat C n hU (σ 1) (σ 0) hu0 hu, hE]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- The row sums of `Θ`: `Σ_b |Θ_t(a,b)| ≤ (1 + C₆)/(1 - t)` from `Θ = 1 + tθ` and the row-sum clause of `ThDecay`
(`hrow`: `Σ_b |θ_t(a,b)| ≤ C₆/(1 - t)`, the second conjunct of `Step5KerGen_ThDecay` at an index with `0 < gK n ≤ Λ`). -/
theorem IniTermIIGen_row_le (C : FlowFM sz) (n : ℕ) (hU : Step2Gen_USemigroup C n) (p q : Bool) {t C₆ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd d (sz.L n))
    (hrow : ∑ b, ‖Step2Gen_thetaKer C n p q t a b‖ ≤ C₆ / (1 - t)) :
    ∑ b, ‖STThg C n p q t a b‖ ≤ (1 + C₆) * (1 - t)⁻¹ := by
  have e : ∀ b, ‖STThg C n p q t a b‖ ≤ (if a = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n p q t a b‖ := by
    intro b
    rw [IniTermIIGen_Theta_eq C n hU p q ht0 ht1, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1.le
  have h1t : 0 < 1 - t := by linarith
  have hinv : 1 ≤ (1 - t)⁻¹ := (one_le_inv₀ h1t).2 (by linarith)
  calc ∑ b, ‖STThg C n p q t a b‖ ≤ ∑ b, ((if a = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n p q t a b‖) :=
        Finset.sum_le_sum fun b _ => e b
    _ = 1 + ∑ b, ‖Step2Gen_thetaKer C n p q t a b‖ := by rw [Finset.sum_add_distrib]; simp
    _ ≤ 1 + C₆ / (1 - t) := by linarith
    _ ≤ (1 + C₆) * (1 - t)⁻¹ := by rw [add_mul, div_eq_mul_inv]; linarith


/-! ## 3. The profile `(uwp2-92kj)` for `Θ` -/

/-- **`(uwp2-92kj)` without the floor** for the carrier propagator (band `iniTermII_stageA`, `IniTermII:327`): with `Θ = 1 + uθ`
the profile `step5KerGen_profile_holds` of `θ` (at `(u, t) ↦ (s, u)`, decay at `gK`, windows at `sz.lam`, R1) gives
`(1-s) Σ_b |Θ_u(a₁,b)| 𝒯_s(|b-a₂|) ≤ C 𝒯_u(|a₁-a₂|)` with `C = Cp + 1`; the floor `w` is arbitrary. -/
private theorem IniTermIIGen_stageA (d : ℕ) (hd : 3 ≤ d) (Λ C₆ A : ℝ) (hΛ : 0 < Λ) (hC₆ : 0 < C₆) (hA : 1 ≤ A) :
    ∃ CA : ℝ, 0 < CA ∧ ∀ (sz : Sizes d) (C : FlowFM sz) (gK : ℕ → ℝ), Step5KerGen_ThDecay C gK Λ C₆ →
      (∀ n, 0 ≤ gK n * sz.lam n ∧ gK n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ A * gK n ^ 2) →
      ∀ (n : ℕ), Step2Gen_USemigroup C n → ∀ (σ σ' : Bool) (s u : ℝ), 0 < gK n → gK n ≤ Λ → 0 ≤ s → s ≤ u → u < 1 →
        1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → ∀ a₁ a₂ : Zd d (sz.L n),
          (1 - s) * ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
              tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
            CA * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := by
  obtain ⟨Cp, hCp, H⟩ := step5KerGen_profile_holds d hd Λ C₆ A hΛ hC₆ hA
  refine ⟨Cp + 1, by positivity, ?_⟩
  intro sz C gK hdec hcmp n hU σ σ' s u hg hgΛ hs hsu hu hreg a₁ a₂
  obtain ⟨hlam, hc1⟩ := Step5KerGen_cmp_pos (hcmp n) hg
  have hs1 : 0 ≤ 1 - s := by linarith
  have hu0 : 0 < 1 - u := by linarith
  have hu0' : 0 ≤ u := hs.trans hsu
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  set ρ : ℝ := (1 - s) / (1 - u) with hρdef
  have hρ : 0 ≤ ρ := div_nonneg hs1 hu0.le
  have hρ1 : 1 - s ≤ ρ := le_div_self hs1 hu0 (by linarith)
  apply le_of_forall_pos_le_add
  intro ε hε
  set w : ℝ := ε / ((Cp + 1) * (1 + ρ)) with hwdef
  have hw : 0 < w := div_pos hε (by positivity)
  have h := H sz C gK hdec hcmp n σ σ' w⁻¹ 1 s u hg hgΛ (inv_pos.mpr hw) hs hsu hu (Or.inr hreg) a₁ a₂
  rw [Real.rpow_neg_one, inv_inv] at h
  have hW : ∀ r : ℝ, tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 r =
      max (tailT d (sz.L n) (sz.lam n) s (min r ((sz.L n : ℕ) : ℝ))) w := fun r => by
    unfold tailW; rw [Real.rpow_neg_one, inv_inv]
  have hle : ∀ b : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
      tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ) := fun b => by
    rw [hW, min_eq_left (iniTermII_zdistInf_le_L _)]
    exact le_max_left _ _
  have hTW : tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) ≤
      tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + w := by
    rw [hW, min_eq_left (iniTermII_zdistInf_le_L _)]
    exact max_le ((iniTermII_tailT_mono hlam.le hL1 hsu hu (Nat.cast_nonneg _)).trans (le_add_of_nonneg_right hw.le))
      (le_add_of_nonneg_left (tailT_nonneg (Nat.cast_nonneg _)))
  have e : ∀ b, ‖STThg C n σ σ' u a₁ b‖ ≤ (if a₁ = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ := by
    intro b
    rw [IniTermIIGen_Theta_eq C n hU σ σ' hu0' hu, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0']
      exact mul_le_of_le_one_left (norm_nonneg _) hu.le
  have hTWn : ∀ r : ℝ, 0 ≤ tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 r := fun r => by
    rw [hW]; exact le_max_of_le_right hw.le
  have hsum : ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
        tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ) ≤
      tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) +
        ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ) := by
    calc _ ≤ ∑ b : Zd d (sz.L n), (((if a₁ = b then (1 : ℝ) else 0) + ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖) *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ)) :=
          Finset.sum_le_sum fun b _ => mul_le_mul (e b) (hle b) (tailT_nonneg (Nat.cast_nonneg _))
            (add_nonneg (by split_ifs <;> norm_num) (norm_nonneg _))
      _ = _ := by
          simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
            ite_true]
  have hρw : (Cp + 1) * (ρ * w) ≤ ε := by
    have hCp1 : (Cp + 1) ≠ 0 := by positivity
    have hρ1' : (1 + ρ) ≠ 0 := by positivity
    have e : (Cp + 1) * (ρ * w) = ρ / (1 + ρ) * ε := by rw [hwdef]; field_simp
    rw [e]
    have : ρ / (1 + ρ) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
    nlinarith [hε]
  have hT0 : 0 ≤ tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  calc (1 - s) * ∑ b : Zd d (sz.L n), ‖STThg C n σ σ' u a₁ b‖ *
          tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b - a₂) : ℕ)
      ≤ (1 - s) * (tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) +
        ∑ b : Zd d (sz.L n), ‖Step2Gen_thetaKer C n σ σ' u a₁ b‖ *
          tailW d (sz.L n) (sz.lam n) s ((sz.L n : ℕ) : ℝ) w⁻¹ 1 (zdistInf d (sz.L n) (b - a₂) : ℕ)) :=
        mul_le_mul_of_nonneg_left hsum hs1
    _ ≤ (1 - s) * (tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + w) +
          (Cp * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + Cp * (ρ * w)) := by
        rw [mul_add]
        refine add_le_add (mul_le_mul_of_nonneg_left hTW hs1) ?_
        exact h
    _ ≤ (Cp + 1) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) + (Cp + 1) * (ρ * w) := by
        have h1 : (1 - s) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) ≤
            tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℕ) := by nlinarith
        have h2 : (1 - s) * w ≤ ρ * w := mul_le_mul_of_nonneg_right hρ1 hw.le
        nlinarith
    _ ≤ _ := by linarith

end Kernel

/-! ## 4. The second index and the bilinear estimate -/

section Bil

variable {d L : ℕ} [NeZero L]

/-- The second-index smoothing (`3_5:2275`, first `≺`, via `(uwp2-92kj)`; band `iniTermII_ZA`, `IniTermII:369`): with
`|K(a,b)| ≤ α 1_{a=b} + β |Θ_{ab}|`, `α ≤ 1`, `β ≤ 1-s`, `α + β/(1-u) = (1-s)/(1-u)`, the profile `hA` of `Θ` and its row
sums `Σ_b |Θ(a,b)| ≤ CR/(1-u)`, and `|X| ≤ M (q 𝒯_s + F)`. -/
private theorem IniTermIIGen_ZA (Th : Zd d L → Zd d L → ℂ) {g s u α β M q F CA CR : ℝ}
    (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u < 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1 - s)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hM : 0 ≤ M) (hq : 0 ≤ q) (hF : 0 ≤ F) (hCA : 0 ≤ CA) (hCR : 1 ≤ CR) (hg : 0 ≤ g) (hL1 : (1 : ℝ) ≤ L)
    (hrowsum : ∀ a : Zd d L, ∑ b : Zd d L, ‖Th a b‖ ≤ CR * (1 - u)⁻¹)
    (hA : ∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Th a₁ b‖ *
        tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤ CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ))
    (a₂ b₁ : Zd d L) :
    ∑ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Th a₂ b₂‖) *
        (M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F))
      ≤ (1 + CA) * CR * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  set y : Zd d L → ℝ := fun b₂ => M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F) with hy
  have hTs : ∀ b₂ : Zd d L, 0 ≤ tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) :=
    fun b₂ => tailT_nonneg (Nat.cast_nonneg _)
  have hTu : 0 ≤ tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := tailT_nonneg (Nat.cast_nonneg _)
  have h1 : ∀ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Th a₂ b₂‖) * y b₂
      = (if a₂ = b₂ then α * y b₂ else 0) + β * (‖Th a₂ b₂‖ * y b₂) := by
    intro b₂; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun b₂ _ => h1 b₂, Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.mul_sum]
  simp only [Finset.mem_univ, ite_true]
  -- the identity term
  have hid : α * y a₂ ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F) := by
    have h := iniTermII_tailT_mono (d := d) hg hL1 hsu hu (r := (zdistInf d L (b₁ - a₂) : ℕ)) (Nat.cast_nonneg _)
    simp only [hy]
    have h2 : α * (M * (q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + F))
        = M * (α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) + α * F) := by ring
    rw [h2]
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hM
    have hqs : α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) ≤ 1 * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα1 hq) (tailT_nonneg (Nat.cast_nonneg _))
    calc α * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ)
        ≤ 1 * q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := hqs
      _ = q * tailT d L g s (zdistInf d L (b₁ - a₂) : ℕ) := by ring
      _ ≤ q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := mul_le_mul_of_nonneg_left h hq
  -- the propagator term
  have hrow : ∑ b : Zd d L, ‖Th a₂ b‖ ≤ CR * (1 - u)⁻¹ := hrowsum a₂
  have hsplit : ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * y b₂
      = M * q * (∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
        + M * F * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    simp only [hy]; ring
  have hprop : β * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ)
      ≤ CA * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := by
    have hsw : ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ)
        = ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) :=
      Finset.sum_congr rfl fun b₂ _ => by rw [iniTermII_zdistInf_sub_comm b₁ b₂]
    have hnn : 0 ≤ ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) :=
      Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (tailT_nonneg (Nat.cast_nonneg _))
    have := hA a₂ b₁
    rw [iniTermII_zdistInf_sub_comm a₂ b₁] at this
    rw [hsw]
    calc β * _ ≤ (1 - s) * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ *
          tailT d L g s (zdistInf d L (b₂ - b₁) : ℕ) := mul_le_mul_of_nonneg_right hβ1 hnn
      _ ≤ _ := this
  calc α * y a₂ + β * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * y b₂
      ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F)
        + (M * q * (β * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
          + M * F * (β * (CR * (1 - u)⁻¹))) := by
        refine add_le_add hid ?_
        rw [hsplit]
        have : β * (M * q * (∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
            + M * F * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖)
            = M * q * (β * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖ * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ))
              + M * F * (β * ∑ b₂ : Zd d L, ‖Th a₂ b₂‖) := by ring
        rw [this]
        refine add_le_add le_rfl ?_
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrow hβ0) (mul_nonneg hM hF)
    _ ≤ M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + α * F)
        + (M * q * (CA * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + M * F * (β * (CR * (1 - u)⁻¹))) := by
        refine add_le_add le_rfl (add_le_add ?_ le_rfl)
        exact mul_le_mul_of_nonneg_left hprop (mul_nonneg hM hq)
    _ = (1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + M * F * (α + CR * (β * (1 - u)⁻¹)) := by ring
    _ ≤ (1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + M * F * (CR * ((1 - s) / (1 - u))) := by
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hM hF))
        rw [← hαβ]
        nlinarith [mul_nonneg hα0 (sub_nonneg.2 hCR)]
    _ ≤ _ := by
        have hρ : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1 hu0.le
        have hCR0 : 0 ≤ CR := by linarith
        have h1 : 0 ≤ (1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) := by positivity
        have h2 : 0 ≤ CA * M * ((1 - s) / (1 - u) * F) := by positivity
        have h3 : 0 ≤ (CR - 1) * ((1 + CA) * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))) :=
          mul_nonneg (sub_nonneg.2 hCR) h1
        nlinarith [h1, h2, h3, mul_nonneg hCR0 h2]

private theorem IniTermIIGen_Kf_norm_le (Th : Zd d L → Zd d L → ℂ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (a b : Zd d L) :
    ‖(if a = b then (α : ℂ) else 0) + (β : ℂ) * Th a b‖ ≤ α * (if a = b then 1 else 0) + β * ‖Th a b‖ := by
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · split_ifs
    · simp [Real.norm_of_nonneg hα]
    · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]

/-- `K - (ρ/L^d) J = α (1 - L^{-d} J) + β Θ̊` in norm (band `iniTermII_Kf_sub`, `_sub_norm_le`, `IniTermII:681-704`). -/
private theorem IniTermIIGen_Kf_sub_norm_le (Th : Zd d L → Zd d L → ℂ) {g s u α β C₈ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u))
    (hΘ : ∀ a b : Zd d L, ‖Th a b - ((L : ℂ) ^ d)⁻¹ * (((1 - u : ℝ) : ℂ))⁻¹‖ ≤ C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a))
    (a b : Zd d L) :
    ‖((if a = b then (α : ℂ) else 0) + (β : ℂ) * Th a b) - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)‖
      ≤ α * ((if a = b then 1 else 0) + ((L : ℝ) ^ d)⁻¹) + β * (C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a)) := by
  have e : ((if a = b then (α : ℂ) else 0) + (β : ℂ) * Th a b) - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)
      = (α : ℂ) * ((if a = b then (1 : ℂ) else 0) - ((L : ℂ) ^ d)⁻¹)
        + (β : ℂ) * (Th a b - ((L : ℂ) ^ d)⁻¹ * (((1 - u : ℝ) : ℂ))⁻¹) := by
    rw [← hαβ]
    push_cast
    split_ifs <;> ring
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]
    refine mul_le_mul_of_nonneg_left ?_ hα
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · split_ifs <;> simp
    · rw [norm_inv, norm_pow, Complex.norm_natCast]
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left (hΘ a b) hβ

end Bil

section Bil2

variable {L : ℕ} [NeZero L]

/-- **The bilinear estimate** `Σ_{b₁,b₂} (K - ρ L^{-d} J)(a₁,b₁) K(a₂,b₂) X(b₁,b₂)`, `K = α I + β Θ_u` (band `iniTermII_bil`,
`IniTermII:712`), for an abstract propagator `Th` with the profile `hA`, the row sums `hrowsum` and the zero-mode bound `hΘ`
(`C₈ (g²)⁻¹ P(|b-a|)`, `g` the size-level coupling). -/
private theorem IniTermIIGen_bil (d : ℕ) (hd : 3 ≤ d) (CA CR C₈ : ℝ) (hCA : 0 ≤ CA) (hCR : 1 ≤ CR) (hC₈ : 0 ≤ C₈) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g s u α β M q F : ℝ, 0 < g → 0 ≤ s → s ≤ u →
      u < 1 → 1 - s ≤ g ^ 2 / (L : ℝ) ^ 2 → 0 ≤ α → α ≤ 1 → 0 ≤ β → β ≤ 1 - s →
      α + β * (1 - u)⁻¹ = (1 - s) / (1 - u) → 0 ≤ M → 0 ≤ q → 0 ≤ F → ∀ Th : Zd d L → Zd d L → ℂ,
      (∀ a₁ a₂ : Zd d L, (1 - s) * ∑ b : Zd d L, ‖Th a₁ b‖ * tailT d L g s (zdistInf d L (b - a₂) : ℕ) ≤
        CA * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ)) →
      (∀ a : Zd d L, ∑ b : Zd d L, ‖Th a b‖ ≤ CR * (1 - u)⁻¹) →
      (∀ a b : Zd d L, ‖Th a b - ((L : ℂ) ^ d)⁻¹ * (((1 - u : ℝ) : ℂ))⁻¹‖
        ≤ C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b - a)) →
      ∀ (a₁ a₂ : Zd d L) (X : Zd d L → Zd d L → ℂ),
        (∀ b₁ b₂, ‖X b₁ b₂‖ ≤ M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) →
        ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
            (((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)) *
              ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂) * X b₁ b₂‖
          ≤ C * M * (q * tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) + (1 - s) / (1 - u) * F) := by
  set K : ℝ := (d : ℝ) ^ (d - 2) with hK
  set CSD : ℝ := Real.exp (√(d : ℝ)) * (2 ^ d * radC 1) with hCSDdef
  set CSI : ℝ := K * CSD with hCSIdef
  set CCv : ℝ := Real.exp (2 * √(d : ℝ)) * convC (d - 2) with hCCvdef
  have hK0 : 0 ≤ K := by positivity
  have hCSD : 0 ≤ CSD := by have := radC_pos (one_pos : (0 : ℝ) < 1); positivity
  have hCSI : 0 ≤ CSI := mul_nonneg hK0 hCSD
  have hCCv : 0 ≤ CCv := by have := radC_pos κ₀_pos; rw [hCCvdef]; unfold convC; positivity
  set Cq : ℝ := 1 + (CSI + 1) * Real.exp 1 + C₈ * (2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) with hCq
  set Cf : ℝ := 2 + C₈ * CSD with hCf
  have hCq0 : 0 ≤ Cq := by positivity
  have hCf0 : 0 ≤ Cf := by positivity
  have hCR0 : 0 < CR := by linarith
  refine ⟨(1 + CA) * CR * (Cq + Cf + 1), by positivity, ?_⟩
  intro L _ hL g s u α β M q F hg hs hsu hu hreg hα0 hα1 hβ0 hβ1 hαβ hM hq hF Th hA hrowsum hΘ a₁ a₂ X hX
  have hL1 : (1 : ℝ) ≤ L := by
    have : (3 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hu0 : 0 < 1 - u := by linarith
  have hs1 : 0 ≤ 1 - s := by linarith
  have hρ0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hs1 hu0.le
  have hregu : 1 - u ≤ g ^ 2 / (L : ℝ) ^ 2 := by linarith
  have hβL : β * (L : ℝ) ^ 2 ≤ g ^ 2 := by
    have : β ≤ g ^ 2 / (L : ℝ) ^ 2 := hβ1.trans hreg
    rwa [le_div_iff₀ (by positivity)] at this
  have hSD : ∑ x : Zd d L, iniTermII_PD d L x ≤ CSD * (L : ℝ) ^ 2 := by
    have := iniTermII_sum_PD (d := d) (L := L) hd hL1
    calc _ ≤ _ := this
      _ = CSD * (L : ℝ) ^ 2 := by rw [hCSDdef]; ring
  have hSI : ∑ x : Zd d L, iniTermII_PI d L x ≤ CSI * (L : ℝ) ^ 2 := by
    have := iniTermII_sum_PI (d := d) (L := L) hd hL1
    calc _ ≤ _ := this
      _ = CSI * (L : ℝ) ^ 2 := by rw [hCSIdef, hCSDdef, hK]; ring
  have hconv : ∀ a b : Zd d L, ∑ c : Zd d L, iniTermII_PD d L (a - c) * iniTermII_PD d L (c - b)
      ≤ CCv * (L : ℝ) ^ 2 * iniTermII_PD d L (a - b) := fun a b => iniTermII_conv_PD hd a b
  set ρ : ℝ := (1 - s) / (1 - u) with hρ
  set c : ℝ := (L : ℝ) ^ d with hc
  have hc0 : 0 < c := by positivity
  set C₁ : ℝ := (1 + CA) * CR with hC₁
  have hC₁0 : 0 < C₁ := by positivity
  have hZ := fun b₁ => IniTermIIGen_ZA (d := d) (L := L) Th (g := g) (s := s) (u := u) (α := α) (β := β) (M := M)
    (q := q) (F := F) (CA := CA) (CR := CR) hs hsu hu hα0 hα1 hβ0 hβ1 hαβ hM hq hF hCA hCR hg.le hL1 hrowsum hA a₂ b₁
  -- the weights
  set T₀ : ℝ := tailT d L g u (zdistInf d L (a₁ - a₂) : ℕ) with hT₀
  have hT₀0 : 0 ≤ T₀ := tailT_nonneg (Nat.cast_nonneg _)
  set R : Zd d L → ℝ := fun b₁ => C₁ * M * (q * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + ρ * F) with hR
  have hRnn : ∀ b₁, 0 ≤ R b₁ := fun b₁ => by
    have := tailT_nonneg (d := d) (L := L) (g := g) (t := u) (Nat.cast_nonneg (zdistInf d L (b₁ - a₂)))
    simp only [hR]; positivity
  set kk : Zd d L → ℝ := fun b₁ => α * ((if a₁ = b₁ then 1 else 0) + c⁻¹) + β * (C₈ * (g ^ 2)⁻¹ * iniTermII_PD d L (b₁ - a₁)) with hkk
  have hkknn : ∀ b₁, 0 ≤ kk b₁ := fun b₁ => by
    have := iniTermII_PD_nonneg (d := d) (L := L) (b₁ - a₁)
    simp only [hkk]; positivity
  -- step 1 and 2
  have hstep12 : ‖∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
            (((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - (((ρ / c : ℝ)) : ℂ)) *
              ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂) * X b₁ b₂‖ ≤ ∑ b₁ : Zd d L, kk b₁ * R b₁ := by
    calc _ ≤ ∑ b₁ : Zd d L, ‖∑ b₂ : Zd d L, (((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - (((ρ / c : ℝ)) : ℂ)) *
              ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂) * X b₁ b₂‖ := norm_sum_le _ _
      _ ≤ ∑ b₁ : Zd d L, kk b₁ * R b₁ := by
        refine Finset.sum_le_sum fun b₁ _ => ?_
        have hsum_nn : 0 ≤ ∑ b₂ : Zd d L, (α * (if a₂ = b₂ then 1 else 0) + β * ‖Th a₂ b₂‖) *
            (M * (q * tailT d L g s (zdistInf d L (b₁ - b₂) : ℕ) + F)) :=
          Finset.sum_nonneg fun b₂ _ => by
            have := tailT_nonneg (d := d) (L := L) (g := g) (t := s) (Nat.cast_nonneg (zdistInf d L (b₁ - b₂)))
            positivity
        calc ‖∑ b₂ : Zd d L, (((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - (((ρ / c : ℝ)) : ℂ)) *
              ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂) * X b₁ b₂‖
            ≤ ∑ b₂ : Zd d L, ‖(((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - (((ρ / c : ℝ)) : ℂ)) *
              ((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂) * X b₁ b₂‖ := norm_sum_le _ _
          _ = ‖((if a₁ = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th a₁ b₁) - (((ρ / c : ℝ)) : ℂ)‖ *
              ∑ b₂ : Zd d L, ‖((if a₂ = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th a₂ b₂)‖ * ‖X b₁ b₂‖ := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun b₂ _ => by rw [norm_mul, norm_mul]; ring
          _ ≤ kk b₁ * R b₁ := by
              refine mul_le_mul (IniTermIIGen_Kf_sub_norm_le Th hα0 hβ0 hαβ hΘ a₁ b₁) ?_
                (Finset.sum_nonneg fun b₂ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hkknn b₁)
              refine le_trans (Finset.sum_le_sum fun b₂ _ => mul_le_mul (IniTermIIGen_Kf_norm_le Th hα0 hβ0 a₂ b₂)
                (hX b₁ b₂) (norm_nonneg _) (by positivity)) ?_
              exact hZ b₁
  -- step 3
  have hsplit : ∑ b₁ : Zd d L, kk b₁ * R b₁ =
      α * R a₁ + (α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ +
        β * C₈ * (g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁) := by
    have hterm : ∀ b₁ : Zd d L, kk b₁ * R b₁ =
        (if a₁ = b₁ then α * R b₁ else 0) + (α * c⁻¹ * R b₁ +
          β * C₈ * (g ^ 2)⁻¹ * (iniTermII_PD d L (b₁ - a₁) * R b₁)) := by
      intro b₁; simp only [hkk]; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b₁ _ => hterm b₁, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.sum_add_distrib]
    simp only [Finset.mem_univ, ite_true, ← Finset.mul_sum]
  have hRa : R a₁ = C₁ * M * (q * T₀ + ρ * F) := rfl
  have hT0nn : ∀ b₁ : Zd d L, 0 ≤ tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) := fun b₁ =>
    tailT_nonneg (Nat.cast_nonneg _)
  have hsumR : ∑ b₁ : Zd d L, R b₁ =
      C₁ * M * (q * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ) + c * (ρ * F)) := by
    simp only [hR]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_const, Finset.card_univ, hc]
  have hsumPR : ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁ =
      C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁)) := by
    have : C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))
        = ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁ := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by simp only [hR]; ring
    exact this.symm
  -- the three pieces
  have hS2 := iniTermII_S2 (d := d) (L := L) (g := g) (u := u) (CSI := CSI) hL1 hg hu hregu hSI hCSI a₁ a₂
  have hS3 := iniTermII_S3 (d := d) (L := L) (g := g) (u := u) (β := β) (CSD := CSD) (CCv := CCv) hd hL1 hg hu hregu
    hβ0 hβL hSD hCSD hconv hCCv a₁ a₂
  have hS3F := iniTermII_S3F (d := d) (L := L) (g := g) (β := β) (CSD := CSD) hg hβL hβ0 hSD hCSD a₁
  have hqT : 0 ≤ q * T₀ := mul_nonneg hq hT₀0
  have hρF : 0 ≤ ρ * F := mul_nonneg hρ0 hF
  have hi : α * R a₁ ≤ C₁ * M * (q * T₀ + ρ * F) := by
    rw [← hRa]
    calc α * R a₁ ≤ 1 * R a₁ := mul_le_mul_of_nonneg_right hα1 (hRnn a₁)
      _ = R a₁ := one_mul _
  have hii : α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ ≤ C₁ * M * (q * ((CSI + 1) * Real.exp 1 * T₀) + ρ * F) := by
    have h1 : α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ ≤ c⁻¹ * ∑ b₁ : Zd d L, R b₁ := by
      have hnn : 0 ≤ c⁻¹ * ∑ b₁ : Zd d L, R b₁ := mul_nonneg (inv_nonneg.mpr hc0.le) (Finset.sum_nonneg fun b _ => hRnn b)
      calc α * c⁻¹ * ∑ b₁ : Zd d L, R b₁ = α * (c⁻¹ * ∑ b₁ : Zd d L, R b₁) := by ring
        _ ≤ 1 * (c⁻¹ * ∑ b₁ : Zd d L, R b₁) := mul_le_mul_of_nonneg_right hα1 hnn
        _ = _ := one_mul _
    have h2 : c⁻¹ * ∑ b₁ : Zd d L, R b₁ = C₁ * M * (q * (c⁻¹ * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) + ρ * F) := by
      rw [hsumR]; field_simp
    have h3 : q * (c⁻¹ * ∑ b₁ : Zd d L, tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)) ≤ q * ((CSI + 1) * Real.exp 1 * T₀) :=
      mul_le_mul_of_nonneg_left hS2 hq
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := by
        have : 0 ≤ C₁ * M := by positivity
        exact mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl) this
  have hiii : β * C₈ * (g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * R b₁
      ≤ C₁ * M * (q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) + ρ * F * (C₈ * CSD)) := by
    rw [hsumPR]
    have : β * C₈ * (g ^ 2)⁻¹ * (C₁ * M * (q * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ)
        + ρ * F * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁)))
        = C₁ * M * (q * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))))
          + ρ * F * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))))) := by ring
    rw [this]
    have hA1 : q * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁) * tailT d L g u (zdistInf d L (b₁ - a₂) : ℕ))))
        ≤ q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS3 hC₈) hq
    have hA2 : ρ * F * (C₈ * (β * ((g ^ 2)⁻¹ * ∑ b₁ : Zd d L, iniTermII_PD d L (b₁ - a₁))))
        ≤ ρ * F * (C₈ * CSD) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS3F hC₈) hρF
    have : 0 ≤ C₁ * M := by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add hA1 hA2) this
  -- assemble
  have hfinal : ∑ b₁ : Zd d L, kk b₁ * R b₁ ≤ C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) := by
    rw [hsplit]
    calc _ ≤ C₁ * M * (q * T₀ + ρ * F) + (C₁ * M * (q * ((CSI + 1) * Real.exp 1 * T₀) + ρ * F)
          + C₁ * M * (q * (C₈ * ((2 * Real.exp 1 * K * CCv + Real.exp 1 * CSD) * T₀)) + ρ * F * (C₈ * CSD))) :=
          add_le_add hi (add_le_add hii hiii)
      _ = _ := by rw [hCq, hCf]; ring
  have hmain : C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) ≤ C₁ * (Cq + Cf + 1) * M * (q * T₀ + ρ * F) := by
    have h1 : 0 ≤ C₁ * M * ((Cf + 1) * (q * T₀) + (Cq + 1) * (ρ * F)) := by positivity
    have h2 : C₁ * (Cq + Cf + 1) * M * (q * T₀ + ρ * F)
        = C₁ * M * (Cq * (q * T₀) + Cf * (ρ * F)) + C₁ * M * ((Cf + 1) * (q * T₀) + (Cq + 1) * (ρ * F)) := by ring
    rw [h2]; exact le_add_of_nonneg_right h1
  exact hstep12.trans (hfinal.trans hmain)

end Bil2

section ZeroMode

variable {d L : ℕ} [NeZero L]

/-- `Q^{(1)} (K ⊗ K) = (K - (ρ/L^d) J) ⊗ K`: the zero mode of the first index, `Σ_c K(c,b) = ρ` from the column sum
`Σ_c Θ(c,b) = (1-u)⁻¹` (band `iniTermII_zms_rep`, `IniTermII:963`; here the column sum is the datum `hcol`). -/
private theorem IniTermIIGen_zms_rep (Th : Zd d L → Zd d L → ℂ) {s u α β : ℝ}
    (hcol : ∀ b : Zd d L, ∑ c : Zd d L, Th c b = (((1 - u : ℝ) : ℂ))⁻¹)
    (hαβ : α + β * (1 - u)⁻¹ = (1 - s) / (1 - u)) (X : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    zeroModeSet d L {0} (fun a' : Fin 2 → Zd d L => ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
        ((if a' 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th (a' 0) b₁) *
          ((if a' 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th (a' 1) b₂) * X ![b₁, b₂]) a
      = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
          (((if a 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th (a 0) b₁)
            - ((((1 - s) / (1 - u) / (L : ℝ) ^ d : ℝ)) : ℂ)) *
          ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th (a 1) b₂) * X ![b₁, b₂] := by
  have hcol' : ∀ b₁ : Zd d L, ∑ c : Zd d L, ((if c = b₁ then (α : ℂ) else 0) + (β : ℂ) * Th c b₁)
      = (((1 - s) / (1 - u) : ℝ) : ℂ) := by
    intro b₁
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ c : Zd d L, (if c = b₁ then (α : ℂ) else 0) = α := by simp
    rw [h1, hcol b₁, ← hαβ]
    push_cast
    ring
  have hLd : ((L : ℂ) ^ d) ≠ 0 := by
    have : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
    exact pow_ne_zero _ this
  have hupd : ∀ (c : Zd d L), (Function.update a 0 c) 0 = c ∧ (Function.update a 0 c) 1 = a 1 := fun c =>
    ⟨by simp, by simp⟩
  have hS : ∑ x : Zd d L, ∑ x_1 : Zd d L, ∑ x_2 : Zd d L,
        ((if x = x_1 then (α : ℂ) else 0) + (β : ℂ) * Th x x_1) *
          ((if a 1 = x_2 then (α : ℂ) else 0) + (β : ℂ) * Th (a 1) x_2) * X ![x_1, x_2]
      = ∑ b₁ : Zd d L, ∑ b₂ : Zd d L, (((1 - s) / (1 - u) : ℝ) : ℂ) *
          ((if a 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * Th (a 1) b₂) * X ![b₁, b₂] := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hcol']
  simp only [zeroModeSet, Finset.toList_singleton, List.foldr, zeroModeOp, avgOp]
  simp only [hupd]
  rw [hS]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  push_cast
  field_simp

end ZeroMode

/-! ## 5. Target 2: the deterministic cores -/

section Cores

variable {d : ℕ}

private theorem IniTermIIGen_not_of_ne {σ : Fin 2 → Bool} (h : σ 0 ≠ σ 1) : σ 1 = !σ 0 := by
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> simp_all

/-- R1 at one index crosses `(g² + |1-u|)⁻¹ ≤ (g²)⁻¹ ≤ A (l²)⁻¹` (UBA-C1, the Θ̊ bound and the zero mode). -/
private theorem IniTermIIGen_cross_inv {g l A c P u x : ℝ} (hc : 0 ≤ c) (hP : 0 ≤ P)
    (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hg : 0 < g)
    (hx : x ≤ c * (g ^ 2 + |1 - u|)⁻¹ * P) : x ≤ c * A * (l ^ 2)⁻¹ * P := by
  obtain ⟨hl, -⟩ := Step5KerGen_cmp_pos h hg
  have hg2 : 0 < g ^ 2 := by positivity
  have h1 : (g ^ 2 + |1 - u|)⁻¹ ≤ A * (l ^ 2)⁻¹ := by
    calc (g ^ 2 + |1 - u|)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith [abs_nonneg (1 - u)])
      _ ≤ A * (l ^ 2)⁻¹ := by
        rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hg2 (by positivity)]
        linarith [h.2.2]
  refine hx.trans ?_
  calc c * (g ^ 2 + |1 - u|)⁻¹ * P ≤ c * (A * (l ^ 2)⁻¹) * P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc) hP
    _ = _ := by ring

/-- **Target 2, `σ₁ ≠ σ₂`: the deterministic core of `(zYU2)`** (`3_5:2268-2281`; band `iniTermII_core`, `IniTermII:1051`)
over the carrier.  The class `IniTermGen_KerFacts` is the only kernel input.  For `0 ≤ s ≤ u < 1`, the guard
`0 < gK ≤ 𝔡⁻¹`, regime (ii) `1 - s ≤ lam²/L²`, `σ₁ ≠ σ₂` and every two-index `X` with
`|X_b| ≤ M ((λ W^{-d}) 𝒯_s(|b₁-b₂|) + W^{-D})` (the `STDecay` profile at `s`, `𝒯` at the size coupling `sz.lam`):
`|[Q^{(1)} 𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + ((1-s)/(1-u)) W^{-D})`, `C = C(d, κ, 𝔡)`. -/
theorem iniTermIIGen_core (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n →
      gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 →
        1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
            W ^ (-D))) →
          ∀ a, ‖zeroModeSet d (sz.L n) {0} (Step2Gen_UN (mk sz z) n σ s u X) a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) +
              (1 - s) / (1 - u) * W ^ (-D)) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, hC₈, hCs, hc₀, hA, H⟩ := hKF hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨CA, hCA, hAL⟩ := IniTermIIGen_stageA d hd 𝔡⁻¹ C₆ A hΛ hC₆ hA
  obtain ⟨C, hC, Hb⟩ := IniTermIIGen_bil d hd CA (1 + C₆) (C₈ * A) hCA.le (by linarith) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ W D s u M lam hW hs hsu hu hreg hM hlam σ hσ X hX a
  obtain ⟨hU, hdec, hR1, hE1, hG⟩ := H sz ε 𝔠 z hflow
  have hu0 : 0 ≤ u := hs.trans hsu
  have h10 : σ 1 = !σ 0 := IniTermIIGen_not_of_ne hσ
  obtain ⟨hlamn, -⟩ := Step5KerGen_cmp_pos (hR1 n) hg
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ := IniTermIIGen_UN_rep (mk sz z) n (hU n)
    (σ := σ) (fun v hv0 hv1 => by
      have := hE1 n v hv0.le hv1 (σ 0); rw [← h10] at this; exact this.symm) hs hsu hu
  obtain ⟨hcol, hzero, -⟩ := hG n hg hgΛ u hu0 hu
  have hcol' : ∀ b : Zd d (sz.L n), ∑ c : Zd d (sz.L n), STThg (mk sz z) n (σ 0) (σ 1) u c b = (((1 - u : ℝ) : ℂ))⁻¹ := by
    rw [h10]; exact hcol (σ 0)
  have hΘ : ∀ a' b' : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u a' b' -
      (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (((1 - u : ℝ) : ℂ))⁻¹‖ ≤
      C₈ * A * (sz.lam n ^ 2)⁻¹ * iniTermII_PD d (sz.L n) (b' - a') := by
    intro a' b'
    rw [h10]
    exact IniTermIIGen_cross_inv (u := u) hC₈.le (iniTermII_PD_nonneg _) (hR1 n) hg (hzero (σ 0) a' b')
  have hfun : Step2Gen_UN (mk sz z) n σ s u X = fun a' : Fin 2 → Zd d (sz.L n) => ∑ b₁ : Zd d (sz.L n), ∑ b₂ : Zd d (sz.L n),
      ((if a' 0 = b₁ then (α : ℂ) else 0) + (β : ℂ) * STThg (mk sz z) n (σ 0) (σ 1) u (a' 0) b₁) *
        ((if a' 1 = b₂ then (α : ℂ) else 0) + (β : ℂ) * STThg (mk sz z) n (σ 0) (σ 1) u (a' 1) b₂) * X ![b₁, b₂] := by
    funext a'
    exact hrep X a'
  rw [hfun, IniTermIIGen_zms_rep (STThg (mk sz z) n (σ 0) (σ 1) u) hcol' hαβ X a]
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d (sz.L n), ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  exact Hb (sz.L n) (sz.three_le_L n) (sz.lam n) s u α β M (lam * (W ^ d)⁻¹) (W ^ (-D)) hlamn hs hsu hu hreg hα0 hα1 hβ0
    hβ1 hαβ hM hq hF (STThg (mk sz z) n (σ 0) (σ 1) u)
    (hAL sz (mk sz z) (gK sz z) hdec hR1 n (hU n) (σ 0) (σ 1) s u hg hgΛ hs hsu hu hreg)
    (fun a' => IniTermIIGen_row_le (mk sz z) n (hU n) (σ 0) (σ 1) hu0 hu a' ((hdec n hg hgΛ (σ 0) (σ 1) u hu0 hu).2 a')) hΘ (a 0) (a 1)
    (fun b₁ b₂ => X ![b₁, b₂]) hX'

/-- **Target 2, `σ₁ = σ₂`: the short-range initial term** (`3_5:2253`, `(prop:ThfadC_short)`; no zero-mode removal; band
`iniTermII_core_same`, `IniTermII:1378`) over the carrier: `|[𝒰_{s,u,σ} X]_a| ≤ C M ((λ W^{-d}) 𝒯_u(|a₁-a₂|) + W^{-D})`.
The short-range field is read at `gK`, `gK² ≤ lam²` (R1) turns it into the band shape at `g = sz.lam`, `g ≤ A 𝔡⁻¹`. -/
theorem iniTermIIGen_core_same (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) (κ 𝔡 : ℝ) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z → ∀ n : ℕ, 0 < gK sz z n →
      gK sz z n ≤ 𝔡⁻¹ → ∀ (W D s u M lam : ℝ), 0 < W → 0 ≤ s → s ≤ u → u < 1 →
        1 - s ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 → 0 ≤ M → 0 ≤ lam →
        ∀ σ : Fin 2 → Bool, σ 0 = σ 1 → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
            W ^ (-D))) →
          ∀ a, ‖Step2Gen_UN (mk sz z) n σ s u X a‖ ≤
            C * M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) + W ^ (-D)) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, hC₆, hC₈, hCs, hc₀, hA, H⟩ := hKF hd κ 𝔡 hκ h𝔡
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 h𝔡
  obtain ⟨C, hC, Hb⟩ := iniTermII_bil_same d hd Cs c₀ (A * 𝔡⁻¹) hCs.le hc₀
  refine ⟨C, hC, ?_⟩
  intro sz ε 𝔠 z hflow n hg hgΛ W D s u M lam hW hs hsu hu hreg hM hlam σ hσ X hX a
  obtain ⟨hU, hdec, hR1, hE1, hG⟩ := H sz ε 𝔠 z hflow
  have hu0 : 0 ≤ u := hs.trans hsu
  obtain ⟨hlamn, hgl⟩ := Step5KerGen_cmp_pos (hR1 n) hg
  have hlamΛ : sz.lam n ≤ A * 𝔡⁻¹ := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : gK sz z n ^ 2 ≤ (𝔡⁻¹) ^ 2 := by nlinarith
    have h2 := (hR1 n).2.2
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hΛ.le]
  obtain ⟨α, β, hα0, hα1, hβ0, hβ1, hαβ, hrep⟩ := IniTermIIGen_UN_rep (mk sz z) n (hU n)
    (σ := σ) (fun v _ _ => by rw [hσ]) hs hsu hu
  obtain ⟨-, -, hshort⟩ := hG n hg hgΛ u hu0 hu
  have hΘ : ∀ a' b' : Zd d (sz.L n), ‖STThg (mk sz z) n (σ 0) (σ 1) u a' b'‖ ≤
      Cs * ((if a' = b' then 1 else 0) + sz.lam n ^ 2 * Real.exp (-(c₀ * ((zdistD d (sz.L n) (b' - a') : ℕ) : ℝ)))) := by
    intro a' b'
    rw [← hσ]
    refine (hshort (σ 0) a' b').trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hCs.le
    exact mul_le_mul_of_nonneg_right (hR1 n).2.1 (Real.exp_pos _).le
  have hq : 0 ≤ lam * (W ^ d)⁻¹ := by positivity
  have hF : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  have hX' : ∀ b₁ b₂ : Zd d (sz.L n), ‖X ![b₁, b₂]‖ ≤
      M * (lam * (W ^ d)⁻¹ * tailT d (sz.L n) (sz.lam n) s (zdistInf d (sz.L n) (b₁ - b₂) : ℕ) + W ^ (-D)) := fun b₁ b₂ => by
    simpa using hX ![b₁, b₂]
  rw [hrep X a]
  exact Hb (sz.L n) (sz.three_le_L n) (sz.lam n) s u α β M (lam * (W ^ d)⁻¹) (W ^ (-D)) hlamn hlamΛ hsu hu hreg hα0 hα1 hβ0
    (by linarith) hM hq hF (STThg (mk sz z) n (σ 0) (σ 1) u) hΘ (a 0) (a 1) (fun b₁ b₂ => X ![b₁, b₂]) hX'

end Cores


/-! ## 5′. The `Prec` lift of target 3 -/

/-- **The `Prec` lift** (target 3; band `iniTermII_lift`, `IniTermII:1567`): the deterministic core, for
`X = (𝓛-𝒦)^{(2)}_{s,σ}` bounded by the `STDecay` profile `N^{τ/2} (λ W^{-d} 𝒯_s + W^{-D'})`, `D' = D + 1/𝔠`, gives
`STIniTermConclgL` (the union over `(σ, b)` of the premise contains the union over `(u, σ, a)` of the conclusion; the constant
`CC ≤ N^{τ/2}` eventually, `ρ = (1-s)/(1-u) ≤ N ≤ W^{1/𝔠}`; `u` enters only through the kernel). -/
private theorem IniTermIIGen_lift {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ}
    {Q : Finset (Fin 2)} {P : (Fin 2 → Bool) → Prop} {Λ 𝔠 CC : ℝ} (hsz : sz.SizeTendsto) (h𝔠 : 0 < 𝔠)
    (hBand : sz.Bandwidth 𝔠) (hC : 0 < CC) (hlamΛ : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (ht1 : ∀ n, t n < 1) (hR : STReg5II sz s t)
    (hcore : ∀ n : ℕ, 0 < sz.lam n → sz.lam n ≤ Λ → ∀ u : ℝ, s n ≤ u → u ≤ t n → ∀ σ : Fin 2 → Bool, P σ →
        ∀ M D' : ℝ, 0 ≤ M → ∀ X : (Fin 2 → Zd d (sz.L n)) → ℂ,
          (∀ b, ‖X b‖ ≤ M * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) + ((sz.W n : ℕ) : ℝ) ^ (-D'))) →
          ∀ a, ‖zeroModeSet d (sz.L n) Q (Step2Gen_UN C n σ (s n) u X) a‖ ≤
            CC * M * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ) +
              (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-D')))
    (hDec : STDecaygL C μ s) : STIniTermConclgL C μ Q P s t := by
  intro D hD
  have hD' : 0 < D + 1 / 𝔠 := by positivity
  have hP := hDec (D + 1 / 𝔠) hD'
  unfold PrecL at hP ⊢
  refine iniTermII_of_subset hP ?_
  intro τ hτ
  refine ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hlamΛ, (tendsto_size sz hsz).eventually (eventually_le_rpow (2 * CC) (half_pos hτ)), hBand]
    with n hn hCn hBn
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  by_contra hq
  have hq' : ∀ q : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      ‖C.L n (s n) q.1 q.2 ω - C.K n (s n) q.1 q.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
          STWB sz n (s n) (zdistInf d (sz.L n) (q.2 0 - q.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (q.2 0 - q.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) := fun q => not_lt.mp fun h => hq ⟨q, h⟩
  obtain ⟨⟨u, hu1, hu2⟩, ⟨σ, hσ⟩, a⟩ := p
  obtain ⟨hlamn, hlamΛ'⟩ := hn
  have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
  have hs1 : s n < 1 := lt_of_le_of_lt hu1 hu1'
  obtain ⟨hlowt, hregs⟩ := hR n
  have hlows : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - s n := hlowt.trans (by linarith)
  have hlowu : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u := hlowt.trans (by linarith)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hτ0 : 0 < τ := hτ
  set K : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hK
  have hK0 : 0 ≤ K := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hKK : K * K = ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ0
  have hXb : ∀ b : Fin 2 → Zd d (sz.L n), ‖C.L n (s n) σ b ω - C.K n (s n) σ b‖ ≤
      K * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailT d (sz.L n) (sz.lam n) (s n) (zdistInf d (sz.L n) (b 0 - b 1) : ℕ) +
        ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) := fun b => by
    have h := hq' (σ, b)
    rw [iniTermII_prem_eq sz n (s n) (D + 1 / 𝔠) b] at h
    exact h
  have hcb := hcore n hlamn hlamΛ' u hu1 hu2 σ hσ K (D + 1 / 𝔠) hK0
    (fun b => C.L n (s n) σ b ω - C.K n (s n) σ b) hXb a
  -- `ρ W^{-D'} ≤ W^{-D}`
  have hρN := iniTermII_rho_le sz n hlamn hu1' hregs hlowu
  have hNW := iniTermII_N_le_W sz n h𝔠 hBn
  have hρF : (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    calc (1 - s n) / (1 - u) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))
        ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠)) :=
          mul_le_mul_of_nonneg_right (hρN.trans hNW) (Real.rpow_nonneg hW.le _)
      _ = ((sz.W n : ℕ) : ℝ) ^ (-D) := by
          rw [← Real.rpow_add hW]; congr 1; ring
  have hfin := iniTermII_arith (C := CC) (K := K) (lam' := (sz.Bctl n (s n)) ^ (1 / 5 : ℝ))
    (a := (STAI sz n) ^ (-(1 / 5 : ℝ))) (w := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹)
    (T := tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1) : ℕ))
    (Tp := sz.STprof n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (ρ := (1 - s n) / (1 - u)) (F := ((sz.W n : ℕ) : ℝ) ^ (-(D + 1 / 𝔠))) (WD := ((sz.W n : ℕ) : ℝ) ^ (-D))
    hC.le hCn (iniTermII_lam_le sz n hlamn hs1 hlows) (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
    (by positivity) (tailT_nonneg (Nat.cast_nonneg _)) (iniTermII_prof_ge sz n u D a) hρF
    (Real.rpow_nonneg hW.le _)
  have hp' : ((sz.size n : ℕ) : ℝ) ^ τ * ((STAI sz n) ^ (-(1 / 5 : ℝ)) *
      sz.STprof n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) + ((sz.W n : ℕ) : ℝ) ^ (-D)) <
      ‖zeroModeSet d (sz.L n) Q (Step2Gen_UN C n σ (s n) u
        (fun b => C.L n (s n) σ b ω - C.K n (s n) σ b)) a‖ := hp
  rw [← hKK] at hp'
  exact absurd (hcb.trans hfin) (not_le.mpr hp')

/-- The guard (g) (UBA-C1, DECISIONS §273 (1)): from R1 at one index, `0 < l` gives `0 < g`. -/
theorem IniTermIIGen_cmp_pos' {g l A : ℝ} (h : 0 ≤ g * l ∧ g ^ 2 ≤ l ^ 2 ∧ l ^ 2 ≤ A * g ^ 2) (hl : 0 < l) :
    0 < g := by
  obtain ⟨h1, -, h3⟩ := h
  rcases lt_trichotomy g 0 with hg | hg | hg
  · nlinarith [mul_pos hl (neg_pos.2 hg)]
  · subst hg; nlinarith
  · exact hg

/-- **Target 3, the `Prec` lift of the initial terms of case (ii)**, from `STDecaygL` at `s` (`(Eq:Gdecay+IND)`), the
flow facts (admissibility, `T0 < 1`), the class at `(κ, 𝔡)` and the regime `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²`
(`STReg5II`): the initial term of `(zYU2)` obeys `≺ A^{-1/5} W^{-d}𝒯̃^L_{u,D}(|a₁-a₂|) + W^{-D}`, uniformly in `u ∈ [s,t]`, for
`σ₁ ≠ σ₂` with `Q^{(1)}` and for `σ₁ = σ₂` without (band `iniTermII_concl`, `IniTermII:1664`). -/
theorem iniTermIIGen_concl (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (hF : Step5CasesGen_FlowFacts d Flow mk T0)
    (hKF : IniTermGen_KerFacts d Flow mk gK) (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (ht : ∀ n, t n ≤ T0 sz z n)
    (hR : STReg5II sz s t) (hDec : STDecaygL (mk sz z) (law sz) s) :
    STIniTermConclgL (mk sz z) (law sz) {0} STSigMixed s t ∧ STIniTermConclgL (mk sz z) (law sz) ∅ STSigSame s t := by
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨⟨h𝔠, h𝔡, hsz, hBand, hWO⟩, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.mpr h𝔡
  have hlamΛ : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n h1 h2
    exact ⟨h2.1, h1.2⟩
  obtain ⟨Cm, hCm, Hm⟩ := iniTermIIGen_core d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨Cs, hCs, Hs⟩ := iniTermIIGen_core_same d Flow mk gK hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨C₆, C₈, Cs', c₀, A, hC₆, hC₈, hCs', hc₀, hA, H⟩ := hKF hd κ 𝔡 hκ h𝔡
  obtain ⟨-, -, hR1, -, -⟩ := H sz ε 𝔠 z hflow
  have hguard : ∀ n, 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → 0 < gK sz z n ∧ gK sz z n ≤ 𝔡⁻¹ := fun n hg hgΛ =>
    have hgK := IniTermIIGen_cmp_pos' (hR1 n) hg
    ⟨hgK, (Step5KerGen_cmp_pos (hR1 n) hgK).2.trans hgΛ⟩
  refine ⟨?_, ?_⟩
  · refine IniTermIIGen_lift sz (mk sz z) (law sz) hsz h𝔠 hBand hCm hlamΛ ht1 hR ?_ hDec
    intro n hg hgΛ u hu1 hu2 σ hσ M D' hM X hX a
    have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    obtain ⟨hgK, hgKΛ⟩ := hguard n hg hgΛ
    exact Hm sz ε 𝔠 z hflow n hgK hgKΛ ((sz.W n : ℕ) : ℝ) D' (s n) u M ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) hW (hs0 n) hu1 hu1'
      (hR n).2 hM (Real.rpow_nonneg (st_Bctl_pos sz (lt_of_le_of_lt hu1 hu1')).le _) σ hσ X hX a
  · refine IniTermIIGen_lift sz (mk sz z) (law sz) hsz h𝔠 hBand hCs hlamΛ ht1 hR ?_ hDec
    intro n hg hgΛ u hu1 hu2 σ hσ M D' hM X hX a
    have hu1' : u < 1 := lt_of_le_of_lt hu2 (ht1 n)
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    obtain ⟨hgK, hgKΛ⟩ := hguard n hg hgΛ
    have h := Hs sz ε 𝔠 z hflow n hgK hgKΛ ((sz.W n : ℕ) : ℝ) D' (s n) u M ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) hW (hs0 n) hu1
      hu1' (hR n).2 hM (Real.rpow_nonneg (st_Bctl_pos sz (lt_of_le_of_lt hu1 hu1')).le _) σ hσ X hX a
    rw [st5_zeroModeSet_empty]
    refine h.trans ?_
    have hu0 : 0 < 1 - u := by linarith
    have hρ : 1 ≤ (1 - s n) / (1 - u) := (one_le_div hu0).mpr (by linarith)
    have hF : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hW.le _
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (mul_nonneg hCs.le hM)
    exact le_mul_of_one_le_left hF hρ

/-! ## 6. Target 4: the pin `stIniTermIIgL_of` -/

/-- **Target 4, the pin `stIniTermIIgL_of`** (band `stIniTermII_holds`, `IniTermII:1718`): the initial terms of case (ii) over a
carrier tuple, for every law, from the flow facts and the kernel facts. -/
theorem stIniTermIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 → IniTermGen_KerFacts d Flow mk gK → STIniTermIIgL d law Flow mk T0 := by
  intro hF hKF hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR _ _ _ hDec _ _ _ _ _ _
  exact iniTermIIGen_concl d law Flow mk T0 gK hF hKF hd hκ sz hflow hs0 ht hR hDec


/-! ## 7. Band re-derivation and compiled nonempty instances (target 10; `d = 3`, `szB`, `zB`) -/

/-- **Target 4 at the band** (re-derivation of `stIniTermII_holds`, `IniTermII:1718`): the generic pin at the band tuple
`(seqP, STFlow, bandFM ∘ STflowE, lemT)`, `gK = sz.lam`, through `STIniTermII_iff_gL`. -/
theorem iniTermIIGen_band_holds (d : ℕ) : STIniTermII d :=
  (STIniTermII_iff_gL d).2 (stIniTermIIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (step5CasesGen_flowFacts_band d)
    (iniTermGen_kerFacts_band d))

section Inst

open RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **Target 1 at `(szB, zB)`** (`L = 4`, `W_n = n + 4`, `lam = 1`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`): the five conjuncts at the merged
flow; `n = 0`, `σ = +`, `t = 1/2`, `a = b = 0` (column sum `2`); guard `0 < lam 0 = 1 ≤ 10 = 𝔡⁻¹`. -/
example : ∃ C₆ C₈ Cs c₀ A : ℝ, 0 < C₆ ∧ 0 < C₈ ∧ 0 < Cs ∧ 0 < c₀ ∧ 1 ≤ A ∧
    (∀ n, Step2Gen_USemigroup (bandFM szB (STflowE zB)) n) ∧
    Step5KerGen_ThDecay (bandFM szB (STflowE zB)) szB.lam (1 / 10 : ℝ)⁻¹ C₆ ∧
    (∀ n, 0 ≤ szB.lam n * szB.lam n ∧ szB.lam n ^ 2 ≤ szB.lam n ^ 2 ∧ szB.lam n ^ 2 ≤ A * szB.lam n ^ 2) ∧
    (∀ (n : ℕ) (t : ℝ), 0 ≤ t → t < 1 → ∀ σ : Bool, STThg (bandFM szB (STflowE zB)) n σ (!σ) t =
      STThg (bandFM szB (STflowE zB)) n (!σ) σ t) ∧
    ∑ a : Zd 3 (szB.L 0), STThg (bandFM szB (STflowE zB)) 0 true false (1 / 2) a 0 = 2 ∧
    ‖STThg (bandFM szB (STflowE zB)) 0 true false (1 / 2) 0 0 - (((szB.L 0 : ℕ) : ℂ) ^ 3)⁻¹ * (((1 - 1 / 2 : ℝ) : ℂ))⁻¹‖ ≤
      C₈ * (szB.lam 0 ^ 2 + |1 - 1 / 2|)⁻¹ * ((((zdistD 3 (szB.L 0) (0 - 0) : ℕ) : ℝ) + 1) ^ (3 - 2))⁻¹ ∧
    ‖STThg (bandFM szB (STflowE zB)) 0 true true (1 / 2) 0 0‖ ≤
      Cs * ((if (0 : Zd 3 (szB.L 0)) = 0 then (1 : ℝ) else 0) +
        szB.lam 0 ^ 2 * Real.exp (-(c₀ * ((zdistD 3 (szB.L 0) (0 - 0) : ℕ) : ℝ)))) := by
  obtain ⟨C₆, C₈, Cs, c₀, A, h1, h2, h3, h4, h5, H⟩ :=
    iniTermGen_kerFacts_band 3 le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  obtain ⟨hU, hD, hR, hE1, hG⟩ := H szB (1 / 10) (1 / 6) zB flow_zB
  obtain ⟨hc, hz, hs⟩ := hG 0 (by simp [szB]) (by norm_num [szB]) (1 / 2) (by norm_num) (by norm_num)
  refine ⟨C₆, C₈, Cs, c₀, A, h1, h2, h3, h4, h5, hU, hD, hR, hE1, ?_, hz true 0 0, hs true 0 0⟩
  have h2 : (((1 - 1 / 2 : ℝ) : ℂ))⁻¹ = 2 := by push_cast; norm_num
  have h := hc true 0
  rw [h2] at h
  exact h

/-- **Target 2 (`σ₁ ≠ σ₂`) at `(szB, zB)`**, `n = 0`, `W = D = 2`, `(s, u) = (15/16, 31/32)` (`1 - s = lam²/L²`, the boundary of
regime (ii)), `M = lam = 1`, `σ = (+,-)`, the nonzero tensor `X_b = W^{-d} 𝒯_s(|b₁-b₂|) + W^{-D}` (the `STDecay` profile at `s`
attained): every hypothesis of `iniTermIIGen_core` is discharged (flow `flow_zB`, guard `0 < lam 0 = 1 ≤ 10`, regime, profile);
the class is `iniTermGen_kerFacts_band`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 (szB.L 0),
    ‖zeroModeSet 3 (szB.L 0) {0} (Step2Gen_UN (bandFM szB (STflowE zB)) 0 ![true, false] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L 0) (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ))) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (31 / 32) (zdistInf 3 (szB.L 0) (a 0 - a 1) : ℕ) +
        (1 - 15 / 16) / (1 - 31 / 32) * (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermIIGen_core 3 (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
    (fun sz _ => sz.lam) (iniTermGen_kerFacts_band 3) le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun a => H szB (1 / 10) (1 / 6) zB flow_zB 0 (by simp [szB]) (by norm_num [szB]) 2 2 (15 / 16) (31 / 32)
    1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [szB]; norm_num) (by norm_num) (by norm_num)
    ![true, false] (by simp) _ ?_ a⟩
  intro b
  have h0 : 0 ≤ (1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L 0) (b 0 - b 1) : ℕ)
      + (2 : ℝ) ^ (-(2 : ℝ)) := by
    have := tailT_nonneg (d := 3) (L := szB.L 0) (g := szB.lam 0) (t := 15 / 16) (Nat.cast_nonneg (zdistInf 3 (szB.L 0) (b 0 - b 1)))
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_of_eq (by ring)

/-- **Target 2 (`σ₁ = σ₂`) at `(szB, zB)`**: the same data with `σ = (+,+)`. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 (szB.L 0),
    ‖Step2Gen_UN (bandFM szB (STflowE zB)) 0 ![true, true] (15 / 16) (31 / 32)
      (fun b => (((1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L 0) (b 0 - b 1) : ℕ)
        + (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ)) a‖ ≤
      C * 1 * (1 * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (31 / 32) (zdistInf 3 (szB.L 0) (a 0 - a 1) : ℕ) +
        (2 : ℝ) ^ (-(2 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := iniTermIIGen_core_same 3 (fun sz κ ε 𝔠 𝔡 z => sz.STFlow κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
    (fun sz _ => sz.lam) (iniTermGen_kerFacts_band 3) le_rfl (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  refine ⟨C, hC, fun a => H szB (1 / 10) (1 / 6) zB flow_zB 0 (by simp [szB]) (by norm_num [szB]) 2 2 (15 / 16) (31 / 32)
    1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by simp [szB]; norm_num) (by norm_num) (by norm_num)
    ![true, true] (by simp) _ ?_ a⟩
  intro b
  have h0 : 0 ≤ (1 : ℝ) * ((2 : ℝ) ^ 3)⁻¹ * tailT 3 (szB.L 0) (szB.lam 0) (15 / 16) (zdistInf 3 (szB.L 0) (b 0 - b 1) : ℕ)
      + (2 : ℝ) ^ (-(2 : ℝ)) := by
    have := tailT_nonneg (d := 3) (L := szB.L 0) (g := szB.lam 0) (t := 15 / 16) (Nat.cast_nonneg (zdistInf 3 (szB.L 0) (b 0 - b 1)))
    positivity
  rw [Complex.norm_real, Real.norm_of_nonneg h0]
  exact le_of_eq (by ring)

/-- **Target 3 at `(szB, zB, 15/16, 31/32)`** (the merged data of `inst_iniTermII`): `1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`; the
stochastic premise `STDecaygL` at `s` is another gate's pin and stays a hypothesis. -/
example (hDec : STDecaygL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16)) :
    STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) {0} STSigMixed (fun _ => 15 / 16) (fun _ => 31 / 32) ∧
      STIniTermConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) ∅ STSigSame (fun _ => 15 / 16) (fun _ => 31 / 32) :=
  iniTermIIGen_concl 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz _ => sz.lam) (step5CasesGen_flowFacts_band 3)
    (iniTermGen_kerFacts_band 3) le_rfl (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) szB flow_zB
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_reg5II hDec

/-- **Target 4 at the band**: the generic pin `stIniTermIIgL_of`, applied to the band tuple, gives the instance of `Step5Pins`
(`inst_iniTermII`) at `(szB, zB, 15/16, 31/32)` for every `Cd > 0`; the two hypotheses of the pin are discharged by the band
results. -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
      szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_iniTermII ((STIniTermII_iff_gL 3).2 (stIniTermIIgL_of 3 (fun sz => Sizes.seqP sz)
    (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
    (fun sz _ => sz.lam) (step5CasesGen_flowFacts_band 3) (iniTermGen_kerFacts_band 3))) Cd hCd

/-- **Target 4, band re-derivation, instantiated**: `iniTermIIGen_band_holds` gives the instance of `Step5Pins` at
`(szB, zB, 15/16, 31/32)` with the pin proved (as `inst_iniTermII_proved`, `IniTermII:1799`). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)
      szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_iniTermII (iniTermIIGen_band_holds 3) Cd hCd

end Inst

end RBM.BA

end
