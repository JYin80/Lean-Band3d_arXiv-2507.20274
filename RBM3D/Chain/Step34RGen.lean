/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.IterationsGen
import RBM3D.Chain.IterationsGen2
import RBM3D.Chain.NQEndFlowGen
import RBM3D.Chain.QtXiRoundLiftGen
import RBM3D.Chain.QtNonzeroBootGen
import RBM3D.Induction.Step3
import RBM3D.Induction.Step4
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.MainIndRegimes

/-!
# Steps 3-4 of `lem:main_ind` over a carrier family (U3-BA (b), file 1; ticket T2509)

Generic forms of `Induction/Step3.lean` §1-§4 and `Induction/Step4.lean` §1-§2 (neither is edited) over a carrier family
`(law, Flow, mkM, Hf, Es, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper: arXiv:2507.20274, Step 3 `1_2:1359-1366`, proof
`3_5:1366-1431` (regime (iii): `3_5:1384`; regime (i): `3_5:1407-1431`) and `3_5:1572-1601` (case (ii)); Step 4 `1_2:1370-1374`, proof
`3_5:1602-1614`.  No new mathematics: the skeletons are the band proofs with `Prec sz` read as `PrecL sz μ`, `STXiL sz n (E n)` as
`STXiLg C n`, the band `η` as `C.eta n` (the ratio `η_s/η_u = (1-s)/(1-u)` is `IterationsGen_eta_ratio`).

* **Targets 1-3** `stStep3RegIIIgL_of`, `stStep3RegIgL_of`, `stStep3IIgL_of`: `STStep3RgL` at `STReg5III`, `STReg5I`, `STCaseII` from the family
  bundle `IterationsGen2_Fam` (and, for (i), (ii), the bootstrap `STOeqQtgL'`/`STOeqQtNZgL'` and `lem:iterations` `STIterationsgL'`/`STIterationsIIgL'`).
* **Targets 4-5** `stStep4RgL_of_ing`, `stStep34RgL_mono`: `STStep4RgL` from the ingredient pin `STIngRgL d R .. STXiBootgL'`; both pins are
  monotone along the regime.
* **Band re-derivations** (namespace `Step34RGenCheck`): the band `stStep3RegIII_holds`, `stStep3RegI_holds`, `stStep3II_holds`, `stStep4I_holds`,
  `stStep4II_holds` re-derived from 1-4 through the band bridges of `Chain/Step34Gen`, `IterationsGen2_famBand`, `stOeqQtgL'_band`,
  `stOeqQtNZgL'_band`, and compiled nonempty instances at `d = 3`.

The constants `𝔠d` are those of the band proofs (`1/100` at regime (iii); the minimum of the two input pins' constants at (i), (ii); the bootstrap's at Step 4).  Private helpers carry the stem `Step34RGen_`; the model-free band helpers
`step3_xB`, `step3_psi0_le` (size-level), `iterationsB_K_pairsg`, `IterationsGen_Ep` are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private step3_xB step3_psi0_le from RBM3D.Induction.Step3

open private iterationsB_K_pairsg from RBM3D.Chain.IterationsGen2

open private IterationsGen_Ep from RBM3D.Chain.IterationsGen

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ} {sz : Sizes d} {μ : Measure sz.SeqΩ}

/-! ## 1. The skeleton of Step 3 (band `step3_finish`, `step3_skeleton`) -/

/-- The last step of the skeleton, for a control `Z` of `Ξ̂^{(𝓛-𝒦)}_k`: `Ξ̂^{(𝓛-𝒦)}_{v,k} ≺ Z`, `W^{-d}B_{v,0} Z ≤ c` and `(rela_XILXILK)`
(`3_5:1387`) give `Ξ̂^{(𝓛)}_{v,k} ≺ 1 + B Z ≲ 1`, i.e. `(Eq:LGxb)` at the loop length `k` (band `step3_finish`, `Step3:102`). -/
private theorem Step34RGen_finish (C : FlowFM sz) {s t Z : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop)
    (ht1 : ∀ n, t n < 1) {k : ℕ}
    (hX : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg C n q.1.1 k ω) (fun n _ _ => Z n))
    (hBZ : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, sz.Bctl n (v : ℝ) * Z n ≤ c)
    (hrela : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg C n q.1.1 k ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg C n q.1.1 k ω)) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖) (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1)) := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  let ψ : ∀ n, TimeIcc s t n → STPair s t n := fun n v => ⟨((v : ℝ), (v : ℝ)), (v.2).1, le_rfl, (v.2).2⟩
  have hBpos : ∀ n (v : TimeIcc s t n), 0 < sz.Bctl n (v : ℝ) := fun n v =>
    st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))
  obtain ⟨cB, hcB0, hcB⟩ := hBZ
  have hB0 : ∀ n (q : STPair s t n), 0 ≤ sz.Bctl n q.1.1 := fun n q => (hBpos n (φ n q)).le
  have h4 : PrecL sz μ (U := STPair s t) (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg C n q.1.1 k ω)
      (fun n q _ => 1 + sz.Bctl n q.1.1 * Z n) := by
    have hm := StochDomAt.mul (P := μ) (size := sz.size)
      (ξ₁ := fun n (q : STPair s t n) (_ : sz.SeqΩ) => sz.Bctl n q.1.1)
      (ξ₂ := fun n q ω => STXiLKg C n q.1.1 k ω)
      (ζ₁ := fun n (q : STPair s t n) (_ : sz.SeqΩ) => sz.Bctl n q.1.1)
      (ζ₂ := fun n q _ => Z n) hsize
      (fun n q ω => zero_le_one.trans (st_one_le_XiLKg C k ω (hBpos n (φ n q)))) (fun n q _ => hB0 n q)
      (StochDomAt.refl hsize (fun n q _ => hB0 n q)) hX
    have h1 := StochDomAt.refl (P := μ) (size := sz.size) (U := STPair s t)
      (ζ := fun _ _ _ => (1 : ℝ)) hsize (fun _ _ _ => zero_le_one)
    exact StochDomAt.add hsize h1 hm
  have hc1 : PrecL sz μ (U := STPair s t) (fun n q ω => (1 + cB) * (1 : ℝ)) (fun _ _ _ => 1) :=
    StochDomAt.const_mul_left hsize (by linarith) (fun _ _ _ => zero_le_one)
      (StochDomAt.refl hsize (fun _ _ _ => zero_le_one))
  have h6 : PrecL sz μ (U := STPair s t) (fun n q _ => 1 + sz.Bctl n q.1.1 * Z n) (fun _ _ _ => 1) := by
    refine StochDomAt.of_subset hc1 fun τ hτ => ⟨τ, hτ, ?_⟩
    filter_upwards [hcB] with n hn ω hω
    obtain ⟨q, hq⟩ := hω
    refine ⟨q, lt_of_lt_of_le hq ?_⟩
    have := hn (φ n q)
    change 1 + sz.Bctl n q.1.1 * Z n ≤ (1 + cB) * 1
    linarith
  have h7 : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg C n q.1.1 k ω) (fun _ _ _ => 1) :=
    StochDomAt.trans hsize hrela (StochDomAt.trans hsize h4 h6)
  exact st_prec_of_xig (U := fun n => TimeIcc s t n) (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n v p ω => ‖C.L n (v : ℝ) p.1 p.2 ω‖) (fun n v => (sz.Bctl n (v : ℝ)) ^ (k - 1))
    (fun n v => pow_pos (hBpos n v) _) (StochDomAt.precomp_param h7 ψ)

/-- **Step 3 from `lem:iterations`, both cases** (band `step3_skeleton`, `Step3:153`; `3_5:1422-1431` with `A = ilambda² W^d`, `3_5:1575-1595` with
`A = (W^{-d}B_{s,0})⁻¹`), for every loop length `k ≥ 1`. -/
private theorem Step34RGen_skeleton (C : FlowFM sz) {s t A : ℕ → ℝ} (hsize : Tendsto sz.size atTop atTop)
    (hA : ∀ n, 0 ≤ A n) (hA1 : ∀ᶠ n in atTop, 1 ≤ A n) (ht1 : ∀ n, t n < 1)
    (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL C μ s t A r k) →
      (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL C μ s t A r (k - 1)) → STIterHypgL C μ s t A n_ k)
    (hbase : ∀ r, 2 ≤ r → STIterHypgL C μ s t A r 0)
    (hscale : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (A n) (C.eta n (s n) / C.eta n q.1.2) r k ≤ c * A n ^ (3 / 4 : ℝ))
    (hBA : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) ≤ c)
    (havg : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg C n q.1.1 1 ω) (fun _ _ _ => 1))
    (hrela : ∀ r, 1 ≤ r → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg C n q.1.1 r ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLKg C n q.1.1 r ω)) :
    STLmaxUgL C μ s t := by
  intro k hk
  by_cases hk1 : k = 1
  · subst hk1
    obtain ⟨cB, hcB0, hcB⟩ := hBA
    refine Step34RGen_finish C (Z := fun _ => (1 : ℝ)) hsize ht1 havg ⟨cB, hcB0, ?_⟩ (hrela 1 le_rfl)
    filter_upwards [hcB, hA1] with n hn hA1n v
    have h34 : 1 ≤ A n ^ (3 / 4 : ℝ) := Real.one_le_rpow hA1n (by norm_num)
    have hBv : 0 ≤ sz.Bctl n (v : ℝ) := (st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))).le
    calc sz.Bctl n (v : ℝ) * 1 ≤ sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h34 hBv
      _ ≤ cB := hn v
  · have hk2 : 2 ≤ k := by omega
    have hall := st_iterate (S := fun r l => STIterHypgL C μ s t A r l) hbase hIter
    obtain ⟨kk, c, hc, hΨ⟩ := hscale k hk2
    have hAA : ∀ n (q : STPair s t n), 0 ≤ A n ^ (3 / 4 : ℝ) := fun n q => Real.rpow_nonneg (hA n) _
    have h2 : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg C n q.1.1 k ω)
        (fun n q _ => c * A n ^ (3 / 4 : ℝ)) := by
      refine StochDomAt.of_subset (hall kk k hk2) fun τ hτ => ⟨τ, hτ, ?_⟩
      filter_upwards [hΨ] with n hn ω hω
      obtain ⟨q, hq⟩ := hω
      refine ⟨q, lt_of_le_of_lt ?_ hq⟩
      exact mul_le_mul_of_nonneg_left (hn q) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have h3 : PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg C n q.1.1 k ω)
        (fun n q _ => A n ^ (3 / 4 : ℝ)) :=
      StochDomAt.trans hsize h2
        (StochDomAt.const_mul_left hsize hc.le (fun n q _ => hAA n q)
          (StochDomAt.refl hsize (fun n q _ => hAA n q)))
    exact Step34RGen_finish C (Z := fun n => A n ^ (3 / 4 : ℝ)) hsize ht1 h3 hBA (hrela k hk)

/-- **The a priori level `l = 0` of `(eq:iteration_induc)`** (`3_5:1391`; band `step3_hbase`, `Step3:217`): `Ξ̂^{(𝓛-𝒦)}_{v,r} ≤ 1 + cv A (Ξ̂^{(𝓛)}_{v,r} +
(1 + max|𝒦|/B^{r-1}))`, `Ξ̂^{(𝓛)} ≺ ρ^{r-1}` (`(lRB1)`) and `max|𝒦|/B^{r-1} ≺ 1` (`(eq:bcal_k)`), so `≺ 1 + cv A (ρ^{r-1} + 1) ≤ (1 + 2 cv) Ψ(r,0)`. -/
private theorem Step34RGen_hbase (hsize : Tendsto sz.size atTop atTop) {Cf : FlowFM sz} {s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScaleg Cf s t A T cB cv K)
    (hapri : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
      (fun n q _ => (Cf.eta n (s n) / Cf.eta n q.1.2) ^ (m - 1)))
    (hK : ∀ m, 1 ≤ m → PrecL sz μ (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖Cf.K n p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)))
    {r : ℕ} (hr : 1 ≤ r) :
    STIterHypgL Cf μ s t A r 0 := by
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (hS.t_lt_one n))
  have hY := st_prec_one_add_supg hsize (U := STPair s t)
    (V := fun n => (Fin r → Bool) × (Fin r → Zd d (sz.L n)))
    (fun n q p ω => ‖Cf.K n q.1.1 p.1 p.2‖) (fun n q => sz.Bctl n q.1.1 ^ (r - 1))
    (fun n q => pow_pos (hBpos n q) _) (hK r hr)
  have hXY := StochDomAt.add hsize (hapri r hr) hY
  have hcv0 : 0 ≤ cv := by linarith [hS.one_le_cv]
  have hnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ),
      0 ≤ STXiLg Cf n q.1.1 r ω + (1 + Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖) /
          sz.Bctl n q.1.1 ^ (r - 1)) := fun n q ω => by
    have h1 := st_one_le_XiLg Cf (n := n) (v := q.1.1) r ω (hBpos n q)
    have h2 : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖) :=
      le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖Cf.K n q.1.1 p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
    have h3 := div_nonneg h2 (pow_pos (hBpos n q) (r - 1)).le
    linarith
  have hone := iterationsA_prec_one_add_mulg hsize (U := STPair s t)
    (c := fun n _ => cv * A n) (fun n _ => mul_nonneg hcv0 (hS.A_nonneg n)) hnn hXY
  have hΨ : PrecL sz μ (U := STPair s t)
      (fun n q ω => 1 + cv * A n * (STXiLg Cf n q.1.1 r ω + (1 + Finset.univ.sup' Finset.univ_nonempty
        (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖) /
          sz.Bctl n q.1.1 ^ (r - 1))))
      (fun n q _ => STPsi (A n) (Cf.eta n (s n) / Cf.eta n q.1.2) r 0) := by
    refine iterationsA_prec_absorbg hsize (c := 1 + 2 * cv) ?_ ?_
    · filter_upwards [hS.rho] with n hρ q ω
      exact iterationsA_STPsi_nonneg (hS.A_nonneg n) (by linarith [(hρ q).1]) r 0
    · refine iterationsA_prec_mono_rightg hone ?_
      filter_upwards [hS.one_le_A, hS.rho] with n hA1 hρ q ω
      exact step3_psi0_le hA1 (hρ q).1 hcv0
  refine iterationsA_prec_mono_leftg ?_ hΨ
  filter_upwards [hS.Bctl, hS.one_le_A] with n hBn hA1 q ω
  have hB0 := hBpos n q
  have hcvA : 0 < cv * A n := by have := hS.one_le_cv; positivity
  have hlow : (sz.Bctl n q.1.1)⁻¹ ≤ cv * A n := by
    have h := (hBn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).1
    have := inv_anti₀ (inv_pos.2 hcvA) h
    rwa [inv_inv] at this
  set SK : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) => ‖Cf.K n q.1.1 p.1 p.2‖) with hSK
  have hSL0 : 0 ≤ STmaxLg Cf n q.1.1 r ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
      ‖Cf.L n q.1.1 p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have hSK0 : 0 ≤ SK :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
      ‖Cf.K n q.1.1 p.1 p.2‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have hSLK : STmaxLKg Cf n q.1.1 r ω ≤ STmaxLg Cf n q.1.1 r ω + SK := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have h1 : ‖Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2‖ ≤
        ‖Cf.L n q.1.1 p.1 p.2 ω‖ + ‖Cf.K n q.1.1 p.1 p.2‖ := norm_sub_le _ _
    have h2 : ‖Cf.L n q.1.1 p.1 p.2 ω‖ ≤ STmaxLg Cf n q.1.1 r ω :=
      Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖Cf.L n q.1.1 p.1 p.2 ω‖) (Finset.mem_univ p)
    have h3 : ‖Cf.K n q.1.1 p.1 p.2‖ ≤ SK :=
      Finset.le_sup' (fun p : (Fin r → Bool) × (Fin r → Zd d (sz.L n)) =>
        ‖Cf.K n q.1.1 p.1 p.2‖) (Finset.mem_univ p)
    linarith
  have hBr : sz.Bctl n q.1.1 ^ r = sz.Bctl n q.1.1 * sz.Bctl n q.1.1 ^ (r - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hC : 0 < sz.Bctl n q.1.1 ^ (r - 1) := pow_pos hB0 _
  have hdiv : (STmaxLg Cf n q.1.1 r ω + SK) / sz.Bctl n q.1.1 ^ r =
      (STmaxLg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) + SK / sz.Bctl n q.1.1 ^ (r - 1)) *
        (sz.Bctl n q.1.1)⁻¹ := by
    rw [hBr]; field_simp
  have hu0 : 0 ≤ STmaxLg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) := div_nonneg hSL0 hC.le
  have hv0 : 0 ≤ SK / sz.Bctl n q.1.1 ^ (r - 1) := div_nonneg hSK0 hC.le
  have hstep : STmaxLKg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ r ≤
      (STmaxLg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1) + SK / sz.Bctl n q.1.1 ^ (r - 1)) * (cv * A n) := by
    calc STmaxLKg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ r
        ≤ (STmaxLg Cf n q.1.1 r ω + SK) / sz.Bctl n q.1.1 ^ r :=
          div_le_div_of_nonneg_right hSLK (pow_pos hB0 r).le
      _ = _ := hdiv
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (add_nonneg hu0 hv0)
  change 1 + STmaxLKg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ r ≤
    1 + cv * A n * ((1 + STmaxLg Cf n q.1.1 r ω / sz.Bctl n q.1.1 ^ (r - 1)) + (1 + SK / sz.Bctl n q.1.1 ^ (r - 1)))
  nlinarith [mul_nonneg hcvA.le (add_nonneg hu0 hv0)]

/-! ## 2. The scale twins and the assembly (band `st_hscale_I'`, `st_hscale_II'`, `step3_assemble`) -/

/-- `hscale`, case (i), at the carrier `Cm`: the band `st_hscale_I'` (`ScaleFacts3:303`) at the energy `E'` whose `η` is `Cm.eta`
(`IterationsGen_Ep`), so the band scale twin is read, not copied. -/
private theorem Step34RGen_hscale_I {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d 𝔡 : ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hreg : STRegIterI sz s t) (hcon : sz.STConStInd 𝔠d s t) (hWO : sz.WO 𝔡)
    (ht1 : ∀ n, t n < 1) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAI n) (Cm.eta n (s n) / Cm.eta n q.1.2) r k ≤ c * sz.STAI n ^ (3 / 4 : ℝ) := by
  obtain ⟨E', hE', hη⟩ := IterationsGen_Ep hL hm
  have h := st_hscale_I' sz (E := E') h𝔠d hreg hcon hWO ht1 hE'
  simpa only [hη] using h

/-- `hscale`, case (ii) (`A = (W^{-d}B_{s,0})⁻¹`): the band `st_hscale_II'` (`ScaleFacts3:310`) at `E'`. -/
private theorem Step34RGen_hscale_II {Cm : Step2Mat sz} {E s t : ℕ → ℝ} {𝔠d : ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (h𝔠d : 0 < 𝔠d) (hcon : sz.STConStInd 𝔠d s t) (ht1 : ∀ n, t n < 1) :
    ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (sz.STAII s n) (Cm.eta n (s n) / Cm.eta n q.1.2) r k ≤ c * sz.STAII s n ^ (3 / 4 : ℝ) := by
  obtain ⟨E', hE', hη⟩ := IterationsGen_Ep hL hm
  have h := st_hscale_II' sz (E := E') h𝔠d hcon ht1 hE'
  simpa only [hη] using h

/-- **Step 3 from the premises of `lem:iterations`** (band `step3_assemble`, `Step3:334`): `(lRB1)` is the a priori bound
`iterationsA_apriori_of_lRB1g`, `STAvgUgL` (a part of `STStep2ConclgL`) the averaged law, the uniform `𝒦` bound `iterationsB_K_pairsg` gives
`(rela_XILXILK)` and, with the scale facts `hS`, the a priori level `Step34RGen_hbase`; `hIter` is the conclusion of
`STIterationsgL'`/`STIterationsIIgL'`, `hscale`, `hBA` the deterministic scale facts. -/
private theorem Step34RGen_assemble [IsProbabilityMeasure μ] {Cm : Step2Mat sz} {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hN : sz.SizeTendsto) {s t A T : ℕ → ℝ} {cB cv K Cd : ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hKb : STKboundgL Cm.toFlowFM μ) (hS : IterationsAScaleg Cm.toFlowFM s t A T cB cv K)
    (hscale : ∀ r, 2 ≤ r → ∃ k : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop, ∀ q : STPair s t n,
      STPsi (A n) (Cm.eta n (s n) / Cm.eta n q.1.2) r k ≤ c * A n ^ (3 / 4 : ℝ))
    (hBA : ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop, ∀ v : TimeIcc s t n, sz.Bctl n (v : ℝ) * A n ^ (3 / 4 : ℝ) ≤ c)
    (hIter : ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k → (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL Cm.toFlowFM μ s t A r k) →
      (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL Cm.toFlowFM μ s t A r (k - 1)) → STIterHypgL Cm.toFlowFM μ s t A n_ k)
    (hStep1 : STStep1LoopgL Cm.toFlowFM μ s t) (hStep2 : STStep2ConclgL Cm.toFlowFM μ s t Cd) :
    STLmaxUgL Cm.toFlowFM μ s t := by
  have hsize := tendsto_size sz hN
  have hK : ∀ m, 1 ≤ m → PrecL sz μ (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖Cm.toFlowFM.K n p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) := fun m hm =>
    iterationsB_K_pairsg Cm.toFlowFM hN hKb hs0 (fun n => (hst n).le) ht1 m hm
  have hapri := iterationsA_apriori_of_lRB1g hL hsize ht1 hStep1
  exact Step34RGen_skeleton Cm.toFlowFM hsize hS.A_nonneg hS.one_le_A ht1 hIter
    (fun r hr => Step34RGen_hbase hsize hS hapri hK (by omega)) hscale hBA
    (iterationsA_avg_of_STAvgUg Cm.toFlowFM hsize ht1 hStep2.2.1)
    (fun r hr => iterationsA_rela_of_Kg Cm.toFlowFM hsize ht1 r hr (hK r hr))

/-! ## 3. Targets 1-3: Step 3 at the three regimes -/

/-- **Target 1, `stStep3RegIIIgL_of`** (= `T2509_Step3RegIIIOf`; band `stStep3RegIII_holds`, `Step3:377`): Step 3 at regime (iii) `ilambda² ≤ 1 - t`
(`3_5:1384`: `(Eq:LGxb)` follows directly from `(lRB1)`), `𝔠d = 1/100` (not consumed).  `((1-s)/(1-u)) W^{-d}B_{s,0} ≤ 2 W^{-d}B_{u,0}` for `u ∈ [s,t]`
(`step3_xB`), so `(lRB1)` gives `|𝓛^{(k)}_u| ≺ 2^{k-1} (W^{-d}B_{u,0})^{k-1}` and the constant is absorbed. -/
theorem stStep3RegIIIgL_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STStep3RgL d STReg5III law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg _hK _hKw _hLK _hcon hStep1 _hStep2 k hk
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hsize := tendsto_size sz hA.2.2.1
  have hB : ∀ n (p : TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n))),
      0 ≤ sz.Bctl n (p.1 : ℝ) ^ (k - 1) := fun n p =>
    (pow_pos (st_Bctl_pos sz (lt_of_le_of_lt (p.1.2).2 (ht1 n))) _).le
  refine iterationsA_prec_absorbg hsize (c := 2 ^ (k - 1)) (Eventually.of_forall fun n p _ => hB n p) ?_
  refine iterationsA_prec_mono_rightg (hStep1 k hk) (Eventually.of_forall fun n p _ => ?_)
  have hu1 : (p.1 : ℝ) < 1 := lt_of_le_of_lt (p.1.2).2 (ht1 n)
  have hx : 0 < 1 - (p.1 : ℝ) := by linarith
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz (lt_of_le_of_lt (p.1.2).1 hu1)
  have hgu : sz.lam n ^ 2 ≤ 1 - (p.1 : ℝ) := (hreg n).trans (by linarith [(p.1.2).2])
  have hxB := step3_xB sz (n := n) (p.1.2).1 hu1 hgu
  have hq : (1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n) ≤ 2 * sz.Bctl n (p.1 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hx]; linarith
  have hq0 : 0 ≤ (1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n) := by
    have : 0 < 1 - s n := by linarith [(p.1.2).1, hs0 n]
    positivity
  calc ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * sz.Bctl n (s n) ^ (k - 1)
      = ((1 - s n) / (1 - (p.1 : ℝ)) * sz.Bctl n (s n)) ^ (k - 1) := (mul_pow _ _ _).symm
    _ ≤ (2 * sz.Bctl n (p.1 : ℝ)) ^ (k - 1) := pow_le_pow_left₀ hq0 hq _
    _ = 2 ^ (k - 1) * sz.Bctl n (p.1 : ℝ) ^ (k - 1) := mul_pow _ _ _

/-- **Target 2, `stStep3RegIgL_of`** (= `T2509_Step3RegIOf`; band `stStep3RegI_holds`, `Step3:408`): Step 3 at regime (i) `ilambda²/L² ≤ 1 - t`,
`1 - s ≤ ilambda²` (`3_5:1407-1431`).  `𝔠d = min` of the constants of the bootstrap pin `STOeqQtgL'` and of `STIterationsgL'`; `(con_st_ind)` at the minimum
gives it at each of them (`st5_conStInd_mono`).  The iteration `st_iterate` over `STIterationsgL'` (`A = ilambda² W^d`), the scale facts
`iterationsA_scale_Ig`, `Step34RGen_hscale_I`, `st_hBA_I`, the a priori level `Step34RGen_hbase` and `(rela_XILXILK)` give `(Eq:LGxb)`. -/
theorem stStep3RegIgL_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
        STIterationsgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
          STStep3RgL d STReg5I law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hOeq hIt hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hOeq hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hIt hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hcle : min c₁ c₂ ≤ 1 / 100 := (min_le_left _ _).trans hc₁'
  refine ⟨min c₁ c₂, hcpos, hcle, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK hcon hStep1 hStep2
  have := hProb sz
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨hL, hm⟩ := hLoop sz κ ε 𝔠 𝔡 z hκ hflow
  have hregI : STRegIterI sz s t := ⟨fun n => (hreg n).1, fun n => (hreg n).2⟩
  have m : ∀ c', min c₁ c₂ ≤ c' → sz.STConStInd c' s t := fun c' hcc =>
    st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hboot := H₁ 𝔠 sz z hflow s t hs0 hst htT hregI.1 hK hKw hLK (m c₁ (min_le_left _ _)) hStep2
  have hIter := H₂ 𝔠 sz z hflow s t hs0 hst htT hregI hK hLK (m c₂ (min_le_right _ _)) hStep1 hStep2 hboot
  exact Step34RGen_assemble hL hA.2.2.1 hs0 hst ht1 hK
    (iterationsA_scale_Ig (by omega) hL hm hcpos (hcle.trans (by norm_num)) hregI hcon hA.2.2.2.2 ht1)
    (Step34RGen_hscale_I hL hm hcpos hregI hcon hA.2.2.2.2 ht1) (st_hBA_I sz (by omega) hregI.1 hA.2.2.2.2)
    hIter hStep1 hStep2

/-- **Target 3, `stStep3IIgL_of`** (= `T2509_Step3IIOf`; band `stStep3II_holds`, `Step3:432`): Step 3 at case (ii) `1 - s ≤ ilambda²/L²`
(`3_5:1575-1595`, `A = (W^{-d}B_{s,0})⁻¹`).  `𝔠d = min` of the constants of `STOeqQtNZgL'` and `STIterationsIIgL'`; scale facts `iterationsA_scale_IIg`
(`𝔠d ≤ 1/24`), `Step34RGen_hscale_II`, `st_hBA_II` (`𝔠d ≤ 1/4`). -/
theorem stStep3IIgL_of :
    ∀ (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 → STOeqQtNZgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
        STIterationsIIgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 →
          STStep3RgL d STCaseII law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hOeq hIt hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hOeq hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hIt hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hcle : min c₁ c₂ ≤ 1 / 100 := (min_le_left _ _).trans hc₁'
  refine ⟨min c₁ c₂, hcpos, hcle, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK hcon hStep1 hStep2
  have := hProb sz
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨hL, hm⟩ := hLoop sz κ ε 𝔠 𝔡 z hκ hflow
  have m : ∀ c', min c₁ c₂ ≤ c' → sz.STConStInd c' s t := fun c' hcc =>
    st5_conStInd_mono sz hcon ht1 hcpos hcc
  have hboot := H₁ 𝔠 sz z hflow s t hs0 hst htT hreg hK hKw hLK (m c₁ (min_le_left _ _)) hStep2
  have hIter := H₂ 𝔠 sz z hflow s t hs0 hst htT hreg hK hLK (m c₂ (min_le_right _ _)) hStep1 hStep2 hboot
  exact Step34RGen_assemble hL hA.2.2.1 hs0 hst ht1 hK
    (iterationsA_scale_IIg hL hm hcpos (hcle.trans (by norm_num)) hcon ht1)
    (Step34RGen_hscale_II hL hm hcpos hcon ht1) (st_hBA_II sz hcpos (hcle.trans (by norm_num)) hcon ht1)
    hIter hStep1 hStep2

/-! ## 4. Targets 4-5: Step 4 from the bootstrap pin, and the monotonicity in the regime -/

/-- **Step 4 from `(saww02)`, inductively in the length** (`3_5:1605-1613`; band `step4_skeleton`, `Step4:60`): the R2* bootstrap `STXiBootgL'` with
`Ξ^{𝓛} ≡ 1` (`STLmaxUgL`) and `Ξ^{𝓛-𝒦}_1 ≡ 1` (`STAvgUgL`) gives `Ξ̂^{𝓛-𝒦}_{v,n} ≺ B_s^{-1/(4p)} + c_n` for every `p`; `B_s ≥ N^{-2}` and `p` large
give `Ξ̂^{𝓛-𝒦}_n ≺ 1`; induction on the length. -/
private theorem Step34RGen_step4_skeleton {C : FlowFM sz} {s t : ℕ → ℝ} {Λ : ℝ} (hsize : Tendsto sz.size atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (hBoot : STXiBootgL' C μ s t) (h3 : STLmaxUgL C μ s t) (h1 : STAvgUgL C μ s t) : STLKUgL C μ s t := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  let ψ : ∀ n, TimeIcc s t n → STPair s t n := fun n v => ⟨((v : ℝ), (v : ℝ)), (v.2).1, le_rfl, (v.2).2⟩
  have hBpos : ∀ n (v : TimeIcc s t n) (k : ℕ), 0 < (sz.Bctl n (v : ℝ)) ^ k := fun n v k =>
    pow_pos (st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))) k
  have hXiL : ∀ m, 1 ≤ m → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg C n q.1.1 m ω)
      (fun _ _ _ => 1) := fun m hm =>
    StochDomAt.precomp_param
      (st_prec_one_add_supg hsize (U := fun n => TimeIcc s t n)
        (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
        (fun n v p ω => ‖C.L n (v : ℝ) p.1 p.2 ω‖) (fun n v => (sz.Bctl n (v : ℝ)) ^ (m - 1))
        (fun n v => hBpos n v _) (h3 m hm)) φ
  have hBlow := st_Bctl_ge sz hsize hlam
  have hall : ∀ k, 1 ≤ k → PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg C n q.1.1 k ω)
      (fun _ _ _ => 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        exact iterationsA_avg_of_STAvgUg C hsize ht1 h1
      · have hpp : ∀ p, 1 ≤ p → PrecL sz μ (U := STPair s t)
            (fun n q ω => STXiLKg C n q.1.1 k ω)
            (fun n q _ => STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz.Bctl n (s n)) k p) := fun p hp =>
          hBoot k p hk2 hp (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
            (fun m hm _ => hXiL m hm) (fun m hm hmk => ih m (by omega) hm)
        intro τ hτ D hD
        obtain ⟨p, hp⟩ := exists_nat_gt (2 / τ)
        have hp1 : 1 ≤ p := by
          have : (0 : ℝ) < 2 / τ := by positivity
          exact_mod_cast (show (0 : ℝ) < p by linarith)
        have hpτ : 2 / (4 * (p : ℝ)) ≤ τ / 4 := by
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have := (div_lt_iff₀ hτ).1 hp
          nlinarith
        set ck : ℝ := (((Finset.Icc 1 (k - 1)).card + (Finset.Icc (k - 1) (k + 1)).card +
          (Finset.Icc ((k + 1) / 2 + 1) (k - 1)).card : ℕ) : ℝ) with hck
        have hck0 : 0 ≤ ck := Nat.cast_nonneg _
        filter_upwards [hpp p hp1 (τ / 2) (half_pos hτ) D hD, hBlow,
          hsize.eventually (eventually_le_rpow (ck + 1) (show 0 < τ / 4 by positivity)),
          hsize.eventually (eventually_ge_atTop 1)] with n hn hBn hNck hN1
        refine le_trans (measure_mono ?_) hn
        rintro ω ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
        have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
        have hB := hBn (s n) (hs0 n) ((hst n).trans (ht1 n)).le
        have hNq : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := Real.one_le_rpow hN1' (by positivity)
        have hz1 : sz.Bctl n (s n) ^ (-(1 : ℝ) / (4 * (p : ℝ))) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := by
          have hpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hNpos _
          calc sz.Bctl n (s n) ^ (-(1 : ℝ) / (4 * (p : ℝ)))
              ≤ (((sz.size n : ℕ) : ℝ) ^ (-(2 : ℝ))) ^ (-(1 : ℝ) / (4 * (p : ℝ))) :=
                Real.rpow_le_rpow_of_nonpos hpos hB (by
                  have : (0 : ℝ) < p := by exact_mod_cast hp1
                  have : 0 < 4 * (p : ℝ) := by positivity
                  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le)
            _ = ((sz.size n : ℕ) : ℝ) ^ (2 / (4 * (p : ℝ))) := by
                rw [← Real.rpow_mul hNpos.le]; congr 1; ring
            _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := Real.rpow_le_rpow_of_exponent_le hN1' hpτ
        have hz2 : STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz.Bctl n (s n)) k p ≤
            ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
          rw [st_bootRHS_one]
          have hsq : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
              ((sz.size n : ℕ) : ℝ) ^ (τ / 4) * ((sz.size n : ℕ) : ℝ) ^ (τ / 4) := by
            rw [← Real.rpow_add hNpos]; congr 1; ring
          rw [hsq]
          nlinarith
        have hhh : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
            ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
        change ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz.Bctl n (s n)) k p < _
        have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * 1 < STXiLKg C n q.1.1 k ω := hq
        have : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz.Bctl n (s n)) k p ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
          calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
                mul_le_mul_of_nonneg_left hz2 (Real.rpow_nonneg hNpos.le _)
            _ = _ := hhh
        linarith
  intro k hk
  exact st_prec_of_xig (U := fun n => TimeIcc s t n) (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n v p ω => ‖C.L n (v : ℝ) p.1 p.2 ω - C.K n (v : ℝ) p.1 p.2‖)
    (fun n v => (sz.Bctl n (v : ℝ)) ^ k) (fun n v => hBpos n v _)
    (StochDomAt.precomp_param (hall k hk) ψ)

/-- **Target 4, `stStep4RgL_of_ing`** (= `T2509_Step4ROfIng`; band `step4_of_ing`, `Step4:156`, private there): Step 4 under a regime `R` from the bootstrap
pin over `R`, `STIngRgL d R .. STXiBootgL'`; no regime split, the constant `𝔠d` is that of the bootstrap pin. -/
theorem stStep4RgL_of_ing :
    ∀ (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
      (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ →
        Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (Es T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      IterationsGen2_Fam d law Flow mkM Hf Es T0 →
        STIngRgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0
          (fun sz z s t => STXiBootgL' (mkM sz z).toFlowFM (law sz) s t) →
          STStep4RgL d R law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  intro d R law Flow mkM Hf Es T0 ⟨hFl, hProb, hLoop, hLC⟩ hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hK hKw hLK hcon hS1L hS2 hS3
  have hBoot := H 𝔠 sz z hflow s t hs0 hst htT hR hK hKw hLK hcon hS2
  have hA := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (htT n).trans_lt (hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  have hWO : sz.WO 𝔡 := hA.2.2.2.2
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hA.2.2.1
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n hn hpos
    exact ⟨hpos.1, hn.2⟩
  exact Step34RGen_step4_skeleton (μ := law sz) hsize hs0 hst ht1 hlam hBoot hS3 hS2.2.1

/-- **Target 5, `stStep34RgL_mono`** (= `T2509_Step34Mono`; band `step4R_mono`, `Step4:172`, private there, and its Step 3 twin): `STStep3RgL` and `STStep4RgL`
are monotone along the regime, `R' ⊆ R` at `Sizes d`. -/
theorem stStep34RgL_mono :
    ∀ (d : ℕ) (R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
      (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz)
      (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ),
      (∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) →
        (STStep3RgL d R law Flow mk T0 → STStep3RgL d R' law Flow mk T0) ∧
          (STStep4RgL d R law Flow mk T0 → STStep4RgL d R' law Flow mk T0) := by
  intro d R R' law Flow mk T0 hR
  refine ⟨fun h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd => ?_, fun h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd => ?_⟩
  · obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    refine ⟨𝔠d, h0, h1, ?_⟩
    intro 𝔠 sz z hflow s t hs0 hst htT hR' hK hKw hLK hcon hS1L hS2
    exact H 𝔠 sz z hflow s t hs0 hst htT (hR sz s t hR') hK hKw hLK hcon hS1L hS2
  · obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
    refine ⟨𝔠d, h0, h1, ?_⟩
    intro 𝔠 sz z hflow s t hs0 hst htT hR' hK hKw hLK hcon hS1L hS2 hS3
    exact H 𝔠 sz z hflow s t hs0 hst htT (hR sz s t hR') hK hKw hLK hcon hS1L hS2 hS3

/-! ## 5. The band re-derivations (every `d`)

The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), seqHflow, STflowE, lemT)`: the bundle is `IterationsGen2_famBand`, the bootstrap pins are
`stOeqQtgL'_band`, `stOeqQtNZgL'_band` (T2505), the two `lem:iterations` pins are `stIterationsgL'_of`, `stIterationsIIgL'_of` at the bundle.  For `d < 3` every
pin is vacuous (`3 ≤ d →`). -/

section BandReDerivation

namespace Step34RGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- The band **Step 3 at regime (iii)** (`stStep3RegIII_holds`, `Step3:377`) from target 1 through `bandFM_STStep3R` and `IterationsGen2_famBand`. -/
theorem stStep3RegIII_holds_of_gen (d : ℕ) : STStep3R d STReg5III :=
  (bandFM_STStep3R d STReg5III).2
    (stStep3RegIIIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
      (IterationsGen2_famBand d))

/-- The band **Step 3 at regime (i)** (`stStep3RegI_holds`, `Step3:408`) from target 2, `stOeqQtgL'_band` and `stIterationsgL'_of`. -/
theorem stStep3RegI_holds_of_gen (d : ℕ) : STStep3R d STReg5I := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STStep3R d STReg5I).2
      (stStep3RegIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
        (IterationsGen2_famBand d) (QtXiRoundLiftGenCheck.stOeqQtgL'_band d hd)
        (stIterationsgL'_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
          (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
          (IterationsGen2_famBand d)))
  · exact fun h => absurd h hd

/-- The band **Step 3 at case (ii)** (`stStep3II_holds`, `Step3:432`) from target 3, `stOeqQtNZgL'_band` and `stIterationsIIgL'_of`. -/
theorem stStep3II_holds_of_gen (d : ℕ) : STStep3II d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STStep3R d STCaseII).2
      (stStep3IIgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
        (IterationsGen2_famBand d) (QtNonzeroBootGenCheck.stOeqQtNZgL'_band d hd)
        (stIterationsIIgL'_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
          (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
          (IterationsGen2_famBand d)))
  · exact fun h => absurd h hd

/-- The band **Step 4 at case (i)** (`stStep4I_holds`, `Step4:189`) from target 4 and `stOeqQtgL'_band`. -/
theorem stStep4I_holds_of_gen (d : ℕ) : STStep4I d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STStep4R d STCaseI).2
      (stStep4RgL_of_ing d STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
        (IterationsGen2_famBand d) (QtXiRoundLiftGenCheck.stOeqQtgL'_band d hd))
  · exact fun h => absurd h hd

/-- The band **Step 4 at case (ii)** (`stStep4II_holds`, `Step4:193`) from target 4 and `stOeqQtNZgL'_band`. -/
theorem stStep4II_holds_of_gen (d : ℕ) : STStep4II d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STStep4R d STCaseII).2
      (stStep4RgL_of_ing d STCaseII (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
        (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
        (IterationsGen2_famBand d) (QtNonzeroBootGenCheck.stOeqQtNZgL'_band d hd))
  · exact fun h => absurd h hd

end Step34RGenCheck

end BandReDerivation

/-! ## 6. Compiled nonempty instances at `d = 3`

The generic targets are applied directly at the band family (bundle `IterationsGen2_famBand 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `C_d` arbitrary positive) at the merged
data: regimes (iii) and the case-(i) Step 4 at `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`, `s ≡ 0`, `t ≡ 1/16`, `sz0_regIII`, `sz0_caseI`); regime (i) and
case (ii) at `szB` (`L = 4`, `W = n + 4`, `lam = 1`; `(7/8, 15/16)`, `(15/16, 31/32)`).  `STKboundgL`, `STKwardgL` are discharged (theorems of the flow, through
`bandFM_STKward`), as are the bootstrap and `lem:iterations` pins (`stOeqQtgL'_band3`, `stOeqQtNZgL'_band3`, `stIterations(II)gL'_of`); what stays a
hypothesis is another gate's pin: `STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STLmaxUgL` (Step 4). -/

namespace Step34RGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- `STKbound` at the band is `STKboundgL` at the band carrier (`bandFM_STKbound`, `Iff.rfl`; stated at a variable `sz` so that no concrete datum is unfolded). -/
private theorem Step34RGen_band_Kbound {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} (h : STKbound sz E) :
    STKboundgL (bandStep2Mat sz E).toFlowFM (Sizes.seqP sz) := h

/-- `STKward` at the band is `STKwardgL` at the band carrier (`bandFM_STKward`). -/
private theorem Step34RGen_band_Kward {d : ℕ} {sz : Sizes d} {E : ℕ → ℝ} (h : STKward sz E) :
    STKwardgL (bandStep2Mat sz E).toFlowFM (Sizes.seqP sz) := (bandFM_STKward sz E).1 h

/-- The band family arguments of the generic targets (`d = 3`), as a local notation-free helper: the bundle. -/
private theorem Step34RGen_fam3 :
    IterationsGen2_Fam 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n)) :=
  IterationsGen2_famBand 3

/-- **Target 1, instance**: `stStep3RegIIIgL_of` at the band family and `(sz0, z0, 0, 1/16)`; every deterministic hypothesis is discharged. -/
theorem inst_step3RegIIIgL (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst →
        STStep1LoopgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst Cd →
        STLmaxUgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stStep3RegIIIgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
    Step34RGen_fam3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 => H (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht
    RBM.Ind.Step3Inst.sz0_regIII
    (Step34RGen_band_Kbound (stKbound_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    (Step34RGen_band_Kward (stKward_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    ha (sz0_con 𝔠d h0) h1' h2⟩

/-- **Target 2, instance**: `stStep3RegIgL_of` at the band family and `(szB, zB, 7/8, 15/16)` (`STReg5I`); the bootstrap pin and `STIterationsgL'` are the
band theorems `stOeqQtgL'_band3`, `stIterationsgL'_of`. -/
theorem inst_step3RegIgL (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 7 / 8) →
        STStep1LoopgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) →
        STStep2ConclgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16) Cd →
        STLmaxUgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 7 / 8) (fun _ => 15 / 16)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stStep3RegIgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
    Step34RGen_fam3 QtXiRoundLiftGenCheck.stOeqQtgL'_band3
    (stIterationsgL'_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
      Step34RGen_fam3) (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 => H (1 / 6) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun n => ⟨szB_regIterI.1 n, szB_regIterI.2 n⟩)
    (Step34RGen_band_Kbound (stKbound_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB))
    (Step34RGen_band_Kward (stKward_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB))
    ha (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) h1' h2⟩

/-- **Target 3, instance**: `stStep3IIgL_of` at the band family and `(szB, zB, 15/16, 31/32)` (`STCaseII`). -/
theorem inst_step3IIgL (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 15 / 16) →
        STStep1LoopgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) →
        STStep2ConclgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) Cd →
        STLmaxUgL ((bandStep2Mat szB (STflowE zB)).toFlowFM) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32)) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stStep3IIgL_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
    Step34RGen_fam3 QtNonzeroBootGenCheck.stOeqQtNZgL'_band3
    (stIterationsIIgL'_of 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
      Step34RGen_fam3) (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 => H (1 / 6) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (Step34RGen_band_Kbound (stKbound_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB))
    (Step34RGen_band_Kward (stKward_of_flow szB (by norm_num) (κ := 1 / 10) (by norm_num) flow_zB))
    ha (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) h1' h2⟩

/-- **Target 4, instance**: `stStep4RgL_of_ing` at `R = STCaseI`, the band family and `(sz0, z0, 0, 1/16)`; the ingredient pin is `stOeqQtgL'_band3`. -/
theorem inst_step4RgL (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst →
        STStep1LoopgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst Cd →
        STLmaxUgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst →
        STLKUgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := stStep4RgL_of_ing 3 STCaseI (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun sz _ => seqHflow sz) (fun _ z => STflowE z) (fun _ z n => lemT (z n))
    Step34RGen_fam3 QtXiRoundLiftGenCheck.stOeqQtgL'_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 h3 => H (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI
    (Step34RGen_band_Kbound (stKbound_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    (Step34RGen_band_Kward (stKward_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    ha (sz0_con 𝔠d h0) h1' h2 h3⟩

/-- **Target 5, instance**: `stStep34RgL_mono` with `R = STCaseI`, `R' = STReg5III` (`st_caseI_of_reg5III`) applied to the Step 4 pin of the band re-derivation
(`stStep4I_holds_of_gen 3` through `bandFM_STStep4R`) gives Step 4 at regime (iii); applied at `(sz0, z0, 0, 1/16)` (`sz0_regIII`). -/
theorem inst_step34Mono (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLKgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst →
        STStep1LoopgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst →
        STStep2ConclgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst Cd →
        STLmaxUgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst →
        STLKUgL ((bandStep2Mat sz0 (STflowE z0)).toFlowFM) (Sizes.seqP sz0) sInst tInst) := by
  have hm := (stStep34RgL_mono 3 STCaseI STReg5III (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n))
    (fun sz s t h => st_caseI_of_reg5III 3 sz s t h)).2 ((bandFM_STStep4R 3 STCaseI).1 (stStep4I_holds_of_gen 3))
  obtain ⟨𝔠d, h0, h1, H⟩ := hm (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 h3 => H (1 / 6) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht
    RBM.Ind.Step3Inst.sz0_regIII
    (Step34RGen_band_Kbound (stKbound_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    (Step34RGen_band_Kward (stKward_of_flow sz0 (by norm_num) (κ := 1 / 10) (by norm_num) flow_z0))
    ha (sz0_con 𝔠d h0) h1' h2 h3⟩

/-- **The band instances through the re-derived pins**: `inst_step3R`, `inst_step4R` (`Step34Pins:917, 928`) at the band pins `stStep3RegIII_holds_of_gen 3`,
`stStep3RegI_holds_of_gen 3`, `stStep3II_holds_of_gen 3`, `stStep4I_holds_of_gen 3`, `stStep4II_holds_of_gen 3`. -/
example (Cd : ℝ) (hCd : 0 < Cd) : InstStep3Concl sz0 z0 sInst tInst Cd :=
  inst_step3R STReg5III (stStep3RegIII_holds_of_gen 3) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht
    RBM.Ind.Step3Inst.sz0_regIII sz0_con Cd hCd

example (Cd : ℝ) (hCd : 0 < Cd) : InstStep3Concl szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_step3R STReg5I (stStep3RegI_holds_of_gen 3) szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun n => ⟨szB_regIterI.1 n, szB_regIterI.2 n⟩)
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

example (Cd : ℝ) (hCd : 0 < Cd) : InstStep3Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step3R STCaseII (stStep3II_holds_of_gen 3) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

example (Cd : ℝ) (hCd : 0 < Cd) : InstStep4Concl sz0 z0 sInst tInst Cd :=
  inst_step4R STCaseI (stStep4I_holds_of_gen 3) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con Cd hCd

example (Cd : ℝ) (hCd : 0 < Cd) : InstStep4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step4R STCaseII (stStep4II_holds_of_gen 3) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

end Step34RGenCheck

end RBM.BA

end
