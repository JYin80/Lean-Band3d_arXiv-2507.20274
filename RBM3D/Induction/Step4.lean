/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtXiRoundLift
import RBM3D.Induction.QtNonzeroBoot
import RBM3D.Induction.IterationsA
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.MainIndRegimes

/-!
# Step 4 of `lem:main_ind` at `d ≥ 3`, and the main-induction assembly from the step statements

Paper: arXiv:2507.20274, Step 4 of Theorem 2.24 (`lem:main_ind`), (2.91) `Eq:L-KGt-flow`; its
proof (Subsection 4.3, (4.50) `saww02`); the bootstrap bound (4.36) `am;asoi222` with the first
term at `B_{s,0}`.

* §1 `step4_skeleton` (private): the skeleton for `(saww02)` with the bootstrap `STXiBoot'`: the
  first summand of `STbootRHS` is `(W^{-d}B_{s,0})^{-1/(4p)}` (constant in the pair),
  `≤ N^{1/(2p)}` by `st_Bctl_ge` at `s n ∈ [0,1)`; with `Ξ^{(𝓛)} ≡ 1` (`STLmaxU`,
  `st_prec_one_add_sup`) and `Ξ^{(𝓛-𝒦)}_m ≡ 1` for the shorter lengths (strong induction on the
  length, base `iterationsA_avg_of_STAvgU`), `STXiBoot'` gives `Ξ̂^{(𝓛-𝒦)}_{n} ≺ 1`, and
  `st_prec_of_xi` turns that into `(Eq:L-KGt-flow)` uniformly in `u ∈ [s,t]`;
* §2 `step4_of_ing` (private), `step4R_mono` (private), `stStep4I_holds`, `stStep4II_holds`
  (`RBM.Ind`): `STStep4R d R` from the bootstrap `STIngR d R STXiBoot'`
  (`stOeqQt'_holds`, `stOeqQtNZ'_holds`); no regime split, the constant `𝔠_d` is that of the
  bootstrap statement;
* §3 `ST_mainInd_of_pins'` (`RBM.Gauss.Sizes`): `lem:main_ind` from the step statements
  `STStep2`, `STStep3R · STReg5III`, `STStep3R · STReg5I`, `STStep3II`, `STStep5I/II`,
  `STStep6I/II/III` as hypotheses (Step 3 at the regimes the assembly consumes), with Step 4
  proved here.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. The skeleton of `(saww02)` over the bootstrap `STXiBoot'` -/

/-- **Step 4 from `(saww02)`, inductively in the length** (proof of Step 4): the bootstrap `STXiBoot'`
(`(am;asoi222)` with `B_s`) with `Ξ^{𝓛} ≡ 1` (`STLmaxU`) and `Ξ^{𝓛-𝒦}_1 ≡ 1` (`STAvgU`) gives
`Ξ̂^{𝓛-𝒦}_{v,n} ≺ B_s^{-1/(4p)} + c_n` for every `p`; `B_s ≥ N^{-2}` and `p` large give `Ξ̂^{𝓛-𝒦}_n ≺ 1`; the
induction on the length and `Ξ̂ ≺ 1 ⟺ max ≺ B^k` give `(Eq:L-KGt-flow)` uniformly in `u`.  Hypotheses: `0 ≤ s`,
`s < t < 1`, `(eq:WO)` as `0 < ilambda ≤ Λ`. -/
private theorem step4_skeleton {E s t : ℕ → ℝ} {Λ : ℝ} (hsize : Tendsto sz.size atTop atTop)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht1 : ∀ n, t n < 1)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λ)
    (hBoot : STXiBoot' sz E s t) (h3 : STLmaxU sz E s t) (h1 : STAvgU sz E s t) : STLKU sz E s t := by
  let φ : ∀ n, STPair s t n → TimeIcc s t n := fun n q => ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩
  let ψ : ∀ n, TimeIcc s t n → STPair s t n := fun n v => ⟨((v : ℝ), (v : ℝ)), (v.2).1, le_rfl, (v.2).2⟩
  have hBpos : ∀ n (v : TimeIcc s t n) (k : ℕ), 0 < (sz.Bctl n (v : ℝ)) ^ k := fun n v k =>
    pow_pos (st_Bctl_pos sz (lt_of_le_of_lt (v.2).2 (ht1 n))) k
  have hXiL : ∀ m, 1 ≤ m → Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun _ _ _ => 1) := fun m hm =>
    StochDomAt.precomp_param
      (st_prec_one_add_sup sz hsize (U := fun n => TimeIcc s t n)
        (V := fun n => (Fin m → Bool) × (Fin m → Zd d (sz.L n)))
        (fun n v p ω => ‖Lloop sz n (E n) (v : ℝ) p.1 p.2 ω‖) (fun n v => (sz.Bctl n (v : ℝ)) ^ (m - 1))
        (fun n v => hBpos n v _) (h3 m hm)) φ
  have hBlow := st_Bctl_ge sz hsize hlam
  have hall : ∀ k, 1 ≤ k → Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 k ω)
      (fun _ _ _ => 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        exact iterationsA_avg_of_STAvgU sz hsize ht1 h1
      · have hpp : ∀ p, 1 ≤ p → Prec sz (U := STPair s t)
            (fun n q ω => STXiLK sz n (E n) q.1.1 k ω)
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
        have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * 1 < STXiLK sz n (E n) q.1.1 k ω := hq
        have : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz.Bctl n (s n)) k p ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
          calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
                mul_le_mul_of_nonneg_left hz2 (Real.rpow_nonneg hNpos.le _)
            _ = _ := hhh
        linarith
  intro k hk
  exact st_prec_of_xi sz (U := fun n => TimeIcc s t n) (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n v p ω => ‖Lloop sz n (E n) (v : ℝ) p.1 p.2 ω - STKloop sz n (E n) (v : ℝ) p.1 p.2‖)
    (fun n v => (sz.Bctl n (v : ℝ)) ^ k) (fun n v => hBpos n v _)
    (StochDomAt.precomp_param (hall k hk) ψ)

/-! ## 2. `STStep4R` from the bootstrap `STXiBoot'` -/

/-- **Step 4 under a regime `R`, from the bootstrap statement over `R`**: `STIngR d R STXiBoot'` (the shape of the
ingredient statements; `stOeqQt'_holds` for `STCaseI`, `stOeqQtNZ'_holds` for `STCaseII`) and the skeleton.  The constant
`𝔠_d` is that of the bootstrap statement; `STStep4R` has the same `∃ 𝔠d` position and the hypotheses of `STIngR` plus
`STStep1Loop` and `STLmaxU`. -/
private theorem step4_of_ing (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hI : STIngR d R (fun sz E s t => STXiBoot' sz E s t)) : STStep4R d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR hK hKw hLK hcon hS1L hS2 hS3
  have hBoot : STXiBoot' sz (STflowE z) s t := H 𝔠 sz z hflow s t hs0 hst htT hR hK hKw hLK hcon hS2
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow htT
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.1 hflow.1.2.2.1
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO, st5_eventually_A_ge_one sz h𝔡 hWO] with n hn hpos
    exact ⟨hpos.1, hn.2⟩
  exact step4_skeleton sz hsize hs0 hst ht1 hlam hBoot hS3 hS2.2.1

/-- `STStep4R` is monotone along the regime: `STStep4R d R` gives `STStep4R d R'` when `R' ⊆ R` at `Sizes d`. -/
private theorem step4R_mono {d : ℕ} {R R' : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop}
    (h : STStep4R d R) (hR : ∀ (sz : Sizes d) (s t : ℕ → ℝ), R' sz s t → R sz s t) : STStep4R d R' := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := h hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hR' hK hKw hLK hcon hS1L hS2 hS3
  exact H 𝔠 sz z hflow s t hs0 hst htT (hR sz s t hR') hK hKw hLK hcon hS1L hS2 hS3

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-- **`stStep4I_holds`: Step 4 of `lem:main_ind`, case (i) `1 - t ≥ ilambda²/L²`, for every `d`** (proof of Step 4): `(Eq:L-KGt-flow)` uniformly in `u ∈ [s,t]` from
`STLmaxU` (Step 3's conclusion, a hypothesis of `STStep4R`), the bootstrap `stOeqQt'_holds` and the averaged law. -/
theorem stStep4I_holds : ∀ d : ℕ, STStep4I d := fun d => step4_of_ing d STCaseI (stOeqQt'_holds d)

/-- **`stStep4II_holds`: Step 4 of `lem:main_ind`, case (ii) `1 - s ≤ ilambda²/L²`, for every `d`** (proof of Step 4): the same with the bootstrap `stOeqQtNZ'_holds`. -/
theorem stStep4II_holds : ∀ d : ℕ, STStep4II d := fun d => step4_of_ing d STCaseII (stOeqQtNZ'_holds d)

end RBM.Ind

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 3. `lem:main_ind` from the step statements, with Step 3 at the consumed regimes -/

/-- **`lem:main_ind` from the step statements, Step 3 at the regimes the assembly consumes**:
`STStep2`, Step 3 at `STReg5III`, `STReg5I` (`STStep3R d ·`) and `STStep3II`, `STStep5I/II`,
`STStep6I/II/III` are hypotheses.
Step 4 is proved (`stStep4I_holds`, `stStep4II_holds`), the other four steps by
`RBM.Green.stStep1_holds`, `stStep5III_holds`, `stStep5IV_holds`, `stStep6IV_holds`.  Regimes
(iii), (i) use `ST_mainIndR_of_steps` with `R34 = R` (Step 3 at the regime itself; Step 4 by
`step4R_mono` from case (i)), regimes (ii), (iv) use `ST_mainIndR_II/IV_of_steps`. -/
theorem ST_mainInd_of_pins' (d : ℕ) (h2 : STStep2 d) (h3III : STStep3R d STReg5III)
    (h3I : STStep3R d STReg5I) (h3II : STStep3II d) (h5I : STStep5I d) (h5II : STStep5II d)
    (h6I : STStep6I d) (h6II : STStep6II d) (h6III : STStep6III d) : STMainInd d := by
  intro hd
  have h1 : STStep1 d := RBM.Green.stStep1_holds hd
  have h4I : STStep4I d := RBM.Ind.stStep4I_holds d
  have h4II : STStep4II d := RBM.Ind.stStep4II_holds d
  exact ST_mainInd_of_regimes d
    (ST_mainIndR_of_steps d STReg5III STReg5III (fun _ _ _ _ h => h) h1 h2 h3III
      (step4R_mono h4I (fun sz s t h => st_caseI_of_reg5III d sz s t h)) (stStep5III_holds d) h6III)
    (ST_mainIndR_of_steps d STReg5I STReg5I (fun _ _ _ _ h => h) h1 h2 h3I
      (step4R_mono h4I (fun sz s t h => st_caseI_of_reg5I d sz s t h)) h5I h6I)
    (ST_mainIndR_II_of_steps d h1 h2 h3II h4II h5II h6II)
    (ST_mainIndR_IV_of_steps d h1 h2 h3II h4II (stStep5IV_holds d) (stStep6IV_holds d)) hd

end RBM.Gauss.Sizes


end
