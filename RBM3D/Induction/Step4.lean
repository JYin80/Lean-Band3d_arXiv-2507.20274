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
# S3-26 (ticket T2321): Step 4 of `lem:main_ind` at `d ≥ 3`, and the primed main-induction assembly

Paper: arXiv:2507.20274, Step 4 `paper/tex/1_2_Intro_model_result.tex:1370-1374`
(`(Eq:L-KGt-flow)`), proof `paper/tex/3_5_Loop_Hierarchy.tex:1602-1614`
(`(saww02)`, `3_5:1605-1613`);
bootstrap bound `(am;asoi222)` `3_5:1366` (R2*, DECISIONS §80: first term at `B_{s,0}`).
DECISIONS §68 (9), §80, §132, §133.

* §1 `step4_skeleton` (private): the probe skeleton `st_step4_skeleton`
  (`3c58211:RBM3D/Probe/T2041Pins.lean:945-1040`) with `STXiBoot` replaced by `STXiBoot'`: the first
  summand of `STbootRHS` is `(W^{-d}B_{s,0})^{-1/(4p)}` (constant in the pair), `≤ N^{1/(2p)}` by
  `st_Bctl_ge` at `s n ∈ [0,1)`; with `Ξ^{(𝓛)} ≡ 1` (`STLmaxU`, `st_prec_one_add_sup`) and
  `Ξ^{(𝓛-𝒦)}_m ≡ 1` for the shorter lengths (strong induction on the length, base
  `iterationsA_avg_of_STAvgU`), `STXiBoot'` gives `Ξ̂^{(𝓛-𝒦)}_{n} ≺ 1`, and `st_prec_of_xi` turns
  that into `(Eq:L-KGt-flow)` uniformly in `u ∈ [s,t]`;
* §2 `step4_of_ing` (private), `step4R_mono` (private), `stStep4I_holds`, `stStep4II_holds`
  (`RBM.Ind`): `STStep4R d R` from the R2* bootstrap `STIngR d R STXiBoot'`
  (`stOeqQt'_holds`, `stOeqQtNZ'_holds`); no regime split, the constant `𝔠_d` is that of the
  bootstrap pin;
* §3 `ST_mainInd_of_pins'` (`RBM.Gauss.Sizes`): `lem:main_ind` from the step pins still owed, with
  Step 3 at the regimes the assembly consumes (`STStep3R · STReg5III`, `STStep3R · STReg5I`,
  `STStep3II`) in place of `STStep3I`, and Step 4 proved here;
* §4 the compiled nonempty instances (`RBM.Ind.Step4Inst`).

The source of the port is the T2041 probe, not RBM2D.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. The skeleton of `(saww02)` over the R2* bootstrap -/

/-- **Step 4 from `(saww02)`, inductively in the length** (`3_5:1605-1613`): the R2* bootstrap `STXiBoot'`
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

/-! ## 2. `STStep4R` from the R2* bootstrap -/

/-- **Step 4 under a regime `R`, from the bootstrap pin over `R`**: `STIngR d R STXiBoot'` (the shape of the
ingredient pins; `stOeqQt'_holds` for `STCaseI`, `stOeqQtNZ'_holds` for `STCaseII`) and the skeleton.  The constant
`𝔠_d` is that of the bootstrap pin; `STStep4R` has the same `∃ 𝔠d` position and the hypotheses of `STIngR` plus
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

/-- **`stStep4I_holds`: Step 4 of `lem:main_ind`, case (i) `1 - t ≥ ilambda²/L²`, for every `d`** (`1_2:1370-1374`,
proof `3_5:1602-1613`; DECISIONS §133 (1); check shape `T2321_stStep4I`): `(Eq:L-KGt-flow)` uniformly in `u ∈ [s,t]` from
`STLmaxU` (Step 3's conclusion, a hypothesis of `STStep4R`), the R2* bootstrap `stOeqQt'_holds` and the averaged law. -/
theorem stStep4I_holds : ∀ d : ℕ, STStep4I d := fun d => step4_of_ing d STCaseI (stOeqQt'_holds d)

/-- **`stStep4II_holds`: Step 4 of `lem:main_ind`, case (ii) `1 - s ≤ ilambda²/L²`, for every `d`** (DECISIONS §133 (1);
check shape `T2321_stStep4II`): the same with the bootstrap `stOeqQtNZ'_holds`. -/
theorem stStep4II_holds : ∀ d : ℕ, STStep4II d := fun d => step4_of_ing d STCaseII (stOeqQtNZ'_holds d)

end RBM.Ind

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 3. `lem:main_ind` from the step pins still owed, with Step 3 at the consumed regimes -/

/-- **`lem:main_ind` from the step pins still owed, Step 3 at the regimes the assembly consumes** (primed successor of
`ST_mainInd_of_pins`, `MainIndRegimes.lean:674`; DECISIONS §132, §133 (2); check shape `T2321_mainInd_of_pins'`):
`STStep2`, Step 3 at `STReg5III`, `STReg5I` (`STStep3R d ·`) and `STStep3II`, `STStep5I/II`, `STStep6I/II/III`.  Step 4 is
proved (`stStep4I_holds`, `stStep4II_holds`), the other four step pins by `RBM.Green.stStep1_holds`, `stStep5III_holds`,
`stStep5IV_holds`, `stStep6IV_holds`.  Regimes (iii), (i) use `ST_mainIndR_of_steps` with `R34 = R` (Step 3 at the
regime itself; Step 4 by `step4R_mono` from case (i)), regimes (ii), (iv) the unprimed `ST_mainIndR_II/IV_of_steps`. -/
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

/-! ## 4. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.Step4Inst`.  Data (all merged): `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `C_d = 1`; case (i): `sz0`
(`L = 4(n+1)`, `W = (2(n+1))^5`, `ilambda = (2(n+1))^{-6}`), `z0`, `(s,t) = (0, 1/16)` (`sz0_caseI`); case (ii): `szB`
(`L = 4`, `W = n + 4`, `ilambda = 1`), `zB`, `(s,t) = (15/16, 31/32)` (`szB_caseII`: `1 - s = ilambda²/L²`);
`(con_st_ind)` for every `𝔠_d > 0` (`sz0_con`, `conStInd_const`).  `STKbound`, `STKward` are discharged (theorems of the
flow, `stKbound_of_flow`, `stKward_of_flow`); what stays a hypothesis is a premise that is another gate's pin (`STLK s`,
`STStep1Loop`, `STStep2Concl`, `STLmaxU` of Step 3, T2320).  The assembly is applied at `(szB, zB, 0, 31/32)` and at
`(sz0, z0, 0, 1/16)` with the nine step pins as hypotheses. -/

namespace RBM.Ind.Step4Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst
  RBM.Gauss.MainIndRegimesInst RBM.Path Filter

/-- The result of applying `STStep4R` at the data with `STKbound`, `STKward` discharged: the constant `𝔠_d`, then the
premises that are other gates' pins, then `(Eq:L-KGt-flow)` uniformly in `u`. -/
def Step4Concl (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLK sz (STflowE z) s → STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
      STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t)

/-- The common shape of the Step-4 instances: every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the
regime, `(con_st_ind)`, `C_d > 0`, `STKbound`, `STKward`) is discharged. -/
theorem inst_step4R_dis (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STStep4R 3 R)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    Step4Concl sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun ha h1' h2 h3 =>
    H (1 / 6) sz z hflow s t hs0 hst ht hR (stKbound_of_flow sz (by norm_num) (by norm_num) hflow)
      (stKward_of_flow sz (by norm_num) (by norm_num) hflow) ha (hcon 𝔠d h0) h1' h2 h3⟩

/-- **(1) `stStep4I_holds` at the data**: case (i) at `(sz0, z0, 0, 1/16)`, `C_d = 1`. -/
theorem inst_stStep4I : Step4Concl sz0 z0 sInst tInst 1 :=
  inst_step4R_dis STCaseI (stStep4I_holds 3) sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1
    one_pos

/-- **(2) `stStep4II_holds` at the data**: case (ii) at `(szB, zB, 15/16, 31/32)`, `C_d = 1`. -/
theorem inst_stStep4II : Step4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_step4R_dis STCaseII (stStep4II_holds 3) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- (1') the same through the merged `inst_step4I` (premises `STKbound`, `STKward` kept). -/
theorem inst_stStep4I' : InstStep4Concl sz0 z0 sInst tInst 1 := inst_step4I (stStep4I_holds 3) 1 one_pos

/-- (2') the same through the merged `inst_step4II`. -/
theorem inst_stStep4II' : InstStep4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_step4II (stStep4II_holds 3) 1 one_pos

/-- **(3) `ST_mainInd_of_pins'` applied** at `(szB, zB, 0, 31/32)` (the pattern `((i), (ii))` over three cuts; as
`inst_mainInd3_data`): the nine step pins are hypotheses, every deterministic hypothesis is discharged; only the
stochastic premises `(a)`-`(d)` at `s` stay. -/
theorem inst_mainInd3'_data (h2 : STStep2 3) (h3III : STStep3R 3 STReg5III) (h3I : STStep3R 3 STReg5I)
    (h3II : STStep3II 3) (h5I : STStep5I 3) (h5II : STStep5II 3) (h6I : STStep6I 3) (h6II : STStep6II 3)
    (h6III : STStep6III 3) :
    InstMainIndRConcl STAny szB zB (fun _ => 0) (fun _ => 31 / 32) :=
  inst_mainIndR _ ((ST_mainInd_iff_any 3).1 (ST_mainInd_of_pins' 3 h2 h3III h3I h3II h5I h5II h6I h6II h6III))
    szB zB flow_zB _ _ (fun _ => by norm_num) (szB_flow_ht (by norm_num)) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) trivial
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠)

/-- **(3')** `ST_mainInd_of_pins'` applied at `(sz0, z0, 0, 1/16)` (regime (iii) data of `sz0_reg5III`). -/
theorem inst_mainInd3'_sz0 (h2 : STStep2 3) (h3III : STStep3R 3 STReg5III) (h3I : STStep3R 3 STReg5I)
    (h3II : STStep3II 3) (h5I : STStep5I 3) (h5II : STStep5II 3) (h6I : STStep6I 3) (h6II : STStep6II 3)
    (h6III : STStep6III 3) :
    InstMainIndRConcl STAny sz0 z0 sInst tInst :=
  inst_mainIndR _ ((ST_mainInd_iff_any 3).1 (ST_mainInd_of_pins' 3 h2 h3III h3I h3II h5I h5II h6I h6II h6III))
    sz0 z0 flow_z0 sInst tInst sz0_hs0 (fun n => (sz0_hst n).le.trans (sz0_ht n)) sz0_hst sz0_ht trivial sz0_con

end RBM.Ind.Step4Inst

end

#print axioms RBM.Ind.stStep4I_holds
#print axioms RBM.Ind.stStep4II_holds
#print axioms RBM.Gauss.Sizes.ST_mainInd_of_pins'
#print axioms RBM.Ind.Step4Inst.inst_step4R_dis
#print axioms RBM.Ind.Step4Inst.inst_stStep4I
#print axioms RBM.Ind.Step4Inst.inst_stStep4II
#print axioms RBM.Ind.Step4Inst.inst_stStep4I'
#print axioms RBM.Ind.Step4Inst.inst_stStep4II'
#print axioms RBM.Ind.Step4Inst.inst_mainInd3'_data
#print axioms RBM.Ind.Step4Inst.inst_mainInd3'_sz0
