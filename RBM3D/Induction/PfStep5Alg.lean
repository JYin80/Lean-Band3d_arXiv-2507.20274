/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Induction.TailtoTail

/-!
# S5-10 (ST-4): the algebra of `lem:pf_step5`, part 1 (ticket T2209 with Amend 1)

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex:2296-2297` (`def_WTuD`), `:2310`
(`eq:def_new_J*`), `:2317-2338` (`lem_dec_calE`), `:2344-2362` (`TailtoTail`), `:2364-2369`
(`eq:def_TTT`, the stopped hierarchy `(int_K-L_ST)`), `:2371-2383` (`lem:pf_step5`; the paper omits
the proof, "analogous to, and much simpler than, `(2.76)` of [YY_25, §5.3]", `3_5:2380`).

This file is the deterministic algebra of the stopped hierarchy in regime (iii); no `Prec`
conclusion and no pin: `STPfStep5` is S5-11's.  Every statement is per time or deterministic
(DECISIONS §64 (4): nothing with the random right side `J♯^m R` is lifted).  The quadratic-variation
analogue of `TailtoTail` (target 7 of the ticket) is **not** here: Amend 1 moved it to S5-10a
(`Induction/TailtoTailSq`).  Targets, with the pins of the check file
`docs/tickets/checks/T2209-check.lean` (the `def … _pin` of section 1 are copies; the pins of
2′ and 4′ are new, from Amend 1):

* **1** `pfStep5Alg_tailAnti`: `T_{u,D'} ≤ T_{u,D}` for `D ≤ D'`.
* **2′** `pfStep5Alg_ugenSum'` (Amend 1: the level is a sequence `D : ℕ → ℝ`) and **2**
  `pfStep5Alg_ugenSum` (`D_j ≡ D`, a one-line corollary): the weighted sums of `𝒰_{u_j,u_k,σ} ∘ ℰ_j`
  against `T_{u_k,D_j}`, termwise `stTailtoTail_holds` at `D_j`.
* **3** `pfStep5Alg_riemann`: the three left Riemann sums of `(1-u)^{-2}`, `(1-u)^{-3/2}`,
  `(1-u)^{-1}` (telescoping inequalities, no integrals).
* **4′** `pfStep5Alg_goodStop'` (Amend 1: the good event may sit at another level `D₁`) and **4**
  `pfStep5Alg_goodStop` (`D₁ = D`): the stopping condition `J♯(u) ≤ W^ε` turns a good event of
  S5-09 into the one at the constant control `Jst ≡ W^ε`.
* **5** `pfStep5Alg_goodProb`: `lemDecCalEPrec_prob` at the crude control `Jst n u D = W^D`, whose
  hypothesis `STLK2 ≺ W^D T` follows from `STLKU` at `k = 2`, `Bctl ≤ 1` and `T ≥ W^{-D}`.
* **6** `pfStep5Alg_closure`: `N^τ C (1 + log W + W^{2ε} (ilambda² W^d)^{-1/4}) < W^ε` eventually.

Intended use by S5-11 (Amend 1, DECISIONS §70; one level per time `D_u := D* + 2 log_W (1-u)`,
`D* := max(D, D₀) + 2d + 1`): target 5 once at `D*`; at each grid time `u_j` target 4′ with
`(D, D₁) = (D_{u_j}, D*)` feeds `lemDecCalEPrec_goodDet` at the control `Jst ≡ W^ε`; the drift
terms go through target 2′ at the levels `D_{u_j}` and target 3; target 6 closes the sum; target 1
descends from `D_u ≥ D` to `D`.

No private proof is copied from another file; target 2′ uses the public `stTailtoTail_holds`
(`Induction/TailtoTail.lean:582`, constant `(3 e^{(4d+1)/4})²`).  Section 8 holds the compiled
nonempty instances.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Green

/-! ## 1. The pins (copies of the check file `docs/tickets/checks/T2209-check.lean`, section 1) -/

/-- **Target 1** (descent in `D`, `STPfConcl` docstring `Step5Pins.lean:195-201`): `T_{u,D'} ≤ T_{u,D}` for
`D ≤ D'` (`W ≥ 1`). -/
def PfStep5Alg_tailAnti_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (n : ℕ) (u D D' : ℝ) (a : Fin 2 → Zd d (sz.L n)), D ≤ D' →
    STtailTD sz n u D' a ≤ STtailTD sz n u D a

/-- **Target 2** (kernel sums, the `Ugen` form of `stTailtoTail_holds`; `EKsgn (mE E) σ` is
`fun i => mSigma E (σ i)`, `‖mE E‖ = 1` by `norm_mE`): for nonnegative weights `c j` and tensors
`ℰ j` dominated by `p j · T_{u_j,D}`, the weighted sum of `𝒰_{u_j,u_k,σ} ∘ ℰ_j` is dominated by
`Σ c_j p_j (C T_{u_k,D} + ((1-u_j)/(1-u_k))² W^{-D})`, `C` the constant of `STTailtoTail`. -/
def PfStep5Alg_ugenSum_pin (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D E : ℝ), 0 < g → 0 < W → |E| ≤ 2 →
      ∀ (σ : Fin 2 → Bool) (k : ℕ) (u c p : ℕ → ℝ) (ℰ : ℕ → (Fin 2 → Zd d L) → ℂ),
        0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 → g ^ 2 ≤ 1 - u k → (∀ j, 0 ≤ c j) →
        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) D (zdistInf d L (b 0 - b 1) : ℝ)) →
        ∀ a, ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ ≤
          ∑ j ∈ Finset.range k, c j * p j *
            (C * tailTD d W (u k) D (zdistInf d L (a 0 - a 1) : ℝ) +
              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-D))

/-- **Target 2′** (Amend 1, DECISIONS §70: pin 2 with the level a sequence `D : ℕ → ℝ`, one extra binder): the
tensors `ℰ j` are dominated by `p j · T_{u_j,D_j}` and the weighted sum of `𝒰_{u_j,u_k,σ} ∘ ℰ_j` by
`Σ c_j p_j (C T_{u_k,D_j} + ((1-u_j)/(1-u_k))² W^{-D_j})`; pin 2 is the case `D_j ≡ D`. -/
def PfStep5Alg_ugenSum'_pin (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W E : ℝ) (D : ℕ → ℝ), 0 < g → 0 < W → |E| ≤ 2 →
      ∀ (σ : Fin 2 → Bool) (k : ℕ) (u c p : ℕ → ℝ) (ℰ : ℕ → (Fin 2 → Zd d L) → ℂ),
        0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 → g ^ 2 ≤ 1 - u k → (∀ j, 0 ≤ c j) →
        (∀ j, j < k → ∀ b, ‖ℰ j b‖ ≤ p j * tailTD d W (u j) (D j) (zdistInf d L (b 0 - b 1) : ℝ)) →
        ∀ a, ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ ≤
          ∑ j ∈ Finset.range k, c j * p j *
            (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
              ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j)))

/-- **Target 3** (left Riemann sums of the increasing functions `(1-u)^{-2}`, `(1-u)^{-3/2}`, `(1-u)^{-1}`):
the time integrals `∫_s^{t'} (1-u)^{-2} du ≤ (1-t')^{-1}` etc. of Fable §4(3) on a grid. -/
def PfStep5Alg_riemann_pin : Prop :=
  ∀ (k : ℕ) (u : ℕ → ℝ), 0 ≤ u 0 → (∀ j, u j ≤ u (j + 1)) → u k < 1 →
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹ ^ 2 ≤ (1 - u k)⁻¹ ∧
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ) ≤
      2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) ∧
    ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹ ≤ Real.log ((1 - u 0) / (1 - u k))

/-- **Target 4** (the stopped control feeds S5-09's per-time good event): if the realized control is
`J♯(u) ≤ W^ε` (the stopping condition), the good event of `lemDecCalEPrec_good` at any control `J₀`
is inside the good event at the constant control `Jst ≡ W^ε` (conjunct 1 by `LemDecCalELip_Jsharp_basic`,
conjuncts 2-7 do not depend on `Jst`). -/
def PfStep5Alg_goodStop_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
    1 ≤ ((sz.size n : ℕ) : ℝ) →
    LemDecCalELip_Jsharp sz E D n u ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ω ∈ lemDecCalEPrec_good sz E D J₀ τ' n u →
    ω ∈ lemDecCalEPrec_good sz E D (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε) τ' n u

/-- **Target 4′** (Amend 1: the good event is taken at a level `D₁` independent of the level `D` of the
conclusion and of the stopping condition; events 2-7 of `lemDecCalEPrec_good` contain neither `D` nor `Jst`);
pin 4 is the case `D₁ = D`. -/
def PfStep5Alg_goodStop'_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D D₁ ε τ' : ℝ) (J₀ : ℕ → ℝ → ℝ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ), 0 ≤ τ' →
    1 ≤ ((sz.size n : ℕ) : ℝ) →
    LemDecCalELip_Jsharp sz E D n u ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε →
    ω ∈ lemDecCalEPrec_good sz E D₁ J₀ τ' n u →
    ω ∈ lemDecCalEPrec_good sz E D (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε) τ' n u

/-- **Target 5** (probability of the good event without the circular hypothesis): `lemDecCalEPrec_prob` at the
crude control `Jst n u D = W^D`, whose hypothesis `STLK2 ≺ W^D T` follows from `STLKU` at `k = 2`, `Bctl ≤ 1`
and `T ≥ W^{-D}` (`lemDecCalEPrec_tail_ge`). -/
def PfStep5Alg_goodProb_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E s t : ℕ → ℝ) (D : ℝ), sz.SizeTendsto →
    (∀ᶠ n in atTop, ∀ u : TimeIcc s t n, sz.Bctl n (u : ℝ) ≤ 1) →
    STLKU sz E s t → STLocalEntryU sz E s t → STAvgU sz E s t → STLmaxU sz E s t →
    GijGEXPTSwap sz E s t →
    ∀ τ' D₁ : ℝ, 0 < τ' → 0 < D₁ →
      ∀ᶠ n in atTop, ∀ u : TimeIcc s t n,
        sz.seqP (lemDecCalEPrec_good sz E D (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') τ' n (u : ℝ))ᶜ ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁))

/-- **Target 6** (the closure, Fable §4(3) last line): for `0 < ε < 𝔡/4` and every `C ≥ 0` there is `τ > 0`
with `N^τ · C (1 + log W + W^{2ε} (ilambda² W^d)^{-1/4}) < W^ε` eventually (`(eq:WO)` gives
`(ilambda² W^d)^{-1/4} ≤ W^{-𝔡/2}`, `Bandwidth` gives `N^τ ≤ W^{τ/𝔠}`). -/
def PfStep5Alg_closure_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, sz.Admissible 𝔠 𝔡 → ∀ ε C : ℝ, 0 < ε → ε < 𝔡 / 4 → 0 ≤ C →
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ n in atTop,
      ((sz.size n : ℕ) : ℝ) ^ τ *
          (C * (1 + Real.log ((sz.W n : ℕ) : ℝ) +
            ((sz.W n : ℕ) : ℝ) ^ (2 * ε) * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) <
        ((sz.W n : ℕ) : ℝ) ^ ε

/-! ## 2. Target 1: descent in `D` -/

/-- **Target 1**: `T_{u,D'} ≤ T_{u,D}` for `D ≤ D'` (the amplitude is the same, `W^{-D'} ≤ W^{-D}` as `W ≥ 1`). -/
theorem pfStep5Alg_tailAnti {d : ℕ} (sz : Sizes d) : PfStep5Alg_tailAnti_pin sz := by
  intro n u D D' a hDD'
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h := Real.rpow_le_rpow_of_exponent_le hW (neg_le_neg hDD')
  unfold STtailTD tailTD
  linarith

/-! ## 3. Target 2′ and target 2: the kernel sums -/

section UgenSum

/-- `UN` is linear in the tensor: a scalar factor of the tensor comes out. -/
private theorem pfStep5Alg_UN_smul {n d L : ℕ} [NeZero L] (g : ℝ) (m : Fin n → ℂ) (s t : ℝ) (c : ℂ)
    (A : (Fin n → Zd d L) → ℂ) (a : Fin n → Zd d L) :
    UN d L g m s t (fun b => c * A b) a = c * UN d L g m s t A a := by
  unfold UN
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `tailTD > 0` for `W > 0`. -/
private theorem pfStep5Alg_tailTD_pos {d : ℕ} {W u D r : ℝ} (hW : 0 < W) : 0 < tailTD d W u D r := by
  unfold tailTD
  have := Real.rpow_pos_of_pos hW (-D)
  positivity

/-- One term of target 2′: `‖(𝒰_{v,w,σ} ∘ ℰ)_a‖ ≤ p (C T_{w,D'} + ((1-v)/(1-w))² W^{-D'})` when
`‖ℰ_b‖ ≤ p T_{v,D'}(|b₁-b₂|)`, from the constant `C` of `STTailtoTail`. -/
private theorem pfStep5Alg_ugen_term {d : ℕ} {C : ℝ}
    (H : ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D))
    {L : ℕ} [NeZero L] (hL : 3 ≤ L) {g W E v w D' p : ℝ} (hg : 0 < g) (hW : 0 < W) (hE : |E| ≤ 2)
    (σ : Fin 2 → Bool) (ℰ : (Fin 2 → Zd d L) → ℂ) (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (hgw : g ^ 2 ≤ 1 - w) (hℰ : ∀ b, ‖ℰ b‖ ≤ p * tailTD d W v D' (zdistInf d L (b 0 - b 1) : ℝ))
    (a : Fin 2 → Zd d L) :
    ‖RBM.Ind.Ugen d L g E σ v w ℰ a‖ ≤
      p * (C * tailTD d W w D' (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - v) / (1 - w)) ^ 2 * W ^ (-D')) := by
  have hT : 0 < tailTD d W v D' (zdistInf d L ((fun _ => 0 : Fin 2 → Zd d L) 0 - (fun _ => 0 : Fin 2 → Zd d L) 1) : ℝ) :=
    pfStep5Alg_tailTD_pos hW
  have hp0 : 0 ≤ p := by
    by_contra hneg
    have hneg := not_le.1 hneg
    have h1 := hℰ (fun _ => 0)
    have h2 := mul_neg_of_neg_of_pos hneg hT
    linarith [norm_nonneg (ℰ (fun _ => 0))]
  rcases hp0.eq_or_lt with hp | hp
  · -- `p = 0`: `ℰ = 0`
    have hz : ∀ b, ℰ b = 0 := fun b => by
      have := hℰ b
      rw [← hp, zero_mul] at this
      exact norm_le_zero_iff.1 this
    have h0 : RBM.Ind.Ugen d L g E σ v w ℰ a = 0 := by
      unfold RBM.Ind.Ugen UN
      simp [hz]
    rw [h0, norm_zero, ← hp, zero_mul]
  · -- `p > 0`: scale by `p⁻¹`
    set A : (Fin 2 → Zd d L) → ℂ := fun b => (((p⁻¹ : ℝ)) : ℂ) * ℰ b with hA
    have hAb : ∀ b, ‖A b‖ ≤ tailTD d W v D' (zdistInf d L (b 0 - b 1) : ℝ) := fun b => by
      rw [hA, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hp.le)]
      calc p⁻¹ * ‖ℰ b‖ ≤ p⁻¹ * (p * tailTD d W v D' (zdistInf d L (b 0 - b 1) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hℰ b) (inv_nonneg.2 hp.le)
        _ = tailTD d W v D' (zdistInf d L (b 0 - b 1) : ℝ) := by field_simp
    have hℰA : ℰ = fun b => ((p : ℝ) : ℂ) * A b := by
      funext b
      rw [hA]
      simp only
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hp.ne', Complex.ofReal_one, one_mul]
    have hUN := H L hL g W D' v w hg hW hv0 hvw hw1 hgw (mE E) (norm_mE hE) σ A hAb a
    have hUg : RBM.Ind.Ugen d L g E σ v w ℰ a = ((p : ℝ) : ℂ) * UN d L g (EKsgn (mE E) σ) v w A a := by
      rw [hℰA]
      exact pfStep5Alg_UN_smul g (EKsgn (mE E) σ) v w ((p : ℝ) : ℂ) A a
    rw [hUg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le]
    exact mul_le_mul_of_nonneg_left hUN hp.le

end UgenSum

/-- **Target 2′** (Amend 1): the weighted kernel sums with a level `D_j` per term.  Termwise
`stTailtoTail_holds` at `D_j` (scaling by `p_j`, `p_j = 0 ⇒ ℰ_j = 0`, `EKsgn (mE E) σ = fun i => mSigma E (σ i)`
by `rfl`, `‖mE E‖ = 1`), then the triangle inequality. -/
theorem pfStep5Alg_ugenSum' (d : ℕ) : PfStep5Alg_ugenSum'_pin d := by
  intro hd
  obtain ⟨C, hC, H⟩ := stTailtoTail_holds d hd
  refine ⟨C, hC, ?_⟩
  intro L _ hL g W E D hg hW hE σ k u c p ℰ hu0 hmono hk hgk hc hℰ a
  have hm : Monotone u := monotone_nat_of_le_succ hmono
  have term : ∀ j ∈ Finset.range k, ‖RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ ≤
      p j * (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
        ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j))) := fun j hj => by
    have hjk : j < k := Finset.mem_range.1 hj
    exact pfStep5Alg_ugen_term H hL hg hW hE σ (ℰ j) (hu0.trans (hm (Nat.zero_le j))) (hm hjk.le) hk hgk
      (hℰ j hjk) a
  calc ‖∑ j ∈ Finset.range k, ((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖
      ≤ ∑ j ∈ Finset.range k, ‖((c j : ℝ) : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ :=
        norm_sum_le _ _
    _ = ∑ j ∈ Finset.range k, c j * ‖RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖ :=
        Finset.sum_congr rfl fun j _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc j)]
    _ ≤ ∑ j ∈ Finset.range k, c j * p j *
          (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
            ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j))) :=
        Finset.sum_le_sum fun j hj => by
          calc c j * ‖RBM.Ind.Ugen d L g E σ (u j) (u k) (ℰ j) a‖
              ≤ c j * (p j * (C * tailTD d W (u k) (D j) (zdistInf d L (a 0 - a 1) : ℝ) +
                ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(D j)))) :=
                mul_le_mul_of_nonneg_left (term j hj) (hc j)
            _ = _ := by ring

/-- **Target 2**: `D_j ≡ D` in target 2′. -/
theorem pfStep5Alg_ugenSum (d : ℕ) : PfStep5Alg_ugenSum_pin d := by
  intro hd
  obtain ⟨C, hC, H⟩ := pfStep5Alg_ugenSum' d hd
  refine ⟨C, hC, ?_⟩
  intro L _ hL g W D E hg hW hE σ k u c p ℰ hu0 hmono hk hgk hc hℰ a
  exact H L hL g W E (fun _ => D) hg hW hE σ k u c p ℰ hu0 hmono hk hgk hc hℰ a

/-! ## 4. Target 3: the left Riemann sums -/

section Riemann

/-- `(b-a)(1-a)^{-2} ≤ (1-b)^{-1} - (1-a)^{-1}` for `a ≤ b < 1`:
the difference is `(b-a)² / ((1-a)² (1-b))`. -/
private theorem pfStep5Alg_riem1 {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (b - a) * ((1 - a)⁻¹) ^ 2 ≤ (1 - b)⁻¹ - (1 - a)⁻¹ := by
  have hy : 0 < 1 - b := by linarith
  have hx : 0 < 1 - a := by linarith
  have e : (1 - b)⁻¹ - (1 - a)⁻¹ - (b - a) * ((1 - a)⁻¹) ^ 2 =
      (b - a) ^ 2 / ((1 - a) ^ 2 * (1 - b)) := by
    field_simp
    ring
  have : 0 ≤ (b - a) ^ 2 / ((1 - a) ^ 2 * (1 - b)) := by positivity
  linarith

/-- The algebra of the second Riemann sum: for `0 < r ≤ R`, `(r⁻² - R⁻²) r³ ≤ 2 (R - r)`
(the difference is `(R-r)² (2R + r) / R²`). -/
private theorem pfStep5Alg_riem2_alg {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ((r ^ 2)⁻¹ - (R ^ 2)⁻¹) * r ^ 3 ≤ 2 * (R - r) := by
  have hR : 0 < R := hr.trans_le hrR
  have e : 2 * (R - r) - ((r ^ 2)⁻¹ - (R ^ 2)⁻¹) * r ^ 3 = (R - r) ^ 2 * (2 * R + r) / R ^ 2 := by
    field_simp
    ring
  have : 0 ≤ (R - r) ^ 2 * (2 * R + r) / R ^ 2 := by positivity
  linarith

/-- `(b-a)(1-a)^{-3/2} ≤ 2 ((1-b)^{-1/2} - (1-a)^{-1/2})` for `a ≤ b < 1`
(`r = (1-a)^{-1/2}`, `R = (1-b)^{-1/2}`). -/
private theorem pfStep5Alg_riem2 {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (b - a) * ((1 - a)⁻¹) ^ (3 / 2 : ℝ) ≤
      2 * (((1 - b)⁻¹) ^ (1 / 2 : ℝ) - ((1 - a)⁻¹) ^ (1 / 2 : ℝ)) := by
  have hx : 0 < 1 - a := by linarith
  have hy : 0 < 1 - b := by linarith
  have hp0 : 0 < (1 - a)⁻¹ := inv_pos.2 hx
  have hq0 : 0 < (1 - b)⁻¹ := inv_pos.2 hy
  have hpq : (1 - a)⁻¹ ≤ (1 - b)⁻¹ := inv_anti₀ hy (by linarith)
  have hr0 : 0 < Real.sqrt ((1 - a)⁻¹) := Real.sqrt_pos.2 hp0
  have hrR : Real.sqrt ((1 - a)⁻¹) ≤ Real.sqrt ((1 - b)⁻¹) := Real.sqrt_le_sqrt hpq
  have hr2 : Real.sqrt ((1 - a)⁻¹) ^ 2 = (1 - a)⁻¹ := Real.sq_sqrt hp0.le
  have hR2 : Real.sqrt ((1 - b)⁻¹) ^ 2 = (1 - b)⁻¹ := Real.sq_sqrt hq0.le
  have e1 : ((1 - a)⁻¹) ^ (1 / 2 : ℝ) = Real.sqrt ((1 - a)⁻¹) := (Real.sqrt_eq_rpow _).symm
  have e2 : ((1 - b)⁻¹) ^ (1 / 2 : ℝ) = Real.sqrt ((1 - b)⁻¹) := (Real.sqrt_eq_rpow _).symm
  have e3 : ((1 - a)⁻¹) ^ (3 / 2 : ℝ) = Real.sqrt ((1 - a)⁻¹) ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one, e1]
    nth_rewrite 1 [← hr2]
    ring
  have hba : b - a = ((1 - a)⁻¹)⁻¹ - ((1 - b)⁻¹)⁻¹ := by rw [inv_inv, inv_inv]; ring
  have key := pfStep5Alg_riem2_alg hr0 hrR
  rw [e3, e1, e2, hba]
  rw [hr2, hR2] at key
  exact key

/-- `(b-a)(1-a)^{-1} ≤ log ((1-a)/(1-b))` for `a ≤ b < 1` (`log x ≥ 1 - 1/x`). -/
private theorem pfStep5Alg_riem3 {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (b - a) * (1 - a)⁻¹ ≤ Real.log ((1 - a) / (1 - b)) := by
  have hx : 0 < 1 - a := by linarith
  have hy : 0 < 1 - b := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  rw [Real.log_div hx.ne' hy.ne']
  have e : (b - a) * (1 - a)⁻¹ = 1 - (1 - b) / (1 - a) := by
    field_simp
    ring
  rw [e]
  linarith

end Riemann

/-- **Target 3**: the three left Riemann sums on a grid `u₀ ≤ u₁ ≤ … ≤ u_k < 1`. -/
theorem pfStep5Alg_riemann : PfStep5Alg_riemann_pin := by
  intro k u hu0 hmono hk
  have hm : Monotone u := monotone_nat_of_le_succ hmono
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => (hm hj).trans_lt hk
  have h10 : 0 < 1 - u 0 := by linarith [hlt 0 (Nat.zero_le k)]
  have h1k : 0 < 1 - u k := by linarith
  refine ⟨?_, ?_, ?_⟩
  · calc ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹ ^ 2
        ≤ ∑ j ∈ Finset.range k, ((1 - u (j + 1))⁻¹ - (1 - u j)⁻¹) :=
          Finset.sum_le_sum fun j hj =>
            pfStep5Alg_riem1 (hmono j) (hlt (j + 1) (Finset.mem_range.1 hj))
      _ = (1 - u k)⁻¹ - (1 - u 0)⁻¹ := Finset.sum_range_sub (fun j => (1 - u j)⁻¹) k
      _ ≤ (1 - u k)⁻¹ := by
          have : 0 ≤ (1 - u 0)⁻¹ := inv_nonneg.2 h10.le
          linarith
  · calc ∑ j ∈ Finset.range k, (u (j + 1) - u j) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)
        ≤ ∑ j ∈ Finset.range k, 2 * (((1 - u (j + 1))⁻¹) ^ (1 / 2 : ℝ) - ((1 - u j)⁻¹) ^ (1 / 2 : ℝ)) :=
          Finset.sum_le_sum fun j hj =>
            pfStep5Alg_riem2 (hmono j) (hlt (j + 1) (Finset.mem_range.1 hj))
      _ = 2 * (((1 - u k)⁻¹) ^ (1 / 2 : ℝ) - ((1 - u 0)⁻¹) ^ (1 / 2 : ℝ)) := by
          rw [← Finset.mul_sum]
          congr 1
          exact Finset.sum_range_sub (fun j => ((1 - u j)⁻¹) ^ (1 / 2 : ℝ)) k
      _ ≤ 2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) := by
          have : 0 ≤ ((1 - u 0)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (inv_nonneg.2 h10.le) _
          linarith
  · calc ∑ j ∈ Finset.range k, (u (j + 1) - u j) * (1 - u j)⁻¹
        ≤ ∑ j ∈ Finset.range k, Real.log ((1 - u j) / (1 - u (j + 1))) :=
          Finset.sum_le_sum fun j hj =>
            pfStep5Alg_riem3 (hmono j) (hlt (j + 1) (Finset.mem_range.1 hj))
      _ = ∑ j ∈ Finset.range k, (Real.log (1 - u j) - Real.log (1 - u (j + 1))) :=
          Finset.sum_congr rfl fun j hj => by
            have h1 : 0 < 1 - u j := by linarith [hlt j (Finset.mem_range.1 hj).le]
            have h2 : 0 < 1 - u (j + 1) := by linarith [hlt (j + 1) (Finset.mem_range.1 hj)]
            exact Real.log_div h1.ne' h2.ne'
      _ = Real.log (1 - u 0) - Real.log (1 - u k) :=
          Finset.sum_range_sub' (fun j => Real.log (1 - u j)) k
      _ = Real.log ((1 - u 0) / (1 - u k)) := (Real.log_div h10.ne' h1k.ne').symm

/-! ## 5. Targets 4′ and 4: the stopping condition and the good event -/

/-- **Target 4′** (Amend 1): conjunct 1 of `lemDecCalEPrec_good` at the constant control `Jst ≡ W^ε` and level `D` is the
stopping condition `J♯ ≤ W^ε` (`LemDecCalELip_Jsharp_basic`: `STLK2 ≤ J♯ T`; `N^{τ'} ≥ 1`, `T > 0`), and conjuncts 2-7
(`STGM`, `Gt`, the one-, three-, four- and six-loop clauses) contain neither `D` nor the control, so they are
those of the good event at `(D₁, J₀)`. -/
theorem pfStep5Alg_goodStop' {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop'_pin sz := by
  intro E D D₁ ε τ' J₀ n u ω hτ' hN hJ hω
  obtain ⟨-, g2, g3, g4, g53, g54, g56⟩ := hω
  refine ⟨fun σ a => ?_, g2, g3, g4, g53, g54, g56⟩
  have hb := LemDecCalELip_Jsharp_basic sz E D n u ω
  have hT := LemDecCalELip_tail_pos sz n u D a
  have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN hτ'
  have h1 : STLK2 sz n (E n) u σ a ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε * STtailTD sz n u D a :=
    (hb.2.1 σ a).trans (mul_le_mul_of_nonneg_right hJ hT.le)
  have h0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ ε * STtailTD sz n u D a :=
    mul_nonneg (Real.rpow_nonneg hW0 _) hT.le
  calc STLK2 sz n (E n) u σ a ω ≤ ((sz.W n : ℕ) : ℝ) ^ ε * STtailTD sz n u D a := h1
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.W n : ℕ) : ℝ) ^ ε * STtailTD sz n u D a) :=
        le_mul_of_one_le_left h0 hQ

/-- **Target 4**: the case `D₁ = D` of target 4′. -/
theorem pfStep5Alg_goodStop {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodStop_pin sz := by
  intro E D ε τ' J₀ n u ω hτ' hN hJ hω
  exact pfStep5Alg_goodStop' sz E D D ε τ' J₀ n u ω hτ' hN hJ hω

/-! ## 6. Target 5: the probability of the good event -/

/-- `Bctl ≥ 0` (`Bparam` is built from inverses of nonnegative terms). -/
private theorem pfStep5Alg_Bctl_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (u : ℝ) : 0 ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  positivity

/-- **Target 5**: the hypothesis `STLK2 ≺ W^D T` of `lemDecCalEPrec_prob` at `Jst n u D = W^D` from `STLKU` at `k = 2`:
`Bctl² ≤ 1 ≤ W^D · W^{-D} ≤ W^D T` (`Bctl ≤ 1`, `lemDecCalEPrec_tail_ge`), through `st5_prec_mono`. -/
theorem pfStep5Alg_goodProb {d : ℕ} (sz : Sizes d) : PfStep5Alg_goodProb_pin sz := by
  intro E s t D hsize hB hLKU hLoc hAvg hLmax hGij τ' D₁ hτ' hD₁
  have hLK : sz.Prec (U := STIdx2 sz s t) (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => ((sz.W n : ℕ) : ℝ) ^ D * STtailTD sz n (p.1 : ℝ) D p.2.2) := by
    refine st5_prec_mono sz hsize (c := 1) (hLKU 2 (by norm_num)) ?_ ?_
    · filter_upwards [hB] with n hn
      intro p ω
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have hb0 := pfStep5Alg_Bctl_nonneg sz n (p.1 : ℝ)
      have hb1 := hn p.1
      have hT := lemDecCalEPrec_tail_ge sz n (p.1 : ℝ) D p.2.2
      have h1 : ((sz.W n : ℕ) : ℝ) ^ D * ((sz.W n : ℕ) : ℝ) ^ (-D) = 1 := by
        rw [← Real.rpow_add hW0, add_neg_cancel, Real.rpow_zero]
      have h2 : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ D * STtailTD sz n (p.1 : ℝ) D p.2.2 := by
        calc (1 : ℝ) = ((sz.W n : ℕ) : ℝ) ^ D * ((sz.W n : ℕ) : ℝ) ^ (-D) := h1.symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hT (Real.rpow_nonneg hW0.le _)
      have h3 : sz.Bctl n (p.1 : ℝ) ^ 2 ≤ 1 := by nlinarith
      linarith
    · intro n p ω
      have hW0 : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
      exact mul_nonneg (Real.rpow_nonneg hW0 _) (LemDecCalELip_tail_pos sz n (p.1 : ℝ) D p.2.2).le
  exact lemDecCalEPrec_prob sz E s t (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') D hsize hLK hLoc hAvg hLmax hGij
    hτ' hD₁

/-! ## 7. Target 6: the closure -/

/-- **Target 6**: with `τ = 𝔠 ε / 2`: `N^τ ≤ W^{ε/2}` (`Bandwidth`), `(ilambda² W^d)^{-1/4} ≤ W^{-𝔡/2}` (`(eq:WO)`),
`W^{2ε - 𝔡/2} ≤ 1`, `log W ≤ (4/ε) W^{ε/4}`, and `W^{ε/4} ≥ 4C/ε + 2C + 1` eventually (`W → ∞`), so
`C (2 + log W) < W^{ε/2}` and the product is `< W^ε`. -/
theorem pfStep5Alg_closure {d : ℕ} (sz : Sizes d) : PfStep5Alg_closure_pin sz := by
  intro 𝔠 𝔡 hA ε C hε hε𝔡 hC
  obtain ⟨h𝔠, h𝔡, hsize, hBW, hWO⟩ := hA
  refine ⟨𝔠 * ε / 2, by positivity, ?_⟩
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsize
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hBW.mono fun n hn => hn) hNc
  have hε4 : 0 < ε / 4 := by positivity
  have hWε : ∀ᶠ n in atTop, 4 * C / ε + 2 * C + 1 ≤ ((sz.W n : ℕ) : ℝ) ^ (ε / 4) :=
    ((tendsto_rpow_atTop hε4).comp hWt).eventually_ge_atTop _
  filter_upwards [hBW, hWO, hWε, hWt.eventually_ge_atTop 1] with n hBWn hWOn hKn hW1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hW
  -- `N^τ ≤ W^{ε/2}`
  have hNτ : N ^ (𝔠 * ε / 2) ≤ W ^ (ε / 2) := by
    have h1 : (N ^ 𝔠) ^ (ε / 2) ≤ W ^ (ε / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hBWn (by positivity)
    rwa [← Real.rpow_mul hN0.le, ← mul_div_assoc] at h1
  -- `(ilambda² W^d)^{-1/4} ≤ W^{-𝔡/2}`
  have hlam : W ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * W ^ d := sz.lam_sq_mul_pow_ge n hWOn.1
  have hq : (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) ≤ W ^ (-𝔡 / 2) := by
    have h1 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hW0 _) hlam
      (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    rwa [← Real.rpow_mul hW0.le, show 2 * 𝔡 * (-(1 / 4 : ℝ)) = -𝔡 / 2 by ring] at h1
  -- `W^{2ε} (ilambda² W^d)^{-1/4} ≤ 1`
  have hsmall : W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
    calc W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) ≤ W ^ (2 * ε) * W ^ (-𝔡 / 2) :=
          mul_le_mul_of_nonneg_left hq (Real.rpow_nonneg hW0.le _)
      _ = W ^ (2 * ε + -𝔡 / 2) := (Real.rpow_add hW0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
  -- `log W ≤ (4/ε) W^{ε/4}`
  have hlog : Real.log W ≤ W ^ (ε / 4) / (ε / 4) := Real.log_le_rpow_div hW0.le hε4
  set y : ℝ := W ^ (ε / 4) with hy
  have hy1 : 1 ≤ y := by
    have : (1 : ℝ) ≤ 4 * C / ε + 2 * C + 1 := by
      have : 0 ≤ 4 * C / ε + 2 * C := by positivity
      linarith
    linarith
  have hyy : W ^ (ε / 2) = y * y := by
    rw [hy, ← Real.rpow_add hW0]
    congr 1
    ring
  have hWε' : W ^ ε = W ^ (ε / 2) * W ^ (ε / 2) := by
    rw [← Real.rpow_add hW0]
    congr 1
    ring
  have hlog0 : 0 ≤ Real.log W := Real.log_nonneg hW1
  -- `C (2 + log W) < W^{ε/2}`
  have hX : C * (1 + Real.log W + W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) < W ^ (ε / 2) := by
    have h1 : C * (1 + Real.log W + W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) ≤
        C * (2 + Real.log W) := mul_le_mul_of_nonneg_left (by linarith) hC
    have h2 : C * (2 + Real.log W) ≤ 2 * C + C * (y / (ε / 4)) := by
      have := mul_le_mul_of_nonneg_left hlog hC
      linarith
    have h3 : C * (y / (ε / 4)) = 4 * C / ε * y := by
      field_simp
    have h4 : (4 * C / ε + 2 * C + 1) * y ≤ y * y := mul_le_mul_of_nonneg_right hKn (by linarith)
    rw [hyy]
    nlinarith
  have hXnn : 0 ≤ C * (1 + Real.log W + W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) :=
    mul_nonneg hC (by have := Real.rpow_nonneg hW0.le (2 * ε); have := Real.rpow_nonneg (by positivity : 0 ≤ sz.lam n ^ 2 * W ^ d) (-(1 / 4 : ℝ)); positivity)
  have hWh : 0 < W ^ (ε / 2) := Real.rpow_pos_of_pos hW0 _
  calc N ^ (𝔠 * ε / 2) * (C * (1 + Real.log W + W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))))
      ≤ W ^ (ε / 2) * (C * (1 + Real.log W + W ^ (2 * ε) * (sz.lam n ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hNτ hXnn
    _ < W ^ (ε / 2) * W ^ (ε / 2) := mul_lt_mul_of_pos_left hX hWh
    _ = W ^ ε := hWε'.symm

/-! ## 8. Compiled nonempty instances (CLAUDE.md §4 step 2)

Data: the merged preflight instance `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_n = (W_n L_n)^3`, `n = 0`: `L = 4`,
`W = 32`, `N = 2097152`; `Admissible (1/6) (1/10)`), the flow `z0`, `s ≡ 0`, `t ≡ 1/16`; `d = 3`, `L = 4`, `g = 1/64`
(`g² = 1/4096 ≤ 15/16 = 1 - 1/16`), `W = 32`, `E = 0`.  The events of the sample `ω` (the stopping condition and the good
event of targets 4, 4′) and the stochastic pins of target 5 (`STLKU, STLocalEntryU, STAvgU, STLmaxU, GijGEXPTSwap`: other
gates' pins) stay hypotheses of their instance theorems; every deterministic hypothesis is discharged.  Given the five
pins, the events of targets 4, 4′ are jointly satisfiable at `sz0` (`pfStep5Alg_inst_goodStop'_nonvac`: target 5 gives
a sample in the good event, and the stopping condition holds on it at `ε = D₁ + 6/100`). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- The point `a = ((0,0,0), (1,1,1)) ∈ (Z_4^3)²` of the instances: the two components are at distance `1`. -/
private def pfStep5Alg_instA : Fin 2 → Zd 3 (sz0.L 0) := fun i _ => ((i : ℕ) : ZMod (sz0.L 0))

/-- The two components of `pfStep5Alg_instA` are at `zdistInf`-distance `1` (the point is not collapsed). -/
theorem pfStep5Alg_instA_dist : zdistInf 3 (sz0.L 0) (pfStep5Alg_instA 0 - pfStep5Alg_instA 1) = 1 := by
  decide

/-- Target 1 at `sz0`, `n = 0`, `u = 1/16`, `D = 1 ≤ 48 = D'`. -/
theorem pfStep5Alg_inst_tailAnti : STtailTD sz0 0 (1 / 16) 48 pfStep5Alg_instA ≤ STtailTD sz0 0 (1 / 16) 1 pfStep5Alg_instA :=
  pfStep5Alg_tailAnti sz0 0 (1 / 16) 1 48 pfStep5Alg_instA (by norm_num)

/-- The same data, strict: `W = 32 > 1`, `D < D'`, so the descent is not an equality. -/
theorem pfStep5Alg_inst_tailAnti_strict : STtailTD sz0 0 (1 / 16) 48 pfStep5Alg_instA < STtailTD sz0 0 (1 / 16) 1 pfStep5Alg_instA := by
  have hW : (1 : ℝ) < ((sz0.W 0 : ℕ) : ℝ) := by
    rw [sz0_values.2.1]; norm_num
  have h := Real.rpow_lt_rpow_of_exponent_lt hW (show -(48 : ℝ) < -1 by norm_num)
  unfold STtailTD tailTD
  linarith

/-- The levels and weights of the instances of targets 2′, 2: `u_j = j/48` (`k = 3`, `u_3 = 1/16`), `c_j = 1/48`,
`p_j = D_j = j + 1`. -/
private def pfStep5Alg_instU (j : ℕ) : ℝ := (j : ℝ) / 48

private theorem pfStep5Alg_instU_mono (j : ℕ) : pfStep5Alg_instU j ≤ pfStep5Alg_instU (j + 1) := by
  unfold pfStep5Alg_instU
  push_cast
  linarith

/-- **Target 2′ at `d = 3`, `L = 4`, `ℰ ≡ 0`**: three terms with three different levels `D_j = j + 1`, `p_j = j + 1`. -/
theorem pfStep5Alg_inst_ugenSum'_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
      ‖∑ j ∈ Finset.range 3, (((1 / 48 : ℝ)) : ℂ) *
          RBM.Ind.Ugen 3 4 (1 / 64 : ℝ) 0 ![true, false] (pfStep5Alg_instU j) (pfStep5Alg_instU 3)
            (fun _ => (0 : ℂ)) a‖ ≤
        ∑ j ∈ Finset.range 3, (1 / 48 : ℝ) * ((j : ℝ) + 1) *
          (C * tailTD 3 32 (pfStep5Alg_instU 3) ((j : ℝ) + 1) (zdistInf 3 4 (a 0 - a 1) : ℝ) +
            ((1 - pfStep5Alg_instU j) / (1 - pfStep5Alg_instU 3)) ^ 2 * 32 ^ (-((j : ℝ) + 1))) := by
  obtain ⟨C, hC, H⟩ := pfStep5Alg_ugenSum' 3 (le_refl 3)
  refine ⟨C, hC, fun a => ?_⟩
  exact H 4 (by norm_num) (1 / 64) 32 0 (fun j => (j : ℝ) + 1) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] 3 pfStep5Alg_instU (fun _ => 1 / 48) (fun j => (j : ℝ) + 1) (fun _ _ => (0 : ℂ))
    (by simp [pfStep5Alg_instU]) pfStep5Alg_instU_mono (by norm_num [pfStep5Alg_instU])
    (by norm_num [pfStep5Alg_instU]) (fun _ => by norm_num)
    (fun j _ b => by
      rw [norm_zero]
      exact mul_nonneg (by positivity) (tailTD_nonneg (by norm_num))) a

/-- **Target 2′ at the extremal tensors** `ℰ_j(b) = p_j T_{u_j,D_j}(|b₁-b₂|)` (equality in the hypothesis; nonzero data). -/
theorem pfStep5Alg_inst_ugenSum'_extremal :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
      ‖∑ j ∈ Finset.range 3, (((1 / 48 : ℝ)) : ℂ) *
          RBM.Ind.Ugen 3 4 (1 / 64 : ℝ) 0 ![true, false] (pfStep5Alg_instU j) (pfStep5Alg_instU 3)
            (fun b => (((((j : ℝ) + 1) *
              tailTD 3 32 (pfStep5Alg_instU j) ((j : ℝ) + 1) (zdistInf 3 4 (b 0 - b 1) : ℝ) : ℝ)) : ℂ)) a‖ ≤
        ∑ j ∈ Finset.range 3, (1 / 48 : ℝ) * ((j : ℝ) + 1) *
          (C * tailTD 3 32 (pfStep5Alg_instU 3) ((j : ℝ) + 1) (zdistInf 3 4 (a 0 - a 1) : ℝ) +
            ((1 - pfStep5Alg_instU j) / (1 - pfStep5Alg_instU 3)) ^ 2 * 32 ^ (-((j : ℝ) + 1))) := by
  obtain ⟨C, hC, H⟩ := pfStep5Alg_ugenSum' 3 (le_refl 3)
  refine ⟨C, hC, fun a => ?_⟩
  exact H 4 (by norm_num) (1 / 64) 32 0 (fun j => (j : ℝ) + 1) (by norm_num) (by norm_num) (by norm_num)
    ![true, false] 3 pfStep5Alg_instU (fun _ => 1 / 48) (fun j => (j : ℝ) + 1)
    (fun j b => (((((j : ℝ) + 1) *
      tailTD 3 32 (pfStep5Alg_instU j) ((j : ℝ) + 1) (zdistInf 3 4 (b 0 - b 1) : ℝ) : ℝ)) : ℂ))
    (by simp [pfStep5Alg_instU]) pfStep5Alg_instU_mono (by norm_num [pfStep5Alg_instU])
    (by norm_num [pfStep5Alg_instU]) (fun _ => by norm_num)
    (fun j _ b => by
      rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by positivity) (tailTD_nonneg (by norm_num)))]) a

/-- **Target 2 at `d = 3`, `L = 4`, `ℰ ≡ 0`** (one level `D = 1`). -/
theorem pfStep5Alg_inst_ugenSum_zero :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Fin 2 → Zd 3 4,
      ‖∑ j ∈ Finset.range 3, (((1 / 48 : ℝ)) : ℂ) *
          RBM.Ind.Ugen 3 4 (1 / 64 : ℝ) 0 ![true, false] (pfStep5Alg_instU j) (pfStep5Alg_instU 3)
            (fun _ => (0 : ℂ)) a‖ ≤
        ∑ j ∈ Finset.range 3, (1 / 48 : ℝ) * ((j : ℝ) + 1) *
          (C * tailTD 3 32 (pfStep5Alg_instU 3) 1 (zdistInf 3 4 (a 0 - a 1) : ℝ) +
            ((1 - pfStep5Alg_instU j) / (1 - pfStep5Alg_instU 3)) ^ 2 * 32 ^ (-(1 : ℝ))) := by
  obtain ⟨C, hC, H⟩ := pfStep5Alg_ugenSum 3 (le_refl 3)
  refine ⟨C, hC, fun a => ?_⟩
  exact H 4 (by norm_num) (1 / 64) 32 1 0 (by norm_num) (by norm_num) (by norm_num)
    ![true, false] 3 pfStep5Alg_instU (fun _ => 1 / 48) (fun j => (j : ℝ) + 1) (fun _ _ => (0 : ℂ))
    (by simp [pfStep5Alg_instU]) pfStep5Alg_instU_mono (by norm_num [pfStep5Alg_instU])
    (by norm_num [pfStep5Alg_instU]) (fun _ => by norm_num)
    (fun j _ b => by
      rw [norm_zero]
      exact mul_nonneg (by positivity) (tailTD_nonneg (by norm_num))) a

/-- **Target 3 at `u_j = 1 - 2^{-(j+1)}`, `k = 3`** (`u = 1/2, 3/4, 7/8, 15/16`): the three sums. -/
theorem pfStep5Alg_inst_riemann :
    ∑ j ∈ Finset.range 3, ((1 - (1 / 2 : ℝ) ^ (j + 1 + 1)) - (1 - (1 / 2 : ℝ) ^ (j + 1))) *
        (1 - (1 - (1 / 2 : ℝ) ^ (j + 1)))⁻¹ ^ 2 ≤ (1 - (1 - (1 / 2 : ℝ) ^ (3 + 1)))⁻¹ ∧
    ∑ j ∈ Finset.range 3, ((1 - (1 / 2 : ℝ) ^ (j + 1 + 1)) - (1 - (1 / 2 : ℝ) ^ (j + 1))) *
        ((1 - (1 - (1 / 2 : ℝ) ^ (j + 1)))⁻¹) ^ (3 / 2 : ℝ) ≤
      2 * ((1 - (1 - (1 / 2 : ℝ) ^ (3 + 1)))⁻¹) ^ (1 / 2 : ℝ) ∧
    ∑ j ∈ Finset.range 3, ((1 - (1 / 2 : ℝ) ^ (j + 1 + 1)) - (1 - (1 / 2 : ℝ) ^ (j + 1))) *
        (1 - (1 - (1 / 2 : ℝ) ^ (j + 1)))⁻¹ ≤
      Real.log ((1 - (1 - (1 / 2 : ℝ) ^ (0 + 1))) / (1 - (1 - (1 / 2 : ℝ) ^ (3 + 1)))) :=
  pfStep5Alg_riemann 3 (fun j => 1 - (1 / 2 : ℝ) ^ (j + 1)) (by norm_num)
    (fun j => by
      have : (1 / 2 : ℝ) ^ (j + 1 + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ _)
      linarith)
    (by norm_num)

/-- The first sum of the instance of target 3 is `7 ≤ 16` (`1 + 2 + 4`). -/
theorem pfStep5Alg_inst_riemann_sum : ∑ j ∈ Finset.range 3, ((1 - (1 / 2 : ℝ) ^ (j + 1 + 1)) - (1 - (1 / 2 : ℝ) ^ (j + 1))) *
        (1 - (1 - (1 / 2 : ℝ) ^ (j + 1)))⁻¹ ^ 2 = 7 := by
  norm_num [Finset.sum_range_succ]

/-- **Targets 4′ and 4 at `sz0`, `n = 0`, `u = 1/16`, `ε = 1/4`**: the stopping condition and the good event at another
level `D₁ = 55` (target 4′; `D = 1`) stay hypotheses on the sample `ω`; `0 ≤ τ'` and `1 ≤ N = 2097152` are discharged. -/
theorem pfStep5Alg_inst_goodStop' (J₀ : ℕ → ℝ → ℝ → ℝ) (ω : sz0.SeqΩ)
    (hstop : LemDecCalELip_Jsharp sz0 (STflowE z0) 1 0 (1 / 16) ω ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 4 : ℝ))
    (hgood : ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 55 J₀ (1 / 100) 0 (1 / 16)) :
    ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ _ => ((sz0.W m : ℕ) : ℝ) ^ (1 / 4 : ℝ)) (1 / 100) 0
      (1 / 16) :=
  pfStep5Alg_goodStop' sz0 (STflowE z0) 1 55 (1 / 4) (1 / 100) J₀ 0 (1 / 16) ω (by norm_num)
    (by rw [sz0_values.2.2.1]; norm_num) hstop hgood

/-- Target 4 (`D₁ = D = 1`) at the same data. -/
theorem pfStep5Alg_inst_goodStop (J₀ : ℕ → ℝ → ℝ → ℝ) (ω : sz0.SeqΩ)
    (hstop : LemDecCalELip_Jsharp sz0 (STflowE z0) 1 0 (1 / 16) ω ≤ ((sz0.W 0 : ℕ) : ℝ) ^ (1 / 4 : ℝ))
    (hgood : ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 J₀ (1 / 100) 0 (1 / 16)) :
    ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ _ => ((sz0.W m : ℕ) : ℝ) ^ (1 / 4 : ℝ)) (1 / 100) 0
      (1 / 16) :=
  pfStep5Alg_goodStop sz0 (STflowE z0) 1 (1 / 4) (1 / 100) J₀ 0 (1 / 16) ω (by norm_num)
    (by rw [sz0_values.2.2.1]; norm_num) hstop hgood

/-- **Target 5 at `sz0`, `E = STflowE z0`, `s ≡ 0`, `t ≡ 1/16`, `D = 1`, `τ' = 1/100`, `D₁ = 1`**: `SizeTendsto` and
`Bctl ≤ 1` (`st5_Bctl_le_one` at the flow `z0`) are discharged; the five stochastic pins stay hypotheses. -/
theorem pfStep5Alg_inst_goodProb (hLK : STLKU sz0 (STflowE z0) sInst tInst) (hLoc : STLocalEntryU sz0 (STflowE z0) sInst tInst)
    (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst)
    (hGij : GijGEXPTSwap sz0 (STflowE z0) sInst tInst) :
    ∀ᶠ n in atTop, ∀ u : TimeIcc sInst tInst n,
      sz0.seqP (lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D') (1 / 100) n
        (u : ℝ))ᶜ ≤ ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
  pfStep5Alg_goodProb sz0 (STflowE z0) sInst tInst 1 sz0_tendsto
    ((st5_Bctl_le_one sz0 (by norm_num) (by norm_num) flow_z0 sz0_ht).mono fun n hn u => hn (u : ℝ) u.2.2)
    hLK hLoc hAvg hLmax hGij (1 / 100) 1 (by norm_num) (by norm_num)

/-- **The hypotheses of targets 4′, 4 are satisfiable at `sz0`** (conditional on the five stochastic pins, as target 5), for
every pair of levels `0 ≤ D₁`, `D ≤ D₁` (`D = D₁` is target 4): by target 5 the good event at the crude control `Jst = W^{D₁}`
(`τ' = 1/100`) has probability `≥ 1 - N⁻¹ > 0` at some `n` with `N ≥ 2`, so it contains a sample `ω`; on it
`STLK2 ≤ N^{τ'} W^{D₁} T_{u,D₁} ≤ N^{τ'} W^{D₁} T_{u,D}` (target 1), hence `J♯(D) ≤ N^{τ'} W^{D₁} ≤ W^{D₁ + 6/100}`
(`LemDecCalELip_Jsharp_basic`, `N ≤ W^6`): the stopping condition holds with `ε = D₁ + 6/100`, and target 4′ returns `ω` in
the good event at `Jst ≡ W^ε`, level `D`. -/
theorem pfStep5Alg_inst_goodStop'_nonvac (D D₁ : ℝ) (hDD : D ≤ D₁) (hD₁ : 0 ≤ D₁)
    (hLK : STLKU sz0 (STflowE z0) sInst tInst) (hLoc : STLocalEntryU sz0 (STflowE z0) sInst tInst)
    (hAvg : STAvgU sz0 (STflowE z0) sInst tInst) (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst)
    (hGij : GijGEXPTSwap sz0 (STflowE z0) sInst tInst) :
    ∃ (n : ℕ) (ω : sz0.SeqΩ),
      LemDecCalELip_Jsharp sz0 (STflowE z0) D n (1 / 16) ω ≤ ((sz0.W n : ℕ) : ℝ) ^ (D₁ + 6 / 100) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) D₁ (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D') (1 / 100) n
        (1 / 16) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) D (fun m _ _ => ((sz0.W m : ℕ) : ℝ) ^ (D₁ + 6 / 100))
        (1 / 100) n (1 / 16) := by
  have hB : ∀ᶠ n in atTop, ∀ u : TimeIcc sInst tInst n, sz0.Bctl n (u : ℝ) ≤ 1 :=
    (st5_Bctl_le_one sz0 (by norm_num) (by norm_num) flow_z0 sz0_ht).mono fun n hn u => hn (u : ℝ) u.2.2
  have hP := pfStep5Alg_goodProb sz0 (STflowE z0) sInst tInst D₁ sz0_tendsto hB hLK hLoc hAvg hLmax hGij
    (1 / 100) 1 (by norm_num) (by norm_num)
  obtain ⟨n, hn, hN2⟩ := (hP.and (sz0_tendsto.eventually_ge_atTop 2)).exists
  let u : TimeIcc sInst tInst n := ⟨1 / 16, by norm_num [sInst], by norm_num [tInst]⟩
  have hnu := hn u
  -- the good event is nonempty: its complement has probability `≤ N⁻¹ < 1`
  have hne : (lemDecCalEPrec_good sz0 (STflowE z0) D₁ (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D') (1 / 100) n
      (1 / 16)).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h1 : sz0.seqP (lemDecCalEPrec_good sz0 (STflowE z0) D₁ (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D')
        (1 / 100) n (u : ℝ))ᶜ = 1 := by
      have : (u : ℝ) = 1 / 16 := rfl
      rw [this, hemp, Set.compl_empty]
      exact measure_univ
    rw [h1] at hnu
    have h2 := ENNReal.one_le_ofReal.1 hnu
    rw [Real.rpow_neg_one] at h2
    have : ((sz0.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hN2
    linarith
  obtain ⟨ω, hω⟩ := hne
  have hW1 : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n
  have hN1 : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by linarith
  -- the stopping condition with `ε = D₁ + 6/100`
  have hstop : LemDecCalELip_Jsharp sz0 (STflowE z0) D n (1 / 16) ω ≤ ((sz0.W n : ℕ) : ℝ) ^ (D₁ + 6 / 100) := by
    have hNW : ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (6 / 100 : ℝ) := by
      have h6 : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (6 : ℕ) := by
        exact_mod_cast sz0_size_le_W_pow n
      calc ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) ≤ (((sz0.W n : ℕ) : ℝ) ^ (6 : ℕ)) ^ (1 / 100 : ℝ) :=
            Real.rpow_le_rpow (by linarith) h6 (by norm_num)
        _ = ((sz0.W n : ℕ) : ℝ) ^ (6 / 100 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            norm_num
    have hX1 : 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ D₁ := by
      have h1 : 1 ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) := Real.one_le_rpow hN1 (by norm_num)
      have h2 : 1 ≤ ((sz0.W n : ℕ) : ℝ) ^ D₁ := Real.one_le_rpow hW1 hD₁
      exact one_le_mul_of_one_le_of_one_le h1 h2
    refine ((LemDecCalELip_Jsharp_basic sz0 (STflowE z0) D n (1 / 16) ω).2.2 _ hX1 fun σ a => ?_).trans ?_
    · have h1 := hω.1 σ a
      have h2 := pfStep5Alg_tailAnti sz0 n (1 / 16) D D₁ a hDD
      have hN0 : (0 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) := Real.rpow_nonneg (by linarith) _
      have hW0 : (0 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ D₁ := Real.rpow_nonneg (by linarith) _
      calc STLK2 sz0 n (STflowE z0 n) (1 / 16) σ a ω
          ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * (((sz0.W n : ℕ) : ℝ) ^ D₁ * STtailTD sz0 n (1 / 16) D₁ a) := h1
        _ ≤ ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * (((sz0.W n : ℕ) : ℝ) ^ D₁ * STtailTD sz0 n (1 / 16) D a) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hW0) hN0
        _ = _ := by ring
    · calc ((sz0.size n : ℕ) : ℝ) ^ (1 / 100 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ D₁
          ≤ ((sz0.W n : ℕ) : ℝ) ^ (6 / 100 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ D₁ :=
            mul_le_mul_of_nonneg_right hNW (Real.rpow_nonneg (by linarith) _)
        _ = ((sz0.W n : ℕ) : ℝ) ^ (D₁ + 6 / 100) := by
            rw [← Real.rpow_add (by linarith), add_comm]
  exact ⟨n, ω, hstop, hω, pfStep5Alg_goodStop' sz0 (STflowE z0) D D₁ (D₁ + 6 / 100) (1 / 100) _ n (1 / 16) ω
    (by norm_num) hN1 hstop hω⟩

/-- The case `D = D₁ = 1` of the previous theorem (target 4). -/
theorem pfStep5Alg_inst_goodStop_nonvac_one (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hLoc : STLocalEntryU sz0 (STflowE z0) sInst tInst) (hAvg : STAvgU sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hGij : GijGEXPTSwap sz0 (STflowE z0) sInst tInst) :
    ∃ (n : ℕ) (ω : sz0.SeqΩ),
      LemDecCalELip_Jsharp sz0 (STflowE z0) 1 n (1 / 16) ω ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 + 6 / 100 : ℝ) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D') (1 / 100) n
        (1 / 16) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ _ => ((sz0.W m : ℕ) : ℝ) ^ (1 + 6 / 100 : ℝ))
        (1 / 100) n (1 / 16) :=
  pfStep5Alg_inst_goodStop'_nonvac 1 1 le_rfl (by norm_num) hLK hLoc hAvg hLmax hGij

/-- The case `D = 1`, `D₁ = 55` (the shape S5-11 uses: the good event at `D*`, the conclusion at the level `D`). -/
theorem pfStep5Alg_inst_goodStop'_nonvac_55 (hLK : STLKU sz0 (STflowE z0) sInst tInst)
    (hLoc : STLocalEntryU sz0 (STflowE z0) sInst tInst) (hAvg : STAvgU sz0 (STflowE z0) sInst tInst)
    (hLmax : STLmaxU sz0 (STflowE z0) sInst tInst) (hGij : GijGEXPTSwap sz0 (STflowE z0) sInst tInst) :
    ∃ (n : ℕ) (ω : sz0.SeqΩ),
      LemDecCalELip_Jsharp sz0 (STflowE z0) 1 n (1 / 16) ω ≤ ((sz0.W n : ℕ) : ℝ) ^ (55 + 6 / 100 : ℝ) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 55 (fun m _ D' => ((sz0.W m : ℕ) : ℝ) ^ D') (1 / 100) n
        (1 / 16) ∧
      ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 1 (fun m _ _ => ((sz0.W m : ℕ) : ℝ) ^ (55 + 6 / 100 : ℝ))
        (1 / 100) n (1 / 16) :=
  pfStep5Alg_inst_goodStop'_nonvac 1 55 (by norm_num) (by norm_num) hLK hLoc hAvg hLmax hGij

/-- **Target 6 at `sz0`** with its merged `Admissible (1/6) (1/10)` (`sz0_admissible`), `ε = 1/50 < 1/40 = 𝔡/4`, `C = 6000`:
there is `τ > 0` with the closure eventually. -/
theorem pfStep5Alg_inst_closure : ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ n in atTop,
    ((sz0.size n : ℕ) : ℝ) ^ τ *
        (6000 * (1 + Real.log ((sz0.W n : ℕ) : ℝ) +
          ((sz0.W n : ℕ) : ℝ) ^ (2 * (1 / 50 : ℝ)) *
            (sz0.lam n ^ 2 * ((sz0.W n : ℕ) : ℝ) ^ 3) ^ (-(1 / 4 : ℝ)))) <
      ((sz0.W n : ℕ) : ℝ) ^ (1 / 50 : ℝ) :=
  pfStep5Alg_closure sz0 (1 / 6) (1 / 10) sz0_admissible (1 / 50) 6000 (by norm_num) (by norm_num)
    (by norm_num)

end Instances

end RBM.Gauss.Sizes
