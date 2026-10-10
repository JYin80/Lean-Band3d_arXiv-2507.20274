/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWProv
import RBM3D.Graph.LWMomentExpA
import RBM3D.Graph.LWMomExpInf
import RBM3D.Graph.LWXiExp
import RBM3D.Graph.LWMomExpFar
import RBM3D.Graph.AuxGraph
import RBM3D.Graph.LWMoment
import RBM3D.Graph.AuxGraphRooted
import RBM3D.Graph.LWMomExpD
/-!
# LW-13b R3 (F): `lem:LW_moment_exp` (`7_8:78-83`), the assembly (T2364)
Paper `7_8:78-83`, proof `7_8:1595-1660` (`paper/tex/7_8_light_weight.tex`): the regime `regA K` (merged (A)), the exact three-way split `f = f^{>} + f^{(a)} + f^{(b)}` (`LWf_split`), the far pin (`lem:LW_moment_exp_far`) and the near pins
(`lem:LW_moment_exp_near`) from the engine with provenance (`lw_localregularXP`), the rooted `GtoAG` (`Graph/AuxGraphRooted.lean`), `lwMomExpFar_and`, `lwMomExp_nearInf`, `lwXiExpClaim_holds`; target `lwMomentExp_holds`.
Quantifier of `K` (C6): the pins are proved for every `K > 0` (far tail radius `r = K (log W)^{3/2}/K_card`, `K_card` the size of the engine lists, chosen after `𝔠, D`); the final theorem uses `K = 1`.
Ports (merged RBM3D, text copied and adapted): `Graph/LWMoment.lean`, `Graph/LWMomentExpA.lean`, `Graph/LWSizeClaim.lean`, `Graph/AuxGraph.lean`; statements = probe `t/T2348:RBM3D/Probe/T2348Pins.lean:248-322, 507-538`.
-/
set_option linter.style.setOption false set_option linter.style.longLine false set_option linter.unusedSectionVars false set_option linter.flexible false set_option linter.unusedFintypeInType false set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false set_option linter.style.show false set_option linter.unusedSimpArgs false set_option linter.unusedVariables false set_option linter.deprecated false
noncomputable section
open MeasureTheory Matrix Filter
open RBM RBM.Gauss RBM.Green RBM.Graph RBM.Gauss.Sizes
namespace RBM.Graph
/-! ## 1. The three domains and the statements -/
section Domains
variable (d L : ℕ) [NeZero L]
/-- `f^{>}`: both distances `> ℓ` (the merged `lwMomExpFar_farDAnd`, `LWMomExpFar.lean:42`, for one pair `(a, b)`) -/
def domFar (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ℓ < ((zdistInf d L (a - c) : ℕ) : ℝ) ∧ ℓ < ((zdistInf d L (b - c) : ℕ) : ℝ)
/-- `f^{(a)}`: `a_1` within `ℓ` of `a` (single centre `a`) -/
def domNearA (a : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ ℓ
/-- `f^{(b)}`: `a_1` farther than `ℓ` from `a` and within `ℓ` of `b` (single centre `b`) -/
def domNearB (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c => ℓ < ((zdistInf d L (a - c) : ℕ) : ℝ) ∧ ((zdistInf d L (b - c) : ℕ) : ℝ) ≤ ℓ
variable {d L}
/-- the merged far domain takes the radius as a parameter: for `p ≥ 1` constant paths it is `domFar` -/
theorem domFar_eq {p : ℕ} (hp : 0 < p) (a b : Zd d L) (ℓ : ℝ) :
    lwMomExpFar_farDAnd d L (fun _ : Fin p => a) (fun _ => b) ℓ = domFar d L a b ℓ := by
  ext c
  simp only [lwMomExpFar_farDAnd, domFar, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h ⟨0, hp⟩, fun h _ => h⟩
/-- the three domains partition `Z_L^d` -/
theorem dom_union (a b : Zd d L) (ℓ : ℝ) :
    domFar d L a b ℓ ∪ domNearA d L a ℓ ∪ domNearB d L a b ℓ = Finset.univ := by
  ext c
  simp only [domFar, domNearA, domNearB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  by_cases h1 : ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ ℓ
  · exact Or.inl (Or.inr h1)
  · by_cases h2 : ((zdistInf d L (b - c) : ℕ) : ℝ) ≤ ℓ
    · exact Or.inr ⟨not_le.1 h1, h2⟩
    · exact Or.inl (Or.inl ⟨not_le.1 h1, not_le.1 h2⟩)
theorem dom_disj (a b : Zd d L) (ℓ : ℝ) :
    Disjoint (domFar d L a b ℓ) (domNearA d L a ℓ) ∧ Disjoint (domFar d L a b ℓ ∪ domNearA d L a ℓ) (domNearB d L a b ℓ) := by
  refine ⟨Finset.disjoint_left.2 fun c h1 h2 => ?_, Finset.disjoint_left.2 fun c h1 h2 => ?_⟩
  · simp only [domFar, domNearA, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact absurd h2 (not_le.2 h1.1)
  · simp only [domFar, domNearA, domNearB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rcases h1 with h1 | h1
    · exact absurd h2.2 (not_le.2 h1.2)
    · exact absurd h1 (not_le.2 h2.1)
end Domains
/-- **G4**: `f = f^{>} + f^{(a)} + f^{(b)}` exactly, `a = [x]`, `b = [y]` (`D = univ` is `LWf`) -/
theorem LWf_split {d : ℕ} (sz : Sizes d) (n : ℕ) (E t ℓ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    LWf sz n E t ω x y =
      LWfD sz n E t ω (domFar d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y +
      LWfD sz n E t ω (domNearA d (sz.L n) (STblk sz n x) ℓ) x y +
      LWfD sz n E t ω (domNearB d (sz.L n) (STblk sz n x) (STblk sz n y) ℓ) x y := by
  have h0 : LWfD sz n E t ω Finset.univ x y = LWf sz n E t ω x y := by simp [LWfD, LWf]
  rw [← LWfD_union sz n E t ω (dom_disj _ _ ℓ).1, ← LWfD_union sz n E t ω (dom_disj _ _ ℓ).2, dom_union, h0]
/-- `|a+b+c|^p ≤ 3^{p-1}(|a|^p + |b|^p + |c|^p)`: the pointwise step of the assembly (`E|f|^p ≤ 3^{p-1} Σ E|f^•|^p`) -/
theorem norm_add3_pow_le (a b c : ℂ) {p : ℕ} (hp : 0 < p) :
    ‖a + b + c‖ ^ p ≤ 3 ^ (p - 1) * (‖a‖ ^ p + ‖b‖ ^ p + ‖c‖ ^ p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  have h2 := pow_sum_le_card_mul_sum_pow (s := (Finset.univ : Finset (Fin 3))) (f := ![‖a‖, ‖b‖, ‖c‖])
    (fun i _ => by fin_cases i <;> simp) n
  simp only [Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 _).trans (by simpa using h2)
/-- `lem:LW_moment_exp` (`LWPins.lean:341`) for `f^{dom}` on the pairs/lengths in `reg` (`dom ≡ univ`, `reg ≡ True` is the target) -/
def LWMomentExpOn (d : ℕ) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (reg : ∀ (sz : Sizes d) (n : ℕ), ℝ → ℝ → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ reg sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWfD sz n (STflowE z n) (t n) ω
            (dom (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
          (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))
/-- **far pin** (`lem:LW_moment_exp_far`; engine with provenance, rooted `GtoAG`, `lwMomExpFar_and`) in `¬ regA` -/
def LWMomExpFarPin (d : ℕ) (K : ℝ) : Prop :=
  LWMomentExpOn d (fun L _ a b ℓ => domFar d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
/-- **near pins** (`lem:LW_moment_exp_near`, split by the centre; `AnpNearInfAt`) in `¬ regA` -/
def LWMomExpNearPin (d : ℕ) (K : ℝ) : Prop :=
  LWMomentExpOn d (fun L _ a _ ℓ => domNearA d L a ℓ) (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) ∧
    LWMomentExpOn d (fun L _ a b ℓ => domNearB d L a b ℓ) fun sz n t ℓ q => ¬ regA d K sz n t ℓ q
/-- **the assembly** `lwMomentExp_of_parts`: (A) in the regime `regA K` (merged `LWMomExpNoExpF`), the far pin and both near pins give the target -/
def LWMomentExpOfParts (d : ℕ) : Prop :=
  ∀ K : ℝ, 0 < K → LWMomExpNoExpF d K → LWMomExpFarPin d K → LWMomExpNearPin d K → RBM.Gauss.Sizes.LWMomentExp d
/-! ## 2. Integrability of `|f^D|^p` and the assembly -/
section Assembly
variable {d : ℕ} (sz : Sizes d)
private theorem lwMomentExp_meas_Gt (n : ℕ) (E t : ℝ) (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable fun ω : sz.SeqΩ => Gt sz n E t true ω x y := by
  have : (fun ω : sz.SeqΩ => Gt sz n E t true ω x y) = fun ω => green (sz.seqHflow n t ω) (zt E t) x y := by
    funext ω; rw [lwMoment_Gt_true_eq]
  rw [this]
  exact measurable_green_apply sz n t (zt E t) x y
/-- `|f^D|^p` is integrable (bounded by `η⁻¹`-powers, measurable): the pointwise step of the three-way split needs it -/
theorem lwMomentExp_integrable (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (p : ℕ) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω => ‖LWfD sz n E t ω Dm x y‖ ^ p) sz.seqP := by
  have hm : Measurable fun ω : sz.SeqΩ => LWfD sz n E t ω Dm x y := by
    unfold LWfD
    refine Finset.measurable_sum _ fun α _ => ?_
    by_cases hα : α = x ∨ α = y
    · simp only [hα, ite_true]; exact measurable_const
    · simp only [hα, ite_false]
      refine Finset.measurable_sum _ fun β _ => ?_
      by_cases hβ : STblk sz n β ∈ Dm
      · simp only [hβ, ite_true]
        have hS : Measurable fun ω : sz.SeqΩ => STGM sz n E t ω β β :=
          (lwMomentExp_meas_Gt sz n E t β β).sub measurable_const
        exact (((measurable_const.mul hS).mul (lwMomentExp_meas_Gt sz n E t x α)).mul (lwMomentExp_meas_Gt sz n E t α y))
      · simp only [hβ, ite_false]; exact measurable_const
  have hη0 : 0 < etaT E t := by
    unfold etaT; exact mul_pos (by linarith) (mE_im_pos hE)
  set H : ℝ := (etaT E t)⁻¹ with hH
  have hH0 : 0 ≤ H := inv_nonneg.2 hη0.le
  have hGb : ∀ (ω : sz.SeqΩ) (a b : Idx d (sz.L n) (sz.W n)), ‖Gt sz n E t true ω a b‖ ≤ H :=
    fun ω a b => lwMoment_norm_Gt_le (sz := sz) hE ht n ω a b
  have hmE : ‖mE E‖ = 1 := norm_mE hE.le
  have hb : ∀ ω : sz.SeqΩ, ‖LWfD sz n E t ω Dm x y‖ ≤ ∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n),
      ‖(LWS sz n α β : ℂ)‖ * ((H + 1) * (H * H)) := by
    intro ω
    unfold LWfD
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    by_cases hα : α = x ∨ α = y
    · simp only [hα, ite_true, norm_zero]
      exact Finset.sum_nonneg fun β _ => by positivity
    · simp only [hα, ite_false]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
      by_cases hβ : STblk sz n β ∈ Dm
      · simp only [hβ, ite_true, norm_mul]
        have hS : ‖STGM sz n E t ω β β‖ ≤ H + 1 := by
          unfold STGM
          simp only [ite_true]
          exact (norm_sub_le _ _).trans (by linarith [hGb ω β β])
        have := mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hS (norm_nonneg ((LWS sz n α β : ℝ) : ℂ)))
          (hGb ω x α) (norm_nonneg _) (by positivity)) (hGb ω α y) (norm_nonneg _) (by positivity)
        calc _ ≤ _ := this
          _ = _ := by ring
      · simp only [hβ, ite_false, norm_zero]; positivity
  refine Integrable.of_bound ((hm.norm.pow_const p).aestronglyMeasurable)
    ((∑ α : Idx d (sz.L n) (sz.W n), ∑ β : Idx d (sz.L n) (sz.W n), ‖(LWS sz n α β : ℂ)‖ * ((H + 1) * (H * H))) ^ p)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) p
private theorem lwMomentExp_comb {p : ℕ} {I0 I1 I2 I3 R Nh : ℝ} (hI0 : I0 ≤ 3 ^ (p - 1) * (I1 + I2 + I3))
    (h1 : I1 ≤ Nh * R) (h2 : I2 ≤ Nh * R) (h3 : I3 ≤ Nh * R) (hp : 0 < p) (hN : (3 : ℝ) ^ p ≤ Nh) (hR : 0 ≤ R) :
    I0 ≤ Nh * Nh * R := by
  have h33 : (3 : ℝ) ^ (p - 1) * 3 = 3 ^ p := by
    rw [← pow_succ]; congr 1; omega
  have hp3 : (0 : ℝ) ≤ 3 ^ (p - 1) := by positivity
  calc I0 ≤ 3 ^ (p - 1) * (I1 + I2 + I3) := hI0
    _ ≤ 3 ^ (p - 1) * (3 * (Nh * R)) := mul_le_mul_of_nonneg_left (by linarith) hp3
    _ = 3 ^ p * (Nh * R) := by rw [← h33]; ring
    _ ≤ Nh * (Nh * R) := mul_le_mul_of_nonneg_right hN (by nlinarith [(by positivity : (0 : ℝ) ≤ 3 ^ p)])
    _ = _ := by ring
/-- **`lwMomentExp_of_parts`** (`7_8:1595-1611`): (A) on `regA K`; on `¬ regA K` the split `f = f^> + f^(a) + f^(b)` with `E|f|^p ≤ 3^{p-1} Σ E|f^•|^p` -/
theorem lwMomentExp_of_parts (d : ℕ) : LWMomentExpOfParts d := by
  intro K hK hA hF hN hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  obtain ⟨-, hE, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hA' := (st6_prec_det_iff sz hsz _ _).1 (hA hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hF' := (st6_prec_det_iff sz hsz _ _).1 (hF hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hN1 := (st6_prec_det_iff sz hsz _ _).1 (hN.1 hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  have hN2 := (st6_prec_det_iff sz hsz _ _).1 (hN.2 hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  rcases Nat.eq_zero_or_pos p with hp0 | hp0
  · subst hp0
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1' q
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1' hτ.le
    have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    nlinarith
  · filter_upwards [hA' τ hτ, hF' (τ / 2) (half_pos hτ), hN1 (τ / 2) (half_pos hτ), hN2 (τ / 2) (half_pos hτ),
      ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop ((3 : ℝ) ^ p)] with n hA1 hF1 hN11 hN21 h3
    intro q
    by_cases hreg : regA d K sz n (t n) (ℓ n) q.1
    · exact hA1 ⟨q.1, q.2, hreg⟩
    · have hE2 : |STflowE z n| < 2 := by linarith [hE n, hκ]
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have e1 := hF1 ⟨q.1, q.2, hreg⟩
      have e2 := hN11 ⟨q.1, q.2, hreg⟩
      have e3 := hN21 ⟨q.1, q.2, hreg⟩
      have hR0 : 0 ≤ ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p +
          ((sz.W n : ℕ) : ℝ) ^ (-D) := by
        have h1 := inv_nonneg.2 (lwN_etaT_nonneg (STflowE z n) (t n) (ht1 n).le)
        have h2 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) :=
          Real.rpow_nonneg (by unfold Sizes.Bctl Bparam; positivity) _
        have h3 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
          (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))
        have h4 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        positivity
      refine le_trans (lwMomentExp_comb ?_ e1 e2 e3 hp0 h3 hR0) (le_of_eq ?_)
      swap
      · rw [← Real.rpow_add hN0]; congr 2; ring
      set f1 : sz.SeqΩ → ℝ := fun ω => ‖LWfD sz n (STflowE z n) (t n) ω
        (domFar d (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf1
      set f2 : sz.SeqΩ → ℝ := fun ω => ‖LWfD sz n (STflowE z n) (t n) ω
        (domNearA d (sz.L n) (STblk sz n q.1.1) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf2
      set f3 : sz.SeqΩ → ℝ := fun ω => ‖LWfD sz n (STflowE z n) (t n) ω
        (domNearB d (sz.L n) (STblk sz n q.1.1) (STblk sz n q.1.2) (ℓ n)) q.1.1 q.1.2‖ ^ p with hf3
      have hpt : ∀ ω : sz.SeqΩ, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ≤ 3 ^ (p - 1) * (f1 ω + f2 ω + f3 ω) := by
        intro ω
        rw [LWf_split sz n (STflowE z n) (t n) (ℓ n) ω q.1.1 q.1.2]
        exact norm_add3_pow_le _ _ _ hp0
      have i1 : Integrable f1 sz.seqP := lwMomentExp_integrable sz n hE2 (ht1 n) p _ q.1.1 q.1.2
      have i2 : Integrable f2 sz.seqP := lwMomentExp_integrable sz n hE2 (ht1 n) p _ q.1.1 q.1.2
      have i3 : Integrable f3 sz.seqP := lwMomentExp_integrable sz n hE2 (ht1 n) p _ q.1.1 q.1.2
      calc _ ≤ ∫ ω, (3 : ℝ) ^ (p - 1) * (f1 ω + f2 ω + f3 ω) ∂sz.seqP :=
            integral_mono_of_nonneg (Eventually.of_forall fun ω => by positivity) (((i1.add i2).add i3).const_mul _)
              (Eventually.of_forall hpt)
        _ = (3 : ℝ) ^ (p - 1) * (∫ ω, f1 ω ∂sz.seqP + ∫ ω, f2 ω ∂sz.seqP + ∫ ω, f3 ω ∂sz.seqP) := by
            rw [integral_const_mul]
            congr 1
            rw [integral_add (f := fun a => f1 a + f2 a) (g := f3) (i1.add i2) i3, integral_add i1 i2]
end Assembly
/-! ## 3. Weighted values: homogeneity, the claim `size` and the scalemole tail for `valW` (`|Wt| ≤ 1`) -/
section Weighted
variable {ι : Type} [Fintype ι] [DecidableEq ι] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
private theorem lwMomentExp_waved_prod (D : LData ι) (s : ℂ) {V : Type} (ℓ : V → ι) (l : List (WEdge V)) :
    (l.map (WEdge.val { D with S := s • D.S } ℓ)).prod =
      s ^ (l.countP (fun e => !e.col)) * (l.map (WEdge.val D ℓ)).prod := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    by_cases h : e.col
    · simp only [WEdge.val, h, ite_true, List.countP_cons, Bool.not_true, Bool.false_eq_true, ite_false, add_zero]
      split_ifs <;> ring
    · simp [WEdge.val, h, pow_succ, Matrix.smul_apply, List.countP_cons]
      ring
/-- homogeneity of the weighted value in `S` (twin of `lwMoment_val_smul`, `LWMoment.lean:57`) -/
theorem lwMomentExp_valW_smul (Γ : LGraph E I) (D : LData ι) (s : ℂ) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    valW Γ { D with S := s • D.S } Wt ℓe = s ^ (Γ.waved.countP fun e => !e.col) * valW Γ D Wt ℓe := by
  unfold valW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  unfold LGraph.term
  rw [lwMomentExp_waved_prod]
  have : (Γ.solid.map (SEdge.val { D with S := s • D.S } (Sum.elim ℓe ℓi))) =
      (Γ.solid.map (SEdge.val D (Sum.elim ℓe ℓi))) := rfl
  rw [this]; ring
theorem lwMomentExp_pvalW_smul {E0 : Type} (P : PGraph E0) (D : LData ι) (s : ℂ) (Wt : (P.E' ⊕ P.I' → ι) → ℝ) (ℓe : E0 → ι) :
    pvalW P { D with S := s • D.S } Wt ℓe = s ^ (P.g.waved.countP fun e => !e.col) * pvalW P D Wt ℓe := by
  classical
  by_cases h : ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [lwProv_pvalW_of_factor _ _ _ hℓ', lwProv_pvalW_of_factor _ _ _ hℓ']
    exact lwMomentExp_valW_smul P.g D s _ ℓ'
  · rw [lwProv_pvalW_of_not _ _ _ h, lwProv_pvalW_of_not _ _ _ h]; simp
theorem lwMomentExp_pvalW_evX (m : ℂ) (r : (ℕ × ℕ) × PGraph (Fin 2)) (D : LData ι) (Wt : (r.2.E' ⊕ r.2.I' → ι) → ℝ)
    (ℓe : Fin 2 → ι) :
    pvalW (lwEvX m r) D Wt ℓe = (m ^ r.1.1 * star m ^ r.1.2) * pvalW r.2 D Wt ℓe := by
  classical
  by_cases h : ∃ ℓ' : r.2.E' → ι, ℓe = ℓ' ∘ r.2.ext
  · obtain ⟨ℓ', hℓ'⟩ := h
    rw [lwProv_pvalW_of_factor r.2 D Wt hℓ', lwProv_pvalW_of_factor (lwEvX m r) D Wt (ℓ' := ℓ') hℓ']
    change valW { r.2.g with coeff := m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff } D Wt ℓ' = _
    unfold valW
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    unfold LGraph.term
    ring
  · rw [lwProv_pvalW_of_not r.2 D Wt h, lwProv_pvalW_of_not (lwEvX m r) D Wt h]; simp
/-- the weighted `L¹` form of `claim:size` (twin of `LGraph.val_norm_le`, `LWSizeClaim.lean:1058`): `|Wt| ≤ 1` costs nothing -/
theorem lwMomentExp_valW_norm_le [Nonempty ι] (Γ : LGraph E I) (hN : Γ.Normal) (D : LData ι) {m : ℂ} {Ψ a K₁ : ℝ}
    (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S a K₁) (hSp : LWKBound D.Sp a K₁) (ℓe : E → ι) (Wt : (E ⊕ I → ι) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖valW Γ D Wt ℓe‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
      ((Fintype.card ι : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) * a ^ (Γ.nW - (Γ.nV - Γ.nM))) := by
  have hΨ : 0 ≤ Ψ := by obtain ⟨x⟩ := ‹Nonempty ι›; exact (norm_nonneg _).trans (hGd x)
  unfold valW
  calc ‖∑ ℓi : I → ι, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖
      ≤ ∑ ℓi : I → ι, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓi _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (hWt _))
    _ ≤ ∑ ℓi : I → ι, ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod :=
        Finset.sum_le_sum fun ℓi _ => Γ.term_norm_le hN D hM hG hGd _
    _ = ‖Γ.coeff‖ * Ψ ^ Γ.nS * ∑ ℓi : I → ι, (Γ.waved.map fun e => ‖WEdge.val D (Sum.elim ℓe ℓi) e‖).prod := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Γ.waved_sum_le hN D hS hSp ℓe) (mul_nonneg (norm_nonneg _) (pow_nonneg hΨ _))
/-- the size identity of `claim:size` (private `lwSize_alg`, `LWSizeClaim.lean:1082`, copied) -/
private theorem lwMomentExp_size_alg (W d L nM nV nW : ℕ) (hW : (W : ℝ) ≠ 0) (h1 : nM ≤ nV) (h2 : nV - nM ≤ nW) (K₀ : ℝ) :
    ((((W * L) ^ d : ℕ) : ℝ)) ^ nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (nW - (nV - nM)) =
      K₀ ^ (nW - (nV - nM)) * (((L : ℝ) ^ d) ^ nM * (W : ℝ) ^ (-(d : ℤ) * ((nW : ℤ) - nV))) := by
  obtain ⟨t, ht⟩ : ∃ t, nW = (nV - nM) + t := ⟨nW - (nV - nM), by omega⟩
  have htt : nW - (nV - nM) = t := by omega
  have hexp : -(d : ℤ) * ((nW : ℤ) - nV) = ((d * nM : ℕ) : ℤ) - ((d * t : ℕ) : ℤ) := by
    have : (nW : ℤ) - nV = (t : ℤ) - nM := by omega
    rw [this]; push_cast; ring
  rw [htt, hexp, zpow_sub₀ hW, zpow_natCast, zpow_natCast]
  push_cast
  rw [mul_pow, mul_pow, mul_pow, inv_pow, ← pow_mul, ← pow_mul]
  field_simp
  rw [pow_mul (W : ℝ) d t]
/-- **`claim:size` for the weighted value** (twin of `lwClaimSize`, `LWSizeClaim.lean:1118`) -/
theorem lwMomentExp_claimSize {d L W : ℕ} [NeZero L] [NeZero W] (Γ : LGraph E I) (hN : Γ.Normal) (D : LData (Idx d L W))
    {m : ℂ} {Ψ K₀ K₁ : ℝ} (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (ℓe : E → Idx d L W) (Wt : (E ⊕ I → Idx d L W) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖valW Γ D Wt ℓe‖ ≤ Γ.sizeConst K₀ K₁ * Γ.scalingSize Ψ W d L := by
  have : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hb := lwMomentExp_valW_norm_le Γ hN D hM hG hGd hS hSp ℓe Wt hWt
  have hW : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  rw [show (Fintype.card (Idx d L W) : ℝ) = ((((W * L) ^ d : ℕ)) : ℝ) by rw [Gauss.card_Idx]] at hb
  refine hb.trans (le_of_eq ?_)
  have hal := lwMomentExp_size_alg W d L Γ.nM Γ.nV Γ.nW hW h1 h2 K₀
  unfold LGraph.sizeConst LGraph.scalingSize Counters.scalingSize
  change ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) *
      (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) = _
  calc ‖Γ.coeff‖ * Ψ ^ Γ.nS * ((((W * L) ^ d : ℕ) : ℝ) ^ Γ.nM * K₁ ^ (Γ.nV - Γ.nM) *
        (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM)))
      = ‖Γ.coeff‖ * Ψ ^ Γ.nS * K₁ ^ (Γ.nV - Γ.nM) *
        (((((W * L) ^ d : ℕ) : ℝ)) ^ Γ.nM * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nV - Γ.nM))) := by ring
    _ = _ := by rw [hal]; simp only [LGraph.counters]; ring
/-- **`scalemole` for the weighted value** (twin of `lwScalemole_holds`, `AuxGraph.lean:1130`) -/
theorem lwMomentExp_scalemole {d L W : ℕ} [NeZero L] [NeZero W] (hd : 3 ≤ d) (Γ : LGraph E I) (hN : Γ.Normal)
    (D : LData (Idx d L W)) {m : ℂ} {Ψ C c r : ℝ} (hM : ∀ x y, D.M x y = if x = y then m else 0)
    (hG : ∀ x y, x ≠ y → ‖D.G x y‖ ≤ Ψ) (hGd : ∀ x, ‖D.G x x - m‖ ≤ Ψ) (hC : 0 ≤ C) (hc : 0 < c)
    (hS : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSp : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ)))) (hr : 0 ≤ r)
    (ℓe : E → Idx d L W) (a b : E) (hab : Γ.molOf (Sum.inl a) = Γ.molOf (Sum.inl b))
    (hfar : (Fintype.card (E ⊕ I) : ℝ) * r < (lwBdist d L W (ℓe a) (ℓe b) : ℝ))
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖valW Γ D Wt ℓe‖ ≤ Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) * Γ.scalingSize Ψ W d L := by
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have htail := auxGraph_tail_sum hd Γ hN D (r := r) hGd hC hc hS hSp ℓe
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS *
        (Real.exp (-(c * r / 2)) * (Γ.waved.map fun e => ‖WEdge.val (auxGraph_wdata D c) (Sum.elim ℓe ℓi) e‖).prod) := by
    intro ℓi
    refine auxGraph_term_tail Γ hN D hM hG hGd hc _ ?_
    by_contra hcon
    have hconf : ∀ e ∈ Γ.waved, (lwBdist d L W (Sum.elim ℓe ℓi e.x) (Sum.elim ℓe ℓi e.y) : ℝ) ≤ r := by
      intro e he
      by_contra h
      exact hcon ⟨e, he, not_le.1 h⟩
    have hd' := auxGraph_mol_dist Γ hN.1 (Sum.elim ℓe ℓi) hr hconf hab
    exact absurd hfar (not_lt.2 hd')
  unfold valW
  have h1 : ‖∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * Γ.term D (Sum.elim ℓe ℓi)‖
      ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓi _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hWt _)
  exact h1.trans ((Finset.sum_le_sum fun ℓi _ => hpt ℓi).trans htail)
end Weighted
/-! ## 4. The weighted expansion identity: `E|f^D|^p ≤ Σ_o ‖E 𝒱_o‖` -/
section Expand
variable {d : ℕ} (sz : Sizes d)
/-- the weight of the starting graph pulled back to an output `o` through its provenance map: `Π_k 1_D(blk ℓ(π β^{(k)}))` -/
def lwMomentExp_wt (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : ProvOutX (fxyPowGraph p).pack) :
    (o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ :=
  fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (o.π (Sum.inr (localReg_fxyBeta k)))) ∈ Dm then 1 else 0
theorem lwMomentExp_wt_abs (n : ℕ) (Dm : Finset (Zd d (sz.L n))) {p : ℕ} (o : ProvOutX (fxyPowGraph p).pack)
    (ℓ : o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n)) : |lwMomentExp_wt sz n Dm o ℓ| ≤ 1 := by
  unfold lwMomentExp_wt
  have h0 : ∀ k ∈ (Finset.univ : Finset (Fin p)), 0 ≤ if STblk sz n (ℓ (o.π (Sum.inr (localReg_fxyBeta k)))) ∈ Dm then (1 : ℝ) else 0 :=
    fun k _ => by split_ifs <;> norm_num
  rw [abs_of_nonneg (Finset.prod_nonneg h0)]
  exact Finset.prod_le_one₀ h0 fun k _ => by split_ifs <;> norm_num
/-- **the weighted expansion** (twin of `lwMoment_expand`, `LWMoment.lean:258`): `E |f^D_{xy}|^p ≤ Σ_o ‖E 𝒱_o^{π_o^*𝟙_D}‖` -/
theorem lwMomentExp_expand {p : ℕ} (hp : Even p) (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    {outs : List (ProvOutX (fxyPowGraph p).pack)} (hW : ∀ o ∈ outs, p ≤ o.Q.g.waved.countP (fun e => !e.col))
    (hX : WExp (mE E) (fxyPowGraph p).pack (outs.map (·.ev (mE E)))) (Dm : Finset (Zd d (sz.L n)))
    (x y : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP ≤
      (outs.map fun o => ‖∫ ω, pvalW o.Q (lwMoment_D sz n E t ω) (lwMomentExp_wt sz n Dm o) ![x, y] ∂sz.seqP‖).sum := by
  classical
  have hm0 : mE E ≠ 0 := lwWx_mE_ne E hE
  have hnorm : ‖mE E‖ = 1 := norm_mE hE.le
  have hflow := lwWx_flow E t hE
  have him : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
  have hmt : ‖mE E‖ ^ 2 * t < 1 := by rw [hnorm]; simpa using ht1
  have hSp := fun i j => lwSplus_spec (sz := sz) (n := n) ht0.le hmt i j
  have hSpT := lwSymm_lwSplus_symm (sz := sz) (n := n) ht0.le hmt
  have hid := WExp.prod hX (lwSplus sz n t (mE E)) (Matrix.diagonal fun _ => mE E) (RBM.Green.gaussIBP sz) him ht0 hm0 hflow
    hSp hSpT (fun a => by simp) (fun a b hab => by simp [Matrix.diagonal_apply_ne _ hab])
    (fun _ x => if STblk sz n x ∈ Dm then 1 else 0) ![x, y]
  have hL : ∀ ω : sz.SeqΩ, pvalW (fxyPowGraph p).pack
      (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω)
      (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] =
        ((t ^ p * ‖LWfD sz n E t ω Dm x y‖ ^ p : ℝ) : ℂ) := by
    intro ω
    rw [lwMoment_Dt_eq, lwMomentExp_pvalW_smul, lwEngine_fxy_nWS, lwProv_bridge sz hp n E t ω Dm x y]
    push_cast; ring
  have hR : ∀ o ∈ outs, ∫ ω, pvalW (o.ev (mE E)).Q
      (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω)
      (lwMomentExp_wt sz n Dm o) ![x, y] ∂sz.seqP =
      (mE E ^ o.tag.1 * star (mE E) ^ o.tag.2) * ((t : ℂ) ^ (o.Q.g.waved.countP fun e => !e.col) *
        ∫ ω, pvalW o.Q (lwMoment_D sz n E t ω) (lwMomentExp_wt sz n Dm o) ![x, y] ∂sz.seqP) := by
    intro o _
    have e1 : ∀ ω : sz.SeqΩ, pvalW (o.ev (mE E)).Q
        (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω)
        (lwMomentExp_wt sz n Dm o) ![x, y] = (mE E ^ o.tag.1 * star (mE E) ^ o.tag.2) *
          ((t : ℂ) ^ (o.Q.g.waved.countP fun e => !e.col) *
            pvalW o.Q (lwMoment_D sz n E t ω) (lwMomentExp_wt sz n Dm o) ![x, y]) := by
      intro ω
      rw [lwMoment_Dt_eq]
      exact (lwMomentExp_pvalW_evX (mE E) (o.tag, o.Q) _ (lwMomentExp_wt sz n Dm o) ![x, y]).trans
        (congrArg _ (lwMomentExp_pvalW_smul o.Q (lwMoment_D sz n E t ω) (t : ℂ) _ ![x, y]))
    simp only [e1]
    rw [integral_const_mul, integral_const_mul]
  have hI0 : 0 ≤ ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP := integral_nonneg fun ω => by positivity
  have hLHS : (∫ ω, pvalW (fxyPowGraph p).pack
      (lwSampleData sz n (zt E t) t (Matrix.diagonal fun _ => mE E) (lwS sz n t) (lwSplus sz n t (mE E)) ω)
      (fun ℓ => ∏ k : Fin p, if STblk sz n (ℓ (Sum.inr (localReg_fxyBeta k))) ∈ Dm then (1 : ℝ) else 0) ![x, y] ∂sz.seqP) =
      ((t ^ p * ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP : ℝ) : ℂ) := by
    simp only [hL]
    rw [integral_complex_ofReal, integral_const_mul]
  rw [hLHS] at hid
  have hid' : ((t ^ p * ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP : ℝ) : ℂ) =
      (outs.map fun o => (mE E ^ o.tag.1 * star (mE E) ^ o.tag.2) * ((t : ℂ) ^ (o.Q.g.waved.countP fun e => !e.col) *
        ∫ ω, pvalW o.Q (lwMoment_D sz n E t ω) (lwMomentExp_wt sz n Dm o) ![x, y] ∂sz.seqP)).sum := by
    rw [hid, List.map_map]
    congr 1
    exact List.map_congr_left fun o ho => hR o ho
  have hnn : 0 ≤ t ^ p * ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP := mul_nonneg (by positivity) hI0
  have h1 : t ^ p * ∫ ω, ‖LWfD sz n E t ω Dm x y‖ ^ p ∂sz.seqP ≤
      (outs.map fun o => t ^ p * ‖∫ ω, pvalW o.Q (lwMoment_D sz n E t ω) (lwMomentExp_wt sz n Dm o) ![x, y] ∂sz.seqP‖).sum := by
    have h2 := congrArg norm hid'
    rw [Complex.norm_real, Real.norm_of_nonneg hnn] at h2
    rw [h2]
    refine (lwMoment_norm_list_sum_le _ _).trans ?_
    refine List.sum_le_sum fun o ho => ?_
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hn1 : ‖mE E‖ ^ o.tag.1 * ‖star (mE E)‖ ^ o.tag.2 = 1 := by
      rw [norm_star, hnorm]; simp
    rw [hn1, one_mul]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht0.le ht1.le (hW o ho)) (norm_nonneg _)
  rw [List.sum_map_mul_left] at h1
  exact le_of_mul_le_mul_left h1 (by positivity)
end Expand
/-! ## 5. The context: `LWAssm` for the class `Φ_B` (`Φ_B(0) = B_{ctl}^{1/2}`), copied from the (A) file -/
section Context
variable {d : ℕ}
private theorem lwMomentExp_flow_im_pos (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _) (hflow.2 n).2.1
private theorem lwMomentExp_wneg (W : ℝ) (hW : 0 ≤ W) (d : ℕ) : W ^ (-(d : ℝ)) = (W ^ d)⁻¹ := by
  rw [Real.rpow_neg hW, Real.rpow_natCast]
theorem lwMomentExp_phi_zero (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) :
    LWPhiB sz (d : ℝ) K t n 0 = (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
  unfold LWPhiB Sizes.Bctl
  rw [lwMomentExp_wneg _ (Nat.cast_nonneg _)]
  simp
private theorem lwMomentExp_phi_sq (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    LWPhiB sz (d : ℝ) K t n x ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊x⌋₊ (K n)) := by
  unfold LWPhiB
  rw [lwMomentExp_wneg _ (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
  unfold Bparam
  positivity
/-- **`LWAssm` for the B class** from `LWAssmExp` (copy of `lwMEA_assm`, `LWMomentExpA.lean:127`): `Φ_B = LWPhiB`, `K n = ⌊ℓ n⌋ ∧ L n`, at the window `ε₁ = min(ε₀, d c/2)` -/
theorem lwMomentExp_assm (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ lemT (z n))
    {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ LWAssm sz (STflowE z) t ε₁ Ψ (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t)
      ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) := by
  obtain ⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩ := hA
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (lemT_lt_one (lwMomentExp_flow_im_pos sz hflow n))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min ε₀ ((d : ℝ) * c / 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c := by
    have : ε₁ ≤ (d : ℝ) * c / 2 := by rw [hε₁def]; exact min_le_right _ _
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  have ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1 := Eventually.of_forall fun n => ⟨ht0 n, (ht1 n).le⟩
  have hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [lwN_Bctl_le sz hκ hε h𝔡 hflow htT] with n hn
    have h1 := hn (t n) (ht0 n) le_rfl
    rw [← hcdef] at h1
    have h2 := lwN_size_rpow_neg_le sz n hc.le
    have h3 : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
    rw [lwMomentExp_wneg _ (Nat.cast_nonneg _)]
    exact (h1.trans h2).trans h3
  set K : ℕ → ℕ := fun n => min ⌊ℓ n⌋₊ (sz.L n) with hKdef
  obtain ⟨-, hcls, hrel⟩ := LWPhiB_psiAll sz (by omega : 2 ≤ d) (ε₀ := ε₁) (c₀ := (d : ℝ)) K t hε₁pos le_rfl hg ht hup
  have hwin' : LWWindow sz ε₁ Ψ := by
    filter_upwards [hwin] with n hn
    exact ⟨hn.1, hn.2.trans (Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith))⟩
  have hinit' : LWInit sz (STflowE z) t ε₁ Ψ := by
    refine ⟨?_, hinit.2⟩
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  have hL2 : LWLoop2 sz (STflowE z) t (LWPhiB sz (d : ℝ) K t) := by
    refine lwN_prec_mono hsize (c := 1) ?_ (hloop (1 / 𝔠) (by positivity))
    filter_upwards [lwN_Wneg_le sz h𝔠 hband] with n hn
    rintro ⟨σ, a, b⟩ ω
    simp only
    have hLn : (zdistInf d (sz.L n) (a - b) : ℕ) ≤ sz.L n := lwMoment_zdistInf_le _ _
    rw [lwMomentExp_phi_sq, Nat.floor_natCast, one_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr (by positivity)) ?_, ?_⟩
    · unfold Bparam; positivity
    · refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact lwN_tailW_le (L := sz.L n) _ hLn (by have := sz.three_le_L n; omega) rfl (hℓ0 n) (ht0 n) (ht1 n) hn
  exact ⟨ε₁, hε₁pos, hε₁pos, hwin', hinit', hcls, hrel, hL2⟩
end Context
/-! ## 6. The normalized pins: far (`AnpFarAndAt`) and near (`AnpNearInfAt`) in the form the assembly consumes -/
section Pins
/-- `a^n ≤ c^{|n|} b^n` for `0 < a ≤ b ≤ c a`, `c ≥ 1`, `n ∈ ℤ` -/
theorem lwMomentExp_zpow_cmp {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ c * a) (hc : 1 ≤ c) (n : ℤ) :
    a ^ n ≤ c ^ n.natAbs * b ^ n := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp only [zpow_natCast, Int.natAbs_natCast]
    exact (pow_le_pow_left₀ ha.le hab k).trans (le_mul_of_one_le_left (pow_nonneg hb.le k) (one_le_pow₀ hc))
  · simp only [_root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast]
    have h1 : b ^ k ≤ c ^ k * a ^ k := by rw [← mul_pow]; exact pow_le_pow_left₀ hb.le hba k
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (pow_pos ha k) (pow_pos hb k)]
    linarith
/-- `Ψ_t ≤ c_d 𝖳_t(0)` for `g² ≤ L²(1-t)` (the zero mode of `B_{t,0}` is dominated, `zeroMode_le_of_ge`), `c_d = (1 + 2^{d-1})^{1/2}` -/
theorem lwMomentExp_PsiT_le {d L : ℕ} [NeZero L] {W g t : ℝ} (hd : 2 ≤ d) (hW : 0 < W) (ht : t < 1)
    (hgt : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) :
    PsiT d L W g t ≤ Real.sqrt (1 + 2 ^ (d - 1)) * sfT d L W g t 0 := by
  have hL : (1 : ℝ) ≤ L := Nat.one_le_cast.2 (NeZero.pos L)
  have hgt' : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hz := zeroMode_le_of_ge hd hL ht (le_refl (0 : ℝ)) (by positivity) hgt'
  have hB : Bparam d L g t 0 ≤ (1 + 2 ^ (d - 1)) * (g ^ 2 + |1 - t|)⁻¹ := by
    simp only [Bparam, Nat.cast_zero, zero_add, one_pow, inv_one, mul_one] at hz ⊢
    nlinarith
  have hWd : 0 ≤ (W ^ d)⁻¹ := by positivity
  have hA : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  rw [PsiT, sfT_zero, ← Real.sqrt_mul hWd, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  nlinarith [mul_le_mul_of_nonneg_left hB hWd]
/-- the pin in the normalized form the assembly consumes (`AnpFarAndAt` with `θ = (W^d η)⁻¹` / `AnpNearInfAt`): `(W^d)^q Γ.valOn ≤ X^q C η^{-q} Ψ_t^{ord-p} 𝖳_t(|a-b|∧ℓ)^p` for `Λ² ≤ X` -/
def lwMomentExp_PinN (d : ℕ) {p q : ℕ} (Γ : NGraph p q)
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L] (W g t η ℓ Λ X : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
    0 < η → η ≤ 1 - t → 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → 1 ≤ Λ → Λ ^ 2 ≤ X →
    ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
      (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
      (∀ α, ∑ β, ξ α β ^ 2 ≤ ((W ^ d) * η)⁻¹) → ∀ a b : Zd d L,
        (W ^ d) ^ q * Γ.valOn ξ (fun _ => a) (fun _ => b) (Fintype.piFinset fun _ : Fin q => dom L a b ℓ) ≤
          X ^ q * C * (η⁻¹) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
            sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p
/-- **far pin, normalized** (`AnpFarAndAt` with the domain `domFar`, `domFar_eq`) -/
theorem lwMomentExp_pinN_far {d : ℕ} (hd : 3 ≤ d) {p q : ℕ} (hp : 0 < p) {Γ : NGraph p q} (hF : AnpFarAndAt d Γ) :
    lwMomentExp_PinN d Γ (fun L _ a b ℓ => domFar d L a b ℓ) := by
  obtain ⟨C, hC, H⟩ := hF
  have hc1 : (1 : ℝ) ≤ Real.sqrt (1 + 2 ^ (d - 1)) := by
    rw [Real.one_le_sqrt]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (d - 1)]
  refine ⟨C * Real.sqrt (1 + 2 ^ (d - 1)) ^ (Γ.ordN - (p : ℤ)).natAbs, by positivity, ?_⟩
  intro L _ W g t η ℓ Λ X hW hg ht hgt hη hηt hℓ1 hℓΛ hΛ hΛX ξ hξ hξT hrow a b
  have hX : 1 ≤ X := by nlinarith
  have hWd : 0 < W ^ d := pow_pos hW d
  set θ : ℝ := ((W ^ d) * η)⁻¹ with hθ
  have hθ0 : 0 < θ := by positivity
  have h1 := H L W g t θ ℓ hW ht hθ0 (by linarith) ξ hξ hξT hrow (fun _ => a) (fun _ => b)
  rw [domFar_eq hp] at h1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  have hT0 : 0 < sfT d L W g t 0 := by
    rw [sfT_zero]
    have : 0 < g ^ 2 + |1 - t| := by have := abs_pos.2 (show 1 - t ≠ 0 by linarith); positivity
    positivity
  have hP := lwMomentExp_PsiT_le (d := d) (L := L) (by omega) hW ht hgt
  have hP0 := sfT_zero_le_PsiT (d := d) (L := L) (g := g) (t := t) hW
  have hz := lwMomentExp_zpow_cmp hT0 hP0 hP hc1 (Γ.ordN - (p : ℤ))
  have hηq : ((W ^ d) ^ q) * θ ^ q = (η⁻¹) ^ q := by
    rw [← mul_pow]; congr 1; rw [hθ]; field_simp
  have hT : 0 ≤ sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := pow_nonneg (sfT_nonneg _) _
  calc (W ^ d) ^ q * Γ.valOn ξ (fun _ => a) (fun _ => b) (Fintype.piFinset fun _ : Fin q => domFar d L a b ℓ)
      ≤ (W ^ d) ^ q * (C * θ ^ q * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * ((W ^ d) ^ q * θ ^ q) * sfT d L W g t 0 ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by ring
    _ ≤ C * (η⁻¹) ^ q * (Real.sqrt (1 + 2 ^ (d - 1)) ^ (Γ.ordN - (p : ℤ)).natAbs * PsiT d L W g t ^ (Γ.ordN - (p : ℤ))) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by
        rw [hηq]
        gcongr
    _ ≤ _ := by
        have : 1 ≤ X ^ q := one_le_pow₀ hX
        have hpos : 0 ≤ C * (η⁻¹) ^ q * (Real.sqrt (1 + 2 ^ (d - 1)) ^ (Γ.ordN - (p : ℤ)).natAbs * PsiT d L W g t ^ (Γ.ordN - (p : ℤ))) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by
          have hPs : 0 ≤ PsiT d L W g t := PsiT_nonneg
          positivity
        nlinarith
/-- **near pin, normalized** (`AnpNearInfAt`, centre `cen`; the domain lies in the `ℓ^∞` ball of radius `ℓ` around `cen`) -/
theorem lwMomentExp_pinN_near {d : ℕ} {p q : ℕ} {Γ : NGraph p q} (hN : AnpNearInfAt d Γ)
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (cen : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → Zd d L)
    (hcen : ∀ (L : ℕ) [NeZero L] (a b : Zd d L) (ℓ : ℝ), ∀ α ∈ dom L a b ℓ, ((zdistInf d L (cen L a b - α) : ℕ) : ℝ) ≤ ℓ) :
    lwMomentExp_PinN d Γ dom := by
  obtain ⟨C, hC, H⟩ := hN
  refine ⟨C, hC, ?_⟩
  intro L _ W g t η ℓ Λ X hW hg ht hgt hη hηt hℓ1 hℓΛ hΛ hΛX ξ hξ hξT hrow a b
  have h1 := H L W g t hW hg ht hgt ℓ Λ hℓ1 hℓΛ ξ hξ hξT (cen L a b) a b (dom L a b ℓ) (hcen L a b ℓ)
  rw [lwMomExp_valOnD_eq_valOn] at h1
  have ht1 : 0 < 1 - t := by linarith
  have hWd : 0 < W ^ d := pow_pos hW d
  have hq : (W ^ d) ^ q * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q = (Λ ^ 2 / (1 - t)) ^ q := by
    rw [← mul_pow]; congr 1; field_simp
  have hdiv : Λ ^ 2 / (1 - t) ≤ X * η⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul hΛX (inv_anti₀ hη hηt) (by positivity) (by nlinarith)
  have hq2 : (Λ ^ 2 / (1 - t)) ^ q ≤ (X * η⁻¹) ^ q := pow_le_pow_left₀ (by positivity) hdiv q
  have hPs : 0 ≤ PsiT d L W g t := PsiT_nonneg
  have hT : 0 ≤ sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := pow_nonneg (sfT_nonneg _) _
  have hzp : 0 ≤ PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) := zpow_nonneg hPs _
  calc (W ^ d) ^ q * Γ.valOn ξ (fun _ => a) (fun _ => b) (Fintype.piFinset fun _ : Fin q => dom L a b ℓ)
      ≤ (W ^ d) ^ q * (C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * ((W ^ d) ^ q * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q) * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by ring
    _ ≤ C * ((X * η⁻¹) ^ q) * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by
        rw [hq]
        gcongr
    _ = _ := by rw [mul_pow]; ring
end Pins
/-! ## 7. The floor `W^{-D'}` of the edge variables, homogeneity, exponent arithmetic -/
section Floor
theorem lwMomentExp_list_prod_le_one {α : Type*} (l : List α) (g : α → ℝ) (h0 : ∀ e, 0 ≤ g e) (h1 : ∀ e, g e ≤ 1) :
    (l.map g).prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons]
    have hl0 : 0 ≤ (l.map g).prod := List.prod_nonneg fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy; exact h0 e
    nlinarith [h0 b, h1 b]
/-- `Π f ≤ Π g + (2^n - 1) w` for `f ≤ g + w`, `0 ≤ f`, `0 ≤ g ≤ 1`, `0 ≤ w ≤ 1` -/
theorem lwMomentExp_list_prod_add_le {α : Type*} (l : List α) (f g : α → ℝ) (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hf0 : ∀ e, 0 ≤ f e) (hg0 : ∀ e, 0 ≤ g e) (hg1 : ∀ e, g e ≤ 1) (hfg : ∀ e, f e ≤ g e + w) :
    (l.map f).prod ≤ (l.map g).prod + (2 ^ l.length - 1) * w := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have hPf : 0 ≤ (l.map f).prod := List.prod_nonneg fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy; exact hf0 e
    have hPg : 0 ≤ (l.map g).prod := List.prod_nonneg fun y hy => by
      obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy; exact hg0 e
    have hP1 : (l.map g).prod ≤ 1 := lwMomentExp_list_prod_le_one l g hg0 hg1
    have hc : 0 ≤ (2 : ℝ) ^ l.length - 1 := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := l.length); linarith
    have h1 : f a * (l.map f).prod ≤ (g a + w) * ((l.map g).prod + (2 ^ l.length - 1) * w) :=
      mul_le_mul (hfg a) ih hPf (by linarith [hg0 a])
    have e2 : (2 : ℝ) ^ (l.length + 1) = 2 * 2 ^ l.length := by ring
    rw [e2]
    nlinarith [mul_nonneg (mul_nonneg hc hw0) (sub_nonneg.2 (hg1 a)), mul_nonneg hw0 (sub_nonneg.2 hP1),
      mul_nonneg (mul_nonneg hc hw0) (sub_nonneg.2 hw1)]
/-- the floor in the value of a nested graph: `ξ ≤ ξ' + w` edgewise, `ξ' ≤ 1`, gives `valOn ξ ≤ valOn ξ' + |S| 2^{|E|} w` -/
theorem lwMomentExp_valOn_floor {p q : ℕ} (Γ : NGraph p q) {ι : Type*} [Fintype ι] (ξ ξ' : ι → ι → ℝ) (w : ℝ) (hw0 : 0 ≤ w)
    (hw1 : w ≤ 1) (h0 : ∀ α β, 0 ≤ ξ α β) (h0' : ∀ α β, 0 ≤ ξ' α β) (h1' : ∀ α β, ξ' α β ≤ 1)
    (hξ : ∀ α β, ξ α β ≤ ξ' α β + w) (a b : Fin p → ι) (S : Finset (Fin q → ι)) :
    Γ.valOn ξ a b S ≤ Γ.valOn ξ' a b S + S.card * (2 ^ Γ.es.length * w) := by
  unfold NGraph.valOn
  have hS : ∀ ℓ ∈ S, (Γ.es.map fun e => if e.ghost then (1 : ℝ) else
        ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod ≤
      (Γ.es.map fun e => if e.ghost then (1 : ℝ) else
        ξ' (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod + 2 ^ Γ.es.length * w := by
    intro ℓ _
    have := lwMomentExp_list_prod_add_le Γ.es
      (fun e => if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v))
      (fun e => if e.ghost then (1 : ℝ) else ξ' (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)) w hw0 hw1
      (fun e => by split_ifs <;> [norm_num; exact h0 _ _]) (fun e => by split_ifs <;> [norm_num; exact h0' _ _])
      (fun e => by split_ifs <;> [norm_num; exact h1' _ _]) (fun e => by split_ifs <;> [linarith; exact hξ _ _])
    refine this.trans ?_
    have : (2 : ℝ) ^ Γ.es.length * w - w ≤ 2 ^ Γ.es.length * w := by linarith
    nlinarith
  calc _ ≤ ∑ ℓ ∈ S, ((Γ.es.map fun e => if e.ghost then (1 : ℝ) else
        ξ' (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod + 2 ^ Γ.es.length * w) :=
        Finset.sum_le_sum hS
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
/-- homogeneity of the value of a ghost-free nested graph in the edge variables: `valOn (s ξ) = s^{|E|} valOn ξ` -/
theorem lwMomentExp_valOn_smul {p q : ℕ} (Γ : NGraph p q) (hNG : Γ.NoGhost) {ι : Type*} [Fintype ι] (ξ : ι → ι → ℝ) (s : ℝ)
    (a b : Fin p → ι) (S : Finset (Fin q → ι)) :
    Γ.valOn (fun α β => s * ξ α β) a b S = s ^ Γ.es.length * Γ.valOn ξ a b S := by
  unfold NGraph.valOn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  have key : ∀ l : List (NEdge p q), (∀ e ∈ l, e.ghost = false) →
      (l.map fun e => if e.ghost then (1 : ℝ) else s * ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod =
        s ^ l.length * (l.map fun e => if e.ghost then (1 : ℝ) else ξ (Sum.elim (Sum.elim a b) ℓ e.u) (Sum.elim (Sum.elim a b) ℓ e.v)).prod := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons e l ih =>
      intro h
      have he := h e (List.mem_cons_self ..)
      have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
      simp only [List.map_cons, List.prod_cons, List.length_cons, he, Bool.false_eq_true, ite_false, this, pow_succ]
      ring
  exact key Γ.es hNG
end Floor
/-! ## 8. The radius of the edge variables and the exponent arithmetic -/
section Arith
/-- the radius `ρ = 2 K (log W)^{3/2} + 1` satisfies `√ρ ≤ τ log N` eventually (the radius hypothesis of `lwXiExpClaim_holds`) -/
theorem lwMomentExp_rad {d : ℕ} (sz : Sizes d) (hd : d ≠ 0) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) {K : ℝ} (hK : 0 < K) (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, Real.sqrt (2 * (K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) + 1) ≤
      τ * Real.log ((sz.size n : ℕ) : ℝ) := by
  set Y₀ : ℝ := max 1 (((2 * K + 1) / τ ^ 2) ^ 2) with hY₀
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp Y₀),
    hsz.eventually_ge_atTop 1] with n hb hbig hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlogW : Y₀ ≤ Real.log ((sz.W n : ℕ) : ℝ) := (Real.le_log_iff_exp_le hW0).2 (le_trans hbig hb)
  set y : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hy
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hlogW
  have hy0 : 0 < y := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ N := by
    have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
    have h : sz.W n ≤ sz.size n := by
      unfold Sizes.size
      calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd _
    rw [hN]; exact_mod_cast h
  have hlogN : y ≤ Real.log N := Real.log_le_log hW0 hWN
  have hsq : (2 * K + 1) / τ ^ 2 ≤ Real.sqrt y :=
    (Real.le_sqrt (by positivity) hy0.le).2 (le_trans (le_max_right _ _) hlogW)
  have h32 : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hsy : 1 ≤ Real.sqrt y := by rw [Real.one_le_sqrt]; exact hy1
  have hτ2 : 0 < τ ^ 2 := by positivity
  have h2K : 2 * K + 1 ≤ τ ^ 2 * Real.sqrt y := by
    have := mul_le_mul_of_nonneg_left hsq hτ2.le
    rwa [mul_div_cancel₀ _ hτ2.ne'] at this
  refine Real.sqrt_le_iff.2 ⟨by have := Real.log_nonneg (show (1 : ℝ) ≤ N by linarith); positivity, ?_⟩
  rw [h32]
  have hρ : 2 * (K * (y * Real.sqrt y)) + 1 ≤ (2 * K + 1) * (y * Real.sqrt y) := by
    nlinarith [mul_le_mul hy1 hsy zero_le_one hy0.le]
  have hsy2 : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  calc 2 * (K * (y * Real.sqrt y)) + 1 ≤ (2 * K + 1) * (y * Real.sqrt y) := hρ
    _ ≤ (τ ^ 2 * Real.sqrt y) * (y * Real.sqrt y) := by gcongr
    _ = τ ^ 2 * y * (Real.sqrt y * Real.sqrt y) := by ring
    _ = (τ * y) ^ 2 := by rw [hsy2]; ring
    _ ≤ (τ * Real.log N) ^ 2 := by gcongr
/-- the exponent bookkeeping of the pin term (`n_M = q ≤ p`, `ord ≥ 2p`, `η ≤ 1`, `f0 ≤ 1`) -/
theorem lwMomentExp_arith {X M f0 η C K1 T : ℝ} {e1 k len q p : ℕ} {a o : ℤ} (hX : 1 ≤ X) (hM : 1 ≤ M) (hf0 : 0 < f0)
    (hf1 : f0 ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 0 ≤ T) (hC : 0 ≤ C) (hK1 : 0 ≤ K1) (hq : q ≤ p)
    (hord : 2 * (p : ℤ) ≤ o) (ho : o = (e1 : ℤ) + a) :
    K1 * (M * X * f0) ^ e1 * (X ^ (k + len) * (X ^ q * C * (η⁻¹) ^ q * f0 ^ (a - p) * T ^ p)) ≤
      X ^ (e1 + k + len + q) * (K1 * M ^ e1 * C) * (η⁻¹ * f0 * T) ^ p := by
  have hX0 : 0 < X := by linarith
  have hηi : 1 ≤ η⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hfz : f0 ^ e1 * f0 ^ (a - p) = f0 ^ (o - p) := by
    rw [← zpow_natCast, ← zpow_add₀ hf0.ne']; congr 1; omega
  have hf2 : f0 ^ (o - p) ≤ f0 ^ (p : ℤ) := zpow_le_zpow_right_of_le_one₀ hf0 hf1 (by omega)
  have hη2 : (η⁻¹) ^ q ≤ (η⁻¹) ^ p := pow_le_pow_right₀ hηi hq
  have hpf : (η⁻¹ * f0 * T) ^ p = (η⁻¹) ^ p * f0 ^ (p : ℤ) * T ^ p := by rw [zpow_natCast, mul_pow, mul_pow]
  have hL : K1 * (M * X * f0) ^ e1 * (X ^ (k + len) * (X ^ q * C * (η⁻¹) ^ q * f0 ^ (a - p) * T ^ p)) =
      (X ^ (e1 + k + len + q) * (K1 * M ^ e1 * C)) * ((η⁻¹) ^ q * (f0 ^ e1 * f0 ^ (a - p)) * T ^ p) := by
    rw [mul_pow, mul_pow]
    have : X ^ (e1 + k + len + q) = X ^ e1 * X ^ (k + len) * X ^ q := by ring
    rw [this]; ring
  rw [hL, hfz, hpf]
  have hKM : 0 ≤ X ^ (e1 + k + len + q) * (K1 * M ^ e1 * C) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hKM
  exact mul_le_mul_of_nonneg_right (mul_le_mul hη2 hf2 (zpow_nonneg hf0.le _) (by positivity)) (by positivity)
end Arith
/-! ## 9. The outputs of the engine: envelope, errors, the outputs with `𝓜_x = 𝓜_y` -/
section Out
variable {d : ℕ} {sz : Sizes d} {κ ε 𝔡 𝔠 : ℝ} {z : ℕ → ℂ} {t : ℕ → ℝ} {ε₀ ε₁ C₁ C₂ C₃ : ℝ} {Cc : ℝ → ℝ} {Ψ ℓ : ℕ → ℝ}
  {Φ : ℕ → ℝ → ℝ}
/-- the right side of `LWMomentExp` -/
def lwMomentExp_R (sz : Sizes d) (E t ℓ : ℕ → ℝ) (p : ℕ) (D : ℝ) (n : ℕ) (x y : Idx d (sz.L n) (sz.W n)) : ℝ :=
  ((etaT (E n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
    (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D)
/-- the context of a pin: `LWAssm` for the B class at the window `ε₁` (`lwMomentExp_assm`) next to `LWAssmExp` at `ε₀` -/
private structure lwMomentExp_Ctx (d : ℕ) (κ ε 𝔡 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (ε₀ ε₁ : ℝ) (Ψ ℓ : ℕ → ℝ) : Prop where
  S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ
    (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t)
  hAss : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ
theorem lwMomentExp_t1 (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ C₁ C₂ C₃ Cc Ψ Φ) (n : ℕ) : t n < 1 :=
  (lwMoment_flow_facts S).2.2.1 n
theorem lwMomentExp_R_ge (E t ℓ : ℕ → ℝ) (p : ℕ) (D : ℝ) (n : ℕ) (x y : Idx d (sz.L n) (sz.W n)) (ht1 : t n ≤ 1) :
    ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ lwMomentExp_R sz E t ℓ p D n x y := by
  have h1 := inv_nonneg.2 (lwN_etaT_nonneg (E n) (t n) ht1)
  have h2 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by unfold Sizes.Bctl Bparam; positivity) _
  have h3 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
    (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n))
  exact le_add_of_nonneg_left (pow_nonneg (by positivity) _)
theorem lwMomentExp_floor_le (hd : d ≠ 0) (n : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ((sz.size n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
  have h : sz.W n ≤ sz.size n := by
    unfold Sizes.size
    exact (Nat.le_mul_of_pos_right _ hL).trans (Nat.le_self_pow hd _)
  exact Real.rpow_le_rpow_of_nonpos hW0 (by exact_mod_cast h) (by linarith)
/-- the weighted claim `size` at the sample (twin of `lwMoment_pval_claim`, `LWMoment.lean:644`) -/
theorem lwMomentExp_pval_claim (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ C₁ C₂ C₃ Cc Ψ Φ) {C c : ℝ} (hC : 0 < C) (hc : 0 < c) {n : ℕ}
    (hdec : (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwS sz n 1 x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))) ∧
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖lwSplus sz n (t n) (mE (STflowE z n)) x y‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d (sz.L n) (sz.W n) x y : ℝ)))))
    {ω : sz.SeqΩ} {A : ℝ} (hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω x y‖ ≤ A)
    (Q : PGraph (Fin 2)) (hQ : Q.g.Normal) (x y : Idx d (sz.L n) (sz.W n))
    (Wt : (Q.E' ⊕ Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ) (hWt : ∀ ℓ, |Wt ℓ| ≤ 1) :
    ‖pvalW Q (lwMoment_D sz n (STflowE z n) (t n) ω) Wt ![x, y]‖ ≤
      Q.g.sizeConst C (C * expC (d - 2) c) * Q.g.scalingSize A ((sz.W n : ℕ)) d (sz.L n) := by
  classical
  have hKS := lwKBound_of_decay S.hd hC.le hc hdec.1
  have hKSp := lwKBound_of_decay S.hd hC.le hc hdec.2
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x y)
  obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
  by_cases hf : ∃ ℓ' : Q.E' → Idx d (sz.L n) (sz.W n), ![x, y] = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [lwProv_pvalW_of_factor _ _ _ hℓ']
    exact lwMomentExp_claimSize Q.g hQ (lwMoment_D sz n (STflowE z n) (t n) ω) (m := mE (STflowE z n)) (Ψ := A)
      (K₀ := C) (K₁ := C * expC (d - 2) c) (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply])
      hG hGd hKS hKSp ℓ' Wt hWt
  · rw [lwProv_pvalW_of_not _ _ _ hf, norm_zero]
    refine mul_nonneg (Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)) ?_
    unfold LGraph.scalingSize Counters.scalingSize
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
/-- the polynomial envelope of the weighted value (twin of `lwMoment_env`, `LWMoment.lean:673`), uniform in the weight -/
private theorem lwMomentExp_env (S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ C₁ C₂ C₃ Cc Ψ Φ) (Q : PGraph (Fin 2)) (hQ : Q.g.Normal) :
    ∃ envExp : ℝ, ∀ᶠ n in atTop, ∀ (x y : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ)
      (Wt : (Q.E' ⊕ Q.I' → Idx d (sz.L n) (sz.W n)) → ℝ), (∀ ℓ, |Wt ℓ| ≤ 1) →
      ‖pvalW Q (lwMoment_D sz n (STflowE z n) (t n) ω) Wt ![x, y]‖ ≤ ((sz.size n : ℕ) : ℝ) ^ envExp := by
  obtain ⟨hadm, hE, ht1', -⟩ := lwMoment_flow_facts S
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  have hsz := lwMoment_size_tendsto S
  refine ⟨((Q.g.nM + Q.g.nV + 2 * Q.g.nS + 1 : ℕ) : ℝ), ?_⟩
  filter_upwards [hdec, lwMoment_eta_lower S, hsz.eventually_ge_atTop 2,
    hsz.eventually_ge_atTop (Q.g.sizeConst C (C * expC (d - 2) c))] with n hn hη hN2 hNc x y ω Wt hWt
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hEn : |STflowE z n| < 2 := by linarith [hE n, S.hκ]
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn (ht1' n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one hEn (S.t0 n) (ht1' n)
  have hηN : (etaT (STflowE z n) (t n))⁻¹ ≤ N :=
    calc (etaT (STflowE z n) (t n))⁻¹ ≤ (N ^ (-(1 : ℝ)))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) hη
      _ = N := by rw [Real.rpow_neg_one, inv_inv]
  have hηi : 1 ≤ (etaT (STflowE z n) (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤ 2 * (etaT (STflowE z n) (t n))⁻¹ := by
    intro a b
    have h1 := lwMoment_norm_Gt_le (sz := sz) hEn (ht1' n) n ω a b
    have h2 : ‖mE (STflowE z n)‖ = 1 := norm_mE hEn.le
    unfold STGM
    split_ifs
    · exact (norm_sub_le _ _).trans (by linarith)
    · rw [sub_zero]; linarith
  have h1 := lwMomentExp_pval_claim S hC hc hn hA Q hQ x y Wt hWt
  have h2 := lwMoment_scalingSize_le Q.g (Ψ := 2 * (etaT (STflowE z n) (t n))⁻¹) (B := 2 * N) (by positivity)
    (by linarith) (by linarith) (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega)
  have hK : 0 ≤ Q.g.sizeConst C (C * expC (d - 2) c) :=
    Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have h3 : (2 * N) ^ Q.g.nS ≤ (N ^ 2) ^ Q.g.nS := pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have e : ((((sz.W n) * (sz.L n)) ^ d : ℕ) : ℝ) = N := rfl
  rw [e] at h2
  calc _ ≤ Q.g.sizeConst C (C * expC (d - 2) c) * (N ^ (Q.g.nM + Q.g.nV) * (N ^ 2) ^ Q.g.nS) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))) hK)
    _ ≤ N * (N ^ (Q.g.nM + Q.g.nV) * (N ^ 2) ^ Q.g.nS) := mul_le_mul_of_nonneg_right hNc (by positivity)
    _ = N ^ ((Q.g.nM + Q.g.nV + 2 * Q.g.nS + 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast, ← pow_mul]; ring
/-- **errors** (twin of `lwMoment_prec_err`, `LWMoment.lean:827`): the weighted size bound at the entry scale `Ψ'` gives `N^{-D} ≤ W^{-D} ≤ R` -/
private theorem lwMomentExp_prec_err (H : lwMomentExp_Ctx d κ ε 𝔡 𝔠 sz z t ε₀ ε₁ Ψ ℓ) (hd : d ≠ 0) {p K0 : ℕ} {D Deng : ℝ} (hD0 : 0 < D)
    (hK0 : 1 / 𝔠 ≤ K0) (hDe : (D + 1) / 𝔠 ≤ Deng) {V : ℕ → Type}
    (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : ProvOutX (fxyPowGraph p).pack) (hQ : o.Q.g.Normal)
    (herr : ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 → (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ →
      Ψ ≤ (W : ℝ) ^ (-(ε₁ / 2)) → o.Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-Deng)) :
    sz.Prec (U := V) (fun n v ω => ‖pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
        (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2) := by
  have S := H.S
  have h𝔠 : 0 < 𝔠 := S.flow.1.1
  have hε₁ := S.assm.1
  have hsz := lwMoment_size_tendsto S
  set Φ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t with hΦ
  apply lwMoment_prec_of_whp
  intro τ hτ
  refine ⟨_, lwMoment_entry_whp S (τ₁ := 𝔠 * ε₁ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  filter_upwards [hdec, lwMoment_Psi_facts S (τ₁ := 𝔠 * ε₁ / 4) (by positivity) le_rfl, lwMoment_Wneg_le S hD0.le hDe,
    lwMoment_L_le_W S hK0, hsz.eventually_ge_atTop 1, hsz.eventually_ge_atTop (o.Q.g.sizeConst C (C * expC (d - 2) c))]
    with n hdn hPsi hWn hLW hN1 hNc
  intro ω hω v
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
      max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * Φ n 0 := by positivity
    nlinarith [le_max_left 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2))]
  have h1 := lwMomentExp_pval_claim S hC hc hdn hA o.Q hQ (pr n v).1 (pr n v).2
    (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) (lwMomentExp_wt_abs sz n _ o)
  have h2 := herr (sz.W n) (sz.L n) _ (sz.W_pos n) (by have := sz.three_le_L n; omega) hLW hwin hup
  have hK0' : 0 ≤ o.Q.g.sizeConst C (C * expC (d - 2) c) :=
    o.Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have hRg := lwMomentExp_R_ge (sz := sz) (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 (lwMomentExp_t1 S n).le
  have hR0 : 0 ≤ lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  calc _ ≤ _ := (h1.trans (mul_le_mul_of_nonneg_left h2 hK0')).trans (hWn _ hNc)
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := lwMomentExp_floor_le hd n hD0.le
    _ ≤ _ := hRg
    _ ≤ _ := le_mul_of_one_le_left hR0 (Real.one_le_rpow hN1 hτ.le)
/-- **outputs with `𝓜_x = 𝓜_y` at far pairs** (twin of `lwMoment_prec_scale`, `LWMoment.lean:925`, radius `r = Krad (log W)^{3/2}`, `lwTail32`) -/
private theorem lwMomentExp_prec_scale (H : lwMomentExp_Ctx d κ ε 𝔡 𝔠 sz z t ε₀ ε₁ Ψ ℓ) (hd : d ≠ 0) {p : ℕ} {D Krad : ℝ} (hD0 : 0 < D)
    (hKr : 0 < Krad) {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : ProvOutX (fxyPowGraph p).pack) (hQ : o.Q.g.Normal)
    (hmol : o.Q.g.molOf (Sum.inl (o.Q.ext 0)) = o.Q.g.molOf (Sum.inl (o.Q.ext 1)))
    (hfar : ∀ n (v : V n), (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (Krad * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) <
      (lwBdist d (sz.L n) (sz.W n) (pr n v).1 (pr n v).2 : ℝ)) :
    sz.Prec (U := V) (fun n v ω => ‖pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
        (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2) := by
  classical
  have S := H.S
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  have hε₁ := S.assm.1
  set Φ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t with hΦ
  apply lwMoment_prec_of_whp
  intro τ hτ
  refine ⟨_, lwMoment_entry_whp S (τ₁ := 𝔠 * ε₁ / 4) (by positivity), ?_⟩
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  filter_upwards [hdec, lwMoment_Psi_facts S (τ₁ := 𝔠 * ε₁ / 4) (by positivity) le_rfl,
    lwTail32 sz h𝔠 (mul_pos hc hKr) hsz hband ((o.Q.g.nM + o.Q.g.nV + 1 : ℕ) : ℝ) D, hsz.eventually_ge_atTop 1,
    hsz.eventually_ge_atTop (o.Q.g.sizeConst C (C * expC (d - 2) (c / 2)))] with n hdn hPsi htail hN1 hNc
  intro ω hω v
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤
      max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * Φ n 0 := by
    intro a b
    refine (hω (a, b)).trans ?_
    have h1 : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) := Real.one_le_rpow hN1 (by positivity)
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * Φ n 0 := by positivity
    nlinarith [le_max_left 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2))]
  have hRg := lwMomentExp_R_ge (sz := sz) (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 (lwMomentExp_t1 S n).le
  have hR0 : 0 ≤ lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 := (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  refine le_trans ?_ (le_mul_of_one_le_left hR0 (Real.one_le_rpow hN1 hτ.le))
  by_cases hf : ∃ ℓ' : o.Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ o.Q.ext
  · obtain ⟨ℓ', hℓ'⟩ := hf
    rw [lwProv_pvalW_of_factor _ _ _ hℓ']
    have hr0 : 0 ≤ Krad * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
      mul_nonneg hKr.le (Real.rpow_nonneg (Real.log_nonneg hW1) _)
    obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
    have hsc := lwMomentExp_scalemole S.hd o.Q.g hQ (lwMoment_D sz n (STflowE z n) (t n) ω) (m := mE (STflowE z n))
      (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply]) hG hGd hC.le hc hdn.1 hdn.2 hr0 ℓ'
      (o.Q.ext 0) (o.Q.ext 1) hmol
      (by rw [show ℓ' (o.Q.ext 0) = (pr n v).1 from (congrFun hℓ' 0).symm, show ℓ' (o.Q.ext 1) = (pr n v).2 from (congrFun hℓ' 1).symm]
          exact hfar n v)
      (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) (lwMomentExp_wt_abs sz n _ o)
    have hM1 : 1 ≤ max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) := le_max_left _ _
    have hΨ0 : 0 < max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 4) * Φ n 0 := by
      have : 0 < max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) := lt_of_lt_of_le one_pos hM1
      positivity
    rw [mul_assoc] at htail
    exact hsc.trans ((lwMoment_tail_le o.Q.g (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega) hΨ0
      (hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))) hNc
      (o.Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) (half_pos hc); positivity)) htail).trans
      ((lwMomentExp_floor_le hd n hD0.le).trans hRg))
  · rw [lwProv_pvalW_of_not _ _ _ hf, norm_zero]; exact hR0
/-- the roots from the coverage (`Cover`): every internal molecule contains the image of some `β^{(k)}`, an internal vertex carrying the weight -/
private theorem lwMomentExp_rep {p : ℕ} (o : ProvOutX (fxyPowGraph p).pack) (hcov : o.Cover p) (n : ℕ) (Dm : Finset (Zd d (sz.L n))) :
    ∃ rep : LGraph.AuxIMol o.Q.g → o.Q.I', (∀ c, o.Q.g.molOf (Sum.inr (rep c)) = c.1) ∧
      ∀ ℓ : o.Q.E' ⊕ o.Q.I' → Idx d (sz.L n) (sz.W n), lwMomentExp_wt sz n Dm o ℓ ≠ 0 →
        ∀ c, (split d (sz.L n) (sz.W n) (ℓ (Sum.inr (rep c)))).1 ∈ Dm := by
  have hex : ∀ c : LGraph.AuxIMol o.Q.g, ∃ (i : o.Q.I') (k : Fin p), o.π (Sum.inr (localReg_fxyBeta k)) = Sum.inr i ∧
      o.Q.g.molOf (Sum.inr i) = c.1 := by
    rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hcov c hc
    rcases hπ : o.π (Sum.inr (localReg_fxyBeta k)) with a | i
    · exact absurd ⟨a, by simpa [hπ] using hk⟩ hc
    · exact ⟨i, k, hπ, by simpa [hπ] using hk⟩
  choose rep k hk hrep using hex
  refine ⟨rep, hrep, fun ℓ hℓ c => ?_⟩
  have h := Finset.prod_ne_zero_iff.1 hℓ (k c) (Finset.mem_univ _)
  rw [hk c] at h
  by_contra hn
  exact h (if_neg hn)
theorem lwMomentExp_eta_le {E t : ℝ} (hE : |E| < 2) (ht : t < 1) : etaT E t ≤ 1 - t := by
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  unfold etaT
  nlinarith
theorem lwMomentExp_logW (sz : Sizes d) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (M0 : ℝ) :
    ∀ᶠ n in atTop, M0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := by
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp M0)] with n hb hbig
  exact (Real.le_log_iff_exp_le (by exact_mod_cast sz.W_pos n)).2 (hbig.trans hb)
set_option maxHeartbeats 3200000 in
/-- **the outputs with `𝓜_x ≠ 𝓜_y`** (twin of `lwMoment_prec_anp`, `LWMoment.lean:1034`): rooted `GtoAG`, nested form, the pin, the floor `W^{-D'}` of `ξ ≺ 𝖳 + W^{-D'}`; radius `R = K (log W)^{3/2}`, `r = (K/Kc) (log W)^{3/2}` -/
private theorem lwMomentExp_prec_anp (H : lwMomentExp_Ctx d κ ε 𝔡 𝔠 sz z t ε₀ ε₁ Ψ ℓ) (hd : d ≠ 0) {p : ℕ} (hp : 0 < p) {K Kc D : ℝ} (hK : 0 < K)
    (hKc : 0 < Kc) (hD0 : 0 < D) {V : ℕ → Type} (pr : ∀ n, V n → Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L)) (o : ProvOutX (fxyPowGraph p).pack)
    (hPin : ∀ Γ : NGraph p o.Q.g.nM, Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → lwMomentExp_PinN d Γ dom)
    (hQ : o.Q.g.Normal) (h345 : o.Q.LocReg345 p) (hxy : o.Q.g.molOf (Sum.inl (o.Q.ext 0)) ≠ o.Q.g.molOf (Sum.inl (o.Q.ext 1)))
    (hnM : o.Q.g.nM ≤ p) (hord : (2 * p : ℤ) ≤ o.Q.g.scalingOrder) (hcard : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kc)
    (hcov : o.Cover p) (hreg1 : ∀ n (v : V n), sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n)
    (hreg2 : ∀ n (v : V n), K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) <
      (zdistInf d (sz.L n) (STblk sz n (pr n v).1 - STblk sz n (pr n v).2) : ℝ))
    (hreg3 : ∀ n (v : V n), K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) < ℓ n) :
    sz.Prec (U := V) (fun n v ω => ‖pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
        (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖)
      (fun n v _ => lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2) := by
  classical
  have S := H.S
  obtain ⟨h𝔠, -, hsz, hband, -⟩ := (lwMoment_flow_facts S).1
  have hε₁ := S.assm.1
  set Φ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t with hΦ
  obtain ⟨Γa, hnog, hnest, hown, hordN, hval⟩ := lwAuxNestedOwnOn_holds p o.Q hp h345 hxy
  obtain ⟨Caux, hCaux, hPinH⟩ := hPin Γa hnog hnest hown
  have hAe : (((o.Q.g.scalingOrder - LGraph.auxOrd o.Q.g).toNat : ℕ) : ℤ) = o.Q.g.scalingOrder - LGraph.auxOrd o.Q.g :=
    Int.toNat_of_nonneg (sub_nonneg.2 (o.Q.g.auxOrd_le_scalingOrder hQ))
  set e1 : ℕ := (o.Q.g.scalingOrder - LGraph.auxOrd o.Q.g).toNat with he1
  set nE : ℕ := Γa.es.length with hnE
  set A : ℕ := e1 + 2 * nE + o.Q.g.nM + 1 with hAdef
  set aN : ℕ := 2 * o.Q.g.nM + 2 * nE with haN
  set D' : ℝ := (D + aN + 1 + 1) / 𝔠 with hD'def
  have hD'0 : 0 < D' := by positivity
  set Rr : ℕ → ℝ := fun n => K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) with hRr
  have hlog : ∀ n, 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := fun n => Real.log_nonneg (Nat.one_le_cast.2 (sz.W_pos n))
  have hRr0 : ∀ n, 0 ≤ Rr n := fun n => mul_nonneg hK.le (Real.rpow_nonneg (hlog n) _)
  have hxi := lwXiExpClaim_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ Ψ ℓ H.hAss ε₀ H.hAss.1 H.hAss.2.2.1.1 D' hD'0
    (fun n => 2 * Rr n + 1) (fun n => by have := hRr0 n; linarith)
    (fun τ hτ => by filter_upwards [lwMomentExp_rad sz hd h𝔠 hsz hband hK τ hτ] with n hn; exact hn)
  have hE2 := lwGbyXi_holds d S.hd κ ε 𝔡 S.hκ S.hε S.h𝔡 𝔠 sz z S.flow t S.t0 S.t1 ε₀ H.hAss.1 H.hAss.2.2.1.1
    (fun n => 2 * Rr n + 1) Rr hRr0 (fun n => le_rfl)
  apply lwMoment_prec_of_whp
  intro τ hτ
  set τ₁ : ℝ := min (min (τ / (2 * A)) (𝔠 * ε₁ / 4)) 1 with hτ₁def
  have hτ₁ : 0 < τ₁ := lt_min (lt_min (by positivity) (by positivity)) one_pos
  refine ⟨_, HighProbAt.inter (tendsto_size sz hsz) (lwMoment_entry_whp S hτ₁)
    (HighProbAt.inter (tendsto_size sz hsz) (Sizes.Prec.whp sz hE2 hτ₁)
      (HighProbAt.inter (tendsto_size sz hsz) (Sizes.Prec.whp sz hxi.2.1 hτ₁) (Sizes.Prec.whp sz hxi.2.2 hτ₁))), ?_⟩
  obtain ⟨C, c, hC, hc, hdec⟩ := lwMoment_decay S
  set K1 : ℝ := o.Q.g.sizeConst C (C * expC (d - 2) c) with hK1
  set K2 : ℝ := o.Q.g.sizeConst C (C * expC (d - 2) (c / 2)) with hK2
  set M : ℝ := max 1 (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) with hM
  set Kbig : ℝ := K1 * M ^ e1 * Caux with hKbig
  have hK10 : 0 ≤ K1 := o.Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) hc; positivity)
  have hK20 : 0 ≤ K2 := o.Q.g.sizeConst_nonneg hC.le (by have := lwMoment_expC_nonneg (d - 2) (half_pos hc); positivity)
  have hM1 : 1 ≤ M := le_max_left _ _
  filter_upwards [hdec, lwMoment_Psi_facts S hτ₁.le ((min_le_left _ _).trans (min_le_right _ _)),
    lwTail32 sz h𝔠 (mul_pos hc (div_pos hK hKc)) hsz hband ((o.Q.g.nM + o.Q.g.nV + 1 : ℕ) : ℝ) D,
    hsz.eventually_ge_atTop 1, hsz.eventually_ge_atTop K2, hsz.eventually_ge_atTop (K1 * 2 ^ nE),
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsz).eventually_ge_atTop (Kbig + 2),
    lwXiRad_holds sz hsz 1 0 20 zero_le_one le_rfl (by norm_num) τ₁ hτ₁, lwMomentExp_logW sz h𝔠 hsz hband (max 1 (1 / K)),
    lwMoment_Wneg_le S (Kf := D + aN + 1) (by positivity) le_rfl, S.flow.1.2.2.2.2]
    with n hdn hPsi htail hN1 hNc hNc1 hNb hrad hlw hWn hWO
  intro ω hω v
  obtain ⟨h1, h2, h3, h4⟩ := hω
  obtain ⟨hΦ0, hwin, hup⟩ := hPsi
  obtain ⟨hlg1, hlgK⟩ : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) ∧ 1 / K ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    ⟨(le_max_left _ _).trans hlw, (le_max_right _ _).trans hlw⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set Wn : ℝ := ((sz.W n : ℕ) : ℝ) with hWn'
  set X : ℝ := N ^ τ₁ with hX
  have hN0 : 0 < N := by linarith
  have hX1 : 1 ≤ X := Real.one_le_rpow hN1 hτ₁.le
  have hX0 : 0 < X := by linarith
  have hXN : X ≤ N := by
    calc X ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right _ _)
      _ = N := Real.rpow_one N
  have hW1 : (1 : ℝ) ≤ Wn := Nat.one_le_cast.2 (sz.W_pos n)
  have hW0 : 0 < Wn := by linarith
  have hWd : Wn ^ d ≤ N := by
    have : (sz.W n) ^ d ≤ sz.size n := by
      unfold Sizes.size
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    rw [hN, hWn']; exact_mod_cast this
  have hEn : |STflowE z n| < 2 := by linarith [(lwMoment_flow_facts S).2.1 n, S.hκ]
  have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos hEn (lwMomentExp_t1 S n)
  have hηt := lwMomentExp_eta_le hEn (lwMomentExp_t1 S n)
  have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwMoment_etaT_le_one hEn (S.t0 n) (lwMomentExp_t1 S n)
  have hΨ0 : 0 < M * X * Φ n 0 := by positivity
  have hΨ1 : M * X * Φ n 0 ≤ 1 := hup.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  have hMX : 1 ≤ M * X := by nlinarith
  have hf0 : Φ n 0 ≤ 1 := le_trans (by simpa using mul_le_mul_of_nonneg_right hMX hΦ0.le) hΨ1
  have hRg := lwMomentExp_R_ge (sz := sz) (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 (lwMomentExp_t1 S n).le
  have hR0 : 0 ≤ lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 :=
    (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hRg
  have hND : N ^ (-D) ≤ lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 :=
    (lwMomentExp_floor_le hd n hD0.le).trans hRg
  have hXA : X ^ A ≤ N ^ (τ / 2) := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow_of_exponent_le hN1 ?_
    have hA0 : (0 : ℝ) < A := by positivity
    calc τ₁ * (A : ℝ) ≤ τ / (2 * A) * A :=
          mul_le_mul_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) hA0.le
      _ = τ / 2 := by field_simp
  have hfin : X ^ A * Kbig + 2 ≤ N ^ τ := by
    have hh : N ^ (τ / 2) * N ^ (τ / 2) = N ^ τ := by rw [← Real.rpow_add hN0]; congr 1; ring
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    have h1' : 1 ≤ N ^ (τ / 2) := Real.one_le_rpow hN1 (half_pos hτ).le
    calc X ^ A * Kbig + 2 ≤ N ^ (τ / 2) * Kbig + N ^ (τ / 2) * 2 :=
          add_le_add (mul_le_mul_of_nonneg_right hXA hKb) (by linarith)
      _ = N ^ (τ / 2) * (Kbig + 2) := by ring
      _ ≤ N ^ (τ / 2) * N ^ (τ / 2) := mul_le_mul_of_nonneg_left hNb (by positivity)
      _ = _ := hh
  suffices hmain : ‖pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
      (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n)) o) ![(pr n v).1, (pr n v).2]‖ ≤
      (X ^ A * Kbig + 2) * lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 from
    hmain.trans (mul_le_mul_of_nonneg_right hfin hR0)
  by_cases hf : ∃ ℓ' : o.Q.E' → Idx d (sz.L n) (sz.W n), ![(pr n v).1, (pr n v).2] = ℓ' ∘ o.Q.ext
  swap
  · rw [lwProv_pvalW_of_not _ _ _ hf, norm_zero]
    exact mul_nonneg (by have : 0 ≤ Kbig := by rw [hKbig]; positivity
                         positivity) hR0
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [lwProv_pvalW_of_factor _ _ _ hℓ']
  have e0 : ℓ' (o.Q.ext 0) = (pr n v).1 := (congrFun hℓ' 0).symm
  have e1' : ℓ' (o.Q.ext 1) = (pr n v).2 := (congrFun hℓ' 1).symm
  set Dmv := dom (sz.L n) (STblk sz n (pr n v).1) (STblk sz n (pr n v).2) (ℓ n) with hDmv
  obtain ⟨rep, hrep, hWt0⟩ := lwMomentExp_rep o hcov n Dmv
  have hA : ∀ a b : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω a b‖ ≤ M * X * Φ n 0 := fun a b =>
    (h1 (a, b)).trans (by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ X) hΦ0.le])
  obtain ⟨hG, hGd⟩ := lwMoment_entries (E := STflowE z n) (t := t n) hA
  set L32 : ℝ := Real.log Wn ^ (3 / 2 : ℝ) with hL32
  have hr0 : 0 ≤ K / Kc * L32 := mul_nonneg (div_nonneg hK.le hKc.le) (Real.rpow_nonneg (hlog n) _)
  have hRr' : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (K / Kc * L32) ≤ Rr n :=
    (mul_le_mul_of_nonneg_right hcard hr0).trans (le_of_eq (by have := hKc.ne'; simp only [hRr, hL32]; field_simp; try rfl))
  set ξ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => lwXiVar sz (STflowE z) t (fun n => 2 * Rr n + 1) n a b ω with hξ
  obtain ⟨hξ0, hξG⟩ := lwGbyXi_hxi sz (STflowE z) t (fun n => 2 * Rr n + 1) Rr n (Matrix.diagonal fun _ => mE (STflowE z n))
    (lwS sz n 1) (lwSplus sz n (t n) (mE (STflowE z n))) ω hX0.le (fun a b a' b' hab h1' h2' => h2 ⟨((a, b), (a', b')), hab, h1', h2'⟩)
  have hgt := lwGtoAGRooted_holds d S.hd (sz.L n) (sz.W n) o.Q.g hQ (lwMoment_ext_mol hxy) rep hrep
    (lwMoment_D sz n (STflowE z n) (t n) ω) (mE (STflowE z n)) (M * X * Φ n 0) C c (K / Kc * L32) (Rr n)
    (fun a b => X * ξ a b) Dmv (fun a b => by simp [lwMoment_D, lwSampleData, Matrix.diagonal_apply]) hG hGd hC.le hc hdn.1 hdn.2
    hwin hr0 hRr' hξ0 hξG (lwMomentExp_wt sz n Dmv o) (lwMomentExp_wt_abs sz n Dmv o) hWt0 ℓ'
  have htl := lwMoment_tail_le o.Q.g (sz.W n) (sz.L n) d (sz.W_pos n) (by have := sz.three_le_L n; omega) hΨ0 hΨ1 hNc hK20
    (by rw [mul_assoc] at htail; exact htail)
  -- the auxiliary graph: `Γ^aux_{Dm}(X ξ) = X^{2 nE} Γa.valOn ζ`, floor, pin
  set aa := STblk sz n (pr n v).1 with haa
  set bb := STblk sz n (pr n v).2 with hbb
  set ζ : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => ξ a b / X with hζ
  set T : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => sfT d (sz.L n) Wn (sz.lam n) (t n)
    (min ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) (ℓ n)) with hT
  set ζ' : Zd d (sz.L n) → Zd d (sz.L n) → ℝ := fun a b => min (ζ a b) (T a b) with hζ'
  set S0 := Fintype.piFinset fun _ : Fin o.Q.g.nM => Dmv with hS0
  set δ0 : ℝ := Wn ^ (-D') with hδ0
  have hξs : ∀ a b, ξ a b = ξ b a := fun a b => lwXiVar_symm sz (STflowE z) t _ n a b ω
  have hPsiT : PsiT d (sz.L n) Wn (sz.lam n) (t n) = Φ n 0 := by
    rw [hΦ, lwMomentExp_phi_zero]; unfold PsiT Sizes.Bctl; rw [Real.sqrt_eq_rpow]
  have hT1 : ∀ a b, T a b ≤ 1 := fun a b =>
    ((sfT_antitone (le_refl 0) (le_min (Nat.cast_nonneg _) (H.hAss.2.2.2.1 n))).trans
      ((sfT_zero_le_PsiT hW0).trans (hPsiT ▸ hf0)))
  have hζ0 : ∀ a b, 0 ≤ ζ a b := fun a b => div_nonneg (lwXiVar_nonneg sz (STflowE z) t _ n a b ω) hX0.le
  have hζle : ∀ a b, ζ a b ≤ T a b + δ0 := fun a b => by
    rw [hζ, div_le_iff₀ hX0]; have := h3 ⟨(a, b), hreg1 n v⟩; simp only [mul_comm] at this ⊢; exact this
  have hζ'0 : ∀ a b, 0 ≤ ζ' a b := fun a b => le_min (hζ0 a b) (sfT_nonneg _)
  have hζ'1 : ∀ a b, ζ' a b ≤ 1 := fun a b => (min_le_right _ _).trans (hT1 a b)
  have hζ'le : ∀ a b, ζ a b ≤ ζ' a b + δ0 := fun a b => by
    by_cases h : ζ a b ≤ T a b
    · change ζ a b ≤ min (ζ a b) (T a b) + δ0
      rw [min_eq_left h]; have : 0 ≤ δ0 := Real.rpow_nonneg hW0.le _; linarith
    · change ζ a b ≤ min (ζ a b) (T a b) + δ0
      rw [min_eq_right (not_le.1 h).le]; exact hζle a b
  have hTs : ∀ a b, T a b = T b a := fun a b => by simp only [hT]; rw [anpKey_zdistInf_sub_comm]
  have hrow : ∀ α, ∑ β, ζ' α β ^ 2 ≤ ((Wn ^ d) * etaT (STflowE z n) (t n))⁻¹ := fun α => by
    have hθ : 0 ≤ ((Wn ^ d) * etaT (STflowE z n) (t n))⁻¹ := by positivity
    calc ∑ β, ζ' α β ^ 2 ≤ ∑ β, (ξ α β / X) ^ 2 := Finset.sum_le_sum fun β _ => pow_le_pow_left₀ (hζ'0 _ _) (min_le_left _ _) 2
      _ = (∑ β, ξ α β ^ 2) / X ^ 2 := by simp [div_pow, Finset.sum_div]
      _ ≤ (X * ((Wn ^ d) * etaT (STflowE z n) (t n))⁻¹) / X ^ 2 := by gcongr; exact h4 α
      _ ≤ _ := by rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg hθ (mul_nonneg hX0.le (sub_nonneg.2 hX1))]
  have hΛ : 1 ≤ Real.log Wn ^ 10 := one_le_pow₀ hlg1
  have hΛX : (Real.log Wn ^ 10) ^ 2 ≤ X := by
    have : (Real.log Wn ^ 10) ^ 2 = Real.log Wn ^ (20 : ℝ) := by rw [← pow_mul, ← Real.rpow_natCast]; norm_num
    rw [this]; have := hrad; linarith
  have hℓ1 : 1 ≤ ℓ n := by
    have h1' := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := t n) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h2' : 1 ≤ K * L32 := by
      have := Real.self_le_rpow_of_one_le hlg1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
      have := (div_le_iff₀ hK).1 hlgK
      nlinarith
    nlinarith [hreg3 n v]
  have hgt' : sz.lam n ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ 2 * (1 - t n) := by
    have := hreg1 n v
    rw [div_lt_iff₀ (by have := sz.three_le_L n; positivity)] at this; linarith
  have hpin := hPinH (sz.L n) Wn (sz.lam n) (t n) (etaT (STflowE z n) (t n)) (ℓ n) (Real.log Wn ^ 10) X hW0
    ((Real.rpow_nonneg hW0.le _).trans hWO.1) (lwMomentExp_t1 S n) hgt' hη0 hηt hℓ1 (H.hAss.2.2.2.2.1 n) hΛ hΛX ζ'
    (fun a b => ⟨hζ'0 a b, by simp only [hζ', hζ, hξs a b, hTs a b]⟩) (fun a b => min_le_right _ _) hrow aa bb
  have hval' := hval (κ := Zd d (sz.L n)) (fun a b => X * ξ a b) (fun u v => by rw [hξs u v])
    (fun a => (split d (sz.L n) (sz.W n) (ℓ' a)).1) Dmv
  rw [show (split d (sz.L n) (sz.W n) (ℓ' (o.Q.ext 0))).1 = aa by rw [e0]; rfl,
    show (split d (sz.L n) (sz.W n) (ℓ' (o.Q.ext 1))).1 = bb by rw [e1']; rfl] at hval'
  have hξζ : Γa.valOn (fun a b => X * ξ a b) (fun _ => aa) (fun _ => bb) S0 =
      X ^ nE * (X ^ nE * Γa.valOn ζ (fun _ => aa) (fun _ => bb) S0) := by
    rw [lwMomentExp_valOn_smul Γa hnog ξ X]
    congr 1
    have := lwMomentExp_valOn_smul Γa hnog ζ X (fun _ => aa) (fun _ => bb) S0
    simp only [hζ, mul_div_cancel₀ _ hX0.ne'] at this
    exact this
  have hδ0 : 0 ≤ δ0 := Real.rpow_nonneg hW0.le _
  have hfl := lwMomentExp_valOn_floor Γa ζ ζ' δ0 hδ0 (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)) hζ0 hζ'0 hζ'1 hζ'le
    (fun _ => aa) (fun _ => bb) S0
  have hΨe : 0 ≤ K1 * (M * X * Φ n 0) ^ e1 := by positivity
  have hWq : 0 ≤ (Wn ^ d) ^ o.Q.g.nM := by positivity
  rw [← hAe, zpow_natCast, ← hval'] at hgt
  rw [hξζ] at hgt
  have hfirst : K1 * (M * X * Φ n 0) ^ e1 * (X ^ (nE + nE) * (X ^ o.Q.g.nM * Caux * (etaT (STflowE z n) (t n))⁻¹ ^ o.Q.g.nM *
      Φ n 0 ^ (Γa.ordN - (p : ℤ)) * T aa bb ^ p)) ≤ X ^ A * Kbig * lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 := by
    have := lwMomentExp_arith (X := X) (M := M) (f0 := Φ n 0) (η := etaT (STflowE z n) (t n)) (C := Caux) (K1 := K1) (T := T aa bb)
      (e1 := e1) (k := nE) (len := nE) (q := o.Q.g.nM) (p := p) (a := Γa.ordN) (o := o.Q.g.scalingOrder) hX1 hM1 hΦ0 hf0 hη0 hη1
      (sfT_nonneg _) hCaux.le hK10 hnM hord (by rw [hordN]; omega)
    refine this.trans ?_
    have h5 : (etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * T aa bb = (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) Wn (sz.lam n) (t n) (min ((zdistInf d (sz.L n) (aa - bb) : ℕ) : ℝ) (ℓ n)) := by rw [hΦ, lwMomentExp_phi_zero]
    have hKb : 0 ≤ Kbig := by rw [hKbig]; positivity
    have h6 : X ^ (e1 + nE + nE + o.Q.g.nM) ≤ X ^ A := pow_le_pow_right₀ hX1 (by rw [hAdef]; omega)
    have h7 : ((etaT (STflowE z n) (t n))⁻¹ * Φ n 0 * T aa bb) ^ p ≤ lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 := by
      rw [h5]; exact le_add_of_nonneg_right (Real.rpow_nonneg hW0.le _)
    exact mul_le_mul (mul_le_mul_of_nonneg_right h6 hKb) h7
      (pow_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 hη0.le) hΦ0.le) (sfT_nonneg _)) _) (mul_nonneg (pow_nonneg hX0.le _) hKb)
  have hFT : K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0))))) ≤ N ^ (-D) := by
    have hc1 : (S0.card : ℝ) ≤ N ^ o.Q.g.nM := by
      rw [hS0, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have : Dmv.card ≤ sz.size n := (Finset.card_le_univ Dmv).trans (by
        rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]; unfold Sizes.size
        exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d)
      rw [Nat.cast_pow]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.2 this) _
    have h2 := hWn 1 hN1
    rw [one_mul] at h2
    have hd2 : δ0 ≤ N ^ (-(D + aN + 1)) := h2
    have e1' : N ^ (aN : ℝ) * N ^ (-(D + aN + 1)) = N ^ (-D) / N := by
      rw [← Real.rpow_add hN0, eq_div_iff hN0.ne', ← Real.rpow_add_one hN0.ne']; congr 1; ring
    have h8 : (Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0)))) ≤
        2 ^ nE * (N ^ aN * N ^ (-(D + aN + 1))) := by
      calc _ ≤ N ^ o.Q.g.nM * (N ^ nE * (N ^ nE * (N ^ o.Q.g.nM * (2 ^ nE * N ^ (-(D + aN + 1)))))) := by gcongr
        _ = 2 ^ nE * (N ^ aN * N ^ (-(D + aN + 1))) := by rw [haN]; ring
    have hΨ1' : (M * X * Φ n 0) ^ e1 ≤ 1 := pow_le_one₀ hΨ0.le hΨ1
    calc _ ≤ K1 * 1 * (2 ^ nE * (N ^ (aN : ℝ) * N ^ (-(D + aN + 1)))) := by
          rw [Real.rpow_natCast]; gcongr
      _ = K1 * 2 ^ nE * (N ^ (-D) / N) := by rw [e1']; ring
      _ ≤ N * (N ^ (-D) / N) := by gcongr
      _ = N ^ (-D) := by field_simp
  rw [hPsiT] at hpin
  have hmain : K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * Γa.valOn ζ (fun _ => aa) (fun _ => bb) S0))) ≤
      X ^ A * Kbig * lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 + N ^ (-D) := by
    calc _ ≤ K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (Γa.valOn ζ' (fun _ => aa) (fun _ => bb) S0 +
          S0.card * (2 ^ nE * δ0))))) := by gcongr
      _ = K1 * (M * X * Φ n 0) ^ e1 * (X ^ (nE + nE) * ((Wn ^ d) ^ o.Q.g.nM * Γa.valOn ζ' (fun _ => aa) (fun _ => bb) S0)) +
          K1 * (M * X * Φ n 0) ^ e1 * ((Wn ^ d) ^ o.Q.g.nM * (X ^ nE * (X ^ nE * (S0.card * (2 ^ nE * δ0))))) := by ring
      _ ≤ _ := add_le_add ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpin (by positivity)) hΨe).trans hfirst) hFT
  have hfin2 : X ^ A * Kbig * lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 + N ^ (-D) + N ^ (-D) ≤
      (X ^ A * Kbig + 2) * lwMomentExp_R sz (STflowE z) t ℓ p D n (pr n v).1 (pr n v).2 := by nlinarith [hND]
  exact hgt.trans ((add_le_add hmain htl).trans hfin2)
end Out
/-! ## 10. The three pins from the engine with provenance -/
section Pin
/-- `t = 0`: `f^D = 0` (`lwMoment_LWf_zero`, `LWMoment.lean:1241`, with the restriction to `Dm`) -/
theorem lwMomentExp_LWfD_zero {d : ℕ} (sz : Sizes d) {E t : ℝ} (hE : |E| < 2) (ht : t = 0) (n : ℕ) (Dm : Finset (Zd d (sz.L n)))
    (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : LWfD sz n E t ω Dm x y = 0 := by
  subst ht
  unfold LWfD
  refine Finset.sum_eq_zero fun α _ => ?_
  split_ifs
  · rfl
  refine Finset.sum_eq_zero fun β _ => ?_
  split_ifs
  · have : STGM sz n E 0 ω β β = 0 := by simp [STGM, lwExpTerm3_Gt_zero sz n hE]
    rw [this]; simp
  · rfl
/-- **a pin from its normalized deterministic bound**: the engine with provenance, the weighted expansion, the three kinds of outputs, the upgrade `≺ → 𝔼`, the sum over the list; every `K > 0` -/
theorem lwMomentExp_pin_gen {d : ℕ} {K : ℝ} (hK : 0 < K) (dom : ∀ (L : ℕ) [NeZero L], Zd d L → Zd d L → ℝ → Finset (Zd d L))
    (hPin : 3 ≤ d → ∀ {p q : ℕ}, 0 < p → ∀ Γ : NGraph p q, Γ.NoGhost → Γ.IsNested → lwMomExpFar_ownExt Γ → lwMomentExp_PinN d Γ dom) :
    LWMomentExpOn d dom (fun sz n t ℓ q => ¬ regA d K sz n t ℓ q) := by
  classical
  intro hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAss D hD
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  obtain ⟨-, hE, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hd0 : d ≠ 0 := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
    filter_upwards [hsz.eventually_ge_atTop 1] with n hN1 v
    have hX : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
    have hW : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one]
    nlinarith
  have hpe : Even p := even_iff_two_dvd.2 hp2
  obtain ⟨ε₁, hε₁, hassm⟩ := lwMomentExp_assm hd hκ hε h𝔡 sz hflow ht0 htT hAss
  let S : LWMomentCtx sz κ ε 𝔡 𝔠 z t ε₁ ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) Ψ
      (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t) := ⟨hd, hκ, hε, h𝔡, hflow, ht0, htT, hassm⟩
  let H : lwMomentExp_Ctx d κ ε 𝔡 𝔠 sz z t ε₀ ε₁ Ψ ℓ := ⟨S, hAss⟩
  set K0 : ℕ := ⌈1 / 𝔠⌉₊ with hK0def
  have hK0 : 1 / 𝔠 ≤ K0 := Nat.le_ceil _
  obtain ⟨outs, errs, hcovx, Hm⟩ := lw_localregularXP p (ε₁ / 2) (half_pos hε₁) K0 d ((D + 1) / 𝔠)
  set Kn : ℕ := ((outs ++ errs).map fun o => Fintype.card (o.Q.E' ⊕ o.Q.I')).sum with hKn
  set Kc : ℝ := (Kn : ℝ) + 1 with hKc
  have hKc1 : 1 ≤ Kc := by have : (0 : ℝ) ≤ Kn := Nat.cast_nonneg _; linarith
  have hKc0 : 0 < Kc := by linarith
  have hcard : ∀ o ∈ outs ++ errs, (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kc := by
    intro o ho
    have : Fintype.card (o.Q.E' ⊕ o.Q.I') ≤ Kn :=
      List.le_sum_of_mem (List.mem_map_of_mem (f := fun o : ProvOutX (fxyPowGraph p).pack => Fintype.card (o.Q.E' ⊕ o.Q.I')) ho)
    have h2 : (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) ≤ Kn := by exact_mod_cast this
    rw [hKc]; linarith
  obtain ⟨-, hc2, hc3, -, hc5⟩ := (Hm 1 one_ne_zero).1
  let V : ℕ → Type := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
    sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ ¬ regA d K sz n (t n) (ℓ n) q}
  have hper : ∀ o ∈ outs ++ errs, sz.Prec (U := V) (fun n v ω => ‖pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
        (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2]‖)
      (fun n v _ => lwMomentExp_R sz (STflowE z) t ℓ p D n v.1.1 v.1.2) := by
    intro o ho
    have hrm : (o.ev 1).Q ∈ (outs.map (·.ev 1)).map (·.Q) ++ (errs.map (·.ev 1)).map (·.Q) := by
      rcases List.mem_append.1 ho with h | h
      · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem h))
      · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem h))
    have e1 : (o.ev 1).Q = o.Q := lwMoment_evX_one (o.tag, o.Q)
    obtain ⟨-, hQ, -, hnM', -⟩ := hc3 _ hrm
    rw [e1] at hQ hnM'
    have hnM : o.Q.g.nM ≤ p := hnM'.trans_eq (fxyPowGraph_nM p)
    obtain ⟨-, hcov⟩ := hcovx o ho
    rcases List.mem_append.1 ho with h | h
    · have hq : (o.ev 1).Q ∈ (outs.map (·.ev 1)).map (·.Q) := List.mem_map_of_mem (List.mem_map_of_mem h)
      obtain ⟨-, -, h345, h6, -⟩ := hc5 _ hq
      rw [e1] at h345 h6
      by_cases hmol : o.Q.g.molOf (Sum.inl (o.Q.ext 0)) = o.Q.g.molOf (Sum.inl (o.Q.ext 1))
      · have hs := lwMomentExp_prec_scale H hd0 hD (V := V) (Krad := K / Kc) (div_pos hK hKc0) (fun n v => v.1) dom o hQ hmol
        refine hs ?_
        intro n v
        have hreg := not_or.1 v.2.2
        have h1 : (zdistInf d (sz.L n) (STblk sz n v.1.1 - STblk sz n v.1.2) : ℝ) ≤ (lwBdist d (sz.L n) (sz.W n) v.1.1 v.1.2 : ℝ) :=
          by exact_mod_cast zdistInf_le_zdistD d (sz.L n) _
        have hL0 : 0 ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) :=
          mul_nonneg hK.le (Real.rpow_nonneg (Real.log_nonneg (Nat.one_le_cast.2 (sz.W_pos n))) _)
        have hell : (1 : ℝ) ≤ ellT (sz.L n) (sz.lam n) (t n) := one_le_ellT (Nat.one_le_cast.2 (by have := sz.three_le_L n; omega))
        have h2 := not_le.1 hreg.1
        calc (Fintype.card (o.Q.E' ⊕ o.Q.I') : ℝ) * (K / Kc * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ))
            ≤ Kc * (K / Kc * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right (hcard o ho) (by positivity)
          _ = K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) := by field_simp
          _ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) := le_mul_of_one_le_right hL0 hell
          _ < _ := h2.trans_le h1
      · exact lwMomentExp_prec_anp H hd0 hp0 hK hKc0 hD (V := V) (fun n v => v.1) dom o (fun Γ hNG hN hO => hPin hd hp0 Γ hNG hN hO) hQ h345 hmol hnM h6
          (hcard o ho) hcov (fun n v => v.2.1) (fun n v => not_le.1 (not_or.1 v.2.2).1) (fun n v => not_le.1 (not_or.1 v.2.2).2)
    · have hq : (o.ev 1).Q ∈ (errs.map (·.ev 1)).map (·.Q) := List.mem_map_of_mem (List.mem_map_of_mem h)
      have herr := hc2 _ hq
      rw [e1] at herr
      exact lwMomentExp_prec_err H hd0 hD hK0 le_rfl (V := V) (fun n v => v.1) dom o hQ herr
  have hint : ∀ o ∈ outs ++ errs, sz.Prec (U := V) (fun n v _ => ‖∫ ω, pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
        (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2] ∂sz.seqP‖)
      (fun n v _ => lwMomentExp_R sz (STflowE z) t ℓ p D n v.1.1 v.1.2) := by
    intro o ho
    have hrm : (o.ev 1).Q ∈ (outs.map (·.ev 1)).map (·.Q) ++ (errs.map (·.ev 1)).map (·.Q) := by
      rcases List.mem_append.1 ho with h | h
      · exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_map_of_mem h))
      · exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem h))
    have e1 : (o.ev 1).Q = o.Q := lwMoment_evX_one (o.tag, o.Q)
    obtain ⟨-, hQ, -⟩ := hc3 _ hrm
    rw [e1] at hQ
    obtain ⟨envExp, henv⟩ := lwMomentExp_env S o.Q hQ
    exact lwExpTerm_prec_integral sz (V := V) (fun n v ω => pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
      (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2])
      (fun n v => lwMomentExp_R sz (STflowE z) t ℓ p D n v.1.1 v.1.2) (Kenv := envExp) (Kf := D) hsz
      (henv.mono fun n h v ω => h _ _ ω _ (lwMomentExp_wt_abs sz n _ o))
      (Eventually.of_forall fun n v => (lwMomentExp_floor_le hd0 n hD.le).trans
        (lwMomentExp_R_ge (sz := sz) (STflowE z) t ℓ p D n v.1.1 v.1.2 (ht1 n).le))
      (hper o ho)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  let F : ProvOutX (fxyPowGraph p).pack → ∀ n, V n → ℝ := fun o n v => ‖∫ ω, pvalW o.Q (lwMoment_D sz n (STflowE z n) (t n) ω)
    (lwMomentExp_wt sz n (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) o) ![v.1.1, v.1.2] ∂sz.seqP‖
  let G : ∀ n, V n → ℝ := fun n v => lwMomentExp_R sz (STflowE z) t ℓ p D n v.1.1 v.1.2
  have hG : ∀ n v, 0 ≤ G n v := fun n v => (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans
    (lwMomentExp_R_ge (sz := sz) (STflowE z) t ℓ p D n v.1.1 v.1.2 (ht1 n).le)
  have hsum := lwMoment_sum_det sz hsz (V := V) (outs ++ errs) F G hG
    (fun o ho => (st6_prec_det_iff sz hsz (F o) G).1 (hint o ho)) τ hτ
  filter_upwards [hsum] with n hn
  intro v
  have hEn : |STflowE z n| < 2 := by linarith [hE n, hκ]
  by_cases ht0' : t n = 0
  · have hz : ∀ ω : sz.SeqΩ, ‖LWfD sz n (STflowE z n) (t n) ω (dom (sz.L n) (STblk sz n v.1.1) (STblk sz n v.1.2) (ℓ n)) v.1.1 v.1.2‖ ^ p = 0 :=
      fun ω => by rw [lwMomentExp_LWfD_zero sz hEn ht0' n _ ω _ _]; simp [hp0.ne']
    simp only [hz, integral_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hG n v)
  · have ht0'' : 0 < t n := lt_of_le_of_ne (ht0 n) (Ne.symm ht0')
    obtain ⟨-, hw, hXw⟩ := Hm (mE (STflowE z n)) (lwWx_mE_ne _ hEn)
    refine le_trans (lwMomentExp_expand sz hpe n hEn ht0'' (ht1 n) (outs := outs ++ errs) ?_ hXw _ v.1.1 v.1.2) (hn v)
    intro o ho
    exact hw (o.ev (mE (STflowE z n))).Q (List.mem_map_of_mem (List.mem_map_of_mem ho))
end Pin
/-! ## 11. The far and near pins, and the target -/
/-- **the far pin** (`lem:LW_moment_exp_far`, `7_8:1620-1643`) for every `K > 0`: `AnpFarAndAt` (`lwMomExpFar_and`) with the domain `domFar` -/
theorem lwMomentExp_farPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpFarPin d K :=
  lwMomentExp_pin_gen hK (fun L _ a b ℓ => domFar d L a b ℓ)
    (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_far hd hp (lwMomExpFar_and d p q Γ hNG hN hO))
/-- **the near pins** (`lem:LW_moment_exp_near`, `7_8:1648-1660`) for every `K > 0`: `AnpNearInfAt` (`lwMomExp_nearInf`) with the centres `a` and `b` -/
theorem lwMomentExp_nearPin_holds (d : ℕ) {K : ℝ} (hK : 0 < K) : LWMomExpNearPin d K :=
  ⟨lwMomentExp_pin_gen hK (fun L _ a _ ℓ => domNearA d L a ℓ)
      (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_near (lwMomExp_nearInf d hd p q Γ hNG hN) _ (fun L _ a _ => a)
        (fun L _ a b ℓ α hα => (Finset.mem_filter.1 hα).2)),
    lwMomentExp_pin_gen hK (fun L _ a b ℓ => domNearB d L a b ℓ)
      (fun hd p q hp Γ hNG hN hO => lwMomentExp_pinN_near (lwMomExp_nearInf d hd p q Γ hNG hN) _ (fun L _ _ b => b)
        (fun L _ a b ℓ α hα => (Finset.mem_filter.1 hα).2.2))⟩
end RBM.Graph
namespace RBM.Gauss.Sizes
/-- **`lem:LW_moment_exp`** (`7_8:78-83`): the target `LWMomentExp d` for every `d` (assembly at `K = 1`: (A) for `regA 1`, the far pin and the near pins on `¬ regA 1`) -/
theorem lwMomentExp_holds : ∀ d : ℕ, LWMomentExp d := fun d =>
  RBM.Graph.lwMomentExp_of_parts d 1 one_pos (RBM.Graph.lwMomExpNoExp_holds d 1 one_pos) (RBM.Graph.lwMomentExp_farPin_holds d one_pos)
    (RBM.Graph.lwMomentExp_nearPin_holds d one_pos)
end RBM.Gauss.Sizes
namespace RBM.Graph
/-! ## 12. Compiled nonempty instances at `d = 3`
The merged preflight data (`sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `λ_n = (2(n+1))^{-6}`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `z0`, `flow_z0`; `t ≡ 1/16`; `ε₀ = 1/20`,
`Ψ0 = W^{-1}`, `ℓ_n = ℓ_t`, `LWAssmExp` from `assmExp_of`), `p = 2`.  What stays a hypothesis is another gate's stochastic input: `LWInit` and `LWLoopExp`. -/
section Instances
open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst
/-- the index set of the three pins at `K = 1/100` is nonempty at `n = 0` (`x = 0`, `y = (32, 32, 32)`: block distance `1`, `K (log W)^{3/2} ℓ_t ≤ 0.64`) -/
theorem lwMomentExp_inst_nonempty :
    Nonempty {q : Idx 3 (sz0.L 0) (sz0.W 0) × Idx 3 (sz0.L 0) (sz0.W 0) //
      sz0.lam 0 ^ 2 / ((sz0.L 0 : ℕ) : ℝ) ^ 2 < 1 - tInst 0 ∧ ¬ regA 3 (1 / 100) sz0 0 (tInst 0) (ℓT tInst 0) q} := by
  refine ⟨⟨(fun _ => 0, fun _ => 32), strict_all 0, ?_⟩⟩
  have hd : zdistInf 3 (sz0.L 0) (STblk sz0 0 (fun _ => 0) - STblk sz0 0 (fun _ => 32)) = 1 := by decide +kernel
  have hW : ((sz0.W 0 : ℕ) : ℝ) = 32 := by rw [sz0_values.2.1]; norm_num
  have hlog : Real.log ((sz0.W 0 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ 16 := by
    rw [hW, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
    have h2 := Real.log_two_lt_d9
    have h0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : ((5 : ℕ) : ℝ) * Real.log 2 ≤ 4 := by push_cast; linarith
    have hl1 : 1 ≤ ((5 : ℕ) : ℝ) * Real.log 2 := by push_cast; linarith [Real.log_two_gt_d9]
    calc (((5 : ℕ) : ℝ) * Real.log 2) ^ (3 / 2 : ℝ) ≤ (((5 : ℕ) : ℝ) * Real.log 2) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num)
      _ ≤ 4 ^ (2 : ℝ) := Real.rpow_le_rpow (by positivity) hl (by norm_num)
      _ = 16 := by norm_num
  have hL1 : (1 : ℝ) ≤ (sz0.L 0 : ℝ) := by rw [sz0_values.1]; norm_num
  have hell1 : 1 ≤ ellT (sz0.L 0) (sz0.lam 0) (tInst 0) := one_le_ellT hL1
  have hell4 : ellT (sz0.L 0) (sz0.lam 0) (tInst 0) ≤ 4 := by
    have := ellT_le_L (L := sz0.L 0) (g := sz0.lam 0) (t := tInst 0)
    refine this.trans (le_of_eq ?_)
    rw [sz0_values.1]; norm_num
  unfold regA ℓT
  push Not
  constructor
  · rw [hd]; push_cast; nlinarith
  · nlinarith
/-- `lwMomentExp_holds 3` at the preflight data (index set nonempty at every `n`): `E |f_{xy}|^2 ≺ (η⁻¹ B_{ctl}^{1/2} 𝖳_t(|a-b|_∞ ∧ ℓ))² + W^{-D}` on `λ²/L² < 1 - t` -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  RBM.Gauss.Sizes.lwMomentExp_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2) (1 / 6) sz0 z0
    flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD
example (n : ℕ) : Nonempty {_q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n} := ⟨⟨(0, 0), strict_all n⟩⟩
/-- the far pin at `K = 1/100` -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  lwMomentExp_farPin_holds 3 (K := 1 / 100) (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2)
    (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD
/-- the near pins at `K = 1/100` (centre `a`, centre `b`) -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  (lwMomentExp_nearPin_holds 3 (K := 1 / 100) (by norm_num)).1 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2)
    (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  (lwMomentExp_nearPin_holds 3 (K := 1 / 100) (by norm_num)).2 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2)
    (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD
/-- the assembly `lwMomentExp_of_parts` at `d = 3`, `K = 1/100`, with the proved (A), far and near pins -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst)) (D : ℝ) (hD : 0 < D) :=
  lwMomentExp_of_parts 3 (1 / 100) (by norm_num) (lwMomExpNoExp_holds 3 (1 / 100) (by norm_num)) (lwMomentExp_farPin_holds 3 (by norm_num))
    (lwMomentExp_nearPin_holds 3 (by norm_num)) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 2 (dvd_refl 2)
    (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) D hD
/-- the three domains at `d = 3`, `L = 4`, `a = 0`, `b = (2,0,0)`, `ℓ = 1` are nonempty and partition `Z_4^3`; `domFar` is the merged far domain; `f = f^> + f^(a) + f^(b)` at `sz0`; the pointwise step of the split -/
example : (domFar 3 4 (0 : Zd 3 4) ![2, 0, 0] 1).Nonempty ∧ (domNearA 3 4 (0 : Zd 3 4) 1).Nonempty ∧ (domNearB 3 4 (0 : Zd 3 4) ![2, 0, 0] 1).Nonempty := by
  refine ⟨⟨![0, 2, 0], ?_⟩, ⟨0, ?_⟩, ⟨![2, 0, 0], ?_⟩⟩ <;> simp only [domFar, domNearA, domNearB, Finset.mem_filter, Finset.mem_univ, true_and]
  · exact ⟨Nat.one_lt_cast.2 (by decide +kernel), Nat.one_lt_cast.2 (by decide +kernel)⟩
  · exact Nat.cast_le_one.2 (by decide +kernel)
  · exact ⟨Nat.one_lt_cast.2 (by decide +kernel), Nat.cast_le_one.2 (by decide +kernel)⟩
example : domFar 3 4 (0 : Zd 3 4) ![2, 0, 0] 1 ∪ domNearA 3 4 0 1 ∪ domNearB 3 4 0 ![2, 0, 0] 1 = Finset.univ := dom_union _ _ _
example := dom_disj (d := 3) (L := 4) 0 ![2, 0, 0] 1
example : lwMomExpFar_farDAnd 3 4 (fun _ : Fin 2 => (0 : Zd 3 4)) (fun _ => ![2, 0, 0]) 1 = domFar 3 4 0 ![2, 0, 0] 1 := domFar_eq (by norm_num) _ _ _
example (ω : sz0.SeqΩ) := LWf_split sz0 0 0 (1 / 2) 1 ω 0 1
example : ‖(1 : ℂ) + 2 + 3‖ ^ 2 ≤ 3 ^ (2 - 1) * (‖(1 : ℂ)‖ ^ 2 + ‖(2 : ℂ)‖ ^ 2 + ‖(3 : ℂ)‖ ^ 2) := norm_add3_pow_le 1 2 3 (by norm_num)
end Instances
end RBM.Graph
end
