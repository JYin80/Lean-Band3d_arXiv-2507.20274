/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QtNonzeroEnd
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQLin
import RBM3D.Induction.ScaleFacts3
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.Step2Events
import RBM3D.Green.Pins

/-!
# The case-(ii) endpoint at the flow, per time (`d ≥ 3`): `stOeqNZPT''_holds`

Ticket T2292 (S3-22b, per-time half; stochastic layer ST-3, case (ii) `1 - s ≤ ilambda^2/L^2`).
Third of the case-(ii) chain S3-21 = `Induction/QtNonzero`, S3-22a = `Induction/QtNonzeroEnd`
(`nzGridEndN`), S3-22b, S3-22c; cut by DECISIONS §96 (3), §97 (1) (supervisor 0956 O5): this file
is the per-time endpoint, the uniform lift `STOeqNZ''` is T2292b. Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `(normQA2)` `:1466`, `lem:STOeq_Qt_nonzero`
`:1561-1572`, proof `:1889-1933` (`(eq:expandQAempty)` `:1893`, `(sahwNQ_smalleta)` `:1903`,
`(sahwNQ2)` `:1910`, `(am;asoiuw_smalleta)` `:1916`, "the same argument applies to each fixed `u`"
`:1931`). Format model: `Induction/NQEndFlow.lean` (T2246, case (i); `nqFlow_core`,
`NQEndFlow.lean:642`) with `nzGridEndN` in place of `nqGridEndLinN`.

## What is here

* §1 the pins `STNZConclPT''` (the merged `STNQConclPT''`, `NQEndFlow.lean:107`, with the index
  set "every `σ`, every `A ⊇ I_diff(σ)`" and the quantity `‖(Q^{(A)}(𝓛-𝒦)^{(n_)})_{u,σ,a}‖`; the
  first summand of `STbootRHS` at `B_s`, R2*, DECISIONS §80) and `STOeqNZPT''` (`STIngR d
  STCaseII`);
* §2 window and setting facts, §3 the levels (private copies of `NQEndFlow.lean:205-211`,
  `:293-583`, `:802-819`; `nqFlowLam`, `nqFlowPhiC` are reused public, never redefined);
* §4 the transfer facts (copies of `NQEndFlow.lean:593-630`) and the `Q^{(A)}` facts (new): the
  bound `(normQA2)` on the projected tensor, measurability of the projected matrix functional, the
  projected initial event `nzFlow_initQ` from `STLK s` at half the exponent;
* §5 the per-section endpoint `nzFlow_core`, `nzFlow_section` (private): `nzGridEndN` on the
  window `[s, v]`, the good events `gridGoodN_holds` (re-instantiated on `[s, v]`) and
  `nqLinGood_holds`, the initial event, the terminal transfer, and the collapsed sections `u_n =
  s_n`, bounded directly by `STLK s` and `(normQA2)`;
* §6 **`stOeqNZPT''_holds`** (paper-delta candidates `T2292a`, `T2292c`, `T2292d`);
* §7 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QtNonzeroFlowInst`).

Every helper that the ticket does not pin is `private` or prefixed `nzFlow_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. The pins (R2*, DECISIONS §80 (1); `STNQConclPT''` with `Q^{(A)}`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- **Per-time case-(ii) projected endpoint, R2*** (`lem:STOeq_Qt_nonzero` `3_5:1561`, the bound
`(am;asoiuw_smalleta)` `3_5:1916-1922` for `Q^{(A)}(𝓛-𝒦)^{(n_)}` at each fixed `u`, `3_5:1931`; DECISIONS §80 (1),
§91 (2); paper-delta candidate `T2292a`): the merged `STNQConclPT''` (`NQEndFlow.lean:107`) with the index set
`{σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)}` replaced by "every `σ`, every `A ⊇ I_diff(σ)`"
(`{σA // STIdiff σA.1 ⊆ σA.2}`) and the quantity `‖Lloop … - STKloop …‖` by
`‖(Q^{(A)}(𝓛-𝒦)^{(n_)})_{u,σ,a}‖ = ‖zeroModeSet d L A (fun b => Lloop … b ω - STKloop … b) a‖`; hypotheses,
the normalisation `/ B_u^{n_}` and the right side `B_u^{1/6} XLK n_ + STbootRHS 2 … B_s n_ p` are unchanged. -/
def STNZConclPT'' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := fun n => TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖zeroModeSet d (sz.L n) q.2.1.1.2
          (fun b : Fin n_ → Zd d (sz.L n) =>
            Lloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n (q.1 : ℝ) +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (s n)) n_ p)

end Pins

/-- The per-time pin in the ingredient shape (case (ii)): the conclusion of `stOeqNZPT''_holds` (T2292); consumed
(after the lift T2292b) by S3-22c. -/
def STOeqNZPT'' (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STNZConclPT'' sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 2. Window and setting facts (private copies of `NQEndFlow.lean:293-331`, `:205-211`) -/

section Window

variable {d : ℕ}

/-- A pointwise larger right side keeps `≺` (the failure event only shrinks; `N^τ ≥ 0`). -/
private theorem nzFlow_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(con_st_ind)` is monotone in the exponent: it forces `B_t < 1` (`B_t^a ≥ 1` if `B_t ≥ 1`, against the
ratio `< 1`), and `B^b ≤ B^a` for `B ≤ 1`, `a ≤ b`. -/
private theorem nzFlow_conStInd_exp_mono (sz : Sizes d) {s t : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (ht1 : ∀ n, t n < 1) (h : sz.STConStInd a s t) : sz.STConStInd b s t := by
  filter_upwards [h] with n hn
  refine ⟨?_, hn.2⟩
  have hBt : 0 < sz.Bctl n (t n) := st_Bctl_pos sz (ht1 n)
  have hlt : sz.Bctl n (t n) < 1 := by
    by_contra hge
    have h1 : (1 : ℝ) ≤ sz.Bctl n (t n) := not_lt.1 hge
    have h2 : (1 : ℝ) ≤ (sz.Bctl n (t n)) ^ a := Real.one_le_rpow h1 ha.le
    linarith [hn.1, hn.2]
  exact (Real.rpow_le_rpow_of_exponent_ge hBt hlt.le hab).trans hn.1

/-- The three parts of `STStep2Concl` restrict from `[s,t]` to `[s,v]`, `v ≤ t` (restriction of the parameter set
along `TimeIcc s v n ⊆ TimeIcc s t n`; the right side of `STGdecayW` depends on `s` and `u` only). -/
private theorem nzFlow_step2_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} {Cd : ℝ} (hvt : ∀ n, v n ≤ t n)
    (h : STStep2Concl sz E s t Cd) : STStep2Concl sz E s v Cd := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) h1
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))
  · exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))) h2
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))
  · intro D hD
    exact StochDomAt.precomp_param
      (V := fun n => TimeIcc s v n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) (h3 D hD)
      (fun n p => (⟨p.1.1, p.1.2.1, p.1.2.2.trans (hvt n)⟩, p.2))

/-- The pair hypotheses `Ξ̂_{w,m} ≺ Z m n u`, `s_n ≤ w ≤ u ≤ t_n`, restricted to the pairs `(w, v_n)`, `w ∈ [s_n, v_n]`
(`v_n ≤ t_n`): the controls become the numbers `Z m n (v n)` (`StochDomAt.precomp_param`). -/
private theorem nzFlow_restrict_pair {sz : Sizes d} {s t v : ℕ → ℝ} (hvt : ∀ n, v n ≤ t n)
    {F : ∀ n, ℝ → sz.SeqΩ → ℝ} {Z : ∀ n, ℝ → ℝ}
    (h : sz.Prec (U := STPair s t) (fun n q ω => F n q.1.1 ω) (fun n q _ => Z n q.1.2)) :
    sz.Prec (U := fun n => TimeIcc s v n) (fun n u ω => F n (u : ℝ) ω) (fun n _ _ => Z n (v n)) :=
  StochDomAt.precomp_param (V := fun n => TimeIcc s v n) h
    (fun n w => (⟨((w : ℝ), v n), w.2.1, w.2.2, hvt n⟩ : STPair s t n))

end Window

/-! ## 3. The levels (private copies of `NQEndFlow.lean:347-583`) -/

section Levels

variable {d : ℕ}

/-- `Ξ̂^{(𝓛)}_{v,k} ≥ 1` (copy of the private `gridGood_one_le_STXiL`, `GridGoodN.lean:655`). -/
private theorem nzFlow_one_le_STXiL (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

/-- **G1, exactly** (R2*): `(XL(2k−1) (XL(4p)/B)^{1/(2p)})^{1/2}` is the first summand of `STbootRHS … B k p`
(`B > 0`, `p ≥ 1`, `XL ≥ 0`): `nqFlowLam` at `B = B_s` has `Λ^{1/2}` equal to it, with no loss. -/
private theorem nzFlow_lam_sqrt {X : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hp : 1 ≤ p) (hB : 0 < B) (hX : ∀ m, 0 ≤ X m) :
    (nqFlowLam X B k p) ^ ((1 : ℝ) / 2) =
      B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) * X (4 * p) ^ (1 / (4 * (p : ℝ))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr : 0 ≤ (X (4 * p) / B) := div_nonneg (hX _) hB.le
  unfold nqFlowLam
  rw [Real.mul_rpow (hX _) (Real.rpow_nonneg hr _), ← Real.rpow_mul hr]
  have hc : 1 / (2 * (p : ℝ)) * ((1 : ℝ) / 2) = 1 / (4 * (p : ℝ)) := by field_simp; norm_num
  rw [hc, Real.div_rpow (hX _) hB.le, show -(1 : ℝ) / (4 * (p : ℝ)) = -(1 / (4 * (p : ℝ))) by ring,
    Real.rpow_neg hB.le]
  have : (1 / 2 : ℝ) = (1 : ℝ) / 2 := by norm_num
  rw [this]
  ring

/-- `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m` for `k ≥ 2`, `XL ≥ 1` (`Φ₃ = (XL(n₁) XL(n₂))^{1/2}`, `(n₁,n₂) = STn12E k ∈
{(k-1,k+1), (k,k)}`: `√(xy) ≤ x + y`). -/
private theorem nzFlow_phi3_le {X : ℕ → ℝ} {k : ℕ} (hk : 2 ≤ k) (hX : ∀ m, 1 ≤ X m) :
    1 + nqLinPhi3 X k ≤ ∑ m ∈ Finset.Icc (k - 1) (k + 1), X m := by
  have e : Finset.Icc (k - 1) (k + 1) = {k - 1, k, k + 1} := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]; omega
  rw [e, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; omega), Finset.sum_singleton]
  have h1 := hX (k - 1)
  have h2 := hX k
  have h3 := hX (k + 1)
  unfold nqLinPhi3 STn12E
  split_ifs with h
  · simp only
    rw [← Real.sqrt_eq_rpow]
    have : Real.sqrt (X (k - 1) * X (k + 1)) ≤ X (k - 1) + X (k + 1) :=
      Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    linarith
  · simp only
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul_self (by linarith)]
    linarith

/-- **The degree-1 inequality** (R2*): the final loss `Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃` with
`Λ_s = max 1 (nqFlowLam X B_s k p)` is at most the right side `B^{1/6} XLK k + STbootRHS 2 X Y B_s k p` of the
pin.  `Φ₁` is the sum of the controls `XLK 2 … XLK (k-1)`, `Φ₂` is the third sum of `STbootRHS` plus
`B^{1/6} XLK k`, `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m` (`nzFlow_phi3_le`), and `(nqFlowLam X B_s k p)^{1/2}` is the first
summand of `STbootRHS` (`nzFlow_lam_sqrt`), so `Λ_s^{1/2} ≤ 1 + ` that summand. -/
private theorem nzFlow_level_le {X Y : ℕ → ℝ} {B Bs : ℝ} {k p : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p)
    (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) (hBs : 0 < Bs) :
    (max 1 (nqFlowLam X Bs k p)) ^ ((1 : ℝ) / 2) + nqLinPhi1 Y k + nqLinPhi2 X Y B k (Y k) +
        nqLinPhi3 X k ≤
      B ^ (1 / 6 : ℝ) * Y k + STbootRHS 2 X Y Bs k p := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hphi3 := nzFlow_phi3_le hk hX
  have hlam := nzFlow_lam_sqrt (k := k) hp hBs hX0
  have hfirst : 0 ≤ Bs ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) *
      X (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hBs.le _) (Real.rpow_nonneg (hX0 _) _))
      (Real.rpow_nonneg (hX0 _) _)
  have hmax : (max 1 (nqFlowLam X Bs k p)) ^ ((1 : ℝ) / 2) ≤
      1 + Bs ^ (-(1 : ℝ) / (4 * (p : ℝ))) * X (2 * k - 1) ^ (1 / 2 : ℝ) *
        X (4 * p) ^ (1 / (4 * (p : ℝ))) := by
    rcases le_total 1 (nqFlowLam X Bs k p) with h | h
    · rw [max_eq_right h, hlam]; linarith
    · rw [max_eq_left h, Real.one_rpow]; linarith
  unfold nqLinPhi1 nqLinPhi2 STbootRHS
  linarith

/-- **`hQ` at the level `Λ_s`** (the shape of the private `gridGood_prec_Q_one`, `GridGoodN.lean:1045`, with the controls
`Xa, Xb` in place of `1` and `B_s` as the floor): `Ξ̂_a (Ξ̂_b/B_u)^r ≺ max 1 (Xa (Xb/B_s)^r)` for `0 ≤ r ≤ 1` from
`Ξ̂_a ≺ Xa`, `Ξ̂_b ≺ Xb` uniformly in `u ∈ [s,v]` (`B_{u,0}` is non-decreasing in `u`, `STBctl_mono`). -/
private theorem nzFlow_hQ (sz : Sizes d) (hsz : sz.SizeTendsto) {E s v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n)
    (hv1 : ∀ n, v n < 1) {a b p : ℕ} (hp : 1 ≤ p) {Xa Xb : ℕ → ℝ} (hXa : ∀ n, 0 ≤ Xa n)
    (hXb : ∀ n, 0 ≤ Xb n)
    (ha : Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω)
      (fun n _ _ => Xa n))
    (hb : Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) b ω)
      (fun n _ _ => Xb n)) :
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) a ω *
        (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))))) := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) ha hb fun τ hτ =>
    ⟨τ / 2, half_pos hτ, Eventually.of_forall fun n => ?_⟩
  intro ω hω
  obtain ⟨u, hu⟩ := hω
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨h1, h2⟩ := hno
  have hu1 : (u : ℝ) < 1 := (u.2.2).trans_lt (hv1 n)
  have hBu : 0 < sz.Bctl n (u : ℝ) := st_Bctl_pos sz hu1
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz ((hsv n).trans_lt (hv1 n))
  have hBsu : sz.Bctl n (s n) ≤ sz.Bctl n (u : ℝ) := STBctl_mono sz n u.2.1 hu1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hXia := h1 u
  have hXib := h2 u
  have hXb0 : 0 ≤ STXiL sz n (E n) (u : ℝ) b ω := zero_le_one.trans (nzFlow_one_le_STXiL sz b ω hBu)
  have hXa0 : 0 ≤ STXiL sz n (E n) (u : ℝ) a ω := zero_le_one.trans (nzFlow_one_le_STXiL sz a ω hBu)
  set Nh : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) with hNh
  have hNh1 : 1 ≤ Nh := Real.one_le_rpow hN1 (half_pos hτ).le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hr0 : 0 ≤ 1 / (2 * (p : ℝ)) := by positivity
  have hr1 : 1 / (2 * (p : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have e1 : (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Nh * Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_le_rpow (div_nonneg hXb0 hBu.le) (div_le_div_of_nonneg_right hXib hBu.le) hr0
  have e2 : (Nh * Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) =
      Nh ^ (1 / (2 * (p : ℝ))) * (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) := by
    rw [mul_div_assoc, Real.mul_rpow (by linarith) (div_nonneg (hXb n) hBu.le)]
  have e3 : (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_le_rpow (div_nonneg (hXb n) hBu.le) (div_le_div_of_nonneg_left (hXb n) hBs hBsu) hr0
  have e4 : Nh ^ (1 / (2 * (p : ℝ))) ≤ Nh :=
    (Real.rpow_le_rpow_of_exponent_le hNh1 hr1).trans_eq (Real.rpow_one _)
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ = Nh * Nh := by
    rw [hNh]; exact (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
  have hM : 0 ≤ (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
    Real.rpow_nonneg (div_nonneg (hXb n) hBs.le) _
  have hlam : Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) ≤
      max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := le_max_right _ _
  have hlam0 : 0 ≤ Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) := mul_nonneg (hXa n) hM
  have hmax0 : 0 ≤ max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) :=
    zero_le_one.trans (le_max_left _ _)
  have hstep : STXiL sz n (E n) (u : ℝ) a ω *
      (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) ≤
      (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by
    refine mul_le_mul hXia ?_ (Real.rpow_nonneg (div_nonneg hXb0 hBu.le) _)
      (mul_nonneg (by linarith) (hXa n))
    calc (STXiL sz n (E n) (u : ℝ) b ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ)))
        ≤ Nh ^ (1 / (2 * (p : ℝ))) * (Xb n / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))) :=
          e1.trans e2.le
      _ ≤ Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ))) :=
          mul_le_mul e4 e3 (Real.rpow_nonneg (div_nonneg (hXb n) hBu.le) _) (by linarith)
  have hfin : (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) ≤
      Nh * Nh * max 1 (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by
    have : (Nh * Xa n) * (Nh * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) =
        Nh * Nh * (Xa n * (Xb n / sz.Bctl n (s n)) ^ (1 / (2 * (p : ℝ)))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hlam (mul_nonneg (by linarith) (by linarith))
  rw [hsq] at hu
  linarith

/-- The `Φ`-levels are nonnegative (`XL, XLK ≥ 1`, `B ≥ 0`). -/
private theorem nzFlow_phi_nonneg {X Y : ℕ → ℝ} {B : ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hB : 0 ≤ B) :
    0 ≤ nqLinPhi1 Y k ∧ 0 ≤ nqLinPhi2 X Y B k (Y k) ∧ 0 ≤ nqLinPhi3 X k := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hY0 : ∀ m, 0 ≤ Y m := fun m => zero_le_one.trans (hY m)
  refine ⟨Finset.sum_nonneg fun m _ => hY0 m, ?_, Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _⟩
  exact add_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (hY0 _)
    (Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _)) (mul_nonneg (Real.rpow_nonneg hB _) (hY0 _))

/-- The crude level `Φc` dominates every control of length `1 … k+1` and is `≥ 1`. -/
private theorem nzFlow_phiC_ge {X Y : ℕ → ℝ} {k m : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hm : m ∈ Finset.Icc 1 (k + 1)) : X m ≤ nqFlowPhiC X Y k ∧ Y m ≤ nqFlowPhiC X Y k := by
  have h := Finset.single_le_sum (f := fun m => X m + Y m)
    (fun m _ => add_nonneg (zero_le_one.trans (hX m)) (zero_le_one.trans (hY m))) hm
  have := hX m
  have := hY m
  unfold nqFlowPhiC
  constructor <;> linarith

private theorem nzFlow_phiC_one_le {X Y : ℕ → ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) :
    1 ≤ nqFlowPhiC X Y k := by
  have := (nzFlow_phiC_ge (k := k) (m := 1) hX hY (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)).1
  exact (hX 1).trans this

/-- The grid of the endpoint: `K_n = max 1 ⌈N^{C}⌉` (so `N^C ≤ K_n ≤ ⌈N^C⌉`, `K_n ≠ 0`; copy of
`nqFlow_K`, `NQEndFlow.lean:532`). -/
private def nzFlow_K (sz : Sizes d) (C : ℝ) (n : ℕ) : ℕ := max 1 ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊

private theorem nzFlow_K_ne_zero (sz : Sizes d) (C : ℝ) (n : ℕ) : nzFlow_K sz C n ≠ 0 := by
  unfold nzFlow_K
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

private theorem nzFlow_K_low (sz : Sizes d) (C : ℝ) (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) ^ C ≤ (nzFlow_K sz C n : ℝ) := by
  unfold nzFlow_K
  have h : ((sz.size n : ℕ) : ℝ) ^ C ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

private theorem nzFlow_K_up (sz : Sizes d) (C : ℝ) (n : ℕ) :
    nzFlow_K sz C n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ := by
  unfold nzFlow_K
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- `K_n + 1 ≤ N^{C+2}` eventually (`C ≥ 0`, `N ≥ 2`): `K_n ≤ ⌈N^C⌉ < N^C + 1`, `N^{C+2} = N^C N² ≥ 4 N^C ≥ N^C + 3`. -/
private theorem nzFlow_K_card (sz : Sizes d) (hsz : sz.SizeTendsto) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ((nzFlow_K sz C n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (C + 2) := by
  filter_upwards [hsz.eventually_ge_atTop 2] with n hN2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := Real.one_le_rpow hN1 hC
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := by linarith
  have hceil : (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) < ((sz.size n : ℕ) : ℝ) ^ C + 1 :=
    Nat.ceil_lt_add_one hP0
  have hK : (nzFlow_K sz C n : ℝ) ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := by
    exact_mod_cast nzFlow_K_up sz C n
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ (C + 2) = ((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    rw [Real.rpow_add hN0, Real.rpow_two]
  have h4 : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
  push_cast
  rw [hsplit]
  nlinarith

/-- `4 N^{-(D+2)} ≤ N^{-D}` for `N ≥ 2` (the four failure events of the endpoint). -/
private theorem nzFlow_four_pow_le {N D : ℝ} (hN : 2 ≤ N) : 4 * N ^ (-(D + 2)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have h : N ^ (-(D + 2)) = N ^ (-D) * (N ^ (2 : ℝ))⁻¹ := by
    rw [show -(D + 2) = -D + -2 by ring, Real.rpow_add hN0]
    congr 1
    exact Real.rpow_neg hN0.le 2
  rw [h]
  have h4 : (4 : ℝ) ≤ N ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
  have hp : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  have hN2 : 0 < N ^ (2 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have : 4 * (N ^ (2 : ℝ))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hN2]; exact h4
  nlinarith


/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1`: the sum `Σ_{m=k-1}^{k+1} XL m` contains
`XL k ≥ 1` and the other terms are nonnegative. -/
private theorem nzFlow_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
    (hXL : ∀ m, 1 ≤ XL m) (hXLK : ∀ m, 0 ≤ XLK m) (hB : 0 ≤ B) : 1 ≤ STbootRHS lo XL XLK B k p := by
  have hXL0 : ∀ m, 0 ≤ XL m := fun m => zero_le_one.trans (hXL m)
  unfold STbootRHS
  have h1 : 0 ≤ B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * k - 1) ^ (1 / 2 : ℝ) *
      XL (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg (hXL0 _) _))
      (Real.rpow_nonneg (hXL0 _) _)
  have h2 : 0 ≤ ∑ m ∈ Finset.Icc lo (k - 1), XLK m := Finset.sum_nonneg fun m _ => hXLK m
  have h3 : XL k ≤ ∑ m ∈ Finset.Icc (k - 1) (k + 1), XL m :=
    Finset.single_le_sum (f := XL) (fun m _ => hXL0 m) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have h4 : 0 ≤ ∑ m ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun m _ => mul_nonneg (hXLK _) (Real.rpow_nonneg (mul_nonneg (hXL0 _) (hXL0 _)) _)
  have := hXL k
  linarith

end Levels

/-! ## 4. Transfer facts (copies) and the `Q^{(A)}` facts: `(normQA2)` on the projected tensor, measurability, the projected initial event -/

section QProj

variable {d : ℕ}

private theorem nzFlow_meas_pathH (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem nzFlow_meas_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) : Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry sz n u i j

/-- `(𝓛 - 𝒦)^{(k)}_{u,σ,a}(H)` is measurable in the matrix `H` (as `gridGood_meas_loopFine`,
`GridGoodN.lean:266`, minus the constant `STKloop`). -/
private theorem nzFlow_meas_STLKM (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STLKM n E u H σ a :=
  (walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a).sub_const _

/-- **The transfer** (`map_pathH_eq`; copy of `nqFlow_transfer`, `NQEndFlow.lean:610`): a measurable matrix event has
the same probability on `pathP` at the grid index `j` and on `seqP` at the grid time. -/
private theorem nzFlow_transfer (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (j : ℕ) (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (hK : K n ≠ 0)
    {S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)} (hS : MeasurableSet S) :
    pathP sz (pathH sz s v K n j ⁻¹' S) = sz.seqP (sz.seqHflow n (gridTime s v K n j) ⁻¹' S) := by
  rw [← Measure.map_apply (nzFlow_meas_pathH sz s v K n j) hS,
    ← Measure.map_apply (nzFlow_meas_seqHflow sz n _) hS, map_pathH_eq sz s v K n j hs0 hsv hK]

/-- The union bound for four events of probability at most `x` each. -/
private theorem nzFlow_union4 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S A B C D' : Set Ω} {x y : ℝ}
    (hx : 0 ≤ x) (hA : μ A ≤ ENNReal.ofReal x) (hB : μ B ≤ ENNReal.ofReal x) (hC : μ C ≤ ENNReal.ofReal x)
    (hD : μ D' ≤ ENNReal.ofReal x) (hS : S ⊆ A ∪ B ∪ C ∪ D') (hxy : 4 * x ≤ y) :
    μ S ≤ ENNReal.ofReal y := by
  refine (measure_mono hS).trans ?_
  calc μ (A ∪ B ∪ C ∪ D') ≤ μ (A ∪ B ∪ C) + μ D' := measure_union_le _ _
    _ ≤ (μ (A ∪ B) + μ C) + μ D' := add_le_add_left (measure_union_le _ _) _
    _ ≤ ((μ A + μ B) + μ C) + μ D' := add_le_add_left (add_le_add_left (measure_union_le _ _) _) _
    _ ≤ ((ENNReal.ofReal x + ENNReal.ofReal x) + ENNReal.ofReal x) + ENNReal.ofReal x := by gcongr
    _ = ENNReal.ofReal (x + x + x + x) := by
        rw [ENNReal.ofReal_add (by positivity) hx, ENNReal.ofReal_add (by positivity) hx,
          ENNReal.ofReal_add hx hx]
    _ ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal (by linarith)


/-- **`(normQA2)` on the loops** (`3_5:1466`, `norm_zeroModeSet_le`): if every entry of the tensor `T` has norm at most
`x`, then `‖(Q^{(A)} T)_a‖ ≤ 2^{|A|} ‖T‖ ≤ 2^k x` (`|A| ≤ k`). -/
private theorem nzFlow_proj_le {L k : ℕ} [NeZero L] (A : Finset (Fin k)) (T : (Fin k → Zd d L) → ℂ)
    {x : ℝ} (hx : 0 ≤ x) (hT : ∀ b, ‖T b‖ ≤ x) (a : Fin k → Zd d L) :
    ‖zeroModeSet d L A T a‖ ≤ 2 ^ k * x := by
  have h1 : ‖T‖ ≤ x := (pi_norm_le_iff_of_nonneg hx).2 hT
  have hA : A.card ≤ k := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ A
  calc ‖zeroModeSet d L A T a‖ ≤ ‖zeroModeSet d L A T‖ := norm_le_pi_norm _ a
    _ ≤ 2 ^ A.card * ‖T‖ := norm_zeroModeSet_le A T
    _ ≤ 2 ^ k * x :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hA) h1 (norm_nonneg _) (by positivity)

/-- **Measurability of the projected matrix functional**: `H ↦ ‖(Q^{(A)}(𝓛-𝒦)^{(k)}_{u,σ,·}(H))_a‖` is measurable
(`Measurable.of_eval` with `nzFlow_meas_STLKM`, then the continuous linear functional `T ↦ (Q^{(A)} T)_a` on the
finite-dimensional space of `k`-index tensors, `zeroModeSetLin`). -/
private theorem nzFlow_meas_proj (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (A : Finset (Fin k)) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖zeroModeSet d (sz.L n) A (fun b => sz.STLKM n E u H σ b) a‖ := by
  have h1 : Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      (fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b) :=
    Measurable.of_eval fun b => nzFlow_meas_STLKM sz n E u σ b
  have h2 : Continuous fun T : (Fin k → Zd d (sz.L n)) → ℂ => zeroModeSet d (sz.L n) A T a :=
    LinearMap.continuous_of_finiteDimensional
      ((LinearMap.proj a).comp (zeroModeSetLin (d := d) (L := sz.L n) A))
  exact (h2.measurable.comp h1).norm

/-- **The projected initial event** (DECISIONS §94 (2); `3_5:1902`, `(normQA2)` `3_5:1466`; paper-delta candidate
`T2292c`): from `STLK s` at the length `k ≥ 1` and the half exponent `ε/2` (its bad set is over all `(σ, b)`), for
every `ε, D > 0`, eventually `P(∃ σ, A, a: N^ε B_s^k < ‖(Q^{(A)}(𝓛-𝒦)^{(k)}_{s,σ,·})_a‖) ≤ N^{-D}`:
`‖(Q^{(A)} T)_a‖ ≤ 2^{|A|} sup_b ‖T_b‖ ≤ 2^k N^{ε/2} B_s^k ≤ N^ε B_s^k` once `2^k ≤ N^{ε/2}`. -/
private theorem nzFlow_initQ (sz : Sizes d) (hsize : sz.SizeTendsto) {E s : ℕ → ℝ} (hLK : STLK sz E s)
    {k : ℕ} (hk : 1 ≤ k) {ε : ℝ} (hε : 0 < ε) {D : ℝ} (hD : 0 < D) :
    ∀ᶠ n in atTop, sz.seqP {ω | ∃ (σ : Fin k → Bool) (A : Finset (Fin k))
        (a : Fin k → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ k <
          ‖zeroModeSet d (sz.L n) A
            (fun b => Lloop sz n (E n) (s n) σ b ω - STKloop sz n (E n) (s n) σ b) a‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  have h2k : ∀ᶠ n in atTop, (2 : ℝ) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hsize).eventually_ge_atTop _
  filter_upwards [hLK k hk (ε / 2) (half_pos hε) D hD, h2k] with n h1 h2
  refine le_trans (measure_mono ?_) h1
  intro ω hω
  obtain ⟨σ, A, a, hlt⟩ := hω
  by_contra hno
  have hall : ∀ b : Fin k → Zd d (sz.L n),
      ‖Lloop sz n (E n) (s n) σ b ω - STKloop sz n (E n) (s n) σ b‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k := by
    intro b
    by_contra hb
    exact hno ⟨(σ, b), not_le.1 hb⟩
  have hx0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k :=
    (norm_nonneg _).trans (hall fun _ => 0)
  have hproj := nzFlow_proj_le A (fun b => Lloop sz n (E n) (s n) σ b ω - STKloop sz n (E n) (s n) σ b)
    hx0 hall a
  have hsq : ((sz.size n : ℕ) : ℝ) ^ ε =
      ((sz.size n : ℕ) : ℝ) ^ (ε / 2) * ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ hε).symm
  have hfin : (2 : ℝ) ^ k * (((sz.size n : ℕ) : ℝ) ^ (ε / 2) * (sz.Bctl n (s n)) ^ k) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ k := by
    rw [hsq, mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 hx0
  linarith

/-- **The collapsed section** `u_n = s_n` (the separate case `v_n = s_n` of paper-delta D597, `docs/paper-deltas.md:1556`; paper-delta candidate `T2292d`): for
every deterministic `ζ_n ≥ 1` and every choice `σ_n`, `A_n`, `a_n` (no relation between `A_n` and `I_diff(σ_n)` is
needed), `‖(Q^{(A_n)}(𝓛-𝒦)^{(k)}_{s,σ_n,·})_{a_n}‖ / B_s^k ≺ ζ`: `STLK s` at the exponent `τ`, `(normQA2)` through
`nzFlow_initQ`, `B_s^k > 0` and `ζ ≥ 1`. -/
private theorem nzFlow_collapsed (sz : Sizes d) (hsize : sz.SizeTendsto) {E s : ℕ → ℝ} (hLK : STLK sz E s)
    {k : ℕ} (hk : 1 ≤ k) (hBs : ∀ n, 0 < sz.Bctl n (s n)) {ζ : ℕ → ℝ} (hζ : ∀ n, 1 ≤ ζ n)
    (σ : ∀ n, Fin k → Bool) (A : ∀ n, Finset (Fin k)) (a : ∀ n, Fin k → Zd d (sz.L n)) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (A n)
          (fun b => Lloop sz n (E n) (s n) (σ n) b ω - STKloop sz n (E n) (s n) (σ n) b) (a n)‖ /
        (sz.Bctl n (s n)) ^ k)
      (fun n (_ : Unit) _ => ζ n) := by
  intro τ hτ D hD
  filter_upwards [nzFlow_initQ sz hsize hLK hk hτ hD] with n h2
  refine le_trans (measure_mono ?_) h2
  intro ω hω
  simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
  obtain ⟨_, hω⟩ := hω
  refine ⟨σ n, A n, a n, ?_⟩
  have hBk : 0 < (sz.Bctl n (s n)) ^ k := pow_pos (hBs n) _
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hlt := (lt_div_iff₀ hBk).1 hω
  calc ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (s n)) ^ k
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n * (sz.Bctl n (s n)) ^ k := by
        have := mul_le_mul_of_nonneg_left (hζ n) hN0
        nlinarith
    _ < _ := hlt

end QProj

/-! ## 5. The per-section endpoint -/

section Endpoint

variable {d : ℕ}

/-- **The endpoint at one non-collapsed section** (`s_n < v_n ≤ t_n`; the shape of the merged `nqFlow_core`,
`NQEndFlow.lean:642`, with `nzGridEndN` in place of `nqGridEndLinN`): for deterministic controls `X m n`, `Y m n ≥ 1` with `Ξ̂^{(𝓛)}_{w,m} ≺ X m`
(`STlenL n_ p m`) and `Ξ̂^{(𝓛-𝒦)}_{w,m} ≺ Y m` (`m ≤ n_`) uniformly in `w ∈ [s_n, v_n]`, the zero-mode-removed
`(Q^{(A_n)}(𝓛-𝒦)^{(n_)})_{v,σ_n,a_n}/B_v^{n_}` (`A_n ⊇ I_diff(σ_n)`) is `≺ B_v^{1/6} Y n_ + STbootRHS 2 X Y B_s n_ p`.
The failure event is inside the union of four events of probability `≤ N^{-(D+2)}`: the grid walk leaving `GoodSetN`
(`hGrid`, the good-event lemma on the window `[s, v]`, at the crude level `Φc` and the level `Λ_s`) or `GoodLinN`
(`hLin`), the projected initial loops (`nzFlow_initQ`, `map_pathH_eq` at `j = 0`) and the exceptional event `Gᶜ` of
`nzGridEndN` at `ε₀ = τ/2`, `D₁ = D + 2`; outside it, `nzGridEndN` bounds the terminal projected loop by
`N^{τ/2}(Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^{n_} ≤ N^{τ} ζ B_v^{n_}` (`nzFlow_level_le`), transferred to `seqHflow` at
`v_n` by `map_pathH_eq` at `j = K_n` (`gridTime_last`).  No window `W⁻¹ ≤ (1-t)/(1-s)` and no `hσ`: `nzGridEndN` has
neither. -/
private theorem nzFlow_core (sz : Sizes d) {E s t v : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseII s t) (hrange : sz.RangeCond τR t)
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLK sz E s) (hGrid : GridGoodNConcl sz E s v)
    (hLin : NQLinConcl sz E s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {X Y : ℕ → ℕ → ℝ}
    (hX1 : ∀ m n, 1 ≤ X m n) (hY1 : ∀ m n, 1 ≤ Y m n)
    (hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => X m n))
    (hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Y m n))
    (σ : ∀ n, Fin n_ → Bool) (A : ∀ n, Finset (Fin n_)) (hA : ∀ n, STIdiff (σ n) ⊆ A n)
    (a : ∀ n, Fin n_ → Zd d (sz.L n)) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (A n)
          (fun b => Lloop sz n (E n) (v n) (σ n) b ω - STKloop sz n (E n) (v n) (σ n) b) (a n)‖ /
        (sz.Bctl n (v n)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) := by
  intro τ hτ D hD
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (nqFlowLam (fun m => X m n) (sz.Bctl n (s n)) n_ p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun m => Y m n) n_ with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (v n)) n_ (Y n_ n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun m => X m n) n_ with hΦ₃def
  set Φc : ℕ → ℝ := fun n => nqFlowPhiC (fun m => X m n) (fun m => Y m n) n_ with hΦcdef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    nzFlow_phi_nonneg (fun m => hX1 m n) (fun m => hY1 m n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => nzFlow_phiC_one_le (fun m => hX1 m n) (fun m => hY1 m n)
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := nzGridEndN sz κ' 𝔠 τR 𝔡 E s t hd hκ h𝔠 hτR h𝔡
    hsize hband hWO hE hs0 hst ht1 hcase hrange n_ hn Λ Φ₁ Φ₂ Φ₃ hΛ0 (Eventually.of_forall hΛ1)
    (fun n => (hΦ n).1) (fun n => (hΦ n).2.1) (fun n => (hΦ n).2.2) v (fun n => (hsv n).le) hvt
    (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := nzFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := nzFlow_K_ne_zero sz C_K
  have hKcard := nzFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (nzFlow_K_low sz C_K))
    (Eventually.of_forall (nzFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Φc n) :=
    fun m hm hm' => nzFlow_prec_of_le_right (hX m hm (Or.inl hm')) fun n u ω =>
      (nzFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, hm'⟩)).1
  have hYg : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => Φc n) :=
    fun m hm hm' => nzFlow_prec_of_le_right (hY m hm hm') fun n u ω =>
      (nzFlow_phiC_ge (fun m => hX1 m n) (fun m => hY1 m n) (Finset.mem_Icc.2 ⟨hm, by omega⟩)).2
  have hQ : Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * n_ - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    nzFlow_hQ sz hsize (fun n => (hsv n).le) hv1 (a := 2 * n_ - 1) (b := 4 * p) hp
      (Xa := fun n => X (2 * n_ - 1) n) (Xb := fun n => X (4 * p) n)
      (fun n => zero_le_one.trans (hX1 _ n)) (fun n => zero_le_one.trans (hX1 _ n))
      (hX (2 * n_ - 1) (by omega) (Or.inr (Or.inl rfl))) (hX (4 * p) (by omega) (Or.inr (Or.inr rfl)))
  have hgood := hGrid v (fun n => (hsv n).le) (fun n => le_rfl) K hK0 n_ hn Λ Φc hΛ1 hΦc1 hXg hYg p hp hQ
    (C_K + 2) hKcard ε₁ hε₁ τ' hτ' D' hD'
  have hlin := hLin v (fun n => (hsv n).le) hvt K hK0 n_ hn X Y hX1 hY1
    (fun m hm hm' => hX m hm (Or.inl hm')) hY (C_K + 2) hKcard ε₁ hε₁
  have hinit := nzFlow_initQ sz hsize hLK (k := n_) (by omega) hε₁ (D := D + 2) (by linarith)
  filter_upwards [hpin, hgood (D + 2) (by linarith), hlin (D + 2) (by linarith), hinit,
    hsize.eventually_ge_atTop 2] with n hG hGood hLinn hInit hN2
  obtain ⟨G, hGP, hGb⟩ := hG
  have hNn1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg (by linarith) _
  -- the two matrix events: the terminal projected bound fails / an initial projected loop is large
  set Sterm : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
        STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) <
      ‖zeroModeSet d (sz.L n) (A n) (fun b => sz.STLKM n (E n) (v n) M (σ n) b) (a n)‖ /
        (sz.Bctl n (v n)) ^ n_} with hStermdef
  set Sinit : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ (σ' : Fin n_ → Bool) (A' : Finset (Fin n_)) (a' : Fin n_ → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
        ‖zeroModeSet d (sz.L n) A' (fun b => sz.STLKM n (E n) (s n) M σ' b) a'‖}
    with hSinitdef
  have hSterm : MeasurableSet Sterm :=
    measurableSet_lt measurable_const
      ((nzFlow_meas_proj sz n (E n) (v n) (σ n) (A n) (a n)).div_const _)
  have hSinit : MeasurableSet Sinit := by
    have heq : Sinit = ⋃ x : (Fin n_ → Bool) × Finset (Fin n_) × (Fin n_ → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ <
          ‖zeroModeSet d (sz.L n) x.2.1 (fun b => sz.STLKM n (E n) (s n) M x.1 b) x.2.2‖} := by
      ext M; simp [hSinitdef]
    rw [heq]
    exact MeasurableSet.iUnion fun x =>
      measurableSet_lt measurable_const (nzFlow_meas_proj sz n (E n) (s n) x.1 x.2.1 x.2.2)
  -- the transfers at the terminal grid index and at index `0`
  have e1 : sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := by
    have := nzFlow_transfer sz (s := s) (v := v) (K := K) (n := n) (K n) (hs0 n) (hsv n).le (hK0 n) hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have e0 : pathP sz (pathH sz s v K n 0 ⁻¹' Sinit) = sz.seqP (sz.seqHflow n (s n) ⁻¹' Sinit) := by
    have := nzFlow_transfer sz (s := s) (v := v) (K := K) (n := n) 0 (hs0 n) (hsv n).le (hK0 n) hSinit
    rw [ST_gridTime_zero] at this
    exact this
  -- the failure event of the terminal bound is inside the union of four events
  have hmain : pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine nzFlow_union4 (C := pathH sz s v K n 0 ⁻¹' Sinit) (D' := Gᶜ) hx0 hGood hLinn ?_ ?_ ?_
      (nzFlow_four_pow_le hN2)
    · rw [e0]
      exact hInit
    · rw [← ofReal_measureReal (measure_ne_top (pathP sz) _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨hgoodω, hlinω⟩, hinitω⟩, hGω⟩ := hno
      have hinit' : ∀ σ' : Fin n_ → Bool, ∀ A' : Finset (Fin n_), STIdiff σ' ⊆ A' →
          ∀ a' : Fin n_ → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A' (fun b => sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ' b) a'‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ n_ := by
        intro σ' A' _ a'
        by_contra hcon
        exact hinitω ⟨σ', A', a', not_le.1 hcon⟩
      have hb := hGb ω hGω (fun j hj => ⟨hgoodω j hj, hlinω j hj⟩) hinit' (σ n) (A n) (hA n) (a n)
      have hlev : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤
          (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p :=
        nzFlow_level_le hn hp (fun m => hX1 m n) (fun m => hY1 m n) (hBs n)
      have hBk : 0 < (sz.Bctl n (v n)) ^ n_ := pow_pos (hBv n) _
      have hL0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ n
        linarith [this]
      have hdiv : ‖zeroModeSet d (sz.L n) (A n)
            (fun b => sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) (σ n) b) (a n)‖ /
          (sz.Bctl n (v n)) ^ n_ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) := (div_le_iff₀ hBk).2 hb
      have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
        Real.rpow_le_rpow_of_exponent_le hNn1 (by linarith)
      have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
      have hz0 : 0 ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
          STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p := hL0.trans hlev
      have hfin : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
            STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
        calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y n_ n +
              STbootRHS 2 (fun m => X m n) (fun m => Y m n) (sz.Bctl n (s n)) n_ p) :=
              mul_le_mul_of_nonneg_left hlev hpos
          _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hz0
      exact absurd hω (not_lt.2 (hdiv.trans hfin))
  calc sz.seqP (badSetAt sz.size _ _ τ n) = sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) := by
        congr 1
        ext ω
        exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
    _ = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

/-- **The endpoint at an arbitrary section** `q n = (u_n, ⟨(σ_n, A_n), h_n⟩, a_n)` of the parameter set of
`STNZConclPT''` (`perTimeDomAt_iff_forall_section`): `v_n = u_n` where `s_n < u_n`, `v_n = t_n` elsewhere (so
`s < v ≤ t`), the controls are the numbers `XL m n (v n)`, `XLK m n (v n)` on the window `[s, v]`
(`nzFlow_restrict_pair`), and `nzFlow_core` gives the bound at the indices with `s_n < u_n` (`STCaseII s t` concerns
`s` only, so it holds on every window `[s, v]` unchanged).  At the collapsed indices `u_n = s_n` (the separate case
`v_n = s_n` of paper-delta D597; paper-delta candidate `T2292d`) the section is bounded by `nzFlow_collapsed`
(`STLK s` and `(normQA2)`): `‖(Q^{(A)}(𝓛-𝒦))_s‖ ≤ N^τ B_s^{n_} ≤ N^τ ζ B_s^{n_}`, `ζ ≥ 1`. -/
private theorem nzFlow_section (sz : Sizes d) {E s t : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseII s t) (hrange : sz.RangeCond τR t)
    (hLK : STLK sz E s)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConcl sz E s v)
    (hLin : NQLinConcl sz E s t) {n_ p : ℕ} (hn : 2 ≤ n_) (hp : 1 ≤ p) {XL XLK : ℕ → ℕ → ℝ → ℝ}
    (hXL : ∀ m n u, 1 ≤ XL m n u) (hXLK : ∀ m n u, 1 ≤ XLK m n u)
    (hXLp : ∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2))
    (hXLKp : ∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2))
    (q : ∀ n, TimeIcc s t n × {σA : (Fin n_ → Bool) × Finset (Fin n_) // STIdiff σA.1 ⊆ σA.2} ×
      (Fin n_ → Zd d (sz.L n))) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => ‖zeroModeSet d (sz.L n) (q n).2.1.1.2
          (fun b => Lloop sz n (E n) ((q n).1 : ℝ) (q n).2.1.1.1 b ω -
            STKloop sz n (E n) ((q n).1 : ℝ) (q n).2.1.1.1 b) (q n).2.2‖ /
        (sz.Bctl n ((q n).1 : ℝ)) ^ n_)
      (fun n (_ : Unit) _ => (sz.Bctl n ((q n).1 : ℝ)) ^ (1 / 6 : ℝ) * XLK n_ n ((q n).1 : ℝ) +
        STbootRHS 2 (fun m => XL m n ((q n).1 : ℝ)) (fun m => XLK m n ((q n).1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
  classical
  -- the end `v` of the window of the endpoint
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => if s n < ((q n).1 : ℝ) then ((q n).1 : ℝ) else t n :=
    ⟨_, rfl⟩
  have hsv : ∀ n, s n < v n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]
    · simp only [hvdef, h, ↓reduceIte]; exact hst n
  have hvt : ∀ n, v n ≤ t n := fun n => by
    by_cases h : s n < ((q n).1 : ℝ)
    · simp only [hvdef, h, ↓reduceIte]; exact (q n).1.2.2
    · simp only [hvdef, h, ↓reduceIte]; exact le_rfl
  have hX : ∀ m : ℕ, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => XL m n (v n)) := fun m hm hl =>
    nzFlow_restrict_pair (sz := sz) (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiL sz n (E n) w m ω) (Z := fun n u => XL m n u) (hXLp m hm hl)
  have hY : ∀ m : ℕ, 1 ≤ m → m ≤ n_ →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω)
        (fun n _ _ => XLK m n (v n)) := fun m hm hm' =>
    nzFlow_restrict_pair (sz := sz) (s := s) (t := t) (v := v) hvt
      (F := fun n w ω => STXiLK sz n (E n) w m ω) (Z := fun n u => XLK m n u) (hXLKp m hm hm')
  have hcore := nzFlow_core sz hd hκ h𝔠 hτR h𝔡 hsize hband hWO hE hs0 (fun n => (hst n).le) ht1 hcase
    hrange hsv hvt hLK (hGrid v hsv hvt) hLin hn hp (X := fun m n => XL m n (v n))
    (Y := fun m n => XLK m n (v n)) (fun m n => hXL m n _) (fun m n => hXLK m n _) hX hY
    (fun n => (q n).2.1.1.1) (fun n => (q n).2.1.1.2) (fun n => (q n).2.1.2) (fun n => (q n).2.2)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hst n).trans (ht1 n))
  have hζ1 : ∀ n, 1 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) +
      STbootRHS 2 (fun m => XL m n (s n)) (fun m => XLK m n (s n)) (sz.Bctl n (s n)) n_ p := by
    intro n
    have h0 : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 6 : ℝ) * XLK n_ n (s n) :=
      mul_nonneg (Real.rpow_nonneg (hBs n).le _) (zero_le_one.trans (hXLK _ _ _))
    have := nzFlow_bootRHS_one_le (lo := 2) (XL := fun m => XL m n (s n)) (XLK := fun m => XLK m n (s n))
      (B := sz.Bctl n (s n)) (k := n_) (p := p) (by omega) (fun m => hXL _ _ _)
      (fun m => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
    linarith
  have hcoll := nzFlow_collapsed sz hsize hLK (k := n_) (by omega) hBs hζ1
    (fun n => (q n).2.1.1.1) (fun n => (q n).2.1.1.2) (fun n => (q n).2.2)
  intro τ hτ D hD
  filter_upwards [hcore τ hτ D hD, hcoll τ hτ D hD] with n h1 h2
  by_cases hn' : s n < ((q n).1 : ℝ)
  · -- the section is not collapsed: `v n = u_n`
    have hv : v n = ((q n).1 : ℝ) := by simp only [hvdef, hn', ↓reduceIte]
    simp only [badSetAt] at h1 ⊢
    rw [hv] at h1
    exact h1
  · -- collapsed: `u_n = s_n`
    have hu : ((q n).1 : ℝ) = s n := le_antisymm (not_lt.1 hn') (q n).1.2.1
    refine le_trans (measure_mono ?_) h2
    intro ω hω
    simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨_, hω⟩ := hω
    rw [hu] at hω
    exact ⟨(), hω⟩

end Endpoint

/-! ## 6. The per-time pin `stOeqNZPT''_holds` -/

/-- **`stOeqNZPT''_holds`: the per-time case-(ii) projected R2* pin for every `d ≥ 3`**
(`T2292_stOeqNZPT''_holds`; `lem:STOeq_Qt_nonzero` `3_5:1561`, bound `(am;asoiuw_smalleta)` `3_5:1916-1922` at each
fixed `u` with the first summand of `STbootRHS` at `B_s`, `3_5:1931`; proof `3_5:1889-1933`).
`𝔠_d = min 𝔠_d^G 𝔠_d^L`, with `𝔠_d^G`, `𝔠_d^L` the constants of `gridGoodN_holds d` and `nqLinGood_holds d` at the same
`(κ, ε, 𝔡, C_d)`; `STConStInd` passes to the larger exponents `𝔠_d^G`, `𝔠_d^L` (`nzFlow_conStInd_exp_mono`).  There is no
`1/(2d)` in `𝔠_d`: case (ii) uses no `st_window` and `nzGridEndN` has no `W⁻¹ ≤ (1-t)/(1-s)` premise.  The premises of
`nzGridEndN` come from the flow (`v3_premises_of_stFlow` with `κ/2`, `ε/2`); the good-event lemma `gridGoodN_holds` is
re-instantiated on every window `[s, v]` (`st_conStInd_sub`, `nzFlow_step2_restrict`); then
`perTimeDomAt_iff_forall_section` and `nzFlow_section` (paper-delta candidates `T2292a`, `T2292c`, `T2292d`). -/
theorem stOeqNZPT''_holds : ∀ d : ℕ, STOeqNZPT'' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := gridGoodN_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := nqLinGood_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min 𝔠G 𝔠L := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min hG0 hL0
  have h𝔠dG : 𝔠d ≤ 𝔠G := by rw [h𝔠d]; exact min_le_left _ _
  have h𝔠dL : 𝔠d ≤ 𝔠L := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hconG : sz.STConStInd 𝔠G s t := nzFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := nzFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) →
      GridGoodNConcl sz (STflowE z) s v := fun v hsv hvt =>
    HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (nzFlow_step2_restrict hvt hStep2)
  have hLin : NQLinConcl sz (STflowE z) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  refine (perTimeDomAt_iff_forall_section sz.seqP sz.size
    (fun n => ⟨(⟨s n, le_rfl, (hst n).le⟩, ⟨((fun _ => true), Finset.univ), Finset.subset_univ _⟩,
      fun _ => 0)⟩) _ _).2 ?_
  intro q
  exact nzFlow_section sz hd (half_pos hκ) hA.1 (half_pos hε) hA.2.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2
    (fun n => (hE' n).le) hs hst ht1 hR hrange hLK hGrid hLin hn hp hXL hXLK hXLp hXLKp q

/-! ## 7. Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.QtNonzeroFlowInst`.  Data: the case-(ii) data of the merged `inst_OeqQtNZ`
(`Step34Pins.lean:1006`): `szB` (`d = 3`, `L = 4`, `W = n + 4`, `ilambda = 1`, `N = (4(n+4))^3`), the flow `zB`
(`z_n = 1/2 + i/64`, `flow_zB` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 15/16`, `t ≡ 31/32` (`szB_flow_ht`;
`szB_caseII`: `1 - s = 1/16 = ilambda²/L²`, the boundary of case (ii); `conStInd_const`: `(con_st_ind)` for every
`𝔠_d > 0`), `C_d = 1`.  `STKbound`, `STKward` are theorems of the flow (`stKbound_of_flow`, `stKward_of_flow`); what
stays a hypothesis of an example is a stochastic premise that is another gate's pin (`STLK s`, `STStep2Concl`, the pair
hypotheses `Ξ̂ ≺ 1` of the pin). -/

namespace QtNonzeroFlowInst

open RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.QtNonzeroEndInst

/-- **(1) `stOeqNZPT''_holds` at the data**: the per-time case-(ii) projected R2* pin at
`(szB, zB, s ≡ 15/16, t ≡ 31/32)`, `C_d = 1`: the constant `𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR`
(`STKbound`, `STKward`, `STLK`, `STStep2Concl`), then the conclusion `STNZConclPT''`.  Every deterministic hypothesis
(`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime `STCaseII`, `(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqNZPT'' :
    InstIngConcl (fun sz E s t => STNZConclPT'' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STNZConclPT'' sz E s t) (stOeqNZPT''_holds 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **(2) the conclusion applied** at `n_ = 3`, `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the flow, the
stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` of the pin (the conclusions of Steps 3-4,
other gates' pins) stay hypotheses; the per-time conclusion
`(Q^{(A)}(𝓛-𝒦)^{(3)})_{u,σ,a}/B_u³ ≺ B_u^{1/6} + STbootRHS 2 1 1 B_s 3 1` for every sign vector `σ`, every
`A ⊇ I_diff(σ)` and every label `a` (`PrecPT`: the union over `u ∈ [15/16, 31/32]` outside `P`) is the conclusion. -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16))
    (hStep2 : STStep2Concl szB (STflowE zB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiL szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec szB (U := STPair (fun _ => 15 / 16) (fun _ => 31 / 32))
        (fun n q ω => STXiLK szB n (STflowE zB n) q.1.1 m ω) (fun n q _ => (1 : ℝ))) :
    PrecPT szB (U := fun n => TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
        {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n)))
      (fun n q ω => ‖zeroModeSet 3 (szB.L n) q.2.1.1.2
          (fun b : Fin 3 → Zd 3 (szB.L n) =>
            Lloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b ω -
              STKloop szB n (STflowE zB n) (q.1 : ℝ) q.2.1.1.1 b) q.2.2‖ /
        (szB.Bctl n (q.1 : ℝ)) ^ 3)
      (fun n q _ => (szB.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 2 (fun _ => 1) (fun _ => 1) (szB.Bctl n (15 / 16)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqNZPT''
  exact hC (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB) hLK hStep2 3 1 (by norm_num) le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(3) `nzFlow_initQ` at the data** (`szB`, `k = 3`, `s ≡ 15/16`, exponent `ε = 1/160`, `D = 3`): the projected
initial event over all `σ`, `A`, `a` has probability at most `N^{-3}` eventually; `STLK s` is the hypothesis, and
`SizeTendsto` is discharged (`szB_tendsto`). -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
    ∀ᶠ n in atTop, szB.seqP {ω | ∃ (σ : Fin 3 → Bool) (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 (szB.L n)),
        ((szB.size n : ℕ) : ℝ) ^ (1 / 160 : ℝ) * (szB.Bctl n (15 / 16)) ^ 3 <
          ‖zeroModeSet 3 (szB.L n) A
            (fun b => Lloop szB n (STflowE zB n) (15 / 16) σ b ω - STKloop szB n (STflowE zB n) (15 / 16) σ b) a‖} ≤
      ENNReal.ofReal (((szB.size n : ℕ) : ℝ) ^ (-(3 : ℝ))) :=
  nzFlow_initQ szB szB_tendsto hLK (k := 3) (by norm_num) (ε := 1 / 160) (by norm_num) (D := 3) (by norm_num)

/-- **(3) at one size index**: the eventual statement of (3) is unfolded at a size index (`Filter.Eventually.exists`),
so it is not vacuous in `n`. -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
    ∃ n : ℕ, szB.seqP {ω | ∃ (σ : Fin 3 → Bool) (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 (szB.L n)),
        ((szB.size n : ℕ) : ℝ) ^ (1 / 160 : ℝ) * (szB.Bctl n (15 / 16)) ^ 3 <
          ‖zeroModeSet 3 (szB.L n) A
            (fun b => Lloop szB n (STflowE zB n) (15 / 16) σ b ω - STKloop szB n (STflowE zB n) (15 / 16) σ b) a‖} ≤
      ENNReal.ofReal (((szB.size n : ℕ) : ℝ) ^ (-(3 : ℝ))) :=
  (nzFlow_initQ szB szB_tendsto hLK (k := 3) (by norm_num) (ε := 1 / 160) (by norm_num) (D := 3)
    (by norm_num)).exists

/-- **(3) the collapsed section at the data** (`u_n = s_n ≡ 15/16`, `nzFlow_collapsed`): `STLK s` and `(normQA2)` give
`(Q^{(A)}(𝓛-𝒦)^{(3)})_{s,σ,a}/B_s³ ≺ 1` for `σ = sig3`, `A = I_diff(σ) = {0, 1}`, `a ≡ 0`; `B_s > 0` is discharged
(`st_Bctl_pos`, `s = 15/16 < 1`). -/
example (hLK : STLK szB (STflowE zB) (fun _ => 15 / 16)) :
    StochDomAt szB.seqP szB.size
      (fun n (_ : Unit) ω => ‖zeroModeSet 3 (szB.L n) ({0, 1} : Finset (Fin 3))
          (fun b => Lloop szB n (STflowE zB n) (15 / 16) sig3 b ω -
            STKloop szB n (STflowE zB n) (15 / 16) sig3 b) (fun _ => 0)‖ / (szB.Bctl n (15 / 16)) ^ 3)
      (fun n (_ : Unit) _ => (1 : ℝ)) :=
  nzFlow_collapsed szB szB_tendsto hLK (k := 3) (by norm_num) (fun n => st_Bctl_pos szB (by norm_num))
    (ζ := fun _ => 1) (fun _ => le_rfl) (fun _ => sig3) (fun _ => {0, 1}) (fun _ _ => 0)

/-- **(3) the bound `(normQA2)`** at numbers: `‖(Q^{(A)} 1)_a‖ ≤ 2^3` for the constant tensor `1` on `3` indices
over `Z_4^3` and every `A ⊆ Fin 3`. -/
example (A : Finset (Fin 3)) (a : Fin 3 → Zd 3 4) :
    ‖zeroModeSet 3 4 A (fun _ : Fin 3 → Zd 3 4 => (1 : ℂ)) a‖ ≤ 2 ^ 3 * 1 :=
  nzFlow_proj_le A _ zero_le_one (fun _ => by simp) a

/-- **(3) measurability at the data**: the projected matrix functional of `nzFlow_meas_proj` at `szB`, size index `0`,
`σ = sig3`, `A = I_diff(σ) = {0, 1}`. -/
example (a : Fin 3 → Zd 3 (szB.L 0)) :
    Measurable fun H : Matrix (Idx 3 (szB.L 0) (szB.W 0)) (Idx 3 (szB.L 0) (szB.W 0)) ℂ =>
      ‖zeroModeSet 3 (szB.L 0) ({0, 1} : Finset (Fin 3)) (fun b => szB.STLKM 0 (STflowE zB 0) (15 / 16) H sig3 b) a‖ :=
  nzFlow_meas_proj szB 0 (STflowE zB 0) (15 / 16) sig3 {0, 1} a

/-- **(4) the index set of the pin is nonempty and has the intended members**: `σ = sig3 = (+,-,+)` with `A = {0, 1}`
(`I_diff(sig3) = {0, 1}`, `QtNonzeroEndInst.σ3_idiff`), the constant `σ ≡ +` with `A = ∅` (`I_diff = ∅`), and any `A`
containing `I_diff(σ)`; the parameter type of `STNZConclPT''` at `szB` is nonempty at every size index. -/
example (n : ℕ) : Nonempty (TimeIcc (fun _ : ℕ => (15 / 16 : ℝ)) (fun _ : ℕ => (31 / 32 : ℝ)) n ×
    {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2} × (Fin 3 → Zd 3 (szB.L n))) :=
  ⟨(⟨15 / 16, le_rfl, by norm_num⟩, ⟨(sig3, {0, 1}), by rw [σ3_idiff]⟩, fun _ => 0)⟩

example : ∃ x : {σA : (Fin 3 → Bool) × Finset (Fin 3) // STIdiff σA.1 ⊆ σA.2},
    x.1 = ((fun _ => true), (∅ : Finset (Fin 3))) :=
  ⟨⟨((fun _ => true), ∅), by decide⟩, rfl⟩

example : STIdiff sig3 = ({0, 1} : Finset (Fin 3)) := σ3_idiff

/-- **(5) the statement of the target** (`T2292_stOeqNZPT''_holds`, check file section 3): `stOeqNZPT''_holds` has
exactly the type `∀ d : ℕ, STOeqNZPT'' d`. -/
example : ∀ d : ℕ, STOeqNZPT'' d := @stOeqNZPT''_holds

end QtNonzeroFlowInst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.STNZConclPT''
#print axioms RBM.Gauss.Sizes.STOeqNZPT''
#print axioms RBM.Ind.stOeqNZPT''_holds
#print axioms RBM.Ind.QtNonzeroFlowInst.inst_OeqNZPT''
