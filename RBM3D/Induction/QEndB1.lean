/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndGrid
import RBM3D.Induction.QEndA
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.NQLin
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.NQBudget
import RBM3D.Loop.KLFinal

/-!
# S3-18b1 (ticket T2310): per-time alternating flow endpoint, `stOeqQtRoundPT'_holds`

Stochastic layer ST-3, ticket 45 of 46 (the alternating chain S3-15…18; S3-18b2 assembles the
round to `STXiBoot'`). Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`):
`lem:STOeq_Qt` `3_5:1362-1378`, its proof `3_5:1678-1714` (non-alternating signs: `lem:STOeq_NQ`
`3_5:1679`; alternating signs: `(eq:alternatecase1)` `3_5:1687`, `(y27kasdfg)` `3_5:1692`,
`(eq:alternatecase2)` `3_5:1713`). Authority: DECISIONS §62 (2)/(4), §95 (3), §105 (1), §119-§120.
Format models: `Induction/NQEndFlow.lean` (T2246; `nqFlow_core`, `:642`) and
`Induction/QtNonzeroFlow.lean` (T2292) with `altGridEndQN` (`QEndGrid.lean:1326`, T2302) in place
of `nqGridEndLinN`.

## What is here (namespace `RBM.Gauss.Sizes` for the pins, `RBM.Ind` for the proof; every helper
is `private` with the prefix `altQFlow_`)

* **Pins** `STXiRoundPT'` (`STXiRound'`, `QtNonzeroBoot.lean:92`, with `Prec ↦ PrecPT` in the
  conclusion and `3 ≤ n_`; the index set is the pairs `(w, u)`, `s ≤ w ≤ u ≤ t`, and the
  current-length control `XLK n_` enters through the summand `B_u^{1/6} XLK n_ n u`) and
  `STOeqQtRoundPT'` (= `STIngR d STCaseI STXiRoundPT'`);
* §0 private copies of the helpers of `NQEndFlow.lean` (window and setting facts, the levels
  `Λ_s`, `Φc`, the degree-1 inequality, `hQ`, the grid `K_n`, the transfer `map_pathH_eq`, `1 ≤
  STbootRHS`);
* §1 small facts: `STbootRHS 2 ≤ STbootRHS 1`, `XLK (k-1) ≤ STbootRHS 2` for `k ≥ 3`, `W ≤ N`,
  `#Z_L^d`, `2 N^{-(D+c)} ≤ N^{-D}`;
* §2 **`altQFlow_initQ`**: the projected initial loops `‖𝒬_s(𝓛-𝒦)^{(m+2)}_{s,σ}‖ ≤ N^ε B_s^{m+2}`
  for every alternating `σ`, with high probability, from `startLevelQN` (`QLevelsA.lean:421`),
  `STLK s` at the lengths `m+1`, `m+2` and the far decay `STDecayLoopU` (`stDecayLoopU_of_step2`);
* §3 **`altQFlow_core`**: the alternating endpoint at one section `s < v ≤ t` (`altGridEndQN` at
  `ε₀ = τ/2`, `D₁ = D + 2`, the good events `gridGoodN_holds`, `nqLinGood_holds`, `altYGridN` at
  the length `m+1`, the initial event, the transfer to `seqHflow`);
* §4 `altQFlow_nq_half` (the non-alternating signs from the merged per-time pin
  `stOeqNQPT''_holds` on the window `[s, uu]` with the controls frozen at `uu_n`, union over `(σ,
  a)` by `stochDomAt_of_perTimeDomAt`) and `altQFlow_collapsed` (`STLK s`);
* §5 `altQFlow_section`: the bound at an arbitrary pair `q n = ((w_n, u_n), _)`; §6
  **`stOeqQtRoundPT'_holds`**;
* §7 compiled nonempty instances at `d = 3` (namespace `RBM.Ind.QEndB1Inst`).

Differences from the ticket's proof sketch (paper-delta candidates, see the prove report):
`T2310a` the pin is the pair-indexed per-time form of `(eq:alternatecase1)` with controls constant
in `v` and `B_v^{1/6} ≤ B_u^{1/6}`; `T2310b` the initial-loop split is `ν = N^{e/8}`, `τ_N = e/2`,
`e = min ε₁ 1` (the sketch's `τ_N = ε₁/8` violates `hMΛ`, and `ν ≤ N` needs `ε₁ ≤ 8`); `T2310c`
the non-alternating half is the merged `stOeqNQPT''_holds` used as a black box on the window `[s,
uu]` (the sketch has no non-alternating half, but `Ξ̂^{(𝓛-𝒦)}` is the maximum over all signs);
`T2310d` collapsed sections `w_n = s_n` by `STLK s`; `T2310e` the factor `2` of the `X`-summand
and of `1 + max` is absorbed by `N^{τ/2} ≥ 2`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## Pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Pins

variable {d : ℕ} (sz : Sizes d)

/-- Per-time round: `STXiRound'` with `Prec` ↦ `PrecPT` in the conclusion and `3 ≤ n_`.
    Target of `stOeqQtRoundPT'_holds`; assembled to `STXiBoot'`/`STOeqQt'` by S3-18b2
    via `stXiBootR_of_round` (QtNonzeroBoot.lean:581). -/
def STXiRoundPT' (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 3 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
        (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => XLK m n q.1.2)) →
    PrecPT sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => sz.Bctl n q.1.2 ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2)
          (sz.Bctl n (s n)) n_ p)

end Pins

/-- Per-time round ingredient: `STXiRoundPT'` packed into the `STIngR` shape. -/
def STOeqQtRoundPT' (d : ℕ) : Prop :=
  STIngR d STCaseI (fun sz E s t => STXiRoundPT' sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Ind

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## §0 helpers (private copies of `NQEndFlow.lean`) -/

section Helpers

variable {d : ℕ}

/-- A pointwise larger right side keeps `≺` (the failure event only shrinks; `N^τ ≥ 0`). -/
private theorem altQFlow_prec_of_le_right {sz : Sizes d} {U : ℕ → Type*} {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : sz.Prec ξ ζ) (hle : ∀ n u ω, ζ n u ω ≤ ζ' n u ω) : sz.Prec ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  exact ⟨u, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hle n u ω)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hu⟩

/-- `(con_st_ind)` is monotone in the exponent: it forces `B_t < 1` (`B_t^a ≥ 1` if `B_t ≥ 1`, against the
ratio `< 1`), and `B^b ≤ B^a` for `B ≤ 1`, `a ≤ b`. -/
private theorem altQFlow_conStInd_exp_mono (sz : Sizes d) {s t : ℕ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
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
private theorem altQFlow_step2_restrict {sz : Sizes d} {E s t v : ℕ → ℝ} {Cd : ℝ} (hvt : ∀ n, v n ≤ t n)
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

/-- `Ξ̂^{(𝓛)}_{v,k} ≥ 1` (copy of the private `gridGood_one_le_STXiL`, `GridGoodN.lean:655`). -/
private theorem altQFlow_one_le_STXiL (sz : Sizes d) {n : ℕ} {E v : ℝ} (k : ℕ) (ω : sz.SeqΩ)
    (hB : 0 < sz.Bctl n v) : 1 ≤ STXiL sz n E v k ω := by
  unfold STXiL
  have h0 : 0 ≤ STmaxL sz n E v k ω :=
    le_trans (norm_nonneg _) (Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω‖) (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))))
  have := div_nonneg h0 (pow_pos hB (k - 1)).le
  linarith

/-- **G1, exactly** (R2*): `(XL(2k−1) (XL(4p)/B)^{1/(2p)})^{1/2}` is the first summand of `STbootRHS … B k p`
(`B > 0`, `p ≥ 1`, `XL ≥ 0`): `nqFlowLam` at `B = B_s` has `Λ^{1/2}` equal to it, with no loss. -/
private theorem altQFlow_lam_sqrt {X : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hp : 1 ≤ p) (hB : 0 < B) (hX : ∀ m, 0 ≤ X m) :
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
private theorem altQFlow_phi3_le {X : ℕ → ℝ} {k : ℕ} (hk : 2 ≤ k) (hX : ∀ m, 1 ≤ X m) :
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
`B^{1/6} XLK k`, `1 + Φ₃ ≤ Σ_{m=k-1}^{k+1} XL m` (`altQFlow_phi3_le`), and `(nqFlowLam X B_s k p)^{1/2}` is the first
summand of `STbootRHS` (`altQFlow_lam_sqrt`), so `Λ_s^{1/2} ≤ 1 + ` that summand. -/
private theorem altQFlow_level_le {X Y : ℕ → ℝ} {B Bs : ℝ} {k p : ℕ} (hk : 2 ≤ k) (hp : 1 ≤ p)
    (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) (hBs : 0 < Bs) :
    (max 1 (nqFlowLam X Bs k p)) ^ ((1 : ℝ) / 2) + nqLinPhi1 Y k + nqLinPhi2 X Y B k (Y k) +
        nqLinPhi3 X k ≤
      B ^ (1 / 6 : ℝ) * Y k + STbootRHS 2 X Y Bs k p := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hphi3 := altQFlow_phi3_le hk hX
  have hlam := altQFlow_lam_sqrt (k := k) hp hBs hX0
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
private theorem altQFlow_hQ (sz : Sizes d) (hsz : sz.SizeTendsto) {E s v : ℕ → ℝ} (hsv : ∀ n, s n ≤ v n)
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
  have hXb0 : 0 ≤ STXiL sz n (E n) (u : ℝ) b ω := zero_le_one.trans (altQFlow_one_le_STXiL sz b ω hBu)
  have hXa0 : 0 ≤ STXiL sz n (E n) (u : ℝ) a ω := zero_le_one.trans (altQFlow_one_le_STXiL sz a ω hBu)
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
private theorem altQFlow_phi_nonneg {X Y : ℕ → ℝ} {B : ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hB : 0 ≤ B) :
    0 ≤ nqLinPhi1 Y k ∧ 0 ≤ nqLinPhi2 X Y B k (Y k) ∧ 0 ≤ nqLinPhi3 X k := by
  have hX0 : ∀ m, 0 ≤ X m := fun m => zero_le_one.trans (hX m)
  have hY0 : ∀ m, 0 ≤ Y m := fun m => zero_le_one.trans (hY m)
  refine ⟨Finset.sum_nonneg fun m _ => hY0 m, ?_, Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _⟩
  exact add_nonneg (Finset.sum_nonneg fun m _ => mul_nonneg (hY0 _)
    (Real.rpow_nonneg (mul_nonneg (hX0 _) (hX0 _)) _)) (mul_nonneg (Real.rpow_nonneg hB _) (hY0 _))

/-- The crude level `Φc` dominates every control of length `1 … k+1` and is `≥ 1`. -/
private theorem altQFlow_phiC_ge {X Y : ℕ → ℝ} {k m : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m)
    (hm : m ∈ Finset.Icc 1 (k + 1)) : X m ≤ nqFlowPhiC X Y k ∧ Y m ≤ nqFlowPhiC X Y k := by
  have h := Finset.single_le_sum (f := fun m => X m + Y m)
    (fun m _ => add_nonneg (zero_le_one.trans (hX m)) (zero_le_one.trans (hY m))) hm
  have := hX m
  have := hY m
  unfold nqFlowPhiC
  constructor <;> linarith

private theorem altQFlow_phiC_one_le {X Y : ℕ → ℝ} {k : ℕ} (hX : ∀ m, 1 ≤ X m) (hY : ∀ m, 1 ≤ Y m) :
    1 ≤ nqFlowPhiC X Y k := by
  have := (altQFlow_phiC_ge (k := k) (m := 1) hX hY (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)).1
  exact (hX 1).trans this

/-- The grid of the endpoint: `K_n = max 1 ⌈N^{C}⌉` (so `N^C ≤ K_n ≤ ⌈N^C⌉`, `K_n ≠ 0`; copy of `nqFlow_K`,
`NQEndFlow.lean:532`). -/
private def altQFlow_K (sz : Sizes d) (C : ℝ) (n : ℕ) : ℕ := max 1 ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊

private theorem altQFlow_K_ne_zero (sz : Sizes d) (C : ℝ) (n : ℕ) : altQFlow_K sz C n ≠ 0 := by
  unfold altQFlow_K
  exact Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le one_pos (le_max_left _ _))

private theorem altQFlow_K_low (sz : Sizes d) (C : ℝ) (n : ℕ) :
    ((sz.size n : ℕ) : ℝ) ^ C ≤ (altQFlow_K sz C n : ℝ) := by
  unfold altQFlow_K
  have h : ((sz.size n : ℕ) : ℝ) ^ C ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := Nat.le_ceil _
  exact h.trans (by exact_mod_cast le_max_right _ _)

private theorem altQFlow_K_up (sz : Sizes d) (C : ℝ) (n : ℕ) :
    altQFlow_K sz C n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ := by
  unfold altQFlow_K
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  exact max_le (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN _)) le_rfl

/-- `K_n + 1 ≤ N^{C+2}` eventually (`C ≥ 0`, `N ≥ 2`): `K_n ≤ ⌈N^C⌉ < N^C + 1`, `N^{C+2} = N^C N² ≥ 4 N^C ≥ N^C + 3`. -/
private theorem altQFlow_K_card (sz : Sizes d) (hsz : sz.SizeTendsto) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ n in atTop, ((altQFlow_K sz C n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (C + 2) := by
  filter_upwards [hsz.eventually_ge_atTop 2] with n hN2
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hP1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := Real.one_le_rpow hN1 hC
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C := by linarith
  have hceil : (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) < ((sz.size n : ℕ) : ℝ) ^ C + 1 :=
    Nat.ceil_lt_add_one hP0
  have hK : (altQFlow_K sz C n : ℝ) ≤ (⌈((sz.size n : ℕ) : ℝ) ^ C⌉₊ : ℝ) := by
    exact_mod_cast altQFlow_K_up sz C n
  have hsplit : ((sz.size n : ℕ) : ℝ) ^ (C + 2) = ((sz.size n : ℕ) : ℝ) ^ C * ((sz.size n : ℕ) : ℝ) ^ 2 := by
    rw [Real.rpow_add hN0, Real.rpow_two]
  have h4 : (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := by nlinarith
  push_cast
  rw [hsplit]
  nlinarith

private theorem altQFlow_meas_pathH (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) :
    Measurable (pathH sz s t K n k) :=
  Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j

private theorem altQFlow_meas_seqHflow (sz : Sizes d) (n : ℕ) (u : ℝ) : Measurable (sz.seqHflow n u) :=
  Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry sz n u i j

/-- `(𝓛 - 𝒦)^{(k)}_{u,σ,a}(H)` is measurable in the matrix `H` (as `gridGood_meas_loopFine`,
`GridGoodN.lean:266`, minus the constant `STKloop`). -/
private theorem altQFlow_meas_STLKM (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      sz.STLKM n E u H σ a :=
  (walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a).sub_const _

/-- **The transfer** (`map_pathH_eq`; copy of `nqFlow_transfer`, `NQEndFlow.lean:610`): a measurable matrix event
has the same probability on `pathP` at the grid index `j` and on `seqP` at the grid time. -/
private theorem altQFlow_transfer (sz : Sizes d) {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (j : ℕ) (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (hK : K n ≠ 0)
    {S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)} (hS : MeasurableSet S) :
    pathP sz (pathH sz s v K n j ⁻¹' S) = sz.seqP (sz.seqHflow n (gridTime s v K n j) ⁻¹' S) := by
  rw [← Measure.map_apply (altQFlow_meas_pathH sz s v K n j) hS,
    ← Measure.map_apply (altQFlow_meas_seqHflow sz n _) hS, map_pathH_eq sz s v K n j hs0 hsv hK]

/-- `1 ≤ STbootRHS lo XL XLK B k p` for `XL ≥ 1`, `XLK ≥ 0`, `B ≥ 0`, `k ≥ 1`: the sum `Σ_{m=k-1}^{k+1} XL m` contains
`XL k ≥ 1` and the other terms are nonnegative. -/
private theorem altQFlow_bootRHS_one_le {lo : ℕ} {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 1 ≤ k)
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

/-! ## §1 small facts: `STbootRHS`, the sizes, the failure-probability arithmetic -/

/-- `STbootRHS 2 ≤ STbootRHS 1` (the sum over `Icc 1 (k-1)` contains the sum over `Icc 2 (k-1)`), `XLK ≥ 0`. -/
private theorem altQFlow_bootRHS_two_le_one {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hXLK : ∀ i, 0 ≤ XLK i) :
    STbootRHS 2 XL XLK B k p ≤ STbootRHS 1 XL XLK B k p := by
  unfold STbootRHS
  have h : ∑ i ∈ Finset.Icc 2 (k - 1), XLK i ≤ ∑ i ∈ Finset.Icc 1 (k - 1), XLK i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by norm_num) le_rfl) (fun i _ _ => hXLK i)
  linarith

/-- `XLK (k-1) ≤ STbootRHS 2 XL XLK B k p` for `3 ≤ k` (the length `k - 1 ≥ 2` is in the sum over `Icc 2 (k-1)`). -/
private theorem altQFlow_Ylow_le_bootRHS {XL XLK : ℕ → ℝ} {B : ℝ} {k p : ℕ} (hk : 3 ≤ k)
    (hXL : ∀ i, 0 ≤ XL i) (hXLK : ∀ i, 0 ≤ XLK i) (hB : 0 ≤ B) :
    XLK (k - 1) ≤ STbootRHS 2 XL XLK B k p := by
  unfold STbootRHS
  have h1 : 0 ≤ B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * k - 1) ^ (1 / 2 : ℝ) *
      XL (4 * p) ^ (1 / (4 * (p : ℝ))) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hB _) (Real.rpow_nonneg (hXL _) _))
      (Real.rpow_nonneg (hXL _) _)
  have h2 : XLK (k - 1) ≤ ∑ i ∈ Finset.Icc 2 (k - 1), XLK i :=
    Finset.single_le_sum (f := XLK) (fun i _ => hXLK i) (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  have h3 : 0 ≤ ∑ i ∈ Finset.Icc (k - 1) (k + 1), XL i := Finset.sum_nonneg fun i _ => hXL i
  have h4 : 0 ≤ ∑ i ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
      XLK (k + 2 - i) * (XL (STn12 i).1 * XL (STn12 i).2) ^ (1 / 2 : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hXLK _) (Real.rpow_nonneg (mul_nonneg (hXL _) (hXL _)) _)
  linarith

/-- `W ≤ N = (W L)^d` for `d ≥ 1`. -/
private theorem altQFlow_W_le_size {d : ℕ} (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)
  have h2 : sz.W n * sz.L n ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow (by omega) _
  exact_mod_cast h1.trans h2

/-- `L^d ≤ N`. -/
private theorem altQFlow_Zd_le_size {d : ℕ} (sz : Sizes d) (n : ℕ) : (sz.L n) ^ d ≤ sz.size n := by
  rw [Sizes.size]
  exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d

/-- `#Z_L^d = L^d` (copy of the private `entryDom_card_Zd`, `Green/EntryDom.lean:730`). -/
private theorem altQFlow_card_Zd {d : ℕ} (L : ℕ) [NeZero L] : Fintype.card (Zd d L) = L ^ d := by
  simp [Zd, ZMod.card]

/-- `2 N^{-(D+c)} ≤ N^{-D}` for `N ≥ 2`, `c ≥ 1`. -/
private theorem altQFlow_two_pow_le {N D c : ℝ} (hN : 2 ≤ N) (hc : 1 ≤ c) :
    2 * N ^ (-(D + c)) ≤ N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have h : N ^ (-(D + c)) = N ^ (-D) * N ^ (-c) := by
    rw [show -(D + c) = -D + -c by ring, Real.rpow_add hN0]
  have h1 : N ^ (-c) ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h2 : N ^ (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.rpow_neg_one]
    have : (1 : ℝ) / N ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN
    simpa [one_div] using this
  have hp : 0 < N ^ (-D) := Real.rpow_pos_of_pos hN0 _
  rw [h]
  nlinarith

/-! ## §2 the projected initial loops `altQFlow_initQ` -/

/-- `H ↦ ‖(𝒬_t (𝓛-𝒦)^{(k)}_{u,σ}(H))_a‖` is measurable (`𝒬_t 𝒜 = 𝒜 - (𝒫𝒜)_{a₀} ϑ_{t,a}`, a finite sum of the
measurable entries `altQFlow_meas_STLKM`). -/
private theorem altQFlow_meas_STQop (sz : Sizes d) (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin (k + 1) → Bool)
    (ϑ : ℝ → (Fin (k + 1) → Zd d (sz.L n)) → ℂ) (t : ℝ) (a : Fin (k + 1) → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      ‖STQop (d := d) ϑ t (fun b => sz.STLKM n E u H σ b) a‖ := by
  unfold STQop STPsum
  refine Measurable.norm ?_
  refine (altQFlow_meas_STLKM sz n E u σ a).sub ?_
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ (fun b _ => altQFlow_meas_STLKM sz n E u σ b)

/-- The set of matrices with the projected initial bound at every alternating sign and label is measurable. -/
private theorem altQFlow_meas_initSet (sz : Sizes d) (n : ℕ) (E u t c : ℝ) {k : ℕ}
    (ϑ : ℝ → (Fin (k + 1) → Zd d (sz.L n)) → ℂ) :
    MeasurableSet {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)), x.1 (Fin.last k) = !x.1 0 →
        ‖STQop (d := d) ϑ t (fun b => sz.STLKM n E u M x.1 b) x.2‖ ≤ c} := by
  have e : {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ∀ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)), x.1 (Fin.last k) = !x.1 0 →
        ‖STQop (d := d) ϑ t (fun b => sz.STLKM n E u M x.1 b) x.2‖ ≤ c} =
      ⋂ x : (Fin (k + 1) → Bool) × (Fin (k + 1) → Zd d (sz.L n)),
        {M | x.1 (Fin.last k) = !x.1 0 →
          ‖STQop (d := d) ϑ t (fun b => sz.STLKM n E u M x.1 b) x.2‖ ≤ c} := by
    ext M; simp
  rw [e]
  refine MeasurableSet.iInter fun x => ?_
  by_cases hx : x.1 (Fin.last k) = !x.1 0
  · simp only [hx, true_imp_iff]
    exact measurableSet_le (altQFlow_meas_STQop sz n E u x.1 ϑ t x.2) measurable_const
  · have hu : {M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        x.1 (Fin.last k) = !x.1 0 →
          ‖STQop (d := d) ϑ t (fun b => sz.STLKM n E u M x.1 b) x.2‖ ≤ c} = Set.univ := by
      ext M; simp [hx]
    rw [hu]
    exact MeasurableSet.univ

/-- **The projected initial loops** (`3_5:1676-1690`, the "start term" of the alternating case; the first row of the
S3-18b1 part of the T2302 G3 table): for every `ε > 0`, with high probability the projected initial loops
`𝒬_s (𝓛-𝒦)^{(m+2)}_{s,σ}` of every alternating sign `σ` are at most `N^ε B_s^{m+2}`.  Proof: `startLevelQN` (`QLevelsA.lean:421`)
per matrix, at `u = s_n`, `X ≡ 1`, `ν = N^{e/8}`, `τ_N = e/2`, `e = min ε 1`, with the inputs `hY` (`STLK s` at length `m+1`),
`hYtop` (`STLK s` at length `m+2`) and `hF` (`stDecayLoopU_of_step2` at the far labels, window `ωf = W^{e/(8dm)}`, decay
`D_F = (2m+5)/𝔠`).  The ticket's split `τ_N = ε₁/8` fails `hMΛ` (the constant `c₀ ν²` exceeds `N^{τ_N}`); `τ_N = e/2` closes
eventually (paper-delta candidate `T2310b`). -/
private theorem altQFlow_initQ (sz : Sizes d) (hd : 3 ≤ d) {E s t : ℕ → ℝ} {κ' 𝔠 𝔡 τR : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠) (hWO : sz.WO 𝔡)
    (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1)
    (hrange : sz.RangeCond τR t) (hτR : 0 < τR) (hLK : STLK sz E s) (hDecay : STDecayLoopU sz E s t)
    {m : ℕ} (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    HighProbAt (seqP sz) sz.size (fun n => {ω | ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
      x.1 (Fin.last (m + 1)) = !x.1 0 →
        ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
          (fun b => sz.STLKM n (E n) (s n) (sz.seqHflow n (s n) ω) x.1 b) x.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (sz.Bctl n (s n)) ^ (m + 1 + 1)}) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hsz := tendsto_size sz hsize
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = min ε 1 := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact lt_min hε one_pos
  have he1 : e ≤ 1 := by rw [he]; exact min_le_right _ _
  have heε : e ≤ ε := by rw [he]; exact min_le_left _ _
  have hdm : (0 : ℝ) < ((d * m : ℕ) : ℝ) := by
    have : 0 < d * m := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  obtain ⟨τ'', hτ''⟩ : ∃ τ'' : ℝ, τ'' = e / (8 * ((d * m : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hτ''0 : 0 < τ'' := by rw [hτ'']; positivity
  obtain ⟨DF, hDF⟩ : ∃ DF : ℝ, DF = (2 * (m : ℝ) + 5) / 𝔠 := ⟨_, rfl⟩
  have hDF0 : 0 < DF := by rw [hDF]; positivity
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
      c₀ = (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ') * C) := ⟨_, rfl⟩
  have hA1 := Prec.whp sz (hLK (m + 1) (by omega)) (τ := e / 8) (by positivity)
  have hA2 := Prec.whp sz (hLK (m + 1 + 1) (by omega)) (τ := e / 8) (by positivity)
  have hA3 := Prec.whp sz (hDecay (m + 1) (by omega) τ'' hτ''0 DF hDF0) (τ := 1) one_pos
  refine HighProbAt.mono (HighProbAt.inter hsz (HighProbAt.inter hsz hA1 hA2) hA3) ?_
  have hc₀ev : ∀ᶠ n in atTop, c₀ ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 4) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < e / 4)).comp hsize).eventually_ge_atTop c₀
  have h2ev : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < e / 2)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hWO, hband, hrange, hc₀ev, h2ev] with n hwo hbd hrg hc hN2
  rintro ω ⟨⟨hY1, hYtop'⟩, hFar⟩ x hx
  -- the scalar facts at the size index `n`
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN := altQFlow_W_le_size sz hd1 n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hwo.1
  have hu1 : s n < 1 := (hst n).trans_lt (ht1 n)
  have hBs : 0 < sz.Bctl n (s n) := st_Bctl_pos sz hu1
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - s n := by
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τR) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    rw [Real.rpow_neg_one] at h1
    linarith [hst n]
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = ((sz.size n : ℕ) : ℝ) ^ (e / 8) := ⟨_, rfl⟩
  have hν1 : 1 ≤ ν := by rw [hν]; exact Real.one_le_rpow hN1 (by positivity)
  have hνN : ν ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hν]
    calc ((sz.size n : ℕ) : ℝ) ^ (e / 8) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = _ := Real.rpow_one _
  have hν2 : ν ^ 2 = ((sz.size n : ℕ) : ℝ) ^ (e / 4) := by
    rw [hν, sq, ← Real.rpow_add hN0]; congr 1; ring
  -- the window `ωf = W^{τ''}`
  obtain ⟨ωf, hωfdef⟩ : ∃ ωf : ℝ, ωf = ((sz.W n : ℕ) : ℝ) ^ τ'' := ⟨_, rfl⟩
  have hωf : 1 ≤ ωf := by rw [hωfdef]; exact Real.one_le_rpow hW1 hτ''0.le
  have hωd : ωf ^ (d * m) ≤ ν := by
    have e1 : ωf ^ (d * m) = ((sz.W n : ℕ) : ℝ) ^ (e / 8) := by
      rw [hωfdef, ← Real.rpow_natCast, ← Real.rpow_mul hW0.le, hτ'']
      congr 1; field_simp
    rw [e1, hν]
    exact Real.rpow_le_rpow hW0.le hWN (by positivity)
  -- the far decay level
  obtain ⟨Fv, hFvdef⟩ : ∃ Fv : ℝ, Fv = ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-DF) := ⟨_, rfl⟩
  have hFv0 : 0 ≤ Fv := by rw [hFvdef]; positivity
  have hFv : Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
    have hWD : ((sz.size n : ℕ) : ℝ) ^ (2 * m + 5) ≤ ((sz.W n : ℕ) : ℝ) ^ DF := by
      calc ((sz.size n : ℕ) : ℝ) ^ (2 * m + 5) = (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ DF := by
            rw [← Real.rpow_mul hN0.le, show 𝔠 * DF = ((2 * m + 5 : ℕ) : ℝ) by
              rw [hDF]; push_cast; field_simp, Real.rpow_natCast]
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ DF := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hbd hDF0.le
    have hWneg : ((sz.W n : ℕ) : ℝ) ^ (-DF) ≤ (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ := by
      rw [Real.rpow_neg hW0.le]
      exact inv_anti₀ (by positivity) hWD
    have h1 : ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ =
        (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ := by
      rw [show 2 * m + 5 = (2 * m + 4) + 1 by ring, pow_succ]
      field_simp
    have h2 : (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ :=
      le_mul_of_one_le_left (by positivity) hν1
    rw [hFvdef]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-DF)
        ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 5))⁻¹ :=
          mul_le_mul_of_nonneg_left hWneg hN0.le
      _ = _ := h1
      _ ≤ _ := h2
  -- `hMΛ`
  have hMΛ : (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ') * C * ν ^ 2) ≤
      ((sz.size n : ℕ) : ℝ) ^ (e / 2) := by
    have hsq : ((sz.size n : ℕ) : ℝ) ^ (e / 2) = ((sz.size n : ℕ) : ℝ) ^ (e / 4) * ((sz.size n : ℕ) : ℝ) ^ (e / 4) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have hp : 0 ≤ ν ^ 2 := by positivity
    calc (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ') * C * ν ^ 2)
        = c₀ * ν ^ 2 := by rw [hc₀]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 4) * ν ^ 2 := mul_le_mul_of_nonneg_right hc hp
      _ = _ := by rw [hsq, hν2]
  -- the levels read off the three events
  obtain ⟨H, hH⟩ : ∃ H, H = sz.seqHflow n (s n) ω := ⟨_, rfl⟩
  have hHherm : H.IsHermitian := by rw [hH]; exact Sizes.seqHflow_isHermitian sz n (s n) ω
  have hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n (E n) (s n) H σ' a'‖ ≤ ν * 1 * sz.Bctl n (s n) ^ (m + 1) := by
    intro σ' a'
    have h : ‖Lloop sz n (E n) (s n) σ' a' ω - STKloop sz n (E n) (s n) σ' a'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (e / 8) * sz.Bctl n (s n) ^ (m + 1) := hY1 (σ', a')
    rw [hH, mul_one, hν]
    exact h
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) (s n) * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n (E n) (s n) H σ' a'‖ ≤ Fv := by
    intro σ' a' hfar
    have h : (‖Lloop sz n (E n) (s n) σ' a' ω‖ + ‖Lloop sz n (E n) (s n) σ' a' ω - STKloop sz n (E n) (s n) σ' a'‖) *
        (if ellT (sz.L n) (sz.lam n) (s n) * ((sz.W n : ℕ) : ℝ) ^ τ'' ≤ (STdiamInf a' : ℝ) then 1 else 0) ≤
        ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-DF) := hFar (⟨s n, le_rfl, hst n⟩, σ', a')
    rw [← hωfdef] at h
    simp only [hfar, ↓reduceIte, mul_one, Real.rpow_one] at h
    rw [hH, hFvdef]
    exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h
  have hYtop : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖sz.STLKM n (E n) (s n) H x.1 b‖ ≤ ν * sz.Bctl n (s n) ^ (m + 1 + 1) := by
    intro b
    have h : ‖Lloop sz n (E n) (s n) x.1 b ω - STKloop sz n (E n) (s n) x.1 b‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (e / 8) * sz.Bctl n (s n) ^ (m + 1 + 1) := hYtop' (x.1, b)
    rw [hH, hν]
    exact h
  -- the mollifier bound
  have hϑ : STMollifierProps (d := d) (sz.lam n) C (1 / 2)
      (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) := by
    rw [hC]; exact QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam
  have hexp : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n) (s n) a‖ ≤
        C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine (hϑ.2.1 (s n) (hs0 n) hu1 a).trans ?_
    have hl : 0 < ellT (sz.L n) (sz.lam n) (s n) := ellT_pos (by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hex : Real.exp (-(1 / 2 : ℝ) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ)) / ellT (sz.L n) (sz.lam n) (s n)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hS]) hl.le
    have hC1 : 0 ≤ C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) := by positivity
    calc _ ≤ C * (((ellT (sz.L n) (sz.lam n) (s n) ^ d)⁻¹) ^ (m + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hex hC1
      _ = _ := by rw [mul_one]
  have key := startLevelQN d (by omega) sz n (E n) (s n) κ' hκ (hE n) (hs0 n) hu1 hlam hNu H hHherm m
    (2 / Real.sqrt κ') ν 1 ωf Fv C (e / 2) (ν * sz.Bctl n (s n) ^ (m + 2)) rfl hν1 le_rfl hωf hωd hνN hFv hFv0
    hC0.le hMΛ hY hF _ hexp x.1 hx hYtop x.2
  rw [hH] at key
  -- `ν + N^{e/2} ≤ N^ε`
  have hsq : ((sz.size n : ℕ) : ℝ) ^ e = ((sz.size n : ℕ) : ℝ) ^ (e / 2) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ he0).symm
  have hle1 : ν ≤ ((sz.size n : ℕ) : ℝ) ^ (e / 2) := by
    rw [hν]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hle2 : ((sz.size n : ℕ) : ℝ) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hN1 heε
  have hsum : ν + ((sz.size n : ℕ) : ℝ) ^ (e / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ ε := by
    have : (2 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ (e / 2) * ((sz.size n : ℕ) : ℝ) ^ (e / 2) :=
      mul_le_mul_of_nonneg_right hN2 (Real.rpow_nonneg hN0.le _)
    linarith
  have hBp : 0 ≤ sz.Bctl n (s n) ^ (m + 2) := (pow_pos hBs _).le
  calc _ ≤ ν * sz.Bctl n (s n) ^ (m + 2) + ((sz.size n : ℕ) : ℝ) ^ (e / 2) * (sz.Bctl n (s n) ^ (m + 2) * 1) := key
    _ = (ν + ((sz.size n : ℕ) : ℝ) ^ (e / 2)) * sz.Bctl n (s n) ^ (m + 2) := by ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ ε * sz.Bctl n (s n) ^ (m + 1 + 1) :=
        mul_le_mul_of_nonneg_right hsum hBp

/-! ## §3 the alternating endpoint at one non-collapsed section -/

/-- The union bound for two events of probability at most `x` each. -/
private theorem altQFlow_union2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {S A B : Set Ω} {x y : ℝ}
    (hx : 0 ≤ x) (hA : μ A ≤ ENNReal.ofReal x) (hB : μ B ≤ ENNReal.ofReal x) (hS : S ⊆ A ∪ B)
    (hxy : 2 * x ≤ y) : μ S ≤ ENNReal.ofReal y := by
  refine (measure_mono hS).trans ?_
  calc μ (A ∪ B) ≤ μ A + μ B := measure_union_le _ _
    _ ≤ ENNReal.ofReal x + ENNReal.ofReal x := add_le_add hA hB
    _ = ENNReal.ofReal (x + x) := (ENNReal.ofReal_add hx hx).symm
    _ ≤ ENNReal.ofReal y := ENNReal.ofReal_le_ofReal (by linarith)

/-- **The alternating endpoint at one non-collapsed section** (`s_n < v_n ≤ t_n`; the shape of `nqFlow_core`,
`NQEndFlow.lean:642`, with `altGridEndQN`, `QEndGrid.lean:1326`, in place of `nqGridEndLinN`): for deterministic controls
`X i n`, `Y i n ≥ 1` with `Ξ̂^{(𝓛)}_{w,i} ≺ X i` (`STlenL (m+2) p i`) and `Ξ̂^{(𝓛-𝒦)}_{w,i} ≺ Y i` (`i ≤ m+2`, the current length
included) uniformly in `w ∈ [s_n, v_n]`, the alternating `(𝓛-𝒦)^{(m+2)}_{v,σ,a}/B_v^{m+2}` (`σ_{last} = ¬σ_0`), uniformly in `(σ, a)`,
is `≺ B_v^{1/6} Y (m+2) + STbootRHS 2 X Y B_s (m+2) p`.  The failure event is inside the union of `(W_n)ᶜ`, the walk leaving
`GoodSetN ∩ GoodLinN ∩ altYSetN` or the projected initial bound failing (`altQFlow_initQ`), of probability `≤ N^{-(D+2)}`
(`HighProbAt.inter` at `D + 2`), and the exceptional event `Gᶜ` of `altGridEndQN` at `ε₀ = τ/2`, `D₁ = D + 2`; outside it
`altGridEndQN` bounds the terminal loop by `N^{τ/2}(Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃ + X) B_v^{m+2}` with `X = Y (m+1)`, and
`Λ_s^{1/2} + Φ₁ + Φ₂ + Φ₃ ≤ ζ`, `Y (m+1) ≤ ζ` (`m + 1 ≥ 2`), so the bracket is at most `2ζ` and
`N^{τ/2} · 2ζ ≤ N^{τ/2} N^{τ/2} ζ = N^τ ζ` (`N^{τ/2} ≥ 2` eventually). -/
private theorem altQFlow_core (sz : Sizes d) {E s t v : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hsv : ∀ n, s n < v n) (hvt : ∀ n, v n ≤ t n) (hLK : STLK sz E s) (hDecay : STDecayLoopU sz E s t)
    (hGrid : GridGoodNConcl sz E s v) (hLin : NQLinConcl sz E s t) {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p)
    {X Y : ℕ → ℕ → ℝ} (hX1 : ∀ i n, 1 ≤ X i n) (hY1 : ∀ i n, 1 ≤ Y i n)
    (hX : ∀ i : ℕ, 1 ≤ i → STlenL (m + 1 + 1) p i →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => X i n))
    (hY : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => Y i n)) :
    StochDomAt sz.seqP sz.size
      (fun n (x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} ×
          (Fin (m + 1 + 1) → Zd d (sz.L n))) ω =>
        ‖Lloop sz n (E n) (v n) x.1.1 x.2 ω - STKloop sz n (E n) (v n) x.1.1 x.2‖ /
          (sz.Bctl n (v n)) ^ (m + 1 + 1))
      (fun n _ _ => (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n +
        STbootRHS 2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p) := by
  intro τ hτ D hD
  have hsz := tendsto_size sz hsize
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have hBv : ∀ n, 0 < sz.Bctl n (v n) := fun n => st_Bctl_pos sz (hv1 n)
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hsv n).le.trans_lt (hv1 n))
  -- the levels
  set Λ : ℕ → ℝ := fun n => max 1 (nqFlowLam (fun i => X i n) (sz.Bctl n (s n)) (m + 1 + 1) p) with hΛdef
  set Φ₁ : ℕ → ℝ := fun n => nqLinPhi1 (fun i => Y i n) (m + 1 + 1) with hΦ₁def
  set Φ₂ : ℕ → ℝ := fun n =>
    nqLinPhi2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (v n)) (m + 1 + 1) (Y (m + 1 + 1) n) with hΦ₂def
  set Φ₃ : ℕ → ℝ := fun n => nqLinPhi3 (fun i => X i n) (m + 1 + 1) with hΦ₃def
  set Φc : ℕ → ℝ := fun n => nqFlowPhiC (fun i => X i n) (fun i => Y i n) (m + 1 + 1) with hΦcdef
  set Xl : ℕ → ℝ := fun n => Y (m + 1) n with hXldef
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => le_max_left _ _
  have hΛ0 : ∀ n, 0 ≤ Λ n := fun n => zero_le_one.trans (hΛ1 n)
  have hΦ : ∀ n, 0 ≤ Φ₁ n ∧ 0 ≤ Φ₂ n ∧ 0 ≤ Φ₃ n := fun n =>
    altQFlow_phi_nonneg (fun i => hX1 i n) (fun i => hY1 i n) (hBv n).le
  have hΦc1 : ∀ n, 1 ≤ Φc n := fun n => altQFlow_phiC_one_le (fun i => hX1 i n) (fun i => hY1 i n)
  have hXl1 : ∀ n, 1 ≤ Xl n := fun n => hY1 _ n
  -- the endpoint of the grid walk at `ε₀ = τ/2`, `D₁ = D + 2`
  obtain ⟨ε₁, τ', D', C_K, hε₁, hτ', hD', hCK, hend⟩ := altGridEndQN sz κ' 𝔠 τR 𝔡 E s t hd hκ h𝔠 hτR h𝔡
    hsize hband hWO hE hs0 hst ht1 hcase hrange hWt m hm Λ Φ₁ Φ₂ Φ₃ Xl hΛ0 (Eventually.of_forall hΛ1)
    (fun n => (hΦ n).1) (fun n => (hΦ n).2.1) (fun n => (hΦ n).2.2) hXl1 v (fun n => (hsv n).le) hvt
    (τ / 2) (half_pos hτ) (D + 2) (by linarith)
  -- the grid
  set K : ℕ → ℕ := altQFlow_K sz C_K with hKdef
  have hK0 : ∀ n, K n ≠ 0 := altQFlow_K_ne_zero sz C_K
  have hKcard := altQFlow_K_card sz hsize hCK
  have hpin := hend Φc K hK0 (Eventually.of_forall (altQFlow_K_low sz C_K))
    (Eventually.of_forall (altQFlow_K_up sz C_K))
  -- the hypotheses of the good-event lemma on `[s, v]` at the crude level `Φc` and the level `Λ_s`
  have hXg : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => Φc n) :=
    fun i hi hi' => altQFlow_prec_of_le_right (hX i hi (Or.inl hi')) fun n u ω =>
      (altQFlow_phiC_ge (fun i => hX1 i n) (fun i => hY1 i n) (Finset.mem_Icc.2 ⟨hi, hi'⟩)).1
  have hYg : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => Φc n) :=
    fun i hi hi' => altQFlow_prec_of_le_right (hY i hi hi') fun n u ω =>
      (altQFlow_phiC_ge (fun i => hX1 i n) (fun i => hY1 i n) (Finset.mem_Icc.2 ⟨hi, by omega⟩)).2
  have hQ : Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiL sz n (E n) (u : ℝ) (2 * (m + 1 + 1) - 1) ω *
        (STXiL sz n (E n) (u : ℝ) (4 * p) ω / sz.Bctl n (u : ℝ)) ^ (1 / (2 * (p : ℝ))))
      (fun n _ _ => Λ n) :=
    altQFlow_hQ sz hsize (fun n => (hsv n).le) hv1 (a := 2 * (m + 1 + 1) - 1) (b := 4 * p) hp
      (Xa := fun n => X (2 * (m + 1 + 1) - 1) n) (Xb := fun n => X (4 * p) n)
      (fun n => zero_le_one.trans (hX1 _ n)) (fun n => zero_le_one.trans (hX1 _ n))
      (hX (2 * (m + 1 + 1) - 1) (by omega) (Or.inr (Or.inl rfl))) (hX (4 * p) (by omega) (Or.inr (Or.inr rfl)))
  have hgood := hGrid v (fun n => (hsv n).le) (fun n => le_rfl) K hK0 (m + 1 + 1) (by omega) Λ Φc hΛ1 hΦc1 hXg hYg
    p hp hQ (C_K + 2) hKcard ε₁ hε₁ τ' hτ' D' hD'
  have hlin := hLin v (fun n => (hsv n).le) hvt K hK0 (m + 1 + 1) (by omega) X Y hX1 hY1
    (fun i hi hi' => hX i hi (Or.inl hi')) hY (C_K + 2) hKcard ε₁ hε₁
  have hyg := altYGridN sz E s v K (m + 1) Xl hs0 (fun n => (hsv n).le) hv1 hK0 hXl1
    (hY (m + 1) (by omega) (by omega)) (C_K + 2) hKcard ε₁ hε₁
  have hinit := altQFlow_initQ sz hd hκ h𝔠 hsize hband hWO hE hs0 hst ht1 hrange hτR hLK hDecay hm hε₁
  -- the initial event on the path space at the grid index `0` (the transfer `map_pathH_eq`)
  let initGood : ∀ n, Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) := fun n =>
    {M | ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
      x.1 (Fin.last (m + 1)) = !x.1 0 →
        ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
          (fun b => sz.STLKM n (E n) (s n) M x.1 b) x.2‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)}
  have hinitP : HighProbAt (pathP sz) sz.size (fun n => pathH sz s v K n 0 ⁻¹' initGood n) := by
    intro D'' hD''
    filter_upwards [hinit D'' hD''] with n hn
    have hS : MeasurableSet (initGood n) :=
      altQFlow_meas_initSet sz n (E n) (s n) (s n)
        (((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1))
        (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n))
    have htr := altQFlow_transfer sz (s := s) (v := v) (K := K) (n := n) 0 (hs0 n) (hsv n).le (hK0 n) hS.compl
    rw [ST_gridTime_zero] at htr
    rw [← Set.preimage_compl, htr, Set.preimage_compl]
    exact hn
  have hW := HighProbAt.inter hsz (HighProbAt.inter hsz (HighProbAt.inter hsz hgood hlin) hyg) hinitP
  have h2ev : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop 2
  filter_upwards [hpin, hW (D + 2) (by linarith), hsize.eventually_ge_atTop 2, h2ev] with n hG hWn hN2 hhalf
  obtain ⟨G, hGP, hGb⟩ := hG
  have hNn1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 2)) := Real.rpow_nonneg (by linarith) _
  obtain ⟨ζ₂, hζ₂⟩ : ∃ ζ₂ : ℝ, ζ₂ = (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n +
      STbootRHS 2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p := ⟨_, rfl⟩
  -- the terminal event
  set Sterm : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {M | ∃ x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ <
        ‖sz.STLKM n (E n) (v n) M x.1.1 x.2‖ / (sz.Bctl n (v n)) ^ (m + 1 + 1)} with hStermdef
  have hSterm : MeasurableSet Sterm := by
    have heq : Sterm = ⋃ x : {σ : Fin (m + 1 + 1) → Bool // σ (Fin.last (m + 1)) = !σ 0} ×
        (Fin (m + 1 + 1) → Zd d (sz.L n)),
        {M | ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ <
          ‖sz.STLKM n (E n) (v n) M x.1.1 x.2‖ / (sz.Bctl n (v n)) ^ (m + 1 + 1)} := by
      ext M; simp [hStermdef]
    rw [heq]
    exact MeasurableSet.iUnion fun x =>
      measurableSet_lt measurable_const
        ((altQFlow_meas_STLKM sz n (E n) (v n) x.1.1 x.2).norm.div_const _)
  have e1 : sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := by
    have := altQFlow_transfer sz (s := s) (v := v) (K := K) (n := n) (K n) (hs0 n) (hsv n).le (hK0 n) hSterm
    rw [gridTime_last s v K n (hK0 n)] at this
    exact this.symm
  have hmain : pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
    refine altQFlow_union2 (B := Gᶜ) hx0 hWn ?_ ?_ (altQFlow_two_pow_le hN2 (by norm_num))
    · rw [← ofReal_measureReal (measure_ne_top (pathP sz) _)]
      exact ENNReal.ofReal_le_ofReal hGP
    · intro ω hω
      by_contra hno
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or,
        not_not] at hno
      obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hI⟩, hGω⟩ := hno
      obtain ⟨x, hx⟩ := hω
      have hb := hGb ω hGω (fun j hj => ⟨⟨hA j hj, hB j hj⟩, hC j hj⟩) (fun σ hσ a => hI (σ, a) hσ)
        x.1.1 x.1.2 x.2
      have hlev : Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n ≤ ζ₂ := by
        rw [hζ₂]
        exact altQFlow_level_le (by omega) hp (fun i => hX1 i n) (fun i => hY1 i n) (hBs n)
      have hXl : Xl n ≤ STbootRHS 2 (fun i => X i n) (fun i => Y i n) (sz.Bctl n (s n)) (m + 1 + 1) p :=
        altQFlow_Ylow_le_bootRHS (XL := fun i => X i n) (XLK := fun i => Y i n) (B := sz.Bctl n (s n))
          (k := m + 1 + 1) (p := p) (by omega) (fun i => zero_le_one.trans (hX1 i n))
          (fun i => zero_le_one.trans (hY1 i n)) (hBs n).le
      have hBY : 0 ≤ (sz.Bctl n (v n)) ^ (1 / 6 : ℝ) * Y (m + 1 + 1) n :=
        mul_nonneg (Real.rpow_nonneg (hBv n).le _) (zero_le_one.trans (hY1 _ n))
      have hXlζ : Xl n ≤ ζ₂ := by rw [hζ₂]; linarith
      have hL0 : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have h1 := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have h2 := hΦ n
        linarith [h2.1, h2.2.1, h2.2.2]
      have hζ0 : 0 ≤ ζ₂ := hL0.trans hlev
      have hBk : 0 < (sz.Bctl n (v n)) ^ (m + 1 + 1) := pow_pos (hBv n) _
      have hdiv : ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) x.1.1 x.2‖ /
          (sz.Bctl n (v n)) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n) := (div_le_iff₀ hBk).2 hb
      have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
      have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
      have hfin : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
          (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n) ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ := by
        have h2z : 2 * ζ₂ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ := mul_le_mul_of_nonneg_right hhalf hζ0
        calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + Xl n)
            ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (2 * ζ₂) :=
              mul_le_mul_of_nonneg_left (by linarith) hpos
          _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂) :=
              mul_le_mul_of_nonneg_left h2z hpos
          _ = _ := by rw [hsq]; ring
      exact absurd hx (not_lt.2 (hdiv.trans hfin))
  calc sz.seqP (badSetAt sz.size _ _ τ n) = sz.seqP (sz.seqHflow n (v n) ⁻¹' Sterm) := by
        congr 1
        ext ω
        simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_preimage, hStermdef, hζ₂]
        rfl
    _ = pathP sz (pathH sz s v K n (K n) ⁻¹' Sterm) := e1
    _ ≤ _ := hmain

/-! ## §4 the non-alternating half (the merged per-time pin `stOeqNQPT''_holds`) and the collapsed section -/

/-- **The non-alternating half at a section time, uniformly in the signs and labels.**  The merged per-time pin
`STNQConclPT''` (`NQEndFlow.lean:107`) on the window `[s, uu]` with the controls frozen at `uu_n`
(`XL i n x := XL i n (uu n)`, so the pair hypotheses restrict along `(w, x) ↦ (w, uu_n)`) is `PrecPT` over
`TimeIcc s uu × {σ non-alternating} × labels`; at the time `w_n ∈ [s_n, uu_n]` it is a `PerTimeDomAt` over
`{σ} × labels`, and `stochDomAt_of_perTimeDomAt` (`StochDomAt.lean:249`, `#(σ, a) ≤ 2^{n_} (L^d)^{n_} ≤ N^{2n_}`) moves the
union over `(σ, a)` inside `P`. -/
private theorem altQFlow_nq_half (sz : Sizes d) (hsize : sz.SizeTendsto) {E s t uu w : ℕ → ℝ} {n_ p : ℕ}
    (hn : 2 ≤ n_) (hp : 1 ≤ p) {XL XLK : ℕ → ℕ → ℝ → ℝ} (hXL : ∀ i n u, 1 ≤ XL i n u)
    (hXLK : ∀ i n u, 1 ≤ XLK i n u)
    (hXLp : ∀ i, 1 ≤ i → STlenL n_ p i →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 i ω) (fun n q _ => XL i n q.1.2))
    (hXLKp : ∀ i, 1 ≤ i → i ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 i ω) (fun n q _ => XLK i n q.1.2))
    (hsw : ∀ n, s n ≤ w n) (hwu : ∀ n, w n ≤ uu n) (hut : ∀ n, uu n ≤ t n)
    (hNQ : STNQConclPT'' sz E s uu) :
    Prec sz (U := fun n => {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n)))
      (fun n x ω => ‖Lloop sz n (E n) (w n) x.1.1 x.2 ω - STKloop sz n (E n) (w n) x.1.1 x.2‖ /
        (sz.Bctl n (w n)) ^ n_)
      (fun n _ _ => (sz.Bctl n (w n)) ^ (1 / 6 : ℝ) * XLK n_ n (uu n) +
        STbootRHS 2 (fun i => XL i n (uu n)) (fun i => XLK i n (uu n)) (sz.Bctl n (s n)) n_ p) := by
  have hX' : ∀ i, 1 ≤ i → STlenL n_ p i →
      Prec sz (U := STPair s uu) (fun n q ω => STXiL sz n (E n) q.1.1 i ω) (fun n q _ => XL i n (uu n)) :=
    fun i hi hl => StochDomAt.precomp_param (V := STPair s uu) (hXLp i hi hl)
      (fun n q => ⟨(q.1.1, uu n), q.2.1, q.2.2.1.trans q.2.2.2, hut n⟩)
  have hY' : ∀ i, 1 ≤ i → i ≤ n_ →
      Prec sz (U := STPair s uu) (fun n q ω => STXiLK sz n (E n) q.1.1 i ω) (fun n q _ => XLK i n (uu n)) :=
    fun i hi hl => StochDomAt.precomp_param (V := STPair s uu) (hXLKp i hi hl)
      (fun n q => ⟨(q.1.1, uu n), q.2.1, q.2.2.1.trans q.2.2.2, hut n⟩)
  have h := hNQ n_ p hn hp (fun i n _ => XL i n (uu n)) (fun i n _ => XLK i n (uu n))
    (fun i n _ => hXL i n _) (fun i n _ => hXLK i n _) hX' hY'
  have hper : Path.PerTimeDomAt (seqP sz) sz.size
      (U := fun n => {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} × (Fin n_ → Zd d (sz.L n)))
      (fun n x ω => ‖Lloop sz n (E n) (w n) x.1.1 x.2 ω - STKloop sz n (E n) (w n) x.1.1 x.2‖ /
        (sz.Bctl n (w n)) ^ n_)
      (fun n _ _ => (sz.Bctl n (w n)) ^ (1 / 6 : ℝ) * XLK n_ n (uu n) +
        STbootRHS 2 (fun i => XL i n (uu n)) (fun i => XLK i n (uu n)) (sz.Bctl n (s n)) n_ p) := by
    intro τ hτ D hD
    filter_upwards [h τ hτ D hD] with n hn' x
    exact hn' (⟨(w n), hsw n, hwu n⟩, x.1, x.2)
  refine Path.stochDomAt_of_perTimeDomAt (seqP sz) sz.size (C := ((2 * n_ : ℕ) : ℝ)) (by positivity) ?_ hper
  filter_upwards [hsize.eventually_ge_atTop 2] with n hN2
  have hN2' : 2 ≤ sz.size n := by exact_mod_cast hN2
  have h1 : Fintype.card {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ≤ 2 ^ n_ := by
    calc _ ≤ Fintype.card (Fin n_ → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ n_ := by simp
  have h2 : Fintype.card (Fin n_ → Zd d (sz.L n)) = ((sz.L n) ^ d) ^ n_ := by
    rw [Fintype.card_fun, altQFlow_card_Zd, Fintype.card_fin]
  have h3 : 2 ^ n_ ≤ (sz.size n) ^ n_ := Nat.pow_le_pow_left hN2' n_
  have h4 : ((sz.L n) ^ d) ^ n_ ≤ (sz.size n) ^ n_ := Nat.pow_le_pow_left (altQFlow_Zd_le_size sz n) n_
  rw [Real.rpow_natCast, Fintype.card_prod, h2]
  have h5 : Fintype.card {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} * ((sz.L n) ^ d) ^ n_ ≤
      (sz.size n) ^ (2 * n_) := by
    calc _ ≤ 2 ^ n_ * ((sz.L n) ^ d) ^ n_ := Nat.mul_le_mul_right _ h1
      _ ≤ (sz.size n) ^ n_ * (sz.size n) ^ n_ := Nat.mul_le_mul h3 h4
      _ = (sz.size n) ^ (2 * n_) := by rw [← pow_add]; congr 1; ring
  exact_mod_cast h5

/-- **The collapsed section** `w_n = s_n`: `STLK s` at the length `k` gives
`‖(𝓛-𝒦)^{(k)}_{s,σ,a}‖ / B_s^k ≺ 1`, uniformly in `(σ, a)`. -/
private theorem altQFlow_collapsed (sz : Sizes d) {E s : ℕ → ℝ} (hLK : STLK sz E s) {k : ℕ} (hk : 1 ≤ k)
    (hBs : ∀ n, 0 < sz.Bctl n (s n)) :
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n x ω => ‖Lloop sz n (E n) (s n) x.1 x.2 ω - STKloop sz n (E n) (s n) x.1 x.2‖ /
        (sz.Bctl n (s n)) ^ k)
      (fun n _ _ => (1 : ℝ)) := by
  refine StochDomAt.of_subset (hLK k hk) fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨x, hx⟩ := hω
  refine ⟨x, ?_⟩
  have hBk : 0 < (sz.Bctl n (s n)) ^ k := pow_pos (hBs n) _
  have h := (lt_div_iff₀ hBk).1 hx
  simpa using h

/-! ## §5 the endpoint at an arbitrary pair `(w_n, u_n)` -/

/-- `Ξ̂^{(𝓛-𝒦)}_{v,k} ≤ 1 + x` as soon as every entry `‖(𝓛-𝒦)^{(k)}_{v,σ,a}‖ / B_v^k` is at most `x`. -/
private theorem altQFlow_xi_le {sz : Sizes d} {n : ℕ} {E v : ℝ} {k : ℕ} (hB : 0 < sz.Bctl n v) {ω : sz.SeqΩ}
    {x : ℝ}
    (h : ∀ p' : (Fin k → Bool) × (Fin k → Zd d (sz.L n)),
      ‖Lloop sz n E v p'.1 p'.2 ω - STKloop sz n E v p'.1 p'.2‖ / (sz.Bctl n v) ^ k ≤ x) :
    STXiLK sz n E v k ω ≤ 1 + x := by
  unfold STXiLK STmaxLK
  have hBk : 0 < (sz.Bctl n v) ^ k := pow_pos hB k
  have h1 : (Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
      (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
        ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖)) / (sz.Bctl n v) ^ k ≤ x := by
    rw [div_le_iff₀ hBk]
    exact Finset.sup'_le _ _ fun p' _ => (div_le_iff₀ hBk).1 (h p')
  linarith

/-- **The endpoint at an arbitrary pair** `q n = ((w_n, u_n), _)` of the parameter set `STPair s t` of `STXiRoundPT'`
(`perTimeDomAt_iff_forall_section`): `Ξ̂^{(𝓛-𝒦)}_{w_n, m+2} ≺ B_{u_n}^{1/6} XLK (m+2) u_n + STbootRHS 1 … B_s (m+2) p`.
Where `s_n < w_n` the window is `[s, v]` with `v_n = w_n` and the controls are frozen at `uu_n = u_n` (the pair hypotheses
restrict along `w ↦ (w, uu_n)`); where `w_n = s_n` (collapsed) the window is the dummy `[s, t]`, `uu_n = t_n`, and the
section is bounded by `STLK s` (`altQFlow_collapsed`).  At a non-collapsed `n` the failure event is inside the union of the
alternating part (`altQFlow_core`: `altGridEndQN`) and the non-alternating part (`altQFlow_nq_half`: the merged per-time pin
`stOeqNQPT''_holds`); every sign is one of the two (`σ_{last} = ¬σ_0` or `σ_{last} = σ_{finRotate last} = σ_0`), the maximum over
`(σ, a)` is at most the common bound `N^{τ/2} ζ_A`, and `1 + N^{τ/2} ζ_A ≤ 2 N^{τ/2} ζ_A ≤ N^τ ζ_A ≤ N^τ ζ`
(`ζ_A ≤ ζ`: `B_w ≤ B_u`, `STbootRHS 2 ≤ STbootRHS 1`). -/
private theorem altQFlow_section (sz : Sizes d) {E s t : ℕ → ℝ} (hd : 3 ≤ d) {κ' 𝔠 τR 𝔡 : ℝ} (hκ : 0 < κ')
    (h𝔠 : 0 < 𝔠) (hτR : 0 < τR) (h𝔡 : 0 < 𝔡) (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hWO : sz.WO 𝔡) (hE : ∀ n, |E n| ≤ 2 - κ') (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseI s t) (hrange : sz.RangeCond τR t)
    (hWt : ∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n))
    (hLK : STLK sz E s) (hDecay : STDecayLoopU sz E s t)
    (hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) → GridGoodNConcl sz E s v)
    (hLin : NQLinConcl sz E s t)
    (hNQ : ∀ t' : ℕ → ℝ, (∀ n, s n < t' n) → (∀ n, t' n ≤ t n) → STNQConclPT'' sz E s t')
    {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) {XL XLK : ℕ → ℕ → ℝ → ℝ}
    (hXL : ∀ i n u, 1 ≤ XL i n u) (hXLK : ∀ i n u, 1 ≤ XLK i n u)
    (hXLp : ∀ i, 1 ≤ i → STlenL (m + 1 + 1) p i →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 i ω) (fun n q _ => XL i n q.1.2))
    (hXLKp : ∀ i, 1 ≤ i → i ≤ m + 1 + 1 →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 i ω) (fun n q _ => XLK i n q.1.2))
    (q : ∀ n, STPair s t n) :
    StochDomAt sz.seqP sz.size
      (fun n (_ : Unit) ω => STXiLK sz n (E n) (q n).1.1 (m + 1 + 1) ω)
      (fun n (_ : Unit) _ => (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
        STbootRHS 1 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n))
          (m + 1 + 1) p) := by
  classical
  -- the window `v`, the frozen controls `uu`
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => if s n < (q n).1.1 then (q n).1.1 else t n := ⟨_, rfl⟩
  obtain ⟨uu, huudef⟩ : ∃ uu : ℕ → ℝ, uu = fun n => if s n < (q n).1.1 then (q n).1.2 else t n := ⟨_, rfl⟩
  have hv_pos : ∀ n, s n < (q n).1.1 → v n = (q n).1.1 := fun n h => by simp only [hvdef, h, ↓reduceIte]
  have hv_neg : ∀ n, ¬ s n < (q n).1.1 → v n = t n := fun n h => by simp only [hvdef, h, ↓reduceIte]
  have hu_pos : ∀ n, s n < (q n).1.1 → uu n = (q n).1.2 := fun n h => by simp only [huudef, h, ↓reduceIte]
  have hu_neg : ∀ n, ¬ s n < (q n).1.1 → uu n = t n := fun n h => by simp only [huudef, h, ↓reduceIte]
  have hsv : ∀ n, s n < v n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hv_pos n h]; exact h
    · rw [hv_neg n h]; exact hst n
  have hvu : ∀ n, v n ≤ uu n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hv_pos n h, hu_pos n h]; exact (q n).2.2.1
    · rw [hv_neg n h, hu_neg n h]
  have hut : ∀ n, uu n ≤ t n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hu_pos n h]; exact (q n).2.2.2
    · rw [hu_neg n h]
  have hvt : ∀ n, v n ≤ t n := fun n => (hvu n).trans (hut n)
  have hsu : ∀ n, s n < uu n := fun n => (hsv n).trans_le (hvu n)
  have hwu : ∀ n, (q n).1.1 ≤ uu n := fun n => by
    by_cases h : s n < (q n).1.1
    · rw [hu_pos n h]; exact (q n).2.2.1
    · have : (q n).1.1 = s n := le_antisymm (not_lt.1 h) (q n).2.1
      rw [hu_neg n h, this]; exact (hst n).le
  have hBs : ∀ n, 0 < sz.Bctl n (s n) := fun n => st_Bctl_pos sz ((hst n).trans (ht1 n))
  -- the restricted pair hypotheses on `[s, v]` with the controls at `uu`
  have hX : ∀ i : ℕ, 1 ≤ i → STlenL (m + 1 + 1) p i →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiL sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => XL i n (uu n)) := fun i hi hl =>
    StochDomAt.precomp_param (V := fun n => TimeIcc s v n) (hXLp i hi hl)
      (fun n w' => (⟨((w' : ℝ), uu n), w'.2.1, w'.2.2.trans (hvu n), hut n⟩ : STPair s t n))
  have hY : ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 + 1 →
      Prec sz (U := fun n => TimeIcc s v n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) i ω)
        (fun n _ _ => XLK i n (uu n)) := fun i hi hl =>
    StochDomAt.precomp_param (V := fun n => TimeIcc s v n) (hXLKp i hi hl)
      (fun n w' => (⟨((w' : ℝ), uu n), w'.2.1, w'.2.2.trans (hvu n), hut n⟩ : STPair s t n))
  have hAlt := altQFlow_core sz hd hκ h𝔠 hτR h𝔡 hsize hband hWO hE hs0 (fun n => (hst n).le) ht1 hcase hrange hWt
    hsv hvt hLK hDecay (hGrid v hsv hvt) hLin hm hp (X := fun i n => XL i n (uu n))
    (Y := fun i n => XLK i n (uu n)) (fun i n => hXL i n _) (fun i n => hXLK i n _) hX hY
  have hNQh := altQFlow_nq_half sz hsize (w := fun n => (q n).1.1) (n_ := m + 1 + 1) (by omega) hp hXL hXLK hXLp
    hXLKp (fun n => (q n).2.1) hwu hut (hNQ uu hsu hut)
  have hcoll := altQFlow_collapsed sz hLK (k := m + 1 + 1) (by omega) hBs
  have h2ev : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := fun τ hτ =>
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop 2
  intro τ hτ D hD
  filter_upwards [hAlt (τ / 2) (half_pos hτ) (D + 1) (by linarith), hNQh (τ / 2) (half_pos hτ) (D + 1) (by linarith),
    hcoll (τ / 2) (half_pos hτ) (D + 1) (by linarith), hsize.eventually_ge_atTop 2, h2ev τ hτ] with n h1 h2 h3 hN2 hhalf
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (by linarith) _
  have hu1 : (q n).1.2 < 1 := ((q n).2.2.2).trans_lt (ht1 n)
  have hw1 : (q n).1.1 < 1 := ((q n).2.2.1).trans_lt hu1
  have hBw : 0 < sz.Bctl n (q n).1.1 := st_Bctl_pos sz hw1
  have hBu : 0 < sz.Bctl n (q n).1.2 := st_Bctl_pos sz hu1
  have hBwu : sz.Bctl n (q n).1.1 ≤ sz.Bctl n (q n).1.2 := STBctl_mono sz n (q n).2.2.1 hu1
  have hNτ : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (by linarith) _
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (by linarith) _
  have hsq : ((sz.size n : ℕ) : ℝ) ^ τ =
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    (UnifDetDom.rpow_half_mul_rpow_half _ hτ).symm
  -- the right side `ζ` of the pin at the pair, and its lower bound `1 ≤ ζ`
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℝ, ζ = (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
      STbootRHS 1 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n)) (m + 1 + 1) p :=
    ⟨_, rfl⟩
  have hζ1 : 1 ≤ ζ := by
    have h0 : 0 ≤ (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 :=
      mul_nonneg (Real.rpow_nonneg hBu.le _) (zero_le_one.trans (hXLK _ _ _))
    have := altQFlow_bootRHS_one_le (lo := 1) (XL := fun i => XL i n (q n).1.2)
      (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p) (by omega)
      (fun i => hXL _ _ _) (fun i => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
    rw [hζ]; linarith
  by_cases hn' : s n < (q n).1.1
  · -- non-collapsed: `v n = w_n`, `uu n = u_n`; the union of the alternating and non-alternating parts
    have hv : v n = (q n).1.1 := hv_pos n hn'
    have hu : uu n = (q n).1.2 := hu_pos n hn'
    refine altQFlow_union2 hN0 h1 h2 ?_ (altQFlow_two_pow_le hN2 (by norm_num))
    intro ω hω
    by_contra hno
    simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
    obtain ⟨hnoA, hnoB⟩ := hno
    rw [hv, hu] at hnoA
    rw [hu] at hnoB
    simp only [badSetAt, Set.mem_ofPred_eq] at hω
    obtain ⟨_, hω⟩ := hω
    obtain ⟨ζA, hζA⟩ : ∃ ζA : ℝ, ζA = (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 +
        STbootRHS 2 (fun i => XL i n (q n).1.2) (fun i => XLK i n (q n).1.2) (sz.Bctl n (s n)) (m + 1 + 1) p :=
      ⟨_, rfl⟩
    have hmax : ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖Lloop sz n (E n) (q n).1.1 x.1 x.2 ω - STKloop sz n (E n) (q n).1.1 x.1 x.2‖ /
          (sz.Bctl n (q n).1.1) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by
      intro x
      by_cases hσ : x.1 (Fin.last (m + 1)) = !x.1 0
      · rw [hζA]; exact hnoA (⟨x.1, hσ⟩, x.2)
      · have hσ0 : x.1 (Fin.last (m + 1)) = x.1 0 := by
          revert hσ
          generalize x.1 (Fin.last (m + 1)) = b
          generalize x.1 0 = c
          cases b <;> cases c <;> simp
        have hσ' : ∃ k, x.1 k = x.1 (finRotate (m + 1 + 1) k) :=
          ⟨Fin.last (m + 1), by rw [finRotate_last]; exact hσ0⟩
        rw [hζA]; exact hnoB (⟨x.1, hσ'⟩, x.2)
    have hXi := altQFlow_xi_le hBw hmax
    have hζA1 : 1 ≤ ζA := by
      have h0 : 0 ≤ (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) * XLK (m + 1 + 1) n (q n).1.2 :=
        mul_nonneg (Real.rpow_nonneg hBw.le _) (zero_le_one.trans (hXLK _ _ _))
      have := altQFlow_bootRHS_one_le (lo := 2) (XL := fun i => XL i n (q n).1.2)
        (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p) (by omega)
        (fun i => hXL _ _ _) (fun i => zero_le_one.trans (hXLK _ _ _)) (hBs n).le
      rw [hζA]; linarith
    have hζAle : ζA ≤ ζ := by
      have e1 : (sz.Bctl n (q n).1.1) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n (q n).1.2) ^ (1 / 6 : ℝ) :=
        Real.rpow_le_rpow hBw.le hBwu (by norm_num)
      have e2 := altQFlow_bootRHS_two_le_one (XL := fun i => XL i n (q n).1.2)
        (XLK := fun i => XLK i n (q n).1.2) (B := sz.Bctl n (s n)) (k := m + 1 + 1) (p := p)
        (fun i => zero_le_one.trans (hXLK _ _ _))
      have e3 := mul_le_mul_of_nonneg_right e1 (zero_le_one.trans (hXLK (m + 1 + 1) n (q n).1.2))
      rw [hζA, hζ]; linarith
    have hfin : 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := by
      have hN1' : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
      calc 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA
          ≤ ζA + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by linarith
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA := by
            have := mul_le_mul_of_nonneg_right hN1' (by linarith : (0 : ℝ) ≤ ζA)
            linarith
        _ = 2 * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA) := by ring
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζA) :=
            mul_le_mul_of_nonneg_right hhalf (mul_nonneg hpos (by linarith))
        _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζA := by rw [hsq]; ring
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := mul_le_mul_of_nonneg_left hζAle hNτ
    rw [← hζ] at hω
    exact absurd hω (not_lt.2 (hXi.trans hfin))
  · -- collapsed: `w_n = s_n`, `STLK s`
    have hw : (q n).1.1 = s n := le_antisymm (not_lt.1 hn') (q n).2.1
    refine le_trans (measure_mono ?_) (h3.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))))
    intro ω hω
    simp only [badSetAt, Set.mem_ofPred_eq] at hω ⊢
    obtain ⟨_, hω⟩ := hω
    by_contra hno
    push Not at hno
    have hmax : ∀ x : (Fin (m + 1 + 1) → Bool) × (Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖Lloop sz n (E n) (q n).1.1 x.1 x.2 ω - STKloop sz n (E n) (q n).1.1 x.1 x.2‖ /
          (sz.Bctl n (q n).1.1) ^ (m + 1 + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
      intro x
      rw [hw]
      simpa using hno x
    have hXi := altQFlow_xi_le hBw hmax
    have hN1' : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
    rw [← hζ] at hω
    have : 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := by
      calc 1 + ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
            mul_le_mul_of_nonneg_right hhalf hpos
        _ = ((sz.size n : ℕ) : ℝ) ^ τ := hsq.symm
        _ = ((sz.size n : ℕ) : ℝ) ^ τ * 1 := (mul_one _).symm
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ := mul_le_mul_of_nonneg_left hζ1 hNτ
    exact absurd hω (not_lt.2 (hXi.trans this))

end Helpers

/-! ## §6 the per-time round `stOeqQtRoundPT'_holds` -/

/-- **`stOeqQtRoundPT'_holds`: the per-time alternating-and-non-alternating round for every `d ≥ 3`** (`lem:STOeq_Qt`
`3_5:1362-1378`, the alternating case `3_5:1676-1714`, `(eq:alternatecase1)` `3_5:1687`; the non-alternating signs are
`lem:STOeq_NQ`, `3_5:1679`; DECISIONS §62 (2)/(4), §95 (3), §105 (1), §119-§120; paper-delta candidates `T2310a`, `T2310b`).
`𝔠_d = min 𝔠_d^G 𝔠_d^L 𝔠_d^{NQ} (1/(2d))` with `𝔠_d^G`, `𝔠_d^L` the constants of `gridGoodN_holds d` and `nqLinGood_holds d`
and `𝔠_d^{NQ}` that of the merged `stOeqNQPT''_holds d`, all at the same `(κ, ε, 𝔡, C_d)`: `d 𝔠_d ≤ 1/2 < 1` for
`st_window`, and `STConStInd` passes to the larger exponents (`altQFlow_conStInd_exp_mono`).  The premises of `altGridEndQN`
come from the flow (`v3_premises_of_stFlow` with `κ/2`, `ε/2`; `st_window`); the good-event lemmas are re-instantiated on every
window `[s, v]` (`st_conStInd_sub`, `altQFlow_step2_restrict`), the decay `STDecayLoopU` is `stDecayLoopU_of_step2` at
`STGdecayW`, and the merged `stOeqNQPT''_holds` on every window `[s, t']`; then `perTimeDomAt_iff_forall_section` and
`altQFlow_section`. -/
theorem stOeqQtRoundPT'_holds : ∀ d : ℕ, STOeqQtRoundPT' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠G, hG0, hG1, HG⟩ := gridGoodN_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠L, hL0, hL1, HL⟩ := nqLinGood_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠N, hN0, hN1, HN⟩ := stOeqNQPT''_holds d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd2 : (0 : ℝ) < 1 / (2 * d) := by positivity
  obtain ⟨𝔠d, h𝔠d⟩ : ∃ 𝔠d : ℝ, 𝔠d = min (min (min 𝔠G 𝔠L) 𝔠N) (1 / (2 * d)) := ⟨_, rfl⟩
  have h𝔠d0 : 0 < 𝔠d := by rw [h𝔠d]; exact lt_min (lt_min (lt_min hG0 hL0) hN0) hd2
  have h𝔠dG : 𝔠d ≤ 𝔠G := by
    rw [h𝔠d]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have h𝔠dL : 𝔠d ≤ 𝔠L := by
    rw [h𝔠d]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have h𝔠dN : 𝔠d ≤ 𝔠N := by rw [h𝔠d]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h𝔠dd : 𝔠d ≤ 1 / (2 * d) := by rw [h𝔠d]; exact min_le_right _ _
  refine ⟨𝔠d, h𝔠d0, h𝔠dG.trans hG1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  obtain ⟨hA, hE', ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow ht
  have hconG : sz.STConStInd 𝔠G s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dG ht1 hcon
  have hconL : sz.STConStInd 𝔠L s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dL ht1 hcon
  have hconN : sz.STConStInd 𝔠N s t := altQFlow_conStInd_exp_mono sz h𝔠d0 h𝔠dN ht1 hcon
  have hdc : (d : ℝ) * 𝔠d < 1 := by
    calc (d : ℝ) * 𝔠d ≤ d * (1 / (2 * d)) := mul_le_mul_of_nonneg_left h𝔠dd hd0.le
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hWt := st_window sz h𝔠d0 hdc hcon hA.2.2.2.2 (scaleFacts3_W_tendsto sz hA) hs ht1
  have hGrid : ∀ v : ℕ → ℝ, (∀ n, s n < v n) → (∀ n, v n ≤ t n) →
      GridGoodNConcl sz (STflowE z) s v := fun v hsv hvt =>
    HG 𝔠 sz z hflow s v hs hsv (fun n => (hvt n).trans (ht n)) trivial hK hKw hLK
      (st_conStInd_sub sz hG0 hconG (fun n => le_rfl) hsv hvt ht1) (altQFlow_step2_restrict hvt hStep2)
  have hLin : NQLinConcl sz (STflowE z) s t :=
    HL 𝔠 sz z hflow s t hs hst ht trivial hK hKw hLK hconL hStep2
  have hDecay : STDecayLoopU sz (STflowE z) s t :=
    stDecayLoopU_of_step2 hd sz hκ hε hflow hs (fun n => (hst n).le) ht Cd hStep2.2.2
  have hNQ : ∀ t' : ℕ → ℝ, (∀ n, s n < t' n) → (∀ n, t' n ≤ t n) → STNQConclPT'' sz (STflowE z) s t' :=
    fun t' hst' ht't =>
      HN 𝔠 sz z hflow s t' hs hst' (fun n => (ht't n).trans (ht n)) (fun n => (hR n).trans (by linarith [ht't n]))
        hK hKw hLK (st_conStInd_sub sz hN0 hconN (fun n => le_rfl) hst' ht't ht1)
        (altQFlow_step2_restrict ht't hStep2)
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  obtain ⟨m, rfl⟩ : ∃ m, n_ = m + 1 + 1 := ⟨n_ - 2, by omega⟩
  refine (perTimeDomAt_iff_forall_section sz.seqP sz.size
    (fun n => ⟨(s n, s n), le_rfl, le_rfl, (hst n).le⟩) _ _).2 ?_
  intro q
  exact altQFlow_section sz hd (half_pos hκ) hA.1 (half_pos hε) hA.2.1 hA.2.2.1 hA.2.2.2.1 hA.2.2.2.2
    (fun n => (hE' n).le) hs hst ht1 hR hrange hWt hLK hDecay hGrid hLin hNQ (by omega) hp hXL hXLK hXLp hXLKp q

/-! ## §7 Compiled nonempty instances at `d = 3`

Namespace `RBM.Ind.QEndB1Inst`.  Data (the merged instance data of `RBM.Gauss.Step34Inst`, as `NQEndFlowInst`): `sz0`
(`d = 3`, `L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2^21`), the flow `z0`
(`flow_z0` at `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z_n`, `STCaseI`: `sz0_caseI`; `(con_st_ind)` for
every `𝔠_d > 0`: `sz0_con`), `C_d = 1`.  `STKbound`, `STKward` are theorems of the flow (`stKbound_of_flow`, `stKward_of_flow`);
what stays a hypothesis of an example is a stochastic premise that is another gate's pin (`STLK s`, `STStep2Concl`, the pair
hypotheses `Ξ̂ ≺ 1` of the pin).  The pin is stated over the pairs `(w, u)`, `0 ≤ w ≤ u ≤ 1/16`, including `w < u`. -/

namespace QEndB1Inst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- **(1) `stOeqQtRoundPT'_holds` at the data**: the per-time round pin at `(sz0, z0, s ≡ 0, t ≡ 1/16)`, `C_d = 1`: the
constant `𝔠_d ∈ (0, 1/100]`, then the stochastic premises of `STIngR` (`STKbound`, `STKward`, `STLK`, `STStep2Concl`), then
the conclusion `STXiRoundPT'`.  Every deterministic hypothesis (`3 ≤ d`, the flow, `0 ≤ s < t ≤ lemT z`, the regime
`STCaseI`, `(con_st_ind)`, `C_d > 0`) is discharged by `inst_ing`. -/
theorem inst_OeqQtRoundPT' :
    InstIngConcl (fun sz E s t => STXiRoundPT' sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing STCaseI (fun sz E s t => STXiRoundPT' sz E s t) (stOeqQtRoundPT'_holds 3) sz0 z0 flow_z0 sInst tInst
    sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con 1 one_pos

/-- **(1) with the conclusion applied** at `n_ = 3` (`m = 1`), `p = 1`, `XL ≡ XLK ≡ 1`: `STKbound`, `STKward` come from the
flow, the stochastic premises `STLK s`, `STStep2Concl` and the pair hypotheses `Ξ̂ ≺ 1` of the pin (the conclusions of
Steps 3-4, other gates' pins) stay hypotheses; the per-time conclusion
`Ξ̂^{(𝓛-𝒦)}_{w,3} ≺ B_u^{1/6} + STbootRHS 1 1 1 B_s 3 1` for every pair `s ≤ w ≤ u ≤ t` (`PrecPT`: the union over the pairs
outside `P`) is the conclusion. -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 3 1 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 3 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 3 ω)
      (fun n q _ => sz0.Bctl n q.1.2 ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 3 1) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqQtRoundPT'
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 3 1 le_rfl le_rfl
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(2) the same at `n_ = 4`** (`m = 2`), `p = 2`: the current-length control `XLK 4` and the lower-length control
`XLK 3` (the level `X` of `altGridEndQN`, `m + 1 = 3`) are both used by the proof. -/
example (hLK : STLK sz0 (STflowE z0) sInst) (hStep2 : STStep2Concl sz0 (STflowE z0) sInst tInst 1)
    (hXp : ∀ m, 1 ≤ m → STlenL 4 2 m →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiL sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ)))
    (hXKp : ∀ m, 1 ≤ m → m ≤ 4 →
      Prec sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 m ω)
        (fun n q _ => (1 : ℝ))) :
    PrecPT sz0 (U := STPair sInst tInst) (fun n q ω => STXiLK sz0 n (STflowE z0 n) q.1.1 4 ω)
      (fun n q _ => sz0.Bctl n q.1.2 ^ (1 / 6 : ℝ) * 1 +
        STbootRHS 1 (fun _ => 1) (fun _ => 1) (sz0.Bctl n (sInst n)) 4 2) := by
  obtain ⟨𝔠d, -, -, hC⟩ := inst_OeqQtRoundPT'
  exact hC (stKbound_of_flow sz0 (by norm_num) (by norm_num) flow_z0)
    (stKward_of_flow sz0 (by norm_num) (by norm_num) flow_z0) hLK hStep2 4 2 (by norm_num) (by norm_num)
    (fun _ _ _ => 1) (fun _ _ _ => 1) (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) hXp hXKp

/-- **(3) the index set of the pin is nondegenerate**: at every size index the pairs `(w, u)` with `w < u` exist
(`(0, 1/16)`), as do diagonal pairs `(0, 0)`. -/
example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 < q.1.2 :=
  ⟨⟨((0 : ℝ), 1 / 16), by simp only [sInst, tInst]; norm_num⟩, by norm_num⟩

example (n : ℕ) : ∃ q : STPair sInst tInst n, q.1.1 = q.1.2 :=
  ⟨⟨((0 : ℝ), 0), by simp only [sInst, tInst]; norm_num⟩, rfl⟩

/-- **(4) the helpers at numbers**: `STbootRHS 2 ≤ STbootRHS 1` and `XLK (k-1) ≤ STbootRHS 2 …` at `k = 3`, `p = 1`, `B = 1/2`,
`XL ≡ XLK ≡ 1`; the failure-probability arithmetic `2 N^{-(D+1)} ≤ N^{-D}` at `N = 4`, `D = 1`. -/
example : STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 ≤
    STbootRHS 1 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 :=
  altQFlow_bootRHS_two_le_one (fun _ => zero_le_one)

example : (fun _ : ℕ => (1 : ℝ)) (3 - 1) ≤ STbootRHS 2 (fun _ => (1 : ℝ)) (fun _ => 1) (1 / 2) 3 1 :=
  altQFlow_Ylow_le_bootRHS (k := 3) le_rfl (fun _ => zero_le_one) (fun _ => zero_le_one) (by norm_num)

example : 2 * (4 : ℝ) ^ (-(1 + (1 : ℝ))) ≤ (4 : ℝ) ^ (-(1 : ℝ)) :=
  altQFlow_two_pow_le (by norm_num) le_rfl

/-- **(5) the statement of the target** (`T2310_stOeqQtRoundPT'_holds`, check file section 3): `stOeqQtRoundPT'_holds` has
exactly the type `∀ d : ℕ, STOeqQtRoundPT' d`. -/
example : ∀ d : ℕ, STOeqQtRoundPT' d := @stOeqQtRoundPT'_holds

end QEndB1Inst

end RBM.Ind

end

#print axioms RBM.Gauss.Sizes.STXiRoundPT'
#print axioms RBM.Gauss.Sizes.STOeqQtRoundPT'
#print axioms RBM.Ind.stOeqQtRoundPT'_holds
#print axioms RBM.Ind.QEndB1Inst.inst_OeqQtRoundPT'
