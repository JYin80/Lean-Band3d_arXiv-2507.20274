/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QBudgetA

/-!
# S3-17b (ticket T2286): the linear drift level of the alternating chain, eventual absorptions

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `lem:STOeq_Qt`
`3_5:1364-1378`, the alternating case `3_5:1676-1714` (`(y27kasdfg)`, `(A4)`, `(A5)`
`3_5:1692-1706`), `lem_+Q`/`(normQA)` `3_5:1284-1289`, the non-alternating linear budget
`3_5:1152-1180`.

Re-scope (DECISIONS §92 (4), §62 (2)/(4), §64 (4)/(5), §83, §91 (2)): the merged level
`dDriftAltQN` (`QLevelsB.lean:53`) takes the block level from (D2) of `GoodSetN`; here the block
level is the linear one of `GoodLinN` (`NQLin.lean:66`), `GoodSetN` enters only through its
level-free clauses (Herm), (Vb), (Dec) at a free crude level, and `hY` (the length-`m + 1`
control) is an explicit premise.  No probability, no `Prec`, no lift, no prime.

* §0 vocabulary (check file `docs/tickets/checks/T2286-check.lean` §2, verbatim):
  `altBudgetNumQN`, `altBudgetExpQN`;
* §1 targets 1-4: `dFlowQN_levelLin`, `alt_hdriftLinQN`, `dDriftAltLinQN_nonneg`,
  `dDriftAltQN_eq_lin`;
* §2 asymptotic helpers and the eight row lemmas (private, copies of `NQEndLin.lean:54-436`);
* §3 targets 5-6: `altBudgetExpQN_of_choice`, `altBudgetNumQN_eventually`;
* §4 compiled nonempty instances (namespace `QBudgetBInst`) at `d = 3`, `sz0`.

Unpinned helpers are `private` or prefixed `QBudgetB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## §2 Vocabulary (copied verbatim into `QBudgetB.lean`) -/

/-- **The eight numerical hypotheses of `budgetAltQN` at the linear drift level** (one `n`):
`ha1`, `ha2`, `ha3`, `he0`, `he1`, `he2`, `he3`, `he4` of `budgetAltQN` (`QBudgetA.lean:575`) verbatim, with
`Pa = W^{C_n ε'} (Γ Γ) k + N^{τ_N}` (the shape of `dDriftAltLinQN_le_shape`, `QBudgetA.lean:419`) at
`Γ = N^{ε₁}`, `b = W^{-D'+C_n}`, `δ0 = 2 W^{-D'}` (`alt_hA0clsQN`), `δD = 4 W^{-D'}` (`alt_hDclsQN`),
`C_n = qProxyCn d (m+1) Λg KL C c` (one constant for the drift level and the QV). -/
def altBudgetNumQN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n m : ℕ)
    (Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ : ℝ) : Prop :=
  -- `ha1`
  ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 ∧
  -- `ha2` at `Pa`
  ((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
      (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε') *
          (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
        ((sz.size n : ℕ) : ℝ) ^ τN) *
      ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
    ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 ∧
  -- `ha3`
  ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ (qProxy4C d (m + 1 + 1) Λg κ' KL * ε) *
      ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε) * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤
    ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 ∧
  -- `he0` at `δ0 = 2 W^{-D'}`
  ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
      (((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))) ≤
    ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 ∧
  -- `he1` at `b = W^{-D'+C_n}`, `δD = 4 W^{-D'}`
  ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * (altBudget_kapFar sz n (m + 1 + 1) Λg κ' KL ε *
        ((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL C c) +
      ((sz.W n : ℕ) : ℝ) ^ qProxy4C d (m + 1 + 1) Λg κ' KL * (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))) ≤
    ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 ∧
  -- `he2`
  ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) *
      Real.sqrt (((m + 1 + 1 : ℕ) : ℝ) * (altBudget_qvFar sz n (m + 1 + 1) Λg κ' KL ε *
        ((sz.W n : ℕ) : ℝ) ^ (-D'' + qProxyCQ d (m + 1) Λg KL C c)))) ≤
    ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 ∧
  -- `he3`, `he4`
  ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 ∧
  ((sz.size n : ℕ) : ℝ) ^ (m + 1 + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6

/-- **The exponent conditions of the eight absorptions** (`k = m + 2`, `C4 = C₄`, `Cn = C_n`, `C_Q = 2 C_n + 2`,
bandwidth exponent `𝔠`, common `he2` exponent `ξ`): nonnegativity of the positive `W`-exponents, then per row
(`ha1`; `ha2` two summands; `ha3`; `he0` and the `δD` part of `he1`; the `b` part of `he1`; `he2` as
`nqEnd_ev_he2`, `NQEndLin.lean:397`, with `R = ((1+g²)N)^k` and `D = D'' - C_Q`; `he3`; `he4`). -/
def altBudgetExpQN (k : ℕ) (C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ : ℝ) : Prop :=
  0 ≤ C4 * ε ∧ 0 ≤ Cn * ε ∧ 0 ≤ Cn * ε' ∧
  C4 * ε + ε₁ < ε₀ ∧
  C4 * ε + Cn * ε' + 2 * ε₁ < ε₀ ∧ C4 * ε + τN < ε₀ ∧
  εq + C4 * ε + Cn * ε + ε₁ < ε₀ ∧
  C4 ≤ D' ∧ (k : ℝ) + 𝔠 * (C4 - D') < ε₀ ∧
  C4 * ε + Cn ≤ D' ∧ 2 * (k : ℝ) + 𝔠 * (C4 * ε + Cn - D') < ε₀ ∧
  2 * (C4 * ε) - (D'' - (2 * Cn + 2)) ≤ 0 ∧ C4 * ε + C4 - (D'' - (2 * Cn + 2)) ≤ 0 ∧
  C4 + (k : ℝ) - (D'' - (2 * Cn + 2)) ≤ 0 ∧
  2 * (k : ℝ) + 𝔠 * (2 * (C4 * ε) - (D'' - (2 * Cn + 2))) ≤ ξ ∧
  (k : ℝ) + 𝔠 * (C4 * ε + C4 - (D'' - (2 * Cn + 2))) ≤ ξ ∧
  𝔠 * (C4 + (k : ℝ) - (D'' - (2 * Cn + 2))) ≤ ξ ∧
  εq + (k : ℝ) + ξ / 2 < ε₀ ∧
  (k : ℝ) - D_Y < ε₀ ∧ (k : ℝ) - D_t < ε₀

/-! ## 1. Targets 1-4: the linear drift level of the alternating chain -/

/-- `C_n = qProxyCn d m Λg K C c` is the `Classical.choose` of `stQopNorm_holds` under the range `3 ≤ d ∧ 0 < Λg ∧
0 < K ∧ 0 < C ∧ 0 < c` (the `dite` of `QProxy.lean:434`, as in `qProxyCn_pos`, `QProxy.lean:458`). -/
private theorem QBudgetB_qProxyCn_eq {d : ℕ} (hd : 3 ≤ d) (m : ℕ) {Λg K C c : ℝ} (hΛ : 0 < Λg)
    (hK : 0 < K) (hC : 0 < C) (hc : 0 < c) :
    qProxyCn d m Λg K C c = Classical.choose (stQopNorm_holds d hd m Λg K C c hΛ hK hC hc) := by
  unfold qProxyCn
  rw [dite_eq_left_of_eq_true (eq_true ⟨hd, hΛ, hK, hC, hc⟩)]

/-- Target 1: the per-matrix LINEAR drift level of the alternating chain (`dFlowQN_levelM` with
`driftTensorN_norm_le_of_goodLin` for the block, `GoodSetN` only at a free crude level for (Herm), (Vb), (Dec),
`hY` an explicit premise, `C_n = qProxyCn d (m+1) Λg KL C c` explicit). -/
theorem dFlowQN_levelLin :
  ∀ (d m : ℕ) (Λg KL C c : ℝ), 3 ≤ d → 0 < Λg → 0 < KL → 0 < C → 0 < c →
    ∀ (sz : Sizes d) (n : ℕ) (E u κ Γc Λc Φc Γ Φ₁ Φ₂ Φ₃ τ' ε' D' ν X τN : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ),
      0 < κ → |E| ≤ 2 - κ → 0 ≤ u → u < 1 → 0 < sz.lam n → sz.lam n ≤ Λg →
      (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u →
      1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' →
      4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      1 ≤ ν → 1 ≤ X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) →
      ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ →
      (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * C * ν ^ 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ τN →
      STMollifierProps (d := d) (sz.lam n) C c ϑ →
      H ∈ sz.GoodSetN n E u (m + 1 + 1) Γc Λc Φc τ' D' →
      H ∈ GoodLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ →
      (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1)) →
      σ (Fin.last (m + 1)) = !σ 0 →
      ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖dFlowQN sz n E u ϑ σ H a‖ ≤
          dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ (qProxyCn d (m + 1) Λg KL C c) ε' D' τN X := by
  intro d m Λg KL C c hd hΛg hKL hC hc sz n E u κ Γc Λc Φc Γ Φ₁ Φ₂ Φ₃ τ' ε' D' ν X τN Hm σ ϑ hκ hE hu0 hu1
    hlam hlamΛ hNu hW hτ' hε hε1 hD h4 hLW hdW hν hX hνt hνN hFv hMΛ hϑ hG hGL hY hσ a
  rw [QBudgetB_qProxyCn_eq hd (m + 1) hΛg hKL hC hc]
  obtain ⟨hCn, H3⟩ := Classical.choose_spec (stQopNorm_holds d hd (m + 1) Λg KL C c hΛg hKL hC hc)
  generalize Classical.choose (stQopNorm_holds d hd (m + 1) Λg KL C c hΛg hKL hC hc) = Cn at hCn H3 ⊢
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hfast : EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
      (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b) :=
    drift13_fastDecay sz hd σ hdW hG
  have hq := H3 (sz.L n) (sz.three_le_L n) (sz.lam n) hlam hlamΛ ((sz.W n : ℕ) : ℝ) ε' D' hW hε hε1 hD h4
    hLW ϑ hϑ u hu0 hu1 _ hfast
  have hpt : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖driftTensorN sz n E u Hm σ b‖ ≤
      dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ := fun b =>
    driftTensorN_norm_le_of_goodLin sz (by omega) hGL σ b
  have hnn : 0 ≤ dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ :=
    (norm_nonneg _).trans (hpt (fun _ => 0))
  have hsup : ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b‖ ≤
      dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ := (pi_norm_le_iff_of_nonneg hnn).2 hpt
  have hrp : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') := Real.rpow_nonneg hWpos.le _
  have hQ : ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b) a‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftLinN sz n E u (m + 1 + 1) Γ Φ₁ Φ₂ Φ₃ +
        ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
    calc _ ≤ ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b)‖ :=
          norm_le_pi_norm _ a
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
          driftTensorN sz n E u Hm σ b‖ + ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := hq
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hsup hrp
          linarith
  have hHerm : Hm.IsHermitian := hG.1
  have hωf : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW.le hτ'
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
        ‖sz.STLKM n E u Hm σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := fun σ' a' hfar =>
    goodSetN_LKM_far d sz n E u (m + 1 + 1) Γc Λc Φc τ' D' Hm hG (m + 1) (by omega) (by omega) σ' a' hfar
  have hexp : ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
      ‖ϑ u a‖ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by
    intro a
    refine (hϑ.2.1 u hu0 hu1 a).trans ?_
    have hl : 0 < ellT (sz.L n) (sz.lam n) u := ellT_pos (by
      exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have hS : 0 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hex : Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1 + 1)),
        (zdistD d (sz.L n) (a i - a 0) : ℝ)) / ellT (sz.L n) (sz.lam n) u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg hc.le hS]) hl.le
    have hC0 : 0 ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) := by positivity
    calc _ ≤ C * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1)) * 1 :=
          mul_le_mul_of_nonneg_left hex hC0
      _ = _ := by rw [mul_one]
  have hB45 := altB45N_levelM d (by omega) sz n E u κ hκ hE hu0 hu1 hlam hNu Hm hHerm m (2 / Real.sqrt κ) ν X
    (((sz.W n : ℕ) : ℝ) ^ τ') (((sz.W n : ℕ) : ℝ) ^ (-D')) C τN rfl hν hX hωf hνt hνN hFv
    (Real.rpow_nonneg hWpos.le _) hC.le hMΛ hY hF ϑ hexp (fun a => hϑ.2.2.2 u hu0 hu1 a) σ hσ a
  have hflow : dFlowQN sz n E u ϑ σ Hm a =
      STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b) a +
        altB4N sz n E u ϑ σ Hm a + altB5N sz n E u ϑ σ Hm a := rfl
  rw [hflow]
  unfold dDriftAltLinQN
  have h3 := norm_add₃_le (a := STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
    driftTensorN sz n E u Hm σ b) a) (b := altB4N sz n E u ϑ σ Hm a) (c := altB5N sz n E u ϑ σ Hm a)
  linarith [hB45.2]

/-- Target 2: the field `hdrift` of `GridAssemblyHypN` along the walk at the linear level (`alt_hdriftQN` with
target 1; mollifier `QopAlgebra_mollifier`, `C = (1 + 40 d(m+1)) 6^{d(m+1)}`, `c = 1/2`; membership in
`GoodSetN ∩ GoodLinN` in the form of `mem_of_lt_nqLinExitTauN`; `hY` on `{j < τ}` separate). -/
theorem alt_hdriftLinQN :
  ∀ (d m : ℕ) (Λg KL : ℝ), 3 ≤ d → 0 < Λg → 0 < KL →
    ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
      (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (κ τ' ε' D' ν X τN : ℝ) (τ : PathΩ sz → ℕ),
      0 < κ → |E n| ≤ 2 - κ → 0 < sz.lam n → sz.lam n ≤ Λg →
      0 ≤ s n → s n ≤ v n → v n < 1 → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n →
      1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' →
      4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ KL →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      1 ≤ ν → 1 ≤ X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) →
      ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ →
      (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) *
          ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤
        ((sz.size n : ℕ) : ℝ) ^ τN →
      σ (Fin.last (m + 1)) = !σ 0 →
      (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈
        sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1 + 1) (Γ n) (Λ n) (Φ n) τ' D' ∩
          GoodLinN sz n (E n) (gridTime s v Kg n j) (m + 1 + 1) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
      (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ‖sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ' a'‖ ≤
          ν * X * sz.Bctl n (gridTime s v Kg n j) ^ (m + 1)) →
      ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤
          dDriftAltLinQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)
            (qProxyCn d (m + 1) Λg KL ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) (1 / 2))
            ε' D' τN X := by
  intro d m Λg KL hd hΛg hKL sz n σ E s v Kg Γ Λ Φ Φ₁ Φ₂ Φ₃ κ τ' ε' D' ν X τN τ hκ hE hlam hlamΛ hs0 hsv hv1
    hNv hW hτ' hε hε1 hD h4 hLW hdW hν hX hνt hνN hFv hMΛ hσ hτG hY ω j hj hjτ b
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  rw [dGridQN_eq_dFlowQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω]
  have hKne : Kg n ≠ 0 := by omega
  have hmem := ST_gridTime_mem s v Kg n j hsv hKne hj.le
  have hu0 : 0 ≤ gridTime s v Kg n j := hs0.trans hmem.1
  have hu1 : gridTime s v Kg n j < 1 := lt_of_le_of_lt hmem.2 hv1
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - gridTime s v Kg n j := by linarith [hmem.2]
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam
  exact dFlowQN_levelLin d m Λg KL _ (1 / 2) hd hΛg hKL hC0 (by norm_num) sz n (E n) (gridTime s v Kg n j) κ
    (Γ n) (Λ n) (Φ n) (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) τ' ε' D' ν X τN (pathH sz s v Kg n j ω) σ
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hκ hE hu0 hu1 hlam hlamΛ hNu hW hτ' hε hε1 hD h4 hLW
    hdW hν hX hνt hνN hFv hMΛ hϑ (hτG ω j hjτ).1 (hτG ω j hjτ).2 (hY ω j hjτ) hσ b

/-- Target 3: the field `hdDrift0` at the linear level. -/
theorem dDriftAltLinQN_nonneg :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X →
      0 ≤ dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X := by
  intro d sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X hE hu h1 h2 h3 hX
  have hη : 0 < etaT E u := etaT_pos hE hu
  have hB : 0 < sz.Bctl n u := STBctl_pos sz n hu
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold dDriftAltLinQN dDriftLinN
  have hk : (0 : ℝ) ≤ (((m + 1 + 1 : ℕ) : ℝ) - 2) := by
    push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hT : 0 ≤ sz.Bctl n u ^ (m + 1 + 1) / etaT E u := div_nonneg (pow_nonneg hB.le _) hη.le
  have h1' : 0 ≤ Γ * Γ * (sz.Bctl n u ^ (m + 1 + 1) / etaT E u) *
      ((((m + 1 + 1 : ℕ) : ℝ) - 2) * Φ₁ + Φ₂ + Φ₃) :=
    mul_nonneg (mul_nonneg (mul_self_nonneg Γ) hT) (add_nonneg (add_nonneg (mul_nonneg hk h1) h2) h3)
  have h2' := Real.rpow_nonneg hWpos.le (Cn * ε')
  have h3' := Real.rpow_nonneg hWpos.le (-D' + Cn)
  have h4' := Real.rpow_nonneg hN τN
  have h5 : 0 ≤ (etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X := by positivity
  have := mul_nonneg h2' h1'
  have := mul_nonneg h4' h5
  linarith

/-- Target 4: the merged quadratic level is the linear level at `Φ₁ = Φ₃ = Φ`, `Φ₂ = kΓΦ²`
(`dDriftNonAltN_eq_lin`; consistency of the two S3-16b/S3-17 levels). -/
theorem dDriftAltQN_eq_lin :
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
    dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X =
      dDriftAltLinQN sz n E u m Γ Φ (((m + 1 + 1 : ℕ) : ℝ) * Γ * Φ ^ 2) Φ Cn ε' D' τN X := by
  intro d sz n E u m Γ Φ Cn ε' D' τN X
  unfold dDriftAltQN dDriftAltLinQN
  rw [dDriftNonAltN_eq_lin]


/-! ## 2. Asymptotic helpers and the eight row lemmas

The private helpers `QBudgetB_ev_rpow_le`, `QBudgetB_ev_rpow_log_le`, `QBudgetB_ev_polylog_le`, `QBudgetB_W_le_size`,
`QBudgetB_Wpow_le`, `QBudgetB_he2_bound`, `QBudgetB_he2_final`, `QBudgetB_ev_he4` are copies of the `nqEnd_*` lemmas of
`NQEndLin.lean` (`:57`, `:67`, `:92`, `:142`, `:154`, `:324`, `:367`, `:303`; ticket T2199, RBM2D `NonAltEnd.lean:54-121`,
`:266`, `:573`); the rows `ha2`, `ha3`, `he1` are adapted to the eventual hypothesis `κ' ≤ Im m(E n)`, to the two-term
`Pa`, and to the `b` part. -/

section Asymp

/-- `C · x^a ≤ x^b` for all large real `x` when `a < b` (RBM2D `NonAltEnd_ev_rpow_le`, `NonAltEnd:60`). -/
private theorem QBudgetB_ev_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ x ^ b := by
  have ht : Tendsto (fun x : ℝ => x ^ (b - a)) atTop atTop := tendsto_rpow_atTop (sub_pos.mpr hab)
  filter_upwards [ht.eventually_ge_atTop C, eventually_gt_atTop 0] with x hx hx0
  have h1 : x ^ b = x ^ (b - a) * x ^ a := by
    rw [← Real.rpow_add hx0]; ring_nf
  rw [h1]
  exact mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg hx0.le _)

/-- `C · x^a (log x + 1) ≤ x^b` for all large real `x` when `a < b` (RBM2D `NonAltEnd:70`). -/
private theorem QBudgetB_ev_rpow_log_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a * (Real.log x + 1) ≤ x ^ b := by
  set δ := (b - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  filter_upwards [QBudgetB_ev_rpow_le (a := a + δ) (b := b) (by rw [hδ]; linarith)
    (max C 0 * (1 / δ + 1)), eventually_ge_atTop 1] with x hN hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hNδ : 1 ≤ x ^ δ := Real.one_le_rpow hx1 hδ0.le
  have hl : Real.log x + 1 ≤ (1 / δ + 1) * x ^ δ := by
    have : x ^ δ / δ = 1 / δ * x ^ δ := by ring
    nlinarith
  have hCa : C * x ^ a ≤ max C 0 * x ^ a :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _)
  have hM0 : 0 ≤ max C 0 * x ^ a := mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hx0.le _)
  calc C * x ^ a * (Real.log x + 1)
      ≤ max C 0 * x ^ a * (Real.log x + 1) := mul_le_mul_of_nonneg_right hCa (by linarith)
    _ ≤ max C 0 * x ^ a * ((1 / δ + 1) * x ^ δ) := mul_le_mul_of_nonneg_left hl hM0
    _ = max C 0 * (1 / δ + 1) * x ^ (a + δ) := by
        rw [Real.rpow_add hx0]; ring
    _ ≤ x ^ b := hN

/-- **Polylog absorption**: `C (1 + log x)^j x^a ≤ x^b` for all large real `x` when `a < b`
(RBM2D `NonAltEnd_ev_polylog_le`, `NonAltEnd:94`). -/
private theorem QBudgetB_ev_polylog_le (j : ℕ) :
    ∀ {a b : ℝ}, a < b → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ^ j * x ^ a ≤ x ^ b := by
  induction j with
  | zero =>
    intro a b hab C
    filter_upwards [QBudgetB_ev_rpow_le hab C] with x hx
    simpa using hx
  | succ j ih =>
    intro a b hab C
    set m := (a + b) / 2 with hm
    have ham : a < m := by rw [hm]; linarith
    have hmb : m < b := by rw [hm]; linarith
    filter_upwards [QBudgetB_ev_rpow_log_le ham (max C 0), ih hmb 1, eventually_ge_atTop 1] with
      x h1 h2 hx1
    have hx0 : (0 : ℝ) < x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hL : 0 ≤ (1 + Real.log x) ^ j := by positivity
    have hxa : 0 ≤ x ^ a := Real.rpow_nonneg hx0.le _
    calc C * (1 + Real.log x) ^ (j + 1) * x ^ a
        ≤ max C 0 * (1 + Real.log x) ^ (j + 1) * x ^ a := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (by positivity)) hxa
      _ = (1 + Real.log x) ^ j * (max C 0 * x ^ a * (Real.log x + 1)) := by ring
      _ ≤ (1 + Real.log x) ^ j * x ^ m := mul_le_mul_of_nonneg_left h1 hL
      _ = 1 * (1 + Real.log x) ^ j * x ^ m := by ring
      _ ≤ x ^ b := h2

end Asymp

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`
(copy of `nqEnd_W_le_size`, `NQEndLin.lean:142`). -/
private theorem QBudgetB_W_le_size {d : ℕ} (sz : Sizes d) (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

/-- `W^e ≤ N^{𝔠 e}` for `e ≤ 0` from `N^𝔠 ≤ W` (the negative powers of `W`; RBM2D
`NonAltEnd_Wneg_le`, `NonAltEnd:266`, with a general nonpositive exponent). -/
private theorem QBudgetB_Wpow_le {W N c e : ℝ} (hN0 : 0 < N) (hcW : N ^ c ≤ W) (he : e ≤ 0) :
    W ^ e ≤ N ^ (c * e) := by
  have h1 : 0 < N ^ c := Real.rpow_pos_of_pos hN0 _
  have h := Real.rpow_le_rpow_of_nonpos h1 hcW he
  rwa [← Real.rpow_mul hN0.le] at h

/-- The core bound of (he2), on plain reals: with `R ≤ P N^r`, the three exponents `e₁ = 2a - D`,
`e₂ = a + b - D`, `e₃ = b + k - D` all `≤ 0` (so that `W^{e} ≤ N^{𝔠 e}`) and
`2r + 𝔠 e₁, r + 𝔠 e₂, 𝔠 e₃ ≤ ξ`:
`(W^a R (W^a R + W^b) + W^b W^k) W^{-D} ≤ (P² + P + 1) N^ξ`.  Here `a = Cε`, `b = C`,
`R = ((1+g²)N)^{k-1}`, so the left side is `nqBudget_qvFar · W^{-D''}`: the positive powers of `W` are
combined with `W^{-D''}` before the bandwidth `W ≥ N^𝔠` is used. -/
private theorem QBudgetB_he2_bound {x N R P a b D 𝔠 ξ r : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hx : N ^ 𝔠 ≤ x)
    (hR0 : 0 ≤ R) (hRP : R ≤ P * N ^ r) (hP : 0 ≤ P) (he1 : 2 * a - D ≤ 0) (he2 : a + b - D ≤ 0)
    (he3 : b + (k : ℝ) - D ≤ 0) (h1 : 2 * r + 𝔠 * (2 * a - D) ≤ ξ) (h2 : r + 𝔠 * (a + b - D) ≤ ξ)
    (h3 : 𝔠 * (b + (k : ℝ) - D) ≤ ξ) :
    ((x ^ a * R) * ((x ^ a * R) + x ^ b) + x ^ b * x ^ k) * x ^ (-D) ≤ (P ^ 2 + P + 1) * N ^ ξ := by
  have hN0 : 0 < N := by linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hx
  have e1 : x ^ a * x ^ a * x ^ (-D) = x ^ (2 * a - D) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ a * x ^ b * x ^ (-D) = x ^ (a + b - D) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1
  have e3 : x ^ b * x ^ k * x ^ (-D) = x ^ (b + (k : ℝ) - D) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1
  have hexp : ((x ^ a * R) * ((x ^ a * R) + x ^ b) + x ^ b * x ^ k) * x ^ (-D) =
      R ^ 2 * x ^ (2 * a - D) + R * x ^ (a + b - D) + x ^ (b + (k : ℝ) - D) := by
    calc _ = R ^ 2 * (x ^ a * x ^ a * x ^ (-D)) + R * (x ^ a * x ^ b * x ^ (-D)) +
          x ^ b * x ^ k * x ^ (-D) := by ring
      _ = _ := by rw [e1, e2, e3]
  have hb1 : x ^ (2 * a - D) ≤ N ^ (𝔠 * (2 * a - D)) := QBudgetB_Wpow_le hN0 hx he1
  have hb2 : x ^ (a + b - D) ≤ N ^ (𝔠 * (a + b - D)) := QBudgetB_Wpow_le hN0 hx he2
  have hb3 : x ^ (b + (k : ℝ) - D) ≤ N ^ (𝔠 * (b + (k : ℝ) - D)) := QBudgetB_Wpow_le hN0 hx he3
  have hNr : 0 ≤ N ^ r := Real.rpow_nonneg hN0.le _
  have hsq : (N ^ r) ^ 2 = N ^ (2 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
  have t1 : R ^ 2 * x ^ (2 * a - D) ≤ P ^ 2 * N ^ ξ := by
    calc R ^ 2 * x ^ (2 * a - D) ≤ (P * N ^ r) ^ 2 * N ^ (𝔠 * (2 * a - D)) :=
          mul_le_mul (pow_le_pow_left₀ hR0 hRP 2) hb1 (by positivity) (by positivity)
      _ = P ^ 2 * N ^ (2 * r + 𝔠 * (2 * a - D)) := by
          rw [mul_pow, hsq, Real.rpow_add hN0]; ring
      _ ≤ P ^ 2 * N ^ ξ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h1) (by positivity)
  have t2 : R * x ^ (a + b - D) ≤ P * N ^ ξ := by
    calc R * x ^ (a + b - D) ≤ (P * N ^ r) * N ^ (𝔠 * (a + b - D)) :=
          mul_le_mul hRP hb2 (by positivity) (by positivity)
      _ = P * N ^ (r + 𝔠 * (a + b - D)) := by rw [Real.rpow_add hN0]; ring
      _ ≤ P * N ^ ξ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 h2) hP
  have t3 : x ^ (b + (k : ℝ) - D) ≤ N ^ ξ :=
    hb3.trans (Real.rpow_le_rpow_of_exponent_le hN1 h3)
  rw [hexp]
  nlinarith [t1, t2, t3]

/-- The last step of (he2), on plain reals: `Y ≤ M N^ξ` and `12 √(k M) N^{εq + k + ξ/2} ≤ N^{ε₀}` give
`N^{εq} (N^k √(k Y)) ≤ N^{ε₀}/12`. -/
private theorem QBudgetB_he2_final {N Y εq ε₀ ξ M : ℝ} {k : ℕ} (hN1 : 1 ≤ N) (hM : 0 ≤ M)
    (hY : Y ≤ M * N ^ ξ)
    (h : 12 * Real.sqrt ((k : ℝ) * M) * N ^ (εq + (k : ℝ) + ξ / 2) ≤ N ^ ε₀) :
    N ^ εq * (N ^ k * Real.sqrt ((k : ℝ) * Y)) ≤ N ^ ε₀ / 12 := by
  have hN0 : 0 < N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hs1 : Real.sqrt ((k : ℝ) * Y) ≤ Real.sqrt ((k : ℝ) * (M * N ^ ξ)) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hY hk0)
  have hsN : Real.sqrt (N ^ ξ) = N ^ (ξ / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; ring_nf
  have hs2 : Real.sqrt ((k : ℝ) * (M * N ^ ξ)) = Real.sqrt ((k : ℝ) * M) * N ^ (ξ / 2) := by
    rw [← mul_assoc, Real.sqrt_mul (by positivity), hsN]
  have hk : N ^ k = N ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hNk : 0 ≤ N ^ k := by positivity
  calc N ^ εq * (N ^ k * Real.sqrt ((k : ℝ) * Y))
      ≤ N ^ εq * (N ^ k * (Real.sqrt ((k : ℝ) * M) * N ^ (ξ / 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hs1.trans_eq hs2) hNk) hNe
    _ = Real.sqrt ((k : ℝ) * M) * N ^ (εq + (k : ℝ) + ξ / 2) := by
        rw [hk, Real.rpow_add hN0, Real.rpow_add hN0]; ring
    _ ≤ N ^ ε₀ / 12 := by linarith

/-- (he3, he4) `N^k N^{-D} ≤ N^{ε₀}/6` when `k - D < ε₀` (`budgetNonAltLinN.he3`, `he4` at
`D = D_Y`, `D = D_t`; RBM2D `NonAltEnd_ev_he4`, `NonAltEnd:573`). -/
private theorem QBudgetB_ev_he4 {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) (k : ℕ) {D ε₀ : ℝ}
    (hε : (k : ℝ) - D < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (QBudgetB_ev_polylog_le 0 hε 6),
    hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  simp only [pow_zero, mul_one] at h
  rw [← Real.rpow_natCast, ← Real.rpow_add hN0]
  have e : (k : ℝ) + -D = (k : ℝ) - D := by ring
  rw [e]
  linarith

/-- (ha1) `W^c N^{ε₁} ≤ N^{ε₀}/6` when `0 ≤ c`, `c + ε₁ < ε₀` (copy of `nqEnd_ev_ha1`, `NQEndLin.lean:173`). -/
private theorem QBudgetB_ev_ha1 {d : ℕ} (sz : Sizes d) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) {c ε₁ ε₀ : ℝ}
    (hc : 0 ≤ c) (hε : c + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  filter_upwards [hsize.eventually (QBudgetB_ev_rpow_le hε 6), hsize.eventually_ge_atTop 1] with n h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have h1 : ((sz.W n : ℕ) : ℝ) ^ c ≤ ((sz.size n : ℕ) : ℝ) ^ c :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (QBudgetB_W_le_size sz hd n) hc
  have hE1 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ := Real.rpow_nonneg hN0.le _
  rw [Real.rpow_add hN0] at h
  calc ((sz.W n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁
      ≤ ((sz.size n : ℕ) : ℝ) ^ c * ((sz.size n : ℕ) : ℝ) ^ ε₁ :=
        mul_le_mul_of_nonneg_right h1 hE1
    _ ≤ _ := by linarith

/-- (ha2) the two-term `Pa`: `W^a (W^b (N^{ε₁} N^{ε₁}) k + N^{τ_N}) Ls ≤ N^{ε₀}/12` when `0 ≤ a, b`,
`a + b + 2ε₁ < ε₀`, `a + τ_N < ε₀`, `Ls = (Im m(E n))⁻¹ log N`, eventually `κ' ≤ Im m(E n)`; each summand is
absorbed to `N^{ε₀}/24` (adapted from `nqEnd_ev_ha2`, `NQEndLin.lean:190`). -/
private theorem QBudgetB_ev_ha2 {d : ℕ} (sz : Sizes d) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ)
    {κ' : ℝ} (hκ' : 0 < κ') {E : ℕ → ℝ} (hκm : ∀ᶠ n : ℕ in atTop, κ' ≤ (mE (E n)).im)
    {a b ε₁ τN ε₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a + b + 2 * ε₁ < ε₀) (h2 : a + τN < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.W n : ℕ) : ℝ) ^ a * (((sz.W n : ℕ) : ℝ) ^ b *
        (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * (k : ℝ) +
          ((sz.size n : ℕ) : ℝ) ^ τN) * ((mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hsize.eventually (QBudgetB_ev_polylog_le 1 h1 (24 * ((k : ℝ) * κ'⁻¹))),
    hsize.eventually (QBudgetB_ev_polylog_le 1 h2 (24 * κ'⁻¹)), hsize.eventually_ge_atTop 1, hκm] with
    n hA hB hN1 hκ
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have him0 : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' hκ
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' hκ
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N := mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by positivity
  have hWa : ((sz.W n : ℕ) : ℝ) ^ a ≤ N ^ a :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (QBudgetB_W_le_size sz hd n) ha
  have hWb : ((sz.W n : ℕ) : ℝ) ^ b ≤ N ^ b :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (QBudgetB_W_le_size sz hd n) hb
  have hsq : N ^ ε₁ * N ^ ε₁ = N ^ (2 * ε₁) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have e1 : N ^ (a + b + 2 * ε₁) = N ^ a * N ^ b * (N ^ ε₁ * N ^ ε₁) := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, hsq]
  have e2 : N ^ (a + τN) = N ^ a * N ^ τN := Real.rpow_add hN0 _ _
  have hNa : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le _
  have hNb : 0 ≤ N ^ b := Real.rpow_nonneg hN0.le _
  have hNe : 0 ≤ N ^ ε₁ := Real.rpow_nonneg hN0.le _
  have hNt : 0 ≤ N ^ τN := Real.rpow_nonneg hN0.le _
  have step1 : ((sz.W n : ℕ) : ℝ) ^ a * (((sz.W n : ℕ) : ℝ) ^ b * (N ^ ε₁ * N ^ ε₁) * (k : ℝ) + N ^ τN) *
      ((mE (E n)).im⁻¹ * Real.log N) ≤
      N ^ a * (N ^ b * (N ^ ε₁ * N ^ ε₁) * (k : ℝ) + N ^ τN) * (κ'⁻¹ * Real.log N) := by
    refine mul_le_mul (mul_le_mul hWa (add_le_add (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hWb (by positivity)) hk0) le_rfl) (by positivity) hNa) hLs hLs0
      (by positivity)
  have step2 : N ^ a * (N ^ b * (N ^ ε₁ * N ^ ε₁) * (k : ℝ) + N ^ τN) * (κ'⁻¹ * Real.log N) =
      ((k : ℝ) * κ'⁻¹) * Real.log N * N ^ (a + b + 2 * ε₁) + κ'⁻¹ * Real.log N * N ^ (a + τN) := by
    rw [e1, e2]; ring
  have hT1 : ((k : ℝ) * κ'⁻¹) * Real.log N * N ^ (a + b + 2 * ε₁) ≤ N ^ ε₀ / 24 := by
    have h' : 24 * ((k : ℝ) * κ'⁻¹) * (1 + Real.log N) ^ 1 * N ^ (a + b + 2 * ε₁) ≤ N ^ ε₀ := hA
    rw [pow_one] at h'
    have : 0 ≤ ((k : ℝ) * κ'⁻¹) * N ^ (a + b + 2 * ε₁) := by positivity
    nlinarith
  have hT2 : κ'⁻¹ * Real.log N * N ^ (a + τN) ≤ N ^ ε₀ / 24 := by
    have h' : 24 * κ'⁻¹ * (1 + Real.log N) ^ 1 * N ^ (a + τN) ≤ N ^ ε₀ := hB
    rw [pow_one] at h'
    have : 0 ≤ κ'⁻¹ * N ^ (a + τN) := by positivity
    nlinarith
  calc _ ≤ _ := step1
    _ = _ := step2
    _ ≤ N ^ ε₀ / 12 := by linarith

/-- (ha3) `N^{εq} (W^a W^b N^{ε₁} √(k (Ls + 1))) ≤ N^{ε₀}/12` when `0 ≤ a, b`, `εq + a + b + ε₁ < ε₀`, eventually
`κ' ≤ Im m(E n)` (adapted from `nqEnd_ev_ha3`, `NQEndLin.lean:229`, with `c = a + b`; `√z ≤ z + 1`). -/
private theorem QBudgetB_ev_ha3 {d : ℕ} (sz : Sizes d) (hd : 1 ≤ d) (hsize : sz.SizeTendsto) (k : ℕ)
    {κ' : ℝ} (hκ' : 0 < κ') {E : ℕ → ℝ} (hκm : ∀ᶠ n : ℕ in atTop, κ' ≤ (mE (E n)).im)
    {a b ε₁ εq ε₀ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : εq + a + b + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.W n : ℕ) : ℝ) ^ a * ((sz.W n : ℕ) : ℝ) ^ b *
        ((sz.size n : ℕ) : ℝ) ^ ε₁ * Real.sqrt ((k : ℝ) * ((mE (E n)).im⁻¹ *
          Real.log ((sz.size n : ℕ) : ℝ) + 1))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  filter_upwards [hsize.eventually (QBudgetB_ev_polylog_le 1 hε
    (12 * ((k : ℝ) * κ'⁻¹ + k + 1))), hsize.eventually_ge_atTop 1, hκm] with n h hN1 hκ
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have him0 : 0 < (mE (E n)).im := lt_of_lt_of_le hκ' hκ
  have hIm : ((mE (E n)).im)⁻¹ ≤ κ'⁻¹ := inv_anti₀ hκ' hκ
  have hWa : ((sz.W n : ℕ) : ℝ) ^ a ≤ N ^ a :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (QBudgetB_W_le_size sz hd n) ha
  have hWb : ((sz.W n : ℕ) : ℝ) ^ b ≤ N ^ b :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (QBudgetB_W_le_size sz hd n) hb
  have hLs : (mE (E n)).im⁻¹ * Real.log N ≤ κ'⁻¹ * Real.log N :=
    mul_le_mul_of_nonneg_right hIm hlog0
  have hLs0 : 0 ≤ (mE (E n)).im⁻¹ * Real.log N := by positivity
  set Z : ℝ := (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N + 1) with hZ
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hsq : Real.sqrt Z ≤ Z + 1 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hZle : Z + 1 ≤ ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) := by
    have h1 : (k : ℝ) * ((mE (E n)).im⁻¹ * Real.log N) ≤ (k : ℝ) * (κ'⁻¹ * Real.log N) :=
      mul_le_mul_of_nonneg_left hLs hk0
    have h2 : 0 ≤ (k : ℝ) * κ'⁻¹ := by positivity
    have h3 : 0 ≤ ((k : ℝ) + 1) * Real.log N := by positivity
    rw [hZ]
    nlinarith
  have hrp : N ^ (εq + a + b + ε₁) = N ^ εq * N ^ a * N ^ b * N ^ ε₁ := by
    rw [Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_add hN0]
  have hNe : 0 ≤ N ^ εq := Real.rpow_nonneg hN0.le _
  have hN1' : 0 ≤ N ^ ε₁ := Real.rpow_nonneg hN0.le _
  have hNa : 0 ≤ N ^ a := Real.rpow_nonneg hN0.le _
  have hNb : 0 ≤ N ^ b := Real.rpow_nonneg hN0.le _
  have hWab : ((sz.W n : ℕ) : ℝ) ^ a * ((sz.W n : ℕ) : ℝ) ^ b ≤ N ^ a * N ^ b :=
    mul_le_mul hWa hWb (Real.rpow_nonneg (Nat.cast_nonneg _) _) hNa
  calc N ^ εq * (((sz.W n : ℕ) : ℝ) ^ a * ((sz.W n : ℕ) : ℝ) ^ b * N ^ ε₁ * Real.sqrt Z)
      ≤ N ^ εq * (N ^ a * N ^ b * N ^ ε₁ * (((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right hWab hN1')
          (hsq.trans hZle) (Real.sqrt_nonneg _) (by positivity)) hNe
    _ = ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) * N ^ (εq + a + b + ε₁) := by rw [hrp]; ring
    _ ≤ N ^ ε₀ / 12 := by
        have h' : 12 * ((k : ℝ) * κ'⁻¹ + k + 1) * (1 + Real.log N) ^ 1 * N ^ (εq + a + b + ε₁) ≤
            N ^ ε₀ := h
        rw [pow_one] at h'
        linarith

/-- (he0, and the `δD` part of he1) `N^k (W^C (c₀ W^{-D'})) ≤ N^{ε₀}/q` when `C ≤ D'`, `k + 𝔠 (C - D') < ε₀`
(`W^C W^{-D'} = W^{C-D'} ≤ N^{𝔠(C-D')}`; adapted from `nqEnd_ev_he1`, `NQEndLin.lean:276`, with a constant). -/
private theorem QBudgetB_ev_he0 {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {𝔠 : ℝ}
    (hband : sz.Bandwidth 𝔠) (k : ℕ) {C D' ε₀ c₀ q : ℝ} (hc₀ : 0 ≤ c₀) (hq : 0 < q) (hCD : C ≤ D')
    (hε : (k : ℝ) + 𝔠 * (C - D') < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * (((sz.W n : ℕ) : ℝ) ^ C *
        (c₀ * ((sz.W n : ℕ) : ℝ) ^ (-D'))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / q := by
  filter_upwards [hband, hsize.eventually (QBudgetB_ev_rpow_le hε (q * c₀)),
    hsize.eventually_ge_atTop 1] with n hW h hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hW
  have hmerge : ((sz.W n : ℕ) : ℝ) ^ C * ((sz.W n : ℕ) : ℝ) ^ (-D') =
      ((sz.W n : ℕ) : ℝ) ^ (C - D') := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have hle := QBudgetB_Wpow_le hN0 hW (show C - D' ≤ 0 by linarith)
  have hk : ((sz.size n : ℕ) : ℝ) ^ k = ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hrp : ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 𝔠 * (C - D')) =
      ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (C - D')) :=
    Real.rpow_add hN0 _ _
  rw [hrp] at h
  have hNk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := Real.rpow_nonneg hN0.le _
  have e : ((sz.W n : ℕ) : ℝ) ^ C * (c₀ * ((sz.W n : ℕ) : ℝ) ^ (-D')) =
      c₀ * ((sz.W n : ℕ) : ℝ) ^ (C - D') := by rw [← hmerge]; ring
  rw [e, hk]
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * (c₀ * ((sz.W n : ℕ) : ℝ) ^ (C - D')) ≤
      ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * (c₀ * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (C - D'))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle hc₀) hNk
  rw [le_div_iff₀ hq]
  nlinarith [h1, h]

/-- (he1, `b` part) `N^k (W^a ((1 + g²) N)^k W^{-D'+C_n}) ≤ N^{ε₀}/24` when `a + C_n ≤ D'`,
`2k + 𝔠 (a + C_n - D') < ε₀`, eventually `0 < g ≤ Λg` (`((1+g²)N)^k ≤ (1+Λg²)^k N^k`,
`W^a W^{-D'+C_n} = W^{a + C_n - D'} ≤ N^{𝔠(a + C_n - D')}`). -/
private theorem QBudgetB_ev_he1b {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {𝔠 : ℝ}
    (hband : sz.Bandwidth 𝔠) (k : ℕ) {Λg : ℝ} (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    {a Cn D' ε₀ : ℝ} (hD : a + Cn ≤ D') (hε : 2 * (k : ℝ) + 𝔠 * (a + Cn - D') < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * (((sz.W n : ℕ) : ℝ) ^ a *
        ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k * ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 24 := by
  set P : ℝ := (1 + Λg ^ 2) ^ k with hP
  have hP0 : 0 ≤ P := by positivity
  filter_upwards [hband, hlam, hsize.eventually (QBudgetB_ev_rpow_le hε (24 * P)),
    hsize.eventually_ge_atTop 1] with n hW hg h hN1
  obtain ⟨hg0, hgΛ⟩ := hg
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hW
  have hR0 : 0 ≤ ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k := by positivity
  have hR : ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k ≤ P * ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := by
    have h2' : ((sz.size n : ℕ) : ℝ) ^ k = ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
    rw [mul_pow, h2']
    have h1' : (1 + sz.lam n ^ 2) ^ k ≤ P :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    exact mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg hN0.le _)
  have hmerge : ((sz.W n : ℕ) : ℝ) ^ a * ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) =
      ((sz.W n : ℕ) : ℝ) ^ (a + Cn - D') := by
    rw [← Real.rpow_add hWpos]; ring_nf
  have hle := QBudgetB_Wpow_le hN0 hW (show a + Cn - D' ≤ 0 by linarith)
  have hk : ((sz.size n : ℕ) : ℝ) ^ k = ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
  have hNk : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := Real.rpow_nonneg hN0.le _
  have hWe : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (a + Cn - D') := Real.rpow_nonneg hWpos.le _
  have e : ((sz.W n : ℕ) : ℝ) ^ a * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k *
      ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) =
      ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k * ((sz.W n : ℕ) : ℝ) ^ (a + Cn - D') := by
    rw [← hmerge]; ring
  rw [e, hk]
  have hNs : ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 𝔠 * (a + Cn - D')) =
      ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) *
        ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (a + Cn - D')) := by
    rw [Real.rpow_add hN0, two_mul, Real.rpow_add hN0]
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * (((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k *
      ((sz.W n : ℕ) : ℝ) ^ (a + Cn - D')) ≤ P * (((sz.size n : ℕ) : ℝ) ^ (k : ℝ) *
        ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (a + Cn - D'))) := by
    calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) * ((P * ((sz.size n : ℕ) : ℝ) ^ (k : ℝ)) *
          ((sz.size n : ℕ) : ℝ) ^ (𝔠 * (a + Cn - D'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hR hle hWe (by positivity)) hNk
      _ = _ := by ring
  rw [← hNs] at h1
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 24)]
  nlinarith [h1, h]

/-- (he2) `N^{εq} (N^k √(k · qvFar' · W^{-D})) ≤ N^{ε₀}/12`, `qvFar' = W^a R (W^a R + W^b) + W^b W^k` with
`R = ((1+g²)N)^k`, `a = C₄ε`, `b = C₄`, `D = D'' - C_Q` (adapted from `nqEnd_ev_he2`, `NQEndLin.lean:397`, at
`r = k`, since `kappaAltQN` has exponent `k`, not `k - 1`). -/
private theorem QBudgetB_ev_he2 {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {𝔠 : ℝ}
    (hband : sz.Bandwidth 𝔠) (k : ℕ) {Λg a b D εq ε₀ ξ : ℝ}
    (hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg)
    (he1 : 2 * a - D ≤ 0) (he2 : a + b - D ≤ 0) (he3 : b + (k : ℝ) - D ≤ 0)
    (h1 : 2 * (k : ℝ) + 𝔠 * (2 * a - D) ≤ ξ) (h2 : (k : ℝ) + 𝔠 * (a + b - D) ≤ ξ)
    (h3 : 𝔠 * (b + (k : ℝ) - D) ≤ ξ) (hξ : εq + (k : ℝ) + ξ / 2 < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
        Real.sqrt ((k : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ a * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k *
          (((sz.W n : ℕ) : ℝ) ^ a * ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k +
            ((sz.W n : ℕ) : ℝ) ^ b) + ((sz.W n : ℕ) : ℝ) ^ b * ((sz.W n : ℕ) : ℝ) ^ k) *
          ((sz.W n : ℕ) : ℝ) ^ (-D)))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  set P : ℝ := (1 + Λg ^ 2) ^ k with hP
  have hP0 : 0 ≤ P := by positivity
  set M : ℝ := P ^ 2 + P + 1 with hM
  have hM0 : 0 ≤ M := by positivity
  filter_upwards [hband, hlam, hsize.eventually (QBudgetB_ev_rpow_le hξ (12 * Real.sqrt ((k : ℝ) * M))),
    hsize.eventually_ge_atTop 1] with n hW hg h hN1
  obtain ⟨hg0, hgΛ⟩ := hg
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hR0 : 0 ≤ ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k := by positivity
  have hR : ((1 + sz.lam n ^ 2) * ((sz.size n : ℕ) : ℝ)) ^ k ≤ P * ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := by
    have h2' : ((sz.size n : ℕ) : ℝ) ^ k = ((sz.size n : ℕ) : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
    rw [mul_pow, h2']
    have h1' : (1 + sz.lam n ^ 2) ^ k ≤ P :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    exact mul_le_mul_of_nonneg_right h1' (Real.rpow_nonneg hN0.le _)
  have hbound := QBudgetB_he2_bound (x := ((sz.W n : ℕ) : ℝ)) (N := ((sz.size n : ℕ) : ℝ))
    (a := a) (b := b) (D := D) (𝔠 := 𝔠) (ξ := ξ) (r := (k : ℝ)) (k := k) hN1 hW hR0 hR hP0 he1 he2 he3
    h1 h2 h3
  exact QBudgetB_he2_final hN1 hM0 hbound h

/-! ## 3. Targets 5-6: the exponent choice and the eventual absorptions -/

/-- Target 5: an explicit admissible choice of the exponents (`ξ = -(2k+1)`; monotone in `D'`, `D''`, `D_Y`,
`D_t`; `ε`, `ε'`, `ε₁`, `εq`, `τN` small against `ε₀`), so the conditions are not vacuous for any positive
`C₄`, `C_n`, `𝔠`, `ε₀`. -/
theorem altBudgetExpQN_of_choice :
  ∀ (k : ℕ) (C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ : ℝ),
    0 < C4 → 0 < Cn → 0 < 𝔠 → 0 < ε₀ → 0 < ε → ε ≤ 1 / 2 →
    C4 * ε ≤ ε₀ / 8 → Cn * ε ≤ ε₀ / 8 → 0 ≤ ε' → Cn * ε' ≤ ε₀ / 8 →
    ε₁ ≤ ε₀ / 8 → εq ≤ ε₀ / 8 → τN ≤ ε₀ / 8 →
    C4 + Cn + (2 * (k : ℝ) + 1) / 𝔠 ≤ D' →
    2 * Cn + 2 + 2 * C4 + (k : ℝ) + (4 * (k : ℝ) + 1) / 𝔠 ≤ D'' →
    (k : ℝ) ≤ D_Y → (k : ℝ) ≤ D_t →
      altBudgetExpQN k C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ (-(2 * (k : ℝ) + 1)) := by
  intro k C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ hC4 hCn h𝔠 hε₀ hε hε2 hC4ε hCnε hε' hCnε' hε₁ hεq hτN hD' hD''
    hDY hDt
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨q1, hq1d⟩ : ∃ q1 : ℝ, q1 = (2 * (k : ℝ) + 1) / 𝔠 := ⟨_, rfl⟩
  obtain ⟨q2, hq2d⟩ : ∃ q2 : ℝ, q2 = (4 * (k : ℝ) + 1) / 𝔠 := ⟨_, rfl⟩
  have hq1 : 𝔠 * q1 = 2 * (k : ℝ) + 1 := by rw [hq1d]; field_simp
  have hq2 : 𝔠 * q2 = 4 * (k : ℝ) + 1 := by rw [hq2d]; field_simp
  have hq1p : 0 < q1 := by rw [hq1d]; positivity
  have hq2p : 0 < q2 := by rw [hq2d]; positivity
  rw [← hq1d] at hD'
  rw [← hq2d] at hD''
  have hCε : C4 * ε ≤ C4 := by
    have := mul_le_mul_of_nonneg_left (show ε ≤ 1 by linarith) hC4.le
    linarith
  have hCε0 : 0 ≤ C4 * ε := by positivity
  have hCnε0 : 0 ≤ C4 * ε := hCε0
  have h𝔠k : 0 ≤ 𝔠 * (k : ℝ) := mul_nonneg h𝔠.le hk0
  have h𝔠C4 : 0 ≤ 𝔠 * C4 := mul_nonneg h𝔠.le hC4.le
  have a9 := mul_le_mul_of_nonneg_left (show C4 - D' ≤ -Cn - q1 by linarith) h𝔠.le
  have a11 := mul_le_mul_of_nonneg_left (show C4 * ε + Cn - D' ≤ -q1 by linarith) h𝔠.le
  have a15 := mul_le_mul_of_nonneg_left
    (show 2 * (C4 * ε) - (D'' - (2 * Cn + 2)) ≤ -(k : ℝ) - q2 by linarith) h𝔠.le
  have a16 := mul_le_mul_of_nonneg_left
    (show C4 * ε + C4 - (D'' - (2 * Cn + 2)) ≤ -(k : ℝ) - q2 by linarith) h𝔠.le
  have a17 := mul_le_mul_of_nonneg_left
    (show C4 + (k : ℝ) - (D'' - (2 * Cn + 2)) ≤ -C4 - q2 by linarith) h𝔠.le
  have hCnε0 : 0 ≤ Cn * ε := by positivity
  have hCnε'0 : 0 ≤ Cn * ε' := mul_nonneg hCn.le hε'
  have f9 : (k : ℝ) + 𝔠 * (C4 - D') < ε₀ := by
    have := mul_pos h𝔠 hCn
    linarith
  have f11 : 2 * (k : ℝ) + 𝔠 * (C4 * ε + Cn - D') < ε₀ := by linarith
  have f15 : 2 * (k : ℝ) + 𝔠 * (2 * (C4 * ε) - (D'' - (2 * Cn + 2))) ≤ -(2 * (k : ℝ) + 1) := by linarith
  have f16 : (k : ℝ) + 𝔠 * (C4 * ε + C4 - (D'' - (2 * Cn + 2))) ≤ -(2 * (k : ℝ) + 1) := by linarith
  have f17 : 𝔠 * (C4 + (k : ℝ) - (D'' - (2 * Cn + 2))) ≤ -(2 * (k : ℝ) + 1) := by linarith
  exact ⟨hCε0, hCnε0, hCnε'0, by linarith, by linarith, by linarith, by linarith, by linarith, f9,
    by linarith, f11, by linarith, by linarith, by linarith, f15, f16, f17, by linarith, by linarith,
    by linarith⟩

/-- Target 6 (the theorem S3-18a consumes): the eight hypotheses of `budgetAltQN` at the linear level hold
eventually, from `SizeTendsto`, `Bandwidth 𝔠`, `κ' ≤ Im m(E n)` and `0 < g ≤ Λg` eventually, and the exponent
conditions at `C₄ = qProxy4C d (m+2) Λg κ' KL`, `C_n = qProxyCn d (m+1) Λg KL C c`. -/
theorem altBudgetNumQN_eventually :
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (m : ℕ)
    (Λg κ' KL C c 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ : ℝ),
    1 ≤ d → sz.SizeTendsto → sz.Bandwidth 𝔠 → 0 < κ' →
    (∀ᶠ n : ℕ in atTop, κ' ≤ (mE (E n)).im) →
    (∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg) →
    altBudgetExpQN (m + 1 + 1) (qProxy4C d (m + 1 + 1) Λg κ' KL) (qProxyCn d (m + 1) Λg KL C c) 𝔠
      ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ →
    ∀ᶠ n : ℕ in atTop, altBudgetNumQN sz E n m Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ := by
  intro d sz E m Λg κ' KL C c 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ hd hsize hband hκ' hκm hlam hexp
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20⟩ := hexp
  have eD : -D'' + qProxyCQ d (m + 1) Λg KL C c = -(D'' - (2 * qProxyCn d (m + 1) Λg KL C c + 2)) := by
    unfold qProxyCQ; ring
  have r1 := QBudgetB_ev_ha1 sz hd hsize g1 g4
  have r2 := QBudgetB_ev_ha2 sz hd hsize (m + 1 + 1) hκ' hκm g1 g3 g5 g6
  have r3 := QBudgetB_ev_ha3 sz hd hsize (m + 1 + 1) hκ' hκm g1 g2 g7
  have r4 := QBudgetB_ev_he0 sz hsize hband (m + 1 + 1) (c₀ := 2) (q := 12) (by norm_num) (by norm_num) g8 g9
  have r5a := QBudgetB_ev_he1b sz hsize hband (m + 1 + 1) hlam g10 g11
  have r5b := QBudgetB_ev_he0 sz hsize hband (m + 1 + 1) (c₀ := 4) (q := 24) (by norm_num) (by norm_num) g8 g9
  have r6 := QBudgetB_ev_he2 sz hsize hband (m + 1 + 1) hlam
    (a := qProxy4C d (m + 1 + 1) Λg κ' KL * ε) (b := qProxy4C d (m + 1 + 1) Λg κ' KL)
    (D := D'' - (2 * qProxyCn d (m + 1) Λg KL C c + 2)) g12 g13 g14 g15 g16 g17 g18
  have r7 := QBudgetB_ev_he4 sz hsize (m + 1 + 1) g19
  have r8 := QBudgetB_ev_he4 sz hsize (m + 1 + 1) g20
  filter_upwards [r1, r2, r3, r4, r5a, r5b, r6, r7, r8] with n s1 s2 s3 s4 s5a s5b s6 s7 s8
  refine ⟨s1, s2, s3, s4, ?_, ?_, s7, s8⟩
  · unfold altBudget_kapFar
    rw [mul_add]
    linarith
  · unfold altBudget_qvFar altBudget_kapFar
    rw [eD]
    exact s6


/-! ## 4. Compiled nonempty instances (namespace `QBudgetBInst`)

Targets 1-4 at the data of `QLevelsBInst` (`QLevelsB.lean:307-582`): the merged admissible sequence `sz0` (`d = 3`,
`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at `n = 4` (`x = 10`, `L = 20`, `W = 10^5`,
`N = (W L)^3 = 8·10^18`, `lam = 10^{-6}`), `m = 2` (tensors of `k = 4` indices), `K_L = 2`, `Λ_g = 1`, `E = 0`,
`u = 0`, `κ = 1`, `H = 0`, `σ = ![T, F, T, F]`, the crude `GoodSetN` levels `(Γc, Λc, Φc) = (4, 100, 1)`, the
`GoodLinN` levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, 16, 1)` (`goodSetN_subset_goodLinN`, `Φ₂ = kΓΦ² = 16`), `τ' = 1/10`,
`ε' = 1/5`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, `C = Cmol3`, `c = 1/2`.  The premise `hY` of targets 1-2 is
discharged by `goodSetN_LKM_le` (`4 ≤ ν X = W`).  Targets 5-6: `k = 3` (`m = 1`), `Λ_g = 1`, `κ' = 24/25`,
`K_L = 1`, `C = 1`, `c = 1/2`, `𝔠 = 1/6`, `ε₀ = 1`, `ε₁ = εq = τ_N = 1/8`, `D' = C₄ + C_n + 42`,
`D'' = 2C_n + 2 + 2C₄ + 3 + 78`, `D_Y = D_t = 3`, `ε = min (1/(8(C₄ + C_n))) (1/2)`, `ε' = 1/(8 C_n)`, with the abstract
positive constants `C₄ = qProxy4C 3 3 1 (24/25) 1`, `C_n = qProxyCn 3 2 1 1 1 (1/2)`; target 6 at `sz0`, `E ≡ 1/2`
(`Im m = √15/4 ≥ 24/25`).  The numeric helpers are copies of the private ones of `QLevelsBInst` and `QBudgetAInst`. -/

namespace QBudgetBInst

open RBM.Gauss.SizesInst

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

/-- The numeric hypotheses of the instances at `n` with `x = 2(n+1) ≥ 10` (copy of `QDriftBInst.numeric`). -/
private theorem numeric (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have hW110 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine ⟨by rw [hxW]; nlinarith [pow_le_pow_left₀ (by norm_num) hx 5], ?_, ?_, ?_⟩
  · rw [hW15]; linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hW110]
    push_cast
    nlinarith

/-- The constants of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m' = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- `0 ∈ GoodSetN` at `E = 0`, `u = 0`, `k = 4` with the levels `(Γ, Λ, Φ) = (4, 100, 1)` (`Γ² Λ = 1600 ≥ 4 · 2^8`),
every `τ'`, `D'` (copy of `QDriftBInst.zero_mem_inst`). -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 τ' D' := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

private abbrev H0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ := 0

private theorem hx4 : (10 : ℝ) ≤ 2 * (((4 : ℕ) : ℝ) + 1) := by norm_num

private theorem W4 : ((sz0.W 4 : ℕ) : ℝ) = 100000 := by
  rw [(sz0_facts 4).1]; norm_num

private theorem N4 : ((sz0.size 4 : ℕ) : ℝ) = 8000000000000000000 := by
  have : sz0.size 4 = 8000000000000000000 := by norm_num [Sizes.size, sz0]
  exact_mod_cast this

private theorem W10_4 : ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt 10 := by
  rw [(sz0_facts 4).1, rpow_pow5 (by positivity), show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt10_pow6 : (Real.sqrt 10) ^ (3 * 2) = 1000 := by
  rw [show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The alternating sign pattern of the instances. -/
private abbrev σalt : Fin (2 + 1 + 1) → Bool := ![true, false, true, false]

private theorem σalt_last : σalt (Fin.last (2 + 1)) = !σalt 0 := by decide

private theorem hFv4 : ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤
    ((sz0.W 4 : ℕ) : ℝ) * (((sz0.size 4 : ℕ) : ℝ) ^ (2 * 2 + 4))⁻¹ := by
  rw [W4, N4, Real.rpow_neg (by norm_num), show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem hMΛ4 : (2 * ((2 : ℕ) : ℝ) + 5) * (3 * 4 ^ (3 * 2) * (2 / Real.sqrt 1) * Cmol3 *
    ((sz0.W 4 : ℕ) : ℝ) ^ 2) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [W4, N4, Real.rpow_two, Real.sqrt_one]
  norm_num

private theorem hNu4 : (((sz0.size 4 : ℕ) : ℝ))⁻¹ ≤ 1 - 0 := by
  rw [N4]; norm_num

/-- `0 ∈ GoodLinN` at the levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, kΓΦ², 1)`, `k = 4` (`goodSetN_subset_goodLinN`). -/
private theorem zero_mem_lin (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      GoodLinN sz0 n 0 0 (3 + 1) 4 1 (((3 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 :=
  goodSetN_subset_goodLinN sz0 n 0 0 (3 + 1) 4 100 1 τ' D' (zero_mem_inst n hlam1 τ' D')

/-- The premise `hY` of targets 1-2 at the data: `‖(𝓛-𝒦)^{(j)}‖ ≤ ν X B^{m+1}` with `ν = W`, `X = 1`, `j = m + 1 = 3`
(`goodSetN_LKM_le`, `4 ≤ W`). -/
private theorem hY4 : ∀ (σ' : Fin (2 + 1) → Bool) (a' : Fin (2 + 1) → Zd 3 (sz0.L 4)),
    ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) * 1 * sz0.Bctl 4 0 ^ (2 + 1) := by
  intro σ' a'
  have h := (goodSetN_LKM_le 3 sz0 4 0 0 (2 + 1 + 1) 4 100 1 (1 / 10) 40 H0
    (zero_mem_inst 4 (lam_le_one 4) _ _) (by norm_num) (2 + 1) (by omega) (by omega)).2 σ' a'
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_pos (STBctl_pos sz0 4 (by norm_num)) _).le)
  rw [W4]; norm_num

/-- **Instance of target 1** (`dFlowQN_levelLin`): `d = 3`, `m = 2`, `Λ_g = 1`, `K_L = 2`, the explicit mollifier
(`C = Cmol3`, `c = 1/2`), `n = 4`, `E = 0`, `u = 0`, `H = 0` in `GoodSetN` at `(4, 100, 1)` and in `GoodLinN` at
`(4, 1, 16, 1)`, `κ = 1`, `τ' = 1/10`, `ε' = 1/5`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, alternating `σ`, every
label `a`; every deterministic hypothesis is discharged. -/
theorem dFlowQN_levelLin_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖dFlowQN sz0 4 0 0 (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt H0 a‖ ≤
      dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1
        (qProxyCn 3 (2 + 1) 1 2 Cmol3 (1 / 2)) (1 / 5) 40 2 1 := by
  obtain ⟨hW, hWε, hLK, hdW⟩ := numeric 4 hx4
  exact dFlowQN_levelLin 3 2 1 2 Cmol3 (1 / 2) (le_refl 3) one_pos (by norm_num) (by positivity)
    (by norm_num) sz0 4 0 0 1 4 100 1 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 (1 / 10) (1 / 5) 40
    (((sz0.W 4 : ℕ) : ℝ)) 1 2 H0 σalt _
    one_pos (by norm_num) le_rfl (by norm_num) (lam_pos_n 4) (lam_le_one 4) hNu4 hW (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hWε hLK hdW (by linarith) le_rfl
    (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4
    hMΛ4 (QopAlgebra_mollifier_props 3 (sz0.L 4) 3 (sz0.three_le_L 4) (lam_pos_n 4))
    (zero_mem_inst 4 (lam_le_one 4) _ _) (zero_mem_lin 4 (lam_le_one 4) (1 / 10) 40) hY4 σalt_last a

/-- **Instance of target 2** (`alt_hdriftLinQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4` (so `H_0 = 0`,
`u_0 = 0`), the stopping time `τ ≡ 1` (`H_0 ∈ GoodSetN ∩ GoodLinN` for `j < τ`), levels `(Γ, Λ, Φ) = (4, 100, 1)`,
`(Φ₁, Φ₂, Φ₃) = (1, 16, 1)`, `Λ_g = 1`, `K_L = 2`, `n = 4`, the alternating `σ`, every path `ω`, `j = 0` and every
label `b`. -/
theorem alt_hdriftLinQN_instance :
    ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)),
      ‖dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω b‖ ≤
        dDriftAltLinQN sz0 4 0
          (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 0) 2 4 1
          (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1
          (qProxyCn 3 (2 + 1) 1 2 ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))) (1 / 2))
          (1 / 5) 40 2 1 := by
  obtain ⟨hW, hWε, hLK, hdW⟩ := numeric 4 hx4
  intro ω b
  refine alt_hdriftLinQN 3 2 1 2 (le_refl 3) one_pos (by norm_num) sz0 4 σalt (fun _ => (0 : ℝ))
    (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => ((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) (fun _ => 1) 1 (1 / 10) (1 / 5) 40
    (((sz0.W 4 : ℕ) : ℝ)) 1 2 (fun _ => 1)
    one_pos (by norm_num) (lam_pos_n 4) (lam_le_one 4) le_rfl (by norm_num) (by norm_num)
    (by rw [N4]; norm_num) hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) hWε hLK hdW
    (by linarith) le_rfl (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4 ?_
    σalt_last ?_ ?_ ω 0 (by norm_num) (by norm_num) b
  · rw [W4, N4, Real.rpow_two, Real.sqrt_one]
    norm_num
  · intro ω' j hj
    have hj0 : j = 0 := by
      have : j < 1 := hj
      omega
    subst hj0
    rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ 4 rfl ω', ST_gridTime_zero]
    exact ⟨zero_mem_inst 4 (lam_le_one 4) _ _, zero_mem_lin 4 (lam_le_one 4) (1 / 10) 40⟩
  · intro ω' j hj σ' a'
    have hj0 : j = 0 := by
      have : j < 1 := hj
      omega
    subst hj0
    rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ 4 rfl ω', ST_gridTime_zero]
    exact hY4 σ' a'

/-- **Instance of target 3** (`dDriftAltLinQN_nonneg`): `n = 4`, `E = 0`, `u = 0`, `m = 2`, the levels
`(Γ, Φ₁, Φ₂, Φ₃, X) = (4, 1, 16, 1, 1)`, `C_n = 1`, `ε' = 1/5`, `D' = 40`, `τ_N = 2`. -/
theorem dDriftAltLinQN_nonneg_instance :
    0 ≤ dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 1 (1 / 5) 40 2 1 :=
  dDriftAltLinQN_nonneg sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 1 (1 / 5) 40 2 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Instance of target 4** (`dDriftAltQN_eq_lin`) at the same data: the merged level `dDriftAltQN` at `(Γ, Φ) = (4, 1)`
equals the linear level at `(1, kΓΦ², 1) = (1, 16, 1)`. -/
theorem dDriftAltQN_eq_lin_instance :
    dDriftAltQN sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1 =
      dDriftAltLinQN sz0 4 0 0 2 4 1 (((2 + 1 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 1 (1 / 5) 40 2 1 :=
  dDriftAltQN_eq_lin sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1

/-! ### Targets 5-6 -/

private theorem im_ge : (24 / 25 : ℝ) ≤ (mE (1 / 2)).im := by
  rw [mE_im]
  have : (48 / 25 : ℝ) ≤ Real.sqrt (4 - (1 / 2) ^ 2) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num
  linarith

private noncomputable abbrev C4i : ℝ := qProxy4C 3 (1 + 1 + 1) 1 (24 / 25) 1
private noncomputable abbrev Cni : ℝ := qProxyCn 3 (1 + 1) 1 1 1 (1 / 2)
private noncomputable abbrev εi : ℝ := min (1 / (8 * (C4i + Cni))) (1 / 2)
private noncomputable abbrev ε'i : ℝ := 1 / (8 * Cni)
private noncomputable abbrev D'i : ℝ := C4i + Cni + 42
private noncomputable abbrev D''i : ℝ := 2 * Cni + 2 + 2 * C4i + 3 + 78

private theorem C4i_pos : 0 < C4i :=
  qProxy4C_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem Cni_pos : 0 < Cni :=
  qProxyCn_pos (by norm_num) _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

private theorem εi_pos : 0 < εi := lt_min (by have := C4i_pos; have := Cni_pos; positivity) (by norm_num)

private theorem εi_le : εi ≤ 1 / 2 := min_le_right _ _

private theorem C4εi_le : C4i * εi ≤ 1 / 8 := by
  have h1 : C4i * εi ≤ C4i * (1 / (8 * (C4i + Cni))) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) C4i_pos.le
  have h2 : C4i * (1 / (8 * (C4i + Cni))) ≤ 1 / 8 := by
    have := C4i_pos; have := Cni_pos
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  exact h1.trans h2

private theorem Cnεi_le : Cni * εi ≤ 1 / 8 := by
  have h1 : Cni * εi ≤ Cni * (1 / (8 * (C4i + Cni))) :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) Cni_pos.le
  have h2 : Cni * (1 / (8 * (C4i + Cni))) ≤ 1 / 8 := by
    have := C4i_pos; have := Cni_pos
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  exact h1.trans h2

private theorem ε'i_nonneg : 0 ≤ ε'i := by have := Cni_pos; positivity

private theorem Cnε'i_le : Cni * ε'i ≤ 1 / 8 := by
  have := Cni_pos
  have : Cni * ε'i = 1 / 8 := by
    change Cni * (1 / (8 * Cni)) = 1 / 8
    field_simp
  linarith

/-- **Instance of target 5** (`altBudgetExpQN_of_choice`) at `k = 3`, `𝔠 = 1/6`, `ε₀ = 1`, with the abstract positive
constants `C₄ = qProxy4C 3 3 1 (24/25) 1`, `C_n = qProxyCn 3 2 1 1 1 (1/2)`: the twenty exponent conditions hold at
`ε = min (1/(8(C₄+C_n))) (1/2)`, `ε' = 1/(8C_n)`, `ε₁ = εq = τ_N = 1/8`, `D' = C₄ + C_n + 42`,
`D'' = 2C_n + 2 + 2C₄ + 81`, `D_Y = D_t = 3`, `ξ = -7`. -/
theorem altBudgetExpQN_of_choice_instance :
    altBudgetExpQN (1 + 1 + 1) C4i Cni (1 / 6) εi ε'i (1 / 8) D'i D''i 3 3 (1 / 8) 1 (1 / 8)
      (-(2 * ((1 + 1 + 1 : ℕ) : ℝ) + 1)) :=
  altBudgetExpQN_of_choice (1 + 1 + 1) C4i Cni (1 / 6) εi ε'i (1 / 8) D'i D''i 3 3 (1 / 8) 1 (1 / 8)
    C4i_pos Cni_pos (by norm_num) one_pos εi_pos εi_le (by simpa using C4εi_le) (by simpa using Cnεi_le)
    ε'i_nonneg (by simpa using Cnε'i_le) (by norm_num) (by norm_num) (by norm_num)
    (by push_cast; unfold D'i; norm_num) (by push_cast; unfold D''i; norm_num) (by push_cast; norm_num)
    (by push_cast; norm_num)

/-- **Instance of target 6** (`altBudgetNumQN_eventually`) at `sz0` (`SizeTendsto` by `sz0_tendsto`, `Bandwidth 1/6` by
`sz0_bandwidth`), `E ≡ 1/2` (`κ' = 24/25 ≤ Im m(1/2) = √15/4`), `m = 1` (`k = 3`), `Λ_g = 1`, `K_L = 1`, `C = 1`,
`c = 1/2`, and the exponents of target 5: there is an `n` at which all eight inequalities `ha1`-`he4` hold. -/
theorem altBudgetNumQN_eventually_instance :
    ∃ n : ℕ, altBudgetNumQN sz0 (fun _ => (1 / 2 : ℝ)) n 1 1 (24 / 25) 1 1 (1 / 2) εi ε'i (1 / 8) D'i D''i 3 3
      (1 / 8) 1 (1 / 8) :=
  (altBudgetNumQN_eventually sz0 (fun _ => (1 / 2 : ℝ)) 1 1 (24 / 25) 1 1 (1 / 2) (1 / 6) εi ε'i (1 / 8) D'i
    D''i 3 3 (1 / 8) 1 (1 / 8) (-(2 * ((1 + 1 + 1 : ℕ) : ℝ) + 1)) (by norm_num) sz0_tendsto sz0_bandwidth
    (by norm_num) (Eventually.of_forall fun _ => im_ge)
    (Eventually.of_forall fun n => ⟨lam_pos_n n, lam_le_one n⟩) altBudgetExpQN_of_choice_instance).exists

/-- **Consumer check** (CLAUDE.md §45 O2; compiled): S3-18a obtains the eight hypotheses of `budgetAltQN` from one
`altBudgetNumQN` and passes them with `Pa = W^{C_n ε'}(N^{ε₁}N^{ε₁})k + N^{τ_N}`, `b = W^{-D'+C_n}`,
`δ0 = 2W^{-D'}`, `δD = 4W^{-D'}`; the other hypotheses of `budgetAltQN` stay hypotheses of this example. -/
example {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ)
    (Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ τK X0 Φd : ℝ) (Γ Λ dd : ℕ → ℝ)
    (a : Fin (m + 1 + 1) → Zd d (sz.L n))
    (h : altBudgetNumQN sz E n m Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁)
    (hε₁ : 0 ≤ ε₁) (hE : |E n| < 2) (hs0 : 0 ≤ s n) (hsv : s n ≤ v n) (hv1 : v n < 1) (hK : K n ≠ 0)
    (hη : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hΔη : gridStep s v K n * (etaT (E n) (v n))⁻¹ ≤ 1)
    (hΓ : Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁) (hΛ : 1 ≤ Λ n)
    (hPa : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε') *
      (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
        ((sz.size n : ℕ) : ℝ) ^ τN)
    (hΦd : 0 ≤ Φd) (hb : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL C c))
    (hδ0 : 0 ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (hδD : 0 ≤ 4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
    (hdd : ∀ j < K n, dd j ≤ (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε') *
        (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
          ((sz.size n : ℕ) : ℝ) ^ τN) * Φd * ((sz.Bctl n (gridTime s v K n j)) ^ (m + 1 + 1) /
        etaT (E n) (gridTime s v K n j)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL C c))
    (hlog : ∑ j ∈ Finset.range (K n), gridStep s v K n / etaT (E n) (gridTime s v K n j) ≤
      (mE (E n)).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ))
    (hX0 : X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1))
    (hR : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ (m + 1 + 1) *
        stepErrN d (sz.L n) (sz.W n) (E n) (m + 1 + 1) (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ^ (m + 1 + 1)) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-D_t)) :
    assembledRHSAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd (2 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
        (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y τK εq X0 a ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φd) * (sz.Bctl n (v n)) ^ (m + 1 + 1) := by
  obtain ⟨ha1, ha2, ha3, he0, he1, he2, he3, he4⟩ := h
  exact budgetAltQN sz E s v K n m Λg κ' KL C c ε Γ Λ dd
    (((sz.W n : ℕ) : ℝ) ^ (qProxyCn d (m + 1) Λg KL C c * ε') *
      (((sz.size n : ℕ) : ℝ) ^ ε₁ * ((sz.size n : ℕ) : ℝ) ^ ε₁) * ((m + 1 + 1 : ℕ) : ℝ) +
        ((sz.size n : ℕ) : ℝ) ^ τN) Φd (((sz.W n : ℕ) : ℝ) ^ (-D' + qProxyCn d (m + 1) Λg KL C c))
    (2 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) D'' D_Y D_t τK εq ε₀ ε₁ X0 a
    hε₁ hE hs0 hsv hv1 hK hη hΔη hΓ hΛ hPa hΦd hb hδ0 hδD hdd hlog hX0 hR
    ha1 ha2 ha3 he0 he1 he2 he3 he4

end QBudgetBInst

end RBM.Ind

end

#print axioms RBM.Ind.altBudgetNumQN
#print axioms RBM.Ind.altBudgetExpQN
#print axioms RBM.Ind.dFlowQN_levelLin
#print axioms RBM.Ind.alt_hdriftLinQN
#print axioms RBM.Ind.dDriftAltLinQN_nonneg
#print axioms RBM.Ind.dDriftAltQN_eq_lin
#print axioms RBM.Ind.altBudgetExpQN_of_choice
#print axioms RBM.Ind.altBudgetNumQN_eventually
#print axioms RBM.Ind.QBudgetBInst.dFlowQN_levelLin_instance
#print axioms RBM.Ind.QBudgetBInst.alt_hdriftLinQN_instance
#print axioms RBM.Ind.QBudgetBInst.dDriftAltLinQN_nonneg_instance
#print axioms RBM.Ind.QBudgetBInst.dDriftAltQN_eq_lin_instance
#print axioms RBM.Ind.QBudgetBInst.altBudgetExpQN_of_choice_instance
#print axioms RBM.Ind.QBudgetBInst.altBudgetNumQN_eventually_instance
