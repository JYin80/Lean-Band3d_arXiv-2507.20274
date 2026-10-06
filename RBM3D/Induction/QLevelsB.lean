/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Events
import RBM3D.Induction.AzumaProxyN

/-!
# S3-16b (ticket T2272): the deterministic drift level of the alternating chain at a good matrix

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): `int_K-L+Q` `3_5:1337-1346`
(`ℬ₀…ℬ₅`), `lem_+Q`/`(normQA)` `3_5:1284-1289`, the integrand `𝒬_v Σ_{k=1}^3 ℬ_k(v)` `3_5:1684`,
`(y27kasdfg)`, `(A5)`, `(A4)` `3_5:1692-1706`.

Re-scope (DECISIONS §83, §64 (4)/(5)): RBM2D `AltLevelsQ` (`AltLevelsQ.lean:165-257, 314-360, 481-560` at
`c9a24cf`) is ported in its deterministic, per-matrix form: no per-time stochastic good set, no `≺`, no lift, no
probability.  `GoodSetN` membership is a hypothesis (pathwise on `{j < τ}`).

* `dDriftAltQN` (vocabulary): the level `W^{C_nε'}dDriftNonAltN + W^{-D'+C_n} + N^{τ_N}η⁻¹B^{m+2}X`;
* `goodSetN_LKM_le`, `goodSetN_LKM_far` (targets 1, 2): clauses (G2), (Dec) of `GoodSetN` in the `hY`, `hF`
  shapes of `altB45N_levelM`;
* `qopB13N_levelM` (target 3): `(normQA)` on the block `driftTensorN`;
* `dFlowQN_levelM` (target 4): the per-matrix level of `dFlowQN = 𝒬_u(block) + ℬ₄ + ℬ₅`;
* `alt_hdriftQN` (target 5): the field `hdrift` of `GridAssemblyHypN` along the walk;
* `dDriftAltQN_nonneg` (target 6): the field `hdDrift0`;
* instances (namespace `QLevelsBInst`) at `sz0`, `d = 3`, `m = 2`, `n = 4`, `E = 0`, `u = 0`, `H = 0`.

Unpinned helpers are `private` or prefixed `QLevelsB_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 0. Vocabulary -/

/-- **The drift level of the alternating chain** at a matrix (tensors of `m + 2` indices, `k = m + 2`):
`W^{C_n ε'}·dDriftNonAltN(k) + W^{-D'+C_n}` (the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)`, `(normQA)` on the good-set level
of the block) plus `N^{τ_N}η_u⁻¹B_u^{m+2}X` (the level of `ℬ₄ + ℬ₅`, `altB45N_levelM`, `(y27kasdfg)`). -/
def dDriftAltQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-! ## 1. Targets 1 and 2: the good-set clauses (G2), (Dec) as entry bounds -/

/-- Clause (G2) of `GoodSetN` read as an entry bound: `‖(𝓛-𝒦)^{(j)}_{σ,a}(H)‖ ≤ (Z - 1) B^j` (copy of the private
`QLevelsAInst.norm_STLKM_le_of_XiLKM`, `QLevelsA.lean`). -/
private theorem QLevelsB_norm_STLKM_le_of_XiLKM {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (j : ℕ) {Z : ℝ}
    (hB : 0 < sz.Bctl n u) (h : sz.STXiLKM n E u j H ≤ Z) (σ : Fin j → Bool)
    (a : Fin j → Zd d (sz.L n)) : ‖sz.STLKM n E u H σ a‖ ≤ (Z - 1) * sz.Bctl n u ^ j := by
  have hBj : 0 < sz.Bctl n u ^ j := pow_pos hB j
  unfold STXiLKM at h
  have h1 : ‖sz.STLKM n E u H σ a‖ ≤ STmaxLKM sz n E u j H :=
    Finset.le_sup' (fun p : (Fin j → Bool) × (Fin j → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖)
      (Finset.mem_univ (σ, a))
  have h2 : STmaxLKM sz n E u j H / sz.Bctl n u ^ j ≤ Z - 1 := by linarith
  rw [div_le_iff₀ hBj] at h2
  exact h1.trans h2

/-- `STmaxLKM ≥ 0`: a `sup'` of norms. -/
private theorem QLevelsB_STmaxLKM_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (j : ℕ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : 0 ≤ STmaxLKM sz n E u j H :=
  (norm_nonneg _).trans (Finset.le_sup' (fun p : (Fin j → Bool) × (Fin j → Zd d (sz.L n)) =>
      ‖loopFine d (sz.L n) (sz.W n) H (zt E u) p.1 p.2 - STKloop sz n E u p.1 p.2‖)
      (Finset.mem_univ (((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))) :
        (Fin j → Bool) × (Fin j → Zd d (sz.L n)))))

/-- **Target 1, `goodSetN_LKM_le`** (clause (G2) of `GoodSetN` in the `hY` shape of `altB45N_levelM`):
`STXiLKM j H = 1 + STmaxLKM j H / B^j ≤ ΓΦ` gives `1 ≤ ΓΦ` and `‖(𝓛-𝒦)_{u,σ'}(H)_{a'}‖ ≤ ΓΦ B_u^j`, `1 ≤ j < k`. -/
theorem goodSetN_LKM_le :
    ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → u < 1 → ∀ j : ℕ, 1 ≤ j → j < k →
        1 ≤ Γ * Φ ∧ ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
          ‖sz.STLKM n E u H σ' a'‖ ≤ Γ * Φ * sz.Bctl n u ^ j := by
  intro d sz n E u k Γ Λ Φ τ' D' H hH hu j hj1 hjk
  have hXi : sz.STXiLKM n E u j H ≤ Γ * Φ := hH.2.1 j hj1 hjk
  have hB : 0 < sz.Bctl n u := STBctl_pos sz n hu
  have hBj : 0 < sz.Bctl n u ^ j := pow_pos hB j
  have hmax := QLevelsB_STmaxLKM_nonneg sz n E u j H
  have h1 : 1 ≤ Γ * Φ := by
    have : 0 ≤ STmaxLKM sz n E u j H / sz.Bctl n u ^ j := div_nonneg hmax hBj.le
    unfold STXiLKM at hXi
    linarith
  refine ⟨h1, fun σ' a' => ?_⟩
  have h := QLevelsB_norm_STLKM_le_of_XiLKM sz n E u H j hB hXi σ' a'
  refine h.trans ?_
  nlinarith

/-- **Target 2, `goodSetN_LKM_far`** (clause (Dec) of `GoodSetN` in the `hF` shape of `altB45N_levelM`, window
`ωf = W^{τ'}`, `Fv = W^{-D'}`). -/
theorem goodSetN_LKM_far :
    ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 →
        ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
          ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
            ‖sz.STLKM n E u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := by
  intro d sz n E u k Γ Λ Φ τ' D' H hH j hj1 hj σ' a' hfar
  have h := hH.2.2.1 j hj1 hj σ' a' hfar
  have e : sz.STLKM n E u H σ' a' =
      loopFine d (sz.L n) (sz.W n) H (zt E u) σ' a' - STKloop sz n E u σ' a' := rfl
  rw [e]
  exact le_trans (le_add_of_nonneg_left (norm_nonneg _)) h

/-! ## 2. Target 3: the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)` -/

/-- **Target 3, `qopB13N_levelM`** (the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)` at a good matrix): `stQopNorm_holds` (`(normQA)`)
at `m + 1`, applied to the block `driftTensorN` (decay: `drift13_fastDecay`; sup: `driftTensorN_norm_le_of_goodSet`). -/
theorem qopB13N_levelM :
    ∀ (d m : ℕ) (Λg K C c : ℝ), 3 ≤ d → 0 < Λg → 0 < K → 0 < C → 0 < c →
      ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (E u Γ Λ Φ τ' ε' D' : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ),
        0 < sz.lam n → sz.lam n ≤ Λg → 1 < ((sz.W n : ℕ) : ℝ) → 0 < ε' → ε' < 1 → 1 < D' →
        4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        STMollifierProps (d := d) (sz.lam n) C c ϑ → 0 ≤ u → u < 1 →
        H ∈ sz.GoodSetN n E u (m + 1 + 1) Γ Λ Φ τ' D' →
        ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b) a‖ ≤
            ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ +
              ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := by
  intro d m Λg K C c hd hΛg hK hC hc
  obtain ⟨Cn, hCn, H⟩ := stQopNorm_holds d hd (m + 1) Λg K C c hΛg hK hC hc
  refine ⟨Cn, hCn, ?_⟩
  intro sz n E u Γ Λ Φ τ' ε' D' Hm σ ϑ hlam hlamΛ hW hε hε1 hD h4 hLW hdW hϑ hu0 hu1 hG a
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hfast : EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
      (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b) :=
    drift13_fastDecay sz hd σ hdW hG
  have hq := H (sz.L n) (sz.three_le_L n) (sz.lam n) hlam hlamΛ ((sz.W n : ℕ) : ℝ) ε' D' hW hε hε1 hD h4 hLW
    ϑ hϑ u hu0 hu1 _ hfast
  have hpt : ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖driftTensorN sz n E u Hm σ b‖ ≤
      dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ := fun b =>
    driftTensorN_norm_le_of_goodSet sz (by omega) hG σ b
  have hnn : 0 ≤ dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ :=
    (norm_nonneg _).trans (hpt (fun _ => 0))
  have hsup : ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b‖ ≤
      dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ := (pi_norm_le_iff_of_nonneg hnn).2 hpt
  have hrp : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') := Real.rpow_nonneg hWpos.le _
  calc _ ≤ ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b)‖ :=
        norm_le_pi_norm _ a
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * ‖fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
        driftTensorN sz n E u Hm σ b‖ + ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) := hq
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hsup hrp
        linarith

/-! ## 3. Target 4: the per-matrix level of the drift `dFlowQN` -/

/-- **Target 4, `dFlowQN_levelM`** (the per-matrix drift level): `dFlowQN = 𝒬_u(block) + ℬ₄ + ℬ₅`; target 3 plus
the second conjunct of `altB45N_levelM` with `hY` from target 1 (`ΓΦ ≤ νX`), `hF` from target 2 (`ωf = W^{τ'}`,
`Fv = W^{-D'}`), `Γ = 2/√κ`, mollifier constant `Λ = C` (clauses 2 and 4 of `STMollifierProps`, `exp(-…) ≤ 1`). -/
theorem dFlowQN_levelM :
    ∀ (d m : ℕ) (Λg K C c : ℝ), 3 ≤ d → 0 < Λg → 0 < K → 0 < C → 0 < c →
      ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (E u κ Γ Λ Φ τ' ε' D' ν X τN : ℝ)
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
        (σ : Fin (m + 1 + 1) → Bool) (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ),
        0 < κ → |E| ≤ 2 - κ → 0 ≤ u → u < 1 → 0 < sz.lam n → sz.lam n ≤ Λg →
        (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u →
        1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' →
        4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        1 ≤ ν → 1 ≤ X → Γ * Φ ≤ ν * X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν →
        ν ≤ ((sz.size n : ℕ) : ℝ) →
        ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ →
        (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) * C * ν ^ 2) ≤
          ((sz.size n : ℕ) : ℝ) ^ τN →
        STMollifierProps (d := d) (sz.lam n) C c ϑ →
        H ∈ sz.GoodSetN n E u (m + 1 + 1) Γ Λ Φ τ' D' →
        σ (Fin.last (m + 1)) = !σ 0 →
        ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖dFlowQN sz n E u ϑ σ H a‖ ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X := by
  intro d m Λg K C c hd hΛg hK hC hc
  obtain ⟨Cn, hCn, H3⟩ := qopB13N_levelM d m Λg K C c hd hΛg hK hC hc
  refine ⟨Cn, hCn, ?_⟩
  intro sz n E u κ Γ Λ Φ τ' ε' D' ν X τN Hm σ ϑ hκ hE hu0 hu1 hlam hlamΛ hNu hW hτ' hε hε1 hD h4 hLW hdW hν
    hX hΓΦ hωd hνN hFv hMΛ hϑ hG hσ a
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hB0 : 0 < sz.Bctl n u := STBctl_pos sz n hu1
  have hq := H3 sz n E u Γ Λ Φ τ' ε' D' Hm σ ϑ hlam hlamΛ hW hε hε1 hD h4 hLW hdW hϑ hu0 hu1 hG a
  have hHerm : Hm.IsHermitian := hG.1
  have hωf : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hW.le hτ'
  have hY : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ‖sz.STLKM n E u Hm σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1) := by
    intro σ' a'
    have h := (goodSetN_LKM_le d sz n E u (m + 1 + 1) Γ Λ Φ τ' D' Hm hG hu1 (m + 1) (by omega)
      (by omega)).2 σ' a'
    exact h.trans (mul_le_mul_of_nonneg_right hΓΦ (pow_pos hB0 _).le)
  have hF : ∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
      ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
        ‖sz.STLKM n E u Hm σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := fun σ' a' hfar =>
    goodSetN_LKM_far d sz n E u (m + 1 + 1) Γ Λ Φ τ' D' Hm hG (m + 1) (by omega) (by omega) σ' a' hfar
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
    (((sz.W n : ℕ) : ℝ) ^ τ') (((sz.W n : ℕ) : ℝ) ^ (-D')) C τN rfl hν hX hωf hωd hνN hFv
    (Real.rpow_nonneg hWpos.le _) hC.le hMΛ hY hF ϑ hexp (fun a => hϑ.2.2.2 u hu0 hu1 a) σ hσ a
  have hflow : dFlowQN sz n E u ϑ σ Hm a =
      STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => driftTensorN sz n E u Hm σ b) a +
        altB4N sz n E u ϑ σ Hm a + altB5N sz n E u ϑ σ Hm a := rfl
  rw [hflow]
  unfold dDriftAltQN
  have h3 := norm_add₃_le (a := STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
    driftTensorN sz n E u Hm σ b) a) (b := altB4N sz n E u ϑ σ Hm a) (c := altB5N sz n E u ϑ σ Hm a)
  linarith [hB45.2]

/-! ## 4. Target 5: the field `hdrift` of `GridAssemblyHypN` along the walk -/

/-- **Target 5, `alt_hdriftQN`** (the field `hdrift` of `GridAssemblyHypN`, `GridAssemblyN.lean:208`, for the
alternating chain): `Dr j ω = dGridQN … (QopAlgebra_mollifier d L (m+1) g) σ j ω` (the `Dr` of `alt_hDclsQN` at
`m + 1`), `dDrift j ω = dDriftAltQN … (u_j) …`, on `{j < Kg n, j < τ ω}`: `dGridQN_eq_dFlowQN`, target 4 at
`u = u_j`, `H = H_j`, `C = (1 + 40·d(m+1))·6^{d(m+1)}`, `c = 1/2` (`QopAlgebra_mollifier_props`). -/
theorem alt_hdriftQN :
    ∀ (d m : ℕ) (Λg K : ℝ), 3 ≤ d → 0 < Λg → 0 < K →
      ∃ Cn : ℝ, 0 < Cn ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1 + 1) → Bool) (E s v : ℕ → ℝ)
        (Kg : ℕ → ℕ) (Γ Λ Φ : ℕ → ℝ) (κ τ' ε' D' ν X τN : ℝ) (τ : PathΩ sz → ℕ),
        0 < κ → |E n| ≤ 2 - κ → 0 < sz.lam n → sz.lam n ≤ Λg →
        0 ≤ s n → s n ≤ v n → v n < 1 → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - v n →
        1 < ((sz.W n : ℕ) : ℝ) → 0 ≤ τ' → 0 < ε' → ε' < 1 → 1 < D' →
        4 ≤ ((sz.W n : ℕ) : ℝ) ^ ε' → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
        (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
        1 ≤ ν → 1 ≤ X → Γ n * Φ n ≤ ν * X → (((sz.W n : ℕ) : ℝ) ^ τ') ^ (d * m) ≤ ν →
        ν ≤ ((sz.size n : ℕ) : ℝ) →
        ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ →
        (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * (2 / Real.sqrt κ) *
            ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1))) * ν ^ 2) ≤
          ((sz.size n : ℕ) : ℝ) ^ τN →
        σ (Fin.last (m + 1)) = !σ 0 →
        (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈
          sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1 + 1) (Γ n) (Λ n) (Φ n) τ' D') →
        ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω → ∀ b : Fin (m + 1 + 1) → Zd d (sz.L n),
          ‖dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω b‖ ≤
            dDriftAltQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ n) Cn ε' D' τN X := by
  intro d m Λg K hd hΛg hK
  have hC0 : (0 : ℝ) < (1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)) := by positivity
  obtain ⟨Cn, hCn, H4⟩ := dFlowQN_levelM d m Λg K ((1 + 40 * ((d * (m + 1) : ℕ) : ℝ)) * 6 ^ (d * (m + 1)))
    (1 / 2) hd hΛg hK hC0 (by norm_num)
  refine ⟨Cn, hCn, ?_⟩
  intro sz n σ E s v Kg Γ Λ Φ κ τ' ε' D' ν X τN τ hκ hE hlam hlamΛ hs0 hsv hv1 hNv hW hτ' hε hε1 hD h4 hLW hdW
    hν hX hΓΦ hωd hνN hFv hMΛ hσ hτG ω j hj hjτ b
  rw [dGridQN_eq_dFlowQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) σ j ω]
  have hKne : Kg n ≠ 0 := by omega
  have hmem := ST_gridTime_mem s v Kg n j hsv hKne hj.le
  have hu0 : 0 ≤ gridTime s v Kg n j := hs0.trans hmem.1
  have hu1 : gridTime s v Kg n j < 1 := lt_of_le_of_lt hmem.2 hv1
  have hNu : (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - gridTime s v Kg n j := by linarith [hmem.2]
  have hϑ := QopAlgebra_mollifier_props d (sz.L n) (m + 1) (sz.three_le_L n) hlam
  exact H4 sz n (E n) (gridTime s v Kg n j) κ (Γ n) (Λ n) (Φ n) τ' ε' D' ν X τN (pathH sz s v Kg n j ω) σ
    (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) hκ hE hu0 hu1 hlam hlamΛ hNu hW hτ' hε hε1 hD h4 hLW
    hdW hν hX hΓΦ hωd hνN hFv hMΛ hϑ (hτG ω j hjτ) hσ b

/-! ## 5. Target 6: the field `hdDrift0` -/

/-- **Target 6, `dDriftAltQN_nonneg`** (the field `hdDrift0`, `GridAssemblyN.lean:206`, at `u = u_j < 1`). -/
theorem dDriftAltQN_nonneg :
    ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
      |E| < 2 → u < 1 → 0 ≤ Γ → 0 ≤ Φ → 0 ≤ X → 0 ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X := by
  intro d sz n E u m Γ Φ Cn ε' D' τN X hE hu hΓ hΦ hX
  have hη : 0 < etaT E u := etaT_pos hE hu
  have hB : 0 < sz.Bctl n u := STBctl_pos sz n hu
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  unfold dDriftAltQN dDriftNonAltN
  have hk : (0 : ℝ) ≤ (((m + 1 + 1 : ℕ) : ℝ) - 1) := by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h1 : 0 ≤ Γ * (Γ * Φ) * (sz.Bctl n u ^ (m + 1 + 1) / etaT E u) *
      (((m + 1 + 1 : ℕ) : ℝ) - 1 + ((m + 1 + 1 : ℕ) : ℝ) * (Γ * Φ)) := by positivity
  have h2 := Real.rpow_nonneg hWpos.le (Cn * ε')
  have h3 := Real.rpow_nonneg hWpos.le (-D' + Cn)
  have h4 := Real.rpow_nonneg hN τN
  have h5 : 0 ≤ (etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X := by positivity
  have := mul_nonneg h2 h1
  have := mul_nonneg h4 h5
  linarith

/-! ## 6. Compiled nonempty instances (namespace `QLevelsBInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at
`n = 4` (`x = 2(n+1) = 10`, `L = 20`, `W = 10^5`, `N = (W L)^3 = 8·10^18`, `lam = 10^{-6}`), `d = 3`, `m = 2`
(tensors of `m + 2 = 4` indices, `k = 4 = 3 + 1`), `K = 2`, `Λ_g = 1`, `E = 0`, `u = 0`, `κ = 1`, `H = 0`,
`τ' = 1/10`, `ε' = 1/5`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, the explicit mollifier
`QopAlgebra_mollifier 3 L 3 lam` (`C = (1 + 40·9)·6^9`, `c = 1/2`), `0 ∈ GoodSetN` at the levels
`(Γ, Λ, Φ) = (4, 100, 1)`.  The numeric helpers are copies of the private ones of `QDriftBInst`
(ticket T2263, `QDriftB.lean:449-640`).  No crude sup is needed (no hypothesis of the targets asks for it),
so `n = 4` is concrete (no existential `n`).  At `H = 0` the entries may vanish: the instances test the
hypotheses and the application, not tightness.  Every deterministic hypothesis is discharged. -/

namespace QLevelsBInst

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

private theorem W_rpow_fifth (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := by
  have hx0 : 0 ≤ 2 * ((n : ℝ) + 1) := by linarith
  rw [(sz0_facts n).1, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]

/-- `ℓ_0 = 1` for `g ≤ 1`. -/
private theorem ellT_zero_eq (L : ℕ) (hL : 1 ≤ L) {g : ℝ} (hg : g ≤ 1) : ellT L g 0 = 1 := by
  unfold ellT
  rw [sub_zero, abs_one, Real.sqrt_one, div_one, max_eq_right hg]
  exact min_eq_left (by exact_mod_cast hL)

private theorem ellT_sz0 (n : ℕ) : ellT (sz0.L n) (sz0.lam n) 0 = 1 :=
  ellT_zero_eq _ (by have := sz0.three_le_L n; omega) (lam_le_one n)

/-- The coordinate `x = L/2 = 2(n+1)` is at distance `2(n+1)` from `0` on `Z_{4(n+1)}`. -/
private theorem zdist_far (n : ℕ) :
    zdist (sz0.L n) (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))) = 2 * (n + 1) := by
  have hL : sz0.L n = 4 * (n + 1) := rfl
  have hv : (((2 * (n + 1) : ℕ) : ZMod (sz0.L n))).val = 2 * (n + 1) := by
    rw [ZMod.val_natCast, hL]
    exact Nat.mod_eq_of_lt (by omega)
  unfold zdist
  rw [hv, hL]
  omega

private def farv (n : ℕ) : Zd 3 (sz0.L n) := fun _ => (((2 * (n + 1) : ℕ) : ZMod (sz0.L n)))

private theorem zdistInf_farv (n : ℕ) : zdistInf 3 (sz0.L n) (farv n) = 2 * (n + 1) := by
  unfold zdistInf farv
  simp only [zdist_far]
  rw [Finset.sup_const (Finset.univ_nonempty)]

private def farb (n : ℕ) : Fin (3 + 1) → Zd 3 (sz0.L n) := ![0, farv n, 0, 0]

/-- The `L^∞` window is attained: `diam_∞ (farb n) ≥ x ≥ ℓ_0 w`. -/
private theorem window_linf (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * w ≤ (STdiamInf b : ℝ) := by
  refine ⟨farb n, ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (3 + 1) × Fin (3 + 1) =>
      zdistInf 3 (sz0.L n) (farb n q.1 - farb n q.2)) (Finset.mem_univ ((1 : Fin (3 + 1)), (0 : Fin (3 + 1))))
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistInf_farv] at h
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf (farb n) : ℝ) := by exact_mod_cast h
  rw [ellT_sz0]
  push_cast at h2
  linarith

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

private theorem L4 : ((sz0.L 4 : ℕ) : ℝ) = 20 := by
  rw [(sz0_facts 4).2.1]; norm_num

private theorem N4 : ((sz0.size 4 : ℕ) : ℝ) = 8000000000000000000 := by
  have : sz0.size 4 = 8000000000000000000 := by norm_num [Sizes.size, sz0]
  exact_mod_cast this

private theorem W5_4 : ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 10 := by
  rw [W_rpow_fifth 4 hx4]; norm_num

private theorem W10_4 : ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt 10 := by
  rw [(sz0_facts 4).1, rpow_pow5 (by positivity), show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt10_pow6 : (Real.sqrt 10) ^ (3 * 2) = 1000 := by
  rw [show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
  norm_num

private theorem sqrt10_le : Real.sqrt 10 ≤ 10 := by
  rw [Real.sqrt_le_left (by norm_num)]; norm_num

private theorem lam4 : sz0.lam 4 = ((10 : ℝ) ^ 6)⁻¹ := by
  rw [(sz0_facts 4).2.2]; norm_num

/-- The far window of the `L^∞` clause: `ℓ_0 W^{1/10} ≤ diam_∞` is attained by a tuple of `4` labels. -/
private theorem window4 : ∃ b : Fin (3 + 1) → Zd 3 (sz0.L 4),
    ellT (sz0.L 4) (sz0.lam 4) 0 * ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ) := by
  refine window_linf 4 ?_
  rw [W10_4]
  exact sqrt10_le.trans (by norm_num)

/-- The alternating sign pattern of the instances. -/
private abbrev σalt : Fin (2 + 1 + 1) → Bool := ![true, false, true, false]

private theorem σalt_last : σalt (Fin.last (2 + 1)) = !σalt 0 := by decide

/-- **Instance of target 1** (`goodSetN_LKM_le`): `0 ∈ GoodSetN` at `(Γ, Λ, Φ) = (4, 100, 1)`, `k = 4`, `j = 1, 2, 3`. -/
theorem goodSetN_LKM_le_instance (j : ℕ) (hj1 : 1 ≤ j) (hj : j < 3 + 1) :
    1 ≤ (4 : ℝ) * 1 ∧ ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd 3 (sz0.L 4)),
      ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ 4 * 1 * sz0.Bctl 4 0 ^ j :=
  goodSetN_LKM_le 3 sz0 4 0 0 (3 + 1) 4 100 1 (1 / 10) 40 H0 (zero_mem_inst 4 (lam_le_one 4) _ _)
    (by norm_num) j hj1 hj

/-- **Instance of target 2** (`goodSetN_LKM_far`): the same data, `j = 4 ≤ 2k + 2`; the far window
`ℓ_0 W^{1/10} ≤ diam_∞` is attained by a tuple (not vacuous), and the level `W^{-40}` holds at every far label. -/
theorem goodSetN_LKM_far_instance :
    (∃ b : Fin (3 + 1) → Zd 3 (sz0.L 4),
      ellT (sz0.L 4) (sz0.lam 4) 0 * ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf b : ℝ)) ∧
    ∀ (σ' : Fin (3 + 1) → Bool) (a' : Fin (3 + 1) → Zd 3 (sz0.L 4)),
      ellT (sz0.L 4) (sz0.lam 4) 0 * ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf a' : ℝ) →
        ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ)) :=
  ⟨window4, fun σ' a' h =>
    goodSetN_LKM_far 3 sz0 4 0 0 (3 + 1) 4 100 1 (1 / 10) 40 H0 (zero_mem_inst 4 (lam_le_one 4) _ _)
      (3 + 1) (by norm_num) (by norm_num) σ' a' h⟩

/-- **Instance of target 3** (`qopB13N_levelM`): `d = 3`, `m = 2`, `Λ_g = 1`, `K = 2`, the explicit mollifier
(`C = (1 + 40·9)·6^9`, `c = 1/2`), `n = 4`, `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN` at `(4, 100, 1)`,
`τ' = 1/10`, `ε' = 1/5`, `D' = 40`, every `σ` and label `a`. -/
theorem qopB13N_levelM_instance (σ : Fin (2 + 1 + 1) → Bool) (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ∃ Cn : ℝ, 0 < Cn ∧
      ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) 0
          (fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => driftTensorN sz0 4 0 0 H0 σ b) a‖ ≤
        ((sz0.W 4 : ℕ) : ℝ) ^ (Cn * (1 / 5)) * dDriftNonAltN sz0 4 0 0 (2 + 1 + 1) 4 1 +
          ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ) + Cn) := by
  obtain ⟨Cn, hCn, H⟩ := qopB13N_levelM 3 2 1 2 Cmol3 (1 / 2) (le_refl 3) one_pos (by norm_num)
    (by positivity) (by norm_num)
  obtain ⟨hW, hWε, hLK, hdW⟩ := numeric 4 hx4
  exact ⟨Cn, hCn, H sz0 4 0 0 4 100 1 (1 / 10) (1 / 5) 40 H0 σ _ (lam_pos_n 4) (lam_le_one 4) hW (by norm_num)
    (by norm_num) (by norm_num) hWε hLK hdW
    (QopAlgebra_mollifier_props 3 (sz0.L 4) 3 (sz0.three_le_L 4) (lam_pos_n 4)) le_rfl (by norm_num)
    (zero_mem_inst 4 (lam_le_one 4) _ _) a⟩

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

/-- **Instance of target 4** (`dFlowQN_levelM`): the data of target 3 with `κ = 1`, `ν = W`, `X = 1`, `τ_N = 2`
and the alternating `σ = ![T, F, T, F]`; every deterministic hypothesis is discharged. -/
theorem dFlowQN_levelM_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ∃ Cn : ℝ, 0 < Cn ∧
      ‖dFlowQN sz0 4 0 0 (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) σalt H0 a‖ ≤
        dDriftAltQN sz0 4 0 0 2 4 1 Cn (1 / 5) 40 2 1 := by
  obtain ⟨Cn, hCn, H⟩ := dFlowQN_levelM 3 2 1 2 Cmol3 (1 / 2) (le_refl 3) one_pos (by norm_num)
    (by positivity) (by norm_num)
  obtain ⟨hW, hWε, hLK, hdW⟩ := numeric 4 hx4
  refine ⟨Cn, hCn, H sz0 4 0 0 1 4 100 1 (1 / 10) (1 / 5) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 H0 σalt _
    one_pos (by norm_num) le_rfl (by norm_num) (lam_pos_n 4) (lam_le_one 4) hNu4 hW (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hWε hLK hdW (by linarith) le_rfl
    (by rw [W4]; norm_num) (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4
    hMΛ4 (QopAlgebra_mollifier_props 3 (sz0.L 4) 3 (sz0.three_le_L 4) (lam_pos_n 4))
    (zero_mem_inst 4 (lam_le_one 4) _ _) σalt_last a⟩

/-- **Instance of target 5** (`alt_hdriftQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4` (so `H_0 = 0`,
`u_0 = 0`), the stopping time `τ ≡ 1` (`H_0 ∈ GoodSetN` for `j < τ`), levels `(4, 100, 1)`, `Λ_g = 1`, `K = 2`,
`n = 4`, the alternating `σ`, every path `ω`, `j = 0` and every label `b`. -/
theorem alt_hdriftQN_instance :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)),
      ‖dGridQN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) 3 (sz0.lam 4)) σalt 0 ω b‖ ≤
        dDriftAltQN sz0 4 0
          (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 4 0) 2 4 1 Cn (1 / 5) 40 2 1 := by
  obtain ⟨Cn, hCn, H⟩ := alt_hdriftQN 3 2 1 2 (le_refl 3) one_pos (by norm_num)
  obtain ⟨hW, hWε, hLK, hdW⟩ := numeric 4 hx4
  refine ⟨Cn, hCn, fun ω b => ?_⟩
  refine H sz0 4 σalt (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4)
    (fun _ => 4) (fun _ => 100) (fun _ => 1) 1 (1 / 10) (1 / 5) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 (fun _ => 1)
    one_pos (by norm_num) (lam_pos_n 4) (lam_le_one 4) le_rfl (by norm_num) (by norm_num)
    (by rw [N4]; norm_num) hW (by norm_num) (by norm_num) (by norm_num) (by norm_num) hWε hLK hdW
    (by linarith) le_rfl (by show (4 : ℝ) * 1 ≤ _ * 1; rw [W4]; norm_num)
    (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4 ?_ σalt_last ?_ ω 0
    (by norm_num) (by norm_num) b
  · rw [W4, N4, Real.rpow_two, Real.sqrt_one]
    norm_num
  · intro ω' j hj
    have hj0 : j = 0 := by
      have : j < 1 := hj
      omega
    subst hj0
    rw [azumaProxy_pathH_zero_of_s_zero sz0 _ _ _ 4 rfl ω', ST_gridTime_zero]
    exact zero_mem_inst 4 (lam_le_one 4) _ _

/-- **Instance of target 6** (`dDriftAltQN_nonneg`): `n = 4`, `E = 0`, `u = 0`, `m = 2`, the levels `(Γ, Φ, X) = (4, 1, 1)`
and `C_n = 1`, `ε' = 1/5`, `D' = 40`, `τ_N = 2`. -/
theorem dDriftAltQN_nonneg_instance :
    0 ≤ dDriftAltQN sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1 :=
  dDriftAltQN_nonneg 3 sz0 4 0 0 2 4 1 1 (1 / 5) 40 2 1 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

end QLevelsBInst

end RBM.Ind

end
