/-
Check file for ticket T2286 (S3-17b, `RBM3D/Induction/QBudgetB.lean`).
Only imports of merged modules, `open`/`namespace`, `def … : Prop` pin texts, vocabulary defs,
`#check` of merged names; no proof terms or tactic blocks.  Must compile on `main` (b39ac53) as is.
-/
import RBM3D.Induction.QBudgetA

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## §1 Merged names used (namespaces from the enclosing `namespace … end` blocks) -/

-- S3-17a = T2279 (b39ac53, `Induction/QBudgetA`, namespace `RBM.Ind`)
#check @RBM.Ind.altBudget_kapFar          -- :57
#check @RBM.Ind.altBudget_qvFar           -- :63
#check @RBM.Ind.qvBdAltQN                 -- :70
#check @RBM.Ind.dDriftAltLinQN            -- :94
#check @RBM.Ind.assembledRHSAltQN         -- :104
#check @RBM.Ind.dDriftAltLinQN_le_shape   -- :419
#check @RBM.Ind.dDriftAltQN_le_shape      -- :469
#check @RBM.Ind.budgetAltQN               -- :575
-- S3-16b = T2272 (54b8610, `Induction/QLevelsB`, `RBM.Ind`)
#check @RBM.Ind.dDriftAltQN               -- :53
#check @RBM.Ind.goodSetN_LKM_le           -- :86
#check @RBM.Ind.goodSetN_LKM_far          -- :108
#check @RBM.Ind.qopB13N_levelM            -- :126
#check @RBM.Ind.dFlowQN_levelM            -- :171
#check @RBM.Ind.alt_hdriftQN              -- :245
#check @RBM.Ind.dDriftAltQN_nonneg        -- :287
-- S3-16a = T2268 (f515695, `Induction/QLevelsA`, `RBM.Ind`)
#check @RBM.Ind.altB45N_levelM            -- :376
#check @RBM.Ind.startLevelQN              -- :421
-- S3-15a = T2250 (88ee6fd, `Induction/QDriftA`, `RBM.Ind`); S3-15b = T2263 (c01b292, `Induction/QDriftB`)
#check @RBM.Ind.dFlowQN                   -- QDriftA :79
#check @RBM.Ind.dGridQN_eq_dFlowQN        -- QDriftA :131
#check @RBM.Ind.alt_hA0clsQN              -- QDriftA :473 (δ0 = 2 W^{-D'})
#check @RBM.Ind.drift13_fastDecay         -- QDriftB :152
#check @RBM.Ind.alt_hDclsQN               -- QDriftB :379 (δD = 4 W^{-D'})
-- S3-13a (549a62d, `Induction/QGridA`, `RBM.Ind`)
#check @RBM.Ind.dGridQN                   -- :1274
-- S3-14 = T2194 (9a207a1, `Induction/QProxy`, `RBM.Ind`)
#check @RBM.Ind.qProxyCn                  -- :434
#check @RBM.Ind.qProxyCQ                  -- :440
#check @RBM.Ind.qProxy4C                  -- :444
#check @RBM.Ind.qProxyCn_pos              -- :458
#check @RBM.Ind.qProxy4C_pos              -- :465
-- S3-05 (eb6d67a, `Induction/QopNorm`, namespace `RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.stQopNorm_holds   -- :261
-- S3-04 (6b2494e, `Induction/QopAlgebra`, `RBM.Gauss.Sizes`); `Induction/Step34Pins` (`RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier        -- :345
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props  -- :511
#check @RBM.Gauss.Sizes.STMollifierProps            -- Step34Pins :510
-- S3-12a = T2186 (d783ee3, `Induction/NQLin`; `GoodLin`/`NQLinGood` in `RBM.Gauss.Sizes` :54-701, the rest in `RBM.Ind`)
#check @RBM.Gauss.Sizes.GoodLinN                    -- :66
#check @RBM.Gauss.Sizes.NQLinConcl                  -- :102
#check @RBM.Gauss.Sizes.goodSetN_subset_goodLinN    -- :212
#check @RBM.Gauss.Sizes.nqLinGood_holds             -- :591
#check @RBM.Ind.dDriftLinN                          -- :711
#check @RBM.Ind.nqLinExitTauN                       -- :716
#check @RBM.Ind.dDriftNonAltN_eq_lin                -- :724
#check @RBM.Ind.driftTensorN_norm_le_of_goodLin     -- :732
#check @RBM.Ind.nqLin_hdriftN                       -- :761
#check @RBM.Ind.mem_of_lt_nqLinExitTauN             -- :772
#check @RBM.Ind.budgetNonAltLinN                    -- :966
#check @RBM.Ind.NQLinInst.zero_mem_goodLinN_inst    -- :1338
-- ST2 / AzumaProxyN (`RBM.Ind`)
#check @RBM.Ind.zero_mem_goodSetN_of_levels         -- AzumaProxyN :924
-- Sizes (0a873f1, `Defs/Sizes`: `RBM.Gauss.Sizes` :148-246, `RBM.Gauss.SizesInst` :257-)
#check @RBM.Gauss.Sizes.Bandwidth                   -- :168
#check @RBM.Gauss.Sizes.SizeTendsto                 -- :173
#check @RBM.Gauss.SizesInst.sz0                     -- :260
#check @RBM.Gauss.SizesInst.sz0_bandwidth           -- :298
#check @RBM.Gauss.SizesInst.sz0_tendsto             -- :300

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

/-! ## §3 Pinned statements (theorem name = `Prop` name without `T2286_`) -/

/-- Target 1: the per-matrix LINEAR drift level of the alternating chain (`dFlowQN_levelM` with
`driftTensorN_norm_le_of_goodLin` for the block, `GoodSetN` only at a free crude level for (Herm), (Vb), (Dec),
`hY` an explicit premise, `C_n = qProxyCn d (m+1) Λg KL C c` explicit). -/
def T2286_dFlowQN_levelLin : Prop :=
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
          dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ (qProxyCn d (m + 1) Λg KL C c) ε' D' τN X

/-- Target 2: the field `hdrift` of `GridAssemblyHypN` along the walk at the linear level (`alt_hdriftQN` with
target 1; mollifier `QopAlgebra_mollifier`, `C = (1 + 40 d(m+1)) 6^{d(m+1)}`, `c = 1/2`; membership in
`GoodSetN ∩ GoodLinN` in the form of `mem_of_lt_nqLinExitTauN`; `hY` on `{j < τ}` separate). -/
def T2286_alt_hdriftLinQN : Prop :=
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
            ε' D' τN X

/-- Target 3: the field `hdDrift0` at the linear level. -/
def T2286_dDriftAltLinQN_nonneg : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Φ₁ → 0 ≤ Φ₂ → 0 ≤ Φ₃ → 0 ≤ X →
      0 ≤ dDriftAltLinQN sz n E u m Γ Φ₁ Φ₂ Φ₃ Cn ε' D' τN X

/-- Target 4: the merged quadratic level is the linear level at `Φ₁ = Φ₃ = Φ`, `Φ₂ = kΓΦ²`
(`dDriftNonAltN_eq_lin`; consistency of the two S3-16b/S3-17 levels). -/
def T2286_dDriftAltQN_eq_lin : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
    dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X =
      dDriftAltLinQN sz n E u m Γ Φ (((m + 1 + 1 : ℕ) : ℝ) * Γ * Φ ^ 2) Φ Cn ε' D' τN X

/-- Target 5: an explicit admissible choice of the exponents (`ξ = -(2k+1)`; monotone in `D'`, `D''`, `D_Y`,
`D_t`; `ε`, `ε'`, `ε₁`, `εq`, `τN` small against `ε₀`), so the conditions are not vacuous for any positive
`C₄`, `C_n`, `𝔠`, `ε₀`. -/
def T2286_altBudgetExpQN_of_choice : Prop :=
  ∀ (k : ℕ) (C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ : ℝ),
    0 < C4 → 0 < Cn → 0 < 𝔠 → 0 < ε₀ → 0 < ε → ε ≤ 1 / 2 →
    C4 * ε ≤ ε₀ / 8 → Cn * ε ≤ ε₀ / 8 → 0 ≤ ε' → Cn * ε' ≤ ε₀ / 8 →
    ε₁ ≤ ε₀ / 8 → εq ≤ ε₀ / 8 → τN ≤ ε₀ / 8 →
    C4 + Cn + (2 * (k : ℝ) + 1) / 𝔠 ≤ D' →
    2 * Cn + 2 + 2 * C4 + (k : ℝ) + (4 * (k : ℝ) + 1) / 𝔠 ≤ D'' →
    (k : ℝ) ≤ D_Y → (k : ℝ) ≤ D_t →
      altBudgetExpQN k C4 Cn 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ (-(2 * (k : ℝ) + 1))

/-- Target 6 (the theorem S3-18a consumes): the eight hypotheses of `budgetAltQN` at the linear level hold
eventually, from `SizeTendsto`, `Bandwidth 𝔠`, `κ' ≤ Im m(E n)` and `0 < g ≤ Λg` eventually, and the exponent
conditions at `C₄ = qProxy4C d (m+2) Λg κ' KL`, `C_n = qProxyCn d (m+1) Λg KL C c`. -/
def T2286_altBudgetNumQN_eventually : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (m : ℕ)
    (Λg κ' KL C c 𝔠 ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ : ℝ),
    1 ≤ d → sz.SizeTendsto → sz.Bandwidth 𝔠 → 0 < κ' →
    (∀ᶠ n : ℕ in atTop, κ' ≤ (mE (E n)).im) →
    (∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg) →
    altBudgetExpQN (m + 1 + 1) (qProxy4C d (m + 1 + 1) Λg κ' KL) (qProxyCn d (m + 1) Λg KL C c) 𝔠
      ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁ ξ →
    ∀ᶠ n : ℕ in atTop, altBudgetNumQN sz E n m Λg κ' KL C c ε ε' τN D' D'' D_Y D_t εq ε₀ ε₁

end RBM.Ind

end
