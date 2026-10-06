/-
Check file for T2272 (S3-16b, `Induction/QLevelsB.lean`; DECISIONS §83 re-plan).
Only merged imports, `#check`s of merged names, one vocabulary definition (§2, copied verbatim into
`QLevelsB.lean`) and `Prop` pin texts (§3). No proofs.
-/
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.ScaleFacts
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Events
import RBM3D.Induction.AzumaProxyN

set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## §1. Merged names used (full namespaces from the enclosing `namespace … end` blocks) -/

-- `Induction/QLevelsA.lean` (f515695), namespace `RBM.Ind`
#check @RBM.Ind.altB45N_levelM        -- :376
#check @RBM.Ind.startLevelQN          -- :421
#check @RBM.Ind.crudeLKM_of_level     -- :462

-- `Induction/QDriftA.lean` (88ee6fd), namespace `RBM.Ind`
#check @RBM.Ind.altB4N                -- :59
#check @RBM.Ind.altB5N                -- :71
#check @RBM.Ind.dFlowQN               -- :79
#check @RBM.Ind.altClsQN              -- :93
#check @RBM.Ind.dGridQN_eq_dFlowQN    -- :131
#check @RBM.Ind.fastDecay_of_diamInf  -- :234

-- `Induction/QDriftB.lean` (c01b292), namespace `RBM.Ind`
#check @RBM.Ind.drift13_fastDecay     -- :152
#check @RBM.Ind.alt_hDclsQN           -- :379

-- `Induction/NQGood1.lean` (691566a), `Induction/NQGood2.lean` (cc96b69), namespace `RBM.Ind`
#check @RBM.Ind.driftTensorN                     -- NQGood1 :95
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet  -- NQGood1 :104
#check @RBM.Ind.driftTensorN_far_of_goodSet      -- NQGood1 :133
#check @RBM.Ind.dDriftNonAltN                    -- NQGood2 :96
#check @RBM.Ind.nonAlt_hdriftN                   -- NQGood2 :315

-- `Induction/QGridA.lean` (549a62d), `Induction/GridAssemblyN.lean` (686cf71), namespace `RBM.Ind`
#check @RBM.Ind.dGridQN                 -- QGridA :1274
#check @RBM.Ind.GridAssemblyHypN        -- GridAssemblyN :183
#check @RBM.Ind.GridAssemblyHypN.hdrift   -- GridAssemblyN :208
#check @RBM.Ind.GridAssemblyHypN.hdDrift0 -- GridAssemblyN :206

-- `Induction/GridGoodN.lean` (2f246bf), `Induction/Step2Defs.lean` (86124dc), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STmaxLKM   -- GridGoodN :68
#check @RBM.Gauss.Sizes.STXiLKM    -- GridGoodN :82
#check @RBM.Gauss.Sizes.GoodSetN   -- GridGoodN :124
#check @RBM.Gauss.Sizes.STLM       -- Step2Defs :60
#check @RBM.Gauss.Sizes.STLKM      -- Step2Defs :68

-- `Induction/Step34Pins.lean` (fc76526), `Induction/QopNorm.lean` (eb6d67a), `Induction/QopAlgebra.lean` (6b2494e),
-- namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STPsum                       -- Step34Pins :87
#check @RBM.Gauss.Sizes.STQop                        -- Step34Pins :92
#check @RBM.Gauss.Sizes.STMollifierProps             -- Step34Pins :510
#check @RBM.Gauss.Sizes.STQopNorm                    -- Step34Pins :528
#check @RBM.Gauss.Sizes.stQopNorm_holds              -- QopNorm :261
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier         -- QopAlgebra :345
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props   -- QopAlgebra :511

-- `Induction/ScaleFacts.lean` (5d1e6b1), `Induction/Step2Core.lean` (092aaf0), `Induction/Step2Events.lean` (7f9bfa1):
-- namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STBctl_pos                    -- ScaleFacts :64
#check @RBM.Gauss.Sizes.ST_gridTime_mem               -- Step2Core :387
#check @RBM.Gauss.Sizes.ST_gridTime_zero              -- Step2Events :596
#check @RBM.Gauss.Sizes.ST_gridTime_mono              -- Step2Events :1151

-- `Induction/AzumaProxyN.lean` (43ab861), namespace `RBM.Ind` (instances only)
#check @RBM.Ind.zero_mem_goodSetN_of_levels           -- AzumaProxyN :924

-- `Loop/GLoop.lean` (e0c58e6), namespace `RBM.Gauss`; `Defs/Params.lean` (c3f3d5d), namespace `RBM`;
-- `Path/Walk.lean` (ddf5f74), namespace `RBM.Path`
#check @RBM.Gauss.etaT_pos   -- GLoop :83
#check @RBM.ellT_pos         -- Params :44
#check @RBM.Path.gridTime    -- Walk :70
#check @RBM.Path.pathH       -- Walk :75

namespace RBM.Ind

/-! ## §2. Vocabulary (copied verbatim into `QLevelsB.lean`, namespace `RBM.Ind`) -/

/-- **The drift level of the alternating chain** at a matrix (tensors of `m + 2` indices, `k = m + 2`):
`W^{C_n ε'}·dDriftNonAltN(k) + W^{-D'+C_n}` (the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)`, `(normQA)` on the good-set level
of the block) plus `N^{τ_N}η_u⁻¹B_u^{m+2}X` (the level of `ℬ₄ + ℬ₅`, `altB45N_levelM`, `(y27kasdfg)`). -/
def dDriftAltQN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ) : ℝ :=
  ((sz.W n : ℕ) : ℝ) ^ (Cn * ε') * dDriftNonAltN sz n E u (m + 1 + 1) Γ Φ +
    ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn) +
    ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

namespace T2272Check

/-! ## §3. The pinned statements (theorem name = `Prop` name without `T2272_`) -/

/-- **Target 1, `goodSetN_LKM_le`** (clause (G2) of `GoodSetN` in the `hY` shape of `altB45N_levelM`):
`STXiLKM j H = 1 + STmaxLKM j H / B^j ≤ ΓΦ` gives `1 ≤ ΓΦ` and `‖(𝓛-𝒦)_{u,σ'}(H)_{a'}‖ ≤ ΓΦ B_u^j`, `1 ≤ j < k`. -/
def T2272_goodSetN_LKM_le : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → u < 1 → ∀ j : ℕ, 1 ≤ j → j < k →
      1 ≤ Γ * Φ ∧ ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
        ‖sz.STLKM n E u H σ' a'‖ ≤ Γ * Φ * sz.Bctl n u ^ j

/-- **Target 2, `goodSetN_LKM_far`** (clause (Dec) of `GoodSetN` in the `hF` shape of `altB45N_levelM`, window
`ωf = W^{τ'}`, `Fv = W^{-D'}`). -/
def T2272_goodSetN_LKM_far : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (k : ℕ) (Γ Λ Φ τ' D' : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    H ∈ sz.GoodSetN n E u k Γ Λ Φ τ' D' → ∀ j : ℕ, 1 ≤ j → j ≤ 2 * k + 2 →
      ∀ (σ' : Fin j → Bool) (a' : Fin j → Zd d (sz.L n)),
        ellT (sz.L n) (sz.lam n) u * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf a' : ℝ) →
          ‖sz.STLKM n E u H σ' a'‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D')

/-- **Target 3, `qopB13N_levelM`** (the level of `𝒬_u(ℬ₁+ℬ₂+ℬ₃)` at a good matrix): `stQopNorm_holds` (`(normQA)`)
at `m + 1`, applied to the block `driftTensorN` (decay: `drift13_fastDecay`; sup: `driftTensorN_norm_le_of_goodSet`). -/
def T2272_qopB13N_levelM : Prop :=
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
            ((sz.W n : ℕ) : ℝ) ^ (-D' + Cn)

/-- **Target 4, `dFlowQN_levelM`** (the per-matrix drift level): `dFlowQN = 𝒬_u(block) + ℬ₄ + ℬ₅`; target 3 plus
the second conjunct of `altB45N_levelM` with `hY` from target 1 (`ΓΦ ≤ νX`), `hF` from target 2 (`ωf = W^{τ'}`,
`Fv = W^{-D'}`), `Γ = 2/√κ`, mollifier constant `Λ = C` (clauses 2 and 4 of `STMollifierProps`, `exp(-…) ≤ 1`). -/
def T2272_dFlowQN_levelM : Prop :=
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
        ‖dFlowQN sz n E u ϑ σ H a‖ ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X

/-- **Target 5, `alt_hdriftQN`** (the field `hdrift` of `GridAssemblyHypN`, `GridAssemblyN.lean:208`, for the
alternating chain): `Dr j ω = dGridQN … (QopAlgebra_mollifier d L (m+1) g) σ j ω` (the `Dr` of `alt_hDclsQN` at
`m + 1`), `dDrift j ω = dDriftAltQN … (u_j) …`, on `{j < Kg n, j < τ ω}`: `dGridQN_eq_dFlowQN`, target 4 at
`u = u_j`, `H = H_j`, `C = (1 + 40·d(m+1))·6^{d(m+1)}`, `c = 1/2` (`QopAlgebra_mollifier_props`). -/
def T2272_alt_hdriftQN : Prop :=
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
          dDriftAltQN sz n (E n) (gridTime s v Kg n j) m (Γ n) (Φ n) Cn ε' D' τN X

/-- **Target 6, `dDriftAltQN_nonneg`** (the field `hdDrift0`, `GridAssemblyN.lean:206`, at `u = u_j < 1`). -/
def T2272_dDriftAltQN_nonneg : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ) (m : ℕ) (Γ Φ Cn ε' D' τN X : ℝ),
    |E| < 2 → u < 1 → 0 ≤ Γ → 0 ≤ Φ → 0 ≤ X → 0 ≤ dDriftAltQN sz n E u m Γ Φ Cn ε' D' τN X

end T2272Check

end RBM.Ind
