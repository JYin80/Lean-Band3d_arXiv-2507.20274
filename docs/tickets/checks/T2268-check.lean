/-
Check file for T2268 (S3-16a, `Induction/QLevelsA.lean`; DECISIONS §83 re-scope).
Only merged imports, `#check`s of merged names, and `Prop` pin texts (no proofs).
-/
import RBM3D.Induction.QDriftB
import RBM3D.Induction.B45

set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## §1. Merged names used (full namespaces from the enclosing `namespace … end` blocks) -/

-- `Induction/B45.lean` (1ef8fa7), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.B45_ward_fin        -- :200
#check @RBM.Gauss.Sizes.B45_Psum_le         -- :304
#check @RBM.Gauss.Sizes.B45_Psum_LK_le      -- :414
#check @RBM.Gauss.Sizes.B45_master_real     -- :530
#check @RBM.Gauss.Sizes.B45_norm_ThetaN_le  -- :671
#check @RBM.Gauss.Sizes.B45_Psum_ThetaN_le  -- :794
#check @RBM.Gauss.Sizes.B45_B4_le           -- :862
#check @RBM.Gauss.Sizes.B45_det             -- :2346
#check @RBM.Gauss.Sizes.B45_det2            -- :2577
#check @RBM.Gauss.Sizes.B45_vth_sup         -- :2115

-- `Induction/QDriftA.lean` (88ee6fd), `Induction/QDriftB.lean` (c01b292), namespace `RBM.Ind`
#check @RBM.Ind.altB4N              -- QDriftA :59
#check @RBM.Ind.altB5N              -- QDriftA :71
#check @RBM.Ind.dFlowQN             -- QDriftA :79
#check @RBM.Ind.goodSetN_A0clsQN    -- QDriftA :438
#check @RBM.Ind.alt_hA0clsQN        -- QDriftA :473
#check @RBM.Ind.alt_hDclsQN         -- QDriftB :379

-- `Induction/NQGood1.lean` (691566a), namespace `RBM.Ind`
#check @RBM.Ind.driftTensorN                     -- :95
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet  -- :104

-- `Induction/GridGoodN.lean` (2f246bf), `Induction/Step2Defs.lean` (86124dc), `Defs/Sizes.lean`:
-- namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.GoodSetN   -- GridGoodN :124
#check @RBM.Gauss.Sizes.STLM       -- Step2Defs :60
#check @RBM.Gauss.Sizes.STLKM      -- Step2Defs :68
#check @RBM.Gauss.Sizes.Bctl       -- Defs/Sizes :214

-- `Induction/Step34Pins.lean` (fc76526), namespace `RBM.Gauss.Sizes`; `Induction/GridAssemblyN.lean` (14137ce),
-- namespace `RBM.Ind`
#check @RBM.Gauss.Sizes.STPsum      -- Step34Pins :87
#check @RBM.Gauss.Sizes.STQop       -- Step34Pins :92
#check @RBM.Ind.GridAssemblyHypN    -- GridAssemblyN :183

namespace RBM.Ind

namespace T2268Check

/-! ## §3. The pinned statements (targets 2–4; theorem name = `Prop` name without `T2268_`) -/

/-- **Target 2, `altB45N_levelM`**: the merged `B45_det2` (`B45.lean:2577`) at a Hermitian matrix `H`, with
the conclusion restated on `altB4N`/`altB5N` (`QDriftA.lean:59,71`). The hypotheses are those of `B45_det2`
verbatim, with `sz.STLKM n E u H` for `STLKtensor sz n E u ω` and `H.IsHermitian` for `ω : sz.SeqΩ`. -/
def T2268_altB45N_levelM : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E u κ : ℝ), 0 < κ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 < sz.lam n → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u →
    ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H.IsHermitian →
    ∀ (m : ℕ) (Γ ν X ωf Fv Λ τN : ℝ), Γ = 2 / Real.sqrt κ → 1 ≤ ν → 1 ≤ X →
      1 ≤ ωf → ωf ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) →
      Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → 0 ≤ Fv → 0 ≤ Λ →
      (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN →
      (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1)) →
      (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv) →
      ∀ (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ),
      (∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) →
      (∀ a : Fin (m + 1 + 1) → Zd d (sz.L n), ‖deriv (fun t : ℝ => ϑ t a) u‖ ≤
        Λ * (1 - u)⁻¹ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) →
      ∀ (σ : Fin (m + 1 + 1) → Bool), σ (Fin.last (m + 1)) = !σ 0 →
      ∀ (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖STPsum (d := d) (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) (a 0) *
            ϑ u a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X) ∧
        ‖altB4N sz n E u ϑ σ H a‖ + ‖altB5N sz n E u ϑ σ H a‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τN * ((etaT E u)⁻¹ * sz.Bctl n u ^ (m + 2) * X)

/-- **Target 3, `startLevelQN`** (deterministic port of RBM2D `AltLevelsQ0`, `AltLevelsQ0.lean:55`, at a
matrix): with the hypotheses of target 2 and a rank-`(m+2)` level `Y` of `(𝓛-𝒦)_{u,σ}(H)`,
`‖𝒬_u(𝓛-𝒦)_{u,σ}(H)‖ ≤ Y + N^τ B_u^{m+2} X`. -/
def T2268_startLevelQN : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (sz : Sizes d) (n : ℕ) (E u κ : ℝ), 0 < κ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 < sz.lam n → (((sz.size n : ℕ) : ℝ))⁻¹ ≤ 1 - u →
    ∀ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), H.IsHermitian →
    ∀ (m : ℕ) (Γ ν X ωf Fv Λ τN Y : ℝ), Γ = 2 / Real.sqrt κ → 1 ≤ ν → 1 ≤ X →
      1 ≤ ωf → ωf ^ (d * m) ≤ ν → ν ≤ ((sz.size n : ℕ) : ℝ) →
      Fv ≤ ν * (((sz.size n : ℕ) : ℝ) ^ (2 * m + 4))⁻¹ → 0 ≤ Fv → 0 ≤ Λ →
      (2 * (m : ℝ) + 5) * (3 * 4 ^ (d * m) * Γ * Λ * ν ^ 2) ≤ ((sz.size n : ℕ) : ℝ) ^ τN →
      (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ‖sz.STLKM n E u H σ' a'‖ ≤ ν * X * sz.Bctl n u ^ (m + 1)) →
      (∀ (σ' : Fin (m + 1) → Bool) (a' : Fin (m + 1) → Zd d (sz.L n)),
        ellT (sz.L n) (sz.lam n) u * ωf ≤ (STdiamInf a' : ℝ) → ‖sz.STLKM n E u H σ' a'‖ ≤ Fv) →
      ∀ (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ),
      (∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
        ‖ϑ u a‖ ≤ Λ * (((ellT (sz.L n) (sz.lam n) u ^ d)⁻¹) ^ (m + 1))) →
      ∀ (σ : Fin (m + 1 + 1) → Bool), σ (Fin.last (m + 1)) = !σ 0 →
      (∀ b : Fin (m + 1 + 1) → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y) →
      ∀ (a : Fin (m + 1 + 1) → Zd d (sz.L n)),
        ‖STQop (d := d) ϑ u (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b) a‖ ≤
          Y + ((sz.size n : ℕ) : ℝ) ^ τN * (sz.Bctl n u ^ (m + 2) * X)

/-- **Target 4, `crudeLKM_of_level`**: a level `Y ≤ W^{C₀}` of `(𝓛-𝒦)_{u,σ}(H)` gives the crude-sup binder
of `goodSetN_A0clsQN` (`QDriftA.lean:450`) and `alt_hDclsQN` (`QDriftB.lean:395-398`). -/
def T2268_crudeLKM_of_level : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (k : ℕ) (σ : Fin k → Bool)
    (Y C₀ : ℝ),
    (∀ b : Fin k → Zd d (sz.L n), ‖sz.STLKM n E u H σ b‖ ≤ Y) → Y ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
      ‖fun b : Fin k → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀

end T2268Check

end RBM.Ind
