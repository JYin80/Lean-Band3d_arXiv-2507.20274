/-
Release check for T2302 (dispatcher V1, Tue Oct  6 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2,
§62 (2)/(4), §95 (3), §98 (1), §105 (1); supervisor 2026-10-06-1356 O1, O5).
S3-18a2 (ST-3 alternating chain, after S3-18a1 = T2294 merged 8a0c4cd): the alternating grid endpoint
`altGridEndQN` in the new file `Induction/QEndGrid` (namespace `RBM.Ind`).
Section 1: the merged names the ticket cites (namespaces from the enclosing `namespace … end` blocks).
Section 2: the pinned statement `T2302_altGridEndQN` (= `T2294_altGridEndQN_shape` of
`docs/tickets/checks/T2294-check.lean` §3 verbatim, with `altYSetN` now the merged `RBM.Ind.altYSetN`);
T2302 proves `RBM.Ind.altGridEndQN` with exactly this statement.
Section 3: Prop-valued examples (no proof obligations).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree (8a0c4cd): `lake env lean docs/tickets/checks/T2302-check.lean`.
-/
import RBM3D.Induction.QEndA
import RBM3D.Induction.QBudgetB
import RBM3D.Induction.QBudgetA
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.QLevelsB
import RBM3D.Induction.QDriftA
import RBM3D.Induction.QDriftB
import RBM3D.Induction.QGridA
import RBM3D.Induction.QGridB
import RBM3D.Induction.QProxy
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.NQLin
import RBM3D.Induction.NQGood1
import RBM3D.Induction.NQBudget
import RBM3D.Induction.NQEndLin
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.QtNonzeroEnd
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridDriftN
import RBM3D.Induction.StepDecompN
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Defs
import RBM3D.Loop.KLFinal
import RBM3D.Defs.StochDomAt
import RBM3D.Defs.Params
import RBM3D.Path.Walk

/-! ## §1 Merged names (compiled `#check`s) -/

-- S3-18a1 = T2294 (`Induction/QEndA`, `RBM.Ind`)
#check @RBM.Ind.altYSetN
#check @RBM.Ind.altExitTauN
#check @RBM.Ind.measurableAltYSetN
#check @RBM.Ind.mem_of_lt_altExitTauN
#check @RBM.Ind.altExitMeasN
#check @RBM.Ind.altYGridN
#check @RBM.Ind.gridDriftQN_envelope
#check @RBM.Ind.assembledRHSAltQN_qErr_le
#check @RBM.Ind.hQ_altQN
#check @RBM.Ind.subGaussStop_altQN
#check @RBM.Ind.alt_hkerGridQN
#check @RBM.Ind.alt_hdriftGridQN
#check @RBM.Ind.alt_hA0clsGridQN
#check @RBM.Ind.alt_hDclsGridQN
#check @RBM.Ind.altEnd_crudeSup
#check @RBM.Ind.altEnd_driftSup
#check @RBM.Ind.altEnd_hexp
#check @RBM.Ind.altEnd_stronglyMeasurable_zVecQN
#check @RBM.Ind.altEnd_aFroz_eq_aTrue
#check @RBM.Ind.altEnd_unQ
#check @RBM.Ind.altEnd_yMomentsMax
-- S3-17a/b (`Induction/QBudgetA`, `Induction/QBudgetB`, `RBM.Ind`)
#check @RBM.Ind.cQVAltQN
#check @RBM.Ind.dDriftAltLinQN
#check @RBM.Ind.assembledRHSAltQN
#check @RBM.Ind.dDriftAltLinQN_le_shape
#check @RBM.Ind.budgetAltQN
#check @RBM.Ind.altBudgetNumQN
#check @RBM.Ind.altBudgetExpQN
#check @RBM.Ind.altBudgetExpQN_of_choice
#check @RBM.Ind.altBudgetNumQN_eventually
#check @RBM.Ind.dDriftAltLinQN_nonneg
-- S3-16a/b, S3-15a/b (`QLevelsA`, `QLevelsB`, `QDriftA`, `QDriftB`, `RBM.Ind`)
#check @RBM.Ind.altB45N_levelM
#check @RBM.Ind.startLevelQN
#check @RBM.Ind.goodSetN_LKM_far
#check @RBM.Ind.altClsQN
#check @RBM.Ind.kappaAltQN
#check @RBM.Ind.epsAltQN
#check @RBM.Ind.QDriftA_W0
-- S3-13a/b, S3-14 (`QGridA`, `QGridB`, `QProxy`, `RBM.Ind`)
#check @RBM.Ind.aTrueQN
#check @RBM.Ind.aFrozQN
#check @RBM.Ind.dGridQN
#check @RBM.Ind.rGridQN
#check @RBM.Ind.qErrQN
#check @RBM.Ind.sum_weighted_qErrQN_le
#check @RBM.Ind.zVecQN
#check @RBM.Ind.yVecQN
#check @RBM.Ind.qProxyCn
#check @RBM.Ind.qProxyCQ
#check @RBM.Ind.qProxy4C
#check @RBM.Ind.qProxyW0
#check @RBM.Ind.yMomentsQUnifN
-- grid layer, budgets, format models
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.assembledN
#check @RBM.Ind.SubGaussStopN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.exists_norm_Kcal_le_win
#check @RBM.Ind.nqBudget_merged_inputs
#check @RBM.Ind.dDriftLinN
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.nqGood1_mE_im_ge
#check @RBM.Ind.STmaxLKM_crudeN
#check @RBM.Ind.nqGridEndLinN
#check @RBM.Ind.nzGridEndN
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
-- pins, sizes, mollifier, walk
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.ST_gridTime_zero
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.ellT
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq
#check @RBM.Path.pathH

/-! ## §2 The pinned statement (namespace `RBM.Ind.T2302Check`) -/

namespace RBM.Ind.T2302Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **Pin `T2302_altGridEndQN`** (= `T2294_altGridEndQN_shape`, unchanged; format model `nqGridEndLinN`,
`NQEndLin.lean:1067`): the alternating grid endpoint (`k = m + 2`) with the linear right side plus the
lower-length level `X`.  Good walk: crude `GoodSetN` (`Φc` free), `GoodLinN` at `Φ₁, Φ₂, Φ₃`, the `hY` set
`altYSetN` at length `m + 1` and level `N^{ε₁} X`; initial hypothesis on the projected loops
`𝒬_s(𝓛-𝒦)_s` (as T2284c); conclusion on `(𝓛-𝒦)_v` for alternating `σ`.  No `Φ²`, no `Φc`, no
current-length control on the right side (DECISIONS §62 (2)/(4), §95 (3)). -/
def T2302_altGridEndQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseI s t → sz.RangeCond τ t →
    (∀ᶠ n : ℕ in atTop, (((sz.W n : ℕ) : ℝ))⁻¹ ≤ (1 - t n) / (1 - s n)) →
    ∀ m : ℕ, 1 ≤ m →
    ∀ Λ Φ₁ Φ₂ Φ₃ X : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) → (∀ n, 1 ≤ X n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        (pathP sz).real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, pathH sz s v K n j ω ∈
            sz.GoodSetN n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) (m + 1 + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
              altYSetN sz n (E n) (gridTime s v K n j) (m + 1) (((sz.size n : ℕ) : ℝ) ^ ε₁ * X n)) →
          (∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖STQop (d := d) (QopAlgebra_mollifier d (sz.L n) (m + 1) (sz.lam n)) (s n)
                  (fun b : Fin (m + 1 + 1) → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ (m + 1 + 1)) →
          ∀ σ : Fin (m + 1 + 1) → Bool, σ (Fin.last (m + 1)) = !σ 0 →
            ∀ a : Fin (m + 1 + 1) → Zd d (sz.L n),
              ‖sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n + X n) *
                  (sz.Bctl n (v n)) ^ (m + 1 + 1)

/-! ## §3 Prop-valued examples (no proof obligations) -/

example : Prop := T2302_altGridEndQN

/-- The fact behind the `lam`-patch of Design (c): at a non-positive coupling the window `ellT` is `1`. -/
example : Prop := ∀ (L : ℕ) (g t : ℝ), 1 ≤ L → g ≤ 0 → RBM.ellT L g t = 1

example {d : ℕ} (sz : Sizes d) (n m : ℕ) (C c : ℝ)
    (ϑ : ℝ → (Fin (m + 1 + 1) → Zd d (sz.L n)) → ℂ) : Prop :=
  STMollifierProps (d := d) (sz.lam n) C c ϑ

example {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (m : ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ X : ℕ → ℝ)
    (ε₁ τ' D' : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop :=
  altExitTauN sz E s v K (m + 1 + 1) Γ Λ Φc Φ₁ Φ₂ Φ₃
    (fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ * X n) τ' D' n ω = K n

end RBM.Ind.T2302Check
