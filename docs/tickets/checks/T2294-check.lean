/-
Release check for T2294 (dispatcher V1, Tue Oct  6 2026; CLAUDE.md §4 step 0; DECISIONS §29, §45 O2,
§62 (2)/(4), §83, §92 (4), §95 (3), §97 (3); supervisor 2026-10-06-1102 O1).
S3-18a1 (ST-3 alternating chain, after S3-17b = T2286 merged acb4f83): vocabulary `altYSetN`, `altExitTauN`,
the high-probability `hY` event at length `n_ - 1` on the grid at the deterministic level `N^ε X` (`altYGridN`,
pinned in §2), and the compositions C1-C5 (statements free, ticket targets 1, 3-7) in the new file
`Induction/QEndA` (namespace `RBM.Ind`).  §3 pins the consumer shape of S3-18a2 (`Induction/QEndGrid`,
`altGridEndQN`; NOT proved by T2294).
Section 1: the merged names the ticket cites.  Section 2: vocabulary (copied verbatim into `QEndA.lean`) and
the pinned statement `T2294_altYGridN` (T2294 proves `RBM.Ind.altYGridN` with exactly this statement).
Section 3: the S3-18a2 shape and Prop-valued examples (no proof obligations).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree (fbec579): `lake env lean docs/tickets/checks/T2294-check.lean`.
-/
import RBM3D.Induction.QBudgetB
import RBM3D.Induction.QBudgetA
import RBM3D.Induction.QLevelsB
import RBM3D.Induction.QLevelsA
import RBM3D.Induction.QDriftB
import RBM3D.Induction.QDriftA
import RBM3D.Induction.QProxy
import RBM3D.Induction.QGridA
import RBM3D.Induction.QGridB
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.NQLin
import RBM3D.Induction.NQGood1
import RBM3D.Induction.NQGood2
import RBM3D.Induction.NQEndLin
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.GridAssemblyN
import RBM3D.Induction.GridGoodN
import RBM3D.Induction.GridDriftN
import RBM3D.Induction.GridEnvelopeN
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.Step2Events
import RBM3D.Induction.Defs
import RBM3D.Loop.KLFinal
import RBM3D.Defs.StochDomAt
import RBM3D.Path.Walk

/-! ## §1 Merged names (compiled `#check`s; namespaces from the enclosing `namespace … end` blocks) -/

-- S3-17b = T2286 (`Induction/QBudgetB`, `RBM.Ind`)
#check @RBM.Ind.altBudgetNumQN
#check @RBM.Ind.altBudgetExpQN
#check @RBM.Ind.dFlowQN_levelLin
#check @RBM.Ind.alt_hdriftLinQN
#check @RBM.Ind.dDriftAltLinQN_nonneg
#check @RBM.Ind.altBudgetExpQN_of_choice
#check @RBM.Ind.altBudgetNumQN_eventually
-- S3-17a = T2279 (`Induction/QBudgetA`, `RBM.Ind`)
#check @RBM.Ind.altBudget_kapFar
#check @RBM.Ind.qvBdAltQN
#check @RBM.Ind.cQVAltQN
#check @RBM.Ind.dDriftAltLinQN
#check @RBM.Ind.assembledRHSAltQN
#check @RBM.Ind.dDriftAltLinQN_le_shape
#check @RBM.Ind.budgetAltQN
-- S3-16a/b (`Induction/QLevelsA`, `Induction/QLevelsB`, `RBM.Ind`)
#check @RBM.Ind.altB45N_levelM
#check @RBM.Ind.startLevelQN
#check @RBM.Ind.crudeLKM_of_level
#check @RBM.Ind.goodSetN_LKM_le
#check @RBM.Ind.goodSetN_LKM_far
-- S3-15a/b (`Induction/QDriftA`, `Induction/QDriftB`, `RBM.Ind`)
#check @RBM.Ind.dFlowQN
#check @RBM.Ind.altClsQN
#check @RBM.Ind.kappaAltQN
#check @RBM.Ind.epsAltQN
#check @RBM.Ind.dGridQN_eq_dFlowQN
#check @RBM.Ind.alt_hkerQN
#check @RBM.Ind.alt_hA0clsQN
#check @RBM.Ind.alt_hDclsQN
-- S3-13a/b (`Induction/QGridA`, `Induction/QGridB`, `RBM.Ind`)
#check @RBM.Ind.aTrueQN
#check @RBM.Ind.dGridQN
#check @RBM.Ind.aFrozQN
#check @RBM.Ind.martIncQN
#check @RBM.Ind.rGridQN
#check @RBM.Ind.qErrQN
#check @RBM.Ind.gridDriftQN
#check @RBM.Ind.stoppedDuhamelQN
#check @RBM.Ind.sum_weighted_qErrQN_le
-- S3-14 = T2194 (`Induction/QProxy`, `RBM.Ind`)
#check @RBM.Ind.qvFormQN
#check @RBM.Ind.zVecQN
#check @RBM.Ind.yVecQN
#check @RBM.Ind.martIncQN_ae_eq
#check @RBM.Ind.azumaSubGQ_gridExitN
#check @RBM.Ind.qProxyCn
#check @RBM.Ind.qProxyCQ
#check @RBM.Ind.qProxy4C
#check @RBM.Ind.qProxyW0
#check @RBM.Ind.qvFormQN_le_of_bounds
#check @RBM.Ind.qvFormQN_le_of_goodSetN
#check @RBM.Ind.yMomentsQUnifN
-- S3-12a/b, S3-12c1 (`Induction/NQLin`, `Induction/NQEndLin`, `Induction/NQEndFlow`)
#check @RBM.Gauss.Sizes.GoodLinN
#check @RBM.Gauss.Sizes.nqLinPhi2
#check @RBM.Gauss.Sizes.NQLinConcl
#check @RBM.Gauss.Sizes.measurableGoodLinN
#check @RBM.Ind.nqLinExitTauN
#check @RBM.Ind.mem_of_lt_nqLinExitTauN
#check @RBM.Ind.nqLinExitMeasN
#check @RBM.Ind.nqGridEndLinN
#check @RBM.Gauss.Sizes.STXiBoot'
#check @RBM.Gauss.Sizes.STOeqQt'
-- ST2 grid layer
#check @RBM.Gauss.Sizes.STmaxLKM
#check @RBM.Gauss.Sizes.STXiLKM
#check @RBM.Gauss.Sizes.gridGood_STXiLKM_seqHflow
#check @RBM.Gauss.Sizes.GoodSetN
#check @RBM.Gauss.Sizes.measurableGoodSetN
#check @RBM.Gauss.Sizes.GridGoodNConcl
#check @RBM.Path.gridExitTauN
#check @RBM.Path.mem_of_lt_gridExitTauN
#check @RBM.Path.gridExitTauN_eq_of_forall_mem
#check @RBM.Path.gridExitTauN_measurableSet
#check @RBM.Ind.YMomentBoundsN
#check @RBM.Ind.GridAssemblyHypN
#check @RBM.Ind.AssembledN
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.stepErrN
#check @RBM.Ind.exists_norm_Kcal_le_win
#check @RBM.Ind.gridDriftN_envelope
#check @RBM.Ind.driftTensorN
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.norm_STeeM_shiftN_le
#check @RBM.Ind.hQ_nonAltN
-- pins, sizes, mollifier, walk, stochastic domination
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STCaseI
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.st_Bctl_pos
#check @RBM.Gauss.Sizes.ST_gridTime_mono
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.stKbound_holds
#check @RBM.Gauss.Sizes.STXiLK
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.Path.highProbAt_iInter
#check @RBM.Path.pathH
#check @RBM.Path.gridTime_last
#check @RBM.Path.map_pathH_eq

/-! ## §2 Vocabulary and the pinned statement (namespace `RBM.Ind.T2294Check`; copied verbatim into
`QEndA.lean`, namespace `RBM.Ind`) -/

namespace RBM.Ind.T2294Check

open MeasureTheory ProbabilityTheory Filter Matrix
open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- **The `hY` set at length `l`** (supervisor 1102 O1): the fine matrices whose `(𝓛-𝒦)^{(l)}` loops are at most
`Y · B_u^l` at every sign vector and label (the `hY` premise of `altB45N_levelM`, `alt_hdriftLinQN` at `ν X := Y`). -/
def altYSetN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ) :
    Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
  {H | ∀ (σ' : Fin l → Bool) (a' : Fin l → Zd d (sz.L n)),
    ‖sz.STLKM n E u H σ' a'‖ ≤ Y * sz.Bctl n u ^ l}

/-- **The alternating exit time**: `nqLinExitTauN` (`NQLin.lean:716`) with the `hY` set at length `k - 1` added
(`GoodSetN` at the crude level `Φc`, `GoodLinN` at the linear levels, `altYSetN` at the level `Yl`). -/
noncomputable def altExitTauN {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ)
    (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ) (τ' D' : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  gridExitTauN sz s v K n (fun j =>
    sz.GoodSetN n (E n) (gridTime s v K n j) k (Γ n) (Λ n) (Φc n) τ' D' ∩
      GoodLinN sz n (E n) (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) ∩
        altYSetN sz n (E n) (gridTime s v K n j) (k - 1) (Yl n))

/-- **Pin `T2294_altYGridN`** (target 2; supervisor 1102 O1, DECISIONS §95 (3)): from the deterministic control
`Ξ̂^{(𝓛-𝒦)}_l ≺ X` uniformly on `[s_n, v_n]`, with high probability the grid walk is in `altYSetN` at the level
`N^ε X` at every grid time `j ≤ K n` (`map_pathH_eq` at each `j` and the union bound `highProbAt_iInter`,
`K n + 1 ≤ N^C`; the pattern of (G2) in `gridGoodN_holds`).  S3-18b calls it with `l = n_ - 1`. -/
def T2294_altYGridN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) → (∀ n, K n ≠ 0) → (∀ n, 1 ≤ X n) →
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLK sz n (E n) (u : ℝ) l ω) (fun n _ _ => X n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l
          (((sz.size n : ℕ) : ℝ) ^ ε * X n)})

/-! ## §3 The S3-18a2 consumer shape (NOT proved by T2294) and examples -/

/-- **Shape of `altGridEndQN`** (S3-18a2, `Induction/QEndGrid`; format model `nqGridEndLinN`, `NQEndLin.lean:1067`):
the alternating grid endpoint with the linear right side plus the lower-length level `X` (`k = m + 2`).  Good
walk: crude `GoodSetN` (`Φc` free), `GoodLinN` at `Φ₁, Φ₂, Φ₃`, the `hY` set at length `m + 1` and level
`N^{ε₁} X`; initial hypothesis on the projected loops `𝒬_s(𝓛-𝒦)_s` (as T2284c); conclusion on `(𝓛-𝒦)_v` for
alternating `σ` (de-`𝒬` by C5d).  No `Φ²`, no `Φc`, no current-length control on the right side. -/
def T2294_altGridEndQN_shape : Prop :=
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

example : Prop := T2294_altYGridN

example : Prop := T2294_altGridEndQN_shape

example : Prop := RBM.Gauss.Sizes.STOeqQt' 3

example {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (l : ℕ) (Y : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : Prop :=
  H ∈ altYSetN sz n E u l Y

example {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (k : ℕ) (Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl : ℕ → ℝ)
    (τ' D' : ℝ) (n : ℕ) (ω : PathΩ sz) : Prop :=
  0 < altExitTauN sz E s v K k Γ Λ Φc Φ₁ Φ₂ Φ₃ Yl τ' D' n ω

end RBM.Ind.T2294Check
