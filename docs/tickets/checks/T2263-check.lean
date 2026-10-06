/-
Release check for T2263 (dispatcher V1, Tue Oct  6 06:06 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §83, §81 (3)-(4),
§80 (3), §64 (4)-(5), §62 (4), §45 O2, §29, §20, §17, §16).
**S3-15b** (ST-3, alternating chain, second ticket after S3-14; S3-15a = T2250 merged 88ee6fd `Induction/QDriftA`,
S6-09c = T2249 merged 24b85cd `Induction/QopDecay`): the decay class `hDcls` of the alternating drift
`dFlowQN = 𝒬_u(ℬ₁+ℬ₂+ℬ₃) + ℬ₄ + ℬ₅` in the merged class `altClsQN` (radius `ε'`, the radius of the merged
`goodSetN_A0clsQN`), at a `GoodSetN` matrix and as the field `hDcls` of `GridAssemblyHypN` along the walk
(explicit mollifier `QopAlgebra_mollifier`).  NOT S3-18b: `STXiBoot'`/`STOeqQt'` need the alternating endpoint
S3-18a (unwritten), see the ticket.
Section 1: `#check` of every merged name the ticket cites (exact namespaces; `main` 193512b).
Section 2: vocabulary: none (the new file adds no public `def`).
Section 3: the pinned statements as `Prop`s (namespace `RBM.Ind.T2263Check`); each is proved in
`RBM3D/Induction/QDriftB.lean` with exactly that statement, theorem name = `Prop` name without `T2263_`, in namespace
`RBM.Ind` (statement script: `example : RBM.Ind.T2263Check.T2263_x := @RBM.Ind.x`).
Section 4: well-formedness `example`s (Prop-valued, no proof obligation).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2263-check.lean`.
-/
import RBM3D.Induction.QDriftA
import RBM3D.Induction.QopDecay
import RBM3D.Induction.B45
import RBM3D.Induction.NQGood1
import RBM3D.Induction.Step2Core
import RBM3D.Induction.NQEndFlowLift
import RBM3D.Kernel.PropT

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Ind

open MeasureTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path

/-! ## 1. Merged names used (full namespaces) -/

-- `Induction/QDriftA.lean` (88ee6fd, S3-15a = T2250), namespace `RBM.Ind`
#check @RBM.Ind.altB4N                 -- :59
#check @RBM.Ind.altB5N                 -- :71
#check @RBM.Ind.dFlowQN                -- :79
#check @RBM.Ind.altClsQN               -- :93
#check @RBM.Ind.dGridQN_eq_dFlowQN     -- :131
#check @RBM.Ind.dFlowQN_sumZero        -- :143
#check @RBM.Ind.Qop_fastDecay          -- :209
#check @RBM.Ind.fastDecay_of_diamInf   -- :234
#check @RBM.Ind.QDriftA_W0             -- :403  (private spec `QDriftA_W0_spec` :409: copy)
#check @RBM.Ind.QDriftA_W0_gt_one      -- :426
#check @RBM.Ind.goodSetN_A0clsQN       -- :438  (pattern of target 5; private `QDriftA_window_of_diamInf` :389: copy)
#check @RBM.Ind.alt_hA0clsQN           -- :473  (pattern of target 6)
#check @RBM.Ind.alt_hkerQN             -- :353  (consumer shape, S3-18a)
#check @RBM.Ind.QDriftAInst.goodSetN_A0clsQN_instance  -- :1218 (instance data and crude-sup pattern)
#check @RBM.Ind.QDriftAInst.alt_hA0clsQN_instance      -- :1276
-- `Induction/QopDecay.lean` (24b85cd, S6-09c = T2249), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_derivDecay  -- :497
#check @RBM.Gauss.Sizes.QopDecay_deriv_fastDecay         -- :514
#check @RBM.Gauss.Sizes.QopDecay_thetaKer_decay          -- :636
#check @RBM.Gauss.Sizes.QopDecay_ThetaN_fastDecay        -- :762
-- `Induction/QopAlgebra.lean` (6b2494e), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier                 -- :345
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props           -- :511
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_differentiableAt -- :581
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sub                -- :860
#check @RBM.Gauss.Sizes.QopAlgebra_commutator_ThetaN         -- :871
-- `Induction/QopNorm.lean` (eb6d67a), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay   -- :378
#check @RBM.Gauss.Sizes.stQopNorm_holds       -- :261
-- `Induction/B45.lean` (1ef8fa7), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.B45_Psum_le           -- :304
#check @RBM.Gauss.Sizes.B45_norm_ThetaN_le    -- :671
#check @RBM.Gauss.Sizes.B45_Psum_ThetaN_le    -- :794
-- `Induction/Step34Pins.lean` (fc76526), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STPsum                -- :87
#check @RBM.Gauss.Sizes.STQop                 -- :92
#check @RBM.Gauss.Sizes.STMollifierProps      -- :510
-- `Induction/GridGoodN.lean` (2f246bf), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.GoodSetN              -- :124 ((Dec) :130-135, (Vb) :143-148)
-- `Induction/Step2Defs.lean` (86124dc), `Induction/DecayLoopA.lean` (6179d8c), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STLKM                 -- :68
#check @RBM.Gauss.Sizes.STksimLKM             -- :723
#check @RBM.Gauss.Sizes.STelklkM              -- :737
#check @RBM.Gauss.Sizes.STegtM                -- :750
#check @RBM.Gauss.Sizes.STdiamInf             -- DecayLoopA :71
-- `Induction/NQGood1.lean` (691566a), `Induction/NQGood2.lean` (cc96b69), namespace `RBM.Ind`
#check @RBM.Ind.driftTensorN                      -- NQGood1 :95 (= the `ℬ₁+ℬ₂+ℬ₃` block of `dFlowQN`, `rfl`)
#check @RBM.Ind.driftTensorN_norm_le_of_goodSet   -- NQGood1 :104 (crude sup of the block from (D1)-(D3))
#check @RBM.Ind.norm_loopFine_crudeN              -- NQGood1 :916
#check @RBM.Ind.NQGood1Inst.zero_mem_goodSetN_inst_grid  -- NQGood1 :1128
#check @RBM.Ind.goodSetN_A0clsN                   -- NQGood2 :284
-- `Induction/QGridA.lean` (549a62d), `Induction/GridDuhamelN.lean` (2ebee73), `Induction/GridAssemblyN.lean`
-- (686cf71), `Induction/GridDriftN.lean` (14137ce), namespace `RBM.Ind`
#check @RBM.Ind.dGridQN                   -- QGridA :1274
#check @RBM.Ind.AvecN                     -- GridDuhamelN :272
#check @RBM.Ind.GridAssemblyHypN          -- GridAssemblyN :183
#check @RBM.Ind.GridAssemblyHypN.hDcls    -- GridAssemblyN :209 (the field this ticket supplies)
#check @RBM.Ind.exists_norm_Kcal_le_win   -- GridDriftN :1098 (instances)
-- `Evolution/Pins.lean` (d9de66f), `Kernel/Evolution.lean` (ff8d36d), `Defs/Semicircle.lean` (fbc9870),
-- `Defs/Params.lean`, `Kernel/PropT.lean` (c3f3d5d), namespace `RBM`
#check @RBM.EKFastDecay     -- Pins :51
#check @RBM.EKSumZero       -- Pins :56
#check @RBM.ThetaN          -- Evolution :60
#check @RBM.mSigma          -- Semicircle :85
#check @RBM.norm_mSigma     -- Semicircle :87
#check @RBM.ellT            -- Params :32
#check @RBM.one_le_ellT     -- Params :39
#check @RBM.ellT_pos        -- Params :44
#check @RBM.ellT_mono       -- PropT :58
-- `Induction/Step2Events.lean` (7f9bfa1), `Induction/Step2Core.lean` (092aaf0), namespace `RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.ST_gridTime_zero   -- Step2Events :596
#check @RBM.Gauss.Sizes.ST_gridTime_mono   -- Step2Events :1151
#check @RBM.Gauss.Sizes.ST_gridTime_mem    -- Step2Core :387
-- `Path/Walk.lean` (ddf5f74), namespace `RBM.Path`
#check @RBM.Path.PathΩ      -- :54
#check @RBM.Path.gridTime   -- :70
#check @RBM.Path.pathH      -- :75
-- Why S3-18b is not this ticket: the R2* pins (`Induction/NQEndFlow.lean`, 0f60da2, namespace `RBM.Gauss.Sizes`)
-- and the merged non-alternating endpoint (`Induction/NQEndFlowLift.lean`, d0484be, namespace `RBM.Ind`)
#check @RBM.Gauss.Sizes.STNQConcl''   -- NQEndFlow :79 (sign vectors `∃ k, σ k = σ (finRotate n_ k)` only)
#check @RBM.Gauss.Sizes.STXiBoot'     -- NQEndFlow :95 (`STXiLK`: all sign vectors)
#check @RBM.Gauss.Sizes.STOeqQt'      -- NQEndFlow :127
#check @RBM.Gauss.Sizes.STOeqNQ''     -- NQEndFlow :124
#check @RBM.Ind.stOeqNQ''_holds       -- NQEndFlowLift :939

/-! ## 2. Vocabulary: none -/

/-! ## 3. Statements (each proved in `QDriftB.lean` with exactly this statement) -/

namespace T2263Check

/-- Target 2: the `ℬ₁+ℬ₂+ℬ₃` block decays in the `ℓ¹` window of radius `ε'` at a `GoodSetN` matrix: clause (Vb)
of `GoodSetN` (`GridGoodN.lean:143-148`, `L^∞` window `ℓ_u W^{τ'}`, three norms `≤ W^{-D'}`, triangle
inequality) and `fastDecay_of_diamInf` (`d W^{τ'} ≤ W^{ε'}`).  No threshold, no crude sup. -/
def T2263_drift13_fastDecay : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ {m n : ℕ} {E u Γ Λ Φ τ' ε' D' : ℝ}
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (σ : Fin (m + 1) → Bool),
    (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
    H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' →
    EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
      (fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b)

/-- Target 3: `ℬ₄` decays at **every** radius `ε' > 0` and depth `D'` from the crude sup of `(𝓛-𝒦)_{u,σ}(H)` alone
(no decay input): `ℬ₄ = Θ((𝒫A)ϑ) - (𝒫ΘA)ϑ = Θ(A - 𝒬A) - (ΘA - 𝒬ΘA)` (`QopAlgebra_commutator_ThetaN`,
`QopAlgebra_ThetaN_sub`); `A - 𝒬A` and `ΘA - 𝒬ΘA` decay via `stQop_sub_fastDecay` (crude sups: `‖A‖ ≤ W^{C₀}`,
`‖ΘA‖ ≤ (m+1)(1-u)⁻¹W^{C₀}` from `B45_norm_ThetaN_le`), `Θ(A - 𝒬A)` via `QopDecay_ThetaN_fastDecay` (radius
`ε'/2 → ε'`, depth `D'+K+2 → D'+1`); `2W^{-(D'+1)} ≤ W^{-D'}`. -/
def T2263_altB4N_fastDecay : Prop :=
  ∀ (d m : ℕ) (Λg K C c C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < C → 0 < c → 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ) (σ : Fin (m + 1) → Bool),
      |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      STMollifierProps (d := d) (sz.lam n) C c ϑ →
      ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H)

/-- Target 4: `ℬ₅ = (-𝒫A)_{a₁} ∂_uϑ_{u,a}` decays at every radius and depth for the explicit mollifier
(`QopDecay_deriv_fastDecay` with `B = -𝒫A`, `‖𝒫A‖ ≤ ((2^d)^m + (L^d)^m)‖A‖ ≤ W^{C₀+Km+1}` from `B45_Psum_le`). -/
def T2263_altB5N_fastDecay_moll : Prop :=
  ∀ (d m : ℕ) (K C₀ ε' D' : ℝ), 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ)
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin (m + 1) → Bool),
      0 < sz.lam n → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ‖fun b : Fin (m + 1) → Zd d (sz.L n) => sz.STLKM n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
      EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D'
        (altB5N sz n E u (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ H)

/-- Target 5: **the drift class at a matrix**, general mollifier: `dFlowQN … u … H ∈ altClsQN … ε' Dc uu i` with
`δ = 4W^{-D'}` whenever `ℓ_u ≤ ℓ_{uu i}` (index shift of `hDcls`): sum-zero from `dFlowQN_sumZero`; on the `ℓ¹`
window `W^{ε'}ℓ_u`: `|𝒬_u(ℬ₁₋₃)| ≤ 2W^{-D'}` (target 2 + `Qop_fastDecay` at the threshold `QDriftA_W0`, crude
sup of the block a hypothesis), `|ℬ₄|, |ℬ₅| ≤ W^{-D'}` (hypotheses; targets 3, 4).  Threshold and radius are
those of the merged `goodSetN_A0clsQN` (same `QDriftA_W0 d m K C c C₀ ε' D'`, same `hdW`). -/
def T2263_dFlowQN_clsQN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d), 3 ≤ d → ∀ (m : ℕ) (K C c C₀ ε' D' : ℝ), 0 < C → 0 < c → 0 < ε' →
    ∀ {n : ℕ} {E u Γ Λ Φ τ' Dc : ℝ} {uu : ℕ → ℝ} {i : ℕ},
    QDriftA_W0 d m K C c C₀ ε' D' ≤ ((sz.W n : ℕ) : ℝ) →
    ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
    (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
    4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
    |E| ≤ 2 → 0 < sz.lam n → 0 ≤ u → u < 1 →
    ellT (sz.L n) (sz.lam n) u ≤ ellT (sz.L n) (sz.lam n) (uu i) →
    ∀ {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ},
    H ∈ sz.GoodSetN n E u (m + 1) Γ Λ Φ τ' D' →
    ∀ (ϑ : ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), STMollifierProps (d := d) (sz.lam n) C c ϑ →
    (∀ a : Fin (m + 1) → Zd d (sz.L n), DifferentiableAt ℝ (fun τ => ϑ τ a) u) →
    ∀ (σ : Fin (m + 1) → Bool),
    ‖fun b : Fin (m + 1) → Zd d (sz.L n) => driftTensorN sz n E u H σ b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
    EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB4N sz n E u ϑ σ H) →
    EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε' D' (altB5N sz n E u ϑ σ H) →
    altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc uu i
      (4 * ((sz.W n : ℕ) : ℝ) ^ (-D')) (dFlowQN sz n E u ϑ σ H)

/-- Target 6: **the field `hDcls` of `GridAssemblyHypN`** (`GridAssemblyN.lean:209`) for the alternating chain at the
explicit mollifier: `Cls = altClsQN … ε' Dc (gridTime s v Kg n)`, `δD ≡ 4W^{-D'}`, `Dr j ω = dGridQN … j ω`, on
`{j < Kg n, j < τ ω}`, when `H_j ∈ GoodSetN(u_j)` for `j < τ` (as `alt_hA0clsQN`) and the two crude sups hold there;
`dGridQN_eq_dFlowQN`, target 5 at `uu = gridTime s v Kg n`, `i = j + 1` (`ℓ_{u_j} ≤ ℓ_{u_{j+1}}`: `ellT_mono`,
`ST_gridTime_mono`, `ST_gridTime_mem`), targets 3, 4 at `u = u_j` (`(1-u_j)⁻¹ ≤ (1-v_n)⁻¹ ≤ W^K`), the mollifier
facts `QopAlgebra_mollifier_props` (`C = (1+40dm)6^{dm}`, `c = 1/2`) and `QopAlgebra_mollifier_differentiableAt`. -/
def T2263_alt_hDclsQN : Prop :=
  ∀ (d m : ℕ) (Λg K C₀ ε' D' : ℝ), 3 ≤ d → 0 < Λg → 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (σ : Fin (m + 1) → Bool) (E s v : ℕ → ℝ) (Kg : ℕ → ℕ)
      (Γ Λ Φ : ℕ → ℝ) (τ' Dc : ℝ) (τ : PathΩ sz → ℕ),
      |E n| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λg → W₀ ≤ ((sz.W n : ℕ) : ℝ) →
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      0 ≤ s n → s n ≤ v n → v n < 1 → (1 - v n)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      (d : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ ε' →
      4 * ((sz.W n : ℕ) : ℝ) ^ (-D') ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dc) →
      (∀ (ω : PathΩ sz) (j : ℕ), j < τ ω → pathH sz s v Kg n j ω ∈
        sz.GoodSetN n (E n) (gridTime s v Kg n j) (m + 1) (Γ n) (Λ n) (Φ n) τ' D') →
      (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
          sz.STLKM n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ C₀) →
      (∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
        ‖fun b : Fin (m + 1) → Zd d (sz.L n) =>
          driftTensorN sz n (E n) (gridTime s v Kg n j) (pathH sz s v Kg n j ω) σ b‖ ≤
          ((sz.W n : ℕ) : ℝ) ^ C₀) →
      ∀ (ω : PathΩ sz) (j : ℕ), j < Kg n → j < τ ω →
        altClsQN d (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) ε' Dc (gridTime s v Kg n) (j + 1)
          (4 * ((sz.W n : ℕ) : ℝ) ^ (-D'))
          (dGridQN sz E s v Kg n (QopAlgebra_mollifier d (sz.L n) m (sz.lam n)) σ j ω)

/-! ## 4. Well-formedness (Prop-valued; no proof obligation) -/

example : Prop := T2263_drift13_fastDecay ∧ T2263_altB4N_fastDecay ∧ T2263_altB5N_fastDecay_moll ∧
  T2263_dFlowQN_clsQN ∧ T2263_alt_hDclsQN

/-- The class statement of target 5 at `H = 0`, the explicit mollifier, `d = 3`, `m = 3` (the instance shape). -/
example : Prop :=
  ∀ (sz : Sizes 3) (n : ℕ),
    altClsQN 3 (sz.L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) (1 / 5) 2 (fun _ => (0 : ℝ)) 1
      (4 * ((sz.W n : ℕ) : ℝ) ^ (-(3 : ℝ)))
      (dFlowQN sz n 0 0 (QopAlgebra_mollifier 3 (sz.L n) 3 (sz.lam n)) (fun _ : Fin (3 + 1) => true)
        (0 : Matrix (Idx 3 (sz.L n) (sz.W n)) (Idx 3 (sz.L n) (sz.W n)) ℂ))

/-- The block of target 2 is the first `STQop` argument of `dFlowQN` (`Finset.Icc 3 (m+1)`, `k = m + 1`). -/
example : Prop :=
  ∀ (sz : Sizes 3) (n : ℕ) (E u : ℝ)
    (H : Matrix (Idx 3 (sz.L n) (sz.W n)) (Idx 3 (sz.L n) (sz.W n)) ℂ) (σ : Fin (3 + 1) → Bool),
    (fun b : Fin (3 + 1) → Zd 3 (sz.L n) => driftTensorN sz n E u H σ b) =
      (fun b : Fin (3 + 1) → Zd 3 (sz.L n) => ∑ l ∈ Finset.Icc 3 (3 + 1), sz.STksimLKM n E u H l (loopOf σ b) +
        sz.STelklkM n E u H (loopOf σ b) + sz.STegtM n E u H (loopOf σ b))

end T2263Check

end RBM.Ind

end
