/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QProxy

/-!
# Compiled nonempty instances of `Induction/QProxy` (T2498, row U3s3a, sibling file)

The instances of the `𝒬`-proxy layer (§11 of the previous layout of `QProxy.lean`, moved here verbatim where their statement still reads a
declaration of `QProxy`, namespace `RBM.Ind.QProxyInst`), and the instances of the generic twins over the carrier
`bandStep2Mat sz E` (`d = 3`, the band data `sz0`, `szB`).  The items that applied the band proofs replaced in place
(`qv_at_propagatorQ`, `azumaSubGQ_ugenN`, `ugenPairQN_le_of_bounds`, the private body of `yMomentsQUnifN`) are re-pointed at the generic theorems.
Imported only by `RBM3D.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Green RBM.BA

namespace QProxyInst

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.GridGoodNInst RBM.Ind.GridDriftNCheck
  RBM.Ind.QGridACheck RBM.Ind.AzumaProxyNInst

/-! ### Generic items (T2498): the carrier `bandStep2Mat sz0 E`, `d = 3`

D1, the generic `𝒬`-proxy statements and their instances at the band carrier (kernel coupling `gK = sz0.lam`, `A = 1`, `Cv = C4`);
BA readings are in the ticket's check only. -/

open RBM.Gauss.Step34Inst in
/-- **Instance of D1** (`qProxyG_kerEK4_band`) at the band flow `(szB, zB)` of `Step34Pins` (`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `d = 3`, `k = 2`,
`KL = 3`: the constant `C4 > 0` exists and the class holds eventually in `n`. -/
theorem qProxyG_kerEK4_band_instance :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ᶠ n in atTop, QProxyG_KerEK4 (bandFM szB (STflowE zB)) szB.lam 2 3 C4 n :=
  (qProxyG_kerEK4_band 3 le_rfl 2 le_rfl (1 / 10) (1 / 10) (1 / 10) 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).imp
    fun _ h => ⟨h.1, h.2 szB (1 / 6) zB flow_zB⟩

/-- **Instance of `martIncQNg_ae_eq`** at `bandStep2Mat sz0 E0` (the data of `martIncQN_ae_eq_instance`). -/
theorem martIncQNg_ae_eq_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    ∀ᵐ ω ∂(bandStep2Mat sz0 E0).Pp, martIncQNg (bandStep2Mat sz0 E0) s0 t0 K0 0 moll sigma4 0 ω a =
      zVecQNg (bandStep2Mat sz0 E0) s0 t0 K0 0 0 moll sigma4 ω a + yVecQNg (bandStep2Mat sz0 E0) s0 t0 K0 0 0 moll sigma4 ω a :=
  martIncQNg_ae_eq (stepDecompGen_loopForm_band sz0 E0 (fun _ => by norm_num [E0])) (stepDecompGen_walkForm_band sz0 E0)
    s0 t0 K0 0 0 (hierDriftGen_kLink_band sz0 E0 0) (by norm_num [s0]) (by norm_num [s0, t0]) (by norm_num [t0])
    (by norm_num [K0]) (by norm_num [K0]) moll sigma4 a

/-! ### Item 1: `martIncQN_ae_eq` -/

theorem martIncQN_ae_eq_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    ∀ᵐ ω ∂(pathP sz0), martIncQN sz0 E0 s0 t0 K0 0 moll sigma4 0 ω a =
      zVecQN sz0 E0 s0 t0 K0 0 0 moll sigma4 ω a + yVecQN sz0 E0 s0 t0 K0 0 0 moll sigma4 ω a :=
  martIncQN_ae_eq sz0 E0 s0 t0 K0 0 0 (by norm_num [E0]) (by rw [data.2.2]; norm_num) moll sigma4 a

/-! ### Item 2: `qv_at_propagatorQ` at a non-scalar Hermitian `M` -/

/-- The non-scalar Hermitian matrix `X_{(0,0,true)}`. -/
abbrev Mx : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ :=
  coordinateMatrix 3 (sz0.L 0) (sz0.W 0)
    ((0 : Idx 3 (sz0.L 0) (sz0.W 0)), (0 : Idx 3 (sz0.L 0) (sz0.W 0)), true)

/-- **Instance of `qv_at_propagatorQg`** at `bandStep2Mat sz0 Einst` and the non-scalar Hermitian `Mx`. -/
theorem qv_at_propagatorQg_instance (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    ∑ c : CoordF 3 (sz0.L 0) (sz0.W 0), (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) c : ℝ) *
        ‖∑ b : Fin (3 + 1) → Zd 3 (sz0.L 0),
          (∏ i : Fin (3 + 1), Step2Gen_uKer (bandStep2Mat sz0 Einst).toFlowFM 0 (sigma4 i) (sigma4 (finRotate (3 + 1) i))
            (1 / 3) (1 / 2) (a i) (b i)) *
          STQop (d := 3) moll (1 / 3) (fun b'' => RBM.Ind.dirDerivN (fun H => (bandStep2Mat sz0 Einst).LM 0 (1 / 3) H sigma4 b'') Mx
            (coordinateMatrix 3 (sz0.L 0) (sz0.W 0) c)) b‖ ^ 2 ≤
      ((3 + 1 : ℕ) : ℝ) * qvFormQNg (bandStep2Mat sz0 Einst) 0 moll (1 / 3) (1 / 2) sigma4 Mx a :=
  qv_at_propagatorQg (qvPropagatedNg (bandStep2Mat sz0 Einst) Einst sz0.lam
    (stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt) (fun _ => rfl))
    (gridRepTailGen_ker_band sz0 Einst 0 (Einst_abs_lt 0).le) (1 / 3) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) Mx (coordinateMatrix_isHermitian 3 (sz0.L 0) (sz0.W 0) _) 3 (by norm_num) moll sigma4 a


/-! ### Item 3: `qqTensorN_sumZero` at the delta tensor and the merged mollifier -/

/-- The delta tensor `1_{(0,0)}` on `(Fin (m + 1) → Z_L^d)²` (nonzero, not sum-zero). -/
def deltaTensor {d L : ℕ} (m : ℕ) : (Fin (m + 1) → Zd d L) → (Fin (m + 1) → Zd d L) → ℂ :=
  fun c c' => if c = 0 ∧ c' = 0 then 1 else 0

/-- The delta tensor `𝒜 = 1_{(0,0)}` on `(Fin 2 → Z_5^3)²`. -/
abbrev Adelta : (Fin (1 + 1) → Zd 3 5) → (Fin (1 + 1) → Zd 3 5) → ℂ := deltaTensor 1

theorem Adelta_ne : Adelta ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [Adelta, deltaTensor] at this

/-- `𝒜` itself is not sum-zero (in the first block, at `b' = 0`): the conclusion of `qqTensorN_sumZero` is a
property of `𝒬 ⊗ 𝒬̄ 𝒜`, not of `𝒜`. -/
theorem Adelta_not_sumZero : ¬ EKSumZero (fun b => Adelta b 0) := by
  intro h
  have h1 := h 0 rfl 0
  simp [Adelta, deltaTensor] at h1

theorem qqTensorN_sumZero_instance (t : ℝ) :
    (∀ b', EKSumZero (fun b => qqTensorN (QopAlgebra_mollifier 3 5 1 1) t Adelta b b')) ∧
      (∀ b, EKSumZero (fun b' => qqTensorN (QopAlgebra_mollifier 3 5 1 1) t Adelta b b')) :=
  qqTensorN_sumZero (QopAlgebra_mollifier 3 5 1 1) t
    ((QopAlgebra_mollifier_props 3 5 1 (by norm_num) one_pos).1 t) Adelta

private theorem hL_Ei : StepDecompGen_LoopForm (bandStep2Mat sz0 Einst) Einst :=
  stepDecompGen_loopForm_band sz0 Einst Einst_abs_lt

private theorem hW_Ei : StepDecompGen_WalkForm (bandStep2Mat sz0 Einst) sz0.lam (fun _ => 0) :=
  stepDecompGen_walkForm_band sz0 Einst

private theorem hQV_Ei : QVPropagatedNg (bandStep2Mat sz0 Einst) sz0.lam :=
  qvPropagatedNg (bandStep2Mat sz0 Einst) Einst sz0.lam hL_Ei (fun _ => rfl)

private theorem hKer_Ei : GridRepTailGen_Ker (bandStep2Mat sz0 Einst).toFlowFM 0 :=
  gridRepTailGen_ker_band sz0 Einst 0 (Einst_abs_lt 0).le

/-! ### Item 5: the sub-Gaussian input (grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`, `E ≡ 1/2`, `n = 0`) -/

/-- **Instance of `azumaSubGQ_ugenNg`** at `bandStep2Mat sz0 Einst`: for every target time `p ∈ (0, 4]` and label `a`, with `τ ≡ K 0 = 4`,
`G 0 = {0}` (`H_0 = 0`, `s ≡ 0`) and `G j = {Hermitian}`, and `Q` the exact variance form at `M = 0`. -/
theorem azumaSubGQ_ugenNg_instance (p : ℕ) (hp : p ≤ Kg 0) (hp0 : 0 < p)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) :
    SubGaussStopNg (bandStep2Mat sz0 Einst) sigma4 (gridTime sInst vg Kg 0) (fun _ => Kg 0)
      (fun j ω => zVecQNg (bandStep2Mat sz0 Einst) sInst vg Kg 0 j moll sigma4 ω) p a 0
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) *
        qvFormQNg (bandStep2Mat sz0 Einst) 0 moll (gridTime sInst vg Kg 0 (0 + 1)) (gridTime sInst vg Kg 0 p)
          sigma4 0 a))) := by
  refine azumaSubGQ_ugenNg (azumaSubGNg (bandStep2Mat sz0 Einst) hW_Ei sInst vg Kg) hL_Ei hQV_Ei sInst_nonneg sInst_le_vg
    vg_lt_one 0 3 hKer_Ei (by norm_num) moll sigma4 (fun _ => Kg 0) (fun j M => M.IsHermitian ∧ (j = 0 → M = 0))
    (fun j => MeasurableSet.const _)
    (fun ω j hj => ⟨pathH_isHermitian sz0 sInst vg Kg 0 j ω, fun hj0 => by
      subst hj0
      exact azumaProxy_pathH_zero_of_s_zero sz0 sInst vg Kg 0 rfl ω⟩) p hp a 0 hp0 _
    (fun M hM _ => ?_)
  rw [hM.2 rfl]
  exact Real.le_coe_toNNReal _

/-- **Instance of `azumaSubGQ_gridExitNg` with `hQ` discharged**: the family `G j = {0}` (measurable) and `Q` the exact variance form at `M = 0`. -/
theorem azumaSubGQ_gridExitNg_instance_zero (p : ℕ) (hp : p ≤ Kg 0)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < p) :
    SubGaussStopNg (bandStep2Mat sz0 Einst) sigma4 (gridTime sInst vg Kg 0)
      (gridExitTauNg (bandStep2Mat sz0 Einst) sInst vg Kg 0 (fun _ =>
        ({0} : Set (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))))
      (fun j ω => zVecQNg (bandStep2Mat sz0 Einst) sInst vg Kg 0 j moll sigma4 ω) p a j
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) *
        qvFormQNg (bandStep2Mat sz0 Einst) 0 moll (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 p)
          sigma4 0 a))) :=
  azumaSubGQ_gridExitNg (azumaSubGNg (bandStep2Mat sz0 Einst) hW_Ei sInst vg Kg) hL_Ei hW_Ei hQV_Ei sInst_nonneg
    sInst_le_vg vg_lt_one 0 3 hKer_Ei (by norm_num) moll sigma4 (fun _ => {0}) (fun _ => measurableSet_singleton 0) p hp a j hj _
    (fun M hM _ => by
      rw [Set.mem_singleton_iff.1 hM]
      exact Real.le_coe_toNNReal _)

/-- **Instance of `azumaSubGQ_gridExitN`** at the exit time of the good sets `GoodSetN … u_j` (measurable by
`measurableGoodSetN`), any levels `Γ Λ Φ` and exponents `τ' D'`; the deterministic majorant `hQ` stays a
hypothesis (the work of the Step 3 tickets S3-15/S3-18, as in the merged `azumaSubGN_goodExit_instance`). -/
theorem azumaSubGQ_gridExitN_instance (Γ Λ Φ τ' D' : ℝ) (p : ℕ) (hp : p ≤ Kg 0)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < p) (Q : ℝ≥0)
    (hQ : ∀ M ∈ sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D',
      M.IsHermitian → gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) * qvFormQN sz0 0 moll (Einst 0)
        (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 p) sigma4 M a) ≤ (Q : ℝ)) :
    SubGaussStopN sz0 (Einst 0) sigma4 (gridTime sInst vg Kg 0)
      (gridExitTauN sz0 sInst vg Kg 0 (fun j =>
        sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D'))
      (fun j ω => zVecQN sz0 Einst sInst vg Kg 0 j moll sigma4 ω) p a j Q :=
  azumaSubGQ_gridExitN sz0 Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one 0 3 (by norm_num) moll
    sigma4 (fun j => sz0.GoodSetN 0 (Einst 0) (gridTime sInst vg Kg 0 j) (3 + 1) Γ Λ Φ τ' D')
    (fun j => measurableGoodSetN 3 sz0 0 _ _ _ _ _ _ _ _) p hp a j hj Q hQ

/-- **Instance of `azumaSubGQ_gridExitN` with `hQ` discharged**: the family `G j = {0}` (measurable) and `Q` the
exact variance form at `M = 0`. -/
theorem azumaSubGQ_gridExitN_instance_zero (p : ℕ) (hp : p ≤ Kg 0)
    (a : Fin (3 + 1) → Zd 3 (sz0.L 0)) (j : ℕ) (hj : j < p) :
    SubGaussStopN sz0 (Einst 0) sigma4 (gridTime sInst vg Kg 0)
      (gridExitTauN sz0 sInst vg Kg 0 (fun _ =>
        ({0} : Set (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ))))
      (fun j ω => zVecQN sz0 Einst sInst vg Kg 0 j moll sigma4 ω) p a j
      (Real.toNNReal (gridStep sInst vg Kg 0 * (((3 + 1 : ℕ) : ℝ) *
        qvFormQN sz0 0 moll (Einst 0) (gridTime sInst vg Kg 0 (j + 1)) (gridTime sInst vg Kg 0 p)
          sigma4 0 a))) :=
  azumaSubGQ_gridExitN sz0 Einst_abs_lt sInst_nonneg sInst_le_vg vg_lt_one 0 3 (by norm_num) moll
    sigma4 (fun _ => {0}) (fun _ => measurableSet_singleton 0) p hp a j hj _
    (fun M hM _ => by
      rw [Set.mem_singleton_iff.1 hM]
      exact Real.le_coe_toNNReal _)

/-! ### Item 6: `yMomentsQUnifN` with `P > 0` -/

/-- `RangeCond` at the instance: `N^{-1+1/2} ≤ 1 - 1/32` for `N ≥ 4` (copy of the private
`azumaProxy2_rangeCond_vg`). -/
private theorem rangeCond_vg : sz0.RangeCond (1 / 2) vg := by
  filter_upwards [sz0_tendsto.eventually_ge_atTop (4 : ℝ)] with n hn
  have h4 : (0 : ℝ) < 4 := by norm_num
  have h := Real.rpow_le_rpow_of_nonpos h4 hn (show (-1 + (1 / 2 : ℝ)) ≤ 0 by norm_num)
  have h2 : (4 : ℝ) ^ (-1 + (1 / 2 : ℝ)) = 1 / 2 := by
    rw [show (-1 + (1 / 2 : ℝ)) = -(1 / 2) by norm_num, Real.rpow_neg (by norm_num)]
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : (1 : ℝ) - vg n = 31 / 32 := by norm_num [vg]
  rw [h3]
  linarith

private theorem Kg_ne_zero : ∀ n, Kg n ≠ 0 := fun n => by simp [Kg]

private theorem gridStep_pos (n : ℕ) : 0 < gridStep sInst vg Kg n := by
  unfold gridStep
  exact div_pos (by norm_num [vg, sInst]) (Nat.cast_pos.2 (Nat.pos_of_ne_zero (Kg_ne_zero n)))

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity
/-- **Instance of `yMomentsQUnifNg`** (the explicit positive level, `qProxy_yMomentsQPosg`; `m = 3`, every `σ`, `ϑ_n = QopAlgebra_mollifier`,
`C = (1 + 40·9)·6^9`, `c = 1/2`) at `bandStep2Mat sz0 Einst` (`κm = √1/2`): `C_P` before the grid `K = Kg`, applied at a concrete `n`
from the eventual filter, with the stopping time `τ ≡ K n` and the window `Δ > 0`. -/
theorem yMomentsQUnifNg_instance_pos (σ : Fin (3 + 1) → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 < P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsNg (bandStep2Mat sz0 Einst) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => yVecQNg (bandStep2Mat sz0 Einst) sInst vg Kg n j
          (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := qProxy_yMomentsQPosg hL_Ei hW_Ei (fun n => gridRepTailGen_ker_band sz0 Einst n (Einst_abs_lt n).le)
    (Real.sqrt 1 / 2) (1 / 2) sInst vg (DecayGen_bandSpec sz0 one_pos (fun n => by norm_num [Einst])) sInst_nonneg sInst_le_vg
    vg_lt_one sz0_tendsto rangeCond_vg 3 ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1 / 2)
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (by positivity) (by norm_num)
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n,
    hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩



/-- **Instance of `yMomentsQUnifN`** itself (the public statement, `0 ≤ P`). -/
theorem yMomentsQUnifN_instance (σ : Fin (3 + 1) → Bool) :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      0 < gridStep sInst vg Kg n ∧
      YMomentBoundsN sz0 (Einst n) σ (gridTime sInst vg Kg n) (fun _ => Kg n) (Kg n)
        (fun j ω => yVecQN sz0 Einst sInst vg Kg n j
          (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) σ ω)
        (fun _ => gridStep sInst vg Kg n ^ 2 * P) (fun _ => gridStep sInst vg Kg n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, hev⟩ := yMomentsQUnifN sz0 1 (1 / 2) Einst sInst vg one_pos
    (fun n => by norm_num [Einst]) sInst_nonneg sInst_le_vg vg_lt_one sz0_tendsto rangeCond_vg 3
    ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1 / 2)
    (fun n => QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) (by positivity) (by norm_num)
    (fun n => QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) (lam_pos_n n)) σ
  obtain ⟨n, P, hP0, hPN, hτ⟩ := (hev Kg Kg_ne_zero).exists
  exact ⟨C_P, hC, n, P, hP0, hPN, gridStep_pos n,
    hτ (fun _ => Kg n) (fun j => MeasurableSet.const _)⟩


/-! ### Item 4: targets 4-6 (`qqTensorBoundsN`, `ugenPairQN_le_of_bounds`, `qvFormQN_le_of_bounds`,
`qvFormQN_le_of_goodSetN`) -/

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem mE_zero_im_ge : (1 / 2 : ℝ) ≤ (mE 0).im := by
  rw [mE_zero_im]; norm_num

private theorem etaT_zero_zero : etaT 0 0 = 1 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem diam_append_zero {d L k : ℕ} :
    STdiamInf (Fin.append (0 : Fin k → Zd d L) (0 : Fin k → Zd d L)) = 0 := by
  have h : ∀ i, Fin.append (0 : Fin k → Zd d L) (0 : Fin k → Zd d L) i = 0 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; rfl
    · rw [Fin.append_right]; rfl
  unfold STdiamInf
  refine (Finset.sup_eq_bot_iff _ _).2 fun p _ => ?_
  simp [h, zdistInf]

/-! #### Target 5 at `d = 3`, `k = 2`, `L = 5`, `g = 1/2`, `W = 25` -/

/-- `e = (1,0,0) ∈ Z_5^3`. -/
private abbrev e5 : Zd 3 5 := ![1, 0, 0]

/-- The sum-zero vector `w = 1_{(0,0)} - 1_{(0,e)}` on `(Z_5^3)²` (first coordinate fixed). -/
def w5 : (Fin 2 → Zd 3 5) → ℂ := fun b =>
  (if b = ![0, 0] then 1 else 0) - (if b = ![0, e5] then 1 else 0)

private theorem zero_ne_e5 : (0 : Zd 3 5) ≠ e5 := by
  intro h
  have := congrFun h 0
  simp only [e5, Pi.zero_apply, Matrix.cons_val_zero] at this
  exact absurd this (by decide)

private theorem b1_ne_b2 : (![0, 0] : Fin 2 → Zd 3 5) ≠ ![0, e5] := by
  intro h
  exact zero_ne_e5 (congrFun h 1)

private theorem zdistD_e5 : zdistD 3 5 e5 = 1 := by
  unfold zdistD
  simp only [zdist, e5, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    ZMod.val_zero, tsub_zero, zero_le, inf_of_le_left, add_zero, Matrix.cons_val]
  decide

theorem w5_sumZero : EKSumZero w5 := by
  intro i₀ hi x
  have hi0 : i₀ = 0 := Fin.ext (by simpa using hi)
  subst hi0
  unfold w5
  rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [Finset.mem_filter]

private theorem w5_b1 : w5 ![0, 0] = 1 := by
  simp only [w5, b1_ne_b2, ↓reduceIte]
  norm_num

theorem w5_ne : w5 ≠ 0 := by
  intro h
  have := congrFun h ![0, 0]
  simp only [w5, b1_ne_b2, ↓reduceIte, Pi.zero_apply] at this
  norm_num at this

private theorem w5_norm (b : Fin 2 → Zd 3 5) : ‖w5 b‖ ≤ 1 := by
  by_cases h1 : b = ![0, 0]
  · subst h1
    simp only [w5, b1_ne_b2, ↓reduceIte]
    norm_num
  · by_cases h2 : b = ![0, e5]
    · subst h2
      simp only [w5, h1, ↓reduceIte]
      norm_num
    · simp only [w5, h1, h2, ↓reduceIte]
      norm_num

private theorem w5_small (b : Fin 2 → Zd 3 5) (hb : w5 b ≠ 0) :
    ∀ i j : Fin 2, (zdistD 3 5 (b i - b j) : ℝ) ≤ 1 := by
  have hb' : b = ![0, 0] ∨ b = ![0, e5] := by
    by_contra h
    rw [not_or] at h
    apply hb
    simp only [w5, h.1, h.2, ↓reduceIte]
    norm_num
  rcases hb' with rfl | rfl
  · simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp
  · simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simp
    · have : (![0, e5] : Fin 2 → Zd 3 5) 0 - (![0, e5] : Fin 2 → Zd 3 5) 1 = -e5 := by simp
      rw [this, zdistD_neg, zdistD_e5]; norm_num
    · have : (![0, e5] : Fin 2 → Zd 3 5) 1 - (![0, e5] : Fin 2 → Zd 3 5) 0 = e5 := by simp
      rw [this, zdistD_e5]; norm_num
    · simp

/-- The pair tensor `T = w ⊗ w` (sum-zero in each block, supported on tuples of spread `≤ 1`). -/
def T5 : (Fin 2 → Zd 3 5) → (Fin 2 → Zd 3 5) → ℂ := fun b b' => w5 b * w5 b'

theorem T5_ne : T5 ≠ 0 := by
  intro h
  have := congrFun (congrFun h ![0, 0]) ![0, 0]
  simp only [T5, w5_b1, Pi.zero_apply] at this
  norm_num at this

private theorem rpow25 : (25 : ℝ) ^ (1 / 2 : ℝ) = 5 := by
  rw [← Real.sqrt_eq_rpow, show (25 : ℝ) = 5 ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

private theorem ellT_five_le : ellT 5 (1 / 2) (1 / 2) ≤ 1 := by
  unfold ellT
  refine (min_le_left _ _).trans (max_le ?_ le_rfl)
  rw [div_le_one (Real.sqrt_pos.2 (by rw [abs_of_pos (by norm_num)]; norm_num))]
  exact (Real.le_sqrt' (by norm_num : (0 : ℝ) < 1 / 2)).2
    (by rw [abs_of_pos (by norm_num)]; norm_num)

private theorem zdistD_222 : zdistD 3 5 (![2, 2, 2] : Zd 3 5) = 6 := by
  unfold zdistD
  simp only [zdist, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  decide

/-- The `ℓ¹` window of the instance (`W^ε ℓ_s = 5`) is attained: the tuple `(0, (2,2,2))` has `ℓ¹`-spread `6`. -/
private theorem window_five :
    ∃ b : Fin 2 → Zd 3 5, ∃ i j,
      (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ) := by
  refine ⟨![0, ![2, 2, 2]], 1, 0, ?_⟩
  have h1 : (![0, ![2, 2, 2]] : Fin 2 → Zd 3 5) 1 - (![0, ![2, 2, 2]] : Fin 2 → Zd 3 5) 0 =
      ![2, 2, 2] := by simp
  rw [h1, zdistD_222, rpow25]
  have := ellT_five_le
  push_cast
  nlinarith
/-- The sizes of the instance of target 5: `L = 5`, `W = 25`, `lam = 1/2` (constant sequences). -/
def szQP : Sizes 3 where
  L := fun _ => 5
  W := fun _ => 25
  lam := fun _ => 1 / 2
  three_le_L := fun _ => by norm_num
  W_pos := fun _ => by norm_num

/-- **Instance of `ugenPairQNg_le_of_bounds`** (target 3): the carrier `bandFM szQP (fun _ => 0)` (`d = 3`, `L = 5`, `W = 25`, `gK = lam = 1/2`, `A = 1`),
`k = 2`, `C4 = Cv = qProxy4C 3 2 1 (1/2) 2` (D1 by `qProxyG_kerEK4_band_at`), `ε₁ = ε = 1/2` (`W^ε = 5 ≤ 6`, the `ℓ¹`-diameter of the torus: the window is
attained), `D₂ = 4 > k + 1`, `s = 1/2 < t = 9/10`, `σ = (+,-)`, the nonzero tensor `T = w ⊗ w`, sum-zero in each block, `M' = 1`, `δ' = 0`: every
hypothesis is discharged. -/
theorem ugenPairQNg_le_of_bounds_instance (a : Fin 2 → Zd 3 (szQP.L 0)) :
    (∃ b : Fin 2 → Zd 3 5, ∃ i j,
      (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) ∧
    ‖Step2Gen_UN (bandFM szQP (fun _ => 0)) 0 ![true, false] (1 / 2) (9 / 10)
        (fun b => Step2Gen_UN (bandFM szQP (fun _ => 0)) 0 (fun i => !(![true, false] : Fin 2 → Bool) i) (1 / 2) (9 / 10)
          (fun b' => T5 b b') a) a‖ ≤
      (25 ^ (qProxy4C 3 2 1 (1 / 2) 2 * (1 / 2 : ℝ)) *
          (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2) *
        ((25 ^ (qProxy4C 3 2 1 (1 / 2) 2 * (1 / 2 : ℝ)) *
            (((1 / 2 : ℝ) ^ 2 + |1 - 1 / 2|) / ((1 / 2 : ℝ) ^ 2 + |1 - 9 / 10|)) ^ 2) * 1 +
          25 ^ qProxy4C 3 2 1 (1 / 2) 2 * 0) +
        25 ^ qProxy4C 3 2 1 (1 / 2) 2 * (25 ^ 2 * 0) := by
  have hW5 : (4 : ℝ) ≤ (25 : ℝ) ^ (1 / 2 : ℝ) := by rw [rpow25]; norm_num
  have hlog : Real.log ((5 : ℕ) : ℝ) ≤ (25 : ℝ) ^ (1 / 2 : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((5 : ℕ) : ℝ) by norm_num)
    rw [rpow25]
    push_cast at this ⊢
    linarith
  have hLK : ((5 : ℕ) : ℝ) ^ 3 ≤ (25 : ℝ) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; norm_num
  have hz1 : ∀ b' : Fin 2 → Zd 3 5, EKSumZero (fun b => T5 b b') := by
    intro b' i₀ hi x
    have h := w5_sumZero i₀ hi x
    simp only [T5, ← Finset.sum_mul, h, zero_mul]
  have hz2 : ∀ b : Fin 2 → Zd 3 5, EKSumZero (fun b' => T5 b b') := by
    intro b i₀ hi x
    have h := w5_sumZero i₀ hi x
    simp only [T5, ← Finset.mul_sum, h, mul_zero]
  have hT : ∀ b b' : Fin 2 → Zd 3 5, ‖T5 b b'‖ ≤ 1 := fun b b' => by
    unfold T5
    rw [norm_mul]
    calc ‖w5 b‖ * ‖w5 b'‖ ≤ 1 * 1 := mul_le_mul (w5_norm b) (w5_norm b') (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hspread : ∀ b : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) →
        w5 b = 0 := by
    intro b ⟨i, j, hij⟩
    by_contra hne
    have h1 := w5_small b hne i j
    have h2 : (1 : ℝ) ≤ ellT 5 (1 / 2) (1 / 2) := one_le_ellT (by norm_num)
    rw [rpow25] at hij
    nlinarith
  have hslice : ∀ b b' : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b' i - b' j) : ℝ)) →
        ‖T5 b b'‖ ≤ 0 := by
    intro b b' hb'
    simp [T5, hspread b' hb']
  have hblock : ∀ b b' : Fin 2 → Zd 3 5,
      (∃ i j, (25 : ℝ) ^ (1 / 2 : ℝ) * ellT 5 (1 / 2) (1 / 2) ≤ (zdistD 3 5 (b i - b j) : ℝ)) →
        ‖T5 b b'‖ ≤ 0 := by
    intro b b' hb
    simp [T5, hspread b hb]
  have hKer := qProxyG_kerEK4_band_at szQP (fun _ => 0) (by norm_num) le_rfl one_pos (by norm_num : (0 : ℝ) < 1 / 2) two_pos 0
    (by norm_num [szQP]) (by norm_num [szQP]) (by norm_num) mE_zero_im_ge
  refine ⟨window_five, ?_⟩
  exact ugenPairQNg_le_of_bounds (bandFM szQP (fun _ => 0)) (gK := szQP.lam) (A := 1)
    (fun n' => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩) le_rfl hKer
    (gridRepTailGen_ker_band szQP (fun _ => 0) 0 (by norm_num)) le_rfl (ε := 1 / 2) (ε₁ := 1 / 2) (D₂ := 4)
    (by norm_num [szQP]) (by norm_num [szQP]) (by norm_num) (by norm_num) (by simpa [szQP] using hW5) (by simpa [szQP] using hlog)
    (by simp) (by simp) (by norm_num) (s := 1 / 2) (t := 9 / 10) (by norm_num) (by norm_num) (by norm_num [szQP]) (by norm_num [szQP])
    (σ := ![true, false]) T5 (M' := 1) (δ' := 0) le_rfl (Real.rpow_nonneg (by norm_num) _) hT hz1 hz2
    hslice hblock a


/-! #### Targets 4, 6a, 6b at `sz0`, `d = 3`, `m = 3`, `E = 0`, `t = u = 0`, large `n`

`x = 2(n+1)`, `W = x^5`, `L = 2x`, `lam = x^{-6}`; `ε = 1/5` (`W^ε = x`, below the `ℓ¹`-diameter `3x` of the torus),
`τ' = 1/10` (`W^{τ'} = √x ≤ x`, below the `L^∞`-diameter `x`): the windows of the decay clauses are attained by
the tuples of `farb`. -/

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

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

/-- The far point `(x, x, x)`. -/
private def farv (n : ℕ) : Zd 3 (sz0.L n) := fun _ => (((2 * (n + 1) : ℕ) : ZMod (sz0.L n)))

private theorem zdistD_farv (n : ℕ) : zdistD 3 (sz0.L n) (farv n) = 3 * (2 * (n + 1)) := by
  unfold zdistD farv
  simp only [zdist_far, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

private theorem zdistInf_farv (n : ℕ) : zdistInf 3 (sz0.L n) (farv n) = 2 * (n + 1) := by
  unfold zdistInf farv
  simp only [zdist_far]
  rw [Finset.sup_const (Finset.univ_nonempty)]

/-- The far tuple `(0, x⃗, 0, 0)`. -/
private def farb (n : ℕ) : Fin (3 + 1) → Zd 3 (sz0.L n) := ![0, farv n, 0, 0]

/-- The `ℓ¹` window is attained: a tuple of `ℓ¹`-spread `3x ≥ x ≥ w ℓ_0`. -/
private theorem window_l1 (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j,
      w * ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ) := by
  refine ⟨farb n, 1, 0, ?_⟩
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistD_farv, ellT_sz0]
  push_cast
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The `L^∞` window is attained: `diam_∞ (0 ⧺ b') ≥ x ≥ ℓ_0 w`. -/
private theorem window_linf (n : ℕ) {w : ℝ} (hw : w ≤ 2 * ((n : ℝ) + 1)) :
    ∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * w ≤ (STdiamInf (Fin.append b b') : ℝ) := by
  refine ⟨0, farb n, ?_⟩
  have h := Finset.le_sup (f := fun q : Fin (3 + 1 + (3 + 1)) × Fin (3 + 1 + (3 + 1)) =>
      zdistInf 3 (sz0.L n) (Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) (farb n) q.1 -
        Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n)) (farb n) q.2))
    (Finset.mem_univ (Fin.natAdd (3 + 1) 1, Fin.natAdd (3 + 1) 0))
  rw [Fin.append_right, Fin.append_right] at h
  have h1 : farb n 1 - farb n 0 = farv n := by simp [farb]
  rw [h1, zdistInf_farv] at h
  have h2 : ((2 * (n + 1) : ℕ) : ℝ) ≤ (STdiamInf (Fin.append (0 : Fin (3 + 1) → Zd 3 (sz0.L n))
      (farb n)) : ℝ) := by exact_mod_cast h
  rw [ellT_sz0]
  push_cast at h2
  linarith

/-- `B_{0} = W^{-d} B_{0,0} ≤ 1` at `u = 0` (`W ≥ 2`). -/
private theorem Bctl_zero_le (n : ℕ) (hW : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) : sz0.Bctl n 0 ≤ 1 := by
  unfold Sizes.Bctl Bparam
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one, sub_zero, abs_one]
  have hL : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    have := sz0.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz0.L n)
  have h1 : (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 / 8 := by
    have : (8 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 3 := by nlinarith [sq_nonneg ((sz0.W n : ℝ))]
    calc (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 8⁻¹ := inv_anti₀ (by norm_num) this
      _ = 1 / 8 := by norm_num
  have h2 : (sz0.lam n ^ 2 + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (sz0.lam n)])
  have h3 : (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL)
  have h4 : 0 ≤ (sz0.lam n ^ 2 + 1)⁻¹ + (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹ := by positivity
  calc (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((sz0.lam n ^ 2 + 1)⁻¹ + (((sz0.L n : ℕ) : ℝ) ^ 3)⁻¹)
      ≤ (1 / 8) * (1 + 1) := by gcongr
    _ ≤ 1 := by norm_num

/-- The constant of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- The constants `C_n`, `C_Q` of the instance. -/
private noncomputable abbrev Cn3 : ℝ := qProxyCn 3 3 1 2 Cmol3 (1 / 2)
private noncomputable abbrev CQ3 : ℝ := qProxyCQ 3 3 1 2 Cmol3 (1 / 2)

/-- The decay exponent `D = C_Q + 6 > m + 2 + C_Q` of the instance. -/
private noncomputable def Dq : ℝ := CQ3 + 6

/-- The threshold `W₀` of the instance (`d = 3`, `m = 3`, `Λ_g = 1`, `K = 2`, `C₀ = 4`, `ε = 1/5`, `D = Dq`). -/
private noncomputable def R0 : ℝ := qProxyW0 3 3 1 2 Cmol3 (1 / 2) 4 (1 / 5) Dq

/-- All the numeric hypotheses of targets 4 and 6 at `sz0`, `n` with `2 (n + 1) ≥ max W₀ 10`, `ε = 1/5`,
`τ' = 1/10`, `K = 2`, `C₀ = 4`, `u = 0`, `w = 1/2`, `E = 0`. -/
private theorem sz0_numeric (n : ℕ) (hx : max R0 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    Real.log ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    R0 ≤ ((sz0.W n : ℕ) : ℝ) ∧ 0 < sz0.lam n ∧ sz0.lam n ≤ 1 ∧
    (1 / 2 : ℝ) ≤ 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ∧
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - 1 / 2) / (1 - 0) ∧
    4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0) ≤ ((sz0.W n : ℕ) : ℝ) ^ (4 : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx10 : 10 ≤ x := (le_max_right _ _).trans hx
  have hxR : R0 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have hx5 : 10 ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx10 5
  have h3 : (10 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx10 3
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx10 7
  have h20 : (10 : ℝ) ^ 20 ≤ x ^ 20 := pow_le_pow_left₀ (by norm_num) hx10 20
  have hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by rw [hxW]; nlinarith
  have hlam0 : 0 < sz0.lam n := lam_pos_n n
  have hlam1 : sz0.lam n ≤ 1 := lam_le_one n
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  refine ⟨by rw [hxW]; nlinarith, ?_, ?_, ?_, ?_, ?_, hlam0, hlam1, ?_, ?_, ?_⟩
  · rw [hW15]; linarith
  · rw [hW15, hL, Real.log_mul (by norm_num) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)
    have h2 := Real.log_two_lt_d9
    linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
    have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
    push_cast
    nlinarith
  · rw [hxW]
    exact hxR.trans (le_self_pow₀ hx1 (by norm_num))
  · have hL4 : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by rw [hL]; linarith
    rw [le_sub_comm, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (sz0.lam n)]
  · calc (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hW2
      _ = (1 - 1 / 2) / (1 - 0) := by norm_num
  · rw [etaT_zero_zero, div_one, hxW, rpow_pow5 hx0, show (5 : ℝ) * 4 = ((20 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    have hB1 := Bctl_zero_le n hW2
    have hB0 : 0 ≤ sz0.Bctl n 0 := (STBctl_pos sz0 n (by norm_num)).le
    have hB8 : (sz0.Bctl n 0) ^ (2 * (3 + 1)) ≤ 1 := pow_le_one₀ hB0 hB1
    nlinarith

/-- The closed form of `qvFormQN_le_of_bounds` at the data of the instance (`v = u = 0`, `w = 1/2`, `m = 3`,
`Λ_g = 1`, `κ' = 1/2`, `K = 2`, `ε = 1/5`, `D = Dq`). -/
private noncomputable def bdQ (n : ℕ) (Mee : ℝ) : ℝ :=
  (((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
      ((sz0.lam n ^ 2 + |1 - 0|) / (sz0.lam n ^ 2 + |1 - 1 / 2|)) ^ (3 + 1)) *
    ((((sz0.W n : ℕ) : ℝ) ^ (qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * (1 / 5 : ℝ)) *
        ((sz0.lam n ^ 2 + |1 - 0|) / (sz0.lam n ^ 2 + |1 - 1 / 2|)) ^ (3 + 1)) *
      (((sz0.W n : ℕ) : ℝ) ^ (2 * Cn3 * (1 / 5 : ℝ)) * Mee + ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) +
      ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 * ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) +
    ((sz0.W n : ℕ) : ℝ) ^ qProxy4C 3 (3 + 1) 1 (1 / 2) 2 *
      (((sz0.W n : ℕ) : ℝ) ^ (3 + 1) * ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3))

private theorem hD_inst : ((3 : ℕ) : ℝ) + 2 + CQ3 < Dq := by
  unfold Dq
  push_cast
  linarith

/-- `0 ∈ GoodSetN` at `u = 0` with the levels `Γ = 4`, `Λ = 100`, `Φ = 1` (`Γ² Λ = 1600 ≥ 4 · 2^8`). -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 (1 / 10) Dq := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

/-- `n` large enough for all of `sz0_numeric` and the windows. -/
private theorem exists_big_n : ∃ n : ℕ, max R0 10 ≤ 2 * ((n : ℝ) + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max R0 10)
  exact ⟨n, by have := Nat.cast_nonneg (α := ℝ) n; linarith⟩

/-- `W^{τ'} ≤ x` and `W^ε ≤ x` at `τ' = 1/10`, `ε = 1/5`. -/
private theorem W_rpow_le_x (n : ℕ) (hx : max R0 10 ≤ 2 * ((n : ℝ) + 1)) :
    ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ 2 * ((n : ℝ) + 1) ∧
      ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
  obtain ⟨-, -, -, -, h3, -⟩ := sz0_numeric n hx
  obtain ⟨hW, -, -⟩ := sz0_facts n
  have hx10 : 10 ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx0 : 0 ≤ 2 * ((n : ℝ) + 1) := by linarith
  have h15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = 2 * ((n : ℝ) + 1) := by
    rw [hW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hpos : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_nonneg (by positivity) _
  refine ⟨?_, h15.le⟩
  push_cast at h3
  linarith
/-- **Instance of `qvFormQNg_le_of_bounds`** (target 3) at `bandStep2Mat sz0 (fun _ => 0)` (`gK = sz0.lam`, `A = 1`, `ε₁ = ε = 1/5`,
`C4 = Cv = qProxy4C`, D1 by `qProxyG_kerEK4_band_at`): the data of `qvFormQN_le_of_bounds_instance`; the bounds on `𝓔 ⊗ 𝓔` are the clauses
(D4) and (Vb) of the membership `0 ∈ GoodSetN`. -/
theorem qvFormQNg_le_of_bounds_instance :
    ∃ n : ℕ,
      (∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf (Fin.append b b') : ℝ)) ∧
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        qvFormQNg (bandStep2Mat sz0 (fun _ => 0)) n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (1 / 2) sigma4 0 a ≤
          bdQ n (4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨hWx, -⟩ := W_rpow_le_x n hx
  refine ⟨n, window_linf n hWx, fun a => ?_⟩
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := zero_mem_inst n hlam1
  have hKer := qProxyG_kerEK4_band_at sz0 (fun _ => 0) (by norm_num) (by norm_num : 2 ≤ 3 + 1) one_pos
    (by norm_num : (0 : ℝ) < 1 / 2) two_pos n hlam0 hlam1 (by norm_num) mE_zero_im_ge
  exact qvFormQNg_le_of_bounds (d := 3) (m := 3) (by norm_num) (by norm_num) 1 2 Cmol3 (1 / 2) one_pos two_pos (by positivity)
    (by norm_num) (bandStep2Mat sz0 (fun _ => 0)) (gK := sz0.lam) (A := 1) (fun n' => ⟨mul_self_nonneg _, le_rfl, by rw [one_mul]⟩)
    le_rfl hlam0 hlam1 hKer (gridRepTailGen_ker_band sz0 (fun _ => 0) n (by norm_num)) le_rfl
    (ε := 1 / 5) (ε₁ := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num) (by norm_num) hWε hlog (by norm_num)
    (by norm_num) hWε (by simp) hLK hdW (by simp) (by norm_num) hD_inst hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (v := 0) (w := 1 / 2) le_rfl (by norm_num) hwL hWt
    (σ := sigma4) 0 (Mee := 4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) hMee
    (fun b b' => hD4 sigma4 b b') (fun b b' hfar => hVb sigma4 b b' hfar) a


/-- **Instance of `qvFormQN_le_of_goodSetN`** (target 6b) at `sz0`, `d = 3`, `m = 3` (`k = 4`), `σ = (+,-,+,-)`,
`Λ_g = 1`, `κ' = 1/2`, `K = 2`, the merged mollifier (`C = (1 + 40·9)·6^9`, `c = 1/2`), `ε = 1/5`, `τ' = 1/10`,
`C₀ = 4`, `D = C_Q + 6`, `E = 0`, `u = 0`, `w = 1/2`, `H = 0 ∈ GoodSetN` with the levels `(Γ, Λ, Φ) = (4, 100, 1)`,
at an `n` with `W_n ≥ W₀` (`qProxyW0`): every hypothesis is discharged; `Φ` is arbitrary (here `1`).  The far clause
(Vb) is exercised: there is a pair `(b, b')` with `ℓ_0 W^{τ'} ≤ diam_∞(b ⧺ b')` (the window fits in the torus). -/
theorem qvFormQN_le_of_goodSetN_instance :
    ∃ n : ℕ,
      (∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf (Fin.append b b') : ℝ)) ∧
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        qvFormQN sz0 n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 0 (1 / 2) sigma4 0 a ≤
          bdQ n (4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨hWx, -⟩ := W_rpow_le_x n hx
  refine ⟨n, window_linf n hWx, fun a => ?_⟩
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  exact qvFormQN_le_of_goodSetN (d := 3) (m := 3) (by norm_num) (by norm_num) 1 (1 / 2) 2 Cmol3
    (1 / 2) one_pos (by norm_num) two_pos (by positivity) (by norm_num) sz0 n hlam0 hlam1
    (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (by norm_num) hD_inst hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (u := 0) (w := 1 / 2) le_rfl
    (by norm_num) hwL hWt (E := 0) (by norm_num) mE_zero_im_ge (σ := sigma4) (Γ := 4) (Λ := 100)
    (Φ := 1) (zero_mem_inst n hlam1) hMee a

/-- **Instance of `qvFormQN_le_of_bounds`** (target 6a) at the same data: the bounds on `𝓔 ⊗ 𝓔` are the clauses
(D4) and (Vb) of the membership `0 ∈ GoodSetN`; `M_ee = 4 (4 · 100) B_0^8 / η_0`. -/
theorem qvFormQN_le_of_bounds_instance :
    ∃ n : ℕ,
      (∃ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ellT (sz0.L n) (sz0.lam n) 0 *
        ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ (STdiamInf (Fin.append b b') : ℝ)) ∧
      ∀ a : Fin (3 + 1) → Zd 3 (sz0.L n),
        qvFormQN sz0 n (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 0 (1 / 2) sigma4 0 a ≤
          bdQ n (4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨hWx, -⟩ := W_rpow_le_x n hx
  refine ⟨n, window_linf n hWx, fun a => ?_⟩
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  obtain ⟨-, -, -, -, -, -, hD4, -, hVb⟩ := zero_mem_inst n hlam1
  exact qvFormQN_le_of_bounds (d := 3) (m := 3) (by norm_num) (by norm_num) 1 (1 / 2) 2 Cmol3
    (1 / 2) one_pos (by norm_num) two_pos (by positivity) (by norm_num) sz0 n hlam0 hlam1
    (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num) (by norm_num) hWε hlog hLK hdW
    (by norm_num) hD_inst hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (v := 0) (w := 1 / 2) le_rfl
    (by norm_num) hwL hWt (E := 0) (by norm_num) mE_zero_im_ge (σ := sigma4) 0
    (Mee := 4 * (4 * 100) * ((sz0.Bctl n 0) ^ (2 * (3 + 1)) / etaT 0 0)) hMee
    (fun b b' => hD4 sigma4 b b') (fun b b' hfar => hVb sigma4 b b' hfar) a

/-- **Instance of `qqTensorBoundsN`** (target 4) at `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `g = lam_n`), `d = 3`,
`m = 3`, `Λ_g = 1`, `K = 2`, the merged mollifier at `t = 0` (`ℓ_0 = 1`), `ε = 1/5`, `τ' = 1/10`, `C₀ = 4`, `D = C_Q + 6`,
the nonzero delta tensor `T = 1_{(0,0)}` (`M_ee = 1`, support of `L^∞`-spread `0`), at an `n` with `W_n ≥ W₀`
(`qProxyW0`): every hypothesis is discharged; the windows of (ii), (iii) are attained (a tuple of `ℓ¹`-spread
`3x ≥ W^ε ℓ_0`). -/
theorem qqTensorBoundsN_instance :
    ∃ n : ℕ, deltaTensor (d := 3) (L := sz0.L n) 3 ≠ 0 ∧
      (∃ b : Fin (3 + 1) → Zd 3 (sz0.L n), ∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) *
        ellT (sz0.L n) (sz0.lam n) 0 ≤ (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) ∧
      (∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
        ‖qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b'‖ ≤
          ((sz0.W n : ℕ) : ℝ) ^ (2 * Cn3 * (1 / 5 : ℝ)) * 1 + ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) ∧
      (∀ b : Fin (3 + 1) → Zd 3 (sz0.L n),
        EKFastDecay (d := 3) (L := sz0.L n) (sz0.lam n) 0 ((sz0.W n : ℕ) : ℝ) (1 / 5) (Dq - CQ3)
          (fun b' => qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b')) ∧
      (∀ b' b : Fin (3 + 1) → Zd 3 (sz0.L n),
        (∃ i j, ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) * ellT (sz0.L n) (sz0.lam n) 0 ≤
          (zdistD 3 (sz0.L n) (b i - b j) : ℝ)) →
          ‖qqTensorN (QopAlgebra_mollifier 3 (sz0.L n) 3 (sz0.lam n)) 0 (deltaTensor 3) b b'‖ ≤
            ((sz0.W n : ℕ) : ℝ) ^ (-Dq + CQ3)) := by
  obtain ⟨n, hx⟩ := exists_big_n
  obtain ⟨-, hWx⟩ := W_rpow_le_x n hx
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW₀, hlam0, hlam1, hwL, hWt, hMee⟩ := sz0_numeric n hx
  have hW1 : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hW.le
  have hDn : Cn3 + 2 < Dq := by
    have : (0 : ℝ) < qProxyCn 3 3 1 2 Cmol3 (1 / 2) :=
      qProxyCn_pos (by norm_num) 3 one_pos two_pos (by positivity) (by norm_num)
    simp only [Dq, CQ3, Cn3, qProxyCQ]
    linarith
  have hT : ∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n), ‖deltaTensor (d := 3) (L := sz0.L n) 3 b b'‖ ≤ 1 := by
    intro b b'
    unfold deltaTensor
    split_ifs <;> simp
  have hTfar : ∀ b b' : Fin (3 + 1) → Zd 3 (sz0.L n),
      ellT (sz0.L n) (sz0.lam n) 0 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤
        (STdiamInf (Fin.append b b') : ℝ) →
        ‖deltaTensor (d := 3) (L := sz0.L n) 3 b b'‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (-Dq) := by
    intro b b' hfar
    by_cases hb : b = 0 ∧ b' = 0
    · exfalso
      obtain ⟨rfl, rfl⟩ := hb
      rw [diam_append_zero, Nat.cast_zero] at hfar
      have h1 : 0 < ellT (sz0.L n) (sz0.lam n) 0 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) :=
        mul_pos (ellT_pos (by have := sz0.three_le_L n; exact_mod_cast (by omega : 1 ≤ sz0.L n)))
          (Real.rpow_pos_of_pos (by linarith) _)
      linarith
    · have : deltaTensor (d := 3) (L := sz0.L n) 3 b b' = 0 := by simp [deltaTensor, hb]
      rw [this]
      simpa using Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) _
  have h := qqTensorBoundsN (d := 3) (m := 3) (by norm_num) 1 2 Cmol3 (1 / 2) one_pos two_pos
    (by positivity) (by norm_num) (L := sz0.L n) (sz0.three_le_L n) (g := sz0.lam n) hlam0 hlam1
    (W := ((sz0.W n : ℕ) : ℝ)) (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 4) (D := Dq) hW (by norm_num)
    (by norm_num) hWε hLK hdW (by norm_num) hDn hW₀
    (QopAlgebra_mollifier_props 3 (sz0.L n) 3 (sz0.three_le_L n) hlam0) (t := 0) le_rfl
    (by norm_num) (deltaTensor 3) (Mee := 1)
    (Real.one_le_rpow hW1 (by norm_num)) hT hTfar
  refine ⟨n, ?_, window_l1 n hWx, h⟩
  intro h0
  have := congrFun (congrFun h0 0) 0
  simp [deltaTensor] at this

end QProxyInst
end RBM.Ind

end
