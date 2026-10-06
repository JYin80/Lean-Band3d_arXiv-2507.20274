/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.CouplingWindow
import RBM3D.BA.FlowPins
import RBM3D.Induction.Step1Setup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Real.Sqrt

/-!
# BA-S2a (T2205 portmap): `(lRB1)` is deterministic at `s₀ = 1 - c₁` for the members of `Fam(0)`

Paper: `paper/tex/7_8_light_weight.tex` (`7_8:1987-1990`, Step 1 of `lem:main_ind_BA`, "same as [RBSO1D, Section 7.1]";
D536 = T2205b).  Namespace `RBM.BA`.  Moved verbatim from the compiled T2205 probe
(`RBM3D/Probe/T2205Pins.lean` at `96e4087`, `:1250-1254`, `:1284-1291`, `:1293-1295`, `:1775-1784`; only the docstring of
`BATrivialLmax` changes, BA-S2 to BA-S2a and the registry class):

* `BAFamZ` (route (A) family `Fam(u)`), `BAflow_T0_bounds` (`0 < t₀ < 1`), `BAFamZ_main` (the main flow is a member);
* `BATrivialLmax` (the pin), proved by `BATrivialLmax_holds`.

New (proved here): `BAFamZ_lam0_window` (the member's coupling lies in the window `[√(1 - c₁) g₀, g₀]`),
`BAFamZ_im_m_ge` (`Im m(E, g₀') ≥ κ` by `BAWinBulk`), `baFM_loop_det` (the deterministic loop bound of any block
Anderson carrier, `‖𝓛^{(k)}‖ ≤ η⁻ᵏ (W^{-d})^{k-1}`; model `s1_loop_det`, `Step1Setup.lean:653`), and
`BATrivialLmax_holds` (second branch of `s1_h55`, `Step1Setup.lean:732-758`, with the block Anderson carrier).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal Topology Kronecker

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

section Family

variable {d : ℕ}

/-- Route (A) family at time `u`, the horizon cone: spectral parameters `z'` with the energy of `z` and a horizon
`t₀(z') ∈ [min(t₀(z), max(u, 1 - c₁)), t₀(z)]` (so `u ≤ t₀(z')` when `u ≤ t₀(z)`). -/
def BAFamZ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (z' : ℕ → ℂ) : Prop :=
  ∀ n, BAflowEs sz z' n = BAflowEs sz z n ∧
    min (BAflowT0 sz z n) (max (u n) (1 - c₁)) ≤ BAflowT0 sz z' n ∧ BAflowT0 sz z' n ≤ BAflowT0 sz z n

/-- In the chain domain `Im z > 0`, `Im m(z, g) > 0` and `0 < t₀ < 1`. -/
theorem BAflow_T0_bounds {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 < (z n).im ∧ 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im ∧ 0 < BAflowT0 sz z n ∧ BAflowT0 sz z n < 1 := by
  obtain ⟨hκm, hz1, -⟩ := h.2 n
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hzpos : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) hz1
  have hmpos : 0 < (BAm d (sz.L n) (sz.lam n) (z n)).im := lt_of_lt_of_le hκ hκm
  exact ⟨hzpos, hmpos, BAt0_pos hzpos hmpos, BAt0_lt_one hzpos hmpos⟩

/-- *Proved.* The main flow is a member of the family at every time `u` (all data). -/
theorem BAFamZ_main (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) : BAFamZ sz z c₁ u z :=
  fun _ => ⟨rfl, min_le_left _ _, le_rfl⟩

/-- *Proved.* The coupling of a member of `Fam(0)` lies in the window `[√(1 - c₁) g₀, g₀]` of the main flow
(`g₀ = BAflowLam0 sz z`, `g₀' = BAflowLam0 sz z'`): `t₀' ≥ min(t₀, 1 - c₁) ≥ (1 - c₁) t₀` since `0 < t₀ < 1`, and `t₀' ≤ t₀`. -/
theorem BAFamZ_lam0_window {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hlam : ∀ n, 0 < sz.lam n) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) {z' : ℕ → ℂ}
    (hfam : BAFamZ sz z c₁ (fun _ => 0) z') (n : ℕ) :
    Real.sqrt (1 - c₁) * BAflowLam0 sz z n ≤ BAflowLam0 sz z' n ∧ BAflowLam0 sz z' n ≤ BAflowLam0 sz z n := by
  obtain ⟨-, -, ht0, ht1⟩ := BAflow_T0_bounds hκ hflow n
  obtain ⟨-, hlo, hhi⟩ := hfam n
  have hmax : max (0 : ℝ) (1 - c₁) = 1 - c₁ := max_eq_right (by linarith)
  rw [hmax] at hlo
  have hlo' : (1 - c₁) * BAflowT0 sz z n ≤ BAflowT0 sz z' n := by
    rcases le_total (BAflowT0 sz z n) (1 - c₁) with h | h
    · rw [min_eq_left h] at hlo
      nlinarith
    · rw [min_eq_right h] at hlo
      nlinarith
  have hl := hlam n
  have hc : (0 : ℝ) ≤ 1 - c₁ := by linarith
  refine ⟨?_, ?_⟩
  · unfold BAflowLam0
    rw [← mul_assoc, ← Real.sqrt_mul hc]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hlo') hl.le
  · unfold BAflowLam0
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hhi) hl.le

/-- *Proved.* `Im m(E, g₀') ≥ κ` for the member's own carrier: `BAWinBulk` at `g' = g₀'` (by `BAFamZ_lam0_window`), and the
member has the energy of `z`. -/
theorem BAFamZ_im_m_ge {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (hlam : ∀ n, 0 < sz.lam n) {c₁ : ℝ} (hc₁ : 0 < c₁) (hc₁' : c₁ ≤ 1 / 2) (hwin : BAWinBulk sz z c₁ κ)
    {z' : ℕ → ℂ} (hfam : BAFamZ sz z c₁ (fun _ => 0) z') (n : ℕ) :
    κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := by
  obtain ⟨h1, h2⟩ := BAFamZ_lam0_window hκ hflow hlam hc₁ hc₁' hfam n
  have h := hwin n (BAflowLam0 sz z' n) h1 h2
  have hE : BAflowEs sz z' n = BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n)) := (hfam n).1
  unfold BAmF
  rw [hE]
  exact h

end Family

section LoopDet

variable {d : ℕ}

private theorem Step1Trivial_seqHflowBA_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) : (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

private theorem Step1Trivial_blockMat_herm {L W : ℕ} [NeZero L] [NeZero W]
    {M : Matrix (Idx d L W) (Idx d L W) ℂ} (hM : M.IsHermitian) :
    (blockMat d L W M).IsHermitian :=
  hM.submatrix _

/-- *Proved.* The deterministic loop bound of any block Anderson carrier `baFM sz lam0 E`: if `0 < η ≤ Im z_u` then
`‖𝓛^{(k)}_{u,σ,a}‖ ≤ η⁻ᵏ (W^{-d})^{k-1}` (`‖G‖ ≤ 1/η` and the loop bound in one step, `norm_loopM_le_sharp`;
the block Anderson form of `s1_loop_det`, `Step1Setup.lean:653`). -/
theorem baFM_loop_det (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (u η : ℝ) (hη : 0 < η)
    (hz : η ≤ (ztOf (BAmF sz lam0 E n) (E n) u).im) (k : ℕ) (hk : 1 ≤ k) (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖(baFM sz lam0 E).L n u σ a ω‖ ≤ η⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hz' : η ≤ |(ztOf (BAmF sz lam0 E n) (E n) u).im| := hz.trans (le_abs_self _)
  have h1 := norm_loopM_le_sharp d (sz.L n) (sz.W n)
    (Step1Trivial_blockMat_herm (Step1Trivial_seqHflowBA_herm sz lam0 n u ω)) hη hz' σ a
  change ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω)
    (ztOf (BAmF sz lam0 E n) (E n) u) σ a‖ ≤ _
  simpa [loopFine] using h1

end LoopDet

section Trivial

/-- **(lRB1) is deterministic below `1 - c₁`** (BA-S2a): at the constant time `s₀ = 1 - c₁` every member of the window has the loop
bound `max |𝓛^{(k)}_{s₀}| ≺ (W^{-d} B_{s₀,0})^{k-1}` (`η_{s₀} = c₁ Im m(E, g') ≥ c₁ κ`, `‖G‖ ≤ 1/η`, `W^{-d} ≤ (lam² + 1) Bctl`, `lam ≤ 𝔡⁻¹`
eventually, constants `(c₁κ)^{-k} (𝔡⁻² + 1)^{k-1}` absorbed by `N^τ`).  The same estimate at every `u ≤ 1 - c₁` gives `(lRB1)` there
(`(1-s) Bctl_s ≥ (1-u) Bctl_u` for `s ≤ u`: `x ↦ x/(g² + x) + L^{-d}` increases).  *Proved* (`BATrivialLmax_holds`); no registry line (DECISIONS §20). -/
def BATrivialLmax (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
      ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
        ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ (fun _ => 0) z' →
          STLmaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) (fun _ => 1 - c₁)

/-- *Proved.* `(lRB1)` at `s₀ = 1 - c₁`: `Im z_{s₀} = c₁ Im m(E, g₀') ≥ c₁ κ` (`BAFamZ_im_m_ge`), so
`‖𝓛^{(k)}‖ ≤ (c₁κ)^{-k} (W^{-d})^{k-1}` (`baFM_loop_det`); `W^{-d} ≤ (lam² + 1) Bctl` (`s1_Wd_le_Bctl`) and
`lam ≤ 𝔡⁻¹` eventually (`(eq:WO)`) give `‖𝓛^{(k)}‖ ≤ C Bctl^{k-1}` eventually, `C = (c₁κ)^{-k} (𝔡⁻² + 1)^{k-1}`, which
is absorbed by `N^τ` (`StochDomAt.const_mul_left`).  The law plays no role (deterministic bound). -/
theorem BATrivialLmax_holds (d : ℕ) : BATrivialLmax d := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hfam k hk
  have hsize := Ind.s1_hsize sz hflow.1.2.2.1
  have hu0 : (0 : ℝ) ≤ 1 - c₁ := by linarith
  have hu1 : 1 - c₁ < 1 := by linarith
  have hζ : ∀ n, 0 < sz.Bctl n (1 - c₁) := fun n => sz.STBctl_pos n hu1
  set C : ℝ := (c₁ * κ)⁻¹ ^ k * ((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hrefl : StochDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n _ _ => (sz.Bctl n (1 - c₁)) ^ (k - 1)) (fun n _ _ => (sz.Bctl n (1 - c₁)) ^ (k - 1)) :=
    StochDomAt.refl hsize fun n _ _ => pow_nonneg (hζ n).le _
  have hCdom := StochDomAt.const_mul_left hsize hC0
    (fun n _ _ => pow_nonneg (hζ n).le _) hrefl
  refine StochDomAt.of_subset hCdom fun τ hτ => ⟨τ, hτ, ?_⟩
  filter_upwards [hflow.1.2.2.2.2] with n hWO
  rintro ω ⟨p, hp⟩
  refine ⟨p, lt_of_lt_of_le hp ?_⟩
  have hlam0 : 0 ≤ sz.lam n := (hlam n).le
  have hlam2 : sz.lam n ^ 2 ≤ (𝔡⁻¹) ^ 2 := pow_le_pow_left₀ hlam0 hWO.2 2
  have hη : c₁ * κ ≤ (ztOf (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n) (BAflowEs sz z' n) (1 - c₁)).im := by
    rw [ztOf_im]
    unfold etaOf
    have h := BAFamZ_im_m_ge hκ hflow hlam hc₁ hc₁' hwin hfam n
    have : (1 - (1 - c₁)) = c₁ := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h hc₁.le
  have hdet := baFM_loop_det sz (BAflowLam0 sz z') (BAflowEs sz z') n (1 - c₁) (c₁ * κ)
    (by positivity) hη k hk p.1 p.2 ω
  have hW := Ind.s1_Wd_le_Bctl sz n hu0 hu1
  have hW' : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (1 - c₁) :=
    hW.trans (mul_le_mul_of_nonneg_right (by linarith) (hζ n).le)
  have h5 : ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) ≤
      (((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (1 - c₁)) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) hW' _
  rw [mul_pow] at h5
  calc ‖(baFMz sz z').L n (1 - c₁) p.1 p.2 ω‖
      ≤ (c₁ * κ)⁻¹ ^ k * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (k - 1) := hdet
    _ ≤ (c₁ * κ)⁻¹ ^ k * (((𝔡⁻¹) ^ 2 + 1) ^ (k - 1) * sz.Bctl n (1 - c₁) ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = C * sz.Bctl n (1 - c₁) ^ (k - 1) := by rw [hCdef]; ring

end Trivial

section Instance

open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- Instance at `d = 3` and the merged data `sz0`, `zSeq` of T2197; the window premise `BAWinBulk` (its `sz0` instance
belongs to BA-S3) is the only hypothesis. -/
example (hwin : BAWinBulk sz0 zSeq (1 / 3) (1 / 2)) :
    STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 - 1 / 3) :=
  BATrivialLmax_holds 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) hwin zSeq
    (BAFamZ_main sz0 zSeq (1 / 3) (fun _ => 0))

end Instance

end RBM.BA
