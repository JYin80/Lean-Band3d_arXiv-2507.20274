/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QtNonzeroGen
import RBM3D.Chain.NQEndLinGen
import RBM3D.Chain.NQBudgetGen
import RBM3D.Induction.QtNonzeroEnd

/-!
# The case-(ii) grid endpoint of the zero-mode-removed loops over a carrier (U3s4b, file 2; ticket T2505)

Generic form of `Induction/QtNonzeroEnd.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_Qt_nonzero` (`3_5:1561`, proof `3_5:1889-1933`), `(iisuwjyys)` (`3_5:1545`).  The shape is `nqGridEndLinNg`
(`NQEndLinGen`, T2491): the exit time is `nqLinExitTauNg`, the assembly is `assembledNg`, the drift enters per index (D5), the `Y` moments are
`yMomentsUnifNg`, the budget inputs are `nqBudget_merged_inputsg`.

* **Target 8** `nzGridEndNg`: the kernel class is D1 (`QtNZGen_KerNZ`, per index, eventually, one constant `C` fixed after `k`, loss-free), the window is
  `STCaseII` (`1 - s ≤ lam²/L²`) with R1 in the A-form (`lam² ≤ A gK²`), so the grid times satisfy the D1 window `(1 - u) L² ≤ A gK²`.
  `ZeroModeGen_KerSums` (every index) replaces `3 ≤ L`, `|E| ≤ 2`; `|E| < 2` is `LoopForm`, `‖m‖ ≤ 1` is inline; `STKbound` is the pin `STKboundgL`.
  No `𝔡`, no `WO`: the coupling window is inside D1.
* **Target 9** the compiled nonempty instance at the band carrier `bandStep2Mat szB Einst` (`d = 3`).

The model-free privates of `QtNonzeroEnd` §0-§3 are reused by `open private`; the lemmas that read `mE (E n)`, `etaT (E n)` are the band ones at the
energy `E'_n` of `NQEndLinGen_Ep` (`Im mE E'_n = Im m_n`, `etaT E'_n = Cm.eta n`), as in `NQEndLinGen`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private nzEnd_ev_H1 nzEnd_ev_H2 nzEnd_ev_H3 nzEnd_ev_H4 nzEnd_ev_H56 nzEnd_one_le_size nzEnd_step_le nzEnd_K_mul_step nzEnd_gridTime_nonneg
  nzEnd_gridTime_le nzEnd_rangeCond_mono nzEnd_ev_union from RBM3D.Induction.QtNonzeroEnd

open private NQEndLinGen_Ep NQEndLinGen_ev_hη NQEndLinGen_ev_hδ NQEndLinGen_stepErrNg_nonneg NQEndLinGen_eta_win NQEndLinGen_Hpath_collapse
  NQEndLinGen_yMomentsMax from RBM3D.Chain.NQEndLinGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The absorption lemmas `H2`, `H3` over a carrier, the collapsed window -/

section Regime

variable {d : ℕ} {sz : Sizes d}

/-- (H2) over a carrier: `C cA k (N^{ε₁})² Ls ≤ N^{ε₀}/6`, `Ls = (Im m)⁻¹ log N` (band `nzEnd_ev_H2` at `E'`). -/
private theorem QtNZEndGen_ev_H2 (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) (him1 : ∀ n, (Cm.m n).im ≤ 1)
    (hsize : sz.SizeTendsto) (k : ℕ) {C cA ε₁ ε₀ : ℝ} (hC : 0 ≤ C) (hcA : 0 ≤ cA) (hε : 2 * ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
        ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 := by
  obtain ⟨E', -, hmE, -⟩ := NQEndLinGen_Ep Cm hspec him1
  have h := nzEnd_ev_H2 sz hsize k hspec.1 (E := E') (fun n => by rw [hmE n]; exact hspec.2.1 n) hC hcA hε
  simpa only [hmE] using h

/-- (H3) over a carrier: `N^{εq} (C N^{ε₁} √(k Ls)) ≤ N^{ε₀}/12` (band `nzEnd_ev_H3` at `E'`). -/
private theorem QtNZEndGen_ev_H3 (Cm : Step2Mat sz) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) (him1 : ∀ n, (Cm.m n).im ≤ 1)
    (hsize : sz.SizeTendsto) (k : ℕ) {C εq ε₁ ε₀ : ℝ} (hC : 0 ≤ C) (hε : εq + ε₁ < ε₀) :
    ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
        Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 := by
  obtain ⟨E', -, hmE, -⟩ := NQEndLinGen_Ep Cm hspec him1
  have h := nzEnd_ev_H3 sz hsize k hspec.1 (E := E') (fun n => by rw [hmE n]; exact hspec.2.1 n) hC hε
  simpa only [hmE] using h

/-- **The collapsed window** (band `nzEnd_collapse`, `QtNonzeroEnd:572`; the case `v_n = s_n`, where `hc_pos` of the assembly fails): `H_K = H_0` and `u_K = s`, so the
projected initial bound `‖(Q^{(A)}(𝓛-𝒦)_s)(a)‖ ≤ N^{ε₁} B_s^k` with `ε₁ ≤ ε₀`, `N ≥ 1`, `Λ ≥ 1`, `Φ_i ≥ 0` is the conclusion at `v`. -/
private theorem QtNZEndGen_collapse {Cm : Step2Mat sz} {lam' : ℕ → ℝ}
    {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hW' : StepDecompGen_WalkForm Cm lam' Ψ)
    {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hv1 : v n < 1) (hsv : s n = v n) {k : ℕ} {ε₁ ε₀ Λ Φ₁ Φ₂ Φ₃ : ℝ} (hε : ε₁ ≤ ε₀) (hΛ : 1 ≤ Λ)
    (hΦ₁ : 0 ≤ Φ₁) (hΦ₂ : 0 ≤ Φ₂) (hΦ₃ : 0 ≤ Φ₃) (ω : PathΩ sz) (σ : Fin k → Bool) (A : Finset (Fin k)) (a : Fin k → Zd d (sz.L n))
    (hinit : ‖zeroModeSet d (sz.L n) A (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :
    ‖zeroModeSet d (sz.L n) A (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) a‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) * (sz.Bctl n (v n)) ^ k := by
  rw [NQEndLinGen_Hpath_collapse hW' hsv (K n) ω, ← hsv]
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nzEnd_one_le_size sz n
  have hs1 : s n < 1 := by rw [hsv]; exact hv1
  have hB : 0 ≤ (sz.Bctl n (s n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n hs1).le _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_le_rpow_of_exponent_le hN1 hε
  have h2 : 1 ≤ Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃ := by
    have := Real.one_le_rpow hΛ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  have h3 : ((sz.size n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ ^ ((1 : ℝ) / 2) + Φ₁ + Φ₂ + Φ₃) :=
    le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h2
  exact hinit.trans (mul_le_mul_of_nonneg_right (h1.trans h3) hB)

end Regime

/-! ## 2. The assembly at the exit time `nqLinExitTauNg` for one pair `(σ, A)`, `A ⊇ I_diff(σ)`

Band `nzEnd_assembly` (`QtNonzeroEnd:709`).  The kernel class is "fixed points of `Q^{(A)}`" with `κ ≡ C`, `εK ≡ 0` (`nz_hkerg`, loss-free EK-5); every tensor is
pushed through `Q^{(A)}` (drift `nz_hdriftNg`, Azuma `subGaussStop_nzNg`, moments `yMomentBounds_nzNg`, step error by `(normQA2)` = `norm_zeroModeSet_le`);
`A_{j∧τ} := 𝒰 Q^{(A)}A_0 + Σ 𝒰 (Δ Dr + Z + Y + R)` is defined by its formula (`hexp` is `rfl`) and equals `Q^{(A)}A_K` on the good walk by
`zeroModeCalc_duhamel_inside_atg`.  `GoodSetNg` is used through its `STeeMg` clause only (inside `subGaussStop_nzNg`). -/

section Assembly

variable {d : ℕ} {sz : Sizes d}

/-- **The assembly at the exit time, for one pair `(σ, A)`**.  `hKerN` is D1 (eventually in `n`, one constant `C`), `hcase` and `hR1` give the D1 window at every grid time. -/
private theorem QtNZEndGen_assembly (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm Ar : ℝ} {s v : ℕ → ℝ} {K : ℕ → ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (hKS : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ) (hGD : ∀ᶠ n : ℕ in atTop, GridDriftNgAt Cm s v K n)
    (hsize : sz.SizeTendsto) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hK0 : ∀ n, K n ≠ 0)
    (hcase : ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hR1 : ∀ n, sz.lam n ^ 2 ≤ Ar * gK n ^ 2)
    (Γ Λ Φ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (hΓ : ∀ n, 0 ≤ Γ n) (hΛ : ∀ n, 0 ≤ Λ n)
    (hΦ₁ : ∀ n, 0 ≤ Φ₁ n) (hΦ₂ : ∀ n, 0 ≤ Φ₂ n) (hΦ₃ : ∀ n, 0 ≤ Φ₃ n)
    {C τ' D' D'' D_Y τK εq D₁ C_P C_K : ℝ} (hC : 0 < C)
    (hKerN : ∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ Cm.toFlowFM gK k Ar C n)
    (hεq : 0 < εq) (hτK : 0 < τK) (hCK0 : 0 ≤ C_K)
    (hCK : D₁ + 4 * D_Y + (k : ℝ) + 2 * (C_P + 2 * (k : ℝ) + 2) + 8 ≤ C_K)
    (hKN : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hKU : ∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊)
    (hY : ∀ σ : Fin k → Bool, ∀ᶠ n : ℕ in atTop, ∃ P : ℝ, 0 ≤ P ∧
      P ≤ ((sz.size n : ℕ) : ℝ) ^ C_P ∧
      ∀ τ : PathΩ sz → ℕ, (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
        YMomentBoundsNg Cm σ (gridTime s v K n) τ (K n)
          (fun j ω => YvecNg Cm s v K n j σ ω)
          (fun _ => gridStep s v K n ^ 2 * P) (fun _ => gridStep s v K n ^ 4 * P ^ 2))
    (hδ : ∀ᶠ n : ℕ in atTop, ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-D') +
      eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    ∀ᶠ n : ℕ in atTop, ∀ σ : Fin k → Bool, ∀ A : Finset (Fin k), STIdiff σ ⊆ A → s n < v n →
      ∃ G : Set (PathΩ sz), Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) k (Γ n) (Λ n) (Φ n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          ∀ a : Fin k → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A (AvecNg Cm s v K n (K n) σ ω) a‖ ≤
              assembledRHSNZNg Cm s v K n k C (2 ^ k) Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y τK εq
                (Finset.univ.sup' Finset.univ_nonempty fun b =>
                  ‖zeroModeSet d (sz.L n) A (AvecNg Cm s v K n 0 σ ω) b‖) := by
  have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
  have him1 : ∀ n, (Cm.m n).im ≤ 1 := fun n => NQGood1Gen_im_le_one (hm n)
  have hA' := assembledNg Cm hsize k εq hεq D_Y D₁ (C_P + 2 * (k : ℝ) + 2) C_K hCK0 hCK
  have hη := NQEndLinGen_eta_win hL hm
  have hEnv := fun σ : Fin k → Bool => gridDriftNg_envelope_ev Cm μ k hk τK hτK hsize hKb hKK hη hs0 hsv hv1 hK0 hGD σ
  have hQV : QVPropagatedNg Cm lam' := qvPropagatedNg Cm E lam' hL hSeq
  have hSub : AzumaSubGNg Cm lam' s v K := azumaSubGNg Cm hW' s v K
  filter_upwards [hA', hKN, hKU, Filter.eventually_all.2 hY, Filter.eventually_all.2 hEnv, hKerN, hδ,
    hsize.eventually_ge_atTop ((4 : ℝ) ^ (k + 1)), hsize.eventually_ge_atTop 1] with
    n hAn hKNn hKUn hYn hEnvn hKerNn hδn h4n hN1
  intro σ A hσA hsvn
  obtain ⟨P, hP0, hPle, hYP⟩ := hYn σ
  have hKn : K n ≠ 0 := hK0 n
  have hK1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 hKn
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := nzEnd_step_le sz hKNn hvs
  have hKΔ : (K n : ℝ) * gridStep s v K n ≤ 1 := nzEnd_K_mul_step hKn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu0 : ∀ i ≤ K n, 0 ≤ gridTime s v K n i := fun i _ => nzEnd_gridTime_nonneg (hs0 n) (hsv n) i
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => (nzEnd_gridTime_le (hsv n) hKn hi).trans_lt (hv1 n)
  have hmono : ∀ i m, i ≤ m → m ≤ K n → gridTime s v K n i ≤ gridTime s v K n m := fun i m him _ => ST_gridTime_mono s v K n (hsv n) him
  have hsu : ∀ i, s n ≤ gridTime s v K n i := fun i => by
    have h := ST_gridTime_mono s v K n (hsv n) (Nat.zero_le i)
    rwa [ST_gridTime_zero] at h
  have hL2 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
  have hcaseU : ∀ i, (1 - gridTime s v K n i) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ Ar * gK n ^ 2 := fun i => by
    have h1 : (1 - s n) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 := by
      have := hcase n
      rwa [le_div_iff₀ hL2] at this
    have h2 : (1 - gridTime s v K n i) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ (1 - s n) * ((sz.L n : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith [hsu i]) hL2.le
    linarith [hR1 n]
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hAk : (2 : ℝ) ^ A.card ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (by simpa using Finset.card_le_univ A)
  have h4A : (4 : ℝ) ^ (A.card + 1) ≤ 4 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (by simpa using Finset.card_le_univ A))
  have h16A : (16 : ℝ) ^ (A.card + 1) ≤ 16 ^ (k + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ (by simpa using Finset.card_le_univ A))
  have h16 : (16 : ℝ) ^ (k + 1) = ((4 : ℝ) ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hdD0 : ∀ j, j ≤ K n → 0 ≤ dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) := by
    intro j hj
    have hη' := NQGood1Gen_eta_pos hL n (hu1 j hj)
    have hB := Sizes.STBctl_pos sz n (hu1 j hj)
    have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    unfold dDriftLinNg
    have h1 := hΓ n
    have h2 := hΦ₁ n
    have h3 := hΦ₂ n
    have h4 := hΦ₃ n
    positivity
  -- the data of the assembly
  set u : ℕ → ℝ := gridTime s v K n with hu
  set Δ : ℝ := gridStep s v K n with hΔdef
  set τ : PathΩ sz → ℕ := nqLinExitTauNg Cm s v K k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D' n with hτdef
  set A0 : PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun ω => zeroModeSet d (sz.L n) A (AvecNg Cm s v K n 0 σ ω) with hA0
  set Dr : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (driftTensorNg Cm n (u j) (Cm.Hpath s v K n j ω) σ) with hDr
  set Z : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => zeroModeSet d (sz.L n) A (ZvecNg Cm s v K n j σ ω) with hZ
  set Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω => zeroModeSet d (sz.L n) A (YvecNg Cm s v K n j σ ω) with hY'
  set R : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun j ω =>
    zeroModeSet d (sz.L n) A (predIncNg Cm s v K n j σ ω - ((Δ : ℝ) : ℂ) • driftTensorNg Cm n (u j) (Cm.Hpath s v K n j ω) σ) with hR
  set Af : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ := fun m ω =>
    Step2Gen_UN Cm.toFlowFM n σ (u 0) (u m) (A0 ω) +
      ∑ j ∈ Finset.range (min m (τ ω)), Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
        (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) with hAf
  set stepE : ℕ → ℝ := fun j => 2 ^ k * stepErrNg Cm.toFlowFM n k (u j) (u (j + 1)) Δ
    (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (u (j + 1)))⁻¹ ^ k) with hstepE
  have hτmeas : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω} := nqLinExitMeasNg hL hW' s v K n k Γ Λ Φ Φ₁ Φ₂ Φ₃ τ' D'
  have hmemG : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω →
      GoodSetNg Cm n (u j) k (Γ n) (Λ n) (Φ n) τ' D' (Cm.Hpath s v K n j ω) := fun ω j hj => (mem_of_lt_nqLinExitTauNg hj).1
  have hmemL : ∀ (ω : PathΩ sz) (j : ℕ), j < τ ω →
      Cm.Hpath s v K n j ω ∈ GoodLinNg Cm n (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) := fun ω j hj => (mem_of_lt_nqLinExitTauNg hj).2
  have hσA' : ∀ i, σ i ≠ σ (finRotate k i) → i ∈ A := (ZeroModeCalc_STIdiff_subset_iff σ A).1 hσA
  have hop : ∀ i m, i ≤ m → m ≤ K n → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN Cm.toFlowFM n σ (u i) (u m) X)‖ ≤ C * ‖X‖ := fun i m him hmK =>
    hKerNn (u i) (u m) (hu0 i (him.trans hmK)) (hcaseU i) (hmono i m him hmK) (hu1 m hmK) σ A hσA'
  have hZmeas : ∀ j, StronglyMeasurable[filt sz (j + 1)] (Z j) := fun j =>
    (LinearMap.continuous_of_finiteDimensional (zeroModeSetLin (d := d) (L := sz.L n) A)).comp_stronglyMeasurable
      (GridAssemblyGen_stronglyMeasurable_ZvecNg hL hW' s v K n j σ)
  have hsubG : ∀ m ≤ K n, ∀ (a : Fin k → Zd d (sz.L n)) (j : ℕ), j < m →
      SubGaussStopNg Cm σ u τ Z m a j (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j) := by
    intro m hm' a j hj
    have hrow := qtNZGen_row_of_kerNZ hKerNn hC.le (hu0 _ ((Nat.succ_le_of_lt hj).trans hm')) (hcaseU _)
      (hmono _ _ (Nat.succ_le_of_lt hj) hm') (hu1 m hm') σ A hσA' a
    exact subGaussStop_nzNg hk hSub hL hQV (hKS n) (hm n) (hS n) hs0 hsv hv1 hC.le (hΓ n) (hΛ n) hτmeas hmemG m hm' a j hj hrow
      (hδn j (lt_of_lt_of_le hj hm'))
  have hu0K : u (K n) = v n := gridTime_last s v K n hKn
  have hu00 : u 0 = s n := ST_gridTime_zero s v K n
  have hP'0 : 0 ≤ (4 : ℝ) ^ (k + 1) * P := by positivity
  have hP'le : (4 : ℝ) ^ (k + 1) * P ≤ ((sz.size n : ℕ) : ℝ) ^ (C_P + 2 * (k : ℝ) + 2) := by
    have h2 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) := by
      calc ((sz.size n : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have h3 : (4 : ℝ) ^ (k + 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) := h4n.trans h2
    calc (4 : ℝ) ^ (k + 1) * P ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 2) * ((sz.size n : ℕ) : ℝ) ^ C_P :=
          mul_le_mul h3 hPle hP0 (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (C_P + 2 * (k : ℝ) + 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  have hv : ∀ j < K n, 4 ^ (A.card + 1) * (Δ ^ 2 * P) ≤ Δ ^ 2 * ((4 : ℝ) ^ (k + 1) * P) := by
    intro j _
    calc (4 : ℝ) ^ (A.card + 1) * (Δ ^ 2 * P) ≤ 4 ^ (k + 1) * (Δ ^ 2 * P) := mul_le_mul_of_nonneg_right h4A (by positivity)
      _ = Δ ^ 2 * ((4 : ℝ) ^ (k + 1) * P) := by ring
  have hw : ∀ j < K n, 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2) ≤ Δ ^ 4 * (((4 : ℝ) ^ (k + 1) * P) ^ 2) := by
    intro j _
    calc (16 : ℝ) ^ (A.card + 1) * (Δ ^ 4 * P ^ 2) ≤ 16 ^ (k + 1) * (Δ ^ 4 * P ^ 2) := mul_le_mul_of_nonneg_right h16A (by positivity)
      _ = Δ ^ 4 * (((4 : ℝ) ^ (k + 1) * P) ^ 2) := by rw [h16]; ring
  have hbundle : GridAssemblyHypNg Cm σ u τ Δ (K n) (fun _ _ X => zeroModeSet d (sz.L n) A X = X) A0 Af Dr Z Y R
      (fun _ _ => C) (fun _ _ => 0) 0 (fun j _ => 2 ^ k * dDriftLinNg Cm n (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) (fun _ _ => 0)
      (fun m a j => cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j) (fun _ => 4 ^ (A.card + 1) * (Δ ^ 2 * P))
      (fun _ => 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2)) stepE := {
    hKer := hRow n
    hu0 := hu0
    hu1 := hu1
    hΔ0 := hΔ0
    hexp := fun m _ => Eventually.of_forall fun ω => rfl
    hκ0 := fun _ _ _ _ => hC.le
    hε0 := fun _ _ _ _ => le_rfl
    hker := nz_hkerg Cm.toFlowFM n (hKS n) σ A u (K n) C hC.le hop
    hδ0 := le_rfl
    hA0cls := fun ω _ => zeroModeSet_idem d (sz.L n) k A _
    hdDrift0 := fun ω j hj => mul_nonneg (by positivity) (hdD0 j hj.le)
    hδD0 := fun _ _ _ => le_rfl
    hdrift := fun ω j hjK hjτ b => by
      have h := nz_hdriftNg hk σ A s v K Γ Φ₁ Φ₂ Φ₃ τ hmemL ω j hjK hjτ b
      exact h.trans (mul_le_mul_of_nonneg_right hAk (hdD0 j hjK.le))
    hDcls := fun ω j _ _ => zeroModeSet_idem d (sz.L n) k A _
    hc_pos := fun m hm1 hmK a => by
      have hΔpos : 0 < Δ := div_pos (by linarith) (by exact_mod_cast Nat.pos_of_ne_zero hKn)
      have hterm : ∀ j ∈ Finset.range m, 0 < (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ) := by
        intro j hj
        have hjK : j ≤ K n := by have := Finset.mem_range.1 hj; omega
        have hη' := NQGood1Gen_eta_pos hL n (hu1 j hjK)
        have hB := Sizes.STBctl_pos sz n (hu1 j hjK)
        have hk0 : (0 : ℝ) < k := by
          have : (2 : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        have h1 := hΓ n
        have h2 := hΛ n
        have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
        have hWD : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_pos_of_pos hW0 _
        have hpos : 0 < Δ * ((k : ℝ) * C ^ 2 * (Γ n * (Γ n * Λ n) * ((sz.Bctl n (u j)) ^ (2 * k) / Cm.eta n (u j)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by positivity
        unfold cQVNZNg
        rw [NNReal.coe_pos, Real.toNNReal_pos]
        exact hpos
      exact Finset.sum_pos hterm ⟨0, Finset.mem_range.2 (by omega)⟩
    hv0 := fun _ _ => by positivity
    hw0 := fun _ _ => by positivity
    hY := yMomentBounds_nzNg σ A u τ (K n) (fun j ω => YvecNg Cm s v K n j σ ω) (fun _ => Δ ^ 2 * P) (fun _ => Δ ^ 4 * P ^ 2) (hKS n)
      (hYP τ hτmeas)
    hstepErr0 := fun j hj => mul_nonneg (by positivity)
      (NQEndLinGen_stepErrNg_nonneg Cm hspec him1 n k (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
        (by
          have := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj)
          positivity))
    hR := (hEnvn σ).mono fun ω hω j hj _ b => by
      have hse0 : 0 ≤ stepErrNg Cm.toFlowFM n k (u j) (u (j + 1)) Δ
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (u (j + 1)))⁻¹ ^ k) :=
        NQEndLinGen_stepErrNg_nonneg Cm hspec him1 n k (hu1 j hj.le) (hu1 (j + 1) hj) hΔ0
          (by
            have := NQGood1Gen_eta_pos hL n (hu1 (j + 1) hj)
            positivity)
      have hnorm : ‖predIncNg Cm s v K n j σ ω - ((Δ : ℝ) : ℂ) • driftTensorNg Cm n (u j) (Cm.Hpath s v K n j ω) σ‖ ≤
          stepErrNg Cm.toFlowFM n k (u j) (u (j + 1)) Δ (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (u (j + 1)))⁻¹ ^ k) := by
        refine (pi_norm_le_iff_of_nonneg hse0).2 fun a => ?_
        have h := hω j hj a
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, driftTensorNg]
        exact h
      calc ‖R j ω b‖ ≤ ‖R j ω‖ := norm_le_pi_norm _ b
        _ ≤ 2 ^ A.card * ‖predIncNg Cm s v K n j σ ω - ((Δ : ℝ) : ℂ) • driftTensorNg Cm n (u j) (Cm.Hpath s v K n j ω) σ‖ :=
            norm_zeroModeSet_le A _
        _ ≤ stepE j := mul_le_mul hAk hnorm (norm_nonneg _) (by positivity) }
  obtain ⟨G, hG, hGb⟩ := hAn (K n) σ u τ Δ (fun _ _ X => zeroModeSet d (sz.L n) A X = X) A0 Af Dr Z Y R (fun _ _ => C) (fun _ _ => 0) 0
    (fun j _ => 2 ^ k * dDriftLinNg Cm n (u j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) (fun _ _ => 0)
    (fun m a j => cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j) (fun _ => 4 ^ (A.card + 1) * (Δ ^ 2 * P))
    (fun _ => 16 ^ (A.card + 1) * (Δ ^ 4 * P ^ 2)) stepE ((4 : ℝ) ^ (k + 1) * P) hK1 hKUn hΔ hKΔ hP'0 hP'le hv hw hτmeas hZmeas hsubG hbundle
  refine ⟨G, hG, fun ω hω hgood a => ?_⟩
  have hτeq : τ ω = K n := gridExitTauNg_eq_of_forall_mem hgood
  have hτpos : 0 < τ ω := by rw [hτeq]; omega
  have hb := hGb ω hω hτpos (K n) le_rfl a
  have hAeq : Af (K n) ω = zeroModeSet d (sz.L n) A (AvecNg Cm s v K n (K n) σ ω) := by
    have hex := zeroModeCalc_duhamel_inside_atg Cm s v K n (hRow n).1 (hKS n) (hs0 n) (hsv n) (hv1 n) hKn σ A τ (K n) ω (min_le_left _ _)
    have hinner : ∀ j, ((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω =
        zeroModeSet d (sz.L n) A (predIncNg Cm s v K n j σ ω) + zeroModeSet d (sz.L n) A (martIncNg Cm s v K n j σ ω) := by
      intro j
      have hm' : martIncNg Cm s v K n j σ ω = ZvecNg Cm s v K n j σ ω + YvecNg Cm s v K n j σ ω := by
        funext b; simp only [YvecNg, Pi.add_apply]; ring
      have e1 : zeroModeSet d (sz.L n) A (predIncNg Cm s v K n j σ ω) = R j ω + ((Δ : ℝ) : ℂ) • Dr j ω := by
        simp only [hR, hDr]
        rw [← zeroModeSet_smul, ← zeroModeSet_add, sub_add_cancel]
      have e2 : zeroModeSet d (sz.L n) A (martIncNg Cm s v K n j σ ω) = Z j ω + Y j ω := by
        rw [hm', zeroModeSet_add]
      rw [e1, e2]
      abel
    rw [hτeq, min_self] at hex
    rw [hex]
    change Step2Gen_UN Cm.toFlowFM n σ (u 0) (u (K n)) (A0 ω) + ∑ j ∈ Finset.range (min (K n) (τ ω)),
        Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u (K n)) (((Δ : ℝ) : ℂ) • Dr j ω + Z j ω + Y j ω + R j ω) = _
    rw [hτeq, min_self]
    simp only [hinner]
    simp only [Step2Gen_UN_add, Finset.sum_add_distrib]
    rw [add_assoc]
  rw [hAeq] at hb
  refine hb.trans_eq ?_
  unfold assembledRHSNZNg
  simp only [zero_mul, add_zero]
  rfl

end Assembly

/-! ## 3. Target 8: the grid endpoint `nzGridEndNg`

Band `nzGridEndN` (`QtNonzeroEnd:979`).  Exponents (fixed order, after the carrier and the D1 constant `C`): `ε₀' = min ε₀ 1`, `ε₁ = εq = ε₀'/8`,
`D'' = 2(k+2)/𝔠 + 1`, `D' = D'' + 1`, `τ' = 1`, `τ_R = min τ 1`, `τK = 1`, `D_Y = D_t = k + 2`, `cA = 2^k`, `C_P^* = max_σ C_P(σ)` (`yMomentsUnifNg`),
`C_P' = C_P^* + 2k + 2`, `D₁' = D₁ + 1`, `C_K = D₁ + 2 C_P' + D'' + 16k + 40`. -/

section Endpoint

variable {d : ℕ} {sz : Sizes d}

/-- **`nzGridEndNg`: the case-(ii) grid endpoint of the zero-mode-removed loops over a carrier** (band `nzGridEndN`, `lem:STOeq_Qt_nonzero`, `3_5:1561`, proof
`3_5:1889-1928`; shape of `nqGridEndLinNg`).  Setting: `3 ≤ d`, `𝔠, τ > 0`, `N → ∞`, `W ≥ N^𝔠`, `0 ≤ s ≤ t < 1`, case (ii) `1 - s ≤ lam²/L²` (`STCaseII`), `1 - t ≥ N^{-1+τ}`;
R1 in the A-form `lam² ≤ Ar gK²` (so `(1 - u) L² ≤ Ar gK²` at every grid time `u ≥ s`: the window of D1).  For every length `k ≥ 2`, every kernel constant `C > 0`
with D1 (`QtNZGen_KerNZ` at the kernel coupling `gK`, eventually in `n`), deterministic levels `Λ ≥ 0` (`≥ 1` eventually), `Φ₁, Φ₂, Φ₃ ≥ 0`, end time `v ∈ [s,t]`, final loss
`ε₀ > 0` and failure exponent `D₁ > 0` there are exponents `ε₁, τ', D', C_K` such that, for every crude level `Φc` of `GoodSetNg` and every grid `N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`,
eventually there is an event `G`, `P(Gᶜ) ≤ N^{-D₁}`, on which: if the carrier walk is in `GoodSetNg(N^{ε₁}, Λ, Φc, τ', D') ∩ GoodLinNg(N^{ε₁}, Φ₁, Φ₂, Φ₃)` at every
`j ≤ K_n` and the initial zero-mode-removed loops satisfy `|(Q^{(A)}(𝓛-𝒦))_{s,σ,a}| ≤ N^{ε₁} B_s^k` for every `σ` and `A ⊇ I_diff(σ)`, then
`|(Q^{(A)}(𝓛-𝒦))_{v,σ,a}(H_{K_n})| ≤ N^{ε₀}(Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k` for every `σ`, `A ⊇ I_diff(σ)` and label `a`.  `|E n| < 2` is `LoopForm`, `|E n| ≤ 2 - κ` is
`DecayGen_Spec`, `‖Cm.m n‖ ≤ 1` is inline (D3); `ZeroModeGen_KerSums` (every `n`) replaces `3 ≤ L`; `STKbound` is the pin `STKboundgL`; the drift enters per index (D5). -/
theorem nzGridEndNg (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ]
    {E lam' gK : ℕ → ℝ} {Ψ : ∀ n : ℕ, Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {κm 𝔠 τ Ar : ℝ} (s t : ℕ → ℝ) (hd : 3 ≤ d) (h𝔠 : 0 < 𝔠) (hτ : 0 < τ)
    (hL : StepDecompGen_LoopForm Cm E) (hW' : StepDecompGen_WalkForm Cm lam' Ψ) (hspec : DecayGen_Spec Cm.toFlowFM κm)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) (hSeq : ∀ n, Cm.S n = SB d (sz.L n) (lam' n))
    (hS : ∀ (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hRow : ∀ n, GridRepTailGen_Ker Cm.toFlowFM n) (hKS : ∀ n, ZeroModeGen_KerSums Cm.toFlowFM n)
    (hKK : ∀ (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      Cm.KI n w (KLloopOf d (sz.L n) σ a) = Cm.K n w σ a)
    (hKb : STKboundgL Cm.toFlowFM μ)
    (hExp : ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand Cm s' t' K' n)
    (hKL : ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop Cm n) (hKT : ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo Cm n)
    (hU : ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep Cm.toFlowFM n)
    (hsize : sz.SizeTendsto) (hband : sz.Bandwidth 𝔠)
    (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (hcase : sz.STCaseII s t) (hrange : sz.RangeCond τ t)
    (hR1 : ∀ n, sz.lam n ^ 2 ≤ Ar * gK n ^ 2) :
    ∀ k : ℕ, 2 ≤ k → ∀ C : ℝ, 0 < C → (∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ Cm.toFlowFM gK k Ar C n) →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
    ∀ v : ℕ → ℝ, (∀ n, s n ≤ v n) → (∀ n, v n ≤ t n) →
    ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D₁ : ℝ, 0 < D₁ →
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
    ∀ (Φc : ℕ → ℝ) (K : ℕ → ℕ), (∀ n, K n ≠ 0) →
      (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
      (∀ᶠ n : ℕ in atTop, K n ≤ ⌈((sz.size n : ℕ) : ℝ) ^ C_K⌉₊) →
      ∀ᶠ n : ℕ in atTop, ∃ G : Set (PathΩ sz),
        Cm.Pp.real Gᶜ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) ∧
        ∀ ω ∈ G,
          (∀ j ≤ K n, Cm.Hpath s v K n j ω ∈
            {H | GoodSetNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n) (Φc n) τ' D' H} ∩
              GoodLinNg Cm n (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A → ∀ a : Fin k → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A → ∀ a : Fin k → Zd d (sz.L n),
            ‖zeroModeSet d (sz.L n) A (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) a‖ ≤
              ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k := by
  intro k hk C hC hKerN Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  classical
  have hd1 : 1 ≤ d := by omega
  have hv1 : ∀ n, v n < 1 := fun n => (hvt n).trans_lt (ht1 n)
  have him1 : ∀ n, (Cm.m n).im ≤ 1 := fun n => NQGood1Gen_im_le_one (hm n)
  have hk0 : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  -- the range exponent of the end time, the `Y`-moment constant (one for all signs, before the grid)
  have hτR : 0 < min τ 1 := lt_min hτ one_pos
  have hτR1 : min τ 1 ≤ 1 := min_le_right _ _
  have hrangeV : sz.RangeCond (min τ 1) v := nzEnd_rangeCond_mono sz (min_le_left _ _) hvt hrange
  obtain ⟨Cmax, hCmax0, hYmax⟩ := NQEndLinGen_yMomentsMax Cm hL hW' hRow hspec hs0 hsv hv1 hsize hrangeV k
  -- the numerical constants, in the fixed order `C → ε₀' → ε₁ → D'' → D' → τ' → C_P → C_K`
  obtain ⟨e0, he0def⟩ : ∃ e0 : ℝ, e0 = min ε₀ 1 := ⟨_, rfl⟩
  have he0 : 0 < e0 := by rw [he0def]; exact lt_min hε₀ one_pos
  have he0le : e0 ≤ ε₀ := by rw [he0def]; exact min_le_left _ _
  obtain ⟨D'', hD''def⟩ : ∃ D'' : ℝ, D'' = 2 * ((k : ℝ) + 2) / 𝔠 + 1 := ⟨_, rfl⟩
  have hD''0 : 0 ≤ D'' := by rw [hD''def]; positivity
  have hD''c : 𝔠 * D'' / 2 = (k : ℝ) + 2 + 𝔠 / 2 := by rw [hD''def]; field_simp
  obtain ⟨C_K, hCKdef⟩ : ∃ C_K : ℝ, C_K = D₁ + 2 * (Cmax + 2 * (k : ℝ) + 2) + D'' + 16 * k + 40 := ⟨_, rfl⟩
  have hCK0 : 0 ≤ C_K := by rw [hCKdef]; linarith
  refine ⟨e0 / 8, 1, D'' + 1, C_K, by linarith, one_pos, by linarith, hCK0, ?_⟩
  intro Φc K hK0 hKN hKU
  -- the exponent constraints on `C_K`
  have hθ1 : 1 - min τ 1 ≤ 1 := by linarith
  have hθk1 : (4 * (k : ℝ) + 8) * (1 - min τ 1) ≤ 4 * k + 8 := mul_le_of_le_one_right (by positivity) hθ1
  have hθk2 : 5 * (k : ℝ) * (1 - min τ 1) ≤ 5 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hθk3 : 2 * (k : ℝ) * (1 - min τ 1) ≤ 2 * k := mul_le_of_le_one_right (by positivity) hθ1
  have hC1 : (D₁ + 1) + 4 * ((k : ℝ) + 2) + (k : ℝ) + 2 * (Cmax + 2 * (k : ℝ) + 2) + 8 ≤ C_K := by rw [hCKdef]; linarith
  have hC2 : 8 + (4 * (k : ℝ) + 8) * (1 - min τ 1) + 2 * ((k : ℝ) + 2) < C_K := by rw [hCKdef]; linarith
  have hC3 : 3 + 4 * (1 : ℝ) + 5 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 2) < C_K := by rw [hCKdef]; linarith
  have hC4 : 2 * (1 - min τ 1) + 1 + 2 * (k : ℝ) * (1 - min τ 1) + ((k : ℝ) + 2) < C_K := by rw [hCKdef]; linarith
  have hC5 : 1 - min τ 1 < C_K := by rw [hCKdef]; linarith
  have hC6 : D'' + 2 * (k : ℝ) + 5 ≤ C_K := by rw [hCKdef]; linarith
  -- the eventual regime facts
  have hη := NQEndLinGen_ev_hη Cm hspec him1 hsize hτR hrangeV
  have hδ := NQEndLinGen_ev_hδ Cm hspec him1 hd1 hsize h𝔠 hband k hs0 hsv hv1 hK0 hη hD''0 hC6 hKN
  have hlogR := nqBudget_merged_inputsg Cm (κm := κm) (τ' := min τ 1) (τK := 1) (C_K := C_K) (D_t := (k : ℝ) + 2) (s := s) (v := v) (K := K) k
    hspec him1 hτR hτR1 one_pos (by linarith) hk hsize hs0 hsv hv1 hK0 hrangeV hC2 hC3 hC4 hC5 hKN
  -- the six absorption lemmas of `budgetNZNg`
  have H1 := nzEnd_ev_H1 sz hsize (C := C) (ε₁ := e0 / 8) (ε₀ := e0) (by linarith)
  have H2 := QtNZEndGen_ev_H2 Cm hspec him1 hsize k (C := C) (cA := (2 : ℝ) ^ k) (ε₁ := e0 / 8) (ε₀ := e0) hC.le (by positivity) (by linarith)
  have H3 := QtNZEndGen_ev_H3 Cm hspec him1 hsize k (C := C) (εq := e0 / 8) (ε₁ := e0 / 8) (ε₀ := e0) hC.le (by linarith)
  have H4 := nzEnd_ev_H4 sz hsize hband k (C := C) (D'' := D'') (εq := e0 / 8) (ε₀ := e0) hC.le hD''0 (by rw [hD''c]; linarith)
  have H5 : ∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-((k : ℝ) + 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ e0 / 6 := by
    filter_upwards [nzEnd_ev_H56 sz hsize k 1 (D := (k : ℝ) + 2) (ε₀ := e0) (by linarith)] with n h
    rw [one_mul] at h
    exact h
  have H6 := nzEnd_ev_H56 sz hsize k ((2 : ℝ) ^ k) (D := (k : ℝ) + 2) (ε₀ := e0) (by linarith)
  have hun := nzEnd_ev_union sz hsize ((4 : ℝ) ^ k) D₁
  -- the drift (D5): the per-index classes give `GridDriftNgAt` for this grid
  have hGD : ∀ᶠ n : ℕ in atTop, GridDriftNgAt Cm s v K n := by
    filter_upwards [hExp, hKL, hKT, hU] with n h1 h2 h3 h4
    exact gridDriftNgAt_of_classes hL hW' s v K n (h1 s v K) h2 h3 h4 (hS n) (fun w _ k σ a => hKK n w k σ a) (hs0 n) (hsv n) (hv1 n) (hK0 n)
  -- the assembly at the exit time `nqLinExitTauNg` (per pair `(σ, A)`, `D₁ + 1`)
  have hΓ0 : ∀ n, 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hAsm := QtNZEndGen_assembly Cm μ k hk hL hW' hspec hm hSeq hS hRow hKS hKK hKb hGD hsize hs0 hsv hv1 hK0 hcase hR1
    (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φc Φ₁ Φ₂ Φ₃ hΓ0 hΛ0 hΦ₁ hΦ₂ hΦ₃ (C := C) (τ' := 1) (D' := D'' + 1) (D'' := D'')
    (D_Y := (k : ℝ) + 2) (τK := 1) (εq := e0 / 8) (D₁ := D₁ + 1) (C_P := Cmax) (C_K := C_K) hC hKerN (by linarith) one_pos hCK0 hC1 hKN hKU
    (hYmax K hK0) hδ
  filter_upwards [hAsm, hlogR, H1, H2, H3, H4, H5, H6, hΛ1, hun, hKN] with n hAsmn hlogRn H1n H2n H3n H4n H5n H6n hΛ1n hunn hKNn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := nzEnd_one_le_size sz n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  by_cases hsvn : s n = v n
  · -- the collapsed window `v_n = s_n`: `G = univ`
    refine ⟨Set.univ, ?_, fun ω _ _ hinit' σ A hσA a => ?_⟩
    · have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
      rw [Set.compl_univ]
      simp only [measureReal_empty]
      exact Real.rpow_nonneg hN0.le _
    · exact QtNZEndGen_collapse hW' (hv1 n) hsvn (by linarith) hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) ω σ A a (hinit' σ A hσA a)
  · have hlt : s n < v n := lt_of_le_of_ne (hsv n) hsvn
    -- the events, one per pair `(σ, A)` with `I_diff(σ) ⊆ A`
    have hAsmP := fun p : {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} => hAsmn p.1.1 p.1.2 p.2 hlt
    choose Gs hGsP hGsb using hAsmP
    have : IsProbabilityMeasure Cm.Pp := by rw [hW'.2.1]; exact isProbabilityMeasure_pathP _
    refine ⟨⋂ p, Gs p, ?_, ?_⟩
    · -- the union bound over the `≤ 4^k` pairs
      have hcompl : (⋂ p, Gs p)ᶜ = ⋃ p, (Gs p)ᶜ := by rw [Set.compl_iInter]
      have hcard : (Fintype.card {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} : ℝ) ≤ (4 : ℝ) ^ k := by
        have h1 := Fintype.card_subtype_le (fun p : (Fin k → Bool) × Finset (Fin k) => STIdiff p.1 ⊆ p.2)
        have h2 : Fintype.card ((Fin k → Bool) × Finset (Fin k)) = 2 ^ k * 2 ^ k := by
          simp [Fintype.card_prod, Fintype.card_finset]
        rw [h2] at h1
        have h3 : (4 : ℝ) ^ k = ((2 ^ k * 2 ^ k : ℕ) : ℝ) := by
          push_cast; rw [← mul_pow]; norm_num
        rw [h3]
        exact_mod_cast h1
      rw [hcompl]
      calc Cm.Pp.real (⋃ p, (Gs p)ᶜ) ≤ ∑ p, Cm.Pp.real (Gs p)ᶜ := measureReal_iUnion_fintype_le _
        _ ≤ ∑ _p : {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2}, ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) :=
            Finset.sum_le_sum fun p _ => hGsP p
        _ = (Fintype.card {p : (Fin k → Bool) × Finset (Fin k) // STIdiff p.1 ⊆ p.2} : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := by simp
        _ ≤ (4 : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-(D₁ + 1)) := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
        _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D₁) := hunn
    · intro ω hω hgood hinit' σ A hσA a
      have hωp : ω ∈ Gs ⟨(σ, A), hσA⟩ := Set.mem_iInter.1 hω ⟨(σ, A), hσA⟩
      have hb := hGsb ⟨(σ, A), hσA⟩ ω hωp hgood a
      have hX0 : (Finset.univ.sup' Finset.univ_nonempty fun b => ‖zeroModeSet d (sz.L n) A (AvecNg Cm s v K n 0 σ ω) b‖) ≤
          ((sz.size n : ℕ) : ℝ) ^ (e0 / 8) * (sz.Bctl n (s n)) ^ k := by
        refine Finset.sup'_le _ _ fun b _ => ?_
        have h := hinit' σ A hσA b
        have e : AvecNg Cm s v K n 0 σ ω = (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (s n) (Cm.Hpath s v K n 0 ω) σ b) := by
          funext b
          simp only [AvecNg, ST_gridTime_zero]
        rw [e]
        exact h
      have hbud := budgetNZNg Cm hL s v K n k C ((2 : ℝ) ^ k) (fun n => ((sz.size n : ℕ) : ℝ) ^ (e0 / 8)) Λ Φ₁ Φ₂ Φ₃ D'' ((k : ℝ) + 2) ((k : ℝ) + 2) 1
        (e0 / 8) e0 (e0 / 8) (Finset.univ.sup' Finset.univ_nonempty fun b => ‖zeroModeSet d (sz.L n) A (AvecNg Cm s v K n 0 σ ω) b‖) hk hC
        (by positivity) (by linarith) (hs0 n) (hsv n) (hv1 n) (hK0 n) rfl hΛ1n (hΦ₁ n) (hΦ₂ n) (hΦ₃ n) hlogRn.1 hX0 hlogRn.2 H1n H2n H3n H4n H5n H6n
      have hlk : AvecNg Cm s v K n (K n) σ ω = (fun b : Fin k → Zd d (sz.L n) => STLKMg Cm n (v n) (Cm.Hpath s v K n (K n) ω) σ b) := by
        funext b
        simp only [AvecNg, gridTime_last s v K n (hK0 n)]
      rw [← hlk]
      refine hb.trans (hbud.trans ?_)
      have hB : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg (Sizes.STBctl_pos sz n (hv1 n)).le _
      have hS' : 0 ≤ Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n := by
        have := Real.rpow_nonneg (hΛ0 n) ((1 : ℝ) / 2)
        have := hΦ₁ n
        have := hΦ₂ n
        have := hΦ₃ n
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 he0le) hS') hB

end Endpoint

/-! ## 3b. The band re-derivation of `nzGridEndN` -/

section BandReDerivation

/-- **Band re-derivation of `nzGridEndN`** (`QtNonzeroEnd:979`, the same statement): the merged band theorem from `nzGridEndNg` at the carrier `bandStep2Mat sz E` with the law
`seqP sz`: `Ar = 1`, `gK = lam' = sz.lam`, `κm = √κ/2`, `C = qtNZGen_bandC d k 𝔡⁻¹ (min κ (4/5))`; `LoopForm`, `WalkForm`, the spectral data, the row sums, the kernel class,
`ZeroModeGen_KerSums` and the four drift classes are the band lemmas; `STKbound` is `stKbound_holds`; D1 is `qtNZGen_kerNZ_band_at`; R1 is `lam² ≤ 1 · lam²`. -/
theorem nzGridEndN_of_gen :
  ∀ {d : ℕ} (sz : Sizes d) (κ 𝔠 τ 𝔡 : ℝ) (E s t : ℕ → ℝ),
    3 ≤ d → 0 < κ → 0 < 𝔠 → 0 < τ → 0 < 𝔡 →
    sz.SizeTendsto → sz.Bandwidth 𝔠 → sz.WO 𝔡 →
    (∀ n, |E n| ≤ 2 - κ) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    sz.STCaseII s t → sz.RangeCond τ t →
    ∀ k : ℕ, 2 ≤ k →
    ∀ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ, (∀ n, 0 ≤ Λ n) → (∀ᶠ n : ℕ in atTop, 1 ≤ Λ n) →
      (∀ n, 0 ≤ Φ₁ n) → (∀ n, 0 ≤ Φ₂ n) → (∀ n, 0 ≤ Φ₃ n) →
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
            sz.GoodSetN n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁) (Λ n)
                (Φc n) τ' D' ∩
              GoodLinN sz n (E n) (gridTime s v K n j) k (((sz.size n : ℕ) : ℝ) ^ ε₁)
                (Φ₁ n) (Φ₂ n) (Φ₃ n)) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (s n) (pathH sz s v K n 0 ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A →
            ∀ a : Fin k → Zd d (sz.L n),
              ‖zeroModeSet d (sz.L n) A
                  (fun b : Fin k → Zd d (sz.L n) =>
                    sz.STLKM n (E n) (v n) (pathH sz s v K n (K n) ω) σ b) a‖ ≤
                ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
                  (sz.Bctl n (v n)) ^ k := by
  intro d sz κ 𝔠 τ 𝔡 E s t hd hκ h𝔠 hτ h𝔡 hsize hband hWO hE hs0 hst ht1 hcase hrange k hk Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  have hE2 : ∀ n, |E n| < 2 := fun n => by have := hE n; linarith [abs_nonneg (E n)]
  obtain ⟨κ', hκ'def⟩ : ∃ κ' : ℝ, κ' = min κ (4 / 5) := ⟨_, rfl⟩
  obtain ⟨Λg, hΛgdef⟩ : ∃ Λg : ℝ, Λg = 𝔡⁻¹ := ⟨_, rfl⟩
  have hκ' : 0 < κ' := by rw [hκ'def]; exact lt_min hκ (by norm_num)
  have hκm : ∀ n, κ' ≤ (mE (E n)).im := fun n => by
    rw [hκ'def]; exact RBM.Ind.nqGood1_mE_im_ge hκ (hE n)
  have hΛg : 0 < Λg := by rw [hΛgdef]; exact inv_pos.2 h𝔡
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz.lam n ∧ sz.lam n ≤ Λg := by
    rw [hΛgdef]
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  have hKb : sz.STKbound E := stKbound_holds sz hd hκ hΛg hsize (Eventually.of_forall hE) hlam
  have hKerN : ∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ (bandStep2Mat sz E).toFlowFM sz.lam k 1 (qtNZGen_bandC d k Λg κ') n := by
    filter_upwards [hlam] with n hn
    exact qtNZGen_kerNZ_band_at hd hk hΛg hκ' sz E n hn.1 hn.2 (hE2 n) (hκm n)
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nzGridEndNg (bandStep2Mat sz E) (Sizes.seqP sz) (E := E) (lam' := sz.lam) (Ψ := fun _ => 0)
    (gK := sz.lam) (Ar := 1) (κm := Real.sqrt κ / 2) s t hd h𝔠 hτ (stepDecompGen_loopForm_band sz E hE2) (stepDecompGen_walkForm_band sz E)
    (DecayGen_bandSpec sz hκ hE) (fun n => (norm_mE (hE2 n).le).le) (fun n => rfl) (fun n a => hierDriftGen_SB_row sz n a)
    (fun n => gridRepTailGen_ker_band sz E n (hE2 n).le) (fun n => zeroModeGen_kerSums_band sz E n) (fun n w k σ a => rfl) hKb
    (Eventually.of_forall fun n s' t' K' => hierDriftGen_expand_band sz E hE2 s' t' K' n)
    (Eventually.of_forall (hierDriftGen_kLoop_band sz E hE2)) (Eventually.of_forall (hierDriftGen_kTwo_band sz E hE2))
    (Eventually.of_forall (hierDriftGen_uStep_band sz E hE2)) hsize hband hs0 hst ht1 hcase hrange (fun n => (one_mul _).ge) k hk
    (qtNZGen_bandC d k Λg κ') (qtNZGen_bandC_pos hd hk hΛg hκ') hKerN Λ Φ₁ Φ₂ Φ₃ hΛ0 hΛ1 hΦ₁ hΦ₂ hΦ₃ v hsv hvt ε₀ hε₀ D₁ hD₁
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, fun Φc K hK0 hKN hKU => ?_⟩
  filter_upwards [hend Φc K hK0 hKN hKU] with n ⟨G, hG, hGb⟩
  refine ⟨G, hG, fun ω hω hgood hinit => ?_⟩
  exact hGb ω hω (fun j hj => ⟨(bandStep2_GoodSetN sz E n _ k _ _ _ τ' D' _).1 (hgood j hj).1, (hgood j hj).2⟩) hinit

end BandReDerivation

/-! ## 4. Compiled nonempty instance of `nzGridEndNg` (`d = 3`, band carrier `bandStep2Mat szB Einst`)

Data of the band instances `QtNonzeroEndInst` (public facts by name): `szB` (`L = 4`, `W = n + 4`, `lam ≡ 1`, `N = (4(n+4))^3`; `szB_tendsto`, `szB_bandwidth` `𝔠 = 1/6`), the
case-(ii) window `s ≡ 15/16`, `t ≡ 31/32` (`szB_caseII`: `1 - s = 1/16 = lam²/L²`), `v ≡ 31/32` (non-collapsed, `s < v`, `Δ > 0`), `E = Einst ≡ 1/2`
(`Im m = √15/4`), `κm = √1/2`, `τ = 1/2` (`rangeCond_tB`), `k ≥ 2` arbitrary, levels `Λ = Φ₁ = Φ₂ = Φ₃ = Φc ≡ 1`, `ε₀ = 1/10`, `D₁ = 1`; the grid is `KB C_K n`
(`N^{C_K} ≤ K_n ≤ ⌈N^{C_K}⌉`); R1 with `Ar = 1`, `gK = lam`.  The kernel constant is `C = qtNZGen_bandC 3 k 10 κz` (abstract, `> 0`), D1 at every index is
`qtNZGen_kerNZ_band_at` (`Λg = 10 ≥ lam = 1`, `κz = min 1 (4/5) ≤ Im m`).  Every hypothesis is discharged (`STKboundgL` by `stKbound_holds`; the drift classes, the kernel
class, `LoopForm`, `WalkForm`, `ZeroModeGen_KerSums`, the spectral data by the band lemmas); the conclusion is unfolded at one size index (`Filter.Eventually.exists`). -/

section Instances

open RBM.Ind.QtNonzeroEndInst renaming vB → vBz
open RBM.Ind.QtNonzeroEndInst (sB tB oneL κz hE_B hκm_B hlam_B sB_nonneg sB_le_tB tB_lt_one sB_le_vB vB_le_tB rangeCond_tB KB KB_ne_zero KB_low KB_up
  window_nondegenerate)
open RBM.Gauss.Step34Inst RBM.Gauss.InductionDefsInst RBM.Gauss.SizesInst RBM.Ind.AzumaProxyNInst

/-- **`nzGridEndNg` at the data**: for every `k ≥ 2` the exponents the theorem produces, at one size index of the grid `KB C_K` on the non-collapsed window, an event `G` with
`P(Gᶜ) ≤ N^{-1}` and the terminal bound for every `σ` and every `A ⊇ I_diff(σ)`. -/
theorem qtNZEndGen_instance (k : ℕ) (hk : 2 ≤ k) :
    ∃ ε₁ τ' D' C_K : ℝ, 0 < ε₁ ∧ 0 < τ' ∧ 0 < D' ∧ 0 ≤ C_K ∧
      ∃ n : ℕ, sB n < vBz n ∧ 0 < gridStep sB vBz (KB C_K) n ∧ ∃ G : Set (PathΩ szB),
        (bandStep2Mat szB Einst).Pp.real Gᶜ ≤ ((szB.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
        ∀ ω ∈ G,
          ((∀ j ≤ KB C_K n, (bandStep2Mat szB Einst).Hpath sB vBz (KB C_K) n j ω ∈
            {H | GoodSetNg (bandStep2Mat szB Einst) n (gridTime sB vBz (KB C_K) n j) k (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 τ' D' H} ∩
              GoodLinNg (bandStep2Mat szB Einst) n (gridTime sB vBz (KB C_K) n j) k (((szB.size n : ℕ) : ℝ) ^ ε₁) 1 1 1) →
          (∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A → ∀ a : Fin k → Zd 3 (szB.L n),
            ‖zeroModeSet 3 (szB.L n) A (fun b : Fin k → Zd 3 (szB.L n) =>
                STLKMg (bandStep2Mat szB Einst) n (sB n) ((bandStep2Mat szB Einst).Hpath sB vBz (KB C_K) n 0 ω) σ b) a‖ ≤
              ((szB.size n : ℕ) : ℝ) ^ ε₁ * (szB.Bctl n (sB n)) ^ k) →
          ∀ (σ : Fin k → Bool) (A : Finset (Fin k)), STIdiff σ ⊆ A → ∀ a : Fin k → Zd 3 (szB.L n),
            ‖zeroModeSet 3 (szB.L n) A (fun b : Fin k → Zd 3 (szB.L n) =>
                STLKMg (bandStep2Mat szB Einst) n (vBz n) ((bandStep2Mat szB Einst).Hpath sB vBz (KB C_K) n (KB C_K n) ω) σ b) a‖ ≤
              ((szB.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * ((1 : ℝ) ^ ((1 : ℝ) / 2) + 1 + 1 + 1) * (szB.Bctl n (vBz n)) ^ k) := by
  have hκz := RBM.Ind.QtNonzeroEndInst.κz_pos
  have hKb : szB.STKbound Einst := stKbound_holds szB (by norm_num) one_pos (by norm_num : (0 : ℝ) < 10) szB_tendsto (Eventually.of_forall hE_B) hlam_B
  have hKerN : ∀ᶠ n : ℕ in atTop, QtNZGen_KerNZ (bandStep2Mat szB Einst).toFlowFM szB.lam k 1 (qtNZGen_bandC 3 k 10 κz) n := by
    filter_upwards [hlam_B] with n hn
    exact qtNZGen_kerNZ_band_at le_rfl hk (by norm_num) hκz szB Einst n hn.1 hn.2 (Einst_abs_lt n) (hκm_B n)
  obtain ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, hend⟩ := nzGridEndNg (bandStep2Mat szB Einst) (Sizes.seqP szB) (E := Einst) (lam' := szB.lam) (Ψ := fun _ => 0)
    (gK := szB.lam) (Ar := 1) (κm := Real.sqrt 1 / 2) (𝔠 := 1 / 6) (τ := 1 / 2) sB tB le_rfl (by norm_num) (by norm_num)
    (stepDecompGen_loopForm_band szB Einst Einst_abs_lt) (stepDecompGen_walkForm_band szB Einst) (DecayGen_bandSpec szB one_pos hE_B)
    (fun n => (norm_mE (Einst_abs_lt n).le).le) (fun n => rfl) (fun n a => hierDriftGen_SB_row szB n a)
    (fun n => gridRepTailGen_ker_band szB Einst n (Einst_abs_lt n).le) (fun n => zeroModeGen_kerSums_band szB Einst n) (fun n w k σ a => rfl) hKb
    (Eventually.of_forall fun n s' t' K' => hierDriftGen_expand_band szB Einst Einst_abs_lt s' t' K' n)
    (Eventually.of_forall (hierDriftGen_kLoop_band szB Einst Einst_abs_lt)) (Eventually.of_forall (hierDriftGen_kTwo_band szB Einst Einst_abs_lt))
    (Eventually.of_forall (hierDriftGen_uStep_band szB Einst Einst_abs_lt)) szB_tendsto szB_bandwidth sB_nonneg sB_le_tB tB_lt_one szB_caseII rangeCond_tB
    (fun n => (one_mul _).ge) k hk (qtNZGen_bandC 3 k 10 κz) (qtNZGen_bandC_pos le_rfl hk (by norm_num) hκz) hKerN oneL oneL oneL oneL
    (fun _ => by norm_num) (Eventually.of_forall fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) vBz sB_le_vB vB_le_tB
    (1 / 10) (by norm_num) 1 one_pos
  refine ⟨ε₁, τ', D', C_K, h1, h2, h3, h4, ?_⟩
  obtain ⟨n, G, hG, hGb⟩ := (hend oneL (KB C_K) (KB_ne_zero C_K) (Eventually.of_forall (KB_low C_K)) (Eventually.of_forall (KB_up C_K))).exists
  exact ⟨n, (window_nondegenerate C_K n).1, (window_nondegenerate C_K n).2, G, hG, hGb⟩

/-- The instance at `k = 2` (no `l ∈ [3,k]`; `A ⊆ Fin 2`). -/
example := qtNZEndGen_instance 2 le_rfl

/-- The instance at `k = 3`. -/
example := qtNZEndGen_instance 3 (by norm_num)

/-- The instance at `k = 4`. -/
example := qtNZEndGen_instance 4 (by norm_num)

end Instances

end RBM.BA

end
