/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QGridGen
import RBM3D.Induction.QGridB
import RBM3D.Chain.GridEnvelopeGen

/-!
# The summed envelope of the `𝒬`-grid remainders over the flow carrier (BA-U row U1s2a, file 2, ticket T2497)

Target 8: `sum_weighted_qErrQNg_le`, the generic form of `Induction/QGridB.lean` `sum_weighted_qErrQN_le` (`QGridB:565`, not edited)
over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.  The four rows are those of the merged
`SumWeightedStepErrNg_Stmt` (`GridEnvelopeGen:235`) at `(k, D_t) = (m + 1, D_t + (m + 1))`; the premises are `DecayGen_Spec`
and the inline `∀ n, (Cm.m n).im ≤ 1` in place of `|E n| ≤ 2 - κ`.

Proof: the band theorem at the energy `E'_n = 2 √(1 - (Im m_n)²)` (`κ = κ_m²`), for which `Im m(E'_n) = Im m_n` and
`|E'_n| ≤ 2 - κ_m²` (`GridEnvelopeGen_mE_im_Ep`, `GridEnvelopeGen_abs_Ep_le`); `qErrQNg` reads the carrier only through `Cm.eta`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter

noncomputable section

namespace RBM.BA

open Matrix RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ## 1. Target 8 -/

section Weighted

variable {d : ℕ} {sz : Sizes d}

/-- `qErrQNg` reads the carrier only through `C.eta n` (as `GridEnvelopeGen_stepErrNg_eta`). -/
private theorem QGridGen2_qErrQNg_eta {C C' : FlowFM sz} (h : ∀ n u, C.eta n u = C'.eta n u)
    (s t : ℕ → ℝ) (K : ℕ → ℕ) (n m : ℕ) (c c₂ Bk : ℝ) (j : ℕ) :
    qErrQNg C s t K n m c c₂ Bk j = qErrQNg C' s t K n m c c₂ Bk j := by
  unfold qErrQNg lkEnvNg driftEnvNg
  rw [GridEnvelopeGen_stepErrNg_eta n (m + 1) _ _ _ _ (fun u => h n u)]
  simp only [h]

/-- **Target 8, `sum_weighted_qErrQNg_le`** (band `sum_weighted_qErrQN_le`, `QGridB:565`; statement `T2497_SumWeightedQErrQNg`): on the
grid `u_j = gridTime s t K n j` with `K n ≥ N^{C_K}`, the one-step remainders `qErrQNg` at the envelope
`B_{m+1} = N^{τ_K} η_{u_{j+1}}^{-(m+1)}`, weighted by the coarse row bound `(1 + (1 - u_p)⁻¹)^{m+1}` of the kernel, sum over `j < p` to
at most `N^{-D_t}` for every `p ≤ K n`, eventually, for any constants `0 ≤ C, C₂`. -/
theorem sum_weighted_qErrQNg_le :
    ∀ (d : ℕ) (sz : Sizes d) (Cm : Step2Mat sz) {κm τ' τK C_K D_t C C₂ : ℝ} {s t : ℕ → ℝ} {K : ℕ → ℕ} (m : ℕ),
    0 ≤ C → 0 ≤ C₂ → DecayGen_Spec Cm.toFlowFM κm → (∀ n, (Cm.m n).im ≤ 1) → 0 < τ' → τ' ≤ 1 → 0 < τK →
    0 ≤ D_t → 1 ≤ m → sz.SizeTendsto → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    sz.RangeCond τ' t →
    8 + (4 * ((m : ℝ) + 1) + 8) * (1 - τ') + 2 * (D_t + ((m : ℝ) + 1)) < C_K →
    3 + 4 * τK + 5 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K →
    2 * (1 - τ') + τK + 2 * ((m : ℝ) + 1) * (1 - τ') + (D_t + ((m : ℝ) + 1)) < C_K → 1 - τ' < C_K →
    (∀ᶠ n : ℕ in atTop, ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) →
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ K n,
      ∑ j ∈ Finset.range p, (1 + (1 - gridTime s t K n p)⁻¹) ^ (m + 1) *
          qErrQNg Cm.toFlowFM s t K n m C C₂
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s t K n (j + 1)))⁻¹ ^ (m + 1)) j ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) := by
  intro d sz Cm κm τ' τK C_K D_t C C₂ s t K m hC hC₂ hspec him1 hτ' hτ'1 hτK hDt hm hsize hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  set E' : ℕ → ℝ := fun n => 2 * Real.sqrt (1 - ((Cm.m n).im) ^ 2) with hE'
  have hκm : 0 < κm := hspec.1
  have hE'2 : ∀ n, |E' n| ≤ 2 - κm ^ 2 := fun n =>
    GridEnvelopeGen_abs_Ep_le hκm (hspec.2.1 n) (him1 n)
  have hmE : ∀ n, (mE (E' n)).im = (Cm.m n).im := fun n =>
    GridEnvelopeGen_mE_im_Ep (hκm.le.trans (hspec.2.1 n)) (him1 n)
  have hetaE : ∀ n u, etaT (E' n) u = Cm.eta n u := fun n u => by
    rw [hspec.2.2 n u]; unfold etaT; rw [hmE n]
  have hq : ∀ n B j, RBM.Ind.qErrQN sz E' s t K n m C C₂ B j = qErrQNg Cm.toFlowFM s t K n m C C₂ B j :=
    fun n B j => (QGridGen_bandFM_qErrQN sz E' s t K n j m C C₂ B).trans
      (QGridGen2_qErrQNg_eta (fun n u => hetaE n u) s t K n m C C₂ B j)
  have hband := RBM.Ind.sum_weighted_qErrQN_le d sz (κ := κm ^ 2) (E := E') m hC hC₂ (by positivity) hτ' hτ'1 hτK hDt hm
    hsize hE'2 hs0 hst ht1 hK0 hrange h1 h2 h3 h4 hKN
  refine hband.mono fun n hn p hp => ?_
  have := hn p hp
  simp only [hq, hetaE] at this
  exact this

end Weighted

/-! ## 2. Compiled nonempty instance (target 9)

Data of `QGridBCheck` re-declared under the stem: `d = 3`, the merged `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `N_0 = 2097152`), the band
carrier `bandStep2Mat sz0 E0` with `E0 ≡ 0` (`Im m = 1`, `κ_m = 1/2` by `DecayGen_bandSpec` at `κ = 1`), `s ≡ 0`, `t ≡ 1/2`, `K n = N_n^{31}`,
`m = 3` (tensors of `4` indices), `τ' = τ_K = 1/2`, `D_t = 1`, `C_K = 31`, and the constants of `gridDriftQNg` at `d = 3`, `m = 3`:
`C = (1 + 40·9) 6^9`, `C₂ = 1000 (1 + 9)²`.  The four rows read `30 < 31`, `20 < 31`, `10.5 < 31`, `0.5 < 31`.  Every hypothesis is
discharged; nothing is left as a hypothesis. -/

namespace QGridGen2Check

open RBM.Gauss.SizesInst RBM.Ind.GridEnvelopeNCheck

private abbrev Cm0 : Step2Mat sz0 := bandStep2Mat sz0 (fun _ => 0)

private theorem hspec0 : DecayGen_Spec Cm0.toFlowFM (Real.sqrt 1 / 2) :=
  DecayGen_bandSpec sz0 (κ := 1) (by norm_num) (fun n => by norm_num)

private theorem him1 (n : ℕ) : (Cm0.m n).im ≤ 1 := by
  change (mE 0).im ≤ 1
  rw [mE_im]
  have h4 : Real.sqrt (4 - (0 : ℝ) ^ 2) = 2 := by
    rw [show (4 - (0 : ℝ) ^ 2) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h4]
  norm_num

/-- `K n = N_n^{31}`: the grid with `K n ≥ N^{C_K}`, `C_K = 31`. -/
def QGridGen2_Kc31 (n : ℕ) : ℕ := sz0.size n ^ 31

private theorem Kc31_ne_zero (n : ℕ) : QGridGen2_Kc31 n ≠ 0 := by
  unfold QGridGen2_Kc31
  have : 0 < sz0.size n := by
    have := four_le_size n
    exact_mod_cast (by linarith : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ))
  positivity

private theorem rpow_31_le_Kc31 (n : ℕ) : ((sz0.size n : ℕ) : ℝ) ^ (31 : ℝ) ≤ (QGridGen2_Kc31 n : ℝ) := by
  unfold QGridGen2_Kc31
  rw [show (31 : ℝ) = ((31 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  push_cast
  exact le_rfl

/-- **Instance of `sum_weighted_qErrQNg_le`** (target 8) at `sz0` (`d = 3`), `m = 3`, `τ' = τ_K = 1/2`, `C_K = 31`, `D_t = 1`,
`K n = N_n^{31}`, `C = (1 + 40·9) 6^9`, `C₂ = 1000 (1 + 9)²`, `κ_m = 1/2`: every hypothesis is discharged
(`SizeTendsto sz0`, `RangeCond`, `DecayGen_Spec`, `Im m ≤ 1`, the grid, the four numerical rows). -/
theorem QGridGen2_sum_weighted_qErrQNg_instance :
    ∀ᶠ n : ℕ in atTop, ∀ p ≤ QGridGen2_Kc31 n,
      ∑ j ∈ Finset.range p,
          (1 + (1 - gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n p)⁻¹) ^ (3 + 1) *
          qErrQNg Cm0.toFlowFM (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n 3
            ((1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (Cm0.eta n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) QGridGen2_Kc31 n
                (j + 1)))⁻¹ ^ (3 + 1)) j ≤
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  sum_weighted_qErrQNg_le 3 sz0 Cm0 (κm := Real.sqrt 1 / 2) (τ' := 1 / 2) (τK := 1 / 2) (C_K := 31) (D_t := 1)
    (C := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)) (C₂ := 1000 * (1 + ((3 * 3 : ℕ) : ℝ)) ^ 2)
    (s := fun _ => 0) (t := fun _ => 1 / 2) (K := QGridGen2_Kc31) 3 (by positivity) (by positivity) hspec0 him1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto (fun _ => le_rfl)
    (fun _ => by norm_num) (fun _ => by norm_num) Kc31_ne_zero rangeCond_half (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (Eventually.of_forall rpow_31_le_Kc31)

end QGridGen2Check

end RBM.BA

end
