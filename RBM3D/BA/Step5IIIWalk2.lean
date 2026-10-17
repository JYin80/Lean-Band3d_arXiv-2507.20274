/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5IIIWalk
import RBM3D.BA.NetLiftBA
import RBM3D.Induction.Step1Setup

/-!
# U5d-2: the stopped grid walk, the closure and the lift of BA case (iii) of Step 5

Ticket T2493, second half of the pre-signed split (branch `t/T2493b`, stacked on
`BA/Step5IIIWalk.lean`, merged as f2af0245).  Paper: `lem:pf_step5` (`3_5:2376-2383`; stopping time
`(eq:def_TTT)` `:2369-2372`; Duhamel form `(int_K-L_ST)` `:136`; `TailtoTail` `:2345-2367`;
`lem_dec_calE` `:2317-2338`); BA `7_8:2101` ("we therefore omit the details", paper-delta candidate
T2459a).  Band twins (not edited): `Induction/PfStep5.lean` (`pfStep5_path`, `pfStep5_fixedN`,
`pfStep5_walk`, `pfStep5_PT_of_walk`, `pfStep5_lift`).  The check is
`docs/tickets/checks/T2493-check.lean`.

**Targets 6-8** (the `T2493_*` pins of the check):

* 6. `BAStep5IIIWalkConcl` (= `T2493_BAWalkConcl`); `baStep5III_walk_at` (= `T2493_WalkAt`, with
  `T2493_ReadPremises` written inline as one conjunction binder); `BAStep5IIIWalk`
  (= `T2493_BAWalk`) with `baStep5IIIWalk_holds` (`𝔠d = 1/100`, as the band).  The closure is the
  proof of `baStep5III_walk_at`; there is no public closure text.
* 7. `BAStep5IIIFromWalk` (= `T2493_BAFromWalk`, correction (a): `0 < ε`, `0 < 𝔡`) with
  `baStep5IIIFromWalk_holds`.
* 8. Compiled nonempty instances at `d = 3` (section 7).

Helpers carry the stem `Step5IIIWalk2_`.  The private lemmas of the band files and of `NetLiftBA`
are reached by `open private` (the dispatcher's copy-or-open rule, §153 (1)); every lemma of
`BA/Step5IIIWalk.lean` used here is public.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private pfStep5_fl pfStep5_Rm pfStep5_hKD pfStep5_hlabel pfStep5_gridStep_le pfStep5_W2_le pfStep5_tailTD_nonneg
  pfStep5_sizes pfStep5_Wev pfStep5_Lab from RBM3D.Induction.PfStep5
open private GridMartBA_Hpath_herm from RBM3D.BA.GridMartBA
open private NetLiftBA_decay_close from RBM3D.BA.NetLiftBA
open private nl2_evR from RBM3D.Path.NetLift2

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

variable {d : ℕ}

/-! ## 1. Vocabulary: the grid conclusion, the walk pin and the lift pin -/

/-- **The grid conclusion** (b1-b3; target 6 (a), `T2493_BAWalkConcl`; the probe's `T2459_BAWalkConcl` with `J♯` the merged `BAStep5IIIJsharp`; band
`PfStep5_walkConcl`, `Induction/PfStep5.lean:79`): there is `ε₁ > 0` such that for every `ε₀ ∈ (0, ε₁)` and every `D > 0` there is a level
`D* ≥ D + 2d` such that for every section `tt n ∈ [s_n, t_n]` and every probability exponent `D'` some grid `K` from `s` to `tt` has, eventually,
`J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for all `k ≤ K` outside an event of probability `≤ N^{-D'}`. -/
def BAStep5IIIWalkConcl {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (s t : ℕ → ℝ) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ D : ℝ, 0 < D → ∃ Dst : ℝ, D + 2 * (d : ℝ) ≤ Dst ∧
    ∀ tt : ∀ n, TimeIcc s t n, ∀ D' : ℝ, 0 < D' → ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n in atTop,
      (baStep2Mat sz lam0 E).Pp {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz lam0 E n
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => (tt m : ℝ)) K n k)) (gridTime s (fun m => (tt m : ℝ)) K n k)
          ((baStep2Mat sz lam0 E).Hpath s (fun m => (tt m : ℝ)) K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- **The walk pin** (target 6 (c), `T2493_BAWalk`; the probe's `T2459_BAWalk`): the shape of `STPfStep5gL` (`Chain/Step5Gen.lean:191`) with the grid
conclusion.  An input of U5e. -/
def BAStep5IIIWalk (d : ℕ) : Prop :=
  STIngR5gL d STReg5III (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
    (fun sz z s t => BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t)

/-- **The lift pin** (target 7, `T2493_BAFromWalk`; the probe's `T2459_BAfromWalk` with correction (a): `0 < ε`, `0 < 𝔡` added for the `η`-window and the
`𝒦` window of the net lift): the grid conclusion gives `STPfConclgL`.  An input of U5e. -/
def BAStep5IIIFromWalk (d : ℕ) : Prop :=
  3 ≤ d → ∀ (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), 0 < κ → 0 < ε → 0 < 𝔡 → BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
      BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t → STPfConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-! ## 2. The pathwise induction (band `pfStep5_path`, `Induction/PfStep5.lean:1525`) -/

section Path

/-- The numerical facts at one size index `n` used by the pathwise induction (all eventual facts of the choice of constants, collected; band
`PfStep5Num`, `Induction/PfStep5.lean:1477`). -/
private structure Step5IIIWalk2_Num (sz : Sizes d) (n : ℕ) (s tt : ℕ → ℝ) (K : ℕ → ℕ)
    (ε₀ τ ε' Dst Dg C₀ Ctot : ℝ) : Prop where
  hs0 : 0 ≤ s n
  hstt : s n ≤ tt n
  htt1 : tt n < 1
  hK : K n ≠ 0
  hreg : sz.lam n ^ 2 ≤ 1 - tt n
  hW : 1 < ((sz.W n : ℕ) : ℝ)
  hlam : 0 < sz.lam n
  hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d
  hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ)
  hN3 : 3 ≤ ((sz.size n : ℕ) : ℝ)
  hτ : 0 < τ
  hε₀ : 0 < ε₀
  hε'τ : ((sz.size n : ℕ) : ℝ) ^ ε' ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ τ)
  hclos : ((sz.size n : ℕ) : ℝ) ^ τ * (Ctot * (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
        (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) < ((sz.W n : ℕ) : ℝ) ^ ε₀
  hNDg : ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))
  hRm : 64 * (((sz.W n : ℕ) : ℝ) ^ d) ^ 7 * (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n) +
        gridStep s tt K n * ((sz.size n : ℕ) : ℝ) ^ 3) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dst)

/-- **The pathwise induction** (`(b3)`; band `pfStep5_path`, `Induction/PfStep5.lean:1525`): at one size index `n` and one sample `ω` of the grid walk,
if the matrix part holds at the grid indices (`hG`), the initial bound (`hI`), the decomposition of clause 1, the remainder bound of clause 2 and the
weighted martingale bound of clause 4 hold, then `J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for every `k ≤ K`: strong induction on `k`; the step is the per-time
layer (`hpt`: target 4 and `baStep5IIIEdet_holds`), the Duhamel form (`Step5IIIWalk_duhamel` inside `Step5IIIWalk_assemble`), the four terms,
`Step5IIIWalk_mart_real` and the closure `hclos`. -/
private theorem Step5IIIWalk2_path {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {s t tt : ℕ → ℝ} {K : ℕ → ℕ}
    {ε₀ τ ε' Dst Dg C₀ τ' θ Cd Cc Cq : ℝ} (hCc : 0 < Cc) (hCq : 0 < Cq)
    (hnum : Step5IIIWalk2_Num sz n s tt K ε₀ τ ε' Dst Dg C₀ (Step5IIIWalk_Ctot d Cc Cq))
    (htn : tt n ≤ t n) (ht0 : 0 ≤ t n)
    (hker : GridRepTailGen_Ker (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n)
    (hTT : ∀ D s' t' : ℝ, 0 ≤ s' → s' ≤ t' → t' < 1 → sz.lam n ^ 2 ≤ 1 - t' → STTailtoTailConclgL (baFMz sz z) n Cc D s' t')
    (hpt : ∀ (u : TimeIcc s t n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H →
      BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H <
        ((sz.W n : ℕ) : ℝ) ^ ε₀ →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STelklkMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b) +
            STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - (u : ℝ))⁻¹) ^ 2 + (1 - (u : ℝ))⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b) ∧
      (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ b b'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (u : ℝ))⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b ^ 2))
    (happ : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hxx : ∀ (v w p : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
      (a : Fin 2 → Zd d (sz.L n)), 0 ≤ v → v ≤ w → w ≤ t n → sz.lam n ^ 2 ≤ 1 - w → 0 ≤ p → H.IsHermitian →
      (∀ b b' : Fin 2 → Zd d (sz.L n),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v H σ b b'‖ ≤
          p * STtailTD sz n v (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst v) b ^ 2) →
      ‖STeeUMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v w H σ a‖ ≤
        (2 * Cq * p + 1) * STtailTD sz n w (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst w) a ^ 2)
    (Rem Mart : ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (hG : ∀ j, j ≤ K n → BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (gridTime s tt K n j) Dst
      (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
      (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (gridTime s tt K n j)
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω)) θ Cd
      ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω))
    (hI : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STgANg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n σ b 0 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)))
    (hC1 : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      STgANg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n σ b k ω =
        STgANg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n σ b 0 ω +
          ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n σ b j ω + Rem (σ, b) k ω + Mart (σ, b) k ω)
    (hC2 : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      ‖Rem (σ, b) k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n))
    (hC4 : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      ‖∑ j ∈ Finset.range k, Step2Gen_UN (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n σ
          (gridTime s tt K n j) (gridTime s tt K n k) (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε' *
          (∑ j ∈ Finset.range k, gridStep s tt K n *
            ‖STeeUMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s tt K n j) (gridTime s tt K n k)
              ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω) σ a‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ)) :
    ∀ k, k ≤ K n → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
      ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀ := by
  obtain ⟨hs0, hstt, htt1, hK, hreg, hW, hlam, hA, hlog, hN3, hτ, hε₀, hε'τ, hclos, hNDg, hRm⟩ := hnum
  set Cm := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z) with hCm
  have hL := baStep2Mat_listLink sz (BAflowLam0 sz z) (BAflowEs sz z)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  -- the grid
  have hΔ : 0 ≤ gridStep s tt K n := by
    unfold gridStep; exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hu : ∀ j, gridTime s tt K n (j + 1) = gridTime s tt K n j + gridStep s tt K n := fun j => by
    simp only [gridTime]; push_cast; ring
  have hu00 : gridTime s tt K n 0 = s n := by simp [gridTime]
  have hmem : ∀ j, j ≤ K n → gridTime s tt K n j ∈ Set.Icc (s n) (tt n) := fun j hj =>
    ST_gridTime_mem s tt K n j hstt hK hj
  have hunn : ∀ j, j ≤ K n → 0 ≤ gridTime s tt K n j := fun j hj => hs0.trans (hmem j hj).1
  have hult : ∀ j, j ≤ K n → gridTime s tt K n j ≤ tt n := fun j hj => (hmem j hj).2
  have hu1 : ∀ j, j ≤ K n → gridTime s tt K n j < 1 := fun j hj => (hult j hj).trans_lt htt1
  have hlamj : ∀ j, j ≤ K n → sz.lam n ^ 2 ≤ 1 - gridTime s tt K n j := fun j hj => by
    linarith [hult j hj]
  have hmono : ∀ j m, j ≤ m → gridTime s tt K n j ≤ gridTime s tt K n m := fun j m hjm => by
    unfold gridTime
    have := mul_le_mul_of_nonneg_right (Nat.cast_le (α := ℝ).2 hjm) hΔ
    linarith
  have hherm : ∀ j, (Cm.Hpath s tt K n j ω).IsHermitian := fun j => GridMartBA_Hpath_herm sz (BAflowLam0 sz z) (BAflowEs sz z) n s tt K j ω
  -- the per-time facts at the grid indices `j < k`
  have hPT : ∀ j, j < k →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STelklkMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) (KLloopOf d (sz.L n) σ b) +
            STegtMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) (KLloopOf d (sz.L n) σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
              ((1 - gridTime s tt K n j)⁻¹) ^ 2 + (1 - gridTime s tt K n j)⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (gridTime s tt K n j)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n j)) b) ∧
      (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) σ b b'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - gridTime s tt K n j)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) *
              ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (gridTime s tt K n j)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n j)) b ^ 2) := by
    intro j hj
    have hjK : j ≤ K n := by omega
    exact hpt ⟨gridTime s tt K n j, (hmem j hjK).1, (hult j hjK).trans htn⟩ (Cm.Hpath s tt K n j ω) (hG j hjK) (ih j hj hjK)
  -- the conclusion at `k`
  have hhuk := hu1 k hk
  have hlk := hlamj k hk
  have hQ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hQ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by linarith
  have hs1 : s n < 1 := lt_of_le_of_lt hstt htt1
  unfold BAStep5IIIJsharp
  refine max_lt (Real.one_lt_rpow hW hε₀) ?_
  refine (Finset.sup'_lt_iff _).2 ?_
  rintro ⟨σ, a⟩ -
  have hT : 0 < STtailTD sz n (gridTime s tt K n k)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a :=
    Step5IIIGood_tail_pos sz n _ _ a
  rw [div_lt_iff₀ hT]
  -- the hypotheses of the assembly, for this `σ`
  have hAbnd : ∀ j, j ≤ k → ∀ b : Fin 2 → Zd d (sz.L n),
      ‖STgANg Cm s tt K n σ b j ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    intro j hj b
    have hjK : j ≤ K n := hj.trans hk
    have h := happ (gridTime s tt K n j) (hunn j hjK) ((hult j hjK).trans htn) (Cm.Hpath s tt K n j ω) (hherm j) σ b
    have e : STgANg Cm s tt K n σ b j ω = STLKMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) σ b :=
      (STLKMg_eq_STLKIMg Cm hL n _ _ σ b).symm
    rw [e]
    exact h
  have hrec : ∀ j, j ≤ k → ∀ b : Fin 2 → Zd d (sz.L n),
      STgANg Cm s tt K n σ b j ω = STgANg Cm s tt K n σ b 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ i ∈ Finset.range j,
          (Step2Gen_ThetaN Cm.toFlowFM n σ (gridTime s tt K n i)
              (fun b => STgANg Cm s tt K n σ b i ω) b +
            (STelklkMg Cm n (gridTime s tt K n i) (Cm.Hpath s tt K n i ω) (KLloopOf d (sz.L n) σ b) +
              STegtMg Cm n (gridTime s tt K n i) (Cm.Hpath s tt K n i ω) (KLloopOf d (sz.L n) σ b))) +
          Rem (σ, b) j ω + Mart (σ, b) j ω := by
    intro j hj b
    have h := hC1 σ b j (hj.trans hk)
    simp only [Step5IIIWalk_drift_eq] at h
    rw [h]
  have hI' : ∀ b : Fin 2 → Zd d (sz.L n), ‖STgANg Cm s tt K n σ b 0 ω‖ ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ τ * tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n 0)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n 0))
        (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := by
    intro b
    rw [hu00]
    exact Step5IIIWalk_init sz n hs0 hs1 hW hQ0 b (hI σ b)
  have hMt : ∀ a' : Fin 2 → Zd d (sz.L n), ‖∑ j ∈ Finset.range k,
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s tt K n j) (gridTime s tt K n k)
        (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a'‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (Real.sqrt (2 * Cq * (d : ℝ)) *
        Real.log ((sz.W n : ℕ) : ℝ) + 2 * Real.sqrt Cq *
          (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^
            (-(1 / 4 : ℝ))) + 2) *
      tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
        (zdistInf d (sz.L n) (a' 0 - a' 1) : ℝ) := by
    intro a'
    have h4 := hC4 σ a' k hk
    have hT0 : 0 ≤ tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
        (zdistInf d (sz.L n) (a' 0 - a' 1) : ℝ) := pfStep5_tailTD_nonneg hW0.le
    have hNm : ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤ tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
        (zdistInf d (sz.L n) (a' 0 - a' 1) : ℝ) ^ 2 :=
      hNDg.trans (pfStep5_W2_le hW (hunn k hk) hhuk)
    have hx : ∀ j, j < k → ‖STeeUMg Cm n (gridTime s tt K n j) (gridTime s tt K n k)
        (Cm.Hpath s tt K n j ω) σ a'‖ ≤ (2 * Cq * (((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - gridTime s tt K n j)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) *
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ))) + 1) *
        tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
          (zdistInf d (sz.L n) (a' 0 - a' 1) : ℝ) ^ 2 := by
      intro j hj
      have hjK : j ≤ K n := by omega
      have hy : 0 ≤ (1 - gridTime s tt K n j)⁻¹ := inv_nonneg.2 (by linarith [hu1 j hjK])
      have hwd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg hW0.le d)
      have hp : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - gridTime s tt K n j)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) *
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ)) :=
        mul_nonneg hQ0 (add_nonneg hy (mul_nonneg (mul_nonneg (Real.rpow_nonneg hW0.le _)
          (Real.rpow_nonneg hwd _)) (Real.rpow_nonneg hy _)))
      exact hxx (gridTime s tt K n j) (gridTime s tt K n k) _ (Cm.Hpath s tt K n j ω) σ a' (hunn j hjK)
        (hmono j k hj.le) ((hult k hk).trans htn) hlk hp (hherm j) ((hPT j hj).2 σ)
    exact Step5IIIWalk_mart_real d Cq hCq k (gridTime s tt K n) (gridStep s tt K n) (sz.lam n)
      ((sz.W n : ℕ) : ℝ) (((sz.size n : ℕ) : ℝ) ^ τ) ε₀ _ (((sz.size n : ℕ) : ℝ) ^ ε')
      (((sz.size n : ℕ) : ℝ) ^ (-Dg)) _ (fun j => ‖STeeUMg Cm n (gridTime s tt K n j)
        (gridTime s tt K n k) (Cm.Hpath s tt K n j ω) σ a'‖) hlam hW hΔ
      (by rw [hu00]; exact hs0) hu hhuk hlk hA hlog hε₀.le hQ hT0 hNm hε'τ hx h4
  have hRm' : 64 * ((1 - gridTime s tt K n k)⁻¹) ^ 7 * (((sz.size n : ℕ) : ℝ) ^ C₀ *
      Real.sqrt (gridStep s tt K n) + gridStep s tt K n * ((sz.size n : ℕ) : ℝ) ^ 3) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-Dst) := by
    refine le_trans ?_ hRm
    have hlam2 : 0 < sz.lam n ^ 2 := by positivity
    have h1 : (1 - gridTime s tt K n k)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
      have h2 : (1 - gridTime s tt K n k)⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hlam2 hlk
      have h3 : (sz.lam n ^ 2)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
        rw [inv_le_iff_one_le_mul₀' hlam2]; linarith
      exact h2.trans h3
    have h4 : 0 ≤ (1 - gridTime s tt K n k)⁻¹ := inv_nonneg.2 (by linarith)
    have h5 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n) +
        gridStep s tt K n * ((sz.size n : ℕ) : ℝ) ^ 3 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h4 h1 7)
      (by norm_num)) h5
  have hass := Step5IIIWalk_assemble (C := Cm.toFlowFM) (Cc := Cc) (Cq := Cq) hker hCc hTT (gridStep s tt K n)
    (((sz.size n : ℕ) : ℝ) ^ 3) (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n))
    (((sz.size n : ℕ) : ℝ) ^ τ) ε₀ Dst σ k (gridTime s tt K n) (fun j b => STgANg Cm s tt K n σ b j ω)
    (fun j b => STelklkMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) (KLloopOf d (sz.L n) σ b) +
      STegtMg Cm n (gridTime s tt K n j) (Cm.Hpath s tt K n j ω) (KLloopOf d (sz.L n) σ b))
    (fun j b => Rem (σ, b) j ω) (fun j b => Mart (σ, b) j ω) hlam hW hΔ
    (by rw [hu00]; exact hs0) hu hhuk hlk hA hQ hε₀.le hlog hAbnd
    (fun j hj b => hC2 σ b j (hj.trans hk)) hrec (fun j hj b => (hPT j hj).1 σ b) hI' hMt hRm' a
  calc ‖STLKMg Cm n (gridTime s tt K n k) (Cm.Hpath s tt K n k ω) σ a‖
      = ‖STgANg Cm s tt K n σ a k ω‖ := by rw [STgANg, STLKMg_eq_STLKIMg Cm hL]
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * Step5IIIWalk_Ctot d Cc Cq *
        (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ))) *
        tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
          (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := hass
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (Step5IIIWalk_Ctot d Cc Cq *
        (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) *
        STtailTD sz n (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a := by
          unfold STtailTD; ring
    _ < ((sz.W n : ℕ) : ℝ) ^ ε₀ * STtailTD sz n (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a :=
        mul_lt_mul_of_pos_right hclos hT

end Path

/-! ## 3. The union bound at one size index (band `pfStep5_fixedN`, `Induction/PfStep5.lean:1785`) -/

section FixedN

/-- **The probability at one size index** (band `pfStep5_fixedN`): the failure event of `∀ k ≤ K, J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` is contained in
the union of the failure of the matrix part at the `K + 1` grid times (`hP1`, probability `≤ (K+1) N^{-D₁}`), of the initial bound (`hP2`), of the
weighted martingale tails of the `#labels` labels (`hP4`) and a null set (clauses 1 and 2, `hae`); off it the pathwise induction applies. -/
private theorem Step5IIIWalk2_fixedN {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {s t tt : ℕ → ℝ} {K : ℕ → ℕ}
    {ε₀ τ ε' Dst Dg C₀ τ' θ Cd Cc Cq D₁ D' : ℝ} (hCc : 0 < Cc) (hCq : 0 < Cq)
    (hnum : Step5IIIWalk2_Num sz n s tt K ε₀ τ ε' Dst Dg C₀ (Step5IIIWalk_Ctot d Cc Cq))
    (htn : tt n ≤ t n) (ht0 : 0 ≤ t n)
    (hker : GridRepTailGen_Ker (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n)
    (hTT : ∀ D s' t' : ℝ, 0 ≤ s' → s' ≤ t' → t' < 1 → sz.lam n ^ 2 ≤ 1 - t' → STTailtoTailConclgL (baFMz sz z) n Cc D s' t')
    (hpt : ∀ (u : TimeIcc s t n) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (u : ℝ) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (u : ℝ) H) θ Cd H →
      BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) (u : ℝ) H <
        ((sz.W n : ℕ) : ℝ) ^ ε₀ →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STelklkMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b) +
            STegtMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H (KLloopOf d (sz.L n) σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - (u : ℝ))⁻¹) ^ 2 + (1 - (u : ℝ))⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b) ∧
      (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (u : ℝ) H σ b b'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - (u : ℝ))⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - (u : ℝ))⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (u : ℝ) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (u : ℝ)) b ^ 2))
    (happ : ∀ u : ℝ, 0 ≤ u → u ≤ t n → ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3)
    (hxx : ∀ (v w p : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
      (a : Fin 2 → Zd d (sz.L n)), 0 ≤ v → v ≤ w → w ≤ t n → sz.lam n ^ 2 ≤ 1 - w → 0 ≤ p → H.IsHermitian →
      (∀ b b' : Fin 2 → Zd d (sz.L n),
        (∀ i : Fin 2, (zdistInf d (sz.L n) (b i - b' i) : ℝ) ≤ 2 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v H σ b b'‖ ≤
          p * STtailTD sz n v (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst v) b ^ 2) →
      ‖STeeUMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n v w H σ a‖ ≤
        (2 * Cq * p + 1) * STtailTD sz n w (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst w) a ^ 2)
    (Rem Mart : ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ)
    (hKD : ((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)))
    (hlabel : (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)))
    (hN3 : 3 ≤ ((sz.size n : ℕ) : ℝ))
    (hP1 : ∀ j, j ≤ K n → (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp
      {ω | ¬ BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (gridTime s tt K n j) Dst
        (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (gridTime s tt K n j)
          ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω)) θ Cd
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω)} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)))
    (hP2 : (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp
      {ω | ∃ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst)) <
        ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (s n)
          ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n 0 ω) p.1 p.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))))
    (hae : ∀ᵐ ω ∂((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp), ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      (∀ k, k ≤ K n → STgANg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n i.1 i.2 k ω =
        STgANg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n i.1 i.2 0 ω +
          ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftNg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) s tt K n i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n)))
    (hP4 : ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp
      {ω | ∃ k, k ≤ K n ∧ ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s tt K n *
          ‖STeeUMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n (gridTime s tt K n j) (gridTime s tt K n k)
            ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n j ω) i.1 i.2‖ +
          ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, Step2Gen_UN (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n i.1
          (gridTime s tt K n j) (gridTime s tt K n k) (fun b => Mart (i.1, b) (j + 1) ω - Mart (i.1, b) j ω) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-Dg))) :
    (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Pp
      {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := by
  classical
  set Cm := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z) with hCm
  have hL := baStep2Mat_listLink sz (BAflowLam0 sz z) (BAflowEs sz z)
  have hs0 := hnum.hs0
  have hstt := hnum.hstt
  have hK := hnum.hK
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu00 : gridTime s tt K n 0 = s n := by simp [gridTime]
  -- the four bad events
  set E1 : Set (PathΩ sz) := ⋃ j ∈ Finset.range (K n + 1), {ω | ¬ BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n
      (gridTime s tt K n j) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
      (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (gridTime s tt K n j) (Cm.Hpath s tt K n j ω)) θ Cd
      (Cm.Hpath s tt K n j ω)} with hE1def
  set E2 : Set (PathΩ sz) := {ω | ∃ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ τ *
      (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKMg Cm n (s n) (Cm.Hpath s tt K n 0 ω) p.1 p.2‖} with hE2def
  set E4 : Set (PathΩ sz) := ⋃ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s tt K n *
          ‖STeeUMg Cm n (gridTime s tt K n j) (gridTime s tt K n k) (Cm.Hpath s tt K n j ω) i.1 i.2‖ +
        ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ) <
      ‖∑ j ∈ Finset.range k, Step2Gen_UN Cm.toFlowFM n i.1
        (gridTime s tt K n j) (gridTime s tt K n k) (fun b => Mart (i.1, b) (j + 1) ω - Mart (i.1, b) j ω) i.2‖}
    with hE4def
  set E3 : Set (PathΩ sz) := {ω | ¬ ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      (∀ k, k ≤ K n → STgANg Cm s tt K n i.1 i.2 k ω = STgANg Cm s tt K n i.1 i.2 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftNg Cm s tt K n i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n))}
    with hE3def
  -- the inclusion
  have hsub : {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
      (Cm.Hpath s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ⊆ E1 ∪ E2 ∪ E4 ∪ E3 := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩ := hnot
    refine hω ?_
    have hG : ∀ j, j ≤ K n → BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n (gridTime s tt K n j) Dst
        (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (gridTime s tt K n j) (Cm.Hpath s tt K n j ω)) θ Cd
        (Cm.Hpath s tt K n j ω) := by
      intro j hj
      by_contra hcon
      exact h1 (by
        simp only [hE1def, Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), hcon⟩)
    have hI : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STgANg Cm s tt K n σ b 0 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst)) := by
      intro σ b
      have h : ¬ ((((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst))) < ‖STLKMg Cm n (s n) (Cm.Hpath s tt K n 0 ω) σ b‖) := by
        intro hlt
        exact h2 ⟨(σ, b), hlt⟩
      have e : STgANg Cm s tt K n σ b 0 ω = STLKMg Cm n (s n) (Cm.Hpath s tt K n 0 ω) σ b := by
        rw [← hu00]; exact (STLKMg_eq_STLKIMg Cm hL n _ _ σ b).symm
      rw [e]
      exact not_lt.1 h
    have h3' : ∀ i : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
        (∀ k, k ≤ K n → STgANg Cm s tt K n i.1 i.2 k ω = STgANg Cm s tt K n i.1 i.2 0 ω +
          ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k, STgDriftNg Cm s tt K n i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
        (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n)) := by
      by_contra hcon
      exact h3 hcon
    refine Step5IIIWalk2_path hCc hCq hnum htn ht0 hker hTT hpt happ hxx Rem Mart ω hG hI
      (fun σ b k hk => (h3' (σ, b)).1 k hk) (fun σ b k hk => (h3' (σ, b)).2 k hk)
      (fun σ a k hk => ?_)
    by_contra hcon
    refine h4 ?_
    simp only [hE4def, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(σ, a), k, hk, not_le.1 hcon⟩
  -- the probabilities of the four events
  have hE1 : Cm.Pp E1 ≤ ENNReal.ofReal (((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range (K n + 1), Cm.Pp {ω | ¬ BAStep5IIIEMatrix sz (BAflowLam0 sz z) (BAflowEs sz z) n
        (gridTime s tt K n j) Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ')
        (BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dst (gridTime s tt K n j) (Cm.Hpath s tt K n j ω)) θ Cd
        (Cm.Hpath s tt K n j ω)} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := fun j hj =>
      hP1 j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]
    simp
  have hE2 : Cm.Pp E2 ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := hP2
  have hE4 : Cm.Pp E4 ≤ ENNReal.ofReal ((Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) *
      ((sz.size n : ℕ) : ℝ) ^ (-Dg)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hP4 i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  have hE3 : Cm.Pp E3 = 0 := by
    have := hae
    rw [ae_iff] at this
    exact this
  -- the sum
  have hpow : ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)) = ((sz.size n : ℕ) : ℝ) ^ (-D') *
      ((sz.size n : ℕ) : ℝ)⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN0]; congr 1; ring
  have hfin : 3 * ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D') := by
    rw [hpow]
    have h1 : 3 * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hN0]; exact hN3
    have h2 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg hN0.le _
    nlinarith
  have hP0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)) := Real.rpow_nonneg hN0.le _
  calc Cm.Pp {ω | ∀ k, k ≤ K n → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
          (Cm.Hpath s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ
      ≤ Cm.Pp (E1 ∪ E2 ∪ E4 ∪ E3) := measure_mono hsub
    _ ≤ Cm.Pp E1 + Cm.Pp E2 + Cm.Pp E4 + Cm.Pp E3 := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) +
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) +
        ENNReal.ofReal ((Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) *
          ((sz.size n : ℕ) : ℝ) ^ (-Dg)) + 0 := by
        rw [hE3]
        exact add_le_add (add_le_add (add_le_add hE1 hE2) hE4) le_rfl
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) +
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) +
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) + 0 := by
        exact add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hKD) le_rfl)
          (ENNReal.ofReal_le_ofReal hlabel)) le_rfl
    _ = ENNReal.ofReal (3 * ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := by
        rw [add_zero, ← ENNReal.ofReal_add hP0 hP0, ← ENNReal.ofReal_add (add_nonneg hP0 hP0) hP0]
        congr 1; ring
    _ ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := ENNReal.ofReal_le_ofReal hfin

end FixedN

/-! ## 4. The walk: the constants and the closure (band `pfStep5_walk`, `Induction/PfStep5.lean:2129`) -/

section Walk

/-- **Target 6 (b), the per-flow walk** (`T2493_WalkAt`; the closure `T2459_BAclosure` is this proof): the grid conclusion from the flow, the horizon,
the regime and the five read premises (`T2493_ReadPremises`, written inline: `STDecayStronggL` at `s` is the initial term, band
`pfStep5_init_le`; `STAvgUgL`, `STGdecayWgL`, `STLmaxUgL`, `STLKUgL` go to `baStep5IIIGoodThm_holds`).  The constants: `ε₁ = min(𝔡/8, 1/4)`, `D* = max(D, D₀) + 2d + 1`,
`D₀ = 2/𝔠 + 12 d`, the closure exponent `τ` of `pfStep5Alg_closure` at the constant `Step5IIIWalk_Ctot d Cc Cq` (`Cc` of `baStep5IIIKernel_at_flow`, `Cq` of
`baStep5IIITailSqQV_holds`, both from `κ, 𝔡` only), then `τ' = τ/48`, `θ = min(1/2, τ/(8(Cd+1)))` (after `ε₀`, `τ`), the grid exponent `CK` of
`baGridRepNAt2_holds d`, and the grid `K = ⌈N^{max(CK, C_R)}⌉ + 1`. -/
theorem baStep5III_walk_at (d : ℕ) (hd : 3 ≤ d) :
    ∀ (κ ε 𝔡 Cd : ℝ), 0 < κ → 0 < ε → 0 < 𝔡 → 0 < Cd → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ BAflowT0 sz z n) → STReg5III sz s t →
        (STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧ STAvgUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
          STGdecayWgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd ∧ STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
          STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) →
        BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t := by
  intro κ ε 𝔡 Cd hκ hε h𝔡 hCd 𝔠 sz z hflow s t hs hst htz hReg hread
  obtain ⟨hDecS, hAvg, hGdec, hLmax, hLKU⟩ := hread
  have hAdm := hflow.1
  obtain ⟨h𝔠, -, hsize, hBW, hWO⟩ := hAdm
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have ht0 : ∀ n, 0 ≤ t n := fun n => (hs n).trans (hst' n)
  have hd1 : 1 ≤ d := by omega
  -- the constants of the kernel and of the quadratic variation (from `κ, 𝔡` only)
  obtain ⟨Cc, hCc, hTTev⟩ := baStep5IIIKernel_at_flow d hd κ 𝔡 hκ h𝔡
  obtain ⟨Cq, hCq, hxx⟩ := Step5IIIWalk_xx (d := d) hd κ 𝔡 hκ h𝔡
  have hCtot : 4 ≤ Step5IIIWalk_Ctot d Cc Cq := Step5IIIWalk_Ctot_ge hCc
  refine ⟨min (𝔡 / 8) (1 / 4), by positivity, fun ε₀ hε₀ hε₀1 D hD => ?_⟩
  have hε₀d : ε₀ < 𝔡 / 4 :=
    lt_of_lt_of_le hε₀1 ((min_le_left _ _).trans (by linarith))
  have hε₀h : ε₀ ≤ 1 / 2 := (hε₀1.trans_le (min_le_right _ _)).le.trans (by norm_num)
  -- (b1) the closure exponent `τ` and the level `D*`
  obtain ⟨τ, hτ, hclos⟩ := pfStep5Alg_closure sz 𝔠 𝔡 hflow.1 ε₀ (Step5IIIWalk_Ctot d Cc Cq) hε₀ hε₀d (by linarith)
  obtain ⟨Dst, hDstdef⟩ : ∃ Dst : ℝ, Dst = max D (2 / 𝔠 + 12 * ((d : ℕ) : ℝ)) + 2 * ((d : ℕ) : ℝ) + 1 := ⟨_, rfl⟩
  have hD₀ : (0 : ℝ) < 2 / 𝔠 + 12 * ((d : ℕ) : ℝ) := by positivity
  have hDstD : D + 2 * ((d : ℕ) : ℝ) ≤ Dst := by
    have := le_max_left D (2 / 𝔠 + 12 * ((d : ℕ) : ℝ)); rw [hDstdef]; linarith
  have hDst0 : 0 < Dst := by
    have := le_max_left D (2 / 𝔠 + 12 * ((d : ℕ) : ℝ)); have : (0 : ℝ) ≤ ((d : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hDstdef]; linarith
  have hDstD₀ : 2 / 𝔠 + 12 * ((d : ℕ) : ℝ) ≤ Dst - 2 * ((d : ℕ) : ℝ) := by
    have := le_max_right D (2 / 𝔠 + 12 * ((d : ℕ) : ℝ)); rw [hDstdef]; linarith
  refine ⟨Dst, hDstD, fun tt D' hD' => ?_⟩
  -- the loss exponents `τ'`, `θ` (after `ε₀`, `τ`; the good event quantifies `τ' D₁ θ`)
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = τ / 48 := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := by rw [hτ'def]; positivity
  have h12 : 12 * τ' ≤ τ / 4 := by rw [hτ'def]; linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (1 / 2) (τ / (8 * (Cd + 1))) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθdef]; exact lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := by rw [hθdef]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hθ' : 2 * (θ * (Cd + 1)) ≤ τ / 4 := by
    have h := min_le_right (1 / 2 : ℝ) (τ / (8 * (Cd + 1)))
    rw [hθdef]
    calc 2 * (min (1 / 2) (τ / (8 * (Cd + 1))) * (Cd + 1)) ≤ 2 * (τ / (8 * (Cd + 1)) * (Cd + 1)) := by gcongr
      _ = τ / 4 := by field_simp; ring
  -- the far exponent, the grid exponents
  obtain ⟨D₂, hD₂, hxxEv⟩ := hxx ε 𝔠 hε sz z hflow t htz Dst hDst0.le
  obtain ⟨C₀, hC₀, hAt⟩ := baGridRepNAt2_holds d
  obtain ⟨Dg, hDgdef⟩ : ∃ Dg : ℝ, Dg = max D' (2 * Dst) + 4 := ⟨_, rfl⟩
  have hDgD' : D' + 4 ≤ Dg := by have := le_max_left D' (2 * Dst); linarith
  have hDg2 : 2 * Dst ≤ Dg := by have := le_max_right D' (2 * Dst); linarith
  have hDg0 : 0 < Dg := by linarith
  have hstt : ∀ n, s n ≤ ((tt n : TimeIcc s t n) : ℝ) := fun n => (tt n).2.1
  have httt : ∀ n, ((tt n : TimeIcc s t n) : ℝ) ≤ t n := fun n => (tt n).2.2
  have httz : ∀ n, ((tt n : TimeIcc s t n) : ℝ) ≤ BAflowT0 sz z n := fun n => (httt n).trans (htz n)
  obtain ⟨CK, hCK, hKex⟩ := hAt κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s (fun m => ((tt m : TimeIcc s t m) : ℝ)) hs hstt httz Dg hDg0
  obtain ⟨cK, hcKdef⟩ : ∃ cK : ℝ, cK = max CK (2 * (C₀ + Dst + 14)) := ⟨_, rfl⟩
  have hcKCK : CK ≤ cK := by rw [hcKdef]; exact le_max_left _ _
  have hcKCR : 2 * (C₀ + Dst + 14) ≤ cK := by rw [hcKdef]; exact le_max_right _ _
  have hcK0 : 0 ≤ cK := hCK.trans hcKCK
  obtain ⟨Kf, hKfdef⟩ : ∃ Kf : ℕ → ℕ, Kf = fun n => ⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ + 1 := ⟨_, rfl⟩
  have hKf0 : ∀ n, Kf n ≠ 0 := fun n => by rw [hKfdef]; exact Nat.succ_ne_zero _
  refine ⟨Kf, hKf0, ?_⟩
  have hKge : ∀ n, ∀ c : ℝ, c ≤ cK → ((sz.size n : ℕ) : ℝ) ^ c ≤ (Kf n : ℝ) := by
    intro n c hc
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    rw [hKfdef]
    push_cast
    calc ((sz.size n : ℕ) : ℝ) ^ c ≤ ((sz.size n : ℕ) : ℝ) ^ cK :=
          Real.rpow_le_rpow_of_exponent_le hN1 hc
      _ ≤ (⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ : ℝ) + 1 := by linarith
  obtain ⟨Mart, Rem, h1, h2, -, h4⟩ := hKex Kf hKf0 (Filter.Eventually.of_forall fun n => hKge n CK hcKCK)
  -- the eventual facts
  have hfl : ∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ)) := by
    filter_upwards [hBW] with n hBWn
    have := pfStep5_fl sz n hd1 h𝔠 hBWn hDstD₀
    simpa using this
  have hQ := Step5IIIWalk_hQ (d := d) hd sz hsize hτ hτ'0.le hθ0 hCd h12 hθ'
  have hpertime := Step5IIIWalk_pertime hd κ ε 𝔠 𝔡 sz z hflow s t hs hst hReg Dst τ' θ Cd ε₀ hτ'0.le hε₀.le hε₀h hθ0 hCd hfl
    (fun n => ((sz.size n : ℕ) : ℝ) ^ τ) hQ
  have happ := Step5IIIWalk_apriori (d := d) hd κ ε 𝔠 𝔡 hκ hε h𝔡 sz z hflow t ht0 htz
  have hgood := Step5IIIWalk_good_of_flow hd κ ε 𝔠 𝔡 Cd sz z hκ hε h𝔡 hCd hflow s t hs hst htz hReg hAvg hLmax hLKU hGdec Dst hDst0
  have hgoodEv := baStep5IIIGood_bundle sz z s t Dst Cd hgood τ' (D' + cK + 3) θ hτ'0 (by positivity) hθ0 hθ1
  have hDecSEv := hDecS Dst hDst0 τ hτ (D' + 1) (by linarith)
  have hnumEv := lemDecCalEPrec_numeric sz hflow.1
  have h4' := h4 (τ / 2) (by positivity)
  filter_upwards [hnumEv, hsize.eventually_ge_atTop 4, hclos, hBW, hxxEv, hTTev ε 𝔠 sz z hflow, happ, hpertime, hgoodEv,
    hDecSEv, h2, h4'] with n hn1 hN4 hclosn hBWn hxxn hTTn happn hptn hgoodn hDSn h2n h4n
  obtain ⟨hlam, hA1, hlog4, hN1⟩ := hn1
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
    have h4 : (1 : ℝ) < Real.exp 4 := Real.one_lt_exp_iff.2 (by norm_num)
    by_contra hcon
    have hle : ((sz.W n : ℕ) : ℝ) ≤ 1 := not_lt.1 hcon
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have : Real.log ((sz.W n : ℕ) : ℝ) ≤ 0 := Real.log_nonpos hW0.le hle
    linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := pfStep5_sizes sz n hd1
  have hKn : Kf n ≠ 0 := hKf0 n
  have hreg : sz.lam n ^ 2 ≤ 1 - ((tt n : TimeIcc s t n) : ℝ) := by
    have := hReg n; have := httt n; linarith
  have ht1 : t n < 1 := (htz n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have htt1 : ((tt n : TimeIcc s t n) : ℝ) < 1 := (httt n).trans_lt ht1
  have hΔ : 0 ≤ gridStep s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n :=
    div_nonneg (by linarith [hstt n]) (Nat.cast_nonneg _)
  have hΔN : gridStep s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(2 * (C₀ + Dst + 14))) :=
    pfStep5_gridStep_le (by have := httt n; have := ht1; have := hs n; linarith) hN0
      (hKge n (2 * (C₀ + Dst + 14)) hcKCR)
  have hN3 : (3 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hRm := pfStep5_Rm sz n hd1 hDst0.le hC₀ hΔ hΔN hN3
  have hNDg : ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst)) := by
    calc ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * Dst)) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst)) :=
          Real.rpow_le_rpow_of_nonpos hW0 hs6 (by linarith)
  have hε'τ : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ τ) := by
    refine le_of_eq ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; congr 1; ring
  set Cm := baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z) with hCm
  have hnum : Step5IIIWalk2_Num sz n s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf ε₀ τ (τ / 2) Dst Dg C₀
      (Step5IIIWalk_Ctot d Cc Cq) :=
    ⟨hs n, hstt n, htt1, hKn, hreg, hW1, hlam, hA1, hlog4, hN3, hτ, hε₀, hε'τ, hclosn, hNDg, hRm⟩
  have hker : GridRepTailGen_Ker Cm.toFlowFM n :=
    gridRepTailGen_ker_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)
  have hmem : ∀ j, j ≤ Kf n → gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n j ∈ Set.Icc (s n) (t n) := fun j hj =>
    ⟨(ST_gridTime_mem s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n j (hstt n) hKn hj).1,
      (ST_gridTime_mem s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n j (hstt n) hKn hj).2.trans (httt n)⟩
  refine Step5IIIWalk2_fixedN (D₁ := D' + cK + 3) hCc hCq hnum (httt n) (ht0 n) hker hTTn hptn happn hxxn (Rem n) (Mart n)
    ?_ (pfStep5_hlabel sz n (by linarith) hDgD') hN3 ?_ ?_ ?_ ?_
  · -- `(K+1) N^{-D₁} ≤ N^{-(D'+1)}`
    rw [hKfdef]
    have := pfStep5_hKD (N := ((sz.size n : ℕ) : ℝ)) (c := cK) (D' := D') hcK0 (by linarith)
    simpa using this
  · -- the matrix part at the grid indices (targets 1-2, transfer to the grid walk)
    intro j hj
    obtain ⟨G, hG, hGm⟩ := hgoodn ⟨_, hmem j hj⟩
    exact Step5IIIWalk_good_transfer sz (BAflowLam0 sz z) (BAflowEs sz z) s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n j
      (hs n) (hstt n) hKn Dst (((sz.size n : ℕ) : ℝ) ^ τ') (((sz.size n : ℕ) : ℝ) ^ τ') θ Cd _ G hG hGm
  · -- the initial bound (`STDecayStronggL` at `s`, transferred to the grid walk at the index `0`)
    have hS0 : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        ∃ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKMg Cm n (s n) H p.1 p.2‖} := by
      have : {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
          ∃ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), ((sz.size n : ℕ) : ℝ) ^ τ *
            (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
              ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKMg Cm n (s n) H p.1 p.2‖} =
          ⋃ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)), {H | ((sz.size n : ℕ) : ℝ) ^ τ *
            (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
              ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKMg Cm n (s n) H p.1 p.2‖} := by
        ext H; simp
      rw [this]
      exact MeasurableSet.iUnion fun p => measurableSet_lt measurable_const
        ((Step2EventsGen_STLKMg_measurable (Step2EventsGenTw_baGrid sz (BAflowLam0 sz z) (BAflowEs sz z)) n (s n) p.1 p.2).norm)
    have hlaw := Step2EventsGenTw_baLaw sz (BAflowLam0 sz z) (BAflowEs sz z) s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n 0
      (hs n) (hstt n) hKn _ hS0
    have hu00 : gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n 0 = s n := by simp [gridTime]
    rw [hu00] at hlaw
    refine hlaw.trans_le ((measure_mono ?_).trans hDSn)
    intro ω' hω'
    obtain ⟨p, hp⟩ := hω'
    exact ⟨⟨p, by have := hReg n; have := hst' n; linarith⟩, hp⟩
  · -- clauses 1 and 2 almost everywhere
    exact ae_all_iff.2 fun i => (h1 n i).and (h2n i)
  · -- clause 4 (martingale)
    exact h4n

end Walk

/-! ## 5. Target 6 (c): the walk pin (`T2493_BAWalk`) from the per-flow walk -/

section WalkPin

/-- **Target 6 (c)** (`T2493_BAWalk`; the probe's `T2459_BAWalk`): the shape of `STPfStep5gL` with the grid conclusion, `𝔠d = 1/100` as the band `pfStep5_walk`.
The five read premises are the projections `STDecayStronggL`, conjuncts 2-3 of `STStep2ConclgL` and the inline Steps 3-4 premises; the carried premises
(`STKboundgL`, `STKwardgL`, `STLKgL`, the weak decay premise of `STIngR5gL`, `STConStInd`, `STStep1LoopgL` and the entry-level conjunct of
`STStep2ConclgL`) are unread. -/
theorem baStep5IIIWalk_holds (d : ℕ) : BAStep5IIIWalk d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg hKb hKw hLK hDec hDecS hCon hStep1 hStep2 hLmax hLKU
  exact baStep5III_walk_at d hd κ ε 𝔡 Cd hκ hε h𝔡 hCd 𝔠 sz z hflow s t hs hst htz hReg
    ⟨hDecS, hStep2.2.1, hStep2.2.2, hLmax, hLKU⟩

end WalkPin

/-! ## 6. Target 7: the lift (band `pfStep5_PT_of_walk`, `Induction/PfStep5.lean:2320`, and `pfStep5_lift`, `:2398`) -/

section Lift

open RBM.Ind RBM.Ind.ContinuityNet

/-- **The endpoint, the sections and the descent `D_u ≥ D`** (band `pfStep5_PT_of_walk`): the grid conclusion gives the per-time domination
`STLK2g ≺ T_{u,D}` (`PrecPTL`).  For a section `tt` and `ε₀ = min(ε₁, τ)/2`, the bad event of `STLK2g ≤ N^τ T_{tt,D}` is inside `{J♯(tt, D_{tt}) ≥ W^{ε₀}}`
(`‖L-K‖ ≤ J♯ T_{tt,D_{tt}} ≤ J♯ T_{tt,D}`, `D_{tt} ≥ D`), a measurable set of matrices (`baStep5IIIJsharp_measurable`) whose law at the last grid index
`K` is the law of the single-time model at `tt` (`Step2EventsGenTw_baLaw`, `gridTime_last`). -/
private theorem Step5IIIWalk2_PT (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) (hReg : STReg5III sz s t)
    (hwalk : BAStep5IIIWalkConcl sz (BAflowLam0 sz z) (BAflowEs sz z) s t) {D : ℝ} (hD : 0 < D) :
    PrecPTL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => STLK2g (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2 ω) (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2) := by
  obtain ⟨ε₁, hε₁, hall⟩ := hwalk
  refine Step2EventsGen_PT_of_sections (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) _ hst _ _ fun tt => ?_
  intro τ hτ D' hD'
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ, ε₀ = min ε₁ τ / 2 := ⟨_, rfl⟩
  have hmin : 0 < min ε₁ τ := lt_min hε₁ hτ
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; exact half_pos hmin
  have hε₀1 : ε₀ < ε₁ := by rw [hε₀def]; have := min_le_left ε₁ τ; linarith
  have hε₀τ : ε₀ ≤ τ := by rw [hε₀def]; have := min_le_right ε₁ τ; linarith
  obtain ⟨Dst, hDstD, hK⟩ := hall ε₀ hε₀ hε₀1 D hD
  obtain ⟨K, hK0, hev⟩ := hK tt D' hD'
  filter_upwards [hev, pfStep5_Wev sz hflow.1] with n hn hWn
  obtain ⟨hW1, hWd⟩ := hWn
  obtain ⟨-, -, -, -, -, hWN, hN1⟩ := pfStep5_sizes sz n (by omega : 1 ≤ d)
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWNτ : ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    (Real.rpow_le_rpow hW0.le hWN hε₀.le).trans (Real.rpow_le_rpow_of_exponent_le hN1 hε₀τ)
  -- the level at the section
  have htt1 : ((tt n : TimeIcc s t n) : ℝ) < 1 := (tt n).2.2.trans_lt ((htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n))
  have hlv := pfStep5Grid_level d ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ) ((tt n : TimeIcc s t n) : ℝ) hW1 le_rfl htt1
  have hWdl : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℕ) : ℝ)) ≤ 1 - ((tt n : TimeIcc s t n) : ℝ) := by
    have := hReg n; have := (tt n).2.2; linarith
  have hDlvl : D ≤ PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ) := by
    have := hlv.2.2.2 hWdl; linarith
  -- the measurable set `{J♯ ≥ W^{ε₀}}`
  obtain ⟨B, hBdef⟩ : ∃ B : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      B = {H | ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ)) ((tt n : TimeIcc s t n) : ℝ) H} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_le measurable_const (baStep5IIIJsharp_measurable d sz _ _ n _ _)
  have hsub : {ω' : sz.SeqΩ | ∃ v : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * STtailTD sz n ((tt n : TimeIcc s t n) : ℝ) D v.2 <
        STLK2g (baFMz sz z) n ((tt n : TimeIcc s t n) : ℝ) v.1 v.2 ω'} ⊆
      {ω' | sz.seqHflowBA (BAflowLam0 sz z) n ((tt n : TimeIcc s t n) : ℝ) ω' ∈ B} := by
    rintro ω' ⟨v, hv⟩
    rw [hBdef]
    change ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ)) ((tt n : TimeIcc s t n) : ℝ)
      (sz.seqHflowBA (BAflowLam0 sz z) n ((tt n : TimeIcc s t n) : ℝ) ω')
    set u : ℝ := ((tt n : TimeIcc s t n) : ℝ) with hu
    set Dl : ℝ := PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u with hDl
    set Hm := sz.seqHflowBA (BAflowLam0 sz z) n u ω' with hHm
    have hspec := baStep5IIIJsharp_spec d sz (BAflowLam0 sz z) (BAflowEs sz z) n Dl u Hm
    have h1 := hspec.2 v.1 v.2
    have h2 : STtailTD sz n u Dl v.2 ≤ STtailTD sz n u D v.2 := pfStep5Alg_tailAnti sz n u D Dl v.2 hDlvl
    have hT := Step5IIIGood_tail_pos sz n u D v.2
    have hJ0 : 0 ≤ BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dl u Hm := by linarith [hspec.1]
    have hLK : STLK2g (baFMz sz z) n u v.1 v.2 ω' =
        ‖STLKMg (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) n u Hm v.1 v.2‖ := rfl
    have h3 : STLK2g (baFMz sz z) n u v.1 v.2 ω' ≤
        BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dl u Hm * STtailTD sz n u D v.2 := by
      rw [hLK]; exact h1.trans (mul_le_mul_of_nonneg_left h2 hJ0)
    have h4 : ((sz.size n : ℕ) : ℝ) ^ τ < BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n Dl u Hm := by
      by_contra hcon
      have := mul_le_mul_of_nonneg_right (not_lt.1 hcon) hT.le
      linarith
    exact hWNτ.trans h4.le
  -- transfer to the grid walk at the last grid index
  have hlast := gridTime_last s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (hK0 n)
  have heq := Step2EventsGenTw_baLaw sz (BAflowLam0 sz z) (BAflowEs sz z) s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n)
    (hs n) (tt n).2.1 (hK0 n) B hBm
  rw [hlast] at heq
  have hsub2 : {ω : PathΩ sz | (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n) ω ∈ B} ⊆
      {ω : PathΩ sz | ∀ k, k ≤ K n → BAStep5IIIJsharp sz (BAflowLam0 sz z) (BAflowEs sz z) n
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k))
        (gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k)
        ((baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k ω) <
          ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ := by
    intro ω hω hall'
    have h1 := hall' (K n) le_rfl
    simp only [hlast] at h1
    have hω' : (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).Hpath s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n) ω ∈ B := hω
    rw [hBdef] at hω'
    exact absurd hω' (not_le.2 h1)
  exact (measure_mono hsub).trans (heq.symm.le.trans ((measure_mono hsub2).trans hn))

/-- **The net lift `PrecPTL → PrecL`** of `STLK2g ≺ T_{u,D}` (band `pfStep5_lift` through `lemDecCalEPrec_lift`; here `cont_core` with the good event
`contGood (sz.withLam 0)`, as `NetLiftBA_decay`): `V n = {±}² × (Z_L^d)²`, `A = 4 D + 40`, `#V ≤ N³`, `ε = N^{-D}`; the loop and `𝒦^{(2)}` moduli are
`NetLiftBA_decay_close` (its first conjunct, at `C_d = 0`), and `T_{u',D} ≤ 2 T_{u,D}` is `LemDecCalELip_relcont`. -/
private theorem Step5IIIWalk2_lift (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {D : ℝ} (hD : 0 < D) :
    PrecPTL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => STLK2g (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2 ω) (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2) →
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => STLK2g (baFMz sz z) n (p.1 : ℝ) p.2.1 p.2.2 ω) (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2) := by
  intro hPT
  obtain ⟨ht1, hRange⟩ := baFlow_premises d κ ε 𝔠 𝔡 hκ hε sz z hflow t htT
  have hsize : sz.SizeTendsto := hflow.1.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hd1 : 1 ≤ d := by omega
  set A : ℝ := 4 * D + 40 with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have ev4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 4
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop _
  have evR := nl2_evR sz hRange (half_pos hε) hcast
  have evg0 : ∀ᶠ n : ℕ in atTop, 0 < BAflowLam0 sz z n :=
    (BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow).mono fun n hn => hn.1
  have evW : ∀ᶠ n : ℕ in atTop, 0 ≤ sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨(Real.rpow_pos_of_pos hW _).le.trans hn.1, hn.2⟩
  have evgx : ∀ᶠ n : ℕ in atTop, (|(0 : ℝ)| + 2) * (((sz.size n : ℕ) : ℝ) *
      ((sz.size n : ℕ) : ℝ) ^ (-A)) ≤ 1 / 4 := by
    filter_upwards [cont_gap hsizeN (|(0 : ℝ)| + 2) (κ := 1 / 4) (p := 1 - A) (q := 0) (by norm_num)
      (by rw [hAdef]; linarith), ev1] with n hn h1
    have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-A) =
        ((sz.size n : ℕ) : ℝ) ^ (1 - A) := by
      rw [show (1 - A) = 1 + -A by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [this]
    rw [Real.rpow_zero] at hn
    linarith
  have evgδ : ∀ᶠ n : ℕ in atTop, Real.sqrt (𝔡⁻¹ * ((sz.size n : ℕ) : ℝ) ^ (2 - A / 2)) ≤ 1 / 4 := by
    filter_upwards [cont_gap hsizeN 𝔡⁻¹ (κ := 1 / 16) (p := 2 - A / 2) (q := 0) (by norm_num)
      (by rw [hAdef]; linarith)] with n hn
    rw [Real.rpow_zero] at hn
    exact Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have evg3 : ∀ᶠ n : ℕ in atTop,
      6 * ((sz.size n : ℕ) : ℝ) ^ (11 - A / 2) + ((sz.size n : ℕ) : ℝ) ^ (2 - A) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D) := by
    filter_upwards [cont_gap hsizeN 6 (κ := 1 / 2) (p := 11 - A / 2) (q := -D) (by norm_num)
      (by rw [hAdef]; linarith),
      cont_gap hsizeN 1 (κ := 1 / 2) (p := 2 - A) (q := -D) (by norm_num)
      (by rw [hAdef]; linarith)] with n h1 h2
    linarith
  have hcard : ∀ᶠ n : ℕ in atTop,
      (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) ≤
        ((sz.size n : ℕ) : ℝ) ^ (((3 : ℕ) : ℝ)) := by
    filter_upwards [ev4] with n h4
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
      simp [Zd, ZMod.card]
    have hcardV : (Fintype.card ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) : ℝ) =
        4 * (((sz.L n : ℝ)) ^ d) ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, hcardZ]
      push_cast
      ring
    have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
    have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) := Nat.cast_nonneg _
    have hLW : (sz.L n : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
    have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by
      simp [Sizes.size]
    have hLN : (sz.L n : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      rw [eN]; exact pow_le_pow_left₀ hL0 hLW d
    rw [hcardV, Real.rpow_natCast]
    calc 4 * ((sz.L n : ℝ) ^ d) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 2 :=
          mul_le_mul h4 (pow_le_pow_left₀ (by positivity) hLN 2) (by positivity) hN0.le
      _ = ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  refine cont_core (V := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) hsizeN hst hlen
    (A := A) (Cv := ((3 : ℕ) : ℝ)) hA0 (Nat.cast_nonneg _) hcard hPT
    (cont_highProbAt_good (sz.withLam 0) hsizeN)
    (ε := fun n => ((sz.size n : ℕ) : ℝ) ^ (-D))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) ?_ ?_
  · -- `hlow`: `N^{-D} ≤ W^{-D} ≤ T_{u,D}`
    filter_upwards [ev1] with n hn1
    intro p ω
    obtain ⟨u, σ, a⟩ := p
    obtain ⟨-, -, -, -, -, hWN, -⟩ := pfStep5_sizes sz n hd1
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact (Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)).trans
      (lemDecCalEPrec_tail_ge sz n (u : ℝ) D a)
  · -- `hclose`
    filter_upwards [evc, evR, evW, evgx, evgδ, evg3, evg0, ev1] with n hc hR hW gx gδ g3 hg hn1
    intro ω hω u u' hΔ v
    obtain ⟨σ, a⟩ := v
    have hdec := NetLiftBA_decay_close sz hκ hflow n hg ω 0 (N := ((sz.size n : ℕ) : ℝ)) (s := s n)
      (t := t n) (u := u) (u' := u') (D := D) (A := A) (Dg := 𝔡⁻¹) rfl hd1 (hs0 n)
      u.2.1 u.2.2 u'.2.1 u'.2.2 (ht1 n) hc hR (fun c => hω c) hΔ hW.1 hW.2 gx gδ g3 σ a
    refine ⟨hdec.1, ?_⟩
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hrel := (LemDecCalELip_relcont sz n (t n) (u : ℝ) (u' : ℝ) D a (ht1 n) u.2.2 u'.2.2).2.2.2.1
    have hx : (1 - t n)⁻¹ * |(u : ℝ) - (u' : ℝ)| ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-A) :=
      mul_le_mul hR hΔ (abs_nonneg _) hN0.le
    have hx8 : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-A) ≤ 1 / 8 := by
      have : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-A) := by positivity
      simp only [abs_zero, zero_add] at gx
      linarith
    have hρ0 : 0 ≤ (1 - t n)⁻¹ * |(u : ℝ) - (u' : ℝ)| := mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (abs_nonneg _)
    have hρ : (1 + (1 - t n)⁻¹ * |(u : ℝ) - (u' : ℝ)|) ^ 2 ≤ 2 := by nlinarith
    have hT0 : 0 ≤ STtailTD sz n (u : ℝ) D a := tailTD_nonneg (Nat.cast_nonneg _)
    exact hrel.trans (by nlinarith)

/-- **Target 7** (`T2493_BAFromWalk`; the probe's `T2459_BAfromWalk`, correction (a): `0 < ε`, `0 < 𝔡` added for the `η`-window and the `𝒦` window):
the grid conclusion gives `STPfConclgL`: the endpoint, the sections and the descent `D_u ≥ D` (`Step5IIIWalk2_PT`), the net lift `PrecPTL → PrecL`
(`Step5IIIWalk2_lift`: `cont_core` with the resolvent and `𝒦^{(2)}` moduli of `NetLiftBA`), and the restriction to the sizes with `lam² ≤ 1 - t` (`precomp_param`). -/
theorem baStep5IIIFromWalk_holds (d : ℕ) : BAStep5IIIFromWalk d := by
  intro hd κ ε 𝔠 𝔡 sz z hκ hε h𝔡 hflow s t hs hst htz hReg hwalk D hD
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hPT := Step5IIIWalk2_PT hd sz hκ hflow hs hst' htz hReg hwalk hD
  have hPrec := Step5IIIWalk2_lift hd sz hκ hε hflow hs hst' htz hD hPT
  exact StochDomAt.precomp_param hPrec
    (fun n (p : {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n}) => p.1)

end Lift

/-! ## 7. Compiled nonempty instances at `d = 3` (target 8)

`sz0`, `zSeq`, `flow_sz0` with `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `s ≡ 1/10 < t ≡ 1/2 < t₀` (`half_lt_t0`), `Cd = 1`.  The regime
(`Step5IIIGood_reg_sz0`) and `(con_st_ind)` (`s1Setup_conStInd_const`) are discharged; what stays a hypothesis is the Steps 1-4 carrier predicates of
`STIngR5gL` (other gates' pins; the probe's `T2459_inst_IngR5` route).  Targets 1-5 and the per-time layer have their instances in
`BA/Step5IIIWalk.lean` (section 11). -/

end RBM.BA
