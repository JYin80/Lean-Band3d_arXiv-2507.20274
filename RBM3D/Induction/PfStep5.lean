/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.PfStep5Grid
import RBM3D.Induction.TailtoTailSq
import RBM3D.Path.DifREP3

/-!
# S5-11b (ST-4): `lem:pf_step5`, part 2b: the stopped loop on the grid, the lift, `STPfStep5`

Ticket T2231 (DECISIONS §71, §70, §64, §63).  Paper: arXiv:2507.20274,
`paper/tex/3_5_Loop_Hierarchy.tex:2364-2369` (`eq:def_TTT`), `:2371-2383` (`lem:pf_step5`; the paper
omits the proof, "analogous to, and in fact much simpler than, the proof of (2.76) in
[YY_25, §5.3]", `3_5:2380`), `:134` (`int_K-L_ST`), `:218-240` (`alu9_STime`).  No RBM2D
counterpart (RBM2D derives Step 5 from Step 4).

Proves the borrowed pin `STPfStep5 d` (`Induction/Step5Pins.lean:211`, text unchanged) from the
deterministic grid layer of S5-11a (`PfStep5Grid`: level `D_u`, `J♯`, the Duhamel form), S5-10
(`PfStep5Alg`), S5-10a (`TailtoTailSq`), S5-09/09a (`LemDecCalEPrec`, `LemDecCalELip`) and the
merged `stGridRepN_holds` (`Path/DifREP3.lean`); target 8 is the one line `STStep5III d`.  The
vocabulary (section 0) and the six pins (section 1) are copies of
`docs/tickets/checks/T2231-check.lean`; each target theorem has the body of the pin of the same
name.

* **1** `pfStep5_realize`: every grid state `H_k = seqXmat(√s ω₀ + √Δ Σ_{i ≤ k} ω_i)` is a
  single-time state `seqHflow n u_k ω'` (private copies of the realization lemmas of
  `Path/Walk.lean:280-316, 411-424`).
* **2** `pfStep5_goodMeas`: the good event `lemDecCalEPrec_good` is the preimage of a measurable set
  of matrices.
* **3** `pfStep5_farAbsorb`: `4 Y L^d ρ³ W^{-D₂} ≤ W^{-2D*}` for `D₂ = 2D* + 8/𝔠 + 3d + 1`,
  `Y = 2N(16N)^6`.
* **4** `pfStep5_walk` (`(b1)-(b3)`): with `ε₁ = min(𝔡/8, 1/4)`, `D* = max(D, D₀) + 2d + 1`,
  `D₀ = 2/𝔠 + 12 d`, the closure exponent `τ` of `pfStep5Alg_closure` at the constant `C_tot`
  (`pfStep5_Ctot`), the loss `τ' = min(τ/24, 1/(2D*))`, the grid exponent `C_K` of `STGridRepNAt` at
  `m = 2` and the grid `K = ⌈N^{max(C_K, C_R)}⌉ + 1`, the failure event of
  `∀ k ≤ K, J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` is covered by the failure of the good events at the
  `K + 1` grid times (transfer `ST_pathP_eq_seqP`), of the initial bound (`STDecayStrong` at `s`),
  of the weighted martingale tail (conjunct 4) of each label, and a null set (conjuncts 1, 2); off
  it the strong induction on `k` (`pfStep5_path`) gives `J♯(u_k, D_{u_k}) < W^{ε₀}`: `goodStop'` and
  `goodDet` per time (`pfStep5_perj`), the Duhamel form (`pfStep5Grid_duhamel`), the four terms
  (`pfStep5_assemble`: initial, drift by `pfStep5Alg_ugenSum'`, martingale by `tailtoTailSq_kernel`
  and `pfStep5_mart_real`, remainder), `pfStep5Alg_riemann`, `pfStep5Alg_closure`.
* **5** `pfStep5_PT_of_walk`: endpoint (`gridTime_last`), sections (`ST_PT_of_sections`), descent
  `D_u ≥ D`.
* **6** `pfStep5_lift`: the only lift of the ticket (`PrecPT → Prec`, deterministic floored right
  side, DECISIONS §64 (4)).
* **7** `stPfStep5_holds`; **8** `stStep5III_holds`.

Corrections (c1)-(c3) of the ticket are followed: one grid per section and per probability exponent
(`PfStep5_walkConcl`); conjuncts 1, 2, 4 of `STGridRepNAt` are used; conjunct 4 is uniform in
`k ≤ K`, so no stopping index is needed (strong induction on the grid index).  Ports: private text
of `Path/Walk.lean` (cited at each lemma), copied because it is private there; nothing from
RBM1D/RBM2D.  Registry (`RBM3D/Test/Axioms.lean`): the lines of `STPfStep5` and `STStep5III` are
removed; the one `Prop` assumed here, `PfStep5_walkConcl` (hypothesis of target 5), is appended to
`owedProps`.  Paper-delta candidates `T2231a`-`T2231c` in the report.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 0. Vocabulary -/

/-- **The grid conclusion** (b1-b3): there is `ε₁ > 0` such that for every `ε₀ ∈ (0, ε₁)` and every `D > 0`
there is a level `D* ≥ D + 2d` such that for every section `tt n ∈ [s_n, t_n]` and every probability
exponent `D'`, some grid `K` from `s` to `tt` has, eventually, `J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for **all**
`k ≤ K` outside an event of probability `≤ N^{-D'}` (the grid depends on `D'`: the grid exponent `C_K` of
`STGridRepNAt` depends on its `D`). -/
def PfStep5_walkConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε₀ : ℝ, 0 < ε₀ → ε₀ < ε₁ → ∀ D : ℝ, 0 < D →
    ∃ Dst : ℝ, D + 2 * (d : ℝ) ≤ Dst ∧ ∀ tt : ∀ n, TimeIcc s t n, ∀ D' : ℝ, 0 < D' →
      ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧ ∀ᶠ n in atTop,
        pathP sz {ω | ∀ k, k ≤ K n →
          PfStep5Grid_JsharpM sz n (E n)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s (fun m => (tt m : ℝ)) K n k))
              (gridTime s (fun m => (tt m : ℝ)) K n k) (pathH sz s (fun m => (tt m : ℝ)) K n k ω) <
            ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D'))

/-- **The per-time conclusion** (b4): `STLK2 ≺ T_{u,D}` per time on `[s,t] × {±}² × (Z_L^d)²`. -/
def PfStep5_PTConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2)

/-- **The uniform conclusion** (b5): `STLK2 ≺ T_{u,D}` uniformly in `u` (the union over `u` inside `P`). -/
def PfStep5_PrecConcl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))))
      (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1 : ℝ) D p.2.2)

/-! ## 1. Pins -/

/-- **Target 1** (realization): every grid state is a single-time state at the grid time
(`H_k = seqXmat(c)`, `c = √s ω₀ + √Δ Σ_{i ≤ k} ω_i`; `ω' := (√u_k)⁻¹ • c` if `u_k > 0`, any `ω'` if `u_k = 0`). -/
def PfStep5_realize_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) (ω : PathΩ sz), 0 ≤ s n → s n ≤ t n →
    ∃ ω' : sz.SeqΩ, sz.seqHflow n (gridTime s t K n j) ω' = pathH sz s t K n j ω

/-- **Target 2** (the good event of S5-09 is the preimage of a measurable set of matrices). -/
def PfStep5_goodMeas_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (Jst : ℕ → ℝ → ℝ → ℝ) (τ' : ℝ) (n : ℕ) (u : ℝ),
    ∃ S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ), MeasurableSet S ∧
      ∀ ω : sz.SeqΩ, ω ∈ lemDecCalEPrec_good sz E D Jst τ' n u ↔ sz.seqHflow n u ω ∈ S

/-- **Target 3** (far-remainder absorption, DECISIONS §71): with `Y = 2N(16N)^6` (`difRep2_norm_STeeM_le_N`
at `m = 2`), some `D₂` gives `4 Y L^d ρ³ W^{-D₂} ≤ W^{-2D*}` eventually, uniformly in `0 ≤ v ≤ w`,
`ilambda² ≤ 1 - w` (`ρ = (1-v)/(1-w) ≤ ilambda^{-2} ≤ W^d`, `L^d ≤ N ≤ W^{1/𝔠}`). -/
def PfStep5_farAbsorb_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, sz.Admissible 𝔠 𝔡 → ∀ Dst : ℝ, 0 ≤ Dst → ∃ D₂ : ℝ, 0 ≤ D₂ ∧
    ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) * ((sz.L n : ℕ) : ℝ) ^ d *
          ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))

/-- **Target 4** (the stopped loop on the grid, b1-b3): the setting of Step 5, regime (iii), gives the grid
conclusion. -/
def PfStep5_walk_pin (d : ℕ) : Prop :=
  STIngR5 d STReg5III (fun sz E s t => PfStep5_walkConcl sz E s t)

/-- **Target 5** (endpoint, sections, descent `D_u ≥ D`, b4). -/
def PfStep5_PT_of_walk_pin (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (E s t : ℕ → ℝ), (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    STReg5III sz s t →
    (∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧ ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ sz.lam n ^ 2) →
    PfStep5_walkConcl sz E s t → PfStep5_PTConcl sz E s t

/-- **Target 6** (the lift `PrecPT → Prec`, b5; DECISIONS §64 (4): deterministic right side, floor `W^{-D}`). -/
def PfStep5_lift_pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
        STReg5III sz s t →
        PfStep5_PTConcl sz (STflowE z) s t → PfStep5_PrecConcl sz (STflowE z) s t

/-! ## 2. Target 1: realization -/

section Realize

variable {d : ℕ} {sz : Sizes d}

-- copy of `Path/Walk.lean:280` (private there).
private theorem pfStep5_slice_add (n : ℕ) (ω ν : Sizes.SeqΩ sz) :
    Sizes.slice sz n (ω + ν) = Sizes.slice sz n ω + Sizes.slice sz n ν := rfl

-- copy of `Path/Walk.lean:283` (private there).
private theorem pfStep5_slice_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ sz) :
    Sizes.slice sz n (a • ω) = a • Sizes.slice sz n ω := rfl

-- copy of `Path/Walk.lean:286` (private there).
private theorem pfStep5_slice_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ sz) :
    Sizes.slice sz n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.slice sz n (ω l) := by
  funext c
  simp [Sizes.slice, Finset.sum_apply]

-- copy of `Path/Walk.lean:293` (private there).
private theorem pfStep5_seqXmat_add (n : ℕ) (ω ν : Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (ω + ν) = Sizes.seqXmat sz n ω + Sizes.seqXmat sz n ν := by
  unfold Sizes.seqXmat
  rw [pfStep5_slice_add, Xmat_add]

-- copy of `Path/Walk.lean:299` (private there).
private theorem pfStep5_seqXmat_smul (n : ℕ) (a : ℝ) (ω : Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (a • ω) = a • Sizes.seqXmat sz n ω := by
  unfold Sizes.seqXmat
  rw [pfStep5_slice_smul, Xmat_smul]

-- copy of `Path/Walk.lean:305` (private there).
private theorem pfStep5_seqXmat_sum {ι : Type*} (n : ℕ) (S : Finset ι) (ω : ι → Sizes.SeqΩ sz) :
    Sizes.seqXmat sz n (∑ l ∈ S, ω l) = ∑ l ∈ S, Sizes.seqXmat sz n (ω l) := by
  unfold Sizes.seqXmat
  rw [pfStep5_slice_sum]
  exact map_sum (Xlinear d (sz.L n) (sz.W n)) (fun l => Sizes.slice sz n (ω l)) S

-- copy of `Path/Walk.lean:313` (private there).
private theorem pfStep5_real_smul_matrix {m : Type*} (r : ℝ) (M : Matrix m m ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

-- copy of `Path/Walk.lean:411` (private there).
private theorem pfStep5_pathH_eq (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz) :
    pathH sz s t K n k ω
      = Sizes.seqXmat sz n ((Real.sqrt (s n) : ℝ) • ω 0
          + (Real.sqrt (gridStep s t K n) : ℝ) • ∑ i ∈ Finset.Icc 1 k, ω i) := by
  rw [pfStep5_seqXmat_add, pfStep5_seqXmat_smul, pfStep5_seqXmat_smul, pfStep5_seqXmat_sum,
    pfStep5_real_smul_matrix, pfStep5_real_smul_matrix]
  rfl

-- copy of `Path/Walk.lean:421` (private there).
private theorem pfStep5_seqHflow_eq (n : ℕ) (u : ℝ) (ω' : Sizes.SeqΩ sz) :
    Sizes.seqHflow sz n u ω' = Sizes.seqXmat sz n ((Real.sqrt u : ℝ) • ω') := by
  rw [Sizes.seqHflow_eq_smul, pfStep5_seqXmat_smul, pfStep5_real_smul_matrix]

/-- **Target 1** (realization): every grid state is a single-time state at the grid time. -/
theorem pfStep5_realize {d : ℕ} (sz : Sizes d) : PfStep5_realize_pin sz := by
  intro s t K n j ω hs hst
  set Δ : ℝ := gridStep s t K n with hΔ
  set c : Sizes.SeqΩ sz := (Real.sqrt (s n) : ℝ) • ω 0
    + (Real.sqrt Δ : ℝ) • ∑ i ∈ Finset.Icc 1 j, ω i with hc
  have hΔ0 : 0 ≤ Δ := by
    rw [hΔ]; unfold gridStep
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  have hjΔ : 0 ≤ (j : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  set u : ℝ := gridTime s t K n j with hu
  have hu' : u = s n + (j : ℝ) * Δ := rfl
  have hu0 : 0 ≤ u := by rw [hu']; linarith
  have key : (Real.sqrt u : ℝ) • (((Real.sqrt u)⁻¹ : ℝ) • c) = c := by
    by_cases hu00 : u = 0
    · have hs0 : s n = 0 := by rw [hu'] at hu00; linarith
      have hjΔ0 : (j : ℝ) * Δ = 0 := by rw [hu'] at hu00; linarith
      have hc0 : c = 0 := by
        rw [hc, hs0, Real.sqrt_zero, zero_smul, zero_add]
        by_cases hj0 : j = 0
        · subst hj0
          simp
        · have hΔ00 : Δ = 0 := by
            rcases mul_eq_zero.1 hjΔ0 with h | h
            · exact absurd (by exact_mod_cast h) hj0
            · exact h
          rw [hΔ00, Real.sqrt_zero, zero_smul]
      rw [hc0, smul_zero, smul_zero]
    · have hsq : Real.sqrt u ≠ 0 := (Real.sqrt_pos.2 (lt_of_le_of_ne hu0 (Ne.symm hu00))).ne'
      rw [smul_inv_smul₀ hsq]
  refine ⟨((Real.sqrt u)⁻¹ : ℝ) • c, ?_⟩
  rw [pfStep5_seqHflow_eq, pfStep5_pathH_eq]
  congr 1

end Realize

/-! ## 3. Target 2: the good event of S5-09 as a preimage of a measurable set of matrices -/

section GoodMeas

/-- A finite family of measurable inequalities cuts out a measurable set of matrices. -/
private theorem pfStep5_measSet_forall_le {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (f g : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    MeasurableSet {x : X | ∀ i, f i x ≤ g i x} := by
  have : {x : X | ∀ i, f i x ≤ g i x} = ⋂ i, {x | f i x ≤ g i x} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurableSet_le (hf i) (hg i)

/-- `gexRHS` is measurable in the matrix. -/
private theorem pfStep5_gexRHS_measurable {d : ℕ} (L W : ℕ) [NeZero L] [NeZero W] (E u : ℝ)
    (a b : Zd d L) :
    Measurable fun H : Matrix (Idx d L W) (Idx d L W) ℂ => RBM.Green.gexRHS d L W E u H a b := by
  unfold RBM.Green.gexRHS
  refine (Finset.measurable_sum _ fun a' _ => Finset.measurable_sum _ fun b' _ => ?_).add
    measurable_const
  by_cases h : zdistInf d L (a' - a) ≤ 1 ∧ zdistInf d L (b' - b) ≤ 1
  · simp only [h, and_self, ite_true]
    exact (walk_measurable_loopFine d L W (zt E u) ![true, false] ![a', b']).norm
  · simp only [h, ite_false]
    exact measurable_const

/-- **Target 2** (the good event is the preimage of a measurable set of matrices). -/
theorem pfStep5_goodMeas {d : ℕ} (sz : Sizes d) : PfStep5_goodMeas_pin sz := by
  intro E D Jst τ' n u
  classical
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  refine ⟨{H | (∀ p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
        ‖STLKM sz n (E n) u H p.1 p.2‖ ≤ N ^ τ' * (Jst n u D * STtailTD sz n u D p.2)) ∧
      (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        ‖STGMM sz n (E n) u H p.1 p.2‖ ^ 2 ≤
          N ^ τ' * STWB sz n u (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2))) ∧
      (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), p.1 ≠ p.2 →
        ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
          N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2) (STblk sz n p.1)) ∧
      (∀ p : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)),
        ‖STLKM sz n (E n) u H p.1 p.2‖ ≤ N ^ τ' * sz.Bctl n u ^ 1) ∧
      (∀ p : (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)),
        ‖STLM sz n (E n) u H p.1 p.2‖ ≤ N ^ τ' * sz.Bctl n u ^ (3 - 1)) ∧
      (∀ p : (Fin 4 → Bool) × (Fin 4 → Zd d (sz.L n)),
        ‖STLM sz n (E n) u H p.1 p.2‖ ≤ N ^ τ' * sz.Bctl n u ^ (4 - 1)) ∧
      (∀ p : (Fin 6 → Bool) × (Fin 6 → Zd d (sz.L n)),
        ‖STLM sz n (E n) u H p.1 p.2‖ ≤ N ^ τ' * sz.Bctl n u ^ (6 - 1))}, ?_, fun ω => ?_⟩
  · -- measurability
    have hm1 := pfStep5_measSet_forall_le
      (fun (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STLKM sz n (E n) u H p.1 p.2‖)
      (fun p _ => N ^ τ' * (Jst n u D * STtailTD sz n u D p.2))
      (fun p => (STLKM_measurable sz n (E n) u p.1 p.2).norm) (fun p => measurable_const)
    have hm2 := pfStep5_measSet_forall_le
      (fun (p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STGMM sz n (E n) u H p.1 p.2‖ ^ 2)
      (fun p _ => N ^ τ' * STWB sz n u (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))
      (fun p => ((STGMM_measurable sz n (E n) u p.1 p.2).norm).pow_const 2)
      (fun p => measurable_const)
    have hm3 : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), p.1 ≠ p.2 →
          ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
            N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
              (STblk sz n p.1)} := by
      have : {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
        ∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n), p.1 ≠ p.2 →
          ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
            N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
              (STblk sz n p.1)} = ⋂ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
          {H | p.1 ≠ p.2 → ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
            N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
              (STblk sz n p.1)} := by ext H; simp
      rw [this]
      refine MeasurableSet.iInter fun p => ?_
      by_cases hp : p.1 = p.2
      · have h0 : {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
            p.1 ≠ p.2 → ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
              N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
                (STblk sz n p.1)} = Set.univ := by
          ext H; simp [hp]
        rw [h0]
        exact MeasurableSet.univ
      · have h0 : {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
            p.1 ≠ p.2 → ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
              N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
                (STblk sz n p.1)} = {H | ‖Gres H (zt (E n) u) true p.1 p.2‖ ^ 2 ≤
              N ^ τ' * RBM.Green.gexRHS d (sz.L n) (sz.W n) (E n) u H (STblk sz n p.2)
                (STblk sz n p.1)} := by
          ext H; simp [hp]
        rw [h0]
        exact measurableSet_le
          (((walk_measurable_Gres_apply (zt (E n) u) true p.1 p.2).norm).pow_const 2)
          (measurable_const.mul (pfStep5_gexRHS_measurable (sz.L n) (sz.W n) (E n) u _ _))
    have hm4 := pfStep5_measSet_forall_le
      (fun (p : (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STLKM sz n (E n) u H p.1 p.2‖)
      (fun p _ => N ^ τ' * sz.Bctl n u ^ 1)
      (fun p => (STLKM_measurable sz n (E n) u p.1 p.2).norm) (fun p => measurable_const)
    have hm5 := pfStep5_measSet_forall_le
      (fun (p : (Fin 3 → Bool) × (Fin 3 → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STLM sz n (E n) u H p.1 p.2‖)
      (fun p _ => N ^ τ' * sz.Bctl n u ^ (3 - 1))
      (fun p => (STLM_measurable sz n (E n) u p.1 p.2).norm) (fun p => measurable_const)
    have hm6 := pfStep5_measSet_forall_le
      (fun (p : (Fin 4 → Bool) × (Fin 4 → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STLM sz n (E n) u H p.1 p.2‖)
      (fun p _ => N ^ τ' * sz.Bctl n u ^ (4 - 1))
      (fun p => (STLM_measurable sz n (E n) u p.1 p.2).norm) (fun p => measurable_const)
    have hm7 := pfStep5_measSet_forall_le
      (fun (p : (Fin 6 → Bool) × (Fin 6 → Zd d (sz.L n)))
        (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
          ‖STLM sz n (E n) u H p.1 p.2‖)
      (fun p _ => N ^ τ' * sz.Bctl n u ^ (6 - 1))
      (fun p => (STLM_measurable sz n (E n) u p.1 p.2).norm) (fun p => measurable_const)
    exact hm1.inter (hm2.inter (hm3.inter (hm4.inter (hm5.inter (hm6.inter hm7)))))
  · -- the equivalence, by unfolding
    simp only [lemDecCalEPrec_good, Set.mem_ofPred_eq, Prod.forall]
    rfl

end GoodMeas

/-! ## 4. Target 3: absorption of the far remainder -/

section FarAbsorb

/-- `W ≥ 1`, `L ≥ 1`, `N = (W L)^d`, `L^d ≤ N`, `W^d ≤ N`, `W ≤ N` and `1 ≤ N` for `1 ≤ d`
(private copy of `lemDecCalEPrec_sizes` with `L^d ≤ N`). -/
private theorem pfStep5_sizes {d : ℕ} (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) :
    1 ≤ ((sz.W n : ℕ) : ℝ) ∧ 1 ≤ ((sz.L n : ℕ) : ℝ) ∧
      ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d ∧
      ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) ∧
      ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) ∧
      ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ∧ 1 ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have hWd : 1 ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ hW
  have hLd : 1 ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL
  refine ⟨hW, hL, hN, ?_, ?_, ?_, ?_⟩
  · rw [hN]; nlinarith
  · rw [hN]; nlinarith
  · rw [hN]
    calc ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := le_self_pow₀ hW (by omega)
      _ ≤ _ := by nlinarith
  · rw [hN]; nlinarith

/-- `d ≥ 1` from `N → ∞`. -/
private theorem pfStep5_one_le_d {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) : 1 ≤ d := by
  by_contra h
  have hd0 : d = 0 := by omega
  subst hd0
  obtain ⟨n, hn⟩ := (hsize.eventually_ge_atTop 2).exists
  simp [Sizes.size] at hn

/-- **Target 3** (far-remainder absorption). -/
theorem pfStep5_farAbsorb {d : ℕ} (sz : Sizes d) : PfStep5_farAbsorb_pin sz := by
  intro 𝔠 𝔡 hA Dst hDst
  obtain ⟨h𝔠, h𝔡, hsize, hBW, hWO⟩ := hA
  have hd : 1 ≤ d := pfStep5_one_le_d sz hsize
  refine ⟨2 * Dst + 8 / 𝔠 + 3 * d + 1, by positivity, ?_⟩
  have hNc : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop :=
    (tendsto_rpow_atTop h𝔠).comp hsize
  filter_upwards [hWO, hBW, hNc.eventually_ge_atTop (8 * 16 ^ 6)] with n hWOn hBWn hbig
  intro v w hv hvw hw
  obtain ⟨hW1, hL1, hNe, hLN, hWdN, hWN, hN1⟩ := pfStep5_sizes sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set L : ℝ := ((sz.L n : ℕ) : ℝ) with hLdef
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWOn.1
  have hA1 := lam_sq_mul_pow_ge sz n hWOn.1
  have hW2 : 1 ≤ W ^ (2 * 𝔡) := Real.one_le_rpow hW1 (by positivity)
  have hlam2 : 0 < sz.lam n ^ 2 := by positivity
  have hWd0 : 0 < W ^ d := pow_pos hW0 d
  -- `W ≥ 8 * 16^6`
  have hW27 : (8 * 16 ^ 6 : ℝ) ≤ W := hbig.trans hBWn
  -- `1 - w ≥ lam², 1 - v ≤ 1`
  have h1w : 0 < 1 - w := lt_of_lt_of_le hlam2 hw
  have h1v : 0 < 1 - v := by linarith
  have hρ : (1 - v) / (1 - w) ≤ W ^ d := by
    have h1 : (1 - v) / (1 - w) ≤ 1 / (1 - w) :=
      div_le_div_of_nonneg_right (by linarith) h1w.le
    have h2 : 1 / (1 - w) ≤ 1 / sz.lam n ^ 2 := one_div_le_one_div_of_le hlam2 hw
    have h3 : 1 / sz.lam n ^ 2 ≤ W ^ d := by
      rw [div_le_iff₀ hlam2]
      nlinarith
    linarith
  have hρ0 : 0 ≤ (1 - v) / (1 - w) := div_nonneg h1v.le h1w.le
  have hρ3 : ((1 - v) / (1 - w)) ^ 3 ≤ W ^ (3 * d) := by
    calc ((1 - v) / (1 - w)) ^ 3 ≤ (W ^ d) ^ 3 := pow_le_pow_left₀ hρ0 hρ 3
      _ = W ^ (3 * d) := by rw [← pow_mul]; ring_nf
  -- `N ≤ W^{1/𝔠}`
  have hNW : N ≤ W ^ (1 / 𝔠) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hBWn (by positivity : (0 : ℝ) ≤ 1 / 𝔠)
    rw [← Real.rpow_mul hN0.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one] at h
    exact h
  have hN8 : N ^ 8 ≤ W ^ (8 / 𝔠) := by
    calc N ^ 8 ≤ (W ^ (1 / 𝔠)) ^ 8 := pow_le_pow_left₀ hN0.le hNW 8
      _ = W ^ (8 / 𝔠) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  -- the bound
  have hexp : W ^ (8 / 𝔠) * W ^ (3 * d) * W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) =
      W ^ (-(2 * Dst)) * W⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hW0, ← Real.rpow_add hW0, ← Real.rpow_neg_one,
      ← Real.rpow_add hW0]
    congr 1; push_cast; ring
  have hP0 : 0 < W ^ (-(2 * Dst)) := Real.rpow_pos_of_pos hW0 _
  have hD0 : 0 ≤ W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) := Real.rpow_nonneg hW0.le _
  calc 4 * (2 * N * (16 * N) ^ 6) * L ^ d * ((1 - v) / (1 - w)) ^ 3 *
        W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1))
      = (8 * 16 ^ 6) * (N ^ 7 * L ^ d) * ((1 - v) / (1 - w)) ^ 3 *
        W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) := by ring
    _ ≤ (8 * 16 ^ 6) * (N ^ 7 * N) * W ^ (3 * d) *
        W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) := by
        gcongr
    _ = (8 * 16 ^ 6) * N ^ 8 * W ^ (3 * d) * W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) := by ring
    _ ≤ (8 * 16 ^ 6) * W ^ (8 / 𝔠) * W ^ (3 * d) *
        W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1)) := by
        gcongr
    _ = (8 * 16 ^ 6) * (W ^ (8 / 𝔠) * W ^ (3 * d) *
        W ^ (-(2 * Dst + 8 / 𝔠 + 3 * (d : ℝ) + 1))) := by ring
    _ = (8 * 16 ^ 6 * W⁻¹) * W ^ (-(2 * Dst)) := by rw [hexp]; ring
    _ ≤ 1 * W ^ (-(2 * Dst)) := by
        refine mul_le_mul_of_nonneg_right ?_ hP0.le
        rw [← div_eq_mul_inv, div_le_one hW0]
        exact hW27
    _ = W ^ (-(2 * Dst)) := one_mul _

end FarAbsorb

/-! ## 5. Generic real-number and tensor lemmas for target 4 -/

section Generic

/-- `C₇ = 18 e^{8d+2}`, the constant of `tailtoTailSq_kernel`. -/
private noncomputable def pfStep5_C7 (d : ℕ) : ℝ := 18 * Real.exp (8 * (d : ℝ) + 2)

/-- The total constant of the closure: `7 c + 3 + c d + √(2 C₇ d) + 2 √C₇`, `c = C + 1`. -/
private noncomputable def pfStep5_Ctot (d : ℕ) (Cu : ℝ) : ℝ :=
  7 * (Cu + 1) + 3 + (Cu + 1) * d + Real.sqrt (2 * pfStep5_C7 d * d) + 2 * Real.sqrt (pfStep5_C7 d)

/-- The constant `C` of `pfStep5Alg_ugenSum'`. -/
private noncomputable def pfStep5_Cu (d : ℕ) (hd : 3 ≤ d) : ℝ :=
  Classical.choose (pfStep5Alg_ugenSum' d hd)

private theorem pfStep5_C7_pos (d : ℕ) : 0 < pfStep5_C7 d := by
  unfold pfStep5_C7; positivity

private theorem pfStep5_Ctot_ge {d : ℕ} {Cu : ℝ} (hCu : 0 < Cu) : 4 ≤ pfStep5_Ctot d Cu := by
  unfold pfStep5_Ctot
  have := Real.sqrt_nonneg (2 * pfStep5_C7 d * d)
  have := Real.sqrt_nonneg (pfStep5_C7 d)
  have : (0 : ℝ) ≤ (Cu + 1) * d := by positivity
  linarith

/-- `T_{x,D'} ≤ T_{x,D}` for `D ≤ D'`, `W ≥ 1`. -/
private theorem pfStep5_tailTD_mono {d : ℕ} {W x D D' r : ℝ} (hW : 1 ≤ W) (h : D ≤ D') :
    tailTD d W x D' r ≤ tailTD d W x D r := by
  unfold tailTD
  have := Real.rpow_le_rpow_of_exponent_le hW (neg_le_neg h)
  linarith

/-- `W^{-D} ≤ T_{x,D}`. -/
private theorem pfStep5_tailTD_floor {d : ℕ} {W x D r : ℝ} :
    W ^ (-D) ≤ tailTD d W x D r := by
  unfold tailTD
  have : 0 ≤ ((W ^ d * |1 - x|)⁻¹) ^ 2 * Real.exp (-Real.sqrt r) := by positivity
  linarith

/-- `T_{x,D} ≥ 0`. -/
private theorem pfStep5_tailTD_nonneg {d : ℕ} {W x D r : ℝ} (hW : 0 ≤ W) : 0 ≤ tailTD d W x D r :=
  (Real.rpow_nonneg hW _).trans pfStep5_tailTD_floor

/-- The three left Riemann sums on the grid `u_{j+1} = u_j + Δ`. -/
private theorem pfStep5_riemann_grid (k : ℕ) (u : ℕ → ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1) :
    Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ 2 ≤ (1 - u k)⁻¹ ∧
    Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ) ≤ 2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) ∧
    Δ * ∑ j ∈ Finset.range k, (1 - u j)⁻¹ ≤ Real.log ((1 - u 0) / (1 - u k)) := by
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  obtain ⟨h1, h2, h3⟩ := pfStep5Alg_riemann k u hu0 hmono huk
  have hd : ∀ j, u (j + 1) - u j = Δ := fun j => by rw [hu j]; ring
  simp only [hd] at h1 h2 h3
  rw [← Finset.mul_sum] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The numerical bounds at the last grid time: with `y ≤ (g²)⁻¹`, `m = g² W^d ≥ 1`:
`(W^d)⁻¹ y ≤ m^{-1/4}`, `((W^d)⁻¹ y)^{1/2} ≤ m^{-1/2} ≤ m^{-1/4}`. -/
private theorem pfStep5_num_m (d : ℕ) {g W y : ℝ} (hg : 0 < g) (hW : 1 < W)
    (hm : 1 ≤ g ^ 2 * W ^ d) (hy : y ≤ (g ^ 2)⁻¹) (hy0 : 0 ≤ y) :
    (W ^ d)⁻¹ * y ≤ (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) ∧
    ((W ^ d)⁻¹ * y) ^ (1 / 2 : ℝ) ≤ (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) ∧
    (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) ≤ (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) := by
  set m : ℝ := g ^ 2 * W ^ d with hmdef
  have hW0 : 0 < W := by linarith
  have hm0 : 0 < m := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have hWd : 0 < W ^ d := pow_pos hW0 d
  have hwy : (W ^ d)⁻¹ * y ≤ m ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, hmdef, mul_inv]
    calc (W ^ d)⁻¹ * y ≤ (W ^ d)⁻¹ * (g ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hy (inv_nonneg.2 hWd.le)
      _ = (g ^ 2)⁻¹ * (W ^ d)⁻¹ := by ring
  have h14 : m ^ (-1 : ℝ) ≤ m ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  have h12 : m ^ (-(1 / 2 : ℝ)) ≤ m ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hm (by norm_num)
  refine ⟨hwy.trans h14, ?_, h12⟩
  have hnn : 0 ≤ (W ^ d)⁻¹ * y := mul_nonneg (inv_nonneg.2 hWd.le) hy0
  calc ((W ^ d)⁻¹ * y) ^ (1 / 2 : ℝ) ≤ (m ^ (-1 : ℝ)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hnn hwy (by norm_num)
    _ = m ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_mul hm0.le]; congr 1; norm_num

/-- `log((1-u₀)/(1-u_k)) ≤ d log W` when `1 - u_k ≥ g²`, `g² W^d ≥ 1`, `0 ≤ u₀ ≤ u_k`. -/
private theorem pfStep5_log_le (d : ℕ) {g W u0 uk : ℝ} (hg : 0 < g) (hW : 1 < W)
    (hm : 1 ≤ g ^ 2 * W ^ d) (hu0 : 0 ≤ u0) (hu0k : u0 ≤ uk) (hgk : g ^ 2 ≤ 1 - uk) :
    Real.log ((1 - u0) / (1 - uk)) ≤ d * Real.log W := by
  have hW0 : 0 < W := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have h1k : 0 < 1 - uk := lt_of_lt_of_le hg2 hgk
  have h10 : 0 < 1 - u0 := by linarith
  have hq0 : 0 < (1 - u0) / (1 - uk) := div_pos h10 h1k
  have hle : (1 - u0) / (1 - uk) ≤ W ^ d := by
    have h1 : (1 - u0) / (1 - uk) ≤ 1 / (1 - uk) := div_le_div_of_nonneg_right (by linarith) h1k.le
    have h2 : 1 / (1 - uk) ≤ 1 / g ^ 2 := one_div_le_one_div_of_le hg2 hgk
    have h3 : 1 / g ^ 2 ≤ W ^ d := by
      rw [div_le_iff₀ hg2]; nlinarith
    linarith
  calc Real.log ((1 - u0) / (1 - uk)) ≤ Real.log (W ^ d) := Real.log_le_log hq0 hle
    _ = d * Real.log W := by rw [Real.log_pow]

/-- The drift sums: `Δ Σ_{j<k} (W^{2ε₀} (W^d)⁻¹ y_j² + y_j + W^{3ε₀/2} ((W^d)⁻¹)^{1/2} y_j^{3/2}) ≤
d log W + 3 X`, `y_j = (1-u_j)⁻¹`, `X = W^{2ε₀} (g² W^d)^{-1/4}`. -/
private theorem pfStep5_drift_sum (d : ℕ) (k : ℕ) (u : ℕ → ℝ) (Δ g W ε₀ : ℝ) (hg : 0 < g)
    (hW : 1 < W) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0) (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1)
    (hgk : g ^ 2 ≤ 1 - u k) (hm : 1 ≤ g ^ 2 * W ^ d) (hε₀ : 0 ≤ ε₀) :
    Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ +
        W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) ≤
      d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨r1, r2, r3⟩ := pfStep5_riemann_grid k u Δ hΔ hu0 hu huk
  have hW0 : 0 < W := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have h1k : 0 < 1 - u k := lt_of_lt_of_le hg2 hgk
  have hy : (1 - u k)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 hgk
  have hy0 : 0 ≤ (1 - u k)⁻¹ := inv_nonneg.2 h1k.le
  obtain ⟨n1, n2, n3⟩ := pfStep5_num_m d hg hW hm hy hy0
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hu0k : u 0 ≤ u k := by
    have : Monotone u := monotone_nat_of_le_succ hmono
    exact this (Nat.zero_le k)
  have hlog := pfStep5_log_le d hg hW hm hu0 hu0k hgk
  have hWd : 0 < W ^ d := pow_pos hW0 d
  have hA0 : 0 ≤ W ^ (2 * ε₀) := Real.rpow_nonneg hW0.le _
  have hB0 : 0 ≤ W ^ (3 * ε₀ / 2) := Real.rpow_nonneg hW0.le _
  have hBA : W ^ (3 * ε₀ / 2) ≤ W ^ (2 * ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)
  have hX0 : 0 ≤ (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by positivity) _
  -- split the sum
  have hsplit : Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ +
        W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) =
      W ^ (2 * ε₀) * (W ^ d)⁻¹ * (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ 2) +
      Δ * ∑ j ∈ Finset.range k, (1 - u j)⁻¹ +
      W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
        (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsplit]
  have e1 : W ^ (2 * ε₀) * (W ^ d)⁻¹ * (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ 2) ≤
      W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) := by
    calc W ^ (2 * ε₀) * (W ^ d)⁻¹ * (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ 2)
        ≤ W ^ (2 * ε₀) * (W ^ d)⁻¹ * (1 - u k)⁻¹ :=
          mul_le_mul_of_nonneg_left r1 (mul_nonneg hA0 (inv_nonneg.2 hWd.le))
      _ = W ^ (2 * ε₀) * ((W ^ d)⁻¹ * (1 - u k)⁻¹) := by ring
      _ ≤ W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left n1 hA0
  have e3 : W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
      (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) ≤
      2 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) := by
    have hwh : ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) ≤
        (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.mul_rpow (inv_nonneg.2 hWd.le) hy0]
      exact n2.trans n3
    have hw0 : 0 ≤ ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (inv_nonneg.2 hWd.le) _
    calc W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))
        ≤ W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * (2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left r2 (mul_nonneg hB0 hw0)
      _ = 2 * (W ^ (3 * ε₀ / 2) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ))) := by
          ring
      _ ≤ 2 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc W ^ (3 * ε₀ / 2) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ))
              ≤ W ^ (3 * ε₀ / 2) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_left hwh hB0
            _ ≤ W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) :=
                mul_le_mul_of_nonneg_right hBA hX0
  linarith

/-- The martingale sums: `Δ Σ_{j<k} (y_j + W^{3ε₀} ((W^d)⁻¹)^{1/2} y_j^{3/2}) ≤ d log W + 2 X²`. -/
private theorem pfStep5_mart_sum (d : ℕ) (k : ℕ) (u : ℕ → ℝ) (Δ g W ε₀ : ℝ) (hg : 0 < g)
    (hW : 1 < W) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0) (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1)
    (hgk : g ^ 2 ≤ 1 - u k) (hm : 1 ≤ g ^ 2 * W ^ d) (hε₀ : 0 ≤ ε₀) :
    Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹ +
        W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) ≤
      d * Real.log W + 2 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) ^ 2 := by
  obtain ⟨r1, r2, r3⟩ := pfStep5_riemann_grid k u Δ hΔ hu0 hu huk
  have hW0 : 0 < W := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have h1k : 0 < 1 - u k := lt_of_lt_of_le hg2 hgk
  have hy : (1 - u k)⁻¹ ≤ (g ^ 2)⁻¹ := inv_anti₀ hg2 hgk
  have hy0 : 0 ≤ (1 - u k)⁻¹ := inv_nonneg.2 h1k.le
  obtain ⟨n1, n2, n3⟩ := pfStep5_num_m d hg hW hm hy hy0
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hu0k : u 0 ≤ u k := by
    have : Monotone u := monotone_nat_of_le_succ hmono
    exact this (Nat.zero_le k)
  have hlog := pfStep5_log_le d hg hW hm hu0 hu0k hgk
  have hWd : 0 < W ^ d := pow_pos hW0 d
  have hB0 : 0 ≤ W ^ (3 * ε₀) := Real.rpow_nonneg hW0.le _
  have hBA : W ^ (3 * ε₀) ≤ W ^ (4 * ε₀) :=
    Real.rpow_le_rpow_of_exponent_le hW.le (by linarith)
  have hsplit : Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹ +
        W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) =
      Δ * ∑ j ∈ Finset.range k, (1 - u j)⁻¹ +
      W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
        (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hsplit]
  have hw0 : 0 ≤ ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (inv_nonneg.2 hWd.le) _
  have hwh : ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ) ≤
      (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (inv_nonneg.2 hWd.le) hy0]
    exact n2
  have hX2 : (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) ^ 2 =
      W ^ (4 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (W ^ (2 * ε₀)), ← Real.rpow_mul hW0.le,
      ← Real.rpow_natCast ((g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))), ← Real.rpow_mul (by positivity)]
    congr 2 <;> push_cast <;> ring
  rw [hX2]
  have e3 : W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
      (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) ≤
      2 * (W ^ (4 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ))) := by
    have hX0 : 0 ≤ (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))
        ≤ W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * (2 * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left r2 (mul_nonneg hB0 hw0)
      _ = 2 * (W ^ (3 * ε₀) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ))) := by
          ring
      _ ≤ 2 * (W ^ (4 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc W ^ (3 * ε₀) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u k)⁻¹) ^ (1 / 2 : ℝ))
              ≤ W ^ (3 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hwh hB0
            _ ≤ W ^ (4 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right hBA hX0
  linarith

/-- The polynomial inequality behind the martingale term. -/
private theorem pfStep5_Zineq {C7 Q Λ X r₁ r₂ d : ℝ} (hd : 0 ≤ d) (hC7 : 0 ≤ C7) (hQ : 1 ≤ Q)
    (hΛ : 1 ≤ Λ) (hX : 0 ≤ X) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (h1 : r₁ ^ 2 = 2 * C7 * d)
    (h2 : r₂ ^ 2 = C7) :
    2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2 ≤ Q * (r₁ * Λ + 2 * r₂ * X + 2) ^ 2 := by
  have hQ0 : 0 ≤ Q := by linarith
  have ha : 0 ≤ r₁ * Λ := mul_nonneg hr₁ (by linarith)
  have hb : 0 ≤ 2 * r₂ * X := by positivity
  have e : (r₁ * Λ + 2 * r₂ * X + 2) ^ 2 = (r₁ * Λ) ^ 2 + (2 * r₂ * X) ^ 2 + 4 +
      (2 * (r₁ * Λ) * (2 * r₂ * X) + 4 * (r₁ * Λ) + 4 * (2 * r₂ * X)) := by ring
  have hc : 0 ≤ 2 * (r₁ * Λ) * (2 * r₂ * X) + 4 * (r₁ * Λ) + 4 * (2 * r₂ * X) := by positivity
  have h3 : (r₁ * Λ) ^ 2 = 2 * C7 * d * Λ ^ 2 := by rw [mul_pow, h1]
  have h4 : (2 * r₂ * X) ^ 2 = 4 * C7 * X ^ 2 := by rw [mul_pow, mul_pow, h2]; ring
  have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
  have h5 : 2 * C7 * d * Λ ≤ 2 * C7 * d * Λ ^ 2 := mul_le_mul_of_nonneg_left hΛ2 (by positivity)
  have h6 : Q * (2 * C7 * d * Λ) ≤ Q * (2 * C7 * d * Λ ^ 2) := mul_le_mul_of_nonneg_left h5 hQ0
  have h7 : Q * (r₁ * Λ + 2 * r₂ * X + 2) ^ 2 ≥ Q * (2 * C7 * d * Λ ^ 2 + 4 * C7 * X ^ 2 + 4) := by
    rw [e, h3, h4]
    exact mul_le_mul_of_nonneg_left (by linarith) hQ0
  have h8 : 2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2 =
      Q * (2 * C7 * d * Λ) + Q * (4 * C7 * X ^ 2) + 2 := by ring
  have h9 : Q * (2 * C7 * d * Λ ^ 2 + 4 * C7 * X ^ 2 + 4) =
      Q * (2 * C7 * d * Λ ^ 2) + Q * (4 * C7 * X ^ 2) + 4 * Q := by ring
  linarith

/-- **The martingale term, real part**: from `x_j ≤ (2 C₇ p_j + 1) T²` for the quadratic variations, the
grid sums and `N^{-D_g} ≤ T²`, the tail of conjunct 4 is at most `Q (r₁ log W + 2 r₂ X + 2) T`. -/
private theorem pfStep5_mart_real (d : ℕ) (k : ℕ) (u : ℕ → ℝ) (Δ g W Q ε₀ T q Nm Mn : ℝ)
    (xx : ℕ → ℝ) (hg : 0 < g) (hW : 1 < W) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1) (hgk : g ^ 2 ≤ 1 - u k)
    (hm : 1 ≤ g ^ 2 * W ^ d) (hlog : 4 ≤ Real.log W) (hε₀ : 0 ≤ ε₀) (hQ : 1 ≤ Q) (hT : 0 ≤ T)
    (hNm : Nm ≤ T ^ 2) (hqQ : q ≤ Real.sqrt Q)
    (hx : ∀ j, j < k → xx j ≤ (2 * pfStep5_C7 d * (Q * ((1 - u j)⁻¹ +
        W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2)
    (hMn : Mn ≤ q * (∑ j ∈ Finset.range k, Δ * xx j + Nm) ^ (1 / 2 : ℝ)) :
    Mn ≤ Q * (Real.sqrt (2 * pfStep5_C7 d * d) * Real.log W +
      2 * Real.sqrt (pfStep5_C7 d) * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) + 2) * T := by
  rw [← Real.sqrt_eq_rpow] at hMn
  set C7 : ℝ := pfStep5_C7 d with hC7
  have hC70 : 0 < C7 := pfStep5_C7_pos d
  set X : ℝ := W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) with hXdef
  set Λ : ℝ := Real.log W with hΛdef
  have hΛ : 1 ≤ Λ := by linarith
  have hW0 : 0 < W := by linarith
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg (by positivity) _)
  have hQ0 : 0 < Q := by linarith
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hform : ∀ j, u j = u 0 + j * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hu j, ih]; push_cast; ring
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := hform k
    linarith
  obtain hsum := pfStep5_mart_sum d k u Δ g W ε₀ hg hW hΔ hu0 hu huk hgk hm hε₀
  -- the sum of the quadratic variations
  have hS : ∑ j ∈ Finset.range k, Δ * xx j ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) := by
    calc ∑ j ∈ Finset.range k, Δ * xx j
        ≤ ∑ j ∈ Finset.range k, Δ * ((2 * C7 * (Q * ((1 - u j)⁻¹ +
            W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2) :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hx j (Finset.mem_range.1 hj)) hΔ
      _ = T ^ 2 * (2 * C7 * Q * (Δ * ∑ j ∈ Finset.range k, ((1 - u j)⁻¹ +
            W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) +
            (k : ℝ) * Δ) := by
          have e : ∀ j, Δ * ((2 * C7 * (Q * ((1 - u j)⁻¹ +
              W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + 1) * T ^ 2) =
              T ^ 2 * (2 * C7 * Q * (Δ * ((1 - u j)⁻¹ +
              W ^ (3 * ε₀) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) + Δ) :=
            fun j => by ring
          rw [Finset.sum_congr rfl (fun j _ => e j)]
          simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul]
      _ ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg T)
          have := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2 * C7 * Q)
          linarith
  -- the sum plus `Nm`
  have hSN : ∑ j ∈ Finset.range k, Δ * xx j + Nm ≤
      T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) := by
    have e : T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) =
        T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 1) + T ^ 2 := by ring
    rw [e]
    linarith
  set r₁ : ℝ := Real.sqrt (2 * C7 * d) with hr₁
  set r₂ : ℝ := Real.sqrt C7 with hr₂
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr₁sq : r₁ ^ 2 = 2 * C7 * d := Real.sq_sqrt (by positivity)
  have hr₂sq : r₂ ^ 2 = C7 := Real.sq_sqrt hC70.le
  have hr₁0 : 0 ≤ r₁ := Real.sqrt_nonneg _
  have hr₂0 : 0 ≤ r₂ := Real.sqrt_nonneg _
  set s : ℝ := r₁ * Λ + 2 * r₂ * X + 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hZ : 2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2 ≤ Q * s ^ 2 :=
    pfStep5_Zineq hd0 hC70.le hQ hΛ hX0 hr₁0 hr₂0 hr₁sq hr₂sq
  have hsq : Real.sqrt (∑ j ∈ Finset.range k, Δ * xx j + Nm) ≤ T * (Real.sqrt Q * s) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    calc ∑ j ∈ Finset.range k, Δ * xx j + Nm
        ≤ T ^ 2 * (2 * C7 * Q * (d * Λ + 2 * X ^ 2) + 2) := hSN
      _ ≤ T ^ 2 * (Q * s ^ 2) := mul_le_mul_of_nonneg_left hZ (sq_nonneg T)
      _ = (T * (Real.sqrt Q * s)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hQ0.le]
  have hQQ : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0.le
  calc Mn ≤ q * Real.sqrt (∑ j ∈ Finset.range k, Δ * xx j + Nm) := hMn
    _ ≤ Real.sqrt Q * (T * (Real.sqrt Q * s)) :=
        mul_le_mul hqQ hsq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt Q * Real.sqrt Q) * s * T := by ring
    _ = Q * s * T := by rw [hQQ]

/-- The last arithmetic of the assembly: `T₁ + T₂ + T₃ + T₄ ≤ Q C_tot (1 + Λ + X) T̂`. -/
private theorem pfStep5_final_ineq {Q c d Λ X r₁ r₂ Th : ℝ} (hQ : 1 ≤ Q) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hΛ : 0 ≤ Λ) (hX : 0 ≤ X) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (hTh : 0 ≤ Th) :
    4 * Q * c * Th + c * Q * (d * Λ + 3 * X) * Th + Q * (r₁ * Λ + 2 * r₂ * X + 2) * Th + Th ≤
      Q * (7 * c + 3 + c * d + r₁ + 2 * r₂) * (1 + Λ + X) * Th := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : Th ≤ Q * Th := by nlinarith
  have h2 : (7 * c + 3 + c * d + r₁ + 2 * r₂) * (1 + Λ + X) =
      (4 * c + 3 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) +
      ((3 * c + c * d + r₁ + 2 * r₂) + (7 * c + 3 + 2 * r₂) * Λ + (4 * c + 3 + c * d + r₁) * X) := by
    ring
  have h3 : 0 ≤ (3 * c + c * d + r₁ + 2 * r₂) + (7 * c + 3 + 2 * r₂) * Λ +
      (4 * c + 3 + c * d + r₁) * X := by positivity
  have h4 : 4 * Q * c * Th + c * Q * (d * Λ + 3 * X) * Th + Q * (r₁ * Λ + 2 * r₂ * X + 2) * Th =
      Q * Th * (4 * c + 2 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) := by ring
  have h5 : Q * (7 * c + 3 + c * d + r₁ + 2 * r₂) * (1 + Λ + X) * Th =
      Q * Th * ((4 * c + 3 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) +
      ((3 * c + c * d + r₁ + 2 * r₂) + (7 * c + 3 + 2 * r₂) * Λ + (4 * c + 3 + c * d + r₁) * X)) := by
    rw [← h2]; ring
  rw [h5]
  have h6 : 0 ≤ Q * Th := mul_nonneg hQ0 hTh
  have h7 : Q * Th * (4 * c + 2 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) + Th ≤
      Q * Th * ((4 * c + 3 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) +
      ((3 * c + c * d + r₁ + 2 * r₂) + (7 * c + 3 + 2 * r₂) * Λ + (4 * c + 3 + c * d + r₁) * X)) := by
    have : Q * Th * (4 * c + 2 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) + Q * Th ≤
        Q * Th * ((4 * c + 3 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) +
        ((3 * c + c * d + r₁ + 2 * r₂) + (7 * c + 3 + 2 * r₂) * Λ + (4 * c + 3 + c * d + r₁) * X)) := by
      have e : Q * Th * (4 * c + 2 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) + Q * Th =
          Q * Th * (4 * c + 3 + (c * d + r₁) * Λ + (3 * c + 2 * r₂) * X) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by linarith) h6
    linarith
  rw [h4.symm] at h7
  linarith

/-- **The assembly of the pathwise estimate** (Duhamel form, drift, initial term, martingale, remainder): on the
grid `u_{j+1} = u_j + Δ`, `A_k` is dominated by `Q C_tot (1 + log W + X) T̂_k`, `T̂_k = T_{u_k, D_{u_k}}`,
where `D_u = D* + 2 log_W (1-u)`. -/
private theorem pfStep5_assemble {d : ℕ} (hd : 3 ≤ d) (L : ℕ) [NeZero L] (hL : 3 ≤ L)
    (g W E Δ M R Q ε₀ Dst : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d L) → ℂ)
    (hg : 0 < g) (hW : 1 < W) (hE : |E| ≤ 2) (hΔ : 0 ≤ Δ) (hu0 : 0 ≤ u 0)
    (hu : ∀ j, u (j + 1) = u j + Δ) (huk : u k < 1) (hgk : g ^ 2 ≤ 1 - u k)
    (hm : 1 ≤ g ^ 2 * W ^ d) (hQ : 1 ≤ Q) (hε₀ : 0 ≤ ε₀) (hlog : 4 ≤ Real.log W)
    (hA : ∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) (hRem : ∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R)
    (hrec : ∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (ThetaN d L g (fun i' => mSigma E (σ i')) (u i) (A i) b + F i b) + Rem j b + Mart j b)
    (hF : ∀ j, j < k → ∀ b, ‖F j b‖ ≤ Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)) *
        tailTD d W (u j) (PfStep5Grid_level W Dst (u j)) (zdistInf d L (b 0 - b 1) : ℝ))
    (hI : ∀ b, ‖A 0 b‖ ≤ 4 * Q *
        tailTD d W (u 0) (PfStep5Grid_level W Dst (u 0)) (zdistInf d L (b 0 - b 1) : ℝ))
    (hMt : ∀ a, ‖∑ j ∈ Finset.range k,
        RBM.Ind.Ugen d L g E σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
        Q * (Real.sqrt (2 * pfStep5_C7 d * d) * Real.log W + 2 * Real.sqrt (pfStep5_C7 d) *
          (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) + 2) *
        tailTD d W (u k) (PfStep5Grid_level W Dst (u k)) (zdistInf d L (a 0 - a 1) : ℝ))
    (hRm : 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) ≤ W ^ (-Dst)) :
    ∀ a, ‖A k a‖ ≤ Q * pfStep5_Ctot d (pfStep5_Cu d hd) *
      (1 + Real.log W + W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) *
      tailTD d W (u k) (PfStep5Grid_level W Dst (u k)) (zdistInf d L (a 0 - a 1) : ℝ) := by
  intro a
  obtain ⟨hCu, HU⟩ := Classical.choose_spec (pfStep5Alg_ugenSum' d hd)
  have hCuC : Classical.choose (pfStep5Alg_ugenSum' d hd) = pfStep5_Cu d hd := rfl
  rw [hCuC] at hCu HU
  set Cu : ℝ := pfStep5_Cu d hd with hCudef
  have hW0 : 0 < W := by linarith
  have hg2 : 0 < g ^ 2 := by positivity
  have h1k : 0 < 1 - u k := lt_of_lt_of_le hg2 hgk
  have hmono : ∀ j, u j ≤ u (j + 1) := fun j => by rw [hu j]; linarith
  have hMono : Monotone u := monotone_nat_of_le_succ hmono
  have hunn : ∀ j, 0 ≤ u j := fun j => hu0.trans (hMono (Nat.zero_le j))
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => lt_of_le_of_lt (hMono hj) huk
  have hlvl := pfStep5Grid_level d W Dst
  -- `T̂_k`
  set Th : ℝ := tailTD d W (u k) (PfStep5Grid_level W Dst (u k)) (zdistInf d L (a 0 - a 1) : ℝ)
    with hThdef
  have hTh0 : 0 ≤ Th := pfStep5_tailTD_nonneg hW0.le
  have hTfl : W ^ (-(PfStep5Grid_level W Dst (u k))) ≤ Th := pfStep5_tailTD_floor
  -- the level at the time `u_j` against the last time
  have hlev : ∀ j, j ≤ k → PfStep5Grid_level W Dst (u k) ≤ PfStep5Grid_level W Dst (u j) ∧
      ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j))) =
        W ^ (-(PfStep5Grid_level W Dst (u k))) := by
    intro j hj
    have hj1 : 0 < 1 - u j := by linarith [hlt j hj]
    obtain ⟨-, h2, -, -⟩ := hlvl (u j) (u k) hW (hMono hj) huk
    obtain ⟨hjj, -, -, -⟩ := hlvl (u j) (u j) hW le_rfl (hlt j hj)
    obtain ⟨hjk, -, -, -⟩ := hlvl (u j) (u k) hW (hMono hj) huk
    refine ⟨h2, ?_⟩
    rw [hjj, hjk]
    field_simp
  -- (1) the initial term
  have hT1 : ‖RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a‖ ≤ 4 * Q * (Cu + 1) * Th := by
    have h := HU L hL g W E (fun _ => PfStep5Grid_level W Dst (u 0)) hg hW0 hE σ 1
      (fun j => if j = 0 then u 0 else u k) (fun _ => 1) (fun _ => 4 * Q) (fun _ => A 0)
      (by simpa using hu0) (fun j => by
        by_cases hj : j = 0
        · subst hj; simpa using hMono (Nat.zero_le k)
        · simp [hj])
      (by simpa using huk) (by simpa using hgk) (fun _ => zero_le_one) (fun j hj b => by
        have : j = 0 := by omega
        subst this
        simpa using hI b) a
    simp only [Finset.sum_range_one, Nat.one_ne_zero, ↓reduceIte, one_mul,
      Complex.ofReal_one] at h
    obtain ⟨hl1, hl2⟩ := hlev 0 (Nat.zero_le k)
    have hmono1 : tailTD d W (u k) (PfStep5Grid_level W Dst (u 0)) (zdistInf d L (a 0 - a 1) : ℝ) ≤ Th :=
      pfStep5_tailTD_mono hW.le hl1
    have hmono2 : ((1 - u 0) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u 0))) ≤ Th :=
      hl2.le.trans hTfl
    calc ‖RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a‖
        ≤ 4 * Q * (Cu * tailTD d W (u k) (PfStep5Grid_level W Dst (u 0))
            (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - u 0) / (1 - u k)) ^ 2 *
            W ^ (-(PfStep5Grid_level W Dst (u 0)))) := h
      _ ≤ 4 * Q * (Cu * Th + Th) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          exact add_le_add (mul_le_mul_of_nonneg_left hmono1 hCu.le) hmono2
      _ = 4 * Q * (Cu + 1) * Th := by ring
  -- (2) the drift term
  have hT2 : ‖∑ j ∈ Finset.range k, (Δ : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (F j) a‖ ≤
      (Cu + 1) * Q * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th := by
    have h := HU L hL g W E (fun j => PfStep5Grid_level W Dst (u j)) hg hW0 hE σ k u
      (fun _ => Δ) (fun j => Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ +
        W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) F hu0 hmono
      huk hgk (fun _ => hΔ) hF a
    refine h.trans ?_
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hWd : 0 < W ^ d := pow_pos hW0 d
    have hterm : ∀ j ∈ Finset.range k, Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) *
        (Cu * tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d L (a 0 - a 1) : ℝ) +
          ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j)))) ≤
        Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) * ((Cu + 1) * Th) := by
      intro j hj
      have hjk : j ≤ k := (Finset.mem_range.1 hj).le
      obtain ⟨hl1, hl2⟩ := hlev j hjk
      have hmono1 : tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d L (a 0 - a 1) : ℝ) ≤
          Th := pfStep5_tailTD_mono hW.le hl1
      have hmono2 : ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j))) ≤ Th :=
        hl2.le.trans hTfl
      have hpos : 0 ≤ Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
          (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) := by
        have : 0 < 1 - u j := by linarith [hlt j hjk]
        positivity
      refine mul_le_mul_of_nonneg_left ?_ hpos
      calc Cu * tailTD d W (u k) (PfStep5Grid_level W Dst (u j)) (zdistInf d L (a 0 - a 1) : ℝ) +
          ((1 - u j) / (1 - u k)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst (u j)))
          ≤ Cu * Th + Th := add_le_add (mul_le_mul_of_nonneg_left hmono1 hCu.le) hmono2
        _ = (Cu + 1) * Th := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hds := pfStep5_drift_sum d k u Δ g W ε₀ hg hW hΔ hu0 hu huk hgk hm hε₀
    have e : ∑ j ∈ Finset.range k, Δ * (Q * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u j)⁻¹) ^ 2 +
        (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) * ((Cu + 1) * Th) =
        Q * ((Cu + 1) * Th) * (Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ *
          ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    have hQT : 0 ≤ Q * ((Cu + 1) * Th) := by positivity
    calc Q * ((Cu + 1) * Th) * (Δ * ∑ j ∈ Finset.range k, (W ^ (2 * ε₀) * (W ^ d)⁻¹ *
          ((1 - u j)⁻¹) ^ 2 + (1 - u j)⁻¹ + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u j)⁻¹) ^ (3 / 2 : ℝ)))
        ≤ Q * ((Cu + 1) * Th) * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hds hQT
      _ = (Cu + 1) * Q * (d * Real.log W + 3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th := by
          ring
  -- (3) the remainder
  have hT4 : 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) ≤ Th := by
    refine hRm.trans ?_
    obtain ⟨-, -, h3, -⟩ := hlvl (u k) (u k) hW le_rfl huk
    exact (Real.rpow_le_rpow_of_exponent_le hW.le (neg_le_neg (h3 (hunn k)))).trans hTfl
  -- the Duhamel form and the triangle inequality
  have hdu := pfStep5Grid_duhamel d L hL g E Δ M R σ k u A F Rem Mart hE hΔ hu0 hu huk hA hRem
    hrec a
  have hMt' := hMt a
  set U0 := RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a with hU0
  set S1 := ∑ j ∈ Finset.range k, (Δ : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (F j) a with hS1
  set S2 := ∑ j ∈ Finset.range k,
    RBM.Ind.Ugen d L g E σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a with hS2
  have htri : ‖A k a‖ ≤ ‖A k a - U0 - S1 - S2‖ + ‖U0‖ + ‖S1‖ + ‖S2‖ := by
    have e : A k a = (A k a - U0 - S1 - S2) + U0 + S1 + S2 := by ring
    calc ‖A k a‖ = ‖(A k a - U0 - S1 - S2) + U0 + S1 + S2‖ := by rw [← e]
      _ ≤ ‖(A k a - U0 - S1 - S2) + U0 + S1‖ + ‖S2‖ := norm_add_le _ _
      _ ≤ (‖(A k a - U0 - S1 - S2) + U0‖ + ‖S1‖) + ‖S2‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ((‖A k a - U0 - S1 - S2‖ + ‖U0‖) + ‖S1‖) + ‖S2‖ := by
          gcongr; exact norm_add_le _ _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hX0 : 0 ≤ W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hW0.le _) (Real.rpow_nonneg (by positivity) _)
  have hfin := pfStep5_final_ineq (Q := Q) (c := Cu + 1) (d := d) (Λ := Real.log W)
    (X := W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) (r₁ := Real.sqrt (2 * pfStep5_C7 d * d))
    (r₂ := Real.sqrt (pfStep5_C7 d)) (Th := Th) hQ (by linarith) hd0 (by linarith) hX0
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hTh0
  unfold pfStep5_Ctot
  calc ‖A k a‖ ≤ ‖A k a - U0 - S1 - S2‖ + ‖U0‖ + ‖S1‖ + ‖S2‖ := htri
    _ ≤ Th + 4 * Q * (Cu + 1) * Th + (Cu + 1) * Q * (d * Real.log W +
        3 * (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ)))) * Th +
        Q * (Real.sqrt (2 * pfStep5_C7 d * d) * Real.log W + 2 * Real.sqrt (pfStep5_C7 d) *
          (W ^ (2 * ε₀) * (g ^ 2 * W ^ d) ^ (-(1 / 4 : ℝ))) + 2) * Th :=
        by linarith
    _ ≤ _ := by linarith

end Generic

/-! ## 6. Per-time bounds at a grid time (from the good event and `J♯ ≤ W^{ε₀}`) -/

section PerTime

variable {d : ℕ}

/-- `J^p ≤ W^{ε₀ p}` for `0 ≤ J ≤ W^{ε₀}`, `p ≥ 0`. -/
private theorem pfStep5_rpow_le {J W ε₀ p : ℝ} (hW : 0 < W) (hJ0 : 0 ≤ J) (hJ : J ≤ W ^ ε₀)
    (hp : 0 ≤ p) : J ^ p ≤ W ^ (ε₀ * p) := by
  calc J ^ p ≤ (W ^ ε₀) ^ p := Real.rpow_le_rpow hJ0 hJ hp
    _ = W ^ (ε₀ * p) := by rw [← Real.rpow_mul hW.le]

/-- `y · (w y)^{1/2} = w^{1/2} y^{3/2}`, `y > 0`, `w ≥ 0`. -/
private theorem pfStep5_y_three_half {y w : ℝ} (hy : 0 < y) (hw : 0 ≤ w) :
    y * (w * y) ^ (1 / 2 : ℝ) = w ^ (1 / 2 : ℝ) * y ^ (3 / 2 : ℝ) := by
  have h : y ^ (3 / 2 : ℝ) = y * y ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  rw [Real.mul_rpow hw hy.le, h]; ring

/-- **The per-time bounds at a grid time**: on the good event at the crude control and with
`J♯ ≤ W^{ε₀}`, the drift term and the quadratic variation of the flow matrix `H_u = √u X(ω')` are
dominated, with `y = (1-u)⁻¹`, `w = (W^d)⁻¹`, by `N^τ (W^{2ε₀} w y² + y + W^{3ε₀/2} w^{1/2} y^{3/2}) T` and
`N^τ (y + W^{3ε₀} w^{1/2} y^{3/2}) T²` (near pairs). -/
private theorem pfStep5_pertime (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ)
    {u D τ τ' ε₀ : ℝ} (ω' : sz.SeqΩ) (hτ' : 0 ≤ τ') (hτ : 0 < τ) (hε₀ : 0 ≤ ε₀) (hε₀h : ε₀ ≤ 1 / 2)
    (hQW : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ))
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ)) (hE : |E n| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hlam : 0 < sz.lam n) (hlamu : sz.lam n ^ 2 ≤ 1 - u)
    (hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D)
    (hkell : ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D))
    (hloss : lossE2wG d (sz.L n) (sz.W n) (32 * ((sz.size n : ℕ) : ℝ) ^ τ') 1 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hω : ω' ∈ lemDecCalEPrec_good sz E D (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε₀) τ' n u)
    (hJ : LemDecCalELip_Jsharp sz E D n u ω' ≤ ((sz.W n : ℕ) : ℝ) ^ ε₀) :
    (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STelklkM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b) +
          STegtM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 + (1 - u)⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) * STtailTD sz n u D b) ∧
    (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n (E n) u (sz.seqHflow n u ω') σ b b'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - u)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) * STtailTD sz n u D b ^ 2) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  have h1u : 0 < 1 - u := by linarith
  have hy0 : 0 < (1 - u)⁻¹ := inv_pos.2 h1u
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  have hw0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.2 hWd.le
  have habs : |1 - u| = 1 - u := abs_of_pos h1u
  have hR1 : ∀ b : Fin 2 → Zd d (sz.L n), lemDecCalEPrec_R1 sz n D u b =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b := by
    intro b
    unfold lemDecCalEPrec_R1
    rw [habs, mul_inv]; ring
  have hR2 : ∀ b : Fin 2 → Zd d (sz.L n), lemDecCalEPrec_R2 sz n D u b =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b := by
    intro b
    unfold lemDecCalEPrec_R2
    rw [habs, mul_inv, pfStep5_y_three_half hy0 hw0]
  have hR3 : ∀ b : Fin 2 → Zd d (sz.L n), lemDecCalEPrec_R3 sz n D u b =
      ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b ^ 2 := by
    intro b
    unfold lemDecCalEPrec_R3
    rw [habs, mul_inv, pfStep5_y_three_half hy0 hw0]
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hJst1 : 1 ≤ (fun (m : ℕ) (_ _ : ℝ) => ((sz.W m : ℕ) : ℝ) ^ ε₀) n u D := by
    change 1 ≤ W ^ ε₀
    exact Real.one_le_rpow hW1 hε₀
  have hJstW : (fun (m : ℕ) (_ _ : ℝ) => ((sz.W m : ℕ) : ℝ) ^ ε₀) n u D ≤ W ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hW1 hε₀h
  have hB := lemDecCalEPrec_goodDet hd sz n E (fun m _ _ => ((sz.W m : ℕ) : ℝ) ^ ε₀) ω' hτ' hτ
    hJst1 hJstW hQW hN1 hE hu0 hu1 hlam hlamu hA hlog hfl hkell hloss hω
  obtain ⟨B1, B2, B3⟩ := hB
  set J : ℝ := LemDecCalELip_Jsharp sz E D n u ω' with hJdef
  have hJ1 : 1 ≤ J := (LemDecCalELip_Jsharp_basic sz E D n u ω').1
  have hJ0 : 0 ≤ J := by linarith
  have hT0 : ∀ b : Fin 2 → Zd d (sz.L n), 0 ≤ STtailTD sz n u D b := fun b =>
    (LemDecCalELip_tail_pos sz n u D b).le
  have hQ0 : 0 ≤ N ^ τ := Real.rpow_nonneg hN0.le _
  have hJ2 : J ^ (2 : ℝ) ≤ W ^ (2 * ε₀) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 2)
    rwa [mul_comm] at this
  have hJ32 : J ^ (3 / 2 : ℝ) ≤ W ^ (3 * ε₀ / 2) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rwa [show ε₀ * (3 / 2 : ℝ) = 3 * ε₀ / 2 by ring] at this
  have hJ3 : J ^ (3 : ℝ) ≤ W ^ (3 * ε₀) := by
    have := pfStep5_rpow_le hW0 hJ0 hJ (by norm_num : (0 : ℝ) ≤ 3)
    rwa [mul_comm] at this
  have hR0₂ : ∀ b : Fin 2 → Zd d (sz.L n), lemDecCalEPrec_R2₀ sz n D u b ≤ (1 - u)⁻¹ * STtailTD sz n u D b := by
    intro b
    unfold lemDecCalEPrec_R2₀
    have : (if ((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    calc (1 - u)⁻¹ * (if ((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) *
          STtailTD sz n u D b ≤ (1 - u)⁻¹ * 1 * STtailTD sz n u D b :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hy0.le) (hT0 b)
      _ = (1 - u)⁻¹ * STtailTD sz n u D b := by ring
  have hR0₃ : ∀ b : Fin 2 → Zd d (sz.L n), lemDecCalEPrec_R3₀ sz n D u b ≤ (1 - u)⁻¹ * STtailTD sz n u D b ^ 2 := by
    intro b
    unfold lemDecCalEPrec_R3₀
    have : (if ((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ≤ 4 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    calc (1 - u)⁻¹ * (if ((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ≤ 4 * Real.log W ^ (3 / 2 : ℝ) then (1 : ℝ) else 0) *
          STtailTD sz n u D b ^ 2 ≤ (1 - u)⁻¹ * 1 * STtailTD sz n u D b ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hy0.le) (sq_nonneg _)
      _ = (1 - u)⁻¹ * STtailTD sz n u D b ^ 2 := by ring
  refine ⟨fun σ b => ?_, fun σ b b' hnear => ?_⟩
  · -- drift
    have e1 := B1 σ b
    have e2 := B2 σ b
    have c1 : ‖STELKLK sz n (E n) u σ b ω'‖ ≤ N ^ τ * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 *
        STtailTD sz n u D b) := by
      refine e1.trans (mul_le_mul_of_nonneg_left ?_ hQ0)
      rw [zero_add, hR1 b]
      have hT := hT0 b
      calc J ^ (2 : ℝ) * ((W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b)
          ≤ W ^ (2 * ε₀) * ((W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b) :=
            mul_le_mul_of_nonneg_right hJ2 (by positivity)
        _ = W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b := by ring
    have c2 : ‖STEGt sz n (E n) u σ b ω'‖ ≤ N ^ τ * ((1 - u)⁻¹ * STtailTD sz n u D b +
        W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) * ((1 - u)⁻¹) ^ (3 / 2 : ℝ) *
          STtailTD sz n u D b) := by
      refine e2.trans (mul_le_mul_of_nonneg_left ?_ hQ0)
      rw [hR2 b]
      have hT := hT0 b
      calc lemDecCalEPrec_R2₀ sz n D u b + J ^ (3 / 2 : ℝ) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b)
          ≤ (1 - u)⁻¹ * STtailTD sz n u D b + W ^ (3 * ε₀ / 2) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b) :=
            add_le_add (hR0₂ b) (mul_le_mul_of_nonneg_right hJ32 (by positivity))
        _ = _ := by ring
    calc ‖STelklkM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b) +
          STegtM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b)‖
        ≤ ‖STelklkM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b)‖ +
          ‖STegtM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b)‖ := norm_add_le _ _
      _ = ‖STELKLK sz n (E n) u σ b ω'‖ + ‖STEGt sz n (E n) u σ b ω'‖ := by
          rw [STELKLK, STEGt, STELKLKM_eq_STelklkM, STEGtM_eq_STegtM]
      _ ≤ N ^ τ * (W ^ (2 * ε₀) * (W ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 * STtailTD sz n u D b) +
          N ^ τ * ((1 - u)⁻¹ * STtailTD sz n u D b + W ^ (3 * ε₀ / 2) * ((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b) := add_le_add c1 c2
      _ = _ := by ring
  · -- quadratic variation
    have e3 := B3 σ b b' hnear
    refine e3.trans ?_
    have hT := hT0 b
    rw [hR3 b]
    calc N ^ τ * (lemDecCalEPrec_R3₀ sz n D u b + J ^ (3 : ℝ) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b ^ 2))
        ≤ N ^ τ * ((1 - u)⁻¹ * STtailTD sz n u D b ^ 2 + W ^ (3 * ε₀) * (((W ^ d)⁻¹) ^ (1 / 2 : ℝ) *
          ((1 - u)⁻¹) ^ (3 / 2 : ℝ) * STtailTD sz n u D b ^ 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hQ0
          exact add_le_add (hR0₃ b) (mul_le_mul_of_nonneg_right hJ3 (by positivity))
      _ = _ := by ring

end PerTime

/-! ## 7. The initial term, the a priori bound, the quadratic variation of a grid time -/

section GridTime

variable {d : ℕ}

/-- `0 ≤ Bctl_u ≤ 2 (W^d (1-u))⁻¹` for `u < 1`. -/
private theorem pfStep5_Bctl_le (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) :
    0 ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ 2 * ((((sz.W n : ℕ) : ℝ) ^ d) * (1 - u))⁻¹ := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    have := sz.three_le_L n
    exact_mod_cast (by omega : 1 ≤ sz.L n)
  have h1u : 0 < 1 - u := by linarith
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos (by linarith) d
  have hLd : 1 ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hLd0 : 0 < ((sz.L n : ℕ) : ℝ) ^ d := by linarith
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos h1u]
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  have hm : (((sz.W n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (1 - u)⁻¹ :=
    mul_inv _ _
  rw [hm]
  set x : ℝ := 1 - u with hx
  have hl2 : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  refine ⟨by positivity, ?_⟩
  have e1 : (sz.lam n ^ 2 + x)⁻¹ ≤ x⁻¹ := inv_anti₀ h1u (by linarith)
  have e2 : (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹ ≤ x⁻¹ := inv_anti₀ h1u (by nlinarith)
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + x)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * x)⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (x⁻¹ + x⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) (inv_nonneg.2 hWd.le)
    _ = 2 * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * x⁻¹) := by ring

/-- The initial bound in the form of the induction: from `STDecayStrong` at `s`, the tail
`Bctl_s² e^{-√r} + W^{-D*} ≤ 4 T_{s,D_s}`, `D_s = D* + 2 log_W (1-s) ≤ D*`. -/
private theorem pfStep5_init_le (sz : Sizes d) (n : ℕ) {s Dst : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (a : Fin 2 → Zd d (sz.L n)) :
    sz.Bctl n s ^ 2 * Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-Dst) ≤
      4 * tailTD d ((sz.W n : ℕ) : ℝ) s (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst s)
        (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := by
  obtain ⟨hB0, hB⟩ := pfStep5_Bctl_le sz n hs1
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := by linarith
  have h1s : 0 < 1 - s := by linarith
  have hB2 : sz.Bctl n s ^ 2 ≤ (2 * ((W ^ d) * (1 - s))⁻¹) ^ 2 := pow_le_pow_left₀ hB0 hB 2
  have hlvl : PfStep5Grid_level W Dst s ≤ Dst :=
    (pfStep5Grid_level d W Dst s s hW le_rfl hs1).2.2.1 hs0
  have hWD : W ^ (-Dst) ≤ W ^ (-(PfStep5Grid_level W Dst s)) :=
    Real.rpow_le_rpow_of_exponent_le hW.le (neg_le_neg hlvl)
  have hexp : Real.exp (-((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) =
      Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
  rw [hexp]
  unfold tailTD
  rw [abs_of_pos h1s]
  have hE0 : 0 ≤ Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) :=
    (Real.exp_pos _).le
  have hq : (2 * ((W ^ d * (1 - s))⁻¹)) ^ 2 = 4 * ((W ^ d * (1 - s))⁻¹) ^ 2 := by ring
  have hWn : 0 ≤ W ^ (-(PfStep5Grid_level W Dst s)) := Real.rpow_nonneg hW0.le _
  have h1 : sz.Bctl n s ^ 2 * Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) ≤
      (4 * ((W ^ d * (1 - s))⁻¹) ^ 2) *
        Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_right (hB2.trans (le_of_eq hq)) hE0
  have h2 : 0 ≤ ((W ^ d * (1 - s))⁻¹) ^ 2 *
      Real.exp (-Real.sqrt ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) := by positivity
  linarith

/-- **The a priori bound** `‖(𝓛-𝒦)^{(2)}_{u,σ,a}(H)‖ ≤ N³` for a Hermitian `H`, `|E| < 2`,
`0 ≤ u < 1`, `η_u ≥ 1/(16 N)`, `1 ≤ lam² W^d`, `lam² ≤ 1 - u`, `N ≥ 257`. -/
private theorem pfStep5_apriori (sz : Sizes d) (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u)
    (hu1 : u < 1) {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    (hH : H.IsHermitian) (hη : 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT E u)
    (hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hlamu : sz.lam n ^ 2 ≤ 1 - u)
    (hN : 257 ≤ ((sz.size n : ℕ) : ℝ)) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ‖STLKM sz n E u H σ a‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hη0 : 0 < etaT E u := etaT_pos hE hu1
  have hinv : (etaT E u)⁻¹ ≤ 16 * N := by
    calc (etaT E u)⁻¹ ≤ (1 / (16 * N))⁻¹ := inv_anti₀ (by positivity) hη
      _ = 16 * N := by rw [one_div, inv_inv]
  have h1 : ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a‖ ≤ (16 * N) ^ 2 := by
    refine (RBM.Ind.norm_loopFine_crudeN sz n hE hH hu1 (by norm_num : 1 ≤ 2) σ a).trans ?_
    exact pow_le_pow_left₀ (inv_nonneg.2 hη0.le) hinv 2
  have h2 : ‖STKloop sz n E u σ a‖ ≤ 1 := by
    refine (lemDecCalEPrec_Kbound sz n hE.le hu0 hu1 σ a).trans ?_
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      exact pow_pos (by linarith) d
    rw [inv_le_one₀ (by nlinarith [sq_nonneg (sz.lam n)])]
    nlinarith
  unfold STLKM STLM
  calc ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a - STKloop sz n E u σ a‖
      ≤ ‖loopFine d (sz.L n) (sz.W n) H (zt E u) σ a‖ + ‖STKloop sz n E u σ a‖ := norm_sub_le _ _
    _ ≤ (16 * N) ^ 2 + 1 := add_le_add h1 h2
    _ ≤ N ^ 3 := by nlinarith

/-- The level facts between two grid times `0 ≤ v ≤ w < 1`: `D_w ≤ D_v`, `D_w ≤ D*`,
`((1-v)/(1-w))² W^{-D_v} = W^{-D_w}`. -/
private theorem pfStep5_lvl {W Dst v w : ℝ} (hW : 1 < W) (hv : 0 ≤ v) (hvw : v ≤ w) (hw : w < 1) :
    PfStep5Grid_level W Dst w ≤ PfStep5Grid_level W Dst v ∧ PfStep5Grid_level W Dst w ≤ Dst ∧
      ((1 - v) / (1 - w)) ^ 2 * W ^ (-(PfStep5Grid_level W Dst v)) =
        W ^ (-(PfStep5Grid_level W Dst w)) := by
  have hv1 : 0 < 1 - v := by linarith
  have hw1 : 0 < 1 - w := by linarith
  obtain ⟨hvk, hmon, -, -⟩ := pfStep5Grid_level 0 W Dst v w hW hvw hw
  obtain ⟨hvv, -, -, -⟩ := pfStep5Grid_level 0 W Dst v v hW le_rfl (by linarith)
  obtain ⟨-, -, hup, -⟩ := pfStep5Grid_level 0 W Dst w w hW le_rfl hw
  refine ⟨hmon, hup (by linarith), ?_⟩
  rw [hvv, hvk]
  field_simp

/-- `W^{-2D*} ≤ T̂_w²` for `0 ≤ w < 1`, `T̂_w = T_{w, D_w}`. -/
private theorem pfStep5_W2_le {W Dst w r : ℝ} (hW : 1 < W) (hw0 : 0 ≤ w) (hw1 : w < 1) :
    W ^ (-(2 * Dst)) ≤ tailTD d W w (PfStep5Grid_level W Dst w) r ^ 2 := by
  have hW0 : 0 < W := by linarith
  have hlv : PfStep5Grid_level W Dst w ≤ Dst := (pfStep5Grid_level d W Dst w w hW le_rfl hw1).2.2.1 hw0
  have h1 : W ^ (-Dst) ≤ W ^ (-(PfStep5Grid_level W Dst w)) :=
    Real.rpow_le_rpow_of_exponent_le hW.le (neg_le_neg hlv)
  have h2 : W ^ (-(2 * Dst)) = (W ^ (-Dst)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  rw [h2]
  exact pow_le_pow_left₀ (Real.rpow_nonneg hW0.le _) (h1.trans pfStep5_tailTD_floor) 2

/-- **The quadratic variation at a grid time** (`tailtoTailSq_kernel` at `(v, w)`, `D = D_v`, the far
remainder absorbed by `hfar`): `‖𝒰𝒰̄ ∘ (ℰ⊗ℰ)^{(2)}_{v}(H)‖ ≤ (2 C₇ p + 1) Th_w²`, `Th_w = T_{w, D_w}`. -/
private theorem pfStep5_xx (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) {E v w Dst D₂ p : ℝ}
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (hE : |E| ≤ 2) (hv : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1)
    (hlam : sz.lam n ^ 2 ≤ 1 - w) (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hW : 1 < ((sz.W n : ℕ) : ℝ)) (hp : 0 ≤ p)
    (hH1 : ∀ b b' : Fin 2 → Zd d (sz.L n),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E v H σ b b'‖ ≤
        p * STtailTD sz n v (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst v) b ^ 2)
    (hH2 : ∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeM sz n E v H σ b b'‖ ≤
      2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6)
    (hH3 : ∀ x y : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) w) ≤
        (zdistInf d (sz.L n) (x - y) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂))
    (hfar : 4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) *
        ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))) :
    ‖STeeUM sz n E v w H σ a‖ ≤
      (2 * pfStep5_C7 d * p + 1) *
        STtailTD sz n w (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst w) a ^ 2 := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 ≤ N := by linarith
  have hY0 : 0 ≤ 2 * N * (16 * N) ^ 6 := by positivity
  have hk := tailtoTailSq_kernel sz hd n E v w (PfStep5Grid_level W Dst v) D₂ p
    (2 * N * (16 * N) ^ 6) H σ hE hv hvw hw1 hlam hlog hp hY0 hH1 hH2 hH3 a
  obtain ⟨hl1, hl2, hl3⟩ := pfStep5_lvl (Dst := Dst) hW hv hvw hw1
  set Th : ℝ := STtailTD sz n w (PfStep5Grid_level W Dst w) a with hTh
  have hT0 : 0 ≤ Th := (LemDecCalELip_tail_pos sz n w _ a).le
  have hT1 : STtailTD sz n w (PfStep5Grid_level W Dst v) a ≤ Th :=
    pfStep5Alg_tailAnti sz n w _ _ a hl1
  have hT1' : 0 ≤ STtailTD sz n w (PfStep5Grid_level W Dst v) a := (LemDecCalELip_tail_pos sz n w _ a).le
  have hfl : W ^ (-(PfStep5Grid_level W Dst w)) ≤ Th := lemDecCalEPrec_tail_ge sz n w _ a
  have hW0 : 0 < W := by linarith
  have hWn : 0 ≤ W ^ (-(PfStep5Grid_level W Dst w)) := Real.rpow_nonneg hW0.le _
  have hρ4 : ((1 - v) / (1 - w)) ^ 4 * (W ^ (-(PfStep5Grid_level W Dst v))) ^ 2 =
      (W ^ (-(PfStep5Grid_level W Dst w))) ^ 2 := by
    rw [← hl3]; ring
  have hfar' : W ^ (-(2 * Dst)) ≤ Th ^ 2 := by
    have h1 : W ^ (-Dst) ≤ W ^ (-(PfStep5Grid_level W Dst w)) :=
      Real.rpow_le_rpow_of_exponent_le hW.le (neg_le_neg hl2)
    have h2 : W ^ (-(2 * Dst)) = (W ^ (-Dst)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
    rw [h2]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hW0.le _) (h1.trans hfl) 2
  have hC7 : 0 ≤ pfStep5_C7 d := (pfStep5_C7_pos d).le
  have hmain : 18 * Real.exp (8 * (d : ℝ) + 2) * p *
        (STtailTD sz n w (PfStep5Grid_level W Dst v) a ^ 2 +
          ((1 - v) / (1 - w)) ^ 4 * (W ^ (-(PfStep5Grid_level W Dst v))) ^ 2) ≤
      pfStep5_C7 d * p * (2 * Th ^ 2) := by
    rw [hρ4]
    have e : 18 * Real.exp (8 * (d : ℝ) + 2) = pfStep5_C7 d := rfl
    rw [e]
    have h1 : STtailTD sz n w (PfStep5Grid_level W Dst v) a ^ 2 ≤ Th ^ 2 :=
      pow_le_pow_left₀ hT1' hT1 2
    have h2 : (W ^ (-(PfStep5Grid_level W Dst w))) ^ 2 ≤ Th ^ 2 := pow_le_pow_left₀ hWn hfl 2
    have : 0 ≤ pfStep5_C7 d * p := mul_nonneg hC7 hp
    calc pfStep5_C7 d * p * (STtailTD sz n w (PfStep5Grid_level W Dst v) a ^ 2 +
          (W ^ (-(PfStep5Grid_level W Dst w))) ^ 2)
        ≤ pfStep5_C7 d * p * (Th ^ 2 + Th ^ 2) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) this
      _ = pfStep5_C7 d * p * (2 * Th ^ 2) := by ring
  calc ‖STeeUM sz n E v w H σ a‖ ≤ _ := hk
    _ ≤ pfStep5_C7 d * p * (2 * Th ^ 2) + Th ^ 2 := add_le_add hmain (hfar.trans hfar')
    _ = (2 * pfStep5_C7 d * p + 1) * Th ^ 2 := by ring

end GridTime

/-! ## 8. The per-time facts at a grid time, from the good event at the crude level `D*` -/

section PerJ

variable {d : ℕ}

/-- **The per-time facts at the time `u`** at the level `D_u = D* + 2 log_W (1-u)`: the good event of S5-09 at
the crude control and the level `D*` (`goodProb`), plus `J♯(u, D_u) ≤ W^{ε₀}`, give via `goodStop'` the good
event at the control `W^{ε₀}` and the level `D_u`, and `pfStep5_pertime` the drift and quadratic-variation
bounds at the level `D_u`. -/
private theorem pfStep5_perj (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ)
    {u Dst τ τ' ε₀ : ℝ} (ω' : sz.SeqΩ) (hτ' : 0 ≤ τ') (hτ : 0 < τ) (hε₀ : 0 ≤ ε₀)
    (hε₀h : ε₀ ≤ 1 / 2) (hQW : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ))
    (hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ)) (hE : |E n| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hlam : 0 < sz.lam n) (hlamu : sz.lam n ^ 2 ≤ 1 - u)
    (hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) (hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ))
    (hW : 1 < ((sz.W n : ℕ) : ℝ))
    (hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ)))
    (hkell : ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dst))
    (hloss : lossE2wG d (sz.L n) (sz.W n) (32 * ((sz.size n : ℕ) : ℝ) ^ τ') 1 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2))
    (hgood : ω' ∈ lemDecCalEPrec_good sz E Dst (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') τ' n u)
    (hJ : LemDecCalELip_Jsharp sz E (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u) n u ω' ≤
      ((sz.W n : ℕ) : ℝ) ^ ε₀) :
    (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STelklkM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b) +
          STegtM sz n (E n) u (sz.seqHflow n u ω') (KLloopOf d (sz.L n) σ b)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((1 - u)⁻¹) ^ 2 + (1 - u)⁻¹ +
            ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
              ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) *
          STtailTD sz n u (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u) b) ∧
    (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n (E n) u (sz.seqHflow n u ω') σ b b'‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ *
          ((1 - u)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
            ((1 - u)⁻¹) ^ (3 / 2 : ℝ)) *
          STtailTD sz n u (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u) b ^ 2) := by
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := hW.le
  have hW0 : 0 < ((sz.W n : ℕ) : ℝ) := by linarith
  -- the level `D_u ∈ [D* - 2d, D*]`
  have h1u : 0 < 1 - u := by linarith
  have hlv := pfStep5Grid_level d ((sz.W n : ℕ) : ℝ) Dst u u hW le_rfl hu1
  have hWdl : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ 1 - u := by
    have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
    rw [Real.rpow_neg hW0.le, Real.rpow_natCast]
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.lam n ^ 2 := by
      rw [inv_le_iff_one_le_mul₀' hWd]; nlinarith
    linarith
  have hlow : Dst - 2 * (d : ℝ) ≤ PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u := hlv.2.2.2 hWdl
  have hup : PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u ≤ Dst := hlv.2.2.1 hu0
  have hfl' : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u) :=
    hfl.trans (Real.rpow_le_rpow_of_exponent_le hW1 hlow)
  have hkell' : ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-(PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u)) := fun a b h =>
    (hkell a b h).trans (Real.rpow_le_rpow_of_exponent_le hW1 (neg_le_neg hup))
  have hgood' := pfStep5Alg_goodStop' sz E (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst u) Dst ε₀ τ'
    (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') n u ω' hτ' hN1 hJ hgood
  exact pfStep5_pertime hd sz n E ω' hτ' hτ hε₀ hε₀h hQW hN1 hE hu0 hu1 hlam hlamu hA hlog hfl' hkell'
    hloss hgood' hJ

end PerJ

/-! ## 9. The pathwise induction -/

section Path

variable {d : ℕ}

/-- The numerical and grid facts at one size index `n` used by the pathwise induction (all eventual facts
of the choice of constants, collected). -/
private structure PfStep5Num {d : ℕ} (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ) (s tt : ℕ → ℝ)
    (K : ℕ → ℕ) (ε₀ τ τ' ε' Dst D₂ Dg C₀ : ℝ) : Prop where
  hs0 : 0 ≤ s n
  hstt : s n ≤ tt n
  htt1 : tt n < 1
  hK : K n ≠ 0
  hreg : sz.lam n ^ 2 ≤ 1 - tt n
  hW : 1 < ((sz.W n : ℕ) : ℝ)
  hlam : 0 < sz.lam n
  hA : 1 ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d
  hlog : 4 ≤ Real.log ((sz.W n : ℕ) : ℝ)
  hN257 : 257 ≤ ((sz.size n : ℕ) : ℝ)
  hE : |E n| < 2
  hη : ∀ u : ℝ, u ≤ tt n → 1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (E n) u
  hτ : 0 < τ
  hτ' : 0 ≤ τ'
  hε₀ : 0 < ε₀
  hε₀h : ε₀ ≤ 1 / 2
  hQW : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)
  hε'τ : ((sz.size n : ℕ) : ℝ) ^ ε' ≤ Real.sqrt (((sz.size n : ℕ) : ℝ) ^ τ)
  hfl : (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ))
  hloss : lossE2wG d (sz.L n) (sz.W n) (32 * ((sz.size n : ℕ) : ℝ) ^ τ') 1 ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2)
  hkellD : ∀ u : ℝ, 0 ≤ u → u ≤ tt n → ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dst)
  hkell2 : ∀ u : ℝ, 0 ≤ u → u ≤ tt n → ∀ a b : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) u) ≤
        (zdistInf d (sz.L n) (a - b) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) a b‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)
  hfar : ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz.size n : ℕ) : ℝ) * (16 * ((sz.size n : ℕ) : ℝ)) ^ 6) * ((sz.L n : ℕ) : ℝ) ^ d *
          ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))
  hclos : ((sz.size n : ℕ) : ℝ) ^ τ * (pfStep5_Ctot d (pfStep5_Cu d hd) *
      (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
        (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) < ((sz.W n : ℕ) : ℝ) ^ ε₀
  hNDg : ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * Dst))
  hRm : 64 * (((sz.W n : ℕ) : ℝ) ^ d) ^ 7 * (((sz.size n : ℕ) : ℝ) ^ C₀ *
        Real.sqrt (gridStep s tt K n) + gridStep s tt K n * ((sz.size n : ℕ) : ℝ) ^ 3) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-Dst)

/-- **The pathwise induction** (`(b3)`, correction (c3)): at one size index `n` and one sample `ω` of the grid walk,
if the good events hold at the grid indices, the initial bound, the decomposition of conjunct 1, the remainder
bound of conjunct 2 and the weighted martingale bound of conjunct 4, then `J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` for
every `k ≤ K`: strong induction on `k`, the step by the Duhamel form (`pfStep5Grid_duhamel`), the four terms
(`pfStep5_assemble`), `pfStep5_mart_real`, and the closure. -/
private theorem pfStep5_path (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ) (s tt : ℕ → ℝ)
    (K : ℕ → ℕ) (ε₀ τ τ' ε' Dst D₂ Dg C₀ : ℝ)
    (Rem Mart : ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (hnum : PfStep5Num hd sz n E s tt K ε₀ τ τ' ε' Dst D₂ Dg C₀)
    (hG : ∀ j, j ≤ K n → ∀ ω' : sz.SeqΩ, sz.seqHflow n (gridTime s tt K n j) ω' =
      pathH sz s tt K n j ω →
      ω' ∈ lemDecCalEPrec_good sz E Dst (fun m _ D' => ((sz.W m : ℕ) : ℝ) ^ D') τ' n
        (gridTime s tt K n j))
    (hI : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      ‖STgAN sz s tt K n (E n) σ b 0 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
        (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)))
    (hC1 : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      STgAN sz s tt K n (E n) σ b k ω = STgAN sz s tt K n (E n) σ b 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
          STgDriftN sz s tt K n (E n) σ b j ω + Rem (σ, b) k ω + Mart (σ, b) k ω)
    (hC2 : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      ‖Rem (σ, b) k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n))
    (hC4 : ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (k : ℕ), k ≤ K n →
      ‖∑ j ∈ Finset.range k, UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i'))
          (gridTime s tt K n j) (gridTime s tt K n k)
          (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε' *
          (∑ j ∈ Finset.range k, gridStep s tt K n *
            ‖STeeUM sz n (E n) (gridTime s tt K n j) (gridTime s tt K n k)
              (pathH sz s tt K n j ω) σ a‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ)) :
    ∀ k, k ≤ K n → PfStep5Grid_JsharpM sz n (E n)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
      (pathH sz s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀ := by
  obtain ⟨hs0, hstt, htt1, hK, hreg, hW, hlam, hA, hlog, hN257, hE, hη, hτ, hτ', hε₀, hε₀h, hQW, hε'τ, hfl, hloss, hkellD, hkell2, hfar, hclos, hNDg, hRm⟩ := hnum
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
  -- the per-time facts at the grid indices `j < k`
  have hPT : ∀ j, j < k →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STelklkM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) (KLloopOf d (sz.L n) σ b) +
            STegtM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω)
              (KLloopOf d (sz.L n) σ b)‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            (((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
                ((1 - gridTime s tt K n j)⁻¹) ^ 2 + (1 - gridTime s tt K n j)⁻¹ +
              ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀ / 2) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
                ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (gridTime s tt K n j)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n j)) b) ∧
      (∀ (σ : Fin 2 → Bool) (b b' : Fin 2 → Zd d (sz.L n)),
        (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
          Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
        ‖STeeM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) σ b b'‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ τ *
            ((1 - gridTime s tt K n j)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (3 * ε₀) *
              ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ) *
                ((1 - gridTime s tt K n j)⁻¹) ^ (3 / 2 : ℝ)) *
            STtailTD sz n (gridTime s tt K n j)
              (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n j)) b ^ 2) := by
    intro j hj
    have hjK : j ≤ K n := by omega
    obtain ⟨ω', hω'⟩ := pfStep5_realize sz s tt K n j ω hs0 hstt
    have hJj := ih j hj hjK
    have hJ' : LemDecCalELip_Jsharp sz E
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n j)) n (gridTime s tt K n j) ω' ≤
        ((sz.W n : ℕ) : ℝ) ^ ε₀ := by
      rw [pfStep5Grid_Jsharp sz E _ n _ ω', hω']
      exact hJj.le
    have h := pfStep5_perj hd sz n E ω' hτ' hτ hε₀.le hε₀h hQW hN1 hE (hunn j hjK) (hu1 j hjK)
      hlam (hlamj j hjK) hA hlog hW hfl (hkellD _ (hunn j hjK) (hult j hjK)) hloss
      (hG j hjK ω' hω') hJ'
    rw [hω'] at h
    exact h
  -- the conclusion at `k`
  have hhuk := hu1 k hk
  have hlk := hlamj k hk
  have hQ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.one_le_rpow hN1 hτ.le
  have hQ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by linarith
  have hs1 : s n < 1 := lt_of_le_of_lt hstt htt1
  unfold PfStep5Grid_JsharpM
  refine max_lt (Real.one_lt_rpow hW hε₀) ?_
  refine (Finset.sup'_lt_iff _).2 ?_
  rintro ⟨σ, a⟩ -
  have hT : 0 < STtailTD sz n (gridTime s tt K n k)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a :=
    LemDecCalELip_tail_pos sz n _ _ a
  rw [div_lt_iff₀ hT]
  -- the hypotheses of the assembly, for this `σ`
  have hAbnd : ∀ j, j ≤ k → ∀ b : Fin 2 → Zd d (sz.L n),
      ‖STgAN sz s tt K n (E n) σ b j ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    intro j hj b
    have hjK : j ≤ K n := hj.trans hk
    have h := pfStep5_apriori sz n hE (hunn j hjK) (hu1 j hjK)
      (pathH_isHermitian sz s tt K n j ω) (hη _ (hult j hjK)) hA (hlamj j hjK) hN257 σ b
    have e : STgAN sz s tt K n (E n) σ b j ω =
        STLKM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) σ b :=
      (STLKM_eq_STLKIM sz n _ _ _ σ b).symm
    rw [e]
    exact h
  have hrec : ∀ j, j ≤ k → ∀ b : Fin 2 → Zd d (sz.L n),
      STgAN sz s tt K n (E n) σ b j ω = STgAN sz s tt K n (E n) σ b 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ i ∈ Finset.range j,
          (ThetaN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (σ i')) (gridTime s tt K n i)
              (fun b => STgAN sz s tt K n (E n) σ b i ω) b +
            (STelklkM sz n (E n) (gridTime s tt K n i) (pathH sz s tt K n i ω)
                (KLloopOf d (sz.L n) σ b) +
              STegtM sz n (E n) (gridTime s tt K n i) (pathH sz s tt K n i ω)
                (KLloopOf d (sz.L n) σ b))) + Rem (σ, b) j ω + Mart (σ, b) j ω := by
    intro j hj b
    have h := hC1 σ b j (hj.trans hk)
    simp only [STgDriftN, Finset.Icc_eq_empty_of_lt (by norm_num : (2 : ℕ) < 3), Finset.sum_empty,
      add_zero] at h
    simp only [h, add_assoc, Finset.sum_add_distrib, mul_add]
    rfl
  have hI' : ∀ b : Fin 2 → Zd d (sz.L n), ‖STgAN sz s tt K n (E n) σ b 0 ω‖ ≤
      4 * ((sz.size n : ℕ) : ℝ) ^ τ * tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n 0)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n 0))
        (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := by
    intro b
    rw [hu00]
    calc ‖STgAN sz s tt K n (E n) σ b 0 ω‖
        ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (sz.Bctl n (s n) ^ 2 *
            Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)) := hI σ b
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (4 * tailTD d ((sz.W n : ℕ) : ℝ) (s n)
            (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (s n)) (zdistInf d (sz.L n) (b 0 - b 1) : ℝ)) :=
          mul_le_mul_of_nonneg_left (pfStep5_init_le sz n hs0 hs1 hW b) hQ0
      _ = 4 * ((sz.size n : ℕ) : ℝ) ^ τ * tailTD d ((sz.W n : ℕ) : ℝ) (s n)
            (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (s n)) (zdistInf d (sz.L n) (b 0 - b 1) : ℝ) := by
          ring
  have hMt : ∀ a' : Fin 2 → Zd d (sz.L n), ‖∑ j ∈ Finset.range k,
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s tt K n j) (gridTime s tt K n k)
        (fun b => Mart (σ, b) (j + 1) ω - Mart (σ, b) j ω) a'‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * (Real.sqrt (2 * pfStep5_C7 d * d) *
        Real.log ((sz.W n : ℕ) : ℝ) + 2 * Real.sqrt (pfStep5_C7 d) *
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
    have hx : ∀ j, j < k → ‖STeeUM sz n (E n) (gridTime s tt K n j) (gridTime s tt K n k)
        (pathH sz s tt K n j ω) σ a'‖ ≤ (2 * pfStep5_C7 d * (((sz.size n : ℕ) : ℝ) ^ τ *
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
      have hH2 : ∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeM sz n (E n) (gridTime s tt K n j)
          (pathH sz s tt K n j ω) σ b b'‖ ≤ 2 * ((sz.size n : ℕ) : ℝ) *
            (16 * ((sz.size n : ℕ) : ℝ)) ^ 6 := by
        intro b b'
        have h := RBM.Ind.difRep2_norm_STeeM_le_N sz n hE (hu1 j hjK)
          (pathH_isHermitian sz s tt K n j ω) (hη _ (hult j hjK)) σ b b'
        norm_num at h
        exact h
      exact pfStep5_xx hd sz n (pathH sz s tt K n j ω) σ a' hE.le (hunn j hjK) (hmono j k hj.le)
        hhuk hlk hlog hW hp ((hPT j hj).2 σ) hH2 (hkell2 _ (hunn k hk) (hult k hk))
        (hfar _ _ (hunn j hjK) (hmono j k hj.le) hlk)
    exact pfStep5_mart_real d k (gridTime s tt K n) (gridStep s tt K n) (sz.lam n)
      ((sz.W n : ℕ) : ℝ) (((sz.size n : ℕ) : ℝ) ^ τ) ε₀ _ (((sz.size n : ℕ) : ℝ) ^ ε')
      (((sz.size n : ℕ) : ℝ) ^ (-Dg)) _ (fun j => ‖STeeUM sz n (E n) (gridTime s tt K n j)
        (gridTime s tt K n k) (pathH sz s tt K n j ω) σ a'‖) hlam hW hΔ
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
  have hass := pfStep5_assemble hd (sz.L n) (sz.three_le_L n) (sz.lam n) ((sz.W n : ℕ) : ℝ) (E n)
    (gridStep s tt K n) (((sz.size n : ℕ) : ℝ) ^ 3)
    (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n)) (((sz.size n : ℕ) : ℝ) ^ τ) ε₀ Dst σ k
    (gridTime s tt K n) (fun j b => STgAN sz s tt K n (E n) σ b j ω)
    (fun j b => STelklkM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω)
        (KLloopOf d (sz.L n) σ b) +
      STegtM sz n (E n) (gridTime s tt K n j) (pathH sz s tt K n j ω) (KLloopOf d (sz.L n) σ b))
    (fun j b => Rem (σ, b) j ω) (fun j b => Mart (σ, b) j ω) hlam hW hE.le hΔ
    (by rw [hu00]; exact hs0) hu hhuk hlk hA hQ hε₀.le hlog hAbnd
    (fun j hj b => hC2 σ b j (hj.trans hk)) hrec (fun j hj b => (hPT j hj).1 σ b) hI' hMt hRm' a
  calc ‖STLKM sz n (E n) (gridTime s tt K n k) (pathH sz s tt K n k ω) σ a‖
      = ‖STgAN sz s tt K n (E n) σ a k ω‖ := by rw [STgAN, STLKM_eq_STLKIM]
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * pfStep5_Ctot d (pfStep5_Cu d hd) *
        (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ))) *
        tailTD d ((sz.W n : ℕ) : ℝ) (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k))
          (zdistInf d (sz.L n) (a 0 - a 1) : ℝ) := hass
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (pfStep5_Ctot d (pfStep5_Cu d hd) *
        (1 + Real.log ((sz.W n : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (2 * ε₀) *
          (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 4 : ℝ)))) *
        STtailTD sz n (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a := by
          unfold STtailTD; ring
    _ < ((sz.W n : ℕ) : ℝ) ^ ε₀ * STtailTD sz n (gridTime s tt K n k)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) a :=
        mul_lt_mul_of_pos_right hclos hT

end Path

/-! ## 10. The union bound at one size index -/

section FixedN

variable {d : ℕ}

/-- The labels `(σ, a)` of the 2-loops. -/
private abbrev pfStep5_Lab (sz : Sizes d) (n : ℕ) : Type :=
  (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))

/-- **The probability at one size index**: the failure event of `∀ k ≤ K, J♯(u_k, D_{u_k})(H_k) < W^{ε₀}` is
contained in the union of the failure of the good events at the `K + 1` grid times (probability
`≤ (K+1) N^{-D₁}`, transfer `ST_pathP_eq_seqP`), of the initial bound, of the martingale tails of the
`#labels` labels, and a null set (conjuncts 1 and 2); off it the pathwise induction applies. -/
private theorem pfStep5_fixedN (hd : 3 ≤ d) (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ) (s tt : ℕ → ℝ)
    (K : ℕ → ℕ) (ε₀ τ τ' ε' Dst D₂ Dg C₀ D₁ D' : ℝ)
    (Rem Mart : pfStep5_Lab sz n → ℕ → PathΩ sz → ℂ)
    (hnum : PfStep5Num hd sz n E s tt K ε₀ τ τ' ε' Dst D₂ Dg C₀)
    (hKD : ((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)))
    (hlabel : (Fintype.card (pfStep5_Lab sz n) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)))
    (hN3 : 3 ≤ ((sz.size n : ℕ) : ℝ))
    (hP1 : ∀ u : ℝ, s n ≤ u → u ≤ tt n →
      sz.seqP (lemDecCalEPrec_good sz E Dst (fun m _ D'' => ((sz.W m : ℕ) : ℝ) ^ D'') τ' n u)ᶜ ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)))
    (hP2 : sz.seqP {ω' | ∃ p : pfStep5_Lab sz n, ((sz.size n : ℕ) : ℝ) ^ τ *
        (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)) <
        ‖STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω') p.1 p.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))))
    (hae : ∀ᵐ ω ∂(pathP sz), ∀ i : pfStep5_Lab sz n,
      (∀ k, k ≤ K n → STgAN sz s tt K n (E n) i.1 i.2 k ω = STgAN sz s tt K n (E n) i.1 i.2 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
          STgDriftN sz s tt K n (E n) i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n)))
    (hP4 : ∀ i : pfStep5_Lab sz n, pathP sz {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s tt K n *
          ‖STeeUM sz n (E n) (gridTime s tt K n j) (gridTime s tt K n k) (pathH sz s tt K n j ω)
            i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i'))
          (gridTime s tt K n j) (gridTime s tt K n k)
          (fun b => Mart (i.1, b) (j + 1) ω - Mart (i.1, b) j ω) i.2‖} ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-Dg))) :
    pathP sz {ω | ∀ k, k ≤ K n → PfStep5Grid_JsharpM sz n (E n)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
      (pathH sz s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ≤
      ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D')) := by
  classical
  have hs0 := hnum.hs0
  have hstt := hnum.hstt
  have hK := hnum.hK
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hu00 : gridTime s tt K n 0 = s n := by simp [gridTime]
  have hmem : ∀ j, j ≤ K n → gridTime s tt K n j ∈ Set.Icc (s n) (tt n) := fun j hj =>
    ST_gridTime_mem s tt K n j hstt hK hj
  -- the measurable sets of the good events
  choose S hSm hSiff using fun j : ℕ => pfStep5_goodMeas sz E Dst
    (fun m _ D'' => ((sz.W m : ℕ) : ℝ) ^ D'') τ' n (gridTime s tt K n j)
  -- the initial set
  set S0 : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) :=
    {H | ∃ p : pfStep5_Lab sz n, ((sz.size n : ℕ) : ℝ) ^ τ *
        (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKM sz n (E n) (s n) H p.1 p.2‖} with hS0
  have hS0m : MeasurableSet S0 := by
    have : S0 = ⋃ p : pfStep5_Lab sz n, {H | ((sz.size n : ℕ) : ℝ) ^ τ *
        (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dst)) < ‖STLKM sz n (E n) (s n) H p.1 p.2‖} := by
      ext H; simp [hS0]
    rw [this]
    exact MeasurableSet.iUnion fun p => measurableSet_lt measurable_const
      (STLKM_measurable sz n (E n) (s n) p.1 p.2).norm
  -- the four bad events
  set E1 : Set (PathΩ sz) := ⋃ j ∈ Finset.range (K n + 1), {ω | pathH sz s tt K n j ω ∈ (S j)ᶜ}
    with hE1def
  set E2 : Set (PathΩ sz) := {ω | pathH sz s tt K n 0 ω ∈ S0} with hE2def
  set E4 : Set (PathΩ sz) := ⋃ i : pfStep5_Lab sz n, {ω | ∃ k, k ≤ K n ∧
      ((sz.size n : ℕ) : ℝ) ^ ε' * (∑ j ∈ Finset.range k, gridStep s tt K n *
          ‖STeeUM sz n (E n) (gridTime s tt K n j) (gridTime s tt K n k) (pathH sz s tt K n j ω)
            i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-Dg)) ^ (1 / 2 : ℝ) <
        ‖∑ j ∈ Finset.range k, UN d (sz.L n) (sz.lam n) (fun i' => mSigma (E n) (i.1 i'))
          (gridTime s tt K n j) (gridTime s tt K n k)
          (fun b => Mart (i.1, b) (j + 1) ω - Mart (i.1, b) j ω) i.2‖} with hE4def
  set E3 : Set (PathΩ sz) := {ω | ¬ ∀ i : pfStep5_Lab sz n,
      (∀ k, k ≤ K n → STgAN sz s tt K n (E n) i.1 i.2 k ω = STgAN sz s tt K n (E n) i.1 i.2 0 ω +
        ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
          STgDriftN sz s tt K n (E n) i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
      (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n))}
    with hE3def
  -- the inclusion
  have hsub : {ω | ∀ k, k ≤ K n → PfStep5Grid_JsharpM sz n (E n)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
      (pathH sz s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ ⊆ E1 ∪ E2 ∪ E4 ∪ E3 := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨⟨h1, h2⟩, h4⟩, h3⟩ := hnot
    refine hω ?_
    have hG : ∀ j, j ≤ K n → ∀ ω' : sz.SeqΩ, sz.seqHflow n (gridTime s tt K n j) ω' =
        pathH sz s tt K n j ω →
        ω' ∈ lemDecCalEPrec_good sz E Dst (fun m _ D'' => ((sz.W m : ℕ) : ℝ) ^ D'') τ' n
          (gridTime s tt K n j) := by
      intro j hj ω' hω'
      rw [hSiff j ω', hω']
      by_contra hcon
      exact h1 (by
        simp only [hE1def, Set.mem_iUnion, Set.mem_ofPred_eq]
        exact ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), hcon⟩)
    have hI : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
        ‖STgAN sz s tt K n (E n) σ b 0 ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst)) := by
      intro σ b
      have h : ¬ ((((sz.size n : ℕ) : ℝ) ^ τ *
          (sz.Bctl n (s n) ^ 2 * Real.exp (-((zdistInf d (sz.L n) (b 0 - b 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dst))) < ‖STLKM sz n (E n) (s n) (pathH sz s tt K n 0 ω) σ b‖) := by
        intro hlt
        exact h2 ⟨(σ, b), hlt⟩
      have e : STgAN sz s tt K n (E n) σ b 0 ω =
          STLKM sz n (E n) (s n) (pathH sz s tt K n 0 ω) σ b := by
        rw [← hu00]; exact (STLKM_eq_STLKIM sz n _ _ _ σ b).symm
      rw [e]
      exact not_lt.1 h
    have h3' : ∀ i : pfStep5_Lab sz n,
        (∀ k, k ≤ K n → STgAN sz s tt K n (E n) i.1 i.2 k ω = STgAN sz s tt K n (E n) i.1 i.2 0 ω +
          ((gridStep s tt K n : ℝ) : ℂ) * ∑ j ∈ Finset.range k,
            STgDriftN sz s tt K n (E n) i.1 i.2 j ω + Rem i k ω + Mart i k ω) ∧
        (∀ k, k ≤ K n → ‖Rem i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s tt K n)) := by
      by_contra hcon
      exact h3 hcon
    refine pfStep5_path hd sz n E s tt K ε₀ τ τ' ε' Dst D₂ Dg C₀ Rem Mart ω hnum hG hI
      (fun σ b k hk => (h3' (σ, b)).1 k hk) (fun σ b k hk => (h3' (σ, b)).2 k hk)
      (fun σ a k hk => ?_)
    by_contra hcon
    refine h4 ?_
    simp only [hE4def, Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨(σ, a), k, hk, not_le.1 hcon⟩
  -- the probabilities of the four events
  have hE1 : pathP sz E1 ≤ ENNReal.ofReal (((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.range (K n + 1), pathP sz {ω | pathH sz s tt K n j ω ∈ (S j)ᶜ} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D₁)) := by
      intro j hj
      have hjK : j ≤ K n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [ST_pathP_eq_seqP sz s tt K n j hs0 hstt hK (hSm j).compl]
      have hset : {ω' : sz.SeqΩ | sz.seqHflow n (gridTime s tt K n j) ω' ∈ (S j)ᶜ} =
          (lemDecCalEPrec_good sz E Dst (fun m _ D'' => ((sz.W m : ℕ) : ℝ) ^ D'') τ' n
            (gridTime s tt K n j))ᶜ := by
        ext ω'
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hSiff j ω']
      rw [hset]
      exact hP1 _ (hmem j hjK).1 (hmem j hjK).2
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one]
    simp
  have hE2 : pathP sz E2 ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) := by
    rw [hE2def, ST_pathP_eq_seqP sz s tt K n 0 hs0 hstt hK hS0m]
    simp only [hu00]
    exact hP2
  have hE4 : pathP sz E4 ≤ ENNReal.ofReal ((Fintype.card (pfStep5_Lab sz n) : ℝ) *
      ((sz.size n : ℕ) : ℝ) ^ (-Dg)) := by
    refine (measure_iUnion_fintype_le _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hP4 i).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  have hE3 : pathP sz E3 = 0 := by
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
  calc pathP sz {ω | ∀ k, k ≤ K n → PfStep5Grid_JsharpM sz n (E n)
          (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s tt K n k)) (gridTime s tt K n k)
          (pathH sz s tt K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ
      ≤ pathP sz (E1 ∪ E2 ∪ E4 ∪ E3) := measure_mono hsub
    _ ≤ pathP sz E1 + pathP sz E2 + pathP sz E4 + pathP sz E3 := by
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        refine (measure_union_le _ _).trans (add_le_add ?_ le_rfl)
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (((K n : ℝ) + 1) * ((sz.size n : ℕ) : ℝ) ^ (-D₁)) +
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(D' + 1))) +
        ENNReal.ofReal ((Fintype.card (pfStep5_Lab sz n) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg)) + 0 := by
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

/-! ## 11. Numerical facts of the choice of constants -/

section Consts

variable {d : ℕ}

/-- `(L^d W^{6d})² ≤ W^{D*-2d}` from `N^𝔠 ≤ W` (`L^d ≤ N ≤ W^{1/𝔠}`) when `2/𝔠 + 12 d ≤ D* - 2d`. -/
private theorem pfStep5_fl (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) {𝔠 Dst : ℝ} (h𝔠 : 0 < 𝔠)
    (hBW : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ))
    (hDst : 2 / 𝔠 + 12 * (d : ℝ) ≤ Dst - 2 * (d : ℝ)) :
    (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤
      ((sz.W n : ℕ) : ℝ) ^ (Dst - 2 * (d : ℝ)) := by
  obtain ⟨hW1, hL1, hNe, hLN, hWdN, hWN, hN1⟩ := pfStep5_sizes sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  set L : ℝ := ((sz.L n : ℕ) : ℝ) with hLdef
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hNW : N ≤ W ^ (1 / 𝔠) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hBW (by positivity : (0 : ℝ) ≤ 1 / 𝔠)
    rw [← Real.rpow_mul hN0.le, mul_one_div_cancel h𝔠.ne', Real.rpow_one] at h
    exact h
  have hLd : 0 ≤ L ^ d := by positivity
  have h1 : L ^ d * W ^ (6 * d) ≤ W ^ (1 / 𝔠) * W ^ (6 * d) :=
    mul_le_mul_of_nonneg_right (hLN.trans hNW) (by positivity)
  have h2 : (L ^ d * W ^ (6 * d)) ^ 2 ≤ (W ^ (1 / 𝔠) * W ^ (6 * d)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (W ^ (1 / 𝔠) * W ^ (6 * d)) ^ 2 = W ^ (2 / 𝔠 + 12 * (d : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (W ^ (1 / 𝔠)), ← Real.rpow_mul hW0.le,
      ← Real.rpow_natCast (W ^ (6 * d)), ← Real.rpow_natCast W (6 * d), ← Real.rpow_mul hW0.le,
      ← Real.rpow_add hW0]
    congr 1; push_cast; ring
  rw [h3] at h2
  exact h2.trans (Real.rpow_le_rpow_of_exponent_le hW1 hDst)

/-- The remainder of the Duhamel form: `64 (W^d)^7 (N^{C₀} √Δ + Δ N³) ≤ W^{-D*}` for `Δ ≤ N^{-C_R}`,
`C_R = 2 (C₀ + D* + 14)`, `N ≥ 3`. -/
private theorem pfStep5_Rm (sz : Sizes d) (n : ℕ) (hd : 1 ≤ d) {Dst C₀ Δ : ℝ} (hDst : 0 ≤ Dst)
    (hC₀ : 0 ≤ C₀) (hΔ : 0 ≤ Δ) (hΔN : Δ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(2 * (C₀ + Dst + 14))))
    (hN : 3 ≤ ((sz.size n : ℕ) : ℝ)) :
    64 * (((sz.W n : ℕ) : ℝ) ^ d) ^ 7 * (((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt Δ +
      Δ * ((sz.size n : ℕ) : ℝ) ^ 3) ≤ ((sz.W n : ℕ) : ℝ) ^ (-Dst) := by
  obtain ⟨hW1, hL1, hNe, hLN, hWdN, hWN, hN1⟩ := pfStep5_sizes sz n hd
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hW0 : 0 < W := by linarith
  have hN0 : 0 < N := by linarith
  have hN1' : (1 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt Δ ≤ N ^ (-(C₀ + Dst + 14)) := by
    calc Real.sqrt Δ ≤ Real.sqrt (N ^ (-(2 * (C₀ + Dst + 14)))) := Real.sqrt_le_sqrt hΔN
      _ = N ^ (-(C₀ + Dst + 14)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN0.le]; congr 1; ring
  have hW7 : (W ^ d) ^ 7 ≤ N ^ 7 := pow_le_pow_left₀ (by positivity) hWdN 7
  have hNC : N ^ C₀ * N ^ (-(C₀ + Dst + 14)) = N ^ (-(Dst + 14)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hΔ3 : Δ * N ^ 3 ≤ N ^ (-(Dst + 14)) := by
    have h1 : Δ * N ^ 3 ≤ N ^ (-(2 * (C₀ + Dst + 14))) * N ^ 3 :=
      mul_le_mul_of_nonneg_right hΔN (by positivity)
    have h2 : N ^ (-(2 * (C₀ + Dst + 14))) * N ^ 3 = N ^ (-(2 * (C₀ + Dst + 14)) + 3) := by
      rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN0]; norm_num
    rw [h2] at h1
    exact h1.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by linarith))
  have hsum : N ^ C₀ * Real.sqrt Δ + Δ * N ^ 3 ≤ 2 * N ^ (-(Dst + 14)) := by
    have := mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le C₀)
    linarith
  have h7 : N ^ (7 : ℕ) * N ^ (-(Dst + 14)) = N ^ (-Dst) * N ^ (-(7 : ℝ)) := by
    rw [← Real.rpow_natCast N 7, ← Real.rpow_add hN0, ← Real.rpow_add hN0]
    congr 1; push_cast; ring
  have h7' : N ^ (-(7 : ℝ)) = (N ^ (7 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hN0.le]; norm_cast
  have h128 : 128 * (N ^ (7 : ℕ))⁻¹ ≤ 1 := by
    have h1 : (N ^ (7 : ℕ))⁻¹ ≤ ((3 : ℝ) ^ (7 : ℕ))⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hN 7)
    have h2 : 128 * ((3 : ℝ) ^ (7 : ℕ))⁻¹ ≤ 1 := by norm_num
    nlinarith
  have hNW : N ^ (-Dst) ≤ W ^ (-Dst) := Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)
  have hE1 : 0 ≤ N ^ (-(Dst + 14)) := Real.rpow_nonneg hN0.le _
  have hA0 : 0 ≤ N ^ C₀ * Real.sqrt Δ + Δ * N ^ 3 := by positivity
  calc 64 * (W ^ d) ^ 7 * (N ^ C₀ * Real.sqrt Δ + Δ * N ^ 3)
      ≤ 64 * N ^ 7 * (2 * N ^ (-(Dst + 14))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hW7 (by norm_num)) hsum hA0 (by positivity)
    _ = 128 * (N ^ (7 : ℕ) * N ^ (-(Dst + 14))) := by ring
    _ = 128 * (N ^ (-Dst) * (N ^ (7 : ℕ))⁻¹) := by rw [h7, h7']
    _ = (128 * (N ^ (7 : ℕ))⁻¹) * N ^ (-Dst) := by ring
    _ ≤ 1 * N ^ (-Dst) := mul_le_mul_of_nonneg_right h128 (Real.rpow_nonneg hN0.le _)
    _ ≤ W ^ (-Dst) := by rw [one_mul]; exact hNW

/-- `(⌈N^c⌉ + 2) N^{-(D'+c+3)} ≤ N^{-(D'+1)}` for `N ≥ 4`, `c ≥ 0`. -/
private theorem pfStep5_hKD {N c D' : ℝ} (hc : 0 ≤ c) (hN : 4 ≤ N) :
    (((⌈N ^ c⌉₊ + 1 : ℕ) : ℝ) + 1) * N ^ (-(D' + c + 3)) ≤ N ^ (-(D' + 1)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNc : 1 ≤ N ^ c := Real.one_le_rpow hN1 hc
  have hceil : (⌈N ^ c⌉₊ : ℝ) < N ^ c + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : (((⌈N ^ c⌉₊ + 1 : ℕ) : ℝ) + 1) ≤ N ^ (c + 2) := by
    have e : N ^ (c + 2) = N ^ c * N ^ (2 : ℕ) := by
      rw [Real.rpow_add hN0, ← Real.rpow_natCast N 2]; norm_num
    rw [e]
    push_cast
    have h4 : (4 : ℝ) ≤ N ^ (2 : ℕ) := by nlinarith
    nlinarith
  have h2 : N ^ (c + 2) * N ^ (-(D' + c + 3)) = N ^ (-(D' + 1)) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  calc (((⌈N ^ c⌉₊ + 1 : ℕ) : ℝ) + 1) * N ^ (-(D' + c + 3))
      ≤ N ^ (c + 2) * N ^ (-(D' + c + 3)) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN0.le _)
    _ = N ^ (-(D' + 1)) := h2

/-- `#labels · N^{-D_g} ≤ N^{-(D'+1)}` for `N ≥ 4`, `D_g ≥ D' + 4`. -/
private theorem pfStep5_hlabel (sz : Sizes d) (n : ℕ) {Dg D' : ℝ}
    (hN : 4 ≤ ((sz.size n : ℕ) : ℝ)) (hDg : D' + 4 ≤ Dg) :
    (Fintype.card (pfStep5_Lab sz n) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(D' + 1)) := by
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := by linarith
  have hcard := lemDecCalEPrec_card_V12 sz n hN
  have h1 : (Fintype.card (pfStep5_Lab sz n) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) ≤
      ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) :=
    mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hN0.le _)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-Dg) =
      ((sz.size n : ℕ) : ℝ) ^ (3 - Dg) := by
    rw [← Real.rpow_add hN0, sub_eq_add_neg]
  refine h1.trans (h2.le.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)))

end Consts

/-! ## 12. Target 4: the stopped loop on the grid -/

section Walk

/-- `η_u ≥ 1/(16 N)` along the flow (`difRep_flow_bounds`, as in `DifREP3.lean:2359-2366`). -/
private theorem pfStep5_eta_lb {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu : u ≤ lemT (z n)) :
    1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (STflowE z n) u := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h := (RBM.Ind.difRep_flow_bounds sz hκ hflow n hu).2.2.1
  refine le_trans ?_ h
  have h2' : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [Real.rpow_neg_one] at h2'
  calc 1 / (16 * ((sz.size n : ℕ) : ℝ)) = ((sz.size n : ℕ) : ℝ)⁻¹ / 16 := by field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 16 := by gcongr

/-- `Δ = (tt - s)/K ≤ N^{-C_R}` when `K ≥ N^{C_R}` and `tt - s ≤ 1`. -/
private theorem pfStep5_gridStep_le {a b K C N : ℝ} (hlen : b - a ≤ 1) (hN : 0 < N)
    (hK : N ^ C ≤ K) : (b - a) / K ≤ N ^ (-C) := by
  have hK1 : 0 < K := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) hK
  calc (b - a) / K ≤ 1 / K := div_le_div_of_nonneg_right hlen hK1.le
    _ ≤ 1 / N ^ C := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN _) hK
    _ = N ^ (-C) := by rw [Real.rpow_neg hN.le, one_div]

/-- **Target 4** (the stopped loop on the grid, `(b1)`-`(b3)`; `𝔠_d := 1/100`, the premise `STConStInd` unused). -/
theorem pfStep5_walk (d : ℕ) : PfStep5_walk_pin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg hKb hKw hLKs hDec hDecS hCon hStep1 hStep2 hLmax hLKU
  obtain ⟨hAdm, hEn, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hAdm' := hAdm
  obtain ⟨h𝔠, -, hsize, hBW, hWO⟩ := hAdm
  have hd1 : 1 ≤ d := by omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  refine ⟨min (𝔡 / 8) (1 / 4), by positivity, fun ε₀ hε₀ hε₀1 D hD => ?_⟩
  have hε₀d : ε₀ < 𝔡 / 4 :=
    lt_of_lt_of_le hε₀1 ((min_le_left _ _).trans (by linarith))
  have hε₀h : ε₀ ≤ 1 / 2 := (hε₀1.trans_le (min_le_right _ _)).le.trans (by norm_num)
  -- (b1) the constants: the closure exponent `τ`, the level `D*`
  have hCu : 0 < pfStep5_Cu d hd := (Classical.choose_spec (pfStep5Alg_ugenSum' d hd)).1
  have hCtot : 4 ≤ pfStep5_Ctot d (pfStep5_Cu d hd) := pfStep5_Ctot_ge hCu
  obtain ⟨τ, hτ, hclos⟩ := pfStep5Alg_closure sz 𝔠 𝔡 hAdm' ε₀ (pfStep5_Ctot d (pfStep5_Cu d hd)) hε₀
    hε₀d (by linarith)
  obtain ⟨Dst, hDstdef⟩ : ∃ Dst : ℝ, Dst = max D (2 / 𝔠 + 12 * (d : ℝ)) + 2 * (d : ℝ) + 1 := ⟨_, rfl⟩
  have hD₀ : (0 : ℝ) < 2 / 𝔠 + 12 * (d : ℝ) := by positivity
  have hDstD : D + 2 * (d : ℝ) ≤ Dst := by
    have := le_max_left D (2 / 𝔠 + 12 * (d : ℝ)); linarith
  have hDst0 : 0 < Dst := by
    have := le_max_left D (2 / 𝔠 + 12 * (d : ℝ)); linarith
  have hDstD₀ : 2 / 𝔠 + 12 * (d : ℝ) ≤ Dst - 2 * (d : ℝ) := by
    have := le_max_right D (2 / 𝔠 + 12 * (d : ℝ)); linarith
  refine ⟨Dst, hDstD, fun tt D' hD' => ?_⟩
  -- the loss exponents
  obtain ⟨τ', hτ'def⟩ : ∃ τ' : ℝ, τ' = min (τ / 24) (1 / (2 * Dst)) := ⟨_, rfl⟩
  have hτ'0 : 0 < τ' := by rw [hτ'def]; exact lt_min (by positivity) (by positivity)
  have h6 : 6 * τ' ≤ τ / 4 := by
    have := min_le_left (τ / 24) (1 / (2 * Dst)); rw [hτ'def]; linarith
  have hDτ : Dst * τ' ≤ 1 / 2 := by
    have h := min_le_right (τ / 24) (1 / (2 * Dst))
    rw [hτ'def]
    calc Dst * min (τ / 24) (1 / (2 * Dst)) ≤ Dst * (1 / (2 * Dst)) :=
          mul_le_mul_of_nonneg_left h hDst0.le
      _ = 1 / 2 := by field_simp
  -- the far exponent `D₂` and the grid exponent
  obtain ⟨D₂, hD₂, hfarEv⟩ := pfStep5_farAbsorb sz 𝔠 𝔡 hAdm' Dst hDst0.le
  obtain ⟨C₀, hC₀, hAt⟩ := RBM.Ind.stGridRepN_holds d hd 2 le_rfl
  obtain ⟨Dg, hDgdef⟩ : ∃ Dg : ℝ, Dg = max D' (2 * Dst) + 4 := ⟨_, rfl⟩
  have hDgD' : D' + 4 ≤ Dg := by have := le_max_left D' (2 * Dst); linarith
  have hDg2 : 2 * Dst ≤ Dg := by have := le_max_right D' (2 * Dst); linarith
  have hDg0 : 0 < Dg := by linarith
  have hstt : ∀ n, s n ≤ ((tt n : TimeIcc s t n) : ℝ) := fun n => (tt n).2.1
  have httt : ∀ n, ((tt n : TimeIcc s t n) : ℝ) ≤ t n := fun n => (tt n).2.2
  have httz : ∀ n, ((tt n : TimeIcc s t n) : ℝ) ≤ lemT (z n) := fun n => (httt n).trans (htz n)
  obtain ⟨CK, hCK, hKex⟩ := hAt κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s (fun m => ((tt m : TimeIcc s t m) : ℝ))
    hs hstt httz Dg hDg0
  obtain ⟨cK, hcKdef⟩ : ∃ cK : ℝ, cK = max CK (2 * (C₀ + Dst + 14)) := ⟨_, rfl⟩
  have hcKCK : CK ≤ cK := by rw [hcKdef]; exact le_max_left _ _
  have hcKCR : 2 * (C₀ + Dst + 14) ≤ cK := by rw [hcKdef]; exact le_max_right _ _
  have hcK0 : 0 ≤ cK := hCK.trans hcKCK
  obtain ⟨Kf, hKfdef⟩ : ∃ Kf : ℕ → ℕ, Kf = fun n => ⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ + 1 := ⟨_, rfl⟩
  refine ⟨Kf, fun n => by rw [hKfdef]; exact Nat.succ_ne_zero _, ?_⟩
  have hKge : ∀ n, ∀ c : ℝ, c ≤ cK → ((sz.size n : ℕ) : ℝ) ^ c ≤ (Kf n : ℝ) := by
    intro n c hc
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    rw [hKfdef]
    push_cast
    calc ((sz.size n : ℕ) : ℝ) ^ c ≤ ((sz.size n : ℕ) : ℝ) ^ cK :=
          Real.rpow_le_rpow_of_exponent_le hN1 hc
      _ ≤ (⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (⌈((sz.size n : ℕ) : ℝ) ^ cK⌉₊ : ℝ) + 1 := by linarith
  obtain ⟨Mart, Rem, h1, h2, -, h4⟩ := hKex Kf (fun n => by rw [hKfdef]; exact Nat.succ_ne_zero _)
    (Filter.Eventually.of_forall fun n => hKge n CK hcKCK)
  -- the eventual facts
  have hnumEv := lemDecCalEPrec_numeric sz hAdm'
  have hgoodProb := pfStep5Alg_goodProb sz (STflowE z) s t Dst hsize
    ((st5_Bctl_le_one sz hκ hε hflow htz).mono fun n hn u => hn (u : ℝ) u.2.2)
    hLKU hStep2.1 hStep2.2.1 hLmax
    (lemDecCalEPrec_gij hd sz z hκ hε hflow hs hst' htz hReg hStep2.1) τ' (D' + cK + 3) hτ'0
    (by positivity)
  have hDecSEv := hDecS Dst hDst0 τ hτ (D' + 1) (by linarith)
  have hkellD := lemDecCalEPrec_kell hd sz z hκ hε hflow htz Dst
  have hkell2 := lemDecCalEPrec_kell hd sz z hκ hε hflow htz D₂
  have hlossEv := lemDecCalEPrec_lossWG_eventually sz hd1 hsize hτ hτ'0.le h6
  have h4' := h4 (τ / 2) (by positivity)
  have hN257Ev := hsize.eventually_ge_atTop 257
  filter_upwards [hnumEv, hN257Ev, hclos, hfarEv, hkellD, hkell2, hlossEv, hBW, hgoodProb, hDecSEv,
    h2, h4'] with n hn1 hN257 hclosn hfarn hkDn hk2n hlossn hBWn hgpn hDSn h2n h4n
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
  have hKn : Kf n ≠ 0 := by rw [hKfdef]; exact Nat.succ_ne_zero _
  have hreg : sz.lam n ^ 2 ≤ 1 - ((tt n : TimeIcc s t n) : ℝ) := by
    have := hReg n; have := httt n; linarith
  have htt1 : ((tt n : TimeIcc s t n) : ℝ) < 1 := (httt n).trans_lt (ht1 n)
  have hfl := pfStep5_fl sz n hd1 h𝔠 hBWn hDstD₀
  have hΔ : 0 ≤ gridStep s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n :=
    div_nonneg (by linarith [hstt n]) (Nat.cast_nonneg _)
  have hΔN : gridStep s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf n ≤
      ((sz.size n : ℕ) : ℝ) ^ (-(2 * (C₀ + Dst + 14))) :=
    pfStep5_gridStep_le (by have := httt n; have := ht1 n; have := hs n; linarith) hN0
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
  have hQW : ((sz.size n : ℕ) : ℝ) ^ τ' ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    refine lemDecCalEPrec_QW sz n hd1 hτ'0.le ?_ hfl
    exact (mul_le_mul_of_nonneg_right (by linarith) hτ'0.le).trans hDτ
  have hη : ∀ u : ℝ, u ≤ ((tt n : TimeIcc s t n) : ℝ) →
      1 / (16 * ((sz.size n : ℕ) : ℝ)) ≤ etaT (STflowE z n) u := fun u hu =>
    pfStep5_eta_lb sz hκ hε hflow n (hu.trans (httz n))
  have hE : |STflowE z n| < 2 := by have := hEn n; linarith
  refine pfStep5_fixedN hd sz n (STflowE z) s (fun m => ((tt m : TimeIcc s t m) : ℝ)) Kf ε₀ τ τ'
    (τ / 2) Dst D₂ Dg C₀ (D' + cK + 3) D' (Rem n) (Mart n)
    ⟨hs n, hstt n, htt1, hKn, hreg, hW1, hlam, hA1, hlog4, hN257, hE, hη, hτ, hτ'0.le, hε₀, hε₀h,
      hQW, hε'τ, hfl, hlossn, fun u hu0 hu => hkDn u hu0 (hu.trans (httt n)),
      fun u hu0 hu => hk2n u hu0 (hu.trans (httt n)), hfarn, hclosn, hNDg, hRm⟩
    ?_ (pfStep5_hlabel sz n (by linarith) hDgD') hN3 ?_ ?_ ?_ ?_
  · -- `(K+1) N^{-D₁} ≤ N^{-(D'+1)}`
    rw [hKfdef]
    have := pfStep5_hKD (N := ((sz.size n : ℕ) : ℝ)) (c := cK) (D' := D') hcK0 (by linarith)
    simpa using this
  · -- the good events (`goodProb`)
    intro u hu1 hu2
    exact hgpn ⟨u, hu1, hu2.trans (httt n)⟩
  · -- the initial bound (`STDecayStrong`)
    refine le_trans (measure_mono ?_) hDSn
    intro ω' hω'
    obtain ⟨p, hp⟩ := hω'
    exact ⟨⟨p, by have := hReg n; have := hst' n; linarith⟩, hp⟩
  · -- conjuncts 1, 2 almost everywhere
    exact ae_all_iff.2 fun i => (h1 n i).and (h2n i)
  · -- conjunct 4 (martingale)
    exact h4n

end Walk

/-! ## 13. Target 5: the endpoint, the sections and the descent `D_u ≥ D` -/

section PT

variable {d : ℕ}

/-- Measurability of the matrix control `J♯` in the fine matrix (a copy of the private lemma of
`Induction/PfStep5Grid.lean:197`, `pfStep5Grid_JsharpM_measurable`). -/
private theorem pfStep5_JsharpM_measurable (sz : Sizes d) (n : ℕ) (E D u : ℝ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      PfStep5Grid_JsharpM sz n E D u H := by
  have hne : (Finset.univ : Finset ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))).Nonempty :=
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have h := Finset.measurable_sup' (s := Finset.univ) hne
    (f := fun (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
        ‖STLKM sz n E u H p.1 p.2‖ / STtailTD sz n u D p.2)
    (fun p _ => ((STLKM_measurable sz n E u p.1 p.2).norm).div_const _)
  have h2 := (measurable_const (a := (1 : ℝ))).max h
  convert h2 using 1
  funext H
  simp [PfStep5Grid_JsharpM, Finset.sup'_apply]

/-- The bad event of `STLK2 ≤ N^τ T_{u,D}` is inside `{J♯(u, D_l) ≥ W^{ε₀}}` when `D ≤ D_l` and
`W^{ε₀} ≤ N^τ` (`STLK2 ≤ J♯ T_{u,D_l} ≤ J♯ T_{u,D}`). -/
private theorem pfStep5_bad_sub (sz : Sizes d) (n : ℕ) (E : ℕ → ℝ) {u D Dl τ ε₀ : ℝ} (hDl : D ≤ Dl)
    (hWN : ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ τ) (ω' : sz.SeqΩ)
    (v : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (hv : ((sz.size n : ℕ) : ℝ) ^ τ * STtailTD sz n u D v.2 < STLK2 sz n (E n) u v.1 v.2 ω') :
    ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ LemDecCalELip_Jsharp sz E Dl n u ω' := by
  have hbasic := LemDecCalELip_Jsharp_basic sz E Dl n u ω'
  have h1 := hbasic.2.1 v.1 v.2
  have h2 : STtailTD sz n u Dl v.2 ≤ STtailTD sz n u D v.2 := pfStep5Alg_tailAnti sz n u D Dl v.2 hDl
  have hT := LemDecCalELip_tail_pos sz n u D v.2
  have hJ0 : 0 ≤ LemDecCalELip_Jsharp sz E Dl n u ω' := by linarith [hbasic.1]
  have h3 : STLK2 sz n (E n) u v.1 v.2 ω' ≤ LemDecCalELip_Jsharp sz E Dl n u ω' * STtailTD sz n u D v.2 :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hJ0)
  have h4 : ((sz.size n : ℕ) : ℝ) ^ τ < LemDecCalELip_Jsharp sz E Dl n u ω' := by
    by_contra hcon
    have := mul_le_mul_of_nonneg_right (not_lt.1 hcon) hT.le
    linarith
  exact hWN.trans h4.le

/-- **Target 5** (endpoint, sections, descent `D_u ≥ D`). -/
theorem pfStep5_PT_of_walk (d : ℕ) : PfStep5_PT_of_walk_pin d := by
  intro sz E s t hs hst ht hReg hWev hwalk D hD
  obtain ⟨ε₁, hε₁, hall⟩ := hwalk
  refine ST_PT_of_sections sz hst _ _ fun tt => ?_
  intro τ hτ D' hD'
  obtain ⟨ε₀, hε₀def⟩ : ∃ ε₀ : ℝ, ε₀ = min ε₁ τ / 2 := ⟨_, rfl⟩
  have hmin : 0 < min ε₁ τ := lt_min hε₁ hτ
  have hε₀ : 0 < ε₀ := by rw [hε₀def]; exact half_pos hmin
  have hε₀1 : ε₀ < ε₁ := by rw [hε₀def]; have := min_le_left ε₁ τ; linarith
  have hε₀τ : ε₀ ≤ τ := by rw [hε₀def]; have := min_le_right ε₁ τ; linarith
  obtain ⟨Dst, hDstD, hK⟩ := hall ε₀ hε₀ hε₀1 D hD
  obtain ⟨K, hK0, hev⟩ := hK tt D' hD'
  filter_upwards [hev, hWev] with n hn hWn
  obtain ⟨hW1, hWd⟩ := hWn
  by_cases hd0 : d = 0
  · -- `N = 1`: the bound `N^{-D'} = 1` is trivial
    have hN : ((sz.size n : ℕ) : ℝ) = 1 := by simp [Sizes.size, hd0]
    rw [hN, Real.one_rpow, ENNReal.ofReal_one]
    exact prob_le_one
  have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
  obtain ⟨-, -, -, -, -, hWN, hN1⟩ := pfStep5_sizes sz n hd1
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWNτ : ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ ((sz.size n : ℕ) : ℝ) ^ τ :=
    (Real.rpow_le_rpow hW0.le hWN hε₀.le).trans (Real.rpow_le_rpow_of_exponent_le hN1 hε₀τ)
  -- the level at the section
  have htt1 : ((tt n : TimeIcc s t n) : ℝ) < 1 := (tt n).2.2.trans_lt (ht n)
  have hlv := pfStep5Grid_level d ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ)
    ((tt n : TimeIcc s t n) : ℝ) hW1 le_rfl htt1
  have hWdl : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ 1 - ((tt n : TimeIcc s t n) : ℝ) := by
    have := hReg n; have := (tt n).2.2; linarith
  have hDlvl : D ≤ PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ) := by
    have := hlv.2.2.2 hWdl; linarith
  -- the measurable set `{J♯ ≥ W^{ε₀}}`
  obtain ⟨B, hBdef⟩ : ∃ B : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
      B = {H | ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ PfStep5Grid_JsharpM sz n (E n)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ))
        ((tt n : TimeIcc s t n) : ℝ) H} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_le measurable_const (pfStep5_JsharpM_measurable sz n (E n) _ _)
  have hsub : {ω' : sz.SeqΩ | ∃ v : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ τ * STtailTD sz n ((tt n : TimeIcc s t n) : ℝ) D v.2 <
        STLK2 sz n (E n) ((tt n : TimeIcc s t n) : ℝ) v.1 v.2 ω'} ⊆
      {ω' | sz.seqHflow n ((tt n : TimeIcc s t n) : ℝ) ω' ∈ B} := by
    rintro ω' ⟨v, hv⟩
    rw [hBdef]
    change ((sz.W n : ℕ) : ℝ) ^ ε₀ ≤ PfStep5Grid_JsharpM sz n (E n)
      (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst ((tt n : TimeIcc s t n) : ℝ))
      ((tt n : TimeIcc s t n) : ℝ) (sz.seqHflow n ((tt n : TimeIcc s t n) : ℝ) ω')
    rw [← pfStep5Grid_Jsharp sz E _ n _ ω']
    exact pfStep5_bad_sub sz n E hDlvl hWNτ ω' v hv
  -- transfer to the grid walk at the last grid index
  have hlast := gridTime_last s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (hK0 n)
  have heq := ST_pathP_eq_seqP sz s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n) (hs n)
    (tt n).2.1 (hK0 n) hBm
  rw [hlast] at heq
  have hsub2 : {ω : PathΩ sz | pathH sz s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n) ω ∈ B} ⊆
      {ω : PathΩ sz | ∀ k, k ≤ K n → PfStep5Grid_JsharpM sz n (E n)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst
          (gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k))
        (gridTime s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k)
        (pathH sz s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n k ω) < ((sz.W n : ℕ) : ℝ) ^ ε₀}ᶜ := by
    intro ω hω hall'
    have h1 := hall' (K n) le_rfl
    simp only [hlast] at h1
    have hω' : pathH sz s (fun m => ((tt m : TimeIcc s t m) : ℝ)) K n (K n) ω ∈ B := hω
    rw [hBdef] at hω'
    exact absurd hω' (not_le.2 h1)
  exact (measure_mono hsub).trans (heq.symm.le.trans ((measure_mono hsub2).trans hn))

end PT

/-! ## 14. Target 6: the lift `PrecPT → Prec` of `STLK2 ≤ N^τ T_{u,D}` (DECISIONS §64 (4)) -/

section Lift

/-- **Target 6** (the lift `PrecPT → Prec`: the right side `T_{u,D}` is deterministic with the floor `W^{-D} ≥ N^{-D}`;
`LemDecCalELip_lift` through `lemDecCalEPrec_lift` at `J ≡ 1`, `m = 0`, `R₀ = 0`, `R = T`). -/
theorem pfStep5_lift (d : ℕ) : PfStep5_lift_pin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htz hReg hPT D hD
  obtain ⟨hAdm, hEn, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hd1 : 1 ≤ d := by omega
  have hsize : sz.SizeTendsto := hAdm.2.2.1
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hE' : ∀ n, |STflowE z n| ≤ 2 - κ / 2 := fun n => (hEn n).le
  have hκ2 : 0 < κ / 2 := half_pos hκ
  have htN := lemDecCalEPrec_htN sz hAdm hReg hd1
  obtain ⟨C, hC0, hC⟩ := LemDecCalELip_LK2 sz (STflowE z) s t (κ / 2) hd hsize hκ2 hE' hs ht1 htN
  have h := lemDecCalEPrec_lift hd sz (STflowE z) s t hκ2 hD hsize hE' hs hst' ht1 htN
    (fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => STLK2 sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω)
    ⟨C, hC0, by
      filter_upwards [hC] with n hn ω hω u u' v
      exact hn ω hω u u' v.1 v.2⟩
    (fun n p => 0) (fun n p => STtailTD sz n (p.1 : ℝ) D p.2.2) (m := 0) 2 3 D (by norm_num)
    (by filter_upwards [hsize.eventually_ge_atTop 4] with n hn; exact lemDecCalEPrec_card_V12 sz n hn)
    (fun n p => le_rfl)
    (by
      filter_upwards [hsize.eventually_ge_atTop 1] with n hn p
      obtain ⟨-, -, -, -, -, hWN, -⟩ := pfStep5_sizes sz n hd1
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      exact (Real.rpow_le_rpow_of_nonpos hW0 hWN (by linarith)).trans
        (lemDecCalEPrec_tail_ge sz n (p.1 : ℝ) D p.2.2))
    (fun n u u' v => ⟨by simp, (LemDecCalELip_relcont sz n (t n) (u : ℝ) (u' : ℝ) D v.2 (ht1 n)
      u.2.2 u'.2.2).2.2.2.1⟩)
    (by
      convert hPT D hD using 2
      simp)
  convert h using 2
  simp

end Lift

/-! ## 15. Targets 7 and 8: `STPfStep5` and the case (iii) of Step 5 -/

section Final

/-- `1 < W` and `W^{-d} ≤ ilambda²` eventually (`(eq:WO)`: `ilambda² W^d ≥ 1`, `4 ≤ log W`). -/
private theorem pfStep5_Wev {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) :
    ∀ᶠ n in atTop, 1 < ((sz.W n : ℕ) : ℝ) ∧
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) ≤ sz.lam n ^ 2 := by
  filter_upwards [lemDecCalEPrec_numeric sz hA] with n hn
  obtain ⟨hlam, hA1, hlog4, -⟩ := hn
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hW1 : (1 : ℝ) < ((sz.W n : ℕ) : ℝ) := by
    by_contra hcon
    have hle : ((sz.W n : ℕ) : ℝ) ≤ 1 := not_lt.1 hcon
    have : Real.log ((sz.W n : ℕ) : ℝ) ≤ 0 := Real.log_nonpos hW0.le hle
    linarith
  refine ⟨hW1, ?_⟩
  have hWd : 0 < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW0 d
  rw [Real.rpow_neg hW0.le, Real.rpow_natCast, inv_le_iff_one_le_mul₀' hWd]
  linarith

/-- **Target 7** (`lem:pf_step5`, regime (iii), the borrowed pin `STPfStep5`, now proved): the grid walk
conclusion (target 4), the endpoint and sections (target 5), the lift (target 6) and the re-indexing by
`StochDomAt.precomp_param`. -/
theorem stPfStep5_holds (d : ℕ) : STPfStep5 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := pfStep5_walk d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htz hReg hKb hKw hLKs hDec hDecS hCon hStep1 hStep2 hLmax hLKU
  have hwalk := H 𝔠 sz z hflow s t hs hst htz hReg hKb hKw hLKs hDec hDecS hCon hStep1 hStep2 hLmax
    hLKU
  obtain ⟨hAdm, -, ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htz
  have hst' : ∀ n, s n ≤ t n := fun n => (hst n).le
  have hPT := pfStep5_PT_of_walk d sz (STflowE z) s t hs hst' ht1 hReg (pfStep5_Wev sz hAdm) hwalk
  have hPrec := pfStep5_lift d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s t hs hst htz hReg hPT
  intro D hD
  exact RBM.StochDomAt.precomp_param (hPrec D hD)
    (fun n (p : {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n}) => p.1)

/-- **Target 8** (one line): case (iii) of Step 5 from `lem:pf_step5` (`ST_step5_caseIII_of_pf`). -/
theorem stStep5III_holds (d : ℕ) : STStep5III d := ST_step5_caseIII_of_pf (stPfStep5_holds d)

end Final

end RBM.Gauss.Sizes

/-! ## 16. Compiled nonempty instances at `d = 3`

The data are the merged preflight instance (`RBM3D/Induction/Step5Pins.lean`, section 8): `sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`, `N_n = (W_n L_n)^3`), the flow `z0` at `κ = ε = 𝔡 = 1/10`,
`𝔠 = 1/6`, `s ≡ 0`, `t ≡ 1/16`, regime (iii) `sz0_reg5III`.  Targets 1-3 are applied at concrete data; target 4
and the pin `STPfStep5` (target 7) through the merged `inst_ing5_III`, `inst_pfStep5` (the stochastic premises of
`STIngR5`, other gates' pins, stay hypotheses inside `InstIng5Concl`); targets 5 and 6 at the same data with the
grid-walk conclusion (the output of target 4) and the per-time conclusion (the output of target 5) as hypotheses;
target 8 through `inst_skeletonIII`. -/

namespace RBM.Gauss.PfStep5Inst

open MeasureTheory Filter RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst
  RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Gauss.Step5Inst

/-- **Instance of target 1** at `sz0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 8` (grid step `1/128`), `n = 0`, `j = 3`,
`ω ≡ 0`: the grid state at the grid time `3/128 > 0` is the single-time state of some sample. -/
theorem pfStep5_inst_realize :
    ∃ ω' : sz0.SeqΩ, sz0.seqHflow 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3) ω' =
      pathH sz0 (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 0) :=
  pfStep5_realize sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 0) le_rfl
    (by norm_num)

/-- The same at the nonzero sample `ω ≡ 1` (every coordinate of every draw equal to `1`). -/
theorem pfStep5_inst_realize_one :
    ∃ ω' : sz0.SeqΩ, sz0.seqHflow 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3) ω' =
      pathH sz0 (fun _ => (0 : ℝ)) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 1) :=
  pfStep5_realize sz0 (fun _ => 0) (fun _ => 1 / 16) (fun _ => 8) 0 3 (fun _ _ => 1) le_rfl
    (by norm_num)

/-- **Instance of target 2** at `sz0`, `E = STflowE z0`, `D = 55`, `Jst ≡ 1`, `τ' = 1/10`, `n = 0`, `u = 1/16`. -/
theorem pfStep5_inst_goodMeas :
    ∃ S : Set (Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ), MeasurableSet S ∧
      ∀ ω : sz0.SeqΩ,
        ω ∈ lemDecCalEPrec_good sz0 (STflowE z0) 55 (fun _ _ _ => (1 : ℝ)) (1 / 10) 0 (1 / 16) ↔
          sz0.seqHflow 0 (1 / 16) ω ∈ S :=
  pfStep5_goodMeas sz0 (STflowE z0) 55 (fun _ _ _ => 1) (1 / 10) 0 (1 / 16)

/-- **Instance of target 3** at `sz0` with the admissibility constants `(𝔠, 𝔡) = (1/6, 1/10)` of `flow_z0`, `D* = 55`. -/
theorem pfStep5_inst_farAbsorb :
    ∃ D₂ : ℝ, 0 ≤ D₂ ∧ ∀ᶠ n in atTop, ∀ v w : ℝ, 0 ≤ v → v ≤ w → sz0.lam n ^ 2 ≤ 1 - w →
      4 * (2 * ((sz0.size n : ℕ) : ℝ) * (16 * ((sz0.size n : ℕ) : ℝ)) ^ 6) * ((sz0.L n : ℕ) : ℝ) ^ 3 *
          ((1 - v) / (1 - w)) ^ 3 * ((sz0.W n : ℕ) : ℝ) ^ (-D₂) ≤
        ((sz0.W n : ℕ) : ℝ) ^ (-(2 * (55 : ℝ))) :=
  pfStep5_farAbsorb sz0 (1 / 6) (1 / 10) sz0_admissible 55 (by norm_num)

/-- **Instance of target 4**: the constant `𝔠_d` and the grid-walk conclusion at `(sz0, z0, 0, 1/16)` from the
(stochastic) premises of `STIngR5`; every deterministic hypothesis (`3 ≤ 3`, the flow `z0`, `0 ≤ s < t ≤ lemT`,
the regime `sz0_reg5III`, `(con_st_ind)`) is discharged by `inst_ing5_III`. -/
theorem pfStep5_inst_walk :
    InstIng5Concl (fun sz E s t => PfStep5_walkConcl sz E s t) sz0 z0 sInst tInst 1 :=
  inst_ing5_III STReg5III _ (pfStep5_walk 3) sz0_reg5III 1 one_pos

/-- **Instance of target 5** at `(sz0, z0, 0, 1/16)`: every deterministic hypothesis is discharged
(`0 ≤ s`, `s ≤ t`, `t < 1`, the regime, `1 < W ∧ W^{-3} ≤ ilambda²` eventually); the grid-walk conclusion is the output of
target 4 (`pfStep5_inst_walk`). -/
theorem pfStep5_inst_PT (hw : PfStep5_walkConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PTConcl sz0 (STflowE z0) sInst tInst :=
  pfStep5_PT_of_walk 3 sz0 (STflowE z0) sInst tInst sz0_hs0 (fun n => (sz0_hst n).le)
    (fun n => by simp only [tInst]; norm_num) sz0_reg5III (pfStep5_Wev sz0 sz0_admissible) hw

/-- **Instance of target 6** at `(sz0, z0, 0, 1/16)`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`: every deterministic hypothesis
is discharged; the per-time conclusion is the output of target 5 (`pfStep5_inst_PT`). -/
theorem pfStep5_inst_lift (hpt : PfStep5_PTConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PrecConcl sz0 (STflowE z0) sInst tInst :=
  pfStep5_lift 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_reg5III hpt

/-- **Targets 5 and 6 composed** at the instance data, from the grid-walk conclusion. -/
theorem pfStep5_inst_Prec (hw : PfStep5_walkConcl sz0 (STflowE z0) sInst tInst) :
    PfStep5_PrecConcl sz0 (STflowE z0) sInst tInst :=
  pfStep5_inst_lift (pfStep5_inst_PT hw)

/-- **Targets 4, 5 composed from the premises** of `STIngR5` at the instance data: the only hypotheses are the
stochastic premises of the pin (other gates' statements, inside `InstIng5Concl`), the conclusion is the per-time
`PfStep5_PTConcl` of target 5. -/
theorem pfStep5_inst_PT_of_premises :
    InstIng5Concl (fun sz E s t => PfStep5_PTConcl sz E s t) sz0 z0 sInst tInst 1 := by
  obtain ⟨c, h0, h1, H⟩ := pfStep5_inst_walk
  exact ⟨c, h0, h1, fun hK hKw ha hD hDS h1' h2 h3 h4 =>
    pfStep5_inst_PT (H hK hKw ha hD hDS h1' h2 h3 h4)⟩

/-- **Targets 4, 5, 6 composed from the premises** of `STIngR5` at the instance data: the conclusion is the uniform
`PfStep5_PrecConcl` of target 6. -/
theorem pfStep5_inst_Prec_of_premises :
    InstIng5Concl (fun sz E s t => PfStep5_PrecConcl sz E s t) sz0 z0 sInst tInst 1 := by
  obtain ⟨c, h0, h1, H⟩ := pfStep5_inst_walk
  exact ⟨c, h0, h1, fun hK hKw ha hD hDS h1' h2 h3 h4 =>
    pfStep5_inst_Prec (H hK hKw ha hD hDS h1' h2 h3 h4)⟩

/-- **Instance of target 7** (`STPfStep5 3` applied at the data of `inst_pfStep5`): `𝔠_d` and the conclusion
`STPfConcl` at `(sz0, z0, 0, 1/16)`, all deterministic hypotheses discharged. -/
theorem pfStep5_inst_pf :
    InstIng5Concl (fun sz E s t => STPfConcl sz E s t) sz0 z0 sInst tInst 1 :=
  inst_pfStep5 (stPfStep5_holds 3) 1 one_pos

/-- **Instance of target 8** (`STStep5III 3` through `inst_skeletonIII`): the conclusion of Step 5, case (iii), at
`(sz0, z0, 0, 1/16)`, unconditional. -/
theorem pfStep5_inst_step5III :
    InstIng5Concl (fun sz E s t => STStep5Concl sz E s t) sz0 z0 sInst tInst 1 :=
  inst_skeletonIII (stPfStep5_holds 3) 1 one_pos

end RBM.Gauss.PfStep5Inst
