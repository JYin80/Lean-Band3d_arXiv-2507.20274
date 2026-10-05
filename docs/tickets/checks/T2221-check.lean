import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import RBM3D.Induction.PfStep5Alg
import RBM3D.Induction.TailtoTailSq
import RBM3D.Induction.Step2Core
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Step5Cases
import RBM3D.Path.DifREP3

/-!
# T2221 (S5-11a) check file: the pins of `Induction/PfStep5Grid` and the cited merged names

Section 0: the vocabulary of the new file (three `noncomputable def`s, copied verbatim into the Lean
file): the time-dependent level `D_u = D* + 2 log_W(1-u)` (DECISIONS §70 (1)), the realized control
`J♯` as a function of a fine matrix (the matrix form of the merged `LemDecCalELip_Jsharp`), and the
grid stopping index of `(eq:def_TTT)` at `(u_j, D_{u_j})`.
Section 1: the exact statements of the targets (`def … : Prop`); the theorem of each target must have
the body of the pin of the same name (script diff, the binder line and the name stripped):
`PfStep5Grid_level_pin` ↔ `pfStep5Grid_level` (target 1), `PfStep5Grid_Jsharp_pin` ↔
`pfStep5Grid_Jsharp` (target 2), `PfStep5Grid_stop_pin` ↔ `pfStep5Grid_stop` (target 3a),
`PfStep5Grid_below_pin` ↔ `pfStep5Grid_below` (target 3b), `PfStep5Grid_duhamel_pin` ↔
`pfStep5Grid_duhamel` (target 4).
Section 2: `#check` of every merged name the ticket cites.
Section 3: Prop-valued examples (statement shapes at merged data, no proofs).
No proofs, no `sorry`, no `by` (DECISIONS §17 check-file rules).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 0. Vocabulary (copied verbatim into `RBM3D/Induction/PfStep5Grid.lean`) -/

/-- The time-dependent level `D_u := D* + 2 log_W(1-u)` (DECISIONS §70 (1); `docs/reports/T2209-prove.md` (a),
row 1): `W^{-D_u} = (1-u)^{-2} W^{-D*}`. -/
noncomputable def PfStep5Grid_level (W Dst u : ℝ) : ℝ :=
  Dst + 2 * (Real.log (1 - u) / Real.log W)

/-- The realized control `J♯ = max(1, max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}(H)| / T_{u,D}(|a₁-a₂|))` of a fine matrix `H`
(the matrix form of `LemDecCalELip_Jsharp`, `Induction/LemDecCalELip.lean:925`, same `sup'`). -/
noncomputable def PfStep5Grid_JsharpM {d : ℕ} (sz : Sizes d) (n : ℕ) (E D u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKM sz n E u H p.1 p.2‖ / STtailTD sz n u D p.2))

/-- **The stopping time `T` of `(eq:def_TTT)`** (`3_5:2364-2369`) on the grid `u_j = s + jΔ`, at the level
`D_{u_j}` (DECISIONS §70 (1)): the first grid index `j ≤ K` with `J♯(u_j, D_{u_j})(H_j) ≥ W^ε` (`K` if none);
the shape of the merged `STstopIdx` (`Induction/Step2Defs.lean:544`). -/
noncomputable def PfStep5Grid_stopIdx {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (E : ℕ → ℝ) (Dst ε : ℝ) (n : ℕ) : PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
      PfStep5Grid_JsharpM sz n (E n)
        (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s t K n j)) (gridTime s t K n j)
        (pathH sz s t K n j ω))
    (((sz.W n : ℕ) : ℝ) ^ ε) (K n)

/-! ## 1. Pins -/

/-- **Target 1** (the level, DECISIONS §70 (1)): for `W > 1`, `u ≤ u' < 1`: `W^{-D_{u'}} = (1-u')^{-2} W^{-D*}`;
`D_u` is nonincreasing in `u`; `D_u ≤ D*` for `u ≥ 0`; `D_{u'} ≥ D* - 2d` when `1 - u' ≥ W^{-d}`. -/
def PfStep5Grid_level_pin : Prop :=
  ∀ (d : ℕ) (W Dst u u' : ℝ), 1 < W → u ≤ u' → u' < 1 →
    W ^ (-(PfStep5Grid_level W Dst u')) = ((1 - u')⁻¹) ^ 2 * W ^ (-Dst) ∧
    PfStep5Grid_level W Dst u' ≤ PfStep5Grid_level W Dst u ∧
    (0 ≤ u → PfStep5Grid_level W Dst u ≤ Dst) ∧
    (W ^ (-(d : ℝ)) ≤ 1 - u' → Dst - 2 * (d : ℝ) ≤ PfStep5Grid_level W Dst u')

/-- **Target 2** (bridge, expected `rfl` after unfolding: `STLM_seqHflow`): the merged realized control of the
model at `(n, u, ω)` is the matrix control at the flow matrix `H_u(ω)`. -/
def PfStep5Grid_Jsharp_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
    LemDecCalELip_Jsharp sz E D n u ω = PfStep5Grid_JsharpM sz n (E n) D u (sz.seqHflow n u ω)

/-- **Target 3a**: the grid stopping index is a stopping time of the coordinate filtration
(`isStoppingTime_firstHit_grid`, measurability of `J♯` in `H` from `STLKM_measurable`). -/
def PfStep5Grid_stop_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (Dst ε : ℝ) (n : ℕ),
    IsStoppingTime (filt sz) (fun ω => (PfStep5Grid_stopIdx sz s t K E Dst ε n ω : ℕ))

/-- **Target 3b** (the stopping condition below the index, `lt_firstHit_imp`): for `j < T`,
`J♯(u_j, D_{u_j})(H_j) < W^ε`. -/
def PfStep5Grid_below_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (Dst ε : ℝ) (n j : ℕ) (ω : PathΩ sz),
    j < PfStep5Grid_stopIdx sz s t K E Dst ε n ω →
      PfStep5Grid_JsharpM sz n (E n) (PfStep5Grid_level ((sz.W n : ℕ) : ℝ) Dst (gridTime s t K n j))
          (gridTime s t K n j) (pathH sz s t K n j ω) <
        ((sz.W n : ℕ) : ℝ) ^ ε

/-- **Target 4** (the Duhamel form `(int_K-L_ST)` from the additive grid decomposition of `STGridRepNAt`
conjunct 1, deterministic, any 2-index tensors): on a grid `u_{j+1} = u_j + Δ`, `0 ≤ u_0`, `u_k < 1`, if
`A_j = A_0 + Δ Σ_{i<j} (Θ^{(2)}_{u_i,σ} A_i + F_i) + Rem_j + Mart_j` for `j ≤ k` with `|A_j| ≤ M`, `|Rem_j| ≤ R`, then
`|A_k - 𝒰_{u_0,u_k} A_0 - Δ Σ_{j<k} 𝒰_{u_j,u_k} F_j - Σ_{j<k} 𝒰_{u_j,u_k}(Mart_{j+1} - Mart_j)| ≤ 64 (1-u_k)^{-7} (R + Δ M)`.
The martingale sum is token for token the one of `STGridRepNAt` conjunct 4 (`Ugen = UN … (fun i => mSigma E (σ i))`). -/
def PfStep5Grid_duhamel_pin (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d L) → ℂ),
    |E| ≤ 2 → 0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 →
    (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) → (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) →
    (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (ThetaN d L g (fun i' => mSigma E (σ i')) (u i) (A i) b + F i b) + Rem j b + Mart j b) →
    ∀ a, ‖A k a - RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k,
          RBM.Ind.Ugen d L g E σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)

/-! ## 2. Merged names cited by the ticket -/

-- the borrowed pin and its consumer
#check STPfStep5
#check STPfConcl
#check STIngR5
#check STReg5III
#check STIdx2
#check STLK2
#check STtailTD
#check ST_step5_caseIII_of_pf
#check RBM.Gauss.Step5Inst.inst_pfStep5
#check st5_ellT_one
-- S5-10 (T2209), S5-10a (T2215)
#check PfStep5Alg_tailAnti_pin
#check PfStep5Alg_ugenSum'_pin
#check PfStep5Alg_riemann_pin
#check PfStep5Alg_goodStop'_pin
#check PfStep5Alg_goodProb_pin
#check PfStep5Alg_closure_pin
#check pfStep5Alg_tailAnti
#check pfStep5Alg_ugenSum'
#check pfStep5Alg_riemann
#check pfStep5Alg_goodStop'
#check pfStep5Alg_goodProb
#check pfStep5Alg_closure
#check tailtoTailSq_kernelGen
#check tailtoTailSq_kernel
-- S5-09, S5-09a
#check lemDecCalEPrec_good
#check lemDecCalEPrec_prob
#check lemDecCalEPrec_Bounds
#check lemDecCalEPrec_goodDet
#check lemDecCalEPrec_gij
#check lemDecCalEPrec_kell
#check lemDecCalEPrec_QW
#check lemDecCalEPrec_numeric
#check lemDecCalEPrec_lossWG_eventually
#check lemDecCalEPrec_R3₀
#check lemDecCalEPrec_R3
#check LemDecCalELip_Jsharp
#check LemDecCalELip_Jsharp_basic
#check LemDecCalELip_tail_pos
#check LemDecCalELip_LK2
#check LemDecCalELip_relcont
#check LemDecCalELip_lift
-- Step 2 vocabulary and grid layer
#check STLM
#check STLM_seqHflow
#check STLKM
#check STLKM_measurable
#check STstopIdx
#check STstopIdx_isStoppingTime
#check STgAN
#check STgDriftN
#check STgA_eq_STgAN
#check STgDrift_eq_STgDriftN
#check STthetaOp_eq_ThetaN
#check STeeUM
#check STGridRepNAt
#check STGridRepN
#check ST_gridMart_of_repN
#check ST_pathP_eq_seqP
#check ST_whp_grid
#check ST_model_of_whp_grid
#check ST_PT_of_sections
#check ST_firstHit_hit
#check RBM.Ind.stGridRepN_holds
#check RBM.Ind.difRep2_norm_STeeM_le_N
-- kernels
#check RBM.Ind.Ugen
#check RBM.Ind.GridDuhamelN_Ugen_add
#check RBM.Ind.GridDuhamelN_Ugen_self
#check RBM.Ind.GridDuhamelN_Ugen_comp
#check RBM.Ind.GridDuhamelN_Ugen_duhamel_telescope
#check RBM.Path.duhamel_telescope
#check RBM.cycProd
#check RBM.thetaKer
#check RBM.uKer
#check RBM.ThetaN
#check RBM.UN
#check RBM.uKer_eq_one_add
#check RBM.norm_Xi_le
#check RBM.norm_uKer_le
#check RBM.norm_UN_le
#check RBM.norm_tensorKer_le
#check RBM.Theta
#check RBM.mul_Theta_of_three_le
#check RBM.norm_Theta_le
#check RBM.norm_SB
#check RBM.mSigma
#check RBM.norm_mSigma
#check RBM.tailTD
-- grid walk and stopping
#check RBM.Path.firstHit
#check RBM.Path.firstHit_le
#check RBM.Path.lt_firstHit_imp
#check RBM.Path.isStoppingTime_firstHit_grid
#check RBM.Path.gridTime
#check RBM.Path.gridStep
#check RBM.Path.gridTime_last
#check RBM.Path.pathH
#check RBM.Path.pathP
#check RBM.Path.filt
#check RBM.Path.map_pathH_eq
-- Mathlib (level algebra)
#check Real.rpow_def_of_pos
#check Real.rpow_add
#check Real.exp_log
#check Real.log_le_log
#check Real.log_nonpos

/-! ## 3. Statement shapes (no proofs) -/

example : Prop := PfStep5Grid_level_pin
example : Prop := PfStep5Grid_duhamel_pin 3
example : Prop := PfStep5Grid_Jsharp_pin SizesInst.sz0
example : Prop := PfStep5Grid_stop_pin SizesInst.sz0
example : Prop := PfStep5Grid_below_pin SizesInst.sz0
example : Prop := STPfStep5 3

end RBM.Gauss.Sizes
