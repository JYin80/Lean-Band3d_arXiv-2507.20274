/-
Release check for T2200 (dispatcher V1, Mon Oct  5 16:45 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §29, §35, §36,
§45 O2, §53, §56, §59 O3, §64 (4)).
ST2-13b (the last open row of ST-2): clause (iv) of `STGridRepNAt`, the `𝒰`-weighted martingale tail, uniform in `k ≤ K`,
proved for the zero-mode-removed kernel `Q^{(A)} ∘ 𝒰 = zeroModeSet Q ∘ UN` and every `Q` (supervisor 2026-10-05-0653 O3);
`GridRepWTailNAt` is the case `Q = ∅`; with the merged `stGridRepN_of_tails` and `gridRepTailN_holds` it closes `STGridRepN`.
Section 1: the merged names it builds on and the consumers.  Section 2: the pinned vocabulary (`uKerQ`, `STeeUQM`,
`GridRepWTailQNAt`; defined in `RBM.Ind` verbatim by T2200, here in `RBM.Ind.T2200Check`) and the target statements as
`Prop`s (each target theorem's type is the body of its `…Stmt`).  Section 3: elaboration examples (Prop-valued, no proof).
Statement and `#check` only: no proofs, no `sorry`, no `by`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2200-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2168 (`Path/DifREP1`, 3df1812): vocabulary, the two tails, the interface, the assembly
#check @RBM.Ind.difRepMartN
#check @RBM.Ind.GridRepTailNAt
#check @RBM.Ind.GridRepWTailNAt
#check @RBM.Ind.difRepMartN_succ_sub
#check @RBM.Ind.difRep_flow_bounds
#check @RBM.Ind.gridRepRemN_holds
#check @RBM.Ind.stGridRepNAt_of_parts
#check @RBM.Ind.stGridRepN_of_tails
-- T2180 (`Path/DifREP2`, 76b840e): the maximal Azuma bound, the weighted conditional mgf, the peeling, crude bounds, tail (iii)
#check @RBM.Ind.azumaRandProxy_max
#check @RBM.Ind.difRepTail_condMGF_Z
#check @RBM.Ind.difRep2_peel
#check @RBM.Ind.difRep2_peel_N
#check @RBM.Ind.difRep2_norm_STeeM_le
#check @RBM.Ind.difRep2_norm_STeeM_le_N
#check @RBM.Ind.difRep2_eeShiftErrN_le
#check @RBM.Ind.difRep2_eeShift_sum_le
#check @RBM.Ind.gridRepTailN_holds
#check @RBM.Ind.stGridMart_holds
#check @RBM.Ind.stGridMartAt_holds
-- kernels: `UN`, `uKer`, tensor kernels, `Q^{(A)}` (`Kernel/Evolution`, ff8d36d; `Induction/ZeroModeCalc`, d1cb5a6)
#check @RBM.cycProd
#check @RBM.uKer
#check @RBM.UN
#check @RBM.uKer_eq_one_add
#check @RBM.norm_Xi_le
#check @RBM.norm_uKer_le
#check @RBM.norm_UN_le
#check @RBM.tensorKer
#check @RBM.UN_eq_tensorKer
#check @RBM.norm_tensorKer_apply_le
#check @RBM.norm_tensorKer_le
#check @RBM.zeroModeSet
#check @RBM.projMat
#check @RBM.norm_projMat_le
#check @RBM.zeroModeSet_tensorKer
#check @RBM.zeroModeSet_sum
#check @RBM.zeroModeSet_empty
#check @RBM.norm_zeroModeSet_le
#check @RBM.zeroModeSet_UN
#check @RBM.ZeroModeCalc_projMat_mul_uKer_comm
#check @RBM.Ind.zeroModeSet_Ugen
#check @RBM.Ind.zeroModeCalc_duhamel_inside_at
-- the semigroup of `𝒰` (`Induction/GridDuhamelN`, 2ebee73; `Path/Kernel`, e88681b)
#check @RBM.Ind.Ugen
#check @RBM.Ind.GridDuhamelN_Ugen_add
#check @RBM.Ind.GridDuhamelN_Ugen_self
#check @RBM.Ind.GridDuhamelN_Ugen_comp
#check @RBM.Path.ukerMat_mul
#check @RBM.Path.ukerMat_self
-- propagator, `S^{(B)}`, charges
#check @RBM.Theta
#check @RBM.Theta_sub_Theta
#check @RBM.norm_Theta_le
#check @RBM.Theta_commute_SB_of_three_le
#check @RBM.norm_t_mul_lt_one
#check @RBM.SB
#check @RBM.norm_SB
#check @RBM.sum_norm_SB_row
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.norm_mul_mSigma_lt_one
-- the increment `ξ = Z + Y`, the pair kernel, the shift, the `Y` moments (T2121, T2166, T2160, T2154, T2103, T2111)
#check @RBM.Ind.martIncN
#check @RBM.Ind.ZvecN
#check @RBM.Ind.YvecN
#check @RBM.Ind.UgenPairN
#check @RBM.Ind.qvFormN
#check @RBM.Ind.qvFormN_eq_re_UgenPairN
#check @RBM.Ind.eeShiftErrN
#check @RBM.Ind.norm_STeeM_shiftN_le
#check @RBM.Ind.AzumaProxyN_stopW
#check @RBM.Ind.AzumaProxyN_YfieldsW
#check @RBM.Ind.AzumaProxyN_rowsum_Ugen_pub
#check @RBM.Ind.gridAsm_stronglyMeasurable_ZvecN
#check @RBM.Ind.gridAsm_stronglyMeasurable_YvecN
#check @RBM.Ind.hermTestFunLoopN
#check @RBM.Ind.qvPropagatedN
-- grid walk, Doob (`Path/Walk`, `Path/Stop`, `Path/Azuma`)
#check @RBM.Path.PathΩ
#check @RBM.Path.pathP
#check @RBM.Path.filt
#check @RBM.Path.gridStep
#check @RBM.Path.gridTime
#check @RBM.Path.pathH
#check @RBM.Path.pathH_measurable_filt
#check @RBM.Gauss.walk_measurable_loopL
#check @RBM.Gauss.walk_measurable_blockMat
#check @RBM.Path.doob_L2_max
#check @RBM.Path.martingale_sq_eq_sum
-- pins, flow
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STGridRepN
#check @RBM.Gauss.Sizes.STGridMart
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
#check @RBM.lemT
-- Mathlib
#check @MeasureTheory.ofReal_measureReal
#check @MeasureTheory.measure_mono
#check @MeasureTheory.martingale_of_condExp_sub_eq_zero_nat
-- instance data
#check @RBM.Gauss.SizesInst.sz0
#check @RBM.Gauss.InductionDefsInst.z0
#check @RBM.Gauss.InductionDefsInst.flow_z0
#check @RBM.Gauss.InductionDefsInst.sInst
#check @RBM.Gauss.InductionDefsInst.tInst
#check @RBM.Gauss.InductionDefsInst.sixteenth_le_lemT
-- downstream (consumers of `GridRepWTailNAt`, `STGridRepN`; S5-15 / S5-26 consume the `Q`-form)
#check @RBM.Gauss.Sizes.ST_gridMart_of_repN
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN
#check @RBM.Gauss.Sizes.ST_step2_of_pinsN'
#check @RBM.Gauss.Sizes.ST_step2_of_pinsLW'
#check @RBM.Gauss.Sizes.STDuhamelConcl
#check @RBM.Gauss.Sizes.STDuhamelI
#check @RBM.Gauss.Sizes.STDuhamelII
#check @RBM.Gauss.Sizes.STStep2
#check @RBM.Gauss.Sizes.STNewKLK
#check @RBM.Gauss.Sizes.STLWT
#check @RBM.Gauss.Sizes.STEMn2Exp
#check @RBM.Gauss.Sizes.STOptL2
#check @RBM.Gauss.Sizes.STLocalAvgOfL2

/-! ## 2. Pinned vocabulary and target statements (T2200; elaboration only) -/

noncomputable section

namespace RBM.Ind.T2200Check

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind
open scoped NNReal ENNReal

/-- Vocabulary 1, `uKerQ`: **the slot kernel of `Q^{(A)} ∘ 𝒰_{v,w,σ}`** at slot `i`: `(I − L^{-d}J)(1 − v μ_i S)Θ_{wμ_i}` for
`i ∈ Q`, `(1 − v μ_i S)Θ_{wμ_i}` otherwise, `μ_i = m(σ_i)m(σ_{i+1})` (`cycProd`); the kernel family of `zeroModeSet_tensorKer`
applied to `UN_eq_tensorKer`.  (`Q` is the zero-mode set `Q^{(A)}`, not the `𝒬`-process of S3-14.) -/
noncomputable def uKerQ (d L : ℕ) [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool)
    (v w : ℝ) (i : Fin m) : Matrix (Zd d L) (Zd d L) ℂ :=
  if i ∈ Q then projMat d L * uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w
  else uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w

/-- Vocabulary 2, `STeeUQM`: **the zero-mode-removed weighted quadratic-variation loop**
`(((Q^{(A)}∘𝒰_{v,w,σ}) ⊗ (Q^{(A)}∘𝒰_{v,w,σ̄})) ∘ (ℰ⊗ℰ)^{M,(m)}_{v,σ})_{a,a}` for a fine matrix `H` (the paper's
`(sahwNQ2)`, `3_5:1908`, with `lem:DIfREP`); `STeeUM` is the case `Q = ∅` (target 1). -/
noncomputable def STeeUQM {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q σ v w i (a i) (b i)) *
      (∏ i, uKerQ d (sz.L n) (sz.lam n) E Q (fun i => !σ i) v w i (a i) (b' i)) *
        sz.STeeM n E v H σ b b'

/-- Vocabulary 3, `GridRepWTailQNAt`: **clause (iv) of `STGridRepNAt` for `Q^{(A)} ∘ 𝒰`** (`difRepMartN`, every zero-mode
set `Q`): the `Q^{(A)}∘𝒰`-weighted martingale tail, for all `k ≤ K` at once.  `GridRepWTailNAt d m` is the case
`Q = ∅` (target 2). -/
def GridRepWTailQNAt (d m : ℕ) (Q : Finset (Fin m)) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
              pathP sz {ω | ∃ k, k ≤ K n ∧
                ((sz.size n : ℕ) : ℝ) ^ ε' *
                    (∑ j ∈ Finset.range k, gridStep s t K n *
                      ‖STeeUQM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                        (pathH sz s t K n j ω) Q i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                        (1 / 2 : ℝ) <
                  ‖∑ j ∈ Finset.range k,
                    zeroModeSet d (sz.L n) Q
                      (UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => difRepMartN sz (STflowE z) s t K n (i.1, b) (j + 1) ω -
                          difRepMartN sz (STflowE z) s t K n (i.1, b) j ω)) i.2‖} ≤
                ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))

/-- Target 1, `STeeUQM_empty`: without zero-mode removal the proxy is the merged `STeeUM`. -/
def STeeUQMEmptyStmt : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)),
    STeeUQM sz n E v w H (∅ : Finset (Fin m)) σ a = sz.STeeUM n E v w H σ a

/-- Target 2, `gridRepWTailN_of_Q`: the case `Q = ∅` is the merged clause (iv) (`zeroModeSet_empty`, target 1). -/
def GridRepWTailNOfQStmt : Prop :=
  ∀ d m : ℕ, GridRepWTailQNAt d m (∅ : Finset (Fin m)) → GridRepWTailNAt d m

/-- Target 3, `zeroModeSet_UN_eq_uKerQ`: `Q^{(A)} ∘ 𝒰_{v,w,σ}` is the tensor kernel of `uKerQ` (no hypothesis). -/
def ZeroModeSetUNEqUKerQStmt : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g E : ℝ) {m : ℕ} (Q : Finset (Fin m)) (σ : Fin m → Bool) (v w : ℝ)
    (A : (Fin m → Zd d L) → ℂ),
    zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) v w A) = tensorKer d L (uKerQ d L g E Q σ v w) A

/-- Target 4, `difRep3_UN_transfer`: **the transfer identity** (semigroup of `𝒰` + `Q^{(A)}` commutes with `𝒰`):
`Σ_{j<k} Q∘𝒰_{u_j,w} A_j = 𝒰_{v,w} (Σ_{j<k} Q∘𝒰_{u_j,v} A_j)` for `0 ≤ v, w < 1`, `|E| ≤ 2`, the `u_j` arbitrary. -/
def DifRep3UNTransferStmt : Prop :=
  ∀ {d L : ℕ} [NeZero L] (g : ℝ), 3 ≤ L → ∀ {E : ℝ}, |E| ≤ 2 →
    ∀ {m : ℕ} (σ : Fin m → Bool) (Q : Finset (Fin m)) {v w : ℝ}, 0 ≤ v → v < 1 → 0 ≤ w → w < 1 →
      ∀ (k : ℕ) (u : ℕ → ℝ) (A : ℕ → (Fin m → Zd d L) → ℂ),
        ∑ j ∈ Finset.range k, zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) w (A j)) =
          UN d L g (fun i => mSigma E (σ i)) v w
            (∑ j ∈ Finset.range k, zeroModeSet d L Q (UN d L g (fun i => mSigma E (σ i)) (u j) v (A j)))

/-- Target 5, `gridRepWTailQN_holds`: **the zero-mode-removed weighted tail at every loop length `m ≥ 2`, every `Q`,
every `d`.** -/
def GridRepWTailQNHoldsStmt : Prop :=
  ∀ d m : ℕ, 2 ≤ m → ∀ Q : Finset (Fin m), GridRepWTailQNAt d m Q

/-- Target 6, `gridRepWTailN_holds`: clause (iv) as pinned by T2168 (`Q = ∅`), every `d`. -/
def GridRepWTailNHoldsStmt : Prop :=
  ∀ d m : ℕ, 2 ≤ m → GridRepWTailNAt d m

/-- Target 7, `stGridRepN_holds`: **the pin `STGridRepN` is unconditional for `3 ≤ d`** (`stGridRepN_of_tails`,
`gridRepTailN_holds`, target 6). -/
def StGridRepNHoldsStmt : Prop :=
  ∀ d : ℕ, 3 ≤ d → STGridRepN d

end RBM.Ind.T2200Check

/-! ## 3. Elaboration examples (Prop-valued; no proof obligation) -/

namespace RBM.Ind.T2200Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.Ind

/-- The `Q`-form at `d = 3`, `m = 2`, `Q = {0}` (the S5-26 case `Q^{(1)}`) is a well-formed `Prop`. -/
example : Prop := GridRepWTailQNAt 3 2 ({0} : Finset (Fin 2))

/-- The `Q = ∅` form at `d = 3`, `m = 3`. -/
example : Prop := GridRepWTailQNAt 3 3 (∅ : Finset (Fin 3))

/-- The vocabulary at the preflight data (`sz0`, `n = 0`, `E = 1/2`, `v = 0`, `w = 1/16`, `H = 0`). -/
example : Prop :=
  STeeUQM RBM.Gauss.SizesInst.sz0 0 (1 / 2) 0 (1 / 16) 0 ({0} : Finset (Fin 2)) (fun _ => true) (fun _ => 0) = 0

end RBM.Ind.T2200Check

end
