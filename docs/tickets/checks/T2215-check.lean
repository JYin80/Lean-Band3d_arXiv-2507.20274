import RBM3D.Induction.TailtoTail
import RBM3D.Induction.Step5Cases
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.LemDecCalEPrec
import RBM3D.Path.DifREP3

/-!
# T2215 (S5-10a) check file: the pins of `Induction/TailtoTailSq` and the cited merged names

Section 1: the exact statements of the targets (`def … : Prop`); the theorem of each target must have
the body of the pin of the same name (script diff, the binder line and the name stripped):
`TailtoTailSq_kernelGen_pin` ↔ `tailtoTailSq_kernelGen` (target 7g, any tensor `X`),
`TailtoTailSq_kernel_pin` ↔ `tailtoTailSq_kernel` (target 7, the merged `STeeUM`; T2209's
`pfStep5Alg_qvKernel` renamed), `TailtoTailSq_instC_pin` ↔ `inst_tailtoTailSq_c` (instance (c) of
`docs/reports/T2209-prove.md` (a)).  1.4 is the bridge shape `STeeUM = Σ Σ ∏ uKer ∏ uKer STeeM` (`rfl`, no target).
Section 2: `#check` of every merged name the ticket cites.
Section 3: Prop-valued examples (statement shapes at merged instance data, no proofs).
No proofs, no `sorry`, no `by` (DECISIONS §17 check-file rules).
-/

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

/-- **Target 7g** (squared-profile `TailtoTail` for an arbitrary 4-index tensor `X`, near/far split at
`ℓ* = (log W)^{3/2}`): (H1) near bound `‖X(b,b')‖ ≤ p T_{v,D}(|b₁-b₂|)²` for `max_i |b_i - b'_i| ≤ ℓ*`
(the shape of `lemDecCalEPrec_Bounds` conjunct 3), (H2) crude bound `‖X‖ ≤ Y`, (H3) `‖Θ_w(x,y)‖ ≤ W^{-D₂}` for
`|x-y| ≥ ℓ* ℓ_w / 8` (the hypothesis `hkell` of `lemDecCalEPrec_goodDet` at `u = w`, `D = D₂`; `ℓ_w = 1` here).
Conclusion with `ρ = (1-v)/(1-w)`, `C₇ = 18 e^{8d+2}`:
`‖Σ_{b,b'} Π_i K^σ_i(a_i,b_i) Π_i K^{σ̄}_i(a_i,b'_i) X(b,b')‖ ≤ C₇ p (T_{w,D}(|a₁-a₂|)² + ρ⁴ W^{-2D}) + 4 Y L^d ρ³ W^{-D₂}`. -/
def TailtoTailSq_kernelGen_pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g W D D₂ E v w p Y : ℝ), 0 < W → |E| ≤ 2 →
    0 ≤ v → v ≤ w → w < 1 → g ^ 2 ≤ 1 - w → 4 ≤ Real.log W → 0 ≤ p → 0 ≤ Y →
    ∀ (σ : Fin 2 → Bool) (X : (Fin 2 → Zd d L) → (Fin 2 → Zd d L) → ℂ),
      (∀ b b' : Fin 2 → Zd d L,
        (∀ i : Fin 2, ((zdistInf d L (b i - b' i) : ℕ) : ℝ) ≤ Real.log W ^ (3 / 2 : ℝ)) →
        ‖X b b'‖ ≤ p * tailTD d W v D ((zdistInf d L (b 0 - b 1) : ℕ) : ℝ) ^ 2) →
      (∀ b b' : Fin 2 → Zd d L, ‖X b b'‖ ≤ Y) →
      (∀ x y : Zd d L,
        (1 / 8 : ℝ) * (Real.log W ^ ((3 : ℝ) / 2) * ellT L g w) ≤ (zdistInf d L (x - y) : ℝ) →
        ‖Theta d L g (w : ℂ) x y‖ ≤ W ^ (-D₂)) →
      ∀ a : Fin 2 → Zd d L,
        ‖∑ b : Fin 2 → Zd d L, ∑ b' : Fin 2 → Zd d L,
            (∏ i, uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
              (∏ i, uKer d L g (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
                X b b'‖ ≤
          18 * Real.exp (8 * (d : ℝ) + 2) * p *
              (tailTD d W w D ((zdistInf d L (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
                ((1 - v) / (1 - w)) ^ 4 * (W ^ (-D)) ^ 2) +
            4 * Y * (L : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * W ^ (-D₂)

/-- **Target 7** (= T2209 target 7 `pfStep5Alg_qvKernel`, restated in `docs/reports/T2209-prove.md` (a)
"Target 2′ and target 7", renamed): target 7g at `L = L_n`, `g = lam_n`, `W = W_n`, `X = STeeM sz n E v H σ`
for any fine matrix `H`; the left side is the merged `STeeUM` (`Step2Defs.lean:797`), the quadratic-variation
weight of `STGridRepNAt` conjunct 4 (`Step2Defs.lean:839-851`). -/
def TailtoTailSq_kernel_pin {d : ℕ} (sz : Sizes d) : Prop :=
  3 ≤ d → ∀ (n : ℕ) (E v w D D₂ p Y : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool),
    |E| ≤ 2 → 0 ≤ v → v ≤ w → w < 1 → sz.lam n ^ 2 ≤ 1 - w →
    4 ≤ Real.log ((sz.W n : ℕ) : ℝ) → 0 ≤ p → 0 ≤ Y →
    (∀ b b' : Fin 2 → Zd d (sz.L n),
      (∀ i : Fin 2, ((zdistInf d (sz.L n) (b i - b' i) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)) →
      ‖STeeM sz n E v H σ b b'‖ ≤ p * STtailTD sz n v D b ^ 2) →
    (∀ b b' : Fin 2 → Zd d (sz.L n), ‖STeeM sz n E v H σ b b'‖ ≤ Y) →
    (∀ x y : Zd d (sz.L n),
      (1 / 8 : ℝ) * (Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) * ellT (sz.L n) (sz.lam n) w) ≤
        (zdistInf d (sz.L n) (x - y) : ℝ) →
      ‖Theta d (sz.L n) (sz.lam n) (w : ℂ) x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-D₂)) →
    ∀ a : Fin 2 → Zd d (sz.L n),
      ‖STeeUM sz n E v w H σ a‖ ≤
        18 * Real.exp (8 * (d : ℝ) + 2) * p *
            (STtailTD sz n w D a ^ 2 + ((1 - v) / (1 - w)) ^ 4 * (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ 2) +
          4 * Y * ((sz.L n : ℕ) : ℝ) ^ d * ((1 - v) / (1 - w)) ^ 3 * ((sz.W n : ℕ) : ℝ) ^ (-D₂)

/-- **Instance (c)** of the preflight (`docs/reports/T2209-prove.md` (a) (ii) (c)): target 7g at `d = 3`, `L = 20`,
`g = 1/64`, `W = 64`, `D = 8`, `D₂ = 5`, `E = 0`, `v = 1/32`, `w = 1/16`, `p = Y = 1`, with the concrete nonnegative
worst tensor `X(b,b') = T_{v,D}(|b₁-b₂|)²` on near pairs and `1` on far pairs (both kinds occur: `max zdist = 10 > ℓ* = 8.48`).
(H1), (H2) and the scalar premises are discharged in the proof; (H3) (`max_{|x| ≥ 2} Θ_w(x) = 2.8e-10 ≤ 64^{-5} = 9.3e-10`,
script (c)) stays a hypothesis. -/
def TailtoTailSq_instC_pin : Prop :=
  (∀ x y : Zd 3 20,
      (1 / 8 : ℝ) * (Real.log 64 ^ ((3 : ℝ) / 2) * ellT 20 (1 / 64) (1 / 16)) ≤ (zdistInf 3 20 (x - y) : ℝ) →
      ‖Theta 3 20 (1 / 64) ((1 / 16 : ℝ) : ℂ) x y‖ ≤ (64 : ℝ) ^ (-(5 : ℝ))) →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 20),
      ‖∑ b : Fin 2 → Zd 3 20, ∑ b' : Fin 2 → Zd 3 20,
          (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (σ i)) i) (1 / 32) (1 / 16) (a i) (b i)) *
            (∏ i, uKer 3 20 (1 / 64) (cycProd (fun i => mSigma 0 (!σ i)) i) (1 / 32) (1 / 16) (a i) (b' i)) *
              (((if (∀ i : Fin 2, ((zdistInf 3 20 (b i - b' i) : ℕ) : ℝ) ≤ Real.log 64 ^ (3 / 2 : ℝ)) then
                  tailTD 3 64 (1 / 32) 8 ((zdistInf 3 20 (b 0 - b 1) : ℕ) : ℝ) ^ 2 else 1 : ℝ)) : ℂ)‖ ≤
        18 * Real.exp (8 * ((3 : ℕ) : ℝ) + 2) * 1 *
            (tailTD 3 64 (1 / 16) 8 ((zdistInf 3 20 (a 0 - a 1) : ℕ) : ℝ) ^ 2 +
              ((1 - 1 / 32) / (1 - 1 / 16)) ^ 4 * ((64 : ℝ) ^ (-(8 : ℝ))) ^ 2) +
          4 * 1 * ((20 : ℕ) : ℝ) ^ 3 * ((1 - 1 / 32) / (1 - 1 / 16)) ^ 3 * (64 : ℝ) ^ (-(5 : ℝ))

/-! ### 1.4 Bridge shape (no target): `STeeUM` unfolds to the left side of target 7g at `X = STeeM` (`rfl`). -/

example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (E v w : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)),
    STeeUM sz n E v w H σ a =
      ∑ b : Fin 2 → Zd d (sz.L n), ∑ b' : Fin 2 → Zd d (sz.L n),
        (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
          (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
            STeeM sz n E v H σ b b'

-- `STtailTD` is `tailTD` at `W_n` and `zdistInf` (`Step5Pins.lean:151-152`, `rfl`): shape only.
example : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)),
    STtailTD sz n u D a = tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)

end RBM.Gauss.Sizes

/-! ## 2. Merged names cited by the ticket -/

-- the kernels (`Kernel/Evolution.lean`, ff8d36d; `Propagator/Basic.lean`, 020ec7a; `Propagator/Props4.lean`, 892334b)
#check @RBM.uKer
#check @RBM.uKer_eq_one_add
#check @RBM.norm_uKer_le
#check @RBM.cycProd
#check @RBM.norm_cycProd
#check @RBM.sum_norm_row_le
#check @RBM.UN
#check @RBM.Theta
#check @RBM.Theta_mul_of_three_le
#check @RBM.Theta_real_eq
#check @RBM.Theta_real_nonneg
#check @RBM.norm_t_mul_lt_one
#check @RBM.norm_Theta_apply_le
#check @RBM.norm_Theta_le
-- the block kernel and the lattice (`Defs/Block.lean` a722f63, `Defs/Neighbours.lean` be709a6,
-- `Defs/Lattice.lean` 51f1a17, `Defs/Sizes.lean` 0a873f1, `Defs/Params.lean` c3f3d5d, `Defs/Semicircle.lean` fbc9870)
#check @RBM.SB_apply
#check @RBM.sbKernelR
#check @RBM.sbKernel_eq_ofReal
#check @RBM.sbKernelR_nonneg
#check @RBM.sum_sbKernelR
#check @RBM.card_nbhd
#check @RBM.zdist_add_le
#check @RBM.zdist_neg
#check @RBM.zdistD
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.Idx
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.neZeroL
#check @RBM.ellT
#check @RBM.mSigma
#check @RBM.norm_mSigma
-- the tail (`Defs/Tail.lean` c8e4f17; `Induction/Step5Pins.lean` d7da51e)
#check @RBM.tailTD
#check @RBM.tailTD_nonneg
#check @RBM.Gauss.Sizes.STtailTD
-- S5-04 (`Induction/TailtoTail.lean`, 37f3a22) and S5-03 (`Induction/Step5Cases.lean`, 30ed55a)
#check @RBM.Gauss.Sizes.STTailtoTail
#check @RBM.Gauss.Sizes.stTailtoTail_holds
#check @RBM.Gauss.Sizes.st5_ellT_one
-- the quadratic-variation objects (`Induction/Step2Defs.lean`, 86124dc; `Induction/Step2Iterate.lean`, c5bbae7)
#check @RBM.Gauss.Sizes.STeeM
#check @RBM.Gauss.Sizes.STeeUM
#check @RBM.Gauss.Sizes.STGridRepNAt
#check @RBM.Gauss.Sizes.STeeM_seqHflow
-- the suppliers of (H1)-(H3) for S5-11 (`Induction/LemDecCalEPrec.lean` d7da51e; `Path/DifREP2.lean` 76b840e)
#check @RBM.Gauss.Sizes.lemDecCalEPrec_Bounds
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3₀
#check @RBM.Gauss.Sizes.lemDecCalEPrec_R3
#check @RBM.Gauss.Sizes.lemDecCalEPrec_goodDet
#check @RBM.Gauss.Sizes.lemDecCalEPrec_kell
#check @RBM.Ind.difRep2_norm_STeeM_le_N
-- grid (`Induction/GridDuhamelN.lean` 2ebee73, `Path/DifREP3.lean` b3c37aa)
#check @RBM.Ind.Ugen
#check @RBM.Ind.stGridRepN_holds
-- instance data (`Defs/Sizes.lean`, 0a873f1)
#check @RBM.Gauss.SizesInst.sz0

/-! ## 3. Statement shapes (Prop-valued, no proofs) -/

example : Prop := RBM.Gauss.Sizes.TailtoTailSq_kernelGen_pin 3
example : Prop := RBM.Gauss.Sizes.TailtoTailSq_kernel_pin RBM.Gauss.SizesInst.sz0
example : Prop := RBM.Gauss.Sizes.TailtoTailSq_instC_pin
example : Prop := RBM.Gauss.Sizes.STTailtoTail 3
