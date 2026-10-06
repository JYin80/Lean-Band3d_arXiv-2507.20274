/-
T2254 (LW-14d) check file: merged names (section 1) and the pin texts of the targets (section 2).
No proofs, no `sorry`, no `by`.  Compiles on `main` (88183b6) as is.
-/
import RBM3D.Graph.LWExpTerm2
import RBM3D.Graph.LWExpTerm
import RBM3D.Graph.LWPins
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step5Kit
import RBM3D.Induction.Step34Pins
import RBM3D.Induction.ScaleFacts
import RBM3D.Loop.KLFinal
import RBM3D.Loop.KLUnique
import RBM3D.Loop.PureLoop
import RBM3D.Defs.RadialSum

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names (each in the namespace of its enclosing `namespace … end` block) -/

-- `Graph/LWExpTerm2.lean` (T2243, d6ebc39, `namespace RBM.Gauss.Sizes` `:63-2053`)
#check @RBM.Gauss.Sizes.LWExpKer
#check @RBM.Gauss.Sizes.LWExpKp
#check @RBM.Gauss.Sizes.LWExpI1K
#check @RBM.Gauss.Sizes.LWExpI23K
#check @RBM.Gauss.Sizes.LWExpI41K
#check @RBM.Gauss.Sizes.LWExpG5'
#check @RBM.Gauss.Sizes.lwCutExp_of_terms
#check @RBM.Gauss.Sizes.lwExpTerm2_KK
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_KK
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_SB
#check @RBM.Gauss.Sizes.lwExpTerm2_ker_of_eventually
#check @RBM.Gauss.Sizes.lwExpTerm2_zdistInf_add_le
#check @RBM.Gauss.Sizes.lwExpTerm2_w
#check @RBM.Gauss.Sizes.lwExpTerm2_L2
#check @RBM.Gauss.Sizes.lwExpTerm2_L3
#check @RBM.Gauss.Sizes.lwExpTerm2_Lloop1
#check @RBM.Gauss.Sizes.lwExpTerm2_Lloop2
#check @RBM.Gauss.Sizes.lwExpTerm2_Lloop3
#check @RBM.Gauss.Sizes.lwExpTerm2_Gt_ct
#check @RBM.Gauss.Sizes.lwExpTerm2_BM
#check @RBM.Gauss.Sizes.lwExpTerm2_BM_Lloop
#check @RBM.Gauss.Sizes.lwExpTerm2_BM_X
#check @RBM.Gauss.Sizes.lwExpTerm2_BM_integrable
#check @RBM.Gauss.Sizes.lwExpTerm2_integral_sum3
#check @RBM.Gauss.Sizes.lwExpTerm2_eta_inv_le
-- `Graph/LWExpTerm2.lean` (`namespace RBM.Gauss.LWInst` `:2060-2116`)
#check @RBM.Gauss.LWInst.lwExpTerm2_inst_ker_KK
#check @RBM.Gauss.LWInst.lwExpTerm2_inst_cut
-- `Graph/LWExpTerm.lean` (T2236, 23d83c4, `namespace RBM.Gauss.Sizes` `:43-1210`)
#check @RBM.Gauss.Sizes.LWCutExp
#check @RBM.Gauss.Sizes.LWExpI1
#check @RBM.Gauss.Sizes.LWExpI41
#check @RBM.Gauss.Sizes.lwExpI1_holds
#check @RBM.Gauss.Sizes.lwExpI41_holds
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut
-- `Graph/LWPins.lean` (`namespace RBM.Gauss.Sizes` `:187-503`; `RBM.Gauss.LWInst` `:578-676`)
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Gauss.LWInst.inst_LWtermEXP
-- `Induction/Defs.lean` (`namespace RBM.Gauss.Sizes` `:57-181`, `:278-388`)
#check @RBM.Gauss.Sizes.STKloop
#check @RBM.Gauss.Sizes.STWB
#check @RBM.Gauss.Sizes.STblk
#check @RBM.Gauss.Sizes.STGM
#check @RBM.Gauss.Sizes.STmaxLoop2
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STflowE
-- `Induction/Step34Pins.lean` (`namespace RBM.Gauss.Sizes` `:40-691`)
#check @RBM.Gauss.Sizes.STKward
#check @RBM.Gauss.Sizes.STKI
-- `Loop/KLFinal.lean` (`namespace RBM.Gauss.Sizes` `:186-383`), `Loop/KLUnique.lean` (`namespace RBM.Loop`)
#check @RBM.Gauss.Sizes.stKward_of_flow
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Loop.KLK_rotate
-- `Induction/Step6Kit.lean`, `Step5Kit.lean`, `ScaleFacts.lean`, `ExpAvg.lean` (`namespace RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.st6_prec_det_iff
#check @RBM.Gauss.Sizes.st6_flowE_lt_two
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.st5_Bctl_le_one
#check @RBM.Gauss.Sizes.STBctl_pos
#check @RBM.Gauss.Sizes.STExpAvgAt_of_LWAvgLaw
-- `Loop/GLoopFlow.lean` (`namespace RBM.Gauss`; `Sizes` `:145-204`), `Loop/GLoop.lean` (`namespace RBM.Gauss`)
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
#check @RBM.Gauss.etaT
#check @RBM.Gauss.etaT_pos
#check @RBM.Gauss.etaT_eq_zt_im
-- `Gauss/FineModel.lean` (`namespace RBM.Gauss`, `Sizes` `:511-594`), `Defs/Semicircle.lean` (`namespace RBM`)
#check @RBM.Gauss.Sizes.seqHflow_isHermitian
#check @RBM.norm_mE
#check @RBM.mSigma
-- `Defs/Sizes.lean` (`namespace RBM.Gauss` `:36-248`), `Defs/Block.lean` (`namespace RBM`)
#check @RBM.Gauss.Idx
#check @RBM.Gauss.zdistInf
#check @RBM.Gauss.zdistInf_le_zdistD
#check @RBM.Gauss.zdistD_le_mul_zdistInf
#check @RBM.SB
#check @RBM.sum_norm_SB_row
#check @RBM.SB_isSymm
-- `Defs/RadialSum.lean` (`namespace RBM`), `Loop/PureLoop.lean` (`namespace RBM.Loop`)
#check @RBM.expC
#check @RBM.sum_radial_exp_decay_le
#check @RBM.sum_shift
#check @RBM.Loop.sum_exp_decay_centre
-- `Induction/ConArgDet.lean` (`namespace RBM`)
#check @RBM.sum_gloop_two_ward
#check @RBM.sum_gloop_ward_last

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

namespace T2254Check

/-! ## Section 2. Pin texts (targets drop the suffix `Pin` and the namespace `T2254Check`;
targets 1-5 are theorems whose statements are these bodies, accepted by a term-mode `example`;
targets 6-9 are the merged pins `LWExpI1K`, `LWExpI23K`, `LWExpI41K` and `LwCutExpOfG5'Pin`) -/

/-- Target 1: a kernel with `LWExpKer` has column and row sums bounded uniformly in `n` (and `L`):
`Σ_a ‖K_{ab}‖, Σ_a ‖K_{ba}‖ ≤ C` (`C = C_K · Σ_{x ∈ Z^d} e^{-c_K |x|_∞}`), replacing `Σ_a ‖S^{(B)}_{ab}‖ = 1`. -/
def LwExpTerm4KerSumPin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ), LWExpKer sz K →
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : Zd d (sz.L n)),
      ∑ a : Zd d (sz.L n), ‖K n a b‖ ≤ C ∧ ∑ a : Zd d (sz.L n), ‖K n b a‖ ≤ C

/-- Target 2: `(WI_calL)` for the 2-loops of charge `(s, +)`, both `s`, second label summed, pathwise:
`W^d Σ_b ‖𝓛^{(2)}_{(s,+),(a,b)}‖ ≤ η_t⁻¹ ‖𝓛^{(1)}_{+,a}‖` (`s = false`: the merged private
`lwExpTerm_ward_sum_le`; `s = true`: `|tr(G E_a G E_b)| ≤ ½(𝓛_{(-,+),(a,b)} + 𝓛_{(-,+),(b,a)})`, then Ward
for each, the second by `Σ_b 𝓛_{(-,+),(b,a)} = W^{-d} tr(G*G E_a)`). -/
def LwExpTerm4WardPin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → t < 1 →
    ∀ (s : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ),
      (((sz.W n : ℕ) : ℝ) ^ d) * ∑ b : Zd d (sz.L n), ‖Lloop sz n E t ![s, true] ![a, b] ω‖ ≤
        (etaT E t)⁻¹ * ‖Lloop sz n E t ![true] ![a] ω‖

/-- Target 3: `(WI_calK)` for `𝒦^{(2)}_{(s,+)}`, both `s`, FIRST label summed (`STKward` at `k = 2`, charge
`![true, s]`, after `KLK_rotate`; `s = false` is the merged private `lwExpTerm_Kward`). -/
def LwExpTerm4KwardPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        Prec sz (U := fun n => Bool × Zd d (sz.L n))
          (fun n p _ => (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n),
              ‖STKloop sz n (STflowE z n) (t n) ![p.1, true] ![a, p.2]‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹)

/-- Target 4: the diagonal entries `max_x |(G_t)_{xx}| ≺ 1` from `STLocalEntry` at `x = y`
(`STWB sz n τ 0 = sz.Bctl n τ` by `rfl`, `B ≤ 1` eventually by `st5_Bctl_le_one`, `‖m‖ = 1`). -/
def LwExpTerm4DiagPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t →
        Prec sz (U := fun n => Idx d (sz.L n) (sz.W n))
          (fun n x ω => ‖Gt sz n (STflowE z n) (t n) true ω x x‖)
          (fun _ _ _ => 1)

/-- Target 5: the 3-loop sum of `I₂`, `I₃` (`B:43-49`), pathwise: with `A ≥ max_x |G_{xx}|`,
`W^d Σ_a ‖𝓛^{(3)}_{(+,+,σ),(a,b,c)}‖ ≤ η_t⁻¹ A (max_{u,v} 𝓛^{(2)}_{(-,+),(u,v)})^{1/2}`
(the vertex Ward identity `Σ_y |G_{xy}|² = Im G_{xx}/η` for the summed vertex, Cauchy–Schwarz twice:
over `y`, and over the `W^{2d}` pairs `(z, x) ∈ [b] × [c]`, whose square sum is `𝓛^{(2)}_{(-,+)}`). -/
def LwExpTerm4L3Pin : Prop :=
  ∀ (d : ℕ) (sz : Sizes d) (n : ℕ) (E t : ℝ), |E| < 2 → t < 1 →
    ∀ (σ : Bool) (b c : Zd d (sz.L n)) (ω : sz.SeqΩ) (A : ℝ),
      (∀ x : Idx d (sz.L n) (sz.W n), ‖Gt sz n E t true ω x x‖ ≤ A) →
      (((sz.W n : ℕ) : ℝ) ^ d) * ∑ a : Zd d (sz.L n), ‖Lloop sz n E t ![true, true, σ] ![a, b, c] ω‖ ≤
        (etaT E t)⁻¹ * A * Real.sqrt (STmaxLoop2 sz n E t ω)

/-- Target 9: with LW-14d, `LWCutExp` needs only `LWExpG5'` (LW-14c). -/
def LwCutExpOfG5'Pin (d : ℕ) : Prop := LWExpG5' d → LWCutExp d

/-! ## Section 3. Instance shapes (`d = 3`; Prop-valued, no proof obligations) -/

example : Prop := LwCutExpOfG5'Pin 3
example : Prop := LwExpTerm4KwardPin 3
example : Prop := LwExpTerm4DiagPin 3
example : Prop := LWExpI1K 3 ∧ LWExpI23K 3 ∧ LWExpI41K 3
example : Prop := LwExpTerm4WardPin ∧ LwExpTerm4L3Pin ∧ LwExpTerm4KerSumPin
example : Prop :=
  LWExpKer RBM.Gauss.SizesInst.sz0
    (fun n => lwExpTerm2_KK RBM.Gauss.SizesInst.sz0 n
      (STflowE RBM.Gauss.InductionDefsInst.z0 n) (RBM.Gauss.InductionDefsInst.tInst n))

end T2254Check

end RBM.Gauss.Sizes
