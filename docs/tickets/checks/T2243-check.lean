/-
T2243 (LW-14b) check file: merged names (section 1) and the pin texts of the targets (section 2).
No proofs, no `sorry`, no `by`.  Compiles on `main` (fd80185) as is.
-/
import RBM3D.Graph.LWExpTerm
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWSizeClaim
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step5Kit
import RBM3D.Green.IBPPoly

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

/-! ## Section 1. Merged names (each in the namespace of its enclosing `namespace … end` block) -/

-- `Graph/LWPins.lean` (`namespace RBM.Gauss.Sizes` `:187-503`; `namespace RBM.Graph` before)
#check @RBM.Gauss.Sizes.LWcut
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWAvgLaw
#check @RBM.Gauss.Sizes.LWtermEXP
#check @RBM.Graph.LWggExp
-- `Graph/LWExpTerm.lean` (T2236, `namespace RBM.Gauss.Sizes`)
#check @RBM.Gauss.Sizes.LWCutExp
#check @RBM.Gauss.Sizes.LWExpI1
#check @RBM.Gauss.Sizes.LWExpI41
#check @RBM.Gauss.Sizes.LWExpG5
#check @RBM.Gauss.Sizes.lwTermEXP_of_cut
#check @RBM.Gauss.Sizes.lwExpI1_holds
#check @RBM.Gauss.Sizes.lwExpI41_holds
#check @RBM.Gauss.Sizes.lwExpTerm_prec_integral
-- `Graph/LWGGExp.lean` (`namespace RBM.Graph`)
#check @RBM.Graph.oe2x_integral
#check @RBM.Graph.lwGGExp_holds
-- `Graph/LWStein.lean` (`namespace RBM.Graph`)
#check @RBM.Graph.lwG
#check @RBM.Graph.lwPoly
#check @RBM.Graph.dhSample
#check @RBM.Graph.dhSample_lwG
#check @RBM.Graph.dhSample_lwG_star
#check @RBM.Graph.lwStein_dh_mul
#check @RBM.Graph.lwStein_dh_sum
#check @RBM.Graph.lwSplus
-- `Graph/LWSizeClaim.lean` (`namespace RBM.Graph`)
#check @RBM.Graph.lwSplus_eq
#check @RBM.Graph.lwSpOf_eq
#check @RBM.Graph.lwSplus_decay
-- `Propagator/Basic.lean`, `Defs/Block.lean` (`namespace RBM`)
#check @RBM.Theta
#check @RBM.SB
#check @RBM.sum_SB_row
-- `Loop/GLoopFlow.lean` (`namespace RBM.Gauss`, `namespace Sizes`)
#check @RBM.Gauss.Sizes.Gt
#check @RBM.Gauss.Sizes.Lloop
-- `Induction/ExpAvg.lean`, `Induction/Step6Kit.lean`, `Induction/Step5Kit.lean`, `Loop/KLFinal.lean`
#check @RBM.Gauss.Sizes.STExpAvgAt_of_LWAvgLaw
#check @RBM.Gauss.Sizes.st6_mE_im_ge
#check @RBM.Gauss.Sizes.st6_flowE_le
#check @RBM.Gauss.Sizes.st5_t_lt_one
#check @RBM.Gauss.Sizes.stKbound_of_flow
#check @RBM.Gauss.Sizes.stKward_of_flow
-- `Induction/ConArgDet.lean` (`namespace RBM`), `Green/IBPPoly.lean` (`namespace RBM.Green`)
#check @RBM.sum_gloop_two_ward
#check @RBM.Green.gaussIBP
-- `Induction/Defs.lean` (premises)
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STDecay

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

namespace T2243Check

/-! ## Section 2. Pin texts (targets drop the suffix `Pin` and the namespace `T2243Check`) -/

/-- Vocabulary: a block kernel with exponential decay, constants uniform in `n`. -/
def LWExpKerPin {d : ℕ} (sz : Sizes d) (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n : ℕ) (a b : Zd d (sz.L n)),
    ‖K n a b‖ ≤ C * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))

/-- Vocabulary: the block kernel of `W^d S⁺` (`lwSpOf_eq`: `S⁺ = t · Lift(S^{(B)} Θ_{t m²})`),
`K⁺ = t S^{(B)} Θ_{t m(E)²}`. -/
noncomputable def LWExpKpPin {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) :
    Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (t : ℂ) • (SB d (sz.L n) (sz.lam n) * RBM.Theta d (sz.L n) (sz.lam n) ((t : ℂ) * mE E ^ 2))

/-- `I₁`, `J₁` (`(eq:termI1)`) with a general decaying first kernel `K` (`K = S^{(B)}` is `LWExpI1`). -/
def LWExpI1KPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKerPin sz K →
        LWAvgLaw sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖∑ a₁, K n a₁ (p.2 1) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
                Lloop sz n (STflowE z n) (t n) p.1.2 p.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (sz.Bctl n (t n)) ^ 3)

/-- `I₂` (`p.1.1 = true`), `I₃` (`p.1.1 = false`) (`(eq:termI2)`), and `J₂`, `J₃`, with a general decaying first
kernel: `p = ((sel, σo), (ac, ao))`, `‖W^d Σ K_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼[X_{a₁} X_{a'} 𝓛^{(3)}_{(+,+,σo),(a'',ac,ao)}]‖
≺ η_t⁻¹ (W^{-d}B_{t,0})^{5/2}`, `(a', a'') = (a₃, a₂)` or `(a₂, a₃)`. -/
def LWExpI23KPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKerPin sz K →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              K n a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![true] ![a₁] ω - mSigma (STflowE z n) true) *
                (Lloop sz n (STflowE z n) (t n) ![true] ![if p.1.1 then a₃ else a₂] ω -
                  mSigma (STflowE z n) true) *
                Lloop sz n (STflowE z n) (t n) ![true, true, p.1.2]
                  ![if p.1.1 then a₂ else a₃, p.2 0, p.2 1] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- `I₄₁`, `J₄₁` (`(eq:termI41)`) with a general decaying first kernel and the two 2-loops of charge
`(s, +)`: `p = ((σ₁, s), (a, b))` (`K = S^{(B)}`, `s = false` is `LWExpI41`). -/
def LWExpI41KPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKerPin sz K →
        LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × Bool) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              K n a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
                Lloop sz n (STflowE z n) (t n) ![p.1.2, true] ![p.2 0, a₂] ω *
                Lloop sz n (STflowE z n) (t n) ![p.1.2, true] ![a₃, p.2 1] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3)

/-- **`LWExpG5'`** (`I₄₂`, `J₄₂`; `(eq;I42inG)`, `(eq;EGxy:x=y)`): the 5-loop of `LWExpG5` with the first kernel
`S^{(B)}` (`p.1.1 = false`) or `K⁺` (`p.1.1 = true`, the `S⁺` edge of `J₄`) and last charge `p.1.2`
(`false`: `σo = -`, `true`: `σo = +`); `p.1 = (false, false)` is `LWExpG5`.  Owed: LW-14c. -/
def LWExpG5'Pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (if p.1.1.1 then LWExpKpPin sz n (STflowE z n) (t n) a₁ a₂
                else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
              (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, p.1.1.2]
                ![a₂, a₁, a₃, p.1.2 1, p.1.2 0] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- Target 7: the assembly `(eq:ELW_term)` → `LWCutExp` from the five term bounds. -/
def LwCutExpOfTermsPin (d : ℕ) : Prop :=
  LWExpI1KPin d → LWExpI23KPin d → LWExpI41KPin d → LWExpG5'Pin d → LWCutExp d

/-- Target 8: `LWExpG5'` contains `LWExpG5` (the case `p.1 = (false, false)`). -/
def LwExpG5OfG5'Pin (d : ℕ) : Prop := LWExpG5'Pin d → LWExpG5 d

/-- Target 9: the merged `I₁`, `I₄₁` are the case `K = S^{(B)}` (`s = false`) of the kernel pins. -/
def LwExpI1OfKPin (d : ℕ) : Prop := LWExpI1KPin d → LWExpI1 d
def LwExpI41OfKPin (d : ℕ) : Prop := LWExpI41KPin d → LWExpI41 d

/-! ## Section 3. Instance shapes (`d = 3`; Prop-valued, no proof obligations) -/

example : Prop := LwCutExpOfTermsPin 3
example : Prop := LWExpG5'Pin 3
example : Prop :=
  LWExpKerPin RBM.Gauss.SizesInst.sz0
    (fun n => SB 3 (RBM.Gauss.SizesInst.sz0.L n) (RBM.Gauss.SizesInst.sz0.lam n))

end T2243Check

end RBM.Gauss.Sizes
