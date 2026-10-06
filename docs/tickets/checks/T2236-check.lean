/-
T2236 check file (LW-14a, `lem:LWterm_EXP` part a of three).  Compiles on `main` (b750bf3) as is:
imports of merged modules, `#check` of merged names, `def … : Prop` pin texts.  No proofs.
-/
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWGGExp
import RBM3D.Induction.ExpAvg
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLFinal
import RBM3D.Green.IBPPoly

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## Section 1: merged names used (namespace from the enclosing `namespace … end` blocks) -/

-- `Graph/LWPins.lean` (975f4ff), `namespace RBM.Gauss.Sizes` (`:187-503`)
#check @RBM.Gauss.Sizes.LWtermEXP        -- :311
#check @RBM.Gauss.Sizes.LWE              -- :218
#check @RBM.Gauss.Sizes.LWcut            -- :211
#check @RBM.Gauss.Sizes.LWAvgLaw         -- :303
#check @RBM.Gauss.Sizes.LWS              -- :194
-- `Induction/Defs.lean`, `namespace RBM.Gauss.Sizes`
#check @RBM.Gauss.Sizes.STKloop          -- :64
#check @RBM.Gauss.Sizes.STWB             -- :69
#check @RBM.Gauss.Sizes.STGM             -- :77
#check @RBM.Gauss.Sizes.STLK             -- :104
#check @RBM.Gauss.Sizes.STLmax           -- :112
#check @RBM.Gauss.Sizes.STDecay          -- :121
#check @RBM.Gauss.Sizes.STLocalEntry     -- :151
#check @RBM.Gauss.Sizes.STKbound         -- :174
#check @RBM.Gauss.Sizes.STflowE          -- :283
#check @RBM.Gauss.Sizes.STFlow           -- :286
-- `Defs/Sizes.lean`
#check @RBM.Gauss.Sizes.Bctl             -- :214
-- `Loop/GLoopFlow.lean`, `namespace RBM.Gauss` / `namespace Sizes`
#check @RBM.Gauss.Sizes.Lloop            -- :158
#check @RBM.Gauss.Sizes.Gt               -- :152
-- `Induction/Step6Pins.lean` (d0d79ce era), `namespace RBM.Gauss.Sizes` (`:167-274`)
#check @RBM.Gauss.Sizes.STExpAvgAt       -- :177
#check @RBM.Gauss.Sizes.STImproveExpAver -- :191
-- `Induction/ExpAvg.lean` (d0d79ce), `namespace RBM.Gauss.Sizes` (`:52-883`)
#check @RBM.Gauss.Sizes.STExpAvgAt_of_LWAvgLaw  -- :799
#check @RBM.Gauss.Sizes.stImproveExpAver_holds  -- :879
-- `Loop/KLFinal.lean` (471b643), `namespace RBM.Gauss.Sizes` (`:186-383`)
#check @RBM.Gauss.Sizes.stKbound_of_flow -- :302
#check @RBM.Gauss.Sizes.stKward_of_flow  -- :308
-- `Induction/ConArgDet.lean` (bbd22a5), `namespace RBM` (`:61-…`)
#check @RBM.sum_gloop_ward_last          -- :268
-- `Graph/LWGGExp.lean` (5c69cb4), `namespace RBM.Graph` (`:56-1748`)  [for LW-14b; listed for the interface]
#check @RBM.Graph.oe2x_integral          -- :312
#check @RBM.Graph.lwGGExp_holds          -- :435
-- `Green/IBPPoly.lean` (3b8c687), `namespace RBM.Green` (`:49-1157`)
#check @RBM.Green.gaussIBP               -- :305

namespace T2236Check

/-! ## Section 2: pins (the file's definitions are these, without the suffix `Pin`) -/

/-- **One cut term of `(eq:EGC)` in expectation** (`B:10-13`, `(eq:ELW_term)` read at the loop level):
under the premises of `LWtermEXP` (`LWPins.lean:311`, verbatim), for both charges `(σc, σo)` and both
blocks `(ac, ao)`, `‖𝔼 LWcut‖ ≺ (1-t)⁻¹ (W^{-d}B_{t,0})^{5/2}` on the index set `ĝ²/L^d ≤ 1 - t`. -/
def LWCutExpPin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Bool × Bool) × (Zd d (sz.L n) × Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖∫ ω, LWcut sz n (STflowE z n) (t n) p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-- Target 2: the reduction `LWE = LWcut + LWcut` (`LWPins.lean:218`). -/
def LwTermEXPOfCutPin (d : ℕ) : Prop := LWCutExpPin d → LWtermEXP d

/-- **The term `I₁`** (`(eq:termI1)`, `B:43-47`) at the loop level, all charges: `p = ((σ₁, σ), (a, b))`,
`‖Σ_{a₁} S^{(B)}_{a₁b} 𝔼[(𝓛^{(1)}_{σ₁,a₁} - m(σ₁)) 𝓛^{(2)}_{σ,(a,b)}]‖ ≺ (W^{-d}B_{t,0})³`
(`𝔼 tr(Ǧ E_{a₁}) · 𝒦^{(2)}` by `STExpAvgAt` and `STKbound`; `𝔼[tr(Ǧ E_{a₁}) (𝓛-𝒦)^{(2)}]` by `LWAvgLaw`, `STLK`). -/
def LWExpI1Pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖∑ a₁, (SB d (sz.L n) (sz.lam n) a₁ (p.2 1) : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
                Lloop sz n (STflowE z n) (t n) p.1.2 p.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (sz.Bctl n (t n)) ^ 3)

/-- **The term `I₄₁`** (`(eq:termI41)`, `B:66-80`) at the loop level: `p = (σ₁, (a, b))`,
`‖W^d Σ_{a₁,a₂,a₃} S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼[(𝓛^{(1)}_{σ₁,a₁} - m(σ₁)) 𝓛^{(2)}_{(-,+),(a,a₂)} 𝓛^{(2)}_{(-,+),(a₃,b)}]‖
≺ η_t⁻¹ (W^{-d}B_{t,0})³` (Ward `(WI_calL)` for `Σ_{a₂}`, `(WI_calK)` for `Σ_{a₃}`). -/
def LWExpI41Pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => Bool × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1] ![a₁] ω - mSigma (STflowE z n) p.1) *
                Lloop sz n (STflowE z n) (t n) ![false, true] ![p.2 0, a₂] ω *
                Lloop sz n (STflowE z n) (t n) ![false, true] ![a₃, p.2 1] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ 3)

/-- **The term `I₄₂`** (`(eq;I42inG)`, `(eq;EGxy:x=y)`, `B:81-90`): the 5-loop
`‖W^d Σ_{a₁,a₂,a₃} S^{(B)}_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼 𝓛^{(5)}_{(+,+,+,+,-),(a₂,a₁,a₃,b,a)}‖ ≺ η_t⁻¹ (W^{-d}B_{t,0})^{5/2}`
under the premises of `LWtermEXP`.  Stated here (interface of LW-14b/c), proved in LW-14c. -/
def LWExpG5Pin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : Fin 2 → Zd d (sz.L n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, false]
                ![a₂, a₁, a₃, p.1 1, p.1 0] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))

/-! ## Section 3: shapes of the instances (Prop-valued examples, no proof obligations) -/

example : Prop := LwTermEXPOfCutPin 3
example : Prop := LWExpI1Pin 3 ∧ LWExpI41Pin 3
example : Prop := LWExpG5Pin 3 → LWCutExpPin 3

end T2236Check
