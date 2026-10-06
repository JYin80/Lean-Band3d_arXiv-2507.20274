/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpTerm
import RBM3D.Graph.LWGGExp
import RBM3D.Graph.LWSizeClaim
import RBM3D.Induction.Step6Kit
import RBM3D.Induction.Step5Kit
import RBM3D.Green.IBPPoly

/-!
# LW-14b (T2243): `lem:LWterm_EXP`, part b: the expansion side

Paper: arXiv:2507.20274, `paper/tex/6_Step6_two_loop.tex:83-88` (`lem:LWterm_EXP`), proof
`paper/tex/B_graphical_lemmas.tex:7-121` (`B:line`): the reduction `(eq:ELW_term)` (`B:10-13`),
the eight terms `I₁…J₄` (`B:17-34`), `(eq:termI1)`, `(eq:termI2)`, the `∂` split `I₄ = I₄₁ + I₄₂`,
`(eq:termI41)`, `(eq;I42inG)`; the `GG` expansion `(Oe2x)` (`7_8:334-349`).  No port (RBM2D has no
light-weight layer).

## What is proved

`lwCutExp_of_terms : LWExpI1K d → LWExpI23K d → LWExpI41K d → LWExpG5' d → LWCutExp d` (target 7):
the expectation of one cut `LWcut` of `(eq:EGC)` is, up to the kernels, a sum of five loop-level
terms, each of which is the expression of one of the four pinned term bounds (`LWExpI1K`,
`LWExpI23K`, `LWExpI41K`, `LWExpG5'`, section 1: the check file
`docs/tickets/checks/T2243-check.lean`, section 2, verbatim up to the suffix `Pin`; they are
proved in LW-14d / LW-14c).

## Route

* §2-§4, §8: **no probability**.  Block weights `dw_a(x) = W^{-d} 1[x ∈ [a]]`, loops as nested
  sums `L₂, L₃, L₄` (`tr(A₁ D_u A₂ D_v …)`), the block lift `Σ_y c₀ M_{a,[y]} F_y = Σ_b M_{ab} Σ_y
  dw_b(y) F_y`, the kernel summation `lwExpTerm2_keyQ` (`Σ_x dw_a(x)(m F_x + m³ Σ_y S⁺_{xy} F_y) =
  Σ_{a'} (m δ_{aa'} + m³ K⁺_{aa'}) Σ_y dw_{a'}(y) F_y`), the five block evaluations
  `lwExpTerm2_eval1/3/5/7a/7b`, `lwExpTerm2_alg`, `lwExpTerm2_assemble`.
* §5-§7: the bridge `Lloop sz n E t σ a ω` = a nested sum of the entries of `G_t(σ)` (`blockMat`,
  `Eblk`), the resolvent polynomial `f = X_a Ĝ_{co}` (`lwPoly`), `∂_{h_{βv}} f` through
  `lwStein_dh_mul`, `dhSample_lwG`, `dhSample_lwG_star` (`lwExpTerm2_dh`: `-M₁_{vβ} Ĝ_{co} - X
  Ĝ_{cβ} Ĝ_{vo}` for both charges), `(Oe2x)` at one triple `(α, c, o)` through `oe2x_integral`
  (`lwExpTerm2_triple`), and its sum over `α ∈ [a₂]`, `c ∈ [ac]`, `o ∈ [ao]` (`lwExpTerm2_block`).
* §10-§11: the kernel `K = S^{(B)}(m + m³K⁺)` (`m(1 - m²S)⁻¹ = m + m³S⁺`) collects the `I` and the
  `J` terms: `𝔼 LWcut(+, σ) = P_a + t P_b(+) + t P_b(-) + m P_d + t P_c`
  (`lwExpTerm2_cut_expand`), with `t S^{(B)}(m + m³ K⁺) = m K⁺` (`lwExpTerm2_tKK`, from
  `lwExpTerm2_Kp_split`), so `I₄₂ + J₄₂` is `m` times the 5-loop with the first kernel `K⁺`
  (`LWExpG5'` with `p.1.1.1 = true`).
* §12: `conj LWcut(-, σ, ac, ao) = LWcut(+, -σ, ao, ac)`; `t = 0` (`LWcut = 0`): §14.
* §13: `LWExpKer` of `S^{(B)}`, `K⁺` (`lwSplus_decay`, `lwSpOf_eq`) and `K`.
* §14-§15: the `≺`-assembly with `η_t⁻¹ ≤ (2/√(2κ)) (1-t)⁻¹`, `B ≤ 1`; targets 8-9; §16 the
  compiled instances.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Graph RBM.Green

/-! ## 1. Vocabulary and pins (the check file `docs/tickets/checks/T2243-check.lean`, section 2, without the suffix `Pin`) -/

/-- Vocabulary: a block kernel with exponential decay, constants uniform in `n`. -/
def LWExpKer {d : ℕ} (sz : Sizes d) (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n : ℕ) (a b : Zd d (sz.L n)),
    ‖K n a b‖ ≤ C * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))

/-- Vocabulary: the block kernel of `W^d S⁺` (`lwSpOf_eq`: `S⁺ = t · Lift(S^{(B)} Θ_{t m²})`),
`K⁺ = t S^{(B)} Θ_{t m(E)²}`. -/
noncomputable def LWExpKp {d : ℕ} (sz : Sizes d) (n : ℕ) (E t : ℝ) :
    Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  (t : ℂ) • (SB d (sz.L n) (sz.lam n) * RBM.Theta d (sz.L n) (sz.lam n) ((t : ℂ) * mE E ^ 2))

/-- `I₁`, `J₁` (`(eq:termI1)`) with a general decaying first kernel `K` (`K = S^{(B)}` is `LWExpI1`). -/
def LWExpI1K (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKer sz K →
        LWAvgLaw sz (STflowE z) t → STLK sz (STflowE z) t →
        Prec sz (U := fun n => (Bool × (Fin 2 → Bool)) × (Fin 2 → Zd d (sz.L n)))
          (fun n p _ => ‖∑ a₁, K n a₁ (p.2 1) *
              ∫ ω, (Lloop sz n (STflowE z n) (t n) ![p.1.1] ![a₁] ω - mSigma (STflowE z n) p.1.1) *
                Lloop sz n (STflowE z n) (t n) p.1.2 p.2 ω ∂(sz.seqP)‖)
          (fun n _ _ => (sz.Bctl n (t n)) ^ 3)

/-- `I₂` (`p.1.1 = true`), `I₃` (`p.1.1 = false`) (`(eq:termI2)`), and `J₂`, `J₃`, with a general decaying first
kernel: `p = ((sel, σo), (ac, ao))`, `‖W^d Σ K_{a₁a₂} S^{(B)}_{a₂a₃} 𝔼[X_{a₁} X_{a'} 𝓛^{(3)}_{(+,+,σo),(a'',ac,ao)}]‖
≺ η_t⁻¹ (W^{-d}B_{t,0})^{5/2}`, `(a', a'') = (a₃, a₂)` or `(a₂, a₃)`. -/
def LWExpI23K (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKer sz K →
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
def LWExpI41K (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ, LWExpKer sz K →
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
def LWExpG5' (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalEntry sz (STflowE z) t → LWAvgLaw sz (STflowE z) t → STLmax sz (STflowE z) t →
        STLK sz (STflowE z) t → STDecay sz (STflowE z) t →
        Prec sz (U := fun n => {_p : (Bool × Bool) × (Fin 2 → Zd d (sz.L n)) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n})
          (fun n p _ => ‖(((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃,
              (if p.1.1.1 then LWExpKp sz n (STflowE z n) (t n) a₁ a₂
                else (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ)) *
              (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
              ∫ ω, Lloop sz n (STflowE z n) (t n) ![true, true, true, true, p.1.1.2]
                ![a₂, a₁, a₃, p.1.2 1, p.1.2 0] ω ∂(sz.seqP)‖)
          (fun n _ _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))


/-! ## 2. Block-weighted sums: the algebra of `(Oe2x)` at the block level (no probability) -/

section Alg

variable {ι B : Type*} [Fintype ι] [DecidableEq ι] [Fintype B] [DecidableEq B]

/-- The block weight `(E_a)_{xx} = W^{-d} 1[x ∈ [a]]` on a block-labelled index set. -/
def lwExpTerm2_dw (bl : ι → B) (c₀ : ℂ) (a : B) (x : ι) : ℂ := if bl x = a then c₀ else 0

variable (bl : ι → B) (c₀ : ℂ)

theorem lwExpTerm2_dw_sum (hc : ∀ a, ((Finset.univ.filter fun x => bl x = a).card : ℂ) * c₀ = 1) (a : B) :
    ∑ x, lwExpTerm2_dw bl c₀ a x = 1 := by
  simp only [lwExpTerm2_dw, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  exact hc a

theorem lwExpTerm2_dw_blocks (x : ι) (g : B → ℂ) :
    ∑ a, lwExpTerm2_dw bl c₀ a x * g a = c₀ * g (bl x) := by
  simp only [lwExpTerm2_dw]
  simp [ite_mul, Finset.sum_ite_eq]

theorem lwExpTerm2_dw_mul (a : B) (x : ι) (g : B → ℂ) :
    lwExpTerm2_dw bl c₀ a x * g (bl x) = lwExpTerm2_dw bl c₀ a x * g a := by
  unfold lwExpTerm2_dw
  by_cases h : bl x = a <;> simp [h]

theorem lwExpTerm2_dw_mul_self (a b : B) (x : ι) :
    lwExpTerm2_dw bl c₀ a x * lwExpTerm2_dw bl c₀ b x =
      if a = b then c₀ * lwExpTerm2_dw bl c₀ a x else 0 := by
  unfold lwExpTerm2_dw
  by_cases h : bl x = a <;> by_cases h' : bl x = b <;> by_cases hab : a = b <;> simp_all

/-- The block-lift sum: `Σ_y c₀ M_{a,[y]} F_y = Σ_b M_{ab} Σ_y dw_b(y) F_y`. -/
theorem lwExpTerm2_lift_sum (M : B → B → ℂ) (a : B) (F : ι → ℂ) :
    ∑ y, c₀ * M a (bl y) * F y = ∑ b, M a b * ∑ y, lwExpTerm2_dw bl c₀ b y * F y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have := lwExpTerm2_dw_blocks bl c₀ y (fun b => M a b)
  calc c₀ * M a (bl y) * F y = (∑ b, lwExpTerm2_dw bl c₀ b y * M a b) * F y := by rw [this]
    _ = _ := by rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun b _ => by ring

/-- **`Σ_x dw_a(x) (m F_x + m³ Σ_y S⁺_{xy} F_y) = Σ_{a'} (m δ_{aa'} + m³ K⁺_{aa'}) Σ_y dw_{a'}(y) F_y`**
(`S⁺_{xy} = c₀ K⁺_{[x][y]}`): the block form of the kernel `m (1 - m² S)⁻¹ = m + m³ S⁺`. -/
theorem lwExpTerm2_keyQ (hc : ∀ a, ((Finset.univ.filter fun x => bl x = a).card : ℂ) * c₀ = 1)
    (Sp : ι → ι → ℂ) (Kp : B → B → ℂ) (hSp : ∀ x y, Sp x y = c₀ * Kp (bl x) (bl y)) (m : ℂ)
    (a : B) (F : ι → ℂ) :
    ∑ x, lwExpTerm2_dw bl c₀ a x * (m * F x + m ^ 3 * ∑ y, Sp x y * F y) =
      ∑ a', (m * (if a = a' then 1 else 0) + m ^ 3 * Kp a a') * ∑ y, lwExpTerm2_dw bl c₀ a' y * F y := by
  have h1 : ∑ x, lwExpTerm2_dw bl c₀ a x * (m * F x) =
      ∑ a', m * (if a = a' then 1 else 0) * ∑ y, lwExpTerm2_dw bl c₀ a' y * F y := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∑ x, lwExpTerm2_dw bl c₀ a x * (∑ y, Sp x y * F y) =
      ∑ a', Kp a a' * ∑ y, lwExpTerm2_dw bl c₀ a' y * F y := by
    have e : ∀ x, lwExpTerm2_dw bl c₀ a x * (∑ y, Sp x y * F y) =
        lwExpTerm2_dw bl c₀ a x * (∑ y, c₀ * Kp a (bl y) * F y) := by
      intro x
      have := lwExpTerm2_dw_mul bl c₀ a x (fun b => ∑ y, c₀ * Kp b (bl y) * F y)
      simp only [hSp] at *
      rw [← this]
    simp_rw [e]
    rw [← Finset.sum_mul, lwExpTerm2_dw_sum bl c₀ hc a, one_mul, lwExpTerm2_lift_sum]
  have e : ∀ x, lwExpTerm2_dw bl c₀ a x * (m * F x + m ^ 3 * ∑ y, Sp x y * F y) =
      lwExpTerm2_dw bl c₀ a x * (m * F x) + m ^ 3 * (lwExpTerm2_dw bl c₀ a x * ∑ y, Sp x y * F y) :=
    fun x => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a' _ => by ring


/-! ### Loops as nested sums (the trace of a product with diagonal weights) -/

/-- `tr(A₁ D_u A₂ D_v)`. -/
def lwExpTerm2_L2 (A₁ A₂ : Matrix ι ι ℂ) (u v : ι → ℂ) : ℂ :=
  ∑ x, ∑ y, A₁ x y * u y * (A₂ y x * v x)

/-- `tr(A₁ D_u A₂ D_v A₃ D_w)`. -/
def lwExpTerm2_L3 (A₁ A₂ A₃ : Matrix ι ι ℂ) (u v w : ι → ℂ) : ℂ :=
  ∑ x, ∑ y, ∑ z, A₁ x y * u y * (A₂ y z * v z * (A₃ z x * w x))

/-- `tr(A₁ D_{u₁} A₂ D_{u₂} A₃ D_{u₃} A₄ D_{u₄})`. -/
def lwExpTerm2_L4 (A₁ A₂ A₃ A₄ : Matrix ι ι ℂ) (u₁ u₂ u₃ u₄ : ι → ℂ) : ℂ :=
  ∑ x₀, ∑ x₁, ∑ x₂, ∑ x₃,
    A₁ x₀ x₁ * u₁ x₁ * (A₂ x₁ x₂ * u₂ x₂ * (A₃ x₂ x₃ * u₃ x₃ * (A₄ x₃ x₀ * u₄ x₀)))

/-- The centred trace `tr(Ǧ D_a) = Σ_x dw_a(x) (G_{xx} - m)`. -/
def lwExpTerm2_Xv (G : Matrix ι ι ℂ) (m : ℂ) (u : ι → ℂ) : ℂ := ∑ x, u x * (G x x - m)


section Eval

theorem lwExpTerm2_sum3_rot {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

theorem lwExpTerm2_sum3_rot' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ a, ∑ b, f a b c :=
  (lwExpTerm2_sum3_rot (fun c a b => f a b c)).symm

theorem lwExpTerm2_sum4_rot' {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ a, ∑ b, ∑ c, f a b c d := by
  have : ∀ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ d, ∑ b, ∑ c, f a b c d := fun a => lwExpTerm2_sum3_rot' (f a)
  rw [Finset.sum_congr rfl fun a _ => this a]
  exact Finset.sum_comm

theorem lwExpTerm2_sum4_rot {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d :=
  (lwExpTerm2_sum4_rot' (fun b c d a => f a b c d)).symm

theorem lwExpTerm2_sum3_rev {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [lwExpTerm2_sum3_rot']
  exact Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- `tr(A₁ D_u A₂ D_v A₃ D_w)` with the third vertex outermost (the nest of the expansion sums). -/
theorem lwExpTerm2_L3_cov (A₁ A₂ A₃ : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    lwExpTerm2_L3 A₁ A₂ A₃ u v w =
      ∑ z, ∑ x, ∑ y, v z * w x * u y * (A₁ x y * (A₂ y z * A₃ z x)) := by
  unfold lwExpTerm2_L3
  rw [lwExpTerm2_sum3_rot']
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable (t : ℂ) (SB' : B → B → ℂ) (G Gs : Matrix ι ι ℂ) (m : ℂ) (S : Matrix ι ι ℂ)

theorem lwExpTerm2_S_sum (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (v : ι) (F : ι → ℂ) :
    ∑ β, S v β * F β = ∑ b, (t * SB' (bl v) b) * ∑ β, lwExpTerm2_dw bl c₀ b β * F β := by
  simp_rw [hS]
  exact lwExpTerm2_lift_sum bl c₀ (fun a b => t * SB' a b) (bl v) F

/-- The term `Φ₁` (the `δ_{xy}`/`S⁺_{xy}` terms of `(Oe2x)`): `δ_{vc}` against the weight `dw_{a'}`. -/
theorem lwExpTerm2_eval1 (a' ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        ((if v = c then 1 else 0) * G o v * (X₁ * Gs c o)) =
      (if a' = ac then c₀ else 0) * X₁ *
        lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ ao) (lwExpTerm2_dw bl c₀ ac) := by
  unfold lwExpTerm2_L2
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single c (fun v _ hv => by simp [hv]) (fun h => absurd (Finset.mem_univ c) h)]
  simp only [ite_true, one_mul]
  have h := lwExpTerm2_dw_mul_self bl c₀ a' ac c
  calc lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' c * (G o c * (X₁ * Gs c o))
      = (lwExpTerm2_dw bl c₀ a' c * lwExpTerm2_dw bl c₀ ac c) * (lwExpTerm2_dw bl c₀ ao o * (G o c * (X₁ * Gs c o))) := by ring
    _ = _ := by
      rw [h]
      by_cases hh : a' = ac
      · subst hh; simp only [ite_true]; ring
      · simp [hh]

/-- The weights of the `X`-sum `Σ_β S_{vβ}(G_{ββ} - m)` over a block. -/
theorem lwExpTerm2_eval3 (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (a' ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        ((∑ β, S v β * (G β β - m)) * (G v c * G o v * (X₁ * Gs c o))) =
      (t * ∑ b, SB' a' b * lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ b)) * X₁ *
        lwExpTerm2_L3 G G Gs (lwExpTerm2_dw bl c₀ a') (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao) := by
  set K : ℂ := ∑ b, (t * SB' a' b) * lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ b) with hK
  have hv : ∀ v, lwExpTerm2_dw bl c₀ a' v * (∑ β, S v β * (G β β - m)) = lwExpTerm2_dw bl c₀ a' v * K := by
    intro v
    rw [lwExpTerm2_S_sum bl c₀ t SB' S hS v (fun β => G β β - m)]
    have := lwExpTerm2_dw_mul bl c₀ a' v (fun a => ∑ b, (t * SB' a b) * ∑ β, lwExpTerm2_dw bl c₀ b β * (G β β - m))
    beta_reduce at this
    rw [this, hK]
    rfl
  have e : ∀ c o v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        ((∑ β, S v β * (G β β - m)) * (G v c * G o v * (X₁ * Gs c o))) =
      K * X₁ * (G o v * lwExpTerm2_dw bl c₀ a' v * (G v c * lwExpTerm2_dw bl c₀ ac c * (Gs c o * lwExpTerm2_dw bl c₀ ao o))) := by
    intro c o v
    calc _ = lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o *
          (lwExpTerm2_dw bl c₀ a' v * (∑ β, S v β * (G β β - m))) * (G v c * G o v * (X₁ * Gs c o)) := by ring
      _ = _ := by rw [hv v]; ring
  simp only [e]
  have hK' : (t * ∑ b, SB' a' b * lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ b)) = K := by
    rw [hK, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hK']
  conv_lhs => simp only [← Finset.mul_sum]; rw [lwExpTerm2_sum3_rot]
  rfl

/-- The term `Φ₅`: `(G_{vv} - m) Σ_β S_{vβ} G_{βc} G_{oβ} f`. -/
theorem lwExpTerm2_eval5 (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (a' ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        ((G v v - m) * ∑ β, S v β * G β c * G o β * (X₁ * Gs c o)) =
      lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ a') * (t * ∑ b, SB' a' b * X₁ *
        lwExpTerm2_L3 G G Gs (lwExpTerm2_dw bl c₀ b) (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao)) := by
  set H : ι → ι → ℂ := fun c o => ∑ b, (t * SB' a' b) *
    ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o β * (X₁ * Gs c o)) with hH
  have hv : ∀ c o v, lwExpTerm2_dw bl c₀ a' v * ∑ β, S v β * G β c * G o β * (X₁ * Gs c o) =
      lwExpTerm2_dw bl c₀ a' v * H c o := by
    intro c o v
    have h1 := lwExpTerm2_S_sum bl c₀ t SB' S hS v (fun β => G β c * G o β * (X₁ * Gs c o))
    have h2 := lwExpTerm2_dw_mul bl c₀ a' v (fun a => ∑ b, (t * SB' a b) *
      ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o β * (X₁ * Gs c o)))
    beta_reduce at h1 h2
    have h3 : ∑ β, S v β * G β c * G o β * (X₁ * Gs c o) = ∑ β, S v β * (G β c * G o β * (X₁ * Gs c o)) :=
      Finset.sum_congr rfl fun β _ => by ring
    rw [h3, h1, h2]
  have e : ∀ c o v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        ((G v v - m) * ∑ β, S v β * G β c * G o β * (X₁ * Gs c o)) =
      (lwExpTerm2_dw bl c₀ a' v * (G v v - m)) * (lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * H c o) := by
    intro c o v
    calc _ = lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * (G v v - m) *
          (lwExpTerm2_dw bl c₀ a' v * ∑ β, S v β * G β c * G o β * (X₁ * Gs c o)) := by ring
      _ = _ := by rw [hv c o v]; ring
  simp only [e]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  unfold lwExpTerm2_Xv
  congr 1
  have hH2 : ∑ c, ∑ o, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * H c o =
      ∑ b, t * (SB' a' b * X₁ * lwExpTerm2_L3 G G Gs (lwExpTerm2_dw bl c₀ b) (lwExpTerm2_dw bl c₀ ac)
        (lwExpTerm2_dw bl c₀ ao)) := by
    simp only [hH, Finset.mul_sum]
    rw [lwExpTerm2_sum3_rot']
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [lwExpTerm2_L3_cov]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun β _ => by ring
  rw [hH2, ← Finset.mul_sum]

/-- The term `Φ₇b` (the derivative of `g = Ĝ_{co}`): a product of two 2-loops. -/
theorem lwExpTerm2_eval7b (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (a' ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        (∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o))) =
      t * ∑ b, SB' a' b * X₁ *
        (lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ ao) (lwExpTerm2_dw bl c₀ a') *
          lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ b) (lwExpTerm2_dw bl c₀ ac)) := by
  set H : ι → ι → ι → ℂ := fun c o v => ∑ b, (t * SB' a' b) *
    ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o v * (X₁ * (Gs c β * Gs v o))) with hH
  have hv : ∀ c o v, lwExpTerm2_dw bl c₀ a' v * (∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o))) =
      lwExpTerm2_dw bl c₀ a' v * H c o v := by
    intro c o v
    have h1 := lwExpTerm2_S_sum bl c₀ t SB' S hS v (fun β => G β c * G o v * (X₁ * (Gs c β * Gs v o)))
    have h2 := lwExpTerm2_dw_mul bl c₀ a' v (fun a => ∑ b, (t * SB' a b) *
      ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o v * (X₁ * (Gs c β * Gs v o))))
    beta_reduce at h1 h2
    have h3 : ∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o)) =
        ∑ β, S v β * (G β c * G o v * (X₁ * (Gs c β * Gs v o))) :=
      Finset.sum_congr rfl fun β _ => by ring
    rw [h3, h1, h2]
  have e : ∀ c o v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        (∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o))) =
      lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * (lwExpTerm2_dw bl c₀ a' v * H c o v) := by
    intro c o v
    rw [← hv c o v]; ring
  simp only [e, hH, Finset.mul_sum]
  rw [lwExpTerm2_sum4_rot' (fun c o v b => ∑ β, _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [lwExpTerm2_L2, Finset.sum_mul, Finset.mul_sum]
  refine (Finset.sum_congr rfl fun c _ => lwExpTerm2_sum3_rev _).trans ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun o _ => ?_
  ring

/-- The term `Φ₇a` (the derivative of `X₁ = tr(Ǧ D_{a₁})`, `∂_{βv} G_{γγ} = -(G_{γβ} G_{vγ})`): a 4-loop
with the middle matrix `M₁ = G D_{a₁} G`. -/
theorem lwExpTerm2_eval7a (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (M₁ : Matrix ι ι ℂ)
    (a' ac ao : B) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        (∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o)) =
      t * ∑ b, SB' a' b * lwExpTerm2_L4 G M₁ G Gs (lwExpTerm2_dw bl c₀ a') (lwExpTerm2_dw bl c₀ b)
        (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao) := by
  set H : ι → ι → ι → ℂ := fun c o v => ∑ b, (t * SB' a' b) *
    ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o v * (M₁ v β * Gs c o)) with hH
  have hv : ∀ c o v, lwExpTerm2_dw bl c₀ a' v * (∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o)) =
      lwExpTerm2_dw bl c₀ a' v * H c o v := by
    intro c o v
    have h1 := lwExpTerm2_S_sum bl c₀ t SB' S hS v (fun β => G β c * G o v * (M₁ v β * Gs c o))
    have h2 := lwExpTerm2_dw_mul bl c₀ a' v (fun a => ∑ b, (t * SB' a b) *
      ∑ β, lwExpTerm2_dw bl c₀ b β * (G β c * G o v * (M₁ v β * Gs c o)))
    beta_reduce at h1 h2
    have h3 : ∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o) =
        ∑ β, S v β * (G β c * G o v * (M₁ v β * Gs c o)) :=
      Finset.sum_congr rfl fun β _ => by ring
    rw [h3, h1, h2]
  have e : ∀ c o v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        (∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o)) =
      lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * (lwExpTerm2_dw bl c₀ a' v * H c o v) := by
    intro c o v
    rw [← hv c o v]; ring
  simp only [e, hH, Finset.mul_sum]
  rw [lwExpTerm2_sum4_rot' (fun c o v b => ∑ β, _)]
  refine Finset.sum_congr rfl fun b _ => ?_
  unfold lwExpTerm2_L4
  simp only [Finset.mul_sum]
  rw [lwExpTerm2_sum4_rot]
  refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun β _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **The one-vertex integrand `Φ_v`** of `(Oe2x)` summed over the kernel `m(1 - m² S)⁻¹`, for
`f = X₁ Ĝ_{co}` and `∂_{βv} f = -M₁_{vβ} Ĝ_{co} - X₁ Ĝ_{cβ} Ĝ_{vo}`. -/
def lwExpTerm2_Phi (G Gs S : Matrix ι ι ℂ) (m X₁ : ℂ) (M₁ : Matrix ι ι ℂ) (c o v : ι) : ℂ :=
  (if v = c then 1 else 0) * G o v * (X₁ * Gs c o) +
    (∑ β, S v β * (G β β - m)) * (G v c * G o v * (X₁ * Gs c o)) +
    (G v v - m) * (∑ β, S v β * G β c * G o β * (X₁ * Gs c o)) +
    ∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o) +
    ∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o))

/-- **The five block terms** of `Σ_{c,o,v} dw_{ac}(c) dw_{ao}(o) dw_{a'}(v) Φ_v`: `(Oe2x)` for `f = X₁ Ĝ_{co}` summed over the
block `a'` of the expansion vertex.  In the order of the terms `I₁`, `I₂`, `I₃`, `I₄₂`, `I₄₁` (and their `J`
companions): a 2-loop, two 3-loops with an extra `X`, a 4-loop with the middle matrix `M₁ = G D_{a₁} G` (the
5-loop), the product of two 2-loops. -/
def lwExpTerm2_five (bl : ι → B) (c₀ t : ℂ) (SB' : B → B → ℂ) (G Gs : Matrix ι ι ℂ) (m : ℂ) (M₁ : Matrix ι ι ℂ)
    (X₁ : ℂ) (a' ac ao : B) : ℂ :=
  (if a' = ac then c₀ else 0) * X₁ *
      lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ ao) (lwExpTerm2_dw bl c₀ ac) +
    (t * ∑ b, SB' a' b * lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ b)) * X₁ *
      lwExpTerm2_L3 G G Gs (lwExpTerm2_dw bl c₀ a') (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao) +
    lwExpTerm2_Xv G m (lwExpTerm2_dw bl c₀ a') * (t * ∑ b, SB' a' b * X₁ *
      lwExpTerm2_L3 G G Gs (lwExpTerm2_dw bl c₀ b) (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao)) +
    t * ∑ b, SB' a' b * lwExpTerm2_L4 G M₁ G Gs (lwExpTerm2_dw bl c₀ a') (lwExpTerm2_dw bl c₀ b)
      (lwExpTerm2_dw bl c₀ ac) (lwExpTerm2_dw bl c₀ ao) +
    t * ∑ b, SB' a' b * X₁ *
      (lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ ao) (lwExpTerm2_dw bl c₀ a') *
        lwExpTerm2_L2 Gs G (lwExpTerm2_dw bl c₀ b) (lwExpTerm2_dw bl c₀ ac))

/-- **The block form of `Σ_v dw_{a'}(v) Φ_v`**: the five terms. -/
theorem lwExpTerm2_evalJ (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (M₁ : Matrix ι ι ℂ)
    (a' ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
        lwExpTerm2_Phi G Gs S m X₁ M₁ c o v = lwExpTerm2_five bl c₀ t SB' G Gs m M₁ X₁ a' ac ao := by
  unfold lwExpTerm2_five
  rw [← lwExpTerm2_eval1 bl c₀ G Gs a' ac ao X₁, ← lwExpTerm2_eval3 bl c₀ t SB' G Gs m S hS a' ac ao X₁,
    ← lwExpTerm2_eval5 bl c₀ t SB' G Gs m S hS a' ac ao X₁, ← lwExpTerm2_eval7a bl c₀ t SB' G Gs S hS M₁ a' ac ao,
    ← lwExpTerm2_eval7b bl c₀ t SB' G Gs S hS a' ac ao X₁]
  simp only [lwExpTerm2_Phi, mul_add, Finset.sum_add_distrib]

/-- **Kernel summation**: `Σ_{c,o,α} dw_{a₂}(α) … (m Φ_α + m³ Σ_v S⁺_{αv} Φ_v) = Σ_{a'} Q_{a₂a'} J(a')`. -/
theorem lwExpTerm2_alg (hc : ∀ a, ((Finset.univ.filter fun x => bl x = a).card : ℂ) * c₀ = 1)
    (Sp : Matrix ι ι ℂ) (Kp : B → B → ℂ) (hSp : ∀ x y, Sp x y = c₀ * Kp (bl x) (bl y))
    (hS : ∀ x y, S x y = c₀ * (t * SB' (bl x) (bl y))) (M₁ : Matrix ι ι ℂ) (a₂ ac ao : B) (X₁ : ℂ) :
    ∑ c, ∑ o, ∑ α, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a₂ α *
        (m * lwExpTerm2_Phi G Gs S m X₁ M₁ c o α +
          m ^ 3 * ∑ v, Sp α v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v) =
      ∑ a', (m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
        lwExpTerm2_five bl c₀ t SB' G Gs m M₁ X₁ a' ac ao := by
  have step : ∀ c o, ∑ α, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a₂ α *
        (m * lwExpTerm2_Phi G Gs S m X₁ M₁ c o α +
          m ^ 3 * ∑ v, Sp α v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v) =
      lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o *
        ∑ a', (m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
          ∑ v, lwExpTerm2_dw bl c₀ a' v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v := by
    intro c o
    rw [← lwExpTerm2_keyQ bl c₀ hc Sp Kp hSp m a₂ (lwExpTerm2_Phi G Gs S m X₁ M₁ c o), Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o _ => step c o]
  have e1 : ∀ c o, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o *
      ∑ a', (m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
        ∑ v, lwExpTerm2_dw bl c₀ a' v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v =
      ∑ a', lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o *
        ((m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
          ∑ v, lwExpTerm2_dw bl c₀ a' v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v) := fun c o => by
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o _ => e1 c o]
  rw [lwExpTerm2_sum3_rot']
  refine Finset.sum_congr rfl fun a' _ => ?_
  have e2 : ∑ c, ∑ o, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o *
        ((m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
          ∑ v, lwExpTerm2_dw bl c₀ a' v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v) =
      (m * (if a₂ = a' then 1 else 0) + m ^ 3 * Kp a₂ a') *
        ∑ c, ∑ o, ∑ v, lwExpTerm2_dw bl c₀ ac c * lwExpTerm2_dw bl c₀ ao o * lwExpTerm2_dw bl c₀ a' v *
          lwExpTerm2_Phi G Gs S m X₁ M₁ c o v := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun v _ => by ring
  rw [e2, lwExpTerm2_evalJ bl c₀ t SB' G Gs m S hS M₁ a' ac ao X₁]

/-- **`(Oe2x)` is `m Φ_α + m³ Σ_v S⁺_{αv} Φ_v`**: the eight terms of `(Oe2x)` for `f = X₁ Ĝ_{co}` regrouped along
the kernel `m (1 - m² S)⁻¹` (pure algebra). -/
theorem lwExpTerm2_Q8 (Sp : Matrix ι ι ℂ) (M₁ : Matrix ι ι ℂ) (X₁ : ℂ) (c o α : ι) (f : ℂ)
    (hf : f = X₁ * Gs c o) (df : ι → ι → ℂ)
    (hdf : ∀ β v, df β v = -(M₁ v β * Gs c o) - X₁ * (Gs c β * Gs v o)) :
    (m * (if α = c then 1 else 0)) * G o α * f + m ^ 3 * Sp α c * G o c * f +
        (m * ∑ β, S α β * (G β β - m)) * (G α c * G o α * f) +
        m ^ 3 * ∑ α', ∑ β, Sp α α' * S α' β * (G β β - m) * G α' c * G o α' * f +
        m * (G α α - m) * ∑ α', S α α' * G α' c * G o α' * f +
        m ^ 3 * ∑ α', ∑ β, Sp α α' * S α' β * (G α' α' - m) * G β c * G o β * f -
        m * ∑ α', S α α' * G α' c * G o α * df α' α -
        m ^ 3 * ∑ α', ∑ β, Sp α α' * S α' β * G β c * G o α' * df β α' =
      m * lwExpTerm2_Phi G Gs S m X₁ M₁ c o α +
        m ^ 3 * ∑ v, Sp α v * lwExpTerm2_Phi G Gs S m X₁ M₁ c o v := by
  subst hf
  have h2 : ∑ v, Sp α v * ((if v = c then 1 else 0) * G o v * (X₁ * Gs c o)) = Sp α c * G o c * (X₁ * Gs c o) := by
    rw [Finset.sum_eq_single c (fun v _ hv => by simp [hv]) (fun h => absurd (Finset.mem_univ c) h)]
    simp only [ite_true]; ring
  have h4 : ∀ v, Sp α v * ((∑ β, S v β * (G β β - m)) * (G v c * G o v * (X₁ * Gs c o))) =
      ∑ β, Sp α v * S v β * (G β β - m) * G v c * G o v * (X₁ * Gs c o) := fun v => by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h6 : ∀ v, Sp α v * ((G v v - m) * (∑ β, S v β * G β c * G o β * (X₁ * Gs c o))) =
      ∑ β, Sp α v * S v β * (G v v - m) * G β c * G o β * (X₁ * Gs c o) := fun v => by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h7 : ∀ β v, df β v = -(M₁ v β * Gs c o) - X₁ * (Gs c β * Gs v o) := hdf
  have h8a : ∀ v, ∑ β, Sp α v * S v β * G β c * G o v * df β v =
      -(Sp α v * ∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o)) -
        Sp α v * ∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o)) := fun v => by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [h7]; ring
  have h7a : ∑ α', S α α' * G α' c * G o α * df α' α =
      -(∑ β, S α β * G β c * G o α * (M₁ α β * Gs c o)) -
        ∑ β, S α β * G β c * G o α * (X₁ * (Gs c β * Gs α o)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [h7]; ring
  unfold lwExpTerm2_Phi
  simp only [mul_add, Finset.sum_add_distrib, h2, h4, h6]
  rw [h7a]
  have h8 : ∑ α', ∑ β, Sp α α' * S α' β * G β c * G o α' * df β α' =
      ∑ v, (-(Sp α v * ∑ β, S v β * G β c * G o v * (M₁ v β * Gs c o)) -
        Sp α v * ∑ β, S v β * G β c * G o v * (X₁ * (Gs c β * Gs v o))) :=
    Finset.sum_congr rfl fun v _ => h8a v
  rw [h8]
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

end Eval

end Alg

/-! ## 3. Traces of products with diagonal weights -/

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem lwExpTerm2_trace_prod1 (P : Fin 1 → Matrix ι ι ℂ) :
    trace (List.ofFn P).prod = ∑ x, P 0 x x := by
  simp [List.ofFn_succ, Matrix.trace]

theorem lwExpTerm2_trace_prod2 (P : Fin 2 → Matrix ι ι ℂ) :
    trace (List.ofFn P).prod = ∑ x, ∑ y, P 0 x y * P 1 y x := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply]

theorem lwExpTerm2_trace_prod3 (P : Fin 3 → Matrix ι ι ℂ) :
    trace (List.ofFn P).prod = ∑ x, ∑ y, ∑ z, P 0 x y * (P 1 y z * P 2 z x) := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

theorem lwExpTerm2_trace_prod4 (P : Fin 4 → Matrix ι ι ℂ) :
    trace (List.ofFn P).prod = ∑ x₀, ∑ x₁, ∑ x₂, ∑ x₃, P 0 x₀ x₁ * (P 1 x₁ x₂ * (P 2 x₂ x₃ * P 3 x₃ x₀)) := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

theorem lwExpTerm2_trace_prod5 (P : Fin 5 → Matrix ι ι ℂ) :
    trace (List.ofFn P).prod = ∑ x₀, ∑ x₁, ∑ x₂, ∑ x₃, ∑ x₄, P 0 x₀ x₁ * (P 1 x₁ x₂ * (P 2 x₂ x₃ * (P 3 x₃ x₄ * P 4 x₄ x₀))) := by
  simp [List.ofFn_succ, Matrix.trace, Matrix.mul_apply, Finset.mul_sum]

end Trace

/-! ## 4. The bridge `Lloop` ↔ fine-lattice traces -/

/-- fine block label -/
def lwExpTerm2_bl (d L W : ℕ) [NeZero L] [NeZero W] (x : Idx d L W) : Zd d L := (split d L W x).1

section Bridge

variable {d L W : ℕ} [NeZero L] [NeZero W]


theorem lwExpTerm2_gres_blockMat (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) (σ : Bool) :
    Gres (blockMat d L W H) z σ = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) (Gres H z σ) := by
  unfold Gres blockMat
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix
        (splitEquiv d L W).symm (splitEquiv d L W).symm := by
    ext i j
    cases σ <;> simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  simp

theorem lwExpTerm2_Eblk_reindex (a : Zd d L) :
    Eblk d L W a = Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)
      (Matrix.diagonal (lwExpTerm2_dw (lwExpTerm2_bl d L W) (((W : ℂ) ^ d)⁻¹) a)) := by
  ext p q
  have h : split d L W ((splitEquiv d L W).symm p) = p := (splitEquiv d L W).apply_symm_apply p
  simp [Eblk, lwExpTerm2_dw, lwExpTerm2_bl, Matrix.diagonal_apply, h]

theorem lwExpTerm2_trace_reindex (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    Matrix.trace (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W) M) = Matrix.trace M := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp (splitEquiv d L W).symm (fun i => M i i) |>.symm ▸ rfl

/-- **`𝓛^{(k)}` as a trace on the fine lattice**: the block-product bridge `blockMat` and `E_a`. -/
theorem lwExpTerm2_loop_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) :
    loopFine d L W H z σ a = Matrix.trace (List.ofFn fun i =>
      Gres H z (σ i) * Matrix.diagonal (lwExpTerm2_dw (lwExpTerm2_bl d L W) (((W : ℂ) ^ d)⁻¹) (a i))).prod := by
  unfold loopFine loopM
  simp only [lwExpTerm2_gres_blockMat, lwExpTerm2_Eblk_reindex, ← map_mul]
  have h : (List.ofFn fun i => Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)
      (Gres H z (σ i) * Matrix.diagonal (lwExpTerm2_dw (lwExpTerm2_bl d L W) (((W : ℂ) ^ d)⁻¹) (a i)))) =
      (List.ofFn fun i => Gres H z (σ i) * Matrix.diagonal (lwExpTerm2_dw (lwExpTerm2_bl d L W) (((W : ℂ) ^ d)⁻¹) (a i))).map
        (Matrix.reindexAlgEquiv ℂ ℂ (splitEquiv d L W)) := List.map_ofFn.symm
  rw [h, ← map_list_prod, lwExpTerm2_trace_reindex]

end Bridge

/-! ## 5. `Lloop` at the size-`n` model as the nested sums of §2/§3 -/

section SzLoops

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The fine block weight `(E_a)_{xx} = W^{-d} 1[x ∈ [a]]` of the size-`n` model. -/
abbrev lwExpTerm2_w (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) : ℂ :=
  lwExpTerm2_dw (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) a x

theorem lwExpTerm2_Lloop1 (E t : ℝ) (s : Bool) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![s] ![a] ω =
      ∑ x, Gt sz n E t s ω x x * lwExpTerm2_w sz n a x := by
  unfold Lloop
  rw [lwExpTerm2_loop_eq, lwExpTerm2_trace_prod1]
  simp [Matrix.mul_diagonal, Gt, lwExpTerm2_w]

theorem lwExpTerm2_Lloop2 (E t : ℝ) (s₁ s₂ : Bool) (a b : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![s₁, s₂] ![a, b] ω =
      lwExpTerm2_L2 (Gt sz n E t s₁ ω) (Gt sz n E t s₂ ω) (lwExpTerm2_w sz n a) (lwExpTerm2_w sz n b) := by
  unfold Lloop
  rw [lwExpTerm2_loop_eq, lwExpTerm2_trace_prod2]
  simp [Matrix.mul_diagonal, Gt, lwExpTerm2_w, lwExpTerm2_L2]

theorem lwExpTerm2_Lloop3 (E t : ℝ) (s₁ s₂ s₃ : Bool) (a b c : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![s₁, s₂, s₃] ![a, b, c] ω =
      lwExpTerm2_L3 (Gt sz n E t s₁ ω) (Gt sz n E t s₂ ω) (Gt sz n E t s₃ ω)
        (lwExpTerm2_w sz n a) (lwExpTerm2_w sz n b) (lwExpTerm2_w sz n c) := by
  unfold Lloop
  rw [lwExpTerm2_loop_eq, lwExpTerm2_trace_prod3]
  simp [Matrix.mul_diagonal, Gt, lwExpTerm2_w, lwExpTerm2_L3]

theorem lwExpTerm2_Lloop5 (E t : ℝ) (s₁ s₂ s₃ s₄ s₅ : Bool) (a₁ a₂ a₃ a₄ a₅ : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Lloop sz n E t ![s₁, s₂, s₃, s₄, s₅] ![a₁, a₂, a₃, a₄, a₅] ω =
      lwExpTerm2_L4 (Gt sz n E t s₁ ω)
        (Gt sz n E t s₂ ω * Matrix.diagonal (lwExpTerm2_w sz n a₂) * Gt sz n E t s₃ ω)
        (Gt sz n E t s₄ ω) (Gt sz n E t s₅ ω)
        (lwExpTerm2_w sz n a₁) (lwExpTerm2_w sz n a₃) (lwExpTerm2_w sz n a₄) (lwExpTerm2_w sz n a₅) := by
  unfold Lloop
  rw [lwExpTerm2_loop_eq]
  have h5 : ∀ A₁ A₂ A₃ A₄ A₅ D₁ D₂ D₃ D₄ D₅ : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ,
      Matrix.trace (List.ofFn fun i : Fin 5 => ![A₁, A₂, A₃, A₄, A₅] i * ![D₁, D₂, D₃, D₄, D₅] i).prod =
        Matrix.trace (List.ofFn ![A₁ * D₁, A₂ * D₂ * A₃ * D₃, A₄ * D₄, A₅ * D₅]).prod := by
    intro A₁ A₂ A₃ A₄ A₅ D₁ D₂ D₃ D₄ D₅
    simp [List.ofFn_succ, Matrix.mul_assoc]
  have h5' : (fun i : Fin 5 => Gres (sz.seqHflow n t ω) (zt E t) (![s₁, s₂, s₃, s₄, s₅] i) *
      Matrix.diagonal (lwExpTerm2_dw (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹)
        (![a₁, a₂, a₃, a₄, a₅] i))) = fun i : Fin 5 =>
      ![Gres (sz.seqHflow n t ω) (zt E t) s₁, Gres (sz.seqHflow n t ω) (zt E t) s₂,
        Gres (sz.seqHflow n t ω) (zt E t) s₃, Gres (sz.seqHflow n t ω) (zt E t) s₄,
        Gres (sz.seqHflow n t ω) (zt E t) s₅] i *
      ![Matrix.diagonal (lwExpTerm2_w sz n a₁), Matrix.diagonal (lwExpTerm2_w sz n a₂),
        Matrix.diagonal (lwExpTerm2_w sz n a₃), Matrix.diagonal (lwExpTerm2_w sz n a₄),
        Matrix.diagonal (lwExpTerm2_w sz n a₅)] i := by
    funext i
    fin_cases i <;> rfl
  rw [h5', h5, lwExpTerm2_trace_prod4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.mul_diagonal]
  rfl


/-! ## 6. The fine resolvent objects, `∂_{h_{βv}}` of `f = X Ĝ_{co}`, `(Oe2x)` at one triple -/

/-- The charge-`σ` resolvent entry `Ĝ_{ij}`: `G_{ij}` for `σ = +`, `conj G_{ji}` for `σ = -`. -/
def lwExpTerm2_Gsm (z : ℂ) (u : ℝ) (σ : Bool) (ω : sz.SeqΩ) : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Matrix.of fun i j => if σ then lwG sz n z u i j ω else star (lwG sz n z u j i ω)

/-- `M₁ = G D_{a₁} G`. -/
def lwExpTerm2_M1 (z : ℂ) (u : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  lwGm sz n z u ω * Matrix.diagonal (lwExpTerm2_w sz n a) * lwGm sz n z u ω

theorem lwExpTerm2_tame1_Xv {z : ℂ} (hz : 0 < z.im) (u : ℝ) (m : ℂ) (a : Zd d (sz.L n)) :
    Tame1 sz n (fun ω => lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a)) := by
  unfold lwExpTerm2_Xv
  refine Tame1.sum _ fun γ _ => (Tame1.const _).mul ((lwG_tame1 hz u γ γ).sub (Tame1.const _))

theorem lwExpTerm2_tame1_Gsm {z : ℂ} (hz : 0 < z.im) (u : ℝ) (σ : Bool) (c o : Idx d (sz.L n) (sz.W n)) :
    Tame1 sz n (fun ω => lwExpTerm2_Gsm sz n z u σ ω c o) := by
  cases σ
  · simpa [lwExpTerm2_Gsm] using (lwG_tame1 hz u o c).conj
  · simpa [lwExpTerm2_Gsm] using lwG_tame1 hz u c o

/-- **`∂_{h_{βv}}` of `f = X_{a₁} Ĝ_{co}`** (`(Oe2x)`, `B:50-56`): the sum of the derivative of `X_{a₁}`
(`∂_{βv} G_{γγ} = -G_{γβ}G_{vγ}`, the 5-loop term) and of `Ĝ_{co}` (`∂_{βv} Ĝ_{co} = -Ĝ_{cβ}Ĝ_{vo}`, the product
of two 2-loops), for both charges. -/
theorem lwExpTerm2_dh {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (m : ℂ) (a : Zd d (sz.L n)) (σ : Bool)
    (c o β v : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ) :
    dhSample sz n u β v (fun ω => lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) *
        lwExpTerm2_Gsm sz n z u σ ω c o) ω =
      -(lwExpTerm2_M1 sz n z u a ω v β * lwExpTerm2_Gsm sz n z u σ ω c o) -
        lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) *
          (lwExpTerm2_Gsm sz n z u σ ω c β * lwExpTerm2_Gsm sz n z u σ ω v o) := by
  have hX := lwExpTerm2_tame1_Xv sz n hz u m a
  have hG := lwExpTerm2_tame1_Gsm sz n hz u σ c o
  rw [lwStein_dh_mul hX hG]
  have h1 : dhSample sz n u β v (fun ω => lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a)) ω =
      -(lwExpTerm2_M1 sz n z u a ω v β) := by
    change dhSample sz n u β v (fun ω => ∑ γ, lwExpTerm2_w sz n a γ * (lwG sz n z u γ γ ω - m)) ω = _
    have hs : ∀ γ ∈ (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))),
        Tame1 sz n (fun ω => lwExpTerm2_w sz n a γ * (lwG sz n z u γ γ ω - m)) :=
      fun γ _ => (Tame1.const _).mul ((lwG_tame1 hz u γ γ).sub (Tame1.const _))
    rw [lwStein_dh_sum _ hs]
    have hγ : ∀ γ, dhSample sz n u β v (fun ω => lwExpTerm2_w sz n a γ * (lwG sz n z u γ γ ω - m)) ω =
        -(lwExpTerm2_w sz n a γ * (lwG sz n z u γ β ω * lwG sz n z u v γ ω)) := by
      intro γ
      rw [lwStein_dh_const_mul _ ((lwG_tame1 hz u γ γ).sub (Tame1.const _)),
        lwStein_dh_sub (lwG_tame1 hz u γ γ) (Tame1.const _), lwStein_dh_const, dhSample_lwG sz n hz hu]
      ring
    simp only [hγ]
    unfold lwExpTerm2_M1
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by simp only [lwG]; ring
  have h2 : dhSample sz n u β v (fun ω => lwExpTerm2_Gsm sz n z u σ ω c o) ω =
      -(lwExpTerm2_Gsm sz n z u σ ω c β * lwExpTerm2_Gsm sz n z u σ ω v o) := by
    cases σ
    · have := dhSample_lwG_star sz n hz hu β v o c ω
      simp only [lwExpTerm2_Gsm, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte]
      rw [this, star_mul']
      ring
    · have := dhSample_lwG sz n hz hu β v c o ω
      simp only [lwExpTerm2_Gsm, Matrix.of_apply, ↓reduceIte]
      exact this
  rw [h1, h2]
  ring

/-- The resolvent polynomial of `f = X_a Ĝ_{co}` (`lwPoly`). -/
def lwExpTerm2_P (m : ℂ) (a : Zd d (sz.L n)) (σ : Bool) (c o : Idx d (sz.L n) (sz.W n)) :
    MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ :=
  (∑ γ, MvPolynomial.C (lwExpTerm2_w sz n a γ) * (MvPolynomial.X (γ, γ, true) - MvPolynomial.C m)) *
    (if σ then MvPolynomial.X (c, o, true) else MvPolynomial.X (o, c, false))

theorem lwExpTerm2_lwPoly (z : ℂ) (u : ℝ) (m : ℂ) (a : Zd d (sz.L n)) (σ : Bool)
    (c o : Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ) :
    lwPoly sz n z u (lwExpTerm2_P sz n m a σ c o) ω =
      lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) * lwExpTerm2_Gsm sz n z u σ ω c o := by
  unfold lwPoly lwExpTerm2_P lwExpTerm2_Xv lwExpTerm2_Gsm
  cases σ <;> simp [lwVar, lwG, map_sum, map_mul]

/-- **`(Oe2x)` at one triple** `(α, c, o)`, `f = X_a Ĝ_{co}`: `E[G_{αc} G_{oα} f] = E[m Φ_α + m³ Σ_v S⁺_{αv} Φ_v]`
(`oe2x_integral` with `S⁺ = lwSplus`, the `∂` terms evaluated by `lwExpTerm2_dh`, regrouped by `lwExpTerm2_Q8`). -/
theorem lwExpTerm2_triple (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    (a : Zd d (sz.L n)) (σ : Bool) (α c o : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, lwG sz n (zt E t) t α c ω * lwG sz n (zt E t) t o α ω *
        (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a) *
          lwExpTerm2_Gsm sz n (zt E t) t σ ω c o) ∂(sz.seqP) =
      ∫ ω, (mE E * lwExpTerm2_Phi (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω)
            (lwS sz n t) (mE E) (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a))
            (lwExpTerm2_M1 sz n (zt E t) t a ω) c o α +
          mE E ^ 3 * ∑ v, lwSplus sz n t (mE E) α v *
            lwExpTerm2_Phi (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω)
              (lwS sz n t) (mE E) (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a))
              (lwExpTerm2_M1 sz n (zt E t) t a ω) c o v) ∂(sz.seqP) := by
  have hz : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
  have hm : ‖mE E‖ ^ 2 * t < 1 := by rw [norm_mE hE.le]; simpa using ht1
  have key := oe2x_integral (sz := sz) (n := n) hG hz ht0 (lwWx_mE_ne E hE) (lwWx_flow E t hE)
    (lwSplus sz n t (mE E)) (fun i j => lwSplus_spec (sz := sz) (n := n) ht0.le hm i j)
    (lwExpTerm2_P sz n (mE E) a σ c o) α c o
  have hPf : lwPoly sz n (zt E t) t (lwExpTerm2_P sz n (mE E) a σ c o) = fun ω =>
      lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a) *
        lwExpTerm2_Gsm sz n (zt E t) t σ ω c o :=
    funext fun ω => lwExpTerm2_lwPoly sz n _ _ _ _ _ _ _ ω
  rw [hPf] at key
  refine key.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_))
  have hdf := fun β v => lwExpTerm2_dh sz n hz ht0 (mE E) a σ c o β v ω
  exact lwExpTerm2_Q8 (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω) (mE E) (lwS sz n t)
    (lwSplus sz n t (mE E)) (lwExpTerm2_M1 sz n (zt E t) t a ω)
    (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a)) c o α _ rfl
    (fun β v => dhSample sz n t β v (fun ω => lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a) *
        lwExpTerm2_Gsm sz n (zt E t) t σ ω c o) ω) hdf

/-! ### The block structure of `S`, `S⁺` -/

theorem lwExpTerm2_hc (a : Zd d (sz.L n)) :
    ((Finset.univ.filter fun x : Idx d (sz.L n) (sz.W n) => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a).card : ℂ) *
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) = 1 := by
  have h := card_Iblk d (sz.L n) (sz.W n) a
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne')
  have h' : (Finset.univ.filter fun x : Idx d (sz.L n) (sz.W n) => lwExpTerm2_bl d (sz.L n) (sz.W n) x = a).card =
      (sz.W n) ^ d := h
  rw [h']
  push_cast
  exact mul_inv_cancel₀ hW

theorem lwExpTerm2_hS (t : ℝ) (x y : Idx d (sz.L n) (sz.W n)) :
    lwS sz n t x y = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) *
      ((t : ℂ) * SB d (sz.L n) (sz.lam n) (lwExpTerm2_bl d (sz.L n) (sz.W n) x)
        (lwExpTerm2_bl d (sz.L n) (sz.W n) y)) := by
  have h := congrFun (congrFun (lwSmat_eq d (sz.L n) (sz.W n) (sz.lam n) t) x) y
  have h2 : lwS sz n t x y = lwSmat d (sz.L n) (sz.W n) (sz.lam n) t x y := rfl
  rw [h2, h]
  simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, lwExpTerm2_bl]
  ring

theorem lwExpTerm2_hSp (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (x y : Idx d (sz.L n) (sz.W n)) :
    lwSplus sz n t (mE E) x y = ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) *
      LWExpKp sz n E t (lwExpTerm2_bl d (sz.L n) (sz.W n) x) (lwExpTerm2_bl d (sz.L n) (sz.W n) y) := by
  have h := congrFun (congrFun (lwSpOf_eq (d := d) (L := sz.L n) (W := sz.W n) (sz.three_le_L n)
    (g := sz.lam n) ht0 ht1 (m := mE E) (norm_mE hE.le)) x) y
  rw [lwSplus_eq, h]
  simp only [Matrix.smul_apply, lwLift, Matrix.of_apply, smul_eq_mul, LWExpKp, lwExpTerm2_bl]
  ring

/-- `G(-) = G(+)^*` for a Hermitian matrix (the flow matrix). -/
theorem lwExpTerm2_Gt_false (E t : ℝ) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) :
    Gt sz n E t false ω i j = star (Gt sz n E t true ω j i) := by
  have hH : (sz.seqHflow n t ω).IsHermitian := Sizes.seqHflow_isHermitian sz n t ω
  have hH' : (sz.seqHflow n t ω)ᴴ = sz.seqHflow n t ω := hH
  have : Gt sz n E t false ω = (Gt sz n E t true ω)ᴴ := by
    unfold Gt Gres
    simp only [Bool.false_eq_true, ↓reduceIte, ← Matrix.nonsing_inv_eq_ringInverse,
      Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hH', Complex.star_def]
  rw [this, Matrix.conjTranspose_apply]

theorem lwExpTerm2_Gt_eq_Gsm (E t : ℝ) (σ : Bool) (ω : sz.SeqΩ) :
    Gt sz n E t σ ω = lwExpTerm2_Gsm sz n (zt E t) t σ ω := by
  ext i j
  cases σ
  · simp only [lwExpTerm2_Gsm, Matrix.of_apply, Bool.false_eq_true, ↓reduceIte]
    exact lwExpTerm2_Gt_false sz n E t ω i j
  · rfl

/-! ### Tameness and integrability of the fine terms -/

theorem lwExpTerm2_tame_Gm {z : ℂ} (hz : 0 < z.im) (u : ℝ) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => lwGm sz n z u ω i j) := lwStein_tame_lwG sz n hz.ne' u i j

theorem lwExpTerm2_tame_M1 {z : ℂ} (hz : 0 < z.im) (u : ℝ) (a : Zd d (sz.L n)) (i j : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => lwExpTerm2_M1 sz n z u a ω i j) :=
  lwStein_tame_GDG sz n hz.ne' u (Matrix.diagonal (lwExpTerm2_w sz n a)) i j

/-- Tameness of the one-vertex integrand `Φ_v`. -/
theorem lwExpTerm2_tame_Phi {z : ℂ} (hz : 0 < z.im) (u : ℝ) (S : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (m : ℂ) (a : Zd d (sz.L n)) (σ : Bool) (c o v : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => lwExpTerm2_Phi (lwGm sz n z u ω) (lwExpTerm2_Gsm sz n z u σ ω) S m
      (lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a)) (lwExpTerm2_M1 sz n z u a ω) c o v) := by
  have hX : Tame sz (fun ω => lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a)) :=
    (lwExpTerm2_tame1_Xv sz n hz u m a).tame
  have hGs : ∀ i j, Tame sz (fun ω => lwExpTerm2_Gsm sz n z u σ ω i j) :=
    fun i j => (lwExpTerm2_tame1_Gsm sz n hz u σ i j).tame
  have hGm := lwExpTerm2_tame_Gm sz n hz u
  have hM1 := lwExpTerm2_tame_M1 sz n hz u a
  unfold lwExpTerm2_Phi
  have hXG : Tame sz (fun ω => lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) *
      lwExpTerm2_Gsm sz n z u σ ω c o) := hX.mul (hGs c o)
  have h1 := ((Tame.const (sz := sz) (if v = c then (1 : ℂ) else 0)).mul (hGm o v)).mul hXG
  have h2 := (Tame.sum (sz := sz) Finset.univ (F := fun β ω => S v β * (lwGm sz n z u ω β β - m))
    (fun β _ => (Tame.const _).mul ((hGm β β).sub (Tame.const _)))).mul (((hGm v c).mul (hGm o v)).mul hXG)
  have h3 := ((hGm v v).sub (Tame.const m)).mul (Tame.sum (sz := sz) Finset.univ
    (F := fun β ω => S v β * lwGm sz n z u ω β c * lwGm sz n z u ω o β * (lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) *
      lwExpTerm2_Gsm sz n z u σ ω c o))
    (fun β _ => (((Tame.const _).mul (hGm β c)).mul (hGm o β)).mul hXG))
  have h4 := Tame.sum (sz := sz) Finset.univ
    (F := fun β ω => S v β * lwGm sz n z u ω β c * lwGm sz n z u ω o v * (lwExpTerm2_M1 sz n z u a ω v β *
      lwExpTerm2_Gsm sz n z u σ ω c o))
    (fun β _ => (((Tame.const _).mul (hGm β c)).mul (hGm o v)).mul ((hM1 v β).mul (hGs c o)))
  have h5 := Tame.sum (sz := sz) Finset.univ
    (F := fun β ω => S v β * lwGm sz n z u ω β c * lwGm sz n z u ω o v * (lwExpTerm2_Xv (lwGm sz n z u ω) m (lwExpTerm2_w sz n a) *
      (lwExpTerm2_Gsm sz n z u σ ω c β * lwExpTerm2_Gsm sz n z u σ ω v o)))
    (fun β _ => (((Tame.const _).mul (hGm β c)).mul (hGm o v)).mul (hX.mul ((hGs c β).mul (hGs v o))))
  exact ((((h1.add h2).add h3).add h4).add h5)

end SzLoops

/-! ## 7. Integrals of the fine sums, the block form of one `(a₁, a₂)`-term -/

theorem lwExpTerm2_integral_sum3 {Ω κ₁ κ₂ κ₃ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] (F : κ₁ → κ₂ → κ₃ → Ω → ℂ)
    (h : ∀ i j k, Integrable (F i j k) μ) :
    ∫ ω, ∑ i, ∑ j, ∑ k, F i j k ω ∂μ = ∑ i, ∑ j, ∑ k, ∫ ω, F i j k ω ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => h i j k)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => h i j k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => h i j k)]

theorem lwExpTerm2_integral_weighted {Ω κ₁ κ₂ κ₃ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃] (w : κ₁ → κ₂ → κ₃ → ℂ) (F Ψ : κ₁ → κ₂ → κ₃ → Ω → ℂ)
    (hF : ∀ i j k, Integrable (F i j k) μ) (hΨ : ∀ i j k, Integrable (Ψ i j k) μ)
    (h : ∀ i j k, ∫ ω, F i j k ω ∂μ = ∫ ω, Ψ i j k ω ∂μ) :
    ∫ ω, ∑ i, ∑ j, ∑ k, w i j k * F i j k ω ∂μ = ∫ ω, ∑ i, ∑ j, ∑ k, w i j k * Ψ i j k ω ∂μ := by
  rw [lwExpTerm2_integral_sum3 (fun i j k ω => w i j k * F i j k ω) (fun i j k => (hF i j k).const_mul _),
    lwExpTerm2_integral_sum3 (fun i j k ω => w i j k * Ψ i j k ω) (fun i j k => (hΨ i j k).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul, h]

section Block

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- The block-level integrand of the expansion of one `(a₁, a₂)`-term of `LWcut(+, σ)`. -/
def lwExpTerm2_cutRHS (E t : ℝ) (a₁ a₂ ac ao : Zd d (sz.L n)) (σ : Bool) (ω : sz.SeqΩ) : ℂ :=
  ∑ a', (mE E * (if a₂ = a' then 1 else 0) + mE E ^ 3 * LWExpKp sz n E t a₂ a') *
    lwExpTerm2_five (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (t : ℂ)
      (fun a b => SB d (sz.L n) (sz.lam n) a b) (Gt sz n E t true ω) (Gt sz n E t σ ω) (mE E)
      (Gt sz n E t true ω * Matrix.diagonal (lwExpTerm2_w sz n a₁) * Gt sz n E t true ω)
      (lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁)) a' ac ao

/-- **The `(a₁, a₂)`-term of `𝔼 LWcut(+, σ)`, expanded** (`(Oe2x)` at the vertex `α ∈ [a₂]` of `G_{xα}G_{αy}`, summed over
`x ∈ [ac]`, `y ∈ [ao]`, `α ∈ [a₂]`). -/
theorem lwExpTerm2_block (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    (a₁ a₂ ac ao : Zd d (sz.L n)) (σ : Bool) :
    ∫ ω, lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁) *
        lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
          (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao) ∂(sz.seqP) =
      ∫ ω, lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω ∂(sz.seqP) := by
  have hz : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
  have hGt : ∀ ω, Gt sz n E t true ω = lwGm sz n (zt E t) t ω := fun ω => rfl
  have hGs : ∀ ω, Gt sz n E t σ ω = lwExpTerm2_Gsm sz n (zt E t) t σ ω := fun ω => lwExpTerm2_Gt_eq_Gsm sz n E t σ ω
  simp only [hGs, hGt, lwExpTerm2_cutRHS]
  have hX : Tame sz (fun ω => lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁)) :=
    (lwExpTerm2_tame1_Xv sz n hz t (mE E) a₁).tame
  have hGsT : ∀ i j, Tame sz (fun ω => lwExpTerm2_Gsm sz n (zt E t) t σ ω i j) :=
    fun i j => (lwExpTerm2_tame1_Gsm sz n hz t σ i j).tame
  have hL : ∀ ω : sz.SeqΩ, lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁) *
      lwExpTerm2_L3 (lwGm sz n (zt E t) t ω) (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω)
        (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao) =
      ∑ c, ∑ o, ∑ α, (lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * lwExpTerm2_w sz n a₂ α) *
        (lwG sz n (zt E t) t α c ω * lwG sz n (zt E t) t o α ω *
          (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁) *
            lwExpTerm2_Gsm sz n (zt E t) t σ ω c o)) := by
    intro ω
    rw [lwExpTerm2_L3_cov, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [lwG]
    ring
  simp only [hL]
  rw [lwExpTerm2_integral_weighted (μ := sz.seqP)
    (fun c o α => lwExpTerm2_w sz n ac c * lwExpTerm2_w sz n ao o * lwExpTerm2_w sz n a₂ α)
    (fun c o α ω => lwG sz n (zt E t) t α c ω * lwG sz n (zt E t) t o α ω *
      (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁) *
        lwExpTerm2_Gsm sz n (zt E t) t σ ω c o))
    (fun c o α ω => mE E * lwExpTerm2_Phi (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω)
            (lwS sz n t) (mE E) (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁))
            (lwExpTerm2_M1 sz n (zt E t) t a₁ ω) c o α +
          mE E ^ 3 * ∑ v, lwSplus sz n t (mE E) α v *
            lwExpTerm2_Phi (lwGm sz n (zt E t) t ω) (lwExpTerm2_Gsm sz n (zt E t) t σ ω)
              (lwS sz n t) (mE E) (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁))
              (lwExpTerm2_M1 sz n (zt E t) t a₁ ω) c o v)
    (fun c o α => Tame.integrable hG (((lwStein_tame_lwG sz n hz.ne' t α c).mul
      (lwStein_tame_lwG sz n hz.ne' t o α)).mul (hX.mul (hGsT c o))))
    (fun c o α => Tame.integrable hG (((Tame.const _).mul (lwExpTerm2_tame_Phi sz n hz t (lwS sz n t) (mE E) a₁ σ c o α)).add
      ((Tame.const _).mul (Tame.sum _ fun v _ => (Tame.const _).mul
        (lwExpTerm2_tame_Phi sz n hz t (lwS sz n t) (mE E) a₁ σ c o v)))))
    (fun c o α => lwExpTerm2_triple sz n hG hE ht0 ht1 a₁ σ α c o)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  exact lwExpTerm2_alg (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (t : ℂ)
    (fun a b => SB d (sz.L n) (sz.lam n) a b) (lwGm sz n (zt E t) t ω)
    (lwExpTerm2_Gsm sz n (zt E t) t σ ω) (mE E) (lwS sz n t) (lwExpTerm2_hc sz n)
    (lwSplus sz n t (mE E)) (LWExpKp sz n E t) (lwExpTerm2_hSp sz n E t hE ht0.le ht1)
    (lwExpTerm2_hS sz n t) (lwExpTerm2_M1 sz n (zt E t) t a₁ ω) a₂ ac ao
    (lwExpTerm2_Xv (lwGm sz n (zt E t) t ω) (mE E) (lwExpTerm2_w sz n a₁))

end Block


/-! ## 8. Finite-sum algebra of the assembly (no probability) -/

section Assemble

variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The five terms at the level of the loops: `(X : B → ℂ)` the centred traces, `A2` the 2-loops of charge `(σ, +)`,
`L3` the 3-loops `(+,+,σ)` with first label `a`, `L5` the 5-loops `(+,+,+,+,σ)` with labels `(a', a₁, b)`. -/
def lwExpTerm2_fiveA (t c₀ : ℂ) (SBm : B → B → ℂ) (X : B → ℂ) (A2 : B → B → ℂ) (L3 : B → ℂ)
    (L5 : B → B → B → ℂ) (ac ao a₁ a' : B) : ℂ :=
  (if a' = ac then c₀ else 0) * X a₁ * A2 ao ac +
    (t * ∑ b, SBm a' b * X b) * X a₁ * L3 a' +
    X a' * (t * ∑ b, SBm a' b * X a₁ * L3 b) +
    t * ∑ b, SBm a' b * L5 a' a₁ b +
    t * ∑ b, SBm a' b * X a₁ * (A2 ao a' * A2 b ac)

/-- The collapse of the kernel: `Σ_{a₂} SB_{a₁a₂} Σ_{a'} Q_{a₂a'} g(a₁,a') = Σ_{a'} KK_{a₁a'} g(a₁,a')`. -/
theorem lwExpTerm2_kk_collapse (SBm KK : B → B → ℂ) (Q : B → B → ℂ) (hKK : ∀ a₁ a', KK a₁ a' = ∑ a₂, SBm a₁ a₂ * Q a₂ a')
    (g : B → B → ℂ) (a₁ : B) :
    ∑ a₂, SBm a₁ a₂ * ∑ a', Q a₂ a' * g a₁ a' = ∑ a', KK a₁ a' * g a₁ a' := by
  simp only [hKK, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a₂ _ => by ring

/-- **The assembly** (pure finite-sum algebra): `Wd Σ_{a₁a₂} SB_{a₁a₂} Σ_{a'} Q_{a₂a'} five(a₁,a')` is the sum of the
five pin expressions. -/
theorem lwExpTerm2_assemble (m t c₀ Wd : ℂ) (hW : Wd * c₀ = 1) (SBm Kp KK Q : B → B → ℂ)
    (hKK : ∀ a₁ a', KK a₁ a' = ∑ a₂, SBm a₁ a₂ * Q a₂ a') (hq : ∀ a₁ a', t * KK a₁ a' = m * Kp a₁ a')
    (X : B → ℂ) (A2 : B → B → ℂ) (L3 : B → ℂ) (L5 : B → B → B → ℂ) (ac ao : B) :
    Wd * ∑ a₁, ∑ a₂, SBm a₁ a₂ * ∑ a', Q a₂ a' * lwExpTerm2_fiveA t c₀ SBm X A2 L3 L5 ac ao a₁ a' =
      ∑ a₁, KK a₁ ac * (X a₁ * A2 ao ac) +
        t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * X a₃ * L3 a₂)) +
        t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * X a₂ * L3 a₃)) +
        m * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, Kp a₁ a₂ * SBm a₂ a₃ * L5 a₂ a₁ a₃) +
        t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * A2 ao a₂ * A2 a₃ ac)) := by
  have h1 : ∀ a₁, ∑ a₂, SBm a₁ a₂ * ∑ a', Q a₂ a' * lwExpTerm2_fiveA t c₀ SBm X A2 L3 L5 ac ao a₁ a' =
      ∑ a', KK a₁ a' * lwExpTerm2_fiveA t c₀ SBm X A2 L3 L5 ac ao a₁ a' :=
    fun a₁ => lwExpTerm2_kk_collapse SBm KK Q hKK _ a₁
  simp only [h1]
  unfold lwExpTerm2_fiveA
  have e1 : Wd * ∑ a₁, ∑ a', KK a₁ a' * ((if a' = ac then c₀ else 0) * X a₁ * A2 ao ac) =
      ∑ a₁, KK a₁ ac * (X a₁ * A2 ao ac) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    linear_combination (KK a₁ ac * X a₁ * A2 ao ac) * hW
  have e2 : Wd * ∑ a₁, ∑ a', KK a₁ a' * ((t * ∑ b, SBm a' b * X b) * X a₁ * L3 a') =
      t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * X a₃ * L3 a₂)) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun a₃ _ => by ring
  have e3 : Wd * ∑ a₁, ∑ a', KK a₁ a' * (X a' * (t * ∑ b, SBm a' b * X a₁ * L3 b)) =
      t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * X a₂ * L3 a₃)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun a₃ _ => by ring
  have e4 : Wd * ∑ a₁, ∑ a', KK a₁ a' * (t * ∑ b, SBm a' b * L5 a' a₁ b) =
      m * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, Kp a₁ a₂ * SBm a₂ a₃ * L5 a₂ a₁ a₃) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun a₃ _ => ?_
    linear_combination (Wd * SBm a₂ a₃ * L5 a₂ a₁ a₃) * hq a₁ a₂
  have e5 : Wd * ∑ a₁, ∑ a', KK a₁ a' * (t * ∑ b, SBm a' b * X a₁ * (A2 ao a' * A2 b ac)) =
      t * (Wd * ∑ a₁, ∑ a₂, ∑ a₃, KK a₁ a₂ * SBm a₂ a₃ * (X a₁ * A2 ao a₂ * A2 a₃ ac)) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => Finset.sum_congr rfl fun a₃ _ => by ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [e1, e2, e3, e4, e5]

end Assemble

/-! ## 9. Bounded measurable random variables (integrability of every random term; copy of `LWExpTerm.lean` §3, which is private there) -/

/-- A bounded measurable `ℂ`-valued random variable. -/
def lwExpTerm2_BM {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℂ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C

section BM

variable {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → ℂ}

theorem lwExpTerm2_BM_const (c : ℂ) : lwExpTerm2_BM (fun _ : Ω => c) :=
  ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

theorem lwExpTerm2_BM_mul (hf : lwExpTerm2_BM f) (hg : lwExpTerm2_BM g) :
    lwExpTerm2_BM (fun ω => f ω * g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  refine ⟨hfm.mul hgm, Cf * Cg, fun ω => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hCf ω) (hCg ω) (norm_nonneg _) ((norm_nonneg _).trans (hCf ω))

theorem lwExpTerm2_BM_add (hf : lwExpTerm2_BM f) (hg : lwExpTerm2_BM g) :
    lwExpTerm2_BM (fun ω => f ω + g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.add hgm, Cf + Cg, fun ω => (norm_add_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

theorem lwExpTerm2_BM_sub (hf : lwExpTerm2_BM f) (hg : lwExpTerm2_BM g) :
    lwExpTerm2_BM (fun ω => f ω - g ω) := by
  obtain ⟨hfm, Cf, hCf⟩ := hf
  obtain ⟨hgm, Cg, hCg⟩ := hg
  exact ⟨hfm.sub hgm, Cf + Cg, fun ω => (norm_sub_le _ _).trans (add_le_add (hCf ω) (hCg ω))⟩

theorem lwExpTerm2_BM_sum {ι : Type*} (s : Finset ι) {F : ι → Ω → ℂ}
    (h : ∀ i ∈ s, lwExpTerm2_BM (F i)) : lwExpTerm2_BM (fun ω => ∑ i ∈ s, F i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lwExpTerm2_BM_const (0 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact lwExpTerm2_BM_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lwExpTerm2_BM_integrable {P : Measure Ω} [IsFiniteMeasure P] (hf : lwExpTerm2_BM f) :
    Integrable f P := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact Integrable.of_bound hfm.aestronglyMeasurable C (Eventually.of_forall hC)

end BM

section LoopBM

variable {d : ℕ} (sz : Sizes d)

/-- The loops of the flow are bounded measurable (`walk_measurable_Lloop`, `norm_Lloop_le`). -/
theorem lwExpTerm2_BM_Lloop (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) :=
  ⟨walk_measurable_Lloop sz n E t σ a, (etaT E t)⁻¹ ^ (k + 1), fun ω => norm_Lloop_le sz n hE ht σ a ω⟩

theorem lwExpTerm2_BM_X (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool)
    (a : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t ![σ] ![a] ω - mSigma E σ) :=
  lwExpTerm2_BM_sub (lwExpTerm2_BM_Lloop sz n hE ht _ _) (lwExpTerm2_BM_const _)

/-- `LWcut` is bounded measurable. -/
theorem lwExpTerm2_BM_LWcut (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σc σo : Bool)
    (ac ao : Zd d (sz.L n)) : lwExpTerm2_BM (fun ω : sz.SeqΩ => LWcut sz n E t σc σo ac ao ω) := by
  unfold LWcut
  refine lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (lwExpTerm2_BM_sum _ fun a₁ _ =>
    lwExpTerm2_BM_sum _ fun a₂ _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (lwExpTerm2_BM_const _)
      (lwExpTerm2_BM_X sz n hE ht σc a₁)) ?_)
  exact lwExpTerm2_BM_Lloop sz n hE ht (k := 2) _ _

end LoopBM


/-! ## 10. The kernel `K⁺`: the split identity -/

section Kernel

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- **`t · (S^{(B)} K⁺) = m⁻² (K⁺ − t S^{(B)})`** (`(1 − ξ S^{(B)}) Θ_ξ = 1` at `ξ = t m²`,
`K⁺ = t S^{(B)} Θ_ξ`): the identity which writes every `J`-term through `K⁺` and `S^{(B)}`. -/
theorem lwExpTerm2_Kp_split (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) • (SB d (sz.L n) (sz.lam n) * LWExpKp sz n E t) =
      ((mE E) ^ 2)⁻¹ • (LWExpKp sz n E t - (t : ℂ) • SB d (sz.L n) (sz.lam n)) := by
  have hn : ‖mE E‖ = 1 := norm_mE hE.le
  set m := mE E with hm
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  set SB' := SB d (sz.L n) (sz.lam n) with hSB
  set Θ := RBM.Theta d (sz.L n) (sz.lam n) ((t : ℂ) * m ^ 2) with hΘ
  have hξ : ‖(t : ℂ) * m ^ 2‖ < 1 := by
    simp [norm_pow, hn, abs_of_nonneg ht0, ht1]
  have h1 : (1 - ((t : ℂ) * m ^ 2) • SB') * Θ = 1 := mul_Theta_of_three_le (sz.three_le_L n) hξ
  have h2 : Θ - 1 = ((t : ℂ) * m ^ 2) • (SB' * Θ) := by
    calc Θ - 1 = Θ - ((1 - ((t : ℂ) * m ^ 2) • SB') * Θ) := by rw [h1]
      _ = _ := by rw [sub_mul, one_mul, smul_mul_assoc]; abel
  have hKp : LWExpKp sz n E t = (t : ℂ) • (SB' * Θ) := rfl
  rw [hKp]
  have h3 : SB' * ((t : ℂ) • (SB' * Θ)) = (t : ℂ) • (SB' * (SB' * Θ)) := by rw [Matrix.mul_smul]
  have h4 : ((t : ℂ) • (SB' * Θ) - (t : ℂ) • SB') = (t : ℂ) • (SB' * (Θ - 1)) := by
    rw [Matrix.mul_sub, mul_one, smul_sub]
  rw [h3, h4, h2, Matrix.mul_smul]
  simp only [smul_smul]
  have hc : (t : ℂ) * (t : ℂ) = ((m ^ 2)⁻¹ * ((t : ℂ) * ((t : ℂ) * m ^ 2))) := by field_simp
  rw [hc]

/-- `t · S^{(B)} (m + m³ K⁺) = m K⁺`: the kernel of `I₄₂ + J₄₂` is `m K⁺` (`m + m³ K⁺ = m Θ_{t m²}`). -/
theorem lwExpTerm2_tKK (E t : ℝ) (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (t : ℂ) • (SB d (sz.L n) (sz.lam n) * ((mE E) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
      (mE E) ^ 3 • LWExpKp sz n E t)) = (mE E) • LWExpKp sz n E t := by
  have hs := lwExpTerm2_Kp_split sz n E t hE ht0 ht1
  have hn : ‖mE E‖ = 1 := norm_mE hE.le
  have hm0 : mE E ≠ 0 := by
    intro h; rw [h] at hn; simp at hn
  set m := mE E with hm
  set SB' := SB d (sz.L n) (sz.lam n) with hSB
  set Kp := LWExpKp sz n E t with hKp
  have e1 : SB' * (m • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) + m ^ 3 • Kp) = m • SB' + m ^ 3 • (SB' * Kp) := by
    rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
  have hs' : m ^ 3 • ((t : ℂ) • (SB' * Kp)) = m • (Kp - (t : ℂ) • SB') := by
    rw [hs, smul_smul]
    have : m ^ 3 * (m ^ 2)⁻¹ = m := by field_simp
    rw [this]
  rw [e1, smul_add, smul_comm (t : ℂ) (m ^ 3), hs', smul_sub, smul_smul, smul_smul, mul_comm (t : ℂ) m]
  abel

end Kernel

/-! ## 11. The expansion of `𝔼 LWcut(+, σ)` at one size: five loop-level terms -/

theorem lwExpTerm2_integral_add5 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (f₁ f₂ f₃ f₄ f₅ : Ω → ℂ)
    (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ) (h₄ : Integrable f₄ μ)
    (h₅ : Integrable f₅ μ) :
    ∫ ω, (f₁ ω + f₂ ω + f₃ ω + f₄ ω + f₅ ω) ∂μ =
      ∫ ω, f₁ ω ∂μ + ∫ ω, f₂ ω ∂μ + ∫ ω, f₃ ω ∂μ + ∫ ω, f₄ ω ∂μ + ∫ ω, f₅ ω ∂μ := by
  have h12 : Integrable (fun ω => f₁ ω + f₂ ω) μ := h₁.add h₂
  have h123 : Integrable (fun ω => f₁ ω + f₂ ω + f₃ ω) μ := h12.add h₃
  have h1234 : Integrable (fun ω => f₁ ω + f₂ ω + f₃ ω + f₄ ω) μ := h123.add h₄
  rw [integral_add h1234 h₅, integral_add h123 h₄, integral_add h12 h₃, integral_add h₁ h₂]

theorem lwExpTerm2_integral_wsum1 {Ω κ₁ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype κ₁]
    (w : κ₁ → ℂ) (F : κ₁ → Ω → ℂ) (h : ∀ i, Integrable (F i) μ) :
    ∫ ω, ∑ i, w i * F i ω ∂μ = ∑ i, w i * ∫ ω, F i ω ∂μ := by
  rw [integral_finsetSum _ (fun i _ => (h i).const_mul _)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem lwExpTerm2_integral_wsum2 {Ω κ₁ κ₂ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [Fintype κ₁] [Fintype κ₂]
    (c : ℂ) (w : κ₁ → κ₂ → ℂ) (F : κ₁ → κ₂ → Ω → ℂ) (h : ∀ i j, Integrable (F i j) μ) :
    ∫ ω, c * ∑ i, ∑ j, w i j * F i j ω ∂μ = c * ∑ i, ∑ j, w i j * ∫ ω, F i j ω ∂μ := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (h i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (h i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

theorem lwExpTerm2_integral_wsum3 {Ω κ₁ κ₂ κ₃ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Fintype κ₁] [Fintype κ₂] [Fintype κ₃]
    (c : ℂ) (w : κ₁ → κ₂ → κ₃ → ℂ) (F : κ₁ → κ₂ → κ₃ → Ω → ℂ) (h : ∀ i j k, Integrable (F i j k) μ) :
    ∫ ω, c * ∑ i, ∑ j, ∑ k, w i j k * F i j k ω ∂μ = c * ∑ i, ∑ j, ∑ k, w i j k * ∫ ω, F i j k ω ∂μ := by
  rw [integral_const_mul]
  congr 1
  rw [lwExpTerm2_integral_sum3 (fun i j k ω => w i j k * F i j k ω) (fun i j k => (h i j k).const_mul _)]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    integral_const_mul _ _

section Expand

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

/-- `K = S^{(B)} (m + m³ K⁺)`: the kernel between the trace block `a₁` and the vertex block `a'` of `(Oe2x)`. -/
def lwExpTerm2_KK (E t : ℝ) : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ :=
  SB d (sz.L n) (sz.lam n) * ((mE E) • (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) +
    (mE E) ^ 3 • LWExpKp sz n E t)

theorem lwExpTerm2_KK_apply (E t : ℝ) (a b : Zd d (sz.L n)) :
    lwExpTerm2_KK sz n E t a b = ∑ c, (SB d (sz.L n) (sz.lam n) a c : ℂ) *
      (mE E * (if c = b then 1 else 0) + mE E ^ 3 * LWExpKp sz n E t c b) := by
  simp [lwExpTerm2_KK, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

theorem lwExpTerm2_Xv_eq (E t : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a) =
      Lloop sz n E t ![true] ![a] ω - mSigma E true := by
  have h1 : ∑ x, lwExpTerm2_w sz n a x = 1 :=
    lwExpTerm2_dw_sum (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (lwExpTerm2_hc sz n) a
  rw [lwExpTerm2_Lloop1]
  unfold lwExpTerm2_Xv
  have h2 : ∑ x, lwExpTerm2_w sz n a x * mE E = mE E := by rw [← Finset.sum_mul, h1, one_mul]
  simp only [mul_sub, Finset.sum_sub_distrib, h2, mSigma, ite_true]
  exact congrArg (· - mE E) (Finset.sum_congr rfl fun x _ => mul_comm _ _)

/-- The five terms through the loops `𝓛^{(k)}` of the model (`lwExpTerm2_fiveA` at the families of loops). -/
def lwExpTerm2_fiveL (E t : ℝ) (σ : Bool) (a₁ a' ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  lwExpTerm2_fiveA (t : ℂ) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (fun a b => (SB d (sz.L n) (sz.lam n) a b : ℂ))
    (fun b => Lloop sz n E t ![true] ![b] ω - mSigma E true)
    (fun x y => Lloop sz n E t ![σ, true] ![x, y] ω)
    (fun a => Lloop sz n E t ![true, true, σ] ![a, ac, ao] ω)
    (fun a b c => Lloop sz n E t ![true, true, true, true, σ] ![a, b, c, ac, ao] ω) ac ao a₁ a'

theorem lwExpTerm2_five_eq (E t : ℝ) (σ : Bool) (a₁ a' ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwExpTerm2_five (lwExpTerm2_bl d (sz.L n) (sz.W n)) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (t : ℂ)
      (fun a b => (SB d (sz.L n) (sz.lam n) a b : ℂ)) (Gt sz n E t true ω) (Gt sz n E t σ ω) (mE E)
      (Gt sz n E t true ω * Matrix.diagonal (lwExpTerm2_w sz n a₁) * Gt sz n E t true ω)
      (lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁)) a' ac ao =
      lwExpTerm2_fiveL sz n E t σ a₁ a' ac ao ω := by
  unfold lwExpTerm2_five lwExpTerm2_fiveL lwExpTerm2_fiveA
  simp only [lwExpTerm2_Lloop2, lwExpTerm2_Lloop3, lwExpTerm2_Lloop5, lwExpTerm2_Xv_eq]

theorem lwExpTerm2_cutRHS_eq (E t : ℝ) (a₁ a₂ ac ao : Zd d (sz.L n)) (σ : Bool) (ω : sz.SeqΩ) :
    lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω =
      ∑ a', (mE E * (if a₂ = a' then 1 else 0) + mE E ^ 3 * LWExpKp sz n E t a₂ a') *
        lwExpTerm2_fiveL sz n E t σ a₁ a' ac ao ω := by
  unfold lwExpTerm2_cutRHS
  exact Finset.sum_congr rfl fun a' _ => by rw [lwExpTerm2_five_eq]

/-- `LWcut(+, σ)` through the fine nested sums. -/
theorem lwExpTerm2_LWcut_true (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    LWcut sz n E t true σ ac ao ω = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂,
      (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) * (lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁) *
        lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
          (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) := by
  unfold LWcut
  congr 1
  refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
  rw [lwExpTerm2_Xv_eq, ← lwExpTerm2_Lloop3 sz n E t true true σ a₂ ac ao ω]
  ring

/-- The five terms through the loops are bounded measurable (`‖G_t‖ ≤ η_t⁻¹`, `t < 1`). -/
theorem lwExpTerm2_BM_fiveL {E t : ℝ} (hE : |E| < 2) (ht : t < 1) (σ : Bool) (a₁ a' ac ao : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => lwExpTerm2_fiveL sz n E t σ a₁ a' ac ao ω) := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht σ a
  unfold lwExpTerm2_fiveL lwExpTerm2_fiveA
  repeat' first
    | exact lwExpTerm2_BM_const _
    | exact hLl _ _
    | apply lwExpTerm2_BM_mul
    | apply lwExpTerm2_BM_add
    | apply lwExpTerm2_BM_sub
    | (apply lwExpTerm2_BM_sum; intros)

/-- The pathwise value of the left side of the block theorem as a product of two loops. -/
theorem lwExpTerm2_XL3_eq (E t : ℝ) (σ : Bool) (a₁ a₂ ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁) *
        lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
          (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao) =
      (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) * Lloop sz n E t ![true, true, σ] ![a₂, ac, ao] ω := by
  rw [lwExpTerm2_Xv_eq, lwExpTerm2_Lloop3]

/-- The block-level integrand `Rtot = W^d Σ_{a₁a₂} S^{(B)}_{a₁a₂} cutRHS(a₁, a₂)`. -/
def lwExpTerm2_Rtot (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
    lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω

/-- **`𝔼 LWcut(+, σ) = 𝔼 Rtot`**: the expansion `(Oe2x)` at the vertex `α ∈ [a₂]`, summed with the weights of `LWcut`. -/
theorem lwExpTerm2_cut_eq_Rtot (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    ∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP) = ∫ ω, lwExpTerm2_Rtot sz n E t σ ac ao ω ∂(sz.seqP) := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht1 σ a
  have hI1 : ∀ a₁ a₂ : Zd d (sz.L n), Integrable (fun ω : sz.SeqΩ => lwExpTerm2_Xv (Gt sz n E t true ω) (mE E)
      (lwExpTerm2_w sz n a₁) * lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
        (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) (sz.seqP) := by
    intro a₁ a₂
    simp only [lwExpTerm2_XL3_eq]
    exact lwExpTerm2_BM_integrable (lwExpTerm2_BM_mul (lwExpTerm2_BM_X sz n hE ht1 true a₁) (hLl _ _))
  have hI2 : ∀ a₁ a₂ : Zd d (sz.L n), Integrable (fun ω : sz.SeqΩ => lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω)
      (sz.seqP) := by
    intro a₁ a₂
    simp only [lwExpTerm2_cutRHS_eq]
    refine lwExpTerm2_BM_integrable (lwExpTerm2_BM_sum _ fun a' _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) ?_)
    exact lwExpTerm2_BM_fiveL sz n hE ht1 σ a₁ a' ac ao
  calc ∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP)
      = ∫ ω, (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        (lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁) *
          lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
            (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) ∂(sz.seqP) := by
        simp only [lwExpTerm2_LWcut_true]
    _ = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        ∫ ω, (lwExpTerm2_Xv (Gt sz n E t true ω) (mE E) (lwExpTerm2_w sz n a₁) *
          lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
            (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) ∂(sz.seqP) :=
        lwExpTerm2_integral_wsum2 _ _ (fun a₁ a₂ ω => lwExpTerm2_Xv (Gt sz n E t true ω) (mE E)
          (lwExpTerm2_w sz n a₁) * lwExpTerm2_L3 (Gt sz n E t true ω) (Gt sz n E t true ω) (Gt sz n E t σ ω)
            (lwExpTerm2_w sz n a₂) (lwExpTerm2_w sz n ac) (lwExpTerm2_w sz n ao)) hI1
    _ = (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, (SB d (sz.L n) (sz.lam n) a₁ a₂ : ℂ) *
        ∫ ω, lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω ∂(sz.seqP) := by
        simp only [lwExpTerm2_block sz n hG hE ht0 ht1 _ _ ac ao σ]
    _ = ∫ ω, lwExpTerm2_Rtot sz n E t σ ac ao ω ∂(sz.seqP) :=
        (lwExpTerm2_integral_wsum2 _ _ (fun a₁ a₂ ω => lwExpTerm2_cutRHS sz n E t a₁ a₂ ac ao σ ω) hI2).symm

/-- The pathwise integrands of the five terms, with the kernel `K` (`(t, m)`-factors are carried outside). -/
def lwExpTerm2_e1 (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  ∑ a₁, K a₁ ac * ((Lloop sz n E t ![true] ![a₁] ω - mSigma E true) * Lloop sz n E t ![σ, true] ![ao, ac] ω)

def lwExpTerm2_e3 (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (sel σ : Bool) (ac ao : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ((Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
      Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω)

def lwExpTerm2_e4 (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ((Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      Lloop sz n E t ![σ, true] ![ao, a₂] ω * Lloop sz n E t ![σ, true] ![a₃, ac] ω)

def lwExpTerm2_e5 (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    Lloop sz n E t ![true, true, true, true, σ] ![a₂, a₁, a₃, ac, ao] ω

theorem lwExpTerm2_Rtot_eq {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool)
    (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    lwExpTerm2_Rtot sz n E t σ ac ao ω =
      lwExpTerm2_e1 sz n (lwExpTerm2_KK sz n E t) E t σ ac ao ω +
        (t : ℂ) * lwExpTerm2_e3 sz n (lwExpTerm2_KK sz n E t) E t true σ ac ao ω +
        (t : ℂ) * lwExpTerm2_e3 sz n (lwExpTerm2_KK sz n E t) E t false σ ac ao ω +
        mE E * lwExpTerm2_e5 sz n (LWExpKp sz n E t) E t σ ac ao ω +
        (t : ℂ) * lwExpTerm2_e4 sz n (lwExpTerm2_KK sz n E t) E t σ ac ao ω := by
  have hW : (((sz.W n : ℕ) : ℂ) ^ d) * ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) = 1 :=
    mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (sz.W_pos n).ne'))
  have hq : ∀ a₁ a' : Zd d (sz.L n), (t : ℂ) * lwExpTerm2_KK sz n E t a₁ a' = mE E * LWExpKp sz n E t a₁ a' := by
    intro a₁ a'
    have := congrFun (congrFun (lwExpTerm2_tKK sz n E t hE ht0 ht1) a₁) a'
    simpa only [Matrix.smul_apply, smul_eq_mul, lwExpTerm2_KK] using this
  unfold lwExpTerm2_Rtot
  simp only [lwExpTerm2_cutRHS_eq]
  unfold lwExpTerm2_fiveL
  exact lwExpTerm2_assemble (mE E) (t : ℂ) ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) (((sz.W n : ℕ) : ℂ) ^ d) hW
    (fun a b => (SB d (sz.L n) (sz.lam n) a b : ℂ)) (fun a b => LWExpKp sz n E t a b)
    (fun a b => lwExpTerm2_KK sz n E t a b)
    (fun a b => mE E * (if a = b then 1 else 0) + mE E ^ 3 * LWExpKp sz n E t a b)
    (fun a₁ a' => lwExpTerm2_KK_apply sz n E t a₁ a') hq
    (fun b => Lloop sz n E t ![true] ![b] ω - mSigma E true)
    (fun x y => Lloop sz n E t ![σ, true] ![x, y] ω)
    (fun a => Lloop sz n E t ![true, true, σ] ![a, ac, ao] ω)
    (fun a b c => Lloop sz n E t ![true, true, true, true, σ] ![a, b, c, ac, ao] ω) ac ao

/-- The expression of `LWExpI1K` at `p = ((true, (σ, +)), (ao, ac))`. -/
def lwExpTerm2_Pa (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  ∑ a₁, K a₁ ac * ∫ ω, (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
    Lloop sz n E t ![σ, true] ![ao, ac] ω ∂(sz.seqP)

/-- The expression of `LWExpI23K` at `p = ((sel, σ), (ac, ao))`. -/
def lwExpTerm2_Pb (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (sel σ : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ∫ ω, (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
      Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω ∂(sz.seqP)

/-- The expression of `LWExpI41K` at `p = ((true, σ), (ao, ac))`. -/
def lwExpTerm2_Pc (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ∫ ω, (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      Lloop sz n E t ![σ, true] ![ao, a₂] ω * Lloop sz n E t ![σ, true] ![a₃, ac] ω ∂(sz.seqP)

/-- The expression of `LWExpG5'` (first kernel `K`) at the label pair `(ao, ac)` and last charge `σ`. -/
def lwExpTerm2_Pd (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ a₁, ∑ a₂, ∑ a₃, K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ) *
    ∫ ω, Lloop sz n E t ![true, true, true, true, σ] ![a₂, a₁, a₃, ac, ao] ω ∂(sz.seqP)

/-- Each pathwise integrand is bounded measurable, and its mean is the expression of the corresponding pin. -/
theorem lwExpTerm2_int_e1 {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => lwExpTerm2_e1 sz n K E t σ ac ao ω) ∧
      ∫ ω, lwExpTerm2_e1 sz n K E t σ ac ao ω ∂(sz.seqP) = lwExpTerm2_Pa sz n K E t σ ac ao := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht1 σ a
  have hX := lwExpTerm2_BM_X sz n hE ht1 true
  have hb : ∀ a₁ : Zd d (sz.L n), lwExpTerm2_BM (fun ω : sz.SeqΩ => (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
      Lloop sz n E t ![σ, true] ![ao, ac] ω) := fun a₁ => lwExpTerm2_BM_mul (hX a₁) (hLl _ _)
  exact ⟨lwExpTerm2_BM_sum _ fun a₁ _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (hb a₁),
    lwExpTerm2_integral_wsum1 (fun a₁ => K a₁ ac) _ fun a₁ => lwExpTerm2_BM_integrable (hb a₁)⟩

theorem lwExpTerm2_int_e3 {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (sel σ : Bool) (ac ao : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => lwExpTerm2_e3 sz n K E t sel σ ac ao ω) ∧
      ∫ ω, lwExpTerm2_e3 sz n K E t sel σ ac ao ω ∂(sz.seqP) = lwExpTerm2_Pb sz n K E t sel σ ac ao := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht1 σ a
  have hX := lwExpTerm2_BM_X sz n hE ht1 true
  have hb : ∀ a₁ a₂ a₃ : Zd d (sz.L n), lwExpTerm2_BM (fun ω : sz.SeqΩ =>
      (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
        (Lloop sz n E t ![true] ![if sel then a₃ else a₂] ω - mSigma E true) *
        Lloop sz n E t ![true, true, σ] ![if sel then a₂ else a₃, ac, ao] ω) :=
    fun a₁ a₂ a₃ => lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (hX a₁) (hX _)) (hLl _ _)
  refine ⟨lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (lwExpTerm2_BM_sum _ fun a₁ _ => lwExpTerm2_BM_sum _ fun a₂ _ =>
    lwExpTerm2_BM_sum _ fun a₃ _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (hb a₁ a₂ a₃)), ?_⟩
  exact lwExpTerm2_integral_wsum3 _ (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ)) _
    fun a₁ a₂ a₃ => lwExpTerm2_BM_integrable (hb a₁ a₂ a₃)

theorem lwExpTerm2_int_e4 {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => lwExpTerm2_e4 sz n K E t σ ac ao ω) ∧
      ∫ ω, lwExpTerm2_e4 sz n K E t σ ac ao ω ∂(sz.seqP) = lwExpTerm2_Pc sz n K E t σ ac ao := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht1 σ a
  have hX := lwExpTerm2_BM_X sz n hE ht1 true
  have hb : ∀ a₁ a₂ a₃ : Zd d (sz.L n), lwExpTerm2_BM (fun ω : sz.SeqΩ =>
      (Lloop sz n E t ![true] ![a₁] ω - mSigma E true) *
        Lloop sz n E t ![σ, true] ![ao, a₂] ω * Lloop sz n E t ![σ, true] ![a₃, ac] ω) :=
    fun a₁ a₂ a₃ => lwExpTerm2_BM_mul (lwExpTerm2_BM_mul (hX a₁) (hLl _ _)) (hLl _ _)
  refine ⟨lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (lwExpTerm2_BM_sum _ fun a₁ _ => lwExpTerm2_BM_sum _ fun a₂ _ =>
    lwExpTerm2_BM_sum _ fun a₃ _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (hb a₁ a₂ a₃)), ?_⟩
  exact lwExpTerm2_integral_wsum3 _ (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ)) _
    fun a₁ a₂ a₃ => lwExpTerm2_BM_integrable (hb a₁ a₂ a₃)

theorem lwExpTerm2_int_e5 {E t : ℝ} (hE : |E| < 2) (ht1 : t < 1) (K : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    lwExpTerm2_BM (fun ω : sz.SeqΩ => lwExpTerm2_e5 sz n K E t σ ac ao ω) ∧
      ∫ ω, lwExpTerm2_e5 sz n K E t σ ac ao ω ∂(sz.seqP) = lwExpTerm2_Pd sz n K E t σ ac ao := by
  have hLl : ∀ {k : ℕ} (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)),
      lwExpTerm2_BM (fun ω : sz.SeqΩ => Lloop sz n E t σ a ω) := fun σ a => lwExpTerm2_BM_Lloop sz n hE ht1 σ a
  refine ⟨lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (lwExpTerm2_BM_sum _ fun a₁ _ => lwExpTerm2_BM_sum _ fun a₂ _ =>
    lwExpTerm2_BM_sum _ fun a₃ _ => lwExpTerm2_BM_mul (lwExpTerm2_BM_const _) (hLl _ _)), ?_⟩
  exact lwExpTerm2_integral_wsum3 _ (fun a₁ a₂ a₃ => K a₁ a₂ * (SB d (sz.L n) (sz.lam n) a₂ a₃ : ℂ)) _
    fun a₁ a₂ a₃ => lwExpTerm2_BM_integrable (hLl _ _)

/-- **`𝔼 LWcut(+, σ, ac, ao)` is the sum of five loop-level terms** (`(eq:ELW_term)` expanded by `(Oe2x)`, the
terms `I₁ + J₁`, `I₂ + J₂`, `I₃ + J₃`, `I₄₂ + J₄₂`, `I₄₁ + J₄₁`, `B:17-34`, with the kernel `K = S^{(B)}(m + m³K⁺)`;
`I₄₂ + J₄₂` is `m` times the 5-loop with the first kernel `K⁺`, `t K = m K⁺`). -/
theorem lwExpTerm2_cut_expand (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 < t) (ht1 : t < 1)
    (σ : Bool) (ac ao : Zd d (sz.L n)) :
    ∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP) =
      lwExpTerm2_Pa sz n (lwExpTerm2_KK sz n E t) E t σ ac ao +
        (t : ℂ) * lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t true σ ac ao +
        (t : ℂ) * lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t false σ ac ao +
        mE E * lwExpTerm2_Pd sz n (LWExpKp sz n E t) E t σ ac ao +
        (t : ℂ) * lwExpTerm2_Pc sz n (lwExpTerm2_KK sz n E t) E t σ ac ao := by
  obtain ⟨b1, i1⟩ := lwExpTerm2_int_e1 sz n hE ht1 (lwExpTerm2_KK sz n E t) σ ac ao
  obtain ⟨b3, i3⟩ := lwExpTerm2_int_e3 sz n hE ht1 (lwExpTerm2_KK sz n E t) true σ ac ao
  obtain ⟨b5, i5⟩ := lwExpTerm2_int_e3 sz n hE ht1 (lwExpTerm2_KK sz n E t) false σ ac ao
  obtain ⟨b7, i7⟩ := lwExpTerm2_int_e5 sz n hE ht1 (LWExpKp sz n E t) σ ac ao
  obtain ⟨b9, i9⟩ := lwExpTerm2_int_e4 sz n hE ht1 (lwExpTerm2_KK sz n E t) σ ac ao
  rw [lwExpTerm2_cut_eq_Rtot sz n hG hE ht0 ht1]
  simp only [lwExpTerm2_Rtot_eq sz n hE ht0.le ht1]
  have j1 := lwExpTerm2_BM_integrable (P := sz.seqP) b1
  have j3 := lwExpTerm2_BM_integrable (P := sz.seqP) (lwExpTerm2_BM_mul (lwExpTerm2_BM_const (t : ℂ)) b3)
  have j5 := lwExpTerm2_BM_integrable (P := sz.seqP) (lwExpTerm2_BM_mul (lwExpTerm2_BM_const (t : ℂ)) b5)
  have j7 := lwExpTerm2_BM_integrable (P := sz.seqP) (lwExpTerm2_BM_mul (lwExpTerm2_BM_const (mE E)) b7)
  have j9 := lwExpTerm2_BM_integrable (P := sz.seqP) (lwExpTerm2_BM_mul (lwExpTerm2_BM_const (t : ℂ)) b9)
  rw [lwExpTerm2_integral_add5 _ _ _ _ _ j1 j3 j5 j7 j9]
  simp only [integral_const_mul, i1, i3, i5, i7, i9]

end Expand

/-! ## 12. Conjugation `σ_c = - → +` -/

section Conj

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

theorem lwExpTerm2_conj_Gt (E t : ℝ) (s : Bool) (ω : sz.SeqΩ) (i j : Idx d (sz.L n) (sz.W n)) :
    (starRingEnd ℂ) (Gt sz n E t s ω i j) = Gt sz n E t (!s) ω j i := by
  cases s
  · have := lwExpTerm2_Gt_false sz n E t ω i j
    simp only [Bool.not_false]
    rw [this]; simp
  · have := lwExpTerm2_Gt_false sz n E t ω j i
    simp only [Bool.not_true]
    rw [this]; simp

theorem lwExpTerm2_conj_w (a : Zd d (sz.L n)) (x : Idx d (sz.L n) (sz.W n)) :
    (starRingEnd ℂ) (lwExpTerm2_w sz n a x) = lwExpTerm2_w sz n a x := by
  unfold lwExpTerm2_w lwExpTerm2_dw
  split_ifs <;> simp

theorem lwExpTerm2_conj_Lloop1 (E t : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (starRingEnd ℂ) (Lloop sz n E t ![false] ![a] ω) = Lloop sz n E t ![true] ![a] ω := by
  rw [lwExpTerm2_Lloop1, lwExpTerm2_Lloop1, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, lwExpTerm2_conj_Gt, lwExpTerm2_conj_w]
  simp

theorem lwExpTerm2_Gt_ct (E t : ℝ) (s : Bool) (ω : sz.SeqΩ) :
    (Gt sz n E t s ω)ᴴ = Gt sz n E t (!s) ω := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  have := lwExpTerm2_conj_Gt sz n E t s ω j i
  simpa [Complex.star_def] using this

theorem lwExpTerm2_L3_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (A₁ A₂ A₃ : Matrix ι ι ℂ) (u v w : ι → ℂ) :
    lwExpTerm2_L3 A₁ A₂ A₃ u v w = Matrix.trace ((A₁ * Matrix.diagonal u) * ((A₂ * Matrix.diagonal v) *
      (A₃ * Matrix.diagonal w))) := by
  have h := lwExpTerm2_trace_prod3 ![A₁ * Matrix.diagonal u, A₂ * Matrix.diagonal v, A₃ * Matrix.diagonal w]
  have h2 : (List.ofFn ![A₁ * Matrix.diagonal u, A₂ * Matrix.diagonal v, A₃ * Matrix.diagonal w]).prod =
      (A₁ * Matrix.diagonal u) * ((A₂ * Matrix.diagonal v) * (A₃ * Matrix.diagonal w)) := by
    simp [List.ofFn_succ]
  rw [h2] at h
  rw [h]
  simp [Matrix.mul_diagonal, lwExpTerm2_L3]

theorem lwExpTerm2_conj_Lloop3 (E t : ℝ) (σ : Bool) (a b c : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (starRingEnd ℂ) (Lloop sz n E t ![false, false, σ] ![a, b, c] ω) =
      Lloop sz n E t ![true, true, !σ] ![a, c, b] ω := by
  rw [lwExpTerm2_Lloop3, lwExpTerm2_Lloop3, lwExpTerm2_L3_trace, lwExpTerm2_L3_trace]
  have hw : ∀ x : Zd d (sz.L n), (Matrix.diagonal (lwExpTerm2_w sz n x))ᴴ = Matrix.diagonal (lwExpTerm2_w sz n x) := by
    intro x
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext y
    simpa using lwExpTerm2_conj_w sz n x y
  have h := Matrix.trace_conjTranspose ((Gt sz n E t false ω * Matrix.diagonal (lwExpTerm2_w sz n a)) *
    ((Gt sz n E t false ω * Matrix.diagonal (lwExpTerm2_w sz n b)) * (Gt sz n E t σ ω * Matrix.diagonal (lwExpTerm2_w sz n c))))
  simp only [Matrix.conjTranspose_mul, hw, lwExpTerm2_Gt_ct, Bool.not_false] at h
  have h3 : (starRingEnd ℂ) (Matrix.trace ((Gt sz n E t false ω * Matrix.diagonal (lwExpTerm2_w sz n a)) *
    ((Gt sz n E t false ω * Matrix.diagonal (lwExpTerm2_w sz n b)) * (Gt sz n E t σ ω * Matrix.diagonal (lwExpTerm2_w sz n c))))) =
      Matrix.trace (Matrix.diagonal (lwExpTerm2_w sz n c) * Gt sz n E t (!σ) ω *
        (Matrix.diagonal (lwExpTerm2_w sz n b) * Gt sz n E t true ω) *
        (Matrix.diagonal (lwExpTerm2_w sz n a) * Gt sz n E t true ω)) := h.symm
  rw [h3]
  calc _ = Matrix.trace (Matrix.diagonal (lwExpTerm2_w sz n c) * (Gt sz n E t (!σ) ω *
          (Matrix.diagonal (lwExpTerm2_w sz n b) * Gt sz n E t true ω) *
          (Matrix.diagonal (lwExpTerm2_w sz n a) * Gt sz n E t true ω))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Gt sz n E t (!σ) ω *
          (Matrix.diagonal (lwExpTerm2_w sz n b) * Gt sz n E t true ω) *
          (Matrix.diagonal (lwExpTerm2_w sz n a) * Gt sz n E t true ω)) * Matrix.diagonal (lwExpTerm2_w sz n c)) :=
        Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Gt sz n E t (!σ) ω * Matrix.diagonal (lwExpTerm2_w sz n b)) *
          (Gt sz n E t true ω * Matrix.diagonal (lwExpTerm2_w sz n a) * Gt sz n E t true ω *
            Matrix.diagonal (lwExpTerm2_w sz n c))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Gt sz n E t true ω * Matrix.diagonal (lwExpTerm2_w sz n a) * Gt sz n E t true ω *
            Matrix.diagonal (lwExpTerm2_w sz n c)) * (Gt sz n E t (!σ) ω * Matrix.diagonal (lwExpTerm2_w sz n b))) :=
        Matrix.trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]

theorem lwExpTerm2_conj_SB (a b : Zd d (sz.L n)) :
    (starRingEnd ℂ) (SB d (sz.L n) (sz.lam n) a b) = SB d (sz.L n) (sz.lam n) a b := by
  rw [SB_apply, sbKernel_eq_ofReal, Complex.conj_ofReal]

/-- **`conj LWcut(-, σ_o, a_c, a_o) = LWcut(+, -σ_o, a_o, a_c)`** (`G(-) = G(+)^*`, `E_a` and `S^{(B)}` real, the
cyclic rotation of the 3-loop). -/
theorem lwExpTerm2_cut_conj (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    (starRingEnd ℂ) (LWcut sz n E t false σ ac ao ω) = LWcut sz n E t true (!σ) ao ac ω := by
  unfold LWcut
  rw [map_mul, map_sum]
  refine congrArg₂ (· * ·) (by simp) (Finset.sum_congr rfl fun a₁ _ => ?_)
  rw [map_sum]
  refine Finset.sum_congr rfl fun a₂ _ => ?_
  rw [map_mul, map_mul, lwExpTerm2_conj_SB, map_sub, lwExpTerm2_conj_Lloop1, lwExpTerm2_conj_Lloop3]
  simp [mSigma]

end Conj

/-! ## 13. Kernel facts: `LWExpKer` of `S^{(B)}`, `K⁺` and the kernel of the expansion -/

section Ker

variable {d : ℕ} (sz : Sizes d)

theorem lwExpTerm2_zdistInf_add_le (L : ℕ) [NeZero L] (u v : Zd d L) :
    zdistInf d L (u + v) ≤ zdistInf d L u + zdistInf d L v := by
  refine Finset.sup_le fun i _ => ?_
  calc zdist L ((u + v) i) = zdist L (u i + v i) := rfl
    _ ≤ zdist L (u i) + zdist L (v i) := zdist_add_le L (u i) (v i)
    _ ≤ zdistInf d L u + zdistInf d L v :=
        add_le_add (Finset.le_sup (f := fun j => zdist L (u j)) (Finset.mem_univ i))
          (Finset.le_sup (f := fun j => zdist L (v j)) (Finset.mem_univ i))

/-- A kernel that decays eventually decays for every `n` (a finite patch of the constant). -/
theorem lwExpTerm2_ker_of_eventually (K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) {C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) (n₀ : ℕ) (h : ∀ n, n₀ ≤ n → ∀ a b : Zd d (sz.L n),
      ‖K n a b‖ ≤ C * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))) : LWExpKer sz K := by
  set M : ℝ := ∑ n ∈ Finset.range n₀, ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
    ‖K n a b‖ * Real.exp (c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨C + M, c, by linarith, hc, fun n a b => ?_⟩
  by_cases hn : n₀ ≤ n
  · refine (h n hn a b).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · have hn' : n ∈ Finset.range n₀ := Finset.mem_range.2 (not_le.1 hn)
    have h1 : ‖K n a b‖ * Real.exp (c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)) ≤ M := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun n => ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
        ‖K n a b‖ * Real.exp (c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))
        (fun n _ => Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
          mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) hn')
      refine le_trans ?_ (Finset.single_le_sum (f := fun a : Zd d (sz.L n) => ∑ b : Zd d (sz.L n),
        ‖K n a b‖ * Real.exp (c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))
        (fun a _ => Finset.sum_nonneg fun b _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ a))
      exact Finset.single_le_sum (f := fun b : Zd d (sz.L n) =>
        ‖K n a b‖ * Real.exp (c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))
        (fun b _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (Finset.mem_univ b)
    have h2 : ‖K n a b‖ ≤ M * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) := by
      have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))).le
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
      exact this
    exact h2.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

theorem lwExpTerm2_ker_add {K₁ K₂ : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ} (h₁ : LWExpKer sz K₁)
    (h₂ : LWExpKer sz K₂) : LWExpKer sz (fun n => K₁ n + K₂ n) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := h₁
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := h₂
  refine ⟨C₁ + C₂, min c₁ c₂, by linarith, lt_min hc₁ hc₂, fun n a b => ?_⟩
  beta_reduce
  have e1 : Real.exp (-(c₁ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) ≤
      Real.exp (-(min c₁ c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right (min_le_left c₁ c₂) (Nat.cast_nonneg (zdistInf d (sz.L n) (a - b)))
    linarith
  have e2 : Real.exp (-(c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) ≤
      Real.exp (-(min c₁ c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right (min_le_right c₁ c₂) (Nat.cast_nonneg (zdistInf d (sz.L n) (a - b)))
    linarith
  calc ‖(K₁ n + K₂ n) a b‖ = ‖K₁ n a b + K₂ n a b‖ := rfl
    _ ≤ ‖K₁ n a b‖ + ‖K₂ n a b‖ := norm_add_le _ _
    _ ≤ C₁ * Real.exp (-(c₁ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) +
        C₂ * Real.exp (-(c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) := add_le_add (h₁ n a b) (h₂ n a b)
    _ ≤ C₁ * Real.exp (-(min c₁ c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) +
        C₂ * Real.exp (-(min c₁ c₂ * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁.le) (mul_le_mul_of_nonneg_left e2 hC₂.le)
    _ = _ := by ring

theorem lwExpTerm2_ker_smul {K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ} (m : ℕ → ℂ)
    (hm : ∀ n, ‖m n‖ ≤ 1) (h : LWExpKer sz K) : LWExpKer sz (fun n => m n • K n) := by
  obtain ⟨C, c, hC, hc, h⟩ := h
  refine ⟨C, c, hC, hc, fun n a b => ?_⟩
  beta_reduce
  calc ‖(m n • K n) a b‖ = ‖m n‖ * ‖K n a b‖ := by simp [Matrix.smul_apply]
    _ ≤ 1 * ‖K n a b‖ := mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact h n a b

theorem lwExpTerm2_ker_one : LWExpKer sz (fun n => (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)) := by
  refine ⟨1, 1, one_pos, one_pos, fun n a b => ?_⟩
  beta_reduce
  by_cases h : a = b
  · subst h
    simp [zdistInf]
  · rw [Matrix.one_apply_ne h]
    simp only [norm_zero]
    positivity

/-- The support of `S^{(B)}`: nearest neighbours and the diagonal. -/
theorem lwExpTerm2_SB_support (L : ℕ) [NeZero L] (g : ℝ) {a b : Zd d L} (h : SB d L g a b ≠ 0) :
    zdistInf d L (a - b) ≤ 1 := by
  rw [SB_apply] at h
  unfold sbKernel at h
  refine (zdistInf_le_zdistD d L (a - b)).trans ?_
  by_cases h0 : a - b = 0
  · simp [h0]
  · by_cases h1 : zdistD d L (a - b) = 1
    · exact h1.le
    · exfalso; apply h; simp [h0, h1]

/-- **`LWExpKer` of `S^{(B)}`**: support on `|a - b|₁ ≤ 1`, entries `≤ 1`. -/
theorem lwExpTerm2_ker_SB : LWExpKer sz (fun n => SB d (sz.L n) (sz.lam n)) := by
  refine ⟨Real.exp 1, 1, Real.exp_pos 1, one_pos, fun n a b => ?_⟩
  beta_reduce
  by_cases h : SB d (sz.L n) (sz.lam n) a b = 0
  · rw [h, norm_zero]; positivity
  · have h1 := lwExpTerm2_SB_support (d := d) (sz.L n) (sz.lam n) h
    have h2 : ‖SB d (sz.L n) (sz.lam n) a b‖ ≤ 1 := by
      rw [← sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) a]
      exact Finset.single_le_sum (f := fun b => ‖SB d (sz.L n) (sz.lam n) a b‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ b)
    have h3 : (1 : ℝ) ≤ Real.exp 1 * Real.exp (-(1 * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ))) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
      linarith
    exact h2.trans h3

/-- Left multiplication by `S^{(B)}` keeps the decay (`|a - x| ≤ 1` on the support, `Σ_x ‖S^{(B)}_{ax}‖ = 1`). -/
theorem lwExpTerm2_ker_SB_mul {K : ∀ n, Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ} (h : LWExpKer sz K) :
    LWExpKer sz (fun n => SB d (sz.L n) (sz.lam n) * K n) := by
  obtain ⟨C, c, hC, hc, h⟩ := h
  refine ⟨C * Real.exp c, c, mul_pos hC (Real.exp_pos c), hc, fun n a b => ?_⟩
  beta_reduce
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ x, ‖SB d (sz.L n) (sz.lam n) a x * K n x b‖
      ≤ ∑ x, ‖SB d (sz.L n) (sz.lam n) a x‖ *
          (C * Real.exp c * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul]
        by_cases hx : SB d (sz.L n) (sz.lam n) a x = 0
        · simp [hx]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := lwExpTerm2_SB_support (d := d) (sz.L n) (sz.lam n) hx
        have h2 : zdistInf d (sz.L n) (a - b) ≤ zdistInf d (sz.L n) (a - x) + zdistInf d (sz.L n) (x - b) := by
          have := lwExpTerm2_zdistInf_add_le (d := d) (sz.L n) (a - x) (x - b)
          rwa [show a - x + (x - b) = a - b by ring] at this
        have h3 : (zdistInf d (sz.L n) (a - b) : ℝ) ≤ 1 + (zdistInf d (sz.L n) (x - b) : ℝ) := by
          have : zdistInf d (sz.L n) (a - b) ≤ 1 + zdistInf d (sz.L n) (x - b) := by omega
          exact_mod_cast this
        refine (h n x b).trans ?_
        calc C * Real.exp (-(c * ((zdistInf d (sz.L n) (x - b) : ℕ) : ℝ)))
            ≤ C * (Real.exp c * Real.exp (-(c * ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)))) := by
              refine mul_le_mul_of_nonneg_left ?_ hC.le
              rw [← Real.exp_add]
              apply Real.exp_le_exp.2
              nlinarith
          _ = _ := by ring
    _ = _ := by
        rw [← Finset.sum_mul, sum_norm_SB_row d (sz.L n) (sz.lam n) (sz.three_le_L n) a, one_mul]

/-- **`LWExpKer` of `K⁺ = t S^{(B)} Θ_{t m²}`** along the flow: `lwSplus_decay` (the fine entries `S⁺_{xy} = W^{-d} K⁺_{[x][y]}`,
`lwSpOf_eq`), uniform in `n` after a finite patch (`0 < ĝ ≤ 𝔡⁻¹` holds only eventually). -/
theorem lwExpTerm2_ker_Kp (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    LWExpKer sz (fun n => LWExpKp sz n (STflowE z n) (t n)) := by
  have h𝔡 : 0 < 𝔡 := hz.1.2.1
  obtain ⟨C, c, hC, hc, hdec⟩ := lwSplus_decay d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hz.1.2.2.2.2] with n hn
    have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hlam
  refine lwExpTerm2_ker_of_eventually sz _ hC hc n₀ fun n hn a b => ?_
  have ht1 : t n < 1 := st5_t_lt_one sz hz htz n
  have hE2 : |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz n
  set x : Idx d (sz.L n) (sz.W n) := (splitEquiv d (sz.L n) (sz.W n)).symm (a, ⟨0, pow_pos (sz.W_pos n) d⟩) with hx
  set y : Idx d (sz.L n) (sz.W n) := (splitEquiv d (sz.L n) (sz.W n)).symm (b, ⟨0, pow_pos (sz.W_pos n) d⟩) with hy
  have hxa : lwExpTerm2_bl d (sz.L n) (sz.W n) x = a := by
    have := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply (a, (⟨0, pow_pos (sz.W_pos n) d⟩ : Fin (sz.W n ^ d)))
    exact congrArg Prod.fst this
  have hyb : lwExpTerm2_bl d (sz.L n) (sz.W n) y = b := by
    have := (splitEquiv d (sz.L n) (sz.W n)).apply_symm_apply (b, (⟨0, pow_pos (sz.W_pos n) d⟩ : Fin (sz.W n ^ d)))
    exact congrArg Prod.fst this
  have h1 := hdec sz n (hn₀ n hn).1 (hn₀ n hn).2 (t n) (STflowE z n) (ht0 n) ht1 (st6_flowE_le sz hz n) x y
  rw [lwExpTerm2_hSp sz n (STflowE z n) (t n) hE2 (ht0 n) ht1 x y, hxa, hyb] at h1
  have hW : (0 : ℝ) < (((sz.W n : ℕ) : ℝ) ^ d) := by
    have := sz.W_pos n
    positivity
  have hnorm : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  rw [norm_mul, hnorm] at h1
  have hWi : 0 < ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := inv_pos.2 hW
  have h3 : lwBdist d (sz.L n) (sz.W n) x y = zdistD d (sz.L n) (a - b) := by
    unfold lwBdist
    have e1 : (split d (sz.L n) (sz.W n) x).1 = a := hxa
    have e2 : (split d (sz.L n) (sz.W n) y).1 = b := hyb
    rw [e1, e2]
  rw [h3] at h1
  have h2 : ‖LWExpKp sz n (STflowE z n) (t n) a b‖ ≤ C * Real.exp (-(c * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ))) := by
    have h4 : ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * ‖LWExpKp sz n (STflowE z n) (t n) a b‖ ≤
        ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ * (C * Real.exp (-(c * ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ)))) := by
      calc _ ≤ _ := h1
        _ = _ := by ring
    exact le_of_mul_le_mul_left h4 hWi
  refine h2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le)
  have : ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ) ≤ ((zdistD d (sz.L n) (a - b) : ℕ) : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) (a - b)
  have := mul_le_mul_of_nonneg_left this hc.le
  linarith

/-- `LWExpKer` of `K = S^{(B)} (m + m³ K⁺)` along the flow (the kernel of `(Oe2x)`): `S^{(B)}`, `1`, `K⁺`. -/
theorem lwExpTerm2_ker_KK (hd : 3 ≤ d) {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z)
    {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htz : ∀ n, t n ≤ lemT (z n)) :
    LWExpKer sz (fun n => lwExpTerm2_KK sz n (STflowE z n) (t n)) := by
  have hm : ∀ n, ‖mE (STflowE z n)‖ ≤ 1 := fun n =>
    (norm_mE (by linarith [st6_flowE_le sz hz n, hκ])).le
  have hm3 : ∀ n, ‖mE (STflowE z n) ^ 3‖ ≤ 1 := fun n => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (hm n)
  exact lwExpTerm2_ker_SB_mul sz (lwExpTerm2_ker_add sz (lwExpTerm2_ker_smul sz (fun n => mE (STflowE z n)) hm
    (lwExpTerm2_ker_one sz)) (lwExpTerm2_ker_smul sz (fun n => mE (STflowE z n) ^ 3) hm3
    (lwExpTerm2_ker_Kp sz hd hκ hz ht0 htz)))

end Ker

/-! ## 14. The deterministic bound of one cut: `t = 0`, `σ_c = -`, the five terms -/

section Bound

variable {d : ℕ} (sz : Sizes d) (n : ℕ)

private theorem lwExpTerm2_vec1 {α : Type*} (x : α) : (![x] : Fin 1 → α) = fun _ => x := by
  funext i
  fin_cases i
  rfl

/-- `LWcut = 0` at `t = 0` (`G_0 = m I`, so `X ≡ 0`). -/
theorem lwExpTerm2_cut_zero {E : ℝ} (hE : |E| ≤ 2) (σc σo : Bool) (ac ao : Zd d (sz.L n)) (ω : sz.SeqΩ) :
    LWcut sz n E 0 σc σo ac ao ω = 0 := by
  unfold LWcut
  have : ∀ a₁ : Zd d (sz.L n), Lloop sz n E 0 ![σc] ![a₁] ω - mSigma E σc = 0 := fun a₁ => by
    rw [lwExpTerm2_vec1, lwExpTerm2_vec1, Lloop_zero_one sz n hE σc a₁ ω, sub_self]
  simp [this]

theorem lwExpTerm2_eta_inv_le {κ E t : ℝ} (hκ : 0 < κ) (hE : |E| ≤ 2 - κ) (ht : t < 1) :
    (etaT E t)⁻¹ ≤ (2 / Real.sqrt (2 * κ)) * (1 - t)⁻¹ := by
  have hs : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  have h1 := st6_mE_im_ge hκ hE
  have h1t : 0 < 1 - t := by linarith
  have h2 : (1 - t) * (Real.sqrt (2 * κ) / 2) ≤ etaT E t := by
    unfold etaT
    exact mul_le_mul_of_nonneg_left h1 h1t.le
  have h3 : 0 < (1 - t) * (Real.sqrt (2 * κ) / 2) := by positivity
  calc (etaT E t)⁻¹ ≤ ((1 - t) * (Real.sqrt (2 * κ) / 2))⁻¹ := inv_anti₀ h3 h2
    _ = _ := by field_simp

theorem lwExpTerm2_bound_true (hG : GaussIBP sz) {E t : ℝ} (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (σ : Bool)
    (ac ao : Zd d (sz.L n)) {u e B ζ c : ℝ} (hu : 0 ≤ u) (he : 0 ≤ e) (hB0 : 0 ≤ B) (hB1 : B ≤ 1) (hζ : 1 ≤ ζ)
    (hc : 0 ≤ c) (hec : e ≤ c * ζ)
    (hP1 : ‖lwExpTerm2_Pa sz n (lwExpTerm2_KK sz n E t) E t σ ac ao‖ ≤ u * B ^ 3)
    (hP2 : ‖lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t true σ ac ao‖ ≤ u * (e * B ^ (5 / 2 : ℝ)))
    (hP3 : ‖lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n E t) E t false σ ac ao‖ ≤ u * (e * B ^ (5 / 2 : ℝ)))
    (hP4 : ‖lwExpTerm2_Pc sz n (lwExpTerm2_KK sz n E t) E t σ ac ao‖ ≤ u * (e * B ^ 3))
    (hP5 : ‖lwExpTerm2_Pd sz n (LWExpKp sz n E t) E t σ ac ao‖ ≤ u * (e * B ^ (5 / 2 : ℝ))) :
    ‖∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP)‖ ≤ u * ((1 + 4 * c) * (ζ * B ^ (5 / 2 : ℝ))) := by
  have hB52 : 0 ≤ B ^ (5 / 2 : ℝ) := Real.rpow_nonneg hB0 _
  have hB3 : B ^ 3 ≤ B ^ (5 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge' hB0 hB1 (by norm_num : (0 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 3)
    rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  have hRHS : 0 ≤ u * ((1 + 4 * c) * (ζ * B ^ (5 / 2 : ℝ))) := by
    have : 0 ≤ ζ := by linarith
    positivity
  rcases ht0.eq_or_lt with rfl | ht
  · have : ∫ ω, LWcut sz n E 0 true σ ac ao ω ∂(sz.seqP) = 0 := by
      simp only [lwExpTerm2_cut_zero sz n hE.le, integral_zero]
    rw [this, norm_zero]
    exact hRHS
  · have hG' : ∫ ω, LWcut sz n E t true σ ac ao ω ∂(sz.seqP) = _ := lwExpTerm2_cut_expand sz n hG hE ht ht1 σ ac ao
    rw [hG']
    have hm : ‖mE E‖ = 1 := norm_mE hE.le
    have ht' : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]; exact ht1.le
    have tri : ∀ a b c d e : ℂ, ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := fun a b c d e => by
      calc ‖a + b + c + d + e‖ ≤ ‖a + b + c + d‖ + ‖e‖ := norm_add_le _ _
        _ ≤ (‖a + b + c‖ + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
        _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by gcongr; exact norm_add_le _ _
    have hmul : ∀ (w : ℂ) (x : ℂ), ‖w‖ ≤ 1 → ‖w * x‖ ≤ ‖x‖ := fun w x hw => by
      rw [norm_mul]
      calc ‖w‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
        _ = ‖x‖ := one_mul _
    refine (tri _ _ _ _ _).trans ?_
    have hm' : ‖mE E‖ ≤ 1 := hm.le
    have e2 := (hmul _ _ ht').trans hP2
    have e3 := (hmul _ _ ht').trans hP3
    have e4 := (hmul _ _ hm').trans hP5
    have e5 := (hmul _ _ ht').trans hP4
    have hζ0 : 0 ≤ ζ := by linarith
    have hB52ζ : B ^ (5 / 2 : ℝ) ≤ ζ * B ^ (5 / 2 : ℝ) := by nlinarith
    have h_a : u * B ^ 3 ≤ u * (ζ * B ^ (5 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hB3.trans hB52ζ) hu
    have h_b : u * (e * B ^ (5 / 2 : ℝ)) ≤ u * (c * (ζ * B ^ (5 / 2 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ hu
      calc e * B ^ (5 / 2 : ℝ) ≤ (c * ζ) * B ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_right hec hB52
        _ = _ := by ring
    have h_c : u * (e * B ^ 3) ≤ u * (c * (ζ * B ^ (5 / 2 : ℝ))) := by
      refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB3 he) hu) h_b
    calc _ ≤ u * B ^ 3 + u * (e * B ^ (5 / 2 : ℝ)) + u * (e * B ^ (5 / 2 : ℝ)) + u * (e * B ^ (5 / 2 : ℝ)) +
          u * (e * B ^ 3) := by linarith
      _ ≤ u * (ζ * B ^ (5 / 2 : ℝ)) + u * (c * (ζ * B ^ (5 / 2 : ℝ))) + u * (c * (ζ * B ^ (5 / 2 : ℝ))) +
          u * (c * (ζ * B ^ (5 / 2 : ℝ))) + u * (c * (ζ * B ^ (5 / 2 : ℝ))) := by linarith
      _ = _ := by ring

theorem lwExpTerm2_norm_cut_false (E t : ℝ) (σ : Bool) (ac ao : Zd d (sz.L n)) :
    ‖∫ ω, LWcut sz n E t false σ ac ao ω ∂(sz.seqP)‖ = ‖∫ ω, LWcut sz n E t true (!σ) ao ac ω ∂(sz.seqP)‖ := by
  have : ∫ ω, LWcut sz n E t true (!σ) ao ac ω ∂(sz.seqP) =
      ∫ ω, (starRingEnd ℂ) (LWcut sz n E t false σ ac ao ω) ∂(sz.seqP) := by
    simp only [lwExpTerm2_cut_conj]
  rw [this, integral_conj, Complex.norm_conj]

end Bound

/-! ## 15. Targets 7-9: the assembly and the consistency of the new pins with the merged ones -/

/-- **Target 7: the assembly** `(eq:ELW_term)` → `LWCutExp` from the five term bounds. -/
theorem lwCutExp_of_terms (d : ℕ) :
    LWExpI1K d → LWExpI23K d → LWExpI41K d → LWExpG5' d → LWCutExp d := by
  intro h1 h23 h41 h5 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hz htz
  have hE2 : ∀ n, |STflowE z n| < 2 := st6_flowE_lt_two sz hκ hz
  have hEκ : ∀ n, |STflowE z n| ≤ 2 - κ := st6_flowE_le sz hz
  have hKK := lwExpTerm2_ker_KK sz hd hκ hz ht0 htz
  have hG : GaussIBP sz := gaussIBP sz
  have p1 := (st6_prec_det_iff sz hsz _ _).1
    (h1 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz _ hKK hLW hLK)
  have p23 := (st6_prec_det_iff sz hsz _ _).1
    (h23 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz _ hKK hLE hLW hLmax hLK hDec)
  have p41 := (st6_prec_det_iff sz hsz _ _).1
    (h41 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz _ hKK hLW hLmax hLK)
  have p5 := (st6_prec_det_iff sz hsz _ _).1
    (h5 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec)
  refine (st6_prec_det_iff sz hsz _ _).2 ?_
  intro τ hτ
  have hτ2 : 0 < τ / 2 := half_pos hτ
  have hs : 0 < Real.sqrt (2 * κ) := Real.sqrt_pos.2 (by linarith)
  set c : ℝ := 2 / Real.sqrt (2 * κ) with hc
  have hc0 : 0 ≤ c := by positivity
  filter_upwards [p1 (τ / 2) hτ2, p23 (τ / 2) hτ2, p41 (τ / 2) hτ2, p5 (τ / 2) hτ2,
    ((tendsto_rpow_atTop hτ2).comp hsz).eventually (eventually_ge_atTop (1 + 4 * c)),
    st5_Bctl_le_one sz hκ hε hz htz] with n a1 a23 a41 a5 hN hB
  rintro ⟨⟨⟨σc, σo⟩, ac, ao⟩, hg⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := Nat.cast_pos.mpr (by have := sz.one_le_size n; omega)
  set B : ℝ := sz.Bctl n (t n) with hBdef
  have hB0 : 0 < B := STBctl_pos sz n (ht1 n)
  have hB1 : B ≤ 1 := hB (t n) le_rfl
  have h1t : 0 < 1 - t n := by linarith [ht1 n]
  have hζ : 1 ≤ (1 - t n)⁻¹ := one_le_inv₀ h1t |>.2 (by linarith [ht0 n])
  have hec := lwExpTerm2_eta_inv_le hκ (hEκ n) (ht1 n)
  have he0 : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := (inv_pos.2 (etaT_pos (hE2 n) (ht1 n))).le
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]; congr 1; ring
  have hu0 : 0 ≤ N ^ (τ / 2) := Real.rpow_nonneg hNpos.le _
  have hX0 : 0 ≤ (1 - t n)⁻¹ * B ^ (5 / 2 : ℝ) := by
    have := Real.rpow_nonneg hB0.le (5 / 2 : ℝ)
    positivity
  have key : ∀ (σ : Bool) (ac ao : Zd d (sz.L n)),
      ‖∫ ω, LWcut sz n (STflowE z n) (t n) true σ ac ao ω ∂(sz.seqP)‖ ≤
        N ^ τ * ((1 - t n)⁻¹ * B ^ (5 / 2 : ℝ)) := by
    intro σ ac ao
    have e1 : ‖lwExpTerm2_Pa sz n (lwExpTerm2_KK sz n (STflowE z n) (t n)) (STflowE z n) (t n) σ ac ao‖ ≤
        N ^ (τ / 2) * B ^ 3 := a1 ((true, ![σ, true]), ![ao, ac])
    have e2 : ‖lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n (STflowE z n) (t n)) (STflowE z n) (t n) true σ ac ao‖ ≤
        N ^ (τ / 2) * ((etaT (STflowE z n) (t n))⁻¹ * B ^ (5 / 2 : ℝ)) := a23 ((true, σ), ![ac, ao])
    have e3 : ‖lwExpTerm2_Pb sz n (lwExpTerm2_KK sz n (STflowE z n) (t n)) (STflowE z n) (t n) false σ ac ao‖ ≤
        N ^ (τ / 2) * ((etaT (STflowE z n) (t n))⁻¹ * B ^ (5 / 2 : ℝ)) := a23 ((false, σ), ![ac, ao])
    have e4 : ‖lwExpTerm2_Pc sz n (lwExpTerm2_KK sz n (STflowE z n) (t n)) (STflowE z n) (t n) σ ac ao‖ ≤
        N ^ (τ / 2) * ((etaT (STflowE z n) (t n))⁻¹ * B ^ 3) := a41 ((true, σ), ![ao, ac])
    have e5 : ‖lwExpTerm2_Pd sz n (LWExpKp sz n (STflowE z n) (t n)) (STflowE z n) (t n) σ ac ao‖ ≤
        N ^ (τ / 2) * ((etaT (STflowE z n) (t n))⁻¹ * B ^ (5 / 2 : ℝ)) := a5 ⟨((true, σ), ![ao, ac]), hg⟩
    have hb := lwExpTerm2_bound_true sz n hG (hE2 n) (ht0 n) (ht1 n) σ ac ao hu0 he0 hB0.le hB1 hζ hc0 hec
      e1 e2 e3 e4 e5
    refine hb.trans ?_
    rw [hNτ]
    calc N ^ (τ / 2) * ((1 + 4 * c) * ((1 - t n)⁻¹ * B ^ (5 / 2 : ℝ)))
        = (N ^ (τ / 2) * (1 + 4 * c)) * ((1 - t n)⁻¹ * B ^ (5 / 2 : ℝ)) := by ring
      _ ≤ (N ^ (τ / 2) * N ^ (τ / 2)) * ((1 - t n)⁻¹ * B ^ (5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hu0) hX0
  cases σc
  · rw [lwExpTerm2_norm_cut_false]
    exact key _ _ _
  · exact key _ _ _


/-- **Target 8: `LWExpG5'` contains `LWExpG5`** (the case `p.1 = (false, false)`: first kernel `S^{(B)}`, last charge `-`). -/
theorem lwExpG5_of_G5' (d : ℕ) : LWExpG5' d → LWExpG5 d := by
  intro h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have h' := (st6_prec_det_iff sz hsz _ _).1 (h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLE hLW hLmax hLK hDec)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [h' τ hτ] with n hn
  intro p
  exact hn ⟨((false, false), p.1), p.2⟩

/-- **Target 9a: the merged `I₁` is the case `K = S^{(B)}` of `LWExpI1K`** (`lwExpTerm2_ker_SB`). -/
theorem lwExpI1_of_K (d : ℕ) : LWExpI1K d → LWExpI1 d := by
  intro h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLW hLK
  exact h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz (fun n => SB d (sz.L n) (sz.lam n))
    (lwExpTerm2_ker_SB sz) hLW hLK

/-- **Target 9b: the merged `I₄₁` is the case `K = S^{(B)}`, `s = false` of `LWExpI41K`.** -/
theorem lwExpI41_of_K (d : ℕ) : LWExpI41K d → LWExpI41 d := by
  intro h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz hLW hLmax hLK
  have hsz : sz.SizeTendsto := hz.1.2.2.1
  have h' := (st6_prec_det_iff sz hsz _ _).1 (h hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hz t ht0 htz
    (fun n => SB d (sz.L n) (sz.lam n)) (lwExpTerm2_ker_SB sz) hLW hLmax hLK)
  refine (st6_prec_det_iff sz hsz _ _).2 fun τ hτ => ?_
  filter_upwards [h' τ hτ] with n hn
  intro p
  exact hn ((p.1, false), p.2)

end RBM.Gauss.Sizes

/-! ## 16. Compiled nonempty instances (`d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, the merged data `sz0`, `z0`, `tInst`
of `RBM.Gauss.LWInst`): every deterministic hypothesis is discharged (`3 ≤ 3`, `0 < 1/10`, `flow_z0`, `0 ≤ tInst`,
`tInst ≤ lemT z0`); the local laws (`LWAvgLaw`, `STLK`, `STLmax`, `STLocalEntry`, `STDecay`) and the four term pins
(`LWExpI1K`, `LWExpI23K`, `LWExpI41K`, `LWExpG5'`; LW-14d, LW-14c) are other gates' pins and stay hypotheses. -/

namespace RBM.Gauss.LWInst

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst Filter

theorem lwExpTerm2_inst_cut (h1 : LWExpI1K 3) (h23 : LWExpI23K 3) (h41 : LWExpI41K 3) (h5 : LWExpG5' 3)
    (hLE : STLocalEntry sz0 (STflowE z0) tInst) (hLW : LWAvgLaw sz0 (STflowE z0) tInst)
    (hLmax : STLmax sz0 (STflowE z0) tInst) (hLK : STLK sz0 (STflowE z0) tInst)
    (hDec : STDecay sz0 (STflowE z0) tInst) :
    Prec sz0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ 1 - tInst n})
      (fun n p _ => ‖∫ ω, LWE sz0 n (STflowE z0 n) (tInst n) p.1.1 p.1.2 ω ∂(sz0.seqP)‖)
      (fun n _ _ => (1 - tInst n)⁻¹ * (sz0.Bctl n (tInst n)) ^ (5 / 2 : ℝ)) :=
  inst_LWtermEXP (lwTermEXP_of_cut 3 (lwCutExp_of_terms 3 h1 h23 h41 h5)) hLE hLW hLmax hLK hDec

theorem lwExpTerm2_inst_ker_SB : LWExpKer sz0 (fun n => SB 3 (sz0.L n) (sz0.lam n)) :=
  lwExpTerm2_ker_SB sz0

theorem lwExpTerm2_inst_ker_Kp : LWExpKer sz0 (fun n => LWExpKp sz0 n (STflowE z0 n) (tInst n)) :=
  lwExpTerm2_ker_Kp sz0 le_rfl (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) flow_z0
    tInst_range.1 tInst_range.2

theorem lwExpTerm2_inst_ker_KK : LWExpKer sz0 (fun n => lwExpTerm2_KK sz0 n (STflowE z0 n) (tInst n)) :=
  lwExpTerm2_ker_KK sz0 le_rfl (κ := 1 / 10) (ε := 1 / 10) (𝔠 := 1 / 6) (𝔡 := 1 / 10) (by norm_num) flow_z0
    tInst_range.1 tInst_range.2

/-- The expansion of one cut at the instance data (`n = 0`: `L = 4`, `W = 32`, `t = 1/16`, `σ_c = σ_o = +`). -/
theorem lwExpTerm2_inst_expand :
    ∫ ω, LWcut sz0 0 (STflowE z0 0) (tInst 0) true true 0 0 ω ∂(sz0.seqP) =
      lwExpTerm2_Pa sz0 0 (lwExpTerm2_KK sz0 0 (STflowE z0 0) (tInst 0)) (STflowE z0 0) (tInst 0) true 0 0 +
        ((tInst 0 : ℝ) : ℂ) * lwExpTerm2_Pb sz0 0 (lwExpTerm2_KK sz0 0 (STflowE z0 0) (tInst 0)) (STflowE z0 0)
          (tInst 0) true true 0 0 +
        ((tInst 0 : ℝ) : ℂ) * lwExpTerm2_Pb sz0 0 (lwExpTerm2_KK sz0 0 (STflowE z0 0) (tInst 0)) (STflowE z0 0)
          (tInst 0) false true 0 0 +
        mE (STflowE z0 0) * lwExpTerm2_Pd sz0 0 (LWExpKp sz0 0 (STflowE z0 0) (tInst 0)) (STflowE z0 0)
          (tInst 0) true 0 0 +
        ((tInst 0 : ℝ) : ℂ) * lwExpTerm2_Pc sz0 0 (lwExpTerm2_KK sz0 0 (STflowE z0 0) (tInst 0)) (STflowE z0 0)
          (tInst 0) true 0 0 :=
  lwExpTerm2_cut_expand sz0 0 (Green.gaussIBP sz0) (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0)
    (by simp [tInst]) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0) true 0 0

theorem lwExpTerm2_inst_conj (ω : sz0.SeqΩ) :
    (starRingEnd ℂ) (LWcut sz0 0 (STflowE z0 0) (tInst 0) false true 0 0 ω) =
      LWcut sz0 0 (STflowE z0 0) (tInst 0) true false 0 0 ω :=
  lwExpTerm2_cut_conj sz0 0 (STflowE z0 0) (tInst 0) true 0 0 ω

theorem lwExpTerm2_inst_Kp_split :
    ((tInst 0 : ℝ) : ℂ) • (SB 3 (sz0.L 0) (sz0.lam 0) * LWExpKp sz0 0 (STflowE z0 0) (tInst 0)) =
      ((mE (STflowE z0 0)) ^ 2)⁻¹ • (LWExpKp sz0 0 (STflowE z0 0) (tInst 0) -
        ((tInst 0 : ℝ) : ℂ) • SB 3 (sz0.L 0) (sz0.lam 0)) :=
  lwExpTerm2_Kp_split sz0 0 (STflowE z0 0) (tInst 0) (st6_flowE_lt_two sz0 (by norm_num : (0 : ℝ) < 1 / 10) flow_z0 0)
    (tInst_range.1 0) (st5_t_lt_one sz0 flow_z0 tInst_range.2 0)

theorem lwExpTerm2_inst_G5 (h : LWExpG5' 3) : LWExpG5 3 := lwExpG5_of_G5' 3 h
theorem lwExpTerm2_inst_I1 (h : LWExpI1K 3) : LWExpI1 3 := lwExpI1_of_K 3 h
theorem lwExpTerm2_inst_I41 (h : LWExpI41K 3) : LWExpI41 3 := lwExpI41_of_K 3 h

end RBM.Gauss.LWInst
