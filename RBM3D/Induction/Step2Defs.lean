/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Induction.Step34Pins
import RBM3D.Kernel.Evolution
import RBM3D.Path.Walk
import RBM3D.Path.Stop

/-!
# ST2-01 (ticket T2066): the vocabulary and the pins of Step 2 of `lem:main_ind`

Moved from the T2039 design probe (`git show 0362cbc:RBM3D/Probe/T2039Pins.lean`): sections 1 and 2
(probe lines 248-818: the vocabulary of Step 2 at matrix and model level, their measurability, the
pins), the pins `STScaleExists`, `STOptL2`, `STLocalAvgOfL2` of section 12 (probe 4101-4149), and
the definitions of sections 3-12 that the pins mention (`STScaleOk`, `STScaleAdm`, `STL2decayPT`,
the list-loop matrix functionals `STLIM ... STeeM` and the grid forms `STgAN`, `STgDriftN`,
`STeeUM`, `STGridRepNAt`, `STGridRepN`, probe 2274-2296, 4995-5045, 5077-5156).  No theorem of
sections 3-12.  Section 4 holds the probe's compiled instances that use only this file.
Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`) and
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`).

Differences from the probe text: the `open` lines (`RBM.Probe.T2039` is replaced by `RBM.Gauss`:
the 24 copies of section 0 and the 4 copies of section 12.1 are the merged declarations of
`Induction/Defs.lean` and `Induction/Step34Pins.lean`, and `STeeLoop` is the merged
`Step34Pins.lean:152`), the section/namespace brackets, and the pin `STStep2`, which here
concludes the merged bundle `STStep2Concl` (DECISIONS §28, T2039 report (d).6).  Docstrings are
the probe's (their `Prop5Decay (borrowed)` remarks are stale: `prop5Decay_holds` is proved).
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal
/-! ## 1. The Step 2 vocabulary (matrix level, then model level), namespace `RBM.Gauss.Sizes`

Everything is first written for an arbitrary fine matrix `H` (the random matrix of the model at
time `u`, or the grid state `pathH`), so that the same functional is evaluated on the single-time
model (`seqHflow sz n u ω`, section 1.1) and on the grid walk (`pathH sz s t K n j ω`,
section 2.3).  The loop length is `2` throughout (Step 2, `3_5:359–363`); the general-`n`
forms of the drift and quadratic-variation terms are those of `lem:SEforLn` (ST-D3).  Merged
vocabulary used: `loopFine`, `Lloop`, `Gt`, `KLK`, `SB`, `Theta`, `tailT`, `tailW`, `Bctl`,
`zdistInf`, `etaT`, `mE`, `zt`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `K^{(1)}_σ = m(σ)` (`Def_Ktza`, `1_2:988`): `m(+) = m(E)`, `m(-) = conj m(E)`. -/
def STmsig (E : ℝ) (σ : Bool) : ℂ := if σ then mE E else (starRingEnd ℂ) (mE E)

/-- `𝓛^{(k)}_{u,σ,a}` of a fine matrix `H` (`(Eq:defGLoop)`, `1_2:824`) at size index `n`,
energy `E`, time `u`: `Lloop` is this at `H = seqHflow sz n u ω` (`STLM_seqHflow`). -/
def STLM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  loopFine d (sz.L n) (sz.W n) H (zt E u) σ a

theorem STLM_seqHflow (n : ℕ) (E u : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (ω : sz.SeqΩ) : STLM sz n E u (sz.seqHflow n u ω) σ a = Lloop sz n E u σ a ω := rfl

/-- `(𝓛 - 𝒦)^{(k)}_{u,σ,a}` of a fine matrix `H` (the merged `KLK` is deterministic). -/
def STLKM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  STLM sz n E u H σ a - STKloop sz n E u σ a

/-- **The profile `W^{-d} 𝒯̃^ℓ_{u,D}(|a-b|)`** of `(defWTTlD)` (`3_5:319`) at size index `n`, with
the paper's `L^∞` distance (paper-delta T2002b): the merged `tailW` at `ilambda = sz.lam n`,
`W = sz.W n`; `STprof sz n u D ℓ a b ≥ W^{-d-D} > 0`. -/
def STprof (n : ℕ) (u D ℓ : ℝ) (a b : Zd d (sz.L n)) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
    tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a - b) : ℕ) : ℝ)

/-- **The random control `Ĵ^ℓ_{u,D}`** of `(defCALJ)` (`3_5:365`):
`max_{σ ∈ {+,-}², a=(a₁,a₂)} |(𝓛-𝒦)^{(2)}_{u,σ,a}| / [W^{-d} 𝒯̃^ℓ_{u,D}(|a₁-a₂|)]`, of a fine matrix `H`. -/
def STJhatM (n : ℕ) (E D ℓ u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))

/-- `Ĵ^ℓ_{u,D}` of the single-time model at size index `n`. -/
def STJhat (n : ℕ) (E D ℓ u : ℝ) (ω : sz.SeqΩ) : ℝ := STJhatM sz n E D ℓ u (sz.seqHflow n u ω)

/-- `⟨G̃_u(σ) E_a⟩ = tr((G_u(σ) - m(σ)) E_a) = 𝓛^{(1)}_{u,σ,a} - m(σ)` of a fine matrix. -/
def STavgM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Bool) (a : Zd d (sz.L n)) : ℂ :=
  STLM sz n E u H (fun _ : Fin 1 => σ) (fun _ => a) - STmsig E σ

/-- **The light-weight term `𝓔^{G̃,(2)}_{u,σ,a}`** (`(def_EwtG)`, `1_2:962`, `n = 2`):
`W^d Σ_{k=1}^{2} Σ_{x,y} ⟨G̃_u(σ_k)E_x⟩ S^{(B)}_{xy} (cut^{(y)}_k ∘ 𝓛^{(2)}_{u,σ,a})`, with
`cut^{(y)}_1 (σ,a) = ((σ₁,σ₁,σ₂),(y,a₁,a₂))`, `cut^{(y)}_2 (σ,a) = ((σ₁,σ₂,σ₂),(a₁,y,a₂))`
(`Def:oper_loop`, `1_2:914–916`). -/
def STEGtM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    (STavgM sz n E u H (σ 0) x * SB d (sz.L n) (sz.lam n) x y *
        STLM sz n E u H ![σ 0, σ 0, σ 1] ![y, a 0, a 1] +
      STavgM sz n E u H (σ 1) x * SB d (sz.L n) (sz.lam n) x y *
        STLM sz n E u H ![σ 0, σ 1, σ 1] ![a 0, y, a 1])

/-- **`𝓔^{(𝓛-𝓚)×(𝓛-𝓚),(2)}_{u,σ,a}`** (`(def_ELKLK)`, `3_5:98`, `n = 2`, `k = 1`, `l = 2`):
`W^d Σ_{x,y} (𝓛-𝒦)_{σ,(x,a₂)} S^{(B)}_{xy} (𝓛-𝒦)_{σ,(a₁,y)}` (`cutL^{(x)}_{1,2}(σ,a) = (σ,(x,a₂))`,
`cutR^{(y)}_{1,2}(σ,a) = (σ,(a₁,y))`). -/
def STELKLKM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ x : Zd d (sz.L n), ∑ y : Zd d (sz.L n),
    STLKM sz n E u H σ ![x, a 1] * SB d (sz.L n) (sz.lam n) x y * STLKM sz n E u H σ ![a 0, y]

/-- **The operator `Θ^{(2)}_{u,σ}`** of `DefTHUST` (`3_5:109–113`, `n = 2`) acting on a tensor
`A : (Z_L^d)² → ℂ`: `Σ_{i=1}^{2} Σ_b (M S^{(B)} (1 - u M S^{(B)})^{-1})_{a_i b} A_{a^{(i)}(b)}`,
`M = m(σ₁) m(σ₂)` (the same for both `i`: `σ₃ = σ₁`); `S (1 - u M S)^{-1} = S Θ_{uM}` with the
merged `Theta`. -/
def STthetaOp (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  ∑ i : Fin 2, ∑ b : Zd d (sz.L n),
    (STmsig E (σ 0) * STmsig E (σ 1)) *
      ((SB d (sz.L n) (sz.lam n) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1)))) (a i) b) *
      A (Function.update a i b)

/-- **The quadratic-variation loop `(𝓔⊗𝓔)^{M,(2;k)}_{u,σ,a,a}`** (`def:CALE`, `3_5:176–190`, `n = 2`,
`a' = a`): `W^d Σ_{c,c'} S^{(B)}_{cc'} 𝓛^{(6)}_{(σ⊗σ̄)^{(k)}, (a⊗a)^{(k)}(c',c)}`.  For `k = 1`
(`3_5:672`): signs `(σ₁,σ₂,σ₁,-σ₁,-σ₂,-σ₁)`, labels `(a₁,a₂,c',a₂,a₁,c)`; for `k = 2` the roles of
the two edges are exchanged: signs `(σ₂,σ₁,σ₂,-σ₂,-σ₁,-σ₂)`, labels `(a₂,a₁,c',a₁,a₂,c)`. -/
def STEEkM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ c : Zd d (sz.L n), ∑ c' : Zd d (sz.L n),
    SB d (sz.L n) (sz.lam n) c c' *
      (if k = 0 then
        STLM sz n E u H ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a 0, a 1, c', a 1, a 0, c]
      else
        STLM sz n E u H ![σ 1, σ 0, σ 1, !(σ 1), !(σ 0), !(σ 1)] ![a 1, a 0, c', a 0, a 1, c])

/-- `(𝓔⊗𝓔)^{M,(2)} = Σ_{k=1}^2 (𝓔⊗𝓔)^{M,(2;k)}` (`(defEOTE)`). -/
def STEEM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) : ℂ :=
  STEEkM sz n E u H 0 σ a + STEEkM sz n E u H 1 σ a

/-- `(G_u - M)_{xy}` of a fine matrix `H` (`M = m(E) I`). -/
def STGMM (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  Gres H (zt E u) true x y - (if x = y then mE E else 0)

theorem STGMM_seqHflow (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    STGMM sz n E u (sz.seqHflow n u ω) x y = STGM sz n E u ω x y := rfl

end RBM.Gauss.Sizes
/-! ### 1.1 Measurability of the Step 2 functionals in the matrix (needed to transfer between
the single-time model and the grid walk, and for the stopping time of section 1.2) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

section Meas

variable (n : ℕ) (E u : ℝ)

theorem STLM_measurable {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLM sz n E u H σ a :=
  walk_measurable_loopFine d (sz.L n) (sz.W n) (zt E u) σ a

theorem STLKM_measurable {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STLKM sz n E u H σ a :=
  (STLM_measurable sz n E u σ a).sub measurable_const

theorem STJhatM_measurable (D ℓ : ℝ) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STJhatM sz n E D ℓ u H := by
  have hne : (Finset.univ : Finset ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))).Nonempty :=
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have h := Finset.measurable_sup' (s := Finset.univ) hne
    (f := fun (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
        ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1))
    (fun p _ => ((STLKM_measurable sz n E u p.1 p.2).norm).div_const _)
  convert h using 1
  funext H
  simp [STJhatM, Finset.sup'_apply]

theorem STavgM_measurable (σ : Bool) (a : Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STavgM sz n E u H σ a :=
  (STLM_measurable sz n E u _ _).sub measurable_const

theorem STEGtM_measurable (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STEGtM sz n E u H σ a := by
  unfold STEGtM
  refine measurable_const.mul (Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ => ?_)
  exact ((((STavgM_measurable sz n E u _ x).mul measurable_const).mul
      (STLM_measurable sz n E u _ _)).add
    (((STavgM_measurable sz n E u _ x).mul measurable_const).mul (STLM_measurable sz n E u _ _)))

theorem STEEkM_measurable (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STEEkM sz n E u H k σ a := by
  unfold STEEkM
  refine measurable_const.mul (Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun c' _ => ?_)
  refine measurable_const.mul ?_
  by_cases hk : k = 0
  · simp only [hk, ite_true]; exact STLM_measurable sz n E u _ _
  · simp only [hk, ite_false]; exact STLM_measurable sz n E u _ _

theorem STEEM_measurable (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STEEM sz n E u H σ a :=
  (STEEkM_measurable sz n E u 0 σ a).add (STEEkM_measurable sz n E u 1 σ a)

theorem STGMM_measurable (x y : Idx d (sz.L n) (sz.W n)) :
    Measurable fun H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      STGMM sz n E u H x y :=
  (walk_measurable_Gres_apply (zt E u) true x y).sub measurable_const

end Meas

end RBM.Gauss.Sizes
/-! ## 2. The pins (`d` is the dimension; constants before the sequence)

2.1 the three conclusions of Step 2 (`1_2:1340–1351`), uniformly in `u ∈ [s,t]` (`Prec`) and per time
(`PrecPT`); 2.2 the single-time ingredients (`lem:newKLK`, the contraction inequality, the
light-weight inputs `lem:LWterm`, `lem: EWGn2_N`, the martingale estimate `lem: EMn2_N`); 2.3 the
grid representation `Sol_CalL` + `lem:DIfREP` (path layer, `PrecGrid` scale `N`); 2.4 the stopping
time `(eq:def2_stopping)`; 2.5 the deterministic `𝒦^{(2)}` decay, the net lift, and the combined
pin `STStep2`.  Premises that no ticket proves are listed with their registry class in the report. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Conclusions

variable {d : ℕ} (sz : Sizes d)

/-- **`(Gt_bound_flow)`** (`1_2:1343`), uniformly in `u ∈ [s,t]`: `|(G_u - M)_{xy}|² ≺ W^{-d}
B_{u,|x-y|/W}`, with `|x-y|/W` read as the block distance (paper-delta T2001e) and the `L^∞`
distance (T2002b). -/
def STStep2Local (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))

/-- **`(Gt_avgbound_flow)`** (`1_2:1345`), uniformly in `u ∈ [s,t]`: `max_a |tr((G_u - M)E_a)| ≺
W^{-d} B_{u,0}`, with `tr((G_u - M) E_a) = 𝓛^{(1)}_{u,+,a} - m(E)`. -/
def STStep2Avg (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - mE (E n)‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- **`(Eq:Gdecay_w)`** (`1_2:1349–1351`), uniformly in `u ∈ [s,t]`, every `D > 0`:
`|𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}| ≺ ((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5}
(W^{-d}B_{u,|a₁-a₂|}) e^{-(|a₁-a₂|/ℓ_u)^{1/2}} + W^{-D}`. -/
def STStep2Decay (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- `(Gt_bound_flow)` per time (the union over `u` outside `P`). -/
def STStep2LocalPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))

/-- `(Gt_avgbound_flow)` per time. -/
def STStep2AvgPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × Zd d (sz.L n))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) (fun _ : Fin 1 => true) (fun _ => p.2) ω - mE (E n)‖)
    (fun n p _ => sz.Bctl n (p.1 : ℝ))

/-- `(Eq:Gdecay_w)` per time. -/
def STStep2DecayPT (Cd : ℝ) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω -
        STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

end Conclusions

end RBM.Gauss.Sizes
namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ### 2.2 The single-time ingredients -/

section Ingredients

variable {d : ℕ} (sz : Sizes d)

/-- The model-level light-weight term `𝓔^{G̃,(2)}_{t,σ,a}` at time `t` (`seqHflow`). -/
def STEGt (n : ℕ) (E t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  STEGtM sz n E t (sz.seqHflow n t ω) σ a

/-- The model-level quadratic-variation loop `(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a}`. -/
def STEEk (n : ℕ) (E t : ℝ) (k : Fin 2) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (ω : sz.SeqΩ) : ℂ :=
  STEEkM sz n E t (sz.seqHflow n t ω) k σ a

/-- **`(initialGT2)`** (`3_5:28–30`) at the time sequence `t`, for a deterministic control `Ψ`:
`‖G_t - M‖_max ≺ W^{-ε₀}` and `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Ψ_t²` (the two premises of
`STGavLGEX`). -/
def STInitialGT2 (E t : ℕ → ℝ) (ε₀ : ℝ) (Ψ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2)

/-- **The class of profiles `Ψ_t(|a-b|)`** of `lem:LWterm` (`3_5:385–393`): deterministic
`0 < Ψ_t(r) ≤ W^{-ε₀}` (`r ∈ ℕ` the block distance), nonincreasing in `r`, with `(eq:Psi)`:
`W^{-d/2} ≲ Ψ_t(0) ≍ Ψ_t(r)` for `r ≤ C` (the implicit constants depend on `C`), and
`Ψ_t(r₁)/Ψ_t(r₂) ≤ C₁ (r₂/r₁)^{C₂}` for `1 ≤ r₁ ≤ r₂` with constants `C₁, C₂ > 1`. -/
def STPsiClass (ε₀ : ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  (∀ n r, 0 < Ψ n r ∧ Ψ n r ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ∧
    (∀ n r r', r ≤ r' → Ψ n r' ≤ Ψ n r) ∧
    (∀ C : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ c⁻¹ * Ψ n 0 ∧ ∀ r ≤ C, c * Ψ n 0 ≤ Ψ n r) ∧
    (∃ C₁ C₂ : ℝ, 1 < C₁ ∧ 1 < C₂ ∧ ∀ n r₁ r₂ : ℕ, 1 ≤ r₁ → r₁ ≤ r₂ →
      Ψ n r₁ / Ψ n r₂ ≤ C₁ * ((r₂ : ℝ) / r₁) ^ C₂)

/-- **`(eq:LW_assm)`** (`3_5:388`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ Ψ_t²(|a-b|)` for `σ ∈ {(+,-),(-,+)}`. -/
def STLWassm (E t : ℕ → ℝ) (Ψ : ℕ → ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (t n) p.1.1 p.2 ω‖)
    (fun n p _ => (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)

/-- **`(eq:LW_assm_exp)`** (`3_5:409`): `𝓛^{(2)}_{t,σ,(a,b)} ≺ W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)` for
`σ ∈ {(+,-),(-,+)}`, at the deterministic scale `ℓ_n`. -/
def STLWassmExp (E t : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (t n) p.1.1 p.2 ω‖)
    (fun n p _ => STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))

end Ingredients

/-- **`lem:newKLK`** (`3_5:371–378`, proof `3_5:610–654`), deterministic form: there are `C, δ₀ > 0`
(depending on `d`, `κ`, `𝔡` only: through `prop:ThfadC`, `lem:propT`) such that for every fine
Hermitian `H` with `‖G_u - M‖_max ≤ δ₀` (the weak local law `(Gtmwc)` at `u`, eventually true with
high probability) and every `0 ≤ ℓ ≤ L`, `D ≥ 0`: `|Θ^{(2)}_{u,σ} ∘ (𝓛-𝒦)^{(2)}_{u,σ}|` and
`|𝓔^{(𝓛-𝓚)×(𝓛-𝓚)}_{u,σ}|` are at most `C/(1-u) (Ĵ + Ĵ² 1_{ℓ≥1}) W^{-d} 𝒯̃^ℓ_{u,D}(|a-b|)`
(`(juwo2=klk)`, `(juwo=Lklk)`), as the predicate `STNewKLKAt` at the constants `C, δ₀`.  Inputs of its proof: `Prop5Decay` (borrowed), `lem:propT`
(`EKPropT`, to be bridged to `zdistInf`), the Ward identities (`KLK_ward`, `eq_Ward`). -/
def STNewKLKAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D ℓ : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOp sz n E u σ (STLKM sz n E u H σ) a‖ ≤
            C / (1 - u) * STJhatM sz n E D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKM sz n E u H σ a‖ ≤
            C / (1 - u) * (STJhatM sz n E D ℓ u H +
              STJhatM sz n E D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- **`lem:newKLK`**, the pin: `∃ C, δ₀` with `STNewKLKAt`. -/
def STNewKLK (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKAt d κ 𝔡 C δ₀

/-- **The pointwise contraction inequality of Step 2** (`ygdhmsgq0`, `(eq_sym_loop_bound)`,
`3_5:751–761`; the paper calls it "a pointwise version of the more general contraction inequality
`(u2jzooi-2)`", which is the merged Step 3 pin `STContract` of T2049, `Induction/Step34Pins.lean:307`;
the two statements differ (label-dependent maxima here, maxima over all labels there), hence the
name `STContractPt`), deterministic:
for every Hermitian `H` on the fine lattice, `z` with `Im z > 0`, signs `σ`, labels `a, b`, a set
`𝒜` of blocks and `M ≥ 0` with `(𝓛^{(4)}_{(σ₁,-σ₁,σ₁,-σ₁),(c',b,c',b)})^{1/2} ≤ M` on `𝒜`:
`Σ_{c'∈𝒜} Σ_{|c-c'|≤1} 𝓛^{(6)}_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)} ≤ 3^d/(W^d Im z) · M ·
max_{σ'} |𝓛^{(3)}_{(σ',σ₂,-σ₂),(a,b,a)}|` (the constant `3^d` is the neighbour count; the numeric check
of the report gives the ratio `0.39` at `d = 3`, `W = 2`, `L = 4`).  Proof: Cauchy–Schwarz and
Ward's identity (`G(+) G(-) = (G(+) - G(-))/(2 i Im z)`). -/
def STContractPt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ),
    H.IsHermitian → 0 < z.im → ∀ (σ : Fin 2 → Bool) (a b : Zd d L) (𝒜 : Finset (Zd d L)) (M : ℝ),
      0 ≤ M →
      (∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ) ≤ M) →
        ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ ≤
          3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * M *
            max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
              ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖

/-- **`lem:LWterm`** (light-weight estimate, `B`-bound; `3_5:385–404`; LW gate, proved there: **owed**),
a statement about the model alone at one time sequence `t ≤ t₀`: under `(initialGT2)`, `(eq:LW_assm)`
and the profile conditions `(eq:Psi)`, `𝓔^{G̃,(2)}_{t,σ,(a,b)} ≺ η_t^{-1} Ψ_t(0) Ψ_t²(|a-b|)`
for all `σ ∈ {+,-}²`, `a, b`. -/
def STLWB (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2 sz (STflowE z) t ε₀ (fun n => Ψ n 0) → STLWassm sz (STflowE z) t Ψ →
            Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEGt sz n (STflowE z n) (t n) p.1 p.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2 0 - p.2 1))) ^ 2)

/-- **`lem: EWGn2_N`** (light-weight estimate, `𝒯`-bound; `3_5:406–415`; LW gate: **owed**): under
`(initialGT2)` (`W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`) and `(eq:LW_assm_exp)` at a scale
`0 ≤ ℓ ≤ (log W)^{10} ℓ_t`, for every large `D`:
`𝓔^{G̃,(2)}_{t,σ,(a,b)} ≺ η_t^{-1} (W^{-d} B_{t,0})^{1/2} W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|)`. -/
def STLWT (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEGt sz n (STflowE z n) (t n) p.1 p.2 ω‖)
                (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                  STprof sz n (t n) D (ℓ n) (p.2 0) (p.2 1))

/-- **`lem: EMn2_N`, first estimate** `(eq:MG_conclusion)` (`3_5:427–432`, proof `3_5:800–825` with
the contraction inequality; ST-2): the same premises as `STLWB`; for each cut `k ∈ {1,2}`
`(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a} ≺ η_t^{-1} Ψ_t(0) Ψ_t⁴(|a-b|)`. -/
def STEMn2Poly (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℕ → ℝ, STPsiClass sz ε₀ Ψ →
          STInitialGT2 sz (STflowE z) t ε₀ (fun n => Ψ n 0) → STLWassm sz (STflowE z) t Ψ →
            Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
              (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
              (fun n p _ => (etaT (STflowE z n) (t n))⁻¹ * Ψ n 0 *
                (Ψ n (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1))) ^ 4)

/-- **`lem: EMn2_N`, third estimate** `(eq:MG_conclusion3)` (`3_5:437–440`, proof `3_5:829–888`):
the same premises as `STLWT`; for each cut `k` and every large `D`,
`(𝓔⊗𝓔)^{M,(2;k)}_{t,σ,a,a} ≺ η_t^{-1} [(W^{-d}B_{t,0})^{1/2} + (Ĵ^ℓ_{t,D})³] (W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|))²`
with the **random** control `Ĵ^ℓ_{t,D}` (`STJhat`). -/
def STEMn2Exp (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
          (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
            Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
          STInitialGT2 sz (STflowE z) t ε₀ Ψ →
          ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
              ellT (sz.L n) (sz.lam n) (t n)) →
            (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
            ∀ D : ℝ, 0 < D →
              Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                (fun n p ω => ‖STEEk sz n (STflowE z n) (t n) p.1 p.2.1 p.2.2 ω‖)
                (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                  ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                    (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                  (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2)

end RBM.Gauss.Sizes
/-! ### 2.3 The grid representation `Sol_CalL` and the martingale estimate `lem:DIfREP` (path layer)

The walk is the grid Gaussian walk `pathH` (DECISIONS §7); `gridStep`, `gridTime` are merged.  The
loop observable of the walk at grid index `k` is `A_k = (𝓛-𝒦)^{(2)}_{u_k,σ,a}(H_k)`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section PathLayer

variable {d : ℕ} (sz : Sizes d)

/-- `A_k = (𝓛-𝒦)^{(2)}_{u_k,σ,a}(H_k)`: the observable of the grid walk at grid index `k`. -/
def STgA (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n))
    (k : ℕ) (ω : PathΩ sz) : ℂ :=
  STLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) σ a

/-- The drift of `(𝓛-𝒦)^{(2)}` (`(LK_simple)`, `3_5:360–362`): `Θ^{(2)}_{u,σ} ∘ (𝓛-𝒦)^{(2)} +
𝓔^{(𝓛-𝓚)×(𝓛-𝓚)} + 𝓔^{G̃}`, at the grid state. -/
def STgDrift (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  STthetaOp sz n E (gridTime s t K n k)  σ
      (STLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) σ) a +
    STELKLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) σ a +
    STEGtM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) σ a

/-- **`Sol_CalL` (`3_5:134–148`, `(int_K-L_ST)`) and `lem:DIfREP` (`3_5:218–228`) in grid form**
(`n = 2`; `d = 2` sources: `Path/{OneStep, LoopStep, DriftAlgebra, Expansion, StepDecomp, QVIdentity,
DuhamelTail}`, `Induction/{LoopGenN, GridDriftN, StepDecompN, AzumaProxyN, GridAssemblyN}`): for every
`D` there is a grid exponent `C_K` such that on every grid `K_n ≥ N^{C_K}` from `s` to `t ≤ t₀`
the observable splits as `A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k + Mart_k` pathP-a.e. for all
`k ≤ K` with (i) `|Rem_k| ≤ N^{C₀} Δ^{1/2}` (the one-step error `N^{C₀} Δ^{3/2}` summed over `K`
steps) and (ii) the martingale part obeys the random-proxy tail bound (the grid form of the
Burkholder–Davis–Gundy step `(aaswtghh)` + Markov, via Azuma–Hoeffding with Doob, DECISIONS §7):
`|Mart_k| ≤ N^{ε'} (Σ_{j<k} Δ |(𝓔⊗𝓔)^{M,(2)}_{u_j}(H_j)| + N^{-D})^{1/2}` for all `k ≤ K`, with
probability `≥ 1 - N^{-D}`.  The constant `C₀` depends on `d` only; `Δ = (t-s)/K`.  **owed** (ST-2). -/
def STGridMartAt (d : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ n i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                STgA sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgA sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDrift sz s t K n (STflowE z n) i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i, ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i,
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STEEM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                          i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- **`Sol_CalL` + `lem:DIfREP`**, the pin: `∃ C₀` with `STGridMartAt`. -/
def STGridMart (d : ℕ) : Prop := ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridMartAt d C₀

/-! ### 2.4 The stopping time `(eq:def2_stopping)` on the grid -/

/-- **`T` of `(eq:def2_stopping)`** (`3_5:533`) on the grid `u_j = s + jΔ`: the first grid index
`j ≤ K` at which `Ĵ^{K_{u_j}}_{u_j,D}(H_j) ≥ (W^{-d} B_{u_j,0})^{1/6}` (`K` if there is none), for the
scale family `ℓ n u` (the paper's `K_u`); `τ = t ∧ T` is the paper's stopping time. -/
def STstopIdx (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ → ℝ) (n : ℕ) :
    PathΩ sz → ℕ :=
  firstHit (fun j (ω : PathΩ sz) =>
    STJhatM sz n (E n) D (ℓ n (gridTime s t K n j)) (gridTime s t K n j) (pathH sz s t K n j ω) /
      (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n)

/-- The stopping index `T` is a stopping time of the coordinate filtration of the grid walk. -/
theorem STstopIdx_isStoppingTime (s t : ℕ → ℝ) (K : ℕ → ℕ) (E : ℕ → ℝ) (D : ℝ) (ℓ : ℕ → ℝ → ℝ)
    (n : ℕ) :
    MeasureTheory.IsStoppingTime (filt sz) (fun ω => (STstopIdx sz s t K E D ℓ n ω : ℕ)) :=
  isStoppingTime_firstHit_grid sz s t K n
    (F := fun (j : ℕ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) =>
      STJhatM sz n (E n) D (ℓ n (gridTime s t K n j)) (gridTime s t K n j) H /
        (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ))
    (fun j => (STJhatM_measurable sz n (E n) (gridTime s t K n j) D _).div_const _) 1 (K n)

end PathLayer

/-! ### 2.5 `𝒦^{(2)}` decay, the net lift, and the combined pin -/

/-- **`(eq:simpleboundK)`** (`3_5:518`) = `(eq:kn2sol_decay)` (`3_5:457`), deterministic: `|𝒦^{(2)}_{u,σ,a}| ≤
C W^{-d} 𝒯̃^{L}_{u,D}(|a₁-a₂|)` for every `D ≥ 0` (from `(Kn2sol)` = merged `KLK_two` and
`prop:ThfadC`, `Prop5Decay` borrowed; the `ℓ¹` versus `L^∞` distance costs only the constant `c_d`
in the exponent, absorbed by the square root of `𝒯`). -/
def STK2decay (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
      0 ≤ u → u < 1 → 0 ≤ D → ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STKloop sz n E u σ a‖ ≤ C * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

section Lift

variable {d : ℕ}

/-- **The net lift of Step 2** (the standard `N^{-C}`-net and perturbation argument, `1_2:1400`;
RBM2D `Path/NetLift.lean`, `Step2NetLift`, `Step2LocalNetLift`): the per-time conclusions give the
uniform ones, for every `C_d`. -/
def STNetLift2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ Cd : ℝ, STStep2LocalPT sz (STflowE z) s t → STStep2AvgPT sz (STflowE z) s t →
          STStep2DecayPT sz Cd (STflowE z) s t →
            STStep2Local sz (STflowE z) s t ∧ STStep2Avg sz (STflowE z) s t ∧
              STStep2Decay sz Cd (STflowE z) s t

/-- **Step 2 of `lem:main_ind`** (`1_2:1340–1357`, `(Gt_bound_flow)`, `(Gt_avgbound_flow)`,
`(Eq:Gdecay_w)`) at sequence level.  Constants first: `κ, ε, 𝔡`, then `C_d` (independent of `𝔠_d`),
then `𝔠_d ∈ (0, 10^{-2}]` (depending on `d, κ, ε, 𝔡` and `C_d`), then the bandwidth exponent `𝔠`, the
sizes and `z`.  Premises: `(a)` and `(b)` (first part) at `s`, `(con_st_ind)`, and Step 1's conclusions
`(lRB1)`, `(Gtmwc)` uniformly in `u ∈ [s,t]` (`STStep1Loop`, `STStep1Weak`); `(c)`, `(d)` and the
strong form of `(b)` are not used by Step 2.  The conclusion is the merged bundle `STStep2Concl`
(`Induction/Step34Pins.lean:221`: `STLocalEntryU ∧ STAvgU ∧ STGdecayW`); `STStep2Local ∧ STStep2Avg ∧
STStep2Decay` below are the three parts in the single-charge form of the probe, which ST2-04 proves
and turns into `STStep2Concl` (`STStep2Avg` ≠ `STAvgU` as a statement: paper-delta T2039g). -/
def STStep2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep1Weak sz (STflowE z) s t →
            STStep2Concl sz (STflowE z) s t Cd

end Lift

end RBM.Gauss.Sizes

/-! ## 3. Definitions the pins mention: the scale family, the per-time `(eq:L2_decay)`, the list-loop matrix functionals -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- **Admissible scale family** (`(kwr3juw)`, `(eq:monotone_Ku)`, `3_5:521–527`): `K_u ≥ 0`, `K_u ≤ L`
(the profile only sees distances `≤ L`), `K_u ≤ (log W)^{10} ℓ_u` (the range of `lem: EWGn2_N`),
eventually in `n`, and `u ↦ 𝒯_u(K_u)` is non-decreasing on `[s_n, t_n]`, eventually in `n`. -/
def STScaleOk (s t : ℕ → ℝ) (Kf : ℕ → ℝ → ℝ) : Prop :=
  (∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧ Kf n u ≤ ((sz.L n : ℕ) : ℝ) ∧
    Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u) ∧
  (∀ᶠ n in atTop, ∀ u v, s n ≤ u → u ≤ v → v ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ tailT d (sz.L n) (sz.lam n) v (Kf n v))

/-- **The scale iteration `(eq:def_ell1)`**: `Kseq m n u` is `K_u` after `m` steps: `K_0 = 0`; every
level is admissible (`STScaleOk`); `0 ≤ K_m ≤ K_{m+1}` and `𝒯_u(K_{m+1}) ≥ (W^{-d}B_{u,0})^{1/6} 𝒯_u(K_m)`
(equality unless the solution of `(eq:def_ell1)` exceeds `L`, where the family is cut at `L`); after
`M(D)` steps either `𝒯_u(K_M) ≤ W^{-D}` or `K_M ≥ L` (`𝒯̃^{K} ≍ 𝒯̃^{L}`), for all `u ∈ [s_n,t_n]`
eventually in `n` (`3_5:577`); every clause but `K_0 = 0` is required only eventually in `n`. -/
def STScaleAdm (s t : ℕ → ℝ) (Kseq : ℕ → ℕ → ℝ → ℝ) : Prop :=
  (∀ n u, Kseq 0 n u = 0) ∧ (∀ m, STScaleOk sz s t (Kseq m)) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kseq m n u ∧ Kseq m n u ≤ Kseq (m + 1) n u) ∧
  (∀ m, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    (sz.Bctl n u) ^ (1 / 6 : ℝ) * tailT d (sz.L n) (sz.lam n) u (Kseq m n u) ≤
      tailT d (sz.L n) (sz.lam n) u (Kseq (m + 1) n u)) ∧
  (∀ D : ℝ, 0 < D → ∃ M : ℕ, ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
    tailT d (sz.L n) (sz.lam n) u (Kseq M n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) ∨
      ((sz.L n : ℕ) : ℝ) ≤ Kseq M n u)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **The scale family** `K_u^{(m)}` of `(eq:def_ell1)` (`3_5:571–577`; deterministic, ST-2, **owed**):
for every flow and every `0 ≤ s_n ≤ t_n ≤ lemT(z_n)` there is an admissible family (`STScaleAdm`):
`K^{(0)} = 0`, `𝒯_u(K^{(m+1)}_u) = (W^{-d}B_{u,0})^{1/6} 𝒯_u(K^{(m)}_u)` (intermediate value theorem on the
continuous decreasing `r ↦ 𝒯_u(r)`, cut at `L`), `u ↦ 𝒯_u(K_u)` non-decreasing, and the floor
`𝒯_u(K_M) ≤ W^{-D}` after `M(D) ≍ (D + d)/c` steps (`b_u ≤ N^{-c}`). -/
def STScaleExists (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz s t Kseq

/-- **`(eq:opt_L2)`** (`3_5:470`, proof `3_5:466–512`; ST-2, **owed**): the maximal bound
`max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ W^{-d} B_{u,0}` uniformly in `u ∈ [s,t]` (per time), from the
premises of Step 2 with `𝔠_d` small depending on the constant of `lem:newKLK`; its proof is the
linear Grönwall argument at `ℓ = 0` (`STNewKLK`, `STLWB`, `STEMn2Poly`, `STGridMart`, the bound
`(lokis2)` from `STStep1Loop`).  It is the base of the iteration over scales. -/
def STOptL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep1Weak sz (STflowE z) s t →
          PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
            (fun n p ω => ‖Lloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2 ω -
              STKloop sz n (STflowE z n) (p.1 : ℝ) p.2.1 p.2.2‖)
            (fun n p _ => sz.Bctl n (p.1 : ℝ))

section L2

variable {d : ℕ} (sz : Sizes d)

/-- **`(eq:L2_decay)`** (`3_5:460`) per time: `𝓛^{(2)}_{u,(-,+),(a₁,a₂)} ≺ W^{-d} B_{u,|a₁-a₂|}`. -/
def STL2decayPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × (Fin 2 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) ![false, true] p.2 ω‖)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2 0 - p.2 1)))

end L2

/-- **The closing paragraph of Step 2** (`3_5:455–465`; ST-2, **owed**, uses the merged ST-1 pin
`STGbEXP`): `(eq:L2_decay)` and the weak law `(Gtmwc)` verify `(initialGT2)` at every time and
`lem_GbEXP` gives `(Gt_bound_flow)` (`(GiiGEX)`, `(GijGEX)` with the neighbour sums of
`STgexRHS`) and `(Gt_avgbound_flow)` (`(GavLGEX)`), per time. -/
def STLocalAvgOfL2 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STStep1Weak sz (STflowE z) s t → STL2decayPT sz (STflowE z) s t →
          STStep2LocalPT sz (STflowE z) s t ∧ STStep2AvgPT sz (STflowE z) s t

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section MatrixN

variable {d : ℕ} (sz : Sizes d)

/-- `𝓛_{τ,I}` of a list-based loop index for an arbitrary fine matrix `H` (the grid state): the model-level
`STLI` is the case `H = seqHflow sz n τ ω` (`STLIM_seqHflow`, `rfl`). -/
def STLIM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E τ) I

/-- `(𝓛 - 𝒦)_{τ,I}` of a fine matrix `H`. -/
def STLKIM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  STLIM sz n E τ H I - KLK d (sz.L n) (sz.lam n) (sz.W n) E τ I

/-- `[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(n)}_{τ,I}` of a fine matrix `H` (`STksimLK` with `H` for `ω`). -/
def STksimLKM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      ((if (I.cutGlueR k l' b).length = l then
          STLKIM sz n E τ H (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
            KLK d (sz.L n) (sz.lam n) (sz.W n) E τ (I.cutGlueR k l' b)
        else 0) +
       (if (I.cutGlueL k l' a).length = l then
          KLK d (sz.L n) (sz.lam n) (sz.W n) E τ (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
            STLKIM sz n E τ H (I.cutGlueR k l' b)
        else 0))

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(n)}_{τ,I}` of a fine matrix `H` (`STelklk` with `H` for `ω`). -/
def STelklkM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      STLKIM sz n E τ H (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
        STLKIM sz n E τ H (I.cutGlueR k l' b)

/-- `tr(G̃_τ(σ) E_a)` of a fine matrix `H` (`STavgErr` with `H` for `ω`). -/
def STavgErrM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Bool) (a : Zd d (sz.L n)) : ℂ :=
  STLIM sz n E τ H ⟨[σ], [a]⟩ - mSigma E σ

/-- `ℰ^{G̃,(n)}_{τ,I}` of a fine matrix `H` (`STegt` with `H` for `ω`). -/
def STegtM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
    STavgErrM sz n E τ H (I.σ.getD (k - 1) false) a * SB d (sz.L n) (sz.lam n) a b *
      STLIM sz n E τ H (I.cutGlue k b)

/-- `(ℰ⊗ℰ)^{M,(m)}_{τ,σ,a,a'}` of a fine matrix `H` (`STee` with `H` for `ω`). -/
def STeeM (n : ℕ) (E τ : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
    SB d (sz.L n) (sz.lam n) b b' *
      STLIM sz n E τ H (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

end MatrixN

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section GridN

variable {d : ℕ} (sz : Sizes d)


/-- `A_k = (𝓛-𝒦)^{(m)}_{u_k,σ,a}(H_k)`: the observable of the grid walk at grid index `k`, loop length `m`. -/
def STgAN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  STLKIM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- **The drift of `(𝓛-𝒦)^{(m)}`** (`(eq_L-Keee)`, `3_5:75-100`) at the grid state:
`Θ^{(m)}_{u,σ} ∘ (𝓛-𝒦)^{(m)} + Σ_{l_K=3}^{m} [𝒦^{(l_K)} ∼ (𝓛-𝒦)]^{(m)} + ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(m)} + ℰ^{G̃,(m)}`
(`Θ^{(m)}` = the merged `ThetaN`, `DefTHUST`, `m(σ_i)` the charge values). -/
def STgDriftN (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E : ℝ) {m : ℕ} (σ : Fin m → Bool)
    (a : Fin m → Zd d (sz.L n)) (k : ℕ) (ω : PathΩ sz) : ℂ :=
  ThetaN d (sz.L n) (sz.lam n) (fun i => mSigma E (σ i)) (gridTime s t K n k)
      (fun a' => STLKIM sz n E (gridTime s t K n k) (pathH sz s t K n k ω)
        (KLloopOf d (sz.L n) σ a')) a +
    ∑ l ∈ Finset.Icc 3 m, STksimLKM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) l
      (KLloopOf d (sz.L n) σ a) +
    STelklkM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) (KLloopOf d (sz.L n) σ a) +
    STegtM sz n E (gridTime s t K n k) (pathH sz s t K n k ω) (KLloopOf d (sz.L n) σ a)

/-- **The weighted quadratic-variation loop** `((𝒰_{v,w,σ} ⊗ 𝒰_{v,w,σ̄}) ∘ (ℰ⊗ℰ)^{M,(m)}_{v,σ})_{a,a}` of
`(alu9_STime)` (`3_5:232-240`, `(def_Ustz)`) for a fine matrix `H`: the merged kernels `uKer` with the
charge values `m(σ_i)` and `m(-σ_i) = conj m(σ_i)`, `M^{(σ_i,σ_{i+1})} = m(σ_i)m(σ_{i+1})` (`cycProd`). -/
def STeeUM (n : ℕ) (E v w : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    {m : ℕ} (σ : Fin m → Bool) (a : Fin m → Zd d (sz.L n)) : ℂ :=
  ∑ b : Fin m → Zd d (sz.L n), ∑ b' : Fin m → Zd d (sz.L n),
    (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (σ i)) i) v w (a i) (b i)) *
      (∏ i, uKer d (sz.L n) (sz.lam n) (cycProd (fun i => mSigma E (!σ i)) i) v w (a i) (b' i)) *
        STeeM sz n E v H σ b b'

/-- **`Sol_CalL` and `lem:DIfREP` on the grid, every loop length `m`** (`(int_K-L_ST)` `3_5:134`, `(aaswtghh)`
and `(alu9_STime)` `3_5:218-240`; DECISIONS §7: the Burkholder-Davis-Gundy step is replaced by the
Azuma-Hoeffding step on the grid with the random proxy).  For every flow, every `D`, there is a grid
exponent `C_K` such that on every grid `K_n ≥ N^{C_K}` from `s` to `t ≤ t₀` the observable splits
`pathP`-a.e., for all `k ≤ K` simultaneously (hence at every stopping index), as
`A_k = A_0 + Δ Σ_{j<k} Drift_j + Rem_k + Mart_k` with (i) `|Rem_k| ≤ N^{C₀} Δ^{1/2}` (`C₀ = C₀(d,m)`),
(ii) the martingale tail `|Mart_k| ≤ N^{ε'} (Σ_{j<k} Δ |(ℰ⊗ℰ)^{M,(m)}_{u_j}(H_j)| + N^{-D})^{1/2}` for all
`k ≤ K`, with probability `≥ 1 - N^{-D}`, and (iii) the weighted tail of `(alu9_STime)` for the **same**
`Mart`: `|Σ_{j<k} (𝒰_{u_j,u_k,σ} ∘ ΔMart_j)_a| ≤ N^{ε'} (Σ_{j<k} Δ |((𝒰⊗𝒰̄) ∘ (ℰ⊗ℰ)^{M,(m)}_{u_j})_{a,a}| +
N^{-D})^{1/2}`, for all `k ≤ K`, with probability `≥ 1 - N^{-D}` (the Duhamel form `(int_K-LcalE)` at the
index `k` follows from the decomposition by the algebraic telescope of `Ugen`, RBM2D
`GridDuhamelN_Ugen_duhamel_telescope`, and the remainder `N^{C}Δ^{1/2}`).  `m = 2` is the pin
`STGridMartAt` (`ST_gridMart_of_repN`).  **owed** (ST2-12, ST2-13, ST2-27, ST2-34, ST2-35). -/
def STGridRepNAt (d m : ℕ) (C₀ : ℝ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ D : ℝ, 0 < D → ∃ CK : ℝ, 0 ≤ CK ∧
          ∀ K : ℕ → ℕ, (∀ n, K n ≠ 0) → (∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ K n) →
            ∃ Mart Rem : ∀ n, ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) → ℕ → PathΩ sz → ℂ,
              (∀ (n : ℕ) (i : (Fin m → Bool) × (Fin m → Zd d (sz.L n))), ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                STgAN sz s t K n (STflowE z n) i.1 i.2 k ω =
                  STgAN sz s t K n (STflowE z n) i.1 i.2 0 ω +
                    ((gridStep s t K n : ℝ) : ℂ) *
                      ∑ j ∈ Finset.range k, STgDriftN sz s t K n (STflowE z n) i.1 i.2 j ω +
                    Rem n i k ω + Mart n i k ω) ∧
              (∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)), ∀ᵐ ω ∂(pathP sz), ∀ k, k ≤ K n →
                ‖Rem n i k ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s t K n)) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeM sz n (STflowE z n) (gridTime s t K n j) (pathH sz s t K n j ω)
                          i.1 i.2 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^ (1 / 2 : ℝ) <
                    ‖Mart n i k ω‖} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) ∧
              (∀ ε' : ℝ, 0 < ε' → ∀ᶠ n in atTop, ∀ i : (Fin m → Bool) × (Fin m → Zd d (sz.L n)),
                pathP sz {ω | ∃ k, k ≤ K n ∧
                  ((sz.size n : ℕ) : ℝ) ^ ε' *
                      (∑ j ∈ Finset.range k, gridStep s t K n *
                        ‖STeeUM sz n (STflowE z n) (gridTime s t K n j) (gridTime s t K n k)
                          (pathH sz s t K n j ω) i.1 i.2‖ + ((sz.size n : ℕ) : ℝ) ^ (-D)) ^
                          (1 / 2 : ℝ) <
                    ‖∑ j ∈ Finset.range k,
                      UN d (sz.L n) (sz.lam n) (fun i' => mSigma (STflowE z n) (i.1 i'))
                        (gridTime s t K n j) (gridTime s t K n k)
                        (fun b => Mart n (i.1, b) (j + 1) ω - Mart n (i.1, b) j ω) i.2‖} ≤
                  ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)))

/-- **`Sol_CalL` + `lem:DIfREP`, every loop length**, the pin: for every `m ≥ 2` there is `C₀` with
`STGridRepNAt`. -/
def STGridRepN (d : ℕ) : Prop := ∀ m : ℕ, 2 ≤ m → ∃ C₀ : ℝ, 0 ≤ C₀ ∧ STGridRepNAt d m C₀

end GridN

end RBM.Gauss.Sizes



/-! ## 4. Compiled nonempty instances at `d = 3` (probe §13, the part that uses only this file)

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` and the flow block of
`Induction/Defs.lean` (`RBM.Gauss.InductionDefsInst`: `z0`, `flow_z0`, `sInst ≡ 0`, `tInst ≡ 1/16`,
`conStInd_inst`, `sz1`, `flow_z1`): `d = 3`, `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `z_n = 1/2 + i N_n^{-4/5}`.
Every deterministic hypothesis is discharged; what stays a hypothesis of an instance is the pin
itself (`h : STNewKLK 3`, ...) or a stochastic premise of the pin (`STLK`, `STDecay`, `STStep1Loop`,
`STStep1Weak`, `STInitialGT2`, `STLWassm`, `STLWassmExp`, the per-time statements of `STNetLift2`).
The instances of the probe that use theorems of sections 3-12 (`inst_Bdata`, `inst_skeleton*`,
`inst_step2_concl`, `inst_scaleAdm_szX`) move with those theorems (ST2-02 to ST2-04). -/

namespace RBM.Gauss.Step2DefsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Path Filter

/-- **Step 2 of `lem:main_ind`, instantiated** (`STStep2`, concluding the merged bundle
`STStep2Concl`): the constants `C_d`, `𝔠_d`, then the deterministic data `(sz0, z0, s ≡ 0, t ≡ 1/16)`
with `(con_st_ind)`; the premises `STLK`, `STDecay` at `s` and Step 1's conclusions stay hypotheses. -/
theorem inst_step2 (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz0 (STflowE z0) sInst → STDecay sz0 (STflowE z0) sInst →
        STStep1Loop sz0 (STflowE z0) sInst tInst → STStep1Weak sz0 (STflowE z0) sInst tInst →
        STStep2Concl sz0 (STflowE z0) sInst tInst Cd) := by
  obtain ⟨Cd, hCd, 𝔠d, h0, h1, hall⟩ :=
    h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cd, hCd, 𝔠d, h0, h1, fun hLK hDec hS1L hS1W => ?_⟩
  exact hall (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hLK hDec
    (conStInd_inst h0) hS1L hS1W

/-- **Step 2 at the extreme coupling** `ilambda = W^{-d/2+𝔡}` (lower end of `(eq:WO)`). -/
theorem inst_step2_lowg (h : STStep2 3) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STLK sz1 (STflowE z0) sInst → STDecay sz1 (STflowE z0) sInst →
        STStep1Loop sz1 (STflowE z0) sInst tInst → STStep1Weak sz1 (STflowE z0) sInst tInst →
        STStep2Concl sz1 (STflowE z0) sInst tInst Cd) := by
  obtain ⟨Cd, hCd, 𝔠d, h0, h1, hall⟩ :=
    h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨Cd, hCd, 𝔠d, h0, h1, fun hLK hDec hS1L hS1W => ?_⟩
  exact hall (1 / 6) sz1 z0 flow_z1 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hLK hDec
    (conStInd_gen sz1 W_tendsto_sz1 h0) hS1L hS1W

/-- At `H = 0`, `u = 0` the resolvent is `m(E) I`: `G_0 = M` exactly (`|E| < 2`); this is the
nondegenerate witness for the weak-law premise of `lem:newKLK`. -/
theorem STGMM_zero {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2)
    (x y : Idx d (sz.L n) (sz.W n)) :
    STGMM sz n E 0 (0 : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) x y = 0 := by
  have hm := mE_mul hE.le
  have hne : -((E : ℂ) + mE E) ≠ 0 := by
    intro h0
    have h1 : (E : ℂ) + mE E = 0 := neg_eq_zero.mp h0
    have : mE E * (mE E + E) = 0 := by rw [add_comm, h1, mul_zero]
    rw [this] at hm; norm_num at hm
  have hinv : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hz : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  unfold STGMM Gres
  rw [hz]
  simp only [if_true]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one hne, hinv]
  by_cases hxy : x = y
  · subst hxy; simp
  · simp [hxy, Matrix.one_apply_ne hxy]

/-- **`lem:newKLK`, instantiated** at `n = 0`, `E = 1/2`, `u = 0`, `D = 1`, `ℓ = 0` and the matrix
`H = 0` (Hermitian, `‖G_0 - M‖_max = 0 ≤ δ₀`): the constants `C, δ₀` of the pin, then the two bounds
of `(juwo2=klk)`, `(juwo=Lklk)`. -/
theorem inst_newKLK (h : STNewKLK 3) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STthetaOp sz0 0 (1 / 2) 0 σ
          (STLKM sz0 0 (1 / 2) 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ) a‖ ≤
          C / (1 - 0) * STJhatM sz0 0 (1 / 2) 1 0 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) *
            STprof sz0 0 0 1 0 (a 0) (a 1) ∧
        ‖STELKLKM sz0 0 (1 / 2) 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) σ a‖ ≤
          C / (1 - 0) * (STJhatM sz0 0 (1 / 2) 1 0 0
            (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) +
            STJhatM sz0 0 (1 / 2) 1 0 0
              (0 : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ) ^ 2 *
              (if 1 ≤ (0 : ℝ) then 1 else 0)) * STprof sz0 0 0 1 0 (a 0) (a 1) := by
  obtain ⟨C, δ₀, hC, hδ, hAt⟩ := h (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  refine ⟨C, δ₀, hC, hδ, fun σ a => ?_⟩
  exact hAt sz0 0 (1 / 2) 0 1 0 hlam hlam' (by norm_num [abs_of_pos]) le_rfl one_pos
    zero_le_one le_rfl (by simp) 0 Matrix.isHermitian_zero
    (fun x y => by rw [STGMM_zero sz0 0 (by norm_num [abs_of_pos]) x y]; simpa using hδ.le) σ a

/-- **The contraction inequality, instantiated** at `d = 3`, `L = 3`, `W = 2`, `H = 0` (Hermitian),
`z = i` (`Im z = 1`), `σ = (+,-)`, `a = b = 0`, `𝒜 = {0}` and `M` the exact value
`(𝓛^{(4)})^{1/2}`. -/
theorem inst_contractPt (h : STContractPt 3) :
    ∑ c' ∈ ({0} : Finset (Zd 3 3)), ∑ c ∈ Finset.univ.filter
        (fun c : Zd 3 3 => zdistInf 3 3 (c - c') ≤ 1),
      ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
        ![![true, false] 0, ![true, false] 1, ![true, false] 0, !(![true, false] 0),
          !(![true, false] 1), !(![true, false] 0)] ![0, 0, c', 0, 0, c]‖ ≤
      3 ^ 3 / (((2 : ℕ) : ℝ) ^ 3 * Complex.I.im) *
        (‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
          ![![true, false] 0, !(![true, false] 0), ![true, false] 0, !(![true, false] 0)]
          ![(0 : Zd 3 3), 0, 0, 0]‖ ^ (1 / 2 : ℝ)) *
        max ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
            ![true, ![true, false] 1, !(![true, false] 1)] ![0, 0, 0]‖
          ‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
            ![false, ![true, false] 1, !(![true, false] 1)] ![0, 0, 0]‖ := by
  have := h 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I Matrix.isHermitian_zero
    (by simp) ![true, false] 0 0 {0}
    (‖loopFine 3 3 2 (0 : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ) Complex.I
      ![![true, false] 0, !(![true, false] 0), ![true, false] 0, !(![true, false] 0)]
      ![(0 : Zd 3 3), 0, 0, 0]‖ ^ (1 / 2 : ℝ)) (Real.rpow_nonneg (norm_nonneg _) _)
    (by intro c' hc'; simp at hc'; subst hc'; exact le_rfl)
  convert this using 3

/-- The deterministic control profile `Ψ_n(r) = W_n^{-1}` (constant in `r`). -/
def Ψ0 (n : ℕ) (_ : ℕ) : ℝ := ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))

theorem W_ge_one (n : ℕ) : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n

/-- `Ψ_n(r) = W_n^{-1}` is in the class `STPsiClass` of `(eq:Psi)` for `ε₀ = 1/20`: all four
conditions are checked (`W^{-3/2} ≤ Ψ ≤ W^{-1/20}`, monotone, `Ψ(0) ≍ Ψ(r)`, ratio `1 ≤ 2 (r₂/r₁)²`). -/
theorem Ψ0_class : STPsiClass sz0 (1 / 20) Ψ0 := by
  have hpos : ∀ n, 0 < ((sz0.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz0.W_pos n
  refine ⟨fun n r => ⟨?_, ?_⟩, fun n r r' _ => le_rfl, fun C => ⟨1, one_pos, ?_⟩, ⟨2, 2, ?_⟩⟩
  · exact Real.rpow_pos_of_pos (hpos n) _
  · exact Real.rpow_le_rpow_of_exponent_le (W_ge_one n) (by norm_num)
  · refine Eventually.of_forall fun n => ⟨?_, fun r _ => (one_mul _).le⟩
    rw [inv_one, one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (W_ge_one n) (by norm_num)
  · refine ⟨by norm_num, by norm_num, fun n r₁ r₂ h1 h12 => ?_⟩
    have hr1 : (0 : ℝ) < r₁ := by exact_mod_cast h1
    have hr : (1 : ℝ) ≤ (r₂ : ℝ) / r₁ := by
      rw [le_div_iff₀ hr1]; simpa using (by exact_mod_cast h12 : (r₁ : ℝ) ≤ r₂)
    have hΨ := Real.rpow_pos_of_pos (hpos n) (-(1 : ℝ))
    have : Ψ0 n r₁ / Ψ0 n r₂ = 1 := by simp [Ψ0, hΨ.ne']
    rw [this]
    have := Real.one_le_rpow hr (by norm_num : (0 : ℝ) ≤ 2)
    linarith

/-- **The light-weight `B`-bound `lem:LWterm`, instantiated** at `t ≡ 1/16 ≤ t₀`, `ε₀ = 1/20`,
`Ψ_n(r) = W_n^{-1}`: the class `(eq:Psi)` and every deterministic hypothesis are discharged; only
`(initialGT2)` and `(eq:LW_assm)` stay hypotheses. -/
theorem inst_LWB (h : STLWB 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEGt sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2 0 - p.2 1))) ^ 2) :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20) (by norm_num) Ψ0
    Ψ0_class hI hA

/-- **`lem: EMn2_N`, first estimate, instantiated** (same data as `inst_LWB`). -/
theorem inst_EMn2Poly (h : STEMn2Poly 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => Ψ0 n 0))
    (hA : STLWassm sz0 (STflowE z0) tInst Ψ0) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * Ψ0 n 0 *
        (Ψ0 n (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1))) ^ 4) :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20) (by norm_num) Ψ0
    Ψ0_class hI hA

theorem Ψ1_window : ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) ∧
    ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)) :=
  Eventually.of_forall fun n =>
    ⟨Real.rpow_le_rpow_of_exponent_le (W_ge_one n) (by norm_num),
      Real.rpow_le_rpow_of_exponent_le (W_ge_one n) (by norm_num)⟩

theorem ℓ0_range : ∀ᶠ n in atTop, (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 *
    ellT (sz0.L n) (sz0.lam n) (tInst n) :=
  Eventually.of_forall fun n => ⟨le_rfl, mul_nonneg (by positivity) ellT_nonneg⟩

/-- **`lem: EWGn2_N`, instantiated** at the scale `ℓ ≡ 0`, `Ψ_n = W_n^{-1}`, `W^{-3/2} ≤ Ψ ≤ W^{-1/20}`
and `ℓ ≤ (log W)^{10} ℓ_t` discharged; `(initialGT2)` and `(eq:LW_assm_exp)` (all `D`) stay hypotheses. -/
theorem inst_LWT (h : STLWT 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D → STLWassmExp sz0 (STflowE z0) tInst D (fun _ => 0)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEGt sz0 n (STflowE z0 n) (tInst n) p.1 p.2 ω‖)
      (fun n p _ => (etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        STprof sz0 n (tInst n) D 0 (p.2 0) (p.2 1)) :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20) (by norm_num)
    (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI (fun _ => 0) ℓ0_range hA D hD

/-- **`lem: EMn2_N`, third estimate, instantiated** (same data as `inst_LWT`). -/
theorem inst_EMn2Exp (h : STEMn2Exp 3)
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D → STLWassmExp sz0 (STflowE z0) tInst D (fun _ => 0)) (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p ω => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        ((sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) +
          (STJhat sz0 n (STflowE z0 n) D 0 (tInst n) ω) ^ 3) *
        (STprof sz0 n (tInst n) D 0 (p.2.2 0) (p.2.2 1)) ^ 2) :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20) (by norm_num)
    (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI (fun _ => 0) ℓ0_range hA D hD

/- **`Sol_CalL` + `lem:DIfREP`, instantiated** at `s ≡ 0`, `t ≡ 1/16`, `D = 1`: the grid-size
exponent `C_K` of the pin, the admissible grid `K_n = ⌈N^{C_K}⌉` (nonzero, `K_n ≥ N^{C_K}`), and the
decomposition `A_k = A_0 + Δ Σ Drift_j + Rem_k + Mart_k` a.e. for the grid walk. -/
example (h : STGridMart 3) :
    ∃ C₀ CK : ℝ, 0 ≤ C₀ ∧ 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      ∃ Mart Rem : ∀ n, ((Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
        ∀ n i, ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgA sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDrift sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := by
  obtain ⟨C₀, hC₀, hAt⟩ := h
  obtain ⟨CK, hCK, hK⟩ := hAt (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) 1 one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ ≠ 0 := fun n =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_size_sz0 n)) _)).ne'
  obtain ⟨Mart, Rem, hid, -, -⟩ := hK (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊) hK0
    (Eventually.of_forall fun n => Nat.le_ceil _)
  exact ⟨C₀, CK, hC₀, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊, hK0,
    Eventually.of_forall fun n => Nat.le_ceil _, Mart, Rem, hid⟩

/-- **The stopping time `(eq:def2_stopping)`, instantiated**: `T` is a stopping time of the
coordinate filtration of the grid walk (grid of `8` steps on `[0, 1/16]`, scale family `K_u ≡ 0`,
`D = 1`). -/
theorem inst_stop :
    MeasureTheory.IsStoppingTime (filt sz0)
      (fun ω => (STstopIdx sz0 sInst tInst (fun _ => 8) (STflowE z0) 1 (fun _ _ => 0) 0 ω : ℕ)) :=
  STstopIdx_isStoppingTime sz0 sInst tInst (fun _ => 8) (STflowE z0) 1 (fun _ _ => 0) 0

/-- **The deterministic `𝒦^{(2)}` decay, instantiated** at `n = 0`, `E = 1/2`, `u = 0`, `D = 1`. -/
theorem inst_K2decay (h : STK2decay 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd 3 (sz0.L 0)),
      ‖STKloop sz0 0 (1 / 2) 0 σ a‖ ≤
        C * STprof sz0 0 0 1 ((sz0.L 0 : ℕ) : ℝ) (a 0) (a 1) := by
  obtain ⟨C, hC, hall⟩ := h (by norm_num) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ ((1 : ℝ) / 10)⁻¹ := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  exact ⟨C, hC, fun σ a => hall sz0 0 (1 / 2) 0 1 hlam hlam' (by norm_num [abs_of_pos]) le_rfl
    one_pos zero_le_one σ a⟩

/- **The net lift of Step 2, instantiated**: the three per-time statements stay hypotheses, the
uniform ones follow for every `C_d`. -/
example (h : STNetLift2 3) (Cd : ℝ)
    (hL : STStep2LocalPT sz0 (STflowE z0) sInst tInst)
    (hA : STStep2AvgPT sz0 (STflowE z0) sInst tInst)
    (hD : STStep2DecayPT sz0 Cd (STflowE z0) sInst tInst) :
    STStep2Local sz0 (STflowE z0) sInst tInst ∧ STStep2Avg sz0 (STflowE z0) sInst tInst ∧
      STStep2Decay sz0 Cd (STflowE z0) sInst tInst :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    sInst tInst (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) Cd hL hA hD

/-- **The scale family, instantiated.** -/
theorem inst_scaleExists (h : STScaleExists 3) : ∃ Kseq : ℕ → ℕ → ℝ → ℝ, STScaleAdm sz0 sInst tInst Kseq :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    sInst tInst (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n)

/-- **`(eq:opt_L2)`, instantiated**: a constant `𝔠₀`; for every `0 < 𝔠_d ≤ 𝔠₀` the premises
`STLK`, Step 1 stay hypotheses and `(con_st_ind)` is discharged. -/
theorem inst_optL2 (h : STOptL2 3) :
    ∃ 𝔠₀ : ℝ, 0 < 𝔠₀ ∧ ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 𝔠₀ →
      (STLK sz0 (STflowE z0) sInst → STStep1Loop sz0 (STflowE z0) sInst tInst →
        STStep1Weak sz0 (STflowE z0) sInst tInst →
        PrecPT sz0 (U := fun n => TimeIcc sInst tInst n × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2 ω -
            STKloop sz0 n (STflowE z0 n) (p.1 : ℝ) p.2.1 p.2.2‖)
          (fun n p _ => sz0.Bctl n (p.1 : ℝ))) := by
  obtain ⟨𝔠₀, h0, hall⟩ := h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨𝔠₀, h0, fun 𝔠d h1 h2 hLK hS1L hS1W => ?_⟩
  exact hall 𝔠d h1 h2 (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hLK
    (conStInd_inst h1) hS1L hS1W

/- **The closing paragraph of Step 2, instantiated.** -/
example (h : STLocalAvgOfL2 3) :
    STStep1Weak sz0 (STflowE z0) sInst tInst → STL2decayPT sz0 (STflowE z0) sInst tInst →
      STStep2LocalPT sz0 (STflowE z0) sInst tInst ∧ STStep2AvgPT sz0 (STflowE z0) sInst tInst :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    sInst tInst (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n)

/-- **`Sol_CalL` + `lem:DIfREP` for every loop length, instantiated** at the loop length `m = 3`, `s ≡ 0`,
`t ≡ 1/16`, `D = 1`: the grid exponent `C_K`, the admissible grid `K_n = ⌈N^{C_K}⌉`, and the decomposition
`A_k = A_0 + Δ Σ Drift_j + Rem_k + Mart_k` a.e. for the grid walk, with the general-`n` drift
(`Θ^{(3)} ∘ (𝓛-𝒦) + [𝒦^{(3)} ∼ (𝓛-𝒦)] + ℰ^{(𝓛-𝒦)×(𝓛-𝒦)} + ℰ^{G̃}`); the remainder, the tail and the
weighted tail clauses stay inside the pin. -/
theorem inst_gridRepN (h : STGridRepN 3) :
    ∃ C₀ CK : ℝ, 0 ≤ C₀ ∧ 0 ≤ CK ∧ ∃ K : ℕ → ℕ, (∀ n, K n ≠ 0) ∧
      (∀ᶠ n in atTop, ((sz0.size n : ℕ) : ℝ) ^ CK ≤ K n) ∧
      ∃ Mart Rem : ∀ n, ((Fin 3 → Bool) × (Fin 3 → Zd 3 (sz0.L n))) → ℕ → PathΩ sz0 → ℂ,
        ∀ n i, ∀ᵐ ω ∂(pathP sz0), ∀ k, k ≤ K n →
          STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 k ω =
            STgAN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 0 ω +
              ((gridStep sInst tInst K n : ℝ) : ℂ) *
                ∑ j ∈ Finset.range k, STgDriftN sz0 sInst tInst K n (STflowE z0 n) i.1 i.2 j ω +
              Rem n i k ω + Mart n i k ω := by
  obtain ⟨C₀, hC₀, hAt⟩ := h 3 (by norm_num)
  obtain ⟨CK, hCK, hK⟩ := hAt (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) 1 one_pos
  have hK0 : ∀ n, ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊ ≠ 0 := fun n =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_size_sz0 n)) _)).ne'
  obtain ⟨Mart, Rem, hid, -, -, -⟩ := hK (fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊) hK0
    (Eventually.of_forall fun n => Nat.le_ceil _)
  exact ⟨C₀, CK, hC₀, hCK, fun n => ⌈((sz0.size n : ℕ) : ℝ) ^ CK⌉₊, hK0,
    Eventually.of_forall fun n => Nat.le_ceil _, Mart, Rem, hid⟩

/-- The theorems of sections 1-2 at concrete data (`d = 3`, `sz0`, `n = 0`): `STLM` of the model matrix
is `Lloop`; the matrix functionals are measurable; the stopping index is a stopping time (`inst_stop`). -/
example (ω : sz0.SeqΩ) :
    STLM sz0 0 (1 / 2) 0 (sz0.seqHflow 0 0 ω) (fun _ : Fin 1 => true) (fun _ => 0) =
      Lloop sz0 0 (1 / 2) 0 (fun _ : Fin 1 => true) (fun _ => 0) ω :=
  STLM_seqHflow sz0 0 (1 / 2) 0 _ _ ω

example (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    STGMM sz0 0 (1 / 2) 0 (sz0.seqHflow 0 0 ω) x y = STGM sz0 0 (1 / 2) 0 ω x y :=
  STGMM_seqHflow sz0 0 (1 / 2) 0 ω x y

example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
    STLM sz0 0 (1 / 2) 0 H (fun _ : Fin 1 => true) (fun _ => 0) :=
  STLM_measurable sz0 0 (1 / 2) 0 _ _

example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
    STJhatM sz0 0 (1 / 2) 1 0 0 H :=
  STJhatM_measurable sz0 0 (1 / 2) 0 1 0

example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
    STEGtM sz0 0 (1 / 2) 0 H ![true, false] ![0, 0] :=
  STEGtM_measurable sz0 0 (1 / 2) 0 _ _

example : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0)) (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ =>
    STEEM sz0 0 (1 / 2) 0 H ![true, false] ![0, 0] :=
  STEEM_measurable sz0 0 (1 / 2) 0 _ _

example (x y : Idx 3 (sz0.L 0) (sz0.W 0)) : Measurable fun H : Matrix (Idx 3 (sz0.L 0) (sz0.W 0))
    (Idx 3 (sz0.L 0) (sz0.W 0)) ℂ => STGMM sz0 0 (1 / 2) 0 H x y :=
  STGMM_measurable sz0 0 (1 / 2) 0 x y

end RBM.Gauss.Step2DefsInst
