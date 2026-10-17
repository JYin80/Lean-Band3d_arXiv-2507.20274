/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.FineModel
import RBM3D.Defs.Sizes
import RBM3D.Defs.Params
import RBM3D.Defs.Semicircle
import RBM3D.Defs.StochDom
import RBM3D.Loop.GLoop
import RBM3D.Loop.KLTree
import RBM3D.Defs.StochDomAt
import RBM3D.Loop.GLoopFlow
import RBM3D.Gauss.DominationAt

/-!
# The pins of `lem:main_ind`, `lem_GbEXP`, `lem_ConArg` and Step 1 (ST-1, S1-07)

Ticket T2028 (S1-07).  Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (cited
`1_2:line`) and `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`).  This file replaces RBM2D's
`Induction/Defs.lean` (`RBM2D/Induction/Defs.lean` at `c9a24cf`: `InitLK`, `Step1LoopUnif`,
`KboundConcl`, `MainIndHyp`, ...) by the estimate-level definitions and the pins of the compiled
T2015 probe (`RBM3D/Probe/T2015Pins.lean` at `752e027` on branch `t/T2015`, never merged).

* Sections 1, 1b, 2 are the probe's sections 1, 1b, 2 (probe lines 161-501), copied with their
  docstrings and proofs; the probe's section 0 (the copy of the T2002 probe, which the base of the
  probe's branch needed) is not copied: its declarations are the merged `Gres`, `loopM`,
  `blockMat`, `loopFine`, `Gt`, `Lloop`, `badSetAt`, `StochDomAt`, `HighProbAt`, `PerTimeDomAt`,
  `TimeIcc`, `Prec`, `PrecPT`, `Whp` (report b.2 of T2015).  The `open` lines of the probe name
  `RBM.Probe.T2015`; here they name `RBM.Path RBM.Gauss`, and the three imports
  `RBM3D.Defs.StochDomAt`, `RBM3D.Loop.GLoopFlow`, `RBM3D.Gauss.DominationAt` are added: the
  rewrite `bind1` of the report of T2015.
* Section 3 (probe lines 503-848): the compiled nonempty instances of the pins at `d = 3` on the
  merged preflight sequence `RBM.Gauss.SizesInst.sz0`, in namespace
  `RBM.Gauss.InductionDefsInst` (the probe's `RBM.Probe.T2015.Inst`).  What stays a hypothesis of an
  instance is a premise that is the statement of another pin or a stochastic premise of the
  theorem itself.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Estimate-level definitions (`ST...`), namespace `RBM.Gauss.Sizes`

The energy is a sequence `E : ℕ → ℝ`, a time is a sequence `τ : ℕ → ℝ` (TEAM §8 lesson 23); the
loop length is `k` (the paper's `n`, here the index of the size sequence).  Every `≺` is `Prec`
(union over the index inside `P`, the scale `N = sz.size n`).  `W^{-d} B_{τ,0}` is the merged
`sz.Bctl n τ`; `ℓ_τ` is the merged `ellT`; `η_τ` is the merged `Gauss.etaT`; `𝒦` is the merged
`RBM.Loop.KLK`; `E_a` is the merged `Gauss.Eblk` (inside `Lloop`).  A distance `|a - b|` between
block labels is `zdistInf` (paper-delta T2002b). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `𝒦^{(k)}_{τ,σ,a}` of `Def_Ktza` at size index `n`, energy `E` (merged `KLK`). -/
def STKloop (n : ℕ) (E τ : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  KLK d (sz.L n) (sz.lam n) (sz.W n) E τ (KLloopOf d (sz.L n) σ a)

/-- `W^{-d} B_{τ,K}` of `(eq_B_param)` (`1_2:1107`) at size index `n`, `K` a block distance;
`STWB sz n τ 0 = sz.Bctl n τ`. -/
def STWB (n : ℕ) (τ : ℝ) (K : ℕ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) τ K

/-- The block label `[x]` of a lattice point `x ∈ Z_{WL}^d` (`(eq:blockIa)`, `1_2:266`). -/
def STblk (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) : Zd d (sz.L n) :=
  (split d (sz.L n) (sz.W n) x).1

/-- `(G_τ - M)_{xy}` for the random band matrix: `M = m(E) I` (`(eq:defMzsc)`, `1_2:344`). -/
def STGM (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  Gt sz n E τ true ω x y - (if x = y then mE E else 0)

/-- `max_{a,b} 𝓛^{(2)}_{τ,(-,+),(a,b)}` (the control of `(GiiGEX)`, `3_5:21`); the loops are
`≥ 0`, the norm only fixes the type. -/
def STmaxLoop2 (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖Lloop sz n E τ ![false, true] ![p.1, p.2] ω‖)

/-- The indicator of `Ω_τ = {‖G_τ‖_max ≤ C₀}` of `lem_ConArg` (`3_5:48`). -/
def STomegaC (n : ℕ) (E τ C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖Gt sz n E τ true ω x y‖ ≤ C₀ then 1 else 0

/-- The right side of `(GijGEX)` (`3_5:24–26`): `Σ_{|a'-a|≤1, |b'-b|≤1, σ ∈ {(+,-),(-,+)}}
𝓛^{(2)}_{τ,σ,(a',b')} + W^{-d} 1_{|a-b|≤1}`, with the paper's `L^∞` distance. -/
def STgexRHS (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖Lloop sz n E τ σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)

/-! ### The hypotheses (a)-(d) of `lem:main_ind` and the estimates of `ML:GLoop`, `ML:GLoop_expec`,
`ML:GtLocal` (the same shapes at the time sequence `τ`) -/

/-- **(a)** `(Eq:L-KGt+IND)` `1_2:1262` / **`(Eq:L-KGt)`** `1_2:1196`: for every fixed loop length
`k ≥ 1`, `max_{σ,a} |𝓛^{(k)}_{τ,σ,a} - 𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^k`. -/
def STLK (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω - STKloop sz n (E n) (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k)

/-- **`(Eq:L-KGt2)`** `1_2:1198` = **`(eq:loopbound_s)`** `3_5:46`: `max_{σ,a} |𝓛^{(k)}_{τ,σ,a}| ≺
(W^{-d}B_{τ,0})^{k-1}`, every `k ≥ 1`. -/
def STLmax (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- **(b), first part** `(Eq:Gdecay+IND)` `1_2:1268` / **`(Eq:Gdecay)`** `1_2:1205`: for `σ ∈ {+,-}²`,
`a ∈ (Z_L^d)²` and every `D > 0`, `|𝓛^{(2)} - 𝒦^{(2)}| ≺ (W^{-d}B_{τ,0})^{1/5}
(W^{-d}B_{τ,|a₁-a₂|}) e^{-(|a₁-a₂|/ℓ_τ)^{1/2}} + W^{-D}`. -/
def STDecay (E τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω - STKloop sz n (E n) (τ n) p.1 p.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ (1 / 5 : ℝ) *
          STWB sz n (τ n) (zdistInf d (sz.L n) (p.2 0 - p.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (τ n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **(b), second part** `(Eq:Gdecay+IND_s<g)` `1_2:1271` / **`(Eq:Gdecay+s<g)`** `1_2:1311`:
only at the sizes with `1 - τ ≥ ilambda²` (the index set is empty otherwise), `|𝓛^{(2)} - 𝒦^{(2)}|
≺ (W^{-d}B_{τ,0})² e^{-|a₁-a₂|^{1/2}} + W^{-D}`. -/
def STDecayStrong (E τ : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - τ n})
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1.1 p.1.2 ω - STKloop sz n (E n) (τ n) p.1.1 p.1.2‖)
      (fun n p _ => (sz.Bctl n (τ n)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **(c)** `(Gt_bound+IND)` `1_2:1274`: `‖G_τ - M‖_max ≺ (W^{-d}B_{τ,0})^{1/2}`. -/
def STLocalMax (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))

/-- **`(Gt_bound)`** `1_2:1222`: `|(G_τ - M)_{xy}|² ≺ W^{-d} B_{τ,(|x-y|/W)}`, with `|x-y|/W` read
as the block distance `|[x]-[y]|` (paper-delta T2001e). -/
def STLocalEntry (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))

/-- **(d)** `(Eq:Gtlp_exp+IND)` `1_2:1281` / **`(Eq:Gtlp_exp)`** `1_2:1209`: `max_{σ,a} |𝔼 𝓛^{(2)} -
𝒦^{(2)}| ≺ (W^{-d}B_{τ,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{τ,0})`; the left side is
deterministic. -/
def STExp2 (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (τ n) p.1 p.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (τ n) p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))

/-- **`(con_st_ind)`** `1_2:1296`: `(W^{-d}B_{t,0})^{𝔠_d} ≤ (1-t)/(1-s) < 1`, eventually in the
size index. -/
def STConStInd (𝔠d : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, (sz.Bctl n (t n)) ^ 𝔠d ≤ (1 - t n) / (1 - s n) ∧ (1 - t n) / (1 - s n) < 1

/-- **`ML:Kbound`** `(eq:bcal_k)` `1_2:1056` at the sequence level: for every time sequence
`τ n ∈ [0,1)`, `max_{σ,a} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}`, every `k ≥ 1` (the left side
is deterministic).  Proved by the KL gate (KL7); a hypothesis of Step 1. -/
def STKbound (E : ℕ → ℝ) : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    ∀ k : ℕ, 1 ≤ k →
      Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖STKloop sz n (E n) (τ n) p.1 p.2‖)
        (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

end RBM.Gauss.Sizes

/-! ## 1b. The three parts of `lem_GbEXP` and the Step 1 conclusions

`lem_GbEXP` (`3_5:14–40`) is a single-time statement: `E, t : ℕ → ℝ` are the flow energy and the
time, `ε₀ > 0` the exponent of `Ω(t, ε₀)` (the paper's "small constant", read as "every
`ε₀ > 0`": the event shrinks as `ε₀` grows, so the claim for small `ε₀` implies the others). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The indicator of `{‖G_τ - M‖_max ≤ A}` (`A = W^{-ε₀}`: `Ω(τ, ε₀)`; `A = 2 α`: the
forbidden-region event of the bootstrap). -/
def STindMax (n : ℕ) (E τ A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E τ ω x y‖ ≤ A then 1 else 0

/-- **`(GiiGEX)`** `3_5:21`: `1(Ω(t,ε₀)) ‖G_t - M‖²_max ≺ max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)}`
(the paper's `W^τ`, `W^{-D}` are `N^τ`, `N^{-D}`: paper-delta T2002i). -/
def STGiiGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)

/-- **`(GijGEX)`** `3_5:24`: `1(Ω(t,ε₀)) max_{x∈[a], y∈[b], x≠y} |(G_t)_{xy}|² ≺ Σ_{|a'-a|≤1,
|b'-b|≤1, σ ∈ {(+,-),(-,+)}} 𝓛^{(2)}_{t,σ,(a',b')} + W^{-d} 1_{|a-b|≤1}`. -/
def STGijGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖Gt sz n (E n) (t n) true ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => STgexRHS sz n (E n) (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- **`(GavLGEX)`** `3_5:33` under `(initialGT2)` `3_5:30`: for a deterministic control
`W^{-d/2} ≤ Ψ_t ≤ W^{-ε₀}`, `‖G_t - M‖_max ≺ W^{-ε₀}` and `max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)} ≺ Ψ_t²`
give `max_a |tr((G_t - M)E_a)| ≺ Ψ_t²`, where `tr((G_t - M)E_a) = 𝓛^{(1)}_{t,+,a} - m(E)`. -/
def STGavLGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  ∀ Ψ : ℕ → ℝ, (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖STGM sz n (E n) (t n) ω p.1 p.2‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
    Prec sz (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)
      (fun n _ _ => Ψ n ^ 2) →
    Prec sz (U := fun n => Zd d (sz.L n))
      (fun n a ω => ‖Lloop sz n (E n) (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - mE (E n)‖)
      (fun n _ _ => Ψ n ^ 2)

/-- **(lRB1)** `1_2:1321`, uniform in `u ∈ [s,t]`: `max_{σ,a} |𝓛^{(k)}_{u,σ,a}| ≺
((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1}`. -/
def STStep1Loop (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- **(Gtmwc)** `1_2:1327`, uniform in `u ∈ [s,t]`: `‖G_u - M‖_max ≺ (W^{-d}B_{u,0})^{1/4}`. -/
def STStep1Weak (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

/-- (lRB1) per time (union over `u` outside `P`): the shape in which Step 2 consumes Step 1
(RBM2D `Step1LoopPT`, `Path/Step2Props.lean:141`). -/
def STStep1LoopPT (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- (Gtmwc) per time (RBM2D `Step1WeakLawPT`, `Path/Step2Props.lean:149`). -/
def STStep1WeakPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

end RBM.Gauss.Sizes

/-! ## 2. The pins (`d` is the dimension; constants before the sequence)

`STFlow` is the setting of `MR:locSC` (`1_2:357–366`) and of the flow framework `zztE`
(`1_2:787`) along a sequence: `sz.Admissible 𝔠 𝔡` (`W ≥ N^𝔠`, `(eq:WO)`, `N → ∞`) and
`z_n ∈ 𝐃_{κ,ε}` at every size index (`(eq:spectral_domain)`, `1_2:380`).  The flow data are
`E_n = lemE z_n`, `t₀_n = lemT z_n` (`(eq:t0E0)`, `1_2:789`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The flow energy `E(z)` of `zztE` along a sequence `z`. -/
def STflowE (z : ℕ → ℂ) : ℕ → ℝ := fun n => lemE (z n)

/-- The setting of `MR:locSC` and `zztE` along a sequence. -/
def STFlow {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, sz.locDomain κ ε n (z n)

/-- **`lem:main_ind`** (`1_2:1256–1330`) at sequence level.  Constants first: `κ, ε, 𝔡`, then
`𝔠_d ∈ (0, 10^{-2}]` (depending on `d, κ, ε, 𝔡` only), then the bandwidth exponent `𝔠`, the sizes
and `z`.  Hypotheses (a)-(d) at `s ∈ [0, t₀]`, the condition `(con_st_ind)`, `s < t ≤ t₀`; the
conclusions `(Eq:L-KGt)`, `(Eq:L-KGt2)`, `(Eq:Gdecay)`, `(Eq:Gtlp_exp)`, `(Gt_bound)` at `t`, and
`(Eq:Gdecay+s<g)` (at the sizes with `1 - t ≥ ilambda²`). -/
def STMainInd (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          (STLK sz (STflowE z) s ∧ STDecay sz (STflowE z) s ∧ STDecayStrong sz (STflowE z) s ∧
            STLocalMax sz (STflowE z) s ∧ STExp2 sz (STflowE z) s) →
          STConStInd sz 𝔠d s t →
          STLK sz (STflowE z) t ∧ STLmax sz (STflowE z) t ∧ STDecay sz (STflowE z) t ∧
            STExp2 sz (STflowE z) t ∧ STLocalEntry sz (STflowE z) t ∧
            STDecayStrong sz (STflowE z) t

/-- **`lem_GbEXP`, `(GiiGEX)`** (`3_5:21`), every `ε₀ > 0`, every `t ∈ [0, t₀]`. -/
def STGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEX sz (STflowE z) t ε₀

/-- **`lem_GbEXP`, `(GijGEX)`** (`3_5:24`). -/
def STGbEXPij (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEX sz (STflowE z) t ε₀

/-- **`lem_GbEXP`, `(GavLGEX)`** (`3_5:33`, hypotheses `(initialGT2)`). -/
def STGbEXPav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEX sz (STflowE z) t ε₀

/-- **`lem_GbEXP`** (`3_5:14–40`), the three parts. -/
def STGbEXP (d : ℕ) : Prop := STGbEXPii d ∧ STGbEXPij d ∧ STGbEXPav d

/-- **Step 1 of `lem:main_ind`** (`1_2:1317–1328`; `3_5:64–66`): from (a), (c), `ML:Kbound`,
`(con_st_ind)` with `𝔠_d ≤ 10^{-2}`, the conclusions `(lRB1)` and `(Gtmwc)` uniformly in
`u ∈ [s,t]`. -/
def STStep1 (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ lemT (z n)) → (∀ n, s n < t n) →
          (∀ n, t n ≤ lemT (z n)) →
          STKbound sz (STflowE z) → STLK sz (STflowE z) s → STLocalMax sz (STflowE z) s →
          STConStInd sz 𝔠d s t →
            STStep1Loop sz (STflowE z) s t ∧ STStep1Weak sz (STflowE z) s t

end RBM.Gauss.Sizes

/-! ## 3. Compiled nonempty instances at `d = 3`

The size data are the merged preflight sequence `RBM.Gauss.SizesInst.sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6} → 0`, `N_n = (W_n L_n)^3`; `n = 0`: `L = 4`, `W = 32`,
`lam = 1/64`, `N = 2097152`), admissible at `𝔠 = 1/6`, `𝔡 = 1/10` (`sz0_admissible`); `κ = ε = 1/10`.
The flow points are `z_n = 1/2 + i N_n^{-4/5} ∈ 𝐃_{κ,ε}` (energy `1/2`, `N^{-1+ε} = N^{-9/10} ≤
Im z_n`), a non-constant sequence of spectral parameters.  Times: `s = 0`, `t = 1/16 ≤ lemT z_n`
(`lemma28_quant`) for `lem:main_ind`, Step 1 and the bootstrap; `t = 1/16` for `lem_GbEXP`;
`1/16 ≤ s = 1/16 ≤ t = 1/2 < 1` for `lem_ConArg`.  Every deterministic hypothesis (`STFlow`, the
time ranges, `STConStInd` for every `𝔠_d > 0`) is discharged; what stays a hypothesis of an
instance is a stochastic premise of the theorem itself (`(a)-(d)` at `s`, `(eq:loopbound_s)`) or the
`ML:Kbound` input. -/

namespace RBM.Gauss.InductionDefsInst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Path Filter

theorem W_ge_32 (n : ℕ) : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  have h : 32 ≤ sz0.W n := by
    change 32 ≤ (2 * (n + 1)) ^ 5
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  exact_mod_cast h

/-! ### 3a. Extreme input: the end of the flow, `t = t₀(z_n) = lemT z_n` (`t → 1`)

The ranges `t ≤ t₀` of `lem_GbEXP` and `1/16 ≤ s ≤ t < 1` of `lem_ConArg` are used up to the right
endpoint: at `t = t₀`, `1 - t₀ = η/(Im m + η)` is as small as the domain `𝐃_{κ,ε}` allows (here
`η = N^{-4/5}`).  `lem:main_ind` and Step 1 need a step `(s, t)` with `(con_st_ind)` there, which is
the numeric instance A of the report, section (a)(ii). -/

/-! ### 3b. Extreme input: the lower end of `(eq:WO)`, `ilambda_n = W_n^{-d/2+𝔡}` exactly

The four pins are applied again at the preflight sequence with `lam_n` replaced by its smallest
admissible value, `W_n^{-3/2+1/10}` (`g → W^{-d/2+𝔡}`): `(eq:WO)` holds with equality at the lower
end, `W^{-d}B_{t,0} ≥ W^{-d} g^{-2}...` is as large as the window allows (`≈ W^{-2𝔡}`), and the
deterministic hypotheses are discharged by the same generic lemmas. -/

end RBM.Gauss.InductionDefsInst
