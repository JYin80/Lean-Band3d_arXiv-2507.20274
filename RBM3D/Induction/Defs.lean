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

/-- The forbidden-region estimate of the continuity argument at the time sequence `u`
(`3_5:64–66`, [YY_25 §5.1]; RBM2D `Induction/Step1.lean:1024`, bound `6 M_s^{-7/15}` against
the threshold `M_s^{-1/4}`): `1(‖G_u - M‖_max ≤ 2α) ‖G_u - M‖_max ≺ α^{3/2}`, `α = (W^{-d}B_{s,0})^{1/4}`. -/
def STForbidden (E s u : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMax sz n (E n) (u n) (2 * (sz.Bctl n (s n)) ^ (1 / 4 : ℝ)) ω *
      ‖STGM sz n (E n) (u n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (s n)) ^ (3 / 8 : ℝ))

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

/-- **`lem_ConArg`** (`3_5:42–62`): `ε₁ ≤ s ≤ t < 1` (the paper allows `t = 1`, where `η_t = 0`;
paper-delta T2015b), the loop bound `(eq:loopbound_s)` at `s`; on `Ω_t = {‖G_t‖_max ≤ C₀}`, for
every `k ≥ 2`, `max |𝓛^{(k)}_t| ≺ ((W^{-d}B_{s,0}) η_s/η_t)^{k-1}` (`(res_lo_bo_eta)`, first form). -/
def STConArg (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ C₀ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ → 0 < C₀ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        STLmax sz (STflowE z) s →
        ∀ k : ℕ, 2 ≤ k →
          Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => STomegaC sz n (STflowE z n) (t n) C₀ ω *
              ‖Lloop sz n (STflowE z n) (t n) p.1 p.2 ω‖)
            (fun n _ _ => (sz.Bctl n (s n) *
              (etaT (STflowE z n) (s n) / etaT (STflowE z n) (t n))) ^ (k - 1))

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

/-- **The continuity bootstrap** of Step 1 (`3_5:64–66`, [YY_25 §5.1]; RBM2D
`Induction/Continuity.lean:65` `GopboundPin`, `PerTimeCalc.lean:698` `forbidden_region`): if the
forbidden-region estimate holds at every time sequence in `[s,t]` and `(c)` holds at `s`, then w.h.p.
`‖G_u - M‖_max ≤ (W^{-d}B_{s,0})^{1/4}` simultaneously for all `u ∈ [s,t]`. -/
def STBootstrap (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        STLocalMax sz (STflowE z) s →
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) → STForbidden sz (STflowE z) s u) →
        Whp sz (fun n => {ω | ∀ u ∈ Set.Icc (s n) (t n), ∀ x y : Idx d (sz.L n) (sz.W n),
          ‖STGM sz n (STflowE z n) u ω x y‖ ≤ (sz.Bctl n (s n)) ^ (1 / 4 : ℝ)})

/-- **The net lift** of Step 1 (`Gopboundu` and the net argument; RBM2D `Induction/Continuity.lean:1261`
`Step1NetLift`): if the loop bound `(lRB1)` holds at every time sequence in `[s,t]` (a per-time
statement: for the `≺` of a family indexed by the times of a net, this is the same as the
statement for every section of the index set, the union bound over the polynomial net being the
content of the lemma), then it holds uniformly in `u ∈ [s,t]`. -/
def STNetLift (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        (∀ u : ℕ → ℝ, (∀ n, s n ≤ u n) → (∀ n, u n ≤ t n) →
          ∀ k : ℕ, 1 ≤ k →
            Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
              (fun n p ω => ‖Lloop sz n (STflowE z n) (u n) p.1 p.2 ω‖)
              (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
          STStep1Loop sz (STflowE z) s t

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

theorem one_le_size_sz0 (n : ℕ) : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by
  have h : 1 ≤ sz0.size n :=
    Nat.one_le_pow _ _ (Nat.mul_pos (sz0.W_pos n) (by have := sz0.three_le_L n; omega))
  exact_mod_cast h

/-- The flow points `z_n = 1/2 + i N_n^{-4/5}`. -/
def z0 (n : ℕ) : ℂ := ⟨1 / 2, ((sz0.size n : ℕ) : ℝ) ^ (-(4 / 5 : ℝ))⟩

theorem z0_locDomain (n : ℕ) : sz0.locDomain (1 / 10) (1 / 10) n (z0 n) := by
  have hN := one_le_size_sz0 n
  refine ⟨?_, ?_, ?_⟩
  · simp only [z0, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    norm_num
  · exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)

theorem z0_im_pos (n : ℕ) : 0 < (z0 n).im :=
  Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_size_sz0 n)) _

theorem z0_im_le_one (n : ℕ) : (z0 n).im ≤ 1 := (z0_locDomain n).2.2

/-- `t₀ = lemT z_n ≥ 1/16` (merged `lemma28_quant`). -/
theorem sixteenth_le_lemT (n : ℕ) : (1 / 16 : ℝ) ≤ lemT (z0 n) :=
  (lemma28_quant (z := z0 n) (κ := 1 / 10) (by norm_num) (z0_im_pos n) (z0_im_le_one n)
    (z0_locDomain n).1).2.1

theorem zero_le_lemT (n : ℕ) : (0 : ℝ) ≤ lemT (z0 n) := (lemT_pos (z0_im_pos n)).le

theorem flow_z0 : STFlow sz0 (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 :=
  ⟨sz0_admissible, z0_locDomain⟩

/-- The start time `s ≡ 0` and the end time `t ≡ 1/16` of the first induction step. -/
def sInst : ℕ → ℝ := fun _ => 0
def tInst : ℕ → ℝ := fun _ => 1 / 16

theorem W_ge_32 (n : ℕ) : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  have h : 32 ≤ sz0.W n := by
    change 32 ≤ (2 * (n + 1)) ^ 5
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
  exact_mod_cast h

/-- `W^{-3} B_{c,0} ≤ 2 (1-c)⁻¹ W^{-3}` for `c < 1` (`ilambda² ≥ 0`, `L ≥ 1`): any size data at `d = 3`. -/
theorem Bctl_const_le_gen (sz : Sizes 3) (n : ℕ) {c : ℝ} (hc1 : c < 1) :
    sz.Bctl n c ≤ 2 * (1 - c)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - c := by linarith
  rw [abs_of_pos hx]
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (sz.lam n ^ 2 + (1 - c))⁻¹ ≤ (1 - c)⁻¹ := inv_anti₀ hx (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ 3 * (1 - c))⁻¹ ≤ (1 - c)⁻¹ := by
    have h3 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 3 := one_le_pow₀ hL
    exact inv_anti₀ hx (by nlinarith)
  have hz : (((0 : ℕ) : ℝ) + 1) ^ (3 - 2) = 1 := by norm_num
  have hW0 : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ *
        ((sz.lam n ^ 2 + (1 - c))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (3 - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ 3 * (1 - c))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ * ((1 - c)⁻¹ * 1 + (1 - c)⁻¹) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ h2) hW0
        simp only [hz, inv_one, mul_one]; exact h1
    _ = 2 * (1 - c)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ := by ring

theorem Bctl_const_le (n : ℕ) {c : ℝ} (hc1 : c < 1) :
    sz0.Bctl n c ≤ 2 * (1 - c)⁻¹ * (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ := Bctl_const_le_gen sz0 n hc1

/-- `W^{-d}B_{1/16,0} → 0` (`≤ 3 W^{-3}`) for any size data at `d = 3` with `W → ∞`. -/
theorem Bctl_tInst_tendsto_gen (sz : Sizes 3)
    (hWt : Tendsto (fun n : ℕ => ((sz.W n : ℕ) : ℝ)) atTop atTop) :
    Tendsto (fun n => sz.Bctl n (tInst n)) atTop (nhds 0) := by
  have hW : Tendsto (fun n : ℕ => (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hWt)
  have hup : Tendsto (fun n : ℕ => 3 * (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) := by
    simpa using hW.const_mul 3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => ?_) (fun n => ?_)
  · unfold Sizes.Bctl Bparam
    positivity
  · have h := Bctl_const_le_gen sz n (c := tInst n) (by simp only [tInst]; norm_num)
    have hW0 : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹ := by positivity
    refine h.trans ?_
    have : 2 * (1 - tInst n)⁻¹ ≤ 3 := by simp only [tInst]; norm_num
    nlinarith

/-- `(con_st_ind)` at `(0, 1/16)` holds eventually for **every** `𝔠_d > 0` (any size data at `d = 3`
with `W → ∞`): the only deterministic hypothesis of `lem:main_ind` that involves the constant `𝔠_d`. -/
theorem conStInd_gen (sz : Sizes 3) (hWt : Tendsto (fun n : ℕ => ((sz.W n : ℕ) : ℝ)) atTop atTop)
    {𝔠d : ℝ} (h𝔠 : 0 < 𝔠d) : STConStInd sz 𝔠d sInst tInst := by
  have h0 : Tendsto (fun n => sz.Bctl n (tInst n) ^ 𝔠d) atTop (nhds ((0 : ℝ) ^ 𝔠d)) :=
    (Bctl_tInst_tendsto_gen sz hWt).rpow_const (Or.inr h𝔠.le)
  rw [Real.zero_rpow h𝔠.ne'] at h0
  filter_upwards [h0.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 15 / 16))] with n hn
  simp only [sInst, tInst] at hn ⊢
  refine ⟨?_, ?_⟩
  · norm_num; linarith
  · norm_num

theorem W_tendsto_sz0 : Tendsto (fun n : ℕ => ((sz0.W n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h : n ≤ sz0.W n := by
    change n ≤ (2 * (n + 1)) ^ 5
    calc n ≤ 2 * (n + 1) := by omega
      _ ≤ (2 * (n + 1)) ^ 5 := Nat.le_self_pow (by norm_num) _
  exact_mod_cast h

theorem Bctl_tInst_tendsto : Tendsto (fun n => sz0.Bctl n (tInst n)) atTop (nhds 0) :=
  Bctl_tInst_tendsto_gen sz0 W_tendsto_sz0

theorem conStInd_inst {𝔠d : ℝ} (h𝔠 : 0 < 𝔠d) : STConStInd sz0 𝔠d sInst tInst :=
  conStInd_gen sz0 W_tendsto_sz0 h𝔠

/-- **`lem:main_ind`, instantiated**: the constant `𝔠_d` of the pin, then the deterministic data
`(sz0, z0, s ≡ 0, t ≡ 1/16)` with `(con_st_ind)`; the premises `(a)-(d)` at `s` stay hypotheses. -/
theorem inst_mainInd (h : STMainInd 3) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ((STLK sz0 (STflowE z0) sInst ∧ STDecay sz0 (STflowE z0) sInst ∧
          STDecayStrong sz0 (STflowE z0) sInst ∧ STLocalMax sz0 (STflowE z0) sInst ∧
          STExp2 sz0 (STflowE z0) sInst) →
        (STLK sz0 (STflowE z0) tInst ∧ STLmax sz0 (STflowE z0) tInst ∧
          STDecay sz0 (STflowE z0) tInst ∧ STExp2 sz0 (STflowE z0) tInst ∧
          STLocalEntry sz0 (STflowE z0) tInst ∧ STDecayStrong sz0 (STflowE z0) tInst)) := by
  obtain ⟨𝔠d, h0, h1, hall⟩ :=
    h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨𝔠d, h0, h1, fun hyp => ?_⟩
  exact hall (1 / 6) sz0 z0 flow_z0 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hyp
    (conStInd_inst h0)

/-- **`lem_GbEXP`, three parts, instantiated** at `t ≡ 1/16 ≤ t₀`, `ε₀ = 1/20`. -/
theorem inst_gbEXP (h : STGbEXP 3) :
    STGiiGEX sz0 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tInst (1 / 20) := by
  refine ⟨h.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num),
    h.2.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num),
    h.2.2 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num)⟩

/-- **`lem_GbEXP` part 3 `(GavLGEX)`, applied** at the concrete deterministic control
`Ψ_n = W_n^{-1}`, `ε₀ = 1/20`: both window bounds `W^{-3/2} ≤ Ψ_n ≤ W^{-1/20}` (`3_5:28`) are
discharged; only the two `Prec` premises of `(initialGT2)` stay hypotheses. -/
theorem inst_gbEXP_av (h : STGbEXP 3)
    (hG : Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
      (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ))))
    (hL : Prec sz0 (U := fun _ => Unit) (fun n _ ω => STmaxLoop2 sz0 n (STflowE z0 n) (tInst n) ω)
      (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2)) :
    Prec sz0 (U := fun n => Zd 3 (sz0.L n))
      (fun n a ω => ‖Lloop sz0 n (STflowE z0 n) (tInst n) (fun _ : Fin 1 => true) (fun _ => a) ω -
        mE (STflowE z0 n)‖)
      (fun n _ _ => (((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ^ 2) := by
  refine (inst_gbEXP h).2.2 (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) ?_ ?_ hG hL
  · exact Eventually.of_forall fun n =>
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num)
  · exact Eventually.of_forall fun n =>
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast sz0.W_pos n) (by norm_num)

/-- **`lem_ConArg`, instantiated**: `ε₁ = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t ≡ 1/2 < 1`; the premise
`(eq:loopbound_s)` stays a hypothesis. -/
theorem inst_conArg (h : STConArg 3) (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) := fun k hk =>
  h (1 / 10) (1 / 10) (1 / 10) (1 / 16) 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 (fun _ => 1 / 16) (fun _ => 1 / 2)
    (fun _ => le_rfl) (fun n => by norm_num) (fun n => by norm_num) hL k hk

/-- **Step 1, instantiated**: any `𝔠_d ∈ (0, 10^{-2}]`; the stochastic premises `(a)`, `(c)` and
`ML:Kbound` stay hypotheses. -/
theorem inst_step1 (h : STStep1 3) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hK : STKbound sz0 (STflowE z0)) (ha : STLK sz0 (STflowE z0) sInst)
    (hc : STLocalMax sz0 (STflowE z0) sInst) :
    STStep1Loop sz0 (STflowE z0) sInst tInst ∧ STStep1Weak sz0 (STflowE z0) sInst tInst :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 𝔠d h0 h1 (1 / 6) sz0 z0
    flow_z0 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hK ha hc
    (conStInd_inst h0)

/-- **The bootstrap, instantiated**: the forbidden-region estimate at every time in `[0, 1/16]`
stays a hypothesis. -/
theorem inst_bootstrap (h : STBootstrap 3) (hc : STLocalMax sz0 (STflowE z0) sInst)
    (hF : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      STForbidden sz0 (STflowE z0) sInst u) :
    Whp sz0 (fun n => {ω | ∀ u ∈ Set.Icc (sInst n) (tInst n),
      ∀ x y : Idx 3 (sz0.L n) (sz0.W n),
        ‖STGM sz0 n (STflowE z0 n) u ω x y‖ ≤ (sz0.Bctl n (sInst n)) ^ (1 / 4 : ℝ)}) :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    sInst tInst (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) hc hF

/-- **The net lift, instantiated.** -/
theorem inst_netLift (h : STNetLift 3)
    (hu : ∀ u : ℕ → ℝ, (∀ n, sInst n ≤ u n) → (∀ n, u n ≤ tInst n) →
      ∀ k : ℕ, 1 ≤ k →
        Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
          (fun n p ω => ‖Lloop sz0 n (STflowE z0 n) (u n) p.1 p.2 ω‖)
          (fun n _ _ => ((1 - sInst n) / (1 - u n)) ^ (k - 1) * (sz0.Bctl n (sInst n)) ^ (k - 1))) :
    STStep1Loop sz0 (STflowE z0) sInst tInst :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0
    sInst tInst (fun _ => le_rfl) (fun n => by simp only [sInst, tInst]; norm_num)
    (fun n => sixteenth_le_lemT n) hu

/-! ### 3a. Extreme input: the end of the flow, `t = t₀(z_n) = lemT z_n` (`t → 1`)

The ranges `t ≤ t₀` of `lem_GbEXP` and `1/16 ≤ s ≤ t < 1` of `lem_ConArg` are used up to the right
endpoint: at `t = t₀`, `1 - t₀ = η/(Im m + η)` is as small as the domain `𝐃_{κ,ε}` allows (here
`η = N^{-4/5}`).  `lem:main_ind` and Step 1 need a step `(s, t)` with `(con_st_ind)` there, which is
the numeric instance A of the report, section (a)(ii). -/

/-- The end of the flow, `t₀ = lemT z_n`. -/
def tEnd : ℕ → ℝ := fun n => lemT (z0 n)

theorem tEnd_lt_one (n : ℕ) : tEnd n < 1 := lemT_lt_one (z0_im_pos n)

/-- **`lem_GbEXP`, three parts, at the end of the flow** `t = t₀`, `ε₀ = 1/20`. -/
theorem inst_gbEXP_endT (h : STGbEXP 3) :
    STGiiGEX sz0 (STflowE z0) tEnd (1 / 20) ∧ STGijGEX sz0 (STflowE z0) tEnd (1 / 20) ∧
      STGavLGEX sz0 (STflowE z0) tEnd (1 / 20) :=
  ⟨h.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tEnd (fun n => zero_le_lemT n) (fun _ => le_rfl) (1 / 20) (by norm_num),
    h.2.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tEnd (fun n => zero_le_lemT n) (fun _ => le_rfl) (1 / 20) (by norm_num),
    h.2.2 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 z0
      flow_z0 tEnd (fun n => zero_le_lemT n) (fun _ => le_rfl) (1 / 20) (by norm_num)⟩

/-- **`lem_ConArg`, at the end of the flow**: `ε₁ = 1/16`, `C₀ = 2`, `s ≡ 1/16 ≤ t = t₀ < 1`;
the premise `(eq:loopbound_s)` stays a hypothesis. -/
theorem inst_conArg_endT (h : STConArg 3) (hL : STLmax sz0 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz0 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => STomegaC sz0 n (STflowE z0 n) (tEnd n) 2 ω *
          ‖Lloop sz0 n (STflowE z0 n) (tEnd n) p.1 p.2 ω‖)
        (fun n _ _ => (sz0.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) (tEnd n))) ^ (k - 1)) := fun k hk =>
  h (1 / 10) (1 / 10) (1 / 10) (1 / 16) 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz0 z0 flow_z0 (fun _ => 1 / 16) tEnd
    (fun _ => le_rfl) (fun n => sixteenth_le_lemT n) tEnd_lt_one hL k hk

/-! ### 3b. Extreme input: the lower end of `(eq:WO)`, `ilambda_n = W_n^{-d/2+𝔡}` exactly

The four pins are applied again at the preflight sequence with `lam_n` replaced by its smallest
admissible value, `W_n^{-3/2+1/10}` (`g → W^{-d/2+𝔡}`): `(eq:WO)` holds with equality at the lower
end, `W^{-d}B_{t,0} ≥ W^{-d} g^{-2}...` is as large as the window allows (`≈ W^{-2𝔡}`), and the
deterministic hypotheses are discharged by the same generic lemmas. -/

/-- The preflight sequence with the coupling at the lower end of `(eq:WO)`. -/
def sz1 : Sizes 3 := sz0.withLam fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2 + 1 / 10)

theorem sz1_admissible : sz1.Admissible (1 / 6) (1 / 10) := by
  refine ⟨by norm_num, by norm_num, sz0_tendsto, sz0_bandwidth, ?_⟩
  refine Eventually.of_forall fun n => ⟨?_, ?_⟩
  · change ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10) ≤
      ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2 + 1 / 10)
    norm_num
  · have hW : (1 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n
    have h := Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num : (-(3 : ℝ) / 2 + 1 / 10) ≤ 0)
    change ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2 + 1 / 10) ≤ ((1 : ℝ) / 10)⁻¹
    norm_num
    linarith

theorem flow_z1 : STFlow sz1 (1 / 10) (1 / 10) (1 / 6) (1 / 10) z0 :=
  ⟨sz1_admissible, fun n => z0_locDomain n⟩

theorem W_tendsto_sz1 : Tendsto (fun n : ℕ => ((sz1.W n : ℕ) : ℝ)) atTop atTop := W_tendsto_sz0

/-- `lem:main_ind` at the extreme coupling. -/
theorem inst_mainInd_lowg (h : STMainInd 3) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ((STLK sz1 (STflowE z0) sInst ∧ STDecay sz1 (STflowE z0) sInst ∧
          STDecayStrong sz1 (STflowE z0) sInst ∧ STLocalMax sz1 (STflowE z0) sInst ∧
          STExp2 sz1 (STflowE z0) sInst) →
        (STLK sz1 (STflowE z0) tInst ∧ STLmax sz1 (STflowE z0) tInst ∧
          STDecay sz1 (STflowE z0) tInst ∧ STExp2 sz1 (STflowE z0) tInst ∧
          STLocalEntry sz1 (STflowE z0) tInst ∧ STDecayStrong sz1 (STflowE z0) tInst)) := by
  obtain ⟨𝔠d, h0, h1, hall⟩ :=
    h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨𝔠d, h0, h1, fun hyp => ?_⟩
  exact hall (1 / 6) sz1 z0 flow_z1 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hyp
    (conStInd_gen sz1 W_tendsto_sz1 h0)

/-- `lem_GbEXP` (three parts) at the extreme coupling. -/
theorem inst_gbEXP_lowg (h : STGbEXP 3) :
    STGiiGEX sz1 (STflowE z0) tInst (1 / 20) ∧ STGijGEX sz1 (STflowE z0) tInst (1 / 20) ∧
      STGavLGEX sz1 (STflowE z0) tInst (1 / 20) :=
  ⟨h.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz1 z0
      flow_z1 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num),
    h.2.1 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz1 z0
      flow_z1 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num),
    h.2.2 (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz1 z0
      flow_z1 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
      (by norm_num)⟩

/-- `lem_ConArg` at the extreme coupling. -/
theorem inst_conArg_lowg (h : STConArg 3) (hL : STLmax sz1 (STflowE z0) (fun _ => 1 / 16)) :
    ∀ k : ℕ, 2 ≤ k →
      Prec sz1 (U := fun n => (Fin k → Bool) × (Fin k → Zd 3 (sz1.L n)))
        (fun n p ω => STomegaC sz1 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) 2 ω *
          ‖Lloop sz1 n (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n) p.1 p.2 ω‖)
        (fun n _ _ => (sz1.Bctl n ((fun _ => (1 : ℝ) / 16) n) *
          (etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 16) n) /
            etaT (STflowE z0 n) ((fun _ => (1 : ℝ) / 2) n))) ^ (k - 1)) := fun k hk =>
  h (1 / 10) (1 / 10) (1 / 10) (1 / 16) 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (1 / 6) sz1 z0 flow_z1 (fun _ => 1 / 16) (fun _ => 1 / 2)
    (fun _ => le_rfl) (fun n => by norm_num) (fun n => by norm_num) hL k hk

/-- Step 1 at the extreme coupling (any `𝔠_d ∈ (0, 10^{-2}]`). -/
theorem inst_step1_lowg (h : STStep1 3) {𝔠d : ℝ} (h0 : 0 < 𝔠d) (h1 : 𝔠d ≤ 1 / 100)
    (hK : STKbound sz1 (STflowE z0)) (ha : STLK sz1 (STflowE z0) sInst)
    (hc : STLocalMax sz1 (STflowE z0) sInst) :
    STStep1Loop sz1 (STflowE z0) sInst tInst ∧ STStep1Weak sz1 (STflowE z0) sInst tInst :=
  h (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) 𝔠d h0 h1 (1 / 6) sz1 z0
    flow_z1 sInst tInst (fun _ => le_rfl) (fun n => zero_le_lemT n)
    (fun n => by simp only [sInst, tInst]; norm_num) (fun n => sixteenth_le_lemT n) hK ha hc
    (conStInd_gen sz1 W_tendsto_sz1 h0)

end RBM.Gauss.InductionDefsInst
