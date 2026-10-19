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
# The statements of Theorem 2.24 (`lem:main_ind`), Lemma 3.1 (`lem_GbEXP`) and Step 1

Paper: arXiv:2507.20274.  The estimate-level definitions (`ST...`) of the loop estimates, and the
statements `STMainInd` (Theorem 2.24, `lem:main_ind`), `STGbEXP` (Lemma 3.1, `lem_GbEXP`) and
`STStep1` (Step 1 of the proof of `lem:main_ind`, using Lemma 3.2 `lem_ConArg`), for a size sequence
`sz : Sizes d`.

* Section 1 (namespace `RBM.Gauss.Sizes`): `STKloop`, `STWB`, `STblk`, `STGM`, `STmaxLoop2`,
  `STomegaC`, `STgexRHS`, the hypotheses (a)-(d) of `lem:main_ind` (`STLK`, `STLmax`, `STDecay`,
  `STDecayStrong`, `STLocalMax`, `STLocalEntry`, `STExp2`, `STConStInd`) and `STKbound`.
* Section 1b: the three parts of `lem_GbEXP` (`STGiiGEX`, `STGijGEX`, `STGavLGEX`) and the Step 1
  conclusions `STStep1Loop`, `STStep1Weak` with their per-time forms.
* Section 2: the flow setting `STFlow` and the statements `STMainInd`, `STGbEXPii`, `STGbEXPij`,
  `STGbEXPav`, `STGbEXP`, `STStep1`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Estimate-level definitions (`ST...`), namespace `RBM.Gauss.Sizes`

The energy is a sequence `E : ℕ → ℝ`, a time is a sequence `τ : ℕ → ℝ`; the
loop length is `k` (the paper's `n`, here the index of the size sequence).  Every `≺` is `Prec`
(union over the index inside `P`, the scale `N = sz.size n`).  `W^{-d} B_{τ,0}` is `sz.Bctl n τ`;
`ℓ_τ` is `ellT`; `η_τ` is `Gauss.etaT`; `𝒦` is `RBM.Loop.KLK`; `E_a` is `Gauss.Eblk` (inside `Lloop`).
A distance `|a - b|` between block labels is the `L^∞` distance `zdistInf`. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- `𝒦^{(k)}_{τ,σ,a}` of Definition 2.14 (`Def_Ktza`) at size index `n`, energy `E` (`KLK`). -/
def STKloop (n : ℕ) (E τ : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) : ℂ :=
  KLK d (sz.L n) (sz.lam n) (sz.W n) E τ (KLloopOf d (sz.L n) σ a)

/-- `W^{-d} B_{τ,K}` of (2.62) `eq_B_param` at size index `n`, `K` a block distance;
`STWB sz n τ 0 = sz.Bctl n τ`. -/
def STWB (n : ℕ) (τ : ℝ) (K : ℕ) : ℝ :=
  (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) τ K

/-- The block label `[x]` of a lattice point `x ∈ Z_{WL}^d` ((2.2) `eq:blockIa`). -/
def STblk (n : ℕ) (x : Idx d (sz.L n) (sz.W n)) : Zd d (sz.L n) :=
  (split d (sz.L n) (sz.W n) x).1

/-- `(G_τ - M)_{xy}` for the random band matrix: `M = m(E) I` ((2.8) `eq:defMzsc`). -/
def STGM (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) : ℂ :=
  Gt sz n E τ true ω x y - (if x = y then mE E else 0)

/-- `max_{a,b} 𝓛^{(2)}_{τ,(-,+),(a,b)}` (the bound of (3.2) `GiiGEX`); the loops are
`≥ 0`, the norm only fixes the type. -/
def STmaxLoop2 (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n))), Finset.mem_univ _⟩
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖Lloop sz n E τ ![false, true] ![p.1, p.2] ω‖)

/-- The indicator of `Ω_τ = {‖G_τ‖_max ≤ C₀}` of Lemma 3.2 (`lem_ConArg`). -/
def STomegaC (n : ℕ) (E τ C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖Gt sz n E τ true ω x y‖ ≤ C₀ then 1 else 0

/-- The right side of (3.3) `GijGEX`: `Σ_{|a'-a|≤1, |b'-b|≤1, σ ∈ {(+,-),(-,+)}}
𝓛^{(2)}_{τ,σ,(a',b')} + W^{-d} 1_{|a-b|≤1}`, with the paper's `L^∞` distance. -/
def STgexRHS (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (a b : Zd d (sz.L n)) : ℝ :=
  (∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
    ∑ a' ∈ Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1),
      ∑ b' ∈ Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1),
        ‖Lloop sz n E τ σ ![a', b'] ω‖) +
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then 1 else 0)

/-! ### The hypotheses (a)-(d) of Theorem 2.24 (`lem:main_ind`) and the estimates of Lemmas 2.21-2.23
(`ML:GLoop`, `ML:GLoop_expec`, `ML:GtLocal`) (the same shapes at the time sequence `τ`) -/

/-- **(a)** (2.78) `Eq:L-KGt+IND` / **(2.73) `Eq:L-KGt`**: for every fixed loop length
`k ≥ 1`, `max_{σ,a} |𝓛^{(k)}_{τ,σ,a} - 𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^k`. -/
def STLK (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω - STKloop sz n (E n) (τ n) p.1 p.2‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ k)

/-- **(2.74) `Eq:L-KGt2`** = **(3.6) `eq:loopbound_s`**: `max_{σ,a} |𝓛^{(k)}_{τ,σ,a}| ≺
(W^{-d}B_{τ,0})^{k-1}`, every `k ≥ 1`. -/
def STLmax (E τ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (τ n) p.1 p.2 ω‖)
      (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

/-- **(b), first part** (2.79) `Eq:Gdecay+IND` / **(2.75) `Eq:Gdecay`**: for `σ ∈ {+,-}²`,
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

/-- **(b), second part** (2.80) `Eq:Gdecay+IND_s<g` / **(2.84) `Eq:Gdecay+s<g`**:
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

/-- **(c)** (2.81) `Gt_bound+IND`: `‖G_τ - M‖_max ≺ (W^{-d}B_{τ,0})^{1/2}`. -/
def STLocalMax (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ (1 / 2 : ℝ))

/-- **(2.77) `Gt_bound`**: `|(G_τ - M)_{xy}|² ≺ W^{-d} B_{τ,(|x-y|/W)}`, with `|x-y|/W` read
as the block distance `|[x]-[y]|`. -/
def STLocalEntry (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (τ n) ω p.1 p.2‖ ^ 2)
    (fun n p _ => STWB sz n (τ n) (zdistInf d (sz.L n) (STblk sz n p.1 - STblk sz n p.2)))

/-- **(d)** (2.82) `Eq:Gtlp_exp+IND` / **(2.76) `Eq:Gtlp_exp`**: `max_{σ,a} |𝔼 𝓛^{(2)} -
𝒦^{(2)}| ≺ (W^{-d}B_{τ,0})² ((ilambda² W^d)^{-1/5} + W^{-d}B_{τ,0})`; the left side is
deterministic. -/
def STExp2 (E τ : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (fun n p _ => ‖(∫ ω, Lloop sz n (E n) (τ n) p.1 p.2 ω ∂(sz.seqP)) -
        STKloop sz n (E n) (τ n) p.1 p.2‖)
    (fun n _ _ => (sz.Bctl n (τ n)) ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + sz.Bctl n (τ n)))

/-- **(2.83) `con_st_ind`**: `(W^{-d}B_{t,0})^{𝔠_d} ≤ (1-t)/(1-s) < 1`, eventually in the
size index. -/
def STConStInd (𝔠d : ℝ) (s t : ℕ → ℝ) : Prop :=
  ∀ᶠ n in atTop, (sz.Bctl n (t n)) ^ 𝔠d ≤ (1 - t n) / (1 - s n) ∧ (1 - t n) / (1 - s n) < 1

/-- **Lemma 2.16 (`ML:Kbound`)**, (2.58) `eq:bcal_k`, at the sequence level: for every time sequence
`τ n ∈ [0,1)`, `max_{σ,a} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d}B_{τ,0})^{k-1}`, every `k ≥ 1` (the left side
is deterministic); a hypothesis of Step 1. -/
def STKbound (E : ℕ → ℝ) : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) →
    ∀ k : ℕ, 1 ≤ k →
      Prec sz (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p _ => ‖STKloop sz n (E n) (τ n) p.1 p.2‖)
        (fun n _ _ => (sz.Bctl n (τ n)) ^ (k - 1))

end RBM.Gauss.Sizes

/-! ## 1b. The three parts of `lem_GbEXP` and the Step 1 conclusions

Lemma 3.1 (`lem_GbEXP`) is a single-time statement: `E, t : ℕ → ℝ` are the flow energy and the
time, `ε₀ > 0` the exponent of `Ω(t, ε₀)` (the paper's "small constant", read as "every
`ε₀ > 0`": the event shrinks as `ε₀` grows, so the claim for small `ε₀` implies the others). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The indicator of `{‖G_τ - M‖_max ≤ A}` (`A = W^{-ε₀}`: `Ω(τ, ε₀)`; `A = 2 α`: the
forbidden-region event of the bootstrap). -/
def STindMax (n : ℕ) (E τ A : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n E τ ω x y‖ ≤ A then 1 else 0

/-- **(3.2) `GiiGEX`**: `1(Ω(t,ε₀)) ‖G_t - M‖²_max ≺ max_{a,b} 𝓛^{(2)}_{t,(-,+),(a,b)}`
(the paper's `W^τ`, `W^{-D}` are read as `N^τ`, `N^{-D}`). -/
def STGiiGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖STGM sz n (E n) (t n) ω p.1 p.2‖ ^ 2)
    (fun n _ ω => STmaxLoop2 sz n (E n) (t n) ω)

/-- **(3.3) `GijGEX`**: `1(Ω(t,ε₀)) max_{x∈[a], y∈[b], x≠y} |(G_t)_{xy}|² ≺ Σ_{|a'-a|≤1,
|b'-b|≤1, σ ∈ {(+,-),(-,+)}} 𝓛^{(2)}_{t,σ,(a',b')} + W^{-d} 1_{|a-b|≤1}`. -/
def STGijGEX (E t : ℕ → ℝ) (ε₀ : ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
    (fun n p ω => STindMax sz n (E n) (t n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖Gt sz n (E n) (t n) true ω p.1.1 p.1.2‖ ^ 2)
    (fun n p ω => STgexRHS sz n (E n) (t n) ω (STblk sz n p.1.1) (STblk sz n p.1.2))

/-- **(3.5) `GavLGEX`** under (3.4) `initialGT2`: for a deterministic bound
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

/-- **(2.85) `lRB1`**, uniform in `u ∈ [s,t]`: `max_{σ,a} |𝓛^{(k)}_{u,σ,a}| ≺
((1-s)/(1-u))^{k-1} (W^{-d}B_{s,0})^{k-1}`. -/
def STStep1Loop (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- **(2.86) `Gtmwc`**, uniform in `u ∈ [s,t]`: `‖G_u - M‖_max ≺ (W^{-d}B_{u,0})^{1/4}`. -/
def STStep1Weak (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

/-- (2.85) `lRB1` per time (union over `u` outside `P`): the shape in which Step 2 consumes Step 1. -/
def STStep1LoopPT (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    PrecPT sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))

/-- (2.86) `Gtmwc` per time (union over `u` outside `P`). -/
def STStep1WeakPT (E s t : ℕ → ℝ) : Prop :=
  PrecPT sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))

end RBM.Gauss.Sizes

/-! ## 2. The statements (`d` is the dimension; constants before the sequence)

`STFlow` is the setting of Theorem 2.1 (`MR:decol`) and of the flow framework of Lemma 2.10 (`zztE`)
along a sequence: `sz.Admissible 𝔠 𝔡` (`W ≥ N^𝔠`, (2.10) `eq:WO`, `N → ∞`) and
`z_n ∈ 𝐃_{κ,ε}` at every size index ((2.12) `eq:spectral_domain`).  The flow data are
`E_n = lemE z_n`, `t₀_n = lemT z_n` ((2.42) `eq:t0E0`). -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- The flow energy `E(z)` of `zztE` along a sequence `z`. -/
def STflowE (z : ℕ → ℂ) : ℕ → ℝ := fun n => lemE (z n)

/-- The setting of `MR:locSC` and `zztE` along a sequence. -/
def STFlow {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) : Prop :=
  sz.Admissible 𝔠 𝔡 ∧ ∀ n, sz.locDomain κ ε n (z n)

/-- **Theorem 2.24 (`lem:main_ind`)** at sequence level.  Constants first: `κ, ε, 𝔡`, then
`𝔠_d ∈ (0, 10^{-2}]` (depending on `d, κ, ε, 𝔡` only), then the bandwidth exponent `𝔠`, the sizes
and `z`.  Hypotheses (a)-(d) at `s ∈ [0, t₀]`, the condition (2.83) `con_st_ind`, `s < t ≤ t₀`; the
conclusions (2.73) `Eq:L-KGt`, (2.74) `Eq:L-KGt2`, (2.75) `Eq:Gdecay`, (2.76) `Eq:Gtlp_exp`,
(2.77) `Gt_bound` at `t`, and (2.84) `Eq:Gdecay+s<g` (at the sizes with `1 - t ≥ ilambda²`). -/
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

/-- **Lemma 3.1 (`lem_GbEXP`), (3.2) `GiiGEX`**, every `ε₀ > 0`, every `t ∈ [0, t₀]`. -/
def STGbEXPii (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEX sz (STflowE z) t ε₀

/-- **Lemma 3.1 (`lem_GbEXP`), (3.3) `GijGEX`**. -/
def STGbEXPij (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGijGEX sz (STflowE z) t ε₀

/-- **Lemma 3.1 (`lem_GbEXP`), (3.5) `GavLGEX`** (hypotheses (3.4) `initialGT2`). -/
def STGbEXPav (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEX sz (STflowE z) t ε₀

/-- **Lemma 3.1 (`lem_GbEXP`)**, the three parts. -/
def STGbEXP (d : ℕ) : Prop := STGbEXPii d ∧ STGbEXPij d ∧ STGbEXPav d

/-- **Step 1 of Theorem 2.24 (`lem:main_ind`)**: from (a), (c), `ML:Kbound`,
(2.83) `con_st_ind` with `𝔠_d ≤ 10^{-2}`, the conclusions (2.85) `lRB1` and (2.86) `Gtmwc` uniformly in
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
