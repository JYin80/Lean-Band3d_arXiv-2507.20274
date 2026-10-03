/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Defs
import RBM3D.Evolution.Pins
import RBM3D.Evolution.SumDecay
import RBM3D.Propagator.Prop6Hold
import RBM3D.Loop.KLWard

set_option linter.style.longLine false

/-!
# S3-01 (ticket T2049): the pins of Steps 3 and 4 of `lem:main_ind`, their ingredients and the
# consumer form of the evolution-kernel pins (EK-6)

Moved from the T2041 design probe (`git show 3c58211:RBM3D/Probe/T2041Pins.lean`, sections 1-4, with the
`STMollifierProps` docstring tag corrected to `T2041b`; section 5 and 6 of the probe belong to EK-6 and S3-25/S3-26).
Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`) and
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`).  The pins live in `RBM.Gauss.Sizes`, prefix `ST`;
every `≺` is the merged `Prec` (scale `N = sz.size n`); constants are quantified before the sequence.

* §1 vocabulary (`STXiL`, `STXiLK`, `STPsi`, `STPsum`, `STQop`, `STIdiff`, the hierarchy terms), ported from RBM2D
  `Induction/HierVocab.lean:150-193` at `c9a24cf`;
* §2 the targets `STStep3R`, `STStep4R` and the Step-2 conclusions `STStep2Concl`, `STLmaxU`, `STLKU`;
* §3 the ingredient pins; §4 the consumer forms `STEK*`;
* `st_Bctl_pos`, then the deterministic instances at `d = 3` (`sz0` and `szB`) in `RBM.Gauss.Step34Inst`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Vocabulary -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The pairs `(v, u)`, `s_n ≤ v ≤ u ≤ t_n`: the index set of "`sup_{v ∈ [s,u]}`, uniformly in
`u ∈ [s,t]`" (`3_5:1366`, `3_5:1407-1410`, `(eq:iteration_induc)`). -/
abbrev STPair (s t : ℕ → ℝ) (n : ℕ) : Type := {q : ℝ × ℝ // s n ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ t n}

/-- `max_{σ,a} |𝓛^{(k)}_{v,σ,a}|` at size index `n`, energy `E`, time `v`. -/
def STmaxL (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) => ‖Lloop sz n E v p.1 p.2 ω‖)

/-- `max_{σ,a} |(𝓛 - 𝒦)^{(k)}_{v,σ,a}|`. -/
def STmaxLK (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  Finset.univ.sup' ⟨((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))), Finset.mem_univ _⟩
    (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Lloop sz n E v p.1 p.2 ω - STKloop sz n E v p.1 p.2‖)

/-- **`Ξ̂^{(𝓛)}_{v,k}`** of `(def:XiL)` (`3_5:1010`): `1 + max_{σ,a} |𝓛^{(k)}_{v,σ,a}| /
(W^{-d}B_{v,0})^{k-1}`; the deterministic control parameters `Ξ^{(𝓛)}` of the paper dominate it. -/
def STXiL (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  1 + STmaxL sz n E v k ω / (sz.Bctl n v) ^ (k - 1)

/-- **`Ξ̂^{(𝓛-𝒦)}_{v,k}`** of `(def:XIL-K)` (`3_5:1012`): `1 + max_{σ,a} |(𝓛-𝒦)^{(k)}_{v,σ,a}| /
(W^{-d}B_{v,0})^k`. -/
def STXiLK (n : ℕ) (E v : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  1 + STmaxLK sz n E v k ω / (sz.Bctl n v) ^ k

/-- **The control parameter `Ψ(n,k;s,t)`** of `(adsyzz0s8d6)` (`3_5:1396`), case `1 - s ≤ ilambda²`:
`A^{3/4} + r^{n-1} A^{1-k/8}` with `A = ilambda² W^d` and `r = η_s/η_t`; and of
`(eq:psipara_smalletacase)` (`3_5:1578`), case `1 - s ≤ ilambda²/L²`: the same shape with
`A = (W^{-d}B_{s,0})⁻¹` (the printed formula is `A^{3/4}` written as `(W^{-d}B_{s,0})^{-3/4}` and
`A^{1-k/8}` as `(W^{-d}B_{s,0})^{k/8-1}`). -/
def STPsi (A r : ℝ) (n k : ℕ) : ℝ := A ^ (3 / 4 : ℝ) + r ^ (n - 1) * A ^ (1 - (k : ℝ) / 8)

/-- `ilambda² W^d` of `Ψ` in case `1 - s ≤ ilambda²`. -/
def STAI (n : ℕ) : ℝ := sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d

/-- `(W^{-d}B_{s,0})⁻¹` of `Ψ` in case `1 - s ≤ ilambda²/L²`. -/
def STAII (s : ℕ → ℝ) (n : ℕ) : ℝ := (sz.Bctl n (s n))⁻¹

/-! ### Tensor operators of `Def:QtPt` and `def;zero_mode_remove` -/

/-- `(𝒫 ∘ 𝒜)_{a₁} = Σ_{a₂,…,a_k} 𝒜_a` (`Def:QtPt`, `3_5:1204`); tensors of `m + 1` indices. -/
def STPsum {m L : ℕ} [NeZero L] (A : (Fin (m + 1) → Zd d L) → ℂ) (a₁ : Zd d L) : ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), A a

/-- The sum-zero operator `𝒬_t 𝒜 = 𝒜 - (𝒫 𝒜)_{a₁} ϑ_{t,a}` (`(eq:sumzero_op)`, `3_5:1210`) for a
mollifier family `ϑ : t ↦ tensor` (`(eq:suma1chi)`, `(eq:derv_Theta)`: `STMollifier`). -/
def STQop {m L : ℕ} [NeZero L] (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) (t : ℝ)
    (A : (Fin (m + 1) → Zd d L) → ℂ) : (Fin (m + 1) → Zd d L) → ℂ :=
  fun a => A a - STPsum (d := d) A (a 0) * ϑ t a

/-- `I_diff(σ) = {i : σ_i ≠ σ_{i+1}}`, cyclic (`3_5:1470-1471`). -/
def STIdiff {k : ℕ} (σ : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i => σ i ≠ σ (finRotate k i))

/-! ### The hierarchy terms of `eq_L-Keee` (`3_5:75-100`, `def_EwtG` `1_2:961`, `def:CALE` `3_5:169`)

Port of RBM2D `Induction/HierVocab.lean:150-193` (`LLf`, `LKf`, `ksimLK`, `elklkN`, `egtN`, `eeLoop`,
`eeN`; `c9a24cf`) onto the merged `loopL`, `blockMat`, `seqHflow`, `KLK`, `LoopIdx.cutGlue{,L,R}`:
`Z2 L ↦ Zd d L`, `W^2 ↦ W^d`, `SB L ↦ SB d L g`. -/

/-- `𝓛_{τ,I}` of a list-based loop index (the matrix `blockMat (H_τ)`, the flow value `zt E τ`). -/
def STLI (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (seqHflow sz n τ ω)) (zt E τ) I

/-- `𝒦_{τ,I}` of a list-based loop index (merged `KLK`). -/
def STKI (n : ℕ) (E τ : ℝ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  KLK d (sz.L n) (sz.lam n) (sz.W n) E τ I

/-- `(𝓛 - 𝒦)_{τ,I}`. -/
def STLKI (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  STLI sz n E τ ω I - STKI sz n E τ I

/-- `[𝒦^{(l)} ∼ (𝓛-𝒦)]^{(n)}_{τ,I}` of `(DefKsimLK)` (`3_5:89`): the cut pairs `k < l'` with the
`𝒦`-piece of length `l`, both orders. -/
def STksimLK (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (l : ℕ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      ((if (I.cutGlueR k l' b).length = l then
          STLKI sz n E τ ω (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
            STKI sz n E τ (I.cutGlueR k l' b)
        else 0) +
       (if (I.cutGlueL k l' a).length = l then
          STKI sz n E τ (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
            STLKI sz n E τ ω (I.cutGlueR k l' b)
        else 0))

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(n)}_{τ,I}` of `(def_ELKLK)` (`3_5:97`). -/
def STelklk (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ l' ∈ Finset.Ioc k I.length,
    ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
      STLKI sz n E τ ω (I.cutGlueL k l' a) * SB d (sz.L n) (sz.lam n) a b *
        STLKI sz n E τ ω (I.cutGlueR k l' b)

/-- `tr(G̃_τ(σ) E_a) = 𝓛^{(1)}_{τ,σ,a} - m(σ)`, `G̃ = G - m` (`def_EwtG`). -/
def STavgErr (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (σ : Bool) (a : Zd d (sz.L n)) : ℂ :=
  STLI sz n E τ ω ⟨[σ], [a]⟩ - mSigma E σ

/-- `ℰ^{G̃,(n)}_{τ,I}` of `(def_EwtG)` (`1_2:961`): the light-weight term. -/
def STegt (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) (I : LoopIdx (Zd d (sz.L n))) : ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 I.length, ∑ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n),
    STavgErr sz n E τ ω (I.σ.getD (k - 1) false) a * SB d (sz.L n) (sz.lam n) a b *
      STLI sz n E τ ω (I.cutGlue k b)

/-- The `(2n+2)`-loop of `(def_diffakn_k)` (`3_5:187`), cut at the edge `k`:
`a^{(k)} = (a_k..a_n, a_1..a_{k-1}, b', a'_{k-1}..a'_1, a'_n..a'_k, b)`,
`σ^{(k)} = (σ_k..σ_n, σ_1..σ_k, σ̄_k..σ̄_1, σ̄_n..σ̄_k)`. -/
def STeeLoop {α : Type*} (σ : List Bool) (a a' : List α) (k : ℕ) (b b' : α) : LoopIdx α :=
  ⟨σ.drop (k - 1) ++ σ.take k ++ ((σ.take k).reverse.map not) ++ ((σ.drop (k - 1)).reverse.map not),
    a.drop (k - 1) ++ a.take (k - 1) ++ [b'] ++ (a'.take (k - 1)).reverse ++
      (a'.drop (k - 1)).reverse ++ [b]⟩

/-- `(ℰ⊗ℰ)^{M,(n)}_{τ,σ,a,a'}` of `(defEOTE)` (`3_5:176`): the quadratic variation loop, summed over
the cut edge `k`. -/
def STee (n : ℕ) (E τ : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin m → Bool) (a a' : Fin m → Zd d (sz.L n)) :
    ℂ :=
  (((sz.W n : ℕ) : ℂ) ^ d) * ∑ k ∈ Finset.Icc 1 m, ∑ b : Zd d (sz.L n), ∑ b' : Zd d (sz.L n),
    SB d (sz.L n) (sz.lam n) b b' *
      STLI sz n E τ ω (STeeLoop (List.ofFn σ) (List.ofFn a) (List.ofFn a') k b b')

/-! ## 2. Steps 3 and 4 uniformly in `u ∈ [s,t]`; the conclusions of Step 2 that Step 3 consumes

`STLmaxU`, `STLKU` are the shapes of `STLmax`, `STLK` (DECISIONS §19) with the time sequence `τ`
replaced by `u ∈ [s_n, t_n]` inside `Prec` (union over `u` inside `P`, as the paper's "uniformly in
`u`", `1_2:1371`).  Step 2 (ST-D2, T2039) provides `(Gt_bound_flow)`, `(Gt_avgbound_flow)`,
`(Eq:Gdecay_w)` uniformly in `u`: `STStep2Concl`.  `STLK`, `STLocalEntry`, `STDecay` of §19 are at one
time sequence, and `STDecay` has no loss `((1-s)/(1-u))^{C_d}` (`STGdecayW`): so the three
uniform statements are new. -/

/-- **`(Eq:LGxb)`** (`1_2:1361`), uniformly in `u ∈ [s,t]`: `max_{σ,a} |𝓛^{(k)}_{u,σ,a}| ≺
(W^{-d}B_{u,0})^{k-1}`, every `k ≥ 1`. -/
def STLmaxU (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (k - 1))

/-- **`(Eq:L-KGt-flow)`** (`1_2:1371`), uniformly in `u ∈ [s,t]`: `max_{σ,a} |(𝓛-𝒦)^{(k)}_{u,σ,a}| ≺
(W^{-d}B_{u,0})^k`, every `k ≥ 1`. -/
def STLKU (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ k)

/-- **`(Gt_avgbound_flow)`** (`1_2:1344`), uniformly in `u`: `max_a |tr((G_u - M)E_a)| ≺ W^{-d}B_{u,0}`,
i.e. `STLKU` at `k = 1` (`tr((G_u - M)E_a) = 𝓛^{(1)}_{u,+,a} - 𝒦^{(1)}_{u,+,a}`). -/
def STAvgU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n)))
    (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ 1)

/-- **`(Gt_bound_flow)`** (`1_2:1342`), uniformly in `u`: `|(G_u - M)_{xy}|² ≺ W^{-d}B_{u,|[x]-[y]|}`
(the shape of `STLocalEntry` with the index `u ∈ [s,t]` inside `Prec`). -/
def STLocalEntryU (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
    (fun n p ω => ‖STGM sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2‖ ^ 2)
    (fun n p _ => STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (STblk sz n p.2.1 - STblk sz n p.2.2)))

/-- **`(Eq:Gdecay_w)`** (`1_2:1349`), uniformly in `u ∈ [s,t]`, every `σ ∈ {±}²`, with the loss
`((1-s)/(1-u))^{C_d}`: `|𝓛^{(2)}_u - 𝒦^{(2)}_u| ≺ ((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5}
(W^{-d}B_{u,|a₁-a₂|}) e^{-(|a₁-a₂|/ℓ_u)^{1/2}} + W^{-D}`.  `C_d` is the constant of Step 2,
independent of `𝔠_d` of `(con_st_ind)`. -/
def STGdecayW (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖Lloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω - STKloop sz n (E n) (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) /
            ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **The conclusions of Step 2 that Steps 3-4 consume** (`1_2:1342-1349`): `(Gt_bound_flow)`,
`(Gt_avgbound_flow)`, `(Eq:Gdecay_w)` with the loss exponent `C_d`.  The pins of T2039 (ST-D2) must
imply this bundle; Step 3 needs nothing else from Step 2. -/
def STStep2Concl (E s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  STLocalEntryU sz E s t ∧ STAvgU sz E s t ∧ STGdecayW sz E s t Cd

/-- **`lem_wardineq_K`**, `(wardineq_K)` (`3_5:1001`, KL pin `KLwardIneqPin` of T2004 / KL12), at the
sequence level: for every time sequence `τ ∈ [0,1)` and `k ≥ 2`, `max_σ Σ_{a_k} |𝒦^{(k)}_{τ,σ,a}| ≺
(W^d η_τ)⁻¹ (W^{-d}B_{τ,0})^{k-2}` (the sum is over the last label; the left side is deterministic,
so this is the `L^τ`-loss form `KLwardIneqAt` converted to the scale `N`).  Registry class: **owed**
(KL12 proves it). -/
def STKward (E : ℕ → ℝ) : Prop :=
  ∀ τ : ℕ → ℝ, (∀ n, 0 ≤ τ n) → (∀ n, τ n < 1) → ∀ k : ℕ, 2 ≤ k →
    Prec sz (U := fun n => (Fin k → Bool) × (Fin (k - 1) → Zd d (sz.L n)))
      (fun n p _ => ∑ x : Zd d (sz.L n),
        ‖STKI sz n (E n) (τ n) ⟨List.ofFn p.1, List.ofFn p.2 ++ [x]⟩‖)
      (fun n _ _ => (((sz.W n : ℕ) : ℝ) ^ d * etaT (E n) (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2))

/-- **Case (i)** of `3_5:1105`: `1 - t ≥ ilambda²/L²`, for all sizes. -/
def STCaseI (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n

/-- **Case (ii)** of `3_5:1105`: `1 - s ≤ ilambda²/L²`, for all sizes. -/
def STCaseII (s _t : ℕ → ℝ) : Prop :=
  ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2

/-- **Step 3 of `lem:main_ind`** (`1_2:1359-1366`; proof `3_5:1107-1601`), uniformly in `u ∈ [s,t]`, under
a regime predicate `R` of the time sequences (`True`: the general statement; `STCaseI`, `STCaseII`: the
two cases of `3_5:1105`).  Constants first: `κ, ε, 𝔡`, the Step-2 exponent `C_d`, then
`𝔠_d ∈ (0, 10^{-2}]` (small depending on `C_d`: `(eq:sumtwoloop)`, `3_5:1069`), then `𝔠`, the sizes, `z`.
Hypotheses: (a) at `s`, `(lRB1)` (Step 1), the three conclusions of Step 2, `(con_st_ind)`, `ML:Kbound`
(`STKbound`), `(wardineq_K)` (`STKward`). -/
def STStep3R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t

/-- **Step 4 of `lem:main_ind`** (`1_2:1370-1374`; proof `3_5:1602-1614`), uniformly in `u ∈ [s,t]`: the
hypotheses of Step 3 and its conclusion `(Eq:LGxb)` give `(Eq:L-KGt-flow)`. -/
def STStep4R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t →
          STLKU sz (STflowE z) s t

/-- The regime predicates as functions of the sizes (`STCaseI`, `STCaseII` have an implicit `d`). -/
def STAny {d : ℕ} (_sz : Sizes d) (_s _t : ℕ → ℝ) : Prop := True

/-- Steps 3 and 4, the general statements, and the two cases. -/
def STStep3 (d : ℕ) : Prop := STStep3R d STAny
def STStep4 (d : ℕ) : Prop := STStep4R d STAny
def STStep3I (d : ℕ) : Prop := STStep3R d STCaseI
def STStep3II (d : ℕ) : Prop := STStep3R d STCaseII
def STStep4I (d : ℕ) : Prop := STStep4R d STCaseI
def STStep4II (d : ℕ) : Prop := STStep4R d STCaseII

/-- The endpoint `u = t` of `STLmaxU` is the conclusion `STLmax` of `lem:main_ind` at `t`
(DECISIONS §19). -/
theorem STLmax_of_STLmaxU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLmaxU sz E s t) :
    STLmax sz E t := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-- The endpoint `u = t` of `STLKU` is the conclusion `STLK` of `lem:main_ind` at `t`. -/
theorem STLK_of_STLKU {E s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (h : STLKU sz E s t) :
    STLK sz E t := by
  intro k hk
  exact StochDomAt.precomp_param (h k hk)
    (fun n (p : (Fin k → Bool) × (Fin k → Zd d (sz.L n))) => ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))

/-! ## 3. The ingredients: contraction inequality, `lem: newPQ`, `lem:SEforLn`, `lem:STOeq_*`,
`lem:iterations` -/

/-- **The contraction inequality** `(yi2oslxj2)`, `(u2jzooi-2)` of `ygdhmsgq` (`3_5:923`, new in
`d ≥ 3`, no RBM2D source), deterministic for every sample and flow time `τ ∈ [0,1)`, `|E| < 2`
(`η_τ = (1-τ) Im m(E) > 0`): for a loop of length `m ≥ 2`, `1 ≤ k ≤ m-1`,
`Σ_{a_m} |𝓛^{(m)}_{τ,σ,a}| ≤ (W^d η_τ)⁻¹ (max|𝓛^{(2k-1)}| max|𝓛^{(2m-2k-1)}|)^{1/2}`; and for `m ≥ 4`,
`1 ≤ k < j < l ≤ m-1`, `𝒜(a_m) ⊂ Z_L^d` with `|𝒜(a_m)| ≤ C`, `p ≥ 1`:
`Σ_{a_m} Σ_{a_j ∈ 𝒜(a_m)} |𝓛^{(m)}| ≤ C (W^d η_τ)⁻¹ (max|𝓛^{(2k-1)}| max|𝓛^{(2m-2l-1)}|)^{1/2}
(max|𝓛^{(2(l-k)p)}|)^{1/(2p)}` (`max` = `STmaxL`: over all `σ`, `a`). -/
def STContract (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ ω : sz.SeqΩ,
    (∀ (m k : ℕ), 1 ≤ k → k + 1 ≤ m → ∀ (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn a ++ [x]⟩‖ ≤
        (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
          (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * m - 2 * k - 1) ω) ^ (1 / 2 : ℝ)) ∧
    (∀ (m k l p : ℕ) (j : Fin (m - 1)) (C : ℝ), 4 ≤ m → 1 ≤ p → 1 ≤ k → k < j.val + 1 →
      j.val + 1 < l → l + 1 ≤ m → 0 ≤ C → ∀ (𝒜 : Zd d (sz.L n) → Finset (Zd d (sz.L n))),
      (∀ x, ((𝒜 x).card : ℝ) ≤ C) → ∀ (σ : Fin m → Bool) (a : Fin (m - 1) → Zd d (sz.L n)),
      ∑ x : Zd d (sz.L n), ∑ y ∈ 𝒜 x,
          ‖STLI sz n E τ ω ⟨List.ofFn σ, List.ofFn (Function.update a j y) ++ [x]⟩‖ ≤
        C * (((sz.W n : ℕ) : ℝ) ^ d * etaT E τ)⁻¹ *
          (STmaxL sz n E τ (2 * k - 1) ω * STmaxL sz n E τ (2 * m - 2 * l - 1) ω) ^ (1 / 2 : ℝ) *
          STmaxL sz n E τ (2 * (l - k) * p) ω ^ (1 / (2 * (p : ℝ))))

/-- **`lem: newPQ`** (`3_5:1482-1507`, expansions `(yurenAL)`, `(yurenAK)`): for every length `m`,
charges `σ` and subset `A ⊂ ⟦m⟧` there is a family of `O(1)` data `(k_α, ξ_α, σ_α, ι_α, A_α)` (independent
of the sizes, the sample, the labels): `1 ≤ k_α ≤ m-1`, `ξ_α ∈ ℤ`, `σ_α ∈ {±}^{k_α}`, `ι_α : ⟦k_α⟧ → ⟦m⟧` (the
labels `a_α = a ∘ ι_α` are a sub-collection of `a`), `A_α ⊇ I_diff(σ_α)`, with
`(Q^{(A)}∘𝓛^{(m)})_{σ,a} = (Q^{(A_m)}∘𝓛^{(m)})_{σ,a} + Σ_α ξ_α (2 i N η_τ)^{-(m-k_α)}
(Q^{(A_α)}∘𝓛^{(k_α)})_{σ_α,a_α}`, `A_m = A ∪ I_diff(σ)`, `N = (WL)^d`, and the same identity for `𝒦`
(Ward's identities `(WI_calL)` and `(WI_calK)` = merged `KLK_ward`).  `Q^{(A)}` is the merged
`zeroModeSet`. -/
def STNewPQ (d : ℕ) : Prop :=
  ∀ (m : ℕ) (σ : Fin m → Bool) (A : Finset (Fin m)),
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin m) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ m) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (sz : Sizes d) (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz.SeqΩ)
        (a : Fin m → Zd d (sz.L n)),
        (zeroModeSet d (sz.L n) A (fun a' => Lloop sz n E τ σ a' ω) a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => Lloop sz n E τ σ a' ω) a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => Lloop sz n E τ (σ' α) a' ω) (a ∘ ι α)) ∧
        (zeroModeSet d (sz.L n) A (fun a' => STKloop sz n E τ σ a') a =
          zeroModeSet d (sz.L n) (A ∪ STIdiff σ) (fun a' => STKloop sz n E τ σ a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (m - k α)) *
              zeroModeSet d (sz.L n) (A' α) (fun a' => STKloop sz n E τ (σ' α) a') (a ∘ ι α))

/-- The indices `(n₁, n₂)` of `lem:SEforLn` (1) (`3_5:1025`): `(n-1, n+1)` for `n` even, `(n, n)` for `n` odd. -/
def STn12E (n : ℕ) : ℕ × ℕ := if n % 2 = 0 then (n - 1, n + 1) else (n, n)

/-- The indices `(n'₁, n'₂)` below `(eq:L-KsimL-K)` (`3_5:1039`): `(n'-1, n'-1)` for `n'` even,
`(n'-2, n')` for `n'` odd. -/
def STn12 (n' : ℕ) : ℕ × ℕ := if n' % 2 = 0 then (n' - 1, n' - 1) else (n' - 2, n')

/-- **`lem:SEforLn`**, the four estimates of the `ℰ` terms (`3_5:1017-1065`), uniformly in `u ∈ [s,t]`
and in the labels, for every fixed loop length `k ≥ 2` (the paper's `n`) and `p ≥ 1`; the random
control parameters are `Ξ̂`; `η_u = etaT`, `B = W^{-d}B_{u,0}`:
(1) `|ℰ^{G̃,(k)}| ≺ B^k η⁻¹ (Ξ̂^{𝓛}_{n₁} Ξ̂^{𝓛}_{n₂})^{1/2}`;
(2) `3 ≤ l ≤ k`: `|[𝒦^{(l)}∼(𝓛-𝒦)]^{(k)}| ≺ B^k η⁻¹ Ξ̂^{𝓛-𝒦}_{k-l+2}`;
(3) `|ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(k)}| ≺ B^k η⁻¹ (Σ_{n'=⌈k/2⌉+1}^{k-1} Ξ̂^{𝓛-𝒦}_{k+2-n'} (Ξ̂^{𝓛}_{n'₁} Ξ̂^{𝓛}_{n'₂})^{1/2}
+ B^{1/6} Ξ̂^{𝓛-𝒦}_k)`;
(4) `|(ℰ⊗ℰ)^{M,(k)}| ≺ B^{2k-1/(2p)} η⁻¹ Ξ̂^{𝓛}_{2k-1} (Ξ̂^{𝓛}_{4p})^{1/(2p)}`
(the paper's `max` over `O(1)` terms is a sum, and `(ℰ⊗ℰ)^M` is the sum over the `k` cut edges of
`(defEOTE)`: both change the right side by a constant factor). -/
def STSEforLnConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STegt sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (STXiL sz n (E n) (p.1 : ℝ) (STn12E k).1 ω * STXiL sz n (E n) (p.1 : ℝ) (STn12E k).2 ω) ^ (1 / 2 : ℝ)) ∧
    (∀ l : ℕ, 3 ≤ l → l ≤ k →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STksimLK sz n (E n) (p.1 : ℝ) ω l ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
          STXiLK sz n (E n) (p.1 : ℝ) (k - l + 2) ω)) ∧
    Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖STelklk sz n (E n) (p.1 : ℝ) ω ⟨List.ofFn p.2.1, List.ofFn p.2.2⟩‖)
      (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ k / etaT (E n) (p.1 : ℝ) *
        (∑ n' ∈ Finset.Icc ((k + 1) / 2 + 1) (k - 1),
            STXiLK sz n (E n) (p.1 : ℝ) (k + 2 - n') ω *
              (STXiL sz n (E n) (p.1 : ℝ) (STn12 n').1 ω * STXiL sz n (E n) (p.1 : ℝ) (STn12 n').2 ω) ^ (1 / 2 : ℝ) +
          (sz.Bctl n (p.1 : ℝ)) ^ (1 / 6 : ℝ) * STXiLK sz n (E n) (p.1 : ℝ) k ω)) ∧
    (∀ q : ℕ, 1 ≤ q →
      Prec sz (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖STee sz n (E n) (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2‖)
        (fun n p ω => (sz.Bctl n (p.1 : ℝ)) ^ ((2 * k : ℝ) - 1 / (2 * (q : ℝ))) / etaT (E n) (p.1 : ℝ) *
          (STXiL sz n (E n) (p.1 : ℝ) (2 * k - 1) ω * STXiL sz n (E n) (p.1 : ℝ) (4 * q) ω ^ (1 / (2 * (q : ℝ))))))

/-! ### The bootstrap bound `(am;asoi222)` and the iteration -/

/-- The lengths of `Ξ^{𝓛}` that enter `STbootRHS` (and so must be controlled): `m ≤ n_ + 1` (`max_{n'=n-1}^{n+1}`,
`n'₁, n'₂ ≤ n-1`), `m = 2 n_ - 1`, `m = 4 p`; those of `Ξ^{𝓛-𝒦}` are `m ≤ n_ - 1`. -/
def STlenL (n_ p m : ℕ) : Prop := m ≤ n_ + 1 ∨ m = 2 * n_ - 1 ∨ m = 4 * p

/-- `sup_{w ∈ [s,u]} Ξ̂^{𝓛-𝒦}_{w,k}` (a bounded family: the loops are bounded on `[s,u] ⊂ [0,1)`). -/
def STsupXiLK (n : ℕ) (E s u : ℝ) (k : ℕ) (ω : sz.SeqΩ) : ℝ :=
  ⨆ w : Set.Icc s u, STXiLK sz n E (w : ℝ) k ω

/-- The deterministic part of the right side of `(am;asoi222)` (`3_5:1366`) / of `(am;asoiuw)`
(`3_5:1143-1149`): controls `XL m = Ξ^{𝓛}_{·,m}`, `XLK m = Ξ^{𝓛-𝒦}_{·,m}` (constant in `v ∈ [s,u]`, depending on the
endpoint `u`), `B = W^{-d}B_{u,0}`, loop length `n_`, martingale exponent `p`; `lo = 1` for
`lem:STOeq_Qt(_nonzero)` (`max_{n'=1}^{n-1}`), `lo = 2` for `lem:STOeq_NQ` (`max_{n'=2}^{n-1}`).  The paper's
`max` over `O(1)` terms is written as a sum (equivalent for `≺`). -/
def STbootRHS (lo : ℕ) (XL XLK : ℕ → ℝ) (B : ℝ) (n_ p : ℕ) : ℝ :=
  B ^ (-(1 : ℝ) / (4 * (p : ℝ))) * XL (2 * n_ - 1) ^ (1 / 2 : ℝ) * XL (4 * p) ^ (1 / (4 * (p : ℝ))) +
    (∑ m ∈ Finset.Icc lo (n_ - 1), XLK m + ∑ m ∈ Finset.Icc (n_ - 1) (n_ + 1), XL m +
      ∑ m ∈ Finset.Icc ((n_ + 1) / 2 + 1) (n_ - 1),
        XLK (n_ + 2 - m) * (XL (STn12 m).1 * XL (STn12 m).2) ^ (1 / 2 : ℝ))

/-- **`(am;asoi222)`** (`3_5:1366`), the conclusion of `lem:STOeq_Qt` and `lem:STOeq_Qt_nonzero`, uniformly in
`u ∈ [s,t]` and with the supremum over `v ∈ [s,u]` inside `Prec` (the index `(v,u)`): for `n_ ≥ 2`, `p ≥ 1` and
deterministic control parameters `Ξ^{𝓛}_{v,m} = XL m n u`, `Ξ^{𝓛-𝒦}_{v,m} = XLK m n u` (`≥ 1`, constant in `v`,
depending on `u`: the form in which `lem:iterations` and `(saww02)` apply the lemma; the paper allows `v`-dependent
parameters and a `sup_v` on the right, paper-delta candidate `T2041a`) with `Ξ̂ ≺ Ξ` for the lengths `m` that occur:
`sup_{v ∈ [s,u]} Ξ̂^{𝓛-𝒦}_{v,n_} ≺ STbootRHS 1 ...`. -/
def STXiBoot (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 n_ ω)
      (fun n q _ => STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n q.1.2) n_ p)

/-- **`lem:STOeq_NQ`** (`3_5:1136`, bound `(am;asoiuw)` `3_5:1143-1148`): for the non-alternating sign vectors
(`σ_k = σ_{k+1}` for some `k`), uniformly in the endpoint `u`, the loops at `u`:
`max_{σ nal, a} |(𝓛-𝒦)^{(n_)}_{u,σ,a}| / (W^{-d}B_{u,0})^{n_} ≺ B_u^{1/6} sup_{w ∈ [s,u]} Ξ̂^{𝓛-𝒦}_{w,n_} +
STbootRHS 2 ...` (same controls as `STXiBoot`). -/
def STNQConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ n_ p : ℕ, 2 ≤ n_ → 1 ≤ p → ∀ XL XLK : ℕ → ℕ → ℝ → ℝ,
    (∀ m n u, 1 ≤ XL m n u) → (∀ m n u, 1 ≤ XLK m n u) →
    (∀ m, 1 ≤ m → STlenL n_ p m →
      Prec sz (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => XL m n q.1.2)) →
    (∀ m, 1 ≤ m → m + 1 ≤ n_ →
      Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => XLK m n q.1.2)) →
    Prec sz (U := fun n => TimeIcc s t n × {σ : Fin n_ → Bool // ∃ k, σ k = σ (finRotate n_ k)} ×
        (Fin n_ → Zd d (sz.L n)))
      (fun n q ω => ‖Lloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2 ω - STKloop sz n (E n) (q.1 : ℝ) q.2.1.1 q.2.2‖ /
        (sz.Bctl n (q.1 : ℝ)) ^ n_)
      (fun n q ω => (sz.Bctl n (q.1 : ℝ)) ^ (1 / 6 : ℝ) * STsupXiLK sz n (E n) (s n) (q.1 : ℝ) n_ ω +
        STbootRHS 2 (fun m => XL m n (q.1 : ℝ)) (fun m => XLK m n (q.1 : ℝ)) (sz.Bctl n (q.1 : ℝ)) n_ p)

/-- A Step-3 ingredient pin: the setting of `lem:main_ind` (constants first, `𝔠_d` after `C_d`), a regime `R`,
the hypotheses `(a)` at `s`, `(con_st_ind)`, the conclusions of Step 2, `ML:Kbound`, `(wardineq_K)`; the
conclusion is the statement `Concl` about `(E, s, t)`. -/
def STIngR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep2Concl sz (STflowE z) s t Cd → Concl sz (STflowE z) s t

/-- `lem:SEforLn` (the setting of `lem:main_ind`; any regime). -/
def STSEforLn (d : ℕ) : Prop := STIngR d STAny (fun sz E s t => STSEforLnConcl sz E s t)

/-- `lem:STOeq_NQ` (`3_5:1136`): case (i). -/
def STOeqNQ (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STNQConcl sz E s t)

/-- `lem:STOeq_Qt` (`3_5:1362`): case (i), `1 - t ≥ ilambda²/L²`. -/
def STOeqQt (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STXiBoot sz E s t)

/-- `lem:STOeq_Qt_nonzero` (`3_5:1561`): case (ii), `1 - s ≤ ilambda²/L²`: the same bound `(am;asoi222)`. -/
def STOeqQtNZ (d : ℕ) : Prop := STIngR d STCaseII (fun sz E s t => STXiBoot sz E s t)

/-- `(eq:iteration_induc)` at `(r,l)` (`3_5:1410`): `sup_{v ∈ [s,u]} Ξ̂^{𝓛-𝒦}_{v,r} ≺ Ψ(r,l;s,u)`, uniformly in
`u ∈ [s,t]`, with `Ψ` built from the parameter `A`. -/
def STIterHyp (E s t : ℕ → ℝ) (A : ℕ → ℝ) (r l : ℕ) : Prop :=
  Prec sz (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 r ω)
    (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) r l)

/-- **`lem:iterations`** (`3_5:1407-1417`) and its case-`(ii)` analogue (`3_5:1575-1595`; "we omit the details", `3_5:1594`):
under the setting, `(lRB1)`, the Step-2 conclusions and `(am;asoi222)` (`STXiBoot`), with `1 - s ≤ ilambda²` and
`1 - t ≥ ilambda²/L²` (case (i), `A = ilambda² W^d`) resp. `1 - s ≤ ilambda²/L²` (case (ii), `A = (W^{-d}B_{s,0})⁻¹`):
if `(eq:iteration_induc)` holds at `(r,k)`, `2 ≤ r ≤ n_-1`, and at `(r,k-1)`, `2 ≤ r ≤ n_+2`, then at `(n_,k)`;
`n_ ≥ 2`, `k ≥ 1`. -/
def STIterR (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STLK sz (STflowE z) s → STConStInd sz 𝔠d s t →
          STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
          STXiBoot sz (STflowE z) s t →
          ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
            (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) →
            (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t (Aof sz s) r (k - 1)) →
            STIterHyp sz (STflowE z) s t (Aof sz s) n_ k

/-- Regime of `lem:iterations`, case (i): `1 - s ≤ ilambda²` and `1 - t ≥ ilambda²/L²`. -/
def STRegIterI {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  STCaseI sz s t ∧ ∀ n, 1 - s n ≤ sz.lam n ^ 2

/-- `lem:iterations`, case (i) (`A = ilambda² W^d`, `Ψ` of `(adsyzz0s8d6)`). -/
def STIterations (d : ℕ) : Prop := STIterR d STRegIterI (fun sz _ n => STAI sz n)

/-- The case-(ii) analogue (`A = (W^{-d}B_{s,0})⁻¹`, `Ψ` of `(eq:psipara_smalletacase)`). -/
def STIterationsII (d : ℕ) : Prop := STIterR d STCaseII (fun sz s n => STAII sz s n)

/-! ### The mollifier `ϑ`, the bounds on `𝒬_t`, `(eq:Ward_typeP)` and `ℬ₄, ℬ₅` -/

/-- **The mollifier `ϑ^{(n)}_{t,a}`** of `Def:QtPt` (`3_5:1217-1229`) for tensors of `m + 1` indices: `Σ_{a₂..a_n}
ϑ_{t,a} = 1` (`(eq:suma1chi)`), `|ϑ_{t,a}| ≤ C (ℓ_t^d)^{-m} exp(-c Σ_{i≥2} |a_i - a₁| / ℓ_t)` and
`|∂_tϑ_{t,a}| ≤ C (1-t)⁻¹ (ℓ_t^d)^{-m}` (`(eq:derv_Theta)`), differentiable in `t ∈ [0,1)` (the paper's `∂_t` needs it:
`ℓ_t = min(max(g/√(1-t),1),L)` has kinks, so the bump of `rmk:choosechi` needs a smoothed scale; paper-delta candidate
`T2041b`).  The RBM2D choice `ϑ = (1-t)^{m} Π Θ_t(a₁,a_i)` (`HierVocab.lean:66`) violates the first bound at `d ≥ 3`:
`(1-t)Θ_t(a,a) ≍ ℓ_t^{-2}` against `ℓ_t^{-d}`. -/
def STMollifierProps {m L : ℕ} [NeZero L] (g C c : ℝ) (ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ) : Prop :=
  (∀ t a₁, ∑ a ∈ Finset.univ.filter (fun a : Fin (m + 1) → Zd d L => a 0 = a₁), ϑ t a = 1) ∧
  (∀ t, 0 ≤ t → t < 1 → ∀ a, ‖ϑ t a‖ ≤ C * (((ellT L g t) ^ d)⁻¹) ^ m *
      Real.exp (-c * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)), (zdistD d L (a i - a 0) : ℝ)) / ellT L g t)) ∧
  (∀ a, DifferentiableOn ℝ (fun t => ϑ t a) (Set.Ico 0 1)) ∧
  (∀ t, 0 ≤ t → t < 1 → ∀ a, ‖deriv (fun τ => ϑ τ a) t‖ ≤ C * (1 - t)⁻¹ * (((ellT L g t) ^ d)⁻¹) ^ m)

/-- **Existence of the mollifier** (`rmk:choosechi`, `3_5:1250`): constants `C, c` depend on `(d, m, Λ)` only. -/
def STMollifierEx (d : ℕ) : Prop :=
  3 ≤ d → ∀ (m : ℕ) (Λ : ℝ), 0 < Λ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      haveI : NeZero L := ⟨by omega⟩
      ∃ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ

/-- **`lem_+Q`**, `(normQA)` (`3_5:1285-1289`): for `(t, ε, D)`-decaying tensors (`EKFastDecay`),
`‖𝒬_t 𝒜‖_∞ ≤ W^{C_n ε} ‖𝒜‖_∞ + W^{-D+C_n}`, `C_n` independent of `ε, D`: it depends on `(d, m, Λ, K)` and the mollifier
constants `C, c`.  The hypothesis `L^d ≤ W^K` is the one of `EKSumDecay2` (DECISIONS §21, T2042a): the far part of
`𝒫 𝒜` has `L^{d m}` terms of size `W^{-D}`; `4 ≤ W^ε` absorbs the constant `C` of the mollifier into `W^{C_n ε}`. -/
def STQopNorm (d : ℕ) : Prop :=
  3 ≤ d → ∀ (m : ℕ) (Λ K C c : ℝ), 0 < Λ → 0 < K → 0 < C → 0 < c →
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ →
      ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → (L : ℝ) ^ d ≤ W ^ K →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ, STMollifierProps (d := d) g C c ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ 𝒜 : (Fin (m + 1) → Zd d L) → ℂ, EKFastDecay g t W ε D 𝒜 →
        ‖STQop (d := d) ϑ t 𝒜‖ ≤ W ^ (Cn * ε) * ‖𝒜‖ + W ^ (-D + Cn)

/-- `(L - K)^{(m+1)}_{u,σ}` as a tensor of `m + 1` indices (the argument of `𝒫`, `𝒬_u`). -/
def STLKtensor (n : ℕ) (E u : ℝ) (ω : sz.SeqΩ) {m : ℕ} (σ : Fin (m + 1) → Bool) :
    (Fin (m + 1) → Zd d (sz.L n)) → ℂ :=
  fun a => Lloop sz n E u σ a ω - STKloop sz n E u σ a

/-- The alternating sign vectors: `σ_k = -σ_{k+1}` for all `k` (`(NALsig_diff)`, `3_5:1199`). -/
def STAlternating {k : ℕ} (σ : Fin k → Bool) : Prop := ∀ i, σ (finRotate k i) ≠ σ i

/-- **`(eq:Ward_typeP)`** (`3_5:1264`, `jywiiwsoks` `3_5:1271`), alternating `σ`, uniformly in `u ∈ [s,t]`, case (i):
`[𝒫∘(𝓛-𝒦)^{(m+1)}_{u,σ}]_{a₁} ϑ_{u,a} ≺ (W^{-d}B_{u,0})^{m+1} Ξ^{𝓛-𝒦}_{u,m}` for a deterministic `Ξ^{𝓛-𝒦}_{u,m} = X n u`
(`Ξ̂ ≺ Ξ`) and any mollifier family with constants `C, c`.  Proof: Ward `(WI_calK)`, fast decay, `(ℓ^d η)⁻¹ ≲ B_{u,0}`
(`3_5:1264`: needs `1 - u ≥ ilambda²/L²`). -/
def STWardTypeP (E s t : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (C c : ℝ), 1 ≤ m →
    ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) →
      Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) →
      Prec sz (U := fun n => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n)))
        (fun n q ω => ‖STPsum (d := d) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) * ϑ n (q.1 : ℝ) q.2.2‖)
        (fun n q _ => (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))

/-- **`(y27kasdfg)`** (`3_5:1692`): for alternating `σ` and `ℬ₄ = [𝒬_u, Θ^{(m+1)}_{u,σ}] ∘ (𝓛-𝒦)_{u,σ}`,
`ℬ₅ = -[𝒫∘(𝓛-𝒦)_{u,σ}] ∂_uϑ_u`: `‖ℬ₄(u)‖_∞ + ‖ℬ₅(u)‖_∞ ≺ η_u⁻¹ (W^{-d}B_{u,0})^{m+1} Ξ^{𝓛-𝒦}_{u,m}` (same controls). -/
def STB45 (E s t : ℕ → ℝ) : Prop :=
  ∀ (m : ℕ) (C c : ℝ), 1 ≤ m →
    ∀ ϑ : (∀ n : ℕ, ℝ → (Fin (m + 1) → Zd d (sz.L n)) → ℂ), (∀ n, STMollifierProps (d := d) (sz.lam n) C c (ϑ n)) →
    ∀ X : ℕ → ℝ → ℝ, (∀ n u, 1 ≤ X n u) →
      Prec sz (U := fun n => TimeIcc s t n) (fun n u ω => STXiLK sz n (E n) (u : ℝ) m ω) (fun n u _ => X n (u : ℝ)) →
      Prec sz (U := fun n => TimeIcc s t n × {σ : Fin (m + 1) → Bool // STAlternating σ} × (Fin (m + 1) → Zd d (sz.L n)))
        (fun n q ω =>
          ‖(STQop (d := d) (ϑ n) (q.1 : ℝ)
              (ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) q.2.1.1) (q.1 : ℝ)
                (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1)) -
            ThetaN d (sz.L n) (sz.lam n) (EKsgn (mE (E n)) q.2.1.1) (q.1 : ℝ)
              (STQop (d := d) (ϑ n) (q.1 : ℝ) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1))) q.2.2‖ +
          ‖STPsum (d := d) (STLKtensor sz n (E n) (q.1 : ℝ) ω q.2.1.1) (q.2.2 0) *
              deriv (fun τ => ϑ n τ q.2.2) (q.1 : ℝ)‖)
        (fun n q _ => (etaT (E n) (q.1 : ℝ))⁻¹ * (sz.Bctl n (q.1 : ℝ)) ^ (m + 1) * X n (q.1 : ℝ))

/-- `(eq:Ward_typeP)`: case (i). -/
def STWardTypePPin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STWardTypeP sz E s t)

/-- `(y27kasdfg)`: case (i). -/
def STB45Pin (d : ℕ) : Prop := STIngR d STCaseI (fun sz E s t => STB45 sz E s t)

/-! ## 4. The consumer form of the evolution-kernel pins (for EK-6)

Steps 3-4 use, in `3_5:900-1934`, only `(sum_res_2_NAL)` (`3_5:1153-1166`, `lem:STOeq_NQ`), `(sum_res_2)`
(`3_5:1681-1716`, `lem:STOeq_Qt`) and `lem:sum_decay_nonzero` (`3_5:1557-1559`, `lem:STOeq_Qt_nonzero`); `(sum_res_1)`,
`lem:propT`, `claim:TTk`, `(eq:latticesum_d3)` do not occur there (script, report b.6).  The kernel is applied
sample by sample to a random tensor family `𝒜_v(ω)`, `v ∈ [s_n,t_n]` (the integrand of the Duhamel formula at the
time `v`), with the decay property `(deccA0)` w.h.p. for every `ε, D` and a control `X ≥ N^{-b}` w.h.p.; the output
is `‖U_{v,t,σ} ∘ 𝒜_v‖_∞ ≺ (ratio)^{·} X`, uniformly in `v`, at the scale `N = sz.size n`.  EK-6 derives each
form from the merged pin: `W^{Cε} ≤ N^{τ}` (`W ≤ N^{1/d}`, `ε = τ d / (4 C)`), `W^{-D+C} ≤ N^{-b'}`
(`W ≥ N^𝔠`), `4 ≤ W^ε` and `log L ≤ W^ε` eventually (`W ≥ N^𝔠 → ∞`), `L^d ≤ N ≤ W^{1/𝔠}` (`K = 1/𝔠`,
DECISIONS §21), `g ≤ Λ = 𝔡⁻¹` from `(eq:WO)`. -/

/-- `(deccA0)` w.h.p. for every `ε, D > 0`, at the kernel start time `v` (`Def_decay`, `lem_decayLoop`). -/
def STEKDecay {m : ℕ} (s t : ℕ → ℝ)
    (𝒜 : ∀ n, TimeIcc s t n → sz.SeqΩ → (Fin m → Zd d (sz.L n)) → ℂ) : Prop :=
  ∀ ε D : ℝ, 0 < ε → 0 < D →
    Whp sz (fun n => {ω | ∀ v : TimeIcc s t n,
      EKFastDecay (sz.lam n) (v : ℝ) ((sz.W n : ℕ) : ℝ) ε D (𝒜 n v ω)})

/-- The control is polynomially bounded below, w.h.p.: `X ≥ N^{-b}` for some `b`. -/
def STEKLow (s t : ℕ → ℝ) (X : ∀ n, TimeIcc s t n → sz.SeqΩ → ℝ) : Prop :=
  ∃ b : ℝ, Whp sz (fun n => {ω | ∀ v : TimeIcc s t n, ((sz.size n : ℕ) : ℝ) ^ (-b) ≤ X n v ω})

/-- The window of `lem:sum_decay` (`3_5:1633`): `0 ≤ s ≤ t ≤ 1 - ilambda²/L²` (case (i)) and `(1-t)/(1-s) ≥ W⁻¹`,
the latter eventually (it follows from `(con_st_ind)` when `d 𝔠_d < 1`, report (a) F1). -/
def STEKWin (s t : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ s n) ∧ (∀ n, s n ≤ t n) ∧ (∀ n, t n ≤ 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) ∧
    (∀ n, t n < 1) ∧ ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ)⁻¹ ≤ (1 - t n) / (1 - s n)

/-- **`lem:sum_Ndecay`** `(sum_res_Ndecay)` (`3_5:1620`) at scale `N`: `‖U_{v,t,σ}∘𝒜_v‖ ≺ ((1-v)/(1-t))^{n} X` from
`‖𝒜_v‖ ≺ X`, for `0 ≤ s ≤ t < 1`, any charges `m` with `|m| = 1`, any sign vector. -/
def STEKSumNdecay (d : ℕ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ),
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v ω, 0 ≤ X n v ω) →
      Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((1 - (v : ℝ)) / (1 - t n)) ^ n_ * X n v ω)

/-- **`(sum_res_1)`** (`3_5:1639`) at scale `N` (any `σ`; not consumed by Steps 3-4): `≺ (ℓ_t²/ℓ_s²)·ratio^{n}`. -/
def STEKSumRes1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X →
      Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => (ellT (sz.L n) (sz.lam n) (t n) ^ 2 / ellT (sz.L n) (sz.lam n) (v : ℝ) ^ 2) *
          ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)

/-- **`(sum_res_2_NAL)`** (`3_5:1649`) at scale `N`, `σ` non-alternating, bulk `κ ≤ Im m`: `≺ ratio^{n-1} X`. -/
def STEKSumRes2NAL (d : ℕ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → (∀ n, κ ≤ (m n).im) →
    ∀ σ : Fin n_ → Bool, (∃ k, σ k = σ (finRotate n_ k)) →
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X →
      Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ (n_ - 1) * X n v ω)

/-- **`(sum_res_2)`** (`3_5:1659`) at scale `N` for sum-zero tensors (`(sumAzero)`, surely), any `σ`, bulk `κ ≤ Im m`:
`≺ ratio^{n} X`; the pin `EKSumDecay2` carries `log L ≤ W^ε` and `L^d ≤ W^K` (T2016a, T2042a), both eventual here
(`K = 1/𝔠`). -/
def STEKSumRes2 (d : ℕ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, STEKWin sz s t → ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → (∀ n, κ ≤ (m n).im) →
    ∀ σ : Fin n_ → Bool,
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ), STEKDecay sz s t 𝒜 →
    (∀ n v ω, EKSumZero (𝒜 n v ω)) →
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), STEKLow sz s t X →
      Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω)‖)
        (fun n v ω => ((sz.lam n ^ 2 + |1 - (v : ℝ)|) / (sz.lam n ^ 2 + |1 - t n|)) ^ n_ * X n v ω)

/-- **`lem:sum_decay_nonzero`** (`3_5:1666`) at scale `N`, case (ii) `1 - ilambda²/L² ≤ s ≤ t < 1`, `A ⊇ I_diff(σ)`,
bulk `κ ≤ Im m` (both charges): `‖Q^{(A)}∘U_{v,t,σ}∘𝒜_v‖_∞ ≺ X` from `‖𝒜_v‖_∞ ≺ X` (no decay hypothesis).
The window carries `0 ≤ s` (DECISIONS §27, T2053 Amend 1): without it `ilambda > L` lets `[s,t]` reach negative times. -/
def STEKNonzero (d : ℕ) : Prop :=
  3 ≤ d → ∀ n_ : ℕ, 2 ≤ n_ → ∀ κ 𝔠 𝔡 : ℝ, 0 < κ → ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 →
    ∀ s t : ℕ → ℝ, (∀ n, 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ s n) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
    ∀ m : ℕ → ℂ, (∀ n, ‖m n‖ = 1) → (∀ n, κ ≤ (m n).im) →
    ∀ σ : Fin n_ → Bool, ∀ A : Finset (Fin n_), (∀ i, σ i ≠ σ (finRotate n_ i) → i ∈ A) →
    ∀ 𝒜 : (∀ n, TimeIcc s t n → sz.SeqΩ → (Fin n_ → Zd d (sz.L n)) → ℂ),
    ∀ X : (∀ n, TimeIcc s t n → sz.SeqΩ → ℝ), (∀ n v ω, 0 ≤ X n v ω) →
      Prec sz (U := fun n => TimeIcc s t n) (fun n v ω => ‖𝒜 n v ω‖) X →
      Prec sz (U := fun n => TimeIcc s t n)
        (fun n v ω => ‖zeroModeSet d (sz.L n) A
          (UN d (sz.L n) (sz.lam n) (EKsgn (m n) σ) (v : ℝ) (t n) (𝒜 n v ω))‖) X


/-- `W^{-d} B_{u,0} > 0` for `u < 1` (the first term `(ilambda² + 1 - u)⁻¹` is positive). -/
theorem st_Bctl_pos {n : ℕ} {u : ℝ} (hu : u < 1) : 0 < sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have h1 : 0 < |1 - u| := abs_pos.2 (by linarith)
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
  have h2 : 0 < (sz.lam n ^ 2 + |1 - u|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have h3 : 0 < (((sz.L n : ℕ) : ℝ) ^ d * |1 - u|)⁻¹ := by positivity
  positivity

end RBM.Gauss.Sizes

/-! ## 7. Instances at `d = 3`

Two concrete size sequences, both nondegenerate (`N → ∞`, `d = 3`, `L ≥ 3`, `W ≥ 32` resp. `W ≥ 4`):
* `sz0` (merged, `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6} → 0`, flow `z0`, `s ≡ 0`, `t ≡ 1/16`):
  case (i): `ilambda²/L² ≤ 15/16`;
* `szB` (new: `L = 4`, `W_n = n + 4`, `ilambda = 1`, flow `zB = 1/2 + i/64`, `lemT zB ≥ 31/32`): constant times in every regime,
  `ilambda²/L² = 1/16`: case (ii) `(s,t) = (15/16, 31/32)` (`1 - s = ilambda²/L²`, `1 - t = ilambda²/(2L²)`, the intermediate
  regime `ilambda²/L^3 = 1/64 ≤ 1 - t ≤ ilambda²/L²`), and `lem:iterations` case (i) `(s,t) = (7/8, 15/16)`
  (`1 - s = 1/8 ≤ ilambda²`, `1 - t = ilambda²/L²`).
What stays a hypothesis of an instance is a stochastic premise (`STKbound`, `STKward`, `(a)`, `(lRB1)`, the Step-2
conclusions, `STXiBoot`), as in `RBM.Gauss.InductionDefsInst`. -/

namespace RBM.Gauss.Step34Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Path Filter

/-- The second size sequence: `L = 4`, `W_n = n + 4`, `ilambda = 1`. -/
def szB : Sizes 3 where
  L := fun _ => 4
  W := fun n => n + 4
  lam := fun _ => 1
  three_le_L := fun _ => by norm_num
  W_pos := fun n => by omega

theorem szB_W_tendsto : Tendsto (fun n : ℕ => ((szB.W n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  change (n : ℝ) ≤ ((n + 4 : ℕ) : ℝ)
  exact_mod_cast Nat.le_add_right n 4

theorem szB_size (n : ℕ) : szB.size n = (4 * (n + 4)) ^ 3 := by
  simp [Sizes.size, szB, mul_comm]

theorem szB_size_ge (n : ℕ) : 4096 ≤ szB.size n := by
  rw [szB_size]
  calc 4096 = 16 ^ 3 := by norm_num
    _ ≤ (4 * (n + 4)) ^ 3 := Nat.pow_le_pow_left (by omega) 3

theorem szB_tendsto : szB.SizeTendsto := by
  refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
  have : n ≤ szB.size n := by
    rw [szB_size]
    calc n ≤ 4 * (n + 4) := by omega
      _ ≤ (4 * (n + 4)) ^ 3 := Nat.le_self_pow (by norm_num) _
  exact_mod_cast this

theorem szB_bandwidth : szB.Bandwidth (1 / 6) := by
  refine Eventually.of_forall fun n => ?_
  have h : ((szB.size n : ℕ) : ℝ) ≤ ((szB.W n : ℕ) : ℝ) ^ 6 := by
    have : szB.size n ≤ (szB.W n) ^ 6 := by
      rw [szB_size]
      change (4 * (n + 4)) ^ 3 ≤ (n + 4) ^ 6
      have h4 : 4 * (n + 4) ≤ (n + 4) ^ 2 := by nlinarith
      calc (4 * (n + 4)) ^ 3 ≤ ((n + 4) ^ 2) ^ 3 := Nat.pow_le_pow_left h4 3
        _ = (n + 4) ^ 6 := by ring
    exact_mod_cast this
  calc ((szB.size n : ℕ) : ℝ) ^ (1 / 6 : ℝ)
      ≤ (((szB.W n : ℕ) : ℝ) ^ 6) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) h (by norm_num)
    _ = (szB.W n : ℝ) := by
        rw [show (1 / 6 : ℝ) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (Nat.cast_nonneg _) (by norm_num)

theorem szB_WO : szB.WO (1 / 10) := by
  refine Eventually.of_forall fun n => ⟨?_, by norm_num [szB]⟩
  have hW : (1 : ℝ) ≤ ((szB.W n : ℕ) : ℝ) := by
    change (1 : ℝ) ≤ ((n + 4 : ℕ) : ℝ)
    exact_mod_cast (by omega : 1 ≤ n + 4)
  exact (Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)).trans (by simp [szB])

theorem szB_admissible : szB.Admissible (1 / 6) (1 / 10) :=
  ⟨by norm_num, by norm_num, szB_tendsto, szB_bandwidth, szB_WO⟩

/-- The flow points `z_n = 1/2 + i/64` of the second family. -/
def zB (_n : ℕ) : ℂ := ⟨1 / 2, 1 / 64⟩

theorem zB_locDomain (n : ℕ) : szB.locDomain (1 / 10) (1 / 10) n (zB n) := by
  have hN : (4096 : ℝ) ≤ ((szB.size n : ℕ) : ℝ) := by exact_mod_cast szB_size_ge n
  refine ⟨?_, ?_, ?_⟩
  · simp only [zB, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]; norm_num
  · change ((szB.size n : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) ≤ 1 / 64
    calc ((szB.size n : ℕ) : ℝ) ^ (-1 + 1 / 10 : ℝ) ≤ (4096 : ℝ) ^ (-1 + 1 / 10 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by norm_num)
      _ ≤ 1 / 64 := by
          have h1 : (64 : ℝ) ≤ (4096 : ℝ) ^ (9 / 10 : ℝ) := by
            calc (64 : ℝ) = (4096 : ℝ) ^ (1 / 2 : ℝ) := by
                  rw [← Real.sqrt_eq_rpow]; rw [show (4096 : ℝ) = 64 ^ 2 by norm_num]
                  exact (Real.sqrt_sq (by norm_num)).symm
              _ ≤ (4096 : ℝ) ^ (9 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rw [show (-1 + 1 / 10 : ℝ) = -(9 / 10 : ℝ) by norm_num, Real.rpow_neg (by norm_num)]
          calc ((4096 : ℝ) ^ (9 / 10 : ℝ))⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
            _ = 1 / 64 := by norm_num
  · simp only [zB]; norm_num

theorem flow_zB : STFlow szB (1 / 10) (1 / 10) (1 / 6) (1 / 10) zB := ⟨szB_admissible, zB_locDomain⟩

/-- `lemT zB ≥ 31/32`: `(1 - t₀) Im m(E) = √t₀ Im z` (merged `zt_im_lemma28`), `Im m(E) ≥ 1/2` for `|E| ≤ |Re z| = 1/2`,
`Im z = 1/64`. -/
theorem lemT_zB (n : ℕ) : (31 / 32 : ℝ) ≤ lemT (zB n) := by
  have hz : 0 < (zB n).im := by simp [zB]
  have h1 := zt_im_lemma28 hz
  rw [zt_im] at h1
  have hE : |lemE (zB n)| ≤ 1 / 2 := (abs_lemE_le hz).trans (by simp [zB])
  have hE2 : (lemE (zB n)) ^ 2 ≤ 1 / 4 := by
    have := abs_le.1 hE
    nlinarith [this.1, this.2]
  have hmE : (1 / 2 : ℝ) ≤ (mE (lemE (zB n))).im := by
    rw [mE_im]
    have h4 : (1 : ℝ) ≤ Real.sqrt (4 - (lemE (zB n)) ^ 2) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hT := lemT_lt_one hz
  have hsq : Real.sqrt (lemT (zB n)) ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT.le
  have him : (zB n).im = 1 / 64 := by simp [zB]
  rw [him] at h1
  have h2 : (1 - lemT (zB n)) * (1 / 2) ≤ (1 - lemT (zB n)) * (mE (lemE (zB n))).im :=
    mul_le_mul_of_nonneg_left hmE (by linarith)
  have h3 : Real.sqrt (lemT (zB n)) * (1 / 64) ≤ 1 / 64 := by nlinarith
  linarith

/-- `W^{-3} B_{c,0} → 0` for a constant time `c < 1` (any size data at `d = 3` with `W → ∞`). -/
theorem Bctl_tendsto_const (sz : Sizes 3)
    (hWt : Tendsto (fun n : ℕ => ((sz.W n : ℕ) : ℝ)) atTop atTop) {c : ℝ} (hc : c < 1) :
    Tendsto (fun n => sz.Bctl n c) atTop (nhds 0) := by
  have hW : Tendsto (fun n : ℕ => (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp hWt)
  have hup : Tendsto (fun n : ℕ => 2 * (1 - c)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) := by
    simpa using hW.const_mul (2 * (1 - c)⁻¹)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => (st_Bctl_pos sz hc).le) (fun n => Bctl_const_le_gen sz n hc)

/-- `(con_st_ind)` for constant times `s₀ < t₀ < 1`, every `𝔠_d > 0`. -/
theorem conStInd_const (sz : Sizes 3)
    (hWt : Tendsto (fun n : ℕ => ((sz.W n : ℕ) : ℝ)) atTop atTop) {s0 t0 : ℝ} (hst : s0 < t0)
    (ht : t0 < 1) {𝔠d : ℝ} (h𝔠 : 0 < 𝔠d) : STConStInd sz 𝔠d (fun _ => s0) (fun _ => t0) := by
  have h0 := (Bctl_tendsto_const sz hWt ht).rpow_const (Or.inr h𝔠.le)
  rw [Real.zero_rpow h𝔠.ne'] at h0
  have hr : 0 < (1 - t0) / (1 - s0) := div_pos (by linarith) (by linarith)
  filter_upwards [h0.eventually (gt_mem_nhds hr)] with n hn
  exact ⟨hn.le, (div_lt_one (by linarith)).2 (by linarith)⟩

theorem szB_caseI : STCaseI szB (fun _ => 0) (fun _ => 1 / 16) := fun n => by
  simp [szB]; norm_num

theorem szB_caseII : STCaseII szB (fun _ => 15 / 16) (fun _ => 31 / 32) := fun n => by
  simp [szB]; norm_num

theorem szB_regIterI : STRegIterI szB (fun _ => 7 / 8) (fun _ => 15 / 16) :=
  ⟨fun n => by simp [szB]; norm_num, fun n => by simp [szB]; norm_num⟩

theorem sz0_caseI : STCaseI sz0 sInst tInst := by
  intro n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hl0 : 0 ≤ sz0.lam n := by
    change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
    positivity
  have hl : sz0.lam n ≤ 1 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hL : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    change (4 : ℝ) ≤ ((4 * (n + 1) : ℕ) : ℝ)
    push_cast; linarith
  have h2 : sz0.lam n ^ 2 ≤ 1 := by nlinarith
  have h3 : (16 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 2 := by nlinarith
  change sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 - 1 / 16
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- The result of applying an ingredient pin `STIngR` at the data `(sz, z, s, t)`: the constant `𝔠_d`, then the stochastic
premises, then the conclusion. -/
def InstIngConcl (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (sz : Sizes 3)
    (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s →
      STStep2Concl sz (STflowE z) s t Cd → Concl sz (STflowE z) s t)

/-- The result of applying `STStep3R` at the data. -/
def InstStep3Concl (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s →
      STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t)

/-- The result of applying `STStep4R` at the data. -/
def InstStep4Concl (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound sz (STflowE z) → STKward sz (STflowE z) → STLK sz (STflowE z) s →
      STStep1Loop sz (STflowE z) s t → STStep2Concl sz (STflowE z) s t Cd →
      STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t)

/-- The result of applying `STIterR` at the data. -/
def InstIterConcl (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (Cd : ℝ) : Prop :=
  ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STKbound sz (STflowE z) → STLK sz (STflowE z) s → STStep1Loop sz (STflowE z) s t →
      STStep2Concl sz (STflowE z) s t Cd → STXiBoot sz (STflowE z) s t →
      ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
        (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHyp sz (STflowE z) s t (Aof sz s) r k) →
        (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHyp sz (STflowE z) s t (Aof sz s) r (k - 1)) →
        STIterHyp sz (STflowE z) s t (Aof sz s) n_ k)

/-- The common shape of the instances of the ingredient pins `STIngR`: the constant `𝔠_d` of the pin, then
deterministic data `(sz, z, s, t)` with the regime `R` and `(con_st_ind)`; the stochastic premises stay hypotheses. -/
theorem inst_ing (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STIngR 3 R Concl)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl Concl sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hKw ha h2 => H (1 / 6) sz z hflow s t hs0 hst ht hR hK hKw ha (hcon 𝔠d h0) h2⟩

/-- The same for `lem:iterations` (`STIterR`). -/
theorem inst_iter (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Aof : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → ℕ → ℝ) (h : STIterR 3 R Aof)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIterConcl Aof sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK ha h1' h2 hB => H (1 / 6) sz z hflow s t hs0 hst ht hR hK ha (hcon 𝔠d h0) h1' h2 hB⟩

/-- The same for `STStep3R` (`(lRB1)` is a hypothesis of Step 3). -/
theorem inst_step3R (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STStep3R 3 R)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hKw ha h1' h2 =>
    H (1 / 6) sz z hflow s t hs0 hst ht hR hK hKw ha (hcon 𝔠d h0) h1' h2⟩

/-- The same for `STStep4R` (the conclusion of Step 3 is a hypothesis). -/
theorem inst_step4R (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) (h : STStep4R 3 R)
    (sz : Sizes 3) (z : ℕ → ℂ) (hflow : STFlow sz (1 / 10) (1 / 10) (1 / 6) (1 / 10) z)
    (s t : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n) (ht : ∀ n, t n ≤ lemT (z n))
    (hR : R sz s t) (hcon : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl sz z s t Cd := by
  obtain ⟨𝔠d, h0, h1, H⟩ := h (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hKw ha h1' h2 h3 =>
    H (1 / 6) sz z hflow s t hs0 hst ht hR hK hKw ha (hcon 𝔠d h0) h1' h2 h3⟩

/-! ### The instances of the pins.  Data: `sz0, z0, s ≡ 0, t ≡ 1/16` (general, case (i)); `szB, zB` with the constant times
of the regime. -/

theorem sz0_hs0 : ∀ n, 0 ≤ sInst n := fun _ => le_rfl
theorem sz0_hst : ∀ n, sInst n < tInst n := fun n => by simp only [sInst, tInst]; norm_num
theorem sz0_ht : ∀ n, tInst n ≤ lemT (z0 n) := fun n => sixteenth_le_lemT n
theorem sz0_con : ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz0 𝔠d sInst tInst := fun _ h => conStInd_inst h

theorem szB_flow_ht {t0 : ℝ} (h : t0 ≤ 31 / 32) (n : ℕ) : t0 ≤ lemT (zB n) := h.trans (lemT_zB n)

/-- **Step 3**, general statement, at `(sz0, z0, 0, 1/16)`. -/
theorem inst_step3 (h : STStep3 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz0 z0 sInst tInst Cd :=
  inst_step3R STAny h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial sz0_con Cd hCd

/-- **Step 3**, case (i), at `(sz0, z0, 0, 1/16)`. -/
theorem inst_step3I (h : STStep3I 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl sz0 z0 sInst tInst Cd :=
  inst_step3R STCaseI h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con Cd hCd

/-- **Step 3**, case (ii), at `(szB, zB, 15/16, 31/32)`: `1 - s = ilambda²/L²`, `1 - t = ilambda²/(2 L²)`. -/
theorem inst_step3II (h : STStep3II 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep3Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step3R STCaseII h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

theorem inst_step4 (h : STStep4 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl sz0 z0 sInst tInst Cd :=
  inst_step4R STAny h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht trivial sz0_con Cd hCd

theorem inst_step4I (h : STStep4I 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl sz0 z0 sInst tInst Cd :=
  inst_step4R STCaseI h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst sz0_ht sz0_caseI sz0_con Cd hCd

theorem inst_step4II (h : STStep4II 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstStep4Concl szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_step4R STCaseII h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num)
    (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

/-- The bridge `STLmax_of_STLmaxU` at `(sz0, z0, 0, 1/16)`; `hst` from `sz0_hst`, the owed `STLmaxU` stays a premise. -/
example (h : STLmaxU sz0 (STflowE z0) sInst tInst) : STLmax sz0 (STflowE z0) tInst :=
  STLmax_of_STLmaxU sz0 (fun n => (sz0_hst n).le) h

/-- The bridge `STLK_of_STLKU` at `(sz0, z0, 0, 1/16)`; `hst` from `sz0_hst`, the owed `STLKU` stays a premise. -/
example (h : STLKU sz0 (STflowE z0) sInst tInst) : STLK sz0 (STflowE z0) tInst :=
  STLK_of_STLKU sz0 (fun n => (sz0_hst n).le) h

/-- `lem:SEforLn` at `(sz0, z0, 0, 1/16)`. -/
theorem inst_SEforLn (h : STSEforLn 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STSEforLnConcl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STAny (fun sz E s t => STSEforLnConcl sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht trivial sz0_con Cd hCd

/-- `lem:STOeq_NQ` (case (i)) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_OeqNQ (h : STOeqNQ 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STNQConcl sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STCaseI (fun sz E s t => STNQConcl sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht sz0_caseI sz0_con Cd hCd

/-- `lem:STOeq_Qt` (case (i)) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_OeqQt (h : STOeqQt 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STXiBoot sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STCaseI (fun sz E s t => STXiBoot sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht sz0_caseI sz0_con Cd hCd

/-- `lem:STOeq_Qt_nonzero` (case (ii)) at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_OeqQtNZ (h : STOeqQtNZ 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STXiBoot sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_ing STCaseII (fun sz E s t => STXiBoot sz E s t) h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

/-- `(eq:Ward_typeP)` (case (i)) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_WardTypeP (h : STWardTypePPin 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STWardTypeP sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STCaseI (fun sz E s t => STWardTypeP sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht sz0_caseI sz0_con Cd hCd

/-- `(y27kasdfg)` (case (i)) at `(sz0, z0, 0, 1/16)`. -/
theorem inst_B45 (h : STB45Pin 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIngConcl (fun sz E s t => STB45 sz E s t) sz0 z0 sInst tInst Cd :=
  inst_ing STCaseI (fun sz E s t => STB45 sz E s t) h sz0 z0 flow_z0 sInst tInst sz0_hs0 sz0_hst
    sz0_ht sz0_caseI sz0_con Cd hCd

/-- `lem:iterations`, case (i) (`1 - s = 1/8 ≤ ilambda² = 1`, `1 - t = ilambda²/L² = 1/16`) at `(szB, zB, 7/8, 15/16)`. -/
theorem inst_iterations (h : STIterations 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIterConcl (fun sz _ n => STAI sz n) szB zB (fun _ => 7 / 8) (fun _ => 15 / 16) Cd :=
  inst_iter STRegIterI (fun sz _ n => STAI sz n) h szB zB flow_zB (fun _ => 7 / 8) (fun _ => 15 / 16)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_regIterI
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

/-- `lem:iterations`, case (ii), at `(szB, zB, 15/16, 31/32)`. -/
theorem inst_iterationsII (h : STIterationsII 3) (Cd : ℝ) (hCd : 0 < Cd) :
    InstIterConcl (fun sz s n => STAII sz s n) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_iter STCaseII (fun sz s n => STAII sz s n) h szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32)
    (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) Cd hCd

/-! ### The deterministic pins at `d = 3` -/

/-- `(yi2oslxj2)` and `(u2jzooi-2)`: the two inequalities of `STContract 3` at `(sz0, n = 2, E = 0, τ = 1/2, ω = 0)`,
`m = 3, k = 1` resp. `m = 4, 1 = k < j = 2 < l = 3`, `p = 1`, `𝒜 ≡ {0}`, `C = 1`. -/
theorem inst_contract (h : STContract 3) :
    (∑ x : Zd 3 (sz0.L 2), ‖STLI sz0 2 0 (1 / 2) (0 : sz0.SeqΩ)
        ⟨List.ofFn (![true, false, true] : Fin 3 → Bool), List.ofFn (![0, 0] : Fin 2 → Zd 3 (sz0.L 2)) ++ [x]⟩‖ ≤
      (((sz0.W 2 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 2 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 2 0 (1 / 2) (2 * 3 - 2 * 1 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ)) ∧
    (∑ x : Zd 3 (sz0.L 2), ∑ y ∈ ({0} : Finset (Zd 3 (sz0.L 2))),
        ‖STLI sz0 2 0 (1 / 2) (0 : sz0.SeqΩ) ⟨List.ofFn (![true, false, true, false] : Fin 4 → Bool),
          List.ofFn (Function.update (![0, 0, 0] : Fin 3 → Zd 3 (sz0.L 2)) (1 : Fin 3) y) ++ [x]⟩‖ ≤
      1 * (((sz0.W 2 : ℕ) : ℝ) ^ 3 * etaT 0 (1 / 2))⁻¹ *
        (STmaxL sz0 2 0 (1 / 2) (2 * 1 - 1) (0 : sz0.SeqΩ) *
          STmaxL sz0 2 0 (1 / 2) (2 * 4 - 2 * 3 - 1) (0 : sz0.SeqΩ)) ^ (1 / 2 : ℝ) *
          STmaxL sz0 2 0 (1 / 2) (2 * (3 - 1) * 1) (0 : sz0.SeqΩ) ^ (1 / (2 * ((1 : ℕ) : ℝ)))) := by
  have H := h sz0 2 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num) 0
  refine ⟨H.1 3 1 (by norm_num) (by norm_num) ![true, false, true] ![0, 0], ?_⟩
  exact H.2 4 1 3 1 ⟨1, by norm_num⟩ 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (fun _ => {0}) (fun _ => by norm_num)
    ![true, false, true, false] ![0, 0, 0]

/-- `lem: newPQ` at `m = 3`, `σ = (+,-,+)`, `A = ∅`: the combinatorial data exist. -/
theorem inst_newPQ (h : STNewPQ 3) :
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool)
      (ι : ∀ α, Fin (k α) → Fin 3) (A' : ∀ α, Finset (Fin (k α))),
      (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      ∀ (n : ℕ) (E τ : ℝ), |E| < 2 → 0 ≤ τ → τ < 1 → ∀ (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L n)),
        zeroModeSet 3 (sz0.L n) ∅ (fun a' => Lloop sz0 n E τ ![true, false, true] a' ω) a =
          zeroModeSet 3 (sz0.L n) (∅ ∪ STIdiff ![true, false, true]) (fun a' => Lloop sz0 n E τ ![true, false, true] a' ω) a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size n : ℕ) : ℂ) * (etaT E τ : ℂ)) ^ (3 - k α)) *
              zeroModeSet 3 (sz0.L n) (A' α) (fun a' => Lloop sz0 n E τ (σ' α) a' ω) (a ∘ ι α) := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, H⟩ := h 3 ![true, false, true] ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, fun n E τ hE h0 h1 ω a => (H sz0 n E τ hE h0 h1 ω a).1⟩

/-- The mollifier exists at `d = 3`, `m = 2` (three indices), `Λ = 1`. -/
theorem inst_mollifier (h : STMollifierEx 3) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
      haveI : NeZero L := ⟨by omega⟩
      ∃ ϑ : ℝ → (Fin (2 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g C c ϑ :=
  h (by norm_num) 2 1 one_pos

/-- `lem_+Q` at `d = 3`, `m = 1` (two indices), `Λ = 1`, `K = 2`, `C = c = 1`. -/
theorem inst_qopNorm (h : STQopNorm 3) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ (L : ℕ) (_ : 3 ≤ L) (g : ℝ), 0 < g → g ≤ 1 →
      ∀ W ε D : ℝ, 1 < W → 0 < ε → ε < 1 → 1 < D → 4 ≤ W ^ ε → (L : ℝ) ^ 3 ≤ W ^ (2 : ℝ) →
      haveI : NeZero L := ⟨by omega⟩
      ∀ ϑ : ℝ → (Fin (1 + 1) → Zd 3 L) → ℂ, STMollifierProps (d := 3) g 1 1 ϑ →
      ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ 𝒜 : (Fin (1 + 1) → Zd 3 L) → ℂ, EKFastDecay g t W ε D 𝒜 →
        ‖STQop (d := 3) ϑ t 𝒜‖ ≤ W ^ (Cn * ε) * ‖𝒜‖ + W ^ (-D + Cn) :=
  h (by norm_num) 1 1 2 1 1 one_pos two_pos one_pos one_pos


end RBM.Gauss.Step34Inst
