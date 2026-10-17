/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.KDecay
import RBM3D.Induction.NewKLK
import RBM3D.Induction.GridDuhamelN

/-!
# S5-01 (ST-4): the vocabulary and pins of Step 5 of `lem:main_ind`

Moved from the T2134 design probe (`7b2b789`, `RBM3D/Probe/T2134Pins.lean`, never merged).
Paper: arXiv:2507.20274, `paper/tex/1_2_Intro_model_result.tex` (`1_2:line`) and
`paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`).  Step 5 is `1_2:1379-1388`, its proof
`3_5:1935-2383`.

Sections: 2 the four regimes, the Step-5 conclusions and the shape `STIngR5` of every Step-5
pin; 3 case (iii) pins (`STTailtoTail`, `STLemDecCalE`, `STPfStep5`); 4 cases (i)-(ii) pins
(`STNewKLKL`, `STEtermsMid`, `STDuhamelI/II`, `STIniTermI/II`, `STWardII`); 5 the CLT cancellation
of case (i) (`STCltFar`, `STCltIso`, `STExpInv`); 6 the Step-5 pins per regime
(`STStep5I/II/III/IV`, `STStep5`); 8 compiled nonempty instances at `d = 3` (namespace
`RBM.Gauss.Step5Inst`); `tailTD` is in `Defs/Tail.lean`.  The registry class
(DECISIONS §16, §20) of each pin is in its docstring and in `RBM3D/Test/Axioms.lean`; the split
into proof tickets `S5-01 ... S5-29` is in `docs/reports/T2134-portmap.md`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 2. The four regimes of Step 5 (`3_5:1939-1940`) and the conclusions -/

/-- **Case (i)** `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²` (`3_5:1939`), for all sizes. -/
def STReg5I {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ 1 - t n ∧ 1 - s n ≤ sz.lam n ^ 2

/-- **Case (ii)** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²/L²` (`3_5:1939`). -/
def STReg5II {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n ∧
    1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2

/-- **Cases (i) and (ii) together** `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²`: the window of the light-weight and
quadratic-variation bounds `(S5WG+M000)`, `(S5WG+M)` (`3_5:1961-1975`), which use only `ℓ = L` and the Step-2 inputs. -/
def STReg5Mid {d : ℕ} (sz : Sizes d) (s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - t n ∧ 1 - s n ≤ sz.lam n ^ 2

/-- **Case (iii)** `1-s ≥ 1-t ≥ ilambda²` (`3_5:1939`; `1-s ≥ 1-t` is `s ≤ t`). -/
def STReg5III {d : ℕ} (sz : Sizes d) (_s t : ℕ → ℝ) : Prop :=
  ∀ n, sz.lam n ^ 2 ≤ 1 - t n

/-- **Case (iv)** `1-t ≤ 1-s ≤ ilambda²/L^d` (`3_5:1939`): `ℓ_t = L` and `B_{t,0}` is dominated by the zero mode;
Step 5 is then Step 4 (`3_5:1940`). -/
def STReg5IV {d : ℕ} (sz : Sizes d) (s _t : ℕ → ℝ) : Prop :=
  ∀ n, 1 - s n ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d

/-- **`(Eq:Gdecay+s<g_flow)`** (`1_2:1384`, `3_5:2383`), uniformly in `u ∈ [s,t]`: if `1 - t ≥ ilambda²` (so `1 - u ≥
ilambda²` for every `u ≤ t`; the index set is empty at the other sizes, as in `STDecayStrong`), for every `D > 0`,
`|𝓛^{(2)}_{u,σ,a} - 𝒦^{(2)}_{u,σ,a}| ≺ (W^{-d}B_{u,0})² e^{-|a₁-a₂|^{1/2}} + W^{-D}`. -/
def STDecayStrongU (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => ‖Lloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω - STKloop sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1.1 : ℝ)) ^ 2 *
          Real.exp (-((zdistInf d (sz.L n) (p.1.2.2 0 - p.1.2.2 1) : ℕ) : ℝ) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **A Step-5 pin** (the shape of `STIngR`, `Induction/Step34Pins.lean:445`): the setting of `lem:main_ind` with
the conclusions of Steps 1-4 on `[s,t]`, the induction hypothesis `(Eq:Gdecay+IND)` at `s` and, if `1-s ≥ ilambda²`,
`(Eq:Gdecay+IND_s<g)`; a regime `R`; the conclusion is `Concl` about `(E, s, t)`.  Constants first: `κ, ε, 𝔡`, the
Step-2 exponent `C_d`, then `𝔠_d ∈ (0, 10^{-2}]` (small depending on `C_d`), then `𝔠`, the sizes and `z`. -/
def STIngR5 (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ Cd : ℝ, 0 < Cd →
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n < t n) → (∀ n, t n ≤ lemT (z n)) →
          R sz s t → STKbound sz (STflowE z) → STKward sz (STflowE z) →
          STLK sz (STflowE z) s → STDecay sz (STflowE z) s → STDecayStrong sz (STflowE z) s →
          STConStInd sz 𝔠d s t → STStep1Loop sz (STflowE z) s t →
          STStep2Concl sz (STflowE z) s t Cd → STLmaxU sz (STflowE z) s t → STLKU sz (STflowE z) s t →
            Concl sz (STflowE z) s t

/-- **Step 5 of `lem:main_ind`** (`1_2:1379-1388`; proof `3_5:1935-2383`), uniformly in `u ∈ [s,t]`: `(Eq:Gdecay_flow)`
is the merged `STGdecayW` with the loss exponent `C_d = 0` (no factor `((1-s)/(1-u))^{C_d}`: the point of Step 5),
and `(Eq:Gdecay+s<g_flow)` is `STDecayStrongU`. -/
def STStep5Concl {d : ℕ} (sz : Sizes d) (E s t : ℕ → ℝ) : Prop :=
  STGdecayW sz E s t 0 ∧ STDecayStrongU sz E s t

/-- Step 5 under a regime predicate `R` (`True` for the general statement). -/
def STStep5R (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : Prop :=
  STIngR5 d R (fun sz E s t => STStep5Concl sz E s t)

end RBM.Gauss.Sizes


/-! ## 3. Case (iii) `1 - t ≥ ilambda²`: `tailtoTail`, `lem_dec_calE`, `lem:pf_step5` (`3_5:2284-2383`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss

/-- **`TailtoTail`**, `(neiwuj)` (`3_5:2344-2362`), for the tail `T_{u,D}` of `def_WTuD` (not `𝒯_u`; DECISIONS §33 correction,
`docs/claude-team/fable/2026-10-04-tailtotail.md` §2, §4(2)).  Deterministic, every `σ ∈ {±}²`, `|m| = 1`: for
`0 ≤ s ≤ t < 1`, `ilambda² ≤ 1 - t`, `W > 0` and `|A_b| ≤ T_{s,D}(|b₁-b₂|)`,
`|(𝒰^{(2)}_{s,t,σ} ∘ A)_a| ≤ C T_{t,D}(|a₁-a₂|) + ((1-s)/(1-t))² W^{-D}`, with `C = C_d²` free of `s, t, L, W, ilambda, D`
(proof: `P = (s/t) + ((t-s)/t) Θ_t ≥ 0` with row sum `ρ = (1-s)/(1-t)`, `ρ² (W^d(1-s))^{-2} = (W^d(1-t))^{-2}` exactly
(`ell_s = ell_t = 1`), `√|a₁-a₂| ≤ √|a₁-b₁| + √|b₁-b₂| + √|b₂-a₂|`, and `(1-t)Θ_t(0,x) ≤ q^{|x|₁}`,
`q = 2d t g²/(1+2dg²-t) ≤ 2d/(2d+1)` since `1 - t ≥ g²`; for `σ₁ = σ₂`: `|Θ^{(σ)}| ≤ Θ^{(+,-)}`, property 4).  Distances are
`zdistInf`.  Registry class: **owed** (S5-04). -/
def STTailtoTail (d : ℕ) : Prop :=
  3 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) (_hL : 3 ≤ L) (g W D s t : ℝ), 0 < g → 0 < W → 0 ≤ s → s ≤ t → t < 1 → g ^ 2 ≤ 1 - t →
      ∀ m : ℂ, ‖m‖ = 1 → ∀ σ : Fin 2 → Bool, ∀ A : (Fin 2 → Zd d L) → ℂ,
        (∀ b, ‖A b‖ ≤ tailTD d W s D (zdistInf d L (b 0 - b 1) : ℝ)) →
        haveI : NeZero L := ⟨by omega⟩
        ∀ a, ‖UN d L g (EKsgn m σ) s t A a‖ ≤
          C * tailTD d W t D (zdistInf d L (a 0 - a 1) : ℝ) + ((1 - s) / (1 - t)) ^ 2 * W ^ (-D)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The index set `(u, σ, a)` of the 2-loop estimates of Steps 2-5: `u ∈ [s_n, t_n]`, `σ ∈ {±}²`, `a ∈ (Z_L^d)²`. -/
abbrev STIdx2 (s t : ℕ → ℝ) (n : ℕ) : Type :=
  TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))

/-- `|(𝓛 - 𝒦)^{(2)}_{u,σ,a}|` at the single time `u` of the model. -/
def STLK2 (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℝ :=
  ‖Lloop sz n E u σ a ω - STKloop sz n E u σ a‖

/-- `ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}` of the single-time model (`(def_ELKLK)`, `3_5:97`). -/
def STELKLK (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  STELKLKM sz n E u (sz.seqHflow n u ω) σ a

/-- `T_{u,D}(|a₁-a₂|)` of `def_WTuD` at size index `n` (`zdistInf` distance, paper-delta T2002b). -/
def STtailTD (n : ℕ) (u D : ℝ) (a : Fin 2 → Zd d (sz.L n)) : ℝ :=
  tailTD d ((sz.W n : ℕ) : ℝ) u D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)

/-- **`lem_dec_calE`** (`3_5:2314-2338`) for `1 - t ≥ ilambda²`, deterministic control `J*_{u,D} ≥ 1` of
`max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| / T_{u,D}(|a₁-a₂|) ≺ J*_{u,D}` (`(eq:def_new_J*)`, `3_5:2310`), uniformly in `u ∈ [s,t]`,
for `D` with eventually `(L^dW^{6d})² ≤ W^D` and `J*_{u,D} ≤ W^{1/2}` (DECISIONS §61, §63; paper `W^D ≥ N`, paper-delta T2193a/b): the three bounds (`res_deccalE_lk`) `ℰ^{LK×LK}/T ≺ (1-u)⁻¹ (W^d|1-u|)⁻¹ (J*)²`,
(`res_deccalE_wG`) `ℰ^{G̃}/T ≺ (1-u)⁻¹ [1(|a₁-a₂| ≤ (log W)^{3/2}) + (W^d|1-u|)^{-1/2} (J*)^{3/2}]`, and (`res_deccalE_dif`) for
`|a_i - a'_i| ≤ (log W)^{3/2}`: `(ℰ⊗ℰ)^{M,(2)}_{u,σ,a,a'}/T² ≺ (1-u)⁻¹ [1(|a₁-a₂| ≤ 4(log W)^{3/2}) + (W^d|1-u|)^{-1/2} (J*)³]`.
The paper omits the proof ("a special case of [YY_25, Lemma 5.7]"); RBM2D has it deterministically
(`Path/LemDecCalE*.lean`, `lossE2`, `E2Hyp`), the d = 2 exponents `M_u = W² ℓ_u² η_u`. -/
def STLemDecCalEConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ Jst : ℕ → ℝ → ℝ → ℝ, (∀ n u D, 1 ≤ Jst n u D) →
    (∀ n u D, Jst n u D ≤ ((sz.W n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) →
    ∀ D : ℝ, 0 < D →
      (∀ᶠ n in atTop, (((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (6 * d)) ^ 2 ≤ ((sz.W n : ℕ) : ℝ) ^ D) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => STLK2 sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω)
        (fun n p _ => Jst n (p.1 : ℝ) D * STtailTD sz n (p.1 : ℝ) D p.2.2) →
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ * Jst n (p.1 : ℝ) D ^ 2 *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz (U := STIdx2 sz s t)
        (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => (1 - (p.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (p.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (p.1 : ℝ) D ^ (3 / 2 : ℝ)) *
          STtailTD sz n (p.1 : ℝ) D p.2.2) ∧
      Prec sz
        (U := fun n => {q : STIdx2 sz s t n × (Fin 2 → Zd d (sz.L n)) //
          ∀ i : Fin 2, ((zdistInf d (sz.L n) (q.1.2.2 i - q.2 i) : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)})
        (fun n q ω => ‖STee sz n (E n) (q.1.1.1 : ℝ) ω q.1.1.2.1 q.1.1.2.2 q.1.2‖)
        (fun n q _ => (1 - (q.1.1.1 : ℝ))⁻¹ *
          ((if ((zdistInf d (sz.L n) (q.1.1.2.2 0 - q.1.1.2.2 1) : ℕ) : ℝ) ≤ 4 * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)
              then 1 else 0) +
            (((sz.W n : ℕ) : ℝ) ^ d * |1 - (q.1.1.1 : ℝ)|)⁻¹ ^ (1 / 2 : ℝ) * Jst n (q.1.1.1 : ℝ) D ^ (3 : ℝ)) *
          STtailTD sz n (q.1.1.1 : ℝ) D q.1.1.2.2 ^ 2)

/-- **`lem:pf_step5`** (`3_5:2371-2383`) at the sequence level: the stopping time `T` of `(eq:def_TTT)` is `≥ t` with
high probability for every `ε > 0` (small `ε` suffices: `ε` is arbitrary in the conclusion) iff
`max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}| / T_{u,D}(|a₁-a₂|) ≺ 1` uniformly in `u ∈ [s,t]`, for every `D > 0` (`T_{u,D}` decreases in `D`
at fixed `u`, so large `D` implies small `D`).  Index set empty unless `1 - t ≥ ilambda²`.  The paper omits the proof
("analogous to, and much simpler than, `(2.76)` of [YY_25, §5.3]"); the closure at `d = 3` is Fable §4(3):
`J*_{t'∧T} ≺ C + log W + W^{2ε - 𝔡/2} < W^ε` for `ε < 𝔡/4` and large `W` (`ε ≤ 2𝔡`, `2𝔡`, `𝔡` for the three terms in the
preflight table, last row). -/
def STPfConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz
      (U := fun n => {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n})
      (fun n p ω => STLK2 sz n (E n) (p.1.1 : ℝ) p.1.2.1 p.1.2.2 ω)
      (fun n p _ => STtailTD sz n (p.1.1 : ℝ) D p.1.2.2)

/-- **`lem:pf_step5`**, regime (iii).  Registry class: **borrowed** (DECISIONS §16: the paper cites it, "analogous to, and much simpler
than, the proof of (2.76) in [YY_25, §5.3]", `3_5:2380`); S5-10, S5-11 prove it (DECISIONS §5). -/
def STPfStep5 (d : ℕ) : Prop := STIngR5 d STReg5III (fun sz E s t => STPfConcl sz E s t)

end RBM.Gauss.Sizes

/-! ## 4. Cases (i) and (ii) `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²` (`3_5:1957-2283`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-- The index set `(u, σ, a)` of the 2-loop estimates with `σ` restricted to a class `P` (`σ₁ = σ₂` or `σ₁ ≠ σ₂`). -/
abbrev STIdx2P (P : (Fin 2 → Bool) → Prop) (s t : ℕ → ℝ) (n : ℕ) : Type :=
  TimeIcc s t n × {σ : Fin 2 → Bool // P σ} × (Fin 2 → Zd d (sz.L n))

/-- **`lem:newKLK` at `ℓ = L`, sharp form** (`(i2kk2zgg)` `3_5:628-651` with `ℓ = L`; paper-delta candidate `T2134a`):
for every Hermitian `H` with `‖G_u - M‖_max ≤ δ₀` and `D ≥ 0`,
`|ℰ^{(𝓛-𝒦)×(𝓛-𝒦),(2)}_{u,σ,a}| ≤ C/(1-u) (Ĵ² W^{-d} 𝒯̃^L_{u,D}(|a₁-a₂|) + Ĵ W^{-d-D})`, `Ĵ = Ĵ^L_{u,D}`.  Step 5, case (i), needs
`(ilambda² W^d)^{-1/3}` (`(S5WG+M000)`, `3_5:1968`), i.e. no term linear in `Ĵ ≺ (ilambda² W^d)^{-1/6}`; the printed
`lem:newKLK` (`(juwo=Lklk)`, merged `STNewKLK`, `Ĵ + Ĵ² 1_{ℓ≥1}`) is too weak by `ρ (ilambda² W^d)^{1/30}`; the paper's remark
"the index sets `{c' : |c'-b| ≥ L-1}` are empty" gives the sharp form when `𝒯_u(L) ≥ W^{-D}`, and the linear term is the
floor `Ĵ W^{-d-D}` otherwise (the far pairs: `Σ_c (|𝓛_{(a,c)}| + |𝒦_{(a,c)}|) ≤ (1+o(1)) W^{-d}/(1-u)` by Ward, `3_5:640-646`).  Registry class: **owed**
(S5-12; the proof is `Induction/NewKLK.lean` `nkl_bound2` with the floor kept). -/
def STNewKLKLAt (d : ℕ) (κ 𝔡 C δ₀ : ℝ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u D : ℝ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ → |E| ≤ 2 - κ →
    0 ≤ u → u < 1 → 0 ≤ D →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMM sz n E u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STELKLKM sz n E u H σ a‖ ≤
          C / (1 - u) * (STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H ^ 2 *
              STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1) +
            STJhatM sz n E D ((sz.L n : ℕ) : ℝ) u H * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **`lem:newKLK` at `ℓ = L`, the pin** (constants `C, δ₀` depend on `d, κ, 𝔡` only, as `STNewKLK`). -/
def STNewKLKL (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ STNewKLKLAt d κ 𝔡 C δ₀

/-- **`(S5WG+M000)` and `(S5WG+M)`** (`3_5:1968-1979`), the negligibility of the three error terms of `(int_K-LcalE_n=2)` at
`ℓ = L` in the window `ilambda²/L^d ≤ 1-t ≤ 1-s ≤ ilambda²` (cases (i) and (ii)), uniformly in `u ∈ [s,t]`, every `D > 0`,
`A = ilambda² W^d` (`STAI`; `B_{u,0} ≍ ilambda⁻²`, `W^{-d} B_{u,0} ≍ A⁻¹`):
`ℰ^{LK×LK} ≺ A^{-1/3} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`, `ℰ^{G̃} ≺ A^{-1/2} η_u⁻¹ W^{-d}𝒯̃^L_{u,D}`,
`(ℰ⊗ℰ)^{M,(2;k)} ≺ A^{-1/2} η_u⁻¹ (W^{-d}𝒯̃^L_{u,D})²`.  Inputs (not hypotheses of the pin; its proof ticket derives them):
`(eq:Step2_inputs)` from `STGdecayW` and `STK2decay` (`𝓛^{(2)} ≺ W^{-d}𝒯̃^L`, `(𝓛-𝒦)^{(2)} ≺ A^{-1/6} W^{-d}𝒯̃^L`, with
`ρ^{C_d} Δ_u^{1/5} ≤ Δ_u^{1/6}`, `𝔠_d C_d ≤ 1/30`), `STNewKLKL`, `STLWT`, `STEMn2Exp` with `Ĵ ≺ A^{-1/6}`.  The
`dℰ^M` term enters through its quadratic variation `(ℰ⊗ℰ)^{M}` (DECISIONS §7: Azuma on the grid instead of BDG).
Registry class: **owed** (S5-13). -/
def STEtermsMidConcl (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STELKLK sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 3) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := STIdx2 sz s t)
      (fun n p ω => ‖STEGt sz n (E n) (p.1 : ℝ) p.2.1 p.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1 : ℝ))⁻¹ *
        STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1)) ∧
    Prec sz (U := fun n => STIdx2 sz s t n × Fin 2)
      (fun n p ω => ‖STEEk sz n (E n) (p.1.1 : ℝ) p.2 p.1.2.1 p.1.2.2 ω‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 2) : ℝ) * (etaT (E n) (p.1.1 : ℝ))⁻¹ *
        STprof sz n (p.1.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.1.2.2 0) (p.1.2.2 1) ^ 2)

/-- **`(S5WG+M000)`, `(S5WG+M)`**, window of cases (i)+(ii). -/
def STEtermsMid (d : ℕ) : Prop := STIngR5 d STReg5Mid (fun sz E s t => STEtermsMidConcl sz E s t)

/-- **The initial term** `𝒰^{(2)}_{s,u,σ} ∘ (𝓛-𝒦)^{(2)}_{s,σ}` (`(iksjuwjx0)` `3_5:2072`; `(zYU2)` `3_5:2269` for
`Q^{(1)}`), a statement at the time `s` only (the kernel `𝒰_{s,u,σ}` is the merged `Ugen`), uniformly in `u ∈ [s,t]`, for the
sign class `P`, with the zero-mode-removing set `Q` (`Q^{(A)} = zeroModeSet`): `≺ A^{-1/5} W^{-d}𝒯̃^L_{u,D}(|a₁-a₂|) + W^{-D}`. -/
def STIniTermConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- **The integrated hierarchy at `n = 2`** (`(int_K-LcalE_n=2)` `3_5:1942-1948`, `(iois-mtx)`..`(iois-mtx2)`
`3_5:2046-2069`), conditional on the initial term: if the initial term obeys a deterministic single-time control `F` at the time
`s` (index `(u,σ,a)`), then `Q^{(A)} ∘ (𝓛-𝒦)^{(2)}_{u,σ}` obeys `F + A^{-1/5} W^{-d}𝒯̃^L_{u,D} + W^{-D}`, uniformly in `u ∈ [s,t]`.
The three error terms are controlled by `STEtermsMidConcl` (hypothesis of the pin), the kernel by `(eq:decompU)`
`P = s/t + ((t-s)/t) Θ_t`, `‖Θ_t^{(+,-)}‖_{∞→∞} = 1/(1-t)` (`(eq:THETAinftinf)`), `(uwp2-92kj)` (`(TTT2)` and
`prop:ThfadC`), `(uwftgwesj)`, and the closure of the exponents `ρ A^{-1/3}`, `ρ A^{-1/2}`, `ρ³ A^{-1/4} ≤ A^{-1/5}`
with `ρ ≤ Δ_t^{-𝔠_d} ≤ (2A)^{𝔠_d}`, `𝔠_d ≤ 1/100 < 1/60` (preflight table row 4).  The martingale term is the Azuma form of
`(alu9_STime)` for the `𝒰`-weighted increments of `STGridRepN` (loop length `2`).  Registry class: **owed** (S5-15). -/
def STDuhamelConcl (Q : Finset (Fin 2)) (P : (Fin 2 → Bool) → Prop) (E s t : ℕ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D → ∀ F : ∀ n, STIdx2P sz P s t n → ℝ, (∀ n p, 0 ≤ F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (RBM.Ind.Ugen d (sz.L n) (sz.lam n) (E n) p.2.1.1 (s n) (p.1 : ℝ)
          (fun b => STLKM sz n (E n) (s n) (sz.seqHflow n (s n) ω) p.2.1.1 b)) p.2.2‖)
      (fun n p _ => F n p) →
    Prec sz (U := STIdx2P sz P s t)
      (fun n p ω => ‖zeroModeSet d (sz.L n) Q
        (fun a' => STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
      (fun n p _ => F n p + (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-- Sign classes: equal and different signs. -/
def STSigSame (σ : Fin 2 → Bool) : Prop := σ 0 = σ 1
def STSigMixed (σ : Fin 2 → Bool) : Prop := σ 0 ≠ σ 1
def STSigAll (_σ : Fin 2 → Bool) : Prop := True

/-- **Case (i)**, the integrated hierarchy without zero-mode removal, all signs (`(iois-mtx2)`, `3_5:2067`).  Registry class:
**owed** (S5-15). -/
def STDuhamelI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STEtermsMidConcl sz E s t → STDuhamelConcl sz ∅ STSigAll E s t)

/-- **Case (i)**, the initial term, all signs (`(iksjuwjx0)`, `3_5:2072`; for `σ₁ = σ₂` by the short-range decay
`prop:ThfadC_short`, for `σ₁ ≠ σ₂` through `lem;CLT`, `f^{near}`, the Ward term `g_a`).  Registry class: **owed** (S5-16). -/
def STIniTermI (d : ℕ) : Prop :=
  STIngR5 d STReg5I (fun sz E s t => STIniTermConcl sz ∅ STSigAll E s t)

/-- **Case (ii)**, the integrated hierarchy: `Q^{(1)}` (`zeroModeSet {0}`) for `σ₁ ≠ σ₂` (`(iisuwjyys)` at `n = 2`,
`3_5:2263-2277`, merged `ZeroModeCalc`), and without `Q` for `σ₁ = σ₂` (`3_5:2253`).  Registry class: **owed** (S5-26). -/
def STDuhamelII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t => STEtermsMidConcl sz E s t →
    STDuhamelConcl sz {0} STSigMixed E s t ∧ STDuhamelConcl sz ∅ STSigSame E s t)

/-- **Case (ii)**, the initial term: `(1-s)² Θ̊_t (𝓛-𝒦)_s Θ_t` of `(zYU2)` (`3_5:2275-2281`, absolute values and `(prop:ThfadC0)`,
`1-s ≤ ilambda²/L²`) for `σ₁ ≠ σ₂`, short-range for `σ₁ = σ₂`.  Registry class: **owed** (S5-27). -/
def STIniTermII (d : ℕ) : Prop :=
  STIngR5 d STReg5II (fun sz E s t =>
    STIniTermConcl sz {0} STSigMixed E s t ∧ STIniTermConcl sz ∅ STSigSame E s t)

/-- **`(zYU1)`** (`3_5:2257-2262`), `σ₁ ≠ σ₂`: `(𝓛-𝒦)^{(2)}_{u,σ,a} - [Q^{(1)} ∘ (𝓛-𝒦)^{(2)}_{u,σ}]_a = Im(𝓛-𝒦)^{(1)}_{u,+,a₂} /
(N η_u) ≺ A⁻¹ (N η_u)⁻¹` (Ward's identities `(WI_calL)`, `(WI_calK)` and `(Gt_avgbound_flow)`, `Δ_u ≍ A⁻¹` in `(ii)`),
`N = (WL)^d`.  Registry class: **owed** (S5-28). -/
def STWardIIConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz (U := STIdx2P sz STSigMixed s t)
    (fun n p ω => ‖STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 p.2.2 -
      zeroModeSet d (sz.L n) {0}
        (fun a' => STLKM sz n (E n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
    (fun n p _ => (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT (E n) (p.1 : ℝ))⁻¹)

/-- **`(zYU1)`**, regime (ii). -/
def STWardII (d : ℕ) : Prop := STIngR5 d STReg5II (fun sz E s t => STWardIIConcl sz E s t)

end RBM.Gauss.Sizes

/-! ## 5. The CLT cancellation of case (i): `lem;CLT` (`3_5:2160-2250`) -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

open Classical in
/-- **`f^{far}_{σ,a}`** of `3_5:2160-2170`, for `σ₁ ≠ σ₂` (`Θ^{(σ₁,σ₂)}_t = Θ_{t}` since `m(σ₁)m(σ₂) = |m|² = 1`):
`(1-s)² Σ_{b₁ : |b₁-a₁|∧|b₁-a₂| > (log W)^4 ℓ_s} Σ_{b₂} Θ_{t,a₁b₁} 𝓑_{b₁b₂} (Θ_{t,b₂a₂} - Θ_{t,b₁a₂})`,
`𝓑 = (𝓛-𝒦)^{(2)}_{s,σ}` at the time `s`; the propagator is the merged `Theta` at `ξ = t m(σ₁) m(σ₂)`. -/
def STfFar (n : ℕ) (E s t : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((1 - s) ^ 2 : ℝ) : ℂ) * ∑ b₁ ∈ Finset.univ.filter (fun b₁ : Zd d (sz.L n) =>
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 0) : ℕ) : ℝ) ∧
      Real.log ((sz.W n : ℕ) : ℝ) ^ 4 * ellT (sz.L n) (sz.lam n) s < ((zdistInf d (sz.L n) (b₁ - a 1) : ℕ) : ℝ)),
    ∑ b₂ : Zd d (sz.L n),
      Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) (a 0) b₁ *
        STLKM sz n E s (sz.seqHflow n s ω) σ ![b₁, b₂] *
        (Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₂ (a 1) -
          Theta d (sz.L n) (sz.lam n) ((t : ℂ) * (STmsig E (σ 0) * STmsig E (σ 1))) b₁ (a 1))

/-- **`lem;CLT`** (`3_5:2173-2176`, proof `3_5:2182-2249`): under `ilambda²/L² ≤ 1-t ≤ 1-s ≤ ilambda²` and `(con_st_ind)`,
`(eq:ells_to_ellt)` `ℓ_t ≥ ℓ_s (log W)^5` and `(eq:ells_to_ellt2)` `|a₁-a₂| ≤ ½ (log W)^{3/2} ℓ_t + (log W)^{5/2} ℓ_s` (`3_5:2119-2126`),
`f^{far}_{σ,a} ≺ (ilambda² W^d)^{-6/5} / (|a₁-a₂|^{d-2} + 1)`, `σ₁ ≠ σ₂`.  What is new against RBM2D's CLT (`Evolution/Clt*.lean`, the
`clt-lemma` of [DYYY25, §7] used in Step 3 of `d = 2`; DYYY25 `(7.39)` = `CltFar`, `Evolution/CltDecorrelation.lean:277`):
(1) the summand is a *two-label* loop `𝓑_{b₁b₂}` in a window `|b₁-b₂| ≤ (log W)³ ℓ_s`, weighted by first differences
`Θ_{b₂a₂} - Θ_{b₁a₂}` (`prop:BD1`) carrying polynomial decay around *both* `a₁` and `a₂`, whereas RBM2D's `Z_{ab}` are bounded kernels
(Case 1: supported in `|a-b| < W^τ ℓ_t`; Case 2: `≺ (1+|a-b|)⁻¹`, one label) with conclusion `W^{Cτ} ℓ_t ℓ_u Λ`, no decay in `|a₁-a₂|`;
(2) the target keeps the decay `1/(|a₁-a₂|^{d-2}+1)`: the moment sum `(eq:2p_product_pair)` needs
`Σ_b (|b|^{d-1}+1)^{-k} < ∞`, true iff `(d-1)k > d`, i.e. `k ≥ 2` at `d = 3` (fails at `d = 2, k = 2`); clusters of size 1 are removed by
the isolation bound `STCltIso`, not by summability; the cluster exponent count `d-(d-2)k+(d+2)(k-1)+2 = 4k` holds for all `d ≥ 3`, `k`
(preflight (i)); (3) the mean part `𝔼 f^{far}` uses translation invariance and reflection symmetry of `𝔼 𝓑` (`STExpInv`) and the second
difference `prop:BD2` (`ℓ_s²/(|a₂-b₁|^d+1)`), which has no `d = 2` counterpart in Step 3; (4) `eq:bound_isolated` is dimension free
(`3_5:2245`), port of `CltFar`.  Registry class: **owed** (S5-25). -/
def STCltFarConcl (E s t : ℕ → ℝ) : Prop :=
  Prec sz
    (U := fun n => {p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)) //
      Real.log ((sz.W n : ℕ) : ℝ) ^ 5 * ellT (sz.L n) (sz.lam n) (s n) ≤ ellT (sz.L n) (sz.lam n) (t n) ∧
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
          (1 / 2 : ℝ) * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (t n) +
            Real.log ((sz.W n : ℕ) : ℝ) ^ (5 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) (s n)})
    (fun n p ω => ‖STfFar sz n (E n) (s n) (t n) p.1.1.1 p.1.2 ω‖)
    (fun n p _ => (STAI sz n) ^ (-(6 / 5) : ℝ) / (((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ) ^ (d - 2) + 1))

/-- **`lem;CLT`**, case (i). -/
def STCltFar (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltFarConcl sz E s t)

/-- `𝗕_b := (ilambda² W^d)^{6/5} (𝓛-𝒦)^{(2)}_{s,σ,b}` (`3_5:2217`). -/
def STcltB (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (ω : sz.SeqΩ) : ℂ :=
  (((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (6 / 5 : ℝ) : ℝ) : ℂ) *
    STLKM sz n E s (sz.seqHflow n s ω) σ b

/-- The factor `𝔼-centred 𝗕` (`conj = false`) or its conjugate (`conj = true`): `𝗕 - 𝔼𝗕`, `\bar{𝗕 - 𝔼𝗕}`. -/
def STcltX (n : ℕ) (E s : ℝ) (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)) (cj : Bool) (ω : sz.SeqΩ) : ℂ :=
  if cj then (starRingEnd ℂ) (STcltB sz n E s σ b ω - ∫ ω', STcltB sz n E s σ b ω' ∂(sz.seqP))
  else STcltB sz n E s σ b ω - ∫ ω', STcltB sz n E s σ b ω' ∂(sz.seqP)

/-- **`(eq:bound_isolated)`** (`3_5:2245`; [DYYY25, `(7.39)`], [RBSO1D, `(A.112)`], "does not depend on `d`"): if one label `b^{(i)}`
is isolated, `min_{j≠i} |b₁^{(i)} - b₁^{(j)}| ≥ 10 (log W)³ ℓ_s` (all labels in the window `|b₁-b₂| ≤ (log W)³ ℓ_s`), then
`|𝔼 ∏_{k=1}^{p} IE 𝗕_{b^{(k)}} ∏_{k=p+1}^{2p} IE \bar𝗕_{b^{(k)}}| ≤ W^{-D}`, every fixed `p ≥ 1`, `D > 0`, eventually.  The paper takes it
from the literature (`3_5:2248`: registry class **borrowed**, DECISIONS §16); §5 lets only LSY be external, so it is proved here: port of RBM2D `CltFar` (`Evolution/CltDecorrelation.lean:277`,
replacement/telescoping over the `2 N²` real coordinates, `CltSwap`, `CltResolvent`, `CltPath`, `CltGood`, `CltStep`, `FarEntry`) with
`Z2 ↦ Zd d`; its inputs are `(Gt_bound_flow)` and `(Eq:Gdecay_w)` at the time `s` (`STStep2Concl`, `u = s`), `(GijGEX)` (merged
`STGbEXPij`).  Registry class: **borrowed** (proved by S5-17..S5-21). -/
def STCltIsoConcl (E s _t : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, 1 ≤ p → ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ σ : Fin 2 → Bool, σ 0 ≠ σ 1 →
    ∀ b : Fin (2 * p) → (Fin 2 → Zd d (sz.L n)),
      (∀ k, ((zdistInf d (sz.L n) ((b k) 0 - (b k) 1) : ℕ) : ℝ) ≤
        Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n)) →
      (∃ i, ∀ j, j ≠ i → 10 * Real.log ((sz.W n : ℕ) : ℝ) ^ 3 * ellT (sz.L n) (sz.lam n) (s n) ≤
        ((zdistInf d (sz.L n) ((b i) 0 - (b j) 0) : ℕ) : ℝ)) →
      ‖∫ ω, ∏ k : Fin (2 * p), STcltX sz n (E n) (s n) σ (b k) (decide (p ≤ k.val)) ω ∂(sz.seqP)‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D)

/-- **`(eq:bound_isolated)`**, case (i). -/
def STCltIso (d : ℕ) : Prop := STIngR5 d STReg5I (fun sz E s t => STCltIsoConcl sz E s t)

end RBM.Gauss.Sizes

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **Translation and reflection invariance of `𝔼 𝓛^{(2)}`** (`3_5:2196-2200`: "By the translation invariance and symmetry of our
model on the block level, `𝔼𝓑` is translationally invariant and symmetric"): the law of the model is invariant under the
translations `a ↦ a + c` and the reflection `a ↦ -a` of the block lattice (the variance profile `(eq:variancematrix)` is), so
`𝔼 𝓛^{(2)}_{u,σ,(a₁+c,a₂+c)} = 𝔼 𝓛^{(2)}_{u,σ,a}` and `𝔼 𝓛^{(2)}_{u,σ,(-a₁,-a₂)} = 𝔼 𝓛^{(2)}_{u,σ,a}`; with `c = a₁ + a₂`
they give `𝔼 𝓛_{(a₂,a₁)} = 𝔼 𝓛_{(a₁,a₂)}`.  `𝒦` is invariant by `Θ` property 2 and the symmetric `S^{(B)}`.  RBM2D:
`Evolution/MLExpInv.lean` (pin S2.4 of `ML:exp`, ST-5) and `Induction/AltSymm.lean`; shared with Step 6.  Registry class: **owed**
(S5-22, or the Step-6 ticket if it lands first). -/
def STExpInv (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (n : ℕ) (E u : ℝ), |E| < 2 → 0 ≤ u → u < 1 →
    ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) (c : Zd d (sz.L n)),
      (∫ ω, Lloop sz n E u σ (fun i => a i + c) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP)) ∧
      (∫ ω, Lloop sz n E u σ (fun i => -a i) ω ∂(sz.seqP) = ∫ ω, Lloop sz n E u σ a ω ∂(sz.seqP))

/-! ## 6. The pins of Step 5 in each regime -/

/-- **Step 5, case (i)**.  Registry class: **owed** (follows from `STEtermsMid`, `STDuhamelI`, `STIniTermI` by
`ST_step5_caseI_of_pins`, S5-02). -/
def STStep5I (d : ℕ) : Prop := STStep5R d STReg5I
/-- **Step 5, case (ii)**.  Registry class: **owed** (follows from `STEtermsMid`, `STDuhamelII`, `STIniTermII`, `STWardII` by
`ST_step5_caseII_of_pins`, S5-03). -/
def STStep5II (d : ℕ) : Prop := STStep5R d STReg5II
/-- **Step 5, case (iii)**.  Registry class: **owed** (follows from `STPfStep5` by `ST_step5_caseIII_of_pf`, S5-03). -/
def STStep5III (d : ℕ) : Prop := STStep5R d STReg5III
/-- **Step 5, case (iv)** (from Step 4: proved in this probe, `stStep5IV_holds`; library move S5-02). -/
def STStep5IV (d : ℕ) : Prop := STStep5R d STReg5IV
/-- Case (i) is inside the window of cases (i)+(ii) (probe `7b2b789:732`, used by `inst_etermsMid`, `inst_duhamelI`). -/
theorem st5_reg5I_mid {sz : Sizes d} (hd : 2 ≤ d) {s t : ℕ → ℝ} (h : STReg5I sz s t) : STReg5Mid sz s t := by
  intro n
  refine ⟨?_, (h n).2⟩
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have h2 : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL hd
  refine le_trans ?_ (h n).1
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) h2

end RBM.Gauss.Sizes


/-! ## 8. Compiled nonempty instances at `d = 3`

Size data: the merged `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6}`, flow `z0`, `s ≡ 0`, `t ≡ 1/16`), the merged
`szB` (`L = 4`, `W_n = n+4`, `ilambda = 1`, flow `zB`, `lemT zB ≥ 31/32`), and the new `szG` (`szB` with `ilambda = 5 ≤ 𝔡⁻¹ = 10`).
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`.  Regimes (`ilambda²/L² = 1/16`, `ilambda²/L^3 = 1/64` for `szB`; `ilambda²/L^3 = 25/64` for `szG`):
* case (i)  `szB`, `(s,t) = (7/8, 15/16)`:   `1/16 ≤ 1-t = 1/16 ≤ 1-s = 1/8 ≤ 1`;
* case (ii) `szB`, `(s,t) = (15/16, 31/32)`: `1/64 ≤ 1-t = 1/32 ≤ 1-s = 1/16 ≤ 1/16`;
* case (iii) `sz0`, `(s,t) = (0, 1/16)`:       `ilambda_n² ≤ 15/16 = 1-t`;
* case (iv) `szG`, `(s,t) = (5/8, 3/4)`:       `1-t = 1/4 ≤ 1-s = 3/8 ≤ 25/64`;
* the CLT pins of case (i) (`inst_cltFar`, `inst_cltIso`): `szCL` (`L_n = 2(n+24)^5 → ∞`, `W_n = 2^{n+24}`, `ilambda = 1`), flow
  `zCL`, `(s_n,t_n) = (0, 1 - L_n^{-2})`: at `L = 4` the index set of `STCltFarConcl` and the isolation premise of
  `STCltIsoConcl` are empty (`ℓ_t/ℓ_s ≤ L` must exceed `(log W)^5`, `L/2` must exceed `10 (log W)^3`).
Every deterministic hypothesis (flow, time ranges, regime, `(con_st_ind)` for every `𝔠_d > 0`) is discharged; what stays a hypothesis
of an instance is a stochastic premise of the pin (`STKbound`, `STKward`, `STLK`, `STDecay`, `STDecayStrong` at `s`, Steps 1-4). -/

/-! ### The ingredients -/

/-! ### Data with `L_n → ∞` for the CLT pins of case (i) (`STCltFar`, `STCltIso`)

`szCL`: `m = n + 24`, `L_n = 2 m^5`, `W_n = 2^m`, `ilambda = 1`; flow `zCL_n = 1/2 + i/(2 L_n²)` (`1 - lemT ≤ 2 Im z`);
`s ≡ 0`, `1 - t_n = L_n^{-2}` (case (i): `ilambda²/L² = 1-t ≤ 1-s = ilambda² = 1`).  Then `ℓ_s = 1`, `ℓ_t = L_n`,
`1 ≤ log W_n = m log 2 ≤ m`, `W ≥ L` (`2 m^5 ≤ 2^m` for `m ≥ 24`), `W^{-3}B_{t,0} ≤ 4^{-m}`, so `(con_st_ind)` holds for
every `𝔠_d > 0` (`4 m^{10} ≤ (4^{𝔠_d})^m` eventually).  The index set of `STCltFarConcl` is nonempty
(`szCL_cltFar_index_nonempty`) and the premises of `STCltIsoConcl` hold for a configuration with `p = 1`
(`szCL_cltIso_witness`), at every `n`. -/

/-! ### The deterministic pins -/
