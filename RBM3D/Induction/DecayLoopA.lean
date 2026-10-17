/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.KDecay
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.Split
import RBM3D.Induction.Defs
import RBM3D.Induction.PerTimeCalc
import RBM3D.Green.Pins

/-!
# S3-07a (ticket T2133): `lem_decayLoop` at a single time and over a window

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex`, `lem_decayLoop` (`3_5:1126`) and
`res_decayLK` (`3_5:1128`).  The source is the `d = 2` file `RBM2D/Induction/DecayLoop.lean`
(read at `9e0f275`; the ticket cites `c9a24cf`) and its pins `DecayLoopAt`, `DecayLoopWindow`
(`RBM2D/Induction/HierVocab.lean:226-262` at `c9a24cf`).

* `STdiamInf a = max_{i,j} |a_i - a_j|_∞` (the `L^∞` diameter of a label vector).
* `STDecayLoopAt sz κ 𝔠 𝔡 C₀ E u P` (the pin) and `stDecayLoopAt_holds` (`3 ≤ d`): from the decay
  input at the single time `u` (a section of `STStep2DecayPT`, prefactor `P`), every loop of length
  `k ≥ 1` with labels spread beyond `ℓ_u W^{τ'}` satisfies `(|𝓛| + |𝓛-𝒦|) ≺ W^{-D'}` per time.
* `STDecayLoopPT sz E s t` and `stDecayLoopPT_of_step2`: the same over `u ∈ [s,t]`, from
  `STStep2DecayPT Cd sz E s t` along the flow `STFlow`, `0 ≤ s ≤ t ≤ lemT z`; prefactor
  `P_u = ((1-s)/(1-u))^{Cd} Bctl^{1/5}`, `C₀ = max Cd 0 + 1`.

Proof of `stDecayLoopAt_holds` (`k ≥ 2`; for `k = 1` the far set is empty), as in RBM2D, with the
`d`-dimensional replacements marked below.  For a far `a`:
1. (`DecayLoopA_adjacent`) some adjacent pair satisfies `diam_∞ a ≤ (k-1) |a_m - a_{m+1}|_∞`
   (triangle inequality of `zdistInf` along the chain).
2. (`DecayLoopA_cut`, `DecayLoopA_pair`) rotate the loop so that this pair is (first, last label),
   cut it into a one-`G` chain and a `(k-1)`-chain; `norm_sq_gloop_le_symIdx` (Cauchy-Schwarz) gives
   `|𝓛_{σ,a}|² ≤ |𝓛_{(+,-),c}| · |symmetric (k-1)-loop|`, and the second factor is at most
   `η_u^{-2(k-1)}` (`norm_gloop_le_of_le_abs_im`).  No entry bound of `G` is used.
3. The `(+,-)` 2-loop at `c`: `|𝓛| ≤ |𝒦| + |𝓛-𝒦|`; `|𝒦|` by `STKcalDecay` at length 2 (the premise
   `W^{-Q} ≤ g` is `(eq:WO)`, `Q = d/2`, `inst_stKcalDecay_admissible`); `|𝓛-𝒦|` by the decay input
   at the pair `c` (`τ₁ = 1`, `D = Q`) with `exp(-√(|c₀-c₁|_∞/ℓ_u)) ≤ W^{-Q}` eventually.
4. `|𝓛-𝒦| ≤ |𝓛| + |𝒦|`; `|𝒦_{σ,a}| ≤ W^{-(D'+1)}` is `STKcalDecay` at length `k`
   (`diam_∞ ≤ KLmaxDist`, `zdistInf ≤ zdistD`).
5. Exponents (`DecayLoopA_alg`): `η_u⁻¹ ≤ (2/√κ) N` (`Im m(E) ≥ √κ/2` and `1 - u ≥ N⁻¹`, which
   follows from the far premise, `DecayLoopA_one_sub_u`), `STWB ≤ 2` (`DecayLoopA_STWB_le`),
   `P ≤ N^{C₀}`, `N ≤ W^{1/𝔠}`, and the exponent `Q = 2D' + (2(k-1) + 1 + C₀)/𝔠 + 1`.
6. Only the event `{|(𝓛-𝒦)_{(+,-),c}| > N ζ_c}` of the decay input at the pair `c` occurs, so the
   pointwise implication `perTimeCalc_of_imp` closes the probability.

Replacements for `d ≥ 3`: `Z2 L ↦ Zd d L`, `zdist2 ↦ zdistInf`, `KLoop.maxDist ↦ STdiamInf`,
`gloop ↦ loopL`, `BlockIndex ↦ Vtx`, `scaleM⁻² ↦ STWB` (bounded by `2` instead of `(2/κ)²`),
`KcalDecay ↦ STKcalDecay`, `Bandwidth/SizeTendsto/RangeCond ↦ Sizes.Admissible` (and the flow
`1 - u ≥ N^{-1+ε/2}` from `v3_premises_of_stFlow` for the window form).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 1. Vocabulary: the `L^∞` diameter, the pins -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`diam_∞ a = max_{i,j} |a_i - a_j|_∞`** of a label vector (the paper's `max_{i,j} |a_i - a_j|`
of `lem_decayLoop`, `3_5:1126`, with the `L^∞` distance, paper-delta T2002b).  The KL layer's
`KLmaxDist` is the `ℓ¹` one: `STdiamInf a ≤ KLmaxDist d L a` (`DecayLoopA_diam_le_KLmaxDist`). -/
def STdiamInf {d L k : ℕ} (a : Fin k → Zd d L) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2)

end RBM.Gauss.Sizes

/-! ## 2. Deterministic: the adjacent far pair and the cut -/

/-! ## 3. Deterministic: scales, exponents -/

/-! ## 4. The probabilistic step, `k ≥ 2` -/

/-! ## 5. The targets -/

/-! ## 6. Compiled nonempty instances (`d = 3`)

The size sequence is the merged preflight sequence `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`,
`lam = (2(n+1))^{-6}`, `Admissible (1/6) (1/10)` = `sz0_admissible`) and the flow of the merged
instance `z0` (`flow_z0`).  The decay input (`STStep2DecayPT`-shaped) is another gate's output
(the Step 2 chain) and stays a hypothesis of the examples; every deterministic hypothesis is
discharged.  `sz0_far_nonempty` shows that the indicator `1(ℓ_u W^{τ'} ≤ diam_∞ a)` is not
identically `0` at the data of the first example, for every `n`. -/

end
