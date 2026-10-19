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
# The `L^∞` diameter of a label vector

For a vector of labels `a : Fin k → Zd d L` the quantity
`STdiamInf a = max_{i,j} |a_i - a_j|_∞` is the `L^∞` diameter of `a`.  It measures how far apart
the labels of a loop are in Claim 4.5 (`lem_decayLoop`, (4.20) `res_decayLK`): a loop is small,
`≺ W^{-D'}`, once `ℓ_u W^{τ'} ≤ diam_∞ a`.  `DecayLoopB.lean` states and proves the uniform form of
that decay (`STDecayLoopU`) in terms of `STdiamInf`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## The `L^∞` diameter -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-- **`diam_∞ a = max_{i,j} |a_i - a_j|_∞`** of a label vector: the maximum in `lem_decayLoop`
(Claim 4.5), taken with the `L^∞` distance.  The `ℓ¹` analogue `KLmaxDist` of the `𝒦`-decay layer
satisfies `STdiamInf a ≤ KLmaxDist d L a` (`zdistInf ≤ zdistD`). -/
def STdiamInf {d L k : ℕ} (a : Fin k → Zd d L) : ℕ :=
  Finset.univ.sup fun p : Fin k × Fin k => zdistInf d L (a p.1 - a p.2)

end RBM.Gauss.Sizes

end
