/-
Release check for T2285 (dispatcher V1, Tue Oct  6 10:20 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §92 (1), §93 (2),
§90, §57 (1), §51, §45 O2, §29, §20, §17, §16).
BA-D6 (block Anderson, gate BA; T2161 split P.9, `docs/reports/T2161-portmap.md:1000`, `:1058`): `RBM3D/BA/Boundary.lean`,
the boundary values of `m(z, g)` on the real axis; proves the merged pin `RBM.BA.BAmBoundary` (`MFixedPoint.lean:548`,
not restated here: it is merged and unchanged).
Section 1: the merged names the proofs use (exact namespaces from the enclosing `namespace … end` blocks; file:line and
last commit on `main` 596a83a), and the Mathlib names of the route (IFT, strict derivatives, sequential compactness).
Section 2: the statements of the five public theorems of T2285 as `*_pin : Prop` in the temporary namespace
`RBM.BA.T2285Check`; T2285 proves each in `RBM.BA` under the name without `_pin`, binders in this order.
Omitted: the private lemmas (prefix `Boundary_`) and the instances (compiled in the file, namespace `RBM.BA.BoundaryInst`).
Section 3: Prop-valued examples at concrete merged data (no proof obligation).
Statements and `#check` only: no theorem, no proof, no tactic block.  Never imported or merged.
Imports: `RBM3D.BA.CouplingWindow` (imports `RBM3D.BA.MFixedPoint`), `RBM3D.BA.FlowPins` (the clause-2 instance), and the
Mathlib modules of the Mathlib names checked in section 1.
Run from the main worktree: `lake env lean docs/tickets/checks/T2285-check.lean`.
-/
import RBM3D.BA.CouplingWindow
import RBM3D.BA.FlowPins
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.MetricSpace.Bounded

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`, namespace `RBM.BA` (`:43-836`)
#check @RBM.BA.BAcard_Zd
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAspec
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAward_avg
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAmBoundary
#check @RBM.BA.BAMB_trace_eq_sum
#check @RBM.BA.BASelf_iff_freeConv
#check @RBM.BA.BASelf_exists
#check @RBM.BA.BASelf_unique
#check @RBM.BA.baMExists_holds
#check @RBM.BA.baMUniqReal_holds
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
-- T2227 (BA-D8, e1fec21): `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA` (`:37-919`)
#check @RBM.BA.BAgapReal
#check @RBM.BA.BAMB_trace_sq_eq_sum
#check @RBM.BA.BAgapReal_holds
#check @RBM.BA.BAm_im_nonneg
#check @RBM.BA.BAself_im_le_one
-- `RBM3D/BA/CouplingWindow.lean`, namespace `RBM.BA.CouplingWindowInst` (`:840-917`)
#check @RBM.BA.CouplingWindowInst.t0P
#check @RBM.BA.CouplingWindowInst.EP
#check @RBM.BA.CouplingWindowInst.m0P
#check @RBM.BA.CouplingWindowInst.g0P
#check @RBM.BA.CouplingWindowInst.flowP_data
#check @RBM.BA.CouplingWindowInst.g0P_pos
-- T2197 (BA-C1a, b750bf3): `RBM3D/BA/FlowPins.lean`, namespace `RBM.BA` (`:660-900`)
#check @RBM.BA.baSelf_none_of_gt
#check @RBM.BA.BAm_eq_zero_of_gt
-- T2013 (868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`, namespace `RBM.Gauss`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.Mres
-- `RBM3D/Defs/Lattice.lean` (51f1a17), namespace `RBM`
#check @RBM.Zd
-- Mathlib: the 1-D inverse function theorem (`Mathlib/Analysis/Calculus/InverseFunctionTheorem/Deriv.lean:33-48`)
#check @HasStrictDerivAt.localInverse
#check @HasStrictDerivAt.eventually_right_inverse
#check @HasStrictDerivAt.eventually_left_inverse
#check @HasStrictDerivAt.to_localInverse
-- Mathlib: strict derivatives (`Deriv/Inv.lean:41`, `Deriv/Comp.lean:256`, `Deriv/Add.lean:202`, `Deriv/Basic.lean:319`)
#check @hasStrictDerivAt_inv
#check @HasStrictDerivAt.comp
#check @HasStrictDerivAt.fun_sum
#check @HasStrictDerivAt.hasDerivAt
-- Mathlib: sequences under a countably generated filter, Bolzano-Weierstrass
-- (`Order/Filter/AtTopBot/CountablyGenerated.lean:118`, `Topology/MetricSpace/Sequences.lean:38`, `Bounded.lean:73`)
#check @Filter.frequently_iff_seq_forall
#check @tendsto_subseq_of_bounded
#check @Metric.isBounded_closedBall

noncomputable section

namespace RBM.BA.T2285Check

open Filter
open scoped Topology
open RBM RBM.Gauss RBM.BA

/-! ## 2. The public theorems of T2285, as propositions -/

/-- `BASelf_of_tendsto` (M3): `(self_m)` is closed along `zₖ → z`, `mₖ → m` with `Im zₖ ≥ 0` and `Im m > 0`. -/
def BASelf_of_tendsto_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ) (zs ms : ℕ → ℂ),
    Tendsto zs atTop (𝓝 z) → Tendsto ms atTop (𝓝 m) → (∀ k, 0 ≤ (zs k).im) →
      (∀ k, BASelf d L g (zs k) (ms k)) → 0 < m.im → BASelf d L g z m

/-- `BAm_tendsto_of_self` (clause 1 of `BAmBoundary`, M2): a real-axis solution is the boundary value. -/
def BAm_tendsto_of_self_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → ∀ (E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m →
    Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m)

/-- `BAm_im_tendsto_zero` (clause 2 of `BAmBoundary`, M4): no real-axis solution, `Im m(E + iη) → 0`. -/
def BAm_im_tendsto_zero_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L] (g E : ℝ), (¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) →
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0)

/-- `BArho_tendsto` (M5): `ρ_N(E) = π⁻¹ Im m(E + i0)` at every real `E` (`1_2:624`, `1_2:715`). -/
def BArho_tendsto_pin : Prop :=
  ∀ (d L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → ∀ E : ℝ,
    Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
      (𝓝 (BArho d L g E))

/-- `baMBoundary_holds`: the merged pin `BAmBoundary` (`MFixedPoint.lean:548`), proved at every `d`. -/
def baMBoundary_holds_pin : Prop := ∀ d : ℕ, BAmBoundary d

/-! ## 3. Statement shapes at concrete merged data (no proof obligation) -/

open RBM.BA.CouplingWindowInst

-- the pin at `d = 3`
example : Prop := BAmBoundary 3
-- clause 1 at the merged flow point `(L, g, E, m) = (4, g0P, EP, m0P)` (`flowP_data.2.2`)
example : Prop := BASelf 3 4 g0P (EP : ℂ) m0P
example : Prop :=
  Tendsto (fun η : ℝ => BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m0P)
-- clause 2 at the gap point `(L, g, E) = (4, 10, 63)` (`baSelf_none_of_gt`: `2 + 2·3·|10| = 62 < 63`)
example : Prop := ¬ ∃ m : ℂ, BASelf 3 4 10 ((63 : ℝ) : ℂ) m
example : Prop :=
  Tendsto (fun η : ℝ => (BAm 3 4 10 (((63 : ℝ) : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0)
-- `ρ_N` at both points
example : Prop :=
  Tendsto (fun η : ℝ => (BAm 3 4 g0P ((EP : ℂ) + (η : ℂ) * Complex.I)).im / Real.pi) (𝓝[>] (0 : ℝ))
    (𝓝 (BArho 3 4 g0P EP))
example : Prop := BArho 3 4 10 63 = 0
-- the public theorems, as propositions
example : Prop := BASelf_of_tendsto_pin ∧ BAm_tendsto_of_self_pin ∧ BAm_im_tendsto_zero_pin
example : Prop := BArho_tendsto_pin ∧ baMBoundary_holds_pin

end RBM.BA.T2285Check

end
