/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.DecayGen
import RBM3D.BA.TwistPins
import RBM3D.BA.Step2BA
import RBM3D.BA.FlowPins

/-!
# TLF-C5 and the BA readings of `Chain/Step34Gen` (BA-U row U3s1 leaf, ticket T2457)

A leaf (no module imports it): it may import `BA/`, while `Chain/Step34Gen.lean` may not.

* **TLF-C5 (target 8).** `twSteps` (`BA/TwistPins.lean:133`) is `STStep2ConclgL ∧ STLmaxUgL ∧ STLKUgL ∧ STDecayLoopUgL`
  (conjuncts 2-3 are the pins of `Chain/Step34Gen`, conjunct 4 is T7's `STDecayLoopUgL`, `Chain/DecayGen.lean:66`): the first
  `example` is `Iff.rfl` (supervisor `2026-10-11-1049.md:123-127`), the other two extract conjuncts 2 and 3 (`h.2.1`, `h.2.2.1`).
  They are also applied at concrete data (the band carrier `bandFM sz0 (fun _ => 0)`).
* **BA readings, statement level** (`example : Prop := ...`, proofs owed by U3-BA): targets 1 and 5 at the BA carrier family
  `(law, Flow, mk, T0) = (seqP ∘ withLam 0, BAFlow, baFMz, BAflowT0)`; target 3 at `baStep2Mat` and the flow matrix
  `seqHflowBA (BAflowLam0 sz z)`; `STSEforLngL` at the BA reading.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter

/-! ## 1. Target 8 (TLF-C5): `twSteps` and the pins of `Chain/Step34Gen` -/

/-! ## 2. The BA readings (statement level; the proofs are owed by U3-BA) -/
