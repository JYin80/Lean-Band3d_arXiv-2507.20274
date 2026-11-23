/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/

module

public import RBM3D.Chain.Step34Gen
public import RBM3D.Chain.DecayGen
public import RBM3D.BA.TwistPins
public import RBM3D.BA.Step2BA
public import RBM3D.BA.FlowPins

@[expose] public section

/-!
# Imports of the Step 3-4 statements and the block Anderson twist

This module declares nothing.  It imports `RBM3D.Chain.Step34Gen`, `RBM3D.Chain.DecayGen`,
`RBM3D.BA.TwistPins`, `RBM3D.BA.Step2BA` and `RBM3D.BA.FlowPins`, sets the linter options and opens
`MeasureTheory Filter`.  The statements about Steps 3 and 4 are in `Chain/Step34Gen`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open MeasureTheory Filter
