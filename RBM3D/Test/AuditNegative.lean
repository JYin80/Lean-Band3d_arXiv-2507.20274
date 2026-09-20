/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Test.Axioms

/-!
# The audit catches an unclassified premise

`#assert_rbm_axioms` fails the build when a theorem assumes a `Prop` that no theorem of
this development proves and that is in none of the three ledgers.  A check that only ever
passes is worth little, so this file exhibits exactly such a premise -- in the namespace
`RBM.Audit.Fixture`, which the real audit skips -- and asserts that the scan reports it.

This is the same discipline as `RBM3D/Test/InterfaceShape.lean`: the mechanism is tested
against a case where it must fire, not only against the cases where it must not.
-/

namespace RBM.Audit.Fixture

/-- A premise nothing proves: exactly the shape the audit must not let through. -/
def FakePremise (n : Nat) : Prop := n = Nat.succ n

/-- A theorem assuming it, so that the scan sees the premise in a hypothesis. -/
theorem uses_fake (n : Nat) (_h : FakePremise n) : n = n := rfl

end RBM.Audit.Fixture

#assert_rbm_audit_detects RBM.Audit.Fixture.FakePremise
