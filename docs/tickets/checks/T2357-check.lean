/-
Release check for T2357 (dispatcher V1, Fri Oct 9 01:04 UTC 2026; DECISIONS §161).  BA-P8 `Prop6Path`: properties 5-8 of `lem_propTH`
for `Θ_BA`, all charge pairs, and the bundle.  Section 1: merged names (`main` 5869c29).  Section 2: the target
statements (Prop values; no proof).  Run: `lake env lean docs/tickets/checks/T2357-check.lean`.
-/
import RBM3D.BA.Prop5
import RBM3D.BA.PropUnit
import RBM3D.BA.Prop5Short
import RBM3D.BA.FlowPins
import RBM3D.Propagator.Prop6Hold

-- Section 1
#check @RBM.BA.BAProp5
#check @RBM.BA.BAProp5s
#check @RBM.BA.BAProp6
#check @RBM.BA.BAProp7
#check @RBM.BA.BAProp8
#check @RBM.BA.BAProp5to8
#check @RBM.BA.BAProp5mixed
#check @RBM.BA.BAProp8mixed
#check @RBM.BA.BAPropUnit1mixed
#check @RBM.BA.BAPropUnit2mixed
#check @RBM.BA.baProp5s_holds
#check @RBM.BA.baProp5mixed_holds
#check @RBM.BA.baProp8mixed_holds
#check @RBM.BA.baPropUnit1mixed_holds
#check @RBM.BA.baPropUnit2mixed_holds
#check @RBM.BA.BATheta
#check @RBM.BA.BATheta0
#check @RBM.BA.BAReal
#check @RBM.prop6Diff1_holds
#check @RBM.prop7Diff2_holds
#check @RBM.zdistD
#check @RBM.Bparam
#check @RBM.ellT

-- Section 2
namespace RBM.BA.T2357Check

def T2357_baProp5_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), RBM.BA.BAProp5 d Λ κ
def T2357_baProp6_holds : Prop := ∀ (d : ℕ) (Λ κ c : ℝ), RBM.BA.BAProp6 d Λ κ c
def T2357_baProp7_holds : Prop := ∀ (d : ℕ) (Λ κ c : ℝ), RBM.BA.BAProp7 d Λ κ c
def T2357_baProp8_holds : Prop := ∀ (d : ℕ) (Λ κ : ℝ), RBM.BA.BAProp8 d Λ κ
def T2357_baProp5to8_holds : Prop := ∀ (d : ℕ) (Λ κ c : ℝ), RBM.BA.BAProp5to8 d Λ κ c

end RBM.BA.T2357Check
