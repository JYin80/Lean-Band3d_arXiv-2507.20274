/-
Release check for T2375 (dispatcher V2, Sat Oct 10 07:25 UTC 2026; DECISIONS §185).  LW-01 + ST-6 R4: `Graph/LWTermHolds.lean`,
`Induction/MainIndHolds.lean`; `lem:LWterm`, `lem: EWGn2_N` from the moment bounds, then `STMainInd`, `UNMLOut`.
Part 1: the target statements (existing pins; no new pin).  Part 2: merged names (on `main`; `lwMomentExp_holds` is on
`t/T2364` until it merges and is not checked here).  No proofs, no sorry.
Run: lake env lean docs/tickets/checks/T2375-check.lean
-/
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWTermExpN
import RBM3D.Induction.MainIndOut
import RBM3D.Green.GbEXP

open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## Part 1: the target statements -/
example : Prop := ∀ d : ℕ, LWInteg d
example : Prop := ∀ d : ℕ, LWReduceB d
example : Prop := ∀ d : ℕ, LWReduceT d
example : Prop := ∀ d : ℕ, LWterm d
example : Prop := ∀ d : ℕ, LWtermB d
example : Prop := ∀ d : ℕ, LWtermExpS d
example : Prop := ∀ d : ℕ, LWtermExpN d
example : Prop := ∀ d : ℕ, LWtermExp d
example : Prop := ∀ d : ℕ, STMainInd d
example : Prop := ∀ d : ℕ, RBM.Univ.UNMLOut d

/-! ## Part 2: merged names -/
#check @RBM.Gauss.Sizes.LWMoment
#check @RBM.Gauss.Sizes.LWMomentExp
#check @RBM.Gauss.Sizes.lwMoment_holds
#check @RBM.Gauss.Sizes.lwtermExpN_of_LWterm
#check @RBM.Gauss.Sizes.stMainInd_of_LW
#check @RBM.Univ.unMLOut_of_LW
#check @RBM.Green.stGbEXP_holds
#check @RBM.Gauss.Sizes.LWE
#check @RBM.Gauss.Sizes.LWf
