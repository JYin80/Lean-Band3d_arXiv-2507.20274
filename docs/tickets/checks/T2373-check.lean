/-
Release check for T2373 (dispatcher V2, Sat Oct 10 04:31 UTC 2026; DECISIONS §184).  UN-10b: `Universality/EigenInterlacing.lean`,
`Universality/GUELocalSchur.lean`, the Schur tail `UNGUESchurTail` and the weak GUE local law `UNGUELocal`
(RBM2D `Universality/EigenInterlacing.lean`, `Universality/GUELocalSchur.lean`).
Part 1: the target statements (existing pins; no new pin).
Part 2: merged names the port uses.  No proofs, no sorry.  Run: lake env lean docs/tickets/checks/T2373-check.lean
-/
import RBM3D.Universality.GUELocalBootstrap
import RBM3D.Universality.GUEPhase.AuxCarrier
import RBM3D.Green.EntryCore
import RBM3D.Green.LDE
import RBM3D.Green.Pins
import RBM3D.Defs.Sizes

open RBM RBM.Univ

/-! ## Part 1: the target statements -/
#check @RBM.Univ.UNGUESchurTail
#check @RBM.Univ.UNGUELocal
example : Prop := RBM.Univ.UNGUESchurTail
example : Prop := RBM.Univ.UNGUELocal

/-! ## Part 2: merged names -/
#check @RBM.Univ.un_gueLocal_of_tail
#check @RBM.Univ.schurErr
#check @RBM.Univ.schurBud
#check @RBM.Univ.gueP
#check @RBM.Univ.gueVar
#check @RBM.Green.green_diag_paper
#check @RBM.Green.inv_minor_resolvent
#check @RBM.Green.green_diag_ne_zero
#check @RBM.Green.im_green_diag
#check @RBM.Gauss.SizesInst.sz0
