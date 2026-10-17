/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAS3Close

/-!
# BA-L L4d2b (T2450), part B: the stuck catalogue and the closure "`BAG5LeafProps` or catalogued"
of the S3 trees

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-121`; design
`docs/claude-team/fable/2026-10-12-s3-fold-A.md` §1, §4;
the stuck graphs `docs/reports/T2433-prove.md` §(a⁗).  Part A is `Graph/BAS3Close.lean` (the
roots, the identity, isomorphisms of packed
graphs, the invariants `Even`/`Conn`, Lemma A, the abstract closure).

## Contents (namespace `RBM.Graph`; private prefix `BAS3Close_`)

1. The 14 stuck graphs `baS3Stuck k j s` (7 per root `T3C-tr_k`, both tail charges): the engine's
   output, flattened.
2. The closure modulo the catalogue `baS3Close_mod`: every output of the three root lists at
   `BAselStar`, fuel `2`, both charges, is a leaf
   with the five properties of `BAG5LeafProps` or has the value of a catalogue graph.  The
   classification of the root terms and of the kids of
   the order-`3` terms is a kernel computation on concrete graphs; the passage to the real nodes
   is the isomorphism of part A.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private BAVocab_self_mem_atom from RBM3D.Graph.BAVocab
open private BAS3Close_Iso BAS3Close_iso_symm BAS3Close_iso_trans BAS3Close_iso_val BAS3Close_rel BAS3Close_pk
  BAS3Close_InvC BAS3Close_MC BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_CandC BAS3Close_Kids2 BAS3Close_Kids4
  BAS3Close_root_ge1 BAS3Close_root_ord3 BAS3Close_kids_coeff2 BAS3Close_kids_coeff4 BAS3Close_Even BAS3Close_Conn
  BAS3Close_CtxG BAS3Close_LeafT BAS3Close_MC
  BAS3Close_split_mono BAS3Close_even_split BAS3Close_conn_split BAS3Close_Even_dec BAS3Close_Conn_dec
  from RBM3D.Graph.BAS3Close

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

/-! ## 1. The stuck graphs

The 7 stuck outputs of each tree `T3C-tr_k` (`k = 0` inside `MERGED`, `k = 1`), as produced by the merged definitions: `j = 0` the root term
`#2`, `j = 1` the kid of the first `BACtx` candidate of the order-`3` term, `j = 2, ..., 6` the kids `#2, #17, #22, #47, #52` of the second
(`gg2` for `j ≤ 4`, `gg4` for `j = 5, 6`), at the tail charge `s` (the closing edge `Ǧ(y,x)` or `Ḡ̌(x,y)`).  `BAS3Close_cf{k}_{j}` is the
output with its internal vertices renamed in the order of their roles (core-first): `0 = u₀` (the end of `Ǧ(x,·)`), `1 = u₁` (its
`M`-partner), `2 = u₂` (the end of the middle edge `Ǧ(u₁, u₂)`), `3 = u₃` (the `M`-partner of `u₂`, the start of `Ǧ(u₃, y)`), then the
vertices of the tie chain between `u₀` and `u₂`, then those of the chain between `u₁` and `u₃`; `BAS3Close_eI{k}_{j}` is the renaming. -/

private def BAS3Close_cf0_0 (s : Bool) : BAGraph (Fin 2) (Fin 4) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1))]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 0) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_1 (s : Bool) : BAGraph (Fin 2) (Fin 6) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 1) (Sum.inr 2), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 4), WEdge.mk false false (Sum.inr 0) (Sum.inr 2), WEdge.mk true true (Sum.inr 5) (Sum.inr 3)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_2 (s : Bool) : BAGraph (Fin 2) (Fin 6) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 0) (Sum.inr 4), WEdge.mk true true (Sum.inr 5) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_3 (s : Bool) : BAGraph (Fin 2) (Fin 6) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 4) (Sum.inr 5), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 5) (Sum.inr 4), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 4), WEdge.mk false false (Sum.inr 0) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 5)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_4 (s : Bool) : BAGraph (Fin 2) (Fin 6) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 4), WEdge.mk false false (Sum.inr 0) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 5)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_5 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 6) (Sum.inr 7), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 7) (Sum.inr 6), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 6), WEdge.mk false false (Sum.inr 0) (Sum.inr 4), WEdge.mk true true (Sum.inr 5) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 7)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf0_6 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk false false (Sum.inr 1) (Sum.inr 6), WEdge.mk false false (Sum.inr 0) (Sum.inr 4), WEdge.mk true true (Sum.inr 5) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 7)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_0 (s : Bool) : BAGraph (Fin 2) (Fin 6) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1))]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 5) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_1 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 1) (Sum.inr 2), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 6), WEdge.mk false false (Sum.inr 5) (Sum.inr 2), WEdge.mk true true (Sum.inr 7) (Sum.inr 3)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_2 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 3), WEdge.mk false false (Sum.inr 5) (Sum.inr 6), WEdge.mk true true (Sum.inr 7) (Sum.inr 2)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_3 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 6) (Sum.inr 7), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 7) (Sum.inr 6), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 6), WEdge.mk false false (Sum.inr 5) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 7)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_4 (s : Bool) : BAGraph (Fin 2) (Fin 8) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 6), WEdge.mk false false (Sum.inr 5) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 7)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_5 (s : Bool) : BAGraph (Fin 2) (Fin 10) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 8) (Sum.inr 9), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 9) (Sum.inr 8), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 8), WEdge.mk false false (Sum.inr 5) (Sum.inr 6), WEdge.mk true true (Sum.inr 7) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 9)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_cf1_6 (s : Bool) : BAGraph (Fin 2) (Fin 10) where
  solid := [SEdge.mk true true (Sum.inl 0) (Sum.inr 0), (if s then SEdge.mk true true (Sum.inl 1) (Sum.inl 0) else SEdge.mk false true (Sum.inl 0) (Sum.inl 1)), SEdge.mk true true (Sum.inr 3) (Sum.inl 1), SEdge.mk true true (Sum.inr 1) (Sum.inr 2)]
  waved := [WEdge.mk true true (Sum.inr 4) (Sum.inr 0), WEdge.mk false false (Sum.inr 1) (Sum.inr 8), WEdge.mk false false (Sum.inr 5) (Sum.inr 6), WEdge.mk true true (Sum.inr 7) (Sum.inr 2), WEdge.mk false true (Sum.inr 3) (Sum.inr 9)]
  dotted := []
  coeff := 1
  psi := []
  mdot := [BAMEdge.mk true (Sum.inr 8) (Sum.inr 9), BAMEdge.mk true (Sum.inr 9) (Sum.inr 8), BAMEdge.mk true (Sum.inr 6) (Sum.inr 7), BAMEdge.mk true (Sum.inr 7) (Sum.inr 6), BAMEdge.mk true (Sum.inr 2) (Sum.inr 3), BAMEdge.mk true (Sum.inr 5) (Sum.inr 4), BAMEdge.mk true (Sum.inr 4) (Sum.inr 5), BAMEdge.mk true (Sum.inr 0) (Sum.inr 1)]

private def BAS3Close_eI0_0 : Fin 4 ≃ Fin 4 where
  toFun := ![0, 1, 3, 2]
  invFun := ![0, 1, 3, 2]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_1 : Fin 4 ⊕ Fin 2 ≃ Fin 6 where
  toFun := fun v => Sum.elim ![0, 1, 4, 2] ![5, 3] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 1, Sum.inl 2, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_2 : Fin 4 ⊕ Fin 2 ≃ Fin 6 where
  toFun := fun v => Sum.elim ![0, 1, 3, 4] ![5, 2] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_3 : Fin 4 ⊕ Fin 2 ≃ Fin 6 where
  toFun := fun v => Sum.elim ![0, 1, 4, 2] ![3, 5] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 0, Sum.inl 2, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_4 : Fin 4 ⊕ Fin 2 ≃ Fin 6 where
  toFun := fun v => Sum.elim ![0, 1, 4, 2] ![3, 5] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inl 3, Sum.inr 0, Sum.inl 2, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_5 : Fin 4 ⊕ Fin 4 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![0, 1, 6, 4] ![5, 2, 3, 7] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 2, Sum.inl 3, Sum.inr 0, Sum.inl 2, Sum.inr 3]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI0_6 : Fin 4 ⊕ Fin 4 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![0, 1, 6, 4] ![5, 2, 3, 7] v
  invFun := ![Sum.inl 0, Sum.inl 1, Sum.inr 1, Sum.inr 2, Sum.inl 3, Sum.inr 0, Sum.inl 2, Sum.inr 3]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_0 : Fin 6 ≃ Fin 6 where
  toFun := ![5, 4, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 1, 0]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_1 : Fin 6 ⊕ Fin 2 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 6, 2] ![7, 3] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inr 1, Sum.inl 1, Sum.inl 0, Sum.inl 4, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_2 : Fin 6 ⊕ Fin 2 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 3, 6] ![7, 2] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inr 1, Sum.inl 4, Sum.inl 1, Sum.inl 0, Sum.inl 5, Sum.inr 0]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_3 : Fin 6 ⊕ Fin 2 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 6, 2] ![3, 7] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inr 0, Sum.inl 1, Sum.inl 0, Sum.inl 4, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_4 : Fin 6 ⊕ Fin 2 ≃ Fin 8 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 6, 2] ![3, 7] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inl 5, Sum.inr 0, Sum.inl 1, Sum.inl 0, Sum.inl 4, Sum.inr 1]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_5 : Fin 6 ⊕ Fin 4 ≃ Fin 10 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 8, 6] ![7, 2, 3, 9] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inr 1, Sum.inr 2, Sum.inl 1, Sum.inl 0, Sum.inl 5, Sum.inr 0, Sum.inl 4, Sum.inr 3]
  left_inv := by decide
  right_inv := by decide

private def BAS3Close_eI1_6 : Fin 6 ⊕ Fin 4 ≃ Fin 10 where
  toFun := fun v => Sum.elim ![5, 4, 0, 1, 8, 6] ![7, 2, 3, 9] v
  invFun := ![Sum.inl 2, Sum.inl 3, Sum.inr 1, Sum.inr 2, Sum.inl 1, Sum.inl 0, Sum.inl 5, Sum.inr 0, Sum.inl 4, Sum.inr 3]
  left_inv := by decide
  right_inv := by decide

section Keys

variable {V : Type}

private def BAS3Close_sk (e : SEdge V) : Bool × Bool × V × V := (e.σ, e.circ, e.src, e.dst)
private def BAS3Close_wk (e : WEdge V) : Bool × Bool × V × V := (e.col, e.σ, e.x, e.y)
private def BAS3Close_dk (e : DEdge V) : Bool × V × V := (e.eq, e.x, e.y)
private def BAS3Close_psk (e : BAPsiEdge V) : V × V := (e.x, e.y)
private def BAS3Close_mk (e : BAMEdge V) : Bool × V × V := (e.σ, e.x, e.y)

private theorem BAS3Close_sk_inj : Function.Injective (BAS3Close_sk (V := V)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [BAS3Close_sk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl

private theorem BAS3Close_wk_inj : Function.Injective (BAS3Close_wk (V := V)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [BAS3Close_wk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h; rfl

private theorem BAS3Close_dk_inj : Function.Injective (BAS3Close_dk (V := V)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [BAS3Close_dk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; rfl

private theorem BAS3Close_psk_inj : Function.Injective (BAS3Close_psk (V := V)) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  simp only [BAS3Close_psk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

private theorem BAS3Close_mk_inj : Function.Injective (BAS3Close_mk (V := V)) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [BAS3Close_mk, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h; rfl

end Keys

/-- Two graphs have the same edge lists (a Boolean test, decidable on concrete graphs). -/
private def BAS3Close_Keys {E I : Type} [DecidableEq E] [DecidableEq I] (Δ g : BAGraph E I) : Prop :=
  (decide (Δ.solid.map BAS3Close_sk = g.solid.map BAS3Close_sk) && decide (Δ.waved.map BAS3Close_wk = g.waved.map BAS3Close_wk) &&
    decide (Δ.dotted.map BAS3Close_dk = g.dotted.map BAS3Close_dk) && decide (Δ.psi.map BAS3Close_psk = g.psi.map BAS3Close_psk) &&
    decide (Δ.mdot.map BAS3Close_mk = g.mdot.map BAS3Close_mk)) = true

private instance BAS3Close_Keys_dec {E I : Type} [DecidableEq E] [DecidableEq I] (Δ g : BAGraph E I) :
    Decidable (BAS3Close_Keys Δ g) := by
  unfold BAS3Close_Keys
  infer_instance

private theorem BAS3Close_keys_eq {E I : Type} [DecidableEq E] [DecidableEq I] {Δ g : BAGraph E I} (h : BAS3Close_Keys Δ g)
    (hc : Δ.coeff = g.coeff) : Δ = g := by
  obtain ⟨⟨s, w, d, c⟩, p, m⟩ := Δ
  obtain ⟨⟨s', w', d', c'⟩, p', m'⟩ := g
  simp only [BAS3Close_Keys, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  simp only [] at h1 h2 h3 h4 h5 hc
  have e1 := (List.map_injective_iff.2 BAS3Close_sk_inj) h1
  have e2 := (List.map_injective_iff.2 BAS3Close_wk_inj) h2
  have e3 := (List.map_injective_iff.2 BAS3Close_dk_inj) h3
  have e4 := (List.map_injective_iff.2 BAS3Close_psk_inj) h4
  have e5 := (List.map_injective_iff.2 BAS3Close_mk_inj) h5
  subst e1 e2 e3 e4 e5 hc
  rfl

/-- **The catalogue of the stuck graphs** (target 3): `baS3Stuck k j s` is stuck node `j` of `T3C-tr_k` (`k = false, true`) at the tail
charge `s`, packed over `Fin` (`ext = id`): `j = 0` the root term `#2` (the anchor, `T2450_stuck0_val`), `j = 1, ..., 6` the kids `#1, #2, #17,
#22, #47, #52`. -/
def baS3Stuck : Bool → Fin 7 → Bool → BAPGraph (Fin 2)
  | false, ⟨0, _⟩, s => BAS3Close_pk (BAS3Close_cf0_0 s)
  | false, ⟨1, _⟩, s => BAS3Close_pk (BAS3Close_cf0_1 s)
  | false, ⟨2, _⟩, s => BAS3Close_pk (BAS3Close_cf0_2 s)
  | false, ⟨3, _⟩, s => BAS3Close_pk (BAS3Close_cf0_3 s)
  | false, ⟨4, _⟩, s => BAS3Close_pk (BAS3Close_cf0_4 s)
  | false, ⟨5, _⟩, s => BAS3Close_pk (BAS3Close_cf0_5 s)
  | false, _, s => BAS3Close_pk (BAS3Close_cf0_6 s)
  | true, ⟨0, _⟩, s => BAS3Close_pk (BAS3Close_cf1_0 s)
  | true, ⟨1, _⟩, s => BAS3Close_pk (BAS3Close_cf1_1 s)
  | true, ⟨2, _⟩, s => BAS3Close_pk (BAS3Close_cf1_2 s)
  | true, ⟨3, _⟩, s => BAS3Close_pk (BAS3Close_cf1_3 s)
  | true, ⟨4, _⟩, s => BAS3Close_pk (BAS3Close_cf1_4 s)
  | true, ⟨5, _⟩, s => BAS3Close_pk (BAS3Close_cf1_5 s)
  | true, _, s => BAS3Close_pk (BAS3Close_cf1_6 s)

/-- A node is catalogued: isomorphic to a catalogue graph of the tail charge `s`. -/
private def BAS3Close_Cat (s : Bool) (Q : BAPGraph (Fin 2)) : Prop := ∃ (k : Bool) (j : Fin 7), BAS3Close_Iso Q (baS3Stuck k j s)

private theorem BAS3Close_cat_iso (s : Bool) : ∀ Q Q' : BAPGraph (Fin 2), BAS3Close_Iso Q Q' → BAS3Close_Cat s Q' → BAS3Close_Cat s Q := by
  rintro Q Q' h ⟨k, j, hj⟩
  exact ⟨k, j, BAS3Close_iso_trans h hj⟩

/-- A graph that becomes the pattern `g` under a renaming `e` of its internal vertices is isomorphic (as a trivial pack) to the trivial
pack of `g`. -/
private theorem BAS3Close_iso_pk_perm {A : Type} [Fintype A] [DecidableEq A] {N : ℕ} (e : A ≃ Fin N) {Δ : BAGraph (Fin 2) A}
    {g : BAGraph (Fin 2) (Fin N)} (h : BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) e) Δ = g) :
    BAS3Close_Iso (BAS3Close_pk Δ) (BAS3Close_pk g) :=
  ⟨Equiv.refl _, e, fun _ => rfl, h.symm⟩

section Mirror

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private def BAS3Close_stepL (adj : E ⊕ I → E ⊕ I → Bool) (vs s : List (E ⊕ I)) : List (E ⊕ I) :=
  vs.filter fun w => s.any fun x => decide (x = w) || adj x w

/-- Membership in a list as a Boolean (through `DecidableEq` only). -/
private def BAS3Close_memB {V : Type} [DecidableEq V] (L : List V) (w : V) : Bool := L.any fun x => decide (x = w)

private theorem BAS3Close_memB_iff {V : Type} [DecidableEq V] {L : List V} {w : V} : BAS3Close_memB L w = true ↔ w ∈ L := by
  simp [BAS3Close_memB, List.any_eq_true]

private def BAS3Close_atomL (Γ : BAGraph E I) (vs : List (E ⊕ I)) (v : E ⊕ I) : List (E ⊕ I) :=
  (BAS3Close_stepL (fun a b => Γ.atomAdj a b) vs)^[vs.length] [v]

private theorem BAS3Close_iter_mem (Γ : BAGraph E I) (vs : List (E ⊕ I)) (hvs : ∀ u, u ∈ vs) (v : E ⊕ I) (n : ℕ) :
    ∀ w, w ∈ (BAS3Close_stepL (fun a b => Γ.atomAdj a b) vs)^[n] [v] ↔ w ∈ (Γ.atomStep)^[n] {v} := by
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [BAS3Close_stepL, List.mem_filter, hvs w, true_and, List.any_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      BAGraph.atomStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ]
    constructor
    · rintro ⟨x, hx, rfl | hx2⟩
      · exact Or.inl ((ih _).1 hx)
      · exact Or.inr ⟨x, (ih x).1 hx, hx2⟩
    · rintro (hw | ⟨x, hx, hx2⟩)
      · exact ⟨w, (ih w).2 hw, Or.inl rfl⟩
      · exact ⟨x, (ih x).2 hx, Or.inr hx2⟩

/-- **The bridge**: the list-valued atom has the members of the atom. -/
private theorem BAS3Close_atomL_mem (Γ : BAGraph E I) (vs : List (E ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (E ⊕ I)) (v w : E ⊕ I) : w ∈ BAS3Close_atomL Γ vs v ↔ w ∈ Γ.atom v := by
  unfold BAS3Close_atomL BAGraph.atom
  rw [hlen]
  exact BAS3Close_iter_mem Γ vs hvs v _ w

/-- The representatives of the atoms of internal vertices: the first vertex of the atom in `vs`. -/
private def BAS3Close_repsL (Γ : BAGraph E I) (vs : List (E ⊕ I)) : List (E ⊕ I) :=
  vs.filter fun v => (BAS3Close_atomL Γ vs v).all (fun w => w.isRight) &&
    decide (vs.find? (fun w => BAS3Close_memB (BAS3Close_atomL Γ vs v) w) = some v)

/-- **`n_A ≤` the number of representatives.** -/
private theorem BAS3Close_nA_le (Γ : BAGraph E I) (vs : List (E ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (E ⊕ I)) : Γ.nA ≤ (BAS3Close_repsL Γ vs).length := by
  classical
  unfold BAGraph.nA
  have hmem := BAS3Close_atomL_mem Γ vs hvs hlen
  have hself : ∀ v, v ∈ Γ.atom v := fun v => by rw [BAGraph.mem_atom_iff]
  calc ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ.atom v, w.isRight = true)).image Γ.atom).card
      ≤ (((BAS3Close_repsL Γ vs).toFinset).image Γ.atom).card := by
        refine Finset.card_le_card ?_
        intro A hA
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        have hex : (vs.find? (fun w => BAS3Close_memB (BAS3Close_atomL Γ vs v) w)).isSome := by
          rw [List.find?_isSome]
          exact ⟨v, hvs v, BAS3Close_memB_iff.2 ((hmem v v).2 (hself v))⟩
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hex
        have hu1 : u ∈ vs := List.mem_of_find?_eq_some hu
        have hu2 : u ∈ Γ.atom v := by
          exact (hmem v u).1 (BAS3Close_memB_iff.1 (List.find?_some hu))
        have hAu : Γ.atom u = Γ.atom v := BALvl1B_atom_eq_of_mem Γ hu2
        have hsame : ∀ x, x ∈ BAS3Close_atomL Γ vs u ↔ x ∈ BAS3Close_atomL Γ vs v := fun x => by
          rw [hmem, hmem, hAu]
        refine Finset.mem_image.2 ⟨u, ?_, hAu⟩
        rw [List.mem_toFinset, BAS3Close_repsL, List.mem_filter]
        refine ⟨hu1, ?_⟩
        simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
        refine ⟨fun w hw => ?_, ?_⟩
        · have : w ∈ Γ.atom v := (hmem v w).1 ((hsame w).1 hw)
          exact hv w this
        · have hfun : (fun w => BAS3Close_memB (BAS3Close_atomL Γ vs u) w) = (fun w => BAS3Close_memB (BAS3Close_atomL Γ vs v) w) := by
            funext w
            rw [Bool.eq_iff_iff]
            constructor <;> intro h
            · exact BAS3Close_memB_iff.2 ((hsame w).1 (BAS3Close_memB_iff.1 h))
            · exact BAS3Close_memB_iff.2 ((hsame w).2 (BAS3Close_memB_iff.1 h))
          rw [hfun]; exact hu
    _ ≤ ((BAS3Close_repsL Γ vs).toFinset).card := Finset.card_image_le
    _ ≤ (BAS3Close_repsL Γ vs).length := List.toFinset_card_le _


/-- The graph-level `BACtx` conditions, through the list mirror of the atoms. -/
private def BAS3Close_CtxGL (Γ : BAGraph E I) (vs : List (E ⊕ I)) (v y y' : E ⊕ I) : Prop :=
  Γ.Normal ∧ (BAS3Close_atomL Γ vs v).all (fun w => w.isRight) = true ∧
    (Γ.solid.filter fun e => BAS3Close_memB (BAS3Close_atomL Γ vs v) e.src || BAS3Close_memB (BAS3Close_atomL Γ vs v) e.dst).length = 2 ∧
    BAS3Close_memB (BAS3Close_atomL Γ vs v) y = false ∧ BAS3Close_memB (BAS3Close_atomL Γ vs v) y' = false ∧
    BAS3Close_memB (BAS3Close_atomL Γ vs y') y = false ∧
    ((BAS3Close_atomL Γ vs y').all (fun w => w.isRight) = true ∨ (BAS3Close_atomL Γ vs y).all (fun w => w.isRight) = true)

private instance BAS3Close_CtxGL_dec (Γ : BAGraph E I) (vs : List (E ⊕ I)) (v y y' : E ⊕ I) :
    Decidable (BAS3Close_CtxGL Γ vs v y y') := by
  unfold BAS3Close_CtxGL BAGraph.Normal
  infer_instance

private theorem BAS3Close_ctxGL_iff (Γ : BAGraph E I) (vs : List (E ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (E ⊕ I)) (v y y' : E ⊕ I) : BAS3Close_CtxGL Γ vs v y y' ↔ BAS3Close_CtxG Γ v y y' := by
  have hmem := BAS3Close_atomL_mem Γ vs hvs hlen
  have hne : ∀ a b : E ⊕ I, BAS3Close_memB (BAS3Close_atomL Γ vs a) b = false ↔ Γ.atom a ≠ Γ.atom b := by
    intro a b
    constructor
    · intro hb hab
      have : b ∈ Γ.atom a := by rw [hab]; exact BAVocab_self_mem_atom Γ b
      have h2 := (BAS3Close_memB_iff (L := BAS3Close_atomL Γ vs a) (w := b)).2 ((hmem a b).2 this)
      rw [hb] at h2; exact absurd h2 (by simp)
    · intro hab
      by_contra hb
      have hb' : BAS3Close_memB (BAS3Close_atomL Γ vs a) b = true := by simpa using hb
      have : b ∈ Γ.atom a := (hmem a b).1 (BAS3Close_memB_iff.1 hb')
      exact hab (BALvl1B_atom_eq_of_mem Γ this).symm
  have hall : ∀ a : E ⊕ I, (BAS3Close_atomL Γ vs a).all (fun w => w.isRight) = true ↔ ∀ w ∈ Γ.atom a, w.isRight = true := by
    intro a
    rw [List.all_eq_true]
    constructor
    · intro ha w hw; exact ha w ((hmem a w).2 hw)
    · intro ha w hw; exact ha w ((hmem a w).1 hw)
  have hfil : (Γ.solid.filter fun e => BAS3Close_memB (BAS3Close_atomL Γ vs v) e.src || BAS3Close_memB (BAS3Close_atomL Γ vs v) e.dst) =
      (Γ.solid.filter fun e => decide (e.src ∈ Γ.atom v ∨ e.dst ∈ Γ.atom v)) := by
    refine List.filter_congr fun e _ => ?_
    refine Bool.eq_iff_iff.2 ?_
    simp only [Bool.or_eq_true, decide_eq_true_eq, BAS3Close_memB_iff, hmem]
  unfold BAS3Close_CtxGL BAS3Close_CtxG
  rw [hfil, hall, hall, hall, hne, hne, hne]

private def BAS3Close_CandM (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) : Prop :=
  p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true ∧ p.1.src = q.1.dst ∧
    BAS3Close_CtxGL Γ vs p.1.src p.1.dst q.1.src

private instance BAS3Close_CandM_dec (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    Decidable (BAS3Close_CandM Γ vs p q) := by
  unfold BAS3Close_CandM
  infer_instance

private def BAS3Close_CtxExM (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) : Prop :=
  ∃ p ∈ lwSplit Γ.solid, ∃ q ∈ lwSplit p.2, BAS3Close_CandM Γ vs p q

private instance BAS3Close_CtxExM_dec (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) : Decidable (BAS3Close_CtxExM Γ vs) := by
  unfold BAS3Close_CtxExM
  infer_instance

private theorem BAS3Close_candM_iff (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (Fin 2 ⊕ I)) (p q : SEdge (Fin 2 ⊕ I) × List (SEdge (Fin 2 ⊕ I))) :
    BAS3Close_CandM Γ vs p q ↔ BAS3Close_CandC Γ p q := by
  unfold BAS3Close_CandM BAS3Close_CandC
  rw [BAS3Close_ctxGL_iff Γ vs hvs hlen]

private theorem BAS3Close_ctxExM_sound (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (Fin 2 ⊕ I)) (h : BAS3Close_CtxExM Γ vs) : BAS3Close_CtxExD Γ := by
  obtain ⟨p, hp, q, hq, hc⟩ := h
  exact ⟨p, hp, q, hq, (BAS3Close_candM_iff Γ vs hvs hlen p q).1 hc⟩

/-- The margin `ord + 2·1[x ~ y]` through the mirror (a lower bound of `BAS3Close_MC`). -/
private def BAS3Close_MCM (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) : ℤ :=
  (Γ.nS : ℤ) + 2 * ((Γ.nW : ℤ) - ((BAS3Close_repsL Γ vs).length : ℤ)) +
    (if BAS3Close_memB (BAS3Close_atomL Γ vs (Sum.inl 0)) (Sum.inl 1) = true then 2 else 0)

private theorem BAS3Close_mcm_le (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (Fin 2 ⊕ I)) : BAS3Close_MCM Γ vs ≤ BAS3Close_MC Γ := by
  have hA := BAS3Close_nA_le Γ vs hvs hlen
  have hmem := BAS3Close_atomL_mem Γ vs hvs hlen
  have hxy : (BAS3Close_memB (BAS3Close_atomL Γ vs (Sum.inl 0)) (Sum.inl 1) = true) ↔
      (Γ.atom (Sum.inl 0) = Γ.atom (Sum.inl 1)) := by
    rw [BAS3Close_memB_iff, hmem]
    constructor
    · intro hh; exact (BALvl1B_atom_eq_of_mem Γ hh).symm
    · intro hh; rw [hh]; exact BAVocab_self_mem_atom Γ _
  have hite : (if BAS3Close_memB (BAS3Close_atomL Γ vs (Sum.inl 0)) (Sum.inl 1) = true then (2 : ℤ) else 0) =
      (if Γ.atom (Sum.inl 0) = Γ.atom (Sum.inl 1) then 2 else 0) := by
    by_cases hx : Γ.atom (Sum.inl 0) = Γ.atom (Sum.inl 1)
    · simp [hx, hxy.2 hx]
    · have : ¬ (BAS3Close_memB (BAS3Close_atomL Γ vs (Sum.inl 0)) (Sum.inl 1) = true) := fun hh => hx (hxy.1 hh)
      simp [hx, this]
  unfold BAS3Close_MCM BAS3Close_MC
  unfold BAGraph.scalingOrder BAGraph.counters ord
  rw [hite]
  simp only []
  omega

private theorem BAS3Close_leafM_sound (Γ : BAGraph (Fin 2) I) (vs : List (Fin 2 ⊕ I)) (hvs : ∀ u, u ∈ vs)
    (hlen : vs.length = Fintype.card (Fin 2 ⊕ I)) (h : 5 ≤ BAS3Close_MCM Γ vs) : BAS3Close_LeafT Γ :=
  le_trans h (BAS3Close_mcm_le Γ vs hvs hlen)

end Mirror


private def BAS3Close_vsAB (a b : ℕ) : List (Fin 2 ⊕ (Fin a ⊕ Fin b)) :=
  (List.finRange 2).map Sum.inl ++ ((List.finRange a).map Sum.inl ++ (List.finRange b).map Sum.inr).map Sum.inr

private theorem BAS3Close_vsAB_mem (a b : ℕ) : ∀ u, u ∈ BAS3Close_vsAB a b := by
  rintro (i | i | i) <;> simp [BAS3Close_vsAB]

private theorem BAS3Close_vsAB_len (a b : ℕ) : (BAS3Close_vsAB a b).length = Fintype.card (Fin 2 ⊕ (Fin a ⊕ Fin b)) := by
  simp [BAS3Close_vsAB]



private def BAS3Close_vs1 (a : ℕ) : List (Fin 2 ⊕ Fin a) := (List.finRange 2).map Sum.inl ++ (List.finRange a).map Sum.inr

private theorem BAS3Close_vs1_mem (a : ℕ) : ∀ u, u ∈ BAS3Close_vs1 a := by
  rintro (i | i) <;> simp [BAS3Close_vs1]

private theorem BAS3Close_vs1_len (a : ℕ) : (BAS3Close_vs1 a).length = Fintype.card (Fin 2 ⊕ Fin a) := by
  simp [BAS3Close_vs1]

/-- The facts about a root graph from which the invariants of all its split terms follow. -/
private def BAS3Close_RootFacts {I : Type} [Fintype I] [DecidableEq I] (R : BAGraph (Fin 2) I) : Prop :=
  (∀ e ∈ R.dotted, e.eq = false) ∧ R.nM ≤ 1 ∧ 1 ≤ R.nW ∧ BAS3Close_Even R ∧ BAS3Close_Conn R

private instance BAS3Close_RootFacts_dec {I : Type} [Fintype I] [DecidableEq I] (R : BAGraph (Fin 2) I) :
    Decidable (BAS3Close_RootFacts R) := by
  unfold BAS3Close_RootFacts
  infer_instance

private theorem BAS3Close_invC_of_facts {I : Type} [Fintype I] [DecidableEq I] {R : BAGraph (Fin 2) I} (h : BAS3Close_RootFacts R) :
    ∀ Γ ∈ R.splitG, BAS3Close_InvC Γ ∧ Γ.coeff = R.coeff := by
  intro Γ hΓ
  obtain ⟨hd, hM, hW, hE, hC⟩ := h
  have hed := BAGraph.splitG_edges R Γ hΓ
  refine ⟨⟨⟨by rw [hed.2.1]; exact hd, BAGraph.splitG_circ R Γ hΓ⟩, ?_, ?_, BAS3Close_even_split hE hΓ, BAS3Close_conn_split hC hΓ⟩, ?_⟩
  · have := (BALvl1B_coarse R Γ (BAS3Close_split_mono R hΓ).1 (BAS3Close_split_mono R hΓ).2).2.1
    exact this.trans hM
  · rw [hed.1]; exact hW
  · simp only [BAGraph.splitG, List.mem_map] at hΓ
    obtain ⟨r, -, rfl⟩ := hΓ
    rfl



section Tree0

private def BAS3Close_CatR0 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 4)) : Prop := BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_0) Γ) (BAS3Close_cf0_0 s)

private def BAS3Close_Cat2_0 (s : Bool) (Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 2)) : Prop :=
  BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_1) Δ) (BAS3Close_cf0_1 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_2) Δ) (BAS3Close_cf0_2 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_3) Δ) (BAS3Close_cf0_3 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_4) Δ) (BAS3Close_cf0_4 s)

private def BAS3Close_Cat4_0 (s : Bool) (Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 4)) : Prop :=
  BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_5) Δ) (BAS3Close_cf0_5 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI0_6) Δ) (BAS3Close_cf0_6 s)

private instance (s : Bool) (Γ : BAGraph (Fin 2) (Fin 4)) : Decidable (BAS3Close_CatR0 s Γ) := by
  unfold BAS3Close_CatR0; infer_instance
private instance (s : Bool) (Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 2)) : Decidable (BAS3Close_Cat2_0 s Δ) := by
  unfold BAS3Close_Cat2_0; infer_instance
private instance (s : Bool) (Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 4)) : Decidable (BAS3Close_Cat4_0 s Δ) := by
  unfold BAS3Close_Cat4_0; infer_instance

/-- The classification test of a root term of the tree `0` (everything through the list mirror of the atoms): either a margin `≥ -1` with a
leaf, a candidate or the catalogue, or the order-`3` shape: a candidate exists and every blue `BACtx` candidate has classified kids
(catalogue first, then a candidate, then the leaf target). -/
private def BAS3Close_RootOK0 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 4)) : Prop :=
  (4 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 4) ∧ ((2 ≤ Γ.nW ∧ 5 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 4)) ∨
      BAS3Close_CtxExM Γ (BAS3Close_vs1 4) ∨ BAS3Close_CatR0 s Γ)) ∨
    (3 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 4) ∧ BAS3Close_CtxExM Γ (BAS3Close_vs1 4) ∧
      ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, BAS3Close_CandM Γ (BAS3Close_vs1 4) p q →
        (∀ Δ ∈ BAS3Close_Kids2 Γ p q, BAS3Close_Cat2_0 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 4 2) ∨
          5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 4 2)) ∧
        (∀ Δ ∈ BAS3Close_Kids4 Γ p q, BAS3Close_Cat4_0 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 4 4) ∨
          5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 4 4)))

private instance BAS3Close_RootOK0_dec (s : Bool) (Γ : BAGraph (Fin 2) (Fin 4)) : Decidable (BAS3Close_RootOK0 s Γ) := by
  unfold BAS3Close_RootOK0; infer_instance

private theorem BAS3Close_cat_r0 (s : Bool) {Γ : BAGraph (Fin 2) (Fin 4)} (h : BAS3Close_CatR0 s Γ) (hc : Γ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Γ) :=
  ⟨false, 0, BAS3Close_iso_pk_perm BAS3Close_eI0_0 (BAS3Close_keys_eq h hc)⟩

private theorem BAS3Close_cat_2_0 (s : Bool) {Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 2)} (h : BAS3Close_Cat2_0 s Δ) (hc : Δ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Δ) := by
  rcases h with h | h | h | h
  · exact ⟨false, 1, BAS3Close_iso_pk_perm BAS3Close_eI0_1 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨false, 2, BAS3Close_iso_pk_perm BAS3Close_eI0_2 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨false, 3, BAS3Close_iso_pk_perm BAS3Close_eI0_3 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨false, 4, BAS3Close_iso_pk_perm BAS3Close_eI0_4 (BAS3Close_keys_eq h hc)⟩

private theorem BAS3Close_cat_4_0 (s : Bool) {Δ : BAGraph (Fin 2) (Fin 4 ⊕ Fin 4)} (h : BAS3Close_Cat4_0 s Δ) (hc : Δ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Δ) := by
  rcases h with h | h
  · exact ⟨false, 5, BAS3Close_iso_pk_perm BAS3Close_eI0_5 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨false, 6, BAS3Close_iso_pk_perm BAS3Close_eI0_6 (BAS3Close_keys_eq h hc)⟩

/-- **A root term that passes the test has all its outputs leaves or catalogued.** -/
private theorem BAS3Close_rootok_sound0 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 4)) (h : BAS3Close_RootOK0 s Γ)
    (hI : BAS3Close_InvC Γ) (hc : Γ.coeff = 1) :
    ∀ x ∈ BAexpand BAselStar 2 Γ.packMerge, BAG5LeafProps (fun _ _ => [x.2]) ∨ BAS3Close_Cat s x.2 := by
  have hvs := BAS3Close_vs1_mem 4
  have hlen := BAS3Close_vs1_len 4
  rcases h with h1 | h2
  · obtain ⟨hm, htri⟩ := h1
    refine BAS3Close_root_ge1 (BAS3Close_Cat s) (BAS3Close_cat_iso s) Γ hI.1.1 hI
      (le_trans (by exact_mod_cast hm) (BAS3Close_mcm_le Γ _ hvs hlen)) ?_ 1
    rcases htri with h | h | h
    · exact Or.inl ⟨BAS3Close_leafM_sound Γ _ hvs hlen h.2, hI.2.1, h.1⟩
    · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Γ _ hvs hlen h))
    · exact Or.inr (Or.inr (BAS3Close_cat_r0 s h hc))
  · obtain ⟨hm, hex, hk⟩ := h2
    refine BAS3Close_root_ord3 (BAS3Close_Cat s) (BAS3Close_cat_iso s)
      (fun Δ => BAS3Close_Cat2_0 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 4 2) ∨ 5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 4 2))
      (fun Δ => BAS3Close_Cat4_0 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 4 4) ∨ 5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 4 4)) Γ ?_ ?_
      hI.1.1 hI (le_trans (by exact_mod_cast hm) (BAS3Close_mcm_le Γ _ hvs hlen))
      (BAS3Close_ctxExM_sound Γ _ hvs hlen hex) ?_
    · intro p q Δ hΔ htri
      rcases htri with h | h | h
      · exact Or.inr (Or.inr (BAS3Close_cat_2_0 s h ((BAS3Close_kids_coeff2 Γ p q Δ hΔ).trans hc)))
      · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h))
      · exact Or.inl (BAS3Close_leafM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h)
    · intro p q Δ hΔ htri
      rcases htri with h | h | h
      · exact Or.inr (Or.inr (BAS3Close_cat_4_0 s h ((BAS3Close_kids_coeff4 Γ p q Δ hΔ).trans hc)))
      · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h))
      · exact Or.inl (BAS3Close_leafM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h)
    · intro p hp q hq hcand
      exact hk p hp q hq ((BAS3Close_candM_iff Γ _ hvs hlen p q).2 hcand)

end Tree0


section Tree1

private def BAS3Close_CatR1 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 6)) : Prop := BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_0) Γ) (BAS3Close_cf1_0 s)

private def BAS3Close_Cat2_1 (s : Bool) (Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 2)) : Prop :=
  BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_1) Δ) (BAS3Close_cf1_1 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_2) Δ) (BAS3Close_cf1_2 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_3) Δ) (BAS3Close_cf1_3 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_4) Δ) (BAS3Close_cf1_4 s)

private def BAS3Close_Cat4_1 (s : Bool) (Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 4)) : Prop :=
  BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_5) Δ) (BAS3Close_cf1_5 s) ∨
    BAS3Close_Keys (BAS3Close_rel (Equiv.sumCongr (Equiv.refl (Fin 2)) BAS3Close_eI1_6) Δ) (BAS3Close_cf1_6 s)

private instance (s : Bool) (Γ : BAGraph (Fin 2) (Fin 6)) : Decidable (BAS3Close_CatR1 s Γ) := by
  unfold BAS3Close_CatR1; infer_instance
private instance (s : Bool) (Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 2)) : Decidable (BAS3Close_Cat2_1 s Δ) := by
  unfold BAS3Close_Cat2_1; infer_instance
private instance (s : Bool) (Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 4)) : Decidable (BAS3Close_Cat4_1 s Δ) := by
  unfold BAS3Close_Cat4_1; infer_instance

/-- The classification test of a root term of the tree `1` (everything through the list mirror of the atoms): either a margin `≥ -1` with a
leaf, a candidate or the catalogue, or the order-`3` shape: a candidate exists and every blue `BACtx` candidate has classified kids
(catalogue first, then a candidate, then the leaf target). -/
private def BAS3Close_RootOK1 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 6)) : Prop :=
  (4 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 6) ∧ ((2 ≤ Γ.nW ∧ 5 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 6)) ∨
      BAS3Close_CtxExM Γ (BAS3Close_vs1 6) ∨ BAS3Close_CatR1 s Γ)) ∨
    (3 ≤ BAS3Close_MCM Γ (BAS3Close_vs1 6) ∧ BAS3Close_CtxExM Γ (BAS3Close_vs1 6) ∧
      ∀ p ∈ lwSplit Γ.solid, ∀ q ∈ lwSplit p.2, BAS3Close_CandM Γ (BAS3Close_vs1 6) p q →
        (∀ Δ ∈ BAS3Close_Kids2 Γ p q, BAS3Close_Cat2_1 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 6 2) ∨
          5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 6 2)) ∧
        (∀ Δ ∈ BAS3Close_Kids4 Γ p q, BAS3Close_Cat4_1 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 6 4) ∨
          5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 6 4)))

private instance BAS3Close_RootOK1_dec (s : Bool) (Γ : BAGraph (Fin 2) (Fin 6)) : Decidable (BAS3Close_RootOK1 s Γ) := by
  unfold BAS3Close_RootOK1; infer_instance

private theorem BAS3Close_cat_r1 (s : Bool) {Γ : BAGraph (Fin 2) (Fin 6)} (h : BAS3Close_CatR1 s Γ) (hc : Γ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Γ) :=
  ⟨true, 0, BAS3Close_iso_pk_perm BAS3Close_eI1_0 (BAS3Close_keys_eq h hc)⟩

private theorem BAS3Close_cat_2_1 (s : Bool) {Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 2)} (h : BAS3Close_Cat2_1 s Δ) (hc : Δ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Δ) := by
  rcases h with h | h | h | h
  · exact ⟨true, 1, BAS3Close_iso_pk_perm BAS3Close_eI1_1 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨true, 2, BAS3Close_iso_pk_perm BAS3Close_eI1_2 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨true, 3, BAS3Close_iso_pk_perm BAS3Close_eI1_3 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨true, 4, BAS3Close_iso_pk_perm BAS3Close_eI1_4 (BAS3Close_keys_eq h hc)⟩

private theorem BAS3Close_cat_4_1 (s : Bool) {Δ : BAGraph (Fin 2) (Fin 6 ⊕ Fin 4)} (h : BAS3Close_Cat4_1 s Δ) (hc : Δ.coeff = 1) :
    BAS3Close_Cat s (BAS3Close_pk Δ) := by
  rcases h with h | h
  · exact ⟨true, 5, BAS3Close_iso_pk_perm BAS3Close_eI1_5 (BAS3Close_keys_eq h hc)⟩
  · exact ⟨true, 6, BAS3Close_iso_pk_perm BAS3Close_eI1_6 (BAS3Close_keys_eq h hc)⟩

/-- **A root term that passes the test has all its outputs leaves or catalogued.** -/
private theorem BAS3Close_rootok_sound1 (s : Bool) (Γ : BAGraph (Fin 2) (Fin 6)) (h : BAS3Close_RootOK1 s Γ)
    (hI : BAS3Close_InvC Γ) (hc : Γ.coeff = 1) :
    ∀ x ∈ BAexpand BAselStar 2 Γ.packMerge, BAG5LeafProps (fun _ _ => [x.2]) ∨ BAS3Close_Cat s x.2 := by
  have hvs := BAS3Close_vs1_mem 6
  have hlen := BAS3Close_vs1_len 6
  rcases h with h1 | h2
  · obtain ⟨hm, htri⟩ := h1
    refine BAS3Close_root_ge1 (BAS3Close_Cat s) (BAS3Close_cat_iso s) Γ hI.1.1 hI
      (le_trans (by exact_mod_cast hm) (BAS3Close_mcm_le Γ _ hvs hlen)) ?_ 1
    rcases htri with h | h | h
    · exact Or.inl ⟨BAS3Close_leafM_sound Γ _ hvs hlen h.2, hI.2.1, h.1⟩
    · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Γ _ hvs hlen h))
    · exact Or.inr (Or.inr (BAS3Close_cat_r1 s h hc))
  · obtain ⟨hm, hex, hk⟩ := h2
    refine BAS3Close_root_ord3 (BAS3Close_Cat s) (BAS3Close_cat_iso s)
      (fun Δ => BAS3Close_Cat2_1 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 6 2) ∨ 5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 6 2))
      (fun Δ => BAS3Close_Cat4_1 s Δ ∨ BAS3Close_CtxExM Δ (BAS3Close_vsAB 6 4) ∨ 5 ≤ BAS3Close_MCM Δ (BAS3Close_vsAB 6 4)) Γ ?_ ?_
      hI.1.1 hI (le_trans (by exact_mod_cast hm) (BAS3Close_mcm_le Γ _ hvs hlen))
      (BAS3Close_ctxExM_sound Γ _ hvs hlen hex) ?_
    · intro p q Δ hΔ htri
      rcases htri with h | h | h
      · exact Or.inr (Or.inr (BAS3Close_cat_2_1 s h ((BAS3Close_kids_coeff2 Γ p q Δ hΔ).trans hc)))
      · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h))
      · exact Or.inl (BAS3Close_leafM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h)
    · intro p q Δ hΔ htri
      rcases htri with h | h | h
      · exact Or.inr (Or.inr (BAS3Close_cat_4_1 s h ((BAS3Close_kids_coeff4 Γ p q Δ hΔ).trans hc)))
      · exact Or.inr (Or.inl (BAS3Close_ctxExM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h))
      · exact Or.inl (BAS3Close_leafM_sound Δ _ (BAS3Close_vsAB_mem _ _) (BAS3Close_vsAB_len _ _) h)
    · intro p hp q hq hcand
      exact hk p hp q hq ((BAS3Close_candM_iff Γ _ hvs hlen p q).2 hcand)

end Tree1

/-! ## 3. The closure modulo the catalogue -/

section Tests

set_option maxRecDepth 200000

/-- `MERGED` (`T3C-tr_0 + D1X`): the facts and the test of every root term, both charges (a kernel computation). -/
private theorem BAS3Close_tests_M (s : Bool) :
    BAS3Close_RootFacts (baS3RootM s) ∧ ∀ Γ ∈ (baS3RootM s).splitG, BAS3Close_RootOK0 s Γ := by
  cases s <;> decide +kernel

/-- `D2X`. -/
private theorem BAS3Close_tests_D (s : Bool) :
    BAS3Close_RootFacts (baS3RootD s) ∧ ∀ Γ ∈ (baS3RootD s).splitG, BAS3Close_RootOK0 s Γ := by
  cases s <;> decide +kernel

/-- `T3C-tr_1`. -/
private theorem BAS3Close_tests_1 (s : Bool) :
    BAS3Close_RootFacts (baS3Root1 s) ∧ ∀ Γ ∈ (baS3Root1 s).splitG, BAS3Close_RootOK1 s Γ := by
  cases s <;> decide +kernel

end Tests

/-- The outputs of the list of one root: the partition terms are the packed splits. -/
private theorem BAS3Close_mem_roots {I : Type} [Fintype I] [DecidableEq I] (R : BAGraph (Fin 2) I) (sel : BASel) (fuel : ℕ)
    {q : BAPGraph (Fin 2)} (hq : q ∈ R.partition.flatMap fun P => (BAexpand sel fuel P).map Prod.snd) :
    ∃ Γ ∈ R.splitG, ∃ x ∈ BAexpand sel fuel Γ.packMerge, q = x.2 := by
  obtain ⟨P, hP, hq⟩ := List.mem_flatMap.1 hq
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
  have hP' : P ∈ R.splitG.map BAGraph.packMerge := hP
  obtain ⟨Γ, hΓ, rfl⟩ := List.mem_map.1 hP'
  exact ⟨Γ, hΓ, x, hx, rfl⟩

private theorem BAS3Close_main (r : Fin 3) (s : Bool) :
    ∀ q ∈ BAS3expandRoot BAselStar 2 r s, BAG5LeafProps (fun _ _ => [q]) ∨ BAS3Close_Cat s q := by
  intro q hq
  fin_cases r
  · obtain ⟨Γ, hΓ, x, hx, rfl⟩ := BAS3Close_mem_roots (baS3RootM s) BAselStar 2 hq
    obtain ⟨hF, hT⟩ := BAS3Close_tests_M s
    obtain ⟨hI, hc⟩ := BAS3Close_invC_of_facts hF Γ hΓ
    exact BAS3Close_rootok_sound0 s Γ (hT Γ hΓ) hI hc x hx
  · obtain ⟨Γ, hΓ, x, hx, rfl⟩ := BAS3Close_mem_roots (baS3Root1 s) BAselStar 2 hq
    obtain ⟨hF, hT⟩ := BAS3Close_tests_1 s
    obtain ⟨hI, hc⟩ := BAS3Close_invC_of_facts hF Γ hΓ
    exact BAS3Close_rootok_sound1 s Γ (hT Γ hΓ) hI hc x hx
  · obtain ⟨Γ, hΓ, x, hx, rfl⟩ := BAS3Close_mem_roots (baS3RootD s) BAselStar 2 hq
    obtain ⟨hF, hT⟩ := BAS3Close_tests_D s
    obtain ⟨hI, hc⟩ := BAS3Close_invC_of_facts hF Γ hΓ
    exact BAS3Close_rootok_sound0 s Γ (hT Γ hΓ) hI hc x hx

/-- **The closure modulo the catalogue** (target 4, combinatorial half): every output of the three root lists at the selector `BAselStar`,
fuel `2`, both tail charges, is a leaf with the five properties of `BAG5LeafProps` (the attachment and the target included), or has the value
of a graph of the catalogue `baS3Stuck`. -/
theorem baS3Close_mod : ∀ (r : Fin 3) (s : Bool), ∀ q ∈ BAS3expandRoot BAselStar 2 r s,
    BAG5LeafProps (fun _ _ => [q]) ∨ ∃ (k : Bool) (j : Fin 7), ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (D : BALData ι) (ℓ : Fin 2 → ι),
      q.val D ℓ = (baS3Stuck k j s).val D ℓ := by
  intro r s q hq
  rcases BAS3Close_main r s q hq with h | ⟨k, j, hj⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, j, fun D ℓ => (BAS3Close_iso_val hj D ℓ).symm⟩

end RBM.Graph

end
