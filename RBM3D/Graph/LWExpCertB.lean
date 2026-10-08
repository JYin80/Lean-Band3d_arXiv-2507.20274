/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWExpCert

/-!
# LW-14e-1': the corrected lite flag `belowOf'` and its non-vacuity instances

`LWExpCert.lean` (T2306) with one changed line: the consistency test of `belowOf'` reads the `×`-edges `X0` from
`Δ.dotBase` (the dotted edges that `LGraph.withDots` keeps; the b-edges `isB` are removed, `LWVocab.lean:1073, 1091-1095`),
which is exactly the set of `×`-edges that `cMerge (Δ.withDots c)` tests.  So a choice is skipped iff
`¬ (Δ.withDots c).Consistent`.  The unprimed names of `LWExpCert.lean` stay frozen; this file adds the primed successors
(`belowOf'`, `childrenB'`, `goodB'`, `rootInfo'`, `rootAt'`, `kids'`, `kidsOk'`, `kid'`, `goodB'_succ_of`), the diagnostic
`lostOf`/`lostAt`, and the instances.  The chunk theorems are in `LWExpCertBS0` (`s = false`) and `LWExpCertBS1` (`s = true`,
`cert_all'`).  Paper `B:66-69, 78-108` ("verified by inspecting", `B:98`), `7_8:215-221` (`dot-def`).
All public names are in `namespace RBM.Graph.LWCert`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option maxRecDepth 1000000

noncomputable section

open RBM.Gauss.Sizes

namespace RBM.Graph.LWCert

/-- **The lite classification of the raw choices of a family graph `Δ`.**  For each consistent dotted choice the classes
(`labsOf`) give `B` internal vertices after the merge and `L` uncircled loops; the children (weight splits `t = 0..L`) have
`ord = n_S - t + 2 (n_W - B)`; only the children below the target are built (`cMerge`, `splitWeights`); for every choice with a
leaf variant the leaf properties `n_M ≤ 1`, `2 ≤ n_W`, `LWAttached`, "distinct external molecules or joined" are evaluated on the
molecule classes `mol` (waved edges added to the classes).  First component: all leaf properties hold. -/
def belowOf' (Δ : LGraph (Fin (a+1)) (Fin b)) (ext : Fin 2 → Fin (a+1)) : Bool × List MNode :=
  let n := a + 1 + b
  let nS : ℤ := Δ.solid.length
  let nW : ℤ := Δ.waved.length
  let S : List (Bool × ℕ × ℕ) := Δ.solid.map fun e => (e.circ, vi a b e.src, vi a b e.dst)
  let X0 : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)   -- T2319: was `Δ.dotted` (T2306); `withDots` keeps `dotBase` only
  let E0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => e.eq).map (pairOf a b)
  let W : List (ℕ × ℕ) := Δ.waved.map fun e => (vi a b e.x, vi a b e.y)
  let x0 := vi a b (Sum.inl (ext 0))
  let y0 := vi a b (Sum.inl (ext 1))
  (Δ.dotChoices).foldr (fun c acc =>
    let E1 := (c.2.filter fun e => e.eq).map (pairOf a b)
    let X1 := (c.2.filter fun e => !e.eq).map (pairOf a b)
    let labs := labsOf n (E0 ++ E1)
    if (X0 ++ X1).any (fun e => labs.getD e.1 0 == labs.getD e.2 0) then acc
    else
      let B : ℤ := ((repsOf labs).filter (· ≥ a + 1)).length
      let L : ℤ := (S.filter fun e => !e.1 && labs.getD e.2.1 0 == labs.getD e.2.2 0).length
      let tg : ℤ := if labs.getD x0 0 == labs.getD y0 0 then 4 else 5
      let ok0 : Bool :=
        if nS + 2 * (nW - B) ≥ tg then
          let mol := W.foldl (fun l e => unite l e.1 e.2) labs
          let nMc := ((List.range n).filter fun i => i ≥ a + 1 && mol.getD i 0 == i).length
          nMc ≤ 1 && nW ≥ 2 &&
          ((List.range n).filter fun i => i ≥ a + 1 && mol.getD i 0 == i).all (fun i =>
            2 ≤ (S.filter fun e => mol.getD e.2.1 0 != mol.getD e.2.2 0 && (mol.getD e.2.1 0 == i || mol.getD e.2.2 0 == i)).length) &&
          (labs.getD x0 0 == labs.getD y0 0 || mol.getD x0 0 != mol.getD y0 0 || nMc == 0)
        else true
      if nS - L + 2 * (nW - B) ≥ tg then (ok0 && acc.1, acc.2)
      else
        match cMerge (Δ.withDots c) ext with
        | none => (ok0 && acc.1, acc.2)
        | some N => (ok0 && acc.1, ((N.g.splitWeights 1).map fun g => { N with g := g }).filter (fun M => !leaf M) ++ acc.2)) (true, [])

/-- The below-target children of a node at a candidate (all families), and the leaf-property flag. -/
def childrenB' (N : MNode) (c : Cand N.a N.b) : Bool × List MNode :=
  (fams N.g c).foldr (fun f acc => let r := belowOf' f.2 N.ext; (r.1 && acc.1, r.2 ++ acc.2)) (true, [])

/-- **The AND-tree certificate of height `n`**: a leaf, or a node with a candidate all of whose candidates have only good
below-target children (every candidate, so the certificate does not depend on a selection rule). -/
def goodB' : ℕ → MNode → Bool
  | 0, N => leaf N
  | n + 1, N => leaf N || (!(cands N.g).isEmpty && (cands N.g).all fun c =>
      (childrenB' N c).1 && (childrenB' N c).2.all (goodB' n))

/-- The root: `LWG5Graph k s` as a "family graph" with `x = 0`, `y = 1`: leaf-property flag of all its partition terms, and the
terms below the target (11 for every `(k, s)`). -/
def rootInfo' (k s : Bool) : Bool × List MNode := belowOf' (a := 1) (b := 3) (LWG5Graph k s) ![0, 1]

def rootAt' (k s : Bool) (i : ℕ) : MNode := (rootInfo' k s).2.getD i default

/-- Below-target children of `N` at its `j`-th candidate, and the flag. -/
def kids' (N : MNode) (j : ℕ) : List MNode :=
  match (cands N.g)[j]? with | some c => (childrenB' N c).2 | none => []

def kidsOk' (N : MNode) (j : ℕ) : Bool :=
  match (cands N.g)[j]? with | some c => (childrenB' N c).1 | none => true

def kid' (N : MNode) (j l : ℕ) : MNode := (kids' N j).getD l default

/-- Assembly of the certificate of a node from its candidates and the certificates of its below-target children. -/
theorem goodB'_succ_of (n : ℕ) (N : MNode) (nc : ℕ) (hc : (cands N.g).length = nc) (hnc : 0 < nc)
    (hk : ∀ j < nc, kidsOk' N j = true)
    (hch : ∀ j < nc, ∀ l < (kids' N j).length, goodB' n (kid' N j l) = true) :
    goodB' (n + 1) N = true := by
  unfold goodB'
  have hne : (cands N.g).isEmpty = false := by
    cases h : cands N.g with
    | nil => rw [h] at hc; simp at hc; omega
    | cons _ _ => rfl
  rw [Bool.or_eq_true]
  right
  rw [hne]
  simp only [Bool.not_false, Bool.true_and, List.all_eq_true]
  intro c hc'
  obtain ⟨j, hj, hcj⟩ := List.getElem_of_mem hc'
  have hj' : j < nc := hc ▸ hj
  have h1 := hk j hj'
  have h2 := hch j hj'
  have hq : (cands N.g)[j]? = some c := by rw [List.getElem?_eq_getElem hj, hcj]
  have hk2 : kids' N j = (childrenB' N c).2 := by unfold kids'; rw [hq]
  have hkid : ∀ l, kid' N j l = (childrenB' N c).2.getD l default := by intro l; unfold kid'; rw [hk2]
  unfold kidsOk' at h1
  rw [hq] at h1
  simp only at h1
  rw [h1, Bool.true_and]
  apply all_of_getD
  intro l hl
  have := h2 l (hk2 ▸ hl)
  rwa [hkid] at this


/-! ## The certificate: one inner node, the shapes, and non-vacuity instances -/

theorem inner_node_one' : goodB' 3 (rootAt' false false 0) = true := by
  have h : (cands (rootAt' false false 0).g).length = 2 ∧ ∀ j < 2, kidsOk' (rootAt' false false 0) j = true ∧ (kids' (rootAt' false false 0) j).length = 0 := by decide +kernel
  apply goodB'_succ_of 2 _ 2 h.1 (by omega) (fun j hj => (h.2 j hj).1)
  intro j hj l hl
  have := (h.2 j hj).2
  omega

/-- The root has `163` partition terms, `11` below the target, and all leaf properties hold for the others. -/
theorem root_FF_shape' : (rootInfo' false false).1 = true ∧ (rootInfo' false false).2.length = 11 := by decide +kernel
theorem root_FT_shape' : (rootInfo' false true).1 = true ∧ (rootInfo' false true).2.length = 11 := by decide +kernel

/-- Instance (2): the root term `0` of `(k, s) = (false, false)` is not a leaf, has `scalingOrder 3`, target `4`,
`2` internal vertices and `2` candidates. -/
theorem lwCert_root0_nonleaf' :
    leaf (rootAt' false false 0) = false ∧ (rootAt' false false 0).g.scalingOrder = 3 ∧
      tgt (rootAt' false false 0) = 4 ∧ (rootAt' false false 0).b = 2 ∧
      (cands (rootAt' false false 0).g).length = 2 := by
  decide +kernel

/-- Instance (3): all `11` below-target root terms of both `s` are not leaves. -/
theorem lwCert_roots_below' :
    (rootInfo' false false).2.all (fun N => !leaf N) = true ∧
      (rootInfo' false true).2.all (fun N => !leaf N) = true := by
  decide +kernel

/-! ## Per-candidate split of a depth-1 node (used by the chunk files `LWExpCertBS0`, `LWExpCertBS1`)

A depth-1 node `K` is certified at height `2` by the certificates of its candidates one at a time (each a separate kernel
run, to bound the memory of one declaration): candidate `c` of `K` is good if its families satisfy the leaf properties and every
below-target child has a height-`1` certificate. -/

/-- Candidate `c` of the node `K` is good at height `1`. -/
def lwcertB_candGood (K : MNode) (c : ℕ) : Prop :=
  kidsOk' K c = true ∧ ∀ m < (kids' K c).length, goodB' 1 (kid' K c m) = true

theorem lwcertB_nokids (K : MNode) (c : ℕ) (h : kidsOk' K c = true ∧ (kids' K c).length = 0) :
    lwcertB_candGood K c := by
  refine ⟨h.1, fun m hm => ?_⟩
  have h2 := h.2
  omega

theorem lwcertB_onekid (K : MNode) (c : ℕ) (h : kidsOk' K c = true ∧ (kids' K c).length = 1)
    (hd : goodB' 1 (kid' K c 0) = true) : lwcertB_candGood K c := by
  refine ⟨h.1, fun m hm => ?_⟩
  have h2 := h.2
  have hm0 : m = 0 := by omega
  subst hm0
  exact hd

theorem lwcertB_two (K : MNode) (nc : ℕ) (hn : (cands K.g).length = nc) (hnc : 0 < nc)
    (h : ∀ c < nc, lwcertB_candGood K c) : goodB' 2 K = true :=
  goodB'_succ_of 1 K nc hn hnc (fun c hc => (h c hc).1) (fun c hc l hl => (h c hc).2 l hl)

/-- The choices of `Δ` that `belowOf` skips and `belowOf'` evaluates: no `×`-edge of `Δ.dotBase ++ c.2` inside an
`=`-class, but a b-edge of `Δ` inside one (T2318 (a) (ii); diagnostic, for the instances). -/
def lostOf (Δ : LGraph (Fin (a+1)) (Fin b)) : ℕ :=
  let n := a + 1 + b
  let X0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => !e.eq).map (pairOf a b)
  let X0' : List (ℕ × ℕ) := (Δ.dotBase.filter fun e => !e.eq).map (pairOf a b)
  let E0 : List (ℕ × ℕ) := (Δ.dotted.filter fun e => e.eq).map (pairOf a b)
  (Δ.dotChoices.filter fun c =>
    let E1 := (c.2.filter fun e => e.eq).map (pairOf a b)
    let X1 := (c.2.filter fun e => !e.eq).map (pairOf a b)
    let labs := labsOf n (E0 ++ E1)
    (X0 ++ X1).any (fun e => labs.getD e.1 0 == labs.getD e.2 0) &&
      !((X0' ++ X1).any (fun e => labs.getD e.1 0 == labs.getD e.2 0))).length

/-- `lostOf` of the `i`-th family graph of the `j`-th candidate of `N` (`0` if out of range). -/
def lostAt (N : MNode) (j i : ℕ) : ℕ :=
  match (cands N.g)[j]? with
  | some c => match (fams N.g c)[i]? with | some f => lostOf f.2 | none => 0
  | none => 0

/-- The counterexample of T2318 (a): one external pair, no internal vertex, one b-edge `×(0,1)`. -/
def lwCertB_cex : LGraph (Fin 2) (Fin 0) := ⟨[], [], [⟨false, Sum.inl 0, Sum.inl 1⟩], 1⟩

/-- Instance (5): the change bites in the tree.  Root term `9` of `(k, s) = (false, false)`, candidate `0`: family `R2`
(`fams` index `0`) loses `5` choices, family `R8` (first `q'`, index `6`) loses `36`. -/
theorem lwCertB_lost_R2 : lostAt (rootAt' false false 9) 0 0 = 5 := by decide +kernel
theorem lwCertB_lost_R8 : lostAt (rootAt' false false 9) 0 6 = 36 := by decide +kernel

/-- Instance (6): the counterexample is covered: `belowOf` lists `1` term, `belowOf'` lists `2`, `lostOf = 1`. -/
theorem lwCertB_cex_bites :
    (belowOf (a := 1) (b := 0) lwCertB_cex ![0, 1]).2.length = 1 ∧
    (belowOf' (a := 1) (b := 0) lwCertB_cex ![0, 1]).2.length = 2 ∧
    lostOf (a := 1) (b := 0) lwCertB_cex = 1 := by
  decide +kernel

/-- Instance (7): the root is unchanged (no dotted edge at the root). -/
theorem lwCertB_root_eq :
    (rootInfo' false false).2.length = (rootInfo false false).2.length ∧
    lostOf (a := 1) (b := 3) (LWG5Graph false false) = 0 ∧
    lostOf (a := 1) (b := 3) (LWG5Graph false true) = 0 := by
  decide +kernel

#print axioms goodB'_succ_of
#print axioms inner_node_one'
#print axioms root_FF_shape'
#print axioms root_FT_shape'
#print axioms lwCert_root0_nonleaf'
#print axioms lwCert_roots_below'
#print axioms lwcertB_nokids
#print axioms lwcertB_onekid
#print axioms lwcertB_two
#print axioms lwCertB_lost_R2
#print axioms lwCertB_lost_R8
#print axioms lwCertB_cex_bites
#print axioms lwCertB_root_eq

end RBM.Graph.LWCert
