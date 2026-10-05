/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular6b

/-!
# LW-10c3: `lem:localregular`, property (6), part 3 (T2203)

The local lemma `LGraph.ScostLL` for the last three primitive moves `MoveSC`, `MoveOut`, `Dmove` (F
§3, §4.5), from the helpers of c2 (`LocalRegular6b`, T2195).

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`, property (6) = `(eq:sizeGammamu)`, `7_8:815-818`) and
`paper/tex/B_graphical_lemmas.tex` (cited `B:line`): the proof of (6) `B:200-278` (the edge and `GG`
cases are omitted there, `B:272-275`), the remark `B:280-283`.  Design: DECISIONS §47, §55 (LW-10c
is split into c1-c4: `LocalRegular6a` is c1, `LocalRegular6b` c2, this file c3, then `6d`); the
mathematics is the Fable report `docs/claude-team/fable/2026-10-05-localreg6-locallemma.md` (cited
F).

## What is proved

* **Target 1** `localReg6c_alone_diff` (F §4.1): the exact difference of the cost of the term
  `Γ_rest.owxExt (owxEmb 1) c A W` at a setoid `s'` that leaves the fresh vertex `α` alone and
  the cost of `Γ` at the restriction `s₀ = comap (owxEmb 1) s'`: `#kept(A) - #kept(R) + 2 |W| +
  ([elem A_α] - 2) + Σ_{c₀ ∈ C} [c₀ internal] ([elem (X + A_{c₀})] - [elem (X + R_{c₀})])`,
  `Γ.solid ~ R ++ rest`, `X` the class pattern of `rest`, `C` any finset of classes that
  contains the classes of the old ends of `R` and `A`.  It is `scostLL_fresh_scost` minus
  `scostLL_scost_eq` (c2), localised by `scostLL_sum_support` and `scostLL_clsPat_zero_of_ends`.
* **The class calculus** (private): `localReg6c_ep`, `localReg6c_kp`, `localReg6c_pat`, ... are
  the half-edge pattern and the kept indicator of an edge between abstract classes,
  `localReg6c_dlb A R` is a lower bound of `[elem (X + A)] - [elem (X + R)]` for every residual
  `X` (`0` if `A = R`, `0` if `R` has two colours or two ins or two outs (E6), else `-1` (E0));
  `localReg6c_alone_ge` (`α` alone) and `localReg6c_k2_ge` (`α` in a class, all its edges
  dropped) bound the cost difference below by the abstract row bound `localReg6c_lb`,
  `localReg6c_lb2` on the classes of the named vertices.  The per-class bound does not depend on
  the residuals, so the rows of F §4.5 are inequalities on the equality pattern of at most four
  classes: `localReg6c_row_*` prove them by `rcases eq_or_ne` (every set partition once) and
  `simp`.
* **The three pins** (`T2184-check.lean` section 2, the c3 pins): `scostLL_moveSC`,
  `scostLL_moveOut`, `scostLL_dmove`.  Each is `localReg6c_ll_of_cases`: `α` alone (the
  restriction is the witness; the row lemma), `α` in a class with at most one neighbour (`k ≤
  1`; the placement lemma `scostLL_placement` of c2, through `localReg6b_inst_*_placement`, and
  the split `scostLL_split`), `k = 2` (both `α`-edges dropped; `localReg6c_k2_ge`; the two
  2-cycle collapses, `MoveSC` with `[u] = [v] ≠ [z]` and blue `Dmove` with `[z] = [b] ≠ [a] =
  [v]`, are repaired by `scostLL_repair`, as `localReg6b_inst_moveSC_k2`).
* **Compiled instances** `localReg6c_inst_*`: `Γ_2 = fxyPowGraph 2` and the 2-cycle
  `localReg6b_instCyc` (the repair is forced: the term costs `-2`, the restriction `0`), the
  concrete costs by `localReg6c_scost_ker` (the cost at `Setoid.ker f` as a decidable
  expression, `decide`), the edge, `GG` and weight terms `P3`, `P4`, `D`, `T3` (also at external
  vertices) of `strat_local` by `LGraph.ScostLL.of_perm`.

## Contents (namespace `RBM.Graph`; public: target 1, the pins, the instances; the rest is private)

1. The class calculus on abstract classes.  2. The bridge from the edge lists of a setoid to it.
3. The fresh vertex alone: target 1 and the two row lemmas (`α` alone, `k = 2`).  4. The abstract
rows (the finite case split).  5. The dispatch over the placement of `α`.  6. `MoveSC`.
7. `MoveOut`.  8. `Dmove` (blue and red `q`).  9. The cost at the kernel of a map.
10. Compiled instances (1)-(10) of the ticket.

## Differences from the paper (delta candidates, numbered by the dispatcher)

* `T2203a` (on `T2184c`, the edge and `GG` cases omitted at `B:272-275`): the local lemma for
  `MoveSC`, `MoveOut`, `Dmove` (F §4.5); with c2, every edge, `GG` and weight term of
  `strat_local` reduces to primitives with a proved local lemma (the paper's per-term
  bookkeeping `B:213-262`).
* `T2203b` (extends `T2195b`): the 2-cycle collapse also occurs in `MoveSC` and blue `Dmove` at
  `k = 2` (the terms `P4`, `D`, `T3`, `R7`, `R8` are built from these primitives; the
  restriction is not a witness, instances (2), (5)), repaired by merging the two classes of the
  cycle, never two external ones; `MoveOut` and red `Dmove` never collapse (two colours).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.show false

noncomputable section

namespace RBM.Graph

/-! ## 1. The class calculus on abstract classes -/

section ClassCalculus

variable {Q : Type}

open Classical in
/-- the half-edge pattern at the class `c` of the edge `(σ, circ)` from the class `a` to the class `b`: nothing if the edge is
dropped (uncircled, both ends in one class), else `c-in` at `b` and `c-out` at `a` -/
private def localReg6c_ep (σ circ : Bool) (a b c : Q) : ℕ × ℕ × ℕ × ℕ :=
  if circ = true ∨ a ≠ b then (if b = c then scostLL_hin σ else 0) + (if a = c then scostLL_hout σ else 0) else 0

open Classical in
/-- `1` if the edge `(circ, a, b)` is kept, else `0` -/
private def localReg6c_kp (circ : Bool) (a b : Q) : ℕ := if circ = true ∨ a ≠ b then 1 else 0

open Classical in
/-- a lower bound of `[elem (X + A)] - [elem (X + R)]` that holds for every residual `X` and depends on `A`, `R` only: `0` if
`A = R`, `0` if `R` has two colours or two ins or two outs (then `X + R` is never elementary, (E6)), else `-1` (E0) -/
private def localReg6c_dlb (A R : ℕ × ℕ × ℕ × ℕ) : ℤ :=
  if A = R then 0 else
    if (0 < R.1 + R.2.1 ∧ 0 < R.2.2.1 + R.2.2.2) ∨ 2 ≤ R.2.1 + R.2.2.2 ∨ 2 ≤ R.1 + R.2.2.1 then 0 else -1

private theorem localReg6c_dlb_nonpos (A R : ℕ × ℕ × ℕ × ℕ) : localReg6c_dlb A R ≤ 0 := by
  unfold localReg6c_dlb
  split_ifs <;> omega

/-- the residual `X` of a class is arbitrary: the lower bound `localReg6c_dlb` holds for every `X` -/
private theorem localReg6c_dlb_le (X A R : ℕ × ℕ × ℕ × ℕ) :
    localReg6c_dlb A R ≤ scostLL_el (X + A) - scostLL_el (X + R) := by
  unfold localReg6c_dlb
  split_ifs with h1 h2
  · subst h1
    simp
  · have hR : lwElem (X + R) = false := by
      rcases h2 with ⟨h3, h4⟩ | h3 | h3
      · exact scostLL_elem_E6col X R h3 h4
      · exact scostLL_elem_E6out X R h3
      · exact scostLL_elem_E6in X R h3
    have : scostLL_el (X + R) = 0 := by simp [scostLL_el, hR]
    have := scostLL_el_nonneg (X + A)
    omega
  · exact (scostLL_elem_E0 X R A).1

open Classical in
/-- the pattern of a list of abstract edges `(σ, circ, a, b)` at the class `c` -/
private def localReg6c_pat (L : List (Bool × Bool × Q × Q)) (c : Q) : ℕ × ℕ × ℕ × ℕ :=
  (L.map fun e => localReg6c_ep e.1 e.2.1 e.2.2.1 e.2.2.2 c).sum

open Classical in
/-- the number of kept edges of a list of abstract edges -/
private def localReg6c_keptN (L : List (Bool × Bool × Q × Q)) : ℕ :=
  (L.map fun e => localReg6c_kp e.2.1 e.2.2.1 e.2.2.2).sum

open Classical in
/-- the half-edges at the old classes of the added edges `w → α` (colour `σ`): `c-out` at the class of `w` -/
private def localReg6c_aIn (Ain : List (Bool × Q)) (c : Q) : ℕ × ℕ × ℕ × ℕ :=
  (Ain.map fun x => if x.2 = c then scostLL_hout x.1 else 0).sum

open Classical in
/-- the half-edges at the old classes of the added edges `α → w` (colour `σ`): `c-in` at the class of `w` -/
private def localReg6c_aOut (Aout : List (Bool × Q)) (c : Q) : ℕ × ℕ × ℕ × ℕ :=
  (Aout.map fun x => if x.2 = c then scostLL_hin x.1 else 0).sum

/-- the pattern of the class `{α}` of the fresh vertex alone -/
private def localReg6c_aPat (Ain Aout : List (Bool × Q)) : ℕ × ℕ × ℕ × ℕ :=
  (Ain.map fun x => scostLL_hin x.1).sum + (Aout.map fun x => scostLL_hout x.1).sum

open Classical in
/-- **the lower bound of the row** (`α` alone): `#kept(A) - #kept(R) + 2 n_W + ([elem α] - 2) + Σ_c dlb`, for the removed edges `R`,
the added old edges `A₀`, the added edges `w → α` (`Ain`) and `α → w` (`Aout`), `n_W` waved edges, over the named classes `C` -/
private def localReg6c_lb (R A₀ : List (Bool × Bool × Q × Q)) (Ain Aout : List (Bool × Q)) (nw : ℕ) (C : Finset Q) : ℤ :=
  (localReg6c_keptN A₀ : ℤ) + Ain.length + Aout.length - localReg6c_keptN R + 2 * nw +
    (scostLL_el (localReg6c_aPat Ain Aout) - 2) +
    ∑ c ∈ C, localReg6c_dlb (localReg6c_pat A₀ c + localReg6c_aIn Ain c + localReg6c_aOut Aout c) (localReg6c_pat R c)

open Classical in
/-- **the lower bound of the row** (`α` in a class, all its edges dropped, `k = 2`): `#kept(A₀) - #kept(R) + 2 n_W + Σ_c dlb` -/
private def localReg6c_lb2 (R A₀ : List (Bool × Bool × Q × Q)) (nw : ℕ) (C : Finset Q) : ℤ :=
  (localReg6c_keptN A₀ : ℤ) - localReg6c_keptN R + 2 * nw +
    ∑ c ∈ C, localReg6c_dlb (localReg6c_pat A₀ c) (localReg6c_pat R c)

end ClassCalculus

/-! ## 2. Bridge: kept edges and class patterns of an edge list on a setoid -/

section Bridge

variable {V : Type}

/-- the descriptor of an edge on the classes of `s` -/
private def localReg6c_desc (s : Setoid V) (e : SEdge V) : Bool × Bool × Quotient s × Quotient s :=
  (e.σ, e.circ, Quotient.mk s e.src, Quotient.mk s e.dst)

open Classical in
private theorem localReg6c_clsPat_single (e : SEdge V) (s : Setoid V) (c : Quotient s) :
    scostLL_clsPat [e] s c = localReg6c_ep e.σ e.circ (Quotient.mk s e.src) (Quotient.mk s e.dst) c := by
  unfold scostLL_clsPat localReg6c_ep
  by_cases h : e.circ = true ∨ ¬ s e.src e.dst
  · have hk : scostLL_kept [e] s = [e] := by
      simp only [scostLL_kept, List.filter_cons, List.filter_nil]
      rcases h with h | h <;> simp [h]
    have hne : (e.circ = true ∨ Quotient.mk s e.src ≠ Quotient.mk s e.dst) := by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (fun h' => h (Quotient.exact h'))
    rw [hk, scostLL_halfPat_single]
    simp only [hne, ↓reduceIte]
    by_cases h1 : Quotient.mk s e.dst = c <;> by_cases h2 : Quotient.mk s e.src = c <;> simp [h1, h2]
  · have hk : scostLL_kept [e] s = [] := by
      push Not at h
      simp [scostLL_kept, h.1, h.2]
    have hne : ¬ (e.circ = true ∨ Quotient.mk s e.src ≠ Quotient.mk s e.dst) := by
      push Not at h ⊢
      exact ⟨h.1, Quotient.sound h.2⟩
    rw [hk]
    simp only [hne, ↓reduceIte]
    simp [lwHalfPat]

open Classical in
private theorem localReg6c_kept_single (e : SEdge V) (s : Setoid V) :
    (scostLL_kept [e] s).length = localReg6c_kp e.circ (Quotient.mk s e.src) (Quotient.mk s e.dst) := by
  unfold localReg6c_kp
  by_cases h : e.circ = true ∨ ¬ s e.src e.dst
  · have hk : scostLL_kept [e] s = [e] := by
      simp only [scostLL_kept, List.filter_cons, List.filter_nil]
      rcases h with h | h <;> simp [h]
    have hne : (e.circ = true ∨ Quotient.mk s e.src ≠ Quotient.mk s e.dst) := by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (fun h' => h (Quotient.exact h'))
    rw [hk]
    simp only [hne, ↓reduceIte]
    rfl
  · have hk : scostLL_kept [e] s = [] := by
      push Not at h
      simp [scostLL_kept, h.1, h.2]
    have hne : ¬ (e.circ = true ∨ Quotient.mk s e.src ≠ Quotient.mk s e.dst) := by
      push Not at h ⊢
      exact ⟨h.1, Quotient.sound h.2⟩
    rw [hk]
    simp only [hne, ↓reduceIte]
    rfl

open Classical in
/-- the class pattern of an edge list is the pattern of its descriptors -/
private theorem localReg6c_clsPat_eq (L : List (SEdge V)) (s : Setoid V) (c : Quotient s) :
    scostLL_clsPat L s c = localReg6c_pat (L.map (localReg6c_desc s)) c := by
  induction L with
  | nil => simp [localReg6c_pat, scostLL_clsPat_nil]
  | cons e L ih =>
    have h1 : scostLL_clsPat (e :: L) s c = scostLL_clsPat [e] s c + scostLL_clsPat L s c :=
      scostLL_clsPat_append [e] L s c
    rw [h1, ih, localReg6c_clsPat_single]
    simp [localReg6c_pat, localReg6c_desc]

open Classical in
/-- the number of kept edges of an edge list is that of its descriptors -/
private theorem localReg6c_kept_length (L : List (SEdge V)) (s : Setoid V) :
    (scostLL_kept L s).length = localReg6c_keptN (L.map (localReg6c_desc s)) := by
  induction L with
  | nil => simp [localReg6c_keptN, scostLL_kept]
  | cons e L ih =>
    have h1 : scostLL_kept (e :: L) s = scostLL_kept [e] s ++ scostLL_kept L s := scostLL_kept_append [e] L s
    rw [h1, List.length_append, ih, localReg6c_kept_single]
    simp [localReg6c_keptN, localReg6c_desc]

end Bridge

/-! ## 3. The fresh vertex alone: the exact difference (target 1) -/

section Alone

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- an end of an added edge that is `α` or an old vertex in the named classes `C` is not in the class of `qmap c` for `c ∉ C` -/
private theorem localReg6c_end_ne (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0))
    (C : Finset (Quotient (Setoid.comap (owxEmb 1) s'))) (c : Quotient (Setoid.comap (owxEmb 1) s')) (hc : c ∉ C)
    (w : E ⊕ (I ⊕ Fin 1))
    (hw : w = Sum.inr (Sum.inr 0) ∨ ∃ v, w = owxEmb 1 v ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') v ∈ C) :
    Quotient.mk s' w ≠ localReg6a_qmap (owxEmb 1) s' c := by
  intro h
  rcases hw with rfl | ⟨v, rfl, hv⟩
  · exact (scostLL_qmap_range s' _).1 ⟨c, h.symm⟩ ⟨halone, rfl⟩
  · apply hc
    have h' : localReg6a_qmap (owxEmb 1) s' (Quotient.mk _ v) = localReg6a_qmap (owxEmb 1) s' c := h
    rw [← localReg6a_qmap_injective _ _ h']
    exact hv

open Classical in
/-- **Target 1: the exact difference of the cost of a term `Γ_rest + A + W` with `α` alone and the cost of `Γ` at the restriction**
(F §4.1): `Γ.solid ~ R ++ rest`, `T = Γ_rest.owxExt (owxEmb 1) c A W`; `Δ = #kept(A) - #kept(R) + 2 |W| + ([elem A_α] - 2) +
Σ_{c₀} [c₀ internal] ([elem (X + A_{c₀})] - [elem (X + R_{c₀})])`, `X = rest`'s class pattern, the sum over any `C` that contains
the classes of the old ends of `R` and `A`.  (`+2 |W|`: the waved edges; `-2`: the internal class `{α}`.) -/
theorem localReg6c_alone_diff (Γ : LGraph E I) (rest R : List (SEdge (E ⊕ I))) (hΓ : Γ.solid.Perm (R ++ rest)) (c : ℂ)
    (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0))
    (C : Finset (Quotient (Setoid.comap (owxEmb 1) s')))
    (hR : ∀ e ∈ R, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C)
    (hA : ∀ e ∈ A, ∀ w ∈ [e.src, e.dst], w = Sum.inr (Sum.inr 0) ∨
      ∃ v, w = owxEmb 1 v ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') v ∈ C) :
    (({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) c A W).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') =
      ((scostLL_kept A s').length : ℤ) - ((scostLL_kept R (Setoid.comap (owxEmb 1) s')).length : ℤ) + 2 * (W.length : ℤ) +
        (scostLL_el (scostLL_clsPat A s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2) +
        ∑ c₀ ∈ C, (if c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s') then
          scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) -
            scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
              scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀) else 0) := by
  have h1 := scostLL_fresh_scost ({ Γ with solid := rest } : LGraph E I) c A W s'
  have h2 := scostLL_scost_eq Γ (Setoid.comap (owxEmb 1) s')
  simp only [eq_true halone, ↓reduceIte] at h1
  have hk : (scostLL_kept Γ.solid (Setoid.comap (owxEmb 1) s')).length =
      (scostLL_kept R (Setoid.comap (owxEmb 1) s')).length + (scostLL_kept rest (Setoid.comap (owxEmb 1) s')).length := by
    rw [(scostLL_kept_perm hΓ _).length_eq, scostLL_kept_append, List.length_append]
  have hp : ∀ c₀, scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀ =
      scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ := fun c₀ => by
    rw [scostLL_clsPat_perm hΓ _ c₀, scostLL_clsPat_append]
  have hI : ({ Γ with solid := rest } : LGraph E I).sIntCls (Setoid.comap (owxEmb 1) s') =
      Γ.sIntCls (Setoid.comap (owxEmb 1) s') := rfl
  have hW : ({ Γ with solid := rest } : LGraph E I).waved.length = Γ.waved.length := rfl
  have hsupp : ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'),
      (scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
          scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) -
        scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
          scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀)) =
      ∑ c₀ ∈ C, (if c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s') then
        scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
            scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) -
          scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
            scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀) else 0) := by
    refine scostLL_sum_support _ C _ (fun c₀ hc₀ => ?_)
    have e1 : scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀) = 0 :=
      scostLL_clsPat_zero_of_ends A s' _ (fun e he => ⟨localReg6c_end_ne s' halone C c₀ hc₀ e.src (hA e he e.src (by simp)),
        localReg6c_end_ne s' halone C c₀ hc₀ e.dst (hA e he e.dst (by simp))⟩)
    have e2 : scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀ = 0 :=
      scostLL_clsPat_zero_of_ends R _ c₀ (fun e he => ⟨fun h => hc₀ (h ▸ (hR e he).1), fun h => hc₀ (h ▸ (hR e he).2)⟩)
    rw [e1, e2, sub_self]
  rw [← hsupp]
  have hsplit : ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'),
      (scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
        scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) -
      ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'),
        (scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀) - 2) =
      ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'), (scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
        scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) -
        scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
          scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun c₀ _ => ?_)
    rw [hp c₀, add_comm (scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀)]
    ring
  rw [hI] at h1
  rw [h1, h2, ← hsplit, hk, hW]
  push_cast
  ring

/-- the added edge `w → α` of colour `σ` -/
private def localReg6c_mkIn (x : Bool × (E ⊕ I)) : SEdge (E ⊕ (I ⊕ Fin 1)) :=
  ⟨x.1, false, owxEmb 1 x.2, Sum.inr (Sum.inr 0)⟩

/-- the added edge `α → w` of colour `σ` -/
private def localReg6c_mkOut (x : Bool × (E ⊕ I)) : SEdge (E ⊕ (I ⊕ Fin 1)) :=
  ⟨x.1, false, Sum.inr (Sum.inr 0), owxEmb 1 x.2⟩

private theorem localReg6c_emb_alpha_not (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ x, s' x (Sum.inr (Sum.inr 0)) → x = Sum.inr (Sum.inr 0)) (w : E ⊕ I) :
    ¬ s' (owxEmb 1 w) (Sum.inr (Sum.inr 0)) := fun h => scostLL_emb_ne_alpha w (halone _ h)

private theorem localReg6c_alpha_emb_not (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ x, s' x (Sum.inr (Sum.inr 0)) → x = Sum.inr (Sum.inr 0)) (w : E ⊕ I) :
    ¬ s' (Sum.inr (Sum.inr 0)) (owxEmb 1 w) := fun h => localReg6c_emb_alpha_not s' halone w (s'.symm h)

open Classical in
private theorem localReg6c_kept_mkIn (Ain : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ x, s' x (Sum.inr (Sum.inr 0)) → x = Sum.inr (Sum.inr 0)) :
    scostLL_kept (Ain.map localReg6c_mkIn) s' = Ain.map localReg6c_mkIn := by
  unfold scostLL_kept
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  simp [localReg6c_mkIn, localReg6c_emb_alpha_not s' halone x.2]

open Classical in
private theorem localReg6c_kept_mkOut (Aout : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ x, s' x (Sum.inr (Sum.inr 0)) → x = Sum.inr (Sum.inr 0)) :
    scostLL_kept (Aout.map localReg6c_mkOut) s' = Aout.map localReg6c_mkOut := by
  unfold scostLL_kept
  rw [List.filter_eq_self]
  intro e he
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
  simp [localReg6c_mkOut, localReg6c_alpha_emb_not s' halone x.2]

open Classical in
private theorem localReg6c_clsPat_mkIn (x : Bool × (E ⊕ I)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0))
    (c₀ : Quotient (Setoid.comap (owxEmb 1) s')) :
    scostLL_clsPat [localReg6c_mkIn x] s' (localReg6a_qmap (owxEmb 1) s' c₀) =
      if Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ then scostLL_hout x.1 else 0 := by
  rw [localReg6c_clsPat_single]
  have h1 : Quotient.mk s' (owxEmb 1 x.2) ≠ Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) :=
    fun h => localReg6c_emb_alpha_not s' halone x.2 (Quotient.exact h)
  have h2 : Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) ≠ localReg6a_qmap (owxEmb 1) s' c₀ :=
    fun h => (scostLL_qmap_range s' _).1 ⟨c₀, h.symm⟩ ⟨halone, rfl⟩
  have h3 : (Quotient.mk s' (owxEmb 1 x.2) = localReg6a_qmap (owxEmb 1) s' c₀) ↔
      Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ := by
    have : Quotient.mk s' (owxEmb 1 x.2) = localReg6a_qmap (owxEmb 1) s' (Quotient.mk _ x.2) := rfl
    rw [this]
    exact (localReg6a_qmap_injective _ _).eq_iff
  simp only [localReg6c_ep, localReg6c_mkIn, h1, h2, ne_eq, not_false_eq_true, or_true, ↓reduceIte, h3]
  by_cases h : Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ <;> simp [h]

open Classical in
private theorem localReg6c_clsPat_mkOut (x : Bool × (E ⊕ I)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0))
    (c₀ : Quotient (Setoid.comap (owxEmb 1) s')) :
    scostLL_clsPat [localReg6c_mkOut x] s' (localReg6a_qmap (owxEmb 1) s' c₀) =
      if Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ then scostLL_hin x.1 else 0 := by
  rw [localReg6c_clsPat_single]
  have h1 : Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) ≠ Quotient.mk s' (owxEmb 1 x.2) :=
    fun h => localReg6c_alpha_emb_not s' halone x.2 (Quotient.exact h)
  have h2 : Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) ≠ localReg6a_qmap (owxEmb 1) s' c₀ :=
    fun h => (scostLL_qmap_range s' _).1 ⟨c₀, h.symm⟩ ⟨halone, rfl⟩
  have h3 : (Quotient.mk s' (owxEmb 1 x.2) = localReg6a_qmap (owxEmb 1) s' c₀) ↔
      Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ := by
    have : Quotient.mk s' (owxEmb 1 x.2) = localReg6a_qmap (owxEmb 1) s' (Quotient.mk _ x.2) := rfl
    rw [this]
    exact (localReg6a_qmap_injective _ _).eq_iff
  simp only [localReg6c_ep, localReg6c_mkOut, h1, h2, ne_eq, not_false_eq_true, or_true, ↓reduceIte, h3]
  by_cases h : Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 = c₀ <;> simp [h]

open Classical in
private theorem localReg6c_clsPat_mkIn_alpha (x : Bool × (E ⊕ I)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0)) :
    scostLL_clsPat [localReg6c_mkIn x] s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) = scostLL_hin x.1 := by
  rw [localReg6c_clsPat_single]
  have h1 : Quotient.mk s' (owxEmb 1 x.2) ≠ Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) :=
    fun h => localReg6c_emb_alpha_not s' halone x.2 (Quotient.exact h)
  simp [localReg6c_ep, localReg6c_mkIn, h1, h1.symm]

open Classical in
private theorem localReg6c_clsPat_mkOut_alpha (x : Bool × (E ⊕ I)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0)) :
    scostLL_clsPat [localReg6c_mkOut x] s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) = scostLL_hout x.1 := by
  rw [localReg6c_clsPat_single]
  have h1 : Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) ≠ Quotient.mk s' (owxEmb 1 x.2) :=
    fun h => localReg6c_alpha_emb_not s' halone x.2 (Quotient.exact h)
  simp [localReg6c_ep, localReg6c_mkOut, h1, h1.symm]

open Classical in
private theorem localReg6c_clsPat_mkIn_list (Ain : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0))
    (c₀ : Quotient (Setoid.comap (owxEmb 1) s')) :
    scostLL_clsPat (Ain.map localReg6c_mkIn) s' (localReg6a_qmap (owxEmb 1) s' c₀) =
      localReg6c_aIn (Ain.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀ := by
  induction Ain with
  | nil => simp [localReg6c_aIn, scostLL_clsPat_nil]
  | cons x L ih =>
    have h1 : scostLL_clsPat (x :: L |>.map localReg6c_mkIn) s' (localReg6a_qmap (owxEmb 1) s' c₀) =
        scostLL_clsPat [localReg6c_mkIn x] s' (localReg6a_qmap (owxEmb 1) s' c₀) +
          scostLL_clsPat (L.map localReg6c_mkIn) s' (localReg6a_qmap (owxEmb 1) s' c₀) :=
      scostLL_clsPat_append [localReg6c_mkIn x] (L.map localReg6c_mkIn) s' _
    rw [h1, ih, localReg6c_clsPat_mkIn x s' halone c₀]
    simp [localReg6c_aIn]

open Classical in
private theorem localReg6c_clsPat_mkOut_list (Aout : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0))
    (c₀ : Quotient (Setoid.comap (owxEmb 1) s')) :
    scostLL_clsPat (Aout.map localReg6c_mkOut) s' (localReg6a_qmap (owxEmb 1) s' c₀) =
      localReg6c_aOut (Aout.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀ := by
  induction Aout with
  | nil => simp [localReg6c_aOut, scostLL_clsPat_nil]
  | cons x L ih =>
    have h1 : scostLL_clsPat (x :: L |>.map localReg6c_mkOut) s' (localReg6a_qmap (owxEmb 1) s' c₀) =
        scostLL_clsPat [localReg6c_mkOut x] s' (localReg6a_qmap (owxEmb 1) s' c₀) +
          scostLL_clsPat (L.map localReg6c_mkOut) s' (localReg6a_qmap (owxEmb 1) s' c₀) :=
      scostLL_clsPat_append [localReg6c_mkOut x] (L.map localReg6c_mkOut) s' _
    rw [h1, ih, localReg6c_clsPat_mkOut x s' halone c₀]
    simp [localReg6c_aOut]

open Classical in
private theorem localReg6c_clsPat_mkIn_alpha_list (Ain : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0)) :
    scostLL_clsPat (Ain.map localReg6c_mkIn) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) =
      (Ain.map fun x => scostLL_hin x.1).sum := by
  induction Ain with
  | nil => simp [scostLL_clsPat_nil]
  | cons x L ih =>
    have h1 : scostLL_clsPat (x :: L |>.map localReg6c_mkIn) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) =
        scostLL_clsPat [localReg6c_mkIn x] s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) +
          scostLL_clsPat (L.map localReg6c_mkIn) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) :=
      scostLL_clsPat_append [localReg6c_mkIn x] (L.map localReg6c_mkIn) s' _
    rw [h1, ih, localReg6c_clsPat_mkIn_alpha x s' halone]
    simp

open Classical in
private theorem localReg6c_clsPat_mkOut_alpha_list (Aout : List (Bool × (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ y, s' y (Sum.inr (Sum.inr 0)) → y = Sum.inr (Sum.inr 0)) :
    scostLL_clsPat (Aout.map localReg6c_mkOut) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) =
      (Aout.map fun x => scostLL_hout x.1).sum := by
  induction Aout with
  | nil => simp [scostLL_clsPat_nil]
  | cons x L ih =>
    have h1 : scostLL_clsPat (x :: L |>.map localReg6c_mkOut) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) =
        scostLL_clsPat [localReg6c_mkOut x] s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) +
          scostLL_clsPat (L.map localReg6c_mkOut) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) :=
      scostLL_clsPat_append [localReg6c_mkOut x] (L.map localReg6c_mkOut) s' _
    rw [h1, ih, localReg6c_clsPat_mkOut_alpha x s' halone]
    simp

/-- the ends of the added edges lie in the named classes -/
private theorem localReg6c_hAloc (A₀ : List (SEdge (E ⊕ I))) (Ain Aout : List (Bool × (E ⊕ I)))
    (A : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (hA : A.Perm (A₀.map (SEdge.map (owxEmb 1)) ++ (Ain.map localReg6c_mkIn ++ Aout.map localReg6c_mkOut)))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (C : Finset (Quotient (Setoid.comap (owxEmb 1) s')))
    (hA₀ : ∀ e ∈ A₀, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C)
    (hIn : ∀ x ∈ Ain, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 ∈ C)
    (hOut : ∀ x ∈ Aout, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 ∈ C) :
    ∀ e ∈ A, ∀ w ∈ [e.src, e.dst], w = Sum.inr (Sum.inr 0) ∨
      ∃ v, w = owxEmb 1 v ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') v ∈ C := by
  intro e he w hw
  have he' := hA.mem_iff.1 he
  simp only [List.mem_append, List.mem_map] at he'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases he' with ⟨e₀, he₀, rfl⟩ | ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  · rcases hw with rfl | rfl
    · exact Or.inr ⟨e₀.src, rfl, (hA₀ e₀ he₀).1⟩
    · exact Or.inr ⟨e₀.dst, rfl, (hA₀ e₀ he₀).2⟩
  · rcases hw with rfl | rfl
    · exact Or.inr ⟨x.2, rfl, hIn x hx⟩
    · exact Or.inl rfl
  · rcases hw with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨x.2, rfl, hOut x hx⟩

open Classical in
/-- **The row lemma, `α` alone** (the identity of target 1 and the pattern bound `localReg6c_dlb` per class): for the removed
edges `R`, the added old edges `A₀`, the added edges `w → α` (`Ain`) and `α → w` (`Aout`), the cost of the term exceeds that of the
old graph at the restriction by at least the abstract row bound `localReg6c_lb` on the classes of the named vertices. -/
private theorem localReg6c_alone_ge (Γ : LGraph E I) (rest R A₀ : List (SEdge (E ⊕ I))) (Ain Aout : List (Bool × (E ⊕ I)))
    (hΓ : Γ.solid.Perm (R ++ rest)) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1))))
    (hA : A.Perm (A₀.map (SEdge.map (owxEmb 1)) ++ (Ain.map localReg6c_mkIn ++ Aout.map localReg6c_mkOut)))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0))
    (C : Finset (Quotient (Setoid.comap (owxEmb 1) s')))
    (hR : ∀ e ∈ R, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C)
    (hA₀ : ∀ e ∈ A₀, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C)
    (hIn : ∀ x ∈ Ain, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 ∈ C)
    (hOut : ∀ x ∈ Aout, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2 ∈ C) :
    localReg6c_lb (R.map (localReg6c_desc (Setoid.comap (owxEmb 1) s')))
        (A₀.map (localReg6c_desc (Setoid.comap (owxEmb 1) s')))
        (Ain.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2))
        (Aout.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) W.length C ≤
      (({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) c A W).scost s' -
        Γ.scost (Setoid.comap (owxEmb 1) s') := by
  have hd := localReg6c_alone_diff Γ rest R hΓ c A W s' halone C hR
    (localReg6c_hAloc A₀ Ain Aout A hA s' C hA₀ hIn hOut)
  rw [hd]
  have hkA : (scostLL_kept A s').length =
      (scostLL_kept A₀ (Setoid.comap (owxEmb 1) s')).length + Ain.length + Aout.length := by
    rw [(scostLL_kept_perm hA s').length_eq, scostLL_kept_append, scostLL_kept_append, scostLL_kept_map,
      localReg6c_kept_mkIn Ain s' halone, localReg6c_kept_mkOut Aout s' halone]
    simp only [List.length_append, List.length_map]
    omega
  have hkR := localReg6c_kept_length R (Setoid.comap (owxEmb 1) s')
  have hkA₀ := localReg6c_kept_length A₀ (Setoid.comap (owxEmb 1) s')
  have hpA : ∀ c₀ : Quotient (Setoid.comap (owxEmb 1) s'),
      scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀) =
        localReg6c_pat (A₀.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀ +
          localReg6c_aIn (Ain.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀ +
          localReg6c_aOut (Aout.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀ := by
    intro c₀
    rw [scostLL_clsPat_perm hA s' _, scostLL_clsPat_append, scostLL_clsPat_append, scostLL_clsPat_map,
      localReg6c_clsPat_mkIn_list Ain s' halone c₀, localReg6c_clsPat_mkOut_list Aout s' halone c₀,
      localReg6c_clsPat_eq A₀, add_assoc]
  have hpR : ∀ c₀ : Quotient (Setoid.comap (owxEmb 1) s'),
      scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀ =
        localReg6c_pat (R.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀ := fun c₀ =>
    localReg6c_clsPat_eq R _ c₀
  have hpα : scostLL_clsPat A s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) =
      localReg6c_aPat (Ain.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2))
        (Aout.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) := by
    rw [scostLL_clsPat_perm hA s' _, scostLL_clsPat_append, scostLL_clsPat_append,
      scostLL_clsPat_map_alpha A₀ s' halone, localReg6c_clsPat_mkIn_alpha_list Ain s' halone,
      localReg6c_clsPat_mkOut_alpha_list Aout s' halone, zero_add]
    simp [localReg6c_aPat, List.map_map, Function.comp_def]
  have hsum : ∑ c₀ ∈ C, localReg6c_dlb
        (localReg6c_pat (A₀.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀ +
          localReg6c_aIn (Ain.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀ +
          localReg6c_aOut (Aout.map fun x => (x.1, Quotient.mk (Setoid.comap (owxEmb 1) s') x.2)) c₀)
        (localReg6c_pat (R.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀) ≤
      ∑ c₀ ∈ C, (if c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s') then
          scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
              scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) -
            scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
              scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀) else 0) := by
    refine Finset.sum_le_sum (fun c₀ _ => ?_)
    rw [hpA c₀, hpR c₀]
    split_ifs
    · exact localReg6c_dlb_le _ _ _
    · exact localReg6c_dlb_nonpos _ _
  unfold localReg6c_lb
  rw [hpα, hkA, hkR, hkA₀]
  simp only [List.length_map]
  push_cast
  linarith

open Classical in
/-- **The row lemma, `α` in a class with all its edges dropped** (`k = 2`): the term costs `2 |W|` more than the old graph with the
solid list `A₀ ++ rest` (the old part of the added edges put in), and that graph differs from `Γ` by the surgery on `R`, `A₀` only
(`scostLL_local_diff_C`); the per-class bound is `localReg6c_dlb`. -/
private theorem localReg6c_k2_ge (Γ : LGraph E I) (rest R A₀ : List (SEdge (E ⊕ I))) (Aα : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (hΓ : Γ.solid.Perm (R ++ rest)) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1)))) (W : List (WEdge (E ⊕ (I ⊕ Fin 1))))
    (hA : A.Perm (A₀.map (SEdge.map (owxEmb 1)) ++ Aα)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hna : ¬ ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0))
    (hdrop : scostLL_kept Aα s' = [])
    (C : Finset (Quotient (Setoid.comap (owxEmb 1) s')))
    (hR : ∀ e ∈ R, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C)
    (hA₀ : ∀ e ∈ A₀, Quotient.mk (Setoid.comap (owxEmb 1) s') e.src ∈ C ∧ Quotient.mk (Setoid.comap (owxEmb 1) s') e.dst ∈ C) :
    localReg6c_lb2 (R.map (localReg6c_desc (Setoid.comap (owxEmb 1) s')))
        (A₀.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) W.length C ≤
      (({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) c A W).scost s' -
        Γ.scost (Setoid.comap (owxEmb 1) s') := by
  have hfresh := scostLL_fresh_scost ({ Γ with solid := rest } : LGraph E I) c A W s'
  simp only [eq_false hna, ↓reduceIte, add_zero] at hfresh
  have hkA : (scostLL_kept A s').length = (scostLL_kept A₀ (Setoid.comap (owxEmb 1) s')).length := by
    rw [(scostLL_kept_perm hA s').length_eq, scostLL_kept_append, hdrop, scostLL_kept_map]
    simp
  have hpA : ∀ c₀ : Quotient (Setoid.comap (owxEmb 1) s'),
      scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀) = scostLL_clsPat A₀ (Setoid.comap (owxEmb 1) s') c₀ := by
    intro c₀
    have hα0 : scostLL_clsPat Aα s' (localReg6a_qmap (owxEmb 1) s' c₀) = 0 := by
      unfold scostLL_clsPat
      rw [hdrop]
      simp [lwHalfPat]
    rw [scostLL_clsPat_perm hA s' _, scostLL_clsPat_append, hα0, add_zero, scostLL_clsPat_map]
  have hΓ' : ({ Γ with solid := A₀ ++ rest } : LGraph E I).solid.Perm (A₀ ++ rest) := List.Perm.refl _
  have hdiff := scostLL_local_diff_C Γ ({ Γ with solid := A₀ ++ rest } : LGraph E I) R A₀ rest
    (Setoid.comap (owxEmb 1) s') hΓ hΓ' C hR hA₀
  have hT : (({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) c A W).scost s' =
      ({ Γ with solid := A₀ ++ rest } : LGraph E I).scost (Setoid.comap (owxEmb 1) s') + 2 * (W.length : ℤ) := by
    rw [hfresh, scostLL_scost_eq ({ Γ with solid := A₀ ++ rest } : LGraph E I) (Setoid.comap (owxEmb 1) s')]
    have hk2 : (scostLL_kept (A₀ ++ rest) (Setoid.comap (owxEmb 1) s')).length =
        (scostLL_kept A₀ (Setoid.comap (owxEmb 1) s')).length + (scostLL_kept rest (Setoid.comap (owxEmb 1) s')).length := by
      rw [scostLL_kept_append, List.length_append]
    have hsum : ∑ c₀ ∈ ({ Γ with solid := rest } : LGraph E I).sIntCls (Setoid.comap (owxEmb 1) s'),
        (scostLL_el (scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀ +
          scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) =
        ∑ c₀ ∈ ({ Γ with solid := A₀ ++ rest } : LGraph E I).sIntCls (Setoid.comap (owxEmb 1) s'),
        (scostLL_el (scostLL_clsPat ({ Γ with solid := A₀ ++ rest } : LGraph E I).solid (Setoid.comap (owxEmb 1) s') c₀) - 2) := by
      refine Finset.sum_congr rfl (fun c₀ _ => ?_)
      show scostLL_el (scostLL_clsPat rest _ c₀ + scostLL_clsPat A s' _) - 2 =
        scostLL_el (scostLL_clsPat (A₀ ++ rest) _ c₀) - 2
      rw [hpA c₀, scostLL_clsPat_append, add_comm]
    rw [hsum, hkA, hk2]
    have hw1 : ({ Γ with solid := rest } : LGraph E I).waved.length = Γ.waved.length := rfl
    have hw2 : ({ Γ with solid := A₀ ++ rest } : LGraph E I).waved.length = Γ.waved.length := rfl
    rw [hw1, hw2]
    push_cast
    ring
  have hsumle : ∑ c₀ ∈ C, localReg6c_dlb (localReg6c_pat (A₀.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀)
        (localReg6c_pat (R.map (localReg6c_desc (Setoid.comap (owxEmb 1) s'))) c₀) ≤
      ∑ c₀ ∈ C, (if c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s') then
        scostLL_el (scostLL_clsPat A₀ (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀) -
          scostLL_el (scostLL_clsPat R (Setoid.comap (owxEmb 1) s') c₀ + scostLL_clsPat rest (Setoid.comap (owxEmb 1) s') c₀)
        else 0) := by
    refine Finset.sum_le_sum (fun c₀ _ => ?_)
    rw [← localReg6c_clsPat_eq A₀, ← localReg6c_clsPat_eq R]
    split_ifs
    · rw [add_comm (scostLL_clsPat A₀ _ c₀), add_comm (scostLL_clsPat R _ c₀)]
      exact localReg6c_dlb_le _ _ _
    · exact localReg6c_dlb_nonpos _ _
  have hkA₀ := localReg6c_kept_length A₀ (Setoid.comap (owxEmb 1) s')
  have hkR := localReg6c_kept_length R (Setoid.comap (owxEmb 1) s')
  have hw : ({ Γ with solid := A₀ ++ rest } : LGraph E I).waved.length = Γ.waved.length := rfl
  rw [hT]
  unfold localReg6c_lb2
  rw [hw] at hdiff
  rw [← hkA₀, ← hkR]
  linarith

end Alone


/-! ## 4. The abstract rows: the inequalities of F §4.5 on the equality pattern of the named classes -/

section Rows

variable {Q : Type}

attribute [local simp] localReg6c_lb localReg6c_lb2 localReg6c_pat localReg6c_keptN localReg6c_aIn localReg6c_aOut
  localReg6c_aPat localReg6c_ep localReg6c_kp localReg6c_dlb scostLL_hin scostLL_hout scostLL_el lwElem Prod.ext_iff

open Classical in
/-- `MoveSC`, `α` alone: the three-class rows (F §4.5 `MoveSC` (a)-(c)) on the equality pattern of `[z]`, `[u]`, `[v]`. -/
private theorem localReg6c_row_sc_alone_raw (Z U V : Q) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (true, false, U, Z)] [] [(true, U)] [(true, V)] 1 ({Z, U, V} : Finset Q) := by
  rcases eq_or_ne Z U with rfl | h1
  · rcases eq_or_ne Z V with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z V with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne U V with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `MoveSC`, `k = 2`, `[u] = [v] = [z]`: every edge dropped, `+2`. -/
private theorem localReg6c_row_sc_k2_raw (Z U : Q) (h : Z = U) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (true, false, U, Z)] [] 1 ({Z, U} : Finset Q) := by
  subst h
  simp

open Classical in
/-- `MoveOut`, `α` alone: F §4.5 `MoveOut` (a)-(c) on the equality pattern of `[z]`, `[v]`, `[d]`. -/
private theorem localReg6c_row_mo_alone_raw (Z V D : Q) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (false, false, Z, D)] [] [] [(true, V), (false, D)] 1 ({Z, V, D} : Finset Q) := by
  rcases eq_or_ne Z V with rfl | h1
  · rcases eq_or_ne Z D with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z D with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne V D with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `MoveOut`, `k = 2` (`[v] = [d]`): `U ≠ [z]` costs `0`, `U = [z]` costs `+2`; no collapse. -/
private theorem localReg6c_row_mo_k2_raw (Z U : Q) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (false, false, Z, U)] [] 1 ({Z, U} : Finset Q) := by
  rcases eq_or_ne Z U with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, blue `q`, `α` alone, `p` and `q` uncircled: the 15 partitions of `{z, v, a, b}` (F §4.5). -/
private theorem localReg6c_row_dmb_alone_ff (Z V A B : Q) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (true, false, A, B)] [(true, false, Z, B)] [(true, A)] [(true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  rcases eq_or_ne Z V with rfl | h1
  · rcases eq_or_ne Z A with rfl | h2
    · rcases eq_or_ne Z B with rfl | h3
      · simp
      · simp [h3, h3.symm]
    · rcases eq_or_ne Z B with rfl | h4
      · simp [h2, h2.symm]
      · rcases eq_or_ne A B with rfl | h5
        · simp [h2, h2.symm, h4, h4.symm]
        · simp [h2, h2.symm, h4, h4.symm, h5, h5.symm]
  · rcases eq_or_ne Z A with rfl | h6
    · rcases eq_or_ne Z B with rfl | h7
      · simp [h1, h1.symm]
      · rcases eq_or_ne V B with rfl | h8
        · simp [h1, h1.symm, h7, h7.symm]
        · simp [h1, h1.symm, h7, h7.symm, h8, h8.symm]
    · rcases eq_or_ne V A with rfl | h9
      · rcases eq_or_ne Z B with rfl | h10
        · simp [h1, h1.symm, h6, h6.symm]
        · rcases eq_or_ne V B with rfl | h11
          · simp [h1, h1.symm, h6, h6.symm, h10, h10.symm]
          · simp [h1, h1.symm, h6, h6.symm, h10, h10.symm, h11, h11.symm]
      · rcases eq_or_ne Z B with rfl | h12
        · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm]
        · rcases eq_or_ne V B with rfl | h13
          · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm]
          · rcases eq_or_ne A B with rfl | h14
            · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm, h13, h13.symm]
            · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm, h13, h13.symm, h14, h14.symm]

open Classical in
/-- `Dmove`, blue `q`, `α` alone, `p` uncircled, `q` a light-weight (`a = b`): the 5 partitions of `{z, v, a}`. -/
private theorem localReg6c_row_dmb_alone_ft (Z V A B : Q) (hc : A = B) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (true, true, A, B)] [(true, false, Z, B)] [(true, A)] [(true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hc
  rcases eq_or_ne Z V with rfl | h1
  · rcases eq_or_ne Z A with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z A with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne V A with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, blue `q`, `α` alone, `p` a light-weight (`z = v`), `q` uncircled: the 5 partitions of `{z, a, b}`. -/
private theorem localReg6c_row_dmb_alone_tf (Z V A B : Q) (hcp : Z = V) :
    0 ≤ localReg6c_lb [(true, true, Z, V), (true, false, A, B)] [(true, false, Z, B)] [(true, A)] [(true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hcp
  rcases eq_or_ne Z A with rfl | h1
  · rcases eq_or_ne Z B with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z B with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne A B with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, blue `q`, `α` alone, `p` and `q` light-weights: the 2 partitions of `{z, a}`. -/
private theorem localReg6c_row_dmb_alone_tt (Z V A B : Q) (hcp : Z = V) (hc : A = B) :
    0 ≤ localReg6c_lb [(true, true, Z, V), (true, true, A, B)] [(true, false, Z, B)] [(true, A)] [(true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hcp
  subst hc
  rcases eq_or_ne Z A with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, red `q`, `α` alone, `p` and `q` uncircled: the 15 partitions of `{z, v, a, b}` (F §4.5). -/
private theorem localReg6c_row_dmr_alone_ff (Z V A B : Q) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (false, false, A, B)] [(false, false, A, Z)] [] [(false, B), (true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  rcases eq_or_ne Z V with rfl | h1
  · rcases eq_or_ne Z A with rfl | h2
    · rcases eq_or_ne Z B with rfl | h3
      · simp
      · simp [h3, h3.symm]
    · rcases eq_or_ne Z B with rfl | h4
      · simp [h2, h2.symm]
      · rcases eq_or_ne A B with rfl | h5
        · simp [h2, h2.symm, h4, h4.symm]
        · simp [h2, h2.symm, h4, h4.symm, h5, h5.symm]
  · rcases eq_or_ne Z A with rfl | h6
    · rcases eq_or_ne Z B with rfl | h7
      · simp [h1, h1.symm]
      · rcases eq_or_ne V B with rfl | h8
        · simp [h1, h1.symm, h7, h7.symm]
        · simp [h1, h1.symm, h7, h7.symm, h8, h8.symm]
    · rcases eq_or_ne V A with rfl | h9
      · rcases eq_or_ne Z B with rfl | h10
        · simp [h1, h1.symm, h6, h6.symm]
        · rcases eq_or_ne V B with rfl | h11
          · simp [h1, h1.symm, h6, h6.symm, h10, h10.symm]
          · simp [h1, h1.symm, h6, h6.symm, h10, h10.symm, h11, h11.symm]
      · rcases eq_or_ne Z B with rfl | h12
        · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm]
        · rcases eq_or_ne V B with rfl | h13
          · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm]
          · rcases eq_or_ne A B with rfl | h14
            · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm, h13, h13.symm]
            · simp [h1, h1.symm, h6, h6.symm, h9, h9.symm, h12, h12.symm, h13, h13.symm, h14, h14.symm]

open Classical in
/-- `Dmove`, red `q`, `α` alone, `q` a light-weight: the 5 partitions of `{z, v, a}`. -/
private theorem localReg6c_row_dmr_alone_ft (Z V A B : Q) (hc : A = B) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (false, true, A, B)] [(false, false, A, Z)] [] [(false, B), (true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hc
  rcases eq_or_ne Z V with rfl | h1
  · rcases eq_or_ne Z A with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z A with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne V A with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, red `q`, `α` alone, `p` a light-weight: the 5 partitions of `{z, a, b}`. -/
private theorem localReg6c_row_dmr_alone_tf (Z V A B : Q) (hcp : Z = V) :
    0 ≤ localReg6c_lb [(true, true, Z, V), (false, false, A, B)] [(false, false, A, Z)] [] [(false, B), (true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hcp
  rcases eq_or_ne Z A with rfl | h1
  · rcases eq_or_ne Z B with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z B with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne A B with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, red `q`, `α` alone, `p` and `q` light-weights: the 2 partitions of `{z, a}`. -/
private theorem localReg6c_row_dmr_alone_tt (Z V A B : Q) (hcp : Z = V) (hc : A = B) :
    0 ≤ localReg6c_lb [(true, true, Z, V), (false, true, A, B)] [(false, false, A, Z)] [] [(false, B), (true, V)] 1 ({Z, V, A, B} : Finset Q) := by
  subst hcp
  subst hc
  rcases eq_or_ne Z A with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, blue `q`, `k = 2` (`[a] = [v] = U`), `p`, `q` uncircled: `Z, U, B` distinct, `Z = U ≠ B`, `B = U ≠ Z`, all equal; the collapse `Z = B ≠ U` is excluded (repair). -/
private theorem localReg6c_row_dmb_k2_ff (Z U B : Q) (hnc : ¬ (Z = B ∧ Z ≠ U)) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (true, false, U, B)] [(true, false, Z, B)] 1 ({Z, U, B} : Finset Q) := by
  rcases eq_or_ne Z U with rfl | h1
  · rcases eq_or_ne Z B with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z B with rfl | h3
    · exact absurd ⟨rfl, h1⟩ hnc
    · rcases eq_or_ne U B with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, blue `q`, `k = 2`, `q` a light-weight. -/
private theorem localReg6c_row_dmb_k2_ft (Z U B : Q) (hc : U = B) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (true, true, U, B)] [(true, false, Z, B)] 1 ({Z, U, B} : Finset Q) := by
  subst hc
  rcases eq_or_ne Z U with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, blue `q`, `k = 2`, `p` a light-weight. -/
private theorem localReg6c_row_dmb_k2_tf (Z U B : Q) (hcp : Z = U) :
    0 ≤ localReg6c_lb2 [(true, true, Z, U), (true, false, U, B)] [(true, false, Z, B)] 1 ({Z, U, B} : Finset Q) := by
  subst hcp
  rcases eq_or_ne Z B with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, blue `q`, `k = 2`, `p` and `q` light-weights. -/
private theorem localReg6c_row_dmb_k2_tt (Z U B : Q) (hcp : Z = U) (hc : Z = B) :
    0 ≤ localReg6c_lb2 [(true, true, Z, U), (true, true, U, B)] [(true, false, Z, B)] 1 ({Z, U, B} : Finset Q) := by
  subst hcp
  subst hc
  simp

open Classical in
/-- `Dmove`, red `q`, `k = 2` (`[b] = [v] = U`), `p`, `q` uncircled: `A, Z, U` distinct, `A = Z ≠ U`, `Z = U ≠ A`, `A = U ≠ Z`, all equal; never a collapse. -/
private theorem localReg6c_row_dmr_k2_ff (Z A U : Q) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (false, false, A, U)] [(false, false, A, Z)] 1 ({Z, A, U} : Finset Q) := by
  rcases eq_or_ne Z A with rfl | h1
  · rcases eq_or_ne Z U with rfl | h2
    · simp
    · simp [h2, h2.symm]
  · rcases eq_or_ne Z U with rfl | h3
    · simp [h1, h1.symm]
    · rcases eq_or_ne A U with rfl | h4
      · simp [h1, h1.symm, h3, h3.symm]
      · simp [h1, h1.symm, h3, h3.symm, h4, h4.symm]

open Classical in
/-- `Dmove`, red `q`, `k = 2`, `q` a light-weight. -/
private theorem localReg6c_row_dmr_k2_ft (Z A U : Q) (hc : A = U) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (false, true, A, U)] [(false, false, A, Z)] 1 ({Z, A, U} : Finset Q) := by
  subst hc
  rcases eq_or_ne Z A with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, red `q`, `k = 2`, `p` a light-weight. -/
private theorem localReg6c_row_dmr_k2_tf (Z A U : Q) (hcp : Z = U) :
    0 ≤ localReg6c_lb2 [(true, true, Z, U), (false, false, A, U)] [(false, false, A, Z)] 1 ({Z, A, U} : Finset Q) := by
  subst hcp
  rcases eq_or_ne Z A with rfl | h1
  · simp
  · simp [h1, h1.symm]

open Classical in
/-- `Dmove`, red `q`, `k = 2`, `p` and `q` light-weights. -/
private theorem localReg6c_row_dmr_k2_tt (Z A U : Q) (hcp : Z = U) (hc : A = Z) :
    0 ≤ localReg6c_lb2 [(true, true, Z, U), (false, true, A, U)] [(false, false, A, Z)] 1 ({Z, A, U} : Finset Q) := by
  subst hcp
  subst hc
  simp

open Classical in
/-- the row lemma of `MoveSC`, `α` alone, for any finset of the named classes. -/
private theorem localReg6c_row_sc_alone (Z U V : Q) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = U ∨ x = V) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (true, false, U, Z)] [] [(true, U)] [(true, V)] 1 C := by
  obtain rfl : C = {Z, U, V} := Finset.ext (fun x => by simpa using hC x)
  exact localReg6c_row_sc_alone_raw Z U V

open Classical in
/-- the row lemma of `MoveSC`, `k = 2`, `[z] = [u] = [v]`. -/
private theorem localReg6c_row_sc_k2 (Z U : Q) (h : Z = U) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = U) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (true, false, U, Z)] [] 1 C := by
  obtain rfl : C = {Z, U} := Finset.ext (fun x => by simpa using hC x)
  exact localReg6c_row_sc_k2_raw Z U h

open Classical in
/-- the row lemma of `MoveOut`, `α` alone. -/
private theorem localReg6c_row_mo_alone (Z V D : Q) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = D) :
    0 ≤ localReg6c_lb [(true, false, Z, V), (false, false, Z, D)] [] [] [(true, V), (false, D)] 1 C := by
  obtain rfl : C = {Z, V, D} := Finset.ext (fun x => by simpa using hC x)
  exact localReg6c_row_mo_alone_raw Z V D

open Classical in
/-- the row lemma of `MoveOut`, `k = 2` (no collapse). -/
private theorem localReg6c_row_mo_k2 (Z U : Q) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = U) :
    0 ≤ localReg6c_lb2 [(true, false, Z, U), (false, false, Z, U)] [] 1 C := by
  obtain rfl : C = {Z, U} := Finset.ext (fun x => by simpa using hC x)
  exact localReg6c_row_mo_k2_raw Z U

open Classical in
/-- the row lemma of blue `Dmove`, `α` alone, for the flags `cp`, `c` (light-weight iff the class equation holds). -/
private theorem localReg6c_row_dmb_alone (Z V A B : Q) (cp c : Bool) (hcp : cp = true → Z = V) (hc : c = true → A = B) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = A ∨ x = B) :
    0 ≤ localReg6c_lb [(true, cp, Z, V), (true, c, A, B)] [(true, false, Z, B)] [(true, A)] [(true, V)] 1 C := by
  obtain rfl : C = {Z, V, A, B} := Finset.ext (fun x => by simpa using hC x)
  cases cp <;> cases c
  · exact localReg6c_row_dmb_alone_ff Z V A B
  · exact localReg6c_row_dmb_alone_ft Z V A B (hc rfl)
  · exact localReg6c_row_dmb_alone_tf Z V A B (hcp rfl)
  · exact localReg6c_row_dmb_alone_tt Z V A B (hcp rfl) (hc rfl)

open Classical in
/-- the row lemma of red `Dmove`, `α` alone. -/
private theorem localReg6c_row_dmr_alone (Z V A B : Q) (cp c : Bool) (hcp : cp = true → Z = V) (hc : c = true → A = B) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = A ∨ x = B) :
    0 ≤ localReg6c_lb [(true, cp, Z, V), (false, c, A, B)] [(false, false, A, Z)] [] [(false, B), (true, V)] 1 C := by
  obtain rfl : C = {Z, V, A, B} := Finset.ext (fun x => by simpa using hC x)
  cases cp <;> cases c
  · exact localReg6c_row_dmr_alone_ff Z V A B
  · exact localReg6c_row_dmr_alone_ft Z V A B (hc rfl)
  · exact localReg6c_row_dmr_alone_tf Z V A B (hcp rfl)
  · exact localReg6c_row_dmr_alone_tt Z V A B (hcp rfl) (hc rfl)

open Classical in
/-- the row lemma of blue `Dmove`, `k = 2`, outside the collapse `[z] = [b] ≠ U`. -/
private theorem localReg6c_row_dmb_k2 (Z U B : Q) (cp c : Bool) (hcp : cp = true → Z = U) (hc : c = true → U = B) (hnc : ¬ (Z = B ∧ Z ≠ U)) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = U ∨ x = B) :
    0 ≤ localReg6c_lb2 [(true, cp, Z, U), (true, c, U, B)] [(true, false, Z, B)] 1 C := by
  obtain rfl : C = {Z, U, B} := Finset.ext (fun x => by simpa using hC x)
  cases cp <;> cases c
  · exact localReg6c_row_dmb_k2_ff Z U B hnc
  · exact localReg6c_row_dmb_k2_ft Z U B (hc rfl)
  · exact localReg6c_row_dmb_k2_tf Z U B (hcp rfl)
  · have h1 := hcp rfl
    subst h1
    exact localReg6c_row_dmb_k2_tt Z Z B rfl (hc rfl)

open Classical in
/-- the row lemma of red `Dmove`, `k = 2`. -/
private theorem localReg6c_row_dmr_k2 (Z A U : Q) (cp c : Bool) (hcp : cp = true → Z = U) (hc : c = true → A = U) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = A ∨ x = U) :
    0 ≤ localReg6c_lb2 [(true, cp, Z, U), (false, c, A, U)] [(false, false, A, Z)] 1 C := by
  obtain rfl : C = {Z, A, U} := Finset.ext (fun x => by simpa using hC x)
  cases cp <;> cases c
  · exact localReg6c_row_dmr_k2_ff Z A U
  · exact localReg6c_row_dmr_k2_ft Z A U (hc rfl)
  · exact localReg6c_row_dmr_k2_tf Z A U (hcp rfl)
  · have h1 := hcp rfl
    subst h1
    exact localReg6c_row_dmr_k2_tt Z A Z rfl (hc rfl)

open Classical in
private theorem localReg6c_row_sc_k2' (Z U V : Q) (hVU : V = U) (hZU : Z = U) (C : Finset Q)
    (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = U ∨ x = V) :
    0 ≤ localReg6c_lb2 [(true, false, Z, V), (true, false, U, Z)] [] 1 C := by
  subst hVU
  subst hZU
  obtain rfl : C = {Z} := Finset.ext (fun x => by simpa using hC x)
  simp

open Classical in
private theorem localReg6c_row_mo_k2' (Z V D : Q) (hVD : V = D) (C : Finset Q)
    (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = D) :
    0 ≤ localReg6c_lb2 [(true, false, Z, V), (false, false, Z, D)] [] 1 C := by
  subst hVD
  exact localReg6c_row_mo_k2 Z V C (fun x => by simpa using hC x)

open Classical in
private theorem localReg6c_row_dmb_k2' (Z V A B : Q) (cp c : Bool) (hAV : A = V) (hcp : cp = true → Z = V)
    (hc : c = true → A = B) (hnc : ¬ (Z = B ∧ Z ≠ V)) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = A ∨ x = B) :
    0 ≤ localReg6c_lb2 [(true, cp, Z, V), (true, c, A, B)] [(true, false, Z, B)] 1 C := by
  subst hAV
  exact localReg6c_row_dmb_k2 Z A B cp c hcp hc hnc C (fun x => by simpa using hC x)

open Classical in
private theorem localReg6c_row_dmr_k2' (Z V A B : Q) (cp c : Bool) (hBV : B = V) (hcp : cp = true → Z = V)
    (hc : c = true → A = B) (C : Finset Q) (hC : ∀ x, x ∈ C ↔ x = Z ∨ x = V ∨ x = A ∨ x = B) :
    0 ≤ localReg6c_lb2 [(true, cp, Z, V), (false, c, A, B)] [(false, false, A, Z)] 1 C := by
  subst hBV
  exact localReg6c_row_dmr_k2 Z A B cp c hcp hc C (fun x => by rw [hC x]; tauto)

end Rows


/-! ## 5. The dispatch of the local lemma over the placement of the fresh vertex -/

section Dispatch

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- **The three cases of the local lemma for a primitive with a fresh vertex `α`** (F §4.3): `α` alone (the restriction is the
witness), `α` in a class with at most one of its neighbours (`k ≤ 1`: the placement lemma reduces to `α` alone; the splitting does
not change the restriction nor the relation on the external vertices), and the remaining case `K2` (`k = 2`). -/
private theorem localReg6c_ll_of_cases (Γ : LGraph E I) (T : LGraph E (I ⊕ Fin 1))
    (K2 : Setoid (E ⊕ (I ⊕ Fin 1)) → Prop)
    (halone : ∀ s' : Setoid (E ⊕ (I ⊕ Fin 1)), (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) →
      Γ.scost (Setoid.comap (owxEmb 1) s') ≤ T.scost s')
    (hplace : ∀ s' : Setoid (E ⊕ (I ⊕ Fin 1)), ¬ K2 s' →
      T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s') ≤ T.scost s')
    (hk2 : ∀ s' : Setoid (E ⊕ (I ⊕ Fin 1)), ¬ (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) → K2 s' →
      ∃ s₀ : Setoid (E ⊕ I), (∀ a b : E, ¬ s' (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧
        Γ.scost s₀ ≤ T.scost s') :
    LGraph.ScostLL Γ T := by
  intro s'
  by_cases ha : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · exact ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, halone s' ha⟩
  · by_cases hK : K2 s'
    · exact hk2 s' ha hK
    · have h1 := hplace s' hK
      have h2 := halone (scostLL_split (Sum.inr (Sum.inr 0)) s') (scostLL_split_alone _ s')
      rw [scostLL_split_comap] at h2
      exact ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, h2.trans h1⟩

end Dispatch

/-! ## 6. `MoveSC` -/

section MoveSC

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- `MoveSC(z; u, v)`, `α` alone (F §4.5 `MoveSC` (a)-(c)): the restriction costs at most as much as the term. -/
private theorem localReg6c_moveSC_alone (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    Γ.scost (Setoid.comap (owxEmb 1) s') ≤ (lwPrimMoveSC Γ rest z u v).scost s' := by
  have h := localReg6c_alone_ge Γ rest [⟨true, false, z, v⟩, ⟨true, false, u, z⟩] [] [(true, u)] [(true, v)] hperm 1
    [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' halone
    {Quotient.mk _ z, Quotient.mk _ u, Quotient.mk _ v}
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp)
    (by simp) (by simp) (by simp)
  have key := localReg6c_row_sc_alone (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') u) (Quotient.mk (Setoid.comap (owxEmb 1) s') v)
    {Quotient.mk _ z, Quotient.mk _ u, Quotient.mk _ v} (fun x => by simp)
  have h2 : 0 ≤ (lwPrimMoveSC Γ rest z u v).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') := le_trans key h
  linarith


open Classical in
/-- **The local lemma for `MoveSC`** (F §4.5 `MoveSC`; the pin `ScostLLMoveSCPin` of `T2184-check.lean`): `α` alone (rows (a)-(c) by
the row lemma), `k ≤ 1` (the placement lemma), `k = 2` (`[u] = [v] =: U`; `U = [z]`: every edge dropped, the restriction is the
witness; `U ≠ [z]`: the 2-cycle collapse, the repair of `localReg6b_inst_moveSC_k2`). -/
theorem scostLL_moveSC (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (hu : u ≠ z) (hv : z ≠ v)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest)) :
    LGraph.ScostLL Γ (lwPrimMoveSC Γ rest z u v) := by
  refine localReg6c_ll_of_cases Γ (lwPrimMoveSC Γ rest z u v)
    (fun s' => s' (owxEmb 1 u) (Sum.inr (Sum.inr 0)) ∧ s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v)) ?_ ?_ ?_
  · intro s' halone
    exact localReg6c_moveSC_alone Γ rest z u v hperm s' halone
  · intro s' hk
    exact localReg6b_inst_moveSC_placement Γ rest z u v s' hk
  · intro s' hna hk
    obtain ⟨hu', hv'⟩ := hk
    by_cases huz : s' (owxEmb 1 u) (owxEmb 1 z)
    · refine ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, ?_⟩
      have h := localReg6c_k2_ge Γ rest [⟨true, false, z, v⟩, ⟨true, false, u, z⟩] [] 
        [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] hperm 1
        [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
        [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' hna
        (by simp [scostLL_kept, hu', hv'])
        {Quotient.mk _ z, Quotient.mk _ u, Quotient.mk _ v}
        (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl <;> simp)
        (by simp)
      have hVU : Quotient.mk (Setoid.comap (owxEmb 1) s') v = Quotient.mk (Setoid.comap (owxEmb 1) s') u :=
        Quotient.sound (show (Setoid.comap (owxEmb 1) s') v u from s'.symm (s'.trans hu' hv'))
      have hZU : Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') u :=
        Quotient.sound (show (Setoid.comap (owxEmb 1) s') z u from s'.symm huz)
      have key := localReg6c_row_sc_k2' (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
        (Quotient.mk (Setoid.comap (owxEmb 1) s') u) (Quotient.mk (Setoid.comap (owxEmb 1) s') v)
        hVU hZU {Quotient.mk _ z, Quotient.mk _ u, Quotient.mk _ v} (fun x => by simp)
      have h2 : 0 ≤ (lwPrimMoveSC Γ rest z u v).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') := le_trans key h
      linarith
    · obtain ⟨s₀, hsep, hcost⟩ := localReg6b_inst_moveSC_k2 Γ rest z u v hperm s' hu' hv' huz
      exact ⟨s₀, hsep, hcost⟩

end MoveSC

/-! ## 7. `MoveOut` -/

section MoveOut

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- `MoveOut(z; v, d)`, `α` alone (F §4.5 `MoveOut` (a)-(c)): the restriction costs at most as much as the term. -/
private theorem localReg6c_moveOut_alone (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨false, false, z, d⟩ :: rest))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    Γ.scost (Setoid.comap (owxEmb 1) s') ≤ (lwPrimMoveOut Γ rest z v d).scost s' := by
  have h := localReg6c_alone_ge Γ rest [⟨true, false, z, v⟩, ⟨false, false, z, d⟩] [] [] [(true, v), (false, d)] hperm 1
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 d⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' halone
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ d}
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp)
    (by simp) (by simp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp)
  have key := localReg6c_row_mo_alone (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') d)
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ d} (fun x => by simp)
  have h2 : 0 ≤ (lwPrimMoveOut Γ rest z v d).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') := le_trans key h
  linarith

open Classical in
/-- **The local lemma for `MoveOut`** (F §4.5 `MoveOut`; the pin `ScostLLMoveOutPin` of `T2184-check.lean`): the restriction is the
witness in every case (`α` alone by the row lemma, `k ≤ 1` by the placement lemma, `k = 2` by the row lemma for the dropped
`α`-edges: two colours, so no collapse). -/
theorem scostLL_moveOut (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I) (hv : z ≠ v) (hd : z ≠ d)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨false, false, z, d⟩ :: rest)) :
    LGraph.ScostLL Γ (lwPrimMoveOut Γ rest z v d) := by
  refine localReg6c_ll_of_cases Γ (lwPrimMoveOut Γ rest z v d)
    (fun s' => s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v) ∧ s' (Sum.inr (Sum.inr 0)) (owxEmb 1 d)) ?_ ?_ ?_
  · intro s' halone
    exact localReg6c_moveOut_alone Γ rest z v d hperm s' halone
  · intro s' hk
    exact localReg6b_inst_moveOut_placement Γ rest z v d s' hk
  · intro s' hna hk
    obtain ⟨hv', hd'⟩ := hk
    refine ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, ?_⟩
    have h := localReg6c_k2_ge Γ rest [⟨true, false, z, v⟩, ⟨false, false, z, d⟩] []
      [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 d⟩] hperm 1
      [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 d⟩]
      [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' hna
      (by simp [scostLL_kept, hv', hd'])
      {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ d}
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp)
      (by simp)
    have hVD : Quotient.mk (Setoid.comap (owxEmb 1) s') v = Quotient.mk (Setoid.comap (owxEmb 1) s') d :=
      Quotient.sound (show (Setoid.comap (owxEmb 1) s') v d from s'.trans (s'.symm hv') hd')
    have key := localReg6c_row_mo_k2' (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
      (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') d)
      hVD {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ d} (fun x => by simp)
    have h2 : 0 ≤ (lwPrimMoveOut Γ rest z v d).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') := le_trans key h
    linarith

end MoveOut

/-! ## 8. `Dmove` -/

section Dmove

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- `Dmove(z; p, q)` with a blue `q = a → b`, `α` alone (F §4.5 "`Dmove`, blue `q`": the 15 partitions of `{z, v, a, b}`). -/
private theorem localReg6c_dmoveBlue_alone (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp c : Bool)
    (a b : E ⊕ I) (hcp : z = v ↔ cp = true) (hc : a = b ↔ c = true)
    (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: ⟨true, c, a, b⟩ :: rest))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    Γ.scost (Setoid.comap (owxEmb 1) s') ≤ (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩).scost s' := by
  have h := localReg6c_alone_ge Γ rest [⟨true, cp, z, v⟩, ⟨true, c, a, b⟩] [⟨true, false, z, b⟩] [(true, a)] [(true, v)] hperm 1
    [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, owxEmb 1 z, owxEmb 1 b⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.swap _ _ _).symm s' halone
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b}
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp)
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl <;> simp)
    (by simp) (by simp)
  have hcp' : cp = true → Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
    fun h => by rw [hcp.2 h]
  have hc' : c = true → Quotient.mk (Setoid.comap (owxEmb 1) s') a = Quotient.mk (Setoid.comap (owxEmb 1) s') b :=
    fun h => by rw [hc.2 h]
  have key := localReg6c_row_dmb_alone (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') a)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') b) cp c hcp' hc'
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b} (fun x => by simp)
  have h2 : 0 ≤ (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') :=
    le_trans key h
  linarith

open Classical in
/-- `Dmove(z; p, q)` with a red `q = a → b`, `α` alone (F §4.5 "`Dmove`, red `q`": the 15 partitions of `{z, v, a, b}`). -/
private theorem localReg6c_dmoveRed_alone (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp c : Bool)
    (a b : E ⊕ I) (hcp : z = v ↔ cp = true) (hc : a = b ↔ c = true)
    (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: ⟨false, c, a, b⟩ :: rest))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    Γ.scost (Setoid.comap (owxEmb 1) s') ≤ (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩).scost s' := by
  have h := localReg6c_alone_ge Γ rest [⟨true, cp, z, v⟩, ⟨false, c, a, b⟩] [⟨false, false, a, z⟩] [] [(false, b), (true, v)] hperm 1
    [⟨false, false, owxEmb 1 a, owxEmb 1 z⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 b⟩,
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' halone
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b}
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> simp)
    (by
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl <;> simp)
    (by simp)
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp)
  have hcp' : cp = true → Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
    fun h => by rw [hcp.2 h]
  have hc' : c = true → Quotient.mk (Setoid.comap (owxEmb 1) s') a = Quotient.mk (Setoid.comap (owxEmb 1) s') b :=
    fun h => by rw [hc.2 h]
  have key := localReg6c_row_dmr_alone (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') a)
    (Quotient.mk (Setoid.comap (owxEmb 1) s') b) cp c hcp' hc'
    {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b} (fun x => by simp)
  have h2 : 0 ≤ (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') :=
    le_trans key h
  linarith

open Classical in
/-- **`Dmove` with a blue `q`: the local lemma** (F §4.5 "`Dmove`, blue `q`"; `α` alone: 15 rows; `k ≤ 1`: placement; `k = 2`
(`[a] = [v] =: U`): five rows, and the 2-cycle collapse `[z] = [b] ≠ U` (`z ≠ v`, `a ≠ b` follow from the classes, so `p` and `q` are
uncircled edges; all three added edges are dropped), repaired by `scostLL_repair`). -/
private theorem localReg6c_dmoveBlue (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp c : Bool)
    (a b : E ⊕ I) (hcp : z = v ↔ cp = true) (hc : a = b ↔ c = true)
    (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: ⟨true, c, a, b⟩ :: rest)) :
    LGraph.ScostLL Γ (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩) := by
  refine localReg6c_ll_of_cases Γ (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩)
    (fun s' => s' (owxEmb 1 a) (Sum.inr (Sum.inr 0)) ∧ s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v)) ?_ ?_ ?_
  · intro s' halone
    exact localReg6c_dmoveBlue_alone Γ rest z v cp c a b hcp hc hperm s' halone
  · intro s' hk
    exact localReg6b_inst_dmoveBlue_placement Γ rest z v ⟨true, c, a, b⟩ rfl s' hk
  · intro s' hna hk
    obtain ⟨ha', hv'⟩ := hk
    have hAV : Quotient.mk (Setoid.comap (owxEmb 1) s') a = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
      Quotient.sound (show (Setoid.comap (owxEmb 1) s') a v from s'.trans ha' hv')
    by_cases hcol : Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') b ∧
        Quotient.mk (Setoid.comap (owxEmb 1) s') z ≠ Quotient.mk (Setoid.comap (owxEmb 1) s') v
    · obtain ⟨hZB, hZV⟩ := hcol
      have hzv : z ≠ v := fun h => hZV (by rw [h])
      have hab : a ≠ b := fun h => hZV (hZB.trans ((congrArg (Quotient.mk (Setoid.comap (owxEmb 1) s')) h.symm).trans hAV))
      have hcp0 : cp = false := by
        cases cp
        · rfl
        · exact absurd (hcp.2 rfl) hzv
      have hc0 : c = false := by
        cases c
        · rfl
        · exact absurd (hc.2 rfl) hab
      subst hcp0
      subst hc0
      have hzb' : (Setoid.comap (owxEmb 1) s') z b := Quotient.exact hZB
      have hzb : s' (owxEmb 1 z) (owxEmb 1 b) := hzb'
      have hAk : scostLL_kept [(⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1))),
          ⟨true, false, owxEmb 1 z, owxEmb 1 b⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] s' = [] := by
        simp [scostLL_kept, ha', hv', hzb]
      have hT := scostLL_fresh_dropped ({ Γ with solid := rest } : LGraph E I) 1
        [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, owxEmb 1 z, owxEmb 1 b⟩,
          ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
        [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] s' hAk hna
      obtain ⟨s₁, -, hsep, hcost⟩ := scostLL_repair Γ rest true z v a b v (Setoid.comap (owxEmb 1) s') hperm
        ((Setoid.comap (owxEmb 1) s').refl' v) (Quotient.exact hAV.symm) (Quotient.exact hZB)
        (fun h => hZV (Quotient.sound ((Setoid.comap (owxEmb 1) s').symm h)))
      refine ⟨s₁, fun x y h => hsep x y (fun hc' => h hc'), ?_⟩
      have e : lwPrimDmove Γ rest z v ⟨true, false, a, b⟩ = ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
          [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, owxEmb 1 z, owxEmb 1 b⟩,
            ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] := rfl
      rw [e, hT]
      simp only [List.length_singleton, Nat.cast_one] at *
      linarith
    · refine ⟨Setoid.comap (owxEmb 1) s', fun x y h hc' => h hc', ?_⟩
      have h := localReg6c_k2_ge Γ rest [⟨true, cp, z, v⟩, ⟨true, c, a, b⟩] [⟨true, false, z, b⟩]
        [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] hperm 1
        [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, owxEmb 1 z, owxEmb 1 b⟩,
          ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
        [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.swap _ _ _).symm s' hna
        (by simp [scostLL_kept, ha', hv'])
        {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b}
        (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl <;> simp)
        (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl <;> simp)
      have hcp' : cp = true → Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
        fun h => by rw [hcp.2 h]
      have hc' : c = true → Quotient.mk (Setoid.comap (owxEmb 1) s') a = Quotient.mk (Setoid.comap (owxEmb 1) s') b :=
        fun h => by rw [hc.2 h]
      have key := localReg6c_row_dmb_k2' (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
        (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') a)
        (Quotient.mk (Setoid.comap (owxEmb 1) s') b) cp c hAV hcp' hc' hcol
        {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b} (fun x => by simp)
      have h2 : 0 ≤ (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') :=
        le_trans key h
      linarith

open Classical in
/-- **`Dmove` with a red `q`: the local lemma** (F §4.5 "`Dmove`, red `q`"; `α` alone: 15 rows; `k ≤ 1`: placement; `k = 2`
(`[b] = [v] =: U`): five rows, never a collapse -- two colours). -/
private theorem localReg6c_dmoveRed (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp c : Bool)
    (a b : E ⊕ I) (hcp : z = v ↔ cp = true) (hc : a = b ↔ c = true)
    (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: ⟨false, c, a, b⟩ :: rest)) :
    LGraph.ScostLL Γ (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩) := by
  refine localReg6c_ll_of_cases Γ (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩)
    (fun s' => s' (Sum.inr (Sum.inr 0)) (owxEmb 1 b) ∧ s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v)) ?_ ?_ ?_
  · intro s' halone
    exact localReg6c_dmoveRed_alone Γ rest z v cp c a b hcp hc hperm s' halone
  · intro s' hk
    exact localReg6b_inst_dmoveRed_placement Γ rest z v ⟨false, c, a, b⟩ rfl s' hk
  · intro s' hna hk
    obtain ⟨hb', hv'⟩ := hk
    refine ⟨Setoid.comap (owxEmb 1) s', fun x y h hc' => h hc', ?_⟩
    have hBV : Quotient.mk (Setoid.comap (owxEmb 1) s') b = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
      Quotient.sound (show (Setoid.comap (owxEmb 1) s') b v from s'.trans (s'.symm hb') hv')
    have h := localReg6c_k2_ge Γ rest [⟨true, cp, z, v⟩, ⟨false, c, a, b⟩] [⟨false, false, a, z⟩]
      [⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 b⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] hperm 1
      [⟨false, false, owxEmb 1 a, owxEmb 1 z⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 b⟩,
        ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
      [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] (List.Perm.refl _) s' hna
      (by simp [scostLL_kept, hb', hv'])
      {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b}
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp)
      (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl <;> simp)
    have hcp' : cp = true → Quotient.mk (Setoid.comap (owxEmb 1) s') z = Quotient.mk (Setoid.comap (owxEmb 1) s') v :=
      fun h => by rw [hcp.2 h]
    have hc' : c = true → Quotient.mk (Setoid.comap (owxEmb 1) s') a = Quotient.mk (Setoid.comap (owxEmb 1) s') b :=
      fun h => by rw [hc.2 h]
    have key := localReg6c_row_dmr_k2' (Quotient.mk (Setoid.comap (owxEmb 1) s') z)
      (Quotient.mk (Setoid.comap (owxEmb 1) s') v) (Quotient.mk (Setoid.comap (owxEmb 1) s') a)
      (Quotient.mk (Setoid.comap (owxEmb 1) s') b) cp c hBV hcp' hc'
      {Quotient.mk _ z, Quotient.mk _ v, Quotient.mk _ a, Quotient.mk _ b} (fun x => by simp)
    have h2 : 0 ≤ (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩).scost s' - Γ.scost (Setoid.comap (owxEmb 1) s') :=
      le_trans key h
    linarith

/-- **The local lemma for `Dmove`** (F §3, §4.5; the pin `ScostLLDmovePin` of `T2184-check.lean`): by cases on the colour of `q`. -/
theorem scostLL_dmove (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I) (cp : Bool) (q : SEdge (E ⊕ I))
    (hcp : z = v ↔ cp = true) (hq : q.src = q.dst ↔ q.circ = true)
    (hperm : Γ.solid.Perm (⟨true, cp, z, v⟩ :: q :: rest)) : LGraph.ScostLL Γ (lwPrimDmove Γ rest z v q) := by
  obtain ⟨σ, c, a, b⟩ := q
  cases σ
  · exact localReg6c_dmoveRed Γ rest z v cp c a b hcp hq hperm
  · exact localReg6c_dmoveBlue Γ rest z v cp c a b hcp hq hperm

end Dmove

/-! ## 9. The cost at the kernel of a map (decidable values for the instances) -/

section KerCost

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- the quotient map of `Setoid.ker f` loses no information about `f` -/
private theorem localReg6c_card_image_ker {V : Type} (f : V → ℕ) (S : Finset V) :
    (S.image (Quotient.mk (Setoid.ker f))).card = (S.image f).card := by
  let g : Quotient (Setoid.ker f) → ℕ := Quotient.lift f (fun _ _ h => h)
  have hg : Function.Injective g := by
    intro x y h
    induction x using Quotient.inductionOn with
    | h a =>
      induction y using Quotient.inductionOn with
      | h b => exact Quotient.sound h
  rw [← Finset.card_image_of_injective _ hg, Finset.image_image]
  rfl

open Classical in
/-- **The cost at the kernel of a map** `f : E ⊕ I → ℕ`, as a decidable expression (for `decide` on concrete graphs): kept edges
(circled, or ends with different values), `2 (n_W - #internal values)`, and the elementary internal values. -/
private theorem localReg6c_scost_ker (Γ : LGraph E I) (f : E ⊕ I → ℕ) :
    Γ.scost (Setoid.ker f) =
      ((Γ.solid.filter (fun e => e.circ || decide (f e.src ≠ f e.dst))).length : ℤ) +
        2 * ((Γ.waved.length : ℤ) -
          (((Finset.univ.filter (fun v : E ⊕ I => ∀ a : E, f (Sum.inl a) ≠ f v)).image f).card : ℤ)) +
        (((Finset.univ.filter (fun v : E ⊕ I => (∀ a : E, f (Sum.inl a) ≠ f v) ∧
          lwElem (lwHalfPat (Γ.solid.filter (fun e => e.circ || decide (f e.src ≠ f e.dst)))
            (fun w => f w = f v)) = true)).image f).card : ℤ) := by
  have hk : Γ.skept (Setoid.ker f) = Γ.solid.filter (fun e => e.circ || decide (f e.src ≠ f e.dst)) := by
    unfold LGraph.skept
    refine List.filter_congr (fun e _ => ?_)
    simp [Setoid.ker_def]
  have hI : (Γ.sIntCls (Setoid.ker f)).card =
      ((Finset.univ.filter (fun v : E ⊕ I => ∀ a : E, f (Sum.inl a) ≠ f v)).image f).card := by
    unfold LGraph.sIntCls
    rw [localReg6c_card_image_ker]
    congr 2
    ext v
    simp [Setoid.ker_def]
  have hE : (Γ.sElemCls (Setoid.ker f)).card =
      ((Finset.univ.filter (fun v : E ⊕ I => (∀ a : E, f (Sum.inl a) ≠ f v) ∧
        lwElem (lwHalfPat (Γ.solid.filter (fun e => e.circ || decide (f e.src ≠ f e.dst)))
          (fun w => f w = f v)) = true)).image f).card := by
    unfold LGraph.sElemCls
    rw [localReg6c_card_image_ker]
    congr 2
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Setoid.ker_def]
    rw [hk]
  unfold LGraph.scost
  rw [hk, hI, hE]

end KerCost

/-! ## 10. Compiled instances (CLAUDE.md §4 step 2) -/

section Instances

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the setoid `{x, y, α}`, singletons otherwise, on the vertices of a `Γ_2` primitive with one fresh vertex (the map of the check
file `chkMapXYA`) -/
def localReg6c_mapXYA : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) → ℕ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun i => i.1 + 1) (fun _ => 0))

/-- the setoid `{inr 1, α}`, singletons otherwise, on the vertices of an `instCyc` primitive (the map of the check file
`chkMapCyc`) -/
def localReg6c_mapCyc : Fin 2 ⊕ (Fin 2 ⊕ Fin 1) → ℕ :=
  Sum.elim (fun a => a.1 + 2) (Sum.elim (fun i => i.1) (fun _ => 1))

/-- the trivial setoid (all singletons) on the vertices of a `Γ_2` primitive with one fresh vertex -/
def localReg6c_mapInj : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) → ℕ :=
  Sum.elim (fun a => a.1) (Sum.elim (fun i => i.1 + 2) (fun _ => 6))

/-- Instance (1): `MoveSC(α_0; x, y)` at `Γ_2 = fxyPowGraph 2` (`rest` the other four edges; the `Perm` is
`localReg6b_inst_contractPerm`). -/
theorem localReg6c_inst_moveSC : LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimMoveSC (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)) :=
  scostLL_moveSC _ _ _ _ _ (by decide) (by decide) localReg6b_inst_contractPerm

/-- Instance (1'): at `s' = {x, y, α}` (`k = 2`) the term costs `5`, the restriction `{x, y}` costs `6` (so it is not a witness), and
the merge of the restriction at `x`, `α_0` costs `5` (the repair branch is forced). -/
theorem localReg6c_inst_moveSC_values :
    (lwPrimMoveSC (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost (Setoid.ker localReg6c_mapXYA) = 5 ∧
    (fxyPowGraph 2).scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapXYA)) = 6 ∧
    (fxyPowGraph 2).scost
      (scostLL_merge (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapXYA)) (Sum.inl 0) (Sum.inr 0)) = 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [localReg6c_scost_ker]
    decide
  · have h : Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapXYA) = Setoid.ker (localReg6c_mapXYA ∘ owxEmb 1) :=
      Setoid.ext (fun _ _ => Iff.rfl)
    rw [h, localReg6c_scost_ker]
    decide
  · have h : scostLL_merge (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapXYA)) (Sum.inl 0) (Sum.inr 0) =
        Setoid.ker (fun w : Fin 2 ⊕ Fin (2 * 2) => match w with
          | Sum.inl _ => 0
          | Sum.inr i => if i.1 = 0 then 0 else i.1 + 1) := by
      refine Setoid.ext (fun a b => ?_)
      show (_ ∨ _ ∨ _) ↔ _
      simp only [Setoid.comap_rel, Setoid.ker_def]
      revert a b
      decide
    rw [h, localReg6c_scost_ker]
    decide

/-- Instance (2): `MoveSC(z; u, u)` at the 2-cycle `localReg6b_instCyc` (`z = inr 0`, `u = v = inr 1`): the collapse. -/
theorem localReg6c_inst_moveSC_cyc :
    LGraph.ScostLL localReg6b_instCyc (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)) :=
  scostLL_moveSC _ _ _ _ _ (by decide) (by decide) (List.Perm.refl _)

/-- Instance (2'): at `s' = {inr 1, α}` the term costs `-2` and the restriction (the trivial setoid, cost `0`) is not a witness:
the repair branch is forced. -/
theorem localReg6c_inst_moveSC_cyc_values :
    (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker localReg6c_mapCyc) = -2 ∧
    ¬ localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc)) ≤
      (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker localReg6c_mapCyc) := by
  have hT : (lwPrimMoveSC localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) (Sum.inr 1)).scost (Setoid.ker localReg6c_mapCyc) = -2 := by
    rw [localReg6c_scost_ker]
    decide
  refine ⟨hT, ?_⟩
  have h : Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc) = Setoid.ker (localReg6c_mapCyc ∘ owxEmb 1) :=
    Setoid.ext (fun _ _ => Iff.rfl)
  have h0 : localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc)) = 0 := by
    rw [h, localReg6c_scost_ker]
    decide
  rw [hT, h0]
  decide

/-- the hypothesis of instance (3): the edges `x → α_0` (blue) and `x → α_1` (red) are in front of the solid list of `Γ_2` up to
permutation (`SEdge` has no `DecidableEq`: by unfolding) -/
theorem localReg6c_inst_moveOutPerm : (fxyPowGraph 2).solid.Perm
    ((⟨true, false, Sum.inl 0, Sum.inr 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ ::
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) :=
  (List.perm_middle (a := (⟨true, false, Sum.inl 0, Sum.inr 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))))
    (l₁ := [⟨true, true, Sum.inr 1, Sum.inr 1⟩])
    (l₂ := [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
      ⟨false, false, Sum.inr 2, Sum.inl 1⟩])).trans
    (List.Perm.cons _ (List.perm_middle (a := (⟨false, false, Sum.inl 0, Sum.inr 2⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))))
      (l₁ := [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩])
      (l₂ := [⟨false, false, Sum.inr 2, Sum.inl 1⟩])))

/-- Instance (3): `MoveOut(x; α_0, α_1)` at `Γ_2` (`z = x` external). -/
theorem localReg6c_inst_moveOut : LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimMoveOut (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)) :=
  scostLL_moveOut _ _ _ _ _ (by decide) (by decide) localReg6c_inst_moveOutPerm

/-- the hypothesis of instance (4): the blue light-weight at `β_0` and the red edge `x → α_1` are in front of the solid list of `Γ_2`
up to permutation -/
theorem localReg6c_inst_dmovePerm : (fxyPowGraph 2).solid.Perm
    ((⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨false, false, Sum.inl 0, Sum.inr 2⟩ ::
      [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) :=
  List.Perm.cons _ (List.perm_middle (a := (⟨false, false, Sum.inl 0, Sum.inr 2⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))))
    (l₁ := [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩])
    (l₂ := [⟨false, false, Sum.inr 2, Sum.inl 1⟩]))

/-- Instance (4): `Dmove(β_0; lw_{β_0}, x → α_1)` at `Γ_2` (the `T3` shape, red `q`, `z = v = β_0`, `cp = true`). -/
theorem localReg6c_inst_dmove : LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimDmove (fxyPowGraph 2)
      [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 1) (Sum.inr 1) ⟨false, false, Sum.inl 0, Sum.inr 2⟩) :=
  scostLL_dmove _ _ _ _ true _ (by decide) (by decide) localReg6c_inst_dmovePerm

/-- Instance (5): blue `Dmove(z; z → u, u → z)` at the 2-cycle `localReg6b_instCyc` (`z = inr 0`, `v = a = inr 1`, `b = inr 0`: the
case `[z] = [b] ≠ [v]` at `k = 2`): the collapse; the added edge `z → b` is the uncircled loop `inr 0 → inr 0`. -/
theorem localReg6c_inst_dmove_cyc : LGraph.ScostLL localReg6b_instCyc
    (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩) :=
  scostLL_dmove _ _ _ _ false _ (by decide) (by decide) (List.Perm.refl _)

/-- Instance (5'): at `s' = {inr 1, α}` the term costs `-2` and the restriction (cost `0`) is not a witness: the repair is forced. -/
theorem localReg6c_inst_dmove_cyc_values :
    (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost
        (Setoid.ker localReg6c_mapCyc) = -2 ∧
    ¬ localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc)) ≤
      (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost
        (Setoid.ker localReg6c_mapCyc) := by
  have hT : (lwPrimDmove localReg6b_instCyc [] (Sum.inr 0) (Sum.inr 1) ⟨true, false, Sum.inr 1, Sum.inr 0⟩).scost
      (Setoid.ker localReg6c_mapCyc) = -2 := by
    rw [localReg6c_scost_ker]
    decide
  refine ⟨hT, ?_⟩
  have h : Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc) = Setoid.ker (localReg6c_mapCyc ∘ owxEmb 1) :=
    Setoid.ext (fun _ _ => Iff.rfl)
  have h0 : localReg6b_instCyc.scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapCyc)) = 0 := by
    rw [h, localReg6c_scost_ker]
    decide
  rw [hT, h0]
  decide

/-- Instance (6): the edge term `P3 = MoveOut(x; v, d)` (`oe1xP3`, `LWEdgeExp.lean:1093`): the two added edges are in the other
order, `List.Perm.swap`. -/
theorem localReg6c_inst_P3 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ v) (h2 : Sum.inr x ≠ q.1.dst)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨false, false, Sum.inr x, q.1.dst⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe1xP3 m Γ x v q) :=
  LGraph.ScostLL.of_perm Γ (lwPrimMoveOut Γ q.2 (Sum.inr x) v q.1.dst) (oe1xP3 m Γ x v q)
    (List.Perm.append_left _ (List.Perm.swap _ _ _)) (by simp [lwPrimMoveOut, oe1xP3, LGraph.owxExt])
    (scostLL_moveOut Γ q.2 (Sum.inr x) v q.1.dst h1 h2 hperm)

/-- Instance (7): the edge term `P4 = MoveSC(x; s, v)` (`oe1xP4`, `LWEdgeExp.lean:1111`): equal solid lists. -/
theorem localReg6c_inst_P4 (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : q.1.src ≠ Sum.inr x) (h2 : Sum.inr x ≠ v)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: ⟨true, false, q.1.src, Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe1xP4 m Γ x v q) :=
  LGraph.ScostLL.of_perm Γ (lwPrimMoveSC Γ q.2 (Sum.inr x) q.1.src v) (oe1xP4 m Γ x v q) (List.Perm.refl _)
    (by simp [lwPrimMoveSC, oe1xP4, LGraph.owxExt]) (scostLL_moveSC Γ q.2 (Sum.inr x) q.1.src v h1 h2 hperm)

/-- Instance (8): the edge term `D = Dmove(x; x → v, q)` (`oe1xD`, `LWEdgeExp.lean:606`): equal solid and waved lists. -/
theorem localReg6c_inst_D (m : ℂ) (Γ : LGraph E I) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (h1 : Sum.inr x ≠ v) (hq : q.1.src = q.1.dst ↔ q.1.circ = true)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, v⟩ :: q.1 :: q.2)) : LGraph.ScostLL Γ (oe1xD m Γ x v q) :=
  LGraph.ScostLL.of_perm Γ (lwPrimDmove Γ q.2 (Sum.inr x) v q.1) (oe1xD m Γ x v q) (List.Perm.refl _)
    (by simp [lwPrimDmove, oe1xD, LGraph.owxExt])
    (scostLL_dmove Γ q.2 (Sum.inr x) v false q.1 ⟨fun h => absurd h h1, fun h => by cases h⟩ hq hperm)

/-- Instance (9): the weight term `T3 = Dmove(w; lw_w, q)` (`owxT3`, `LWWeightExp.lean:677`) at an internal vertex. -/
theorem localReg6c_inst_T3 (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (hperm : Γ.solid.Perm (⟨true, true, Sum.inr x, Sum.inr x⟩ :: q.1 :: q.2)) :
    LGraph.ScostLL Γ (owxT3 m Γ x q) :=
  LGraph.ScostLL.of_perm Γ (lwPrimDmove Γ q.2 (Sum.inr x) (Sum.inr x) q.1) (owxT3 m Γ x q) (List.Perm.refl _)
    (by simp [lwPrimDmove, owxT3, LGraph.owxExt])
    (scostLL_dmove Γ q.2 (Sum.inr x) (Sum.inr x) true q.1 ⟨fun _ => rfl, fun _ => rfl⟩ hq hperm)

/-- Instance (9'): the weight term `T3` at an arbitrary vertex (`owxET3`, `LWSymm.lean:603`), in particular at an external one. -/
theorem localReg6c_inst_ET3 (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q.1.src = q.1.dst ↔ q.1.circ = true) (hperm : Γ.solid.Perm (⟨true, true, x, x⟩ :: q.1 :: q.2)) :
    LGraph.ScostLL Γ (owxET3 m Γ x q) :=
  LGraph.ScostLL.of_perm Γ (lwPrimDmove Γ q.2 x x q.1) (owxET3 m Γ x q) (List.Perm.refl _)
    (by simp [lwPrimDmove, owxET3, LGraph.owxExt])
    (scostLL_dmove Γ q.2 x x true q.1 ⟨fun _ => rfl, fun _ => rfl⟩ hq hperm)

/-- Instance (10): the §55 consequence at instances (1), (3), (4): `4 ≤ scost` for every merge and `6 ≤ scost` for every merge
separating `x` and `y` (the merged `localReg6b_inst_s55`; no far/all switch in `ScostLL`). -/
theorem localReg6c_inst_s55 :
    ((∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)),
        4 ≤ (lwPrimMoveSC (fxyPowGraph 2)
          [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s) ∧
      (∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)), ¬ s (Sum.inl 0) (Sum.inl 1) →
        6 ≤ (lwPrimMoveSC (fxyPowGraph 2)
          [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost s)) ∧
    ((∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)),
        4 ≤ (lwPrimMoveOut (fxyPowGraph 2)
          [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)).scost s) ∧
      (∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)), ¬ s (Sum.inl 0) (Sum.inl 1) →
        6 ≤ (lwPrimMoveOut (fxyPowGraph 2)
          [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inl 0) (Sum.inr 0) (Sum.inr 2)).scost s)) ∧
    ((∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)),
        4 ≤ (lwPrimDmove (fxyPowGraph 2)
          [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 1) (Sum.inr 1) ⟨false, false, Sum.inl 0, Sum.inr 2⟩).scost s) ∧
      (∀ s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)), ¬ s (Sum.inl 0) (Sum.inl 1) →
        6 ≤ (lwPrimDmove (fxyPowGraph 2)
          [⟨true, false, Sum.inl 0, Sum.inr 0⟩, ⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
            ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 1) (Sum.inr 1) ⟨false, false, Sum.inl 0, Sum.inr 2⟩).scost s)) :=
  ⟨localReg6b_inst_s55 _ localReg6c_inst_moveSC, localReg6b_inst_s55 _ localReg6c_inst_moveOut,
    localReg6b_inst_s55 _ localReg6c_inst_dmove⟩

open Classical in
/-- Instance of target 1 (`localReg6c_alone_diff`): `MoveSC(α_0; x, y)` at `Γ_2` with the trivial setoid (`α` alone): the removed
edges `α_0 → y`, `x → α_0`, the added edges `x → α`, `α → y` and one waved edge `α_0 - α`; every hypothesis is discharged. -/
example := localReg6c_alone_diff (fxyPowGraph 2)
  [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
    ⟨false, false, Sum.inr 2, Sum.inl 1⟩]
  [⟨true, false, Sum.inr 0, Sum.inl 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩] localReg6b_inst_contractPerm 1
  [⟨true, false, owxEmb 1 (Sum.inl 0), Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 (Sum.inl 1)⟩]
  [⟨false, true, owxEmb 1 (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] (Setoid.ker localReg6c_mapInj)
  (by
    intro w hw
    revert w
    simp only [Setoid.ker_def]
    decide)
  {Quotient.mk _ (Sum.inr 0), Quotient.mk _ (Sum.inl 0), Quotient.mk _ (Sum.inl 1)}
  (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp)
  (by
    intro e he w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he hw
    rcases he with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Or.inr ⟨Sum.inl 0, rfl, by simp⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr ⟨Sum.inl 1, rfl, by simp⟩)

/-- the values of the instance of target 1: at the trivial setoid the term `MoveSC(α_0; x, y)` costs `6` and so does `Γ_2` -/
theorem localReg6c_inst_alone_values :
    (lwPrimMoveSC (fxyPowGraph 2)
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)).scost (Setoid.ker localReg6c_mapInj) = 6 ∧
    (fxyPowGraph 2).scost (Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapInj)) = 6 := by
  refine ⟨?_, ?_⟩
  · rw [localReg6c_scost_ker]
    decide
  · have h : Setoid.comap (owxEmb 1) (Setoid.ker localReg6c_mapInj) = Setoid.ker (localReg6c_mapInj ∘ owxEmb 1) :=
      Setoid.ext (fun _ _ => Iff.rfl)
    rw [h, localReg6c_scost_ker]
    decide

end Instances

end RBM.Graph

end
