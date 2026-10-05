/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular6a

/-!
# LW-10c2: `lem:localregular`, property (6), part 2 (T2195)

The composition API of the local lemma `LGraph.ScostLL`, the helper families of F §4.1-§4.4 that
LW-10c3 consumes (surgery identity, pattern facts, placement lemma, 2-cycle repair), and the local
lemma for the primitives `Loop`, `AddLoop`, `MoveLoop`, `Contract`.

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:786-821` (cited `7_8:line`;
`lem:localregular`, property (6) = `(eq:sizeGammamu)`, `7_8:815-818`) and
`paper/tex/B_graphical_lemmas.tex` (cited `B:line`): the proof of (6) `B:200-278` (the edge and `GG`
cases are omitted there, `B:272-275`), the remark `B:280-283`.
Design: DECISIONS §47, §55 (LW-10c is split into c1-c4: `LocalRegular6a` is c1, this file is c2,
then `6c`, `6d`); the mathematics is the Fable report
`docs/claude-team/fable/2026-10-05-localreg6-locallemma.md` (cited F).

## What is proved

* **Composition** (F §3): `LGraph.ScostLL.trans`, `.of_perm`, `.of_relabel`, `scostLL_refl`.
* **Class sums** (F §4.1): the cost is `#kept + 2 n_W + Σ_{c internal} ([elem (pattern c)] - 2)`
  (`scostLL_scost_eq`; `scostLL_clsPat` is the class pattern, additive over `++`, invariant under
  `List.Perm`).  For the term builder `Γ.owxExt (owxEmb 1) c A W` of the primitives (fresh vertex
  `α = inr (inr 0)`), the exact identity `scostLL_fresh_scost`: the classes of `s'` are the images
  under `localReg6a_qmap` of those of `s₀ = comap (owxEmb 1) s'` (`scostLL_qmap_range`,
  `scostLL_intCls_emb`) plus the class of `α` if `α` is alone.  For one vertex type (`Contract`,
  `AddLoop`): `scostLL_local_diff`, `scostLL_local_diff_C` (localisation to the classes of the
  ends).  `scostLL_merge_scost` is the cost of the merge of two classes.
* **Pattern facts** (F §4.2): `scostLL_elem_E0`, `E1`, `E3`, `E5`, `E4col/out/in`, `E6col/out/in`.
* **Placement** (F §4.3): `scostLL_split` (`a` split off its class) and `scostLL_placement` (loop
  shape and two-edge shape, `k ≤ 1`): splitting the fresh vertex off its class never raises the
  cost.
* **Repair** (F §4.4): `scostLL_merge` and `scostLL_repair`: a 2-cycle `Z → U → Z` of one colour
  between two different classes is repaired by `s` itself or by the merge of `U` and `Z`, which
  never joins two external classes.
* **The four primitives**: `scostLL_loop` (witness `comap (owxEmb 1) s'`), `scostLL_addLoop`
  (Lemma A, `s₀ = s`), `scostLL_moveLoop` (restriction), `scostLL_contract` (`s₀ = s`, or the repair
  in the collapse `[u] = [v] ≠ [z]`).

## Contents (namespace `RBM.Graph`; public helpers `scostLL_`, the others `private`)

1. The composition API.  2. Kept edges, class patterns, pattern facts.  3. The class-sum form.
4. The fresh vertex.  5. One vertex type.  6. `Loop`, `AddLoop`, `MoveLoop`.  7. The merge of two
classes.  8. The 2-cycle repair.  9. `Contract`.  10. The placement lemma.  11. Localisation, the
fresh vertex with all added edges dropped.  12. Compiled instances `localReg6b_inst_` (every
target; the consumers of c3; the §55 values at `Γ_2`).

## Differences from the paper (delta candidates, numbered by the dispatcher)

* `T2195a`: the local lemma composes (F §3) and a merge that puts the fresh vertex into a class
  meeting at most one of its neighbours costs no less than leaving it alone (F §4.3); the 17 terms
  reduce to 7 primitives.  Not in the paper, whose bookkeeping is per term (`B:213-262`).
* `T2195b`: the `GG` term `R2` (`Contract`): the 2-cycle collapse lowers the trivial-merge cost, so
  the paper's "the removal of each distinguished vertex increases the scaling order by at least
  1/2" (`B:272-273`) has no per-step counterpart; the minimum over merges is restored by merging
  the two classes of the cycle (`scostLL_repair`), never two external ones.
* `T2195c` (on `T2184c`, the edge and `GG` cases omitted at `B:272-275`): c2 supplies the local
  lemma for `Loop` (`Oe1xOwx`, `R3`, `T1`), `Contract` (`R2`) and the factors `AddLoop` (`P5`, `P6`,
  `R5`), `Loop` (`R4`, `R6`), `MoveLoop` (`T2`, `T4`); `MoveSC`, `MoveOut`, `Dmove` (c3) close the
  remaining edge and `GG` terms.
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

/-! ## 1. The composition API of `LGraph.ScostLL` -/

section Compose

/-- the local lemma for the identity term (`s₀ = s`) -/
theorem scostLL_refl {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : LGraph E I) :
    LGraph.ScostLL Γ Γ :=
  fun s => ⟨s, fun _ _ h => h, le_rfl⟩

/-- **Composition** (F §3, the pin `ScostLLTransPin`): the local lemma for `Γ → T` and for `T → U` gives it for `Γ → U`
(`s ↦ s₁ ↦ s₀`: the separation and the cost inequality compose). -/
theorem LGraph.ScostLL.trans {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I')
    (U : LGraph E I'') : LGraph.ScostLL Γ T → LGraph.ScostLL T U → LGraph.ScostLL Γ U := by
  intro h1 h2 s
  obtain ⟨s₁, hs₁, hc₁⟩ := h2 s
  obtain ⟨s₀, hs₀, hc₀⟩ := h1 s₁
  exact ⟨s₀, fun a b h => hs₀ a b (hs₁ a b h), hc₀.trans hc₁⟩

/-- the local lemma is invariant under a reordering of the solid edges of the term and the number of its waved edges (the pin
`ScostLLPermPin`; the cost is `scost_perm`) -/
theorem LGraph.ScostLL.of_perm {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] (Γ : LGraph E I) (T T' : LGraph E I') :
    T.solid.Perm T'.solid → T.waved.length = T'.waved.length → LGraph.ScostLL Γ T → LGraph.ScostLL Γ T' := by
  intro hS hW h s
  obtain ⟨s₀, hs₀, hc₀⟩ := h s
  exact ⟨s₀, hs₀, hc₀.trans (le_of_eq (LGraph.scost_perm T T' hS hW s))⟩

/-- the local lemma is invariant under an onto relabelling of the internal vertices of the term fixing the external ones (the pin
`ScostLLRelabelPin`; the witness for `s` is the witness for `comap φ s`, the cost is `scost_relabel`) -/
theorem LGraph.ScostLL.of_relabel {E I I' I'' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
    [Fintype I'] [DecidableEq I'] [Fintype I''] [DecidableEq I''] (Γ : LGraph E I) (T : LGraph E I')
    (φ : E ⊕ I' → E ⊕ I'') : Function.Surjective φ → (∀ a : E, φ (Sum.inl a) = Sum.inl a) →
    LGraph.ScostLL Γ T → LGraph.ScostLL Γ (T.relabel φ) := by
  intro hφ hφl h s
  obtain ⟨s₀, hs₀, hc₀⟩ := h (Setoid.comap φ s)
  refine ⟨s₀, fun a b hab => hs₀ a b ?_, ?_⟩
  · intro hc
    apply hab
    have hc' : (Setoid.comap φ s) (Sum.inl a) (Sum.inl b) := hc
    rw [Setoid.comap_rel, hφl, hφl] at hc'
    exact hc'
  · rw [LGraph.scost_relabel T id Function.surjective_id φ hφ hφl s]
    exact hc₀

end Compose

/-! ## 2. Kept edges, class patterns, the elementary indicator -/

section Basics

variable {V : Type}

open Classical in
/-- The solid edges of `L` **kept** under the merge `s`: the circled edges and the edges between different classes; the
filter of `LGraph.skept`, for an arbitrary list. -/
def scostLL_kept (L : List (SEdge V)) (s : Setoid V) : List (SEdge V) :=
  L.filter fun e => e.circ || !decide (s e.src e.dst)

open Classical in
/-- The **class pattern** of the list `L` at the class `c` of `s`: the half-edge pattern (`lwHalfPat`) of the kept edges of
`L` at the members of `c`. -/
def scostLL_clsPat (L : List (SEdge V)) (s : Setoid V) (c : Quotient s) : ℕ × ℕ × ℕ × ℕ :=
  lwHalfPat (scostLL_kept L s) (fun w => Quotient.mk s w = c)

/-- The elementary indicator `[elem h] ∈ {0, 1}` as an integer. -/
def scostLL_el (h : ℕ × ℕ × ℕ × ℕ) : ℤ := if lwElem h = true then 1 else 0

theorem scostLL_el_nonneg (h : ℕ × ℕ × ℕ × ℕ) : 0 ≤ scostLL_el h := by
  unfold scostLL_el; split_ifs <;> omega

theorem scostLL_el_le_one (h : ℕ × ℕ × ℕ × ℕ) : scostLL_el h ≤ 1 := by
  unfold scostLL_el; split_ifs <;> omega

private theorem scostLL_el_eq_one {h : ℕ × ℕ × ℕ × ℕ} (hh : lwElem h = true) : scostLL_el h = 1 := by
  simp [scostLL_el, hh]

private theorem scostLL_el_eq_zero {h : ℕ × ℕ × ℕ × ℕ} (hh : lwElem h = false) : scostLL_el h = 0 := by
  simp [scostLL_el, hh]

private theorem scostLL_el_spec (a b c d : ℕ) :
    (scostLL_el (a, b, c, d) = 1 ∧ ((a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1))) ∨
      (scostLL_el (a, b, c, d) = 0 ∧ ¬ ((a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1))) := by
  by_cases h : (a = 1 ∧ b = 1 ∧ c = 0 ∧ d = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1 ∧ d = 1)
  · left
    refine ⟨?_, h⟩
    simp [scostLL_el, lwElem, h]
  · right
    refine ⟨?_, h⟩
    simp [scostLL_el, lwElem, h]

/-- the half-edge `c-in` of an edge of colour `σ` -/
def scostLL_hin (σ : Bool) : ℕ × ℕ × ℕ × ℕ := if σ then (1, 0, 0, 0) else (0, 0, 1, 0)

/-- the half-edge `c-out` of an edge of colour `σ` -/
def scostLL_hout (σ : Bool) : ℕ × ℕ × ℕ × ℕ := if σ then (0, 1, 0, 0) else (0, 0, 0, 1)

theorem scostLL_mem_kept (L : List (SEdge V)) (s : Setoid V) (e : SEdge V) :
    e ∈ scostLL_kept L s ↔ e ∈ L ∧ (e.circ = true ∨ ¬ s e.src e.dst) := by
  classical
  simp [scostLL_kept]

theorem scostLL_kept_append (L₁ L₂ : List (SEdge V)) (s : Setoid V) :
    scostLL_kept (L₁ ++ L₂) s = scostLL_kept L₁ s ++ scostLL_kept L₂ s := List.filter_append _ _

theorem scostLL_kept_perm {L₁ L₂ : List (SEdge V)} (h : L₁.Perm L₂) (s : Setoid V) :
    (scostLL_kept L₁ s).Perm (scostLL_kept L₂ s) := h.filter _

open Classical in
theorem scostLL_clsPat_append (L₁ L₂ : List (SEdge V)) (s : Setoid V) (c : Quotient s) :
    scostLL_clsPat (L₁ ++ L₂) s c = scostLL_clsPat L₁ s c + scostLL_clsPat L₂ s c := by
  unfold scostLL_clsPat
  rw [scostLL_kept_append, localReg6a_halfPat_append]

open Classical in
theorem scostLL_clsPat_perm {L₁ L₂ : List (SEdge V)} (h : L₁.Perm L₂) (s : Setoid V) (c : Quotient s) :
    scostLL_clsPat L₁ s c = scostLL_clsPat L₂ s c := by
  unfold scostLL_clsPat
  exact localReg6a_halfPat_perm (scostLL_kept_perm h s) _

theorem scostLL_clsPat_nil (s : Setoid V) (c : Quotient s) : scostLL_clsPat [] s c = 0 := by
  classical
  simp [scostLL_clsPat, scostLL_kept, lwHalfPat]

open Classical in
/-- the class pattern at the class of `v` is the pattern at `fun w => s w v` (the form used by `LGraph.sElemCls`) -/
private theorem scostLL_clsPat_mk (L : List (SEdge V)) (s : Setoid V) (v : V) :
    scostLL_clsPat L s (Quotient.mk s v) = lwHalfPat (scostLL_kept L s) (fun w => s w v) := by
  unfold scostLL_clsPat
  exact localReg6a_halfPat_congr _ (fun w => Quotient.eq)

theorem scostLL_halfPat_single (e : SEdge V) (K : V → Prop) [DecidablePred K] :
    lwHalfPat [e] K = (if K e.dst then scostLL_hin e.σ else 0) + (if K e.src then scostLL_hout e.σ else 0) := by
  rcases e with ⟨σ, c, a, b⟩
  by_cases h1 : K b <;> by_cases h2 : K a <;> cases σ <;>
    simp [lwHalfPat, scostLL_hin, scostLL_hout, h1, h2]

theorem scostLL_halfPat_zero (es : List (SEdge V)) (K : V → Prop) [DecidablePred K] (h : ∀ w, ¬ K w) :
    lwHalfPat es K = 0 := by
  simp [lwHalfPat, h]

/-! ### Pattern facts (F §4.2) -/

/-- (E0): the change of `[elem]` when a residual `X` changes from `X + R` to `X + A` is at least `-1`, and it is `-1` only if
`X + R` was elementary. -/
theorem scostLL_elem_E0 (X R A : ℕ × ℕ × ℕ × ℕ) :
    -1 ≤ scostLL_el (X + A) - scostLL_el (X + R) ∧
      (scostLL_el (X + A) - scostLL_el (X + R) = -1 → lwElem (X + R) = true) := by
  refine ⟨by have := scostLL_el_nonneg (X + A); have := scostLL_el_le_one (X + R); omega, fun h => ?_⟩
  by_contra hne
  have h0 : lwElem (X + R) = false := by simpa using hne
  have := scostLL_el_nonneg (X + A)
  rw [scostLL_el_eq_zero h0] at h
  omega

/-- (E3): equal added and removed patterns do not change `[elem]`. -/
theorem scostLL_elem_E3 (X R : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + R) - scostLL_el (X + R) = 0 := sub_self _

/-- (E1) for a blue pair: `X + (1, 1, 0, 0)` is elementary iff `X = 0`. -/
theorem scostLL_elem_E1 (X : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + (1, 1, 0, 0)) = if X = 0 then 1 else 0 := by
  rcases X with ⟨a, b, c, d⟩
  rcases scostLL_el_spec (a + 1) (b + 1) c d with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    by_cases hX : (a, b, c, d) = 0 <;> simp_all [Prod.ext_iff]

/-- (E5) for a red pair (a red loop is the pair `{r-in, r-out}`): `X + (0, 0, 1, 1)` is elementary iff `X = 0`. -/
theorem scostLL_elem_E5 (X : ℕ × ℕ × ℕ × ℕ) : scostLL_el (X + (0, 0, 1, 1)) = if X = 0 then 1 else 0 := by
  rcases X with ⟨a, b, c, d⟩
  rcases scostLL_el_spec a b (c + 1) (d + 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    by_cases hX : (a, b, c, d) = 0 <;> simp_all [Prod.ext_iff]

/-- an elementary pattern is not `0` -/
theorem scostLL_elem_ne_zero {H : ℕ × ℕ × ℕ × ℕ} (h : lwElem H = true) : H ≠ 0 := by
  rintro rfl
  revert h
  decide

/-- (E4), both colours: a pattern with half-edges of both colours is not elementary. -/
theorem scostLL_elem_E4col (H : ℕ × ℕ × ℕ × ℕ) (h1 : 0 < H.1 + H.2.1) (h2 : 0 < H.2.2.1 + H.2.2.2) :
    lwElem H = false := by
  rcases H with ⟨a, b, c, d⟩
  simp only [lwElem, decide_eq_false_iff_not, Prod.mk.injEq] at h1 h2 ⊢
  omega

/-- (E4), two outs: a pattern with at least two outs is not elementary. -/
theorem scostLL_elem_E4out (H : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ H.2.1 + H.2.2.2) : lwElem H = false := by
  rcases H with ⟨a, b, c, d⟩
  simp only [lwElem, decide_eq_false_iff_not, Prod.mk.injEq] at h ⊢
  omega

/-- (E4), two ins: a pattern with at least two ins is not elementary. -/
theorem scostLL_elem_E4in (H : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ H.1 + H.2.2.1) : lwElem H = false := by
  rcases H with ⟨a, b, c, d⟩
  simp only [lwElem, decide_eq_false_iff_not, Prod.mk.injEq] at h ⊢
  omega

/-- (E6), a pair `A` of two colours: `H + A` is not elementary. -/
theorem scostLL_elem_E6col (H A : ℕ × ℕ × ℕ × ℕ) (h1 : 0 < A.1 + A.2.1) (h2 : 0 < A.2.2.1 + A.2.2.2) :
    lwElem (H + A) = false :=
  scostLL_elem_E4col _ (by simp only [Prod.fst_add, Prod.snd_add]; omega) (by simp only [Prod.fst_add, Prod.snd_add]; omega)

/-- (E6), a pair `A` of two outs: `H + A` is not elementary. -/
theorem scostLL_elem_E6out (H A : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ A.2.1 + A.2.2.2) : lwElem (H + A) = false :=
  scostLL_elem_E4out _ (by simp only [Prod.fst_add, Prod.snd_add]; omega)

/-- (E6), a pair `A` of two ins: `H + A` is not elementary. -/
theorem scostLL_elem_E6in (H A : ℕ × ℕ × ℕ × ℕ) (h : 2 ≤ A.1 + A.2.2.1) : lwElem (H + A) = false :=
  scostLL_elem_E4in _ (by simp only [Prod.fst_add, Prod.snd_add]; omega)

end Basics

/-! ## 3. The class-sum form of the cost (F §4.1, form (a)) -/

section ClassSum

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem scostLL_skept_eq (Γ : LGraph E I) (s : Setoid (E ⊕ I)) : Γ.skept s = scostLL_kept Γ.solid s := rfl

open Classical in
private theorem scostLL_mem_sElemCls_iff (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (c : Quotient s) :
    c ∈ Γ.sElemCls s ↔ c ∈ Γ.sIntCls s ∧ lwElem (scostLL_clsPat Γ.solid s c) = true := by
  rw [localReg6a_mem_sElemCls, localReg6a_mem_sIntCls]
  constructor
  · rintro ⟨v, hv, hel, rfl⟩
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rw [scostLL_clsPat_mk]
    exact hel
  · rintro ⟨⟨v, hv, rfl⟩, hel⟩
    refine ⟨v, hv, ?_, rfl⟩
    rw [scostLL_clsPat_mk] at hel
    exact hel

open Classical in
private theorem scostLL_card_sElemCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) :
    ((Γ.sElemCls s).card : ℤ) = ∑ c ∈ Γ.sIntCls s, scostLL_el (scostLL_clsPat Γ.solid s c) := by
  have h : Γ.sElemCls s = (Γ.sIntCls s).filter (fun c => lwElem (scostLL_clsPat Γ.solid s c) = true) := by
    ext c
    rw [Finset.mem_filter, scostLL_mem_sElemCls_iff]
  rw [h, Finset.card_filter]
  push_cast
  rfl

open Classical in
/-- **The class-sum form** (F §4.1 (a)): `c_s(Γ) = #kept + 2 n_W + Σ_{c internal} ([elem (pattern of c)] - 2)`. -/
theorem scostLL_scost_eq (Γ : LGraph E I) (s : Setoid (E ⊕ I)) :
    Γ.scost s = ((scostLL_kept Γ.solid s).length : ℤ) + 2 * (Γ.waved.length : ℤ) +
      ∑ c ∈ Γ.sIntCls s, (scostLL_el (scostLL_clsPat Γ.solid s c) - 2) := by
  unfold LGraph.scost
  rw [Finset.sum_sub_distrib, ← scostLL_card_sElemCls]
  simp only [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
  rw [scostLL_skept_eq]
  ring

end ClassSum

/-! ## 4. The fresh vertex (F §4.1 (b), (c)) -/

section Fresh

/-- the kept edges of a relabelled list are the images of the kept edges at the pulled-back setoid -/
theorem scostLL_kept_map {V W : Type} (L : List (SEdge V)) (f : V → W) (s : Setoid W) :
    scostLL_kept (L.map (SEdge.map f)) s = (scostLL_kept L (Setoid.comap f s)).map (SEdge.map f) := by
  classical
  unfold scostLL_kept
  simp only [List.filter_map]
  rfl

open Classical in
/-- the class pattern of a relabelled list at the image class is the class pattern at the pulled-back setoid -/
theorem scostLL_clsPat_map {V W : Type} (L : List (SEdge V)) (f : V → W) (s : Setoid W)
    (c : Quotient (Setoid.comap f s)) :
    scostLL_clsPat (L.map (SEdge.map f)) s (localReg6a_qmap f s c) = scostLL_clsPat L (Setoid.comap f s) c := by
  unfold scostLL_clsPat
  rw [scostLL_kept_map, localReg6a_halfPat_map]
  refine localReg6a_halfPat_congr _ (fun v => ?_)
  obtain ⟨a, rfl⟩ := Quotient.exists_rep c
  rw [localReg6a_qmap_mk]
  exact Iff.trans Quotient.eq (Iff.symm Quotient.eq)

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem scostLL_emb_cases (w : E ⊕ (I ⊕ Fin 1)) :
    (∃ v : E ⊕ I, w = owxEmb 1 v) ∨ w = Sum.inr (Sum.inr 0) := by
  rcases w with a | i | j
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inl ⟨Sum.inr i, rfl⟩
  · exact Or.inr (by rw [Subsingleton.elim j 0])

theorem scostLL_emb_ne_alpha (v : E ⊕ I) : owxEmb 1 v ≠ (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) := by
  rcases v with a | i <;> simp [owxEmb]

theorem scostLL_inl_ne_alpha (a : E) : (Sum.inl a : E ⊕ (I ⊕ Fin 1)) ≠ Sum.inr (Sum.inr 0) := by simp

open Classical in
theorem scostLL_clsPat_map_alpha (L : List (SEdge (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    scostLL_clsPat (L.map (SEdge.map (owxEmb 1))) s' (Quotient.mk s' (Sum.inr (Sum.inr 0))) = 0 := by
  unfold scostLL_clsPat
  rw [scostLL_kept_map, localReg6a_halfPat_map]
  refine scostLL_halfPat_zero _ _ (fun v hv => ?_)
  have h : s' (owxEmb 1 v) (Sum.inr (Sum.inr 0)) := Quotient.exact hv
  exact scostLL_emb_ne_alpha v (halone _ h)

open Classical in
/-- **(b)**: the image of `qmap (owxEmb 1) s'` misses exactly the class of `α` if `α` is alone, and nothing otherwise. -/
theorem scostLL_qmap_range (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (c' : Quotient s') :
    (∃ c₀, localReg6a_qmap (owxEmb 1) s' c₀ = c') ↔
      ¬ ((∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) ∧
        c' = Quotient.mk s' (Sum.inr (Sum.inr 0))) := by
  constructor
  · rintro ⟨c₀, rfl⟩ ⟨halone, hc⟩
    obtain ⟨v, rfl⟩ := Quotient.exists_rep c₀
    rw [localReg6a_qmap_mk] at hc
    exact scostLL_emb_ne_alpha v (halone _ (Quotient.exact hc))
  · intro h
    obtain ⟨w, rfl⟩ := Quotient.exists_rep c'
    rcases scostLL_emb_cases w with ⟨v, rfl⟩ | rfl
    · exact ⟨Quotient.mk _ v, rfl⟩
    · have hna : ¬ ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0) := fun ha => h ⟨ha, rfl⟩
      push Not at hna
      obtain ⟨w₀, hw₀, hne⟩ := hna
      rcases scostLL_emb_cases w₀ with ⟨v₀, rfl⟩ | h0
      · exact ⟨Quotient.mk _ v₀, by rw [localReg6a_qmap_mk]; exact Quotient.sound hw₀⟩
      · exact absurd h0 hne

open Classical in
/-- **(b)**: the internal classes of `s'` are the images of those of `s₀ = comap (owxEmb 1) s'`, and the class of `α` if `α` is
alone (`sIntCls` depends only on the setoid). -/
theorem scostLL_intCls_emb (Γ : LGraph E I) (T : LGraph E (I ⊕ Fin 1)) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) :
    T.sIntCls s' = (Γ.sIntCls (Setoid.comap (owxEmb 1) s')).image (localReg6a_qmap (owxEmb 1) s') ∪
      (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then
        {Quotient.mk s' (Sum.inr (Sum.inr 0))} else ∅) := by
  ext c'
  rw [localReg6a_mem_sIntCls, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases scostLL_emb_cases w with ⟨v, rfl⟩ | rfl
    · exact Or.inl ⟨Quotient.mk _ v, (localReg6a_mem_sIntCls _ _ _).2 ⟨v, fun a h => hw a h, rfl⟩, rfl⟩
    · by_cases halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
      · right
        simp only [eq_true halone, ↓reduceIte]
        exact Finset.mem_singleton_self _
      · left
        push Not at halone
        obtain ⟨w₀, hw₀, hne⟩ := halone
        rcases scostLL_emb_cases w₀ with ⟨v₀, rfl⟩ | h0
        · refine ⟨Quotient.mk _ v₀, (localReg6a_mem_sIntCls _ _ _).2 ⟨v₀, fun a h => hw a (s'.trans h hw₀), rfl⟩, ?_⟩
          rw [localReg6a_qmap_mk]
          exact Quotient.sound hw₀
        · exact absurd h0 hne
  · rintro (⟨c₀, hc₀, rfl⟩ | h)
    · obtain ⟨v, hv, rfl⟩ := (localReg6a_mem_sIntCls _ _ _).1 hc₀
      exact ⟨owxEmb 1 v, fun a h => hv a h, rfl⟩
    · by_cases halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
      · simp only [eq_true halone, ↓reduceIte, Finset.mem_singleton] at h
        subst h
        exact ⟨_, fun a h => scostLL_inl_ne_alpha a (halone _ h), rfl⟩
      · simp only [eq_false halone, ↓reduceIte] at h
        exact absurd h (Finset.notMem_empty _)

open Classical in
theorem scostLL_sum_intCls_emb (Γ : LGraph E I) (T : LGraph E (I ⊕ Fin 1)) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (g : Quotient s' → ℤ) :
    ∑ c' ∈ T.sIntCls s', g c' =
      ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'), g (localReg6a_qmap (owxEmb 1) s' c₀) +
        (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then
          g (Quotient.mk s' (Sum.inr (Sum.inr 0))) else 0) := by
  rw [scostLL_intCls_emb Γ T s']
  have hinj : Set.InjOn (localReg6a_qmap (owxEmb 1) s') (Γ.sIntCls (Setoid.comap (owxEmb 1) s') : Set _) :=
    (localReg6a_qmap_injective _ _).injOn
  by_cases halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · simp only [eq_true halone, ↓reduceIte]
    rw [Finset.sum_union, Finset.sum_image hinj, Finset.sum_singleton]
    refine Finset.disjoint_singleton_right.2 (fun hmem => ?_)
    obtain ⟨c₀, -, hc₀⟩ := Finset.mem_image.1 hmem
    exact ((scostLL_qmap_range s' _).1 ⟨c₀, hc₀⟩) ⟨halone, rfl⟩
  · simp only [eq_false halone, ↓reduceIte]
    rw [Finset.union_empty, Finset.sum_image hinj, add_zero]

open Classical in
/-- **The surgery identity for the term builder of the primitives** (F §4.1 (c)): the cost of
`Γ.owxExt (owxEmb 1) c A W` (the graph `Γ` on the old vertices, the edges `A` and `W` appended, a fresh vertex
`α = inr (inr 0)`) at an arbitrary setoid `s'` is the cost-like sum over the classes of `s₀ = comap (owxEmb 1) s'`
(classes of `s'` through `qmap`) plus the class of `α` if `α` is alone. -/
theorem scostLL_fresh_scost (Γ : LGraph E I) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) :
    (Γ.owxExt (owxEmb 1) c A W).scost s' =
      ((scostLL_kept Γ.solid (Setoid.comap (owxEmb 1) s')).length : ℤ) + ((scostLL_kept A s').length : ℤ) +
        2 * ((Γ.waved.length : ℤ) + (W.length : ℤ)) +
        ∑ c₀ ∈ Γ.sIntCls (Setoid.comap (owxEmb 1) s'),
          (scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀ +
            scostLL_clsPat A s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) +
        (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then
          scostLL_el (scostLL_clsPat A s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2 else 0) := by
  have hsolid : (Γ.owxExt (owxEmb 1) c A W).solid = Γ.solid.map (SEdge.map (owxEmb 1)) ++ A := rfl
  have hwaved : (Γ.owxExt (owxEmb 1) c A W).waved.length = Γ.waved.length + W.length := by
    simp [LGraph.owxExt]
  rw [scostLL_scost_eq, hsolid, hwaved, scostLL_sum_intCls_emb Γ _ s', scostLL_kept_append, scostLL_kept_map]
  simp only [List.length_append, List.length_map, scostLL_clsPat_append, scostLL_clsPat_map]
  by_cases halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · simp only [eq_true halone, ↓reduceIte]
    rw [scostLL_clsPat_map_alpha Γ.solid s' halone, zero_add]
    push_cast
    ring
  · simp only [eq_false halone, ↓reduceIte]
    push_cast
    ring

end Fresh

/-! ## 5. One vertex type: the localisation of the class sums (F §4.1 (c), one vertex type) -/

section Local

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- **The surgery identity for one vertex type** (`Contract`, `AddLoop`; F §4.1): `Γ.solid ~ R ++ X`, `Γ'.solid ~ A ++ X`
make the two cost differences a sum over the classes of the (class patterns of) `A`, `R` and the residual `X`. -/
theorem scostLL_local_diff (Γ Γ' : LGraph E I) (R A X : List (SEdge (E ⊕ I))) (s : Setoid (E ⊕ I))
    (hΓ : Γ.solid.Perm (R ++ X)) (hΓ' : Γ'.solid.Perm (A ++ X)) :
    Γ'.scost s - Γ.scost s =
      ((scostLL_kept A s).length : ℤ) - ((scostLL_kept R s).length : ℤ) +
        2 * ((Γ'.waved.length : ℤ) - (Γ.waved.length : ℤ)) +
        ∑ c ∈ Γ.sIntCls s, (scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) -
          scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c)) := by
  have h1 : (scostLL_kept Γ'.solid s).length = (scostLL_kept A s).length + (scostLL_kept X s).length := by
    rw [(scostLL_kept_perm hΓ' s).length_eq, scostLL_kept_append, List.length_append]
  have h2 : (scostLL_kept Γ.solid s).length = (scostLL_kept R s).length + (scostLL_kept X s).length := by
    rw [(scostLL_kept_perm hΓ s).length_eq, scostLL_kept_append, List.length_append]
  have h3 : ∀ c, scostLL_clsPat Γ'.solid s c = scostLL_clsPat A s c + scostLL_clsPat X s c := fun c => by
    rw [scostLL_clsPat_perm hΓ' s c, scostLL_clsPat_append]
  have h4 : ∀ c, scostLL_clsPat Γ.solid s c = scostLL_clsPat R s c + scostLL_clsPat X s c := fun c => by
    rw [scostLL_clsPat_perm hΓ s c, scostLL_clsPat_append]
  have hI : Γ'.sIntCls s = Γ.sIntCls s := rfl
  rw [scostLL_scost_eq Γ' s, scostLL_scost_eq Γ s, h1, h2, hI]
  simp only [h3, h4]
  rw [← sub_eq_zero]
  have : ∀ c ∈ Γ.sIntCls s, (scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) - 2) -
      (scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c) - 2) =
      scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) -
        scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c) := fun c _ => by ring
  have hs := Finset.sum_sub_distrib (s := Γ.sIntCls s)
    (f := fun c => scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) - 2)
    (g := fun c => scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c) - 2)
  rw [Finset.sum_congr rfl this] at hs
  push_cast
  linarith

open Classical in
/-- a sum with a single possibly nonzero term -/
theorem scostLL_sum_single {Q : Type} (S : Finset Q) (d : Q → ℤ) (c₀ : Q) (h : ∀ c, c ≠ c₀ → d c = 0) :
    ∑ c ∈ S, d c = if c₀ ∈ S then d c₀ else 0 := by
  split_ifs with hc
  · exact Finset.sum_eq_single_of_mem c₀ hc (fun c _ hne => h c hne)
  · exact Finset.sum_eq_zero (fun c hc' => h c (fun hh => hc (hh ▸ hc')))

open Classical in
theorem scostLL_clsPat_loop {V : Type} (col : Bool) (v : V) (s : Setoid V) (c : Quotient s) :
    scostLL_clsPat [⟨col, true, v, v⟩] s c =
      if Quotient.mk s v = c then scostLL_hin col + scostLL_hout col else 0 := by
  unfold scostLL_clsPat
  have hk : scostLL_kept [(⟨col, true, v, v⟩ : SEdge V)] s = [⟨col, true, v, v⟩] := by simp [scostLL_kept]
  rw [hk, scostLL_halfPat_single]
  by_cases h : Quotient.mk s v = c <;> simp [h]

theorem scostLL_el_pair (col : Bool) : scostLL_el (scostLL_hin col + scostLL_hout col) = 1 := by
  cases col <;> decide

end Local

/-! ## 6. The local lemma for `Loop`, `AddLoop`, `MoveLoop` (F §4.5) -/

section LoopPrims

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- adding a circled loop at the fresh vertex `α` (and the waved edges `W`) costs at least `2 |W|` over the old graph at
`s₀ = comap (owxEmb 1) s'`: `α` alone gives `+2 |W|` exactly (`+1` kept loop, `-2` class `{α}`, `+1` elementary `{α}`), `α` in
a class gives `+3 + Δelem ≥ 2` (F §4.5 `Loop`). -/
private theorem scostLL_fresh_loop (Γ : LGraph E I) (c : ℂ) (col : Bool) (W : List (WEdge (E ⊕ (I ⊕ Fin 1))))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) :
    Γ.scost (Setoid.comap (owxEmb 1) s') + 2 * (W.length : ℤ) ≤
      (Γ.owxExt (owxEmb 1) c [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] W).scost s' := by
  rw [scostLL_fresh_scost, scostLL_scost_eq Γ (Setoid.comap (owxEmb 1) s')]
  have hk : scostLL_kept [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] s' =
      [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] := by simp [scostLL_kept]
  rw [hk]
  by_cases halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · simp only [eq_true halone, ↓reduceIte]
    have hA : ∀ c₀, scostLL_clsPat [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))]
        s' (localReg6a_qmap (owxEmb 1) s' c₀) = 0 := by
      intro c₀
      have hn : ¬ Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) = localReg6a_qmap (owxEmb 1) s' c₀ :=
        fun h => (scostLL_qmap_range s' _).1 ⟨c₀, h.symm⟩ ⟨halone, rfl⟩
      rw [scostLL_clsPat_loop]
      simp only [hn, ↓reduceIte]
    simp only [hA, add_zero]
    rw [scostLL_clsPat_loop]
    simp only [eq_self, ↓reduceIte, scostLL_el_pair, List.length_singleton]
    push_cast
    linarith
  · simp only [eq_false halone, ↓reduceIte]
    obtain ⟨cs, hcs⟩ := (scostLL_qmap_range s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))).2 (fun h => halone h.1)
    set S := Γ.sIntCls (Setoid.comap (owxEmb 1) s') with hS
    set d : Quotient (Setoid.comap (owxEmb 1) s') → ℤ := fun c₀ =>
      scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀ +
        scostLL_clsPat [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] s'
          (localReg6a_qmap (owxEmb 1) s' c₀)) -
      scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀) with hd
    have hd0 : ∀ c₀, c₀ ≠ cs → d c₀ = 0 := by
      intro c₀ hne
      simp only [hd]
      have hn : ¬ Quotient.mk s' (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) = localReg6a_qmap (owxEmb 1) s' c₀ :=
        fun h => hne (localReg6a_qmap_injective _ _ (h.symm.trans hcs.symm))
      rw [scostLL_clsPat_loop]
      simp only [hn, ↓reduceIte, add_zero, sub_self]
    have hsum : ∑ c₀ ∈ S, (scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀ +
        scostLL_clsPat [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] s'
          (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) =
        ∑ c₀ ∈ S, (scostLL_el (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') c₀) - 2) + ∑ c₀ ∈ S, d c₀ := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun c _ => by simp only [hd]; ring)
    have hge : -1 ≤ ∑ c₀ ∈ S, d c₀ := by
      rw [scostLL_sum_single S d cs hd0]
      split_ifs
      · simp only [hd]
        have := scostLL_el_nonneg (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') cs +
          scostLL_clsPat [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))] s'
            (localReg6a_qmap (owxEmb 1) s' cs))
        have := scostLL_el_le_one (scostLL_clsPat Γ.solid (Setoid.comap (owxEmb 1) s') cs)
        omega
      · omega
    rw [hsum]
    simp only [List.length_singleton]
    push_cast
    linarith

/-- **The local lemma for `Loop`** (F §4.5): the witness is the restriction `comap (owxEmb 1) s'`. -/
theorem scostLL_loop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph.ScostLL Γ (lwPrimLoop Γ z col) := by
  intro s'
  refine ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, ?_⟩
  have h := scostLL_fresh_loop Γ 1 col [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] s'
  have e : lwPrimLoop Γ z col = Γ.owxExt (owxEmb 1) 1 [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
      [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] := rfl
  rw [e]
  simp only [List.length_singleton] at h
  push_cast at h
  linarith

/-- **The local lemma for `AddLoop`** (F §4.5, Lemma A): `s₀ = s`. -/
theorem scostLL_addLoop (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) : LGraph.ScostLL Γ (lwPrimAddLoop Γ z col) :=
  fun s => ⟨s, fun _ _ h => h, LGraph.scost_cons_loop_ge Γ ⟨col, true, z, z⟩ rfl rfl s⟩

open Classical in
/-- **The local lemma for `MoveLoop`** (F §4.5): the witness is the restriction `comap (owxEmb 1) s'`. -/
theorem scostLL_moveLoop (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z : E ⊕ I) (col : Bool)
    (hperm : Γ.solid.Perm (⟨col, true, z, z⟩ :: rest)) : LGraph.ScostLL Γ (lwPrimMoveLoop Γ rest z col) := by
  intro s'
  refine ⟨Setoid.comap (owxEmb 1) s', fun a b h hc => h hc, ?_⟩
  set s₀ := Setoid.comap (owxEmb 1) s' with hs₀
  set Γ₁ : LGraph E I := { Γ with solid := rest } with hΓ₁
  have h1 := scostLL_fresh_loop Γ₁ 1 col [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] s'
  have e : lwPrimMoveLoop Γ rest z col = Γ₁.owxExt (owxEmb 1) 1
      [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] := rfl
  have hd := scostLL_local_diff Γ₁ Γ [] [⟨col, true, z, z⟩] rest s₀ (by simp [hΓ₁]) hperm
  have hk : scostLL_kept [(⟨col, true, z, z⟩ : SEdge (E ⊕ I))] s₀ = [⟨col, true, z, z⟩] := by simp [scostLL_kept]
  have hW : Γ.waved.length = Γ₁.waved.length := rfl
  set d : Quotient s₀ → ℤ := fun c =>
    scostLL_el (scostLL_clsPat [(⟨col, true, z, z⟩ : SEdge (E ⊕ I))] s₀ c + scostLL_clsPat rest s₀ c) -
      scostLL_el (scostLL_clsPat [] s₀ c + scostLL_clsPat rest s₀ c) with hd'
  have hd0 : ∀ c, c ≠ Quotient.mk s₀ z → d c = 0 := by
    intro c hne
    simp only [hd']
    have hn : ¬ Quotient.mk s₀ z = c := fun h => hne h.symm
    rw [scostLL_clsPat_loop]
    simp only [hn, ↓reduceIte, scostLL_clsPat_nil, sub_self]
  have hle : ∑ c ∈ Γ₁.sIntCls s₀, d c ≤ 1 := by
    rw [scostLL_sum_single _ d (Quotient.mk s₀ z) hd0]
    split_ifs
    · simp only [hd']
      have := scostLL_el_le_one (scostLL_clsPat [(⟨col, true, z, z⟩ : SEdge (E ⊕ I))] s₀ (Quotient.mk s₀ z) +
        scostLL_clsPat rest s₀ (Quotient.mk s₀ z))
      have := scostLL_el_nonneg (scostLL_clsPat [] s₀ (Quotient.mk s₀ z) + scostLL_clsPat rest s₀ (Quotient.mk s₀ z))
      omega
    · omega
  rw [e]
  rw [hk, scostLL_kept] at hd
  simp only [List.length_singleton, List.filter_nil, List.length_nil] at hd
  rw [hW] at hd
  simp only [List.length_singleton] at h1
  push_cast at hd h1
  linarith

end LoopPrims

/-! ## 7. The merge of two classes (F §4.4) -/

section Merge

variable {V : Type}

/-- **The merge of the classes of `u` and `z`** (F §4.4): `a ~ b ↔ s a b ∨ (s a u ∧ s z b) ∨ (s a z ∧ s u b)`. -/
def scostLL_merge (s : Setoid V) (u z : V) : Setoid V where
  r a b := s a b ∨ (s a u ∧ s z b) ∨ (s a z ∧ s u b)
  iseqv := by
    refine ⟨fun a => Or.inl (s.refl' a), ?_, ?_⟩
    · rintro a b (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl (s.symm h)
      · exact Or.inr (Or.inr ⟨s.symm h2, s.symm h1⟩)
      · exact Or.inr (Or.inl ⟨s.symm h2, s.symm h1⟩)
    · rintro a b c (h | ⟨h1, h2⟩ | ⟨h1, h2⟩) (h' | ⟨h1', h2'⟩ | ⟨h1', h2'⟩)
      · exact Or.inl (s.trans h h')
      · exact Or.inr (Or.inl ⟨s.trans h h1', h2'⟩)
      · exact Or.inr (Or.inr ⟨s.trans h h1', h2'⟩)
      · exact Or.inr (Or.inl ⟨h1, s.trans h2 h'⟩)
      · exact Or.inl (s.trans (s.trans h1 (s.symm (s.trans h2 h1'))) h2')
      · exact Or.inl (s.trans h1 h2')
      · exact Or.inr (Or.inr ⟨h1, s.trans h2 h'⟩)
      · exact Or.inl (s.trans h1 h2')
      · exact Or.inl (s.trans (s.trans h1 (s.symm (s.trans h2 h1'))) h2')

private theorem scostLL_merge_rel (s : Setoid V) (u z a b : V) :
    scostLL_merge s u z a b ↔ s a b ∨ (s a u ∧ s z b) ∨ (s a z ∧ s u b) := Iff.rfl

private theorem scostLL_le_merge (s : Setoid V) (u z : V) {a b : V} (h : s a b) : scostLL_merge s u z a b := Or.inl h

/-- a vertex is related to `u` in the merge iff it is related to `u` or to `z` -/
private theorem scostLL_merge_u (s : Setoid V) (u z w : V) : scostLL_merge s u z w u ↔ s w u ∨ s w z := by
  rw [scostLL_merge_rel]
  constructor
  · rintro (h | ⟨h1, -⟩ | ⟨h1, -⟩)
    · exact Or.inl h
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨h, s.refl' u⟩)

/-- the induced map of the quotients -/
def scostLL_qmerge (s : Setoid V) (u z : V) : Quotient s → Quotient (scostLL_merge s u z) :=
  Quotient.map id (fun _ _ h => scostLL_le_merge s u z h)

private theorem scostLL_qmerge_mk (s : Setoid V) (u z v : V) :
    scostLL_qmerge s u z (Quotient.mk s v) = Quotient.mk (scostLL_merge s u z) v := rfl

theorem scostLL_qmerge_eq_iff (s : Setoid V) (u z : V) (c c' : Quotient s) :
    scostLL_qmerge s u z c = scostLL_qmerge s u z c' ↔
      c = c' ∨ (c = Quotient.mk s u ∧ c' = Quotient.mk s z) ∨ (c = Quotient.mk s z ∧ c' = Quotient.mk s u) := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep c
  obtain ⟨b, rfl⟩ := Quotient.exists_rep c'
  rw [scostLL_qmerge_mk, scostLL_qmerge_mk]
  simp only [Quotient.eq]
  rw [scostLL_merge_rel]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, s.symm h2⟩)
    · exact Or.inr (Or.inr ⟨h1, s.symm h2⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1, s.symm h2⟩)
    · exact Or.inr (Or.inr ⟨h1, s.symm h2⟩)

private theorem scostLL_merge_iff (s : Setoid V) (u z a b : V) (huz : ¬ s u z) :
    (¬ s a b ∧ scostLL_merge s u z a b) ↔ ((s a u ∧ s b z) ∨ (s a z ∧ s b u)) := by
  rw [scostLL_merge_rel]
  constructor
  · rintro ⟨hn, h | ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact absurd h hn
    · exact Or.inl ⟨h1, s.symm h2⟩
    · exact Or.inr ⟨h1, s.symm h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨fun h => huz (s.trans (s.symm h1) (s.trans h h2)), Or.inr (Or.inl ⟨h1, s.symm h2⟩)⟩
    · refine ⟨fun h => huz (s.trans (s.symm h2) (s.trans (s.symm h) h1)), Or.inr (Or.inr ⟨h1, s.symm h2⟩)⟩

open Classical in
/-- the uncircled kept edges joining the class of `u` to the class of `z`: dropped by the merge -/
def scostLL_joined (L : List (SEdge V)) (s : Setoid V) (u z : V) : List (SEdge V) :=
  L.filter fun e => !e.circ && decide ((s e.src u ∧ s e.dst z) ∨ (s e.src z ∧ s e.dst u))

open Classical in
/-- the kept edges under `s` are the kept edges under the merge and the joined edges -/
private theorem scostLL_kept_merge_perm (L : List (SEdge V)) (s : Setoid V) (u z : V) (huz : ¬ s u z) :
    (scostLL_kept L s).Perm (scostLL_kept L (scostLL_merge s u z) ++ scostLL_joined L s u z) := by
  have h1 : scostLL_kept L (scostLL_merge s u z) =
      (scostLL_kept L s).filter (fun e => e.circ || !decide (scostLL_merge s u z e.src e.dst)) := by
    unfold scostLL_kept
    rw [List.filter_filter]
    refine List.filter_congr (fun e _ => ?_)
    by_cases hc : e.circ = true
    · simp [hc]
    · have hc' : e.circ = false := by simpa using hc
      by_cases hs : s e.src e.dst
      · simp [hc', hs, scostLL_le_merge s u z hs]
      · simp [hc', hs]
  have h2 : scostLL_joined L s u z =
      (scostLL_kept L s).filter (fun e => !(e.circ || !decide (scostLL_merge s u z e.src e.dst))) := by
    unfold scostLL_kept scostLL_joined
    rw [List.filter_filter]
    refine List.filter_congr (fun e _ => ?_)
    by_cases hc : e.circ = true
    · simp [hc]
    · have hc' : e.circ = false := by simpa using hc
      have key := scostLL_merge_iff s u z e.src e.dst huz
      by_cases hs : s e.src e.dst
      · have : ¬ ((s e.src u ∧ s e.dst z) ∨ (s e.src z ∧ s e.dst u)) := fun h => (key.2 h).1 hs
        simp [hc', hs, this]
      · by_cases hm : scostLL_merge s u z e.src e.dst
        · have : ((s e.src u ∧ s e.dst z) ∨ (s e.src z ∧ s e.dst u)) := key.1 ⟨hs, hm⟩
          simp [hc', hs, hm, this]
        · have : ¬ ((s e.src u ∧ s e.dst z) ∨ (s e.src z ∧ s e.dst u)) := fun h => hm (key.2 h).2
          simp [hc', hs, hm, this]
  rw [h1, h2]
  exact (List.filter_append_perm _ _).symm

private theorem scostLL_halfPat_zero_of_ends (es : List (SEdge V)) (K : V → Prop) [DecidablePred K]
    (h : ∀ e ∈ es, ¬ K e.src ∧ ¬ K e.dst) : lwHalfPat es K = 0 := by
  have h0 : ∀ e ∈ es, decide (K e.src) = false ∧ decide (K e.dst) = false := fun e he => by
    simp [(h e he).1, (h e he).2]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [lwHalfPat, List.countP_eq_zero, Prod.fst_zero, Prod.snd_zero] <;>
    intro e he <;> simp [(h0 e he).1, (h0 e he).2]

private theorem scostLL_toNat_or (b : Bool) (P Q : Prop) [Decidable P] [Decidable Q] [Decidable (P ∨ Q)] (h : ¬ (P ∧ Q)) :
    (b && decide (P ∨ Q)).toNat = (b && decide P).toNat + (b && decide Q).toNat := by
  by_cases hP : P
  · by_cases hQ : Q
    · exact absurd ⟨hP, hQ⟩ h
    · cases b <;> simp [hP, hQ]
  · by_cases hQ : Q <;> cases b <;> simp [hP, hQ]

private theorem scostLL_halfPat_or (es : List (SEdge V)) (K₁ K₂ : V → Prop) [DecidablePred K₁] [DecidablePred K₂]
    [DecidablePred (fun w => K₁ w ∨ K₂ w)] (hd : ∀ w, ¬ (K₁ w ∧ K₂ w)) :
    lwHalfPat es (fun w => K₁ w ∨ K₂ w) = lwHalfPat es K₁ + lwHalfPat es K₂ := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only [lwHalfPat, Prod.fst_add, Prod.snd_add] <;>
    exact (localReg6a_countP_add _ _ _ es fun e _ => (scostLL_toNat_or _ _ _ (hd _)).symm).symm

open Classical in
private theorem scostLL_halfPat_kept_merge (L : List (SEdge V)) (s : Setoid V) (u z : V) (huz : ¬ s u z)
    (K : V → Prop) [DecidablePred K] :
    lwHalfPat (scostLL_kept L s) K =
      lwHalfPat (scostLL_kept L (scostLL_merge s u z)) K + lwHalfPat (scostLL_joined L s u z) K := by
  rw [localReg6a_halfPat_perm (scostLL_kept_merge_perm L s u z huz) K, localReg6a_halfPat_append]

open Classical in
/-- the pattern of a class other than those of `u` and `z` is not changed by the merge -/
private theorem scostLL_clsPat_merge_other (L : List (SEdge V)) (s : Setoid V) (u z : V) (huz : ¬ s u z)
    (c : Quotient s) (hU : c ≠ Quotient.mk s u) (hZ : c ≠ Quotient.mk s z) :
    scostLL_clsPat L (scostLL_merge s u z) (scostLL_qmerge s u z c) = scostLL_clsPat L s c := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep c
  have hau : ¬ s a u := fun h => hU (Quotient.sound h)
  have haz : ¬ s a z := fun h => hZ (Quotient.sound h)
  unfold scostLL_clsPat
  have hK : ∀ w, (Quotient.mk (scostLL_merge s u z) w = scostLL_qmerge s u z (Quotient.mk s a)) ↔
      (Quotient.mk s w = Quotient.mk s a) := by
    intro w
    rw [scostLL_qmerge_mk]
    simp only [Quotient.eq]
    rw [scostLL_merge_rel]
    constructor
    · rintro (h | ⟨-, h2⟩ | ⟨-, h2⟩)
      · exact h
      · exact absurd (s.symm h2) haz
      · exact absurd (s.symm h2) hau
    · exact Or.inl
  rw [localReg6a_halfPat_congr _ hK,
    scostLL_halfPat_kept_merge L s u z huz (fun w => Quotient.mk s w = Quotient.mk s a),
    scostLL_halfPat_zero_of_ends (scostLL_joined L s u z) _ ?_, add_zero]
  intro e he
  simp only [scostLL_joined, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨-, -, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩ := he
  · exact ⟨fun h => hau (s.trans (s.symm (Quotient.exact h)) h1), fun h => haz (s.trans (s.symm (Quotient.exact h)) h2)⟩
  · exact ⟨fun h => haz (s.trans (s.symm (Quotient.exact h)) h1), fun h => hau (s.trans (s.symm (Quotient.exact h)) h2)⟩

open Classical in
/-- the pattern of the merged class: it is the sum of the patterns of the two classes minus the joined edges -/
private theorem scostLL_clsPat_merge_M (L : List (SEdge V)) (s : Setoid V) (u z : V) (huz : ¬ s u z) :
    scostLL_clsPat L (scostLL_merge s u z) (Quotient.mk _ u) +
        lwHalfPat (scostLL_joined L s u z) (fun w => s w u ∨ s w z) =
      scostLL_clsPat L s (Quotient.mk s u) + scostLL_clsPat L s (Quotient.mk s z) := by
  unfold scostLL_clsPat
  have h1 : ∀ w, (Quotient.mk (scostLL_merge s u z) w = Quotient.mk (scostLL_merge s u z) u) ↔ (s w u ∨ s w z) := by
    intro w
    rw [Quotient.eq]
    exact scostLL_merge_u s u z w
  have h2 : ∀ w, (Quotient.mk s w = Quotient.mk s u) ↔ s w u := fun w => Quotient.eq
  have h3 : ∀ w, (Quotient.mk s w = Quotient.mk s z) ↔ s w z := fun w => Quotient.eq
  rw [localReg6a_halfPat_congr _ h1, localReg6a_halfPat_congr _ h2, localReg6a_halfPat_congr _ h3,
    ← scostLL_halfPat_or _ (fun w => s w u) (fun w => s w z) (fun w ⟨a, b⟩ => huz (s.trans (s.symm a) b)),
    scostLL_halfPat_kept_merge L s u z huz (fun w => s w u ∨ s w z)]

end Merge

section MergeScost

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
theorem scostLL_mk_mem_sIntCls (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (v : E ⊕ I) :
    Quotient.mk s v ∈ Γ.sIntCls s ↔ ∀ a : E, ¬ s (Sum.inl a) v := by
  rw [localReg6a_mem_sIntCls]
  constructor
  · rintro ⟨w, hw, hwv⟩ a h
    exact hw a (s.trans h (s.symm (Quotient.exact hwv)))
  · intro h
    exact ⟨v, h, rfl⟩

open Classical in
/-- the internal classes of the merge: the images of the internal classes other than those of `u` and `z`, and the merged
class if both are internal -/
private theorem scostLL_intCls_merge (Γ Γ' : LGraph E I) (s : Setoid (E ⊕ I)) (u z : E ⊕ I) (huz : ¬ s u z) :
    Γ'.sIntCls (scostLL_merge s u z) =
      ((Γ.sIntCls s).filter (fun c => ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z))).image (scostLL_qmerge s u z) ∪
        (if ((∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)) then
          {Quotient.mk (scostLL_merge s u z) u} else ∅) := by
  ext c'
  rw [localReg6a_mem_sIntCls, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    by_cases hwuz : s w u ∨ s w z
    · right
      have hcond : (∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z) := by
        rcases hwuz with h | h
        · refine ⟨fun a ha => hw a (Or.inl (s.trans ha (s.symm h))), fun a ha => hw a (Or.inr (Or.inr ⟨ha, s.symm h⟩))⟩
        · refine ⟨fun a ha => hw a (Or.inr (Or.inl ⟨ha, s.symm h⟩)), fun a ha => hw a (Or.inl (s.trans ha (s.symm h)))⟩
      simp only [eq_true hcond, ↓reduceIte, Finset.mem_singleton]
      rw [Quotient.eq]
      exact (scostLL_merge_u s u z w).2 hwuz
    · left
      push Not at hwuz
      refine ⟨Quotient.mk s w, Finset.mem_filter.2 ⟨(scostLL_mk_mem_sIntCls Γ s w).2 (fun a h => hw a (Or.inl h)), ?_⟩, rfl⟩
      rintro (h | h)
      · exact hwuz.1 (Quotient.exact h)
      · exact hwuz.2 (Quotient.exact h)
  · rintro (⟨c, hc, rfl⟩ | h)
    · obtain ⟨hcI, hcn⟩ := Finset.mem_filter.1 hc
      obtain ⟨v, hv, rfl⟩ := (localReg6a_mem_sIntCls _ _ _).1 hcI
      refine ⟨v, fun a h => ?_, rfl⟩
      rcases h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hv a h
      · exact hcn (Or.inr (Quotient.sound (s.symm h2)))
      · exact hcn (Or.inl (Quotient.sound (s.symm h2)))
    · by_cases hcond : (∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)
      · simp only [eq_true hcond, ↓reduceIte, Finset.mem_singleton] at h
        subst h
        refine ⟨u, fun a ha => ?_, rfl⟩
        rcases (scostLL_merge_u s u z _).1 ha with h | h
        · exact hcond.1 a h
        · exact hcond.2 a h
      · simp only [eq_false hcond, ↓reduceIte] at h
        exact absurd h (Finset.notMem_empty _)

open Classical in
private theorem scostLL_sum_intCls_merge (Γ Γ' : LGraph E I) (s : Setoid (E ⊕ I)) (u z : E ⊕ I) (huz : ¬ s u z)
    (g : Quotient (scostLL_merge s u z) → ℤ) :
    ∑ c' ∈ Γ'.sIntCls (scostLL_merge s u z), g c' =
      ∑ c ∈ Γ.sIntCls s, (if ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z) then g (scostLL_qmerge s u z c) else 0) +
        (if ((∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)) then g (Quotient.mk _ u) else 0) := by
  rw [scostLL_intCls_merge Γ Γ' s u z huz, ← Finset.sum_filter]
  have hinj : Set.InjOn (scostLL_qmerge s u z)
      ((Γ.sIntCls s).filter (fun c => ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z)) : Set _) := by
    intro c₁ h₁ c₂ h₂ h
    have h₁' := (Finset.mem_filter.1 h₁).2
    rcases (scostLL_qmerge_eq_iff s u z c₁ c₂).1 h with h | ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact h
    · exact absurd (Or.inl ha) h₁'
    · exact absurd (Or.inr ha) h₁'
  by_cases hcond : (∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)
  · simp only [eq_true hcond, ↓reduceIte]
    rw [Finset.sum_union, Finset.sum_image hinj, Finset.sum_singleton]
    refine Finset.disjoint_singleton_right.2 (fun hmem => ?_)
    obtain ⟨c, hc, hcm⟩ := Finset.mem_image.1 hmem
    have hcn := (Finset.mem_filter.1 hc).2
    have hcm' : scostLL_qmerge s u z c = scostLL_qmerge s u z (Quotient.mk s u) := hcm
    rcases (scostLL_qmerge_eq_iff s u z c _).1 hcm' with h | ⟨h, -⟩ | ⟨h, -⟩
    · exact hcn (Or.inl h)
    · exact hcn (Or.inl h)
    · exact hcn (Or.inr h)
  · simp only [eq_false hcond, ↓reduceIte]
    rw [Finset.union_empty, Finset.sum_image hinj, add_zero]

open Classical in
/-- **The cost of a merge** (F §4.4): merging the classes of `u` and `z` (`¬ s u z`) changes the cost by minus the number of
joined edges, plus the term of the merged class if both are internal, minus the terms of the internal ones among the two
classes. -/
theorem scostLL_merge_scost (Γ : LGraph E I) (s : Setoid (E ⊕ I)) (u z : E ⊕ I) (huz : ¬ s u z) :
    Γ.scost (scostLL_merge s u z) = Γ.scost s - ((scostLL_joined Γ.solid s u z).length : ℤ) +
      (if ((∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)) then
        scostLL_el (scostLL_clsPat Γ.solid (scostLL_merge s u z) (Quotient.mk _ u)) - 2 else 0) -
      (if (∀ a : E, ¬ s (Sum.inl a) u) then
        scostLL_el (scostLL_clsPat Γ.solid s (Quotient.mk s u)) - 2 else 0) -
      (if (∀ a : E, ¬ s (Sum.inl a) z) then
        scostLL_el (scostLL_clsPat Γ.solid s (Quotient.mk s z)) - 2 else 0) := by
  rw [scostLL_scost_eq Γ (scostLL_merge s u z), scostLL_scost_eq Γ s, scostLL_sum_intCls_merge Γ Γ s u z huz]
  set h : Quotient s → ℤ := fun c => scostLL_el (scostLL_clsPat Γ.solid s c) - 2 with hh
  have hUZ : Quotient.mk s u ≠ Quotient.mk s z := fun h' => huz (Quotient.exact h')
  have hlen : ((scostLL_kept Γ.solid (scostLL_merge s u z)).length : ℤ) =
      (scostLL_kept Γ.solid s).length - (scostLL_joined Γ.solid s u z).length := by
    have := (scostLL_kept_merge_perm Γ.solid s u z huz).length_eq
    rw [List.length_append] at this
    omega
  have hsum1 : ∑ c ∈ Γ.sIntCls s, (if ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z) then
      (scostLL_el (scostLL_clsPat Γ.solid (scostLL_merge s u z) (scostLL_qmerge s u z c)) - 2) else 0) =
      ∑ c ∈ Γ.sIntCls s, (if ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z) then h c else 0) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases hc : ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z)
    · simp only [hc, not_false_eq_true, ↓reduceIte, hh]
      rw [scostLL_clsPat_merge_other Γ.solid s u z huz c (fun h' => hc (Or.inl h')) (fun h' => hc (Or.inr h'))]
    · simp [hc]
  have hsum2 : ∑ c ∈ Γ.sIntCls s, h c =
      ∑ c ∈ Γ.sIntCls s, (if ¬ (c = Quotient.mk s u ∨ c = Quotient.mk s z) then h c else 0) +
        (if Quotient.mk s u ∈ Γ.sIntCls s then h (Quotient.mk s u) else 0) +
        (if Quotient.mk s z ∈ Γ.sIntCls s then h (Quotient.mk s z) else 0) := by
    rw [← Finset.sum_ite_eq' (Γ.sIntCls s) (Quotient.mk s u) h, ← Finset.sum_ite_eq' (Γ.sIntCls s) (Quotient.mk s z) h,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    by_cases h1 : c = Quotient.mk s u
    · subst h1
      simp [hUZ]
    · by_cases h2 : c = Quotient.mk s z
      · subst h2
        simp [hUZ.symm]
      · simp [h1, h2]
  rw [hsum1]
  simp only [scostLL_mk_mem_sIntCls] at hsum2
  rw [hsum2, hlen]
  ring

end MergeScost

/-! ## 8. The 2-cycle repair (F §4.4) -/

section Repair

variable {V : Type}

private theorem scostLL_halfPat_eq_zero_imp (es : List (SEdge V)) (K : V → Prop) [DecidablePred K]
    (h : lwHalfPat es K = 0) : ∀ e ∈ es, ¬ K e.src ∧ ¬ K e.dst := by
  intro e he
  have h1 := congrArg (fun p => p.1) h
  have h2 := congrArg (fun p => p.2.1) h
  have h3 := congrArg (fun p => p.2.2.1) h
  have h4 := congrArg (fun p => p.2.2.2) h
  simp only [lwHalfPat, List.countP_eq_zero, Prod.fst_zero, Prod.snd_zero] at h1 h2 h3 h4
  have a1 := h1 e he
  have a2 := h2 e he
  have a3 := h3 e he
  have a4 := h4 e he
  constructor
  · intro hs
    cases hσ : e.σ <;> simp_all
  · intro hd
    cases hσ : e.σ <;> simp_all

open Classical in
private theorem scostLL_clsPat_cyc (col : Bool) (u z v u' z' : V) (s : Setoid V) (hv : s u v) (hu' : s u u')
    (hz' : s z z') (huz : ¬ s u z) (c : Quotient s) :
    scostLL_clsPat [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] s c =
      (if c = Quotient.mk s u then scostLL_hin col + scostLL_hout col else 0) +
      (if c = Quotient.mk s z then scostLL_hin col + scostLL_hout col else 0) := by
  have hk1 : ¬ s z v := fun h => huz (s.symm (s.trans h (s.symm hv)))
  have hk2 : ¬ s u' z' := fun h => huz (s.trans hu' (s.trans h (s.symm hz')))
  have hkept : scostLL_kept [(⟨col, false, z, v⟩ : SEdge V), ⟨col, false, u', z'⟩] s =
      [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] := by
    simp [scostLL_kept, hk1, hk2]
  unfold scostLL_clsPat
  rw [hkept]
  show lwHalfPat ([(⟨col, false, z, v⟩ : SEdge V)] ++ [⟨col, false, u', z'⟩]) _ = _
  rw [localReg6a_halfPat_append, scostLL_halfPat_single, scostLL_halfPat_single]
  have e1 : Quotient.mk s v = Quotient.mk s u := (Quotient.sound hv).symm
  have e2 : Quotient.mk s u' = Quotient.mk s u := (Quotient.sound hu').symm
  have e3 : Quotient.mk s z' = Quotient.mk s z := (Quotient.sound hz').symm
  have hne : Quotient.mk s u ≠ Quotient.mk s z := fun h => huz (Quotient.exact h)
  simp only [e1, e2, e3]
  by_cases h1 : Quotient.mk s u = c
  · subst h1
    simp [hne, hne.symm]
  · by_cases h2 : Quotient.mk s z = c
    · subst h2
      simp [hne, hne.symm]
      abel
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

open Classical in
private theorem scostLL_joined_cyc (col : Bool) (u z v u' z' : V) (s : Setoid V) (hv : s u v) (hu' : s u u')
    (hz' : s z z') : scostLL_joined [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] s u z =
      [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] := by
  have h1 : (s z u ∧ s v z) ∨ (s z z ∧ s v u) := Or.inr ⟨s.refl' z, s.symm hv⟩
  have h2 : (s u' u ∧ s z' z) ∨ (s u' z ∧ s z' u) := Or.inl ⟨s.symm hu', s.symm hz'⟩
  unfold scostLL_joined
  rw [List.filter_eq_self]
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · simpa using h1
  · simpa using h2

open Classical in
private theorem scostLL_joined_eq_nil (L : List (SEdge V)) (s : Setoid V) (u z : V) (huz : ¬ s u z)
    (h : scostLL_clsPat L s (Quotient.mk s u) = 0 ∨ scostLL_clsPat L s (Quotient.mk s z) = 0) :
    scostLL_joined L s u z = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  simp only [scostLL_joined, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at he
  obtain ⟨heL, hcirc, hends⟩ := he
  have hns : ¬ s e.src e.dst := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact fun h => huz (s.trans (s.symm h1) (s.trans h h2))
    · exact fun h => huz (s.trans (s.symm h2) (s.trans (s.symm h) h1))
  have hker : e ∈ scostLL_kept L s := (scostLL_mem_kept L s e).2 ⟨heL, Or.inr hns⟩
  rcases h with h | h
  · have := scostLL_halfPat_eq_zero_imp _ _ h e hker
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact this.1 (Quotient.sound h1)
    · exact this.2 (Quotient.sound h2)
  · have := scostLL_halfPat_eq_zero_imp _ _ h e hker
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact this.2 (Quotient.sound h2)
    · exact this.1 (Quotient.sound h1)

open Classical in
/-- a sum supported on two points -/
theorem scostLL_sum_two {Q : Type} (S : Finset Q) (a b : Q) (hab : a ≠ b) (d : Q → ℤ)
    (h : ∀ c, c ≠ a → c ≠ b → d c = 0) :
    ∑ c ∈ S, d c = (if a ∈ S then d a else 0) + (if b ∈ S then d b else 0) := by
  rw [← Finset.sum_ite_eq' S a d, ← Finset.sum_ite_eq' S b d, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h1 : c = a
  · subst h1
    simp [hab]
  · by_cases h2 : c = b
    · subst h2
      simp [hab.symm]
    · simp [h1, h2, h c h1 h2]

theorem scostLL_el_zero : scostLL_el (0 : ℕ × ℕ × ℕ × ℕ) = 0 := by
  apply scostLL_el_eq_zero
  decide

theorem scostLL_el_pair_add (col : Bool) (X : ℕ × ℕ × ℕ × ℕ) :
    scostLL_el (scostLL_hin col + scostLL_hout col + X) = if X = 0 then 1 else 0 := by
  cases col
  · have : scostLL_hin false + scostLL_hout false = ((0, 0, 1, 1) : ℕ × ℕ × ℕ × ℕ) := rfl
    rw [this, add_comm, scostLL_elem_E5]
  · have : scostLL_hin true + scostLL_hout true = ((1, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) := rfl
    rw [this, add_comm, scostLL_elem_E1]

end Repair

section RepairMain

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- the cost of the graph with the 2-cycle removed, against the graph: `-2` plus the change of `[elem]` at the two classes -/
private theorem scostLL_repair_diff (Γ : LGraph E I) (L : List (SEdge (E ⊕ I))) (col : Bool) (z v u' z' u : E ⊕ I)
    (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L))
    (hv : s u v) (hu' : s u u') (hz' : s z z') (huz : ¬ s u z) :
    ({ Γ with solid := L } : LGraph E I).scost s - Γ.scost s =
      -2 + (if (∀ a : E, ¬ s (Sum.inl a) u) then
          scostLL_el (scostLL_clsPat L s (Quotient.mk s u)) -
            scostLL_el (scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s u)) else 0) +
        (if (∀ a : E, ¬ s (Sum.inl a) z) then
          scostLL_el (scostLL_clsPat L s (Quotient.mk s z)) -
            scostLL_el (scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s z)) else 0) := by
  have hΓ' : Γ.solid.Perm ([⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] ++ L) := hΓ
  have hdiff := scostLL_local_diff Γ ({ Γ with solid := L } : LGraph E I)
    [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] [] L s hΓ' (List.Perm.refl _)
  have hk1 : ¬ s z v := fun h => huz (s.symm (s.trans h (s.symm hv)))
  have hk2 : ¬ s u' z' := fun h => huz (s.trans hu' (s.trans h (s.symm hz')))
  have hkept : scostLL_kept [(⟨col, false, z, v⟩ : SEdge (E ⊕ I)), ⟨col, false, u', z'⟩] s =
      [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] := by simp [scostLL_kept, hk1, hk2]
  have hUZ : Quotient.mk s u ≠ Quotient.mk s z := fun h => huz (Quotient.exact h)
  rw [hkept] at hdiff
  simp only [List.length_cons, List.length_nil, scostLL_kept, List.filter_nil] at hdiff
  have hsum := scostLL_sum_two (Γ.sIntCls s) (Quotient.mk s u) (Quotient.mk s z) hUZ
    (fun c => scostLL_el (scostLL_clsPat [] s c + scostLL_clsPat L s c) -
      scostLL_el (scostLL_clsPat [⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] s c + scostLL_clsPat L s c))
    (fun c h1 h2 => by
      rw [scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz c]
      simp only [h1, h2, ↓reduceIte, scostLL_clsPat_nil]
      simp)
  rw [hsum] at hdiff
  simp only [scostLL_mk_mem_sIntCls, scostLL_clsPat_nil, zero_add] at hdiff
  rw [scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz (Quotient.mk s u),
    scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz (Quotient.mk s z)] at hdiff
  simp only [hUZ, hUZ.symm, add_zero, zero_add, ite_true, ite_false] at hdiff
  have hW : ({ Γ with solid := L } : LGraph E I).waved.length = Γ.waved.length := rfl
  rw [hW] at hdiff
  push_cast at hdiff
  linarith

open Classical in
private theorem scostLL_joined_append {V : Type} (L₁ L₂ : List (SEdge V)) (s : Setoid V) (u z : V) :
    scostLL_joined (L₁ ++ L₂) s u z = scostLL_joined L₁ s u z ++ scostLL_joined L₂ s u z := List.filter_append _ _

open Classical in
private theorem scostLL_joined_perm {V : Type} {L₁ L₂ : List (SEdge V)} (h : L₁.Perm L₂) (s : Setoid V) (u z : V) :
    (scostLL_joined L₁ s u z).Perm (scostLL_joined L₂ s u z) := h.filter _

open Classical in
/-- the cost of the merge of the two classes of the 2-cycle -/
private theorem scostLL_repair_merge (Γ : LGraph E I) (L : List (SEdge (E ⊕ I))) (col : Bool) (z v u' z' u : E ⊕ I)
    (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L))
    (hv : s u v) (hu' : s u u') (hz' : s z z') (huz : ¬ s u z) :
    Γ.scost (scostLL_merge s u z) = Γ.scost s - 2 - ((scostLL_joined L s u z).length : ℤ) +
      (if ((∀ a : E, ¬ s (Sum.inl a) u) ∧ (∀ a : E, ¬ s (Sum.inl a) z)) then
        scostLL_el (scostLL_clsPat Γ.solid (scostLL_merge s u z) (Quotient.mk _ u)) - 2 else 0) -
      (if (∀ a : E, ¬ s (Sum.inl a) u) then
        scostLL_el (scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s u)) - 2 else 0) -
      (if (∀ a : E, ¬ s (Sum.inl a) z) then
        scostLL_el (scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s z)) - 2 else 0) := by
  have hΓ' : Γ.solid.Perm ([⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] ++ L) := hΓ
  have hUZ : Quotient.mk s u ≠ Quotient.mk s z := fun h => huz (Quotient.exact h)
  rw [scostLL_merge_scost Γ s u z huz]
  have hj : (scostLL_joined Γ.solid s u z).length = 2 + (scostLL_joined L s u z).length := by
    rw [(scostLL_joined_perm hΓ' s u z).length_eq, scostLL_joined_append, List.length_append,
      scostLL_joined_cyc col u z v u' z' s hv hu' hz']
    rfl
  have ha : scostLL_clsPat Γ.solid s (Quotient.mk s u) =
      scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s u) := by
    rw [scostLL_clsPat_perm hΓ', scostLL_clsPat_append, scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz]
    simp [hUZ]
  have hb : scostLL_clsPat Γ.solid s (Quotient.mk s z) =
      scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s z) := by
    rw [scostLL_clsPat_perm hΓ', scostLL_clsPat_append, scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz]
    simp [hUZ.symm]
  rw [hj, ha, hb]
  push_cast
  ring

open Classical in
/-- the pattern of the merged class, when no further edge joins the two classes -/
private theorem scostLL_repair_m (Γ : LGraph E I) (L : List (SEdge (E ⊕ I))) (col : Bool) (z v u' z' u : E ⊕ I)
    (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L))
    (hv : s u v) (hu' : s u u') (hz' : s z z') (huz : ¬ s u z) (hL : scostLL_joined L s u z = []) :
    scostLL_clsPat Γ.solid (scostLL_merge s u z) (Quotient.mk _ u) =
      scostLL_clsPat L s (Quotient.mk s u) + scostLL_clsPat L s (Quotient.mk s z) := by
  have hΓ' : Γ.solid.Perm ([⟨col, false, z, v⟩, ⟨col, false, u', z'⟩] ++ L) := hΓ
  have hUZ : Quotient.mk s u ≠ Quotient.mk s z := fun h => huz (Quotient.exact h)
  have h := scostLL_clsPat_merge_M Γ.solid s u z huz
  have hdp : lwHalfPat (scostLL_joined Γ.solid s u z) (fun w => s w u ∨ s w z) =
      (scostLL_hin col + scostLL_hout col) + (scostLL_hin col + scostLL_hout col) := by
    rw [localReg6a_halfPat_perm (scostLL_joined_perm hΓ' s u z), scostLL_joined_append,
      scostLL_joined_cyc col u z v u' z' s hv hu' hz', hL, List.append_nil]
    show lwHalfPat ([(⟨col, false, z, v⟩ : SEdge (E ⊕ I))] ++ [⟨col, false, u', z'⟩]) _ = _
    rw [localReg6a_halfPat_append, scostLL_halfPat_single, scostLL_halfPat_single]
    have k1 : s v u ∨ s v z := Or.inl (s.symm hv)
    have k2 : s z u ∨ s z z := Or.inr (s.refl' z)
    have k3 : s z' u ∨ s z' z := Or.inr (s.symm hz')
    have k4 : s u' u ∨ s u' z := Or.inl (s.symm hu')
    simp only [k1, k2, k3, k4, ite_true]
  have ha : scostLL_clsPat Γ.solid s (Quotient.mk s u) =
      scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s u) := by
    rw [scostLL_clsPat_perm hΓ', scostLL_clsPat_append, scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz]
    simp [hUZ]
  have hb : scostLL_clsPat Γ.solid s (Quotient.mk s z) =
      scostLL_hin col + scostLL_hout col + scostLL_clsPat L s (Quotient.mk s z) := by
    rw [scostLL_clsPat_perm hΓ', scostLL_clsPat_append, scostLL_clsPat_cyc col u z v u' z' s hv hu' hz' huz]
    simp [hUZ.symm]
  rw [hdp, ha, hb] at h
  have h2 : scostLL_clsPat Γ.solid (scostLL_merge s u z) (Quotient.mk _ u) +
      (scostLL_hin col + scostLL_hout col + (scostLL_hin col + scostLL_hout col)) =
      (scostLL_clsPat L s (Quotient.mk s u) + scostLL_clsPat L s (Quotient.mk s z)) +
      (scostLL_hin col + scostLL_hout col + (scostLL_hin col + scostLL_hout col)) := by
    rw [h]; abel
  exact add_right_cancel h2

open Classical in
/-- **The 2-cycle repair lemma** (F §4.4), in the form of the graph `Γ` carrying the cycle: if two uncircled edges of one
colour form a 2-cycle `Z → U → Z` between two different classes of `s` (`s u v`, `s u u'`, `s z z'`, `¬ s u z`), then either
`s` itself or the merge of `U` and `Z` costs at most the cost of `Γ` with the cycle removed, plus the waved edge (`+ 2`); the
merge never joins two classes that both contain an external vertex.  No hypothesis on `Γ` or on the residual `L`. -/
theorem scostLL_repair (Γ : LGraph E I) (L : List (SEdge (E ⊕ I))) (col : Bool) (z v u' z' u : E ⊕ I)
    (s : Setoid (E ⊕ I)) (hΓ : Γ.solid.Perm (⟨col, false, z, v⟩ :: ⟨col, false, u', z'⟩ :: L))
    (hv : s u v) (hu' : s u u') (hz' : s z z') (huz : ¬ s u z) :
    ∃ s₀ : Setoid (E ⊕ I), (s₀ = s ∨ s₀ = scostLL_merge s u z) ∧
      (∀ a b : E, ¬ s (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧
      Γ.scost s₀ ≤ ({ Γ with solid := L } : LGraph E I).scost s + 2 := by
  have hD := scostLL_repair_diff Γ L col z v u' z' u s hΓ hv hu' hz' huz
  have hMg := scostLL_repair_merge Γ L col z v u' z' u s hΓ hv hu' hz' huz
  have eU := scostLL_el_pair_add col (scostLL_clsPat L s (Quotient.mk s u))
  have eZ := scostLL_el_pair_add col (scostLL_clsPat L s (Quotient.mk s z))
  have nU := scostLL_el_nonneg (scostLL_clsPat L s (Quotient.mk s u))
  have nZ := scostLL_el_nonneg (scostLL_clsPat L s (Quotient.mk s z))
  have hJ : (0 : ℤ) ≤ ((scostLL_joined L s u z).length : ℤ) := Int.natCast_nonneg _
  by_cases hU : ∀ a : E, ¬ s (Sum.inl a) u <;> by_cases hZ : ∀ a : E, ¬ s (Sum.inl a) z
  · -- both classes internal
    by_cases hX : scostLL_clsPat L s (Quotient.mk s u) = 0 ∨ scostLL_clsPat L s (Quotient.mk s z) = 0
    · have hjn := scostLL_joined_eq_nil L s u z huz hX
      have hm := scostLL_repair_m Γ L col z v u' z' u s hΓ hv hu' hz' huz hjn
      refine ⟨scostLL_merge s u z, Or.inr rfl, ?_, ?_⟩
      · intro a b hab hc
        rcases (scostLL_merge_iff s u z _ _ huz).1 ⟨hab, hc⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hU a h1
        · exact hU b h2
      · rw [hm, hjn] at hMg
        simp only [eq_true hU, eq_true hZ, and_self, ↓reduceIte, List.length_nil, Nat.cast_zero] at hMg hD
        rcases hX with h0 | h0
        · rw [h0] at hMg hD eU
          simp only [zero_add, scostLL_el_zero] at hMg hD
          linarith
        · rw [h0] at hMg hD eZ
          simp only [add_zero, scostLL_el_zero] at hMg hD
          linarith
    · push Not at hX
      refine ⟨s, Or.inl rfl, fun a b h => h, ?_⟩
      simp only [eq_true hU, eq_true hZ, ↓reduceIte] at hD
      simp only [hX.1, ↓reduceIte] at eU
      simp only [hX.2, ↓reduceIte] at eZ
      linarith
  · -- `U` internal, `Z` external
    refine ⟨scostLL_merge s u z, Or.inr rfl, ?_, ?_⟩
    · intro a b hab hc
      rcases (scostLL_merge_iff s u z _ _ huz).1 ⟨hab, hc⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hU a h1
      · exact hU b h2
    · simp only [eq_true hU, eq_false hZ, and_false, ↓reduceIte] at hMg hD
      linarith
  · -- `U` external, `Z` internal
    refine ⟨scostLL_merge s u z, Or.inr rfl, ?_, ?_⟩
    · intro a b hab hc
      rcases (scostLL_merge_iff s u z _ _ huz).1 ⟨hab, hc⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hZ b h2
      · exact hZ a h1
    · simp only [eq_false hU, eq_true hZ, false_and, ↓reduceIte] at hMg hD
      linarith
  · -- both external
    refine ⟨s, Or.inl rfl, fun a b h => h, ?_⟩
    simp only [eq_false hU, eq_false hZ, ↓reduceIte] at hD
    linarith

end RepairMain

/-! ## 9. The local lemma for `Contract` (F §4.5) -/

section ContractPrim

open Classical in
theorem scostLL_clsPat_single_kept {V : Type} (σ : Bool) (a b : V) (s : Setoid V) (h : ¬ s a b) (c : Quotient s) :
    scostLL_clsPat [⟨σ, false, a, b⟩] s c =
      (if Quotient.mk s b = c then scostLL_hin σ else 0) + (if Quotient.mk s a = c then scostLL_hout σ else 0) := by
  unfold scostLL_clsPat
  have hk : scostLL_kept [(⟨σ, false, a, b⟩ : SEdge V)] s = [⟨σ, false, a, b⟩] := by simp [scostLL_kept, h]
  rw [hk, scostLL_halfPat_single]

open Classical in
theorem scostLL_clsPat_single_dropped {V : Type} (σ : Bool) (a b : V) (s : Setoid V) (h : s a b) (c : Quotient s) :
    scostLL_clsPat [⟨σ, false, a, b⟩] s c = 0 := by
  unfold scostLL_clsPat
  have hk : scostLL_kept [(⟨σ, false, a, b⟩ : SEdge V)] s = [] := by simp [scostLL_kept, h]
  rw [hk]
  simp [lwHalfPat]

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- `Contract` with the same patterns of the added and removed edges at every class other than that of `z`: the cost does not
fall below `#kept(A) - #kept(R) + 1` -/
private theorem scostLL_contract_aux (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (s : Setoid (E ⊕ I))
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest))
    (h0 : ∀ c, c ≠ Quotient.mk s z → scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c =
      scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c) :
    ((scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s).length : ℤ) -
      ((scostLL_kept [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s).length : ℤ) + 1 ≤
      (lwPrimContract Γ rest z u v).scost s - Γ.scost s := by
  have hd := scostLL_local_diff Γ (lwPrimContract Γ rest z u v)
    [⟨true, false, z, v⟩, ⟨true, false, u, z⟩] [⟨true, false, u, v⟩] rest s hperm (List.Perm.refl _)
  have hTwaved : (lwPrimContract Γ rest z u v).waved.length = Γ.waved.length + 1 := rfl
  rw [hTwaved] at hd
  have hd0 : ∀ c, c ≠ Quotient.mk s z →
      scostLL_el (scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c + scostLL_clsPat rest s c) -
        scostLL_el (scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c +
          scostLL_clsPat rest s c) = 0 := fun c hc => by rw [h0 c hc, sub_self]
  have hsum : -1 ≤ ∑ c ∈ Γ.sIntCls s,
      (scostLL_el (scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c + scostLL_clsPat rest s c) -
        scostLL_el (scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c +
          scostLL_clsPat rest s c)) := by
    rw [scostLL_sum_single _ _ (Quotient.mk s z) hd0]
    split_ifs
    · have := scostLL_el_nonneg (scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s (Quotient.mk s z) +
        scostLL_clsPat rest s (Quotient.mk s z))
      have := scostLL_el_le_one (scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s
        (Quotient.mk s z) + scostLL_clsPat rest s (Quotient.mk s z))
      omega
    · omega
  push_cast at hd
  linarith

open Classical in
/-- when the added edge is dropped, the contracted graph costs two more than the graph without the cycle -/
private theorem scostLL_contract_dropped (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (s : Setoid (E ⊕ I))
    (h : s u v) : (lwPrimContract Γ rest z u v).scost s = ({ Γ with solid := rest } : LGraph E I).scost s + 2 := by
  have hd := scostLL_local_diff ({ Γ with solid := rest } : LGraph E I) (lwPrimContract Γ rest z u v) []
    [⟨true, false, u, v⟩] rest s (List.Perm.refl _) (List.Perm.refl _)
  have hTwaved : (lwPrimContract Γ rest z u v).waved.length = Γ.waved.length + 1 := rfl
  have hW : ({ Γ with solid := rest } : LGraph E I).waved.length = Γ.waved.length := rfl
  rw [hTwaved, hW] at hd
  have hk : scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s = [] := by simp [scostLL_kept, h]
  simp only [hk, scostLL_clsPat_single_dropped true u v s h, scostLL_clsPat_nil, List.length_nil, Nat.cast_zero,
    sub_self, Finset.sum_const_zero] at hd
  simp only [scostLL_kept, List.filter_nil, List.length_nil, Nat.cast_zero] at hd
  push_cast at hd
  linarith

open Classical in
/-- **The local lemma for `Contract`** (F §4.5): `s₀ = s`, except for the 2-cycle collapse (`[u] = [v] ≠ [z]`), where
`s₀` is `s` or the merge of the classes of `u` and `z` (the repair lemma). -/
theorem scostLL_contract (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I) (hu : u ≠ z) (hv : z ≠ v)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest)) :
    LGraph.ScostLL Γ (lwPrimContract Γ rest z u v) := by
  intro s
  by_cases hb : s u v ∧ ¬ s u z
  · obtain ⟨hv', huz'⟩ := hb
    obtain ⟨s₀, -, hsep, hcost⟩ := scostLL_repair Γ rest true z v u z u s hperm hv' (s.refl' u) (s.refl' z) huz'
    exact ⟨s₀, hsep, hcost.trans (le_of_eq (scostLL_contract_dropped Γ rest z u v s hv').symm)⟩
  · refine ⟨s, fun a b h => h, ?_⟩
    have hsplit : ∀ (e₁ e₂ : SEdge (E ⊕ I)) (c : Quotient s),
        scostLL_clsPat [e₁, e₂] s c = scostLL_clsPat [e₁] s c + scostLL_clsPat [e₂] s c :=
      fun e₁ e₂ c => scostLL_clsPat_append [e₁] [e₂] s c
    by_cases ha : s u v
    · -- all three in one class
      have hb' : s u z := by
        by_contra h
        exact hb ⟨ha, h⟩
      have hc : s z v := s.trans (s.symm hb') ha
      have h0 : ∀ c, c ≠ Quotient.mk s z → scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c =
          scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c := by
        intro c _
        rw [hsplit, scostLL_clsPat_single_dropped true u v s ha, scostLL_clsPat_single_dropped true z v s hc,
          scostLL_clsPat_single_dropped true u z s hb']
        simp
      have := scostLL_contract_aux Γ rest z u v s hperm h0
      have k1 : scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s = [] := by simp [scostLL_kept, ha]
      have k2 : scostLL_kept [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s = [] := by
        simp [scostLL_kept, hb', hc]
      rw [k1, k2] at this
      simp only [List.length_nil, Nat.cast_zero] at this
      linarith
    · by_cases hb' : s u z
      · -- `[u] = [z] ≠ [v]`
        have hc : ¬ s z v := fun h => ha (s.trans hb' h)
        have hu' : Quotient.mk s u = Quotient.mk s z := Quotient.sound hb'
        have h0 : ∀ c, c ≠ Quotient.mk s z → scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c =
            scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c := by
          intro c hcz
          rw [hsplit, scostLL_clsPat_single_kept true u v s ha, scostLL_clsPat_single_kept true z v s hc,
            scostLL_clsPat_single_dropped true u z s hb', hu']
          simp [Ne.symm hcz]
        have := scostLL_contract_aux Γ rest z u v s hperm h0
        have k1 : scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s = [⟨true, false, u, v⟩] := by
          simp [scostLL_kept, ha]
        have k2 : scostLL_kept [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s =
            [⟨true, false, z, v⟩] := by simp [scostLL_kept, hb', hc]
        rw [k1, k2] at this
        simp only [List.length_singleton, Nat.cast_one] at this
        linarith
      · by_cases hc : s z v
        · -- `[z] = [v] ≠ [u]`
          have hv' : Quotient.mk s v = Quotient.mk s z := (Quotient.sound hc).symm
          have h0 : ∀ c, c ≠ Quotient.mk s z → scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c =
              scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c := by
            intro c hcz
            rw [hsplit, scostLL_clsPat_single_kept true u v s ha, scostLL_clsPat_single_dropped true z v s hc,
              scostLL_clsPat_single_kept true u z s hb', hv']
            simp [Ne.symm hcz]
          have := scostLL_contract_aux Γ rest z u v s hperm h0
          have k1 : scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s = [⟨true, false, u, v⟩] := by
            simp [scostLL_kept, ha]
          have k2 : scostLL_kept [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s =
              [⟨true, false, u, z⟩] := by simp [scostLL_kept, hb', hc]
          rw [k1, k2] at this
          simp only [List.length_singleton, Nat.cast_one] at this
          linarith
        · -- three classes
          have h0 : ∀ c, c ≠ Quotient.mk s z → scostLL_clsPat [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s c =
              scostLL_clsPat [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s c := by
            intro c hcz
            rw [hsplit, scostLL_clsPat_single_kept true u v s ha, scostLL_clsPat_single_kept true z v s hc,
              scostLL_clsPat_single_kept true u z s hb']
            simp [Ne.symm hcz]
          have := scostLL_contract_aux Γ rest z u v s hperm h0
          have k1 : scostLL_kept [(⟨true, false, u, v⟩ : SEdge (E ⊕ I))] s = [⟨true, false, u, v⟩] := by
            simp [scostLL_kept, ha]
          have k2 : scostLL_kept [(⟨true, false, z, v⟩ : SEdge (E ⊕ I)), ⟨true, false, u, z⟩] s =
              [⟨true, false, z, v⟩, ⟨true, false, u, z⟩] := by simp [scostLL_kept, hb', hc]
          rw [k1, k2] at this
          simp only [List.length_cons, List.length_nil] at this
          push_cast at this
          linarith

end ContractPrim

/-! ## 10. The placement lemma (F §4.3) -/

section Split

variable {V : Type}

/-- **`a` split off its class** (F §4.3): `u ~ v ↔ u = v ∨ (u ≠ a ∧ v ≠ a ∧ s u v)`. -/
def scostLL_split (a : V) (s : Setoid V) : Setoid V where
  r u v := u = v ∨ (u ≠ a ∧ v ≠ a ∧ s u v)
  iseqv := by
    refine ⟨fun u => Or.inl rfl, ?_, ?_⟩
    · rintro u v (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h.symm
      · exact Or.inr ⟨h2, h1, s.symm h3⟩
    · rintro u v w (h | ⟨h1, h2, h3⟩) (h' | ⟨h1', h2', h3'⟩)
      · exact Or.inl (h.trans h')
      · subst h
        exact Or.inr ⟨h1', h2', h3'⟩
      · subst h'
        exact Or.inr ⟨h1, h2, h3⟩
      · exact Or.inr ⟨h1, h2', s.trans h3 h3'⟩

private theorem scostLL_split_rel (a : V) (s : Setoid V) (u v : V) :
    scostLL_split a s u v ↔ u = v ∨ (u ≠ a ∧ v ≠ a ∧ s u v) := Iff.rfl

/-- after the split, `a` is alone in its class -/
theorem scostLL_split_alone (a : V) (s : Setoid V) : ∀ w, scostLL_split a s w a → w = a := by
  rintro w (h | ⟨-, h2, -⟩)
  · exact h
  · exact absurd rfl h2

theorem scostLL_split_of_alone (a : V) (s : Setoid V) (halone : ∀ w, s w a → w = a) : scostLL_split a s = s := by
  refine Setoid.ext (fun u v => ?_)
  constructor
  · rintro (h | ⟨-, -, h⟩)
    · exact h ▸ s.refl' _
    · exact h
  · intro h
    by_cases hu : u = a
    · subst hu
      exact Or.inl (halone v (s.symm h)).symm
    · by_cases hv : v = a
      · subst hv
        exact Or.inl (halone u h)
      · exact Or.inr ⟨hu, hv, h⟩

/-- `s` is the merge of the split setoid along `a` and any `w₀` of the class of `a` -/
theorem scostLL_split_merge (a w₀ : V) (s : Setoid V) (hw : s w₀ a) (hne : w₀ ≠ a) :
    s = scostLL_merge (scostLL_split a s) a w₀ := by
  refine Setoid.ext (fun x y => ?_)
  have hA : ∀ x, scostLL_split a s x a ↔ x = a := fun x => by
    constructor
    · exact scostLL_split_alone a s x
    · rintro rfl
      exact Or.inl rfl
  have hB : ∀ y, scostLL_split a s w₀ y ↔ (y ≠ a ∧ s w₀ y) := fun y => by
    constructor
    · rintro (h | ⟨-, h2, h3⟩)
      · subst h
        exact ⟨hne, s.refl' _⟩
      · exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨hne, h1, h2⟩
  have hC : ∀ x, scostLL_split a s x w₀ ↔ (x ≠ a ∧ s x w₀) := fun x => by
    constructor
    · rintro (h | ⟨h1, -, h3⟩)
      · subst h
        exact ⟨hne, s.refl' _⟩
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, hne, h2⟩
  have hD : ∀ y, scostLL_split a s a y ↔ y = a := fun y => by
    constructor
    · intro h
      exact (scostLL_split_alone a s y (scostLL_split a s |>.symm' h)).symm ▸ rfl
    · rintro rfl
      exact Or.inl rfl
  rw [scostLL_merge_rel, hA, hB, hC, hD, scostLL_split_rel]
  constructor
  · intro h
    by_cases hx : x = a <;> by_cases hy : y = a
    · exact Or.inl (Or.inl (hx.trans hy.symm))
    · exact Or.inr (Or.inl ⟨hx, hy, by subst hx; exact s.trans hw h⟩)
    · exact Or.inr (Or.inr ⟨⟨hx, by subst hy; exact s.trans h (s.symm hw)⟩, hy⟩)
    · exact Or.inl (Or.inr ⟨hx, hy, h⟩)
  · rintro ((h | ⟨-, -, h⟩) | ⟨hx, -, h⟩ | ⟨⟨-, h⟩, hy⟩)
    · exact h ▸ s.refl' _
    · exact h
    · subst hx
      exact s.trans (s.symm hw) h
    · subst hy
      exact s.trans h hw

end Split

section Placement

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- the split does not change the restriction to the old vertices -/
theorem scostLL_split_comap (s : Setoid (E ⊕ (I ⊕ Fin 1))) :
    Setoid.comap (owxEmb 1) (scostLL_split (Sum.inr (Sum.inr 0)) s) = Setoid.comap (owxEmb 1) s := by
  refine Setoid.ext (fun u v => ?_)
  constructor
  · rintro (h | ⟨-, -, h⟩)
    · show s (owxEmb 1 u) (owxEmb 1 v)
      rw [h]
    · exact h
  · intro h
    exact Or.inr ⟨scostLL_emb_ne_alpha u, scostLL_emb_ne_alpha v, h⟩

/-- the split does not change the relation on the external vertices -/
theorem scostLL_split_inl (s : Setoid (E ⊕ (I ⊕ Fin 1))) (a b : E) :
    scostLL_split (Sum.inr (Sum.inr 0)) s (Sum.inl a) (Sum.inl b) ↔ s (Sum.inl a) (Sum.inl b) := by
  constructor
  · rintro (h | ⟨-, -, h⟩)
    · exact h ▸ s.refl' _
    · exact h
  · intro h
    exact Or.inr ⟨scostLL_inl_ne_alpha a, scostLL_inl_ne_alpha b, h⟩

open Classical in
private theorem scostLL_joined_map_emb (L : List (SEdge (E ⊕ I))) (s' : Setoid (E ⊕ (I ⊕ Fin 1)))
    (halone : ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) (w₀ : E ⊕ (I ⊕ Fin 1)) :
    scostLL_joined (L.map (SEdge.map (owxEmb 1))) s' (Sum.inr (Sum.inr 0)) w₀ = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro e he
  simp only [scostLL_joined, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at he
  obtain ⟨he, -, hends⟩ := he
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  rcases hends with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact scostLL_emb_ne_alpha _ (halone _ h1)
  · exact scostLL_emb_ne_alpha _ (halone _ h2)

open Classical in
/-- **Placement, general form** (F §4.3): with `s''` the split of `s` at `α` and `w₀` an old vertex of the class of `α`, the
cost of `T` (`T.solid ~ L.map (owxEmb 1) ++ Aα`) at `s` exceeds that at `s''` by `2 - #joined - [elem A_α] + [Z internal]
([elem m] - [elem b])`, `m + dp = A_α + b`. -/
private theorem scostLL_placement_gen (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I)))
    (Aα : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ Aα))
    (s s'' : Setoid (E ⊕ (I ⊕ Fin 1))) (hs'' : s'' = scostLL_split (Sum.inr (Sum.inr 0)) s)
    (w₀ : E ⊕ (I ⊕ Fin 1)) (hw : s w₀ (Sum.inr (Sum.inr 0))) (hne : w₀ ≠ Sum.inr (Sum.inr 0)) :
    ∃ m b : ℕ × ℕ × ℕ × ℕ,
      m + lwHalfPat (scostLL_joined Aα s'' (Sum.inr (Sum.inr 0)) w₀)
          (fun w => s'' w (Sum.inr (Sum.inr 0)) ∨ s'' w w₀) =
        scostLL_clsPat Aα s'' (Quotient.mk _ (Sum.inr (Sum.inr 0))) + b ∧
      T.scost s - T.scost s'' =
        2 - ((scostLL_joined Aα s'' (Sum.inr (Sum.inr 0)) w₀).length : ℤ) -
          scostLL_el (scostLL_clsPat Aα s'' (Quotient.mk _ (Sum.inr (Sum.inr 0)))) +
        (if (∀ a : E, ¬ s'' (Sum.inl a) w₀) then scostLL_el m - scostLL_el b else 0) := by
  have halone : ∀ w, s'' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0) := by
    rw [hs'']
    exact scostLL_split_alone _ s
  have hmerge : s = scostLL_merge s'' (Sum.inr (Sum.inr 0)) w₀ := by
    rw [hs'']
    exact scostLL_split_merge _ w₀ s hw hne
  have huz : ¬ s'' (Sum.inr (Sum.inr 0)) w₀ := fun h => hne (halone _ (s''.symm h))
  have hU : ∀ a : E, ¬ s'' (Sum.inl a) (Sum.inr (Sum.inr 0)) := fun a h => scostLL_inl_ne_alpha a (halone _ h)
  have hM := scostLL_merge_scost T s'' (Sum.inr (Sum.inr 0)) w₀ huz
  have hP := scostLL_clsPat_merge_M T.solid s'' (Sum.inr (Sum.inr 0)) w₀ huz
  have hT1 : scostLL_clsPat T.solid s'' (Quotient.mk s'' (Sum.inr (Sum.inr 0))) =
      scostLL_clsPat Aα s'' (Quotient.mk s'' (Sum.inr (Sum.inr 0))) := by
    rw [scostLL_clsPat_perm hT, scostLL_clsPat_append, scostLL_clsPat_map_alpha L s'' halone, zero_add]
  have hjT : (scostLL_joined T.solid s'' (Sum.inr (Sum.inr 0)) w₀).Perm
      (scostLL_joined Aα s'' (Sum.inr (Sum.inr 0)) w₀) := by
    refine (scostLL_joined_perm hT s'' _ w₀).trans ?_
    rw [scostLL_joined_append, scostLL_joined_map_emb L s'' halone w₀, List.nil_append]
  rw [hT1] at hM hP
  rw [localReg6a_halfPat_perm hjT] at hP
  rw [hjT.length_eq] at hM
  refine ⟨scostLL_clsPat T.solid (scostLL_merge s'' (Sum.inr (Sum.inr 0)) w₀) (Quotient.mk _ (Sum.inr (Sum.inr 0))),
    scostLL_clsPat T.solid s'' (Quotient.mk s'' w₀), hP, ?_⟩
  rw [← hmerge] at hM ⊢
  by_cases hZ : ∀ a : E, ¬ s'' (Sum.inl a) w₀
  · simp only [eq_true hZ, eq_true hU, and_self, ↓reduceIte] at hM ⊢
    linarith
  · simp only [eq_false hZ, eq_true hU, and_false, ↓reduceIte] at hM ⊢
    linarith

/-- two half-edges at `α` that form an elementary pattern are the two halves of an edge of the colour of the first -/
private theorem scostLL_psi_sc (σ₁ σ₂ : Bool) (d₁ d₂ : Prop) [Decidable d₁] [Decidable d₂]
    (h : scostLL_el ((if d₁ then scostLL_hout σ₁ else scostLL_hin σ₁) +
      (if d₂ then scostLL_hout σ₂ else scostLL_hin σ₂)) = 1) :
    (if d₁ then scostLL_hout σ₁ else scostLL_hin σ₁) + (if d₂ then scostLL_hout σ₂ else scostLL_hin σ₂) =
      scostLL_hin σ₁ + scostLL_hout σ₁ := by
  by_cases h1 : d₁ <;> by_cases h2 : d₂ <;> simp only [h1, h2, ite_true, ite_false] at h ⊢ <;>
    revert h <;> cases σ₁ <;> cases σ₂ <;> decide

open Classical in
/-- the class pattern of an uncircled edge with exactly one end at the alone vertex `α`, at the class of `α` -/
private theorem scostLL_clsPat_edge_alpha {V : Type} (α : V) (s' : Setoid V) (halone : ∀ w, s' w α → w = α) (e : SEdge V)
    [Decidable (e.src = α)] (hc : e.circ = false)
    (hshape : (e.src = α ∧ e.dst ≠ α) ∨ (e.dst = α ∧ e.src ≠ α)) :
    scostLL_clsPat [e] s' (Quotient.mk s' α) = if e.src = α then scostLL_hout e.σ else scostLL_hin e.σ := by
  rcases e with ⟨σ, c, x, y⟩
  simp only at hc hshape ⊢
  subst hc
  have hk : ¬ s' x y := by
    rcases hshape with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact fun h' => h (halone _ (s'.symm h'))
    · exact fun h' => h (halone _ h')
  rw [scostLL_clsPat_single_kept σ x y s' hk]
  have hα : ∀ w, Quotient.mk s' w = Quotient.mk s' α ↔ w = α := fun w =>
    ⟨fun h => halone _ (Quotient.exact h), fun h => h ▸ rfl⟩
  rcases hshape with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · have h1 : ¬ Quotient.mk s' y = Quotient.mk s' x := fun h' => h ((hα y).1 h')
    simp [h1]
  · have h1 : ¬ Quotient.mk s' x = Quotient.mk s' y := fun h' => h ((hα x).1 h')
    simp [h1, h]

private theorem scostLL_joined_pred {V : Type} (α w₀ : V) (s : Setoid V) (hw : s w₀ α) (hne : w₀ ≠ α) (x y : V)
    (hshape : (x = α ∧ y ≠ α) ∨ (y = α ∧ x ≠ α)) :
    ((scostLL_split α s x α ∧ scostLL_split α s y w₀) ∨ (scostLL_split α s x w₀ ∧ scostLL_split α s y α)) ↔
      s x y := by
  have hC : ∀ y, y ≠ α → (scostLL_split α s y w₀ ↔ s y w₀) := fun y hy => by
    constructor
    · rintro (h | ⟨-, -, h⟩)
      · exact h ▸ s.refl' _
      · exact h
    · intro h
      exact Or.inr ⟨hy, hne, h⟩
  rcases hshape with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · constructor
    · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
      · exact s.trans (s.symm hw) (s.symm ((hC y h).1 h2))
      · rcases h1 with h1 | ⟨h1, -⟩
        · exact absurd h1 (Ne.symm hne)
        · exact absurd rfl h1
    · intro h'
      exact Or.inl ⟨Or.inl rfl, (hC y h).2 (s.trans (s.symm h') (s.symm hw))⟩
  · constructor
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · rcases h1 with h1 | ⟨-, h1, -⟩
        · exact absurd h1 h
        · exact absurd rfl h1
      · exact s.trans ((hC x h).1 h1) hw
    · intro h'
      exact Or.inr ⟨(hC x h).2 (s.trans h' (s.symm hw)), Or.inl rfl⟩

open Classical in
private theorem scostLL_joined_single {V : Type} (α w₀ : V) (s : Setoid V) (hw : s w₀ α) (hne : w₀ ≠ α) (e : SEdge V)
    (hc : e.circ = false) (hshape : (e.src = α ∧ e.dst ≠ α) ∨ (e.dst = α ∧ e.src ≠ α)) :
    scostLL_joined [e] (scostLL_split α s) α w₀ = if s e.src e.dst then [e] else [] := by
  have key := scostLL_joined_pred α w₀ s hw hne e.src e.dst hshape
  unfold scostLL_joined
  by_cases h : s e.src e.dst
  · have h' := key.2 h
    simp [hc, h, h']
  · have h' : ¬ ((scostLL_split α s e.src α ∧ scostLL_split α s e.dst w₀) ∨
        (scostLL_split α s e.src w₀ ∧ scostLL_split α s e.dst α)) := fun h'' => h (key.1 h'')
    simp [hc, h, h']

open Classical in
/-- **Placement, loop shape** (F §4.3, `Loop`, `MoveLoop`): `T.solid ~ L.map (owxEmb 1) ++ [circled loop at α]`; splitting `α`
off its class never raises the cost. -/
theorem scostLL_placement_loop (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I))) (col : Bool)
    (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++
      [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]))
    (s : Setoid (E ⊕ (I ⊕ Fin 1))) :
    T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s := by
  by_cases halone : ∀ w, s w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · rw [scostLL_split_of_alone _ s halone]
  · push Not at halone
    obtain ⟨w₀, hw, hne⟩ := halone
    obtain ⟨m, b, -, hΔ⟩ := scostLL_placement_gen T L _ hT s _ rfl w₀ hw hne
    have hD : scostLL_joined [(⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1)))]
        (scostLL_split (Sum.inr (Sum.inr 0)) s) (Sum.inr (Sum.inr 0)) w₀ = [] := by simp [scostLL_joined]
    rw [hD, scostLL_clsPat_loop] at hΔ
    simp only [eq_self, ↓reduceIte, scostLL_el_pair] at hΔ
    have h1 := scostLL_el_nonneg m
    have h2 := scostLL_el_le_one b
    split_ifs at hΔ <;> simp only [List.length_nil, Nat.cast_zero] at hΔ <;> linarith

open Classical in
private theorem scostLL_placement_two_aux (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I)))
    (e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)))
    (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ [e₁, e₂]))
    (c₁ : e₁.circ = false)
    (h₁ : (e₁.src = Sum.inr (Sum.inr 0) ∧ e₁.dst ≠ Sum.inr (Sum.inr 0)) ∨
      (e₁.dst = Sum.inr (Sum.inr 0) ∧ e₁.src ≠ Sum.inr (Sum.inr 0)))
    (c₂ : e₂.circ = false)
    (h₂ : (e₂.src = Sum.inr (Sum.inr 0) ∧ e₂.dst ≠ Sum.inr (Sum.inr 0)) ∨
      (e₂.dst = Sum.inr (Sum.inr 0) ∧ e₂.src ≠ Sum.inr (Sum.inr 0)))
    (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk₂ : ¬ s e₂.src e₂.dst) :
    T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s := by
  by_cases halone : ∀ w, s w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)
  · rw [scostLL_split_of_alone _ s halone]
  · push Not at halone
    obtain ⟨w₀, hw, hne⟩ := halone
    obtain ⟨m, b, hrel, hΔ⟩ := scostLL_placement_gen T L [e₁, e₂] hT s _ rfl w₀ hw hne
    have halone'' := scostLL_split_alone (Sum.inr (Sum.inr 0) : E ⊕ (I ⊕ Fin 1)) s
    have hJ2 : scostLL_joined [e₂] (scostLL_split (Sum.inr (Sum.inr 0)) s) (Sum.inr (Sum.inr 0)) w₀ = [] := by
      rw [scostLL_joined_single _ w₀ s hw hne e₂ c₂ h₂]
      simp only [hk₂, ↓reduceIte]
    have hJ : scostLL_joined [e₁, e₂] (scostLL_split (Sum.inr (Sum.inr 0)) s) (Sum.inr (Sum.inr 0)) w₀ =
        (if s e₁.src e₁.dst then [e₁] else []) := by
      show scostLL_joined ([e₁] ++ [e₂]) _ _ w₀ = _
      rw [scostLL_joined_append, scostLL_joined_single _ w₀ s hw hne e₁ c₁ h₁, hJ2, List.append_nil]
    have hpat : scostLL_clsPat [e₁, e₂] (scostLL_split (Sum.inr (Sum.inr 0)) s)
        (Quotient.mk _ (Sum.inr (Sum.inr 0))) =
        (if e₁.src = Sum.inr (Sum.inr 0) then scostLL_hout e₁.σ else scostLL_hin e₁.σ) +
          (if e₂.src = Sum.inr (Sum.inr 0) then scostLL_hout e₂.σ else scostLL_hin e₂.σ) := by
      rw [show [e₁, e₂] = [e₁] ++ [e₂] from rfl, scostLL_clsPat_append,
        scostLL_clsPat_edge_alpha _ _ halone'' e₁ c₁ h₁, scostLL_clsPat_edge_alpha _ _ halone'' e₂ c₂ h₂]
    rw [hJ, hpat] at hΔ hrel
    have hb1 := scostLL_el_nonneg m
    have hb2 := scostLL_el_le_one b
    have hscP : scostLL_el ((if e₁.src = Sum.inr (Sum.inr 0) then scostLL_hout e₁.σ else scostLL_hin e₁.σ) +
        (if e₂.src = Sum.inr (Sum.inr 0) then scostLL_hout e₂.σ else scostLL_hin e₂.σ)) = 1 →
        (if e₁.src = Sum.inr (Sum.inr 0) then scostLL_hout e₁.σ else scostLL_hin e₁.σ) +
          (if e₂.src = Sum.inr (Sum.inr 0) then scostLL_hout e₂.σ else scostLL_hin e₂.σ) =
        scostLL_hin e₁.σ + scostLL_hout e₁.σ := fun hel => scostLL_psi_sc _ _ _ _ hel
    generalize (if e₁.src = Sum.inr (Sum.inr 0) then scostLL_hout e₁.σ else scostLL_hin e₁.σ) +
      (if e₂.src = Sum.inr (Sum.inr 0) then scostLL_hout e₂.σ else scostLL_hin e₂.σ) = P at hΔ hrel hscP
    have hb3 := scostLL_el_le_one P
    have hb4 := scostLL_el_nonneg P
    by_cases hd : s e₁.src e₁.dst
    · simp only [hd, ite_true, List.length_singleton, Nat.cast_one] at hΔ hrel
      have hK := (scostLL_joined_pred _ w₀ s hw hne e₁.src e₁.dst h₁).2 hd
      have hKs : (scostLL_split (Sum.inr (Sum.inr 0)) s e₁.src (Sum.inr (Sum.inr 0)) ∨
          scostLL_split (Sum.inr (Sum.inr 0)) s e₁.src w₀) ∧
          (scostLL_split (Sum.inr (Sum.inr 0)) s e₁.dst (Sum.inr (Sum.inr 0)) ∨
            scostLL_split (Sum.inr (Sum.inr 0)) s e₁.dst w₀) := by
        rcases hK with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨Or.inl h1, Or.inr h2⟩
        · exact ⟨Or.inr h1, Or.inl h2⟩
      have hdp : lwHalfPat [e₁] (fun w => scostLL_split (Sum.inr (Sum.inr 0)) s w (Sum.inr (Sum.inr 0)) ∨
          scostLL_split (Sum.inr (Sum.inr 0)) s w w₀) = scostLL_hin e₁.σ + scostLL_hout e₁.σ := by
        rw [scostLL_halfPat_single]
        simp only [hKs.1, hKs.2, ↓reduceIte]
      rw [hdp] at hrel
      by_cases hel : scostLL_el P = 1
      · have hsc := hscP hel
        rw [hsc] at hrel
        have hmb : m = b := by
          have h3 : (scostLL_hin e₁.σ + scostLL_hout e₁.σ) + m = (scostLL_hin e₁.σ + scostLL_hout e₁.σ) + b := by
            rw [add_comm, hrel]
          exact add_left_cancel h3
        subst hmb
        rw [hel] at hΔ
        split_ifs at hΔ <;> linarith
      · split_ifs at hΔ <;> omega
    · simp only [hd, ite_false, List.length_nil, Nat.cast_zero] at hΔ
      split_ifs at hΔ <;> linarith

open Classical in
/-- **Placement, two-edge shape** (F §4.3, `MoveSC`, `MoveOut`, `Dmove`): `T.solid ~ L.map (owxEmb 1) ++ [e₁, e₂]`, each `e_i`
uncircled with exactly one end at `α` and the other end old; if the two edges are not both inside a class of `s`
(`k ≤ 1`), splitting `α` off its class never raises the cost. -/
theorem scostLL_placement_two (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I)))
    (e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)))
    (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ [e₁, e₂]))
    (c₁ : e₁.circ = false)
    (h₁ : (e₁.src = Sum.inr (Sum.inr 0) ∧ e₁.dst ≠ Sum.inr (Sum.inr 0)) ∨
      (e₁.dst = Sum.inr (Sum.inr 0) ∧ e₁.src ≠ Sum.inr (Sum.inr 0)))
    (c₂ : e₂.circ = false)
    (h₂ : (e₂.src = Sum.inr (Sum.inr 0) ∧ e₂.dst ≠ Sum.inr (Sum.inr 0)) ∨
      (e₂.dst = Sum.inr (Sum.inr 0) ∧ e₂.src ≠ Sum.inr (Sum.inr 0)))
    (s : Setoid (E ⊕ (I ⊕ Fin 1))) (hk : ¬ (s e₁.src e₁.dst ∧ s e₂.src e₂.dst)) :
    T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s := by
  by_cases hd₂ : s e₂.src e₂.dst
  · have hd₁ : ¬ s e₁.src e₁.dst := fun h => hk ⟨h, hd₂⟩
    exact scostLL_placement_two_aux T L e₂ e₁
      (hT.trans (List.Perm.append_left _ (List.Perm.swap e₂ e₁ []))) c₂ h₂ c₁ h₁ s hd₁
  · exact scostLL_placement_two_aux T L e₁ e₂ hT c₁ h₁ c₂ h₂ s hd₂

open Classical in
/-- **Placement** (F §4.3), both shapes of `A_α`: one circled loop at `α` (`Loop`, `MoveLoop`) or two uncircled edges with
one end at `α` and the other end old, not both inside a class of `s` (`k ≤ 1`; `MoveSC`, `MoveOut`, `Dmove`).  `T` is any
graph whose solid list is a permutation of `L.map (owxEmb 1) ++ A_α` (the `owxExt` form); the number of waved edges is
irrelevant. -/
theorem scostLL_placement (T : LGraph E (I ⊕ Fin 1)) (L : List (SEdge (E ⊕ I)))
    (Aα : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (hT : T.solid.Perm (L.map (SEdge.map (owxEmb 1)) ++ Aα))
    (hA : (∃ col : Bool, Aα = [⟨col, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]) ∨
      ∃ e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)), Aα = [e₁, e₂] ∧
        e₁.circ = false ∧ ((e₁.src = Sum.inr (Sum.inr 0) ∧ e₁.dst ≠ Sum.inr (Sum.inr 0)) ∨
          (e₁.dst = Sum.inr (Sum.inr 0) ∧ e₁.src ≠ Sum.inr (Sum.inr 0))) ∧
        e₂.circ = false ∧ ((e₂.src = Sum.inr (Sum.inr 0) ∧ e₂.dst ≠ Sum.inr (Sum.inr 0)) ∨
          (e₂.dst = Sum.inr (Sum.inr 0) ∧ e₂.src ≠ Sum.inr (Sum.inr 0))))
    (s : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hk : ∀ e₁ e₂ : SEdge (E ⊕ (I ⊕ Fin 1)), Aα = [e₁, e₂] → ¬ (s e₁.src e₁.dst ∧ s e₂.src e₂.dst)) :
    T.scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ T.scost s := by
  rcases hA with ⟨col, rfl⟩ | ⟨e₁, e₂, rfl, c₁, h₁, c₂, h₂⟩
  · exact scostLL_placement_loop T L col hT s
  · exact scostLL_placement_two T L e₁ e₂ hT c₁ h₁ c₂ h₂ s (hk e₁ e₂ rfl)

end Placement

/-! ## 11. Localisation, the fresh vertex with all added edges dropped -/

section Localise

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- a sum supported on a finite set -/
theorem scostLL_sum_support {Q : Type} [DecidableEq Q] (S C : Finset Q) (d : Q → ℤ) (h : ∀ c, c ∉ C → d c = 0) :
    ∑ c ∈ S, d c = ∑ c ∈ C, (if c ∈ S then d c else 0) := by
  have h1 : ∑ c ∈ S ∩ C, d c = ∑ c ∈ S, d c :=
    Finset.sum_subset Finset.inter_subset_left (fun x hx hn => h x (fun hc => hn (Finset.mem_inter.2 ⟨hx, hc⟩)))
  rw [← h1, Finset.sum_ite_mem, Finset.inter_comm]

open Classical in
/-- a class that contains no end of an edge of the list sees no half-edge of it -/
theorem scostLL_clsPat_zero_of_ends {V : Type} (R : List (SEdge V)) (s : Setoid V) (c : Quotient s)
    (h : ∀ e ∈ R, Quotient.mk s e.src ≠ c ∧ Quotient.mk s e.dst ≠ c) : scostLL_clsPat R s c = 0 := by
  unfold scostLL_clsPat
  refine scostLL_halfPat_zero_of_ends _ _ (fun e he => ?_)
  exact h e ((scostLL_mem_kept R s e).1 he).1

open Classical in
/-- **The localisation** (F §4.1 (c), one vertex type): the two class sums differ only on any `C : Finset (Quotient s)` that
contains the classes of the ends of the edges of `R ++ A`. -/
theorem scostLL_local_diff_C (Γ Γ' : LGraph E I) (R A X : List (SEdge (E ⊕ I))) (s : Setoid (E ⊕ I))
    (hΓ : Γ.solid.Perm (R ++ X)) (hΓ' : Γ'.solid.Perm (A ++ X)) (C : Finset (Quotient s))
    (hR : ∀ e ∈ R, Quotient.mk s e.src ∈ C ∧ Quotient.mk s e.dst ∈ C)
    (hA : ∀ e ∈ A, Quotient.mk s e.src ∈ C ∧ Quotient.mk s e.dst ∈ C) :
    Γ'.scost s - Γ.scost s =
      ((scostLL_kept A s).length : ℤ) - ((scostLL_kept R s).length : ℤ) +
        2 * ((Γ'.waved.length : ℤ) - (Γ.waved.length : ℤ)) +
        ∑ c ∈ C, (if c ∈ Γ.sIntCls s then
          scostLL_el (scostLL_clsPat A s c + scostLL_clsPat X s c) -
            scostLL_el (scostLL_clsPat R s c + scostLL_clsPat X s c) else 0) := by
  rw [scostLL_local_diff Γ Γ' R A X s hΓ hΓ']
  congr 1
  refine scostLL_sum_support _ C _ (fun c hc => ?_)
  have h1 : scostLL_clsPat A s c = 0 :=
    scostLL_clsPat_zero_of_ends A s c (fun e he => ⟨fun h => hc (h ▸ (hA e he).1), fun h => hc (h ▸ (hA e he).2)⟩)
  have h2 : scostLL_clsPat R s c = 0 :=
    scostLL_clsPat_zero_of_ends R s c (fun e he => ⟨fun h => hc (h ▸ (hR e he).1), fun h => hc (h ▸ (hR e he).2)⟩)
  rw [h1, h2, sub_self]

open Classical in
/-- **The fresh vertex in a class, all added edges dropped** (`k = 2` of F §4.5): if `α` shares a class with an old vertex and no
edge of `A` is kept, the cost is that of the old graph at `s₀`, plus `2` per waved edge. -/
theorem scostLL_fresh_dropped (Γ : LGraph E I) (c : ℂ) (A : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (W : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (hA : scostLL_kept A s' = [])
    (hna : ¬ ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) :
    (Γ.owxExt (owxEmb 1) c A W).scost s' = Γ.scost (Setoid.comap (owxEmb 1) s') + 2 * (W.length : ℤ) := by
  have hpat : ∀ c' : Quotient s', scostLL_clsPat A s' c' = 0 := fun c' => by
    unfold scostLL_clsPat
    rw [hA]
    simp [lwHalfPat]
  rw [scostLL_fresh_scost, scostLL_scost_eq Γ (Setoid.comap (owxEmb 1) s')]
  simp only [eq_false hna, ↓reduceIte, hpat, add_zero, hA, List.length_nil, Nat.cast_zero]
  ring

end Localise

/-! ## 12. Compiled instances (CLAUDE.md §4 step 2) -/

section Instances

private theorem localReg6b_hk_two {V : Type} (e₁ e₂ : SEdge V) (P : SEdge V → SEdge V → Prop) (hk : P e₁ e₂) :
    ∀ e₁' e₂' : SEdge V, [e₁, e₂] = [e₁', e₂'] → P e₁' e₂' := by
  intro e₁' e₂' h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl⟩ := h
  exact hk

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- Instance (1), `scostLL_loop` at `Γ_2 = fxyPowGraph 2`, `z = x`, blue. -/
theorem localReg6b_inst_loop :
    LGraph.ScostLL (fxyPowGraph 2) (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) :=
  scostLL_loop (fxyPowGraph 2) (Sum.inl 0) true

/-- Instance (1'), the term `T1 = owxT1 m Γ x` of `(Owx)`: `Loop(x)` at an arbitrary graph (`owxT1` and `lwPrimLoop` have the
same solid list and the same waved list, up to the coefficient). -/
theorem localReg6b_inst_T1 (m : ℂ) (Γ : LGraph E I) (x : I) : LGraph.ScostLL Γ (owxT1 m Γ x) :=
  LGraph.ScostLL.of_perm Γ (lwPrimLoop Γ (Sum.inr x) true) (owxT1 m Γ x) (List.Perm.refl _) rfl
    (scostLL_loop Γ (Sum.inr x) true)

/-- Instance (2), `scostLL_addLoop` at `Γ_2`, `z = β_0`, blue. -/
theorem localReg6b_inst_addLoop :
    LGraph.ScostLL (fxyPowGraph 2) (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true) :=
  scostLL_addLoop (fxyPowGraph 2) (Sum.inr 1) true

/-- the hypothesis of instance (3): the blue light-weight at `β_0` is the head of the solid list of `Γ_2` -/
theorem localReg6b_inst_moveLoopPerm :
    (fxyPowGraph 2).solid.Perm (⟨true, true, Sum.inr 1, Sum.inr 1⟩ :: (fxyPowGraph 2).solid.tail) :=
  List.Perm.refl _

/-- Instance (3), `scostLL_moveLoop` at `Γ_2`, `z = β_0`, blue. -/
theorem localReg6b_inst_moveLoop :
    LGraph.ScostLL (fxyPowGraph 2) (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true) :=
  scostLL_moveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true localReg6b_inst_moveLoopPerm

/-- The 2-cycle `Z → U → Z` of one colour (two blue edges `inr 0 ⇄ inr 1`), no waved or dotted edge: `scost ⊥ = 0`. -/
def localReg6b_instCyc : LGraph (Fin 2) (Fin 2) where
  solid := [⟨true, false, .inr 0, .inr 1⟩, ⟨true, false, .inr 1, .inr 0⟩]
  waved := []
  dotted := []
  coeff := 1

/-- Instance (4), `scostLL_contract` at the 2-cycle: `Contract(z; u, u)` with `z = inr 0`, `u = v = inr 1` (the collapse; every
hypothesis is discharged). -/
theorem localReg6b_inst_contract :
    LGraph.ScostLL localReg6b_instCyc (lwPrimContract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1)) :=
  scostLL_contract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1) (by decide) (by decide) (List.Perm.refl _)

open Classical in
/-- the trivial merge of the 2-cycle costs `0` -/
theorem localReg6b_instCyc_bot : localReg6b_instCyc.scost ⊥ = 0 := by
  have hk : localReg6b_instCyc.skept ⊥ = localReg6b_instCyc.solid := by
    simp [LGraph.skept, localReg6b_instCyc]
  unfold LGraph.scost
  rw [hk, localReg6a_sIntCls_bot_card, localReg6a_sElemCls_bot_card _ hk]
  have h : localReg6b_instCyc.nElem = 2 := by decide
  rw [h]
  simp [localReg6b_instCyc]

open Classical in
/-- the contracted 2-cycle costs `-2` at the trivial merge: the witness `s₀ = ⊥` fails, the repair is forced -/
theorem localReg6b_instCyc_contract_bot :
    (lwPrimContract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1)).scost ⊥ = -2 := by
  set Γ' := lwPrimContract localReg6b_instCyc [] (.inr 0) (.inr 1) (.inr 1) with hΓ'
  have hk : Γ'.skept ⊥ = [] := by simp [LGraph.skept, hΓ', lwPrimContract]
  have hk' : ({ Γ' with solid := [] } : LGraph (Fin 2) (Fin 2)).skept ⊥ =
      ({ Γ' with solid := [] } : LGraph (Fin 2) (Fin 2)).solid := by simp [LGraph.skept]
  rw [localReg6a_scost_congr Γ' { Γ' with solid := [] } ⊥ (by rw [hk]; simp [LGraph.skept]) rfl]
  unfold LGraph.scost
  rw [hk', localReg6a_sIntCls_bot_card, localReg6a_sElemCls_bot_card _ hk']
  have h : ({ Γ' with solid := [] } : LGraph (Fin 2) (Fin 2)).nElem = 0 := by decide
  rw [h]
  simp [hΓ', lwPrimContract, localReg6b_instCyc]

open Classical in
/-- the 2-cycle removed costs `-4` at the trivial merge -/
theorem localReg6b_instCyc_L_bot :
    ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ = -4 := by
  have hk : ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).skept ⊥ =
      ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).solid := by simp [LGraph.skept]
  unfold LGraph.scost
  rw [hk, localReg6a_sIntCls_bot_card, localReg6a_sElemCls_bot_card _ hk]
  have h : ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).nElem = 0 := by decide
  rw [h]
  simp [localReg6b_instCyc]

/-- Instance (4), `scostLL_repair` at the 2-cycle with `s = ⊥`: the witness is `⊥` or the merge of the two vertices. -/
theorem localReg6b_inst_repair :
    ∃ s₀ : Setoid (Fin 2 ⊕ Fin 2), (s₀ = ⊥ ∨ s₀ = scostLL_merge ⊥ (Sum.inr 1) (Sum.inr 0)) ∧
      (∀ a b : Fin 2, ¬ (⊥ : Setoid (Fin 2 ⊕ Fin 2)) (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧
      localReg6b_instCyc.scost s₀ ≤ ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ + 2 :=
  scostLL_repair localReg6b_instCyc [] true (.inr 0) (.inr 1) (.inr 1) (.inr 0) (.inr 1) ⊥ (List.Perm.refl _) rfl rfl
    rfl (by simp)

/-- the repair is forced at the 2-cycle: `s₀ = ⊥` is not a witness (`0 ≤ -4 + 2` is false) -/
theorem localReg6b_instCyc_repair_forced :
    ¬ localReg6b_instCyc.scost ⊥ ≤ ({ localReg6b_instCyc with solid := [] } : LGraph (Fin 2) (Fin 2)).scost ⊥ + 2 := by
  rw [localReg6b_instCyc_bot, localReg6b_instCyc_L_bot]
  decide

/-- Instance (4'), the term `R2 = oe2xR2 m Γ q x y y'` of the `GG` expansion: `Contract(x; y', y)`. -/
theorem localReg6b_inst_R2 (m : ℂ) (Γ : LGraph E I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (h1 : y' ≠ Sum.inr x) (h2 : Sum.inr x ≠ y)
    (hperm : Γ.solid.Perm (⟨true, false, Sum.inr x, y⟩ :: ⟨true, false, y', Sum.inr x⟩ :: q.2)) :
    LGraph.ScostLL Γ (oe2xR2 m Γ q x y y') := by
  refine LGraph.ScostLL.of_perm Γ (lwPrimContract Γ q.2 (Sum.inr x) y' y) (oe2xR2 m Γ q x y y') ?_ ?_
    (scostLL_contract Γ q.2 (Sum.inr x) y' y h1 h2 hperm)
  · have hm : q.2.map (SEdge.map (id : E ⊕ I → E ⊕ I)) = q.2 := List.map_id'' (fun e => rfl) q.2
    show (⟨true, false, y', y⟩ :: q.2).Perm (q.2.map (SEdge.map id) ++ [⟨true, false, y', y⟩])
    rw [hm]
    exact (List.perm_append_singleton _ _).symm
  · simp [lwPrimContract, oe2xR2, LGraph.owxExt]

/-- Instance (5), `trans` at `Loop(x)` then `AddLoop` at the fresh vertex `α`, red. -/
theorem localReg6b_inst_trans : LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimAddLoop (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) (Sum.inr (Sum.inr 0)) false) :=
  LGraph.ScostLL.trans (fxyPowGraph 2) (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true)
    (lwPrimAddLoop (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) (Sum.inr (Sum.inr 0)) false)
    (scostLL_loop (fxyPowGraph 2) (Sum.inl 0) true)
    (scostLL_addLoop (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) (Sum.inr (Sum.inr 0)) false)

/-- an explicit onto relabelling `I ⊕ Fin 1 ⊕ Fin 1 → I ⊕ Fin 2` fixing the external vertices (`Equiv.sumAssoc`, `finSumFinEquiv`) -/
def localReg6b_phi : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 1) ⊕ Fin 1) → Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 2) :=
  Sum.map id ((Equiv.sumAssoc (Fin (2 * 2)) (Fin 1) (Fin 1)).trans
    (Equiv.sumCongr (Equiv.refl (Fin (2 * 2))) finSumFinEquiv))

theorem localReg6b_phi_surj : Function.Surjective localReg6b_phi :=
  Function.Surjective.sumMap Function.surjective_id
    ((Equiv.sumAssoc (Fin (2 * 2)) (Fin 1) (Fin 1)).trans
      (Equiv.sumCongr (Equiv.refl (Fin (2 * 2))) finSumFinEquiv)).surjective

/-- Instance (6), `trans` and `of_relabel` at the `owxT2` shape: `MoveLoop(β_0)` then `Loop(α)`, relabelled to `I ⊕ Fin 2` by
the explicit `localReg6b_phi`. -/
theorem localReg6b_inst_T2 : LGraph.ScostLL (fxyPowGraph 2)
    ((lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
      (Sum.inr (Sum.inr 0)) true).relabel localReg6b_phi) :=
  LGraph.ScostLL.of_relabel (fxyPowGraph 2) _ localReg6b_phi localReg6b_phi_surj (fun _ => rfl)
    (LGraph.ScostLL.trans (fxyPowGraph 2)
      (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
      (lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
        (Sum.inr (Sum.inr 0)) true) localReg6b_inst_moveLoop
      (scostLL_loop _ (Sum.inr (Sum.inr 0)) true))

/-- Instance (6), the statement of the check file (every onto `φ` fixing `inl`). -/
theorem localReg6b_inst_T2_all :
    ∀ φ : Fin 2 ⊕ ((Fin (2 * 2) ⊕ Fin 1) ⊕ Fin 1) → Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 2),
      Function.Surjective φ → (∀ a : Fin 2, φ (Sum.inl a) = Sum.inl a) →
        LGraph.ScostLL (fxyPowGraph 2)
          ((lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
            (Sum.inr (Sum.inr 0)) true).relabel φ) :=
  fun φ hφ hφl => LGraph.ScostLL.of_relabel (fxyPowGraph 2) _ φ hφ hφl
    (LGraph.ScostLL.trans (fxyPowGraph 2)
      (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
      (lwPrimLoop (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true)
        (Sum.inr (Sum.inr 0)) true) localReg6b_inst_moveLoop
      (scostLL_loop _ (Sum.inr (Sum.inr 0)) true))

/-- Instance (7), the §55 transfer: `ScostLL Γ T` carries `k ≤ scost` from the merges of `Γ` to those of `T`, for `far` and
`all` alike (no hypothesis restricting to far merges). -/
theorem localReg6b_inst_transfer :
    ∀ {I I' : Type} [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I'] (Γ : LGraph (Fin 2) I)
      (T : LGraph (Fin 2) I') (far : Bool) (k : ℤ), LGraph.ScostLL Γ T →
      (∀ s₀ : Setoid (Fin 2 ⊕ I), (far = true → ¬ s₀ (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost Γ s₀) →
        ∀ s : Setoid (Fin 2 ⊕ I'), (far = true → ¬ s (Sum.inl 0) (Sum.inl 1)) → k ≤ LGraph.scost T s := by
  intro I I' _ _ _ _ Γ T far k hLL hk s hs
  obtain ⟨s₀, hsep, hcost⟩ := hLL s
  exact (hk s₀ (fun hf => hsep 0 1 (hs hf))).trans hcost

/-- Instance (8a), the placement lemma for `MoveSC(z; u, v)` (`{u → α, α → v}`), every `Γ`, `rest`, `z`, `u`, `v`: whenever the
two added edges are not both inside a class of `s` (`k ≤ 1`), splitting `α` off costs no more. -/
theorem localReg6b_inst_moveSC_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I)
    (s : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hk : ¬ (s (owxEmb 1 u) (Sum.inr (Sum.inr 0)) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) :
    (lwPrimMoveSC Γ rest z u v).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤
      (lwPrimMoveSC Γ rest z u v).scost s :=
  scostLL_placement (lwPrimMoveSC Γ rest z u v) rest
    [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    (List.Perm.refl _)
    (Or.inr ⟨_, _, rfl, rfl, Or.inr ⟨rfl, scostLL_emb_ne_alpha u⟩, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha v⟩⟩) s
    (localReg6b_hk_two _ _ (fun a b => ¬ (s a.src a.dst ∧ s b.src b.dst)) hk)

/-- Instance (8b), the placement lemma for `MoveOut(z; v, d)` (`{α → v, α → d}`). -/
theorem localReg6b_inst_moveOut_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v d : E ⊕ I)
    (s : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hk : ¬ (s (Sum.inr (Sum.inr 0)) (owxEmb 1 v) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 d))) :
    (lwPrimMoveOut Γ rest z v d).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤
      (lwPrimMoveOut Γ rest z v d).scost s :=
  scostLL_placement (lwPrimMoveOut Γ rest z v d) rest
    [⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩, ⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 d⟩]
    (List.Perm.refl _)
    (Or.inr ⟨_, _, rfl, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha v⟩, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha d⟩⟩) s
    (localReg6b_hk_two _ _ (fun a b => ¬ (s a.src a.dst ∧ s b.src b.dst)) hk)

/-- Instance (8c), the placement lemma for `Dmove(z; p, q)` with a blue `q = a → b`: the `α`-edges are `{a → α, α → v}`, the
third added edge `z → b` avoids `α` and goes into `L`; every `Γ`, `rest`, `z`, `v`, `q`. -/
theorem localReg6b_inst_dmoveBlue_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I)
    (q : SEdge (E ⊕ I)) (hq : q.σ = true) (s : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hk : ¬ (s (owxEmb 1 q.src) (Sum.inr (Sum.inr 0)) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) :
    (lwPrimDmove Γ rest z v q).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤
      (lwPrimDmove Γ rest z v q).scost s := by
  obtain ⟨σ, c, a, b⟩ := q
  simp only at hq
  subst hq
  refine scostLL_placement (lwPrimDmove Γ rest z v ⟨true, c, a, b⟩) (rest ++ [⟨true, false, z, b⟩])
    [⟨true, false, owxEmb 1 a, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] ?_
    (Or.inr ⟨_, _, rfl, rfl, Or.inr ⟨rfl, scostLL_emb_ne_alpha a⟩, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha v⟩⟩) s
    (localReg6b_hk_two _ _ (fun a b => ¬ (s a.src a.dst ∧ s b.src b.dst)) hk)
  show (rest.map (SEdge.map (owxEmb 1)) ++ _).Perm _
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  exact List.Perm.append_left _ (List.Perm.swap _ _ _)

/-- Instance (8c), the placement lemma for `Dmove(z; p, q)` with a red `q = a → b`: the `α`-edges are `{α → b, α → v}`, the
third added edge `a → z` avoids `α` and goes into `L`. -/
theorem localReg6b_inst_dmoveRed_placement (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z v : E ⊕ I)
    (q : SEdge (E ⊕ I)) (hq : q.σ = false) (s : Setoid (E ⊕ (I ⊕ Fin 1)))
    (hk : ¬ (s (Sum.inr (Sum.inr 0)) (owxEmb 1 q.dst) ∧ s (Sum.inr (Sum.inr 0)) (owxEmb 1 v))) :
    (lwPrimDmove Γ rest z v q).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤
      (lwPrimDmove Γ rest z v q).scost s := by
  obtain ⟨σ, c, a, b⟩ := q
  simp only at hq
  subst hq
  refine scostLL_placement (lwPrimDmove Γ rest z v ⟨false, c, a, b⟩) (rest ++ [⟨false, false, a, z⟩])
    [⟨false, false, Sum.inr (Sum.inr 0), owxEmb 1 b⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] ?_
    (Or.inr ⟨_, _, rfl, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha b⟩, rfl, Or.inl ⟨rfl, scostLL_emb_ne_alpha v⟩⟩) s
    (localReg6b_hk_two _ _ (fun a b => ¬ (s a.src a.dst ∧ s b.src b.dst)) hk)
  show (rest.map (SEdge.map (owxEmb 1)) ++ _).Perm _
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  exact List.Perm.refl _

open Classical in
/-- Instance (8d), `scostLL_repair` applied to `MoveSC(z; u, v)` at `k = 2` (`α` in the class of `u` and `v`, `[u] = [v] ≠ [z]`):
after the reduction of the surgery identity (`T.scost s' = Γ_L.scost s₀ + 2`, `scostLL_fresh_dropped`) the local lemma holds
with `s₀` the restriction or its merge. -/
theorem localReg6b_inst_moveSC_k2 (Γ : LGraph E I) (rest : List (SEdge (E ⊕ I))) (z u v : E ⊕ I)
    (hperm : Γ.solid.Perm (⟨true, false, z, v⟩ :: ⟨true, false, u, z⟩ :: rest))
    (s' : Setoid (E ⊕ (I ⊕ Fin 1))) (hu : s' (owxEmb 1 u) (Sum.inr (Sum.inr 0)))
    (hv : s' (Sum.inr (Sum.inr 0)) (owxEmb 1 v)) (huz : ¬ s' (owxEmb 1 u) (owxEmb 1 z)) :
    ∃ s₀ : Setoid (E ⊕ I), (∀ a b : E, ¬ s' (Sum.inl a) (Sum.inl b) → ¬ s₀ (Sum.inl a) (Sum.inl b)) ∧
      Γ.scost s₀ ≤ (lwPrimMoveSC Γ rest z u v).scost s' := by
  have hna : ¬ ∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0) :=
    fun h => scostLL_emb_ne_alpha u (h _ hu)
  have hkA : scostLL_kept [(⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩ : SEdge (E ⊕ (I ⊕ Fin 1))),
      ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩] s' = [] := by simp [scostLL_kept, hu, hv]
  have hT := scostLL_fresh_dropped ({ Γ with solid := rest } : LGraph E I) 1
    [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
    [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] s' hkA hna
  have huv : Setoid.comap (owxEmb 1) s' u v := s'.trans hu hv
  obtain ⟨s₁, -, hsep, hcost⟩ := scostLL_repair Γ rest true z v u z u (Setoid.comap (owxEmb 1) s') hperm huv
    ((Setoid.comap (owxEmb 1) s').refl' u) ((Setoid.comap (owxEmb 1) s').refl' z) huz
  refine ⟨s₁, fun a b h => hsep a b (fun hc => h hc), ?_⟩
  have e : lwPrimMoveSC Γ rest z u v = ({ Γ with solid := rest } : LGraph E I).owxExt (owxEmb 1) 1
      [⟨true, false, owxEmb 1 u, Sum.inr (Sum.inr 0)⟩, ⟨true, false, Sum.inr (Sum.inr 0), owxEmb 1 v⟩]
      [⟨false, true, owxEmb 1 z, Sum.inr (Sum.inr 0)⟩] := rfl
  rw [e, hT]
  simp only [List.length_singleton, Nat.cast_one] at *
  linarith

/-- the placement lemma for the loop shape of `Loop(z)`, at an arbitrary graph -/
theorem localReg6b_inst_loop_placement (Γ : LGraph E I) (z : E ⊕ I) (col : Bool) (s : Setoid (E ⊕ (I ⊕ Fin 1))) :
    (lwPrimLoop Γ z col).scost (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤ (lwPrimLoop Γ z col).scost s :=
  scostLL_placement (lwPrimLoop Γ z col) Γ.solid _ (List.Perm.refl _) (Or.inl ⟨col, rfl⟩) s
    (fun _ _ h => by simp at h)

/-- the placement lemma for the loop shape of `MoveLoop(z)` at `Γ_2` -/
theorem localReg6b_inst_moveLoop_placement (s : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) :
    (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost
        (scostLL_split (Sum.inr (Sum.inr 0)) s) ≤
      (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s :=
  scostLL_placement _ (fxyPowGraph 2).solid.tail _ (List.Perm.refl _) (Or.inl ⟨true, rfl⟩) s
    (fun _ _ h => by simp at h)

/-- Instances of the pattern facts: `(1,1,0,0) + (1,1,0,0)` is not elementary, `0 + (1,1,0,0)` and `0 + (0,0,1,1)` are (E1,
E5); a pair removed from a residual (E0: the value `-1` is attained; E3); two colours, two ins, two outs (E4); an added pair of
two colours, two ins, two outs (E6); an elementary pattern is not `0`. -/
theorem localReg6b_inst_patterns :
    scostLL_el (((1, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = 0 ∧
    scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = 1 ∧
    scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (0, 0, 1, 1)) = 1 ∧
    (scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + 0) - scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = -1 ∧
      lwElem ((0 : ℕ × ℕ × ℕ × ℕ) + (1, 1, 0, 0)) = true) ∧
    scostLL_el (((1, 0, 2, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) -
      scostLL_el (((1, 0, 2, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) = 0 ∧
    lwElem ((1, 0, 1, 0) : ℕ × ℕ × ℕ × ℕ) = false ∧ lwElem ((0, 1, 0, 1) : ℕ × ℕ × ℕ × ℕ) = false ∧
    lwElem ((1, 0, 1, 0) : ℕ × ℕ × ℕ × ℕ) = false ∧
    lwElem (((1, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 1, 0)) = false ∧
    lwElem (((0, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (0, 1, 0, 1)) = false ∧
    lwElem (((0, 0, 0, 0) : ℕ × ℕ × ℕ × ℕ) + (1, 0, 1, 0)) = false ∧
    ((1, 1, 0, 0) : ℕ × ℕ × ℕ × ℕ) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, scostLL_elem_E3 _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [scostLL_elem_E1]
    decide
  · rw [scostLL_elem_E1]
    decide
  · rw [scostLL_elem_E5]
    decide
  · refine ⟨?_, ?_⟩
    · have h1 : scostLL_el ((0 : ℕ × ℕ × ℕ × ℕ) + 0) = 0 := by rw [add_zero]; exact scostLL_el_zero
      rw [h1, zero_add, scostLL_el_eq_one (by decide)]
      norm_num
    · decide
  · exact scostLL_elem_E4col _ (by decide) (by decide)
  · exact scostLL_elem_E4out _ (by decide)
  · exact scostLL_elem_E4in _ (by decide)
  · exact scostLL_elem_E6col _ _ (by decide) (by decide)
  · exact scostLL_elem_E6out _ _ (by decide)
  · exact scostLL_elem_E6in _ _ (by decide)
  · exact scostLL_elem_ne_zero (by decide)

/-- Instance of `scostLL_refl` at `Γ_2`. -/
theorem localReg6b_inst_refl : LGraph.ScostLL (fxyPowGraph 2) (fxyPowGraph 2) := scostLL_refl _

open Classical in
/-- Instance of the class-sum form at `Γ_2`, every merge. -/
theorem localReg6b_inst_scost_eq (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) :
    (fxyPowGraph 2).scost s = ((scostLL_kept (fxyPowGraph 2).solid s).length : ℤ) +
      2 * ((fxyPowGraph 2).waved.length : ℤ) +
      ∑ c ∈ (fxyPowGraph 2).sIntCls s, (scostLL_el (scostLL_clsPat (fxyPowGraph 2).solid s c) - 2) :=
  scostLL_scost_eq (fxyPowGraph 2) s

open Classical in
/-- Instances of the fresh vertex bookkeeping (b) at the vertex types of `Γ_2` plus `α`: the image of `qmap` and the internal
classes. -/
theorem localReg6b_inst_fresh_classes (s' : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) :
    (∀ c' : Quotient s', (∃ c₀, localReg6a_qmap (owxEmb 1) s' c₀ = c') ↔
      ¬ ((∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) ∧
        c' = Quotient.mk s' (Sum.inr (Sum.inr 0)))) ∧
    (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).sIntCls s' =
      ((fxyPowGraph 2).sIntCls (Setoid.comap (owxEmb 1) s')).image (localReg6a_qmap (owxEmb 1) s') ∪
        (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then
          {Quotient.mk s' (Sum.inr (Sum.inr 0))} else ∅) :=
  ⟨scostLL_qmap_range s', scostLL_intCls_emb (fxyPowGraph 2) (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true) s'⟩

/-- the merge of `Γ_2` with `α ~ x` and every other vertex alone: `α`, `x` get the value `0`, `y` the value `1`, `α_i`, `β_i`
the values `i + 2` -/
def localReg6b_instS : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)) :=
  Setoid.ker (fun w : Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1) => match w with
    | Sum.inl a => a.val
    | Sum.inr (Sum.inl j) => j.val + 2
    | Sum.inr (Sum.inr _) => 0)

/-- Instance (8a) at concrete data: `MoveSC(α_0; x, y)` at `Γ_2` with the merge `α ~ x` (`k = 1`, an SC pair): splitting `α` off
costs no more. -/
theorem localReg6b_inst_moveSC_Gamma2 :
    (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0)
        (Sum.inl 1)).scost (scostLL_split (Sum.inr (Sum.inr 0)) localReg6b_instS) ≤
      (lwPrimMoveSC (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0)
        (Sum.inl 1)).scost localReg6b_instS :=
  localReg6b_inst_moveSC_placement (fxyPowGraph 2) _ (Sum.inr 0) (Sum.inl 0) (Sum.inl 1) localReg6b_instS
    (by
      rintro ⟨-, h⟩
      have h' : (0 : ℕ) = 1 := h
      omega)

open Classical in
/-- Instance of the surgery identity at `Γ_2` (the term `Loop(x)`), every merge. -/
theorem localReg6b_inst_surgery (s' : Setoid (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1))) :
    (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s' =
      ((scostLL_kept (fxyPowGraph 2).solid (Setoid.comap (owxEmb 1) s')).length : ℤ) +
        ((scostLL_kept [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ :
          SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s').length : ℤ) +
        2 * (((fxyPowGraph 2).waved.length : ℤ) + 1) +
        ∑ c₀ ∈ (fxyPowGraph 2).sIntCls (Setoid.comap (owxEmb 1) s'),
          (scostLL_el (scostLL_clsPat (fxyPowGraph 2).solid (Setoid.comap (owxEmb 1) s') c₀ +
            scostLL_clsPat [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ :
              SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s' (localReg6a_qmap (owxEmb 1) s' c₀)) - 2) +
        (if (∀ w, s' w (Sum.inr (Sum.inr 0)) → w = Sum.inr (Sum.inr 0)) then
          scostLL_el (scostLL_clsPat [(⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩ :
            SEdge (Fin 2 ⊕ (Fin (2 * 2) ⊕ Fin 1)))] s' (Quotient.mk s' (Sum.inr (Sum.inr 0)))) - 2 else 0) := by
  have h := scostLL_fresh_scost (fxyPowGraph 2) 1
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩] [⟨false, true, owxEmb 1 (Sum.inl 0), Sum.inr (Sum.inr 0)⟩] s'
  simp only [List.length_singleton, Nat.cast_one] at h
  exact h

open Classical in
/-- Instance of the localisation at `Γ_2`: `AddLoop` at `β_0`, blue (`R = []`, `A = [loop at β_0]`, `X = Γ_2.solid`, `C` the
class of `β_0`), every merge. -/
theorem localReg6b_inst_localise (s : Setoid (Fin 2 ⊕ Fin (2 * 2))) :
    (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s - (fxyPowGraph 2).scost s =
      ((scostLL_kept [(⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2)))] s).length : ℤ) -
        ((scostLL_kept ([] : List (SEdge (Fin 2 ⊕ Fin (2 * 2)))) s).length : ℤ) +
        2 * (((lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).waved.length : ℤ) - (fxyPowGraph 2).waved.length) +
        ∑ c ∈ ({Quotient.mk s (Sum.inr 1)} : Finset (Quotient s)),
          (if c ∈ (fxyPowGraph 2).sIntCls s then
            scostLL_el (scostLL_clsPat [(⟨true, true, Sum.inr 1, Sum.inr 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2)))] s c +
              scostLL_clsPat (fxyPowGraph 2).solid s c) -
            scostLL_el (scostLL_clsPat ([] : List (SEdge (Fin 2 ⊕ Fin (2 * 2)))) s c +
              scostLL_clsPat (fxyPowGraph 2).solid s c) else 0) :=
  scostLL_local_diff_C (fxyPowGraph 2) (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true) [] [⟨true, true, Sum.inr 1, Sum.inr 1⟩]
    (fxyPowGraph 2).solid s (List.Perm.refl _) (List.Perm.refl _) {Quotient.mk s (Sum.inr 1)}
    (fun e he => absurd he (List.not_mem_nil))
    (fun e he => by
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩)

/-- the hypothesis of the `Contract(α_0; x, y)` instance at `Γ_2`: the edges `α_0 → y` and `x → α_0` of the blue block (a
permutation of the solid list, not an equality) -/
theorem localReg6b_inst_contractPerm : (fxyPowGraph 2).solid.Perm
    ((⟨true, false, Sum.inr 0, Sum.inl 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))) :: ⟨true, false, Sum.inl 0, Sum.inr 0⟩ ::
      [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩]) :=
  (List.perm_middle (a := (⟨true, false, Sum.inr 0, Sum.inl 1⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))))
    (l₁ := [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩])
    (l₂ := [⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
      ⟨false, false, Sum.inr 2, Sum.inl 1⟩])).trans
    (List.Perm.cons _ (List.perm_middle (a := (⟨true, false, Sum.inl 0, Sum.inr 0⟩ : SEdge (Fin 2 ⊕ Fin (2 * 2))))
      (l₁ := [⟨true, true, Sum.inr 1, Sum.inr 1⟩])
      (l₂ := [⟨false, true, Sum.inr 3, Sum.inr 3⟩, ⟨false, false, Sum.inl 0, Sum.inr 2⟩,
        ⟨false, false, Sum.inr 2, Sum.inl 1⟩])))

/-- Instance (4), `scostLL_contract` at `Γ_2`: `Contract(α_0; x, y)`, the `GG` term `R2` in the starting graph. -/
theorem localReg6b_inst_contractGamma2 : LGraph.ScostLL (fxyPowGraph 2)
    (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
      ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0) (Sum.inl 1)) :=
  scostLL_contract _ _ _ _ _ (by decide) (by decide) localReg6b_inst_contractPerm

/-- the §55 check at `Γ_2` (`p = 2`): a local lemma `ScostLL Γ_2 T` transfers `Φ^all(Γ_2) ≥ 2p = 4` and `Φ^far(Γ_2) ≥ 3p = 6`
to every merge of `T`, with no `far`/`all` switch in `ScostLL` itself -/
theorem localReg6b_inst_s55 {I' : Type} [Fintype I'] [DecidableEq I'] (T : LGraph (Fin 2) I')
    (hT : LGraph.ScostLL (fxyPowGraph 2) T) :
    (∀ s : Setoid (Fin 2 ⊕ I'), 4 ≤ T.scost s) ∧ (∀ s : Setoid (Fin 2 ⊕ I'), ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ T.scost s) :=
  ⟨fun s => localReg6b_inst_transfer (fxyPowGraph 2) T false 4 hT
      (fun s₀ _ => localReg6a_inst_cost2.1 s₀ (fun h => absurd h (by decide))) s (fun h => absurd h (by decide)),
   fun s hs => localReg6b_inst_transfer (fxyPowGraph 2) T true 6 hT
      (fun s₀ h => localReg6a_inst_cost2.2 s₀ h) s (fun _ => hs)⟩

/-- the §55 values for the four primitives at `Γ_2`: `Loop(x)`, `AddLoop(β_0)`, `MoveLoop(β_0)`, `Contract(α_0; x, y)` keep
`4 ≤ scost` for every merge and `6 ≤ scost` for every merge separating `x` and `y` -/
theorem localReg6b_inst_s55_prims :
    ((∀ s, 4 ≤ (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s) ∧
      (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimLoop (fxyPowGraph 2) (Sum.inl 0) true).scost s)) ∧
    ((∀ s, 4 ≤ (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s) ∧
      (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) → 6 ≤ (lwPrimAddLoop (fxyPowGraph 2) (Sum.inr 1) true).scost s)) ∧
    ((∀ s, 4 ≤ (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s) ∧
      (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) →
        6 ≤ (lwPrimMoveLoop (fxyPowGraph 2) (fxyPowGraph 2).solid.tail (Sum.inr 1) true).scost s)) ∧
    ((∀ s, 4 ≤ (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
        ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0)
        (Sum.inl 1)).scost s) ∧
      (∀ s, ¬ s (Sum.inl 0) (Sum.inl 1) →
        6 ≤ (lwPrimContract (fxyPowGraph 2) [⟨true, true, Sum.inr 1, Sum.inr 1⟩, ⟨false, true, Sum.inr 3, Sum.inr 3⟩,
          ⟨false, false, Sum.inl 0, Sum.inr 2⟩, ⟨false, false, Sum.inr 2, Sum.inl 1⟩] (Sum.inr 0) (Sum.inl 0)
          (Sum.inl 1)).scost s)) :=
  ⟨localReg6b_inst_s55 _ localReg6b_inst_loop, localReg6b_inst_s55 _ localReg6b_inst_addLoop,
    localReg6b_inst_s55 _ localReg6b_inst_moveLoop, localReg6b_inst_s55 _ localReg6b_inst_contractGamma2⟩

end Instances

end RBM.Graph

end
