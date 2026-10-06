/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AnpKey6
import RBM3D.Evolution.Pins
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# LW-13a: the deterministic near bound of `lem:LW_moment_exp` (T2281)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:LW_moment_exp`
`:78-83`, the near bound `(adsuu_exp2)` `:1655`, `𝐃_{≤ℓ}` `:1650`, `claim:TTk` `(eq:key_T_reudce)`,
the path-preserving step `:1770-1775`, the end `:1781-1786`.  Scope (amendment 1 of T2281): the near
part only; the far bound `(adsuu33)` is not here.

Route.  `ξ ≤ τ := 𝖳_t(|·-·|_1 ∧ ℓ)`, so the value is at most the value for `τ`.  The edges not on
a path are bounded by `τ ≤ 𝖳_t(0) ≤ Ψ_t`; the paths (edge-disjoint walks `a_i → b_i`) become vertex
sequences, and the value of the sequences is bounded by induction on the number of internal
vertices: the first internal vertex `α` is summed with the merged `ekTTk_holds` (`claim:TTk`) and
deleted from every sequence (the path-preserving step; a passage `x → α → y` becomes the edge
`x y`; a passage with `x = y` or a step `α α` is an edge of weight `𝖳_t(0) ≤ Ψ_t`, kept, so the
power of `Ψ_t` is `A - 2` with `A` the number of occurrences of `α`).  At `q = 0` every vertex has
the label `a` or `b`.

* Section 1: the chain product along a vertex sequence; the marked-sequence lemma.
* Section 2: path systems, the base case, the first variable of a sum.
* Section 3: the one-vertex step.
* Section 4: the induction over the internal vertices.
* Section 5: the kernel `𝖳_t(|·-·|_1 ∧ ℓ)`, the constants of `claim:TTk`, `lwMomExp_near_step'`.
* Section 6: nested graphs as path systems.
* Section 7: the pin `AnpDetNear`, `lwMomExp_near`.
* Section 8: compiled nonempty instances at `d = 3`.

No port: RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. The chain product and the marked sequences -/

/-- The product of `w` along the vertex sequence `x, m₁, …, mₙ, y` (the `n + 1` steps of a path). -/
def lwMomExp_chain {ι : Type*} (w : ι → ι → ℝ) : ι → List ι → ι → ℝ
  | x, [], y => w x y
  | x, z :: m, y => w x z * lwMomExp_chain w z m y

section Marks

variable {ι : Type*} (w : ι → ι → ℝ)

private theorem lwMomExp_fm_some {ι : Type*} (z : ι) (l : List (Option ι)) :
    (some z :: l).filterMap id = z :: l.filterMap id := rfl

private theorem lwMomExp_fm_none {ι : Type*} (l : List (Option ι)) :
    (none :: l).filterMap id = l.filterMap id := rfl

/-- A marked sequence `m` (an entry `none` is the summed vertex `α`, labelled `c`): the chain product
along `x, m, y` is `R · Π_{passages} w(x_j, c) w(c, y_j) · w(c,c)^r`, and the chain product along the
sequence with the `none` entries deleted is `R · Π_{passages} w(x_j, y_j)`; `P.length + r` is the
number of `none` entries, and a sequence containing one has a passage. -/
private theorem lwMomExp_marks (T0 : ℝ) (hww : ∀ c, w c c = T0) (hw0 : ∀ u v, 0 ≤ w u v) (y : ι) :
    ∀ (n : ℕ) (m : List (Option ι)) (x : ι), m.length ≤ n →
      ∃ (R : ℝ) (P : List (ι × ι)) (r : ℕ), 0 ≤ R ∧
        (∀ c, lwMomExp_chain w x (m.map fun o => o.getD c) y =
          R * (P.map fun xy => w xy.1 c * w c xy.2).prod * T0 ^ r) ∧
        lwMomExp_chain w x (m.filterMap id) y = R * (P.map fun xy => w xy.1 xy.2).prod ∧
        P.length + r = (m.filter fun o => o.isNone).length ∧ (none ∈ m → 0 < P.length) := by
  intro n
  induction n with
  | zero =>
    intro m x hm
    have : m = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hm)
    subst this
    exact ⟨w x y, [], 0, hw0 _ _, fun c => by simp [lwMomExp_chain], by simp [lwMomExp_chain],
      by simp, by simp⟩
  | succ n ih =>
    intro m x hm
    cases m with
    | nil =>
      exact ⟨w x y, [], 0, hw0 _ _, fun c => by simp [lwMomExp_chain], by simp [lwMomExp_chain],
        by simp, by simp⟩
    | cons o m' =>
      cases o with
      | some z =>
        obtain ⟨R, P, r, hR, h1, h2, h3, h4⟩ := ih m' z (by simpa using hm)
        refine ⟨w x z * R, P, r, mul_nonneg (hw0 _ _) hR, fun c => ?_, ?_, by simpa using h3, ?_⟩
        · simp only [List.map_cons, Option.getD_some, lwMomExp_chain, h1 c]; ring
        · rw [lwMomExp_fm_some]; simp only [lwMomExp_chain, h2]; ring
        · intro h
          have : none ∈ m' := by simpa using h
          exact h4 this
      | none =>
        cases m' with
        | nil =>
          refine ⟨1, [(x, y)], 0, zero_le_one, fun c => ?_, ?_, by simp, fun _ => by simp⟩
          · simp [lwMomExp_chain]
          · simp [lwMomExp_chain]
        | cons o' m'' =>
          cases o' with
          | none =>
            obtain ⟨R, P, r, hR, h1, h2, h3, h4⟩ := ih (none :: m'') x (by simpa using hm)
            refine ⟨R, P, r + 1, hR, fun c => ?_, ?_, ?_, fun _ => h4 (by simp)⟩
            · have := h1 c
              simp only [List.map_cons, Option.getD_none, lwMomExp_chain, hww] at this ⊢
              rw [pow_succ]
              calc _ = T0 * (w x c * lwMomExp_chain w c (List.map (fun o => o.getD c) m'') y) := by ring
                _ = _ := by rw [this]; ring
            · rw [lwMomExp_fm_none]; rw [lwMomExp_fm_none] at h2; exact h2
            · simp only [List.filter_cons, Option.isNone_none, ite_true, List.length_cons] at h3 ⊢
              omega
          | some z =>
            obtain ⟨R, P, r, hR, h1, h2, h3, h4⟩ := ih m'' z (by simp at hm; omega)
            refine ⟨R, (x, z) :: P, r, hR, fun c => ?_, ?_, ?_, fun _ => by simp⟩
            · simp only [List.map_cons, Option.getD_none, Option.getD_some, lwMomExp_chain, h1 c,
                List.prod_cons]
              ring
            · rw [lwMomExp_fm_none, lwMomExp_fm_some]
              simp only [lwMomExp_chain, h2, List.map_cons, List.prod_cons]
              ring
            · simp only [List.filter_cons, Option.isNone_none, Option.isNone_some, ite_true,
                Bool.false_eq_true, ite_false, List.length_cons, List.length_cons] at h3 ⊢
              omega

end Marks

/-! ## 2. The labelled path systems, the base case, the first variable -/

/-- The labelling of the vertices of a nested graph with the external labels `a_i ≡ a`, `b_i ≡ b`. -/
def lwMomExp_lab {ι : Type*} {p q : ℕ} (a b : ι) (ℓ : Fin q → ι) : NV p q → ι :=
  Sum.elim (Sum.elim (fun _ => a) (fun _ => b)) ℓ

/-- The value of a path system: the paths are the vertex sequences `m i` (between `a_i` and `b_i`), the
internal labels are summed over `D`; a path contributes the chain product of `w` of its labels. -/
def lwMomExp_sysVal {ι : Type*} (w : ι → ι → ℝ) (D : Finset ι) (a b : ι) {p q : ℕ}
    (m : Fin p → List (NV p q)) : ℝ :=
  ∑ ℓ ∈ Fintype.piFinset (fun _ : Fin q => D),
    ∏ i, lwMomExp_chain w a ((m i).map (lwMomExp_lab a b ℓ)) b

private theorem lwMomExp_chain_nonneg {ι : Type*} (w : ι → ι → ℝ) (hw0 : ∀ u v, 0 ≤ w u v) :
    ∀ (m : List ι) (x y : ι), 0 ≤ lwMomExp_chain w x m y := by
  intro m
  induction m with
  | nil => intro x y; exact hw0 _ _
  | cons z m ih => intro x y; exact mul_nonneg (hw0 _ _) (ih _ _)

/-- The base case: a path between the labels `a` and `b` all of whose vertices carry the labels `a`,
`b` has a step `a b` (`w a b`), all the others are at most `T0`. -/
private theorem lwMomExp_base {ι : Type*} (w : ι → ι → ℝ) (a b : ι) (T0 : ℝ)
    (hw0 : ∀ u v, 0 ≤ w u v) (hsym : ∀ u v, w u v = w v u) (hle : ∀ u v, w u v ≤ T0)
    (hww : ∀ c, w c c = T0) :
    ∀ (m : List ι) (x : ι), (∀ z ∈ m, z = a ∨ z = b) → (x = a ∨ x = b) →
      (x = a → lwMomExp_chain w x m b ≤ w a b * T0 ^ m.length) ∧
      (x = b → lwMomExp_chain w x m b ≤ T0 ^ (m.length + 1)) := by
  have hT0 : 0 ≤ T0 := (hw0 a a).trans (hle a a)
  have hab : w a b ≤ T0 := hle a b
  have hab0 : 0 ≤ w a b := hw0 a b
  intro m
  induction m with
  | nil =>
    intro x _ hx
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]; simp [lwMomExp_chain]
    · rw [h]; simp [lwMomExp_chain, hww]
  | cons z m ih =>
    intro x hm hx
    have hz : z = a ∨ z = b := hm z (by simp)
    have hm' : ∀ z' ∈ m, z' = a ∨ z' = b := fun z' h => hm z' (List.mem_cons_of_mem _ h)
    have ih' := ih z hm' hz
    have hpow : 0 ≤ T0 ^ m.length := pow_nonneg hT0 _
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h]
      rcases hz with hz | hz
      · have h1 := ih'.1 hz
        rw [hz] at h1 ⊢
        simp only [lwMomExp_chain, hww, List.length_cons, pow_succ]
        calc T0 * lwMomExp_chain w a m b ≤ T0 * (w a b * T0 ^ m.length) :=
              mul_le_mul_of_nonneg_left h1 hT0
          _ = _ := by ring
      · have h1 := ih'.2 hz
        rw [hz] at h1 ⊢
        simp only [lwMomExp_chain, List.length_cons]
        calc w a b * lwMomExp_chain w b m b ≤ w a b * T0 ^ (m.length + 1) :=
              mul_le_mul_of_nonneg_left h1 hab0
          _ = _ := by ring
    · rw [h]
      rcases hz with hz | hz
      · have h1 := ih'.1 hz
        rw [hz] at h1 ⊢
        simp only [lwMomExp_chain, List.length_cons]
        rw [hsym b a]
        calc w a b * lwMomExp_chain w a m b ≤ w a b * (w a b * T0 ^ m.length) :=
              mul_le_mul_of_nonneg_left h1 hab0
          _ ≤ T0 * (T0 * T0 ^ m.length) := by
              apply mul_le_mul hab _ (by positivity) hT0
              exact mul_le_mul hab le_rfl hpow hT0
          _ = _ := by ring
      · have h1 := ih'.2 hz
        rw [hz] at h1 ⊢
        simp only [lwMomExp_chain, hww, List.length_cons]
        calc T0 * lwMomExp_chain w b m b ≤ T0 * T0 ^ (m.length + 1) :=
              mul_le_mul_of_nonneg_left h1 hT0
          _ = _ := by ring

/-- Splitting off the first variable of a sum over `Fin (q + 1) → ι`. -/
private theorem lwMomExp_sum_succ {ι : Type*} (D : Finset ι) {q : ℕ} (F : (Fin (q + 1) → ι) → ℝ) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin (q + 1) => D), F f =
      ∑ ℓ' ∈ Fintype.piFinset (fun _ : Fin q => D), ∑ c ∈ D, F (Fin.cons c ℓ') := by
  rw [Finset.sum_comm, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun f => (f 0, Fin.tail f)) (fun x => Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Fintype.mem_piFinset, Finset.mem_product, Fin.forall_fin_succ] at hf ⊢
    exact ⟨hf.1, fun i => hf.2 i⟩
  · intro x hx
    simp only [Fintype.mem_piFinset, Finset.mem_product, Fin.forall_fin_succ] at hx ⊢
    exact ⟨by simpa using hx.1, fun i => by simpa using hx.2 i⟩
  · intro f _; simp
  · intro x _; simp
  · intro f _; simp

/-! ## 3. The one-vertex step -/

/-- Deleting the first internal vertex `α = inr 0` and renumbering the others. -/
def lwMomExp_phi {p q : ℕ} : NV p (q + 1) → Option (NV p q) :=
  Sum.elim (fun e => some (Sum.inl e)) (fun j => Fin.cases none (fun j' => some (Sum.inr j')) j)

/-- The path system with the vertex `α` deleted from every path (the path-preserving step: a passage
`x → α → y` becomes the step `x y`). -/
def lwMomExp_del {p q : ℕ} (m : Fin p → List (NV p (q + 1))) : Fin p → List (NV p q) :=
  fun i => (m i).filterMap lwMomExp_phi

/-- The number of occurrences of `α = inr 0` on the paths. -/
def lwMomExp_occ {p q : ℕ} (m : Fin p → List (NV p (q + 1))) : ℕ :=
  ∑ i, (m i).countP fun v => decide (v = Sum.inr 0)

private theorem lwMomExp_phi_none {p q : ℕ} (v : NV p (q + 1)) :
    lwMomExp_phi v = none ↔ v = Sum.inr 0 := by
  rcases v with e | j
  · simp [lwMomExp_phi]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [lwMomExp_phi]
    · simp [lwMomExp_phi]

private theorem lwMomExp_phi_succ {p q : ℕ} (v : NV p (q + 1)) (j : Fin q) :
    lwMomExp_phi v = some (Sum.inr j) ↔ v = Sum.inr j.succ := by
  rcases v with e | j'
  · simp [lwMomExp_phi]
  · refine Fin.cases ?_ (fun j'' => ?_) j'
    · simp [lwMomExp_phi, (Fin.succ_ne_zero j).symm]
    · simp [lwMomExp_phi, Fin.succ_inj]

/-- The marked labels of the vertices: `none` for `α`, the label otherwise. -/
private def lwMomExp_psi {ι : Type*} {p q : ℕ} (a b : ι) (ℓ' : Fin q → ι) (v : NV p (q + 1)) :
    Option ι := (lwMomExp_phi v).map (lwMomExp_lab a b ℓ')

private theorem lwMomExp_lab_cons {ι : Type*} {p q : ℕ} (a b : ι) (c : ι) (ℓ' : Fin q → ι)
    (v : NV p (q + 1)) :
    lwMomExp_lab a b (Fin.cons c ℓ' : Fin (q + 1) → ι) v = (lwMomExp_psi a b ℓ' v).getD c := by
  rcases v with e | j
  · simp [lwMomExp_lab, lwMomExp_psi, lwMomExp_phi]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [lwMomExp_lab, lwMomExp_psi, lwMomExp_phi]
    · simp [lwMomExp_lab, lwMomExp_psi, lwMomExp_phi]

private theorem lwMomExp_prod_flatten {X : Type*} {p : ℕ} (P : Fin p → List X) (g : X → ℝ) :
    (((List.ofFn P).flatten).map g).prod = ∏ i, ((P i).map g).prod := by
  rw [List.map_flatten, List.prod_flatten, List.map_map, ← List.ofFn_comp', List.prod_ofFn]
  rfl

private theorem lwMomExp_prod_fin {X : Type*} (l : List X) (f : X → ℝ) :
    (l.map f).prod = ∏ j : Fin l.length, f (l.get j) := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

private theorem lwMomExp_length_flatten {X : Type*} {p : ℕ} (P : Fin p → List X) :
    ((List.ofFn P).flatten).length = ∑ i, (P i).length := by
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

private theorem lwMomExp_psi_isNone {ι : Type*} {p q : ℕ} (a b : ι) (ℓ' : Fin q → ι)
    (v : NV p (q + 1)) : (lwMomExp_psi a b ℓ' v).isNone = decide (v = Sum.inr 0) := by
  unfold lwMomExp_psi
  rw [Option.isNone_map]
  by_cases h : v = Sum.inr 0
  · simp [h, (lwMomExp_phi_none (Sum.inr 0)).2 rfl]
  · have : (lwMomExp_phi v).isNone = false := by
      cases hh : lwMomExp_phi v with
      | none => exact absurd ((lwMomExp_phi_none v).1 hh) h
      | some _ => rfl
    simp [h, this]

section Step

variable {ι : Type*}

/-- **The corrected one-vertex step** (aux): summing the first internal vertex `α` of a path system
with `≥ 2` paths through it, with a `claim:TTk`-type bound `hstep` for `k ≤ N` passages. -/
private theorem lwMomExp_step_aux (w : ι → ι → ℝ) (T0 Ψ K Z : ℝ) (N : ℕ) (D : Finset ι) (a b : ι)
    (hw0 : ∀ u v, 0 ≤ w u v) (hww : ∀ c, w c c = T0) (hΨ : T0 ≤ Ψ) (hΨ0 : 0 < Ψ) (hKZ : 0 ≤ K * Z)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → ∀ x y : Fin k → ι,
      ∑ c ∈ D, ∏ i, (w (x i) c * w c (y i)) ≤ K * Z * (Ψ ^ (k - 2) * ∏ i, w (x i) (y i)))
    {p q : ℕ} (m : Fin p → List (NV p (q + 1))) (hn : ∑ i, ((m i).length + 1) ≤ N)
    (hv : ∃ i i', i ≠ i' ∧ Sum.inr 0 ∈ m i ∧ Sum.inr 0 ∈ m i') :
    lwMomExp_sysVal w D a b m ≤
      K * Z * Ψ ^ ((lwMomExp_occ m : ℤ) - 2) * lwMomExp_sysVal w D a b (lwMomExp_del m) := by
  have hT0 : 0 ≤ T0 := (hw0 a a).trans (hww a).le
  unfold lwMomExp_sysVal
  rw [lwMomExp_sum_succ, Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ' _ => ?_
  have hm : ∀ i, ∃ (R : ℝ) (P : List (ι × ι)) (r : ℕ), 0 ≤ R ∧
      (∀ c, lwMomExp_chain w a (((m i).map (lwMomExp_psi a b ℓ')).map fun o => o.getD c) b =
        R * (P.map fun xy => w xy.1 c * w c xy.2).prod * T0 ^ r) ∧
      lwMomExp_chain w a (((m i).map (lwMomExp_psi a b ℓ')).filterMap id) b =
        R * (P.map fun xy => w xy.1 xy.2).prod ∧
      P.length + r = (((m i).map (lwMomExp_psi a b ℓ')).filter fun o => o.isNone).length ∧
      (none ∈ (m i).map (lwMomExp_psi a b ℓ') → 0 < P.length) :=
    fun i => lwMomExp_marks w T0 hww hw0 b _ _ a le_rfl
  choose R P r hR h1 h2 h3 h4 using hm
  have hlab : ∀ c i, (m i).map (lwMomExp_lab a b (Fin.cons c ℓ' : Fin (q + 1) → ι)) =
      ((m i).map (lwMomExp_psi a b ℓ')).map fun o => o.getD c := by
    intro c i
    rw [List.map_map]
    exact List.map_congr_left fun v _ => lwMomExp_lab_cons a b c ℓ' v
  have hfil : ∀ i, ((m i).map (lwMomExp_psi a b ℓ')).filterMap id =
      (lwMomExp_del m i).map (lwMomExp_lab a b ℓ') := by
    intro i
    simp only [lwMomExp_del, List.filterMap_map, List.map_filterMap]
    rfl
  have hcnt : ∀ i, (((m i).map (lwMomExp_psi a b ℓ')).filter fun o => o.isNone).length =
      (m i).countP fun v => decide (v = Sum.inr 0) := by
    intro i
    rw [List.filter_map, List.length_map, List.countP_eq_length_filter]
    congr 1
    refine List.filter_congr fun v _ => ?_
    exact lwMomExp_psi_isNone a b ℓ' v
  set Pf : List (ι × ι) := (List.ofFn P).flatten with hPf
  set s : ℕ := ∑ i, r i with hs
  have hG : ∀ c, ∏ i, lwMomExp_chain w a ((m i).map (lwMomExp_lab a b (Fin.cons c ℓ' : Fin (q + 1) → ι))) b =
      (∏ i, R i) * (∏ j : Fin Pf.length, (w (Pf.get j).1 c * w c (Pf.get j).2)) * T0 ^ s := by
    intro c
    simp only [hlab, fun i => h1 i c]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      ← lwMomExp_prod_flatten P (fun xy => w xy.1 c * w c xy.2), lwMomExp_prod_fin]
  have hF : ∏ i, lwMomExp_chain w a ((lwMomExp_del m i).map (lwMomExp_lab a b ℓ')) b =
      (∏ i, R i) * ∏ j : Fin Pf.length, w (Pf.get j).1 (Pf.get j).2 := by
    simp only [← hfil, h2]
    rw [Finset.prod_mul_distrib, ← lwMomExp_prod_flatten P (fun xy => w xy.1 xy.2), lwMomExp_prod_fin]
  have hk : Pf.length = ∑ i, (P i).length := lwMomExp_length_flatten P
  have hA : lwMomExp_occ m = Pf.length + s := by
    unfold lwMomExp_occ
    rw [hk, hs, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← hcnt i, ← h3 i]
  have hocc_le : lwMomExp_occ m ≤ ∑ i, (m i).length :=
    Finset.sum_le_sum fun i _ => List.countP_le_length
  have hk2 : 2 ≤ Pf.length := by
    obtain ⟨i, i', hne, hi, hi'⟩ := hv
    have hpos : ∀ j, Sum.inr 0 ∈ m j → 0 < (P j).length := fun j hj =>
      h4 j (List.mem_map.2 ⟨Sum.inr 0, hj, by simp [lwMomExp_psi, lwMomExp_phi]⟩)
    have h1' := hpos i hi
    have h2' := hpos i' hi'
    rw [hk]
    calc 2 ≤ (P i).length + (P i').length := by omega
      _ = ∑ j ∈ ({i, i'} : Finset (Fin p)), (P j).length := (Finset.sum_pair (f := fun j => (P j).length) hne).symm
      _ ≤ ∑ j, (P j).length := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hkN : Pf.length ≤ N := by
    have : ∑ i, (m i).length ≤ ∑ i, ((m i).length + 1) := Finset.sum_le_sum fun i _ => Nat.le_succ _
    omega
  have hFnn : 0 ≤ ∏ j : Fin Pf.length, w (Pf.get j).1 (Pf.get j).2 :=
    Finset.prod_nonneg fun j _ => hw0 _ _
  have hRnn : 0 ≤ ∏ i, R i := Finset.prod_nonneg fun i _ => hR i
  have hmain := hstep Pf.length hk2 hkN (fun j => (Pf.get j).1) (fun j => (Pf.get j).2)
  have hexp : Ψ ^ ((lwMomExp_occ m : ℤ) - 2) = Ψ ^ (Pf.length - 2) * Ψ ^ s := by
    have : ((lwMomExp_occ m : ℤ) - 2) = ((Pf.length - 2 + s : ℕ) : ℤ) := by omega
    rw [this, zpow_natCast, pow_add]
  have hTΨ : T0 ^ s ≤ Ψ ^ s := pow_le_pow_left₀ hT0 hΨ s
  rw [hF]
  simp only [hG]
  calc ∑ c ∈ D, (∏ i, R i) * (∏ j : Fin Pf.length, (w (Pf.get j).1 c * w c (Pf.get j).2)) * T0 ^ s
      = ((∏ i, R i) * T0 ^ s) * ∑ c ∈ D, ∏ j : Fin Pf.length, (w (Pf.get j).1 c * w c (Pf.get j).2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ ((∏ i, R i) * T0 ^ s) * (K * Z * (Ψ ^ (Pf.length - 2) *
          ∏ j : Fin Pf.length, w (Pf.get j).1 (Pf.get j).2)) :=
        mul_le_mul_of_nonneg_left hmain (mul_nonneg hRnn (pow_nonneg hT0 _))
    _ = K * Z * Ψ ^ (Pf.length - 2) * (T0 ^ s * ((∏ i, R i) *
          ∏ j : Fin Pf.length, w (Pf.get j).1 (Pf.get j).2)) := by ring
    _ ≤ K * Z * Ψ ^ (Pf.length - 2) * (Ψ ^ s * ((∏ i, R i) *
          ∏ j : Fin Pf.length, w (Pf.get j).1 (Pf.get j).2)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hTΨ (mul_nonneg hRnn hFnn))
          (mul_nonneg hKZ (pow_nonneg hΨ0.le _))
    _ = _ := by rw [hexp]; ring

end Step

/-! ## 4. The induction over the internal vertices -/

section Induction

variable {ι : Type*}

private theorem lwMomExp_del_length {p q : ℕ} (m : Fin p → List (NV p (q + 1))) :
    ∑ i, ((lwMomExp_del m i).length + 1) + lwMomExp_occ m = ∑ i, ((m i).length + 1) := by
  unfold lwMomExp_occ
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (lwMomExp_del m i).length =
      (m i).countP fun v => (lwMomExp_phi v).isSome := by
    unfold lwMomExp_del
    rw [List.length_filterMap_eq_countP]
  have h2 := List.length_eq_countP_add_countP (fun v => decide (v = (Sum.inr 0 : NV p (q + 1)))) (l := m i)
  have h3 : ((m i).countP fun v => (lwMomExp_phi v).isSome) =
      (m i).countP fun v => decide ¬(decide (v = (Sum.inr 0 : NV p (q + 1))) = true) := by
    refine List.countP_congr fun v _ => ?_
    have := lwMomExp_phi_none v
    cases hh : lwMomExp_phi v with
    | none => simp [(lwMomExp_phi_none v).1 hh]
    | some _ => simp; intro h; exact absurd (this.2 h) (by simp [hh])
  omega

/-- The bound for a path system in which every internal vertex lies on two distinct paths. -/
private theorem lwMomExp_sys_bound (w : ι → ι → ℝ) (T0 Ψ K Z : ℝ) (N : ℕ) (D : Finset ι) (a b : ι)
    (hw0 : ∀ u v, 0 ≤ w u v) (hsym : ∀ u v, w u v = w v u) (hle : ∀ u v, w u v ≤ T0)
    (hww : ∀ c, w c c = T0) (hΨ : T0 ≤ Ψ) (hΨ0 : 0 < Ψ) (hKZ : 0 ≤ K * Z)
    (hstep : ∀ k, 2 ≤ k → k ≤ N → ∀ x y : Fin k → ι,
      ∑ c ∈ D, ∏ i, (w (x i) c * w c (y i)) ≤ K * Z * (Ψ ^ (k - 2) * ∏ i, w (x i) (y i))) :
    ∀ (q p : ℕ) (m : Fin p → List (NV p q)), ∑ i, ((m i).length + 1) ≤ N →
      (∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ m i ∧ Sum.inr j ∈ m i') →
      lwMomExp_sysVal w D a b m ≤
        (K * Z) ^ q * Ψ ^ (((∑ i, ((m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) * (w a b) ^ p := by
  have hT0 : 0 ≤ T0 := (hw0 a a).trans (hww a).le
  intro q
  induction q with
  | zero =>
    intro p m hn hA
    unfold lwMomExp_sysVal
    have hterm : ∀ ℓ : Fin 0 → ι, ∏ i, lwMomExp_chain w a ((m i).map (lwMomExp_lab a b ℓ)) b ≤
        (w a b) ^ p * Ψ ^ (∑ i, (m i).length) := by
      intro ℓ
      have hi : ∀ i, lwMomExp_chain w a ((m i).map (lwMomExp_lab a b ℓ)) b ≤ w a b * T0 ^ (m i).length := by
        intro i
        have := (lwMomExp_base w a b T0 hw0 hsym hle hww ((m i).map (lwMomExp_lab a b ℓ)) a
          (by
            intro z hz
            obtain ⟨v, _, rfl⟩ := List.mem_map.1 hz
            rcases v with e | j
            · rcases e with e | e
              · exact Or.inl rfl
              · exact Or.inr rfl
            · exact j.elim0) (Or.inl rfl)).1 rfl
        simpa using this
      calc ∏ i, lwMomExp_chain w a ((m i).map (lwMomExp_lab a b ℓ)) b
          ≤ ∏ i : Fin p, (w a b * T0 ^ (m i).length) :=
            Finset.prod_le_prod₀ (fun i _ => lwMomExp_chain_nonneg w hw0 _ _ _) fun i _ => hi i
        _ = (w a b) ^ p * T0 ^ (∑ i, (m i).length) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
            simp
        _ ≤ (w a b) ^ p * Ψ ^ (∑ i, (m i).length) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hΨ _) (pow_nonneg (hw0 a b) _)
    calc _ ≤ (Fintype.piFinset (fun _ : Fin 0 => D)).card • ((w a b) ^ p * Ψ ^ (∑ i, (m i).length)) :=
          Finset.sum_le_card_nsmul _ _ _ fun ℓ _ => hterm ℓ
      _ = _ := by
          rw [Fintype.card_piFinset]
          simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul, pow_zero, one_mul]
          have : (((∑ i, ((m i).length + 1) : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) - (p : ℤ)) =
              ((∑ i, (m i).length : ℕ) : ℤ) := by
            simp [Finset.sum_add_distrib]
          rw [this, zpow_natCast]
          ring
  | succ q ih =>
    intro p m hn hA
    have hstp := lwMomExp_step_aux w T0 Ψ K Z N D a b hw0 hww hΨ hΨ0 hKZ hstep m hn (hA 0)
    have hn' : ∑ i, ((lwMomExp_del m i).length + 1) ≤ N := by
      have := lwMomExp_del_length m
      omega
    have hA' : ∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ lwMomExp_del m i ∧
        Sum.inr j ∈ lwMomExp_del m i' := by
      intro j
      obtain ⟨i, i', hne, hi, hi'⟩ := hA j.succ
      refine ⟨i, i', hne, ?_, ?_⟩
      · exact List.mem_filterMap.2 ⟨_, hi, (lwMomExp_phi_succ _ j).2 rfl⟩
      · exact List.mem_filterMap.2 ⟨_, hi', (lwMomExp_phi_succ _ j).2 rfl⟩
    have hih := ih p (lwMomExp_del m) hn' hA'
    have hlen := lwMomExp_del_length m
    have hexp : Ψ ^ ((lwMomExp_occ m : ℤ) - 2) *
        Ψ ^ (((∑ i, ((lwMomExp_del m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) =
        Ψ ^ (((∑ i, ((m i).length + 1) : ℕ) : ℤ) - 2 * ((q + 1 : ℕ) : ℤ) - (p : ℤ)) := by
      rw [← zpow_add₀ hΨ0.ne']
      congr 1
      have : (((∑ i, ((lwMomExp_del m i).length + 1) : ℕ) : ℤ)) + (lwMomExp_occ m : ℤ) =
          ((∑ i, ((m i).length + 1) : ℕ) : ℤ) := by exact_mod_cast hlen
      push_cast at this ⊢
      linarith
    calc lwMomExp_sysVal w D a b m
        ≤ K * Z * Ψ ^ ((lwMomExp_occ m : ℤ) - 2) * lwMomExp_sysVal w D a b (lwMomExp_del m) := hstp
      _ ≤ K * Z * Ψ ^ ((lwMomExp_occ m : ℤ) - 2) * ((K * Z) ^ q *
          Ψ ^ (((∑ i, ((lwMomExp_del m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) * (w a b) ^ p) :=
          mul_le_mul_of_nonneg_left hih (mul_nonneg hKZ (zpow_nonneg hΨ0.le _))
      _ = (K * Z) ^ (q + 1) * (Ψ ^ ((lwMomExp_occ m : ℤ) - 2) *
          Ψ ^ (((∑ i, ((lwMomExp_del m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ))) *
          (w a b) ^ p := by ring
      _ = _ := by rw [hexp]

end Induction

/-! ## 5. The kernel `𝖳_t(|·-·|_1 ∧ ℓ)`, the constants of `claim:TTk`, the near step -/

/-- `𝖳_t(|u - v|_1 ∧ ℓ)` (`7_8:1650`, the norm `zdistD` of the merged `EKTTk`). -/
noncomputable def lwMomExp_tau (d L : ℕ) (W g t ℓ : ℝ) (u v : Zd d L) : ℝ :=
  sfT d L W g t (min ((zdistD d L (u - v) : ℕ) : ℝ) ℓ)

/-- The value of a nested graph with the internal labels restricted to `D` (`7_8:1636`, `7_8:1650`):
`Σ_{ℓ ∈ D^q} Π_k w_k(ℓ)`, the summand of the merged `anpKey6_val_eq`. -/
noncomputable def lwMomExp_valOnD {p q : ℕ} {ι : Type*} (Γ : NGraph p q) (ξ : ι → ι → ℝ)
    (a b : Fin p → ι) (D : Finset ι) : ℝ :=
  ∑ ℓ ∈ Fintype.piFinset (fun _ : Fin q => D), ∏ k : Fin Γ.es.length, anpKey6_w Γ ξ a b ℓ k

/-- `𝐃_{≤ℓ}` (`7_8:1650`): `|a - c| ∨ |b - c| ≤ ℓ`, block distance `zdistD` (the norm of the merged
`EKTTk`). -/
noncomputable def lwMomExp_nearD (d L : ℕ) [NeZero L] (a b : Zd d L) (ℓ : ℝ) : Finset (Zd d L) :=
  Finset.univ.filter fun c =>
    ((zdistD d L (a - c) : ℕ) : ℝ) ≤ ℓ ∧ ((zdistD d L (b - c) : ℕ) : ℝ) ≤ ℓ

section Tau

variable {d L : ℕ} [NeZero L] {W g t ℓ : ℝ}

private theorem lwMomExp_tau_nonneg (u v : Zd d L) : 0 ≤ lwMomExp_tau d L W g t ℓ u v :=
  sfT_nonneg _

private theorem lwMomExp_tau_symm (u v : Zd d L) :
    lwMomExp_tau d L W g t ℓ u v = lwMomExp_tau d L W g t ℓ v u := by
  unfold lwMomExp_tau
  rw [← neg_sub u v, zdistD_neg]

private theorem lwMomExp_tau_self (hℓ : 0 ≤ ℓ) (c : Zd d L) :
    lwMomExp_tau d L W g t ℓ c c = sfT d L W g t 0 := by
  unfold lwMomExp_tau
  simp [min_eq_left hℓ]

private theorem lwMomExp_sfT_le_zero {r : ℝ} (hr : 0 ≤ r) :
    sfT d L W g t r ≤ sfT d L W g t 0 := by
  refine (sfT_le_zero_mul hr).trans ?_
  have h0 : 0 ≤ sfT d L W g t 0 := sfT_nonneg _
  have h1 : √(((r + 1) ^ (d - 2))⁻¹) ≤ 1 := by
    apply Real.sqrt_le_one.2
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by linarith)
  nlinarith

private theorem lwMomExp_tau_le (hℓ : 0 ≤ ℓ) (u v : Zd d L) :
    lwMomExp_tau d L W g t ℓ u v ≤ sfT d L W g t 0 :=
  lwMomExp_sfT_le_zero (le_min (Nat.cast_nonneg _) hℓ)

private theorem lwMomExp_psi_pos (hW : 0 < W) (ht : t < 1) : 0 < PsiT d L W g t := by
  unfold PsiT
  apply Real.sqrt_pos.2
  have h1t : 0 < |1 - t| := abs_pos.2 (by linarith)
  have hB : 0 < Bparam d L g t 0 := by
    unfold Bparam
    have hg2 : 0 < g ^ 2 + |1 - t| := by nlinarith [sq_nonneg g]
    have : 0 < (g ^ 2 + |1 - t|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
      apply mul_pos (inv_pos.2 hg2)
      simp
    have h2 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
    linarith
  exact mul_pos (inv_pos.2 (pow_pos hW _)) hB

end Tau

/-- The `claim:TTk` body of the merged pin `EKTTk d n` at the constant `C`. -/
private def lwMomExp_TTkBody (d n : ℕ) (C : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
    ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
    ∀ (D : Finset (Zd d L)) (a : Zd d L), (∀ α ∈ D, (zdistD d L (a - α) : ℝ) ≤ ℓ) →
    ∀ x y : Fin n → Zd d L,
      ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistD d L (x i - α) : ℝ) ℓ)
            * sfT d L W g t (min (zdistD d L (y i - α) : ℝ) ℓ))
        ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
            (PsiT d L W g t ^ (n - 2) *
              ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))

private theorem lwMomExp_TTkBody_mono {d n : ℕ} {C C' : ℝ} (h : lwMomExp_TTkBody d n C)
    (hCC : C ≤ C') : lwMomExp_TTkBody d n C' := by
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt D a hD x y
  refine (h L W g t hW hg ht hgL ℓ Λ hℓ hℓt D a hD x y).trans ?_
  have h1t : 0 < 1 - t := by linarith
  have hX : 0 ≤ (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
      (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ)) := by
    have : 0 ≤ PsiT d L W g t := PsiT_nonneg
    have : 0 ≤ ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ) :=
      Finset.prod_nonneg fun i _ => sfT_nonneg _
    positivity
  calc C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))
      = C * ((Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))) := by ring
    _ ≤ C' * ((Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistD d L (x i - y i) : ℝ) ℓ))) :=
        mul_le_mul_of_nonneg_right hCC hX
    _ = _ := by ring

/-- One constant for all `claim:TTk` with `2 ≤ k ≤ N` pairs. -/
private theorem lwMomExp_exists_K (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ k, 2 ≤ k → k ≤ N → lwMomExp_TTkBody d k K := by
  induction N with
  | zero => exact ⟨1, one_pos, fun k hk hkN => by omega⟩
  | succ N ih =>
    obtain ⟨K, hK, hKk⟩ := ih
    by_cases h2 : 2 ≤ N + 1
    · obtain ⟨C, hC, hCb⟩ := ekTTk_holds d (N + 1) hd h2
      refine ⟨max K C, lt_max_of_lt_left hK, fun k hk hkN => ?_⟩
      by_cases hkN' : k ≤ N
      · exact lwMomExp_TTkBody_mono (hKk k hk hkN') (le_max_left _ _)
      · have : k = N + 1 := by omega
        subst this
        exact lwMomExp_TTkBody_mono hCb (le_max_right _ _)
    · exact ⟨K, hK, fun k hk hkN => hKk k hk (by omega)⟩

section NearStep

/-- The `claim:TTk` bound for `k` pairs, for the kernel `τ`. -/
private theorem lwMomExp_hstep {d N : ℕ} {K : ℝ} (hK : ∀ k, 2 ≤ k → k ≤ N → lwMomExp_TTkBody d k K)
    (L : ℕ) [NeZero L] (W g t : ℝ) (hW : 0 < W) (hg : 0 ≤ g) (ht : t < 1)
    (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) (ℓ Λ : ℝ) (hℓ : 1 ≤ ℓ) (hℓt : ℓ ≤ Λ * ellT L g t)
    (a b : Zd d L) :
    ∀ k, 2 ≤ k → k ≤ N → ∀ x y : Fin k → Zd d L,
      ∑ c ∈ lwMomExp_nearD d L a b ℓ,
        ∏ i, (lwMomExp_tau d L W g t ℓ (x i) c * lwMomExp_tau d L W g t ℓ c (y i)) ≤
      K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) * (PsiT d L W g t ^ (k - 2) *
        ∏ i, lwMomExp_tau d L W g t ℓ (x i) (y i)) := by
  intro k hk hkN x y
  have h := hK k hk hkN L W g t hW hg ht hgL ℓ Λ hℓ hℓt (lwMomExp_nearD d L a b ℓ) a
    (fun α hα => by
      unfold lwMomExp_nearD at hα
      exact (Finset.mem_filter.1 hα).2.1) x y
  calc _ = ∑ c ∈ lwMomExp_nearD d L a b ℓ,
        ∏ i, (lwMomExp_tau d L W g t ℓ (x i) c * lwMomExp_tau d L W g t ℓ (y i) c) :=
        Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => by
          rw [lwMomExp_tau_symm c (y i)]
    _ ≤ _ := h

/-- **The corrected one-vertex step of the near sum** (`7_8:1770-1775`, `claim:TTk`; the corrected form of
the ticket's `lwMomExp_near_step`, amendment 1): the paths of a nested graph are vertex sequences `m i`
(between the external vertices `a_i`, `b_i`); the first internal vertex `α = inr 0` is on two distinct
paths.  Summing `α` over `𝐃_{≤ℓ}` and deleting it from every path (a passage `x → α → y` becomes the
step `x y`; a passage with `x = y` or a step `α α` stays as a step of weight `𝖳_t(0) ≤ Ψ_t`) costs
`K Λ² (W^d (1-t))⁻¹ Ψ_t^{A-2}`, `A` the number of occurrences of `α`; the constant `K` depends on `d` and the
total length `N` only. -/
theorem lwMomExp_near_step' (d N : ℕ) (hd : 3 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ a b : Zd d L,
      ∀ {p q : ℕ} (m : Fin p → List (NV p (q + 1))),
        ∑ i, ((m i).length + 1) ≤ N → (∃ i i', i ≠ i' ∧ Sum.inr 0 ∈ m i ∧ Sum.inr 0 ∈ m i') →
        lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b m ≤
          K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) * PsiT d L W g t ^ ((lwMomExp_occ m : ℤ) - 2) *
            lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b
              (lwMomExp_del m) := by
  obtain ⟨K, hK, hKk⟩ := lwMomExp_exists_K d hd N
  refine ⟨K, hK, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt a b p q m hn hv
  have h1t : 0 < 1 - t := by linarith
  have hZ : 0 ≤ Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by positivity
  exact lwMomExp_step_aux (lwMomExp_tau d L W g t ℓ) (sfT d L W g t 0) (PsiT d L W g t) K _ N _ a b
    lwMomExp_tau_nonneg (lwMomExp_tau_self (by linarith)) (sfT_zero_le_PsiT hW)
    (lwMomExp_psi_pos hW ht) (mul_nonneg hK.le hZ)
    (lwMomExp_hstep hKk L W g t hW hg ht hgL ℓ Λ hℓ hℓt a b) m hn hv

/-- The bound for a path system (every internal vertex on two distinct paths), the kernel `τ`. -/
private theorem lwMomExp_sys_near (d N : ℕ) (hd : 3 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ a b : Zd d L,
      ∀ (q p : ℕ) (m : Fin p → List (NV p q)), ∑ i, ((m i).length + 1) ≤ N →
        (∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ m i ∧ Sum.inr j ∈ m i') →
        lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b m ≤
          (K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
            PsiT d L W g t ^ (((∑ i, ((m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
            (lwMomExp_tau d L W g t ℓ a b) ^ p := by
  obtain ⟨K, hK, hKk⟩ := lwMomExp_exists_K d hd N
  refine ⟨K, hK, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt a b
  have h1t : 0 < 1 - t := by linarith
  have hZ : 0 ≤ Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by positivity
  exact lwMomExp_sys_bound (lwMomExp_tau d L W g t ℓ) (sfT d L W g t 0) (PsiT d L W g t) K _ N _ a b
    lwMomExp_tau_nonneg lwMomExp_tau_symm (lwMomExp_tau_le (by linarith))
    (lwMomExp_tau_self (by linarith)) (sfT_zero_le_PsiT hW) (lwMomExp_psi_pos hW ht)
    (mul_nonneg hK.le hZ) (lwMomExp_hstep hKk L W g t hW hg ht hgL ℓ Λ hℓ hℓt a b)

end NearStep

/-! ## 6. Nested graphs as path systems -/

section Graph

variable {p q : ℕ} (Γ : NGraph p q)

/-- The step of `WalkOK`. -/
private def lwMomExp_stepFn (acc : Option (NV p q)) (st : Fin Γ.es.length × NV p q) : Option (NV p q) :=
  acc.bind fun c =>
    if ((Γ.es.get st.1).u = c ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = c ∧ (Γ.es.get st.1).u = st.2) then some st.2 else none

private theorem lwMomExp_stepFn_eq (x y : NV p q) (st : Fin Γ.es.length × NV p q) :
    lwMomExp_stepFn Γ (some x) st = some y ↔
      y = st.2 ∧ (((Γ.es.get st.1).u = x ∧ (Γ.es.get st.1).v = st.2) ∨
        ((Γ.es.get st.1).v = x ∧ (Γ.es.get st.1).u = st.2)) := by
  unfold lwMomExp_stepFn
  dsimp only [Option.bind]
  split_ifs with h
  · simp only [Option.some.injEq]
    constructor
    · intro h'; exact ⟨h'.symm, h⟩
    · intro h'; exact h'.1.symm
  · simp only [false_iff]
    intro h'; exact h h'.2

private theorem lwMomExp_foldl_none (l : List (Fin Γ.es.length × NV p q)) :
    l.foldl (lwMomExp_stepFn Γ) none = none := by
  induction l with
  | nil => rfl
  | cons st t ih => simpa [List.foldl_cons, lwMomExp_stepFn] using ih

/-- The first step of a walk. -/
private theorem lwMomExp_fold_cons (st : Fin Γ.es.length × NV p q) (t : List (Fin Γ.es.length × NV p q))
    (x y : NV p q) (h : (st :: t).foldl (lwMomExp_stepFn Γ) (some x) = some y) :
    lwMomExp_stepFn Γ (some x) st = some st.2 ∧ t.foldl (lwMomExp_stepFn Γ) (some st.2) = some y := by
  rw [List.foldl_cons] at h
  cases hs : lwMomExp_stepFn Γ (some x) st with
  | none =>
    rw [hs, lwMomExp_foldl_none] at h
    exact absurd h (by simp)
  | some z =>
    rw [hs] at h
    have hz : z = st.2 := ((lwMomExp_stepFn_eq Γ x z st).1 hs).1
    subst hz
    exact ⟨rfl, h⟩

/-- A walk whose steps are weighted by a symmetric `w` of the labels of the end vertices of the edge:
the product of the weights is the chain product along the vertex sequence. -/
private theorem lwMomExp_walk_chain {ι : Type*} (w : ι → ι → ℝ) (hsym : ∀ u v, w u v = w v u)
    (lbl : NV p q → ι) :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), l ≠ [] →
      l.foldl (lwMomExp_stepFn Γ) (some x) = some y →
      (l.map fun st => w (lbl (Γ.es.get st.1).u) (lbl (Γ.es.get st.1).v)).prod =
        lwMomExp_chain w (lbl x) (((l.map Prod.snd).dropLast).map lbl) (lbl y) := by
  intro l
  induction l with
  | nil => intro x y h; exact absurd rfl h
  | cons st t ih =>
    intro x y _ h
    obtain ⟨h1, h2⟩ := lwMomExp_fold_cons Γ st t x y h
    have hc := ((lwMomExp_stepFn_eq Γ x st.2 st).1 h1).2
    have hw : w (lbl (Γ.es.get st.1).u) (lbl (Γ.es.get st.1).v) = w (lbl x) (lbl st.2) := by
      rcases hc with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [hu, hv]
      · rw [hu, hv, hsym]
    by_cases ht : t = []
    · subst ht
      have hy : y = st.2 := (by simpa using h2 : st.2 = y).symm
      subst hy
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hw,
        List.dropLast_singleton, lwMomExp_chain]
    · have ih' := ih st.2 y ht h2
      have hne : t.map Prod.snd ≠ [] := by simpa using ht
      simp only [List.map_cons, List.prod_cons, hw, ih']
      rw [List.dropLast_cons_of_ne_nil hne]
      simp [lwMomExp_chain]

/-- A walk ends at `y`: the vertex sequence is its `dropLast` followed by `y`. -/
private theorem lwMomExp_walk_last :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q), l ≠ [] →
      l.foldl (lwMomExp_stepFn Γ) (some x) = some y →
      l.map Prod.snd = (l.map Prod.snd).dropLast ++ [y] := by
  intro l
  induction l with
  | nil => intro x y h; exact absurd rfl h
  | cons st t ih =>
    intro x y _ h
    obtain ⟨h1, h2⟩ := lwMomExp_fold_cons Γ st t x y h
    by_cases ht : t = []
    · subst ht
      have hy : y = st.2 := (by simpa using h2 : st.2 = y).symm
      subst hy
      simp
    · have ih' := ih st.2 y ht h2
      have hne : t.map Prod.snd ≠ [] := by simpa using ht
      rw [List.map_cons, List.dropLast_cons_of_ne_nil hne, List.cons_append, ← ih']

/-- Every vertex of an edge of a step of the walk is the start or one of the later vertices. -/
private theorem lwMomExp_walk_visit :
    ∀ (l : List (Fin Γ.es.length × NV p q)) (x y : NV p q),
      l.foldl (lwMomExp_stepFn Γ) (some x) = some y →
      ∀ st ∈ l, ∀ v0, ((Γ.es.get st.1).u = v0 ∨ (Γ.es.get st.1).v = v0) →
        v0 = x ∨ v0 ∈ l.map Prod.snd := by
  intro l
  induction l with
  | nil => intro x y _ st hst; simp at hst
  | cons st' t ih =>
    intro x y h st hst v0 hv0
    rw [List.foldl_cons] at h
    cases hs : lwMomExp_stepFn Γ (some x) st' with
    | none =>
      rw [hs, lwMomExp_foldl_none] at h
      exact absurd h (by simp)
    | some z =>
      rw [hs] at h
      have hzc := (lwMomExp_stepFn_eq Γ x z st').1 hs
      rcases List.mem_cons.1 hst with rfl | hst
      · rcases hzc.2 with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · rcases hv0 with h0 | h0
          · exact Or.inl (h0.symm.trans hu)
          · exact Or.inr (by rw [← h0, hv]; simp)
        · rcases hv0 with h0 | h0
          · exact Or.inr (by rw [← h0, hu]; simp)
          · exact Or.inl (h0.symm.trans hv)
      · rcases ih z y h st hst v0 hv0 with h0 | h0
        · exact Or.inr (by rw [h0, hzc.1]; simp)
        · exact Or.inr (List.mem_cons_of_mem _ h0)

/-- The path system of a nested graph: the vertex sequence of the path `i` between `a_i` and `b_i`. -/
def lwMomExp_sysOf : Fin p → List (NV p q) := fun i => ((Γ.path i).map Prod.snd).dropLast

private theorem lwMomExp_path_ne (hN : Γ.IsNested) (i : Fin p) : Γ.path i ≠ [] := by
  intro h
  have := hN.2.1 i
  unfold NGraph.WalkOK at this
  rw [h] at this
  simp at this

private theorem lwMomExp_path_split (hN : Γ.IsNested) (i : Fin p) :
    (Γ.path i).map Prod.snd = lwMomExp_sysOf Γ i ++ [Sum.inl (Sum.inr i)] :=
  lwMomExp_walk_last Γ (Γ.path i) _ _ (lwMomExp_path_ne Γ hN i) (hN.2.1 i)

private theorem lwMomExp_sysOf_length (hN : Γ.IsNested) (i : Fin p) :
    (lwMomExp_sysOf Γ i).length + 1 = (Γ.path i).length := by
  have := congrArg List.length (lwMomExp_path_split Γ hN i)
  simpa using this.symm

private theorem lwMomExp_sysOf_mem (hN : Γ.IsNested) (i : Fin p) (j : Fin q) (h : Γ.Visits i (Sum.inr j)) :
    (Sum.inr j : NV p q) ∈ lwMomExp_sysOf Γ i := by
  obtain ⟨st, hst, hv⟩ := h
  rcases lwMomExp_walk_visit Γ (Γ.path i) _ _ (hN.2.1 i) st hst _ hv with h0 | h0
  · exact absurd h0 (by simp)
  · rw [lwMomExp_path_split Γ hN i] at h0
    rcases List.mem_append.1 h0 with h1 | h1
    · exact h1
    · exact absurd (List.mem_singleton.1 h1) (by simp)

/-- The indices of the edges lying on the paths. -/
private def lwMomExp_pathEdges : Finset (Fin Γ.es.length) :=
  Finset.univ.biUnion fun i => ((Γ.path i).map Prod.fst).toFinset

private theorem lwMomExp_pathEdges_disj (hN : Γ.IsNested) :
    ((Finset.univ : Finset (Fin p)) : Set (Fin p)).PairwiseDisjoint
      (fun i => ((Γ.path i).map Prod.fst).toFinset) := by
  intro i _ j _ hij
  refine Finset.disjoint_left.2 fun k hki hkj => ?_
  obtain ⟨st, hst, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hki)
  obtain ⟨st', hst', hk⟩ := List.mem_map.1 (List.mem_toFinset.1 hkj)
  exact hN.2.2.2.1 i j hij st hst st' hst' hk.symm

private theorem lwMomExp_pathEdges_card (hN : Γ.IsNested) :
    (lwMomExp_pathEdges Γ).card = ∑ i, (Γ.path i).length := by
  unfold lwMomExp_pathEdges
  rw [Finset.card_biUnion (lwMomExp_pathEdges_disj Γ hN)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.toFinset_card_of_nodup (hN.2.2.1 i), List.length_map]

/-- The product over all edges is the product over the paths times the product over the other edges. -/
private theorem lwMomExp_prod_split (hN : Γ.IsNested) (g : Fin Γ.es.length → ℝ) :
    ∏ k, g k = (∏ i, ((Γ.path i).map fun st => g st.1).prod) *
      ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, g k := by
  rw [← Finset.prod_mul_prod_compl (lwMomExp_pathEdges Γ)]
  congr 1
  unfold lwMomExp_pathEdges
  rw [Finset.prod_biUnion (lwMomExp_pathEdges_disj Γ hN)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.prod_toFinset _ (hN.2.2.1 i), List.map_map]
  rfl

end Graph

/-! ## 7. The pin `AnpDetNear` and `lwMomExp_near` (`(adsuu_exp2)`, `7_8:1655`) -/

/-- **Near pin** (`(adsuu_exp2)`, `7_8:1655-1786`): `a_i ≡ a`, `b_i ≡ b`; edges `ξ ≤ 𝖳_t(|α-β|∧ℓ)` in
`zdistD`; in the regime of `EKTTk` (`1 - t ≥ g²/L²`, `1 ≤ ℓ ≤ Λ ℓ_t`), the value with internal labels in
`𝐃_{≤ℓ}` is `≤ C (Λ²(W^d(1-t))⁻¹)^q Ψ_t^{ord - p} 𝖳_t(|a-b|∧ℓ)^p`; `C` depends on `Γ`, `d` only. -/
def AnpDetNearAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistD d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ a b : Zd d L,
          lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) (lwMomExp_nearD d L a b ℓ) ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistD d L (a - b) : ℕ) : ℝ) ℓ) ^ p

def AnpDetNear (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpDetNearAt d Γ

section NearGraph

variable {p q : ℕ}

private theorem lwMomExp_nSolid (Γ : NGraph p q) (hNG : Γ.NoGhost) : Γ.nSolid = Γ.es.length := by
  unfold NGraph.nSolid
  rw [List.filter_eq_self.2]
  intro e he
  simp [hNG e he]

private theorem lwMomExp_ordN (Γ : NGraph p q) (hNG : Γ.NoGhost) :
    Γ.ordN = (Γ.es.length : ℤ) - 2 * (q : ℤ) := by
  unfold NGraph.ordN ord
  rw [lwMomExp_nSolid Γ hNG]
  simp
  ring

/-- **`lem:LW_moment_exp`, near bound, for one nested graph.** -/
theorem lwMomExp_near_graph (d : ℕ) (hd : 3 ≤ d) (Γ : NGraph p q) (hNG : Γ.NoGhost) (hN : Γ.IsNested) :
    AnpDetNearAt d Γ := by
  obtain ⟨K, hK, hKb⟩ := lwMomExp_sys_near d (∑ i, (Γ.path i).length) hd
  refine ⟨K ^ q, pow_pos hK q, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt ξ hξ hξτ a b
  have h1t : 0 < 1 - t := by linarith
  have hsum : ∑ i, ((lwMomExp_sysOf Γ i).length + 1) = ∑ i, (Γ.path i).length :=
    Finset.sum_congr rfl fun i _ => lwMomExp_sysOf_length Γ hN i
  have hA : ∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ lwMomExp_sysOf Γ i ∧
      Sum.inr j ∈ lwMomExp_sysOf Γ i' := by
    intro j
    obtain ⟨i, i', hne, hv, hv'⟩ := hN.2.2.2.2.1 j
    exact ⟨i, i', hne, lwMomExp_sysOf_mem Γ hN i j hv, lwMomExp_sysOf_mem Γ hN i' j hv'⟩
  have hsys := hKb L W g t hW hg ht hgL ℓ Λ hℓ hℓt a b q p (lwMomExp_sysOf Γ) hsum.le hA
  rw [hsum] at hsys
  set T0 : ℝ := sfT d L W g t 0 with hT0
  have hT00 : 0 ≤ T0 := sfT_nonneg _
  have hΨ : T0 ≤ PsiT d L W g t := sfT_zero_le_PsiT hW
  have hΨ0 : 0 < PsiT d L W g t := lwMomExp_psi_pos hW ht
  set c : ℕ := (lwMomExp_pathEdges Γ)ᶜ.card with hc
  -- the bound at one labelling of the internal vertices
  have hpt : ∀ ℓ' : Fin q → Zd d L,
      ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤
        T0 ^ c * ∏ i, lwMomExp_chain (lwMomExp_tau d L W g t ℓ) a
          ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b := by
    intro ℓ'
    set g' : Fin Γ.es.length → ℝ := fun k =>
      lwMomExp_tau d L W g t ℓ (lwMomExp_lab a b ℓ' (Γ.es.get k).u)
        (lwMomExp_lab a b ℓ' (Γ.es.get k).v) with hg'
    have hw : ∀ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤ g' k := by
      intro k
      have hgh : (Γ.es.get k).ghost = false := hNG _ (List.get_mem _ k)
      unfold anpKey6_w
      rw [hgh]
      exact hξτ _ _
    calc ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤ ∏ k, g' k :=
          Finset.prod_le_prod₀ (fun k _ => anpKey6_w_nonneg Γ ξ (fun α β => (hξ α β).1) _ _ _ _)
            (fun k _ => hw k)
      _ = (∏ i, ((Γ.path i).map fun st => g' st.1).prod) *
            ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, g' k := lwMomExp_prod_split Γ hN g'
      _ ≤ (∏ i, lwMomExp_chain (lwMomExp_tau d L W g t ℓ) a
            ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b) * T0 ^ c := by
          refine mul_le_mul (le_of_eq ?_) ?_ (Finset.prod_nonneg fun k _ => lwMomExp_tau_nonneg _ _)
            (Finset.prod_nonneg fun i _ => lwMomExp_chain_nonneg _ lwMomExp_tau_nonneg _ _ _)
          · refine Finset.prod_congr rfl fun i _ => ?_
            exact lwMomExp_walk_chain Γ (lwMomExp_tau d L W g t ℓ) lwMomExp_tau_symm
              (lwMomExp_lab a b ℓ') (Γ.path i) _ _ (lwMomExp_path_ne Γ hN i) (hN.2.1 i)
          · calc ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, g' k ≤ ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, T0 :=
                  Finset.prod_le_prod₀ (fun k _ => lwMomExp_tau_nonneg _ _)
                    (fun k _ => lwMomExp_tau_le (by linarith) _ _)
              _ = T0 ^ c := Finset.prod_const _
      _ = _ := mul_comm _ _
  have hcard : (lwMomExp_pathEdges Γ).card + c = Γ.es.length := by
    rw [hc, Finset.card_add_card_compl, Fintype.card_fin]
  have hexp : ((c : ℤ)) + (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) =
      Γ.ordN - (p : ℤ) := by
    have hpc := lwMomExp_pathEdges_card Γ hN
    have h3 : (Γ.es.length : ℤ) = (c : ℤ) + ((∑ i, (Γ.path i).length : ℕ) : ℤ) := by
      exact_mod_cast (by omega : Γ.es.length = c + ∑ i, (Γ.path i).length)
    rw [lwMomExp_ordN Γ hNG]
    linarith
  unfold lwMomExp_valOnD
  calc ∑ ℓ' ∈ Fintype.piFinset (fun _ : Fin q => lwMomExp_nearD d L a b ℓ),
        ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k
      ≤ ∑ ℓ' ∈ Fintype.piFinset (fun _ : Fin q => lwMomExp_nearD d L a b ℓ),
        T0 ^ c * ∏ i, lwMomExp_chain (lwMomExp_tau d L W g t ℓ) a
          ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b :=
        Finset.sum_le_sum fun ℓ' _ => hpt ℓ'
    _ = T0 ^ c * lwMomExp_sysVal (lwMomExp_tau d L W g t ℓ) (lwMomExp_nearD d L a b ℓ) a b
          (lwMomExp_sysOf Γ) := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ T0 ^ c * ((K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
          PsiT d L W g t ^ (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
          (lwMomExp_tau d L W g t ℓ a b) ^ p) :=
        mul_le_mul_of_nonneg_left hsys (pow_nonneg hT00 _)
    _ ≤ PsiT d L W g t ^ c * ((K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
          PsiT d L W g t ^ (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
          (lwMomExp_tau d L W g t ℓ a b) ^ p) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT00 hΨ c) ?_
        have : 0 ≤ Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by positivity
        have := lwMomExp_tau_nonneg (d := d) (L := L) (W := W) (g := g) (t := t) (ℓ := ℓ) a b
        positivity
    _ = K ^ q * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q *
          PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistD d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by
        rw [← hexp, zpow_add₀ hΨ0.ne', zpow_natCast, mul_pow]
        unfold lwMomExp_tau
        ring

/-- **`lem:LW_moment_exp`, the deterministic near bound `(adsuu_exp2)`** for every nested graph without
ghost edges and every `d ≥ 3`. -/
theorem lwMomExp_near : ∀ d, AnpDetNear d :=
  fun d hd _ _ Γ hNG hN => lwMomExp_near_graph d hd Γ hNG hN

end NearGraph

/-! ## 8. Compiled nonempty instances at `d = 3`

The graph is `figAux` (`p = q = 2`, six solid edges, two paths `x → ℳ₁ → ℳ₂ → y`; `figAux_nested`).  The
numerical data: `L = 6`, `W = 2`, `g = 1/2`, `t = 1/2` (`g² = 1/4 ≤ L²(1 - t) = 18`), `ℓ = Λ = 2`
(`ℓ ≤ Λ ℓ_t` since `ℓ_t ≥ 1`, `one_le_ellT`), `a = 0`, `b = e₀`; `𝐃_{≤ℓ}` contains `0` (`|a - 0|_1 = 0`,
`|b - 0|_1 = 1`).  The edge variable is `ξ = 𝖳_t(|·-·|_1 ∧ ℓ)` itself.  No hypothesis is left. -/

/-- Instance 1: the near pin at `figAux`, from `lwMomExp_near`. -/
theorem lwMomExp_inst_near : AnpDetNearAt 3 figAux :=
  lwMomExp_near 3 le_rfl 2 2 figAux figAux_nested.2 figAux_nested.1

private theorem lwMomExp_inst_ell : (2 : ℝ) ≤ 2 * ellT 6 (1 / 2) (1 / 2) := by
  have := one_le_ellT (L := 6) (g := 1 / 2) (t := 1 / 2) (by norm_num)
  linarith

private theorem lwMomExp_inst_mem :
    (0 : Zd 3 6) ∈ lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2 := by
  unfold lwMomExp_nearD
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by simp, ?_⟩
  have : zdistD 3 6 ((Pi.single 0 1 : Zd 3 6) - 0) = 1 := by decide
  rw [this]
  norm_num

/-- Instance 1 at the data above: the inequality of the pin with `ξ = 𝖳_t(|·-·|_1 ∧ ℓ)`, `D ≠ ∅`. -/
theorem lwMomExp_inst_near_pt : ∃ C : ℝ, 0 < C ∧
    (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2).Nonempty ∧
    lwMomExp_valOnD figAux (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2) (fun _ => (0 : Zd 3 6))
        (fun _ => (Pi.single 0 1 : Zd 3 6)) (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) ≤
      C * ((2 : ℝ) ^ 2 * (((2 : ℝ) ^ 3)⁻¹ / (1 - 1 / 2))) ^ 2 *
        PsiT 3 6 2 (1 / 2) (1 / 2) ^ (figAux.ordN - ((2 : ℕ) : ℤ)) *
        sfT 3 6 2 (1 / 2) (1 / 2) (min ((zdistD 3 6 ((0 : Zd 3 6) - Pi.single 0 1) : ℕ) : ℝ) 2) ^ 2 := by
  obtain ⟨C, hC, H⟩ := lwMomExp_inst_near
  refine ⟨C, hC, ⟨0, lwMomExp_inst_mem⟩, ?_⟩
  exact H 6 2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2 2
    (by norm_num) lwMomExp_inst_ell (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2)
    (fun α β => ⟨lwMomExp_tau_nonneg α β, lwMomExp_tau_symm α β⟩) (fun α β => le_rfl) 0 (Pi.single 0 1)

private theorem lwMomExp_sysOf_figAux (i : Fin 2) :
    lwMomExp_sysOf figAux i = [Sum.inr 0, Sum.inr 1] := by
  fin_cases i <;> rfl

/-- Instance 3: the corrected step at the first internal vertex of `figAux` (two passages `k = 2`:
`x → ℳ₁ → ℳ₂` on both paths): the data of instance 1, `N = 6`. -/
theorem lwMomExp_inst_step : ∃ K : ℝ, 0 < K ∧
    lwMomExp_sysVal (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2)
        (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) 0 (Pi.single 0 1) (lwMomExp_sysOf figAux) ≤
      K * ((2 : ℝ) ^ 2 * (((2 : ℝ) ^ 3)⁻¹ / (1 - 1 / 2))) *
        PsiT 3 6 2 (1 / 2) (1 / 2) ^ ((lwMomExp_occ (lwMomExp_sysOf figAux) : ℤ) - 2) *
        lwMomExp_sysVal (lwMomExp_tau 3 6 2 (1 / 2) (1 / 2) 2)
          (lwMomExp_nearD 3 6 (0 : Zd 3 6) (Pi.single 0 1) 2) 0 (Pi.single 0 1)
          (lwMomExp_del (lwMomExp_sysOf figAux)) := by
  obtain ⟨K, hK, H⟩ := lwMomExp_near_step' 3 6 le_rfl
  refine ⟨K, hK, ?_⟩
  exact H 6 2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2 2
    (by norm_num) lwMomExp_inst_ell 0 (Pi.single 0 1) (lwMomExp_sysOf figAux) (by decide)
    ⟨0, 1, by decide, by simp [lwMomExp_sysOf_figAux], by simp [lwMomExp_sysOf_figAux]⟩

end RBM.Graph
