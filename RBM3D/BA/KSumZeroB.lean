/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KSumZeroA
import RBM3D.BA.KPure
import RBM3D.BA.KMolecule
import RBM3D.Loop.KLIndStepA

/-!
# Stage K, row K08b: the absolute weighted clause of the BA molecule weight and `SigSumZeroAbs`

Ticket T2391 (design BA-DK, `docs/reports/T2360-design.md` §3 (c), §5 row K08b).  The argument was
written and audited in the design gate of T2385 (`docs/reports/T2385-prove.md` (a+), "Absolute
weighted clause (K08b)").  Paper: `(eq:Sigma-empty-sum-zero)` and `(eq:molecule-decay)`
(`A_deterministic_estimates.tex:691-734`).  The BA twin of the band `Loop/KLIndStepA.lean` §5
(`KLIndStepA_nc_pointwise`, `KLsumZero_weighted`, `sigSumZeroAbs_band`).

1. `KSumZeroB_unequal_edge` (B1): for a labelling `β` of the slots of a cactus whose leaf labels
   are not constant, either a chord has `β (In J) ≠ β (Out J)` or a node has two `M`-edges with
   unequal ends.
2. `baSig_nc_pointwise` (B2): `|Σ^{(∅)}(σ, δ)| ≤ G g² e^{-c max_{i,j} |δ_i - δ_j|}` for every `σ`
   and every non-constant `δ`, uniformly in the family `(L, g ≤ Λ, E, m, t ≤ 1)`.
3. `baSig_weighted` (B3): for every `Q` and every alternating `σ`, on every slice `δ_r = x`,
   `Σ |Σ^{(∅)}(δ)| (max |δ_i - δ_j| + 1)^Q ≤ C (g² + (1 - t))` (the proof of `KLsumZero_weighted`,
   with B2 for `KLIndStepA_nc_pointwise` and the signed clause `baSig_signed_sum` of K08a).
4. `baSig_sumZeroAbs` (B4): the K-b predicate `SigSumZeroAbs d n L g t (BASig d n L g E m t)`,
   under `3 ≤ n`, `t i < 1` (the ranges of `sigSumZeroAbs_band` and of its consumers;
   `SigSumZeroAbs` itself, which is false at `n = 2`, is untouched).
5. Compiled nonempty instances at the flow point `P` of `(d, L) = (3, 4)`, `n = 4`.

Public: the declarations above; every other helper is `private` with the stem `KSumZeroB_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. B1: an unequal edge in every cactus labelling that is not constant on the leaves -/

section Cycle

/-- A cycle with at most one unequal edge has none: if `b s ≠ b (nx s)` and every other element of the orbit of `s` has
`b s' = b (nx s')`, then going once round the orbit `nx s, nx² s, …, s` shows `b (nx s) = b s`. -/
private theorem KSumZeroB_cycle {α β X : Type*} (nx : α → α) (nd : α → β) (hnd : ∀ s, nd (nx s) = nd s)
    (horb : ∀ s t, nd s = nd t → ∃ k : ℕ, nx^[k] s = t) (b : α → X) {s : α} (hs : b s ≠ b (nx s)) :
    ∃ s' : α, s' ≠ s ∧ nd s' = nd s ∧ b s' ≠ b (nx s') := by
  classical
  by_contra hcon
  push Not at hcon
  have hex : ∃ k : ℕ, nx^[k] (nx s) = s := horb (nx s) s (hnd s)
  have hk₀spec : nx^[Nat.find hex] (nx s) = s := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, nx^[j] (nx s) ≠ s := fun j hj => Nat.find_min hex hj
  have hnodeIter : ∀ j : ℕ, nd (nx^[j] (nx s)) = nd s := by
    intro j
    induction j with
    | zero => exact hnd s
    | succ j ih => rw [Function.iterate_succ_apply', hnd, ih]
  have hchain : ∀ j : ℕ, j ≤ Nat.find hex → b (nx s) = b (nx^[j] (nx s)) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have h2 := hcon (nx^[j] (nx s)) (hmin j (by omega)) (hnodeIter j)
      rw [Function.iterate_succ_apply', ← h2]
      exact ih (by omega)
  have h3 := hchain (Nat.find hex) le_rfl
  rw [hk₀spec] at h3
  exact hs h3.symm

end Cycle

section Combinatorics

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n]

/-- **B1.**  A labelling `β` of the slots of the cactus of `F` (`KLIsTSP F`, `2 ≤ n`) whose leaf labels `β (leaf v)` are not
all equal has either a chord `J` with `β (In J) ≠ β (Out J)`, or a node with two distinct `M`-edges `s — next s` with unequal
ends.  If every chord and every node cycle (`BAnextSlot_orbit`) had equal ends then every edge would, the total length is
`0` and `baSlot_path_le` makes `β` constant.  An unequal `M`-edge is never alone in its node: a cycle closes. -/
theorem KSumZeroB_unequal_edge {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n)
    (β : BAslot F → Zd d L) (hnc : ∃ v w : Fin n, β (BAslotLeaf F v) ≠ β (BAslotLeaf F w)) :
    (∃ J : ↥F, β (BAslotIn F J) ≠ β (BAslotOut F J)) ∨
      ∃ s s' : BAslot F, s ≠ s' ∧ BAslotNode F s = BAslotNode F s' ∧
        β s ≠ β (BAnextSlot F s) ∧ β s' ≠ β (BAnextSlot F s') := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hch, hM⟩ := hcon
  have hnext : ∀ s, β s = β (BAnextSlot F s) := by
    intro s
    by_contra hs
    obtain ⟨s', hne, hnd, hs'⟩ := KSumZeroB_cycle (BAnextSlot F) (BAslotNode F) (BAslotNode_nextSlot F)
      (fun s t h => (BAnextSlot_orbit hF hn s t).1 h) β hs
    exact hs (hM s' s hne hnd hs')
  have hall : ∀ s t : BAslot F, β s = β t := by
    intro s t
    have h := baSlot_path_le hF hn β s t
    have hz : ∑ e : ↥F ⊕ BAslot F, zdistD d L (β (BACactusValSrc F e) - β (BACactusValTgt F e)) = 0 := by
      refine Finset.sum_eq_zero fun e _ => ?_
      rcases e with J | s
      · change zdistD d L (β (BAslotIn F J) - β (BAslotOut F J)) = 0
        rw [hch J, sub_self, zdistD_zero]
      · change zdistD d L (β s - β (BAnextSlot F s)) = 0
        rw [← hnext s, sub_self, zdistD_zero]
    rw [hz] at h
    exact sub_eq_zero.1 ((zdistD_eq_zero_iff d L).1 (Nat.le_zero.1 h))
  obtain ⟨v, w, hvw⟩ := hnc
  exact hvw (hall _ _)

end Combinatorics

end RBM.BA
