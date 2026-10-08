/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LocalRegular6d
import RBM3D.Graph.LWExpTerm5

/-!
# LW engine (T2332): the `m`-free `lem:localregular`

The expansion lists of `lw_localregular` (`LocalRegular6d.lean:1107`) are chosen after the
parameter `m`; the moment bound `lem:LW_moment` needs one list for the random `m`-dependence of
the data.  This file proves the `m`-free form `lw_localregularX`: one pair of tagged lists
`outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2))` whose evaluation `lwEvX m` (the coefficient times
`m^j m̄^{j'}`) satisfies, for every `m ≠ 0`, the six conjuncts of `lw_localregular`
(`LWLocRegConcl`) and has at least `p` black waved edges (T2297's invariant `nWS ≥ p`).

## Contents (namespace `RBM.Graph`; helpers `lwEngine_*`)

1. Definitions: `lwEvX`, `LWLocRegConcl` (the check file's text), the tag algebra
   (`lwEngine_ev3`, `lwEngine_sw`, `lwEngine_shift`).
2. Scaling of the coefficient (`lwEngine_sc`): `partitionX (sc k Δ) = (partitionX Δ).map (scale k)`;
   `LGraph.partition m` is `partitionX` evaluated at `m` (`lwEngine_partition_eq`); a block of
   tagged terms evaluates to the partition of the scaled term (`lwEngine_blk_nat`).
3. The 13 term constructors of the three rules (twists `(c, t)` included) are linear in the
   coefficient with a monomial in `m, m̄`: `lwEngine_T1 … lwEngine_R8`, `lwEngine_Ds`.
4. The `X`-generators `lvl1WeightOutsX`, `lvl1EdgeOutsX`, `lvl1GGOutsX` (tags `+(1,0)` for `m`,
   `+(3,0)` for `m³`, `(1,1)` and `(2,0)` for the loop terms of `oe1xDs`, swapped under
   conjugation), their naturality
   `lvl1…Outs0 m (sc (m^j m̄^{j'}) Γ) = ((lvl1…OutsX Γ).map (shift (j,j'))).map (ev m)`,
   `LocStepX`, `LocStepX.eval`.
5. Black waved edges: `lw_nWS_ge`.
6. The recursion `lwEngine_exists` (WF on `Lvl1Mu K`, mirroring `lvl1_exists_aux`), its transport
   to `LWLocRegConcl`, and `lw_localregularX`.
7. Compiled instances (`RBM.Graph.LWEngineInst`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green RBM.Graph

namespace RBM.Graph

/-! ## 1. Definitions -/

/-- Evaluation of a tagged graph at `m`: the coefficient multiplied by `m^j m̄^{j'}` (as `PartitionXSpec`). -/
def lwEvX (m : ℂ) (r : (ℕ × ℕ) × PGraph (Fin 2)) : PGraph (Fin 2) :=
  { r.2 with g := { r.2.g with coeff := m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff } }

/-- The conclusion of `lw_localregular` (`LocalRegular6d.lean:1110-1129`) for given lists, word for word. -/
def LWLocRegConcl (p : ℕ) (m : ℂ) (c : ℝ) (K0 d : ℕ) (D : ℝ) (outs errs : List (PGraph (Fin 2))) : Prop :=
  (∀ Q ∈ outs, Q.g.LocStd ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder) ∧
  (∀ Q ∈ errs, ∀ (W L : ℕ) (Ψ : ℝ), 1 ≤ W → 1 ≤ L → (L : ℝ) ^ d ≤ (W : ℝ) ^ K0 →
    (W : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ → Ψ ≤ (W : ℝ) ^ (-c) → Q.g.scalingSize Ψ W d L ≤ (W : ℝ) ^ (-D)) ∧
  (∀ Q ∈ outs ++ errs, Lvl1Reach m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack Q ∧
    Q.g.Normal ∧ (fxyPowGraph p).pack.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
    (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW) ∧
  (∀ {sz : Sizes d} {n : ℕ} {z : ℂ} {u : ℝ}
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ),
    GaussIBP sz → 0 < z.im → 0 < u → m ≠ 0 → z + (u : ℂ) * m = -m⁻¹ →
    (∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j) → Spᵀ = Sp →
    (∀ a, M a a = m) → (∀ a b, a ≠ b → M a b = 0) → ∀ ℓe : Fin 2 → Idx d (sz.L n) (sz.W n),
      ∫ ω, (fxyPowGraph p).pack.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
        (outs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
        (errs.map fun Q => ∫ ω, Q.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum) ∧
  (∀ Q ∈ outs, Q.LocReg1 ∧ Q.LocReg2 p ∧ Q.LocReg345 p ∧ Q.LocReg6 p ∧
    (Q.ext 0 ≠ Q.ext 1 → 3 * (p : ℤ) ≤ Q.g.scalingOrder))

/-- the evaluation of a tagged packed graph over any external type (`lwEvX` is the case `Fin 2`) -/
def lwEngine_ev {E0 : Type} (m : ℂ) (r : (ℕ × ℕ) × PGraph E0) : PGraph E0 :=
  { r.2 with g := { r.2.g with coeff := m ^ r.1.1 * star m ^ r.1.2 * r.2.g.coeff } }

theorem lwEngine_evX_eq (m : ℂ) (r : (ℕ × ℕ) × PGraph (Fin 2)) : lwEvX m r = lwEngine_ev m r := rfl

/-- the scalar `m^j m̄^{j'}` of a tag `(j, j')` -/
def lwEngine_ev3 (m : ℂ) (t : ℕ × ℕ) : ℂ := m ^ t.1 * star m ^ t.2

theorem lwEngine_ev3_add (m : ℂ) (u v : ℕ × ℕ) :
    lwEngine_ev3 m (u + v) = lwEngine_ev3 m u * lwEngine_ev3 m v := by
  simp only [lwEngine_ev3, Prod.fst_add, Prod.snd_add, pow_add]; ring

/-- the tag of a term under the twist `(c, t)`: `m ↔ m̄` when `c` conjugates -/
def lwEngine_sw (c : Bool) (a : ℕ × ℕ) : ℕ × ℕ := cond c (a.2, a.1) a

/-- raise every tag by `u` -/
def lwEngine_shift {E0 : Type} (u : ℕ × ℕ) (r : (ℕ × ℕ) × PGraph E0) : (ℕ × ℕ) × PGraph E0 := (u + r.1, r.2)

/-- the coefficient of a graph multiplied by `k` -/
def lwEngine_sc {E I : Type*} (k : ℂ) (Γ : LGraph E I) : LGraph E I := { Γ with coeff := k * Γ.coeff }

/-- the coefficient of a packed graph multiplied by `k` -/
def lwEngine_scP {E0 : Type} (k : ℂ) (P : PGraph E0) : PGraph E0 := { P with g := lwEngine_sc k P.g }

theorem lwEngine_ext {E I : Type*} {Γ Δ : LGraph E I} (h1 : Γ.solid = Δ.solid) (h2 : Γ.waved = Δ.waved)
    (h3 : Γ.dotted = Δ.dotted) (h4 : Γ.coeff = Δ.coeff) : Γ = Δ := by
  cases Γ; cases Δ; simp_all

theorem lwEngine_ev_sc {E0 : Type} (m : ℂ) (w t : ℕ × ℕ) (P : PGraph E0) :
    lwEngine_ev m (t, lwEngine_scP (lwEngine_ev3 m w) P) = lwEngine_ev m (w + t, P) := by
  unfold lwEngine_ev lwEngine_scP lwEngine_sc lwEngine_ev3
  simp only [Prod.fst_add, Prod.snd_add, pow_add]
  congr 2
  ring

theorem lwEngine_ev_zero {E0 : Type} (m : ℂ) (P : PGraph E0) (h : P.g.coeff = 1) :
    lwEngine_ev m ((0, 0), P) = P := by
  cases P with
  | mk E' I' ext ext_surj g =>
    cases g with
    | mk s w d c =>
      simp only at h
      subst h
      simp [lwEngine_ev]

theorem lwEngine_map_shift_zero {E0 : Type} (m : ℂ) (L : List ((ℕ × ℕ) × PGraph E0)) :
    (L.map (lwEngine_shift 0)).map (lwEngine_ev m) = L.map (lwEngine_ev m) := by
  rw [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [lwEngine_shift]

/-! ## 2. The partition of a scaled term -/

section Partition

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem lwEngine_dotChoices_sc (k : ℂ) (Δ : LGraph E I) : (lwEngine_sc k Δ).dotChoices = Δ.dotChoices := rfl

theorem lwEngine_withDots_sc (k : ℂ) (Δ : LGraph E I) (c : ℤ × List (DEdge (E ⊕ I))) :
    (lwEngine_sc k Δ).withDots c = lwEngine_sc k (Δ.withDots c) :=
  lwEngine_ext rfl rfl rfl (by simp [LGraph.withDots, lwEngine_sc]; ring)

theorem lwEngine_partitionTerms_sc (k : ℂ) (Δ : LGraph E I) :
    (lwEngine_sc k Δ).partitionTerms = Δ.partitionTerms.map (lwEngine_sc k) := by
  have hw : (lwEngine_sc k Δ).withDots = lwEngine_sc k ∘ Δ.withDots := funext (lwEngine_withDots_sc k Δ)
  unfold LGraph.partitionTerms
  simp only [lwEngine_dotChoices_sc, List.filter_map, List.map_map]
  rw [hw]
  rfl

/-- **The exponent-tracking partition of a scaled graph** is the scaled exponent-tracking partition. -/
theorem lwEngine_partitionX_sc (k : ℂ) (Δ : LGraph E I) :
    Sizes.partitionX (lwEngine_sc k Δ) = (Sizes.partitionX Δ).map (fun r => (r.1, lwEngine_scP k r.2)) := by
  unfold Sizes.partitionX
  rw [lwEngine_partitionTerms_sc, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun Δ' _ => ?_
  rw [List.map_map]
  rfl

/-- `LGraph.partition` is the exponent-tracking partition evaluated at `m` (`lwExpTerm5_partition_eq`, private there). -/
theorem lwEngine_partition_eq (m : ℂ) (Γ : LGraph E I) :
    Γ.partition m = (Sizes.partitionX Γ).map (lwEngine_ev m) := by
  unfold LGraph.partition Sizes.partitionX
  rw [List.map_flatMap]
  refine List.flatMap_congr fun Δ _ => ?_
  unfold LGraph.mergeSplitP LGraph.splitWeights
  rw [Sizes.lwSplitLoopsX_spec m Δ.merge.solid]
  simp only [List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp [lwEngine_ev]

/-- the block of an expansion term: the exponent-tracking partition of the term at `m = 1`, every tag raised by `u` -/
def lwEngine_blk (u : ℕ × ℕ) (Y : LGraph E I) : List ((ℕ × ℕ) × PGraph E) :=
  (Sizes.partitionX Y).map (lwEngine_shift u)

/-- **A block evaluates to the partition of the scaled term**: the term `Y` (at `m = 1`) times `m^{u₁} m̄^{u₂}` times the
scalar `m^{t₀₁} m̄^{t₀₂}` of the input tag has the partition `((blk u Y).map (shift t₀)).map (ev m)`. -/
theorem lwEngine_blk_nat (m : ℂ) (t0 u : ℕ × ℕ) (Y : LGraph E I) :
    (lwEngine_sc (lwEngine_ev3 m u * lwEngine_ev3 m t0) Y).partition m =
      ((lwEngine_blk u Y).map (lwEngine_shift t0)).map (lwEngine_ev m) := by
  rw [mul_comm, ← lwEngine_ev3_add, lwEngine_partition_eq, lwEngine_partitionX_sc]
  simp only [lwEngine_blk, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, lwEngine_shift]
  rw [lwEngine_ev_sc, add_assoc]

end Partition

/-! ## 3. The term constructors are linear in the coefficient, with a monomial in `m, m̄`

Every graph of a step is `lwSymmTwistG c t (B m F …)`, with the frame `F` of the input twisted by `(c, t)` and `B m F …` an
`owxExt` whose coefficient is `m`, `m³`, `m m̄` or `m²` times that of `F` (`LWWeightExp.lean:658-697`, `LWEdgeExp.lean:606-1116`,
`LWGGExp.lean:485-536`); the twist `(c, t)` conjugates the coefficient when `c`.  So at the coefficient `κ` of the input, the
output at `m` is the output at `m = 1` with the coefficient multiplied by `m^a m̄^b κ` (`(a, b)` swapped when `c`). -/

section Gens

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

set_option hygiene false in
/-- the proof of the constructor lemmas: the three edge lists agree by `rfl` for each twist, and the coefficient by a ring
identity (the twist conjugates the coefficient for `c`). -/
local macro "lwEngine_gen" : tactic => `(tactic|
  (cases c <;> cases t <;> refine lwEngine_ext rfl rfl rfl ?_ <;>
   simp [lwSymmTwistG, LGraph.conj, LGraph.transpose, lwEngine_sc, lwEngine_ev3, lwEngine_sw, LGraph.owxExt,
     lwSymmOwxT1, lwSymmOwxT2, lwSymmOwxT3, lwSymmOwxT4, owxET1, owxET2, owxET3, owxET4,
     lwSymmOe1xOwx, owxT1, lwSymmFrame, lwSymmFrame2, lwSymmUncirc, lwSymmUncirc2,
     lwSymmOe2xR2, lwSymmOe2xR3, lwSymmOe2xR4, lwSymmOe2xR5, lwSymmOe2xR6, lwSymmOe2xR7, lwSymmOe2xR8,
     oe2xR2, oe2xR4, oe2xR5, oe2xR6, oe2xR7, oe2xR8] <;> ring))

/-- term 1 of `(Owx)` (`m`): tag `(1, 0)` -/
theorem lwEngine_T1 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (x : E ⊕ I) :
    lwSymmOwxT1 c t m (lwEngine_sc κ Γ) x =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOwxT1 c t 1 Γ x) := by
  lwEngine_gen

/-- term 2 of `(Owx)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_T2 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I) :
    lwSymmOwxT2 c t m (lwEngine_sc κ Γ) p x =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOwxT2 c t 1 Γ p x) := by
  lwEngine_gen

/-- term 3 of `(Owx)` (`m`): tag `(1, 0)` -/
theorem lwEngine_T3 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmOwxT3 c t m (lwEngine_sc κ Γ) x q =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOwxT3 c t 1 Γ x q) := by
  lwEngine_gen

/-- term 4 of `(Owx)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_T4 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmOwxT4 c t m (lwEngine_sc κ Γ) x q =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOwxT4 c t 1 Γ x q) := by
  lwEngine_gen

/-- the term `m Σ_α S_{xα} Ǧ_{αα} 𝒢` of `(Oe1x)` (`m`): tag `(1, 0)` -/
theorem lwEngine_Oe1xOwx (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    lwSymmOe1xOwx c t m (lwEngine_sc κ Γ) p x =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOe1xOwx c t 1 Γ p x) := by
  lwEngine_gen

/-- `R2` of `(Oe2x)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_R2 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) :
    lwSymmOe2xR2 c t m (lwEngine_sc κ Γ) p q x y y' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOe2xR2 c t 1 Γ p q x y y') := by
  lwEngine_gen

/-- `R3` of `(Oe2x)` (`m`): tag `(1, 0)` -/
theorem lwEngine_R3 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    lwSymmOe2xR3 c t m (lwEngine_sc κ Γ) p q x =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOe2xR3 c t 1 Γ p q x) := by
  lwEngine_gen

/-- `R4` of `(Oe2x)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_R4 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) :
    lwSymmOe2xR4 c t m (lwEngine_sc κ Γ) p q x y y' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOe2xR4 c t 1 Γ p q x y y') := by
  lwEngine_gen

/-- `R5` of `(Oe2x)` (`m`): tag `(1, 0)` -/
theorem lwEngine_R5 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) :
    lwSymmOe2xR5 c t m (lwEngine_sc κ Γ) p q x y y' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOe2xR5 c t 1 Γ p q x y y') := by
  lwEngine_gen

/-- `R6` of `(Oe2x)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_R6 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) :
    lwSymmOe2xR6 c t m (lwEngine_sc κ Γ) p q x y y' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOe2xR6 c t 1 Γ p q x y y') := by
  lwEngine_gen

/-- `R7` of `(Oe2x)` (`m`): tag `(1, 0)` -/
theorem lwEngine_R7 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmOe2xR7 c t m (lwEngine_sc κ Γ) p q x y y' q' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (1, 0)) * κ) (lwSymmOe2xR7 c t 1 Γ p q x y y' q') := by
  lwEngine_gen

/-- `R8` of `(Oe2x)` (`m³`): tag `(3, 0)` -/
theorem lwEngine_R8 (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmOe2xR8 c t m (lwEngine_sc κ Γ) p q x y y' q' =
      lwEngine_sc (lwEngine_ev3 m (lwEngine_sw c (3, 0)) * κ) (lwSymmOe2xR8 c t 1 Γ p q x y y' q') := by
  lwEngine_gen

/-- **The derivative terms of `(Oe1x)` (`oe1xDs`) with their exponent tags** (at `m = 1`): the loop terms `oe1xP3`
(`m m̄`) and `oe1xP4` (`m²`) carry `(1, 1)` and `(2, 0)`, every other term `m`, `(1, 0)`. -/
def lwEngine_oe1xDsX (Γ : LGraph E I) (x : I) (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    List ((ℕ × ℕ) × LGraph E (I ⊕ Fin 1)) :=
  if q.1.σ = false ∧ q.1.src = Sum.inr x then [((1, 0), oe1xP5 1 Γ x v q), ((1, 1), oe1xP3 1 Γ x v q)]
  else if q.1.σ = true ∧ q.1.dst = Sum.inr x then [((1, 0), oe1xP6 1 Γ x v q), ((2, 0), oe1xP4 1 Γ x v q)]
  else [((1, 0), oe1xD 1 Γ x v q)]

/-- the derivative terms of the twisted rule (`lwSymmOe1xDs`) at `m = 1`, with their tags (swapped when `c`) -/
def lwEngine_DsX (c t : Bool) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) (v : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List ((ℕ × ℕ) × LGraph E (I ⊕ Fin 1)) :=
  (lwEngine_oe1xDsX (lwSymmFrame c t Γ p) x v (lwSymmTwistP c t q)).map
    (fun r => (lwEngine_sw c r.1, lwSymmTwistG c t r.2))

set_option hygiene false in
/-- the derivative terms of `(Oe1x)`: the list at the coefficient `κ` is the list at `m = 1` scaled by `m^a m̄^b κ`, term by term -/
theorem lwEngine_Ds (c t : Bool) (m κ : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwSymmOe1xDs c t m (lwEngine_sc κ Γ) p x v q =
      (lwEngine_DsX c t Γ p x v q).map (fun r => lwEngine_sc (lwEngine_ev3 m r.1 * κ) r.2) := by
  unfold lwSymmOe1xDs lwEngine_DsX lwEngine_oe1xDsX oe1xDs
  split_ifs <;> simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] <;>
  (try constructor) <;>
  (cases c <;> cases t <;> refine lwEngine_ext rfl rfl rfl ?_ <;>
   simp [lwSymmTwistG, LGraph.conj, LGraph.transpose, lwEngine_sc, lwEngine_ev3, lwEngine_sw, LGraph.owxExt,
     lwSymmFrame, lwSymmUncirc, oe1xP5, oe1xP3, oe1xP6, oe1xP4, oe1xD] <;> ring)

end Gens

/-! ## 4. The `X`-generators of the three rules, their naturality, `LocStepX` -/

section XGen

variable {E' I' : Type} [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I']

/-- **Step 1 of `strat_local` on the exponent-tracking carrier** (`lvl1WeightOuts0`): the four terms of `(Owx)` at the
light-weight `p.1` at `x`, each followed by the exponent-tracking dotted edge partition; the tags are `(1, 0)` for `m` (terms 1, 3),
`(3, 0)` for `m³` (terms 2, 4), swapped under conjugation. -/
def lvl1WeightOutsX (Γ : LGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : E' ⊕ I') (c t : Bool) :
    List ((ℕ × ℕ) × PGraph E') :=
  lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOwxT1 c t 1 Γ x) ++
    lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOwxT2 c t 1 Γ p x) ++
    (lwSplit p.2).flatMap (fun q => lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOwxT3 c t 1 Γ x q)) ++
    (lwSplit p.2).flatMap (fun q => lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOwxT4 c t 1 Γ x q))

/-- **Step 2 of `strat_local` on the exponent-tracking carrier** (`lvl1EdgeOuts0`): the tags `(1, 0)` for `m`, `(1, 1)` and
`(2, 0)` for the loop terms `oe1xP3` (`m m̄`), `oe1xP4` (`m²`) of the derivative terms (`lwEngine_DsX`). -/
def lvl1EdgeOutsX (Γ : LGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (v : E' ⊕ I')
    (c t : Bool) : List ((ℕ × ℕ) × PGraph E') :=
  lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOe1xOwx c t 1 Γ p x) ++
    (lwSplit p.2).flatMap (fun q => (lwEngine_DsX c t Γ p x v q).flatMap (fun r => lwEngine_blk r.1 r.2))

/-- **Step 3 of `strat_local` on the exponent-tracking carrier** (`lvl1GGOuts0`): `m³` for `R2, R4, R6, R8`, `m` for
`R3, R5, R7`, swapped under conjugation. -/
def lvl1GGOutsX (Γ : LGraph E' I') (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I'))) (x : I') (y y' : E' ⊕ I')
    (c t : Bool) : List ((ℕ × ℕ) × PGraph E') :=
  lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOe2xR2 c t 1 Γ p q x y y') ++
    lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOe2xR3 c t 1 Γ p q x) ++
    lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOe2xR4 c t 1 Γ p q x y y') ++
    lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOe2xR5 c t 1 Γ p q x y y') ++
    lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOe2xR6 c t 1 Γ p q x y y') ++
    (lwSplit q.2).flatMap (fun q' => lwEngine_blk (lwEngine_sw c (1, 0)) (lwSymmOe2xR7 c t 1 Γ p q x y y' q')) ++
    (lwSplit q.2).flatMap (fun q' => lwEngine_blk (lwEngine_sw c (3, 0)) (lwSymmOe2xR8 c t 1 Γ p q x y y' q'))

/-- **Naturality of Step 1**: at the input coefficient `m^j m̄^{j'}`, the outputs at `m` are the `X`-outputs with the input tag
`(j, j')` added, evaluated at `m`. -/
theorem lvl1WeightOuts0_nat (m : ℂ) (t0 : ℕ × ℕ) (Γ : LGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I')))
    (x : E' ⊕ I') (c t : Bool) :
    lvl1WeightOuts0 m (lwEngine_sc (lwEngine_ev3 m t0) Γ) p x c t =
      ((lvl1WeightOutsX Γ p x c t).map (lwEngine_shift t0)).map (lwEngine_ev m) := by
  unfold lvl1WeightOuts0 lvl1WeightOutsX
  simp only [lwEngine_T1, lwEngine_T2, lwEngine_T3, lwEngine_T4, lwEngine_blk_nat, List.map_append, List.map_flatMap]

/-- **Naturality of Step 2**. -/
theorem lvl1EdgeOuts0_nat (m : ℂ) (t0 : ℕ × ℕ) (Γ : LGraph E' I') (p : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I')))
    (x : I') (v : E' ⊕ I') (c t : Bool) :
    lvl1EdgeOuts0 m (lwEngine_sc (lwEngine_ev3 m t0) Γ) p x v c t =
      ((lvl1EdgeOutsX Γ p x v c t).map (lwEngine_shift t0)).map (lwEngine_ev m) := by
  unfold lvl1EdgeOuts0 lvl1EdgeOutsX
  simp only [lwEngine_Oe1xOwx, lwEngine_Ds, lwEngine_blk_nat, List.map_append, List.map_flatMap, List.flatMap_map]

/-- **Naturality of Step 3**. -/
theorem lvl1GGOuts0_nat (m : ℂ) (t0 : ℕ × ℕ) (Γ : LGraph E' I') (p q : SEdge (E' ⊕ I') × List (SEdge (E' ⊕ I')))
    (x : I') (y y' : E' ⊕ I') (c t : Bool) :
    lvl1GGOuts0 m (lwEngine_sc (lwEngine_ev3 m t0) Γ) p q x y y' c t =
      ((lvl1GGOutsX Γ p q x y y' c t).map (lwEngine_shift t0)).map (lwEngine_ev m) := by
  unfold lvl1GGOuts0 lvl1GGOutsX
  simp only [lwEngine_R2, lwEngine_R3, lwEngine_R4, lwEngine_R5, lwEngine_R6, lwEngine_R7, lwEngine_R8,
    lwEngine_blk_nat, List.map_append, List.map_flatMap]

end XGen

section StepX

/-- the `X`-outputs of a step, packed over the external vertices of the input (`lvl1Pack` on the carrier) -/
def lvl1PackX {E : Type} (P : PGraph E) (L : List ((ℕ × ℕ) × PGraph P.E')) : List ((ℕ × ℕ) × PGraph E) :=
  L.map fun r => (r.1, r.2.lvl1Comp P.ext P.ext_surj)

/-- **One step of `strat_local` on the exponent-tracking carrier**: the three constructors of `LocStep` (the hypotheses do not
mention `m`), with the lists `lvl1WeightOutsX`, `lvl1EdgeOutsX`, `lvl1GGOutsX` of tagged outputs. -/
inductive LocStepX : PGraph (Fin 2) → List ((ℕ × ℕ) × PGraph (Fin 2)) → Prop
  | weight (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.E' ⊕ P.I') (c t : Bool) (hx : lwSymmTwistS c t p.1 = ⟨true, true, x, x⟩) :
      LocStepX P (lvl1PackX P (lvl1WeightOutsX P.g p x c t))
  | edge (P : PGraph (Fin 2)) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (x : P.I') (v : P.E' ⊕ P.I') (hv : v ≠ Sum.inr x) (c t : Bool)
      (hx : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, v⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hbad : P.g.lvl1DegAt (Sum.inr x) ≠ 0 ∧ (P.g.lvl1DegAt (Sum.inr x) ≠ 2 ∨ P.g.lvl1ChargeAt (Sum.inr x) ≠ 0)) :
      LocStepX P (lvl1PackX P (lvl1EdgeOutsX P.g p x v c t))
  | gg (P : PGraph (Fin 2)) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I'))) (hp : p ∈ lwSplit P.g.solid)
      (hq : q ∈ lwSplit p.2) (x : P.I') (y y' : P.E' ⊕ P.I') (hy : y ≠ Sum.inr x) (c t : Bool)
      (hp1 : lwSymmTwistS c t p.1 = ⟨true, p.1.circ, Sum.inr x, y⟩)
      (hq1 : lwSymmTwistS c t q.1 = ⟨true, q.1.circ, y', Sum.inr x⟩) (hwf : ∀ e ∈ P.g.solid, e.src ≠ e.dst)
      (hnb : ∀ i : P.I', P.g.lvl1DegAt (Sum.inr i) = 0 ∨ (P.g.lvl1DegAt (Sum.inr i) = 2 ∧ P.g.lvl1ChargeAt (Sum.inr i) = 0)) :
      LocStepX P (lvl1PackX P (lvl1GGOutsX P.g p q x y y' c t))

/-- packing commutes with the evaluation of the tags -/
theorem lwEngine_packX_nat (m : ℂ) (t0 : ℕ × ℕ) (P : PGraph (Fin 2)) (L : List ((ℕ × ℕ) × PGraph P.E')) :
    lvl1Pack (lwEvX m (t0, P)) ((L.map (lwEngine_shift t0)).map (lwEngine_ev (E0 := P.E') m)) =
      ((lvl1PackX P L).map (lwEngine_shift t0)).map (lwEvX m) := by
  change List.map (fun Q : PGraph P.E' => Q.lvl1Comp P.ext P.ext_surj)
    ((L.map (lwEngine_shift t0)).map (lwEngine_ev (E0 := P.E') m)) = _
  simp only [lvl1PackX, List.map_map]
  exact List.map_congr_left fun r _ => rfl

/-- **`LocStepX` is `LocStep` at every `m`**: the `X`-outputs of a step, with the tag `t₀` of the input added and evaluated at `m`,
are the outputs of the step `LocStep m` of the evaluated input (naturality of the three rules). -/
theorem LocStepX.eval {P : PGraph (Fin 2)} {LX : List ((ℕ × ℕ) × PGraph (Fin 2))} (h : LocStepX P LX) (m : ℂ)
    (t0 : ℕ × ℕ) : LocStep m (lwEvX m (t0, P)) ((LX.map (lwEngine_shift t0)).map (lwEvX m)) := by
  cases h with
  | weight p hp x c t hx =>
    have key : LocStep m (lwEvX m (t0, P))
        (lvl1Pack (lwEvX m (t0, P)) (lvl1WeightOuts0 (E' := P.E') (I' := P.I') m (lwEngine_sc (lwEngine_ev3 m t0) P.g) p x c t)) :=
      LocStep.weight (lwEvX m (t0, P)) p hp x c t hx
    have e := (congrArg (lvl1Pack (lwEvX m (t0, P))) (lvl1WeightOuts0_nat m t0 P.g p x c t)).trans
      (lwEngine_packX_nat m t0 P (lvl1WeightOutsX P.g p x c t))
    rw [e] at key
    exact key
  | edge p hp x v hv c t hx hwf hbad =>
    have key : LocStep m (lwEvX m (t0, P))
        (lvl1Pack (lwEvX m (t0, P)) (lvl1EdgeOuts0 (E' := P.E') (I' := P.I') m (lwEngine_sc (lwEngine_ev3 m t0) P.g) p x v c t)) :=
      LocStep.edge (lwEvX m (t0, P)) p hp x v hv c t hx hwf hbad
    have e := (congrArg (lvl1Pack (lwEvX m (t0, P))) (lvl1EdgeOuts0_nat m t0 P.g p x v c t)).trans
      (lwEngine_packX_nat m t0 P (lvl1EdgeOutsX P.g p x v c t))
    rw [e] at key
    exact key
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    have key : LocStep m (lwEvX m (t0, P))
        (lvl1Pack (lwEvX m (t0, P)) (lvl1GGOuts0 (E' := P.E') (I' := P.I') m (lwEngine_sc (lwEngine_ev3 m t0) P.g) p q x y y' c t)) :=
      LocStep.gg (lwEvX m (t0, P)) p q hp hq x y y' hy c t hp1 hq1 hwf hnb
    have e := (congrArg (lvl1Pack (lwEvX m (t0, P))) (lvl1GGOuts0_nat m t0 P.g p q x y y' c t)).trans
      (lwEngine_packX_nat m t0 P (lvl1GGOutsX P.g p q x y y' c t))
    rw [e] at key
    exact key

/-- **`LocStepX` at the tag `0`**: for an input of coefficient `1` the evaluated `X`-outputs are the outputs of `LocStep m`. -/
theorem LocStepX.eval_one {P : PGraph (Fin 2)} {LX : List ((ℕ × ℕ) × PGraph (Fin 2))} (h : LocStepX P LX)
    (hP : P.g.coeff = 1) (m : ℂ) : LocStep m P (LX.map (lwEvX m)) := by
  have := h.eval m 0
  rwa [show lwEvX m (0, P) = P from lwEngine_ev_zero m P hP,
    show (LX.map (lwEngine_shift 0)).map (lwEvX m) = LX.map (lwEvX m) from lwEngine_map_shift_zero m LX] at this

/-- **Step selection on the carrier**: a normal graph that is not locally standard has a step `LocStepX` (the selection
`lvl1_exists_step` reads no coefficient). -/
theorem lwEngine_exists_stepX (P : PGraph (Fin 2)) (hN : P.g.Normal) (hn : ¬ P.g.LocStd) :
    ∃ LX, LocStepX P LX := by
  obtain ⟨outs, hst⟩ := lvl1_exists_step 1 P hN hn
  cases hst with
  | weight p hp x c t hx => exact ⟨_, LocStepX.weight P p hp x c t hx⟩
  | edge p hp x v hv c t hx hwf hbad => exact ⟨_, LocStepX.edge P p hp x v hv c t hx hwf hbad⟩
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb => exact ⟨_, LocStepX.gg P p q hp hq x y y' hy c t hp1 hq1 hwf hnb⟩

end StepX

/-! ## 5. Black waved edges: `nWS ≥ p` along `Lvl1Reach` (T2297's invariant S1)

Every term of the three rules keeps the waved edges of the input (`owxExt` appends, the frame and the twists map them keeping the
colour, `merge` maps them) and only appends waved edges; so the number of black ones does not fall. -/

section NWS

/-- the number of black waved edges of a graph -/
def lwEngine_nWS {E I : Type*} (Γ : LGraph E I) : ℕ := Γ.waved.countP (fun e => !e.col)

theorem lwEngine_col_conj {V : Type*} (e : WEdge V) : (WEdge.conj e).col = e.col := by
  cases h : e.col <;> simp [WEdge.conj, h]

theorem lwEngine_col_transpose {V : Type*} (e : WEdge V) : (WEdge.transpose e).col = e.col := rfl

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

set_option hygiene false in
/-- the proof of the monotonicity lemmas below: every list of waved edges is mapped by colour-keeping maps and appended to -/
local macro "lwEngine_nws" : tactic => `(tactic|
  (cases c <;> cases t <;>
   simp [lwEngine_nWS, lwSymmTwistG, LGraph.conj, LGraph.transpose, LGraph.owxExt, List.countP_append, List.countP_map,
     Function.comp_def, lwEngine_col_conj, lwEngine_col_transpose, WEdge.map,
     lwSymmOwxT1, lwSymmOwxT2, lwSymmOwxT3, lwSymmOwxT4, owxET1, owxET2, owxET3, owxET4,
     lwSymmOe1xOwx, owxT1, lwSymmFrame, lwSymmFrame2, lwSymmUncirc, lwSymmUncirc2,
     lwSymmOe2xR2, lwSymmOe2xR3, lwSymmOe2xR4, lwSymmOe2xR5, lwSymmOe2xR6, lwSymmOe2xR7, lwSymmOe2xR8,
     oe2xR2, oe2xR4, oe2xR5, oe2xR6, oe2xR7, oe2xR8, oe1xP5, oe1xP3, oe1xP6, oe1xP4, oe1xD]))

theorem lwEngine_T1_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOwxT1 c t m Γ x) := by
  lwEngine_nws

theorem lwEngine_T2_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : E ⊕ I) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOwxT2 c t m Γ p x) := by
  lwEngine_nws

theorem lwEngine_T3_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOwxT3 c t m Γ x q) := by
  lwEngine_nws

theorem lwEngine_T4_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (x : E ⊕ I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOwxT4 c t m Γ x q) := by
  lwEngine_nws

theorem lwEngine_Oe1xOwx_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe1xOwx c t m Γ p x) := by
  lwEngine_nws

theorem lwEngine_Ds_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (v : E ⊕ I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    ∀ T ∈ lwSymmOe1xDs c t m Γ p x v q, lwEngine_nWS Γ ≤ lwEngine_nWS T := by
  intro T hT
  obtain ⟨T0, hT0, rfl⟩ := List.mem_map.1 hT
  unfold oe1xDs at hT0
  split_ifs at hT0 <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hT0 <;>
  (try rcases hT0 with rfl | rfl) <;> lwEngine_nws

theorem lwEngine_R2_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR2 c t m Γ p q x y y') := by
  lwEngine_nws

theorem lwEngine_R3_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR3 c t m Γ p q x) := by
  lwEngine_nws

theorem lwEngine_R4_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR4 c t m Γ p q x y y') := by
  lwEngine_nws

theorem lwEngine_R5_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR5 c t m Γ p q x y y') := by
  lwEngine_nws

theorem lwEngine_R6_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) : lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR6 c t m Γ p q x y y') := by
  lwEngine_nws

theorem lwEngine_R7_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR7 c t m Γ p q x y y' q') := by
  lwEngine_nws

theorem lwEngine_R8_nWS (c t : Bool) (m : ℂ) (Γ : LGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I)
    (y y' : E ⊕ I) (q' : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    lwEngine_nWS Γ ≤ lwEngine_nWS (lwSymmOe2xR8 c t m Γ p q x y y' q') := by
  lwEngine_nws

/-- **The packed outputs of a term have the black waved edges of the term**: `waved` of a graph of the partition is the mapped
`waved` of the term (`lvl1_part_struct`), and the maps keep the colour. -/
theorem lwEngine_part_nWS (m : ℂ) (Y : LGraph E I) (Q : PGraph E) (hQ : Q ∈ Y.partition m) :
    lwEngine_nWS Y = lwEngine_nWS Q.g := by
  obtain ⟨vm, -, -, -, -, -, hw, -⟩ := lvl1_part_struct m Y Q hQ
  simp [lwEngine_nWS, hw, List.countP_map, Function.comp_def, WEdge.map]

/-- **A step does not lower the number of black waved edges** (the 17 terms of the three rules). -/
theorem lwEngine_locStep_nWS {E : Type} {m : ℂ} {P : PGraph E} {outs : List (PGraph E)} (hst : LocStep m P outs) :
    ∀ Q ∈ outs, lwEngine_nWS P.g ≤ lwEngine_nWS Q.g := by
  have key : ∀ {I'' : Type} [Fintype I''] [DecidableEq I''] (T : LGraph P.E' I''),
      lwEngine_nWS P.g ≤ lwEngine_nWS T → ∀ Q0 ∈ T.partition m, lwEngine_nWS P.g ≤ lwEngine_nWS Q0.g := by
    intro I'' _ _ T hT Q0 hQ0
    rw [← lwEngine_part_nWS m T Q0 hQ0]
    exact hT
  cases hst with
  | weight p hp x c t hx =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    simp only [lvl1WeightOuts0, List.mem_append, List.mem_flatMap] at hQ0
    change lwEngine_nWS P.g ≤ lwEngine_nWS Q0.g
    rcases hQ0 with ((hQ | hQ) | ⟨q, hq, hQ⟩) | ⟨q, hq, hQ⟩
    · exact key _ (lwEngine_T1_nWS c t m P.g x) Q0 hQ
    · exact key _ (lwEngine_T2_nWS c t m P.g p x) Q0 hQ
    · exact key _ (lwEngine_T3_nWS c t m P.g x q) Q0 hQ
    · exact key _ (lwEngine_T4_nWS c t m P.g x q) Q0 hQ
  | edge p hp x v hv c t hx hwf hbad =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    simp only [lvl1EdgeOuts0, List.mem_append, List.mem_flatMap] at hQ0
    change lwEngine_nWS P.g ≤ lwEngine_nWS Q0.g
    rcases hQ0 with hQ | ⟨q, hq, T, hT, hQ⟩
    · exact key _ (lwEngine_Oe1xOwx_nWS c t m P.g p x) Q0 hQ
    · exact key T (lwEngine_Ds_nWS c t m P.g p x v q T hT) Q0 hQ
  | gg p q hp hq x y y' hy c t hp1 hq1 hwf hnb =>
    intro Q hQ
    unfold lvl1Pack at hQ
    obtain ⟨Q0, hQ0, rfl⟩ := List.mem_map.1 hQ
    simp only [lvl1GGOuts0, List.mem_append, List.mem_flatMap] at hQ0
    change lwEngine_nWS P.g ≤ lwEngine_nWS Q0.g
    rcases hQ0 with (((((hQ | hQ) | hQ) | hQ) | hQ) | ⟨q', hq', hQ⟩) | ⟨q', hq', hQ⟩
    · exact key _ (lwEngine_R2_nWS c t m P.g p q x y y') Q0 hQ
    · exact key _ (lwEngine_R3_nWS c t m P.g p q x) Q0 hQ
    · exact key _ (lwEngine_R4_nWS c t m P.g p q x y y') Q0 hQ
    · exact key _ (lwEngine_R5_nWS c t m P.g p q x y y') Q0 hQ
    · exact key _ (lwEngine_R6_nWS c t m P.g p q x y y') Q0 hQ
    · exact key _ (lwEngine_R7_nWS c t m P.g p q x y y' q') Q0 hQ
    · exact key _ (lwEngine_R8_nWS c t m P.g p q x y y' q') Q0 hQ

/-- **The number of black waved edges does not fall along `Lvl1Reach`** (T2297's invariant `nWS ≥ p`, from the starting graph
`fxyPowGraph p`, which has `p` black waved edges): every graph reached from `P` has at least as many black waved edges as `P`. -/
theorem lw_nWS_ge {E : Type} {m : ℂ} {K : ℤ} {P Q : PGraph E} (h : Lvl1Reach m K P Q) :
    P.g.waved.countP (fun e => !e.col) ≤ Q.g.waved.countP (fun e => !e.col) :=
  lvl1_induction h (fun R => P.g.waved.countP (fun e => !e.col) ≤ R.g.waved.countP (fun e => !e.col)) le_rfl
    (fun _ _ hst hA B hB => hA.trans (lwEngine_locStep_nWS hst B hB))

end NWS

/-! ## 6. The recursion on the carrier and the transport to `LWLocRegConcl`

The recursion mirrors `lvl1_exists_aux` (`LWLvl1.lean:3837`): well-founded on `Lvl1Mu K` of the underlying graph, with the cutoff
`K`; at a graph that is not locally standard below the cutoff the step is `LocStepX` (selected by `lvl1_exists_step`, which reads
no coefficient), and the lists of the children are tagged by the tag of the child.  The specification is stated at every `m` and
every input tag `t₀`, for the evaluated lists, in the form of the four properties of `lvl1_exists_aux`. -/

section Rec

/-- the four properties of the lists `outs`, `errs` of `lvl1_exists_aux` -/
def lwEngine_Exp {E : Type} (m : ℂ) (K : ℤ) (Γ : PGraph E) (o e : List (PGraph E)) : Prop :=
  (∀ Q ∈ o, Q.g.LocStd ∧ ord Q.g.counters < K) ∧ (∀ Q ∈ e, K ≤ ord Q.g.counters) ∧
    (∀ Q ∈ o ++ e, Lvl1Reach m K Γ Q) ∧ Lvl1Ident m Γ o e

/-- **The step of the recursion** (the step part of `lvl1_exists_aux`), for the children `ev a` of a step `LocStep m Γ (LX.map ev)`:
the lists of the children combine. -/
theorem lwEngine_combine {E : Type} {α : Type*} {m : ℂ} {K : ℤ} {Γ : PGraph E} (hN : Γ.g.Normal) (hK : ord Γ.g.counters < K)
    (hL : ¬ Γ.g.LocStd) (LX : List α) (ev : α → PGraph E) (hst : LocStep m Γ (LX.map ev))
    (fo fe : α → List (PGraph E)) (hfo : ∀ a ∈ LX, lwEngine_Exp m K (ev a) (fo a) (fe a)) :
    lwEngine_Exp m K Γ (LX.flatMap fo) (LX.flatMap fe) := by
  have hreach : ∀ a ∈ LX, Lvl1Reach m K Γ (ev a) := fun a ha =>
    Lvl1Reach.step Γ Γ (ev a) (LX.map ev) (Lvl1Reach.refl Γ) hK hL hst (List.mem_map_of_mem ha)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Q' hQ'
    obtain ⟨a, ha, hQ'⟩ := List.mem_flatMap.1 hQ'
    exact (hfo a ha).1 Q' hQ'
  · intro Q' hQ'
    obtain ⟨a, ha, hQ'⟩ := List.mem_flatMap.1 hQ'
    exact (hfo a ha).2.1 Q' hQ'
  · intro Q' hQ'
    rcases List.mem_append.1 hQ' with h | h
    · obtain ⟨a, ha, h⟩ := List.mem_flatMap.1 h
      exact (hreach a ha).trans ((hfo a ha).2.2.1 Q' (List.mem_append_left _ h))
    · obtain ⟨a, ha, h⟩ := List.mem_flatMap.1 h
      exact (hreach a ha).trans ((hfo a ha).2.2.1 Q' (List.mem_append_right _ h))
  · intro d sz n z u Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe
    rw [lvl1_step_identity Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 hst hN ℓe, lvl1_sum_flatMap, lvl1_sum_flatMap,
      ← List.sum_map_add, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun a ha => ?_)
    exact (hfo a ha).2.2.2 Sp M hG hz hu hm0 hzm hSp hSpT hM hM0 ℓe

/-- the evaluated lists of the recursion: the lists of the children, tagged by the tag of the child -/
theorem lwEngine_flat_eval (m : ℂ) (t0 : ℕ × ℕ) (LX : List ((ℕ × ℕ) × PGraph (Fin 2)))
    (g : (ℕ × ℕ) × PGraph (Fin 2) → List ((ℕ × ℕ) × PGraph (Fin 2))) :
    ((LX.flatMap (fun r => (g r).map (lwEngine_shift r.1))).map (lwEngine_shift t0)).map (lwEvX m) =
      LX.flatMap (fun r => ((g r).map (lwEngine_shift (t0 + r.1))).map (lwEvX m)) := by
  rw [List.map_flatMap, List.map_flatMap]
  refine List.flatMap_congr fun r _ => ?_
  simp only [List.map_map]
  refine List.map_congr_left fun r' _ => ?_
  simp only [Function.comp_apply, lwEngine_shift, add_assoc]

/-- **The recursion on the carrier** (`lvl1_exists_aux` for the tagged lists): for a normal graph `Γ` and a cutoff `K` there are
tagged lists `oX`, `eX`, independent of `m` and of the input tag, whose evaluations at every `m`, with the input tag `t₀` added,
have the four properties of `lvl1_exists_aux` for the evaluated input `lwEvX m (t₀, Γ)`. -/
theorem lwEngine_exists (K : ℤ) (Γ : PGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oX eX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ (m : ℂ) (t0 : ℕ × ℕ),
      lwEngine_Exp m K (lwEvX m (t0, Γ)) ((oX.map (lwEngine_shift t0)).map (lwEvX m))
        ((eX.map (lwEngine_shift t0)).map (lwEvX m)) := by
  classical
  induction Γ using (InvImage.wf (Lvl1Mu K) lvl1Lt_wf).induction with
  | _ Γ ih =>
    by_cases hK : K ≤ ord Γ.g.counters
    · refine ⟨[], [((0, 0), Γ)], fun m t0 => ⟨by simp, ?_, ?_, ?_⟩⟩
      · intro Q hQ
        simp only [lwEngine_shift, List.map_cons, List.map_nil, List.mem_singleton] at hQ
        subst hQ
        exact hK
      · intro Q hQ
        simp only [lwEngine_shift, List.map_cons, List.map_nil, List.nil_append, List.mem_singleton,
          Prod.mk_zero_zero, add_zero] at hQ
        subst hQ
        exact Lvl1Reach.refl _
      · intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
        simp [lwEngine_shift, Prod.mk_zero_zero, add_zero]
    have hlt : ord Γ.g.counters < K := by omega
    by_cases hL : Γ.g.LocStd
    · refine ⟨[((0, 0), Γ)], [], fun m t0 => ⟨?_, by simp, ?_, ?_⟩⟩
      · intro Q hQ
        simp only [lwEngine_shift, List.map_cons, List.map_nil, List.mem_singleton] at hQ
        subst hQ
        exact ⟨hL, hlt⟩
      · intro Q hQ
        simp only [lwEngine_shift, List.map_cons, List.map_nil, List.append_nil, List.mem_singleton,
          Prod.mk_zero_zero, add_zero] at hQ
        subst hQ
        exact Lvl1Reach.refl _
      · intro d sz n z u Sp M _ _ _ _ _ _ _ _ _ ℓe
        simp [lwEngine_shift, Prod.mk_zero_zero, add_zero]
    obtain ⟨LX, hLX⟩ := lwEngine_exists_stepX Γ hN hL
    have hgood := lvl1_step_good (hLX.eval 1 0) hN
    have hch : ∀ r ∈ LX, Lvl1Lt (Lvl1Mu K r.2) (Lvl1Mu K Γ) ∧ r.2.g.Normal := by
      intro r hr
      have := hgood (lwEvX 1 (lwEngine_shift 0 r)) (List.mem_map_of_mem (List.mem_map_of_mem hr))
      exact ⟨lvl1_mu_lt hlt this.2, this.1⟩
    obtain ⟨fo, fe, hfo⟩ := lvl1_choose_list
      (fun (r : (ℕ × ℕ) × PGraph (Fin 2)) (o e : List ((ℕ × ℕ) × PGraph (Fin 2))) =>
        ∀ (m : ℂ) (t0 : ℕ × ℕ), lwEngine_Exp m K (lwEvX m (t0, r.2)) ((o.map (lwEngine_shift t0)).map (lwEvX m))
          ((e.map (lwEngine_shift t0)).map (lwEvX m))) LX
      (fun r hr => ih r.2 (hch r hr).1 (hch r hr).2)
    refine ⟨LX.flatMap (fun r => (fo r).map (lwEngine_shift r.1)), LX.flatMap (fun r => (fe r).map (lwEngine_shift r.1)),
      fun m t0 => ?_⟩
    rw [lwEngine_flat_eval, lwEngine_flat_eval]
    exact lwEngine_combine (α := (ℕ × ℕ) × PGraph (Fin 2)) (m := m) (Γ := lwEvX m (t0, Γ)) hN hlt hL LX
      (fun r => lwEvX m (lwEngine_shift t0 r))
      (by have := hLX.eval m t0; rwa [List.map_map] at this)
      (fun r => ((fo r).map (lwEngine_shift (t0 + r.1))).map (lwEvX m))
      (fun r => ((fe r).map (lwEngine_shift (t0 + r.1))).map (lwEvX m))
      (fun r hr => hfo r hr m (t0 + r.1))

/-- **The transport at a fixed `m`**: lists with the four properties of `lvl1_exists_aux` for the starting graph
`(fxyPowGraph p).pack` satisfy `LWLocRegConcl` (the proofs of `lvl1_lemma`, `lvl1_lemma_size`, `lw_localregular_upto5` and
`lw_localregular`, which take these four properties from `lvl1_exists_aux`). -/
theorem lwEngine_assemble (p : ℕ) (m : ℂ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (outs errs : List (PGraph (Fin 2)))
    (hq : lwEngine_Exp m (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack outs errs) :
    LWLocRegConcl p m c K0 d D outs errs := by
  obtain ⟨hout, herr, hreach, hid⟩ := hq
  have hN : (fxyPowGraph p).pack.g.Normal := fxyPowGraph_normal p
  have hinv : ∀ Q ∈ outs ++ errs, Q.g.Normal ∧ ord (fxyPowGraph p).pack.g.counters ≤ ord Q.g.counters ∧
      Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
      (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW := by
    intro Q hQ
    refine lvl1_induction (hreach Q hQ) (fun Q => Q.g.Normal ∧ ord (fxyPowGraph p).pack.g.counters ≤ ord Q.g.counters ∧
        Q.g.nM ≤ (fxyPowGraph p).pack.g.nM ∧
        (Q.g.nV : ℤ) - Q.g.nW ≤ ((fxyPowGraph p).pack.g.nV : ℤ) - (fxyPowGraph p).pack.g.nW)
      ⟨hN, le_refl _, le_refl _, le_refl _⟩ ?_
    intro A L hst hA B hB
    obtain ⟨hBN, hg⟩ := lvl1_step_good hst hA.1 B hB
    obtain ⟨h1, h2, h3, -⟩ := hg
    exact ⟨hBN, le_trans hA.2.1 h1, le_trans h2 hA.2.2.1, by have := hA.2.2.2; omega⟩
  have hP : ∀ Q ∈ outs ++ errs, Q.PathInv2 p := fun Q hQ =>
    lvl1_induction (hreach Q hQ) (fun Q : PGraph (Fin 2) => Q.PathInv2 p) (fxyPowGraph_pathInv2 p)
      (fun A L hst hA B hB => pathInv2_locStep hst hA B hB)
  have hInv : ∀ Q ∈ outs ++ errs, Q.LocReg6Inv p := fun Q hQ =>
    lvl1_induction (hreach Q hQ) (fun Q : PGraph (Fin 2) => Q.LocReg6Inv p) (fxyPowGraph_locReg6Inv p)
      (fun A L hst hA B hB => locReg6Inv_locStep p hst hA B hB)
  refine ⟨fun Q hQ => ⟨(hout Q hQ).1, (hinv Q (List.mem_append_left _ hQ)).2.1⟩, ?_,
    fun Q hQ => ⟨hreach Q hQ, hinv Q hQ⟩, ?_, ?_⟩
  · intro Q hQ W L Ψ hW hL hLW hlow hup
    obtain ⟨-, -, hM, hV⟩ := hinv Q (List.mem_append_right _ hQ)
    exact lvl1_size_le c hc K0 d D (fxyPowGraph p).pack.g.counters W L Ψ hW hL hLW hlow hup Q.g.counters (herr Q hQ) hM hV
  · intro sz n z u
    exact hid
  · intro Q hQ
    have hQ' : Q ∈ outs ++ errs := List.mem_append_left _ hQ
    have hI := hInv Q hQ'
    refine ⟨(hout Q hQ).1, ⟨?_, fun c => Q.g.molNV_le_molNW_add_one (hinv Q hQ').1 c⟩, (hP Q hQ').locReg345 (hout Q hQ).1,
      locReg6_of_locCostGe (hout Q hQ).1 hI.2.2.1, fun hxy => locReg6far_of_locCostGe (hout Q hQ).1 hxy hI.2.2.2⟩
    have := (hinv Q hQ').2.2.1
    rw [show (fxyPowGraph p).pack.g.nM = p from (fxyPowGraph_counters p).2.2.2] at this
    exact this

/-- the starting graph `fxyPowGraph p` has `p` black waved edges -/
theorem lwEngine_fxy_nWS (p : ℕ) : (fxyPowGraph p).pack.g.waved.countP (fun e => !e.col) = p := by
  simp [fxyPowGraph, LGraph.pack, List.countP_map, Function.comp_def]

/-- **The `m`-free `lem:localregular`** (`lw_localregular` with the lists chosen before `m`): one pair of tagged lists `outsX`,
`errsX` such that for every `m ≠ 0` the evaluated lists `outsX.map (lwEvX m)`, `errsX.map (lwEvX m)` satisfy the six conjuncts of
`lw_localregular` (`LWLocRegConcl`) and every graph of both has at least `p` black waved edges. -/
theorem lw_localregularX :
    ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ),
      ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)), ∀ m : ℂ, m ≠ 0 →
        LWLocRegConcl p m c K0 d D (outsX.map (lwEvX m)) (errsX.map (lwEvX m)) ∧
        ∀ Q ∈ outsX.map (lwEvX m) ++ errsX.map (lwEvX m), p ≤ Q.g.waved.countP (fun e => !e.col) := by
  intro p c hc K0 d D
  obtain ⟨oX, eX, h⟩ := lwEngine_exists (lvl1Cutoff c K0 d D (fxyPowGraph p).pack.g.counters : ℤ) (fxyPowGraph p).pack
    (fxyPowGraph_normal p)
  refine ⟨oX, eX, fun m _ => ?_⟩
  have hq := h m 0
  have e0 : lwEvX m (0, (fxyPowGraph p).pack) = (fxyPowGraph p).pack := lwEngine_ev_zero m _ rfl
  have e1 : (oX.map (lwEngine_shift 0)).map (lwEvX m) = oX.map (lwEvX m) := lwEngine_map_shift_zero m oX
  have e2 : (eX.map (lwEngine_shift 0)).map (lwEvX m) = eX.map (lwEvX m) := lwEngine_map_shift_zero m eX
  rw [e0, e1, e2] at hq
  refine ⟨lwEngine_assemble p m c hc K0 d D _ _ hq, fun Q hQ => ?_⟩
  have := lw_nWS_ge (hq.2.2.1 Q hQ)
  rw [lwEngine_fxy_nWS] at this
  exact this

end Rec

/-! ## 7. Compiled instances (CLAUDE.md §4 step 2) -/

namespace LWEngineInst

open MeasureTheory ProbabilityTheory Matrix
open RBM RBM.Gauss RBM.Green

/-- `m(0) = i` (the private `mE_zero` of `Green/MinorDiff.lean`) -/
theorem lwEngineInst_mE_zero : mE 0 = Complex.I := by
  apply Complex.ext <;> simp [mE, show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

/-- **Instance of `lwEvX`**: the tag `(3, 1)` multiplies the coefficient by `m³ m̄`, which is `-1` at `m = i` and `i/4` at
`m = (1 + i)/2` (one tagged graph, two different evaluations). -/
theorem lwEngine_inst_lwEvX (P : PGraph (Fin 2)) :
    (lwEvX Complex.I ((3, 1), P)).g.coeff = -1 * P.g.coeff ∧
    (lwEvX ((1 + Complex.I) / 2) ((3, 1), P)).g.coeff = Complex.I / 4 * P.g.coeff := by
  refine ⟨?_, ?_⟩
  · have h : Complex.I ^ 3 * star Complex.I = -1 := by simp [pow_succ]
    change Complex.I ^ 3 * star Complex.I ^ 1 * P.g.coeff = _
    rw [pow_one, h]
  · have h : ((1 + Complex.I) / 2) ^ 3 * star ((1 + Complex.I) / 2) = Complex.I / 4 := by
      apply Complex.ext <;> simp [pow_succ] <;> norm_num
    change ((1 + Complex.I) / 2) ^ 3 * star ((1 + Complex.I) / 2) ^ 1 * P.g.coeff = _
    rw [pow_one, h]

/-- **Instance of `LocStepX`**: Step 1 of `strat_local` on `p2Graph = fxyPowGraph 2` at the light-weight `(Ǧ - M)_{β₁β₁}`
(selector `(false, false)`; the merged `lvl1_inst_locStep_weight`) as one tagged list. -/
theorem lwEngine_inst_stepX :
    LocStepX p2Graph.pack (lvl1PackX p2Graph.pack (lvl1WeightOutsX p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)) :=
  LocStepX.weight p2Graph.pack lvl1ExP2p List.mem_cons_self (Sum.inr (1 : Fin 4)) false false rfl

/-- **Instance of `LocStepX.eval_one`**: the same tagged list, evaluated at `m = i` and at `m = (1 + i)/2`, is a `LocStep` of that
`m` of `p2Graph`. -/
theorem lwEngine_inst_two_m :
    LocStep Complex.I p2Graph.pack
      ((lvl1PackX p2Graph.pack (lvl1WeightOutsX p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map
        (lwEvX Complex.I)) ∧
    LocStep ((1 + Complex.I) / 2) p2Graph.pack
      ((lvl1PackX p2Graph.pack (lvl1WeightOutsX p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map
        (lwEvX ((1 + Complex.I) / 2))) :=
  ⟨lwEngine_inst_stepX.eval_one rfl Complex.I, lwEngine_inst_stepX.eval_one rfl ((1 + Complex.I) / 2)⟩

/-- **Instance of `LocStepX.edge`, `LocStepX.gg`**: Step 2 at the degree-`1` vertex `α₀` of `lvl1ExDeg1` and Step 3 at the vertex `α₀` of
`lvl1ExSame` (the merged `lvl1_inst_locStep_edge`, `lvl1_inst_locStep_gg`) as tagged lists, evaluated at `m = i` and `m = (1 + i)/2`. -/
theorem lwEngine_inst_stepX_edge_gg :
    (LocStep Complex.I lvl1ExDeg1.pack
      ((lvl1PackX lvl1ExDeg1.pack (lvl1EdgeOutsX lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)).map
        (lwEvX Complex.I)) ∧
    LocStep ((1 + Complex.I) / 2) lvl1ExDeg1.pack
      ((lvl1PackX lvl1ExDeg1.pack (lvl1EdgeOutsX lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)).map
        (lwEvX ((1 + Complex.I) / 2)))) ∧
    (LocStep Complex.I lvl1ExSame.pack
      ((lvl1PackX lvl1ExSame.pack (lvl1GGOutsX lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2))
        (Sum.inl (1 : Fin 2)) false true)).map (lwEvX Complex.I)) ∧
    LocStep ((1 + Complex.I) / 2) lvl1ExSame.pack
      ((lvl1PackX lvl1ExSame.pack (lvl1GGOutsX lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2))
        (Sum.inl (1 : Fin 2)) false true)).map (lwEvX ((1 + Complex.I) / 2)))) := by
  have he : LocStepX lvl1ExDeg1.pack
      (lvl1PackX lvl1ExDeg1.pack (lvl1EdgeOutsX lvl1ExDeg1 lvl1ExDeg1p (0 : Fin 3) (Sum.inl (0 : Fin 2)) false true)) :=
    LocStepX.edge lvl1ExDeg1.pack lvl1ExDeg1p List.mem_cons_self (0 : Fin 3) (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3)
      (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl (by decide) (by decide)
  have hg : LocStepX lvl1ExSame.pack
      (lvl1PackX lvl1ExSame.pack (lvl1GGOutsX lvl1ExSame lvl1ExSamep lvl1ExSameq (0 : Fin 3) (Sum.inl (0 : Fin 2))
        (Sum.inl (1 : Fin 2)) false true)) :=
    LocStepX.gg lvl1ExSame.pack lvl1ExSamep lvl1ExSameq List.mem_cons_self List.mem_cons_self (0 : Fin 3)
      (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 3)
      (by decide : (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 3) ≠ Sum.inr (0 : Fin 3)) false true rfl rfl (by decide) (by decide)
  exact ⟨⟨he.eval_one rfl Complex.I, he.eval_one rfl ((1 + Complex.I) / 2)⟩,
    ⟨hg.eval_one rfl Complex.I, hg.eval_one rfl ((1 + Complex.I) / 2)⟩⟩

/-- **Instance of `lw_nWS_ge`**: `p2Graph` has two black waved edges; every graph reached from it by the first step of `strat_local`
(`Lvl1Reach` with the cutoff `K = 5 > ord p2Graph = 2`, `p2Graph` not locally standard) has at least two. -/
theorem lwEngine_inst_nWS_ge :
    ∀ Q ∈ lvl1Pack p2Graph.pack (lvl1WeightOuts0 (mE 0) p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false),
      2 ≤ Q.g.waved.countP (fun e => !e.col) := fun Q hQ => by
  have hord : ord p2Graph.pack.g.counters = 2 := fxyPowGraph_ord 2
  have hr : Lvl1Reach (mE 0) 5 p2Graph.pack Q :=
    Lvl1Reach.step p2Graph.pack p2Graph.pack Q _ (Lvl1Reach.refl _) (by rw [hord]; norm_num) (by decide)
      lvl1_inst_locStep_weight hQ
  have h := lw_nWS_ge hr
  have e : p2Graph.pack.g.waved.countP (fun e => !e.col) = 2 := by decide
  rw [e] at h
  exact h

/-- **Instance of `lvl1_step_identity` on the evaluated `X`-list** at the merged instance data (`d = 3`, `L = 3`, `W = 1`,
`E = 0`, `t = 1/2`, `m = i`, `M = m·1`, `S⁺ = S (1 - m² S)⁻¹`; `GaussIBP` is the proved `gaussIBP`): every hypothesis discharged. -/
theorem lwEngine_inst_step1_identity :
    ∫ ω, p2Graph.pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
        lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
      (((lvl1PackX p2Graph.pack (lvl1WeightOutsX p2Graph lvl1ExP2p (Sum.inr (1 : Fin 4)) false false)).map
          (lwEvX (mE 0))).map fun Q =>
        ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM (lwS lwWxInstSz 0 (1 / 2))
          lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum :=
  lvl1_step_identity lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num)
    (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE) lwWx_inst_hSp lwSymm_inst_hSpT lwWx_inst_hM
    lwSymm_inst_hM0 (lwEngine_inst_stepX.eval_one rfl (mE 0)) (by decide) lwSymmInstL

/-- **Instance of `lw_localregularX`** at `p = 2`, `d = 3`, `c = 1/4`, `K0 = 1` (`L^3 ≤ W`), `D = 10` (the only hypothesis `0 < c`
is discharged): one pair of tagged lists, evaluated at `m = i` (the regime at `W = 27`, `L = 3`, `Ψ = 27^{-1/4}`, the expectation
identity at the merged instance data with every hypothesis discharged, properties (5) and (6), `nWS ≥ 2`) and at `m = (1 + i)/2`
(the whole conclusion). -/
theorem lwEngine_inst_localregularX :
    ∃ outsX errsX : List ((ℕ × ℕ) × PGraph (Fin 2)),
      ((∀ Q ∈ outsX.map (lwEvX Complex.I), Q.g.LocStd ∧ 2 ≤ Q.g.scalingOrder) ∧
        (∀ Q ∈ errsX.map (lwEvX Complex.I),
          Q.g.scalingSize (((27 : ℕ) : ℝ) ^ (-(1 / 4 : ℝ))) 27 3 3 ≤ ((27 : ℕ) : ℝ) ^ (-(10 : ℝ))) ∧
        ∫ ω, (fxyPowGraph 2).pack.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) lwWxInstM
            (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz) =
          ((outsX.map (lwEvX Complex.I)).map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2)
            lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum +
          ((errsX.map (lwEvX Complex.I)).map fun Q => ∫ ω, Q.val (lwSampleData lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2)
            lwWxInstM (lwS lwWxInstSz 0 (1 / 2)) lwWxInstSp ω) lwSymmInstL ∂(Sizes.seqP lwWxInstSz)).sum ∧
        (∀ Q ∈ outsX.map (lwEvX Complex.I), Q.LocReg1 ∧ Q.LocReg2 2 ∧ Q.LocReg345 2 ∧ Q.LocReg6 2 ∧
          (Q.ext 0 ≠ Q.ext 1 → 3 * (2 : ℤ) ≤ Q.g.scalingOrder)) ∧
        ∀ Q ∈ outsX.map (lwEvX Complex.I) ++ errsX.map (lwEvX Complex.I), 2 ≤ Q.g.waved.countP (fun e => !e.col)) ∧
      (LWLocRegConcl 2 ((1 + Complex.I) / 2) (1 / 4) 1 3 10 (outsX.map (lwEvX ((1 + Complex.I) / 2)))
          (errsX.map (lwEvX ((1 + Complex.I) / 2))) ∧
        ∀ Q ∈ outsX.map (lwEvX ((1 + Complex.I) / 2)) ++ errsX.map (lwEvX ((1 + Complex.I) / 2)),
          2 ≤ Q.g.waved.countP (fun e => !e.col)) := by
  obtain ⟨outsX, errsX, h⟩ := lw_localregularX 2 (1 / 4) (by norm_num) 1 3 10
  have hI : mE 0 = Complex.I := lwEngineInst_mE_zero
  obtain ⟨⟨c1, c2, -, c4, c5⟩, hw⟩ := h Complex.I Complex.I_ne_zero
  refine ⟨outsX, errsX, ⟨fun Q hQ => ?_, fun Q hQ => ?_, ?_, c5, hw⟩, h ((1 + Complex.I) / 2) ?_⟩
  · obtain ⟨a, b⟩ := c1 Q hQ
    have e : (fxyPowGraph 2).pack.g.scalingOrder = 2 := fxyPowGraph_ord 2
    exact ⟨a, by rw [e] at b; exact b⟩
  · refine c2 Q hQ 27 3 _ (by norm_num) (by norm_num) (by norm_num) ?_ (le_refl _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · refine c4 lwWxInstSp lwWxInstM (gaussIBP lwWxInstSz) lwWx_inst_im (by norm_num) Complex.I_ne_zero ?_ ?_
      lwSymm_inst_hSpT ?_ lwSymm_inst_hM0 lwSymmInstL
    · rw [← hI]
      exact lwWx_flow 0 (1 / 2) lwWx_inst_hE
    · intro i j
      rw [← hI]
      exact lwWx_inst_hSp i j
    · intro a
      rw [← hI]
      exact lwWx_inst_hM a
  · intro h0
    have := congrArg Complex.re h0
    simp at this

end LWEngineInst

end RBM.Graph
end
