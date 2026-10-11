/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExpandWOrd

/-!
# BA-L2c1: the weight expansion `lem_lweight` (B.19) as a graph operation (T2407)

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:376-387` (cited `B:line`; `lem_lweight` =
`(eq:LW)`, [yang2024Del, Lemma B.10]).  The identity of the polynomial `f` is `baLweight_holds`
(`Graph/BAExpandW.lean`); this file is its graph form at a self-loop `Ǧ_{xx}` (Amend 1: the term lists are
those of the T2395 probe, copied verbatim).

## Contents (namespace `RBM.Graph`, private prefix `BAWeightOp_`)

1. **Target 1**: `BAGraph.ext`, `bpv`, `bpS`, `bpM`, `bpW`, `BAGraph.lw2`, `BAGraph.lw4`, `baSum`
   (T2395 probe `t/T2395:RBM3D/Probe/T2395Pins.lean` at `4c1de4c`, lines 105-126 and 239-241).
2. **Target 2** (`baExpFrame_lw`, the first conjunct of `BAexpFrameE`): the expectation of `Γ.val` is that of
   `baSum (Γ.lw2 p) + baSum (Γ.lw4 p)`, from `baLweight_holds` and `W = 1 + M⁺ (S W)` (`baW_mul`).
3. **Target 3**: the raw counters of the terms (`lw_counters`), the raw order (`lw_raw`), the counter half
   of `BAstepMono` at `T°` (`lw_mono`), and `lw_scalingOrderG`.
4. Compiled instances (`RBM.Graph.BAWeightOpInst`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-! ## 1. Target 1: the term lists (verbatim from the T2395 probe) -/

section Ops
variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
/-- the generic extension by `k` new vertices `inr (inr i)` (the shape of the merged `lanlwExt`, `BAExpandW.lean:114`, for any `k`). -/
def BAGraph.ext (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I))) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) : BAGraph E (I ⊕ Fin k) :=
  BAGraph.mk (({ Γ.toLGraph with solid := rest } : LGraph E I).owxExt (owxEmb k) 1 s w)
    (Γ.psi.map (BAPsiEdge.map (owxEmb k))) (md ++ Γ.mdot.map (BAMEdge.map (owxEmb k)))
abbrev bpv {E I : Type} {k : ℕ} (i : Fin k) : E ⊕ (I ⊕ Fin k) := Sum.inr (Sum.inr i)
/-- a blue edge, circled iff `c` -/
def bpS {V : Type} (c : Bool) (a b : V) : SEdge V := ⟨true, c, a, b⟩
def bpM {V : Type} (a b : V) : BAMEdge V := ⟨true, a, b⟩
/-- a waved edge: `S⁺` (`col = true`) or `S` -/
def bpW {V : Type} (col : Bool) (a b : V) : WEdge V := ⟨col, true, a, b⟩
/-- **`lem_lweight`** at the self-loop `p = Ǧ_{xx}` (`B:376-387`, L2c1): the `y = x` part is `lw2` (`M_{xα} S_{αβ} Ǧ_{αx} Ǧ_{ββ}` and the derivative
terms, which are those of the merged `lanlwD` since `p.1.dst = p.1.src`), the `(M⁺S⁺)_{xy}` part is `lw4` (`z, y, α, β = bpv 0..3`). -/
def BAGraph.lw2 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (BAGraph E (I ⊕ Fin 2)) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)] :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)
def BAGraph.lw4 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (BAGraph E (I ⊕ Fin 4)) :=
  let w : List (WEdge (E ⊕ (I ⊕ Fin 4))) := [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
  let md : List (BAMEdge (E ⊕ (I ⊕ Fin 4))) := [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]
  BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)] w md ::
    (lwSplit p.2).map fun q => BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1,
      (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2, bpS false (bpv 3) (bpv 1)] w md
end Ops

section Pins
/-- the value of a list of terms -/
def baSum {E I ι : Type} [Fintype I] [DecidableEq I] [Fintype ι] [DecidableEq ι] (Ts : List (BAGraph E I)) (D : BALData ι) (ℓe : E → ι) : ℂ :=
  (Ts.map fun T => T.val D ℓe).sum
end Pins

/-! ## 2. Terms of the extension: labellings and values -/

section Terms

variable {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The term of a generic extension (`BAExpandW_lanlwExt_term` for any `k`). -/
theorem BAWeightOp_ext_term (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (D : BALData ι) (ℓ' : E ⊕ (I ⊕ Fin k) → ι) :
    (BAGraph.ext k Γ rest s w md).term D ℓ' =
      ({ Γ with solid := rest } : BAGraph E I).term D (ℓ' ∘ owxEmb k) * (s.map (SEdge.val D.toLData ℓ')).prod *
        (w.map (WEdge.val D.toLData ℓ')).prod * (md.map (BAMEdge.val D ℓ')).prod := by
  have h1 : (BAPsiEdge.val D ℓ') ∘ (BAPsiEdge.map (owxEmb k)) = BAPsiEdge.val D (ℓ' ∘ owxEmb k) :=
    funext fun e => rfl
  have h2 : (BAMEdge.val D ℓ') ∘ (BAMEdge.map (owxEmb k)) = BAMEdge.val D (ℓ' ∘ owxEmb k) :=
    funext fun e => rfl
  unfold BAGraph.ext BAGraph.term
  simp only [LGraph.term_owxExt, List.map_append, List.prod_append, List.map_map, h1, h2]
  ring

/-- The labelling of `E ⊕ (I ⊕ Fin 4)` extending `(ℓe, ℓi)` by the labels `z, y, α, β`. -/
def BAWeightOp_lab4 (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) : E ⊕ (I ⊕ Fin 4) → ι :=
  Sum.elim ℓe (Sum.elim ℓi ![z, y, α, β])

theorem BAWeightOp_lab4_emb (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) :
    BAWeightOp_lab4 ℓe ℓi z y α β ∘ owxEmb 4 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

/-- A labelling of `I ⊕ Fin 4` is a labelling of `I` and four labels. -/
theorem BAWeightOp_sum_fin4 (F : (I ⊕ Fin 4 → ι) → ℂ) :
    ∑ ℓ', F ℓ' = ∑ ℓi : I → ι, ∑ z : ι, ∑ y : ι, ∑ α : ι, ∑ β : ι, F (Sum.elim ℓi ![z, y, α, β]) := by
  rw [← (Equiv.sumArrowEquivProdArrow I (Fin 4) ι).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sum_pi_fin_succ]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [sum_pi_fin_zero]
  rfl

end Terms

section TermForms

variable {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The leaf of `lw2`: `Σ_{α,β} M_{xα} S_{αβ} Ǧ_{αx} Ǧ_{ββ} f`. -/
private def BAWeightOp_leaf2 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 0) (owxEmb 2 p.1.dst), bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
    [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- The leaf of `lw4`: `Σ_{z,y,α,β} M_{xz} M_{zx} S⁺_{zy} M_{yα} S_{αβ} Ǧ_{αy} Ǧ_{ββ} f`. -/
private def BAWeightOp_leaf4 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ p.2 [bpS true (bpv 2) (bpv 1), bpS true (bpv 3) (bpv 3)]
    [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

/-- The derivative term of `lw4` for the solid edge `q.1` of `f`. -/
private def BAWeightOp_tail4 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ q.2 [(owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1,
      (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2, bpS false (bpv 3) (bpv 1)]
    [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 4 p.1.src), bpM (bpv 1) (bpv 2)]

theorem BAWeightOp_lw2_eq (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.lw2 p = BAWeightOp_leaf2 Γ p :: (lwSplit p.2).map (BAGraph.lanlwD Γ p) := rfl

theorem BAWeightOp_lw4_eq (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    Γ.lw4 p = BAWeightOp_leaf4 Γ p :: (lwSplit p.2).map (BAWeightOp_tail4 Γ p) := rfl

theorem BAWeightOp_leaf2_term (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    (BAWeightOp_leaf2 Γ p).term D (owxLab2 ℓe ℓi α β) =
      ({ Γ with solid := p.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G α (Sum.elim ℓe ℓi p.1.dst) - D.M α (Sum.elim ℓe ℓi p.1.dst)) * (D.G β β - D.M β β) *
          D.S α β * D.M (Sum.elim ℓe ℓi p.1.src) α) := by
  have hq : ∀ v, owxLab2 ℓe ℓi α β (owxEmb 2 v) = Sum.elim ℓe ℓi v := fun v => by rcases v <;> rfl
  have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
  have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
  rw [BAWeightOp_leaf2, BAWeightOp_ext_term, BAExpandW_lab2_emb]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
    BAMEdge.val, bpS, bpW, bpM, bpv, hq, e0, e1]
  simp
  ring

theorem BAWeightOp_leaf4_term (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) :
    (BAWeightOp_leaf4 Γ p).term D (BAWeightOp_lab4 ℓe ℓi z y α β) =
      ({ Γ with solid := p.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((D.G α y - D.M α y) * (D.G β β - D.M β β) * (D.Sp z y * D.S α β) *
          (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M y α)) := by
  have hq : ∀ v, BAWeightOp_lab4 ℓe ℓi z y α β (owxEmb 4 v) = Sum.elim ℓe ℓi v := fun v => by rcases v <;> rfl
  have e0 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 0)) = z := rfl
  have e1 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 1)) = y := rfl
  have e2 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 2)) = α := rfl
  have e3 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 3)) = β := rfl
  rw [BAWeightOp_leaf4, BAWeightOp_ext_term, BAWeightOp_lab4_emb]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val,
    BAMEdge.val, bpS, bpW, bpM, bpv, hq, e0, e1, e2, e3]
  simp
  ring

theorem BAWeightOp_tail4_term (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) (ℓi : I → ι) (z y α β : ι) :
    (BAWeightOp_tail4 Γ p q).term D (BAWeightOp_lab4 ℓe ℓi z y α β) =
      ({ Γ with solid := q.2 } : BAGraph E I).term D (Sum.elim ℓe ℓi) *
        ((if q.1.σ then D.G (Sum.elim ℓe ℓi q.1.src) β * D.G α (Sum.elim ℓe ℓi q.1.dst)
          else star (D.G (Sum.elim ℓe ℓi q.1.src) α) * star (D.G β (Sum.elim ℓe ℓi q.1.dst))) * D.G β y *
          (D.Sp z y * D.S α β) *
          (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M y α)) := by
  have hq : ∀ v, BAWeightOp_lab4 ℓe ℓi z y α β (owxEmb 4 v) = Sum.elim ℓe ℓi v := fun v => by rcases v <;> rfl
  have e0 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 0)) = z := rfl
  have e1 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 1)) = y := rfl
  have e2 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 2)) = α := rfl
  have e3 : BAWeightOp_lab4 ℓe ℓi z y α β (Sum.inr (Sum.inr 3)) = β := rfl
  have h : SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z y α β)
        (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).1 *
      SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z y α β) (owxDE (bpv 3) (bpv 2) (SEdge.map (owxEmb 4) q.1)).2 =
      if q.1.σ then D.G (Sum.elim ℓe ℓi q.1.src) β * D.G α (Sum.elim ℓe ℓi q.1.dst)
        else star (D.G (Sum.elim ℓe ℓi q.1.src) α) * star (D.G β (Sum.elim ℓe ℓi q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq, bpv, e2, e3]
  rw [BAWeightOp_tail4, BAWeightOp_ext_term, BAWeightOp_lab4_emb]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc (SEdge.val D.toLData (BAWeightOp_lab4 ℓe ℓi z y α β) _), h]
  simp [SEdge.val, WEdge.val, BAMEdge.val, bpS, bpW, bpM, bpv, hq, e0, e1, e2, e3]
  split_ifs <;> ring

end TermForms

section Alg

private theorem BAWeightOp_alg {ι : Type*} [Fintype ι] [DecidableEq ι] (K f : ℂ) (x : ι)
    (M S Sp Wm gc g df : ι → ι → ℂ)
    (hW : ∀ y, Wm x y = (if x = y then 1 else 0) + ∑ z, M x z * M z x * Sp z y) :
    K * ∑ y, Wm x y * (∑ α, ∑ β, M y α * S α β * gc α y * gc β β * f -
        ∑ α, ∑ β, M y α * S α β * g β y * df β α) =
      ∑ α, ∑ β, (K * f * (M x α * S α β * gc α x * gc β β) - K * M x α * S α β * g β x * df β α) +
      ∑ z, ∑ y, ∑ α, ∑ β, (M x z * M z x * Sp z y) *
        (K * f * (M y α * S α β * gc α y * gc β β) - K * M y α * S α β * g β y * df β α) := by
  set B : ι → ℂ := fun y => ∑ α, ∑ β, (K * f * (M y α * S α β * gc α y * gc β β) -
    K * M y α * S α β * g β y * df β α) with hBdef
  have hB : ∀ y, K * (∑ α, ∑ β, M y α * S α β * gc α y * gc β β * f -
        ∑ α, ∑ β, M y α * S α β * g β y * df β α) = B y := by
    intro y
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun β _ => by ring
  have h1 : K * ∑ y, Wm x y * (∑ α, ∑ β, M y α * S α β * gc α y * gc β β * f -
        ∑ α, ∑ β, M y α * S α β * g β y * df β α) = ∑ y, Wm x y * B y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hB y]; ring
  have h2 : ∀ z y, ∑ α, ∑ β, (M x z * M z x * Sp z y) *
        (K * f * (M y α * S α β * gc α y * gc β β) - K * M y α * S α β * g β y * df β α) =
      (M x z * M z x * Sp z y) * B y := by
    intro z y
    rw [hBdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum]
  rw [h1]
  simp_rw [h2, hW, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun z y => (M x z * M z x * Sp z y) * B y)]

end Alg

section Kernel

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **`W = 1 + M⁺ (S W)`** (`S⁺ = S W`), entrywise: from `W (1 - M⁺S) = 1` (`baW_mul`) and the commutation of the
one-sided inverses of a square matrix. -/
theorem BAWeightOp_W_sub_one (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht0 : 0 ≤ t) (ht1 : t < 1) (x y : Idx d L W) :
    BAlwW d L W g0 E t m x y = (if x = y then 1 else 0) +
      ∑ z, BAlwM d L W g0 E m x z * BAlwM d L W g0 E m z x *
        (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) z y := by
  have h0 := baW_mul (d := d) (W := W) hL g0 E t m hSelf ht0 ht1
  have h1 : (1 - BAlwMp d L W g0 E m * Matrix.of (BAlwS d L W t)) * BAlwW d L W g0 E t m = 1 :=
    (mul_eq_one_comm (M := Matrix (Idx d L W) (Idx d L W) ℂ)).1 h0
  have h2 : BAlwW d L W g0 E t m = 1 + BAlwMp d L W g0 E m * (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) := by
    rw [← Matrix.mul_assoc]
    rw [sub_mul, one_mul] at h1
    exact sub_eq_iff_eq_add.1 h1
  conv_lhs => rw [h2]
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, BAlwMp, Matrix.of_apply]

end Kernel

section Pathwise

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integrand of the right side of `baExpFrame_lw` at the labelling `(ℓe, ℓi)` of the old vertices: the sum over the
labels of the new vertices of the terms of `lw2` and `lw4`. -/
private def BAWeightOp_R (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι) (ℓe : E → ι)
    (ℓi : I → ι) : ℂ :=
  ∑ α, ∑ β, ((Γ.lw2 p).map fun T => T.term D (owxLab2 ℓe ℓi α β)).sum +
    ∑ z, ∑ y, ∑ α, ∑ β, ((Γ.lw4 p).map fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z y α β)).sum

/-- **The pathwise form of `lem_lweight`**: the terms of `lw2` and `lw4` sum to `K Σ_y W_{xy} (...)`, the right side
of (B.19) with `f` and `∂f` read off the edges of `p.2`. -/
private theorem BAWeightOp_pathwise (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hxx : p.1.src = p.1.dst) (D : BALData ι) (Wm : Matrix ι ι ℂ)
    (hW : ∀ x y, Wm x y = (if x = y then 1 else 0) + ∑ z, D.M x z * D.M z x * D.Sp z y)
    (ℓe : E → ι) (ℓi : I → ι) (K f : ℂ) (df : ι → ι → ℂ)
    (hK : ∀ s : List (SEdge (E ⊕ I)), ({ Γ with solid := s } : BAGraph E I).term D (Sum.elim ℓe ℓi) =
      K * (s.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
    (hf : (p.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod = f)
    (hdf : ∀ β α, df β α = ((lwSplit p.2).map fun q =>
      (if q.1.σ then -(D.G (Sum.elim ℓe ℓi q.1.src) β * D.G α (Sum.elim ℓe ℓi q.1.dst))
        else -(star (D.G (Sum.elim ℓe ℓi q.1.src) α) * star (D.G β (Sum.elim ℓe ℓi q.1.dst)))) *
      (q.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod).sum) :
    BAWeightOp_R Γ p D ℓe ℓi = K * ∑ y, Wm (Sum.elim ℓe ℓi p.1.src) y *
      (∑ α, ∑ β, D.M y α * D.S α β * (D.G α y - D.M α y) * (D.G β β - D.M β β) * f -
        ∑ α, ∑ β, D.M y α * D.S α β * D.G β y * df β α) := by
  have hy : Sum.elim ℓe ℓi p.1.dst = Sum.elim ℓe ℓi p.1.src := by rw [hxx]
  -- the sum of the derivative terms over `q`
  have hD : ∀ (c : ℂ) (β α : ι) (F : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)) → ℂ),
      (∀ q ∈ lwSplit p.2, F q = c * (K * (q.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod *
        (if q.1.σ then D.G (Sum.elim ℓe ℓi q.1.src) β * D.G α (Sum.elim ℓe ℓi q.1.dst)
          else star (D.G (Sum.elim ℓe ℓi q.1.src) α) * star (D.G β (Sum.elim ℓe ℓi q.1.dst))))) →
      ((lwSplit p.2).map F).sum = -(c * K * df β α) := by
    intro c β α F hF
    have h := owx_list_aux (lwSplit p.2) (c * K) (fun q =>
      (if q.1.σ then -(D.G (Sum.elim ℓe ℓi q.1.src) β * D.G α (Sum.elim ℓe ℓi q.1.dst))
        else -(star (D.G (Sum.elim ℓe ℓi q.1.src) α) * star (D.G β (Sum.elim ℓe ℓi q.1.dst)))) * (q.2.map (SEdge.val D.toLData (Sum.elim ℓe ℓi))).prod)
      F (fun q hq => by
        rw [hF q hq]
        by_cases hσ : q.1.σ <;> simp [hσ] <;> ring)
    rw [h, hdf β α]
  have h2l : ∀ α β, (BAWeightOp_leaf2 Γ p).term D (owxLab2 ℓe ℓi α β) =
      K * f * (D.M (Sum.elim ℓe ℓi p.1.src) α * D.S α β * (D.G α (Sum.elim ℓe ℓi p.1.src) - D.M α (Sum.elim ℓe ℓi p.1.src)) * (D.G β β - D.M β β)) := by
    intro α β
    rw [BAWeightOp_leaf2_term, hK, hf, hy]
    ring
  have h2t : ∀ α β, (((lwSplit p.2).map (BAGraph.lanlwD Γ p)).map fun T => T.term D (owxLab2 ℓe ℓi α β)).sum =
      -(K * D.M (Sum.elim ℓe ℓi p.1.src) α * D.S α β * D.G β (Sum.elim ℓe ℓi p.1.src) * df β α) := by
    intro α β
    rw [List.map_map]
    have := hD (D.G β (Sum.elim ℓe ℓi p.1.src) * D.S α β * D.M (Sum.elim ℓe ℓi p.1.src) α) β α ((fun T => T.term D (owxLab2 ℓe ℓi α β)) ∘ BAGraph.lanlwD Γ p)
      (fun q hq => by
        have e0 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 0)) = α := rfl
        have e1 : owxLab2 ℓe ℓi α β (Sum.inr (Sum.inr 1)) = β := rfl
        simp only [Function.comp_apply]
        rw [BAExpandW_lanlwD_term Γ p q D (Sum.elim ℓe ℓi) _ (BAExpandW_lab2_emb ℓe ℓi α β), hK, e0, e1, hy]
        ring)
    rw [this]
    ring
  have h4l : ∀ z y α β, (BAWeightOp_leaf4 Γ p).term D (BAWeightOp_lab4 ℓe ℓi z y α β) =
      (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.Sp z y) * (K * f * (D.M y α * D.S α β * (D.G α y - D.M α y) * (D.G β β - D.M β β))) := by
    intro z y α β
    rw [BAWeightOp_leaf4_term, hK, hf]
    ring
  have h4t : ∀ z y α β, (((lwSplit p.2).map (BAWeightOp_tail4 Γ p)).map fun T =>
      T.term D (BAWeightOp_lab4 ℓe ℓi z y α β)).sum =
      (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.Sp z y) * (-(K * D.M y α * D.S α β * D.G β y * df β α)) := by
    intro z y α β
    rw [List.map_map]
    have := hD (D.G β y * (D.Sp z y * D.S α β) * (D.M (Sum.elim ℓe ℓi p.1.src) z * D.M z (Sum.elim ℓe ℓi p.1.src) * D.M y α)) β α
      ((fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z y α β)) ∘ BAWeightOp_tail4 Γ p)
      (fun q hq => by
        simp only [Function.comp_apply]
        rw [BAWeightOp_tail4_term, hK]
        ring)
    rw [this]
    ring
  have key := BAWeightOp_alg K f (Sum.elim ℓe ℓi p.1.src) D.M D.S D.Sp Wm (fun a b => D.G a b - D.M a b) D.G df (hW _)
  unfold BAWeightOp_R
  simp only [BAWeightOp_lw2_eq, BAWeightOp_lw4_eq, List.map_cons, List.sum_cons, h2l, h2t, h4l, h4t]
  refine Eq.trans ?_ key.symm
  congr 1
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => by ring

end Pathwise

/-! ## 3. Target 2: the value identity -/

section Core

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro `baw_tame` of `Graph/BAExpandW.lean`). -/
local macro "bwo_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply BAExpand_tame_baG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply lwStein_tame_hflow
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- The graph data at a sample of the sequence space (`BAlwData` at the slice, as in `lanlw_val`). -/
private abbrev BAWeightOp_sd (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL)) :
    BALData (Idx d L W) :=
  BAExpandW_sampleData (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (BAlwM d L W g0 E m)
    (Matrix.of (BAlwS d L W t)) (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) ((g0 : ℂ) • PsiI d L W) ω'

/-- The resolvent polynomial of a solid edge at a labelling, in the variables `Bool × Idx × Idx` of `LWPins_resPoly`
(a red edge `Ḡ_{ab}` is the variable `(false, b, a)`). -/
private def BAWeightOp_edgePoly0 (M : Matrix (Idx d L W) (Idx d L W) ℂ) {V : Type*} (ℓ : V → Idx d L W)
    (e : SEdge V) : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
  if e.σ then MvPolynomial.X (true, ℓ e.src, ℓ e.dst) - MvPolynomial.C (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0)
  else MvPolynomial.X (false, ℓ e.dst, ℓ e.src) -
    MvPolynomial.C (star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0))

private theorem BAWeightOp_rename_edgePoly0 (hL : 3 ≤ L) (M : Matrix (Idx d L W) (Idx d L W) ℂ) {V : Type*}
    (ℓ : V → Idx d L W) (e : SEdge V) :
    lwWxRename d L W (BAWeightOp_edgePoly0 M ℓ e) = owxEdgePoly (lwWxSizes d L W 0 hL) 0 M ℓ e := by
  unfold BAWeightOp_edgePoly0 owxEdgePoly lwWxRename
  cases hσ : e.σ <;> simp [lwWxVar]


/-- **One labelling of the old vertices** (the BA twin of `BAExpandW_term_integral` for `lem_lweight`): for the circled
blue self-loop `p.1 = Ǧ_{xx}`, `𝔼 Γ.term` at the labelling `(ℓe, ℓi)` is the expectation of the sum, over the labels of
the new vertices, of the terms of `lw2` and `lw4` (`BAWeightOp_R`), on the sequence space.  From `baLweight_holds`
through `lwWx_integral`; the pathwise identity is `BAWeightOp_pathwise`. -/
private theorem BAWeightOp_core (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht : 0 < t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]
    (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : p.1.σ = true) (hc : p.1.circ = true) (hxx : p.1.src = p.1.dst) (ℓe : Ex → Idx d L W)
    (ℓi : Ix → Idx d L W) :
    Integrable (fun ω' => BAWeightOp_R Γ p (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi)
        (Sizes.seqP (lwWxSizes d L W 0 hL)) ∧
      ∫ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi) ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
        ∫ ω', BAWeightOp_R Γ p (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
  classical
  have hm : 0 < m.im := hSelf.1
  have hz : (ztOf m E t).im ≠ 0 := by
    rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
  have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
  obtain ⟨x, hx⟩ : ∃ x : Idx d L W, Sum.elim ℓe ℓi p.1.src = x := ⟨_, rfl⟩
  have hy : Sum.elim ℓe ℓi p.1.dst = x := by rw [← hxx]; exact hx
  set K : ℂ := BAExpandW_K Γ (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t))
    (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) ((g0 : ℂ) • PsiI d L W) (Sum.elim ℓe ℓi) with hK
  set P0 : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ :=
    (p.2.map (BAWeightOp_edgePoly0 (BAlwM d L W g0 E m) (Sum.elim ℓe ℓi))).prod with hP0
  have hP0r : lwWxRename d L W P0 = (p.2.map (owxEdgePoly (lwWxSizes d L W 0 hL) 0 (BAlwM d L W g0 E m)
      (Sum.elim ℓe ℓi))).prod := by
    rw [hP0, map_list_prod, List.map_map]
    congr 1
    exact List.map_congr_left fun e _ => BAWeightOp_rename_edgePoly0 hL _ _ e
  have hf : ∀ ω', baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' =
      (p.2.map (SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi))).prod := fun ω' => by
    rw [hP0r]; exact BAExpandW_baPoly_edgePoly_prod _ p.2 ω'
  have hP1 : Tame1 (lwWxSizes d L W 0 hL) 0
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) :=
    baPoly_tame1 hz g0 t _
  have tf : Tame (lwWxSizes d L W 0 hL) (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) :=
    hP1.tame
  have tD : ∀ α β : Idx d L W, Tame (lwWxSizes d L W 0 hL)
      (dhSample (lwWxSizes d L W 0 hL) 0 t α β (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0))) :=
    fun α β => lwStein_tame_dhSample hP1 t α β
  have tG : ∀ i j : Idx d L W, Tame (lwWxSizes d L W 0 hL) (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t i j) :=
    fun i j => BAExpand_tame_baG (lwWxSizes d L W 0 hL) 0 hz g0 t i j
  -- the two integrands on the sequence space
  set FL : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ := fun ω' =>
    (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t x x ω' - BAlwM d L W g0 E m x x) *
      baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' with hFL
  set FR : Sizes.SeqΩ (lwWxSizes d L W 0 hL) → ℂ := fun ω' =>
    ∑ y, BAlwW d L W g0 E t m x y *
      (∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β *
          (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t α y ω' - BAlwM d L W g0 E m α y) *
          (baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β β ω' - BAlwM d L W g0 E m β β) *
          baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω' -
        ∑ α, ∑ β, BAlwM d L W g0 E m y α * BAlwS d L W t α β *
          baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t β y ω' *
          dhSample (lwWxSizes d L W 0 hL) 0 t β α
            (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω') with hFR
  have tFL : Tame (lwWxSizes d L W 0 hL) FL := by
    rw [hFL]; bwo_tame
  have tFR : Tame (lwWxSizes d L W 0 hL) FR := by
    rw [hFR]; bwo_tame
  -- the pointwise relations
  have hw : ∀ ω', SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) p.1 =
      baG (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t x x ω' - BAlwM d L W g0 E m x x := by
    intro ω'
    rw [BAExpandW_sedge_val_blue p.1 hσ _ ω', hc, hx, hy]
    simp
  have hΓ : ∀ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi) = K * FL ω' := by
    intro ω'
    rw [BAExpandW_term_eq, lwSplit_prod Γ.solid _ p hp, hw ω']
    simp only [hFL]
    rw [hf ω']
  have hKs : ∀ s : List (SEdge (Ex ⊕ Ix)), BAExpandW_K ({ Γ with solid := s } : BAGraph Ex Ix)
      (BAlwM d L W g0 E m) (Matrix.of (BAlwS d L W t)) (Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m)
      ((g0 : ℂ) • PsiI d L W) (Sum.elim ℓe ℓi) = K := fun s => rfl
  have hsedge : ∀ e : SEdge (Ex ⊕ Ix), Tame1 (lwWxSizes d L W 0 hL) 0
      (fun ω' => SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) e) := fun e =>
    BAExpandW_sedge_val_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) (g0 := g0) (z := ztOf m E t) (u := t)
      (M := BAlwM d L W g0 E m) (S := Matrix.of (BAlwS d L W t))
      (Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 E t m) (gPsi := (g0 : ℂ) • PsiI d L W) hz e _
  have hdh : ∀ (α w : Idx d L W) ω', dhSample (lwWxSizes d L W 0 hL) 0 t α w
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω' =
      ((lwSplit p.2).map fun q =>
        (if q.1.σ then -((BAWeightOp_sd hL g0 E t m ω').G (Sum.elim ℓe ℓi q.1.src) α *
            (BAWeightOp_sd hL g0 E t m ω').G w (Sum.elim ℓe ℓi q.1.dst))
          else -(star ((BAWeightOp_sd hL g0 E t m ω').G (Sum.elim ℓe ℓi q.1.src) w) *
            star ((BAWeightOp_sd hL g0 E t m ω').G α (Sum.elim ℓe ℓi q.1.dst)))) *
        (q.2.map (SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi))).prod).sum := by
    intro α w ω'
    have hfun : baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) = fun ω' =>
        (p.2.map fun a => SEdge.val (BAWeightOp_sd hL g0 E t m ω').toLData (Sum.elim ℓe ℓi) a).prod := funext hf
    rw [hfun, lwStein_dh_listProd p.2 (fun e _ => hsedge e)]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [BAExpandW_dh_sedge_val hz ht q.1 α w (Sum.elim ℓe ℓi) ω']
    rfl
  have hR : ∀ ω', BAWeightOp_R Γ p (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi = K * FR ω' := by
    intro ω'
    have h := BAWeightOp_pathwise Γ p hxx (BAWeightOp_sd hL g0 E t m ω') (BAlwW d L W g0 E t m)
      (fun a b => BAWeightOp_W_sub_one hL g0 E t m hSelf ht.le ht1 a b) ℓe ℓi K
      (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0) ω')
      (fun β α => dhSample (lwWxSizes d L W 0 hL) 0 t β α
        (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω')
      (fun s => by rw [BAExpandW_term_eq, hKs s]) (hf ω').symm
      (fun β α => hdh β α ω')
    rw [hx] at h
    exact h
  -- transport to `PF` and `baLweight_holds`
  have hLint : ∫ ω, BAlweightL d L W g0 E t m P0 x ω ∂(PF d L W 0) =
      ∫ ω', FL ω' ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    refine lwWx_integral hL tFL.cont fun ω' => ?_
    unfold BAlweightL BAlwGc
    rw [hFL, ← baWx_baPoly hL g0 E t m ω' P0]
    rfl
  have hRint : ∫ ω, BAlweightR d L W g0 E t m P0 x ω ∂(PF d L W 0) =
      ∫ ω', FR ω' ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    refine lwWx_integral hL tFR.cont fun ω' => ?_
    have hdf : ∀ β α : Idx d L W, BAlwdf d L W g0 E t m P0 (Sizes.slice (lwWxSizes d L W 0 hL) 0 ω') β α =
        dhSample (lwWxSizes d L W 0 hL) 0 t β α
          (baPoly (lwWxSizes d L W 0 hL) 0 g0 (ztOf m E t) t (lwWxRename d L W P0)) ω' :=
      fun β α => (baWx_dh hL hz ht g0 β α ω' P0).symm
    unfold BAlweightR BAlwGc
    simp only [hdf, ← baWx_baPoly hL g0 E t m ω' P0]
    rw [hFR]
    rfl
  have key := baLweight_holds d L W hL g0 E t m hSelf ht.le ht1 P0 x
  refine ⟨?_, ?_⟩
  · have : (fun ω' => BAWeightOp_R Γ p (BAWeightOp_sd hL g0 E t m ω') ℓe ℓi) = fun ω' => K * FR ω' := funext hR
    rw [this]
    exact (Tame.integrable hG tFR).const_mul K
  · simp_rw [hΓ, hR]
    rw [integral_const_mul, integral_const_mul, ← hLint, ← hRint, key]

end Core


section Assembly

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The expectation of the value of a graph with `k = 2` new internal vertices, summed over the labels. -/
private theorem BAWeightOp_val2 (T : BAGraph E (I ⊕ Fin 2)) (D : BALData ι) (ℓe : E → ι) :
    T.val D ℓe = ∑ ℓi : I → ι, ∑ α, ∑ β, T.term D (owxLab2 ℓe ℓi α β) := by
  unfold BAGraph.val
  exact owx_sum_fin2 (fun ℓ' => T.term D (Sum.elim ℓe ℓ'))

private theorem BAWeightOp_val4 (T : BAGraph E (I ⊕ Fin 4)) (D : BALData ι) (ℓe : E → ι) :
    T.val D ℓe = ∑ ℓi : I → ι, ∑ z, ∑ y, ∑ α, ∑ β, T.term D (BAWeightOp_lab4 ℓe ℓi z y α β) := by
  unfold BAGraph.val
  exact BAWeightOp_sum_fin4 (fun ℓ' => T.term D (Sum.elim ℓe ℓ'))

/-- The value of the two lists is the sum over the labels of the old internal vertices of `BAWeightOp_R`. -/
private theorem BAWeightOp_baSum_eq (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓe : E → ι) :
    baSum (Γ.lw2 p) D ℓe + baSum (Γ.lw4 p) D ℓe = ∑ ℓi : I → ι, BAWeightOp_R Γ p D ℓe ℓi := by
  unfold BAWeightOp_R baSum
  rw [Finset.sum_add_distrib]
  congr 1
  · have e : ((Γ.lw2 p).map fun T => T.val D ℓe) =
        (Γ.lw2 p).map fun T => ∑ ℓi : I → ι, ∑ α, ∑ β, T.term D (owxLab2 ℓe ℓi α β) :=
      List.map_congr_left fun T _ => BAWeightOp_val2 T D ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := ι)]
  · have e : ((Γ.lw4 p).map fun T => T.val D ℓe) =
        (Γ.lw4 p).map fun T => ∑ ℓi : I → ι, ∑ z, ∑ y, ∑ α, ∑ β, T.term D (BAWeightOp_lab4 ℓe ℓi z y α β) :=
      List.map_congr_left fun T _ => BAWeightOp_val4 T D ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← lwStein_sum_list (β := ι)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := ι)]

/-- At `S = 0` every term of a generic extension with a black waved edge vanishes. -/
private theorem BAWeightOp_ext_term_zero (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (D : BALData ι) (hS : D.S = 0)
    (hw : ∃ e ∈ w, e.col = false) (ℓ' : E ⊕ (I ⊕ Fin k) → ι) :
    (BAGraph.ext k Γ rest s w md).term D ℓ' = 0 := by
  obtain ⟨e, he, hc⟩ := hw
  have h0 : WEdge.val D.toLData ℓ' e = 0 := by simp [WEdge.val, hc, hS]
  rw [BAWeightOp_ext_term, List.prod_eq_zero (List.mem_map.2 ⟨e, he, h0⟩)]
  simp

/-- At `S = 0` the values of all terms of `lw2` and `lw4` vanish. -/
private theorem BAWeightOp_baSum_zero (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (hS : D.S = 0) (ℓe : E → ι) : baSum (Γ.lw2 p) D ℓe + baSum (Γ.lw4 p) D ℓe = 0 := by
  have h2 : ∀ T ∈ Γ.lw2 p, T.val D ℓe = 0 := by
    intro T hT
    have hT' : ∀ ℓ' : E ⊕ (I ⊕ Fin 2) → ι, T.term D ℓ' = 0 := by
      rw [BAWeightOp_lw2_eq] at hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact BAWeightOp_ext_term_zero 2 Γ _ _ _ _ D hS ⟨bpW false (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
      · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hT
        exact BAWeightOp_ext_term_zero 2 Γ _ _ _ _ D hS ⟨bpW false (bpv 0) (bpv 1), List.mem_cons_self, rfl⟩
    unfold BAGraph.val
    exact Finset.sum_eq_zero fun ℓi _ => hT' _
  have h4 : ∀ T ∈ Γ.lw4 p, T.val D ℓe = 0 := by
    intro T hT
    have hT' : ∀ ℓ' : E ⊕ (I ⊕ Fin 4) → ι, T.term D ℓ' = 0 := by
      rw [BAWeightOp_lw4_eq] at hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact BAWeightOp_ext_term_zero 4 Γ _ _ _ _ D hS
          ⟨bpW false (bpv 2) (bpv 3), List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
      · obtain ⟨q, _, rfl⟩ := List.mem_map.1 hT
        exact BAWeightOp_ext_term_zero 4 Γ _ _ _ _ D hS
          ⟨bpW false (bpv 2) (bpv 3), List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
    unfold BAGraph.val
    exact Finset.sum_eq_zero fun ℓi _ => hT' _
  have e2 : baSum (Γ.lw2 p) D ℓe = 0 := List.sum_eq_zero fun a ha => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha
    exact h2 T hT
  have e4 : baSum (Γ.lw4 p) D ℓe = 0 := List.sum_eq_zero fun a ha => by
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha
    exact h4 T hT
  rw [e2, e4, add_zero]

end Assembly


section Final

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The value of a graph is tame as a function of the sample (a finite sum of tame terms). -/
private theorem BAWeightOp_val_tame {sz : Sizes d} {n : ℕ} {g0 : ℝ} {z : ℂ} {u : ℝ}
    {M S Sp gPsi : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hz : z.im ≠ 0)
    {E I : Type} [Fintype I] [DecidableEq I] (T : BAGraph E I) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω => T.val (BAExpandW_sampleData sz n g0 z u M S Sp gPsi ω) ℓe) := by
  unfold BAGraph.val
  exact Tame.sum _ fun ℓi _ => (BAExpandW_term_tame1 hz T _).tame

/-- **`lem_lweight` as a graph operation on the sequence space.** -/
private theorem BAWeightOp_val_seq (hL : 3 ≤ L) (g0 E t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (E : ℂ) m)
    (ht : 0 < t) (ht1 : t < 1) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]
    (Γ : BAGraph Ex Ix) (p : SEdge (Ex ⊕ Ix) × List (SEdge (Ex ⊕ Ix))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : p.1.σ = true) (hc : p.1.circ = true) (hxx : p.1.src = p.1.dst) (ℓe : Ex → Idx d L W) :
    ∫ ω', Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
      ∫ ω', (baSum (Γ.lw2 p) (BAWeightOp_sd hL g0 E t m ω') ℓe +
        baSum (Γ.lw4 p) (BAWeightOp_sd hL g0 E t m ω') ℓe) ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
  classical
  have hm : 0 < m.im := hSelf.1
  have hz : (ztOf m E t).im ≠ 0 := by
    rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
  have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
  have hcore := fun ℓi => BAWeightOp_core hL g0 E t m hSelf ht ht1 Γ p hp hσ hc hxx ℓe ℓi
  have hL1 : ∫ ω', Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) =
      ∑ ℓi : Ix → Idx d L W, ∫ ω', Γ.term (BAWeightOp_sd hL g0 E t m ω') (Sum.elim ℓe ℓi)
        ∂(Sizes.seqP (lwWxSizes d L W 0 hL)) := by
    unfold BAGraph.val
    exact integral_finsetSum _ fun ℓi _ =>
      Tame.integrable hG (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz Γ _).tame
  simp_rw [BAWeightOp_baSum_eq]
  rw [hL1, integral_finsetSum _ fun ℓi _ => (hcore ℓi).1]
  exact Finset.sum_congr rfl fun ℓi _ => (hcore ℓi).2


/-- **Target 2: `lem_lweight` (B.19) as a graph operation** (`B:376-387`; the first conjunct of `BAexpFrameE`, probe
`t/T2395:RBM3D/Probe/T2395Pins.lean:244-251`): for a circled blue self-loop `p.1 = Ǧ_{xx}` of `Γ`
(`p ∈ lwSplit Γ.solid`), `𝔼 Γ.val = 𝔼 (Σ_{Δ ∈ lw2} Δ.val + Σ_{Δ ∈ lw4} Δ.val)` at the model data `BAlwData` over
`PF d L W 0`.  For `0 < t < 1`: `baLweight_holds` (the identity of `𝔼 Ǧ_{xx} f`) with `W = 1 + M⁺ (S W)`
(`BAWeightOp_W_sub_one`), on the sequence space and transported by `lwWx_integral`; for `t = 0` both sides vanish
(`Ǧ = 0`, `S = 0`). -/
theorem baExpFrame_lw (d : ℕ) : ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ),
    RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 →
    ∀ {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix] (Γ : BAGraph Ex Ix)
      (ℓe : Ex → Idx d L W), ∀ p ∈ lwSplit Γ.solid, p.1.σ = true → p.1.circ = true → p.1.src = p.1.dst →
      ∫ ω, Γ.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) =
        ∫ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 Em t m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 Em t m ω) ℓe
          ∂(PF d L W 0) := by
  intro L W _ _ hL g0 E t m hSelf ht0 ht1 Ex Ix _ _ _ _ Γ ℓe p hp hσ hc hxx
  have hm : 0 < m.im := hSelf.1
  rcases ht0.eq_or_lt with rfl | ht
  · -- `t = 0`: `Ǧ = 0` on the left, `S = 0` on the right
    have hSz : (BAlwData d L W g0 E 0 m (fun _ => 0)).S = 0 := by
      ext i j
      simp [BAlwData, BAlwS]
    have hR : ∀ ω, baSum (Γ.lw2 p) (BAlwData d L W g0 E 0 m ω) ℓe + baSum (Γ.lw4 p) (BAlwData d L W g0 E 0 m ω) ℓe = 0 :=
      fun ω => BAWeightOp_baSum_zero Γ p _ (by simpa [BAlwData] using hSz) ℓe
    have hLz : ∀ ω, Γ.val (BAlwData d L W g0 E 0 m ω) ℓe = 0 := by
      intro ω
      unfold BAGraph.val
      refine Finset.sum_eq_zero fun ℓi _ => ?_
      have h0 : SEdge.val (BAlwData d L W g0 E 0 m ω).toLData (Sum.elim ℓe ℓi) p.1 = 0 := by
        have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 E m ω
          (Sum.elim ℓe ℓi p.1.src) (Sum.elim ℓe ℓi p.1.dst)
        simp only [SEdge.val, hσ, hc, BAlwData, ite_true]
        simpa [BAlwGc] using this
      simp only [BAGraph.term, LGraph.term, lwSplit_prod Γ.solid _ p hp, h0]
      simp
    simp [hLz, hR]
  · have hz : (ztOf m E t).im ≠ 0 := by
      rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'
    have key := BAWeightOp_val_seq hL g0 E t m hSelf ht ht1 Γ p hp hσ hc hxx ℓe
    have hF1 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) =>
        Γ.val (BAWeightOp_sd hL g0 E t m ω') ℓe) :=
      (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz Γ ℓe).cont
    have hF2 : Continuous (fun ω' : Sizes.SeqΩ (lwWxSizes d L W 0 hL) =>
        baSum (Γ.lw2 p) (BAWeightOp_sd hL g0 E t m ω') ℓe + baSum (Γ.lw4 p) (BAWeightOp_sd hL g0 E t m ω') ℓe) :=
      (continuous_list_sum _ fun T _ =>
        (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓe).cont).add
        (continuous_list_sum _ fun T _ =>
          (BAWeightOp_val_tame (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓe).cont)
    exact (lwWx_integral hL hF1 fun ω' => rfl).trans (key.trans (lwWx_integral hL hF2 fun ω' => rfl).symm)

end Final

/-! ## 4. Target 3: counters and order -/

/-! ### 4.1 Generic closure lemmas (local copies of the private lemmas of `Graph/BAExpandWOrd`, with the pendant part
split into an attached part `P` and unattached classes) -/

section Generic

private theorem BAWeightOp_rtg_symm {α : Type*} (r : α → α → Bool) (hs : ∀ u v, r u v = r v u) {v w : α}
    (h : Relation.ReflTransGen (fun a b => r a b = true) v w) :
    Relation.ReflTransGen (fun a b => r a b = true) w v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (by rw [hs]; exact hbc) ih

/-- The class of an attached vertex `v` of a relation `r'` that extends `r` by pendant vertices (`ρ` retracts the attached
new vertices onto old ones; the edges at unattached vertices stay among unattached ones). -/
private theorem BAWeightOp_rtg_ext {V V' : Type*} (r : V → V → Bool) (r' : V' → V' → Bool)
    (hs' : ∀ u v, r' u v = r' v u) (emb : V → V') (ρ : V' → V) (P : V' → Prop)
    (e1 : ∀ u w, r u w = true → r' (emb u) (emb w) = true)
    (e2 : ∀ b c, r' b c = true → (P b ∧ P c ∧ (ρ b = ρ c ∨ r (ρ b) (ρ c) = true)) ∨ (¬ P b ∧ ¬ P c))
    (e3 : ∀ w, P w → Relation.ReflTransGen (fun a b => r' a b = true) w (emb (ρ w))) (v w : V') (hv : P v) :
    Relation.ReflTransGen (fun a b => r' a b = true) v w ↔
      w = v ∨ (P w ∧ Relation.ReflTransGen (fun a b => r a b = true) (ρ v) (ρ w)) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
      right
      rcases e2 b c hbc with ⟨hPb, hPc, hbc'⟩ | ⟨hPb, _⟩
      · refine ⟨hPc, ?_⟩
        rcases ih with rfl | ⟨_, hrt⟩
        · rcases hbc' with h | h
          · rw [h]
          · exact Relation.ReflTransGen.single h
        · rcases hbc' with h | h
          · rw [← h]; exact hrt
          · exact hrt.tail h
      · rcases ih with rfl | ⟨hPb', _⟩
        · exact absurd hv hPb
        · exact absurd hPb' hPb
  · rintro (rfl | ⟨hPw, h⟩)
    · exact Relation.ReflTransGen.refl
    · have h1 : Relation.ReflTransGen (fun a b => r' a b = true) (emb (ρ v)) (emb (ρ w)) :=
        Relation.ReflTransGen.lift emb (fun a b hab => e1 a b hab) _ _ h
      exact (e3 v hv).trans (h1.trans (BAWeightOp_rtg_symm r' hs' (e3 w hPw)))

/-- The number of classes without a "bad" element (the shape of `BAGraph.nA`, `BAGraph.nM`). -/
private def BAWeightOp_cnt {V : Type*} [Fintype V] [DecidableEq V] (i : V → Bool) (cl : V → Finset V) : ℕ :=
  ((Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl).card

/-- The count of internal classes of a pendant extension: the classes of the attached vertices are the `G`-images of the
classes of `cl`, the unattached vertices form `k` further internal classes. -/
private theorem BAWeightOp_cnt_ext {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (i : V → Bool) (i' : V' → Bool) (cl : V → Finset V) (cl' : V' → Finset V') (emb : V → V') (ρ : V' → V)
    (P : V' → Prop) [DecidablePred P] (k : ℕ) (hρ : ∀ a, ρ (emb a) = a) (hi1 : ∀ a, i' (emb a) = i a)
    (hi2 : ∀ w, i (ρ w) = true → i' w = true) (hP1 : ∀ a, P (emb a)) (hself : ∀ v, v ∈ cl v)
    (hcl : ∀ v, P v → ∀ w, w ∈ cl' v ↔ w = v ∨ (P w ∧ ρ w ∈ cl (ρ v)))
    (hnew : ((Finset.univ.filter (fun v => ¬ P v)).image cl').card = k)
    (hnP : ∀ v, ¬ P v → ∀ w ∈ cl' v, ¬ P w ∧ i' w = true) (hnself : ∀ v, ¬ P v → v ∈ cl' v) :
    BAWeightOp_cnt i' cl' = BAWeightOp_cnt i cl + k := by
  classical
  unfold BAWeightOp_cnt
  set G : Finset V → Finset V' := fun A => Finset.univ.filter (fun w => P w ∧ ρ w ∈ A) with hG
  have h2 : ∀ v, P v → cl' v = G (cl (ρ v)) := by
    intro v hv
    ext w
    rw [hcl v hv]
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | ⟨hw, h⟩)
      · exact ⟨hv, hself _⟩
      · exact ⟨hw, h⟩
    · rintro ⟨hw, h⟩
      exact Or.inr ⟨hw, h⟩
  have hGinj : Function.Injective G := by
    intro A A' h
    have hA : ∀ B : Finset V, B = (G B).image ρ := by
      intro B
      ext a
      simp only [hG, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha
        exact ⟨emb a, ⟨hP1 a, by rw [hρ]; exact ha⟩, hρ a⟩
      · rintro ⟨w, ⟨_, hw⟩, rfl⟩
        exact hw
    rw [hA A, hA A', h]
  have himg : (Finset.univ.filter (fun v : V' => ∀ w ∈ cl' v, i' w = true)).image cl' =
      ((Finset.univ.filter (fun v : V => ∀ w ∈ cl v, i w = true)).image cl).image G ∪
        (Finset.univ.filter (fun w => ¬ P w)).image cl' := by
    ext T
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨v, hv, rfl⟩
      by_cases hPv : P v
      · left
        refine ⟨cl (ρ v), ⟨ρ v, ?_, rfl⟩, (h2 v hPv).symm⟩
        intro a ha
        have : emb a ∈ cl' v := by
          rw [h2 v hPv]
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hP1 a, by rw [hρ]; exact ha⟩
        have := hv _ this
        rwa [hi1] at this
      · right
        exact ⟨v, hPv, rfl⟩
    · rintro (⟨_, ⟨u, hu, rfl⟩, rfl⟩ | ⟨v, hv, rfl⟩)
      · refine ⟨emb u, ?_, ?_⟩
        · intro w hw
          rw [h2 _ (hP1 u), hρ] at hw
          simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hw
          exact hi2 w (hu _ hw.2)
        · rw [h2 _ (hP1 u), hρ]
      · exact ⟨v, fun w hw => (hnP v hv w hw).2, rfl⟩
  rw [himg, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ hGinj, hnew]
  rw [Finset.disjoint_left]
  intro T hT1 hT2
  obtain ⟨A, _, rfl⟩ := Finset.mem_image.1 hT1
  obtain ⟨v, hv, hvT⟩ := Finset.mem_image.1 hT2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  have : v ∈ G A := by rw [← hvT]; exact hnself v hv
  simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at this
  exact hv this.1

end Generic

/-! ### 4.2 Atoms under added dotted edges (local copies) -/

section AtomMono

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

private theorem BAWeightOp_atomAdj_comm (Γ : BAGraph E I) (u v : E ⊕ I) :
    Γ.atomAdj u v = Γ.atomAdj v u := by
  simp only [BAGraph.atomAdj, or_comm]

private theorem BAWeightOp_adj_comm (Γ : BAGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [BAGraph.adj, BAWeightOp_atomAdj_comm Γ u v, LGraph.adj, or_comm]

private theorem BAWeightOp_self_mem_atom (Γ : BAGraph E I) (v : E ⊕ I) : v ∈ Γ.atom v := by
  rw [BAGraph.mem_atom_iff]

private theorem BAWeightOp_atom_eq_of_mem (Γ : BAGraph E I) {v w : E ⊕ I} (h : w ∈ Γ.atom v) :
    Γ.atom w = Γ.atom v := by
  rw [BAGraph.mem_atom_iff] at h
  ext x
  rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
  constructor
  · intro hx; exact h.trans hx
  · intro hx
    exact (BAWeightOp_rtg_symm (fun a b => Γ.atomAdj a b) (BAWeightOp_atomAdj_comm Γ) h).trans hx

/-- Adding atom edges makes the atoms bigger. -/
private theorem BAWeightOp_atom_subset (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) (v : E ⊕ I) : Γ₁.atom v ⊆ Γ₂.atom v := by
  intro w hw
  rw [BAGraph.mem_atom_iff] at hw ⊢
  exact Relation.ReflTransGen.mono (fun a b hab => h a b hab) _ _ hw

/-- **Adding `=`-, `Ψ`- or `M`-dotted edges never increases `n_A`** (merging two atoms never creates an internal
one). -/
private theorem BAWeightOp_nA_le (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) : Γ₂.nA ≤ Γ₁.nA := by
  classical
  unfold BAGraph.nA
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if hA : A.Nonempty then Γ₂.atom hA.choose else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₂.atom v, w.isRight = true)).image Γ₂.atom ⊆
      ((Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₁.atom v, w.isRight = true)).image Γ₁.atom).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine Finset.mem_image.2 ⟨Γ₁.atom v, Finset.mem_image.2 ⟨v, ?_, rfl⟩, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun w hw => hv w (BAWeightOp_atom_subset Γ₁ Γ₂ h v hw)
    · have hne : (Γ₁.atom v).Nonempty := ⟨v, BAWeightOp_self_mem_atom Γ₁ v⟩
      simp only [hF, hne, ↓reduceDIte]
      exact BAWeightOp_atom_eq_of_mem Γ₂ (BAWeightOp_atom_subset Γ₁ Γ₂ h v hne.choose_spec)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- **A singleton internal atom `{b}` that is joined to another vertex loses one internal atom.** -/
private theorem BAWeightOp_nA_lt (Γ₁ Γ₂ : BAGraph E I)
    (h : ∀ u v, Γ₁.atomAdj u v = true → Γ₂.atomAdj u v = true) (b : E ⊕ I) (hb : b.isRight = true)
    (hiso : ∀ w, Γ₁.atomAdj b w = false) (u : E ⊕ I) (hu : u ≠ b) (hbu : Γ₂.atomAdj b u = true) :
    Γ₂.nA + 1 ≤ Γ₁.nA := by
  classical
  have hb1 : Γ₁.atom b = {b} := by
    ext w
    rw [BAGraph.mem_atom_iff, Finset.mem_singleton]
    constructor
    · intro hw
      induction hw with
      | refl => rfl
      | @tail b' c _ hbc ih =>
        subst ih
        rw [hiso c] at hbc
        exact absurd hbc (by simp)
    · rintro rfl; exact Relation.ReflTransGen.refl
  unfold BAGraph.nA
  set IA₁ := (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₁.atom v, w.isRight = true)).image Γ₁.atom with hIA₁
  have hbmem : ({b} : Finset (E ⊕ I)) ∈ IA₁ := by
    rw [hIA₁, Finset.mem_image]
    refine ⟨b, ?_, hb1⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro w hw
    rw [hb1, Finset.mem_singleton] at hw
    rw [hw]; exact hb
  set F : Finset (E ⊕ I) → Finset (E ⊕ I) := fun A =>
    if hA : A.Nonempty then Γ₂.atom hA.choose else ∅ with hF
  have hsub : (Finset.univ.filter (fun v : E ⊕ I => ∀ w ∈ Γ₂.atom v, w.isRight = true)).image Γ₂.atom ⊆
      (IA₁.erase {b}).image F := by
    intro T hT
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    set a : E ⊕ I := if v = b then u else v with ha
    have haT : a ∈ Γ₂.atom v := by
      by_cases hvb : v = b
      · subst hvb
        simp only [ha, ↓reduceIte]
        rw [BAGraph.mem_atom_iff]
        exact Relation.ReflTransGen.single hbu
      · simp only [ha, hvb, ↓reduceIte]; exact BAWeightOp_self_mem_atom Γ₂ v
    have hab : a ≠ b := by
      by_cases hvb : v = b
      · simp only [ha, hvb, ↓reduceIte]; exact hu
      · simp only [ha, hvb, ↓reduceIte]; exact hvb
    have hsubT : Γ₁.atom a ⊆ Γ₂.atom v := by
      intro w hw
      have := BAWeightOp_atom_subset Γ₁ Γ₂ h a hw
      rwa [BAWeightOp_atom_eq_of_mem Γ₂ haT] at this
    refine Finset.mem_image.2 ⟨Γ₁.atom a, Finset.mem_erase.2 ⟨?_, Finset.mem_image.2 ⟨a, ?_, rfl⟩⟩, ?_⟩
    · intro hAb
      have := BAWeightOp_self_mem_atom Γ₁ a
      rw [hAb, Finset.mem_singleton] at this
      exact hab this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun w hw => hv w (hsubT hw)
    · have hne : (Γ₁.atom a).Nonempty := ⟨a, BAWeightOp_self_mem_atom Γ₁ a⟩
      simp only [hF, hne, ↓reduceDIte]
      exact BAWeightOp_atom_eq_of_mem Γ₂ (hsubT hne.choose_spec)
  have h1 := (Finset.card_le_card hsub).trans Finset.card_image_le
  have h2 := Finset.card_erase_of_mem hbmem
  have h3 : 0 < IA₁.card := Finset.card_pos.2 ⟨_, hbmem⟩
  omega

end AtomMono

/-! ### 4.3 The extension by `k` vertices: atoms, molecules, counters -/

section ExtGraph

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The atom edges of a generic extension: those of `Γ` (renamed) and the new `M`-dotted edges. -/
private theorem BAWeightOp_ext_atomAdj (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (u v : E ⊕ (I ⊕ Fin k)) :
    (BAGraph.ext k Γ rest s w md).atomAdj u v = true ↔
      (∃ a b, u = owxEmb k a ∧ v = owxEmb k b ∧ Γ.atomAdj a b = true) ∨
        ∃ e ∈ md, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u) := by
  simp only [BAGraph.atomAdj, BAGraph.ext, LGraph.owxExt, Bool.or_eq_true,
    List.any_eq_true, List.mem_map, List.mem_append, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro (((⟨_, ⟨a, ha, rfl⟩, h1, h2⟩ | ⟨_, ⟨a, ha, rfl⟩, h2⟩) | ⟨e, h1 | ⟨a, ha, rfl⟩, h2⟩))
    · left
      simp only [DEdge.map] at h1 h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl (Or.inl ⟨a, ha, h1, Or.inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl (Or.inl ⟨a, ha, h1, Or.inr ⟨rfl, rfl⟩⟩)⟩
    · left
      simp only [BAPsiEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl (Or.inr ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩)⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl (Or.inr ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩)⟩
    · exact Or.inr ⟨e, h1, h2⟩
    · left
      simp only [BAMEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inr ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inr ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro (⟨a, b, rfl, rfl, ((⟨e, he, h1, h2⟩ | ⟨e, he, h2⟩) | ⟨e, he, h2⟩)⟩ | ⟨e, he, h2⟩)
    · left; left
      refine ⟨DEdge.map (owxEmb k) e, ⟨e, he, rfl⟩, h1, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · left; right
      refine ⟨BAPsiEdge.map (owxEmb k) e, ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      refine ⟨BAMEdge.map (owxEmb k) e, Or.inr ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      exact ⟨e, Or.inl he, h2⟩


/-- The waved and `=`-dotted edges of a generic extension: those of `Γ` (renamed) and the new waved edges. -/
private theorem BAWeightOp_ext_ladj (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (u v : E ⊕ (I ⊕ Fin k)) :
    (BAGraph.ext k Γ rest s w md).toLGraph.adj u v = true ↔
      (∃ a b, u = owxEmb k a ∧ v = owxEmb k b ∧ Γ.toLGraph.adj a b = true) ∨
        ∃ e ∈ w, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u) := by
  simp only [LGraph.adj, BAGraph.ext, LGraph.owxExt, Bool.or_eq_true,
    List.any_eq_true, List.mem_map, List.mem_append, decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · rintro ((⟨e, ⟨a, ha, rfl⟩ | h1, h2⟩) | ⟨_, ⟨a, ha, rfl⟩, h1, h2⟩)
    · left
      simp only [WEdge.map] at h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inl ⟨a, ha, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inl ⟨a, ha, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact Or.inr ⟨e, h1, h2⟩
    · left
      simp only [DEdge.map] at h1 h2
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨a.x, a.y, rfl, rfl, Or.inr ⟨a, ha, h1, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨a.y, a.x, rfl, rfl, Or.inr ⟨a, ha, h1, Or.inr ⟨rfl, rfl⟩⟩⟩
  · rintro (⟨a, b, rfl, rfl, (⟨e, he, h2⟩ | ⟨e, he, h1, h2⟩)⟩ | ⟨e, he, h2⟩)
    · left
      refine ⟨WEdge.map (owxEmb k) e, Or.inl ⟨e, he, rfl⟩, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · right
      refine ⟨DEdge.map (owxEmb k) e, ⟨e, he, rfl⟩, h1, ?_⟩
      rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    · left
      exact ⟨e, Or.inr he, h2⟩

/-- The molecule edges of a generic extension. -/
private theorem BAWeightOp_ext_adj (k : ℕ) (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin k)))) (w : List (WEdge (E ⊕ (I ⊕ Fin k))))
    (md : List (BAMEdge (E ⊕ (I ⊕ Fin k)))) (u v : E ⊕ (I ⊕ Fin k)) :
    (BAGraph.ext k Γ rest s w md).adj u v = true ↔
      (∃ a b, u = owxEmb k a ∧ v = owxEmb k b ∧ Γ.adj a b = true) ∨
        (∃ e ∈ w, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u)) ∨
        ∃ e ∈ md, (e.x = u ∧ e.y = v) ∨ (e.x = v ∧ e.y = u) := by
  simp only [BAGraph.adj, Bool.or_eq_true, BAWeightOp_ext_ladj, BAWeightOp_ext_atomAdj]
  constructor
  · rintro ((⟨a, b, h1, h2, h3⟩ | h) | (⟨a, b, h1, h2, h3⟩ | h))
    · exact Or.inl ⟨a, b, h1, h2, Or.inl h3⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl ⟨a, b, h1, h2, Or.inr h3⟩
    · exact Or.inr (Or.inr h)
  · rintro (⟨a, b, h1, h2, h3 | h3⟩ | h | h)
    · exact Or.inl (Or.inl ⟨a, b, h1, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨a, b, h1, h2, h3⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inr h)

end ExtGraph


/-! ### 4.4 The shape of the terms of `lw4` -/

section Ext4

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The shape common to the leaf and the derivative terms of `lw4`: `Γ` renamed by `owxEmb 4`, its solid edges replaced
by `rest`, the solid edges `s`, the waved edges `S⁺_{zy}`, `S_{αβ}` and the `M`-dotted edges `M_{xz}`, `M_{zx}`, `M_{yα}`
appended (`z, y, α, β = bpv 0..3`). -/
private def BAWeightOp_ext4 (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) : BAGraph E (I ⊕ Fin 4) :=
  BAGraph.ext 4 Γ rest s [bpW true (bpv 0) (bpv 1), bpW false (bpv 2) (bpv 3)]
    [bpM (owxEmb 4 x) (bpv 0), bpM (bpv 0) (owxEmb 4 x), bpM (bpv 1) (bpv 2)]

/-- The retraction of the vertices of the extension: `z, y, α, β` go to `x`. -/
private def BAWeightOp_rho (x : E ⊕ I) : E ⊕ (I ⊕ Fin 4) → E ⊕ I
  | Sum.inl e => Sum.inl e
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr _) => x

private theorem BAWeightOp_rho_emb (x : E ⊕ I) (a : E ⊕ I) : BAWeightOp_rho x (owxEmb 4 a) = a := by
  rcases a with a | a <;> rfl

private theorem BAWeightOp_isRight_emb (a : E ⊕ I) : (owxEmb 4 a : E ⊕ (I ⊕ Fin 4)).isRight = a.isRight := by
  rcases a with a | a <;> rfl

private theorem BAWeightOp_isRight_rho (x : E ⊕ I) (w : E ⊕ (I ⊕ Fin 4))
    (h : (BAWeightOp_rho x w).isRight = true) : w.isRight = true := by
  rcases w with e | i | j
  · simp [BAWeightOp_rho] at h
  · rfl
  · rfl

private theorem BAWeightOp_emb_ne (a : E ⊕ I) (j : Fin 4) : (owxEmb 4 a : E ⊕ (I ⊕ Fin 4)) ≠ bpv j := by
  rcases a with a | a <;> simp [owxEmb]

/-- The atom edges of the extension: those of `Γ` (renamed), `x – z` and `y – α`. -/
private theorem BAWeightOp_ext4_atomAdj (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) (u v : E ⊕ (I ⊕ Fin 4)) :
    (BAWeightOp_ext4 Γ rest s x).atomAdj u v = true ↔
      (∃ a b, u = owxEmb 4 a ∧ v = owxEmb 4 b ∧ Γ.atomAdj a b = true) ∨
        (u = owxEmb 4 x ∧ v = bpv 0) ∨ (u = bpv 0 ∧ v = owxEmb 4 x) ∨ (u = bpv 1 ∧ v = bpv 2) ∨
        (u = bpv 2 ∧ v = bpv 1) := by
  rw [BAWeightOp_ext4, BAWeightOp_ext_atomAdj]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, bpM]
  constructor
  · rintro (h | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩))
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h2.symm, h1.symm⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h1.symm, h2.symm⟩))
    · exact Or.inr (Or.inl ⟨h2.symm, h1.symm⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)))
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl (Or.inl ⟨h1.symm, h2.symm⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h1.symm, h2.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)))


/-- The molecule edges of the extension: those of `Γ` (renamed), `z – y`, `α – β`, `x – z` and `y – α`. -/
private theorem BAWeightOp_ext4_adj (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) (u v : E ⊕ (I ⊕ Fin 4)) :
    (BAWeightOp_ext4 Γ rest s x).adj u v = true ↔
      (∃ a b, u = owxEmb 4 a ∧ v = owxEmb 4 b ∧ Γ.adj a b = true) ∨
        (u = bpv 0 ∧ v = bpv 1) ∨ (u = bpv 1 ∧ v = bpv 0) ∨ (u = bpv 2 ∧ v = bpv 3) ∨ (u = bpv 3 ∧ v = bpv 2) ∨
        (u = owxEmb 4 x ∧ v = bpv 0) ∨ (u = bpv 0 ∧ v = owxEmb 4 x) ∨ (u = bpv 1 ∧ v = bpv 2) ∨
        (u = bpv 2 ∧ v = bpv 1) := by
  rw [BAWeightOp_ext4, BAWeightOp_ext_adj]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, bpM, bpW]
  constructor
  · rintro (h | ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩) |
      (⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    all_goals (subst h1 h2; simp)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h
    all_goals (subst h1 h2; simp)


/-- **`n_A` of the extension is `n_A Γ + 2`**: `z` joins the atom of `x`, `{y, α}` and `{β}` are two new internal atoms. -/
private theorem BAWeightOp_ext4_nA (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) :
    (BAWeightOp_ext4 Γ rest s x).nA = Γ.nA + 2 := by
  classical
  set Δ := BAWeightOp_ext4 Γ rest s x with hΔ
  -- the unattached classes
  have hcl' : ∀ v : E ⊕ (I ⊕ Fin 4), (v = bpv 1 ∨ v = bpv 2 ∨ v = bpv 3) → ∀ w, w ∈ Δ.atom v ↔
      (v = bpv 3 ∧ w = bpv 3) ∨ (v ≠ bpv 3 ∧ (w = bpv 1 ∨ w = bpv 2)) := by
    intro v hv w
    rw [BAGraph.mem_atom_iff]
    constructor
    · intro h
      induction h with
      | refl => rcases hv with rfl | rfl | rfl <;> simp
      | @tail b c _ hbc ih =>
        rcases (BAWeightOp_ext4_atomAdj Γ rest s x _ _).1 hbc with
          ⟨a, a', rfl, rfl, _⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases ih with ⟨_, h⟩ | ⟨_, h | h⟩ <;> exact absurd h (BAWeightOp_emb_ne _ _)
        · rcases ih with ⟨_, h⟩ | ⟨_, h | h⟩ <;> exact absurd h (BAWeightOp_emb_ne _ _)
        · simp at ih
        · rcases ih with ⟨_, h⟩ | ⟨hv3, _⟩
          · simp at h
          · exact Or.inr ⟨hv3, Or.inr rfl⟩
        · rcases ih with ⟨_, h⟩ | ⟨hv3, _⟩
          · simp at h
          · exact Or.inr ⟨hv3, Or.inl rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨hne, rfl | rfl⟩)
      · exact Relation.ReflTransGen.refl
      · rcases hv with rfl | rfl | rfl
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single ((BAWeightOp_ext4_atomAdj Γ rest s x _ _).2
            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
        · exact absurd rfl hne
      · rcases hv with rfl | rfl | rfl
        · exact Relation.ReflTransGen.single ((BAWeightOp_ext4_atomAdj Γ rest s x _ _).2
            (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
        · exact Relation.ReflTransGen.refl
        · exact absurd rfl hne
  have hy' : Δ.atom (bpv 1) = {bpv 1, bpv 2} := by
    ext w; rw [hcl' _ (Or.inl rfl)]; simp
  have ha' : Δ.atom (bpv 2) = {bpv 1, bpv 2} := by
    ext w; rw [hcl' _ (Or.inr (Or.inl rfl))]; simp
  have hb' : Δ.atom (bpv 3) = {bpv 3} := by
    ext w; rw [hcl' _ (Or.inr (Or.inr rfl))]; simp
  have hnew : ((Finset.univ.filter fun v : E ⊕ (I ⊕ Fin 4) => ¬ (v ≠ bpv 1 ∧ v ≠ bpv 2 ∧ v ≠ bpv 3)).image
      Δ.atom).card = 2 := by
    have : (Finset.univ.filter fun v : E ⊕ (I ⊕ Fin 4) => ¬ (v ≠ bpv 1 ∧ v ≠ bpv 2 ∧ v ≠ bpv 3)) =
        {bpv 1, bpv 2, bpv 3} := by
      ext v; simp; tauto
    rw [this, Finset.image_insert, Finset.image_insert, Finset.image_singleton, hy', ha', hb',
      Finset.insert_eq_of_mem (by simp)]
    exact Finset.card_pair fun h => by
      have := Finset.ext_iff.1 h (bpv 1)
      simp at this
  have hnP : ∀ v : E ⊕ (I ⊕ Fin 4), ¬ (v ≠ bpv 1 ∧ v ≠ bpv 2 ∧ v ≠ bpv 3) → ∀ w ∈ Δ.atom v,
      ¬ (w ≠ bpv 1 ∧ w ≠ bpv 2 ∧ w ≠ bpv 3) ∧ w.isRight = true := by
    intro v hv w hw
    have hv' : v = bpv 1 ∨ v = bpv 2 ∨ v = bpv 3 := by tauto
    rw [hcl' v hv'] at hw
    rcases hw with ⟨_, rfl⟩ | ⟨_, rfl | rfl⟩ <;> simp [bpv]
  -- the attached classes
  have e1 : ∀ u w, Γ.atomAdj u w = true → Δ.atomAdj (owxEmb 4 u) (owxEmb 4 w) = true := fun u w h =>
    (BAWeightOp_ext4_atomAdj Γ rest s x _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩)
  have e2 : ∀ b c, Δ.atomAdj b c = true →
      ((b ≠ bpv 1 ∧ b ≠ bpv 2 ∧ b ≠ bpv 3) ∧ (c ≠ bpv 1 ∧ c ≠ bpv 2 ∧ c ≠ bpv 3) ∧
        (BAWeightOp_rho x b = BAWeightOp_rho x c ∨ Γ.atomAdj (BAWeightOp_rho x b) (BAWeightOp_rho x c) = true)) ∨
      (¬ (b ≠ bpv 1 ∧ b ≠ bpv 2 ∧ b ≠ bpv 3) ∧ ¬ (c ≠ bpv 1 ∧ c ≠ bpv 2 ∧ c ≠ bpv 3)) := by
    intro b c hbc
    rcases (BAWeightOp_ext4_atomAdj Γ rest s x _ _).1 hbc with
      ⟨a, a', rfl, rfl, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨⟨BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _⟩,
        ⟨BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _⟩,
        Or.inr (by rw [BAWeightOp_rho_emb, BAWeightOp_rho_emb]; exact h')⟩
    · exact Or.inl ⟨⟨BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _⟩, by simp,
        Or.inl (by rw [BAWeightOp_rho_emb]; rfl)⟩
    · exact Or.inl ⟨by simp, ⟨BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _⟩,
        Or.inl (by rw [BAWeightOp_rho_emb]; rfl)⟩
    · exact Or.inr ⟨by simp, by simp⟩
    · exact Or.inr ⟨by simp, by simp⟩
  have e3 : ∀ w : E ⊕ (I ⊕ Fin 4), (w ≠ bpv 1 ∧ w ≠ bpv 2 ∧ w ≠ bpv 3) →
      Relation.ReflTransGen (fun a b => Δ.atomAdj a b = true) w (owxEmb 4 (BAWeightOp_rho x w)) := by
    intro w hw
    rcases w with e | i | j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.refl
    · fin_cases j
      · exact Relation.ReflTransGen.single ((BAWeightOp_ext4_atomAdj Γ rest s x _ _).2
          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact absurd rfl hw.1
      · exact absurd rfl hw.2.1
      · exact absurd rfl hw.2.2
  have hcl : ∀ v : E ⊕ (I ⊕ Fin 4), (v ≠ bpv 1 ∧ v ≠ bpv 2 ∧ v ≠ bpv 3) → ∀ w, w ∈ Δ.atom v ↔
      w = v ∨ ((w ≠ bpv 1 ∧ w ≠ bpv 2 ∧ w ≠ bpv 3) ∧ BAWeightOp_rho x w ∈ Γ.atom (BAWeightOp_rho x v)) := by
    intro v hv w
    rw [BAGraph.mem_atom_iff, BAGraph.mem_atom_iff]
    rw [BAWeightOp_rtg_ext (fun a b => Γ.atomAdj a b) (fun a b => Δ.atomAdj a b) (BAWeightOp_atomAdj_comm _)
      (owxEmb 4) (BAWeightOp_rho x) (fun w => w ≠ bpv 1 ∧ w ≠ bpv 2 ∧ w ≠ bpv 3) e1 e2 e3 v w hv]
  have key := BAWeightOp_cnt_ext (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 4) => w.isRight) Γ.atom Δ.atom
    (owxEmb 4) (BAWeightOp_rho x) (fun w => w ≠ bpv 1 ∧ w ≠ bpv 2 ∧ w ≠ bpv 3) 2 (BAWeightOp_rho_emb x)
    BAWeightOp_isRight_emb (BAWeightOp_isRight_rho x)
    (fun a => ⟨BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _, BAWeightOp_emb_ne _ _⟩)
    (BAWeightOp_self_mem_atom Γ) hcl hnew hnP (fun v _ => BAWeightOp_self_mem_atom Δ v)
  exact key

/-- **`n_M` of the extension is `n_M Γ`**: `z, y, α, β` join the molecule of `x`. -/
private theorem BAWeightOp_ext4_nM (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) :
    (BAWeightOp_ext4 Γ rest s x).nM = Γ.nM := by
  classical
  set Δ := BAWeightOp_ext4 Γ rest s x with hΔ
  have e1 : ∀ u w, Γ.adj u w = true → Δ.adj (owxEmb 4 u) (owxEmb 4 w) = true := fun u w h =>
    (BAWeightOp_ext4_adj Γ rest s x _ _).2 (Or.inl ⟨u, w, rfl, rfl, h⟩)
  have e2 : ∀ b c, Δ.adj b c = true → (True ∧ True ∧ (BAWeightOp_rho x b = BAWeightOp_rho x c ∨
      Γ.adj (BAWeightOp_rho x b) (BAWeightOp_rho x c) = true)) ∨ (¬ True ∧ ¬ True) := by
    intro b c hbc
    refine Or.inl ⟨trivial, trivial, ?_⟩
    rcases (BAWeightOp_ext4_adj Γ rest s x _ _).1 hbc with
      ⟨a, a', rfl, rfl, h'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr (by rw [BAWeightOp_rho_emb, BAWeightOp_rho_emb]; exact h')
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inl (by rw [BAWeightOp_rho_emb]; rfl)
    · exact Or.inl (by rw [BAWeightOp_rho_emb]; rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl
  have hz : Relation.ReflTransGen (fun a b => Δ.adj a b = true) (bpv 0) (owxEmb 4 x) :=
    Relation.ReflTransGen.single ((BAWeightOp_ext4_adj Γ rest s x _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))))
  have hy : Relation.ReflTransGen (fun a b => Δ.adj a b = true) (bpv 1) (owxEmb 4 x) :=
    Relation.ReflTransGen.head ((BAWeightOp_ext4_adj Γ rest s x _ _).2 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) hz
  have ha : Relation.ReflTransGen (fun a b => Δ.adj a b = true) (bpv 2) (owxEmb 4 x) :=
    Relation.ReflTransGen.head ((BAWeightOp_ext4_adj Γ rest s x _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))))) hy
  have hb : Relation.ReflTransGen (fun a b => Δ.adj a b = true) (bpv 3) (owxEmb 4 x) :=
    Relation.ReflTransGen.head ((BAWeightOp_ext4_adj Γ rest s x _ _).2 (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, rfl⟩)))))) ha
  have e3 : ∀ w : E ⊕ (I ⊕ Fin 4), True →
      Relation.ReflTransGen (fun a b => Δ.adj a b = true) w (owxEmb 4 (BAWeightOp_rho x w)) := by
    intro w _
    rcases w with e | i | j
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.refl
    · fin_cases j
      · exact hz
      · exact hy
      · exact ha
      · exact hb
  have hcl : ∀ v : E ⊕ (I ⊕ Fin 4), True → ∀ w, w ∈ Δ.mol v ↔
      w = v ∨ (True ∧ BAWeightOp_rho x w ∈ Γ.mol (BAWeightOp_rho x v)) := by
    intro v hv w
    rw [BAGraph.mem_mol_iff, BAGraph.mem_mol_iff]
    rw [BAWeightOp_rtg_ext (fun a b => Γ.adj a b) (fun a b => Δ.adj a b) (BAWeightOp_adj_comm _)
      (owxEmb 4) (BAWeightOp_rho x) (fun _ => True) e1 e2 e3 v w hv]
  have key := BAWeightOp_cnt_ext (fun w : E ⊕ I => w.isRight) (fun w : E ⊕ (I ⊕ Fin 4) => w.isRight) Γ.mol Δ.mol
    (owxEmb 4) (BAWeightOp_rho x) (fun _ => True) 0 (BAWeightOp_rho_emb x)
    BAWeightOp_isRight_emb (BAWeightOp_isRight_rho x) (fun _ => trivial) (fun v => by rw [BAGraph.mem_mol_iff])
    hcl (by simp) (fun v hv => absurd trivial hv) (fun v hv => absurd trivial hv)
  exact key

private theorem BAWeightOp_ext4_counters (Γ : BAGraph E I) (rest : List (SEdge (E ⊕ I)))
    (s : List (SEdge (E ⊕ (I ⊕ Fin 4)))) (x : E ⊕ I) :
    (BAWeightOp_ext4 Γ rest s x).counters = ⟨rest.length + s.length, Γ.nW + 2, Γ.nA + 2, Γ.nM, 0, 0⟩ := by
  simp only [BAGraph.counters, BAWeightOp_ext4_nA, BAWeightOp_ext4_nM]
  simp [BAGraph.nS, BAGraph.nW, BAWeightOp_ext4, BAGraph.ext, LGraph.owxExt]

end Ext4

end RBM.Graph

end
