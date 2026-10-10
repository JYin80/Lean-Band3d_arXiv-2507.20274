/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KTreeDeriv
import RBM3D.BA.KSolve
import RBM3D.BA.KCactus

/-!
# Stage K, row K05b: the chord part, `IsKLoopS` for the spliced family, `BAKsolve`, `BATreeRep`

Ticket T2374 (design BA-DK, `docs/reports/T2360-design.md` §3, §4 row K05b; supervisor
`docs/supervisor/2026-10-10-0350.md` C1-C4).  K05a (`BA/KTreeDeriv.lean`) proved the derivative of
the cactus value and the leaf part `baLeafPairs`.  Here:

1. The pins `BATreeRep` (verbatim) and `BAChordPairsStmt`.
2. **`baChordPairs`** (target 2): the chord part of `W^{-d(n-1)} Σ_F ∂_tΓ_F` is the sum over the
   diagonals `J = (i, j)` of the `(i+1, j+1)` summands of `treeEqRhsS` at `S = 1`.  For one tree
   `F ∋ J` the chord-`J` term (the cactus with the weight `tΘ` of the chord `J` replaced by `Θ·Θ`)
   is `Σ_x Γ_{F_out}(σ_out, a_out^x) Γ_{F_in}(σ_in, a_in^x)` (`KTreeRep_cut`): the generic
   splitting `KLgval_split` after the relabelling `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` of the
   slots, which commutes with the cyclic successor `BAnextSlot` (`KTreeRep_next_map`).  The reversed
   inner leaf `Θ^{(σ_j,σ_i)} = (Θ^{(σ_i,σ_j)})ᵀ` needs no symmetry of `M`.  The sum over `F ∋ J` is
   `KLsum_cut` (`Loop/KLCut.lean:1297`).
3. **`baKcac_isKLoopS`** (target 3): the spliced family `BAKcac` of K05a solves `IsKLoopS` on
   `[0,1)`: the derivative is `baGamma_hasDerivAt` + `baLeafPairs` + `baChordPairs` against the pair
   partition of `treeEqRhsS` (`n` leaf pairs and `n(n-3)/2` diagonal pairs); the length-2 equation
   is the closed form `(Kn2sol)`.
4. **`baKsolve`** (target 4), **`baTreeRep`** (target 5, through `baK_unique`).

Public: the pins, `baChordPairs`, `baKcac_isKLoopS`, `baKsolve`, `baTreeRep`; every other helper is
`private` with the stem `KTreeRep_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 0. The pins -/

/-- `tree-representation_BA` (`A:592-598`, [RBSO1D L4.16], stated there for `n ≥ 4`; `n = 3` is `(Kn3sol)`, `1_2:1176`, the
same formula with one tree): `𝒦^{(n)} = W^{-d(n-1)} ∑_{F ∈ TSP(n)} Γ_M(F)`, `n ≥ 3`, with `Γ` the `M`-graph value
(`A:380-583`; rules and numerical check in `T2360-design.md` §3). -/
def BATreeRep (d : ℕ)
    (Γ : ∀ (L n : ℕ) [NeZero L] [NeZero n], (Bool → Matrix (Zd d L) (Zd d L) ℂ) → ℝ →
      Finset (Fin n × Fin n) → (Fin n → Bool) → (Fin n → Zd d L) → ℂ) : Prop :=
  ∀ (Λ κ : ℝ), 0 < Λ → 0 < κ → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
      BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)
        = (((W : ℂ) ^ d)⁻¹) ^ (n - 1) *
            ∑ F ∈ TSP n, Γ L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ a

/-- **`BAChordPairsStmt`** (target 2; supervisor 0350 Q1 table, C1, C2): for every family with `BASplicedFam`, the chord part of
`W^{-d(n-1)} Σ_F ∂_tΓ_F` equals the `(i+1, j+1)` summands of `treeEqRhsS` at `S = 1` over the diagonals `J = (i, j)`.
(`BAReal` and `0 ≤ t < 1` are not used by the proof; they are kept to match `BALeafPairsStmt`.) -/
def BAChordPairsStmt (d : ℕ) : Prop :=
  ∀ (L W : ℕ) [NeZero L] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
    ∀ K : ℝ → LoopIdx (Zd d L) → ℂ, BASplicedFam d L W g E m K →
    ∀ (n : ℕ) [NeZero n], 3 ≤ n → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L) (t : ℝ), 0 ≤ t → t < 1 →
      (((W : ℂ) ^ d)⁻¹) ^ (n - 1) * ∑ F ∈ TSP n, ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
          (BACactusValLeafW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ) (BAslotLeaf F)
          (Function.update (BACactusValEdgeW (BAMsigma d L (BAMB d L g (E : ℂ) m)) t F σ) (Sum.inl J)
            (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
          (BACactusValSrc F) (BACactusValTgt F)
        = ∑ J ∈ diagonals n, ((W : ℂ) ^ d) * ∑ x : Zd d L,
            K t (LoopIdx.cutGlueL (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a)) *
            K t (LoopIdx.cutGlueR (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a))

/-! ## 1. The vertex maps of a cut and the list identities -/

section Maps

variable {d L : ℕ} {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- The vertex `k + i` of the `n`-gon for the vertex `k` of the inner polygon of the cut `J = (i, j)` (the inverse of
`KLinV J` on `[i, j]`). -/
private def KTreeRep_inVinv (J : Fin n × Fin n) (k : Fin (KLwIn J + 1)) : Fin n :=
  ⟨min (k.val + J.1.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The vertex of the `n`-gon for the vertex `k` of the outer polygon of the cut `J` (the inverse of `KLoutV J` off the
open arc of `J`). -/
private def KTreeRep_outVinv (J : Fin n × Fin n) (k : Fin (n - KLwIn J + 1)) : Fin n :=
  ⟨min (KLunCol J k.val) (n - 1), by have := NeZero.pos n; omega⟩

/-- The charges of the inner polygon of the cut `J`: `σ_i, …, σ_j`. -/
private def KTreeRep_σIn (J : Fin n × Fin n) (σ : Fin n → Bool) (k : Fin (KLwIn J + 1)) : Bool :=
  σ (KTreeRep_inVinv J k)

/-- The charges of the outer polygon of the cut `J`: `σ_0, …, σ_i, σ_j, …, σ_{n-1}`. -/
private def KTreeRep_σOut (J : Fin n × Fin n) (σ : Fin n → Bool) (k : Fin (n - KLwIn J + 1)) : Bool :=
  σ (KTreeRep_outVinv J k)

/-- The labels of the inner polygon: `a_i, …, a_{j-1}, x`. -/
private def KTreeRep_aIn (J : Fin n × Fin n) (a : Fin n → Zd d L) (x : Zd d L) : Fin (KLwIn J + 1) → Zd d L :=
  Function.update (fun k => a (KTreeRep_inVinv J k)) (Fin.last _) x

/-- The labels of the outer polygon: `a_0, …, a_{i-1}, x, a_j, …, a_{n-1}`. -/
private def KTreeRep_aOut (J : Fin n × Fin n) (a : Fin n → Zd d L) (x : Zd d L) : Fin (n - KLwIn J + 1) → Zd d L :=
  Function.update (fun k => a (KTreeRep_outVinv J k)) (KLglueV J) x

private theorem KTreeRep_inVinv_val (k : Fin (KLwIn J + 1)) (hJ : J.1.val < J.2.val) :
    (KTreeRep_inVinv J k).val = k.val + J.1.val := by
  have := k.isLt; have := J.2.isLt
  simp only [KTreeRep_inVinv, KLwIn] at *
  omega

private theorem KTreeRep_inVinv_inV {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    KTreeRep_inVinv J (KLinV J r) = r := by
  refine Fin.ext ?_
  simp only [KTreeRep_inVinv, KLinV, KLwIn, Fin.le_def] at *
  have := r.isLt
  omega

private theorem KTreeRep_inV_inVinv (k : Fin (KLwIn J + 1)) (hJ : J.1.val < J.2.val) :
    KLinV J (KTreeRep_inVinv J k) = k := by
  refine Fin.ext ?_
  have := k.isLt; have := J.2.isLt
  simp only [KTreeRep_inVinv, KLinV, KLwIn] at *
  omega

private theorem KTreeRep_outVinv_outV (hJ : J.1.val + 2 ≤ J.2.val) {r : Fin n}
    (h : r.val ≤ J.1.val ∨ J.2.val ≤ r.val) : KTreeRep_outVinv J (KLoutV J r) = r := by
  refine Fin.ext ?_
  have := r.isLt; have := J.2.isLt
  simp only [KTreeRep_outVinv, KLoutV, KLcol, KLunCol, KLwIn] at *
  split_ifs <;> omega

private theorem KTreeRep_outV_outVinv (hJ : J.1.val + 2 ≤ J.2.val) (k : Fin (n - KLwIn J + 1)) :
    KLoutV J (KTreeRep_outVinv J k) = k := by
  refine Fin.ext ?_
  have := k.isLt; have := J.2.isLt
  simp only [KTreeRep_outVinv, KLoutV, KLcol, KLunCol, KLwIn] at *
  split_ifs <;> omega

omit [NeZero n] in
private theorem KTreeRep_glueV_val (hJ : J.1.val + 2 ≤ J.2.val) : (KLglueV J).val = J.1.val := by
  have := J.2.isLt
  simp only [KLglueV, KLwIn]
  omega

end Maps

section Lists

variable {d L : ℕ} {n : ℕ} [NeZero n]

/-- **The inner polygon piece of the cut `(i+1, j+1)`**: `cutGlueR` of `KLloopOf σ a` is the loop of the inner polygon,
charges `σ_i, …, σ_j`, labels `a_i, …, a_{j-1}, x`. -/
private theorem KTreeRep_cutGlueR_eq (J : Fin n × Fin n) (hJ : J.1.val < J.2.val) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueR (J.1.val + 1) (J.2.val + 1) x =
      KLloopOf d L (KTreeRep_σIn J σ) (KTreeRep_aIn J a x) := by
  have hj := J.2.isLt
  have e1 : J.2.val + 1 - (J.1.val + 1) = KLwIn J := by simp [KLwIn]
  simp only [LoopIdx.cutGlueR, KLloopOf, Nat.add_sub_cancel, e1]
  refine LoopIdx.ext ?_ ?_
  · dsimp only
    refine List.ext_getElem (by simp only [List.length_take, List.length_drop, List.length_ofFn]; simp only [KLwIn]; omega)
      fun m h1 h2 => ?_
    have hm : m < KLwIn J + 1 := by simpa using h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, KTreeRep_σIn]
    congr 1
    refine Fin.ext ?_
    rw [KTreeRep_inVinv_val ⟨m, hm⟩ hJ]
    dsimp only
    omega
  · dsimp only
    refine List.ext_getElem (by simp only [List.length_append, List.length_take, List.length_drop,
      List.length_ofFn, List.length_singleton]; simp only [KLwIn]; omega) fun m h1 h2 => ?_
    have hm : m < KLwIn J + 1 := by simpa using h2
    by_cases hmw : m < KLwIn J
    · rw [List.getElem_append_left (by simp only [List.length_take, List.length_drop, List.length_ofFn]; simp only [KLwIn]; omega)]
      simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, KTreeRep_aIn]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega)]
      congr 1
      refine Fin.ext ?_
      rw [KTreeRep_inVinv_val ⟨m, hm⟩ hJ]
      dsimp only
      omega
    · have hmw' : m = KLwIn J := by omega
      subst hmw'
      have hlen : (List.take (KLwIn J) (List.drop (↑J.1) (List.ofFn a))).length = KLwIn J := by
        simp only [List.length_take, List.length_drop, List.length_ofFn]; simp only [KLwIn]; omega
      rw [List.getElem_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem_singleton, KTreeRep_aIn, List.getElem_ofFn]
      exact (Function.update_self (Fin.last (KLwIn J)) x (fun k => a (KTreeRep_inVinv J k))).symm

/-- **The outer polygon piece of the cut `(i+1, j+1)`**: `cutGlueL` of `KLloopOf σ a` is the loop of the outer polygon,
charges `σ_0, …, σ_i, σ_j, …, σ_{n-1}`, labels `a_0, …, a_{i-1}, x, a_j, …, a_{n-1}`. -/
private theorem KTreeRep_cutGlueL_eq (J : Fin n × Fin n) (hJ : J.1.val + 2 ≤ J.2.val) (σ : Fin n → Bool)
    (a : Fin n → Zd d L) (x : Zd d L) :
    (KLloopOf d L σ a).cutGlueL (J.1.val + 1) (J.2.val + 1) x =
      KLloopOf d L (KTreeRep_σOut J σ) (KTreeRep_aOut J a x) := by
  have hj := J.2.isLt
  have hg : (KLglueV J).val = J.1.val := KTreeRep_glueV_val hJ
  simp only [LoopIdx.cutGlueL, KLloopOf, Nat.add_sub_cancel]
  refine LoopIdx.ext ?_ ?_
  · dsimp only
    have hl : (List.take (J.1.val + 1) (List.ofFn σ) ++ List.drop J.2.val (List.ofFn σ)).length =
        (List.ofFn (KTreeRep_σOut J σ)).length := by
      simp only [List.length_append, List.length_take, List.length_drop, List.length_ofFn]
      simp only [KLwIn]
      omega
    refine List.ext_getElem hl fun m h1 h2 => ?_
    have hm : m < n - KLwIn J + 1 := by simpa using h2
    simp only [KLwIn] at hm
    by_cases hmi : m < J.1.val + 1
    · rw [List.getElem_append_left (by simp only [List.length_take, List.length_ofFn]; omega)]
      simp only [List.getElem_take, List.getElem_ofFn, KTreeRep_σOut]
      congr 1
      refine Fin.ext ?_
      simp only [KTreeRep_outVinv, KLunCol, KLwIn]
      split_ifs <;> omega
    · rw [List.getElem_append_right (by simp only [List.length_take, List.length_ofFn]; omega)]
      simp only [List.getElem_drop, List.getElem_ofFn, KTreeRep_σOut]
      congr 1
      refine Fin.ext ?_
      simp only [KTreeRep_outVinv, KLunCol, KLwIn, List.length_take, List.length_ofFn]
      split_ifs <;> omega
  · dsimp only
    have hl : (List.take J.1.val (List.ofFn a) ++ x :: List.drop J.2.val (List.ofFn a)).length =
        (List.ofFn (KTreeRep_aOut J a x)).length := by
      simp only [List.length_append, List.length_take, List.length_drop, List.length_ofFn, List.length_cons]
      simp only [KLwIn]
      omega
    refine List.ext_getElem hl fun m h1 h2 => ?_
    have hm : m < n - KLwIn J + 1 := by simpa using h2
    have hlen : (List.take (J.1.val) (List.ofFn a)).length = J.1.val := by
      simp only [List.length_take, List.length_ofFn]; omega
    simp only [KLwIn] at hm
    by_cases hmi : m < J.1.val
    · rw [List.getElem_append_left (by omega)]
      simp only [List.getElem_take, List.getElem_ofFn, KTreeRep_aOut]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp only [hg] at this; omega)]
      congr 1
      refine Fin.ext ?_
      simp only [KTreeRep_outVinv, KLunCol, KLwIn]
      split_ifs <;> omega
    · rw [List.getElem_append_right (by omega)]
      by_cases hmeq : m = J.1.val
      · subst hmeq
        simp only [hlen, Nat.sub_self, List.getElem_cons_zero, KTreeRep_aOut, List.getElem_ofFn]
        have : (⟨J.1.val, hm⟩ : Fin (n - KLwIn J + 1)) = KLglueV J := Fin.ext (by rw [hg])
        rw [this]
        exact (Function.update_self (KLglueV J) x (fun k => a (KTreeRep_outVinv J k))).symm
      · obtain ⟨m', hm'⟩ : ∃ m', m - (List.take J.1.val (List.ofFn a)).length = m' + 1 :=
          ⟨m - J.1.val - 1, by rw [hlen]; omega⟩
        simp only [hm', List.getElem_cons_succ, List.getElem_drop, List.getElem_ofFn, KTreeRep_aOut]
        rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp only [hg] at this; omega)]
        congr 1
        refine Fin.ext ?_
        simp only [KTreeRep_outVinv, KLunCol, KLwIn, hlen] at hm' ⊢
        split_ifs <;> omega

end Lists

/-! ## 2. Transport of the cyclic successor along an order-preserving relabelling of the slots -/

section Transport

variable {n n' : ℕ} [NeZero n] [NeZero n'] {F : Finset (Fin n × Fin n)} {F' : Finset (Fin n' × Fin n')}

/-- **The cyclic successor commutes with a relabelling of the slots** `φ : BAslot F' → BAslot F` that preserves "same node"
and the order of the starts inside a node, and whose image is closed under "same node": the successor is characterised
by the nodes and the starts alone (`BAnextSlot_eq_of_above`, `BAnextSlot_eq_of_wrap`). -/
private theorem KTreeRep_next_map (hF : KLIsTSP F) (hn : 2 ≤ n) (φ : BAslot F' → BAslot F)
    (hnode : ∀ s t, BAslotNode F (φ s) = BAslotNode F (φ t) ↔ BAslotNode F' s = BAslotNode F' t)
    (hstart : ∀ s t, BAslotNode F' s = BAslotNode F' t →
      (BAslotStart F' s < BAslotStart F' t ↔ BAslotStart F (φ s) < BAslotStart F (φ t)))
    (hclosed : ∀ s x, BAslotNode F x = BAslotNode F (φ s) → ∃ t, φ t = x) (s : BAslot F') :
    φ (BAnextSlot F' s) = BAnextSlot F (φ s) := by
  have hnext : BAslotNode F' (BAnextSlot F' s) = BAslotNode F' s := BAslotNode_nextSlot F' s
  have hle : ∀ s t, BAslotNode F' s = BAslotNode F' t →
      (BAslotStart F' s ≤ BAslotStart F' t ↔ BAslotStart F (φ s) ≤ BAslotStart F (φ t)) := by
    intro s t h
    rw [← not_lt, ← not_lt (a := BAslotStart F (φ t)), hstart t s h.symm]
  symm
  rcases BAnextSlot_spec F' s with ⟨hlt, hmin⟩ | ⟨hmax, hmin⟩
  · refine BAnextSlot_eq_of_above hF hn ((hnode _ _).2 hnext) ((hstart _ _ hnext.symm).1 hlt) ?_
    intro x hx hsx
    obtain ⟨t, rfl⟩ := hclosed s x hx
    have hts : BAslotNode F' t = BAslotNode F' s := (hnode _ _).1 hx
    exact (hle _ _ (hnext.trans hts.symm)).1 (hmin t hts ((hstart _ _ hts.symm).2 hsx))
  · refine BAnextSlot_eq_of_wrap hF hn ((hnode _ _).2 hnext) ?_ ?_
    · intro x hx
      obtain ⟨t, rfl⟩ := hclosed s x hx
      exact (hle _ _ ((hnode _ _).1 hx)).1 (hmax t ((hnode _ _).1 hx))
    · intro x hx
      obtain ⟨t, rfl⟩ := hclosed s x hx
      exact (hle _ _ (hnext.trans ((hnode _ _).1 hx).symm)).1 (hmin t ((hnode _ _).1 hx))

end Transport

/-! ## 3. The inner polygon of a cut: nodes, slots -/

section InSide

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KTreeRep_shiftIn_self : KLshiftIn J J = KLwholeP (KLwIn J + 1) := by
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp [KLshiftIn, KLwholeP, KLwIn]

omit [NeZero n] in
private theorem KTreeRep_arcLe_shiftIn_iff {d e : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2)
    (he : KLArcLe e J) (he12 : e.1 ≤ e.2) :
    KLArcLe (KLshiftIn J d) (KLshiftIn J e) ↔ KLArcLe d e := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLshiftIn_val he he12
  simp only [KLArcLe, Fin.le_def] at hd he hd12 he12 ⊢
  omega

omit [NeZero n] in
private theorem KTreeRep_inArc_shiftIn_iff {d : Fin n × Fin n} (hd : KLArcLe d J) (hd12 : d.1 ≤ d.2) {v : Fin n}
    (hv : KLInArc J v) : KLInArc (KLshiftIn J d) (KLinV J v) ↔ KLInArc d v := by
  have h1 := KLshiftIn_val hd hd12
  have h2 := KLinV_val hv
  simp only [KLArcLe, KLInArc, Fin.le_def, Fin.lt_def] at hd hv hd12 ⊢
  omega

private theorem KTreeRep_shiftIn_mem_nodes (hF : KLIsTSP F) (hJ : J ∈ F) {x : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hxJ : KLArcLe x J) : KLshiftIn J x ∈ KLnodes (KLFIn F J) := by
  by_cases h : x = J
  · subst h
    rw [KTreeRep_shiftIn_self]
    exact KLwholeP_mem_nodes _
  · have hxF : x ∈ F := by
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact absurd hxJ (KLnot_arcLe_wholeP hF hJ)
      · exact hx
    exact KLmem_nodes_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hxF, hxJ, h⟩))

private theorem KTreeRep_mem_nodes_FIn (hJ : J ∈ F) {y : Fin (KLwIn J + 1) × Fin (KLwIn J + 1)}
    (hy : y ∈ KLnodes (KLFIn F J)) : ∃ x ∈ KLnodes F, KLArcLe x J ∧ KLshiftIn J x = y := by
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact ⟨J, KLmem_nodes_of_mem hJ, ⟨le_refl _, le_refl _⟩, KTreeRep_shiftIn_self⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx' := Finset.mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2.1, rfl⟩

/-- **The parent node of an inside leaf, in the inner polygon.** -/
private theorem KTreeRep_leafPar_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {v : Fin n} (hv : KLInArc J v) :
    KLleafPar (KLFIn F J) (KLinV J v) = KLshiftIn J (KLleafPar F v) := by
  have h12 : ∀ x ∈ KLnodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (KLlt_of_mem_nodes hF hn hx)
  have hspec := KLleafPar_spec hF (KLlt_of_inArc hv)
  have hin := KLleafPar_arcLe_of_inArc hF hJ hv
  have hmem := KLleafPar_mem F v
  refine KLleafPar_eq (KTreeRep_shiftIn_mem_nodes hF hJ hmem hin)
    ((KTreeRep_inArc_shiftIn_iff hin (h12 _ hmem) hv).2 hspec.1) ?_
  intro e' he' hev'
  obtain ⟨x, hx, hxJ, rfl⟩ := KTreeRep_mem_nodes_FIn hJ he'
  have hxv := (KTreeRep_inArc_shiftIn_iff hxJ (h12 _ hx) hv).1 hev'
  exact (KTreeRep_arcLe_shiftIn_iff hin (h12 _ hmem) hxJ (h12 _ hx)).2 (hspec.2 x hx hxv)

/-- **The parent node of an inside chord, in the inner polygon.** -/
private theorem KTreeRep_nodePar_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {d : Fin n × Fin n} (hd : d ∈ F)
    (hdJ : KLArcLe d J) (hne : d ≠ J) :
    KLnodePar (KLFIn F J) (KLshiftIn J d) = KLshiftIn J (KLnodePar F d) := by
  have h12 : ∀ x ∈ KLnodes F, x.1 ≤ x.2 := fun x hx => le_of_lt (KLlt_of_mem_nodes hF hn hx)
  have hdn := KLmem_nodes_of_mem hd
  have hspec := KLnodePar_spec hF hn hdn (KLne_wholeP hF hd)
  have hin := KLnodePar_arcLe hF hn hJ hd hdJ hne
  have hpm := KLnodePar_mem F d
  have hdd := KLshiftIn_val hdJ (h12 _ hdn)
  have hlt' := KLlt_of_mem_nodes hF hn hdn
  refine KLnodePar_eq ?_ (KTreeRep_shiftIn_mem_nodes hF hJ hpm hin)
    ((KTreeRep_arcLe_shiftIn_iff hdJ (h12 _ hdn) hin (h12 _ hpm)).2 hspec.2.1) ?_ ?_
  · rw [Fin.le_def, hdd.1, hdd.2]; rw [Fin.lt_def] at hlt'; omega
  · intro h
    exact hspec.2.2.1 (KLshiftIn_injOn hin (h12 _ hpm) hdJ (h12 _ hdn) h)
  · intro e' he' hde' hne'
    obtain ⟨x, hx, hxJ, rfl⟩ := KTreeRep_mem_nodes_FIn hJ he'
    have hdx := (KTreeRep_arcLe_shiftIn_iff hdJ (h12 _ hdn) hxJ (h12 _ hx)).1 hde'
    have hxd : x ≠ d := fun h => hne' (by rw [h])
    exact (KTreeRep_arcLe_shiftIn_iff hin (h12 _ hpm) hxJ (h12 _ hx)).2 (hspec.2.2.2 x hx hdx hxd)

end InSide

section InSlots

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- `KLshiftIn J` as a bijection from the chords of `F` strictly inside `J` onto the chords of the inner polygon. -/
private noncomputable def KTreeRep_eIn (hF : KLIsTSP F) (J : Fin n × Fin n) : KLEIn F J ≃ ↥(KLFIn F J) :=
  Equiv.ofBijective
    (fun d => ⟨KLshiftIn J d.1.1, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨d.1.2, d.2⟩)⟩)
    ⟨fun d e h => Subtype.ext (Subtype.ext (KLshiftIn_injOn d.2.1 (le_of_lt (hF.1 _ d.1.2).1) e.2.1
        (le_of_lt (hF.1 _ e.1.2).1) (congrArg Subtype.val h))),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
        have hx' := Finset.mem_filter.1 hx
        exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩⟩

omit [NeZero n] in
private theorem KTreeRep_eIn_symm (hF : KLIsTSP F) (y : ↥(KLFIn F J)) :
    KLshiftIn J ((KTreeRep_eIn hF J).symm y).1.1 = y.1 := by
  exact congrArg Subtype.val ((KTreeRep_eIn hF J).apply_symm_apply y)

/-- **The relabelling of the slots of the inner polygon**: the leaf `k < w` is the leaf `k + i`, the last leaf is the slot
`BAslotIn J` (the cycle of the node `J`), the chords are lifted by `KLshiftIn⁻¹`. -/
private noncomputable def KTreeRep_φ (hF : KLIsTSP F) (hJ : J ∈ F) : BAslot (KLFIn F J) → BAslot F
  | Sum.inl k => if k.val < KLwIn J then Sum.inl (KTreeRep_inVinv J k) else BAslotIn F ⟨J, hJ⟩
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl ((KTreeRep_eIn hF J).symm y).1)
  | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr ((KTreeRep_eIn hF J).symm y).1)

private theorem KTreeRep_φ_leaf (hF : KLIsTSP F) (hJ : J ∈ F) (k : Fin (KLwIn J + 1)) (hk : k.val < KLwIn J) :
    KTreeRep_φ hF hJ (Sum.inl k) = Sum.inl (KTreeRep_inVinv J k) := by
  simp only [KTreeRep_φ, hk, ↓reduceIte]

private theorem KTreeRep_φ_last (hF : KLIsTSP F) (hJ : J ∈ F) (k : Fin (KLwIn J + 1)) (hk : ¬ k.val < KLwIn J) :
    KTreeRep_φ hF hJ (Sum.inl k) = BAslotIn F ⟨J, hJ⟩ := by
  simp only [KTreeRep_φ, hk, ↓reduceIte]

omit [NeZero n] in
/-- The facts about a chord strictly inside `J` that the maps need. -/
private theorem KTreeRep_inChord (hF : KLIsTSP F) (z : KLEIn F J) :
    KLArcLe z.1.1 J ∧ z.1.1 ≠ J ∧ z.1.1.1 < z.1.1.2 := ⟨z.2.1, z.2.2, (hF.1 _ z.1.2).1⟩

omit [NeZero n] in
private theorem KTreeRep_inV_val {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    (KLinV J r).val = r.val - J.1.val := by
  simp only [KLinV, KLwIn, Fin.le_def] at *
  omega

/-- **The nodes**: the node of `s` in the inner polygon is the `KLshiftIn`-image of the node of `φ s` in `F`, which lies
inside `J`. -/
private theorem KTreeRep_φ_node (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    BAslotNode (KLFIn F J) s = KLshiftIn J (BAslotNode F (KTreeRep_φ hF hJ s)) ∧
      KLArcLe (BAslotNode F (KTreeRep_φ hF hJ s)) J := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k.val < KLwIn J
    · have hv : KLInArc J (KTreeRep_inVinv J k) := by
        have := KTreeRep_inVinv_val k (by omega)
        simp only [KLInArc, Fin.le_def, Fin.lt_def, this]
        simp only [KLwIn] at hk
        omega
      rw [KTreeRep_φ_leaf hF hJ k hk]
      refine ⟨?_, KLleafPar_arcLe_of_inArc hF hJ hv⟩
      have h := KTreeRep_leafPar_in hF hn hJ hv
      rw [KTreeRep_inV_inVinv k (by omega)] at h
      exact h
    · rw [KTreeRep_φ_last hF hJ k hk]
      refine ⟨?_, ⟨le_refl _, le_refl _⟩⟩
      have hkl : k.val = (KLwIn J + 1) - 1 := by have := k.isLt; omega
      change KLleafPar (KLFIn F J) k = KLshiftIn J J
      rw [KLleafPar_root _ hkl, KTreeRep_shiftIn_self]
  · set z := (KTreeRep_eIn hF J).symm y with hz
    have hy := KTreeRep_eIn_symm hF y
    obtain ⟨h1, h2, -⟩ := KTreeRep_inChord hF z
    refine ⟨?_, KLnodePar_arcLe hF hn hJ z.1.2 h1 h2⟩
    change KLnodePar (KLFIn F J) y.1 = KLshiftIn J (KLnodePar F z.1.1)
    rw [← hy]
    exact KTreeRep_nodePar_in hF hn hJ z.1.2 h1 h2
  · set z := (KTreeRep_eIn hF J).symm y with hz
    have hy := KTreeRep_eIn_symm hF y
    obtain ⟨h1, h2, -⟩ := KTreeRep_inChord hF z
    exact ⟨hy.symm, h1⟩

/-- **The starts**: the start of `s` in the inner polygon is `KLinV J` of the start of `φ s`, and the starts of the image
lie in `[i, j]`. -/
private theorem KTreeRep_φ_start (hF : KLIsTSP F) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    BAslotStart (KLFIn F J) s = KLinV J (BAslotStart F (KTreeRep_φ hF hJ s)) ∧
      J.1 ≤ BAslotStart F (KTreeRep_φ hF hJ s) ∧ BAslotStart F (KTreeRep_φ hF hJ s) ≤ J.2 := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k.val < KLwIn J
    · rw [KTreeRep_φ_leaf hF hJ k hk]
      change k = KLinV J (KTreeRep_inVinv J k) ∧ J.1 ≤ KTreeRep_inVinv J k ∧ KTreeRep_inVinv J k ≤ J.2
      have := KTreeRep_inVinv_val k (by omega)
      simp only [Fin.le_def, this]
      refine ⟨(KTreeRep_inV_inVinv k (by omega)).symm, by omega, ?_⟩
      simp only [KLwIn] at hk
      omega
    · rw [KTreeRep_φ_last hF hJ k hk]
      change k = KLinV J J.2 ∧ J.1 ≤ J.2 ∧ J.2 ≤ J.2
      simp only [Fin.le_def]
      refine ⟨Fin.ext ?_, by omega, le_refl _⟩
      have := k.isLt
      rw [KTreeRep_inV_val (by simp only [Fin.le_def]; omega) (le_refl _)]
      simp only [KLwIn] at hk this ⊢
      omega
  · set z := (KTreeRep_eIn hF J).symm y with hz
    have hy := KTreeRep_eIn_symm hF y
    obtain ⟨h1, h2, h3⟩ := KTreeRep_inChord hF z
    simp only [KTreeRep_φ, BAslotStart_out, ← hz]
    refine ⟨?_, h1.1, le_trans (le_of_lt h3) h1.2⟩
    have := congrArg Prod.fst hy
    exact this.symm
  · set z := (KTreeRep_eIn hF J).symm y with hz
    have hy := KTreeRep_eIn_symm hF y
    obtain ⟨h1, h2, h3⟩ := KTreeRep_inChord hF z
    simp only [KTreeRep_φ, BAslotStart_in, ← hz]
    refine ⟨?_, le_trans h1.1 (le_of_lt h3), h1.2⟩
    have := congrArg Prod.snd hy
    exact this.symm

/-- **The image of `φ` is closed under "same node"**: every slot of `F` whose node lies inside `J` is `φ s`. -/
private theorem KTreeRep_φ_closed (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {x : BAslot F}
    (hx : KLArcLe (BAslotNode F x) J) : ∃ s, KTreeRep_φ hF hJ s = x := by
  have hJw := KLdiag_width hF hJ
  rcases x with v | J' | J'
  · have hv : KLInArc J v := by
      by_contra h
      exact KLnot_arcLe_leafPar hF hJ h hx
    have hlt : (KLinV J v).val < KLwIn J := by
      have := KLinV_val hv
      simp only [KLInArc, Fin.lt_def] at hv
      simp only [KLwIn]
      omega
    exact ⟨Sum.inl (KLinV J v), by
      rw [KTreeRep_φ_leaf hF hJ _ hlt, KTreeRep_inVinv_inV hv.1 (le_of_lt hv.2)]⟩
  · have hx' : KLArcLe (KLnodePar F J'.1) J := hx
    have h2 : J'.1 ≠ J := fun h => by
      rw [h] at hx'
      exact KLnot_arcLe_nodePar_self hF hn hJ hx'
    have h1 : KLArcLe J'.1 J :=
      ((KLnodePar_spec hF hn (KLmem_nodes_of_mem J'.2) (KLne_wholeP hF J'.2)).2.1).trans hx'
    refine ⟨Sum.inr (Sum.inl ((KTreeRep_eIn hF J) ⟨J', h1, h2⟩)), ?_⟩
    simp only [KTreeRep_φ, Equiv.symm_apply_apply]
  · have hx' : KLArcLe J'.1 J := hx
    by_cases h2 : J'.1 = J
    · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
      refine ⟨Sum.inl (Fin.last _), ?_⟩
      rw [KTreeRep_φ_last hF hJ _ (by simp), hJ']
    · refine ⟨Sum.inr (Sum.inr ((KTreeRep_eIn hF J) ⟨J', hx', h2⟩)), ?_⟩
      simp only [KTreeRep_φ, Equiv.symm_apply_apply]

/-- **`φ` commutes with the cyclic successor**: the cycle of a node of the inner polygon is the cycle of the corresponding
node of `F`. -/
private theorem KTreeRep_φ_next (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFIn F J)) :
    KTreeRep_φ hF hJ (BAnextSlot (KLFIn F J) s) = BAnextSlot F (KTreeRep_φ hF hJ s) := by
  have h12 : ∀ y : BAslot (KLFIn F J) , (BAslotNode F (KTreeRep_φ hF hJ y)).1 ≤
      (BAslotNode F (KTreeRep_φ hF hJ y)).2 := fun y =>
    le_of_lt (KLlt_of_mem_nodes hF hn (BAslotNode_mem_nodes F _))
  refine KTreeRep_next_map hF hn (KTreeRep_φ hF hJ) ?_ ?_ ?_ s
  · intro s t
    constructor
    · intro h
      rw [(KTreeRep_φ_node hF hn hJ s).1, (KTreeRep_φ_node hF hn hJ t).1, h]
    · intro h
      rw [(KTreeRep_φ_node hF hn hJ s).1, (KTreeRep_φ_node hF hn hJ t).1] at h
      exact KLshiftIn_injOn (KTreeRep_φ_node hF hn hJ s).2 (h12 s) (KTreeRep_φ_node hF hn hJ t).2 (h12 t) h
  · intro s t _
    obtain ⟨hs, hs1, hs2⟩ := KTreeRep_φ_start hF hJ s
    obtain ⟨ht, ht1, ht2⟩ := KTreeRep_φ_start hF hJ t
    rw [hs, ht, Fin.lt_def, Fin.lt_def, KTreeRep_inV_val hs1 hs2, KTreeRep_inV_val ht1 ht2]
    simp only [Fin.le_def] at hs1 hs2 ht1 ht2
    omega
  · intro s x hx
    exact KTreeRep_φ_closed hF hn hJ (by rw [hx]; exact (KTreeRep_φ_node hF hn hJ s).2)

end InSlots

/-! ## 4. The outer polygon of a cut: nodes, slots -/

section OutSide

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KTreeRep_col_le_iff {r s : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r) (hs : s ≤ J.1.val ∨ J.2.val ≤ s)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLcol J r ≤ KLcol J s ↔ r ≤ s := by
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

omit [NeZero n] in
private theorem KTreeRep_col_lt_of_vertex {r v : ℕ} (hr : r ≤ J.1.val ∨ J.2.val ≤ r)
    (hv : v < J.1.val ∨ J.2.val ≤ v) (hJ : J.1.val + 2 ≤ J.2.val) :
    (KLcol J v < KLcol J r ↔ v < r) ∧ (KLcol J r ≤ KLcol J v ↔ r ≤ v) := by
  simp only [KLcol, KLwIn]
  constructor <;> split_ifs <;> omega

omit [NeZero n] in
private theorem KTreeRep_arcLe_shiftOut_iff {d e : Fin n × Fin n} (hd : KLOutEnds J d) (he : KLOutEnds J e)
    (hJ : J.1.val + 2 ≤ J.2.val) : KLArcLe (KLshiftOut J d) (KLshiftOut J e) ↔ KLArcLe d e := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLshiftOut_val e hJ2
  simp only [KLArcLe, Fin.le_def, h1, h2, KTreeRep_col_le_iff he.1 hd.1 hJ, KTreeRep_col_le_iff hd.2.1 he.2.1 hJ]

omit [NeZero n] in
private theorem KTreeRep_inArc_shiftOut_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) {v : Fin n}
    (hv : ¬KLInArc J v) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLoutV J v) ↔ KLInArc d v := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have h2 := KLoutV_val v hJ2
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  simp only [KLInArc, Fin.le_def, Fin.lt_def, h1, h2, (KTreeRep_col_lt_of_vertex hd.1 hv' hJ).2,
    (KTreeRep_col_lt_of_vertex hd.2.1 hv' hJ).1]

omit [NeZero n] in
private theorem KTreeRep_inArc_glue_iff {d : Fin n × Fin n} (hd : KLOutEnds J d) (hJ : J.1.val + 2 ≤ J.2.val) :
    KLInArc (KLshiftOut J d) (KLglueV J) ↔ KLArcLe J d := by
  have hJ2 : J.1.val < J.2.val := by omega
  have h1 := KLshiftOut_val d hJ2
  have hg : (KLglueV J).val = J.1.val := KTreeRep_glueV_val hJ
  obtain ⟨e1, e2, e3⟩ := hd
  simp only [KLInArc, KLArcLe, Fin.le_def, Fin.lt_def, h1, hg]
  simp only [KLcol, KLwIn]
  split_ifs <;> omega

private theorem KTreeRep_shiftOut_whole (hF : KLIsTSP F) (hJ : J ∈ F) :
    KLshiftOut J (KLwholeP n) = KLwholeP (n - KLwIn J + 1) := by
  have hJw := KLdiag_width hF hJ
  have := J.2.isLt
  have hc : KLcol J (n - 1) = n - KLwIn J := by
    rw [KLcol_of_gt (by omega)]; simp only [KLwIn]; omega
  refine Prod.ext (Fin.ext ?_) (Fin.ext ?_)
  · simp [KLshiftOut, KLwholeP, KLcol]
  · simp only [KLshiftOut, KLwholeP, hc]; simp

private theorem KTreeRep_shiftOut_mem_nodes (hF : KLIsTSP F) (hJ : J ∈ F) {x : Fin n × Fin n} (hx : x ∈ KLnodes F)
    (hxJ : ¬KLArcLe x J) : KLshiftOut J x ∈ KLnodes (KLFOut F J) := by
  rcases Finset.mem_insert.1 hx with rfl | hx
  · rw [KTreeRep_shiftOut_whole hF hJ]; exact KLwholeP_mem_nodes _
  · exact KLmem_nodes_of_mem (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, hxJ⟩))

private theorem KTreeRep_mem_nodes_FOut (hF : KLIsTSP F) (hJ : J ∈ F)
    {y : Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)} (hy : y ∈ KLnodes (KLFOut F J)) :
    ∃ x ∈ KLnodes F, ¬KLArcLe x J ∧ KLshiftOut J x = y := by
  rcases Finset.mem_insert.1 hy with rfl | hy
  · exact ⟨KLwholeP n, KLwholeP_mem_nodes F, KLnot_arcLe_wholeP hF hJ, KTreeRep_shiftOut_whole hF hJ⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    have hx' := Finset.mem_filter.1 hx
    exact ⟨x, KLmem_nodes_of_mem hx'.1, hx'.2, rfl⟩

/-- **The parent node of an outside leaf, in the outer polygon.** -/
private theorem KTreeRep_leafPar_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {v : Fin n} (hv : ¬KLInArc J v) :
    KLleafPar (KLFOut F J) (KLoutV J v) = KLshiftOut J (KLleafPar F v) := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hout := KLnot_arcLe_leafPar hF hJ hv
  have hpm := KLleafPar_mem F v
  by_cases hr : v.val < n - 1
  · have hspec := KLleafPar_spec hF hr
    refine KLleafPar_eq (KTreeRep_shiftOut_mem_nodes hF hJ hpm hout)
      ((KTreeRep_inArc_shiftOut_iff (hends _ hpm hout) hv hJw).2 hspec.1) ?_
    intro e' he' hve'
    obtain ⟨z, hz, hzJ, rfl⟩ := KTreeRep_mem_nodes_FOut hF hJ he'
    have hzv := (KTreeRep_inArc_shiftOut_iff (hends _ hz hzJ) hv hJw).1 hve'
    exact (KTreeRep_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2 z hz hzv)
  · have hroot : v.val = n - 1 := by have := v.isLt; omega
    rw [KLleafPar_root F hroot, KTreeRep_shiftOut_whole hF hJ, KLleafPar_root]
    rw [KLoutV_val _ hJ2, hroot]
    have := J.2.isLt
    rw [KLcol_of_gt (by omega)]
    simp only [KLwIn]; omega

/-- **The parent node of the glue leaf, in the outer polygon**: the parent of `J`. -/
private theorem KTreeRep_leafPar_glue (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLleafPar (KLFOut F J) (KLglueV J) = KLshiftOut J (KLnodePar F J) := by
  have hJw := KLdiag_width hF hJ
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hJn := KLmem_nodes_of_mem hJ
  have hspec := KLnodePar_spec hF hn hJn (KLne_wholeP hF hJ)
  have hout := KLnot_arcLe_nodePar_self hF hn hJ
  have hpm := KLnodePar_mem F J
  refine KLleafPar_eq (KTreeRep_shiftOut_mem_nodes hF hJ hpm hout)
    ((KTreeRep_inArc_glue_iff (hends _ hpm hout) hJw).2 hspec.2.1) ?_
  intro e' he' hge'
  obtain ⟨z, hz, hzJ, rfl⟩ := KTreeRep_mem_nodes_FOut hF hJ he'
  have hJz := (KTreeRep_inArc_glue_iff (hends _ hz hzJ) hJw).1 hge'
  have hzne : z ≠ J := fun h => hzJ (h ▸ ⟨le_refl _, le_refl _⟩)
  exact (KTreeRep_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2.2.2 z hz hJz hzne)

/-- **The parent node of an outside chord, in the outer polygon.** -/
private theorem KTreeRep_nodePar_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {d : Fin n × Fin n} (hd : d ∈ F)
    (hdJ : ¬KLArcLe d J) :
    KLnodePar (KLFOut F J) (KLshiftOut J d) = KLshiftOut J (KLnodePar F d) := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  have hends : ∀ y ∈ KLnodes F, ¬KLArcLe y J → KLOutEnds J y := fun y hy hyJ => KLoutEnds_of hF hn hJ hy hyJ
  have hdn := KLmem_nodes_of_mem hd
  have hspec := KLnodePar_spec hF hn hdn (KLne_wholeP hF hd)
  have hout := KLnot_arcLe_nodePar hF hn hd hdJ
  have hpm := KLnodePar_mem F d
  have hdE := hends _ hdn hdJ
  have hdd := KLshiftOut_val d hJ2
  refine KLnodePar_eq ?_ (KTreeRep_shiftOut_mem_nodes hF hJ hpm hout)
    ((KTreeRep_arcLe_shiftOut_iff hdE (hends _ hpm hout) hJw).2 hspec.2.1) ?_ ?_
  · rw [Fin.le_def, hdd.1, hdd.2]
    exact (KTreeRep_col_le_iff hdE.1 hdE.2.1 hJw).2 (le_of_lt hdE.2.2)
  · intro h
    exact hspec.2.2.1 (KLshiftOut_injOn (hends _ hpm hout) hdE hJw h)
  · intro e' he' hde' hne'
    obtain ⟨z, hz, hzJ, rfl⟩ := KTreeRep_mem_nodes_FOut hF hJ he'
    have hdz := (KTreeRep_arcLe_shiftOut_iff hdE (hends _ hz hzJ) hJw).1 hde'
    have hzd : z ≠ d := fun h => hne' (by rw [h])
    exact (KTreeRep_arcLe_shiftOut_iff (hends _ hpm hout) (hends _ hz hzJ) hJw).2 (hspec.2.2.2 z hz hdz hzd)

end OutSide

section OutSlots

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- `KLshiftOut J` as a bijection from the chords of `F` not inside `J` onto the chords of the outer polygon. -/
private noncomputable def KTreeRep_eOut (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KLEOut F J ≃ ↥(KLFOut F J) :=
  Equiv.ofBijective
    (fun d => ⟨KLshiftOut J d.1.1, Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨d.1.2, d.2⟩)⟩)
    ⟨fun d e h => Subtype.ext (Subtype.ext (KLshiftOut_injOn (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem d.1.2) d.2)
        (KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem e.1.2) e.2) (KLdiag_width hF hJ) (congrArg Subtype.val h))),
      fun y => by
        obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 y.2
        have hx' := Finset.mem_filter.1 hx
        exact ⟨⟨⟨x, hx'.1⟩, hx'.2⟩, Subtype.ext hxy⟩⟩

private theorem KTreeRep_eOut_symm (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (y : ↥(KLFOut F J)) :
    KLshiftOut J ((KTreeRep_eOut hF hn hJ).symm y).1.1 = y.1 := by
  exact congrArg Subtype.val ((KTreeRep_eOut hF hn hJ).apply_symm_apply y)

/-- **The relabelling of the slots of the outer polygon**: the glue leaf is the slot `BAslotOut J` (the cycle of the parent
of `J`), the other leaves are lifted by `KLoutV⁻¹`, the chords by `KLshiftOut⁻¹`. -/
private noncomputable def KTreeRep_ψ (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    BAslot (KLFOut F J) → BAslot F
  | Sum.inl k => if k = KLglueV J then BAslotOut F ⟨J, hJ⟩ else Sum.inl (KTreeRep_outVinv J k)
  | Sum.inr (Sum.inl y) => Sum.inr (Sum.inl ((KTreeRep_eOut hF hn hJ).symm y).1)
  | Sum.inr (Sum.inr y) => Sum.inr (Sum.inr ((KTreeRep_eOut hF hn hJ).symm y).1)

private theorem KTreeRep_ψ_leaf (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (k : Fin (n - KLwIn J + 1))
    (hk : k ≠ KLglueV J) : KTreeRep_ψ hF hn hJ (Sum.inl k) = Sum.inl (KTreeRep_outVinv J k) := by
  simp only [KTreeRep_ψ, hk, ↓reduceIte]

private theorem KTreeRep_ψ_glue (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    KTreeRep_ψ hF hn hJ (Sum.inl (KLglueV J)) = BAslotOut F ⟨J, hJ⟩ := by
  simp only [KTreeRep_ψ, ↓reduceIte]

private theorem KTreeRep_outVinv_outer (hJ : J.1.val + 2 ≤ J.2.val) {k : Fin (n - KLwIn J + 1)}
    (hk : k ≠ KLglueV J) : ¬KLInArc J (KTreeRep_outVinv J k) := by
  have hg := KTreeRep_glueV_val hJ
  have hk' : k.val ≠ J.1.val := fun h => hk (Fin.ext (by rw [hg]; exact h))
  have := k.isLt; have := J.2.isLt
  simp only [KLInArc, Fin.le_def, Fin.lt_def, KTreeRep_outVinv, KLunCol, KLwIn, not_and, not_lt]
  split_ifs <;> omega

omit [NeZero n] in
private theorem KTreeRep_outV_ne_glue (hJ : J.1.val + 2 ≤ J.2.val) {v : Fin n} (hv : ¬KLInArc J v) :
    KLoutV J v ≠ KLglueV J := by
  intro h
  have h1 := congrArg Fin.val h
  rw [KLoutV_val v (by omega), KTreeRep_glueV_val hJ] at h1
  simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv
  simp only [KLcol, KLwIn] at h1
  split_ifs at h1 <;> omega

/-- The facts about a chord outside `J` that the maps need. -/
private theorem KTreeRep_outChord (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (z : KLEOut F J) :
    KLOutEnds J z.1.1 := KLoutEnds_of hF hn hJ (KLmem_nodes_of_mem z.1.2) z.2

/-- **The nodes**: the node of `s` in the outer polygon is the `KLshiftOut`-image of the node of `ψ s` in `F`, which is not
inside `J`. -/
private theorem KTreeRep_ψ_node (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    BAslotNode (KLFOut F J) s = KLshiftOut J (BAslotNode F (KTreeRep_ψ hF hn hJ s)) ∧
      ¬KLArcLe (BAslotNode F (KTreeRep_ψ hF hn hJ s)) J := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k = KLglueV J
    · subst hk
      rw [KTreeRep_ψ_glue hF hn hJ]
      exact ⟨KTreeRep_leafPar_glue hF hn hJ, KLnot_arcLe_nodePar_self hF hn hJ⟩
    · have hv := KTreeRep_outVinv_outer hJw hk
      rw [KTreeRep_ψ_leaf hF hn hJ k hk]
      refine ⟨?_, KLnot_arcLe_leafPar hF hJ hv⟩
      have h := KTreeRep_leafPar_out hF hn hJ hv
      rw [KTreeRep_outV_outVinv hJw k] at h
      exact h
  · set z := (KTreeRep_eOut hF hn hJ).symm y with hz
    have hy := KTreeRep_eOut_symm hF hn hJ y
    refine ⟨?_, KLnot_arcLe_nodePar hF hn z.1.2 z.2⟩
    change KLnodePar (KLFOut F J) y.1 = KLshiftOut J (KLnodePar F z.1.1)
    rw [← hy]
    exact KTreeRep_nodePar_out hF hn hJ z.1.2 z.2
  · set z := (KTreeRep_eOut hF hn hJ).symm y with hz
    have hy := KTreeRep_eOut_symm hF hn hJ y
    exact ⟨hy.symm, z.2⟩

/-- **The starts**: the start of `s` in the outer polygon is `KLoutV J` of the start of `ψ s`, and the starts of the image
lie outside the open arc of `J`. -/
private theorem KTreeRep_ψ_start (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    BAslotStart (KLFOut F J) s = KLoutV J (BAslotStart F (KTreeRep_ψ hF hn hJ s)) ∧
      ((BAslotStart F (KTreeRep_ψ hF hn hJ s)).val ≤ J.1.val ∨ J.2.val ≤ (BAslotStart F (KTreeRep_ψ hF hn hJ s)).val) := by
  have hJw := KLdiag_width hF hJ
  rcases s with k | y | y
  · by_cases hk : k = KLglueV J
    · subst hk
      rw [KTreeRep_ψ_glue hF hn hJ]
      change KLglueV J = KLoutV J J.1 ∧ (J.1.val ≤ J.1.val ∨ J.2.val ≤ J.1.val)
      refine ⟨Fin.ext ?_, Or.inl le_rfl⟩
      rw [KLoutV_val _ (by omega), KTreeRep_glueV_val hJw, KLcol_of_le le_rfl]
    · have hv := KTreeRep_outVinv_outer hJw hk
      rw [KTreeRep_ψ_leaf hF hn hJ k hk]
      change k = KLoutV J (KTreeRep_outVinv J k) ∧
        ((KTreeRep_outVinv J k).val ≤ J.1.val ∨ J.2.val ≤ (KTreeRep_outVinv J k).val)
      refine ⟨(KTreeRep_outV_outVinv hJw k).symm, ?_⟩
      simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv
      omega
  · set z := (KTreeRep_eOut hF hn hJ).symm y with hz
    have hy := KTreeRep_eOut_symm hF hn hJ y
    have hE := KTreeRep_outChord hF hn hJ z
    simp only [KTreeRep_ψ, BAslotStart_out, ← hz]
    refine ⟨?_, ?_⟩
    · have := congrArg Prod.fst hy
      exact this.symm
    · rcases hE.1 with h | h
      · exact Or.inl h
      · exact Or.inr h
  · set z := (KTreeRep_eOut hF hn hJ).symm y with hz
    have hy := KTreeRep_eOut_symm hF hn hJ y
    have hE := KTreeRep_outChord hF hn hJ z
    simp only [KTreeRep_ψ, BAslotStart_in, ← hz]
    refine ⟨?_, ?_⟩
    · have := congrArg Prod.snd hy
      exact this.symm
    · rcases hE.2.1 with h | h
      · exact Or.inl h
      · exact Or.inr h

/-- **The image of `ψ` is closed under "same node"**: every slot of `F` whose node is not inside `J` is `ψ s`. -/
private theorem KTreeRep_ψ_closed (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) {x : BAslot F}
    (hx : ¬KLArcLe (BAslotNode F x) J) : ∃ s, KTreeRep_ψ hF hn hJ s = x := by
  have hJw := KLdiag_width hF hJ
  rcases x with v | J' | J'
  · have hv : ¬KLInArc J v := fun h => hx (KLleafPar_arcLe_of_inArc hF hJ h)
    exact ⟨Sum.inl (KLoutV J v), by
      rw [KTreeRep_ψ_leaf hF hn hJ _ (KTreeRep_outV_ne_glue hJw hv), KTreeRep_outVinv_outV hJw (by
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega)]⟩
  · by_cases h2 : J'.1 = J
    · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
      exact ⟨Sum.inl (KLglueV J), by rw [KTreeRep_ψ_glue hF hn hJ, hJ']⟩
    · have h1 : ¬KLArcLe J'.1 J := fun h =>
        hx (KLnodePar_arcLe hF hn hJ J'.2 h h2)
      refine ⟨Sum.inr (Sum.inl ((KTreeRep_eOut hF hn hJ) ⟨J', h1⟩)), ?_⟩
      simp only [KTreeRep_ψ, Equiv.symm_apply_apply]
  · have hx' : ¬KLArcLe J'.1 J := hx
    refine ⟨Sum.inr (Sum.inr ((KTreeRep_eOut hF hn hJ) ⟨J', hx'⟩)), ?_⟩
    simp only [KTreeRep_ψ, Equiv.symm_apply_apply]

/-- **`ψ` commutes with the cyclic successor.** -/
private theorem KTreeRep_ψ_next (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J)) :
    KTreeRep_ψ hF hn hJ (BAnextSlot (KLFOut F J) s) = BAnextSlot F (KTreeRep_ψ hF hn hJ s) := by
  have hJw := KLdiag_width hF hJ
  have hends : ∀ y : BAslot (KLFOut F J), KLOutEnds J (BAslotNode F (KTreeRep_ψ hF hn hJ y)) := fun y =>
    KLoutEnds_of hF hn hJ (BAslotNode_mem_nodes F _) (KTreeRep_ψ_node hF hn hJ y).2
  refine KTreeRep_next_map hF hn (KTreeRep_ψ hF hn hJ) ?_ ?_ ?_ s
  · intro s t
    constructor
    · intro h
      rw [(KTreeRep_ψ_node hF hn hJ s).1, (KTreeRep_ψ_node hF hn hJ t).1, h]
    · intro h
      rw [(KTreeRep_ψ_node hF hn hJ s).1, (KTreeRep_ψ_node hF hn hJ t).1] at h
      exact KLshiftOut_injOn (hends s) (hends t) hJw h
  · intro s t _
    obtain ⟨hs, hs1⟩ := KTreeRep_ψ_start hF hn hJ s
    obtain ⟨ht, ht1⟩ := KTreeRep_ψ_start hF hn hJ t
    rw [hs, ht, Fin.lt_def, Fin.lt_def, KLoutV_val _ (by omega), KLoutV_val _ (by omega)]
    have := (KTreeRep_col_le_iff ht1 hs1 hJw)
    omega
  · intro s x hx
    exact KTreeRep_ψ_closed hF hn hJ (by rw [hx]; exact (KTreeRep_ψ_node hF hn hJ s).2)

end OutSlots

/-! ## 5. The cut of the cactus at a chord -/

section CutEquivs

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KTreeRep_wbounds (hF : KLIsTSP F) (hJ : J ∈ F) :
    2 ≤ KLwIn J ∧ KLwIn J + 2 ≤ n := by
  have hJd := hF.1 J hJ
  obtain ⟨h1, h2, h3⟩ := hJd
  have := J.2.isLt
  rw [Fin.lt_def] at h1
  simp only [KLwIn]
  omega

private theorem KTreeRep_ψ_injective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Injective (KTreeRep_ψ hF hn hJ) := by
  intro s t h
  have hFo := KLisTSP_of_mem_TSP (KLFOut_mem_TSP (hF.1 J hJ) hF hn hJ)
  have hb := KTreeRep_wbounds hF hJ
  refine BAslot_start_inj hFo (by omega) ?_ ?_
  · rw [(KTreeRep_ψ_node hF hn hJ s).1, (KTreeRep_ψ_node hF hn hJ t).1, h]
  · rw [(KTreeRep_ψ_start hF hn hJ s).1, (KTreeRep_ψ_start hF hn hJ t).1, h]

private theorem KTreeRep_φ_injective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Injective (KTreeRep_φ hF hJ) := by
  intro s t h
  have hFi := KLisTSP_of_mem_TSP (KLFIn_mem_TSP (J := J) hF)
  have hb := KTreeRep_wbounds hF hJ
  refine BAslot_start_inj hFi (by omega) ?_ ?_
  · rw [(KTreeRep_φ_node hF hn hJ s).1, (KTreeRep_φ_node hF hn hJ t).1, h]
  · rw [(KTreeRep_φ_start hF hJ s).1, (KTreeRep_φ_start hF hJ t).1, h]

private theorem KTreeRep_ψ_ne_φ (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (s : BAslot (KLFOut F J))
    (t : BAslot (KLFIn F J)) : KTreeRep_ψ hF hn hJ s ≠ KTreeRep_φ hF hJ t := fun h =>
  (KTreeRep_ψ_node hF hn hJ s).2 (h ▸ (KTreeRep_φ_node hF hn hJ t).2)

/-- **The relabelling of the slots of the cut**: `BAslot F_out ⊕ BAslot F_in ≃ BAslot F`. -/
private noncomputable def KTreeRep_eN (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    BAslot (KLFOut F J) ⊕ BAslot (KLFIn F J) ≃ BAslot F :=
  Equiv.ofBijective (Sum.elim (KTreeRep_ψ hF hn hJ) (KTreeRep_φ hF hJ))
    ⟨KTreeRep_ψ_injective hF hn hJ |>.sumElim (KTreeRep_φ_injective hF hn hJ) (KTreeRep_ψ_ne_φ hF hn hJ),
      fun x => by
        by_cases hx : KLArcLe (BAslotNode F x) J
        · obtain ⟨s, hs⟩ := KTreeRep_φ_closed hF hn hJ hx
          exact ⟨Sum.inr s, hs⟩
        · obtain ⟨s, hs⟩ := KTreeRep_ψ_closed hF hn hJ hx
          exact ⟨Sum.inl s, hs⟩⟩

/-- The vertices of `n`-gon split into those outside and inside the arc of `J`. -/
private def KTreeRep_eL (J : Fin n × Fin n) : KLLOut J ⊕ KLLIn J ≃ Fin n :=
  ((Equiv.sumCompl (fun v : Fin n => KLInArc J v)).symm.trans (Equiv.sumComm _ _)).symm

/-- The leaves of the inner polygon: the glue leaf `last` and the vertices inside the arc of `J`. -/
private noncomputable def KTreeRep_eLin (J : Fin n × Fin n) (hJ : J.1.val + 2 ≤ J.2.val) :
    Option (KLLIn J) ≃ Fin (KLwIn J + 1) :=
  Equiv.ofBijective (fun o => o.elim (Fin.last _) (fun v => KLinV J v.1))
    ⟨by
      have hlt : ∀ v : KLLIn J, (KLinV J v.1).val < KLwIn J := by
        intro v
        have h1 := KLinV_val v.2
        have h2 := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
        simp only [KLwIn]; omega
      rintro (_ | v) (_ | v') h
      · rfl
      · have := hlt v'; simp only [Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · have := hlt v; simp only [Option.elim, Fin.ext_iff, Fin.val_last] at h; omega
      · simp only [Option.elim, Fin.ext_iff] at h
        have h1 := KLinV_val v.2
        have h2 := KLinV_val v'.2
        have h3 := v.2
        have h4 := v'.2
        simp only [KLInArc, Fin.le_def] at h3 h4
        exact congrArg some (Subtype.ext (Fin.ext (by omega))),
      fun k => by
        by_cases hk : k.val < KLwIn J
        · have hv : KLInArc J (KTreeRep_inVinv J k) := by
            have := KTreeRep_inVinv_val k (by omega)
            simp only [KLInArc, Fin.le_def, Fin.lt_def, this]
            simp only [KLwIn] at hk
            omega
          exact ⟨some ⟨_, hv⟩, KTreeRep_inV_inVinv k (by omega)⟩
        · exact ⟨none, Fin.ext (by have := k.isLt; simp only [Option.elim, Fin.val_last]; omega)⟩⟩

end CutEquivs

section CutEquivs2

variable {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- The leaves of the outer polygon: the glue leaf and the vertices outside the arc of `J`. -/
private noncomputable def KTreeRep_eLout (J : Fin n × Fin n) (hJ : J.1.val + 2 ≤ J.2.val) :
    Option (KLLOut J) ≃ Fin (n - KLwIn J + 1) :=
  Equiv.ofBijective (fun o => o.elim (KLglueV J) (fun v => KLoutV J v.1))
    ⟨by
      have hv : ∀ v : KLLOut J, v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := fun v => by
        have := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
        omega
      rintro (_ | v) (_ | v') h
      · rfl
      · exact absurd h.symm (KTreeRep_outV_ne_glue hJ v'.2)
      · exact absurd h (KTreeRep_outV_ne_glue hJ v.2)
      · have h' : KLoutV J v.1 = KLoutV J v'.1 := h
        have := congrArg (KTreeRep_outVinv J) h'
        rw [KTreeRep_outVinv_outV hJ (hv v), KTreeRep_outVinv_outV hJ (hv v')] at this
        exact congrArg some (Subtype.ext this),
      fun k => by
        by_cases hk : k = KLglueV J
        · exact ⟨none, hk.symm⟩
        · exact ⟨some ⟨_, KTreeRep_outVinv_outer hJ hk⟩, KTreeRep_outV_outVinv hJ k⟩⟩

/-- The edges of the cut: the chord `J` is the new edge of the splitting, the chords and `M`-edges of `F_out` and `F_in` are
the others. -/
private noncomputable def KTreeRep_Eb (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Option ((↥(KLFOut F J) ⊕ BAslot (KLFOut F J)) ⊕ (↥(KLFIn F J) ⊕ BAslot (KLFIn F J))) → ↥F ⊕ BAslot F
  | none => Sum.inl ⟨J, hJ⟩
  | some (Sum.inl (Sum.inl y)) => Sum.inl ((KTreeRep_eOut hF hn hJ).symm y).1
  | some (Sum.inl (Sum.inr s)) => Sum.inr (KTreeRep_ψ hF hn hJ s)
  | some (Sum.inr (Sum.inl y)) => Sum.inl ((KTreeRep_eIn hF J).symm y).1
  | some (Sum.inr (Sum.inr s)) => Sum.inr (KTreeRep_φ hF hJ s)

private theorem KTreeRep_Eb_bijective (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Function.Bijective (KTreeRep_Eb hF hn hJ) := by
  have hoc : ∀ y, ¬KLArcLe ((KTreeRep_eOut hF hn hJ).symm y).1.1 J := fun y =>
    ((KTreeRep_eOut hF hn hJ).symm y).2
  have hic : ∀ y, KLArcLe ((KTreeRep_eIn hF J).symm y).1.1 J ∧ ((KTreeRep_eIn hF J).symm y).1.1 ≠ J :=
    fun y => ((KTreeRep_eIn hF J).symm y).2
  have hJa : KLArcLe J J := ⟨le_rfl, le_rfl⟩
  constructor
  · rintro (_ | ⟨(y | s) | (y | s)⟩) (_ | ⟨(y' | s') | (y' | s')⟩) h <;>
      simp only [KTreeRep_Eb, reduceCtorEq, Sum.inl.injEq, Sum.inr.injEq] at h
    · rfl
    · exact absurd (by have e := congrArg Subtype.val h; rw [← e]; exact hJa) (hoc y')
    · exact absurd (congrArg Subtype.val h).symm (hic y').2
    · exact absurd (by have e := congrArg Subtype.val h; rw [e]; exact hJa) (hoc y)
    · exact congrArg (fun z => some (Sum.inl (Sum.inl z))) ((KTreeRep_eOut hF hn hJ).symm.injective (Subtype.ext h))
    · exact absurd (congrArg Subtype.val h ▸ (hic y').1) (hoc y)
    · exact congrArg (fun z => some (Sum.inl (Sum.inr z))) (KTreeRep_ψ_injective hF hn hJ h)
    · exact absurd h (KTreeRep_ψ_ne_φ hF hn hJ _ _)
    · exact absurd (congrArg Subtype.val h) (hic y).2
    · exact absurd (congrArg Subtype.val h ▸ (hic y).1) (hoc y')
    · exact congrArg (fun z => some (Sum.inr (Sum.inl z))) ((KTreeRep_eIn hF J).symm.injective (Subtype.ext h))
    · exact absurd h.symm (KTreeRep_ψ_ne_φ hF hn hJ _ _)
    · exact congrArg (fun z => some (Sum.inr (Sum.inr z))) (KTreeRep_φ_injective hF hn hJ h)
  · rintro (J' | x)
    · by_cases h2 : J'.1 = J
      · have hJ' : J' = ⟨J, hJ⟩ := Subtype.ext h2
        exact ⟨none, by rw [hJ']; rfl⟩
      · by_cases h1 : KLArcLe J'.1 J
        · exact ⟨some (Sum.inr (Sum.inl ((KTreeRep_eIn hF J) ⟨J', h1, h2⟩))), by
            simp only [KTreeRep_Eb, Equiv.symm_apply_apply]⟩
        · exact ⟨some (Sum.inl (Sum.inl ((KTreeRep_eOut hF hn hJ) ⟨J', h1⟩))), by
            simp only [KTreeRep_Eb, Equiv.symm_apply_apply]⟩
    · obtain ⟨y, rfl⟩ := (KTreeRep_eN hF hn hJ).surjective x
      rcases y with s | s
      · exact ⟨some (Sum.inl (Sum.inr s)), rfl⟩
      · exact ⟨some (Sum.inr (Sum.inr s)), rfl⟩

/-- **The relabelling of the edges of the cut**: `Option ((↥F_out ⊕ BAslot F_out) ⊕ (↥F_in ⊕ BAslot F_in)) ≃ ↥F ⊕ BAslot F`
(`none ↦` the chord `J`). -/
private noncomputable def KTreeRep_eE (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) :
    Option ((↥(KLFOut F J) ⊕ BAslot (KLFOut F J)) ⊕ (↥(KLFIn F J) ⊕ BAslot (KLFIn F J))) ≃ ↥F ⊕ BAslot F :=
  Equiv.ofBijective (KTreeRep_Eb hF hn hJ) (KTreeRep_Eb_bijective hF hn hJ)

end CutEquivs2

section CutLabels

variable {d L : ℕ} {n : ℕ} [NeZero n] {J : Fin n × Fin n}

omit [NeZero n] in
private theorem KTreeRep_val_add_one {m : ℕ} [NeZero m] (hm : 2 ≤ m) (v : Fin m) :
    (v + 1).val = (v.val + 1) % m := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]

private theorem KTreeRep_σIn_inV (σ : Fin n → Bool) {r : Fin n} (h1 : J.1 ≤ r) (h2 : r ≤ J.2) :
    KTreeRep_σIn J σ (KLinV J r) = σ r := by
  simp only [KTreeRep_σIn, KTreeRep_inVinv_inV h1 h2]

private theorem KTreeRep_σOut_outV (hJ : J.1.val + 2 ≤ J.2.val) (σ : Fin n → Bool) {r : Fin n}
    (h : r.val ≤ J.1.val ∨ J.2.val ≤ r.val) : KTreeRep_σOut J σ (KLoutV J r) = σ r := by
  simp only [KTreeRep_σOut, KTreeRep_outVinv_outV hJ h]

private theorem KTreeRep_inVinv_succ (hJ : J.1.val < J.2.val) {v : Fin n} (hv : KLInArc J v) :
    KTreeRep_inVinv J (KLinV J v + 1) = v + 1 := by
  have h1 := KLinV_val hv
  simp only [KLInArc, Fin.le_def, Fin.lt_def] at hv
  have := J.2.isLt
  have hw : 2 ≤ KLwIn J + 1 := by simp only [KLwIn]; omega
  refine Fin.ext ?_
  rw [KTreeRep_val_add_one (by omega : 2 ≤ n) v, KTreeRep_inVinv_val _ hJ, KTreeRep_val_add_one hw (KLinV J v), h1,
    Nat.mod_eq_of_lt (by simp only [KLwIn]; omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem KTreeRep_outVinv_succ (hJ : J.1.val + 2 ≤ J.2.val) {v : Fin n} (hv : ¬KLInArc J v) :
    KTreeRep_outVinv J (KLoutV J v + 1) = v + 1 := by
  have hv' : v.val < J.1.val ∨ J.2.val ≤ v.val := by
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at hv; omega
  have hv1 := v.isLt
  have := J.2.isLt
  have hp : 2 ≤ n - KLwIn J + 1 := by simp only [KLwIn]; omega
  refine Fin.ext ?_
  have hkv : (KLoutV J v + 1).val = (KLcol J v.val + 1) % (n - KLwIn J + 1) := by
    rw [KTreeRep_val_add_one hp, KLoutV_val (J := J) v (by omega)]
  change min (KLunCol J (KLoutV J v + 1).val) (n - 1) = (v + 1).val
  rw [KTreeRep_val_add_one (by omega : 2 ≤ n) v, hkv]
  rcases hv' with h1 | h1
  · have hc1 : KLcol J v.val = v.val := KLcol_of_le (by omega)
    have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = v.val + 1 := by
      rw [hc1]; exact Nat.mod_eq_of_lt (by simp only [KLwIn]; omega)
    rw [hm, KLunCol_of_le (by omega), Nat.mod_eq_of_lt (by omega : v.val + 1 < n)]
    omega
  · have hc1 : KLcol J v.val = v.val - (KLwIn J - 1) := KLcol_of_gt (by omega)
    by_cases h2 : v.val + 1 < n
    · have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = KLcol J v.val + 1 :=
        Nat.mod_eq_of_lt (by rw [hc1]; simp only [KLwIn]; omega)
      rw [hm, KLunCol_of_gt (by rw [hc1]; simp only [KLwIn]; omega), Nat.mod_eq_of_lt h2, hc1]
      simp only [KLwIn]; omega
    · have h3 : v.val + 1 = n := by omega
      have hm : (KLcol J v.val + 1) % (n - KLwIn J + 1) = 0 := by
        rw [hc1, show v.val - (KLwIn J - 1) + 1 = n - KLwIn J + 1 by simp only [KLwIn]; omega]
        exact Nat.mod_self _
      rw [hm, KLunCol_of_le (by omega), h3, Nat.mod_self]
      simp

omit [NeZero n] in
private theorem KTreeRep_Theta_swap {L : ℕ} [NeZero L] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (s s' : Bool) :
    BAThetaOf M t s' s = (BAThetaOf M t s s')ᵀ := by
  have hQ : BAMssOf M s' s = (BAMssOf M s s')ᵀ := by
    ext a b
    simp only [BAMssOf, Matrix.of_apply, Matrix.transpose_apply, mul_comm]
  unfold BAThetaOf PropThetaQ
  rw [hQ, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul]

end CutLabels

section CutMain

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

/-- The charge of the `M`-edge of a slot of the outer polygon is the charge of the `M`-edge of its image. -/
private theorem KTreeRep_charge_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (s : BAslot (KLFOut F J)) :
    BAMcharge F σ (KTreeRep_ψ hF hn hJ s) = BAMcharge (KLFOut F J) (KTreeRep_σOut J σ) s := by
  have hJw := KLdiag_width hF hJ
  simp only [BAMcharge_def]
  rw [← KTreeRep_ψ_next hF hn hJ s]
  obtain ⟨h1, h2⟩ := KTreeRep_ψ_start hF hn hJ (BAnextSlot (KLFOut F J) s)
  rw [h1, KTreeRep_σOut_outV hJw σ h2]

/-- The charge of the `M`-edge of a slot of the inner polygon is the charge of the `M`-edge of its image. -/
private theorem KTreeRep_charge_in (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (s : BAslot (KLFIn F J)) :
    BAMcharge F σ (KTreeRep_φ hF hJ s) = BAMcharge (KLFIn F J) (KTreeRep_σIn J σ) s := by
  simp only [BAMcharge_def]
  rw [← KTreeRep_φ_next hF hn hJ s]
  obtain ⟨h1, h2, h3⟩ := KTreeRep_φ_start hF hJ (BAnextSlot (KLFIn F J) s)
  rw [h1, KTreeRep_σIn_inV σ h2 h3]

end CutMain

section CutParts

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

private theorem KTreeRep_inVinv_last (hJ : J.1.val < J.2.val) : KTreeRep_inVinv J (Fin.last _) = J.2 := by
  refine Fin.ext ?_
  have := J.2.isLt
  simp only [KTreeRep_inVinv, Fin.val_last, KLwIn]
  omega

private theorem KTreeRep_inVinv_zero (_hJ : J.1.val < J.2.val) : KTreeRep_inVinv J 0 = J.1 := by
  refine Fin.ext ?_
  have := J.1.isLt
  simp only [KTreeRep_inVinv, Fin.val_zero]
  omega

private theorem KTreeRep_outVinv_glue (hJ : J.1.val + 2 ≤ J.2.val) : KTreeRep_outVinv J (KLglueV J) = J.1 := by
  refine Fin.ext ?_
  have := J.1.isLt
  simp only [KTreeRep_outVinv, KTreeRep_glueV_val hJ, KLunCol_of_le (le_refl _)]
  omega

private theorem KTreeRep_outVinv_glue_succ (hJ : J.1.val + 2 ≤ J.2.val) :
    KTreeRep_outVinv J (KLglueV J + 1) = J.2 := by
  refine Fin.ext ?_
  have h2 := J.2.isLt
  have hp : 2 ≤ n - KLwIn J + 1 := by simp only [KLwIn]; omega
  have hv : (KLglueV J + 1).val = J.1.val + 1 := by
    rw [KTreeRep_val_add_one hp, KTreeRep_glueV_val hJ]
    exact Nat.mod_eq_of_lt (by simp only [KLwIn]; omega)
  change min (KLunCol J (KLglueV J + 1).val) (n - 1) = J.2.val
  rw [hv, KLunCol_of_gt (by omega)]
  simp only [KLwIn]
  omega

omit [NeZero L] in
/-- The facts about a chord inside `J` for the charges of the inner polygon. -/
private theorem KTreeRep_chord_in (hF : KLIsTSP F) (σ : Fin n → Bool) (y : ↥(KLFIn F J)) :
    KTreeRep_σIn J σ y.1.1 = σ ((KTreeRep_eIn hF J).symm y).1.1.1 ∧
      KTreeRep_σIn J σ y.1.2 = σ ((KTreeRep_eIn hF J).symm y).1.1.2 := by
  obtain ⟨h1, -, h3⟩ := KTreeRep_inChord hF ((KTreeRep_eIn hF J).symm y)
  have hy := KTreeRep_eIn_symm hF y
  have e1 : y.1.1 = KLinV J ((KTreeRep_eIn hF J).symm y).1.1.1 := (congrArg Prod.fst hy).symm
  have e2 : y.1.2 = KLinV J ((KTreeRep_eIn hF J).symm y).1.1.2 := (congrArg Prod.snd hy).symm
  rw [e1, e2]
  exact ⟨KTreeRep_σIn_inV σ h1.1 (le_trans (le_of_lt h3) h1.2), KTreeRep_σIn_inV σ (le_trans h1.1 (le_of_lt h3)) h1.2⟩

omit [NeZero L] in
/-- The facts about a chord outside `J` for the charges of the outer polygon. -/
private theorem KTreeRep_chord_out (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F) (σ : Fin n → Bool)
    (y : ↥(KLFOut F J)) :
    KTreeRep_σOut J σ y.1.1 = σ ((KTreeRep_eOut hF hn hJ).symm y).1.1.1 ∧
      KTreeRep_σOut J σ y.1.2 = σ ((KTreeRep_eOut hF hn hJ).symm y).1.1.2 := by
  have hJw := KLdiag_width hF hJ
  have hE := KTreeRep_outChord hF hn hJ ((KTreeRep_eOut hF hn hJ).symm y)
  have hy := KTreeRep_eOut_symm hF hn hJ y
  have e1 : y.1.1 = KLoutV J ((KTreeRep_eOut hF hn hJ).symm y).1.1.1 := (congrArg Prod.fst hy).symm
  have e2 : y.1.2 = KLoutV J ((KTreeRep_eOut hF hn hJ).symm y).1.1.2 := (congrArg Prod.snd hy).symm
  rw [e1, e2]
  exact ⟨KTreeRep_σOut_outV hJw σ hE.1, KTreeRep_σOut_outV hJw σ hE.2.1⟩

/-- **The inner part of the cut is the cactus of the inner polygon** (the leaf `none` carries `Θᵀ = Θ^{(σ_j,σ_i)}`). -/
private theorem KTreeRep_in_part (hF : KLIsTSP F) (hJ : J ∈ F) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) (a : Fin n → Zd d L) (u : Zd d L) :
    KLgval d L (fun o : Option (KLLIn J) => o.elim u fun v => a ↑v)
        (fun o => o.elim (BAThetaOf M t (σ J.1) (σ J.2))ᵀ fun v => BACactusValLeafW M t σ ↑v)
        (fun o => o.elim (Sum.inl (Fin.last (KLwIn J))) fun v => Sum.inl (KLinV J ↑v))
        (BACactusValEdgeW M t (KLFIn F J) (KTreeRep_σIn J σ)) (BACactusValSrc (KLFIn F J))
        (BACactusValTgt (KLFIn F J)) =
      BACactusVal d L M t (KLFIn F J) (KTreeRep_σIn J σ) (KTreeRep_aIn J a u) := by
  have hJw := KLdiag_width hF hJ
  have hJ2 : J.1.val < J.2.val := by omega
  refine KLgval_congr (Equiv.refl _) (KTreeRep_eLin J hJw) (Equiv.refl _) ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  rotate_left 2
  · rintro (_ | v) <;> rfl
  · rintro (_ | v)
    · change KTreeRep_aIn J a u (Fin.last _) = u
      simp [KTreeRep_aIn]
    · change KTreeRep_aIn J a u (KLinV J v.1) = a v.1
      have hlt : (KLinV J v.1).val < KLwIn J := by
        have := KLinV_val v.2
        have h2 := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
        simp only [KLwIn]; omega
      simp only [KTreeRep_aIn]
      rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; simp at this; omega),
        KTreeRep_inVinv_inV v.2.1 (le_of_lt v.2.2)]
  · rintro (_ | v)
    · change BACactusValLeafW M t (KTreeRep_σIn J σ) (Fin.last _) = _
      simp only [BACactusValLeafW, Fin.last_add_one]
      change BAThetaOf M t (σ (KTreeRep_inVinv J (Fin.last _))) (σ (KTreeRep_inVinv J 0)) = _
      rw [KTreeRep_inVinv_last hJ2, KTreeRep_inVinv_zero hJ2]
      exact KTreeRep_Theta_swap M t _ _
    · change BACactusValLeafW M t (KTreeRep_σIn J σ) (KLinV J v.1) = BACactusValLeafW M t σ v.1
      simp only [BACactusValLeafW]
      change BAThetaOf M t (KTreeRep_σIn J σ (KLinV J v.1)) (σ (KTreeRep_inVinv J (KLinV J v.1 + 1))) = _
      rw [KTreeRep_σIn_inV σ v.2.1 (le_of_lt v.2.2), KTreeRep_inVinv_succ hJ2 v.2]

/-- **The outer part of the cut is the cactus of the outer polygon** (the glue leaf carries `Θ^{(σ_i,σ_j)}`). -/
private theorem KTreeRep_out_part (hF : KLIsTSP F) (_hn : 2 ≤ n) (hJ : J ∈ F)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (w : Zd d L) :
    KLgval d L (fun o : Option (KLLOut J) => o.elim w fun v => a ↑v)
        (fun o => o.elim (BAThetaOf M t (σ J.1) (σ J.2)) fun v => BACactusValLeafW M t σ ↑v)
        (fun o => o.elim (Sum.inl (KLglueV J)) fun v => Sum.inl (KLoutV J ↑v))
        (BACactusValEdgeW M t (KLFOut F J) (KTreeRep_σOut J σ)) (BACactusValSrc (KLFOut F J))
        (BACactusValTgt (KLFOut F J)) =
      BACactusVal d L M t (KLFOut F J) (KTreeRep_σOut J σ) (KTreeRep_aOut J a w) := by
  have hJw := KLdiag_width hF hJ
  have hv : ∀ v : KLLOut J, v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := fun v => by
    have := v.2
    simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
    omega
  refine KLgval_congr (Equiv.refl _) (KTreeRep_eLout J hJw) (Equiv.refl _) ?_ ?_ ?_ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl)
  rotate_left 2
  · rintro (_ | v) <;> rfl
  · rintro (_ | v)
    · change KTreeRep_aOut J a w (KLglueV J) = w
      simp [KTreeRep_aOut]
    · change KTreeRep_aOut J a w (KLoutV J v.1) = a v.1
      simp only [KTreeRep_aOut]
      rw [Function.update_of_ne (KTreeRep_outV_ne_glue hJw v.2), KTreeRep_outVinv_outV hJw (hv v)]
  · rintro (_ | v)
    · change BACactusValLeafW M t (KTreeRep_σOut J σ) (KLglueV J) = _
      simp only [BACactusValLeafW]
      change BAThetaOf M t (σ (KTreeRep_outVinv J (KLglueV J))) (σ (KTreeRep_outVinv J (KLglueV J + 1))) = _
      rw [KTreeRep_outVinv_glue hJw, KTreeRep_outVinv_glue_succ hJw]
      rfl
    · change BACactusValLeafW M t (KTreeRep_σOut J σ) (KLoutV J v.1) = BACactusValLeafW M t σ v.1
      simp only [BACactusValLeafW]
      change BAThetaOf M t (KTreeRep_σOut J σ (KLoutV J v.1)) (σ (KTreeRep_outVinv J (KLoutV J v.1 + 1))) = _
      rw [KTreeRep_σOut_outV hJw σ (hv v), KTreeRep_outVinv_succ hJw v.2]

end CutParts

section CutThm

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {F : Finset (Fin n × Fin n)} {J : Fin n × Fin n}

set_option synthInstance.maxSize 512 in
/-- **The chord-`J` term of one tree** (the new mathematics of K05b): the cactus of `F ∋ J` with the weight `tΘ` of the
chord `J` replaced by `Θ·Θ` (`Θ = Θ^{(σ_i,σ_j)}`) is `Σ_x Γ_{F_out}(σ_out, a_out^x) Γ_{F_in}(σ_in, a_in^x)`: the splitting
`KLgval_split` at the chord, after the relabelling `BAslot F_out ⊕ BAslot F_in ≃ BAslot F` of the slots, which preserves
the cycles (`KTreeRep_ψ_next`, `KTreeRep_φ_next`); the new leaf of the inner polygon is `Θ^{(σ_j,σ_i)} = Θᵀ`, no symmetry
of `M` is used. -/
private theorem KTreeRep_cut (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    KLgval d L (Nd := BAslot F) (Lf := Fin n) a (BACactusValLeafW M t σ) (BAslotLeaf F)
      (Function.update (BACactusValEdgeW M t F σ) (Sum.inl ⟨J, hJ⟩)
        (BAThetaOf M t (σ J.1) (σ J.2) * BAThetaOf M t (σ J.1) (σ J.2)))
      (BACactusValSrc F) (BACactusValTgt F) =
    ∑ x : Zd d L, BACactusVal d L M t (KLFOut F J) (KTreeRep_σOut J σ) (KTreeRep_aOut J a x) *
      BACactusVal d L M t (KLFIn F J) (KTreeRep_σIn J σ) (KTreeRep_aIn J a x) := by
  have hJw := KLdiag_width hF hJ
  have hb := KTreeRep_wbounds hF hJ
  have hΘ := KTreeRep_Theta_swap M t (σ J.1) (σ J.2)
  have key := KLgval_split (d := d) (L := L)
    (fun v : KLLOut J => a v.1) (fun v => BACactusValLeafW M t σ v.1)
    (fun v => (Sum.inl (KLoutV J v.1) : BAslot (KLFOut F J)))
    (BACactusValEdgeW M t (KLFOut F J) (KTreeRep_σOut J σ)) (BACactusValSrc (KLFOut F J))
    (BACactusValTgt (KLFOut F J))
    (fun v : KLLIn J => a v.1) (fun v => BACactusValLeafW M t σ v.1)
    (fun v => (Sum.inl (KLinV J v.1) : BAslot (KLFIn F J)))
    (BACactusValEdgeW M t (KLFIn F J) (KTreeRep_σIn J σ)) (BACactusValSrc (KLFIn F J))
    (BACactusValTgt (KLFIn F J))
    (BAThetaOf M t (σ J.1) (σ J.2)) 1 (BAThetaOf M t (σ J.1) (σ J.2))
    (Sum.inl (Fin.last _) : BAslot (KLFIn F J)) (Sum.inl (KLglueV J) : BAslot (KLFOut F J))
  refine ((KLgval_congr (KTreeRep_eN hF hn hJ) (KTreeRep_eL J) (KTreeRep_eE hF hn hJ)
    ?_ ?_ ?_ ?_ ?_ ?_).symm.trans key).trans ?_
  · rintro (v | v) <;> rfl
  · rintro (v | v) <;> rfl
  · rintro (v | v)
    · have hv' : v.1.val ≤ J.1.val ∨ J.2.val ≤ v.1.val := by
        have := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def, not_and, not_lt] at this
        omega
      change (Sum.inl v.1 : BAslot F) = KTreeRep_ψ hF hn hJ (Sum.inl (KLoutV J v.1))
      rw [KTreeRep_ψ_leaf hF hn hJ _ (KTreeRep_outV_ne_glue hJw v.2), KTreeRep_outVinv_outV hJw hv']
    · have hlt : (KLinV J v.1).val < KLwIn J := by
        have := KLinV_val v.2
        have h2 := v.2
        simp only [KLInArc, Fin.le_def, Fin.lt_def] at h2
        simp only [KLwIn]; omega
      change (Sum.inl v.1 : BAslot F) = KTreeRep_φ hF hJ (Sum.inl (KLinV J v.1))
      rw [KTreeRep_φ_leaf hF hJ _ hlt, KTreeRep_inVinv_inV v.2.1 (le_of_lt v.2.2)]
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · change Function.update _ (Sum.inl (⟨J, hJ⟩ : ↥F)) _ (Sum.inl (⟨J, hJ⟩ : ↥F)) = _
      rw [Function.update_self, Matrix.mul_one]
      rfl
    · have hne : (Sum.inl ((KTreeRep_eOut hF hn hJ).symm y).1 : ↥F ⊕ BAslot F) ≠ (Sum.inl (⟨J, hJ⟩ : ↥F) : ↥F ⊕ BAslot F) := fun h =>
        ((KTreeRep_eOut hF hn hJ).symm y).2 (by
          have := congrArg Subtype.val (Sum.inl.inj h)
          simp only at this
          rw [this]; exact ⟨le_rfl, le_rfl⟩)
      change Function.update _ _ _ (Sum.inl ((KTreeRep_eOut hF hn hJ).symm y).1) = _
      rw [Function.update_of_ne hne]
      change (t : ℂ) • BAThetaOf M t (σ _) (σ _) = (t : ℂ) • BAThetaOf M t (KTreeRep_σOut J σ y.1.1)
        (KTreeRep_σOut J σ y.1.2)
      rw [(KTreeRep_chord_out hF hn hJ σ y).1, (KTreeRep_chord_out hF hn hJ σ y).2]
    · change Function.update _ _ _ (Sum.inr (KTreeRep_ψ hF hn hJ s)) = _
      rw [Function.update_of_ne (by simp)]
      change M (BAMcharge F σ (KTreeRep_ψ hF hn hJ s)) = M (BAMcharge (KLFOut F J) (KTreeRep_σOut J σ) s)
      rw [KTreeRep_charge_out hF hn hJ σ s]
    · have hne : (Sum.inl ((KTreeRep_eIn hF J).symm y).1 : ↥F ⊕ BAslot F) ≠ (Sum.inl (⟨J, hJ⟩ : ↥F) : ↥F ⊕ BAslot F) := fun h =>
        ((KTreeRep_eIn hF J).symm y).2.2 (congrArg Subtype.val (Sum.inl.inj h))
      change Function.update _ _ _ (Sum.inl ((KTreeRep_eIn hF J).symm y).1) = _
      rw [Function.update_of_ne hne]
      change (t : ℂ) • BAThetaOf M t (σ _) (σ _) = (t : ℂ) • BAThetaOf M t (KTreeRep_σIn J σ y.1.1)
        (KTreeRep_σIn J σ y.1.2)
      rw [(KTreeRep_chord_in hF σ y).1, (KTreeRep_chord_in hF σ y).2]
    · change Function.update _ _ _ (Sum.inr (KTreeRep_φ hF hJ s)) = _
      rw [Function.update_of_ne (by simp)]
      change M (BAMcharge F σ (KTreeRep_φ hF hJ s)) = M (BAMcharge (KLFIn F J) (KTreeRep_σIn J σ) s)
      rw [KTreeRep_charge_in hF hn hJ σ s]
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · exact (KTreeRep_φ_last hF hJ _ (by simp)).symm
    all_goals rfl
  · rintro (_ | ⟨(y | s) | (y | s)⟩)
    · exact (KTreeRep_ψ_glue hF hn hJ).symm
    · rfl
    · exact (KTreeRep_ψ_next hF hn hJ s).symm
    · rfl
    · exact (KTreeRep_φ_next hF hn hJ s).symm
  · simp only [KTreeRep_in_part hF hJ M t σ a, KTreeRep_out_part hF hn hJ M t σ a]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring

end CutThm

/-! ## 6. Target 2: `baChordPairs` -/

section ChordPairs

/-- `W^d · W^{-d(p-1)} · W^{-d(q-1)} = W^{-d(n-1)}` for `(p - 1) + (q - 1) = n ≥ 2`, also at `W^d = 0`. -/
private theorem KTreeRep_wpow (w : ℂ) {n a b : ℕ} (hn : 2 ≤ n) (hab : a + b = n) :
    w * (w⁻¹) ^ a * (w⁻¹) ^ b = (w⁻¹) ^ (n - 1) := by
  rw [mul_assoc, ← pow_add, hab]
  by_cases hw : w = 0
  · subst hw
    simp [zero_pow (show n ≠ 0 by omega), zero_pow (show n - 1 ≠ 0 by omega)]
  · rw [show n = (n - 1) + 1 by omega, pow_succ, ← mul_assoc, mul_comm w, mul_assoc, mul_inv_cancel₀ hw]
    simp

private theorem KTreeRep_sum_swap {d L : ℕ} [NeZero L] {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Zd d L → ℂ) (B : β → Zd d L → ℂ) :
    ∑ G ∈ S, ∑ H ∈ T, ∑ x : Zd d L, A G x * B H x = ∑ x : Zd d L, (∑ G ∈ S, A G x) * (∑ H ∈ T, B H x) := by
  calc _ = ∑ G ∈ S, ∑ x : Zd d L, ∑ H ∈ T, A G x * B H x := Finset.sum_congr rfl fun G _ => Finset.sum_comm
    _ = ∑ x : Zd d L, ∑ G ∈ S, ∑ H ∈ T, A G x * B H x := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun x _ => (Finset.sum_mul_sum _ _ _ _).symm

set_option synthInstance.maxSize 512 in
/-- **Target 2** (`BAChordPairsStmt`): the chord part of `W^{-d(n-1)} Σ_F ∂_tΓ_F` is the sum over the diagonals `J = (i, j)` of
the `(i+1, j+1)` summands of `treeEqRhsS` at `S = 1`, for every family `K` with `BASplicedFam`.  Per tree `F ∋ J` the
chord-`J` term is `KTreeRep_cut`; the sum over `F ∋ J` is the cut bijection `KLsum_cut`, the factor `W^d W^{-d(p-1)} W^{-d(q-1)}`
with `p + q = n + 2` closes the `W` powers (`p, q ≥ 3`: clause 3 of `BASplicedFam` for both pieces). -/
theorem baChordPairs (d : ℕ) : BAChordPairsStmt d := by
  intro L W _ g κ E m hr K hK n _ hn σ a t ht0 ht1
  obtain ⟨-, -, hK3⟩ := hK
  have hn2 : 2 ≤ n := by omega
  set M := BAMsigma d L (BAMB d L g (E : ℂ) m) with hM
  set w : ℂ := (W : ℂ) ^ d with hw
  let f : ∀ J : Fin n × Fin n, Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ := fun J G H =>
    ∑ x : Zd d L, BAGamma d L (n - KLwIn J + 1) M t G (KTreeRep_σOut J σ) (KTreeRep_aOut J a x) *
      BAGamma d L (KLwIn J + 1) M t H (KTreeRep_σIn J σ) (KTreeRep_aIn J a x)
  have step1 : ∀ F ∈ TSP n, ∑ J : ↥F, KLgval d L (Nd := BAslot F) (Lf := Fin n) a
        (BACactusValLeafW M t σ) (BAslotLeaf F)
        (Function.update (BACactusValEdgeW M t F σ) (Sum.inl J)
          (BATheta d L g E m t (σ J.1.1) (σ J.1.2) * BATheta d L g E m t (σ J.1.1) (σ J.1.2)))
        (BACactusValSrc F) (BACactusValTgt F) = ∑ J ∈ F, f J (KLFOut F J) (KLFIn F J) := by
    intro F hF
    rw [← Finset.sum_coe_sort F (fun J => f J (KLFOut F J) (KLFIn F J))]
    exact Finset.sum_congr rfl fun J _ => KTreeRep_cut (KLisTSP_of_mem_TSP hF) hn2 J.2 M t σ a
  rw [Finset.sum_congr rfl step1, Finset.sum_comm' (t' := diagonals n)
    (s' := fun J => (TSP n).filter (fun F => J ∈ F)) (by
      intro F J
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, (mem_TSP.1 h.1).1 h.2⟩, fun h => ⟨h.1.1, h.1.2⟩⟩)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have hJd := KLmem_diagonals_iff.1 hJ
  have hJw := KLwidth_of_isDiag hJd
  have hb : 2 ≤ KLwIn J ∧ KLwIn J + 2 ≤ n := by
    obtain ⟨h1, h2, h3⟩ := hJd
    have := J.2.isLt
    rw [Fin.lt_def] at h1
    simp only [KLwIn]; omega
  rw [KLsum_cut hJd hn2 (f J)]
  have hcL : ∀ x : Zd d L, K t (LoopIdx.cutGlueL (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a)) =
      w⁻¹ ^ (n - KLwIn J) * ∑ G ∈ TSP (n - KLwIn J + 1),
        BAGamma d L (n - KLwIn J + 1) M t G (KTreeRep_σOut J σ) (KTreeRep_aOut J a x) := fun x => by
    rw [KTreeRep_cutGlueL_eq J hJw σ a x]
    exact hK3 t (n - KLwIn J + 1) (by omega) _ _
  have hcR : ∀ x : Zd d L, K t (LoopIdx.cutGlueR (J.1.val + 1) (J.2.val + 1) x (KLloopOf d L σ a)) =
      w⁻¹ ^ (KLwIn J) * ∑ H ∈ TSP (KLwIn J + 1),
        BAGamma d L (KLwIn J + 1) M t H (KTreeRep_σIn J σ) (KTreeRep_aIn J a x) := fun x => by
    rw [KTreeRep_cutGlueR_eq J (by omega) σ a x]
    exact hK3 t (KLwIn J + 1) (by omega) _ _
  simp only [hcL, hcR, f]
  have hpow := KTreeRep_wpow w (n := n) (a := n - KLwIn J) (b := KLwIn J) hn2 (by omega)
  have e := KTreeRep_sum_swap (d := d) (L := L) (TSP (n - KLwIn J + 1)) (TSP (KLwIn J + 1))
    (fun G x => BAGamma d L (n - KLwIn J + 1) M t G (KTreeRep_σOut J σ) (KTreeRep_aOut J a x))
    (fun H x => BAGamma d L (KLwIn J + 1) M t H (KTreeRep_σIn J σ) (KTreeRep_aIn J a x))
  rw [e, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← hpow]
  ring

end ChordPairs

/-! ## 7. Target 3: `baKcac_isKLoopS` -/

section IsKLoop

/-- **The pair partition of `treeEqRhsS`** (supervisor 0350 "Counting"): the pairs `1 ≤ k < l ≤ n` are the `n` leaf pairs
(`(v+1, v+2)` for `v ≤ n-2`, the wrap pair `(1, n)` for `v = n-1`) and the `n(n-3)/2` diagonal pairs `(i+1, j+1)`, `n ≥ 3`. -/
private theorem KTreeRep_pairs {n : ℕ} [NeZero n] (hn : 3 ≤ n) (G : ℕ → ℕ → ℂ) :
    ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, G k l =
      ∑ v : Fin n, G (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) +
        ∑ J ∈ diagonals n, G (J.1.val + 1) (J.2.val + 1) := by
  have hn0 := NeZero.pos n
  have hA : ∑ k ∈ Finset.Icc 1 n, ∑ l ∈ Finset.Ioc k n, G k l =
      ∑ p : Fin n × Fin n, if p.1 < p.2 then G (p.1.val + 1) (p.2.val + 1) else 0 := by
    rw [← Finset.sum_filter]
    refine (Finset.sum_finset_product ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => p.1 < p.2))
      (Finset.Icc 1 n) (fun k => Finset.Ioc k n)
      (fun p => by
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Ioc]; omega)
      (f := fun p => G p.1 p.2)).symm.trans ?_
    refine Finset.sum_nbij' (fun p => (⟨min (p.1 - 1) (n - 1), by omega⟩, ⟨min (p.2 - 1) (n - 1), by omega⟩))
      (fun p => (p.1.val + 1, p.2.val + 1)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, true_and, Fin.lt_def] at hp ⊢
      omega
    · intro p hp
      have h1 := p.1.isLt
      have h2 := p.2.isLt
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_univ, true_and, Fin.lt_def] at hp ⊢
      omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro p hp
      refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only <;> omega
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      have : min (p.1 - 1) (n - 1) + 1 = p.1 := by omega
      have : min (p.2 - 1) (n - 1) + 1 = p.2 := by omega
      simp only [*]
  have hpt : ∀ p : Fin n × Fin n, (if p.1 < p.2 then G (p.1.val + 1) (p.2.val + 1) else 0) =
      (if IsDiag n p.1 p.2 then G (p.1.val + 1) (p.2.val + 1) else 0) +
      (if p.2.val = p.1.val + 1 then G (p.1.val + 1) (p.2.val + 1) else 0) +
      (if p.1.val = 0 ∧ p.2.val = n - 1 then G (p.1.val + 1) (p.2.val + 1) else 0) := by
    intro p
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    unfold IsDiag
    simp only [Fin.lt_def]
    split_ifs <;> first | omega | simp
  have hD : ∑ p : Fin n × Fin n, (if IsDiag n p.1 p.2 then G (p.1.val + 1) (p.2.val + 1) else 0) =
      ∑ J ∈ diagonals n, G (J.1.val + 1) (J.2.val + 1) := by
    simp only [diagonals, Finset.sum_filter]
  have hL1 : ∑ p : Fin n × Fin n, (if p.2.val = p.1.val + 1 then G (p.1.val + 1) (p.2.val + 1) else 0) =
      ∑ v : Fin n, (if v.val + 1 < n then G (v.val + 1) (v.val + 2) else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.val + 1 < n
    · rw [Finset.sum_eq_single (⟨i.val + 1, h⟩ : Fin n)]
      · simp [h]
      · intro j _ hj
        have : j.val ≠ i.val + 1 := fun e => hj (Fin.ext e)
        simp [this]
      · simp
    · simp only [h, ite_false]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := j.isLt
      simp only [show ¬ j.val = i.val + 1 by omega, ite_false]
  have hL2 : ∑ p : Fin n × Fin n, (if p.1.val = 0 ∧ p.2.val = n - 1 then G (p.1.val + 1) (p.2.val + 1) else 0) =
      G 1 n := by
    rw [Finset.sum_eq_single ((⟨0, hn0⟩, ⟨n - 1, by omega⟩) : Fin n × Fin n)]
    · simp only [and_self, ite_true]
      congr 1
      omega
    · intro p _ hp
      refine ite_eq_right_iff.2 fun ⟨e1, e2⟩ => ?_
      exact absurd (Prod.ext (Fin.ext e1) (Fin.ext e2)) hp
    · simp
  have hL3 : ∑ v : Fin n, G (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) =
      ∑ v : Fin n, (if v.val + 1 < n then G (v.val + 1) (v.val + 2) else 0) + G 1 n := by
    have : ∀ v : Fin n, G (if v.val + 1 < n then v.val + 1 else 1) (if v.val + 1 < n then v.val + 2 else n) =
        (if v.val + 1 < n then G (v.val + 1) (v.val + 2) else 0) + (if v.val = n - 1 then G 1 n else 0) := by
      intro v
      have := v.isLt
      by_cases h : v.val + 1 < n
      · simp [h]; omega
      · simp [h]; omega
    simp only [this, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · simp
    · intro v _ hv
      have : v.val ≠ n - 1 := fun e => hv (Fin.ext e)
      simp [this]
    · simp
  rw [hA]
  simp only [hpt, Finset.sum_add_distrib]
  rw [hD, hL1, hL2, hL3]
  ring

end IsKLoop

section IsKLoop2

variable {d L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

private theorem KTreeRep_sum_one (f h : Zd d L → ℂ) :
    ∑ a : Zd d L, ∑ b : Zd d L, f a * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * h b = ∑ a : Zd d L, f a * h a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.one_apply]

/-- `treeEqRhsS` at `S = 1`, `n = 2`: the only cut is `(1,2)` (copy of `BAKSolve_rhs_two`, `BA/KSolve.lean:175`). -/
private theorem KTreeRep_rhs_two (K : LoopIdx (Zd d L) → ℂ) (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    treeEqRhsS d L W 1 K ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      ((W : ℂ) ^ d) * ∑ a : Zd d L, K ⟨[σ₁, σ₂], [a, a₂]⟩ * K ⟨[σ₁, σ₂], [a₁, a]⟩ := by
  have hlen : (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).length = 2 := rfl
  have h12 : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  have hIoc1 : Finset.Ioc 1 2 = ({2} : Finset ℕ) := by decide
  have hIoc2 : Finset.Ioc 2 2 = (∅ : Finset ℕ) := by decide
  rw [treeEqRhsS, hlen, h12, Finset.sum_insert (by decide), Finset.sum_singleton, hIoc1, hIoc2,
    Finset.sum_singleton, Finset.sum_empty, add_zero]
  have hL : ∀ a : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueL 1 2 a = ⟨[σ₁, σ₂], [a, a₂]⟩ := by
    intro a; simp [LoopIdx.cutGlueL]
  have hR : ∀ b : Zd d L,
      (⟨[σ₁, σ₂], [a₁, a₂]⟩ : LoopIdx (Zd d L)).cutGlueR 1 2 b = ⟨[σ₁, σ₂], [a₁, b]⟩ := by
    intro b; simp [LoopIdx.cutGlueR]
  simp only [hL, hR]
  rw [KTreeRep_sum_one (fun a => K ⟨[σ₁, σ₂], [a, a₂]⟩) (fun b => K ⟨[σ₁, σ₂], [a₁, b]⟩)]

/-- **The `2`-loop equation** for the closed form `(Kn2sol)` of `BAKcac`: `∂_t(W^{-d} ΘM) = W^{-d} ΘMΘM =
W^d (W^{-d} ΘM)(W^{-d} ΘM)` (copy of `BAKSolve_two_hasDerivAt`, `BA/KSolve.lean:359`). -/
private theorem KTreeRep_two_hasDerivAt (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    HasDerivAt (fun s => BAKcac d L W g E m s ⟨[σ₁, σ₂], [a₁, a₂]⟩)
      (treeEqRhsS d L W 1 (BAKcac d L W g E m t) ⟨[σ₁, σ₂], [a₁, a₂]⟩) t := by
  have hS := (BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.1
  have hfun : (fun s => BAKcac d L W g E m s ⟨[σ₁, σ₂], [a₁, a₂]⟩) = fun s => (((W : ℂ) ^ d)⁻¹) *
      (BATheta d L g E m s σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂ := funext fun s => hS s σ₁ σ₂ a₁ a₂
  have h1 : HasDerivAt (fun s => (((W : ℂ) ^ d)⁻¹) *
      (BATheta d L g E m s σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂)
      ((((W : ℂ) ^ d)⁻¹) * (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ *
        BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a₂) t := by
    refine HasDerivAt.const_mul _ ?_
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun c _ => (BATheta_hasDerivAt d L g κ E m hr ht0 ht1 σ₁ σ₂ a₁ c).mul_const _
  rw [hfun, KTreeRep_rhs_two]
  refine h1.congr_deriv ?_
  simp only [hS t σ₁ σ₂]
  have hYY : BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ * BATheta d L g E m t σ₁ σ₂ *
      BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ = (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) *
      (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) := Matrix.mul_assoc _ _ _
  rw [hYY, Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ((W : ℂ) ^ d) * (((W : ℂ) ^ d)⁻¹) * (((W : ℂ) ^ d)⁻¹) = (((W : ℂ) ^ d)⁻¹) := by
    by_cases hw : ((W : ℂ) ^ d) = 0
    · simp [hw]
    · rw [mul_inv_cancel₀ hw, one_mul]
  linear_combination (-((BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a₁ a *
    (BATheta d L g E m t σ₁ σ₂ * BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) a a₂)) * h

/-- At `t = 0`, `Θ = 1` and `BAKcac` is the `M`-loop at the length `2` (copy of `BAKSolve_zero`, `BA/KSolve.lean:459`). -/
private theorem KTreeRep_zero_two (σ₁ σ₂ : Bool) (a₁ a₂ : Zd d L) :
    BAKcac d L W g E m 0 ⟨[σ₁, σ₂], [a₁, a₂]⟩ =
      BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨[σ₁, σ₂], [a₁, a₂]⟩ := by
  rw [(BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.1 0 σ₁ σ₂ a₁ a₂]
  have h0 : BATheta d L g E m 0 σ₁ σ₂ = 1 := by simp [BATheta, PropThetaQ]
  rw [h0, Matrix.one_mul]
  simp [BAMLoop, BAMss, LoopIdx.length, List.rotate]

end IsKLoop2

section IsKLoop3

variable {d L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ}

omit [NeZero L] in
/-- A well-formed loop is `KLloopOf σ a` for some `n`, `σ : Fin n → Bool`, `a : Fin n → Zd d L`. -/
private theorem KTreeRep_exists_loopOf {I : LoopIdx (Zd d L)} (hI : I.WF) :
    ∃ (n : ℕ) (σ : Fin n → Bool) (a : Fin n → Zd d L), I = KLloopOf d L σ a := by
  obtain ⟨σ, a⟩ := I
  have h : σ.length = a.length := hI
  refine ⟨a.length, fun i => σ.getD i false, fun i => a.getD i 0, ?_⟩
  simp only [KLloopOf, LoopIdx.mk.injEq]
  constructor
  · refine List.ext_getElem (by simp [h]) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  · refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD]

/-- **The `n`-loop equation, `n ≥ 3`**: `∂_t 𝒦^{(n)} = treeEqRhsS` for the spliced family: `baGamma_hasDerivAt`, the leaf
pairs `baLeafPairs`, the chord pairs `baChordPairs`, and the pair partition of `treeEqRhsS` (`KTreeRep_pairs`). -/
private theorem KTreeRep_deriv_ge3 (hr : BAReal d L g κ E m) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ} [NeZero n]
    (hn : 3 ≤ n) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    HasDerivAt (fun s => BAKcac d L W g E m s (KLloopOf d L σ a))
      (treeEqRhsS d L W 1 (BAKcac d L W g E m t) (KLloopOf d L σ a)) t := by
  have hspl := BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)
  have hfun : (fun s => BAKcac d L W g E m s (KLloopOf d L σ a)) = fun s => ((((W : ℂ) ^ d)⁻¹)) ^ (n - 1) *
      ∑ F ∈ TSP n, BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) s F σ a := funext fun s => hspl.2.2 s n hn σ a
  have hD : HasDerivAt (fun s => ((((W : ℂ) ^ d)⁻¹)) ^ (n - 1) *
      ∑ F ∈ TSP n, BAGamma d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) s F σ a)
      ((((W : ℂ) ^ d)⁻¹ ) ^ (n - 1) * ∑ F ∈ TSP n, BAGammaDerivRHS d L n g E m t F σ a) t :=
    (HasDerivAt.fun_sum fun F hF => baGamma_hasDerivAt d L n g κ E m (by omega) hr F (KLisTSP_of_mem_TSP hF) σ a t ht0
      ht1).const_mul _
  rw [hfun]
  refine hD.congr_deriv ?_
  have hleaf := baLeafPairs d L W g κ E m hr _ hspl n hn σ a t ht0 ht1
  have hchord := baChordPairs d L W g κ E m hr _ hspl n hn σ a t ht0 ht1
  have hlen : (KLloopOf d L σ a).length = n := by simp [KLloopOf, LoopIdx.length]
  symm
  unfold treeEqRhsS
  rw [hlen]
  simp only [KTreeRep_sum_one]
  rw [KTreeRep_pairs hn (fun k l => ∑ x : Zd d L, BAKcac d L W g E m t (LoopIdx.cutGlueL k l x (KLloopOf d L σ a)) *
    BAKcac d L W g E m t (LoopIdx.cutGlueR k l x (KLloopOf d L σ a))), mul_add, Finset.mul_sum, Finset.mul_sum]
  unfold BAGammaDerivRHS
  rw [Finset.sum_add_distrib, mul_add, hleaf, hchord]

end IsKLoop3

set_option synthInstance.maxSize 512 in
/-- **Target 3** (`baKcac_isKLoopS`): under `BAReal`, the spliced family `BAKcac` of K05a solves `IsKLoopS` on `[0,1)` for the
block Anderson data (`S = 1`, initial data `BAMLoop`).  (a) the derivative: `n = 2` the closed form `(Kn2sol)`, `n ≥ 3` the
leaf pairs and the chord pairs; (b) `t = 0`: `BACactusVal_sum_zero_BAMLoop`, resp. `Θ_0 = 1`; (c) length `1`. -/
theorem baKcac_isKLoopS {d L W : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) (BAKcac d L W g E m) := by
  have hspl := BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)
  refine ⟨fun t ht I hI h2 => ?_, fun I hI h2 => ?_, fun t _ s a => hspl.1 t s a⟩
  · rcases (show I.length = 2 ∨ 3 ≤ I.length by omega) with hl | hl
    · obtain ⟨σ₁, σ₂, a₁, a₂, rfl⟩ := exists_eq_of_length_two hI hl
      exact KTreeRep_two_hasDerivAt hr ht.1 ht.2 σ₁ σ₂ a₁ a₂
    · obtain ⟨n, σ, a, rfl⟩ := KTreeRep_exists_loopOf hI
      have hn : 3 ≤ n := by simpa [KLloopOf, LoopIdx.length] using hl
      have : NeZero n := ⟨by omega⟩
      exact KTreeRep_deriv_ge3 hr ht.1 ht.2 hn σ a
  · rcases (show I.length = 2 ∨ 3 ≤ I.length by omega) with hl | hl
    · obtain ⟨σ₁, σ₂, a₁, a₂, rfl⟩ := exists_eq_of_length_two hI hl
      exact KTreeRep_zero_two σ₁ σ₂ a₁ a₂
    · obtain ⟨n, σ, a, rfl⟩ := KTreeRep_exists_loopOf hI
      have hn : 3 ≤ n := by simpa [KLloopOf, LoopIdx.length] using hl
      have : NeZero n := ⟨by omega⟩
      rw [hspl.2.2 0 n hn σ a]
      exact BACactusVal_sum_zero_BAMLoop (by omega) W _ σ a

/-! ## 8. Targets 4 and 5: `baKsolve`, `baTreeRep` -/

/-- **Target 4** (`baKsolve`): the pin `BAKsolve` (K03, `BA/KSolve.lean:58`) is proved by the spliced family `BAKcac`; the
`(Kn2sol)` clause is `BAKcac_spliced` clause 2. -/
theorem baKsolve : ∀ d, BAKsolve d := by
  intro d Λ κ hΛ hκ L hL W g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr
  exact ⟨BAKcac d L W g E m, baKcac_isKLoopS hr, fun t _ σ a₁ a₂ =>
    (BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.1 t σ.1 σ.2 a₁ a₂⟩

/-- **Target 5** (`baTreeRep`, the pin `BATreeRep` for `Γ = BAGamma`, `3 ≤ n`): `baKsolve` makes `BAKsol` a solution of
`IsKLoopS` (`BAKsol_isKLoopS`); `baK_unique` against `baKcac_isKLoopS` gives `BAKsol = BAKcac` on `[0,1)` for loops of length
`≥ 2`; clause 3 of `BAKcac_spliced` is the tree sum. -/
theorem baTreeRep (d : ℕ) : BATreeRep d (@BAGamma d) := by
  intro Λ κ hΛ hκ L hL W g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht n _ hn σ a
  have heq := baK_unique _ _ (BAKsol_isKLoopS (baKsolve d) hΛ hκ hL hg hgΛ hr)
    (baKcac_isKLoopS (W := W) hr) t ht (KLloopOf d L σ a) (by simp [LoopIdx.WF, KLloopOf])
    (by simp only [LoopIdx.length, KLloopOf, List.length_ofFn]; omega)
  rw [heq]
  exact (BAKcac_spliced (d := d) (L := L) (W := W) (g := g) (E := E) (m := m)).2.2 t n hn σ a

/-! ## 9. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
`0 < P.g0 ≤ 10`), `W = 2` (`W^d = 8`), `Λ = 10`, `κ = Im m₀ > 0`, `t = 1/2`, `n = 4` (`TSP 4 = {∅, {(0,2)}, {(1,3)}}`: the two
diagonals `(0,2)`, `(1,3)`, each in one tree; the cut at `J = (0,2)` has an inner and an outer triangle), the charges
`σ = (+,+,-,+)`, four distinct labels.  Every deterministic hypothesis is discharged; nothing is assumed. -/

namespace KTreeRepInst

open RBM.BA.MFixedPointInst

private theorem KTreeRep_isTSP_F02 :
    KLIsTSP ({((0 : Fin 4), (2 : Fin 4))} : Finset (Fin 4 × Fin 4)) :=
  KLisTSP_of_mem_TSP (by rw [TSP_four]; simp)

/-- **The chord-`J` term of one tree** (the new mathematics), at `F = {(0,2)}`, `J = (0,2)`: the cactus with the chord weight
`Θ·Θ` is `Σ_x Γ_{F_out}(σ_out, a_out^x) Γ_{F_in}(σ_in, a_in^x)`, both pieces triangles. -/
example := KTreeRep_cut (d := 3) (L := 4) (F := {((0 : Fin 4), (2 : Fin 4))}) (J := ((0 : Fin 4), (2 : Fin 4)))
  KTreeRep_isTSP_F02 (by norm_num) (Finset.mem_singleton_self _) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2)
  ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- **Target 2** (`baChordPairs`) at the data, with the spliced family `BAKcac` (`W = 2`): `n = 4`, the chord part over the
trees `{(0,2)}`, `{(1,3)}` is the sum over the diagonals `(0,2)`, `(1,3)` of the pair summands of `treeEqRhsS`. -/
example :=
  baChordPairs 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (BAKcac 3 4 2 P.g0 P.E P.m0) BAKcac_spliced 4 (by norm_num)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] (1 / 2) (by norm_num) (by norm_num)

/-- **Target 3** (`baKcac_isKLoopS`) at the data: the spliced family solves `IsKLoopS` on `[0,1)`. -/
example : IsKLoopS 3 4 2 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
    (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) (BAKcac 3 4 2 P.g0 P.E P.m0) :=
  baKcac_isKLoopS P.real

/-- **Target 4** (`baKsolve`) at the data (`Λ = 10`, `κ = Im m₀`, `W = 2`). -/
example := baKsolve 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real

/-- **Target 5** (`baTreeRep`) at the data, `t = 1/2`, `n = 4`: the solution `BAKsol` of the `K`-loop equation at the loop
`((+,+,-,+), (a₀, …, a₃))` is `W^{-3d} Σ_{F ∈ TSP 4} Γ_M(F)`, three trees. -/
example :=
  baTreeRep 3 10 P.m0.im (by norm_num) P.real.1.1 4 (by norm_num) 2 P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    ⟨by norm_num, by norm_num⟩ 4 (by norm_num) ![true, true, false, true]
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

end KTreeRepInst

end RBM.BA
