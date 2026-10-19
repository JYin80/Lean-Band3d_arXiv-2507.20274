/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.GLoop
import RBM3D.Loop.TreeRep
import RBM3D.Gauss.FineModel

/-!
# Flow data, resolvents and `G`-loops along the flow

Paper: arXiv:2507.20274, Section 2 (`(eq:zt)`, `Def:G_loop`, `Def:oper_loop`).

* The flow data `ztOf`, `etaOf` (`z_t`, `η_t`, `(eq:zt)`, `(eta)`); the resolvents `Gres`
  (`G_t(σ)`, `Def:G_loop`) and `Mres` (`M(z)`, `(def_G0)`); the loops `loopM`, `loopL` on the
  block-product index and `loopFine` on the fine lattice, with the bridge `blockMat`; along a size
  sequence `Gt`, `Lloop` (`𝓛^{(k)}_{t,σ,a}`, `(Eq:defGLoop)`), `Gn` (`G(z)`); `Gt_lemT`
  (`(eq:zztE)`, third clause, pointwise); and the check `Lloop_zero_one`
  (`𝓛^{(1)}_{0,σ,a} = m(σ)`).  The Hermitian property of the flow matrix `seqHflow` is restated
  as `gLoopFlow_seqHflow_isHermitian`.  The block Anderson items (`Gt_BA` and its data) are in
  `RBM3D/Gauss/BlockAnderson.lean`, which imports this file.
* The single-edge cut-and-glue `cutGlue` and the matrix words of the two-edge cuts
  `gloop_cutGlueL_split`, `gloop_cutGlueR_split` (with `gloopProd`, which occurs in their
  statements).
* The deterministic envelope of a `G`-loop for an arbitrary Hermitian matrix `H` and
  `η ≤ |Im z|`: `norm_loopM_le` (`|𝓛^{(n)}| ≤ (η⁻¹)^n`), `norm_Lloop_le` (along the flow), and
  the sharp constant `norm_gloop_le_sharp` (`W^d (η⁻¹ W^{-d})^n`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss

/-! ## 6. Flow data: `z_t`, `η_t`, `G_t(σ)`, the `G`-loops -/

section FlowData

/-- `z_t = E + (1-t) m` (`(eq:zt)`) with the value `m = m(E, λ)` as data: for the
random band matrix `m = mE E` (the function `zt`); for the block Anderson model
`m(E, λ₀)` solves `(self_m)` and is supplied by a separate deterministic layer. -/
def ztOf (m : ℂ) (E t : ℝ) : ℂ := E + (1 - t) * m

/-- `η_t = (1-t) Im m` (`(eta)`). -/
def etaOf (m : ℂ) (t : ℝ) : ℝ := (1 - t) * m.im

theorem ztOf_im (m : ℂ) (E t : ℝ) : (ztOf m E t).im = etaOf m t := by
  simp [ztOf, etaOf]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`G_t(σ)`** of `Def:G_loop` for a flow matrix `H` and a flow value `z = z_t`:
`G(+) = (H - z)⁻¹`, `G(-) = (H - z̄)⁻¹ = G(+)^*`.  It is generic in the index type, so it serves
the fine lattice (entries, `(G_bound)`) and the block-product index (loops). -/
def Gres (H : Matrix ι ι ℂ) (z : ℂ) (σ : Bool) : Matrix ι ι ℂ :=
  Ring.inverse (H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ))

/-- **`M(z) = (H_0 - z - m(z))⁻¹`** (`(def_G0)`) for a deterministic initial matrix `H_0`
and the value `m = m(z)`: `H_0 = 0` for the random band matrix, where `M = m I`
(`(eq:defMzsc)`); `H_0 = λ Ψ` for the block Anderson model, where `m` solves
`(self_m)` and `M ≠ m I`. -/
def Mres (H0 : Matrix ι ι ℂ) (z m : ℂ) : Matrix ι ι ℂ :=
  Ring.inverse (H0 - (z + m) • (1 : Matrix ι ι ℂ))

variable (d L W : ℕ) [NeZero L]

/-- **`𝓛^{(n)}_{t,σ,a}`** of `(Eq:defGLoop)` for a matrix `H` on the block-product
index and a flow value `z`: `tr (∏_i G(σ_i) E_{a_i})`, with `Eblk`. -/
def loopM (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) {n : ℕ} (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  Matrix.trace (List.ofFn fun i : Fin n => Gres H z (σ i) * Eblk d L W (a i)).prod

variable [NeZero W]

/-- The matrix of the fine lattice read on the block-product index: the bridge between the
statements (entries on `Z_{WL}^d`, `(G_bound)`) and the loops (block labels,
`(Eq:defGLoop)`). -/
def blockMat (M : Matrix (Idx d L W) (Idx d L W) ℂ) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  M.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm

/-- **`𝓛^{(k)}_{t,σ,a}` along a flow** (`(Eq:defGLoop)`): the loop of a flow matrix on
the fine lattice. -/
def loopFine (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d L) : ℂ :=
  loopM d L W (blockMat d L W H) z σ a

/-- A loop index `(σ, a)` of length `k` as the list-based index `LoopIdx`
(on which the cut-and-glue operators `cutGlueL`, `cutGlueR` of `Def:oper_loop` act). -/
def loopOf {α : Type*} {k : ℕ} (σ : Fin k → Bool) (a : Fin k → α) : Loop.LoopIdx α :=
  ⟨List.ofFn σ, List.ofFn a⟩

/-- The list-based loop `𝓛_I` of a loop index `I = (σ, a)` (`(Eq:defGLoop)`), with the
matrix product `gloopProd`. -/
def loopL (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) : ℂ :=
  Matrix.trace ((I.σ.zip I.a).foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1)

omit [NeZero W] in
theorem loopM_eq_loopL (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopM d L W H z σ a = loopL d L W H z (loopOf σ a) := by
  have hfold : ∀ l : List (Bool × Zd d L),
      l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1 =
        (l.map fun p => Gres H z p.1 * Eblk d L W p.2).prod := by
    intro l
    induction l with
    | nil => simp
    | cons p l ih => simp [ih]
  have hzip : (List.ofFn σ).zip (List.ofFn a) = List.ofFn fun i => (σ i, a i) := by
    refine List.ext_getElem (by simp) fun i h1 h2 => by simp
  unfold loopM loopL loopOf
  rw [hzip, hfold, List.map_ofFn]
  rfl

end FlowData

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **`G_t(σ)`** of `Def:G_loop` along the single-time flow at size index `n` and
energy `E`: the resolvent `(H_t - z_t)⁻¹` of `H_t = seqHflow sz n t ω`, `z_t = zt E t`.  Entries are
on `Z_{WL}^d`, so `(G_bound)` and `(Gt_bound)` read `|(Gt - M)_{xy}|` literally. -/
def Gt (n : ℕ) (E t : ℝ) (σ : Bool) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (seqHflow sz n t ω) (zt E t) σ

/-- **`𝓛^{(k)}_{t,σ,a}`** of the random band matrix at size index `n`, energy `E`, time `t`:
the loop of `Gt` with the block insertions `E_a` (`Def:G_loop`). -/
def Lloop (n : ℕ) (E t : ℝ) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n))
    (ω : SeqΩ sz) : ℂ :=
  loopFine d (sz.L n) (sz.W n) (seqHflow sz n t ω) (zt E t) σ a

/-- **`G(z) = (H - z)⁻¹`** of `(def_Green)` for the size-`n` matrix `H` of the model
measure `seqP sz` (the Green function of the endpoints `MR:locSC`, `MR:QuDiff`). -/
def Gn (n : ℕ) (z : ℂ) (ω : SeqΩ sz) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  Gres (seqXmat sz n ω) z true

/-- `H_u` is Hermitian: the same statement as `seqHflow_isHermitian`, stated with the file
stem as prefix. -/
theorem gLoopFlow_seqHflow_isHermitian (n : ℕ) (u : ℝ) (ω : SeqΩ sz) :
    (seqHflow sz n u ω).IsHermitian := by
  unfold seqHflow
  rw [IsHermitian, conjTranspose_smul, show star (Real.sqrt u : ℂ) = (Real.sqrt u : ℂ) from
    Complex.conj_ofReal _, (seqXmat_isHermitian sz n ω).eq]

/-- **`zztE`, third clause, pointwise** (`(eq:zztE)`): for the single-time carrier
`H_u = √u X`, `G(z) = √t₀ G_{t₀;E}` with `t₀ = lemT z`, `E = lemE z` holds as an identity of random
matrices, hence in distribution (one time only: no coupling across times is involved). -/
theorem Gt_lemT (n : ℕ) {z : ℂ} (hz : 0 < z.im) (ω : SeqΩ sz) :
    (Real.sqrt (lemT z) : ℂ) • Gt sz n (lemE z) (lemT z) true ω = Gn sz n z ω := by
  have hr0 : (Real.sqrt (lemT z) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (lemT_pos hz)).ne'
  have hzt : zt (lemE z) (lemT z) = (Real.sqrt (lemT z) : ℂ) * z := by
    have h := eq_inv_sqrt_mul_zt hz
    calc zt (lemE z) (lemT z)
        = (Real.sqrt (lemT z) : ℂ) * ((Real.sqrt (lemT z) : ℂ)⁻¹ * zt (lemE z) (lemT z)) := by
          field_simp
      _ = (Real.sqrt (lemT z) : ℂ) * z := by rw [← h]
  have hA : IsUnit (seqXmat sz n ω - z • (1 : Matrix _ _ ℂ)) :=
    isUnit_sub_smul_of_isHermitian (seqXmat_isHermitian sz n ω) hz.ne'
  have hHt : seqHflow sz n (lemT z) ω - zt (lemE z) (lemT z) • (1 : Matrix _ _ ℂ) =
      (Real.sqrt (lemT z) : ℂ) • (seqXmat sz n ω - z • (1 : Matrix _ _ ℂ)) := by
    rw [hzt, seqHflow, smul_sub, ← mul_smul]
  unfold Gt Gn Gres
  simp only [↓reduceIte]
  rw [hHt, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
  have : Invertible (Real.sqrt (lemT z) : ℂ) := invertibleOfNonzero hr0
  rw [Matrix.inv_smul (A := seqXmat sz n ω - z • (1 : Matrix _ _ ℂ)) (Real.sqrt (lemT z) : ℂ)
    ((Matrix.isUnit_iff_isUnit_det _).mp hA), smul_smul, invOf_eq_inv,
    mul_inv_cancel₀ hr0, one_smul]

end Sizes

/-! ### Sanity of the loop value at `t = 0`: `𝓛^{(1)}_{0,σ,a} = m(σ)` -/

section LoopZero

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ring_inverse_smul_one {c : ℂ} (hc : c ≠ 0) :
    Ring.inverse (c • (1 : Matrix ι ι ℂ)) = c⁻¹ • 1 := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  refine Matrix.inv_eq_right_inv ?_
  rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, mul_one, one_smul]

theorem trace_Eblk (d L W : ℕ) [NeZero L] [NeZero W] (a : Zd d L) :
    Matrix.trace (Eblk d L W a) = 1 := by
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  simp only [Eblk, Matrix.trace_diagonal]
  rw [Fintype.sum_prod_type]
  have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), if x = a then ((W : ℂ) ^ d)⁻¹ else 0) =
      if x = a then 1 else 0 := by
    intro x
    by_cases h : x = a
    · simp [h, hW]
    · simp [h]
  simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem blockMat_zero (d L W : ℕ) [NeZero L] [NeZero W] :
    blockMat d L W (0 : Matrix (Idx d L W) (Idx d L W) ℂ) = 0 := by
  ext p q
  simp [blockMat]

end LoopZero

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **Sanity of the `𝓛^{(n)}` check at `t = 0`** (`Def_Ktza`: `K^{(1)}_{t,σ,a} = m(σ)`; at
`t = 0` `(eq:initial_K)`, `(eq:KMloop)`): `H_0 = 0`, `z_0 = E + m^{(E)}`, hence
`𝓛^{(1)}_{0,σ,a} = tr (G_0(σ) E_a) = m(σ)`.
It checks in one identity the `W^{-d}` normalisation of `E_a`, the sign of `z_t`, the bridge
`blockMat` and the carrier at `u = 0`. -/
theorem Lloop_zero_one (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) (σ : Bool) (a : Zd d (sz.L n))
    (ω : SeqΩ sz) : Lloop sz n E 0 (fun _ : Fin 1 => σ) (fun _ => a) ω = mSigma E σ := by
  have hm := mE_mul hE
  have hH0 : seqHflow sz n 0 ω = 0 := by simp [seqHflow]
  have hzt : zt E 0 = (E : ℂ) + mE E := by simp [zt]
  have hmz : (-((E : ℂ) + mE E))⁻¹ = mE E := by
    refine inv_eq_of_mul_eq_one_right ?_
    linear_combination (-1 : ℂ) * hm
  have hmz' : (-(starRingEnd ℂ ((E : ℂ) + mE E)))⁻¹ = starRingEnd ℂ (mE E) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have h2 := congrArg (starRingEnd ℂ) hm
    simp only [map_mul, map_add, Complex.conj_ofReal, map_neg, map_one] at h2
    simp only [map_add, Complex.conj_ofReal]
    linear_combination (-1 : ℂ) * h2
  have hne : (E : ℂ) + mE E ≠ 0 := by
    intro h0
    rw [add_comm, h0, mul_zero] at hm
    norm_num at hm
  have hne' : starRingEnd ℂ ((E : ℂ) + mE E) ≠ 0 := (map_ne_zero _).2 hne
  unfold Lloop loopFine loopM
  rw [hH0, blockMat_zero]
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
  cases σ
  · have hG : Gres (0 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ)
        (zt E 0) false = (starRingEnd ℂ (mE E)) • 1 := by
      rw [Gres]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne'), hmz']
    rw [hG, smul_mul_assoc, one_mul, Matrix.trace_smul, trace_Eblk]
    simp [mSigma]
  · have hG : Gres (0 : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ)
        (zt E 0) true = (mE E) • 1 := by
      rw [Gres]
      simp only [↓reduceIte]
      rw [hzt, zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hne), hmz]
    rw [hG, smul_mul_assoc, one_mul, Matrix.trace_smul, trace_Eblk]
    simp [mSigma]

end Sizes

end RBM.Gauss

/-! ## Cut-and-glue on loop indices and the matrix words of the cut loops

The statements and proofs follow the two-dimensional formalization, with `Zd d L` for the
block lattice, `Vtx d L W` for the block-product index, `Gres` for the resolvent and the
list-based `loopL` for the loop. -/

namespace RBM.Loop.LoopIdx

variable {α : Type*}

/-- The paper's single-edge cut-and-glue operation `G_k^(b)` (`Def:oper_loop`), with
one-based edge position `k`: cutting the `k`-th Green edge inserts one block observable `E_b` and
duplicates that edge's sign.  The module `RBM3D/Loop/TreeRep.lean` has only the two-edge
operators `cutGlueL`, `cutGlueR`. -/
def cutGlue (k : ℕ) (b : α) (I : LoopIdx α) : LoopIdx α where
  σ := I.σ.take k ++ I.σ.drop (k - 1)
  a := I.a.take (k - 1) ++ b :: I.a.drop (k - 1)

/-- Index list of the chain containing the final label after a two-edge cut; support of
`gloop_cutGlueL_split`. -/
private theorem cutGlueL_split (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List α)
    (s t : Bool) (a c b : α) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    cutGlueL (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b
      (⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
        a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx α) =
      ⟨σ₁ ++ [s, t] ++ σ₃, a₁ ++ [b, c] ++ a₃⟩ := by
  have htakeσ : (σ₁ ++ s :: σ₂ ++ t :: σ₃).take (σ₁.length + 1) = σ₁ ++ [s] := by
    simp [List.take_append]
  have htakea : (a₁ ++ a :: a₂ ++ c :: a₃).take σ₁.length = a₁ := by
    rw [h₁]
    simp
  have hdropσ : (σ₁ ++ s :: σ₂ ++ t :: σ₃).drop
      (σ₁.length + σ₂.length + 1) = t :: σ₃ := by
    calc
      _ = ((σ₁ ++ s :: σ₂) ++ t :: σ₃).drop (σ₁ ++ s :: σ₂).length := by
        congr 1; simp [List.length_append, Nat.add_assoc]
      _ = t :: σ₃ := List.drop_append_length
  have hdropa : (a₁ ++ a :: a₂ ++ c :: a₃).drop
      (σ₁.length + σ₂.length + 1) = c :: a₃ := by
    calc
      _ = ((a₁ ++ a :: a₂) ++ c :: a₃).drop (a₁ ++ a :: a₂).length := by
        congr 1; simp [h₁, h₂, List.length_append, Nat.add_assoc]
      _ = c :: a₃ := List.drop_append_length
  apply LoopIdx.ext
  · change (σ₁ ++ s :: σ₂ ++ t :: σ₃).take (σ₁.length + 1) ++
        (σ₁ ++ s :: σ₂ ++ t :: σ₃).drop (σ₁.length + σ₂.length + 1) = _
    rw [htakeσ, hdropσ]
    simp
  · change (a₁ ++ a :: a₂ ++ c :: a₃).take σ₁.length ++ b ::
        (a₁ ++ a :: a₂ ++ c :: a₃).drop (σ₁.length + σ₂.length + 1) = _
    rw [htakea, hdropa]
    simp

/-- Index list of the intervening chain after a two-edge cut; support of
`gloop_cutGlueR_split`. -/
private theorem cutGlueR_split (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List α)
    (s t : Bool) (a c b : α) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    cutGlueR (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b
      (⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
        a₁ ++ a :: a₂ ++ c :: a₃⟩ : LoopIdx α) =
      ⟨s :: σ₂ ++ [t], a :: a₂ ++ [b]⟩ := by
  simp [cutGlueR, h₁, h₂, List.take_append,
    show a₁.length + a₂.length + 1 - a₁.length = a₂.length + 1 by omega]

end RBM.Loop.LoopIdx

namespace RBM.Gauss

section Loop

variable (d L W : ℕ) [NeZero L]

/-- The matrix product `∏ᵢ G(σᵢ) E_{aᵢ}` of `Def:G_loop` for a list-based loop index;
`loopL` is its trace.  The lists need equal lengths to represent an `n`-loop (`LoopIdx.WF`);
`zip` truncates malformed pairs.  It occurs in the statements of the two cut-and-glue words
below, so it is public. -/
def gloopProd (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  (I.σ.zip I.a).foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

variable {d L W} {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

/-- The matrix product of the empty loop index is the identity. -/
private theorem gloopProd_nil : gloopProd d L W H z ⟨[], []⟩ = 1 := rfl

/-- The matrix product of a loop index with a first edge `(s, b)` is `G(s) E_b` times the product
of the remaining edges. -/
private theorem gloopProd_cons (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) :
    gloopProd d L W H z ⟨s :: σ, b :: a⟩ =
      Gres H z s * Eblk d L W b * gloopProd d L W H z ⟨σ, a⟩ := rfl

/-- A concatenation of two well-formed index lists gives the product of their matrix words. -/
private theorem gloopProd_append {σ₁ : List Bool} {a₁ : List (Zd d L)}
    (h₁ : σ₁.length = a₁.length)
    (σ₂ : List Bool) (a₂ : List (Zd d L)) :
    gloopProd d L W H z ⟨σ₁ ++ σ₂, a₁ ++ a₂⟩ =
      gloopProd d L W H z ⟨σ₁, a₁⟩ * gloopProd d L W H z ⟨σ₂, a₂⟩ := by
  induction σ₁ generalizing a₁ with
  | nil =>
    obtain rfl : a₁ = [] := List.eq_nil_of_length_eq_zero h₁.symm
    simp [gloopProd]
  | cons s σ ih =>
    obtain ⟨b, a, rfl⟩ : ∃ b a, a₁ = b :: a := by
      cases a₁ with
      | nil => simp at h₁
      | cons b a => exact ⟨b, a, rfl⟩
    have h : σ.length = a.length := by simpa using h₁
    simp only [List.cons_append, gloopProd_cons, ih h, Matrix.mul_assoc]

end Loop

section PairWords

variable (d L W : ℕ) [NeZero L]
variable (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)

/-- Matrix word for the left chain after a two-edge cut: the original middle segment disappears,
the inserted block `b` joins edges `s` and `t`. -/
private theorem gloopProd_cutGlueL_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloopProd d L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      gloopProd d L W H z ⟨σ₁, a₁⟩ *
        (Gres H z s * Eblk d L W b *
          (Gres H z t * Eblk d L W c * gloopProd d L W H z ⟨σ₃, a₃⟩)) := by
  rw [Loop.LoopIdx.cutGlueL_split σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  simp only [List.append_assoc]
  rw [gloopProd_append h₁]
  rfl

/-- Matrix word for the right chain after a two-edge cut. -/
private theorem gloopProd_cutGlueR_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    gloopProd d L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Gres H z s * Eblk d L W a *
        (gloopProd d L W H z ⟨σ₂, a₂⟩ * (Gres H z t * Eblk d L W b)) := by
  rw [Loop.LoopIdx.cutGlueR_split σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]
  change Gres H z s * Eblk d L W a *
      gloopProd d L W H z ⟨σ₂ ++ [t], a₂ ++ [b]⟩ = _
  rw [gloopProd_append h₂]
  simp [gloopProd]

/-- The left cut-and-glue loop (`Def:oper_loop`, two edges `k < l`) is the trace of its
explicit matrix word.  The statement is about the list-based loop `loopL`. -/
theorem gloop_cutGlueL_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    loopL d L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueL
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Matrix.trace (gloopProd d L W H z ⟨σ₁, a₁⟩ *
        (Gres H z s * Eblk d L W b *
          (Gres H z t * Eblk d L W c * gloopProd d L W H z ⟨σ₃, a₃⟩))) := by
  change Matrix.trace (gloopProd d L W H z _) = _
  rw [gloopProd_cutGlueL_split d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]

/-- The right cut-and-glue loop (`Def:oper_loop`, two edges `k < l`) is the trace of its
explicit matrix word. -/
theorem gloop_cutGlueR_split
    (σ₁ σ₂ σ₃ : List Bool) (a₁ a₂ a₃ : List (Zd d L))
    (s t : Bool) (a c b : Zd d L) (h₁ : σ₁.length = a₁.length)
    (h₂ : σ₂.length = a₂.length) :
    loopL d L W H z
      ((⟨σ₁ ++ s :: σ₂ ++ t :: σ₃,
          a₁ ++ a :: a₂ ++ c :: a₃⟩ : Loop.LoopIdx (Zd d L)).cutGlueR
        (σ₁.length + 1) (σ₁.length + σ₂.length + 2) b) =
      Matrix.trace (Gres H z s * Eblk d L W a *
        (gloopProd d L W H z ⟨σ₂, a₂⟩ * (Gres H z t * Eblk d L W b))) := by
  change Matrix.trace (gloopProd d L W H z _) = _
  rw [gloopProd_cutGlueR_split d L W H z σ₁ σ₂ σ₃ a₁ a₂ a₃ s t a c b h₁ h₂]

end PairWords

end RBM.Gauss

namespace RBM.Gauss

/-! ## The deterministic envelope of a `G`-loop, for an arbitrary Hermitian matrix

`|𝓛^{(n)}| ≤ (η⁻¹)^n` pointwise, with no exceptional set, for `H` Hermitian and `η ≤ |Im z|`.
It is the entrywise argument: the entries of `G` are `≤ η⁻¹` (`norm_inverse_entry_le`), and
summing over a block of `W^d` sites against the weight `W^{-d}` of `E_a` is an average.  The
bound serves the flow matrices of this file (`norm_Lloop_le`) and the block Anderson matrix.  The
statement needs `n ≥ 1` (`tr I = N`).  The bound follows from `‖G_t‖ ≤ η_t⁻¹` (used in the
proof of Lemma 7.22 (`lem:Anp`)) and the block structure of `E_a`. -/

/-- The entries of `G(σ) = (H - z)⁻¹` and of `G(σ)^* = (H - z̄)⁻¹` are bounded by `η⁻¹` on the
whole space, for `H` Hermitian and `η ≤ |Im z|`. -/
private theorem norm_Gres_entry_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (σ : Bool) (x y : ι) :
    ‖Gres H z σ x y‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  have hinv : |z.im|⁻¹ ≤ η⁻¹ := inv_anti₀ hη hz
  unfold Gres
  cases σ with
  | true =>
    simp only [↓reduceIte]
    exact (norm_inverse_entry_le hH hzim x y).trans hinv
  | false =>
    have hzc : (starRingEnd ℂ z).im ≠ 0 := by simpa using hzim
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine (norm_inverse_entry_le hH hzc x y).trans ?_
    simpa [abs_neg] using hinv

section EnvelopeLoop

variable (d L W : ℕ) [NeZero L]

private theorem Gres_mul_Eblk_apply (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (σ : Bool)
    (a : Zd d L) (x y : Vtx d L W) :
    (Gres H z σ * Eblk d L W a) x y
      = Gres H z σ x y * (if y.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single y (fun b _ hb => by simp [Eblk_apply, hb])
    (fun h => absurd (Finset.mem_univ y) h)]
  simp [Eblk_apply]

/-- **The invariant.**  A product of factors `G_i E_{a_i}`, with the last one indexed by `a`, has
entries at most `W^{-d} η^{-k}` and is supported in the block `[a]`:
`|(Π_{i<k} G_i E_{a_i})_{xy}| ≤ W^{-d} η^{-k} · 1(y ∈ [a])`.  Each step sums over a block of `W^d`
sites and carries `W^{-d}`, so it is an average. -/
private theorem norm_loopM_prod_entry_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|)
    (b : Bool) (a : Zd d L) :
    ∀ (l : List (Bool × Zd d L)) (x y : Vtx d L W),
      ‖((l.map fun p => Gres H z p.1 * Eblk d L W p.2)
          ++ [Gres H z b * Eblk d L W a]).prod x y‖
        ≤ (((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (l.length + 1)) * (if y.1 = a then 1 else 0) := by
  have hWpos : (0 : ℝ) < (W : ℝ) ^ d ∨ (W : ℝ) ^ d = 0 := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (W : ℝ) ^ d) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  intro l
  induction l with
  | nil =>
    intro x y
    simp only [List.map_nil, List.nil_append, List.prod_singleton, List.length_nil,
      Gres_mul_Eblk_apply, norm_mul]
    by_cases hy : y.1 = a
    · have h1 := norm_Gres_entry_le hH hη hz b x y
      have hWn : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
      simp only [hy, ite_true, mul_one, norm_inv, hWn, zero_add, pow_one]
      calc ‖Gres H z b x y‖ * ((W : ℝ) ^ d)⁻¹
          ≤ η⁻¹ * ((W : ℝ) ^ d)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ((W : ℝ) ^ d)⁻¹ * η⁻¹ := by ring
    · simp [hy]
  | cons p tl ih =>
    intro x y
    have hstep : ((((p :: tl).map fun q => Gres H z q.1 * Eblk d L W q.2)
        ++ [Gres H z b * Eblk d L W a]).prod) x y
        = ∑ w : Vtx d L W,
            (Gres H z p.1 * Eblk d L W p.2) x w
            * (((tl.map fun q => Gres H z q.1 * Eblk d L W q.2)
                ++ [Gres H z b * Eblk d L W a]).prod) w y := by
      simp only [List.map_cons, List.cons_append, List.prod_cons]
      rw [Matrix.mul_apply]
    rw [hstep]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ w : Vtx d L W,
        ‖(Gres H z p.1 * Eblk d L W p.2) x w
          * (((tl.map fun q => Gres H z q.1 * Eblk d L W q.2)
              ++ [Gres H z b * Eblk d L W a]).prod) w y‖
          ≤ (η⁻¹ * ((W : ℝ) ^ d)⁻¹ * (if w.1 = p.2 then 1 else 0))
            * ((((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (tl.length + 1))
              * (if y.1 = a then 1 else 0)) := by
      intro w
      rw [norm_mul]
      refine mul_le_mul ?_ (ih w y) (norm_nonneg _) (by positivity)
      rw [Gres_mul_Eblk_apply, norm_mul]
      by_cases hw : w.1 = p.2
      · have h1 := norm_Gres_entry_le hH hη hz p.1 x w
        have hWn : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
        simp only [hw, ite_true, mul_one, norm_inv, hWn]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      · simp [hw]
    refine le_trans (Finset.sum_le_sum fun w _ => hterm w) ?_
    have hcount : ∑ w : Vtx d L W, (if w.1 = p.2 then (1 : ℝ) else 0) = (W : ℝ) ^ d := by
      rw [Fintype.sum_prod_type]
      simp [apply_ite Finset.card, Finset.sum_ite_eq', Fintype.card_fin]
    have hrw : ∀ w : Vtx d L W,
        (η⁻¹ * ((W : ℝ) ^ d)⁻¹ * (if w.1 = p.2 then 1 else 0))
          * ((((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (tl.length + 1))
            * (if y.1 = a then 1 else 0))
        = (η⁻¹ * ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (tl.length + 1))
            * (if y.1 = a then 1 else 0)) * (if w.1 = p.2 then 1 else 0) := by
      intro w; ring
    simp only [hrw]
    rw [← Finset.mul_sum, hcount]
    have hfinal : η⁻¹ * ((W : ℝ) ^ d)⁻¹
          * (((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (tl.length + 1))
          * (if y.1 = a then 1 else 0) * (W : ℝ) ^ d
        = ((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ ((p :: tl).length + 1)
          * (if y.1 = a then 1 else 0) := by
      rcases hWpos with hW | hW
      · have hη' : η ≠ 0 := ne_of_gt hη
        have hWne : ((W : ℝ) ^ d) ≠ 0 := ne_of_gt hW
        rw [List.length_cons]
        have hpow : η⁻¹ ^ (tl.length + 1 + 1) = η⁻¹ * η⁻¹ ^ (tl.length + 1) := by
          rw [pow_succ']
        rw [hpow]
        field_simp
      · rw [hW]
        simp
    rw [hfinal]

/-- **The deterministic envelope of a `G`-loop, for an arbitrary Hermitian `H`**:
`|𝓛^{(n)}| ≤ (η⁻¹)^n` for `n ≥ 1` factors, `η ≤ |Im z|`, pointwise with no exceptional set.  The
loop is the matrix of `loopM`, so it covers the flow matrices (`norm_Lloop_le`) and the
block Anderson matrix alike. -/
theorem norm_loopM_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {n : ℕ}
    (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Zd d L) :
    ‖loopM d L W H z σ a‖ ≤ η⁻¹ ^ (n + 1) := by
  -- split off the last factor
  set l : List (Bool × Zd d L) :=
    List.ofFn fun i : Fin n => (σ i.castSucc, a i.castSucc) with hl
  have hsplit : (List.ofFn fun i : Fin (n + 1) => (σ i, a i))
      = l ++ [(σ (Fin.last n), a (Fin.last n))] := by
    rw [hl, List.ofFn_succ' (fun i : Fin (n + 1) => (σ i, a i)), List.concat_eq_append]
  have hmap : (List.ofFn fun i : Fin (n + 1) => Gres H z (σ i) * Eblk d L W (a i))
      = (l.map fun p => Gres H z p.1 * Eblk d L W p.2)
        ++ [Gres H z (σ (Fin.last n)) * Eblk d L W (a (Fin.last n))] := by
    rw [show (List.ofFn fun i : Fin (n + 1) => Gres H z (σ i) * Eblk d L W (a i))
        = ((List.ofFn fun i : Fin (n + 1) => (σ i, a i)).map
          fun p => Gres H z p.1 * Eblk d L W p.2) from by
      rw [List.map_ofFn]; rfl]
    rw [hsplit, List.map_append, List.map_singleton]
  have hlen : l.length = n := by rw [hl, List.length_ofFn]
  rw [loopM, hmap, Matrix.trace]
  refine le_trans (norm_sum_le _ _) ?_
  have hbd : ∀ x : Vtx d L W,
      ‖((l.map fun p => Gres H z p.1 * Eblk d L W p.2)
        ++ [Gres H z (σ (Fin.last n)) * Eblk d L W (a (Fin.last n))]).prod x x‖
        ≤ (((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (n + 1))
          * (if x.1 = a (Fin.last n) then 1 else 0) := by
    intro x
    have := norm_loopM_prod_entry_le d L W hH hη hz (σ (Fin.last n)) (a (Fin.last n)) l x x
    rwa [hlen] at this
  refine le_trans (Finset.sum_le_sum fun x _ => hbd x) ?_
  rw [← Finset.mul_sum]
  have hcount : ∑ x : Vtx d L W, (if x.1 = a (Fin.last n) then (1 : ℝ) else 0)
      = (W : ℝ) ^ d := by
    rw [Fintype.sum_prod_type]
    simp [apply_ite Finset.card, Finset.sum_ite_eq', Fintype.card_fin]
  rw [hcount]
  have hWdich : (0 : ℝ) < (W : ℝ) ^ d ∨ (W : ℝ) ^ d = 0 := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (W : ℝ) ^ d) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hWdich with hW | hW
  · have : ((W : ℝ) ^ d)⁻¹ * η⁻¹ ^ (n + 1) * (W : ℝ) ^ d = η⁻¹ ^ (n + 1) := by
      field_simp
    rw [this]
  · rw [hW]
    simp only [_root_.inv_zero, inv_pow, zero_mul, mul_zero, inv_nonneg, ge_iff_le]
    positivity

end EnvelopeLoop

namespace Sizes

variable {d : ℕ} (sz : Sizes d)

/-- **The envelope along the flow**: `|𝓛^{(k)}_{t,σ,a}| ≤ (η_t⁻¹)^k` for the fine-lattice loop
of the single-time flow `H_t = seqHflow sz n t ω`, `|E| < 2`, `t < 1`, `k ≥ 1` factors, pointwise in
`ω`.  The matrix `blockMat H_t` is Hermitian and `|Im z_t| = η_t > 0` (`etaT_pos`), so this is
`norm_loopM_le`. -/
theorem norm_Lloop_le (n : ℕ) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {k : ℕ}
    (σ : Fin (k + 1) → Bool) (a : Fin (k + 1) → Zd d (sz.L n)) (ω : SeqΩ sz) :
    ‖sz.Lloop n E t σ a ω‖ ≤ (etaT E t)⁻¹ ^ (k + 1) := by
  have hpos : 0 < etaT E t := etaT_pos hE ht
  have hH : (blockMat d (sz.L n) (sz.W n) (seqHflow sz n t ω)).IsHermitian :=
    (seqHflow_isHermitian sz n t ω).submatrix _
  exact norm_loopM_le d (sz.L n) (sz.W n) hH hpos (by rw [← etaT_eq_zt_im, abs_of_pos hpos]) σ a

end Sizes

/-! ## The sharp envelope of a nonempty `G`-loop

`|𝓛^{(n)}| ≤ (η⁻¹)^n (W^{-d})^{n-1} = W^d (η⁻¹ W^{-d})^n`: with the last block insertion kept
inside the trace, `|tr (Y E_b)| ≤ ‖Y‖` (the `W^d` sites of a block cancel its weight `W^{-d}`),
and `‖Y‖ ≤ (η⁻¹)^n (W^{-d})^{n-1}` from `‖G‖ ≤ η⁻¹` and `‖E_a‖ ≤ W^{-d}`.  It implies the `η^{-n}`
bound of the entrywise envelope when `W ≥ 1`, and has the volume factor `W^{-d(n-1)}` that the
entrywise argument does not see. -/

section EnvelopeSharp

open scoped Matrix.Norms.L2Operator

/-- A matrix entry is bounded by the `ℓ² → ℓ²` operator norm. -/
private theorem norm_matrix_entry_le_opNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (p q : ι) : ‖M p q‖ ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single q 1)
  rw [PiLp.norm_single, norm_one, mul_one] at h
  refine le_trans ?_ h
  refine le_of_eq_of_le ?_ (PiLp.norm_apply_le _ p)
  simp

/-- `‖(H - z)⁻¹‖ ≤ η⁻¹` in the `ℓ²` operator norm, on the whole space, for `H` Hermitian and
`η ≤ |Im z|`; the proof uses the vector estimate `norm_sub_smul_ge_of_isHermitian` and
`Ring.inverse`. -/
private theorem norm_resolvent_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) :
    ‖Ring.inverse (H - z • (1 : Matrix ι ι ℂ))‖ ≤ η⁻¹ := by
  have hzim : z.im ≠ 0 := fun h => absurd hz (by rw [h]; simpa using hη)
  set A : Matrix ι ι ℂ := H - z • (1 : Matrix ι ι ℂ) with hA
  have hAu : IsUnit A := isUnit_sub_smul_of_isHermitian hH hzim
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hAu
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v ↦ ?_
  set w := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A⁻¹ v with hw
  have hAw : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A w = v := by
    have hmul : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
        * Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A⁻¹ = 1 := by
      rw [← map_mul, Matrix.mul_nonsing_inv A hdet, map_one]
    calc Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A w
        = (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
            * Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A⁻¹) v := rfl
      _ = v := by rw [hmul]; rfl
  have hkey := norm_sub_smul_ge_of_isHermitian hH z w
  have hTw : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A w
      = Matrix.toEuclideanLin H w - z • w := by
    have hH' : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) H w = Matrix.toEuclideanLin H w :=
      congrArg (fun f => f w) (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin H)
    simp [hA, map_sub, map_smul, hH']
  rw [← hTw, hAw] at hkey
  have hfin : η * ‖w‖ ≤ ‖v‖ := le_trans (by nlinarith [norm_nonneg w]) hkey
  rw [inv_mul_eq_div, le_div_iff₀ hη]
  linarith [hfin]

/-- Both spectral signs have the same whole-space resolvent bound. -/
private theorem norm_Gres_le_inv_eta {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) (σ : Bool) :
    ‖Gres H z σ‖ ≤ η⁻¹ := by
  cases σ with
  | true =>
    simp only [Gres, ↓reduceIte]
    exact norm_resolvent_le hH hη hz
  | false =>
    simp only [Gres, Bool.false_eq_true, ↓reduceIte]
    exact norm_resolvent_le hH hη (by simpa using hz)

variable {d L W : ℕ} [NeZero L]

/-- Each normalized block insertion has operator norm at most `W^{-d}`. -/
private theorem norm_Eblk_le_inv_W_pow (a : Zd d L) : ‖Eblk d L W a‖ ≤ ((W : ℝ) ^ d)⁻¹ := by
  rw [Eblk, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  split_ifs with h
  · simp
  · simp

/-- Operator norm of a finite signed Green and block-insertion word. -/
private theorem norm_foldr_Gres_Eblk_le [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (l : List (Bool × Zd d L)) :
    ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M)
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)‖
      ≤ (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldr_cons, List.length_cons, pow_succ]
      calc
        ‖Gres H z p.1 * Eblk d L W p.2 *
            l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖
          ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ *
              ‖l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1‖ := by
                exact (norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ η⁻¹ * ((W : ℝ) ^ d)⁻¹ *
              (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length := by
                gcongr
                · exact norm_Gres_le_inv_eta hH hη hz p.1
                · exact norm_Eblk_le_inv_W_pow p.2
        _ = (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ l.length *
              (η⁻¹ * ((W : ℝ) ^ d)⁻¹) := by ring

/-- Trace against one normalized block insertion costs no volume factor: the `W^d` sites of a
block cancel its `W^{-d}` normalization.  The diagonal is summed directly. -/
private theorem norm_trace_mul_Eblk_le [NeZero W] (M : Matrix (Vtx d L W) (Vtx d L W) ℂ)
    (b : Zd d L) :
    ‖Matrix.trace (M * Eblk d L W b)‖ ≤ ‖M‖ := by
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne W))
  have hdiag : ∀ p : Vtx d L W, ‖(M * Eblk d L W b) p p‖
      ≤ ‖M‖ * (if p.1 = b then ((W : ℝ) ^ d)⁻¹ else 0) := by
    intro p
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single p (fun q _ hq => by simp [Eblk_apply, hq])
      (fun h => absurd (Finset.mem_univ p) h)]
    simp only [Eblk_apply, ite_true, norm_mul]
    by_cases hp : p.1 = b
    · simp only [hp, ite_true, norm_inv, norm_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_right (norm_matrix_entry_le_opNorm M p p) (by positivity)
    · simp [hp]
  have hsum : ∑ p : Vtx d L W, (if p.1 = b then ((W : ℝ) ^ d)⁻¹ else 0) = 1 := by
    rw [Fintype.sum_prod_type]
    have hx : ∀ x : Zd d L, (∑ _y : Fin (W ^ d), if x = b then ((W : ℝ) ^ d)⁻¹ else 0)
        = if x = b then 1 else 0 := by
      intro x
      by_cases h : x = b
      · simp [h, hW]
      · simp [h]
    simp only [hx, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖(M * Eblk d L W b) p p‖
      ≤ ∑ p : Vtx d L W, ‖M‖ * (if p.1 = b then ((W : ℝ) ^ d)⁻¹ else 0) :=
        Finset.sum_le_sum fun p _ => hdiag p
    _ = ‖M‖ := by rw [← Finset.mul_sum, hsum, mul_one]

variable (d L W)

/-- **A nonempty loop has the paper-scale deterministic envelope**: the final block insertion is
kept inside the trace, so no factor involving the number of blocks occurs.  For `H` Hermitian,
`η ≤ |Im z|`, a well-formed loop index with `n ≥ 1` edges:
`|𝓛_I| ≤ (η⁻¹)^n (W^{-d})^{n-1}`, which is `W^d (η⁻¹ W^{-d})^n`.  The statement is about the
list-based loop `loopL`. -/
theorem norm_gloop_le_sharp [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η)
    (hz : η ≤ |z.im|) (I : Loop.LoopIdx (Zd d L)) (hwf : I.WF)
    (hn : 1 ≤ I.a.length) :
    ‖loopL d L W H z I‖ ≤
      η⁻¹ ^ I.a.length * (((W : ℝ) ^ d)⁻¹) ^ (I.a.length - 1) := by
  obtain ⟨σ, a⟩ := I
  rcases List.eq_nil_or_concat' a with rfl | ⟨a', b, rfl⟩
  · simp at hn
  rcases List.eq_nil_or_concat' σ with rfl | ⟨σ', s, rfl⟩
  · simp [Loop.LoopIdx.WF] at hwf
  have hpre : σ'.length = a'.length := by simpa [Loop.LoopIdx.WF] using hwf
  have hfactor :
      loopL d L W H z ⟨σ' ++ [s], a' ++ [b]⟩ =
        Matrix.trace ((gloopProd d L W H z ⟨σ', a'⟩ * Gres H z s) * Eblk d L W b) := by
    change Matrix.trace (gloopProd d L W H z _) = _
    rw [gloopProd_append hpre [s] [b]]
    simp only [gloopProd_cons, gloopProd_nil, mul_one]
    rw [mul_assoc]
  rw [hfactor]
  have hword := norm_foldr_Gres_Eblk_le hH hη hz (σ'.zip a')
  have hG := norm_Gres_le_inv_eta hH hη hz s
  have hlen : (σ'.zip a').length = a'.length := by simp [hpre]
  rw [hlen] at hword
  calc
    ‖Matrix.trace ((gloopProd d L W H z ⟨σ', a'⟩ * Gres H z s) * Eblk d L W b)‖
        ≤ ‖gloopProd d L W H z ⟨σ', a'⟩ * Gres H z s‖ :=
          norm_trace_mul_Eblk_le _ b
    _ ≤ ‖gloopProd d L W H z ⟨σ', a'⟩‖ * ‖Gres H z s‖ := norm_mul_le _ _
    _ ≤ (η⁻¹ * ((W : ℝ) ^ d)⁻¹) ^ a'.length * η⁻¹ := by
          exact mul_le_mul hword hG (norm_nonneg _) (pow_nonneg (by positivity) _)
    _ = η⁻¹ ^ (a' ++ [b]).length * (((W : ℝ) ^ d)⁻¹) ^
          ((a' ++ [b]).length - 1) := by
          simp [pow_succ, mul_pow]
          ring

/-- The sharp envelope for the `Fin`-indexed loop: `|𝓛^{(n+1)}| ≤ (η⁻¹)^{n+1} (W^{-d})^n`. -/
theorem norm_loopM_le_sharp [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) {z : ℂ} {η : ℝ} (hη : 0 < η) (hz : η ≤ |z.im|) {n : ℕ}
    (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Zd d L) :
    ‖loopM d L W H z σ a‖ ≤ η⁻¹ ^ (n + 1) * (((W : ℝ) ^ d)⁻¹) ^ n := by
  rw [loopM_eq_loopL d L W H z σ a]
  have h := norm_gloop_le_sharp d L W hH hη hz (loopOf σ a)
    (by simp [Loop.LoopIdx.WF, loopOf]) (by simp [loopOf])
  simpa [loopOf] using h

end EnvelopeSharp

end RBM.Gauss
