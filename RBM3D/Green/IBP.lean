/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.IBPPoly
import RBM3D.Green.FlucVanish
import RBM3D.Green.LDE

/-!
# The Gaussian integration-by-parts display, as an identity, `d ≥ 3` (S1-23)

Ticket T2091.  Port of `RBM2D/Green/IBP.lean` at RBM2D commit `c9a24cf` (1653 lines: lines 1-1346
are the declarations, 1348-1653 the private `Checks` section and `#print axioms`), itself a port of
RBM1D `Gauss/IBP.lean` at `c06b103`, to the `d`-dimensional sequence model of
`RBM3D/Gauss/FineModel.lean`, with the renaming rules R1-R4 of `docs/tickets/ST1-COMMON.md`
(item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L`/`Idx L W` become `Zd d L`/`Idx d L W`,
`Coord`, `svar`, `gvar` become `CoordF`, `svarF d L W g`, `gvarF d L W g` (`g = sz.lam n` along the
sequence), `spectralM`, `spectralZ` become the merged `mE`, `zt`.  The paper (arXiv:2507.20274) does
not state this file as a lemma: `paper/tex/3_5_Loop_Hierarchy.tex:37` says that the estimates of
`lem_GbEXP` (among them `(GavLGEX)`, `3_5:33`) have been proven as Lemma 4.1 of `[YY_25]` and that
their proofs are dimension-independent (resolvent identities and large deviation estimates).  The
display behind `(GavLGEX)` is

  `E_i(G_ii - m) = E_i[m(-H - tm)G]_ii = t m Σ_k S_ik E_i[G_ii (G_kk - m)]`,

an **identity** (no `≺`, no error term); the remainder `ibpRem` is what separates it from the form
`t m² Σ_k S_ik (G_kk - m) + O≺(Ψ²)` that the fluctuation averaging asks for.

## The four steps

1. **Algebra.**  `G - m = m(-H - tm)G` (`green_sub_smul_one_eq`, private), from `m(t m + z_t) = -1`
   (`mE_mul_add_zt`, `Green/EntryDom.lean`).
2. **Gaussian integration by parts.**  The coordinate derivative of the resolvent along `Hflow`
   (`hasDerivAt_*`), the tameness of the entries (`tame_*`, from the envelope `‖G‖ ≤ η_t⁻¹`,
   `norm_green_apply_le_etaT`), Stein's identity for one resolvent entry (`integral_coord_mul_*`),
   the collapse of the coordinate sum to a row of the variance profile
   (`sum_gvar_Bmat_sandwich_diag`), and the same inside `E_k` (`condRow_*`,
   `condRow_Hflow_mul_green_diag`).
3. **The display** `condExpDiag_eq_sum_Sblk`.
4. **The remainder** `ibpRem`, `ibpRem_eq_add`.

## Reuse and differences from RBM2D

* Merged, not copied: `Tame`, `GaussIBP`, `polyW` (`Green/LDEQuad.lean`), `gaussIBP`
  (`Green/IBPPoly.lean`), `condRow`, `rowSplit`, `IsRowCoord`, `Bmat`, `crd`, `hermCLM`, `resH`,
  `hasFDerivAt_resH`, `finDep_of_Hflow`, `continuous_green_comp`, `greenDiagCentered`
  (`Green/FlucVanish.lean`), `condExpDiag`, `norm_green_apply_le_etaT` (`Green/LDE.lean`),
  `mE_mul_add_zt`, `sub_mul_green_of_im` (`Green/EntryDom.lean`), `usedCoords`
  (`Hierarchy/ContractionBasic.lean`), `svarF`, `gvarF` (`Gauss/FineModel.lean`).
* **The variance profile** is `svarF d L W g`, diagonal `W^{-d}(1 + 2 d g²)⁻¹`, support
  `(2d + 1) W^d` fine sites (D129-D130); `gvarF` is `svarF` on the diagonal and `svarF / 2` off it,
  so `IBP_gvarF_eq` is `rfl`.  The file uses the profile only through its symmetry
  (`svarF_comm`), the definition of `gvarF`, and the row sum `IBP_sum_svarF_row`
  (`Σ_k svarF i k = 1`, `3 ≤ L`), whose proof is new (RBM2D: `Spaper`, `sum_Spaper_row`; here the
  `W^d` fibre of `split` and `sum_sbKernelR`).  The uniform weights of
  RBM2D (`UniformWeight`, DECISIONS §30) do not occur in this file.
* **`hG : GaussIBP d` is discharged** (ticket T2091: "discharge it with `gaussIBP sz` unless a later
  pin keeps it"; no merged file or pin mentions these statements).  Ten RBM2D statements take it as
  a hypothesis (`integral_coord_mul_green_apply`, `integral_coord_mul_Bmat_mul_green_diag`,
  `condRow_coord_mul`, `condRow_finsetSum`, `condRow_tame_add`, `condRow_tame_sub`,
  `condRow_coord_mul_Bmat_mul_green_diag`, `condRow_Hflow_mul_green_diag`,
  `condExpDiag_eq_sum_Sblk`, `ibpRem_eq_add`); here they do not, and every proof uses the theorem
  `gaussIBP sz` (`Green/IBPPoly.lean`).  A statement without the hypothesis is stronger, and the
  owed premise `RBM.Green.GaussIBP` of the registry loses these ten dependents.
* `RBM.Ind.norm_apply_le_l2_opNorm` of RBM2D is `norm_matrix_entry_le_opNorm`
  (`Gauss/FlowCalculus.lean`); `usedCoords` is the merged one, so the identification with the
  explicit `filter` in `IBP_sum_gvar_Bmat_sandwich_diag` is by `GreenDeriv_mem_usedCoords`.
* The private `Checks` section of RBM2D is replaced by the instances at the end of this file
  (`d = 3`, `L = 3`, `W = 2`, `lam = 1/2`: `216` sites).
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Filter Matrix RBM.Gauss
open scoped Matrix.Norms.L2Operator NNReal

variable {d : ℕ}

/-! ### Step 1: the algebraic identity `G - m = m(-H - tm)G`

Everything here is deterministic. -/

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The identity `G - m = m(-H - tm)G`** (RBM1D `green_sub_smul_one_eq`, `IBP:64`; the
self-consistent equation `m = -(t m + z_t)⁻¹` is the merged `mE_mul_add_zt`, which is RBM1D's
`mE_mul_smul_add_zt`, `IBP:57`).  Taking the `ii` entry and applying `E_i` is the first step of
the integration-by-parts display. -/
private theorem green_sub_smul_one_eq {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {E t : ℝ}
    (hE : |E| ≤ 2) (hz : (zt E t).im ≠ 0) :
    green H (zt E t) - mE E • (1 : Matrix ι ι ℂ)
      = mE E • ((-H - ((t : ℂ) * mE E) • (1 : Matrix ι ι ℂ))
          * green H (zt E t)) := by
  have hGH : (H - (zt E t) • (1 : Matrix ι ι ℂ)) * green H (zt E t) = 1 :=
    sub_mul_green_of_im hH hz
  have hkey : mE E * ((t : ℂ) * mE E + zt E t) = -1 :=
    mE_mul_add_zt hE t
  have hsplit : (-H - ((t : ℂ) * mE E) • (1 : Matrix ι ι ℂ))
      = -(H - (zt E t) • (1 : Matrix ι ι ℂ))
        - (((t : ℂ) * mE E + zt E t) • (1 : Matrix ι ι ℂ)) := by
    rw [add_smul]
    abel
  rw [hsplit, sub_mul, neg_mul, hGH, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_neg,
    smul_smul, hkey, neg_smul, one_smul]
  abel

end Algebra

/-! ### Step 2a: moving one Gaussian coordinate

Stein's identity replaces `ω_c` by `gvarF_c · ∂_c`, so the display needs the derivative of a
resolvent entry along a single Gaussian coordinate.  The lemmas below are pathwise: no
integration yet. -/

section Deriv

/-- **Moving the Gaussian coordinate `p` moves `H_u` along `√u · B_p`** (RBM1D
`hasDerivAt_Hflow_update`, `IBP:95`). -/
theorem hasDerivAt_Hflow_update (sz : Sizes d) (n : ℕ) (u : ℝ) (ω : Sizes.SeqΩ sz)
    {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n)) :
    HasDerivAt (fun t : ℝ => Sizes.seqHflow sz n u (Function.update ω (crd sz n p) t))
      (Real.sqrt u • Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2) (ω (crd sz n p)) := by
  set c := crd sz n p with hc
  set B := Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 with hB
  have hline : ∀ t : ℝ, Sizes.seqHflow sz n u (Function.update ω c t)
      = Sizes.seqHflow sz n u ω + (Real.sqrt u * (t - ω c)) • B := by
    intro t
    rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqHflow_eq_realSmul,
      GreenDeriv_seqXmat_update sz n ω hp t, smul_add, smul_smul]
  have hscal : HasDerivAt (fun t : ℝ => Real.sqrt u * (t - ω c)) (Real.sqrt u) (ω c) := by
    simpa using ((hasDerivAt_id (ω c)).sub_const (ω c)).const_mul (Real.sqrt u)
  have h1 : HasDerivAt (fun t : ℝ => Sizes.seqHflow sz n u ω + (Real.sqrt u * (t - ω c)) • B)
      (Real.sqrt u • B) (ω c) := (hscal.smul_const B).const_add _
  exact h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hline t)

/-- **The coordinate derivative of the resolvent**: `∂_c G_u = -√u · G_u B_c G_u` (RBM1D
`hasDerivAt_green_Hflow_update`, `IBP:114`).  The derivative of a resolvent is again a product of
resolvents, which is why the global bound `‖G‖ ≤ η⁻¹` makes every Stein hypothesis free. -/
theorem hasDerivAt_green_Hflow_update (sz : Sizes d) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Sizes.SeqΩ sz) {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n)) :
    HasDerivAt
      (fun t : ℝ => green (Sizes.seqHflow sz n u (Function.update ω (crd sz n p) t)) z)
      (-(Real.sqrt u) • (green (Sizes.seqHflow sz n u ω) z
        * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 * green (Sizes.seqHflow sz n u ω) z))
      (ω (crd sz n p)) := by
  set c := crd sz n p with hc
  set B := Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 with hB
  set G := green (Sizes.seqHflow sz n u ω) z with hG
  have hBherm : B.IsHermitian := GreenDeriv_Bmat_isHermitian hp
  have hres : ∀ t : ℝ, resH z (Sizes.seqHflow sz n u (Function.update ω c t))
      = green (Sizes.seqHflow sz n u (Function.update ω c t)) z :=
    fun t => GreenDeriv_resH_of_isHermitian (Sizes.seqHflow_isHermitian sz n u _)
  have hMG : resH z (Sizes.seqHflow sz n u ω) = G :=
    GreenDeriv_resH_of_isHermitian (Sizes.seqHflow_isHermitian sz n u ω)
  have hpath := hasDerivAt_Hflow_update sz n u ω hp
  have hself : Sizes.seqHflow sz n u (Function.update ω c (ω c)) = Sizes.seqHflow sz n u ω := by
    rw [Function.update_eq_self]
  have key := (hasFDerivAt_resH hz
    (Sizes.seqHflow sz n u (Function.update ω c (ω c)))).comp_hasDerivAt (ω c) hpath
  rw [hself] at key
  have hval : (-((ContinuousLinearMap.mulLeftRight ℝ
      (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
      (resH z (Sizes.seqHflow sz n u ω)) (resH z (Sizes.seqHflow sz n u ω))).comp
        (hermCLM (Idx d (sz.L n) (sz.W n))))) (Real.sqrt u • B) = -(Real.sqrt u) • (G * B * G) := by
    simp only [_root_.neg_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, map_smul, GreenDeriv_hermCLM_of_isHermitian hBherm,
      ContinuousLinearMap.mulLeftRight_apply, hMG]
    rw [smul_neg, neg_smul]
  rw [hval] at key
  exact key.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hres t).symm)

end Deriv

/-! ### Step 2b: the sandwich collapses to two entries

`B_p` has at most two nonzero entries, so `G B_p G` is a sum of two products of resolvent
entries.  This is the Lean form of the derivative `∂_{h_{αx}} f(G)` that the paper's weight
expansion uses (`paper/tex/7_8_light_weight.tex:292-298`, `(Owx)`).  The lemmas are matrix algebra
on `Bmat d L W`. -/

section Sandwich

variable {L W : ℕ} [NeZero L] [NeZero W]

/-- Off the diagonal, `M B_{ij,b} M'` has exactly two terms (RBM1D `mul_Bmat_mul_apply_of_ne`,
`IBP:155`). -/
private theorem mul_Bmat_mul_apply_of_ne {M M' : Matrix (Idx d L W) (Idx d L W) ℂ} {i j : Idx d L W}
    (hij : i ≠ j) (b : Bool) (a c : Idx d L W) :
    (M * Bmat d L W i j b * M') a c
      = (if b then (1 : ℂ) else Complex.I) * (M a i * M' j c)
        + (if b then (1 : ℂ) else -Complex.I) * (M a j * M' i c) := by
  have hrow : ∀ l : Idx d L W, (M * Bmat d L W i j b) a l
      = (if l = j then (if b then (1 : ℂ) else Complex.I) * M a i else 0)
        + (if l = i then (if b then (1 : ℂ) else -Complex.I) * M a j else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hlj : l = j
    · have hli : ¬ l = i := fun h => hij (h ▸ hlj)
      rw [ite_eq_left hlj, ite_eq_right hli, add_zero]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hk h.1),
          ite_eq_right (fun h => hli h.2), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [GreenDeriv_Bmat_apply, ite_eq_left ⟨rfl, hlj⟩, mul_comm]
    · by_cases hli : l = i
      · rw [ite_eq_right hlj, ite_eq_left hli, zero_add]
        refine (Finset.sum_eq_single j ?_ ?_).trans ?_
        · intro k _ hk
          rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2),
            ite_eq_right (fun h => hk h.1), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ j) h
        · rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2), ite_eq_left ⟨rfl, hli⟩,
            mul_comm]
      · rw [ite_eq_right hlj, ite_eq_right hli, add_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hlj h.2), ite_eq_right (fun h => hli h.2),
          mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, add_mul, ite_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j, Finset.sum_ite_eq' Finset.univ i,
    ite_eq_left (Finset.mem_univ j), ite_eq_left (Finset.mem_univ i)]
  ring_nf

/-- On the diagonal the real tag gives a single entry.  (`(i, i, false)` is never a used
coordinate, so the imaginary tag does not occur there.)  RBM1D `mul_Bmat_mul_apply_diag`,
`IBP:193`. -/
private theorem mul_Bmat_mul_apply_diag {M M' : Matrix (Idx d L W) (Idx d L W) ℂ}
    (i a c : Idx d L W) :
    (M * Bmat d L W i i true * M') a c = M a i * M' i c := by
  have hrow : ∀ l : Idx d L W, (M * Bmat d L W i i true) a l = (if l = i then M a i else 0) := by
    intro l
    rw [Matrix.mul_apply]
    by_cases hli : l = i
    · rw [ite_eq_left hli]
      refine (Finset.sum_eq_single i ?_ ?_).trans ?_
      · intro k _ hk
        rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hk h.1),
          ite_eq_right (fun h => hk h.1), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
      · rw [GreenDeriv_Bmat_apply, ite_eq_left ⟨rfl, hli⟩]
        simp
    · refine (Finset.sum_eq_zero fun k _ => ?_).trans (ite_eq_right hli).symm
      rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hli h.2), ite_eq_right (fun h => hli h.2),
        mul_zero]
  rw [Matrix.mul_apply]
  simp only [hrow, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ i, ite_eq_left (Finset.mem_univ i)]

end Sandwich

/-! ### Step 2c: resolvent entries are tame

`GaussIBP sz` (`Green/LDEQuad.lean:302`, a theorem since T2088: `gaussIBP sz`) is Stein's
identity for *polynomially bounded* test functions (`RBM.Green.Tame`), which is the version the
display needs: its integrand carries a factor `H_ik`, so it is never globally bounded.
Resolvent entries themselves are tame for the cheapest possible reason: the deterministic
envelope `‖G‖ ≤ η_t⁻¹` (`norm_green_apply_le_etaT`). -/

section Tame

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- `Im z_t ≠ 0` strictly inside the flow (RBM1D `zt_im_ne_zero_of_lt_one`, `IBP:227`). -/
private theorem zt_im_ne_zero_of_lt_one (hE : |E| < 2) (ht : t < 1) :
    (zt E t).im ≠ 0 := by
  rw [spectralZ_im]
  exact (mul_pos (by linarith) (spectralM_im_pos hE)).ne'

/-- **Every resolvent entry is tame** (RBM1D `tame_green_apply`, `IBP:233`).  No polynomial is
needed: the entry is bounded by `η_t⁻¹` on the whole space, so the dominating polynomial can be
taken constant. -/
theorem tame_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ) (a b : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω : Sizes.SeqΩ sz => green (Sizes.seqHflow sz n u ω) (zt E t) a b) := by
  refine ⟨?_, finDep_of_Hflow sz n u (fun M => green M (zt E t) a b),
    ⟨∅, 0, ((zt E t).im)⁻¹, fun ω => ?_⟩⟩
  · exact Continuous.matrix_elem
      (continuous_green_comp (GreenDeriv_continuous_seqHflow sz n u)
        (Sizes.seqHflow_isHermitian sz n u) (zt_im_ne_zero_of_lt_one hE ht)) a b
  · simpa using norm_green_apply_le_etaT hE ht u a b ω

end Tame

/-! ### Step 2d: reading off one entry

Stein's identity is applied to scalar test functions, so the matrix-valued derivative of step 2a
has to be pushed through the evaluation map.  For the L2 operator norm that map is bounded with
constant one (`RBM.Ind.norm_apply_le_l2_opNorm`), hence a continuous linear map. -/

section Entry

/-- Reading off the `(a, b)` entry, as a bounded `ℝ`-linear map (RBM1D `entryCLM`,
`IBP:253`). -/
private noncomputable def entryCLM (n : Type*) [Fintype n] [DecidableEq n] (a b : n) :
    Matrix n n ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun M => by
      change ‖M a b‖ ≤ 1 * ‖M‖
      simpa using norm_matrix_entry_le_opNorm M a b)

@[simp] private theorem entryCLM_apply {n : Type*} [Fintype n] [DecidableEq n] (a b : n)
    (M : Matrix n n ℂ) : entryCLM n a b M = M a b := rfl

/-- **The coordinate derivative of a resolvent entry** (RBM1D `hasDerivAt_green_apply_update`,
`IBP:270`).  This is the scalar statement Stein's identity consumes. -/
theorem hasDerivAt_green_apply_update (sz : Sizes d) (n : ℕ) (u : ℝ) {z : ℂ} (hz : z.im ≠ 0)
    (ω : Sizes.SeqΩ sz) {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n))
    (a b : Idx d (sz.L n) (sz.W n)) :
    HasDerivAt
      (fun t : ℝ => green (Sizes.seqHflow sz n u (Function.update ω (crd sz n p) t)) z a b)
      (-(Real.sqrt u) • (green (Sizes.seqHflow sz n u ω) z
        * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 * green (Sizes.seqHflow sz n u ω) z) a b)
      (ω (crd sz n p)) := by
  have h := hasDerivAt_green_Hflow_update sz n u hz ω hp
  have h2 := (entryCLM (Idx d (sz.L n) (sz.W n)) a b).hasFDerivAt.comp_hasDerivAt
    (ω (crd sz n p)) h
  simp only [Function.comp_def, entryCLM_apply] at h2
  exact h2

end Entry

/-! ### Step 2e: the integration step

This is where the display stops being pathwise.  `GaussIBP.stein` replaces the Gaussian
coordinate `ω_c` by `gvarF_c · ∂_c`, and `∂_c` of a resolvent entry is the sandwich of step 2a.
The only thing to check is that both sides are tame, and for the derivative that follows by
writing the sandwich as a double sum of entries. -/

section Integral

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- A resolvent sandwich is tame: expand it as a double sum of products of entries (RBM1D
`tame_green_mul_mul_green_apply`, `IBP:295`). -/
theorem tame_green_mul_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a b : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω : Sizes.SeqΩ sz => (green (Sizes.seqHflow sz n u ω) (zt E t) * B
      * green (Sizes.seqHflow sz n u ω) (zt E t)) a b) := by
  have hfun : (fun ω : Sizes.SeqΩ sz => (green (Sizes.seqHflow sz n u ω) (zt E t) * B
      * green (Sizes.seqHflow sz n u ω) (zt E t)) a b)
      = fun ω : Sizes.SeqΩ sz => ∑ l : Idx d (sz.L n) (sz.W n), ∑ k : Idx d (sz.L n) (sz.W n),
        green (Sizes.seqHflow sz n u ω) (zt E t) a k * B k l
          * green (Sizes.seqHflow sz n u ω) (zt E t) l b := by
    funext ω
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  rw [hfun]
  exact Tame.sum _ fun l _ => Tame.sum _ fun k _ =>
    ((tame_green_apply hE ht u a k).mul (Tame.const _)).mul (tame_green_apply hE ht u l b)

/-- **Gaussian integration by parts for one resolvent entry** (RBM1D
`integral_coord_mul_green_apply`, `IBP:315`).  `E[ω_c · G_ab]` becomes `gvarF_c · E[∂_c G_ab]`,
and the derivative is the sandwich `-√u · (G B_c G)_ab`.  This is the step where the `H_ik`
factor of the display is eliminated; the paper uses it as the Gaussian integration by parts
behind the weight expansion (`paper/tex/7_8_light_weight.tex:292-298`), with the complex entries
replaced by the independent real coordinates (`Green/FlucVanish.lean`, `Bmat`, `crd`). -/
theorem integral_coord_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n))
    (a b : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (ω (crd sz n p) : ℂ) * green (Sizes.seqHflow sz n u ω) (zt E t) a b
        ∂(Sizes.seqP sz)
      = (Sizes.seqGvar sz (crd sz n p) : ℝ) * ∫ ω, -((Real.sqrt u : ℂ)
          * (green (Sizes.seqHflow sz n u ω) (zt E t)
            * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u ω) (zt E t)) a b) ∂(Sizes.seqP sz) := by
  refine (gaussIBP sz).stein (crd sz n p) _ _ (tame_green_apply hE ht u a b) ?_ ?_
  · exact ((Tame.const (sz := sz) (Real.sqrt u : ℂ)).mul
      (tame_green_mul_mul_green_apply hE ht u _ a b)).neg
  · intro ω
    have h := hasDerivAt_green_apply_update sz n u (zt_im_ne_zero_of_lt_one hE ht) ω hp a b
    simpa [Complex.real_smul] using h

end Integral

/-! ### Step 2f: from one coordinate to a whole row

One matrix entry of `H` is carried by a *pair* of Gaussian coordinates (real and imaginary tag),
and the two tags have variance `S_ij/2` each.  Summing the one-coordinate identity of step 2e over
`usedCoords` therefore rebuilds `S_ij` exactly, while the two squared off-diagonal terms (the ones
carrying `c_b² = ±1`) cancel between the tags.  What survives is the paper's

  `E[(H_u G)_{aa}] = -u ∑_k S_{ak} E[G_{aa} G_{kk}]`,

here in the form `Σ_{p used} gvarF_p (B_p (G B_p G))_{aa} = Σ_k svarF(a,k) G_aa G_kk` for an
arbitrary complex matrix `G` (`sum_gvar_Bmat_sandwich_diag`).  The bookkeeping of the used
coordinates against the ordered pairs (`IBP_sum_used_eq_sum_pairs`) and the symmetries of `Bmat`
are ported from RBM1D `Gauss/Generator.lean` (commit `c06b103`, lines 916, 930, 977, 1058 ff.). -/

section Row

variable {L W : ℕ} [NeZero L] [NeZero W]

omit [NeZero L] [NeZero W] in
/-- The real direction is symmetric in the pair: `Bmat j i true = Bmat i j true` (RBM1D
`Bmat_swap_true`, `Generator:916`). -/
private theorem IBP_Bmat_swap_true (i j : Idx d L W) :
    Bmat d L W j i true = Bmat d L W i j true := by
  ext k l
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_left h1]
    · rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

omit [NeZero L] [NeZero W] in
/-- The imaginary direction is antisymmetric in the pair (off the diagonal):
`Bmat j i false = -Bmat i j false` (RBM1D `Bmat_swap_false`, `Generator:930`). -/
private theorem IBP_Bmat_swap_false {i j : Idx d L W} (hij : i ≠ j) :
    Bmat d L W j i false = -Bmat d L W i j false := by
  ext k l
  change Bmat d L W j i false k l = -(Bmat d L W i j false k l)
  rw [GreenDeriv_Bmat_apply, GreenDeriv_Bmat_apply]
  by_cases h1 : k = i ∧ l = j
  · have h2 : ¬ (k = j ∧ l = i) := by
      rintro ⟨hkj, _⟩
      refine hij ?_
      rw [← h1.1]
      exact hkj
    rw [ite_eq_right h2, ite_eq_left h1, ite_eq_left h1]; simp
  · by_cases h2 : k = j ∧ l = i
    · rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]; simp
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1, neg_zero]

omit [NeZero L] in
/-- The variance of a coordinate, read off from the index pair (RBM1D `gvar_crd`,
`Generator:977`; `Sblk` is `svarF`): `S_ii` on the diagonal, `S_ij / 2` off it, which is the
definition of `gvarF` (`Gauss/FineModel.lean:89`). -/
private theorem IBP_gvarF_eq (g : ℝ) (p : CoordF d L W) :
    (gvarF d L W g p : ℝ)
      = if p.1 = p.2.1 then svarF d L W g p.1 p.2.1 else svarF d L W g p.1 p.2.1 / 2 := rfl

/-- Halving is injective on an `ℝ`-module: `X + X = Y + Y` forces `X = Y` (RBM1D
`eq_of_add_self_eq_add_self`, `Generator:1014`). -/
private theorem IBP_eq_of_add_self_eq_add_self {V : Type*} [AddCommGroup V] [Module ℝ V]
    {X Y : V} (h : X + X = Y + Y) : X = Y := by
  have h2 : ((2 : ℝ)⁻¹ * 2) • X = ((2 : ℝ)⁻¹ * 2) • Y := by
    rw [mul_smul, mul_smul, two_smul, two_smul, h]
  have hc : ((2 : ℝ)⁻¹ * 2) = 1 := by norm_num
  rwa [hc, one_smul, one_smul] at h2

/-- The off-diagonal bookkeeping: a quarter of each of the two copies, twice over, is a half
(RBM1D `smul_quarter_pair`, `Generator:1024`). -/
private theorem IBP_smul_quarter_pair {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ℝ)
    (A B : V) :
    (c / 2) • A + (c / 2) • B =
      c • (1 / 4 : ℝ) • (A + B) + c • (1 / 4 : ℝ) • (A + B) := by
  rw [smul_smul, ← two_smul ℝ, smul_smul,
    show (2 * (c * (1 / 4)) : ℝ) = c / 2 by ring, smul_add]

/-- A double sum over a square index set is determined by the swap-symmetrization of its summand
(RBM1D `sum_sum_eq_of_swap_add_eq`, `Generator:1032`). -/
private theorem IBP_sum_sum_eq_of_swap_add_eq {ι : Type*} [Fintype ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V] (g h : ι → ι → V)
    (key : ∀ i j, g i j + g j i = h i j + h j i) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, h i j := by
  have e1 : ∀ F : ι → ι → V,
      (∑ i, ∑ j, (F i j + F j i)) = (∑ i, ∑ j, F i j) + (∑ i, ∑ j, F j i) := by
    intro F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hg : (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := Finset.sum_comm
  have hh : (∑ i, ∑ j, h i j) = ∑ i, ∑ j, h j i := Finset.sum_comm
  refine IBP_eq_of_add_self_eq_add_self ?_
  calc (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g i j)
      = (∑ i, ∑ j, g i j) + (∑ i, ∑ j, g j i) := by rw [← hg]
    _ = ∑ i, ∑ j, (g i j + g j i) := (e1 g).symm
    _ = ∑ i, ∑ j, (h i j + h j i) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => key i j
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h j i) := e1 h
    _ = (∑ i, ∑ j, h i j) + (∑ i, ∑ j, h i j) := by rw [← hh]

/-- **The bookkeeping lemma** (RBM1D `sum_used_eq_sum_pairs`, `Generator:1058`).  Summing a
symmetric weight `S` against a symmetric family `f` over the "used" index set (one representative
per unordered pair, both tags, plus the diagonal with the real tag) equals the full double sum over
ordered pairs, with the diagonal treated separately and the off-diagonal terms weighted by `1/4`. -/
private theorem IBP_sum_used_eq_sum_pairs {ι : Type*} [Fintype ι] [DecidableEq ι] {V : Type*}
    [AddCommGroup V] [Module ℝ V]
    (κ : ι → ℕ) (hκ : Function.Injective κ)
    (S : ι → ι → ℝ) (hS : ∀ i j, S i j = S j i)
    (f : ι × ι × Bool → V)
    (htt : ∀ i j, f (i, j, true) = f (j, i, true))
    (hff : ∀ i j, f (i, j, false) = f (j, i, false)) :
    ∑ p ∈ Finset.univ.filter
        (fun p : ι × ι × Bool => κ p.1 < κ p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)),
      (if p.1 = p.2.1 then S p.1 p.2.1 else S p.1 p.2.1 / 2) • f p
      = ∑ i : ι, ∑ j : ι, S i j •
          (if i = j then f (i, i, true)
           else (1 / 4 : ℝ) • (f (i, j, true) + f (i, j, false))) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine IBP_sum_sum_eq_of_swap_add_eq _ _ ?_
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hji : ¬ (j = i) := fun hh => hij hh.symm
    rcases lt_trichotomy (κ i) (κ j) with hlt | heq | hgt
    · simp only [hij, hji, hlt, asymm hlt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero]
      exact IBP_smul_quarter_pair _ _ _
    · exact absurd (hκ heq) hij
    · simp only [hij, hji, hgt, asymm hgt, hS j i, htt j i, hff j i, false_and, or_false,
        ite_true, ite_false, and_true, add_zero, zero_add]
      exact IBP_smul_quarter_pair _ _ _

/-- `(B_p (G B_p G))_{aa}` is `(1 · B_p · (G B_p G))_{aa}`, the shape `mul_Bmat_mul_apply_of_ne`
consumes (RBM1D `Bmat_mul_sandwich_diag_of_ne`, `IBP:345`). -/
private theorem Bmat_mul_sandwich_diag_of_ne (G : Matrix (Idx d L W) (Idx d L W) ℂ)
    {x y : Idx d L W}
    (hxy : x ≠ y) (b : Bool) (a : Idx d L W) :
    (Bmat d L W x y b * (G * Bmat d L W x y b * G)) a a
      = (if b then (1 : ℂ) else Complex.I) * ((1 : Matrix (Idx d L W) (Idx d L W) ℂ) a x
          * (G * Bmat d L W x y b * G) y a)
        + (if b then (1 : ℂ) else -Complex.I) * ((1 : Matrix (Idx d L W) (Idx d L W) ℂ) a y
          * (G * Bmat d L W x y b * G) x a) := by
  have h := mul_Bmat_mul_apply_of_ne (M := (1 : Matrix (Idx d L W) (Idx d L W) ℂ))
    (M' := G * Bmat d L W x y b * G) hxy b a a
  rw [Matrix.one_mul] at h
  exact h

/-- **The two tags of an off-diagonal coordinate** (RBM1D `Bmat_sandwich_diag_add_of_ne`,
`IBP:359`).  The squared off-diagonal terms carry opposite signs and cancel; twice `G_{xx} G_{yy}`
survives. -/
private theorem Bmat_sandwich_diag_add_of_ne (G : Matrix (Idx d L W) (Idx d L W) ℂ)
    {x y : Idx d L W}
    (hxy : x ≠ y) (a : Idx d L W) :
    (Bmat d L W x y true * (G * Bmat d L W x y true * G)) a a
      + (Bmat d L W x y false * (G * Bmat d L W x y false * G)) a a
      = 2 * ((if a = x then G x x * G y y else 0) + (if a = y then G x x * G y y else 0)) := by
  have ht := Bmat_mul_sandwich_diag_of_ne G hxy true a
  have hf := Bmat_mul_sandwich_diag_of_ne G hxy false a
  have hKt := fun (p q : Idx d L W) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy true p q
  have hKf := fun (p q : Idx d L W) => mul_Bmat_mul_apply_of_ne (M := G) (M' := G) hxy false p q
  rw [ht, hf, hKt, hKt, hKf, hKf]
  simp only [Bool.false_eq_true, reduceIte]
  by_cases hax : a = x
  · subst hax
    have hay : ¬ a = y := hxy
    rw [Matrix.one_apply_eq, Matrix.one_apply_ne hay, ite_eq_left rfl, ite_eq_right hay]
    ring_nf
    rw [Complex.I_sq]
    ring
  · by_cases hay : a = y
    · subst hay
      rw [Matrix.one_apply_eq, Matrix.one_apply_ne hax, ite_eq_left rfl, ite_eq_right hax]
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [Matrix.one_apply_ne hax, Matrix.one_apply_ne hay, ite_eq_right hax,
        ite_eq_right hay]
      ring

/-- **The diagonal coordinate** (RBM1D `Bmat_sandwich_diag_diag`, `IBP:388`).
`B_{ii,true} = E_{ii}`, so the sandwich is a single square. -/
private theorem Bmat_sandwich_diag_diag (G : Matrix (Idx d L W) (Idx d L W) ℂ) (x a : Idx d L W) :
    (Bmat d L W x x true * (G * Bmat d L W x x true * G)) a a
      = if a = x then G x x * G x x else 0 := by
  have h := mul_Bmat_mul_apply_diag (M := (1 : Matrix (Idx d L W) (Idx d L W) ℂ))
    (M' := G * Bmat d L W x x true * G) x a a
  rw [Matrix.one_mul] at h
  rw [h, mul_Bmat_mul_apply_diag]
  by_cases hax : a = x
  · subst hax
    simp
  · simp [hax]

/-- The sandwich at a diagonal entry is symmetric under swapping the two indices of the
coordinate: it is quadratic in `B_p`, and the swap changes `B_p` by at most a sign (RBM1D
`Bmat_sandwich_diag_swap`, `IBP:402`). -/
private theorem Bmat_sandwich_diag_swap (G : Matrix (Idx d L W) (Idx d L W) ℂ) (x y : Idx d L W)
    (b : Bool) (a : Idx d L W) :
    (Bmat d L W x y b * (G * Bmat d L W x y b * G)) a a
      = (Bmat d L W y x b * (G * Bmat d L W y x b * G)) a a := by
  by_cases hxy : x = y
  · rw [hxy]
  · cases b with
    | true => rw [IBP_Bmat_swap_true x y]
    | false =>
      rw [IBP_Bmat_swap_false hxy]
      simp

/-- **The coordinate sum of the integration-by-parts display collapses to a row of `S`**
(RBM1D `sum_gvar_Bmat_sandwich_diag`, `IBP:419`, with `Sblk` read as `svarF`).

`∑_{p ∈ usedCoords} gvarF_p (B_p G B_p G)_{aa} = ∑_k svarF_{ak} G_{aa} G_{kk}`: the two tags of an
off-diagonal coordinate each contribute `gvarF = svarF/2`, the squared off-diagonal terms cancel
between them, and the diagonal coordinate (real tag only, `gvarF = svarF`) supplies
`svarF_{aa} G_{aa}²`.  `G` is an arbitrary complex matrix; only `svarF_comm` is used. -/
private theorem IBP_sum_gvar_Bmat_sandwich_diag (g : ℝ) (G : Matrix (Idx d L W) (Idx d L W) ℂ)
    (a : Idx d L W) :
    ∑ p ∈ usedCoords d L W, (gvarF d L W g p : ℝ) •
        (Bmat d L W p.1 p.2.1 p.2.2 * (G * Bmat d L W p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svarF d L W g a k : ℂ) * (G a a * G k k) := by
  classical
  set f : Idx d L W × Idx d L W × Bool → ℂ :=
    fun p => (Bmat d L W p.1 p.2.1 p.2.2 * (G * Bmat d L W p.1 p.2.1 p.2.2 * G)) a a with hf
  have hgv : ∑ p ∈ usedCoords d L W, (gvarF d L W g p : ℝ) • f p
      = ∑ p ∈ usedCoords d L W,
        (if p.1 = p.2.1 then svarF d L W g p.1 p.2.1 else svarF d L W g p.1 p.2.1 / 2) • f p :=
    Finset.sum_congr rfl fun p _ => by rw [IBP_gvarF_eq]
  have hused : usedCoords d L W = Finset.univ.filter
      (fun p : Idx d L W × Idx d L W × Bool =>
        idxKey d L W p.1 < idxKey d L W p.2.1 ∨ (p.1 = p.2.1 ∧ p.2.2 = true)) := by
    ext p
    simp only [GreenDeriv_mem_usedCoords, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hgv, hused,
    IBP_sum_used_eq_sum_pairs (idxKey d L W) (idxKey_injective d L W) (svarF d L W g)
      (svarF_comm d L W g) f
      (fun x y => Bmat_sandwich_diag_swap G x y true a)
      (fun x y => Bmat_sandwich_diag_swap G x y false a)]
  -- The term at `(x, y)` splits into the `x = a` half and the `y = a` half.
  have hterm : ∀ x y : Idx d L W,
      (svarF d L W g x y : ℝ) •
          (if x = y then f (x, x, true) else (1 / 4 : ℝ) • (f (x, y, true) + f (x, y, false)))
        = (if x = a then (2 : ℂ)⁻¹ * ((svarF d L W g a y : ℂ) * (G a a * G y y)) else 0)
          + (if y = a then (2 : ℂ)⁻¹ * ((svarF d L W g x a : ℂ) * (G x x * G a a))
              else 0) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      simp only [hf, ite_true, Bmat_sandwich_diag_diag G x a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        simp only [ite_true]
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        simp only [ite_eq_right hax, ite_eq_right hxa]
        ring
    · simp only [hf, ite_eq_right hxy, Bmat_sandwich_diag_add_of_ne G hxy a, Complex.real_smul]
      by_cases hax : a = x
      · subst hax
        have hya : ¬ (y = a) := fun h => hxy h.symm
        simp only [ite_true, ite_eq_right hxy, ite_eq_right hya]
        push_cast
        ring
      · have hxa : ¬ (x = a) := fun h => hax h.symm
        by_cases hay : a = y
        · subst hay
          simp only [ite_true, ite_eq_right hax, ite_eq_right hxa]
          push_cast
          ring
        · have hya : ¬ (y = a) := fun h => hay h.symm
          simp only [ite_eq_right hax, ite_eq_right hay, ite_eq_right hxa, ite_eq_right hya]
          push_cast
          ring
  simp only [hterm, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y : Idx d L W =>
      if x = a then (2 : ℂ)⁻¹ * ((svarF d L W g a y : ℂ) * (G a a * G y y)) else 0)]
  simp only [Finset.sum_ite_eq' Finset.univ a, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [svarF_comm d L W g k a]
  ring

end Row

/-- **The coordinate sum of the integration-by-parts display collapses to a row of `S`**
(RBM1D `sum_gvar_Bmat_sandwich_diag`, `IBP:419`; `Sblk` is `svarF`).  For an arbitrary complex
matrix `G` (not assumed symmetric) and every `a`,
`∑_{p ∈ usedCoords} gvarF_p (B_p (G B_p G))_{aa} = ∑_k svarF(a,k) G_{aa} G_{kk}`. -/
theorem sum_gvar_Bmat_sandwich_diag (sz : Sizes d) (n : ℕ)
    (G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Idx d (sz.L n) (sz.W n)) :
    ∑ p ∈ usedCoords d (sz.L n) (sz.W n), (Sizes.seqGvar sz (crd sz n p) : ℝ) •
        (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * (G * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) a k : ℂ) * (G a a * G k k) :=
  IBP_sum_gvar_Bmat_sandwich_diag (sz.lam n) G a

/-- The complex form of `sum_gvar_Bmat_sandwich_diag` (RBM1D `sum_gvar_Bmat_sandwich_diag_mul`,
`IBP:569`). -/
theorem sum_gvar_Bmat_sandwich_diag_mul (sz : Sizes d) (n : ℕ)
    (G : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Idx d (sz.L n) (sz.W n)) :
    ∑ p ∈ usedCoords d (sz.L n) (sz.W n), ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ) *
        (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * (G * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 * G)) a a
      = ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) a k : ℂ) * (G a a * G k k) := by
  rw [← sum_gvar_Bmat_sandwich_diag sz n G a]
  exact Finset.sum_congr rfl fun p _ => Complex.real_smul.symm

/-! ### Step 2f (continued): the whole row inside one integral

Multiplication by a constant matrix, and Stein's identity for `(B_p G)_{aa}`. -/

section IntegralRow

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- Multiplying on the left by a **constant** matrix is a finite linear combination of entries,
so it passes through the integral (RBM1D `integral_const_matrix_mul_apply`, `IBP:492`). -/
private theorem integral_const_matrix_mul_apply
    {F : Sizes.SeqΩ sz → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ}
    {g : Sizes.SeqΩ sz → ℂ} (B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a : Idx d (sz.L n) (sz.W n))
    (hint : ∀ l, Integrable (fun ω => g ω * F ω l a) (Sizes.seqP sz)) :
    ∫ ω, g ω * (B * F ω) a a ∂(Sizes.seqP sz)
      = ∑ l, B a l * ∫ ω, g ω * F ω l a ∂(Sizes.seqP sz) := by
  have hpt : ∀ ω, g ω * (B * F ω) a a = ∑ l, B a l * (g ω * F ω l a) := by
    intro ω
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [hpt]
  rw [MeasureTheory.integral_finsetSum _ (fun l _ => (hint l).const_mul (B a l))]
  exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _

/-- `(B G)_{ac}` is tame for a constant `B` (RBM1D `tame_const_mul_green_apply`, `IBP:543`). -/
theorem tame_const_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a c : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω : Sizes.SeqΩ sz => (B * green (Sizes.seqHflow sz n u ω) (zt E t)) a c) := by
  have hfun : (fun ω : Sizes.SeqΩ sz => (B * green (Sizes.seqHflow sz n u ω) (zt E t)) a c)
      = fun ω : Sizes.SeqΩ sz =>
        ∑ l, B a l * green (Sizes.seqHflow sz n u ω) (zt E t) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ => (Tame.const _).mul (tame_green_apply hE ht u l c)

/-- `(B (G B G))_{ac}` is tame for a constant `B` (RBM1D `tame_const_mul_sandwich_apply`,
`IBP:554`). -/
theorem tame_const_mul_sandwich_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a c : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun ω : Sizes.SeqΩ sz => (B * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
      * green (Sizes.seqHflow sz n u ω) (zt E t))) a c) := by
  have hfun : (fun ω : Sizes.SeqΩ sz => (B * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
      * green (Sizes.seqHflow sz n u ω) (zt E t))) a c)
      = fun ω : Sizes.SeqΩ sz => ∑ l, B a l * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
        * green (Sizes.seqHflow sz n u ω) (zt E t)) l c := by
    funext ω
    rw [Matrix.mul_apply]
  rw [hfun]
  exact Tame.sum _ fun l _ =>
    (Tame.const _).mul (tame_green_mul_mul_green_apply hE ht u B l c)

/-- **Integration by parts for a whole row** (RBM1D `integral_coord_mul_Bmat_mul_green_diag`,
`IBP:507`).  `E[ω_p (B_p G)_{aa}]` collapses to the `gvarF`-weighted sandwich
`(B_p G B_p G)_{aa}`: the two entries of `B_p` are handled by `integral_coord_mul_green_apply`
one at a time and recombined. -/
theorem integral_coord_mul_Bmat_mul_green_diag (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n))
    (a : Idx d (sz.L n) (sz.W n)) :
    ∫ ω, (ω (crd sz n p) : ℂ)
        * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * green (Sizes.seqHflow sz n u ω) (zt E t)) a a ∂(Sizes.seqP sz)
      = (Sizes.seqGvar sz (crd sz n p) : ℝ) * ∫ ω, -((Real.sqrt u : ℂ)
          * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * (green (Sizes.seqHflow sz n u ω) (zt E t)
              * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
              * green (Sizes.seqHflow sz n u ω) (zt E t))) a a) ∂(Sizes.seqP sz) := by
  set B := Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 with hB
  have hint1 : ∀ l : Idx d (sz.L n) (sz.W n), Integrable
      (fun ω : Sizes.SeqΩ sz => (ω (crd sz n p) : ℂ)
        * green (Sizes.seqHflow sz n u ω) (zt E t) l a) (Sizes.seqP sz) :=
    fun l => ((Tame.coord (crd sz n p)).mul (tame_green_apply hE ht u l a)).integrable (gaussIBP sz)
  have hint2 : ∀ l : Idx d (sz.L n) (sz.W n), Integrable
      (fun ω : Sizes.SeqΩ sz => (1 : ℂ) * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
        * green (Sizes.seqHflow sz n u ω) (zt E t)) l a) (Sizes.seqP sz) :=
    fun l => ((Tame.const (sz := sz) 1).mul
      (tame_green_mul_mul_green_apply hE ht u B l a)).integrable (gaussIBP sz)
  rw [integral_const_matrix_mul_apply B a hint1]
  have hstep : ∀ l : Idx d (sz.L n) (sz.W n),
      ∫ ω, (ω (crd sz n p) : ℂ) * green (Sizes.seqHflow sz n u ω) (zt E t) l a
          ∂(Sizes.seqP sz)
        = (Sizes.seqGvar sz (crd sz n p) : ℝ) * -((Real.sqrt u : ℂ)
            * ∫ ω, (green (Sizes.seqHflow sz n u ω) (zt E t) * B
              * green (Sizes.seqHflow sz n u ω) (zt E t)) l a ∂(Sizes.seqP sz)) := by
    intro l
    rw [integral_coord_mul_green_apply hE ht u hp l a, integral_neg, integral_const_mul]
  simp only [hstep]
  have hrev : ∫ ω, (1 : ℂ) * (B * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
      * green (Sizes.seqHflow sz n u ω) (zt E t))) a a ∂(Sizes.seqP sz)
      = ∑ l, B a l * ∫ ω, (1 : ℂ) * (green (Sizes.seqHflow sz n u ω) (zt E t) * B
        * green (Sizes.seqHflow sz n u ω) (zt E t)) l a ∂(Sizes.seqP sz) :=
    integral_const_matrix_mul_apply B a hint2
  simp only [one_mul] at hrev
  rw [integral_neg, integral_const_mul, hrev, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

end IntegralRow

/-! ### Step 2g: the same, inside `E_i`

The display is a statement about `E_i`, not about `E`.  That costs nothing extra: `E_i` is
*itself* an integral against `Sizes.seqP sz` of the integrand composed with `rowSplit`, and
`rowSplit` commutes with updating a row-`i` coordinate, so `gaussIBP` applies to it verbatim.
The only new input is that tameness survives freezing the coordinates off row `i`. -/

section CondIBP

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- Updating a **row-`k`** coordinate commutes with the splitting: `rowSplit` reads that
coordinate from its second argument (RBM1D `rowSplit_update`, `IBP:675`). -/
private theorem rowSplit_update (k : Idx d (sz.L n) (sz.W n)) (ω ω' : Sizes.SeqΩ sz)
    {c : Sizes.SeqCoord sz} (hc : IsRowCoord sz n k c) (s : ℝ) :
    rowSplit sz n k ω (Function.update ω' c s) = Function.update (rowSplit sz n k ω ω') c s := by
  funext e
  by_cases hec : e = c
  · subst hec
    rw [rowSplit_apply_of_isRowCoord k ω _ hc, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hec]
    unfold rowSplit
    split_ifs with h
    · rw [Function.update_of_ne hec]
    · rfl

/-- `ω' ↦ rowSplit k ω ω'` is continuous: every coordinate is either a projection or a
constant (RBM1D `continuous_rowSplit_right`, `IBP:690`). -/
private theorem continuous_rowSplit_right (sz : Sizes d) (n : ℕ) (k : Idx d (sz.L n) (sz.W n))
    (ω : Sizes.SeqΩ sz) :
    Continuous fun ω' : Sizes.SeqΩ sz => rowSplit sz n k ω ω' := by
  refine continuous_pi fun c => ?_
  unfold rowSplit
  by_cases h : IsRowCoord sz n k c
  · simpa [h] using continuous_apply c
  · simpa [h] using continuous_const (y := ω c)

/-- `polyW` of a split point is bounded by the product of the two `polyW`s (RBM1D
`polyW_rowSplit_le`, `IBP:699`). -/
private theorem polyW_rowSplit_le (k : Idx d (sz.L n) (sz.W n)) (I : Finset (Sizes.SeqCoord sz))
    (ω ω' : Sizes.SeqΩ sz) :
    polyW I (rowSplit sz n k ω ω') ≤ polyW I ω * polyW I ω' := by
  have hb : ∀ c ∈ I, |rowSplit sz n k ω ω' c| ≤ |ω c| + |ω' c| := by
    intro c _
    unfold rowSplit
    split_ifs with h
    · have : (0 : ℝ) ≤ |ω c| := abs_nonneg _
      linarith
    · have : (0 : ℝ) ≤ |ω' c| := abs_nonneg _
      linarith
  have hsum : ∑ c ∈ I, |rowSplit sz n k ω ω' c| ≤ (∑ c ∈ I, |ω c|) + ∑ c ∈ I, |ω' c| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hb
  have hA : (0 : ℝ) ≤ ∑ c ∈ I, |ω c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB : (0 : ℝ) ≤ ∑ c ∈ I, |ω' c| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold polyW
  nlinarith

/-- **Tameness is preserved by freezing the coordinates off row `k`** (RBM1D
`Tame.comp_rowSplit`, `IBP:718`). -/
private theorem Tame.comp_rowSplit {f : Sizes.SeqΩ sz → ℂ} (hf : Tame sz f)
    (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    Tame sz (fun ω' : Sizes.SeqΩ sz => f (rowSplit sz n k ω ω')) := by
  obtain ⟨I, m, C, hb⟩ := hf.poly
  obtain ⟨J, hJ⟩ := hf.findep
  refine ⟨hf.cont.comp (continuous_rowSplit_right sz n k ω), ⟨J, fun ω' ω'' h => ?_⟩,
    ⟨I, m, C * polyW I ω ^ m, fun ω' => ?_⟩⟩
  · refine hJ _ _ fun e he => ?_
    unfold rowSplit
    split_ifs with hrow
    · exact h e he
    · rfl
  · have hC : 0 ≤ C := by
      have hp : (0 : ℝ) < polyW I (fun _ => 0) ^ m := pow_pos (polyW_pos _ _) _
      nlinarith [norm_nonneg (f fun _ => 0), hb fun _ => 0]
    have hle : polyW I (rowSplit sz n k ω ω') ^ m ≤ polyW I ω ^ m * polyW I ω' ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (le_of_lt (polyW_pos _ _)) (polyW_rowSplit_le k I ω ω') m
    calc ‖f (rowSplit sz n k ω ω')‖ ≤ C * polyW I (rowSplit sz n k ω ω') ^ m :=
          hb (rowSplit sz n k ω ω')
      _ ≤ C * (polyW I ω ^ m * polyW I ω' ^ m) := mul_le_mul_of_nonneg_left hle hC
      _ = C * polyW I ω ^ m * polyW I ω' ^ m := by ring

/-- **Gaussian integration by parts inside `E_k`** (RBM1D `condRow_coord_mul`, `IBP:743`).  For a
coordinate of row `k`, `E_k` is an integral against the *same* product measure in the split
variable, so `gaussIBP` applies verbatim once the integrand is composed with `rowSplit`. -/
theorem condRow_coord_mul (k : Idx d (sz.L n) (sz.W n))
    {c : Sizes.SeqCoord sz} (hc : IsRowCoord sz n k c) (g g' : Sizes.SeqΩ sz → ℂ)
    (hg : Tame sz g) (hg' : Tame sz g')
    (hd : ∀ η : Sizes.SeqΩ sz,
      HasDerivAt (fun s : ℝ => g (Function.update η c s)) (g' η) (η c))
    (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => (η c : ℂ) * g η) ω
      = (Sizes.seqGvar sz c : ℝ) * condRow sz n k g' ω := by
  rw [condRow_apply, condRow_apply]
  have hlhs : ∀ ω' : Sizes.SeqΩ sz,
      ((rowSplit sz n k ω ω' c : ℝ) : ℂ) * g (rowSplit sz n k ω ω')
        = (ω' c : ℂ) * g (rowSplit sz n k ω ω') := by
    intro ω'
    rw [rowSplit_apply_of_isRowCoord k ω ω' hc]
  simp only [hlhs]
  refine (gaussIBP sz).stein c _ _ (hg.comp_rowSplit k ω) (hg'.comp_rowSplit k ω) fun ω' => ?_
  have hup : ∀ s : ℝ, g (rowSplit sz n k ω (Function.update ω' c s))
      = g (Function.update (rowSplit sz n k ω ω') c s) := by
    intro s
    rw [rowSplit_update k ω ω' hc s]
  have h := hd (rowSplit sz n k ω ω')
  rw [rowSplit_apply_of_isRowCoord k ω ω' hc] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => hup s)

/-! ### `E_k` is linear -/

/-- `E_k[c X] = c E_k[X]` (RBM1D `condRow_const_mul`, `IBP:766`). -/
theorem condRow_const_mul (k : Idx d (sz.L n) (sz.W n)) (c : ℂ) (X : Sizes.SeqΩ sz → ℂ)
    (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => c * X η) ω = c * condRow sz n k X ω := by
  rw [condRow_apply, condRow_apply]
  exact integral_const_mul _ _

/-- `E_k[-(c X)] = -(c E_k[X])` (RBM1D `condRow_neg_const_mul`, `IBP:771`). -/
theorem condRow_neg_const_mul (k : Idx d (sz.L n) (sz.W n)) (c : ℂ) (X : Sizes.SeqΩ sz → ℂ)
    (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => -(c * X η)) ω = -(c * condRow sz n k X ω) := by
  rw [condRow_apply, condRow_apply, integral_neg, integral_const_mul]

/-- `E_k` commutes with finite sums of tame functions (RBM1D `condRow_finsetSum`, `IBP:775`). -/
theorem condRow_finsetSum (k : Idx d (sz.L n) (sz.W n)) {ι : Type*}
    (s : Finset ι) (F : ι → Sizes.SeqΩ sz → ℂ) (hF : ∀ p ∈ s, Tame sz (F p))
    (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => ∑ p ∈ s, F p η) ω = ∑ p ∈ s, condRow sz n k (F p) ω := by
  simp only [condRow_apply]
  exact MeasureTheory.integral_finsetSum _
    fun p hp => ((hF p hp).comp_rowSplit k ω).integrable (gaussIBP sz)

/-- `E_k[0] = 0` (RBM1D `condRow_zero_apply`, `IBP:782`). -/
theorem condRow_zero_apply (k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun _ => (0 : ℂ)) ω = 0 := by
  rw [condRow_apply, integral_zero]

/-! ### The coordinates that do not touch row `i` drop out -/

/-- `B_{xy,b}` has no entry in row `i` unless `i` is `x` or `y` (RBM1D
`Bmat_mul_apply_diag_of_ne`, `IBP:789`). -/
theorem Bmat_mul_apply_diag_of_ne {L W : ℕ} [NeZero L] [NeZero W] {x y i : Idx d L W}
    (hx : ¬ i = x) (hy : ¬ i = y) (b : Bool) (M : Matrix (Idx d L W) (Idx d L W) ℂ) :
    (Bmat d L W x y b * M) i i = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [GreenDeriv_Bmat_apply, ite_eq_right (fun h => hx h.1), ite_eq_right (fun h => hy h.1),
    zero_mul]

/-! ### The conditional derivative of a row of the resolvent -/

/-- The coordinate derivative of `(B G)_{ac}` for a constant `B` (RBM1D
`hasDerivAt_const_mul_green_apply_update`, `IBP:798`). -/
theorem hasDerivAt_const_mul_green_apply_update (sz : Sizes d) (n : ℕ) (u : ℝ) {z : ℂ}
    (hz : z.im ≠ 0) (η : Sizes.SeqΩ sz) {p : CoordF d (sz.L n) (sz.W n)}
    (hp : p ∈ usedCoords d (sz.L n) (sz.W n))
    (B : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a c : Idx d (sz.L n) (sz.W n)) :
    HasDerivAt
      (fun s : ℝ => (B * green (Sizes.seqHflow sz n u (Function.update η (crd sz n p) s)) z) a c)
      (-((Real.sqrt u : ℂ) * (B * (green (Sizes.seqHflow sz n u η) z
        * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow sz n u η) z)) a c)) (η (crd sz n p)) := by
  have hterm : ∀ l : Idx d (sz.L n) (sz.W n), HasDerivAt
      (fun s : ℝ => B a l
        * green (Sizes.seqHflow sz n u (Function.update η (crd sz n p) s)) z l c)
      (B a l * -((Real.sqrt u : ℂ) * (green (Sizes.seqHflow sz n u η) z
        * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow sz n u η) z) l c)) (η (crd sz n p)) := by
    intro l
    have h := hasDerivAt_green_apply_update sz n u hz η hp l c
    refine HasDerivAt.const_mul (B a l) ?_
    simpa [Complex.real_smul] using h
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))))
    (A := fun l (s : ℝ) => B a l
      * green (Sizes.seqHflow sz n u (Function.update η (crd sz n p) s)) z l c)
    (A' := fun l => B a l * -((Real.sqrt u : ℂ)
      * (green (Sizes.seqHflow sz n u η) z * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow sz n u η) z) l c))
    (fun l _ => hterm l)
  have hval : ∑ l : Idx d (sz.L n) (sz.W n), B a l * -((Real.sqrt u : ℂ)
      * (green (Sizes.seqHflow sz n u η) z * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow sz n u η) z) l c)
      = -((Real.sqrt u : ℂ) * (B * (green (Sizes.seqHflow sz n u η) z
        * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
        * green (Sizes.seqHflow sz n u η) z)) a c) := by
    rw [Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [hval] at hsum
  refine hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mul_apply (M := B)
    (N := green (Sizes.seqHflow sz n u (Function.update η (crd sz n p) s)) z) (i := a)
    (k := c)).symm

/-! ### Step (b): the conditional integration by parts, one coordinate at a time -/

/-- **`E_i[ω_p (B_p G)_{ii}] = gvarF_p E_i[-√u (B_p G B_p G)_{ii}]`** (RBM1D
`condRow_coord_mul_Bmat_mul_green_diag`, `IBP:834`).  For a coordinate of row `i` this is
`condRow_coord_mul`; for any other coordinate both sides vanish identically, because `B_p` has no
entry in row `i`. -/
theorem condRow_coord_mul_Bmat_mul_green_diag (hE : |E| < 2) (ht : t < 1)
    (u : ℝ) {p : CoordF d (sz.L n) (sz.W n)} (hp : p ∈ usedCoords d (sz.L n) (sz.W n))
    (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    condRow sz n i (fun η => (η (crd sz n p) : ℂ)
        * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * green (Sizes.seqHflow sz n u η) (zt E t)) i i) ω
      = (Sizes.seqGvar sz (crd sz n p) : ℝ) * condRow sz n i (fun η => -((Real.sqrt u : ℂ)
          * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * (green (Sizes.seqHflow sz n u η) (zt E t)
              * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
              * green (Sizes.seqHflow sz n u η) (zt E t))) i i)) ω := by
  obtain ⟨x, y, b⟩ := p
  by_cases hrow : IsRowCoord sz n i (crd sz n (x, y, b))
  · refine condRow_coord_mul i hrow _ _
      (tame_const_mul_green_apply hE ht u (Bmat d (sz.L n) (sz.W n) x y b) i i)
      (((Tame.const (sz := sz) (Real.sqrt u : ℂ)).mul
        (tame_const_mul_sandwich_apply hE ht u (Bmat d (sz.L n) (sz.W n) x y b) i i)).neg)
      (fun η => ?_) ω
    exact hasDerivAt_const_mul_green_apply_update sz n u
      (zt_im_ne_zero_of_lt_one hE ht) η hp (Bmat d (sz.L n) (sz.W n) x y b) i i
  · rw [crd, isRowCoord_mk] at hrow
    have hx : ¬ i = x := fun h => hrow (Or.inl h.symm)
    have hy : ¬ i = y := fun h => hrow (Or.inr h.symm)
    have hz1 : ∀ η : Sizes.SeqΩ sz, (η (crd sz n (x, y, b)) : ℂ)
        * (Bmat d (sz.L n) (sz.W n) x y b
          * green (Sizes.seqHflow sz n u η) (zt E t)) i i = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero]
    have hz2 : ∀ η : Sizes.SeqΩ sz, -((Real.sqrt u : ℂ)
        * (Bmat d (sz.L n) (sz.W n) x y b * (green (Sizes.seqHflow sz n u η) (zt E t)
          * Bmat d (sz.L n) (sz.W n) x y b
          * green (Sizes.seqHflow sz n u η) (zt E t))) i i) = 0 := by
      intro η
      rw [Bmat_mul_apply_diag_of_ne hx hy b, mul_zero, neg_zero]
    simp only [hz1, hz2, condRow_zero_apply, mul_zero]

/-- **Step (b): the conditional row identity** (RBM1D `condRow_Hflow_mul_green_diag`,
`IBP:869`).

`E_i[(H_u G)_{ii}] = -u ∑_k S_{ik} E_i[G_{ii} G_{kk}]`: the whole-row Gaussian integration by
parts of the display, taken inside the conditional expectation `E_i`.  Only the coordinates of
row `i` occur (the others annihilate `B_p` in row `i`), and those are exactly the ones `E_i`
integrates out, so `condRow_coord_mul` applies to every surviving term. -/
theorem condRow_Hflow_mul_green_diag (hE : |E| < 2) (ht : t < 1)
    {u : ℝ} (hu : 0 ≤ u) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    condRow sz n i (fun η => (Sizes.seqHflow sz n u η
        * green (Sizes.seqHflow sz n u η) (zt E t)) i i) ω
      = -((u : ℂ) * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * condRow sz n i (fun η => green (Sizes.seqHflow sz n u η) (zt E t) i i
              * green (Sizes.seqHflow sz n u η) (zt E t) k k) ω) := by
  classical
  have hsq : (Real.sqrt u : ℂ) * (Real.sqrt u : ℂ) = (u : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu]
  have h1 : ∀ η : Sizes.SeqΩ sz, (Sizes.seqHflow sz n u η
      * green (Sizes.seqHflow sz n u η) (zt E t)) i i
      = ∑ p ∈ usedCoords d (sz.L n) (sz.W n), (Real.sqrt u : ℂ) * ((η (crd sz n p) : ℂ)
          * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u η) (zt E t)) i i) := by
    intro η
    rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqXmat_eq_sum, Matrix.smul_mul,
      Finset.sum_mul]
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
      Finset.mul_sum]
  have htamep : ∀ p ∈ usedCoords d (sz.L n) (sz.W n), Tame sz
      (fun η : Sizes.SeqΩ sz => (Real.sqrt u : ℂ) * ((η (crd sz n p) : ℂ)
        * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * green (Sizes.seqHflow sz n u η) (zt E t)) i i)) :=
    fun p _ => (Tame.const (sz := sz) (Real.sqrt u : ℂ)).mul
      ((Tame.coord (crd sz n p)).mul
        (tame_const_mul_green_apply hE ht u (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2) i i))
  simp only [h1]
  rw [condRow_finsetSum i _ _ htamep]
  have hstep : ∀ p ∈ usedCoords d (sz.L n) (sz.W n),
      condRow sz n i (fun η => (Real.sqrt u : ℂ) * ((η (crd sz n p) : ℂ)
          * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u η) (zt E t)) i i)) ω
        = -((u : ℂ) * (((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)
            * condRow sz n i (fun η => (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
              * (green (Sizes.seqHflow sz n u η) (zt E t)
                * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
                * green (Sizes.seqHflow sz n u η) (zt E t))) i i) ω)) := by
    intro p hp
    rw [condRow_const_mul, condRow_coord_mul_Bmat_mul_green_diag hE ht u hp i ω,
      condRow_neg_const_mul, ← hsq]
    ring
  rw [Finset.sum_congr rfl hstep]
  have htameq : ∀ p ∈ usedCoords d (sz.L n) (sz.W n), Tame sz
      (fun η : Sizes.SeqΩ sz => ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)
        * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * (green (Sizes.seqHflow sz n u η) (zt E t)
            * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u η) (zt E t))) i i) :=
    fun p _ => (Tame.const (sz := sz) ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)).mul
      (tame_const_mul_sandwich_apply hE ht u (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2) i i)
  have htamek : ∀ k ∈ (Finset.univ : Finset (Idx d (sz.L n) (sz.W n))), Tame sz
      (fun η : Sizes.SeqΩ sz => (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
        * (green (Sizes.seqHflow sz n u η) (zt E t) i i
          * green (Sizes.seqHflow sz n u η) (zt E t) k k)) :=
    fun k _ => (Tame.const (sz := sz) ((svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℝ) : ℂ)).mul
      ((tame_green_apply hE ht u i i).mul (tame_green_apply hE ht u k k))
  have hcollapse : ∑ p ∈ usedCoords d (sz.L n) (sz.W n),
        ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)
        * condRow sz n i (fun η => (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
          * (green (Sizes.seqHflow sz n u η) (zt E t)
            * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u η) (zt E t))) i i) ω
      = ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
        * condRow sz n i (fun η => green (Sizes.seqHflow sz n u η) (zt E t) i i
            * green (Sizes.seqHflow sz n u η) (zt E t) k k) ω := by
    have hL : ∑ p ∈ usedCoords d (sz.L n) (sz.W n), ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)
          * condRow sz n i (fun η => (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * (green (Sizes.seqHflow sz n u η) (zt E t)
              * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
              * green (Sizes.seqHflow sz n u η) (zt E t))) i i) ω
        = condRow sz n i (fun η => ∑ p ∈ usedCoords d (sz.L n) (sz.W n),
            ((Sizes.seqGvar sz (crd sz n p) : ℝ) : ℂ)
            * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
              * (green (Sizes.seqHflow sz n u η) (zt E t)
                * Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
                * green (Sizes.seqHflow sz n u η) (zt E t))) i i) ω := by
      rw [condRow_finsetSum i _ _ htameq]
      exact Finset.sum_congr rfl fun p _ => (condRow_const_mul _ _ _ _).symm
    have hR : ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * condRow sz n i (fun η => green (Sizes.seqHflow sz n u η) (zt E t) i i
              * green (Sizes.seqHflow sz n u η) (zt E t) k k) ω
        = condRow sz n i (fun η => ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
            * (green (Sizes.seqHflow sz n u η) (zt E t) i i
              * green (Sizes.seqHflow sz n u η) (zt E t) k k)) ω := by
      rw [condRow_finsetSum i _ _ htamek]
      exact Finset.sum_congr rfl fun k _ => (condRow_const_mul _ _ _ _).symm
    rw [hL, hR]
    simp only [sum_gvar_Bmat_sandwich_diag_mul sz n _ i]
  rw [← hcollapse, Finset.sum_neg_distrib, ← Finset.mul_sum]

end CondIBP

/-! ### Step 3: the display, as an identity

Putting step 1 and step 2g together at the entry `(i,i)` gives the display with **no** error
term:

  `E_i(G_ii - m) = t m ∑_k S_ik E_i[G_ii (G_kk - m)]`.

Everything that is `O≺(Ψ²)` in the paper is the difference between this and the form the
fluctuation-averaging step asks for, namely `t m² ∑_k S_ik (G_kk - m)`; that difference is
isolated in the next section. -/

section CondDisplay

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- The coordinate decomposition of `H_u M`, for an arbitrary right factor (RBM1D
`Hflow_mul_apply_eq_sum`, `IBP:961`). -/
private theorem Hflow_mul_apply_eq_sum (sz : Sizes d) (n : ℕ) (u : ℝ) (η : Sizes.SeqΩ sz)
    (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (a c : Idx d (sz.L n) (sz.W n)) :
    (Sizes.seqHflow sz n u η * M) a c
      = ∑ p ∈ usedCoords d (sz.L n) (sz.W n), (Real.sqrt u : ℂ)
          * ((η (crd sz n p) : ℂ) * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2 * M) a c) := by
  rw [GreenDeriv_seqHflow_eq_realSmul, GreenDeriv_seqXmat_eq_sum, Matrix.smul_mul,
    Finset.sum_mul]
  simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.sum_apply, Complex.real_smul,
    Finset.mul_sum]

/-- `(H_u G)_{ac}` is tame (RBM1D `tame_Hflow_mul_green_apply`, `IBP:971`). -/
theorem tame_Hflow_mul_green_apply (hE : |E| < 2) (ht : t < 1) (u : ℝ)
    (a c : Idx d (sz.L n) (sz.W n)) :
    Tame sz (fun η : Sizes.SeqΩ sz =>
      (Sizes.seqHflow sz n u η * green (Sizes.seqHflow sz n u η) (zt E t)) a c) := by
  have hfun : (fun η : Sizes.SeqΩ sz =>
      (Sizes.seqHflow sz n u η * green (Sizes.seqHflow sz n u η) (zt E t)) a c)
      = fun η : Sizes.SeqΩ sz => ∑ p ∈ usedCoords d (sz.L n) (sz.W n), (Real.sqrt u : ℂ)
          * ((η (crd sz n p) : ℂ) * (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow sz n u η) (zt E t)) a c) := by
    funext η
    exact Hflow_mul_apply_eq_sum sz n u η _ a c
  rw [hfun]
  exact Tame.sum _ fun p _ => (Tame.const (sz := sz) (Real.sqrt u : ℂ)).mul
    ((Tame.coord (crd sz n p)).mul
      (tame_const_mul_green_apply hE ht u (Bmat d (sz.L n) (sz.W n) p.1 p.2.1 p.2.2) a c))

/-- `E_k` is additive on tame functions (RBM1D `condRow_tame_add`, `IBP:984`). -/
theorem condRow_tame_add (k : Idx d (sz.L n) (sz.W n))
    {X Y : Sizes.SeqΩ sz → ℂ} (hX : Tame sz X) (hY : Tame sz Y) (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => X η + Y η) ω = condRow sz n k X ω + condRow sz n k Y ω := by
  simp only [condRow_apply]
  exact integral_add ((hX.comp_rowSplit k ω).integrable (gaussIBP sz))
    ((hY.comp_rowSplit k ω).integrable (gaussIBP sz))

/-- `E_k` is subtractive on tame functions (RBM1D `condRow_tame_sub`, `IBP:991`). -/
theorem condRow_tame_sub (k : Idx d (sz.L n) (sz.W n))
    {X Y : Sizes.SeqΩ sz → ℂ} (hX : Tame sz X) (hY : Tame sz Y) (ω : Sizes.SeqΩ sz) :
    condRow sz n k (fun η => X η - Y η) ω = condRow sz n k X ω - condRow sz n k Y ω := by
  simp only [condRow_apply]
  exact integral_sub ((hX.comp_rowSplit k ω).integrable (gaussIBP sz))
    ((hY.comp_rowSplit k ω).integrable (gaussIBP sz))

/-- **The row sums of the variance profile are `1`** (RBM1D `sum_Sblk_row`,
`Green/EntryBound.lean:1012`; RBM2D `IBP_sum_svar_row`, `IBP:1180`), for `3 ≤ L`:
`∑_k S_{ik} = ∑_b S^{(B)}_{ab} = 1`.  This is the one statement of the file whose proof changes
with `d`: RBM2D reads `svar` as the real form of the paper's covariance `Spaper`
(`svar_cast_eq_Spaper`, `RBM.sum_Spaper_row`, five distinct residues of `sbSupport L`); here the
fibre of `split` has `W^d` points per block, `W^{-d} · W^d = 1`, and the block row sum is
`sum_sbKernelR` (`Defs/Block.lean`, `a + 2 d g² a = 1`, which needs `3 ≤ L`).  The proof is the
one of the private `RBM.Green.sum_svarF_row` (`Green/RowIndep.lean:1520`). -/
theorem IBP_sum_svarF_row {L W : ℕ} [NeZero L] [NeZero W] (g : ℝ) (hL : 3 ≤ L)
    (i : Idx d L W) : ∑ k : Idx d L W, svarF d L W g i k = 1 := by
  have h1 : ∑ k : Idx d L W, svarF d L W g i k
      = ∑ p : Vtx d L W, ((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 p.1 :=
    Fintype.sum_equiv (splitEquiv d L W) _ _ fun k => rfl
  have h2 : ∑ b, SBR d L g (split d L W i).1 b = 1 := by
    rw [← sum_sbKernelR d L g hL]
    exact Fintype.sum_equiv (Equiv.subLeft (split d L W i).1) _ _ fun b => by simp [SBR]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hW : ((W : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  calc ∑ a : Zd d L, ((W : ℝ) ^ d) * (((W : ℝ) ^ d)⁻¹ * SBR d L g (split d L W i).1 a)
      = ∑ a : Zd d L, SBR d L g (split d L W i).1 a :=
        Finset.sum_congr rfl fun a _ => by rw [← mul_assoc, mul_inv_cancel₀ hW, one_mul]
    _ = 1 := h2

/-- **The display, exactly** (RBM1D `condExpDiag_eq_sum_Sblk`, `IBP:1003`; `Sblk` is `svarF`).

`E_i(G_{ii} - m) = t m ∑_k S_{ik} E_i[G_{ii}(G_{kk} - m)]`.  This is an *identity*: no error
term, no stochastic domination.  It is `green_sub_smul_one_eq` at the entry `(i,i)`, the
conditional row integration by parts `condRow_Hflow_mul_green_diag`, and `∑_k S_{ik} = 1`
(`IBP_sum_svarF_row`, which needs `3 ≤ L`, given by `sz.three_le_L n`). -/
theorem condExpDiag_eq_sum_Sblk (hE : |E| < 2) (hE2 : |E| ≤ 2)
    (ht0 : 0 ≤ t) (ht : t < 1) (i : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    condExpDiag sz n t (zt E t) (mE E) i ω
      = (t : ℂ) * mE E * ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
              * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω := by
  classical
  have hz := zt_im_ne_zero_of_lt_one (E := E) (t := t) hE ht
  -- the algebraic identity at the entry `(i, i)`
  have hpt : ∀ η : Sizes.SeqΩ sz,
      greenDiagCentered sz n t (zt E t) (mE E) i η
      = (-(mE E)) * (Sizes.seqHflow sz n t η
          * green (Sizes.seqHflow sz n t η) (zt E t)) i i
        + (-((t : ℂ) * mE E ^ 2)) * green (Sizes.seqHflow sz n t η) (zt E t) i i := by
    intro η
    have h := green_sub_smul_one_eq (Sizes.seqHflow_isHermitian sz n t η) hE2 hz
    have hij := congrFun (congrFun h i) i
    rw [sub_smul_one_apply, ite_eq_left rfl] at hij
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.sub_mul, Matrix.neg_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul] at hij
    change green (Sizes.seqHflow sz n t η) (zt E t) i i - mE E = _
    rw [hij]
    ring
  -- `E_i` is linear
  have htame1 : Tame sz
      (fun η : Sizes.SeqΩ sz => (-(mE E)) * (Sizes.seqHflow sz n t η
        * green (Sizes.seqHflow sz n t η) (zt E t)) i i) :=
    (Tame.const (sz := sz) (-(mE E))).mul (tame_Hflow_mul_green_apply hE ht t i i)
  have htame2 : Tame sz
      (fun η : Sizes.SeqΩ sz => (-((t : ℂ) * mE E ^ 2))
        * green (Sizes.seqHflow sz n t η) (zt E t) i i) :=
    (Tame.const (sz := sz) (-((t : ℂ) * mE E ^ 2))).mul (tame_green_apply hE ht t i i)
  have hlin : condExpDiag sz n t (zt E t) (mE E) i ω
      = (-(mE E)) * condRow sz n i
          (fun η => (Sizes.seqHflow sz n t η
            * green (Sizes.seqHflow sz n t η) (zt E t)) i i) ω
        + (-((t : ℂ) * mE E ^ 2)) * condRow sz n i
          (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i) ω := by
    change condRow sz n i (greenDiagCentered sz n t (zt E t) (mE E) i) ω = _
    have : (greenDiagCentered sz n t (zt E t) (mE E) i)
        = fun η => (-(mE E)) * (Sizes.seqHflow sz n t η
            * green (Sizes.seqHflow sz n t η) (zt E t)) i i
          + (-((t : ℂ) * mE E ^ 2))
            * green (Sizes.seqHflow sz n t η) (zt E t) i i := funext hpt
    rw [this, condRow_tame_add i htame1 htame2, condRow_const_mul, condRow_const_mul]
  rw [hlin, condRow_Hflow_mul_green_diag hE ht ht0 i ω]
  -- `∑_k S_ik = 1` turns the lone `E_i[G_ii]` into a row sum
  have hrow : ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, IBP_sum_svarF_row (sz.lam n) (sz.three_le_L n) i, Complex.ofReal_one]
  have hsplit : ∀ k : Idx d (sz.L n) (sz.W n),
      condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
          * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
        = condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
            * green (Sizes.seqHflow sz n t η) (zt E t) k k) ω
          - mE E * condRow sz n i
            (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i) ω := by
    intro k
    have hA : Tame sz (fun η : Sizes.SeqΩ sz => green (Sizes.seqHflow sz n t η) (zt E t) i i
        * green (Sizes.seqHflow sz n t η) (zt E t) k k) :=
      (tame_green_apply hE ht t i i).mul (tame_green_apply hE ht t k k)
    have hB : Tame sz (fun η : Sizes.SeqΩ sz =>
        mE E * green (Sizes.seqHflow sz n t η) (zt E t) i i) :=
      (Tame.const (sz := sz) (mE E)).mul (tame_green_apply hE ht t i i)
    have hfun : (fun η : Sizes.SeqΩ sz => green (Sizes.seqHflow sz n t η) (zt E t) i i
        * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E))
        = fun η : Sizes.SeqΩ sz => green (Sizes.seqHflow sz n t η) (zt E t) i i
            * green (Sizes.seqHflow sz n t η) (zt E t) k k
          - mE E * green (Sizes.seqHflow sz n t η) (zt E t) i i := by
      funext η; ring
    rw [hfun, condRow_tame_sub i hA hB, condRow_const_mul]
  have hsum : ∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
        * condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
            * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
      = (∑ k, (svarF d (sz.L n) (sz.W n) (sz.lam n) i k : ℂ)
          * condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
              * green (Sizes.seqHflow sz n t η) (zt E t) k k) ω)
        - mE E * condRow sz n i
          (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i) ω := by
    simp only [hsplit]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hrow, one_mul]
  rw [hsum]
  ring

end CondDisplay

/-! ### Step 4: the remainder `ibpRem`

What is left is the difference between the identity of step 3 and the shape the
fluctuation-averaging step asks for.  It is isolated as `ibpRem`; the paper bounds it by `Ψ²`
in two pieces (`ibpRem_eq_add`).  The `≺` bookkeeping is not part of this file. -/

section Remainder

variable {sz : Sizes d} {n : ℕ} {E t : ℝ}

/-- **The remainder of the display** at the pair `(i, k)` (RBM1D `ibpRem`, `IBP:1100`):

  `E_i[G_{ii}(G_{kk} - m)] - m(G_{kk} - m)`.

This is the *only* thing between the identity `condExpDiag_eq_sum_Sblk` and the paper's
`t m² ∑_k S_ik (G_kk - m) + O≺(Ψ²)`.  The paper bounds it by `Ψ²` in two pieces
(`ibpRem_eq_add`): `E_i[(G_{ii}-m)(G_{kk}-m)]`, a product of two `Ψ`'s, and
`m(E_i(G_{kk}-m) - (G_{kk}-m))`, the minor-replacement error. -/
noncomputable def ibpRem (sz : Sizes d) (n : ℕ) (E t : ℝ)
    (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) : ℂ :=
  condRow sz n q.1 (fun η => green (Sizes.seqHflow sz n t η) (zt E t) q.1 q.1
      * (green (Sizes.seqHflow sz n t η) (zt E t) q.2 q.2 - mE E)) ω
    - mE E * (green (Sizes.seqHflow sz n t ω) (zt E t) q.2 q.2 - mE E)

/-- **The remainder splits into the paper's two `Ψ²` inputs** (RBM1D `ibpRem_eq_add`,
`IBP:1111`).

`E_i[G_{ii}(G_{kk}-m)] - m(G_{kk}-m) = E_i[(G_{ii}-m)(G_{kk}-m)] + m(E_i(G_{kk}-m) - (G_{kk}-m))`.

The first summand is a product of two entries of `G - m`; the second is the minor-replacement
error (RBM1D `Gauss/MinorReplace.lean`), since `G^{(i)}_{kk}` is `E_i`-invariant. -/
theorem ibpRem_eq_add (hE : |E| < 2) (ht : t < 1)
    (i k : Idx d (sz.L n) (sz.W n)) (ω : Sizes.SeqΩ sz) :
    ibpRem sz n E t (i, k) ω
      = condRow sz n i (fun η => (green (Sizes.seqHflow sz n t η) (zt E t) i i
            - mE E)
          * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
        + mE E * (condRow sz n i
            (greenDiagCentered sz n t (zt E t) (mE E) k) ω
          - (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E)) := by
  have hA : Tame sz (fun η : Sizes.SeqΩ sz =>
      (green (Sizes.seqHflow sz n t η) (zt E t) i i - mE E)
      * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) :=
    ((tame_green_apply hE ht t i i).sub (Tame.const _)).mul
      ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hB : Tame sz (fun η : Sizes.SeqΩ sz => mE E
      * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) :=
    (Tame.const (sz := sz) (mE E)).mul ((tame_green_apply hE ht t k k).sub (Tame.const _))
  have hfun : (fun η : Sizes.SeqΩ sz => green (Sizes.seqHflow sz n t η) (zt E t) i i
      * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E))
      = fun η : Sizes.SeqΩ sz => (green (Sizes.seqHflow sz n t η) (zt E t) i i
          - mE E)
          * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)
        + mE E * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E) := by
    funext η
    ring
  have hgdc : (fun η : Sizes.SeqΩ sz => mE E
      * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E))
      = fun η : Sizes.SeqΩ sz => mE E
        * greenDiagCentered sz n t (zt E t) (mE E) k η := rfl
  change condRow sz n i (fun η => green (Sizes.seqHflow sz n t η) (zt E t) i i
      * (green (Sizes.seqHflow sz n t η) (zt E t) k k - mE E)) ω
      - mE E * (green (Sizes.seqHflow sz n t ω) (zt E t) k k - mE E) = _
  rw [hfun, condRow_tame_add i hA hB, hgdc, condRow_const_mul]
  ring

end Remainder

/-! ### Checks: a compiled nonempty instance of every target

The data: the size sequence `ckS` (`d = 3`, `L n = 3`, `W n = 2`, `lam n = 1/2`), the slice
`n = 0` (`N = (W L)^d = 216` sites `Idx 3 3 2`, blocks of `W^d = 8` fine sites, diagonal variance
`svarF = W^{-d} (1 + 2 d g²)⁻¹ = 1/20`), `E = 1/2` (`|E| = 1/2 < 2`), `t = u = 1/2`
(`t ∈ [0, 1)`, `Im z_t = (1 - t) √(4 - E²)/2 ≈ 0.484 > 0`), and the sites `x0 = (0,0,0)`,
`x1 = (1,0,0)`, `x2 = (0,1,0)` of `Z_6^3`.  No target takes `GaussIBP` (it is the theorem
`gaussIBP`), so no hypothesis of any target is left open. -/

section Checks

noncomputable section

set_option maxRecDepth 100000

private def ckS : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 2
  lam := fun _ => 1 / 2
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => by norm_num

private abbrev ckI : Type := Idx 3 (ckS.L 0) (ckS.W 0)

private def ckx0 : ckI := fun _ => 0
private def ckx1 : ckI := Pi.single 0 1
private def ckx2 : ckI := Pi.single 1 1

/-- The diagonal coordinates `(x, x, true)` at the sites `x0` and `x1`. -/
private abbrev ckp0 : CoordF 3 (ckS.L 0) (ckS.W 0) := (ckx0, ckx0, true)
private abbrev ckp1 : CoordF 3 (ckS.L 0) (ckS.W 0) := (ckx1, ckx1, true)

private theorem ck_hE : |(1 / 2 : ℝ)| < 2 := by norm_num
private theorem ck_hE2 : |(1 / 2 : ℝ)| ≤ 2 := by norm_num
private theorem ck_ht : (1 / 2 : ℝ) < 1 := by norm_num
private theorem ck_ht0 : (0 : ℝ) ≤ 1 / 2 := by norm_num

private theorem ckp0_used : ckp0 ∈ usedCoords 3 (ckS.L 0) (ckS.W 0) := by
  rw [GreenDeriv_mem_usedCoords]
  exact Or.inr ⟨rfl, rfl⟩

private theorem ckp1_used : ckp1 ∈ usedCoords 3 (ckS.L 0) (ckS.W 0) := by
  rw [GreenDeriv_mem_usedCoords]
  exact Or.inr ⟨rfl, rfl⟩

/-- The three sites are distinct (`Z_6^3`: `0 ≠ 1` in `ZMod 6`). -/
private theorem ck_x01 : ckx0 ≠ ckx1 := by
  intro h
  have := congrFun h 0
  simp only [ckx0, ckx1, Pi.single_eq_same] at this
  change (0 : ZMod 6) = 1 at this
  exact absurd this (by decide)

private theorem ck_x20 : ckx2 ≠ ckx0 := by
  intro h
  have := congrFun h 1
  simp only [ckx0, ckx2, Pi.single_eq_same] at this
  change (1 : ZMod 6) = 0 at this
  exact absurd this (by decide)

private theorem ck_x21 : ckx2 ≠ ckx1 := by
  intro h
  have := congrFun h 1
  simp only [ckx1, ckx2, Pi.single_eq_same, Pi.single_apply] at this
  change (1 : ZMod 6) = if (1 : Fin 3) = 0 then 1 else 0 at this
  exact absurd this (by decide)

/-- An off-diagonal used coordinate exists: `x0 ≠ x1`, and one of the two orientations is used
(`idxKey` orders them). -/
private theorem ck_offDiag :
    ∃ p : CoordF 3 (ckS.L 0) (ckS.W 0), p ∈ usedCoords 3 (ckS.L 0) (ckS.W 0) ∧ p.1 ≠ p.2.1 := by
  rcases idxKey_lt_or_eq_or_lt 3 (ckS.L 0) (ckS.W 0) ckx0 ckx1 with h | h | h
  · refine ⟨(ckx0, ckx1, true), ?_, ck_x01⟩
    rw [GreenDeriv_mem_usedCoords]
    exact Or.inl h
  · exact absurd h ck_x01
  · refine ⟨(ckx1, ckx0, true), ?_, ck_x01.symm⟩
    rw [GreenDeriv_mem_usedCoords]
    exact Or.inl h

/-- **T-A**: the coordinate derivatives of `H_u`, `G`, `G_{ab}` and `(B G)_{ac}` at `p = (x,x,true)`
and at an off-diagonal used coordinate. -/
example (ω : Sizes.SeqΩ ckS) := hasDerivAt_Hflow_update ckS 0 (1 / 2) ω ckp0_used

example (ω : Sizes.SeqΩ ckS) :=
  hasDerivAt_green_Hflow_update ckS 0 (1 / 2) (z := zt (1 / 2) (1 / 2))
    (zt_im_ne_zero_of_lt_one ck_hE ck_ht) ω ckp0_used

example (ω : Sizes.SeqΩ ckS) :=
  hasDerivAt_green_apply_update ckS 0 (1 / 2) (z := zt (1 / 2) (1 / 2))
    (zt_im_ne_zero_of_lt_one ck_hE ck_ht) ω ckp0_used ckx0 ckx1

example (ω : Sizes.SeqΩ ckS) :=
  hasDerivAt_const_mul_green_apply_update ckS 0 (1 / 2) (z := zt (1 / 2) (1 / 2))
    (zt_im_ne_zero_of_lt_one ck_hE ck_ht) ω ckp0_used
    (Bmat 3 (ckS.L 0) (ckS.W 0) ckx0 ckx1 true) ckx0 ckx2

example (ω : Sizes.SeqΩ ckS) : ∃ p ∈ usedCoords 3 (ckS.L 0) (ckS.W 0), p.1 ≠ p.2.1 ∧
    HasDerivAt (fun s : ℝ => Sizes.seqHflow ckS 0 (1 / 2) (Function.update ω (crd ckS 0 p) s))
      (Real.sqrt (1 / 2) • Bmat 3 (ckS.L 0) (ckS.W 0) p.1 p.2.1 p.2.2) (ω (crd ckS 0 p)) := by
  obtain ⟨p, hp, hne⟩ := ck_offDiag
  exact ⟨p, hp, hne, hasDerivAt_Hflow_update ckS 0 (1 / 2) ω hp⟩

/-- **T-B**: the five families of entries are tame at `E = t = 1/2`, `u = 1/2`. -/
example := tame_green_apply (sz := ckS) (n := 0) (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2)
  ckx0 ckx1

example := tame_green_mul_mul_green_apply (sz := ckS) (n := 0) (E := 1 / 2) (t := 1 / 2) ck_hE
  ck_ht (1 / 2) (Bmat 3 (ckS.L 0) (ckS.W 0) ckx0 ckx1 true) ckx0 ckx1

example := tame_const_mul_green_apply (sz := ckS) (n := 0) (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht
  (1 / 2) (Bmat 3 (ckS.L 0) (ckS.W 0) ckx0 ckx1 true) ckx0 ckx2

example := tame_const_mul_sandwich_apply (sz := ckS) (n := 0) (E := 1 / 2) (t := 1 / 2) ck_hE
  ck_ht (1 / 2) (Bmat 3 (ckS.L 0) (ckS.W 0) ckx0 ckx1 true) ckx0 ckx2

example := tame_Hflow_mul_green_apply (sz := ckS) (n := 0) (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht
  (1 / 2) ckx0 ckx1

/-- **T-C**: Stein's identity for `G_{ab}` and for `(B_p G)_{aa}`. -/
example := integral_coord_mul_green_apply (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS)
  ck_hE ck_ht (1 / 2) ckp0_used ckx0 ckx1

example := integral_coord_mul_Bmat_mul_green_diag (n := 0) (E := 1 / 2) (t := 1 / 2)
  (sz := ckS) ck_hE ck_ht (1 / 2) ckp0_used ckx0

example : ∃ p ∈ usedCoords 3 (ckS.L 0) (ckS.W 0), p.1 ≠ p.2.1 ∧
    ∫ ω, (ω (crd ckS 0 p) : ℂ) * green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))
        ckx0 ckx0 ∂(Sizes.seqP ckS)
      = (Sizes.seqGvar ckS (crd ckS 0 p) : ℝ) * ∫ ω, -((Real.sqrt (1 / 2) : ℂ)
          * (green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))
            * Bmat 3 (ckS.L 0) (ckS.W 0) p.1 p.2.1 p.2.2
            * green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))) ckx0 ckx0)
          ∂(Sizes.seqP ckS) := by
  obtain ⟨p, hp, hne⟩ := ck_offDiag
  exact ⟨p, hp, hne, integral_coord_mul_green_apply (n := 0) (E := 1 / 2) (t := 1 / 2)
    (sz := ckS) ck_hE ck_ht (1 / 2) hp ckx0 ckx0⟩

/-- **T-D**: the sandwich algebra for the resolvent at the data, and for an arbitrary
non-symmetric complex matrix (the third example). -/
example (ω : Sizes.SeqΩ ckS) :=
  sum_gvar_Bmat_sandwich_diag ckS 0
    (green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))) ckx0

example (ω : Sizes.SeqΩ ckS) :=
  sum_gvar_Bmat_sandwich_diag_mul ckS 0
    (green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))) ckx0

example :=
  sum_gvar_Bmat_sandwich_diag ckS 0 (Matrix.of fun i j : ckI => ((i 0).val : ℂ) + 2 * (j 1).val)
    ckx1

/-- **T-E**: the `condRow` algebra.  `E_k[ω_c ω_c] = gvarF_c E_k[1]` (the variance identity) for
the row-`k` coordinate `c = crd (x,x,true)`, `k = x`: `condRow_coord_mul` with `g = ω_c`,
`g' = 1`. -/
example (ω : Sizes.SeqΩ ckS) :
    condRow ckS 0 ckx0 (fun η => (η (crd ckS 0 ckp0) : ℂ) * (η (crd ckS 0 ckp0) : ℂ)) ω
      = (Sizes.seqGvar ckS (crd ckS 0 ckp0) : ℝ) * condRow ckS 0 ckx0 (fun _ => (1 : ℂ)) ω :=
  condRow_coord_mul (n := 0) (sz := ckS) ckx0
    ((isRowCoord_mk ckS 0 ckx0 ckx0 ckx0 true).2 (Or.inl rfl))
    (fun η => (η (crd ckS 0 ckp0) : ℂ)) (fun _ => (1 : ℂ)) (Tame.coord _) (Tame.const _)
    (fun η => by simpa using (hasDerivAt_id (η (crd ckS 0 ckp0))).ofReal_comp) ω

/-- Linearity of `E_k` at the data: constants, negation, `0`, `+`, `-`, finite sums. -/
example (ω : Sizes.SeqΩ ckS) :=
  condRow_const_mul (sz := ckS) (n := 0) ckx0 (mE (1 / 2))
    (fun η => green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx0 ckx0) ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_neg_const_mul (sz := ckS) (n := 0) ckx0 (mE (1 / 2))
    (fun η => green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx0 ckx0) ω

example (ω : Sizes.SeqΩ ckS) := condRow_zero_apply (sz := ckS) (n := 0) ckx0 ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_tame_add (n := 0) (sz := ckS) ckx0
    (tame_green_apply (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2) ckx0 ckx0)
    (tame_green_apply (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2) ckx1 ckx1) ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_tame_sub (n := 0) (sz := ckS) ckx0
    (tame_green_apply (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2) ckx0 ckx0)
    (tame_green_apply (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2) ckx1 ckx1) ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_finsetSum (n := 0) (sz := ckS) ckx0 (Finset.univ : Finset ckI)
    (fun k η => green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) k k)
    (fun k _ => tame_green_apply (E := 1 / 2) (t := 1 / 2) ck_hE ck_ht (1 / 2) k k) ω

/-- `(B_p M)_{kk} = 0` for `k = x2` and `p = (x0, x1, b)`, `k ∉ {p.1, p.2.1}`. -/
example (M : Matrix ckI ckI ℂ) :=
  Bmat_mul_apply_diag_of_ne (x := ckx0) (y := ckx1) (i := ckx2) ck_x20 ck_x21 true M

/-- **T-F**: `E_i[ω_p (B_p G)_{ii}]` for a row-`i` coordinate (`p = (x,x,true)`, `i = x`) and for a
coordinate off row `i` (`p = (x',x',true)`, `i = x`, both sides vanish); then the whole row
`E_i[(H_u G)_{ii}] = -u Σ_k svarF(i,k) E_i[G_{ii} G_{kk}]` at `u = 1/2`. -/
example (ω : Sizes.SeqΩ ckS) :=
  condRow_coord_mul_Bmat_mul_green_diag (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS)
    ck_hE ck_ht (1 / 2) ckp0_used ckx0 ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_coord_mul_Bmat_mul_green_diag (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS)
    ck_hE ck_ht (1 / 2) ckp1_used ckx0 ω

example (ω : Sizes.SeqΩ ckS) :=
  condRow_Hflow_mul_green_diag (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht
    (u := 1 / 2) ck_ht0 ckx0 ω

example (ω : Sizes.SeqΩ ckS) : True := by
  obtain ⟨p, hp, _⟩ := ck_offDiag
  have _h := condRow_coord_mul_Bmat_mul_green_diag (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS)
    ck_hE ck_ht (1 / 2) hp ckx0 ω
  trivial

/-- **T-G**: `condExpDiag_eq_sum_Sblk` at `d = 3`, `L = 3`, `W = 2`, `lam = 1/2`,
`E = t = 1/2`, `i = x0`, for every `ω`. -/
example (ω : Sizes.SeqΩ ckS) :
    condExpDiag ckS 0 (1 / 2) (zt (1 / 2) (1 / 2)) (mE (1 / 2)) ckx0 ω
      = ((1 / 2 : ℝ) : ℂ) * mE (1 / 2) * ∑ k : ckI, (svarF 3 3 2 (1 / 2) ckx0 k : ℂ)
          * condRow ckS 0 ckx0 (fun η =>
              green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx0 ckx0
              * (green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) k k
                - mE (1 / 2))) ω :=
  condExpDiag_eq_sum_Sblk (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_hE2 ck_ht0
    ck_ht ckx0 ω

/-- **T-H**: the remainder unfolds to its definition and splits into the two `Ψ²` inputs, at an
off-diagonal pair and at the diagonal pair. -/
example (ω : Sizes.SeqΩ ckS) :
    ibpRem ckS 0 (1 / 2) (1 / 2) (ckx0, ckx1) ω
      = condRow ckS 0 ckx0 (fun η =>
          green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx0 ckx0
          * (green (Sizes.seqHflow ckS 0 (1 / 2) η) (zt (1 / 2) (1 / 2)) ckx1 ckx1
            - mE (1 / 2))) ω
        - mE (1 / 2) * (green (Sizes.seqHflow ckS 0 (1 / 2) ω) (zt (1 / 2) (1 / 2))
          ckx1 ckx1 - mE (1 / 2)) := rfl

example (ω : Sizes.SeqΩ ckS) :=
  ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx1 ω

example (ω : Sizes.SeqΩ ckS) :=
  ibpRem_eq_add (n := 0) (E := 1 / 2) (t := 1 / 2) (sz := ckS) ck_hE ck_ht ckx0 ckx0 ω

/-- The ingredient `G - m = m(-H - tm)G` of `condExpDiag_eq_sum_Sblk`, for the Hermitian
`H = H_{1/2}(ω)`. -/
example (ω : Sizes.SeqΩ ckS) :=
  green_sub_smul_one_eq (Sizes.seqHflow_isHermitian ckS 0 (1 / 2) ω) ck_hE2
    (zt_im_ne_zero_of_lt_one ck_hE ck_ht)

/-- **The factor `t` in `G - m = m(-H - tm)G` is needed.**  The form without it,
`G_u - m = -m (H_u + m) G_u`, is false for `u < 1`: at `u = 0` (where `H_0 = 0`, `G_0 = m`) and
`E = 0` its left side is `0` and its right side is `-m³ ≠ 0`, for every `ω`.  The corrected
identity is `green_sub_smul_one_eq`.  (The `d ≥ 3` paper does not state this identity; the
check is the dimension-free algebra behind the `t`.) -/
example (ω : Sizes.SeqΩ ckS) :
    ¬ (green (Sizes.seqHflow ckS 0 0 ω) (zt 0 0) - mE 0 • (1 : Matrix ckI ckI ℂ)
      = mE 0 • ((-Sizes.seqHflow ckS 0 0 ω - mE 0 • (1 : Matrix ckI ckI ℂ))
          * green (Sizes.seqHflow ckS 0 0 ω) (zt 0 0))) := by
  intro h
  have hm2 : mE 0 * mE 0 = -1 := by
    have := mE_mul (E := 0) (by norm_num)
    simpa using this
  have h0 : Sizes.seqHflow ckS 0 0 ω = 0 := by simp [Sizes.seqHflow]
  rw [h0] at h
  have hR : mE 0 • ((-(0 : Matrix ckI ckI ℂ) - mE 0 • (1 : Matrix ckI ckI ℂ))
      * green (0 : Matrix ckI ckI ℂ) (zt 0 0)) = green (0 : Matrix ckI ckI ℂ) (zt 0 0) := by
    rw [neg_zero, zero_sub, neg_mul, Matrix.smul_mul, Matrix.one_mul, smul_neg, smul_smul, hm2]
    simp
  rw [hR] at h
  have h1 : mE 0 • (1 : Matrix ckI ckI ℂ) = 0 := sub_eq_self.mp h
  have h2 : mE 0 = 0 := by
    have := congrFun (congrFun h1 ckx0) ckx0
    simpa using this
  have h3 := mE_im_pos (E := 0) (by norm_num)
  rw [h2, Complex.zero_im] at h3
  exact lt_irrefl _ h3

/-- **Nondegeneracy of the data**: the row sum `Σ_k svarF(i,k) = 1` at `L = 3`, `W = 2`,
`g = 1/2` (`IBP_sum_svarF_row`), the diagonal weight `svarF(i,i) = W^{-d}(1 + 2dg²)⁻¹ = 1/20`,
`216` sites, and a positive variance `gvarF = svarF_xx = 1/20` of the coordinate of the checks. -/
example : ∑ k : ckI, svarF 3 (ckS.L 0) (ckS.W 0) (ckS.lam 0) ckx0 k = 1 :=
  IBP_sum_svarF_row (ckS.lam 0) (ckS.three_le_L 0) ckx0

example : svarF 3 (ckS.L 0) (ckS.W 0) (ckS.lam 0) ckx0 ckx0 = 1 / 20 := by
  have hW : ckS.W 0 = 2 := rfl
  have hl : ckS.lam 0 = 1 / 2 := rfl
  rw [svarF_diag, hW, hl]
  norm_num

example : Fintype.card ckI = 216 := by
  rw [Sizes.card_Idx ckS 0]
  rfl

example : (Sizes.seqGvar ckS (crd ckS 0 ckp0) : ℝ) = 1 / 20 := by
  have hW : ckS.W 0 = 2 := rfl
  have hl : ckS.lam 0 = 1 / 2 := rfl
  change (gvarF 3 (ckS.L 0) (ckS.W 0) (ckS.lam 0) (ckx0, ckx0, true) : ℝ) = 1 / 20
  rw [IBP_gvarF_eq]
  simp only [ite_true]
  rw [svarF_diag, hW, hl]
  norm_num

end

end Checks

end RBM.Green
