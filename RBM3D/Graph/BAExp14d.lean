/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAAtom2
import RBM3D.Graph.BAExp14aB
import RBM3D.Graph.BAG5Leaf
import RBM3D.Graph.LWExpTerm3

/-!
# The `t`-scaling, `GtoAG` at the rescaled kernels without `hext`, and the `q ≤ 1` bound (part A)

Paper: Subappendix B.1: (B.5) `eq;I42inG`, (B.7) `Gammamuxy` (`GtoAG` and Cauchy-Schwarz); (B.22)
`eq:Gbyxi2_BA`; (B.25) `G_by_auxG_BA`.  This is the BA counterpart of the band file
`Graph/LWExpTerm3.lean` (Section 3: `AuxBound`, `SpDecay`, `Pathwise`, `PrecPieces`, `Arith`,
`Arith2`, `Arith3`, and `LwGraphPrec1`, `lwGraphPrec1`).  Part B is `Graph/BAExp14dB.lean`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAExp14d_`)

1. **The rescaled data** `BAExp14d_dataT` (`S' = S/t`, `S⁺' = lift(ω_t)`,
   `ω_t = Θ_t^{(+,+)}`) and the exact `t`-scaling `BAExp14d_val_scale` (every waved factor of
   `BAlwData` is `t` times that of `BAExp14d_dataT`, `baSp_eq`).
2. **`GtoAG` at the rescaled kernels without `hext`** `BAGtoAGT`, `baGtoAGT_holds`: the hypothesis
   `hext` (distinct external vertices in distinct molecules) is not needed, with the kernel
   constants of `S'` and `lift(ω_t)` uniform in `0 ≤ t < 1`.
3. **The deterministic `q ≤ 1` bound** `BAExp14d_det` (private; as `lwExpTerm3_det`).

The band proofs (private lemmas `lwExpTerm3_auxVal_zero`, `_one`) are reused by `open private`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open private lwExpTerm3_auxVal_zero lwExpTerm3_auxVal_one from RBM3D.Graph.LWExpTerm3
open private BASizeClaim_theta_decay from RBM3D.Graph.BASizeClaim

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The rescaled data and the `t`-scaling -/

section Scale

/-- The rescaled data `D'_t` (`S' = svarF(0)`, `S = t S'` by `BAlwS`; `S⁺' = lift(ω_t)`, `S⁺ = S W = t lift(ω_t)` by `baSp_eq`,
`Graph/BASizeClaim.lean`): `G`, `M`, `g₀Ψ` are those of `BAlwData`. -/
def BAExp14d_dataT (d L W : ℕ) [NeZero L] [NeZero W] (g0 E t : ℝ) (m : ℂ) (ω : Ω d L W) : BALData (Idx d L W) :=
  { G := Matrix.of fun x y => BAlwG d L W g0 E t m ω x y,
    M := BAlwM d L W g0 E m,
    S := Matrix.of fun x y => ((svarF d L W 0 x y : ℝ) : ℂ),
    Sp := lwLift d L W (BATheta d L g0 E m t true true),
    gPsi := (g0 : ℂ) • PsiI d L W }

private theorem BAExp14d_wedge_val {ι V : Type*} (D D' : BALData ι) (t : ℝ) (hS : ∀ x y, D.S x y = (t : ℂ) * D'.S x y)
    (hSp : ∀ x y, D.Sp x y = (t : ℂ) * D'.Sp x y) (ℓ : V → ι) (e : WEdge V) :
    WEdge.val D.toLData ℓ e = (t : ℂ) * WEdge.val D'.toLData ℓ e := by
  unfold WEdge.val
  split_ifs
  · exact hSp _ _
  · rw [hSp, star_mul', Complex.star_def, Complex.conj_ofReal]
  · exact hS _ _

private theorem BAExp14d_prod_scale {α : Type*} (l : List α) (f g : α → ℂ) (t : ℂ) (h : ∀ a, f a = t * g a) :
    (l.map f).prod = t ^ l.length * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.prod_cons, List.length_cons, h, ih, pow_succ]; ring

/-- Every waved factor of `D` is `t` times that of `D'`, `G`, `M`, `g₀Ψ` agree: the term is `t^{n_W}` times the term. -/
private theorem BAExp14d_term_scale {ι E I : Type} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (D D' : BALData ι) (t : ℝ) (hS : ∀ x y, D.S x y = (t : ℂ) * D'.S x y) (hSp : ∀ x y, D.Sp x y = (t : ℂ) * D'.Sp x y)
    (hG : D.G = D'.G) (hM : D.M = D'.M) (hP : D.gPsi = D'.gPsi) (ℓ : E ⊕ I → ι) :
    Γ.term D ℓ = (t : ℂ) ^ Γ.nW * Γ.term D' ℓ := by
  have hsol : ∀ e, SEdge.val D.toLData ℓ e = SEdge.val D'.toLData ℓ e := fun e => by
    simp only [SEdge.val, hG, hM]
  have hmd : ∀ e, BAMEdge.val D ℓ e = BAMEdge.val D' ℓ e := fun e => by simp only [BAMEdge.val, hM]
  have hps : ∀ e, BAPsiEdge.val D ℓ e = BAPsiEdge.val D' ℓ e := fun e => by simp only [BAPsiEdge.val, hP]
  unfold BAGraph.term LGraph.term
  rw [BAExp14d_prod_scale Γ.waved _ _ (t : ℂ) (BAExp14d_wedge_val D D' t hS hSp ℓ),
    List.map_congr_left (fun e _ => hsol e), List.map_congr_left (fun e _ => hmd e),
    List.map_congr_left (fun e _ => hps e)]
  unfold BAGraph.nW
  ring

/-- **The `t`-scaling** (the BA form of the `t`-carrying constants of the band,
`lwExpTerm3_Sp_decay`, `lwExpTerm3_sizeConst_smul`): every waved factor of `BAlwData` at `t` is `t` times that of `BAExp14d_dataT`, so a
packed graph value is `t^{n_W}` times its value at `BAExp14d_dataT`, for all `0 ≤ t < 1` (`t = 0` included). -/
theorem BAExp14d_val_scale : ∀ (d L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 κ E t : ℝ) (m : ℂ), BAReal d L g0 κ E m →
    0 ≤ t → t < 1 → ∀ (ω : Ω d L W) (P : BAPGraph (Fin 2)) (ℓ : Fin 2 → Idx d L W),
      P.val (BAlwData d L W g0 E t m ω) ℓ = (t : ℂ) ^ P.g.nW * P.val (BAExp14d_dataT d L W g0 E t m ω) ℓ := by
  intro d L W _ _ hL g0 κ E t m hr ht0 ht1 ω P ℓ
  have hsp := baSp_eq d L W hL g0 κ E t m hr ht0 ht1
  have hSp : ∀ x y, (BAlwData d L W g0 E t m ω).Sp x y = (t : ℂ) * (BAExp14d_dataT d L W g0 E t m ω).Sp x y := fun x y => by
    have := congrFun (congrFun hsp x) y
    simp only [BAlwData, BAExp14d_dataT, this, Matrix.smul_apply, smul_eq_mul]
  have hS : ∀ x y, (BAlwData d L W g0 E t m ω).S x y = (t : ℂ) * (BAExp14d_dataT d L W g0 E t m ω).S x y := fun x y => by
    simp only [BAlwData, BAExp14d_dataT, Matrix.of_apply, BAlwS]
  unfold BAPGraph.val
  split_ifs with h
  · unfold BAGraph.val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ℓi _ => BAExp14d_term_scale P.g _ _ t hS hSp rfl rfl rfl _
  · simp

end Scale

/-! ## 2. `GtoAG` at the rescaled kernels, without `hext` -/

section G3

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The deterministic `GtoAG` at the BA data (the BA counterpart of `lwGtoAG_holds`, Lemma 7.21) without the hypothesis `hext` (distinct external vertices in distinct
molecules), which its proof never uses: the same statement as `BAGtoAG d`, hypotheses as binders. -/
private theorem BAExp14d_G3 (d : ℕ) (hd : 3 ≤ d) (L W : ℕ) [NeZero L] [NeZero W] (Γ : BAGraph E I) (hN : Γ.Normal)
    (D : BALData (Idx d L W)) (Ψ A K₀ K₁ Kd C c r R : ℝ) (ξ : Zd d L → Zd d L → ℝ)
    (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) (hA : 0 ≤ A) (hwin : ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2)
    (hS : LWKBound D.S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁) (hSp : LWKBound D.Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁)
    (hM : LWKBound D.M Kd Kd) (hP : LWKBound D.gPsi Kd Kd) (hC : 0 ≤ C) (hc : 0 < c)
    (hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))))
    (hoff : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0)
    (hr : 0 ≤ r) (hRr : (Fintype.card (E ⊕ I) : ℝ) * r ≤ R) (hξ0 : ∀ a b, 0 ≤ ξ a b)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) (ℓe : E → Idx d L W) :
    ‖Γ.val D ℓe‖ ≤
      Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
        Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
          Γ.scalingSize Ψ W d L := by
  classical
  have hne : Nonempty (Idx d L W) := ⟨fun _ => 0⟩
  have hΨ : 0 ≤ Ψ := (norm_nonneg _).trans (hG (fun _ => 0) (fun _ => 0))
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne W))
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := pow_pos hWpos d
  have hK₀' : 0 ≤ K₀ * ((W : ℝ) ^ d)⁻¹ := (norm_nonneg _).trans (hS.1 (fun _ => 0) (fun _ => 0))
  have hK₀ : 0 ≤ K₀ := by
    by_contra h
    push Not at h
    have : K₀ * ((W : ℝ) ^ d)⁻¹ < 0 := mul_neg_of_neg_of_pos h (inv_pos.2 hWd)
    linarith
  have : Fintype (LGraph.AuxIMol Γ.shadow) := Fintype.ofFinite _
  obtain ⟨h1, h2⟩ := Γ.counters_le hN.1
  have hmS := Γ.molSolid_length_le
  obtain ⟨root, hrootinj, hroot, hmain⟩ := BAAtom_main_sum Γ hN D hξ0 hS hSp hM hP ℓe
  have htail := BAAtom_tail_sum (r := r) hd Γ hN D hΨ hC hc hSd hSpd hMPd hoff ℓe
  have ha : K₀ * ((W : ℝ) ^ d)⁻¹ ≤ K₀ * (A * Ψ ^ 2) := mul_le_mul_of_nonneg_left hwin hK₀
  have hapow : (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤
      (K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM))) := by
    calc (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) ≤ (K₀ * (A * Ψ ^ 2)) ^ (Γ.nW - (Γ.nA - Γ.nM)) :=
          pow_le_pow_left₀ hK₀' ha _
      _ = _ := by rw [← mul_assoc, mul_pow, ← pow_mul, mul_comm 2]
  have hexp : Γ.scalingOrder - Γ.auxOrd =
      (((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM)) : ℕ) : ℤ) := by
    rw [Γ.scalingOrder_sub_auxOrd]
    unfold BAGraph.nS BAGraph.nW at *
    omega
  rw [hexp, zpow_natCast]
  have hav0 := Γ.auxVal_nonneg ξ hξ0 (fun a => (split d L W (ℓe a)).1)
  have hK₁ : 0 ≤ K₁ := (Finset.sum_nonneg fun y _ => norm_nonneg _).trans (hS.2.1 (fun _ => 0))
  have hKd : 0 ≤ Kd := (norm_nonneg _).trans (hM.1 (fun _ => 0) (fun _ => 0))
  have hmain' : ∑ ℓi : I → Idx d L W, ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) ≤
      Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ ((Γ.nS - Γ.shadow.molSolid.length) + 2 * (Γ.nW - (Γ.nA - Γ.nM))) *
        (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) := by
    rw [← Finset.mul_sum]
    have hcn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) := by positivity
    calc ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) * ∑ ℓi : I → Idx d L W,
          ((Γ.shadow.molSolid.map fun e => ξ
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
              (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
            ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))
        ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            (K₁ ^ (Γ.nA - Γ.nM) * (K₀ * ((W : ℝ) ^ d)⁻¹) ^ (Γ.nW - (Γ.nA - Γ.nM)) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) :=
          mul_le_mul_of_nonneg_left hmain hcn
      _ ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1) *
            (K₁ ^ (Γ.nA - Γ.nM) * ((K₀ * A) ^ (Γ.nW - (Γ.nA - Γ.nM)) * Ψ ^ (2 * (Γ.nW - (Γ.nA - Γ.nM)))) *
              Kd ^ (Γ.mdot.length + Γ.psi.length))) := by
          refine mul_le_mul_of_nonneg_left ?_ hcn
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) hav0)
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hapow (by positivity)
      _ = _ := by
          unfold BAGraph.sizeConst
          rw [pow_add]
          ring
  have hpt : ∀ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ ≤
      ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
    intro ℓi
    have hMn : 0 ≤ ‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
      have h1 : 0 ≤ (Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod :=
        List.prod_nonneg fun y hy => by
          obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
          exact hξ0 _ _
      have h2 : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
        Finset.prod_nonneg fun j _ => BAAtom_nonneg_fJ _ _ _ _ _
      positivity
    have hTl : 0 ≤ ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) := by
      have h2 : 0 ≤ ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) :=
        Finset.prod_nonneg fun j _ => BAAtom_fJw_nonneg _ _ _ _ _ _
      positivity
    by_cases hconf : ∀ j : Γ.Jx, (lwBdist d L W (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2) : ℝ) ≤ r
    · exact (BAAtom_term_conf Γ hN D hG hξ hr hRr ℓe ℓi root hroot hconf).trans (le_add_of_nonneg_right hTl)
    · push Not at hconf
      exact (BAAtom_term_tail Γ hN D hG hc _ hconf).trans (le_add_of_nonneg_left hMn)
  unfold BAGraph.val
  calc ‖∑ ℓi : I → Idx d L W, Γ.term D (Sum.elim ℓe ℓi)‖ ≤ ∑ ℓi : I → Idx d L W, ‖Γ.term D (Sum.elim ℓe ℓi)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ ℓi : I → Idx d L W, (‖Γ.coeff‖ * Ψ ^ (Γ.nS - Γ.shadow.molSolid.length) *
        ((Γ.shadow.molSolid.map fun e => ξ
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.src)
            (LGraph.auxLab Γ.shadow (fun a => (split d L W (ℓe a)).1) (fun c => (split d L W (ℓi (root c))).1) e.dst)).prod *
          ∏ j : Γ.Jx, BAAtom_fJ Γ D j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2)) +
      ‖Γ.coeff‖ * Ψ ^ Γ.nS * (Real.exp (-(c * r / 2)) *
        ∏ j : Γ.Jx, BAAtom_fJw Γ D c j (Sum.elim ℓe ℓi (Γ.edgeEnds j).1) (Sum.elim ℓe ℓi (Γ.edgeEnds j).2))) :=
        Finset.sum_le_sum fun ℓi _ => hpt ℓi
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add hmain' htail

end G3

/-- **`GtoAG` at the rescaled kernels without `hext`**: the BA form of Lemma 7.21 with
`D.S = S'`, `D.S⁺ = lift(ω_t)` and no `hext` (distinct external vertices in distinct molecules).  The constants depend on
`(d, Λ, κ)` only, uniformly in `0 ≤ t < 1`; at these kernels no `t` is lost, `BAExp14d_val_scale` restores `t^{n_W}`. -/
def BAGtoAGT (d : ℕ) : Prop :=
  3 ≤ d → ∀ Λ κ : ℝ, 0 < Λ → 0 < κ →
    ∃ K₀ K₁ Kd C c : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧ 0 ≤ C ∧ 0 < c ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 →
        ∀ (E' I' : Type) [Fintype E'] [DecidableEq E'] [Fintype I'] [DecidableEq I'] (Γ : BAGraph E' I'), Γ.Normal →
          ∀ D : BALData (Idx d L W), D.S = Matrix.of (fun x y => ((svarF d L W 0 x y : ℝ) : ℂ)) →
            D.Sp = lwLift d L W (BATheta d L g0 E m t true true) → D.M = BAlwM d L W g0 E m →
            D.gPsi = (g0 : ℂ) • PsiI d L W → ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ),
            (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A → ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 →
            0 ≤ r → (Fintype.card (E' ⊕ I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
            (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
              (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
            ∀ ℓe : E' → Idx d L W,
              ‖Γ.val D ℓe‖ ≤
                Γ.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
                    (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
                  Real.exp (-(c * r / 2)) * Γ.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
                    Γ.scalingSize Ψ W d L

section Kernels

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `S' = svarF(0)` is `W^{-d}` on a block and `0` elsewhere (`BAExp14a_S_apply` at `t = 1`). -/
private theorem BAExp14d_svar0 (x y : Idx d L W) :
    ((svarF d L W 0 x y : ℝ) : ℂ) = ((W : ℂ) ^ d)⁻¹ * if (split d L W x).1 = (split d L W y).1 then 1 else 0 := by
  have h := BAExp14a_S_apply (d := d) (L := L) (W := W) 1 x y
  simpa [BAlwS] using h

/-- Relaxing the constants of an exponential bound. -/
private theorem BAExp14d_relax {v w u C' c' C c : ℝ} (hw : 0 ≤ w) (hu : 0 ≤ u) (hC : C' ≤ C) (hc : c ≤ c') (hC0 : 0 ≤ C')
    (h : v ≤ C' * w * Real.exp (-(c' * u))) : v ≤ C * w * Real.exp (-(c * u)) :=
  h.trans (mul_le_mul (mul_le_mul_of_nonneg_right hC hw) (Real.exp_le_exp.2 (by nlinarith)) (Real.exp_pos _).le
    (mul_nonneg (hC0.trans hC) hw))

end Kernels

theorem baGtoAGT_holds (d : ℕ) : BAGtoAGT d := by
  intro hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  obtain ⟨_K₀, _K₁, Kd, -, -, hKd, hK⟩ := baKBound_E d hd Λ κ hΛ hκ
  obtain ⟨C₁, c₁, hC₁, hc₁, hdec⟩ := BAAtom_decay_E d hd Λ κ hΛ hκ
  have hC5 := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hμ := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  set Cθ : ℝ := (1 + Λ ^ 2) * BAp5s_C d Λ κ with hCθ
  have hCθ0 : 0 < Cθ := by positivity
  set C : ℝ := max (max C₁ 1) Cθ with hCdef
  set c : ℝ := min (min c₁ (BAp5s_rate d Λ κ)) 1 with hcdef
  have hC1 : 1 ≤ C := (le_max_right C₁ 1).trans ((le_max_left _ _))
  have hC0 : 0 ≤ C := by linarith
  have hc0 : 0 < c := lt_min (lt_min hc₁ hμ) one_pos
  have hCC₁ : C₁ ≤ C := (le_max_left C₁ 1).trans (le_max_left _ _)
  have hCCθ : Cθ ≤ C := le_max_right _ _
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hccθ : c ≤ BAp5s_rate d Λ κ := (min_le_left _ _).trans (min_le_right _ _)
  have hE : 0 < expC (d - 2) c := by unfold expC; positivity
  refine ⟨C, C * expC (d - 2) c, Kd, C, c, by linarith, by positivity, hKd, hC0, hc0, ?_⟩
  intro L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 E' I' _ _ _ _ Γ hN D hDS hDSp hDM hDP Ψ A r R ξ hG hA hwin hr0 hRr hξ0 hξ ℓe
  obtain ⟨-, -, hMP, hoff⟩ := hdec L W hL g0 E t m hg hgΛ hr ht0 ht1
  obtain ⟨-, -, hM', hP'⟩ := hK L W hL g0 E t m hg hgΛ hr ht0 ht1
  have hWd : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hbd : ∀ x y : Idx d L W, 0 ≤ (lwBdist d L W x y : ℝ) := fun x y => Nat.cast_nonneg _
  -- the decay of `S' = svarF(0)`
  have hSd : ∀ x y, ‖D.S x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDS, Matrix.of_apply, BAExp14d_svar0]
    by_cases h : (split d L W x).1 = (split d L W y).1
    · have h0 : (lwBdist d L W x y : ℝ) = 0 := by simp [lwBdist, h]
      rw [h0]
      simp only [h, ite_true, mul_one, mul_zero, neg_zero, Real.exp_zero, norm_inv, norm_pow, Complex.norm_natCast]
      nlinarith
    · simp only [h, ite_false, mul_zero, norm_zero]
      positivity
  -- the decay of `S⁺' = lift(ω_t)`
  have hSpd : ∀ x y, ‖D.Sp x y‖ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDSp]
    have hθ := BASizeClaim_theta_decay hL hd Λ g0 κ E t m hΛ hg hgΛ hκ hr ht0 ht1 (split d L W x).1 (split d L W y).1
    have e : ‖lwLift d L W (BATheta d L g0 E m t true true) x y‖ =
        ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖ := by
      simp [lwLift, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    rw [e]
    refine BAExp14d_relax (C' := Cθ) (c' := BAp5s_rate d Λ κ) hWd (hbd x y) hCCθ hccθ hCθ0.le ?_
    calc ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖
        ≤ ((W : ℝ) ^ d)⁻¹ * (Cθ * Real.exp (-(BAp5s_rate d Λ κ * (zdistD d L ((split d L W x).1 - (split d L W y).1) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hθ hWd
      _ = Cθ * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(BAp5s_rate d Λ κ * (lwBdist d L W x y : ℝ))) := by
          unfold lwBdist; ring
  -- the decay of `M`, `g₀ Ψ` and their offset structure
  have hMPd : ∀ x y, ‖D.M x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) ∧
      ‖D.gPsi x y‖ ≤ C * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    rw [hDM, hDP]
    obtain ⟨h1, h2⟩ := hMP x y
    refine ⟨?_, ?_⟩
    · have := BAExp14d_relax (w := 1) (v := ‖BAlwM d L W g0 E m x y‖) (C' := C₁) (c' := c₁) (C := C) (c := c) zero_le_one
        (hbd x y) hCC₁ hcc₁ hC₁ (by simpa using h1)
      simpa using this
    · have := BAExp14d_relax (w := 1) (v := ‖((g0 : ℂ) • PsiI d L W) x y‖) (C' := C₁) (c' := c₁) (C := C) (c := c) zero_le_one
        (hbd x y) hCC₁ hcc₁ hC₁ (by simpa using h2)
      simpa using this
  have hoff' : ∀ x y, (split d L W x).2 ≠ (split d L W y).2 → D.M x y = 0 ∧ D.gPsi x y = 0 := by
    intro x y hxy
    rw [hDM, hDP]
    exact hoff x y hxy
  have hM'' : LWKBound D.M Kd Kd := by rw [hDM]; exact hM'
  have hP'' : LWKBound D.gPsi Kd Kd := by rw [hDP]; exact hP'
  exact BAExp14d_G3 d hd L W Γ hN D Ψ A C (C * expC (d - 2) c) Kd C c r R ξ hG hA hwin
    (lwKBound_of_decay hd hC0 hc0 hSd) (lwKBound_of_decay hd hC0 hc0 hSpd) hM'' hP'' hC0 hc0 hSd hSpd hMPd hoff' hr0 hRr
    hξ0 hξ ℓe

/-! ## 3. The deterministic `q ≤ 1` bound (as `lwExpTerm3_det` in `Graph/LWExpTerm3.lean`) -/

section Det

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

open Classical in
/-- **(B.7) `Gammamuxy`, deterministic form, `q ≤ 1`**: from the bound of `GtoAG` at every non-negative `ξ` dominating `‖G - M‖`
(`hG3`, the conclusion of `BAGtoAGT` with `K = C_Γ(K₀ A, K₁, Kd)` and the tail `T`), with `ξ = min (cc ξ₀, Ψ)`, the auxiliary graph
is `≤ Ψ^{auxOrd}` (`q = 0`) or `≤ Ψ^{auxOrd} · cc² · S2` (`q = 1`, Cauchy-Schwarz on the two attached edges, band
`lwExpTerm3_auxVal_one` on the shadow).  No `hext`, no `M = m I`. -/
private theorem BAExp14d_det {d L W : ℕ} [NeZero L] [NeZero W] (Γ : BAGraph E I) (hN : Γ.Normal) (hnM : Γ.nM ≤ 1)
    (hatt : ∀ v : I, (∀ w ∈ Γ.mol (Sum.inr v), w.isRight = true) →
      2 ≤ (Γ.solid.filter fun e => decide (Γ.mol e.src ≠ Γ.mol e.dst ∧
        (Γ.mol e.src = Γ.mol (Sum.inr v) ∨ Γ.mol e.dst = Γ.mol (Sum.inr v)))).length)
    (D : BALData (Idx d L W)) {Ψ cc S2 R K T : ℝ} (ξ0 : Zd d L → Zd d L → ℝ) (hK : 0 ≤ K) (hΨ : 0 < Ψ) (hcc : 0 ≤ cc)
    (h0 : ∀ a b, 0 ≤ ξ0 a b) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ cc * ξ0 a b)
    (hrow : ∀ a, ∑ v, ξ0 a v ^ 2 ≤ S2) (hcol : ∀ a, ∑ v, ξ0 v a ^ 2 ≤ S2) (ℓe : E → Idx d L W)
    (hG3 : ∀ ξ : Zd d L → Zd d L → ℝ, (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
        (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
      ‖Γ.val D ℓe‖ ≤ K * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) *
          (((W : ℝ) ^ d) ^ Γ.nM * Γ.auxVal ξ (fun a => (split d L W (ℓe a)).1)) + T) :
    ‖Γ.val D ℓe‖ ≤ K * (Ψ ^ Γ.scalingOrder * (if Γ.nM = 1 then ((W : ℝ) ^ d) * (cc ^ 2 * S2) else 1)) + T := by
  set ξ : Zd d L → Zd d L → ℝ := fun a b => min (cc * ξ0 a b) Ψ with hξdef
  have hξ0 : ∀ a b, 0 ≤ ξ a b := fun a b => le_min (mul_nonneg hcc (h0 a b)) hΨ.le
  have hξΨ : ∀ a b, ξ a b ≤ Ψ := fun a b => min_le_right _ _
  have hξ1 : ∀ a b, ξ a b ≤ cc * ξ0 a b := fun a b => min_le_left _ _
  have hmain := hG3 ξ hξ0 (fun x y a b h1 h2 => le_min (hξ x y a b h1 h2) (hG x y))
  set be : E → Zd d L := fun a => (split d L W (ℓe a)).1 with hbe
  have hΨne : Ψ ≠ 0 := hΨ.ne'
  have hsq : ∀ a b, ξ a b ^ 2 ≤ cc ^ 2 * ξ0 a b ^ 2 := fun a b => by
    rw [← mul_pow]; exact pow_le_pow_left₀ (hξ0 a b) (hξ1 a b) 2
  have hrow' : ∀ a, ∑ v, ξ a v ^ 2 ≤ cc ^ 2 * S2 := fun a =>
    (Finset.sum_le_sum fun v _ => hsq a v).trans (by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrow a) (sq_nonneg _))
  have hcol' : ∀ a, ∑ v, ξ v a ^ 2 ≤ cc ^ 2 * S2 := fun a =>
    (Finset.sum_le_sum fun v _ => hsq v a).trans (by
      rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hcol a) (sq_nonneg _))
  have hnMs : Γ.shadow.nM = Γ.nM := BAGraph.shadow_nM Γ
  have hzp : ∀ n : ℤ, 0 ≤ Ψ ^ n := fun n => zpow_nonneg hΨ.le n
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hnM with h1 | h1
  · -- q = 0
    have hav : Γ.auxVal ξ be ≤ Ψ ^ Γ.shadow.molSolid.length :=
      lwExpTerm3_auxVal_zero Γ.shadow (hnMs.trans h1) ξ be hξ0 hξΨ
    have hao : Γ.auxOrd = (Γ.shadow.molSolid.length : ℤ) := by
      simp [BAGraph.auxOrd, LGraph.auxOrd, ord, hnMs.trans h1]
    refine hmain.trans (add_le_add ?_ le_rfl)
    rw [h1]
    simp only [pow_zero, one_mul, zero_ne_one, ite_false, mul_one]
    calc K * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Γ.auxVal ξ be
        ≤ K * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ Γ.shadow.molSolid.length :=
          mul_le_mul_of_nonneg_left hav (mul_nonneg hK (hzp _))
      _ = K * Ψ ^ Γ.scalingOrder := by
          rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hΨne, hao]; congr 2; ring
  · -- q = 1
    have hatt' : ∀ v : I, (∀ w ∈ Γ.shadow.mol (Sum.inr v), w.isRight = true) →
        2 ≤ (Γ.shadow.solid.filter fun e => decide (Γ.shadow.mol e.src ≠ Γ.shadow.mol e.dst ∧
          (Γ.shadow.mol e.src = Γ.shadow.mol (Sum.inr v) ∨ Γ.shadow.mol e.dst = Γ.shadow.mol (Sum.inr v)))).length := by
      intro v hv
      simp only [BAGraph.shadow_mol] at hv ⊢
      exact hatt v hv
    obtain ⟨k, hk, hav⟩ := lwExpTerm3_auxVal_one Γ.shadow (hnMs.trans h1) hatt' ξ be hΨ.le hξ0 hξΨ hrow' hcol'
    have hao : Γ.auxOrd = (k : ℤ) := by
      simp only [BAGraph.auxOrd, LGraph.auxOrd, ord, hnMs.trans h1]; omega
    refine hmain.trans (add_le_add ?_ le_rfl)
    rw [h1]
    simp only [pow_one, ite_true]
    have hav' : Γ.auxVal ξ be ≤ Ψ ^ k * (cc ^ 2 * S2) := hav
    calc K * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * ((W : ℝ) ^ d * Γ.auxVal ξ be)
        ≤ K * Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * ((W : ℝ) ^ d * (Ψ ^ k * (cc ^ 2 * S2))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hav' (by positivity)) (mul_nonneg hK (hzp _))
      _ = K * (Ψ ^ Γ.scalingOrder * ((W : ℝ) ^ d * (cc ^ 2 * S2))) := by
          have : Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ k = Ψ ^ Γ.scalingOrder := by
            rw [← zpow_natCast, ← zpow_add₀ hΨne, hao]; congr 1; ring
          calc _ = K * (Ψ ^ (Γ.scalingOrder - Γ.auxOrd) * Ψ ^ k) * ((W : ℝ) ^ d * (cc ^ 2 * S2)) := by ring
            _ = _ := by rw [this]; ring

end Det

/-- `‖(G_t - M)_{xy}‖ ≤ η⁻¹ + 1` for every sample (`‖G‖ ≤ η⁻¹`, `‖M‖ ≤ 1`). -/
private theorem BAExp14d_GM_le {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  have h1 := BAExp14a_G_le hκ hflow n ht0 htT ω x y
  have h2 := (ba_G_data hκ sz hflow n ht0 htT).2.2.2.2.2 x y
  calc ‖(baFMz sz z).G n t ω x y - (baFMz sz z).M n x y‖
      ≤ ‖(baFMz sz z).G n t ω x y‖ + ‖(baFMz sz z).M n x y‖ := norm_sub_le _ _
    _ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := add_le_add h1 h2

end RBM.BA
