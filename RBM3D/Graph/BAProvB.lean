/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAProv
import RBM3D.Graph.BAShapeO2B

set_option linter.style.header false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open private BAWeightOp_core BAWeightOp_sd from RBM3D.Graph.BAWeightOp
open private BAGGOp_core from RBM3D.Graph.BAGGOp
open private BAExpandW_integrable_PF from RBM3D.Graph.BAExpandW
open private BALvl1A_data_zero BALvl1A_lwSplit_last BALvl1A_sum_eraseIdx from RBM3D.Graph.BALvl1A
open private BAEngine_frame_ne_nil BAEngine_integral_comb BAEngine_partition_ne_nil BAEngine_Spec from RBM3D.Graph.BAEngine

noncomputable section
open MeasureTheory RBM RBM.Gauss RBM.Gauss.Sizes RBM.Green RBM.BA

namespace RBM.Graph

/-! ## 1. Integrability, continuity and the weighted expansion of an extension -/

section Gen

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem BAProv_hz {g0 Em t : ℝ} {m : ℂ} (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht : 0 < t) (ht1 : t < 1) : (ztOf m Em t).im ≠ 0 := by
  have hm : 0 < m.im := hSelf.1
  rw [ztOf_im, etaOf]; exact (mul_pos (by linarith) hm).ne'

/-- every term is integrable at `BAlwData` (`t = 0`: constant; `t > 0`: tame on the sequence space) -/
theorem BAProv_integrable_term (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E I : Type} [Fintype I] [DecidableEq I] (T : BAGraph E I) (ℓ : E ⊕ I → Idx d L W) :
    Integrable (fun ω => T.term (BAlwData d L W g0 Em t m ω) ℓ) (PF d L W 0) := by
  rcases ht0.eq_or_lt with rfl | ht
  · have h : (fun ω : Ω d L W => T.term (BAlwData d L W g0 Em 0 m ω) ℓ) = fun _ => T.term (BAlwData d L W g0 Em 0 m 0) ℓ :=
      funext fun ω => by rw [BALvl1A_data_zero g0 Em m ω 0]
    rw [h]; exact integrable_const _
  · exact BAExpandW_integrable_PF hL (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) (BAProv_hz hSelf ht ht1) T ℓ).tame fun ω' => rfl

theorem BAProv_integrable_valW (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E I : Type} [Fintype I] [DecidableEq I] (T : BAGraph E I) (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    Integrable (fun ω => T.valW (BAlwData d L W g0 Em t m ω) Wt ℓe) (PF d L W 0) :=
  integrable_finsetSum _ fun ℓi _ => (BAProv_integrable_term hL g0 Em t m hSelf ht0 ht1 T _).const_mul _

end Gen

section Ext

variable {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the weighted value of a graph with two new vertices, the weight read through `owxEmb 2` (weighted `BAWeightOp_val2`; `lwProv_EW_ext2`, `LWProv:866`) -/
theorem BAProv_valW_ext2 (T : BAGraph E (I ⊕ Fin 2)) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    T.valW D (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe =
      ∑ ℓi : I → ι, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * ∑ α, ∑ β, T.term D (owxLab2 ℓe ℓi α β) := by
  unfold BAGraph.valW
  rw [owx_sum_fin2 (fun ℓ' => (((Wt ((Sum.elim ℓe ℓ') ∘ owxEmb 2)) : ℝ) : ℂ) * T.term D (Sum.elim ℓe ℓ'))]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have h := BAExpandW_lab2_emb ℓe ℓi α β
  simp only [owxLab2] at h ⊢
  rw [h]

theorem BAProv_valW_ext4 (T : BAGraph E (I ⊕ Fin 4)) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) :
    T.valW D (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe =
      ∑ ℓi : I → ι, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * ∑ z, ∑ y, ∑ α, ∑ β, T.term D (BAWeightOp_lab4 ℓe ℓi z y α β) := by
  unfold BAGraph.valW
  rw [BAWeightOp_sum_fin4 (fun ℓ' => (((Wt ((Sum.elim ℓe ℓ') ∘ owxEmb 4)) : ℝ) : ℂ) * T.term D (Sum.elim ℓe ℓ'))]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have h := BAWeightOp_lab4_emb ℓe ℓi z y α β
  simp only [BAWeightOp_lab4] at h ⊢
  rw [h]

/-- the new-label sums of a step: two lists of terms with two resp. four new vertices (the integrand `BAWeightOp_R` of `lem_lweight`, `BAGGOp_R` of `GGGamma`) -/
def BAProv_R (Ts2 : List (BAGraph E (I ⊕ Fin 2))) (Ts4 : List (BAGraph E (I ⊕ Fin 4))) (D : BALData ι) (ℓe : E → ι) (ℓi : I → ι) : ℂ :=
  ∑ α, ∑ β, (Ts2.map fun T => T.term D (owxLab2 ℓe ℓi α β)).sum +
    ∑ z, ∑ y, ∑ α, ∑ β, (Ts4.map fun T => T.term D (BAWeightOp_lab4 ℓe ℓi z y α β)).sum

theorem BAProv_swap4 {κ' : Type*} (Ls : List κ') (w : (I → ι) → ℂ) (f : κ' → (I → ι) → ι → ι → ι → ι → ℂ) :
    ∑ ℓi, w ℓi * ∑ z, ∑ y, ∑ α, ∑ β, (Ls.map fun q => f q ℓi z y α β).sum =
      (Ls.map fun q => ∑ ℓi, w ℓi * ∑ z, ∑ y, ∑ α, ∑ β, f q ℓi z y α β).sum := by
  induction Ls with
  | nil => simp
  | cons q Ls ih => simp [mul_add, Finset.sum_add_distrib, ih]

/-- **the algebra of a step** (weighted `BAWeightOp_baSum_eq`): the weighted sum of the new-label sums is the sum of the weighted values -/
theorem BAProv_alg (Ts2 : List (BAGraph E (I ⊕ Fin 2))) (Ts4 : List (BAGraph E (I ⊕ Fin 4))) (D : BALData ι) (Wt : (E ⊕ I → ι) → ℝ)
    (ℓe : E → ι) : ∑ ℓi, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * BAProv_R Ts2 Ts4 D ℓe ℓi =
      (Ts2.map fun T => T.valW D (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe).sum + (Ts4.map fun T => T.valW D (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe).sum := by
  unfold BAProv_R
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [lwProv_swap2]
    simp only [BAProv_valW_ext2]
  · rw [BAProv_swap4]
    simp only [BAProv_valW_ext4]

end Ext

/-! ## 2. The weighted identity of a step from its per-labelling core -/

section Step

variable {d L W : ℕ} [NeZero L] [NeZero W]

theorem BAProv_valW_zero {E I : Type} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι] [DecidableEq ι] (T : BAGraph E I) (D : BALData ι)
    (Wt : (E ⊕ I → ι) → ℝ) (ℓe : E → ι) (h : ∀ ℓ, T.term D ℓ = 0) : T.valW D Wt ℓe = 0 :=
  Finset.sum_eq_zero fun ℓi _ => by rw [h]; simp

/-- **the weighted identity of a step** (weighted `baExpFrame_lw` / `baExpFrame_gg` / `lanlw_val`; `lwProv_weight_EW`, `LWProv:850`): if `E Γ.term(ℓ)` is, at every labelling `ℓ = (ℓe, ℓi)` of the old
vertices, `E` of the sum over the labels of the new vertices of the terms of the two lists (`hcore`, on the sequence space), and every term vanishes at `t = 0` (`hzero`), then for every real weight
`E Γ.valW = Σ_T E T.valW`, the weight read through `owxEmb 2` resp. `owxEmb 4` -/
private theorem BAProv_step_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] (Γ : BAGraph E I)
    (Ts2 : List (BAGraph E (I ⊕ Fin 2))) (Ts4 : List (BAGraph E (I ⊕ Fin 4)))
    (hcore : 0 < t → ∀ (ℓe : E → Idx d L W) (ℓi : I → Idx d L W),
      Integrable (fun ω' => BAProv_R Ts2 Ts4 (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi) (lwWxSizes d L W 0 hL).seqP ∧
      ∫ ω', Γ.term (BAWeightOp_sd hL g0 Em t m ω') (Sum.elim ℓe ℓi) ∂(lwWxSizes d L W 0 hL).seqP =
        ∫ ω', BAProv_R Ts2 Ts4 (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi ∂(lwWxSizes d L W 0 hL).seqP)
    (hzero : t = 0 → (∀ ω ℓ, Γ.term (BAlwData d L W g0 Em t m ω) ℓ = 0) ∧ (∀ T ∈ Ts2, ∀ ω ℓ, T.term (BAlwData d L W g0 Em t m ω) ℓ = 0) ∧
      ∀ T ∈ Ts4, ∀ ω ℓ, T.term (BAlwData d L W g0 Em t m ω) ℓ = 0)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      (Ts2.map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      (Ts4.map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe ∂(PF d L W 0)).sum := by
  classical
  rcases ht0.eq_or_lt with rfl | ht
  · obtain ⟨h1, h2, h3⟩ := hzero rfl
    have e2 : ∀ T ∈ Ts2, ∫ ω, T.valW (BAlwData d L W g0 Em 0 m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) = 0 := fun T hT => by
      simp [BAProv_valW_zero T _ _ _ (h2 T hT _)]
    have e4 : ∀ T ∈ Ts4, ∫ ω, T.valW (BAlwData d L W g0 Em 0 m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe ∂(PF d L W 0) = 0 := fun T hT => by
      simp [BAProv_valW_zero T _ _ _ (h3 T hT _)]
    rw [List.sum_eq_zero fun a ha => by obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha; exact e2 T hT,
      List.sum_eq_zero fun a ha => by obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ha; exact e4 T hT]
    simp [BAProv_valW_zero Γ _ _ _ (h1 _)]
  · have hz := BAProv_hz hSelf ht ht1
    have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
    have hint : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') (ℓ : E' ⊕ I' → Idx d L W),
        Integrable (fun ω' => T.term (BAWeightOp_sd hL g0 Em t m ω') ℓ) (lwWxSizes d L W 0 hL).seqP :=
      fun T ℓ => Tame.integrable hG (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓ).tame
    have hcont : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') (W' : (E' ⊕ I' → Idx d L W) → ℝ) (ℓe' : E' → Idx d L W),
        Continuous (fun ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') W' ℓe') :=
      fun T W' ℓe' => continuous_finsetSum _ fun ℓi _ =>
        continuous_const.mul (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz T _).tame.cont
    have hlift : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') (W' : (E' ⊕ I' → Idx d L W) → ℝ) (ℓe' : E' → Idx d L W),
        ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) W' ℓe' ∂(PF d L W 0) =
          ∫ ω', T.valW (BAWeightOp_sd hL g0 Em t m ω') W' ℓe' ∂(lwWxSizes d L W 0 hL).seqP :=
      fun T W' ℓe' => lwWx_integral hL (hcont T W' ℓe') fun ω' => rfl
    have hintV : ∀ {E' I' : Type} [Fintype I'] [DecidableEq I'] (T : BAGraph E' I') (W' : (E' ⊕ I' → Idx d L W) → ℝ) (ℓe' : E' → Idx d L W),
        Integrable (fun ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') W' ℓe') (lwWxSizes d L W 0 hL).seqP :=
      fun T W' ℓe' => integrable_finsetSum _ fun ℓi _ => (hint T _).const_mul _
    rw [hlift Γ Wt ℓe]
    have hL1 : ∫ ω', Γ.valW (BAWeightOp_sd hL g0 Em t m ω') Wt ℓe ∂(lwWxSizes d L W 0 hL).seqP =
        ∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) *
          ∫ ω', Γ.term (BAWeightOp_sd hL g0 Em t m ω') (Sum.elim ℓe ℓi) ∂(lwWxSizes d L W 0 hL).seqP := by
      unfold BAGraph.valW
      rw [integral_finsetSum _ fun ℓi _ => (hint Γ _).const_mul _]
      exact Finset.sum_congr rfl fun ℓi _ => integral_const_mul _ _
    have hR : ∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) *
          ∫ ω', Γ.term (BAWeightOp_sd hL g0 Em t m ω') (Sum.elim ℓe ℓi) ∂(lwWxSizes d L W 0 hL).seqP =
        ∫ ω', ∑ ℓi : I → Idx d L W, ((Wt (Sum.elim ℓe ℓi) : ℝ) : ℂ) * BAProv_R Ts2 Ts4 (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi
          ∂(lwWxSizes d L W 0 hL).seqP := by
      rw [integral_finsetSum _ fun ℓi _ => (hcore ht ℓe ℓi).1.const_mul _]
      exact Finset.sum_congr rfl fun ℓi _ => by rw [(hcore ht ℓe ℓi).2, integral_const_mul]
    rw [hL1, hR]
    simp_rw [BAProv_alg]
    have i2 := owx_integrable_list_sum Ts2 (fun T ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe)
      (fun T _ => hintV T _ _)
    have i4 := owx_integrable_list_sum Ts4 (fun T ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe)
      (fun T _ => hintV T _ _)
    rw [integral_add i2 i4, owx_integral_list_sum _ Ts2 (fun T ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe)
        (fun T _ => hintV T _ _),
      owx_integral_list_sum _ Ts4 (fun T ω' => T.valW (BAWeightOp_sd hL g0 Em t m ω') (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe) (fun T _ => hintV T _ _)]
    congr 1
    · exact congrArg List.sum (List.map_congr_left fun T _ => (hlift T _ _).symm)
    · exact congrArg List.sum (List.map_congr_left fun T _ => (hlift T _ _).symm)

/-! ### The data at `t = 0`: every term of a step vanishes -/

theorem BAProv_S_zero (g0 Em : ℝ) (m : ℂ) (ω : Ω d L W) : (BAlwData d L W g0 Em 0 m ω).S = 0 ∧ (BAlwData d L W g0 Em 0 m ω).Sp = 0 := by
  have h0 : Matrix.of (BAlwS d L W 0) = (0 : Matrix (Idx d L W) (Idx d L W) ℂ) := by ext i j; simp [BAlwS]
  refine ⟨h0, ?_⟩
  change Matrix.of (BAlwS d L W 0) * BAlwW d L W g0 Em 0 m = 0
  rw [h0, zero_mul]

theorem BAProv_term_zero_waved {ι : Type*} [Fintype ι] [DecidableEq ι] {E I : Type} [Fintype I] [DecidableEq I] (T : BAGraph E I) (D : BALData ι)
    (hS : D.S = 0) (hSp : D.Sp = 0) (hne : T.waved ≠ []) (ℓ : E ⊕ I → ι) : T.term D ℓ = 0 := by
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
  have h0 : WEdge.val D.toLData ℓ e = 0 := by
    unfold WEdge.val
    split_ifs <;> simp [hS, hSp]
  have hmem : WEdge.val D.toLData ℓ e ∈ T.waved.map (WEdge.val D.toLData ℓ) := List.mem_map.2 ⟨e, he, rfl⟩
  have hp := List.prod_eq_zero (h0 ▸ hmem)
  unfold BAGraph.term LGraph.term
  rw [hp]
  simp

theorem BAProv_term_zero_edge {E I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true) (g0 Em : ℝ) (m : ℂ) (ω : Ω d L W) (ℓ : E ⊕ I → Idx d L W) :
    Γ.term (BAlwData d L W g0 Em 0 m ω) ℓ = 0 := by
  have h0 : SEdge.val (BAlwData d L W g0 Em 0 m ω).toLData ℓ p.1 = 0 := by
    have := BAExpand_Gc_zero (d := d) (L := L) (W := W) g0 Em m ω (ℓ p.1.src) (ℓ p.1.dst)
    simp only [SEdge.val, hσ, hc, BAlwData, ite_true]
    simpa [BAlwGc] using this
  simp only [BAGraph.term, LGraph.term, lwSplit_prod Γ.solid _ p hp, h0]
  simp

/-- the hypothesis `hzero` of `BAProv_step_W`: the selected edge `Ǧ` vanishes on the left, a waved edge `S` / `S⁺` on the right -/
theorem BAProv_hzero {E I : Type} [Fintype I] [DecidableEq I] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid)
    (hσ : p.1.σ = true) (hc : p.1.circ = true) (Ts2 : List (BAGraph E (I ⊕ Fin 2))) (Ts4 : List (BAGraph E (I ⊕ Fin 4)))
    (h2 : ∀ T ∈ Ts2, T.waved ≠ []) (h4 : ∀ T ∈ Ts4, T.waved ≠ []) (g0 Em : ℝ) (m : ℂ) :
    (∀ (ω : Ω d L W) ℓ, Γ.term (BAlwData d L W g0 Em 0 m ω) ℓ = 0) ∧
      (∀ T ∈ Ts2, ∀ (ω : Ω d L W) ℓ, T.term (BAlwData d L W g0 Em 0 m ω) ℓ = 0) ∧
      ∀ T ∈ Ts4, ∀ (ω : Ω d L W) ℓ, T.term (BAlwData d L W g0 Em 0 m ω) ℓ = 0 :=
  ⟨fun ω ℓ => BAProv_term_zero_edge Γ p hp hσ hc g0 Em m ω ℓ,
    fun T hT ω ℓ => BAProv_term_zero_waved T _ (BAProv_S_zero g0 Em m ω).1 (BAProv_S_zero g0 Em m ω).2 (h2 T hT) ℓ,
    fun T hT ω ℓ => BAProv_term_zero_waved T _ (BAProv_S_zero g0 Em m ω).1 (BAProv_S_zero g0 Em m ω).2 (h4 T hT) ℓ⟩

end Step

/-! ## 3. The weighted identities of the steps -/

section Kinds

variable {d L W : ℕ} [NeZero L] [NeZero W] {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

theorem BAProv_lw_waved (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (∀ T ∈ Γ.lw2 p, T.waved ≠ []) ∧ ∀ T ∈ Γ.lw4 p, T.waved ≠ [] := by
  constructor
  · intro T hT
    simp only [BAGraph.lw2, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, -, rfl⟩ <;> simp [BAGraph.ext, BAGraph.lanlwD, BAGraph.lanlwExt, LGraph.owxExt]
  · intro T hT
    simp only [BAGraph.lw4, List.mem_cons, List.mem_map] at hT
    rcases hT with rfl | ⟨q, -, rfl⟩ <;> simp [BAGraph.ext, LGraph.owxExt]

/-- **`lem_lweight` with a weight on all the vertices** (weighted `baExpFrame_lw`): for the circled blue self-loop `p.1 = Ǧ_{xx}` -/
theorem BAProv_lw_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true)
    (hxx : p.1.src = p.1.dst) (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      ((Γ.lw2 p).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      ((Γ.lw4 p).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe ∂(PF d L W 0)).sum :=
  BAProv_step_W hL g0 Em t m hSelf ht0 ht1 Γ (Γ.lw2 p) (Γ.lw4 p)
    (fun ht ℓe ℓi => BAWeightOp_core hL g0 Em t m hSelf ht ht1 Γ p hp hσ hc hxx ℓe ℓi)
    (fun h0 => by subst h0; exact BAProv_hzero Γ p hp hσ hc _ _ (BAProv_lw_waved Γ p).1 (BAProv_lw_waved Γ p).2 g0 Em m) Wt ℓe

theorem BAProv_gg_waved (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    (∀ T ∈ Γ.gg2 p q, T.waved ≠ []) ∧ ∀ T ∈ Γ.gg4 p q, T.waved ≠ [] := by
  constructor
  · intro T hT
    unfold BAGraph.gg2 at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl | rfl | rfl | rfl) | ⟨r, -, rfl⟩ <;> simp [BAGraph.ext, LGraph.owxExt]
  · intro T hT
    unfold BAGraph.gg4 at hT
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hT
    rcases hT with (rfl | rfl) | ⟨r, -, rfl⟩ <;> simp [BAGraph.ext, LGraph.owxExt]

/-- **`GGGamma` with a weight on all the vertices** (weighted `baExpFrame_gg`): for the circled blue edges `p.1 = Ǧ_{xy}`, `q.1 = Ǧ_{y'x}` -/
theorem BAProv_gg_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hq : q ∈ lwSplit p.2) (hσp : p.1.σ = true)
    (hcp : p.1.circ = true) (hσq : q.1.σ = true) (hcq : q.1.circ = true) (hxy : p.1.src = q.1.dst) (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      ((Γ.gg2 p q).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      ((Γ.gg4 p q).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 4)) ℓe ∂(PF d L W 0)).sum :=
  BAProv_step_W hL g0 Em t m hSelf ht0 ht1 Γ (Γ.gg2 p q) (Γ.gg4 p q)
    (fun ht ℓe ℓi => BAGGOp_core hL g0 Em t m hSelf ht ht1 Γ p q hp hq hσp hcp hσq hcq hxy ℓe ℓi)
    (fun h0 => by subst h0; exact BAProv_hzero Γ p hp hσp hcp _ _ (BAProv_gg_waved Γ p q).1 (BAProv_gg_waved Γ p q).2 g0 Em m) Wt ℓe

theorem BAProv_lanlw_waved (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : ∀ T ∈ BAGraph.lanlwTerms Γ p, T.waved ≠ [] := by
  intro T hT
  simp only [BAGraph.lanlwTerms, List.mem_cons, List.mem_map] at hT
  rcases hT with rfl | ⟨q, -, rfl⟩ <;> simp [BAGraph.lanlwT1, BAGraph.lanlwD, BAGraph.lanlwExt, LGraph.owxExt]

theorem BAProv_int_sum2 {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} (A B : ι → ι → Ω → ℂ) (hA : ∀ a b, Integrable (A a b) P)
    (hB : ∀ a b, Integrable (B a b) P) :
    ∫ ω, ∑ a, ∑ b, (A a b ω + B a b ω) ∂P = ∑ a, ∑ b, ∫ ω, A a b ω ∂P + ∑ a, ∑ b, ∫ ω, B a b ω ∂P := by
  have h1 : ∀ a b, Integrable (fun ω => A a b ω + B a b ω) P := fun a b => (hA a b).add (hB a b)
  have h2 : ∀ a, Integrable (fun ω => ∑ b, (A a b ω + B a b ω)) P := fun a => integrable_finsetSum _ fun b _ => h1 a b
  rw [integral_finsetSum _ fun a _ => h2 a, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => h1 a b, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => integral_add (hA a b) (hB a b)

/-- the per-labelling core of `lanlw` in the form of `BAProv_step_W` (from `BAExpandW_term_integral`, as `lanlw_val`) -/
private theorem BAProv_lanlw_core (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht : 0 < t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true)
    (ℓe : E → Idx d L W) (ℓi : I → Idx d L W) :
    Integrable (fun ω' => BAProv_R (BAGraph.lanlwTerms Γ p) ([] : List (BAGraph E (I ⊕ Fin 4))) (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi)
        (lwWxSizes d L W 0 hL).seqP ∧
      ∫ ω', Γ.term (BAWeightOp_sd hL g0 Em t m ω') (Sum.elim ℓe ℓi) ∂(lwWxSizes d L W 0 hL).seqP =
        ∫ ω', BAProv_R (BAGraph.lanlwTerms Γ p) ([] : List (BAGraph E (I ⊕ Fin 4))) (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi
          ∂(lwWxSizes d L W 0 hL).seqP := by
  classical
  have hm : 0 < m.im := hSelf.1
  have hz := BAProv_hz hSelf ht ht1
  have hG : GaussIBP (lwWxSizes d L W 0 hL) := gaussIBP _
  have hS : Matrix.of (BAlwS d L W t) = lwS (lwWxSizes d L W 0 hL) 0 t := by ext i j; simp [lwS, BAlwS]
  have key := BAExpandW_term_integral (sz := lwWxSizes d L W 0 hL) (n := 0) (g0 := g0) (z := ztOf m Em t) (u := t)
    (M := BAlwM d L W g0 Em m) (Sp := Matrix.of (BAlwS d L W t) * BAlwW d L W g0 Em t m) (gPsi := (g0 : ℂ) • PsiI d L W) hG hz ht m
    (BAExpand_M_diag g0 Em m hSelf) (fun ω => BAExpand_G_sub_M (lwWxSizes d L W 0 hL) 0 g0 Em t m hm ht1 ω) Γ p hp hσ hc ℓe ℓi
  rw [← hS] at key
  have hint : ∀ (T : BAGraph E (I ⊕ Fin 2)) (ℓ' : E ⊕ (I ⊕ Fin 2) → Idx d L W),
      Integrable (fun ω' => T.term (BAWeightOp_sd hL g0 Em t m ω') ℓ') (lwWxSizes d L W 0 hL).seqP :=
    fun T ℓ' => Tame.integrable hG (BAExpandW_term_tame1 (sz := lwWxSizes d L W 0 hL) (n := 0) hz T ℓ').tame
  have hRf : ∀ ω', BAProv_R (BAGraph.lanlwTerms Γ p) ([] : List (BAGraph E (I ⊕ Fin 4))) (BAWeightOp_sd hL g0 Em t m ω') ℓe ℓi =
      ∑ α, ∑ β, ((BAGraph.lanlwT1 Γ p).term (BAWeightOp_sd hL g0 Em t m ω') (owxLab2 ℓe ℓi α β) +
        ((lwSplit p.2).map fun q => (BAGraph.lanlwD Γ p q).term (BAWeightOp_sd hL g0 Em t m ω') (owxLab2 ℓe ℓi α β)).sum) := by
    intro ω'
    simp [BAProv_R, BAGraph.lanlwTerms, Function.comp_def]
  have hB : ∀ α β : Idx d L W, Integrable (fun ω' => ((lwSplit p.2).map fun q =>
      (BAGraph.lanlwD Γ p q).term (BAWeightOp_sd hL g0 Em t m ω') (owxLab2 ℓe ℓi α β)).sum) (lwWxSizes d L W 0 hL).seqP :=
    fun α β => owx_integrable_list_sum _ _ fun q _ => hint _ _
  simp_rw [hRf]
  refine ⟨integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => (hint _ _).add (hB α β), ?_⟩
  refine key.trans ?_
  rw [BAProv_int_sum2 (fun α β ω' => (BAGraph.lanlwT1 Γ p).term (BAWeightOp_sd hL g0 Em t m ω') (owxLab2 ℓe ℓi α β))
    (fun α β ω' => ((lwSplit p.2).map fun q => (BAGraph.lanlwD Γ p q).term (BAWeightOp_sd hL g0 Em t m ω') (owxLab2 ℓe ℓi α β)).sum)
    (fun α β => hint _ _) hB]
  congr 1
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [owx_integral_list_sum _ _ _ fun q _ => hint _ _]

/-- **`lanlw` with a weight on all the vertices** (weighted `lanlw_val`) -/
theorem BAProv_lanlw_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      ((BAGraph.lanlwTerms Γ p).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum := by
  have h := BAProv_step_W hL g0 Em t m hSelf ht0 ht1 Γ (BAGraph.lanlwTerms Γ p) ([] : List (BAGraph E (I ⊕ Fin 4)))
    (fun ht ℓe ℓi => BAProv_lanlw_core hL g0 Em t m hSelf ht ht1 Γ p hp hσ hc ℓe ℓi)
    (fun h0 => by subst h0; exact BAProv_hzero Γ p hp hσ hc _ _ (BAProv_lanlw_waved Γ p) (by simp) g0 Em m) Wt ℓe
  simpa using h

/-! ### The macros (a) `within` and (b) `ggSplit` -/

/-- the transfer graph of macro (a) (`BAPGraph.withinOuts`): the edge `Ǧ_{xy}` is replaced by `M_{xα} M_{αy}` and the loop `Ǧ_{ββ}`... -/
def BAProv_trA (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)]

/-- the loop of the transfer graph and the rest of the edges, read through `owxEmb 2` -/
def BAProv_ppA (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
  (bpS true (bpv 1) (bpv 1), p.2.map (SEdge.map (owxEmb 2)))

/-- the first term of `lanlw`, with `G_{αy}` replaced by `Ǧ_{αy}` -/
def BAProv_A0 (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS true (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)] [bpM (owxEmb 2 p.1.src) (bpv 0)]

/-- **macro (a), pathwise** (`BALvl1A_macroA_val` before the sum over the labels): `G_{αy} = Ǧ_{αy} + M_{αy}` in the first term of `lanlw` -/
theorem BAProv_macroA_term {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (D : BALData ι)
    (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) :
    (BAGraph.lanlwT1 Γ p).term D ℓ' = (BAProv_A0 Γ p).term D ℓ' + (BAProv_trA Γ p).term D ℓ' := by
  change (BAGraph.ext 2 Γ p.2 [bpS true (bpv 1) (bpv 1), bpS false (bpv 0) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
          [bpM (owxEmb 2 p.1.src) (bpv 0)]).term D ℓ' = _
  unfold BAProv_A0 BAProv_trA
  rw [BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val, BAMEdge.val, bpS, bpW, bpM, bpv]
  simp
  ring

theorem BAProv_valW_sum {ι : Type*} [Fintype ι] [DecidableEq ι] {E' I' : Type} [Fintype I'] [DecidableEq I'] (A : BAGraph E' I') (Bs : List (BAGraph E' I'))
    (D : BALData ι) (h : ∀ ℓ, A.term D ℓ = (Bs.map fun T => T.term D ℓ).sum) (Wt : (E' ⊕ I' → ι) → ℝ) (ℓe : E' → ι) :
    A.valW D Wt ℓe = (Bs.map fun T => T.valW D Wt ℓe).sum := by
  unfold BAGraph.valW
  simp_rw [h, ← List.sum_map_mul_left]
  rw [lwStein_sum_list]

theorem BAProv_valW_add {ι : Type*} [Fintype ι] [DecidableEq ι] {E' I' : Type} [Fintype I'] [DecidableEq I'] (A B C : BAGraph E' I') (D : BALData ι)
    (h : ∀ ℓ, A.term D ℓ = B.term D ℓ + C.term D ℓ) (Wt : (E' ⊕ I' → ι) → ℝ) (ℓe : E' → ι) :
    A.valW D Wt ℓe = B.valW D Wt ℓe + C.valW D Wt ℓe := by
  unfold BAGraph.valW
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ℓi _ => by rw [h, mul_add]

/-- **macro (a) with a weight on all the vertices** (weighted `BALvl1A_macroA_graph`): `lanlw` at `p`, the first term split pathwise, `lem_lweight` at the loop of the transfer graph, the weight read
through `owxEmb 2` and then `owxEmb 2` / `owxEmb 4` again -/
theorem BAProv_macroA_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (hσ : p.1.σ = true) (hc : p.1.circ = true)
    (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      ((BAProv_A0 Γ p :: (lwSplit p.2).map (BAGraph.lanlwD Γ p)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      (((BAProv_trA Γ p).lw2 (BAProv_ppA p)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ (owxEmb 2 ∘ owxEmb 2))) ℓe ∂(PF d L W 0)).sum +
      (((BAProv_trA Γ p).lw4 (BAProv_ppA p)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ (owxEmb 4 ∘ owxEmb 2))) ℓe ∂(PF d L W 0)).sum := by
  have h1 := BAProv_lanlw_W hL g0 Em t m hSelf ht0 ht1 Γ p hp hσ hc Wt ℓe
  have hmem : BAProv_ppA p ∈ lwSplit (BAProv_trA Γ p).solid := BALvl1A_lwSplit_last _ _
  have h2 := BAProv_lw_W hL g0 Em t m hSelf ht0 ht1 (BAProv_trA Γ p) (BAProv_ppA p) hmem rfl rfl rfl (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe
  have h3 : ∫ ω, (BAGraph.lanlwT1 Γ p).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) =
      ∫ ω, (BAProv_A0 Γ p).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) +
        ∫ ω, (BAProv_trA Γ p).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) := by
    simp_rw [BAProv_valW_add _ _ _ _ (BAProv_macroA_term Γ p _)]
    exact integral_add (BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 _ _ _) (BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 _ _ _)
  simp only [Function.comp_assoc] at h2
  rw [h1]
  simp only [BAGraph.lanlwTerms, List.map_cons, List.sum_cons, h3, h2]
  ring

/-- the transfer graph of macro (b) (`BAPGraph.splitOuts`) -/
def BAProv_trB (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : BAGraph E (I ⊕ Fin 2) :=
  BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst)]

/-- the four other graphs of the split of the derivative term (`d1`-`d4` of `BAPGraph.splitOuts`) -/
def BAProv_Q4 (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : List (BAGraph E (I ⊕ Fin 2)) :=
  [BALvl1A_dq Γ p q [bpS false (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 0) (owxEmb 2 q.1.dst), bpS false (bpv 1) (owxEmb 2 p.1.dst)] [],
   BALvl1A_dq Γ p q [bpS true (owxEmb 2 q.1.src) (bpv 1)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (bpv 1) (owxEmb 2 p.1.dst)],
   BALvl1A_dq Γ p q [bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1)],
   BALvl1A_dq Γ p q [] [bpM (bpv 0) (owxEmb 2 q.1.dst), bpM (owxEmb 2 q.1.src) (bpv 1), bpM (bpv 1) (owxEmb 2 p.1.dst)]]

/-- the pair of the transfer graph at which `GGGamma` is applied -/
def BAProv_ppB (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
  (bpS true (bpv 1) (owxEmb 2 p.1.dst), q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)])

def BAProv_qqB (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) : SEdge (E ⊕ (I ⊕ Fin 2)) × List (SEdge (E ⊕ (I ⊕ Fin 2))) :=
  (bpS true (owxEmb 2 q.1.src) (bpv 1), q.2.map (SEdge.map (owxEmb 2)))

/-- **macro (b), pathwise** (`BALvl1A_macroB_val` before the sum over the labels): the derivative term at the blue edge `q.1` is the sum of the four graphs of `BAProv_Q4` and the transfer graph -/
theorem BAProv_macroB_term {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hσ : q.1.σ = true) (D : BALData ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) :
    (BAGraph.lanlwD Γ p q).term D ℓ' = ((BAProv_Q4 Γ p q ++ [BAProv_trB Γ p q]).map fun T => T.term D ℓ').sum := by
  rw [BAGraph.lanlwD, BAExpandW_lanlwExt_term]
  unfold BAProv_Q4 BAProv_trB BALvl1A_dq
  simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term, BAWeightOp_ext_term]
  simp only [owxDE, SEdge.map, hσ, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, SEdge.val, WEdge.val, BAMEdge.val, bpS,
    bpW, bpM, bpv]
  simp
  ring

/-- **macro (b) with a weight on all the vertices** (weighted `BALvl1A_macroB_graph`): `lanlw` at `p`, the `j`-th derivative term split pathwise, `GGGamma` at the transfer graph's pair -/
theorem BAProv_macroB_W (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (Γ : BAGraph E I) (p q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q)
    (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) (Wt : (E ⊕ I → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, Γ.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      ((BAGraph.lanlwT1 Γ p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD Γ p)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      ((BAProv_Q4 Γ p q).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
      (((BAProv_trB Γ p q).gg2 (BAProv_ppB p q) (BAProv_qqB q)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ (owxEmb 2 ∘ owxEmb 2))) ℓe ∂(PF d L W 0)).sum +
      (((BAProv_trB Γ p q).gg4 (BAProv_ppB p q) (BAProv_qqB q)).map fun T =>
          ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ (owxEmb 4 ∘ owxEmb 2))) ℓe ∂(PF d L W 0)).sum := by
  have h1 := BAProv_lanlw_W hL g0 Em t m hSelf ht0 ht1 Γ p hp h.1 h.2.1 Wt ℓe
  have hmem : BAProv_ppB p q ∈ lwSplit (BAProv_trB Γ p q).solid := by
    have := BALvl1A_lwSplit_last (q.2.map (SEdge.map (owxEmb 2)) ++ [bpS true (owxEmb 2 q.1.src) (bpv 1)]) (bpS true (bpv 1) (owxEmb 2 p.1.dst))
    rw [List.append_assoc] at this
    exact this
  have hmem2 : BAProv_qqB q ∈ lwSplit (BAProv_ppB p q).2 := BALvl1A_lwSplit_last (q.2.map (SEdge.map (owxEmb 2))) _
  have h2 := BAProv_gg_W hL g0 Em t m hSelf ht0 ht1 (BAProv_trB Γ p q) (BAProv_ppB p q) (BAProv_qqB q) hmem hmem2 rfl rfl rfl rfl rfl
    (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe
  simp only [Function.comp_assoc] at h2
  have h3 : ∫ ω, (BAGraph.lanlwD Γ p q).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) =
      ((BAProv_Q4 Γ p q).map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0)).sum +
        ∫ ω, (BAProv_trB Γ p q).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0) := by
    have e : ∀ ω, (BAGraph.lanlwD Γ p q).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe =
        ((BAProv_Q4 Γ p q).map fun T => T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe).sum +
          (BAProv_trB Γ p q).valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe := by
      intro ω
      have := BAProv_valW_sum _ _ (BAlwData d L W g0 Em t m ω) (BAProv_macroB_term Γ p q h.2.2.1 _) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe
      simpa using this
    simp_rw [e]
    have iQ := owx_integrable_list_sum (P := PF d L W 0) (BAProv_Q4 Γ p q)
      (fun T ω => T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe)
      (fun T _ => BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 _ _ _)
    rw [integral_add iQ (BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 (BAProv_trB Γ p q) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe),
      owx_integral_list_sum (PF d L W 0) (BAProv_Q4 Γ p q)
        (fun T ω => T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe)
        (fun T _ => BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 _ _ _)]
  have e2 := BALvl1A_sum_eraseIdx (fun q' => ∫ ω, (BAGraph.lanlwD Γ p q').valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ owxEmb 2)) ℓe ∂(PF d L W 0))
    (lwSplit p.2) j q hj
  simp only [BAGraph.lanlwTerms, List.map_cons, List.sum_cons, List.map_map, Function.comp_def] at e2 h1 h2 h3 ⊢
  rw [h1, e2, h3, h2]
  ring

end Kinds

/-! ## 4. The weighted expansion of the positions of a step -/

section Prov

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- a child read through `P.ext` has the weighted value of the child at `ℓ'` (weighted `BALvl1A_pcomp_val`) -/
theorem BAProv_pcomp_valW {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (Q : BAPGraph P.E') (D : BALData ι)
    (Wt : (Q.E' ⊕ Q.I' → ι) → ℝ) {ℓe : E → ι} {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) :
    (BALvl1A_pcomp P Q).valW D Wt ℓe = Q.valW D Wt ℓ' := by
  by_cases h : ∃ ℓ'' : Q.E' → ι, ℓ' = ℓ'' ∘ Q.ext
  · obtain ⟨ℓ'', hℓ''⟩ := h
    have h2 : ℓe = ℓ'' ∘ (BALvl1A_pcomp P Q).ext := by rw [hℓ, hℓ'']; rfl
    exact (BAPGraph.valW_of_factor (BALvl1A_pcomp P Q) D Wt h2).trans (BAPGraph.valW_of_factor Q D Wt hℓ'').symm
  · have h3 : ¬ ∃ ℓ3 : (BALvl1A_pcomp P Q).E' → ι, ℓe = ℓ3 ∘ (BALvl1A_pcomp P Q).ext := by
      rintro ⟨ℓ3, hℓ3⟩
      apply h
      refine ⟨ℓ3, ?_⟩
      apply P.ext_surj.injective_comp_right
      exact hℓ.symm.trans hℓ3
    exact (BAPGraph.valW_of_not (BALvl1A_pcomp P Q) D Wt h3).trans (BAPGraph.valW_of_not Q D Wt h).symm

theorem BAProv_pcomp_valW_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (P : BAPGraph E) (Q : BAPGraph P.E') (D : BALData ι)
    (Wt : (Q.E' ⊕ Q.I' → ι) → ℝ) {ℓe : E → ι} (hf : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : (BALvl1A_pcomp P Q).valW D Wt ℓe = 0 := by
  refine BAPGraph.valW_of_not (BALvl1A_pcomp P Q) D Wt ?_
  rintro ⟨ℓ3, hℓ3⟩
  exact hf ⟨ℓ3 ∘ Q.ext, hℓ3⟩

theorem BAProv_integrable_pvalW (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {E : Type} (Q : BAPGraph E) (Wt : (Q.E' ⊕ Q.I' → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    Integrable (fun ω => Q.valW (BAlwData d L W g0 Em t m ω) Wt ℓe) (PF d L W 0) := by
  classical
  by_cases hf : ∃ ℓ' : Q.E' → Idx d L W, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    simp_rw [BAPGraph.valW_of_factor Q _ _ hℓ]
    exact BAProv_integrable_valW hL g0 Em t m hSelf ht0 ht1 _ _ _
  · simp_rw [BAPGraph.valW_of_not Q _ _ hf]
    exact integrable_zero _ _ _

theorem BAProv_provOuts_map (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (emb : P.E' ⊕ P.I' → P.E' ⊕ I') (Ts : List (BAGraph P.E' I')) :
    (BAProv_provOuts P emb Ts).map (·.Q) = P.outsOf Ts := by
  simp [BAProv_provOuts, BAPGraph.outsOf, BAGraph.partition, BAProvOut.ofTerm, BALvl1A_pcomp, List.map_flatMap, List.map_map, Function.comp_def]

theorem BAProv_provOuts_good (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (emb : P.E' ⊕ P.I' → P.E' ⊕ I')
    (Ts : List (BAGraph P.E' I')) (h : ∀ T ∈ Ts, BAProv_Ext P.g emb T) : ∀ o ∈ BAProv_provOuts P emb Ts, o.ExtOK ∧ o.Molecular := by
  intro o ho
  obtain ⟨T, hT, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨T', hT', rfl⟩ := List.mem_map.1 ho
  exact BAProv_ofTerm_good P emb T' ((h T hT).splitG T' hT')

/-- the terms of the partition of a term, read through `P` and the weight through the maps, sum to the weighted value of the term -/
theorem BAProv_splitG_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (emb : P.E' ⊕ P.I' → P.E' ⊕ I')
    (T : BAGraph P.E' I') (D : BALData ι) (Wt : (P.E' ⊕ P.I' → ι) → ℝ) {ℓe : Fin 2 → ι} {ℓ' : P.E' → ι} (hℓ : ℓe = ℓ' ∘ P.ext) :
    ((T.splitG.map (BAProvOut.ofTerm P emb)).map fun o => o.Q.valW D (fun ℓ => Wt (ℓ ∘ o.π)) ℓe).sum = T.valW D (fun ℓ => Wt (ℓ ∘ emb)) ℓ' := by
  rw [BAGraph.valW_partition T D (fun ℓ => Wt (ℓ ∘ emb)) ℓ', List.map_map]
  exact congrArg List.sum (List.map_congr_left fun Δ _ => BAProv_pcomp_valW P Δ.packMerge D _ hℓ)

/-- **the expectation of the weighted values of the positions of a family of terms** (weighted `BALvl1A_pack`) -/
theorem BAProv_provOuts_sum (hL : 3 ≤ L) (g0 Em t : ℝ) (m : ℂ) (hSelf : RBM.BA.BASelf d L g0 (Em : ℂ) m) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (emb : P.E' ⊕ P.I' → P.E' ⊕ I') (Ts : List (BAGraph P.E' I'))
    (Wt : (P.E' ⊕ P.I' → Idx d L W) → ℝ) {ℓe : Fin 2 → Idx d L W} {ℓ' : P.E' → Idx d L W} (hℓ : ℓe = ℓ' ∘ P.ext) :
    ((BAProv_provOuts P emb Ts).map fun o => ∫ ω, o.Q.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ o.π)) ℓe ∂(PF d L W 0)).sum =
      (Ts.map fun T => ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ emb)) ℓ' ∂(PF d L W 0)).sum := by
  have key : ∀ T ∈ Ts, ((T.splitG.map (BAProvOut.ofTerm P emb)).map fun o =>
      ∫ ω, o.Q.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ o.π)) ℓe ∂(PF d L W 0)).sum =
      ∫ ω, T.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ emb)) ℓ' ∂(PF d L W 0) := by
    intro T _
    rw [← owx_integral_list_sum (PF d L W 0) (T.splitG.map (BAProvOut.ofTerm P emb))
      (fun o ω => o.Q.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ o.π)) ℓe)
      (fun o _ => BAProv_integrable_pvalW hL g0 Em t m hSelf ht0 ht1 _ _ _)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => BAProv_splitG_sum P emb T _ Wt hℓ)
  unfold BAProv_provOuts
  rw [lvl1_sum_flatMap]
  exact congrArg List.sum (List.map_congr_left key)

theorem BAProv_provOuts_sum_zero (g0 Em t : ℝ) (m : ℂ) (P : BAPGraph (Fin 2)) {I' : Type} [Fintype I'] [DecidableEq I'] (emb : P.E' ⊕ P.I' → P.E' ⊕ I')
    (Ts : List (BAGraph P.E' I')) (Wt : (P.E' ⊕ P.I' → Idx d L W) → ℝ) {ℓe : Fin 2 → Idx d L W}
    (hf : ¬ ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext) :
    ((BAProv_provOuts P emb Ts).map fun o => ∫ ω, o.Q.valW (BAlwData d L W g0 Em t m ω) (fun ℓ => Wt (ℓ ∘ o.π)) ℓe ∂(PF d L W 0)).sum = 0 := by
  refine List.sum_eq_zero fun a ha => ?_
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ha
  obtain ⟨T, hT, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨Δ, hΔ, rfl⟩ := List.mem_map.1 ho
  exact (integral_congr_ae (Filter.Eventually.of_forall fun ω => BAProv_pcomp_valW_zero P Δ.packMerge _ _ hf)).trans (integral_zero _ _)

/-! ### The five frame kinds: positions with `ExtOK`, `Molecular` and the weighted expansion -/

/-- the positions of a step: `ExtOK`, `Molecular`, the graphs of the step and the weighted expansion -/
def BAProvPosW (d : ℕ) (P : BAPGraph (Fin 2)) (F : List (BAPGraph (Fin 2))) : Prop :=
  ∃ ps : List (BAProvOut P), ps.map (·.Q) = F ∧ (∀ o ∈ ps, o.ExtOK ∧ o.Molecular) ∧ BAWExp d P ps

/-- `weight`: `lw2`, `lw4` -/
theorem BAProv_weight_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true ∧ p.1.src = p.1.dst) :
    BAProvPosW d P (P.outsOf (P.g.lw2 p) ++ P.outsOf (P.g.lw4 p)) := by
  refine ⟨BAProv_provOuts P (owxEmb 2) (P.g.lw2 p) ++ BAProv_provOuts P (owxEmb 4) (P.g.lw4 p), ?_, ?_, ?_⟩
  · rw [List.map_append, BAProv_provOuts_map, BAProv_provOuts_map]
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact BAProv_provOuts_good P _ _ (BAProv_Ext_lw2 P.g hD p) o ho
    · exact BAProv_provOuts_good P _ _ (BAProv_Ext_lw4 P.g hD p) o ho
  · intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp only [List.map_append, List.sum_append, BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
      simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
      exact BAProv_lw_W hL g0 Em t m hS ht0 ht1 P.g p hp h.1 h.2.1 h.2.2 Wt ℓ'
    · simp only [List.map_append, List.sum_append, BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
      simp_rw [BAPGraph.valW_of_not P _ _ hf]
      simp

/-- `edge`: `lanlwTerms` -/
theorem BAProv_edge_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) :
    BAProvPosW d P (P.outsOf (BAGraph.lanlwTerms P.g p)) := by
  refine ⟨BAProv_provOuts P (owxEmb 2) (BAGraph.lanlwTerms P.g p), BAProv_provOuts_map _ _ _,
    BAProv_provOuts_good P _ _ (BAProv_Ext_lanlw P.g hD p), ?_⟩
  intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    rw [BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
    simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
    exact BAProv_lanlw_W hL g0 Em t m hS ht0 ht1 P.g p hp h.1 h.2 Wt ℓ'
  · rw [BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
    simp_rw [BAPGraph.valW_of_not P _ _ hf]
    simp

/-- `gg`: `gg2`, `gg4` -/
theorem BAProv_gg_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (hq : q ∈ lwSplit p.2) (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true)
    (hxy : p.1.src = q.1.dst) : BAProvPosW d P (P.outsOf (P.g.gg2 p q) ++ P.outsOf (P.g.gg4 p q)) := by
  refine ⟨BAProv_provOuts P (owxEmb 2) (P.g.gg2 p q) ++ BAProv_provOuts P (owxEmb 4) (P.g.gg4 p q), ?_, ?_, ?_⟩
  · rw [List.map_append, BAProv_provOuts_map, BAProv_provOuts_map]
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact BAProv_provOuts_good P _ _ (BAProv_Ext_gg2 P.g hD p q) o ho
    · exact BAProv_provOuts_good P _ _ (BAProv_Ext_gg4 P.g hD p q) o ho
  · intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp only [List.map_append, List.sum_append, BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
      simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
      exact BAProv_gg_W hL g0 Em t m hS ht0 ht1 P.g p q hp hq h.1 h.2.1 h.2.2.1 h.2.2.2 hxy Wt ℓ'
    · simp only [List.map_append, List.sum_append, BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
      simp_rw [BAPGraph.valW_of_not P _ _ hf]
      simp

/-- `within` (macro (a)) -/
theorem BAProv_within_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) (p : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (h : p.1.σ = true ∧ p.1.circ = true) : BAProvPosW d P (P.withinOuts p) := by
  have hT : BAProv_Ext P.g (owxEmb 2) (BAProv_trA P.g p) :=
    BAProv_Ext_ext2 P.g hD p.2 [bpS true (bpv 1) (bpv 1)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 p.1.dst)] p.1.src (Or.inl (by simp)) (Or.inr (by simp))
  have e1 : ∀ T ∈ BAProv_A0 P.g p :: (lwSplit p.2).map (BAGraph.lanlwD P.g p), BAProv_Ext P.g (owxEmb 2) T := by
    intro T hT'
    simp only [List.mem_cons, List.mem_map] at hT'
    rcases hT' with rfl | ⟨q, -, rfl⟩
    · exact BAProv_Ext_ext2 P.g hD _ _ _ _ p.1.src (Or.inl (by simp)) (Or.inr (by simp))
    · exact BAProv_Ext_lanlwD P.g hD p q
  have e2 : ∀ T ∈ (BAProv_trA P.g p).lw2 (BAProv_ppA p), BAProv_Ext P.g (owxEmb 2 ∘ owxEmb 2) T :=
    fun T hT' => hT.trans (BAProv_Ext_lw2 _ hT.1 _ T hT')
  have e3 : ∀ T ∈ (BAProv_trA P.g p).lw4 (BAProv_ppA p), BAProv_Ext P.g (owxEmb 4 ∘ owxEmb 2) T :=
    fun T hT' => hT.trans (BAProv_Ext_lw4 _ hT.1 _ T hT')
  refine ⟨BAProv_provOuts P (owxEmb 2) (BAProv_A0 P.g p :: (lwSplit p.2).map (BAGraph.lanlwD P.g p)) ++
    BAProv_provOuts P (owxEmb 2 ∘ owxEmb 2) ((BAProv_trA P.g p).lw2 (BAProv_ppA p)) ++
    BAProv_provOuts P (owxEmb 4 ∘ owxEmb 2) ((BAProv_trA P.g p).lw4 (BAProv_ppA p)), ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, BAProv_provOuts_map, BAProv_provOuts_map, BAProv_provOuts_map]
    rfl
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · rcases List.mem_append.1 ho with ho | ho
      · exact BAProv_provOuts_good P _ _ e1 o ho
      · exact BAProv_provOuts_good P _ _ e2 o ho
    · exact BAProv_provOuts_good P _ _ e3 o ho
  · intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp only [List.map_append, List.sum_append, BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
      simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
      exact BAProv_macroA_W hL g0 Em t m hS ht0 ht1 P.g p hp h.1 h.2 Wt ℓ'
    · simp only [List.map_append, List.sum_append, BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
      simp_rw [BAPGraph.valW_of_not P _ _ hf]
      simp

/-- `ggSplit` (macro (b)) -/
theorem BAProv_ggSplit_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) (p q : SEdge (P.E' ⊕ P.I') × List (SEdge (P.E' ⊕ P.I')))
    (hp : p ∈ lwSplit P.g.solid) (j : ℕ) (hj : (lwSplit p.2)[j]? = some q) (h : p.1.σ = true ∧ p.1.circ = true ∧ q.1.σ = true ∧ q.1.circ = true) :
    BAProvPosW d P (P.splitOuts p q j) := by
  have hT : BAProv_Ext P.g (owxEmb 2) (BAProv_trB P.g p q) :=
    BAProv_Ext_ext2 P.g hD q.2 [bpS true (owxEmb 2 q.1.src) (bpv 1), bpS true (bpv 1) (owxEmb 2 p.1.dst)] [bpW false (bpv 0) (bpv 1)]
      [bpM (owxEmb 2 p.1.src) (bpv 0), bpM (bpv 0) (owxEmb 2 q.1.dst)] p.1.src (Or.inl (by simp)) (Or.inr (by simp))
  have e1 : ∀ T ∈ BAGraph.lanlwT1 P.g p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD P.g p), BAProv_Ext P.g (owxEmb 2) T := by
    intro T hT'
    simp only [List.mem_cons, List.mem_map] at hT'
    rcases hT' with rfl | ⟨r, -, rfl⟩
    · exact BAProv_Ext_lanlwT1 P.g hD p
    · exact BAProv_Ext_lanlwD P.g hD p r
  have e2 : ∀ T ∈ BAProv_Q4 P.g p q, BAProv_Ext P.g (owxEmb 2) T := by
    intro T hT'
    simp only [BAProv_Q4, List.mem_cons, List.not_mem_nil, or_false] at hT'
    rcases hT' with rfl | rfl | rfl | rfl
    all_goals exact BAProv_Ext_ext2 P.g hD _ _ _ _ p.1.src (Or.inl (by simp)) (Or.inr (by simp))
  have e3 : ∀ T ∈ (BAProv_trB P.g p q).gg2 (BAProv_ppB p q) (BAProv_qqB q), BAProv_Ext P.g (owxEmb 2 ∘ owxEmb 2) T :=
    fun T hT' => hT.trans (BAProv_Ext_gg2 _ hT.1 _ _ T hT')
  have e4 : ∀ T ∈ (BAProv_trB P.g p q).gg4 (BAProv_ppB p q) (BAProv_qqB q), BAProv_Ext P.g (owxEmb 4 ∘ owxEmb 2) T :=
    fun T hT' => hT.trans (BAProv_Ext_gg4 _ hT.1 _ _ T hT')
  refine ⟨BAProv_provOuts P (owxEmb 2) (BAGraph.lanlwT1 P.g p :: ((lwSplit p.2).eraseIdx j).map (BAGraph.lanlwD P.g p)) ++
    BAProv_provOuts P (owxEmb 2) (BAProv_Q4 P.g p q) ++
    BAProv_provOuts P (owxEmb 2 ∘ owxEmb 2) ((BAProv_trB P.g p q).gg2 (BAProv_ppB p q) (BAProv_qqB q)) ++
    BAProv_provOuts P (owxEmb 4 ∘ owxEmb 2) ((BAProv_trB P.g p q).gg4 (BAProv_ppB p q) (BAProv_qqB q)), ?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append, List.map_append, BAProv_provOuts_map, BAProv_provOuts_map, BAProv_provOuts_map, BAProv_provOuts_map]
    rfl
  · intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · rcases List.mem_append.1 ho with ho | ho
      · rcases List.mem_append.1 ho with ho | ho
        · exact BAProv_provOuts_good P _ _ e1 o ho
        · exact BAProv_provOuts_good P _ _ e2 o ho
      · exact BAProv_provOuts_good P _ _ e3 o ho
    · exact BAProv_provOuts_good P _ _ e4 o ho
  · intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
    by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
    · obtain ⟨ℓ', hℓ⟩ := hf
      simp only [List.map_append, List.sum_append, BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
      simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
      exact BAProv_macroB_W hL g0 Em t m hS ht0 ht1 P.g p q hp j hj h Wt ℓ'
    · simp only [List.map_append, List.sum_append, BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
      simp_rw [BAPGraph.valW_of_not P _ _ hf]
      simp

/-- **one frame step with positions** (target 4 with the weighted expansion, for all five kinds) -/
theorem BAProv_frameStep_posW (d : ℕ) (P : BAPGraph (Fin 2)) (hD : ∀ e ∈ P.g.dotted, e.eq = false) {F : List (BAPGraph (Fin 2))}
    (h : BAFrameStep P F) : BAProvPosW d P F := by
  cases h with
  | weight p hp h => exact BAProv_weight_posW d P hD p hp h
  | within p hp h => exact BAProv_within_posW d P hD p hp ⟨h.1, h.2.1⟩
  | edge p hp h x hx hwf hv hint hbad => exact BAProv_edge_posW d P hD p hp h
  | gg p hp q hq h x hx hwf hint hnb => exact BAProv_gg_posW d P hD p q hp hq h (hx.1.trans hx.2.symm)
  | ggSplit p hp q j hj h a a' hx hne hsame hwf hint hnb => exact BAProv_ggSplit_posW d P hD p q hp j hj h

end Prov

/-! ## 5. The twist and the step lemma with positions (target 6) -/

section Twist

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- **the weighted value of a twist** (weighted `BALvl1A_pval_twist`; pathwise `BASymm1_term_twist`): the conjugate (if `c`) of the weighted value at the transposed (if `t`) data -/
theorem BAProv_twist_valW {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type} (Q : BAPGraph E) (D : BALData ι) (hS : ∀ i j, star (D.S i j) = D.S i j)
    (hP : ∀ i j, star (D.gPsi i j) = D.gPsi i j) (c t : Bool) (Wt : (Q.E' ⊕ Q.I' → ι) → ℝ) (ℓe : E → ι) :
    (Q.twist c t).valW D Wt ℓe = lwSymmCj c (Q.valW (BASymm1_dataTr D t) Wt ℓe) := by
  by_cases h : ∃ ℓ' : Q.E' → ι, ℓe = ℓ' ∘ Q.ext
  · obtain ⟨ℓ', hℓ⟩ := h
    rw [BAPGraph.valW_of_factor (Q.twist c t) D Wt hℓ, BAPGraph.valW_of_factor Q _ Wt hℓ]
    change (Q.g.twist c t).valW D Wt ℓ' = _
    unfold BAGraph.valW
    simp only [BAGraph.BASymm1_term_twist D hS hP, map_sum, map_mul]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    cases c <;> simp [lwSymmCj]
  · rw [BAPGraph.valW_of_not (Q.twist c t) D Wt h, BAPGraph.valW_of_not Q _ Wt h, map_zero]

/-- the twist in expectation, with a weight (weighted `baTwistComb_holds`; `baTwistIntegral_gen`) -/
theorem BAProv_twist_EW (g0 Em t : ℝ) (m : ℂ) {E : Type} (Q : BAPGraph E) (c t' : Bool) (Wt : (Q.E' ⊕ Q.I' → Idx d L W) → ℝ) (ℓe : E → Idx d L W) :
    ∫ ω, (Q.twist c t').valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0) =
      lwSymmCj c (∫ ω, Q.valW (BAlwData d L W g0 Em t m ω) Wt ℓe ∂(PF d L W 0)) := by
  have h1 : ∀ ω, (Q.twist c t').valW (BAlwData d L W g0 Em t m ω) Wt ℓe =
      lwSymmCj c (Q.valW (BASymm1_dataTr (BAlwData d L W g0 Em t m ω) t') Wt ℓe) := fun ω =>
    BAProv_twist_valW Q _ (BASymm1_data_real d L W g0 Em t m ω).1 (BASymm1_data_real d L W g0 Em t m ω).2 c t' Wt ℓe
  simp only [h1]
  exact baTwistIntegral_gen d L W g0 Em t m c t' (fun D => Q.valW D Wt ℓe)

/-- **the twist of a weighted expansion** (`BAWExp` at `P.twist c t`, the maps unchanged) -/
theorem BAWExp.twist {d : ℕ} {P : BAPGraph (Fin 2)} {ps : List (BAProvOut P)} (c t' : Bool) (h : BAWExp d P ps) :
    BAWExp d (P.twist c t') (ps.map (BAProvOut.twist c t')) := by
  intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
  rw [BAProv_twist_EW g0 Em t m P c t' Wt ℓe, h L W hL g0 Em t m hS ht0 ht1 Wt ℓe, map_list_sum, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun o _ => ?_)
  exact (BAProv_twist_EW g0 Em t m o.Q c t' _ ℓe).symm

theorem BAProv_twist_posW (d : ℕ) (c t : Bool) {P : BAPGraph (Fin 2)} {F : List (BAPGraph (Fin 2))} (h : BAProvPosW d P F) :
    BAProvPosW d (P.twist c t) (F.map (BAPGraph.twist c t)) := by
  obtain ⟨ps, rfl, hps, hW⟩ := h
  refine ⟨ps.map (BAProvOut.twist c t), by simp [BAProvOut.twist, Function.comp_def], fun o ho => ?_, hW.twist c t⟩
  obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.1 ho
  obtain ⟨hE, h1, h2⟩ := hps o₀ ho₀
  refine ⟨hE, fun v w hvw => (BAProv_twist_mol_iff c t _ _ _).2 (h1 v w ((BAProv_twist_mol_iff c t _ _ _).1 hvw)), fun c' hc' => ?_⟩
  induction c' using SimpleGraph.ConnectedComponent.ind with | h w => ?_
  obtain ⟨v, hv, hvw⟩ := h2 (o₀.Q.g.shadow.molOf w) fun ⟨a, ha⟩ => hc' ⟨a, (BAProv_twist_mol_iff c t _ _ _).2 ha⟩
  exact ⟨v, fun ⟨a, ha⟩ => hv ⟨a, (BAProv_twist_mol_iff c t _ _ _).1 ha⟩, (BAProv_twist_mol_iff c t _ _ _).2 hvw⟩

/-- **the step lemma with positions** (target 6; the content of `lwProv_LocStepXProvPos`, `LWProv:1791`, without tags): the outputs of a `BALocStep` of a normal graph come with maps that are
`ExtOK` and `Molecular`, and the weighted expansion `BAWExp` -/
def BAProvStepPos (d : ℕ) : Prop :=
  ∀ (P : BAPGraph (Fin 2)) (L : List (BAPGraph (Fin 2))), BALocStep P L → P.g.Normal →
    ∃ ps : List (BAProvOut P), ps.map (·.Q) = L ∧ (∀ o ∈ ps, o.ExtOK ∧ o.Molecular) ∧ BAWExp d P ps

theorem baProv_stepPos (d : ℕ) : BAProvStepPos d := by
  intro P L hL hN
  obtain ⟨c, t, F, hF, rfl⟩ := hL
  have hN' : (P.twist c t).g.Normal := (ba_twist_inv_out c t P.g).2.2.2.2.2 hN
  have := BAProv_twist_posW d c t (BAProv_frameStep_posW d (P.twist c t) hN'.1 hF)
  rwa [BALvl1A_twist_invol] at this

end Twist

/-! ## 6. The recursion with provenance (target 7) -/

section Rec

variable {d : ℕ}

/-- the body of `BAlvl1Lemma` (`BALvl1C:53-61`) at `E = Fin 2`: the lists `outs`, `errs` of graphs -/
def BAProv_Lvl1Body (d : ℕ) (K : ℤ) (P : BAPGraph (Fin 2)) (outs errs : List (BAPGraph (Fin 2))) : Prop :=
  (∀ Q ∈ outs, Q.g.LocStd ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.scalingOrder < K) ∧ (∀ Q ∈ errs, K ≤ Q.g.scalingOrder) ∧
    (∀ Q ∈ outs ++ errs, BAReach K P Q ∧ Q.g.Normal ∧ P.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ P.g.nM ∧
      (Q.g.nA : ℤ) - Q.g.nW ≤ (P.g.nA : ℤ) - P.g.nW) ∧
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : Fin 2 → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (outs ++ errs) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0)

/-- the leaf: the identity map is `ExtOK` and `Molecular` -/
theorem BAProv_id_good (Γ : BAPGraph (Fin 2)) : (⟨Γ, id⟩ : BAProvOut Γ).ExtOK ∧ (⟨Γ, id⟩ : BAProvOut Γ).Molecular := by
  refine ⟨fun i => rfl, fun v w h => h, fun c hc => ?_⟩
  induction c using SimpleGraph.ConnectedComponent.ind with | h w => exact ⟨w, hc, rfl⟩

/-- **composition of weighted expansions, with positions** (`lwProv_WExp_comp_pos`, `LWProv:1531`): the outputs of `ps` expand into `c₁ o ++ c₂ o`, listed as the composites of all `c₁` and then all `c₂` -/
theorem BAProv_comp_pos {P : BAPGraph (Fin 2)} {ps : List (BAProvOut P)} (h : BAWExp d P ps) (c₁ c₂ : ∀ o : BAProvOut P, List (BAProvOut o.Q))
    (h' : ∀ o ∈ ps, BAWExp d o.Q (c₁ o ++ c₂ o)) :
    BAWExp d P (ps.flatMap (fun o => (c₁ o).map o.comp) ++ ps.flatMap (fun o => (c₂ o).map o.comp)) := by
  intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
  rw [h L W hL g0 Em t m hS ht0 ht1 Wt ℓe, List.map_append, List.sum_append, lvl1_sum_flatMap, lvl1_sum_flatMap, ← List.sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  have := h' o ho L W hL g0 Em t m hS ht0 ht1 (fun ℓ => Wt (ℓ ∘ o.π)) ℓe
  rw [List.map_append, List.sum_append] at this
  rw [List.map_map, List.map_map]
  exact this

/-- the identity of expectations of `BAlvl1Lemma` from the weighted expansion at the weight `1` -/
theorem BAWExp.val_identity {P : BAPGraph (Fin 2)} {ps : List (BAProvOut P)} (h : BAWExp d P ps) :
    ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 Em t : ℝ) (m : ℂ), RBM.BA.BASelf d L g0 (Em : ℂ) m → 0 ≤ t → t < 1 → ∀ ℓe : Fin 2 → Idx d L W,
      ∫ ω, P.val (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) = ∫ ω, BAComb.val (ps.map (·.Q)) (BAlwData d L W g0 Em t m ω) ℓe ∂(PF d L W 0) := by
  intro L W _ _ hL g0 Em t m hS ht0 ht1 ℓe
  have h1 := h L W hL g0 Em t m hS ht0 ht1 (fun _ => 1) ℓe
  simp only [BAPGraph.valW_one] at h1
  rw [BAEngine_integral_comb hL g0 Em t m hS ht0 ht1 _ ℓe, h1, List.map_map]
  rfl

/-- **the recursion with provenance, with the non-emptiness of the lists** (`lwProv_exists`, `LWProv:1560`, without tags; `BALvl1C_aux`, `BALvl1C:482`, with maps): by strong induction on the measure `BALvl1Mu` -/
theorem BAProv_aux (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ (∀ o ∈ oP, o.Q.g.LocStd ∧ o.Q.g.scalingOrder < K) ∧
      (∀ o ∈ eP, K ≤ o.Q.g.scalingOrder) ∧ (∀ o ∈ oP ++ eP, BAReach K Γ o.Q) ∧ oP ++ eP ≠ [] ∧ BAWExp d Γ (oP ++ eP) := by
  classical
  induction Γ using (InvImage.wf (BALvl1Mu K) baLvl1Lt_wf).induction with
  | _ Γ ih =>
    by_cases hK : K ≤ Γ.g.scalingOrder
    · refine ⟨[], [⟨Γ, id⟩], ?_, by simp, ?_, ?_, by simp, by simpa using BAWExp.refl d Γ⟩
      · intro o ho; simp only [List.nil_append, List.mem_singleton] at ho; subst ho; exact BAProv_id_good Γ
      · intro o ho; simp only [List.mem_singleton] at ho; subst ho; exact hK
      · intro o ho; simp only [List.nil_append, List.mem_singleton] at ho; subst ho; exact BAReach.refl Γ
    by_cases hL : Γ.g.LocStd
    · refine ⟨[⟨Γ, id⟩], [], ?_, ?_, by simp, ?_, by simp, by simpa using BAWExp.refl d Γ⟩
      · intro o ho; simp only [List.append_nil, List.mem_singleton] at ho; subst ho; exact BAProv_id_good Γ
      · intro o ho; simp only [List.mem_singleton] at ho; subst ho; exact ⟨hL, show Γ.g.scalingOrder < K by omega⟩
      · intro o ho; simp only [List.append_nil, List.mem_singleton] at ho; subst ho; exact BAReach.refl Γ
    obtain ⟨L, hst⟩ := baLvl1ExistsStep_holds Γ hN hL
    have hgood := baLvl1StepGood_holds Γ L hst hN
    have hlt : Γ.g.scalingOrder < K := not_le.1 hK
    have hLne : L ≠ [] := by
      obtain ⟨c, t, F, hF, hLF⟩ := hst
      rw [hLF]; simpa using BAEngine_frame_ne_nil hF
    obtain ⟨ps, hpsL, hpsok, hpsW⟩ := baProv_stepPos d Γ L hst hN
    have hmem : ∀ o ∈ ps, o.Q ∈ L := fun o ho => hpsL ▸ List.mem_map_of_mem ho
    have hall : ∀ o : BAProvOut Γ, ∃ oc ec : List (BAProvOut o.Q), o ∈ ps →
        (∀ o' ∈ oc ++ ec, o'.ExtOK ∧ o'.Molecular) ∧ (∀ o' ∈ oc, o'.Q.g.LocStd ∧ o'.Q.g.scalingOrder < K) ∧ (∀ o' ∈ ec, K ≤ o'.Q.g.scalingOrder) ∧
          (∀ o' ∈ oc ++ ec, BAReach K o.Q o'.Q) ∧ oc ++ ec ≠ [] ∧ BAWExp d o.Q (oc ++ ec) := by
      intro o
      by_cases ho : o ∈ ps
      · obtain ⟨oc, ec, h⟩ := ih o.Q (ba_lvl1_mu_lt hlt (hgood o.Q (hmem o ho)).2) (hgood o.Q (hmem o ho)).1
        exact ⟨oc, ec, fun _ => h⟩
      · exact ⟨[], [], fun h => absurd h ho⟩
    choose foP feP hfoP using hall
    refine ⟨ps.flatMap fun o => (foP o).map o.comp, ps.flatMap fun o => (feP o).map o.comp, fun o2 ho2 => ?_, fun o2 ho2 => ?_,
      fun o2 ho2 => ?_, fun o2 ho2 => ?_, ?_, BAProv_comp_pos hpsW foP feP fun o ho => (hfoP o ho).2.2.2.2.2⟩
    · simp only [List.mem_append, List.mem_flatMap, List.mem_map] at ho2
      rcases ho2 with ⟨o, ho, o', ho', rfl⟩ | ⟨o, ho, o', ho', rfl⟩
      · have h := (hfoP o ho).1 o' (List.mem_append_left _ ho')
        exact ⟨BAProvOut.ExtOK.comp (hpsok o ho).1 h.1, BAProvOut.Molecular.comp (hpsok o ho).2 h.2⟩
      · have h := (hfoP o ho).1 o' (List.mem_append_right _ ho')
        exact ⟨BAProvOut.ExtOK.comp (hpsok o ho).1 h.1, BAProvOut.Molecular.comp (hpsok o ho).2 h.2⟩
    · simp only [List.mem_flatMap, List.mem_map] at ho2
      obtain ⟨o, ho, o', ho', rfl⟩ := ho2
      exact (hfoP o ho).2.1 o' ho'
    · simp only [List.mem_flatMap, List.mem_map] at ho2
      obtain ⟨o, ho, o', ho', rfl⟩ := ho2
      exact (hfoP o ho).2.2.1 o' ho'
    · have hreach : ∀ o ∈ ps, BAReach K Γ o.Q := fun o ho => BAReach.step Γ Γ o.Q L (BAReach.refl Γ) hlt hL hst (hmem o ho)
      simp only [List.mem_append, List.mem_flatMap, List.mem_map] at ho2
      rcases ho2 with ⟨o, ho, o', ho', rfl⟩ | ⟨o, ho, o', ho', rfl⟩
      · exact (hreach o ho).trans ((hfoP o ho).2.2.2.1 o' (List.mem_append_left _ ho'))
      · exact (hreach o ho).trans ((hfoP o ho).2.2.2.1 o' (List.mem_append_right _ ho'))
    · have hpsne : ps ≠ [] := fun h0 => hLne (by rw [h0] at hpsL; simpa using hpsL.symm)
      obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hpsne
      intro hE
      have h1 := (hfoP o ho).2.2.2.2.1
      obtain ⟨o', ho'⟩ := List.exists_mem_of_ne_nil _ h1
      rcases List.mem_append.1 ho' with ho' | ho'
      · have : o.comp o' ∈ ps.flatMap fun o => (foP o).map o.comp := List.mem_flatMap.2 ⟨o, ho, List.mem_map_of_mem ho'⟩
        rw [List.append_eq_nil_iff.1 hE |>.1] at this
        simp at this
      · have : o.comp o' ∈ ps.flatMap fun o => (feP o).map o.comp := List.mem_flatMap.2 ⟨o, ho, List.mem_map_of_mem ho'⟩
        rw [List.append_eq_nil_iff.1 hE |>.2] at this
        simp at this

/-- **the recursion with provenance, with the non-emptiness of the lists** -/
theorem BAProv_exists_ne (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ BAProv_Lvl1Body d K Γ (oP.map (·.Q)) (eP.map (·.Q)) ∧
      oP ++ eP ≠ [] ∧ BAWExp d Γ (oP ++ eP) := by
  obtain ⟨oP, eP, hok, hout, herr, hreach, hne, hW⟩ := BAProv_aux d K Γ hN
  refine ⟨oP, eP, hok, ?_, hne, hW⟩
  have hinv : ∀ o ∈ oP ++ eP, o.Q.g.Normal ∧ Γ.g.scalingOrder ≤ o.Q.g.scalingOrder ∧ o.Q.g.nM ≤ Γ.g.nM ∧
      (o.Q.g.nA : ℤ) - o.Q.g.nW ≤ (Γ.g.nA : ℤ) - Γ.g.nW := by
    intro o ho
    refine ba_lvl1_induction (hreach o ho) (fun Q => Q.g.Normal ∧ Γ.g.scalingOrder ≤ Q.g.scalingOrder ∧ Q.g.nM ≤ Γ.g.nM ∧
        (Q.g.nA : ℤ) - Q.g.nW ≤ (Γ.g.nA : ℤ) - Γ.g.nW) ⟨hN, le_refl _, le_refl _, le_refl _⟩ ?_
    intro A L hst hA B hB
    obtain ⟨hBN, hg⟩ := baLvl1StepGood_holds A L hst hA.1 B hB
    obtain ⟨h1, h2, h3, -⟩ := hg
    exact ⟨hBN, le_trans hA.2.1 h1, le_trans h2 hA.2.2.1, by have := hA.2.2.2; omega⟩
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun Q hQ => ?_, fun L W _ _ hL g0 Em t m hS ht0 ht1 ℓe => ?_⟩
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hQ
    exact ⟨(hout o ho).1, (hinv o (List.mem_append_left _ ho)).2.1, (hout o ho).2⟩
  · obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hQ
    exact herr o ho
  · rw [← List.map_append] at hQ
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hQ
    exact ⟨hreach o ho, hinv o ho⟩
  · rw [hW.val_identity L W hL g0 Em t m hS ht0 ht1 ℓe, List.map_append]

/-- **the recursion with provenance** (target 7): per normal `Γ` and cutoff `K`, lists `oP eP` of outputs with maps, `ExtOK ∧ Molecular`, the conclusion of `BAlvl1Lemma` for their graphs and the weighted expansion -/
theorem baProv_exists (d : ℕ) (K : ℤ) (Γ : BAPGraph (Fin 2)) (hN : Γ.g.Normal) :
    ∃ oP eP : List (BAProvOut Γ), (∀ o ∈ oP ++ eP, o.ExtOK ∧ o.Molecular) ∧ BAProv_Lvl1Body d K Γ (oP.map (·.Q)) (eP.map (·.Q)) ∧
      BAWExp d Γ (oP ++ eP) := by
  obtain ⟨oP, eP, hok, hb, -, hW⟩ := BAProv_exists_ne d K Γ hN
  exact ⟨oP, eP, hok, hb, hW⟩

/-- the body is the conclusion of `BAlvl1Lemma` (a check of the statement) -/
example (h : BAlvl1Lemma d) (K : ℤ) (P : BAPGraph (Fin 2)) (hN : P.g.Normal) : ∃ outs errs : List (BAPGraph (Fin 2)), BAProv_Lvl1Body d K P outs errs :=
  h K P hN

end Rec

/-! ## 7. The engine with provenance (target 8) -/

section Engine

/-- the outputs of the start graph: one per term of the partition of `G = Ǧ + M` (the `4^p` terms, merged), with the map `vmap` -/
def BAProv_startOuts (p : ℕ) : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) :=
  BAProv_provOuts (baPG (BAGraph.ofLGraph (fxyPowGraph p))) id [(baPG (BAGraph.ofLGraph (fxyPowGraph p))).g]

/-- the weighted partition: a packed graph expands into the terms of the partition of its graph, with the maps `vmap` (the start of the engine; `BAGraph.valW_partition`) -/
theorem BAProv_start_W (d : ℕ) (P : BAPGraph (Fin 2)) : BAWExp d P (BAProv_provOuts P id [P.g]) := by
  intro L W _ _ hL g0 Em t m hS ht0 ht1 Wt ℓe
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓe = ℓ' ∘ P.ext
  · obtain ⟨ℓ', hℓ⟩ := hf
    rw [BAProv_provOuts_sum hL g0 Em t m hS ht0 ht1 P _ _ Wt hℓ]
    simp_rw [BAPGraph.valW_of_factor P _ _ hℓ]
    simp
  · rw [BAProv_provOuts_sum_zero g0 Em t m P _ _ Wt hf]
    simp_rw [BAPGraph.valW_of_not P _ _ hf]
    simp

theorem BAProv_startOuts_map (p : ℕ) : (BAProv_startOuts p).map (·.Q) = (BAGraph.ofLGraph (fxyPowGraph p)).partition := by
  rw [BAProv_startOuts, BAProv_provOuts_map]
  simp [BAPGraph.outsOf, BAGraph.partition, baPG]
  intro a _
  rfl

theorem BAProv_startOuts_mem (p : ℕ) (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) (ho : o ∈ BAProv_startOuts p) :
    ∃ T : BAGraph (Fin 2) (Fin (2 * p)), T ∈ (BAGraph.ofLGraph (fxyPowGraph p)).splitG ∧
      o = BAProvOut.ofTerm (baPG (BAGraph.ofLGraph (fxyPowGraph p))) id T := by
  obtain ⟨T0, hT0, ho⟩ := List.mem_flatMap.1 ho
  obtain rfl := List.mem_singleton.1 hT0
  obtain ⟨T, hT, rfl⟩ := List.mem_map.1 ho
  exact ⟨T, hT, rfl⟩

/-- every start output is `ExtOK`, `Molecular`, and the images of the `β^{(k)}` cover its internal shadow molecules (the explicit form of `BAProv_start`) -/
theorem BAProv_startOuts_good (p : ℕ) : ∀ o ∈ BAProv_startOuts p, o.ExtOK ∧ o.Molecular ∧
    BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k)) := by
  intro o ho
  obtain ⟨T, hT, rfl⟩ := BAProv_startOuts_mem p o ho
  have hΓ : ∀ e ∈ (BAGraph.ofLGraph (fxyPowGraph p)).dotted, e.eq = false := by
    intro e he
    obtain ⟨i, hi⟩ := (localReg_fxy_mem_dotted e).1 he
    rcases hi with rfl | rfl <;> rfl
  have hExt := (BAProv_Ext.refl _ hΓ).splitG T hT
  obtain ⟨hE, hM⟩ := BAProv_ofTerm_good (baPG (BAGraph.ofLGraph (fxyPowGraph p))) id T hExt
  refine ⟨hE, hM, ?_⟩
  refine BAProv_cover_term T hExt.1 (fun k : Fin p => (Sum.inr (localReg_fxyBeta k) : Fin 2 ⊕ Fin (2 * p))) fun w hw => ?_
  rcases w with a | j
  · exact absurd (SimpleGraph.Reachable.refl _) (hw a)
  · obtain ⟨i, hi⟩ : ∃ i : Fin p, j = localReg_fxyAlpha i ∨ j = localReg_fxyBeta i := by
      have h2 : j.1 / 2 < p := by have := j.2; omega
      refine ⟨⟨j.1 / 2, h2⟩, ?_⟩
      by_cases hj : j.1 % 2 = 0
      · exact Or.inl (Fin.ext (by simp [localReg_fxyAlpha]; omega))
      · exact Or.inr (Fin.ext (by simp [localReg_fxyBeta]; omega))
    refine ⟨i, ?_⟩
    rcases hi with rfl | rfl
    · refine BAProv_adj_reach T ?_
      simp only [BAGraph.splitG, List.mem_map] at hT
      obtain ⟨r, hr, rfl⟩ := hT
      simp only [BAGraph.adj, LGraph.adj, Bool.or_eq_true, List.any_eq_true]
      exact Or.inl (Or.inl ⟨⟨false, true, Sum.inr (localReg_fxyAlpha i), Sum.inr (localReg_fxyBeta i)⟩,
        (localReg_fxy_mem_waved _).2 ⟨i, rfl⟩, by simp⟩)
    · exact SimpleGraph.Reachable.refl _

/-- the conclusion of `BAlvl1LemmaSize` at a start term from the body at the cutoff `K = lvl1Cutoff` (as `baLvl1LemmaSize_holds`, `BALvl1C:545`) -/
private theorem BAProv_Lvl1Body_spec (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) (P : BAPGraph (Fin 2)) (outs errs : List (BAPGraph (Fin 2)))
    (h : BAProv_Lvl1Body d (lvl1Cutoff c K0 d D P.g.counters : ℤ) P outs errs) : BAEngine_Spec c K0 d D P outs errs := by
  obtain ⟨hout, herr, hall, hid⟩ := h
  refine ⟨fun Q hQ => ⟨(hout Q hQ).1, (hout Q hQ).2.1⟩, ?_, hall, hid⟩
  intro Q hQ W L Ψ hW hL hLW hlow hup
  obtain ⟨-, -, -, hM, hV⟩ := hall Q (List.mem_append_right _ hQ)
  exact lvl1_size_le c hc K0 d D P.g.counters W L Ψ hW hL hLW hlow hup Q.g.counters (herr Q hQ) hM hV

/-- **the BA `lem:localregular` with provenance, with non-empty lists** (twin of `lw_localregularXP`, `LWProv:1680`, without tags and `∀ m`): per start term the recursion of target 7 at
`lvl1Cutoff c K0 d D P0.g.counters`, composed with the start maps; the assembly `baEngine_assemble` with the binder discharged by `baShapeLL_e2_tn`, `baShapeLL_macroA_tn`, `baShapeLL_macroB_tn` -/
theorem ba_localregularXP_ne (p : ℕ) (c : ℝ) (hc : 0 < c) (K0 d : ℕ) (D : ℝ) :
    ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))), outs ++ errs ≠ [] ∧
      (∀ o ∈ outs ++ errs, o.ExtOK ∧ BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k))) ∧
      BALocRegConcl p c K0 d D (outs.map (·.Q)) (errs.map (·.Q)) ∧
      (∀ o ∈ outs ++ errs, p ≤ o.Q.g.waved.countP (fun e => !e.col)) ∧
      BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) (outs ++ errs) := by
  classical
  have hX : ∀ sh, sh = BAShape.e2 ∨ sh = BAShape.macroA ∨ sh = BAShape.macroB → BAShapeLL sh BAFrameStepTN := by
    intro sh h
    rcases h with rfl | rfl | rfl
    · exact baShapeLL_e2_tn
    · exact baShapeLL_macroA_tn
    · exact baShapeLL_macroB_tn
  have hall : ∀ P0 : BAPGraph (Fin 2), ∃ oc ec : List (BAProvOut P0), P0.g.Normal → (∀ o ∈ oc ++ ec, o.ExtOK ∧ o.Molecular) ∧
      BAProv_Lvl1Body d (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 (oc.map (·.Q)) (ec.map (·.Q)) ∧ oc ++ ec ≠ [] ∧ BAWExp d P0 (oc ++ ec) := by
    intro P0
    by_cases hN : P0.g.Normal
    · obtain ⟨oc, ec, h⟩ := BAProv_exists_ne d (lvl1Cutoff c K0 d D P0.g.counters : ℤ) P0 hN
      exact ⟨oc, ec, fun _ => h⟩
    · exact ⟨[], [], fun h => absurd h hN⟩
  choose foP feP hfoP using hall
  have hmapQ := BAProv_startOuts_map p
  have hN0 : ∀ o ∈ BAProv_startOuts p, o.Q.g.Normal := by
    intro o ho
    have : o.Q ∈ (BAGraph.ofLGraph (fxyPowGraph p)).partition := by rw [← hmapQ]; exact List.mem_map_of_mem ho
    exact BAGraph.partition_normal _ o.Q this
  have hmapO : ∀ F : ∀ P0 : BAPGraph (Fin 2), List (BAProvOut P0),
      ((BAProv_startOuts p).flatMap fun o => (F o.Q).map o.comp).map (·.Q) =
        (BAGraph.ofLGraph (fxyPowGraph p)).partition.flatMap fun P0 => (F P0).map (·.Q) := by
    intro F
    rw [List.map_flatMap, ← hmapQ, List.flatMap_map]
    refine List.flatMap_congr fun o _ => ?_
    simp [List.map_map, Function.comp_def, BAProvOut.comp]
  have hconcl : BALocRegConcl p c K0 d D (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fun P0 => (foP P0).map (·.Q))
      (((BAGraph.ofLGraph (fxyPowGraph p)).partition).flatMap fun P0 => (feP P0).map (·.Q)) :=
    baEngine_assemble hX p c K0 d D (fun P0 => (foP P0).map (·.Q)) (fun P0 => (feP P0).map (·.Q))
      fun P0 hP0 => BAProv_Lvl1Body_spec c hc K0 d D P0 _ _ ((hfoP P0 (BAGraph.partition_normal _ P0 hP0)).2.1)
  rw [← hmapO foP, ← hmapO feP] at hconcl
  refine ⟨(BAProv_startOuts p).flatMap fun o => (foP o.Q).map o.comp, (BAProv_startOuts p).flatMap fun o => (feP o.Q).map o.comp, ?_, ?_, hconcl, ?_,
    BAProv_comp_pos (BAProv_start_W d _) (fun o => foP o.Q) (fun o => feP o.Q) fun o ho => (hfoP o.Q (hN0 o ho)).2.2.2⟩
  · intro hE
    have hne : (BAProv_startOuts p) ≠ [] := by
      intro h0
      have := BAEngine_partition_ne_nil (BAGraph.ofLGraph (fxyPowGraph p))
      rw [← hmapQ, h0] at this
      exact this rfl
    obtain ⟨o, ho⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨o', ho'⟩ := List.exists_mem_of_ne_nil _ (hfoP o.Q (hN0 o ho)).2.2.1
    rcases List.mem_append.1 ho' with ho' | ho'
    · have : o.comp o' ∈ (BAProv_startOuts p).flatMap fun o => (foP o.Q).map o.comp := List.mem_flatMap.2 ⟨o, ho, List.mem_map_of_mem ho'⟩
      rw [List.append_eq_nil_iff.1 hE |>.1] at this
      simp at this
    · have : o.comp o' ∈ (BAProv_startOuts p).flatMap fun o => (feP o.Q).map o.comp := List.mem_flatMap.2 ⟨o, ho, List.mem_map_of_mem ho'⟩
      rw [List.append_eq_nil_iff.1 hE |>.2] at this
      simp at this
  · intro o2 ho2
    simp only [List.mem_append, List.mem_flatMap, List.mem_map] at ho2
    have key : ∀ (o : BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))) (o' : BAProvOut o.Q), o ∈ BAProv_startOuts p →
        o'.ExtOK ∧ o'.Molecular → (o.comp o').ExtOK ∧ BACoverBy (P := (o.comp o').Q) fun k : Fin p => (o.comp o').π (Sum.inr (localReg_fxyBeta k)) :=
      fun o o' ho h => ⟨BAProvOut.ExtOK.comp (BAProv_startOuts_good p o ho).1 h.1,
        BACoverBy.comp (BAProv_startOuts_good p o ho).2.2 h.2⟩
    rcases ho2 with ⟨o, ho, o', ho', rfl⟩ | ⟨o, ho, o', ho', rfl⟩
    · exact key o o' ho ((hfoP o.Q (hN0 o ho)).1 o' (List.mem_append_left _ ho'))
    · exact key o o' ho ((hfoP o.Q (hN0 o ho)).1 o' (List.mem_append_right _ ho'))
  · intro o2 ho2
    obtain ⟨P0, hP0, hreach, -⟩ := hconcl.2.2.1 o2.Q (by rw [← List.map_append]; exact List.mem_map_of_mem ho2)
    have h := ba_nWS_ge hreach
    rw [baStart_nWS p P0 hP0] at h
    exact h

/-- **the BA `lem:localregular` with provenance** (target 8 (a); twin of `lw_localregularXP`, `LWProv:1680`) -/
def BAEngineProv : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph p)))),
    (∀ o ∈ outs ++ errs, o.ExtOK ∧ BACoverBy (P := o.Q) fun k : Fin p => o.π (Sum.inr (localReg_fxyBeta k))) ∧
    BALocRegConcl p c K0 d D (outs.map (·.Q)) (errs.map (·.Q)) ∧
    (∀ o ∈ outs ++ errs, p ≤ o.Q.g.waved.countP (fun e => !e.col)) ∧
    BAWExp d (baPG (BAGraph.ofLGraph (fxyPowGraph p))) (outs ++ errs)

theorem ba_localregularXP : BAEngineProv := by
  intro p c hc K0 d D
  obtain ⟨outs, errs, -, h⟩ := ba_localregularXP_ne p c hc K0 d D
  exact ⟨outs, errs, h⟩

/-- the conclusion of `ba_localregularX` without the binder (target 8 (b); the content of the pin `T2472_LocRegXClosed`) -/
def BAProv_LocRegXClosed : Prop :=
  ∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)

/-- **target 8 (b)** (`lwEngineProv_imp_localregularX`, `LWProv:177`): forgetting the provenance -/
theorem baEngineProv_imp_localregularX (h : BAEngineProv) : BAProv_LocRegXClosed := by
  intro p c hc K0 d D
  obtain ⟨outs, errs, -, hC, hW, -⟩ := h p c hc K0 d D
  refine ⟨outs.map (·.Q), errs.map (·.Q), hC, fun Q hQ => ?_⟩
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (by simpa [List.map_append] using hQ : Q ∈ (outs ++ errs).map (·.Q))
  exact hW o ho

end Engine

/-! ## 8. Compiled instances (`d = 3`, `L = 4`, `W = 2`, the flow point `(g0P, EP, t0P, m0P)`: `BASelf` and `0 < t₀ < 1` are `flowP_data`; labels `ℓ0`) -/

section Inst

open RBM.BA.CouplingWindowInst BASimInst BALvl1AInst BASymm1Inst BAVocabInst

/-- **target 8** at `p = 2`, `c = 1/4`, `K0 = 2`, `d = 3`, `D = 10`: the only hypothesis `0 < c` is discharged; the lists are non-empty (a start term of the 16 has at least one output), every output is `ExtOK` and
covered, `BALocRegConcl` holds, at least `p = 2` black waved edges, and the weighted expansion -/
example := ba_localregularXP_ne 2 (1 / 4) (by norm_num) 2 3 10

/-- **target 8 (b)** at the same data: the conclusion without provenance, and its lists are those of the engine -/
example := baEngineProv_imp_localregularX ba_localregularXP 2 (1 / 4) (by norm_num) 2 3 10

/-- the pinned text of `T2472_LocRegXClosed` (copied by script from `docs/tickets/checks/T2472-check.lean`) is proved by `baEngineProv_imp_localregularX` -/
example : (∀ (p : ℕ) (c : ℝ), 0 < c → ∀ (K0 d : ℕ) (D : ℝ), ∃ outs errs : List (BAPGraph (Fin 2)),
    BALocRegConcl p c K0 d D outs errs ∧ ∀ Q ∈ outs ++ errs, p ≤ Q.g.waved.countP (fun e => !e.col)) := baEngineProv_imp_localregularX ba_localregularXP

/-- **target 3 / target 8: `BAWExp.prod` at the engine's expansion** (not a leaf): at the flow point, `p = 2`, the weights `w_k(x) = 1` at `x = ℓ0 0` and `1/2` elsewhere (`BAProv_w`), the non-empty list of the
engine -/
example : ∃ outs : List (BAProvOut (baPG (BAGraph.ofLGraph (fxyPowGraph 2)))), outs ≠ [] ∧
    ∫ ω, (baPG (BAGraph.ofLGraph (fxyPowGraph 2))).valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => ∏ k : Fin 2, BAProv_w k (ℓ (Sum.inr (localReg_fxyBeta k)))) ℓ0 ∂(PF 3 4 2 0) =
      (outs.map fun o => ∫ ω, o.Q.valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => ∏ k : Fin 2, BAProv_w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓ0 ∂(PF 3 4 2 0)).sum := by
  obtain ⟨outs, errs, hne, -, -, -, hW⟩ := ba_localregularXP_ne 2 (1 / 4) (by norm_num) 2 3 10
  exact ⟨outs ++ errs, hne, BAWExp.prod hW (by norm_num) flowP_data.2.2 flowP_data.1.le flowP_data.2.1 BAProv_w ℓ0⟩

/-- **target 4/8, the start outputs at `p = 2`**: the 16 terms of the partition with their maps `vmap`, `ExtOK`, `Molecular` and covered; and the weighted partition at the flow point (`BAProv_start_W`, the weight `Π_k w_k`) -/
example : (BAProv_startOuts 2).length = 16 ∧ (∀ o ∈ BAProv_startOuts 2, o.ExtOK ∧ o.Molecular ∧
    BACoverBy (P := o.Q) fun k : Fin 2 => o.π (Sum.inr (localReg_fxyBeta k))) :=
  ⟨by decide +kernel, BAProv_startOuts_good 2⟩

example : ∫ ω, (baPG (BAGraph.ofLGraph (fxyPowGraph 2))).valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => ∏ k : Fin 2, BAProv_w k (ℓ (Sum.inr (localReg_fxyBeta k)))) ℓ0 ∂(PF 3 4 2 0) =
      ((BAProv_startOuts 2).map fun o => ∫ ω, o.Q.valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => ∏ k : Fin 2, BAProv_w k (ℓ (o.π (Sum.inr (localReg_fxyBeta k))))) ℓ0 ∂(PF 3 4 2 0)).sum :=
  BAWExp.prod (BAProv_start_W 3 _) (by norm_num) flowP_data.2.2 flowP_data.1.le flowP_data.2.1 BAProv_w ℓ0

/-- **target 5 (b), target 4: the five frame kinds with the weighted expansion** at the merged data of R1 (`BASimInst`): `gg` at `P_A` (31 outputs), `within` at `P_B`, `ggSplit` at `P_C`, `edge` at `P_E`,
`weight` at the first start term -- positions with `ExtOK`, `Molecular` and `BAWExp`, for all the outputs of the step (the output lists are non-empty) -/
example : BAProvPosW 3 (baPG baPA) ggF ∧ ggF.length = 31 := ⟨BAProv_frameStep_posW 3 _ (by decide) hFA, by decide +kernel⟩

example : BAProvPosW 3 (baPG baPB) ((baPG baPB).withinOuts pB) ∧ 0 < ((baPG baPB).withinOuts pB).length :=
  ⟨BAProv_frameStep_posW 3 _ (by decide) hFB, by decide +kernel⟩

example : BAProvPosW 3 (baPG baPC) ((baPG baPC).splitOuts pC qC 0) ∧ 0 < ((baPG baPC).splitOuts pC qC 0).length :=
  ⟨BAProv_frameStep_posW 3 _ (by decide) hFC, by decide +kernel⟩

example : BAProvPosW 3 (baPG baPE) ((baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE)) ∧ 0 < ((baPG baPE).outsOf (BAGraph.lanlwTerms baPE pE)).length :=
  ⟨BAProv_frameStep_posW 3 _ (by decide) hFE, by decide +kernel⟩

example : BAProvPosW 3 (baPG BAProv_baPW2) ((baPG BAProv_baPW2).outsOf (BAProv_baPW2.lw2 BAProv_pW2) ++ (baPG BAProv_baPW2).outsOf (BAProv_baPW2.lw4 BAProv_pW2)) ∧
    0 < ((baPG BAProv_baPW2).outsOf (BAProv_baPW2.lw2 BAProv_pW2)).length :=
  ⟨BAProv_frameStep_posW 3 _ (by decide +kernel) (BAFrameStep.weight (baPG BAProv_baPW2) BAProv_pW2 (List.mem_cons_self ..) (by decide +kernel)),
    by decide +kernel⟩

/-- **target 6** at `BALvl1AInst.locStepB` (the twist of `P_B`; `normalB`): the positions of the outputs, a non-empty list, and the weighted expansion evaluated at the flow point with a non-constant
weight (`1` where the first external vertex carries the label `ℓ0 0`, `1/2` elsewhere) -/
example : ∃ ps : List (BAProvOut ((baPG baPB).twist true true)), ps ≠ [] ∧ (∀ o ∈ ps, o.ExtOK ∧ o.Molecular) ∧
    ∫ ω, ((baPG baPB).twist true true).valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => if ℓ (Sum.inl (0 : Fin 2)) = ℓ0 0 then 1 else 1 / 2) ℓ0 ∂(PF 3 4 2 0) =
      (ps.map fun o => ∫ ω, o.Q.valW (BAlwData 3 4 2 g0P EP t0P m0P ω)
        (fun ℓ => if ℓ (o.π (Sum.inl (0 : Fin 2))) = ℓ0 0 then 1 else 1 / 2) ℓ0 ∂(PF 3 4 2 0)).sum := by
  obtain ⟨ps, hps, hok, hW⟩ := baProv_stepPos 3 _ _ locStepB normalB
  refine ⟨ps, ?_, hok, hW 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ ℓ0⟩
  rintro rfl
  have := congrArg List.length hps
  simp only [List.map_nil, List.length_nil, List.length_map] at this
  have h0 : 0 < ((baPG baPB).withinOuts pB).length := by decide +kernel
  omega

/-- **target 7** at the normal graph `baGGLhs` (one internal vertex with two solid edges of one colour), the cutoff `K = 10`: lists with maps, non-empty, `ExtOK`, `Molecular`, the conclusion of
`BAlvl1Lemma` for their graphs and the weighted expansion -/
example := BAProv_exists_ne 3 10 (baPG baGGLhs) (by decide)

example := baProv_exists 3 3 ((baPG baPB).twist true true) normalB

/-- a non-constant weight: `1` where the vertex `v` carries the label `ℓ0 0`, `1/2` elsewhere -/
def BAProv_wt {V : Type} (v : V) : (V → Idx 3 4 2) → ℝ := fun ℓ => if ℓ v = ℓ0 0 then 1 else 1 / 2

/-- **target 5 (b), the weighted identity of each step kind and of the twist**, applied directly at the merged data of R1 (`BASimInst`, `BALvl1AInst`) and the flow point, the weight `BAProv_wt`
(hypotheses on the selected edges discharged by `decide` / `rfl`): `weight` at the loop of the first start term, `gg` at `(P_A, p_A, q_A)`, `edge` at `(P_E, p_E)`, `within` at `P_B`, `ggSplit` at
`P_C` with `j = 0` -/
example := BAProv_lw_W (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 BAProv_baPW2 BAProv_pW2
  (List.mem_cons_self ..) (by decide +kernel) (by decide +kernel) (by decide +kernel) (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

example := BAProv_gg_W (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 baPA pA qA (List.mem_cons_self ..)
  (List.mem_cons_self ..) (by decide) (by decide) (by decide) (by decide) (by decide) (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

example := BAProv_lanlw_W (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 baPE pE
  (List.mem_cons_of_mem _ (List.mem_map.2 ⟨_, List.mem_cons_self .., rfl⟩)) (by decide) (by decide) (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

example := BAProv_macroA_W (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 baPB pB (List.mem_cons_self ..) rfl rfl
  (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

example := BAProv_macroB_W (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 baPC pC qC (List.mem_cons_self ..) 0 rfl
  ⟨rfl, rfl, rfl, rfl⟩ (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

/-- the weighted twist (`c = t = true`) at `P_B` and the twist of the leaf expansion -/
example := BAProv_twist_EW (L := 4) (W := 2) g0P EP t0P m0P (baPG baPB) true true (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0

example : BAWExp 3 ((baPG baPB).twist true true) ([(⟨baPG baPB, id⟩ : BAProvOut (baPG baPB))].map (BAProvOut.twist true true)) :=
  BAWExp.twist true true (BAWExp.refl 3 (baPG baPB))

/-- **target 7** at `baGGLhs` and `K = 10`, the weighted expansion evaluated at the flow point with the weight `BAProv_wt`, the lists non-empty -/
example : ∃ oP eP : List (BAProvOut (baPG baGGLhs)), oP ++ eP ≠ [] ∧
    ∫ ω, (baPG baGGLhs).valW (BAlwData 3 4 2 g0P EP t0P m0P ω) (BAProv_wt (Sum.inl (0 : Fin 2))) ℓ0 ∂(PF 3 4 2 0) =
      ((oP ++ eP).map fun o => ∫ ω, o.Q.valW (BAlwData 3 4 2 g0P EP t0P m0P ω) (fun ℓ => BAProv_wt (Sum.inl (0 : Fin 2)) (ℓ ∘ o.π)) ℓ0 ∂(PF 3 4 2 0)).sum := by
  obtain ⟨oP, eP, -, -, hne, hW⟩ := BAProv_exists_ne 3 10 (baPG baGGLhs) (by decide)
  exact ⟨oP, eP, hne, hW 4 2 (by norm_num) g0P EP t0P m0P flowP_data.2.2 flowP_data.1.le flowP_data.2.1 _ ℓ0⟩

end Inst

end RBM.Graph
end
