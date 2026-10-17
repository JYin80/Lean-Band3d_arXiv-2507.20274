/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14c

/-!
# BA-L L4c1 (T2464), part B: the `x ~ y` support, the averaged leaf bound, the assembly of S3

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-121`; supervisor
`2026-10-12-0851.md` Q3 (the disjunction), design `docs/reports/T2398-design.md` §5, §7.
Twin of `Graph/LWExpTerm3.lean` `:1749-1858` (§4 count), `:1859-1955`, `:2029-2174` (assembly).
Part A is `Graph/BAExp14c.lean`.

## Contents (namespace `RBM.BA`; private prefix `BAExp14c_`)

5. The `x ~ y` support `BAExp14c_xy_support`; integrals over the carrier law; the average of the
   expectations; `baS3LeafAvg_holds` (the disjunction of 0851 Q3).
6. The conditional assembly `baExp14bS3_of_leaf : BAG5LeafPrec d → BAExp14bS3 d`.
7. The compiled nonempty instances (namespace `BAExp14cInst`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false

open private BAS3Close_pk BAS3Close_LeafC BAS3Close_CtxExD BAS3Close_Iso BAS3Close_iso_symm
  BAS3Close_iso_trans BAS3Close_iso_val BAS3Close_iso_leaf BAS3Close_leaf_pk BAS3Close_ctxEx_pk BAS3Close_iso_cand BAS3Close_iso_root
  BAS3Close_out_stuck from RBM3D.Graph.BAS3Close
open private BAS3Close_RootFacts BAS3Close_tests_M BAS3Close_MCM BAS3Close_vs1 BAS3Close_vs1_mem BAS3Close_vs1_len BAS3Close_invC_of_facts
  BAS3Close_CatR0 BAS3Close_eI0_0 BAS3Close_iso_pk_perm BAS3Close_keys_eq BAS3Close_cf0_0 from RBM3D.Graph.BAS3CloseB
open private BAS3Close_D BAS3Close_data BAS3Close_hG BAS3Close_rho BAS3Close_kD from RBM3D.Graph.BAS3CloseC
open private BAVocab_val_of_factor BAVocab_val_of_not BAVocab_self_mem_atom from RBM3D.Graph.BAVocab
open private BAExpandId_integrable_pval BAExpandId_integrable_val from RBM3D.Graph.BAExpandId

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 5. The `x ~ y` support (target 5) -/

/-- **The `x ~ y` support** (`T2464_xy_support`; the BA form of the `x = y` case of `lwExpTerm3_val_ext_ne`, `LWExpTerm3:1797`): if the external
vertices lie in one atom, the value at `BAlwData` vanishes at labels of different offsets (`baAtom_offset`, `BAAtom_offdiag_E`), so only `W^d` of the
`W^{2d}` pairs of `[a]×[b]` contribute. -/
theorem BAExp14c_xy_support : ∀ (d : ℕ) (κ ε 𝔠 𝔡 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ BAflowT0 sz z n → ∀ (ω : sz.SeqΩ) (P : BAPGraph (Fin 2)),
      P.g.atom (Sum.inl (P.ext 0)) = P.g.atom (Sum.inl (P.ext 1)) →
      ∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
        P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y] = 0 := by
  intro d κ ε 𝔠 𝔡 sz z hf n t ht0 ht ω P hatom x y hxy
  classical
  by_cases hex : ∃ ℓ' : P.E' → Idx d (sz.L n) (sz.W n), ![x, y] = ℓ' ∘ P.ext
  swap
  · exact BAVocab_val_of_not P _ hex
  obtain ⟨ℓ', hℓ'⟩ := hex
  rw [BAVocab_val_of_factor P _ hℓ']
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have hw : (((BAflowEs sz z n : ℝ) : ℂ) + (baFMz sz z).m n).im ≠ 0 := by simpa using hr.1.1.ne'
  have hoff : ∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
      (BAS3Close_D sz z n t ω).M x y = 0 ∧ (BAS3Close_D sz z n t ω).gPsi x y = 0 := fun x y ho =>
    BAAtom_offdiag_E (BAflowLam0 sz z n) (BAflowEs sz z n) ((baFMz sz z).m n) hw x y ho
  unfold BAGraph.val
  refine Finset.sum_eq_zero fun ℓi _ => ?_
  by_contra hne
  have h0 := congrFun hℓ' 0
  have h1 := congrFun hℓ' 1
  simp only [Function.comp, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hv : (Sum.inl (P.ext 1) : P.E' ⊕ P.I') ∈ P.g.atom (Sum.inl (P.ext 0)) := by
    rw [hatom]; exact BAVocab_self_mem_atom P.g _
  have := baAtom_offset P.g (BAS3Close_D sz z n t ω) hoff (Sum.elim ℓ' ℓi) hne (Sum.inl (P.ext 0)) (Sum.inl (P.ext 1)) hv
  simp only [Sum.elim_inl] at this
  rw [← h0, ← h1] at this
  exact hxy this

/-! ### Integrals over the carrier law: transport from `PF`, integrability of graph values, averages -/

section Integrals

/-- `∫ Φ ∘ slice ∂seqP(sz.withLam 0) = ∫ Φ ∂PF d L W 0` for `Φ` a.e. strongly measurable (`BAExp14a_int_slice` without continuity). -/
theorem BAExp14c_int_slice {d : ℕ} {sz : Sizes d} (n : ℕ) (Φ : Ω d (sz.L n) (sz.W n) → ℂ)
    (hΦ : AEStronglyMeasurable Φ (PF d (sz.L n) (sz.W n) 0)) :
    ∫ ω, Φ (BAExp14a_slc sz n ω) ∂(BAExp14a_μ sz) = ∫ ω', Φ ω' ∂(PF d (sz.L n) (sz.W n) 0) := by
  have hmap := Sizes.seqP_map_slice (sz.withLam 0) n
  have hΦ' : AEStronglyMeasurable Φ (Measure.map (Sizes.slice (sz.withLam 0) n) (Sizes.seqP (sz.withLam 0))) := by
    convert hΦ using 1
    exact hmap
  change ∫ ω, Φ (Sizes.slice (sz.withLam 0) n ω) ∂(Sizes.seqP (sz.withLam 0)) = _
  rw [← integral_map (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable hΦ']
  congr 1

/-- Every packed graph value is integrable over the carrier law (`BAExpandId_integrable_pval` over `PF`, transported along the slice). -/
theorem BAExp14c_integrable_val {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hf : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {E0 : Type} (P : BAPGraph E0) (ℓ : E0 → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω : sz.SeqΩ => P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ℓ) (BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hI := BAExpandId_integrable_pval (d := d) (L := sz.L n) (W := sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n)
    (BAflowEs sz z n) t ((baFMz sz z).m n) hr.1 ht0 ht1 P ℓ
  have hmap := Sizes.seqP_map_slice (sz.withLam 0) n
  have hmeas : AEMeasurable (Sizes.slice (sz.withLam 0) n) (Sizes.seqP (sz.withLam 0)) :=
    (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable
  have hI' : Integrable (fun ω' : Ω d (sz.L n) (sz.W n) => P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n)
      (BAflowEs sz z n) t ((baFMz sz z).m n) ω') ℓ) (Measure.map (Sizes.slice (sz.withLam 0) n) (Sizes.seqP (sz.withLam 0))) := by
    convert hI using 1
    exact hmap
  exact (integrable_map_measure hI'.aestronglyMeasurable hmeas).1 hI'

/-- The expectation of a block average is the block average of the expectations (each entry integrable). -/
theorem BAExp14c_int_avg {d : ℕ} {sz : Sizes d} {n : ℕ} (A B' : Finset (Idx d (sz.L n) (sz.W n)))
    (V : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → sz.SeqΩ → ℂ)
    (hV : ∀ x y, Integrable (V x y) (BAExp14a_μ sz)) :
    ∫ ω, ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ A, ∑ y ∈ B', V x y ω ∂(BAExp14a_μ sz) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ A, ∑ y ∈ B', ∫ ω, V x y ω ∂(BAExp14a_μ sz) := by
  rw [integral_const_mul, integral_finsetSum _ (fun x _ => integrable_finsetSum _ fun y _ => hV x y)]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ (fun y _ => hV x y)]

/-- The block average of entries bounded by `F` is bounded by `F`; if the entries vanish at different offsets, by `W^{-d} F`
(`BAExp14a_pair_count`: `W^d` of the `W^{2d}` pairs have equal offsets). -/
theorem BAExp14c_avg_le {d : ℕ} {sz : Sizes d} {n : ℕ} (a b : Zd d (sz.L n)) (f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    {F : ℝ} (hF : ∀ x y, ‖f x y‖ ≤ F) :
    ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, f x y‖ ≤ F := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0 0)
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * ‖∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, f x y‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * F)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans ?_
        calc ∑ x ∈ twBlk n a, ‖∑ y ∈ twBlk n b, f x y‖ ≤ ∑ x ∈ twBlk n a, (((sz.W n : ℕ) : ℝ) ^ d * F) := by
              refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
              calc ∑ y ∈ twBlk n b, ‖f x y‖ ≤ ∑ y ∈ twBlk n b, F := Finset.sum_le_sum fun y _ => hF x y
                _ = ((sz.W n : ℕ) : ℝ) ^ d * F := by
                    rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
          _ = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * F) := by
              rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
    _ = F := by field_simp

theorem BAExp14c_avg_le_tied {d : ℕ} {sz : Sizes d} {n : ℕ} (a b : Zd d (sz.L n))
    (f : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ) {F : ℝ} (hF : ∀ x y, ‖f x y‖ ≤ F)
    (h0 : ∀ x y, (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 → f x y = 0) :
    ‖((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, f x y‖ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * F := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hF0 : 0 ≤ F := (norm_nonneg _).trans (hF 0 0)
  rw [norm_mul, norm_pow, norm_inv, norm_pow, Complex.norm_natCast]
  have hcount : ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
      (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℝ) else 0) = ((sz.W n : ℕ) : ℝ) ^ d :=
    BAExp14a_pair_count (W := sz.W n) a b
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * ‖∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, f x y‖
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 2 * (((sz.W n : ℕ) : ℝ) ^ d * F) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (norm_sum_le _ _).trans ?_
        calc ∑ x ∈ twBlk n a, ‖∑ y ∈ twBlk n b, f x y‖ ≤ ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
              (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then F else 0) := by
              refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => ?_)
              by_cases h : (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2
              · simp only [h, ↓reduceIte]; exact hF x y
              · simp only [h, ↓reduceIte]; rw [h0 x y h, norm_zero]
          _ = ((sz.W n : ℕ) : ℝ) ^ d * F := by
              have : ∀ x y : Idx d (sz.L n) (sz.W n),
                  (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then F else 0) =
                  F * (if (split d (sz.L n) (sz.W n) x).2 = (split d (sz.L n) (sz.W n) y).2 then (1 : ℝ) else 0) := by
                intro x y; split_ifs <;> simp
              simp only [this, ← Finset.mul_sum]
              rw [hcount]; ring
    _ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * F := by field_simp

end Integrals

/-! ### The `BAG5LeafProps` branch of `BAS3LeafAvg`: the pin per pair, then the average

`t^{n_W} ≤ t` (`n_W ≥ 2`), `η⁻¹ ≤ κ⁻¹ (1 - t)⁻¹` (`twEta_ge_holds`); apart atoms (`ord ≥ 5`): `B^{ord/2} ≤ 2^{(ord-5)/2} B^{5/2}`; tied atoms
(`ord ≥ 3`): the entries vanish at different offsets (`BAExp14c_xy_support`), so `W^{-d}` of the average survives, `W^{-d} ≤ (𝔡⁻² + 1) B`
(`twB0_ge_holds`) and `B^{ord/2} ≤ 2^{(ord-3)/2} B^{3/2}`. -/

section G5Branch

private theorem BAExp14c_Bpow {B o c : ℝ} (hB0 : 0 < B) (hB2 : B ≤ 2) (ho : c ≤ o) (hc : 0 ≤ c) :
    B ^ (o / 2) ≤ 2 ^ ((o - c) / 2) * B ^ (c / 2) := by
  have h1 : B ^ (o / 2) = B ^ ((o - c) / 2) * B ^ (c / 2) := by
    rw [← Real.rpow_add hB0]; congr 1; ring
  rw [h1]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hB0.le _)
  exact Real.rpow_le_rpow hB0.le hB2 (by linarith)

private theorem BAExp14c_leafAvg_G5 {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {sz : Sizes d} {z : ℕ → ℂ} (hf : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n) (q : BAPGraph (Fin 2)) (hq : BAG5LeafProps (fun _ _ => [q]))
    (hpin : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p _ => ‖∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂(Sizes.seqP (sz.withLam 0))‖)
      (fun n _ _ => (t n) ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((q.scalingOrder : ℝ) / 2))) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p _ => ‖∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n p.1, ∑ y ∈ twBlk n p.2,
          q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![x, y]) ∂(Sizes.seqP (sz.withLam 0))‖)
      (fun n _ _ => t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) := by
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hf.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (BAS3Close_data sz hf n (ht0 n) (htT n)).1
  have hηinv : ∀ n, ((baFMz sz z).eta n (t n))⁻¹ ≤ κ⁻¹ * (1 - t n)⁻¹ := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    exact fun n => BAExp14a_eta_inv_le hκ hf n (ht1 n)
  obtain ⟨-, -, hnW, -, htgt⟩ := hq false false q (List.mem_singleton_self q)
  refine (BAExp14a_det_iff hsz _ _).2 ?_
  intro τ hτ
  have hpin' := (BAExp14a_det_iff hsz _ _).1 hpin (τ / 2) (half_pos hτ)
  have hev := BAExp14a_eventual_scalars hκ hε h𝔡 hf ht0 htT
  have h6a := twB0_ge_holds sz 𝔡 hf.1.2.2.2.2 t ht0 (fun n => (ht1 n).le)
  set o : ℝ := (q.scalingOrder : ℝ) with ho
  set C : ℝ := max (κ⁻¹ * 2 ^ ((o - 5) / 2)) (κ⁻¹ * 2 ^ ((o - 3) / 2) * (𝔡⁻¹ ^ 2 + 1)) with hCdef
  have hC : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp (tendsto_natCast_atTop_iff.2 hsz)).eventually (eventually_ge_atTop C)
  filter_upwards [hpin', hev, h6a, hC] with n hp hs hw hCn
  obtain ⟨-, -, -, hBle, -⟩ := hs
  intro v
  obtain ⟨a, b⟩ := v
  set Nn : ℝ := ((sz.size n : ℕ) : ℝ) with hNn
  set Bc : ℝ := sz.Bctl n (t n) with hBc
  have hB0 : 0 < Bc := STBctl_pos sz n (ht1 n)
  have hN0 : 0 ≤ Nn ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hR0 : 0 ≤ t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ)) :=
    mul_nonneg (ht0 n) (mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg hB0.le _))
  have hint : ∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
      q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![x, y]) ∂(Sizes.seqP (sz.withLam 0)) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
        ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y] ∂(Sizes.seqP (sz.withLam 0)) :=
    BAExp14c_int_avg (twBlk n a) (twBlk n b) (fun x y ω => q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n)
      (BAflowEs sz z n) (t n) ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y])
      (fun x y => BAExp14c_integrable_val hf (ht0 n) (htT n) q ![x, y])
  rw [hint]
  have hη := hηinv n
  have hη0 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := by
    have := BAExp14a_eta_pos hκ hf n (ht0 n) (htT n)
    exact inv_nonneg.2 this.le
  have htpow : t n ^ q.g.nW ≤ t n := pow_le_of_le_one (ht0 n) (ht1 n).le (by omega)
  have htp0 : 0 ≤ t n ^ q.g.nW := pow_nonneg (ht0 n) _
  have hNpos : 0 < Nn := by
    have : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    change 0 < ((sz.size n : ℕ) : ℝ)
    linarith
  have hpp : Nn ^ τ = Nn ^ (τ / 2) * Nn ^ (τ / 2) := by
    rw [← Real.rpow_add hNpos]
    congr 1; ring
  by_cases hatom : q.g.atom (Sum.inl (q.ext 0)) = q.g.atom (Sum.inl (q.ext 1))
  · -- tied atoms: `ord ≥ 3`, the entries vanish at different offsets
    have h3 : (3 : ℝ) ≤ o := by
      have : (3 : ℤ) ≤ q.scalingOrder := by
        have := htgt; unfold BAG5Tgt at this; simp only [hatom, ↓reduceIte] at this; omega
      rw [ho]; exact_mod_cast this
    have hzero : ∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
        ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y] ∂(Sizes.seqP (sz.withLam 0)) = 0 := by
      intro x y hxy
      calc _ = ∫ _ω, (0 : ℂ) ∂(Sizes.seqP (sz.withLam 0)) :=
            integral_congr_ae (Eventually.of_forall fun ω =>
              BAExp14c_xy_support d κ ε 𝔠 𝔡 sz z hf n (t n) (ht0 n) (htT n) ω q hatom x y hxy)
        _ = 0 := by simp
    have h1 := BAExp14c_avg_le_tied (sz := sz) a b (fun x y => ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n)
      (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y] ∂(Sizes.seqP (sz.withLam 0)))
      (F := Nn ^ (τ / 2) * (t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * Bc ^ (o / 2))) (fun x y => hp (x, y)) hzero
    refine h1.trans ?_
    have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      positivity
    have hdd : (0 : ℝ) ≤ 𝔡⁻¹ ^ 2 + 1 := by positivity
    have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (𝔡⁻¹ ^ 2 + 1) * Bc := by
      have h1' : 1 ≤ (𝔡⁻¹ ^ 2 + 1) * (((sz.W n : ℕ) : ℝ) ^ d * Bc) := by
        have := mul_le_mul_of_nonneg_left hw hdd
        rwa [mul_inv_cancel₀ (by positivity)] at this
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((𝔡⁻¹ ^ 2 + 1) * (((sz.W n : ℕ) : ℝ) ^ d * Bc)) :=
            mul_le_mul_of_nonneg_left h1' (inv_nonneg.2 hWpos.le)
        _ = (𝔡⁻¹ ^ 2 + 1) * Bc := by field_simp
    have hBo := BAExp14c_Bpow hB0 hBle h3 (by norm_num : (0 : ℝ) ≤ 3)
    have hB52 : Bc * Bc ^ ((3 : ℝ) / 2) = Bc ^ ((5 : ℝ) / 2) := by
      rw [← Real.rpow_one_add' hB0.le (by norm_num)]; norm_num
    have h2o : (0 : ℝ) ≤ 2 ^ ((o - 3) / 2) := Real.rpow_nonneg (by norm_num) _
    have hB32 : 0 ≤ Bc ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hB0.le _
    have hW3 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (o / 2) ≤ (𝔡⁻¹ ^ 2 + 1) * 2 ^ ((o - 3) / 2) * Bc ^ ((5 : ℝ) / 2) := by
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (o / 2)
          ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (2 ^ ((o - 3) / 2) * Bc ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hBo (inv_nonneg.2 hWpos.le)
        _ ≤ ((𝔡⁻¹ ^ 2 + 1) * Bc) * (2 ^ ((o - 3) / 2) * Bc ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_right hWd (mul_nonneg h2o hB32)
        _ = (𝔡⁻¹ ^ 2 + 1) * 2 ^ ((o - 3) / 2) * (Bc * Bc ^ ((3 : ℝ) / 2)) := by ring
        _ = _ := by rw [hB52]
    have htη : t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ ≤ t n * (κ⁻¹ * (1 - t n)⁻¹) :=
      mul_le_mul htpow hη hη0 (ht0 n)
    have htη0 : 0 ≤ t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ := mul_nonneg htp0 hη0
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (Nn ^ (τ / 2) * (t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * Bc ^ (o / 2)))
        = Nn ^ (τ / 2) * (t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹) * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bc ^ (o / 2)) := by ring
      _ ≤ Nn ^ (τ / 2) * (t n * (κ⁻¹ * (1 - t n)⁻¹)) * ((𝔡⁻¹ ^ 2 + 1) * 2 ^ ((o - 3) / 2) * Bc ^ ((5 : ℝ) / 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left htη hN0) hW3 ?_ ?_
          · exact mul_nonneg (inv_nonneg.2 hWpos.le) (Real.rpow_nonneg hB0.le _)
          · exact mul_nonneg hN0 (mul_nonneg (ht0 n) (mul_nonneg (inv_nonneg.2 hκ.le) (inv_nonneg.2 (by linarith [ht1 n]))))
      _ = (κ⁻¹ * 2 ^ ((o - 3) / 2) * (𝔡⁻¹ ^ 2 + 1)) * (Nn ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ)))) := by ring
      _ ≤ Nn ^ (τ / 2) * (Nn ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hCn) (mul_nonneg hN0 hR0)
      _ = Nn ^ τ * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ))) := by rw [hpp]; ring
  · -- apart atoms: `ord ≥ 5`
    have h5 : (5 : ℝ) ≤ o := by
      have : (5 : ℤ) ≤ q.scalingOrder := by
        have := htgt; unfold BAG5Tgt at this; simp only [hatom, ↓reduceIte] at this; omega
      rw [ho]; exact_mod_cast this
    have h1 := BAExp14c_avg_le (sz := sz) a b (fun x y => ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n)
      (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y] ∂(Sizes.seqP (sz.withLam 0)))
      (F := Nn ^ (τ / 2) * (t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * Bc ^ (o / 2))) (fun x y => hp (x, y))
    refine h1.trans ?_
    have hBo := BAExp14c_Bpow hB0 hBle h5 (by norm_num : (0 : ℝ) ≤ 5)
    have h2o : (0 : ℝ) ≤ 2 ^ ((o - 5) / 2) := Real.rpow_nonneg (by norm_num) _
    have hB52 : 0 ≤ Bc ^ ((5 : ℝ) / 2) := Real.rpow_nonneg hB0.le _
    have htη : t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ ≤ t n * (κ⁻¹ * (1 - t n)⁻¹) :=
      mul_le_mul htpow hη hη0 (ht0 n)
    have htη0 : 0 ≤ t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ := mul_nonneg htp0 hη0
    calc Nn ^ (τ / 2) * (t n ^ q.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * Bc ^ (o / 2))
        ≤ Nn ^ (τ / 2) * (t n * (κ⁻¹ * (1 - t n)⁻¹) * (2 ^ ((o - 5) / 2) * Bc ^ ((5 : ℝ) / 2))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul htη hBo (Real.rpow_nonneg hB0.le _) ?_) hN0
          exact mul_nonneg (ht0 n) (mul_nonneg (inv_nonneg.2 hκ.le) (inv_nonneg.2 (by linarith [ht1 n])))
      _ = (κ⁻¹ * 2 ^ ((o - 5) / 2)) * (Nn ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ)))) := by ring
      _ ≤ Nn ^ (τ / 2) * (Nn ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ)))) :=
          mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hCn) (mul_nonneg hN0 hR0)
      _ = Nn ^ τ * (t n * ((1 - t n)⁻¹ * Bc ^ (5 / 2 : ℝ))) := by rw [hpp]; ring

end G5Branch

/-! ### The fold branch of `BAS3LeafAvg`: L4d2a directly, in averaged form

Clause (i) of `BAFoldLeafT` writes the average of `q` as `t · twLoop2X(Ǧ, Ǧ, ǦE_bǦ(σ), ρ X^e)`.  `twFold2PrecDet_holds` (`e = false`) or
`twFold2Prec_holds` with `baS3Xprec_holds` (`e = true`) bounds the `twLoop2X` pathwise by `(1 - t)⁻¹ B^{5/2}`; `BAExp14a_prec_integral` takes `𝔼`
(crude envelope of `twLoop2X`, floor `BAExp14a_floor`), and the factor `t` is restored deterministically. -/

section FoldBranch

/-- `twLoop2X` is linear in the weight. -/
private theorem BAExp14c_twLoop2X_smul {d : ℕ} {sz : Sizes d} (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (s : ℂ) (a : Zd d (sz.L n)) :
    twLoop2X n A X C (fun c₁ c₂ c₃ c₄ => s * ρ c₁ c₂ c₃ c₄) a = s * twLoop2X n A X C ρ a := by
  unfold twLoop2X
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₃ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₄ _ => ?_
  ring

/-- The crude bound of `twLoop2X`: entries `≤ Bd` give `‖twLoop2X‖ ≤ (Σ_c ‖ρ‖) Bd³` (`W^{-3d}` against three blocks of `W^d` points). -/
private theorem BAExp14c_twLoop2X_le {d : ℕ} {sz : Sizes d} (n : ℕ) (A X C : Idx d (sz.L n) (sz.W n) → Idx d (sz.L n) (sz.W n) → ℂ)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ) (a : Zd d (sz.L n)) {Bd : ℝ}
    (hA : ∀ u x, ‖A u x‖ ≤ Bd) (hX : ∀ u x, ‖X u x‖ ≤ Bd) (hC : ∀ u x, ‖C u x‖ ≤ Bd) :
    ‖twLoop2X n A X C ρ a‖ ≤ (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖) * Bd ^ 3 := by
  have hBd : 0 ≤ Bd := (norm_nonneg _).trans (hA 0 0)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hterm : ∀ c₁ c₂ c₃ c₄ : Zd d (sz.L n), ‖ρ c₁ c₂ c₃ c₄ * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 *
      ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x)‖ ≤
      ‖ρ c₁ c₂ c₃ c₄‖ * Bd ^ 3 := by
    intro c₁ c₂ c₃ c₄
    rw [norm_mul, norm_mul, norm_pow, TwistFold2_norm_inv_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h1 : ‖∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x‖ ≤
        ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3)) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ x ∈ twBlk n a, ‖∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x‖
          ≤ ∑ x ∈ twBlk n a, (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3)) := by
            refine Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans ?_
            calc ∑ w ∈ twBlk n c₁, ‖∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x‖
                ≤ ∑ w ∈ twBlk n c₁, (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3) := by
                  refine Finset.sum_le_sum fun w _ => (norm_sum_le _ _).trans ?_
                  calc ∑ w' ∈ twBlk n c₃, ‖A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x‖
                      ≤ ∑ w' ∈ twBlk n c₃, Bd ^ 3 := by
                        refine Finset.sum_le_sum fun w' _ => ?_
                        rw [norm_mul, norm_mul]
                        calc ‖A x w‖ * ‖X (twShift n c₂ w) w'‖ * ‖C (twShift n c₄ w') x‖ ≤ Bd * Bd * Bd :=
                              mul_le_mul (mul_le_mul (hA _ _) (hX _ _) (norm_nonneg _) hBd) (hC _ _) (norm_nonneg _)
                                (mul_nonneg hBd hBd)
                          _ = Bd ^ 3 := by ring
                    _ = ((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3 := by
                        rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
              _ = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3) := by
                  rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
        _ = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3)) := by
            rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 3 * ‖∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃,
          A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x‖
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ^ 3 * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * Bd ^ 3))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = Bd ^ 3 := by field_simp
  unfold twLoop2X
  refine (norm_sum_le _ _).trans ?_
  calc ∑ c₁, ‖∑ c₂, ∑ c₃, ∑ c₄, ρ c₁ c₂ c₃ c₄ * (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 3 *
        ∑ x ∈ twBlk n a, ∑ w ∈ twBlk n c₁, ∑ w' ∈ twBlk n c₃, A x w * X (twShift n c₂ w) w' * C (twShift n c₄ w') x)‖
      ≤ ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * Bd ^ 3 := by
        refine Finset.sum_le_sum fun c₁ _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₂ _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun c₃ _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun c₄ _ => hterm c₁ c₂ c₃ c₄)))
    _ = _ := by simp only [Finset.sum_mul]

/-- `‖Ǧ_{xy}‖ ≤ η⁻¹ + 1` pathwise (`|G| ≤ η⁻¹`, `|M| ≤ 1`). -/
private theorem BAExp14c_GM_le {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hf : BAFlow sz κ ε 𝔠 𝔡 z)
    {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFMz sz z).GM n t ω x y‖ ≤ ((baFMz sz z).eta n t)⁻¹ + 1 := by
  obtain ⟨-, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  unfold FlowFM.GM
  exact (norm_sub_le _ _).trans (add_le_add (BAExp14a_G_le hκ hf n ht0 ht ω x y) (BAExp14a_M_le_one hr.1 x y))

/-- The pathwise envelope of the fold average without its factor `t`: with all entries of `Ǧ` bounded by `g ≥ 1` and the `ℓ¹` row bound `Cρ`
of the weight, `‖twLoop2X(Ǧ, Ǧ, ǦE_bǦ(σ), ρ X^e)‖ ≤ L^d Cρ · (W^d g²) · (g²)³`. -/
private theorem BAExp14c_Y_le {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {n : ℕ} {t : ℝ} (ω : sz.SeqΩ) (σ : Bool) (a b : Zd d (sz.L n))
    {g Cρ : ℝ} (hg1 : 1 ≤ g) (hGM : ∀ u v, ‖(baFMz sz z).GM n t ω u v‖ ≤ g)
    (ρ : Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hρ : ∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ ≤ Cρ) (e : Bool) :
    ‖twLoop2X n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
      (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
      (fun c₁ c₂ c₃ c₄ => ρ c₁ c₂ c₃ c₄ *
        (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
          (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a‖ ≤
      ((Fintype.card (Zd d (sz.L n)) : ℝ) * Cρ) * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) * (g ^ 2) ^ 3 := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast sz.W_pos n)
  have hg0 : 0 ≤ g := by linarith
  have hg2 : g ≤ g ^ 2 := by nlinarith
  have htw : ∀ y x : Idx d (sz.L n) (sz.W n), ‖twChg ((baFMz sz z).GM n t ω) σ y x‖ ≤ g := by
    intro y x
    unfold twChg
    split_ifs
    · exact hGM _ _
    · rw [RCLike.norm_conj]; exact hGM _ _
  have hA : ∀ u x : Idx d (sz.L n) (sz.W n), ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x‖ ≤ g ^ 2 := by
    intro u x
    rw [norm_mul, TwistFold2_norm_inv_pow]
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x‖
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hW.le)
          refine (norm_sum_le _ _).trans ?_
          calc ∑ y ∈ twBlk n b, ‖(baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x‖
              ≤ ∑ y ∈ twBlk n b, g ^ 2 := by
                refine Finset.sum_le_sum fun y _ => ?_
                rw [norm_mul, sq]
                exact mul_le_mul (hGM _ _) (htw _ _) (norm_nonneg _) hg0
            _ = ((sz.W n : ℕ) : ℝ) ^ d * g ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
      _ = g ^ 2 := by field_simp
  have hXb : ∀ c₂ c₄ : Zd d (sz.L n), ‖(if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
      (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * g ^ 2 := by
    intro c₂ c₄
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte, norm_one]
      nlinarith
    · simp only [↓reduceIte]
      rw [norm_mul, TwistFold2_norm_inv_pow]
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄, (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖
          ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2)) := by
            refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hW.le)
            refine (norm_sum_le _ _).trans ?_
            calc ∑ u ∈ twBlk n c₂, ‖∑ v ∈ twBlk n c₄, (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖
                ≤ ∑ u ∈ twBlk n c₂, (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
                  refine Finset.sum_le_sum fun u _ => (norm_sum_le _ _).trans ?_
                  calc ∑ v ∈ twBlk n c₄, ‖(baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u‖
                      ≤ ∑ v ∈ twBlk n c₄, g ^ 2 := by
                        refine Finset.sum_le_sum fun v _ => ?_
                        rw [norm_mul, sq]
                        exact mul_le_mul (hGM _ _) (hGM _ _) (norm_nonneg _) hg0
                    _ = ((sz.W n : ℕ) : ℝ) ^ d * g ^ 2 := by
                        rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
              _ = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
                  rw [Finset.sum_const, nsmul_eq_mul, TwistFold2_card_blk]
        _ = ((sz.W n : ℕ) : ℝ) ^ d * g ^ 2 := by field_simp
  have hmain := BAExp14c_twLoop2X_le n ((baFMz sz z).GM n t ω) ((baFMz sz z).GM n t ω)
    (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
      ∑ y ∈ twBlk n b, (baFMz sz z).GM n t ω u y * twChg ((baFMz sz z).GM n t ω) σ y x)
    (fun c₁ c₂ c₃ c₄ => ρ c₁ c₂ c₃ c₄ *
      (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
        (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)) a (Bd := g ^ 2)
    (fun u x => (hGM u x).trans hg2) (fun u x => (hGM u x).trans hg2) hA
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  calc ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄ * (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
        (baFMz sz z).GM n t ω u v * (baFMz sz z).GM n t ω v u else 1)‖
      ≤ ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
        refine Finset.sum_le_sum fun c₁ _ => Finset.sum_le_sum fun c₂ _ => Finset.sum_le_sum fun c₃ _ =>
          Finset.sum_le_sum fun c₄ _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hXb c₂ c₄) (norm_nonneg _)
    _ = (∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖) * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
        simp only [Finset.sum_mul]
    _ ≤ ((Fintype.card (Zd d (sz.L n)) : ℝ) * Cρ) * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ∑ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ c₁ c₂ c₃ c₄‖ ≤ ∑ c₁ : Zd d (sz.L n), Cρ := Finset.sum_le_sum fun c₁ _ => hρ c₁
          _ = (Fintype.card (Zd d (sz.L n)) : ℝ) * Cρ := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem BAExp14c_leafAvg_fold {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡)
    {sz : Sizes d} {z : ℕ → ℂ} (hf : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n)
    (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (hE : STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t)
    (hmax : STLmaxgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t) (q : BAPGraph (Fin 2)) (hq : BAFoldLeafT q) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p _ => ‖∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n p.1, ∑ y ∈ twBlk n p.2,
          q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![x, y]) ∂(Sizes.seqP (sz.withLam 0))‖)
      (fun n _ _ => t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) := by
  obtain ⟨σ, e, ρ, h1, h2⟩ := hq
  obtain ⟨Cρ, hC⟩ := h2 d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hf.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (BAS3Close_data sz hf n (ht0 n) (htT n)).1
  have hρ : ∀ᶠ n in atTop, ∀ p : Bool × Zd d (sz.L n) × Zd d (sz.L n),
      (∀ c₁, ∑ c₂, ∑ c₃, ∑ c₄, ‖ρ d sz z n (t n) p.2.1 p.2.2 c₁ c₂ c₃ c₄‖ ≤ Cρ) ∧
        (∀ c₄, ∑ c₁, ∑ c₂, ∑ c₃, ‖ρ d sz z n (t n) p.2.1 p.2.2 c₁ c₂ c₃ c₄‖ ≤ Cρ) := by
    filter_upwards [hC] with n hn p
    exact hn (t n) (ht0 n) (htT n) p.2.1 p.2.2
  -- the random factor of the nodes #17, #47 is `≺ W^d Bctl` (`baS3Xprec_holds`), the constant `1` too (`TwistFold2_one_prec`)
  have hXprec : PrecL sz (Sizes.seqP (sz.withLam 0))
      (U := fun n => (Bool × Zd d (sz.L n) × Zd d (sz.L n)) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n q' ω => ‖(if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n q'.2.2.1, ∑ v ∈ twBlk n q'.2.2.2.2,
        (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u else 1)‖)
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ d * sz.Bctl n (t n)) := by
    cases e
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact TwistFold2_one_prec hsz (Sizes.seqP (sz.withLam 0)) 𝔡 hf.1.2.2.2.2 t ht0 (fun n => (ht1 n).le)
        (fun n _ _ _ _ _ _ => (1 : ℂ)) (fun n p c₁ c₂ c₃ c₄ ω => by simp)
    · simp only [↓reduceIte]
      exact baS3Xprec_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT hE hmax
  have hY := twFold2Prec_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT hE hmax Cρ
    (fun n p c₁ c₂ c₃ c₄ => ρ d sz z n (t n) p.2.1 p.2.2 c₁ c₂ c₃ c₄) hρ
    (fun n p c₁ c₂ c₃ c₄ ω => if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
        (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u else 1) hXprec
  -- the family `Y` (the average without its factor `t`) at the tail charge `σ`
  let Yf : ∀ n : ℕ, Zd d (sz.L n) × Zd d (sz.L n) → sz.SeqΩ → ℂ := fun n v ω =>
    twLoop2X n ((baFMz sz z).GM n (t n) ω) ((baFMz sz z).GM n (t n) ω)
      (fun (u x : Idx d (sz.L n) (sz.W n)) => (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ *
        ∑ y ∈ twBlk n v.2, (baFMz sz z).GM n (t n) ω u y * twChg ((baFMz sz z).GM n (t n) ω) σ y x)
      (fun c₁ c₂ c₃ c₄ => ρ d sz z n (t n) v.1 v.2 c₁ c₂ c₃ c₄ *
        (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v' ∈ twBlk n c₄,
          (baFMz sz z).GM n (t n) ω u v' * (baFMz sz z).GM n (t n) ω v' u else 1)) v.1
  have hY' : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Zd d (sz.L n) × Zd d (sz.L n))
      (fun n v ω => ‖Yf n v ω‖) (fun n _ _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) :=
    StochDomAt.precomp_param hY (fun n (v : Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((σ, v.1, v.2) : Bool × Zd d (sz.L n) × Zd d (sz.L n)))
  -- the polynomial envelope of `Y` and the floor of the control (the first moment off the failure event)
  set c : ℝ := |1 - ε| + 1 with hc
  have henv : ∀ᶠ n in atTop, ∀ (v : Zd d (sz.L n) × Zd d (sz.L n)) (ω : sz.SeqΩ),
      ‖Yf n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 + 8 * c) := by
    filter_upwards [BAExp14c_scale hd hκ hf 0, (tendsto_natCast_atTop_iff.2 hsz).eventually (eventually_ge_atTop Cρ), hρ]
      with n hs hCn hρn v ω
    obtain ⟨hgN, -, h1N⟩ := hs (t n) (ht0 n) (htT n)
    have hη0 : 0 < (baFMz sz z).eta n (t n) := BAExp14a_eta_pos hκ hf n (ht0 n) (htT n)
    have hg1 : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ + 1 := by
      have := inv_nonneg.2 hη0.le; linarith
    have hpoint := BAExp14c_Y_le (z := z) (t := t n) ω σ v.1 v.2 (g := ((baFMz sz z).eta n (t n))⁻¹ + 1) (Cρ := Cρ) hg1
      (fun u w => BAExp14c_GM_le hκ hf (ht0 n) (htT n) ω u w)
      (fun c₁ c₂ c₃ c₄ => ρ d sz z n (t n) v.1 v.2 c₁ c₂ c₃ c₄) (hρn (σ, v.1, v.2)).1 e
    refine (show ‖Yf n v ω‖ ≤ _ from hpoint).trans ?_
    have hCρ0 : 0 ≤ Cρ := by
      refine le_trans ?_ ((hρn (σ, 0, 0)).1 0)
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hcardZ : (Fintype.card (Zd d (sz.L n)) : ℝ) = ((sz.L n : ℕ) : ℝ) ^ d := by
      have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
      simp [Zd, ZMod.card]
    have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
      simp only [Sizes.size]; push_cast; ring
    set g : ℝ := ((baFMz sz z).eta n (t n))⁻¹ + 1 with hg
    have hg0 : 0 ≤ g := by linarith
    have hg8 : g ^ 8 ≤ (((sz.size n : ℕ) : ℝ) ^ c) ^ 8 := pow_le_pow_left₀ hg0 hgN 8
    have h8 : (((sz.size n : ℕ) : ℝ) ^ c) ^ 8 = ((sz.size n : ℕ) : ℝ) ^ (8 * c) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
    calc ((Fintype.card (Zd d (sz.L n)) : ℝ) * Cρ) * (((sz.W n : ℕ) : ℝ) ^ d * g ^ 2) * (g ^ 2) ^ 3
        = ((sz.size n : ℕ) : ℝ) * Cρ * g ^ 8 := by rw [hcardZ, hNe]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ c) ^ 8 := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left hCn hN0.le) hg8 (by positivity) (by positivity)
          nlinarith
      _ = ((sz.size n : ℕ) : ℝ) ^ (2 + 8 * c) := by
          rw [h8, Real.rpow_add hN0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
  have hfloor : ∀ᶠ n in atTop, ∀ v : Zd d (sz.L n) × Zd d (sz.L n), ((sz.size n : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) ≤
      (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) := by
    refine Eventually.of_forall fun n v => ?_
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    exact BAExp14a_floor n (ht0 n) (ht1 n)
  have hint := BAExp14a_prec_integral (P := Sizes.seqP (sz.withLam 0)) hsz Yf
    (fun n _ => (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) (Kenv := 2 + 8 * c) (Kf := 5 / 2) henv hfloor hY'
  -- restore the factor `t`
  refine (BAExp14a_det_iff hsz _ _).2 ?_
  intro τ hτ
  have hI := (BAExp14a_det_iff hsz _ _).1 hint τ hτ
  filter_upwards [hI] with n hn
  rintro ⟨a, b⟩
  have hpt : ∀ ω : sz.SeqΩ, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
      q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![x, y]) = (t n : ℂ) * Yf n (a, b) ω := by
    intro ω
    rw [h1 d κ ε 𝔠 𝔡 sz z hf n (t n) (ht0 n) (htT n) ω a b]
    have hfun : (fun c₁ c₂ c₃ c₄ => (t n : ℂ) * ρ d sz z n (t n) a b c₁ c₂ c₃ c₄ *
        (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
          (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u else 1)) =
        fun c₁ c₂ c₃ c₄ => (t n : ℂ) * (ρ d sz z n (t n) a b c₁ c₂ c₃ c₄ *
        (if e then (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ u ∈ twBlk n c₂, ∑ v ∈ twBlk n c₄,
          (baFMz sz z).GM n (t n) ω u v * (baFMz sz z).GM n (t n) ω v u else 1)) := by
      funext c₁ c₂ c₃ c₄; ring
    rw [hfun]
    exact BAExp14c_twLoop2X_smul n _ _ _ _ _ a
  dsimp only
  refine le_of_eq_of_le (congrArg norm (integral_congr_ae (μ := Sizes.seqP (sz.withLam 0))
    (Eventually.of_forall hpt))) ?_
  rw [integral_const_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ht0 n)]
  calc t n * ‖∫ ω, Yf n (a, b) ω ∂(Sizes.seqP (sz.withLam 0))‖
      ≤ t n * (((sz.size n : ℕ) : ℝ) ^ τ * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hn (a, b)) (ht0 n)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) := by ring

end FoldBranch

/-- **Target 5 (b)** (`T2464_BAS3LeafAvg`): the averaged leaf bound under the disjunction of 0851 Q3.  A `BAG5LeafProps` leaf goes through the per-pair pin
and is then averaged (with the `x ~ y` count); a fold leaf goes through L4d2a directly, in averaged form. -/
theorem baS3LeafAvg_holds : ∀ d : ℕ, BAS3LeafAvg d := by
  intro d hpin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT μ hE hLW hmax hLK hDec q hq
  rcases hq with hq | hq
  · exact BAExp14c_leafAvg_G5 hd hκ hε h𝔡 hf ht0 htT q hq
      (hpin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT hE hLW hmax hLK hDec q hq)
  · exact BAExp14c_leafAvg_fold hd hκ hε h𝔡 hf ht0 htT hE hmax q hq

/-! ## 6. The conditional assembly of S3 (target 6) -/

section Assembly

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ}

/-- The sum over a list commutes with the finite block sums. -/
private theorem BAExp14c_list_swap {ι κ' : Type*} (L : List κ') (A B' : Finset ι) (f : κ' → ι → ι → ℂ) :
    ∑ x ∈ A, ∑ y ∈ B', (L.map fun q => f q x y).sum = (L.map fun q => ∑ x ∈ A, ∑ y ∈ B', f q x y).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib]
    rw [ih]

/-- `‖Σ_{q ∈ l} f q‖ ≤ |l| G` for `‖f q‖ ≤ G`. -/
private theorem BAExp14c_list_norm_sum_le {α : Type*} (l : List α) (f : α → ℂ) (G : ℝ) (h : ∀ q ∈ l, ‖f q‖ ≤ G) :
    ‖(l.map f).sum‖ ≤ l.length * G := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    refine (norm_add_le _ _).trans ?_
    have h1 := h a (List.mem_cons_self)
    have h2 := ih fun q hq => h q (List.mem_cons_of_mem a hq)
    linarith

/-- Every graph value (not packed) is integrable over the carrier law. -/
theorem BAExp14c_integrable_graph {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hf : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n) {Ex Ix : Type} [Fintype Ex] [DecidableEq Ex] [Fintype Ix] [DecidableEq Ix]
    (T : BAGraph Ex Ix) (ℓ : Ex → Idx d (sz.L n) (sz.W n)) :
    Integrable (fun ω : sz.SeqΩ => T.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ℓ) (BAExp14a_μ sz) := by
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hI := BAExpandId_integrable_val (d := d) (L := sz.L n) (W := sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n)
    (BAflowEs sz z n) t ((baFMz sz z).m n) hr.1 ht0 ht1 T ℓ
  have hmap := Sizes.seqP_map_slice (sz.withLam 0) n
  have hmeas : AEMeasurable (Sizes.slice (sz.withLam 0) n) (Sizes.seqP (sz.withLam 0)) :=
    (Sizes.measurable_slice (sz.withLam 0) n).aemeasurable
  have hI' : Integrable (fun ω' : Ω d (sz.L n) (sz.W n) => T.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n)
      (BAflowEs sz z n) t ((baFMz sz z).m n) ω') ℓ) (Measure.map (Sizes.slice (sz.withLam 0) n) (Sizes.seqP (sz.withLam 0))) := by
    convert hI using 1
    exact hmap
  exact (integrable_map_measure hI'.aestronglyMeasurable hmeas).1 hI'

/-- **The expectation of a root's block average is the sum over its list** (the identity over `PF`, carried to the carrier law along the slice). -/
private theorem BAExp14c_Eroot (hf : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    {I : Type} [Fintype I] [DecidableEq I] (R : BAGraph (Fin 2) I) (L : List (BAPGraph (Fin 2)))
    (hid : ∀ x y : Idx d (sz.L n) (sz.W n),
      ∫ ω, R.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) ω) ![x, y]
        ∂(PF d (sz.L n) (sz.W n) 0) =
        (L.map fun q => ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) ω)
          ![x, y] ∂(PF d (sz.L n) (sz.W n) 0)).sum)
    (a b : Zd d (sz.L n)) :
    ∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
        R.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y]) ∂(BAExp14a_μ sz) =
      (L.map fun q => ∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
        q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
          (BAExp14a_slc sz n ω)) ![x, y]) ∂(BAExp14a_μ sz)).sum := by
  classical
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n ht0 ht
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hRpf : ∀ x y : Idx d (sz.L n) (sz.W n), Integrable (fun ω' : Ω d (sz.L n) (sz.W n) =>
      R.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) ω') ![x, y])
      (PF d (sz.L n) (sz.W n) 0) := fun x y =>
    BAExpandId_integrable_val (sz.three_le_L n) _ _ t _ hr.1 ht0 ht1 R _
  have hqpf : ∀ (q : BAPGraph (Fin 2)) (x y : Idx d (sz.L n) (sz.W n)), Integrable (fun ω' : Ω d (sz.L n) (sz.W n) =>
      q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) ω') ![x, y])
      (PF d (sz.L n) (sz.W n) 0) := fun q x y =>
    BAExpandId_integrable_pval (sz.three_le_L n) _ _ t _ hr.1 ht0 ht1 q _
  rw [BAExp14c_int_avg (twBlk n a) (twBlk n b) _ (fun x y => BAExp14c_integrable_graph hf ht0 ht R ![x, y])]
  have hR : ∀ x y : Idx d (sz.L n) (sz.W n), ∫ ω, R.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n)
      (BAflowEs sz z n) t ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y] ∂(BAExp14a_μ sz) =
      (L.map fun q => ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![x, y] ∂(BAExp14a_μ sz)).sum := by
    intro x y
    rw [BAExp14c_int_slice n _ (hRpf x y).aestronglyMeasurable, hid x y]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    exact (BAExp14c_int_slice n _ (hqpf q x y).aestronglyMeasurable).symm
  simp only [hR]
  have hq : ∀ q : BAPGraph (Fin 2), ∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
      q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![x, y]) ∂(BAExp14a_μ sz) =
      ((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n)
        (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y] ∂(BAExp14a_μ sz) := fun q =>
    BAExp14c_int_avg (twBlk n a) (twBlk n b) _ (fun x y => BAExp14c_integrable_val hf ht0 ht q ![x, y])
  simp only [hq]
  rw [List.sum_map_mul_left, BAExp14c_list_swap L (twBlk n a) (twBlk n b)
    (fun q x y => ∫ ω, q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
      (BAExp14a_slc sz n ω)) ![x, y] ∂(BAExp14a_μ sz))]

/-- `𝔼` of the `[a]×[b]` average of a graph value at the carrier. -/
private def BAExp14c_Av (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (a b : Zd d (sz.L n)) (q : BAPGraph (Fin 2)) : ℂ :=
  ∫ ω, (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
    q.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
      (BAExp14a_slc sz n ω)) ![x, y]) ∂(BAExp14a_μ sz)

/-- The block average of a (non-packed) graph value is integrable. -/
private theorem BAExp14c_integrable_avg (hf : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ BAflowT0 sz z n)
    {I : Type} [Fintype I] [DecidableEq I] (R : BAGraph (Fin 2) I) (a b : Zd d (sz.L n)) :
    Integrable (fun ω : sz.SeqΩ => (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b,
      R.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) t ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![x, y])) (BAExp14a_μ sz) :=
  (integrable_finsetSum _ fun x _ => integrable_finsetSum _ fun y _ =>
    BAExp14c_integrable_graph hf ht0 ht R ![x, y]).const_mul _

/-- All four S3 families vanish at `t = 0` (`BAlwS 0 = 0` in every summand). -/
private theorem BAExp14c_FS3_zero (n : ℕ) (ω : sz.SeqΩ) (j : Fin 4) (σ : Bool) (a b : Zd d (sz.L n)) :
    BAExp14b_FS3 sz z n 0 ω j σ a b = 0 := by
  fin_cases j <;>
  simp [BAExp14b_FS3, BAExp14b_FD1X, BAExp14b_FD2X, BAExp14b_FT3CX, BAExp14b_outerDX, BAlwS]

/-- The bound for a family from the sums over the lists: `T E = Σ_{L1} A - Σ_{L2} A` and `‖A q‖ ≤ M T R'` give `‖E‖ ≤ (|L1| + |L2|) M R'`. -/
private theorem BAExp14c_Ebound {T M R' : ℝ} (hT : 0 < T) (E : ℂ) (L1 L2 : List (BAPGraph (Fin 2))) (A : BAPGraph (Fin 2) → ℂ)
    (hE : (T : ℂ) * E = (L1.map A).sum - (L2.map A).sum) (h1 : ∀ q ∈ L1, ‖A q‖ ≤ M * (T * R'))
    (h2 : ∀ q ∈ L2, ‖A q‖ ≤ M * (T * R')) :
    ‖E‖ ≤ ((L1.length + L2.length : ℕ) : ℝ) * M * R' := by
  have hn : T * ‖E‖ ≤ ((L1.length + L2.length : ℕ) : ℝ) * (M * (T * R')) := by
    calc T * ‖E‖ = ‖(T : ℂ) * E‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hT.le]
      _ = ‖(L1.map A).sum - (L2.map A).sum‖ := by rw [hE]
      _ ≤ ‖(L1.map A).sum‖ + ‖(L2.map A).sum‖ := norm_sub_le _ _
      _ ≤ L1.length * (M * (T * R')) + L2.length * (M * (T * R')) :=
          add_le_add (BAExp14c_list_norm_sum_le L1 A _ h1) (BAExp14c_list_norm_sum_le L2 A _ h2)
      _ = _ := by push_cast; ring
  have : T * ‖E‖ ≤ T * (((L1.length + L2.length : ℕ) : ℝ) * M * R') := by
    calc T * ‖E‖ ≤ ((L1.length + L2.length : ℕ) : ℝ) * (M * (T * R')) := hn
      _ = T * (((L1.length + L2.length : ℕ) : ℝ) * M * R') := by ring
  exact le_of_mul_le_mul_left this hT

/-- **The expectations of the four S3 families against the lists** (the bridge, `baS3Bridge_holds`, pathwise; the identities over `PF`, carried to the carrier
law): `T 𝔼 F_j` is the sum of `𝔼 avg q` over the list of the root (`D1X`: `MERGED` minus the sub-root `T3C-tr_0`). -/
private theorem BAExp14c_fam_E (hf : BAFlow sz κ ε 𝔠 𝔡 z) {n : ℕ} {T : ℝ} (hT0 : 0 ≤ T) (hT : T ≤ BAflowT0 sz z n)
    (σ : Bool) (a b : Zd d (sz.L n)) :
    ((T : ℂ) * ∫ ω, BAExp14b_FT3CX sz z n T ω false σ a b ∂(BAExp14a_μ sz) =
      (((baS3RootT0 σ).partition.flatMap fun P => (BAexpand BAselStar 2 P).map Prod.snd).map
        (BAExp14c_Av sz z n T a b)).sum) ∧
    ((T : ℂ) * ∫ ω, BAExp14b_FD1X sz z n T ω σ a b ∂(BAExp14a_μ sz) =
      ((BAS3expandRoot BAselStar 2 0 σ).map (BAExp14c_Av sz z n T a b)).sum -
        (((baS3RootT0 σ).partition.flatMap fun P => (BAexpand BAselStar 2 P).map Prod.snd).map
          (BAExp14c_Av sz z n T a b)).sum) ∧
    ((T : ℂ) * ∫ ω, BAExp14b_FT3CX sz z n T ω true σ a b ∂(BAExp14a_μ sz) =
      ((BAS3expandRoot BAselStar 2 1 σ).map (BAExp14c_Av sz z n T a b)).sum) ∧
    ((T : ℂ) * ∫ ω, BAExp14b_FD2X sz z n T ω σ a b ∂(BAExp14a_μ sz) =
      ((BAS3expandRoot BAselStar 2 2 σ).map (BAExp14c_Av sz z n T a b)).sum) := by
  obtain ⟨ht1, hr, -⟩ := BAS3Close_data sz hf n hT0 hT
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have : NeZero (sz.W n) := ⟨(sz.W_pos n).ne'⟩
  have hbr := fun ω => baS3Bridge_holds d κ ε 𝔠 𝔡 sz z hf n T hT0 hT ω σ a b
  have hid0 := fun x y => baS3RootT0_identity d BAselStar 2 (sz.L n) (sz.W n) (sz.three_le_L n) _ _ T _ hr.1 hT0 ht1 σ x y
  have hid := fun x y => baS3Identity_holds d BAselStar 2 (sz.L n) (sz.W n) (sz.three_le_L n) _ _ T _ hr.1 hT0 ht1 σ x y
  have E0 := BAExp14c_Eroot hf hT0 hT (baS3RootT0 σ) _ hid0 a b
  have EM := BAExp14c_Eroot hf hT0 hT (baS3RootM σ) _ (fun x y => (hid x y).1) a b
  have E1 := BAExp14c_Eroot hf hT0 hT (baS3Root1 σ) _ (fun x y => (hid x y).2.1) a b
  have ED := BAExp14c_Eroot hf hT0 hT (baS3RootD σ) _ (fun x y => (hid x y).2.2) a b
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← integral_const_mul]
    exact Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => (hbr ω).1)) E0
  · rw [← integral_const_mul]
    have hpt : ∀ ω : sz.SeqΩ, (T : ℂ) * BAExp14b_FD1X sz z n T ω σ a b =
        (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, (baS3RootM σ).val (BAlwData d (sz.L n) (sz.W n)
          (BAflowLam0 sz z n) (BAflowEs sz z n) T ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y]) -
        (((((sz.W n : ℕ) : ℂ) ^ d)⁻¹) ^ 2 * ∑ x ∈ twBlk n a, ∑ y ∈ twBlk n b, (baS3RootT0 σ).val (BAlwData d (sz.L n) (sz.W n)
          (BAflowLam0 sz z n) (BAflowEs sz z n) T ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![x, y]) := by
      intro ω
      linear_combination (hbr ω).2.1 - (hbr ω).1
    rw [integral_congr_ae (Eventually.of_forall hpt),
      integral_sub (BAExp14c_integrable_avg hf hT0 hT (baS3RootM σ) a b) (BAExp14c_integrable_avg hf hT0 hT (baS3RootT0 σ) a b),
      EM, E0]
    rfl
  · rw [← integral_const_mul]
    exact Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => (hbr ω).2.2.1)) E1
  · rw [← integral_const_mul]
    exact Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => (hbr ω).2.2.2)) ED

end Assembly

/-- **Target 6, the conditional assembly** (`T2464_S3OfLeaf`; band `lwExpG5'_of_expand`, `LWExpTerm3:2031`): the leaf pin gives the merged S3 pin
`BAExp14bS3`.  For `t > 0` the family is `t⁻¹ ×` the root average (target 2); its expectation is the sum over the list of the root (target 1 for `T3C-tr_0`,
`baS3Identity_holds` for the others), every term of the lists is a `BAG5LeafProps` leaf or a `BAFoldLeafT` leaf (target 4), and target 5 bounds each by
`t (1 - t)⁻¹ B^{5/2}`; the lists have lengths independent of `n`.  For `t = 0` every family carries `BAlwS 0 = 0`. -/
theorem baExp14bS3_of_leaf : ∀ d : ℕ, BAExp14bS3OfLeaf d := by
  intro d hpin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT μ hE hLW hmax hLK hDec
  have hsz : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hf.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (BAS3Close_data sz hf n (ht0 n) (htT n)).1
  have hLA := baS3LeafAvg_holds d hpin hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hf t ht0 htT hE hLW hmax hLK hDec
  have hleaf := baS3CloseT_holds
  have hleaf0 : ∀ s : Bool, ∀ q ∈ (baS3RootT0 s).partition.flatMap (fun P => (BAexpand BAselStar 2 P).map Prod.snd),
      BAG5LeafProps (fun _ _ => [q]) ∨ BAFoldLeafT q := fun s q hq => hleaf 0 s q (baS3RootT0_list BAselStar 2 s q hq)
  refine (BAExp14a_det_iff hsz _ _).2 ?_
  intro τ hτ
  have hq1 : ∀ q : BAPGraph (Fin 2), (BAG5LeafProps (fun _ _ => [q]) ∨ BAFoldLeafT q) → ∀ᶠ n in atTop,
      ∀ p : Zd d (sz.L n) × Zd d (sz.L n), ‖BAExp14c_Av sz z n (t n) p.1 p.2 q‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :=
    fun q hq => (BAExp14a_det_iff hsz _ _).1 (hLA q hq) (τ / 2) (half_pos hτ)
  set Lt0 : Bool → List (BAPGraph (Fin 2)) := fun s =>
    (baS3RootT0 s).partition.flatMap (fun P => (BAexpand BAselStar 2 P).map Prod.snd) with hLt0
  have hq2 : ∀ᶠ n in atTop,
      (∀ (r : Fin 3) (s : Bool), ∀ q ∈ BAS3expandRoot BAselStar 2 r s, ∀ p : Zd d (sz.L n) × Zd d (sz.L n),
        ‖BAExp14c_Av sz z n (t n) p.1 p.2 q‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))) ∧
      (∀ s : Bool, ∀ q ∈ Lt0 s, ∀ p : Zd d (sz.L n) × Zd d (sz.L n),
        ‖BAExp14c_Av sz z n (t n) p.1 p.2 q‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)))) := by
    refine Filter.Eventually.and ?_ ?_
    · rw [Filter.eventually_all]; intro r
      rw [Filter.eventually_all]; intro s
      exact (Filter.eventually_all_finite (List.finite_toSet _)).2 (fun q hq => hq1 q (hleaf r s q hq))
    · rw [Filter.eventually_all]; intro s
      exact (Filter.eventually_all_finite (List.finite_toSet _)).2 (fun q hq => hq1 q (hleaf0 s q hq))
  set Λn : ℕ := ∑ s : Bool, ((Lt0 s).length + ∑ r : Fin 3, (BAS3expandRoot BAselStar 2 r s).length) with hΛn
  have hlen : ∀ (r : Fin 3) (s : Bool), (Lt0 s).length + (BAS3expandRoot BAselStar 2 r s).length ≤ Λn := by
    intro r s
    cases s <;> fin_cases r <;> simp [hΛn, Fin.sum_univ_three] <;> omega
  have hΛ : ∀ᶠ n in atTop, (Λn : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp (tendsto_natCast_atTop_iff.2 hsz)).eventually (eventually_ge_atTop (Λn : ℝ))
  filter_upwards [hq2, hΛ] with n hqq hΛn'
  obtain ⟨hqa, hqb⟩ := hqq
  rintro ⟨⟨j, ⟨σc, σo⟩, ⟨ac, ao⟩⟩, -⟩
  have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
  have hR0 : 0 ≤ (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ) :=
    mul_nonneg (inv_nonneg.2 (by linarith [ht1 n])) (Real.rpow_nonneg hB0.le _)
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hNN : ((sz.size n : ℕ) : ℝ) ^ τ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    have hNpos : 0 < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    rw [← Real.rpow_add hNpos]; congr 1; ring
  -- `len M R' ≤ N^τ R'` for a total list length `len ≤ Λ ≤ N^{τ/2} = M`
  have hfin : ∀ len : ℕ, len ≤ Λn → (len : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
      ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    intro len hl
    rw [hNN]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((Nat.cast_le.2 hl).trans hΛn') hN0) hR0
  have key : ∀ (j : Fin 4) (σ : Bool) (a b : Zd d (sz.L n)),
      ‖∫ ω, BAExp14b_FS3 sz z n (t n) ω j σ a b ∂μ‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ)) := by
    intro j σ a b
    rcases (ht0 n).eq_or_lt with h0 | hpos
    · have h00 : ∀ ω : sz.SeqΩ, BAExp14b_FS3 sz z n (t n) ω j σ a b = 0 := fun ω => by
        rw [← h0]; exact BAExp14c_FS3_zero n ω j σ a b
      calc ‖∫ ω, BAExp14b_FS3 sz z n (t n) ω j σ a b ∂μ‖ = ‖∫ _ω, (0 : ℂ) ∂μ‖ := by
            congr 1; exact integral_congr_ae (Eventually.of_forall h00)
        _ = 0 := by simp
        _ ≤ _ := mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hR0
    · obtain ⟨hE2, hE0, hE3, hE1⟩ := BAExp14c_fam_E hf (ht0 n) (htT n) σ a b
      have hA1 : ∀ r : Fin 3, ∀ q ∈ BAS3expandRoot BAselStar 2 r σ, ‖BAExp14c_Av sz z n (t n) a b q‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :=
        fun r q hq => hqa r σ q hq (a, b)
      have hA2 : ∀ q ∈ Lt0 σ, ‖BAExp14c_Av sz z n (t n) a b q‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (t n * ((1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))) :=
        fun q hq => hqb σ q hq (a, b)
      fin_cases j
      · have hb := BAExp14c_Ebound (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (R' := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
          hpos _ (BAS3expandRoot BAselStar 2 0 σ) (Lt0 σ) (BAExp14c_Av sz z n (t n) a b) hE0 (hA1 0) hA2
        refine hb.trans ?_
        have := hfin ((BAS3expandRoot BAselStar 2 0 σ).length + (Lt0 σ).length) (by have := hlen 0 σ; omega)
        exact this
      · have hb := BAExp14c_Ebound (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (R' := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
          hpos _ (BAS3expandRoot BAselStar 2 2 σ) [] (BAExp14c_Av sz z n (t n) a b) (by rw [hE1]; simp) (hA1 2)
          (fun q hq => absurd hq (List.not_mem_nil))
        refine hb.trans ?_
        exact hfin _ (by have := hlen 2 σ; simp only [List.length_nil, add_zero]; omega)
      · have hb := BAExp14c_Ebound (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (R' := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
          hpos _ (Lt0 σ) [] (BAExp14c_Av sz z n (t n) a b) (by rw [hE2]; simp only [List.map_nil, List.sum_nil, sub_zero]; rfl) hA2
          (fun q hq => absurd hq (List.not_mem_nil))
        refine hb.trans ?_
        exact hfin _ (by have := hlen 0 σ; simp only [List.length_nil, add_zero]; omega)
      · have hb := BAExp14c_Ebound (M := ((sz.size n : ℕ) : ℝ) ^ (τ / 2)) (R' := (1 - t n)⁻¹ * (sz.Bctl n (t n)) ^ (5 / 2 : ℝ))
          hpos _ (BAS3expandRoot BAselStar 2 1 σ) [] (BAExp14c_Av sz z n (t n) a b) (by rw [hE3]; simp) (hA1 1)
          (fun q hq => absurd hq (List.not_mem_nil))
        refine hb.trans ?_
        exact hfin _ (by have := hlen 1 σ; simp only [List.length_nil, add_zero]; omega)
  by_cases hσc : σc
  · simp only [BAExp14bS3Fam, hσc, ↓reduceIte]
    exact key j σo ao ac
  · simp only [BAExp14bS3Fam, hσc, Bool.false_eq_true, ↓reduceIte, Complex.star_def, integral_conj, RCLike.norm_conj]
    exact key j (!σo) ac ao


/-! ## 7. Compiled nonempty instances (namespace `BAExp14cInst`; `d = 3`, `sz0`, `zSeq`, `flow_sz0`, `n = 0`, `t = 1/2`, `half_lt_t0`)

The leaf pin `BAG5LeafPrec` and the five Step 1/2 pins (other gates') stay hypotheses of the examples of targets 5, 6; every deterministic
hypothesis is discharged at the data. -/

/-! ### Target 1 -/

/-! ### Target 2 -/

/-! ### Target 3 -/

/-! ### Target 4 -/

/-! ### Targets 5, 6 -/

end RBM.BA

end
