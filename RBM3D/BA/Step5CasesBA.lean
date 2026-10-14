/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step5KerBA
import RBM3D.BA.CltFlowBA
import RBM3D.BA.SEforLnBA
import RBM3D.BA.GridMartBA
import RBM3D.BA.GridRepTailBA
import RBM3D.Graph.BATermHoldsB
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.Chain.IniTermIGen2
import RBM3D.Induction.DuhamelII

/-!
# U4-BA, row b: the Ward bridge, the six ingredient pins and Step 5 cases (i), (ii), (iv) at BA

Ticket T2501 (row b; DECISIONS §311, §313 (2)).  Paper: arXiv:2507.20274, Steps 3-6 "extend verbatim" to BA
(`7_8:2099-2100`); `lem:pf_step5` case analysis `3_5:1939-2283`; the Ward term `(zYU1)` `3_5:2257-2262`.  Band twins (not
edited): `stWardII_identity` (`Induction/WardII.lean:143`), `stEtermsMid_of_LWT`, `stDuhamelI_holds`, `stDuhamelII_holds`,
`stIniTermI_holds`, `stIniTermII_holds`, `stWardII_holds`.  The check is `docs/tickets/checks/T2501-check.lean`
(pins `T2501_*`).

BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; Step2Mat family
`mkM sz z = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`; `gK = BAflowLam0`, `E = BAflowEs`.

* 9. `step5CasesGen_wardIdent_of_wardCls` (the UN-C3 bridge, generic, the one-index conjugation inline) and
  `baStep5CasesGen_wardIdent` (= `T2501_WardIdentBA`): `baZeroModeGen_wardCls` (U2-BA) with the conjugation of the one-index `𝓛`
  (conjunct 2 of `baStep2_oneLoop`, every `n`, `u`, `ω`) and `𝒦` (clause 3 of `IsKLoopS` through `baKcac_isKLoopS`, `BAReal` only).
* 10. `baSTEtermsMidgL_holds`, `baSTDuhamelIgL_holds`, `baSTDuhamelIIgL_holds`, `baSTIniTermIgL_holds`, `baSTIniTermIIgL_holds`,
  `baSTWardIIgL_holds` (= `T2501_EtermsMidBA`, `_DuhamelIBA`, `_DuhamelIIBA`, `_IniTermIBA`, `_IniTermIIBA`, `_WardIIBA`): one call each of
  the merged generic result with the family table's discharges (`Hf = baEMn2Hf`, `ζf = baEMn2Zf`).
* 11. `baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds` (= `T2501_Step5IBA`, `_IIBA`, `_IVBA`).
* 12. Compiled nonempty instances (section 5).

Helpers are private and carry the stem `Step5CasesBA_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open private SEforLnBA_Ksol_isKLoopS from RBM3D.BA.SEforLnBA

open MeasureTheory ProbabilityTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 9: the Ward identity from the Ward class and the one-index conjugation -/

section Ward

/-- `T a - Q^{(1)} T a = L^{-d} Σ_c T(c, a₂)` (copy of the private `wardII_zeroMode`, `Induction/WardII.lean:131`). -/
private theorem Step5CasesBA_zeroMode {d : ℕ} (sz : Sizes d) (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ)
    (a : Fin 2 → Zd d (sz.L n)) :
    T a - zeroModeSet d (sz.L n) {0} T a =
      ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), T ![c, a 1] := by
  have hup : ∀ c : Zd d (sz.L n), Function.update a 0 c = ![c, a 1] := by
    intro c
    funext i
    fin_cases i <;> simp
  simp only [zeroModeSet, Finset.toList_singleton, List.foldr_cons, List.foldr_nil, zeroModeOp, avgOp, hup]
  ring

/-- The Ward sum of a Ward family at mixed charges: rotate the label `c` to the end, then the Ward identity. -/
private theorem Step5CasesBA_sum_ward {d L : ℕ} [NeZero L] {κ : ℂ} {T : LoopIdx (Zd d L) → ℂ}
    (h : ZeroModeGen_WardFam d L κ T) (s : Bool) (a₁ : Zd d L) :
    ∑ c : Zd d L, T ⟨[s, !s], [c, a₁]⟩ = κ * (T ⟨[true], [a₁]⟩ - T ⟨[false], [a₁]⟩) := by
  have hw := h.2 (!s) [] [a₁] rfl
  simp only [Bool.not_not] at hw
  calc ∑ c : Zd d L, T ⟨[s, !s], [c, a₁]⟩ = ∑ c : Zd d L, T ⟨[!s, s], [a₁, c]⟩ :=
        Finset.sum_congr rfl fun c _ => h.1 s c [!s] [a₁] rfl
    _ = _ := hw

/-- **Target 9, the UN-C3 bridge** (`T2501_WardIdentBA` shape; pattern `stWardII_identity`, `Induction/WardII.lean:143`): a carrier
in the Ward class `ZeroModeGen_WardCls` whose one-index `𝓛` and `𝒦` at the two charges are complex conjugates satisfies the
`(zYU1)` identity.  `κ_W = (2 i W^d η)⁻¹`; no `η ≠ 0` is needed (at `η = 0` both sides are `0` in `ℂ`). -/
theorem step5CasesGen_wardIdent_of_wardCls {d : ℕ} (sz : Sizes d) (C : FlowFM sz) (hW : ZeroModeGen_WardCls sz C)
    (hc : ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
      C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω = (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω) ∧
      C.K n u (fun _ : Fin 1 => false) (fun _ => a) = (starRingEnd ℂ) (C.K n u (fun _ : Fin 1 => true) (fun _ => a))) :
    Step5CasesGen_WardIdent C := by
  intro n u hu0 hu1 ω σ hσ a
  obtain ⟨TL, TK, hL, hK, hWL, hWK⟩ := hW n u hu0 hu1 ω
  obtain ⟨hcL, hcK⟩ := hc n u hu0 hu1 ω (a 1)
  have hσ1 : σ 1 = !σ 0 := (by decide : ∀ x y : Bool, x ≠ y → y = !x) _ _ hσ
  have hL2 : ∀ c : Zd d (sz.L n), C.L n u σ ![c, a 1] ω = TL ⟨[σ 0, !σ 0], [c, a 1]⟩ := fun c => by
    rw [hL 2 σ ![c, a 1]]
    simp [loopOf, List.ofFn_succ, hσ1]
  have hK2 : ∀ c : Zd d (sz.L n), C.K n u σ ![c, a 1] = TK ⟨[σ 0, !σ 0], [c, a 1]⟩ := fun c => by
    rw [hK 2 σ ![c, a 1]]
    simp [loopOf, List.ofFn_succ, hσ1]
  have hL1 : ∀ s : Bool, C.L n u (fun _ : Fin 1 => s) (fun _ => a 1) ω = TL ⟨[s], [a 1]⟩ := fun s => by
    rw [hL 1 (fun _ : Fin 1 => s) (fun _ => a 1)]
    simp [loopOf, List.ofFn_succ]
  have hK1 : ∀ s : Bool, C.K n u (fun _ : Fin 1 => s) (fun _ => a 1) = TK ⟨[s], [a 1]⟩ := fun s => by
    rw [hK 1 (fun _ : Fin 1 => s) (fun _ => a 1)]
    simp [loopOf, List.ofFn_succ]
  refine (Step5CasesBA_zeroMode sz n (fun a' => C.L n u σ a' ω - C.K n u σ a') a).trans ?_
  simp only [hL2, hK2, Finset.sum_sub_distrib, Step5CasesBA_sum_ward hWL, Step5CasesBA_sum_ward hWK]
  rw [hL1 false, hL1 true] at hcL
  rw [hK1 false, hK1 true] at hcK
  rw [hL1 true, hK1 true]
  have him : (TL ⟨[true], [a 1]⟩ - TL ⟨[false], [a 1]⟩) - (TK ⟨[true], [a 1]⟩ - TK ⟨[false], [a 1]⟩) =
      2 * Complex.I * (((TL ⟨[true], [a 1]⟩ - TK ⟨[true], [a 1]⟩).im : ℝ) : ℂ) := by
    rw [hcL, hcK]
    have h := Complex.sub_conj (TL ⟨[true], [a 1]⟩ - TK ⟨[true], [a 1]⟩)
    rw [map_sub] at h
    push_cast at h
    linear_combination h
  have hsz : (((sz.size n : ℕ) : ℂ)) = ((sz.W n : ℕ) : ℂ) ^ d * ((sz.L n : ℕ) : ℂ) ^ d := by
    simp [Sizes.size, mul_pow]
  rw [← mul_sub, him, hsz]
  by_cases hη : (C.eta n u : ℂ) = 0
  · simp [hη]
  · have hW0 : ((sz.W n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show sz.W n ≠ 0 from (sz.W_pos n).ne')
    have hL0 : ((sz.L n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show sz.L n ≠ 0 by have := sz.three_le_L n; omega)
    field_simp

/-- **Target 9, `baStep5CasesGen_wardIdent`** (`T2501_WardIdentBA`): the `(zYU1)` identity along every BA flow, from the Ward class
`baZeroModeGen_wardCls` (U2-BA) and the one-index conjugation.  `𝓛`: conjunct 2 of `baStep2_oneLoop` (every `n`, `u`, `ω`); `𝒦`: clause 3 of
`IsKLoopS` for `BAKsol` (`SEforLnBA_Ksol_isKLoopS`, from `baKcac_isKLoopS`; `BAReal` only, no `0 < g₀`, so every `n`). -/
theorem baStep5CasesGen_wardIdent (d : ℕ) :
    ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z → Step5CasesGen_WardIdent (baFMz sz z) := by
  intro sz κ ε 𝔠 𝔡 z hκ hflow
  refine step5CasesGen_wardIdent_of_wardCls sz _ (baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow) ?_
  intro n u hu0 hu1 ω a
  refine ⟨(baStep2_oneLoop sz κ ε 𝔠 𝔡 z hκ hflow).2 n u a ω, ?_⟩
  have hK := SEforLnBA_Ksol_isKLoopS (W := sz.W n) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)
  have h := hK.2.2 u ⟨hu0, hu1⟩
  have e : ∀ s : Bool, KLloopOf d (sz.L n) (fun _ : Fin 1 => s) (fun _ => a) = ⟨[s], [a]⟩ := fun s => by
    simp [KLloopOf]
  change BAKsol d (sz.L n) (sz.W n) _ _ u (KLloopOf d (sz.L n) (fun _ : Fin 1 => false) (fun _ => a)) =
    (starRingEnd ℂ) (BAKsol d (sz.L n) (sz.W n) _ _ u (KLloopOf d (sz.L n) (fun _ : Fin 1 => true) (fun _ => a)))
  rw [e, e, h false a, h true a]
  simp [PropSpin]

end Ward

/-! ## 2. The inline premises and the family premises shared by the pins -/

section Family

variable {d : ℕ}

/-- `hmn`: `‖m_n‖ ≤ 1` at the carrier `baStep2Mat sz g₀ E` along a BA flow (copy of the private `Step5KerBA_hmn`,
`BA/Step5KerBA.lean:535`; `BAm_norm_le_one`, `Ward:136`, at the `BASelf` datum of `BAflow_real`). -/
private theorem Step5CasesBA_hmn {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n‖ ≤ 1 :=
  BAm_norm_le_one d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) _ (by simp)
    (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1

/-- `hSr`: `S = 1`, so the row sums of `‖S‖` are `1` (copy of the private `Step5KerBA_hSr`, `BA/Step5KerBA.lean:541`). -/
private theorem Step5CasesBA_hSr (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (a : Zd d (sz.L n)) :
    ∑ b, ‖(baStep2Mat sz lam0 E).S n a b‖ ≤ 1 := by
  have h1 : ∀ b, ‖(baStep2Mat sz lam0 E).S n a b‖ = if a = b then (1 : ℝ) else 0 := fun b => by
    change ‖(1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) a b‖ = _
    rw [Matrix.one_apply]; split_ifs <;> simp
  simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true, le_refl]

/-- `hGR`: `GridRepTailGen_Ker` at the BA carrier, every `n` (`gridRepTailGen_ker_BA` with `BAflow_real`). -/
private theorem Step5CasesBA_hGR (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : GridRepTailGen_Ker (baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).toFlowFM n :=
  gridRepTailGen_ker_BA sz _ _ n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)

end Family

/-! ## 3. Target 10: the six ingredient pins at the BA tuple -/

section Pins

/-- **Target 10, `(S5WG+M000)`, `(S5WG+M)`** (`T2501_EtermsMidBA`): `stEtermsMidgL_of` with `Hf = baEMn2Hf`, `ζf = baEMn2Zf` and the family
table (`hLW` through `stLWTgL_of_LWtermExpG`, `Step2EventsGenTw_baRot3`, `baLWtermExp_holds`; `hNew` = A9, `hFM` = D2). -/
theorem baSTEtermsMidgL_holds : ∀ d : ℕ, 3 ≤ d → STEtermsMidgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stEtermsMidgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 BAflowEs baEMn2Hf baEMn2Zf
    (baStep5CasesGen_flowFacts d)
    (stLWTgL_of_LWtermExpG d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAflowT0 baFMz
      hd (fun _ _ _ _ _ _ h => h.1) (fun sz z => Step2EventsGenTw_baRot3 sz _ _) (baLWtermExp_holds d))
    (baEMn2ExpFacts d) (baEMn2ExpHK hd) (baSTBdatagL_holds d (by omega)) (baStep2_K2 d) (baEtermsMid_newKLKL d)
    (baLemDecCalELipG_flowMod d)
    (fun sz κ ε 𝔠 𝔡 z _ hflow n => Step5CasesBA_hmn hflow n)
    (fun sz κ ε 𝔠 𝔡 z _ _ n a => Step5CasesBA_hSr sz _ _ n a)
    (baStep2Mat_loopForm d)

/-- **Target 10, the integrated hierarchy of case (i)** (`T2501_DuhamelIBA`): `stDuhamelIgL_of` at `gK = BAflowLam0`, `E = BAflowEs`
(`hKer` = target 1, `hGR`, `hGM = baGridMart_holds`, `hKs` = D3 `baKLip_two`). -/
theorem baSTDuhamelIgL_holds : ∀ d : ℕ, 3 ≤ d → STDuhamelIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stDuhamelIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 BAflowEs BAflowLam0
    (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow n => Step5CasesBA_hGR sz κ ε 𝔠 𝔡 z hκ hflow n)
    (baGridMart_holds d) (baSTBdatagL_holds d (by omega)) (baStep2_K2 d) (baLemDecCalELipG_flowMod d)
    (fun sz κ ε 𝔠 𝔡 z _ hflow n => Step5CasesBA_hmn hflow n)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hflow t ht => baKLip_two d hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht)
    (baStep2Mat_loopForm d)
    (fun sz z => Step2EventsGenTw_baGrid sz _ _)
    (fun sz z s t K n k ω => baStep2Mat_Hpath_herm sz _ _ s t K n k ω)

/-- **Target 10, the integrated hierarchy of case (ii)** (`T2501_DuhamelIIBA`): `stDuhamelIIgL_of`, the premises of `baSTDuhamelIgL_holds`. -/
theorem baSTDuhamelIIgL_holds : ∀ d : ℕ, 3 ≤ d → STDuhamelIIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stDuhamelIIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) BAflowT0 BAflowEs BAflowLam0
    (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow n => Step5CasesBA_hGR sz κ ε 𝔠 𝔡 z hκ hflow n)
    (baGridMart_holds d) (baSTBdatagL_holds d (by omega)) (baStep2_K2 d) (baLemDecCalELipG_flowMod d)
    (fun sz κ ε 𝔠 𝔡 z _ hflow n => Step5CasesBA_hmn hflow n)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hflow t ht => baKLip_two d hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht)
    (baStep2Mat_loopForm d)
    (fun sz z => Step2EventsGenTw_baGrid sz _ _)
    (fun sz z s t K n k ω => baStep2Mat_Hpath_herm sz _ _ s t K n k ω)

/-- **Target 10, the initial term of case (i)** (`T2501_IniTermIBA`): `stIniTermIgL_of` with the Ward class `baZeroModeGen_wardCls` and the
X1 class `baIniTermGen_cltFlow`; every law `seqP (sz.withLam 0)` is a probability measure. -/
theorem baSTIniTermIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stIniTermIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 BAflowLam0
    (fun sz => inferInstance) (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow => baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow) (baIniTermGen_cltFlow d)

/-- **Target 10, the initial terms of case (ii)** (`T2501_IniTermIIBA`): `stIniTermIIgL_of` with target 1. -/
theorem baSTIniTermIIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stIniTermIIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 BAflowLam0
    (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)

/-- **Target 10, the Ward term `(zYU1)`** (`T2501_WardIIBA`): `stWardIIgL_of` with target 9. -/
theorem baSTWardIIgL_holds : ∀ d : ℕ, 3 ≤ d → STWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stWardIIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
    (baStep5CasesGen_flowFacts d) (baStep5CasesGen_wardIdent d)

end Pins

/-! ## 4. Target 11: Step 5 in cases (i), (ii), (iv) at the BA tuple -/

section Cases

/-- **Target 11, case (i)** (`T2501_Step5IBA`): `ST_step5_caseI_of_pinsgL` with `baStep5CasesGen_flowFacts d` and target 10. -/
theorem baStep5I_holds : ∀ d : ℕ, 3 ≤ d → STStep5IgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  ST_step5_caseI_of_pinsgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baSTEtermsMidgL_holds d hd) (baSTDuhamelIgL_holds d hd)
    (baSTIniTermIgL_holds d hd)

/-- **Target 11, case (ii)** (`T2501_Step5IIBA`): `ST_step5_caseII_of_pinsgL` with the four pins of target 10. -/
theorem baStep5II_holds : ∀ d : ℕ, 3 ≤ d → STStep5IIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  ST_step5_caseII_of_pinsgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baSTEtermsMidgL_holds d hd) (baSTDuhamelIIgL_holds d hd)
    (baSTIniTermIIgL_holds d hd) (baSTWardIIgL_holds d hd)

/-- **Target 11, case (iv)** (`T2501_Step5IVBA`): `stStep5IVgL_holds` with `baStep5CasesGen_flowFacts d`, every `d`. -/
theorem baStep5IV_holds : ∀ d : ℕ, STStep5IVgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d =>
  stStep5IVgL_holds d _ _ _ _ (baStep5CasesGen_flowFacts d)

end Cases

/-! ## 5. Compiled nonempty instances at `d = 3` (target 12)

At `(sz0, zSeq, flow_sz0)` the regime premise of cases (i), (ii), (iv) is `False` (`T₀_n ≤ 25/36`, so `1 - s_n > 11/36`, while the regimes
need `1 - s_n ≤ lam_n²/L_n²`, `≤ lam_n²/L_n³` with `lam_n ≤ 1/64`), so the cases are applied at private data (T2501 Amend 1; pattern
`CltFlowBA_szI/_flowI`, `BA/CltFlowBA.lean:597-690`, commit `db1932eb`; `TwistStep2_szII`, `BA/TwistStep2.lean:1341`): constant `L`,
constant `lam`, `W_n = n + W₀`, `w = (5003/5000) i`, `z_n ≡ w - m_w` with `m_w = BAmSubord 3 L lam w`, `(κ, ε, 𝔠, 𝔡) = (κ, 1/2, 1/9, 1/10)`,
constant times `0 = s < t ≤ κ/(κ+1) ≤ T₀`.  The nine carrier predicates of `STIngR5gL` (other gates' pins) stay hypotheses; the flow, the regime,
`(con_st_ind)` at every `𝔠_d > 0`, `s < t ≤ T₀` are discharged. -/

section Inst

/-- The size datum: `d = 3`, `L_n ≡ L`, `W_n = n + W₀`, `lam_n ≡ lam`. -/
private def Step5CasesBA_sz (L W₀ : ℕ) (lam : ℝ) (hL : 3 ≤ L) (hW : 0 < W₀) : Sizes 3 where
  L := fun _ => L
  W := fun n => n + W₀
  lam := fun _ => lam
  three_le_L := fun _ => hL
  W_pos := fun n => by omega

private def Step5CasesBA_w : ℂ := ⟨0, 5003 / 5000⟩

/-- The spectral sequence `z_n ≡ w - m_w`, `m_w = BAmSubord 3 L lam w` (`BASelf_subord`). -/
private def Step5CasesBA_z (L : ℕ) [NeZero L] (lam : ℝ) : ℕ → ℂ := fun _ => Step5CasesBA_w - BAmSubord 3 L lam Step5CasesBA_w

private theorem Step5CasesBA_w_norm : ‖Step5CasesBA_w‖ = 5003 / 5000 := by
  have e : Step5CasesBA_w = ((5003 / 5000 : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp [Step5CasesBA_w]
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

/-- `BAFlow` at the datum: `Im m ≥ Im w/(‖w‖² + lam² L³) ≥ κ`, `Im m ≤ 1/Im w`, `N_n ≥ 10^6`; the numerical hypotheses are discharged by
`norm_num` at each datum. -/
private theorem Step5CasesBA_flow (L W₀ : ℕ) [NeZero L] (hL : 3 ≤ L) (hLW : L ≤ W₀) (h100 : 100 ≤ W₀ * L) (lam κ : ℝ)
    (hl1 : 1 ≤ lam) (hl10 : lam ≤ 10) (hκ3 : 3 / 5000 ≤ κ)
    (hκ : κ * ((5003 / 5000 : ℝ) ^ 2 + lam ^ 2 * ((L ^ 3 : ℕ) : ℝ)) ≤ 5003 / 5000) :
    BAFlow (Step5CasesBA_sz L W₀ lam hL (by omega)) κ (1 / 2) (1 / 9) (1 / 10) (Step5CasesBA_z L lam) := by
  have hwi : Step5CasesBA_w.im = 5003 / 5000 := rfl
  have hsub := BASelf_subord 3 L lam (w := Step5CasesBA_w) (by rw [hwi]; norm_num)
  have hlo : κ ≤ (BAmSubord 3 L lam Step5CasesBA_w).im := by
    have hh := hsub.2.1
    rw [Step5CasesBA_w_norm, hwi] at hh
    refine le_trans ?_ hh
    rw [le_div_iff₀ (by positivity)]
    exact hκ
  have hhi : (BAmSubord 3 L lam Step5CasesBA_w).im ≤ 5000 / 5003 := by
    have hh := hsub.2.2.1
    rw [hwi] at hh
    exact hh.trans (by norm_num)
  have hAm : BAm 3 L lam (Step5CasesBA_w - BAmSubord 3 L lam Step5CasesBA_w) = BAmSubord 3 L lam Step5CasesBA_w :=
    BASelf_unique 3 L lam _ _ _ hsub.2.2.2.le (BAm_self 3 L lam _ hsub.2.2.2) hsub.1
  have hsize : ∀ n, (Step5CasesBA_sz L W₀ lam hL (by omega)).size n = ((n + W₀) * L) ^ 3 := fun n => rfl
  refine ⟨⟨by norm_num, by norm_num, ?_, ?_, ?_⟩, fun n => ?_⟩
  · refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    rw [hsize]
    have hn : n ≤ ((n + W₀) * L) ^ 3 := le_trans (by nlinarith) (Nat.le_self_pow (by norm_num) _)
    exact_mod_cast hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : (0 : ℝ) ≤ (L : ℝ) * ((n : ℝ) + W₀) := by positivity
    have e1 : ((((Step5CasesBA_sz L W₀ lam hL (by omega)).size n : ℕ)) : ℝ) = ((L : ℝ) * ((n : ℝ) + W₀)) ^ (3 : ℝ) := by
      rw [hsize, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      push_cast
      ring
    have e2 : ((((Step5CasesBA_sz L W₀ lam hL (by omega)).size n : ℕ)) : ℝ) ^ (1 / 9 : ℝ) =
        ((L : ℝ) * ((n : ℝ) + W₀)) ^ ((3 : ℝ)⁻¹) := by
      rw [e1, ← Real.rpow_mul hx]
      norm_num
    rw [e2, Real.rpow_inv_le_iff_of_pos hx (by positivity) (by norm_num),
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    change (L : ℝ) * ((n : ℝ) + W₀) ≤ (((n + W₀ : ℕ) : ℝ)) ^ 3
    have hLW' : (L : ℝ) ≤ W₀ := by exact_mod_cast hLW
    have hW1 : (1 : ℝ) ≤ W₀ := by
      have : 1 ≤ W₀ := by omega
      exact_mod_cast this
    push_cast
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n + W₀) (by nlinarith : (0 : ℝ) ≤ ((n : ℝ) + W₀) ^ 2 - L)]
  · filter_upwards [eventually_ge_atTop 0] with n hn
    have hW : (1 : ℝ) ≤ (((n + W₀ : ℕ)) : ℝ) := by
      have : 1 ≤ n + W₀ := by omega
      exact_mod_cast this
    change (((n + W₀ : ℕ)) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) ≤ lam ∧ lam ≤ (1 / 10 : ℝ)⁻¹
    exact ⟨(Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)).trans hl1, by norm_num; exact hl10⟩
  · refine ⟨?_, ?_, ?_⟩
    · change κ ≤ (BAm 3 L lam (Step5CasesBA_w - BAmSubord 3 L lam Step5CasesBA_w)).im
      rw [hAm]
      exact hlo
    · have h1e6 : (1000000 : ℝ) ≤ ((((Step5CasesBA_sz L W₀ lam hL (by omega)).size n : ℕ)) : ℝ) := by
        rw [hsize]
        have : 1000000 ≤ ((n + W₀) * L) ^ 3 := by
          calc 1000000 = 100 ^ 3 := by norm_num
            _ ≤ ((n + W₀) * L) ^ 3 :=
              Nat.pow_le_pow_left (h100.trans (by rw [add_mul]; exact Nat.le_add_left _ _)) 3
        exact_mod_cast this
      have h1 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1000000) h1e6 (by norm_num : (-1 + 1 / 2 : ℝ) ≤ 0)
      have h2 : (1000000 : ℝ) ^ (-1 + 1 / 2 : ℝ) = 1 / 1000 := by
        rw [show (1000000 : ℝ) = 1000 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
        norm_num
      refine le_trans h1 ?_
      rw [h2]
      change 1 / 1000 ≤ (Step5CasesBA_w - BAmSubord 3 L lam Step5CasesBA_w).im
      rw [Complex.sub_im, hwi]
      linarith [hhi]
    · change (Step5CasesBA_w - BAmSubord 3 L lam Step5CasesBA_w).im ≤ 1
      rw [Complex.sub_im, hwi]
      linarith [hlo]

/-- `(con_st_ind)` at constant times `s₀ < t₀ < 1` for every `𝔠_d > 0`, eventually: `Bctl_n(t₀) = (W_n³)⁻¹ B_p` with `B_p` constant and
`W_n = n + W₀ → ∞`, so `Bctl^{𝔠_d} → 0 < (1 - t₀)/(1 - s₀)` (the argument of `s1Setup_conStInd_const`, `Induction/Step1Setup.lean:1226`). -/
private theorem Step5CasesBA_conStInd (L W₀ : ℕ) (lam : ℝ) (hL : 3 ≤ L) (hW : 0 < W₀) {s0 t0 𝔠d : ℝ} (hst : s0 < t0) (ht : t0 < 1)
    (h𝔠 : 0 < 𝔠d) : STConStInd (Step5CasesBA_sz L W₀ lam hL hW) 𝔠d (fun _ => s0) (fun _ => t0) := by
  have hB : Tendsto (fun n : ℕ => (Step5CasesBA_sz L W₀ lam hL hW).Bctl n t0) atTop (nhds 0) := by
    have hW' : Tendsto (fun n : ℕ => n + W₀) atTop atTop := tendsto_atTop_mono (fun n => Nat.le_add_right n W₀) tendsto_id
    have h1 : Tendsto (fun n : ℕ => (((n + W₀ : ℕ) : ℝ) ^ 3)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp
        (tendsto_natCast_atTop_atTop.comp hW'))
    have h2 := h1.mul_const (Bparam 3 L lam t0 0)
    rw [zero_mul] at h2
    exact h2
  have h0 : Tendsto (fun n => (Step5CasesBA_sz L W₀ lam hL hW).Bctl n t0 ^ 𝔠d) atTop (nhds ((0 : ℝ) ^ 𝔠d)) :=
    hB.rpow_const (Or.inr h𝔠.le)
  rw [Real.zero_rpow h𝔠.ne'] at h0
  have hpos : 0 < (1 - t0) / (1 - s0) := div_pos (by linarith) (by linarith)
  filter_upwards [h0.eventually (gt_mem_nhds hpos)] with n hn
  exact ⟨hn.le, (div_lt_one (by linarith)).2 (by linarith)⟩

/-- The data of an application of a Step-5 pin at a private datum: `κ > 0`, the flow, `0 ≤ s`, `s < t ≤ T₀`, `(con_st_ind)` at every `𝔠_d`. -/
private def Step5CasesBA_Datum (sz : Sizes 3) (z : ℕ → ℂ) (κ : ℝ) (s t : ℕ → ℝ) : Prop :=
  0 < κ ∧ BAFlow sz κ (1 / 2) (1 / 9) (1 / 10) z ∧ (∀ n, 0 ≤ s n) ∧ (∀ n, s n < t n) ∧ (∀ n, t n ≤ BAflowT0 sz z n) ∧
    ∀ 𝔠d : ℝ, 0 < 𝔠d → STConStInd sz 𝔠d s t

private theorem Step5CasesBA_datum (L W₀ : ℕ) [NeZero L] (hL : 3 ≤ L) (hLW : L ≤ W₀) (h100 : 100 ≤ W₀ * L) (lam κ : ℝ)
    (hl1 : 1 ≤ lam) (hl10 : lam ≤ 10) (hκ3 : 3 / 5000 ≤ κ)
    (hκ : κ * ((5003 / 5000 : ℝ) ^ 2 + lam ^ 2 * ((L ^ 3 : ℕ) : ℝ)) ≤ 5003 / 5000) {t0 : ℝ} (h0 : 0 < t0)
    (ht : t0 ≤ κ / (κ + 1)) :
    Step5CasesBA_Datum (Step5CasesBA_sz L W₀ lam hL (by omega)) (Step5CasesBA_z L lam) κ (fun _ => 0) (fun _ => t0) := by
  have hκ0 : 0 < κ := lt_of_lt_of_le (by norm_num) hκ3
  have hflow := Step5CasesBA_flow L W₀ hL hLW h100 lam κ hl1 hl10 hκ3 hκ
  have ht1 : t0 < 1 := lt_of_le_of_lt ht ((div_lt_one (by linarith)).2 (by linarith))
  exact ⟨hκ0, hflow, fun _ => le_rfl, fun _ => h0, fun n => ht.trans (TwistStep2_T0_ge hκ0 hflow n),
    fun 𝔠d h𝔠 => Step5CasesBA_conStInd L W₀ lam hL (by omega) h0 ht1 h𝔠⟩

/-- The nine carrier predicates of `STIngR5gL` at the BA tuple (other gates' pins; `Cd = 1`). -/
private def Step5CasesBA_prem (sz : Sizes 3) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∧ STKwardgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∧
    STLKgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧ STDecaygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧
    STDecayStronggL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s ∧ STStep1LoopgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
    STStep2ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t 1 ∧ STLmaxUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t ∧
    STLKUgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t

/-- A Step-5 pin over the BA tuple applied at a private datum, `Cd = 1`, `𝔠 = 1/9`. -/
private theorem Step5CasesBA_apply (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (Concl : ∀ (sz : Sizes 3) (z : ℕ → ℂ), (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (hpin : STIngR5gL 3 R (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 Concl)
    {sz : Sizes 3} {z : ℕ → ℂ} {κ : ℝ} {s t : ℕ → ℝ} (hD : Step5CasesBA_Datum sz z κ s t) (hR : R sz s t)
    (hp : Step5CasesBA_prem sz z s t) : Concl sz z s t := by
  obtain ⟨hκ, hflow, hs0, hst, ht, hcon⟩ := hD
  obtain ⟨hKb, hKw, hLK, hDec, hDecS, hS1, hS2, hLmax, hLKU⟩ := hp
  obtain ⟨𝔠d, h0, -, H⟩ := hpin le_rfl κ (1 / 2) (1 / 10) hκ (by norm_num) (by norm_num) 1 one_pos
  exact H (1 / 9) sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS (hcon 𝔠d h0) hS1 hS2 hLmax hLKU

/-! ### The three data: `(L, W₀, lam, κ, t)` = (4, 25, 1, 1/70, 1/100) for case (i), (4, 25, 4, 1/1100, 9/10000) for case (ii), (3, 40, 6, 1/1000, 1/2000) for case (iv);
`s ≡ 0`. -/

private def Step5CasesBA_szI : Sizes 3 := Step5CasesBA_sz 4 25 1 (by norm_num) (by norm_num)
private def Step5CasesBA_zI : ℕ → ℂ := Step5CasesBA_z 4 1
private def Step5CasesBA_szII : Sizes 3 := Step5CasesBA_sz 4 25 4 (by norm_num) (by norm_num)
private def Step5CasesBA_zII : ℕ → ℂ := Step5CasesBA_z 4 4
private def Step5CasesBA_szIV : Sizes 3 := Step5CasesBA_sz 3 40 6 (by norm_num) (by norm_num)
private def Step5CasesBA_zIV : ℕ → ℂ := Step5CasesBA_z 3 6

private theorem Step5CasesBA_datI :
    Step5CasesBA_Datum Step5CasesBA_szI Step5CasesBA_zI (1 / 70) (fun _ => 0) (fun _ => 1 / 100) :=
  Step5CasesBA_datum 4 25 (by norm_num) (by norm_num) (by norm_num) 1 (1 / 70) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem Step5CasesBA_datII :
    Step5CasesBA_Datum Step5CasesBA_szII Step5CasesBA_zII (1 / 1100) (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_datum 4 25 (by norm_num) (by norm_num) (by norm_num) 4 (1 / 1100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem Step5CasesBA_datIV :
    Step5CasesBA_Datum Step5CasesBA_szIV Step5CasesBA_zIV (1 / 1000) (fun _ => 0) (fun _ => 1 / 2000) :=
  Step5CasesBA_datum 3 40 (by norm_num) (by norm_num) (by norm_num) 6 (1 / 1000) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private theorem Step5CasesBA_regI : STReg5I Step5CasesBA_szI (fun _ => 0) (fun _ => 1 / 100) := fun n => by
  constructor <;> norm_num [Step5CasesBA_szI, Step5CasesBA_sz]

private theorem Step5CasesBA_regMidI : STReg5Mid Step5CasesBA_szI (fun _ => 0) (fun _ => 1 / 100) := fun n => by
  constructor <;> norm_num [Step5CasesBA_szI, Step5CasesBA_sz]

private theorem Step5CasesBA_regII : STReg5II Step5CasesBA_szII (fun _ => 0) (fun _ => 9 / 10000) := fun n => by
  constructor <;> norm_num [Step5CasesBA_szII, Step5CasesBA_sz]

private theorem Step5CasesBA_regMidII : STReg5Mid Step5CasesBA_szII (fun _ => 0) (fun _ => 9 / 10000) := fun n => by
  constructor <;> norm_num [Step5CasesBA_szII, Step5CasesBA_sz]

private theorem Step5CasesBA_regIV : STReg5IV Step5CasesBA_szIV (fun _ => 0) (fun _ => 1 / 2000) := fun n => by
  norm_num [Step5CasesBA_szIV, Step5CasesBA_sz]

/-! ### Target 12, target 9 at `(sz0, zSeq, flow_sz0)` (no regime needed), `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)` -/

section WardInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- The identity as a class at `(sz0, zSeq)`: every `n`, `u ∈ [0, 1)`, sample, mixed charges, `a`. -/
example : Step5CasesGen_WardIdent (baFMz sz0 zSeq) :=
  baStep5CasesGen_wardIdent 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0

/-- The identity at `n = 0` (`L = 4`, `W = 32`), `u = 1/2`, `σ = (true, false)`, `a = 0`, every sample `ω`. -/
example (ω : sz0.SeqΩ) :
    ((baFMz sz0 zSeq).L 0 (1 / 2) ![true, false] (fun _ => 0) ω - (baFMz sz0 zSeq).K 0 (1 / 2) ![true, false] (fun _ => 0)) -
        zeroModeSet 3 (sz0.L 0) {0} (fun a' => (baFMz sz0 zSeq).L 0 (1 / 2) ![true, false] a' ω -
          (baFMz sz0 zSeq).K 0 (1 / 2) ![true, false] a') (fun _ => 0) =
      ((((baFMz sz0 zSeq).L 0 (1 / 2) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (sz0.L 0))) ω -
          (baFMz sz0 zSeq).K 0 (1 / 2) (fun _ : Fin 1 => true) (fun _ => (0 : Zd 3 (sz0.L 0)))).im : ℝ) : ℂ) /
        (((sz0.size 0 : ℕ) : ℂ) * (((baFMz sz0 zSeq).eta 0 (1 / 2) : ℝ) : ℂ)) :=
  baStep5CasesGen_wardIdent 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0 (1 / 2) (by norm_num) (by norm_num) ω
    ![true, false] (by simp) (fun _ => 0)

end WardInst

/-! ### Target 12, case (iv): `baStep5IV_holds` at datum (iv) -/

example (hp : Step5CasesBA_prem Step5CasesBA_szIV Step5CasesBA_zIV (fun _ => 0) (fun _ => 1 / 2000)) :
    STStep5ConclgL (baFMz Step5CasesBA_szIV Step5CasesBA_zIV) (Sizes.seqP (Step5CasesBA_szIV.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) :=
  Step5CasesBA_apply STReg5IV (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) (baStep5IV_holds 3)
    Step5CasesBA_datIV Step5CasesBA_regIV hp

/-! ### Target 12, case (i) at datum (i): the three pins of target 10 and `baStep5I_holds` -/

example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
    STEtermsMidConclgL (baFMz Step5CasesBA_szI Step5CasesBA_zI) (Sizes.seqP (Step5CasesBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 100) :=
  Step5CasesBA_apply STReg5Mid (fun sz z s t => STEtermsMidConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (baSTEtermsMidgL_holds 3 le_rfl) Step5CasesBA_datI Step5CasesBA_regMidI hp

example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
    STEtermsMidConclgL (baFMz Step5CasesBA_szI Step5CasesBA_zI) (Sizes.seqP (Step5CasesBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 100) →
      STDuhamelConclgL (baFMz Step5CasesBA_szI Step5CasesBA_zI) (Sizes.seqP (Step5CasesBA_szI.withLam 0)) ∅ STSigAll (fun _ => 0) (fun _ => 1 / 100) :=
  Step5CasesBA_apply STReg5I (fun sz z s t => STEtermsMidConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STDuhamelConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∅ STSigAll s t)
    (baSTDuhamelIgL_holds 3 le_rfl) Step5CasesBA_datI Step5CasesBA_regI hp

example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
    STIniTermConclgL (baFMz Step5CasesBA_szI Step5CasesBA_zI) (Sizes.seqP (Step5CasesBA_szI.withLam 0)) ∅ STSigAll (fun _ => 0) (fun _ => 1 / 100) :=
  Step5CasesBA_apply STReg5I (fun sz z s t => STIniTermConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∅ STSigAll s t)
    (baSTIniTermIgL_holds 3 le_rfl) Step5CasesBA_datI Step5CasesBA_regI hp

example (hp : Step5CasesBA_prem Step5CasesBA_szI Step5CasesBA_zI (fun _ => 0) (fun _ => 1 / 100)) :
    STStep5ConclgL (baFMz Step5CasesBA_szI Step5CasesBA_zI) (Sizes.seqP (Step5CasesBA_szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 100) :=
  Step5CasesBA_apply STReg5I (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) (baStep5I_holds 3 le_rfl)
    Step5CasesBA_datI Step5CasesBA_regI hp

/-! ### Target 12, case (ii) at datum (ii): the four pins of target 10 and `baStep5II_holds` -/

example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
    STEtermsMidConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_apply STReg5Mid (fun sz z s t => STEtermsMidConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (baSTEtermsMidgL_holds 3 le_rfl) Step5CasesBA_datII Step5CasesBA_regMidII hp

example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
    STEtermsMidConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) (fun _ => 0) (fun _ => 9 / 10000) →
      STDuhamelConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) {0} STSigMixed (fun _ => 0) (fun _ => 9 / 10000) ∧
        STDuhamelConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) ∅ STSigSame (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_apply STReg5II (fun sz z s t => STEtermsMidConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t →
      STDuhamelConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) {0} STSigMixed s t ∧
        STDuhamelConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∅ STSigSame s t)
    (baSTDuhamelIIgL_holds 3 le_rfl) Step5CasesBA_datII Step5CasesBA_regII hp

example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
    STIniTermConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) {0} STSigMixed (fun _ => 0) (fun _ => 9 / 10000) ∧
      STIniTermConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) ∅ STSigSame (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_apply STReg5II (fun sz z s t => STIniTermConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) {0} STSigMixed s t ∧
      STIniTermConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) ∅ STSigSame s t)
    (baSTIniTermIIgL_holds 3 le_rfl) Step5CasesBA_datII Step5CasesBA_regII hp

example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
    STWardIIConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_apply STReg5II (fun sz z s t => STWardIIConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t)
    (baSTWardIIgL_holds 3 le_rfl) Step5CasesBA_datII Step5CasesBA_regII hp

example (hp : Step5CasesBA_prem Step5CasesBA_szII Step5CasesBA_zII (fun _ => 0) (fun _ => 9 / 10000)) :
    STStep5ConclgL (baFMz Step5CasesBA_szII Step5CasesBA_zII) (Sizes.seqP (Step5CasesBA_szII.withLam 0)) (fun _ => 0) (fun _ => 9 / 10000) :=
  Step5CasesBA_apply STReg5II (fun sz z s t => STStep5ConclgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t) (baStep5II_holds 3 le_rfl)
    Step5CasesBA_datII Step5CasesBA_regII hp

end Inst

end RBM.BA

end
