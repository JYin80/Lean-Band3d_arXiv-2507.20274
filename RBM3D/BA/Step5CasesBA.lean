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
# The Ward bridge, the six ingredient statements and Step 5 in cases (i), (ii), (iv) at BA

Paper: Steps 3-6 "extend verbatim" to BA (Section 8, Theorem 8.2 `lem:main_ind_BA`); the case analysis of Step 5, Lemma 5.4 (`lem:pf_step5`) in Section 5 (`Sec:Step5`); the Ward term `(zYU1)` (5.37).
Band analogues (not edited): `stWardII_identity` (`Induction/WardII`), `stEtermsMid_of_LWT`, `stDuhamelI_holds`, `stDuhamelII_holds`,
`stIniTermI_holds`, `stIniTermII_holds`, `stWardII_holds`.

BA tuple `(fun sz => Sizes.seqP (sz.withLam 0), BAFlow, baFMz, BAflowT0)`; Step2Mat family
`mkM sz z = baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)`; `gK = BAflowLam0`, `E = BAflowEs`.

* `step5CasesGen_wardIdent_of_wardCls` (the generic bridge from the Ward class, the one-index conjugation inline) and
  `baStep5CasesGen_wardIdent`: `baZeroModeGen_wardCls` with the conjugation of the one-index `𝓛`
  (conjunct 2 of `baStep2_oneLoop`, every `n`, `u`, `ω`) and `𝒦` (clause 3 of `IsKLoopS` through `baKcac_isKLoopS`, `BAReal` only).
* `baSTEtermsMidgL_holds`, `baSTDuhamelIgL_holds`, `baSTDuhamelIIgL_holds`, `baSTIniTermIgL_holds`, `baSTIniTermIIgL_holds`,
  `baSTWardIIgL_holds`: one call each of the generic result with the family table's discharges (`Hf = baEMn2Hf`, `ζf = baEMn2Zf`).
* `baStep5I_holds`, `baStep5II_holds`, `baStep5IV_holds`.

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

/-! ## 1. The Ward identity from the Ward class and the one-index conjugation -/

section Ward

/-- `T a - Q^{(1)} T a = L^{-d} Σ_c T(c, a₂)` (copy of the private `wardII_zeroMode`, `Induction/WardII`). -/
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

/-- The bridge from the Ward class (the pattern of `stWardII_identity`, `Induction/WardII`): a carrier
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

/-- `baStep5CasesGen_wardIdent`: the `(zYU1)` identity along every BA flow, from the Ward class
`baZeroModeGen_wardCls` and the one-index conjugation.  `𝓛`: conjunct 2 of `baStep2_oneLoop` (every `n`, `u`, `ω`); `𝒦`: clause 3 of
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

/-! ## 2. The inline premises and the family premises shared by the statements -/

section Family

variable {d : ℕ}

/-- `hmn`: `‖m_n‖ ≤ 1` at the carrier `baStep2Mat sz g₀ E` along a BA flow (the same premise as in `BA/Step5KerBA`; `BAm_norm_le_one`, `BA/Ward`, at the `BASelf` datum of `BAflow_real`). -/
private theorem Step5CasesBA_hmn {κ ε 𝔠 𝔡 : ℝ} {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    ‖(baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)).m n‖ ≤ 1 :=
  BAm_norm_le_one d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) _ (by simp)
    (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1

/-- `hSr`: `S = 1`, so the row sums of `‖S‖` are `1` (the same premise as in `BA/Step5KerBA`). -/
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

/-! ## 3. The six ingredient statements at the BA tuple -/

section Pins

/-- `baSTEtermsMidgL_holds` (`(S5WG+M000)` (5.4), `(S5WG+M)` (5.5)): `stEtermsMidgL_of` with `Hf = baEMn2Hf`, `ζf = baEMn2Zf` and the family
table (`hLW` through `stLWTgL_of_LWtermExpG`, `Step2EventsGenTw_baRot3`, `baLWtermExp_holds`; `hNew` is `baEtermsMid_newKLKL`, `hFM` is `baStep2Mat_loopForm`). -/
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

/-- `baSTDuhamelIgL_holds`, the integrated hierarchy of case (i): `stDuhamelIgL_of` at `gK = BAflowLam0`, `E = BAflowEs`
(the kernel facts `baIniTermGen_kerFacts`, `hGR`, the grid martingale estimate `baGridMart_holds`, the bound `baStep2_K2`). -/
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

/-- `baSTDuhamelIIgL_holds`, the integrated hierarchy of case (ii): `stDuhamelIIgL_of`, the premises of `baSTDuhamelIgL_holds` and `baKLip_two`. -/
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

/-- `baSTIniTermIgL_holds`, the initial term of case (i): `stIniTermIgL_of` with the Ward class `baZeroModeGen_wardCls` and the
class `baIniTermGen_cltFlow`; every law `seqP (sz.withLam 0)` is a probability measure. -/
theorem baSTIniTermIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stIniTermIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 BAflowLam0
    (fun sz => inferInstance) (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)
    (fun sz κ ε 𝔠 𝔡 z hκ hflow => baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow) (baIniTermGen_cltFlow d)

/-- `baSTIniTermIIgL_holds`, the initial terms of case (ii): `stIniTermIIgL_of` with `baIniTermGen_kerFacts`. -/
theorem baSTIniTermIIgL_holds : ∀ d : ℕ, 3 ≤ d → STIniTermIIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stIniTermIIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 BAflowLam0
    (baStep5CasesGen_flowFacts d) (baIniTermGen_kerFacts d)

/-- `baSTWardIIgL_holds`, the Ward term `(zYU1)`: `stWardIIgL_of` with `baStep5CasesGen_wardIdent`. -/
theorem baSTWardIIgL_holds : ∀ d : ℕ, 3 ≤ d → STWardIIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  stWardIIgL_of d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0
    (baStep5CasesGen_flowFacts d) (baStep5CasesGen_wardIdent d)

end Pins

/-! ## 4. Step 5 in cases (i), (ii), (iv) at the BA tuple -/

section Cases

/-- `baStep5I_holds`, case (i): `ST_step5_caseI_of_pinsgL` with `baStep5CasesGen_flowFacts d`, `baSTEtermsMidgL_holds`, `baSTDuhamelIgL_holds`, `baSTIniTermIgL_holds`. -/
theorem baStep5I_holds : ∀ d : ℕ, 3 ≤ d → STStep5IgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  ST_step5_caseI_of_pinsgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baSTEtermsMidgL_holds d hd) (baSTDuhamelIgL_holds d hd)
    (baSTIniTermIgL_holds d hd)

/-- `baStep5II_holds`, case (ii): `ST_step5_caseII_of_pinsgL` with `baSTEtermsMidgL_holds`, `baSTDuhamelIIgL_holds`, `baSTIniTermIIgL_holds`, `baSTWardIIgL_holds`. -/
theorem baStep5II_holds : ∀ d : ℕ, 3 ≤ d → STStep5IIgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d hd =>
  ST_step5_caseII_of_pinsgL d _ _ _ _ (baStep5CasesGen_flowFacts d) (baSTEtermsMidgL_holds d hd) (baSTDuhamelIIgL_holds d hd)
    (baSTIniTermIIgL_holds d hd) (baSTWardIIgL_holds d hd)

/-- `baStep5IV_holds`, case (iv): `stStep5IVgL_holds` with `baStep5CasesGen_flowFacts d`, every `d`. -/
theorem baStep5IV_holds : ∀ d : ℕ, STStep5IVgL d (fun sz => Sizes.seqP (sz.withLam 0))
    (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) baFMz BAflowT0 := fun d =>
  stStep5IVgL_holds d _ _ _ _ (baStep5CasesGen_flowFacts d)

end Cases

end RBM.BA

end
