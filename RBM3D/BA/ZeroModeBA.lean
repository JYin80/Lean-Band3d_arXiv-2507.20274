/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step34Gen
import RBM3D.Chain.IterationsGen2
import RBM3D.Chain.QGridGen
import RBM3D.Chain.Step2Kern
import RBM3D.Chain.Step2EventsGenTw
import RBM3D.BA.SEforLnBA
import RBM3D.BA.B45BA
import RBM3D.BA.GridRepTailBA
import RBM3D.BA.TwistStep2
import RBM3D.BA.Step1Fam

/-!
# The BA side of U1: `lem: newPQ`, the zero-mode commutation, the kernel semigroup and `lem:iterations` (ticket T2500, U1-BA)

Composition of merged results; no merged file is edited.

* **Target 1** `stNewPQgL_wardCls`: `STNewPQgL` over the carrier Ward class `ZeroModeGen_WardCls`, from `zeroModeGen_newPQ` at the class
  witnesses `TL`, `TK`.
* **Target 2** `baSTNewPQgL`: the same over the class of BA carriers along a BA flow (`baZeroModeGen_wardCls`).
* **Target 3** `baZeroModeSet_UN` (with `BAUN`), `baZeroModeSet_ThetaN`: `Q^{(A)}` commutes with the kernels (`zeroModeSet_UNg`,
  `zeroModeSet_ThetaNg` at `baZeroModeGen_kerSums`; `Step2Kern_UN_BA`).
* **Target 4** `baStep2Gen_USemigroup`: first conjunct of `gridRepTailGen_ker_BA`.
* **Target 5** `baIterationsGen2_fam`: `IterationsGen2_Fam` at the BA tuple.
* **Target 6** `baSTIterationsgL'_holds`, `baSTIterationsIIgL'_holds`: `stIterationsgL'_of`, `stIterationsIIgL'_of` at target 5
  (`(baStep2Mat ..).toFlowFM` is `baFMz sz z` by unfolding).
* **Instances** at `d = 3` in `RBM.BA.ZeroModeBAInst`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ### 1. `lem: newPQ` over the carrier Ward class and at BA -/

/-- The coefficient of the Ward step: `L^{-d} (2 i W^d η)⁻¹ = (2 i N η)⁻¹`, `N = (W L)^d` (copy of the private `ZeroModeGen_coef`). -/
private theorem ZeroModeBA_coef {d : ℕ} (sz : Sizes d) (n : ℕ) (η : ℂ) :
    (((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * η)⁻¹ =
      (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * η)⁻¹ := by
  rw [← mul_inv]
  congr 1
  simp only [Sizes.size]
  push_cast
  ring

/-- **Target 1** (`T2500_NewPQWardCls`): `lem: newPQ` over the carrier Ward class, every `d`. -/
theorem stNewPQgL_wardCls (d : ℕ) : STNewPQgL d (fun sz C => ZeroModeGen_WardCls sz C) := by
  intro m σ A
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := zeroModeGen_newPQ d m σ A
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, ?_⟩
  intro sz C hC n τ hτ0 hτ1 ω a
  obtain ⟨TL, TK, hL, hK, hwL, hwK⟩ := hC n τ hτ0 hτ1 ω
  have hcoef : ∀ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (C.eta n τ : ℂ)) ^ (m - k α))
      = (ξ α : ℂ) * ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹ * (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (C.eta n τ : ℂ))⁻¹) ^ (m - k α) := by
    intro α
    rw [ZeroModeBA_coef, div_eq_mul_inv, inv_pow]
  simp only [hcoef, hL, hK]
  exact ⟨h (sz.L n) _ TL hwL a, h (sz.L n) _ TK hwK a⟩

/-- **Target 2** (`T2500_NewPQBA`): `lem: newPQ` at the class of BA carriers along a BA flow. -/
theorem baSTNewPQgL (d : ℕ) :
    STNewPQgL d (fun sz C => ∃ (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ C = baFMz sz z) := by
  intro m σ A
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := stNewPQgL_wardCls d m σ A
  refine ⟨ℓ, k, ξ, σ', ι, A', hk, hA, ?_⟩
  rintro sz C ⟨κ, ε, 𝔠, 𝔡, z, hκ, hflow, rfl⟩
  exact h sz _ (baZeroModeGen_wardCls d sz κ ε 𝔠 𝔡 z hκ hflow)

/-! ### 2. The zero-mode commutation at BA -/

private theorem ZeroModeBA_hIm {d : ℕ} (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ) (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : (((BAflowEs sz z n : ℝ) : ℂ) + BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im ≠ 0 := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  simpa using (lt_of_lt_of_le hκ hr.2).ne'

/-- **Target 3, `UN`** (`T2500_ZeroModeSetUNBA`): `Q^{(A)}` commutes with stage E's `BAUN` along a BA flow. -/
theorem baZeroModeSet_UN :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n k : ℕ) (σ : Fin k → Bool) (s t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
        zeroModeSet d (sz.L n) A
            (BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t T) =
          BAUN d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) σ s t
            (zeroModeSet d (sz.L n) A T) := by
  intro d sz κ ε 𝔠 𝔡 z hκ hflow n k σ s t A T
  have hIm := ZeroModeBA_hIm sz κ ε 𝔠 𝔡 z hκ hflow n
  have h := zeroModeSet_UNg (baFMz sz z) n (baZeroModeGen_kerSums d sz κ ε 𝔠 𝔡 z hκ hflow n) σ s t A T
  unfold baFMz at h
  rwa [Step2Kern_UN_BA sz _ _ n hIm k σ s t T, Step2Kern_UN_BA sz _ _ n hIm k σ s t (zeroModeSet d (sz.L n) A T)] at h

/-- **Target 3, `ThetaN`** (`T2500_ZeroModeSetThetaNBA`): `Q^{(A)}` commutes with the carrier `Step2Gen_ThetaN` of `baFMz`. -/
theorem baZeroModeSet_ThetaN :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ (n k : ℕ) (σ : Fin k → Bool) (t : ℝ) (A : Finset (Fin k)) (T : (Fin k → Zd d (sz.L n)) → ℂ),
        zeroModeSet d (sz.L n) A (Step2Gen_ThetaN (baFMz sz z) n σ t T) =
          Step2Gen_ThetaN (baFMz sz z) n σ t (zeroModeSet d (sz.L n) A T) :=
  fun d sz κ ε 𝔠 𝔡 z hκ hflow n _k σ t A T =>
    zeroModeSet_ThetaNg (baFMz sz z) n (baZeroModeGen_kerSums d sz κ ε 𝔠 𝔡 z hκ hflow n) σ t A T

/-! ### 3. The kernel semigroup at BA -/

/-- **Target 4** (`T2500_USemigroupBA`): the semigroup class of the BA carrier at every index along a BA flow. -/
theorem baStep2Gen_USemigroup :
    ∀ (d : ℕ) (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ n : ℕ, Step2Gen_USemigroup (baFMz sz z) n :=
  fun _ sz κ ε 𝔠 𝔡 z hκ hflow n =>
    (gridRepTailGen_ker_BA sz (BAflowLam0 sz z) (BAflowEs sz z) n hκ (BAflow_real κ ε 𝔠 𝔡 sz z hflow n)).1

/-! ### 4. `lem:iterations` at BA -/

/-- **Target 5** (`T2500_IterFamBA`): the family bundle `IterationsGen2_Fam` at the BA tuple. -/
theorem baIterationsGen2_fam (d : ℕ) :
    IterationsGen2_Fam d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z)) (fun sz z => sz.seqHflowBA (BAflowLam0 sz z))
      (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z) := by
  refine ⟨Step2EventsGenTw_baFlow d, fun sz => Sizes.isProbabilityMeasure_seqP (sz.withLam 0), ?_, ?_⟩
  · intro sz κ ε 𝔠 𝔡 z hκ hflow
    refine ⟨baStep2Mat_loopForm d sz κ ε 𝔠 𝔡 z hκ hflow, fun n => ?_⟩
    have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
    exact BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hr.1
  · exact fun sz z => ⟨baStep34_LCompat d sz _ _, EMn2BA_seqHflowBA_herm sz _⟩

/-- **Target 6, case (i)** (`T2500_IterationsBA`): the R2* pin `STIterationsgL'` at the BA tuple. -/
theorem baSTIterationsgL'_holds (d : ℕ) :
    STIterationsgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

/-- **Target 6, case (ii)** (`T2500_IterationsIIBA`): `STIterationsIIgL'` at the BA tuple. -/
theorem baSTIterationsIIgL'_holds (d : ℕ) :
    STIterationsIIgL' d (fun sz => Sizes.seqP (sz.withLam 0)) (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => baFMz sz z) (fun sz z => BAflowT0 sz z) :=
  stIterationsIIgL'_of d _ _ (fun sz z => baStep2Mat sz (BAflowLam0 sz z) (BAflowEs sz z))
    (fun sz z => sz.seqHflowBA (BAflowLam0 sz z)) (fun sz z => BAflowEs sz z) (fun sz z => BAflowT0 sz z)
    (baIterationsGen2_fam d)

end RBM.BA

/-! ### 5. Compiled nonempty instances at `d = 3` (targets 1-5)

`sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`), `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`,
`m = 3`, `σ = (+,-,+)` (`STIdiff σ = {0, 1}`), `n = 0`, `τ = 1/2`, windows `s ≡ 1/10 ≤ t ≡ 1/2 < 1`, `K = 4`. -/

namespace RBM.BA.ZeroModeBAInst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

/-- The charge vector `σ = (+,-,+)`: `STIdiff σ = {0, 1}` differs from `A = ∅`. -/
private def σ3 : Fin 3 → Bool := ![true, false, true]

private theorem σ3_idiff : (∅ : Finset (Fin 3)) ∪ STIdiff σ3 ≠ ∅ := by
  decide +kernel

/-- **Targets 1 and 2** at the data: the expansion data for `m = 3`, `σ = (+,-,+)`, `A = ∅` and the two expansions at `(sz0, baFMz sz0 zSeq)`,
`n = 0`, `τ = 1/2`, for every sample `ω` and `a`. -/
theorem inst_newPQ_ba (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)) : (∅ : Finset (Fin 3)) ∪ STIdiff σ3 ≠ ∅ ∧
    ∃ (ℓ : ℕ) (k : Fin ℓ → ℕ) (ξ : Fin ℓ → ℤ) (σ' : ∀ α, Fin (k α) → Bool) (ι : ∀ α, Fin (k α) → Fin 3)
      (A' : ∀ α, Finset (Fin (k α))), (∀ α, 1 ≤ k α ∧ k α + 1 ≤ 3) ∧ (∀ α, STIdiff (σ' α) ⊆ A' α) ∧
      (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => (baFMz sz0 zSeq).L 0 (1 / 2) σ3 a' ω) a =
          zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff σ3) (fun a' => (baFMz sz0 zSeq).L 0 (1 / 2) σ3 a' ω) a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) * ((baFMz sz0 zSeq).eta 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
              zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => (baFMz sz0 zSeq).L 0 (1 / 2) (σ' α) a' ω) (a ∘ ι α)) ∧
        (zeroModeSet 3 (sz0.L 0) ∅ (fun a' => (baFMz sz0 zSeq).K 0 (1 / 2) σ3 a') a =
          zeroModeSet 3 (sz0.L 0) (∅ ∪ STIdiff σ3) (fun a' => (baFMz sz0 zSeq).K 0 (1 / 2) σ3 a') a +
            ∑ α : Fin ℓ, ((ξ α : ℂ) / (2 * Complex.I * ((sz0.size 0 : ℕ) : ℂ) * ((baFMz sz0 zSeq).eta 0 (1 / 2) : ℂ)) ^ (3 - k α)) *
              zeroModeSet 3 (sz0.L 0) (A' α) (fun a' => (baFMz sz0 zSeq).K 0 (1 / 2) (σ' α) a') (a ∘ ι α)) := by
  refine ⟨σ3_idiff, ?_⟩
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := baSTNewPQgL 3 3 σ3 ∅
  exact ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h sz0 (baFMz sz0 zSeq) ⟨1 / 2, 1 / 10, 1 / 6, 1 / 10, zSeq, by norm_num, flow_sz0, rfl⟩
    0 (1 / 2) (by norm_num) (by norm_num) ω a⟩

/-- **Target 1** at the data: the carrier Ward class of `baFMz sz0 zSeq` (`baZeroModeGen_wardCls`) feeds `stNewPQgL_wardCls`. -/
example (ω : sz0.SeqΩ) (a : Fin 3 → Zd 3 (sz0.L 0)) : True := by
  obtain ⟨ℓ, k, ξ, σ', ι, A', hk, hA, h⟩ := stNewPQgL_wardCls 3 3 σ3 ∅
  have := h sz0 (baFMz sz0 zSeq) (baZeroModeGen_wardCls 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0)
    0 (1 / 2) (by norm_num) (by norm_num) ω a
  trivial

/-- **Target 3** at the data (`UN`, `A = {0}`, `s = 1/10`, `t = 1/2`, `T ≡ 1`). -/
example :
    zeroModeSet 3 (sz0.L 0) {0}
        (BAUN 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0)
          σ3 (1 / 10) (1 / 2) (fun _ => 1)) =
      BAUN 3 (sz0.L 0) (BAflowLam0 sz0 zSeq 0) (BAflowEs sz0 zSeq 0) (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0)
        σ3 (1 / 10) (1 / 2) (zeroModeSet 3 (sz0.L 0) {0} (fun _ => 1)) :=
  baZeroModeSet_UN 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0 3 σ3 (1 / 10) (1 / 2) {0} (fun _ => 1)

/-- **Target 3** at the data (`ThetaN`, `A = {0}`, `t = 1/2`, `T ≡ 1`). -/
example :
    zeroModeSet 3 (sz0.L 0) {0} (Step2Gen_ThetaN (baFMz sz0 zSeq) 0 σ3 (1 / 2) (fun _ => 1)) =
      Step2Gen_ThetaN (baFMz sz0 zSeq) 0 σ3 (1 / 2) (zeroModeSet 3 (sz0.L 0) {0} (fun _ => 1)) :=
  baZeroModeSet_ThetaN 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0 3 σ3 (1 / 2) {0} (fun _ => 1)

/-- **Target 4** at the data: the semigroup class of `baFMz sz0 zSeq` at every index. -/
theorem inst_usemigroup (n : ℕ) : Step2Gen_USemigroup (baFMz sz0 zSeq) n :=
  baStep2Gen_USemigroup 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 n

/-- The carrier premises of U1s1 target 3 and U1s2 target 7 at `baStep2Mat sz0 ..`, `n = 0`. -/
private theorem inst_carrier :
    Step2Gen_USemigroup (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).toFlowFM 0 ∧
      ZeroModeGen_KerSums (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)).toFlowFM 0 :=
  ⟨inst_usemigroup 0, baZeroModeGen_kerSums 3 sz0 (1 / 2) (1 / 10) (1 / 6) (1 / 10) zSeq (by norm_num) flow_sz0 0⟩

/-- **U1s1 target 3** (`zeroModeCalc_duhamel_inside_atg`) at `baStep2Mat sz0 ..`, `n = 0`, `s ≡ 1/10 ≤ t ≡ 1/2`, `K ≡ 4`, `τ ≡ 2`, `j = 3`. -/
example (ω : PathΩ sz0) : True := by
  have _ := zeroModeCalc_duhamel_inside_atg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (fun _ => 1 / 10)
    (fun _ => 1 / 2) (fun _ => 4) 0 inst_carrier.1 inst_carrier.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) σ3 ∅
    (fun _ => 2) 3 ω (by norm_num)
  trivial

/-- **U1s2 target 7** (`stoppedDuhamelQNg`) at `baStep2Mat sz0 ..`, `n = 0`, `m = 2`, `ϑ ≡ 1`, `j = 3 ≤ K = 4`. -/
example (ω : PathΩ sz0) : True := by
  have _ := stoppedDuhamelQNg (baStep2Mat sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq)) (fun _ => 1 / 10) (fun _ => 1 / 2)
    (fun _ => 4) 0 (m := 2) (fun _ _ => 1) ![true, false, true] (fun _ => 2) 3 ω inst_carrier.1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

end RBM.BA.ZeroModeBAInst

/-! ### 6. Compiled nonempty instances of target 6 (`d = 3`)

Case (ii) at the merged datum `TwistStep2_szII` (`L ≡ 4`, `W_n = n + 25`, `lam ≡ 5`; `TwistStep2_flowII`), `s ≡ 0 < t ≡ 1/2000`.  Case (i) at the
new private datum `szI` (`lam ≡ 2`, the `TwistStep2_szII` pattern, ported from `BA/TwistStep2.lean:1341-1435` with `g = 2`): `sz0` has no `STRegIterI`
window (`n = 0`: `1 - s₀ ≤ lam₀² = 1/4096` against `t₀ ≤ 25/36`, `t0_sz0_le`), and `TwistStep2_szII` has none either (`lam²/L² = 25/16 > 1 - t`).
`(κ, ε, 𝔠, 𝔡) = (3/1000, 1/2, 1/9, 1/10)`, `s ≡ 0 < t ≡ 1/400 ≤ T₀`, `STCaseI` (`1/4 ≤ 399/400`), `1 - s = 1 ≤ lam² = 4`.  The pin binders (`STKboundgL`,
`STLKgL`, `STStep1LoopgL`, `STStep2ConclgL`, `STXiBootgL'`) and the two induction hypotheses stay hypotheses (other gates' pins). -/

namespace RBM.BA.ZeroModeBAInst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.Step34Inst Filter

private def szI : Sizes 3 where
  L := fun _ => 4
  W := fun n => n + 25
  lam := fun _ => 2
  three_le_L := fun _ => by norm_num
  W_pos := fun n => by omega

private def wI : ℂ := ⟨0, 5003 / 5000⟩
private def mI : ℂ := BAmSubord 3 4 2 wI
private def zI : ℕ → ℂ := fun _ => wI - mI

/-- `BAFlow` at the datum `szI` (`L ≡ 4`, `lam ≡ 2`) with `(κ, ε, 𝔠, 𝔡) = (3/1000, 1/2, 1/9, 1/10)` (`Im m ≥ Im w/(‖w‖² + g² L^d)` rounded down, `BASelf_subord`) and `T₀ ≥ κ/(κ+1) ≥ 1/400`. -/
private theorem flowI : BAFlow szI (3 / 1000) (1 / 2) (1 / 9) (1 / 10) zI ∧ ∀ n, (1 / 400 : ℝ) ≤ BAflowT0 szI zI n := by
  have hwn : ‖wI‖ = 5003 / 5000 := by
    have e : wI = ((5003 / 5000 : ℝ) : ℂ) * Complex.I := by apply Complex.ext <;> simp [wI]
    rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hwi : wI.im = 5003 / 5000 := rfl
  have hsub := BASelf_subord 3 4 2 (w := wI) (by rw [hwi]; norm_num)
  have hlo : (3 / 1000 : ℝ) ≤ (BAmSubord 3 4 2 wI).im := by
    have hh := hsub.2.1
    rw [hwn, hwi] at hh
    refine le_trans ?_ hh
    rw [le_div_iff₀ (by positivity)]
    norm_num
  have hhi : (BAmSubord 3 4 2 wI).im ≤ 5000 / 5003 := by
    have hh := hsub.2.2.1
    rw [hwi] at hh
    exact hh.trans (by norm_num)
  have hAm : BAm 3 4 2 (wI - mI) = mI :=
    BASelf_unique 3 4 2 _ _ _ hsub.2.2.2.le (BAm_self 3 4 2 _ hsub.2.2.2) hsub.1
  have hsize : ∀ n, szI.size n = ((n + 25) * 4) ^ 3 := fun n => rfl
  have hflow : BAFlow szI (3 / 1000) (1 / 2) (1 / 9) (1 / 10) zI := by
    refine ⟨⟨by norm_num, by norm_num, ?_, ?_, ?_⟩, fun n => ?_⟩
    · refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      rw [hsize]
      have hn : n ≤ ((n + 25) * 4) ^ 3 := le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
      exact_mod_cast hn
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hx : (0 : ℝ) ≤ 4 * ((n : ℝ) + 25) := by positivity
      have e1 : (((szI.size n : ℕ)) : ℝ) = (4 * ((n : ℝ) + 25)) ^ (3 : ℝ) := by
        rw [hsize, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        push_cast
        ring
      have e2 : (((szI.size n : ℕ)) : ℝ) ^ (1 / 9 : ℝ) = (4 * ((n : ℝ) + 25)) ^ ((3 : ℝ)⁻¹) := by
        rw [e1, ← Real.rpow_mul hx]
        norm_num
      rw [e2, Real.rpow_inv_le_iff_of_pos hx (by positivity) (by norm_num),
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      show 4 * ((n : ℝ) + 25) ≤ (((n + 25 : ℕ) : ℝ)) ^ 3
      push_cast
      nlinarith [sq_nonneg ((n : ℝ) + 25), mul_nonneg (by linarith : (0 : ℝ) ≤ n + 25) (by linarith : (0 : ℝ) ≤ n + 24)]
    · filter_upwards [eventually_ge_atTop 0] with n hn
      have hW : (1 : ℝ) ≤ (((n + 25 : ℕ)) : ℝ) := by
        have : 1 ≤ n + 25 := by omega
        exact_mod_cast this
      show (((n + 25 : ℕ)) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) ≤ 2 ∧ (2 : ℝ) ≤ (1 / 10 : ℝ)⁻¹
      refine ⟨?_, by norm_num⟩
      calc (((n + 25 : ℕ)) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2 + 1 / 10 : ℝ) ≤ 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos hW (by norm_num)
        _ ≤ 2 := by norm_num
    · refine ⟨?_, ?_, ?_⟩
      · show (3 / 1000 : ℝ) ≤ (BAm 3 4 2 (wI - mI)).im
        rw [hAm]
        exact hlo
      · have h1e6 : (1000000 : ℝ) ≤ ((szI.size n : ℕ) : ℝ) := by
          rw [hsize]
          have : 1000000 ≤ ((n + 25) * 4) ^ 3 := by
            calc 1000000 = 100 ^ 3 := by norm_num
              _ ≤ ((n + 25) * 4) ^ 3 := Nat.pow_le_pow_left (by omega) 3
          exact_mod_cast this
        have h1 := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1000000) h1e6 (by norm_num : (-1 + 1 / 2 : ℝ) ≤ 0)
        have h2 : (1000000 : ℝ) ^ (-1 + 1 / 2 : ℝ) = 1 / 1000 := by
          rw [show (1000000 : ℝ) = 1000 ^ (2 : ℝ) by rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
        refine le_trans h1 ?_
        rw [h2]
        show 1 / 1000 ≤ (wI - mI).im
        rw [Complex.sub_im, hwi]
        show 1 / 1000 ≤ 5003 / 5000 - (BAmSubord 3 4 2 wI).im
        linarith [hhi]
      · show (wI - mI).im ≤ 1
        rw [Complex.sub_im, hwi]
        show 5003 / 5000 - (BAmSubord 3 4 2 wI).im ≤ 1
        linarith [hlo]
  refine ⟨hflow, fun n => ?_⟩
  have hdom := hflow.2 n
  have hm : (3 / 1000 : ℝ) ≤ (BAm 3 (szI.L n) (szI.lam n) (zI n)).im := hdom.1
  have hz1 : (zI n).im ≤ 1 := hdom.2.2
  have hz0 : 0 < (zI n).im := EMn2BA_zim_pos szI hflow n
  show (1 / 400 : ℝ) ≤ (BAm 3 (szI.L n) (szI.lam n) (zI n)).im /
    ((BAm 3 (szI.L n) (szI.lam n) (zI n)).im + (zI n).im)
  rw [le_div_iff₀ (by linarith)]
  linarith


private theorem szI_W_tendsto : Tendsto (fun n : ℕ => ((szI.W n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  show (n : ℝ) ≤ ((n + 25 : ℕ) : ℝ)
  push_cast
  linarith

private theorem szI_window (n : ℕ) : (1 / 400 : ℝ) ≤ BAflowT0 szI zI n :=
  (flowI.2 n)

private theorem szI_regIterI : STRegIterI szI (fun _ => 0) (fun _ => 1 / 400) :=
  ⟨fun n => by show (2 : ℝ) ^ 2 / ((4 : ℕ) : ℝ) ^ 2 ≤ 1 - 1 / 400; norm_num,
    fun n => by show (1 : ℝ) - 0 ≤ 2 ^ 2; norm_num⟩

private theorem szII_W_tendsto : Tendsto (fun n : ℕ => ((TwistStep2_szII.W n : ℕ) : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
  show (n : ℝ) ≤ ((n + 25 : ℕ) : ℝ)
  push_cast
  linarith

private theorem szII_caseII : STCaseII TwistStep2_szII (fun _ => 0) (fun _ => 1 / 2000) := by
  intro n
  show (1 : ℝ) - 0 ≤ (5 : ℝ) ^ 2 / ((4 : ℕ) : ℝ) ^ 2
  norm_num

/-- **Target 6, case (i)** at the datum `szI`: `baSTIterationsgL'_holds 3` at `(κ, ε, 𝔡) = (3/1000, 1/2, 1/10)`, `𝔠 = 1/9`, `s ≡ 0 < t ≡ 1/400`; the flow,
the window, `STRegIterI` and `(con_st_ind)` are discharged. -/
theorem inst_iterationsgL' (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKboundgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) →
        STLKgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) →
        STStep2ConclgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) Cd →
        STXiBootgL' (baFMz szI zI) (Sizes.seqP (szI.withLam 0)) (fun _ => 0) (fun _ => 1 / 400) →
        ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
          (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0))
            (fun _ => 0) (fun _ => 1 / 400) (fun n => STAI szI n) r k) →
          (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0))
            (fun _ => 0) (fun _ => 1 / 400) (fun n => STAI szI n) r (k - 1)) →
          STIterHypgL (baFMz szI zI) (Sizes.seqP (szI.withLam 0))
            (fun _ => 0) (fun _ => 1 / 400) (fun n => STAI szI n) n_ k) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baSTIterationsgL'_holds 3 (by norm_num) (3 / 1000) (1 / 2) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  exact ⟨𝔠d, h0, h1, fun hK hL h1' h2 hB => H (1 / 9) szI zI flowI.1 (fun _ => 0) (fun _ => 1 / 400)
    (fun _ => le_rfl) (fun _ => by norm_num) szI_window szI_regIterI hK hL
    (conStInd_const szI szI_W_tendsto (by norm_num) (by norm_num) h0) h1' h2 hB⟩

/-- **Target 6, case (ii)** at the merged datum `TwistStep2_szII`: `baSTIterationsIIgL'_holds 3` at `(κ, ε, 𝔡) = (3/5000, 1/2, 1/10)`, `𝔠 = 1/9`,
`s ≡ 0 < t ≡ 1/2000`; the flow (`TwistStep2_flowII`), the window, `STCaseII` (`1 ≤ 25/16`) and `(con_st_ind)` are discharged. -/
theorem inst_iterationsIIgL' (Cd : ℝ) (hCd : 0 < Cd) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      (STKboundgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) →
        STLKgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) →
        STStep1LoopgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) →
        STStep2ConclgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) Cd →
        STXiBootgL' (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0)) (fun _ => 0) (fun _ => 1 / 2000) →
        ∀ n_ k : ℕ, 2 ≤ n_ → 1 ≤ k →
          (∀ r, 2 ≤ r → r + 1 ≤ n_ → STIterHypgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0))
            (fun _ => 0) (fun _ => 1 / 2000) (fun n => STAII TwistStep2_szII (fun _ => 0) n) r k) →
          (∀ r, 2 ≤ r → r ≤ n_ + 2 → STIterHypgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0))
            (fun _ => 0) (fun _ => 1 / 2000) (fun n => STAII TwistStep2_szII (fun _ => 0) n) r (k - 1)) →
          STIterHypgL (baFMz TwistStep2_szII TwistStep2_zII) (Sizes.seqP (TwistStep2_szII.withLam 0))
            (fun _ => 0) (fun _ => 1 / 2000) (fun n => STAII TwistStep2_szII (fun _ => 0) n) n_ k) := by
  obtain ⟨𝔠d, h0, h1, H⟩ := baSTIterationsIIgL'_holds 3 (by norm_num) (3 / 5000) (1 / 2) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) Cd hCd
  obtain ⟨hflow, ht0⟩ := TwistStep2_flowII
  exact ⟨𝔠d, h0, h1, fun hK hL h1' h2 hB => H (1 / 9) TwistStep2_szII TwistStep2_zII hflow (fun _ => 0) (fun _ => 1 / 2000)
    (fun _ => le_rfl) (fun _ => by norm_num) ht0 szII_caseII hK hL
    (conStInd_const TwistStep2_szII szII_W_tendsto (by norm_num) (by norm_num) h0) h1' h2 hB⟩

end RBM.BA.ZeroModeBAInst

end
