/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.NQLinGen
import RBM3D.Chain.GridAssemblyGen
import RBM3D.Chain.AzumaProxyGen
import RBM3D.Chain.StepDecompGen
import RBM3D.Induction.QtNonzero

/-!
# The grid ingredients of the zero-mode-removed evolution `Q^{(A)}(𝓛 − 𝒦)^{(k)}` over a carrier (U3s4b, file 1; ticket T2505)

Generic forms of `Induction/QtNonzero.lean` (not edited) over a carrier `Cm : Step2Mat sz`, namespace `RBM.BA`, no `BA/*` import.
Paper: arXiv:2507.20274, `lem:STOeq_Qt_nonzero` (`3_5:1561`), `lem:sum_decay_nonzero` (`3_5:1666`), `(normQA2)` (`3_5:1475`),
`lem: newPQ` (`3_5:1482`).  The kernel is `Step2Gen_UN Cm.toFlowFM` (U-C4); `etaT E u` is `Cm.eta n u`, `|E n| < 2` is `LoopForm`
(`StepDecompGen_LoopForm`) and `‖Cm.m n‖ ≤ 1`; `Q^{(A)}` commutes with the kernel under `ZeroModeGen_KerSums`.

* **Target 6 (D1)** `QtNZGen_KerNZ`, `QtNZGen_KerNZFam` (= `T2505_KerNZ`, `T2505_KerNZFam`, the check texts): `lem:sum_decay_nonzero`,
  deterministic and loss-free (EK-5), in the A-form window `(1 - v) L² ≤ A gK²`; the band discharge `qtNZGen_kerNZ_band_at`,
  `qtNZGen_kerNZ_band` (`A = 1`, `gK = sz.lam`) and the row-sum form `qtNZGen_row_of_kerNZ`.
* **Target 7** (`QtNonzero` §2-§8) `cQVNZNg`, `assembledRHSNZNg`, `nz_hkerg`, `nz_hdriftNg`, `subGaussStop_nzNg`, `yMomentBounds_nzNg`,
  `budgetNZNg`.
* **Target 9** compiled nonempty instances at `d = 3` (band carrier `bandStep2Mat`, data of `szB` and `sz0`).

The model-free privates of `QtNonzero` §1, §6-§8 are reused by `open private`; the ones that read `Ugen`, `etaT`, `mE` are copied under
the stem `QtNZGen_`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private qtNZ_sum_norm_le_of_bound qtNZ_sum_abs_q_le qtNZ_q qtNZ_zeroModeSet_apply qtNZ_re_sum_le qtNZ_comb qtNZ_aesm_of_pow4
  qtNZ_absorb qtNZ_final from RBM3D.Induction.QtNonzero

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqBudget_sqrt_add_le)

/-! ## 1. Target 6 (D1): `lem:sum_decay_nonzero`, the A-form -/

/-- **D1, `QtNZGen_KerNZ`** (= `T2505_KerNZ`, text fixed at row b's 1a-audit): `lem:sum_decay_nonzero` (`3_5:1666`), loss-free (EK-5), for the
carrier kernel at index `n`, every `σ` and `Aset ⊇ I_diff(σ)`, in the A-form window `(1 - v) L² ≤ A gK²` (UBA-C1 (b)).  Band: `nzUgen_holds`
(`A = 1`, `gK = sz.lam`); BA: U3-BA (a), `baEKSumDecayNonzero_holds` with `baTwKerZero_holds` (`A = (κ+1)/κ`). -/
def QtNZGen_KerNZ {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (gK : ℕ → ℝ) (k : ℕ) (A C5 : ℝ) (n : ℕ) : Prop :=
  ∀ v w : ℝ, 0 ≤ v → (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ A * gK n ^ 2 → v ≤ w → w < 1 →
    ∀ (σ : Fin k → Bool) (Aset : Finset (Fin k)), (∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset) →
      ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X)‖ ≤ C5 * ‖X‖

/-- **D1, the family form** (= `T2505_KerNZFam`; guarded; `∃ C5` after `(k, κ, 𝔡)`, before `(sz, z)`: U5S-C3; per index, eventually in `n`). -/
def QtNZGen_KerNZFam (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (Aof : ℝ → ℝ) : Prop :=
  3 ≤ d → ∀ k : ℕ, 2 ≤ k → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C5 : ℝ, 0 < C5 ∧
    ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, QtNZGen_KerNZ (mk sz z) (gK sz z) k (Aof κ) C5 n

section D1Band

/-- The band D1 constant: a total choice of the `∃ C` of `nzUgen_holds` (so that the per-index discharge concludes `QtNZGen_KerNZ`, not `∃`). -/
def qtNZGen_bandC (d k : ℕ) (Λg κ' : ℝ) : ℝ :=
  if h : 3 ≤ d ∧ 2 ≤ k ∧ 0 < Λg ∧ 0 < κ' then Classical.choose (RBM.Ind.nzUgen_holds d k h.1 h.2.1 Λg κ' h.2.2.1 h.2.2.2) else 1

/-- **D1 at one index, band discharge** (`A = 1`, `gK = sz.lam`): `nzUgen_holds` (`QtNonzero:299`) read through `bandStep2_Ugen`
(`GridDuhamelGen:181`) and `ZeroModeCalc_STIdiff_subset_iff`; the window `(1 - v) L² ≤ lam²` is `1 - lam²/L² ≤ v`.  Head `QtNZGen_KerNZ`. -/
theorem qtNZGen_kerNZ_band_at {d : ℕ} (hd : 3 ≤ d) {k : ℕ} (hk : 2 ≤ k) {Λg κ' : ℝ} (hΛg : 0 < Λg) (hκ' : 0 < κ')
    (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (hg : 0 < sz.lam n) (hgΛ : sz.lam n ≤ Λg) (hE : |E n| < 2) (hκE : κ' ≤ (mE (E n)).im) :
    QtNZGen_KerNZ (bandFM sz E) sz.lam k 1 (qtNZGen_bandC d k Λg κ') n := by
  have hspec := Classical.choose_spec (RBM.Ind.nzUgen_holds d k hd hk Λg κ' hΛg hκ')
  simp only [qtNZGen_bandC, hd, hk, hΛg, hκ', and_self, ↓reduceDIte]
  intro v w hv0 hvg hvw hw1 σ Aset hA X
  have hL0 : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ 2 := by
    have : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
    positivity
  have hwin : 1 - sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ v := by
    have h1 : 1 - v ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by
      rw [le_div_iff₀ hL0]; linarith
    linarith
  have key := (hspec.2 (sz.L n) (sz.three_le_L n) (sz.lam n) (E n) hg hgΛ hE hκE v w hv0 hwin hvw hw1 σ Aset
    ((ZeroModeCalc_STIdiff_subset_iff σ Aset).2 hA)).1 X
  rw [← bandStep2_Ugen]
  exact key

end D1Band

/-- **The row of `Q^{(A)} ∘ 𝒰` from an operator bound** (`QtNonzero` §1, model-free duality): `Step2Gen_UN` is a tensor kernel (`Step2Gen:202`), so
`Q^{(A)} ∘ 𝒰` is the tensor kernel with `Proj_{e^⊥} ∘ uKer` at the indices of `A` (`zeroModeSet_tensorKer`); an `∞→∞` bound `C5` gives, for every
label `a`, a row `κ_b = ∏_i K_i(a_i, b_i)` with `Σ_b |κ_b| ≤ C5` (`qtNZ_sum_norm_le_of_bound`). -/
theorem qtNZGen_row_of_op {d : ℕ} {sz : Sizes d} (C : FlowFM sz) {n k : ℕ} (σ : Fin k → Bool) (Aset : Finset (Fin k)) (v w : ℝ)
    {C5 : ℝ} (hC5 : 0 ≤ C5)
    (hop : ∀ X : (Fin k → Zd d (sz.L n)) → ℂ, ‖zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X)‖ ≤ C5 * ‖X‖)
    (a : Fin k → Zd d (sz.L n)) :
    ∃ κ : (Fin k → Zd d (sz.L n)) → ℂ,
      (∀ X : (Fin k → Zd d (sz.L n)) → ℂ, zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X) a = ∑ b, κ b * X b) ∧
        ∑ b, ‖κ b‖ ≤ C5 := by
  set K' : Fin k → Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ := fun i =>
    if i ∈ Aset then projMat d (sz.L n) * Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w
    else Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w with hK'
  have hrow : ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
      zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X) a = ∑ b, (∏ i, K' i (a i) (b i)) * X b := by
    intro X
    change zeroModeSet d (sz.L n) Aset (tensorKer d (sz.L n)
      (fun i : Fin k => Step2Gen_uKer C n (σ i) (σ (finRotate k i)) v w) X) a = _
    rw [zeroModeSet_tensorKer]
    rfl
  refine ⟨fun b => ∏ i, K' i (a i) (b i), hrow, ?_⟩
  exact qtNZ_sum_norm_le_of_bound _ hC5 fun X => by
    rw [← hrow X]
    exact (norm_le_pi_norm _ a).trans (hop X)

/-- **The row-sum form of D1** (target 6): the `∞→∞` bound `C5` of `QtNZGen_KerNZ` gives, for every label `a`, a row `κ` with `Σ_b |κ_b| ≤ C5`. -/
theorem qtNZGen_row_of_kerNZ {d : ℕ} {sz : Sizes d} {C : FlowFM sz} {gK : ℕ → ℝ} {k : ℕ} {A C5 : ℝ} {n : ℕ}
    (h : QtNZGen_KerNZ C gK k A C5 n) (hC5 : 0 ≤ C5) {v w : ℝ} (hv0 : 0 ≤ v)
    (hwin : (1 - v) * ((sz.L n : ℕ) : ℝ) ^ 2 ≤ A * gK n ^ 2) (hvw : v ≤ w) (hw1 : w < 1)
    (σ : Fin k → Bool) (Aset : Finset (Fin k)) (hA : ∀ i, σ i ≠ σ (finRotate k i) → i ∈ Aset) (a : Fin k → Zd d (sz.L n)) :
    ∃ κ : (Fin k → Zd d (sz.L n)) → ℂ,
      (∀ X : (Fin k → Zd d (sz.L n)) → ℂ, zeroModeSet d (sz.L n) Aset (Step2Gen_UN C n σ v w X) a = ∑ b, κ b * X b) ∧
        ∑ b, ‖κ b‖ ≤ C5 :=
  qtNZGen_row_of_op C σ Aset v w hC5 (h v w hv0 hwin hvw hw1 σ Aset hA) a

/-! ## 2. The vocabulary (target 7) -/

section Vocab

variable {d : ℕ} {sz : Sizes d}

/-- **The sub-Gaussian proxy of the `j`-th propagated zero-mode-removed increment** (band `cQVNZN`, `QtNonzero:224`): `Δ · k · C² ·
(Γ(ΓΛ) B_{u_j}^{2k}/η_{u_j} + W^{-D''})`, `η_u = Cm.eta n u`, `C` the row-sum bound of `Q^{(A)} ∘ 𝒰` (no ratio factor, no far part). -/
def cQVNZNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (C Γ Λ D'' : ℝ) (j : ℕ) : ℝ≥0 :=
  (gridStep s v K n * ((k : ℝ) * C ^ 2 *
    (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D'')))).toNNReal

/-- **The right side of `AssembledNg` at `m = K n`** for the zero-mode-removed evolution (band `assembledRHSNZN`, `QtNonzero:233`): kernel
weight `κ ≡ C`, `εK ≡ 0`, drift level `cA · dDriftLinNg`, proxy `cQVNZNg`, step error `cA · stepErrNg` (`cA = 2^{|A|}`). -/
def assembledRHSNZNg (Cm : Step2Mat sz) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y τK εq X0 : ℝ) : ℝ :=
  C * X0 +
    gridStep s v K n * ∑ j ∈ Finset.range (K n),
      C * (cA * dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) +
    ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ)) +
    ((sz.size n : ℕ) : ℝ) ^ (-D_Y) +
    ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
      stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1)) (gridStep s v K n)
        (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k))

end Vocab

/-! ## 3. The fields `hker`, `hdrift` of `GridAssemblyHypNg` for the class "fixed points of `Q^{(A)}`" (target 7) -/

section Fields

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- **The field `hker`** (band `nz_hker`, `QtNonzero:327`): for `X = Q^{(A)} X`, `𝒰 X = 𝒰 Q^{(A)} X = Q^{(A)} 𝒰 X` (`zeroModeSet_UNg`, the carrier fact
`ZeroModeGen_KerSums` replaces `3 ≤ L`, `|E| ≤ 2`), so `‖(𝒰 X)(a)‖ ≤ ‖Q^{(A)} 𝒰 X‖ ≤ C ‖X‖ ≤ C M`.  The grid times need no window here: the
operator bound is a hypothesis. -/
theorem nz_hkerg {k : ℕ} (C : FlowFM sz) (n : ℕ) (hKS : ZeroModeGen_KerSums C n) (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
    (K : ℕ) (Cb : ℝ) (hC : 0 ≤ Cb)
    (hop : ∀ i m, i ≤ m → m ≤ K → ∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
      ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (u i) (u m) X)‖ ≤ Cb * ‖X‖) :
    ∀ i m, i ≤ m → m ≤ K → ∀ (X : (Fin k → Zd d (sz.L n)) → ℂ) (M δ : ℝ), 0 ≤ M → 0 ≤ δ →
      (∀ b, ‖X b‖ ≤ M) → zeroModeSet d (sz.L n) A X = X →
      ∀ a, ‖Step2Gen_UN C n σ (u i) (u m) X a‖ ≤ Cb * M + 0 * δ := by
  intro i m him hmK X M δ hM hδ hXM hXQ a
  have hcomm : zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (u i) (u m) X) = Step2Gen_UN C n σ (u i) (u m) X := by
    have h := zeroModeSet_UNg C n hKS σ (u i) (u m) A X
    rw [hXQ] at h
    exact h
  have hXn : ‖X‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).2 hXM
  calc ‖Step2Gen_UN C n σ (u i) (u m) X a‖
      = ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (u i) (u m) X) a‖ := by rw [hcomm]
    _ ≤ ‖zeroModeSet d (sz.L n) A (Step2Gen_UN C n σ (u i) (u m) X)‖ := norm_le_pi_norm _ a
    _ ≤ Cb * ‖X‖ := hop i m him hmK X
    _ ≤ Cb * M := mul_le_mul_of_nonneg_left hXn hC
    _ = Cb * M + 0 * δ := by ring

/-- **The field `hdrift`** (band `nz_hdriftN`, `QtNonzero:358`): the drift of the zero-mode-removed hierarchy on `GoodLinNg`:
`‖(Q^{(A)} Dr)(b)‖ ≤ 2^{|A|} ‖Dr‖ ≤ 2^{|A|} dDriftLinNg` (`norm_zeroModeSet_le` = `(normQA2)`, `nqLin_hdriftNg`). -/
theorem nz_hdriftNg {n k : ℕ} (hk : 2 ≤ k) (σ : Fin k → Bool) (A : Finset (Fin k))
    (s v : ℕ → ℝ) (K : ℕ → ℕ) (Γ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (τ : PathΩ sz → ℕ)
    (hτG : ∀ ω j, j < τ ω → Cm.Hpath s v K n j ω ∈ GoodLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) :
    ∀ ω j, j < K n → j < τ ω → ∀ b : Fin k → Zd d (sz.L n),
      ‖zeroModeSet d (sz.L n) A (driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ) b‖ ≤
        2 ^ A.card * dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) := by
  intro ω j hjK hjτ b
  have hD := nqLin_hdriftNg (Cm := Cm) hk σ s v K Γ Φ₁ Φ₂ Φ₃ τ hτG ω j hjK hjτ
  have hD0 : 0 ≤ dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    (norm_nonneg _).trans (hD (fun _ => 0))
  have hDn : ‖driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ‖ ≤
      dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
    (pi_norm_le_iff_of_nonneg hD0).2 hD
  calc ‖zeroModeSet d (sz.L n) A (driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ) b‖
      ≤ ‖zeroModeSet d (sz.L n) A (driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ)‖ :=
        norm_le_pi_norm _ b
    _ ≤ 2 ^ A.card * ‖driftTensorNg Cm n (gridTime s v K n j) (Cm.Hpath s v K n j ω) σ‖ := norm_zeroModeSet_le A _
    _ ≤ 2 ^ A.card * dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)

end Fields

/-! ## 4. The Azuma input for `Q^{(A)} Z_j` (target 7) -/

section Azuma

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- **Target 7, `subGaussStop_nzNg`** (band `subGaussStop_nzN`, `QtNonzero:417`): the Azuma input `SubGaussStopNg` for the zero-mode-removed first-chaos
part `Q^{(A)} Z_j`, proxy `cQVNZNg`, on any stopping family that stays in `GoodSetNg` (its `STeeMg` clause (D4) only), from a row-sum bound `≤ C` of
`Q^{(A)} ∘ 𝒰_{u_{j+1},u_m}`.  `𝒰(Q^{(A)} Z_j)(a) = Q^{(A)} 𝒰(Z_j)(a) = Σ_b κ_b Z_j(b)` (`zeroModeSet_UNg` under `ZeroModeGen_KerSums`, the row `κ`);
the pin `AzumaSubGNg` with the loop family `loopFamNg` (in the Hermitian test class by `hermTestFunLoopNOf` under `LoopForm`) and the weights `κ`;
`QVPropagatedNg` at these weights; `Re Σ κ κ̄' ee ≤ C² max‖ee(u_{j+1})‖` and the `STeeMg` clause of `GoodSetNg` at `u_j` plus the shift
`eeShiftErrNg` (the hypothesis `hδ`, `norm_STeeMg_shiftNg_le`). -/
theorem subGaussStop_nzNg [IsProbabilityMeasure Cm.Pp] {E g s v : ℕ → ℝ} {K : ℕ → ℕ} {n k : ℕ} {σ : Fin k → Bool}
    {A : Finset (Fin k)} {C Γ Λ Φ τ' D' D'' : ℝ} {τ : PathΩ sz → ℕ} (hk : 2 ≤ k)
    (h : AzumaSubGNg Cm g s v K) (hL : StepDecompGen_LoopForm Cm E) (hQV : QVPropagatedNg Cm g)
    (hKS : ZeroModeGen_KerSums Cm.toFlowFM n) (hm : ‖Cm.m n‖ ≤ 1)
    (hS : ∀ a : Zd d (sz.L n), ∑ b : Zd d (sz.L n), ‖Cm.S n a b‖ ≤ 1)
    (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1) (hC : 0 ≤ C) (hΓ : 0 ≤ Γ) (hΛ : 0 ≤ Λ)
    (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (hG : ∀ ω j, j < τ ω → GoodSetNg Cm n (gridTime s v K n j) k Γ Λ Φ τ' D' (Cm.Hpath s v K n j ω))
    (m : ℕ) (hmK : m ≤ K n) (a : Fin k → Zd d (sz.L n)) (j : ℕ) (hj : j < m)
    (hrow : ∃ κ : (Fin k → Zd d (sz.L n)) → ℂ,
      (∀ X : (Fin k → Zd d (sz.L n)) → ℂ,
        zeroModeSet d (sz.L n) A (Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n (j + 1)) (gridTime s v K n m) X) a =
          ∑ b, κ b * X b) ∧ ∑ b, ‖κ b‖ ≤ C)
    (hδ : ((sz.W n : ℕ) : ℝ) ^ (-D') + eeShiftErrNg Cm n k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
      ((sz.W n : ℕ) : ℝ) ^ (-D'')) :
    SubGaussStopNg Cm σ (gridTime s v K n) τ
      (fun j ω => zeroModeSet d (sz.L n) A (ZvecNg Cm s v K n j σ ω)) m a j (cQVNZNg Cm s v K n k C Γ Λ D'' j) := by
  obtain ⟨κ, hκ, hκC⟩ := hrow
  have hKn : K n ≠ 0 := by omega
  have hmono : ∀ i i', i ≤ i' → gridTime s v K n i ≤ gridTime s v K n i' := fun i i' hii =>
    ST_gridTime_mono s v K n (hsv n) hii
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => by
    have hh := hmono 0 i (Nat.zero_le i)
    rw [ST_gridTime_zero] at hh
    linarith [hs0 n]
  have hule : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi =>
    (hmono i (K n) hi).trans_eq (gridTime_last s v K n hKn)
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => (hule i hi).trans_lt (hv1 n)
  have hΔ : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hj1 : j + 1 ≤ K n := by omega
  -- the stopped combination is the `κ`-weighted first-chaos sum
  have hcomm : ∀ ω' : PathΩ sz,
      Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n (j + 1)) (gridTime s v K n m)
        (zeroModeSet d (sz.L n) A (ZvecNg Cm s v K n j σ ω')) a =
      ∑ b, κ b * ZfamNg Cm s v K n j (loopFamNg Cm s v K n j σ) ω' b := by
    intro ω'
    rw [← zeroModeSet_UNg Cm.toFlowFM n hKS σ _ _ A]
    exact hκ _
  -- the variance majorant on the good set
  have hQ : ∀ M ∈ {H | GoodSetNg Cm n (gridTime s v K n j) k Γ Λ Φ τ' D' H}, M.IsHermitian →
      gridStep s v K n * ∑ c : CoordF d (sz.L n) (sz.W n),
        (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
          ‖∑ b, κ b * RBM.Ind.dirDerivN (loopFamNg Cm s v K n j σ b) M
            (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2 ≤
        (cQVNZNg Cm s v K n k C Γ Λ D'' j : ℝ) := by
    intro M hM hMh
    have hq := hQV n (gridTime s v K n (j + 1)) (hu0 _) (hu1 _ hj1) M hMh k hk σ κ
    obtain ⟨-, -, -, -, -, -, hD4, -, -⟩ := hM
    have hjj : gridTime s v K n j ≤ gridTime s v K n (j + 1) := hmono j (j + 1) (Nat.le_succ j)
    have hWD' : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D') := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hee : ∀ b b' : Fin k → Zd d (sz.L n),
        ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤
          Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) +
            ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
      intro b b'
      have h1 := hD4 σ b b'
      have h2 := norm_STeeMg_shiftNg_le hL hm hS hMh hjj (hu1 _ hj1) σ b b'
      have h3 : ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b'‖ ≤
          ‖STeeMg Cm n (gridTime s v K n j) M σ b b'‖ +
            ‖STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b' - STeeMg Cm n (gridTime s v K n j) M σ b b'‖ := by
        have := norm_add_le (STeeMg Cm n (gridTime s v K n j) M σ b b')
          (STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b' - STeeMg Cm n (gridTime s v K n j) M σ b b')
        rwa [add_sub_cancel] at this
      linarith
    have hMee0 : 0 ≤ Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
      (norm_nonneg _).trans (hee (fun _ => 0) (fun _ => 0))
    have hre := qtNZ_re_sum_le κ (fun b b' => STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b') hκC hMee0 hee
    calc gridStep s v K n * ∑ c : CoordF d (sz.L n) (sz.W n),
          (gvarF d (sz.L n) (sz.W n) (g n) c : ℝ) *
            ‖∑ b, κ b * RBM.Ind.dirDerivN (loopFamNg Cm s v K n j σ b) M
              (coordinateMatrix d (sz.L n) (sz.W n) c)‖ ^ 2
        ≤ gridStep s v K n * ((k : ℝ) * (∑ b, ∑ b', κ b * (starRingEnd ℂ) (κ b') *
            STeeMg Cm n (gridTime s v K n (j + 1)) M σ b b').re) :=
          mul_le_mul_of_nonneg_left hq hΔ
      _ ≤ gridStep s v K n * ((k : ℝ) * (C ^ 2 * (Γ * (Γ * Λ) *
            ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) +
              ((sz.W n : ℕ) : ℝ) ^ (-D'')))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre (Nat.cast_nonneg k)) hΔ
      _ = gridStep s v K n * ((k : ℝ) * C ^ 2 *
            (Γ * (Γ * Λ) * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) +
              ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by ring
      _ ≤ (cQVNZNg Cm s v K n k C Γ Λ D'' j : ℝ) := Real.le_coe_toNNReal _
  have hΦ : ∀ b, HermTestFun sz n (loopFamNg Cm s v K n j σ b) := fun b => by
    change HermTestFun sz n (fun H => Cm.LM n (gridTime s v K n (j + 1)) H σ b)
    rw [StepDecompGen_LM_eq hL]
    exact (hermTestFunLoopNOf sz k n (Cm.m n) (E n) _ (hL n).1 (hu1 _ hj1) σ b).1
  have key := h n (loopFamNg Cm s v K n j σ) hΦ κ τ
    (fun j' => {H | GoodSetNg Cm n (gridTime s v K n j') k Γ Λ Φ τ' D' H}) hτ hG j
    (cQVNZNg Cm s v K n k C Γ Λ D'' j) hQ
  have hfun : (fun ω' : PathΩ sz => Step2Gen_UN Cm.toFlowFM n σ (gridTime s v K n (j + 1)) (gridTime s v K n m)
        (zeroModeSet d (sz.L n) A (ZvecNg Cm s v K n j σ ω')) a) =
      fun ω => ∑ b, κ b * ZfamNg Cm s v K n j (loopFamNg Cm s v K n j σ) ω b :=
    funext hcomm
  unfold SubGaussStopNg
  simp only []
  rw [hfun]
  exact key

end Azuma

/-! ## 5. The `Y`-moment inputs pass to `Q^{(A)} Y` (target 7) -/

section YMoments

variable {d : ℕ} {sz : Sizes d} {Cm : Step2Mat sz}

/-- `Q^{(A)}` commutes with the stopped propagated increment: the `b`-th stopped edge of `Q^{(A)} Y` is `Σ_{b'} q_{b b'}` times the `b'`-th stopped
edge of `Y` (`zeroModeSet_UNg` under `ZeroModeGen_KerSums`; the real kernel `q` of `Q^{(A)}`; band `qtNZ_stopped_comm`, `QtNonzero:712`). -/
private theorem QtNZGen_stopped_comm {n k : ℕ} (hKS : ZeroModeGen_KerSums Cm.toFlowFM n) (σ : Fin k → Bool) (A : Finset (Fin k))
    (u : ℕ → ℝ) (τ : PathΩ sz → ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (m : ℕ)
    (b : Fin k → Zd d (sz.L n)) (j : ℕ) (ω : PathΩ sz) :
    stoppedEdgeNg Cm σ u (u m) τ (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω =
      ∑ b', ((qtNZ_q d (sz.L n) A b b' : ℝ) : ℂ) * stoppedEdgeNg Cm σ u (u m) τ Y b' j ω := by
  unfold stoppedEdgeNg
  by_cases hω : ω ∈ {ω' | j < τ ω'}
  · simp only [Set.indicator_of_mem hω]
    rw [← zeroModeSet_UNg Cm.toFlowFM n hKS σ _ _ A, qtNZ_zeroModeSet_apply]
  · simp [Set.indicator_of_notMem hω]

/-- **Target 7, `yMomentBounds_nzNg`** (band `yMomentBounds_nzN`, `QtNonzero:731`): the `Y`-moment inputs (`YMomentBoundsNg`) pass to `Q^{(A)} Y` with the
levels `4^{|A|+1} v`, `16^{|A|+1} w`.  `stoppedEdgeNg (Q^{(A)} Y)_b = Σ_{b'} q_{b b'} stoppedEdgeNg (Y)_{b'}` (commutation at `u_m`) with the real kernel `q`
of `Q^{(A)}` and `Σ_{b'} |q_{b b'}| ≤ 2^{|A|}`; then linearity of the conditional expectation and `(Σ q x)² ≤ (Σ|q|) Σ|q| x²`, `(Σ q x)⁴ ≤ (Σ|q|)³ Σ|q| x⁴`
(`qtNZ_comb`, for the real and the imaginary part separately, `q` being real); the measurability of the stopped edges needs no measurability of `{j < τ}`
(`qtNZ_aesm_of_pow4`). -/
theorem yMomentBounds_nzNg [IsProbabilityMeasure Cm.Pp] {n k : ℕ} (σ : Fin k → Bool) (A : Finset (Fin k)) (u : ℕ → ℝ)
    (τ : PathΩ sz → ℕ) (K : ℕ) (Y : ℕ → PathΩ sz → (Fin k → Zd d (sz.L n)) → ℂ) (v w : ℕ → ℝ)
    (hKS : ZeroModeGen_KerSums Cm.toFlowFM n) (hY : YMomentBoundsNg Cm σ u τ K Y v w) :
    YMomentBoundsNg Cm σ u τ K (fun j ω => zeroModeSet d (sz.L n) A (Y j ω))
      (fun j => 4 ^ (A.card + 1) * v j) (fun j => 16 ^ (A.card + 1) * w j) := by
  obtain ⟨hYm, hY⟩ := hY
  refine ⟨fun j => ?_, fun m hm b j hj => ?_⟩
  · exact (LinearMap.continuous_of_finiteDimensional
      (zeroModeSetLin (d := d) (L := sz.L n) A)).comp_stronglyMeasurable (hYm j)
  · -- the stopped edges of `Y` and their real kernel
    have hall := fun b' => hY m hm b' j hj
    have hid := QtNZGen_stopped_comm hKS σ A u τ Y m b j
    -- measurability of the (unstopped) `b'`-th edge
    have hgm : ∀ b', Measurable (fun ω => (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
        (Y j ω) b').re) := by
      intro b'
      have hcont : Continuous (fun T : (Fin k → Zd d (sz.L n)) → ℂ =>
          (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) T b').re) := by
        refine Complex.continuous_re.comp ?_
        unfold Step2Gen_UN
        exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
      exact (hcont.comp_stronglyMeasurable ((hYm j).mono ((filt sz).le (j + 1)))).measurable
    have hgm' : ∀ b', Measurable (fun ω => (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m)
        (Y j ω) b').im) := by
      intro b'
      have hcont : Continuous (fun T : (Fin k → Zd d (sz.L n)) → ℂ =>
          (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) T b').im) := by
        refine Complex.continuous_im.comp ?_
        unfold Step2Gen_UN
        exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
      exact (hcont.comp_stronglyMeasurable ((hYm j).mono ((filt sz).le (j + 1)))).measurable
    have hre_dich : ∀ b' ω, (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).re = 0 ∨
        (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).re =
          (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b').re := by
      intro b' ω
      by_cases hω : ω ∈ {ω' | j < τ ω'}
      · right; simp [stoppedEdgeNg, Set.indicator_of_mem hω]
      · left; simp [stoppedEdgeNg, Set.indicator_of_notMem hω]
    have him_dich : ∀ b' ω, (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).im = 0 ∨
        (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).im =
          (Step2Gen_UN Cm.toFlowFM n σ (u (j + 1)) (u m) (Y j ω) b').im := by
      intro b' ω
      by_cases hω : ω ∈ {ω' | j < τ ω'}
      · right; simp [stoppedEdgeNg, Set.indicator_of_mem hω]
      · left; simp [stoppedEdgeNg, Set.indicator_of_notMem hω]
    have hre_m : ∀ b', AEStronglyMeasurable
        (fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).re) Cm.Pp := fun b' =>
      qtNZ_aesm_of_pow4 _ _ (hgm b') (hre_dich b') (hall b').2.2.1.aestronglyMeasurable
    have him_m : ∀ b', AEStronglyMeasurable
        (fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).im) Cm.Pp := fun b' =>
      qtNZ_aesm_of_pow4 _ _ (hgm' b') (him_dich b') (hall b').2.2.2.1.aestronglyMeasurable
    -- the real kernel
    set q : (Fin k → Zd d (sz.L n)) → ℝ := fun b' => qtNZ_q d (sz.L n) A b b' with hq
    have hre_pt : ∀ ω, (stoppedEdgeNg Cm σ u (u m) τ
          (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω).re =
        ∑ b', q b' * (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).re := by
      intro ω
      rw [hid ω, Complex.re_sum]
      exact Finset.sum_congr rfl fun b' _ => Complex.re_ofReal_mul _ _
    have him_pt : ∀ ω, (stoppedEdgeNg Cm σ u (u m) τ
          (fun j ω => zeroModeSet d (sz.L n) A (Y j ω)) b j ω).im =
        ∑ b', q b' * (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).im := by
      intro ω
      rw [hid ω, Complex.im_sum]
      exact Finset.sum_congr rfl fun b' _ => Complex.im_ofReal_mul _ _
    -- the levels are nonnegative
    obtain ⟨b0⟩ : Nonempty (Fin k → Zd d (sz.L n)) := ⟨fun _ => 0⟩
    have hv0 : 0 ≤ v j := by
      have h1 : 0 ≤ᵐ[Cm.Pp] Cm.Pp[fun ω => (stoppedEdgeNg Cm σ u (u m) τ Y b0 j ω).re ^ 2 |
          filt sz j] := condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      obtain ⟨ω, hω⟩ := (h1.and (hall b0).2.2.2.2.1).exists
      exact hω.1.trans hω.2
    have hw0 : 0 ≤ w j :=
      (integral_nonneg fun ω => by positivity).trans (hall b0).2.2.2.2.2.2.1
    -- the row sum of the kernel
    have hc0 : 0 ≤ ∑ b', |q b'| := Finset.sum_nonneg fun b' _ => abs_nonneg _
    have hc : ∑ b', |q b'| ≤ 2 ^ A.card := qtNZ_sum_abs_q_le A b
    have hc2 : (∑ b', |q b'|) ^ 2 ≤ 4 ^ (A.card + 1) := by
      calc (∑ b', |q b'|) ^ 2 ≤ ((2 : ℝ) ^ A.card) ^ 2 := pow_le_pow_left₀ hc0 hc 2
        _ = 4 ^ A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 4 ^ (A.card + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    have hc4 : (∑ b', |q b'|) ^ 4 ≤ 16 ^ (A.card + 1) := by
      calc (∑ b', |q b'|) ^ 4 ≤ ((2 : ℝ) ^ A.card) ^ 4 := pow_le_pow_left₀ hc0 hc 4
        _ = 16 ^ A.card := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        _ ≤ 16 ^ (A.card + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    -- the real and imaginary parts
    obtain ⟨r0, r4, r2, rI⟩ := qtNZ_comb (m := filt sz j) (μ := Cm.Pp)
      (fun b' ω => (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).re) q hre_m
      (fun b' => (hall b').1) (fun b' => (hall b').2.2.1)
      (fun b' => (hall b').2.2.2.2.1) (fun b' => (hall b').2.2.2.2.2.2.1)
    obtain ⟨i0, i4, i2, iI⟩ := qtNZ_comb (m := filt sz j) (μ := Cm.Pp)
      (fun b' ω => (stoppedEdgeNg Cm σ u (u m) τ Y b' j ω).im) q him_m
      (fun b' => (hall b').2.1) (fun b' => (hall b').2.2.2.1)
      (fun b' => (hall b').2.2.2.2.2.1) (fun b' => (hall b').2.2.2.2.2.2.2)
    simp only [hre_pt, him_pt]
    refine ⟨r0, i0, r4, i4, ?_, ?_, ?_, ?_⟩
    · refine r2.trans (Filter.Eventually.of_forall fun ω => ?_)
      exact mul_le_mul_of_nonneg_right hc2 hv0
    · refine i2.trans (Filter.Eventually.of_forall fun ω => ?_)
      exact mul_le_mul_of_nonneg_right hc2 hv0
    · exact rI.trans (mul_le_mul_of_nonneg_right hc4 hw0)
    · exact iI.trans (mul_le_mul_of_nonneg_right hc4 hw0)


end YMoments

/-! ## 6. The budget of the case-(ii) grid endpoint (target 7) -/

section Budget

variable {d : ℕ} {sz : Sizes d}

/-- **Target 7, `budgetNZNg`** (band `budgetNZN`, `QtNonzero:872`; the analogue of `budgetNonAltLinNg`, `NQLinGen:605`; no ratio weights, no far parts):
`assembledRHSNZNg ≤ N^{ε₀} (Λ^{1/2} + Φ₁ + Φ₂ + Φ₃) B_v^k`.  `B_{u_j} ≤ B_v`, `B_s ≤ B_v` (`STBctl_mono`), `Σ_j Δ/η_{u_j}` by `hlog`, `KΔ = v - s ≤ 1`,
`B_v ≥ N^{-1}` (`cont_inv_size_le_Bctl`: `N^{-D_Y}`, `N^{-D_t}`, `√(k W^{-D''})` are absorbed by `N^k ·`), `Λ ≥ 1`.  `|E n| < 2` is `LoopForm`
(`η_u > 0`, `Im m > 0`). -/
theorem budgetNZNg {E : ℕ → ℝ} (Cm : Step2Mat sz) (hL : StepDecompGen_LoopForm Cm E) (s v : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (C cA : ℝ) (Γ Λ Φ₁ Φ₂ Φ₃ : ℕ → ℝ) (D'' D_Y D_t τK εq ε₀ ε₁ X0 : ℝ) :
      2 ≤ k → 0 < C → 0 ≤ cA → 0 ≤ ε₁ → 0 ≤ s n → s n ≤ v n → v n < 1 → K n ≠ 0 →
      Γ n = ((sz.size n : ℕ) : ℝ) ^ ε₁ → 1 ≤ Λ n → 0 ≤ Φ₁ n → 0 ≤ Φ₂ n → 0 ≤ Φ₃ n →
      ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) ≤
        (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) →
      X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k →
      ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k) ≤
        ((sz.size n : ℕ) : ℝ) ^ (-D_t) →
      C * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 *
          ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      ((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
          Real.sqrt ((k : ℝ) * ((Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ)))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
      ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
          (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 →
      ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      cA * ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) ^ (-D_t) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 →
      assembledRHSNZNg Cm s v K n k C cA Γ Λ Φ₁ Φ₂ Φ₃ D'' D_Y τK εq X0 ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ * (Λ n ^ ((1 : ℝ) / 2) + Φ₁ n + Φ₂ n + Φ₃ n) *
          (sz.Bctl n (v n)) ^ k := by
  intro hk hC hcA hε₁ hs0 hsv hv1 hK hΓ hΛ hΦ₁ hΦ₂ hΦ₃ hlog hX0 hR H1 H2 H3 H4 H5 H6
  -- elementary facts
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : 1 ≤ (sz.W n * sz.L n) ^ d :=
      Nat.one_le_pow _ _ (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega))
    exact_mod_cast (show 1 ≤ sz.size n from h)
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNk : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ k := pow_pos hN0 k
  have hmono : ∀ i i', i ≤ i' → gridTime s v K n i ≤ gridTime s v K n i' := fun i i' h =>
    ST_gridTime_mono s v K n hsv h
  have hu0 : ∀ i, 0 ≤ gridTime s v K n i := fun i => by
    have h := hmono 0 i (Nat.zero_le i)
    rw [ST_gridTime_zero] at h
    linarith
  have huK := gridTime_last s v K n hK
  have hule : ∀ i ≤ K n, gridTime s v K n i ≤ v n := fun i hi =>
    (hmono i (K n) hi).trans_eq huK
  have hu1 : ∀ i ≤ K n, gridTime s v K n i < 1 := fun i hi => (hule i hi).trans_lt hv1
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n hsv
  have hKΔ : (K n : ℝ) * gridStep s v K n = v n - s n := by
    have hK' : (K n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK
    unfold gridStep
    rw [mul_div_cancel₀ _ hK']
  have hKΔ1 : (K n : ℝ) * gridStep s v K n ≤ 1 := by rw [hKΔ]; linarith
  have hΓ0 : 0 ≤ Γ n := by rw [hΓ]; exact Real.rpow_nonneg hN0.le _
  have hΛ0 : 0 ≤ Λ n := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hBv0 := Sizes.STBctl_pos sz n hv1
  have hX0' : 0 ≤ (sz.Bctl n (v n)) ^ k := pow_nonneg hBv0.le _
  have hXN : (((sz.size n : ℕ) : ℝ) ^ k)⁻¹ ≤ (sz.Bctl n (v n)) ^ k := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le)
      (RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n (hs0.trans hsv) hv1) k
  have hP0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ := Real.rpow_nonneg hN0.le _
  have hLs0 : 0 ≤ (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) :=
    mul_nonneg (inv_nonneg.2 (hL n).1.le) (Real.log_nonneg hN1)
  have hΛr1 : 1 ≤ Λ n ^ ((1 : ℝ) / 2) := Real.one_le_rpow hΛ (by norm_num)
  have hWD : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hBmono : ∀ i ≤ K n, sz.Bctl n (gridTime s v K n i) ≤ sz.Bctl n (v n) := fun i hi =>
    Sizes.STBctl_mono sz n (hule i hi) hv1
  have hBpos : ∀ i ≤ K n, 0 < sz.Bctl n (gridTime s v K n i) := fun i hi =>
    Sizes.STBctl_pos sz n (hu1 i hi)
  have hη : ∀ i ≤ K n, 0 < Cm.eta n (gridTime s v K n i) := fun i hi => NQGood1Gen_eta_pos hL n (hu1 i hi)
  -- T1: the initial term
  have T1 : C * X0 ≤ ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k := by
    have hBs0 := Sizes.STBctl_pos sz n (hsv.trans_lt hv1)
    have hBs : sz.Bctl n (s n) ≤ sz.Bctl n (v n) := Sizes.STBctl_mono sz n hsv hv1
    calc C * X0 ≤ C * (((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n (s n)) ^ k) :=
          mul_le_mul_of_nonneg_left hX0 hC.le
      _ = (C * ((sz.size n : ℕ) : ℝ) ^ ε₁) * (sz.Bctl n (s n)) ^ k := by ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * (sz.Bctl n (s n)) ^ k :=
          mul_le_mul_of_nonneg_right H1 (pow_nonneg hBs0.le _)
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * (sz.Bctl n (v n)) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hBs0.le hBs k) (by positivity)
  -- T2: the drift term
  have T2 : gridStep s v K n * ∑ j ∈ Finset.range (K n),
      C * (cA * dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * ((Φ₁ n + Φ₂ n + Φ₃ n) * (sz.Bctl n (v n)) ^ k) := by
    set X : ℝ := (sz.Bctl n (v n)) ^ k with hXdef
    set Ls : ℝ := (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) with hLsdef
    set Dc : ℝ := ((k : ℝ) - 2) * Φ₁ n + Φ₂ n + Φ₃ n with hDc
    have hk2 : (0 : ℝ) ≤ (k : ℝ) - 2 := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hDc0 : 0 ≤ Dc := by
      have := mul_nonneg hk2 hΦ₁
      linarith
    have hDc_le : Dc ≤ (k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n) := by
      have h0 : 0 ≤ 2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n := by
        have h1 : 0 ≤ (k : ℝ) - 1 := by linarith
        nlinarith [mul_nonneg h1 hΦ₂, mul_nonneg h1 hΦ₃]
      have e : (k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n) - Dc =
          2 * Φ₁ n + ((k : ℝ) - 1) * Φ₂ n + ((k : ℝ) - 1) * Φ₃ n := by rw [hDc]; ring
      linarith
    have hterm : gridStep s v K n * ∑ j ∈ Finset.range (K n),
        C * (cA * dDriftLinNg Cm n (gridTime s v K n j) k (Γ n) (Φ₁ n) (Φ₂ n) (Φ₃ n)) ≤
        (C * cA * Γ n * Γ n * Dc * X) * ∑ j ∈ Finset.range (K n),
          gridStep s v K n / Cm.eta n (gridTime s v K n j) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
      have hBj : (sz.Bctl n (gridTime s v K n j)) ^ k ≤ X :=
        pow_le_pow_left₀ (hBpos j hjK).le (hBmono j hjK) k
      have hηj := hη j hjK
      unfold dDriftLinNg
      calc gridStep s v K n * (C * (cA * (Γ n * Γ n *
              ((sz.Bctl n (gridTime s v K n j)) ^ k / Cm.eta n (gridTime s v K n j)) * Dc)))
          = (C * cA * Γ n * Γ n * Dc) * (gridStep s v K n *
              ((sz.Bctl n (gridTime s v K n j)) ^ k / Cm.eta n (gridTime s v K n j))) := by ring
        _ ≤ (C * cA * Γ n * Γ n * Dc) * (gridStep s v K n * (X / Cm.eta n (gridTime s v K n j))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hBj hηj.le) hΔ0)
              (by positivity)
        _ = (C * cA * Γ n * Γ n * Dc * X) * (gridStep s v K n / Cm.eta n (gridTime s v K n j)) := by
            ring
    have hpos : 0 ≤ C * cA * Γ n * Γ n * Dc * X := by positivity
    calc _ ≤ (C * cA * Γ n * Γ n * Dc * X) * ∑ j ∈ Finset.range (K n),
          gridStep s v K n / Cm.eta n (gridTime s v K n j) := hterm
      _ ≤ (C * cA * Γ n * Γ n * Dc * X) * Ls := mul_le_mul_of_nonneg_left hlog hpos
      _ ≤ (C * cA * Γ n * Γ n * ((k : ℝ) * (Φ₁ n + Φ₂ n + Φ₃ n)) * X) * Ls := by
          refine mul_le_mul_of_nonneg_right ?_ hLs0
          refine mul_le_mul_of_nonneg_right ?_ hX0'
          exact mul_le_mul_of_nonneg_left hDc_le (by positivity)
      _ = (C * cA * (k : ℝ) * (((sz.size n : ℕ) : ℝ) ^ ε₁) ^ 2 * Ls) *
            ((Φ₁ n + Φ₂ n + Φ₃ n) * X) := by rw [hΓ]; ring
      _ ≤ (((sz.size n : ℕ) : ℝ) ^ ε₀ / 6) * ((Φ₁ n + Φ₂ n + Φ₃ n) * X) :=
          mul_le_mul_of_nonneg_right H2
            (mul_nonneg (add_nonneg (add_nonneg hΦ₁ hΦ₂) hΦ₃) hX0')
  -- T3: the quadratic-variation term
  have T3 : ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
      (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * (sz.Bctl n (v n)) ^ k) +
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (sz.Bctl n (v n)) ^ k := by
    set X : ℝ := (sz.Bctl n (v n)) ^ k with hXdef
    set Ls : ℝ := (Cm.m n).im⁻¹ * Real.log ((sz.size n : ℕ) : ℝ) with hLsdef
    -- the summands
    have hcq : ∀ j ∈ Finset.range (K n),
        (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ) =
        (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * (gridStep s v K n *
            ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j))) +
          gridStep s v K n * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      intro j hj
      have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
      have hBj := hBpos j hjK
      have hηj := hη j hjK
      unfold cQVNZNg
      rw [Real.coe_toNNReal _ (by positivity)]
      ring
    have hsum : ∑ j ∈ Finset.range (K n), (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ) ≤
        ((k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2) +
          (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
      rw [Finset.sum_congr rfl hcq, Finset.sum_add_distrib]
      refine add_le_add ?_ ?_
      · rw [← Finset.mul_sum]
        have h1 : ∑ j ∈ Finset.range (K n), gridStep s v K n *
            ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j)) ≤
            X ^ 2 * ∑ j ∈ Finset.range (K n), gridStep s v K n / Cm.eta n (gridTime s v K n j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun j hj => ?_
          have hjK : j ≤ K n := (Finset.mem_range.1 hj).le
          have hB2 : (sz.Bctl n (gridTime s v K n j)) ^ (2 * k) ≤ X ^ 2 := by
            calc (sz.Bctl n (gridTime s v K n j)) ^ (2 * k) ≤ (sz.Bctl n (v n)) ^ (2 * k) :=
                  pow_le_pow_left₀ (hBpos j hjK).le (hBmono j hjK) _
              _ = X ^ 2 := by rw [hXdef, ← pow_mul, mul_comm]
          have hηj := hη j hjK
          calc gridStep s v K n * ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) /
                Cm.eta n (gridTime s v K n j))
              ≤ gridStep s v K n * (X ^ 2 / Cm.eta n (gridTime s v K n j)) :=
                mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB2 hηj.le) hΔ0
            _ = X ^ 2 * (gridStep s v K n / Cm.eta n (gridTime s v K n j)) := by ring
        have hc0 : 0 ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n := by positivity
        calc (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * ∑ j ∈ Finset.range (K n), gridStep s v K n *
              ((sz.Bctl n (gridTime s v K n j)) ^ (2 * k) / Cm.eta n (gridTime s v K n j))
            ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * (X ^ 2 * Ls) :=
              mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hlog (sq_nonneg _))) hc0
          _ = (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 := by ring
      · rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        calc (K n : ℝ) * (gridStep s v K n * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')))
            = ((K n : ℝ) * gridStep s v K n) * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
              ring
          _ ≤ 1 * ((k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) :=
              mul_le_mul_of_nonneg_right hKΔ1 (by positivity)
          _ = (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := one_mul _
    have ha0 : 0 ≤ (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 := by positivity
    have hb0 : 0 ≤ (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') := by positivity
    have hs1 := Real.sqrt_le_sqrt hsum
    have hs2 : Real.sqrt (((k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2) +
          (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'')) ≤
        C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X +
          C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by
      refine (nqBudget_sqrt_add_le ha0 hb0).trans (le_of_eq ?_)
      have e1 : (k : ℝ) * C ^ 2 * Γ n ^ 2 * Λ n * Ls * X ^ 2 =
          (C * Γ n * X) ^ 2 * (((k : ℝ) * Ls) * Λ n) := by ring
      have e2 : (k : ℝ) * C ^ 2 * ((sz.W n : ℕ) : ℝ) ^ (-D'') =
          C ^ 2 * ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')) := by ring
      have hA0 : 0 ≤ C * Γ n * X := by positivity
      rw [e1, e2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC.le]
      ring
    have hsΛ : Real.sqrt (Λ n) = Λ n ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (Λ n)
    have hNe : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ εq := Real.rpow_nonneg hN0.le _
    have k1 : ((sz.size n : ℕ) : ℝ) ^ εq *
        (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * (Λ n ^ ((1 : ℝ) / 2) * X) := by
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) =
          (((sz.size n : ℕ) : ℝ) ^ εq * (C * ((sz.size n : ℕ) : ℝ) ^ ε₁ *
            Real.sqrt ((k : ℝ) * Ls))) * (Λ n ^ ((1 : ℝ) / 2) * X) := by
        rw [hsΛ, hΓ]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right H3 (mul_nonneg (by linarith) hX0')
    have k2 : ((sz.size n : ℕ) : ℝ) ^ εq * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) ≤
        ((sz.size n : ℕ) : ℝ) ^ ε₀ / 12 * X := by
      refine qtNZ_absorb hNk (by positivity) ?_ hXN
      have e : ((sz.size n : ℕ) : ℝ) ^ εq *
          (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) * ((sz.size n : ℕ) : ℝ) ^ k =
          ((sz.size n : ℕ) : ℝ) ^ εq * (((sz.size n : ℕ) : ℝ) ^ k *
            (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D'')))) := by ring
      rw [e]; exact H4
    calc ((sz.size n : ℕ) : ℝ) ^ εq * Real.sqrt (∑ j ∈ Finset.range (K n),
          (cQVNZNg Cm s v K n k C (Γ n) (Λ n) D'' j : ℝ))
        ≤ ((sz.size n : ℕ) : ℝ) ^ εq * (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X +
            C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) :=
          mul_le_mul_of_nonneg_left (hs1.trans hs2) hNe
      _ = ((sz.size n : ℕ) : ℝ) ^ εq * (C * Γ n * (Real.sqrt ((k : ℝ) * Ls) * Real.sqrt (Λ n)) * X) +
          ((sz.size n : ℕ) : ℝ) ^ εq * (C * Real.sqrt ((k : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-D''))) := by
          ring
      _ ≤ _ := add_le_add k1 k2
  -- T4, T5
  have T4 : ((sz.size n : ℕ) : ℝ) ^ (-D_Y) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k :=
    qtNZ_absorb hNk (by positivity) ((mul_comm _ _).trans_le H5) hXN
  have T5 : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
        stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k)) ≤
      ((sz.size n : ℕ) : ℝ) ^ ε₀ / 6 * (sz.Bctl n (v n)) ^ k := by
    have e : ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k * (cA *
        stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
          (gridStep s v K n)
          (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k)) =
        cA * ∑ j ∈ Finset.range (K n), (1 + (1 - gridTime s v K n (K n))⁻¹) ^ k *
          stepErrNg Cm.toFlowFM n k (gridTime s v K n j) (gridTime s v K n (j + 1))
            (gridStep s v K n)
            (((sz.size n : ℕ) : ℝ) ^ τK * (Cm.eta n (gridTime s v K n (j + 1)))⁻¹ ^ k) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    refine (mul_le_mul_of_nonneg_left hR hcA).trans ?_
    exact qtNZ_absorb hNk (by positivity) ((mul_comm _ _).trans_le (by linarith [H6])) hXN
  unfold assembledRHSNZNg
  exact qtNZ_final hP0 hX0' hΛr1 hΦ₁ hΦ₂ hΦ₃ T1 T2 T3 T4 T5


end Budget

/-! ## 7. Compiled nonempty instances (`d = 3`, band carriers; target 9)

D1 and `nz_hkerg` at `szB` (`L = 4`, `lam ≡ 1`, `E ≡ 0`, `k = 3`, `σ = (+,-,+)`, `A = I_diff(σ) = {0, 1}`, window `u_i = 15/16 + i/32`, `K = 1`, `X = Q^{(A)} δ₀ ≠ 0`),
the window of the case-(ii) grid (`1 - g²/L² = 15/16`).  `nz_hdriftNg`, `subGaussStop_nzNg`, `yMomentBounds_nzNg`, `budgetNZNg` at the band carrier `bandStep2Mat sz0 Einst`
(`L = 4`, `W = 32`, `N = 2^21`, `E ≡ 1/2`, grid `s ≡ 0`, `v ≡ 1/32`, `K ≡ 4`, `k = 3`, levels `(Γ, Λ, Φ) = (4, 3, 1)`, `(Φ₁, Φ₂, Φ₃) = (1, 12, 1)`, `τ' = 1/5`, `D' = 6`,
`D'' = 5`; data and private numerics of `QtNonzeroInst`, `NQLinGen` by `open private`).  No deterministic hypothesis is left open. -/

/-! ### The band carrier `bandStep2Mat sz0 Einst` (`n = 0`) -/

end RBM.BA

end
