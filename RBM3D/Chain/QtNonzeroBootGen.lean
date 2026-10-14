/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QtNonzeroFlowGen
import RBM3D.Chain.QtBootGen
import RBM3D.Chain.ZeroModeGen
import RBM3D.Chain.Step6KitGen
import RBM3D.Induction.QtNonzeroBoot

/-!
# The case-(ii) round and the bootstrap over the carrier family: `stOeqQtNZgL'_of` (U3s4 row c, file 2; ticket T2505)

Generic form of `Induction/QtNonzeroBoot.lean` §5-§6 (not edited) over a carrier family `(law, Flow, mkM, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper: arXiv:2507.20274,
`lem:STOeq_Qt_nonzero` (`3_5:1561-1572`), proof `3_5:1889-1933`: `lem: newPQ` at `A = ∅` (`(eq:expandQAempty)` `3_5:1893`), the bound before "solving which" `3_5:1916-1930`.
Composition, no new mathematics (`7_8:1841`).

* **Target 13** `stXiRoundNZgL_of`: the case-(ii) round `STXiRoundgL'` over `STIngRgL d STCaseII` from the uniform projected endpoint `STNZConclgL''` (target 12): `zeroModeCalc_LK_expansion_emptyg`
  under `ZeroModeGen_WardCls` (a field of `B45Gen_Facts`) writes `(𝓛-𝒦)^{(n_)}_{v,σ,a}` as `(Q^{(I_diff σ)}(𝓛-𝒦)^{(n_)})_{σ,a}` plus lower terms `k_α ∈ [1, n_-1]`; the first is
  `STNZConclgL''` at the envelope controls, every lower term is `≤ C Ξ̂^{(𝓛-𝒦)}_{v,k_α}` with `(N η_u)⁻¹ ≤ κm⁻¹ B_u` (`DecayGen_Spec`, `QtBootGen_inv_one_sub_le`: the private twin of `expWII_inv_Neta_le`).
* **Target 14** `stOeqQtNZgL'_of` (conclusion = the merged T2491 pin `STOeqQtNZgL'`, binding) = `stXiBootRgL'_of_round d STCaseII` of row a applied to target 13.
* **Target 15 (part)** the band re-derivations `stOeqQtNZgL'_band`, `stOeqQtNZ'_holds_of_gen` (and `stXiRoundNZ_holds_of_gen`) and compiled nonempty instances at `d = 3`.

The model-free privates of `QtNonzeroBoot` (the `STbootRHS` facts) are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private qtBoot_sharp_one_le qtBoot_sharp_le qtBoot_sharp_mono qtBoot_bootRHS_mono qtBoot_bootRHS_one_le qtBoot_bootRHS_two_le_one qtBoot_XLK_le_bootRHS
  from RBM3D.Induction.QtNonzeroBoot

open private NQEndFlowGen_prec_of_le_right NQEndFlowGen_isProb from RBM3D.Chain.NQEndFlowGen

open private QtLiftGen_sharp_prec from RBM3D.Chain.QtXiRoundLiftGen

open private QtBootGen_inv_one_sub_le QtBootGen_flow_abs_le from RBM3D.Chain.QtBootGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqFlowSharp)

/-! ## 1. `≺` algebra for the combination over a law (private copies of `QtNonzeroBoot` §5) -/

section PrecAlgebra

variable {d : ℕ}

/-- **The supremum over a finite inner index** (band `qtBoot_prec_sup`): if `f(q, p) ≺ ζ(q)` over the product `(q, p)` (`P n` a finite non-empty type), then `max_p f(q, p) ≺ ζ(q)` over `q`. -/
private theorem QtNZBootGen_prec_sup {sz : Sizes d} {μ : Measure sz.SeqΩ} {Q P : ℕ → Type*} [∀ n, Fintype (P n)]
    (hne : ∀ n, (Finset.univ : Finset (P n)).Nonempty)
    {f : ∀ n, Q n → P n → sz.SeqΩ → ℝ} {ζ : ∀ n, Q n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ (U := fun n => Q n × P n) (fun n x ω => f n x.1 x.2 ω) (fun n x ω => ζ n x.1 ω)) :
    PrecL sz μ (U := Q) (fun n q ω => (Finset.univ : Finset (P n)).sup' (hne n) (fun p => f n q p ω)) ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine le_trans (measure_mono ?_) hn
  intro ω hω
  obtain ⟨q, hq⟩ := hω
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' (hne n) (fun p => f n q p ω)
  refine ⟨(q, p), ?_⟩
  change ((sz.size n : ℕ) : ℝ) ^ τ * ζ n q ω < f n q p ω
  rw [← hp]
  exact hq

/-- `ξ ≤ ξ₁ + ξ₂ + ζ`, `ξ₁ ≺ ζ`, `ξ₂ ≺ ζ`, `ζ ≥ 0` give `ξ ≺ ζ` (band `qtBoot_prec_of_add_le`). -/
private theorem QtNZBootGen_prec_of_add_le {sz : Sizes d} {μ : Measure sz.SeqΩ} (hsz : sz.SizeTendsto) {U : ℕ → Type*}
    {ξ ξ₁ ξ₂ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (h₁ : PrecL sz μ ξ₁ ζ) (h₂ : PrecL sz μ ξ₂ ζ) (hle : ∀ n u ω, ξ n u ω ≤ ξ₁ n u ω + ξ₂ n u ω + ζ n u ω) :
    PrecL sz μ ξ ζ := by
  have hsize := sz.tendsto_size hsz
  refine StochDomAt.of_subset_union hsize h₁ h₂ fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (RBM.eventually_le_rpow 3 (half_pos hτ))] with n h3
  rintro ω ⟨u, hu⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  have hhalf : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) =
      ((sz.size n : ℕ) : ℝ) ^ τ := UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ
  have hζ0 := hζ n u ω
  have h1 := hno.1 u
  have h2 := hno.2 u
  have h4 := hle n u ω
  have hP : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by linarith
  nlinarith [mul_nonneg hP hζ0, mul_le_mul_of_nonneg_right h3 hζ0]

/-- A finite sum of `≺ ζ` families is `≺ ζ` (band `qtBoot_prec_sum`; induction; `ξ₁ + ξ₂ ≤ ξ₁ + ξ₂ + ζ`). -/
private theorem QtNZBootGen_prec_sum {sz : Sizes d} {μ : Measure sz.SeqΩ} (hsz : sz.SizeTendsto) {U : ℕ → Type*} {ι : Type*}
    (S : Finset ι) {f : ι → ∀ n, U n → sz.SeqΩ → ℝ} {ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (hζ : ∀ n u ω, 0 ≤ ζ n u ω) (h : ∀ i ∈ S, PrecL sz μ (f i) ζ) :
    PrecL sz μ (fun n u ω => ∑ i ∈ S, f i n u ω) ζ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact StochDomAt.of_le_left (fun n u ω => by simpa using hζ n u ω) (StochDomAt.refl (sz.tendsto_size hsz) hζ)
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self a S)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine QtNZBootGen_prec_of_add_le hsz hζ h1 h2 fun n u ω => ?_
    rw [Finset.sum_insert ha]
    linarith [hζ n u ω]

end PrecAlgebra

/-! ## 2. The lower terms of `(eq:expandQAempty)` over a carrier -/

section LowerTerms

variable {d : ℕ}

/-- **`(2 N η_v)⁻¹ ≤ κm⁻¹ B_v`** (band `qtBoot_inv_Neta`, `QtNonzeroBoot.lean:744`; the twin of `expWII_inv_Neta_le`, `ExpWardII:303`): `η_v = (1 - v) Im m ≥ (1 - v) κm` (`DecayGen_Spec`) and
`(1 - v)⁻¹ ≤ N B_v` (`QtBootGen_inv_one_sub_le`), `v < 1`: the `(Nη_t)^{-1} ≤ C W^{-d}B_{t,0}` of `3_5:1925`. -/
private theorem QtNZBootGen_inv_Neta {sz : Sizes d} (Cf : FlowFM sz) (n : ℕ) {κm v : ℝ} (hspec : DecayGen_Spec Cf κm) (hv : v < 1) :
    (2 * (((sz.size n : ℕ) : ℝ) * Cf.eta n v))⁻¹ ≤ κm⁻¹ * sz.Bctl n v := by
  obtain ⟨hκm, hIm, hηeq⟩ := hspec
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hm0 : 0 < (Cf.m n).im := lt_of_lt_of_le hκm (hIm n)
  have h1v : 0 < 1 - v := by linarith
  have hB : 0 ≤ sz.Bctl n v := (STBctl_pos sz n hv).le
  have h1 := QtBootGen_inv_one_sub_le sz n hv
  have h2 : ((Cf.m n).im)⁻¹ ≤ κm⁻¹ := inv_anti₀ hκm (hIm n)
  rw [hηeq]
  have e : (2 * (((sz.size n : ℕ) : ℝ) * ((1 - v) * (Cf.m n).im)))⁻¹ =
      2⁻¹ * (((sz.size n : ℕ) : ℝ)⁻¹ * ((1 - v)⁻¹ * ((Cf.m n).im)⁻¹)) := by
    simp only [mul_inv]
  rw [e]
  have hNinv : 0 ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := inv_nonneg.2 hN.le
  calc 2⁻¹ * (((sz.size n : ℕ) : ℝ)⁻¹ * ((1 - v)⁻¹ * ((Cf.m n).im)⁻¹))
      ≤ 1 * (((sz.size n : ℕ) : ℝ)⁻¹ * ((((sz.size n : ℕ) : ℝ) * sz.Bctl n v) * κm⁻¹)) := by
        refine mul_le_mul (by norm_num) (mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (inv_nonneg.2 hm0.le)
          (mul_nonneg hN.le hB)) hNinv) (by positivity) (by norm_num)
    _ = κm⁻¹ * sz.Bctl n v := by field_simp

/-- **One lower term of `(eq:expandQAempty)`, divided by `B_v^{n_}`** (band `qtBoot_term_le`, `QtNonzeroBoot.lean:767`): with `1 ≤ k ≤ n_ - 1` (`k_α = 1` included, paper-delta candidate `T2304b`),
`|ξ| (2Nη_v)^{-(n_-k)} |(Q^{(A')}(𝓛-𝒦)^{(k)}_{v,σ'})(a ∘ ι)| / B_v^{n_} ≤ |ξ| 2^k κm^{-(n_-k)} Ξ̂^{(𝓛-𝒦)}_{v,k}`: `(normQA2)` `‖Q^{(A')} T‖ ≤ 2^{#A'} ‖T‖` with `#A' ≤ k`,
`‖T‖ ≤ max|(𝓛-𝒦)^{(k)}_v| ≤ B_v^k Ξ̂_{v,k}`, and `(2Nη_v)⁻¹ ≤ κm⁻¹ B_v`: the powers of `B` cancel exactly (`(n_-k) + k = n_`). -/
private theorem QtNZBootGen_term_le {sz : Sizes d} (Cf : FlowFM sz) (n : ℕ) {κm v : ℝ} (hspec : DecayGen_Spec Cf κm)
    (hv1 : v < 1) (ω : sz.SeqΩ) {n_ k : ℕ} (hkn : k + 1 ≤ n_) (ξc : ℤ) (σ' : Fin k → Bool)
    (ι : Fin k → Fin n_) (A' : Finset (Fin k)) (a : Fin n_ → Zd d (sz.L n)) :
    ‖(ξc : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n v : ℂ)) ^ (n_ - k) *
        zeroModeSet d (sz.L n) A' (fun a' => Cf.L n v σ' a' ω - Cf.K n v σ' a') (a ∘ ι)‖ /
        (sz.Bctl n v) ^ n_ ≤
      (|(ξc : ℝ)| * 2 ^ k * (κm⁻¹) ^ (n_ - k)) * STXiLKg Cf n v k ω := by
  have hη : 0 < Cf.eta n v := by
    obtain ⟨hκm, hIm, hηeq⟩ := hspec
    rw [hηeq]
    exact mul_pos (by linarith) (lt_of_lt_of_le hκm (hIm n))
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hB : 0 < sz.Bctl n v := STBctl_pos sz n hv1
  have hmk : (n_ - k) + k = n_ := by omega
  have hinv := QtNZBootGen_inv_Neta Cf n hspec hv1
  have hκm : 0 < κm := hspec.1
  -- the scalar
  have hnorm : ‖(ξc : ℂ) / (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n v : ℂ)) ^ (n_ - k)‖ =
      |(ξc : ℝ)| * ((2 * (((sz.size n : ℕ) : ℝ) * Cf.eta n v))⁻¹) ^ (n_ - k) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast, Complex.norm_real,
      Complex.norm_two, Complex.norm_intCast, Real.norm_of_nonneg hη.le, div_eq_mul_inv, ← inv_pow]
    congr 3
    ring
  -- `max|(𝓛-𝒦)^{(k)}|` and `Ξ̂`
  have hMdef : STmaxLKg Cf n v k ω = (STXiLKg Cf n v k ω - 1) * (sz.Bctl n v) ^ k := by
    unfold STXiLKg
    field_simp
    ring
  have hM0 : 0 ≤ STmaxLKg Cf n v k ω :=
    Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n))))) (norm_nonneg _)
  have hTnorm : ‖fun a' : Fin k → Zd d (sz.L n) => Cf.L n v σ' a' ω - Cf.K n v σ' a'‖ ≤ STmaxLKg Cf n v k ω := by
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun b => ?_
    exact Finset.le_sup' (fun p : (Fin k → Bool) × (Fin k → Zd d (sz.L n)) =>
      ‖Cf.L n v p.1 p.2 ω - Cf.K n v p.1 p.2‖) (Finset.mem_univ (σ', b))
  have hQ : ‖zeroModeSet d (sz.L n) A' (fun a' => Cf.L n v σ' a' ω - Cf.K n v σ' a') (a ∘ ι)‖ ≤
      2 ^ k * STmaxLKg Cf n v k ω := by
    have h1 := norm_le_pi_norm (zeroModeSet d (sz.L n) A' (fun a' => Cf.L n v σ' a' ω - Cf.K n v σ' a')) (a ∘ ι)
    have h2 := norm_zeroModeSet_le A' (fun a' => Cf.L n v σ' a' ω - Cf.K n v σ' a')
    have h3 : (2 : ℝ) ^ A'.card ≤ 2 ^ k := by
      refine pow_le_pow_right₀ (by norm_num) ?_
      simpa using Finset.card_le_univ A'
    calc _ ≤ _ := h1
      _ ≤ 2 ^ A'.card * ‖fun a' : Fin k → Zd d (sz.L n) => Cf.L n v σ' a' ω - Cf.K n v σ' a'‖ := h2
      _ ≤ 2 ^ k * STmaxLKg Cf n v k ω := mul_le_mul h3 hTnorm (norm_nonneg _) (by positivity)
  -- assemble
  rw [norm_mul, hnorm, div_le_iff₀ (pow_pos hB _)]
  have hpow : ((2 * (((sz.size n : ℕ) : ℝ) * Cf.eta n v))⁻¹) ^ (n_ - k) ≤ (κm⁻¹ * sz.Bctl n v) ^ (n_ - k) :=
    pow_le_pow_left₀ (inv_nonneg.2 (by positivity)) hinv _
  have hXk : STmaxLKg Cf n v k ω ≤ (sz.Bctl n v) ^ k * STXiLKg Cf n v k ω := by
    rw [hMdef]; nlinarith [pow_pos hB k]
  have hBn : (sz.Bctl n v) ^ n_ = (sz.Bctl n v) ^ (n_ - k) * (sz.Bctl n v) ^ k := by
    rw [← pow_add, hmk]
  calc |(ξc : ℝ)| * ((2 * (((sz.size n : ℕ) : ℝ) * Cf.eta n v))⁻¹) ^ (n_ - k) *
        ‖zeroModeSet d (sz.L n) A' (fun a' => Cf.L n v σ' a' ω - Cf.K n v σ' a') (a ∘ ι)‖
      ≤ |(ξc : ℝ)| * ((κm⁻¹ * sz.Bctl n v) ^ (n_ - k)) *
        (2 ^ k * ((sz.Bctl n v) ^ k * STXiLKg Cf n v k ω)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hpow (abs_nonneg _)) ?_ (norm_nonneg _) (by positivity)
        exact hQ.trans (mul_le_mul_of_nonneg_left hXk (by positivity))
    _ = (|(ξc : ℝ)| * 2 ^ k * (κm⁻¹) ^ (n_ - k)) * STXiLKg Cf n v k ω * (sz.Bctl n v) ^ n_ := by
        rw [hBn, mul_pow]; ring

end LowerTerms

/-! ## 3. Target 13: the case-(ii) round from the uniform projected endpoint -/

section Combine

variable {d : ℕ}

/-- **The case-(ii) round from the uniform projected endpoint at one carrier** (band `qtBoot_round_of_NZ`, `QtNonzeroBoot.lean:845`; `lem:STOeq_Qt_nonzero`, proof `3_5:1889-1933`): at the carrier data
`DecayGen_Spec`, `ZeroModeGen_WardCls`, `0 ≤ s`, `t < 1`, `STNZConclgL''` (the uniform pin for `Q^{(I_diff σ)}(𝓛-𝒦)`) gives `STXiRoundgL'`: `lem: newPQ` at `A = ∅`
(`zeroModeCalc_LK_expansion_emptyg`, data chosen per `σ`) writes `(𝓛-𝒦)^{(n_)}_{v,σ,a}` as `(Q^{(I_diff σ)}(𝓛-𝒦)^{(n_)})_{σ,a}` plus lower terms; the first is `STNZConclgL''` at the envelope
controls (compared with the controls of the round on the pairs), every lower term `k_α ∈ [1, n_-1]` is `≤ C_{n_} Ξ̂_{v,k_α}` (`QtNZBootGen_term_le`) and `Ξ̂_{v,k_α} ≺ XLK k_α u ≤ STbootRHS 1`; the finite
max over `(σ, a)` and the finite sums are `≺` algebra.  Paper-delta candidate `T2304b` (the lower terms follow from the hypotheses, `k_α = 1` included; no averaged law `(eq:kalpha1)`). -/
private theorem QtNZBootGen_round_of_NZ {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto)
    {κm : ℝ} (hspec : DecayGen_Spec Cf κm) (hWard : ZeroModeGen_WardCls sz Cf) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hNZ : STNZConclgL'' Cf μ s t) : STXiRoundgL' Cf μ s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsize := sz.tendsto_size hsz
  -- the envelope controls and the uniform endpoint at them
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => qtBoot_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => qtBoot_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cf n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm hl =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLg Cf n w m ω) XL m hXL (hXLp m hm hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cf n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm hm' =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLKg Cf n w m ω) XLK m hXLK (hXLKp m hm hm')
  have hNZ' := hNZ n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  -- positivity and the control `ζ`
  have hBs : ∀ n, ∀ q : STPair s t n, 0 < sz.Bctl n (s n) := fun n q =>
    STBctl_pos sz n (q.2.1.trans (q.2.2.1.trans q.2.2.2) |>.trans_lt (ht1 n))
  have hζ1 : ∀ (n : ℕ) (q : STPair s t n),
      1 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p := by
    intro n q
    have hu1 : q.1.2 < 1 := q.2.2.2.trans_lt (ht1 n)
    have h0 : 0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 :=
      mul_nonneg (Real.rpow_nonneg (STBctl_pos sz n hu1).le _) (zero_le_one.trans (hXLK n_ n q.1.2))
    have := qtBoot_bootRHS_one_le (lo := 1) (XL := fun m => XL m n q.1.2) (XLK := fun m => XLK m n q.1.2)
      (B := sz.Bctl n (s n)) (k := n_) (p := p) (by omega) (fun m => hXL m n q.1.2)
      (fun m => zero_le_one.trans (hXLK m n q.1.2)) (hBs n q).le
    linarith
  have hζ0 : ∀ (n : ℕ) (q : STPair s t n) (ω : sz.SeqΩ),
      0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p :=
    fun n q ω => zero_le_one.trans (hζ1 n q)
  -- (A) the first term, over the product `(q, σ, a)`
  have hT1 : PrecL sz μ (U := fun n => STPair s t n × ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n))))
      (fun n x ω => ‖zeroModeSet d (sz.L n) (STIdiff x.2.1)
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n x.1.1.1 x.2.1 b ω - Cf.K n x.1.1.1 x.2.1 b) x.2.2‖ /
        (sz.Bctl n x.1.1.1) ^ n_)
      (fun n x _ => (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 +
        STbootRHS 1 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p) := by
    have h := StochDomAt.precomp_param
      (V := fun n => STPair s t n × ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))) hNZ'
      (fun n x => (⟨x.1.1.1, x.1.2.1, x.1.2.2.1.trans x.1.2.2.2⟩,
        ⟨(x.2.1, STIdiff x.2.1), Finset.Subset.refl _⟩, x.2.2))
    refine NQEndFlowGen_prec_of_le_right h fun n x ω => ?_
    have hsv : s n ≤ x.1.1.1 := x.1.2.1
    have hvu : x.1.1.1 ≤ x.1.1.2 := x.1.2.2.1
    have hut : x.1.1.2 ≤ t n := x.1.2.2.2
    have hu1 : x.1.1.2 < 1 := hut.trans_lt (ht1 n)
    have hv1 : x.1.1.1 < 1 := hvu.trans_lt hu1
    have hBsn : 0 < sz.Bctl n (s n) := STBctl_pos sz n (hsv.trans_lt hv1)
    have hBv : 0 < sz.Bctl n x.1.1.1 := STBctl_pos sz n hv1
    have hBvu : sz.Bctl n x.1.1.1 ≤ sz.Bctl n x.1.1.2 := STBctl_mono sz n hvu hu1
    have hsharp : ∀ X : ℕ → ℕ → ℝ → ℝ, (∀ m n u, 1 ≤ X m n u) → ∀ m,
        nqFlowSharp t X m n x.1.1.1 ≤ X m n x.1.1.2 := fun X hX m =>
      (qtBoot_sharp_mono t X hX m n x.1.1.1 x.1.1.2 hvu hut).trans (qtBoot_sharp_le t X hX m n x.1.1.2)
    have h1 : (sz.Bctl n x.1.1.1) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n x.1.1.1 ≤
        (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 :=
      mul_le_mul (Real.rpow_le_rpow hBv.le hBvu (by norm_num)) (hsharp XLK hXLK n_)
        (zero_le_one.trans (qtBoot_sharp_one_le t XLK n_ n x.1.1.1)) (Real.rpow_nonneg (hBv.le.trans hBvu) _)
    have h2 : STbootRHS 2 (fun m => nqFlowSharp t XL m n x.1.1.1) (fun m => nqFlowSharp t XLK m n x.1.1.1)
          (sz.Bctl n (s n)) n_ p ≤
        STbootRHS 2 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p :=
      qtBoot_bootRHS_mono 2 _ _ _ _ _ n_ p hBsn
        (fun m => zero_le_one.trans (qtBoot_sharp_one_le t XL m n x.1.1.1))
        (fun m => zero_le_one.trans (qtBoot_sharp_one_le t XLK m n x.1.1.1))
        (fun m => hsharp XL hXL m) (fun m => hsharp XLK hXLK m)
    have h3 := qtBoot_bootRHS_two_le_one (XL := fun m => XL m n x.1.1.2) (XLK := fun m => XLK m n x.1.1.2)
      (B := sz.Bctl n (s n)) (n_ := n_) (p := p) (fun m => zero_le_one.trans (hXLK m n x.1.1.2))
    change (sz.Bctl n x.1.1.1) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n x.1.1.1 +
        STbootRHS 2 (fun m => nqFlowSharp t XL m n x.1.1.1) (fun m => nqFlowSharp t XLK m n x.1.1.1)
          (sz.Bctl n (s n)) n_ p ≤
      (sz.Bctl n x.1.1.2) ^ (1 / 6 : ℝ) * XLK n_ n x.1.1.2 +
        STbootRHS 1 (fun m => XL m n x.1.1.2) (fun m => XLK m n x.1.1.2) (sz.Bctl n (s n)) n_ p
    linarith
  -- (B) the finite maximum over `(σ, a)`
  have hne : ∀ n, (Finset.univ : Finset ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))).Nonempty := fun n =>
    ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
  have hT2 := QtNZBootGen_prec_sup (sz := sz) (μ := μ) (Q := fun n => STPair s t n)
    (P := fun n => (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n))) hne
    (f := fun n q p ω => ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n q.1.1 p.1 b ω - Cf.K n q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_)
    (ζ := fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p) hT1
  -- (C) the data of `lem: newPQ` at `A = ∅`, per `σ`
  choose ℓ k ξc σ' ι A' hk hA hexp using fun σ : Fin n_ → Bool => zeroModeCalc_LK_expansion_emptyg d n_ σ
  set cF : ∀ σ : Fin n_ → Bool, Fin (ℓ σ) → ℝ := fun σ α =>
    |(ξc σ α : ℝ)| * 2 ^ (k σ α) * (κm⁻¹) ^ (n_ - k σ α) with hcF
  have hκm : 0 < κm := hspec.1
  have hcF0 : ∀ σ α, 0 ≤ cF σ α := fun σ α => by positivity
  -- (D) the lower terms, summed
  have hF : ∀ σ : Fin n_ → Bool, PrecL sz μ (U := STPair s t)
      (fun n q ω => ∑ α : Fin (ℓ σ), cF σ α * STXiLKg Cf n q.1.1 (k σ α) ω)
      (fun n q _ => (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
        STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p) := by
    intro σ
    refine QtNZBootGen_prec_sum hsz Finset.univ hζ0 fun α _ => ?_
    have hkα : 1 ≤ k σ α ∧ k σ α + 1 ≤ n_ := hk σ α
    have h1 := hXLKp (k σ α) hkα.1 (by omega)
    have h2 := StochDomAt.const_mul_left hsize (c := cF σ α) (hcF0 σ α)
      (fun (n : ℕ) (q : STPair s t n) (ω : sz.SeqΩ) => zero_le_one.trans (hXLK (k σ α) n q.1.2)) h1
    refine NQEndFlowGen_prec_of_le_right h2 fun n q ω => ?_
    have hu1 : q.1.2 < 1 := q.2.2.2.trans_lt (ht1 n)
    have hb := qtBoot_XLK_le_bootRHS (XL := fun m => XL m n q.1.2) (XLK := fun m => XLK m n q.1.2)
      (B := sz.Bctl n (s n)) (n_ := n_) (p := p) hkα.1 (by omega)
      (fun m => zero_le_one.trans (hXL m n q.1.2)) (fun m => zero_le_one.trans (hXLK m n q.1.2)) (hBs n q).le
    have h0 : 0 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 :=
      mul_nonneg (Real.rpow_nonneg (STBctl_pos sz n hu1).le _) (zero_le_one.trans (hXLK n_ n q.1.2))
    change XLK (k σ α) n q.1.2 ≤ (sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p
    linarith
  have hG := QtNZBootGen_prec_sum hsz (Finset.univ : Finset (Fin n_ → Bool)) hζ0 fun σ _ => hF σ
  -- (E) the pointwise inequality
  refine QtNZBootGen_prec_of_add_le hsz hζ0 hT2 hG fun n q ω => ?_
  have hsq : s n ≤ q.1.1 := q.2.1
  have hvt : q.1.1 ≤ t n := q.2.2.1.trans q.2.2.2
  have hv0 : 0 ≤ q.1.1 := (hs n).trans hsq
  have hv1 : q.1.1 < 1 := hvt.trans_lt (ht1 n)
  have hBv : 0 < sz.Bctl n q.1.1 := STBctl_pos sz n hv1
  set ξ₁ : ℝ := (Finset.univ : Finset ((Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)))).sup' (hne n)
    (fun p => ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n q.1.1 p.1 b ω - Cf.K n q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_) with hξ₁
  set G : ℝ := ∑ σ : Fin n_ → Bool, ∑ α : Fin (ℓ σ), cF σ α * STXiLKg Cf n q.1.1 (k σ α) ω with hGdef
  have hXi0 : ∀ σ α, 0 ≤ cF σ α * STXiLKg Cf n q.1.1 (k σ α) ω := by
    intro σ α
    refine mul_nonneg (hcF0 σ α) ?_
    unfold STXiLKg
    have : 0 ≤ STmaxLKg Cf n q.1.1 (k σ α) ω / (sz.Bctl n q.1.1) ^ (k σ α) :=
      div_nonneg (Finset.le_sup'_of_le _ (Finset.mem_univ ((fun _ => true), (fun _ => (0 : Zd d (sz.L n)))))
        (norm_nonneg _)) (pow_nonneg hBv.le _)
    linarith
  -- per `(σ, a)`: `‖(𝓛-𝒦)_{σ,a}‖ / B^{n_} ≤ ξ₁ + G`
  have hpt : ∀ p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)),
      ‖Cf.L n q.1.1 p.1 p.2 ω - Cf.K n q.1.1 p.1 p.2‖ / (sz.Bctl n q.1.1) ^ n_ ≤ ξ₁ + G := by
    rintro ⟨σ, a⟩
    have hex := hexp σ sz Cf hWard n q.1.1 hv0 hv1 ω a
    have h1 : ‖Cf.L n q.1.1 σ a ω - Cf.K n q.1.1 σ a‖ ≤
        ‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => Cf.L n q.1.1 σ a' ω - Cf.K n q.1.1 σ a') a‖ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => Cf.L n q.1.1 (σ' σ α) a' ω - Cf.K n q.1.1 (σ' σ α) a') (a ∘ ι σ α)‖ := by
      rw [hex]
      exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    have hfirst : ‖zeroModeSet d (sz.L n) (STIdiff σ)
          (fun a' => Cf.L n q.1.1 σ a' ω - Cf.K n q.1.1 σ a') a‖ / (sz.Bctl n q.1.1) ^ n_ ≤ ξ₁ :=
      Finset.le_sup' (fun p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)) =>
        ‖zeroModeSet d (sz.L n) (STIdiff p.1)
          (fun b : Fin n_ → Zd d (sz.L n) => Cf.L n q.1.1 p.1 b ω - Cf.K n q.1.1 p.1 b) p.2‖ /
        (sz.Bctl n q.1.1) ^ n_) (Finset.mem_univ (σ, a))
    have hlower : ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => Cf.L n q.1.1 (σ' σ α) a' ω - Cf.K n q.1.1 (σ' σ α) a') (a ∘ ι σ α)‖ /
          (sz.Bctl n q.1.1) ^ n_ ≤ G := by
      calc _ ≤ ∑ α : Fin (ℓ σ), cF σ α * STXiLKg Cf n q.1.1 (k σ α) ω := by
            refine Finset.sum_le_sum fun α _ => ?_
            exact QtNZBootGen_term_le Cf n hspec hv1 ω (hk σ α).2 (ξc σ α) (σ' σ α) (ι σ α) (A' σ α) a
        _ ≤ G := Finset.single_le_sum (f := fun σ : Fin n_ → Bool =>
            ∑ α : Fin (ℓ σ), cF σ α * STXiLKg Cf n q.1.1 (k σ α) ω)
          (fun σ _ => Finset.sum_nonneg fun α _ => hXi0 σ α) (Finset.mem_univ σ)
    calc ‖Cf.L n q.1.1 σ a ω - Cf.K n q.1.1 σ a‖ / (sz.Bctl n q.1.1) ^ n_
        ≤ (‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => Cf.L n q.1.1 σ a' ω - Cf.K n q.1.1 σ a') a‖ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => Cf.L n q.1.1 (σ' σ α) a' ω - Cf.K n q.1.1 (σ' σ α) a') (a ∘ ι σ α)‖) /
          (sz.Bctl n q.1.1) ^ n_ := div_le_div_of_nonneg_right h1 (pow_nonneg hBv.le _)
      _ = ‖zeroModeSet d (sz.L n) (STIdiff σ)
            (fun a' => Cf.L n q.1.1 σ a' ω - Cf.K n q.1.1 σ a') a‖ / (sz.Bctl n q.1.1) ^ n_ +
          ∑ α : Fin (ℓ σ), ‖(ξc σ α : ℂ) /
              (2 * Complex.I * ((sz.size n : ℕ) : ℂ) * (Cf.eta n q.1.1 : ℂ)) ^ (n_ - k σ α) *
            zeroModeSet d (sz.L n) (A' σ α)
              (fun a' => Cf.L n q.1.1 (σ' σ α) a' ω - Cf.K n q.1.1 (σ' σ α) a') (a ∘ ι σ α)‖ /
          (sz.Bctl n q.1.1) ^ n_ := by rw [add_div, Finset.sum_div]
      _ ≤ ξ₁ + G := add_le_add hfirst hlower
  -- the maximum over `(σ, a)` and `Ξ̂ = 1 + max / B^{n_}`
  have hmax : STmaxLKg Cf n q.1.1 n_ ω ≤ (sz.Bctl n q.1.1) ^ n_ * (ξ₁ + G) := by
    refine Finset.sup'_le _ _ fun p _ => ?_
    have := hpt p
    rw [div_le_iff₀ (pow_pos hBv _)] at this
    linarith
  have hXi : STXiLKg Cf n q.1.1 n_ ω ≤ 1 + (ξ₁ + G) := by
    unfold STXiLKg
    have : STmaxLKg Cf n q.1.1 n_ ω / (sz.Bctl n q.1.1) ^ n_ ≤ ξ₁ + G :=
      (div_le_iff₀ (pow_pos hBv _)).2 (by linarith)
    linarith
  have := hζ1 n q
  change STXiLKg Cf n q.1.1 n_ ω ≤ ξ₁ + G +
    ((sz.Bctl n q.1.2) ^ (1 / 6 : ℝ) * XLK n_ n q.1.2 +
      STbootRHS 1 (fun m => XL m n q.1.2) (fun m => XLK m n q.1.2) (sz.Bctl n (s n)) n_ p)
  linarith

end Combine

/-! ## 4. Targets 13 and 14 over a carrier family

The family-premise table (ticket T2505): the premises are those of `stOeqNZgL''_of` (rows 1-6, 3, 4, 7, 11, 9 `B45Gen_Facts`, 14 D1 with R1, 12, 15 `NQEndFlowGen_KLipFam`, 16 `QtBootGen_FlowModFam`);
the round reads in addition the fields `ZeroModeGen_WardCls` of `B45Gen_Facts` and the spectral data.  No D1 of the alternating endpoint (`QProxyG_KerEK4Fam`), no `Θ`-decay class (`hTh`), no non-alternating
kernel class (`NQGoodGen_KerNALFam`), no `∀ n` drift or hierarchy premise.  The pinned `∃`: `𝔠d` (of `stOeqNZPTgL''_of`), `C5` (D1), `c` (row 16), `Aof κ`, all before `(sz, z)`. -/

section Public

/-- **Target 13, `stXiRoundNZgL_of`** (band `stXiRoundNZ_holds`, `QtNonzeroBoot.lean:1059`): the case-(ii) round `STXiRoundgL'` over `STIngRgL d STCaseII` of a carrier family, with the constant `𝔠_d`
of `stOeqNZgL''_of`.  The combination `QtNZBootGen_round_of_NZ` (`lem: newPQ` at `A = ∅`, `zeroModeCalc_LK_expansion_emptyg` under `ZeroModeGen_WardCls`; the lower terms from the hypotheses) is applied to
the uniform projected endpoint `STNZConclgL''`; `STCaseII` enters only through `stOeqNZgL''_of`. -/
theorem stXiRoundNZgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- rows 1-6 (the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`)
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- row 9: the carrier facts `ZeroModeGen_KerSums`, `ZeroModeGen_WardCls` (fields of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- row 14: D1 (the `∃ C5` before `(sz, z)`) and R1 in the A-form (the pinned `Aof κ`); row 12: the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- rows 15, 16: the `𝒦` modulus (U3s2c, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (U4s3, family row 16)
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
    STIngRgL d STCaseII law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t) := by
  have hNZ := stOeqNZgL''_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK
    hExp hKL hKT hU hB45 hKerFam hR1 hT0 hKLip hFM
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := hNZ hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hNZ' := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨C₆, -, hB⟩ := hB45 κ hκ
  exact QtNZBootGen_round_of_NZ (mkM sz z).toFlowFM (law sz) hA.2.2.1 hspec (hB sz ε 𝔠 𝔡 z hflow).1 hs ht1 hNZ'

/-- **Target 14, `stOeqQtNZgL'_of`** (band `stOeqQtNZ'_holds`, `QtNonzeroBoot.lean:1074`; conclusion = the merged T2491 pin `STOeqQtNZgL'`, binding): `lem:STOeq_Qt_nonzero`, R2*, over a carrier family.
`stXiBootRgL'_of_round d STCaseII` (row a; the bundle `QtBootGen_Hyp` from the premises: the law is a probability measure at a flow by `hW`, `hLaw` and `isProbabilityMeasure_pathP`) applied to
`stXiRoundNZgL_of`; the self-absorbing current-length term is removed by the deterministic bootstrap. -/
theorem stOeqQtNZgL'_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- rows 1-6 (the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`)
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- row 9: the carrier facts `ZeroModeGen_KerSums`, `ZeroModeGen_WardCls` (fields of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- row 14: D1 (the `∃ C5` before `(sz, z)`) and R1 in the A-form (the pinned `Aof κ`); row 12: the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- rows 15, 16: the `𝒦` modulus (U3s2c, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (U4s3, family row 16)
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
    STOeqQtNZgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  refine stXiBootRgL'_of_round d STCaseII law Flow mkM T0 ⟨hFlow, ?_, ?_, hT0, hFM⟩
    (stXiRoundNZgL_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU
      hB45 hKerFam hR1 hT0 hKLip hFM)
  · intro sz κ ε 𝔠 𝔡 z hκ hz
    have : IsProbabilityMeasure (mkM sz z).Pp := by
      rw [(hW sz κ ε 𝔠 𝔡 z hκ hz).2.1]; exact isProbabilityMeasure_pathP _
    exact NQEndFlowGen_isProb (hLaw sz z)
  · intro sz κ ε 𝔠 𝔡 z hκ hz
    exact ⟨⟨E sz z, hL sz κ ε 𝔠 𝔡 z hκ hz⟩, hm sz κ ε 𝔠 𝔡 z hκ hz, hSpec sz κ ε 𝔠 𝔡 z hκ hz⟩

end Public

/-! ## 5. The band re-derivations (every `d ≥ 3`)

The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), lemT)`, `Hf = seqHflow`, `E = STflowE`, `lam' = sz.lam`, `Ψ = 0`, `gK = sz.lam`, `Aof = 1`: every row is discharged as in
`stOeqNZgL''_band` (`Chain/QtNonzeroFlowGen`); row 9 is `b45Gen_facts_band` (its `ZeroModeGen_WardCls` field is `zeroModeGen_wardCls_band`).  No hypothesis is left open: the pins are theorems at every
`d ≥ 3`. -/

section BandReDerivation

namespace QtNonzeroBootGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- **Target 13 at the band** (`stXiRoundNZ_holds`, `QtNonzeroBoot.lean:1059`, re-derived at every `d ≥ 3`) through `stXiRoundNZgL_of`: every row of the family-premise table is discharged at the band family. -/
theorem stXiRoundNZgL_band (d : ℕ) (hd : 3 ≤ d) :
    STIngRgL d STCaseII (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n))
      (fun sz z s t => STXiRoundgL' (bandStep2Mat sz (STflowE z)).toFlowFM (Sizes.seqP sz) s t) :=
  stXiRoundNZgL_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z => seqHflow sz) (fun _ z => STflowE z)
    (fun sz _ => sz.lam) (fun sz _ => sz.lam) (fun _ _ _ => 0) (fun _ => 1)
    ((bandFM_STSEforLn d).1 (stSEforLn_holds d)) (Step2EventsGen_bandFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => ⟨Real.sqrt κ / 2, DecayGen_bandSpec sz hκ (QtBootGen_flow_abs_le hz)⟩)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => stepDecompGen_loopForm_band sz _ fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))
    (fun sz κ ε 𝔠 𝔡 z _ _ => stepDecompGen_walkForm_band sz _)
    (fun sz z => Step2EventsGen_bandLaw sz _) (fun sz z => bandStep34_LCompat sz _)
    (fun sz z => DecayGen_bandWardPair sz _)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => bandFM_STKcalDecay hd sz hκ hz.1 (QtBootGen_flow_abs_le hz))
    (fun sz κ ε 𝔠 𝔡 z hκ hz s t hs hst ht1 hU k hk σ =>
      stEtermDecay hd sz hκ (QtBootGen_flow_abs_le hz) hz.1 hs hst ht1 ((bandFM_STDecayLoopU sz _ s t).2 hU) k hk σ)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (norm_mE (by linarith [QtBootGen_flow_abs_le hz n])).le)
    (fun sz z n => rfl) (fun sz z n a => hierDriftGen_SB_row sz n a)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => gridRepTailGen_ker_band sz _ n (by linarith [QtBootGen_flow_abs_le hz n]))
    (fun sz z n w k σ a => rfl)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall fun n s' t' K' =>
      hierDriftGen_expand_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith)) s' t' K' n)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kLoop_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kTwo_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_uStep_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (b45Gen_facts_band d) (qtNZGen_kerNZ_band d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (one_mul _).ge)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hz => ⟨ε / 2, half_pos hε, (Green.v3_premises_of_stFlow sz hκ hε hz (fun n => le_rfl)).2.2.2⟩)
    (nqEndFlowGen_kLip_band d) (qtBootGen_flowModFam_band d)

/-- **The band re-derivation of `stOeqQtNZ'_holds` at every `d ≥ 3`** through `stOeqQtNZgL'_of`: the generic pin `STOeqQtNZgL'` holds at the band family with no open hypothesis. -/
theorem stOeqQtNZgL'_band (d : ℕ) (hd : 3 ≤ d) :
    STOeqQtNZgL' d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
      (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqQtNZgL'_of d (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandStep2Mat sz (STflowE z)) (fun _ z n => lemT (z n)) (fun sz z => seqHflow sz) (fun _ z => STflowE z)
    (fun sz _ => sz.lam) (fun sz _ => sz.lam) (fun _ _ _ => 0) (fun _ => 1)
    ((bandFM_STSEforLn d).1 (stSEforLn_holds d)) (Step2EventsGen_bandFlow d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => ⟨Real.sqrt κ / 2, DecayGen_bandSpec sz hκ (QtBootGen_flow_abs_le hz)⟩)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => stepDecompGen_loopForm_band sz _ fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))
    (fun sz κ ε 𝔠 𝔡 z _ _ => stepDecompGen_walkForm_band sz _)
    (fun sz z => Step2EventsGen_bandLaw sz _) (fun sz z => bandStep34_LCompat sz _)
    (fun sz z => DecayGen_bandWardPair sz _)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => bandFM_STKcalDecay hd sz hκ hz.1 (QtBootGen_flow_abs_le hz))
    (fun sz κ ε 𝔠 𝔡 z hκ hz s t hs hst ht1 hU k hk σ =>
      stEtermDecay hd sz hκ (QtBootGen_flow_abs_le hz) hz.1 hs hst ht1 ((bandFM_STDecayLoopU sz _ s t).2 hU) k hk σ)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (norm_mE (by linarith [QtBootGen_flow_abs_le hz n])).le)
    (fun sz z n => rfl) (fun sz z n a => hierDriftGen_SB_row sz n a)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => gridRepTailGen_ker_band sz _ n (by linarith [QtBootGen_flow_abs_le hz n]))
    (fun sz z n w k σ a => rfl)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall fun n s' t' K' =>
      hierDriftGen_expand_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith)) s' t' K' n)
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kLoop_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_kTwo_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (fun sz κ ε 𝔠 𝔡 z hκ hz => Eventually.of_forall
      (hierDriftGen_uStep_band sz _ (fun n => (QtBootGen_flow_abs_le hz n).trans_lt (by linarith))))
    (b45Gen_facts_band d) (qtNZGen_kerNZ_band d)
    (fun sz κ ε 𝔠 𝔡 z hκ hz n => (one_mul _).ge)
    (fun sz κ ε 𝔠 𝔡 z hκ hε hz => ⟨ε / 2, half_pos hε, (Green.v3_premises_of_stFlow sz hκ hε hz (fun n => le_rfl)).2.2.2⟩)
    (nqEndFlowGen_kLip_band d) (qtBootGen_flowModFam_band d)

/-- `stOeqQtNZgL'_band` at `d = 3` (used by the instances of §6). -/
theorem stOeqQtNZgL'_band3 : STOeqQtNZgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n)) :=
  stOeqQtNZgL'_band 3 le_rfl

/-- `stXiRoundNZgL_band` at `d = 3` (used by the instances of §6). -/
theorem stXiRoundNZgL_band3 : STIngRgL 3 STCaseII (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => (bandStep2Mat sz (STflowE z)).toFlowFM) (fun _ z n => lemT (z n))
    (fun sz z s t => STXiRoundgL' (bandStep2Mat sz (STflowE z)).toFlowFM (Sizes.seqP sz) s t) :=
  stXiRoundNZgL_band 3 le_rfl

/-- **Band re-derivation of `stXiRoundNZ_holds`** (`QtNonzeroBoot.lean:1059`: `∀ d, STIngR d STCaseII (STXiRound' ..)`) through `stXiRoundNZgL_band` and `bandFM_STXiRound'`
(used by the instances of §6; not a ticket target). -/
theorem stXiRoundNZ_holds_of_gen (d : ℕ) : STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t) := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STIngR d STCaseII (fun sz E s t => STXiRound' sz E s t)).2 (stXiRoundNZgL_band d hd)
  · exact fun h => absurd h hd

end QtNonzeroBootGenCheck

/-- **Band re-derivation of `stOeqQtNZ'_holds`** (`QtNonzeroBoot.lean:1074`, the same statement `∀ d, STOeqQtNZ' d`): for `3 ≤ d` the band pin from the generic one (`stOeqQtNZgL'_band`) through
`bandFM_STOeqQtNZ'`; for `d < 3` the pin is vacuous (`STIngRgL` starts with `3 ≤ d →`). -/
theorem stOeqQtNZ'_holds_of_gen (d : ℕ) : STOeqQtNZ' d := by
  by_cases hd : 3 ≤ d
  · exact (bandFM_STOeqQtNZ' d).2 (QtNonzeroBootGenCheck.stOeqQtNZgL'_band d hd)
  · exact fun h => absurd h hd

end BandReDerivation

/-! ## 6. Compiled nonempty instances (`d = 3`)

Data of the merged band instances (`Induction/Step34Pins.lean:717-946`, `Induction/QtNonzeroBoot.lean:1085-1251`): `szB` (`L = 4`, `W = n + 4`, `lam ≡ 1`, `N = (4(n+4))^3`), the flow `zB`
(`z_n = 1/2 + i/64`, `flow_zB` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`), `s ≡ 15/16`, `t ≡ 31/32` (`szB_flow_ht`; `szB_caseII`: `1 - s = 1/16 = lam²/L²`, the boundary of case (ii);
`conStInd_const`), `C_d = 1`.  `STKboundgL`, `STKwardgL` are theorems of the flow; what stays a hypothesis of an example is a stochastic premise that is another gate's pin: `STLKgL s` and
`STStep2ConclgL` (premises of `STIngRgL`). -/

section Instances

namespace QtNonzeroBootGenCheck

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Ind.AzumaProxyNInst RBM.Ind.QtNonzeroEndInst

/-- **Target 13 at the data**: the generic round `STIngRgL d STCaseII … STXiRoundgL'` (no open hypothesis, `stXiRoundNZgL_band3`, i.e. `stXiRoundNZgL_of` with every row discharged) evaluated at `(szB, zB)`,
window `[15/16, 31/32]`, `C_d = 1`: the constant `𝔠_d ∈ (0, 1/100]` and, given the stochastic pins `STLKgL s`, `STStep2ConclgL`, the round conclusion `STXiRoundgL'` of the band carrier. -/
theorem inst_XiRoundNZgL (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16))
    (hStep2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STXiRoundgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) := by
  obtain ⟨𝔠d, h0, h1, hC⟩ := stXiRoundNZgL_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact ⟨𝔠d, h0, h1, hC (1 / 6) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    ((bandFM_STKward szB (STflowE zB)).1 (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB)) hLK
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hStep2⟩

/-- **Target 14 at the data**: the generic pin `STOeqQtNZgL'` (`stOeqQtNZgL'_band3`) evaluated at the same data; the conclusion is the bootstrap pin `STXiBootgL'` (the merged T2491 text). -/
theorem inst_OeqQtNZgL' (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16))
    (hStep2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1) :
    ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
      STXiBootgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) := by
  obtain ⟨𝔠d, h0, h1, hC⟩ := stOeqQtNZgL'_band3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 1 one_pos
  exact ⟨𝔠d, h0, h1, hC (1 / 6) szB zB flow_zB (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num)
    (szB_flow_ht (by norm_num)) szB_caseII (stKbound_of_flow szB (by norm_num) (by norm_num) flow_zB)
    ((bandFM_STKward szB (STflowE zB)).1 (stKward_of_flow szB (by norm_num) (by norm_num) flow_zB)) hLK
    (conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h0) hStep2⟩

/-- **The combination at the data**: the uniform projected endpoint `STNZConclgL''` at `(szB, zB)` (target 12, `inst_OeqNZgL''`) gives the round `STXiRoundgL'` through `QtNZBootGen_round_of_NZ`:
`DecayGen_Spec` (`DecayGen_bandSpec`, `κm = √(1/10)/2`), `ZeroModeGen_WardCls` (`zeroModeGen_wardCls_band`), `0 ≤ s`, `t < 1` are discharged. -/
example (hLK : STLKgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16))
    (hStep2 : STStep2ConclgL (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) 1) :
    STXiRoundgL' (bandFM szB (STflowE zB)) (Sizes.seqP szB) (fun _ => 15 / 16) (fun _ => 31 / 32) := by
  obtain ⟨-, -, -, hNZ⟩ := QtNonzeroFlowGenCheck.inst_OeqNZgL'' hLK hStep2
  exact QtNZBootGen_round_of_NZ (bandFM szB (STflowE zB)) (Sizes.seqP szB) szB_tendsto
    (DecayGen_bandSpec szB (κ := 1 / 10) (by norm_num) (QtBootGen_flow_abs_le flow_zB))
    (zeroModeGen_wardCls_band szB (STflowE zB) (fun n => abs_lemE_lt_two (z := zB n)
      (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast szB.one_le_size n) _) (flow_zB.2 n).2.1)))
    (fun _ => by norm_num) (fun _ => by norm_num) hNZ

/-- **`(2 N η_v)⁻¹ ≤ κm⁻¹ B_v` at the data** (`QtNZBootGen_inv_Neta`, size index `0` (`N = 4096`), `v = 31/32`, `κm = √(1/10)/2`): the one lower-term fact of `3_5:1925`. -/
example : (2 * (((szB.size 0 : ℕ) : ℝ) * (bandFM szB (STflowE zB)).eta 0 (31 / 32)))⁻¹ ≤
    (Real.sqrt (1 / 10) / 2)⁻¹ * szB.Bctl 0 (31 / 32) :=
  QtNZBootGen_inv_Neta (bandFM szB (STflowE zB)) 0 (DecayGen_bandSpec szB (κ := 1 / 10) (by norm_num) (QtBootGen_flow_abs_le flow_zB))
    (by norm_num)

/-- **One lower term at the data** (`QtNZBootGen_term_le`, size index `0`, `n_ = 3`, `k = 2`, `σ' = (+,-)`, `ι = (0, 1)`, `A' = {0}`, `ξ = 1`, `v = 31/32`): the lower term
of `(eq:expandQAempty)` divided by `B_v^{3}` is at most `|ξ| 2^k κm^{-(n_-k)} Ξ̂^{(𝓛-𝒦)}_{v,k}`. -/
example (ω : szB.SeqΩ) (a : Fin 3 → Zd 3 (szB.L 0)) :
    ‖((1 : ℤ) : ℂ) / (2 * Complex.I * ((szB.size 0 : ℕ) : ℂ) * ((bandFM szB (STflowE zB)).eta 0 (31 / 32) : ℂ)) ^ (3 - 2) *
        zeroModeSet 3 (szB.L 0) ({0} : Finset (Fin 2))
          (fun a' => (bandFM szB (STflowE zB)).L 0 (31 / 32) ![true, false] a' ω -
            (bandFM szB (STflowE zB)).K 0 (31 / 32) ![true, false] a') (a ∘ ![0, 1])‖ / (szB.Bctl 0 (31 / 32)) ^ 3 ≤
      (|((1 : ℤ) : ℝ)| * 2 ^ 2 * ((Real.sqrt (1 / 10) / 2)⁻¹) ^ (3 - 2)) * STXiLKg (bandFM szB (STflowE zB)) 0 (31 / 32) 2 ω :=
  QtNZBootGen_term_le (bandFM szB (STflowE zB)) 0
    (DecayGen_bandSpec szB (κ := 1 / 10) (by norm_num) (QtBootGen_flow_abs_le flow_zB)) (by norm_num) ω (n_ := 3) (k := 2) (by norm_num)
    1 ![true, false] ![0, 1] {0} a

/-- **Targets 13, 14, band corollaries at the data**: the merged pins `STXiRound'`, `STOeqQtNZ' 3` (`stXiRoundNZ_holds_of_gen`, `stOeqQtNZ'_holds_of_gen`) evaluated at `(szB, zB)` by the merged `inst_ing`. -/
example : InstIngConcl (fun sz E s t => STXiRound' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STXiRound' sz E s t) (stXiRoundNZ_holds_of_gen 3) szB zB flow_zB (fun _ => 15 / 16)
    (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

example : InstIngConcl (fun sz E s t => STXiBoot' sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) 1 :=
  inst_ing STCaseII (fun sz E s t => STXiBoot' sz E s t) (by simpa [STOeqQtNZ'] using stOeqQtNZ'_holds_of_gen 3) szB zB flow_zB
    (fun _ => 15 / 16) (fun _ => 31 / 32) (fun _ => by norm_num) (fun _ => by norm_num) (szB_flow_ht (by norm_num)) szB_caseII
    (fun _ h𝔠 => conStInd_const szB szB_W_tendsto (by norm_num) (by norm_num) h𝔠) 1 one_pos

/-- **Target 14, the statement of the merged pin** (`bandFM_STOeqQtNZ'`): the band pin is the generic one at the band family. -/
example : STOeqQtNZ' 3 ↔ STOeqQtNZgL' 3 (fun sz => Sizes.seqP sz) (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z)
    (fun sz z => bandFM sz (STflowE z)) (fun _ z n => lemT (z n)) := bandFM_STOeqQtNZ' 3

/-- **The finite sums of the combination at the data** (`QtNZBootGen_prec_sum`): a finite sum of constants `≺` their bound over `Unit` at `szB`, `PrecL` at the band law; `SizeTendsto` is
discharged (`szB_tendsto`). -/
example : PrecL szB (Sizes.seqP szB) (U := fun _ => Unit) (fun _ _ _ => ∑ i ∈ Finset.range 3, (1 : ℝ)) (fun _ _ _ => (3 : ℝ)) :=
  QtNZBootGen_prec_sum szB_tendsto (Finset.range 3) (f := fun _ _ _ _ => (1 : ℝ)) (fun _ _ _ => by norm_num)
    (fun i _ => StochDomAt.of_le_left (ξ₁ := fun _ _ _ => (3 : ℝ)) (fun _ _ _ => by norm_num)
      (StochDomAt.refl (szB.tendsto_size szB_tendsto) (fun _ _ _ => by norm_num)))

end QtNonzeroBootGenCheck

end Instances

end RBM.BA

end
