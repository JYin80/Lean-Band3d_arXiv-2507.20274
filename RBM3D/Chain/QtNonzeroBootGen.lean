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
# The case-(ii) round and the bootstrap over the carrier family: `stOeqQtNZgL'_of`

Generic form of `Induction/QtNonzeroBoot` §5-§6 over a carrier family `(law, Flow, mkM, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper:
Lemma 4.14 (`lem:STOeq_Qt_nonzero`), its proof: `lem: newPQ` at `A = ∅` ((4.72) `eq:expandQAempty`), the bound before "solving which", (4.76) `am;asoiuw_smalleta`.

* `stXiRoundNZgL_of`: the case-(ii) round `STXiRoundgL'` over `STIngRgL d STCaseII` from the uniform projected endpoint `STNZConclgL''`: `zeroModeCalc_LK_expansion_emptyg`
  under `ZeroModeGen_WardCls` (a field of `B45Gen_Facts`) writes `(𝓛-𝒦)^{(n_)}_{v,σ,a}` as `(Q^{(I_diff σ)}(𝓛-𝒦)^{(n_)})_{σ,a}` plus lower terms `k_α ∈ [1, n_-1]`; the first is
  `STNZConclgL''` at the envelope bounds, every lower term is `≤ C Ξ̂^{(𝓛-𝒦)}_{v,k_α}` with `(N η_u)⁻¹ ≤ κm⁻¹ B_u` (`DecayGen_Spec`, `QtBootGen_inv_one_sub_le`: the twin of `expWII_inv_Neta_le`).
* `stOeqQtNZgL'_of` (the statement `STOeqQtNZgL'`) = `stXiBootRgL'_of_round d STCaseII` applied to `stXiRoundNZgL_of`.

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

open private QtBootGen_inv_one_sub_le from RBM3D.Chain.QtBootGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqFlowSharp)

/-! ## 1. `≺` algebra for the combination over a law (copies of the private lemmas of `QtNonzeroBoot`) -/

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

/-! ## 2. The lower terms of (4.72) `eq:expandQAempty` over a carrier -/

section LowerTerms

variable {d : ℕ}

/-- **`(2 N η_v)⁻¹ ≤ κm⁻¹ B_v`** (band `qtBoot_inv_Neta`; the twin of `expWII_inv_Neta_le`): `η_v = (1 - v) Im m ≥ (1 - v) κm` (`DecayGen_Spec`) and
`(1 - v)⁻¹ ≤ N B_v` (`QtBootGen_inv_one_sub_le`), `v < 1`: the bound `(Nη_t)^{-1} ≤ C W^{-d}B_{t,0}` used in the proof of Lemma 4.17. -/
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

/-- **One lower term of (4.72) `eq:expandQAempty`, divided by `B_v^{n_}`** (band `qtBoot_term_le`): with `1 ≤ k ≤ n_ - 1` (`k_α = 1` included),
`|ξ| (2Nη_v)^{-(n_-k)} |(Q^{(A')}(𝓛-𝒦)^{(k)}_{v,σ'})(a ∘ ι)| / B_v^{n_} ≤ |ξ| 2^k κm^{-(n_-k)} Ξ̂^{(𝓛-𝒦)}_{v,k}`: (4.43) `normQA2` `‖Q^{(A')} T‖ ≤ 2^{#A'} ‖T‖` with `#A' ≤ k`,
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

/-! ## 3. The case-(ii) round from the uniform projected endpoint -/

section Combine

variable {d : ℕ}

/-- **The case-(ii) round from the uniform projected endpoint at one carrier** (band `qtBoot_round_of_NZ`; Lemma 4.14 `lem:STOeq_Qt_nonzero`): at the carrier data
`DecayGen_Spec`, `ZeroModeGen_WardCls`, `0 ≤ s`, `t < 1`, `STNZConclgL''` (the uniform statement for `Q^{(I_diff σ)}(𝓛-𝒦)`) gives `STXiRoundgL'`: `lem: newPQ` at `A = ∅`
(`zeroModeCalc_LK_expansion_emptyg`, data chosen per `σ`) writes `(𝓛-𝒦)^{(n_)}_{v,σ,a}` as `(Q^{(I_diff σ)}(𝓛-𝒦)^{(n_)})_{σ,a}` plus lower terms; the first is `STNZConclgL''` at the envelope
bounds (compared with the bounds of the round on the pairs), every lower term `k_α ∈ [1, n_-1]` is `≤ C_{n_} Ξ̂_{v,k_α}` (`QtNZBootGen_term_le`) and `Ξ̂_{v,k_α} ≺ XLK k_α u ≤ STbootRHS 1`; the finite
max over `(σ, a)` and the finite sums are `≺` algebra.  The lower terms follow from the hypotheses (`k_α = 1` included; no averaged law is used). -/
private theorem QtNZBootGen_round_of_NZ {sz : Sizes d} (Cf : FlowFM sz) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto)
    {κm : ℝ} (hspec : DecayGen_Spec Cf κm) (hWard : ZeroModeGen_WardCls sz Cf) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (ht1 : ∀ n, t n < 1) (hNZ : STNZConclgL'' Cf μ s t) : STXiRoundgL' Cf μ s t := by
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsize := sz.tendsto_size hsz
  -- the envelope bounds and the uniform endpoint at them
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
  -- positivity and the bound `ζ`
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

/-! ## 4. The round and the bootstrap over a carrier family

The hypotheses are those of `stOeqNZgL''_of` (`B45Gen_Facts`, the kernel class with the comparison hypothesis, `NQEndFlowGen_KLipFam`, `QtBootGen_FlowModFam`);
the round reads in addition the fields `ZeroModeGen_WardCls` of `B45Gen_Facts` and the spectral data.  There is no kernel class of the alternating endpoint (`QProxyG_KerEK4Fam`), no `Θ`-decay class (`hTh`), no non-alternating
kernel class (`NQGoodGen_KerNALFam`), no `∀ n` drift or hierarchy hypothesis.  The existentials fixed before `(sz, z)`: `𝔠d` (of `stOeqNZPTgL''_of`), `C5` (kernel class), `c` (flow modulus), `Aof κ`. -/

section Public

/-- **`stXiRoundNZgL_of`** (band `stXiRoundNZ_holds`): the case-(ii) round `STXiRoundgL'` over `STIngRgL d STCaseII` of a carrier family, with the constant `𝔠_d`
of `stOeqNZgL''_of`.  The combination `QtNZBootGen_round_of_NZ` (`lem: newPQ` at `A = ∅`, `zeroModeCalc_LK_expansion_emptyg` under `ZeroModeGen_WardCls`; the lower terms from the hypotheses) is applied to
the uniform projected endpoint `STNZConclgL''`; `STCaseII` enters only through `stOeqNZgL''_of`. -/
theorem stXiRoundNZgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
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
    -- the spectral data, the walk's variance law, the kernel class, the drift classes
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
    -- the carrier facts `ZeroModeGen_KerSums`, `ZeroModeGen_WardCls` (fields of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- the kernel class (the `∃ C5` before `(sz, z)`) and the comparison hypothesis in the A-form (`Aof κ`); the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- the `𝒦` modulus (`NQEndFlowGen_KLipFam`) and the `𝓛` modulus (`QtBootGen_FlowModFam`)
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

/-- **`stOeqQtNZgL'_of`** (band `stOeqQtNZ'_holds`; the statement `STOeqQtNZgL'`): Lemma 4.14 (`lem:STOeq_Qt_nonzero`) over a carrier family.
`stXiBootRgL'_of_round d STCaseII` (the bundle `QtBootGen_Hyp` from the hypotheses: the law is a probability measure at a flow by `hW`, `hLaw` and `isProbabilityMeasure_pathP`) applied to
`stXiRoundNZgL_of`; the self-absorbing current-length term is removed by the deterministic bootstrap. -/
theorem stOeqQtNZgL'_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
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
    -- the spectral data, the walk's variance law, the kernel class, the drift classes
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
    -- the carrier facts `ZeroModeGen_KerSums`, `ZeroModeGen_WardCls` (fields of `B45Gen_Facts`)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- the kernel class (the `∃ C5` before `(sz, z)`) and the comparison hypothesis in the A-form (`Aof κ`); the flow window
    (hKerFam : QtNZGen_KerNZFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK Aof)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- the `𝒦` modulus (`NQEndFlowGen_KLipFam`) and the `𝓛` modulus (`QtBootGen_FlowModFam`)
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

end RBM.BA

end
