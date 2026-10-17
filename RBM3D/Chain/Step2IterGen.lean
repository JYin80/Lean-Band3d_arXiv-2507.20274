/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step2EventsGen
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.NewKLK

/-!
# The Step 2 iteration over the carrier, first half (BA-T row T1a, ticket T2478)

Design `docs/reports/T2379-design.md` row T1, `docs/reports/T2452-design.md` (P4), check file
`docs/tickets/checks/T2478-check.lean`.  The band files `Induction/Step2Iterate.lean`, `OptL2a.lean`,
`OptL2b.lean`, `Induction/Step2Core.lean` are **not** edited: this file (T1a, with `Chain/Step2IterGen2.lean`) states
their generic forms over a carrier `Cm : Step2Mat sz` (or `C : FlowFM sz`) and a law `μ`.  No `BA/` import.

* **Target 1.**  The carrier classes `Step2IterGen_NewKLKAtN` (`lem:newKLK` at one carrier and one size index, the body of
  `STNewKLKAtgL'` at `mk sz (fun _ => E)` read as `Cm`), `Step2IterGen_NewKLK`, `Step2IterGen_K2` (`hK2e`, the conclusion of
  `ST_K2e_of_flow`), `Step2IterGen_OneLoop` (`𝒦^{(1)} = m(σ)`, `𝓛^{(1)}_- = conj 𝓛^{(1)}_+`), each with its band
  discharge (`step2IterGen_newKLK_band`, `_K2_band`, `_oneLoop_band`).
* **Target 2.**  `ST_good_engineg` (P4, `Step2Core:997`).
* **Target 3.**  `STSelfImpgL`, `ST_nextg`, `ST_decay_of_finalg`, `ST_selfImprove_sectiong`, `ST_selfImproveg`.
* **Band re-derivations** (section 4, `example : type_of% @<band name>`): the statements of `ST_good_engine`, `ST_selfImprove`, `ST_next`,
  `ST_decay_of_final` from the generic results at the band carrier; compiled nonempty instances of every target at `d = 3`.

Hypotheses of the generic results are the carrier facts F1-F3, F9 (T7a/T7b), the loop pins over `Cm`, and the classes of target 1.
No kernel is defined here.
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.setOption false

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1: the carrier classes -/

/-- **Target 1, `lem:newKLK` at one carrier and one size index** (`Step2IterGen_NewKLKAtN`): the body of `STNewKLKAtgL'`
(`Chain/NewKLKGen.lean:58`) at the carrier `Cm` and the index `n`.  It replaces `STNewKLKAt` in `ST_good_engine`. -/
def Step2IterGen_NewKLKAtN {d : ℕ} {sz : Sizes d} (Cm : Step2Mat sz) (n : ℕ) (C δ₀ : ℝ) : Prop :=
  ∀ (u D ℓ : ℝ), 0 ≤ u → u < 1 → 0 ≤ D → 0 ≤ ℓ → ℓ ≤ ((sz.L n : ℕ) : ℝ) →
    ∀ H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ, H.IsHermitian →
      (∀ x y, ‖STGMMg Cm n u H x y‖ ≤ δ₀) →
      ∀ (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        ‖STthetaOpg Cm n u σ (STLKMg Cm n u H σ) a‖ ≤
            C / (1 - u) * STJhatMg Cm n D ℓ u H * STprof sz n u D ℓ (a 0) (a 1) ∧
        ‖STELKLKMg Cm n u H σ a‖ ≤
            C / (1 - u) * (STJhatMg Cm n D ℓ u H +
              STJhatMg Cm n D ℓ u H ^ 2 * (if 1 ≤ ℓ then 1 else 0)) *
              STprof sz n u D ℓ (a 0) (a 1)

/-- **Target 1, `lem:newKLK` over a flow family** (`Step2IterGen_NewKLK`): the constants `C, δ₀` depend on `κ, 𝔡` only. -/
def Step2IterGen_NewKLK (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
    ∀ (ε 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, Step2IterGen_NewKLKAtN (mk sz z) n C δ₀

/-- **Target 1, the deterministic `𝒦^{(2)}` decay** (`Step2IterGen_K2`): `hK2e` of the skeleton, the conclusion form of
`ST_K2e_of_flow` over the carrier. -/
def Step2IterGen_K2 (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz) : Prop :=
  3 ≤ d → ∀ κ ε 𝔠 𝔡 : ℝ, 0 < κ → 0 < 𝔡 → ∀ (sz : Sizes d) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
    ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, t n < 1) →
      ∃ C_K : ℝ, 0 < C_K ∧ ∀ᶠ n in atTop, ∀ (u D : ℝ) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)),
        s n ≤ u → u ≤ t n → 0 ≤ D →
        ‖(mk sz z).K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1)

/-- **Target 1, the one-loop facts** (`Step2IterGen_OneLoop`): `𝒦^{(1)}_{σ,a} = m(σ)` in the window and
`𝓛^{(1)}_- = conj 𝓛^{(1)}_+` (band `ST_Kloop_one`, `ST_Lloop_one_false`). -/
def Step2IterGen_OneLoop {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  (∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ (σ : Bool) (a : Zd d (sz.L n)),
      C.K n u (fun _ : Fin 1 => σ) (fun _ => a) = if σ then C.m n else (starRingEnd ℂ) (C.m n)) ∧
    ∀ (n : ℕ) (u : ℝ) (a : Zd d (sz.L n)) (ω : sz.SeqΩ),
      C.L n u (fun _ : Fin 1 => false) (fun _ => a) ω =
        (starRingEnd ℂ) (C.L n u (fun _ : Fin 1 => true) (fun _ => a) ω)

/-! ### Band discharges of target 1 -/

section Band

/-- **Band discharge of `Step2IterGen_NewKLKAtN`** (one size index): `STNewKLKAt` (the band pin, proved as `stNewKLK_holds`) at the energy
`E n` gives the class at `bandStep2Mat sz E` and the index `n` (`bandStep2Mat sz (fun _ => E n)` and `bandStep2Mat sz E` agree at
index `n`; the `Θ`-term through `bandStep2_STthetaOp`). -/
theorem step2IterGen_newKLKAtN_band {d : ℕ} {κ 𝔡 C δ₀ : ℝ} (hnew : STNewKLKAt d κ 𝔡 C δ₀) (sz : Sizes d) (E : ℕ → ℝ)
    (n : ℕ) (hlam : 0 < sz.lam n) (hlam' : sz.lam n ≤ 𝔡⁻¹) (hE : |E n| ≤ 2 - κ) :
    Step2IterGen_NewKLKAtN (bandStep2Mat sz E) n C δ₀ := by
  intro u D ℓ hu0 hu1 hD hℓ0 hℓL H hH hGM σ a
  have h := hnew sz n (E n) u D ℓ hlam hlam' hE hu0 hu1 hD hℓ0 hℓL H hH hGM σ a
  refine ⟨?_, h.2⟩
  have h1 := h.1
  rwa [bandStep2_STthetaOp sz E n u σ _ a] at h1

/-- **Band discharge of `Step2IterGen_K2`** (`ST_K2e_of_flow`, `Induction/Step2Iterate.lean:1800`). -/
theorem step2IterGen_K2_band (d : ℕ) :
    Step2IterGen_K2 d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandStep2Mat sz (STflowE z)) :=
  fun hd3 _ _ _ _ hκ h𝔡 _ _ hflow _ _ hs ht1 => ST_K2e_of_flow hd3 hκ h𝔡 hflow hs ht1

end Band

/-! ## 2. Target 2: P4, `ST_good_engineg` (`Step2Core:997`) -/

/-- **Target 2, `ST_good_engineg`** (band `ST_good_engine`, `Step2Core.lean:997`): on the good event `STGoodAtg` of one step the
stopping index never fires and `Ĵ_k ≤ c₁ Λ² (1 + q + log r_k) b_k^{1/5} r_k^{3C}` for all grid indices, `c₁ = 3 + 3/Im m`.
Over a carrier `Cm : Step2Mat sz`: `hNew` is `Step2IterGen_NewKLKAtN` at `(Cm, n)`, `Im m` is `(Cm.m n).im` with F3 (`DecayGen_Spec`:
`0 < κm ≤ Im m`, `η = (1 - u) Im m`), the grid walk `Cm.Hpath` is Hermitian (inline), the stopping index is `STstopIdxg`. -/
theorem ST_good_engineg {d : ℕ} (sz : Sizes d) (Cm : Step2Mat sz) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (D : ℝ)
    (Kf : ℕ → ℝ → ℝ) (κm Λ δ₀ C a₀ r₀ ρ₁ q : ℝ)
    (hK : K n ≠ 0) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hD : 0 ≤ D)
    (hSpec : DecayGen_Spec Cm.toFlowFM κm) (hlam : 0 ≤ sz.lam n) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀)
    (hr₀ : 0 ≤ r₀) (hρ₁ : 0 ≤ ρ₁) (hNew : Step2IterGen_NewKLKAtN Cm n C δ₀)
    (hKf0 : ∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s t K n j))
    (hKfL : ∀ j, j ≤ K n → Kf n (gridTime s t K n j) ≤ ((sz.L n : ℕ) : ℝ))
    (hTmono : ∀ j k, j ≤ k → k ≤ K n →
      tailT d (sz.L n) (sz.lam n) (gridTime s t K n j) (Kf n (gridTime s t K n j)) ≤
        tailT d (sz.L n) (sz.lam n) (gridTime s t K n k) (Kf n (gridTime s t K n k)))
    (hb1 : sz.Bctl n (t n) ≤ 1) (hq0 : 0 ≤ q)
    (ha : a₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) (hr : r₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ))
    (hρ : ρ₁ ≤ (q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2)
    (hsmall : ∀ k, k ≤ K n →
      (3 + 3 * ((Cm.m n).im)⁻¹) * Λ ^ 2 *
          (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) *
          (sz.Bctl n (gridTime s t K n k)) ^ (1 / 30 : ℝ) < 1)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (hHerm : ∀ j, j ≤ K n → (Cm.Hpath s t K n j ω).IsHermitian)
    (hg : STGoodAtg Cm s t K n D (fun j => Kf n (gridTime s t K n j)) Λ δ₀ a₀ r₀ ρ₁ Mart Rem ω) :
    STstopIdxg Cm s t K D Kf n ω = K n ∧ ∀ k, k ≤ K n →
      STJhatMg Cm n D (Kf n (gridTime s t K n k)) (gridTime s t K n k) (Cm.Hpath s t K n k ω) ≤
        ((3 + 3 * ((Cm.m n).im)⁻¹) * Λ ^ 2 *
            (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
            (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) := by
  classical
  have hmI : 0 < (Cm.m n).im := lt_of_lt_of_le hSpec.1 (hSpec.2.1 n)
  have heta : ∀ u, Cm.eta n u = (Cm.m n).im * (1 - u) := fun u => by rw [hSpec.2.2 n u]; ring
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (by linarith) hKpos.le
  have hlast : s n + (K n : ℝ) * gridStep s t K n = t n := by
    have := gridTime_last s t K n hK
    simpa [gridTime] using this
  have hu_le : ∀ j, j ≤ K n → gridTime s t K n j ≤ t n := fun j hj =>
    (ST_gridTime_mem s t K n j hst hK hj).2
  have hu_ge : ∀ j, j ≤ K n → s n ≤ gridTime s t K n j := fun j hj =>
    (ST_gridTime_mem s t K n j hst hK hj).1
  have hu_mono : ∀ j k, j ≤ k → gridTime s t K n j ≤ gridTime s t K n k := by
    intro j k hjk
    unfold gridTime
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith [mul_le_mul_of_nonneg_right this hΔ]
  have hu_lt : ∀ j, j ≤ K n → gridTime s t K n j < 1 := fun j hj =>
    lt_of_le_of_lt (hu_le j hj) ht1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hbpos : ∀ j, j ≤ K n → 0 < sz.Bctl n (gridTime s t K n j) := fun j hj =>
    STBctl_pos sz n (hu_lt j hj)
  have hbmono : MonotoneOn (fun j => sz.Bctl n (gridTime s t K n j)) (Set.Iic (K n)) := by
    intro j hj k hk hjk
    exact STBctl_mono sz n (hu_mono j k hjk) (hu_lt k hk)
  have hb1' : ∀ j, j ≤ K n → sz.Bctl n (gridTime s t K n j) ≤ 1 := fun j hj =>
    (STBctl_mono sz n (hu_le j hj) ht1).trans hb1
  -- the profile
  have hPpos : ∀ (j : ℕ) (i : STLab sz n), 0 < STprof sz n (gridTime s t K n j) D
      (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j i
    unfold STprof
    exact mul_pos (inv_pos.mpr (pow_pos hW d)) (tailW_pos hW _)
  have hPm : ∀ i : STLab sz n, MonotoneOn (fun j => STprof sz n (gridTime s t K n j) D
      (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1)) (Set.Iic (K n)) := by
    intro i j hj k hk hjk
    simp only [Set.mem_Iic] at hj hk
    unfold STprof
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hW.le d))
    exact ST_tailW_mono_time hL1 hlam (hu_mono j k hjk) (hu_lt k hk) (hKf0 j hj) (hKf0 k hk)
      (Nat.cast_nonneg _) (hTmono j k hjk hk)
  have hJhsup : ∀ k B, k ≤ K n → (∀ i : STLab sz n, ‖STgAg Cm s t K n i.1 i.2 k ω‖ /
      STprof sz n (gridTime s t K n k) D (Kf n (gridTime s t K n k)) (i.2 0) (i.2 1) ≤ B) →
      STJhatMg Cm n D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
        (Cm.Hpath s t K n k ω) ≤ B := by
    intro k B hk h
    unfold STJhatMg
    exact Finset.sup'_le _ _ fun p _ => h p
  have hJh0 : ∀ j, j ≤ K n → 0 ≤ STJhatMg Cm n D (Kf n (gridTime s t K n j))
      (gridTime s t K n j) (Cm.Hpath s t K n j ω) := by
    intro j hj
    unfold STJhatMg
    have hw : STLab sz n := ((fun _ => true), (fun _ => 0))
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ hw))
    exact div_nonneg (norm_nonneg _) (hPpos j hw).le
  -- the stopping index
  have hτK : STstopIdxg Cm s t K D Kf n ω ≤ K n := firstHit_le _ _ _ ω
  have hbelow : ∀ j, j < STstopIdxg Cm s t K D Kf n ω →
      STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (Cm.Hpath s t K n j ω) < (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ) := by
    intro j hj
    have hj' : j < firstHit (fun j (ω : PathΩ sz) =>
        STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (Cm.Hpath s t K n j ω) / (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n) ω := hj
    have h1 := lt_firstHit_imp _ _ _ hj'
    have hb6 : 0 < (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ) :=
      Real.rpow_pos_of_pos (hbpos j (hj.le.trans hτK)) _
    exact (div_lt_one hb6).mp h1
  have hhit : STstopIdxg Cm s t K D Kf n ω < K n →
      (sz.Bctl n (gridTime s t K n (STstopIdxg Cm s t K D Kf n ω))) ^ (1 / 6 : ℝ) ≤
        STJhatMg Cm n D (Kf n (gridTime s t K n (STstopIdxg Cm s t K D Kf n ω)))
          (gridTime s t K n (STstopIdxg Cm s t K D Kf n ω))
          (Cm.Hpath s t K n (STstopIdxg Cm s t K D Kf n ω) ω) := by
    intro h
    have h' : firstHit (fun j (ω : PathΩ sz) =>
        STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (Cm.Hpath s t K n j ω) / (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n) ω <
        K n := h
    have h1 := ST_firstHit_hit _ 1 (K n) h'
    have hb6 : 0 < (sz.Bctl n (gridTime s t K n (STstopIdxg Cm s t K D Kf n ω))) ^
        (1 / 6 : ℝ) := Real.rpow_pos_of_pos (hbpos _ h.le) _
    exact (one_le_div hb6).mp h1
  -- the labels and the pathwise inequalities
  have hsK : s n + (K n : ℝ) * gridStep s t K n < 1 := by rw [hlast]; exact ht1
  have hg0 : gridTime s t K n 0 = s n := by simp [gridTime]
  have hdec : ∀ (i : STLab sz n) (k : ℕ), k ≤ K n → k ≤ STstopIdxg Cm s t K D Kf n ω →
      ‖STgAg Cm s t K n i.1 i.2 k ω‖ ≤ ‖STgAg Cm s t K n i.1 i.2 0 ω‖ +
        gridStep s t K n * ∑ j ∈ Finset.range k, ‖STgDriftg Cm s t K n i.1 i.2 j ω‖ +
        ‖Rem i k ω‖ + ‖Mart i k ω‖ := by
    intro i k hk _
    have hid := hg.ident i k hk
    have hsum : ‖((gridStep s t K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω‖ ≤
        gridStep s t K n * ∑ j ∈ Finset.range k, ‖STgDriftg Cm s t K n i.1 i.2 j ω‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hΔ
    rw [hid]
    calc ‖STgAg Cm s t K n i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω + Rem i k ω + Mart i k ω‖
        ≤ ‖STgAg Cm s t K n i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω + Rem i k ω‖ +
          ‖Mart i k ω‖ := norm_add_le _ _
      _ ≤ (‖STgAg Cm s t K n i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω‖ + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖STgAg Cm s t K n i.1 i.2 0 ω‖ + ‖((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDriftg Cm s t K n i.1 i.2 j ω‖) + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr
  have hdr : ∀ (j : ℕ) (i : STLab sz n),
      ‖STgDriftg Cm s t K n i.1 i.2 j ω‖ ≤
        ‖STthetaOpg Cm n (gridTime s t K n j) i.1
          (STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1) i.2‖ +
        ‖STELKLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ +
        ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ := by
    intro j i
    unfold STgDriftg
    exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  -- `lem:newKLK` at the grid states
  have hnewk : ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STthetaOpg Cm n (gridTime s t K n j) i.1
          (STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1) i.2‖ ≤
        C / (1 - gridTime s t K n j) * STJhatMg Cm n D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (Cm.Hpath s t K n j ω) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) ∧
      ‖STELKLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
        C / (1 - gridTime s t K n j) * (STJhatMg Cm n D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (Cm.Hpath s t K n j ω) +
          STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
            (Cm.Hpath s t K n j ω) ^ 2 * (if 1 ≤ Kf n (gridTime s t K n j) then 1 else 0)) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j hj i
    exact hNew (gridTime s t K n j) D (Kf n (gridTime s t K n j))
      (hs0.trans (hu_ge j hj)) (hu_lt j hj) hD (hKf0 j hj) (hKfL j hj)
      (Cm.Hpath s t K n j ω) (hHerm j hj) (hg.weak j hj) i.1 i.2
  have hCj : ∀ j, j ≤ K n → 0 ≤ C / (1 - gridTime s t K n j) := fun j hj =>
    div_nonneg hC (by linarith [hu_lt j hj])
  have hel : ∀ (j : ℕ) (i : STLab sz n), j ≤ K n →
      ‖STELKLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖ ≤
        C / (1 - gridTime s t K n j) * (STJhatMg Cm n D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (Cm.Hpath s t K n j ω) +
          STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
            (Cm.Hpath s t K n j ω) ^ 2) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j i hj
    refine (hnewk j hj i).2.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (hCj j hj))
      (hPpos j i).le
    split_ifs
    · simp
    · simp [sq_nonneg]
  have hs1 : s n < 1 := lt_of_le_of_lt hst ht1
  -- the closure `α'_k R_k < b_k^{1/6}` and the bound of `α_k`
  have hrk : ∀ k, k ≤ K n → 1 ≤ (1 - s n) / (1 - gridTime s t K n k) := by
    intro k hk
    have h1 : 0 < 1 - gridTime s t K n k := by linarith [hu_lt k hk]
    rw [le_div_iff₀ h1]
    linarith [hu_ge k hk]
  have hbs : ∀ k, k ≤ K n → sz.Bctl n (s n) ≤ sz.Bctl n (gridTime s t K n k) := fun k hk =>
    STBctl_mono sz n (hu_ge k hk) (hu_lt k hk)
  have hqb : ∀ k, k ≤ K n → q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) ≤
      q * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ) := fun k hk =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (STBctl_pos sz n hs1).le (hbs k hk)
      (by norm_num)) hq0
  have hρb : ∀ k, k ≤ K n → ρ₁ ≤ (q * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) ^ 2 := by
    intro k hk
    refine hρ.trans (pow_le_pow_left₀ (mul_nonneg hq0 (Real.rpow_nonneg (STBctl_pos sz n hs1).le _))
      (hqb k hk) 2)
  have hclose : ∀ k, k ≤ K n →
      (a₀ + r₀ + gridStep s t K n * ∑ j ∈ Finset.range k, Λ / ((Cm.m n).im *
          (1 - (s n + j * gridStep s t K n))) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
        Λ * (2 * Λ * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 2 : ℝ) *
          (gridStep s t K n * ∑ j ∈ Finset.range k,
            ((Cm.m n).im * (1 - (s n + j * gridStep s t K n)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
        ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) <
        (sz.Bctl n (gridTime s t K n k)) ^ (1 / 6 : ℝ) := by
    intro k hk
    have hk1 : s n + (k : ℝ) * gridStep s t K n < 1 := by
      have := hu_lt k hk; simpa [gridTime] using this
    have hα := ST_alpha_bound (k := k) (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀)
      (ρ₁ := ρ₁) (Λ := Λ) (mI := (Cm.m n).im)
      (b := fun j => sz.Bctl n (gridTime s t K n j)) hΔ hmI hΛ hρ₁
      (fun j hj => hbpos j (hj.trans hk)) (hbmono.mono (Set.Iic_subset_Iic.mpr hk)) hk1
    have hr1 : 1 ≤ (1 - s n) / (1 - (s n + k * gridStep s t K n)) := by
      have := hrk k hk; simpa [gridTime] using this
    have hR0 : 0 ≤ ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) :=
      Real.rpow_nonneg (by linarith) _
    have hcl := ST_closure_arith (b := sz.Bctl n (gridTime s t K n k)) (q := q)
      (L := Real.log ((1 - s n) / (1 - (s n + k * gridStep s t K n)))) (Λ := Λ)
      (mI := (Cm.m n).im) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁)
      (R := ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C))
      (hbpos k hk) (hb1' k hk) hΛ hmI (Real.log_nonneg hr1) hq0 hR0 (ha.trans (hqb k hk))
      (hr.trans (hqb k hk)) (hρb k hk) hρ₁ (by simpa [gridTime] using hsmall k hk)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα hR0) hcl
  have hmain : STstopIdxg Cm s t K D Kf n ω = K n ∧ ∀ k, k ≤ K n →
      STJhatMg Cm n D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
          (Cm.Hpath s t K n k ω) ≤
        (a₀ + r₀ + gridStep s t K n * ∑ j ∈ Finset.range k, Λ / ((Cm.m n).im *
            (1 - (s n + j * gridStep s t K n))) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
          Λ * (2 * Λ * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 2 : ℝ) *
            (gridStep s t K n * ∑ j ∈ Finset.range k,
              ((Cm.m n).im * (1 - (s n + j * gridStep s t K n)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
          ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) := by
    refine ST_engine (K := K n) (τ := STstopIdxg Cm s t K D Kf n ω)
      (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁) (Λ := Λ) (C := C)
      (mI := (Cm.m n).im)
      (x := fun j (i : STLab sz n) => ‖STgAg Cm s t K n i.1 i.2 j ω‖)
      (dr := fun j (i : STLab sz n) => ‖STgDriftg Cm s t K n i.1 i.2 j ω‖)
      (th := fun j (i : STLab sz n) => ‖STthetaOpg Cm n (gridTime s t K n j) i.1
        (STLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1) i.2‖)
      (el := fun j (i : STLab sz n) =>
        ‖STELKLKMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖)
      (eg := fun j (i : STLab sz n) =>
        ‖STEGtMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖)
      (mart := fun k (i : STLab sz n) => ‖Mart i k ω‖)
      (remk := fun k (i : STLab sz n) => ‖Rem i k ω‖)
      (ee := fun j (i : STLab sz n) =>
        ‖STEEMg Cm n (gridTime s t K n j) (Cm.Hpath s t K n j ω) i.1 i.2‖)
      (P := fun j (i : STLab sz n) => STprof sz n (gridTime s t K n j) D
        (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1))
      (Jh := fun j => STJhatMg Cm n D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
        (Cm.Hpath s t K n j ω))
      (b := fun j => sz.Bctl n (gridTime s t K n j))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hΔ
    · exact hsK
    · exact hmI
    · exact hΛ
    · exact hC
    · exact ha₀
    · exact hr₀
    · exact hρ₁
    · exact hbpos
    · exact hb1'
    · exact hbmono
    · exact fun j i hj => hPpos j i
    · exact hPm
    · exact hJh0
    · exact hJhsup
    · exact hτK
    · exact hbelow
    · exact hhit
    · exact hdec
    · exact hdr
    · exact fun j i hj => (hnewk j hj i).1
    · exact fun j i hj => hel j i hj
    · exact fun j i hj => by have := hg.lw j hj i; rw [heta] at this; exact this
    · exact fun j i hj => by have := hg.mg j hj i; rw [heta] at this; exact this
    · exact fun j i => norm_nonneg _
    · exact fun i k hk => hg.mart i k hk
    · exact fun i k hk => hg.rem i k hk
    · exact fun i => hg.init i
    · exact hclose
  refine ⟨hmain.1, fun k hk => (hmain.2 k hk).trans ?_⟩
  have hk1 : s n + (k : ℝ) * gridStep s t K n < 1 := by
    have := hu_lt k hk; simpa [gridTime] using this
  have hα := ST_alpha_bound (k := k) (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀)
    (ρ₁ := ρ₁) (Λ := Λ) (mI := (Cm.m n).im)
    (b := fun j => sz.Bctl n (gridTime s t K n j)) hΔ hmI hΛ hρ₁
    (fun j hj => hbpos j (hj.trans hk)) (hbmono.mono (Set.Iic_subset_Iic.mpr hk)) hk1
  have hr1 : 1 ≤ (1 - s n) / (1 - (s n + k * gridStep s t K n)) := by
    have := hrk k hk; simpa [gridTime] using this
  have hR0 : 0 ≤ ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) :=
    Real.rpow_nonneg (by linarith) _
  have hα' := ST_alpha'_le (b := sz.Bctl n (gridTime s t K n k)) (q := q)
    (L := Real.log ((1 - s n) / (1 - (s n + k * gridStep s t K n)))) (Λ := Λ)
    (mI := (Cm.m n).im) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁) (hbpos k hk) (hb1' k hk) hΛ hmI
    (Real.log_nonneg hr1) hq0 (ha.trans (hqb k hk)) (hr.trans (hqb k hk)) (hρb k hk) hρ₁
  have hfin := mul_le_mul_of_nonneg_right (hα.trans hα') hR0
  simpa [gridTime] using hfin

/-! ## 3. Target 3: one self-improving step (`Step2Iterate:56-724`) -/

/-- **Target 3, `STSelfImpgL`** (band `STSelfImp`, `Step2Iterate.lean:56`): the conclusion of one self-improving step
(`(eq:Gronwall_dervJuD)`, per time) over a flow carrier `C` and a law `μ`.  Definitional at `bandFM`. -/
def STSelfImpgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (Cd : ℝ) (s t : ℕ → ℝ)
    (Kf : ℕ → ℝ → ℝ) : Prop :=
  ∀ D : ℝ, 0 < D →
    PrecPTL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
      (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1))

/-- Enlarging the control pointwise (eventually in `n`, for all sample points) preserves `PrecPTL` (band `ST_PT_mono_eventually`,
`Step2Iterate.lean:65`). -/
theorem Step2IterGen_PT_mono_eventually {d : ℕ} {sz : Sizes d} (μ : Measure sz.SeqΩ) {U : ℕ → Type*}
    {ξ ζ ζ' : ∀ n, U n → sz.SeqΩ → ℝ} (hle : ∀ᶠ n in atTop, ∀ u ω, ζ n u ω ≤ ζ' n u ω)
    (h : PrecPTL sz μ ξ ζ) : PrecPTL sz μ ξ ζ' := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD, hle] with n hn hle' u
  refine le_trans (measure_mono ?_) (hn u)
  intro ω hω
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hle' u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hω

/-- **From one self-improving step to the next premise** (band `ST_next`, `Step2Iterate.lean:85`; `(eq:def_ell1)`, `3_5:570–575`,
with `(eq:simpleboundK)`): `𝓛 = 𝒦 + (𝓛-𝒦)`, `|𝒦| ≤ C_K W^{-d} 𝒯̃^L`, `|𝓛-𝒦| ≺ q W^{-d} 𝒯̃^{K}` with `q ≤ (W^{-d}B_{u,0})^{1/6}`, and the
scale step `𝒯_u(K') = (W^{-d}B_{u,0})^{1/6} 𝒯_u(K)` give `|𝓛| ≺ W^{-d} 𝒯̃^{K'}` at every time section.  Concludes `STScaleInvgL`. -/
theorem ST_nextg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (hsz : sz.SizeTendsto)
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) {Cd C_K : ℝ}
    (hCK : 0 < C_K) (Kf Kf' : ℕ → ℝ → ℝ)
    (hK2 : ∀ᶠ n in atTop, ∀ u D (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)), s n ≤ u →
      u ≤ t n → 0 ≤ D →
      ‖C.K n u σ a‖ ≤ C_K * STprof sz n u D ((sz.L n : ℕ) : ℝ) (a 0) (a 1))
    (hrange : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧ Kf n u ≤ Kf' n u)
    (hstep : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → (sz.Bctl n u) ^ (1 / 6 : ℝ) *
      tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ tailT d (sz.L n) (sz.lam n) u (Kf' n u))
    (hq : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) ∧
        0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ∧
        (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ 1)
    (h : STSelfImpgL C μ Cd s t Kf) : STScaleInvgL C μ s t Kf' := by
  intro tt D hD
  have hsize := tendsto_size sz hsz
  -- the section form of `h`, restricted to the alternating charges
  have hcard : ∀ᶠ n in atTop, (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 4)] with n hn
    exact ST_card_lab_le sz n hn
  have hsec := Step2EventsGen_sections_of_PT μ (V := STLab sz) (s := s) (t := t)
    (fun n p ω => ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω -
      C.K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ Cd * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1)) (by norm_num) hcard
    (h D hD) tt
  have hsec' : StochDomAt μ sz.size (U := STLab sz)
      (fun n (p : STLab sz n) ω => ‖C.L n (tt n : ℝ) p.1 p.2 ω -
        C.K n (tt n : ℝ) p.1 p.2‖)
      (fun n p _ => ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1)) := hsec
  have hres := StochDomAt.precomp_param (V := fun n =>
      {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n))) hsec'
    (fun n p => (p.1.1, p.2))
  have hnonneg : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) :=
    fun n p _ => mul_nonneg hCK.le (ST_STprof_pos sz n _ _ _ _ _).le
  have hKp : StochDomAt μ sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.K n (tt n : ℝ) p.1.1 p.2‖)
      (fun n p _ => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1)) :=
    Step2EventsGen_prec_of_le_ev μ hnonneg (by
      filter_upwards [hK2] with n hn p ω
      exact hn (tt n : ℝ) D p.1.1 p.2 (tt n).2.1 (tt n).2.2 hD.le)
  have hsum := StochDomAt.add hsize hKp hres
  have hL : StochDomAt μ sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p ω => C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1)) := by
    refine StochDomAt.of_le_left (fun n p ω => ?_) hsum
    have := norm_add_le (C.K n (tt n : ℝ) p.1.1 p.2)
      (C.L n (tt n : ℝ) p.1.1 p.2 ω - C.K n (tt n : ℝ) p.1.1 p.2)
    simpa [add_sub_cancel] using this
  -- the deterministic comparison
  have hcmp : ∀ᶠ n in atTop, ∀ (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ),
      C_K * STprof sz n (tt n : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2 0) (p.2 1) +
        ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
          STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (p.2 0) (p.2 1) ≤
      (C_K + 1) * STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1) := by
    filter_upwards [hq, hrange, hstep] with n hn hrangen hstepn p ω
    obtain ⟨hq1, hq0, hq2⟩ := hn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    obtain ⟨hK0, hKK⟩ := hrangen (tt n : ℝ) (tt n).2.1 (tt n).2.2
    have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hρL := ST_zdistInf_le sz n (p.2 0 - p.2 1)
    have hstep' := hstepn (tt n : ℝ) (tt n).2.1 (tt n).2.2
    have hsc := ST_tailW_scale_step (d := d) (L := sz.L n) (g := sz.lam n) (u := (tt n : ℝ))
      (K := Kf n (tt n : ℝ)) (K' := Kf' n (tt n : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
      (e := (sz.Bctl n (tt n : ℝ)) ^ (1 / 6 : ℝ)) (ρ := ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))
      hW hK0 hKK (hq0.trans hq1) hq2 hstep' hρ0
    have hL' := ST_tailW_L_le (d := d) (L := sz.L n) (g := sz.lam n) (u := (tt n : ℝ))
      (ℓ := Kf' n (tt n : ℝ)) (W := ((sz.W n : ℕ) : ℝ)) (D := D)
      (ρ := ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ)) (hK0.trans hKK) hρ0 hρL
    have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hW d)
    unfold STprof
    have hP1 : 0 ≤ tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) := (tailW_pos (by
          exact_mod_cast sz.W_pos n) _).le
    have e1 : ((1 - s n) / (1 - (tt n : ℝ))) ^ Cd * (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) ≤
        tailW d (sz.L n) (sz.lam n) (tt n : ℝ) (Kf' n (tt n : ℝ)) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.2 0 - p.2 1) : ℕ) : ℝ) :=
      (mul_le_mul_of_nonneg_right hq1 hP1).trans hsc
    nlinarith [mul_le_mul_of_nonneg_left hL' (mul_nonneg hCK.le hWd),
      mul_le_mul_of_nonneg_left e1 hWd]
  -- assemble: `ξ ≺ C_K P^L + q P^{Kf} ≤ (C_K + 1) P^{Kf'} ≺ P^{Kf'}`
  have hmono : StochDomAt μ sz.size
      (U := fun n => {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => ‖C.L n (tt n : ℝ) p.1.1 p.2 ω‖)
      (fun n p _ => (C_K + 1) * STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1)) :=
    StochDomAt.of_subset hL fun τ hτ => ⟨τ, hτ, hcmp.mono fun n hn ω hω => by
      obtain ⟨p, hp⟩ := hω
      exact ⟨p, lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hn p ω)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hp⟩⟩
  have hpos : ∀ (n : ℕ) (p : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)))
      (ω : sz.SeqΩ), 0 ≤ STprof sz n (tt n : ℝ) D (Kf' n (tt n : ℝ)) (p.2 0) (p.2 1) :=
    fun n p _ => (ST_STprof_pos sz n _ _ _ _ _).le
  have hcst := StochDomAt.const_mul_left (P := μ) hsize (show 0 ≤ C_K + 1 by linarith)
    hpos (StochDomAt.refl (P := μ) hsize hpos)
  exact StochDomAt.trans hsize hmono hcst

/-- **The last scale gives `(Eq:Gdecay_w)`** (band `ST_decay_of_final`, `Step2Iterate.lean:192`; `3_5:575–577`): if for every `D > 0` the
self-improving bound holds at a family `Kf` with `𝒯_u(K_u) ≤ W^{-D}` (eventually), then `𝒯̃^{K}_{u,D} = max(𝒯_u, W^{-D})` and
`q W^{-d} 𝒯̃ ≤ q W^{-d} 𝒯 + W^{-D}`: the per-time `STStep2DecayPTgL`. -/
theorem ST_decay_of_finalg {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) {s t : ℕ → ℝ} {Cd : ℝ}
    (h : ∀ D : ℝ, 0 < D → ∃ Kf : ℕ → ℝ → ℝ, STSelfImpgL C μ Cd s t Kf ∧
      ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
        (tailT d (sz.L n) (sz.lam n) u (Kf n u) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) ∨
          ((sz.L n : ℕ) : ℝ) ≤ Kf n u))
    (hqW : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1)
    (hq0 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      0 ≤ ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)) :
    STStep2DecayPTgL C μ Cd s t := by
  intro D hD
  obtain ⟨Kf, hself, hfin⟩ := h D hD
  refine Step2IterGen_PT_mono_eventually μ ?_ (hself D hD)
  filter_upwards [hfin, hqW, hq0] with n hn hqn hq0n
  intro p ω
  obtain ⟨⟨u, hsu, hut⟩, σ, a⟩ := p
  obtain ⟨hK0, hT⟩ := hn u hsu hut
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hρ0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfinal : tailW d (sz.L n) (sz.lam n) u (Kf n u) ((sz.W n : ℕ) : ℝ) D
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) =
      max (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
        (((sz.W n : ℕ) : ℝ) ^ (-D)) := by
    rcases hT with hT | hL
    · exact ST_tailW_final (d := d) (L := sz.L n) (g := sz.lam n) (u := u) (K := Kf n u)
        (W := ((sz.W n : ℕ) : ℝ)) (D := D) (ρ := ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
        hK0 hT
    · unfold tailW
      have hρL := ST_zdistInf_le sz n (a 0 - a 1)
      rw [min_eq_left (hρL.trans hL)]
  have hTnn := tailT_nonneg (d := d) (L := sz.L n) (g := sz.lam n) (t := u) hρ0
  have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW.le _
  have hmax : max (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ))
      (((sz.W n : ℕ) : ℝ) ^ (-D)) ≤
      tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) :=
    max_le (by linarith) (by linarith)
  have hWd : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := inv_nonneg.mpr (pow_nonneg hW.le d)
  -- `T(ρ) = B_{u,ρ} exp(-(ρ/ℓ_u)^{1/2})`
  have hTeq : tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) =
      Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) := by
    unfold tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
  have hq := hq0n u hsu hut
  have hqW' := hqn u hsu hut
  show ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
      STprof sz n u D (Kf n u) (a 0) (a 1) ≤
    ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-D)
  unfold STprof STWB
  rw [hfinal]
  set q := ((1 - s n) / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) with hqdef
  set Wd := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWddef
  have e1 : q * (Wd * max (tailT d (sz.L n) (sz.lam n) u
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ)) (((sz.W n : ℕ) : ℝ) ^ (-D))) ≤
      q * (Wd * (tailT d (sz.L n) (sz.lam n) u ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) +
        ((sz.W n : ℕ) : ℝ) ^ (-D))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmax hWd) hq
  have e2 : q * (Wd * (tailT d (sz.L n) (sz.lam n) u
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) + ((sz.W n : ℕ) : ℝ) ^ (-D))) =
      q * (Wd * Bparam d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a 0 - a 1))) *
        Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) + (q * Wd) * ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    rw [hTeq]; ring
  have e3 : (q * Wd) * ((sz.W n : ℕ) : ℝ) ^ (-D) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := by
    nlinarith [mul_le_mul_of_nonneg_right hqW' hWD]
  linarith

set_option maxHeartbeats 3200000 in
-- the stopped Grönwall bootstrap on the good event is one declaration, as the band `ST_selfImprove_section` (same limit)
/-- **One self-improving step at a time section** (band `ST_selfImprove_section`, `Step2Iterate.lean:284`; `(eq:Gronwall_dervJuD)`,
`3_5:529`, per time): from the premise `Inv(Kf)` (`STScaleInvgL`) and the pins `lem:newKLK` (target 1), `lem: EWGn2_N`, `lem: EMn2_N`
(`STLWTgL`, `STEMn2ExpgL`), `Sol_CalL` + `lem:DIfREP` (`STGridMartgL`, the constant `C₀` is taken inside): `|(𝓛-𝒦)^{(2)}_{u,σ,a}| ≺ ((1-s)/(1-u))^{C_d} (W^{-d}B_{u,0})^{1/5}
W^{-d} 𝒯̃^{K_u}_{u,D}(|a₁-a₂|)` at `u = tt n`, `C_d = 3C + 1`.  The stopped Grönwall bootstrap of `ST_good_engineg` on the good event
`ST_good_probg`, transferred to the model at `t_n` through F9 (`Step2EventsGen_model_le_path`).  The flow enters through F1-F2
(`Step2EventsGen_Flow`) and F3 (`DecayGen_Spec`, `cstar = 3 + 3/κm`). -/
theorem ST_selfImprove_sectiong (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hFl : Step2EventsGen_Flow d Flow T0) (hLWT : STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMe : STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0) (hd : 0 < d)
    {sz : Sizes d} {κ ε 𝔡 𝔠 κm : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hSpec : DecayGen_Spec (mk sz z).toFlowFM κm)
    (hG : Step2EventsGen_Grid (mk sz z) (law sz))
    (hHerm : ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz), ((mk sz z).Hpath s t K n k ω).IsHermitian)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ T0 sz z n)
    {C δ₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀)
    (hnew : ∀ᶠ n in atTop, Step2IterGen_NewKLKAtN (mk sz z) n C δ₀) (hmart : STGridMartgL d Flow mk T0)
    (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
    (hDec : STDecaygL (mk sz z).toFlowFM (law sz) s) (hCon : STConStInd sz 𝔠d s t)
    (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf)
    (tt : ∀ n, TimeIcc s t n) (D : ℝ) (hD : 0 < D) :
    PrecL sz (law sz) (U := fun n => STLab sz n)
      (fun n i ω => ‖(mk sz z).L n (tt n : ℝ) i.1 i.2 ω - (mk sz z).K n (tt n : ℝ) i.1 i.2‖)
      (fun n i _ => ((1 - s n) / (1 - (tt n : ℝ))) ^ (3 * C + 1) *
        (sz.Bctl n (tt n : ℝ)) ^ (1 / 5 : ℝ) *
        STprof sz n (tt n : ℝ) D (Kf n (tt n : ℝ)) (i.2 0) (i.2 1)) := by
  classical
  obtain ⟨C₀, hC₀, hmart⟩ := hmart
  intro τ hτ D' hD'
  have hadm := hFl.1 sz κ ε 𝔠 𝔡 z hflow
  have hTlt1 : ∀ n, T0 sz z n < 1 := fun n => hFl.2 sz κ ε 𝔠 𝔡 z hκ hflow n
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := tendsto_size sz hsz
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband : sz.Bandwidth 𝔠 := hadm.2.2.2.1
  have hWO : sz.WO 𝔡 := hadm.2.2.2.2
  have hG' := hG
  obtain ⟨Hm, hGMM, hLM, hLMm, hGMMm, hlaw⟩ := hG
  -- the end of the grid is the section
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → ℝ, T = fun n => (tt n : ℝ) := ⟨_, rfl⟩
  have hsT : ∀ n, s n ≤ T n := fun n => by rw [hTdef]; exact (tt n).2.1
  have hTt : ∀ n, T n ≤ t n := fun n => by rw [hTdef]; exact (tt n).2.2
  have hTT : ∀ n, T n ≤ T0 sz z n := fun n => (hTt n).trans (htT n)
  have hT1 : ∀ n, T n < 1 := fun n =>
    lt_of_le_of_lt (hTT n) (hTlt1 n)
  have hT0 : ∀ n, 0 ≤ T n := fun n => (hs n).trans (hsT n)
  have hTD : ∀ n, T n = (tt n : ℝ) := fun n => by rw [hTdef]
  -- the loss `ε₁`, the floors
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (τ / 6) (c / 400) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; exact lt_min (by linarith) (by linarith)
  have hε₁τ : ε₁ ≤ τ / 6 := by rw [hε₁def]; exact min_le_left _ _
  have hε₁c : ε₁ ≤ c / 400 := by rw [hε₁def]; exact min_le_right _ _
  obtain ⟨Dm, hDmdef⟩ : ∃ Dm : ℝ, Dm = D' + 2 * D + 10 := ⟨_, rfl⟩
  have hDm1 : D' + 1 + 3 ≤ Dm := by rw [hDmdef]; linarith
  have hDm2 : 2 * D + 6 ≤ Dm := by rw [hDmdef]; linarith
  have hDmpos : 0 < Dm := by rw [hDmdef]; linarith
  -- the grid size and the martingale decomposition from the pin
  obtain ⟨CK, hCK0, hCK⟩ := hmart κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow s T hs hsT hTT Dm hDmpos
  obtain ⟨CK', hCK'def⟩ : ∃ CK' : ℝ, CK' = max CK (2 * (C₀ + D + 3)) := ⟨_, rfl⟩
  have hCK'0 : 0 ≤ CK' := by rw [hCK'def]; exact hCK0.trans (le_max_left _ _)
  have hCK'1 : CK ≤ CK' := by rw [hCK'def]; exact le_max_left _ _
  have hCK'2 : 2 * (C₀ + D + 3) ≤ CK' := by rw [hCK'def]; exact le_max_right _ _
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℕ, K = fun n => ⌈((sz.size n : ℕ) : ℝ) ^ CK'⌉₊ := ⟨_, rfl⟩
  have hKn : ∀ n, K n = ⌈((sz.size n : ℕ) : ℝ) ^ CK'⌉₊ := fun n => by rw [hKdef]
  have hK0 : ∀ n, K n ≠ 0 := fun n => by
    rw [hKn n]
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    exact (Nat.ceil_pos.2 (Real.rpow_pos_of_pos hN0 _)).ne'
  have hKbig' : ∀ n, ((sz.size n : ℕ) : ℝ) ^ CK' ≤ (K n : ℝ) := fun n => by
    rw [hKn n]; exact Nat.le_ceil _
  have hKbig : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ CK ≤ (K n : ℝ) := by
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with n hn
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hn
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hCK'1).trans (hKbig' n)
  obtain ⟨Mart, Rem, hident, hrem0, hmart0⟩ := hCK K hK0 hKbig
  -- the parameters of the good event: `Λ = q = 2 N^{ε₁}`, `a₀ = r₀ = Λ b_s^{1/5}`, `ρ₁ = a₀²`
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, X = fun n => ((sz.size n : ℕ) : ℝ) ^ ε₁ := ⟨_, rfl⟩
  have hX1 : ∀ n, 1 ≤ X n := fun n => by
    rw [hXdef]
    exact Real.one_le_rpow (by exact_mod_cast sz.one_le_size n) hε₁pos.le
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : ℕ → ℝ, Λ = fun n => 2 * X n := ⟨_, rfl⟩
  have hΛ1 : ∀ n, 1 ≤ Λ n := fun n => by rw [hΛdef]; have := hX1 n; simp only; linarith
  have hΛX : ∀ n, ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n := fun n => by
    rw [hΛdef]; have := hX1 n; rw [hXdef] at this ⊢; simp only at this ⊢; linarith
  have hΛX2 : ∀ n, 2 * ((sz.size n : ℕ) : ℝ) ^ ε₁ ≤ Λ n := fun n => by
    rw [hΛdef, hXdef]
  obtain ⟨a₀, ha₀def⟩ : ∃ a₀ : ℕ → ℝ, a₀ = fun n => Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) :=
    ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁def⟩ : ∃ ρ₁ : ℕ → ℝ,
      ρ₁ = fun n => (Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2 := ⟨_, rfl⟩
  -- cardinalities of the label sets
  have hN4 : ∀ᶠ n in atTop, 4 ≤ sz.size n := hsize.eventually (eventually_ge_atTop 4)
  have hcardIdx := ST_hcard sz
    (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsize hCK'0 K hKn
    (by filter_upwards [hN4] with n hn
        exact ST_card_idx_prod_le sz n (by omega))
  have hcardLab3 : ∀ᶠ n in atTop,
      (Fintype.card (STLab sz n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (3 : ℝ) := by
    filter_upwards [hN4] with n hn using ST_card_lab_le sz n hn
  have hcardLab := ST_hcard sz (V := fun n => STLab sz n) hsize hCK'0 K hKn (by
    filter_upwards [hcardLab3, hN4] with n hn hN
    refine hn.trans (Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num))
    exact_mod_cast (by omega : 1 ≤ sz.size n))
  have hcardF2 := ST_hcard sz (V := fun n => Fin 2 × STLab sz n) hsize hCK'0 K hKn (by
    filter_upwards [hN4] with n hn using ST_card_fin2_lab_le sz n hn)
  -- polynomial floors
  have hNcB : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ cB ^ (1 / 5 : ℝ) :=
    ST_size_pow_small sz hsize (by norm_num) (Real.rpow_pos_of_pos hcB _)
  have hbP : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → ∀ (ℓ : ℝ) (a b : Zd d (sz.L n)),
      ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) ≤ (sz.Bctl n u) ^ (1 / 5 : ℝ) * STprof sz n u D ℓ a b := by
    filter_upwards [hBd, hNcB] with n hn hN u hsu hut ℓ a b
    exact ST_bP_lower sz hd n hcB hD.le (hn u ((hs n).trans hsu) hut).1 hN a b
  -- (E1) the weak law
  have hsmallE1 : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n →
      ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ) ≤ δ₀ := by
    filter_upwards [hBd, ST_size_pow_small sz hsize (a := ε₁ - c / 4) (δ := δ₀)
      (by linarith) hδ₀] with n hn hsm u hsu hut
    have hb := (hn u ((hs n).trans hsu) hut).2
    have hN0 : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hb0 : 0 ≤ sz.Bctl n u := ((mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d)))).trans (hn u ((hs n).trans hsu) hut).1
    calc ((sz.size n : ℕ) : ℝ) ^ ε₁ * (sz.Bctl n u) ^ (1 / 4 : ℝ)
        ≤ ((sz.size n : ℕ) : ℝ) ^ ε₁ * (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb0 hb (by norm_num))
            (Real.rpow_nonneg hN0 _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (ε₁ - c / 4) := by
          rw [← Real.rpow_mul hN0, ← Real.rpow_add' hN0 (by linarith)]; congr 1; ring
      _ ≤ δ₀ := hsm
  have hE1 := ST_event_weakg d sz (mk sz z) (law sz) hG' s t T K hs hsT hTt hK0 (CK' + 5)
    (by linarith : (0 : ℝ) ≤ CK' + 5) hcardIdx hS1W ε₁ δ₀ hε₁pos hsmallE1
  have hst' : ∀ n, s n ≤ t n := fun n => (hsT n).trans (hTt n)
  have hKcap : ∀ᶠ n in atTop, ∀ u, s n ≤ u → u ≤ t n → 0 ≤ Kf n u ∧
      Kf n u ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 * ellT (sz.L n) (sz.lam n) u := by
    filter_upwards [hKok.1] with n hn u h1 h2
    exact ⟨(hn u h1 h2).1, (hn u h1 h2).2.2⟩
  -- (E2) the initial value
  obtain ⟨Di, hDidef⟩ : ∃ Di : ℝ, Di = (D + 3) / 𝔠 := ⟨_, rfl⟩
  have hDipos : 0 < Di := by rw [hDidef]; positivity
  have hWDi : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-Di) ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) := by
    filter_upwards [hband] with n hn
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
    calc ((sz.W n : ℕ) : ℝ) ^ (-Di) ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-Di) :=
          Real.rpow_le_rpow_of_nonpos hNc hn (by linarith)
      _ = ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) := by
          rw [← Real.rpow_mul hN0.le]; congr 1; rw [hDidef]; field_simp
  have hcmp : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ ε₁ *
      ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
        STWB sz n (s n) (zdistInf d (sz.L n) (i.2 0 - i.2 1)) *
        Real.exp (-(((zdistInf d (sz.L n) (i.2 0 - i.2 1) : ℕ) : ℝ) /
          ellT (sz.L n) (sz.lam n) (s n)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-Di)) ≤
      a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := by
    filter_upwards [hBd, hbP, hWDi, hKok.1] with n hn hP hW hKc i
    have hKs := (hKc (s n) le_rfl (hst' n)).1
    have hbs0 : 0 ≤ sz.Bctl n (s n) := (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg
      (Nat.cast_nonneg _) d))).trans (hn (s n) (hs n) (hst' n)).1
    have h := ST_init_cmp sz n (u := s n) (D := D) (ℓ := Kf n (s n)) (Di := Di)
      (X := ((sz.size n : ℕ) : ℝ) ^ ε₁) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hKs hbs0 i
      (hW.trans (hP (s n) le_rfl (hst' n) _ _ _))
    rw [ha₀def, hΛdef, hXdef]
    exact h
  have hE2 := ST_event_initg d sz (mk sz z) (law sz) hG' s T K hs hsT hK0 hDec 3
    (by norm_num) hcardLab3 ε₁ hε₁pos Di hDipos D Kf a₀ hcmp
  -- (E3), (E4) the light-weight term and the quadratic variation
  have hE3 := ST_event_lwg d law Flow mk T0 hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 κm z hκ hε h𝔡 hflow hSpec hG' s t T K cB c Kf
    hs htT hS1W hcB hc hBd hKcap hinv hsT hTt hK0 (CK' + 5) (by linarith) hcardLab ε₁ hε₁pos Λ hΛX D hD
  have hE4 := ST_event_mgg d law Flow mk T0 hFl hLWT hEMe hd sz κ ε 𝔡 𝔠 κm z hκ hε h𝔡 hflow hSpec hG' s t T K cB c Kf
    hs htT hS1W hcB hc hBd hKcap hinv hsT hTt hK0 (CK' + 5) (by linarith) hcardF2 ε₁ hε₁pos Λ hΛX2 D hD
  -- the floors of the martingale event and of the remainder
  have hρ : ∀ᶠ n in atTop, ∀ i : STLab sz n, ((sz.size n : ℕ) : ℝ) ^ (-Dm) ≤ ρ₁ n *
      STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) ^ 2 := by
    filter_upwards [hbP, hsize.eventually (eventually_ge_atTop 1)] with n hP hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    rw [ST_gridTime_zero]
    have h1 := ST_floor_sq (q := Λ n) hN1' (hΛ1 n) (hP (s n) le_rfl (hst' n) (Kf n (s n))
      (i.2 0) (i.2 1)) hDm2
    rw [hρ₁def]
    refine h1.trans (le_of_eq ?_)
    simp only
    ring
  have hrem : ∀ᶠ n in atTop, ∀ i : STLab sz n, ∀ᵐ ω ∂((mk sz z).Pp), ∀ k, k ≤ K n →
      ‖Rem n i k ω‖ ≤ a₀ n *
        STprof sz n (gridTime s T K n 0) D (Kf n (gridTime s T K n 0)) (i.2 0) (i.2 1) := by
    filter_upwards [hrem0, hbP, hsize.eventually (eventually_ge_atTop 1)] with n hr hP hN1 i
    have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    rw [ST_gridTime_zero]
    refine (hr i).mono fun ω hω k hk => (hω k hk).trans ?_
    have hts : T n - s n ≤ 1 := by have := hT1 n; have := hs n; linarith
    have hsq := ST_sqrt_gridStep_le s T K n hN1' hts (hKbig' n)
    have hP0 := hP (s n) le_rfl (hst' n) (Kf n (s n)) (i.2 0) (i.2 1)
    have hb5 : 0 ≤ (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) :=
      (Real.rpow_nonneg hN0.le _).trans hP0
    calc ((sz.size n : ℕ) : ℝ) ^ C₀ * Real.sqrt (gridStep s T K n)
        ≤ ((sz.size n : ℕ) : ℝ) ^ C₀ * ((sz.size n : ℕ) : ℝ) ^ (-CK' / 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ (C₀ + -CK' / 2) := (Real.rpow_add hN0 _ _).symm
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-(D + 3)) :=
          Real.rpow_le_rpow_of_exponent_le hN1' (by linarith)
      _ ≤ (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := hP0
      _ ≤ Λ n * ((sz.Bctl n (s n)) ^ (1 / 5 : ℝ) *
            STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1)) :=
          le_mul_of_one_le_left hb5 (hΛ1 n)
      _ = a₀ n * STprof sz n (s n) D (Kf n (s n)) (i.2 0) (i.2 1) := by
          rw [ha₀def]; simp only; ring
  have hgp := ST_good_probg d sz (mk sz z) hsize s T K D Kf δ₀ Λ a₀ a₀ ρ₁ Mart Rem hE1 hE2 hE3 hE4
    (fun n => ST_gridStep_nonneg s T K n (hsT n)) D' Dm ε₁ hD' hDm1
    (hmart0 ε₁ hε₁pos) hΛX hρ hident hrem hcardLab3
  -- the size constants of the closure and of the final comparison
  obtain ⟨cstar, hcstardef⟩ : ∃ cstar : ℝ, cstar = 3 + 3 * κm⁻¹ := ⟨_, rfl⟩
  have hcstar0 : 0 < cstar := by
    rw [hcstardef]; have := hSpec.1; positivity
  have hP1 : ∀ᶠ n in atTop, 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60) < 1 := by
    filter_upwards [ST_size_pow_small sz hsize (a := 3 * ε₁ - c / 60) (δ := 1 / (24 * cstar))
      (by linarith) (by positivity)] with n hn
    calc 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60)
        ≤ 12 * cstar * (1 / (24 * cstar)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
      _ < 1 := by norm_num
  have hP2 : ∀ᶠ n in atTop, 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ := by
    filter_upwards [ST_size_pow_big sz hsize (a := τ - 3 * ε₁) (M := 12 * cstar)
      (by linarith), hsize.eventually (eventually_ge_atTop 1)] with n hn hN1
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
    calc 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ - 3 * ε₁) * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hN0.le _)
      _ = ((sz.size n : ℕ) : ℝ) ^ τ := by rw [← Real.rpow_add hN0]; congr 1; ring
  filter_upwards [hgp, hBd, hP1, hP2, hKok.1, hKok.2, hCon, hWO,
    hsize.eventually (eventually_ge_atTop 1), hnew] with n hgpn hbdn hP1n hP2n hKc hKmono hconn hwon hN1 hnewn
  have hN1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hmI : 0 < ((mk sz z).m n).im := lt_of_lt_of_le hSpec.1 (hSpec.2.1 n)
  have hlam : 0 ≤ sz.lam n :=
    (lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hwon.1).le
  have hcstar : 3 + 3 * (((mk sz z).m n).im)⁻¹ ≤ cstar := by
    rw [hcstardef]; exact Step2EventsGen_cstar_le hSpec n
  have hc₁0 : 0 ≤ 3 + 3 * (((mk sz z).m n).im)⁻¹ := by positivity
  have hlt1 : ∀ u, u ≤ t n → u < 1 := fun u hu =>
    lt_of_le_of_lt (hu.trans (htT n)) (hTlt1 n)
  have hbpos : ∀ u, u ≤ t n → 0 < sz.Bctl n u := fun u hu => STBctl_pos sz n (hlt1 u hu)
  have hbtn := hbdn (t n) ((hs n).trans (hst' n)) le_rfl
  have hbt1 : sz.Bctl n (t n) ≤ 1 :=
    hbtn.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  have hbT := hbdn (T n) (hT0 n) (hTt n)
  have hb1 : sz.Bctl n (T n) ≤ 1 :=
    hbT.2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1' (by linarith))
  -- the closure `hΛq`
  have hΛq : (3 + 3 * (((mk sz z).m n).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n) *
      (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) < 1 := by
    have hX := hX1 n
    have hΛe : Λ n = 2 * X n := by rw [hΛdef]
    have h12 : (Λ n) ^ 2 * (1 + Λ n) ≤ 12 * (X n) ^ 3 := by
      rw [hΛe]; nlinarith [mul_nonneg (sub_nonneg.2 hX) (sq_nonneg (X n))]
    have hXe : (X n) ^ 3 = ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by
      rw [hXdef]; simp only
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hbt60 : (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
      calc (sz.Bctl n (t n)) ^ (1 / 60 : ℝ)
          ≤ (((sz.size n : ℕ) : ℝ) ^ (-c)) ^ (1 / 60 : ℝ) :=
            Real.rpow_le_rpow (hbpos _ le_rfl).le hbtn.2 (by norm_num)
        _ = ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
    have hΛ0 : 0 ≤ (Λ n) ^ 2 * (1 + Λ n) := by have := hΛ1 n; positivity
    calc (3 + 3 * (((mk sz z).m n).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n) *
          (sz.Bctl n (t n)) ^ (1 / 60 : ℝ)
        = (3 + 3 * (((mk sz z).m n).im)⁻¹) * ((Λ n) ^ 2 * (1 + Λ n)) *
          (sz.Bctl n (t n)) ^ (1 / 60 : ℝ) := by ring
      _ ≤ cstar * (12 * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)) *
          ((sz.size n : ℕ) : ℝ) ^ (-c / 60) := by
          refine mul_le_mul (mul_le_mul hcstar (by rw [← hXe]; exact h12) hΛ0 hcstar0.le)
            hbt60 (Real.rpow_nonneg (hbpos _ le_rfl).le _) (by positivity)
      _ = 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁ - c / 60) := by
          have : (3 * ε₁ - c / 60) = 3 * ε₁ + (-c / 60) := by ring
          rw [this, Real.rpow_add hN0]; ring
      _ < 1 := hP1n
  -- the probability transfer
  have hJmeas : ∀ (n : ℕ) (u : ℝ), Measurable (fun H : Matrix (Idx d (sz.L n) (sz.W n))
      (Idx d (sz.L n) (sz.W n)) ℂ => STJhatMg (mk sz z) n D (Kf n u) u H) :=
    fun n u => Step2EventsGen_STJhatMg_measurable hG' n u D (Kf n u)
  have hmodel := Step2EventsGen_model_le_path (mk sz z) (law sz) hlaw s T K hs hsT hK0 n
    (fun n u H => STJhatMg (mk sz z) n D (Kf n u) u H)
    (fun n u _ => ((1 - s n) / (1 - u)) ^ (3 * C + 1) * (sz.Bctl n u) ^ (1 / 5 : ℝ))
    hJmeas (fun n u => measurable_const) τ
    {ω | ¬ STGoodAtg (mk sz z) s T K n D (fun j => Kf n (gridTime s T K n j)) (Λ n) δ₀
      (a₀ n) (a₀ n) (ρ₁ n) (Mart n) (Rem n) ω} (by
      intro ω hω hg
      -- the engine on the good event
      have hKs : ∀ j, j ≤ K n → s n ≤ gridTime s T K n j ∧ gridTime s T K n j ≤ T n := fun j hj =>
        ST_gridTime_mem s T K n j (hsT n) (hK0 n) hj
      have hKf0 : ∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s T K n j) := fun j hj =>
        (hKc _ (hKs j hj).1 ((hKs j hj).2.trans (hTt n))).1
      have hKfL : ∀ j, j ≤ K n → Kf n (gridTime s T K n j) ≤ ((sz.L n : ℕ) : ℝ) := fun j hj =>
        (hKc _ (hKs j hj).1 ((hKs j hj).2.trans (hTt n))).2.1
      have hTmono : ∀ j k, j ≤ k → k ≤ K n →
          tailT d (sz.L n) (sz.lam n) (gridTime s T K n j) (Kf n (gridTime s T K n j)) ≤
            tailT d (sz.L n) (sz.lam n) (gridTime s T K n k) (Kf n (gridTime s T K n k)) :=
        fun j k hjk hk => hKmono _ _ (hKs j (hjk.trans hk)).1
          (ST_gridTime_mono s T K n (hsT n) hjk) ((hKs k hk).2.trans (hTt n))
      have hsmall : ∀ k, k ≤ K n →
          (3 + 3 * (((mk sz z).m n).im)⁻¹) * (Λ n) ^ 2 *
            (1 + Λ n + Real.log ((1 - s n) / (1 - gridTime s T K n k))) *
            ((1 - s n) / (1 - gridTime s T K n k)) ^ (3 * C) *
            (sz.Bctl n (gridTime s T K n k)) ^ (1 / 30 : ℝ) < 1 := by
        intro k hk
        have hu1 := hlt1 (gridTime s T K n k) ((hKs k hk).2.trans (hTt n))
        have hu2 := hKs k hk
        have hs1 : 0 < 1 - s n := by
          have := hlt1 (s n) (hst' n); linarith
        have hr1 : 1 ≤ (1 - s n) / (1 - gridTime s T K n k) := by
          rw [le_div_iff₀ (by linarith)]; linarith [hu2.1]
        have hrb : (1 - s n) / (1 - gridTime s T K n k) ≤ (sz.Bctl n (t n)) ^ (-𝔠d) := by
          have ht1 : 0 < 1 - t n := by have := hlt1 (t n) le_rfl; linarith
          have hcon1 := hconn.1
          have hcon2 := hconn.2
          calc (1 - s n) / (1 - gridTime s T K n k) ≤ (1 - s n) / (1 - t n) :=
                div_le_div_of_nonneg_left hs1.le ht1 (by linarith [(hu2.2).trans (hTt n)])
            _ = ((1 - t n) / (1 - s n))⁻¹ := (inv_div _ _).symm
            _ ≤ ((sz.Bctl n (t n)) ^ 𝔠d)⁻¹ :=
                inv_anti₀ (Real.rpow_pos_of_pos (hbpos _ le_rfl) _) hcon1
            _ = (sz.Bctl n (t n)) ^ (-𝔠d) := (Real.rpow_neg (hbpos _ le_rfl).le _).symm
        exact ST_hsmall_aux (c₁ := 3 + 3 * (((mk sz z).m n).im)⁻¹) (Λ := Λ n) (q := Λ n)
          hC.le (by have := hΛ1 n; linarith) hc₁0 hr1 hrb
          (hbpos _ ((hKs k hk).2.trans (hTt n)))
          (STBctl_mono sz n ((hKs k hk).2.trans (hTt n)) (hlt1 (t n) le_rfl)) hbt1 h3 hΛq
      have ha₀0 : 0 ≤ a₀ n := by
        rw [ha₀def]
        exact mul_nonneg (by have := hΛ1 n; linarith) (Real.rpow_nonneg (hbpos _ (hst' n)).le _)
      have hρ₁0 : 0 ≤ ρ₁ n := by rw [hρ₁def]; exact sq_nonneg _
      have hq0 : 0 ≤ Λ n := by have := hΛ1 n; linarith
      have hae : a₀ n ≤ Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) := le_of_eq (by rw [ha₀def])
      have hρe : ρ₁ n ≤ (Λ n * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2 := le_of_eq (by rw [hρ₁def])
      have hb_eng := (ST_good_engineg sz (mk sz z) s T K n D Kf κm (Λ n) δ₀ C (a₀ n) (a₀ n) (ρ₁ n) (Λ n)
        (hK0 n) (hs n) (hsT n) (hT1 n) hD.le hSpec hlam (hΛ1 n) hC.le ha₀0 ha₀0 hρ₁0 hnewn hKf0 hKfL
        hTmono hb1 hq0 hae hae hρe hsmall (Mart n) (Rem n) ω (fun j _ => hHerm s T K n j ω) hg).2 (K n) le_rfl
      rw [gridTime_last s T K n (hK0 n)] at hb_eng
      have hr1 : 1 ≤ (1 - s n) / (1 - T n) := by
        rw [le_div_iff₀ (by linarith [hT1 n])]; linarith [hsT n]
      have hfinal := ST_final_cmp (c₁ := 3 + 3 * (((mk sz z).m n).im)⁻¹) (Λ := Λ n)
        (q := Λ n) (C := C) (r := (1 - s n) / (1 - T n)) (b := sz.Bctl n (T n))
        (M := ((sz.size n : ℕ) : ℝ) ^ τ) (by have := hΛ1 n; linarith) hc₁0 hr1
        (hbpos _ (hTt n)).le (by
          have hΛe : Λ n = 2 * X n := by rw [hΛdef]
          have hX := hX1 n
          have h12 : (Λ n) ^ 2 * (1 + Λ n) ≤ 12 * (X n) ^ 3 := by
            rw [hΛe]; nlinarith [mul_nonneg (sub_nonneg.2 hX) (sq_nonneg (X n))]
          have hXe : (X n) ^ 3 = ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by
            rw [hXdef]; simp only
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
          have hΛ0 : 0 ≤ (Λ n) ^ 2 * (1 + Λ n) := by have := hΛ1 n; positivity
          calc (3 + 3 * (((mk sz z).m n).im)⁻¹) * (Λ n) ^ 2 * (1 + Λ n)
              = (3 + 3 * (((mk sz z).m n).im)⁻¹) * ((Λ n) ^ 2 * (1 + Λ n)) := by ring
            _ ≤ cstar * (12 * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁)) :=
                mul_le_mul hcstar (by rw [← hXe]; exact h12) hΛ0 hcstar0.le
            _ = 12 * cstar * ((sz.size n : ℕ) : ℝ) ^ (3 * ε₁) := by ring
            _ ≤ _ := hP2n)
      -- `hω : N^τ Z < Ĵ`
      have hω' : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
          (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) <
          STJhatMg (mk sz z) n D (Kf n (T n)) (T n) ((mk sz z).Hpath s T K n (K n) ω) := hω
      exact absurd hω' (not_lt.2 (hb_eng.trans hfinal)))
  refine le_trans (measure_mono ?_) (hmodel.trans hgpn)
  intro ω hω
  obtain ⟨i, hi⟩ := hω
  have hPpos := ST_STprof_pos sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)
  have hratio : ‖(mk sz z).L n (T n) i.1 i.2 ω - (mk sz z).K n (T n) i.1 i.2‖ /
      STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) ≤
      STJhatMg (mk sz z) n D (Kf n (T n)) (T n) (Hm n (T n) ω) := by
    unfold STJhatMg
    rw [← Step2EventsGen_STLKMg_eq (mk sz z) hLM n (T n) i.1 i.2 ω]
    exact Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKMg (mk sz z) n (T n) (Hm n (T n) ω) p.1 p.2‖ /
        STprof sz n (T n) D (Kf n (T n)) (p.2 0) (p.2 1)) (Finset.mem_univ i)
  rw [div_le_iff₀ hPpos] at hratio
  show ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) <
    STJhatMg (mk sz z) n D (Kf n (T n)) (T n) (Hm n (T n) ω)
  have hi' : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)) <
      ‖(mk sz z).L n (T n) i.1 i.2 ω - (mk sz z).K n (T n) i.1 i.2‖ := by
    rw [hTD n]; exact hi
  have h2 : ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
      (sz.Bctl n (T n)) ^ (1 / 5 : ℝ)) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) <
      STJhatMg (mk sz z) n D (Kf n (T n)) (T n) (Hm n (T n) ω) *
        STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1) := by
    calc _ = ((sz.size n : ℕ) : ℝ) ^ τ * (((1 - s n) / (1 - T n)) ^ (3 * C + 1) *
          (sz.Bctl n (T n)) ^ (1 / 5 : ℝ) * STprof sz n (T n) D (Kf n (T n)) (i.2 0) (i.2 1)) := by
          ring
      _ < _ := hi'
      _ ≤ _ := hratio
  exact lt_of_mul_lt_mul_right h2 hPpos.le

/-- **All time sections** (band `ST_selfImprove`, `Step2Iterate.lean:700`): the self-improving bound of one step holds per time
(`STSelfImpgL`, `(eq:Gronwall_dervJuD)` for every `u ∈ [s,t]`). -/
theorem ST_selfImproveg (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hFl : Step2EventsGen_Flow d Flow T0) (hLWT : STLWTgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0)
    (hEMe : STEMn2ExpgL d law Flow (fun sz z => (mk sz z).toFlowFM) T0) (hd : 0 < d)
    {sz : Sizes d} {κ ε 𝔡 𝔠 κm : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) {z : ℕ → ℂ}
    (hflow : Flow sz κ ε 𝔠 𝔡 z) (hSpec : DecayGen_Spec (mk sz z).toFlowFM κm)
    (hG : Step2EventsGen_Grid (mk sz z) (law sz))
    (hHerm : ∀ (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ sz), ((mk sz z).Hpath s t K n k ω).IsHermitian)
    {s t : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (htT : ∀ n, t n ≤ T0 sz z n)
    {C δ₀ 𝔠d : ℝ} (hC : 0 < C) (hδ₀ : 0 < δ₀)
    (hnew : ∀ᶠ n in atTop, Step2IterGen_NewKLKAtN (mk sz z) n C δ₀) (hmart : STGridMartgL d Flow mk T0)
    (h𝔠d : 0 < 𝔠d) (h3 : (3 * C + 1) * 𝔠d ≤ 1 / 60)
    (hDec : STDecaygL (mk sz z).toFlowFM (law sz) s) (hCon : STConStInd sz 𝔠d s t)
    (hS1W : STStep1WeakgL (mk sz z).toFlowFM (law sz) s t) {cB c : ℝ} (hcB : 0 < cB) (hc : 0 < c)
    (hBd : ∀ᶠ n in atTop, ∀ u : ℝ, 0 ≤ u → u ≤ t n →
      cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n u ∧ sz.Bctl n u ≤ ((sz.size n : ℕ) : ℝ) ^ (-c))
    (Kf : ℕ → ℝ → ℝ) (hKok : STScaleOk sz s t Kf) (hinv : STScaleInvgL (mk sz z).toFlowFM (law sz) s t Kf) :
    STSelfImpgL (mk sz z).toFlowFM (law sz) (3 * C + 1) s t Kf := by
  intro D hD
  exact Step2EventsGen_PT_of_sections (law sz) (V := fun n => STLab sz n) hst
    (fun n p ω => ‖(mk sz z).L n (p.1 : ℝ) p.2.1 p.2.2 ω - (mk sz z).K n (p.1 : ℝ) p.2.1 p.2.2‖)
    (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (3 * C + 1) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
      STprof sz n (p.1 : ℝ) D (Kf n (p.1 : ℝ)) (p.2.2 0) (p.2.2 1))
    (fun tt => ST_selfImprove_sectiong d law Flow mk T0 hFl hLWT hEMe hd hκ hε h𝔡 hflow hSpec hG hHerm hs htT hC hδ₀
      hnew hmart h𝔠d h3 hDec hCon hS1W hcB hc hBd Kf hKok hinv tt D hD)

/-! ## 4. Compiled nonempty instances (targets 1-3; CLAUDE.md §4 step 2)

Data: the band carrier `bandStep2Mat sz0 (STflowE z0)` (`d = 3`, `sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; flow `z0`,
`κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`), the law `seqP sz0`, the window `[0, 1/16]`; for the engine `n = 100`, `E = 0`, `K ≡ 16`.  The band
privates of `Induction/Step2Core.lean` are opened by `open private` (precedent `Chain/DecayGen.lean:45-47`).  What stays a hypothesis of
an example is another gate's pin or a stochastic premise (`STLWTgL`, `STEMn2ExpgL`, `STGridMartgL`, `STDecaygL`, `STStep1WeakgL`,
`STScaleInvgL`, `STSelfImpgL`, `STGridMartgL`, the class `Step2IterGen_NewKLKAtN` at `C = 1`, the good event `STGoodAtg`). -/

end RBM.BA

end
