/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.Step5Gen
import RBM3D.Induction.Step5Cases
import RBM3D.Induction.WardII

/-!
# The Step 5 kit over the carrier: flow facts, cases (i)-(iv), assembly, Ward term (T2462, U4s1a)

Additive restatement of `Induction/Step5Kit.lean`, `Induction/Step5Cases.lean` and
`Induction/WardII.lean` (none edited) over a carrier tuple `(law, Flow, mk, T0)` of
`Chain/Step5Gen.lean` (the shape `STIngR5gL`).  Paper: arXiv:2507.20274, Step 5 is
`1_2:1379-1388`, its proof `3_5:1935-2383`.  The size-level lemmas of the band files
(`st5_compare_I`, `st5_compare_IV`, `st5_compare_IIIa`, `st5_compare_IIIb`, `st5_A15_le`,
`st5_polylog_le_W`, ...) are reused as they are; what mentions the law is restated under the
stem `Step5CasesGen_` (private).  Every size-level read is at `sz.lam` (UBA-C1); no kernel
coupling and no comparison hypothesis occurs in this file (Amend 1: that is target 9, U4s1b).

* **Target 1.** `Step5CasesGen_FlowFacts` (the spectral and size facts a flow carries:
  admissibility, `T0 < 1`, `κm ≤ Im m`, `η_t = (1 - t) Im m`) and its band result
  `step5CasesGen_flowFacts_band`.
* **Targets 2-4.** `ST_step5_caseI_of_pinsgL`, `ST_step5_caseII_of_pinsgL`,
  `ST_step5_caseIII_of_pfgL`: cases (i)-(iii) from their ingredient pins.
* **Target 5.** `stStep5IVgL_holds`: case (iv) proved.  `W^{-d}B_{u,0} ≤ 1` on `[s,t]` comes from
  `STConStInd` and `STBctl_mono` (size level, as `Bctl_le_one_of_conStInd`,
  `BA/Step1Fam.lean:382`), not from the spectral `st5_Bctl_le_one`.
* **Target 6.** `ST_step5_assemblygL`: the endpoint `u = t`.
* **Target 7.** `Step5CasesGen_WardIdent` (the `(zYU1)` identity as a carrier datum, D1), its band
  result `step5CasesGen_wardIdent_band` (from `stWardII_identity`) and `stWardIIgL_of`.

Ported from `Induction/Step5Kit.lean` (`st5_prec_mono` `:45`, `st5_prec_cover` `:63`,
`st5_prec_of_isEmpty` `:280`, `ST_step5_assembly` `:79`, `ST_step5_caseI_of_pins` `:292`,
`stStep5IV_holds` `:549`), `Induction/Step5Cases.lean` (`st5_prec_mono'` `:39`,
`ST_step5_caseIII_of_pf` `:311`, `ST_step5_caseII_of_pins` `:542`) and `Induction/WardII.lean`
(`wardII_prec_scale` `:256`, `stWardII_holds` `:269`) of this project; the d = 1 and d = 2
projects are not used.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false

open private wardII_Bctl_le from RBM3D.Induction.WardII

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The `Prec` calculus at a law `μ` -/

section PrecLaw

variable {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ)

/-- `ξ ≺ ζ₁`, `ζ₁ ≤ c ζ₂` eventually, `ζ₂ ≥ 0` imply `ξ ≺ ζ₂` (`st5_prec_mono`, `Step5Kit:45`, at the law `μ`). -/
private theorem Step5CasesGen_prec_mono (hsz : sz.SizeTendsto) {U : ℕ → Type*}
    {ξ ζ₁ ζ₂ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ℝ}
    (h : PrecL sz μ ξ ζ₁) (hle : ∀ᶠ n in atTop, ∀ u ω, ζ₁ n u ω ≤ c * ζ₂ n u ω)
    (hζ₂ : ∀ n u ω, 0 ≤ ζ₂ n u ω) : PrecL sz μ ξ ζ₂ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle, (tendsto_size sz hsz).eventually (eventually_le_rpow c (half_pos hτ))] with n hn hc
  intro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (c * ζ₂ n u ω) := mul_le_mul_of_nonneg_left (hn u ω) hpos
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ n u ω) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc (hζ₂ n u ω)) hpos
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact lt_of_le_of_lt h1 hu

/-- `ξ ≺ ζ₁` and `ζ₁ ≤ N^τ ζ₂` eventually for every `τ > 0` give `ξ ≺ ζ₂` (`st5_prec_mono'`, `Step5Cases:39`, at the law `μ`). -/
private theorem Step5CasesGen_prec_mono' {U : ℕ → Type*} {ξ ζ₁ ζ₂ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : PrecL sz μ ξ ζ₁)
    (hle : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ u ω, ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω) :
    PrecL sz μ ξ ζ₂ := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle (τ / 2) (half_pos hτ)] with n hn
  intro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hpos : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
    calc ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₁ n u ω
        ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ₂ n u ω) :=
          mul_le_mul_of_nonneg_left (hn u ω) hpos
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ₂ n u ω := by
          rw [← mul_assoc, UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ]
  exact lt_of_le_of_lt h1 hu

/-- Two index families that cover the index set: `≺` on both gives `≺` on the whole (`st5_prec_cover`, `Step5Kit:63`). -/
private theorem Step5CasesGen_prec_cover (hsz : sz.SizeTendsto) {U V₁ V₂ : ℕ → Type*}
    {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (φ₁ : ∀ n, V₁ n → U n) (φ₂ : ∀ n, V₂ n → U n)
    (hcov : ∀ n u, (∃ v, φ₁ n v = u) ∨ (∃ v, φ₂ n v = u))
    (h₁ : PrecL sz μ (fun n v ω => ξ n (φ₁ n v) ω) (fun n v ω => ζ n (φ₁ n v) ω))
    (h₂ : PrecL sz μ (fun n v ω => ξ n (φ₂ n v) ω) (fun n v ω => ζ n (φ₂ n v) ω)) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_subset_union (tendsto_size sz hsz) h₁ h₂ fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun n => ?_⟩
  intro ω ⟨u, hu⟩
  rcases hcov n u with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact Or.inl ⟨v, hu⟩
  · exact Or.inr ⟨v, hu⟩

/-- An empty index set gives `≺` for free (`st5_prec_of_isEmpty`, `Step5Kit:280`). -/
private theorem Step5CasesGen_prec_of_isEmpty {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ}
    (h : ∀ n, IsEmpty (U n)) : PrecL sz μ ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => Eventually.of_forall fun n => ?_
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
  intro u _
  exact (h n).false u

/-- A positive deterministic factor passes through `≺` (`wardII_prec_scale`, `WardII:256`, at the law `μ`). -/
private theorem Step5CasesGen_prec_scale {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ}
    (hc : ∀ n p, 0 < c n p) (h : PrecL sz μ ξ' ζ) (hle : ∀ n p ω, ξ n p ω ≤ c n p * ξ' n p ω) :
    PrecL sz μ ξ (fun n p ω => c n p * ζ n p ω) := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Filter.Eventually.of_forall fun n ω ⟨u, hu⟩ => ⟨u, ?_⟩⟩
  have h1 : c n u * (((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) < c n u * ξ' n u ω := by
    calc c n u * (((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) = ((sz.size n : ℕ) : ℝ) ^ τ * (c n u * ζ n u ω) := by ring
      _ < ξ n u ω := hu
      _ ≤ c n u * ξ' n u ω := hle n u ω
  exact lt_of_mul_lt_mul_left h1 (hc n u).le

end PrecLaw

/-! ## 2. Target 1: the flow facts of a carrier tuple -/

/-- **Target 1** (`T2462_FlowFacts`): the facts a flow carries.  At every `κ > 0`, one `κm > 0`: admissible sizes, `T0 < 1`,
`κm ≤ Im m` and `η_t = (1 - t) Im m` (band: `STFlow`, `lemT_lt_one`, `st5_mE_im_ge` with the semicircle domain fact,
`etaT_eq_etaOf`; BA: `BAFlow`, `EMn2BA_T0_lt_one`, `EMn2BA_mF_data`, the `eta` field of `baFM`). -/
def Step5CasesGen_FlowFacts (d : ℕ) (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∃ κm : ℝ, 0 < κm ∧
    ∀ (sz : Sizes d) (ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Flow sz κ ε 𝔠 𝔡 z →
      sz.Admissible 𝔠 𝔡 ∧ (∀ n, T0 sz z n < 1) ∧ (∀ n, κm ≤ ((mk sz z).m n).im) ∧
        ∀ (n : ℕ) (t : ℝ), (mk sz z).eta n t = (1 - t) * ((mk sz z).m n).im

/-- The semicircle domain facts of a band flow: `Im z_n > 0` and `|E(z_n)| ≤ 2 - κ` (Lemma 2.8, `lemma28_quant`). -/
private theorem Step5CasesGen_flow_dom {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im ∧ |lemE (z n)| ≤ 2 - κ := by
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hflow.2 n).2.1
  exact ⟨him, (lemma28_quant hκ him (hflow.2 n).2.2 (hflow.2 n).1).1⟩

/-- **Target 1, band result** (`T2462_FlowFacts_band`): the band tuple `(STFlow, bandFM ∘ STflowE, lemT)` satisfies the flow
facts, with `κm = √(2κ)/2`. -/
theorem step5CasesGen_flowFacts_band (d : ℕ) :
    Step5CasesGen_FlowFacts d (fun sz κ ε 𝔠 𝔡 z => STFlow sz κ ε 𝔠 𝔡 z) (fun sz z => bandFM sz (STflowE z))
      (fun _ z n => lemT (z n)) := by
  intro κ hκ
  refine ⟨Real.sqrt (2 * κ) / 2, by positivity, ?_⟩
  intro sz ε 𝔠 𝔡 z hflow
  exact ⟨hflow.1, fun n => lemT_lt_one (Step5CasesGen_flow_dom hκ hflow n).1,
    fun n => st5_mE_im_ge hκ (Step5CasesGen_flow_dom hκ hflow n).2, fun n t => rfl⟩

/-! ## 3. Target 6: the assembly -/

/-- **Target 6** (`T2462_assembly`): the uniform Step-5 conclusion gives `(Eq:Gdecay)` and `(Eq:Gdecay+s<g)` at the time
sequence `t` (the endpoint `u = t` of the index; band `ST_step5_assembly`, `Step5Kit:79`). -/
theorem ST_step5_assemblygL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ)
    (hst : ∀ n, s n ≤ t n) (h : STStep5ConclgL C μ s t) : STDecaygL C μ t ∧ STDecayStronggL C μ t := by
  obtain ⟨hW, hS⟩ := h
  refine ⟨fun D hD => ?_, fun D hD => ?_⟩
  · have := StochDomAt.precomp_param (hW D hD)
      (fun n (p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))) =>
        ((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p))
    simp only [Real.rpow_zero, one_mul] at this
    exact this
  · exact StochDomAt.precomp_param (hS D hD)
      (fun n (p : {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n}) =>
        (⟨((⟨t n, hst n, le_rfl⟩ : TimeIcc s t n), p.1), p.2⟩ :
          {_p : TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) // sz.lam n ^ 2 ≤ 1 - t n}))

/-! ## 4. Target 7: the Ward term `(zYU1)` -/

/-- **Target 7, D1** (`T2462_WardIdent`): the `(zYU1)` identity (`3_5:2257-2262`) as a carrier datum, mixed charges, every sample:
`(𝓛-𝒦)_{u,σ,a} - [Q^{(1)}(𝓛-𝒦)_{u,σ}]_a = Im (𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`, `N = (WL)^d` (band: `stWardII_identity`). -/
def Step5CasesGen_WardIdent {d : ℕ} {sz : Sizes d} (C : FlowFM sz) : Prop :=
  ∀ (n : ℕ) (u : ℝ), 0 ≤ u → u < 1 → ∀ (ω : sz.SeqΩ) (σ : Fin 2 → Bool), σ 0 ≠ σ 1 →
    ∀ a : Fin 2 → Zd d (sz.L n),
      (C.L n u σ a ω - C.K n u σ a) -
          zeroModeSet d (sz.L n) {0} (fun a' => C.L n u σ a' ω - C.K n u σ a') a =
        (((C.L n u (fun _ : Fin 1 => true) (fun _ => a 1) ω -
            C.K n u (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
          ((((sz.size n : ℕ) : ℂ)) * (C.eta n u : ℂ))

/-- **Target 7, the Ward term over a carrier tuple** (`T2462_stWardIIgL_of`; band `stWardII_holds`, `WardII:269`): the identity,
the averaged local law `STAvgUgL` inside `STStep2ConclgL`, and `W^{-d}B_{u,0} ≤ 2 A⁻¹` in regime (ii) give `(zYU1)`. -/
theorem stWardIIgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 →
      (∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
        Step5CasesGen_WardIdent (mk sz z)) →
        STWardIIgL d law Flow mk T0 := by
  intro hF hW hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨hadm, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have hident := hW sz κ ε 𝔠 𝔡 z hκ hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hev := st5_eventually_A_ge_one sz hadm.2.1 hadm.2.2.2.2
  have hu0 : ∀ n (u : TimeIcc s t n), 0 ≤ (u : ℝ) := fun n u => (hs0 n).trans u.2.1
  have hu1 : ∀ n (u : TimeIcc s t n), (u : ℝ) < 1 := fun n u => lt_of_le_of_lt u.2.2 (ht1 n)
  have hηpos : ∀ n (u : TimeIcc s t n), 0 < (mk sz z).eta n (u : ℝ) := fun n u => by
    rw [hη]
    exact mul_pos (by linarith [hu1 n u]) (lt_of_lt_of_le hκm (hIm n))
  have hN : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  -- the averaged local law, pulled back to the index set `(u, σ, a)`
  have hpre := StochDomAt.precomp_param hS2.2.1
    (fun n (p : STIdx2P sz STSigMixed s t n) =>
      ((p.1, (fun _ : Fin 1 => true), (fun _ : Fin 1 => p.2.2 1)) :
        TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
  have hscale := Step5CasesGen_prec_scale sz (law sz) (U := STIdx2P sz STSigMixed s t)
    (ξ := fun n p ω => ‖((mk sz z).L n (p.1 : ℝ) p.2.1.1 p.2.2 ω - (mk sz z).K n (p.1 : ℝ) p.2.1.1 p.2.2) -
      zeroModeSet d (sz.L n) {0}
        (fun a' => (mk sz z).L n (p.1 : ℝ) p.2.1.1 a' ω - (mk sz z).K n (p.1 : ℝ) p.2.1.1 a') p.2.2‖)
    (c := fun n p => (((sz.size n : ℕ) : ℝ) * (mk sz z).eta n (p.1 : ℝ))⁻¹)
    (fun n p => inv_pos.2 (mul_pos (hN n) (hηpos n p.1)))
    hpre
    (fun n p ω => by
      have hid := hident n (p.1 : ℝ) (hu0 n p.1) (hu1 n p.1) ω p.2.1.1 p.2.1.2 p.2.2
      have hη' := hηpos n p.1
      rw [hid, norm_div, Complex.norm_real, Complex.norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg hη'.le]
      rw [div_eq_mul_inv, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (mul_pos (hN n) hη').le)
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans le_rfl)
  refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 2) hscale ?_ ?_
  · filter_upwards [hev] with n hn
    intro p ω
    have hB := wardII_Bctl_le sz n hn.1 (hu1 n p.1) (by linarith [(hR n).1, ht1 n, p.1.2.2, hst n])
    have hc : 0 ≤ (((sz.size n : ℕ) : ℝ) * (mk sz z).eta n (p.1 : ℝ))⁻¹ :=
      inv_nonneg.2 (mul_pos (hN n) (hηpos n p.1)).le
    change (((sz.size n : ℕ) : ℝ) * (mk sz z).eta n (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ 1 ≤
      2 * ((STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * (mk sz z).eta n (p.1 : ℝ))⁻¹)
    rw [pow_one]
    nlinarith [mul_le_mul_of_nonneg_left hB hc]
  · intro n p ω
    exact mul_nonneg (inv_nonneg.2 (st5_STAI_nonneg sz n)) (inv_nonneg.2 (mul_pos (hN n) (hηpos n p.1)).le)

/-! ## 5. Targets 5 and 2: cases (iv) and (i) -/

/-- `W^{-d} B_{s,0} ≤ W^{-d} B_{u,0}` for `s ≤ u < 1` (`STBctl_mono`, `Induction/ScaleFacts.lean:74`, copied: `ScaleFacts` is not in
the import list of this file). -/
private theorem Step5CasesGen_Bctl_mono {d : ℕ} (sz : Sizes d) (n : ℕ) {s u : ℝ} (hsu : s ≤ u) (hu : u < 1) :
    sz.Bctl n s ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hxu : 0 < 1 - u := by linarith
  have hxs : 0 < 1 - s := by linarith
  rw [abs_of_pos hxu, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hg : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (sz.lam n ^ 2 + (1 - s))⁻¹ ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (by gcongr)
  have hK : 0 ≤ ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  gcongr

/-- **Target 5** (`T2462_caseIV`): case (iv) is Step 4 (`3_5:1940`), with no ingredient pin (band `stStep5IV_holds`,
`Step5Kit:549`).  The smallness `W^{-d}B_{u,0} ≤ 1` on `[s,t]` is size-level: `(con_st_ind)` gives `Bctl_t < 1` eventually
and `STBctl_mono` (copied) gives `Bctl_u ≤ Bctl_t` for `u ≤ t` (as `Bctl_le_one_of_conStInd`, `BA/Step1Fam.lean:382`); the spectral
`st5_Bctl_le_one` is not used. -/
theorem stStep5IVgL_holds (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 → STStep5IVgL d law Flow mk T0 := by
  intro hF hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨hadm, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hev := st5_eventually_A_ge_one sz hadm.2.1 hadm.2.2.2.2
  have hΔ : ∀ᶠ n in atTop, ∀ u : ℝ, u ≤ t n → sz.Bctl n u ≤ 1 := by
    filter_upwards [hcon] with n hn u hu
    have hlt : sz.Bctl n (t n) < 1 := by
      by_contra hge
      push Not at hge
      have := Real.one_le_rpow hge (by norm_num : (0 : ℝ) ≤ 1 / 100)
      linarith [hn.1, hn.2]
    exact (Step5CasesGen_Bctl_mono sz n hu (ht1 n)).trans hlt.le
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 6) (hLKU 2 (by norm_num)) ?_ ?_
    · filter_upwards [hev, hΔ] with n hn hΔn
      intro p ω
      have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
      have hx : 1 - (p.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d := by
        linarith [hR n, p.1.2.1]
      have := st5_compare_IV sz n hn.1 (by omega) (D := D) hu (hΔn (p.1 : ℝ) p.1.2.2) hx p.2.2
      simpa using this
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hS0 : 0 ≤ sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hr : (0 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by
        rw [Real.rpow_zero]; norm_num
      positivity
  · refine Step5CasesGen_prec_of_isEmpty sz (law sz) fun n => ⟨fun p => ?_⟩
    have h1 := hR n
    have h2 := p.2
    have h3 := hst n
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d :=
      one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h4 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ sz.lam n ^ 2 := div_le_self (sq_nonneg _) hL1
    linarith

/-- **Target 2** (`T2462_caseI`): case (i) from its ingredients (`3_5:1957-2250`): the light-weight and quadratic-variation
bounds `STEtermsMidgL`, the integrated hierarchy `STDuhamelIgL` and the initial term `STIniTermIgL` give `(Eq:Gdecay_flow)`; the
strong estimate is void (band `ST_step5_caseI_of_pins`, `Step5Kit:292`).  The constant `𝔠_d` is the minimum of the three pins'. -/
theorem ST_step5_caseI_of_pinsgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIgL d law Flow mk T0 →
      STIniTermIgL d law Flow mk T0 → STStep5IgL d law Flow mk T0 := by
  intro hF hE hD hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hD hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨min c₁ (min c₂ c₃), lt_min hc₁ (lt_min hc₂ hc₃), (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨hadm, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hcpos : 0 < min c₁ (min c₂ c₃) := lt_min hc₁ (lt_min hc₂ hc₃)
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hm₁ := st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)
  have hm₂ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))
  have hm₃ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_right _ _))
  have hE' := H₁ 𝔠 sz z hflow s t hs0 hst ht (st5_reg5I_mid (by omega) hR) hKb hKw hLK hDec hDecS hm₁ hS1 hS2
    hLmax hLKU
  have hD' := H₂ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₂ hS1 hS2 hLmax hLKU hE'
  have hI' := H₃ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₃ hS1 hS2 hLmax hLKU
  have hev := st5_eventually_A_ge_one sz hadm.2.1 hadm.2.2.2.2
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · have hdu := hD' D hD0
      (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
      (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
        (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hI' D hD0)
    have h1 := StochDomAt.precomp_param hdu
      (fun n (p : STIdx2 sz s t n) => ((p.1, ⟨p.2.1, trivial⟩, p.2.2) : STIdx2P sz STSigAll s t n))
    simp only [st5_zeroModeSet_empty] at h1
    refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 4) h1 ?_ ?_
    · filter_upwards [hev] with n hn
      intro p ω
      have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
      have hx : 1 - (p.1 : ℝ) ≤ sz.lam n ^ 2 := by
        have := p.1.2.1
        have := (hR n).2
        linarith [p.1.2.1]
      have := st5_compare_I sz n hn.1 hn.2 (D := D) hu hx p.2.2
      simpa using this
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hS0 : 0 ≤ sz.STWB n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0 : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have hr : (0 : ℝ) ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by
        rw [Real.rpow_zero]; norm_num
      positivity
  · refine Step5CasesGen_prec_of_isEmpty sz (law sz) fun n => ⟨fun p => ?_⟩
    have h1 := (hR n).2
    have h2 := p.2
    have h3 := hst n
    linarith [p.1.1.2.1, p.1.1.2.2, h2]

/-! ## 6. Target 4: case (iii) from `lem:pf_step5` -/

/-- **Target 4** (`T2462_caseIII`): the pin `STPfStep5gL` (`T ≥ t` w.h.p.) gives `(Eq:Gdecay+s<g_flow)` and `(Eq:Gdecay_flow)` up to
the `(log W)^{2(d-2)}` that `≺` absorbs (band `ST_step5_caseIII_of_pf`, `Step5Cases:311`; sizes only). -/
theorem ST_step5_caseIII_of_pfgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 → STPfStep5gL d law Flow mk T0 → STStep5IIIgL d law Flow mk T0 := by
  intro hF hPf hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hPf hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨c₁, hc₁, hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨hadm, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have hPfc := H₁ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hWO := hadm.2.2.2.2
  have hbw := hadm.2.2.2.1
  have h𝔠 := hadm.1
  have hN : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsz
  have hWt : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (hbw.mono fun n hn => hn) ((tendsto_rpow_atTop h𝔠).comp hN)
  have hWt' : Tendsto sz.W atTop atTop := tendsto_natCast_atTop_iff.1 hWt
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · -- `(Eq:Gdecay_flow)` from the `T_{u,D}` bound
    have h1 := StochDomAt.precomp_param (hPfc D hD0)
      (fun n (p : STIdx2 sz s t n) => (⟨p, hR n⟩ : {_p : STIdx2 sz s t n // sz.lam n ^ 2 ≤ 1 - t n}))
    refine Step5CasesGen_prec_mono' sz (law sz) h1 ?_
    intro τ hτ
    have hlog := st5_polylog_le_W hWt' d (D := D) h𝔡
    filter_upwards [hWO, hlog, (tendsto_size sz hsz).eventually (eventually_le_rpow 4 hτ)] with n hn hl h4 p ω
    have hu : (p.1 : ℝ) < 1 := lt_of_le_of_lt p.1.2.2 (ht1 n)
    have hx : sz.lam n ^ 2 ≤ 1 - (p.1 : ℝ) := by linarith [hR n, p.1.2.2]
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hA := lam_sq_mul_pow_ge sz n hn.1
    have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hn.1
    -- `y ≤ W^{-2𝔡}`
    have hy : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡)) := by
      have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      have h2 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)) := by
        calc ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) ≤ sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d := hA
          _ = ((sz.W n : ℕ) : ℝ) ^ d * sz.lam n ^ 2 := by ring
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)) := mul_le_mul_of_nonneg_left hx hWd.le
      rw [Real.rpow_neg hW0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) h2
    have hy1 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ≤ 1 :=
      hy.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
    have hy0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ := by
      have : 0 < 1 - (p.1 : ℝ) := by linarith [sq_nonneg (sz.lam n)]
      have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
      positivity
    have hcond : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 *
        ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2) ≤ 1 := by
      have e1 : ((((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (1 / 5 : ℝ)) ^ 4 =
          (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hy0]; norm_num
      have e2 : (((sz.W n : ℕ) : ℝ) ^ (-(2 * 𝔡))) ^ (4 / 5 : ℝ) = ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) := by
        rw [← Real.rpow_mul hW0.le]; ring_nf
      have h3 : (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) := by
        rw [← e2]; exact Real.rpow_le_rpow hy0 hy (by norm_num)
      rw [e1]
      calc (((sz.W n : ℕ) : ℝ) ^ d * (1 - (p.1 : ℝ)))⁻¹ ^ (4 / 5 : ℝ) *
            ((D * Real.log ((sz.W n : ℕ) : ℝ)) ^ 2 + 1) ^ (d - 2)
          ≤ ((sz.W n : ℕ) : ℝ) ^ (-(8 * 𝔡 / 5)) * ((sz.W n : ℕ) : ℝ) ^ (8 * 𝔡 / 5) :=
            mul_le_mul h3 hl (by positivity) (Real.rpow_nonneg hW0.le _)
        _ = 1 := by rw [← Real.rpow_add hW0]; simp
    have key := st5_compare_IIIb sz n hD0 hu hx hy1 hcond p.2.2
    have h0 : ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
    have hT : STtailTD sz n (p.1 : ℝ) D p.2.2 ≤ 4 * (((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
      rw [h0]; simpa using key
    have hnonneg : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (p.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (p.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D) := by
      have hB0 : 0 ≤ sz.Bctl n (p.1 : ℝ) := (st_Bctl_pos sz hu).le
      have hS0 : 0 ≤ STWB sz n (p.1 : ℝ) (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1)) := by
        unfold STWB Bparam
        have hx0' : 0 ≤ |1 - (p.1 : ℝ)| := abs_nonneg _
        positivity
      have : 0 ≤ ((1 - s n) / (1 - (p.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
      positivity
    calc STtailTD sz n (p.1 : ℝ) D p.2.2 ≤ 4 * _ := hT
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * _ := mul_le_mul_of_nonneg_right h4 hnonneg
  · -- `(Eq:Gdecay+s<g_flow)`
    refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 4) (hPfc D hD0) ?_ ?_
    · refine Eventually.of_forall fun n => ?_
      intro p ω
      have hu : (p.1.1 : ℝ) < 1 := lt_of_le_of_lt p.1.1.2.2 (ht1 n)
      have hx : sz.lam n ^ 2 ≤ 1 - (p.1.1 : ℝ) := by linarith [p.2, p.1.1.2.2]
      exact st5_compare_IIIa sz n (D := D) hu hx p.1.2.2
    · intro n p ω
      have hB0 : 0 ≤ sz.Bctl n (p.1.1 : ℝ) := by
        unfold Sizes.Bctl Bparam
        have hx0 : 0 ≤ |1 - (p.1.1 : ℝ)| := abs_nonneg _
        positivity
      have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      positivity

/-! ## 7. Target 3: case (ii) -/

/-- **Case (ii), the Ward term `(zYU1)`, restated with `C.eta` and the datum `κm ≤ Im m`** (`st5_compare_IIward`, `Step5Cases:438`):
`A⁻¹ (N η_u)⁻¹ ≤ (6/c) Δ_u^{1/5} W^{-d}B_{u,r} e^{-(r/ℓ_u)^{1/2}}` for `1 - u ≤ ilambda²/L²` (`ℓ_u = L`), `η_u = (1 - u) m` and
`c ≤ m`.  It is the band lemma at the energy `E = 0` (`Im m(0) = 1`, `etaT 0 u = 1 - u`) and `c = 1`, with
`(N η_u)⁻¹ ≤ c⁻¹ (N (1 - u))⁻¹`. -/
private theorem Step5CasesGen_compare_IIward {d : ℕ} (sz : Sizes d) (n : ℕ) (hlam : 0 < sz.lam n)
    (hA1 : 1 ≤ STAI sz n) {u η m c : ℝ} (hu : u < 1)
    (hx : 1 - u ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2) (hc : 0 < c) (hm : c ≤ m) (hη : η = (1 - u) * m)
    (a : Fin 2 → Zd d (sz.L n)) :
    (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤
      (6 / c) * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ))) := by
  have hm0 : (mE 0).im = 1 := by
    rw [mE_im, show (4 : ℝ) - 0 ^ 2 = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    norm_num
  have hb := st5_compare_IIward sz n hlam hA1 (E := 0) hu hx (c := 1) one_pos (by rw [hm0]) a
  have hη0 : etaT 0 u = 1 - u := by unfold etaT; rw [hm0, mul_one]
  rw [hη0] at hb
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hx0 : 0 < 1 - u := by linarith
  have hηle : (1 - u) * c ≤ η := by
    rw [hη]; exact mul_le_mul_of_nonneg_left hm hx0.le
  have h1 : (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ c⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
    calc (((sz.size n : ℕ) : ℝ) * η)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * ((1 - u) * c))⁻¹ :=
          inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hηle hN.le)
      _ = c⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
          rw [show ((sz.size n : ℕ) : ℝ) * ((1 - u) * c) = c * (((sz.size n : ℕ) : ℝ) * (1 - u)) by ring, mul_inv]
  have hA0 : 0 ≤ (STAI sz n)⁻¹ := inv_nonneg.2 (st5_STAI_nonneg sz n)
  calc (STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * η)⁻¹
      ≤ (STAI sz n)⁻¹ * (c⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) := mul_le_mul_of_nonneg_left h1 hA0
    _ = c⁻¹ * ((STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹) := by ring
    _ ≤ c⁻¹ * (6 / 1 * (((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          STWB sz n u (zdistInf d (sz.L n) (a 0 - a 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hc.le)
    _ = _ := by ring

/-- **Target 3** (`T2462_caseII`): case (ii) from its ingredients (`3_5:2251-2283`): the three error terms (`STEtermsMidgL`), the
integrated hierarchy with `Q^{(1)}` for `σ₁ ≠ σ₂` and without `Q` for `σ₁ = σ₂` (`STDuhamelIIgL`), the initial terms
(`STIniTermIIgL`) and the Ward term `(zYU1)` (`STWardIIgL`) give `(Eq:Gdecay_flow)`; the strong estimate is void (band
`ST_step5_caseII_of_pins`, `Step5Cases:542`).  The spectral datum is `κm ≤ Im m` of `Step5CasesGen_FlowFacts`. -/
theorem ST_step5_caseII_of_pinsgL (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop)
    (mk : ∀ (sz : Sizes d) (z : ℕ → ℂ), FlowFM sz) (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) :
    Step5CasesGen_FlowFacts d Flow mk T0 → STEtermsMidgL d law Flow mk T0 → STDuhamelIIgL d law Flow mk T0 →
      STIniTermIIgL d law Flow mk T0 → STWardIIgL d law Flow mk T0 → STStep5IIgL d law Flow mk T0 := by
  intro hF hE hD hI hWd hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₁, hc₁, hc₁', H₁⟩ := hE hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₂, hc₂, hc₂', H₂⟩ := hD hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₃, hc₃, hc₃', H₃⟩ := hI hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨c₄, hc₄, hc₄', H₄⟩ := hWd hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have hcpos : 0 < min c₁ (min c₂ (min c₃ c₄)) := lt_min hc₁ (lt_min hc₂ (lt_min hc₃ hc₄))
  refine ⟨min c₁ (min c₂ (min c₃ c₄)), hcpos, (min_le_left _ _).trans hc₁', ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  obtain ⟨κm, hκm, hFl⟩ := hF κ hκ
  obtain ⟨hadm, hT0, hIm, hη⟩ := hFl sz ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hT0 n)
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hm₁ := st5_conStInd_mono sz hcon ht1 hcpos (min_le_left _ _)
  have hm₂ := st5_conStInd_mono sz hcon ht1 hcpos ((min_le_right _ _).trans (min_le_left _ _))
  have hm₃ := st5_conStInd_mono sz hcon ht1 hcpos
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hm₄ := st5_conStInd_mono sz hcon ht1 hcpos
    (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hE' := H₁ 𝔠 sz z hflow s t hs0 hst ht (st5_reg5II_mid hR) hKb hKw hLK hDec hDecS hm₁ hS1 hS2
    hLmax hLKU
  obtain ⟨hDQ, hDS⟩ := H₂ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₂ hS1 hS2 hLmax hLKU hE'
  obtain ⟨hIQ, hIS⟩ := H₃ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₃ hS1 hS2 hLmax hLKU
  have hW' := H₄ 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hm₄ hS1 hS2 hLmax hLKU
  have hev := st5_eventually_A_ge_one sz hadm.2.1 hadm.2.2.2.2
  refine ⟨fun D hD0 => ?_, fun D hD0 => ?_⟩
  · -- the two sign classes
    have hmix : PrecL sz (law sz) (U := STIdx2P sz STSigMixed s t)
        (fun n v ω => ‖(mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2‖)
        (fun n v _ => ((((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)))) := by
      have hQ := hDQ D hD0
        (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
        (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
          (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hIQ D hD0)
      have hsum := StochDomAt.add (tendsto_size sz hsz) hW' hQ
      have hle : ∀ (n : ℕ) (v : STIdx2P sz STSigMixed s t n) (ω : sz.SeqΩ),
          ‖(mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2‖ ≤
            ((fun n (v : STIdx2P sz STSigMixed s t n) ω =>
              ‖((mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2) -
                zeroModeSet d (sz.L n) {0}
                  (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2‖) +
            (fun n (v : STIdx2P sz STSigMixed s t n) ω =>
              ‖zeroModeSet d (sz.L n) {0}
                (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2‖)) n v ω := by
        intro n v ω
        change ‖(mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2‖ ≤
          ‖((mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2) -
            zeroModeSet d (sz.L n) {0}
              (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2‖ +
          ‖zeroModeSet d (sz.L n) {0}
            (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2‖
        have := norm_add_le (((mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2) -
            zeroModeSet d (sz.L n) {0}
              (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2)
          (zeroModeSet d (sz.L n) {0}
            (fun a' => (mk sz z).L n (v.1 : ℝ) v.2.1.1 a' ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 a') v.2.2)
        rwa [sub_add_cancel] at this
      have hsum' := StochDomAt.of_le_left hle hsum
      refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 6 / κm + 4) hsum' ?_ ?_
      · filter_upwards [hev] with n hn
        intro v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hxL : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [(hR n).2, v.1.2.1]
        have hxg : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 := by
          have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
          exact hxL.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))
        have h1 := Step5CasesGen_compare_IIward sz n hn.1 hn.2 hu hxL hκm (hIm n) (hη n (v.1 : ℝ)) v.2.2
        have h2 := st5_compare_I sz n hn.1 hn.2 (D := D) hu hxg v.2.2
        have hP : 0 ≤ ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
              STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
              Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) := by
          have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
          have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
            unfold STWB Bparam
            have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
            positivity
          have : 0 ≤ ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
          positivity
        have hWD : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
        have h0' : ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
        rw [h0] at h1 h2 hP
        simp only [Pi.add_apply]
        rw [h0']
        have hcc : 0 < 6 / κm := by positivity
        nlinarith [h1, h2, hP, hWD, mul_nonneg hcc.le hWD]
      · intro n v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
          unfold STWB Bparam
          have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
          positivity
        have : 0 ≤ ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
        positivity
    have hsame : PrecL sz (law sz) (U := STIdx2P sz STSigSame s t)
        (fun n v ω => ‖(mk sz z).L n (v.1 : ℝ) v.2.1.1 v.2.2 ω - (mk sz z).K n (v.1 : ℝ) v.2.1.1 v.2.2‖)
        (fun n v _ => ((((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) * (sz.Bctl n (v.1 : ℝ)) ^ (1 / 5 : ℝ) *
          STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) (v.1 : ℝ)) ^ (1 / 2 : ℝ)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)))) := by
      have hDu := hDS D hD0
        (fun n p => (STAI sz n) ^ (-(1 / 5) : ℝ) *
          STprof sz n (p.1 : ℝ) D ((sz.L n : ℕ) : ℝ) (p.2.2 0) (p.2.2 1) + ((sz.W n : ℕ) : ℝ) ^ (-D))
        (fun n p => add_nonneg (mul_nonneg (Real.rpow_nonneg (st5_STAI_nonneg sz n) _)
          (st5_STprof_nonneg sz n _ _ _ _ _)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hIS D hD0)
      simp only [st5_zeroModeSet_empty] at hDu
      refine Step5CasesGen_prec_mono sz (law sz) hsz (c := 4) hDu ?_ ?_
      · filter_upwards [hev] with n hn
        intro v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hxg : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 := by
          have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
          have : 1 - (v.1 : ℝ) ≤ sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 := by linarith [(hR n).2, v.1.2.1]
          exact this.trans (div_le_self (sq_nonneg _) (one_le_pow₀ hL))
        have h2 := st5_compare_I sz n hn.1 hn.2 (D := D) hu hxg v.2.2
        have h0 : ((1 - 0 : ℝ) / 1) ^ (0 : ℝ) = 1 := by simp
        have h0' : ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) = 1 := by rw [Real.rpow_zero]
        rw [h0] at h2
        rw [h0']
        exact h2
      · intro n v ω
        have hu : (v.1 : ℝ) < 1 := lt_of_le_of_lt v.1.2.2 (ht1 n)
        have hB0 : 0 ≤ sz.Bctl n (v.1 : ℝ) := (st_Bctl_pos sz hu).le
        have hW0 : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hS0 : 0 ≤ STWB sz n (v.1 : ℝ) (zdistInf d (sz.L n) (v.2.2 0 - v.2.2 1)) := by
          unfold STWB Bparam
          have hx0' : 0 ≤ |1 - (v.1 : ℝ)| := abs_nonneg _
          positivity
        have : 0 ≤ ((1 - s n) / (1 - (v.1 : ℝ))) ^ (0 : ℝ) := by rw [Real.rpow_zero]; norm_num
        positivity
    exact Step5CasesGen_prec_cover sz (law sz) hsz
      (fun n (v : STIdx2P sz STSigMixed s t n) => ((v.1, v.2.1.1, v.2.2) : STIdx2 sz s t n))
      (fun n (v : STIdx2P sz STSigSame s t n) => ((v.1, v.2.1.1, v.2.2) : STIdx2 sz s t n))
      (fun n u => by
        by_cases h : u.2.1 0 = u.2.1 1
        · exact Or.inr ⟨(u.1, ⟨u.2.1, h⟩, u.2.2), rfl⟩
        · exact Or.inl ⟨(u.1, ⟨u.2.1, h⟩, u.2.2), rfl⟩) hmix hsame
  · refine Step5CasesGen_prec_of_isEmpty sz (law sz) fun n => ⟨fun p => ?_⟩
    have h1 := (hR n).2
    have h2 := p.2
    have h3 := hst n
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ 2 :=
      one_le_pow₀ (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n))
    have h4 : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 ≤ sz.lam n ^ 2 := div_le_self (sq_nonneg _) hL1
    linarith

/-! ## 8. Compiled nonempty instances at `d = 3`

The size data are the merged `szB` (`L = 4`, `W_n = n + 4`, `lam = 1`, flow `zB`, `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`),
`szG` (`szB` with `lam = 5`, case (iv)) and `sz0` (case (iii)) with the regimes of `Step5Inst`: case (i) at `(7/8, 15/16)`,
case (ii) at `(15/16, 31/32)`, case (iv) at `(5/8, 3/4)` on `(szB/szG, zB)`.  Every deterministic hypothesis (flow, time ranges,
regime, `(con_st_ind)` for every `𝔠_d > 0`) is discharged by the merged `inst_*` theorems; what stays a hypothesis of an instance
is a pin of another row: `STEtermsMid`, `STDuhamelI`, `STDuhamelII`, `STIniTermI`, `STIniTermII`, `STPfStep5` (owners U4s2, U4s3, U5)
and the stochastic premises `STKbound ... STLKU` inside `InstIng5Concl`. -/

end RBM.BA
