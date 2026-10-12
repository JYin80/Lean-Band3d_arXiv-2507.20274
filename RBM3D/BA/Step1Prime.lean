/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GbEXPav
import RBM3D.BA.KBound

/-!
# BA-G7 (T2468): the primed Step-1 rewire

Ticket T2468 (DECISIONS §272; supervisor `2026-10-10-1155` C3, `2026-10-10-2254` Q2-Q3, `2026-10-11-0150` O2).
Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`), `lem_GbEXP_BA` `:1916-1946`, Step 1 `:1987-1990`.  Namespace `RBM.BA`.

The merged Step 1 at BA (`baBootstrap'_holds`, `BA/Step1.lean:576`; `baStep1_holds`, `BA/Step1Fam.lean:695`) reads the
unprimed band-window pin `BAGbEXPij`.  This file writes their primed successors on `BAGbEXPij'` (`BA/GreenCore.lean`,
proved by `baGbEXPij'_holds`, `BA/GreenOff.lean:1289`) with the unprimed diagonal `BAGbEXPii`, additively: no merged file is
edited.

* section 1: target 1 `baGij'_member`, the primed pin at every member of `Fam(t)`;
* section 2: target 2, the sample core `step1Prime_wl_det` and the event bookkeeping `step1Prime_loopPrem`;
* section 3: target 3, `baS1_wl_seq'`, `baS1_forb'`, `baS1_boot'`, `baS1_weakPT'`, `baS1_loopPT'`;
* section 4: targets 4-5, `baBootstrap'_of_ij'`, `baStep1_of_ij'`, `baBootstrap'_holds'`, `baStep1_holds'`;
* section 5: target 6, the BA readings `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`;
* section 6: target 7, compiled nonempty instances (`RBM.BA.Step1PrimeInst`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

open private Boot_baFMz_eqAt from RBM3D.BA.Step1Boot

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Target 1: the primed member transfer -/

section Member

variable {d : ℕ}

/-- **The finite modification of a member of `Fam(t)`, with `(κ', ε')` in front of the sizes** (copy of the private
`Boot_member`, `BA/Step1Boot.lean:232`, whose `κ'`, `ε'` come after the sizes): `BAFlowMember` gives `κ', ε'` depending
on `(κ, ε, 𝔡)` only; for `0 ≤ u ≤ t ≤ t₀(z)` there is `z''` with `BAFlow sz κ' ε' 𝔠 𝔡 z''`, `u ≤ t₀(z'')` and
`z'' n = z' n` eventually. -/
private theorem Step1Prime_member (hmem : BAFlowMember d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ κ' ε' : ℝ, 0 < κ' ∧ 0 < ε' ∧
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
        ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
          ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
            ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) →
              ∃ z'' : ℕ → ℂ, BAFlow sz κ' ε' 𝔠 𝔡 z'' ∧ (∀ n, u n ≤ BAflowT0 sz z'' n) ∧
                (∀ᶠ n in atTop, z'' n = z' n) := by
  obtain ⟨κ', ε', hκ'0, -, hε'0, -, H⟩ := hmem κ ε 𝔡 hκ hε h𝔡
  refine ⟨κ', ε', hκ'0, hε'0, ?_⟩
  intro 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u hu0 hut
  have hfam0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hu0 n).trans (hut n)) hfam
  obtain ⟨n₀, hflow'⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin z' hfam0
  refine ⟨fun n => if n < n₀ then z n else z' n, hflow', ?_, ?_⟩
  · intro n
    by_cases hn : n < n₀
    · have h1 : BAflowT0 sz (fun n => if n < n₀ then z n else z' n) n = BAflowT0 sz z n := by
        unfold BAflowT0; simp only [hn, ↓reduceIte]
      rw [h1]
      exact (hut n).trans (htT n)
    · have h1 : BAflowT0 sz (fun n => if n < n₀ then z n else z' n) n = BAflowT0 sz z' n := by
        unfold BAflowT0; simp only [hn, ↓reduceIte]
      rw [h1]
      exact BAFamZ_horizon (fun n => (hut n).trans (htT n)) (BAFamZ_mono hut hfam) n
  · exact Filter.eventually_atTop.mpr ⟨n₀, fun n hn => by simp [not_lt.mpr hn]⟩

/-- The indicator `Ω(t, A)` and the entries of `G - M` of a carrier at the index `n` depend on `z n` only. -/
private theorem Step1Prime_indMax_eq (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) (t A : ℝ) :
    (baFMz sz z₁).indMax n t A = (baFMz sz z₂).indMax n t A := by
  obtain ⟨-, hG, hM⟩ := Boot_baFMz_eqAt sz h
  funext ω
  simp only [FlowFM.indMax, FlowFM.GM, hG, hM]
  rfl

private theorem Step1Prime_GM_eq (sz : Sizes d) {z₁ z₂ : ℕ → ℂ} {n : ℕ} (h : z₁ n = z₂ n) (t : ℝ) :
    (baFMz sz z₁).GM n t = (baFMz sz z₂).GM n t := by
  obtain ⟨-, hG, hM⟩ := Boot_baFMz_eqAt sz h
  funext ω x y
  simp only [FlowFM.GM, hG, hM]

/-- **Target 1** (`baGij'_member`, pin `T2468_GijMember'`; successor of `baGij_member`, `BA/Step1Boot.lean:283`): the primed
pin `BAGbEXPij'` at every member `z'` of `Fam(t)` and every `0 ≤ u ≤ t`.  `(κ', ε')` of `BAFlowMember` come before the sizes,
then `c = c(κ', ε', 𝔡)` of `BAGbEXPij'`; the loop premise moves from `z'` to the finite modification `z''` and the decay
conclusion back, by `PrecL_congr` (the carriers of `z''` and `z'` agree for `n ≥ n₀`). -/
theorem baGij'_member (d : ℕ) :
    BAGbEXPij' d → BAFlowMember d →
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∃ c : ℝ, 0 < c ∧
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z → (∀ n, 0 < sz.lam n) →
          ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ 1 / 2 → BAWinBulk sz z c₁ κ →
            ∀ t : ℕ → ℝ, (∀ n, t n ≤ BAflowT0 sz z n) → ∀ z' : ℕ → ℂ, BAFamZ sz z c₁ t z' →
              ∀ u : ℕ → ℝ, (∀ n, 0 ≤ u n) → (∀ n, u n ≤ t n) →
                ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
                  ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
                    (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                    (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
                    (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
                    GreenCore_loopPrem sz z' u ε₀ Φ → GreenCore_decayConcl sz z' u ε₀ D c Φ Ψ := by
  intro hij hmem κ ε 𝔡 hκ hε h𝔡
  obtain ⟨κ', ε', hκ', hε', H⟩ := Step1Prime_member hmem hκ hε h𝔡
  obtain ⟨c, hc, hmain⟩ := hij κ' ε' 𝔡 hκ' hε' h𝔡
  refine ⟨c, hc, ?_⟩
  intro 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u hu0 hut ε₀ hε₀ D hD Φ Ψ hΦ hΨ1 hΨ2 hprem
  obtain ⟨z'', hfl', hhor, hev⟩ := H 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u hu0 hut
  have hprem' : GreenCore_loopPrem sz z'' u ε₀ Φ := by
    unfold GreenCore_loopPrem at hprem ⊢
    refine (PrecL_congr ?_).mpr hprem
    filter_upwards [hev] with n hn
    obtain ⟨hL, -, -⟩ := Boot_baFMz_eqAt sz hn
    refine ⟨?_, rfl⟩
    funext p ω
    rw [Step1Prime_indMax_eq sz hn, hL]
  have h := hmain 𝔠 sz z'' hfl' u hu0 hhor ε₀ hε₀ D hD Φ Ψ hΦ hΨ1 hΨ2 hprem'
  unfold GreenCore_decayConcl at h ⊢
  refine (PrecL_congr ?_).mp h
  filter_upwards [hev] with n hn
  refine ⟨?_, rfl⟩
  funext p ω
  rw [Step1Prime_indMax_eq sz hn, Step1Prime_GM_eq sz hn]

end Member

/-! ## 2. Target 2: the sample core and the event bookkeeping -/

section SampleCore

/-- The window constant of the primed sample core, `3 S⁴ + 4`, `S = expC (d-2) (c/d)` the bound of `Σ_{a'} e^{-c|a'-a|}` on `Z_L^d`
(`BAsum_exp_decay_le`, `BA/Prop5Short.lean:251`; `zdistD ≤ d · zdistInf`).  It depends on `(d, c)` only, not on `n`. -/
def Step1Prime_K (d : ℕ) (c : ℝ) : ℝ := 3 * (RBM.expC (d - 2) (c / d)) ^ 4 + 4

/-- `64 ≤ expC k c` for `c > 0` (`2^(k+2) ≥ 4`, `2^(k+3) ≥ 8`, `1 + (k+3)!/c^(k+3) ≥ 1`). -/
private theorem Step1Prime_expC_ge (k : ℕ) {c : ℝ} (hc : 0 < c) : 64 ≤ RBM.expC k c := by
  unfold RBM.expC
  have h1 : (1 : ℝ) ≤ 1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3) := by
    have : 0 ≤ (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3) := by positivity
    linarith
  have h2 : (4 : ℝ) ≤ 2 ^ (k + 2) := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (8 : ℝ) ≤ 2 ^ (k + 3) := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (8 : ℝ) * 1 ≤ 2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3)) :=
    mul_le_mul h3 h1 zero_le_one (by positivity)
  have h5 : (2 : ℝ) * (8 * 1) ≤ 2 * (2 ^ (k + 3) * (1 + (Nat.factorial (k + 3) : ℝ) / c ^ (k + 3))) :=
    mul_le_mul_of_nonneg_left h4 (by norm_num)
  nlinarith

/-- `Σ_{a'} e^{-c|a'-a|_∞} ≤ expC (d-2) (c/d)` on `Z_L^d`, `d ≥ 2` (`|·|_∞ = zdistInf`; `zdistD ≤ d · zdistInf`). -/
private theorem Step1Prime_exp_sum_le {d L : ℕ} [NeZero L] (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) (a : Zd d L) :
    ∑ a' : Zd d L, Real.exp (-c * (zdistInf d L (a' - a) : ℝ)) ≤ RBM.expC (d - 2) (c / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  refine le_trans (Finset.sum_le_sum fun a' _ => ?_) (BAsum_exp_decay_le d L hd (c / d) (div_pos hc hd0) a)
  refine Real.exp_le_exp.2 ?_
  rw [← neg_sub a' a, zdistD_neg]
  have h1 : (zdistD d L (a' - a) : ℝ) ≤ d * (zdistInf d L (a' - a) : ℝ) := by
    exact_mod_cast zdistD_le_mul_zdistInf d L (a' - a)
  have h2 : c / d * (zdistD d L (a' - a) : ℝ) ≤ c * (zdistInf d L (a' - a) : ℝ) := by
    calc c / d * (zdistD d L (a' - a) : ℝ) ≤ c / d * (d * (zdistInf d L (a' - a) : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (div_pos hc hd0).le
      _ = c * (zdistInf d L (a' - a) : ℝ) := by field_simp
  linarith

/-- The printed right side of `(GijGEX_BA)` with the constant control `Φ ≡ Ψ ≡ φ`, `D = d/2`, is at most `(S² + 2) φ`
(`S = expC (d-2) (c/d)`) once `W^{-d/2} ≤ φ`: the double sum factorises into two sums `≤ S`, and the two exponentials are `≤ 1`. -/
private theorem Step1Prime_decayRHS_le {d L W : ℕ} [NeZero L] (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) {φ : ℝ} (hφ : 0 < φ)
    (hW : ((W : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ φ) (a b : Zd d L) :
    GreenCore_decayRHS d L W c ((d : ℝ) / 2) (fun _ _ => φ) φ a b ≤ ((RBM.expC (d - 2) (c / d)) ^ 2 + 2) * φ := by
  set S := RBM.expC (d - 2) (c / d) with hS
  have hSa := Step1Prime_exp_sum_le hd hc a
  have hSb := Step1Prime_exp_sum_le hd hc b
  have hA0 : 0 ≤ ∑ a' : Zd d L, Real.exp (-c * (zdistInf d L (a' - a) : ℝ)) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have hB0 : 0 ≤ ∑ b' : Zd d L, Real.exp (-c * (zdistInf d L (b' - b) : ℝ)) :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have h1 : (∑ a' : Zd d L, ∑ b' : Zd d L, φ *
      Real.exp (-c * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ)))) =
      φ * ((∑ a' : Zd d L, Real.exp (-c * (zdistInf d L (a' - a) : ℝ))) *
        (∑ b' : Zd d L, Real.exp (-c * (zdistInf d L (b' - b) : ℝ)))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [show -c * ((zdistInf d L (a' - a) : ℝ) + (zdistInf d L (b' - b) : ℝ)) =
      -c * (zdistInf d L (a' - a) : ℝ) + -c * (zdistInf d L (b' - b) : ℝ) by ring, Real.exp_add]
  have h2 : φ * ((∑ a' : Zd d L, Real.exp (-c * (zdistInf d L (a' - a) : ℝ))) *
        (∑ b' : Zd d L, Real.exp (-c * (zdistInf d L (b' - b) : ℝ)))) ≤ φ * (S ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ hφ.le
    rw [sq]
    exact mul_le_mul hSa hSb hB0 (hA0.trans hSa)
  have h3 : φ * Real.exp (-c * (zdistInf d L (a - b) : ℝ)) ≤ φ * 1 := by
    refine mul_le_mul_of_nonneg_left ?_ hφ.le
    refine Real.exp_le_one_iff.2 ?_
    have : (0 : ℝ) ≤ (zdistInf d L (a - b) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have h4 : ((W : ℕ) : ℝ) ^ (-((d : ℝ) / 2)) ≤ φ := by rwa [neg_div] at hW
  unfold GreenCore_decayRHS
  rw [h1]
  nlinarith

/-- **Target 2 (b)** (`step1Prime_wl_det`; twin of `flowFM_wl_det`, `BA/Step1Setup.lean:113`): the weak-law core at one sample
over any carrier, with the off-diagonal input in the printed shape of `(GijGEX_BA)`.  The off-diagonal hypothesis is
`1_Ω |(G_u - M)_{xy}| ≤ Nτ · decayRHS([x],[y])` with the constant control `Φ ≡ Ψ ≡ φ` and `D = d/2`
(`GreenCore_decayRHS`), in place of the window `gexRHS`; the control satisfies `W^{-d/2} ≤ φ` and the loop input is
`Ω_C |𝓛^{(2)}| ≤ Nτ φ²`.  The conclusion `‖(G_u - M)_{ij}‖² ≤ (3S⁴ + 4) Nτ² φ²` has a constant `Step1Prime_K d c` that
depends on `(d, c)` only (`2 ≤ d`). -/
theorem step1Prime_wl_det (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (ω : sz.SeqΩ) (u a c' φ Nτ C₀ : ℝ), 0 < c' →
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ 2 * a) →
      2 * a ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') → 1 ≤ Nτ → 0 < φ → ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ φ →
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n u ω x y‖ ≤ C₀) →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), C.omegaC n u C₀ ω * ‖C.L n u σ b ω‖ ≤ Nτ * φ ^ 2) →
      (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1 p.2‖ ^ 2 ≤
          Nτ * STmaxLoop2g C n u ω) →
      (∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2},
        C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1.1 p.1.2‖ ≤
          Nτ * GreenCore_decayRHS d (sz.L n) (sz.W n) c ((d : ℝ) / 2) (fun _ _ => φ) φ
            (STblk sz n p.1.1) (STblk sz n p.1.2)) →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω i j‖ ^ 2 ≤ Step1Prime_K d c * Nτ ^ 2 * φ ^ 2 := by
  intro sz C n ω u a c' φ Nτ C₀ hc' hx hΩ hNτ hφ hWφ hG hLoop hii hij
  have hom : C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω = 1 := by
    unfold FlowFM.indMax
    have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') :=
      fun x y => (hx x y).trans hΩ
    simp [hall]
  have hom2 : C.omegaC n u C₀ ω = 1 := by
    unfold FlowFM.omegaC
    simp [hG]
  have hLoop' : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), ‖C.L n u σ b ω‖ ≤ Nτ * φ ^ 2 :=
    fun σ b => by
      have := hLoop σ b
      rwa [hom2, one_mul] at this
  have hφ2 : 0 < φ ^ 2 := by positivity
  have hB : 0 ≤ Nτ * φ ^ 2 := mul_nonneg (by linarith) hφ2.le
  have hmax : STmaxLoop2g C n u ω ≤ Nτ * φ ^ 2 :=
    Finset.sup'_le _ _ fun p _ => hLoop' _ _
  have hS : 64 ≤ RBM.expC (d - 2) (c / d) :=
    Step1Prime_expC_ge _ (div_pos hc (by exact_mod_cast (by omega : 0 < d)))
  set S := RBM.expC (d - 2) (c / d) with hSdef
  have hK : 3 * S ^ 4 + 4 = Step1Prime_K d c := rfl
  have hS2 : 2 ≤ S ^ 2 := by nlinarith
  have hS4 : S ^ 2 ≤ S ^ 4 := by nlinarith
  have hNτ2 : 0 ≤ Nτ ^ 2 * φ ^ 2 := by positivity
  intro i j
  by_cases hij' : i = j
  · subst hij'
    have h1 := hii (i, i)
    rw [hom, one_mul] at h1
    have h2 : Nτ * STmaxLoop2g C n u ω ≤ Nτ * (Nτ * φ ^ 2) :=
      mul_le_mul_of_nonneg_left hmax (by linarith)
    have h4 : Nτ * (Nτ * φ ^ 2) ≤ Step1Prime_K d c * Nτ ^ 2 * φ ^ 2 := by
      rw [← hK]
      nlinarith [mul_nonneg (sq_nonneg (S ^ 2)) hNτ2]
    simp only at h1
    linarith
  · have h1 := hij ⟨(i, j), hij'⟩
    rw [hom, one_mul] at h1
    simp only at h1
    have h2 := Step1Prime_decayRHS_le (L := sz.L n) (W := sz.W n) hd hc hφ hWφ (STblk sz n i) (STblk sz n j)
    have h3 : ‖C.GM n u ω i j‖ ≤ Nτ * ((S ^ 2 + 2) * φ) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h5 : ‖C.GM n u ω i j‖ ^ 2 ≤ (Nτ * ((S ^ 2 + 2) * φ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h6 : (Nτ * ((S ^ 2 + 2) * φ)) ^ 2 = (S ^ 2 + 2) ^ 2 * (Nτ ^ 2 * φ ^ 2) := by ring
    have h7 : (S ^ 2 + 2) ^ 2 * (Nτ ^ 2 * φ ^ 2) ≤ Step1Prime_K d c * Nτ ^ 2 * φ ^ 2 := by
      rw [← hK]
      have : (S ^ 2 + 2) ^ 2 ≤ 3 * S ^ 4 + 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hNτ2]
    linarith

end SampleCore

section Bookkeeping

open RBM.Ind FlowFM

/-- On `Ω(u, A) = {‖G_u - M‖_max ≤ A}`, `A ≤ 1`, the event `Ω_u` of threshold `1 + κm⁻¹` holds: `|M_xy| ≤ (Im m)⁻¹ ≤ κm⁻¹`
(`baM_entry_le`, `BA/Step1Boot.lean:322`), so `indMax ≤ omegaC` (the step of `baS1_wl_seq`, `BA/Step1.lean:249-260`). -/
private theorem Step1Prime_indMax_le_omegaC {d : ℕ} (sz : Sizes d) (z' : ℕ → ℂ) {κm : ℝ} (hκm : 0 < κm)
    (n : ℕ) (hmκ : κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) (u A : ℝ) (hA : A ≤ 1)
    (ω : sz.SeqΩ) :
    (baFMz sz z').indMax n u A ω ≤ (baFMz sz z').omegaC n u (1 + κm⁻¹) ω := by
  unfold FlowFM.indMax
  split_ifs with h1
  · have hmpos : 0 < (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := hκm.trans_le hmκ
    have hG : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z').G n u ω x y‖ ≤ 1 + κm⁻¹ := by
      intro x y
      have h1' := norm_le_norm_sub_add ((baFMz sz z').G n u ω x y) ((baFMz sz z').M n x y)
      have h2' := h1 x y
      change ‖(baFMz sz z').G n u ω x y - (baFMz sz z').M n x y‖ ≤ _ at h2'
      have h3' : ‖(baFMz sz z').M n x y‖ ≤ ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ :=
        baM_entry_le d sz (BAflowLam0 sz z') (BAflowEs sz z') n hmpos x y
      have h4' : ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ ≤ κm⁻¹ :=
        inv_anti₀ hκm hmκ
      linarith
    unfold FlowFM.omegaC
    simp [hG]
  · unfold FlowFM.omegaC
    split_ifs <;> norm_num

/-- **Target 2 (a)** (`step1Prime_loopPrem`): the loop premise of the primed pin at a member `z'`, time `u ∈ [s, t]`, for
the deterministic control `Φ_n ≡ Bctl_n(s_n)^{7/15}`: `1_Ω 𝓛^{(2)}_{u,(-,+),(a,b)} ≺ Φ_n²` uniformly in `(a, b)`, `Ω = {‖G_u - M‖_max ≤ W^{-ε₀}}`
(any `ε₀ > 0`, in particular `ε₀ = c'` of `s1_F5`).  It comes from the uniform loop input at `k = 2` (the `hLI` of `baS1_wl_seq`, event
`Ω_u` of threshold `1 + κm⁻¹`): `indMax(W^{-ε₀}) ≤ omegaC(1 + κm⁻¹)` and `Bctl_s · (1-s)/(1-u) ≤ Bctl_s^{14/15} = Φ²` eventually
(`s1_ratio_ev`).  No constant. -/
theorem step1Prime_loopPrem (d : ℕ) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
      (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1)) →
    ∀ ε₀ : ℝ, 0 < ε₀ →
      GreenCore_loopPrem sz z' u ε₀ (fun n _ _ => (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ u hu hLI ε₀ hε₀
  unfold GreenCore_loopPrem
  refine StochDomAt.of_subset
    (StochDomAt.precomp_param hLI (fun n (p : Zd d (sz.L n) × Zd d (sz.L n)) =>
      ((![false, true] : Fin 2 → Bool), (![p.1, p.2] : Fin 2 → Zd d (sz.L n))))) ?_
  intro τ₁ hτ₁
  refine ⟨τ₁, hτ₁, ?_⟩
  filter_upwards [s1_ratio_ev h] with n hn
  rintro ω ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hBs := s1_B_pos h n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hind := Step1Prime_indMax_le_omegaC sz z' hκm n (hmκ n) (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀))
    (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)) ω
  have hgr : (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) = ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBs.le]; norm_num
  have hz : ((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤
      ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [← hgr]
    have := hn (u n) (hu n).1 (hu n).2
    simpa [mul_comm] using this
  have hN0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hL0 : 0 ≤ ‖(baFMz sz z').L n (u n) ![false, true] ![p.1, p.2] ω‖ := norm_nonneg _
  change ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 <
    (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
      ‖(baFMz sz z').L n (u n) ![false, true] ![p.1, p.2] ω‖ at hp
  change ((sz.size n : ℕ) : ℝ) ^ τ₁ * (((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1)) <
    (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω *
      ‖(baFMz sz z').L n (u n) ![false, true] ![p.1, p.2] ω‖
  calc ((sz.size n : ℕ) : ℝ) ^ τ₁ * (((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1))
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ₁ * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 :=
        mul_le_mul_of_nonneg_left hz hN0
    _ < _ := hp
    _ ≤ _ := mul_le_mul_of_nonneg_right hind hL0

end Bookkeeping

/-! ## 3. Target 3: the targets 1-5 of Step 1, primed

Twins of `baS1_wl_seq`, `baS1_forb`, `baS1_boot`, `baS1_weakPT`, `baS1_loopPT` (`BA/Step1.lean:191, 306, 428, 469, 507`).  The
single change of the statements: the family `hGij` (`BAGijGEX`) is replaced by the primed member family of target 1 at the rate
`c` (the body of `baGij'_member` at a fixed member `z'`, with `GreenCore_decayConcl` unfolded: the premise scan of
`#assert_rbm_axioms` finds a `Prop` definition in a hypothesis and `GreenCore_decayConcl` is concluded by no theorem, only by the
pin `BAGbEXPij'` under an existential; `GreenCore_loopPrem` is concluded by `step1Prime_loopPrem`); the binders `hd : 2 ≤ d`, `c`, `hc : 0 < c` are added (the guard of
the merged Green pins and the window constant of `step1Prime_wl_det`).  Every other hypothesis and every conclusion is verbatim.
`baS1_wl_seq'` is proved from target 2; the other four are the merged proofs with `baS1_wl_seq'`. -/

open private BAStep1_le_gmMax BAStep1_gmMax_le BAStep1_gmMax_nonneg BAStep1_gmMax_le_add BAStep1_gmMax_continuousOn
  BAStep1_norm_BAmF_le_one BAStep1_net BAStep1_net_mem BAStep1_exists_close BAStep1_perTime_timeIcc from RBM3D.BA.Step1

section Windows

/-- `W^{-d/2} ≤ φ` from `(W^d)⁻¹ ≤ φ²` (`φ ≥ 0`, `W > 0`). -/
private theorem Step1Prime_wd_half {d : ℕ} {W : ℝ} (hW : 0 < W) {φ : ℝ} (hφ : 0 ≤ φ) (h : (W ^ d)⁻¹ ≤ φ ^ 2) :
    W ^ (-(d : ℝ) / 2) ≤ φ := by
  have h0 : 0 ≤ W ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hW.le _
  refine (pow_le_pow_iff_left₀ h0 hφ two_ne_zero).1 ?_
  have e : (W ^ (-(d : ℝ) / 2)) ^ 2 = (W ^ d)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW.le, ← Real.rpow_natCast W d, ← Real.rpow_neg hW.le]
    congr 1
    ring
  rw [e]
  exact h

end Windows

section Weak

open RBM.Ind FlowFM

/-- **Target 3, `baS1_wl_seq'`** (primed `baS1_wl_seq`, `BA/Step1.lean:191`): the weak-law step at one time sequence
`u ∈ [s,t]`: `1(‖G_u - M‖_max ≤ 2 a_s^{1/4}) ‖G_u - M‖_max ≺ 2·3^d a_s^{7/15}` per time, `a_s = W^{-d}B_{s,0}`.  The inputs are
`(GiiGEX)` at `ε₀ = c'` of `s1_F5`, the primed pin `(GijGEX_BA)` at the member (`ε₀ = c'`, `D = d/2`, `Φ ≡ Ψ ≡ a_s^{7/15}`,
whose windows hold eventually: `s1_F5`, `s1_F8`, `a_s ≤ 1`; and whose loop premise is `step1Prime_loopPrem`), the uniform loop
input at `k = 2` with `s1_ratio_ev`, and the deterministic core `step1Prime_wl_det` at `C₀ = 1 + κm⁻¹`.  The events are taken
at `τ'/2`; the window constant `Step1Prime_K d c` (depending on `(d, c)` only) is absorbed by `N^{τ'}` eventually
(`s1_N_pow_ev`). -/
theorem baS1_wl_seq' (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ →
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
            (Sizes.STblk sz n p.1.2))) →
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (U := fun _ => Unit)
        (fun n _ ω => {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator
          (fun ω => gmMax (baFMz sz z') n (u n) ω) ω)
        (fun n _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hLI hGii hGij u hu
  have hsize := s1_hsize sz h.hN
  obtain ⟨c', hc', hF5⟩ := s1_F5 h
  have hGii' := hGii u hu c' hc'
  have hLI2 := hLI u hu 2 (by norm_num)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  -- the windows of the primed pin at `Φ ≡ Ψ ≡ a_s^{7/15}`
  have hwin : ∀ᶠ n in atTop, 0 < (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) ∧
      (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') ∧
      ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) := by
    filter_upwards [hF5, s1_F8 h, s1_B_le_one h] with n hn5 hn8 hn1
    have hBs := s1_B_pos h n
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have hgr : (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) = ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBs.le]; norm_num
    have hpos : 0 < (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) := Real.rpow_pos_of_pos hBs _
    refine ⟨hpos, ?_, ?_⟩
    · have h1 : (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) ≤ (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow_of_exponent_ge hBs hn1 (by norm_num)
      have h2 : 0 ≤ (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hBs.le _
      linarith
    · refine Step1Prime_wd_half hW0 hpos.le ?_
      rw [← hgr]
      exact hn8
  have hGij' := hGij u hu c' hc' ((d : ℝ) / 2) (by positivity)
    (fun n _ _ => (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) (fun n => (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))
    (by filter_upwards [hwin] with n hn _ _ using ⟨hn.1, hn.2.1⟩)
    (by filter_upwards [hwin] with n hn using hn.2.2)
    (by filter_upwards [hwin] with n hn using hn.2.1)
    (step1Prime_loopPrem d sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ u hu hLI2 c' hc')
  refine s1_pt_of_highProb fun τ' hτ' => ?_
  have hτ2 : 0 < τ' / 2 := half_pos hτ'
  have Ev1 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hGij' hτ2
  have Ev2 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hGii' hτ2
  have Ev3 := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hLI2 hτ2
  have EvAll := PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize Ev1 Ev2) Ev3
  refine PerTimeCalc.perTimeCalc_highProbAt_mono EvAll ?_
  filter_upwards [hF5, hwin, s1_ratio_ev h, s1_N_pow_ev h hτ' (Step1Prime_K d c / (4 * 9 ^ d))] with n hn5 hnw hnr hnK
  rintro ω ⟨⟨h1, h2⟩, h3⟩ ⟨⟩
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) := Real.one_le_rpow hN1 hτ2.le
  have hNτ' : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := Real.one_le_rpow hN1 hτ'.le
  have hNsq : (((sz.size n : ℕ) : ℝ) ^ (τ' / 2)) ^ 2 = ((sz.size n : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  have hBs := s1_B_pos h n
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hgr : (sz.Bctl n (s n)) ^ ((14 : ℝ) / 15) = ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hBs.le]; norm_num
  have hQ1 : (1 : ℝ) ≤ 3 ^ d := one_le_pow₀ (by norm_num)
  have h9 : (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hLoop : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)),
      (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) σ b ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ' / 2) * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := fun σ b => by
    have hb := h3 (σ, b)
    have hz : ((1 - s n) / (1 - u n)) ^ (2 - 1) * (sz.Bctl n (s n)) ^ (2 - 1) ≤
        ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := by
      rw [← hgr]
      have := hnr (u n) (hu n).1 (hu n).2
      simpa [mul_comm] using this
    exact hb.trans (mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  change {ω | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}.indicator
      (fun ω => gmMax (baFMz sz z') n (u n) ω) ω ≤
    ((sz.size n : ℕ) : ℝ) ^ τ' * ((2 * (3 : ℝ) ^ d) * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))
  by_cases hx : gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)
  · rw [Set.indicator_of_mem (s := {ω : sz.SeqΩ | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)})
      (a := ω) hx]
    have hxe : ∀ x y : Idx d (sz.L n) (sz.W n),
        ‖(baFMz sz z').GM n (u n) ω x y‖ ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) :=
      fun x y => (BAStep1_le_gmMax (baFMz sz z') n (u n) ω x y).trans hx
    have hmpos : 0 < (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := hκm.trans_le (hmκ n)
    have hG : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z').G n (u n) ω x y‖ ≤ 1 + κm⁻¹ := by
      intro x y
      have h1' := norm_le_norm_sub_add ((baFMz sz z').G n (u n) ω x y) ((baFMz sz z').M n x y)
      have h2' := hxe x y
      change ‖(baFMz sz z').G n (u n) ω x y - (baFMz sz z').M n x y‖ ≤ _ at h2'
      have h3' : ‖(baFMz sz z').M n x y‖ ≤ ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ :=
        baM_entry_le d sz (BAflowLam0 sz z') (BAflowEs sz z') n hmpos x y
      have h4' : ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ ≤ κm⁻¹ :=
        inv_anti₀ hκm (hmκ n)
      have h5' : ((sz.W n : ℕ) : ℝ) ^ (-c') ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)
      linarith
    have hent := step1Prime_wl_det d hd c hc sz (baFMz sz z') n ω (u n) ((sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)) c'
      ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) (((sz.size n : ℕ) : ℝ) ^ (τ' / 2)) (1 + κm⁻¹) hc' hxe hn5 hNτ hnw.1 hnw.2.2
      hG hLoop (fun p => h2 p) (fun p => h1 p)
    refine BAStep1_gmMax_le (baFMz sz z') n (u n) ω fun i j => ?_
    have hij := hent i j
    rw [hNsq] at hij
    have hA0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by linarith
    have hφ0 : 0 ≤ (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15) := hnw.1.le
    have hB0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) :=
      mul_nonneg hA0 (by positivity)
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) hB0 two_ne_zero).1 ?_
    have hK : Step1Prime_K d c ≤ 4 * 9 ^ d * ((sz.size n : ℕ) : ℝ) ^ τ' := by
      have h49 : (0 : ℝ) < 4 * 9 ^ d := by positivity
      rw [div_le_iff₀ h49] at hnK
      linarith
    have e2 : (((sz.size n : ℕ) : ℝ) ^ τ' * (2 * (3 : ℝ) ^ d * (sz.Bctl n (s n)) ^ ((7 : ℝ) / 15))) ^ 2 =
        (4 * 9 ^ d * ((sz.size n : ℕ) : ℝ) ^ τ') * (((sz.size n : ℕ) : ℝ) ^ τ' *
          ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2) := by
      rw [show (9 : ℝ) ^ d = ((3 : ℝ) ^ d) ^ 2 from h9]
      ring
    rw [e2]
    have h7 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 :=
      mul_nonneg hA0 (sq_nonneg _)
    calc ‖(baFMz sz z').GM n (u n) ω i j‖ ^ 2
        ≤ Step1Prime_K d c * ((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2 := hij
      _ = Step1Prime_K d c * (((sz.size n : ℕ) : ℝ) ^ τ' * ((sz.Bctl n (s n)) ^ ((7 : ℝ) / 15)) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK h7
  · rw [Set.indicator_of_notMem (s := {ω : sz.SeqΩ | gmMax (baFMz sz z') n (u n) ω ≤ 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)})
      (a := ω) hx]
    exact mul_nonneg (by linarith) (by positivity)


/-- **Target 3, `baS1_forb'`** (primed `baS1_forb`, `BA/Step1.lean:306`): the forbidden region for all `u ∈ [s,t]` simultaneously (the merged proof
with `baS1_wl_seq'`; statement differs from `baS1_forb` in the family `hGij` and the binders `hd`, `c`, `hc` only). -/
theorem baS1_forb' (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ →
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
            (Sizes.STblk sz n p.1.2))) →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ∨
        (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) < gmMax (baFMz sz z') n (u : ℝ) ω}) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij
  have hsize := s1_hsize sz h.hN
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [h.hs0 n, h.ht1 n]
  obtain ⟨C', hC', hgop⟩ := baGopbound d sz (BAflowLam0 sz z') (BAflowEs sz z') κm hκm hmκ hm1 h.hN 1 one_pos
  obtain ⟨ε, hε, hF4⟩ := s1_F4 h
  -- the net-level forbidden region
  have hpt : PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun l => Fin (netSize C' (sz.size l) + 1))
      (fun l k ω => {ω : sz.SeqΩ | gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω ≤
          2 * (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4)}.indicator
        (fun ω => gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω) ω)
      (fun l _ _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl l (s l)) ^ ((7 : ℝ) / 15)) := by
    rw [perTimeDomAt_iff_forall_section (Sizes.seqP (sz.withLam 0)) sz.size (fun l => ⟨0⟩)]
    intro sec
    exact s1_stochDom_unit (baS1_wl_seq' d hd c hc sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hLI hGii hGij
      (fun n => BAStep1_net s t C' (sz.size n) n (sec n))
      (fun n => BAStep1_net_mem h.hst C' (sz.size n) n (sec n)))
  have hnetSD := stochDomAt_of_perTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size (C := C' + 1)
    (by linarith) (hsize.eventually (card_net_le hC'.le)) hpt
  have hnet := PerTimeCalc.Unif.forbidden_region hsize
    (x := fun l (k : Fin (netSize C' (sz.size l) + 1)) (ω : sz.SeqΩ) =>
      gmMax (baFMz sz z') l (BAStep1_net s t C' (sz.size l) l k) ω)
    (f := fun l _ => (2 * (3 : ℝ) ^ d) * (sz.Bctl l (s l)) ^ ((7 : ℝ) / 15))
    (a := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4) / 2)
    (b := fun l _ => 2 * (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4))
    (fun l _ => by
      have := Real.rpow_pos_of_pos (s1_B_pos h l) ((1 : ℝ) / 4)
      positivity) hε
    (by filter_upwards [hF4] with l hl _; exact hl) hnetSD
  -- the good event of `baGopbound`
  have hgood : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω : sz.SeqΩ | ¬ (∃ u u' : ℝ,
        0 ≤ u ∧ 0 ≤ u' ∧ u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
        |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
        ∃ x y : Idx d (sz.L n) (sz.W n),
          ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) <
            ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y -
              BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u' ω x y‖)}) := by
    intro D hD
    filter_upwards [hgop D hD] with n hn
    refine le_trans (measure_mono ?_) hn
    intro ω hω
    exact not_not.1 hω
  refine PerTimeCalc.perTimeCalc_highProbAt_mono
    (PerTimeCalc.perTimeCalc_highProbAt_inter hsize hnet hgood) ?_
  filter_upwards [h.hR, s1_F6 h] with n hR hF6
  rintro ω ⟨hω1, hω2⟩ u
  have hN1 : 1 ≤ ((sz.size n : ℕ) : ℝ) := s1_one_le_size sz n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos hN1
  obtain ⟨k, hk⟩ := BAStep1_exists_close hlen C' (sz.size n) n u.2
  have hθ := BAStep1_net_mem h.hst C' (sz.size n) n k
  have hdist : |(u : ℝ) - BAStep1_net s t C' (sz.size n) n k| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') := by
    refine hk.trans ?_
    have h1 : ((sz.size n : ℕ) : ℝ) ^ C' ≤ (netSize C' (sz.size n) : ℝ) :=
      rpow_le_netSize C' (sz.size n)
    calc 1 / (netSize C' (sz.size n) : ℝ) ≤ 1 / ((sz.size n : ℕ) : ℝ) ^ C' :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hN0 _) h1
      _ = ((sz.size n : ℕ) : ℝ) ^ (-C') := by rw [Real.rpow_neg hN0.le, one_div]
  have hrange : ∀ v ∈ Set.Icc (s n) (t n), v ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ := by
    intro v hv
    have h1 : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [h.hτ])
    rw [Real.rpow_neg_one] at h1
    linarith [hv.2]
  have hgop1 : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y -
        BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n (BAStep1_net s t C' (sz.size n) n k) ω x y‖ ≤
      ((sz.size n : ℕ) : ℝ)⁻¹ := by
    intro x y
    by_contra hlt
    push Not at hlt
    refine hω2 ⟨u, BAStep1_net s t C' (sz.size n) n k, (h.hs0 n).trans u.2.1, (h.hs0 n).trans hθ.1,
      hrange u u.2, hrange _ hθ, hdist, x, y, ?_⟩
    rwa [Real.rpow_neg_one]
  have hgop2 : ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n (BAStep1_net s t C' (sz.size n) n k) ω x y -
        BAGt sz (BAflowLam0 sz z') (BAflowEs sz z') n u ω x y‖ ≤ ((sz.size n : ℕ) : ℝ)⁻¹ :=
    fun x y => by rw [norm_sub_rev]; exact hgop1 x y
  have hup : (baFMz sz z').gmMax n u ω ≤
      (baFMz sz z').gmMax n (BAStep1_net s t C' (sz.size n) n k) ω + ((sz.size n : ℕ) : ℝ)⁻¹ :=
    BAStep1_gmMax_le_add sz (BAflowLam0 sz z') (BAflowEs sz z') n u _ _ ω hgop1
  have hdown : (baFMz sz z').gmMax n (BAStep1_net s t C' (sz.size n) n k) ω ≤
      (baFMz sz z').gmMax n u ω + ((sz.size n : ℕ) : ℝ)⁻¹ :=
    BAStep1_gmMax_le_add sz (BAflowLam0 sz z') (BAflowEs sz z') n _ u _ ω hgop2
  have hapos : 0 < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (s1_B_pos h n) _
  have hF6' : ((sz.size n : ℕ) : ℝ)⁻¹ ≤ (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) / 2 := hF6
  rcases hω1 k with h1 | h1
  · left
    change gmMax (baFMz sz z') n (BAStep1_net s t C' (sz.size n) n k) ω <
      (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) / 2 at h1
    linarith
  · right
    change 2 * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) <
      gmMax (baFMz sz z') n (BAStep1_net s t C' (sz.size n) n k) ω at h1
    linarith

/-- **Target 3, `baS1_boot'`** (primed `baS1_boot`, `BA/Step1.lean:428`): the continuity argument (the merged proof with `baS1_forb'`; statement
differs from `baS1_boot` in the family `hGij` and the binders `hd`, `c`, `hc` only). -/
theorem baS1_boot' (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ →
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
            (Sizes.STblk sz n p.1.2))) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ u : TimeIcc s t n,
      gmMax (baFMz sz z') n (u : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  have hsize := s1_hsize sz h.hN
  -- the initial condition
  have hinit : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size
      (fun n => {ω : sz.SeqΩ | gmMax (baFMz sz z') n (s n) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4)}) := by
    obtain ⟨τ₀, hτ₀, hF3⟩ := s1_F3 h
    have hev := PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt hIL hτ₀
    refine PerTimeCalc.perTimeCalc_highProbAt_mono hev ?_
    filter_upwards [hF3] with n hn ω hω
    have hb : (baFMz sz z').gmMax n (s n) ω ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₀ * (sz.Bctl n (s n)) ^ ((1 : ℝ) / 2) :=
      BAStep1_gmMax_le (baFMz sz z') n (s n) ω fun x y => hω (x, y)
    exact lt_of_le_of_lt hb hn
  have hcont : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun l => {ω : sz.SeqΩ | ContinuousOn
      (fun u => gmMax (baFMz sz z') l u ω) (Set.Icc (s l) (t l))}) :=
    PerTimeCalc.perTimeCalc_highProbAt_mono (highProbAt_univ _ _)
      (Eventually.of_forall fun l ω _ =>
        BAStep1_gmMax_continuousOn sz (BAflowLam0 sz z') (BAflowEs sz z') l (hκm.trans_le (hmκ l))
          (h.ht1 l) ω)
  exact PerTimeCalc.stepOneBootstrap hsize (M := fun l v (ω : sz.SeqΩ) => gmMax (baFMz sz z') l v ω)
    (a := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4)) (b := fun l _ => (sz.Bctl l (s l)) ^ ((1 : ℝ) / 4))
    (s := s) (t := t) hcont (fun l => continuousOn_const) (Eventually.of_forall fun l u => le_rfl)
    (baS1_forb' d hd c hc sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij) hinit

/-- **Target 3, `baS1_weakPT'`** (primed `baS1_weakPT`, `BA/Step1.lean:469`): `(Gtmwc)` per time over `[s,t]` (the merged proof with `baS1_boot'`;
statement differs from `baS1_weakPT` in the family `hGij` and the binders `hd`, `c`, `hc` only). -/
theorem baS1_weakPT' (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ →
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
            (Sizes.STblk sz n p.1.2))) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
      (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z').GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  have hsize := s1_hsize sz h.hN
  have hboot := baS1_boot' d hd c hc sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  refine PerTimeCalc.PerTime.stochDom_of_highProb hsize (fun n p ω =>
    Real.rpow_nonneg (s1_Bu_pos h n p.1.2.2).le _) ?_
  refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot (Eventually.of_forall fun n ω hω p => ?_)
  obtain ⟨u, i, j⟩ := p
  have h1 := BAStep1_le_gmMax (baFMz sz z') n (u : ℝ) ω i j
  have h2 := hω u
  have h3 : sz.Bctl n (s n) ≤ sz.Bctl n u :=
    sz.STBctl_mono n u.2.1 (lt_of_le_of_lt u.2.2 (h.ht1 n))
  have h4 : (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow (s1_B_pos h n).le h3 (by norm_num)
  exact (h1.trans h2.le).trans h4

/-- **Target 3, `baS1_loopPT'`** (primed `baS1_loopPT`, `BA/Step1.lean:507`): `(lRB1)` per time over `[s,t]` (the merged proof with `baS1_boot'`;
statement differs from `baS1_loopPT` in the family `hGij` and the binders `hd`, `c`, `hc` only). -/
theorem baS1_loopPT' (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    ∀ (sz : Sizes d) (z' : ℕ → ℂ) (κ' 𝔠 𝔡 τ 𝔠d κm : ℝ) (Ed s t : ℕ → ℝ),
    RBM.Ind.S1Std sz κ' 𝔠 𝔡 τ 𝔠d Ed s t → 0 < κm →
    (∀ n, κm ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im) →
    (∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ k : ℕ, 1 ≤ k →
      PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (u n) (1 + κm⁻¹) ω * ‖(baFMz sz z').L n (u n) p.1 p.2 ω‖)
        (fun n _ _ => ((1 - s n) / (1 - u n)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀) →
    (∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ →
        PrecL sz (Sizes.seqP (sz.withLam 0))
          (U := fun n => {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2})
          (fun n p ω => (baFMz sz z').indMax n (u n) (((sz.W n : ℕ) : ℝ) ^ (-ε₀)) ω *
            ‖(baFMz sz z').GM n (u n) ω p.1.1 p.1.2‖)
          (fun n p _ => GreenCore_decayRHS d (sz.L n) (sz.W n) c D (Φ n) (Ψ n) (Sizes.STblk sz n p.1.1)
            (Sizes.STblk sz n p.1.2))) →
    STLocalMaxgL (baFMz sz z') (Sizes.seqP (sz.withLam 0)) s →
    ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) := by
  intro sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL k hk
  have hsize := s1_hsize sz h.hN
  have hboot := baS1_boot' d hd c hc sz z' κ' 𝔠 𝔡 τ 𝔠d κm Ed s t h hκm hmκ hm1 hLI hGii hGij hIL
  refine PerTimeCalc.PerTime.stochDom_of_indicator hsize
    (Ωs := fun n p => {ω : sz.SeqΩ | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹}) ?_ ?_
  · refine PerTimeCalc.perTimeCalc_highProbAt_mono hboot ?_
    filter_upwards [s1_F7 h] with n hF7 ω hω p x y
    have hmpos : 0 < (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im := hκm.trans_le (hmκ n)
    have h1 := norm_le_norm_sub_add ((baFMz sz z').G n (p.1 : ℝ) ω x y) ((baFMz sz z').M n x y)
    have h2 := BAStep1_le_gmMax (baFMz sz z') n (p.1 : ℝ) ω x y
    have h3 := hω p.1
    have h4 : ‖(baFMz sz z').M n x y‖ ≤ ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ :=
      baM_entry_le d sz (BAflowLam0 sz z') (BAflowEs sz z') n hmpos x y
    have h5 : ((BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im)⁻¹ ≤ κm⁻¹ :=
      inv_anti₀ hκm (hmκ n)
    change ‖(baFMz sz z').G n (p.1 : ℝ) ω x y - (baFMz sz z').M n x y‖ ≤ _ at h2
    change (baFMz sz z').gmMax n (p.1 : ℝ) ω < (sz.Bctl n (s n)) ^ ((1 : ℝ) / 4) at h3
    change ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹
    linarith
  · have key : PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
        (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n p ω => (baFMz sz z').omegaC n (p.1 : ℝ) (1 + κm⁻¹) ω *
          ‖(baFMz sz z').L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1)) :=
      BAStep1_perTime_timeIcc (Sizes.seqP (sz.withLam 0)) sz.size h.hst
        (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
        (fun n => ⟨(fun _ => true, fun _ => 0)⟩)
        (fun n v q (ω : sz.SeqΩ) => (baFMz sz z').omegaC n v (1 + κm⁻¹) ω * ‖(baFMz sz z').L n v q.1 q.2 ω‖)
        (fun n v _ _ => ((1 - s n) / (1 - v)) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))
        (fun u hu => perTimeOfStochDomAt (Sizes.seqP (sz.withLam 0)) sz.size _ _ (hLI u hu k hk))
    refine PerTimeCalc.PerTime.stochDom_of_le_left_eventually
      (Eventually.of_forall fun n p ω => le_of_eq ?_) key
    by_cases hg : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z').G n (p.1 : ℝ) ω x y‖ ≤ 1 + κm⁻¹
    · simp [Set.indicator, FlowFM.omegaC, hg]
    · simp [Set.indicator, FlowFM.omegaC, hg]

end Weak

/-! ## 4. Targets 4-5: the primed bootstrap and Step 1 at BA -/

section Main

open RBM.Ind FlowFM

/-- **Target 4a** (`baBootstrap'_of_ij'`, pin `T2468_BootstrapIj'`): `baBootstrap'_holds` (`BA/Step1.lean:576`) with the primed pin
`BAGbEXPij'` in place of `BAGbEXPij`, guard `2 ≤ d` (that of the merged Green pins; paper deltas T2403a, T2408b).  Proof: the
merged one, with `baGij'_member` (the rate `c` fixed after `(κ, ε, 𝔡)`) and `baS1_loopPT'`, `baS1_weakPT'`. -/
theorem baBootstrap'_of_ij' (d : ℕ) (hd : 2 ≤ d) : BAFlowMember d → BAGbEXPii d → BAGbEXPij' d → BABootstrap' d := by
  intro hmem hii hij κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 hsT hst htT z' hfam
    hK hLK hLoc hCond hcon
  have h := baS1Std d κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow s t hs0 (fun n => (hst n).le) htT hCond
  have hfam0 : BAFamZ sz z c₁ (fun _ => 0) z' :=
    BAFamZ_mono (fun n => (hs0 n).trans (hst n).le) hfam
  have him : ∀ n, κ ≤ (BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n).im :=
    BAFamZ_im_m_ge hκ hflow hlam hc₁ hc₁' hwin hfam0
  have hm1 : ∀ n, ‖BAmF sz (BAflowLam0 sz z') (BAflowEs sz z') n‖ ≤ 1 := fun n =>
    BAStep1_norm_BAmF_le_one sz _ _ n (hκ.trans_le (him n))
  have hLI := baBoot_LI d κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin s t hs0 (fun n => (hst n).le) htT z'
    hfam (fun u h1 h2 => (hcon u h1 h2).1) (1 + κ⁻¹) (by positivity)
  have hGii : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz z' u ε₀ :=
    fun u hu ε₀ hε₀ => baGii_member d hii hmem κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u
      (fun n => (hs0 n).trans (hu n).1) (fun n => (hu n).2) ε₀ hε₀
  obtain ⟨c, hc, hmain⟩ := baGij'_member d hij hmem κ ε 𝔡 hκ hε h𝔡
  have hGij : ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (s n) (t n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz z' u ε₀ Φ → GreenCore_decayConcl sz z' u ε₀ D c Φ Ψ :=
    fun u hu ε₀ hε₀ D hD Φ Ψ h1 h2 h3 hp =>
      hmain 𝔠 sz z hflow hlam c₁ hc₁ hc₁' hwin t htT z' hfam u (fun n => (hs0 n).trans (hu n).1)
        (fun n => (hu n).2) ε₀ hε₀ D hD Φ Ψ h1 h2 h3 hp
  have hnet := baNetLift d sz (BAflowLam0 sz z') (BAflowEs sz z') κ (ε / 2) s t hκ him hm1 (half_pos hε) hs0
    (fun n => (hst n).le) h.ht1 h.hN h.hR
  exact ⟨hnet.1 (baS1_loopPT' d hd c hc sz z' (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d κ (fun _ => 0) s t h hκ him hm1 hLI hGii hGij hLoc),
    hnet.2 (baS1_weakPT' d hd c hc sz z' (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d κ (fun _ => 0) s t h hκ him hm1 hLI hGii hGij hLoc)⟩

/-- **Target 4b** (`baStep1_of_ij'`, pin `T2468_Step1Ij'`): `baStep1_holds` (`BA/Step1Fam.lean:695`) through `BAStep1_of_parts'`
with `baBootstrap'_of_ij'`; guard `2 ≤ d`. -/
theorem baStep1_of_ij' (d : ℕ) (hd : 2 ≤ d) : BAGbEXPii d → BAGbEXPij' d → BAStep1 d := fun hii hij =>
  BAStep1_of_parts' d (BAFlowMember_holds d) (BALmaxFromLK_holds d) (BATrivialLmax_holds d) (baConArg''_holds d)
    (baBootstrap'_of_ij' d hd (BAFlowMember_holds d) hii hij)

/-- **Target 5a** (`baBootstrap'_holds'`, pin `T2468_BootstrapHolds`): the bootstrap `BABootstrap'` at BA, unconditional for
`2 ≤ d`: `baBootstrap'_of_ij'` applied to `BAFlowMember_holds`, `baGbEXPii_holds`, `baGbEXPij'_holds`. -/
theorem baBootstrap'_holds' (d : ℕ) (hd : 2 ≤ d) : BABootstrap' d :=
  baBootstrap'_of_ij' d hd (BAFlowMember_holds d) (baGbEXPii_holds d hd) (baGbEXPij'_holds d hd)

/-- **Target 5b** (`baStep1_holds'`, pin `T2468_Step1Holds`): Step 1 of `lem:main_ind_BA` at BA (`BAStep1 d`), unconditional for
`2 ≤ d`: `baStep1_of_ij'` applied to `baGbEXPii_holds`, `baGbEXPij'_holds`.  The named producer for U3-BA (b) and U5
(REQ UBA `:30`). -/
theorem baStep1_holds' (d : ℕ) (hd : 2 ≤ d) : BAStep1 d :=
  baStep1_of_ij' d hd (baGbEXPii_holds d hd) (baGbEXPij'_holds d hd)

end Main

/-! ## 5. Target 6: the BA readings of the generic Green pins (registry `:148`, `:150`) -/

section Readings

/-- **Target 6a** (`baSTGiiGEXgL_holds`, pin `T2468_STGiiBA`): the generic `(GiiGEX)` at the BA carrier `baFMz sz z` and the law
`seqP (sz.withLam 0)`, from `baGbEXPii_holds` (`BAGiiGEX` is `STGiiGEXgL` at `baFMz`: `FlowFM.indMax` and `STindMaxg` have the same
body). -/
theorem baSTGiiGEXgL_holds (d : ℕ) (hd : 2 ≤ d) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGiiGEXgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ :=
  fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ =>
    baGbEXPii_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀

/-- **Target 6b** (`baSTGavLGEXgL_holds`, pin `T2468_STGavBA`): the generic `(GavLGEX)` at the BA carrier and law, from
`baGbEXPav_holds` (`STInitialGT2gL` is the conjunction of the two premises of `STGavLGEXgL`). -/
theorem baSTGavLGEXgL_holds (d : ℕ) (hd : 2 ≤ d) : ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ ε₀ : ℝ, 0 < ε₀ → STGavLGEXgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ :=
  fun κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ h1 h2 hA hB =>
    baGbEXPav_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ h1 h2 ⟨hA, hB⟩

end Readings

end RBM.BA

/-! ## 6. Compiled nonempty instances (`RBM.BA.Step1PrimeInst`)

The data are those of the merged instances (`BA/Step1.lean` §5, `BA/Step1Fam.lean` §6): `d = 3`, `sz0` (`L_n = 4(n+1)`,
`W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the spectral parameters `zSeq`
(`BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` is `flow_sz0`), the member `z' = zSeq`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`𝔠d = 1/100`, `c₁ = 1/3`, `(s, t) = (1/2, 2/3)` (`sI`, `tI`) and `(0, 1/16)` (`sInst`, `tInst`).  Every deterministic hypothesis
is discharged: the window `BAWinBulk sz0 zSeq (1/3) (1/2)` (`sz0_win_third`), `BAFlowMember_holds`, and the three Green pins
`baGbEXPii_holds`, `baGbEXPij'_holds` (the diagonal and band pins of `lem_GbEXP_BA`), and, for the bootstrap, `hK` by
`inst_BAKbound` (supervisor `2026-10-11-0150` O2).  What stays a hypothesis: the initial data `STLKgL`, `STLocalMaxgL` of the
carrier at `sI` and, for the family form, the per-member premise (BA-V's).  The conclusions are `∀ᶠ` statements; they claim no
value at a finite `n`. -/

namespace RBM.BA.Step1PrimeInst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA RBM.BA.FlowPinsInst RBM.Gauss.SizesInst
  RBM.BA.Step1SetupInst RBM.Gauss.InductionDefsInst RBM.BA.Step1Inst RBM.BA.Step1FamInst

open private BASetup_maxLoop_nonneg BASetup_omegaC_le_one from RBM3D.BA.Step1Setup

/-- **Instance of `baGij'_member`** (target 1): `d = 3`, `sz0`, `zSeq`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `c₁ = 1/3`,
`t ≡ 2/3`, the member `z' = zSeq`, every `u ∈ [1/2, 2/3]`; the pins `BAGbEXPij' 3` (`baGbEXPij'_holds`), `BAFlowMember 3` and the
window are discharged.  The rate `c` is produced by the theorem (existential, as in the pin). -/
theorem inst_baGij'_member :
    ∃ c : ℝ, 0 < c ∧ ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sI n) (tI n)) → ∀ ε₀ : ℝ, 0 < ε₀ → ∀ D : ℝ, 0 < D →
      ∀ (Φ : ∀ n, Zd 3 (sz0.L n) → Zd 3 (sz0.L n) → ℝ) (Ψ : ℕ → ℝ),
        (∀ᶠ n in atTop, ∀ a b, 0 < Φ n a b ∧ Φ n a b ≤ ((sz0.W n : ℕ) : ℝ) ^ (-ε₀)) →
        (∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) ≤ Ψ n) →
        (∀ᶠ n in atTop, Ψ n ≤ ((sz0.W n : ℕ) : ℝ) ^ (-ε₀)) →
        GreenCore_loopPrem sz0 zSeq u ε₀ Φ → GreenCore_decayConcl sz0 zSeq u ε₀ D c Φ Ψ := by
  obtain ⟨c, hc, H⟩ := baGij'_member 3 (baGbEXPij'_holds 3 (by norm_num)) (BAFlowMember_holds 3) (1 / 2) (1 / 10) (1 / 10)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, fun u hu ε₀ hε₀ D hD Φ Ψ h1 h2 h3 hp => ?_⟩
  have h2' : ∀ᶠ n in atTop, ((sz0.W n : ℕ) : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ Ψ n := by
    simpa using h2
  exact H (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num) sz0_win_third tI
    (fun n => t0_sz0 n) zSeq (BAFamZ_main sz0 zSeq (1 / 3) tI) u
    (fun n => (show (0 : ℝ) ≤ sI n by norm_num [sI]).trans (hu n).1) (fun n => (hu n).2) ε₀ hε₀ D hD Φ Ψ h1 h2' h3 hp

/-- **Instance of `step1Prime_loopPrem`** (target 2 (a)): the data above, `u ≡ 2/3 ∈ [1/2, 2/3]`, `κm = 1/2`, any `ε₀ > 0`; the
`k = 2` loop input is the merged `inst_hLI` (`baBoot_LI` with the proved window).  No hypothesis is left. -/
theorem inst_step1Prime_loopPrem (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    GreenCore_loopPrem sz0 zSeq (fun _ => 2 / 3) ε₀ (fun n _ _ => (sz0.Bctl n (sI n)) ^ ((7 : ℝ) / 15)) :=
  step1Prime_loopPrem 3 sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (1 / 2) (fun _ => 0) sI tI
    inst_baS1Std (by norm_num) inst_im_m_ge (fun _ => 2 / 3) (fun _ => ⟨by norm_num [sI], by norm_num [tI]⟩)
    (inst_hLI sz0_win_third (fun _ => 2 / 3) (fun _ => ⟨by norm_num [sI], by norm_num [tI]⟩) 2 (by norm_num)) ε₀ hε₀

/-- **Instance of `step1Prime_wl_det`** (target 2 (b)) at the carrier `baFMz sz0 zSeq`, `n = 0`, `u = 0` (so `G_0 = M`,
`G - M = 0`), `c = 1`, `a = 1/64` (`2a = 1/32 ≤ W^{-1/20}`, `W_0 = 32`), `c' = 1/20`, `φ = 1/10` (`W^{-3/2} ≤ 1/32 ≤ φ`),
`Nτ = 4`, `C₀ = 3`.  The loop premise is `baFM_loop_det` (`‖𝓛^{(2)}_0‖ ≤ 4 W^{-3} ≤ Nτ φ²`).  Every hypothesis is discharged. -/
theorem inst_step1Prime_wl_det (ω : sz0.SeqΩ) :
    ∀ i j : Idx 3 (sz0.L 0) (sz0.W 0), ‖(baFMz sz0 zSeq).GM 0 0 ω i j‖ ^ 2 ≤
      Step1Prime_K 3 1 * (4 : ℝ) ^ 2 * (1 / 10 : ℝ) ^ 2 := by
  have hm := BAmF_sz0_im_pos 0
  have hmge := inst_im_m_ge 0
  have hW32 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by
    rw [sz0_values.2.1]
    norm_num
  have hGMz : ∀ x y : Idx 3 (sz0.L 0) (sz0.W 0), (baFMz sz0 zSeq).GM 0 0 ω x y = 0 := inst_GM_zero ω
  refine step1Prime_wl_det 3 (by norm_num) 1 one_pos sz0 (baFMz sz0 zSeq) 0 ω 0 (1 / 64) (1 / 20) (1 / 10) 4 3
    (by norm_num) ?_ ?_ (by norm_num) (by norm_num) ?_ ?_ ?_ ?_ ?_
  · intro x y
    rw [hGMz]
    norm_num
  · rw [hW32]
    calc 2 * (1 / 64 : ℝ) = (32 : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
          norm_num
      _ ≤ (32 : ℝ) ^ (-(1 / 20 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  · rw [hW32]
    calc (32 : ℝ) ^ (-((3 : ℕ) : ℝ) / 2) ≤ (32 : ℝ) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ 1 / 10 := by
          rw [Real.rpow_neg_one]
          norm_num
  · intro x y
    have h1 := norm_le_norm_sub_add ((baFMz sz0 zSeq).G 0 0 ω x y) ((baFMz sz0 zSeq).M 0 x y)
    have h2 : ‖(baFMz sz0 zSeq).G 0 0 ω x y - (baFMz sz0 zSeq).M 0 x y‖ = 0 := by
      have := hGMz x y
      change (baFMz sz0 zSeq).G 0 0 ω x y - (baFMz sz0 zSeq).M 0 x y = 0 at this
      rw [this, norm_zero]
    have h3 : ‖(baFMz sz0 zSeq).M 0 x y‖ ≤ ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im)⁻¹ :=
      baM_entry_le 3 sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 hm x y
    have h4 : ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) hmge
    have h5 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    linarith
  · intro σ b
    have hη : (1 / 2 : ℝ) ≤ (ztOf (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0)
        (BAflowEs sz0 zSeq 0) 0).im := by
      rw [ztOf_im]
      unfold etaOf
      linarith
    have hdet := baFM_loop_det sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 0 (1 / 2) (by norm_num) hη 2
      (by norm_num) σ b ω
    have hom := BASetup_omegaC_le_one (baFMz sz0 zSeq) 0 0 3 ω
    have hL : ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖ ≤ 4 * (1 / 10 : ℝ) ^ 2 := by
      refine hdet.trans ?_
      rw [hW32]
      norm_num
    calc (baFMz sz0 zSeq).omegaC 0 0 3 ω * ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖
        ≤ ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖ := mul_le_of_le_one_left (norm_nonneg _) hom
      _ ≤ _ := hL
  · intro p
    have := BASetup_maxLoop_nonneg (baFMz sz0 zSeq) 0 0 ω
    simp only [hGMz, norm_zero]
    nlinarith [this]
  · intro p
    have h0 : 0 ≤ GreenCore_decayRHS 3 (sz0.L 0) (sz0.W 0) 1 (((3 : ℕ) : ℝ) / 2) (fun _ _ => (1 / 10 : ℝ)) (1 / 10)
        (STblk sz0 0 p.1.1) (STblk sz0 0 p.1.2) := by
      unfold GreenCore_decayRHS
      positivity
    simp only [hGMz, norm_zero]
    nlinarith [h0]

/-- The instance of `step1Prime_wl_det` at the all-ones sample. -/
example := inst_step1Prime_wl_det (fun _ => (1 : ℝ))

/-- The proved diagonal hypothesis `(GiiGEX)` of the member `zSeq` at `d = 3` (`baGii_member` with `baGbEXPii_holds`). -/
theorem inst_hGii' :
    ∀ u : ℕ → ℝ, (∀ n, u n ∈ Set.Icc (sI n) (tI n)) → ∀ ε₀ : ℝ, 0 < ε₀ → BAGiiGEX sz0 zSeq u ε₀ :=
  inst_hGii (baGbEXPii_holds 3 (by norm_num)) (BAFlowMember_holds 3) sz0_win_third

/-- **Instance of `baS1_wl_seq'`** (target 3): the data above, the time sequence `u ≡ 2/3 ∈ [1/2, 2/3]`, `κm = 1/2`; the primed
member family is `inst_baGij'_member` (rate `c` existential); no hypothesis is left. -/
theorem inst_baS1_wl_seq' :
    ∃ c : ℝ, 0 < c ∧ PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size (U := fun _ => Unit)
      (fun n _ ω => {ω | (baFMz sz0 zSeq).gmMax n ((fun _ => (2 / 3 : ℝ)) n) ω ≤
          2 * (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4)}.indicator
        (fun ω => (baFMz sz0 zSeq).gmMax n ((fun _ => (2 / 3 : ℝ)) n) ω) ω)
      (fun n _ _ => (2 * (3 : ℝ) ^ 3) * (sz0.Bctl n (sI n)) ^ ((7 : ℝ) / 15)) := by
  obtain ⟨c, hc, hfam⟩ := inst_baGij'_member
  exact ⟨c, hc, baS1_wl_seq' 3 (by norm_num) c hc sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100)
    (1 / 2) (fun _ => 0) sI tI inst_baS1Std (by norm_num) inst_im_m_ge (inst_hLI sz0_win_third) inst_hGii' hfam
    (fun _ => 2 / 3) (fun _ => ⟨by norm_num [sI], by norm_num [tI]⟩)⟩

/-- **Instance of `baS1_forb'`** (target 3): the same data. -/
theorem inst_baS1_forb' :
    ∃ c : ℝ, 0 < c ∧ HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (fun n => {ω | ∀ u : TimeIcc sI tI n,
      (baFMz sz0 zSeq).gmMax n (u : ℝ) ω < (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4) ∨
        (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4) < (baFMz sz0 zSeq).gmMax n (u : ℝ) ω}) := by
  obtain ⟨c, hc, hfam⟩ := inst_baGij'_member
  exact ⟨c, hc, baS1_forb' 3 (by norm_num) c hc sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100)
    (1 / 2) (fun _ => 0) sI tI inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI sz0_win_third)
    inst_hGii' hfam⟩

/-- **Instance of `baS1_boot'`** (target 3): the same data; `STLocalMaxgL` of the carrier at `sI` (other gate's) is a
hypothesis. -/
theorem inst_baS1_boot'
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    ∃ c : ℝ, 0 < c ∧ HighProbAt (Sizes.seqP (sz0.withLam 0)) sz0.size (fun n => {ω | ∀ u : TimeIcc sI tI n,
      (baFMz sz0 zSeq).gmMax n (u : ℝ) ω < (sz0.Bctl n (sI n)) ^ ((1 : ℝ) / 4)}) := by
  obtain ⟨c, hc, hfam⟩ := inst_baGij'_member
  exact ⟨c, hc, baS1_boot' 3 (by norm_num) c hc sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100)
    (1 / 2) (fun _ => 0) sI tI inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI sz0_win_third)
    inst_hGii' hfam hLoc⟩

/-- **Instance of `baS1_weakPT'`** (target 3): the same data. -/
theorem inst_baS1_weakPT'
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    ∃ c : ℝ, 0 < c ∧ PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
      (U := fun n => TimeIcc sI tI n × Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
      (fun n p ω => ‖(baFMz sz0 zSeq).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
      (fun n p _ => (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) := by
  obtain ⟨c, hc, hfam⟩ := inst_baGij'_member
  exact ⟨c, hc, baS1_weakPT' 3 (by norm_num) c hc sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100)
    (1 / 2) (fun _ => 0) sI tI inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI sz0_win_third)
    inst_hGii' hfam hLoc⟩

/-- **Instance of `baS1_loopPT'`** (target 3): the same data, every `k ≥ 1`. -/
theorem inst_baS1_loopPT'
    (hLoc : STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
        (U := fun n => TimeIcc sI tI n × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => ‖(baFMz sz0 zSeq).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - sI n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz0.Bctl n (sI n)) ^ (k - 1)) := by
  obtain ⟨c, hc, hfam⟩ := inst_baGij'_member
  exact ⟨c, hc, baS1_loopPT' 3 (by norm_num) c hc sz0 zSeq (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100)
    (1 / 2) (fun _ => 0) sI tI inst_baS1Std (by norm_num) inst_im_m_ge inst_norm_m_le (inst_hLI sz0_win_third)
    inst_hGii' hfam hLoc⟩

/-- **Instance of `baBootstrap'_of_ij'`** (target 4a, pin `T2468_InstBootstrap`): `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠d = 1/100`,
`𝔠 = 1/6`, `c₁ = 1/3`, `s ≡ 1/2 < t ≡ 2/3 ≤ t₀`, the member `z' = zSeq`.  `hmem`, `hwin` (`sz0_win_third`), `hii`, `hij'` and
`hK` (`inst_BAKbound`, supervisor `2026-10-11-0150` O2) are discharged, as are `STConStInd` and both halves of the ConArg
premise (`inst_hcon_full`); `hLK`, `hLoc` stay (BA-V's). -/
theorem inst_baBootstrap'_ij' :
    STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI →
      STLocalMaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI →
        STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
          STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
  fun hLK hLoc =>
    baBootstrap'_of_ij' 3 (by norm_num) (BAFlowMember_holds 3) (baGbEXPii_holds 3 (by norm_num))
      (baGbEXPij'_holds 3 (by norm_num)) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
      (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num)
      sz0_win_third sI tI (fun _ => by norm_num [sI]) (fun n => (show sI n ≤ 2 / 3 by norm_num [sI]).trans (t0_sz0 n))
      (fun _ => by norm_num [sI, tI]) (fun n => t0_sz0 n) zSeq (BAFamZ_main sz0 zSeq (1 / 3) tI) inst_BAKbound hLK hLoc
      (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (s0 := 1 / 2) (t0 := 2 / 3) (by norm_num) (by norm_num)
        (by norm_num)) (inst_hcon_full sz0_win_third)

/-- **Instance of `baStep1_holds'`** (targets 4b, 5b, pin `T2468_InstStep1`) at `sz0`, `(s, t) = (1/2, 2/3)`: window
`sz0_win_third`, `STConStInd` by `s1Setup_conStInd_const`; no Green pin is a hypothesis; the per-member family premise stays
(supervisor `2026-10-11-0150` K2: the discharge is BA-V's). -/
theorem inst_baStep1' :
    (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sI z' →
      STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧
        STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI ∧
        STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sI) →
      STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
        STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI :=
  fun hmemb =>
    baStep1_holds' 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
      (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num)
      sz0_win_third sI tI (fun _ => by norm_num [sI]) (fun n => (show sI n ≤ 2 / 3 by norm_num [sI]).trans (t0_sz0 n))
      (fun _ => by norm_num [sI, tI]) (fun n => t0_sz0 n) hmemb
      (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (s0 := 1 / 2) (t0 := 2 / 3) (by norm_num) (by norm_num)
        (by norm_num)) zSeq (BAFamZ_main sz0 zSeq (1 / 3) tI)

/-- **Instance of `baStep1_holds'` at `sz0`, `(s, t) = (0, 1/16)`** (`t < 1 - c₁`, so the ConArg range of `BABootstrap'` is
`{u ≡ 2/3}`, above `t`: the §86 case). -/
theorem inst_baStep1'_low :
    (∀ z' : ℕ → ℂ, BAFamZ sz0 zSeq (1 / 3) sInst z' →
      STKboundgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) ∧
        STLKgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst ∧
        STLocalMaxgL (baFMz sz0 z') (Sizes.seqP (sz0.withLam 0)) sInst) →
      STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst ∧
        STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sInst tInst :=
  fun hmemb =>
    baStep1_holds' 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
      (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sz0_lam_pos (1 / 3) (by norm_num) (by norm_num)
      sz0_win_third sInst tInst (fun _ => le_rfl) (fun n => (sz0_T0_pos n).le.trans' (by norm_num [sInst]))
      (fun n => by simp only [sInst, tInst]; norm_num)
      (fun n => (show tInst n ≤ 2 / 3 by norm_num [tInst]).trans (t0_sz0 n)) hmemb (conStInd_inst (by norm_num)) zSeq
      (BAFamZ_main sz0 zSeq (1 / 3) tInst)

/-- The conditional form `baStep1_of_ij'` at `d = 3` with the three proved pins supplied (the pin's two hypotheses are
`baGbEXPii_holds`, `baGbEXPij'_holds`). -/
example : BAStep1 3 := baStep1_of_ij' 3 (by norm_num) (baGbEXPii_holds 3 (by norm_num)) (baGbEXPij'_holds 3 (by norm_num))

/-- The unconditional producers at `d = 3`. -/
example : BABootstrap' 3 ∧ BAStep1 3 := ⟨baBootstrap'_holds' 3 (by norm_num), baStep1_holds' 3 (by norm_num)⟩

/-- **Instances of `baSTGiiGEXgL_holds`, `baSTGavLGEXgL_holds`** (target 6): `d = 3`, `sz0`, `zSeq`, `κ = 1/2`,
`ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `t ≡ 2/3 ≤ t₀`, `ε₀ = 1/10`; no hypothesis is left. -/
example : STGiiGEXgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tI (1 / 10) :=
  baSTGiiGEXgL_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 tI (fun _ => by norm_num [tI]) (fun n => t0_sz0 n) (1 / 10) (by norm_num)

example : STGavLGEXgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) tI (1 / 10) :=
  baSTGavLGEXgL_holds 3 (by norm_num) (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq
    flow_sz0 tI (fun _ => by norm_num [tI]) (fun n => t0_sz0 n) (1 / 10) (by norm_num)

/-- Optional (supervisor `2026-10-11-0150` O2): `inst_BAKbound` feeds `inst_BALmaxFromLK`; only `hLK` stays. -/
example : STLKgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI →
    STLmaxgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI :=
  fun hLK => inst_BALmaxFromLK inst_BAKbound hLK

end RBM.BA.Step1PrimeInst
