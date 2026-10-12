/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.TwistKer
import RBM3D.BA.KInduct
import RBM3D.Induction.KDecay
import RBM3D.Induction.Contract

/-!
# BA stage TL, row TL2b (T2429), part 2: the sources of the twisted Duhamel formula

The statements `BATwistSrc1`, `BATwistSrc2`, `BATwistSrc4`, `BATwistSrc5` of
`BA/TwistPins.lean:261-277` (Lemma T.11 (i), (ii), (iv), (v) of
`docs/tickets/T2398-TL-proofs.md`) are proved for every regime `R`, in the frame `BATwFrame`
(Steps 1-4 on `[s,t]` as the hypothesis `twSteps`, `(con_st_ind)`), from the merged inputs and the
deterministic kernel and fine-lattice facts of `BA/TwistKer.lean`.

* (i): `twK_bound_holds` (made uniform in the time by `TwistKer2_unif`) and the third conjunct of
  `twSteps` at `k = 2`.
* (ii): the fold and Ward core `TwistKer_twEG_le` (T.4 at `n = 3`), `STAvgUgL` with
  `baKsol_one`, the second conjunct of `twSteps` at `k = 1, 3`.
* (iv): `(4.16)` at the carrier (stem copies of `SEforLn2_{Bctl_ge_inv, WD, conU, sumTwo_pt, sum2}`)
  and `STGdecayWgL`, with `𝔠_d = min (1/100) (1/(30 C_d))`.
* (v): entries of `G` from the 2-loop decay (fourth conjunct of `twSteps` at `k = 2`),
  `baTwKDecay_holds`, against deterministic polynomial bounds.

Private helpers carry the stem `TwistKer2_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.flexible false

open MeasureTheory Filter
open scoped Matrix

noncomputable section

namespace RBM.BA
open RBM RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. Generic calculus of `StochDomAt` and uniformity in the time -/

section Calculus

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U U₁ : ℕ → Type*}

/-- `StochDomAt.of_subset` with a source family on another parameter type (a copy of the private `SEforLn2_of_subset`, `Induction/SEforLn2.lean:269`). -/
private theorem TwistKer2_of_subset {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ} {ξ ζ : ∀ l, U l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop, badSetAt size ξ ζ τ l ⊆ badSetAt size ξ₁ ζ₁ τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  exact (measure_mono h1).trans h2

/-- **Transfer through a pointwise comparison** (`StochDomAt.of_subset` with the same `τ` split in halves): if eventually
`ξ(u,ω) ≤ c · κ(u,ω) · ξ₁(φ(u,ω), ω)` and `κ(u,ω) · ζ₁(φ(u,ω), ω) ≤ ζ(u,ω)` with `κ ≥ 0`, `ξ₁ ≥ 0`, then `ξ₁ ≺ ζ₁` gives `ξ ≺ ζ`
(`φ` may depend on `ω`: the maximiser of a sum). -/
private theorem TwistKer2_comp (hsize : Tendsto size atTop atTop) {ξ ζ : ∀ l, U l → Ω → ℝ} {ξ₁ ζ₁ : ∀ l, U₁ l → Ω → ℝ}
    (h : StochDomAt P size ξ₁ ζ₁) (φ : ∀ l, U l → Ω → U₁ l) (κ : ∀ l, U l → Ω → ℝ) {c : ℝ}
    (hξ₁ : ∀ l u ω, 0 ≤ ξ₁ l u ω) (hκ : ∀ l u ω, 0 ≤ κ l u ω)
    (hle : ∀ᶠ l in atTop, ∀ u ω, ξ l u ω ≤ c * (κ l u ω * ξ₁ l (φ l u ω) ω))
    (hζ : ∀ᶠ l in atTop, ∀ u ω, κ l u ω * ζ₁ l (φ l u ω) ω ≤ ζ l u ω) : StochDomAt P size ξ ζ := by
  refine TwistKer2_of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hsize.eventually (eventually_le_rpow c (half_pos hτ)), hle, hζ] with l hcN hl hz
  intro ω ⟨u, hu⟩
  refine ⟨φ l u ω, ?_⟩
  by_contra hno
  simp only [not_lt] at hno
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hk := hκ l u ω
  have := calc ξ l u ω ≤ c * (κ l u ω * ξ₁ l (φ l u ω) ω) := hl u ω
    _ ≤ (size l : ℝ) ^ (τ / 2) * (κ l u ω * ξ₁ l (φ l u ω) ω) :=
        mul_le_mul_of_nonneg_right hcN (mul_nonneg hk (hξ₁ l _ ω))
    _ ≤ (size l : ℝ) ^ (τ / 2) * (κ l u ω * ((size l : ℝ) ^ (τ / 2) * ζ₁ l (φ l u ω) ω)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hno hk) hpos
    _ = (size l : ℝ) ^ τ * (κ l u ω * ζ₁ l (φ l u ω) ω) := by
        rw [← UnifDetDom.rpow_half_mul_rpow_half (size l) hτ]; ring
    _ ≤ (size l : ℝ) ^ τ * ζ l u ω := mul_le_mul_of_nonneg_left (hz u ω) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact absurd hu (not_lt.2 this)

/-- **Uniformity in the time from the per-sequence form** (`twK_bound_holds` is stated per time sequence, with an eventual set that does not depend on it): if
`P n v` holds eventually for every time sequence `t` with `0 ≤ t n ≤ T n`, it holds eventually uniformly in `v ∈ [0, T n]`.  Proof: a frequent failure
would give a time sequence (the failing `v_n` where there is one) that fails frequently. -/
private theorem TwistKer2_unif {T : ℕ → ℝ} (hT : ∀ n, 0 ≤ T n) {Pr : ℕ → ℝ → Prop}
    (h : ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ T n) → ∀ᶠ n in atTop, Pr n (t n)) :
    ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ T n → Pr n v := by
  by_contra hcon
  rw [not_eventually] at hcon
  classical
  let t : ℕ → ℝ := fun n => if hx : ∃ v : ℝ, 0 ≤ v ∧ v ≤ T n ∧ ¬ Pr n v then hx.choose else 0
  have hspec : ∀ n, (∃ v : ℝ, 0 ≤ v ∧ v ≤ T n ∧ ¬ Pr n v) → (0 ≤ t n ∧ t n ≤ T n ∧ ¬ Pr n (t n)) := fun n hx => by
    simpa [t, hx] using hx.choose_spec
  have ht0 : ∀ n, 0 ≤ t n := fun n => by
    by_cases hx : ∃ v : ℝ, 0 ≤ v ∧ v ≤ T n ∧ ¬ Pr n v
    · exact (hspec n hx).1
    · simp [t, hx]
  have htT : ∀ n, t n ≤ T n := fun n => by
    by_cases hx : ∃ v : ℝ, 0 ≤ v ∧ v ≤ T n ∧ ¬ Pr n v
    · exact (hspec n hx).2.1
    · simpa [t, hx] using hT n
  have hfreq : ∃ᶠ n in atTop, ¬ Pr n (t n) := by
    refine hcon.mono fun n hn => ?_
    push Not at hn
    obtain ⟨v, hv0, hvT, hv⟩ := hn
    exact (hspec n ⟨v, hv0, hvT, hv⟩).2.2
  exact hfreq ((h t ht0 htT).mono fun n hn => not_not.2 hn)

end Calculus

/-! ## 2. Carrier facts and the sum bound -/

section Carrier

variable {d : ℕ} {sz : Sizes d}

/-- `η_v = (1 - v) Im m_F` at the carrier (`FlowFM.eta` of `baFM`, `etaOf`). -/
private theorem TwistKer2_eta_eq (z : ℕ → ℂ) (n : ℕ) (v : ℝ) :
    (baFMz sz z).eta n v = (1 - v) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl

/-- `0 < η_v ≤ 1` for `0 ≤ v ≤ t₀_n` on the flow. -/
private theorem TwistKer2_eta_pos {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ}
    (hv : 0 ≤ v) (hvT : v ≤ BAflowT0 sz z n) : 0 < (baFMz sz z).eta n v ∧ (baFMz sz z).eta n v ≤ 1 := by
  have hm := EMn2BA_mF_data sz hflow n
  have hT := EMn2BA_T0_lt_one hκ sz hflow n
  rw [TwistKer2_eta_eq]
  refine ⟨mul_pos (by linarith) (by linarith [hm.1]), ?_⟩
  nlinarith [hm.2]

/-- A maximiser of a function on a nonempty finite type. -/
private theorem TwistKer2_argmax {ι : Type*} [Finite ι] [Nonempty ι] (g : ι → ℝ) : ∃ i₀, ∀ i, g i ≤ g i₀ := by
  have := Fintype.ofFinite ι
  obtain ⟨i₀, -, h⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
  exact ⟨i₀, fun i => h i (Finset.mem_univ i)⟩

/-- `t₀_n ≥ 0` on the flow. -/
private theorem TwistKer2_T0_nonneg {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) :
    0 ≤ BAflowT0 sz z n := by
  have hzim := EMn2BA_zim_pos sz hflow n
  exact (BAt0_pos hzim (EMn2BA_mim_pos hκ sz hflow n)).le

end Carrier

/-! ## 3. T.11 (i): `B̃₁ ≺ η⁻¹ (W^{-d} B)²` -/

section Src1

/-- **Uniform form of `twK_bound_holds`** (the per-sequence statement, made uniform in `v ∈ [0, t₀_n]` by `TwistKer2_unif`). -/
private theorem TwistKer2_twK_unif {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) :
    ∃ C : ℝ, 0 < C ∧ ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n in atTop, ∀ v : ℝ, 0 ≤ v → v ≤ BAflowT0 sz z n → ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
        (∀ a, ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ C * sz.Bctl n v) ∧
        ∑ a, ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹ := by
  obtain ⟨C, hC, H⟩ := twK_bound_holds d hd κ ε 𝔡 hκ hε h𝔡
  refine ⟨C, hC, fun 𝔠 sz z hflow => ?_⟩
  exact TwistKer2_unif (Pr := fun n v => ∀ (σ : Fin 2 → Bool) (c₁ c₂ : Zd d (sz.L n)),
      (∀ a, ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ C * sz.Bctl n v) ∧
      ∑ a, ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ C * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹)
    (fun n => TwistKer2_T0_nonneg hκ hflow n) (fun t ht0 htT => H 𝔠 sz z hflow t ht0 htT)

/-- **T.11 (i)** (`TP:144`): `|B̃₁(v)(a)| ≤ W^d max_b |(L-K)^{(2)}_{(a,b)}| Σ_b |K̃_v(b)| ≤ C η⁻¹ max_b |(L-K)^{(2)}_{(a,b)}| ≺ η⁻¹ (W^{-d}B)²`
(`twSteps`, third conjunct at `k = 2`; `Σ_b |K̃| ≤ C (W^d η)⁻¹` by `twK_bound_holds` (T.1 (ii)), uniform in `v`).  No regime is used. -/
theorem baTwistSrc1_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc1 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨CK, hCK, HK⟩ := TwistKer2_twK_unif hd hκ hε h𝔡
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps
  have hsize := tendsto_size sz hflow.1.2.2.1
  have h3 := hsteps.2.2.1 2 (by norm_num)
  have hNe : ∀ n, Nonempty (Zd d (sz.L n)) := fun n => ⟨0⟩
  unfold twSrc
  refine TwistKer2_comp hsize h3
    (fun n u ω => ⟨u.1, u.2.1, ![u.2.2.1, Classical.choose (TwistKer2_argmax (fun b : Zd d (sz.L n) =>
      ‖(baFMz sz z).L n (u.1 : ℝ) u.2.1 ![u.2.2.1, b] ω - (baFMz sz z).K n (u.1 : ℝ) u.2.1 ![u.2.2.1, b]‖))]⟩)
    (fun n u ω => ((baFMz sz z).eta n (u.1 : ℝ))⁻¹) (c := CK) (fun _ _ _ => norm_nonneg _) ?_ ?_ ?_
  · intro n u ω
    have hv := u.1.2
    have := TwistKer2_eta_pos hκ hflow n (hs n |>.trans hv.1) (hv.2.trans (htT n))
    exact inv_nonneg.2 this.1.le
  · filter_upwards [HK 𝔠 sz z hflow] with n hn
    intro u ω
    obtain ⟨⟨v, hv⟩, σ, a, c₁, c₂⟩ := u
    dsimp only
    have hv0 : 0 ≤ v := (hs n).trans hv.1
    have hvT : v ≤ BAflowT0 sz z n := hv.2.trans (htT n)
    obtain ⟨-, hKs⟩ := hn v hv0 hvT σ c₁ c₂
    obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      positivity
    have hmax := Classical.choose_spec (TwistKer2_argmax (fun b : Zd d (sz.L n) =>
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖))
    set b₀ := Classical.choose (TwistKer2_argmax (fun b : Zd d (sz.L n) =>
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖)) with hb₀
    have hB1 : ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d *
        ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ := by
      unfold twB1
      rw [norm_mul, norm_pow, Complex.norm_natCast]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_mul _ _).le)) (by positivity)
    calc ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ *
            ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ := hB1
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖) *
            ‖(baFMz sz z).L n v σ ![a, b₀] ω - (baFMz sz z).K n v σ ![a, b₀]‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hWd.le
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hmax b) (norm_nonneg _)
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹) *
            ‖(baFMz sz z).L n v σ ![a, b₀] ω - (baFMz sz z).K n v σ ![a, b₀]‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKs (norm_nonneg _)) hWd.le
      _ = CK * (((baFMz sz z).eta n v)⁻¹ *
            ‖(baFMz sz z).L n v σ ![a, b₀] ω - (baFMz sz z).K n v σ ![a, b₀]‖) := by
          field_simp
  · exact Eventually.of_forall fun n u ω => by
      simp only [one_mul]
      rw [Real.rpow_two]

end Src1

/-! ## 4. The 2-loop sum of `(4.16)` at the carrier: stem copies of `SEforLn2_{Bctl_ge_inv, WD, conU, sumTwo_pt, sum2}` (`Induction/SEforLn2.lean:280-530`) -/

section SumTwo

open RBM.Loop

variable {d : ℕ} (sz : Sizes d)

/-- `N⁻¹ ≤ W^{-d} B_{u,0}` for `0 ≤ u < 1` (a copy of the private `SEforLn2_Bctl_ge_inv`). -/
private theorem TwistKer2_Bctl_ge_inv (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (((sz.size n : ℕ) : ℝ))⁻¹ ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hx : 0 < 1 - u := by linarith
  rw [abs_of_pos hx]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  rw [hsize, mul_inv]
  have hg : 0 ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
    inv_anti₀ (by positivity) (mul_le_of_le_one_right (by positivity) (by linarith))
  have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  have hW0 : 0 ≤ ((((sz.W n : ℕ) : ℝ) ^ d))⁻¹ := by positivity
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d)⁻¹
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ :=
        mul_le_mul_of_nonneg_left h1 hW0
    _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
          (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ hW0
        linarith

/-- The absorption of the `W^{-D}` term: `N W^{-2/𝔠} ≤ N⁻¹` from `W ≥ N^𝔠` (a copy of the private `SEforLn2_WD`). -/
private theorem TwistKer2_WD (n : ℕ) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) :
    ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-(2 / 𝔠)) ≤ (((sz.size n : ℕ) : ℝ))⁻¹ := by
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have h1 : (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (2 / 𝔠) = ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠) := by
    rw [← h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hb (by positivity)
  have h3 : ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]; norm_num
  rw [h3] at h2
  rw [Real.rpow_neg hW.le]
  have h4 : (((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠))⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) h2
  calc ((sz.size n : ℕ) : ℝ) * (((sz.W n : ℕ) : ℝ) ^ (2 / 𝔠))⁻¹
      ≤ ((sz.size n : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h4 hN0.le
    _ = (((sz.size n : ℕ) : ℝ))⁻¹ := by field_simp

/-- `(con_st_ind)` at an intermediate time `u ∈ [s, t]` (a copy of the private `SEforLn2_conU`). -/
private theorem TwistKer2_conU (n : ℕ) {𝔠d s' t' u : ℝ} (h𝔠 : 0 < 𝔠d)
    (hcon : (sz.Bctl n t') ^ 𝔠d ≤ (1 - t') / (1 - s') ∧ (1 - t') / (1 - s') < 1) (hut : u ≤ t')
    (ht1 : t' < 1) :
    0 < 1 - s' ∧ sz.Bctl n u ≤ 1 ∧ (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s') := by
  obtain ⟨hB, hρ⟩ := hcon
  have hBpos : 0 < sz.Bctl n t' := st_Bctl_pos sz ht1
  have hu : 0 < 1 - t' := by linarith
  have hr0 : 0 < (1 - t') / (1 - s') := lt_of_lt_of_le (Real.rpow_pos_of_pos hBpos _) hB
  have hs : 0 < 1 - s' := by
    by_contra h
    push Not at h
    have := div_nonpos_of_nonneg_of_nonpos hu.le h
    linarith
  have hB1 : sz.Bctl n t' < 1 := by
    by_contra h
    push Not at h
    have : 1 ≤ (sz.Bctl n t') ^ 𝔠d := Real.one_le_rpow h h𝔠.le
    linarith
  have hmono : sz.Bctl n u ≤ sz.Bctl n t' := STBctl_mono sz n hut ht1
  refine ⟨hs, hmono.trans hB1.le, ?_⟩
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz (hut.trans_lt ht1)
  calc (sz.Bctl n u) ^ 𝔠d ≤ (sz.Bctl n t') ^ 𝔠d := Real.rpow_le_rpow hBu.le hmono h𝔠.le
    _ ≤ (1 - t') / (1 - s') := hB
    _ ≤ (1 - u) / (1 - s') := div_le_div_of_nonneg_right (by linarith) hs.le

/-- **`(eq:sumtwoloop)`, pointwise** (the proof of `SEforLn2_sumTwo_pt` without the last step `(1-u)⁻¹ ≤ η_u⁻¹`):
`((1-s)/(1-u))^{C_d} B^{1/5} Σ_{a₂} 𝒯_u(|a₁-a₂|) ≤ C_∞(d) B^{1/6} (1-u)⁻¹`. -/
private theorem TwistKer2_sumTwo_pt (hd : 2 ≤ d) (n : ℕ) {𝔠d Cd s' u : ℝ} (h𝔠 : 0 < 𝔠d) (hCd : 0 ≤ Cd)
    (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1)
    (hl : 0 ≤ sz.lam n) (a₁ : Zd d (sz.L n)) :
    ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤
      KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹ := by
  have hBpos : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hu : 0 < 1 - u := by linarith
  have hρle : (1 - s') / (1 - u) ≤ (sz.Bctl n u) ^ (-𝔠d) := by
    rw [Real.rpow_neg hBpos.le, ← inv_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hBpos _) hB
  have hρ0 : 0 ≤ (1 - s') / (1 - u) := by positivity
  have h3 : ((1 - s') / (1 - u)) ^ Cd ≤ (sz.Bctl n u) ^ (-(𝔠d * Cd)) := by
    calc ((1 - s') / (1 - u)) ^ Cd ≤ ((sz.Bctl n u) ^ (-𝔠d)) ^ Cd :=
          Real.rpow_le_rpow hρ0 hρle hCd
      _ = (sz.Bctl n u) ^ (-(𝔠d * Cd)) := by
          rw [← Real.rpow_mul hBpos.le]; congr 1; ring
  have h4 : ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) ≤
      (sz.Bctl n u) ^ (1 / 6 : ℝ) := by
    calc ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ)
        ≤ (sz.Bctl n u) ^ (-(𝔠d * Cd)) * (sz.Bctl n u) ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hBpos.le _)
      _ = (sz.Bctl n u) ^ (-(𝔠d * Cd) + 1 / 5) := (Real.rpow_add hBpos _ _).symm
      _ ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by linarith)
  have h5 : ∑ a₂ : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) =
      ∑ a : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) a : ℝ) :=
    Equiv.sum_comp (Equiv.subLeft a₁)
      (fun a : Zd d (sz.L n) => tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) a : ℝ))
  have h6 := KDecay_sum_tailT_le (L := sz.L n) hd hl hu1
  have h7 : 0 ≤ ∑ a₂ : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) :=
    Finset.sum_nonneg fun a _ => tailT_nonneg (Nat.cast_nonneg _)
  calc ((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        ∑ a₂ : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (a₁ - a₂) : ℝ)
      ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (KDecay_tailC d / (1 - u)) :=
        mul_le_mul h4 (h5 ▸ h6) h7 (Real.rpow_nonneg hBpos.le _)
    _ = KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹ := by ring

/-- **`(eq:sumtwoloop)`, deterministic part** (the proof of `SEforLn2_sum2`, for an abstract nonnegative `f` in place of `‖𝓛 - 𝒦‖` and `(1-u)` in place of `η_u`):
if `f_{σ',(a₁,a₂)} ≤ δ (ρ^{C_d} B^{1/5} 𝒲_u(|a₁-a₂|) e^{-(|a₁-a₂|/ℓ)^{1/2}} + W^{-D_w})` with `N W^{-D_w} ≤ B`, then
`Σ_{a₂} f_{σ',(c,a₂)} ≤ δ (C_∞(d) + 1) B^{1/6} (W^d (1-u))⁻¹`. -/
private theorem TwistKer2_sum2 (hd : 2 ≤ d) (n : ℕ) {𝔠d Cd s' u δ Dw : ℝ} (h𝔠 : 0 < 𝔠d) (hCd : 0 ≤ Cd)
    (hcc : 𝔠d * Cd ≤ 1 / 30) (hs : 0 < 1 - s') (h0 : 0 ≤ u) (hu1 : u < 1)
    (hB : (sz.Bctl n u) ^ 𝔠d ≤ (1 - u) / (1 - s')) (hB1 : sz.Bctl n u ≤ 1)
    (hl : 0 ≤ sz.lam n) (hδ : 0 ≤ δ) (hWD : ((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) ≤ sz.Bctl n u)
    (f : (Fin 2 → Bool) → (Fin 2 → Zd d (sz.L n)) → ℝ)
    (hno : ∀ (σ' : Fin 2 → Bool) (a2 : Fin 2 → Zd d (sz.L n)), f σ' a2 ≤
        δ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) * STWB sz n u (zdistInf d (sz.L n) (a2 0 - a2 1)) *
          Real.exp (-(((zdistInf d (sz.L n) (a2 0 - a2 1) : ℕ) : ℝ) / ellT (sz.L n) (sz.lam n) u) ^ (1 / 2 : ℝ)) +
            ((sz.W n : ℕ) : ℝ) ^ (-Dw)))
    (σ' : Fin 2 → Bool) (c : Zd d (sz.L n)) :
    ∑ x : Zd d (sz.L n), f σ' ![c, x] ≤
      δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * (1 - u))⁻¹ := by
  have hBpos : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hu : 0 < 1 - u := by linarith
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hη1 : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ hu).2 (by linarith)
  have hpt : ∀ x : Zd d (sz.L n), f σ' ![c, x] ≤
      δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
        tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) + ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
    intro x
    refine (hno σ' ![c, x]).trans (le_of_eq ?_)
    have e0 : (![c, x] : Fin 2 → Zd d (sz.L n)) 0 = c := rfl
    have e1 : (![c, x] : Fin 2 → Zd d (sz.L n)) 1 = x := rfl
    rw [e0, e1]
    congr 1
    unfold STWB tailT
    rw [BparamR_natCast, Real.sqrt_eq_rpow]
    ring
  calc ∑ x : Zd d (sz.L n), f σ' ![c, x]
      ≤ ∑ x : Zd d (sz.L n), δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd *
          (sz.Bctl n u) ^ (1 / 5 : ℝ) * tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := Finset.sum_le_sum fun x _ => hpt x
    _ = δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((1 - s') / (1 - u)) ^ Cd * (sz.Bctl n u) ^ (1 / 5 : ℝ) *
          ∑ x : Zd d (sz.L n), tailT d (sz.L n) (sz.lam n) u (zdistInf d (sz.L n) (c - x) : ℝ)) +
          (((sz.L n : ℕ) : ℝ) ^ d) * ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ δ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (KDecay_tailC d * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹) +
          (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hδ
        · exact mul_le_mul_of_nonneg_left
            (TwistKer2_sumTwo_pt sz hd n h𝔠 hCd hcc hs hu1 hB hB1 hl c) (by positivity)
        · have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
            simp [Sizes.size, mul_pow]
          have h1 : (((sz.L n : ℕ) : ℝ) ^ d) * ((sz.W n : ℕ) : ℝ) ^ (-Dw) =
              (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (((sz.size n : ℕ) : ℝ) * ((sz.W n : ℕ) : ℝ) ^ (-Dw)) := by
            rw [hsize]; field_simp
          have h2 : sz.Bctl n u ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) := by
            have := Real.rpow_le_rpow_of_exponent_ge hBpos hB1 (by norm_num : (1 / 6 : ℝ) ≤ 1)
            simpa using this
          have h3 : (sz.Bctl n u) ^ (1 / 6 : ℝ) ≤ (sz.Bctl n u) ^ (1 / 6 : ℝ) * (1 - u)⁻¹ :=
            le_mul_of_one_le_right (Real.rpow_nonneg hBpos.le _) hη1
          rw [h1, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hWD.trans (h2.trans h3)) (by positivity)
    _ = δ * (KDecay_tailC d + 1) * (sz.Bctl n u) ^ (1 / 6 : ℝ) * ((((sz.W n : ℕ) : ℝ) ^ d) * (1 - u))⁻¹ := by
        rw [mul_inv]; ring

end SumTwo

/-! ## 5. T.11 (iv): `B̃₂ ≺ Ξ̃ η⁻¹ (W^{-d}B)^{γ+1/6}` -/

section Src4

open RBM.Loop

/-- **T.11 (iv)** (`TP:146`): `|B̃₂(v)(a)| ≤ ‖Z_v‖_∞ W^d Σ_b |(L-K)^{(2)}_{(a,b)}|`, `‖Z_v‖_∞ ≤ Ξ̃ (W^{-d}B)^γ` and `(4.16)`: `W^d Σ_b |(L-K)^{(2)}_{(a,b)}| ≺ η⁻¹ (W^{-d}B)^{1/6}`
(`STGdecayWgL`, the third conjunct of `twSteps.1`, `TwistKer2_sum2`, `(con_st_ind)` with `𝔠_d = min (1/100) (1/(30 C_d))`, so `𝔠_d C_d ≤ 1/30`).
The exponents close: `1/5 - 𝔠_d C_d ≥ 1/6`.  No regime is used. -/
theorem baTwistSrc4_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc4 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  have h𝔠d : 0 < min (1 / 100) (1 / (30 * Cd)) := lt_min (by norm_num) (by positivity)
  have hcc : min (1 / 100) (1 / (30 * Cd)) * Cd ≤ 1 / 30 :=
    calc min (1 / 100) (1 / (30 * Cd)) * Cd ≤ 1 / (30 * Cd) * Cd :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hCd.le
      _ = 1 / 30 := by field_simp
  refine ⟨min (1 / 100) (1 / (30 * Cd)), h𝔠d, min_le_left _ _, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps γ hγ1 hγ2 Ξ hΞ hZ
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hlam : ∀ᶠ n in atTop, 0 ≤ sz.lam n := by
    filter_upwards [hflow.1.2.2.2.2] with n hn
    exact (Real.rpow_nonneg (Nat.cast_nonneg _) _).trans hn.1
  have hG' := hsteps.1.2.2 (2 / 𝔠) (by positivity)
  unfold twSrc
  refine TwistKer2_of_subset hG' (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow (KDecay_tailC d + 1) (half_pos hτ)), hcon, hlam, hband]
    with n hCN hcon_n hlam_n hband_n
  rintro ω ⟨⟨⟨v, hv⟩, σ, a, c₁, c₂⟩, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  have hv0 : 0 ≤ v := (hs n).trans hv.1
  have hvT : v ≤ BAflowT0 sz z n := hv.2.trans (htT n)
  have hu1 : v < 1 := hvT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have ht1 : t n < 1 := (htT n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hBpos : 0 < sz.Bctl n v := st_Bctl_pos sz hu1
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  obtain ⟨hs', hB1, hBc⟩ := TwistKer2_conU sz n h𝔠d hcon_n hv.2 ht1
  have hWD := (TwistKer2_WD sz n h𝔠 hband_n).trans (TwistKer2_Bctl_ge_inv sz n hv0 hu1)
  have hδ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hWdpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hS := TwistKer2_sum2 sz (by omega) n h𝔠d hCd.le hcc hs' hv0 hu1 hBc hB1 hlam_n hδ0 hWD
    (fun σ' a2 => ‖(baFMz sz z).L n v σ' a2 ω - (baFMz sz z).K n v σ' a2‖)
    (fun σ' a2 => hno ⟨⟨v, hv⟩, σ', a2⟩) σ a
  have hΞ1 := hΞ n ω
  have hZb := fun b => hZ n ω v σ b c₁ c₂ hv.1 hv.2
  have hBγ : 0 ≤ sz.Bctl n v ^ γ := Real.rpow_nonneg hBpos.le _
  -- `‖B̃₂‖ ≤ Ξ̃ B^γ · W^d Σ_b ‖(L-K)_{(a,b)}‖`
  have hB2 : ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ Ξ n ω * sz.Bctl n v ^ γ *
      (((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖) := by
    unfold twB2
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    calc ((sz.W n : ℕ) : ℝ) ^ d * ‖∑ b, (twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂) *
            ((baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b])‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b, Ξ n ω * sz.Bctl n v ^ γ *
            ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ := by
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)) hWdpos.le
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hZb b) (norm_nonneg _)
      _ = _ := by rw [← Finset.mul_sum]; ring
  have hΞB : 0 ≤ Ξ n ω * sz.Bctl n v ^ γ := mul_nonneg (by linarith) hBγ
  -- the bound `W^d Σ ≤ N^{τ/2} (C_∞ + 1) B^{1/6} (1-v)⁻¹`, `(1-v)⁻¹ ≤ η⁻¹`
  have hη' : (1 - v)⁻¹ ≤ ((baFMz sz z).eta n v)⁻¹ := by
    have hm := EMn2BA_mF_data sz hflow n
    refine inv_anti₀ hη ?_
    rw [TwistKer2_eta_eq]
    have : 0 < 1 - v := by linarith
    nlinarith [hm.2]
  have hS' : ((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
      ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (KDecay_tailC d + 1) * sz.Bctl n v ^ (1 / 6 : ℝ) * ((baFMz sz z).eta n v)⁻¹ := by
    have h1 : ∑ b, ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ =
        ∑ x : Zd d (sz.L n), (fun (σ' : Fin 2 → Bool) (a2 : Fin 2 → Zd d (sz.L n)) =>
          ‖(baFMz sz z).L n v σ' a2 ω - (baFMz sz z).K n v σ' a2‖) σ ![a, x] := rfl
    rw [h1]
    refine (mul_le_mul_of_nonneg_left hS hWdpos.le).trans ?_
    have hB6 := Real.rpow_nonneg hBpos.le (1 / 6 : ℝ)
    calc ((sz.W n : ℕ) : ℝ) ^ d * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (KDecay_tailC d + 1) * sz.Bctl n v ^ (1 / 6 : ℝ) *
          ((((sz.W n : ℕ) : ℝ) ^ d) * (1 - v))⁻¹)
        = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (KDecay_tailC d + 1) * sz.Bctl n v ^ (1 / 6 : ℝ) * (1 - v)⁻¹ := by
          field_simp
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left hη' ?_
          have := KDecay_one_le_tailC (d := d) (by omega)
          positivity
  have hfin : ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (Ξ n ω * (((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ (γ + 1 / 6))) := by
    refine hB2.trans ?_
    calc Ξ n ω * sz.Bctl n v ^ γ * (((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖)
        ≤ Ξ n ω * sz.Bctl n v ^ γ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * (KDecay_tailC d + 1) * sz.Bctl n v ^ (1 / 6 : ℝ) *
            ((baFMz sz z).eta n v)⁻¹) := mul_le_mul_of_nonneg_left hS' hΞB
      _ ≤ Ξ n ω * sz.Bctl n v ^ γ * (((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) *
            sz.Bctl n v ^ (1 / 6 : ℝ) * ((baFMz sz z).eta n v)⁻¹) := by
          refine mul_le_mul_of_nonneg_left ?_ hΞB
          have hB6 := Real.rpow_nonneg hBpos.le (1 / 6 : ℝ)
          have hηinv : 0 ≤ ((baFMz sz z).eta n v)⁻¹ := inv_nonneg.2 hη.le
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hB6) hηinv
          exact mul_le_mul_of_nonneg_left hCN hδ0
      _ = ((sz.size n : ℕ) : ℝ) ^ τ * (Ξ n ω * (((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ (γ + 1 / 6))) := by
          rw [UnifDetDom.rpow_half_mul_rpow_half (sz.size n) hτ, Real.rpow_add hBpos]; ring
  exact absurd hp (not_lt.2 hfin)

end Src4

/-! ## 6. T.11 (ii): `Ẽ^{G̊} ≺ η⁻¹ (W^{-d}B)²` -/

section Src2

/-- `3 N^{-(D+1)} ≤ N^{-D}` for `N ≥ 3`. -/
private theorem TwistKer2_three_mul_rpow_le (D : ℝ) :
    ∀ᶠ N : ℕ in atTop, 3 * (N : ℝ) ^ (-(D + 1)) ≤ (N : ℝ) ^ (-D) := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  rw [neg_add, Real.rpow_add hN0, Real.rpow_neg_one]
  have h := Real.rpow_nonneg hN0.le (-D)
  calc 3 * ((N : ℝ) ^ (-D) * (N : ℝ)⁻¹) = (N : ℝ) ^ (-D) * (3 / N) := by ring
    _ ≤ (N : ℝ) ^ (-D) * 1 := by
        gcongr; rw [div_le_one hN0]; exact hN3
    _ = _ := mul_one _

section Calculus3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- `StochDomAt.of_subset_union` with three failure events (a copy of its proof with `3 N^{-(D+1)} ≤ N^{-D}`). -/
private theorem TwistKer2_union3 (hsize : Tendsto size atTop atTop) {U₁ U₂ U₃ : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {f₁ g₁ : ∀ l, U₁ l → Ω → ℝ} {f₂ g₂ : ∀ l, U₂ l → Ω → ℝ} {f₃ g₃ : ∀ l, U₃ l → Ω → ℝ}
    (h₁ : StochDomAt P size f₁ g₁) (h₂ : StochDomAt P size f₂ g₂) (h₃ : StochDomAt P size f₃ g₃)
    (hsub : ∀ τ > (0 : ℝ), ∃ τ' > (0 : ℝ), ∀ᶠ l : ℕ in atTop,
      badSetAt size ξ ζ τ l ⊆ badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l ∪ badSetAt size f₃ g₃ τ' l) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := hsub τ hτ
  filter_upwards [hs, h₁ τ' hτ' (D + 1) (by linarith), h₂ τ' hτ' (D + 1) (by linarith), h₃ τ' hτ' (D + 1) (by linarith),
    hsize.eventually (TwistKer2_three_mul_rpow_le D)] with l h0 h1 h2 h3 h4
  have hp : (0 : ℝ) ≤ (size l : ℝ) ^ (-(D + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc P (badSetAt size ξ ζ τ l) ≤ P (badSetAt size f₁ g₁ τ' l ∪ badSetAt size f₂ g₂ τ' l ∪ badSetAt size f₃ g₃ τ' l) :=
        measure_mono h0
    _ ≤ P (badSetAt size f₁ g₁ τ' l) + P (badSetAt size f₂ g₂ τ' l) + P (badSetAt size f₃ g₃ τ' l) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) + ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) +
          ENNReal.ofReal ((size l : ℝ) ^ (-(D + 1))) := add_le_add (add_le_add h1 h2) h3
    _ = ENNReal.ofReal (3 * (size l : ℝ) ^ (-(D + 1))) := by
        rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (add_nonneg hp hp) hp]; ring_nf
    _ ≤ ENNReal.ofReal ((size l : ℝ) ^ (-D)) := ENNReal.ofReal_le_ofReal h4

end Calculus3

/-- The Hermitian matrix of the carrier (a copy of the private `GreenLocal_hermitian`, `BA/GreenLocal.lean:178`). -/
private theorem TwistKer2_hermitian {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA (BAflowLam0 sz z) n t ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine Matrix.IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n t ω)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (BAflowLam0 sz z n : ℂ) = (BAflowLam0 sz z n : ℂ) from Complex.conj_ofReal _]

/-- `𝒦^{(1)}_{σ,a} = m(σ)` at the carrier (`baKsol_one`). -/
private theorem TwistKer2_K1 {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) {sz : Sizes d} {z : ℕ → ℂ} (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ)
    (hg : 0 < BAflowLam0 sz z n) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (τ : Bool) (a : Zd d (sz.L n)) :
    (baFMz sz z).K n v ![τ] ![a] = if τ then (baFMz sz z).m n else (starRingEnd ℂ) ((baFMz sz z).m n) :=
  baKsol_one d hκ hg (sz.three_le_L n) (sz.W n) (BAflow_real κ ε 𝔠 𝔡 sz z hflow n) ⟨hv0, hv1⟩ ![τ] ![a]

/-- The carrier at `(n, v, ω)` as a resolvent of a Hermitian matrix: `G = Gres H ζ true`, `𝓛 = loopFine H ζ`, `Im ζ = η_v`. -/
private theorem TwistKer2_carrier {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (v : ℝ) (ω : sz.SeqΩ) :
    (baFMz sz z).G n v ω = Gres (sz.seqHflowBA (BAflowLam0 sz z) n v ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v) true ∧
    (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), (baFMz sz z).L n v σ a ω =
      loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n v ω) (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v) σ a) ∧
    (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v).im = (baFMz sz z).eta n v :=
  ⟨rfl, fun _ _ _ => rfl, ztOf_im _ _ _⟩

/-- **T.11 (ii)** (`TP:145`): `|Ẽ^{G̊}_v(a)| ≤ 2 m η⁻¹ (M₁ M₃)^{1/2}` (`TwistKer_twEG_le`: fold of `L̃^{(3)}` at the twist, Ward at `a'`), `m ≺ W^{-d}B` (`STAvgUgL` and `𝒦^{(1)} = m(σ)`),
`M₁ ≺ 1`, `M₃ ≺ (W^{-d}B)²` (`twSteps`, second conjunct at `k = 1, 3`).  No regime is used. -/
theorem baTwistSrc2_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc2 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps
  have hsize := tendsto_size sz hflow.1.2.2.1
  have hA := hsteps.1.2.1
  have h1 := hsteps.2.1 1 le_rfl
  have h3 := hsteps.2.1 3 (by norm_num)
  unfold twSrc
  refine TwistKer2_union3 hsize hA h1 h3 (fun τ hτ => ⟨τ / 4, by positivity, ?_⟩)
  filter_upwards [hsize.eventually (eventually_le_rpow 2 (τ := τ / 2) (by positivity)), BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow]
    with n h2N hlam
  rintro ω ⟨⟨⟨v, hv⟩, σ, a, c₁, c₂⟩, hp⟩
  by_contra hno
  simp only [Set.mem_union, badSetAt, Set.mem_ofPred_eq, not_or, not_exists, not_lt] at hno
  obtain ⟨⟨hnoA, hno1⟩, hno3⟩ := hno
  have hv0 : 0 ≤ v := (hs n).trans hv.1
  have hvT : v ≤ BAflowT0 sz z n := hv.2.trans (htT n)
  have hu1 : v < 1 := hvT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hBpos : 0 < sz.Bctl n v := st_Bctl_pos sz hu1
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  obtain ⟨hGc, hLc, hzc⟩ := TwistKer2_carrier sz z n v ω
  have hH := TwistKer2_hermitian sz z n v ω
  have hz : 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v).im := by rw [hzc]; exact hη
  set δ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 4) with hδ
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hδδ : δ * δ = ((sz.size n : ℕ) : ℝ) ^ (τ / 2) := by
    rw [hδ, ← Real.rpow_add (by exact_mod_cast sz.one_le_size n)]; congr 1; ring
  have hδ2 : 2 ≤ δ * δ := by rw [hδδ]; exact h2N
  have htr : ∀ (τ' : Bool) (a' : Zd d (sz.L n)), ‖(baFMz sz z).L n v ![τ'] ![a'] ω -
      (if τ' then (baFMz sz z).m n else (starRingEnd ℂ) ((baFMz sz z).m n))‖ ≤ δ * sz.Bctl n v := by
    intro τ' a'
    have := hnoA ⟨⟨v, hv⟩, ![τ'], ![a']⟩
    rw [TwistKer2_K1 hκ hflow n hlam.1 hv0 hu1] at this
    simpa using this
  have hM₁ : ∀ (τ' : Bool) (c : Zd d (sz.L n)), ‖(baFMz sz z).L n v ![τ'] ![c] ω‖ ≤ δ := by
    intro τ' c
    simpa using hno1 ⟨⟨v, hv⟩, ![τ'], ![c]⟩
  have hM₃ : ∀ (τ' : Fin 3 → Bool) (b : Fin 3 → Zd d (sz.L n)), ‖(baFMz sz z).L n v τ' b ω‖ ≤ δ * sz.Bctl n v ^ 2 := by
    intro τ' b
    simpa using hno3 ⟨⟨v, hv⟩, τ', b⟩
  have hEG := TwistKer_twEG_le n (baFMz sz z) hH hz v ω hGc hLc σ a c₁ c₂ htr hM₁ hM₃
  rw [hzc] at hEG
  have hB : Real.sqrt (δ * (δ * sz.Bctl n v ^ 2)) = δ * sz.Bctl n v := by
    rw [show δ * (δ * sz.Bctl n v ^ 2) = (δ * sz.Bctl n v) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hδ0 hBpos.le)]
  rw [hB] at hEG
  have hfin : ‖twEG (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
      (1 * (((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ (2 : ℝ))) := by
    refine hEG.trans ?_
    have hτ4 : ((sz.size n : ℕ) : ℝ) ^ τ = (δ * δ) * (δ * δ) := by
      rw [hδδ, ← Real.rpow_add (by exact_mod_cast sz.one_le_size n)]; congr 1; ring
    rw [hτ4, Real.rpow_two]
    have hη' : 0 ≤ ((baFMz sz z).eta n v)⁻¹ := inv_nonneg.2 hη.le
    calc 2 * (δ * sz.Bctl n v) * (((baFMz sz z).eta n v)⁻¹ * (δ * sz.Bctl n v)) = 2 * (δ * δ) * (((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ 2) := by ring
      _ ≤ (δ * δ) * (δ * δ) * (1 * (((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ 2)) := by
          rw [one_mul]
          have hX : 0 ≤ ((baFMz sz z).eta n v)⁻¹ * sz.Bctl n v ^ 2 := by positivity
          have hδδ0 : 0 ≤ δ * δ := mul_nonneg hδ0 hδ0
          have h22 : 2 * (δ * δ) ≤ (δ * δ) * (δ * δ) := by nlinarith
          exact mul_le_mul_of_nonneg_right h22 hX
  exact absurd hp (not_lt.2 hfin)

end Src2

/-! ## 7. T.11 (v): the decay of the sources beyond `3 W^ε ℓ_v` -/

section Src5

/-- **The absorptions of T.11 (v)**: with `W ≥ N^𝔠`, `D_pp = 2D + 16/𝔠` and `ρ = N^{τ/2} W^{-D_pp}`: `N⁸ ρ^{1/2}`, `N⁸ ρ`, `N⁸ W^{-(D+8/𝔠)}` are all `≤ N^{τ/2} W^{-D}`. -/
private theorem TwistKer2_arith {Nn Wn 𝔠 τ D : ℝ} (hN : 1 ≤ Nn) (hW : 1 ≤ Wn) (h𝔠 : 0 < 𝔠) (hb : Nn ^ 𝔠 ≤ Wn) (hτ : 0 < τ) (hD : 0 ≤ D) :
    Nn ^ 8 * Real.sqrt (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠))) ≤ Nn ^ (τ / 2) * Wn ^ (-D) ∧
    Nn ^ 8 * (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠))) ≤ Nn ^ (τ / 2) * Wn ^ (-D) ∧
    Nn ^ 8 * Wn ^ (-(D + 8 / 𝔠)) ≤ Nn ^ (τ / 2) * Wn ^ (-D) := by
  have hN0 : 0 < Nn := by linarith
  have hW0 : 0 < Wn := by linarith
  have hN8 : Nn ^ 8 ≤ Wn ^ (8 / 𝔠) := by
    have h1 : Nn ^ 8 = (Nn ^ 𝔠) ^ (8 / 𝔠) := by
      rw [← Real.rpow_mul hN0.le]
      rw [show 𝔠 * (8 / 𝔠) = (8 : ℝ) by field_simp]
      norm_cast
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hb (by positivity)
  have hNt : 1 ≤ Nn ^ (τ / 2) := Real.one_le_rpow hN (by positivity)
  have hNt4 : Nn ^ (τ / 4) ≤ Nn ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hWD : Wn ^ (8 / 𝔠) * Wn ^ (-(D + 8 / 𝔠)) = Wn ^ (-D) := by
    rw [← Real.rpow_add hW0]; congr 1; ring
  refine ⟨?_, ?_, ?_⟩
  · have hs : Real.sqrt (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠))) = Nn ^ (τ / 4) * Wn ^ (-(D + 8 / 𝔠)) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hW0.le _), ← Real.rpow_mul hN0.le,
        ← Real.rpow_mul hW0.le]
      congr 2 <;> ring
    rw [hs]
    calc Nn ^ 8 * (Nn ^ (τ / 4) * Wn ^ (-(D + 8 / 𝔠))) = Nn ^ (τ / 4) * (Nn ^ 8 * Wn ^ (-(D + 8 / 𝔠))) := by ring
      _ ≤ Nn ^ (τ / 4) * (Wn ^ (8 / 𝔠) * Wn ^ (-(D + 8 / 𝔠))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN8 (Real.rpow_nonneg hW0.le _)) (Real.rpow_nonneg hN0.le _)
      _ = Nn ^ (τ / 4) * Wn ^ (-D) := by rw [hWD]
      _ ≤ Nn ^ (τ / 2) * Wn ^ (-D) := mul_le_mul_of_nonneg_right hNt4 (Real.rpow_nonneg hW0.le _)
  · calc Nn ^ 8 * (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠))) = Nn ^ (τ / 2) * (Nn ^ 8 * Wn ^ (-(2 * D + 16 / 𝔠))) := by ring
      _ ≤ Nn ^ (τ / 2) * (Wn ^ (8 / 𝔠) * Wn ^ (-(2 * D + 16 / 𝔠))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN8 (Real.rpow_nonneg hW0.le _)) (Real.rpow_nonneg hN0.le _)
      _ = Nn ^ (τ / 2) * Wn ^ (8 / 𝔠 + -(2 * D + 16 / 𝔠)) := by rw [← Real.rpow_add hW0]
      _ ≤ Nn ^ (τ / 2) * Wn ^ (-D) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hW ?_) (Real.rpow_nonneg hN0.le _)
          have : 0 < 8 / 𝔠 := by positivity
          have h16 : 16 / 𝔠 = 2 * (8 / 𝔠) := by ring
          linarith
  · calc Nn ^ 8 * Wn ^ (-(D + 8 / 𝔠)) ≤ Wn ^ (8 / 𝔠) * Wn ^ (-(D + 8 / 𝔠)) :=
          mul_le_mul_of_nonneg_right hN8 (Real.rpow_nonneg hW0.le _)
      _ = Wn ^ (-D) := hWD
      _ = 1 * Wn ^ (-D) := (one_mul _).symm
      _ ≤ Nn ^ (τ / 2) * Wn ^ (-D) := mul_le_mul_of_nonneg_right hNt (Real.rpow_nonneg hW0.le _)

section Facts5

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

private theorem TwistKer2_norm_winv (n : ℕ) : ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹‖ = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by simp

/-- `η_v⁻¹ ≤ (2/κ) N` for `0 ≤ v ≤ t₀_n` (`1 - v ≥ 1 - t₀ ≥ Im z/2 ≥ N^{-1}/2`, `Im m_F ≥ κ`; the shape of `TwistKer_amp`). -/
private theorem TwistKer2_eta_inv_le (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ} (hv0 : 0 ≤ v)
    (hvT : v ≤ BAflowT0 sz z n) : ((baFMz sz z).eta n v)⁻¹ ≤ (2 / κ) * ((sz.size n : ℕ) : ℝ) := by
  have hNpos : 0 < sz.size n := by
    unfold Sizes.size
    exact pow_pos (Nat.mul_pos (sz.W_pos n) (by have := sz.three_le_L n; omega)) d
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hNpos
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hNim' : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hT := EMn2BA_one_sub_T0 hκ sz hflow n
  have hm := EMn2BA_mF_data sz hflow n
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have h1v : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2 ≤ 1 - v := by linarith
  have hη : κ * (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2) ≤ (baFMz sz z).eta n v := by
    rw [TwistKer2_eta_eq]
    have := mul_le_mul h1v hm.1 hκ.le (by linarith)
    linarith
  have hκN : 0 < κ * (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2) := by positivity
  calc ((baFMz sz z).eta n v)⁻¹ ≤ (κ * (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) / 2))⁻¹ := inv_anti₀ hκN hη
    _ = (2 / κ) * ((sz.size n : ℕ) : ℝ) := by
        rw [Real.rpow_neg_one]; field_simp

/-- `‖m_F‖ ≤ 1` (a copy of the last step of `EMn2BA_mF_data`, `BA/EMn2BA.lean:125`). -/
private theorem TwistKer2_m_norm (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : ‖(baFMz sz z).m n‖ ≤ 1 := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  exact BAm_norm_le_one d (sz.L n) _ ((BAflowEs sz z n : ℝ) : ℂ) _ (by simp) hr.1

/-- **`|𝒦^{(2)}| ≤ η⁻¹`** (every charge pair): `𝒦^{(2)}_{(a,b)} = W^{-d} (Θ M)(a,b)` (`baKsol_two`), `Σ_b |(Θ M)(a,b)| ≤ (1-v)⁻¹` (`baComp_row_le`), `η ≤ 1 - v`. -/
private theorem TwistKer2_K2_le (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg : 0 < BAflowLam0 sz z n) {v : ℝ} (hv0 : 0 ≤ v)
    (hvT : v ≤ BAflowT0 sz z n) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    ‖(baFMz sz z).K n v σ ![a, b]‖ ≤ ((baFMz sz z).eta n v)⁻¹ := by
  have hu1 : v < 1 := hvT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have h := baKsol_two d hκ hg (sz.three_le_L n) (sz.W n) hr ⟨hv0, hu1⟩ σ ![a, b]
  have e : (baFMz sz z).K n v σ ![a, b] = (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) * BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n)
        (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1)) a b := h
  rw [e, norm_mul, TwistKer2_norm_winv n]
  have hrow := baComp_row_le hr hv0 hu1 (σ 0) (σ 1) a
  have hent : ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) (σ 1)) a b‖ ≤
      (1 - v)⁻¹ := by
    refine le_trans ?_ hrow
    exact Finset.single_le_sum (f := fun b' => ‖(BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v
      (σ 0) (σ 1) * BAMss d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))
        (σ 0) (σ 1)) a b'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ b)
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hm := EMn2BA_mF_data sz hflow n
  have h1v : 0 < 1 - v := by linarith
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have hη' : (1 - v)⁻¹ ≤ ((baFMz sz z).eta n v)⁻¹ := by
    refine inv_anti₀ hη ?_
    rw [TwistKer2_eta_eq]
    nlinarith [hm.2]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖_‖ ≤ 1 * (1 - v)⁻¹ :=
        mul_le_mul hW1 hent (norm_nonneg _) zero_le_one
    _ ≤ ((baFMz sz z).eta n v)⁻¹ := by rw [one_mul]; exact hη'

end Facts5

section Engine

variable {d : ℕ} {sz : Sizes d}

/-- **The engine of T.11 (v)**: `twDec` for `F` from the fourth conjunct of `twSteps` at `k = 2` (`τ' = ε`, `D' = D_pp`) and a deterministic implication: on the event
`(‖𝓛^{(2)}‖ + ‖(𝓛-𝒦)^{(2)}‖) 1(ℓ_v W^ε ≤ |p - q|_∞) ≤ N^{τ/2} W^{-D_pp}`, the source satisfies `F ≤ N^τ W^{-D}` at every `(v, σ, a, c₁, c₂)` with `|a - c₁|_∞ ≥ 3 W^ε ℓ_v`. -/
private theorem TwistKer2_dec_engine {C : FlowFM sz} {μ : Measure sz.SeqΩ} {s t : ℕ → ℝ}
    (h4 : ∀ τ' D' : ℝ, 0 < τ' → 0 < D' → PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
      (fun n p ω => (‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω‖ + ‖C.L n (p.1 : ℝ) p.2.1 p.2.2 ω - C.K n (p.1 : ℝ) p.2.1 p.2.2‖) *
        (if ellT (sz.L n) (sz.lam n) (p.1 : ℝ) * ((sz.W n : ℕ) : ℝ) ^ τ' ≤ (STdiamInf p.2.2 : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D')))
    (F : ∀ n, ℝ → sz.SeqΩ → (Fin 2 → Bool) → Zd d (sz.L n) → Zd d (sz.L n) → Zd d (sz.L n) → ℝ)
    (ε D Dpp : ℝ) (hε : 0 < ε) (hDpp : 0 < Dpp)
    (hitem : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ∀ (ω : sz.SeqΩ) (v : ℝ), s n ≤ v → v ≤ t n → ∀ (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)),
      3 * ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) →
      (∀ (σ' : Fin 2 → Bool) (p q : Zd d (sz.L n)), ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (p - q) : ℝ) →
        ‖C.L n v σ' ![p, q] ω‖ + ‖C.L n v σ' ![p, q] ω - C.K n v σ' ![p, q]‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-Dpp)) →
      F n v ω σ a c₁ c₂ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-D)) :
    PrecL sz μ (U := fun n => TimeIcc s t n × (Fin 2 → Bool) × Zd d (sz.L n) × Zd d (sz.L n) × Zd d (sz.L n))
      (fun n p ω => F n (p.1 : ℝ) ω p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 *
        (if 3 * ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) (p.1 : ℝ) ≤ (zdistInf d (sz.L n) (p.2.2.1 - p.2.2.2.1) : ℝ) then 1 else 0))
      (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  refine TwistKer2_of_subset (h4 ε Dpp hε hDpp) (fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩)
  filter_upwards [hitem τ hτ] with n hn
  rintro ω ⟨⟨⟨v, hv⟩, σ, a, c₁, c₂⟩, hp⟩
  by_contra hno
  simp only [badSetAt, Set.mem_ofPred_eq, not_exists, not_lt] at hno
  by_cases hc : 3 * ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ)
  · simp only [hc, ↓reduceIte, mul_one] at hp
    have hloop : ∀ (σ' : Fin 2 → Bool) (p q : Zd d (sz.L n)), ((sz.W n : ℕ) : ℝ) ^ ε * ellT (sz.L n) (sz.lam n) v ≤ (zdistInf d (sz.L n) (p - q) : ℝ) →
        ‖C.L n v σ' ![p, q] ω‖ + ‖C.L n v σ' ![p, q] ω - C.K n v σ' ![p, q]‖ ≤
          ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-Dpp) := by
      intro σ' p q hpq
      have h1 := hno ⟨⟨v, hv⟩, σ', ![p, q]⟩
      have hdiam : (zdistInf d (sz.L n) (p - q) : ℝ) ≤ (STdiamInf (![p, q] : Fin 2 → Zd d (sz.L n)) : ℝ) := by
        have : zdistInf d (sz.L n) (p - q) ≤ STdiamInf (![p, q] : Fin 2 → Zd d (sz.L n)) :=
          Finset.le_sup (f := fun pr : Fin 2 × Fin 2 => zdistInf d (sz.L n) ((![p, q] : Fin 2 → Zd d (sz.L n)) pr.1 - (![p, q] : Fin 2 → Zd d (sz.L n)) pr.2))
            (Finset.mem_univ ((0 : Fin 2), (1 : Fin 2)))
        exact_mod_cast this
      have hind : ellT (sz.L n) (sz.lam n) v * ((sz.W n : ℕ) : ℝ) ^ ε ≤ (STdiamInf (![p, q] : Fin 2 → Zd d (sz.L n)) : ℝ) := by
        rw [mul_comm]; exact hpq.trans hdiam
      simpa [hind] using h1
    exact absurd (hn ω v hv.1 hv.2 σ a c₁ c₂ hc hloop) (not_le.2 hp)
  · simp only [hc, ↓reduceIte, mul_zero] at hp
    exact absurd hp (not_lt.2 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

/-- The closing arithmetic of T.11 (v): `F ≤ a N⁸ ρ^{1/2} + b N⁸ ρ + c N⁸ W^{-(D+8/𝔠)}` with `a + b + c ≤ N^{τ/2}` gives `F ≤ N^τ W^{-D}`. -/
private theorem TwistKer2_close {Nn Wn 𝔠 τ D a b c F : ℝ} (hN : 1 ≤ Nn) (hW : 1 ≤ Wn) (h𝔠 : 0 < 𝔠) (hbd : Nn ^ 𝔠 ≤ Wn) (hτ : 0 < τ) (hD : 0 ≤ D)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcst : a + b + c ≤ Nn ^ (τ / 2))
    (hF : F ≤ a * (Nn ^ 8 * Real.sqrt (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠)))) + b * (Nn ^ 8 * (Nn ^ (τ / 2) * Wn ^ (-(2 * D + 16 / 𝔠)))) +
      c * (Nn ^ 8 * Wn ^ (-(D + 8 / 𝔠)))) :
    F ≤ Nn ^ τ * Wn ^ (-D) := by
  obtain ⟨h1, h2, h3⟩ := TwistKer2_arith hN hW h𝔠 hbd hτ hD (D := D)
  have hN0 : 0 < Nn := by linarith
  have hQ : 0 ≤ Nn ^ (τ / 2) * Wn ^ (-D) := mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg (by linarith) _)
  calc F ≤ a * (Nn ^ (τ / 2) * Wn ^ (-D)) + b * (Nn ^ (τ / 2) * Wn ^ (-D)) + c * (Nn ^ (τ / 2) * Wn ^ (-D)) :=
        hF.trans (add_le_add (add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)) (mul_le_mul_of_nonneg_left h3 hc))
    _ = (a + b + c) * (Nn ^ (τ / 2) * Wn ^ (-D)) := by ring
    _ ≤ Nn ^ (τ / 2) * (Nn ^ (τ / 2) * Wn ^ (-D)) := mul_le_mul_of_nonneg_right hcst hQ
    _ = Nn ^ τ * Wn ^ (-D) := by
        rw [← mul_assoc, ← Real.rpow_add hN0]; congr 2; ring

end Engine

section Items5

variable {d : ℕ} {sz : Sizes d} {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ}

/-- `W^d ≤ N` and `L^d ≤ N`. -/
private theorem TwistKer2_Wd_Ld_le (n : ℕ) : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) ∧ ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
  have hW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hsize : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  rw [hsize]
  exact ⟨le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL), le_mul_of_one_le_left (by positivity) (one_le_pow₀ hW)⟩

/-- The carrier at `(n, v, ω)` with the entry facts of T.11 (v): a Hermitian `H` and `ζ` with `Im ζ = η_v`, `G = Gres H ζ true`, `𝓛 = loopFine H ζ`, all entries of `G(σ)` are `≤ η⁻¹`,
and the entries between blocks at distance `≥ X` are `≤ W^d ρ^{1/2}` (from the 2-loop decay `ρ`). -/
private theorem TwistKer2_entries (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hvT : v ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) {X ρ : ℝ}
    (hloop : ∀ (σ' : Fin 2 → Bool) (p q : Zd d (sz.L n)), X ≤ (zdistInf d (sz.L n) (p - q) : ℝ) →
      ‖(baFMz sz z).L n v σ' ![p, q] ω‖ + ‖(baFMz sz z).L n v σ' ![p, q] ω - (baFMz sz z).K n v σ' ![p, q]‖ ≤ ρ) :
    ∃ (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (ζ : ℂ), H.IsHermitian ∧ ζ.im = (baFMz sz z).eta n v ∧
      (baFMz sz z).G n v ω = Gres H ζ true ∧
      (∀ (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)), (baFMz sz z).L n v σ a ω = loopFine d (sz.L n) (sz.W n) H ζ σ a) ∧
      (∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres H ζ τ y x‖ ≤ ((baFMz sz z).eta n v)⁻¹) ∧
      (∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)),
        X ≤ (zdistInf d (sz.L n) ((split d (sz.L n) (sz.W n) y).1 - (split d (sz.L n) (sz.W n) x).1) : ℝ) →
          ‖Gres H ζ τ y x‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ) := by
  obtain ⟨hGc, hLc, hzc⟩ := TwistKer2_carrier sz z n v ω
  have hH := TwistKer2_hermitian sz z n v ω
  obtain ⟨hη, -⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hz : 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v).im := by rw [hzc]; exact hη
  refine ⟨_, _, hH, hzc, hGc, hLc, fun τ y x => ?_, ?_⟩
  · have := TwistKer_entry_le hH hz τ y x
    rwa [hzc] at this
  · refine TwistKer_entry_decay n hH (fun p q hpq => ?_)
    rw [← hLc 2]
    exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hloop ![true, false] p q hpq)

/-- **T.11 (v) for `Z = L̃ - K̃`**: `|L̃_{σ,(a;c₁,c₂)}| ≤ ν Λ` (entries of `G` between `[a]` and `[c₁]`, `TwistKer_twL2_bounds`) and `|K̃| ≤ W^{-D₁}` (`baTwKDecay_holds`). -/
private theorem TwistKer2_decZ (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Cd : ℝ}
    (hsteps : twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    twDec (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖) := by
  intro ε' D hε' hD
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  refine TwistKer2_dec_engine (hsteps.2.2.2 2 (by norm_num))
    (fun n v ω σ a c₁ c₂ => ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖) ε' D (2 * D + 16 / 𝔠) hε' (by positivity) ?_
  intro τ hτ
  have hK := baTwKDecay_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow ε' (D + 8 / 𝔠) hε' (by positivity)
  have hsize := tendsto_size sz hflow.1.2.2.1
  filter_upwards [hband, hK, hsize.eventually (eventually_le_rpow (2 / κ + 1) (half_pos hτ))] with n hb hK hcst
  intro ω v hv1 hv2 σ a c₁ c₂ hcut hloop
  have hv0 : 0 ≤ v := (hs n).trans hv1
  have hvT : v ≤ BAflowT0 sz z n := hv2.trans (htT n)
  obtain ⟨H, ζ, hH, hzc, hG, hL, hbd, hDec⟩ := TwistKer2_entries hκ hflow n hv0 hvT ω hloop
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hΛ := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hWd, -⟩ := TwistKer2_Wd_Ld_le (sz := sz) n
  set ρ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D + 16 / 𝔠)) with hρ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith) _) (by have := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := v) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)); linarith)
  have hXa : X ≤ (zdistInf d (sz.L n) (a - c₁) : ℝ) := by linarith
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  set ν : ℝ := ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ with hν
  have hν0 : 0 ≤ ν := by positivity
  have hL2 := TwistKer_twL2_bounds n (baFMz sz z) hH v ω hG σ a c₁ c₂ hν0 hbd hDec
  have hKd := hK v hv0 hvT σ a c₁ c₂ hXa
  have hsq := Real.sqrt_nonneg ρ
  have hN8 : ((sz.size n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := pow_le_pow_right₀ hNN (by norm_num)
  have hW1 : ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠)) ≤ ((sz.size n : ℕ) : ℝ) ^ 8 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠)) :=
    le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _) (one_le_pow₀ hNN)
  refine TwistKer2_close (a := 2 / κ) (b := 0) (c := 1) hNN hWW h𝔠 hb hτ hD.le (by positivity) le_rfl zero_le_one (by linarith) ?_
  calc ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖
      ≤ ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂‖ + ‖twK (baFMz sz z) n v σ a c₁ c₂‖ := norm_sub_le _ _
    _ ≤ ν * ((baFMz sz z).eta n v)⁻¹ + ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠)) := add_le_add (hL2.2 hXa) hKd
    _ ≤ 2 / κ * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + 0 * (((sz.size n : ℕ) : ℝ) ^ 8 * ρ) +
          1 * (((sz.size n : ℕ) : ℝ) ^ 8 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠))) := by
        have h1 : ν * ((baFMz sz z).eta n v)⁻¹ ≤ 2 / κ * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) := by
          have : ν * ((baFMz sz z).eta n v)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) * Real.sqrt ρ) * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hWd hsq) hΛ (inv_nonneg.2 hη.le) (by positivity)
          calc ν * ((baFMz sz z).eta n v)⁻¹ ≤ _ := this
            _ = 2 / κ * (((sz.size n : ℕ) : ℝ) ^ 2 * Real.sqrt ρ) := by ring
            _ ≤ 2 / κ * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) := by gcongr
        linarith

/-- **T.11 (v) for `Ẽ^{G̊}`** (`TwistKer_twEG_decay`: entries of `G` between `[a]`, `[c₁]` or `[a]`, `[a']`, `[a']`, `[c₁]`, and `|Tr(G̊E_{a'})| ≤ η⁻¹ + 1`). -/
private theorem TwistKer2_decEG (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Cd : ℝ}
    (hsteps : twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    twDec (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twEG (baFMz sz z) n v ω σ a c₁ c₂‖) := by
  intro ε' D hε' hD
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  refine TwistKer2_dec_engine (hsteps.2.2.2 2 (by norm_num)) (fun n v ω σ a c₁ c₂ => ‖twEG (baFMz sz z) n v ω σ a c₁ c₂‖) ε' D
    (2 * D + 16 / 𝔠) hε' (by positivity) ?_
  intro τ hτ
  have hsize := tendsto_size sz hflow.1.2.2.1
  filter_upwards [hband, hsize.eventually (eventually_le_rpow (4 * (2 / κ) ^ 3) (half_pos hτ))] with n hb hcst
  intro ω v hv1 hv2 σ a c₁ c₂ hcut hloop
  have hv0 : 0 ≤ v := (hs n).trans hv1
  have hvT : v ≤ BAflowT0 sz z n := hv2.trans (htT n)
  obtain ⟨H, ζ, hH, hzc, hG, hL, hbd, hDec⟩ := TwistKer2_entries hκ hflow n hv0 hvT ω hloop
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hΛ := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hWd, -⟩ := TwistKer2_Wd_Ld_le (sz := sz) n
  set ρ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D + 16 / 𝔠)) with hρ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith) _) (by have := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := v) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)); linarith)
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  set ν : ℝ := ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ with hν
  have hν0 : 0 ≤ ν := by positivity
  set Λ : ℝ := ((baFMz sz z).eta n v)⁻¹ with hΛdef
  have hΛ1 : 1 ≤ Λ := (one_le_inv₀ hη).2 hη1
  have hhz : 0 < ζ.im := by rw [hzc]; exact hη
  have htr : ∀ (τ' : Bool) (a' : Zd d (sz.L n)), ‖(baFMz sz z).L n v ![τ'] ![a'] ω -
      (if τ' then (baFMz sz z).m n else (starRingEnd ℂ) ((baFMz sz z).m n))‖ ≤ Λ + 1 := by
    intro τ' a'
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [hL 1]
      have := TwistKer_loop1_le n hH hhz τ' a'
      rwa [hzc] at this
    · have hm := TwistKer2_m_norm hflow n
      cases τ'
      · simpa [Complex.norm_conj] using hm
      · simpa using hm
  have hMt : Λ + 1 ≤ 2 * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) := by linarith
  have hEG := TwistKer_twEG_decay n (baFMz sz z) hH v ω hG σ a c₁ c₂ hν0 hX0 hbd hDec htr (by linarith)
  have hsq := Real.sqrt_nonneg ρ
  have hΛ0 : 0 ≤ Λ := by linarith
  refine TwistKer2_close (a := 4 * (2 / κ) ^ 3) (b := 0) (c := 0) hNN hWW h𝔠 hb hτ hD.le (by positivity) le_rfl le_rfl (by linarith) ?_
  have hνN : ν ≤ ((sz.size n : ℕ) : ℝ) * Real.sqrt ρ := mul_le_mul_of_nonneg_right hWd hsq
  calc ‖twEG (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.size n : ℕ) : ℝ) * (2 * ((Λ + 1) * (Λ * (Λ * ν)))) := hEG
    _ ≤ ((sz.size n : ℕ) : ℝ) * (2 * ((2 * ((2 / κ) * ((sz.size n : ℕ) : ℝ))) * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) *
          (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * (((sz.size n : ℕ) : ℝ) * Real.sqrt ρ))))) := by
        gcongr
    _ = 4 * (2 / κ) ^ 3 * (((sz.size n : ℕ) : ℝ) ^ 5 * Real.sqrt ρ) := by ring
    _ ≤ 4 * (2 / κ) ^ 3 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hNN (by norm_num)) hsq) (by positivity)
    _ = 4 * (2 / κ) ^ 3 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + 0 * (((sz.size n : ℕ) : ℝ) ^ 8 * ρ) +
          0 * (((sz.size n : ℕ) : ℝ) ^ 8 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠))) := by ring

/-- **T.11 (v) for `(Ẽ⊗Ẽ)(·, b')`** (`TwistKer_twEE_decay`; `S = I` at BA, `(baFMz sz z).S n = 1`): decay in the first index for every second index `b'`. -/
private theorem TwistKer2_decEE (hκ : 0 < κ) (hε : 0 < ε) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Cd : ℝ}
    (hsteps : twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) (b' : ∀ n, Zd d (sz.L n)) :
    twDec (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twEE (baFMz sz z) n v ω σ a (b' n) c₁ c₂‖) := by
  intro ε' D hε' hD
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  refine TwistKer2_dec_engine (hsteps.2.2.2 2 (by norm_num)) (fun n v ω σ a c₁ c₂ => ‖twEE (baFMz sz z) n v ω σ a (b' n) c₁ c₂‖) ε' D
    (2 * D + 16 / 𝔠) hε' (by positivity) ?_
  intro τ hτ
  have hsize := tendsto_size sz hflow.1.2.2.1
  filter_upwards [hband, hsize.eventually (eventually_le_rpow (4 * (2 / κ) ^ 5) (half_pos hτ))] with n hb hcst
  intro ω v hv1 hv2 σ a c₁ c₂ hcut hloop
  have hv0 : 0 ≤ v := (hs n).trans hv1
  have hvT : v ≤ BAflowT0 sz z n := hv2.trans (htT n)
  obtain ⟨H, ζ, hH, hzc, hG, hL, hbd, hDec⟩ := TwistKer2_entries hκ hflow n hv0 hvT ω hloop
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hΛ := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hWd, -⟩ := TwistKer2_Wd_Ld_le (sz := sz) n
  set ρ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D + 16 / 𝔠)) with hρ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith) _) (by have := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := v) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)); linarith)
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  set ν : ℝ := ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ with hν
  have hν0 : 0 ≤ ν := by positivity
  set Λ : ℝ := ((baFMz sz z).eta n v)⁻¹ with hΛdef
  have hΛ1 : 1 ≤ Λ := (one_le_inv₀ hη).2 hη1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hS0 : ∀ p q : Zd d (sz.L n), p ≠ q → (baFMz sz z).S n p q = 0 := fun p q hpq => Matrix.one_apply_ne hpq
  have hS1 : ∀ p q : Zd d (sz.L n), ‖(baFMz sz z).S n p q‖ ≤ 1 := fun p q => by
    by_cases hpq : p = q
    · subst hpq; simp [baFMz, baFM]
    · rw [hS0 p q hpq]; simp
  have hEE := TwistKer_twEE_decay n (baFMz sz z) hH v ω hG σ a (b' n) c₁ c₂ hν0 hX0 hbd hDec hS0 hS1 (by linarith)
  have hsq := Real.sqrt_nonneg ρ
  refine TwistKer2_close (a := 4 * (2 / κ) ^ 5) (b := 0) (c := 0) hNN hWW h𝔠 hb hτ hD.le (by positivity) le_rfl le_rfl (by linarith) ?_
  have hνN : ν ≤ ((sz.size n : ℕ) : ℝ) * Real.sqrt ρ := mul_le_mul_of_nonneg_right hWd hsq
  calc ‖twEE (baFMz sz z) n v ω σ a (b' n) c₁ c₂‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * (2 * (Λ * (Λ * ν)) * (2 * (Λ * (Λ * Λ)))) := hEE
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 * (2 * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) *
          (((sz.size n : ℕ) : ℝ) * Real.sqrt ρ))) * (2 * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) *
          ((2 / κ) * ((sz.size n : ℕ) : ℝ)))))) := by
        gcongr
    _ = 4 * (2 / κ) ^ 5 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) := by ring
    _ = 4 * (2 / κ) ^ 5 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + 0 * (((sz.size n : ℕ) : ℝ) ^ 8 * ρ) +
          0 * (((sz.size n : ℕ) : ℝ) ^ 8 * ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠))) := by ring

/-- **The deterministic bound of `𝓛^{(2)} - 𝒦^{(2)}`**: `|𝓛^{(2)}_{σ,(a,b)}| ≤ η⁻²`, `|𝒦^{(2)}_{σ,(a,b)}| ≤ η⁻¹`, so `|(𝓛-𝒦)^{(2)}| ≤ 2 η⁻²`. -/
private theorem TwistKer2_LK_det (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) (hg : 0 < BAflowLam0 sz z n) {v : ℝ} (hv0 : 0 ≤ v)
    (hvT : v ≤ BAflowT0 sz z n) (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a b : Zd d (sz.L n)) :
    ‖(baFMz sz z).L n v σ ![a, b] ω‖ ≤ ((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹ ∧
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤ 2 * (((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹) := by
  obtain ⟨hGc, hLc, hzc⟩ := TwistKer2_carrier sz z n v ω
  have hH := TwistKer2_hermitian sz z n v ω
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hz : 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v).im := by rw [hzc]; exact hη
  have hσ : σ = ![σ 0, σ 1] := by funext i; fin_cases i <;> rfl
  have h1 : ‖(baFMz sz z).L n v σ ![a, b] ω‖ ≤ ((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹ := by
    rw [hLc 2, hσ]
    have := TwistKer_loop2_le n hH hz (σ 0) (σ 1) a b
    rwa [hzc] at this
  refine ⟨h1, ?_⟩
  have h2 := TwistKer2_K2_le hκ hflow n hg hv0 hvT σ a b
  have hΛ1 : 1 ≤ ((baFMz sz z).eta n v)⁻¹ := (one_le_inv₀ hη).2 hη1
  calc ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤ ‖(baFMz sz z).L n v σ ![a, b] ω‖ + ‖(baFMz sz z).K n v σ ![a, b]‖ :=
        norm_sub_le _ _
    _ ≤ ((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹ + ((baFMz sz z).eta n v)⁻¹ := add_le_add h1 h2
    _ ≤ 2 * (((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹) := by nlinarith

/-- **T.11 (v) for `B̃₁`** (`TP:146`): each summand of `W^d Σ_b K̃(b) (𝓛-𝒦)_{(a,b)}` has `|b - c₁| ≥ W^ε ℓ` (`K̃` decays, `baTwKDecay_holds`) or `|a - b| ≥ 2 W^ε ℓ` (the 2-loop decays);
`Σ_b |K̃(b)| ≤ C (W^d η)⁻¹` (`twK_bound_holds`) and the deterministic bound `2 η⁻²` of `𝓛^{(2)} - 𝒦^{(2)}`. -/
private theorem TwistKer2_decB1 (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Cd : ℝ}
    (hsteps : twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    twDec (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖) := by
  intro ε' D hε' hD
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  obtain ⟨CK, hCK, HK⟩ := TwistKer2_twK_unif hd hκ hε h𝔡
  refine TwistKer2_dec_engine (hsteps.2.2.2 2 (by norm_num)) (fun n v ω σ a c₁ c₂ => ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖) ε' D
    (2 * D + 16 / 𝔠) hε' (by positivity) ?_
  intro τ hτ
  have hK := baTwKDecay_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow ε' (D + 8 / 𝔠) hε' (by positivity)
  have hsize := tendsto_size sz hflow.1.2.2.1
  filter_upwards [hband, hK, HK 𝔠 sz z hflow, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow,
    hsize.eventually (eventually_le_rpow (CK * (2 / κ) + 2 * (2 / κ) ^ 2) (half_pos hτ))] with n hb hK hKu hlam hcst
  intro ω v hv1 hv2 σ a c₁ c₂ hcut hloop
  have hv0 : 0 ≤ v := (hs n).trans hv1
  have hvT : v ≤ BAflowT0 sz z n := hv2.trans (htT n)
  obtain ⟨H, ζ, hH, hzc, hG, hL, hbd, hDec⟩ := TwistKer2_entries hκ hflow n hv0 hvT ω hloop
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hΛ := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hWd, hLd⟩ := TwistKer2_Wd_Ld_le (sz := sz) n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  set ρ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D + 16 / 𝔠)) with hρ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith) _) (by have := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := v) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)); linarith)
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  set Λ : ℝ := ((baFMz sz z).eta n v)⁻¹ with hΛdef
  have hΛ1 : 1 ≤ Λ := (one_le_inv₀ hη).2 hη1
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨-, hKs⟩ := hKu v hv0 hvT σ c₁ c₂
  set Wm : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠)) with hWm
  have hWm0 : 0 ≤ Wm := Real.rpow_nonneg (by linarith) _
  have hterm : ∀ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
      Wm * (2 * (Λ * Λ)) + ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ := by
    intro b
    by_cases hfar : X ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ)
    · have h1 := hK v hv0 hvT σ b c₁ c₂ hfar
      have h2 := (TwistKer2_LK_det hκ hflow n hlam.1 hv0 hvT ω σ a b).2
      calc ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤ Wm * (2 * (Λ * Λ)) :=
            mul_le_mul h1 h2 (norm_nonneg _) hWm0
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) hρ0)
    · push Not at hfar
      rcases TwistKer_far_split (X := X) (sz.L n) a b c₁ (by linarith) with h | h
      · have h3 := hloop σ a b h
        calc ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
              ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ :=
            mul_le_mul_of_nonneg_left (le_trans (le_add_of_nonneg_left (norm_nonneg _)) h3) (norm_nonneg _)
          _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hWm0 (by positivity))
      · exact absurd h (not_le.2 hfar)
  have hB1 : ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ *
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ := by
    unfold twB1
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_mul _ _).le)) (by positivity)
  have hsumK : ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ ≤ CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹ := hKs
  have hsum : ∑ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
      ((sz.L n : ℕ) : ℝ) ^ d * (Wm * (2 * (Λ * Λ))) + ρ * (CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹) := by
    calc _ ≤ ∑ b : Zd d (sz.L n), (Wm * (2 * (Λ * Λ)) + ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ) := Finset.sum_le_sum fun b _ => hterm b
      _ = ((sz.L n : ℕ) : ℝ) ^ d * (Wm * (2 * (Λ * Λ))) + ρ * ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ := by
          have e : ∑ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ = ρ * ∑ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ := by
            rw [← Finset.sum_mul, mul_comm]
          rw [Finset.sum_add_distrib, e, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          rfl
      _ ≤ _ := by
          have : 0 ≤ ρ := hρ0
          have := mul_le_mul_of_nonneg_left hsumK hρ0
          linarith
  have hsq := Real.sqrt_nonneg ρ
  refine TwistKer2_close (a := 0) (b := CK * (2 / κ)) (c := 2 * (2 / κ) ^ 2) hNN hWW h𝔠 hb hτ hD.le le_rfl (by positivity) (by positivity) (by linarith) ?_
  calc ‖twB1 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * (Wm * (2 * (Λ * Λ))) +
        ρ * (CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹)) := hB1.trans (mul_le_mul_of_nonneg_left hsum hW0.le)
    _ = ((sz.size n : ℕ) : ℝ) * (Wm * (2 * (Λ * Λ))) + CK * Λ * ρ := by
        have hsize' : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by simp [Sizes.size, mul_pow]
        rw [hsize', hΛdef]
        field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) * (Wm * (2 * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ((2 / κ) * ((sz.size n : ℕ) : ℝ))))) +
          CK * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ρ := by
        gcongr
    _ = 0 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + (CK * (2 / κ)) * (((sz.size n : ℕ) : ℝ) * ρ) +
          (2 * (2 / κ) ^ 2) * (((sz.size n : ℕ) : ℝ) ^ 3 * Wm) := by ring
    _ ≤ 0 * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + (CK * (2 / κ)) * (((sz.size n : ℕ) : ℝ) ^ 8 * ρ) +
          (2 * (2 / κ) ^ 2) * (((sz.size n : ℕ) : ℝ) ^ 8 * Wm) := by
        have h1 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := by
          calc ((sz.size n : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ hNN (by norm_num)
        have h3 : ((sz.size n : ℕ) : ℝ) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := pow_le_pow_right₀ hNN (by norm_num)
        have hc1 : 0 ≤ CK * (2 / κ) := by positivity
        have hc2 : 0 ≤ 2 * (2 / κ) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hρ0) hc1
        have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hWm0) hc2
        linarith

/-- **T.11 (v) for `B̃₂`** (`TP:146`): as `B̃₁` with `Z(b) = L̃(b) - K̃(b)`: `|Z(b)| ≤ ν Λ + W^{-D₁}` for `|b - c₁| ≥ W^ε ℓ` (`TwistKer2_decZ`'s deterministic part) and
`|Z(b)| ≤ η⁻² + |K̃(b)|` always. -/
private theorem TwistKer2_decB2 (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ}
    (hs : ∀ n, 0 ≤ s n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) {Cd : ℝ}
    (hsteps : twSteps (baFMz sz z) (Sizes.seqP (sz.withLam 0)) s t Cd) :
    twDec (sz := sz) (Sizes.seqP (sz.withLam 0)) s t (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖) := by
  intro ε' D hε' hD
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  obtain ⟨CK, hCK, HK⟩ := TwistKer2_twK_unif hd hκ hε h𝔡
  refine TwistKer2_dec_engine (hsteps.2.2.2 2 (by norm_num)) (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖) ε' D
    (2 * D + 16 / 𝔠) hε' (by positivity) ?_
  intro τ hτ
  have hK := baTwKDecay_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow ε' (D + 8 / 𝔠) hε' (by positivity)
  have hsize := tendsto_size sz hflow.1.2.2.1
  filter_upwards [hband, hK, HK 𝔠 sz z hflow, BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow,
    hsize.eventually (eventually_le_rpow (2 * (2 / κ) ^ 3 + ((2 / κ) ^ 2 + CK * (2 / κ)) + 2 * (2 / κ) ^ 2) (half_pos hτ))]
    with n hb hK hKu hlam hcst
  intro ω v hv1 hv2 σ a c₁ c₂ hcut hloop
  have hv0 : 0 ≤ v := (hs n).trans hv1
  have hvT : v ≤ BAflowT0 sz z n := hv2.trans (htT n)
  obtain ⟨H, ζ, hH, hzc, hG, hL, hbd, hDec⟩ := TwistKer2_entries hκ hflow n hv0 hvT ω hloop
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hΛ := TwistKer2_eta_inv_le hκ hε hflow n hv0 hvT
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hWW : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  obtain ⟨hWd, hLd⟩ := TwistKer2_Wd_Ld_le (sz := sz) n
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  set ρ : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-(2 * D + 16 / 𝔠)) with hρ
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ ε' * ellT (sz.L n) (sz.lam n) v with hX
  have hX0 : 0 ≤ X := mul_nonneg (Real.rpow_nonneg (by linarith) _) (by have := one_le_ellT (L := sz.L n) (g := sz.lam n) (t := v) (by exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)); linarith)
  have hρ0 : 0 ≤ ρ := mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  set ν : ℝ := ((sz.W n : ℕ) : ℝ) ^ d * Real.sqrt ρ with hν
  have hsq := Real.sqrt_nonneg ρ
  have hν0 : 0 ≤ ν := by positivity
  set Λ : ℝ := ((baFMz sz z).eta n v)⁻¹ with hΛdef
  have hΛ1 : 1 ≤ Λ := (one_le_inv₀ hη).2 hη1
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨-, hKs⟩ := hKu v hv0 hvT σ c₁ c₂
  set Wm : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-(D + 8 / 𝔠)) with hWm
  have hWm0 : 0 ≤ Wm := Real.rpow_nonneg (by linarith) _
  have hterm : ∀ b : Zd d (sz.L n), ‖twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂‖ *
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
      (ν * Λ + Wm) * (2 * (Λ * Λ)) + (Λ * Λ + ‖twK (baFMz sz z) n v σ b c₁ c₂‖) * ρ := by
    intro b
    have hL2 := TwistKer_twL2_bounds n (baFMz sz z) hH v ω hG σ b c₁ c₂ hν0 hbd hDec
    by_cases hfar : X ≤ (zdistInf d (sz.L n) (b - c₁) : ℝ)
    · have h1 := hK v hv0 hvT σ b c₁ c₂ hfar
      have h2 := (TwistKer2_LK_det hκ hflow n hlam.1 hv0 hvT ω σ a b).2
      have hZ : ‖twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂‖ ≤ ν * Λ + Wm :=
        (norm_sub_le _ _).trans (add_le_add (hL2.2 hfar) h1)
      calc _ ≤ (ν * Λ + Wm) * (2 * (Λ * Λ)) := mul_le_mul hZ h2 (norm_nonneg _) (by positivity)
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by positivity) hρ0)
    · push Not at hfar
      rcases TwistKer_far_split (X := X) (sz.L n) a b c₁ (by linarith) with h | h
      · have h3 := hloop σ a b h
        have hZ : ‖twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂‖ ≤ Λ * Λ + ‖twK (baFMz sz z) n v σ b c₁ c₂‖ :=
          (norm_sub_le _ _).trans (add_le_add hL2.1 le_rfl)
        calc _ ≤ (Λ * Λ + ‖twK (baFMz sz z) n v σ b c₁ c₂‖) * ρ :=
              mul_le_mul hZ (le_trans (le_add_of_nonneg_left (norm_nonneg _)) h3) (norm_nonneg _) (by positivity)
          _ ≤ _ := le_add_of_nonneg_left (by positivity)
      · exact absurd h (not_le.2 hfar)
  have hB2 : ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ∑ b, ‖twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂‖ *
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ := by
    unfold twB2
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => (norm_mul _ _).le)) (by positivity)
  have hsumK : ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ ≤ CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹ := hKs
  have hsum : ∑ b : Zd d (sz.L n), ‖twL2' (baFMz sz z) n v ω σ b c₁ c₂ - twK (baFMz sz z) n v σ b c₁ c₂‖ *
      ‖(baFMz sz z).L n v σ ![a, b] ω - (baFMz sz z).K n v σ ![a, b]‖ ≤
      ((sz.L n : ℕ) : ℝ) ^ d * ((ν * Λ + Wm) * (2 * (Λ * Λ)) + Λ * Λ * ρ) + ρ * (CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹) := by
    calc _ ≤ ∑ b : Zd d (sz.L n), (((ν * Λ + Wm) * (2 * (Λ * Λ)) + Λ * Λ * ρ) + ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ) :=
          Finset.sum_le_sum fun b _ => (hterm b).trans (le_of_eq (by ring))
      _ = ((sz.L n : ℕ) : ℝ) ^ d * ((ν * Λ + Wm) * (2 * (Λ * Λ)) + Λ * Λ * ρ) + ρ * ∑ b, ‖twK (baFMz sz z) n v σ b c₁ c₂‖ := by
          have e : ∑ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ * ρ = ρ * ∑ b : Zd d (sz.L n), ‖twK (baFMz sz z) n v σ b c₁ c₂‖ := by
            rw [← Finset.sum_mul, mul_comm]
          rw [Finset.sum_add_distrib, e, Finset.sum_const, Finset.card_univ, card_Zd, nsmul_eq_mul]
          push_cast
          rfl
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hsumK hρ0
          linarith
  refine TwistKer2_close (a := 2 * (2 / κ) ^ 3) (b := (2 / κ) ^ 2 + CK * (2 / κ)) (c := 2 * (2 / κ) ^ 2) hNN hWW h𝔠 hb hτ hD.le (by positivity)
    (by positivity) (by positivity) hcst ?_
  have hνN : ν ≤ ((sz.size n : ℕ) : ℝ) * Real.sqrt ρ := mul_le_mul_of_nonneg_right hWd hsq
  have hsize' : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by simp [Sizes.size, mul_pow]
  calc ‖twB2 (baFMz sz z) n v ω σ a c₁ c₂‖ ≤ ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((ν * Λ + Wm) * (2 * (Λ * Λ)) + Λ * Λ * ρ) +
        ρ * (CK * ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n v)⁻¹)) := hB2.trans (mul_le_mul_of_nonneg_left hsum hW0.le)
    _ = ((sz.size n : ℕ) : ℝ) * ((ν * Λ + Wm) * (2 * (Λ * Λ)) + Λ * Λ * ρ) + CK * Λ * ρ := by
        rw [hsize', hΛdef]
        field_simp
    _ ≤ ((sz.size n : ℕ) : ℝ) * ((((sz.size n : ℕ) : ℝ) * Real.sqrt ρ * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) + Wm) *
          (2 * (((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ((2 / κ) * ((sz.size n : ℕ) : ℝ)))) +
          ((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ρ) + CK * ((2 / κ) * ((sz.size n : ℕ) : ℝ)) * ρ := by
        gcongr
    _ = (2 * (2 / κ) ^ 3) * (((sz.size n : ℕ) : ℝ) ^ 5 * Real.sqrt ρ) + ((2 / κ) ^ 2 * ((sz.size n : ℕ) : ℝ) ^ 3 + CK * (2 / κ) * ((sz.size n : ℕ) : ℝ)) * ρ +
          (2 * (2 / κ) ^ 2) * (((sz.size n : ℕ) : ℝ) ^ 3 * Wm) := by ring
    _ ≤ (2 * (2 / κ) ^ 3) * (((sz.size n : ℕ) : ℝ) ^ 8 * Real.sqrt ρ) + ((2 / κ) ^ 2 + CK * (2 / κ)) * (((sz.size n : ℕ) : ℝ) ^ 8 * ρ) +
          (2 * (2 / κ) ^ 2) * (((sz.size n : ℕ) : ℝ) ^ 8 * Wm) := by
        have h1 : ((sz.size n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := by
          calc ((sz.size n : ℕ) : ℝ) = ((sz.size n : ℕ) : ℝ) ^ 1 := (pow_one _).symm
            _ ≤ _ := pow_le_pow_right₀ hNN (by norm_num)
        have h3 : ((sz.size n : ℕ) : ℝ) ^ 3 ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := pow_le_pow_right₀ hNN (by norm_num)
        have h5 : ((sz.size n : ℕ) : ℝ) ^ 5 ≤ ((sz.size n : ℕ) : ℝ) ^ 8 := pow_le_pow_right₀ hNN (by norm_num)
        have hc0 : 0 ≤ (2 / κ) ^ 2 := by positivity
        have hc1 : 0 ≤ CK * (2 / κ) := by positivity
        have ha : 0 ≤ 2 * (2 / κ) ^ 3 := by positivity
        have hb' : 0 ≤ 2 * (2 / κ) ^ 2 := by positivity
        have e1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h5 hsq) ha
        have e2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hρ0) hc0
        have e3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hρ0) hc1
        have e4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hWm0) hb'
        linarith

/-- `|M(σ)_{ab}| = |M^{(B)}_{ab}|` (a copy of the private `TwistPins_norm_sigma`, `BA/TwistPins.lean:517`). -/
private theorem TwistKer2_norm_sigma {L : ℕ} [NeZero L] (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

/-- `|M(σ)_{ab}| ≤ 1` (a copy of the private `TwistPins_M_le_one`, `BA/TwistPins.lean:526`). -/
private theorem TwistKer2_M_le_one {L : ℕ} [NeZero L] {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤ 1 := by
  rw [TwistKer2_norm_sigma]
  have hrow := BAMB_row_sq_real d L g E m hr.1 x
  have hle : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAMB d L g (E : ℂ) m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m x y)]

/-- **A crude deterministic bound of `K̃`, every `n`**: `|K̃| ≤ W^{-d} Σ_{a'} |Θ(a,a')| ≤ (1-v)⁻¹ ≤ η⁻¹` (`EKPins_norm_Theta_le`, `|M| ≤ 1`). -/
private theorem TwistKer2_twK_crude (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hvT : v ≤ BAflowT0 sz z n)
    (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) : ‖twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ ((baFMz sz z).eta n v)⁻¹ := by
  have hu1 : v < 1 := hvT.trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hm := EMn2BA_mF_data sz hflow n
  rw [twK_ba z n hr.1.1 v σ a c₁ c₂, norm_mul, TwistKer2_norm_winv n]
  have hΘ := EKPins_norm_Theta_le hr hv0 hu1 (σ 0) (σ 1)
  have hrow := sum_norm_row_le (BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1)) a
  have hsum : ‖∑ a', BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) a a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a' *
      BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖ ≤ (1 - v)⁻¹ := by
    refine (norm_sum_le _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun a' _ => ?_) (hrow.trans hΘ)
    rw [norm_mul, norm_mul]
    have h0 := TwistKer2_M_le_one hr (σ 0) c₂ a'
    have h1 := TwistKer2_M_le_one hr (σ 1) a' c₁
    calc ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) a a'‖ *
          ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 0) c₂ a'‖ *
          ‖BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (σ 1) a' c₁‖
        ≤ ‖BATheta d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) v (σ 0) (σ 1) a a'‖ * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h0 (norm_nonneg _)) h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hW1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := by
    have : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    exact inv_le_one_of_one_le₀ (one_le_pow₀ this)
  have h1v : 0 < 1 - v := by linarith
  have hη' : (1 - v)⁻¹ ≤ ((baFMz sz z).eta n v)⁻¹ := by
    refine inv_anti₀ hη ?_
    rw [TwistKer2_eta_eq]
    nlinarith [hm.2]
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖_‖ ≤ 1 * (1 - v)⁻¹ := mul_le_mul hW1 hsum (norm_nonneg _) zero_le_one
    _ ≤ _ := by rw [one_mul]; exact hη'

/-- **`‖Z‖ ≤ 2 η⁻²`, every `n`**: `Z = L̃ - K̃`, `|L̃| ≤ η⁻²` (`TwistKer_twL2_bounds`), `|K̃| ≤ η⁻¹` (`TwistKer2_twK_crude`). -/
private theorem TwistKer2_Z_crude (hκ : 0 < κ) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {v : ℝ} (hv0 : 0 ≤ v) (hvT : v ≤ BAflowT0 sz z n)
    (ω : sz.SeqΩ) (σ : Fin 2 → Bool) (a c₁ c₂ : Zd d (sz.L n)) :
    ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂ - twK (baFMz sz z) n v σ a c₁ c₂‖ ≤ 2 * (((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹) := by
  obtain ⟨hGc, hLc, hzc⟩ := TwistKer2_carrier sz z n v ω
  have hH := TwistKer2_hermitian sz z n v ω
  obtain ⟨hη, hη1⟩ := TwistKer2_eta_pos hκ hflow n hv0 hvT
  have hz : 0 < (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v).im := by rw [hzc]; exact hη
  have hbd : ∀ (τ : Bool) (y x : Idx d (sz.L n) (sz.W n)), ‖Gres (sz.seqHflowBA (BAflowLam0 sz z) n v ω)
      (ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) v) τ y x‖ ≤ ((baFMz sz z).eta n v)⁻¹ := fun τ y x => by
    have := TwistKer_entry_le hH hz τ y x
    rwa [hzc] at this
  have hΛ0 : 0 ≤ ((baFMz sz z).eta n v)⁻¹ := inv_nonneg.2 hη.le
  have h1 := (TwistKer_twL2_bounds n (baFMz sz z) hH v ω hGc σ a c₁ c₂ hΛ0 hbd (X := 0) (ν := ((baFMz sz z).eta n v)⁻¹)
    (fun τ y x _ => hbd τ y x)).1
  have h2 := TwistKer2_twK_crude hκ hflow n hv0 hvT σ a c₁ c₂
  have hΛ1 : 1 ≤ ((baFMz sz z).eta n v)⁻¹ := (one_le_inv₀ hη).2 hη1
  calc _ ≤ ‖twL2' (baFMz sz z) n v ω σ a c₁ c₂‖ + ‖twK (baFMz sz z) n v σ a c₁ c₂‖ := norm_sub_le _ _
    _ ≤ ((baFMz sz z).eta n v)⁻¹ * ((baFMz sz z).eta n v)⁻¹ + ((baFMz sz z).eta n v)⁻¹ := add_le_add h1 h2
    _ ≤ _ := by nlinarith

/-- `B_{v,0}^γ ≥ N^{-2}` for `γ ∈ [1,2]`, `0 ≤ v < 1` (`B ≥ N⁻¹`, `B^γ ≥ min (1, B²)`). -/
private theorem TwistKer2_Bctl_rpow_ge (n : ℕ) {v γ : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 2) :
    (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ ≤ sz.Bctl n v ^ γ := by
  have hB := TwistKer2_Bctl_ge_inv sz n hv0 hv1
  have hBpos : 0 < sz.Bctl n v := st_Bctl_pos sz hv1
  have hNN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : 0 < ((sz.size n : ℕ) : ℝ) := by linarith
  have hsq : (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ ≤ sz.Bctl n v ^ 2 := by
    have := pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hB 2
    rwa [inv_pow] at this
  by_cases hB1 : 1 ≤ sz.Bctl n v
  · calc (((sz.size n : ℕ) : ℝ) ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hNN)
      _ ≤ sz.Bctl n v ^ γ := Real.one_le_rpow hB1 (by linarith)
  · push Not at hB1
    refine hsq.trans ?_
    have := Real.rpow_le_rpow_of_exponent_ge hBpos hB1.le hγ2
    simpa [Real.rpow_two] using this

end Items5

/-- **T.11 (v)** (`TP:147`): the decay `|·| ≤ W^{-D}` for `|a - c₁| ≥ 3 W^ε ℓ_v` of `B̃₁`, `B̃₂`, `Ẽ^{G̊}`, `Z = L̃ - K̃` and `(Ẽ⊗Ẽ)(·, b')` (every second index `b'`), for every regime `R`:
the entry decay of `G` from the 2-loop decay (`twSteps`, fourth conjunct at `k = 2`) and the decay of `K̃` (`baTwKDecay_holds`), against deterministic polynomial bounds
(`‖G‖ ≤ η⁻¹`, `η⁻¹ ≤ (2/κ) N`, `W ≥ N^𝔠`). -/
theorem baTwistSrc5_holds (d : ℕ) (R : ∀ {d : ℕ}, Sizes d → (ℕ → ℝ) → (ℕ → ℝ) → Prop) : BATwistSrc5 d R := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs hst htT hR hcon hsteps
  exact ⟨TwistKer2_decB1 hd hκ hε h𝔡 hflow hs htT hsteps, TwistKer2_decB2 hd hκ hε h𝔡 hflow hs htT hsteps,
    TwistKer2_decEG hκ hε hflow hs htT hsteps, TwistKer2_decZ hd hκ hε h𝔡 hflow hs htT hsteps,
    fun b' => TwistKer2_decEE hκ hε hflow hs htT hsteps b'⟩

end Src5

/-! ## 8. The instances (`d = 3`, `sz0`: `L = 4(n+1)`, `W = (2(n+1))^5`, `λ = (2(n+1))^{-6}`, `flow_sz0`; `s ≡ 1/2 < t ≡ 2/3 ≤ BAflowT0`, regime `STAny`).  `twSteps` is the hypothesis (other gates' pins). -/

section Inst
open RBM.BA.FlowPinsInst RBM.Gauss.SizesInst RBM.BA.MFixedPointInst
local notation "μ0" => Sizes.seqP (sz0.withLam 0)

/-- Every deterministic hypothesis of a `BATwFrame` statement at `(κ, ε, 𝔡, 𝔠) = (1/2, 1/10, 1/10, 1/6)`, `sz0`, `s ≡ 1/2`, `t ≡ 2/3`, regime `STAny`
(a stem copy of the private `TwistPins_frame_inst`, `BA/TwistPins.lean:766`). -/
private theorem TwistKer2_frame_inst {Q : ∀ sz : Sizes 3, FlowFM sz → Measure sz.SeqΩ → (ℕ → ℝ) → (ℕ → ℝ) → Prop} (h : BATwFrame 3 STAny Q) {Cd : ℝ}
    (hC : 0 < Cd) (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd) :
    Q sz0 (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) := by
  obtain ⟨c, hc, -, H⟩ := h le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) Cd hC
  exact H (1 / 6) sz0 zSeq flow_sz0 _ _ (fun _ => by norm_num) (fun _ => by norm_num) (fun n => t0_sz0 n) trivial
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (by norm_num) (by norm_num) hc) hS

variable {Cd : ℝ} (hC : 0 < Cd) (hS : twSteps (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) Cd)
include hC hS

/-- T.11 (i): `B̃₁ ≺ η⁻¹ (W^{-d}B)²`. -/
example : twSrc (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twB1 (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2 :=
  TwistKer2_frame_inst (baTwistSrc1_holds 3 STAny) hC hS
/-- T.11 (ii): `Ẽ^{G̊} ≺ η⁻¹ (W^{-d}B)²`. -/
example : twSrc (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twEG (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) (fun _ _ => 1) 2 :=
  TwistKer2_frame_inst (baTwistSrc2_holds 3 STAny) hC hS
/-- T.11 (iv) with its a priori hypothesis discharged: for every `γ ∈ [1,2]` the family `Ξ_n = 32 N_n⁴ ≥ 1` satisfies `‖Z_v‖ ≤ Ξ B^γ` for all `n`, `ω`,
`v ∈ [1/2, 2/3]`, `σ`, `a`, `c₁`, `c₂` (`‖Z‖ ≤ 2 η⁻²`, `η⁻¹ ≤ 4N`, `B^γ ≥ N^{-2}`), and `B̃₂ ≺ Ξ η⁻¹ (W^{-d}B)^{γ+1/6}`. -/
example (γ : ℝ) (hγ1 : 1 ≤ γ) (hγ2 : γ ≤ 2) : ∃ Ξ : ℕ → sz0.SeqΩ → ℝ, (∀ n ω, 1 ≤ Ξ n ω) ∧
    (∀ n ω (v : ℝ) σ a c₁ c₂, 1 / 2 ≤ v → v ≤ 2 / 3 → ‖twL2' (baFMz sz0 zSeq) n v ω σ a c₁ c₂ - twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖ ≤
      Ξ n ω * sz0.Bctl n v ^ γ) ∧
    twSrc (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) Ξ (γ + 1 / 6) := by
  have hΞ : ∀ n (ω : sz0.SeqΩ), 1 ≤ 32 * ((sz0.size n : ℕ) : ℝ) ^ 4 := fun n ω => by
    have : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast sz0.one_le_size n
    nlinarith [one_le_pow₀ (n := 4) this]
  have hZ : ∀ n (ω : sz0.SeqΩ) (v : ℝ) σ a c₁ c₂, 1 / 2 ≤ v → v ≤ 2 / 3 → ‖twL2' (baFMz sz0 zSeq) n v ω σ a c₁ c₂ - twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖ ≤
      (32 * ((sz0.size n : ℕ) : ℝ) ^ 4) * sz0.Bctl n v ^ γ := by
    intro n ω v σ a c₁ c₂ hv1 hv2
    have hv0 : 0 ≤ v := by linarith
    have hvT : v ≤ BAflowT0 sz0 zSeq n := hv2.trans (t0_sz0 n)
    have hv1' : v < 1 := by linarith
    have h1 := TwistKer2_Z_crude (by norm_num : (0 : ℝ) < 1 / 2) flow_sz0 n hv0 hvT ω σ a c₁ c₂
    have h2 := TwistKer2_eta_inv_le (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 10) flow_sz0 n hv0 hvT
    have h3 := TwistKer2_Bctl_rpow_ge (sz := sz0) n hv0 hv1' hγ1 hγ2
    have hNN : (1 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by exact_mod_cast sz0.one_le_size n
    have hη0 : 0 ≤ ((baFMz sz0 zSeq).eta n v)⁻¹ := by
      have := (TwistKer2_eta_pos (by norm_num : (0 : ℝ) < 1 / 2) flow_sz0 n hv0 hvT).1
      positivity
    have h2' : ((baFMz sz0 zSeq).eta n v)⁻¹ ≤ 4 * ((sz0.size n : ℕ) : ℝ) := by linarith
    calc _ ≤ 2 * (((baFMz sz0 zSeq).eta n v)⁻¹ * ((baFMz sz0 zSeq).eta n v)⁻¹) := h1
      _ ≤ 2 * ((4 * ((sz0.size n : ℕ) : ℝ)) * (4 * ((sz0.size n : ℕ) : ℝ))) := by gcongr
      _ = (32 * ((sz0.size n : ℕ) : ℝ) ^ 4) * (((sz0.size n : ℕ) : ℝ) ^ 2)⁻¹ := by
          have : ((sz0.size n : ℕ) : ℝ) ^ 2 ≠ 0 := by positivity
          field_simp
          norm_num
      _ ≤ (32 * ((sz0.size n : ℕ) : ℝ) ^ 4) * sz0.Bctl n v ^ γ := mul_le_mul_of_nonneg_left h3 (by positivity)
  exact ⟨fun n _ => 32 * ((sz0.size n : ℕ) : ℝ) ^ 4, hΞ, hZ,
    TwistKer2_frame_inst (baTwistSrc4_holds 3 STAny) hC hS γ hγ1 hγ2 _ hΞ hZ⟩
/-- T.11 (v): the decay of the five sources beyond `3 W^ε ℓ_v`. -/
example : twDec (sz := sz0) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twB1 (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) ∧
    twDec (sz := sz0) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twB2 (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) ∧
    twDec (sz := sz0) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twEG (baFMz sz0 zSeq) n v ω σ a c₁ c₂‖) ∧
    twDec (sz := sz0) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twL2' (baFMz sz0 zSeq) n v ω σ a c₁ c₂ - twK (baFMz sz0 zSeq) n v σ a c₁ c₂‖) ∧
    ∀ b' : ∀ n, Zd 3 (sz0.L n), twDec (sz := sz0) μ0 (fun _ => 1 / 2) (fun _ => 2 / 3) (fun n v ω σ a c₁ c₂ => ‖twEE (baFMz sz0 zSeq) n v ω σ a (b' n) c₁ c₂‖) :=
  TwistKer2_frame_inst (baTwistSrc5_holds 3 STAny) hC hS

end Inst

end RBM.BA

end
