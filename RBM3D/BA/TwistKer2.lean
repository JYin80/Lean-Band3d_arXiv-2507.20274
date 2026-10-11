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
# BA stage TL, row TL2b (T2429), part 2: the sources of the twisted Duhamel formula (T.11 (i), (ii), (iv), (v))

The statements `BATwistSrc1`, `BATwistSrc2`, `BATwistSrc4`, `BATwistSrc5` of `BA/TwistPins.lean:261-277` are proved for every regime `R`,
in the frame `BATwFrame` (Steps 1-4 on `[s,t]` as the hypothesis `twSteps`, `(con_st_ind)`), from the merged inputs and the deterministic
kernel facts of `BA/TwistKer.lean`.  Paper: `docs/tickets/T2398-TL-proofs.md` Lemma T.11 (i), (ii), (iv), (v) with T.1 (ii), (iii), T.4, T.5.

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
private theorem TwistKer2_argmax {ι : Type*} [Fintype ι] [Nonempty ι] (g : ι → ℝ) : ∃ i₀, ∀ i, g i ≤ g i₀ := by
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

end RBM.BA

end
