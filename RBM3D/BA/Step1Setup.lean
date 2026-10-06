/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.Step1Boot
import RBM3D.Induction.Continuity
import RBM3D.Induction.Step1Setup

/-!
# BA-S2b2a (T2262): the block Anderson analogue of `Induction/Step1Setup.lean` and of the
net layer of `Induction/Continuity.lean`

Ticket T2262; DECISIONS §84 (2), §86, §81 (1), §72 (4); `docs/tickets/T2256.md` "Split" (S2b2a).
Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`): Step 1 `:1987-1990` ("same as [RBSO1D,
§7.1]"), `lem_GbEXP_BA` `:1916-1946`, `(def_G0)`, `M` `:1857`, `:1891`; band source
`paper/tex/3_5_Loop_Hierarchy.tex` Step 1 `:64-66`.  Namespace `RBM.BA`.  Consumed by BA-S2b2b
(`baBootstrap'_holds`).

Ports (cited `file:line` at the merged commit): `Induction/Step1Setup.lean` at `4f186cf`
(`S1Std` `:237`, `s1_gexRHS_le` `:1015`, `s1_wl_det` `:1064`); `Induction/Continuity.lean` at
`a51b69e` (`cont_entry_diff` `:66`, `contWord` `:89`, `cont_word_norm` `:100`, `cont_word_diff`
`:119`, `cont_loopFine_eq` `:158`, `cont_loopAbs_diff` `:170`, `cont_one_add_pow_le` `:230`,
`cont_LP_zeta_ratio` `:249`, `cont_LP_low` `:286`, `cont_WL_low` `:307`, `cont_LP_eventually`
`:315`, `cont_eta_inv_le` `:346`, `cont_LP_close` `:365`, `cont_WL_close` `:438`, `gopbound`
`:527`, `step1NetLift` `:605`); `Induction/Step1.lean` at `b969625` (`s1x_continuousOn` `:372`).

* section 1: target 4 `flowFM_omegaC_mono`; target 5 `flowFM_wl_det`;
* section 2: target 1 `baS1Std` (the band standing hypotheses at the dummy energy `E ≡ 0`);
* section 3: target 2 `baG_continuousOn`;
* section 4: the resolvent moduli along the block Anderson flow and target 3 `baGopbound`;
* section 5: target 6 `baNetLift`;
* sections 6, 7: private facts for the instances; compiled nonempty instances
  (`RBM.BA.Step1SetupInst`).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Targets 4 and 5: the event `Ω_C` is monotone; the weak-law core over any carrier -/

/-- **Target 4** (`flowFM_omegaC_mono_stmt`): `Ω_{C₁} ⊆ Ω_{C₂}` for `C₁ ≤ C₂` (T2256d). -/
theorem flowFM_omegaC_mono (d : ℕ) :
    ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (t C₁ C₂ : ℝ) (ω : sz.SeqΩ), C₁ ≤ C₂ →
      C.omegaC n t C₁ ω ≤ C.omegaC n t C₂ ω := by
  intro sz C n t C₁ C₂ ω h
  unfold FlowFM.omegaC
  by_cases h1 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₁
  · have h2 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₂ := fun x y => (h1 x y).trans h
    simp [h1, h2]
  · by_cases h2 : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₂ <;> simp [h1, h2]

/-- The right side of `(GijGEX)` over a carrier is at most `2·9^d B + W^{-d}` if every `|𝓛^{(2)}_{σ,(a',b')}| ≤ B`
(the band `s1_gexRHS_le`, `Induction/Step1Setup.lean:1015`, with `Lloop sz n E u` replaced by the carrier's `C.L n u`). -/
private theorem BASetup_gexRHS_le {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (u B : ℝ) (ω : sz.SeqΩ)
    (hL : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), ‖C.L n u σ b ω‖ ≤ B)
    (a b : Zd d (sz.L n)) :
    C.gexRHS n u ω a b ≤ 2 * 9 ^ d * B + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hL (fun _ => true) (fun _ => 0))
  unfold FlowFM.gexRHS
  set Fa := Finset.univ.filter (fun a' : Zd d (sz.L n) => zdistInf d (sz.L n) (a' - a) ≤ 1)
    with hFa
  set Fb := Finset.univ.filter (fun b' : Zd d (sz.L n) => zdistInf d (sz.L n) (b' - b) ≤ 1)
    with hFb
  have hFa' : (Fa.card : ℝ) ≤ 3 ^ d := Ind.s1_near_card a
  have hFb' : (Fb.card : ℝ) ≤ 3 ^ d := Ind.s1_near_card b
  have h3d : (0 : ℝ) ≤ 3 ^ d := by positivity
  have hinner : ∀ σ : Fin 2 → Bool,
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖C.L n u σ ![a', b'] ω‖ ≤ 3 ^ d * (3 ^ d * B) := by
    intro σ
    calc ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖C.L n u σ ![a', b'] ω‖
        ≤ ∑ _a' ∈ Fa, ((3 : ℝ) ^ d * B) := Finset.sum_le_sum fun a' _ => by
          calc ∑ b' ∈ Fb, ‖C.L n u σ ![a', b'] ω‖ ≤ ∑ _b' ∈ Fb, B :=
                Finset.sum_le_sum fun b' _ => hL σ ![a', b']
            _ = Fb.card * B := by rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 3 ^ d * B := mul_le_mul_of_nonneg_right hFb' hB
      _ = Fa.card * ((3 : ℝ) ^ d * B) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 ^ d * (3 ^ d * B) := mul_le_mul_of_nonneg_right hFa' (by positivity)
  have hS : ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
      ∑ a' ∈ Fa, ∑ b' ∈ Fb, ‖C.L n u σ ![a', b'] ω‖ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
    calc _ ≤ ∑ _σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ((3 : ℝ) ^ d * (3 ^ d * B)) := Finset.sum_le_sum fun σ _ => hinner σ
      _ = (({![true, false], ![false, true]} : Finset (Fin 2 → Bool)).card : ℝ) *
          (3 ^ d * (3 ^ d * B)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * (3 ^ d * (3 ^ d * B)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast Finset.card_le_two
  have h2 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * (if zdistInf d (sz.L n) (a - b) ≤ 1 then (1 : ℝ) else 0) ≤
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; positivity
  have h9 : 2 * ((3 : ℝ) ^ d * (3 ^ d * B)) = 2 * 9 ^ d * B := by
    rw [show (9 : ℝ) = 3 * 3 by norm_num, mul_pow]; ring
  linarith

/-- **Target 5** (`flowFM_wl_det_stmt`): the weak-law core at one sample over **any** carrier, with the non-scalar `M`
(the band `s1_wl_det`, `Induction/Step1Setup.lean:1064`, with `s1_gexRHS_le` `:1015`, `s1_indMax_eq_one` `:1001`,
`s1_omegaC_eq_one` `:988`): the threshold `2` of the band event is the hypothesis `‖G‖_max ≤ C₀`, the off-diagonal
input is on `(G - M)_{xy}` (`BAGijGEX`, T2256 P2), the constant `2·9^d + 1` is the band's. -/
theorem flowFM_wl_det (d : ℕ) :
    ∀ (sz : Sizes d) (C : FlowFM sz) (n : ℕ) (ω : sz.SeqΩ) (u a c' g Nτ C₀ : ℝ), 0 < c' →
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ 2 * a) →
      2 * a ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') → 1 ≤ Nτ → 0 ≤ g → (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ g →
      (∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n u ω x y‖ ≤ C₀) →
      (∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), C.omegaC n u C₀ ω * ‖C.L n u σ b ω‖ ≤ Nτ * g) →
      (∀ p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
        C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1 p.2‖ ^ 2 ≤
          Nτ * STmaxLoop2g C n u ω) →
      (∀ p : {p : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // p.1 ≠ p.2},
        C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω * ‖C.GM n u ω p.1.1 p.1.2‖ ^ 2 ≤
          Nτ * C.gexRHS n u ω (STblk sz n p.1.1) (STblk sz n p.1.2)) →
      ∀ i j : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω i j‖ ^ 2 ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by
  intro sz C n ω u a c' g Nτ C₀ hc' hx hΩ hNτ hg hWg hG hLoop hii hij
  have hom : C.indMax n u (((sz.W n : ℕ) : ℝ) ^ (-c')) ω = 1 := by
    unfold FlowFM.indMax
    have hall : ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.GM n u ω x y‖ ≤ ((sz.W n : ℕ) : ℝ) ^ (-c') :=
      fun x y => (hx x y).trans hΩ
    simp [hall]
  have hom2 : C.omegaC n u C₀ ω = 1 := by
    unfold FlowFM.omegaC
    simp [hG]
  have hLoop' : ∀ (σ : Fin 2 → Bool) (b : Fin 2 → Zd d (sz.L n)), ‖C.L n u σ b ω‖ ≤ Nτ * g :=
    fun σ b => by
      have := hLoop σ b
      rwa [hom2, one_mul] at this
  have hB : 0 ≤ Nτ * g := mul_nonneg (by linarith) hg
  have hmax : STmaxLoop2g C n u ω ≤ Nτ * g :=
    Finset.sup'_le _ _ fun p _ => hLoop' _ _
  have hgle : g ≤ Nτ * g := by nlinarith
  intro i j
  by_cases hij' : i = j
  · subst hij'
    have h1 := hii (i, i)
    rw [hom, one_mul] at h1
    have h2 : Nτ * STmaxLoop2g C n u ω ≤ Nτ * (Nτ * g) :=
      mul_le_mul_of_nonneg_left hmax (by linarith)
    have h3 : 0 ≤ Nτ ^ 2 * g := mul_nonneg (sq_nonneg _) hg
    have h9 : (0 : ℝ) ≤ 9 ^ d := by positivity
    have h4 : Nτ * (Nτ * g) ≤ (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by
      nlinarith [mul_nonneg h9 h3]
    simp only at h1
    linarith
  · have h1 := hij ⟨(i, j), hij'⟩
    rw [hom, one_mul] at h1
    simp only at h1
    have h2 := BASetup_gexRHS_le C n u (Nτ * g) ω hLoop' (STblk sz n i) (STblk sz n j)
    have h3 : Nτ * C.gexRHS n u ω (STblk sz n i) (STblk sz n j) ≤
        Nτ * (2 * 9 ^ d * (Nτ * g) + Nτ * g) :=
      mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by linarith)
    have e : Nτ * (2 * 9 ^ d * (Nτ * g) + Nτ * g) = (2 * 9 ^ d + 1) * Nτ ^ 2 * g := by ring
    linarith

/-! ## 2. Target 1: the standing hypotheses `S1Std` along a block Anderson window (dummy energy) -/

section Std

/-- `Im m(z, g) ≤ 1` for `Im z ≥ 0` (`BAself_norm_le_one` when `(self_m)` has a solution, `m = 0` otherwise). -/
private theorem BASetup_BAm_im_le_one (d L : ℕ) [NeZero L] (g : ℝ) (z : ℂ) (hz : 0 ≤ z.im) :
    (BAm d L g z).im ≤ 1 := by
  by_cases h : ∃ m, BASelf d L g z m
  · have hs := BAm_spec h
    exact (Complex.im_le_norm _).trans (BAself_norm_le_one d L g z _ hz hs)
  · have h0 : BAm d L g z = 0 := by
      unfold BAm
      simp [h]
    rw [h0]
    simp

/-- **Target 1** (`baS1Std_stmt`): the band standing hypotheses `S1Std` (`Induction/Step1Setup.lean:237`) at the **dummy
energy** `E ≡ 0` and the bulk constant `min κ 1` hold along a block Anderson window `0 ≤ s ≤ t ≤ t₀(z)`.  The only
energy field of `S1Std` is `hE : |E n| ≤ 2 - κ'`, which reads `0 ≤ 2 - min κ 1` at `E ≡ 0`; no scale fact
(`s1_F3`-`s1_F8`, `s1_B_pos`, `s1_hsize`, `s1_Wd_le_Bctl`, ...) reads it.  `τ = ε/2`:
`1 - t ≥ 1 - t₀ = Im z/(Im m + Im z) ≥ Im z/2 ≥ N^{-1+ε}/2 ≥ N^{-1+ε/2}` eventually (`Im m ≤ |m| ≤ 1`,
`BAm_spec`, `BAself_norm_le_one`). -/
theorem baS1Std (d : ℕ) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ 𝔠d : ℝ, 0 < 𝔠d → 𝔠d ≤ 1 / 100 →
        ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
          ∀ s t : ℕ → ℝ, (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
            STConStInd sz 𝔠d s t →
            RBM.Ind.S1Std sz (min κ 1) 𝔠 𝔡 (ε / 2) 𝔠d (fun _ => 0) s t := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠d h𝔠d h𝔠d' 𝔠 sz z hflow s t hs0 hst htT hC
  have hA := hflow.1
  have hN0 : ∀ n, (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.one_le_size n
  have hT1 : ∀ n, BAflowT0 sz z n < 1 := fun n => (BAflow_T0_bounds hκ hflow n).2.2.2
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (hT1 n)
  refine ⟨lt_min hκ one_pos, fun n => ?_, hA.1, hA.2.1, half_pos hε, h𝔠d, h𝔠d', hs0, hst, ht1,
    hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2, hC, ?_⟩
  · simp only [abs_zero]
    have := min_le_right κ 1
    linarith
  · have hN := sz.tendsto_size hA.2.2.1
    filter_upwards [hN.eventually (eventually_le_rpow 2 (half_pos hε))] with n hn
    obtain ⟨-, hz1, hz2⟩ := hflow.2 n
    obtain ⟨hzpos, hmpos, -, -⟩ := BAflow_T0_bounds hκ hflow n
    have hm1 := BASetup_BAm_im_le_one d (sz.L n) (sz.lam n) (z n) hzpos.le
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    have hNpos : 0 < N := hN0 n
    have hsplit : N ^ (-1 + ε) = N ^ (-1 + ε / 2) * N ^ (ε / 2) := by
      rw [← Real.rpow_add hNpos]
      congr 1
      ring
    have hpos : 0 ≤ N ^ (-1 + ε / 2) := Real.rpow_nonneg hNpos.le _
    have h5 : N ^ (-1 + ε / 2) * 2 ≤ N ^ (-1 + ε) := by
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hn hpos
    set m : ℝ := (BAm d (sz.L n) (sz.lam n) (z n)).im with hmdef
    set zi : ℝ := (z n).im with hzidef
    have hT : BAflowT0 sz z n = m / (m + zi) := rfl
    have hden : 0 < m + zi := by linarith
    have h1t : zi / 2 ≤ 1 - BAflowT0 sz z n := by
      rw [hT, show 1 - m / (m + zi) = zi / (m + zi) by field_simp; ring, le_div_iff₀ hden]
      nlinarith
    change N ^ (-1 + ε / 2) ≤ 1 - t n
    linarith [htT n]

end Std

/-! ## 3. Target 2: time continuity of `v ↦ (G_v - M)_{xy}` -/

section Cont

variable {d : ℕ}

/-- The flow matrix `H_u = g₀ Ψ + √u X` is Hermitian (`g₀` real). -/
private theorem BASetup_herm (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ) :
    (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ (Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω)
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- `u ↦ H_u(ω)` is continuous (entrywise `g₀ Ψ_{ij} + √u X_{ij}`). -/
private theorem BASetup_continuous_H (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) :
    Continuous fun v : ℝ => sz.seqHflowBA lam0 n v ω := by
  refine continuous_matrix fun i j => ?_
  unfold Sizes.seqHflowBA
  simp only [Matrix.add_apply, Matrix.of_apply]
  exact continuous_const.add (Sizes.continuous_seqHflow_entry_time (sz.withLam 0) n ω i j)

/-- **Target 2** (`baG_continuousOn_stmt`): `v ↦ (G_v - M)_{xy}` of the block Anderson carrier is continuous on
`[a, b]`, `b < 1`, for every sample (the band `s1x_continuousOn`, `Induction/Step1.lean:372`: `continuous_green_of_isHermitian_moving`
for the clamped path `z(min(v, b))`; `Im z_v = (1 - v) Im m > 0`, `H_v = g₀ Ψ + √v X` Hermitian). -/
theorem baG_continuousOn (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ), 0 < (BAmF sz lam0 E n).im →
      ∀ a b : ℝ, b < 1 → ∀ (ω : sz.SeqΩ) (x y : Idx d (sz.L n) (sz.W n)),
        ContinuousOn (fun v : ℝ => (baFM sz lam0 E).GM n v ω x y) (Set.Icc a b) := by
  intro sz lam0 E n hm a b hb ω x y
  set z : ℝ → ℂ := fun v => ztOf (BAmF sz lam0 E n) (E n) (min v b) with hz
  have hzc : Continuous z := by
    simp only [hz, ztOf]
    exact continuous_const.add ((continuous_const.sub
      (Complex.continuous_ofReal.comp (continuous_id.min continuous_const))).mul continuous_const)
  have hzi : ∀ v, (z v).im ≠ 0 := by
    intro v
    simp only [hz, ztOf_im, etaOf]
    have : 0 < 1 - min v b := by
      have := min_le_right v b
      linarith
    exact (mul_pos this hm).ne'
  have hcont := continuous_green_of_isHermitian_moving (BASetup_continuous_H sz lam0 n ω)
    (fun v => BASetup_herm sz lam0 n v ω) hzc hzi
  have hfun : Continuous fun v : ℝ =>
      Gres (sz.seqHflowBA lam0 n v ω) (z v) true x y - BAMfine sz lam0 E n x y :=
    (hcont.matrix_elem x y).sub continuous_const
  refine hfun.continuousOn.congr fun v hv => ?_
  change BAGt sz lam0 E n v ω x y - BAMfine sz lam0 E n x y = _
  simp only [BAGt, hz, min_eq_left hv.2]

end Cont

/-! ## 4. The resolvent moduli along the block Anderson flow and target 3 -/

section Moduli

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- **The entry modulus of the resolvent** (the band `cont_entry_diff`, `Induction/Continuity.lean:66`, for two arbitrary
Hermitian matrices with `H - H' = c X`): `‖X‖ ≤ Xb`, `|c| ≤ √Δ`, `Δ ≤ 1`, `η ≤ |Im z|, |Im z'|`, `η⁻¹ ≤ Q`,
`‖z - z'‖ ≤ Δ` give `‖(G(H, z) - G(H', z'))_{ij}‖ ≤ Q² (Xb + 1) √Δ`. -/
private theorem BASetup_entry_diff {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' X : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X) {Xb Δ : ℝ}
    (hX : ‖X‖ ≤ Xb) (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) {z z' : ℂ} {η Q : ℝ}
    (hη : 0 < η) (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|) (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ)
    (i j : ι) :
    ‖Gres H z true i j - Gres H' z' true i j‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
  have hG := cont_green_flow_diff hH hH' hd hX hc hΔ0 hΔ1 hη hQ hz hz' hzz
  have hent := norm_matrix_entry_le_opNorm (green H z - green H' z') i j
  have h3 : (green H z - green H' z') i j = Gres H z true i j - Gres H' z' true i j := by
    rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]
    rfl
  rw [h3] at hent
  exact hent.trans hG

/-- `H_u - H_{u'} = (√u - √u') X` for the block Anderson flow: the deterministic part `g₀ Ψ` cancels. -/
private theorem BASetup_H_sub (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u u' : ℝ) (ω : sz.SeqΩ) :
    sz.seqHflowBA lam0 n u ω - sz.seqHflowBA lam0 n u' ω =
      ((Real.sqrt u - Real.sqrt u' : ℝ) : ℂ) • sz.seqXmat n ω := by
  ext i j
  have h1 : ∀ v : ℝ, sz.seqHflowBA lam0 n v ω i j =
      (lam0 n : ℂ) * PsiI d (sz.L n) (sz.W n) i j + (Real.sqrt v : ℂ) * sz.seqXmat n ω i j := fun v => rfl
  rw [Matrix.sub_apply, h1, h1, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `‖z_u - z_{u'}‖ ≤ |u - u'|` for `z_u = E + (1 - u) m`, `|m| ≤ 1`. -/
private theorem BASetup_zdiff (m : ℂ) (E u u' : ℝ) (hm : ‖m‖ ≤ 1) :
    ‖ztOf m E u - ztOf m E u'‖ ≤ |u - u'| := by
  have h : ztOf m E u - ztOf m E u' = ((u' - u : ℝ) : ℂ) * m := by
    unfold ztOf
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact mul_le_of_le_one_right (abs_nonneg _) hm

/-- `η_t ≤ |Im z_u|` for `u ≤ t < 1` and `Im m ≥ 0` (`Im z_u = (1 - u) Im m`; the band `cont_eta_le_abs_im`,
`Induction/ContinuityNet.lean:618`). -/
private theorem BASetup_eta_le (m : ℂ) (E : ℝ) {t u : ℝ} (hm : 0 ≤ m.im) (ht : t < 1) (hut : u ≤ t) :
    etaOf m t ≤ |(ztOf m E u).im| := by
  rw [ztOf_im, etaOf, etaOf, abs_of_nonneg (mul_nonneg (by linarith) hm)]
  exact mul_le_mul_of_nonneg_right (by linarith) hm

/-- **Target 3** (`baGopbound_stmt`): the time-Lipschitz bound of `BAGt` w.h.p. under the block Anderson law (the block
Anderson form of `GopboundPin`, `Induction/ContinuityNet.lean:55`; the band `gopbound`, `Induction/Continuity.lean:527`).
`C' = 2C + 10`.  On the good event `‖X‖ ≤ 2N²` (`contGood (sz.withLam 0)`), `H_u - H_{u'} = (√u - √u') X`, `z_u - z_{u'}
= (u' - u) m`, `‖G_u‖ ≤ ((1 - u) Im m)⁻¹ ≤ N/κ` for `u ≤ 1 - N⁻¹`, so
`‖G_u - G_{u'}‖_max ≤ (N/κ)² (2N² + 1) |u-u'|^{1/2} ≤ 3 κ⁻² N⁴ N^{-C'/2} = 3 κ⁻² N^{-1} N^{-C} ≤ N^{-C}` once `N ≥ 3 κ⁻²`. -/
theorem baGopbound (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ : ℝ), 0 < κ → (∀ n, κ ≤ (BAmF sz lam0 E n).im) →
      (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → sz.SizeTendsto →
      ∀ C > (0 : ℝ), ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
        Sizes.seqP (sz.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
            u ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz.size n : ℕ) : ℝ)⁻¹ ∧
            |u - u'| ≤ ((sz.size n : ℕ) : ℝ) ^ (-C') ∧
            ∃ x y : Idx d (sz.L n) (sz.W n),
              ((sz.size n : ℕ) : ℝ) ^ (-C) < ‖BAGt sz lam0 E n u ω x y - BAGt sz lam0 E n u' ω x y‖} ≤
          ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  intro sz lam0 E κ hκ hmκ hm1 hsize C hC
  refine ⟨2 * C + 10, by linarith, fun D hD => ?_⟩
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  filter_upwards [hcast.eventually_ge_atTop (max 3 (3 * (κ⁻¹) ^ 2)),
    hcast.eventually (cont_eventually_tail D)] with n hn htail
  have h3 : (3 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hn
  have hK3 : 3 * (κ⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hn
  refine le_trans (measure_mono ?_)
    ((cont_good_compl (sz.withLam 0) n).trans (ENNReal.ofReal_le_ofReal htail))
  rintro ω ⟨u, u', hu0, hu'0, hut, hu't, hΔ, i, j, hbad⟩
  by_contra hng
  have hmem : ω ∈ contGood (sz.withLam 0) n := not_not.1 hng
  have hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |ω ⟨n, c⟩| ≤ ((sz.size n : ℕ) : ℝ) := fun c => hmem c
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNi : 0 < N⁻¹ := inv_pos.2 hN0
  have hNi1 : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN1
  have hK0 : 0 < κ⁻¹ := inv_pos.2 hκ
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le (hmκ n)).le
  set η : ℝ := κ * N⁻¹ with hηdef
  have hη : 0 < η := by positivity
  have hQ : η⁻¹ ≤ N * κ⁻¹ := by
    rw [hηdef, mul_inv, inv_inv, mul_comm]
  have hz : ∀ v : ℝ, 0 ≤ v → v ≤ 1 - N⁻¹ → η ≤ |(ztOf (BAmF sz lam0 E n) (E n) v).im| := by
    intro v hv0 hv1
    rw [ztOf_im, etaOf, abs_of_nonneg (mul_nonneg (by linarith) hm0), hηdef]
    calc κ * N⁻¹ ≤ (BAmF sz lam0 E n).im * (1 - v) :=
          mul_le_mul (hmκ n) (by linarith) hNi.le hm0
      _ = (1 - v) * (BAmF sz lam0 E n).im := mul_comm _ _
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n]
  have hX : ‖sz.seqXmat n ω‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_Xmat_le (sz.slice n ω) hgood
    rw [hcardI] at h
    change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _ at h
    change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _
    linarith
  have key := BASetup_entry_diff (BASetup_herm sz lam0 n u ω) (BASetup_herm sz lam0 n u' ω)
    (BASetup_H_sub sz lam0 n u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1
    hη hQ (hz u hu0 hut) (hz u' hu'0 hu't) (BASetup_zdiff _ _ u u' (hm1 n)) i j
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(2 * C + 10) / 2) := cont_sqrt_abs_le hN0.le hΔ
  have hQ2 : (N * κ⁻¹) * (N * κ⁻¹) * (2 * N ^ 2 + 1) ≤ (3 * (κ⁻¹) ^ 2) * N ^ 4 := by
    have : N ^ 2 ≤ N ^ 4 := pow_le_pow_right₀ hN1 (by norm_num)
    have h2 : (N * κ⁻¹) * (N * κ⁻¹) * (2 * N ^ 2 + 1) = (κ⁻¹) ^ 2 * (2 * N ^ 4 + N ^ 2) := by ring
    rw [h2]
    nlinarith [sq_nonneg κ⁻¹, mul_nonneg (sq_nonneg κ⁻¹) (sub_nonneg.2 this)]
  have hexp : (3 * (κ⁻¹) ^ 2) * N ^ 4 * N ^ (-(2 * C + 10) / 2) ≤ N ^ (-C) := by
    have e1 : N ^ 4 * N ^ (-(2 * C + 10) / 2) = N ^ (-C) * N⁻¹ := by
      rw [cont_pow_mul_rpow hN0 4 _, ← Real.rpow_neg_one, ← Real.rpow_add hN0]
      congr 1
      push_cast
      ring
    have hp : 0 ≤ N ^ (-C) := Real.rpow_nonneg hN0.le _
    calc (3 * (κ⁻¹) ^ 2) * N ^ 4 * N ^ (-(2 * C + 10) / 2)
        = (3 * (κ⁻¹) ^ 2) * (N ^ 4 * N ^ (-(2 * C + 10) / 2)) := by ring
      _ = ((3 * (κ⁻¹) ^ 2) * N⁻¹) * N ^ (-C) := by rw [e1]; ring
      _ ≤ 1 * N ^ (-C) := by
          refine mul_le_mul_of_nonneg_right ?_ hp
          rw [← div_eq_mul_inv, div_le_one hN0]
          exact hK3
      _ = N ^ (-C) := one_mul _
  have hfin : ‖BAGt sz lam0 E n u ω i j - BAGt sz lam0 E n u' ω i j‖ ≤ N ^ (-C) :=
    key.trans ((mul_le_mul (hQ2.trans' le_rfl) hsq (Real.sqrt_nonneg _) (by positivity)).trans hexp)
  exact absurd hbad (not_lt.2 hfin)

end Moduli

/-! ## 5. Target 6: the net lift of the two Step 1 families of the block Anderson carrier

The band `Step1NetLift`/`step1NetLift` (`Induction/Continuity.lean:594-735`) at `baFM sz lam0 E`, law `seqP (sz.withLam 0)`;
the bulk premise `|E| ≤ 2 - κ` is replaced by `κ ≤ Im m`, `|m| ≤ 1`, and the energy-bound helpers `cont_bulk`,
`cont_eta_le_abs_im`, `cont_norm_spectralZ_sub`, `cont_eta_inv_le` by `BASetup_eta_le`, `BASetup_zdiff`,
`BASetup_eta_inv_le`.  The private scalar helpers of `Continuity.lean` §2 are copied with the prefix `BASetup_`. -/

section Words

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The resolvent word `∏ᵢ G(σᵢ) E_{aᵢ}` over a list of `(σᵢ, aᵢ)` (`Continuity.lean:89`, `contWord`). -/
private noncomputable def BASetup_word (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (l : List (Bool × Zd d L)) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1

omit [NeZero W] in
/-- `Continuity.lean:95` (`contWord_cons`). -/
private theorem BASetup_word_cons (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (p : Bool × Zd d L) (l : List (Bool × Zd d L)) :
    BASetup_word H z (p :: l) = Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l := rfl

/-- `Continuity.lean:100` (`cont_word_norm`). -/
private theorem BASetup_word_norm (hW : 1 ≤ W) {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    {z : ℂ} {Q : ℝ} (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (l : List (Bool × Zd d L)) :
    ‖BASetup_word H z l‖ ≤ Q ^ l.length := by
  have hQ0 : 0 ≤ Q := (norm_nonneg _).trans (hQ true)
  induction l with
  | nil => simp [BASetup_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [BASetup_word_cons, List.length_cons, pow_succ]
    calc ‖Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l‖
        ≤ ‖Gres H z p.1‖ * ‖Eblk d L W p.2‖ * ‖BASetup_word H z l‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ Q * 1 * Q ^ l.length :=
          mul_le_mul (mul_le_mul (hQ _) hEa (norm_nonneg _) hQ0) ih (norm_nonneg _) (by positivity)
      _ = Q ^ l.length * Q := by ring

/-- The `k`-fold telescoping of a resolvent word (`Continuity.lean:119`, `cont_word_diff`). -/
private theorem BASetup_word_diff (hW : 1 ≤ W)
    {H H' : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z z' : ℂ} {Q S : ℝ} (hQ1 : 1 ≤ Q)
    (hQ : ∀ σ, ‖Gres H z σ‖ ≤ Q) (hQ' : ∀ σ, ‖Gres H' z' σ‖ ≤ Q)
    (hS : ∀ σ, ‖Gres H z σ - Gres H' z' σ‖ ≤ S) (l : List (Bool × Zd d L)) :
    ‖BASetup_word H z l - BASetup_word H' z' l‖ ≤ (l.length : ℝ) * Q ^ l.length * S := by
  have hQ0 : 0 ≤ Q := by linarith
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS true)
  induction l with
  | nil => simp [BASetup_word]
  | cons p l ih =>
    have hEa := cont_norm_Eblk_le_one (d := d) (L := L) hW p.2
    rw [BASetup_word_cons, BASetup_word_cons]
    have key : Gres H z p.1 * Eblk d L W p.2 * BASetup_word H z l -
        Gres H' z' p.1 * Eblk d L W p.2 * BASetup_word H' z' l =
        (Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * BASetup_word H z l +
          Gres H' z' p.1 * Eblk d L W p.2 * (BASetup_word H z l - BASetup_word H' z' l) := by
      noncomm_ring
    rw [key]
    have hP := BASetup_word_norm hW hQ l
    have t1 : ‖(Gres H z p.1 - Gres H' z' p.1) * Eblk d L W p.2 * BASetup_word H z l‖ ≤
        S * 1 * Q ^ l.length := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hS _) hEa (norm_nonneg _) hS0)) hP
        (norm_nonneg _) (by positivity)
    have t2 : ‖Gres H' z' p.1 * Eblk d L W p.2 * (BASetup_word H z l - BASetup_word H' z' l)‖ ≤
        Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := by
      refine (norm_mul_le _ _).trans ?_
      exact mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul (hQ' _) hEa (norm_nonneg _) hQ0)) ih
        (norm_nonneg _) (by positivity)
    have hpos : 0 ≤ S * Q ^ l.length * (Q - 1) :=
      mul_nonneg (mul_nonneg hS0 (pow_nonneg hQ0 _)) (sub_nonneg.2 hQ1)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ S * 1 * Q ^ l.length + Q * 1 * ((l.length : ℝ) * Q ^ l.length * S) := add_le_add t1 t2
      _ ≤ (((p :: l).length : ℕ) : ℝ) * Q ^ (p :: l).length * S := by
        rw [List.length_cons, pow_succ]
        push_cast
        nlinarith [hpos]

/-- The loop `loopFine` is the trace of the word of the block matrix (`Continuity.lean:158`, `cont_loopFine_eq`). -/
private theorem BASetup_loopFine_eq (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    loopFine d L W H z σ a =
      Matrix.trace (BASetup_word (blockMat d L W H) z ((List.ofFn σ).zip (List.ofFn a))) := by
  unfold loopFine
  rw [loopM_eq_loopL]
  rfl

/-- **The modulus of a loop of length `k`** for two Hermitian matrices with `H - H' = c X` (the band `cont_loopAbs_diff`,
`Continuity.lean:170`, with `Hflow`, `zt E u` replaced by the flow matrices `H`, `H'` and spectral parameters `z`, `z'`;
the trace is bounded by `card(Vtx) · ‖·‖`). -/
private theorem BASetup_loopAbs_diff (hW : 1 ≤ W) {H H' X : Matrix (Idx d L W) (Idx d L W) ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) {c : ℝ} (hd : H - H' = (c : ℂ) • X)
    {z z' : ℂ} {η Q Xb Δ : ℝ} (hη : 0 < η) (hQ1 : 1 ≤ Q) (hQ : η⁻¹ ≤ Q) (hz : η ≤ |z.im|)
    (hz' : η ≤ |z'.im|) (hzz : ‖z - z'‖ ≤ Δ) (hc : |c| ≤ Real.sqrt Δ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hXb : ‖blockMat d L W X‖ ≤ Xb) {k : ℕ} (σ : Fin k → Bool) (a : Fin k → Zd d L) :
    |‖loopFine d L W H z σ a‖ - ‖loopFine d L W H' z' σ a‖| ≤
      (Fintype.card (Vtx d L W) : ℝ) *
        ((k : ℝ) * Q ^ k * (Q * Q * (Xb + 1) * Real.sqrt Δ)) := by
  have hHu : (blockMat d L W H).IsHermitian := hH.submatrix _
  have hHu' : (blockMat d L W H').IsHermitian := hH'.submatrix _
  have hdb : blockMat d L W H - blockMat d L W H' = (c : ℂ) • blockMat d L W X := by
    rw [← cont_blockMat_sub, hd, cont_blockMat_smul]
  have hgt := cont_green_flow_diff hHu hHu' hdb hXb hc hΔ0 hΔ1 hη hQ hz hz' hzz
  have hgf : ‖green (blockMat d L W H) ((starRingEnd ℂ) z) -
      green (blockMat d L W H') ((starRingEnd ℂ) z')‖ ≤ Q * Q * (Xb + 1) * Real.sqrt Δ := by
    refine cont_green_flow_diff hHu hHu' hdb hXb hc hΔ0 hΔ1 hη hQ ?_ ?_ ?_
    · rw [Complex.conj_im, abs_neg]; exact hz
    · rw [Complex.conj_im, abs_neg]; exact hz'
    · rw [← map_sub, Complex.norm_conj]; exact hzz
  have hS : ∀ σ : Bool, ‖Gres (blockMat d L W H) z σ - Gres (blockMat d L W H') z' σ‖ ≤
      Q * Q * (Xb + 1) * Real.sqrt Δ := by
    intro σ
    cases σ
    · rw [cont_Gres_false_eq_green, cont_Gres_false_eq_green]; exact hgf
    · rw [cont_Gres_true_eq_green, cont_Gres_true_eq_green]; exact hgt
  have hGu : ∀ σ : Bool, ‖Gres (blockMat d L W H) z σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu hη hz σ).trans hQ
  have hGu' : ∀ σ : Bool, ‖Gres (blockMat d L W H') z' σ‖ ≤ Q := fun σ =>
    (norm_Gsig_le_inv_eta hHu' hη hz' σ).trans hQ
  have hw := BASetup_word_diff hW hQ1 hGu hGu' hS ((List.ofFn σ).zip (List.ofFn a))
  have hlen : ((List.ofFn σ).zip (List.ofFn a)).length = k := by simp
  rw [hlen] at hw
  rw [BASetup_loopFine_eq, BASetup_loopFine_eq]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← Matrix.trace_sub]
  refine (norm_matrix_trace_le_card_mul _).trans ?_
  exact mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)

end Words

section Scalars

open RBM.Ind RBM.Ind.ContinuityNet

/-- `(1 + x)^m ≤ 1 + 2 m x` when `m x ≤ 1/2` (`Continuity.lean:230`, `cont_one_add_pow_le`). -/
private theorem BASetup_one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : (m : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ m ≤ 1 + 2 * m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast at hm ⊢
    have hm' : (m : ℝ) * x ≤ 1 / 2 := by nlinarith
    have h1 := ih hm'
    calc (1 + x) ^ (m + 1) = (1 + x) ^ m * (1 + x) := pow_succ _ _
      _ ≤ (1 + 2 * m * x) * (1 + x) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ 1 + 2 * ((m : ℝ) + 1) * x := by
          nlinarith [mul_nonneg hx (by linarith : (0 : ℝ) ≤ 1 - 2 * (m : ℝ) * x)]

/-- **The control of `STStep1Loop` moves by at most a factor `2` under a small time change**
(`Continuity.lean:249`, `cont_LP_zeta_ratio`). -/
private theorem BASetup_LP_zeta_ratio {s t u u' x B : ℝ} (k : ℕ) (hB : 0 ≤ B) (hsu : s ≤ u)
    (hut : u ≤ t) (hu't : u' ≤ t) (ht : t < 1) (hx0 : 0 ≤ x)
    (hx : (1 - t)⁻¹ * |u - u'| ≤ x) (hk : ((k - 1 : ℕ) : ℝ) * x ≤ 1 / 2) :
    ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1) ≤
      2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by
  have hu1 : u < 1 := lt_of_le_of_lt hut ht
  have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
  have hxu : 0 < 1 - u := by linarith
  have hxu' : 0 < 1 - u' := by linarith
  have hxs : 0 ≤ 1 - s := by linarith
  have hr0 : 0 ≤ (1 - s) / (1 - u) := div_nonneg hxs hxu.le
  have hr0' : 0 ≤ (1 - s) / (1 - u') := div_nonneg hxs hxu'.le
  have h1 := cont_inv_add_one_sub_ratio (γ := 0) le_rfl ht hu't hut
  rw [zero_add, zero_add, abs_sub_comm] at h1
  have hratio : (1 - s) / (1 - u') ≤ (1 + x) * ((1 - s) / (1 - u)) := by
    have h2 : (1 - u')⁻¹ ≤ (1 + x) * (1 - u)⁻¹ :=
      h1.trans (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hxu.le))
    calc (1 - s) / (1 - u') = (1 - s) * (1 - u')⁻¹ := div_eq_mul_inv _ _
      _ ≤ (1 - s) * ((1 + x) * (1 - u)⁻¹) := mul_le_mul_of_nonneg_left h2 hxs
      _ = (1 + x) * ((1 - s) / (1 - u)) := by rw [div_eq_mul_inv]; ring
  have hA : ((1 - s) / (1 - u')) ^ (k - 1) ≤
      (1 + x) ^ (k - 1) * ((1 - s) / (1 - u)) ^ (k - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hr0' hratio _
  have hpow : (1 + x) ^ (k - 1) ≤ 2 := by
    have := BASetup_one_add_pow_le hx0 (k - 1) hk
    nlinarith
  have hζ0 : 0 ≤ ((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1) := by positivity
  calc ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1)
      ≤ ((1 + x) ^ (k - 1) * ((1 - s) / (1 - u)) ^ (k - 1)) * B ^ (k - 1) :=
        mul_le_mul_of_nonneg_right hA (by positivity)
    _ = (1 + x) ^ (k - 1) * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by ring
    _ ≤ 2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) :=
        mul_le_mul_of_nonneg_right hpow hζ0

/-- `ε ≤ ζ` for `STStep1Loop` (`Continuity.lean:286`, `cont_LP_low`): `(1-s)/(1-u) ≥ 1` and `Bctl n s ≥ N⁻¹`. -/
private theorem BASetup_LP_low {d : ℕ} (sz : Sizes d) (n k : ℕ) {s u : ℝ} (hs0 : 0 ≤ s)
    (hsu : s ≤ u) (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤
      ((1 - s) / (1 - u)) ^ (k - 1) * (sz.Bctl n s) ^ (k - 1) := by
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hs1 : s < 1 := lt_of_le_of_lt hsu hu
  have hB := cont_inv_size_le_Bctl sz n hs0 hs1
  have hB0 : 0 ≤ ((sz.size n : ℕ) : ℝ)⁻¹ := inv_nonneg.2 (by linarith)
  have hr : 1 ≤ (1 - s) / (1 - u) := (one_le_div (by linarith)).2 (by linarith)
  have h1 : 1 ≤ ((1 - s) / (1 - u)) ^ (k - 1) := one_le_pow₀ hr
  have h2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ (k - 1) ≤ (sz.Bctl n s) ^ (k - 1) :=
    pow_le_pow_left₀ hB0 hB _
  have h3 : ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤ ((((sz.size n : ℕ) : ℝ))⁻¹) ^ (k - 1) :=
    pow_le_pow_of_le_one hB0 (inv_le_one_of_one_le₀ hN1) (Nat.sub_le k 1)
  calc ((((sz.size n : ℕ) : ℝ))⁻¹) ^ k ≤ ((((sz.size n : ℕ) : ℝ))⁻¹) ^ (k - 1) := h3
    _ ≤ (sz.Bctl n s) ^ (k - 1) := h2
    _ = 1 * (sz.Bctl n s) ^ (k - 1) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (pow_nonneg (hB0.trans hB) _)

/-- `ε ≤ ζ` for `STStep1Weak` (`Continuity.lean:307`, `cont_WL_low`). -/
private theorem BASetup_WL_low {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) :
    ((((sz.size n : ℕ) : ℝ))⁻¹) ^ ((1 : ℝ) / 4) ≤ (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
  Real.rpow_le_rpow (inv_nonneg.2 (Nat.cast_nonneg _)) (cont_inv_size_le_Bctl sz n hu0 hu)
    (by norm_num)

/-- The eventual numerical facts for a fixed loop length `k`, in `N` (exponent `A = 6k + 16`;
`Continuity.lean:315`, `cont_LP_eventually`). -/
private theorem BASetup_LP_eventually (k : ℕ) :
    ∀ᶠ N : ℝ in atTop, 1 ≤ N ∧ 6 * (k : ℝ) ≤ N ∧ (2 : ℝ) ^ k ≤ N ∧
      N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹ ∧
      N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (6 * (k : ℝ)),
    eventually_ge_atTop ((2 : ℝ) ^ k)] with N h1 h2 h3
  have hN0 : 0 < N := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hinv : N ^ (-1 : ℝ) = N⁻¹ := Real.rpow_neg_one N
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · have e : N * N ^ (-(6 * (k : ℝ) + 16)) = N ^ (1 + -(6 * (k : ℝ) + 16)) := by
      rw [Real.rpow_add hN0, Real.rpow_one]
    rw [e, ← hinv]
    exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · have e : N ^ (-(6 * (k : ℝ) + 16) / 2) = (N ^ (3 * k + 8))⁻¹ := by
      rw [show -(6 * (k : ℝ) + 16) / 2 = -((3 * k + 8 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_neg hN0.le, Real.rpow_natCast]
    have hpos : 0 < N ^ (3 * k + 8) := pow_pos hN0 _
    have hk1 : 0 < N ^ k := pow_pos hN0 k
    have e2 : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * (N ^ (3 * k + 8))⁻¹)) =
        (3 * k * N ^ (2 * k + 7)) / N ^ (3 * k + 8) := by
      field_simp
      ring
    rw [e, e2, inv_pow, ← one_div, div_le_div_iff₀ hpos hk1]
    have h5 : 3 * (k : ℝ) ≤ N := by linarith
    calc 3 * (k : ℝ) * N ^ (2 * k + 7) * N ^ k = 3 * (k : ℝ) * N ^ (3 * k + 7) := by ring
      _ ≤ N * N ^ (3 * k + 7) := mul_le_mul_of_nonneg_right h5 (pow_nonneg hN0.le _)
      _ = 1 * N ^ (3 * k + 8) := by ring

/-- `(η_t)⁻¹ ≤ N²` from `(1 - t)⁻¹ ≤ N`, `Im m ≥ κ` and `1/κ ≤ N` (`Continuity.lean:346`, `cont_eta_inv_le`, with
`c₁ ≤ Im m(E)` replaced by `κ ≤ Im m`). -/
private theorem BASetup_eta_inv_le {m : ℂ} {t N κ : ℝ} (hN0 : 0 < N) (hκ : 0 < κ) (hκm : κ ≤ m.im)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N) : (etaOf m t)⁻¹ ≤ N ^ 2 := by
  have hm : 0 < m.im := lt_of_lt_of_le hκ hκm
  have h1 : (etaOf m t)⁻¹ = (1 - t)⁻¹ * (m.im)⁻¹ := by
    unfold etaOf
    rw [mul_inv]
  have h2 : (m.im)⁻¹ ≤ N := by
    refine le_trans ?_ hNc
    rw [one_div]
    exact inv_anti₀ hκ hκm
  rw [h1, sq]
  exact mul_le_mul hN1 h2 (inv_nonneg.2 hm.le) hN0.le

end Scalars

section Close

open scoped Matrix.Norms.L2Operator

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- `‖X‖ ≤ 2N²` on the good event, for the Gaussian matrix `X` of `sz.withLam 0` at size `n`. -/
private theorem BASetup_X_norm (sz : Sizes d) (n : ℕ) (ω : sz.SeqΩ) {N : ℝ}
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N) :
    ‖sz.seqXmat n ω‖ ≤ 2 * N ^ 2 := by
  have hcardI : (Fintype.card (Idx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [sz.card_Idx n, hN]
  have h := cont_norm_Xmat_le (sz.slice n ω) hgood
  rw [hcardI] at h
  change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _ at h
  change ‖Xmat d (sz.L n) (sz.W n) (sz.slice n ω)‖ ≤ _
  linarith

/-- **The two conclusions of `hclose` for the loop family of `STStep1Loop`** at one index `n`, deterministic:
`‖𝓛_u‖ ≤ ‖𝓛_{u'}‖ + N^{-k}` and `ζ_{u'} ≤ 2 ζ_u` (the band `cont_LP_close`, `Continuity.lean:365`; `H_u = g₀ Ψ + √u X`,
`z_u = E + (1 - u) m`, `(η_t)⁻¹ ≤ N²` from `κ ≤ Im m`, `1/κ ≤ N`). -/
private theorem BASetup_LP_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N s t u u' κ B : ℝ} {k : ℕ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hB : 0 ≤ B) (hs0 : 0 ≤ s) (hsu : s ≤ u) (hut : u ≤ t) (hsu' : s ≤ u')
    (hu't : u' ≤ t) (ht : t < 1) (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im)
    (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1) (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16)))
    (g1 : 1 ≤ N) (g2 : 6 * (k : ℝ) ≤ N)
    (gA : N * N ^ (-(6 * (k : ℝ) + 16)) ≤ N⁻¹)
    (gC : N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) ≤ (N⁻¹) ^ k)
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) :
    ‖(baFM sz lam0 E).L n u σ a ω‖ ≤ ‖(baFM sz lam0 E).L n u' σ a ω‖ + (N⁻¹) ^ k ∧
      ((1 - s) / (1 - u')) ^ (k - 1) * B ^ (k - 1) ≤
        2 * (((1 - s) / (1 - u)) ^ (k - 1) * B ^ (k - 1)) := by
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hu0 : 0 ≤ u := hs0.trans hsu
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-(6 * (k : ℝ) + 16) / 2) := cont_sqrt_abs_le hN0.le hy
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos h1t (hκ.trans_le hmκ)
  have hQ1 : 1 ≤ N ^ 2 := one_le_pow₀ g1
  have hcardB : (Fintype.card (Vtx d (sz.L n) (sz.W n)) : ℝ) = N := by
    rw [card_BlockIndex, hN]
    change _ = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ)
    rw [mul_comm]
  have hXb : ‖blockMat d (sz.L n) (sz.W n) (sz.seqXmat n ω)‖ ≤ 2 * N ^ 2 := by
    have h := cont_norm_blockMat_Xmat_le (sz.slice n ω) hgood
    rw [hcardB] at h
    change ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤ _ at h
    change ‖blockMat d (sz.L n) (sz.W n) (Xmat d (sz.L n) (sz.W n) (sz.slice n ω))‖ ≤ _
    linarith
  have hloop := BASetup_loopAbs_diff (sz.W_pos n) (BASetup_herm sz lam0 n u ω)
    (BASetup_herm sz lam0 n u' ω) (BASetup_H_sub sz lam0 n u u' ω) hη hQ1 hQ
    (BASetup_eta_le _ (E n) hm0 ht hut) (BASetup_eta_le _ (E n) hm0 ht hu't)
    (BASetup_zdiff _ _ u u' hm1) (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1 hXb σ a
  rw [hcardB] at hloop
  refine ⟨?_, ?_⟩
  · have hS : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| ≤
        3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2) := by
      have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) ≤ 3 * N ^ 6 := by
        have : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ g1 (by norm_num)
        nlinarith
      exact mul_le_mul e1 hsq (Real.sqrt_nonneg _) (by positivity)
    have hbound : |‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω)
          (ztOf (BAmF sz lam0 E n) (E n) u) σ a‖ -
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u' ω)
          (ztOf (BAmF sz lam0 E n) (E n) u') σ a‖| ≤
        N * ((k : ℝ) * (N ^ 2) ^ k * (3 * N ^ 6 * N ^ (-(6 * (k : ℝ) + 16) / 2))) :=
      hloop.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hS (by positivity)) hN0.le)
    have := (abs_le.1 (hbound.trans gC)).2
    change ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u ω)
          (ztOf (BAmF sz lam0 E n) (E n) u) σ a‖ ≤
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n u' ω)
          (ztOf (BAmF sz lam0 E n) (E n) u') σ a‖ + _
    linarith
  · have hx0 : 0 ≤ N⁻¹ := inv_nonneg.2 hN0.le
    have hx1 : (1 - t)⁻¹ * |u - u'| ≤ N⁻¹ :=
      (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans gA
    have h3k : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hk : ((k - 1 : ℕ) : ℝ) * N⁻¹ ≤ 1 / 2 := by
      calc ((k - 1 : ℕ) : ℝ) * N⁻¹ ≤ k * N⁻¹ := mul_le_mul_of_nonneg_right h3k hx0
        _ ≤ (N / 6) * N⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hx0
        _ = 1 / 6 := by field_simp
        _ ≤ 1 / 2 := by norm_num
    exact BASetup_LP_zeta_ratio k hB hsu hut hu't ht hx0 hx1 hk

/-- **The two conclusions of `hclose` for the weak-law family of `STStep1Weak`** at one index `n`, deterministic:
`‖(G_u - M)_{xy}‖ ≤ ‖(G_{u'} - M)_{xy}‖ + N^{-1/4}` and `Bctl(u')^{1/4} ≤ 2 Bctl(u)^{1/4}` (the band `cont_WL_close`,
`Continuity.lean:438`; `M` is time independent, so `(G - M)` differences are `G` differences). -/
private theorem BASetup_WL_close (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {N t u u' A κ : ℝ} (hN : N = ((sz.size n : ℕ) : ℝ))
    (hu0 : 0 ≤ u) (hut : u ≤ t) (hu'0 : 0 ≤ u') (hu't : u' ≤ t) (ht : t < 1)
    (hκ : 0 < κ) (hmκ : κ ≤ (BAmF sz lam0 E n).im) (hm1 : ‖BAmF sz lam0 E n‖ ≤ 1)
    (hNc : 1 / κ ≤ N) (hN1 : (1 - t)⁻¹ ≤ N)
    (hgood : ∀ c : CoordF d (sz.L n) (sz.W n), |sz.slice n ω c| ≤ N)
    (hy : |u - u'| ≤ N ^ (-A)) (g2 : N * N ^ (-A) ≤ 1 / 10)
    (g3 : 3 * N ^ 6 * N ^ (-A / 2) ≤ (N⁻¹) ^ ((1 : ℝ) / 4)) (x y : Idx d (sz.L n) (sz.W n)) :
    ‖(baFM sz lam0 E).GM n u ω x y‖ ≤ ‖(baFM sz lam0 E).GM n u' ω x y‖ + (N⁻¹) ^ ((1 : ℝ) / 4) ∧
      (sz.Bctl n u') ^ ((1 : ℝ) / 4) ≤ 2 * (sz.Bctl n u) ^ ((1 : ℝ) / 4) := by
  have hNge : (1 : ℝ) ≤ N := by
    rw [hN]
    exact_mod_cast sz.one_le_size n
  have hN0 : 0 < N := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hΔ1 : |u - u'| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hsq : Real.sqrt |u - u'| ≤ N ^ (-A / 2) := cont_sqrt_abs_le hN0.le hy
  have hm0 : 0 ≤ (BAmF sz lam0 E n).im := (hκ.trans_le hmκ).le
  have hQ : (etaOf (BAmF sz lam0 E n) t)⁻¹ ≤ N ^ 2 := BASetup_eta_inv_le hN0 hκ hmκ hNc hN1
  have hη : 0 < etaOf (BAmF sz lam0 E n) t := by
    unfold etaOf
    exact mul_pos h1t (hκ.trans_le hmκ)
  have hX := BASetup_X_norm sz n ω hN hgood
  have hent := BASetup_entry_diff (BASetup_herm sz lam0 n u ω) (BASetup_herm sz lam0 n u' ω)
    (BASetup_H_sub sz lam0 n u u' ω) hX (cont_abs_sqrt_sub_sqrt_le hu0 hu'0) (abs_nonneg _) hΔ1 hη hQ
    (BASetup_eta_le _ (E n) hm0 ht hut) (BASetup_eta_le _ (E n) hm0 ht hu't)
    (BASetup_zdiff _ _ u u' hm1) x y
  have hs0' : 0 ≤ Real.sqrt |u - u'| := Real.sqrt_nonneg _
  have hN4 : N ^ 4 ≤ N ^ 6 := pow_le_pow_right₀ hNge (by norm_num)
  have hbound : ‖Gres (sz.seqHflowBA lam0 n u ω) (ztOf (BAmF sz lam0 E n) (E n) u) true x y -
        Gres (sz.seqHflowBA lam0 n u' ω) (ztOf (BAmF sz lam0 E n) (E n) u') true x y‖ ≤
      (N⁻¹) ^ ((1 : ℝ) / 4) := by
    refine hent.trans ?_
    have e1 : N ^ 2 * N ^ 2 * (2 * N ^ 2 + 1) * Real.sqrt |u - u'| =
        (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| := by ring
    rw [e1]
    calc (2 * N ^ 6 + N ^ 4) * Real.sqrt |u - u'| ≤ 3 * N ^ 6 * Real.sqrt |u - u'| :=
          mul_le_mul_of_nonneg_right (by linarith) hs0'
      _ ≤ 3 * N ^ 6 * N ^ (-A / 2) := mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ (N⁻¹) ^ ((1 : ℝ) / 4) := g3
  refine ⟨?_, ?_⟩
  · have hdiff : (baFM sz lam0 E).GM n u ω x y - (baFM sz lam0 E).GM n u' ω x y =
        Gres (sz.seqHflowBA lam0 n u ω) (ztOf (BAmF sz lam0 E n) (E n) u) true x y -
          Gres (sz.seqHflowBA lam0 n u' ω) (ztOf (BAmF sz lam0 E n) (E n) u') true x y := by
      change BAGt sz lam0 E n u ω x y - BAMfine sz lam0 E n x y -
        (BAGt sz lam0 E n u' ω x y - BAMfine sz lam0 E n x y) = _
      rw [sub_sub_sub_cancel_right]
      rfl
    have habs := abs_norm_sub_norm_le ((baFM sz lam0 E).GM n u ω x y) ((baFM sz lam0 E).GM n u' ω x y)
    rw [hdiff] at habs
    have := (abs_le.1 (habs.trans hbound)).2
    linarith
  · have hu1 : u < 1 := lt_of_le_of_lt hut ht
    have hu'1 : u' < 1 := lt_of_le_of_lt hu't ht
    have hBu : 0 ≤ sz.Bctl n u :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu0 hu1)
    have hBu' : 0 ≤ sz.Bctl n u' :=
      (inv_nonneg.2 (Nat.cast_nonneg _)).trans (cont_inv_size_le_Bctl sz n hu'0 hu'1)
    have hx : (1 - t)⁻¹ * |u' - u| ≤ 1 / 10 := by
      rw [abs_sub_comm]
      exact (mul_le_mul hN1 hy (abs_nonneg _) hN0.le).trans g2
    have hr := cont_Bctl_ratio sz n ht hu't hut
    have hMratio : sz.Bctl n u' ≤ (11 / 10) * sz.Bctl n u :=
      hr.trans (mul_le_mul_of_nonneg_right (by linarith) hBu)
    have h2 : (sz.Bctl n u') ^ ((1 : ℝ) / 4) ≤ ((11 / 10) * sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hBu' hMratio (by norm_num)
    rw [Real.mul_rpow (by norm_num) hBu] at h2
    have h3 : ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ 2 := by
      calc ((11 / 10 : ℝ)) ^ ((1 : ℝ) / 4) ≤ (11 / 10 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ ≤ 2 := by rw [Real.rpow_one]; norm_num
    calc (sz.Bctl n u') ^ ((1 : ℝ) / 4)
        ≤ (11 / 10 : ℝ) ^ ((1 : ℝ) / 4) * (sz.Bctl n u) ^ ((1 : ℝ) / 4) := h2
      _ ≤ 2 * (sz.Bctl n u) ^ ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hBu _)

end Close

section NetLift

open RBM.Ind RBM.Ind.ContinuityNet

variable {d : ℕ}

/-- **Target 6** (`baNetLift_stmt`): the two halves of the band `Step1NetLift`/`step1NetLift` (`Continuity.lean:594-735`)
for `baFM sz lam0 E` at the law `seqP (sz.withLam 0)`: the per-time domination (`PerTimeDomAt`) gives `STStep1LoopgL`,
`STStep1WeakgL`.  Both halves apply `cont_core` (`ContinuityNet`) on `TimeIcc s t n × V n` with the good event
`contGood (sz.withLam 0)` and the net of mesh `N^{-A-1}`; loops: `V n = (σ, a)`, `A = 6k + 16`, `#V ≤ N^{k+1}`,
`ε = N^{-k}`; weak law: `V n = Idx × Idx`, `A = 40`, `#V = N²`, `ε = N^{-1/4}`.  The bulk premise `|E| ≤ 2 - κ` of the band
is replaced by `κ ≤ Im m`, `|m| ≤ 1`. -/
theorem baNetLift (d : ℕ) :
    ∀ (sz : Sizes d) (lam0 E : ℕ → ℝ) (κ τ : ℝ) (s t : ℕ → ℝ), 0 < κ →
      (∀ n, κ ≤ (BAmF sz lam0 E n).im) → (∀ n, ‖BAmF sz lam0 E n‖ ≤ 1) → 0 < τ →
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → sz.SizeTendsto → sz.RangeCond τ t →
      ((∀ k : ℕ, 1 ≤ k →
          PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
            (U := fun n => TimeIcc s t n × (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
            (fun n p ω => ‖(baFM sz lam0 E).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
            (fun n p _ => ((1 - s n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz.Bctl n (s n)) ^ (k - 1))) →
        STStep1LoopgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) ∧
      (PerTimeDomAt (Sizes.seqP (sz.withLam 0)) sz.size
          (U := fun n => TimeIcc s t n × Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFM sz lam0 E).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
          (fun n p _ => (sz.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ)) →
        STStep1WeakgL (baFM sz lam0 E) (Sizes.seqP (sz.withLam 0)) s t) := by
  intro sz lam0 E κ τ s t hκ hmκ hm1 hτ hs0 hst ht1 hsize hRange
  have hlen : ∀ n, t n - s n ≤ 1 := fun n => by linarith [hs0 n, ht1 n]
  have hcast : Tendsto (fun n : ℕ => ((sz.size n : ℕ) : ℝ)) atTop atTop := hsize
  have hsizeN : Tendsto sz.size atTop atTop := tendsto_natCast_atTop_iff.mp hcast
  have hgoodP : HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (contGood (sz.withLam 0)) :=
    cont_highProbAt_good (sz.withLam 0) hsizeN
  have ev1 : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := hcast.eventually_ge_atTop 1
  have evc : ∀ᶠ n : ℕ in atTop, 1 / κ ≤ ((sz.size n : ℕ) : ℝ) :=
    hcast.eventually_ge_atTop _
  have evR : ∀ᶠ n : ℕ in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    filter_upwards [hRange, ev1] with n hn h1
    have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) := Real.rpow_pos_of_pos hx0 _
    have h2 := inv_anti₀ hpos hn
    rw [← Real.rpow_neg hx0.le] at h2
    refine h2.trans ?_
    calc ((sz.size n : ℕ) : ℝ) ^ (-(-1 + τ)) ≤ ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = _ := Real.rpow_one _
  have hBnn : ∀ n, 0 ≤ sz.Bctl n (s n) := fun n =>
    (inv_nonneg.2 (Nat.cast_nonneg _)).trans
      (cont_inv_size_le_Bctl sz n (hs0 n) (lt_of_le_of_lt (hst n) (ht1 n)))
  refine ⟨fun hPT => ?_, fun hPT => ?_⟩
  · -- the loop family
    intro k hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hA0 : 0 ≤ 6 * (k : ℝ) + 16 := by linarith
    have hcard : ∀ᶠ n : ℕ in atTop,
        (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ) ≤
          ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) := by
      filter_upwards [hcast.eventually (BASetup_LP_eventually k)] with n hev
      obtain ⟨g1, _, g3, -⟩ := hev
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have e : ((sz.size n : ℕ) : ℝ) ^ ((k : ℝ) + 1) =
          ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) := by
        rw [Real.rpow_add hN0, Real.rpow_natCast, Real.rpow_one]
      have hcardZ : Fintype.card (Zd d (sz.L n)) = sz.L n ^ d := by
        simp [Zd, ZMod.card]
      have hcardV : (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ) =
          (2 : ℝ) ^ k * (((sz.L n : ℕ) : ℝ) ^ d) ^ k := by
        rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_fin, hcardZ]
        push_cast
        ring
      have hW1 : (1 : ℝ) ≤ (sz.W n : ℝ) := by exact_mod_cast sz.W_pos n
      have hL0 : (0 : ℝ) ≤ (sz.L n : ℝ) := Nat.cast_nonneg _
      have hLW : (sz.L n : ℝ) ≤ (sz.W n : ℝ) * (sz.L n : ℝ) := le_mul_of_one_le_left hL0 hW1
      have eN : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℝ) * (sz.L n : ℝ)) ^ d := by
        simp [Sizes.size]
      have hLN : (sz.L n : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
        rw [eN]
        exact pow_le_pow_left₀ hL0 hLW d
      rw [e, hcardV]
      calc (2 : ℝ) ^ k * ((sz.L n : ℝ) ^ d) ^ k
          ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ k :=
            mul_le_mul g3 (pow_le_pow_left₀ (by positivity) hLN k) (by positivity) hN0.le
        _ = ((sz.size n : ℕ) : ℝ) ^ k * ((sz.size n : ℕ) : ℝ) := by ring
    refine cont_core (V := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n))) hsizeN hst hlen
      (A := 6 * (k : ℝ) + 16) (Cv := (k : ℝ) + 1) hA0 (by linarith) hcard (hPT k hk)
      hgoodP
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ k)
      (fun n => pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, σ, a⟩ := p
      exact BASetup_LP_low sz n k (hs0 n) u.2.1 (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [hcast.eventually (BASetup_LP_eventually k), evc, evR] with n hev hc hR
      obtain ⟨g1, g2, _, gA, gC⟩ := hev
      intro ω hω u u' hΔ v
      obtain ⟨σ, a⟩ := v
      exact BASetup_LP_close sz lam0 E n ω
        (N := ((sz.size n : ℕ) : ℝ)) (s := s n) (t := t n) (u := u) (u' := u')
        (B := sz.Bctl n (s n)) (κ := κ) rfl (hBnn n) (hs0 n) u.2.1 u.2.2 u'.2.1 u'.2.2
        (ht1 n) hκ (hmκ n) (hm1 n) hc hR (fun c => hω c) hΔ g1 g2 gA gC σ a
  · -- the weak law
    have evg2 : ∀ᶠ n : ℕ in atTop,
        ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤ 1 / 10 := by
      filter_upwards [cont_gap hsizeN 1 (κ := 1 / 10) (p := 1 - 40) (q := 0) (by norm_num)
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ)) =
          ((sz.size n : ℕ) : ℝ) ^ (1 - 40 : ℝ) := by
        rw [show (1 - 40 : ℝ) = 1 + -40 by ring, Real.rpow_add hx0, Real.rpow_one]
      rw [this]
      rw [Real.rpow_zero] at hn
      linarith
    have evg3 : ∀ᶠ n : ℕ in atTop,
        3 * ((sz.size n : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) ≤
          (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) := by
      filter_upwards [cont_gap hsizeN 3 (κ := 1) (p := 6 - 40 / 2) (q := -(1 / 4)) one_pos
        (by norm_num), ev1] with n hn h1
      have hx0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have e1 : 3 * ((sz.size n : ℕ) : ℝ) ^ 6 * ((sz.size n : ℕ) : ℝ) ^ (-(40 : ℝ) / 2) =
          3 * ((sz.size n : ℕ) : ℝ) ^ (6 - 40 / 2 : ℝ) := by
        rw [mul_assoc, cont_pow_mul_rpow hx0]
        congr 2
        push_cast
        ring
      have e2 : (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4) =
          ((sz.size n : ℕ) : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.inv_rpow hx0.le, Real.rpow_neg hx0.le]
      rw [e1, e2]
      linarith
    have hcard : ∀ n : ℕ,
        (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : ℝ) ≤
          ((sz.size n : ℕ) : ℝ) ^ (2 : ℝ) := by
      intro n
      rw [Fintype.card_prod, Nat.cast_mul, Real.rpow_two, sz.card_Idx n]
      ring_nf
      exact le_rfl
    refine cont_core (V := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) hsizeN
      hst hlen (A := 40) (Cv := 2) (by norm_num) (by norm_num) (Eventually.of_forall hcard) hPT
      hgoodP
      (ε := fun n => (((sz.size n : ℕ) : ℝ)⁻¹) ^ ((1 : ℝ) / 4))
      (fun n => Real.rpow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) ?_ ?_
    · -- `hlow`
      refine Eventually.of_forall fun n p ω => ?_
      obtain ⟨u, i, j⟩ := p
      exact BASetup_WL_low sz n ((hs0 n).trans u.2.1) (lt_of_le_of_lt u.2.2 (ht1 n))
    · -- `hclose`
      filter_upwards [evc, evR, evg2, evg3] with n hc hR g2 g3
      intro ω hω u u' hΔ v
      obtain ⟨i, j⟩ := v
      exact BASetup_WL_close sz lam0 E n ω (N := ((sz.size n : ℕ) : ℝ)) (t := t n) (u := u)
        (u' := u') (A := 40) (κ := κ) rfl ((hs0 n).trans u.2.1) u.2.2
        ((hs0 n).trans u'.2.1) u'.2.2 (ht1 n) hκ (hmκ n) (hm1 n) hc hR (fun c => hω c) hΔ g2 g3 i j

end NetLift

/-! ## 6. Private facts used by the instances -/

section InstHelpers

variable {d : ℕ}

/-- At `t = 0` the flow is `H_0 = g₀ Ψ` and `z_0 = E + m`, so `G_0 = M` (the copy of T2256's `Boot_GM_zero`,
`Step1Boot.lean:358`). -/
private theorem BASetup_GM_zero (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (x y : Idx d (sz.L n) (sz.W n)) : (baFM sz lam0 E).GM n 0 ω x y = 0 := by
  have hH : sz.seqHflowBA lam0 n 0 ω = ((lam0 n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) := by
    ext i j
    have h : (sz.withLam 0).seqHflow n 0 ω i j = 0 := by
      have h0 : (sz.withLam 0).seqHflow n 0 ω = 0 := by simp [Sizes.seqHflow]
      rw [h0]
      rfl
    simp [Sizes.seqHflowBA, h]
  change BAGt sz lam0 E n 0 ω x y - BAMfine sz lam0 E n x y = 0
  unfold BAGt BAMfine Mres
  rw [hH]
  have hz : ztOf (BAmF sz lam0 E n) (E n) 0 = (E n : ℂ) + BAmF sz lam0 E n := by simp [ztOf]
  rw [hz]
  simp [Gres]

/-- `|m| ≤ 1` for `m = m(E, g₀)` when `Im m > 0` (`(self_m)` has a solution, `BAm_spec`; `BAself_norm_le_one` at the real
point `z = E`). -/
private theorem BASetup_norm_BAmF_le_one (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ)
    (h : 0 < (BAmF sz lam0 E n).im) : ‖BAmF sz lam0 E n‖ ≤ 1 := by
  have hex : ∃ m, BASelf d (sz.L n) (lam0 n) (E n : ℂ) m := by
    by_contra hne
    have h0 : BAmF sz lam0 E n = 0 := by
      unfold BAmF BAm
      simp [hne]
    rw [h0] at h
    simp at h
  exact BAself_norm_le_one d (sz.L n) (lam0 n) (E n : ℂ) _ (by simp) (BAm_spec hex)

private theorem BASetup_maxLoop_nonneg {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ) :
    0 ≤ STmaxLoop2g C n t ω :=
  (norm_nonneg _).trans (Finset.le_sup'
    (fun p : Zd d (sz.L n) × Zd d (sz.L n) => ‖C.L n t ![false, true] ![p.1, p.2] ω‖)
    (Finset.mem_univ ((0 : Zd d (sz.L n)), (0 : Zd d (sz.L n)))))

private theorem BASetup_gexRHS_nonneg {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t : ℝ) (ω : sz.SeqΩ)
    (a b : Zd d (sz.L n)) : 0 ≤ C.gexRHS n t ω a b := by
  unfold FlowFM.gexRHS
  positivity

private theorem BASetup_omegaC_le_one {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) :
    C.omegaC n t C₀ ω ≤ 1 := by
  unfold FlowFM.omegaC
  split_ifs <;> norm_num

end InstHelpers

/-! ## 7. Compiled nonempty instances (`RBM.BA.Step1SetupInst`)

The size data are the merged preflight sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`;
`n = 0`: `L = 4`, `W = 32`, `N = 2097152`), the spectral parameters `zSeq`, `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq`
(`flow_sz0`), flow parameters `lam0 = BAflowLam0 sz0 zSeq`, `E = BAflowEs sz0 zSeq`, `κ = 1/2` with `Im m ≥ 1/2`
(`inst_im_m_ge`, from `mS_im_half`: no window hypothesis is needed), `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`,
`s ≡ 1/2`, `t ≡ 2/3 ≤ t₀` (`Step1BootInst.inst_BAFamZ_horizon`).  Every deterministic hypothesis is discharged.  What
stays a hypothesis: the per-time dominations `PerTimeDomAt` of `baNetLift` (the block Anderson analogue of
`STStep1LoopPT`, `STStep1WeakPT`: BA-S2b2b). -/

end RBM.BA

namespace RBM.BA.Step1SetupInst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- The constant times `s ≡ 1/2`, `t ≡ 2/3`. -/
def sI : ℕ → ℝ := fun _ => 1 / 2

def tI : ℕ → ℝ := fun _ => 2 / 3

/-- `Im m(E_n, g₀_n) ≥ 1/2` along `sz0`, `zSeq`, for every `n`: `m = m_S/√t₀` (`BAmF_sz0_eq`), `Im m_S ≥ 4/5`
(`mS_im_half`) and `0 < √t₀ ≤ 1`. -/
theorem inst_im_m_ge (n : ℕ) :
    (1 / 2 : ℝ) ≤ (BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n).im := by
  rw [BAmF_sz0_eq n]
  have h1 := mS_im_half (sz0.L n) (sz0.lam n) (sz0_lam_L n)
  obtain ⟨-, -, ht0, ht1⟩ := BAflow_T0_bounds (by norm_num : (0 : ℝ) < 1 / 2) flow_sz0 n
  have hs0 : 0 < Real.sqrt (BAflowT0 sz0 zSeq n) := Real.sqrt_pos.2 ht0
  have hs1 : Real.sqrt (BAflowT0 sz0 zSeq n) ≤ 1 := Real.sqrt_le_one.2 ht1.le
  rw [Complex.div_ofReal_im]
  calc (1 / 2 : ℝ) ≤ 4 / 5 := by norm_num
    _ ≤ (MFixedPointInst.mS (sz0.L n) (sz0.lam n)).im := h1
    _ ≤ (MFixedPointInst.mS (sz0.L n) (sz0.lam n)).im / Real.sqrt (BAflowT0 sz0 zSeq n) :=
        le_div_self (by linarith) hs0 hs1

theorem inst_norm_m_le (n : ℕ) :
    ‖BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n‖ ≤ 1 :=
  BASetup_norm_BAmF_le_one sz0 _ _ n (BAmF_sz0_im_pos n)

/-- **Instance of `baS1Std`** (target 1): `sz0`, `zSeq`, `κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `𝔠d = 1/100`,
`s ≡ 1/2`, `t ≡ 2/3`; `STConStInd` by the merged `s1Setup_conStInd_const`.  Every hypothesis discharged. -/
theorem inst_baS1Std :
    RBM.Ind.S1Std sz0 (min (1 / 2) 1) (1 / 6) (1 / 10) ((1 / 10) / 2) (1 / 100) (fun _ => 0) sI tI :=
  baS1Std 3 (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 100)
    (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0 sI tI (fun _ => by norm_num [sI])
    (fun _ => by norm_num [sI, tI]) Step1BootInst.inst_BAFamZ_horizon
    (RBM.Ind.Step1SetupInst.s1Setup_conStInd_const (s0 := 1 / 2) (t0 := 2 / 3) (by norm_num) (by norm_num)
      (by norm_num))

/-- The scale facts of the band apply to the block Anderson window (here `s1_F3`, `s1_F6`, `s1_F8`, which read `S1Std`
and nothing of the energy). -/
example : ∃ τ₀ > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ((sz0.size n : ℕ) : ℝ) ^ τ₀ * (RBM.Ind.s1B sz0 sI n) ^ ((1 : ℝ) / 2) <
      (RBM.Ind.s1B sz0 sI n) ^ ((1 : ℝ) / 4) := RBM.Ind.s1_F3 inst_baS1Std

example : ∀ᶠ n : ℕ in atTop,
    ((sz0.size n : ℕ) : ℝ)⁻¹ ≤ (RBM.Ind.s1B sz0 sI n) ^ ((1 : ℝ) / 4) / 2 := RBM.Ind.s1_F6 inst_baS1Std

example : ∀ᶠ n : ℕ in atTop,
    (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ ≤ (RBM.Ind.s1B sz0 sI n) ^ ((14 : ℝ) / 15) := RBM.Ind.s1_F8 inst_baS1Std

/-- **Instance of `baG_continuousOn`** (target 2): `sz0`, the flow data of `zSeq`, `n = 0`, the window `[0, 2/3]`, the
all-ones sample, the entry `(0, 0)`; `Im m > 0` is `BAmF_sz0_im_pos`. -/
theorem inst_baG_continuousOn :
    ContinuousOn (fun v : ℝ => (baFMz sz0 zSeq).GM 0 v (fun _ => (1 : ℝ)) 0 0) (Set.Icc 0 (2 / 3)) :=
  baG_continuousOn 3 sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 (BAmF_sz0_im_pos 0) 0 (2 / 3)
    (by norm_num) _ 0 0

/-- **Instance of `baGopbound`** (target 3): `sz0`, the flow data of `zSeq`, `κ = 1/2`, `C = 1`; `κ ≤ Im m`
(`inst_im_m_ge`), `|m| ≤ 1` (`inst_norm_m_le`), `SizeTendsto sz0` (`sz0_tendsto`). -/
theorem inst_baGopbound :
    ∃ C' > (0 : ℝ), ∀ D > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      Sizes.seqP (sz0.withLam 0) {ω | ∃ u u' : ℝ, 0 ≤ u ∧ 0 ≤ u' ∧
          u ≤ 1 - ((sz0.size n : ℕ) : ℝ)⁻¹ ∧ u' ≤ 1 - ((sz0.size n : ℕ) : ℝ)⁻¹ ∧
          |u - u'| ≤ ((sz0.size n : ℕ) : ℝ) ^ (-C') ∧
          ∃ x y : Idx 3 (sz0.L n) (sz0.W n),
            ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) <
              ‖BAGt sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n u ω x y -
                BAGt sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) n u' ω x y‖} ≤
        ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-D)) :=
  baGopbound 3 sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (1 / 2) (by norm_num) inst_im_m_ge inst_norm_m_le
    sz0_tendsto 1 one_pos

/-- `RangeCond (1/2) t` at `t ≡ 2/3` along `sz0`: `N^{-1/2} ≤ 1/3` eventually. -/
theorem inst_rangeCond : sz0.RangeCond (1 / 2) tI := by
  have h1 : Tendsto (fun n : ℕ => ((sz0.size n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp sz0_tendsto
  filter_upwards [h1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with n hn
  have e : (-1 + (1 / 2 : ℝ)) = -(1 / 2) := by norm_num
  rw [e]
  change _ ≤ 1 - 2 / 3
  linarith

/-- **Instance of `baNetLift`** (target 6): `sz0`, the flow data of `zSeq`, `κ = 1/2`, `τ = 1/2`, `s ≡ 1/2`, `t ≡ 2/3`;
`κ ≤ Im m`, `|m| ≤ 1`, `0 ≤ s ≤ t < 1`, `SizeTendsto`, `RangeCond (1/2) t` are discharged.  The per-time dominations stay
hypotheses (BA-S2b2b). -/
theorem inst_baNetLift
    (hpt : ∀ k : ℕ, 1 ≤ k →
      PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
        (U := fun n => TimeIcc sI tI n × (Fin k → Bool) × (Fin k → Zd 3 (sz0.L n)))
        (fun n p ω => ‖(baFMz sz0 zSeq).L n (p.1 : ℝ) p.2.1 p.2.2 ω‖)
        (fun n p _ => ((1 - sI n) / (1 - (p.1 : ℝ))) ^ (k - 1) * (sz0.Bctl n (sI n)) ^ (k - 1)))
    (hptw : PerTimeDomAt (Sizes.seqP (sz0.withLam 0)) sz0.size
        (U := fun n => TimeIcc sI tI n × Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
        (fun n p ω => ‖(baFMz sz0 zSeq).GM n (p.1 : ℝ) ω p.2.1 p.2.2‖)
        (fun n p _ => (sz0.Bctl n (p.1 : ℝ)) ^ (1 / 4 : ℝ))) :
    STStep1LoopgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI ∧
      STStep1WeakgL (baFMz sz0 zSeq) (Sizes.seqP (sz0.withLam 0)) sI tI := by
  have h := baNetLift 3 sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) (1 / 2) (1 / 2) sI tI (by norm_num)
    inst_im_m_ge inst_norm_m_le (by norm_num) (fun _ => by norm_num [sI]) (fun _ => by norm_num [sI, tI])
    (fun _ => by norm_num [tI]) sz0_tendsto inst_rangeCond
  exact ⟨h.1 hpt, h.2 hptw⟩

/-- `G_0 = M`: `(G_0 - M)_{xy} = 0` along the flow of `zSeq`. -/
theorem inst_GM_zero (ω : sz0.SeqΩ) (x y : Idx 3 (sz0.L 0) (sz0.W 0)) :
    (baFMz sz0 zSeq).GM 0 0 ω x y = 0 :=
  BASetup_GM_zero sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0 ω x y

/-- **Instance of `flowFM_wl_det`** (target 5) at the carrier `baFMz sz0 zSeq`, `n = 0`, `u = 0` (so `G_0 = M`,
`G - M = 0`: as T2256's `inst_baOmegaC_eq_one`), `a = 1/64` (`2a = 1/32 ≤ W^{-1/20}`, `W_0 = 32`), `c' = 1/20`,
`g = (W^3)⁻¹`, `Nτ = 4`, `C₀ = 3` (`‖G_0‖_max = ‖M‖_max ≤ (Im m)⁻¹ ≤ 2`).  The loop premise is `baFM_loop_det`
(`‖𝓛^{(2)}_0‖ ≤ (Im m)⁻² W^{-3} ≤ 4 g`); the two `(GiiGEX)`, `(GijGEX)` premises hold because `G - M = 0`.  Every
hypothesis is discharged. -/
theorem inst_flowFM_wl_det (ω : sz0.SeqΩ) :
    ∀ i j : Idx 3 (sz0.L 0) (sz0.W 0), ‖(baFMz sz0 zSeq).GM 0 0 ω i j‖ ^ 2 ≤
      (2 * 9 ^ 3 + 1) * (4 : ℝ) ^ 2 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ := by
  have hm := BAmF_sz0_im_pos 0
  have hmge := inst_im_m_ge 0
  have hW32 : ((sz0.W 0 : ℕ) : ℝ) = 32 := by
    rw [sz0_values.2.1]
    norm_num
  have hGMz : ∀ x y : Idx 3 (sz0.L 0) (sz0.W 0), (baFMz sz0 zSeq).GM 0 0 ω x y = 0 := inst_GM_zero ω
  refine flowFM_wl_det 3 sz0 (baFMz sz0 zSeq) 0 ω 0 (1 / 64) (1 / 20) (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ 4 3
    (by norm_num) ?_ ?_ (by norm_num) (by positivity) le_rfl ?_ ?_ ?_ ?_
  · intro x y
    rw [hGMz]
    norm_num
  · rw [hW32]
    calc 2 * (1 / 64 : ℝ) = (32 : ℝ) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one]
          norm_num
      _ ≤ (32 : ℝ) ^ (-(1 / 20 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
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
    have hL : ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖ ≤ 4 * (((sz0.W 0 : ℕ) : ℝ) ^ 3)⁻¹ := by
      refine hdet.trans (le_of_eq ?_)
      norm_num
    calc (baFMz sz0 zSeq).omegaC 0 0 3 ω * ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖
        ≤ ‖(baFMz sz0 zSeq).L 0 0 σ b ω‖ := mul_le_of_le_one_left (norm_nonneg _) hom
      _ ≤ _ := hL
  · intro p
    have := BASetup_maxLoop_nonneg (baFMz sz0 zSeq) 0 0 ω
    simp only [hGMz, norm_zero]
    nlinarith [this]
  · intro p
    have := BASetup_gexRHS_nonneg (baFMz sz0 zSeq) 0 0 ω (STblk sz0 0 p.1.1) (STblk sz0 0 p.1.2)
    simp only [hGMz, norm_zero]
    nlinarith [this]

/-- The instance of `flowFM_wl_det` at the all-ones sample. -/
example := inst_flowFM_wl_det (fun _ => (1 : ℝ))

/-- **Instance of `flowFM_omegaC_mono`** (target 4) at the same data, `C₁ = 1 < C₂ = 3`. -/
theorem inst_flowFM_omegaC_mono (ω : sz0.SeqΩ) :
    (baFMz sz0 zSeq).omegaC 0 0 1 ω ≤ (baFMz sz0 zSeq).omegaC 0 0 3 ω :=
  flowFM_omegaC_mono 3 sz0 (baFMz sz0 zSeq) 0 0 1 3 ω (by norm_num)

/-- The event `Ω_3 = {‖G_0‖_max ≤ 3}` has indicator `1` along the flow of `zSeq` at `u = 0`: `Ω_{1 + (Im m)⁻¹}` has
indicator `1` (`Step1BootInst.inst_baOmegaC_eq_one`, `1 + (Im m)⁻¹ ≤ 3`) and `flowFM_omegaC_mono`. -/
theorem inst_omegaC_three (ω : sz0.SeqΩ) : (baFMz sz0 zSeq).omegaC 0 0 3 ω = 1 := by
  have h1 := Step1BootInst.inst_baOmegaC_eq_one ω
  have h2 : 1 + ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im)⁻¹ ≤ 3 := by
    have h4 : ((BAmF sz0 (BAflowLam0 sz0 zSeq) (BAflowEs sz0 zSeq) 0).im)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (inst_im_m_ge 0)
    have h5 : (1 / 2 : ℝ)⁻¹ = 2 := by norm_num
    linarith
  have h3 := flowFM_omegaC_mono 3 sz0 (baFMz sz0 zSeq) 0 0 _ 3 ω h2
  have h6 := BASetup_omegaC_le_one (baFMz sz0 zSeq) 0 0 3 ω
  rw [h1] at h3
  exact le_antisymm h6 h3

end RBM.BA.Step1SetupInst
