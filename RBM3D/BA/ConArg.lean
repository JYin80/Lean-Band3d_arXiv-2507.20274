/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.FlowPins
import RBM3D.BA.CouplingWindow
import RBM3D.Induction.ConArg
import RBM3D.Induction.ConArgDet
import RBM3D.Induction.Split

/-!
# BA-S1: `lem_ConArg_BA` (`7_8:1956-1987`) in the event form `BAConArg''`

Ticket T2237 with Amend 1 (supervisor `2026-10-06-0255` §1.1-§1.3, DECISIONS §81).  Port of the
band proof `RBM3D/Induction/ConArg.lean` (`conArg`, `stConArg_holds`, commit `8a8cfeb`) onto the
block Anderson carrier.

* section 0: the event indicator `FlowFM.omegaC` of a carrier, the conjunct `BAConArgLoop''`, the
  successor pin `BAConArg''` of `BAConArg'` (`FlowPins.lean:630`), and the hypothesis bundle
  `BAConArgHyp`;
* section 1: the scalar layer (`|m| ≤ 1`, the bulk energy bound, the arithmetic of the shifted
  parameter `z̃ = √(t/s) z_s`);
* section 2: the same-`ω` scaling `H_t(g₀) = √(t/s) H_s(g_s)` and the resolvent scaling;
* section 3: the spectral layer (η-monotonicity and the Poisson-kernel comparison of
  `Im v^* G v`, the off-diagonal bound);
* section 4: the recursion of the band proof (copied, generic in the measure), the BA scalar data
  and the loop bookkeeping;
* section 5: conjunct 1 (`baConArgLoop''_holds`); section 6: conjunct 2 (`baConArgVec_holds`) and
  `BAimTrace_compare`; section 7: `baConArg''_holds`; section 8: compiled nonempty instances.

Paper: `paper/tex/7_8_light_weight.tex` (`7_8:line`), `lem_ConArg_BA` `:1956-1981`, its proof
(exactly Lemma 7.1 of [RBSO1D]) `:1983-1985`.  Band source:
`paper/tex/3_5_Loop_Hierarchy.tex:42-62`.
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

/-! ## 0. The event form of `lem_ConArg_BA` -/

/-- The indicator of `Ω_t = {‖G_t‖_max ≤ C₀}` over a flow carrier (the band's `STomegaC`, `Induction/Defs.lean:87`, is
the case `bandFM`). -/
def FlowFM.omegaC {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) : ℝ :=
  if ∀ x y : Idx d (sz.L n) (sz.W n), ‖C.G n t ω x y‖ ≤ C₀ then 1 else 0

/-- `lem_ConArg_BA` (1) in the event form (T2237a): `1(Ω_t) max |𝓛^{(k)}_{t,σ,a}(z_t, g₀)| ≺
((η_s/η_t) W^{-d}B_{s,0})^{k-1}`, `Ω_t = {‖G_t‖_max ≤ C₀}`, under the block Anderson law `seqP (sz.withLam 0)`;
the band's `STConArg` shape (`Induction/Defs.lean:334-345`), no factor `max_a tr(Im G_t E_a)`. -/
def BAConArgLoop'' {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (k : ℕ) (C₀ : ℝ) : Prop :=
  PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
    (fun n p ω => (baFMz sz z).omegaC n (t n) C₀ ω * ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
    (fun n _ _ => ((etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
          (baFMz sz z).eta n (t n)) * sz.Bctl n (s n)) ^ (k - 1))

/-- **`lem_ConArg_BA`, event form** (`7_8:1956-1987`; supervisor `2026-10-06-0255` §1.2; DECISIONS §81): the
hypotheses of `BAConArg'` (`FlowPins.lean:630-636`) verbatim; then, for every threshold `C₀ > 0`, `BAConArgLoop''`
for every `k ≥ 2` and the vector part `BAConArgVec`.  Registry class: proved here (`baConArg''_holds`). -/
def BAConArg'' (d : ℕ) : Prop :=
  ∀ κ ε 𝔡 ε₁ : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → 0 < ε₁ →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ s t : ℕ → ℝ, (∀ n, ε₁ ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) →
        (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) →
        STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s →
        ∀ C₀ : ℝ, 0 < C₀ → (∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀) ∧ BAConArgVec sz z s t

/-- The event indicator of the band carrier is the merged `STomegaC` (`Induction/Defs.lean:87`). -/
theorem bandFM_omegaC {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (n : ℕ) (t C₀ : ℝ) (ω : sz.SeqΩ) :
    (bandFM sz E).omegaC n t C₀ ω = Sizes.STomegaC sz n (E n) t C₀ ω := rfl

/-- The hypotheses of `BAConArg''`, as one conjunction (`FlowPins.lean:630-636`, verbatim; not a pin). -/
def BAConArgHyp {d : ℕ} (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) : Prop :=
  0 < κ ∧ 0 < ε ∧ 0 < 𝔡 ∧ 0 < ε₁ ∧ BAFlow sz κ ε 𝔠 𝔡 z ∧ (∀ n, ε₁ ≤ s n) ∧ (∀ n, s n ≤ t n) ∧
    (∀ n, t n < 1) ∧ (∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) ∧
    STLmaxgL (baFM sz (BAlamS sz z s t) (BAflowEs sz z)) (Sizes.seqP (sz.withLam 0)) s

/-! ## 1. The scalar layer -/

/-- **`|m| ≤ 1`** for every solution of `(self_m)` with `Im z ≥ 0` (`BAward_avg` and Cauchy-Schwarz,
supervisor `2026-10-05-1806` §1.1): `|m|² ≤ L^{-d} Σ_a |M_{aa}|² ≤ L^{-d} Σ_{a,b} |M_{ba}|² = Im m / (Im m + Im z) ≤ 1`. -/
theorem BAself_norm_le_one :
    ∀ (d L : ℕ) [NeZero L] (g : ℝ) (z m : ℂ), 0 ≤ z.im → BASelf d L g z m → ‖m‖ ≤ 1 := by
  intro d L _ g z m hz hm
  have hward := BAward_avg d L g hz hm
  obtain ⟨hmpos, hmeq⟩ := hm
  have hNpos : (0 : ℝ) < ((L ^ d : ℕ) : ℝ) := by
    have : 0 < L ^ d := pow_pos (NeZero.pos L) d
    exact_mod_cast this
  have hcard : (Finset.univ : Finset (Zd d L)).card = L ^ d := by rw [Finset.card_univ, BAcard_Zd]
  have hc : (((L ^ d : ℕ) : ℂ))⁻¹ = ((((L ^ d : ℕ) : ℝ))⁻¹ : ℝ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  set N : ℝ := ((L ^ d : ℕ) : ℝ) with hN
  set M := BAMB d L g z m with hMdef
  -- `‖m‖ ≤ N⁻¹ Σ_a ‖M a a‖`
  have h1 : ‖m‖ ≤ N⁻¹ * ∑ a : Zd d L, ‖M a a‖ := by
    have : ‖m‖ = N⁻¹ * ‖M.trace‖ := by
      rw [hmeq, hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hNpos.le)]
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hNpos.le)
    exact norm_sum_le _ _
  -- Cauchy-Schwarz
  have h2 : (∑ a : Zd d L, ‖M a a‖) ^ 2 ≤ N * ∑ a : Zd d L, ∑ b : Zd d L, ‖M b a‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Zd d L))) (f := fun a => ‖M a a‖)
    rw [hcard] at this
    refine this.trans ?_
    rw [hN]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by positivity)
    exact Finset.single_le_sum (f := fun b => ‖M b a‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hmim : 0 < m.im + z.im := by linarith
  set S : ℝ := ∑ a : Zd d L, ∑ b : Zd d L, ‖M b a‖ ^ 2 with hS
  set T : ℝ := ∑ a : Zd d L, ‖M a a‖ with hT
  have h3 : N⁻¹ * S ≤ 1 := by
    have h4 : N⁻¹ * S = m.im / (m.im + z.im) := by
      rw [eq_div_iff hmim.ne']
      calc (N⁻¹ * S) * (m.im + z.im) = (m.im + z.im) * (N⁻¹ * S) := by ring
        _ = m.im := hward
    rw [h4, div_le_one hmim]
    linarith
  have h5 : ‖m‖ ^ 2 ≤ 1 := by
    calc ‖m‖ ^ 2 ≤ (N⁻¹ * T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = N⁻¹ * (N⁻¹ * T ^ 2) := by ring
      _ ≤ N⁻¹ * (N⁻¹ * (N * S)) := by gcongr
      _ = N⁻¹ * S := by field_simp
      _ ≤ 1 := h3
  nlinarith [norm_nonneg m]

/-- **The bulk energy is bounded**: `Im m(E, g) > 0 ⇒ |E| ≤ 2 + 2d|g|` (contrapositive of `BAm_eq_zero_of_gt`).
With `(eq:WO)` (`g_n ≤ 𝔡⁻¹` eventually) this gives `|E_n| ≤ Λ := 2 + 2d/𝔡` eventually. -/
theorem BAenergy_le :
    ∀ (d L : ℕ) [NeZero L] (g E : ℝ), 0 < (BAm d L g (E : ℂ)).im → |E| ≤ 2 + 2 * d * |g| := by
  intro d L _ g E h
  by_contra hlt
  push Not at hlt
  rw [BAm_eq_zero_of_gt d L g E hlt] at h
  simp at h

/-- **The shifted spectral parameter** (BA form of `ztTilde_arith`, `ConArgDet.lean:850`):
`z̃ = √(t/s) z_s(E, g_s)`; constants depend on `(c, κ, Λ)` only.  The fourth conjunct replaces the band's
`η_t ≤ η_s` (false in general for BA: the couplings differ). -/
theorem BAztTilde_arith :
    ∀ c κ Λ : ℝ, 0 < c → 0 < κ → 0 < Λ → ∃ C : ℝ, 0 < C ∧
      ∀ (E s t : ℝ) (m₀ ms : ℂ), c ≤ s → s ≤ t → t < 1 → |E| ≤ Λ → ‖m₀‖ ≤ 1 → ‖ms‖ ≤ 1 → κ ≤ ms.im →
        ‖ztOf m₀ E t - (Real.sqrt (t / s) : ℂ) * ztOf ms E s‖ ^ 2 ≤ C * etaOf ms s ^ 2 ∧
        etaOf ms s ≤ ((Real.sqrt (t / s) : ℂ) * ztOf ms E s).im ∧
        ((Real.sqrt (t / s) : ℂ) * ztOf ms E s).im ≤ C * etaOf ms s ∧
        etaOf m₀ t ≤ C * etaOf ms s := by
  intro c κ Λ hc hκ hΛ
  set B : ℝ := Λ / c + 1 + c⁻¹ with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨(B / κ) ^ 2 + c⁻¹ + κ⁻¹, by positivity, ?_⟩
  intro E s t m₀ ms hcs hst ht hE hm0 hms hκms
  have hs0 : 0 < s := hc.trans_le hcs
  have hs1 : s < 1 := hst.trans_lt ht
  have hts : 1 ≤ t / s := (one_le_div hs0).2 hst
  set r : ℝ := Real.sqrt (t / s) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hts
  have hrsq : r ^ 2 = t / s := Real.sq_sqrt (by positivity)
  have hts_le : t / s ≤ c⁻¹ := by
    rw [div_le_iff₀ hs0]
    have : 1 ≤ c⁻¹ * s := by rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
    nlinarith
  have hr_le : r ≤ c⁻¹ := by nlinarith
  have hrm1 : r - 1 ≤ (1 - s) / c := by
    have h1 : r - 1 ≤ t / s - 1 := by nlinarith
    have h2 : t / s - 1 = (t - s) / s := by field_simp
    have h3 : (t - s) / s ≤ (1 - s) / c := by
      rw [div_le_div_iff₀ hs0 hc]
      nlinarith
    linarith
  have hηs : etaOf ms s = (1 - s) * ms.im := rfl
  have hηs_lo : (1 - s) * κ ≤ etaOf ms s := by
    rw [hηs]; exact mul_le_mul_of_nonneg_left hκms (by linarith)
  have hηs0 : 0 < etaOf ms s := lt_of_lt_of_le (mul_pos (by linarith) hκ) hηs_lo
  have h1s : 1 - s ≤ etaOf ms s / κ := by rw [le_div_iff₀ hκ]; linarith
  have him : ((r : ℂ) * ztOf ms E s).im = r * etaOf ms s := by
    rw [Complex.im_ofReal_mul, ztOf_im]
  have hmim : m₀.im ≤ 1 := (Complex.im_le_norm m₀).trans hm0
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the squared distance
    have key : ztOf m₀ E t - (r : ℂ) * ztOf ms E s =
        ((E * (1 - r) : ℝ) : ℂ) + ((1 - t : ℝ) : ℂ) * m₀ - ((r * (1 - s) : ℝ) : ℂ) * ms := by
      unfold ztOf; push_cast; ring
    have hnorm : ‖ztOf m₀ E t - (r : ℂ) * ztOf ms E s‖ ≤ B * (1 - s) := by
      rw [key]
      refine (norm_sub_le _ _).trans ?_
      refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
        abs_of_nonneg (by linarith : 0 ≤ 1 - s), abs_of_nonpos (by linarith : 1 - r ≤ 0),
        abs_of_nonneg (by linarith : 0 ≤ r)]
      have e1 : |E| * (-(1 - r)) ≤ Λ * ((1 - s) / c) := by
        have : -(1 - r) = r - 1 := by ring
        rw [this]
        exact mul_le_mul hE hrm1 (by linarith) hΛ.le
      have e2 : (1 - t) * ‖m₀‖ ≤ 1 - s := by
        nlinarith [norm_nonneg m₀]
      have e3 : r * (1 - s) * ‖ms‖ ≤ c⁻¹ * (1 - s) := by
        have : r * (1 - s) * ‖ms‖ ≤ r * (1 - s) * 1 :=
          mul_le_mul_of_nonneg_left hms (by nlinarith)
        nlinarith
      have e4 : Λ * ((1 - s) / c) = Λ / c * (1 - s) := by ring
      rw [hB]
      nlinarith
    calc ‖ztOf m₀ E t - (r : ℂ) * ztOf ms E s‖ ^ 2 ≤ (B * (1 - s)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ ≤ (B * (etaOf ms s / κ)) ^ 2 := by
          gcongr
      _ = (B / κ) ^ 2 * etaOf ms s ^ 2 := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
          have : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
          linarith
  · rw [him]; nlinarith
  · rw [him]
    calc r * etaOf ms s ≤ c⁻¹ * etaOf ms s := mul_le_mul_of_nonneg_right hr_le hηs0.le
      _ ≤ _ := by nlinarith [sq_nonneg (B / κ), inv_pos.mpr hκ]
  · have h1 : etaOf m₀ t ≤ 1 - s := by
      have : etaOf m₀ t = (1 - t) * m₀.im := rfl
      rw [this]
      nlinarith
    calc etaOf m₀ t ≤ 1 - s := h1
      _ ≤ etaOf ms s / κ := h1s
      _ = κ⁻¹ * etaOf ms s := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hηs0.le
          have : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
          have : 0 ≤ (B / κ) ^ 2 := sq_nonneg _
          linarith

/-! ## 2. The same-`ω` scaling `H_t(g₀) = √(t/s) H_s(g_s)` and the resolvent scaling -/

/-- **Same-`ω` scaling** (supervisor `2026-10-05-1806` §1.4): `H_t(g₀) = √(t/s) · H_s(g_s)` for `g_s = √(s/t) g₀`
(`BAlamS`), with the same `ω` (`seqHflowBA`: `g₀Ψ + √u X(ω)`; `seqHflow_eq_smul`). -/
theorem BAhflow_scale (d : ℕ) :
    ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ), 0 < s n → 0 < t n →
      sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω =
        ((Real.sqrt (t n / s n) : ℝ) : ℂ) • sz.seqHflowBA (BAlamS sz z s t) n (s n) ω := by
  intro sz z s t n ω hs ht
  have h1 : Real.sqrt (t n / s n) * Real.sqrt (s n / t n) = 1 := by
    rw [← Real.sqrt_mul (by positivity), div_mul_div_comm, mul_comm (t n) (s n),
      div_self (by positivity), Real.sqrt_one]
  have h2 : Real.sqrt (t n / s n) * Real.sqrt (s n) = Real.sqrt (t n) := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hs.ne']
  set X : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ := seqXmat (sz.withLam 0) n ω with hXdef
  have hBA : ∀ (lam0 : ℕ → ℝ) (u : ℝ), sz.seqHflowBA lam0 n u ω =
      (lam0 n : ℂ) • PsiI d (sz.L n) (sz.W n) + (Real.sqrt u : ℂ) • X := fun _ _ => rfl
  have h1' : ((Real.sqrt (t n / s n) : ℝ) : ℂ) * ((Real.sqrt (s n / t n) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, h1]; simp
  have h2' : ((Real.sqrt (t n / s n) : ℝ) : ℂ) * ((Real.sqrt (s n) : ℝ) : ℂ) = ((Real.sqrt (t n) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, h2]
  rw [hBA, hBA, smul_add, smul_smul, smul_smul]
  congr 2
  · simp only [BAlamS, Complex.ofReal_mul]
    rw [← mul_assoc, h1', one_mul]
  · exact h2'.symm

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for a nonzero scalar (no invertibility assumption on `A`).  Copy of the private
`conArg_inv_smul` (`Induction/ConArg.lean:386`, `8a8cfeb`). -/
private theorem ConArg_inv_smul {n : Type*} [Fintype n] [DecidableEq n] {c : ℂ} (hc : c ≠ 0)
    (A : Matrix n n ℂ) : (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · have : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv c]
  · have hdet : A.det = 0 := by simpa [isUnit_iff_ne_zero] using h
    have h2 : ¬ IsUnit (c • A).det := by
      rw [Matrix.det_smul, hdet, mul_zero]
      simp
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h2, Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

/-- `G(cH, cz) = c⁻¹ G(H, z)`; copy of the private `conArg_green_smul_mul` (`Induction/ConArg.lean:400`). -/
private theorem ConArg_green_smul_mul {n : Type*} [Fintype n] [DecidableEq n] {c : ℂ} (hc : c ≠ 0)
    (H : Matrix n n ℂ) (z : ℂ) : green (c • H) (c * z) = c⁻¹ • green H z := by
  have hsub : c • H - (c * z) • (1 : Matrix n n ℂ) = c • (H - z • (1 : Matrix n n ℂ)) := by
    rw [smul_sub, smul_smul]
  unfold green
  rw [hsub, ConArg_inv_smul hc]

/-- **Resolvent scaling**: `(rH - rw)^{-1} = r^{-1}(H - w)^{-1}` for real `r ≠ 0`, both charges (the BA form
of the band's private `conArg_Gres_smul_mul`, `Induction/ConArg.lean:409`). -/
theorem BAGres_smul :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (w : ℂ) (σ : Bool) (r : ℝ), r ≠ 0 →
      Gres ((r : ℂ) • H) ((r : ℂ) * w) σ = ((r : ℂ))⁻¹ • Gres H w σ := by
  intro ι _ _ H w σ r hr
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr
  rw [Ind.Gres_eq_green_zSig, Ind.Gres_eq_green_zSig]
  cases σ with
  | true => simpa only [Ind.zSig_true] using ConArg_green_smul_mul hrC H w
  | false =>
    simp only [Ind.zSig_false]
    rw [map_mul, Complex.conj_ofReal]
    exact ConArg_green_smul_mul hrC H _

/-- `H_u(g)` of the block Anderson flow is Hermitian (no merged lemma: `PsiI_isHermitian`,
`seqHflow_isHermitian`). -/
private theorem ConArg_seqHflowBA_isHermitian {d : ℕ} (sz : Sizes d) (lam0 : ℕ → ℝ) (n : ℕ) (u : ℝ)
    (ω : sz.SeqΩ) : (sz.seqHflowBA lam0 n u ω).IsHermitian := by
  unfold Sizes.seqHflowBA
  refine IsHermitian.add ?_ ((Sizes.seqHflow_isHermitian (sz.withLam 0) n u ω))
  unfold IsHermitian
  rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
    show star (lam0 n : ℂ) = (lam0 n : ℂ) from Complex.conj_ofReal _]

/-- The word of a list of `(σ, a)` pairs scales by `c⁻¹` per factor; copy of the private
`conArg_foldr_smul_mul` (`Induction/ConArg.lean:422`). -/
private theorem ConArg_foldr_smul_mul {d L W : ℕ} [NeZero L] {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (l : List (Bool × Zd d L)) :
    l.foldr (fun p M => Gres ((r : ℂ) • H) ((r : ℂ) * z) p.1 * Eblk d L W p.2 * M) 1
      = (((r : ℂ))⁻¹ ^ l.length) • l.foldr (fun p M => Gres H z p.1 * Eblk d L W p.2 * M) 1 := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih, BAGres_smul _ H z p.1 r (by exact_mod_cast hr), smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      smul_smul, pow_succ']

/-- `L(cH, cz) = c⁻ⁿ L(H, z)`; copy of the private `conArg_loopL_smul_mul` (`Induction/ConArg.lean:435`). -/
private theorem ConArg_loopL_smul_mul {d L W : ℕ} [NeZero L] {r : ℝ} (hr : (r : ℂ) ≠ 0)
    (H : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ) (I : Loop.LoopIdx (Zd d L)) :
    loopL d L W ((r : ℂ) • H) ((r : ℂ) * z) I
      = ((r : ℂ))⁻¹ ^ (I.σ.zip I.a).length * loopL d L W H z I := by
  unfold loopL
  rw [ConArg_foldr_smul_mul hr, Matrix.trace_smul, smul_eq_mul]

/-- **(6.1) pointwise, as a bound on `loopMax`, BA form**: for `0 < s ≤ t`, every loop of
`(H_t(g₀), z̃)`, `z̃ = √(t/s) z_s`, is `(s/t)^{k/2}` times the loop of `(H_s(g_s), z_s)` at the same sample point
(`BAhflow_scale`), hence `max|L̃^{(k)}| ≤ max|L_s^{(k)}|`.  Port of the private `conArg_loopMax_tilde_le`
(`Induction/ConArg.lean:448`). -/
private theorem ConArg_loopMax_tilde_le {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ)
    (h₁ : 0 < s n) (h₁₂ : s n ≤ t n) (ω : sz.SeqΩ) (zs : ℂ) (k : ℕ) :
    Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω))
        ((Real.sqrt (t n / s n) : ℂ) * zs) k
      ≤ Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω)) zs k := by
  set r : ℝ := Real.sqrt (t n / s n) with hr_def
  have hr1 : 1 ≤ r := by
    rw [hr_def, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ((one_le_div h₁).2 h₁₂)
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hH : blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω)
      = (r : ℂ) • blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω) := by
    rw [BAhflow_scale d sz z s t n ω h₁ (h₁.trans_le h₁₂)]
    rfl
  refine Ind.loopMax_le fun I hσ ha => ?_
  rw [hH, ConArg_loopL_smul_mul hrC, norm_mul, norm_pow, norm_inv,
    Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hle : r⁻¹ ^ (I.σ.zip I.a).length ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hr1)
  calc r⁻¹ ^ (I.σ.zip I.a).length * ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω)) zs I‖
      ≤ 1 * ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω)) zs I‖ :=
        mul_le_mul_of_nonneg_right hle (norm_nonneg _)
    _ = ‖loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω)) zs I‖ := one_mul _
    _ ≤ _ := Ind.norm_gloop_le_loopMax I hσ ha

/-! ## 3. The spectral layer: `η`-monotonicity, the Poisson comparison and the off-diagonal bound

For a Hermitian `H` with eigenvalues `λ_l` and `c = U^* v` (`U` the eigenvector unitary),
`v^* G(x+iy) v = Σ_l |c_l|² / (λ_l - x - iy)`, so `Im v^* G v = y Σ_l |c_l|² / ((λ_l-x)²+y²)`.  The private
`ConArg_inv_spectral` is the copy of `MFixedPoint_inv_spectral` (`MFixedPoint.lean:614`) at `g = 1`. -/

private theorem ConArg_inv_spectral {n : Type*} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {w : ℂ} (hw : ∀ l, (hH.eigenvalues l : ℂ) ≠ w) :
    Ring.inverse (H - w • (1 : Matrix n n ℂ)) =
      (hH.eigenvectorUnitary : Matrix n n ℂ)
        * diagonal (fun l => ((hH.eigenvalues l : ℂ) - w)⁻¹)
        * star (hH.eigenvectorUnitary : Matrix n n ℂ) := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (fun l => (hH.eigenvalues l : ℂ)) * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    rfl
  have hdiag : diagonal (fun l => (hH.eigenvalues l : ℂ) - w)
      = diagonal (fun l => (hH.eigenvalues l : ℂ)) - w • (1 : Matrix n n ℂ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h]
  have hsub : H - w • (1 : Matrix n n ℂ)
      = U * diagonal (fun l => (hH.eigenvalues l : ℂ) - w) * star U := by
    have h2 : U * (w • (1 : Matrix n n ℂ)) * star U = w • (1 : Matrix n n ℂ) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hUU']
    rw [hdiag, Matrix.mul_sub, Matrix.sub_mul, h2, ← hspec]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  apply Matrix.inv_eq_right_inv
  rw [hsub]
  calc U * diagonal (fun l => (hH.eigenvalues l : ℂ) - w) * star U
        * (U * diagonal (fun l => ((hH.eigenvalues l : ℂ) - w)⁻¹) * star U)
      = U * (diagonal (fun l => (hH.eigenvalues l : ℂ) - w) * (star U * U)
          * diagonal (fun l => ((hH.eigenvalues l : ℂ) - w)⁻¹)) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * 1 * star U := by
        have hd : (fun l => ((hH.eigenvalues l : ℂ) - w)
              * ((hH.eigenvalues l : ℂ) - w)⁻¹) = fun _ => (1 : ℂ) :=
          funext fun l => mul_inv_cancel₀ (sub_ne_zero.mpr (hw l))
        rw [hUU, mul_one, diagonal_mul_diagonal, hd, diagonal_one]
    _ = 1 := by rw [mul_one, hUU']

/-- the coordinates `c = U^* v` of `v` in the eigenbasis -/
private def ConArg_coef {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (v : ι → ℂ) : ι → ℂ :=
  (star (hH.eigenvectorUnitary : Matrix ι ι ℂ)) *ᵥ v

private theorem ConArg_vec_spectral {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {a : ℂ} (ha : a.im ≠ 0) (v w : ι → ℂ) :
    BAvecEntry (Gres H a true) v w =
      ∑ l, star (ConArg_coef hH v l) * (((hH.eigenvalues l : ℂ) - a)⁻¹ * ConArg_coef hH w l) := by
  have hw : ∀ l, (hH.eigenvalues l : ℂ) ≠ a := by
    intro l h
    have := congrArg Complex.im h
    simp at this
    exact ha this.symm
  unfold BAvecEntry Gres
  simp only [ite_true]
  rw [ConArg_inv_spectral hH hw, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have e1 : star v ᵥ* (hH.eigenvectorUnitary : Matrix ι ι ℂ) = star (ConArg_coef hH v) := by
    unfold ConArg_coef
    rw [Matrix.star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [e1]
  unfold dotProduct
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mulVec_diagonal]
  rfl

private theorem ConArg_inv_im (l x y : ℝ) :
    (((l : ℂ) - ((x : ℂ) + (y : ℂ) * Complex.I))⁻¹).im = y / ((l - x) ^ 2 + y ^ 2) := by
  rw [Complex.inv_im]
  simp [Complex.normSq_apply]
  ring_nf

private theorem ConArg_star_mul_im (c e : ℂ) : (star c * (e * c)).im = ‖c‖ ^ 2 * e.im := by
  have : star c * (e * c) = e * ((Complex.normSq c : ℝ) : ℂ) := by
    rw [mul_comm e c, ← mul_assoc, mul_comm (star c) c]
    rw [Complex.star_def, Complex.mul_conj]; ring
  rw [this, Complex.im_mul_ofReal, ← Complex.sq_norm]
  ring

private theorem ConArg_imG_formula {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v : ι → ℂ) (x y : ℝ) (hy : 0 < y) :
    (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im =
      y * ∑ l, ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2) := by
  have him : ((x : ℂ) + (y : ℂ) * Complex.I).im ≠ 0 := by simpa using hy.ne'
  rw [ConArg_vec_spectral hH him, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ConArg_star_mul_im, ConArg_inv_im]
  ring

/-- **`η`-monotonicity** of `Im v^*G(x+iy)v` at a fixed Hermitian matrix: `y ↦ y · Im G_vv` is nondecreasing and
`y ↦ Im G_vv / y` is nonincreasing (spectral decomposition). -/
theorem BAimG_eta_mono :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ) (x y y' : ℝ),
      H.IsHermitian → 0 < y → y ≤ y' →
        y * (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im ≤
            y' * (BAvecEntry (Gres H ((x : ℂ) + (y' : ℂ) * Complex.I) true) v v).im ∧
          (BAvecEntry (Gres H ((x : ℂ) + (y' : ℂ) * Complex.I) true) v v).im / y' ≤
            (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im / y := by
  intro ι _ _ H v x y y' hH hy hyy'
  have hy' : 0 < y' := hy.trans_le hyy'
  rw [ConArg_imG_formula hH v x y hy, ConArg_imG_formula hH v x y' hy']
  have hpos : ∀ (l : ι) (u : ℝ), 0 < u → 0 < (hH.eigenvalues l - x) ^ 2 + u ^ 2 := fun l u hu => by positivity
  constructor
  · calc y * (y * ∑ l, ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2))
        = ∑ l, ‖ConArg_coef hH v l‖ ^ 2 * (y ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
      _ ≤ ∑ l, ‖ConArg_coef hH v l‖ ^ 2 * (y' ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y' ^ 2)) := by
          refine Finset.sum_le_sum fun l _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          rw [div_le_div_iff₀ (hpos l y hy) (hpos l y' hy')]
          nlinarith [sq_nonneg (hH.eigenvalues l - x), mul_nonneg (sq_nonneg (hH.eigenvalues l - x))
            (sub_nonneg.mpr (pow_le_pow_left₀ hy.le hyy' 2))]
      _ = y' * (y' * ∑ l, ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y' ^ 2)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
  · rw [mul_div_cancel_left₀ _ hy'.ne', mul_div_cancel_left₀ _ hy.ne']
    refine Finset.sum_le_sum fun l _ => ?_
    exact div_le_div_of_nonneg_left (sq_nonneg _) (hpos l y hy)
      (by nlinarith [pow_le_pow_left₀ hy.le hyy' 2])

/-- **Poisson-kernel comparison** (1806 §1.4): `Im G_vv(x+iy) ≤ (2 + 2C²) Im G_vv(x'+iy)` for `|x - x'| ≤ C y`. -/
theorem BAimG_poisson :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (v : ι → ℂ) (x x' y C : ℝ),
      H.IsHermitian → 0 < y → 0 ≤ C → |x - x'| ≤ C * y →
        (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im ≤
          (2 + 2 * C ^ 2) * (BAvecEntry (Gres H ((x' : ℂ) + (y : ℂ) * Complex.I) true) v v).im := by
  intro ι _ _ H v x x' y C hH hy hC hxx
  rw [ConArg_imG_formula hH v x y hy, ConArg_imG_formula hH v x' y hy]
  have hxx2 : (x - x') ^ 2 ≤ C ^ 2 * y ^ 2 := by
    have := sq_le_sq' (abs_le.mp hxx).1 (abs_le.mp hxx).2
    nlinarith [this]
  calc y * ∑ l, ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2)
      ≤ y * ∑ l, (2 + 2 * C ^ 2) * (‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x') ^ 2 + y ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) hy.le
        have h1 : 0 < (hH.eigenvalues l - x) ^ 2 + y ^ 2 := by positivity
        have h2 : 0 < (hH.eigenvalues l - x') ^ 2 + y ^ 2 := by positivity
        have k : (hH.eigenvalues l - x') ^ 2 ≤ 2 * (hH.eigenvalues l - x) ^ 2 + 2 * (x - x') ^ 2 := by
          nlinarith [sq_nonneg (hH.eigenvalues l - x - (x - x'))]
        have h3 : 1 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2) ≤
            (2 + 2 * C ^ 2) * (1 / ((hH.eigenvalues l - x') ^ 2 + y ^ 2)) := by
          rw [← mul_div_assoc, mul_one, div_le_div_iff₀ h1 h2]
          nlinarith [sq_nonneg (hH.eigenvalues l - x), sq_nonneg y, mul_nonneg (sq_nonneg C) (sq_nonneg y)]
        calc ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2)
            = ‖ConArg_coef hH v l‖ ^ 2 * (1 / ((hH.eigenvalues l - x) ^ 2 + y ^ 2)) := by ring
          _ ≤ ‖ConArg_coef hH v l‖ ^ 2 * ((2 + 2 * C ^ 2) * (1 / ((hH.eigenvalues l - x') ^ 2 + y ^ 2))) :=
              mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
          _ = (2 + 2 * C ^ 2) * (‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x') ^ 2 + y ^ 2)) := by ring
    _ = (2 + 2 * C ^ 2) * (y * ∑ l, ‖ConArg_coef hH v l‖ ^ 2 / ((hH.eigenvalues l - x') ^ 2 + y ^ 2)) := by
        rw [← Finset.mul_sum]; ring

private theorem ConArg_normsq_e (l : ℝ) (a : ℂ) :
    ‖((l : ℂ) - a)⁻¹‖ ^ 2 = 1 / ((l - a.re) ^ 2 + a.im ^ 2) := by
  rw [norm_inv, inv_pow, Complex.sq_norm, Complex.normSq_apply, one_div]
  congr 1
  simp
  ring

/-- `Im G_vv(a) / Im a = Σ |c_l|² / |λ_l - a|²` (the Ward identity, spectral form). -/
private theorem ConArg_imG_div {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v : ι → ℂ) (a : ℂ) (ha : 0 < a.im) :
    (BAvecEntry (Gres H a true) v v).im / a.im =
      ∑ l, ‖ConArg_coef hH v l‖ ^ 2 * ‖((hH.eigenvalues l : ℂ) - a)⁻¹‖ ^ 2 := by
  have hae : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have h1 := ConArg_imG_formula hH v a.re a.im ha
  rw [← hae] at h1
  rw [h1, mul_div_cancel_left₀ _ ha.ne']
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [ConArg_normsq_e, div_eq_mul_one_div]

/-- **The off-diagonal comparison** (resolvent identity `G(a) - G(b) = (a - b) G(a) G(b)` and Cauchy-Schwarz, in
the eigenbasis; [RBSO1D] L7.1 (2)): for `Im a, Im b > 0`,
`|v^*G(a)w - v^*G(b)w| ≤ |a - b| (Im G(a)_vv / Im a)^{1/2} (Im G(b)_ww / Im b)^{1/2}`. -/
private theorem ConArg_offdiag {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v w : ι → ℂ) {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    ‖BAvecEntry (Gres H a true) v w - BAvecEntry (Gres H b true) v w‖ ≤
      ‖a - b‖ * (Real.sqrt ((BAvecEntry (Gres H a true) v v).im / a.im) *
        Real.sqrt ((BAvecEntry (Gres H b true) w w).im / b.im)) := by
  rw [ConArg_vec_spectral hH ha.ne' v w, ConArg_vec_spectral hH hb.ne' v w, ← Finset.sum_sub_distrib,
    ConArg_imG_div hH v a ha, ConArg_imG_div hH w b hb]
  set c := ConArg_coef hH v
  set d := ConArg_coef hH w
  have hterm : ∀ l, star (c l) * (((hH.eigenvalues l : ℂ) - a)⁻¹ * d l) -
      star (c l) * (((hH.eigenvalues l : ℂ) - b)⁻¹ * d l) =
      (a - b) * (star (c l) * d l * (((hH.eigenvalues l : ℂ) - a)⁻¹ * ((hH.eigenvalues l : ℂ) - b)⁻¹)) := by
    intro l
    have ha' : (hH.eigenvalues l : ℂ) - a ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hb' : (hH.eigenvalues l : ℂ) - b ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    field_simp
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans ?_
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι)
    (fun l => ‖c l‖ * ‖((hH.eigenvalues l : ℂ) - a)⁻¹‖) (fun l => ‖d l‖ * ‖((hH.eigenvalues l : ℂ) - b)⁻¹‖)
  have e1 : ∀ l, ‖star (c l) * d l * (((hH.eigenvalues l : ℂ) - a)⁻¹ * ((hH.eigenvalues l : ℂ) - b)⁻¹)‖ =
      (‖c l‖ * ‖((hH.eigenvalues l : ℂ) - a)⁻¹‖) * (‖d l‖ * ‖((hH.eigenvalues l : ℂ) - b)⁻¹‖) := by
    intro l
    rw [norm_mul, norm_mul, norm_mul, norm_star]
    ring
  simp_rw [e1]
  refine h2.trans (le_of_eq ?_)
  congr 2 <;> (refine Finset.sum_congr rfl fun l _ => ?_; ring)

private theorem ConArg_imG_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v : ι → ℂ) (x y : ℝ) (hy : 0 < y) :
    0 ≤ (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im := by
  rw [ConArg_imG_formula hH v x y hy]
  exact mul_nonneg hy.le (Finset.sum_nonneg fun l _ => by positivity)

/-- **Both directions of the diagonal comparison** at two spectral parameters `a, b` with `‖a - b‖ ≤ D Im b`,
`Im a ≤ E₁ Im b`, `Im b ≤ E₂ Im a` (η-monotonicity between the heights, Poisson comparison between the real
parts): `Im G(a)_vv ≤ (E₁+E₂)(2+2D²) Im G(b)_vv` and `Im G(b)_vv ≤ (E₁+E₂)(2+2D²) Im G(a)_vv`. -/
private theorem ConArg_diag_both {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v : ι → ℂ) {a b : ℂ} {D E₁ E₂ : ℝ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hD : 0 ≤ D) (hab : ‖a - b‖ ≤ D * b.im) (h1 : a.im ≤ E₁ * b.im) (h2 : b.im ≤ E₂ * a.im) :
    (BAvecEntry (Gres H a true) v v).im ≤ (E₁ + E₂) * ((2 + 2 * D ^ 2) * (BAvecEntry (Gres H b true) v v).im) ∧
      (BAvecEntry (Gres H b true) v v).im ≤ (E₁ + E₂) * ((2 + 2 * D ^ 2) * (BAvecEntry (Gres H a true) v v).im) := by
  have hE₁ : 0 ≤ E₁ := by
    by_contra h
    push Not at h
    nlinarith
  have hE₂ : 0 ≤ E₂ := by
    by_contra h
    push Not at h
    nlinarith
  have hae : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have hbe : b = (b.re : ℂ) + (b.im : ℂ) * Complex.I := (Complex.re_add_im b).symm
  set g : ℝ → ℝ → ℝ := fun x y => (BAvecEntry (Gres H ((x : ℂ) + (y : ℂ) * Complex.I) true) v v).im with hg
  have hga : (BAvecEntry (Gres H a true) v v).im = g a.re a.im := by rw [hg]; simp only; rw [← hae]
  have hgb : (BAvecEntry (Gres H b true) v v).im = g b.re b.im := by rw [hg]; simp only; rw [← hbe]
  rw [hga, hgb]
  have hx : |a.re - b.re| ≤ D * b.im := by
    refine le_trans ?_ hab
    have := Complex.abs_re_le_norm (a - b)
    simpa using this
  have hP1 := BAimG_poisson ι H v a.re b.re b.im D hH hb hD hx
  have hP2 := BAimG_poisson ι H v b.re a.re b.im D hH hb hD (by rwa [abs_sub_comm])
  have hg0 : ∀ x y, 0 < y → 0 ≤ g x y := fun x y hy => ConArg_imG_nonneg hH v x y hy
  have hK : 0 ≤ 2 + 2 * D ^ 2 := by positivity
  change g a.re b.im ≤ (2 + 2 * D ^ 2) * g b.re b.im at hP1
  change g b.re b.im ≤ (2 + 2 * D ^ 2) * g a.re b.im at hP2
  -- the η-comparison at `x = Re a`
  have key : g a.re a.im ≤ (E₁ + E₂) * g a.re b.im ∧ g a.re b.im ≤ (E₁ + E₂) * g a.re a.im := by
    rcases le_total b.im a.im with hle | hle
    · have hm := BAimG_eta_mono ι H v a.re b.im a.im hH hb hle
      change b.im * g a.re b.im ≤ a.im * g a.re a.im ∧ g a.re a.im / a.im ≤ g a.re b.im / b.im at hm
      obtain ⟨hm1, hm2⟩ := hm
      rw [div_le_div_iff₀ ha hb] at hm2
      have hgb0 := hg0 a.re b.im hb
      have hga0 := hg0 a.re a.im ha
      constructor
      · -- `g(ya) ≤ E₁ g(η)`
        have : g a.re a.im * b.im ≤ (E₁ * g a.re b.im) * b.im := by nlinarith
        have := le_of_mul_le_mul_right this hb
        nlinarith
      · -- `g(η) ≤ (ya/η) g(ya)`, `ya/η ≤ E₁`
        have : g a.re b.im * b.im ≤ ((E₁ + E₂) * g a.re a.im) * b.im := by
          nlinarith [mul_le_mul_of_nonneg_right h1 hga0, mul_nonneg (mul_nonneg hE₂ hga0) hb.le]
        exact le_of_mul_le_mul_right this hb
    · have hm := BAimG_eta_mono ι H v a.re a.im b.im hH ha hle
      change a.im * g a.re a.im ≤ b.im * g a.re b.im ∧ g a.re b.im / b.im ≤ g a.re a.im / a.im at hm
      obtain ⟨hm1, hm2⟩ := hm
      rw [div_le_div_iff₀ hb ha] at hm2
      have hgb0 := hg0 a.re b.im hb
      have hga0 := hg0 a.re a.im ha
      constructor
      · have : g a.re a.im * a.im ≤ ((E₁ + E₂) * g a.re b.im) * a.im := by
          nlinarith [mul_le_mul_of_nonneg_right h2 hgb0, mul_nonneg (mul_nonneg hE₁ hgb0) ha.le]
        exact le_of_mul_le_mul_right this ha
      · have : g a.re b.im * a.im ≤ ((E₁ + E₂) * g a.re a.im) * a.im := by
          nlinarith [mul_le_mul_of_nonneg_left h2 hga0, mul_nonneg (mul_nonneg hE₁ hga0) ha.le]
        exact le_of_mul_le_mul_right this ha
  have hT : 0 ≤ E₁ + E₂ := by linarith
  constructor
  · calc g a.re a.im ≤ (E₁ + E₂) * g a.re b.im := key.1
      _ ≤ (E₁ + E₂) * ((2 + 2 * D ^ 2) * g b.re b.im) := mul_le_mul_of_nonneg_left hP1 hT
  · calc g b.re b.im ≤ (2 + 2 * D ^ 2) * g a.re b.im := hP2
      _ ≤ (2 + 2 * D ^ 2) * ((E₁ + E₂) * g a.re a.im) := mul_le_mul_of_nonneg_left key.2 hK
      _ = (E₁ + E₂) * ((2 + 2 * D ^ 2) * g a.re a.im) := by ring

/-! ## 4. The recursion of §6 under `PerTimeDomAt` (copied from the band file) and the loop bookkeeping

Copied, with the prefix `ConArg_`, from the private helpers of `RBM3D/Induction/ConArg.lean` at `8a8cfeb`: the
recursion `ConArg_continuity_recursion` (`:65-376`, generic in the measure `P`; port of RBM1D
`StochDom.continuity_recursion`, `ContinuityAssembly.lean:697`), the base case (`:485-554`), the parameter count
(`:576-591`) and `a₁⁻¹ ≤ size` (`:621-645`). -/

section Recursion

open RBM.Ind.PerTimeCalc.PerTime

/-- `(x^{pj-1})^{1/p} ≤ x^j M^{1/p}` for `x > 0`, `x⁻¹ ≤ M`: the loss `M_{t₁}^{1/p}` of (6.10).
Port of RBM1D `rpow_pow_mul_sub_one_le` (`ContinuityAssembly.lean:646`). -/
private theorem ConArg_rpow_pow_mul_sub_one_le {x M : ℝ} (hx : 0 < x) (hM : x⁻¹ ≤ M) {p j : ℕ}
    (hp : 1 ≤ p) (hj : 1 ≤ j) :
    (x ^ (p * j - 1)) ^ (1 / (p : ℝ)) ≤ x ^ j * M ^ (1 / (p : ℝ)) := by
  have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have e : x ^ (p * j - 1) = (x ^ j) ^ p * x⁻¹ := by
    rw [← pow_mul, mul_comm j p]
    have : x ^ (p * j) = x ^ (p * j - 1) * x := by
      rw [← pow_succ]; congr 1; omega
    rw [this, mul_assoc, mul_inv_cancel₀ hx.ne', mul_one]
  rw [e, Real.mul_rpow (by positivity) (by positivity), one_div,
    Real.pow_rpow_inv_natCast (by positivity) (by omega)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hM (by positivity))
    (by positivity)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {size : ℕ → ℕ} {U : ℕ → Type*}

/-- Multiplying both sides of `≺` by a deterministic non-negative factor.  Port of RBM1D
`StochDom.det_mul_of` (`ContinuityAssembly.lean:663`). -/
private theorem ConArg_det_mul (hsize : Tendsto size atTop atTop) {f : ℕ → ℝ}
    (hf : ∀ N, 0 ≤ f N) {ξ ζ : ∀ N, U N → Ω → ℝ} (hξ : ∀ N u ω, 0 ≤ ξ N u ω)
    (h : PerTimeDomAt P size ξ ζ) :
    PerTimeDomAt P size (fun N u ω => f N * ξ N u ω) (fun N u ω => f N * ζ N u ω) :=
  perTimeCalc_mul (ξ₁ := fun N _ _ => f N) (ζ₁ := fun N _ _ => f N) hsize hξ
    (fun N _ _ => hf N) (perTimeCalc_refl hsize fun N _ _ => hf N) h

/-- A pointwise smaller left side. -/
private theorem ConArg_of_le_left {ξ ξ' ζ : ∀ N, U N → Ω → ℝ}
    (hle : ∀ N u ω, ξ N u ω ≤ ξ' N u ω) (h : PerTimeDomAt P size ξ' ζ) :
    PerTimeDomAt P size ξ ζ :=
  stochDom_of_le_left_eventually (Eventually.of_forall hle) h

/-- **Odd loops from even ones** ((6.4) under `≺`).  Port of RBM1D `StochDom.odd_of_even`
(`ContinuityAssembly.lean:670`). -/
private theorem ConArg_odd_of_even (hsize : Tendsto size atTop atTop)
    {Y : ℕ → ∀ N, U N → Ω → ℝ} {a : ℕ → ℝ} (ha : ∀ N, 0 ≤ a N)
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) {l : ℕ} (hl : 1 ≤ l)
    (hodd : ∀ N u ω, Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (h1 : PerTimeDomAt P size (Y (2 * l)) (fun N _ _ => a N ^ (2 * l - 1)))
    (h2 : PerTimeDomAt P size (Y (2 * l + 2)) (fun N _ _ => a N ^ (2 * l + 1))) :
    PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
  have hm := perTimeCalc_mul hsize (hY0 _) (fun N _ _ => pow_nonneg (ha N) _) h1 h2
  have hs := sqrt_of (fun N u ω => mul_nonneg (hY0 _ N u ω) (hY0 _ N u ω))
    (fun N u ω => mul_nonneg (pow_nonneg (ha N) _) (pow_nonneg (ha N) _)) hm
  have e : ∀ N, Real.sqrt (a N ^ (2 * l - 1) * a N ^ (2 * l + 1)) = a N ^ (2 * l) := by
    intro N
    rw [← pow_add, show 2 * l - 1 + (2 * l + 1) = 2 * (2 * l) by omega, pow_mul',
      Real.sqrt_sq (pow_nonneg (ha N) _)]
  refine ConArg_of_le_left (fun N u ω => Real.le_sqrt_of_sq_le (hodd N u ω)) ?_
  simpa only [e] using hs

/-- **The induction of §6, abstractly, per time.**  Port of RBM1D
`StochDom.continuity_recursion` (`ContinuityAssembly.lean:697`) with `N ↦ size N`:
for deterministic `0 < a₁ ≤ a`, `K ≥ 0`, `K a₁ ≤ C a`, `a₁⁻¹ ≤ size`, and families `Y_n, T_n ≥ 0`
with `T_n ≺ a₁^{n-1}`, `Y_1 ≤ B`, (6.4) and (6.11), one has `Y_n ≺ a^{n-1}` for every `n ≥ 1`. -/
private theorem ConArg_continuity_recursion (hsize : Tendsto size atTop atTop)
    {Y T : ℕ → ∀ N, U N → Ω → ℝ} {a a1 K : ℕ → ℝ} {C B : ℝ}
    (hY0 : ∀ n N u ω, 0 ≤ Y n N u ω) (hT0 : ∀ n N u ω, 0 ≤ T n N u ω)
    (ha1 : ∀ N, 0 < a1 N) (ha1a : ∀ N, a1 N ≤ a N) (hK0 : ∀ N, 0 ≤ K N) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hK : ∀ N, K N * a1 N ≤ C * a N) (hN : ∀ᶠ N : ℕ in atTop, (a1 N)⁻¹ ≤ (size N : ℝ))
    (hT : ∀ n, 1 ≤ n → PerTimeDomAt P size (T n) (fun N _ _ => a1 N ^ (n - 1)))
    (hY1 : ∀ N u ω, Y 1 N u ω ≤ B)
    (hodd : ∀ l, 1 ≤ l → ∀ N u ω,
      Y (2 * l + 1) N u ω ^ 2 ≤ Y (2 * l) N u ω * Y (2 * l + 2) N u ω)
    (hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ N u ω, Y (2 * m) N u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) N u ω + K N * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) N u ω * T (p * (2 * (m - l) - 1)) N u ω ^ (1 / (p : ℝ)))) :
    ∀ n, 1 ≤ n → PerTimeDomAt P size (Y n) (fun N _ _ => a N ^ (n - 1)) := by
  have ha0 : ∀ N, 0 < a N := fun N => (ha1 N).trans_le (ha1a N)
  have hY1' : PerTimeDomAt P size (Y 1) (fun N _ _ => a N ^ (2 * 0)) := by
    simp only [mul_zero, pow_zero]
    exact stochDom_of_le_const_mul hsize (hY0 1) (fun _ _ _ => zero_le_one) B
      (fun N u ω => by linarith [hY1 N u ω])
  -- the even lengths, by strong induction
  have hE : ∀ m, 1 ≤ m → PerTimeDomAt P size (Y (2 * m)) (fun N _ _ => a N ^ (2 * m - 1)) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hOdd : ∀ l, l < k → PerTimeDomAt P size (Y (2 * l + 1)) (fun N _ _ => a N ^ (2 * l)) := by
      intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl0
      · exact hY1'
      · refine ConArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hl0 (hodd l hl0)
          (ih l (by omega) hl0) ?_
        have := ih (l + 1) (by omega) (by omega)
        rwa [show 2 * (l + 1) = 2 * l + 2 by ring, show 2 * l + 2 - 1 = 2 * l + 1 by omega]
          at this
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    refine of_forall_rpow_mul fun δ hδ => ?_
    obtain ⟨p0, hp0⟩ := exists_nat_one_div_lt (half_pos hδ)
    set p := p0 + 1 with hp_def
    have hp : 1 ≤ p := by omega
    set r : ℝ := 1 / (p : ℝ) with hr
    have hr0 : 0 < r := by positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one (by positivity)]; exact_mod_cast hp
    have hrδ : r + r ≤ δ := by
      have : r < δ / 2 := by rw [hr, hp_def]; push_cast; exact hp0
      linarith
    set A : ℕ → ℝ := fun N => a N ^ (2 * k + 1) with hA
    have hA0 : ∀ N, 0 ≤ A N := fun N => pow_nonneg (ha0 N).le _
    have hNr : ∀ N : ℕ, 0 ≤ (size N : ℝ) ^ r := fun N => Real.rpow_nonneg (Nat.cast_nonneg _) r
    have hev : ∀ᶠ N : ℕ in atTop, 1 ≤ (size N : ℝ) ^ r ∧ (a1 N)⁻¹ ≤ (size N : ℝ) := by
      filter_upwards [hN, hsize.eventually (eventually_ge_atTop 1)] with N hN1 hN2
      exact ⟨Real.one_le_rpow (by exact_mod_cast hN2) hr0.le, hN1⟩
    -- (R1): the `G̃` loop of length `2m`
    have hR1 : PerTimeDomAt P size (T (2 * (k + 1)))
        (fun N _ _ => A N * (size N : ℝ) ^ r) := by
      refine mono_right_eventually (hT (2 * (k + 1)) (by omega)) ?_
      filter_upwards [hev] with N hN u ω
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      calc a1 N ^ (2 * k + 1) ≤ A N := pow_le_pow_left₀ (ha1 N).le (ha1a N) _
        _ ≤ A N * (size N : ℝ) ^ r := le_mul_of_one_le_right (hA0 N) hN.1
    -- the `G̃` factors `T^{1/p}`
    have hTr : ∀ j, 1 ≤ j → PerTimeDomAt P size (fun N u ω => K N * T (p * j) N u ω ^ r)
        (fun N _ _ => C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r) := by
      intro j hj
      have hpj : 1 ≤ p * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h1 := ConArg_det_mul hsize hK0 (fun N u ω => Real.rpow_nonneg (hT0 _ N u ω) r)
        (rpow_of_le_one hr0 hr1 (hT0 (p * j)) (fun N _ _ => pow_nonneg (ha1 N).le _)
          (hT (p * j) hpj))
      refine mono_right_eventually h1 ?_
      filter_upwards [hev] with N hN u ω
      have h2 := ConArg_rpow_pow_mul_sub_one_le (ha1 N) hN.2 hp hj
      calc K N * (a1 N ^ (p * j - 1)) ^ r ≤ K N * (a1 N ^ j * (size N : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left h2 (hK0 N)
        _ = (K N * a1 N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r := by
            rw [show a1 N ^ j = a1 N * a1 N ^ (j - 1) by
              rw [← pow_succ']; congr 1; omega]
            ring
        _ ≤ (C * a N) * a1 N ^ (j - 1) * (size N : ℝ) ^ r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hK N)
              (pow_nonneg (ha1 N).le _)) (hNr N)
        _ = C * a1 N ^ (j - 1) * a N * (size N : ℝ) ^ r := by ring
    -- (R2): the terms `l < m - 1`
    have hR2 : PerTimeDomAt P size (fun N u ω => ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        (fun N _ _ => ∑ l ∈ Finset.range k, C * A N * (size N : ℝ) ^ r) := by
      refine finset_sum_of hsize _ fun l hl => ?_
      have hl' := Finset.mem_range.mp hl
      have hj : 1 ≤ 2 * (k + 1 - l) - 1 := by omega
      have h1 := perTimeCalc_mul hsize
        (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 _ N u ω) r))
        (fun N _ _ => pow_nonneg (ha0 N).le _) (hOdd l hl') (hTr _ hj)
      refine mono_right_eventually (ConArg_of_le_left (fun N u ω => le_of_eq ?_) h1) ?_
      · ring
      · filter_upwards [hev] with N hN u ω
        have e : 2 * (k + 1 - l) - 1 - 1 = 2 * (k - l) := by omega
        rw [e]
        calc a N ^ (2 * l) * (C * a1 N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r)
            ≤ a N ^ (2 * l) * (C * a N ^ (2 * (k - l)) * a N * (size N : ℝ) ^ r) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (ha1 N).le (ha1a N) _) hC) (ha0 N).le) (hNr N))
                (pow_nonneg (ha0 N).le _)
          _ = C * A N * (size N : ℝ) ^ r := by
              simp only [hA]
              rw [show 2 * k + 1 = 2 * l + 2 * (k - l) + 1 by omega, pow_succ, pow_add]
              ring
    -- (R3): the term `l = m - 1`
    have hR3 : PerTimeDomAt P size (fun N u ω => K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r))
        (fun N u ω => B * C * A N * (size N : ℝ) ^ r
          + C * (size N : ℝ) ^ r * Real.sqrt (A N * Y (2 * (k + 1)) N u ω)) := by
      have hT1 := hTr 1 le_rfl
      simp only [mul_one, Nat.sub_self, pow_zero] at hT1
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · -- `m = 1`: the base case (5.6)
        have h1 := ConArg_det_mul (f := fun _ => B) hsize (fun _ => hB)
          (fun N u ω => mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)) hT1
        refine mono_right_eventually (ConArg_of_le_left (fun N u ω => ?_) h1) ?_
        · have hy := hY1 N u ω
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          simp only [mul_zero, zero_add]
          nlinarith
        · filter_upwards with N u ω
          simp only [hA, mul_zero, zero_add, pow_one]
          have h1 : 0 ≤ C * (size N : ℝ) ^ r * Real.sqrt (a N * Y (2 * 1) N u ω) :=
            mul_nonneg (mul_nonneg hC (hNr N)) (Real.sqrt_nonneg _)
          have h2 : 0 ≤ C * a N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)
          linarith
      · -- `m > 1`: (6.4) and the induction hypothesis for the `(2m-2)`-loops
        have hIH := sqrt_of (hY0 _) (fun N _ _ => pow_nonneg (ha0 N).le _)
          (ih k (by omega) hk0)
        have h1 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg _)
          (fun N _ _ => mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N)) hT1 hIH
        have h2 := perTimeCalc_mul hsize (fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
          (fun N _ _ => mul_nonneg (mul_nonneg (mul_nonneg hC (ha0 N).le) (hNr N))
            (Real.sqrt_nonneg _)) h1
          (perTimeCalc_refl hsize fun N u ω => Real.sqrt_nonneg (Y (2 * (k + 1)) N u ω))
        refine mono_right_eventually (ConArg_of_le_left (fun N u ω => ?_) h2) ?_
        · have hodd' := hodd k hk0 N u ω
          rw [show 2 * k + 2 = 2 * (k + 1) by ring] at hodd'
          have hy : Y (2 * k + 1) N u ω
              ≤ Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            rw [← Real.sqrt_mul (hY0 _ N u ω)]
            exact Real.le_sqrt_of_sq_le hodd'
          have hk := mul_nonneg (hK0 N) (Real.rpow_nonneg (hT0 p N u ω) r)
          calc K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)
              = (K N * T p N u ω ^ r) * Y (2 * k + 1) N u ω := by ring
            _ ≤ (K N * T p N u ω ^ r)
                * (Real.sqrt (Y (2 * k) N u ω) * Real.sqrt (Y (2 * (k + 1)) N u ω)) :=
                mul_le_mul_of_nonneg_left hy hk
            _ = _ := by ring
        · filter_upwards with N u ω
          have e : Real.sqrt (A N * Y (2 * (k + 1)) N u ω)
              = a N * Real.sqrt (a N ^ (2 * k - 1)) * Real.sqrt (Y (2 * (k + 1)) N u ω) := by
            simp only [hA]
            rw [show 2 * k + 1 = 2 + (2 * k - 1) by omega, pow_add,
              Real.sqrt_mul (mul_nonneg (pow_nonneg (ha0 N).le _) (pow_nonneg (ha0 N).le _)),
              Real.sqrt_mul (pow_nonneg (ha0 N).le _), Real.sqrt_sq (ha0 N).le]
          rw [e]
          have : 0 ≤ B * C * A N * (size N : ℝ) ^ r :=
            mul_nonneg (mul_nonneg (mul_nonneg hB hC) (hA0 N)) (hNr N)
          nlinarith [this]
    -- (6.13): assemble
    have hsum : ∀ N u ω, Y (2 * (k + 1)) N u ω ≤ ((k : ℝ) + 2) * ((T (2 * (k + 1)) N u ω
        + ∑ l ∈ Finset.range k,
          K N * (Y (2 * l + 1) N u ω * T (p * (2 * (k + 1 - l) - 1)) N u ω ^ r))
        + K N * (Y (2 * k + 1) N u ω * T p N u ω ^ r)) := by
      intro N u ω
      have h := hrec (k + 1) (by omega) p hp N u ω
      rw [Finset.sum_range_succ, show k + 1 - k = 1 by omega,
        show p * (2 * 1 - 1) = p by ring, ← hr] at h
      refine h.trans (le_of_eq ?_)
      rw [mul_add (K N), Finset.mul_sum]
      push_cast
      ring
    have hR := ConArg_det_mul (f := fun _ => (k : ℝ) + 2) hsize (fun _ => by positivity)
      (fun N u ω => add_nonneg (add_nonneg (hT0 _ N u ω) (Finset.sum_nonneg fun l _ =>
        mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
        (mul_nonneg (hK0 N) (mul_nonneg (hY0 _ N u ω) (Real.rpow_nonneg (hT0 _ N u ω) r))))
      (perTimeCalc_add hsize (perTimeCalc_add hsize hR1 hR2) hR3)
    set D1 : ℝ := ((k : ℝ) + 2) * (1 + ((k : ℝ) + B) * C) with hD1
    set D2 : ℝ := ((k : ℝ) + 2) * C with hD2
    set D : ℝ := (D1 + D2 + 1) ^ 2 with hD
    have hD1_0 : 0 ≤ D1 := mul_nonneg (by positivity)
      (by have := mul_nonneg (add_nonneg (Nat.cast_nonneg k) hB) hC; linarith)
    have hD2_0 : 0 ≤ D2 := mul_nonneg (by positivity) hC
    have hD1D : D1 ≤ D := by nlinarith
    have hD2D : D2 ^ 2 ≤ D := by nlinarith
    have hD0 : 0 ≤ D := sq_nonneg _
    have hstep : PerTimeDomAt P size (Y (2 * (k + 1))) (fun N u ω =>
        D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
          + Real.sqrt (D * ((size N : ℝ) ^ r * (size N : ℝ) ^ r * A N)
            * Y (2 * (k + 1)) N u ω)) := by
      refine mono_right_eventually (ConArg_of_le_left (fun N u ω => hsum N u ω) hR) ?_
      filter_upwards [hev] with N hN u ω
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      set x := (size N : ℝ) ^ r
      set y := Y (2 * (k + 1)) N u ω
      have hx1 : 1 ≤ x := hN.1
      have hy : 0 ≤ y := hY0 _ N u ω
      have hAy : 0 ≤ A N * y := mul_nonneg (hA0 N) hy
      have p1 : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
          ≤ D * (x * x * A N) := by
        have e : ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
            = D1 * (A N * x) := by rw [hD1]; ring
        rw [e]
        have hAx : 0 ≤ A N * x := mul_nonneg (hA0 N) (by linarith)
        calc D1 * (A N * x) ≤ D * (A N * x) := mul_le_mul_of_nonneg_right hD1D hAx
          _ ≤ D * (A N * x * x) := mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_right hAx hx1) hD0
          _ = D * (x * x * A N) := by ring
      have p2 : ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
          ≤ Real.sqrt (D * (x * x * A N) * y) := by
        refine Real.le_sqrt_of_sq_le ?_
        have e : (((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))) ^ 2
            = D2 ^ 2 * (x ^ 2 * (A N * y)) := by
          rw [show ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y))
            = D2 * x * Real.sqrt (A N * y) by rw [hD2]; ring, mul_pow, mul_pow,
            Real.sq_sqrt hAy]
          ring
        rw [e]
        calc D2 ^ 2 * (x ^ 2 * (A N * y)) ≤ D * (x ^ 2 * (A N * y)) :=
              mul_le_mul_of_nonneg_right hD2D (mul_nonneg (sq_nonneg _) hAy)
          _ = D * (x * x * A N) * y := by ring
      calc ((k : ℝ) + 2) * (A N * x + k * (C * A N * x)
            + (B * C * A N * x + C * x * Real.sqrt (A N * y)))
          = ((k : ℝ) + 2) * (A N * x + k * (C * A N * x) + B * C * A N * x)
            + ((k : ℝ) + 2) * (C * x * Real.sqrt (A N * y)) := by ring
        _ ≤ _ := add_le_add p1 p2
    have hZ0 : ∀ N (u : U N) (ω : Ω), 0 ≤ (size N : ℝ) ^ r * (size N : ℝ) ^ r * A N :=
      fun N _ _ => mul_nonneg (mul_nonneg (hNr N) (hNr N)) (hA0 N)
    have hZ := of_le_add_sqrt_mul hsize (hY0 _) (fun N u ω => mul_nonneg hD0 (hZ0 N u ω))
      hstep
    refine perTimeCalc_mono hsize
      (fun N _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) δ) (hA0 N)) D ?_ hZ
    filter_upwards [hsize.eventually (eventually_ge_atTop 1)] with N hN1 u ω
    have hN1' : (1 : ℝ) ≤ (size N : ℝ) := by exact_mod_cast hN1
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by positivity)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hN1' hrδ) (hA0 N)) hD0
  intro n hn
  rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
  · exact hE m (by omega)
  · rw [show 2 * m + 1 - 1 = 2 * m by omega]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · exact hY1'
    · refine ConArg_odd_of_even hsize (fun N => (ha0 N).le) hY0 hm0 (hodd m hm0) (hE m hm0) ?_
      have := hE (m + 1) (by omega)
      rwa [show 2 * (m + 1) = 2 * m + 2 by ring, show 2 * m + 2 - 1 = 2 * m + 1 by omega]
        at this

end Recursion

section BaseCase

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- `|⟨M E_b⟩| ≤ K` if every diagonal entry of `M` has modulus `≤ K` (`E_b = diag(bw b)` has total
weight `1`, `sum_bw`).  RBM2D `ConArg.lean:505` (`ConArg_norm_trace_mul_Eblk_le_of_diag`); RBM1D
`norm_trace_mul_Eblk_le_of_diag` (`ContinuityAssembly.lean:956`). -/
private theorem ConArg_norm_trace_mul_Eblk_le_of_diag
    (M : Matrix (Vtx d L W) (Vtx d L W) ℂ) (b : Zd d L) {K : ℝ}
    (hM : ∀ p, ‖M p p‖ ≤ K) : ‖trace (M * Eblk d L W b)‖ ≤ K := by
  rw [Ind.Eblk_eq_diagonal_bw, trace]
  simp only [diag_apply, mul_diagonal]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ p, ‖M p p * ((Ind.bw b p : ℝ) : ℂ)‖ ≤ ∑ p, K * Ind.bw b p := by
        refine Finset.sum_le_sum fun p _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Ind.bw_nonneg b p)]
        exact mul_le_mul_of_nonneg_right (hM p) (Ind.bw_nonneg b p)
    _ = K := by rw [← Finset.mul_sum, Ind.sum_bw, mul_one]

omit [NeZero W] in
/-- `G(-) = G(+)ᴴ` for Hermitian `H` (copy of the private `gres_false` of `Green/Pins.lean:367`). -/
private theorem ConArg_Gres_false {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H.IsHermitian)
    (z : ℂ) : Gres H z false = (Gres H z true)ᴴ := by
  unfold Gres
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv]
  congr 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH.eq]
  rfl

/-- **The base case (5.6)**: `|G_{ii}| ≤ K` for all `i` gives `max|L^{(1)}| ≤ K`.  RBM2D
`ConArg.lean:517` (`ConArg_loopMax_one_le`); RBM1D `loopMax_one_le`
(`ContinuityAssembly.lean:969`). -/
private theorem ConArg_loopMax_one_le {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hH : H.IsHermitian) {K : ℝ} (hK : ∀ i, ‖Gres H z true i i‖ ≤ K) :
    Ind.loopMax d L W H z 1 ≤ K := by
  refine Ind.loopMax_le fun I hσ ha => ?_
  obtain ⟨σ, a⟩ := I
  obtain ⟨s, rfl⟩ := List.length_eq_one_iff.mp hσ
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp ha
  have e : loopL d L W H z ⟨[s], [b]⟩ = trace (Gres H z s * Eblk d L W b) := by
    simp [loopL]
  rw [e]
  refine ConArg_norm_trace_mul_Eblk_le_of_diag _ b fun p => ?_
  cases s
  · rw [ConArg_Gres_false hH, conjTranspose_apply, norm_star]
    exact hK p
  · exact hK p

/-- The diagonal of the block-indexed Green function is the diagonal of the fine one: `blockMat` is
a relabelling by the equivalence `splitEquiv` (copy of the private `gres_blockMat_true` of
`Green/Pins.lean:350`). -/
private theorem ConArg_gres_blockMat_true (H : Matrix (Idx d L W) (Idx d L W) ℂ)
    (z : ℂ) (x y : Vtx d L W) :
    Gres (blockMat d L W H) z true x y =
      Gres H z true ((splitEquiv d L W).symm x) ((splitEquiv d L W).symm y) := by
  unfold Gres blockMat
  simp only [ite_true]
  have e1 : H.submatrix (splitEquiv d L W).symm (splitEquiv d L W).symm -
        z • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ) =
      (H - z • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)).submatrix (splitEquiv d L W).symm
        (splitEquiv d L W).symm := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply]
  rw [e1, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.inv_submatrix_equiv]
  rfl

end BaseCase

/-- `#((Fin k → Bool) × (Fin k → Zd d L)) = 2^k L^{dk} ≤ size^{2k}` once `2 ≤ size`. -/
private theorem ConArg_card_le {d : ℕ} (sz : Sizes d) (n k : ℕ) (h2 : 2 ≤ sz.size n) :
    (Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n))) : ℝ)
      ≤ ((sz.size n : ℕ) : ℝ) ^ ((2 * k : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  have hc : Fintype.card ((Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      = 2 ^ k * (sz.L n ^ d) ^ k := by
    simp [Fintype.card_prod, ZMod.card]
  have h1 : sz.L n ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
  have key : 2 ^ k * (sz.L n ^ d) ^ k ≤ sz.size n ^ (2 * k) := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul (Nat.pow_le_pow_left h2 k) (Nat.pow_le_pow_left h1 k)
  rw [hc]
  exact_mod_cast key

/-- `a₁⁻¹ ≤ size`: `W^{-d} B_{s,0} ≥ (W L)^{-d}` for `0 ≤ s < 1` (`B_{s,0} ≥ (L^d |1-s|)⁻¹ ≥ L^{-d}`
as `0 < 1 - s ≤ 1`; the first summand of `B` is `≥ 0`), for every `d`, every coupling `lam` and every
`L`: the scale `a₁` never beats the volume `N = (W L)^d`. -/
private theorem ConArg_Bctl_inv_le {d : ℕ} (sz : Sizes d) (n : ℕ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : (sz.Bctl n s)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  have hx : 0 < 1 - s := by linarith
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    unfold Sizes.size
    push_cast
    ring
  have hge : (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n s := by
    unfold Sizes.Bctl Bparam
    rw [abs_of_pos hx]
    have h1 : (((sz.L n : ℕ) : ℝ) ^ d)⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - s))⁻¹ :=
      inv_anti₀ (by positivity) (mul_le_of_le_one_right (by positivity) (by linarith))
    have h2 : 0 ≤ (sz.lam n ^ 2 + (1 - s))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
    rw [mul_inv]
    exact mul_le_mul_of_nonneg_left (h1.trans (le_add_of_nonneg_left h2)) (by positivity)
  rw [hsz]
  calc (sz.Bctl n s)⁻¹
      ≤ ((((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)⁻¹)⁻¹ := inv_anti₀ (by positivity) hge
    _ = _ := inv_inv _

/-! ### The deterministic flow data

`Im z_n > 0` on the chain domain; `m(E_n, g₀_n)` solves `(self_m)` (`BAzztE_data`) and so does `m(E_n, g_s)` when its
imaginary part is positive; both have modulus `≤ 1` (`BAself_norm_le_one`); the energies `E_n` are bounded by
`Λ := 2 + 2d (𝔡⁻¹ + Σ_{i<n₀} |g_i|)` for all `n` (`BAenergy_le`, `(eq:WO)` from `n₀` on). -/

/-- `Im z_n > 0` on the chain domain (`N^{-1+ε} ≤ Im z_n`); copy of the private `FlowPins_zim_pos`
(`FlowPins.lean:934`). -/
private theorem ConArg_zim_pos {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ} (h : BAFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)
  linarith

/-- `m(E_n, g₀_n)` solves `(self_m)` at the flow parameters (`BAzztE_data`, `BAm_real_eq_of_self`). -/
private theorem ConArg_m0_self {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (hz : 0 < (z n).im) :
    BASelf d (sz.L n) (BAflowLam0 sz z n) ((BAflowEs sz z n : ℝ) : ℂ)
      (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) := by
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  obtain ⟨-, -, hself, -, -⟩ := BAzztE_data d (sz.L n) (sz.lam n) hz hm
  have h := BAm_real_eq_of_self d (sz.L n) _ _ _ hself
  have e : BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n =
      BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAflowT0 sz z n) : ℂ) := h
  rw [e]
  exact hself

/-- `m(E, g)` solves `(self_m)` when its imaginary part is positive. -/
private theorem ConArg_self_of_im_pos {d : ℕ} (sz : Sizes d) (g E : ℕ → ℝ) (n : ℕ)
    (h : 0 < (BAmF sz g E n).im) : BASelf d (sz.L n) (g n) ((E n : ℝ) : ℂ) (BAmF sz g E n) := by
  by_contra hno
  have hne : ¬ ∃ m, BASelf d (sz.L n) (g n) ((E n : ℝ) : ℂ) m := by
    rintro ⟨m, hm⟩
    exact hno (BAm_spec ⟨m, hm⟩)
  have : BAmF sz g E n = 0 := by
    unfold BAmF BAm
    simp [hne]
  rw [this] at h
  simp at h

/-- `|g_s| ≤ |g_n|`: `g_s = √(s/t) √t₀ g_n` with `s ≤ t`, `t₀ < 1`. -/
private theorem ConArg_lamS_abs_le {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ)
    (hz : 0 < (z n).im) (hs0 : 0 < s n) (hst : s n ≤ t n) : |BAlamS sz z s t n| ≤ |sz.lam n| := by
  have hm := BAm_self d (sz.L n) (sz.lam n) (z n) hz
  have h1 : Real.sqrt (s n / t n) ≤ 1 :=
    Real.sqrt_le_one.mpr (div_le_one_of_le₀ hst (hs0.trans_le hst).le)
  have h2 : Real.sqrt (BAflowT0 sz z n) ≤ 1 := Real.sqrt_le_one.mpr (BAt0_lt_one hz hm.1).le
  unfold BAlamS BAflowLam0
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  calc Real.sqrt (s n / t n) * (Real.sqrt (BAflowT0 sz z n) * |sz.lam n|) ≤ 1 * (1 * |sz.lam n|) := by
        refine mul_le_mul h1 ?_ (by positivity) zero_le_one
        exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ = |sz.lam n| := by ring

/-- `|E_n| ≤ Λ` for all `n`, with `Λ = 2 + 2d (𝔡⁻¹ + Σ_{i<n₀} |g_i|)` (`BAenergy_le` at the coupling `g_s`,
`|g_s| ≤ |g_n|`; `(eq:WO)` from `n₀` on). -/
private theorem ConArg_energy_bound {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hκ : 0 < κ) (hs0 : ∀ n, 0 < s n) (hst : ∀ n, s n ≤ t n)
    (hκm : ∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ n, |BAflowEs sz z n| ≤ Λ := by
  have hz : ∀ n, 0 < (z n).im := ConArg_zim_pos sz hflow
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hflow.1.2.2.2.2
  set L₀ : ℝ := 𝔡⁻¹ + ∑ i ∈ Finset.range n₀, |sz.lam i| with hL₀
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range n₀, |sz.lam i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h𝔡inv : 0 ≤ 𝔡⁻¹ := inv_nonneg.mpr hflow.1.2.1.le
  have hlam : ∀ n, |sz.lam n| ≤ L₀ := by
    intro n
    by_cases hn : n₀ ≤ n
    · obtain ⟨h1, h2⟩ := hn₀ n hn
      have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
      have : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) h1
      rw [abs_of_pos this]
      linarith
    · have : |sz.lam n| ≤ ∑ i ∈ Finset.range n₀, |sz.lam i| :=
        Finset.single_le_sum (f := fun i => |sz.lam i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (not_le.mp hn))
      linarith
  refine ⟨2 + 2 * d * L₀, by have : 0 ≤ L₀ := by linarith
                             positivity, fun n => ?_⟩
  have hen := BAenergy_le d (sz.L n) (BAlamS sz z s t n) (BAflowEs sz z n) (lt_of_lt_of_le hκ (hκm n))
  have hgs : |BAlamS sz z s t n| ≤ |sz.lam n| := ConArg_lamS_abs_le sz z s t n (hz n) (hs0 n) (hst n)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  calc |BAflowEs sz z n| ≤ 2 + 2 * d * |BAlamS sz z s t n| := hen
    _ ≤ 2 + 2 * d * L₀ := by nlinarith [hlam n, hgs]

/-! ## 5. Conjunct 1: `baConArgLoop''_holds` (the port of `conArg`, `Induction/ConArg.lean:673-789`) -/

/-- `‖𝓛^{(k)}_{t,σ,a}‖` of the BA carrier is the norm of the list-based loop `loopL` of the block matrix
(`conArg_norm_Lloop_eq`, `Induction/ConArg.lean:559`). -/
private theorem ConArg_norm_L_eq {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖(baFM sz lam0 E).L n t σ a ω‖ =
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω))
        (ztOf (BAmF sz lam0 E n) (E n) t) ⟨List.ofFn σ, List.ofFn a⟩‖ := by
  change ‖BALloop sz lam0 E n t σ a ω‖ = _
  unfold BALloop loopFine
  rw [loopM_eq_loopL]
  rfl

/-- `‖𝓛^{(k)}_{t,σ,a}‖ ≤ max_{σ,a}`. -/
private theorem ConArg_norm_L_le_loopMax {d : ℕ} (sz : Sizes d) (lam0 E : ℕ → ℝ) (n : ℕ) (t : ℝ) {k : ℕ}
    (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)) (ω : sz.SeqΩ) :
    ‖(baFM sz lam0 E).L n t σ a ω‖ ≤ Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n t ω)) (ztOf (BAmF sz lam0 E n) (E n) t) k := by
  rw [ConArg_norm_L_eq]
  exact Ind.norm_gloop_le_loopMax _ (by simp) (by simp)

/-- A bound `≺` for all loops of length `k` (parameter `(σ, a)`, union inside `μ`) gives the per-time bound for
their maximum `loopMax` (the event `{max > size^τ ζ}` is inside the union event).  The BA form of the private
`conArg_loopMax_perTime` (`Induction/ConArg.lean:597`), without the cardinality step. -/
private theorem ConArg_loopMax_perTime {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (lam0 E : ℕ → ℝ)
    (s : ℕ → ℝ) {k : ℕ}
    (h : PrecL sz μ (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => ‖(baFM sz lam0 E).L n (s n) p.1 p.2 ω‖) (fun n _ _ => sz.Bctl n (s n) ^ (k - 1))) :
    PerTimeDomAt μ sz.size (U := fun _ => Unit)
      (fun n _ ω => Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA lam0 n (s n) ω)) (ztOf (BAmF sz lam0 E n) (E n) (s n)) k)
      (fun n _ _ => sz.Bctl n (s n) ^ (k - 1)) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn u
  refine (measure_mono ?_).trans hn
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  unfold Ind.loopMax at hω
  obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup hω
  refine ⟨x, ?_⟩
  beta_reduce
  rw [ConArg_norm_L_eq]
  exact hx

/-- **Conjunct 1 of `BAConArg''`** (`(res_lo_bo_eta_BA)`, `7_8:1965`, in the event form): the port of the band proof
`conArg` (`Induction/ConArg.lean:673`) with `a₁ = Bctl_s`, `a = a₁ η_s/η_t`, `a' = M a`, `M = max(1, C)`
(`C = C(ε₁, κ, Λ)` of `BAztTilde_arith`), `K = |z_t - z̃|²/(Im z_t Im z̃) ≤ C η_s/η_t`, `Y_j = 1_{Ω_t} max|𝓛_t^{(j)}(g₀)|`,
`T_j = max|𝓛̃^{(j)}|` at the shifted parameter `z̃ = √(t/s) z_s`, whose loops are `(s/t)^{j/2} ≤ 1` times those of
`(H_s(g_s), z_s)` (`BAhflow_scale`, `BAGres_smul`), so `T_j ≺ a₁^{j-1}` by `STLmaxgL` at `(g_s, s)`. -/
theorem baConArgLoop''_holds (d : ℕ) :
    ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
      ∀ C₀ : ℝ, 0 < C₀ → ∀ k : ℕ, 2 ≤ k → BAConArgLoop'' sz z s t k C₀ := by
  intro κ ε 𝔡 ε₁ 𝔠 sz z s t hyp C₀ hC₀ k hk
  obtain ⟨hκ, hε, h𝔡, hε₁, hflow, hs, hst, ht, hκm, hL⟩ := hyp
  have hsizeT : sz.SizeTendsto := hflow.1.2.2.1
  have hsize : Tendsto sz.size atTop atTop := sz.tendsto_size hsizeT
  have hsz2 : ∀ᶠ n : ℕ in atTop, 2 ≤ sz.size n := hsize.eventually (eventually_ge_atTop 2)
  have hs0 : ∀ n, 0 < s n := fun n => hε₁.trans_le (hs n)
  have ht0 : ∀ n, 0 < t n := fun n => (hs0 n).trans_le (hst n)
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans_lt (ht n)
  have hz : ∀ n, 0 < (z n).im := ConArg_zim_pos sz hflow
  obtain ⟨Λ, hΛ0, hEΛ⟩ := ConArg_energy_bound sz z s t hflow hκ hs0 hst hκm
  obtain ⟨Ca, hCa0, hCa⟩ := BAztTilde_arith ε₁ κ Λ hε₁ hκ hΛ0
  set P : Measure sz.SeqΩ := Sizes.seqP (sz.withLam 0) with hP
  -- the scalar data
  have hm0self := fun n => ConArg_m0_self sz z n (hz n)
  have hmsself := fun n => ConArg_self_of_im_pos sz (BAlamS sz z s t) (BAflowEs sz z) n (lt_of_lt_of_le hκ (hκm n))
  have hnm0 : ∀ n, ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 := fun n =>
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) (hm0self n)
  have hnms : ∀ n, ‖BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n‖ ≤ 1 := fun n =>
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) (hmsself n)
  have harith := fun n => hCa (BAflowEs sz z n) (s n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (hs n) (hst n) (ht n) (hEΛ n) (hnm0 n) (hnms n) (hκm n)
  -- the deterministic quantities
  set a1 : ℕ → ℝ := fun n => sz.Bctl n (s n) with ha1_def
  set ηs : ℕ → ℝ := fun n => etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) with hηs_def
  set ηt : ℕ → ℝ := fun n => (baFMz sz z).eta n (t n) with hηt_def
  have hηt_eq : ∀ n, ηt n = etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) := fun n => rfl
  have hηt : ∀ n, 0 < ηt n := fun n => by
    rw [hηt_eq]
    exact mul_pos (by linarith [ht n]) (hm0self n).1
  have hηs : ∀ n, 0 < ηs n := fun n => by
    have : ηs n = (1 - s n) * (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im := rfl
    rw [this]
    exact mul_pos (by linarith [hs1 n]) (lt_of_lt_of_le hκ (hκm n))
  set a : ℕ → ℝ := fun n => (ηs n / ηt n) * a1 n with ha_def
  set M : ℝ := max 1 Ca with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMCa : Ca ≤ M := le_max_right _ _
  set zz : ℕ → ℂ := fun n => ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) with hzz_def
  set zs : ℕ → ℂ := fun n => ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n) with hzs_def
  set zw : ℕ → ℂ := fun n => (Real.sqrt (t n / s n) : ℂ) * zs n with hzw_def
  set K : ℕ → ℝ := fun n => ‖zz n - zw n‖ ^ 2 * ((zz n).im * (zw n).im)⁻¹ with hK_def
  have hzz : ∀ n, (zz n).im = ηt n := fun n => ztOf_im _ _ _
  have hzw : ∀ n, ηs n ≤ (zw n).im := fun n => (harith n).2.1
  have hzw0 : ∀ n, 0 < (zw n).im := fun n => (hηs n).trans_le (hzw n)
  have hηts : ∀ n, ηt n ≤ Ca * ηs n := fun n => (harith n).2.2.2
  have ha1 : ∀ n, 0 < a1 n := fun n => sz.STBctl_pos n (hs1 n)
  have ha0 : ∀ n, 0 < a n := fun n => mul_pos (div_pos (hηs n) (hηt n)) (ha1 n)
  have ha'1 : ∀ n, a1 n ≤ M * a n := fun n => by
    have h1 : 1 ≤ M * (ηs n / ηt n) := by
      rw [← mul_div_assoc, le_div_iff₀ (hηt n)]
      nlinarith [hηts n, hηs n]
    calc a1 n = 1 * a1 n := (one_mul _).symm
      _ ≤ (M * (ηs n / ηt n)) * a1 n := mul_le_mul_of_nonneg_right h1 (ha1 n).le
      _ = M * a n := by simp only [ha_def]; ring
  have hK0 : ∀ n, 0 ≤ K n := fun n =>
    mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (mul_nonneg (by rw [hzz]; exact (hηt n).le) (hzw0 n).le))
  have hK : ∀ n, K n * a1 n ≤ Ca * (M * a n) := by
    intro n
    have hsq := (harith n).1
    have hx : ‖zz n - zw n‖ ^ 2 ≤ Ca * ηs n * (zw n).im := by
      calc ‖zz n - zw n‖ ^ 2 ≤ Ca * ηs n ^ 2 := hsq
        _ = Ca * ηs n * ηs n := by ring
        _ ≤ Ca * ηs n * (zw n).im := mul_le_mul_of_nonneg_left (hzw n) (mul_nonneg hCa0.le (hηs n).le)
    have hden : 0 < ηt n * (zw n).im := mul_pos (hηt n) (hzw0 n)
    have h1 : K n * a1 n ≤ Ca * a n := by
      simp only [hK_def, ha_def, hzz]
      calc ‖zz n - zw n‖ ^ 2 * (ηt n * (zw n).im)⁻¹ * a1 n
          ≤ (Ca * ηs n * (zw n).im) * (ηt n * (zw n).im)⁻¹ * a1 n :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (inv_nonneg.mpr hden.le)) (ha1 n).le
        _ = Ca * (ηs n / ηt n * a1 n) := by
            have := hηs n; have := hηt n; have := hzw0 n
            field_simp
    calc K n * a1 n ≤ Ca * a n := h1
      _ ≤ Ca * (M * a n) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (ha0 n).le hM1) hCa0.le
  have hNev : ∀ᶠ n : ℕ in atTop, (a1 n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) :=
    Eventually.of_forall fun n => ConArg_Bctl_inv_le sz n (hs0 n).le (hs1 n)
  -- the random families
  have hH : ∀ n u ω, (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n u ω)).IsHermitian :=
    fun n u ω => (ConArg_seqHflowBA_isHermitian sz (BAflowLam0 sz z) n u ω).submatrix _
  have hind : ∀ n ω, 0 ≤ (baFMz sz z).omegaC n (t n) C₀ ω := fun n ω => by
    unfold FlowFM.omegaC
    split_ifs <;> norm_num
  set Y : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → sz.SeqΩ → ℝ := fun j n _ ω =>
    (baFMz sz z).omegaC n (t n) C₀ ω *
      Ind.loopMax d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω)) (zz n) j with hY
  set T : ℕ → ∀ n : ℕ, (fun _ : ℕ => Unit) n → sz.SeqΩ → ℝ := fun j n _ ω =>
    Ind.loopMax d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω)) (zw n) j with hT
  have hY0 : ∀ j n u ω, 0 ≤ Y j n u ω := fun j n u ω => mul_nonneg (hind n ω) (Ind.loopMax_nonneg _)
  have hT0 : ∀ j n u ω, 0 ≤ T j n u ω := fun j n u ω => Ind.loopMax_nonneg _
  have hTd : ∀ j, 1 ≤ j → PerTimeDomAt P sz.size (T j) (fun n _ _ => a1 n ^ (j - 1)) := fun j hj =>
    ConArg_of_le_left (fun n _ ω => ConArg_loopMax_tilde_le sz z s t n (hs0 n) (hst n) ω (zs n) j)
      (ConArg_loopMax_perTime sz P (BAlamS sz z s t) (BAflowEs sz z) s (hL j hj))
  have hY1 : ∀ n u ω, Y 1 n u ω ≤ C₀ := by
    intro n u ω
    simp only [hY]
    unfold FlowFM.omegaC
    split_ifs with hω
    · rw [one_mul]
      refine ConArg_loopMax_one_le (hH n _ ω) fun i => ?_
      rw [ConArg_gres_blockMat_true]
      exact hω _ _
    · rw [zero_mul]; exact hC₀.le
  have hodd : ∀ l, 1 ≤ l → ∀ n u ω,
      Y (2 * l + 1) n u ω ^ 2 ≤ Y (2 * l) n u ω * Y (2 * l + 2) n u ω := by
    intro l hl n u ω
    simp only [hY]
    unfold FlowFM.omegaC
    split_ifs
    · simp only [one_mul]
      exact Ind.loopMax_odd_sq_le (hH n _ ω) hl
    · simp
  have hrec : ∀ m, 1 ≤ m → ∀ p, 1 ≤ p → ∀ n u ω, Y (2 * m) n u ω ≤ (m + 1 : ℝ) *
      (T (2 * m) n u ω + K n * ∑ l ∈ Finset.range m,
        Y (2 * l + 1) n u ω * T (p * (2 * (m - l) - 1)) n u ω ^ (1 / (p : ℝ))) := by
    intro m hm p hp n u ω
    simp only [hY, hT]
    unfold FlowFM.omegaC
    split_ifs with hω
    · simp only [one_mul]
      have hz' : 0 < (zz n).im := by rw [hzz]; exact hηt n
      refine (Ind.loopMax_two_mul_le_tilde (hH n _ ω) hz' (hzw0 n) hm hp).trans (le_of_eq ?_)
      simp only [hK_def]
      ring
    · simp only [zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      exact mul_nonneg (by positivity) (Ind.loopMax_nonneg _)
  have hmain := ConArg_continuity_recursion (P := P) (a := fun n => M * a n) hsize hY0 hT0 ha1 ha'1 hK0
    hCa0.le hC₀.le hK hNev hTd hY1 hodd hrec
  -- from `a'` to `a`
  have hY' : PerTimeDomAt P sz.size (Y k) (fun n _ _ => a n ^ (k - 1)) := by
    refine RBM.Ind.PerTimeCalc.PerTime.perTimeCalc_mono hsize (fun n _ _ => pow_nonneg (ha0 n).le _) (M ^ (k - 1))
      (Eventually.of_forall fun n u ω => le_of_eq (mul_pow _ _ _)) (hmain k (by omega))
  -- back to the parameter `(σ, a)`
  have hpar : PerTimeDomAt P sz.size (U := fun n => (Fin k → Bool) × (Fin k → Zd d (sz.L n)))
      (fun n p ω => (baFMz sz z).omegaC n (t n) C₀ ω * ‖(baFMz sz z).L n (t n) p.1 p.2 ω‖)
      (fun n _ _ => a n ^ (k - 1)) := by
    intro τ hτ D hD
    filter_upwards [hY' τ hτ D hD] with n hn p
    refine (measure_mono ?_).trans (hn ())
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    refine hω.trans_le ?_
    simp only [hY]
    exact mul_le_mul_of_nonneg_left (ConArg_norm_L_le_loopMax sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) p.1 p.2 ω)
      (hind n ω)
  exact stochDomAt_of_perTimeDomAt P sz.size (C := ((2 * k : ℕ) : ℝ)) (by positivity)
    (hsz2.mono fun n hn => ConArg_card_le sz n k hn) hpar

/-! ## 6. Conjunct 2: the vector bounds -/

private theorem ConArg_imG_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (v : ι → ℂ) {a : ℂ} (ha : 0 < a.im) :
    0 ≤ (BAvecEntry (Gres H a true) v v).im := by
  have hae : a = (a.re : ℂ) + (a.im : ℂ) * Complex.I := (Complex.re_add_im a).symm
  have := ConArg_imG_nonneg hH v a.re a.im ha
  rwa [← hae] at this

/-- The deterministic core of conjunct 2. -/
private theorem ConArg_vec_step {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (v w : ι → ℂ) {a b : ℂ} {r Ca c K₀ ηs ηt : ℝ} (hr1 : 1 ≤ r) (hrc : r ≤ c⁻¹) (hc : 0 < c) (hCa : 0 < Ca)
    (hK₀ : 0 ≤ K₀) (ha : 0 < a.im) (hb : 0 < b.im) (hab : ‖a - b‖ ^ 2 ≤ Ca * b.im ^ 2)
    (hηt : ηt = r * a.im) (hη : ηs = b.im) (hηts : ηt ≤ Ca * ηs)
    (hv : (BAvecEntry (Gres H b true) v v).im ≤ K₀) (hw : (BAvecEntry (Gres H b true) w w).im ≤ K₀)
    (hvw : ‖BAvecEntry (Gres H b true) v w‖ ≤ K₀) :
    (BAvecEntry (Gres H a true) v v).im ≤ (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * K₀ * (ηs / ηt) ∧
      ‖BAvecEntry (Gres H a true) v w‖ ≤
        (K₀ * Ca + Real.sqrt (Ca * ((Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * K₀) * K₀ * c⁻¹)) * (ηs / ηt) := by
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hηs0 : 0 < ηs := by rw [hη]; exact hb
  set ρ := ηs / ηt with hρ
  have hρ0 : 0 < ρ := div_pos hηs0 hηt0
  have h1ρ : 1 ≤ Ca * ρ := by rw [hρ, ← mul_div_assoc, le_div_iff₀ hηt0]; linarith
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  -- ratio bounds
  have h1 : a.im ≤ Ca * b.im := by
    have : a.im ≤ ηt := by rw [hηt]; nlinarith
    rw [← hη]; linarith
  have h2 : b.im ≤ (c⁻¹ * ρ) * a.im := by
    have e : ηs = ρ * ηt := by rw [hρ]; field_simp
    rw [← hη, e, hηt]
    nlinarith [mul_le_mul_of_nonneg_left hrc (mul_nonneg hρ0.le ha.le)]
  have hab' : ‖a - b‖ ≤ Real.sqrt Ca * b.im := by
    rw [show Real.sqrt Ca * b.im = Real.sqrt (Ca * b.im ^ 2) by
      rw [Real.sqrt_mul hCa.le, Real.sqrt_sq hb.le]]
    exact Real.le_sqrt_of_sq_le hab
  obtain ⟨hd1, -⟩ := ConArg_diag_both hH v ha hb (Real.sqrt_nonneg Ca) hab' h1 h2
  rw [Real.sq_sqrt hCa.le] at hd1
  have hga0 := ConArg_imG_nonneg' hH v ha
  have hgbw := ConArg_imG_nonneg' hH w hb
  have hgbv := ConArg_imG_nonneg' hH v hb
  set A1 : ℝ := (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * K₀ with hA1
  have hA10 : 0 ≤ A1 := by positivity
  have hdiag : (BAvecEntry (Gres H a true) v v).im ≤ A1 * ρ := by
    refine hd1.trans ?_
    have e1 : Ca + c⁻¹ * ρ ≤ (Ca ^ 2 + c⁻¹) * ρ := by nlinarith
    calc (Ca + c⁻¹ * ρ) * ((2 + 2 * Ca) * (BAvecEntry (Gres H b true) v v).im)
        ≤ ((Ca ^ 2 + c⁻¹) * ρ) * ((2 + 2 * Ca) * K₀) := by
          refine mul_le_mul e1 (mul_le_mul_of_nonneg_left hv (by positivity)) ?_ (by positivity)
          exact mul_nonneg (by positivity) hgbv
      _ = A1 * ρ := by rw [hA1]; ring
  refine ⟨hdiag, ?_⟩
  -- the off-diagonal entry
  have hoff := ConArg_offdiag hH v w ha hb
  set P := (BAvecEntry (Gres H a true) v v).im / a.im with hP
  set R := (BAvecEntry (Gres H b true) w w).im / b.im with hR
  have hP0 : 0 ≤ P := div_nonneg hga0 ha.le
  have hR0 : 0 ≤ R := div_nonneg hgbw hb.le
  have hPm : P ≤ A1 * ρ / a.im := div_le_div_of_nonneg_right hdiag ha.le
  have hRm : R ≤ K₀ / b.im := div_le_div_of_nonneg_right hw hb.le
  have hbia : b.im / a.im ≤ c⁻¹ * ρ := by rw [div_le_iff₀ ha]; exact h2
  set Z : ℝ := Real.sqrt (Ca * A1 * K₀ * c⁻¹) with hZ
  have hZ0 : 0 ≤ Z := Real.sqrt_nonneg _
  have hX : ‖a - b‖ * (Real.sqrt P * Real.sqrt R) ≤ Z * ρ := by
    have h3 : ‖a - b‖ * (Real.sqrt P * Real.sqrt R) ≤
        (Real.sqrt Ca * b.im) * (Real.sqrt (A1 * ρ / a.im) * Real.sqrt (K₀ / b.im)) := by
      refine mul_le_mul hab' (mul_le_mul (Real.sqrt_le_sqrt hPm) (Real.sqrt_le_sqrt hRm)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (by positivity) (by positivity)
    refine h3.trans ?_
    have hQ0 : 0 ≤ (Real.sqrt Ca * b.im) * (Real.sqrt (A1 * ρ / a.im) * Real.sqrt (K₀ / b.im)) := by positivity
    refine (pow_le_pow_iff_left₀ hQ0 (mul_nonneg hZ0 hρ0.le) (two_ne_zero)).mp ?_
    have hq : ((Real.sqrt Ca * b.im) * (Real.sqrt (A1 * ρ / a.im) * Real.sqrt (K₀ / b.im))) ^ 2 =
        Ca * (A1 * ρ) * K₀ * (b.im / a.im) := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hCa.le, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      field_simp
    rw [hq, mul_pow, hZ, Real.sq_sqrt (by positivity)]
    calc Ca * (A1 * ρ) * K₀ * (b.im / a.im) ≤ Ca * (A1 * ρ) * K₀ * (c⁻¹ * ρ) :=
          mul_le_mul_of_nonneg_left hbia (by positivity)
      _ = Ca * A1 * K₀ * c⁻¹ * ρ ^ 2 := by ring
  calc ‖BAvecEntry (Gres H a true) v w‖
      ≤ ‖BAvecEntry (Gres H b true) v w‖ + ‖BAvecEntry (Gres H a true) v w - BAvecEntry (Gres H b true) v w‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ K₀ + Z * ρ := add_le_add hvw (hoff.trans hX)
    _ ≤ (K₀ * Ca + Z) * ρ := by nlinarith [mul_le_mul_of_nonneg_left h1ρ hK₀]

/-- `BAvecEntry` is linear in the matrix. -/
private theorem ConArg_vecEntry_smul {ι : Type*} [Fintype ι] (c : ℂ) (A : Matrix ι ι ℂ) (v w : ι → ℂ) :
    BAvecEntry (c • A) v w = c * BAvecEntry A v w := by
  unfold BAvecEntry
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- `1 ≤ r = √(t/s) ≤ c⁻¹` for `c ≤ s ≤ t < 1` (`r ≤ r² = t/s ≤ s⁻¹ ≤ c⁻¹`). -/
private theorem ConArg_r_bounds {c s t : ℝ} (hc : 0 < c) (hcs : c ≤ s) (hst : s ≤ t) (ht : t < 1) :
    1 ≤ Real.sqrt (t / s) ∧ Real.sqrt (t / s) ≤ c⁻¹ := by
  have hs0 : 0 < s := hc.trans_le hcs
  have hts : 1 ≤ t / s := (one_le_div hs0).2 hst
  have hr1 : 1 ≤ Real.sqrt (t / s) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hts
  refine ⟨hr1, ?_⟩
  have hrsq : Real.sqrt (t / s) ^ 2 = t / s := Real.sq_sqrt (by positivity)
  have hts_le : t / s ≤ c⁻¹ := by
    rw [div_le_iff₀ hs0]
    have : 1 ≤ c⁻¹ * s := by rw [inv_mul_eq_div, le_div_iff₀ hc]; linarith
    nlinarith
  nlinarith

/-- **The scaling setup at one `(n, ω)`** (shared by conjunct 2 and `BAimTrace_compare`): with `r = √(t/s)` and
`a = r⁻¹ z_t`, `G_t(z_t; H_t(g₀)) = r⁻¹ G(a; H_s(g_s))` (`BAhflow_scale`, `BAGres_smul`), `η_t = r Im a`, and
`|a - z_s|² ≤ C_a Im z_s²` (from `|z_t - z̃|² ≤ C_a η_s²`, `r ≥ 1`). -/
private theorem ConArg_setup {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    {c Ca : ℝ} (hc : 0 < c) (hcs : c ≤ s n) (hst : s n ≤ t n) (ht : t n < 1)
    (h1 : ‖ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) -
        (Real.sqrt (t n / s n) : ℂ) *
          ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)‖ ^ 2 ≤
        Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) ^ 2)
    (hηt0 : 0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n))
    (hηs0 : 0 < etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n)) :
    ∃ (r : ℝ) (a : ℂ), 1 ≤ r ∧ r ≤ c⁻¹ ∧
      BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω =
        ((r : ℂ))⁻¹ • Gres (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω) a true ∧
      0 < a.im ∧ 0 < (ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)).im ∧
      ‖a - ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)‖ ^ 2 ≤
        Ca * (ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)).im ^ 2 ∧
      etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) = r * a.im := by
  have hs0 : 0 < s n := hc.trans_le hcs
  have ht0 : 0 < t n := hs0.trans_le hst
  obtain ⟨hr1, hrc⟩ := ConArg_r_bounds hc hcs hst ht
  set r : ℝ := Real.sqrt (t n / s n) with hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  set zz : ℂ := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) with hzz
  set zs : ℂ := ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n) with hzs
  set a : ℂ := ((r⁻¹ : ℝ) : ℂ) * zz with ha_def
  have hra : (r : ℂ) * a = zz := by
    rw [ha_def, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hr0.ne']; simp
  have hGt : BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω =
      ((r : ℂ))⁻¹ • Gres (sz.seqHflowBA (BAlamS sz z s t) n (s n) ω) a true := by
    have e1 : sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω = (r : ℂ) • sz.seqHflowBA (BAlamS sz z s t) n (s n) ω :=
      BAhflow_scale d sz z s t n ω hs0 ht0
    change Gres (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω) zz true = _
    rw [e1, ← hra]
    exact BAGres_smul _ _ a true r hr0.ne'
  have hai : a.im = r⁻¹ * zz.im := by rw [ha_def, Complex.im_ofReal_mul]
  have hbim : zs.im = etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) := ztOf_im _ _ _
  refine ⟨r, a, hr1, hrc, hGt, ?_, ?_, ?_, ?_⟩
  · rw [hai, hzz, ztOf_im]
    exact mul_pos (inv_pos.mpr hr0) hηt0
  · rw [hbim]; exact hηs0
  · have e : a - zs = ((r⁻¹ : ℝ) : ℂ) * (zz - (r : ℂ) * zs) := by
      rw [ha_def]
      have : ((r⁻¹ : ℝ) : ℂ) * ((r : ℂ) * zs) = zs := by
        rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne']; simp
      rw [mul_sub, this]
    have hn : ‖a - zs‖ ≤ ‖zz - (r : ℂ) * zs‖ := by
      rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
      calc r⁻¹ * ‖zz - (r : ℂ) * zs‖ ≤ 1 * ‖zz - (r : ℂ) * zs‖ :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr1) (norm_nonneg _)
        _ = _ := one_mul _
    calc ‖a - zs‖ ^ 2 ≤ ‖zz - (r : ℂ) * zs‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ ≤ Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) ^ 2 := h1
      _ = Ca * zs.im ^ 2 := by rw [hbim]
  · rw [hai, hzz, ztOf_im, ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]

/-- **The deterministic core of conjunct 2 at one `(n, ω)`**: from `Im (G_s)_{vv}, Im (G_s)_{ww}, |(G_s)_{vw}| ≤ K₀`
(`G_s = G(z_s; H_s(g_s))`) to `Im (G_t)_{vv}, |(G_t)_{vw}| ≲ η_s/η_t` (`ConArg_setup`, then `ConArg_vec_step`). -/
private theorem ConArg_vec_at {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (v w : Idx d (sz.L n) (sz.W n) → ℂ) {c Ca K₀ : ℝ} (hc : 0 < c) (hCa : 0 < Ca) (hK₀ : 0 ≤ K₀)
    (hcs : c ≤ s n) (hst : s n ≤ t n) (ht : t n < 1)
    (h1 : ‖ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) -
        (Real.sqrt (t n / s n) : ℂ) *
          ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)‖ ^ 2 ≤
        Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) ^ 2)
    (h4 : etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) ≤
      Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n))
    (hηt0 : 0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n))
    (hηs0 : 0 < etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n))
    (hv : (BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) v v).im ≤ K₀)
    (hw : (BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) w w).im ≤ K₀)
    (hvw : ‖BAvecEntry (BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω) v w‖ ≤ K₀) :
    (BAvecEntry (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω) v v).im ≤
        (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * K₀ *
          (etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
            etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n)) ∧
      ‖BAvecEntry (BAGt sz (BAflowLam0 sz z) (BAflowEs sz z) n (t n) ω) v w‖ ≤
        (K₀ * Ca + Real.sqrt (Ca * ((Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * K₀) * K₀ * c⁻¹)) *
          (etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
            etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n)) := by
  obtain ⟨r, a, hr1, hrc, hGt, ha, hb, hab, hηt⟩ := ConArg_setup sz z s t n ω hc hcs hst ht h1 hηt0 hηs0
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  set H := sz.seqHflowBA (BAlamS sz z s t) n (s n) ω with hHdef
  have hH : H.IsHermitian := ConArg_seqHflowBA_isHermitian sz _ n _ ω
  have hGs : BAGt sz (BAlamS sz z s t) (BAflowEs sz z) n (s n) ω =
      Gres H (ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)) true := rfl
  rw [hGs] at hv hw hvw
  have hbim : (ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)).im =
      etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) := ztOf_im _ _ _
  obtain ⟨hd, ho⟩ := ConArg_vec_step hH v w hr1 hrc hc hCa hK₀ ha hb hab hηt hbim.symm h4 hv hw hvw
  rw [hGt, ConArg_vecEntry_smul, ConArg_vecEntry_smul]
  have hcinv : ((r : ℂ))⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv]
  rw [hcinv]
  constructor
  · rw [Complex.im_ofReal_mul]
    calc r⁻¹ * (BAvecEntry (Gres H a true) v v).im ≤ 1 * (BAvecEntry (Gres H a true) v v).im :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr1) (ConArg_imG_nonneg' hH v ha)
      _ ≤ _ := by rw [one_mul]; exact hd
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hr0.le)]
    calc r⁻¹ * ‖BAvecEntry (Gres H a true) v w‖ ≤ 1 * ‖BAvecEntry (Gres H a true) v w‖ :=
          mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr1) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact ho

/-- The scalar data of conjuncts 1 and 2 along the sequence: a constant `C_a = C_a(ε₁, κ, Λ)` with, for every `n`,
`|z_t - z̃|² ≤ C_a η_s²`, `η_t ≤ C_a η_s`, `η_t > 0`, `η_s > 0` (`BAztTilde_arith` with `|m| ≤ 1`). -/
private theorem ConArg_eta_data {d : ℕ} {κ ε 𝔠 𝔡 ε₁ : ℝ} (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ)
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (hκ : 0 < κ) (hε₁ : 0 < ε₁) (hs : ∀ n, ε₁ ≤ s n) (hst : ∀ n, s n ≤ t n)
    (ht : ∀ n, t n < 1) (hκm : ∀ n, κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ n,
      ‖ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) -
          (Real.sqrt (t n / s n) : ℂ) *
            ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)‖ ^ 2 ≤
          Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) ^ 2 ∧
      etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) ≤
        Ca * etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) ∧
      0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) ∧
      0 < etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) := by
  have hs0 : ∀ n, 0 < s n := fun n => hε₁.trans_le (hs n)
  have hs1 : ∀ n, s n < 1 := fun n => (hst n).trans_lt (ht n)
  have hz : ∀ n, 0 < (z n).im := ConArg_zim_pos sz hflow
  obtain ⟨Λ, hΛ0, hEΛ⟩ := ConArg_energy_bound sz z s t hflow hκ hs0 hst hκm
  obtain ⟨Ca, hCa0, hCa⟩ := BAztTilde_arith ε₁ κ Λ hε₁ hκ hΛ0
  refine ⟨Ca, hCa0, fun n => ?_⟩
  have hm0self := ConArg_m0_self sz z n (hz n)
  have hmsself := ConArg_self_of_im_pos sz (BAlamS sz z s t) (BAflowEs sz z) n (lt_of_lt_of_le hκ (hκm n))
  have hnm0 : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) hm0self
  have hnms : ‖BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n‖ ≤ 1 :=
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) hmsself
  obtain ⟨h1, -, -, h4⟩ := hCa (BAflowEs sz z n) (s n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (hs n) (hst n) (ht n) (hEΛ n) hnm0 hnms (hκm n)
  refine ⟨h1, h4, ?_, ?_⟩
  · exact mul_pos (by linarith [ht n]) hm0self.1
  · exact mul_pos (by linarith [hs1 n]) (lt_of_lt_of_le hκ (hκm n))

/-- **Conjunct 2 of `BAConArg''`** (`(eq:ImGs)` ⇒ `(eq:ImGt)`, `7_8:1976-1979`), deterministic on the event of the
premise: `G_t(z_t; H_t(g₀)) = √(s/t) G(a; H_s(g_s))`, `a = √(s/t) z_t` (`ConArg_vec_at`); the event of the premise
is contained in the event of the conclusion with `C₁ = A₁ + K₀ C_a + Z + 1`, so `HighProbAt.mono` applies. -/
theorem baConArgVec_holds (d : ℕ) :
    ∀ (κ ε 𝔡 ε₁ 𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ), BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t →
      BAConArgVec sz z s t := by
  intro κ ε 𝔡 ε₁ 𝔠 sz z s t hyp v w hv hw hprem
  obtain ⟨hκ, hε, h𝔡, hε₁, hflow, hs, hst, ht, hκm, hL⟩ := hyp
  obtain ⟨K₀, hK₀, hHP⟩ := hprem
  obtain ⟨Ca, hCa0, hCa⟩ := ConArg_eta_data sz z s t hflow hκ hε₁ hs hst ht hκm
  refine ⟨(Ca ^ 2 + ε₁⁻¹) * (2 + 2 * Ca) * K₀ + K₀ * Ca +
    Real.sqrt (Ca * ((Ca ^ 2 + ε₁⁻¹) * (2 + 2 * Ca) * K₀) * K₀ * ε₁⁻¹) + 1, by positivity, ?_⟩
  refine HighProbAt.mono hHP (Eventually.of_forall fun n ω hω => ?_)
  obtain ⟨hv', hw', hvw'⟩ := hω
  obtain ⟨c1, c4, hηt, hηs⟩ := hCa n
  obtain ⟨hd, ho⟩ := ConArg_vec_at sz z s t n ω (v n) (w n) hε₁ hCa0 hK₀.le (hs n) (hst n) (ht n) c1 c4 hηt hηs
    hv' hw' hvw'
  have hρ0 : 0 ≤ etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
      etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) := (div_pos hηs hηt).le
  have hsq : 0 ≤ Real.sqrt (Ca * ((Ca ^ 2 + ε₁⁻¹) * (2 + 2 * Ca) * K₀) * K₀ * ε₁⁻¹) := Real.sqrt_nonneg _
  have hA1 : 0 ≤ (Ca ^ 2 + ε₁⁻¹) * (2 + 2 * Ca) * K₀ := by
    have : 0 < ε₁⁻¹ := inv_pos.mpr hε₁
    positivity
  refine ⟨?_, ?_⟩
  · refine hd.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hρ0
    nlinarith [mul_nonneg hK₀.le hCa0.le]
  · refine ho.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hρ0
    nlinarith [mul_nonneg hK₀.le hCa0.le]

/-- `v^* A v` at a coordinate vector is the diagonal entry. -/
private theorem ConArg_vecEntry_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (q : ι) :
    BAvecEntry A (Pi.single q 1) (Pi.single q 1) = A q q := by
  unfold BAvecEntry
  simp [Matrix.mulVec_single]

/-- The ratio bounds of the shifted parameter: with `η_t = r Im a`, `η_s = Im b`, `η_t ≤ C_a η_s`, `1 ≤ r ≤ c⁻¹`:
`Im a ≤ C_a Im b`, `Im b ≤ c⁻¹ (η_s/η_t) Im a`, `|a - b| ≤ √C_a Im b`, `1 ≤ C_a η_s/η_t`. -/
private theorem ConArg_ratio {a b : ℂ} {r Ca c ηs ηt : ℝ} (hr1 : 1 ≤ r) (hrc : r ≤ c⁻¹) (hCa : 0 < Ca)
    (ha : 0 < a.im) (hb : 0 < b.im) (hab : ‖a - b‖ ^ 2 ≤ Ca * b.im ^ 2) (hηt : ηt = r * a.im)
    (hη : ηs = b.im) (hηts : ηt ≤ Ca * ηs) :
    a.im ≤ Ca * b.im ∧ b.im ≤ (c⁻¹ * (ηs / ηt)) * a.im ∧ ‖a - b‖ ≤ Real.sqrt Ca * b.im ∧
      1 ≤ Ca * (ηs / ηt) := by
  have hηt0 : 0 < ηt := by rw [hηt]; positivity
  have hηs0 : 0 < ηs := by rw [hη]; exact hb
  have hρ0 : 0 < ηs / ηt := div_pos hηs0 hηt0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : a.im ≤ ηt := by rw [hηt]; nlinarith
    rw [← hη]; linarith
  · have e : b.im = (ηs / ηt) * ηt := by rw [← hη]; field_simp
    calc b.im = (ηs / ηt) * ηt := e
      _ = (ηs / ηt) * (r * a.im) := by rw [← hηt]
      _ ≤ (ηs / ηt) * (c⁻¹ * a.im) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrc ha.le) hρ0.le
      _ = (c⁻¹ * (ηs / ηt)) * a.im := by ring
  · rw [show Real.sqrt Ca * b.im = Real.sqrt (Ca * b.im ^ 2) by
      rw [Real.sqrt_mul hCa.le, Real.sqrt_sq hb.le]]
    exact Real.le_sqrt_of_sq_le hab
  · rw [← mul_div_assoc, le_div_iff₀ hηt0]; linarith

/-- `Im tr ((G(+) - G(-)) E_a) = 2 Σ_p bw_a(p) Im G_{pp}` for the `k = 1` loops (`E_a = diag(bw_a)`,
`G(-) = G(+)^*`). -/
private theorem ConArg_loop1_im {d L W : ℕ} [NeZero L] [NeZero W] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H.IsHermitian) (z : ℂ) (a : Zd d L) :
    (loopM d L W H z (fun _ : Fin 1 => true) (fun _ => a) -
        loopM d L W H z (fun _ : Fin 1 => false) (fun _ => a)).im =
      2 * ∑ p, Ind.bw a p * (Gres H z true p p).im := by
  have e : ∀ σ : Bool, loopM d L W H z (fun _ : Fin 1 => σ) (fun _ => a) =
      Matrix.trace (Gres H z σ * Eblk d L W a) := by
    intro σ; simp [loopM, List.ofFn_succ]
  rw [e, e, Ind.Eblk_eq_diagonal_bw, ConArg_Gres_false hH, Matrix.trace, Matrix.trace]
  simp only [diag_apply, mul_diagonal, Matrix.conjTranspose_apply]
  rw [← Finset.sum_sub_distrib, Complex.im_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [Complex.mul_im]
  ring

/-- **Comparison of the `Im`-trace factors** (η-monotonicity + Poisson comparison + scaling, deterministic,
every `ω`): `max_a tr(Im G_s(z_s, g_s) E_a) ≤ C (η_s/η_t) tr(Im G_t(z_t, g₀) E_a)`, written with the `k = 1`
loops of the two carriers as in `BAConArgLoop`.  (Not used by the event form `BAConArgLoop''`: preflight P1.) -/
theorem BAimTrace_compare (d : ℕ) :
    ∀ c κ Λ : ℝ, 0 < c → 0 < κ → 0 < Λ → ∃ C : ℝ, 0 < C ∧
      ∀ (sz : Sizes d) (z : ℕ → ℂ) (s t : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (a : Zd d (sz.L n)),
        0 < (z n).im → c ≤ s n → s n ≤ t n → t n < 1 → |BAflowEs sz z n| ≤ Λ →
        κ ≤ (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n).im →
          ((baFM sz (BAlamS sz z s t) (BAflowEs sz z)).L n (s n) (fun _ : Fin 1 => true) (fun _ => a) ω -
              (baFM sz (BAlamS sz z s t) (BAflowEs sz z)).L n (s n) (fun _ : Fin 1 => false) (fun _ => a) ω).im ≤
            C * ((baFM sz (BAlamS sz z s t) (BAflowEs sz z)).eta n (s n) / (baFMz sz z).eta n (t n)) *
              ((baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω -
                (baFMz sz z).L n (t n) (fun _ : Fin 1 => false) (fun _ => a) ω).im := by
  intro c κ Λ hc hκ hΛ
  obtain ⟨Ca, hCa0, hCa⟩ := BAztTilde_arith c κ Λ hc hκ hΛ
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  refine ⟨(Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹, by positivity, ?_⟩
  intro sz z s t n ω a hz hcs hst ht hE hκm
  have hm0self := ConArg_m0_self sz z n hz
  have hmsself := ConArg_self_of_im_pos sz (BAlamS sz z s t) (BAflowEs sz z) n (lt_of_lt_of_le hκ hκm)
  have hnm0 : ‖BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n‖ ≤ 1 :=
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) hm0self
  have hnms : ‖BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n‖ ≤ 1 :=
    BAself_norm_le_one d (sz.L n) _ _ _ (by simp) hmsself
  obtain ⟨h1, -, -, h4⟩ := hCa (BAflowEs sz z n) (s n) (t n) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)
    (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) hcs hst ht hE hnm0 hnms hκm
  have hs0 : 0 < s n := hc.trans_le hcs
  have hs1 : s n < 1 := hst.trans_lt ht
  have hηt0 : 0 < etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) :=
    mul_pos (by linarith) hm0self.1
  have hηs0 : 0 < etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) :=
    mul_pos (by linarith) (lt_of_lt_of_le hκ hκm)
  obtain ⟨r, a', hr1, hrc, hGt, ha, hb, hab, hηt⟩ := ConArg_setup sz z s t n ω hc hcs hst ht h1 hηt0 hηs0
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  set Hs := sz.seqHflowBA (BAlamS sz z s t) n (s n) ω with hHs
  have hH : Hs.IsHermitian := ConArg_seqHflowBA_isHermitian sz _ n _ ω
  have hHb : (blockMat d (sz.L n) (sz.W n) Hs).IsHermitian := hH.submatrix _
  have hHt : (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω)).IsHermitian :=
    (ConArg_seqHflowBA_isHermitian sz _ n _ ω).submatrix _
  have hbim : (ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n)).im =
      etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) := ztOf_im _ _ _
  obtain ⟨hr1', hr2', hr3', hρ1⟩ := ConArg_ratio hr1 hrc hCa0 ha hb hab hηt hbim.symm h4
  set ρ := etaOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (s n) /
    etaOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (t n) with hρ
  have hρ0 : 0 ≤ ρ := (div_pos hηs0 hηt0).le
  set zs := ztOf (BAmF sz (BAlamS sz z s t) (BAflowEs sz z) n) (BAflowEs sz z n) (s n) with hzs
  set zz := ztOf (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) (BAflowEs sz z n) (t n) with hzz
  set Ht := sz.seqHflowBA (BAflowLam0 sz z) n (t n) ω with hHt'
  -- the pointwise comparison of the diagonal entries (`G_s(z_s)_{qq}` against `G_t(z_t)_{qq}`)
  have hpt : ∀ q : Idx d (sz.L n) (sz.W n), (Gres Hs zs true q q).im ≤
      (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ * (Gres Ht zz true q q).im := by
    intro q
    obtain ⟨-, hd2⟩ := ConArg_diag_both hH (Pi.single q 1) ha hb (Real.sqrt_nonneg Ca) hr3' hr1' hr2'
    rw [Real.sq_sqrt hCa0.le] at hd2
    rw [ConArg_vecEntry_single, ConArg_vecEntry_single] at hd2
    have hGtq : Gres Ht zz true q q = ((r : ℂ))⁻¹ * Gres Hs a' true q q := by
      have := congrFun (congrFun hGt q) q
      exact this
    have hcinv : ((r : ℂ))⁻¹ = ((r⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv]
    have hGim : (Gres Ht zz true q q).im = r⁻¹ * (Gres Hs a' true q q).im := by
      rw [hGtq, hcinv, Complex.im_ofReal_mul]
    have hga0 : 0 ≤ (Gres Hs a' true q q).im := by
      have := ConArg_imG_nonneg' hH (Pi.single q 1) ha
      rwa [ConArg_vecEntry_single] at this
    have hGt0 : 0 ≤ (Gres Ht zz true q q).im := by
      rw [hGim]; exact mul_nonneg (inv_nonneg.mpr hr0.le) hga0
    have hga : (Gres Hs a' true q q).im ≤ c⁻¹ * (Gres Ht zz true q q).im := by
      have : (Gres Hs a' true q q).im = r * (Gres Ht zz true q q).im := by
        rw [hGim]; field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_right hrc hGt0
    have hE : Ca + c⁻¹ * ρ ≤ (Ca ^ 2 + c⁻¹) * ρ := by nlinarith [mul_le_mul_of_nonneg_left hρ1 hCa0.le]
    calc (Gres Hs zs true q q).im ≤ (Ca + c⁻¹ * ρ) * ((2 + 2 * Ca) * (Gres Hs a' true q q).im) := hd2
      _ ≤ ((Ca ^ 2 + c⁻¹) * ρ) * ((2 + 2 * Ca) * (c⁻¹ * (Gres Ht zz true q q).im)) := by
          refine mul_le_mul hE (mul_le_mul_of_nonneg_left hga (by positivity)) ?_ (by positivity)
          exact mul_nonneg (by positivity) hga0
      _ = (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ * (Gres Ht zz true q q).im := by ring
  -- the loops
  have eS : ∀ σ : Bool, (baFM sz (BAlamS sz z s t) (BAflowEs sz z)).L n (s n) (fun _ : Fin 1 => σ) (fun _ => a) ω =
      loopM d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) Hs) zs (fun _ => σ) (fun _ => a) := fun σ => rfl
  have eT : ∀ σ : Bool, (baFMz sz z).L n (t n) (fun _ : Fin 1 => σ) (fun _ => a) ω =
      loopM d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) Ht) zz (fun _ => σ) (fun _ => a) := fun σ => rfl
  have hη : (baFM sz (BAlamS sz z s t) (BAflowEs sz z)).eta n (s n) / (baFMz sz z).eta n (t n) = ρ := rfl
  rw [eS true, eS false, eT true, eT false, ConArg_loop1_im hHb zs a, ConArg_loop1_im hHt zz a, hη]
  simp only [ConArg_gres_blockMat_true]
  have hbw : ∀ x : Vtx d (sz.L n) (sz.W n), 0 ≤ Ind.bw a x := fun x => Ind.bw_nonneg a x
  have hsum : ∑ x, Ind.bw a x * (Gres Hs zs true ((splitEquiv d (sz.L n) (sz.W n)).symm x)
        ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im ≤
      ∑ x, Ind.bw a x * ((Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ *
        (Gres Ht zz true ((splitEquiv d (sz.L n) (sz.W n)).symm x)
          ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im) :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt _) (hbw x)
  have hrhs : ∑ x, Ind.bw a x * ((Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ *
        (Gres Ht zz true ((splitEquiv d (sz.L n) (sz.W n)).symm x)
          ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im) =
      (Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ * ∑ x, Ind.bw a x * (Gres Ht zz true
        ((splitEquiv d (sz.L n) (sz.W n)).symm x) ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring
  rw [hrhs] at hsum
  calc _ ≤ 2 * ((Ca ^ 2 + c⁻¹) * (2 + 2 * Ca) * c⁻¹ * ρ * ∑ x, Ind.bw a x * (Gres Ht zz true
        ((splitEquiv d (sz.L n) (sz.W n)).symm x) ((splitEquiv d (sz.L n) (sz.W n)).symm x)).im) := by linarith
    _ = _ := by ring

/-! ## 7. `lem_ConArg_BA` in the event form -/

/-- **`lem_ConArg_BA` (`7_8:1956-1987`), event form, for every `d`** (target 1 of T2237 with Amend 1): conjunct 1
`baConArgLoop''_holds` and conjunct 2 `baConArgVec_holds`.  The merged pin `BAConArg'` (the `Φ_t` form) is not proved:
it needs a lower bound on `Φ_s` that the premises do not give (T2237a). -/
theorem baConArg''_holds (d : ℕ) : BAConArg'' d := by
  intro κ ε 𝔡 ε₁ hκ hε h𝔡 hε₁ 𝔠 sz z hflow s t hs hst ht hκm hL C₀ hC₀
  have hyp : BAConArgHyp κ ε 𝔡 ε₁ 𝔠 sz z s t := ⟨hκ, hε, h𝔡, hε₁, hflow, hs, hst, ht, hκm, hL⟩
  exact ⟨fun k hk => baConArgLoop''_holds d κ ε 𝔡 ε₁ 𝔠 sz z s t hyp C₀ hC₀ k hk,
    baConArgVec_holds d κ ε 𝔡 ε₁ 𝔠 sz z s t hyp⟩

end RBM.BA

/-! ## 8. Compiled nonempty instances (`RBM.BA.ConArgInst`)

The size data are the merged preflight sequence `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `g_n = (2(n+1))^{-6}`;
`n = 0`: `L = 4`, `W = 32`, `g = 1/64`, `N = 2097152`), the spectral parameters `zSeq` (`z_S(L_n, g_n)`,
`11/30 ≤ Im z_n ≤ 7/10`, `BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` is `flow_sz0`), `κ = ε₁ = 1/2`,
`ε = 𝔡 = 1/10`, `𝔠 = 1/6`, `s ≡ t ≡ 1/2` (so `κ ≤ Im m(E, g_s)` is `inst_premise_diag`); every deterministic hypothesis
is discharged.  What stays a hypothesis of an instance is the loop bound `(eq:loopbound_s)` at `s`
(`STLmaxgL` at the carrier of `g_s`: the BA chain, owed).  The `s < t` instances are BA-S3's (`sz0` has `t₀ ≥ 2/3`). -/

namespace RBM.BA.ConArgInst

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

/-- The hypothesis bundle `BAConArgHyp` at the data, up to the loop bound. -/
theorem inst_BAConArgHyp (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2))
        (BAflowEs sz0 zSeq)) (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    BAConArgHyp (1 / 2) (1 / 10) (1 / 10) (1 / 2) (1 / 6) sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num, flow_sz0, fun _ => le_rfl, fun _ => le_rfl,
    fun _ => by norm_num, inst_premise_diag, hL⟩

/-- **Instance of `baConArg''_holds`** (target 1): `sz0`, `zSeq`, `κ = ε₁ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`s ≡ t ≡ 1/2`, `C₀ = 2`; only `(eq:loopbound_s)` at `s` is a hypothesis. -/
theorem inst_baConArg''
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    (∀ k : ℕ, 2 ≤ k →
        BAConArgLoop'' sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) k 2) ∧
      BAConArgVec sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  baConArg''_holds 3 (1 / 2) (1 / 10) (1 / 10) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => le_rfl) (fun _ => le_rfl)
    (fun _ => by norm_num) inst_premise_diag hL 2 (by norm_num)

/-- **Instance of `baConArgLoop''_holds`** (conjunct 1) at every threshold `C₀ > 0` and loop length `k ≥ 2`. -/
theorem inst_baConArgLoop''
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2))
    (C₀ : ℝ) (hC₀ : 0 < C₀) (k : ℕ) (hk : 2 ≤ k) :
    BAConArgLoop'' sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) k C₀ :=
  baConArgLoop''_holds 3 (1 / 2) (1 / 10) (1 / 10) (1 / 2) (1 / 6) sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)
    (inst_BAConArgHyp hL) C₀ hC₀ k hk

/-- **Instance of `baConArgVec_holds`** (conjunct 2). -/
theorem inst_baConArgVec
    (hL : STLmaxgL (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq))
      (Sizes.seqP (sz0.withLam 0)) (fun _ => 1 / 2)) :
    BAConArgVec sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) :=
  baConArgVec_holds 3 (1 / 2) (1 / 10) (1 / 10) (1 / 2) (1 / 6) sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)
    (inst_BAConArgHyp hL)

/-- **Instance of `bandFM_omegaC`**: `sz0`, `E ≡ 0`, `t = 1/2`, `C₀ = 2`, every `n` and `ω`. -/
example (n : ℕ) (ω : sz0.SeqΩ) :
    (bandFM sz0 (fun _ => 0)).omegaC n (1 / 2) 2 ω = Sizes.STomegaC sz0 n 0 (1 / 2) 2 ω :=
  bandFM_omegaC sz0 (fun _ => 0) n (1 / 2) 2 ω

/-- **Instance of `BAhflow_scale`** with `s < t`: `sz0`, `n = 0`, `s ≡ 1/2`, `t ≡ 3/4`, every sample `ω`:
`H_t(g₀) = √(3/2) · H_s(g_s)`, `g_s = √(2/3) g₀`. -/
theorem inst_hflow_scale (ω : sz0.SeqΩ) :
    sz0.seqHflowBA (BAflowLam0 sz0 zSeq) 0 ((fun _ => (3 / 4 : ℝ)) 0) ω =
      ((Real.sqrt ((fun _ => (3 / 4 : ℝ)) 0 / (fun _ => (1 / 2 : ℝ)) 0) : ℝ) : ℂ) •
        sz0.seqHflowBA (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 4)) 0 ((fun _ => (1 / 2 : ℝ)) 0) ω :=
  BAhflow_scale 3 sz0 zSeq (fun _ => 1 / 2) (fun _ => 3 / 4) 0 ω (by norm_num) (by norm_num)

/-- **Instance of `BAGres_smul`**: the Hermitian `2 × 2` matrix `diag(1, -1)`, `w = i`, `r = 2`, both charges. -/
example (σ : Bool) :
    Gres (((2 : ℝ) : ℂ) • (Matrix.diagonal ![(1 : ℂ), -1])) (((2 : ℝ) : ℂ) * Complex.I) σ =
      (((2 : ℝ) : ℂ))⁻¹ • Gres (Matrix.diagonal ![(1 : ℂ), -1]) Complex.I σ :=
  BAGres_smul (Fin 2) _ _ σ 2 (by norm_num)

/-- `diag(1, -1)` is Hermitian. -/
private theorem herm_diag : (Matrix.diagonal ![(1 : ℂ), -1]).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]

/-- **Instance of `BAimG_eta_mono`**: `H = diag(1, -1)`, `v = e₀`, `x = 0`, `y = 1 ≤ y' = 2`. -/
example :
    1 * (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) true)
        (Pi.single 0 1) (Pi.single 0 1)).im ≤
      2 * (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((0 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * Complex.I) true)
        (Pi.single 0 1) (Pi.single 0 1)).im ∧
    (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((0 : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * Complex.I) true)
        (Pi.single 0 1) (Pi.single 0 1)).im / 2 ≤
      (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) true)
        (Pi.single 0 1) (Pi.single 0 1)).im / 1 :=
  BAimG_eta_mono (Fin 2) (Matrix.diagonal ![(1 : ℂ), -1]) (Pi.single 0 1) 0 1 2 herm_diag one_pos (by norm_num)

/-- **Instance of `BAimG_poisson`**: `H = diag(1, -1)`, `v = e₀`, `x = 0`, `x' = 1`, `y = 1`, `C = 1`. -/
example :
    (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((0 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) true)
        (Pi.single 0 1) (Pi.single 0 1)).im ≤
      (2 + 2 * (1 : ℝ) ^ 2) *
        (BAvecEntry (Gres (Matrix.diagonal ![(1 : ℂ), -1]) (((1 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I) true)
          (Pi.single 0 1) (Pi.single 0 1)).im :=
  BAimG_poisson (Fin 2) (Matrix.diagonal ![(1 : ℂ), -1]) (Pi.single 0 1) 0 1 1 1 herm_diag one_pos zero_le_one
    (by norm_num)

/-- **Instance of `BAself_norm_le_one`** at the flow point `P` of `(L, g) = (4, 10)` (`BASelf 3 4 P.g₀ P.E P.m₀`). -/
example : ‖RBM.BA.MFixedPointInst.P.m0‖ ≤ 1 :=
  BAself_norm_le_one 3 4 RBM.BA.MFixedPointInst.P.g0 (RBM.BA.MFixedPointInst.P.E : ℂ)
    RBM.BA.MFixedPointInst.P.m0 (by simp) RBM.BA.MFixedPointInst.P.real.1

/-- **Instance of `BAenergy_le`** at `(d, L, g, E) = (3, 4, P.g₀, P.E)`: `Im m(E, g₀) > 0` there. -/
example : |RBM.BA.MFixedPointInst.P.E| ≤ 2 + 2 * ((3 : ℕ) : ℝ) * |RBM.BA.MFixedPointInst.P.g0| :=
  BAenergy_le 3 4 RBM.BA.MFixedPointInst.P.g0 RBM.BA.MFixedPointInst.P.E (by
    rw [BAm_real_eq_of_self 3 4 _ _ _ RBM.BA.MFixedPointInst.P.real.1]
    exact RBM.BA.MFixedPointInst.P.real.1.1)

/-- **Instance of `BAztTilde_arith`** at `(c, κ, Λ) = (1/2, 1/2, 62)` and the data `E = 1/10`, `s = 1/2`,
`t = 3/4`, `m₀ = 1/10 + i/2`, `m_s = i` (`‖m₀‖² = 0.26`, `‖m_s‖ = 1`, `κ ≤ Im m_s`). -/
example : ∃ C : ℝ, 0 < C ∧
    ‖ztOf ((1 / 10 : ℝ) + (1 / 2 : ℝ) * Complex.I) (1 / 10) (3 / 4) -
        (Real.sqrt ((3 / 4) / (1 / 2)) : ℂ) * ztOf Complex.I (1 / 10) (1 / 2)‖ ^ 2 ≤ C * etaOf Complex.I (1 / 2) ^ 2 ∧
      etaOf Complex.I (1 / 2) ≤ ((Real.sqrt ((3 / 4) / (1 / 2)) : ℂ) * ztOf Complex.I (1 / 10) (1 / 2)).im ∧
      ((Real.sqrt ((3 / 4) / (1 / 2)) : ℂ) * ztOf Complex.I (1 / 10) (1 / 2)).im ≤ C * etaOf Complex.I (1 / 2) ∧
      etaOf ((1 / 10 : ℝ) + (1 / 2 : ℝ) * Complex.I) (3 / 4) ≤ C * etaOf Complex.I (1 / 2) := by
  obtain ⟨C, hC, h⟩ := BAztTilde_arith (1 / 2) (1 / 2) 62 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, h (1 / 10) (1 / 2) (3 / 4) _ Complex.I (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [abs_of_pos]) ?_ (by simp) (by norm_num)⟩
  rw [Complex.norm_def, Complex.normSq_apply]
  simp
  norm_num

/-- **Instance of `BAimTrace_compare`**: `sz0`, `zSeq`, `s ≡ t ≡ 1/2`, `n = 0`, every sample `ω` and block `a`,
`(c, κ, Λ) = (1/2, 1/2, 5)` (`|E_0| ≤ 2 + 6/64`). -/
theorem inst_imTrace (ω : sz0.SeqΩ) (a : Zd 3 (sz0.L 0)) :
    ∃ C : ℝ, 0 < C ∧
      ((baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq)).L 0 (1 / 2)
            (fun _ : Fin 1 => true) (fun _ => a) ω -
          (baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq)).L 0 (1 / 2)
            (fun _ : Fin 1 => false) (fun _ => a) ω).im ≤
        C * ((baFM sz0 (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2)) (BAflowEs sz0 zSeq)).eta 0 (1 / 2) /
            (baFMz sz0 zSeq).eta 0 (1 / 2)) *
          ((baFMz sz0 zSeq).L 0 (1 / 2) (fun _ : Fin 1 => true) (fun _ => a) ω -
            (baFMz sz0 zSeq).L 0 (1 / 2) (fun _ : Fin 1 => false) (fun _ => a) ω).im := by
  obtain ⟨C, hC, h⟩ := BAimTrace_compare 3 (1 / 2) (1 / 2) 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, h sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) 0 ω a (zSeq_im_pos 0) le_rfl le_rfl
    (by norm_num) ?_ (inst_premise_diag 0)⟩
  have h1 := BAenergy_le 3 (sz0.L 0) (BAlamS sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) 0) (BAflowEs sz0 zSeq 0)
    (lt_of_lt_of_le (by norm_num) (inst_premise_diag 0))
  have h2 := ConArg_lamS_abs_le sz0 zSeq (fun _ => 1 / 2) (fun _ => 1 / 2) 0 (zSeq_im_pos 0) (by norm_num) le_rfl
  have h3 : |sz0.lam 0| = 1 / 64 := by rw [sz0_values.2.2.2]; norm_num
  rw [h3] at h2
  have h4 : |BAflowEs sz0 zSeq 0| ≤ 2 + 2 * ((3 : ℕ) : ℝ) * (1 / 64) := by
    refine h1.trans ?_
    have : (0 : ℝ) ≤ ((3 : ℕ) : ℝ) := Nat.cast_nonneg 3
    nlinarith
  refine h4.trans ?_
  norm_num

end RBM.BA.ConArgInst

end
