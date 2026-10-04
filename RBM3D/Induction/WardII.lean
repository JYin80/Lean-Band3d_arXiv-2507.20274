/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step5Cases
import RBM3D.Induction.ConArgDet
import RBM3D.Loop.KLWard

/-!
# S5-28 (ST-4): the Ward term `(zYU1)` of case (ii) of Step 5

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex:2257-2262`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

section Det

variable {d L W : ℕ} [NeZero L] {H : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}

private theorem wardII_loopL_rot (s t : Bool) (b a : Zd d L) :
    loopL d L W H z ⟨[s, t], [b, a]⟩ = loopL d L W H z ⟨[t, s], [a, b]⟩ := by
  simp only [loopL, List.zip_cons_cons, List.zip_nil_left, List.foldr_cons, List.foldr_nil,
    Matrix.mul_one]
  exact Matrix.trace_mul_comm _ _

private theorem wardII_loopL_conj (a b : Zd d L) :
    loopL d L W H ((starRingEnd ℂ) z) ⟨[true, false], [a, b]⟩ =
      loopL d L W H z ⟨[false, true], [a, b]⟩ := by
  simp [loopL, Gres]

private theorem wardII_loopL_one (s : Bool) (a : Zd d L) :
    loopL d L W H z ⟨[s], [a]⟩ = Matrix.trace (green H (RBM.Ind.zSig z s) * Eblk d L W a) := by
  simp [loopL, ← RBM.Ind.Gres_eq_green_zSig]

/-- `(WI_calL)` at `n = 2`, summed over the FIRST label, both charge orders. -/
private theorem wardII_sum (hH : H.IsHermitian) (hz : z.im ≠ 0) (s : Bool) (a : Zd d L) :
    (2 * Complex.I * (z.im : ℂ)) * ∑ c : Zd d L, loopL d L W H z ⟨[s, !s], [c, a]⟩ =
      (((W : ℂ) ^ d)⁻¹) * (loopL d L W H z ⟨[true], [a]⟩ - loopL d L W H z ⟨[false], [a]⟩) := by
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  have hu' := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH
    (z := (starRingEnd ℂ) z) (by simpa using hz)
  have h1 := wardII_loopL_one (H := H) (z := z) true a
  have h2 := wardII_loopL_one (H := H) (z := z) false a
  simp only [RBM.Ind.zSig_true, RBM.Ind.zSig_false] at h1 h2
  rw [h1, h2]
  cases s with
  | false =>
    simp only [Bool.not_false]
    simp_rw [wardII_loopL_rot (H := H) (z := z) false true]
    exact sum_gloop_two_ward d L W hu hu' a
  | true =>
    simp only [Bool.not_true]
    simp_rw [wardII_loopL_rot (H := H) (z := z) true false]
    simp_rw [← wardII_loopL_conj (H := H) (z := z)]
    have h := sum_gloop_two_ward d L W (H := H) (z := (starRingEnd ℂ) z) hu' (by simpa using hu) a
    simp only [Complex.conj_conj, Complex.conj_im, Complex.ofReal_neg] at h
    linear_combination -h

private theorem wardII_green_conj (hH : H.IsHermitian) (hz : z.im ≠ 0) :
    green H ((starRingEnd ℂ) z) = (green H z)ᴴ := by
  have hH' : Hᴴ = H := hH
  have hu := RBM.Ind.isUnit_sub_smul_one_of_im_ne_zero hH hz
  simp only [green, Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hH', Complex.star_def]

omit [NeZero L] in
private theorem wardII_Eblk_conjTranspose (a : Zd d L) : (Eblk d L W a)ᴴ = Eblk d L W a := by
  unfold Eblk
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext x
  by_cases h : x.1 = a <;> simp [h]

/-- `𝓛^{(1)}_{-} = conj 𝓛^{(1)}_{+}` for Hermitian `H`. -/
private theorem wardII_one_conj (hH : H.IsHermitian) (hz : z.im ≠ 0) (a : Zd d L) :
    loopL d L W H z ⟨[false], [a]⟩ = (starRingEnd ℂ) (loopL d L W H z ⟨[true], [a]⟩) := by
  have h1 := wardII_loopL_one (H := H) (z := z) true a
  have h2 := wardII_loopL_one (H := H) (z := z) false a
  simp only [RBM.Ind.zSig_true, RBM.Ind.zSig_false] at h1 h2
  rw [h1, h2, wardII_green_conj hH hz]
  have : (starRingEnd ℂ) (Matrix.trace (green H z * Eblk d L W a)) =
      Matrix.trace ((green H z)ᴴ * Eblk d L W a) := by
    have h := Matrix.trace_conjTranspose (green H z * Eblk d L W a)
    rw [Matrix.conjTranspose_mul, wardII_Eblk_conjTranspose, Matrix.trace_mul_comm] at h
    simpa [Complex.star_def] using h.symm
  rw [this]

end Det

section Identity

variable {d : ℕ} (sz : Sizes d)

private theorem wardII_STLM_eq (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STLM sz n E u H σ a =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u) ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  unfold STLM loopFine
  rw [loopM_eq_loopL]
  simp [loopOf, List.ofFn_succ]

private theorem wardII_STLM_eq1 (n : ℕ) (E u : ℝ) (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (s : Bool) (a : Zd d (sz.L n)) :
    STLM sz n E u H (fun _ : Fin 1 => s) (fun _ => a) =
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u) ⟨[s], [a]⟩ := by
  unfold STLM loopFine
  rw [loopM_eq_loopL]
  simp [loopOf, List.ofFn_succ]

private theorem wardII_STKloop_eq (n : ℕ) (E u : ℝ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a = KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
  simp [STKloop, KLloopOf, List.ofFn_succ]

private theorem wardII_STKloop_eq1 (n : ℕ) (E u : ℝ) (s : Bool) (a : Zd d (sz.L n)) :
    STKloop sz n E u (fun _ : Fin 1 => s) (fun _ => a) =
      KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨[s], [a]⟩ := by
  simp [STKloop, KLloopOf, List.ofFn_succ]

private theorem wardII_zeroMode (n : ℕ) (T : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    T a - zeroModeSet d (sz.L n) {0} T a =
      ((((sz.L n : ℕ) : ℂ) ^ d)⁻¹) * ∑ c : Zd d (sz.L n), T ![c, a 1] := by
  have hup : ∀ c : Zd d (sz.L n), Function.update a 0 c = ![c, a 1] := by
    intro c
    funext i
    fin_cases i <;> simp
  simp only [zeroModeSet, Finset.toList_singleton, List.foldr_cons, List.foldr_nil, zeroModeOp, avgOp, hup]
  ring

/-- **`(WI_calL)` and `(WI_calK)` summed over the first label, `(zYU1)` of `3_5:2257-2262`** (deterministic, every Hermitian `H`, `σ₁ ≠ σ₂`,
`0 ≤ u < 1`, `|E| < 2`): `(𝓛-𝒦)^{(2)}_{u,σ,a} - [Q^{(1)} ∘ (𝓛-𝒦)^{(2)}_{u,σ}]_a = Im(𝓛-𝒦)^{(1)}_{u,+,a₂} / (N η_u)`, `N = (WL)^d`. -/
theorem stWardII_identity (n : ℕ) {E u : ℝ} (hE : |E| < 2) (hu0 : 0 ≤ u) (hu1 : u < 1)
    {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ} (hH : H.IsHermitian)
    {σ : Fin 2 → Bool} (hσ : σ 0 ≠ σ 1) (a : Fin 2 → Zd d (sz.L n)) :
    STLKM sz n E u H σ a - zeroModeSet d (sz.L n) {0} (fun a' => STLKM sz n E u H σ a') a =
      (((STLKM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) /
        ((((sz.size n : ℕ) : ℂ)) * (etaT E u : ℂ)) := by
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have hη : 0 < etaT E u := etaT_pos hE hu1
  have hz : (zt E u).im ≠ 0 := by rw [← etaT_eq_zt_im]; exact hη.ne'
  have hHb : (blockMat d (sz.L n) (sz.W n) H).IsHermitian := hH.submatrix _
  have hσ1 : σ 1 = !σ 0 := (by decide : ∀ x y : Bool, x ≠ y → y = !x) _ _ hσ
  set s := σ 0 with hs
  rw [wardII_zeroMode sz n _ a]
  -- the two sums
  have hKsum : ∑ c : Zd d (sz.L n), STKloop sz n E u σ ![c, a 1] =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (mSigma E true - mSigma E false) := by
    have hrot : ∀ c : Zd d (sz.L n), STKloop sz n E u σ ![c, a 1] =
        KLK d (sz.L n) (sz.lam n) (sz.W n) E u ⟨[!s, s], [a 1, c]⟩ := by
      intro c
      rw [wardII_STKloop_eq, hσ1]
      exact KLK_rotate d (sz.L n) (sz.W n) (sz.lam n) E hL3 hW1 hE u ⟨hu0, hu1⟩ s c [!s] [a 1] rfl
    simp_rw [hrot]
    have h := KLward_two d (sz.L n) (sz.lam n) hL3 (sz.W n) hW1 hE (t := u) ⟨hu0, hu1⟩ (!s) (a 1)
    rw [Bool.not_not] at h
    rw [h]
    simp only [KLK_one]
  have hLsum : ∑ c : Zd d (sz.L n), STLM sz n E u H σ ![c, a 1] =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        (STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) -
          STLM sz n E u H (fun _ : Fin 1 => false) (fun _ => a 1)) := by
    have hw := wardII_sum (H := blockMat d (sz.L n) (sz.W n) H) (z := zt E u) hHb hz s (a 1)
    have hrw : ∀ c : Zd d (sz.L n), STLM sz n E u H σ ![c, a 1] =
        loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) H) (zt E u) ⟨[s, !s], [c, a 1]⟩ := by
      intro c
      rw [wardII_STLM_eq, hσ1]
      rfl
    simp_rw [hrw, wardII_STLM_eq1]
    rw [← etaT_eq_zt_im] at hw
    have hW0 : ((sz.W n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show sz.W n ≠ 0 by omega)
    have hη0 : (etaT E u : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    field_simp
    field_simp at hw
    linear_combination hw
  have hsum : ∑ c : Zd d (sz.L n), STLKM sz n E u H σ ![c, a 1] =
      (2 * Complex.I * ((sz.W n : ℕ) : ℂ) ^ d * (etaT E u : ℂ))⁻¹ *
        ((STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) -
          STLM sz n E u H (fun _ : Fin 1 => false) (fun _ => a 1)) -
         (mSigma E true - mSigma E false)) := by
    simp only [STLKM, Finset.sum_sub_distrib, hLsum, hKsum]
    ring
  have hconj : STLM sz n E u H (fun _ : Fin 1 => false) (fun _ => a 1) =
      (starRingEnd ℂ) (STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1)) := by
    rw [wardII_STLM_eq1, wardII_STLM_eq1]
    exact wardII_one_conj hHb hz (a 1)
  have hm : mSigma E false = (starRingEnd ℂ) (mSigma E true) := by simp [mSigma]
  have hX : (STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) -
          STLM sz n E u H (fun _ : Fin 1 => false) (fun _ => a 1)) -
         (mSigma E true - mSigma E false) =
      2 * Complex.I * (((STLKM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1)).im : ℝ) : ℂ) := by
    have h := Complex.sub_conj (STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) - mSigma E true)
    rw [map_sub] at h
    have hK : STLKM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) =
        STLM sz n E u H (fun _ : Fin 1 => true) (fun _ => a 1) - mSigma E true := by
      simp only [STLKM, wardII_STKloop_eq1, KLK_one]
    rw [hK, hconj, hm]
    push_cast at h
    linear_combination h
  rw [hsum, hX]
  have hW0 : ((sz.W n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show sz.W n ≠ 0 by omega)
  have hL0 : ((sz.L n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show sz.L n ≠ 0 by omega)
  have hη0 : (etaT E u : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hN : (((sz.size n : ℕ)) : ℂ) = ((sz.W n : ℕ) : ℂ) ^ d * ((sz.L n : ℕ) : ℂ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  rw [hN]
  field_simp

end Identity

section Chain

variable {d : ℕ} (sz : Sizes d)

/-- `W^{-d} B_{u,0} ≤ 2 A⁻¹` in regime (ii): `1 - u ≥ ilambda²/L^d` gives `(L^d (1-u))⁻¹ ≤ ilambda⁻²`
and `(ilambda² + 1 - u)⁻¹ ≤ ilambda⁻²`; `(3_5:2259`, `Δ_u ≍ A⁻¹`). -/
private theorem wardII_Bctl_le (n : ℕ) (hlam : 0 < sz.lam n) {u : ℝ} (hu : u < 1)
    (hx : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ d ≤ 1 - u) :
    sz.Bctl n u ≤ 2 * (STAI sz n)⁻¹ := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by have := sz.three_le_L n; omega)
  have hLd : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) ^ d := by positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hx0 : 0 < 1 - u := lt_of_lt_of_le (by positivity) hx
  unfold Sizes.Bctl Bparam STAI
  rw [abs_of_pos hx0]
  have h0 : (((0 : ℕ) : ℝ) + 1) ^ (d - 2) = 1 := by simp
  rw [h0, inv_one, mul_one]
  have h1 : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ :=
    inv_anti₀ hg2 (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := by
    apply inv_anti₀ hg2
    have := (div_le_iff₀ hLd).1 hx
    linarith
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ + (sz.lam n ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = 2 * (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [mul_inv]; ring

/-- A positive deterministic factor passes through `≺`: `ξ ≤ c ξ'`, `ξ' ≺ ζ` give `ξ ≺ c ζ`. -/
private theorem wardII_prec_scale {U : ℕ → Type*} {ξ ξ' ζ : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ}
    (hc : ∀ n p, 0 < c n p) (h : sz.Prec ξ' ζ) (hle : ∀ n p ω, ξ n p ω ≤ c n p * ξ' n p ω) :
    sz.Prec ξ (fun n p ω => c n p * ζ n p ω) := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Filter.Eventually.of_forall fun n ω ⟨u, hu⟩ => ⟨u, ?_⟩⟩
  have h1 : c n u * (((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) < c n u * ξ' n u ω := by
    calc c n u * (((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω) = ((sz.size n : ℕ) : ℝ) ^ τ * (c n u * ζ n u ω) := by ring
      _ < ξ n u ω := hu
      _ ≤ c n u * ξ' n u ω := hle n u ω
  exact lt_of_mul_lt_mul_left h1 (hc n u).le

/-- **`(zYU1)`** (`3_5:2257-2262`), case (ii) of Step 5, `σ₁ ≠ σ₂`: the pin `STWardII d` (Ward's identities
`(WI_calL)`, `(WI_calK)` through `stWardII_identity`, and `(Gt_avgbound_flow)`, i.e. `STAvgU` inside `STStep2Concl`,
with `W^{-d}B_{u,0} ≤ 2 A⁻¹` in regime (ii)). -/
theorem stWardII_holds (d : ℕ) : STWardII d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst ht hR hKb hKw hLK hDec hDecS hcon hS1 hS2 hLmax hLKU
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := st5_t_lt_one sz hflow ht
  have hev := st5_eventually_A_ge_one sz hflow.1.2.1 hflow.1.2.2.2.2
  have hE2 : ∀ n, |STflowE z n| < 2 := fun n => by
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have him : 0 < (z n).im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) (hflow.2 n).2.1
    have := (lemma28_quant hκ him (hflow.2 n).2.2 (hflow.2 n).1).1
    have h' : |lemE (z n)| ≤ 2 - κ := this
    change |lemE (z n)| < 2
    linarith
  have hu0 : ∀ n (u : TimeIcc s t n), 0 ≤ (u : ℝ) := fun n u => (hs0 n).trans u.2.1
  have hu1 : ∀ n (u : TimeIcc s t n), (u : ℝ) < 1 := fun n u => lt_of_le_of_lt u.2.2 (ht1 n)
  -- the averaged local law, pulled back to the index set `(u, σ, a)`
  have hpre := StochDomAt.precomp_param hS2.2.1
    (fun n (p : STIdx2P sz STSigMixed s t n) =>
      ((p.1, (fun _ : Fin 1 => true), (fun _ : Fin 1 => p.2.2 1)) :
        TimeIcc s t n × (Fin 1 → Bool) × (Fin 1 → Zd d (sz.L n))))
  have hscale := wardII_prec_scale sz (U := STIdx2P sz STSigMixed s t)
    (ξ := fun n p ω => ‖STLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 p.2.2 -
      zeroModeSet d (sz.L n) {0}
        (fun a' => STLKM sz n (STflowE z n) (p.1 : ℝ) (sz.seqHflow n (p.1 : ℝ) ω) p.2.1.1 a') p.2.2‖)
    (c := fun n p => (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) (p.1 : ℝ))⁻¹)
    (fun n p => by
      have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      exact inv_pos.2 (mul_pos hN (etaT_pos (hE2 n) (hu1 n p.1))))
    hpre
    (fun n p ω => by
      have hid := stWardII_identity sz n (hE2 n) (hu0 n p.1) (hu1 n p.1)
        (sz.seqHflow_isHermitian n (p.1 : ℝ) ω) p.2.1.2 p.2.2
      have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hη := etaT_pos (hE2 n) (hu1 n p.1)
      rw [hid, norm_div, Complex.norm_real, Complex.norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_of_nonneg hη.le]
      rw [div_eq_mul_inv, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (mul_pos hN hη).le)
      rw [Real.norm_eq_abs]
      exact (Complex.abs_im_le_norm _).trans le_rfl)
  refine st5_prec_mono sz hsz (c := 2) hscale ?_ ?_
  · filter_upwards [hev] with n hn
    intro p ω
    have hB := wardII_Bctl_le sz n hn.1 (hu1 n p.1) (by linarith [(hR n).1, ht1 n, p.1.2.2, hst n])
    have hc : 0 ≤ (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) (p.1 : ℝ))⁻¹ := by
      have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      exact inv_nonneg.2 (mul_pos hN (etaT_pos (hE2 n) (hu1 n p.1))).le
    change (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) (p.1 : ℝ))⁻¹ * (sz.Bctl n (p.1 : ℝ)) ^ 1 ≤
      2 * ((STAI sz n)⁻¹ * (((sz.size n : ℕ) : ℝ) * etaT (STflowE z n) (p.1 : ℝ))⁻¹)
    rw [pow_one]
    nlinarith [mul_le_mul_of_nonneg_left hB hc]
  · intro n p ω
    have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hη := etaT_pos (hE2 n) (hu1 n p.1)
    exact mul_nonneg (inv_nonneg.2 (st5_STAI_nonneg sz n)) (inv_nonneg.2 (mul_pos hN hη).le)

end Chain

/-! ## Compiled nonempty instances -/

/-- `d = 3`, `L = 3`, `W = 1` (`N = (WL)^d = 27`), `ilambda = 1`: the data of the identity instance. -/
private def wardII_szI : Sizes 3 where
  L := fun _ => 3
  W := fun _ => 1
  lam := fun _ => 1
  three_le_L := fun _ => le_rfl
  W_pos := fun _ => Nat.one_pos

/-- The identity `stWardII_identity` at `d = 3`, `L = 3`, `W = 1`, `E = 0`, `u = 1/2`, the Hermitian `H = 1` of the
`27 × 27` matrices, `σ = (+,-)`, `a = (0, e₁)`: every hypothesis (`|E| < 2`, `0 ≤ u < 1`, `H` Hermitian, `σ₁ ≠ σ₂`) is
discharged. -/
example :
    STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ) ![true, false]
        ![(0 : Zd 3 3), ![1, 0, 0]] -
      zeroModeSet 3 3 {0} (fun a' => STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)
        ![true, false] a') ![(0 : Zd 3 3), ![1, 0, 0]] =
      (((STLKM wardII_szI 0 (0 : ℝ) (1 / 2 : ℝ) (1 : Matrix (Idx 3 3 1) (Idx 3 3 1) ℂ)
          (fun _ : Fin 1 => true) (fun _ => (![1, 0, 0] : Zd 3 3))).im : ℝ) : ℂ) /
        ((((wardII_szI.size 0 : ℕ) : ℂ)) * (etaT (0 : ℝ) (1 / 2 : ℝ) : ℂ)) :=
  stWardII_identity wardII_szI 0 (by norm_num) (by norm_num) (by norm_num) Matrix.isHermitian_one
    (by decide) _

end RBM.Gauss.Sizes

namespace RBM.Gauss.Step5Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst RBM.Path Filter

/-- `stWardII_holds 3` applied at the Step-5 instance data `(szB, zB, 15/16, 31/32)` (regime (ii): `1-t = 1/32 ≥ ilambda²/L^3 = 1/64`,
`1-s = 1/16 = ilambda²/L²`); the stochastic premises `STKbound ... STLKU` stay hypotheses (other gates' pins). -/
example (Cd : ℝ) (hCd : 0 < Cd) :
    InstIng5Concl (fun sz E s t => STWardIIConcl sz E s t) szB zB (fun _ => 15 / 16) (fun _ => 31 / 32) Cd :=
  inst_wardII (stWardII_holds 3) Cd hCd

end RBM.Gauss.Step5Inst
