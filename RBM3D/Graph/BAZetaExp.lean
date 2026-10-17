/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWXiExp
import RBM3D.Graph.BAAuxGraph2B
import RBM3D.Chain.LWGen
import RBM3D.BA.LWPinsBA
import RBM3D.BA.FlowPins
import RBM3D.BA.GreenLDE

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# BA-L L3c3b: `claim:xi` for the exp class at BA, the variables `ζ` (T2444)

Paper: arXiv:2507.20274 (`7_8:line` is `paper/tex/7_8_light_weight.tex:line`, `B:line` is `paper/tex/B_graphical_lemmas.tex:line`):
`claim:xi` (`7_8:873-890`, no proof in the paper), `(eq:xia1a2)` (`7_8:882`), the radius `(log W)^{3/2}` (`7_8:95-97`, `7_8:1653`),
`(eq:Gbyxi2_BA)` (`B:428-431`), the exp class `(LW_assm_exp)` (`3_5:406-415`).
Basis: the band file `RBM3D/Graph/LWXiExp.lean` `:1-787` (T2359), of which this file is the twin on the BA carrier `baFMz sz z`
(law `seqP (sz.withLam 0)`, `BAFlow`, horizon `BAflowT0`), with the BA edge variables `ζ = baZetaVar` of L3c3a (T2435,
`Graph/BAAuxGraph2.lean`, `BAAuxGraph2B.lean`) in place of `lwXiVar`.

* Section 1: the statements `LWXiEgL` (the carrier form of `LWXiE`), `LWXiEgL_bandFM` (`Iff.rfl`), `BAZetaExpClaim`.
* Section 2: the deterministic facts on the class `Φ_E = lwXE_phi` (copied from `LWXiExp.lean` §3 as private lemmas: the band
  file's are private; `lwXE_phi` and `lwTail32` are public there and are imported, not twinned).
* Section 3: the arithmetic and the core of conjunct 2 for `ζ` (the floor `W^{-D₁}` stays additive and is absorbed into `W^{-D}`
  of the target: the threshold on `D₁` is `max (2 D) (1/𝔠)`, not `D + d`).
* Section 4: `baZetaExpClaim_holds`.
* Section 5: compiled nonempty instances at the `d = 3` data of `BA/LWPinsBA.lean` §3.

Ports (merged files, text copied and adapted): `Graph/LWXiExp.lean:124-270, 374-401, 513-529, 535-558, 568-716` at the merged
commit `eb56169` (the last commit touching `LWXiExp.lean`).  The band file's lattice, `≺` and Ward helpers (§4) are L3c3a's public `BAAuxGraph2_*` instead.  RBM1D and
RBM2D have no light-weight graph layer.
-/

noncomputable section

namespace RBM.Graph

open MeasureTheory Filter
open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.BA
open scoped Matrix

/-! ## 1. The statements -/

/-- **`LWXiE` over a carrier `C` and a law `μ`** (`LWXiE`, `Graph/LWXiExp.lean:57`, with `sz.Prec` replaced by `PrecL sz μ` and
`etaT (E n) (t n)` by `C.eta n (t n)`; the check file's `T2444_LWXiEgL` up to the name): the exp-class edge variables
`ξ_{αβ} = ξ_{βα} ≥ 0`, `ξ_{αβ} ≺ 𝖳_t(|α-β|_∞ ∧ ℓ) + W^{-D}` on the pairs with `λ²/L² < 1 - t`, and `Σ_β ξ_{αβ}² ≺ (W^d η_t)⁻¹`.
Generic over the carrier: the BA instance is `C = baFMz sz z`, `μ = seqP (sz.withLam 0)`. -/
def LWXiEgL {d : ℕ} {sz : Sizes d} (C : FlowFM sz) (μ : Measure sz.SeqΩ) (t ℓ : ℕ → ℝ) (D : ℝ)
    (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    PrecL sz μ (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    PrecL sz μ (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * C.eta n (t n))⁻¹)

/-- **`claim:xi` for the exp class at BA** (`7_8:884-890`, `(eq:Gbyxi2_BA)` `B:428-431`; twin of `LWXiExpClaim`,
`LWXiExp.lean:68`; the check file's `T2444_BAZetaExpClaim` up to the name): at the `baPin` data (law `seqP (sz.withLam 0)`, setting
`BAFlow`, carrier `baFMz`, horizon `BAflowT0`), under `(LW_assm_exp)` (`LWAssmExpgL`) and `‖G_t - M‖_max ≺ W^{-ε₁}`, the variables
`baZetaVar` at a radius `ρ` with `√ρ ≤ τ log N` eventually for every `τ > 0` and a floor exponent `D₁ ≥ max (2 D) (1/𝔠)` satisfy
`LWXiEgL`. -/
def BAZetaExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
          ∀ ε₁ : ℝ, 0 < ε₁ →
          PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
            (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
          ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
            (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
            ∀ D₁ : ℝ, max (2 * D) (1 / 𝔠) ≤ D₁ →
              LWXiEgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ℓ D (baZetaVar sz z t ρ D₁)

/-! ## 2. Deterministic facts on the class `Φ_E` (copied from `LWXiExp.lean` §3; `lwXE_phi` is imported) -/

private theorem BAZetaExp_phi_pos {d L : ℕ} {W g t c D : ℝ} (hW : 0 < W) (r : ℝ) : 0 < lwXE_phi d L W g t c D r :=
  Real.sqrt_pos.2 (mul_pos (inv_pos.2 (pow_pos hW d)) (tailW_pos hW r))

private theorem BAZetaExp_phi_sq {d L : ℕ} {W g t c D : ℝ} (hW : 0 < W) (r : ℝ) :
    lwXE_phi d L W g t c D r ^ 2 = (W ^ d)⁻¹ * tailW d L g t c W D r :=
  Real.sq_sqrt (mul_pos (inv_pos.2 (pow_pos hW d)) (tailW_pos hW r)).le

/-- **The cost of shifting the argument of `𝒯_t`** (paper-delta candidate `T2348a`): for `0 ≤ a`, `0 ≤ b ≤ ρ + a`,
`𝒯_t(a) ≤ (ρ+1)^{d-2} e^{√(ρ/ℓ_t)} 𝒯_t(b)` (`B_{t,a} ≤ (ρ+1)^{d-2} B_{t,b}`: the zero mode is common, `a + 1 ≥ (b+1)/(ρ+1)`;
`√b ≤ √ρ + √a`). -/
private theorem BAZetaExp_tailT_shift {d L : ℕ} {g t a b ρ : ℝ} (hL : 1 ≤ (L : ℝ)) (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
    (hab : b ≤ ρ + a) (hb : 0 ≤ b) :
    tailT d L g t a ≤ (ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t)) * tailT d L g t b := by
  have hℓ : 0 < ellT L g t := ellT_pos hL
  unfold tailT BparamR
  set A : ℝ := (g ^ 2 + |1 - t|)⁻¹ with hA
  set Z : ℝ := ((L : ℝ) ^ d * |1 - t|)⁻¹ with hZ
  have hA0 : 0 ≤ A := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have hP1 : 1 ≤ (ρ + 1) ^ (d - 2) := one_le_pow₀ (by linarith)
  have hpoly : ((a + 1) ^ (d - 2))⁻¹ ≤ (ρ + 1) ^ (d - 2) * ((b + 1) ^ (d - 2))⁻¹ := by
    have h1 : b + 1 ≤ (ρ + 1) * (a + 1) := by nlinarith
    have h2 : (b + 1) ^ (d - 2) ≤ (ρ + 1) ^ (d - 2) * (a + 1) ^ (d - 2) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) h1 _
    have hb1 : 0 < (b + 1) ^ (d - 2) := by positivity
    have ha1 : 0 < (a + 1) ^ (d - 2) := by positivity
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ ha1 hb1]
    linarith
  have hB : A * ((a + 1) ^ (d - 2))⁻¹ + Z ≤ (ρ + 1) ^ (d - 2) * (A * ((b + 1) ^ (d - 2))⁻¹ + Z) := by
    nlinarith [mul_le_mul_of_nonneg_left hpoly hA0, mul_le_mul_of_nonneg_right hP1 hZ0]
  have hexp : Real.exp (-Real.sqrt (a / ellT L g t)) ≤
      Real.exp (Real.sqrt (ρ / ellT L g t)) * Real.exp (-Real.sqrt (b / ellT L g t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : b / ellT L g t ≤ ρ / ellT L g t + a / ellT L g t := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hℓ.le
    have h2 := Real.sqrt_le_sqrt h1
    have h3 := sqrt_add_le_add_sqrt (div_nonneg hρ hℓ.le) (div_nonneg ha hℓ.le)
    linarith
  calc (A * ((a + 1) ^ (d - 2))⁻¹ + Z) * Real.exp (-Real.sqrt (a / ellT L g t))
      ≤ ((ρ + 1) ^ (d - 2) * (A * ((b + 1) ^ (d - 2))⁻¹ + Z)) *
        (Real.exp (Real.sqrt (ρ / ellT L g t)) * Real.exp (-Real.sqrt (b / ellT L g t))) :=
        mul_le_mul hB hexp (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The shift for the truncated tail `wT^c_{t,D}`: `r₂ ≤ ρ + r₁` gives `wT(r₁) ≤ (ρ+1)^{d-2} e^{√(ρ/ℓ_t)} wT(r₂)` (the floor
`W^{-D}` is absorbed since the factor is `≥ 1`). -/
private theorem BAZetaExp_tailW_shift {d L : ℕ} {W g t c D ρ r₁ r₂ : ℝ} (hW : 0 < W) (hL : 1 ≤ (L : ℝ)) (hc : 0 ≤ c)
    (hρ : 0 ≤ ρ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (h : r₂ ≤ ρ + r₁) :
    tailW d L g t c W D r₁ ≤ (ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t)) * tailW d L g t c W D r₂ := by
  have hK1 : 1 ≤ (ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t)) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (Real.one_le_exp (Real.sqrt_nonneg _))
  have hmin : min r₂ c ≤ ρ + min r₁ c := by
    rcases le_total r₁ c with h1 | h1
    · rw [min_eq_left h1]; exact (min_le_left _ _).trans h
    · rw [min_eq_right h1]; linarith [min_le_right r₂ c]
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW.le _
  unfold tailW
  refine max_le ?_ ?_
  · calc tailT d L g t (min r₁ c)
        ≤ (ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t)) * tailT d L g t (min r₂ c) :=
          BAZetaExp_tailT_shift hL (le_min hr₁ hc) hρ hmin (le_min hr₂ hc)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  · calc W ^ (-D) ≤ ((ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t))) * W ^ (-D) :=
          le_mul_of_one_le_left hWD hK1
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

/-- **`Φ_E(m) ≤ K_n Φ_E(ℓ')` for `ℓ' ≤ 2ρ + m`** (the comparability that replaces `(eq:Psi)` in `auxGraph2_phi_cmp`,
`Graph/AuxGraph2.lean:723`): `K_n = ((2ρ+1)^{d-2} e^{√(2ρ/ℓ_t)})^{1/2}`. -/
private theorem BAZetaExp_phi_cmp {d L : ℕ} {W g t c D ρ ℓ' m : ℝ} (hW : 0 < W) (hL : 1 ≤ (L : ℝ)) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hℓ' : 0 ≤ ℓ') (hm : 0 ≤ m) (h : ℓ' ≤ 2 * ρ + m) :
    lwXE_phi d L W g t c D m ≤
      Real.sqrt ((2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t))) * lwXE_phi d L W g t c D ℓ' := by
  unfold lwXE_phi
  have hK : 0 ≤ (2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t)) := by positivity
  rw [← Real.sqrt_mul hK]
  refine Real.sqrt_le_sqrt ?_
  have hs := BAZetaExp_tailW_shift (d := d) (L := L) (W := W) (g := g) (t := t) (c := c) (D := D) hW hL hc
    (by linarith : 0 ≤ 2 * ρ) hm hℓ' h
  calc (W ^ d)⁻¹ * tailW d L g t c W D m
      ≤ (W ^ d)⁻¹ * ((2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t)) * tailW d L g t c W D ℓ') :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- **The comparison with the target** (regime `λ²/L² ≤ 1 - t`, `0 ≤ r ≤ L`): `Φ_E(r) ≤ (1 + 2^{d-1}) (𝖳_t(r ∧ c) + W^{-D})`
for the class at `2D` (`tailW_regime1_bounds`: the zero mode of `B_{t,r}` is dominated by `zeroMode_le_of_ge`; `W^{-d-2D} ≤ (W^{-D})²`). -/
private theorem BAZetaExp_phi_le {d L : ℕ} {W g t c D r : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) (hW : 1 ≤ W)
    (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hrL : r ≤ L) :
    lwXE_phi d L W g t c (2 * D) r ≤ (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r c) + W ^ (-D)) := by
  have hW0 : 0 < W := by linarith
  have hmin : min r (min c L) = min r c := by
    rw [← min_assoc, min_eq_left ((min_le_left r c).trans hrL)]
  have hrw : tailW d L g t (min c L) W (2 * D) r = tailW d L g t c W (2 * D) r := by
    unfold tailW; rw [hmin]
  obtain ⟨-, h2⟩ := tailW_regime1_bounds (d := d) (L := L) (W := W) (g := g) (t := t) (ℓ := min c L) (D := 2 * D) hd hL ht hW0
    hgt (le_min hc (by linarith)) (min_le_right _ _) hr0
  rw [hrw, hmin] at h2
  have he : W ^ (-(2 * D)) = (W ^ (-D)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have hWd : (W ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  have hs0 : 0 ≤ sfT d L W g t (min r c) := sfT_nonneg _
  have hK1 : (1 : ℝ) ≤ 1 + 2 ^ (d - 1) := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (d - 1)]
  have hK0 : (0 : ℝ) ≤ 1 + 2 ^ (d - 1) := by linarith
  unfold lwXE_phi
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc (W ^ d)⁻¹ * tailW d L g t c W (2 * D) r
      ≤ (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r c) ^ 2 + (W ^ d)⁻¹ * W ^ (-(2 * D))) := h2
    _ ≤ (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r c) ^ 2 + (W ^ (-D)) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) hK0
        rw [he]; exact mul_le_of_le_one_left (sq_nonneg _) hWd
    _ ≤ (1 + 2 ^ (d - 1)) * (sfT d L W g t (min r c) + W ^ (-D)) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        nlinarith [mul_nonneg hs0 hWD]
    _ ≤ ((1 + 2 ^ (d - 1)) * (sfT d L W g t (min r c) + W ^ (-D))) ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)

/-- **The window `W^{-d} ≤ C₃ Φ_E(0)²`** with `C₃ = 1 + 𝔡⁻²` (`0 ≤ t < 1`, `0 ≤ g ≤ 𝔡⁻¹`; no regime):
`wT(0) ≥ 𝒯_t(0) = B_{t,0} ≥ (g² + |1-t|)⁻¹ ≥ (1 + 𝔡⁻²)⁻¹`. -/
private theorem BAZetaExp_window {d L : ℕ} {W g t c D 𝔡 : ℝ} (hW : 0 < W) (ht0 : 0 ≤ t) (ht : t < 1) (hg : 0 ≤ g)
    (hg' : g ≤ 𝔡⁻¹) (hc : 0 ≤ c) :
    (W ^ d)⁻¹ ≤ (1 + (𝔡⁻¹) ^ 2) * lwXE_phi d L W g t c D 0 ^ 2 := by
  rw [BAZetaExp_phi_sq hW]
  have hy : 0 < g ^ 2 + |1 - t| := by
    have : 0 < |1 - t| := abs_pos.2 (by linarith)
    positivity
  have hy' : g ^ 2 + |1 - t| ≤ 1 + (𝔡⁻¹) ^ 2 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < 1 - t)]
    nlinarith [pow_le_pow_left₀ hg hg' 2]
  have hT : (g ^ 2 + |1 - t|)⁻¹ ≤ tailW d L g t c W D 0 := by
    refine le_trans ?_ (le_max_left _ _)
    rw [min_eq_left hc]
    have h0 : tailT d L g t 0 = Bparam d L g t 0 := tailT_zero
    rw [h0]
    have : Bparam d L g t 0 = (g ^ 2 + |1 - t|)⁻¹ + ((L : ℝ) ^ d * |1 - t|)⁻¹ := by simp [Bparam]
    rw [this]
    have : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
    linarith
  have h1 : 1 ≤ (1 + (𝔡⁻¹) ^ 2) * tailW d L g t c W D 0 := by
    calc (1 : ℝ) = (g ^ 2 + |1 - t|) * (g ^ 2 + |1 - t|)⁻¹ := (mul_inv_cancel₀ hy.ne').symm
      _ ≤ (1 + (𝔡⁻¹) ^ 2) * (g ^ 2 + |1 - t|)⁻¹ := mul_le_mul_of_nonneg_right hy' (inv_nonneg.2 hy.le)
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  have hWd : 0 < (W ^ d)⁻¹ := inv_pos.2 (pow_pos hW d)
  calc (W ^ d)⁻¹ = (W ^ d)⁻¹ * 1 := (mul_one _).symm
    _ ≤ (W ^ d)⁻¹ * ((1 + (𝔡⁻¹) ^ 2) * tailW d L g t c W D 0) := mul_le_mul_of_nonneg_left h1 hWd.le
    _ = _ := by ring

/-- **A radius with `√ρ ≤ τ log N` eventually for every `τ > 0` is `N^{o(1)}`** (copy of `lwXE_rho_poly`, `LWXiExp.lean:374`): `ρ + 1 ≤ N^τ` eventually for every `τ > 0`
(`ρ ≤ (log N)²` and `log N ≤ N^{τ/4}/(τ/4)`). -/
private theorem BAZetaExp_rho_poly {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {ρ : ℕ → ℝ} (hρ0 : ∀ n, 0 ≤ ρ n)
    (hρ : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  intro τ hτ
  have hε0 : 0 < τ / 4 := by positivity
  have hbig : ∀ᶠ n in atTop, 16 / τ ^ 2 + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop _
  filter_upwards [hρ 1 one_pos, hbig, hsize.eventually_ge_atTop 1] with n h1 hb hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have h2 : ρ n ≤ Real.log N ^ 2 := by
    have : Real.sqrt (ρ n) ≤ Real.log N := by simpa using h1
    calc ρ n = Real.sqrt (ρ n) ^ 2 := (Real.sq_sqrt (hρ0 n)).symm
      _ ≤ Real.log N ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
  have h4 : Real.log N ^ 2 ≤ (N ^ (τ / 4) / (τ / 4)) ^ 2 :=
    pow_le_pow_left₀ hlog0 (Real.log_le_rpow_div hN0.le hε0) 2
  have e1 : (N ^ (τ / 4)) ^ 2 = N ^ (τ / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have h5 : (N ^ (τ / 4) / (τ / 4)) ^ 2 = 16 / τ ^ 2 * N ^ (τ / 2) := by
    rw [div_pow, e1]; field_simp; ring
  have hY : 1 ≤ N ^ (τ / 2) := Real.one_le_rpow hN1 (by positivity)
  have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  calc ρ n + 1 ≤ 16 / τ ^ 2 * N ^ (τ / 2) + 1 := by linarith [h2, h4, h5.le]
    _ ≤ (16 / τ ^ 2 + 1) * N ^ (τ / 2) := by nlinarith
    _ ≤ N ^ (τ / 2) * N ^ (τ / 2) := mul_le_mul_of_nonneg_right hb (by linarith)
    _ = N ^ τ := hNτ.symm

/-! ## 3. The arithmetic and the core of conjunct 2 for `ζ` -/

/-- The arithmetic of conjunct 2, in powers of `u` (twin of `lwXE_num`, `LWXiExp.lean:513`, without the window lower bound `2 ≤ u^8`:
the floor is kept additive, so the bound is `(2 A u⁴ + S) K² ≤ 2 u⁸`). -/
private theorem BAZetaExp_num {u A₁ K2 S : ℝ} (hu : 1 ≤ u) (hA : 2 * A₁ ≤ u ^ 2) (hC : S ≤ u ^ 4)
    (hK : K2 ≤ u ^ 2) (hA0 : 0 ≤ A₁) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K2) :
    (2 * A₁ * u ^ 4 + S) * K2 ≤ 2 * u ^ 8 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 2 * A₁ * u ^ 4 ≤ u ^ 6 := by
    calc _ ≤ u ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = u ^ 6 := by ring
  have h2' : u ^ 4 ≤ u ^ 6 := pow_le_pow_right₀ hu (by norm_num)
  have h3 : 2 * A₁ * u ^ 4 + S ≤ 2 * u ^ 6 := by linarith
  have h4 : (2 * A₁ * u ^ 4 + S) * K2 ≤ 2 * u ^ 6 * u ^ 2 :=
    mul_le_mul h3 hK hK0 (by positivity)
  have h5 : 2 * u ^ 6 * u ^ 2 = 2 * u ^ 8 := by ring
  linarith

/-- **The core of conjunct 2** (twin of `lwXE_core`, `LWXiExp.lean:535`, for `ζ` with the floor `W^{-D₁}`): with `u ≥ 1`, the loop bound
`‖𝓛^{(2)}‖ ≤ u⁴ Φ²`, the comparability `Φ(m) ≤ K_n Φ(ℓ)` for `ℓ ≤ 2ρ + m`, the window `W^{-d} ≤ C₃² Φ(0)²` and the size conditions
`2 (2ρ+1)^{2d} ≤ u²`, `K_n ≤ u`, `C₃² ≤ u⁴`: `ζ([a₁],[a₂])² ≤ 2 u⁸ Φ(|a₁ - a₂|)² + W^{-D₁}`. -/
private theorem BAZetaExp_core {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t ρ : ℕ → ℝ) (D₁ : ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n) {u Kn C₃ : ℝ} (hu : 1 ≤ u) (hKn0 : 0 ≤ Kn)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖(baFMz sz z).L n (t n) ![s, !s] ![b₁, b₂] ω‖ ≤ u ^ 4 * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ Kn * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ ^ 2 * Φn 0 ^ 2)
    (q1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2) (q2 : Kn ≤ u) (q3 : C₃ ^ 2 ≤ u ^ 4)
    (a₁ a₂ : Zd d (sz.L n)) :
    baZetaSq sz z t ρ D₁ n a₁ a₂ ω ≤
      2 * u ^ 8 * Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 + ((sz.W n : ℕ) : ℝ) ^ (-D₁) := by
  have hu0 : 0 ≤ u := by linarith
  have hbound := BAAuxGraph2_zetaSq_le sz z t ρ D₁ n ω Φn hρ (B := u ^ 4) (K := Kn) (C₃ := C₃) (by positivity)
    hloop hΦnn hcmp hW a₁ a₂
  have hnum := BAZetaExp_num hu q1 q3 (pow_le_pow_left₀ hKn0 q2 2) (pow_nonneg (by linarith) _) (sq_nonneg _) (sq_nonneg _)
  refine hbound.trans (add_le_add_left ?_ _)
  exact mul_le_mul_of_nonneg_right hnum (sq_nonneg _)

/-! ## 4. `claim:xi` for the exp class at BA -/

/-- **`claim:xi` for the exp class at BA** (`7_8:884-890`, `(eq:Gbyxi2_BA)` `B:428-431`; twin of `lwXiExpClaim_holds`, `LWXiExp.lean:568`):
under `(LW_assm_exp)` (`LWAssmExpgL`) and `‖G_t - M‖_max ≺ W^{-ε₁}`, the variables `baZetaVar` at a radius `ρ` with `√ρ ≤ τ log N`
eventually for every `τ > 0` and a floor exponent `D₁ ≥ max (2 D) (1/𝔠)` satisfy `LWXiEgL`: symmetric, non-negative,
`ζ([a₁],[a₂]) ≺ 𝖳_t(|a₁ - a₂|_∞ ∧ ℓ) + W^{-D}` on the pairs with `λ²/L² < 1 - t`, and `Σ_{a₂} ζ([a₁],[a₂])² ≺ (W^d η_t)⁻¹`
(Ward's identity, block form).  Conjunct 2: the class `Φ_E = (W^{-d} wT^ℓ_{t,2D})^{1/2}` is the class of `LWLoopExpgL` at `2D`; the floor
`W^{-D₁} ≤ W^{-2D} ≤ (W^{-D})²` is absorbed into the target for `D₁ ≥ 2D`; conjunct 3: the Ward sum, whose floor is `L^d W^{-D₁} ≤ W^{-d}`
for `D₁ ≥ 1/𝔠`. -/
theorem baZetaExpClaim_holds (d : ℕ) : BAZetaExpClaim d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hAssm ε₁ hε₁ hent D hD ρ hρ0 hρ D₁ hD₁
  have hadm := hflow.1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hd0 : 0 < d := by omega
  have hD₁a : 2 * D ≤ D₁ := (le_max_left _ _).trans hD₁
  have hD₁b : 1 / 𝔠 ≤ D₁ := (le_max_right _ _).trans hD₁
  have hρ' := BAZetaExp_rho_poly sz hsize hρ0 hρ
  obtain ⟨-, -, -, hℓ0, -, hloopE⟩ := hAssm
  refine ⟨fun n α β ω => ⟨baZetaVar_nonneg sz z t ρ D₁ n α β ω, baZetaVar_symm sz z t ρ D₁ n α β ω⟩, ?_, ?_⟩
  · -- conjunct 2: `ζ ≺ 𝖳_t(|a₁ - a₂|_∞ ∧ ℓ) + W^{-D}` on `λ²/L² < 1 - t`
    have hD2 : 0 < 2 * D := by positivity
    refine BAAuxGraph2_prec_of_imp (hloopE (2 * D) hD2) ?_
    intro τ hτ
    refine ⟨τ / 4, by positivity, ?_⟩
    have p1 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 2) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 8) (by positivity)
    have p2 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 1) (e := ((d - 2 : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 16) (by positivity)
    have p4 : ∀ᶠ n in atTop, 1 + (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
      ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
    have p6 : ∀ᶠ n in atTop, 1 + (2 : ℝ) ^ (d - 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
    filter_upwards [p1, p2, hρ (τ / 32) (by positivity), p4, p6, hadm.2.2.2.2,
      hsize.eventually_ge_atTop 1] with n q1 q2 q3 q4 q6 hWO hX1
    intro ω p hp
    by_contra hno
    push Not at hno
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    have hX0 : 0 < X := by linarith
    set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
    have hW1 : 1 ≤ W := Nat.one_le_cast.2 (sz.W_pos n)
    have hW0 : 0 < W := by linarith
    have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
    have hlam0 : 0 ≤ sz.lam n := (lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hWO.1).le
    have htlt : t n < 1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
    set u : ℝ := X ^ (τ / 16) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow hX1 (by positivity)
    have hpow : ∀ k : ℕ, X ^ (τ / 16 * (k : ℝ)) = u ^ k := fun k => (BAAuxGraph2_rpow_nat X hX0.le _ k).symm
    have e2 : X ^ (τ / 8) = u ^ 2 := by rw [← hpow 2]; congr 1; push_cast; ring
    have e4 : X ^ (τ / 4) = u ^ 4 := by rw [← hpow 4]; congr 1; push_cast; ring
    have e8 : X ^ (τ / 2) = u ^ 8 := by rw [← hpow 8]; congr 1; push_cast; ring
    have e16 : X ^ τ = u ^ 16 := by rw [← hpow 16]; congr 1; push_cast; ring
    -- the class `Φ_E` and the loop bound on the complement of the bad event
    set Φn : ℝ → ℝ := lwXE_phi d (sz.L n) W (sz.lam n) (t n) (ℓ n) (2 * D) with hΦn
    have hΦpos : ∀ r : ℝ, 0 < Φn r := fun r => BAZetaExp_phi_pos hW0 r
    have hloop' : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
        ‖(baFMz sz z).L n (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
          u ^ 4 * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := by
      intro s b₁ b₂
      have := hno (s, b₁, b₂)
      rw [hΦn, BAZetaExp_phi_sq hW0, ← e4]
      exact this
    set Kn : ℝ := Real.sqrt ((2 * ρ n + 1) ^ (d - 2) *
      Real.exp (Real.sqrt (2 * ρ n / ellT (sz.L n) (sz.lam n) (t n)))) with hKn
    have hKn0 : 0 ≤ Kn := Real.sqrt_nonneg _
    have hcmp : ∀ ℓ' m : ℝ, 0 ≤ ℓ' → 0 ≤ m → ℓ' ≤ 2 * ρ n + m → Φn m ≤ Kn * Φn ℓ' :=
      fun ℓ' m hℓ' hm h => BAZetaExp_phi_cmp hW0 hL1 (hℓ0 n) (hρ0 n) hℓ' hm h
    have hKnu : Kn ≤ u := by
      have hP : (2 * ρ n + 1) ^ (d - 2) ≤ u := by
        have := q2
        rw [Real.rpow_natCast, one_mul] at this
        exact this
      have hEx : Real.exp (Real.sqrt (2 * ρ n / ellT (sz.L n) (sz.lam n) (t n))) ≤ u := by
        have h1 : Real.sqrt (2 * ρ n / ellT (sz.L n) (sz.lam n) (t n)) ≤ Real.sqrt (2 * ρ n) :=
          Real.sqrt_le_sqrt (div_le_self (by have := hρ0 n; positivity) (one_le_ellT hL1))
        have h2 : Real.sqrt (2 * ρ n) ≤ 2 * Real.sqrt (ρ n) :=
          Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [Real.sq_sqrt (hρ0 n)]⟩
        calc _ ≤ Real.exp (Real.sqrt (2 * ρ n)) := Real.exp_le_exp.2 h1
          _ ≤ u := by
            rw [hu, Real.rpow_def_of_pos hX0]
            exact Real.exp_le_exp.2 (by linarith)
      refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
      calc _ ≤ u * u := mul_le_mul hP hEx (Real.exp_pos _).le (by linarith)
        _ = u ^ 2 := by ring
    -- the window with `C₃ = √(1 + 𝔡⁻²)`, `C₃² = 1 + 𝔡⁻²`
    have hC₃ : Real.sqrt (1 + (𝔡⁻¹) ^ 2) ^ 2 = 1 + (𝔡⁻¹) ^ 2 := Real.sq_sqrt (by positivity)
    have hwin : (W ^ d)⁻¹ ≤ Real.sqrt (1 + (𝔡⁻¹) ^ 2) ^ 2 * Φn 0 ^ 2 := by
      rw [hC₃]; exact BAZetaExp_window hW0 (ht0 n) htlt hlam0 hWO.2 (hℓ0 n)
    have hq1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2 := by
      have := q1
      rw [Real.rpow_natCast, e2] at this
      exact this
    have hq3 : Real.sqrt (1 + (𝔡⁻¹) ^ 2) ^ 2 ≤ u ^ 4 := by rw [hC₃, ← e4]; exact q4
    have hCE : 1 + (2 : ℝ) ^ (d - 1) ≤ u ^ 8 := by rw [← e8]; exact q6
    have h8 : (3 : ℝ) ≤ u ^ 8 := by
      have h4 : (2 : ℝ) ^ 2 ≤ 2 ^ (d - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hcore := BAZetaExp_core sz z t ρ D₁ n ω Φn (hρ0 n) hu1 hKn0 hloop' (fun r _ => (hΦpos r).le) hcmp hwin hq1 hKnu hq3
      p.1.1 p.1.2
    -- the comparison with the target on `λ²/L² < 1 - t`
    have hrL : ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast BAAuxGraph2_zdistInf_le_L d (sz.L n) _
    have hcomp := BAZetaExp_phi_le (d := d) (L := sz.L n) (W := W) (g := sz.lam n) (t := t n) (c := ℓ n) (D := D)
      (r := ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ)) (by omega) hL1 htlt hW1 p.2.le (hℓ0 n)
      (Nat.cast_nonneg _) hrL
    set Θ : ℝ := sfT d (sz.L n) W (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D) with hΘ
    have hp' : X ^ τ * Θ < baZetaVar sz z t ρ D₁ n p.1.1 p.1.2 ω := hp
    have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
    have hΘ0 : 0 ≤ Θ := add_nonneg (sfT_nonneg _) hWD
    have hWΘ : W ^ (-D) ≤ Θ := le_add_of_nonneg_left (sfT_nonneg _)
    -- the floor is absorbed: `W^{-D₁} ≤ W^{-2D} = (W^{-D})² ≤ Θ²`
    have hfl : W ^ (-D₁) ≤ Θ ^ 2 := by
      have he : W ^ (-(2 * D)) = (W ^ (-D)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
      calc W ^ (-D₁) ≤ W ^ (-(2 * D)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
        _ = (W ^ (-D)) ^ 2 := he
        _ ≤ Θ ^ 2 := pow_le_pow_left₀ hWD hWΘ 2
    have hΦΘ : Φn ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) ≤ u ^ 8 * Θ :=
      hcomp.trans (mul_le_mul_of_nonneg_right hCE hΘ0)
    have h32 : 2 * u ^ 24 + 1 ≤ (u ^ 16) ^ 2 := by
      have h24 : 1 ≤ u ^ 24 := one_le_pow₀ hu1
      have h3 : u ^ 24 * 3 ≤ u ^ 24 * u ^ 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
      calc 2 * u ^ 24 + 1 ≤ u ^ 24 * 3 := by linarith
        _ ≤ u ^ 24 * u ^ 8 := h3
        _ = (u ^ 16) ^ 2 := by ring
    have hsq : baZetaSq sz z t ρ D₁ n p.1.1 p.1.2 ω ≤ (X ^ τ * Θ) ^ 2 := by
      calc _ ≤ 2 * u ^ 8 * Φn ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) ^ 2 + W ^ (-D₁) := hcore
        _ ≤ 2 * u ^ 8 * (u ^ 8 * Θ) ^ 2 + Θ ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΦpos _).le hΦΘ 2) (by positivity)) hfl
        _ = (2 * u ^ 24 + 1) * Θ ^ 2 := by ring
        _ ≤ (u ^ 16) ^ 2 * Θ ^ 2 := mul_le_mul_of_nonneg_right h32 (sq_nonneg _)
        _ = (X ^ τ * Θ) ^ 2 := by rw [e16]; ring
    have hle : baZetaVar sz z t ρ D₁ n p.1.1 p.1.2 ω ≤ X ^ τ * Θ :=
      Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩
    linarith
  · -- conjunct 3: `Σ_β ζ² ≺ (W^d η)⁻¹` (Ward's identity on `‖G - M‖_max ≤ 1`)
    refine BAAuxGraph2_prec_of_imp hent ?_
    intro τ hτ
    refine ⟨𝔠 * ε₁ / 2, by positivity, ?_⟩
    have p1 := BAAuxGraph2_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 6) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) hτ
    filter_upwards [hadm.2.2.2.1, p1] with n hb q1
    intro ω α hα
    by_contra hno
    push Not at hno
    have hsm := BAAuxGraph2_pow_small sz n h𝔠 hε₁ hb
    have hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ 1 := fun x y =>
      ((hno (x, y)).trans hsm.1).trans hsm.2
    have hw := baZeta_ward_sum sz z t ρ D₁ n hκ hflow (ht0 n) (htT n) (hρ0 n) ω hA α
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    set Q : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * (baFMz sz z).eta n (t n))⁻¹ with hQ
    have hα' : X ^ τ * Q < ∑ β, baZetaVar sz z t ρ D₁ n α β ω ^ 2 := hα
    simp_rw [BAAuxGraph2_zetaVar_sq] at hα'
    obtain ⟨ht1, -, hmi, hzi, -, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (htT n)
    have hη0 : 0 < (baFMz sz z).eta n (t n) := by
      have := hzi
      rw [ztOf_im] at this
      exact this
    have hη1 : (baFMz sz z).eta n (t n) ≤ 1 := BAAuxGraph2_eta_le_one sz z hκ hflow n (ht0 n) (htT n)
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      positivity
    have hQ0 : 0 < Q := inv_pos.2 (mul_pos hWd hη0)
    have hWQ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Q :=
      inv_anti₀ (mul_pos hWd hη0) (by nlinarith)
    have hρ1 : (1 : ℝ) ≤ 2 * ρ n + 1 := by have := hρ0 n; linarith
    have hA01 : (2 * ρ n + 1) ^ d ≤ (2 * ρ n + 1) ^ (2 * d) :=
      pow_le_pow_right₀ hρ1 (by omega)
    have hA1pos : 1 ≤ (2 * ρ n + 1) ^ (2 * d) := one_le_pow₀ hρ1
    have hq : 6 * (2 * ρ n + 1) ^ (2 * d) ≤ X ^ τ := by
      have := q1
      rwa [Real.rpow_natCast] at this
    have hfl := BAAuxGraph2_floorL_le sz h𝔠 n hb hD₁b
    have hsum : ∑ β, baZetaSq sz z t ρ D₁ n α β ω ≤ 6 * (2 * ρ n + 1) ^ (2 * d) * Q := by
      refine hw.trans ?_
      have h1 : (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        mul_le_mul hA01 hWQ (by positivity) (by linarith)
      have h2 : ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        hfl.trans (hWQ.trans (le_mul_of_one_le_left hQ0.le hA1pos))
      nlinarith
    have := mul_le_mul_of_nonneg_right hq hQ0.le
    linarith

/-! ## 5. Compiled nonempty instances at `d = 3`

The data of `BA/LWPinsBA.lean` §3: `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `λ_n = (2(n+1))^{-6}`; `n = 0` is `L = 4`, `W = 32`), the flow
`flow_sz0` (`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}`, `ℓ ≡ 0`,
`ε₁ = 1/20`, the radius `ρ_n = log N_n` (`√ρ ≤ τ log N` eventually for every `τ > 0`: `log N ≥ τ^{-2}`), every `D > 0`, `D₁ = max (2 D) 6`
(`1/𝔠 = 6`).  The subtype of conjunct 2 (`λ²/L² < 1/2`) is all of `n` and nonempty at every `n`.  What stays a hypothesis is another
gate's stochastic input: `STInitialGT2gL` and `LWLoopExpgL` (`(initialGT2)`, `(LW_assm_exp)`) and the entry law `‖G_t - M‖_max ≺ W^{-ε₁}`. -/

end RBM.Graph

end
