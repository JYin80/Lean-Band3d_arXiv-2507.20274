/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.AuxGraph2
import RBM3D.Graph.AnpKey
import RBM3D.Graph.LWTermExpN
import RBM3D.Graph.LWPsi
import RBM3D.Kernel.PropT

/-!
# LW-13b R2 (X): `claim:xi` for the exp class and the `(log W)^{3/2}` tail (T2359)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `claim:xi` (`7_8:873-890`, no proof in the paper),
`(eq:xia1a2)` (`7_8:882`), the exp class `(LW_assm_exp)` (`3_5:411`, `3_5:406-415`), the radius `(log W)^{3/2}` (`7_8:95-97`,
`7_8:1653`).  This is the twin of `lwXiClaim_holds` (`Graph/AuxGraph2.lean:965`) for the class
`Φ_E := (W^{-d} wT^ℓ_{t,2D})^{1/2}` (`tailW`, `Defs/Tail.lean:52`), which does not satisfy `(eq:Psi)`: the comparison
`Φ(m) ≤ K Φ(ℓ')` for `ℓ' ≤ 2ρ + m` is proved directly (`lwXE_phi_cmp`, shift of `tailW`, factor
`(ρ'+1)^{(d-2)/2} e^{½√(ρ'/ℓ_t)}`, paper-delta candidate `T2348a`).  The radius hypothesis is `√ρ ≤ τ log N` eventually
for every `τ > 0` (`ρ = N^{o(1)}` in the sense `ρ ≤ (log N)^{2-}`).

Amend 1 (DECISIONS §163 (1)): conjunct 2 of `LWXiE` is stated on the subtype `λ²/L² < 1 - t` (the domain of the target
`LWMomentExp`, `Graph/LWPins.lean:346`); there the zero mode of `B_{t,r}` is dominated (`tailW_regime1_bounds`,
`Graph/LWPsi.lean:476`, `zeroMode_le_of_ge`, `Defs/Tail.lean:119`).

* Section 1: the statements `LWXiE`, `LWXiExpClaim`.
* Section 2: `lwTail32`, the copy of `lwMoment_tail` (`Graph/LWMoment.lean:473`) with `(log W)^{3/2}`.
* Section 3: deterministic facts on the class `Φ_E`: positivity, window, shift comparability, comparison with the target.
* Section 4: the private helpers of `Graph/AuxGraph2.lean` reached from `lwXiClaim_holds` (copied: `AuxGraph2.lean` is not
  writable) and the core of conjunct 2.
* Section 5: `lwXiExpClaim_holds`.
* Section 6: a compiled nonempty instance.

Ports (merged files, text copied and adapted): `Graph/AuxGraph2.lean:126-159, 617-629, 703-722, 784-950, 965-1100` and
`Graph/LWMoment.lean:473-505` at the merged commit `1fcb883`; `Probe/T2348Pins.lean:467-500` (`t/T2348`, `9f3bd75`).
RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss RBM.Gauss.Sizes Filter

/-! ## 1. The statements -/

/-- the exp-class edge variables (`7_8:1653`): `ξ ≺ 𝖳_t(|·|_∞ ∧ ℓ) + W^{-D}` on the pairs with `λ²/L² < 1 - t` (Amend 1) and
the Ward bound -/
def LWXiE {d : ℕ} (sz : Sizes d) (E t ℓ : ℕ → ℝ) (D : ℝ) (ξ : ∀ n, Zd d (sz.L n) → Zd d (sz.L n) → sz.SeqΩ → ℝ) : Prop :=
  (∀ n α β ω, 0 ≤ ξ n α β ω ∧ ξ n α β ω = ξ n β α ω) ∧
    sz.Prec (U := fun n => {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ξ n p.1.1 p.1.2 ω)
      (fun n p _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-D)) ∧
    sz.Prec (U := fun n => Zd d (sz.L n)) (fun n α ω => ∑ β, ξ n α β ω ^ 2)
      (fun n _ _ => ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (E n) (t n))⁻¹)

/-- **G2**: the twin of `lwXiClaim_holds` (`AuxGraph2.lean:965`) for the exp class, without `LWPsiAll`.  The radius is `o((log N)²)`
in the sense `√ρ ≤ τ log N` eventually, e.g. `ρ = 2K(log W)^{3/2}+1`; `K(log W)²` (`LWMoment.lean:1048`) is excluded. -/
def LWXiExpClaim (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) → ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ →
      ∀ ε₁ : ℝ, 0 < ε₁ → sz.Prec (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖STGM sz n (STflowE z n) (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) →
        ∀ D : ℝ, 0 < D → ∀ ρ : ℕ → ℝ, (∀ n, 0 ≤ ρ n) →
          (∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (ρ n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ)) →
          LWXiE sz (STflowE z) t ℓ D (lwXiVar sz (STflowE z) t ρ)

/-! ## 2. The `(log W)^{3/2}` tail -/

/-- the `(log W)^{3/2}` copy of `lwMoment_tail` (`LWMoment.lean:473`, there `(log W)²`): `W ≥ N^𝔠`, `N → ∞` give
`e^{-c (log W)^{3/2}/2} N^a ≤ N^{-b}` eventually; the threshold is `log W ≥ (2A/(𝔠c))²` instead of `≥ 2A/(𝔠c)`. -/
theorem lwTail32 {d : ℕ} (sz : Sizes d) {𝔠 c : ℝ} (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) (a b : ℝ) :
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) * ((sz.size n : ℕ) : ℝ) ^ a ≤
      ((sz.size n : ℕ) : ℝ) ^ (-b) := by
  set A : ℝ := |a| + |b| with hA
  set M : ℝ := 2 * A / (𝔠 * c) with hM
  have hA0 : 0 ≤ A := by positivity
  have hM0 : 0 ≤ M := by positivity
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp (M ^ 2)),
    hsz.eventually_ge_atTop 1] with n hb hbig hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hLg : M ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) := (Real.le_log_iff_exp_le hW0).2 (le_trans hbig hb)
  set Lg : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hLgdef
  have hL0 : 0 ≤ Lg := le_trans (sq_nonneg M) hLg
  have h1 : N ^ (a + b) ≤ N ^ A := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [le_abs_self a, le_abs_self b])
  have h2 : N ^ A ≤ Real.exp (Lg * (A / 𝔠)) :=
    (Sizes.size_rpow_le_W_rpow sz h𝔠 n hb hA0).trans_eq (Real.rpow_def_of_pos hW0 _)
  have hsq : M ≤ Real.sqrt Lg := (Real.le_sqrt hM0 hL0).2 hLg
  have h32 : Lg ^ (3 / 2 : ℝ) = Lg * Real.sqrt Lg := by
    rcases hL0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one, Real.sqrt_eq_rpow]
  have h4 : Lg * (A / 𝔠) ≤ c * Lg ^ (3 / 2 : ℝ) / 2 := by
    have : A / 𝔠 = c * M / 2 := by rw [hM]; field_simp
    rw [this, h32]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ c * Lg / 2)]
  have h5 : N ^ (a + b) ≤ Real.exp (c * Lg ^ (3 / 2 : ℝ) / 2) := h1.trans (h2.trans (Real.exp_le_exp.2 h4))
  have hNb : 0 < N ^ b := Real.rpow_pos_of_pos hN0 b
  refine le_of_mul_le_mul_right ?_ hNb
  rw [← Real.rpow_add hN0 (-b) b, neg_add_cancel, Real.rpow_zero, mul_assoc, ← Real.rpow_add hN0]
  calc Real.exp (-(c * Lg ^ (3 / 2 : ℝ) / 2)) * N ^ (a + b)
      ≤ Real.exp (-(c * Lg ^ (3 / 2 : ℝ) / 2)) * Real.exp (c * Lg ^ (3 / 2 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

/-! ## 3. Deterministic facts on the class `Φ_E` -/

/-- **The class of G2 for the exp assumption**: `Φ_E(r) = (W^{-d} wT^c_{t,D}(r))^{1/2}`, `wT = tailW` of `(defWTTlD)`
(`Defs/Tail.lean:52`); `Φ_E² = W^{-d} wT` is the right side of `(LW_assm_exp)` (`LWLoopExp`, `Graph/LWPins.lean:274`). -/
def lwXE_phi (d L : ℕ) (W g t c D r : ℝ) : ℝ := Real.sqrt ((W ^ d)⁻¹ * tailW d L g t c W D r)

private theorem lwXE_phi_pos {d L : ℕ} {W g t c D : ℝ} (hW : 0 < W) (r : ℝ) : 0 < lwXE_phi d L W g t c D r :=
  Real.sqrt_pos.2 (mul_pos (inv_pos.2 (pow_pos hW d)) (tailW_pos hW r))

private theorem lwXE_phi_sq {d L : ℕ} {W g t c D : ℝ} (hW : 0 < W) (r : ℝ) :
    lwXE_phi d L W g t c D r ^ 2 = (W ^ d)⁻¹ * tailW d L g t c W D r :=
  Real.sq_sqrt (mul_pos (inv_pos.2 (pow_pos hW d)) (tailW_pos hW r)).le

/-- **The cost of shifting the argument of `𝒯_t`** (paper-delta candidate `T2348a`): for `0 ≤ a`, `0 ≤ b ≤ ρ + a`,
`𝒯_t(a) ≤ (ρ+1)^{d-2} e^{√(ρ/ℓ_t)} 𝒯_t(b)` (`B_{t,a} ≤ (ρ+1)^{d-2} B_{t,b}`: the zero mode is common, `a + 1 ≥ (b+1)/(ρ+1)`;
`√b ≤ √ρ + √a`). -/
private theorem lwXE_tailT_shift {d L : ℕ} {g t a b ρ : ℝ} (hL : 1 ≤ (L : ℝ)) (ha : 0 ≤ a) (hρ : 0 ≤ ρ)
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
private theorem lwXE_tailW_shift {d L : ℕ} {W g t c D ρ r₁ r₂ : ℝ} (hW : 0 < W) (hL : 1 ≤ (L : ℝ)) (hc : 0 ≤ c)
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
          lwXE_tailT_shift hL (le_min hr₁ hc) hρ hmin (le_min hr₂ hc)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
  · calc W ^ (-D) ≤ ((ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (ρ / ellT L g t))) * W ^ (-D) :=
          le_mul_of_one_le_left hWD hK1
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) (by linarith)

/-- **`Φ_E(m) ≤ K_n Φ_E(ℓ')` for `ℓ' ≤ 2ρ + m`** (the comparability that replaces `(eq:Psi)` in `auxGraph2_phi_cmp`,
`Graph/AuxGraph2.lean:723`): `K_n = ((2ρ+1)^{d-2} e^{√(2ρ/ℓ_t)})^{1/2}`. -/
private theorem lwXE_phi_cmp {d L : ℕ} {W g t c D ρ ℓ' m : ℝ} (hW : 0 < W) (hL : 1 ≤ (L : ℝ)) (hc : 0 ≤ c) (hρ : 0 ≤ ρ)
    (hℓ' : 0 ≤ ℓ') (hm : 0 ≤ m) (h : ℓ' ≤ 2 * ρ + m) :
    lwXE_phi d L W g t c D m ≤
      Real.sqrt ((2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t))) * lwXE_phi d L W g t c D ℓ' := by
  unfold lwXE_phi
  have hK : 0 ≤ (2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t)) := by positivity
  rw [← Real.sqrt_mul hK]
  refine Real.sqrt_le_sqrt ?_
  have hs := lwXE_tailW_shift (d := d) (L := L) (W := W) (g := g) (t := t) (c := c) (D := D) hW hL hc
    (by linarith : 0 ≤ 2 * ρ) hm hℓ' h
  calc (W ^ d)⁻¹ * tailW d L g t c W D m
      ≤ (W ^ d)⁻¹ * ((2 * ρ + 1) ^ (d - 2) * Real.exp (Real.sqrt (2 * ρ / ellT L g t)) * tailW d L g t c W D ℓ') :=
        mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- **The comparison with the target** (regime `λ²/L² ≤ 1 - t`, `0 ≤ r ≤ L`): `Φ_E(r) ≤ (1 + 2^{d-1}) (𝖳_t(r ∧ c) + W^{-D})`
for the class at `2D` (`tailW_regime1_bounds`: the zero mode of `B_{t,r}` is dominated by `zeroMode_le_of_ge`; `W^{-d-2D} ≤ (W^{-D})²`). -/
private theorem lwXE_phi_le {d L : ℕ} {W g t c D r : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) (hW : 1 ≤ W)
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
private theorem lwXE_window {d L : ℕ} {W g t c D 𝔡 : ℝ} (hW : 0 < W) (ht0 : 0 ≤ t) (ht : t < 1) (hg : 0 ≤ g)
    (hg' : g ≤ 𝔡⁻¹) (hc : 0 ≤ c) :
    (W ^ d)⁻¹ ≤ (1 + (𝔡⁻¹) ^ 2) * lwXE_phi d L W g t c D 0 ^ 2 := by
  rw [lwXE_phi_sq hW]
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

/-! ## 4. The private helpers of `Graph/AuxGraph2.lean` reached from `lwXiClaim_holds`, and the core of conjunct 2

Copied (`AuxGraph2.lean` is not writable) with the renames `auxGraph2_ ↦ lwXE_`; the lattice facts come from the merged
`anpKey_zdistInf_tri`, `anpKey_zdistInf_sub_comm` (`Graph/AnpKey.lean:91-101`).  Two adaptations: `lwXE_xiSq_le` carries the
window constant `C₃` instead of `C₃²`; `lwXE_core` is the chain of `lwXiClaim_holds` (`:1030-1062`) after the loop bound, in
terms of one parameter `u = N^{τ/16}`. -/

private theorem lwXE_tri_real {d L : ℕ} [NeZero L] (x y w : Zd d L) :
    (zdistInf d L (x - w) : ℝ) ≤ (zdistInf d L (x - y) : ℝ) + (zdistInf d L (y - w) : ℝ) := by
  exact_mod_cast anpKey_zdistInf_tri x y w

private theorem lwXE_zdistInf_le {d : ℕ} (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

private theorem lwXE_xiSq_nonneg {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : 0 ≤ lwXiSq sz E t ρ n a₁ a₂ ω := by
  unfold lwXiSq
  refine add_nonneg (Finset.sum_nonneg fun b₁ _ => Finset.sum_nonneg fun b₂ _ =>
    Finset.sum_nonneg fun σ _ => norm_nonneg _) ?_
  have : (0 : ℝ) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  split_ifs <;> positivity

private theorem lwXE_xiVar_sq {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (a₁ a₂ : Zd d (sz.L n))
    (ω : sz.SeqΩ) : lwXiVar sz E t ρ n a₁ a₂ ω ^ 2 = lwXiSq sz E t ρ n a₁ a₂ ω :=
  Real.sq_sqrt (lwXE_xiSq_nonneg sz E t ρ n a₁ a₂ ω)

private theorem lwXE_pair_sum (g : (Fin 2 → Bool) → ℝ) :
    ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)), g σ =
      g ![true, false] + g ![false, true] := by
  rw [Finset.sum_pair]
  intro h
  have := congrFun h 0
  simp at this

/-- A failure event of `(ξ, ζ)` that is eventually contained in the failure event of one domination `(ξ₁, ζ₁)` (the parameter
types may differ). -/
private theorem lwXE_prec_of_imp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} {size : ℕ → ℕ}
    {U V : ℕ → Type*} {ξ ζ : ∀ l, U l → Ω → ℝ}
    {ξ₁ ζ₁ : ∀ l, V l → Ω → ℝ} (h : StochDomAt P size ξ₁ ζ₁)
    (himp : ∀ τ : ℝ, 0 < τ → ∃ τ' : ℝ, 0 < τ' ∧ ∀ᶠ l : ℕ in atTop, ∀ (ω : Ω) (u : U l),
      (size l : ℝ) ^ τ * ζ l u ω < ξ l u ω → ∃ v : V l, (size l : ℝ) ^ τ' * ζ₁ l v ω < ξ₁ l v ω) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  obtain ⟨τ', hτ', hs⟩ := himp τ hτ
  filter_upwards [hs, h τ' hτ' D hD] with l h1 h2
  refine (MeasureTheory.measure_mono ?_).trans h2
  rintro ω ⟨u, hu⟩
  exact h1 ω u hu

/-- The flow facts used by the probabilistic targets: `|E_n| < 2`, `t_n < 1`, admissibility. -/
private theorem lwXE_flow_facts {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hκ : 0 < κ) (hε : 0 < ε)
    (h : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (h1 : ∀ n, t n ≤ lemT (z n)) :
    (∀ n, |STflowE z n| < 2) ∧ (∀ n, t n < 1) ∧ sz.Admissible 𝔠 𝔡 := by
  obtain ⟨hA, hE, ht, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε h h1
  exact ⟨fun n => (hE n).trans (by linarith), ht, hA⟩

private theorem lwXE_etaT_le_one {E t : ℝ} (hE : |E| < 2) (h0 : 0 ≤ t) (ht : t < 1) : etaT E t ≤ 1 := by
  have h1 : (mE E).im ≤ 1 := by
    rw [mE_im]
    have : Real.sqrt (4 - E ^ 2) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [sq_nonneg E]⟩
    linarith
  have h2 : 0 < (mE E).im := mE_im_pos hE
  unfold etaT
  nlinarith

/-- Polynomial radii are `N^{o(1)}`: `c (aρ + b)^e ≤ N^τ` eventually. -/
private theorem lwXE_ev_poly {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {ρ : ℕ → ℝ}
    (hρ0 : ∀ n, 0 ≤ ρ n)
    (hρ : ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, ρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ)
    {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (he : 0 ≤ e) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, c * (a * ρ n + b) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ τ := by
  set τ₂ := τ / (2 * (e + 1)) with hτ₂
  have hτ₂0 : 0 < τ₂ := by positivity
  have h1 := hρ τ₂ hτ₂0
  have h2 : ∀ᶠ n in atTop, c * (a + b) ^ e ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hsize).eventually_ge_atTop _
  filter_upwards [h1, h2, hsize.eventually_ge_atTop 1] with n h1 h2 hX1
  set X := ((sz.size n : ℕ) : ℝ) with hXdef
  have hX0 : 0 < X := by linarith
  have e1 : a * ρ n + b ≤ (a + b) * X ^ τ₂ := by
    calc a * ρ n + b ≤ (a + b) * (ρ n + 1) := by nlinarith [hρ0 n]
      _ ≤ (a + b) * X ^ τ₂ := mul_le_mul_of_nonneg_left h1 (by linarith)
  have e2 : (a * ρ n + b) ^ e ≤ (a + b) ^ e * X ^ (τ₂ * e) := by
    have : 0 ≤ a * ρ n + b := by have := hρ0 n; positivity
    calc (a * ρ n + b) ^ e ≤ ((a + b) * X ^ τ₂) ^ e := Real.rpow_le_rpow this e1 he
      _ = (a + b) ^ e * (X ^ τ₂) ^ e := Real.mul_rpow (by linarith) (by positivity)
      _ = (a + b) ^ e * X ^ (τ₂ * e) := by rw [← Real.rpow_mul hX0.le]
  have e3 : X ^ (τ₂ * e) ≤ X ^ (τ / 2) := by
    refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
    have : τ₂ * (e + 1) = τ / 2 := by rw [hτ₂]; field_simp
    nlinarith
  calc c * (a * ρ n + b) ^ e ≤ c * ((a + b) ^ e * X ^ (τ₂ * e)) := mul_le_mul_of_nonneg_left e2 hc
    _ = (c * (a + b) ^ e) * X ^ (τ₂ * e) := by ring
    _ ≤ X ^ (τ / 2) * X ^ (τ / 2) :=
        mul_le_mul h2 e3 (Real.rpow_nonneg hX0.le _) (Real.rpow_nonneg hX0.le _)
    _ = X ^ τ := by rw [← Real.rpow_add hX0]; congr 1; ring

/-- **A radius with `√ρ ≤ τ log N` eventually for every `τ > 0` is `N^{o(1)}`**: `ρ + 1 ≤ N^τ` eventually for every `τ > 0`
(`ρ ≤ (log N)²` and `log N ≤ N^{τ/4}/(τ/4)`). -/
private theorem lwXE_rho_poly {d : ℕ} (sz : Sizes d) (hsize : sz.SizeTendsto) {ρ : ℕ → ℝ} (hρ0 : ∀ n, 0 ≤ ρ n)
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

private theorem lwXE_card_ball {d L : ℕ} [NeZero L] (c : Zd d L) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ).card : ℕ) : ℝ) ≤
      (2 * ρ + 1) ^ d := by
  have := RBM.Ind.DecayLoopB_card_ball (L := L) c hρ
  have e : (Finset.univ.filter fun b : Zd d L => (zdistInf d L (b - c) : ℝ) ≤ ρ) =
      Finset.univ.filter fun u : Zd d L => (zdistInf d L (c - u) : ℝ) ≤ ρ := by
    refine Finset.filter_congr fun b _ => ?_
    rw [anpKey_zdistInf_sub_comm]
  rw [e]; exact this

/-- **`ξ([a₁],[a₂])² ≲ Φ(|a₁ - a₂|)²` from `(LW_assm)` and the comparability** (target 3 (c), deterministic part; the twin of
`auxGraph2_xiSq_le`, `AuxGraph2.lean:828`, with the window constant `C₃` for `W^{-d} ≤ C₃ Φ(0)²`): if every
`‖𝓛^{(2)}_{(s,!s),(b₁,b₂)}‖ ≤ B Φ(|b₁ - b₂|)²`, `Φ(m) ≤ K Φ(ℓ)` for `ℓ ≤ 2ρ + m`, then
`ξ² ≤ (2 (2ρ+1)^{2d} B + C₃) K² Φ(|a₁ - a₂|)²`. -/
private theorem lwXE_xiSq_le {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ)
    (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n) {B K C₃ : ℝ} (hB : 0 ≤ B) (hC₃ : 0 ≤ C₃)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖Lloop sz n (E n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
        B * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ K * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ * Φn 0 ^ 2) (a₁ a₂ : Zd d (sz.L n)) :
    lwXiSq sz E t ρ n a₁ a₂ ω ≤
      (2 * (2 * ρ n + 1) ^ (2 * d) * B + C₃) * K ^ 2 *
        Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 := by
  classical
  set ℓ : ℝ := ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) with hℓ
  have hℓ0 : 0 ≤ ℓ := Nat.cast_nonneg _
  set Q : ℝ := K ^ 2 * Φn ℓ ^ 2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hterm : ∀ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∀ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
      ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
        ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * B * Q := by
    intro b₁ hb₁ b₂ hb₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb₁ hb₂
    set m : ℝ := ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) with hm
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have h1 : (zdistInf d (sz.L n) (a₁ - b₁) : ℝ) ≤ ρ n := by
      rw [anpKey_zdistInf_sub_comm]; exact hb₁
    have hlm : ℓ ≤ 2 * ρ n + m := by
      have t1 := lwXE_tri_real a₁ b₁ a₂
      have t3 := lwXE_tri_real b₁ b₂ a₂
      rw [hℓ, hm]
      linarith
    have hΦ : Φn m ≤ K * Φn ℓ := hcmp ℓ m hℓ0 hm0 hlm
    have hsq : Φn m ^ 2 ≤ Q := by
      rw [hQ, ← mul_pow]
      exact pow_le_pow_left₀ (hΦnn m hm0) hΦ 2
    rw [lwXE_pair_sum]
    have e1 := hloop true b₁ b₂
    have e2 := hloop false b₁ b₂
    have e3 : B * Φn m ^ 2 ≤ B * Q := mul_le_mul_of_nonneg_left hsq hB
    simp only [Bool.not_true, Bool.not_false] at e1 e2
    linarith
  have hfirst : ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
      ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
        ∑ σ ∈ ({![true, false], ![false, true]} : Finset (Fin 2 → Bool)),
          ‖Lloop sz n (E n) (t n) σ ![b₁, b₂] ω‖ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
    calc _ ≤ ∑ b₁ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n),
          ∑ b₂ ∈ Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n),
            2 * B * Q :=
          Finset.sum_le_sum fun b₁ hb₁ => Finset.sum_le_sum fun b₂ hb₂ => hterm b₁ hb₁ b₂ hb₂
      _ = (((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₁) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
          ((((Finset.univ.filter (fun b : Zd d (sz.L n) => (zdistInf d (sz.L n) (b - a₂) : ℝ) ≤ ρ n)).card : ℕ) : ℝ) *
            (2 * B * Q)) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 * ρ n + 1) ^ d * ((2 * ρ n + 1) ^ d * (2 * B * Q)) := by
          have c1 := lwXE_card_ball (d := d) a₁ hρ
          have c2 := lwXE_card_ball (d := d) a₂ hρ
          have hBQ : 0 ≤ 2 * B * Q := by positivity
          exact mul_le_mul c1 (mul_le_mul_of_nonneg_right c2 hBQ) (by positivity) (by positivity)
      _ = 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q := by
          rw [show 2 * d = d + d from two_mul d, pow_add]; ring
  have hsecond : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      (if (zdistInf d (sz.L n) (a₁ - a₂) : ℝ) ≤ ρ n then 1 else 0) ≤ C₃ * Q := by
    split_ifs with hc
    · have : Φn 0 ≤ K * Φn ℓ := hcmp ℓ 0 hℓ0 le_rfl (by rw [hℓ]; linarith)
      have h0 : 0 ≤ Φn 0 := hΦnn 0 le_rfl
      have : Φn 0 ^ 2 ≤ Q := by
        rw [hQ, ← mul_pow]; exact pow_le_pow_left₀ h0 this 2
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 ≤ C₃ * Φn 0 ^ 2 := by rw [mul_one]; exact hW
        _ ≤ C₃ * Q := mul_le_mul_of_nonneg_left this hC₃
    · rw [mul_zero]; positivity
  unfold lwXiSq
  calc _ ≤ 2 * (2 * ρ n + 1) ^ (2 * d) * B * Q + C₃ * Q := add_le_add hfirst hsecond
    _ = _ := by rw [hQ]; ring

/-- `N^{𝔠 ε₁/2} W^{-ε₁} ≤ W^{-ε₁/2} ≤ 1` (`W ≥ N^𝔠`): the entry law at `τ = 𝔠 ε₁/2` is `≤ W^{-ε₁/2}`. -/
private theorem lwXE_pow_small {d : ℕ} (sz : Sizes d) (n : ℕ) {𝔠 ε₁ : ℝ} (h𝔠 : 0 < 𝔠) (hε₁ : 0 < ε₁)
    (hb : ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ (sz.W n : ℝ)) :
    ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) ≤ ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) ∧
      ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) ≤ 1 := by
  have hτ : 0 < 𝔠 * ε₁ / 2 := by positivity
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have h2 : ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) := by
    have := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := 𝔠 * ε₁ / 2) hτ.le
    have e : 𝔠 * ε₁ / 2 / 𝔠 = ε₁ / 2 := by field_simp
    rwa [e] at this
  refine ⟨?_, Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith)⟩
  calc ((sz.size n : ℕ) : ℝ) ^ (𝔠 * ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁)
      ≤ ((sz.W n : ℕ) : ℝ) ^ (ε₁ / 2) * ((sz.W n : ℕ) : ℝ) ^ (-ε₁) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW.le _)
    _ = ((sz.W n : ℕ) : ℝ) ^ (-(ε₁ / 2)) := by
        rw [← Real.rpow_add hW]; congr 1; ring

private theorem lwXE_rpow_nat (X : ℝ) (hX : 0 ≤ X) (x : ℝ) (k : ℕ) : (X ^ x) ^ k = X ^ (x * k) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]

/-- The arithmetic of target 3 (c), in powers of `u`. -/
private theorem lwXE_num {u A₁ K2 S : ℝ} (hu : 1 ≤ u) (hA : 2 * A₁ ≤ u ^ 2) (hC : S ≤ u ^ 4)
    (hK : K2 ≤ u ^ 2) (h2 : 2 ≤ u ^ 8) (hA0 : 0 ≤ A₁) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K2) :
    (2 * A₁ * u ^ 4 + S) * K2 ≤ (u ^ 8) ^ 2 := by
  have hu0 : 0 ≤ u := by linarith
  have h1 : 2 * A₁ * u ^ 4 ≤ u ^ 6 := by
    calc _ ≤ u ^ 2 * u ^ 4 := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = u ^ 6 := by ring
  have h2' : u ^ 4 ≤ u ^ 6 := pow_le_pow_right₀ hu (by norm_num)
  have h3 : 2 * A₁ * u ^ 4 + S ≤ 2 * u ^ 6 := by linarith
  have h4 : (2 * A₁ * u ^ 4 + S) * K2 ≤ 2 * u ^ 6 * u ^ 2 :=
    mul_le_mul h3 hK hK0 (by positivity)
  have h5 : 2 * u ^ 6 * u ^ 2 = 2 * u ^ 8 := by ring
  have h6 : 2 * u ^ 8 ≤ (u ^ 8) ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 (pow_nonneg hu0 8)
    nlinarith
  linarith

/-- **The core of conjunct 2** (the chain of `lwXiClaim_holds`, `AuxGraph2.lean:1030-1062`, after the loop bound): with
`u ≥ 1`, the loop bound `‖𝓛^{(2)}‖ ≤ u⁴ Φ²`, the comparability `Φ(m) ≤ K_n Φ(ℓ)` for `ℓ ≤ 2ρ + m`, the window
`W^{-d} ≤ C₃ Φ(0)²` and the size conditions `2 (2ρ+1)^{2d} ≤ u²`, `K_n ≤ u`, `C₃ ≤ u⁴`, `2 ≤ u⁸`:
`ξ([a₁],[a₂]) ≤ u⁸ Φ(|a₁ - a₂|)`. -/
private theorem lwXE_core {d : ℕ} (sz : Sizes d) (E t ρ : ℕ → ℝ) (n : ℕ) (ω : sz.SeqΩ) (Φn : ℝ → ℝ) (hρ : 0 ≤ ρ n)
    {u Kn C₃ : ℝ} (hu : 1 ≤ u) (hKn0 : 0 ≤ Kn) (hC₃ : 0 ≤ C₃)
    (hloop : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
      ‖Lloop sz n (E n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤ u ^ 4 * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2)
    (hΦnn : ∀ r : ℝ, 0 ≤ r → 0 ≤ Φn r)
    (hcmp : ∀ ℓ m : ℝ, 0 ≤ ℓ → 0 ≤ m → ℓ ≤ 2 * ρ n + m → Φn m ≤ Kn * Φn ℓ)
    (hW : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ C₃ * Φn 0 ^ 2)
    (q1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2) (q2 : Kn ≤ u) (q3 : C₃ ≤ u ^ 4) (q4 : 2 ≤ u ^ 8)
    (a₁ a₂ : Zd d (sz.L n)) :
    lwXiVar sz E t ρ n a₁ a₂ ω ≤ u ^ 8 * Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) := by
  have hu0 : 0 ≤ u := by linarith
  have hbound := lwXE_xiSq_le sz E t ρ n ω Φn hρ (B := u ^ 4) (K := Kn) (C₃ := C₃) (by positivity) hC₃
    hloop hΦnn hcmp hW a₁ a₂
  have hnum := lwXE_num hu q1 q3 (pow_le_pow_left₀ hKn0 q2 2) q4 (pow_nonneg (by linarith) _) hC₃ (sq_nonneg _)
  have hΦ0 := hΦnn _ (Nat.cast_nonneg (zdistInf d (sz.L n) (a₁ - a₂)))
  have hsq : lwXiSq sz E t ρ n a₁ a₂ ω ≤ (u ^ 8 * Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ)) ^ 2 := by
    calc _ ≤ _ := hbound
      _ = ((2 * (2 * ρ n + 1) ^ (2 * d) * u ^ 4 + C₃) * Kn ^ 2) *
            Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ (u ^ 8) ^ 2 * Φn ((zdistInf d (sz.L n) (a₁ - a₂) : ℕ) : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
      _ = _ := by ring
  unfold lwXiVar
  exact Real.sqrt_le_iff.2 ⟨by positivity, hsq⟩

/-! ## 5. `claim:xi` for the exp class -/

/-- **`claim:xi` for the exp class** (`7_8:884-890`, `(eq:Gbyxi2)`; Amend 1): under `(LW_assm_exp)` (`LWAssmExp`), and
`‖G_t - M‖_max ≺ W^{-ε₁}`, the variables `lwXiVar` at a radius `ρ` with `√ρ ≤ τ log N` eventually for every `τ > 0` satisfy
`LWXiE`: symmetric, non-negative, `ξ([a₁],[a₂]) ≺ 𝖳_t(|a₁ - a₂|_∞ ∧ ℓ) + W^{-D}` on the pairs with `λ²/L² < 1 - t`, and
`Σ_{a₂} ξ([a₁],[a₂])² ≺ (W^d η_t)⁻¹` (Ward's identity).  Conjunct 2: the class `Φ_E = (W^{-d} wT^ℓ_{t,2D})^{1/2}`
(`lwXE_phi`) is the class of `LWLoopExp` at `2D`; the comparability `Φ_E(m) ≤ K_n Φ_E(ℓ')` (`lwXE_phi_cmp`) replaces
`auxGraph2_phi_cmp`; the comparison with the target is `lwXE_phi_le`. -/
theorem lwXiExpClaim_holds (d : ℕ) : LWXiExpClaim d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ Ψ ℓ hAssm ε₁ hε₁ hent D hD ρ hρ0 hρ
  obtain ⟨hE, htlt, hadm⟩ := lwXE_flow_facts sz hκ hε hflow ht1
  have hsize : sz.SizeTendsto := hadm.2.2.1
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hd0 : 0 < d := by omega
  have hρ' := lwXE_rho_poly sz hsize hρ0 hρ
  obtain ⟨-, -, -, hℓ0, -, hloopE⟩ := hAssm
  refine ⟨fun n α β ω => ⟨lwXiVar_nonneg sz _ t ρ n α β ω, lwXiVar_symm sz _ t ρ n α β ω⟩, ?_, ?_⟩
  · -- conjunct 2: `ξ ≺ 𝖳_t(|a₁ - a₂|_∞ ∧ ℓ) + W^{-D}` on `λ²/L² < 1 - t`
    have hD2 : 0 < 2 * D := by positivity
    refine lwXE_prec_of_imp (hloopE (2 * D) hD2) ?_
    intro τ hτ
    refine ⟨τ / 4, by positivity, ?_⟩
    have p1 := lwXE_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 2) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 8) (by positivity)
    have p2 := lwXE_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 1) (e := ((d - 2 : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) (τ := τ / 16) (by positivity)
    have p4 : ∀ᶠ n in atTop, 1 + (𝔡⁻¹) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 4) :=
      ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
    have p5 : ∀ᶠ n in atTop, (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
    have p6 : ∀ᶠ n in atTop, 1 + (2 : ℝ) ^ (d - 1) ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop (by positivity)).comp hsize).eventually_ge_atTop _
    filter_upwards [p1, p2, hρ (τ / 32) (by positivity), p4, p5, p6, hadm.2.2.2.2,
      hsize.eventually_ge_atTop 1] with n q1 q2 q3 q4 q5 q6 hWO hX1
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
    set u : ℝ := X ^ (τ / 16) with hu
    have hu1 : 1 ≤ u := Real.one_le_rpow hX1 (by positivity)
    have hpow : ∀ k : ℕ, X ^ (τ / 16 * (k : ℝ)) = u ^ k := fun k => (lwXE_rpow_nat X hX0.le _ k).symm
    have e2 : X ^ (τ / 8) = u ^ 2 := by rw [← hpow 2]; congr 1; push_cast; ring
    have e4 : X ^ (τ / 4) = u ^ 4 := by rw [← hpow 4]; congr 1; push_cast; ring
    have e8 : X ^ (τ / 2) = u ^ 8 := by rw [← hpow 8]; congr 1; push_cast; ring
    have e16 : X ^ τ = u ^ 16 := by rw [← hpow 16]; congr 1; push_cast; ring
    -- the class `Φ_E` and the loop bound on the complement of the bad event
    set Φn : ℝ → ℝ := lwXE_phi d (sz.L n) W (sz.lam n) (t n) (ℓ n) (2 * D) with hΦn
    have hΦpos : ∀ r : ℝ, 0 < Φn r := fun r => lwXE_phi_pos hW0 r
    have hloop' : ∀ (s : Bool) (b₁ b₂ : Zd d (sz.L n)),
        ‖Lloop sz n (STflowE z n) (t n) ![s, !s] ![b₁, b₂] ω‖ ≤
          u ^ 4 * Φn ((zdistInf d (sz.L n) (b₁ - b₂) : ℕ) : ℝ) ^ 2 := by
      intro s b₁ b₂
      have := hno (s, b₁, b₂)
      rw [hΦn, lwXE_phi_sq hW0, ← e4]
      exact this
    set Kn : ℝ := Real.sqrt ((2 * ρ n + 1) ^ (d - 2) *
      Real.exp (Real.sqrt (2 * ρ n / ellT (sz.L n) (sz.lam n) (t n)))) with hKn
    have hKn0 : 0 ≤ Kn := Real.sqrt_nonneg _
    have hcmp : ∀ ℓ' m : ℝ, 0 ≤ ℓ' → 0 ≤ m → ℓ' ≤ 2 * ρ n + m → Φn m ≤ Kn * Φn ℓ' :=
      fun ℓ' m hℓ' hm h => lwXE_phi_cmp hW0 hL1 (hℓ0 n) (hρ0 n) hℓ' hm h
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
    have hwin : (W ^ d)⁻¹ ≤ (1 + (𝔡⁻¹) ^ 2) * Φn 0 ^ 2 :=
      lwXE_window hW0 (ht0 n) (htlt n) hlam0 hWO.2 (hℓ0 n)
    have hq1 : 2 * (2 * ρ n + 1) ^ (2 * d) ≤ u ^ 2 := by
      have := q1
      rw [Real.rpow_natCast, e2] at this
      exact this
    have hq3 : 1 + (𝔡⁻¹) ^ 2 ≤ u ^ 4 := by rw [← e4]; exact q4
    have hq4 : 2 ≤ u ^ 8 := by rw [← e8]; exact q5
    have hcore := lwXE_core sz (STflowE z) t ρ n ω Φn (hρ0 n) hu1 hKn0 (by positivity) hloop'
      (fun r _ => (hΦpos r).le) hcmp hwin hq1 hKnu hq3 hq4 p.1.1 p.1.2
    -- the comparison with the target on `λ²/L² < 1 - t`
    have hrL : ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
      exact_mod_cast lwXE_zdistInf_le (sz.L n) _
    have hcomp := lwXE_phi_le (d := d) (L := sz.L n) (W := W) (g := sz.lam n) (t := t n) (c := ℓ n) (D := D)
      (r := ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ)) (by omega) hL1 (htlt n) hW1 p.2.le (hℓ0 n)
      (Nat.cast_nonneg _) hrL
    have hp' : X ^ τ * (sfT d (sz.L n) W (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D)) <
        lwXiVar sz (STflowE z) t ρ n p.1.1 p.1.2 ω := hp
    have hζ0 : 0 ≤ sfT d (sz.L n) W (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D) :=
      add_nonneg (sfT_nonneg _) (Real.rpow_nonneg hW0.le _)
    have hCE : 1 + (2 : ℝ) ^ (d - 1) ≤ u ^ 8 := by rw [← e8]; exact q6
    have hfin : lwXiVar sz (STflowE z) t ρ n p.1.1 p.1.2 ω ≤ X ^ τ * (sfT d (sz.L n) W (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D)) := by
      calc _ ≤ u ^ 8 * Φn ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) := hcore
        _ ≤ u ^ 8 * ((1 + 2 ^ (d - 1)) * (sfT d (sz.L n) W (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D))) :=
            mul_le_mul_of_nonneg_left hcomp (by positivity)
        _ ≤ u ^ 8 * (u ^ 8 * (sfT d (sz.L n) W (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (p.1.1 - p.1.2) : ℕ) : ℝ) (ℓ n)) + W ^ (-D))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCE hζ0) (by positivity)
        _ = _ := by rw [e16]; ring
    linarith
  · -- conjunct 3: `Σ_β ξ² ≺ (W^d η)⁻¹` (Ward's identity on `‖G - M‖_max ≤ 1`)
    refine lwXE_prec_of_imp hent ?_
    intro τ hτ
    refine ⟨𝔠 * ε₁ / 2, by positivity, ?_⟩
    have p1 := lwXE_ev_poly sz hsize hρ0 hρ' (a := 2) (b := 1) (c := 5) (e := ((2 * d : ℕ) : ℝ))
      (by norm_num) (by norm_num) (by norm_num) (Nat.cast_nonneg _) hτ
    filter_upwards [hadm.2.2.2.1, p1] with n hb q1
    intro ω α hα
    by_contra hno
    push Not at hno
    have hsm := lwXE_pow_small sz n h𝔠 hε₁ hb
    have hA : ∀ x y : Idx d (sz.L n) (sz.W n), ‖STGM sz n (STflowE z n) (t n) ω x y‖ ≤ 1 := fun x y =>
      ((hno (x, y)).trans hsm.1).trans hsm.2
    have hw := lwXi_ward_sum sz (STflowE z) t ρ n (hE n) (htlt n) (hρ0 n) ω hA α
    set X : ℝ := ((sz.size n : ℕ) : ℝ) with hXdef
    set Q : ℝ := ((((sz.W n : ℕ) : ℝ) ^ d) * etaT (STflowE z n) (t n))⁻¹ with hQ
    have hα' : X ^ τ * Q < ∑ β, lwXiVar sz (STflowE z) t ρ n α β ω ^ 2 := hα
    simp_rw [lwXE_xiVar_sq] at hα'
    have hη0 : 0 < etaT (STflowE z n) (t n) := etaT_pos (hE n) (htlt n)
    have hη1 : etaT (STflowE z n) (t n) ≤ 1 := lwXE_etaT_le_one (hE n) (ht0 n) (htlt n)
    have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
      have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      positivity
    have hQ0 : 0 < Q := inv_pos.2 (mul_pos hWd hη0)
    have hWQ : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ Q :=
      inv_anti₀ (mul_pos hWd hη0) (by nlinarith)
    have hρ1 : (1 : ℝ) ≤ 2 * ρ n + 1 := by have := hρ0 n; linarith
    have hA01 : (2 * ρ n + 1) ^ d ≤ (2 * ρ n + 1) ^ (2 * d) :=
      pow_le_pow_right₀ hρ1 (by omega)
    have hA1pos : 0 ≤ (2 * ρ n + 1) ^ (2 * d) := pow_nonneg (by linarith) _
    have hq : 5 * (2 * ρ n + 1) ^ (2 * d) ≤ X ^ τ := by
      have := q1
      rwa [Real.rpow_natCast] at this
    have hsum : ∑ β, lwXiSq sz (STflowE z) t ρ n α β ω ≤ 5 * (2 * ρ n + 1) ^ (2 * d) * Q := by
      refine hw.trans ?_
      have h1 : (2 * ρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (2 * ρ n + 1) ^ (2 * d) * Q :=
        mul_le_mul hA01 hWQ (by positivity) hA1pos
      nlinarith
    have := mul_le_mul_of_nonneg_right hq hQ0.le
    linarith

/-! ## 6. Compiled nonempty instances at `d = 3`

The merged preflight data (`sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`;
`z0`, `flow_z0`; `t ≡ 1/16 ≤ lemT z_n`; `ε₀ = ε₁ = 1/20`, `Ψ0 = W^{-1}`, `ℓ_n = ℓ_t`, `LWAssmExp` from `assmExp_of`), the radius
`ρ0 n = log N_n` (`√ρ0 ≤ τ log N` eventually for every `τ > 0`: `log N ≥ τ^{-2}`).  The subtype of conjunct 2 is all of `n`
(`strict_all`: `λ²/L² < 1 - t`) and is nonempty at every `n`.  What stays a hypothesis is another gate's stochastic input:
`LWInit` and `LWLoopExp` (`(initialGT2)`, `(LW_assm_exp)`) and the entry law `‖G_t - M‖_max ≺ W^{-ε₁}`. -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst

/-- The radius `ρ0 n = log N_n`. -/
private def lwXE_ρ0 : ℕ → ℝ := fun n => Real.log ((sz0.size n : ℕ) : ℝ)

private theorem lwXE_ρ0_nonneg (n : ℕ) : 0 ≤ lwXE_ρ0 n :=
  Real.log_nonneg (Nat.one_le_cast.2 (sz0.one_le_size n))

/-- The radius premise: `√ρ0 ≤ τ log N` eventually for every `τ > 0` (limit `√(log N)/log N = (log N)^{-1/2} → 0`). -/
private theorem lwXE_ρ0_rad :
    ∀ τ : ℝ, 0 < τ → ∀ᶠ n in atTop, Real.sqrt (lwXE_ρ0 n) ≤ τ * Real.log ((sz0.size n : ℕ) : ℝ) := by
  intro τ hτ
  have hlog : Tendsto (fun n => Real.log ((sz0.size n : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp sz0_tendsto
  filter_upwards [hlog.eventually_ge_atTop (1 / τ ^ 2)] with n hn
  have hy : 0 < Real.log ((sz0.size n : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hn
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have h1 : 1 ≤ τ ^ 2 * Real.log ((sz0.size n : ℕ) : ℝ) := by
    have := mul_le_mul_of_nonneg_left hn (sq_nonneg τ)
    rwa [mul_one_div_cancel (by positivity)] at this
  calc lwXE_ρ0 n = 1 * Real.log ((sz0.size n : ℕ) : ℝ) := by rw [one_mul]; rfl
    _ ≤ (τ ^ 2 * Real.log ((sz0.size n : ℕ) : ℝ)) * Real.log ((sz0.size n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hy.le
    _ = (τ * Real.log ((sz0.size n : ℕ) : ℝ)) ^ 2 := by ring

/-- The entry law `‖G_t - M‖_max ≺ W^{-ε₁}` at `ε₁ = 1/20` (a stochastic input, kept as a hypothesis). -/
private def lwXE_Entry : Prop :=
  Prec sz0 (U := fun n => Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n))
    (fun n p ω => ‖STGM sz0 n (STflowE z0 n) (tInst n) ω p.1 p.2‖)
    (fun n _ _ => ((sz0.W n : ℕ) : ℝ) ^ (-(1 / 20 : ℝ)))

/-- The index set of conjunct 2 (`λ²/L² < 1 - t`) is nonempty at every size at the instance. -/
example : ∀ n, Nonempty {_p : Zd 3 (sz0.L n) × Zd 3 (sz0.L n) // sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n} :=
  fun n => ⟨⟨(0, 0), strict_all n⟩⟩

/-- **Instance of `lwXiExpClaim_holds`** (`d = 3`, merged `sz0`, `t ≡ 1/16`, radius `log N`, every `D > 0`): the conclusion `LWXiE`
(symmetry, conjunct 2 on `λ²/L² < 1 - t`, the Ward bound) at the preflight data; `LWInit`, `LWLoopExp` and the entry law
stay hypotheses, every deterministic hypothesis is discharged. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst))
    (hent : lwXE_Entry) (D : ℝ) (hD : 0 < D) :
    LWXiE sz0 (STflowE z0) tInst (ℓT tInst) D (lwXiVar sz0 (STflowE z0) tInst lwXE_ρ0) :=
  lwXiExpClaim_holds 3 le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst) (assmExp_of hI hL) (1 / 20)
    (by norm_num) hent D hD lwXE_ρ0 lwXE_ρ0_nonneg lwXE_ρ0_rad

/-- **Instance of `lwTail32`** at `sz0` (`𝔠 = 1/6`), `c = 1`, `a = 2`, `b = 3`. -/
example : ∀ᶠ n in atTop, Real.exp (-(1 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) *
    ((sz0.size n : ℕ) : ℝ) ^ (2 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(3 : ℝ)) :=
  lwTail32 sz0 (by norm_num) one_pos sz0_admissible.2.2.1 sz0_admissible.2.2.2.1 2 3

/-- **Instance of `lwTail32`**, a free constant `c = 1/4` (C4 (c)), `a = 5`, `b = 1`. -/
example : ∀ᶠ n in atTop, Real.exp (-(1 / 4 * Real.log ((sz0.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) / 2)) *
    ((sz0.size n : ℕ) : ℝ) ^ (5 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
  lwTail32 sz0 (by norm_num) (by norm_num) sz0_admissible.2.2.1 sz0_admissible.2.2.2.1 5 1

end Instances

end RBM.Graph

end
