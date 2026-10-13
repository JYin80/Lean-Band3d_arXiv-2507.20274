/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BATermHolds
import RBM3D.Graph.BAZetaExp
import RBM3D.BA.Step2CloseBA

/-!
# BA-L L5b (T2494), file B: `lem: EWGn2_N` for `1 - t > λ²/L²`, the union, BA Step 2 closed

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:15-91` (cited `7_8:line`),
`paper/tex/3_5_Loop_Hierarchy.tex:380-420`; `paper/tex/B_graphical_lemmas.tex:286-288`
("analogously"), `:408-415`.  Twin of `Graph/LWTermHolds.lean` §5-§6 (`:722-1615`) in a new file;
the second half of the row split A | B + C of ticket T2494 (file A: `Graph/BATermHolds.lean`,
merged, targets 1-3: `baLWterm_holds` and the regime `1 - t ≤ λ²/L²`).

## Contents (namespace `RBM.BA`; helpers carry the stem `BATermHoldsB_`)

5. The deterministic facts of the `T` side: the arithmetic `BATermHoldsB_arithT` (the band's
   `LWTermHolds_arithT`, `:934`, for the part without the closing edge, plus the **`M`-part** of
   the closing edge `G_{yx} = (G - M)_{yx} + M_{yx}`: the weight `W^{-d}` of the equal-offset
   pairs, `Wd Mb ≤ cs Kz s`), and the decay of `M` against the profile `𝖳`,
   `BATermHoldsB_sfMb` (`𝖳_t(0) e^{-c r} ≤ E 𝖳_t(r ∧ ℓ)`).
6. The events of the `T` side: the `M`-part facts without the standing hypotheses of file A
   (`BATermHoldsB_Mpart`), the window `ε₁` (`BATermHoldsB_eps`), the radius
   `ρ_n = log N √(log N)`, `(eq:directG2)` at BA (`BATermHoldsB_GM_T`: `baGbyZeta_holds` at
   `R = 0` then `baZetaExpClaim_holds`; this replaces the band's `LWTermHolds_Gij_T` and its
   `ξ²` lemma), `(GavLGEX)` at `Ψ_t = max (W^{-d/2}, Bctl^{1/2})` (`BATermHoldsB_avg`,
   `baGbEXPav_holds`), the Markov step (`BATermHoldsB_fT`, from `baLWMomentExp_closed`), and the
   reduction for `D ≥ 2d + 1` (`BATermHoldsB_core`, the pathwise bound `BATermHolds_LWE_le` of
   file A).
7. **`baLWtermExpS_holds`** (target 4, statement def `BALWtermExpS`; every `D > 0` through
   `D' = max (D, 2d + 1)`), **`baLWtermExp_holds : ∀ d, BALWtermExp d`** (target 5, the union
   with `baLWtermExpN_holds` of file A) and **`baStep2_closed : ∀ d, BAStep2 d`** (target 6, one
   line from `baStep2_holds`).
8. Compiled nonempty instances of targets 4, 5, 6 at `d = 3`.

**Public names**: `BALWtermExpS`, `baLWtermExpS_holds`, `baLWtermExp_holds`, `baStep2_closed`;
every helper is `private`.
**Premise scan** (`scanPremises` of `Test/Axioms.lean`): the public theorems have the binder
`d : ℕ` only (the pin hypothesis `LWAssmExpgL` occurs inside the pin `BALWtermExp` and the
statement def `BALWtermExpS`); the private helpers take it folded.  Private lemmas of file A and
of the band are read by `open private`.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

open private BATermHolds_W_tendsto BATermHolds_zdistInf_le BATermHolds_LWE_le BATermHolds_poly_exp from RBM3D.Graph.BATermHolds
open private LWTermHolds_arithT LWTermHolds_sfT_sq_le LWTermHolds_sfT_zero_sq LWTermHolds_A_ge LWTermHolds_tail_cmp from RBM3D.Graph.LWTermHolds

/-! ## 5. The `T` side: deterministic facts -/

/-- **The arithmetic of the `T` side with the `M`-part of the closing edge** (twin of `LWTermHolds_arithT`, `Graph/LWTermHolds.lean:934`, which it calls for the part
without the closing edge): the pathwise bound `2 (γ (φ + 4 μ γ) + W^{-d} (γ + Mb)(φ + 4 μ (γ + Mb)))` of `BATermHolds_LWE_le` (`A = 2`) with `γ = X (s + W^{-d} w)`,
`φ = X (u s + w)`, `μ ≤ X cB b²` is at most `K X³ Z` when `u (s² + W^{-d} w) ≤ 2 Z` and `s0 · Mb ≤ Kz · s`. -/
private theorem BATermHoldsB_arithT {X u b s s0 w Wd μ Mb Z Z0 cB cs Kz : ℝ}
    (hX : 1 ≤ X) (hu : 0 < u) (hb : 0 ≤ b) (hb1 : b ≤ 1) (hbu : b ≤ u) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hs0 : 0 ≤ s0) (hs01 : s0 ≤ 1) (hw : 0 ≤ w) (hWd : 0 ≤ Wd) (hWd1 : Wd ≤ 1) (hμ0 : 0 ≤ μ)
    (hcB : 0 ≤ cB) (hcs : 0 ≤ cs) (hKz : 0 ≤ Kz) (hμ : μ ≤ X * (cB * (b * b)))
    (hwu : w ≤ u ^ 2 * Wd) (hwu' : w ≤ u) (hcs' : Wd ≤ cs * s0 ^ 2)
    (hZ : u * (s ^ 2 + Wd * w) ≤ 2 * Z) (hZ0 : u * s0 ^ 2 ≤ 2 * Z0) (hMb : 0 ≤ Mb) (hMs : s0 * Mb ≤ Kz * s) :
    2 * (X * (s + Wd * w) * (X * (u * s + w) + 2 * μ * 2 * (X * (s + Wd * w))) +
      Wd * ((X * (s + Wd * w) + Mb) * (X * (u * s + w) + 2 * μ * 2 * (X * (s + Wd * w) + Mb)))) ≤
    (4 * (6 + 16 * cB + 2 * (4 + 8 * cB) * cs) + 2 * (cs * Kz * (4 + 32 * cB + 8 * Kz * cB))) * X ^ 3 * Z := by
  have hX0 : 0 < X := by linarith
  have hZ0' : 0 ≤ Z := by
    have := mul_nonneg hu.le (add_nonneg (sq_nonneg s) (mul_nonneg hWd hw)); linarith
  have hWdw : 0 ≤ Wd * w := mul_nonneg hWd hw
  -- part I: the band arithmetic with `δ = 0`
  have hI := LWTermHolds_arithT (X := X) (Γ := X) (u := u) (b := b) (s := s) (s0 := s0) (w := w) (w₂ := Wd * w)
    (Wd := Wd) (μ := μ) (cB := cB) (cs := cs) (Z := Z) (Z0 := Z0) (δ := 0) hX hX hu hb hb1 hbu hs hs1 hw hWdw hWd hWd1
    hμ0 hcB hcs hμ hwu hwu' le_rfl hcs' hZ hZ0 (Or.inl rfl)
  rw [mul_zero, mul_zero, add_zero] at hI
  set P : ℝ := X * (s + Wd * w) * (X * (u * s + w) + 2 * μ * 2 * (X * (s + Wd * w))) with hPdef
  have hP0 : 0 ≤ P := by rw [hPdef]; positivity
  -- the product bounds `Wd Mb`, `Wd Mb²`
  have hm1 : Wd * Mb ≤ cs * Kz * s := by
    calc Wd * Mb ≤ cs * s0 ^ 2 * Mb := mul_le_mul_of_nonneg_right hcs' hMb
      _ = cs * s0 * (s0 * Mb) := by ring
      _ ≤ cs * s0 * (Kz * s) := mul_le_mul_of_nonneg_left hMs (by positivity)
      _ ≤ cs * 1 * (Kz * s) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs01 hcs) (by positivity)
      _ = cs * Kz * s := by ring
  have hm2 : Wd * Mb ^ 2 ≤ cs * Kz ^ 2 * s ^ 2 := by
    calc Wd * Mb ^ 2 ≤ cs * s0 ^ 2 * Mb ^ 2 := mul_le_mul_of_nonneg_right hcs' (sq_nonneg _)
      _ = cs * (s0 * Mb) ^ 2 := by ring
      _ ≤ cs * (Kz * s) ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMs 2) hcs
      _ = cs * Kz ^ 2 * s ^ 2 := by ring
  -- `s w ≤ u s² + u Wd w`
  have hsw : s * w ≤ u * s ^ 2 + u * (Wd * w) := by
    have h1 : u * (2 * (s * w)) ≤ u * (u * s ^ 2 + u * (Wd * w)) := by
      have h2 : w * w ≤ w * (u ^ 2 * Wd) := mul_le_mul_of_nonneg_left hwu hw
      linarith [sq_nonneg (u * s - w), h2]
    have h3 : 2 * (s * w) ≤ u * s ^ 2 + u * (Wd * w) := le_of_mul_le_mul_left h1 hu
    linarith [mul_nonneg hs hw]
  have huW : 0 ≤ u * (Wd * w) := mul_nonneg hu.le hWdw
  have hu2 : 2 * (u * s ^ 2) + u * (Wd * w) ≤ 4 * Z := by linarith [hZ]
  have hus : u * s ^ 2 ≤ 2 * Z := by linarith [hZ]
  have hbb1 : b * b ≤ 1 := by
    calc b * b ≤ 1 * 1 := mul_le_mul hb1 hb1 hb zero_le_one
      _ = 1 := one_mul 1
  have hbbu : b * b ≤ u := by
    calc b * b ≤ 1 * b := mul_le_mul_of_nonneg_right hb1 hb
      _ = b := one_mul b
      _ ≤ u := hbu
  -- (i) `Wd Mb φ`
  have hT1 : Wd * Mb * (X * (u * s + w)) ≤ cs * Kz * X * (4 * Z) := by
    calc Wd * Mb * (X * (u * s + w)) ≤ (cs * Kz * s) * (X * (u * s + w)) :=
          mul_le_mul_of_nonneg_right hm1 (by positivity)
      _ = cs * Kz * X * (u * s ^ 2 + s * w) := by ring
      _ ≤ cs * Kz * X * (2 * (u * s ^ 2) + u * (Wd * w)) :=
          mul_le_mul_of_nonneg_left (by linarith [hsw, mul_nonneg hu.le (sq_nonneg s)]) (by positivity)
      _ ≤ cs * Kz * X * (4 * Z) := mul_le_mul_of_nonneg_left hu2 (by positivity)
  -- (ii) `Wd Mb μ γ`
  have hbb2 : b * b * (s * (s + Wd * w)) ≤ 2 * (u * s ^ 2) + u * (Wd * w) := by
    have e1 : b * b * (s * s) ≤ u * s ^ 2 := by
      calc b * b * (s * s) ≤ u * (s * s) := mul_le_mul_of_nonneg_right hbbu (mul_self_nonneg s)
        _ = u * s ^ 2 := by ring
    have e2 : b * b * (s * (Wd * w)) ≤ s * w := by
      calc b * b * (s * (Wd * w)) ≤ 1 * (s * (Wd * w)) :=
            mul_le_mul_of_nonneg_right hbb1 (mul_nonneg hs hWdw)
        _ = s * (Wd * w) := one_mul _
        _ ≤ s * w := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hw hWd1) hs
    linarith [e1, e2, hsw]
  have hT2 : Wd * Mb * (μ * (X * (s + Wd * w))) ≤ cs * Kz * cB * X ^ 2 * (4 * Z) := by
    have h1 : Wd * Mb * (μ * (X * (s + Wd * w))) ≤ (cs * Kz * s) * ((X * (cB * (b * b))) * (X * (s + Wd * w))) := by
      refine mul_le_mul hm1 (mul_le_mul_of_nonneg_right hμ (by positivity)) (by positivity) (by positivity)
    calc Wd * Mb * (μ * (X * (s + Wd * w))) ≤ _ := h1
      _ = cs * Kz * cB * X ^ 2 * (b * b * (s * (s + Wd * w))) := by ring
      _ ≤ cs * Kz * cB * X ^ 2 * (2 * (u * s ^ 2) + u * (Wd * w)) := mul_le_mul_of_nonneg_left hbb2 (by positivity)
      _ ≤ cs * Kz * cB * X ^ 2 * (4 * Z) := mul_le_mul_of_nonneg_left hu2 (by positivity)
  -- (iii) `Wd Mb² μ`
  have hT3 : Wd * Mb ^ 2 * μ ≤ cs * Kz ^ 2 * cB * X * (2 * Z) := by
    have h1 : Wd * Mb ^ 2 * μ ≤ (cs * Kz ^ 2 * s ^ 2) * (X * (cB * (b * b))) :=
      mul_le_mul hm2 hμ hμ0 (by positivity)
    calc Wd * Mb ^ 2 * μ ≤ _ := h1
      _ = cs * Kz ^ 2 * cB * X * (b * b * s ^ 2) := by ring
      _ ≤ cs * Kz ^ 2 * cB * X * (u * s ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbbu (sq_nonneg s)) (by positivity)
      _ ≤ cs * Kz ^ 2 * cB * X * (2 * Z) := mul_le_mul_of_nonneg_left hus (by positivity)
  -- assembly
  have hX2 : X ^ 2 * Z ≤ X ^ 3 * Z := mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg X]) hZ0'
  have hX1 : X * Z ≤ X ^ 2 * Z := mul_le_mul_of_nonneg_right (by nlinarith) hZ0'
  have hXc : X ^ 2 * Z ≥ 0 := by positivity
  have hPle : P ≤ (6 + 16 * cB + 2 * (4 + 8 * cB) * cs) * X ^ 3 * Z := by
    have : P ≤ (6 + 16 * cB + 2 * (4 + 8 * cB) * cs) * X ^ 2 * X * Z := hI
    calc P ≤ _ := this
      _ = _ := by ring
  have hid : X * (s + Wd * w) * (X * (u * s + w) + 2 * μ * 2 * (X * (s + Wd * w))) +
      Wd * ((X * (s + Wd * w) + Mb) * (X * (u * s + w) + 2 * μ * 2 * (X * (s + Wd * w) + Mb))) =
      P * (1 + Wd) + (Wd * Mb * (X * (u * s + w)) + 8 * (Wd * Mb * (μ * (X * (s + Wd * w)))) + 4 * (Wd * Mb ^ 2 * μ)) := by
    rw [hPdef]; ring
  rw [hid]
  have hPW : P * (1 + Wd) ≤ 2 * P := by linarith [mul_nonneg hP0 (sub_nonneg.2 hWd1)]
  have hK2 : Wd * Mb * (X * (u * s + w)) + 8 * (Wd * Mb * (μ * (X * (s + Wd * w)))) + 4 * (Wd * Mb ^ 2 * μ) ≤
      cs * Kz * (4 + 32 * cB + 8 * Kz * cB) * (X ^ 3 * Z) := by
    have a1 : cs * Kz * X * (4 * Z) ≤ cs * Kz * 4 * (X ^ 3 * Z) := by
      have : cs * Kz * 4 * (X * Z) ≤ cs * Kz * 4 * (X ^ 3 * Z) :=
        mul_le_mul_of_nonneg_left (hX1.trans hX2) (by positivity)
      calc _ = cs * Kz * 4 * (X * Z) := by ring
        _ ≤ _ := this
    have a2 : cs * Kz * cB * X ^ 2 * (4 * Z) ≤ cs * Kz * cB * 4 * (X ^ 3 * Z) := by
      have : cs * Kz * cB * 4 * (X ^ 2 * Z) ≤ cs * Kz * cB * 4 * (X ^ 3 * Z) :=
        mul_le_mul_of_nonneg_left hX2 (by positivity)
      calc _ = cs * Kz * cB * 4 * (X ^ 2 * Z) := by ring
        _ ≤ _ := this
    have a3 : cs * Kz ^ 2 * cB * X * (2 * Z) ≤ cs * Kz ^ 2 * cB * 2 * (X ^ 3 * Z) := by
      have : cs * Kz ^ 2 * cB * 2 * (X * Z) ≤ cs * Kz ^ 2 * cB * 2 * (X ^ 3 * Z) :=
        mul_le_mul_of_nonneg_left (hX1.trans hX2) (by positivity)
      calc _ = cs * Kz ^ 2 * cB * 2 * (X * Z) := by ring
        _ ≤ _ := this
    linarith [hT1, hT2, hT3, a1, a2, a3]
  linarith [hPle, hPW, hK2]




/-- `(1/2) √r ≤ (c/2) r + 1/(8c)` (the square `(2c√r - 1)²`). -/
private theorem BATermHoldsB_sqrt_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    (1 / 2) * Real.sqrt r ≤ c / 2 * r + 1 / (8 * c) := by
  have h8 : 0 < 8 * c := by positivity
  have e : c ^ 2 * Real.sqrt r ^ 2 = c ^ 2 * r := by rw [Real.sq_sqrt hr]
  have : (1 / 2) * Real.sqrt r - c / 2 * r ≤ 1 / (8 * c) := by
    rw [le_div_iff₀ h8]
    nlinarith [sq_nonneg (2 * c * Real.sqrt r - 1), e]
  linarith

/-- **The decay of `M` against the profile `𝖳`**: `𝖳_t(0) e^{-c r} ≤ E · 𝖳_t(r ∧ ℓ)` with `E` depending on `(d, c)` only (`ℓ_t ≥ 1`,
`d ≥ 3`): the polynomial factor `(r+1)^{(d-2)/2}` and the factor `e^{√(r/ℓ_t)/2}` of `𝖳_t(0)/𝖳_t(r ∧ ℓ)` are absorbed by `e^{-c r}`. -/
private theorem BATermHoldsB_sfMb {d : ℕ} (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c) :
    ∃ E : ℝ, 0 < E ∧ ∀ {L : ℕ} {W g t ℓ r : ℝ}, 1 ≤ ellT L g t → 0 ≤ r → 0 ≤ ℓ →
      sfT d L W g t 0 * Real.exp (-(c * r)) ≤ E * sfT d L W g t (min r ℓ) := by
  have hk : (0 : ℝ) < ((d - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 2)
  obtain ⟨E₀, hE₀, hpoly⟩ := BATermHolds_poly_exp (C₂ := ((d - 2 : ℕ) : ℝ)) (c := c / 2) hk (by positivity)
  refine ⟨2 ^ (d - 2) * E₀ * Real.exp (1 / (8 * c)), by positivity, ?_⟩
  intro L W g t ℓ r hℓt hr hℓ
  have hm0 : 0 ≤ min r ℓ := le_min hr hℓ
  have hmr : min r ℓ ≤ r := min_le_left _ _
  rw [sfT_zero]
  unfold sfT
  set m : ℝ := min r ℓ with hm
  set A : ℝ := √((W ^ d)⁻¹) * √((g ^ 2 + |1 - t|)⁻¹) with hA
  have hA0 : 0 ≤ A := by positivity
  set k : ℕ := d - 2 with hkdef
  set S : ℝ := Real.sqrt (((m + 1) ^ k)) with hS
  set T : ℝ := Real.exp ((1 / 2) * Real.sqrt (m / ellT L g t)) with hT
  have hm1 : 1 ≤ (m + 1) ^ k := one_le_pow₀ (by linarith)
  have hS0 : 0 < S := Real.sqrt_pos.2 (by linarith)
  have hq1 : √(((m + 1) ^ k)⁻¹) * S = 1 := by
    rw [hS, ← Real.sqrt_mul (inv_nonneg.2 (by linarith)), inv_mul_cancel₀ (by linarith)]
    exact Real.sqrt_one
  have hq2 : Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t)) * T = 1 := by
    rw [hT, ← Real.exp_add]; simp
  -- the bound `exp(-c r) S T ≤ E`
  have hSb : S ≤ (r + 1) ^ k := by
    have h1 : (m + 1) ^ k ≤ (r + 1) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
    have h2 : 1 ≤ (r + 1) ^ k := one_le_pow₀ (by linarith)
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [h1, h2]
  have hTb : T ≤ Real.exp ((1 / 2) * Real.sqrt r) := by
    refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
    exact (div_le_self hm0 hℓt).trans hmr
  have hpow : (r + 1) ^ k ≤ 2 ^ k * (max 1 r) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by rcases le_total 1 r with h | h <;> simp [h] <;> linarith) k
  have hp := hpoly r hr
  rw [Real.rpow_natCast] at hp
  have hST : Real.exp (-(c * r)) * (S * T) ≤ 2 ^ k * E₀ * Real.exp (1 / (8 * c)) := by
    have h1 : Real.exp (-(c * r)) * (S * T) ≤ Real.exp (-(c * r)) * ((r + 1) ^ k * Real.exp (c / 2 * r + 1 / (8 * c))) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul hSb (hTb.trans (Real.exp_le_exp.2 (BATermHoldsB_sqrt_le hc hr)))
        (Real.exp_pos _).le (by positivity)) (Real.exp_pos _).le
    have h2 : Real.exp (-(c * r)) * ((r + 1) ^ k * Real.exp (c / 2 * r + 1 / (8 * c))) =
        ((r + 1) ^ k * Real.exp (-(c / 2 * r))) * Real.exp (1 / (8 * c)) := by
      rw [show -(c * r) = -(c / 2 * r) + -(c / 2 * r) by ring, Real.exp_add, Real.exp_add]
      have : Real.exp (-(c / 2 * r)) * Real.exp (c / 2 * r) = 1 := by rw [← Real.exp_add]; simp
      calc _ = (r + 1) ^ k * Real.exp (-(c / 2 * r)) * (Real.exp (-(c / 2 * r)) * Real.exp (c / 2 * r)) * Real.exp (1 / (8 * c)) := by ring
        _ = _ := by rw [this]; ring
    have h3 : (r + 1) ^ k * Real.exp (-(c / 2 * r)) ≤ 2 ^ k * E₀ := by
      calc (r + 1) ^ k * Real.exp (-(c / 2 * r)) ≤ (2 ^ k * (max 1 r) ^ k) * Real.exp (-(c / 2 * r)) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ = 2 ^ k * ((max 1 r) ^ k * Real.exp (-(c / 2 * r))) := by ring
        _ ≤ 2 ^ k * E₀ := mul_le_mul_of_nonneg_left hp (by positivity)
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ 2 ^ k * E₀ * Real.exp (1 / (8 * c)) := mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  -- conclusion
  have hqq : 0 ≤ √(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t)) := by positivity
  have hkey : Real.exp (-(c * r)) ≤ 2 ^ k * E₀ * Real.exp (1 / (8 * c)) *
      (√(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t))) := by
    calc Real.exp (-(c * r)) = (Real.exp (-(c * r)) * (S * T)) *
          (√(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t))) := by
          have : S * T * (√(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t))) = 1 := by
            calc _ = (√(((m + 1) ^ k)⁻¹) * S) * (Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t)) * T) := by ring
              _ = 1 := by rw [hq1, hq2, one_mul]
          calc Real.exp (-(c * r)) = Real.exp (-(c * r)) * (S * T * (√(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t)))) := by rw [this, mul_one]
            _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hST hqq
  calc A * Real.exp (-(c * r)) ≤ A * (2 ^ k * E₀ * Real.exp (1 / (8 * c)) *
        (√(((m + 1) ^ k)⁻¹) * Real.exp (-(1 / 2) * Real.sqrt (m / ellT L g t)))) :=
        mul_le_mul_of_nonneg_left hkey hA0
    _ = _ := by ring


/-! ## 6. The `T` side: the `M`-part, the window, the radius and the events -/

/-- The support and the decay of `M` at the BA carrier, without the standing hypotheses of `BAMomentGen_decay`
(`BATermHolds_Mpart`, `Graph/BATermHolds.lean:556`, takes `LWAssmgL` unfolded; here it is not available): constants `C' ≥ 2`, `c > 0`
(of `(d, 𝔡, κ)`) such that eventually `M_{xy} = 0` unless the offsets of `x`, `y` agree and `‖M_{xy}‖ ≤ C' e^{-c |[x]-[y]|}`. -/
private theorem BATermHoldsB_Mpart {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ}
    (hd : 3 ≤ d) (hκ : 0 < κ) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
    (ht1 : ∀ n, t n ≤ BAflowT0 sz z n) : ∃ C' c : ℝ, 2 ≤ C' ∧ 0 < c ∧ ∀ᶠ n in atTop,
    (∀ x y : Idx d (sz.L n) (sz.W n), (split d (sz.L n) (sz.W n) x).2 ≠ (split d (sz.L n) (sz.W n) y).2 →
      (baFMz sz z).M n x y = 0) ∧
    ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).M n x y‖ ≤
      C' * Real.exp (-(c * ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ))) := by
  obtain ⟨C, c, Kd, hC1, hc, hKd, h⟩ := BAMomentGen_consts d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  refine ⟨max C 2, c, le_max_right _ _, hc, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  obtain ⟨ht1', hr, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
  obtain ⟨-, -, hMP, hoff, -⟩ := h (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
    (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hn.1 hn.2 hr (ht0 n) ht1' (BAMomentGen_D sz z n (t n) (fun _ => 0))
    rfl rfl rfl rfl
  refine ⟨fun x y h => (hoff x y h).1, fun x y => ?_⟩
  refine (hMP x y).1.trans ?_
  have hle : ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) ≤ (lwBdist d (sz.L n) (sz.W n) x y : ℝ) := by
    exact_mod_cast zdistInf_le_zdistD d (sz.L n) (STblk sz n x - STblk sz n y)
  refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (le_trans (by norm_num) (le_max_right _ _))
  have := mul_le_mul_of_nonneg_left hle hc.le
  linarith

/-- **The window** `ε₁ = min (min ε₀ (d c₀/4)) (d/2)`: `ε₁ ≤ ε₀`, `ε₁ ≤ d/2` and `Bctl ≤ W^{-2ε₁}` eventually (`Bctl ≤ 2 N^{-c₀}` from
`BAExp14d_Bctl_small`, in the place of the band's `lwN_Bctl_le`); the same computation as in `baLWtermExpN_holds`
(`Graph/BATermHolds.lean:758`). -/
private theorem BATermHoldsB_eps {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ : ℝ}
    (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
    (ht1 : ∀ n, t n ≤ BAflowT0 sz z n) (hε₀ : 0 < ε₀) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ ε₀ ∧ ε₁ ≤ (d : ℝ) / 2 ∧
      ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
  have hadm := hflow.1
  obtain ⟨c₀, hc₀, hBs⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (min ε₀ ((d : ℝ) * c₀ / 4)) ((d : ℝ) / 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min (lt_min hε₀ (by positivity)) (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₁c : ε₁ ≤ (d : ℝ) / 2 := by rw [hε₁def]; exact min_le_right _ _
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c₀ / 2 := by
    have : ε₁ ≤ (d : ℝ) * c₀ / 4 := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  refine ⟨ε₁, hε₁pos, hε₁a, hε₁c, ?_⟩
  filter_upwards [hBs t ht0 ht1, (BATermHolds_W_tendsto hadm).eventually
    ((tendsto_rpow_atTop (by positivity : 0 < (d : ℝ) * c₀ / 2)).eventually_ge_atTop 2)] with n hn hW2
  have h1 : sz.Bctl n (t n) ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) :=
    hn.trans (mul_le_mul_of_nonneg_left (Sizes.lwN_size_rpow_neg_le sz n hc₀.le) zero_le_two)
  set a : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos (hWpos n) _
  have haa : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀)) = a * a := by
    rw [ha, ← Real.rpow_add (hWpos n)]; congr 1; ring
  have ha2 : 2 * a ≤ 1 := by
    have : a * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c₀ / 2) = 1 := by
      rw [ha, ← Real.rpow_add (hWpos n)]; simp
    nlinarith
  have h3 : a ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
    Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
  calc sz.Bctl n (t n) ≤ 2 * (a * a) := by rw [← haa]; exact h1
    _ ≤ 1 * a := by nlinarith
    _ ≤ _ := by rw [one_mul]; exact h3

/-- The radius of the variables `ζ` on the `T` side: `ρ_n = log N_n · √(log N_n)` (`R = 0`).  It satisfies `K log W ≤ ρ_n` eventually for every
`K` (the hypothesis of `baGbyZeta_holds`) and `√ρ_n ≤ τ log N_n` eventually for every `τ > 0` (that of `baZetaExpClaim_holds`). -/
private def BATermHoldsB_ρ {d : ℕ} (sz : Sizes d) (n : ℕ) : ℝ :=
  Real.log ((sz.size n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz.size n : ℕ) : ℝ))

private theorem BATermHoldsB_ρ_nonneg {d : ℕ} (sz : Sizes d) (n : ℕ) : 0 ≤ BATermHoldsB_ρ sz n :=
  mul_nonneg (Real.log_nonneg (Nat.one_le_cast.2 (sz.one_le_size n))) (Real.sqrt_nonneg _)

private theorem BATermHoldsB_ρ_sep {d : ℕ} (hd : 1 ≤ d) (sz : Sizes d) (hsz : sz.SizeTendsto) (K : ℝ) :
    ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ BATermHoldsB_ρ sz n - 2 * (fun _ : ℕ => (0 : ℝ)) n := by
  have hY : Tendsto (fun n => Real.log ((sz.size n : ℕ) : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hsz
  filter_upwards [hY.eventually_ge_atTop (K ^ 2)] with n h1
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hWN : sz.W n ≤ sz.size n :=
    (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)).trans (Nat.le_self_pow (by omega) _)
  have hWN' : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hWN
  have hlogW0 : 0 ≤ Real.log ((sz.W n : ℕ) : ℝ) := Real.log_nonneg hW1
  have hlogW : Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.size n : ℕ) : ℝ) := Real.log_le_log (by linarith) hWN'
  simp only [BATermHoldsB_ρ, mul_zero, sub_zero]
  calc K * Real.log ((sz.W n : ℕ) : ℝ) ≤ |K| * Real.log ((sz.W n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) hlogW0
    _ ≤ Real.sqrt (Real.log ((sz.size n : ℕ) : ℝ)) * Real.log ((sz.size n : ℕ) : ℝ) :=
        mul_le_mul (Real.abs_le_sqrt h1) hlogW hlogW0 (Real.sqrt_nonneg _)
    _ = _ := mul_comm _ _

private theorem BATermHoldsB_ρ_rad {d : ℕ} (sz : Sizes d) (hsz : sz.SizeTendsto) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, Real.sqrt (BATermHoldsB_ρ sz n) ≤ τ * Real.log ((sz.size n : ℕ) : ℝ) := by
  have hY : Tendsto (fun n => Real.log ((sz.size n : ℕ) : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp hsz
  filter_upwards [hY.eventually_ge_atTop ((1 / τ ^ 2) ^ 2), hY.eventually_ge_atTop 0] with n h1 h2
  set Y : ℝ := Real.log ((sz.size n : ℕ) : ℝ) with hYdef
  set s : ℝ := Real.sqrt Y with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = Y := Real.sq_sqrt h2
  have hs1 : 1 / τ ^ 2 ≤ s := by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at this
  have h3 : 1 ≤ τ ^ 2 * s := by
    have := mul_le_mul_of_nonneg_left hs1 (sq_nonneg τ)
    rwa [mul_one_div_cancel (by positivity)] at this
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  unfold BATermHoldsB_ρ
  calc Y * s = s ^ 2 * s := by rw [hs2]
    _ ≤ s ^ 2 * s * (τ ^ 2 * s) := le_mul_of_one_le_right (by positivity) h3
    _ = (τ * s ^ 2) ^ 2 := by ring
    _ = (τ * Y) ^ 2 := by rw [hs2]



section TSide

variable {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔡 𝔠 : ℝ} {t : ℕ → ℝ} {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ}
  (hd : 3 ≤ d) (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (ht0 : ∀ n, 0 ≤ t n)
  (ht1 : ∀ n, t n ≤ BAflowT0 sz z n) (hA : LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ)
include hd hκ hε h𝔡 hflow ht0 ht1 hA

/-- **`(eq:directG2)` at BA** (`7_8:24-30`; twin of `LWTermHolds_Gij_T`, `Graph/LWTermHolds.lean:1047`): on the sizes with `λ²/L² < 1 - t`,
`‖(G_t - M)_{xy}‖ ≺ 𝖳_t(|[x]-[y]| ∧ ℓ) + W^{-D_z}` for all `x, y`: `baGbyZeta_holds` (`R = 0`, `ρ_n = log N √(log N)`) bounds the entry by
the edge variable `ζ([x],[y])`, and `baZetaExpClaim_holds` (conjunct 2, stated at `𝖳_t(|α-β| ∧ ℓ) + W^{-D}` directly, so the shift lemma of the band is not read) bounds `ζ`. -/
private theorem BATermHoldsB_GM_T {Dz : ℝ} (hDz : 0 < Dz) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n q ω => ‖(baFMz sz z).GM n (t n) ω q.1.1 q.1.2‖)
      (fun n q _ => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) + ((sz.W n : ℕ) : ℝ) ^ (-Dz)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hε₀ := hA.1
  have hent := hA.2.2.1.1
  set D₁ : ℝ := max (2 * Dz) (1 / 𝔠) with hD₁
  have h1 := baGbyZeta_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ hε₀ hent (BATermHoldsB_ρ sz) (fun _ => 0) D₁
    (fun _ => le_rfl) (fun K => BATermHoldsB_ρ_sep (by omega) sz hsz K)
  have h2 := (baZetaExpClaim_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₀ Ψ ℓ hA ε₀ hε₀ hent Dz hDz (BATermHoldsB_ρ sz)
    (BATermHoldsB_ρ_nonneg sz) (fun τ hτ => BATermHoldsB_ρ_rad sz hsz hτ) D₁ le_rfl).2.1
  have p1 := StochDomAt.precomp_param h1
    (fun n (v : {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) =>
      (⟨((v.1.1, v.1.2), (STblk sz n v.1.1, STblk sz n v.1.2)), by simp [STblk], by simp [STblk]⟩ :
        BAGbyZetaU sz (fun _ => (0 : ℝ)) n))
  have p2 := StochDomAt.precomp_param h2
    (fun n (v : {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}) =>
      (⟨(STblk sz n v.1.1, STblk sz n v.1.2), v.2⟩ :
        {_p : Zd d (sz.L n) × Zd d (sz.L n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n}))
  exact StochDomAt.trans (Sizes.tendsto_size sz hsz) p1 p2

/-- **`(GavLGEX)` at `Ψ_t = max(W^{-d/2}, Bctl^{1/2})`** (`7_8:62-66`, `(eq:recolterm2)`; twin of `LWTermHolds_avg_T`, `Graph/LWTermHolds.lean:1182`):
`max_a |𝓛^{(1)}_{+,a} - m| ≤ N^{τ₁} Ψ_t²` w.h.p.  `(initialGT2)` is `hA.2.2.1` (from `ε₀` down to `ε₁ ≤ ε₀`), the loop bound `max 𝓛^{(2)} ≺ Ψ_t²` is
`(LW_assm_exp)` at `D = 1` (`wT(r) ≤ wT(0)`), the window is `Bctl ≤ W^{-2ε₁}` (`BATermHoldsB_eps`); the pin is `baGbEXPav_holds`. -/
private theorem BATermHoldsB_avg {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ a : Zd d (sz.L n),
      ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a) ω - (baFMz sz z).m n‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ τ₁ *
          (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2}) := by
  have hadm := hflow.1
  have hsize := Sizes.tendsto_size sz hadm.2.2.1
  have hε₀ := hA.1
  have hinit := hA.2.2.1
  have hℓ0 := hA.2.2.2.1
  have hloopE := hA.2.2.2.2.2
  obtain ⟨ε₁, hε₁0, hε₁a, hε₁c, hup⟩ := BATermHoldsB_eps hd hκ hε h𝔡 hflow ht0 ht1 hε₀
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hwin := LWWindow_max_Bctl sz hε₁c t hup
  have hent' : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁)) := by
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  have hmax : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun _ => Unit)
      (fun n _ ω => STmaxLoop2g (baFMz sz z) n (t n) ω)
      (fun n _ _ => (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2) := by
    apply BAMomentGen_prec_of_whp sz
    intro τ hτ
    refine ⟨_, BAMomentGen_whp_of_prec sz (hloopE 1 one_pos) hτ, ?_⟩
    refine Eventually.of_forall fun n => ?_
    intro ω hω u
    unfold STmaxLoop2g
    refine Finset.sup'_le _ _ fun q _ => ?_
    refine (hω (false, q.1, q.2)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have hr0 : (0 : ℝ) ≤ ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ) ≤
        tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 :=
      tailW_antitone (hℓ0 n) le_rfl hr0
    have hWd : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤
        (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2 := by
      have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hWpos n).le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring,
          Real.rpow_neg (hWpos n).le, Real.rpow_natCast]
      rw [← e]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (hWpos n).le _) (le_max_left _ _) 2
    have hB : sz.Bctl n (t n) ≤
        (max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) (Real.sqrt (sz.Bctl n (t n)))) ^ 2 := by
      have hB0 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
      calc sz.Bctl n (t n) = Real.sqrt (sz.Bctl n (t n)) ^ 2 := (Real.sq_sqrt hB0).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2
    have hT0 : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 =
        max (Bparam d (sz.L n) (sz.lam n) (t n) 0) (((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
      unfold tailW; rw [min_eq_left (hℓ0 n), tailT_zero]
    have hWn : ((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (hW1 n) (by norm_num)
    have hWd0 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by have := hWpos n; positivity
    calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1
          ((zdistInf d (sz.L n) (q.1 - q.2) : ℕ) : ℝ)
        ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) 1 0 :=
          mul_le_mul_of_nonneg_left h1 hWd0
      _ = max ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) 0)
            ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
          rw [hT0]; exact mul_max_of_nonneg _ _ hWd0
      _ ≤ _ := max_le hB (by
          calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * 1 := mul_le_mul_of_nonneg_left hWn hWd0
            _ ≤ _ := by rw [mul_one]; exact hWd)
  have hGav := baGbEXPav_holds d (by omega) κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 ht1 ε₁ hε₁0
  exact BAMomentGen_whp_of_prec sz (hGav _ (hwin.mono fun n hn => hn.1) (hwin.mono fun n hn => hn.2) ⟨hent', hmax⟩) hτ₁

/-- **The Markov step for `lem:LW_moment_exp` at BA** (`7_8:86-91`; twin of `LWTermHolds_fT`, `Graph/LWTermHolds.lean:1487`): `f_{xy} ≺ η_t⁻¹ B^{1/2} 𝖳_t(|a-b|∧ℓ) + W^{-D}` on the sizes
with `λ²/L² < 1 - t`, from `baLWMomentExp_closed` at the moment `p = 2 p₀`, `D' = p D` (`a^p + (W^{-D})^p ≤ (a + W^{-D})^p`) and the integrability of `|f_{xy}|^p`
(`BAMomentExp_integrable`, `LWfgD_univ`). -/
private theorem BATermHoldsB_fT {D : ℝ} (hD : 0 < D) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n q ω => ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖)
      (fun n q _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
          (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := by
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  refine LWTermHolds_prec_of_moments (sz.withLam 0) hsz
    (V := fun n => {_q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) // sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
    (fun n q ω => ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖)
    (fun n q => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
      sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n)) +
      ((sz.W n : ℕ) : ℝ) ^ (-D)) (C := 2) ?_ (fun n q ω => norm_nonneg _) (fun p n q => ?_) ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    refine (Nat.cast_le.2 (Fintype.card_subtype_le _)).trans ?_
    rw [Fintype.card_prod, Sizes.card_Idx, Real.rpow_two]
    push_cast; ring_nf; exact le_rfl
  · have h2 : Integrable (fun ω => ‖LWfg (baFMz sz z) n (t n) ω q.1.1 q.1.2‖ ^ p) (BAExp14a_μ sz) := by
      simpa only [LWfgD_univ] using BAMomentExp_integrable hκ hflow n (ht0 n) (ht1 n) p Finset.univ q.1.1 q.1.2
    exact h2
  · refine Eventually.of_forall fun n q => ?_
    have h1 : 0 < ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_pos_of_pos (Nat.cast_pos.2 (sz.W_pos n)) _
    have h2 : 0 < ((baFMz sz z).eta n (t n))⁻¹ := inv_pos.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n))
    have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
    have h4 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
      (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))
    positivity
  · intro τ₀ hτ₀ D' hD'
    set p₀ : ℕ := ⌈(D' + 2) / τ₀⌉₊ + 1 with hp₀
    have hp2 : 2 ∣ 2 * p₀ := dvd_mul_right _ _
    have hpD : 0 < ((2 * p₀ : ℕ) : ℝ) * D := mul_pos (by positivity) hD
    have hH := baLWMomentExp_closed d hd κ ε 𝔡 hκ hε h𝔡 (2 * p₀) hp2 𝔠 sz z hflow t ht0 ht1 _ Ψ ℓ hA _ hpD
    refine ⟨2 * p₀, by omega, ?_, 1, one_pos, ?_⟩
    · have h1 : (D' + 2) / τ₀ ≤ (⌈(D' + 2) / τ₀⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : D' + 2 ≤ τ₀ * (⌈(D' + 2) / τ₀⌉₊ : ℝ) := by
        have := mul_le_mul_of_nonneg_left h1 hτ₀.le
        rwa [mul_div_cancel₀ _ hτ₀.ne'] at this
      have hp : ((2 * p₀ : ℕ) : ℝ) = 2 * ((⌈(D' + 2) / τ₀⌉₊ : ℝ) + 1) := by rw [hp₀]; push_cast; ring
      rw [hp]
      nlinarith [h2, hτ₀]
    · have h1 := (BAExp14a_det_iff (P := BAExp14a_μ sz) (Sizes.tendsto_size sz hsz) _ _).1 hH 1 one_pos
      filter_upwards [h1] with n hn q
      refine (hn q).trans ?_
      rw [Real.rpow_one]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
      have hw : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hW0.le _
      have h2 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := (inv_pos.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n))).le
      have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
      have h4 := sfT_nonneg (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n)
        (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))
      have e : ((sz.W n : ℕ) : ℝ) ^ (-(((2 * p₀ : ℕ) : ℝ) * D)) = (((sz.W n : ℕ) : ℝ) ^ (-D)) ^ (2 * p₀) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; ring
      rw [e, one_mul]
      exact pow_add_pow_le (by positivity) hw (by omega)

/-- **The `T`-side reduction** for `D ≥ 2d + 1` (`7_8:20-58`, `(eq:recolterm2)`, `(eq:recoltermwt2)`; twin of `LWTermHolds_reduceT_core`, `Graph/LWTermHolds.lean:1270`), on the sizes
with `λ²/L² < 1 - t`: from `f_{xy} ≺ η_t⁻¹ B^{1/2} 𝖳_t(|a-b|∧ℓ) + W^{-D}` (`BATermHoldsB_fT`), `(eq:directG2)` (`BATermHoldsB_GM_T` at `D_z = d + D`), the diagonal
`‖G_{xx}‖ ≤ 2` (the entry law of `(initialGT2)` and `‖M‖ ≤ 1`) and `(GavLGEX)` (`BATermHoldsB_avg`), with the `M`-part of the closing edge in `BATermHolds_LWE_le`
(support of `M` on equal offsets, decay `C' e^{-c r}`, `BATermHoldsB_Mpart`) absorbed by `BATermHoldsB_sfMb` in `BATermHoldsB_arithT`.  The restriction `D ≥ 2d + 1` is where
the cross term `W^{-D} 𝖳` is absorbed (paper-delta candidate `T2375c` of the band). -/
private theorem BATermHoldsB_core {D : ℝ} (hD : 2 * (d : ℝ) + 1 ≤ D) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
        sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
      (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
      (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) := by
  have hadm := hflow.1
  have hsz : sz.SizeTendsto := hadm.2.2.1
  have hsize := Sizes.tendsto_size sz hsz
  have h𝔠 : 0 < 𝔠 := hadm.1
  have hband := hadm.2.2.2.1
  have hD0 : 0 < D := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  have hε₀ := hA.1
  have hinit := hA.2.2.1
  have hℓ0 := hA.2.2.2.1
  obtain ⟨C', c, hC'2, hc, hMpart⟩ := BATermHoldsB_Mpart hd hκ h𝔡 hflow ht0 ht1
  obtain ⟨E, hE, hsfMb⟩ := BATermHoldsB_sfMb hd hc
  obtain ⟨ε₁, hε₁0, -, -, hBup⟩ := BATermHoldsB_eps hd hκ hε h𝔡 hflow ht0 ht1 hε₀
  refine BAMomentGen_prec_of_whp sz fun τ hτ => ?_
  have hτ₁ : 0 < τ / 6 := by positivity
  set τ₂ : ℝ := min (τ / 6) (𝔠 * ε₀ / 2) with hτ₂def
  have hτ₂ : 0 < τ₂ := lt_min hτ₁ (by positivity)
  have E1 := BAMomentGen_whp_of_prec sz (BATermHoldsB_fT hd hκ hε h𝔡 hflow ht0 ht1 hA hD0) hτ₁
  have E2 := BAMomentGen_whp_of_prec sz
    (BATermHoldsB_GM_T hd hκ hε h𝔡 hflow ht0 ht1 hA (Dz := (d : ℝ) + D) (by positivity)) hτ₁
  have E3 := BAMomentGen_whp_of_prec sz hinit.1 hτ₂
  have E4 := BATermHoldsB_avg hd hκ hε h𝔡 hflow ht0 ht1 hA hτ₁
  refine ⟨_, HighProbAt.inter hsize (HighProbAt.inter hsize (HighProbAt.inter hsize E1 E2) E3) E4, ?_⟩
  set Λ : ℝ := 𝔡⁻¹ with hΛ
  set Kz : ℝ := C' * E with hKz
  set K0 : ℝ := 4 * (6 + 16 * (1 + Λ ^ 2) + 2 * (4 + 8 * (1 + Λ ^ 2)) * (1 + Λ ^ 2)) +
    2 * ((1 + Λ ^ 2) * Kz * (4 + 32 * (1 + Λ ^ 2) + 8 * Kz * (1 + Λ ^ 2))) with hK0
  have hK : ∀ᶠ n in atTop, K0 ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 6) :=
    ((tendsto_rpow_atTop hτ₁).comp hsz).eventually_ge_atTop _
  have hWbig : ∀ᶠ n in atTop, 1 + Λ ^ 2 ≤ ((sz.W n : ℕ) : ℝ) :=
    (BATermHolds_W_tendsto hadm).eventually_ge_atTop _
  filter_upwards [hadm.2.2.2.2, hband, hBup, hK, hWbig, hsize.eventually (eventually_ge_atTop 1), hMpart]
    with n hWO hb hBn hKn hWn hN1 hMp
  intro ω hω u
  obtain ⟨⟨⟨hf, hgm⟩, hent⟩, havg⟩ := hω
  obtain ⟨⟨σ, a⟩, hP⟩ := u
  have hX1' : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast hN1
  set X : ℝ := ((sz.size n : ℕ) : ℝ) ^ (τ / 6) with hXdef
  have hX1 : 1 ≤ X := Real.one_le_rpow hX1' hτ₁.le
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := Nat.cast_pos.2 (sz.W_pos n)
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  have hg0 : 0 ≤ sz.lam n := (Real.rpow_pos_of_pos hW0 _).le.trans hWO.1
  have hg : sz.lam n ≤ Λ := hWO.2
  have hℓn := hℓ0 n
  have hℓt : 1 ≤ ellT (sz.L n) (sz.lam n) (t n) := one_le_ellT hL1
  have hη0 : 0 < (baFMz sz z).eta n (t n) := BAExp14a_eta_pos hκ hflow n (ht0 n) (ht1 n)
  have hη1 : (baFMz sz z).eta n (t n) ≤ 1 := BAExp14c_eta_le_one hκ hflow n (ht0 n) (ht1 n)
  have htlt : t n < 1 := (ba_G_data hκ sz hflow n (ht0 n) (ht1 n)).1
  have hI : 1 ≤ ((baFMz sz z).eta n (t n))⁻¹ := one_le_inv_iff₀.2 ⟨hη0, hη1⟩
  -- `B_{t,0}` and `Bctl`
  have hAge := LWTermHolds_A_ge hg hg0 (ht0 n) htlt
  have hBpar : (sz.lam n ^ 2 + |1 - t n|)⁻¹ ≤ Bparam d (sz.L n) (sz.lam n) (t n) 0 := by
    unfold Bparam; simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
    have : 0 ≤ (((sz.L n : ℕ) : ℝ) ^ d * |1 - t n|)⁻¹ := by positivity
    linarith
  set Wd : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hWd
  have hWd0 : 0 < Wd := by positivity
  have hWd1 : Wd ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
  have hBctl : sz.Bctl n (t n) = Wd * Bparam d (sz.L n) (sz.lam n) (t n) 0 := rfl
  have hBlow : Wd ≤ (1 + Λ ^ 2) * sz.Bctl n (t n) := by
    have h1 : Wd * (1 + Λ ^ 2)⁻¹ ≤ sz.Bctl n (t n) := by
      rw [hBctl]; exact mul_le_mul_of_nonneg_left (hAge.trans hBpar) hWd0.le
    have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + Λ ^ 2)
    rwa [show (1 + Λ ^ 2) * (Wd * (1 + Λ ^ 2)⁻¹) = Wd by field_simp] at this
  have hB0 : 0 < sz.Bctl n (t n) := by
    have : 0 < Wd * (1 + Λ ^ 2)⁻¹ := by positivity
    rw [hBctl]; exact lt_of_lt_of_le this (mul_le_mul_of_nonneg_left (hAge.trans hBpar) hWd0.le)
  have hB1 : sz.Bctl n (t n) ≤ 1 :=
    hBn.trans (Real.rpow_le_one_of_one_le_of_nonpos hW1 (by linarith))
  set b : ℝ := Real.sqrt (sz.Bctl n (t n)) with hbdef
  have hb0 : 0 < b := Real.sqrt_pos.2 hB0
  have hbb : b * b = sz.Bctl n (t n) := Real.mul_self_sqrt hB0.le
  have hb1 : b ≤ 1 := by rw [hbdef, Real.sqrt_le_one]; exact hB1
  set u : ℝ := ((baFMz sz z).eta n (t n))⁻¹ * b with hudef
  have hu0 : 0 < u := by positivity
  have hbu : b ≤ u := le_mul_of_one_le_left hb0.le hI
  have e12 : (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) = b := by rw [hbdef, Real.sqrt_eq_rpow]
  -- the sizes of `w = W^{-D}` and `w₂ = W^{-(d+D)} = W^{-d} w`
  have hWdr : ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) = Wd := by rw [hWd, Real.rpow_neg hW0.le, Real.rpow_natCast]
  set w : ℝ := ((sz.W n : ℕ) : ℝ) ^ (-D) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos hW0 _
  have hw₂ : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + D)) = Wd * w := by
    rw [show -((d : ℝ) + D) = -(d : ℝ) + -D by ring, Real.rpow_add hW0, hWdr]
  have hwW : (1 + Λ ^ 2) * w ≤ Wd ^ 2 := by
    have h1 : w ≤ ((sz.W n : ℕ) : ℝ) ^ (-(2 * (d : ℝ) + 1)) := Real.rpow_le_rpow_of_exponent_le hW1 (by linarith)
    have h2 : ((sz.W n : ℕ) : ℝ) ^ (-(2 * (d : ℝ) + 1)) = Wd ^ 2 * (((sz.W n : ℕ) : ℝ))⁻¹ := by
      rw [show -(2 * (d : ℝ) + 1) = -(d : ℝ) + -(d : ℝ) + -1 by ring, Real.rpow_add hW0, Real.rpow_add hW0, hWdr,
        Real.rpow_neg_one]
      ring
    have h3 : (1 + Λ ^ 2) * (((sz.W n : ℕ) : ℝ))⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hW0]; exact hWn
    calc (1 + Λ ^ 2) * w ≤ (1 + Λ ^ 2) * (Wd ^ 2 * (((sz.W n : ℕ) : ℝ))⁻¹) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
      _ = Wd ^ 2 * ((1 + Λ ^ 2) * (((sz.W n : ℕ) : ℝ))⁻¹) := by ring
      _ ≤ Wd ^ 2 * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = _ := mul_one _
  have hwb : w ≤ b := by
    have h1 : w ≤ Wd / (1 + Λ ^ 2) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      calc (1 + Λ ^ 2) * w ≤ Wd ^ 2 := hwW
        _ = Wd * Wd := sq Wd
        _ ≤ Wd * 1 := mul_le_mul_of_nonneg_left hWd1 hWd0.le
        _ = Wd := mul_one _
    have h2 : Wd / (1 + Λ ^ 2) ≤ sz.Bctl n (t n) := by
      rw [div_le_iff₀ (by positivity), mul_comm]; exact hBlow
    exact (h1.trans h2).trans (by rw [← hbb]; exact mul_le_of_le_one_right hb0.le hb1)
  have hwu : w ≤ u ^ 2 * Wd := by
    have h1 : Wd ^ 2 / (1 + Λ ^ 2) ≥ w := by rw [ge_iff_le, le_div_iff₀ (by positivity), mul_comm]; exact hwW
    have h2 : Wd / (1 + Λ ^ 2) ≤ u ^ 2 := by
      calc Wd / (1 + Λ ^ 2) ≤ sz.Bctl n (t n) := by
            rw [div_le_iff₀ (by positivity), mul_comm]; exact hBlow
        _ = b * b := hbb.symm
        _ ≤ u * u := mul_le_mul hbu hbu hb0.le hu0.le
        _ = u ^ 2 := (sq u).symm
    calc w ≤ Wd ^ 2 / (1 + Λ ^ 2) := h1
      _ = (Wd / (1 + Λ ^ 2)) * Wd := by ring
      _ ≤ u ^ 2 * Wd := mul_le_mul_of_nonneg_right h2 hWd0.le
  have hwu' : w ≤ u := hwb.trans hbu
  -- the profile `𝖳` and the target `Z`
  set sf : ℕ → ℝ := fun r => sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) (min (r : ℝ) (ℓ n)) with hsf
  have hsf0 : ∀ r, 0 ≤ sf r := fun r => sfT_nonneg _
  have hsf1 : ∀ r, sf r ≤ 1 := fun r => by
    have h1 := LWTermHolds_sfT_sq_le (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hW0 (le_min (Nat.cast_nonneg r) hℓn)
    have h2 : Wd * (sz.lam n ^ 2 + |1 - t n|)⁻¹ ≤ sz.Bctl n (t n) := by
      rw [hBctl]; exact mul_le_mul_of_nonneg_left hBpar hWd0.le
    exact (pow_le_one_iff_of_nonneg (hsf0 r) two_ne_zero).1 (h1.trans (h2.trans hB1))
  set s0 : ℝ := sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n) 0 with hs0def
  have hs0sf : sf 0 = s0 := by simp [hsf, hs0def, min_eq_left hℓn]
  have hs00 : 0 ≤ s0 := sfT_nonneg _
  have hs01 : s0 ≤ 1 := hs0sf ▸ hsf1 0
  have hs0sq : Wd ≤ (1 + Λ ^ 2) * s0 ^ 2 := by
    have h1 := LWTermHolds_sfT_zero_sq (d := d) (L := sz.L n) (g := sz.lam n) (t := t n) hW0
    have h3 : Wd * (1 + Λ ^ 2)⁻¹ ≤ s0 ^ 2 := by
      rw [hs0def, h1]; exact mul_le_mul_of_nonneg_left hAge hWd0.le
    have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 1 + Λ ^ 2)
    rwa [show (1 + Λ ^ 2) * (Wd * (1 + Λ ^ 2)⁻¹) = Wd by field_simp] at this
  set Z : ℕ → ℝ := fun r => u * (Wd * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (r : ℝ)) with hZdef
  have hZ : ∀ r : ℕ, (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) → u * (sf r ^ 2 + Wd * w) ≤ 2 * Z r := fun r hrL => by
    have hc := (LWTermHolds_tail_cmp (d := d) (L := sz.L n) (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) (ℓ := ℓ n)
      (D := D) (by omega) hL1 htlt hW0 hP.le hℓn (Nat.cast_nonneg r) hrL).1
    have := mul_le_mul_of_nonneg_left hc hu0.le
    simp only [hZdef, hsf]
    linarith [this]
  -- the entry bounds
  have hGA : ∀ v, ‖(baFMz sz z).G n (t n) ω v v‖ ≤ 2 := by
    intro v
    have h1 : ‖(baFMz sz z).GM n (t n) ω v v‖ ≤ 1 := by
      refine (hent (v, v)).trans ?_
      have h2 := Sizes.size_rpow_le_W_rpow sz h𝔠 n hb (τ := τ₂) hτ₂.le
      have h3 : τ₂ / 𝔠 ≤ ε₀ := by
        rw [div_le_iff₀ h𝔠]
        have : τ₂ ≤ 𝔠 * ε₀ / 2 := min_le_right _ _
        linarith [mul_pos h𝔠 hε₀]
      calc ((sz.size n : ℕ) : ℝ) ^ τ₂ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) ≤
            ((sz.W n : ℕ) : ℝ) ^ (τ₂ / 𝔠) * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hW0.le _)
        _ ≤ ((sz.W n : ℕ) : ℝ) ^ ε₀ * ((sz.W n : ℕ) : ℝ) ^ (-ε₀) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hW1 h3) (Real.rpow_nonneg hW0.le _)
        _ = 1 := by rw [← Real.rpow_add hW0]; simp
    have h3 : (baFMz sz z).G n (t n) ω v v = (baFMz sz z).GM n (t n) ω v v + (baFMz sz z).M n v v := by
      unfold FlowFM.GM; ring
    obtain ⟨-, -, -, -, -, hMle⟩ := ba_G_data hκ sz hflow n (ht0 n) (ht1 n)
    rw [h3]
    exact (norm_add_le _ _).trans (by have := hMle v v; change ‖(baFMz sz z).M n v v‖ ≤ 1 at this; linarith)
  have hγ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖(baFMz sz z).GM n (t n) ω x y‖ ≤
      (fun r : ℕ => X * (sf r + Wd * w)) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) := fun x y => by
    have h : ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ X * (sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
        (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) + D))) := hgm ⟨(x, y), hP⟩
    rw [hw₂] at h
    exact h
  have hφ : ∀ x y : Idx d (sz.L n) (sz.W n), ‖LWfg (baFMz sz z) n (t n) ω x y‖ ≤
      (fun r : ℕ => X * (u * sf r + w)) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) := fun x y => by
    have h : ‖LWfg (baFMz sz z) n (t n) ω x y‖ ≤ X * (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
        sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
          (min ((zdistInf d (sz.L n) (STblk sz n x - STblk sz n y) : ℕ) : ℝ) (ℓ n)) +
        ((sz.W n : ℕ) : ℝ) ^ (-D)) := hf ⟨(x, y), hP⟩
    rw [e12] at h
    exact h
  set Ψt : ℝ := max (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) b with hΨt
  have hΨsq : Ψt ^ 2 ≤ (1 + Λ ^ 2) * (b * b) := by
    have e : (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 = Wd := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le, show -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(d : ℝ) by push_cast; ring, hWdr]
    rw [hbb]
    rcases le_total (((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2)) b with h | h
    · rw [hΨt, max_eq_right h, ← hbb]
      have : 0 ≤ b * b := mul_nonneg hb0.le hb0.le
      calc b ^ 2 = 1 * (b * b) := by ring
        _ ≤ (1 + Λ ^ 2) * (b * b) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg Λ)) this
    · rw [hΨt, max_eq_left h, e]
      exact hBlow
  have hμ : ∀ a' : Zd d (sz.L n), ‖(baFMz sz z).L n (t n) (fun _ : Fin 1 => true) (fun _ => a') ω - (baFMz sz z).m n‖ ≤
      X * Ψt ^ 2 := havg
  -- the `M`-part
  obtain ⟨hM0, hM⟩ := hMp
  set Mb : ℕ → ℝ := fun r => C' * Real.exp (-(c * (r : ℝ))) with hMbdef
  have hC'0 : 0 ≤ C' := by linarith
  have hMb0 : ∀ r, 0 ≤ Mb r := fun r => by have := Real.exp_pos (-(c * (r : ℝ))); positivity
  have hAM : (2 : ℝ) ≤ Mb 0 := by simpa [hMbdef] using hC'2
  have hKz0 : 0 ≤ Kz := by rw [hKz]; positivity
  -- the pathwise bound
  have hSelf := (BAflow_real κ ε 𝔠 𝔡 sz z hflow n).1
  have hLWE := BATermHolds_LWE_le n (t n) ω hSelf σ a (A := 2) (μ := X * Ψt ^ 2)
    (γ := fun r : ℕ => X * (sf r + Wd * w)) (φ := fun r : ℕ => X * (u * sf r + w)) (Mb := Mb)
    (by positivity) (by norm_num) (fun r => by have := hsf0 r; positivity) (fun r => by have := hsf0 r; positivity)
    hMb0 hAM hμ hGA hγ hM0 hM hφ
  set r : ℕ := zdistInf d (sz.L n) (a 0 - a 1) with hr
  have hrL : (r : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast BATermHolds_zdistInf_le (sz.L n) (a 0 - a 1)
  have hZr := hZ r hrL
  have hZ0 := hZ 0 (by simp)
  have hZ0' : u * s0 ^ 2 ≤ 2 * Z 0 := by
    have h := hZ0
    rw [hs0sf] at h
    linarith [mul_nonneg hu0.le (mul_nonneg hWd0.le hw0.le)]
  have hZnn : 0 ≤ Z r := by
    have := mul_nonneg hu0.le (add_nonneg (sq_nonneg (sf r)) (mul_nonneg hWd0.le hw0.le)); linarith
  have hμb : X * Ψt ^ 2 ≤ X * ((1 + Λ ^ 2) * (b * b)) := mul_le_mul_of_nonneg_left hΨsq (by linarith)
  have hMs : s0 * Mb r ≤ Kz * sf r := by
    have h := hsfMb (W := ((sz.W n : ℕ) : ℝ)) (g := sz.lam n) (t := t n) hℓt (Nat.cast_nonneg r) hℓn
    calc s0 * Mb r = C' * (s0 * Real.exp (-(c * (r : ℝ)))) := by simp only [hMbdef]; ring
      _ ≤ C' * (E * sf r) := mul_le_mul_of_nonneg_left h hC'0
      _ = Kz * sf r := by rw [hKz]; ring
  have hbd := BATermHoldsB_arithT (X := X) (u := u) (b := b) (s := sf r) (s0 := s0) (w := w) (Wd := Wd)
    (μ := X * Ψt ^ 2) (Mb := Mb r) (Z := Z r) (Z0 := Z 0) (cB := 1 + Λ ^ 2) (cs := 1 + Λ ^ 2) (Kz := Kz)
    hX1 hu0 hb0.le hb1 hbu (hsf0 r) (hsf1 r) hs00 hs01 hw0.le hWd0.le hWd1 (by positivity) (by positivity)
    (by positivity) hKz0 hμb hwu hwu' hs0sq hZr hZ0' (hMb0 r) hMs
  have hN : ((sz.size n : ℕ) : ℝ) ^ τ = X ^ 6 := by
    rw [hXdef, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; push_cast; ring
  have e13 : ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
      (Wd * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (r : ℝ)) = Z r := by
    rw [e12]
  change ‖LWEg (baFMz sz z) n (t n) σ a ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((baFMz sz z).eta n (t n))⁻¹ *
    (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * (Wd * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (r : ℝ)))
  rw [e13, hN]
  have hX4 : X * X ^ 3 ≤ X ^ 6 := by
    have : X ^ 4 ≤ X ^ 6 := pow_le_pow_right₀ hX1 (by norm_num)
    calc X * X ^ 3 = X ^ 4 := by ring
      _ ≤ _ := this
  calc ‖LWEg (baFMz sz z) n (t n) σ a ω‖ ≤ _ := hLWE
    _ ≤ K0 * X ^ 3 * Z r := hbd
    _ ≤ X * X ^ 3 * Z r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKn (by positivity)) hZnn
    _ ≤ X ^ 6 * Z r := mul_le_mul_of_nonneg_right hX4 hZnn

end TSide

/-! ## 7. The regime `1 - t > λ²/L²` of `lem: EWGn2_N`, the union, and BA Step 2 closed -/

/-- **`lem: EWGn2_N` on the sizes where `1 - t > λ²/L²`** (`7_8:20-58`; `LWtermExpS`, `Graph/LWPins.lean:447`) at the block Anderson data: the conclusion of
`BALWtermExp` (`BA/LWPinsBA.lean:47`) on the index set of the regime (the other regime is `BALWtermExpN`, `Graph/BATermHolds.lean:715`).  The statement def of
target 4; the union is `baLWtermExp_holds`. -/
def BALWtermExpS (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
        ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExpgL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t ε₀ Ψ ℓ →
          ∀ D : ℝ, 0 < D →
            PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) //
                sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n})
              (fun n p ω => ‖LWEg (baFMz sz z) n (t n) p.1.1 p.1.2 ω‖)
              (fun n p _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
                ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * tailW d (sz.L n) (sz.lam n) (t n) (ℓ n)
                  ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ)))

/-- **`lem: EWGn2_N`, regime `1 - t > λ²/L²`, for every `D > 0`** (`7_8:20-58`; twin of `lwtermExpS_holds` through `LWTermHolds_concT`,
`Graph/LWTermHolds.lean:1551`): the reduction `BATermHoldsB_core` at `D' = max (D, 2d + 1)` (its premise is `BATermHoldsB_fT` at `D'`), then `wT_{D'} ≤ wT_D`
(`D' ≥ D`).  For `D ≥ 2d + 1` this is the reduction at `D`; for `D < 2d + 1` the premise at `D` is too weak (the cross term `W^{-D} 𝖳` needs `D ≥ 2d + 1`,
paper-delta candidate `T2375c` of the band). -/
theorem baLWtermExpS_holds : ∀ d : ℕ, BALWtermExpS d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  have hsize := Sizes.tendsto_size sz hflow.1.2.2.1
  have hD'0 : 0 < max D (2 * (d : ℝ) + 1) := lt_max_of_lt_left hD
  have h1 := BATermHoldsB_core hd hκ hε h𝔡 hflow ht0 htT hA (D := max D (2 * (d : ℝ) + 1)) (le_max_right _ _)
  refine lwN_prec_mono hsize (c := 1) ?_ h1
  refine Eventually.of_forall fun n => ?_
  rintro ⟨⟨σ, a⟩, hP⟩ ω
  have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.one_le_cast.2 (sz.W_pos n)
  have h2 : 0 ≤ ((baFMz sz z).eta n (t n))⁻¹ := (inv_pos.2 (BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n))).le
  have h3 : 0 ≤ sz.Bctl n (t n) := by unfold Sizes.Bctl Bparam; positivity
  have h4 : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have h5 : 0 ≤ tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) :=
    (tailW_pos hW0 _).le
  have hle : tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) (max D (2 * (d : ℝ) + 1))
      ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) ≤
      tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D ((zdistInf d (sz.L n) (a 0 - a 1) : ℕ) : ℝ) := by
    unfold tailW
    exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le hW1 (by linarith [le_max_left D (2 * (d : ℝ) + 1)]))
  refine ⟨by positivity, ?_⟩
  rw [one_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle h4) (mul_nonneg h2 (Real.rpow_nonneg h3 _))

/-- **Target 5: `lem: EWGn2_N` at the block Anderson data** (`3_5:406-415`, `7_8:15-91`): the union of the two index sets, `1 - t > λ²/L²`
(`baLWtermExpS_holds`) and `1 - t ≤ λ²/L²` (`baLWtermExpN_holds`, `Graph/BATermHolds.lean:758`).  This is the merged pin `BALWtermExp = baPin LWtermExpG`
(`BA/LWPinsBA.lean:47`), unchanged; the registry line of `BALWtermExp` leaves. -/
theorem baLWtermExp_holds : ∀ d : ℕ, BALWtermExp d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  have hS := baLWtermExpS_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  have hN := baLWtermExpN_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  refine StochDomAt.of_subset_union (Sizes.tendsto_size sz hflow.1.2.2.1) hS hN fun τ hτ =>
    ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨u, hu⟩ := hω
  by_cases hP : sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n
  · exact Or.inl ⟨⟨u, hP⟩, hu⟩
  · exact Or.inr ⟨⟨u, not_lt.1 hP⟩, hu⟩

/-- **Target 6: BA Step 2 closed** (`3_5:345-609`, BA `7_8:1993-2099`): `baStep2_holds` (`BA/Step2CloseBA.lean:181`) at the two stage-L closures; `BAStep2 d` for every `d`
with no antecedent.  The carrier forms of `BALWterm`, `BALWtermExp` (`baPin LWtermG`, `baPin LWtermExpG`) are those of T2386, so the closed pins enter `STStep2G`
through `stLWBgL_of_LWtermG`, `stLWTgL_of_LWtermExpG` (`Chain/Step2EventsGen`). -/
theorem baStep2_closed : ∀ d : ℕ, BAStep2 d := fun d => baStep2_holds d (baLWterm_holds d) (baLWtermExp_holds d)

/-! ## 8. Compiled nonempty instances of targets 4, 5, 6 (`d = 3`)

Data (`BA/LWPinsBA.lean` §3, `Graph/BATermHolds.lean` §4): `sz0` (`n = 0`: `L = 4`, `W = 32`, `N = 2097152`, `λ = 1/64`), the flow `flow_sz0`
(`κ = 1/2`, `ε = 𝔡 = 1/10`, `𝔠 = 1/6`), `z = zSeq`, `t ≡ 1/2 ≤ BAflowT0` (`half_lt_t0`), `ε₀ = 1/10`, `Ψ_n = W_n^{-1/2}` (window `W^{-3/2} ≤ Ψ ≤ W^{-1/10}`), `ℓ_n = ℓ_t = ellT` (`≥ 1`, in the window
`ℓ ≤ (log W)^{10} ℓ_t`: not a collapsed window), `D = 5`.  What stays a hypothesis is another gate's input: `STInitialGT2gL` and `LWLoopExpgL` (inside `LWAssmExpgL`).  The index set of the regime `1 - t > λ²/L²` is
nonempty at every `n`; that of the regime `1 - t ≤ λ²/L²` is empty at the merged flow data for every `t ≤ BAflowT0` (the last example of this section), so the
union (target 5) is exercised through the first regime. -/

section Inst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst RBM.BA.MFixedPointInst

local notation "μ0" => Sizes.seqP (sz0.withLam 0)

open private Ψ0 Ψ0_window from RBM3D.BA.LWPinsBA
open private FlowPins_zS_add_mS_im FlowPins_wI_im from RBM3D.BA.FlowPins

/-- The range `ℓ_n = ℓ_t` of the instances of targets 4, 5 (`ℓ_t ≥ 1`). -/
private def BATermHoldsB_ℓ0 (n : ℕ) : ℝ := ellT (sz0.L n) (sz0.lam n) (1 / 2)

private theorem BATermHoldsB_ℓ0_ge (n : ℕ) : 1 ≤ BATermHoldsB_ℓ0 n :=
  one_le_ellT (by exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n))

/-- `ℓ_n ≤ (log W_n)^{10} ℓ_t`: `log W_n ≥ 1` since `W_n ≥ 32 > e`. -/
private theorem BATermHoldsB_ℓ0_le (n : ℕ) :
    BATermHoldsB_ℓ0 n ≤ (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (1 / 2) := by
  have hW : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    change (32 : ℝ) ≤ (((2 * (n + 1)) ^ 5 : ℕ) : ℝ)
    have h : 2 ^ 5 ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    exact_mod_cast h
  have hlog : 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  exact le_mul_of_one_le_left (zero_le_one.trans (BATermHoldsB_ℓ0_ge n)) (one_le_pow₀ hlog)

/-- `λ_n²/L_n² ≤ 2^{-12}` along `sz0` (`λ_n ≤ 1/64`, `L_n ≥ 1`). -/
private theorem BATermHoldsB_reg_small (n : ℕ) : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 / 4096 := by
  have hx : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hlam : sz0.lam n ≤ 1 / 64 := by
    change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1 / 64
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hx 6])
  have hlam0 : 0 ≤ sz0.lam n := by change 0 ≤ ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹; positivity
  have hL1 : (1 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz0.three_le_L n; omega : 1 ≤ sz0.L n)
  have h1 : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ sz0.lam n ^ 2 :=
    div_le_self (by positivity) (one_le_pow₀ hL1)
  have h2 : sz0.lam n ^ 2 ≤ (1 / 64) ^ 2 := pow_le_pow_left₀ hlam0 hlam 2
  nlinarith

/-- The horizon at the merged flow data is `BAflowT0 ≤ 25/36` (`BAt0 = Im m/(Im m + Im z)`, `Im z_n + Im m_n = 6/5`, `Im z_n ≥ 11/30`). -/
private theorem BATermHoldsB_t0_le (n : ℕ) : BAflowT0 sz0 zSeq n ≤ 25 / 36 := by
  unfold BAflowT0 BAt0
  rw [BAm_zSeq n]
  have h2 := FlowPins_zS_add_mS_im (sz0.L n) (sz0.lam n)
  have h3 : (zSeq n).im + (mS (sz0.L n) (sz0.lam n)).im = 6 / 5 := by
    unfold zSeq; rw [h2, FlowPins_wI_im]
  have h4 : (mS (sz0.L n) (sz0.lam n)).im + (zSeq n).im = 6 / 5 := by linarith
  have h5 := zSeq_im_ge n
  rw [h4, div_le_iff₀ (by norm_num)]
  linarith

/-- The index set of `BALWtermExpS 3` is nonempty at every size at the instance data (`λ_n²/L_n² ≤ 2^{-12} < 1/2`). -/
example : ∀ n, Nonempty {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
    sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - (1 / 2 : ℝ)} :=
  fun n => ⟨⟨(fun _ => true, fun _ => 0), by have := BATermHoldsB_reg_small n; linarith⟩⟩

/-- **The regime `1 - t ≤ λ²/L²` of `lem: EWGn2_N` is empty at the merged flow data for every admissible `t`** (`t ≤ BAflowT0 ≤ 25/36`, so
`1 - t ≥ 11/36 > 2^{-12} ≥ λ_n²/L_n²`): the instance of `baLWtermExpN_holds` (`Graph/BATermHolds.lean:758`) is n/a at `(sz0, zSeq)`, and target 5 is
exercised through the regime of target 4. -/
example : ∀ n, ∀ t : ℝ, t ≤ BAflowT0 sz0 zSeq n → sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - t := by
  intro n t ht
  have h1 := BATermHoldsB_t0_le n
  have h2 := BATermHoldsB_reg_small n
  linarith

/-- **Instance of target 4** (`baLWtermExpS_holds 3`): `𝓔^{Gc,(2)}_{t,σ,(a,b)} ≺ η_t⁻¹ (W^{-d} B_{t,0})^{1/2} W^{-d} 𝒯^ℓ_{t,D}(|a-b|)` on the regime `1 - t > λ²/L²` at the data
above, `D = 5 < 2d + 1` (the branch through `max (D, 2d + 1)`). -/
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BATermHoldsB_ℓ0) :
    PrecL sz0 μ0 (U := fun n => {_p : (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - (1 / 2 : ℝ)})
      (fun n p ω => ‖LWEg (baFMz sz0 zSeq) n (1 / 2 : ℝ) p.1.1 p.1.2 ω‖)
      (fun n p _ => ((baFMz sz0 zSeq).eta n (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (1 / 2 : ℝ) (BATermHoldsB_ℓ0 n) ((sz0.W n : ℕ) : ℝ) 5
          ((zdistInf 3 (sz0.L n) (p.1.2 0 - p.1.2 1) : ℕ) : ℝ))) :=
  baLWtermExpS_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) Ψ0 BATermHoldsB_ℓ0
    ⟨by norm_num, Ψ0_window, hI, fun n => zero_le_one.trans (BATermHoldsB_ℓ0_ge n), BATermHoldsB_ℓ0_le, hL⟩ 5 (by norm_num)

/-- **Instance of target 5** (`baLWtermExp_holds 3`, the merged pin `BALWtermExp 3`): the union of the two regimes at the data above and `D = 5`. -/
example (hI : STInitialGT2gL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) (1 / 10) Ψ0)
    (hL : LWLoopExpgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 2) BATermHoldsB_ℓ0) :
    PrecL sz0 μ0 (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖LWEg (baFMz sz0 zSeq) n (1 / 2 : ℝ) p.1 p.2 ω‖)
      (fun n p _ => ((baFMz sz0 zSeq).eta n (1 / 2 : ℝ))⁻¹ * (sz0.Bctl n (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
        ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 (sz0.L n) (sz0.lam n) (1 / 2 : ℝ) (BATermHoldsB_ℓ0 n) ((sz0.W n : ℕ) : ℝ) 5
          ((zdistInf 3 (sz0.L n) (p.2 0 - p.2 1) : ℕ) : ℝ))) :=
  baLWtermExp_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6) sz0 zSeq flow_sz0
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun n => (half_lt_t0 n).le) (1 / 10) Ψ0 BATermHoldsB_ℓ0
    ⟨by norm_num, Ψ0_window, hI, fun n => zero_le_one.trans (BATermHoldsB_ℓ0_ge n), BATermHoldsB_ℓ0_le, hL⟩ 5 (by norm_num)

/-- **Instance of target 6** (`baStep2_closed 3`), shape of `BA/Step2CloseBA.lean` §5 (instance of `baStep2_holds`) with `BALWterm 3`, `BALWtermExp 3` now discharged:
the constants `C_d, 𝔠_d` first, then the conclusion bundle at `s ≡ 1/10 < t ≡ 1/2` under the binders of `STStep2G`. -/
example : ∃ Cd : ℝ, 0 < Cd ∧ ∃ 𝔠d : ℝ, 0 < 𝔠d ∧ 𝔠d ≤ 1 / 100 ∧
    (STLKgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) → STDecaygL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) →
      STConStInd sz0 𝔠d (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1LoopgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
      STStep1WeakgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) →
        STStep2ConclgL (baFMz sz0 zSeq) μ0 (fun _ => 1 / 10) (fun _ => 1 / 2) Cd) := by
  obtain ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h⟩ := baStep2_closed 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num)
  exact ⟨Cd, hCd, 𝔠d, h𝔠d, h𝔠d1, h (1 / 6) sz0 zSeq flow_sz0 (fun _ => 1 / 10) (fun _ => 1 / 2) (fun _ => by norm_num)
    (fun n => by have := half_lt_t0 n; change (1 / 10 : ℝ) ≤ BAflowT0 sz0 zSeq n; linarith) (fun _ => by norm_num)
    (fun n => (half_lt_t0 n).le)⟩

end Inst

end RBM.BA

end
