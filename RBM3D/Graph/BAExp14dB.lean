/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14d
import RBM3D.Graph.BAAuxGraph2B

/-!
# BA-L L4c2 (T2466), part B: smallness of `B`, entry law, pathwise bound, `n_M = 1` leaf bound

Paper: arXiv:2507.20274, `paper/tex/B_graphical_lemmas.tex:66-110` (`(Gammamuxy)`, `B:84-90`),
`B:428-431` (`(eq:Gbyxi2_BA)`).  Twin of the band file `Graph/LWExpTerm3.lean` `:829-1227` and
`:1426-1661`; part A is `Graph/BAExp14d.lean`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAExp14d_`)

4. **The smallness of `Bctl` and the entry law** `BAExp14d_Bctl_small`, `BAExp14dEntry`,
   `baExp14dEntry_holds`.
5. **Arithmetic, pathwise bound, envelope, scalar facts, the pathwise `≺`** (private).
6. **The `n_M = 1` leaf bound** `BAG5LeafPrec1`, `baG5LeafPrec1_holds`: the `n_M = 1` half of the
   leaf pin `BAG5LeafPrec` of L4c1 (`T2464`); the `n_M = 0` half is `BAGraphPrecJoin` (L4g).
7. **Compiled instances** of targets 3-5 (`BAExp14d_pw`) and 4, 6 (namespace `BAExp14dInst`, as in part A).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open private BAExp14d_det BAExp14d_GM_le from RBM3D.Graph.BAExp14d
open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 4. The smallness of `Bctl` along the flow and the entry law -/

section EntryLaw

/-- `W^{-d} B_{u,0} ≤ (λ² W^d)⁻¹ + (N (1 - u))⁻¹` (the unfolding of `BAExp14a_Bctl_le_two`, `BAExp14aB:1103`). -/
private theorem BAExp14d_Bctl_le {d : ℕ} (sz : Sizes d) (n : ℕ) {u : ℝ} (hu : u < 1) (hg : 0 < sz.lam n) :
    sz.Bctl n u ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
  have hv : 0 < 1 - u := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by
    have : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    positivity
  have hg2 : 0 < sz.lam n ^ 2 := by positivity
  have hNe : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp only [Sizes.size]; push_cast; ring
  unfold Sizes.Bctl Bparam
  rw [abs_of_pos hv]
  have hT1 : (sz.lam n ^ 2 + (1 - u))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := by
    have ha : (sz.lam n ^ 2 + (1 - u))⁻¹ ≤ (sz.lam n ^ 2)⁻¹ := inv_anti₀ hg2 (by linarith)
    simpa only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one] using ha
  calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2 + (1 - u))⁻¹ *
        ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹)
      ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((sz.lam n ^ 2)⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - u))⁻¹) := by gcongr
    _ = (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + (((sz.size n : ℕ) : ℝ) * (1 - u))⁻¹ := by
        rw [hNe]; field_simp

/-- **Target 4, the smallness of `B`** (`T2466_Bctl_small`; the BA form of the `scaleFacts_R1` input of `lwExpTerm3_hent`, `LWExpTerm3:874`,
which has no BA twin on `main`): `W^{-d} B_{t,0} ≤ (λ² W^d)⁻¹ + (N (1 - t))⁻¹ ≤ W^{-2𝔡} + 2 N^{-ε} ≤ 2 N^{-c₀}`,
`c₀ = min (2 𝔠 𝔡, ε) / 2` (`lam_sq_mul_pow_ge`, `BAExp14a_one_sub_t`, `W ≥ N^𝔠`). -/
theorem BAExp14d_Bctl_small (d : ℕ) : 3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    BAFlow sz κ ε 𝔠 𝔡 z → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (-c₀) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hflow.1
  set c₀ : ℝ := min (2 * 𝔠 * 𝔡) ε / 2 with hc₀def
  have hc₀ : 0 < c₀ := by
    have : 0 < min (2 * 𝔠 * 𝔡) ε := lt_min (by positivity) hε
    positivity
  refine ⟨c₀, hc₀, fun t ht0 htT => ?_⟩
  have hN3 : ∀ᶠ n in atTop, (3 / 2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ c₀ :=
    ((tendsto_rpow_atTop hc₀).comp hsz).eventually (eventually_ge_atTop (3 / 2))
  filter_upwards [hbw, hWO, hN3, hsz.eventually (eventually_ge_atTop 1)] with n hb hwo hN32 hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hW0 _) hwo.1
  obtain ⟨ht1, -, -, hzi, -⟩ := ba_G_data hκ sz hflow n (ht0 n) (htT n)
  have hBle := BAExp14d_Bctl_le sz n ht1 hlam
  -- the first term
  have hT1 : (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ N ^ (-(2 * 𝔠 * 𝔡)) := by
    have h1 := sz.lam_sq_mul_pow_ge n hwo.1
    have h2 : N ^ (2 * 𝔠 * 𝔡) ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
      calc N ^ (2 * 𝔠 * 𝔡) = (N ^ 𝔠) ^ (2 * 𝔡) := by
            rw [← Real.rpow_mul hN0.le]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hN0.le _) hb (by positivity)
    rw [Real.rpow_neg hN0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hN0 _) (h2.trans h1)
  -- the second term
  have hT2 : (N * (1 - t n))⁻¹ ≤ 2 * N ^ (-ε) := by
    have h1 := BAExp14a_one_sub_t hκ hflow n (htT n)
    have h2 := (hflow.2 n).2.1
    have h3 : N ^ ε / 2 ≤ N * (1 - t n) := by
      calc N ^ ε / 2 = N * (N ^ (-1 + ε) / 2) := by
            rw [← mul_div_assoc, ← Real.rpow_one_add' hN0.le (by linarith)]; congr 2; ring
        _ ≤ N * ((z n).im / 2) := by gcongr
        _ ≤ N * (1 - t n) := by gcongr
    have hNε : 0 < N ^ ε := Real.rpow_pos_of_pos hN0 _
    calc (N * (1 - t n))⁻¹ ≤ (N ^ ε / 2)⁻¹ := inv_anti₀ (by positivity) h3
      _ = 2 * N ^ (-ε) := by rw [Real.rpow_neg hN0.le]; field_simp
  -- the sum
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hc2 : 2 * c₀ = min (2 * 𝔠 * 𝔡) ε := by rw [hc₀def]; ring
  have hm1 : N ^ (-(2 * 𝔠 * 𝔡)) ≤ N ^ (-(2 * c₀)) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
    rw [hc2]; linarith [min_le_left (2 * 𝔠 * 𝔡) ε]
  have hm2 : N ^ (-ε) ≤ N ^ (-(2 * c₀)) := by
    refine Real.rpow_le_rpow_of_exponent_le hN1' ?_
    rw [hc2]; linarith [min_le_right (2 * 𝔠 * 𝔡) ε]
  have hsq : N ^ (-(2 * c₀)) = N ^ (-c₀) * N ^ (-c₀) := by
    rw [← Real.rpow_add hN0]; congr 1; ring
  have hsmall : N ^ (-c₀) * 3 ≤ 2 := by
    rw [Real.rpow_neg hN0.le, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hN0 _)]; linarith
  have hp : 0 ≤ N ^ (-c₀) := Real.rpow_nonneg hN0.le _
  calc sz.Bctl n (t n) ≤ N ^ (-(2 * 𝔠 * 𝔡)) + 2 * N ^ (-ε) := hBle.trans (add_le_add hT1 hT2)
    _ ≤ 3 * N ^ (-(2 * c₀)) := by linarith
    _ = 3 * N ^ (-c₀) * N ^ (-c₀) := by rw [hsq]; ring
    _ ≤ 2 * N ^ (-c₀) := by nlinarith

/-- **Target 4, the entry law** (`T2466_entry`; twin of `lwExpTerm3_hent`, `LWExpTerm3:872`): `‖G_t - M‖_max ≺ W^{-ε₁}` (the premise of
`baGbyZeta_holds`) from `STLocalEntrygL` alone. -/
def BAExp14dEntry (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p ω => ‖(baFMz sz z).GM n (t n) ω p.1 p.2‖) (fun n _ _ => ((sz.W n : ℕ) : ℝ) ^ (-ε₁))

theorem baExp14dEntry_holds (d : ℕ) : BAExp14dEntry d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hLE
  obtain ⟨c₀, hc₀, hBsm⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hB := hBsm t ht0 htT
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hd0 : 0 < d := by omega
  refine ⟨(d : ℝ) * c₀ / 4, by positivity, ?_⟩
  refine StochDomAt.of_subset hLE fun τ hτ => ⟨τ, hτ, ?_⟩
  have hc2 : 0 < c₀ / 2 := by positivity
  filter_upwards [hB, ((tendsto_rpow_atTop hc2).comp hsz).eventually (eventually_ge_atTop (2 : ℝ))] with n hBn hN2
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN2' : (2 : ℝ) ≤ N ^ (c₀ / 2) := hN2
  have hu' : N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 4)) < ‖(baFMz sz z).GM n (t n) ω u.1 u.2‖ := hu
  have hWp : 0 < ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 4)) := Real.rpow_pos_of_pos hW0 _
  have hNτ : 0 < N ^ τ := Real.rpow_pos_of_pos hN0 _
  have hsq := pow_lt_pow_left₀ hu' (mul_nonneg hNτ.le hWp.le) two_ne_zero
  have hWN : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) * c₀ / 2) ≤ N ^ (c₀ / 2) := by
    have := sz.W_rpow_le hd0 n (τ := (d : ℝ) * c₀ / 2) (by positivity)
    have e : (d : ℝ) * c₀ / 2 / d = c₀ / 2 := by field_simp
    rwa [e] at this
  have hWinv : N ^ (-(c₀ / 2)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := by
    rw [Real.rpow_neg hN0.le, Real.rpow_neg hW0.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hW0 _) hWN
  have e2 : (((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 4))) ^ 2 = ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]; congr 1; push_cast; ring
  have e3 : (N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 4))) ^ 2 =
      N ^ τ * (N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2))) := by
    rw [mul_pow, e2]
    have : (N ^ τ) ^ 2 = N ^ τ * N ^ τ := sq _
    rw [this]; ring
  have hB2 : 2 * N ^ (-c₀) ≤ N ^ (-(c₀ / 2)) := by
    have : N ^ (-c₀) = N ^ (-(c₀ / 2)) * N ^ (-(c₀ / 2)) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have h2' : N ^ (-(c₀ / 2)) * 2 ≤ 1 := by
      have : N ^ (-(c₀ / 2)) = (N ^ (c₀ / 2))⁻¹ := Real.rpow_neg hN0.le _
      rw [this]
      have hp : 0 < N ^ (c₀ / 2) := Real.rpow_pos_of_pos hN0 _
      rw [inv_mul_le_iff₀ hp]; linarith
    have hp : 0 < N ^ (-(c₀ / 2)) := Real.rpow_pos_of_pos hN0 _
    nlinarith
  have hSTWB : STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) ≤ sz.Bctl n (t n) :=
    BAExp14a_STWB_le n (t n) _ (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  change N ^ τ * STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) <
    ‖(baFMz sz z).GM n (t n) ω u.1 u.2‖ ^ 2
  refine lt_of_le_of_lt ?_ hsq
  rw [e3]
  refine mul_le_mul_of_nonneg_left ?_ hNτ.le
  calc STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n u.1 - STblk sz n u.2)) ≤ sz.Bctl n (t n) := hSTWB
    _ ≤ 2 * N ^ (-c₀) := hBn
    _ ≤ N ^ (-(c₀ / 2)) := hB2
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := hWinv
    _ ≤ N ^ τ * ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := by
        have : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c₀ / 2)) := Real.rpow_nonneg hW0.le _
        have hN1τ : (1 : ℝ) ≤ N ^ τ := Real.one_le_rpow hN1 hτ.le
        nlinarith

end EntryLaw

/-! ## 5. Arithmetic (twin of `lwExpTerm3_Q_le`, `_size_le`, `_arith`, `LWExpTerm3:1058-1225`) -/

section Arith

/-- **The `q = 1` factor** `W^d cc² S2` with the three summands of `baZeta_ward_sum` (the third, the floor `L^d W^{-D₁}`, is the BA
addition) is `≤ 4 cc² (2ρ+1)^{2d} (1+Ψ) η⁻¹` (the band has the constant 3: no floor). -/
private theorem BAExp14d_Q_le (d W L : ℕ) (hW : 0 < W) {ρ cc Ψ η D₁ : ℝ} (hρ : 0 ≤ ρ) (hcc : 1 ≤ cc) (hΨ : 0 ≤ Ψ)
    (hη0 : 0 < η) (hη1 : η ≤ 1) (hfl : ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-D₁)) ≤ 1) :
    ((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
        (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)) + (L : ℝ) ^ d * (W : ℝ) ^ (-D₁))) ≤
      4 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by
  have hWd : (0 : ℝ) < (W : ℝ) ^ d := by
    have : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
    positivity
  have hM1 : 1 ≤ 2 * ρ + 1 := by linarith
  have hMd : (2 * ρ + 1) ^ d ≤ (2 * ρ + 1) ^ (2 * d) := pow_le_pow_right₀ hM1 (by omega)
  have hη' : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  have hcc2 : 1 ≤ cc ^ 2 := one_le_pow₀ hcc
  have hM2 : 1 ≤ (2 * ρ + 1) ^ (2 * d) := one_le_pow₀ hM1
  have h1Ψ : 1 ≤ 1 + Ψ := by linarith
  set X : ℝ := (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ with hX
  have hX1 : 1 ≤ X := by
    rw [hX]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ _ := by gcongr
  have hXd : (2 * ρ + 1) ^ d ≤ X := by
    rw [hX]
    calc (2 * ρ + 1) ^ d ≤ (2 * ρ + 1) ^ (2 * d) * 1 * 1 := by rw [mul_one, mul_one]; exact hMd
      _ ≤ _ := by gcongr
  have e : ((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
        (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)) + (L : ℝ) ^ d * (W : ℝ) ^ (-D₁))) =
      cc ^ 2 * (2 * X + (2 * ρ + 1) ^ d + ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-D₁))) := by
    rw [hX]; field_simp
  rw [e]
  calc cc ^ 2 * (2 * X + (2 * ρ + 1) ^ d + ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-D₁)))
      ≤ cc ^ 2 * (2 * X + X + X) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 4 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ := by rw [hX]; ring

/-- The size of a counter set before the polynomial bound: `size ≤ N^{n_M} Ψ^{n_S} N^{n_V}` (`L^d, W^d ≤ N`, `W ≥ 1`). -/
private theorem BAExp14d_size_le0 (c : Counters) (d L W : ℕ) (hW : 0 < W) {N Ψ : ℝ} (hΨ0 : 0 < Ψ)
    (hLN : (L : ℝ) ^ d ≤ N) (hWN : (W : ℝ) ^ d ≤ N) :
    c.scalingSize Ψ W d L ≤ N ^ c.nM * Ψ ^ c.nS * N ^ c.nV := by
  unfold Counters.scalingSize
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have h1 : ((L : ℝ) ^ d) ^ c.nM ≤ N ^ c.nM := pow_le_pow_left₀ (by positivity) hLN _
  have h3 : (W : ℝ) ^ (-(d : ℤ) * ((c.nW : ℤ) - (c.nV : ℤ))) ≤ N ^ c.nV := by
    have h4 : (W : ℝ) ^ (-(d : ℤ) * ((c.nW : ℤ) - (c.nV : ℤ))) ≤ (W : ℝ) ^ ((d : ℤ) * c.nV) :=
      zpow_le_zpow_right₀ hW1 (by nlinarith [(Nat.cast_nonneg c.nW : (0 : ℤ) ≤ c.nW), (Nat.cast_nonneg d : (0 : ℤ) ≤ d)])
    refine h4.trans ?_
    rw [_root_.zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hWN _
  have hpos3 : 0 ≤ (W : ℝ) ^ (-(d : ℤ) * ((c.nW : ℤ) - (c.nV : ℤ))) := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 (by positivity)) h3 hpos3
    (mul_nonneg ((pow_nonneg ((by positivity : (0 : ℝ) ≤ (L : ℝ) ^ d).trans hLN) _)) (by positivity))

/-- **The arithmetic of the pathwise bound** (`F ≤ N^τ η⁻¹ B^{ord/2} + N^{-D}`): twin of `lwExpTerm3_arith` with the prefactor 4 of
`BAExp14d_Q_le` and the floor `L^d W^{-D₁}` of the Ward sum. -/
private theorem BAExp14d_arith (c : Counters) (hnM : c.nM = 1) (d L W : ℕ) (hW : 0 < W)
    {N B η ρ r Ψ cc K₁ K₂ τ τ' D c₁ D₁ : ℝ}
    (hN : 1 ≤ N) (hB0 : 0 < B) (hB1 : B ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hΨ : Ψ = N ^ τ' * Real.sqrt B) (hcc : cc = N ^ τ') (hτ'0 : 0 < τ') (hτ'1 : τ' ≤ 1)
    (hτ' : τ' * ((|ord c| : ℤ) + 2 * d + 3) ≤ τ / 2)
    (hρ0 : 0 ≤ ρ) (hρN : ρ + 1 ≤ N ^ τ')
    (hK1 : 0 ≤ K₁) (hK1N : 8 * 4 ^ d * K₁ ≤ N ^ (τ / 2)) (hK2 : 0 ≤ K₂) (hK2N : K₂ ≤ N)
    (hexp : Real.exp (-(c₁ * r / 2)) ≤ N ^ (-(D + ((c.nM + c.nS + c.nV : ℕ) : ℝ) + 1)))
    (hLN : (L : ℝ) ^ d ≤ N) (hWN : (W : ℝ) ^ d ≤ N) (hfl : ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-D₁)) ≤ 1) :
    K₁ * (Ψ ^ ord c * (((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
          (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)) + (L : ℝ) ^ d * (W : ℝ) ^ (-D₁))))) +
      Real.exp (-(c₁ * r / 2)) * K₂ * c.scalingSize Ψ W d L ≤
    N ^ τ * (η⁻¹ * B ^ ((ord c : ℝ) / 2)) + N ^ (-D) := by
  have hN0 : 0 < N := by linarith
  have hNτ' : 1 ≤ N ^ τ' := Real.one_le_rpow hN hτ'0.le
  have hsB : Real.sqrt B ≤ 1 := Real.sqrt_le_one.2 hB1 |>.trans' le_rfl
  have hsB0 : 0 < Real.sqrt B := Real.sqrt_pos.2 hB0
  have hΨ0 : 0 < Ψ := by rw [hΨ]; positivity
  have hΨ1 : Ψ ≤ N ^ τ' := by
    rw [hΨ]; calc N ^ τ' * Real.sqrt B ≤ N ^ τ' * 1 := by gcongr
      _ = _ := mul_one _
  have hNτ'N : N ^ τ' ≤ N := by
    calc N ^ τ' ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hτ'1
      _ = N := Real.rpow_one N
  have hη' : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.2 hη1
  -- the second term
  have hF2 : Real.exp (-(c₁ * r / 2)) * K₂ * c.scalingSize Ψ W d L ≤ N ^ (-D) := by
    have hsz := BAExp14d_size_le0 c d L W hW hΨ0 hLN hWN
    have hsz0 : 0 ≤ c.scalingSize Ψ W d L := by unfold Counters.scalingSize; positivity
    have hΨN : Ψ ^ c.nS ≤ N ^ c.nS := pow_le_pow_left₀ hΨ0.le (hΨ1.trans hNτ'N) _
    set m : ℕ := c.nM + c.nS + c.nV with hm
    have e1 : N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m = N ^ (-D) := by
      rw [show N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m = N ^ (-(D + (m : ℝ) + 1)) * N ^ (1 : ℝ) * N ^ (m : ℝ) by
        rw [Real.rpow_one, Real.rpow_natCast], ← Real.rpow_add hN0, ← Real.rpow_add hN0]
      congr 1; ring
    have hsz' : c.scalingSize Ψ W d L ≤ N ^ m := by
      refine hsz.trans ?_
      rw [hm, pow_add, pow_add]
      calc N ^ c.nM * Ψ ^ c.nS * N ^ c.nV ≤ N ^ c.nM * N ^ c.nS * N ^ c.nV := by gcongr
        _ = _ := by ring
    calc Real.exp (-(c₁ * r / 2)) * K₂ * c.scalingSize Ψ W d L
        ≤ N ^ (-(D + (m : ℝ) + 1)) * N * N ^ m := by gcongr
      _ = N ^ (-D) := e1
  -- the first term
  set o : ℤ := ord c with ho
  have hQ := BAExp14d_Q_le d W L hW hρ0 (hcc ▸ hNτ') hΨ0.le hη0 hη1 hfl
  have hMbd : 2 * ρ + 1 ≤ 2 * N ^ τ' := by linarith
  have hΨ2 : 1 + Ψ ≤ 2 * N ^ τ' := by linarith
  have hM2 : (2 * ρ + 1) ^ (2 * d) ≤ (2 * N ^ τ') ^ (2 * d) := pow_le_pow_left₀ (by linarith) hMbd _
  have hQb : 4 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹ ≤
      8 * 4 ^ d * N ^ (τ' * (2 * d + 3)) * η⁻¹ := by
    have hccN : cc ^ 2 = N ^ (2 * τ') := by
      rw [hcc, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have hpow : (2 * N ^ τ') ^ (2 * d) = 4 ^ d * N ^ (τ' * (2 * d)) := by
      have h4 : (2 : ℝ) ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
      have h5 : (N ^ τ') ^ (2 * d) = N ^ (τ' * (2 * d)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; push_cast; ring_nf
      rw [mul_pow, h4, h5]
    have hN3 : N ^ (2 * τ') * N ^ (τ' * (2 * d)) * N ^ τ' = N ^ (τ' * (2 * d + 3)) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    calc 4 * cc ^ 2 * (2 * ρ + 1) ^ (2 * d) * (1 + Ψ) * η⁻¹
        ≤ 4 * N ^ (2 * τ') * (4 ^ d * N ^ (τ' * (2 * d))) * (2 * N ^ τ') * η⁻¹ := by
          rw [hccN, ← hpow]; gcongr
      _ = 8 * 4 ^ d * (N ^ (2 * τ') * N ^ (τ' * (2 * d)) * N ^ τ') * η⁻¹ := by ring
      _ = _ := by rw [hN3]
  have hΨo : Ψ ^ o = N ^ (τ' * (o : ℝ)) * B ^ ((o : ℝ) / 2) := by
    rw [hΨ]; exact lwExpTerm3_Psi_zpow hN0 hB0 o
  have hΨo0 : 0 ≤ Ψ ^ o := zpow_nonneg hΨ0.le o
  have hexp1 : N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3)) ≤ N ^ (τ / 2) := by
    have h1 : (o : ℝ) ≤ ((|o| : ℤ) : ℝ) := by exact_mod_cast le_abs_self o
    calc N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3)) = N ^ (τ' * (o : ℝ) + τ' * (2 * d + 3)) :=
          (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ (τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3)) :=
          Real.rpow_le_rpow_of_exponent_le hN (by nlinarith [hτ'0])
      _ ≤ N ^ (τ / 2) := Real.rpow_le_rpow_of_exponent_le hN hτ'
  have hF1 : K₁ * (Ψ ^ o * (((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
          (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)) + (L : ℝ) ^ d * (W : ℝ) ^ (-D₁))))) ≤
        N ^ τ * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
    have hBo : 0 ≤ B ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
    calc K₁ * (Ψ ^ o * (((W : ℝ) ^ d) * (cc ^ 2 * (2 * (2 * ρ + 1) ^ (2 * d) * ((((W : ℝ) ^ d) * η)⁻¹ * (1 + Ψ)) +
          (2 * ρ + 1) ^ d * ((((W : ℝ) ^ d)⁻¹)) + (L : ℝ) ^ d * (W : ℝ) ^ (-D₁)))))
        ≤ K₁ * (Ψ ^ o * (8 * 4 ^ d * N ^ (τ' * (2 * d + 3)) * η⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hQ.trans hQb) hΨo0) hK1
      _ = (8 * 4 ^ d * K₁) * (N ^ (τ' * (o : ℝ)) * N ^ (τ' * (2 * d + 3))) * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          rw [hΨo]; ring
      _ ≤ N ^ (τ / 2) * N ^ (τ / 2) * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          gcongr
      _ = N ^ τ * (η⁻¹ * B ^ ((o : ℝ) / 2)) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  exact add_le_add hF1 hF2

end Arith

/-! ## 5b. The pathwise bound of one packed value, the entry event, the random variable -/

section Pathwise

/-- A packed value at a labelling that factors through `ext` (the BA twin of `PGraph.val_of_factor`, `LWVocab:678`). -/
private theorem BAExp14d_val_of_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (P : BAPGraph (Fin 2)) (D : BALData ι)
    {ℓe : Fin 2 → ι} {ℓ' : P.E' → ι} (h : ℓe = ℓ' ∘ P.ext) : P.val D ℓe = P.g.val D ℓ' := by
  classical
  have hex : ∃ ℓ'' : P.E' → ι, ℓe = ℓ'' ∘ P.ext := ⟨ℓ', h⟩
  simp only [BAPGraph.val, hex, ↓reduceDIte]
  congr 1
  apply P.ext_surj.injective_comp_right
  exact hex.choose_spec.symm.trans h

/-- A packed value at a labelling that does not factor through `ext` is `0` (twin of `PGraph.val_of_not`). -/
private theorem BAExp14d_val_of_not {ι : Type*} [Fintype ι] [DecidableEq ι] (P : BAPGraph (Fin 2)) (D : BALData ι)
    {ℓe : Fin 2 → ι} (h : ¬ ∃ ℓ' : P.E' → ι, ℓe = ℓ' ∘ P.ext) : P.val D ℓe = 0 := by
  classical
  simp only [BAPGraph.val, h, ↓reduceDIte]

/-- **Pathwise bound of one packed value** (`(Gammamuxy)`, `B:84-90`; twin of `lwExpTerm3_pathwise`, `LWExpTerm3:954`) at any data `D`
that satisfies the bound of G3 (`hG3`, the conclusion of `BAGtoAGT` at `P.g`, `D`): `‖P_{ℓ}‖ ≤ C_Γ Ψ^{ord} W^d cc² S2 + (tail)` when
`‖G - M‖ ≤ Ψ` and `‖G - M‖ ≤ cc ξ₀` on the `R`-balls, with the row and column sums of `ξ₀²` bounded by `S2`. -/
private theorem BAExp14d_pw {d L W : ℕ} [NeZero L] [NeZero W] (P : BAPGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM = 1)
    (hatt : BAG5Attached P) (D : BALData (Idx d L W)) {Ψ cc S2 R r A K₀ K₁ Kd C c : ℝ} (ξ0 : Zd d L → Zd d L → ℝ)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hKd : 0 ≤ Kd) (hC : 0 ≤ C) (hc : 0 < c) (hA : 0 ≤ A) (hΨ : 0 < Ψ) (hcc : 0 ≤ cc)
    (hwin : ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2) (hr : 0 ≤ r) (hRr : (Fintype.card (P.E' ⊕ P.I') : ℝ) * r ≤ R)
    (h0 : ∀ a b, 0 ≤ ξ0 a b) (hG : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ)
    (hξ : ∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
      (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ cc * ξ0 a b)
    (hrow : ∀ a, ∑ v, ξ0 a v ^ 2 ≤ S2) (hcol : ∀ a, ∑ v, ξ0 v a ^ 2 ≤ S2)
    (hG3 : ∀ (Ψ A r R : ℝ) (ξ : Zd d L → Zd d L → ℝ), (∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ) → 0 ≤ A →
      ((W : ℝ) ^ d)⁻¹ ≤ A * Ψ ^ 2 → 0 ≤ r → (Fintype.card (P.E' ⊕ P.I') : ℝ) * r ≤ R → (∀ a b, 0 ≤ ξ a b) →
      (∀ (x y : Idx d L W) (a b : Zd d L), (zdistD d L ((split d L W x).1 - a) : ℝ) ≤ R →
        (zdistD d L ((split d L W y).1 - b) : ℝ) ≤ R → ‖D.G x y - D.M x y‖ ≤ ξ a b) →
      ∀ ℓe : P.E' → Idx d L W, ‖P.g.val D ℓe‖ ≤ P.g.sizeConst (K₀ * A) K₁ Kd * Ψ ^ (P.g.scalingOrder - P.g.auxOrd) *
          (((W : ℝ) ^ d) ^ P.g.nM * P.g.auxVal ξ (fun a => (split d L W (ℓe a)).1)) +
        Real.exp (-(c * r / 2)) * P.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
          P.g.scalingSize Ψ W d L)
    (ℓ : Fin 2 → Idx d L W) :
    ‖P.val D ℓ‖ ≤ P.g.sizeConst (K₀ * A) K₁ Kd * (Ψ ^ P.g.scalingOrder * (((W : ℝ) ^ d) * (cc ^ 2 * S2))) +
      Real.exp (-(c * r / 2)) * P.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) *
        P.g.scalingSize Ψ W d L := by
  classical
  have hK : 0 ≤ P.g.sizeConst (K₀ * A) K₁ Kd := by unfold BAGraph.sizeConst; positivity
  have hc2 : 0 < c / 2 := by positivity
  have hexp : 0 ≤ expC (d - 2) (c / 2) := by unfold expC; positivity
  have hK2 : 0 ≤ P.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) := by
    unfold BAGraph.sizeConst
    have : 0 ≤ C * (1 + expC (d - 2) (c / 2)) := mul_nonneg hC (by linarith)
    positivity
  have hsz : 0 ≤ P.g.scalingSize Ψ W d L := by
    unfold BAGraph.scalingSize Counters.scalingSize BAGraph.counters; positivity
  have hS2 : 0 ≤ S2 := (Finset.sum_nonneg fun v _ => sq_nonneg (ξ0 0 v)).trans (hrow 0)
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓ = ℓ' ∘ P.ext
  swap
  · rw [BAExp14d_val_of_not P D hf, norm_zero]
    have hq : 0 ≤ ((W : ℝ) ^ d) * (cc ^ 2 * S2) := by positivity
    have hz : 0 ≤ Ψ ^ P.g.scalingOrder := zpow_nonneg hΨ.le _
    positivity
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [BAExp14d_val_of_factor P D hℓ']
  have := BAExp14d_det P.g hN (le_of_eq hnM) hatt D ξ0 hK hΨ hcc h0 hG hξ hrow hcol ℓ'
    (hG3 Ψ A r R · hG hA hwin hr hRr · · ℓ')
  simpa only [hnM, ↓reduceIte] using this

end Pathwise

/-! ## 5c. The random variable, the entry event, the envelope -/

section Random

/-- The packed value at the rescaled data of the carrier at size `n`, the sample `ω`: `X = t^{-n_W} P_{xy}`. -/
private def BAExp14d_X {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (t : ℕ → ℝ) (P : BAPGraph (Fin 2)) (n : ℕ)
    (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ) : ℂ :=
  P.val (BAExp14d_dataT d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
    (BAExp14a_slc sz n ω)) ![v.1, v.2]

/-- **The entry event** `‖G_t - M‖_max ≤ N^{τ'} B^{1/2}` holds w.h.p. under `STLocalEntrygL` (twin of `lwExpTerm3_entry_whp`,
`LWExpTerm3:846`; `STWB ≤ B`). -/
private theorem BAExp14d_entry_whp {d : ℕ} {sz : Sizes d} {z : ℕ → ℂ} {t : ℕ → ℝ} (ht1 : ∀ n, t n < 1)
    (hLE : STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t) {τ' : ℝ} (hτ' : 0 < τ') :
    HighProbAt (Sizes.seqP (sz.withLam 0)) sz.size (fun n => {ω | ∀ x y : Idx d (sz.L n) (sz.W n),
      ‖(baFMz sz z).GM n (t n) ω x y‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))}) := by
  refine HighProbAt.mono (StochDomAt.highProb hLE (τ := 2 * τ') (by positivity))
    (Eventually.of_forall fun n ω hω x y => ?_)
  have h1 := hω (x, y)
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hB : STWB sz n (t n) (zdistInf d (sz.L n) (STblk sz n x - STblk sz n y)) ≤ sz.Bctl n (t n) :=
    BAExp14a_STWB_le n (t n) _ (ht1 n)
  have hpow : 0 < ((sz.size n : ℕ) : ℝ) ^ (2 * τ') := Real.rpow_pos_of_pos hN0 _
  have h2 : ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n) :=
    h1.trans (mul_le_mul_of_nonneg_left hB hpow.le)
  have hB0 : 0 ≤ sz.Bctl n (t n) := (STBctl_pos sz n (ht1 n)).le
  have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 * τ') = (((sz.size n : ℕ) : ℝ) ^ τ') ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have h3 : ‖(baFMz sz z).GM n (t n) ω x y‖ ^ 2 ≤
      (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB0, ← e1]; exact h2
  exact le_of_sq_le_sq h3 (mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.sqrt_nonneg _))

/-- **The envelope**: `‖X‖ ≤ N^{Kenv}` for all samples (G3 and `BAExp14d_pw` at `Ψ = N² + 1`, `ξ ≡ 1`, `cc = Ψ`, `r = R = 0`;
`‖G‖ ≤ η⁻¹ ≤ N²`, `‖M‖ ≤ 1`). -/
private theorem BAExp14d_env {d : ℕ} (hd : 3 ≤ d) {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (P : BAPGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM = 1) (hatt : BAG5Attached P) :
    ∃ Kenv : ℝ, ∀ᶠ n in atTop, ∀ (v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) (ω : sz.SeqΩ),
      ‖BAExp14d_X sz z t P n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
  obtain ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, hG3⟩ := baGtoAGT_holds d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  set K : ℝ := P.g.sizeConst (K₀ * 1) K₁ Kd with hKdef
  set K2 : ℝ := P.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) with hK2def
  have hK : 0 ≤ K := by rw [hKdef]; unfold BAGraph.sizeConst; positivity
  have hc2 : 0 < c / 2 := by positivity
  have hexp : 0 ≤ expC (d - 2) (c / 2) := by unfold expC; positivity
  have hK2 : 0 ≤ K2 := by
    rw [hK2def]; unfold BAGraph.sizeConst
    have : 0 ≤ C * (1 + expC (d - 2) (c / 2)) := mul_nonneg hC (by linarith)
    positivity
  set m₀ : ℕ := P.g.scalingOrder.natAbs with hm₀
  set e : ℕ := 3 * m₀ + 7 + P.g.nM + 3 * P.g.nS + P.g.nA with hedef
  refine ⟨(e : ℝ) + 1, ?_⟩
  filter_upwards [BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 htT, BAExp14a_eventually hκ hε hflow htT,
    hsz.eventually_ge_atTop (max (K + K2) 2)] with n hsc hev hNK
  obtain ⟨-, -, hη, -, ht1⟩ := hsc
  obtain ⟨-, -, hg, hgΛ⟩ := hev
  intro v ω
  have hLpos : 0 < sz.L n := by have := sz.three_le_L n; omega
  have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.L n) ^ d ≤ sz.size n := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
    exact_mod_cast h
  have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    have h : (sz.W n) ^ d ≤ sz.size n := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hLpos) d
    exact_mod_cast h
  have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
    simp only [Sizes.size]; push_cast; ring
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN2 : (2 : ℝ) ≤ N := (le_max_right _ _).trans hNK
  have hN0 : 0 < N := by linarith
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  set D := BAExp14d_dataT d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
    (BAExp14a_slc sz n ω) with hD
  set Ψ₀ : ℝ := N ^ 2 + 1 with hΨ₀
  have hΨ0 : 0 < Ψ₀ := by positivity
  have hΨ1 : 1 ≤ Ψ₀ := by nlinarith
  have hΨN : Ψ₀ ≤ N ^ 3 := by nlinarith [sq_nonneg N]
  have hG0 : ∀ x y, ‖D.G x y - D.M x y‖ ≤ Ψ₀ := fun x y =>
    (BAExp14d_GM_le hκ hflow n (ht0 n) (htT n) ω x y).trans (by linarith)
  have hwin : ((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ ≤ 1 * Ψ₀ ^ 2 := by
    have hW1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    have : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW1)
    nlinarith
  have hcard : ∀ a : Zd d (sz.L n), ∑ v : Zd d (sz.L n), (fun _ _ : Zd d (sz.L n) => (1 : ℝ)) a v ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := by
    intro a
    simp [Zd, ZMod.card]
  have hpw := BAExp14d_pw P hN hnM hatt D (A := 1) (Ψ := Ψ₀) (cc := Ψ₀) (S2 := ((sz.L n : ℕ) : ℝ) ^ d) (R := 0) (r := 0)
    (fun _ _ => (1 : ℝ)) hK₀.le hK₁.le hKd hC hc zero_le_one hΨ0 hΨ0.le hwin le_rfl (by simp)
    (fun _ _ => zero_le_one) hG0 (fun x y a b _ _ => by simpa using (hG0 x y)) hcard hcard
    (hG3 (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n) hg hgΛ hr
      (ht0 n) ht1 P.E' P.I' P.g hN D rfl rfl rfl rfl) ![v.1, v.2]
  change ‖P.val D ![v.1, v.2]‖ ≤ N ^ ((e : ℝ) + 1)
  refine hpw.trans ?_
  -- the polynomial bound
  have hz : Ψ₀ ^ P.g.scalingOrder ≤ Ψ₀ ^ m₀ := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ hΨ1 (by rw [hm₀]; exact Int.le_natAbs)
  have hp1 : K * (Ψ₀ ^ P.g.scalingOrder * (((sz.W n : ℕ) : ℝ) ^ d * (Ψ₀ ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d))) ≤
      K * N ^ (3 * m₀ + 7) := by
    have e1 : ((sz.W n : ℕ) : ℝ) ^ d * (Ψ₀ ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d) = Ψ₀ ^ 2 * N := by
      rw [← hWL]; ring
    rw [e1]
    have h3 : Ψ₀ ^ m₀ ≤ N ^ (3 * m₀) := by rw [pow_mul]; exact pow_le_pow_left₀ hΨ0.le hΨN _
    have h4 : Ψ₀ ^ 2 ≤ N ^ 6 := by
      calc Ψ₀ ^ 2 ≤ (N ^ 3) ^ 2 := pow_le_pow_left₀ hΨ0.le hΨN _
        _ = N ^ 6 := by ring
    calc K * (Ψ₀ ^ P.g.scalingOrder * (Ψ₀ ^ 2 * N)) ≤ K * (N ^ (3 * m₀) * (N ^ 6 * N)) := by
          gcongr
          exact hz.trans h3
      _ = K * N ^ (3 * m₀ + 7) := by ring
  have hp2 : Real.exp (-(c * 0 / 2)) * K2 * P.g.scalingSize Ψ₀ ((sz.W n : ℕ)) d (sz.L n) ≤
      K2 * N ^ (P.g.nM + 3 * P.g.nS + P.g.nA) := by
    have hsz0 := BAExp14d_size_le0 P.g.counters d (sz.L n) (sz.W n) (sz.W_pos n) hΨ0 hLN hWN
    have hΨs : Ψ₀ ^ P.g.counters.nS ≤ (N ^ 3) ^ P.g.counters.nS := pow_le_pow_left₀ hΨ0.le hΨN _
    have hs : P.g.scalingSize Ψ₀ (sz.W n) d (sz.L n) ≤ N ^ (P.g.nM + 3 * P.g.nS + P.g.nA) := by
      refine hsz0.trans ?_
      change N ^ P.g.nM * Ψ₀ ^ P.g.nS * N ^ P.g.nA ≤ _
      calc N ^ P.g.nM * Ψ₀ ^ P.g.nS * N ^ P.g.nA ≤ N ^ P.g.nM * (N ^ 3) ^ P.g.nS * N ^ P.g.nA := by gcongr
        _ = _ := by rw [← pow_mul, ← pow_add, ← pow_add]
    simp only [mul_zero, zero_div, neg_zero, Real.exp_zero, one_mul]
    exact mul_le_mul_of_nonneg_left hs hK2
  have hNe : (K + K2) * N ^ e ≤ N ^ ((e : ℝ) + 1) := by
    rw [Real.rpow_add hN0, Real.rpow_one, Real.rpow_natCast, mul_comm (N ^ e) N]
    exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hNK) (pow_nonneg hN0.le e)
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have ha1 : N ^ (3 * m₀ + 7) ≤ N ^ e := pow_le_pow_right₀ hN1 (by rw [hedef]; omega)
  have ha2 : N ^ (P.g.nM + 3 * P.g.nS + P.g.nA) ≤ N ^ e := pow_le_pow_right₀ hN1 (by rw [hedef]; omega)
  calc K * (Ψ₀ ^ P.g.scalingOrder * (((sz.W n : ℕ) : ℝ) ^ d * (Ψ₀ ^ 2 * ((sz.L n : ℕ) : ℝ) ^ d))) +
        Real.exp (-(c * 0 / 2)) * K2 * P.g.scalingSize Ψ₀ ((sz.W n : ℕ)) d (sz.L n)
      ≤ K * N ^ e + K2 * N ^ e := add_le_add (hp1.trans (mul_le_mul_of_nonneg_left ha1 hK))
        (hp2.trans (mul_le_mul_of_nonneg_left ha2 hK2))
    _ = (K + K2) * N ^ e := by ring
    _ ≤ _ := hNe

end Random

/-! ## 5d. Scalar facts along the flow: the floor, the radii, the tail -/

section Scalars

/-- `B ≤ 1` eventually (from `BAExp14d_Bctl_small`; there is no BA twin of `st5_Bctl_le_one`, `BAExp14aB:1102`). -/
private theorem BAExp14d_B_le_one {d : ℕ} (hd : 3 ≤ d) {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n) :
    ∀ᶠ n in atTop, sz.Bctl n (t n) ≤ 1 := by
  obtain ⟨c₀, hc₀, hBsm⟩ := BAExp14d_Bctl_small d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  filter_upwards [hBsm t ht0 htT, ((tendsto_rpow_atTop hc₀).comp hsz).eventually (eventually_ge_atTop (2 : ℝ)),
    hsz.eventually (eventually_ge_atTop 1)] with n hB hN2 hN1
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  refine hB.trans ?_
  rw [Real.rpow_neg hN0.le]
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ c₀ := Real.rpow_pos_of_pos hN0 _
  rw [mul_inv_le_iff₀ hp]
  have : (2 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ c₀ := hN2
  linarith

/-- **The floor** `N^{-|o|/2} ≤ η⁻¹ B^{o/2}` eventually (copy of the use of `lwExpTerm3_floor`, `LWExpTerm3:1499-1505`; `η ≤ 1` is
`BAAuxGraph2_eta_le_one`, `B ≤ 1` eventually, `N⁻¹ ≤ B` is `expAvg_Bctl_ge`). -/
private theorem BAExp14d_floor {d : ℕ} (hd : 3 ≤ d) {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (o : ℤ) : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤
      ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2) := by
  filter_upwards [BAExp14d_B_le_one hd hκ hε h𝔡 hflow ht0 htT] with n hBn
  have ht1 := (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lwExpTerm3_floor hN1 (STBctl_pos sz n ht1) hBn (expAvg_Bctl_ge sz n (ht0 n) ht1)
    (BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)) (BAAuxGraph2_eta_le_one sz z hκ hflow n (ht0 n) (htT n)) o

/-- The separation `ρ - 2R = (log W)^{3/2} ≥ K log W` eventually (the pattern of `BAAuxGraph2B_sep`, `BAAuxGraph2B:938`, for a general
`W ≥ N^𝔠`). -/
private theorem BAExp14d_sepW {d : ℕ} {sz : Sizes d} {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto) (hbw : sz.Bandwidth 𝔠) (K : ℝ) :
    ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by
  have hW : Tendsto (fun n => ((sz.W n : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hbw ((tendsto_rpow_atTop h𝔠).comp hsz)
  filter_upwards [(Real.tendsto_log_atTop.comp hW).eventually_ge_atTop (K ^ 2),
    (Real.tendsto_log_atTop.comp hW).eventually_ge_atTop 1] with n h1' h2'
  have h1 : K ^ 2 ≤ Real.log ((sz.W n : ℕ) : ℝ) := h1'
  have h2 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) := h2'
  have e : Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
      Real.log ((sz.W n : ℕ) : ℝ) * Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [e]
  calc K * Real.log ((sz.W n : ℕ) : ℝ) ≤ |K| * Real.log ((sz.W n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self K) (by linarith)
    _ ≤ Real.sqrt (Real.log ((sz.W n : ℕ) : ℝ)) * Real.log ((sz.W n : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (Real.abs_le_sqrt h1) (by linarith)
    _ = _ := mul_comm _ _

/-- The tail `e^{-c r/2} ≤ N^{-D'}` for `r = (log W)^{3/2}` eventually (`lwTail_log32` and `W ≥ N^𝔠`; `LWExpTerm3:1544-1561`). -/
private theorem BAExp14d_tail {d : ℕ} {sz : Sizes d} {𝔠 c : ℝ} (h𝔠 : 0 < 𝔠) (hc : 0 < c) (hsz : sz.SizeTendsto)
    (hbw : sz.Bandwidth 𝔠) (D' : ℝ) (hD' : 0 ≤ D') :
    ∀ᶠ n in atTop, Real.exp (-(c * Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) / 2)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D') := by
  obtain ⟨W₀, hW₀⟩ := lwTail_log32 hc (D' / 𝔠)
  have hWlarge : ∀ᶠ n in atTop, (W₀ : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := by
    have h1 : Tendsto (fun n => ((sz.size n : ℕ) : ℝ) ^ 𝔠) atTop atTop := (tendsto_rpow_atTop h𝔠).comp hsz
    filter_upwards [hbw, h1.eventually_ge_atTop (W₀ : ℝ)] with n hn1 hn2
    exact hn2.trans hn1
  filter_upwards [hWlarge, hbw] with n hn1 hn2
  have hWn : W₀ ≤ sz.W n := by exact_mod_cast hn1
  refine (hW₀ (sz.W n) hWn).trans ?_
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hNc : 0 < ((sz.size n : ℕ) : ℝ) ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  calc ((sz.W n : ℕ) : ℝ) ^ (-(D' / 𝔠))
      ≤ (((sz.size n : ℕ) : ℝ) ^ 𝔠) ^ (-(D' / 𝔠)) :=
        Real.rpow_le_rpow_of_nonpos hNc hn2 (by have : 0 ≤ D' / 𝔠 := by positivity
                                                linarith)
    _ = ((sz.size n : ℕ) : ℝ) ^ (-D') := by
        rw [← Real.rpow_mul hN0.le]; congr 1; field_simp

/-- The floor `W^d (L^d W^{-D₁}) ≤ 1` for `D₁ = 2 / 𝔠` (`W ≥ N^𝔠`, `W^d L^d = N`): the BA floor of the Ward sum is `≤ N⁻¹`. -/
private theorem BAExp14d_floorW {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (d W L : ℕ) {N : ℝ} (hN1 : 1 ≤ N)
    (hWL : (W : ℝ) ^ d * (L : ℝ) ^ d = N) (hb : N ^ 𝔠 ≤ (W : ℝ)) :
    ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-(2 / 𝔠))) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have hNc : 0 < N ^ 𝔠 := Real.rpow_pos_of_pos hN0 _
  have hW0 : (0 : ℝ) < W := lt_of_lt_of_le hNc hb
  have h1 : (W : ℝ) ^ (-(2 / 𝔠)) ≤ (N ^ 𝔠) ^ (-(2 / 𝔠)) :=
    Real.rpow_le_rpow_of_nonpos hNc hb (by have : 0 ≤ 2 / 𝔠 := by positivity
                                           linarith)
  have h2 : (N ^ 𝔠) ^ (-(2 / 𝔠)) = N ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_mul hN0.le]; congr 1; field_simp
  rw [h2] at h1
  calc ((W : ℝ) ^ d) * (((L : ℝ) ^ d) * (W : ℝ) ^ (-(2 / 𝔠))) = N * (W : ℝ) ^ (-(2 / 𝔠)) := by rw [← hWL]; ring
    _ ≤ N * N ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left h1 hN0.le
    _ = N ^ (-(1 : ℝ)) := by
        have : N ^ (-(1 : ℝ)) = N ^ (1 : ℝ) * N ^ (-(2 : ℝ)) := by rw [← Real.rpow_add hN0]; norm_num
        rw [this, Real.rpow_one]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)

end Scalars

/-! ## 5e. The pathwise `≺` of `X` against `η⁻¹ B^{ord/2}` (twin of `LWExpTerm3:1506-1629`) -/

section Prec

/-- **`‖X‖ ≺ η⁻¹ B^{ord/2}`** for `X = P_{xy}` at the rescaled data: on the intersection of the entry event (`STLocalEntrygL`) and the `ζ` event
(`baGbyZeta_holds`, `(eq:Gbyxi2_BA)`), `BAExp14d_pw` with `Ψ = N^{τ'} B^{1/2}`, `cc = N^{τ'}`, `ξ₀ = ζ`, the Ward sum `baZeta_ward_sum`, then the
arithmetic `BAExp14d_arith`; the floor of the control is `BAExp14d_floor`. -/
private theorem BAExp14d_prec {d : ℕ} (hd : 3 ≤ d) {sz : Sizes d} {z : ℕ → ℂ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε)
    (h𝔡 : 0 < 𝔡) (hflow : BAFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ BAflowT0 sz z n)
    (hE : STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t)
    (P : BAPGraph (Fin 2)) (hN : P.g.Normal) (hnM : P.g.nM = 1) (hatt : BAG5Attached P) :
    PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n v ω => ‖BAExp14d_X sz z t P n v ω‖)
      (fun n _ _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2)) := by
  classical
  obtain ⟨h𝔠, -, hsz, hbw, hWO⟩ := hflow.1
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hr : ∀ n, BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) :=
    fun n => BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨K₀, K₁, Kd, C, c, hK₀, hK₁, hKd, hC, hc, hG3⟩ := baGtoAGT_holds d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  obtain ⟨ε₁, hε₁, hent⟩ := baExp14dEntry_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE
  set kk : ℝ := (Fintype.card (P.E' ⊕ P.I') : ℝ) with hkk
  set rr : ℕ → ℝ := fun n => Real.log ((sz.W n : ℕ) : ℝ) ^ ((3 : ℝ) / 2) with hrr
  set RR : ℕ → ℝ := fun n => kk * rr n with hRR
  set ρρ : ℕ → ℝ := fun n => 2 * RR n + rr n with hρρ
  set D₁ : ℝ := 2 / 𝔠 with hD₁
  have hrr0 : ∀ n, 0 ≤ rr n := fun n => Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast sz.W_pos n)) _
  have hRR0 : ∀ n, 0 ≤ RR n := fun n => mul_nonneg (Nat.cast_nonneg _) (hrr0 n)
  have hρ0 : ∀ n, 0 ≤ ρρ n := fun n => add_nonneg (mul_nonneg two_pos.le (hRR0 n)) (hrr0 n)
  have hsep : ∀ K : ℝ, ∀ᶠ n in atTop, K * Real.log ((sz.W n : ℕ) : ℝ) ≤ ρρ n - 2 * RR n := fun K => by
    filter_upwards [BAExp14d_sepW h𝔠 hsz hbw K] with n hn
    simp only [hρρ, hRR, hrr]
    linarith
  have hGbyZeta := baGbyZeta_holds d hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₁ hε₁ hent ρρ RR D₁ hRR0 hsep
  set o : ℤ := P.scalingOrder with ho
  have hfloor := BAExp14d_floor hd hκ hε h𝔡 hflow ht0 htT o
  refine StochDomAt.of_highProbAt_add_rpow_neg (P := Sizes.seqP (sz.withLam 0)) (size := sz.size) hsz'
    (b := ((|o| : ℤ) : ℝ) / 2) ?_ ?_
  · refine HighProbAt.of_eventually_univ ?_
    filter_upwards [hfloor] with n hn ω v
    exact hn
  · intro τ hτ D hD
    set T : ℝ := ((|o| : ℤ) : ℝ) + 2 * d + 4 with hT
    have habs0 : (0 : ℝ) ≤ ((|o| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg o
    have hT0 : 0 < T := by positivity
    set τ' : ℝ := min 1 (τ / (2 * T)) with hτ'def
    have hτ'0 : 0 < τ' := lt_min one_pos (by positivity)
    have hτ'1 : τ' ≤ 1 := min_le_left _ _
    have hτ'2 : τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3) ≤ τ / 2 := by
      have h1 : τ' ≤ τ / (2 * T) := min_le_right _ _
      calc τ' * (((|o| : ℤ) : ℝ) + 2 * d + 3) ≤ τ / (2 * T) * T :=
            mul_le_mul h1 (by linarith) (by positivity) (by positivity)
        _ = τ / 2 := by field_simp
    have hE₁ := BAExp14d_entry_whp ht1 hE hτ'0
    have hE₂ := StochDomAt.highProb hGbyZeta hτ'0
    refine HighProbAt.mono (HighProbAt.inter hsz' hE₁ hE₂) ?_
    set A : ℝ := 𝔡⁻¹ ^ 2 + 1 with hAdef
    set K₁' : ℝ := P.g.sizeConst (K₀ * A) K₁ Kd with hK₁'
    set K₂ : ℝ := P.g.sizeConst C (C * expC (d - 2) (c / 2)) (C * (1 + expC (d - 2) (c / 2))) with hK₂
    set m : ℕ := P.g.nM + P.g.nS + P.g.nA with hm
    have hA0 : 0 ≤ A := by positivity
    have hK1nn : 0 ≤ K₁' := by rw [hK₁']; unfold BAGraph.sizeConst; positivity
    have hc2 : 0 < c / 2 := by positivity
    have hexp : 0 ≤ expC (d - 2) (c / 2) := by unfold expC; positivity
    have hK2nn : 0 ≤ K₂ := by
      rw [hK₂]; unfold BAGraph.sizeConst
      have : 0 ≤ C * (1 + expC (d - 2) (c / 2)) := mul_nonneg hC (by linarith)
      positivity
    have hτ2 : 0 < τ / 2 := by positivity
    have hev1 : ∀ᶠ n in atTop, 8 * 4 ^ d * K₁' ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
      ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
    have hev2 : ∀ᶠ n in atTop, K₂ ≤ ((sz.size n : ℕ) : ℝ) := hsz.eventually_ge_atTop _
    have hev4 : ∀ᶠ n in atTop, ρρ n + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' := by
      filter_upwards [lwXiRad_holds sz hsz (2 * kk + 1) 0 (3 / 2) (by positivity) le_rfl (by norm_num) τ' hτ'0] with n hn
      simp only [hρρ, hRR, hrr]
      linarith
    have hev5 := BAExp14d_tail h𝔠 hc hsz hbw (D + (m : ℝ) + 1) (by positivity)
    filter_upwards [BAExp14a_eventually hκ hε hflow htT, hWO, BAExp14d_B_le_one hd hκ hε h𝔡 hflow ht0 htT,
      hev1, hev2, hev4, hev5, hbw] with n hgg hlamn hBn hK1n hK2n hradn htailn hb
    rintro ω ⟨hω1, hω2⟩ v
    obtain ⟨-, -, hg, hgΛ⟩ := hgg
    have hlam0 : 0 < sz.lam n :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hlamn.1
    have hLpos : 0 < sz.L n := by have := sz.three_le_L n; omega
    have hLN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      have h : (sz.L n) ^ d ≤ sz.size n := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left _ (sz.W_pos n)) d
      exact_mod_cast h
    have hWN : ((sz.W n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
      have h : (sz.W n) ^ d ≤ sz.size n := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hLpos) d
      exact_mod_cast h
    have hWL : ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
      simp only [Sizes.size]; push_cast; ring
    have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
    have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
    have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)
    have hη1 := BAAuxGraph2_eta_le_one sz z hκ hflow n (ht0 n) (htT n)
    have hfl := BAExp14d_floorW h𝔠 d (sz.W n) (sz.L n) hN1 hWL hb
    have hΨ0 : 0 < ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) :=
      mul_pos (Real.rpow_pos_of_pos hN0 _) (Real.sqrt_pos.2 hB0)
    have hwindow : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ A * (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) ^ 2 := by
      have h1 := BAExp14a_Wd_le (sz := sz) n (ht0 n) (ht1 n)
      have hl2 : sz.lam n ^ 2 + 1 ≤ A := by
        have := pow_le_pow_left₀ hlam0.le hlamn.2 2
        rw [hAdef]; linarith
      have hsq : (((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) ^ 2 =
          ((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n) := by
        rw [mul_pow, Real.sq_sqrt hB0.le, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        congr 2; push_cast; ring
      have hNτ : 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * τ') := Real.one_le_rpow hN1 (by positivity)
      rw [hsq]
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ (sz.lam n ^ 2 + 1) * sz.Bctl n (t n) := h1
        _ ≤ A * sz.Bctl n (t n) := mul_le_mul_of_nonneg_right hl2 hB0.le
        _ ≤ A * (((sz.size n : ℕ) : ℝ) ^ (2 * τ') * sz.Bctl n (t n)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA0
            calc sz.Bctl n (t n) = 1 * sz.Bctl n (t n) := (one_mul _).symm
              _ ≤ _ := mul_le_mul_of_nonneg_right hNτ hB0.le
    -- the Ward sums of `ζ`
    set Ψ : ℝ := ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) with hΨdef
    have hxi : ∀ a, ∑ w, baZetaVar sz z t ρρ D₁ n a w ω ^ 2 ≤
        2 * (2 * ρρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (t n))⁻¹ * (1 + Ψ)) +
          (2 * ρρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) := fun a => by
      exact (Finset.sum_congr rfl fun w _ => BAAuxGraph2_zetaVar_sq sz z t ρρ D₁ n a w ω).trans_le
        (baZeta_ward_sum sz z t ρρ D₁ n hκ hflow (ht0 n) (htT n) (hρ0 n) ω hω1 a)
    have hxi' : ∀ a, ∑ w, baZetaVar sz z t ρρ D₁ n w a ω ^ 2 ≤
        2 * (2 * ρρ n + 1) ^ (2 * d) * ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (t n))⁻¹ * (1 + Ψ)) +
          (2 * ρρ n + 1) ^ d * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ + ((sz.L n : ℕ) : ℝ) ^ d * ((sz.W n : ℕ) : ℝ) ^ (-D₁) := fun a => by
      simp only [baZetaVar_symm sz z t ρρ D₁ n _ a ω]; exact hxi a
    have hpw := BAExp14d_pw P hN hnM hatt
      (BAExp14d_dataT d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n) (BAExp14a_slc sz n ω))
      (A := A) (Ψ := Ψ) (cc := ((sz.size n : ℕ) : ℝ) ^ τ') (R := RR n) (r := rr n)
      (fun a b => baZetaVar sz z t ρρ D₁ n a b ω) hK₀.le hK₁.le hKd hC hc hA0 hΨ0
      (Real.rpow_nonneg hN0.le _) hwindow (hrr0 n) le_rfl (fun a b => baZetaVar_nonneg sz z t ρρ D₁ n a b ω) hω1
      (fun x y a b h1 h2 => hω2 ⟨((x, y), (a, b)), h1, h2⟩) hxi hxi'
      (hG3 (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n) hg hgΛ (hr n)
        (ht0 n) (ht1 n) P.E' P.I' P.g hN _ rfl rfl rfl rfl) ![v.1, v.2]
    have harith := BAExp14d_arith P.g.counters hnM d (sz.L n) (sz.W n) (sz.W_pos n) hN1 hB0 hBn hη0 hη1 rfl rfl hτ'0 hτ'1
      hτ'2 (hρ0 n) hradn hK1nn hK1n hK2nn hK2n htailn hLN hWN hfl
    exact hpw.trans harith

end Prec

/-! ## 6. The `n_M = 1` leaf bound -/

/-- **Target 6, the `n_M = 1` leaf bound** (`T2466_BAG5LeafPrec1`, `T2465_Q1Need` up to the name; twin of `LwGraphPrec1`, `LWExpTerm3:1430`):
for every `P` with the leaf properties of `BAG5LeafProps` and `n_M = 1` and every pair `(x, y)`, `‖𝔼 P_{xy}‖ ≺ t^{n_W} η_t⁻¹ B^{ord(P)/2}` at
`BAlwData` over the carrier law, under the five premises of `BAExp14bS3` (of which only `STLocalEntrygL` is used).  It is the leaf pin
`BAG5LeafPrec` of L4c1 (`T2464`) with the extra hypothesis `P.g.nM = 1`; no distinct-molecule hypothesis on `P`. -/
def BAG5LeafPrec1 (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) → let μ := Sizes.seqP (sz.withLam 0)
      STLocalEntrygL (baFMz sz z) μ t → LWAvgLawgL (baFMz sz z) μ t → STLmaxgL (baFMz sz z) μ t → STLKgL (baFMz sz z) μ t →
      STDecaygL (baFMz sz z) μ t →
      ∀ P : BAPGraph (Fin 2), BAG5LeafProps (fun _ _ => [P]) → P.g.nM = 1 →
        PrecL sz μ (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
            ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂μ‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-- **The `n_M = 1` leaf bound**, route as `lwGraphPrec1` (`LWExpTerm3:1442-1661`): `𝔼 P(BAlwData) = t^{n_W} 𝔼 X`
(`BAExp14d_val_scale`, `t = 0` included), `‖X‖ ≺ η⁻¹ B^{ord/2}` (`BAExp14d_prec`), then `≺ → 𝔼` (`BAExp14a_prec_integral`, with the
polynomial envelope `BAExp14d_env` and the floor `BAExp14d_floor`) and `BAExp14a_det_iff`. -/
theorem baG5LeafPrec1_holds (d : ℕ) : BAG5LeafPrec1 d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT μ hE hA hLmax hLK hDec P hLP hnM1
  obtain ⟨hN, -, -, hatt, -⟩ := hLP true true P (List.mem_singleton_self P)
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hflow.1.2.2.1
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hr : ∀ n, BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) :=
    fun n => BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨Kenv, henv⟩ := BAExp14d_env hd hκ hε h𝔡 hflow ht0 htT P hN hnM1 hatt
  have hprecX := BAExp14d_prec hd hκ hε h𝔡 hflow ht0 htT hE P hN hnM1 hatt
  have hfl := BAExp14d_floor hd hκ hε h𝔡 hflow ht0 htT P.scalingOrder
  have hint := BAExp14a_prec_integral (P := μ) hsz' (BAExp14d_X sz z t P)
    (fun n _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))
    (Kf := ((|P.scalingOrder| : ℤ) : ℝ) / 2) henv (hfl.mono fun n hn _ => hn) hprecX
  have hdet := (BAExp14a_det_iff hsz' _ _).1 hint
  refine (BAExp14a_det_iff hsz' _ _).2 fun τ hτ => ?_
  filter_upwards [hdet τ hτ] with n hn v
  have h1 := hn v
  have hval : ∀ ω : sz.SeqΩ, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] = ((t n : ℝ) : ℂ) ^ P.g.nW * BAExp14d_X sz z t P n v ω :=
    fun ω => BAExp14d_val_scale d (sz.L n) (sz.W n) (sz.three_le_L n) _ κ _ (t n) _ (hr n) (ht0 n) (ht1 n)
      (BAExp14a_slc sz n ω) P ![v.1, v.2]
  have hI : ∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] ∂μ =
      ((t n : ℝ) : ℂ) ^ P.g.nW * ∫ ω, BAExp14d_X sz z t P n v ω ∂μ := by
    exact (integral_congr_ae (Eventually.of_forall hval)).trans (integral_const_mul _ _)
  rw [hI, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (ht0 n)]
  calc (t n) ^ P.g.nW * ‖∫ ω, BAExp14d_X sz z t P n v ω ∂μ‖
      ≤ (t n) ^ P.g.nW * (((sz.size n : ℕ) : ℝ) ^ τ * (((baFMz sz z).eta n (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))) := mul_le_mul_of_nonneg_left h1 (pow_nonneg (ht0 n) _)
    _ = _ := by ring

/-! ## 7. Compiled nonempty instances of targets 4 and 6

Same data as in part A (`d = 3`, `sz0`, `zSeq`, `flow_sz0`, `n = 0`, `t ≡ 1/2`); the instance leaf `leaf1` of target 6 is defined in
part A.  What stays a hypothesis of the leaf instance is the five Step 1/2 pins (other gates' inputs). -/

end RBM.BA
