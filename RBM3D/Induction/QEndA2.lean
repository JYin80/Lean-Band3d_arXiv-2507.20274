/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.QEndA
import RBM3D.Chain.QGridGen2

/-!
# Compiled nonempty instances of `Induction/QEndA` (T2498, row U3s3a′, sibling file)

§8 of the previous layout of `QEndA.lean`, moved here verbatim (namespace `RBM.Ind.QEndAInst`: the instances of the band theorems, which keep name and type), followed by the instances of
the generic twins over the carrier `bandStep2Mat sz E` (`d = 3`, the band data `sz0`).  Imported only by `RBM3D.lean`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Ind

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Path RBM.BA

/-! ### Copies of the private grid helpers of `QEndA` (read by the moved instances) -/

private theorem altEnd_gridStep_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n) :
    0 ≤ gridStep s v K n :=
  div_nonneg (sub_nonneg.2 hsv) (Nat.cast_nonneg _)

private theorem altEnd_gridTime_nonneg {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hs0 : 0 ≤ s n)
    (hsv : s n ≤ v n) (j : ℕ) : 0 ≤ gridTime s v K n j := by
  have hΔ := altEnd_gridStep_nonneg (s := s) (v := v) (K := K) hsv
  unfold gridTime
  have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg this hΔ]

/-- `u_i ≤ v_n` for `i ≤ K_n`, `K_n ≠ 0`. -/
private theorem altEnd_gridTime_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} (hsv : s n ≤ v n)
    (hK : K n ≠ 0) {i : ℕ} (hi : i ≤ K n) : gridTime s v K n i ≤ v n :=
  (ST_gridTime_mono s v K n hsv hi).trans_eq (gridTime_last s v K n hK)

/-! ## 8. Compiled nonempty instances (namespace `QEndAInst`)

The merged admissible sequence `sz0` (`d = 3`; `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`) at the data of
`QBudgetBInst`/`QDriftBInst`: `n = 4` (`L = 20`, `W = 10^5`, `N = (W L)^3 = 8·10^18`) for the fixed-`n` instances, `m = 2`
(tensors of `k = 4` indices), `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `Kg ≡ 4` (`Δ = 1/8`), the alternating `σ = (+,-,+,-)`, the
explicit mollifier `QopAlgebra_mollifier … (m+1)`; and a large `n` (`W_n` above the abstract thresholds `qProxyW0`,
`QDriftA_W0`, taken from `exists_nat_ge`/`inst_data`) where an abstract constant enters.  The numeric helpers are copies of
the private ones of `QDriftBInst` (`QDriftB.lean:451-754`) and `QBudgetBInst` (`QBudgetB.lean:880-935`). -/

namespace QEndAInst

open RBM.Gauss.SizesInst RBM.Ind.GridDriftNCheck RBM.Ind.GridEnvelopeNCheck RBM.Ind.QGridBCheck

private theorem rpow_pow5 {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y ^ 5) ^ r = y ^ (5 * r) := by
  rw [← Real.rpow_natCast y 5, ← Real.rpow_mul hy]; norm_num

private theorem mE_zero_im : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem etaT_zero_half : etaT 0 (1 / 2) = 1 / 2 := by
  unfold etaT
  rw [mE_zero_im]
  norm_num

private theorem sz0_facts (n : ℕ) :
    ((sz0.W n : ℕ) : ℝ) = (2 * ((n : ℝ) + 1)) ^ 5 ∧
      ((sz0.L n : ℕ) : ℝ) = 2 * (2 * ((n : ℝ) + 1)) ∧
      sz0.lam n = ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ := by
  refine ⟨?_, ?_, rfl⟩
  · simp [sz0]
  · simp [sz0]; ring

private theorem lam_pos_n (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem lam_le_one (n : ℕ) : sz0.lam n ≤ 1 := by
  change ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
  have hx1 : (1 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact inv_le_one_of_one_le₀ (one_le_pow₀ hx1)

private theorem L_ge_four (n : ℕ) : (4 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) := by
  have h := (sz0_facts n).2.1
  have := Nat.cast_nonneg (α := ℝ) n
  rw [h]; linarith

/-- All the numeric hypotheses of the instances at `n` with `x = 2(n+1) ≥ 10`. -/
private theorem numeric (n : ℕ) (hx : 10 ≤ 2 * ((n : ℝ) + 1)) :
    1 < ((sz0.W n : ℕ) : ℝ) ∧ (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    Real.log ((sz0.L n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    ((sz0.L n : ℕ) : ℝ) ^ 3 ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ) ∧
    ((3 : ℕ) : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ∧
    (3 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) ∧ (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
  obtain ⟨hW, hL, hlam⟩ := sz0_facts n
  set x : ℝ := 2 * ((n : ℝ) + 1) with hxdef
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxW : ((sz0.W n : ℕ) : ℝ) = x ^ 5 := hW
  have h7 : (10 : ℝ) ^ 7 ≤ x ^ 7 := pow_le_pow_left₀ (by norm_num) hx 7
  have hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    rw [hxW]
    have : (10 : ℝ) ^ 5 ≤ x ^ 5 := pow_le_pow_left₀ (by norm_num) hx 5
    linarith
  have hW15 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) = x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 5) = 1 by norm_num, Real.rpow_one]
  have hs : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have hs3 : (3 : ℝ) ≤ Real.sqrt x := (Real.le_sqrt' (by norm_num)).2 (by nlinarith)
  have hW110 : ((sz0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt x := by
    rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  refine ⟨by rw [hxW]; nlinarith [pow_le_pow_left₀ (by norm_num) hx 5], ?_, ?_, ?_, ?_, ?_, hW2⟩
  · rw [hW15]; linarith
  · rw [hW15, hL, Real.log_mul (by norm_num) (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < x by linarith)
    have h2 := Real.log_two_lt_d9
    linarith
  · rw [hxW, rpow_pow5 hx0, show (5 : ℝ) * 2 = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, hL]
    have h10 : x ^ 10 = x ^ 3 * x ^ 7 := by ring
    have h8 : (2 * x) ^ 3 = 8 * x ^ 3 := by ring
    nlinarith [mul_le_mul_of_nonneg_left h7 (pow_nonneg hx0 3)]
  · rw [hW15, hW110]
    push_cast
    nlinarith
  · rw [hW110]; exact hs3

/-- The constants of the mollifier of `QopAlgebra_mollifier_props` at `d = 3`, `m = 3`. -/
private noncomputable abbrev Cmol3 : ℝ := (1 + 40 * ((3 * 3 : ℕ) : ℝ)) * 6 ^ (3 * 3)

/-- `0 ∈ GoodSetN` at `E = 0`, `u = 0`, `k = 4` with the levels `(Γ, Λ, Φ) = (4, 100, 1)`
(`Γ² Λ = 1600 ≥ 4 · 2^8`), every `τ'`, `D'`. -/
private theorem zero_mem_inst (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (3 + 1) 4 100 1 τ' D' := by
  refine zero_mem_goodSetN_of_levels sz0 n (E := 0) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  have h1 : (1 + sz0.lam n ^ 2) ≤ 2 := by nlinarith [sq_nonneg (sz0.lam n), lam_pos_n n]
  have h2 : (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 2 ^ (2 * (3 + 1)) :=
    pow_le_pow_left₀ (by positivity) h1 _
  push_cast
  calc 4 * (1 + sz0.lam n ^ 2) ^ (2 * (3 + 1)) ≤ 4 * 2 ^ (2 * (3 + 1)) := by gcongr
    _ ≤ 4 * (4 * 100) := by norm_num

/-- `x = 2(n+1) ≤ W_n` and `W_n ≥ 17`, from `max W₁ 17 ≤ x`. -/
private theorem x_le_W (n : ℕ) (hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1)) :
    2 * ((n : ℝ) + 1) ≤ ((sz0.W n : ℕ) : ℝ) := by
  rw [(sz0_facts n).1]
  exact le_self_pow₀ (by linarith) (by norm_num)

/-- `4 W^{-6} ≤ W^{-3}` for `W ≥ 4` (`D' = 6`, `Dc = 3`). -/
private theorem hDD_inst {W : ℝ} (hW : 4 ≤ W) : 4 * W ^ (-(6 : ℝ)) ≤ W ^ (-(3 : ℝ)) := by
  have hW0 : 0 < W := by linarith
  have h : W ^ (-(6 : ℝ)) = W ^ (-(3 : ℝ)) * W ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_add hW0]; norm_num
  have h3 : W ^ (-(3 : ℝ)) ≤ 4⁻¹ := by
    rw [Real.rpow_neg hW0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact inv_anti₀ (by norm_num) (by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hW 3])
  have h2 : 0 ≤ W ^ (-(3 : ℝ)) := Real.rpow_nonneg hW0.le _
  rw [h]
  nlinarith

/-- The `𝒦` envelope on `[0, 1/2]` at `n` (`exists_norm_Kcal_le_win` for the `STKbound E0` proved by `stKbound_holds`),
for the loops of length `≤ 4`, together with a large `n` (`max W₁ 17 ≤ x = 2(n+1)`). -/
private theorem inst_data2 (W₁ : ℝ) :
    ∃ n : ℕ, max W₁ 17 ≤ 2 * ((n : ℝ) + 1) ∧
      ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
        2 ≤ J.length → J.length ≤ 4 →
          ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
            ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4 := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  have hKev := exists_norm_Kcal_le_win sz0 sz0_tendsto E0 hKb (fun _ => by norm_num)
    (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 1 one_pos
  obtain ⟨n, hn1, hn2⟩ := (hKev.and (Filter.eventually_ge_atTop ⌈max W₁ 17⌉₊)).exists
  have hn : max W₁ 17 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn2)
  exact ⟨n, by have := Nat.cast_nonneg (α := ℝ) n; linarith, hn1⟩

/-- **The crude sup at length 4 from the exit family** at a grid time `u ∈ [0, 1/2]` and `E = 0`: for Hermitian `H`,
`‖(𝓛-𝒦)^{(4)}_{u,σ}(H)‖ ≤ W^7` (`altEnd_crudeSup` with `M_K = 16 N`, from the `𝒦` envelope; `N ≤ W^6`, `W ≥ 17`). -/
private theorem crude_u (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ))
    (hn1 : ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 4 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    {H : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin (3 + 1) → Bool) :
    ‖fun a => sz0.STLKM n 0 u H σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hWpos : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by linarith
  have hsize : ((sz0.size n : ℕ) : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    exact_mod_cast sz0_size_le_W_pow n
  have hK : ∀ (σ' : Fin 4 → Bool) (a : Fin 4 → Zd 3 (sz0.L n)),
      ‖sz0.STKloop n 0 u σ' a‖ ≤ ((sz0.size n : ℕ) : ℝ) * 16 := by
    intro σ' a
    have hJ : sz0.STKloop n 0 u σ' a = KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) u (loopOf σ' a) := rfl
    rw [hJ]
    have h2 := hn1 u ⟨hu0, hu⟩ (loopOf σ' a) (by simp [LoopIdx.WF, loopOf])
      (by simp [LoopIdx.length, loopOf]) (by simp [LoopIdx.length, loopOf])
    have hη' : etaT (E0 n) (1 / 2) = 1 / 2 := etaT_zero_half
    simp only [hη', Real.rpow_one] at h2
    refine h2.trans (le_of_eq ?_)
    norm_num
  have hη1 : (etaT 0 u)⁻¹ ^ 4 ≤ 16 := by
    have h : (1 / 2 : ℝ) ≤ etaT 0 u := by
      unfold etaT; rw [mE_zero_im]; linarith
    have h' : (etaT 0 u)⁻¹ ≤ 2 := by
      calc (etaT 0 u)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h
        _ = 2 := by norm_num
    calc (etaT 0 u)⁻¹ ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (inv_nonneg.2 (by linarith)) h' 4
      _ = 16 := by norm_num
  have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h6 : (16 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := by
    have h1 : (17 : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hW17 6
    have h2 : (16 : ℝ) ≤ 17 ^ 6 := by norm_num
    linarith
  have h5 : (17 : ℝ) * ((sz0.W n : ℕ) : ℝ) ^ 6 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
    have : ((sz0.W n : ℕ) : ℝ) ^ 7 = ((sz0.W n : ℕ) : ℝ) ^ 6 * ((sz0.W n : ℕ) : ℝ) := by ring
    rw [this]
    nlinarith [pow_pos hWpos 6]
  have hu1 : u < 1 := by linarith
  have hη : (etaT 0 u)⁻¹ ^ 4 + ((sz0.size n : ℕ) : ℝ) * 16 ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
    rw [h7]
    linarith [hη1, hsize, h5, h6]
  exact altEnd_crudeSup sz0 n (E := 0) (by norm_num) hu0 hu1 hH (by norm_num) (MK := ((sz0.size n : ℕ) : ℝ) * 16)
    (C₀ := 7) hK hη σ

/-- `0 < gridExitTauN` when the grid walk starts in `G 0` and the grid is not empty (`K n > 0`): the first hit is not
at `0` (`hittingBtwn_mem_set_of_hittingBtwn_lt`). -/
private theorem zero_lt_exitTau {d : ℕ} {sz : Sizes d} {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ}
    {G : ℕ → Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)} {ω : PathΩ sz}
    (hK : 0 < K n) (h0 : pathH sz s v K n 0 ω ∈ G 0) : 0 < gridExitTauN sz s v K n G ω := by
  by_contra hne
  have h0' : gridExitTauN sz s v K n G ω = 0 := Nat.eq_zero_of_not_pos hne
  have hlt : gridExitTauN sz s v K n G ω < K n := by omega
  have hmem : (1 / 2 : ℝ) ≤ (G (gridExitTauN sz s v K n G ω))ᶜ.indicator (fun _ => (1 : ℝ))
      (pathH sz s v K n (gridExitTauN sz s v K n G ω) ω) :=
    MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt hlt
  rw [h0', Set.indicator_of_notMem (show pathH sz s v K n 0 ω ∉ (G 0)ᶜ from fun hc => hc h0)] at hmem
  norm_num at hmem



private abbrev H0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ := 0

private theorem hx4 : (10 : ℝ) ≤ 2 * (((4 : ℕ) : ℝ) + 1) := by norm_num

private theorem W4 : ((sz0.W 4 : ℕ) : ℝ) = 100000 := by
  rw [(sz0_facts 4).1]; norm_num

private theorem N4 : ((sz0.size 4 : ℕ) : ℝ) = 8000000000000000000 := by
  have : sz0.size 4 = 8000000000000000000 := by norm_num [Sizes.size, sz0]
  exact_mod_cast this

private theorem W10_4 : ((sz0.W 4 : ℕ) : ℝ) ^ (1 / 10 : ℝ) = Real.sqrt 10 := by
  rw [(sz0_facts 4).1, rpow_pow5 (by positivity), show (5 : ℝ) * (1 / 10) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow]
  norm_num

private theorem sqrt10_pow6 : (Real.sqrt 10) ^ (3 * 2) = 1000 := by
  rw [show 3 * 2 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The alternating sign pattern of the instances. -/
private abbrev σalt : Fin (2 + 1 + 1) → Bool := ![true, false, true, false]

private theorem σalt_last : σalt (Fin.last (2 + 1)) = !σalt 0 := by decide

private theorem hFv4 : ((sz0.W 4 : ℕ) : ℝ) ^ (-(40 : ℝ)) ≤
    ((sz0.W 4 : ℕ) : ℝ) * (((sz0.size 4 : ℕ) : ℝ) ^ (2 * 2 + 4))⁻¹ := by
  rw [W4, N4, Real.rpow_neg (by norm_num), show (40 : ℝ) = ((40 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem hMΛ4 : (2 * ((2 : ℕ) : ℝ) + 5) * (3 * 4 ^ (3 * 2) * (2 / Real.sqrt 1) * Cmol3 *
    ((sz0.W 4 : ℕ) : ℝ) ^ 2) ≤ ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) := by
  rw [W4, N4, Real.rpow_two, Real.sqrt_one]
  norm_num

private theorem hNu4 : (((sz0.size 4 : ℕ) : ℝ))⁻¹ ≤ 1 - 0 := by
  rw [N4]; norm_num

/-- `0 ∈ GoodLinN` at the levels `(Γ, Φ₁, Φ₂, Φ₃) = (4, 1, kΓΦ², 1)`, `k = 4` (`goodSetN_subset_goodLinN`). -/
private theorem zero_mem_lin (n : ℕ) (hlam1 : sz0.lam n ≤ 1) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      GoodLinN sz0 n 0 0 (3 + 1) 4 1 (((3 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2) 1 :=
  goodSetN_subset_goodLinN sz0 n 0 0 (3 + 1) 4 100 1 τ' D' (zero_mem_inst n hlam1 τ' D')

/-- The levels `Φ₂ = kΓΦ² = 16` of the `GoodLinN` set of the instances. -/
private noncomputable abbrev Φ2v : ℝ := ((3 + 1 : ℕ) : ℝ) * 4 * 1 ^ 2

/-- `0` is in the three sets of the exit family at `u = 0` (`GoodSetN` at `(4, 100, 1)`, `GoodLinN` at `(4, 1, 16, 1)`,
`altYSetN` at length `3` and level `4`), for every `n`, `τ'`, `D'`. -/
private theorem zero_mem_G0 (n : ℕ) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n 0 0 (2 + 1 + 1) 4 100 1 τ' D' ∩ GoodLinN sz0 n 0 0 (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetN sz0 n 0 0 (2 + 1 + 1 - 1) 4 := by
  refine ⟨⟨zero_mem_inst n (lam_le_one n) τ' D', zero_mem_lin n (lam_le_one n) τ' D'⟩, fun σ' a' => ?_⟩
  have h := (goodSetN_LKM_le 3 sz0 n 0 0 (2 + 1 + 1) 4 100 1 τ' D' 0
    (zero_mem_inst n (lam_le_one n) τ' D') (by norm_num) (2 + 1) (by omega) (by omega)).2 σ' a'
  simpa using h

/-- The premise `hY` of targets 1-2 at the data: `‖(𝓛-𝒦)^{(j)}‖ ≤ ν X B^{m+1}` with `ν = W`, `X = 1`, `j = m + 1 = 3`
(`goodSetN_LKM_le`, `4 ≤ W`). -/
private theorem hY4 : ∀ (σ' : Fin (2 + 1) → Bool) (a' : Fin (2 + 1) → Zd 3 (sz0.L 4)),
    ‖sz0.STLKM 4 0 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) * 1 * sz0.Bctl 4 0 ^ (2 + 1) := by
  intro σ' a'
  have h := (goodSetN_LKM_le 3 sz0 4 0 0 (2 + 1 + 1) 4 100 1 (1 / 10) 40 H0
    (zero_mem_inst 4 (lam_le_one 4) _ _) (by norm_num) (2 + 1) (by omega) (by omega)).2 σ' a'
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (pow_pos (STBctl_pos sz0 4 (by norm_num)) _).le)
  rw [W4]; norm_num



/-! ### The shift hypothesis `hδ` of C2 at a fixed `n` (copies of the private helpers of `NQEndLin.lean`, `:127-152`,
`:459-482`, `:533-552`, and of the body of `nqEnd_ev_hδ`, `:558-647`; ticket T2199) -/

section ShiftFixed

variable {d : ℕ} (sz : Sizes d)

private theorem altEnd_one_le_size (n : ℕ) : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  exact_mod_cast sz.one_le_size n


/-- `W^d L^d = N` (the private `gridEnv_size_cast` of `GridEnvelopeN`). -/
private theorem altEnd_size_cast (n : ℕ) :
    (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d = ((sz.size n : ℕ) : ℝ) := by
  have : ((sz.size n : ℕ) : ℝ) = (((sz.W n * sz.L n) ^ d : ℕ) : ℝ) := rfl
  rw [this]
  push_cast
  ring

/-- **Crude `W ≤ N`** (`W ≤ W^d ≤ (W L)^d = N`, `d ≥ 1`): the bound for the positive powers of `W`. -/
private theorem altEnd_W_le_size (hd : 1 ≤ d) (n : ℕ) :
    ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by
  have h1 : sz.W n ≤ (sz.W n) ^ d := Nat.le_self_pow (by omega) _
  have h2 : (sz.W n) ^ d ≤ sz.size n := by
    unfold Sizes.size
    exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
  exact_mod_cast h1.trans h2

/-- `Δ ≤ N^{-C_K}` on a grid with `N^{C_K} ≤ K n` and `v - s ≤ 1` (RBM2D `NonAltEnd_step_le`,
`NonAltEnd:652`). -/
private theorem altEnd_step_le {s v : ℕ → ℝ} {K : ℕ → ℕ} {n : ℕ} {C_K : ℝ}
    (hK : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ)) (hvs : v n - s n ≤ 1) :
    gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := lt_of_lt_of_le one_pos (altEnd_one_le_size sz n)
  have hpos : 0 < ((sz.size n : ℕ) : ℝ) ^ C_K := Real.rpow_pos_of_pos hN0 _
  have hK0 : (0 : ℝ) < K n := lt_of_lt_of_le hpos hK
  unfold gridStep
  rw [Real.rpow_neg hN0.le, div_le_iff₀ hK0]
  calc v n - s n ≤ 1 := hvs
    _ = (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * ((sz.size n : ℕ) : ℝ) ^ C_K :=
        (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ (((sz.size n : ℕ) : ℝ) ^ C_K)⁻¹ * (K n : ℝ) :=
        mul_le_mul_of_nonneg_left hK (inv_nonneg.2 hpos.le)

/-- The one-step increment of the grid times is `Δ`. -/
private theorem altEnd_gridTime_succ_sub (s v : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) :
    gridTime s v K n (j + 1) - gridTime s v K n j = gridStep s v K n := by
  unfold gridTime; push_cast; ring

/-- The shift error with `η_{u'}⁻¹ ≤ B`: `eeShiftErrN ≤ W^d k L^d (2k+2) B^{2k+3} (u' - u)`
(RBM2D `NonAltEnd_eeShiftErr_le`, `NonAltEnd:694`, with `W^d`, `L^d`). -/
private theorem altEnd_eeShiftErrN_le {d L W : ℕ} (hW : 1 ≤ W) {E : ℝ} (k : ℕ) {u u' B : ℝ}
    (hη0 : 0 ≤ (etaT E u')⁻¹) (hB : (etaT E u')⁻¹ ≤ B) (hΔ : 0 ≤ u' - u) :
    eeShiftErrN d L W E k u u' ≤
      (W : ℝ) ^ d * ((k : ℝ) * ((L : ℝ) ^ d * (((2 * k + 2 : ℕ) : ℝ) *
        (B ^ (2 * k + 2 + 1) * (u' - u))))) := by
  unfold eeShiftErrN loopShiftErrN
  have hW1 : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hWi : (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ hW1))
  have hWi0 : 0 ≤ (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) := by positivity
  have h1 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) ≤ B ^ (2 * k + 2 + 1) := pow_le_pow_left₀ hη0 hB _
  have h2 : (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * (((W : ℝ) ^ d)⁻¹) ^ (2 * k + 2 - 1) * (u' - u) ≤
      B ^ (2 * k + 2 + 1) * (u' - u) := by
    calc _ ≤ (etaT E u')⁻¹ ^ (2 * k + 2 + 1) * 1 * (u' - u) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWi (by positivity)) hΔ
      _ ≤ _ := by rw [mul_one]; exact mul_le_mul_of_nonneg_right h1 hΔ
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl0 : (0 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  gcongr


/-- (`hδ`, fixed `n`) `W^{-(D''+1)} + eeShiftErrN(u_j, u_{j+1}) ≤ W^{-D''}` for every `j < K n`, given `N^{C_K} ≤ K n`,
`C_K ≥ D'' + 2k + 5`, `2 ≤ W`, `N ≥ 2k(2k+2)`, `η_{v_n}⁻¹ ≤ N` (the body of `nqEnd_ev_hδ`, `NQEndLin.lean:558`, after its
`filter_upwards`). -/
private theorem altEnd_shift_fixed (hd : 1 ≤ d) (k : ℕ) {D'' C_K : ℝ} {E s v : ℕ → ℝ} {K : ℕ → ℕ} (n : ℕ)
    (hE : ∀ n, |E n| < 2) (hs0 : ∀ n, 0 ≤ s n) (hsv : ∀ n, s n ≤ v n) (hv1 : ∀ n, v n < 1)
    (hK0 : ∀ n, K n ≠ 0) (hηn : (etaT (E n) (v n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ)) (hD'' : 0 ≤ D'')
    (hCK : D'' + 2 * (k : ℝ) + 5 ≤ C_K) (hKNn : ((sz.size n : ℕ) : ℝ) ^ C_K ≤ (K n : ℝ))
    (hW2 : (2 : ℝ) ≤ ((sz.W n : ℕ) : ℝ))
    (hNA : 2 * ((k : ℝ) * ((2 * k + 2 : ℕ) : ℝ)) ≤ ((sz.size n : ℕ) : ℝ)) :
    ∀ j < K n, ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) +
      eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j) (gridTime s v K n (j + 1)) ≤
        ((sz.W n : ℕ) : ℝ) ^ (-D'') := by
  set A : ℝ := (k : ℝ) * ((2 * k + 2 : ℕ) : ℝ) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  intro j hj
  have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
  have hWpos : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := altEnd_W_le_size sz hd n
  have hvs : v n - s n ≤ 1 := by linarith [hv1 n, hs0 n]
  have hΔ : gridStep s v K n ≤ ((sz.size n : ℕ) : ℝ) ^ (-C_K) := altEnd_step_le sz hKNn hvs
  have hΔ0 : 0 ≤ gridStep s v K n := ST_gridStep_nonneg s v K n (hsv n)
  have hu'v : gridTime s v K n (j + 1) ≤ v n := by
    have h := ST_gridTime_mono s v K n (hsv n) (show j + 1 ≤ K n by omega)
    rwa [gridTime_last s v K n (hK0 n)] at h
  have hdiff := altEnd_gridTime_succ_sub s v K n j
  have hEn := hE n
  have hηv : 0 < etaT (E n) (v n) := etaT_pos hEn (hv1 n)
  have hη' : 0 < etaT (E n) (gridTime s v K n (j + 1)) := etaT_pos hEn (hu'v.trans_lt (hv1 n))
  have hηle : (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
    refine le_trans (inv_anti₀ hηv ?_) hηn
    unfold etaT
    exact mul_le_mul_of_nonneg_right (by linarith) (mE_im_pos hEn).le
  have hη0 : 0 ≤ (etaT (E n) (gridTime s v K n (j + 1)))⁻¹ := inv_nonneg.2 hη'.le
  have hee := altEnd_eeShiftErrN_le (d := d) (L := sz.L n) (W := sz.W n) (sz.W_pos n) k
    (E := E n) (u := gridTime s v K n j) (u' := gridTime s v K n (j + 1)) hη0 hηle
    (by rw [hdiff]; exact hΔ0)
  rw [hdiff] at hee
  have hsz := altEnd_size_cast sz n
  have hpow : ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
      ((sz.size n : ℕ) : ℝ) ^ (-C_K) = ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by
    have e1 : ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) =
        ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [e1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K)
        = ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * (k : ℝ) + 3) *
          ((sz.size n : ℕ) : ℝ) ^ (-C_K) := by rw [Real.rpow_one]
      _ = ((sz.size n : ℕ) : ℝ) ^ (1 + (2 * (k : ℝ) + 3) + (-C_K)) := by
          rw [Real.rpow_add hN0 (1 + (2 * (k : ℝ) + 3)) (-C_K), Real.rpow_add hN0 (1 : ℝ)]
      _ = _ := by congr 1; ring
  have hmain : eeShiftErrN d (sz.L n) (sz.W n) (E n) k (gridTime s v K n j)
      (gridTime s v K n (j + 1)) ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) := by
    refine hee.trans ?_
    have e : ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * (((sz.L n : ℕ) : ℝ) ^ d *
        (((2 * k + 2 : ℕ) : ℝ) * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)))) =
        (((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) * A *
          (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n) := by rw [hA]; ring
    rw [e, hsz]
    calc ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) * gridStep s v K n)
        ≤ ((sz.size n : ℕ) : ℝ) * A * (((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by gcongr
      _ = A * (((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2 + 1) *
            ((sz.size n : ℕ) : ℝ) ^ (-C_K)) := by ring
      _ = A * ((sz.size n : ℕ) : ℝ) ^ ((2 * (k : ℝ) + 4) - C_K) := by rw [hpow]
      _ ≤ A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) hA0
  have hN2 : A * ((sz.size n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have h0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hN0.le _
    have h2A : A * ((sz.size n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hN0]; linarith
    calc A * (((sz.size n : ℕ) : ℝ) ^ (-D'') * ((sz.size n : ℕ) : ℝ)⁻¹)
        = ((sz.size n : ℕ) : ℝ) ^ (-D'') * (A * ((sz.size n : ℕ) : ℝ)⁻¹) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left h2A h0
      _ = ((sz.size n : ℕ) : ℝ) ^ (-D'') / 2 := by ring
  have hWD : ((sz.size n : ℕ) : ℝ) ^ (-D'') ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') :=
    Real.rpow_le_rpow_of_nonpos hWpos hWN (by linarith)
  have hWm1 : ((sz.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') / 2 := by
    rw [show (-(D'' + 1)) = -D'' + -1 by ring, Real.rpow_add hWpos, Real.rpow_neg_one]
    have hpos : 0 ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') := Real.rpow_nonneg hWpos.le _
    have : ((sz.W n : ℕ) : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) hW2
    calc ((sz.W n : ℕ) : ℝ) ^ (-D'') * ((sz.W n : ℕ) : ℝ)⁻¹
        ≤ ((sz.W n : ℕ) : ℝ) ^ (-D'') * (1 / 2) := mul_le_mul_of_nonneg_left this hpos
      _ = _ := by ring
  linarith

end ShiftFixed

/-! ### Instances 1, 2, 7: the `hY` set, the `hY` event on the grid, the pinned statement -/

/-- **Instance 1** (`altYSetN`, `measurableAltYSetN`): the zero matrix (the walk start `H_0 = 0` at `s ≡ 0`) is in
`altYSetN` at length `m + 1 = 3`, level `ν X = W·1` (`goodSetN_LKM_le`), and the set is measurable. -/
theorem altYSetN_instance :
    (0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ) ∈
      altYSetN sz0 4 0 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1) ∧
    MeasurableSet (altYSetN sz0 4 0 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1)) :=
  ⟨fun σ' a' => hY4 σ' a', measurableAltYSetN sz0 4 0 0 (2 + 1) _⟩

/-- **Instance 2** (`altYGridN`) at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `l = 3`, `X ≡ 1`, `C = 1`
(`K + 1 = 5 ≤ N`, from `sz0_tendsto`), `ε = 1/10`.  The premise `Prec (Ξ̂^{(𝓛-𝒦)}_3 ≺ 1)` on `[s_n, v_n]` is the owed
`STLKU`-type gate (`Step34Pins.lean:184`) and stays a hypothesis; the conclusion is unfolded at one `n` (failure
probability of the grid event at most `N^{-1}`). -/
theorem altYGridN_instance
    (hP : Prec sz0 (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n)
      (fun n u ω => STXiLK sz0 n ((fun _ => (0 : ℝ)) n) (u : ℝ) 3 ω) (fun n _ _ => (fun _ => (1 : ℝ)) n)) :
    ∃ n : ℕ, pathP sz0 {ω | ∀ j ≤ 4, pathH sz0 (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j ω ∈
        altYSetN sz0 n 0 (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j) 3
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1)}ᶜ ≤
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h := altYGridN sz0 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 3
    (fun _ => (1 : ℝ)) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => le_rfl) hP 1
    (by
      filter_upwards [sz0_tendsto.eventually_ge_atTop 5] with n hn
      rw [Real.rpow_one]
      exact_mod_cast hn)
    (1 / 10) (by norm_num)
  obtain ⟨n, hn⟩ := (h 1 one_pos).exists
  exact ⟨n, hn⟩

/-- **Instance 7**: the pinned statement `T2294_altYGridN` (check file §2, copied verbatim) is proved by `altYGridN`. -/
private def T2294_altYGridN : Prop :=
  ∀ {d : ℕ} (sz : Sizes d) (E s v : ℕ → ℝ) (K : ℕ → ℕ) (l : ℕ) (X : ℕ → ℝ),
    (∀ n, 0 ≤ s n) → (∀ n, s n ≤ v n) → (∀ n, v n < 1) → (∀ n, K n ≠ 0) → (∀ n, 1 ≤ X n) →
    Prec sz (U := fun n => TimeIcc s v n)
      (fun n u ω => STXiLK sz n (E n) (u : ℝ) l ω) (fun n _ _ => X n) →
    ∀ C : ℝ, (∀ᶠ n in atTop, ((K n + 1 : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C) →
    ∀ ε : ℝ, 0 < ε →
      HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ≤ K n,
        pathH sz s v K n j ω ∈ altYSetN sz n (E n) (gridTime s v K n j) l
          (((sz.size n : ℕ) : ℝ) ^ ε * X n)})

example : T2294_altYGridN := @altYGridN


/-! ### Instance 3: the `𝒬`-remainder envelope and the bridge -/

private abbrev sg0 : ℕ → ℝ := fun _ => 0

private abbrev vg2 : ℕ → ℝ := fun _ => 1 / 2

/-- **Instance of C1a** (`gridDriftQN_envelope`) at `sz0` (`SizeTendsto` by `sz0_tendsto`; `STKbound E0` by the proved
`stKbound_holds`), `m = 2` (`k = 4`), `κ = 1`, `τ_K = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the alternating `σ`: there
is an `n` where, a.e. in the walk, every grid step `j < 4` and label has `‖rGridQN‖ ≤ qErrQN` at the envelope
`N η_{u_{j+1}}^{-4}`. -/
theorem gridDriftQN_envelope_instance :
    ∃ n : ℕ, ∀ᵐ ω ∂(pathP sz0), ∀ j, j < 4 → ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      ‖rGridQN sz0 E0 sg0 vg2 (fun _ => 4) n (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω a‖ ≤
        qErrQN sz0 E0 sg0 vg2 (fun _ => 4) n (2 + 1) ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
          (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2)
          (((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * (etaT (E0 n) (gridTime sg0 vg2 (fun _ => 4) n (j + 1)))⁻¹ ^
            (2 + 1 + 1)) j := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  exact (gridDriftQN_envelope sz0 1 one_pos 2 (by norm_num) 1 one_pos sz0_tendsto hKb
    (fun _ => by norm_num [E0]) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (Filter.Eventually.of_forall lam_pos_n) σalt).exists

/-- The alternating sign of length `m + 2 = 2` (`m = 0`) of the instance of `gridDriftQN_envelope'`. -/
private abbrev σalt0 : Fin (0 + 1 + 1) → Bool := ![true, false]

/-- **Instance of `gridDriftQN_envelope'` at `m = 0`** (T2313; tensors of `m + 2 = 2` indices, mollifier at `m + 1 = 1`): the data
of `gridDriftQN_envelope_instance` (`sz0`, `κ = 1`, `τ_K = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`; `STKbound E0` by the proved
`stKbound_holds`) with `m = 0` and the alternating `σ = (true, false)`.  There is an `n` where, a.e. in the walk, every grid
step `j < 4` and label has `‖rGridQN‖ ≤ qErrQN` at the envelope `N η_{u_{j+1}}^{-2}`.  No hypothesis is left. -/
theorem gridDriftQN_envelope'_instance :
    ∃ n : ℕ, ∀ᵐ ω ∂(pathP sz0), ∀ j, j < 4 → ∀ a : Fin (0 + 1 + 1) → Zd 3 (sz0.L n),
      ‖rGridQN sz0 E0 sg0 vg2 (fun _ => 4) n (QopAlgebra_mollifier 3 (sz0.L n) (0 + 1) (sz0.lam n)) σalt0 j ω a‖ ≤
        qErrQN sz0 E0 sg0 vg2 (fun _ => 4) n (0 + 1) ((1 + 40 * ((3 * (0 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (0 + 1)))
          (1000 * (1 + ((3 * (0 + 1) : ℕ) : ℝ)) ^ 2)
          (((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * (etaT (E0 n) (gridTime sg0 vg2 (fun _ => 4) n (j + 1)))⁻¹ ^
            (0 + 1 + 1)) j := by
  have hKb : sz0.STKbound E0 := stKbound_holds sz0 (by norm_num) (κ := 1) (gmax := 10) one_pos
    (by norm_num) sz0_tendsto (Filter.Eventually.of_forall fun n => by norm_num [E0])
    (Filter.Eventually.of_forall fun n => ⟨lam_pos_n n, (lam_le_one n).trans (by norm_num)⟩)
  exact (gridDriftQN_envelope' sz0 1 one_pos 0 1 one_pos sz0_tendsto hKb
    (fun _ => by norm_num [E0]) (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num) (Filter.Eventually.of_forall lam_pos_n) σalt0).exists

/-- The kernel weight of the instance of C1b (`k = 4` indices, `Λ_g = κ' = K_L = 1`, `ε = 1/10`, grid `K n = N_n^{31}`). -/
private noncomputable abbrev kapI (n i m' : ℕ) : ℝ :=
  kappaAltQN 3 (2 + 1 + 1) 1 1 1 (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 10) (gridTime sg0 vg2 Kc31 n) i m'

/-- The additive decay weight of the instance of C1b. -/
private noncomputable abbrev epsI (n i m' : ℕ) : ℝ :=
  epsAltQN 3 (2 + 1 + 1) 1 1 1 ((sz0.W n : ℕ) : ℝ) i m'

/-- **Instance of C1b** (`assembledRHSAltQN_qErr_le`) at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K n = N_n^{31}` (`Kc31`),
`m = 2` (`k = 4`), `D_t = 1`, `τ_K = 1/2`, the mollifier constants `C₁ = (1 + 40·9)6^9`, `C₂ = 1000(1 + 9)²`: the weighted
`qErrQN` sum is at most `N^{-1}` by the merged `sum_weighted_qErrQN_instance` (`QGridB.lean:723`); the five common terms
are at the real values `Λ_g = κ' = K_L = C = 1`, `c = 1/2`, `ε = ε_q = 1/10`, `Γ = Λ = dd ≡ 1`, `δ0 = δD = D'' = D_Y = 1`,
`X_s = 1 ≤ X_0 = 2`, every label `a`: the left side (the `AssembledN` right side with `stepErr := qErrQN`) is at most
`assembledRHSAltQN … + N^{-1}`. -/
theorem assembledRHSAltQN_qErr_le_instance :
    ∃ n : ℕ, ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      kapI n 0 (Kc31 n) * 1 + epsI n 0 (Kc31 n) * 1 +
        gridStep sg0 vg2 Kc31 n * ∑ j ∈ Finset.range (Kc31 n), (kapI n (j + 1) (Kc31 n) * 1 + epsI n (j + 1) (Kc31 n) * 1) +
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Real.sqrt (∑ j ∈ Finset.range (Kc31 n),
          (cQVAltQN sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1) 1 (Kc31 n) a j : ℝ)) +
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) +
        ∑ j ∈ Finset.range (Kc31 n), (1 + (1 - gridTime sg0 vg2 Kc31 n (Kc31 n))⁻¹) ^ (2 + 1 + 1) *
          qErrQN sz0 E1 sg0 vg2 Kc31 n (2 + 1) ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
            (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2) (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (etaT (E1 n) (gridTime sg0 vg2 Kc31 n (j + 1)))⁻¹ ^ (2 + 1 + 1)) j ≤
      assembledRHSAltQN sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1 1
        (1 / 2) (1 / 10) 2 a + ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨n, hn⟩ := (sum_weighted_qErrQN_instance.and (Filter.eventually_ge_atTop 0)).exists
  refine ⟨n, fun a => ?_⟩
  exact assembledRHSAltQN_qErr_le sz0 E1 sg0 vg2 Kc31 n 2 1 1 1 1 (1 / 2) (1 / 10) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) 1 1 1 1 (1 / 2) (1 / 10) 1 2 1 ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
    (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2) a (by norm_num [E1]) (by norm_num [sg0]) (by norm_num [sg0, vg2])
    (by norm_num [vg2]) (Kc31_ne_zero n) (by norm_num) (by norm_num) (by convert hn.1 (Kc31 n) le_rfl using 3)

/-! ### Instance 4: the variance proxy after the shift (C2) and `SubGaussStopN` -/

/-- The mollifier constant `C = (1 + 40·9) 6^9` of `QopAlgebra_mollifier … 3` (`d = 3`, `m + 1 = 3`). -/
private noncomputable abbrev Cm2 : ℝ := (1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))

/-- `B_u ≤ 4` for `0 ≤ u ≤ 1/2` at `sz0` (`W ≥ 1`, `L ≥ 4`, `g ≤ 1`; the pattern of `crude_block`). -/
private theorem Bctl_le_four (n : ℕ) (hW : 1 ≤ ((sz0.W n : ℕ) : ℝ)) {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    sz0.Bctl n u ≤ 4 := by
  have hL4 := L_ge_four n
  have hlam := lam_pos_n n
  have hx : (1 / 2 : ℝ) ≤ |1 - u| := by rw [abs_of_nonneg (by linarith)]; linarith
  have h1 : ((sz0.lam n) ^ 2 + |1 - u|)⁻¹ ≤ 2 := by
    have h : (1 / 2 : ℝ) ≤ (sz0.lam n) ^ 2 + |1 - u| := by nlinarith [sq_nonneg (sz0.lam n)]
    calc _ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h
      _ = 2 := by norm_num
  have h3 : (((sz0.L n : ℕ) : ℝ) ^ 3 * |1 - u|)⁻¹ ≤ 1 := by
    have hL3 : (64 : ℝ) ≤ ((sz0.L n : ℕ) : ℝ) ^ 3 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) hL4 3]
    exact inv_le_one_of_one_le₀ (by nlinarith)
  have hBpar0 : 0 ≤ Bparam 3 (sz0.L n) (sz0.lam n) u 0 := by unfold Bparam; positivity
  have hBpar : Bparam 3 (sz0.L n) (sz0.lam n) u 0 ≤ 3 := by
    unfold Bparam
    have h2 : (((((0 : ℕ) : ℝ)) + 1) ^ (3 - 2))⁻¹ = 1 := by norm_num
    rw [h2, mul_one]
    linarith
  have hW3 : ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hW)
  unfold Sizes.Bctl
  calc ((((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) * Bparam 3 (sz0.L n) (sz0.lam n) u 0 ≤ 1 * 3 :=
        mul_le_mul hW3 hBpar hBpar0 zero_le_one
    _ ≤ 4 := by norm_num

private theorem etaT_zero (u : ℝ) : etaT 0 u = 1 - u := by
  unfold etaT
  rw [mE_zero_im, mul_one]

/-- `v ≡ 1/2 ≤ 1 - g²/L²` at `sz0` (`g ≤ 1`, `L ≥ 4`). -/
private theorem hwL_gen (n : ℕ) : vg2 n ≤ 1 - sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 := by
  have hl1 := lam_le_one n
  have hl0 := lam_pos_n n
  have hL4 := L_ge_four n
  have : sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 ≤ 1 / 16 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  norm_num [vg2]
  linarith

/-- `W⁻¹ ≤ (1 - v)/(1 - s) = 1/2` for `W ≥ 2`. -/
private theorem hWt_gen (n : ℕ) (hW2 : (2 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ)) :
    (((sz0.W n : ℕ) : ℝ))⁻¹ ≤ (1 - vg2 n) / (1 - sg0 n) := by
  norm_num [vg2, sg0]
  exact (inv_anti₀ (by norm_num) hW2 : _).trans_eq (by norm_num)

/-- **Instances of C2 and of `subGaussStop_altQN`** at `sz0` (`d = 3`), `m = 2` (`k = 4`), `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`,
`σ` alternating, `M = 0 ∈ GoodSetN` at the levels `(Γ, Λ, Φc) = (4, 100, 1)` (`GoodLinN` at `(4, 1, 16, 1)`), `Λ_g = κ' = 1`,
`K_L = 2`, `C = (1 + 40·9)6^9`, `c = 1/2`, `ε = 1/5`, `τ' = 1/10`, `C₀ = 7`, and the abstract constant `C_Q = qProxyCQ`
(`D'' = 5 + C_Q`, `D' = D'' + 2`, `W_n ≥ qProxyW0 …`).  The shift hypothesis is discharged by the fixed-`n` form of
`nqEnd_ev_hδ` on the grid `K n = ⌈N^{D'' + 14}⌉` (so `Δ ≤ N^{-(D''+14)}`; the window `[0, 1/2]` is not collapsed).  At
`j = 0 < p = 1`: the proxy `Δ · (4 · qvFormQN_{u_1,u_1}(0)(a)) ≤ cQVAltQN`, and `SubGaussStopN` of the stopped propagated
first-chaos part for the exit family `altExitTauN`. -/
theorem hQ_altQN_subGaussStop_altQN_instance :
    ∃ (K : ℕ → ℕ) (n : ℕ), K n ≠ 0 ∧ 0 < gridStep sg0 vg2 K n ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        gridStep sg0 vg2 K n * (((2 + 1 + 1 : ℕ) : ℝ) * qvFormQN sz0 n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) 0 (gridTime sg0 vg2 K n (0 + 1))
          (gridTime sg0 vg2 K n 1) σalt
          (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) a) ≤
        (cQVAltQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n 2 1 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
          (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0 : ℝ)) ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        SubGaussStopN sz0 ((fun _ => (0 : ℝ)) n) σalt (gridTime sg0 vg2 K n)
          (altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
            (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) + 1 + 1) n)
          (fun j ω => zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n j
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt ω) 1 a 0
          (cQVAltQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 K n 2 1 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0)) := by
  set CQ : ℝ := qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) with hCQdef
  have hCQ0 : 0 < CQ := qProxyCQ_pos (by norm_num) _ one_pos two_pos (by positivity) (by norm_num)
  set D'' : ℝ := 5 + CQ with hD''def
  set W₀ : ℝ := qProxyW0 3 (2 + 1) 1 2 Cm2 (1 / 2) 7 (1 / 5) (D'' + 1) with hW₀def
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max W₀ 100) 17)
  have hx : max (max W₀ 100) 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx100 : (100 : ℝ) ≤ 2 * ((n : ℝ) + 1) := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := (((le_max_left _ _).trans (le_max_left _ _)).trans hx).trans hxW
  have hW100 : (100 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx100.trans hxW
  have hWN : ((sz0.W n : ℕ) : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := altEnd_W_le_size sz0 (by norm_num) n
  have hN100 : (100 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := hW100.trans hWN
  have hN0 : ∀ m : ℕ, (0 : ℝ) < ((sz0.size m : ℕ) : ℝ) := fun m =>
    lt_of_lt_of_le one_pos (by exact_mod_cast sz0.one_le_size m)
  set CK : ℝ := D'' + 14 with hCK
  set Kf : ℕ → ℕ := fun m => ⌈((sz0.size m : ℕ) : ℝ) ^ CK⌉₊ with hKf
  have hK0 : ∀ m, Kf m ≠ 0 := fun m =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (hN0 m) _)).ne'
  have hKNn : ((sz0.size n : ℕ) : ℝ) ^ CK ≤ (Kf n : ℝ) := Nat.le_ceil _
  have hKpos : 1 ≤ Kf n := Nat.one_le_iff_ne_zero.2 (hK0 n)
  have hΔ : 0 < gridStep sg0 vg2 Kf n := by
    unfold gridStep
    exact div_pos (by norm_num [sg0, vg2]) (by exact_mod_cast Nat.pos_of_ne_zero (hK0 n))
  have hEn : ∀ m, |(fun _ : ℕ => (0 : ℝ)) m| < 2 := fun _ => by norm_num
  have hs0 : ∀ m, 0 ≤ sg0 m := fun _ => le_rfl
  have hsv : ∀ m, sg0 m ≤ vg2 m := fun _ => by norm_num [sg0, vg2]
  have hv1 : ∀ m, vg2 m < 1 := fun _ => by norm_num [vg2]
  have hηn : (etaT ((fun _ : ℕ => (0 : ℝ)) n) (vg2 n))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by
    change (etaT 0 (1 / 2))⁻¹ ≤ _
    rw [etaT_zero_half, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
    linarith
  have hNA : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) ≤ ((sz0.size n : ℕ) : ℝ) := by
    have h80 : (80 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by linarith
    have e : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) = 80 := by norm_num
    rw [e]; exact h80
  have hCKle : D'' + 1 + 2 * ((4 : ℕ) : ℝ) + 5 ≤ CK := by rw [hCK]; push_cast; linarith
  have hδall := altEnd_shift_fixed sz0 (by norm_num) 4 (D'' := D'' + 1) (C_K := CK) (E := fun _ => (0 : ℝ))
    (s := sg0) (v := vg2) (K := Kf) n hEn hs0 hsv hv1 hK0 hηn (by linarith) hCKle hKNn hW2 hNA
  have hδ0 := hδall 0 (Nat.pos_of_ne_zero (hK0 n))
  -- the bound on the sup of `𝓔 ⊗ 𝓔` at `u_1`
  have hmem := ST_gridTime_mem sg0 vg2 Kf n 1 (by norm_num [sg0, vg2]) (hK0 n) hKpos
  have hu1 : gridTime sg0 vg2 Kf n (0 + 1) ≤ 1 / 2 := by simpa [vg2] using hmem.2
  have hu10 : 0 ≤ gridTime sg0 vg2 Kf n (0 + 1) := by simpa [sg0] using hmem.1
  have hB4 := Bctl_le_four n (by linarith) hu10 hu1
  have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1)) := (STBctl_pos sz0 n (by linarith)).le
  have hη2 : (1 / 2 : ℝ) ≤ etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) := by
    change (1 / 2 : ℝ) ≤ etaT 0 _
    rw [etaT_zero]; linarith
  have hMee : (fun _ : ℕ => (4 : ℝ)) n * ((fun _ : ℕ => (4 : ℝ)) n * (fun _ : ℕ => (100 : ℝ)) n) *
      ((sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1))) +
        ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h3 : ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
    have h2' : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 131072 :=
      h2.trans (by norm_num)
    have h17' : (410338673 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      have : (17 : ℝ) ^ 7 = 410338673 := by norm_num
      linarith
    rw [h7]
    have h4 := mul_le_mul_of_nonneg_left h2' (by norm_num : (0 : ℝ) ≤ 4 * (4 * 100))
    change 4 * (4 * 100) * _ + _ ≤ _
    linarith
  have hwL := hwL_gen n
  have hWt := hWt_gen n hW2
  have hκm : (1 : ℝ) ≤ (mE ((fun _ : ℕ => (0 : ℝ)) n)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  have hϑ := QopAlgebra_mollifier_props 3 (sz0.L n) (2 + 1) (sz0.three_le_L n) (lam_pos_n n)
  have hD : ((2 + 1 : ℕ) : ℝ) + 2 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) < D'' + 1 := by
    rw [hD''def, ← hCQdef]; push_cast; linarith
  have hHerm : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ).IsHermitian :=
    Matrix.isHermitian_zero
  have hzero : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n 0) (2 + 1 + 1)
        ((fun _ : ℕ => (4 : ℝ)) n) ((fun _ : ℕ => (100 : ℝ)) n) ((fun _ : ℕ => (1 : ℝ)) n) (1 / 10)
        (D'' + 1 + 1) := by
    rw [ST_gridTime_zero]
    exact zero_mem_inst n (lam_le_one n) (1 / 10) (D'' + 1 + 1)
  clear_value Kf CK W₀ D'' CQ
  refine ⟨Kf, n, hK0 n, hΔ, fun a => ?_, fun a => ?_⟩
  · exact hQ_altQN (m := 2) 1 1 2 Cm2 (1 / 2) (by norm_num) one_pos one_pos two_pos (by positivity)
      (by norm_num) sz0 (fun _ => (0 : ℝ)) sg0 vg2 Kf n (hEn n) (hs0 n) (hsv n) (hv1 n) hwL hWt hκm
      (lam_pos_n n) (lam_le_one n) (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 7) (D' := D'' + 1 + 1) (D'' := D'')
      (by linarith) (by norm_num) (by norm_num) hWε hlog hLK hdW (by norm_num) hD (hW₀def.symm.trans_le hW0W)
      hϑ (σ := σalt) (fun _ => 4) (fun _ => 100) (fun _ => 1) 1 (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0
      (by norm_num) hMee hδ0 0 hzero hHerm
  · exact subGaussStop_altQN (m := 2) 1 1 2 (by norm_num) one_pos one_pos two_pos sz0 (E := fun _ => (0 : ℝ))
      (s := sg0) (v := vg2) (K := Kf) hEn hs0 hsv hv1 n hwL hWt hκm (lam_pos_n n) (lam_le_one n)
      (ε := 1 / 5) (τ' := 1 / 10) (C₀ := 7) (D' := D'' + 1 + 1) (D'' := D'') (by linarith) (by norm_num)
      (by norm_num) hWε hlog hLK hdW (by norm_num) hD (hW₀def.symm.trans_le hW0W) (σ := σalt)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1)
      (fun _ => 4) 1 (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0 (by norm_num) hMee hδ0

/-! ### Instance 5: the kernel field (C3) and the drift/class fields (C4) -/

/-- **Instance of C3** (`alt_hkerGridQN`) at `n = 4`, `m = 2`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `Λ_g = κ' = 1`,
`K_L = 2`, `ε = 1/5`, `ε' = 1/10`, `D_c = 2`, the alternating `σ`, at `i = 0`, `m' = 1` and the zero tensor in the class:
every deterministic hypothesis (regime `v ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-v)/(1-s)`, the window `4 ≤ W^ε`, `log L ≤ W^ε`,
`L^3 ≤ W^{K_L}`, `d W^{ε'} ≤ W^ε`) is discharged. -/
theorem alt_hkerGridQN_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 0)
        (gridTime sg0 vg2 (fun _ => 4) 4 1) (fun _ => 0) a‖ ≤
      kappaAltQN 3 (2 + 1 + 1) 1 1 2 (sz0.lam 4) ((sz0.W 4 : ℕ) : ℝ) (1 / 5)
          (gridTime sg0 vg2 (fun _ => 4) 4) 0 1 * 0 +
        epsAltQN 3 (2 + 1 + 1) 1 1 2 ((sz0.W 4 : ℕ) : ℝ) 0 1 * 0 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  have hW2' : (2 : ℝ) ≤ ((sz0.W 4 : ℕ) : ℝ) := by rw [W4]; norm_num
  have hκm : (1 : ℝ) ≤ (mE ((fun _ : ℕ => (0 : ℝ)) 4)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  refine alt_hkerGridQN (m := 2) 1 1 2 (by norm_num) one_pos one_pos two_pos sz0 (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) 4 le_rfl (by norm_num [sg0, vg2]) (by norm_num) (by norm_num) hκm (lam_pos_n 4) (lam_le_one 4)
    (ε := 1 / 5) (ε' := 1 / 10) (Dc := 2) hW (by norm_num) (by norm_num) hWε hlog hLK hdW (by norm_num)
    (hwL_gen 4) (hWt_gen 4 hW2') σalt 0 1 (by norm_num) (by norm_num) (fun _ => 0) 0 0 le_rfl le_rfl
    (fun _ => by simp) ⟨fun _ _ _ => by simp, by positivity, fun _ _ => by simp⟩ a

/-- **Instance of C4a** (`alt_hdriftGridQN`) on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `n = 4`, `m = 2`,
the alternating `σ`, levels `(Γ, Λ, Φc) = (4, 100, 1)`, `(Φ₁, Φ₂, Φ₃) = (1, 16, 1)`, `Y_l = 4`, the exit time
`altExitTauN` (`0 < τ ω` for every `ω`: `H_0 = 0` is in the three sets, `zero_lt_exitTau`), every path `ω`, `j = 0` and every
label: the three components of `mem_of_lt_altExitTauN` supply `hτG` and `hY`. -/
theorem alt_hdriftGridQN_instance :
    ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)),
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω ∧
      ‖dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω b‖ ≤
        dDriftAltLinQN sz0 4 0 (gridTime sg0 vg2 (fun _ => 4) 4 0) 2 4 1 Φ2v 1
          (qProxyCn 3 (2 + 1) 1 2 Cm2 (1 / 2)) (1 / 5) 40 2 1 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  intro ω b
  have hpos : 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω := by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ 4 rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 4 (1 / 10) 40
  refine ⟨hpos, alt_hdriftGridQN 3 2 1 2 (le_refl 3) one_pos (by norm_num) sz0 4 σalt (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    1 (1 / 10) (1 / 5) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 one_pos (by norm_num) (lam_pos_n 4) (lam_le_one 4) le_rfl
    (by norm_num) (by norm_num) (by rw [N4]; norm_num) hW (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hWε hLK hdW (by linarith) le_rfl (by rw [W10_4, sqrt10_pow6, W4]; norm_num)
    (by rw [W4, N4]; norm_num) hFv4 (by rw [W4, N4, Real.rpow_two, Real.sqrt_one]; norm_num)
    (by rw [W4]; norm_num) σalt_last ω 0 (by norm_num) hpos b⟩

/-- **Instance of C4b** (`alt_hA0clsGridQN`): `m = 2`, `K_L = 2`, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `D_c = 3`,
the exit family at `(Γ, Λ, Φc, Φ₁, Φ₂, Φ₃, Y_l) = (4, 100, 1, 1, 16, 1, 4)`, at an `n` with `W_n ≥ W₀`; for every path
`ω`, `0 < τ ω` and the initial `𝒬`-process is in the class `altClsQN … 0` with `δ_0 = 2 W^{-6}`; the crude sup of the
premise is derived from the Hermitian component and the `𝒦` envelope (`altEnd_crudeSup`, `crude_u`). -/
theorem alt_hA0clsGridQN_instance :
    ∃ n : ℕ, ∀ ω : PathΩ sz0,
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω ∧
      altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) 0
        (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt 0 ω) := by
  set WQ : ℝ := QDriftA_W0 3 (2 + 1) 2 Cm2 (1 / 2) 7 (1 / 5) 6 with hWQ
  obtain ⟨n, hx, hn1⟩ := inst_data2 WQ
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hWQ' : WQ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  refine ⟨n, fun ω => ?_⟩
  have hpos : 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω := by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 n (1 / 10) 6
  refine ⟨hpos, alt_hA0clsGridQN sz0 (le_refl 3) 2 2 7 (1 / 5) 6 (by norm_num) σalt (fun _ => (0 : ℝ)) sg0 vg2
    (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    (1 / 10) 3 hWQ' hLK hdW ?_ (lam_pos_n n) le_rfl (by norm_num) ?_ ω hpos⟩
  · have h6 := hDD_inst (show (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) by linarith)
    have h0 : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (by linarith) _
    linarith
  · intro ω' hω'
    have hH := (mem_of_lt_altExitTauN hω').1.1.1
    have hu0 : 0 ≤ gridTime sg0 vg2 (fun _ => 4) n 0 := by rw [ST_gridTime_zero]
    have hu : gridTime sg0 vg2 (fun _ => 4) n 0 ≤ 1 / 2 := by rw [ST_gridTime_zero]; norm_num [sg0]
    exact crude_u n hW17 hn1 hu0 hu hH σalt

/-- **Instance of C4c** (`alt_hDclsGridQN`): the data of C4b with `D' = 6`, `D_c = 3`; for every path `ω` and every
`j < 4` with `j < altExitTauN ω`, the drift `dGridQN … j ω` is in the class `altClsQN … (j + 1)` with `δ_D = 4 W^{-6}`.  The
two crude sups of the premises are derived for every grid time from the exit-family membership (`altEnd_crudeSup` with the
`𝒦` envelope, and `altEnd_driftSup` with `dDriftLinN ≤ 4^2·(4^4·2)·19 ≤ W^7`). -/
theorem alt_hDclsGridQN_instance :
    ∃ n : ℕ, (∀ ω : PathΩ sz0,
      0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω) ∧
      ∀ (ω : PathΩ sz0) (j : ℕ), j < 4 →
        j < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
          (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω →
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) (j + 1)
          (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
          (dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω) := by
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsGridQN 3 2 1 2 7 (1 / 5) 6 (le_refl 3) one_pos (by norm_num)
  obtain ⟨n, hx, hn1⟩ := inst_data2 W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hpos : ∀ ω : PathΩ sz0, 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n
      ω := fun ω => by
    refine zero_lt_exitTau (by norm_num) ?_
    rw [azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω, ST_gridTime_zero]
    exact zero_mem_G0 n (1 / 10) 6
  refine ⟨n, hpos, fun ω j hj hjτ => ?_⟩
  have hu0 : ∀ i, 0 ≤ gridTime sg0 vg2 (fun _ => 4) n i := fun i =>
    altEnd_gridTime_nonneg (le_rfl : (0 : ℝ) ≤ sg0 n) (by norm_num [sg0, vg2]) i
  have hu : ∀ i ≤ 4, gridTime sg0 vg2 (fun _ => 4) n i ≤ 1 / 2 := fun i hi => by
    have := altEnd_gridTime_le (s := sg0) (v := vg2) (K := fun _ => 4) (n := n) (by norm_num [sg0, vg2])
      (by norm_num) hi
    simpa [vg2] using this
  refine H sz0 n σalt (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 3 (by norm_num) (lam_pos_n n) (lam_le_one n)
    hW0W hLK le_rfl (by norm_num [sg0, vg2]) (by norm_num [vg2])
    (by
      change (1 - (1 / 2 : ℝ))⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ)
      have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      rw [h2, Real.rpow_two]
      nlinarith)
    hdW (hDD_inst (by linarith)) ?_ ?_ ω j hj hjτ
  · intro ω' j' hj' hjτ'
    exact crude_u n hW17 hn1 (hu0 j') (hu j' (by omega)) (mem_of_lt_altExitTauN hjτ').1.1.1 σalt
  · intro ω' j' hj' hjτ'
    have hB4 := Bctl_le_four n (by linarith) (hu0 j') (hu j' (by omega))
    have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j') :=
      (STBctl_pos sz0 n (by have := hu j' (by omega); linarith)).le
    have hη2 : (1 / 2 : ℝ) ≤ etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j') := by
      change (1 / 2 : ℝ) ≤ etaT 0 _
      rw [etaT_zero]; have := hu j' (by omega); linarith
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) ≤ 4 ^ (2 + 1 + 1) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j') ≤ 4 ^ (2 + 1 + 1) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hW17 7
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    refine altEnd_driftSup sz0 n (by norm_num) (mem_of_lt_altExitTauN hjτ').1.2 ?_ σalt
    unfold dDriftLinN
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4 * 4)
    have h4 : (17 : ℝ) ^ 7 = 410338673 := by norm_num
    rw [h7]
    change (4 : ℝ) * 4 * (_ / _) * ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) ≤ _
    have e : ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) = 19 := by
      unfold Φ2v; norm_num
    rw [e]
    have h5 : (4 : ℝ) * 4 * ((sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 (fun _ => 4) n j')) ≤ 4 * 4 * (4 ^ (2 + 1 + 1) / (1 / 2)) := h3
    norm_num at h5
    nlinarith

/-! ### Instance 6: the identity, measurability, terminal value, de-`𝒬` and the `Y` moments (C5), and `altExitMeasN` -/

/-- **Instance of `altExitMeasN`** at the data of C4a: `{0 < altExitTauN}` is `filt 0`-measurable. -/
theorem altExitMeasN_instance :
    MeasurableSet[filt sz0 0] {ω | 0 < altExitTauN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω} :=
  altExitMeasN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 0

/-- **Instance of C5a** (`altEnd_hexp`) at `n = 4`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the explicit mollifier, the
alternating `σ` and the stopping index `τ ≡ 1`: for every target `m' ≤ 4`, a.e., the frozen `𝒬`-process is the Duhamel
expansion (the field `hexp` of `GridAssemblyHypN`). -/
theorem altEnd_hexp_instance :
    ∀ m' ≤ 4, ∀ᵐ ω ∂(pathP sz0),
      aFrozQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 1) m' ω =
        Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 0)
            (gridTime sg0 vg2 (fun _ => 4) 4 m')
            (aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
              (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω) +
          ∑ j ∈ Finset.range (min m' ((fun _ : PathΩ sz0 => 1) ω)),
            Ugen 3 (sz0.L 4) (sz0.lam 4) ((fun _ : ℕ => (0 : ℝ)) 4) σalt (gridTime sg0 vg2 (fun _ => 4) 4 (j + 1))
              (gridTime sg0 vg2 (fun _ => 4) 4 m')
              ((gridStep sg0 vg2 (fun _ => 4) 4 : ℂ) • dGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω +
                zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                yVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                rGridQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω) :=
  altEnd_hexp sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (by norm_num) le_rfl (by norm_num [sg0, vg2])
    (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 1)

/-- **Instance of C5b** (`altEnd_stronglyMeasurable_zVecQN`) at the same data, `j = 0`. -/
theorem altEnd_stronglyMeasurable_zVecQN_instance :
    StronglyMeasurable[filt sz0 (0 + 1)] (fun ω => zVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 0
      (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω) :=
  altEnd_stronglyMeasurable_zVecQN sz0 _ _ _ _ 4 0 _ σalt

/-- **Instance of C5c** (`altEnd_aFroz_eq_aTrue`) at the same data and `τ ≡ 4 = K n`: for every path, the frozen and the
true `𝒬`-processes agree at the last grid index. -/
theorem altEnd_aFroz_eq_aTrue_instance (ω : PathΩ sz0) :
    aFrozQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 4) 4 ω =
      aTrueQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 4 ω :=
  altEnd_aFroz_eq_aTrue sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) 4 (by norm_num) le_rfl
    (by norm_num [sg0, vg2]) (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 4) ω le_rfl

/-- **Instance of C5d** (`altEnd_unQ`) at `n = 4`, `m = 2`, `E = 0`, `u = 0`, `H = 0 ∈ GoodSetN` at `(4, 100, 1)`, `κ = 1`,
`τ' = 1/10`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, the explicit mollifier, the alternating `σ` and every label:
`‖(𝓛-𝒦)_{0,σ}(0)_a‖ ≤ ‖𝒬_0(𝓛-𝒦)_{0,σ}(0)_a‖ + N² B_0^{4}`.  The level `hY` is the one of `goodSetN_LKM_le`. -/
theorem altEnd_unQ_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖sz0.STLKM 4 0 0 H0 σalt a‖ ≤
      ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) 0
          (fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => sz0.STLKM 4 0 0 H0 σalt b) a‖ +
        ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 4 0 ^ (2 + 2) * 1) := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  exact altEnd_unQ (le_refl 3) 2 sz0 4 0 0 1 4 100 1 (1 / 10) 40 (((sz0.W 4 : ℕ) : ℝ)) 1 2 Cm2 (1 / 2) H0 σalt
    (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) one_pos (by norm_num) le_rfl (by norm_num)
    (lam_pos_n 4) hNu4 hW (by norm_num) (by rw [W4]; norm_num) le_rfl
    (by rw [W10_4, sqrt10_pow6, W4]; norm_num) (by rw [W4, N4]; norm_num) hFv4 (by positivity)
    (by norm_num) hMΛ4 (QopAlgebra_mollifier_props 3 (sz0.L 4) (2 + 1) (sz0.three_le_L 4) (lam_pos_n 4))
    (zero_mem_inst 4 (lam_le_one 4) _ _) hY4 σalt_last a

/-- **Instance of C5e** (`altEnd_yMomentsMax`) at `sz0` (`SizeTendsto` by `sz0_tendsto`, `RangeCond (1/2) v` by
`rangeCond_half`, `0 < lam n` for every `n`), `m = 2`, `κ = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, the grid `K ≡ 4`, the
alternating `σ`: one `C_P` and, at some `n`, a level `P ≤ N^{C_P}` for which the `Y` moments of `yVecQN` hold for the
stopping index `τ ≡ 1` (`YMomentBoundsN` with `v_j = Δ² P`, `w_j = Δ⁴ P²`). -/
theorem altEnd_yMomentsMax_instance :
    ∃ C_P : ℝ, 0 ≤ C_P ∧ ∃ n : ℕ, ∃ P : ℝ, 0 ≤ P ∧ P ≤ ((sz0.size n : ℕ) : ℝ) ^ C_P ∧
      YMomentBoundsN sz0 ((fun _ : ℕ => (0 : ℝ)) n) σalt (gridTime sg0 vg2 (fun _ => 4) n) (fun _ => 1) 4
        (fun j ω => yVecQN sz0 (fun _ => (0 : ℝ)) sg0 vg2 (fun _ => 4) n j
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt ω)
        (fun _ => gridStep sg0 vg2 (fun _ => 4) n ^ 2 * P) (fun _ => gridStep sg0 vg2 (fun _ => 4) n ^ 4 * P ^ 2) := by
  obtain ⟨C_P, hC, H⟩ := altEnd_yMomentsMax sz0 (κ := 1) (τR := 1 / 2) (E := fun _ => (0 : ℝ)) (s := sg0) (v := vg2)
    one_pos (fun _ => by norm_num) (fun _ => le_rfl) (fun _ => by norm_num [sg0, vg2]) (fun _ => by norm_num [vg2])
    sz0_tendsto rangeCond_half lam_pos_n 2
  refine ⟨C_P, hC, ?_⟩
  obtain ⟨n, P, hP0, hPle, hτ⟩ := (H (fun _ => 4) (fun _ => by norm_num) σalt).exists
  exact ⟨n, P, hP0, hPle, hτ (fun _ => 1) (fun j => MeasurableSet.const _)⟩


/-! ### Generic instances (T2498, row U3s3a′): the carrier `bandStep2Mat sz0 Ez`, `Ez ≡ 0`, `d = 3`

The data of the band instances above (`sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `n = 4` or a large `n`, `m = 2`, the alternating `σ`).  The carrier facts are the band discharges
(`stepDecompGen_loopForm_band`, `stepDecompGen_walkForm_band`, `gridRepTailGen_ker_band`, `qvPropagatedNg`, `hierDriftGen_*_band`, `bandStep34_LCompat`, `Step2EventsGen_bandLaw`); D1 by
`qProxyG_kerEK4_band_at`; the spectral levels by `zeroModeGen_wardCls_band`, `zeroModeGen_kerSums_band` and the rows and columns of `Step2Gen_thetaKer`; `GoodSetNg`, `GoodLinNg`,
`altYSetNg` from the band sets by the `rfl` bridges.  The registered pins `STKboundgL` (KL7) and the `Prec` control of `altYGridNg` stay hypotheses of their examples. -/

private abbrev Ez : ℕ → ℝ := fun _ => 0

private abbrev CmZ : Step2Mat sz0 := bandStep2Mat sz0 Ez

private theorem Ez_lt : ∀ n, |Ez n| < 2 := fun _ => by norm_num [Ez]

private theorem hLZ : StepDecompGen_LoopForm CmZ Ez := stepDecompGen_loopForm_band sz0 Ez Ez_lt

private theorem hWZ : StepDecompGen_WalkForm CmZ sz0.lam (fun _ => 0) := stepDecompGen_walkForm_band sz0 Ez

private theorem hmZ (n : ℕ) : ‖CmZ.m n‖ ≤ 1 := (norm_mE (E := 0) (by norm_num)).le

private theorem hSZ (n : ℕ) (a : Zd 3 (sz0.L n)) : ∑ b : Zd 3 (sz0.L n), ‖CmZ.S n a b‖ ≤ 1 :=
  (sum_norm_SB_row 3 (sz0.L n) (sz0.lam n) (sz0.three_le_L n) a).le

private theorem hRowZ (n : ℕ) : GridRepTailGen_Ker CmZ.toFlowFM n := gridRepTailGen_ker_band sz0 Ez n (Ez_lt n).le

private theorem hQVZ : QVPropagatedNg CmZ sz0.lam := qvPropagatedNg CmZ Ez sz0.lam hLZ (fun _ => rfl)

private theorem hR1Z : ∀ m, 0 ≤ sz0.lam m * sz0.lam m ∧ sz0.lam m ^ 2 ≤ sz0.lam m ^ 2 ∧ sz0.lam m ^ 2 ≤ 1 * sz0.lam m ^ 2 :=
  fun m => ⟨mul_self_nonneg _, le_rfl, (one_mul _).ge⟩

private theorem hηZ (n : ℕ) (v : ℝ) (_ : 0 ≤ v) (hv1 : v < 1) : 0 < CmZ.eta n v ∧ CmZ.eta n v ≤ 1 - v :=
  hierDriftGen_band_eta 0 (by norm_num) hv1

private theorem mE_im_one : (mE 0).im = 1 := by
  rw [mE_im]
  have : (4 : ℝ) - 0 ^ 2 = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem hY4g : ∀ (σ' : Fin (2 + 1) → Bool) (a' : Fin (2 + 1) → Zd 3 (sz0.L 4)),
    ‖STLKMg CmZ 4 0 H0 σ' a'‖ ≤ ((sz0.W 4 : ℕ) : ℝ) * 1 * sz0.Bctl 4 0 ^ (2 + 1) := by
  intro σ' a'
  rw [← bandStep2_STLKM]
  exact hY4 σ' a'

/-- **Instance of `altYSetNg`, `measurableAltYSetNg`**: the zero matrix is in `altYSetNg` at length `m + 1 = 3`, level `ν X = W·1`, and the set is measurable. -/
theorem altYSetNg_instance :
    (0 : Matrix (Idx 3 (sz0.L 4) (sz0.W 4)) (Idx 3 (sz0.L 4) (sz0.W 4)) ℂ) ∈
      altYSetNg CmZ 4 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1) ∧
    MeasurableSet (altYSetNg CmZ 4 0 (2 + 1) (((sz0.W 4 : ℕ) : ℝ) * 1)) :=
  ⟨fun σ' a' => hY4g σ' a', measurableAltYSetNg hLZ 4 0 (2 + 1) _⟩

/-- **Instance of `altYGridNg`** at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `l = 3`, `X ≡ 1`, `C = 1` (`K + 1 = 5 ≤ N`), `ε = 1/10`.  The premise
`Ξ̂^{(𝓛-𝒦)}_3 ≺ 1` on `[s_n, v_n]` is the owed `STLKU`-type gate and stays a hypothesis; the conclusion is unfolded at one `n`. -/
theorem altYGridNg_instance
    (hP : PrecL sz0 (Sizes.seqP sz0) (U := fun n => TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) n)
      (fun n u ω => STXiLKg CmZ.toFlowFM n (u : ℝ) 3 ω) (fun n _ _ => (fun _ => (1 : ℝ)) n)) :
    ∃ n : ℕ, CmZ.Pp {ω | ∀ j ≤ 4, CmZ.Hpath (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j ω ∈
        altYSetNg CmZ n (gridTime (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) n j) 3
          (((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * 1)}ᶜ ≤
      ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
  have h := altYGridNg CmZ (Sizes.seqP sz0) (seqHflow sz0) hLZ (bandStep34_LCompat sz0 Ez) (Step2EventsGen_bandLaw sz0 Ez)
    (fun _ => (0 : ℝ)) (fun _ => (1 / 2 : ℝ)) (fun _ => 4) 3 (fun _ => (1 : ℝ)) (fun _ => le_rfl) (fun _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) hP (C := 1)
    (by
      filter_upwards [sz0_tendsto.eventually_ge_atTop 5] with n hn
      rw [Real.rpow_one]
      exact_mod_cast hn)
    (ε := 1 / 10) (by norm_num)
  obtain ⟨n, hn⟩ := (h 1 one_pos).exists
  exact ⟨n, hn⟩

/-- **Instance of D2** (`gridDriftQNg_envelope_ev`) at `sz0`, `m = 2` (`k = 4`), `τ_K = 1`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the alternating `σ`: there is an `n` where, a.e. in the walk,
every grid step `j < 4` and label has `‖rGridQNg‖ ≤ qErrQNg` at the envelope `N η_{u_{j+1}}^{-4}`.  The drift classes are the band discharges `hierDriftGen_*_band` under `∀ᶠ n`, the link is
`rfl`; the registered pin `STKboundgL` (KL7) is the one hypothesis left open. -/
theorem gridDriftQNg_envelope_ev_instance (hKb : STKboundgL CmZ.toFlowFM (Sizes.seqP sz0)) :
    ∃ n : ℕ, ∀ᵐ ω ∂CmZ.Pp, ∀ j, j < 4 → ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      ‖rGridQNg CmZ sg0 vg2 (fun _ => 4) n (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω a‖ ≤
        qErrQNg CmZ.toFlowFM sg0 vg2 (fun _ => 4) n (2 + 1) ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1)))
          (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2)
          (((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * (CmZ.eta n (gridTime sg0 vg2 (fun _ => 4) n (j + 1)))⁻¹ ^ (2 + 1 + 1)) j :=
  (gridDriftQNg_envelope_ev 3 sz0 CmZ Ez sz0.lam (fun _ => 0) (Sizes.seqP sz0) 2 1 one_pos sg0 vg2 (fun _ => 4) sz0_tendsto hKb hLZ hWZ
    (fun n a => hSZ n a) (fun n w k σ a => rfl) hmZ hηZ (fun _ => le_rfl) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => by norm_num)
    (Eventually.of_forall fun n => ⟨lam_pos_n n, hierDriftGen_expand_band sz0 _ Ez_lt _ _ _ n, hierDriftGen_kLoop_band sz0 _ Ez_lt n,
      hierDriftGen_kTwo_band sz0 _ Ez_lt n, hierDriftGen_uStep_band sz0 _ Ez_lt n⟩) σalt).exists

/-- The kernel weight of the generic instance of `assembledRHSAltQNg_qErr_le` (`k = 4` indices, `Cv = C₄ = qProxy4C 3 4 1 1 1`, `ε = 1/10`, grid `K n = N_n^{31}`). -/
private noncomputable abbrev kapZ (n i m' : ℕ) : ℝ :=
  kappaAltQNg (2 + 1 + 1) (qProxy4C 3 (2 + 1 + 1) 1 1 1) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 10)
    (gridTime sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n) i m'

/-- The additive decay weight of the generic instance of `assembledRHSAltQNg_qErr_le`. -/
private noncomputable abbrev epsZ (n i m' : ℕ) : ℝ :=
  epsAltQNg (qProxy4C 3 (2 + 1 + 1) 1 1 1) ((sz0.W n : ℕ) : ℝ) i m'

/-- **Instance of `assembledRHSAltQNg_qErr_le`** at `sz0`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K n = N_n^{31}`, `m = 2` (`k = 4`), `D_t = 1`, `τ_K = 1/2`, the mollifier constants
`C₁ = (1 + 40·9)6^9`, `C₂ = 1000(1 + 9)²`: the weighted `qErrQNg` sum is at most `N^{-1}` by the merged `QGridGen2_sum_weighted_qErrQNg_instance`; the five common terms are at the real values
`Λ_g = κ' = K_L = C = 1`, `c = 1/2`, `ε = ε_q = 1/10`, `Γ = Λ = dd ≡ 1`, `δ0 = δD = D'' = D_Y = 1`, `X_s = 1 ≤ X_0 = 2`, every label `a`. -/
theorem assembledRHSAltQNg_qErr_le_instance :
    ∃ n : ℕ, ∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
      kapZ n 0 (QGridGen2Check.QGridGen2_Kc31 n) * 1 + epsZ n 0 (QGridGen2Check.QGridGen2_Kc31 n) * 1 +
        gridStep sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n * ∑ j ∈ Finset.range (QGridGen2Check.QGridGen2_Kc31 n),
          (kapZ n (j + 1) (QGridGen2Check.QGridGen2_Kc31 n) * 1 + epsZ n (j + 1) (QGridGen2Check.QGridGen2_Kc31 n) * 1) +
        ((sz0.size n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * Real.sqrt (∑ j ∈ Finset.range (QGridGen2Check.QGridGen2_Kc31 n),
          (cQVAltQNg CmZ sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n 2 (qProxy4C 3 (2 + 1 + 1) 1 1 1) 1 1 1 (1 / 2) (1 / 10)
            (fun _ => 1) (fun _ => 1) 1 (QGridGen2Check.QGridGen2_Kc31 n) a j : ℝ)) +
        ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) +
        ∑ j ∈ Finset.range (QGridGen2Check.QGridGen2_Kc31 n),
          (1 + (1 - gridTime sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n (QGridGen2Check.QGridGen2_Kc31 n))⁻¹) ^ (2 + 1 + 1) *
          qErrQNg CmZ.toFlowFM sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n (2 + 1)
            ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))) (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2)
            (((sz0.size n : ℕ) : ℝ) ^ (1 / 2 : ℝ) *
              (CmZ.eta n (gridTime sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n (j + 1)))⁻¹ ^ (2 + 1 + 1)) j ≤
      assembledRHSAltQNg CmZ sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n 2 (qProxy4C 3 (2 + 1 + 1) 1 1 1) 1 1 1 (1 / 2) (1 / 10)
        (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1 1 (1 / 2) (1 / 10) 2 a + ((sz0.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  obtain ⟨n, hn⟩ := (QGridGen2Check.QGridGen2_sum_weighted_qErrQNg_instance.and (Filter.eventually_ge_atTop 0)).exists
  refine ⟨n, fun a => ?_⟩
  exact assembledRHSAltQNg_qErr_le CmZ hLZ sg0 vg2 QGridGen2Check.QGridGen2_Kc31 n 2 (qProxy4C 3 (2 + 1 + 1) 1 1 1) 1 1 1 (1 / 2)
    (1 / 10) (fun _ => 1) (fun _ => 1) (fun _ => 1) 1 1 1 1 (1 / 2) (1 / 10) 1 2 1
    ((1 + 40 * ((3 * (2 + 1) : ℕ) : ℝ)) * 6 ^ (3 * (2 + 1))) (1000 * (1 + ((3 * (2 + 1) : ℕ) : ℝ)) ^ 2) a
    (by norm_num [sg0]) (by norm_num [sg0, vg2]) (by norm_num [vg2]) (by
      unfold QGridGen2Check.QGridGen2_Kc31
      have : 0 < sz0.size n := by
        have := four_le_size n
        exact_mod_cast (by linarith : (0 : ℝ) < ((sz0.size n : ℕ) : ℝ))
      positivity) (by norm_num) (by norm_num) (by convert hn.1 (QGridGen2Check.QGridGen2_Kc31 n) le_rfl using 3)


/-- **Instances of `hQ_altQNg` and `subGaussStop_altQNg`** at `sz0` (`d = 3`), `m = 2` (`k = 4`), `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `σ` alternating, `M = 0 ∈ GoodSetNg` at the levels
`(Γ, Λ, Φc) = (4, 100, 1)`, `Λ_g = κ' = 1`, `K_L = 2`, `C = (1 + 40·9)6^9`, `c = 1/2`, `ε = ε₁ = 1/5`, `τ' = 1/10`, `C₀ = 7`, `Cv = C4 = qProxy4C 3 4 1 1 2` (D1 by `qProxyG_kerEK4_band_at`, R1 at
`A = 1`, `gK = sz0.lam`), the abstract constant `C_Q = qProxyCQ` (`D'' = 5 + C_Q`, `D' = D'' + 2`, `W_n ≥ qProxyW0 …`).  The shift hypothesis is discharged by the fixed-`n` form of `nqEnd_ev_hδ` on
the grid `K n = ⌈N^{D'' + 14}⌉` (the window `[0, 1/2]` is not collapsed).  At `j = 0 < p = 1`: the proxy `Δ · (4 · qvFormQNg_{u_1,u_1}(0)(a)) ≤ cQVAltQNg`, and `SubGaussStopNg` of the stopped
propagated first-chaos part for the exit family `altExitTauNg`; the pins `AzumaSubGNg`, `QVPropagatedNg` are the theorems `azumaSubGNg`, `qvPropagatedNg`. -/
theorem hQ_altQNg_subGaussStop_altQNg_instance :
    ∃ (K : ℕ → ℕ) (n : ℕ), K n ≠ 0 ∧ 0 < gridStep sg0 vg2 K n ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        gridStep sg0 vg2 K n * (((2 + 1 + 1 : ℕ) : ℝ) * qvFormQNg CmZ n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) (gridTime sg0 vg2 K n (0 + 1))
          (gridTime sg0 vg2 K n 1) σalt
          (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) a) ≤
        (cQVAltQNg CmZ sg0 vg2 K n 2 (qProxy4C 3 (2 + 1 + 1) 1 1 2) 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
          (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0 : ℝ)) ∧
      (∀ a : Fin (2 + 1 + 1) → Zd 3 (sz0.L n),
        SubGaussStopNg CmZ σalt (gridTime sg0 vg2 K n)
          (altExitTauNg CmZ sg0 vg2 K (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
            (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) + 1 + 1) n)
          (fun j ω => zVecQNg CmZ sg0 vg2 K n j
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt ω) 1 a 0
          (cQVAltQNg CmZ sg0 vg2 K n 2 (qProxy4C 3 (2 + 1 + 1) 1 1 2) 1 2 Cm2 (1 / 2) (1 / 5) (fun _ => 4) (fun _ => 100)
            (5 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2)) 1 a 0)) := by
  set CQ : ℝ := qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) with hCQdef
  have hCQ0 : 0 < CQ := qProxyCQ_pos (by norm_num) _ one_pos two_pos (by positivity) (by norm_num)
  set D'' : ℝ := 5 + CQ with hD''def
  set W₀ : ℝ := qProxyW0 3 (2 + 1) 1 2 Cm2 (1 / 2) 7 (1 / 5) (D'' + 1) with hW₀def
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max W₀ 100) 17)
  have hx : max (max W₀ 100) 17 ≤ 2 * ((n : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx100 : (100 : ℝ) ≤ 2 * ((n : ℝ) + 1) := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := (((le_max_left _ _).trans (le_max_left _ _)).trans hx).trans hxW
  have hW100 : (100 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx100.trans hxW
  have hWN : ((sz0.W n : ℕ) : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := altEnd_W_le_size sz0 (by norm_num) n
  have hN100 : (100 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := hW100.trans hWN
  have hN0 : ∀ m : ℕ, (0 : ℝ) < ((sz0.size m : ℕ) : ℝ) := fun m =>
    lt_of_lt_of_le one_pos (by exact_mod_cast sz0.one_le_size m)
  set CK : ℝ := D'' + 14 with hCK
  set Kf : ℕ → ℕ := fun m => ⌈((sz0.size m : ℕ) : ℝ) ^ CK⌉₊ with hKf
  have hK0 : ∀ m, Kf m ≠ 0 := fun m =>
    (Nat.ceil_pos.2 (Real.rpow_pos_of_pos (hN0 m) _)).ne'
  have hKNn : ((sz0.size n : ℕ) : ℝ) ^ CK ≤ (Kf n : ℝ) := Nat.le_ceil _
  have hKpos : 1 ≤ Kf n := Nat.one_le_iff_ne_zero.2 (hK0 n)
  have hΔ : 0 < gridStep sg0 vg2 Kf n := by
    unfold gridStep
    exact div_pos (by norm_num [sg0, vg2]) (by exact_mod_cast Nat.pos_of_ne_zero (hK0 n))
  have hEn : ∀ m, |(fun _ : ℕ => (0 : ℝ)) m| < 2 := fun _ => by norm_num
  have hs0 : ∀ m, 0 ≤ sg0 m := fun _ => le_rfl
  have hsv : ∀ m, sg0 m ≤ vg2 m := fun _ => by norm_num [sg0, vg2]
  have hv1 : ∀ m, vg2 m < 1 := fun _ => by norm_num [vg2]
  have hηn : (etaT ((fun _ : ℕ => (0 : ℝ)) n) (vg2 n))⁻¹ ≤ ((sz0.size n : ℕ) : ℝ) := by
    change (etaT 0 (1 / 2))⁻¹ ≤ _
    rw [etaT_zero_half, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
    linarith
  have hNA : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) ≤ ((sz0.size n : ℕ) : ℝ) := by
    have h80 : (80 : ℝ) ≤ ((sz0.size n : ℕ) : ℝ) := by linarith
    have e : 2 * (((4 : ℕ) : ℝ) * ((2 * 4 + 2 : ℕ) : ℝ)) = 80 := by norm_num
    rw [e]; exact h80
  have hCKle : D'' + 1 + 2 * ((4 : ℕ) : ℝ) + 5 ≤ CK := by rw [hCK]; push_cast; linarith
  have hδall := altEnd_shift_fixed sz0 (by norm_num) 4 (D'' := D'' + 1) (C_K := CK) (E := fun _ => (0 : ℝ))
    (s := sg0) (v := vg2) (K := Kf) n hEn hs0 hsv hv1 hK0 hηn (by linarith) hCKle hKNn hW2 hNA
  have hδ0 := hδall 0 (Nat.pos_of_ne_zero (hK0 n))
  -- the bound on the sup of `𝓔 ⊗ 𝓔` at `u_1`
  have hmem := ST_gridTime_mem sg0 vg2 Kf n 1 (by norm_num [sg0, vg2]) (hK0 n) hKpos
  have hu1 : gridTime sg0 vg2 Kf n (0 + 1) ≤ 1 / 2 := by simpa [vg2] using hmem.2
  have hu10 : 0 ≤ gridTime sg0 vg2 Kf n (0 + 1) := by simpa [sg0] using hmem.1
  have hB4 := Bctl_le_four n (by linarith) hu10 hu1
  have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1)) := (STBctl_pos sz0 n (by linarith)).le
  have hη2 : (1 / 2 : ℝ) ≤ etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) := by
    change (1 / 2 : ℝ) ≤ etaT 0 _
    rw [etaT_zero]; linarith
  have hMee : (fun _ : ℕ => (4 : ℝ)) n * ((fun _ : ℕ => (4 : ℝ)) n * (fun _ : ℕ => (100 : ℝ)) n) *
      ((sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1))) +
        ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) := by
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 4 ^ (2 * (2 + 1 + 1)) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h3 : ((sz0.W n : ℕ) : ℝ) ^ (-(D'' + 1)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
    have h2' : (sz0.Bctl n (gridTime sg0 vg2 Kf n (0 + 1))) ^ (2 * (2 + 1 + 1)) /
        etaT ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n (0 + 1)) ≤ 131072 :=
      h2.trans (by norm_num)
    have h17' : (410338673 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      have : (17 : ℝ) ^ 7 = 410338673 := by norm_num
      linarith
    rw [h7]
    have h4 := mul_le_mul_of_nonneg_left h2' (by norm_num : (0 : ℝ) ≤ 4 * (4 * 100))
    change 4 * (4 * 100) * _ + _ ≤ _
    linarith
  have hwL := hwL_gen n
  have hWt := hWt_gen n hW2
  have hκm : (1 : ℝ) ≤ (mE ((fun _ : ℕ => (0 : ℝ)) n)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  have hϑ := QopAlgebra_mollifier_props 3 (sz0.L n) (2 + 1) (sz0.three_le_L n) (lam_pos_n n)
  have hD : ((2 + 1 : ℕ) : ℝ) + 2 + qProxyCQ 3 (2 + 1) 1 2 Cm2 (1 / 2) < D'' + 1 := by
    rw [hD''def, ← hCQdef]; push_cast; linarith
  have hHerm : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ).IsHermitian :=
    Matrix.isHermitian_zero
  have hzero : (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      sz0.GoodSetN n ((fun _ : ℕ => (0 : ℝ)) n) (gridTime sg0 vg2 Kf n 0) (2 + 1 + 1)
        ((fun _ : ℕ => (4 : ℝ)) n) ((fun _ : ℕ => (100 : ℝ)) n) ((fun _ : ℕ => (1 : ℝ)) n) (1 / 10)
        (D'' + 1 + 1) := by
    rw [ST_gridTime_zero]
    exact zero_mem_inst n (lam_le_one n) (1 / 10) (D'' + 1 + 1)
  clear_value Kf CK W₀ D'' CQ
  have hzeroZ : GoodSetNg CmZ n (gridTime sg0 vg2 Kf n 0) (2 + 1 + 1) ((fun _ : ℕ => (4 : ℝ)) n) ((fun _ : ℕ => (100 : ℝ)) n)
      ((fun _ : ℕ => (1 : ℝ)) n) (1 / 10) (D'' + 1 + 1)
      (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) :=
    (bandStep2_GoodSetN sz0 Ez n _ (2 + 1 + 1) _ _ _ (1 / 10) (D'' + 1 + 1) 0).1 hzero
  have hKerZ : QProxyG_KerEK4 CmZ.toFlowFM sz0.lam (2 + 1 + 1) 2 (qProxy4C 3 (2 + 1 + 1) 1 1 2) n :=
    qProxyG_kerEK4_band_at sz0 Ez (by norm_num) (by norm_num) one_pos one_pos two_pos n (lam_pos_n n) (lam_le_one n)
      (Ez_lt n).le hκm
  have hεε : Real.sqrt 1 * ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) ^ (1 / 5 : ℝ) := by
    rw [Real.sqrt_one, one_mul]
  have hAk : (1 : ℝ) ^ (2 + 1 + 1) ≤ ((sz0.W n : ℕ) : ℝ) ^ ((qProxy4C 3 (2 + 1 + 1) 1 1 2 - qProxy4C 3 (2 + 1 + 1) 1 1 2) * (1 / 5 : ℝ)) := by
    rw [sub_self, zero_mul, Real.rpow_zero, one_pow]
  refine ⟨Kf, n, hK0 n, hΔ, fun a => ?_, fun a => ?_⟩
  · exact hQ_altQNg (m := 2) (by norm_num) 1 2 Cm2 (1 / 2) one_pos two_pos (by positivity) (by norm_num) CmZ hLZ (gK := sz0.lam)
      (A := 1) (C4 := qProxy4C 3 (2 + 1 + 1) 1 1 2) (Cv := qProxy4C 3 (2 + 1 + 1) 1 1 2) (s := sg0) (v := vg2) (K := Kf)
      (n := n) (hmZ n) (hSZ n) hR1Z le_rfl hKerZ (hRowZ n) le_rfl (hs0 n) (hsv n) (hv1 n) hwL hWt (lam_pos_n n)
      (lam_le_one n) (ε := 1 / 5) (ε₁ := 1 / 5) (τ' := 1 / 10) (C₀ := 7) (D' := D'' + 1 + 1) (D'' := D'')
      (by linarith) (by norm_num) (by norm_num) hWε hlog (by norm_num) (by norm_num) hWε hεε hLK hdW hAk (by norm_num) hD
      (hW₀def.symm.trans_le hW0W) hϑ (σ := σalt) (fun _ => 4) (fun _ => 100) (fun _ => 1) 1
      (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0 (by norm_num) hMee hδ0 0 hzeroZ hHerm
  · exact subGaussStop_altQNg (m := 2) (by norm_num) 1 2 one_pos two_pos (E := Ez)
      (azumaSubGNg CmZ hWZ sg0 vg2 Kf) hLZ hWZ hQVZ (gK := sz0.lam) (A := 1)
      (C4 := qProxy4C 3 (2 + 1 + 1) 1 1 2) (Cv := qProxy4C 3 (2 + 1 + 1) 1 1 2) hs0 hsv hv1 n (hmZ n) (hSZ n) hR1Z le_rfl hKerZ
      (hRowZ n) le_rfl hwL hWt (lam_pos_n n) (lam_le_one n) (ε := 1 / 5) (ε₁ := 1 / 5) (τ' := 1 / 10) (C₀ := 7)
      (D' := D'' + 1 + 1) (D'' := D'') (by linarith) (by norm_num) (by norm_num) hWε hlog (by norm_num) (by norm_num) hWε hεε
      hLK hdW hAk (by norm_num) hD (hW₀def.symm.trans_le hW0W) (σ := σalt) (fun _ => 4) (fun _ => 100) (fun _ => 1)
      (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) 1 (Nat.one_le_iff_ne_zero.2 (hK0 n)) a 0 (by norm_num) hMee hδ0


open private B45_norm_colsum from RBM3D.Induction.B45 in
/-- The columns of `Step2Gen_thetaKer` at the band carrier `CmZ` (`E ≡ 0`): `‖Σ_a θ_{σσ'}(a,b)‖ ≤ 1/(1-t)` (the field `hcol` of `B45Gen_Facts`). -/
private theorem thetaKerZ_cols (n : ℕ) (σ σ' : Bool) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (b : Zd 3 (sz0.L n)) :
    ‖∑ a : Zd 3 (sz0.L n), Step2Gen_thetaKer CmZ.toFlowFM n σ σ' t a b‖ ≤ 1 / (1 - t) := by
  have hμ : ‖mSigma 0 σ * mSigma 0 σ'‖ = 1 := by
    rw [norm_mul, norm_mSigma (by norm_num), norm_mSigma (by norm_num), one_mul]
  have hker := Step2Kern_thetaKer_band sz0 Ez n σ σ' t
  have h1t : (1 - t)⁻¹ = 1 / (1 - t) := one_div (1 - t) ▸ rfl
  simp only [bandStep2Mat, hker]
  rw [QopAlgebra_col_sum_thetaKer (sz0.lam n) (sz0.three_le_L n)
    (by rw [norm_mul, hμ, mul_one, Complex.norm_of_nonneg ht0]; exact ht1) b, ← h1t]
  exact B45_norm_colsum hμ ht0 ht1

/-- The rows of `Step2Gen_thetaKer` at the band carrier `CmZ`: `Σ_b ‖θ_{σσ'}(a,b)‖ ≤ 1/(1-t)` (the field `hrow` of `B45Gen_Facts`). -/
private theorem thetaKerZ_rows (n : ℕ) (σ σ' : Bool) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (a : Zd 3 (sz0.L n)) :
    ∑ b : Zd 3 (sz0.L n), ‖Step2Gen_thetaKer CmZ.toFlowFM n σ σ' t a b‖ ≤ 1 / (1 - t) := by
  have hμ : ‖mSigma 0 σ * mSigma 0 σ'‖ = 1 := by
    rw [norm_mul, norm_mSigma (by norm_num), norm_mSigma (by norm_num), one_mul]
  have hker := Step2Kern_thetaKer_band sz0 Ez n σ σ' t
  have h1t : (1 - t)⁻¹ = 1 / (1 - t) := one_div (1 - t) ▸ rfl
  simp only [bandStep2Mat, hker]
  rw [← h1t]
  exact B45_row_thetaKer (sz0.lam n) (sz0.three_le_L n) hμ ht0 ht1 a

/-- `κm = 1/2 ≤ Im m = 1` at the carrier `CmZ`. -/
private theorem hκmZ (n : ℕ) : (1 / 2 : ℝ) ≤ (CmZ.m n).im := by
  change (1 / 2 : ℝ) ≤ (mE 0).im
  rw [mE_im_one]; norm_num

/-- `0` is in the three sets of the exit family at `u = 0` over the carrier `CmZ` (`GoodSetNg` at `(4, 100, 1)`, `GoodLinNg` at `(4, 1, 16, 1)`, `altYSetNg` at length `3` and level `4`), for every
`n`, `τ'`, `D'`. -/
private theorem zero_mem_GZ (n : ℕ) (τ' D' : ℝ) :
    (0 : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) ∈
      {H | GoodSetNg CmZ n 0 (2 + 1 + 1) 4 100 1 τ' D' H} ∩ GoodLinNg CmZ n 0 (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetNg CmZ n 0 (2 + 1 + 1 - 1) 4 :=
  ⟨⟨(bandStep2_GoodSetN sz0 Ez n 0 (2 + 1 + 1) 4 100 1 τ' D' 0).1 (zero_mem_G0 n τ' D').1.1,
    by rw [← bandStep2_GoodLinN]; exact (zero_mem_G0 n τ' D').1.2⟩, (zero_mem_G0 n τ' D').2⟩

/-- The crude sup at length `4` from the exit family over the carrier `CmZ` at a grid time `u ∈ [0, 1/2]` (band `crude_u`; `STLKMg` at `bandStep2Mat` is `STLKM`). -/
private theorem crude_uZ (n : ℕ) (hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ))
    (hn1 : ∀ w ∈ Set.Icc (0 : ℝ) ((fun _ : ℕ => (1 / 2 : ℝ)) n), ∀ J : LoopIdx (Zd 3 (sz0.L n)), J.WF →
      2 ≤ J.length → J.length ≤ 4 →
        ‖KLK 3 (sz0.L n) (sz0.lam n) (sz0.W n) (E0 n) w J‖ ≤
          ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) * ((etaT (E0 n) ((fun _ : ℕ => (1 / 2 : ℝ)) n))⁻¹) ^ 4)
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2)
    {H : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ} (hH : H.IsHermitian)
    (σ : Fin (3 + 1) → Bool) :
    ‖fun a => STLKMg CmZ n u H σ a‖ ≤ ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) :=
  crude_u n hW17 hn1 hu0 hu hH σ

/-- **Instance of `alt_hkerGridQNg`** at `n = 4`, `m = 2`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `Λ_g = κ' = 1`, `K_L = 2`, `Cv = C4 = qProxy4C 3 4 1 1 2`, `ε = 1/5`, `ε' = 1/10`, `D_c = 2`, the
alternating `σ`, at `i = 0`, `m' = 1` and the zero tensor in the class: every deterministic hypothesis (regime `v ≤ 1 - g²/L²`, `W⁻¹ ≤ (1-v)/(1-s)`, the window `4 ≤ W^ε`, `log L ≤ W^ε`, `L^3 ≤ W^{K_L}`,
`d √A W^{ε'} ≤ W^ε`, D1, R1 at `A = 1`) is discharged. -/
theorem alt_hkerGridQNg_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖Step2Gen_UN CmZ.toFlowFM 4 σalt (gridTime sg0 vg2 (fun _ => 4) 4 0) (gridTime sg0 vg2 (fun _ => 4) 4 1) (fun _ => 0) a‖ ≤
      kappaAltQNg (2 + 1 + 1) (qProxy4C 3 (2 + 1 + 1) 1 1 2) (sz0.lam 4) ((sz0.W 4 : ℕ) : ℝ) (1 / 5)
          (gridTime sg0 vg2 (fun _ => 4) 4) 0 1 * 0 +
        epsAltQNg (qProxy4C 3 (2 + 1 + 1) 1 1 2) ((sz0.W 4 : ℕ) : ℝ) 0 1 * 0 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  have hW2' : (2 : ℝ) ≤ ((sz0.W 4 : ℕ) : ℝ) := by rw [W4]; norm_num
  have hκm : (1 : ℝ) ≤ (mE (Ez 4)).im := by
    change (1 : ℝ) ≤ (mE 0).im
    rw [mE_zero_im]
  refine alt_hkerGridQNg (m := 2) (by norm_num) CmZ (gK := sz0.lam) (A := 1) (C4 := qProxy4C 3 (2 + 1 + 1) 1 1 2)
    (Cv := qProxy4C 3 (2 + 1 + 1) 1 1 2) (KL := 2) hR1Z le_rfl sg0 vg2 (fun _ => 4) 4
    (qProxyG_kerEK4_band_at sz0 Ez (by norm_num) (by norm_num) one_pos one_pos two_pos 4 (lam_pos_n 4) (lam_le_one 4)
      (Ez_lt 4).le hκm) le_rfl le_rfl (by norm_num [sg0, vg2]) (by norm_num)
    (ε := 1 / 5) (ε' := 1 / 10) (Dc := 2) hW (by norm_num) (by norm_num) hWε hlog hLK
    (by rw [Real.sqrt_one, mul_one]; exact hdW)
    (by rw [sub_self, zero_mul, Real.rpow_zero, one_pow]) (by norm_num) (hwL_gen 4) (hWt_gen 4 hW2') σalt 0 1
    (by norm_num) (by norm_num) (fun _ => 0) 0 0 le_rfl le_rfl (fun _ => by simp)
    ⟨fun _ _ _ => by simp, by positivity, fun _ _ => by simp⟩ a


set_option maxRecDepth 20000 in
/-- **Instance of `alt_hdriftGridQNg`** on the walk with `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, `n = 4`, `m = 2`, the alternating `σ`, levels `(Γ, Λ, Φc) = (4, 100, 1)`,
`(Φ₁, Φ₂, Φ₃) = (1, 16, 1)`, `Y_l = 4`, `κm = 1/2`, `K₆ = 1`, the exit time `altExitTauNg` (`0 < τ ω` for every `ω`: `H_0 = 0` is in the three sets), every path `ω`, `j = 0` and every label: the three
components of `mem_of_lt_altExitTauNg` supply `hτG` and `hY`. -/
theorem alt_hdriftGridQNg_instance :
    ∀ (ω : PathΩ sz0) (b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)),
      0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω ∧
      ‖dGridQNg CmZ sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω b‖ ≤
        dDriftAltLinQNg CmZ 4 (gridTime sg0 vg2 (fun _ => 4) 4 0) 2 4 1 Φ2v 1
          (qProxyCn 3 (2 + 1) 1 2 Cm2 (1 / 2)) (1 / 5) 40 2 1 := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  intro ω b
  have hH0 : CmZ.Hpath sg0 vg2 (fun _ => 4) 4 0 ω = 0 := by
    change pathH sz0 sg0 vg2 (fun _ => 4) 4 0 ω = 0
    exact azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ 4 rfl ω
  have hpos : 0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω := by
    refine azumaProxy_pos_gridExitTauNg (by norm_num) ?_
    change CmZ.Hpath sg0 vg2 (fun _ => 4) 4 0 ω ∈ {H | GoodSetNg CmZ 4 (gridTime sg0 vg2 (fun _ => 4) 4 0) (2 + 1 + 1) 4 100 1 (1 / 10) 40 H} ∩
      GoodLinNg CmZ 4 (gridTime sg0 vg2 (fun _ => 4) 4 0) (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetNg CmZ 4 (gridTime sg0 vg2 (fun _ => 4) 4 0) (2 + 1 + 1 - 1) 4
    rw [hH0, ST_gridTime_zero]
    exact zero_mem_GZ 4 (1 / 10) 40
  refine ⟨hpos, alt_hdriftGridQNg (E := Ez) (by norm_num) 2 1 2 one_pos two_pos CmZ hLZ 4 (κm := 1 / 2) (K₆ := 1)
    (by norm_num) (hκmZ 4) (hmZ 4) (zeroModeGen_wardCls_band sz0 Ez Ez_lt) (zeroModeGen_kerSums_band sz0 Ez 4) le_rfl
    (fun σ σ' t ht0 ht1 a => thetaKerZ_rows 4 σ σ' t ht0 ht1 a) (fun σ σ' t ht0 ht1 b => thetaKerZ_cols 4 σ σ' t ht0 ht1 b)
    σalt sg0 vg2 (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    (τ' := 1 / 10) (ε' := 1 / 5) (D' := 40) (ν := ((sz0.W 4 : ℕ) : ℝ)) (X := 1) (τN := 2)
    (lam_pos_n 4) (lam_le_one 4) le_rfl (by norm_num) (by norm_num) (by rw [N4]; norm_num) hW (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hWε hLK hdW (by linarith) le_rfl (by rw [W10_4, sqrt10_pow6, W4]; norm_num)
    (by rw [W4, N4]; norm_num) hFv4 (by rw [W4, N4, Real.rpow_two]; norm_num) (by rw [W4]; norm_num) σalt_last ω 0
    (by norm_num) hpos b⟩

/-- **Instance of `alt_hA0clsGridQNg`**: `m = 2`, `K_L = 2`, `C₀ = 7`, `ε' = 1/5`, `τ' = 1/10`, `D' = 6`, `D_c = 3`, the exit family at `(Γ, Λ, Φc, Φ₁, Φ₂, Φ₃, Y_l) = (4, 100, 1, 1, 16, 1, 4)`, at an `n`
with `W_n ≥ W₀`; for every path `ω`, `0 < τ ω` and the initial `𝒬`-process is in the class `altClsQN … 0` with `δ_0 = 2 W^{-6}`; the crude sup of the premise is derived from the Hermitian component and the
`𝒦` envelope (`crude_uZ`). -/
theorem alt_hA0clsGridQNg_instance :
    ∃ n : ℕ, ∀ ω : PathΩ sz0,
      0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω ∧
      altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) 0
        (2 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
        (aTrueQNg CmZ sg0 vg2 (fun _ => 4) n
          (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt 0 ω) := by
  set WQ : ℝ := QDriftA_W0 3 (2 + 1) 2 Cm2 (1 / 2) 7 (1 / 5) 6 with hWQ
  obtain ⟨n, hx, hn1⟩ := inst_data2 WQ
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hWQ' : WQ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  refine ⟨n, fun ω => ?_⟩
  have hH0 : CmZ.Hpath sg0 vg2 (fun _ => 4) n 0 ω = 0 := by
    change pathH sz0 sg0 vg2 (fun _ => 4) n 0 ω = 0
    exact azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω
  have hpos : 0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4)
      (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω := by
    refine azumaProxy_pos_gridExitTauNg (by norm_num) ?_
    change CmZ.Hpath sg0 vg2 (fun _ => 4) n 0 ω ∈ {H | GoodSetNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1) 4 100 1 (1 / 10) 6 H} ∩
      GoodLinNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1 - 1) 4
    rw [hH0, ST_gridTime_zero]
    exact zero_mem_GZ n (1 / 10) 6
  refine ⟨hpos, alt_hA0clsGridQNg (le_refl 3) 2 2 7 (1 / 5) 6 (by norm_num) CmZ σalt sg0 vg2
    (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4)
    (1 / 10) 3 hWQ' hLK hdW ?_ (lam_pos_n n) le_rfl (by norm_num) ?_ ω hpos⟩
  · have h6 := hDD_inst (show (4 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) by linarith)
    have h0 : 0 ≤ ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)) := Real.rpow_nonneg (by linarith) _
    linarith
  · intro ω' hω'
    have hH := (mem_of_lt_altExitTauNg hω').1.1.1
    have hu0 : 0 ≤ gridTime sg0 vg2 (fun _ => 4) n 0 := by rw [ST_gridTime_zero]
    have hu : gridTime sg0 vg2 (fun _ => 4) n 0 ≤ 1 / 2 := by rw [ST_gridTime_zero]; norm_num [sg0]
    exact crude_uZ n hW17 hn1 hu0 hu hH σalt


/-- **Instance of `alt_hDclsGridQNg`**: the data of `alt_hA0clsGridQNg_instance` with `D' = 6`, `D_c = 3`, `C₆` from `step5KerGen_thDecay_band` (`Λ_g = 1`); for every path `ω` and every `j < 4` with
`j < altExitTauNg ω`, the drift `dGridQNg … j ω` is in the class `altClsQN … (j + 1)` with `δ_D = 4 W^{-6}`.  The two crude sups of the premises are derived for every grid time from the exit-family
membership (`crude_uZ` with the `𝒦` envelope, and `altEnd_driftSupg` with `dDriftLinNg ≤ 4^2·(4^4·2)·19 ≤ W^7`). -/
theorem alt_hDclsGridQNg_instance :
    ∃ n : ℕ, (∀ ω : PathΩ sz0,
      0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
        (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω) ∧
      ∀ (ω : PathΩ sz0) (j : ℕ), j < 4 →
        j < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1) (fun _ => 4) (fun _ => 100)
          (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n ω →
        altClsQN 3 (sz0.L n) (sz0.lam n) ((sz0.W n : ℕ) : ℝ) (1 / 5) 3 (gridTime sg0 vg2 (fun _ => 4) n) (j + 1)
          (4 * ((sz0.W n : ℕ) : ℝ) ^ (-(6 : ℝ)))
          (dGridQNg CmZ sg0 vg2 (fun _ => 4) n
            (QopAlgebra_mollifier 3 (sz0.L n) (2 + 1) (sz0.lam n)) σalt j ω) := by
  obtain ⟨C₆, hC₆, hdec⟩ := step5KerGen_thDecay_band 3 1 (by norm_num) one_pos
  obtain ⟨W₀, hW₀, H⟩ := alt_hDclsGridQNg 3 2 1 2 7 (1 / 5) 6 C₆ 1 (le_refl 3) one_pos (by norm_num) hC₆.le le_rfl
  obtain ⟨n, hx, hn1⟩ := inst_data2 W₀
  have hx17 : (17 : ℝ) ≤ 2 * ((n : ℝ) + 1) := (le_max_right _ _).trans hx
  have hx10 : (10 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by linarith
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric n hx10
  have hxW := x_le_W n hx17
  have hW0W : W₀ ≤ ((sz0.W n : ℕ) : ℝ) := ((le_max_left _ _).trans hx).trans hxW
  have hW17 : (17 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := hx17.trans hxW
  have hpos : ∀ ω : PathΩ sz0, 0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 6 n
      ω := fun ω => by
    have hH0 : CmZ.Hpath sg0 vg2 (fun _ => 4) n 0 ω = 0 := by
      change pathH sz0 sg0 vg2 (fun _ => 4) n 0 ω = 0
      exact azumaProxy_pathH_zero_of_s_zero sz0 sg0 vg2 _ n rfl ω
    refine azumaProxy_pos_gridExitTauNg (by norm_num) ?_
    change CmZ.Hpath sg0 vg2 (fun _ => 4) n 0 ω ∈ {H | GoodSetNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1) 4 100 1 (1 / 10) 6 H} ∩
      GoodLinNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1) 4 1 Φ2v 1 ∩
        altYSetNg CmZ n (gridTime sg0 vg2 (fun _ => 4) n 0) (2 + 1 + 1 - 1) 4
    rw [hH0, ST_gridTime_zero]
    exact zero_mem_GZ n (1 / 10) 6
  refine ⟨n, hpos, fun ω j hj hjτ => ?_⟩
  have hu0 : ∀ i, 0 ≤ gridTime sg0 vg2 (fun _ => 4) n i := fun i =>
    altEnd_gridTime_nonneg (le_rfl : (0 : ℝ) ≤ sg0 n) (by norm_num [sg0, vg2]) i
  have hu : ∀ i ≤ 4, gridTime sg0 vg2 (fun _ => 4) n i ≤ 1 / 2 := fun i hi => by
    have := altEnd_gridTime_le (s := sg0) (v := vg2) (K := fun _ => 4) (n := n) (by norm_num [sg0, vg2])
      (by norm_num) hi
    simpa [vg2] using this
  refine H sz0 CmZ sz0.lam n σalt sg0 vg2 (fun _ => 4) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 3 (zeroModeGen_kerSums_band sz0 Ez n)
    (hdec sz0 Ez fun n' => (Ez_lt n').le) hR1Z (lam_pos_n n) (lam_le_one n)
    hW0W hLK le_rfl (by norm_num [sg0, vg2]) (by norm_num [vg2])
    (by
      change (1 - (1 / 2 : ℝ))⁻¹ ≤ ((sz0.W n : ℕ) : ℝ) ^ (2 : ℝ)
      have h2 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
      rw [h2, Real.rpow_two]
      nlinarith)
    hdW (hDD_inst (by linarith)) ?_ ?_ ω j hj hjτ
  · intro ω' j' hj' hjτ'
    exact crude_uZ n hW17 hn1 (hu0 j') (hu j' (by omega)) (mem_of_lt_altExitTauNg hjτ').1.1.1 σalt
  · intro ω' j' hj' hjτ'
    have hB4 := Bctl_le_four n (by linarith) (hu0 j') (hu j' (by omega))
    have hB0 : 0 ≤ sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j') :=
      (STBctl_pos sz0 n (by have := hu j' (by omega); linarith)).le
    have hη2 : (1 / 2 : ℝ) ≤ CmZ.eta n (gridTime sg0 vg2 (fun _ => 4) n j') := by
      change (1 / 2 : ℝ) ≤ etaT 0 _
      rw [etaT_zero]; have := hu j' (by omega); linarith
    have h1 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) ≤ 4 ^ (2 + 1 + 1) :=
      pow_le_pow_left₀ hB0 hB4 _
    have h2 : (sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        CmZ.eta n (gridTime sg0 vg2 (fun _ => 4) n j') ≤ 4 ^ (2 + 1 + 1) / (1 / 2) :=
      div_le_div₀ (by positivity) h1 (by norm_num) hη2
    have h17 : (17 : ℝ) ^ 7 ≤ ((sz0.W n : ℕ) : ℝ) ^ 7 := pow_le_pow_left₀ (by norm_num) hW17 7
    have h7 : ((sz0.W n : ℕ) : ℝ) ^ (7 : ℝ) = ((sz0.W n : ℕ) : ℝ) ^ 7 := by
      rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    refine altEnd_driftSupg CmZ n (by norm_num) (mem_of_lt_altExitTauNg hjτ').1.2 ?_ σalt
    unfold dDriftLinNg
    have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4 * 4)
    have h4 : (17 : ℝ) ^ 7 = 410338673 := by norm_num
    rw [h7]
    change (4 : ℝ) * 4 * (_ / _) * ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) ≤ _
    have e : ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) = 19 := by
      unfold Φ2v; norm_num
    rw [e]
    have h5 : (4 : ℝ) * 4 * ((sz0.Bctl n (gridTime sg0 vg2 (fun _ => 4) n j')) ^ (2 + 1 + 1) /
        CmZ.eta n (gridTime sg0 vg2 (fun _ => 4) n j')) ≤ 4 * 4 * (4 ^ (2 + 1 + 1) / (1 / 2)) := h3
    norm_num at h5
    nlinarith

/-- **Instance of `altExitMeasNg`** at the data of `alt_hdriftGridQNg_instance`: `{0 < altExitTauNg}` is `filt 0`-measurable. -/
theorem altExitMeasNg_instance :
    MeasurableSet[filt sz0 0] {ω | 0 < altExitTauNg CmZ sg0 vg2 (fun _ => 4) (2 + 1 + 1)
      (fun _ => 4) (fun _ => 100) (fun _ => 1) (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 4 ω} :=
  altExitMeasNg hLZ hWZ sg0 vg2 (fun _ => 4) 4 (2 + 1 + 1) (fun _ => 4) (fun _ => 100) (fun _ => 1)
    (fun _ => 1) (fun _ => Φ2v) (fun _ => 1) (fun _ => 4) (1 / 10) 40 0

/-- **Instance of `altEnd_hexpg`** at `n = 4`, `E ≡ 0`, `s ≡ 0`, `v ≡ 1/2`, `K ≡ 4`, the explicit mollifier, the alternating `σ` and the stopping index `τ ≡ 1`: for every target `m' ≤ 4`, a.e., the
frozen `𝒬`-process is the Duhamel expansion (the field `hexp` of `GridAssemblyHypNg`); the link by `hierDriftGen_kLink_band`, the semigroup law by `step2Gen_USemigroup_band`. -/
theorem altEnd_hexpg_instance :
    ∀ m' ≤ 4, ∀ᵐ ω ∂CmZ.Pp,
      aFrozQNg CmZ sg0 vg2 (fun _ => 4) 4
          (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 1) m' ω =
        Step2Gen_UN CmZ.toFlowFM 4 σalt (gridTime sg0 vg2 (fun _ => 4) 4 0) (gridTime sg0 vg2 (fun _ => 4) 4 m')
            (aTrueQNg CmZ sg0 vg2 (fun _ => 4) 4
              (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 0 ω) +
          ∑ j ∈ Finset.range (min m' ((fun _ : PathΩ sz0 => 1) ω)),
            Step2Gen_UN CmZ.toFlowFM 4 σalt (gridTime sg0 vg2 (fun _ => 4) 4 (j + 1)) (gridTime sg0 vg2 (fun _ => 4) 4 m')
              ((gridStep sg0 vg2 (fun _ => 4) 4 : ℂ) • dGridQNg CmZ sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω +
                zVecQNg CmZ sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                yVecQNg CmZ sg0 vg2 (fun _ => 4) 4 j
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω +
                rGridQNg CmZ sg0 vg2 (fun _ => 4) 4
                  (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt j ω) :=
  altEnd_hexpg CmZ hLZ hWZ sg0 vg2 (fun _ => 4) 4 (hierDriftGen_kLink_band sz0 Ez 4)
    (step2Gen_USemigroup_band sz0 Ez 4 (Ez_lt 4).le) le_rfl (by norm_num [sg0, vg2])
    (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 1)

/-- **Instance of `altEnd_stronglyMeasurable_zVecQNg`** at the same data, `j = 0`. -/
theorem altEnd_stronglyMeasurable_zVecQNg_instance :
    StronglyMeasurable[filt sz0 (0 + 1)] (fun ω => zVecQNg CmZ sg0 vg2 (fun _ => 4) 4 0
      (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt ω) :=
  altEnd_stronglyMeasurable_zVecQNg CmZ hLZ hWZ _ _ _ 4 0 _ σalt

/-- **Instance of `altEnd_aFroz_eq_aTrueg`** at the same data and `τ ≡ 4 = K n`: for every path, the frozen and the true `𝒬`-processes agree at the last grid index. -/
theorem altEnd_aFroz_eq_aTrueg_instance (ω : PathΩ sz0) :
    aFrozQNg CmZ sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt (fun _ => 4) 4 ω =
      aTrueQNg CmZ sg0 vg2 (fun _ => 4) 4
        (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) σalt 4 ω :=
  altEnd_aFroz_eq_aTrueg CmZ sg0 vg2 (fun _ => 4) 4 (step2Gen_USemigroup_band sz0 Ez 4 (Ez_lt 4).le) le_rfl
    (by norm_num [sg0, vg2]) (by norm_num [vg2]) (by norm_num) _ σalt (fun _ => 4) ω le_rfl

set_option maxRecDepth 20000 in
/-- **Instance of `altEnd_unQg`** at `n = 4`, `m = 2`, `E ≡ 0`, `u = 0`, `H = 0 ∈ GoodSetNg` at `(4, 100, 1)`, `κm = 1/2`, `K₆ = 1`, `τ' = 1/10`, `D' = 40`, `ν = W`, `X = 1`, `τ_N = 2`, the explicit
mollifier, the alternating `σ` and every label: `‖(𝓛-𝒦)_{0,σ}(0)_a‖ ≤ ‖𝒬_0(𝓛-𝒦)_{0,σ}(0)_a‖ + N² B_0^{4}`.  The level `hY` is the one of `goodSetN_LKM_le`. -/
theorem altEnd_unQg_instance (a : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4)) :
    ‖STLKMg CmZ 4 0 H0 σalt a‖ ≤
      ‖STQop (d := 3) (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) 0
          (fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => STLKMg CmZ 4 0 H0 σalt b) a‖ +
        ((sz0.size 4 : ℕ) : ℝ) ^ (2 : ℝ) * (sz0.Bctl 4 0 ^ (2 + 2) * 1) := by
  obtain ⟨hW, hWε, hlog, hLK, hdW, hW3, hW2⟩ := numeric 4 hx4
  exact altEnd_unQg (E := Ez) (le_refl 3) 2 CmZ hLZ 4 (κm := 1 / 2) (K₆ := 1) (by norm_num) (hκmZ 4) (hmZ 4)
    (zeroModeGen_wardCls_band sz0 Ez Ez_lt) (zeroModeGen_kerSums_band sz0 Ez 4) le_rfl
    (fun σ σ' t ht0 ht1 a => thetaKerZ_rows 4 σ σ' t ht0 ht1 a) (fun σ σ' t ht0 ht1 b => thetaKerZ_cols 4 σ σ' t ht0 ht1 b)
    (u := 0) (Γc := 4) (Λc := 100) (Φc := 1) (τ' := 1 / 10) (D' := 40) (ν := ((sz0.W 4 : ℕ) : ℝ)) (X := 1) (τN := 2)
    (C := Cm2) (c := 1 / 2) H0 σalt (QopAlgebra_mollifier 3 (sz0.L 4) (2 + 1) (sz0.lam 4)) le_rfl (by norm_num)
    (lam_pos_n 4) hNu4 hW (by norm_num) (by rw [W4]; norm_num) le_rfl (by rw [W10_4, sqrt10_pow6, W4]; norm_num)
    (by rw [W4, N4]; norm_num) hFv4 (by positivity) (by norm_num) (by rw [W4, N4, Real.rpow_two]; norm_num [Cm2])
    (QopAlgebra_mollifier_props 3 (sz0.L 4) (2 + 1) (sz0.three_le_L 4) (lam_pos_n 4))
    ((bandStep2_GoodSetN sz0 Ez 4 0 (2 + 1 + 1) 4 100 1 (1 / 10) 40 H0).1 (zero_mem_inst 4 (lam_le_one 4) _ _)) hY4g σalt_last a

/-- **Instance of `altEnd_driftSupg`** at `n = 4`, `u = 0`, `k = 4`, `0 ∈ GoodLinNg` at `(4, 1, 16, 1)`, `C₀ = 7`: `dDriftLinNg ≤ 4^2·(4^4·2)·19 ≤ W^7`, so `‖driftTensorNg‖ ≤ W^7` for every `σ`. -/
theorem altEnd_driftSupg_instance (σ : Fin (2 + 1 + 1) → Bool) :
    ‖fun b : Fin (2 + 1 + 1) → Zd 3 (sz0.L 4) => driftTensorNg CmZ 4 0 H0 σ b‖ ≤ ((sz0.W 4 : ℕ) : ℝ) ^ (7 : ℝ) := by
  have hB4 := Bctl_le_four 4 (by rw [W4]; norm_num) (le_refl (0 : ℝ)) (by norm_num)
  have hB0 : 0 ≤ sz0.Bctl 4 0 := (STBctl_pos sz0 4 (by norm_num)).le
  have hη2 : (1 / 2 : ℝ) ≤ CmZ.eta 4 0 := by
    change (1 / 2 : ℝ) ≤ etaT 0 _
    rw [etaT_zero]; norm_num
  have h1 : (sz0.Bctl 4 0) ^ (2 + 1 + 1) ≤ 4 ^ (2 + 1 + 1) := pow_le_pow_left₀ hB0 hB4 _
  have h2 : (sz0.Bctl 4 0) ^ (2 + 1 + 1) / CmZ.eta 4 0 ≤ 4 ^ (2 + 1 + 1) / (1 / 2) :=
    div_le_div₀ (by positivity) h1 (by norm_num) hη2
  refine altEnd_driftSupg CmZ 4 (by norm_num) (zero_mem_GZ 4 (1 / 10) 40).1.2 ?_ σ
  unfold dDriftLinNg
  have h3 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 4 * 4)
  have e : ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) = 19 := by
    unfold Φ2v; norm_num
  change (4 : ℝ) * 4 * (_ / _) * ((((2 + 1 + 1 : ℕ) : ℝ) - 2) * 1 + Φ2v + 1) ≤ _
  rw [e, W4]
  norm_num at h3 ⊢
  nlinarith


end QEndAInst

end RBM.Ind

end
