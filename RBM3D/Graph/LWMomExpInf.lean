/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMomExp
import RBM3D.Graph.AnpKey
import RBM3D.Kernel.PropT

/-!
# LW-13b R2 (M): `claim:TTk` and the near pin in `ℓ^∞` (T2359)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `claim:TTk` `(eq:key_T_reudce)`
(`7_8:1662-1664`), the near bound `(adsuu_exp2)` (`7_8:1655`), the domain `𝐃_{≤ℓ}` (`7_8:1650`); the paper's `|·|` is
the `L^∞` norm (`1_2:274`).  This file is the `zdistInf` twin of the merged `EKTTk` (`Evolution/Pins.lean:156`) and of
`AnpDetNearAt` (`Graph/LWMomExp.lean:900`).

* Section 1: the statements `EKTTkInf`, `AnpNearInfAt`, `AnpNearInf`.
* Section 2: the `ℓ^∞` lattice sum `sum_ball_inf_min_pow_le` (from `sum_ball_min_pow_le` at radius `dℓ`) and the kernel
  lemmas in `ℓ^∞`: the pointwise bound for two factors (the `zdistInf` twin of `sfT_pair_le` of `Kernel/PropT.lean:788`,
  in real variables), the summed bound (twin of `key_T_reduce`, `:913`, and `key_T_reduce_absorbed`, `:1056`),
  `ekTTkInf_holds`.
* Section 3: the near chain in `ℓ^∞`: the kernel `𝖳_t(|·-·|_∞ ∧ ℓ)`, the constants of `claim:TTk`, the path systems
  (the generic chain `lwMomExp_sys_bound` of `Graph/LWMomExp.lean:434` is reused), `lwMomExp_near_graph` twin,
  `lwMomExp_nearInf`.
* Section 4: compiled nonempty instances at `d = 3`.

Ports (merged files, text copied and adapted; `zdistD ↦ zdistInf`): `Kernel/PropT.lean:644-914, 1056-1076` at the
merged commit `1fcb883`; `Graph/LWMomExp.lean:521-699, 918-1024` (same commit); `Probe/T2348Pins.lean:335-394`
(`t/T2348`, `9f3bd75`).  RBM1D and RBM2D have no light-weight graph layer.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.style.show false

noncomputable section

namespace RBM.Graph

open RBM RBM.Gauss

/-! ## 1. The statements -/

/-- `claim:TTk` in `ℓ^∞`, single centre (`7_8:1662-1664`; the `zdistInf` twin of `EKTTk`, `Evolution/Pins.lean:156`). -/
def EKTTkInf (d n : ℕ) : Prop :=
  3 ≤ d → 2 ≤ n → ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
      ∀ (D : Finset (Zd d L)) (c : Zd d L), (∀ α ∈ D, (zdistInf d L (c - α) : ℝ) ≤ ℓ) → ∀ x y : Fin n → Zd d L,
        ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistInf d L (x i - α) : ℝ) ℓ) * sfT d L W g t (min (zdistInf d L (y i - α) : ℝ) ℓ))
          ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
              (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))

/-- the near pin in `ℓ^∞` (`AnpDetNearAt`, `LWMomExp.lean:900`, with `zdistInf`; the domain is any set in an `ℓ^∞` ball of radius `ℓ`
around a centre `c`, for the split `c = a` or `c = b`) -/
def AnpNearInfAt (d : ℕ) {p q : ℕ} (Γ : NGraph p q) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ ξ : Zd d L → Zd d L → ℝ, (∀ α β, 0 ≤ ξ α β ∧ ξ α β = ξ β α) →
        (∀ α β, ξ α β ≤ sfT d L W g t (min ((zdistInf d L (α - β) : ℕ) : ℝ) ℓ)) →
        ∀ (c a b : Zd d L) (D : Finset (Zd d L)), (∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) →
          lwMomExp_valOnD Γ ξ (fun _ => a) (fun _ => b) D ≤
            C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q * PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
              sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p

/-- `AnpDetNear` (`Graph/LWMomExp.lean:911`) in `ℓ^∞`. -/
def AnpNearInf (d : ℕ) : Prop :=
  3 ≤ d → ∀ (p q : ℕ) (Γ : NGraph p q), Γ.NoGhost → Γ.IsNested → AnpNearInfAt d Γ

/-! ## 2. The `ℓ^∞` lattice sum and the kernel lemmas -/

/-- **The new analytic content of the `ℓ^∞` twin**: the lattice sum of the proof of `claim:TTk`
(`A_deterministic_estimates.tex:291`) over a set in an `ℓ^∞` ball, from the merged `ℓ¹` lemma `sum_ball_min_pow_le`
(`Defs/RadialSum.lean:367`) at radius `dℓ`; constant `d^{k+2} ballC_k`. -/
theorem sum_ball_inf_min_pow_le {L : ℕ} [NeZero L] (k : ℕ) {ℓ : ℝ} (hℓ : 1 ≤ ℓ) (D : Finset (Zd (k + 2) L))
    (c x : Zd (k + 2) L) (hD : ∀ α ∈ D, ((zdistInf (k + 2) L (c - α) : ℕ) : ℝ) ≤ ℓ) :
    ∑ α ∈ D, ((min ((zdistInf (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (ballC k * ℓ ^ 2) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ((k + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hδ]
  have hδ1 : (1 : ℝ) ≤ δ := by rw [hδ]; exact_mod_cast (by omega : 1 ≤ k + 2)
  have hℓ' : 1 ≤ δ * ℓ := by nlinarith
  have hD' : ∀ α ∈ D, ((zdistD (k + 2) L (c - α) : ℕ) : ℝ) ≤ δ * ℓ := fun α hα => by
    have h1 : ((zdistD (k + 2) L (c - α) : ℕ) : ℝ) ≤ δ * ((zdistInf (k + 2) L (c - α) : ℕ) : ℝ) := by
      rw [hδ]; exact_mod_cast zdistD_le_mul_zdistInf (k + 2) L (c - α)
    nlinarith [hD α hα]
  have hterm : ∀ α ∈ D, ((min ((zdistInf (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ ≤
      δ ^ k * ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) (δ * ℓ) + 1) ^ k)⁻¹ := by
    intro α _
    set r1 : ℝ := ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) with hr1
    set r8 : ℝ := ((zdistInf (k + 2) L (x - α) : ℕ) : ℝ) with hr8
    have h18 : r1 ≤ δ * r8 := by rw [hr1, hr8, hδ]; exact_mod_cast zdistD_le_mul_zdistInf (k + 2) L (x - α)
    have hr8' : 0 ≤ r8 := Nat.cast_nonneg _
    have hr1' : 0 ≤ r1 := Nat.cast_nonneg _
    have hm : min r1 (δ * ℓ) + 1 ≤ δ * (min r8 ℓ + 1) := by
      have : min r1 (δ * ℓ) ≤ δ * min r8 ℓ := by
        rw [mul_min_of_nonneg _ _ (by linarith)]; exact min_le_min h18 le_rfl
      nlinarith
    have hpos : 0 < min r1 (δ * ℓ) + 1 := by have : 0 ≤ min r1 (δ * ℓ) := le_min hr1' (by nlinarith); linarith
    have hpos2 : 0 < min r8 ℓ + 1 := by have : 0 ≤ min r8 ℓ := le_min hr8' (by linarith); linarith
    have hpow := pow_le_pow_left₀ hpos.le hm k
    rw [mul_pow] at hpow
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ (pow_pos hpos2 k) (pow_pos hpos k)]
    nlinarith
  calc ∑ α ∈ D, ((min ((zdistInf (k + 2) L (x - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
      ≤ ∑ α ∈ D, δ ^ k * ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) (δ * ℓ) + 1) ^ k)⁻¹ := Finset.sum_le_sum hterm
    _ = δ ^ k * ∑ α ∈ D, ((min ((zdistD (k + 2) L (x - α) : ℕ) : ℝ) (δ * ℓ) + 1) ^ k)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ δ ^ k * (ballC k * (δ * ℓ) ^ 2) := mul_le_mul_of_nonneg_left (sum_ball_min_pow_le (L := L) k hℓ' D c x hD') (by positivity)
    _ = δ ^ (k + 2) * (ballC k * ℓ ^ 2) := by ring

/-- the triangle inequality `|x - y|_∞ ≤ |x - α|_∞ + |y - α|_∞` in the form needed for `s ≤ p + q`. -/
private theorem lwMEI_tri {d L : ℕ} [NeZero L] (x y α : Zd d L) :
    ((zdistInf d L (x - y) : ℕ) : ℝ) ≤ ((zdistInf d L (x - α) : ℕ) : ℝ) + ((zdistInf d L (y - α) : ℕ) : ℝ) := by
  have h := anpKey_zdistInf_tri x α y
  rw [anpKey_zdistInf_sub_comm α y] at h
  exact_mod_cast h

/-- **The pointwise bound for two factors in real variables** (`(eq:TtTt)`, `(eq:KtKt)` and the case coverage of Appendix A.4
in one statement; the `zdistInf` twin of `sfT_pair_le`, `Kernel/PropT.lean:788`, with `s ≤ p + q` as a hypothesis):
`𝖳(p ∧ ℓ) 𝖳(q ∧ ℓ) ≤ 2^{(d-2)/2} 𝖳(s ∧ ℓ) Ψ_t (p ∧ q ∧ ℓ + 1)^{-(d-2)/2}`. -/
private theorem lwMEI_pair_le {d L : ℕ} {W g t : ℝ} (hW : 0 < W) {ℓ p q s : ℝ} (hℓ : 0 ≤ ℓ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hs : 0 ≤ s) (hspq : s ≤ p + q) :
    sfT d L W g t (min p ℓ) * sfT d L W g t (min q ℓ) ≤
      √((2 : ℝ) ^ (d - 2)) * (sfT d L W g t (min s ℓ) * (PsiT d L W g t * wfac d (min (min p ℓ) (min q ℓ)))) := by
  have hone : (1 : ℝ) ≤ √((2 : ℝ) ^ (d - 2)) := by
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (one_le_pow₀ one_le_two)
  have hTℓ : sfT d L W g t ℓ ≤ sfT d L W g t (min s ℓ) := sfT_antitone (le_min hs hℓ) (min_le_right _ _)
  have hfin : ∀ u : ℝ, sfT d L W g t ℓ * (PsiT d L W g t * wfac d u) ≤
      √((2 : ℝ) ^ (d - 2)) * (sfT d L W g t (min s ℓ) * (PsiT d L W g t * wfac d u)) := fun u => by
    have h0 : 0 ≤ PsiT d L W g t * wfac d u := mul_nonneg PsiT_nonneg (wfac_nonneg _ _)
    calc sfT d L W g t ℓ * (PsiT d L W g t * wfac d u)
        ≤ sfT d L W g t (min s ℓ) * (PsiT d L W g t * wfac d u) := mul_le_mul_of_nonneg_right hTℓ h0
      _ ≤ _ := le_mul_of_one_le_left (mul_nonneg (sfT_nonneg _) h0) hone
  rcases le_total q ℓ with hqℓ | hqℓ
  · have h2 : min q ℓ = q := min_eq_left hqℓ
    rcases le_total p ℓ with hpℓ | hpℓ
    · rw [min_eq_left hpℓ, h2]
      exact sfT_mul_le_TtTt hW hp hq (le_min hs hℓ) ((min_le_left _ _).trans hspq)
    · rw [min_eq_right hpℓ, h2, min_eq_right hqℓ, mul_comm (sfT d L W g t ℓ) (sfT d L W g t q)]
      exact (sfT_mul_le_KtKt hW hq).trans (hfin q)
  · rw [min_eq_right hqℓ, min_eq_left (min_le_right p ℓ)]
    exact (sfT_mul_le_KtKt hW (le_min hp hℓ)).trans (hfin _)

/-- The constant of the `ℓ^∞` summed bound, `d = k + 2` and `n` pairs (`keyC` of `Kernel/PropT.lean:897` with the ball constant
`4 d^{k+2} ballC_k` of `sum_ball_inf_min_pow_le`). -/
def lwMEI_keyC (k n : ℕ) : ℝ := (√((2 : ℝ) ^ k)) ^ n * (4 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * ballC k))

private theorem lwMEI_keyC_pos (k n : ℕ) : 0 < lwMEI_keyC k n := by
  unfold lwMEI_keyC
  have := ballC_pos k
  positivity

/-- The product of the `n` pointwise bounds (the `zdistInf` twin of `prod_sfT_pair_le`, `Kernel/PropT.lean:839`). -/
private theorem lwMEI_prod_pair {d L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {n : ℕ}
    (x y : Fin n → Zd d L) (α : Zd d L) :
    ∏ i, (sfT d L W g t (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
          * sfT d L W g t (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ))
      ≤ (√((2 : ℝ) ^ (d - 2)) * PsiT d L W g t) ^ n
        * ((∏ i, sfT d L W g t (min ((zdistInf d L (x i - y i) : ℕ) : ℝ) ℓ))
          * ∏ i, wfac d (min (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
                             (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ))) := by
  have hstep : ∀ i : Fin n,
      sfT d L W g t (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
          * sfT d L W g t (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ)
        ≤ (√((2 : ℝ) ^ (d - 2)) * PsiT d L W g t)
          * (sfT d L W g t (min ((zdistInf d L (x i - y i) : ℕ) : ℝ) ℓ)
            * wfac d (min (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
                          (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ))) := by
    intro i
    calc _ ≤ √((2 : ℝ) ^ (d - 2))
          * (sfT d L W g t (min ((zdistInf d L (x i - y i) : ℕ) : ℝ) ℓ)
            * (PsiT d L W g t
              * wfac d (min (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
                            (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ)))) :=
          lwMEI_pair_le hW hℓ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (lwMEI_tri (x i) (y i) α)
      _ = _ := by ring
  calc _ ≤ ∏ i, ((√((2 : ℝ) ^ (d - 2)) * PsiT d L W g t)
          * (sfT d L W g t (min ((zdistInf d L (x i - y i) : ℕ) : ℝ) ℓ)
            * wfac d (min (min ((zdistInf d L (x i - α) : ℕ) : ℝ) ℓ)
                          (min ((zdistInf d L (y i - α) : ℕ) : ℝ) ℓ)))) :=
        Finset.prod_le_prod₀ (fun i _ => mul_nonneg (sfT_nonneg _) (sfT_nonneg _)) (fun i _ => hstep i)
    _ = _ := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]

/-- **`(eq:key_T_reudce)` in `ℓ^∞`** (`claim:TTk`, the summed version; the twin of `key_T_reduce`, `Kernel/PropT.lean:913`):
for `d = k + 2`, `n ≥ 2` pairs and any set `D` of internal vertices inside the `ℓ^∞` ball of radius `ℓ ≥ 1` around `a`,
`Σ_{α ∈ D} Π_i 𝖳(|x_i-α|_∞ ∧ ℓ) 𝖳(|y_i-α|_∞ ∧ ℓ) ≤ C Ψ_t² ℓ² Ψ_t^{n-2} Π_i 𝖳(|x_i-y_i|_∞ ∧ ℓ)`. -/
private theorem lwMEI_key {L : ℕ} [NeZero L] {W g t : ℝ} (hW : 0 < W) {k n : ℕ} (hn : 2 ≤ n) {ℓ : ℝ} (hℓ : 1 ≤ ℓ)
    (D : Finset (Zd (k + 2) L)) (a : Zd (k + 2) L)
    (hD : ∀ α ∈ D, ((zdistInf (k + 2) L (a - α) : ℕ) : ℝ) ≤ ℓ) (x y : Fin n → Zd (k + 2) L) :
    ∑ α ∈ D, ∏ i, (sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - α) : ℕ) : ℝ) ℓ)
          * sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (y i - α) : ℕ) : ℝ) ℓ))
      ≤ lwMEI_keyC k n * (PsiT (k + 2) L W g t ^ 2 * ℓ ^ 2)
        * (PsiT (k + 2) L W g t ^ (n - 2)
          * ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ)) := by
  have hℓ0 : (0 : ℝ) ≤ ℓ := by linarith
  have hi₀ : (0 : ℕ) < n := by omega
  have hi₁ : (1 : ℕ) < n := by omega
  set i₀ : Fin n := ⟨0, hi₀⟩ with hi₀def
  set i₁ : Fin n := ⟨1, hi₁⟩ with hi₁def
  set w : Zd (k + 2) L → Fin n → ℝ := fun α i =>
    wfac (k + 2) (min (min ((zdistInf (k + 2) L (x i - α) : ℕ) : ℝ) ℓ)
                      (min ((zdistInf (k + 2) L (y i - α) : ℕ) : ℝ) ℓ)) with hw
  have hw0 : ∀ α i, 0 ≤ w α i := fun _ _ => wfac_nonneg _ _
  have hwsq : ∀ (α : Zd (k + 2) L) (i : Fin n), w α i ^ 2
      ≤ ((min ((zdistInf (k + 2) L (x i - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
        + ((min ((zdistInf (k + 2) L (y i - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹ := by
    intro α i
    have h := wfac_min_sq_le (k + 2)
      (p := min ((zdistInf (k + 2) L (x i - α) : ℕ) : ℝ) ℓ)
      (q := min ((zdistInf (k + 2) L (y i - α) : ℕ) : ℝ) ℓ)
      (le_min (Nat.cast_nonneg _) hℓ0) (le_min (Nat.cast_nonneg _) hℓ0)
    simpa [hw] using h
  have hprod : ∀ α ∈ D, ∏ i, w α i
      ≤ (((min ((zdistInf (k + 2) L (x i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
          + ((min ((zdistInf (k + 2) L (y i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹)
        + (((min ((zdistInf (k + 2) L (x i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
          + ((min ((zdistInf (k + 2) L (y i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹) := by
    intro α _
    have h1 : ∏ i, w α i ≤ w α i₀ * w α i₁ :=
      prod_wfac_le_two hn (w α) (hw0 α) (fun i => wfac_le_one _
        (le_min (le_min (Nat.cast_nonneg _) hℓ0) (le_min (Nat.cast_nonneg _) hℓ0)))
    have h2 := two_mul_le_add_sq (w α i₀) (w α i₁)
    have h3 := hwsq α i₀
    have h4 := hwsq α i₁
    linarith [sq_nonneg (w α i₀), sq_nonneg (w α i₁)]
  have hsum : ∑ α ∈ D, ∏ i, w α i ≤ 4 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * ballC k) * ℓ ^ 2 := by
    have hb := fun z : Zd (k + 2) L => sum_ball_inf_min_pow_le (L := L) k hℓ D a z hD
    calc ∑ α ∈ D, ∏ i, w α i
        ≤ ∑ α ∈ D, ((((min ((zdistInf (k + 2) L (x i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
            + ((min ((zdistInf (k + 2) L (y i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹)
          + (((min ((zdistInf (k + 2) L (x i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
            + ((min ((zdistInf (k + 2) L (y i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹)) :=
          Finset.sum_le_sum hprod
      _ = ((∑ α ∈ D, ((min ((zdistInf (k + 2) L (x i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
            + ∑ α ∈ D, ((min ((zdistInf (k + 2) L (y i₀ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹)
          + (∑ α ∈ D, ((min ((zdistInf (k + 2) L (x i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹
            + ∑ α ∈ D, ((min ((zdistInf (k + 2) L (y i₁ - α) : ℕ) : ℝ) ℓ + 1) ^ k)⁻¹)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ 4 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * ballC k) * ℓ ^ 2 := by
          have b1 := hb (x i₀)
          have b2 := hb (y i₀)
          have b3 := hb (x i₁)
          have b4 := hb (y i₁)
          linarith
  have hC : (0 : ℝ) ≤ (√((2 : ℝ) ^ k) * PsiT (k + 2) L W g t) ^ n := by
    have : (0 : ℝ) ≤ √((2 : ℝ) ^ k) * PsiT (k + 2) L W g t :=
      mul_nonneg (Real.sqrt_nonneg _) PsiT_nonneg
    positivity
  have hS : (0 : ℝ) ≤ ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ) :=
    Finset.prod_nonneg fun i _ => sfT_nonneg _
  have hpow : PsiT (k + 2) L W g t ^ n
      = PsiT (k + 2) L W g t ^ 2 * PsiT (k + 2) L W g t ^ (n - 2) := by
    rw [← pow_add]; congr 1; omega
  calc ∑ α ∈ D, ∏ i, (sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - α) : ℕ) : ℝ) ℓ)
        * sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (y i - α) : ℕ) : ℝ) ℓ))
      ≤ ∑ α ∈ D, (√((2 : ℝ) ^ k) * PsiT (k + 2) L W g t) ^ n
          * ((∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ))
            * ∏ i, w α i) := by
        refine Finset.sum_le_sum fun α _ => ?_
        have h := lwMEI_prod_pair (d := k + 2) (L := L) (W := W) (g := g) (t := t) hW hℓ0 x y α
        simpa [hw] using h
    _ = (√((2 : ℝ) ^ k) * PsiT (k + 2) L W g t) ^ n
          * ((∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ))
            * ∑ α ∈ D, ∏ i, w α i) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (√((2 : ℝ) ^ k) * PsiT (k + 2) L W g t) ^ n
          * ((∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ))
            * (4 * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * ballC k) * ℓ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hS) hC
    _ = lwMEI_keyC k n * (PsiT (k + 2) L W g t ^ 2 * ℓ ^ 2)
          * (PsiT (k + 2) L W g t ^ (n - 2)
            * ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ)) := by
        rw [lwMEI_keyC, mul_pow, hpow]
        ring

/-- **`claim:TTk` in `ℓ^∞`** (`7_8:1662-1664`): the pin `EKTTkInf d n` for every `d`, `n`.  The constant is `3 · lwMEI_keyC`
(`key_T_reduce_absorbed`, `Kernel/PropT.lean:1056`, with `PsiT_sq_mul_le`, `:1021`, `Bparam_mul_ellT_sq_le`). -/
theorem ekTTkInf_holds (d n : ℕ) : EKTTkInf d n := by
  intro hd hn
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  refine ⟨3 * lwMEI_keyC k n, by have := lwMEI_keyC_pos k n; positivity, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt D a hD x y
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hkeyC : 0 ≤ lwMEI_keyC k n := (lwMEI_keyC_pos k n).le
  have hrest : 0 ≤ PsiT (k + 2) L W g t ^ (n - 2)
      * ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ) :=
    mul_nonneg (pow_nonneg PsiT_nonneg _) (Finset.prod_nonneg fun i _ => sfT_nonneg _)
  refine (lwMEI_key hW hn hℓ D a hD x y).trans ?_
  have habs := PsiT_sq_mul_le (d := k + 2) (L := L) (W := W) (g := g) (t := t) (by omega) hW hL1 hg ht hgL
    (by linarith) hℓt
  calc lwMEI_keyC k n * (PsiT (k + 2) L W g t ^ 2 * ℓ ^ 2) * (PsiT (k + 2) L W g t ^ (n - 2) *
          ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ))
      ≤ lwMEI_keyC k n * (3 * Λ ^ 2 * ((W ^ (k + 2))⁻¹ / (1 - t))) * (PsiT (k + 2) L W g t ^ (n - 2) *
          ∏ i, sfT (k + 2) L W g t (min ((zdistInf (k + 2) L (x i - y i) : ℕ) : ℝ) ℓ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hkeyC) hrest
    _ = _ := by ring

/-! ## 3. The near chain in `ℓ^∞`

The generic chain of `Graph/LWMomExp.lean` (`lwMomExp_step_aux`, `lwMomExp_sys_bound`: no `zdist` occurs in
`Graph/LWMomExp.lean:304-516`) is used as it is (the 11 keywords are public).  Copied and adapted here
(`zdistD ↦ zdistInf`): the kernel block (`LWMomExp.lean:521-581`), `TTkBody` to `sys_near` (`:584-699`), `near_graph` with
its two helpers (`:918-1024`).  The domain is any `D` in an `ℓ^∞` ball of radius `ℓ` around a centre `c`. -/

/-- `𝖳_t(|u - v|_∞ ∧ ℓ)` (`7_8:1650`; the twin of `lwMomExp_tau`, `Graph/LWMomExp.lean:521`). -/
def lwMEI_tau (d L : ℕ) (W g t ℓ : ℝ) (u v : Zd d L) : ℝ :=
  sfT d L W g t (min ((zdistInf d L (u - v) : ℕ) : ℝ) ℓ)

private theorem lwMEI_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

section Tau

variable {d L : ℕ} [NeZero L] {W g t ℓ : ℝ}

private theorem lwMEI_tau_nonneg (u v : Zd d L) : 0 ≤ lwMEI_tau d L W g t ℓ u v := sfT_nonneg _

private theorem lwMEI_tau_symm (u v : Zd d L) :
    lwMEI_tau d L W g t ℓ u v = lwMEI_tau d L W g t ℓ v u := by
  unfold lwMEI_tau
  rw [anpKey_zdistInf_sub_comm u v]

private theorem lwMEI_tau_self (hℓ : 0 ≤ ℓ) (c : Zd d L) :
    lwMEI_tau d L W g t ℓ c c = sfT d L W g t 0 := by
  unfold lwMEI_tau
  rw [sub_self, lwMEI_zdistInf_zero, Nat.cast_zero, min_eq_left hℓ]

private theorem lwMEI_tau_le (hℓ : 0 ≤ ℓ) (u v : Zd d L) : lwMEI_tau d L W g t ℓ u v ≤ sfT d L W g t 0 :=
  sfT_antitone le_rfl (le_min (Nat.cast_nonneg _) hℓ)

private theorem lwMEI_psi_pos (hW : 0 < W) (ht : t < 1) : 0 < PsiT d L W g t := by
  unfold PsiT
  apply Real.sqrt_pos.2
  have h1t : 0 < |1 - t| := abs_pos.2 (by linarith)
  have hB : 0 < Bparam d L g t 0 := by
    unfold Bparam
    have hg2 : 0 < g ^ 2 + |1 - t| := by nlinarith [sq_nonneg g]
    have : 0 < (g ^ 2 + |1 - t|)⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by
      apply mul_pos (inv_pos.2 hg2)
      simp
    have h2 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
    linarith
  exact mul_pos (inv_pos.2 (pow_pos hW _)) hB

end Tau

/-- The `claim:TTk` body of the pin `EKTTkInf d n` at the constant `C`. -/
private def lwMEI_TTkBody (d n : ℕ) (C : ℝ) : Prop :=
  ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
    ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t →
    ∀ (D : Finset (Zd d L)) (c : Zd d L), (∀ α ∈ D, (zdistInf d L (c - α) : ℝ) ≤ ℓ) →
    ∀ x y : Fin n → Zd d L,
      ∑ α ∈ D, ∏ i, (sfT d L W g t (min (zdistInf d L (x i - α) : ℝ) ℓ)
            * sfT d L W g t (min (zdistInf d L (y i - α) : ℝ) ℓ))
        ≤ C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
            (PsiT d L W g t ^ (n - 2) *
              ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))

private theorem lwMEI_TTkBody_mono {d n : ℕ} {C C' : ℝ} (h : lwMEI_TTkBody d n C)
    (hCC : C ≤ C') : lwMEI_TTkBody d n C' := by
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt D c hD x y
  refine (h L W g t hW hg ht hgL ℓ Λ hℓ hℓt D c hD x y).trans ?_
  have h1t : 0 < 1 - t := by linarith
  have hX : 0 ≤ (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
      (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ)) := by
    have : 0 ≤ PsiT d L W g t := PsiT_nonneg
    have : 0 ≤ ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ) :=
      Finset.prod_nonneg fun i _ => sfT_nonneg _
    positivity
  calc C * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))
      = C * ((Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))) := by ring
    _ ≤ C' * ((Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) *
        (PsiT d L W g t ^ (n - 2) * ∏ i, sfT d L W g t (min (zdistInf d L (x i - y i) : ℝ) ℓ))) :=
        mul_le_mul_of_nonneg_right hCC hX
    _ = _ := by ring

/-- One constant for all `claim:TTk` with `2 ≤ k ≤ N` pairs. -/
private theorem lwMEI_exists_K (d : ℕ) (hd : 3 ≤ d) (N : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ k, 2 ≤ k → k ≤ N → lwMEI_TTkBody d k K := by
  induction N with
  | zero => exact ⟨1, one_pos, fun k hk hkN => by omega⟩
  | succ N ih =>
    obtain ⟨K, hK, hKk⟩ := ih
    by_cases h2 : 2 ≤ N + 1
    · obtain ⟨C, hC, hCb⟩ := ekTTkInf_holds d (N + 1) hd h2
      refine ⟨max K C, lt_max_of_lt_left hK, fun k hk hkN => ?_⟩
      by_cases hkN' : k ≤ N
      · exact lwMEI_TTkBody_mono (hKk k hk hkN') (le_max_left _ _)
      · have : k = N + 1 := by omega
        subst this
        exact lwMEI_TTkBody_mono hCb (le_max_right _ _)
    · exact ⟨K, hK, fun k hk hkN => hKk k hk (by omega)⟩

/-- The `claim:TTk` bound for `k` pairs, for the kernel `τ`, on a domain `D` in an `ℓ^∞` ball. -/
private theorem lwMEI_hstep {d N : ℕ} {K : ℝ} (hK : ∀ k, 2 ≤ k → k ≤ N → lwMEI_TTkBody d k K)
    (L : ℕ) [NeZero L] (W g t : ℝ) (hW : 0 < W) (hg : 0 ≤ g) (ht : t < 1)
    (hgL : g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t)) (ℓ Λ : ℝ) (hℓ : 1 ≤ ℓ) (hℓt : ℓ ≤ Λ * ellT L g t)
    (D : Finset (Zd d L)) (c : Zd d L) (hD : ∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) :
    ∀ k, 2 ≤ k → k ≤ N → ∀ x y : Fin k → Zd d L,
      ∑ α ∈ D, ∏ i, (lwMEI_tau d L W g t ℓ (x i) α * lwMEI_tau d L W g t ℓ α (y i)) ≤
      K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) * (PsiT d L W g t ^ (k - 2) *
        ∏ i, lwMEI_tau d L W g t ℓ (x i) (y i)) := by
  intro k hk hkN x y
  have h := hK k hk hkN L W g t hW hg ht hgL ℓ Λ hℓ hℓt D c hD x y
  calc _ = ∑ α ∈ D, ∏ i, (lwMEI_tau d L W g t ℓ (x i) α * lwMEI_tau d L W g t ℓ (y i) α) :=
        Finset.sum_congr rfl fun α _ => Finset.prod_congr rfl fun i _ => by
          rw [lwMEI_tau_symm α (y i)]
    _ ≤ _ := h

/-- The bound for a path system (every internal vertex on two distinct paths), the kernel `τ` in `ℓ^∞` (twin of
`lwMomExp_sys_near`, `Graph/LWMomExp.lean:682`). -/
private theorem lwMEI_sys_near (d N : ℕ) (hd : 3 ≤ d) : ∃ K : ℝ, 0 < K ∧
    ∀ (L : ℕ) [NeZero L] (W g t : ℝ), 0 < W → 0 ≤ g → t < 1 → g ^ 2 ≤ (L : ℝ) ^ 2 * (1 - t) →
      ∀ ℓ Λ : ℝ, 1 ≤ ℓ → ℓ ≤ Λ * ellT L g t → ∀ (D : Finset (Zd d L)) (c a b : Zd d L),
      (∀ α ∈ D, ((zdistInf d L (c - α) : ℕ) : ℝ) ≤ ℓ) →
      ∀ (q p : ℕ) (m : Fin p → List (NV p q)), ∑ i, ((m i).length + 1) ≤ N →
        (∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ m i ∧ Sum.inr j ∈ m i') →
        lwMomExp_sysVal (lwMEI_tau d L W g t ℓ) D a b m ≤
          (K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
            PsiT d L W g t ^ (((∑ i, ((m i).length + 1) : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
            (lwMEI_tau d L W g t ℓ a b) ^ p := by
  obtain ⟨K, hK, hKk⟩ := lwMEI_exists_K d hd N
  refine ⟨K, hK, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt D c a b hD
  have h1t : 0 < 1 - t := by linarith
  have hZ : 0 ≤ Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by positivity
  exact lwMomExp_sys_bound (lwMEI_tau d L W g t ℓ) (sfT d L W g t 0) (PsiT d L W g t) K _ N D a b
    lwMEI_tau_nonneg lwMEI_tau_symm (lwMEI_tau_le (by linarith))
    (lwMEI_tau_self (by linarith)) (sfT_zero_le_PsiT hW) (lwMEI_psi_pos hW ht)
    (mul_nonneg hK.le hZ) (lwMEI_hstep hKk L W g t hW hg ht hgL ℓ Λ hℓ hℓt D c hD)

section NearGraph

variable {p q : ℕ}

private theorem lwMEI_nSolid (Γ : NGraph p q) (hNG : Γ.NoGhost) : Γ.nSolid = Γ.es.length := by
  unfold NGraph.nSolid
  rw [List.filter_eq_self.2]
  intro e he
  simp [hNG e he]

private theorem lwMEI_ordN (Γ : NGraph p q) (hNG : Γ.NoGhost) :
    Γ.ordN = (Γ.es.length : ℤ) - 2 * (q : ℤ) := by
  unfold NGraph.ordN ord
  rw [lwMEI_nSolid Γ hNG]
  simp
  ring

/-- **`lem:LW_moment_exp`, near bound in `ℓ^∞`, for one nested graph** (twin of `lwMomExp_near_graph`,
`Graph/LWMomExp.lean:932`, with the domain `D` in an `ℓ^∞` ball of radius `ℓ` around `c`). -/
private theorem lwMEI_near_graph (d : ℕ) (hd : 3 ≤ d) (Γ : NGraph p q) (hNG : Γ.NoGhost) (hN : Γ.IsNested) :
    AnpNearInfAt d Γ := by
  obtain ⟨K, hK, hKb⟩ := lwMEI_sys_near d (∑ i, (Γ.path i).length) hd
  refine ⟨K ^ q, pow_pos hK q, ?_⟩
  intro L _ W g t hW hg ht hgL ℓ Λ hℓ hℓt ξ hξ hξτ c a b D hD
  have h1t : 0 < 1 - t := by linarith
  have hsum : ∑ i, ((lwMomExp_sysOf Γ i).length + 1) = ∑ i, (Γ.path i).length :=
    Finset.sum_congr rfl fun i _ => lwMomExp_sysOf_length Γ hN i
  have hA : ∀ j : Fin q, ∃ i i', i ≠ i' ∧ Sum.inr j ∈ lwMomExp_sysOf Γ i ∧
      Sum.inr j ∈ lwMomExp_sysOf Γ i' := by
    intro j
    obtain ⟨i, i', hne, hv, hv'⟩ := hN.2.2.2.2.1 j
    exact ⟨i, i', hne, lwMomExp_sysOf_mem Γ hN i j hv, lwMomExp_sysOf_mem Γ hN i' j hv'⟩
  have hsys := hKb L W g t hW hg ht hgL ℓ Λ hℓ hℓt D c a b hD q p (lwMomExp_sysOf Γ) hsum.le hA
  rw [hsum] at hsys
  set T0 : ℝ := sfT d L W g t 0 with hT0
  have hT00 : 0 ≤ T0 := sfT_nonneg _
  have hΨ : T0 ≤ PsiT d L W g t := sfT_zero_le_PsiT hW
  have hΨ0 : 0 < PsiT d L W g t := lwMEI_psi_pos hW ht
  set c' : ℕ := (lwMomExp_pathEdges Γ)ᶜ.card with hc'
  have hpt : ∀ ℓ' : Fin q → Zd d L,
      ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤
        T0 ^ c' * ∏ i, lwMomExp_chain (lwMEI_tau d L W g t ℓ) a
          ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b := by
    intro ℓ'
    set g' : Fin Γ.es.length → ℝ := fun k =>
      lwMEI_tau d L W g t ℓ (lwMomExp_lab a b ℓ' (Γ.es.get k).u)
        (lwMomExp_lab a b ℓ' (Γ.es.get k).v) with hg'
    have hw : ∀ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤ g' k := by
      intro k
      have hgh : (Γ.es.get k).ghost = false := hNG _ (List.get_mem _ k)
      unfold anpKey6_w
      rw [hgh]
      exact hξτ _ _
    calc ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k ≤ ∏ k, g' k :=
          Finset.prod_le_prod₀ (fun k _ => anpKey6_w_nonneg Γ ξ (fun α β => (hξ α β).1) _ _ _ _)
            (fun k _ => hw k)
      _ = (∏ i, ((Γ.path i).map fun st => g' st.1).prod) *
            ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, g' k := lwMomExp_prod_split Γ hN g'
      _ ≤ (∏ i, lwMomExp_chain (lwMEI_tau d L W g t ℓ) a
            ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b) * T0 ^ c' := by
          refine mul_le_mul (le_of_eq ?_) ?_ (Finset.prod_nonneg fun k _ => lwMEI_tau_nonneg _ _)
            (Finset.prod_nonneg fun i _ => lwMomExp_chain_nonneg _ lwMEI_tau_nonneg _ _ _)
          · refine Finset.prod_congr rfl fun i _ => ?_
            exact lwMomExp_walk_chain Γ (lwMEI_tau d L W g t ℓ) lwMEI_tau_symm
              (lwMomExp_lab a b ℓ') (Γ.path i) _ _ (lwMomExp_path_ne Γ hN i) (hN.2.1 i)
          · calc ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, g' k ≤ ∏ k ∈ (lwMomExp_pathEdges Γ)ᶜ, T0 :=
                  Finset.prod_le_prod₀ (fun k _ => lwMEI_tau_nonneg _ _)
                    (fun k _ => lwMEI_tau_le (by linarith) _ _)
              _ = T0 ^ c' := Finset.prod_const _
      _ = _ := mul_comm _ _
  have hcard : (lwMomExp_pathEdges Γ).card + c' = Γ.es.length := by
    rw [hc', Finset.card_add_card_compl, Fintype.card_fin]
  have hexp : ((c' : ℤ)) + (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) =
      Γ.ordN - (p : ℤ) := by
    have hpc := lwMomExp_pathEdges_card Γ hN
    have h3 : (Γ.es.length : ℤ) = (c' : ℤ) + ((∑ i, (Γ.path i).length : ℕ) : ℤ) := by
      exact_mod_cast (by omega : Γ.es.length = c' + ∑ i, (Γ.path i).length)
    rw [lwMEI_ordN Γ hNG]
    linarith
  unfold lwMomExp_valOnD
  calc ∑ ℓ' ∈ Fintype.piFinset (fun _ : Fin q => D),
        ∏ k, anpKey6_w Γ ξ (fun _ => a) (fun _ => b) ℓ' k
      ≤ ∑ ℓ' ∈ Fintype.piFinset (fun _ : Fin q => D),
        T0 ^ c' * ∏ i, lwMomExp_chain (lwMEI_tau d L W g t ℓ) a
          ((lwMomExp_sysOf Γ i).map (lwMomExp_lab a b ℓ')) b :=
        Finset.sum_le_sum fun ℓ' _ => hpt ℓ'
    _ = T0 ^ c' * lwMomExp_sysVal (lwMEI_tau d L W g t ℓ) D a b (lwMomExp_sysOf Γ) := by
        rw [← Finset.mul_sum]; rfl
    _ ≤ T0 ^ c' * ((K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
          PsiT d L W g t ^ (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
          (lwMEI_tau d L W g t ℓ a b) ^ p) :=
        mul_le_mul_of_nonneg_left hsys (pow_nonneg hT00 _)
    _ ≤ PsiT d L W g t ^ c' * ((K * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)))) ^ q *
          PsiT d L W g t ^ (((∑ i, (Γ.path i).length : ℕ) : ℤ) - 2 * (q : ℤ) - (p : ℤ)) *
          (lwMEI_tau d L W g t ℓ a b) ^ p) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT00 hΨ c') ?_
        have : 0 ≤ Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t)) := by positivity
        have := lwMEI_tau_nonneg (d := d) (L := L) (W := W) (g := g) (t := t) (ℓ := ℓ) a b
        positivity
    _ = K ^ q * (Λ ^ 2 * ((W ^ d)⁻¹ / (1 - t))) ^ q *
          PsiT d L W g t ^ (Γ.ordN - (p : ℤ)) *
          sfT d L W g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ) ^ p := by
        rw [← hexp, zpow_add₀ hΨ0.ne', zpow_natCast, mul_pow]
        unfold lwMEI_tau
        ring

/-- **`lem:LW_moment_exp`, the deterministic near bound `(adsuu_exp2)` in `ℓ^∞`** for every nested graph without ghost edges
and every `d ≥ 3`. -/
theorem lwMomExp_nearInf : ∀ d, AnpNearInf d :=
  fun d hd _ _ Γ hNG hN => lwMEI_near_graph d hd Γ hNG hN

end NearGraph

/-! ## 4. Compiled nonempty instances at `d = 3`

Every deterministic hypothesis is discharged at the data; nothing is left as a hypothesis.
* `ekTTkInf_holds 3 2`: `L = ℓ = Λ = 5`, `W = 25`, `g = 1/2`, `t = 9/10` (`g² = 1/4 ≤ L²(1 - t) = 5/2`), `D = univ` (the 125
  points of `Z_5^3`, all within `ℓ^∞`-distance `5` of the centre `0`), `x = (0, e₀)`, `y = (e₁, e₂)`.
* `lwMomExp_nearInf` at `figAux` (`p = q = 2`, six solid edges): `L = 6`, `W = 2`, `g = t = 1/2`, `ℓ = Λ = 2`, centre `c = a = 0`,
  `b = e₀`, `D` the `ℓ^∞` ball of radius `2` around `0` (nonempty), `ξ = 𝖳_t(|·-·|_∞ ∧ ℓ)` itself. -/

namespace LWMomExpInfInst


private theorem lwMEI_zdistInf_le {d : ℕ} (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

/-- The `ℓ^∞` ball sum at `d = 3` (`k = 1`), `L = ℓ = 5`, `D = univ`, `x = c = 0`. -/
example : ∑ α : Zd (1 + 2) 5, ((min ((zdistInf (1 + 2) 5 (0 - α) : ℕ) : ℝ) 5 + 1) ^ 1)⁻¹ ≤
    ((1 + 2 : ℕ) : ℝ) ^ (1 + 2) * (ballC 1 * 5 ^ 2) :=
  sum_ball_inf_min_pow_le 1 (by norm_num) Finset.univ 0 0 fun α _ => by
    exact_mod_cast lwMEI_zdistInf_le (d := 1 + 2) 5 (0 - α)

/-- **Instance of `ekTTkInf_holds`** (`d = 3`, `n = 2`): the inequality of `claim:TTk` in `ℓ^∞` at the data above. -/
theorem inst_ekTTkInf : ∃ C : ℝ, 0 < C ∧
    ∑ α : Zd 3 5, ∏ i : Fin 2,
        (sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistInf 3 5 ((![0, Pi.single 0 1] : Fin 2 → Zd 3 5) i - α) : ℝ) 5) *
          sfT 3 5 25 (1 / 2) (9 / 10) (min (zdistInf 3 5 ((![Pi.single 1 1, Pi.single 2 1] : Fin 2 → Zd 3 5) i - α) : ℝ) 5)) ≤
      C * ((5 : ℝ) ^ 2 * (((25 : ℝ) ^ 3)⁻¹ / (1 - 9 / 10))) *
        (PsiT 3 5 25 (1 / 2) (9 / 10) ^ (2 - 2) * ∏ i : Fin 2, sfT 3 5 25 (1 / 2) (9 / 10)
          (min (zdistInf 3 5 ((![0, Pi.single 0 1] : Fin 2 → Zd 3 5) i - (![Pi.single 1 1, Pi.single 2 1] : Fin 2 → Zd 3 5) i) : ℝ) 5)) := by
  obtain ⟨C, hC, H⟩ := ekTTkInf_holds 3 2 le_rfl le_rfl
  refine ⟨C, hC, H 5 25 (1 / 2) (9 / 10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 5 5 (by norm_num) ?_
    Finset.univ 0 (fun α _ => by exact_mod_cast lwMEI_zdistInf_le (d := 3) 5 (0 - α)) _ _⟩
  have := one_le_ellT (L := 5) (g := 1 / 2) (t := 9 / 10) (by norm_num)
  linarith

/-- Instance 1: the near pin in `ℓ^∞` at `figAux`, from `lwMomExp_nearInf`. -/
theorem inst_near : AnpNearInfAt 3 figAux :=
  lwMomExp_nearInf 3 le_rfl 2 2 figAux figAux_nested.2 figAux_nested.1

/-- Instance 1 at the data above: the inequality of the pin with `ξ = 𝖳_t(|·-·|_∞ ∧ ℓ)`, `D ≠ ∅`. -/
theorem inst_near_pt : ∃ C : ℝ, 0 < C ∧
    (Finset.univ.filter fun α : Zd 3 6 => ((zdistInf 3 6 (0 - α) : ℕ) : ℝ) ≤ 2).Nonempty ∧
    lwMomExp_valOnD figAux (lwMEI_tau 3 6 2 (1 / 2) (1 / 2) 2) (fun _ => (0 : Zd 3 6))
        (fun _ => (Pi.single 0 1 : Zd 3 6)) (Finset.univ.filter fun α : Zd 3 6 => ((zdistInf 3 6 (0 - α) : ℕ) : ℝ) ≤ 2) ≤
      C * ((2 : ℝ) ^ 2 * (((2 : ℝ) ^ 3)⁻¹ / (1 - 1 / 2))) ^ 2 *
        PsiT 3 6 2 (1 / 2) (1 / 2) ^ (figAux.ordN - ((2 : ℕ) : ℤ)) *
        sfT 3 6 2 (1 / 2) (1 / 2) (min ((zdistInf 3 6 ((0 : Zd 3 6) - Pi.single 0 1) : ℕ) : ℝ) 2) ^ 2 := by
  obtain ⟨C, hC, H⟩ := inst_near
  have hell : (2 : ℝ) ≤ 2 * ellT 6 (1 / 2) (1 / 2) := by
    have := one_le_ellT (L := 6) (g := 1 / 2) (t := 1 / 2) (by norm_num)
    linarith
  refine ⟨C, hC, ⟨0, ?_⟩, ?_⟩
  · simp [lwMEI_zdistInf_zero]
  · exact H 6 2 (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 2 2
      (by norm_num) hell (lwMEI_tau 3 6 2 (1 / 2) (1 / 2) 2)
      (fun α β => ⟨lwMEI_tau_nonneg α β, lwMEI_tau_symm α β⟩) (fun α β => le_rfl) 0 0 (Pi.single 0 1) _
      (fun α hα => (Finset.mem_filter.1 hα).2)

end LWMomExpInfInst

end RBM.Graph

end
