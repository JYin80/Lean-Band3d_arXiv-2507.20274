/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.Bootstrap
import RBM3D.Defs.StochDomAt
import RBM3D.Induction.PerTimeCalc

/-!
# The abstract bootstraps of the GUE phase on the size scale (§7.2 of [YY_25]), `Z_L^d` (T2212)

Port of RBM2D `Universality/GUEPhase/BootstrapAt.lean` at `c9a24cf` (`:1-750`) to `d` dimensions:
the bootstraps of `Universality/GUEPhase/Bootstrap.lean` with `StochDom`, `HighProb`, `UnifDetDom`
and the powers `N^{τ}`, `N^{-D}` of the sequence index replaced by `StochDomAt`, `HighProbAt`,
`UnifDetDomAt` and `(size N)^{τ}`, `(size N)^{-D}`, the matrix dimension along an admissible
sequence `size` (class G of T2173: `P`, `size`, `Nf` abstract; no matrix model).

* `UnifDetDomAt`, `unifDetDom_iff_at_id` (new: `RBM.UnifDetDom` is `UnifDetDomAt` at `size = id`),
  `eventually_size_rpow_le_of_neg`, `stochDomAt_of_forall_highProbAt`;
* `eq736_detDomAt` (`eq736` on the size scale; the only `d`-dependent statement: `Zd d (Lf N)`,
  `primRhsGUE d`, `LoopSet d`, `(W L)^d` in (7.30));
* `eq728GAt` ((7.46)G ⟹ (7.28)) and `eq727GEAt` ((7.45)G at even lengths ⟹ (7.27)).

The pathwise lemmas are copied verbatim from RBM2D `BootstrapAt.lean` (themselves copied from
`Bootstrap.lean`, where they are `private`) under the prefix `BootstrapAt_`; they are
dimension-free.  All statements hold for every `d` (no `3 ≤ d`).  The section `BootstrapAtCheck`
at the end holds compiled nonempty instances of every target.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace RBM.Univ.GUEPhase

open Matrix Finset Filter RBM.Loop

/-! ### Pathwise lemmas (copied from `Bootstrap.lean`, text unchanged) -/

section LBootstrapG

open Set Filter MeasureTheory

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

private theorem BootstrapAt_rhs746G_self (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) :
    rhs746G N η t1 Lm Dm n t1 = (N * η t1)⁻¹ ^ n := by
  simp [rhs746G]

/-- **(7.46)G ⟹ (7.28), pathwise, for `1 ≤ n ≤ n₀`.** -/
private theorem BootstrapAt_eq728_pathG {Lm Dm : ℕ → ℝ → ℝ} {n0 : ℕ} {t0 M M' Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hDc : ∀ m ∈ Set.Icc 1 n0, ContinuousOn (Dm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hL : ∀ j, 2 ≤ j → j ≤ 2 * n0 → ∀ t ∈ Icc t1 t0, Lm j t ≤ M * (N * η t)⁻¹ ^ (j - 1))
    (h746 : ∀ m ∈ Set.Icc 1 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Φ * rhs746G N η t1 Lm Dm m t)
    (hM : 0 ≤ M) (hM' : 0 ≤ M') (hΦ : 0 ≤ Φ)
    (hcond : Φ * (ε * n0 * ((1 + M') * M') + 1 + ε * (M' * M) + Real.sqrt (ε * M)) < M') :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 1 n0, Dm m t < M' * (N * η t)⁻¹ ^ m := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ Set.Icc 1 n0, ContinuousOn (fun t => M' * (N * η t)⁻¹ ^ m) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  have hc1 : 0 ≤ ε * n0 * ((1 + M') * M') := by positivity
  have hc3 : 0 ≤ ε * (M' * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt (ε * M) := Real.sqrt_nonneg _
  refine continuity_argument (Set.finite_Icc 1 n0) hDc hgc (fun m hm => ?_)
    (fun t ht hprev m hm => ?_)
  · have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
    have hD := h746 m hm t1 ht1
    rw [BootstrapAt_rhs746G_self] at hD
    have hpos : 0 < (N * η t1)⁻¹ ^ m := pow_pos (hx0 t1 ht1) _
    change Dm m t1 < M' * (N * η t1)⁻¹ ^ m
    have : Φ < M' := by nlinarith
    nlinarith
  show Dm m t < M' * (N * η t)⁻¹ ^ m
  set x := (N * η t)⁻¹ with hx
  have hxp := hx0 t ht
  have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
  have hηt := hη t ht
  have ht1t : t1 ≤ t := ht.1
  have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
  obtain ⟨hm1, hmn⟩ := hm
  have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
    intro u hu
    have hu0 := hsub hu
    refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
    exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
  have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ 2 * n0 → Lm j u ≤ M * x ^ (j - 1) := by
    intro u hu j h2 hj
    refine (hL j h2 hj u (hsub hu)).trans ?_
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
      Dm j u ≤ M' * x ^ (j - 1 + 1) := by
    intro u hu j h2 hj
    refine ⟨hD0 j u, (hprev u hu j ⟨by omega, hj.trans hmn⟩).trans ?_⟩
    have : j - 1 + 1 = j := by omega
    rw [this]
    gcongr
    · exact (hxu u hu).1
    · exact (hxu u hu).2
  have hD1u : ∀ u ∈ Icc t1 t, Dm 1 u ≤ M' * x := by
    intro u hu
    have h1n0 : (1 : ℕ) ∈ Set.Icc 1 n0 := ⟨le_rfl, by omega⟩
    have hprev1 := hprev u hu 1 h1n0
    calc Dm 1 u ≤ M' * (N * η u)⁻¹ ^ 1 := hprev1
      _ = M' * (N * η u)⁻¹ := by ring
      _ ≤ M' * x := mul_le_mul_of_nonneg_left (hxu u hu).2 hM'
  have hmx : x⁻¹ * x ^ (m + 1) = x ^ m := by
    rw [inv_mul_pow hxp.ne' (by omega)]; rfl
  have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
  have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
  -- line 1
  have hl1 := supOn_line1_le N η t1 (n := m) 1 le_rfl ht1t hM' hxp.le hx1 hxu hDu
  have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
      ≤ ε * n0 * ((1 + M') * M') * x ^ m := by
    calc _ ≤ N * (t - t1) * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_mul_of_nonneg_left hl1 hNt
      _ ≤ ε * x⁻¹ * (m * ((1 + M') * M' * x ^ (m + 1))) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * m * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by ring
      _ ≤ ε * n0 * ((1 + M') * M') * (x⁻¹ * x ^ (m + 1)) := by gcongr
      _ = _ := by rw [hmx]
  -- line 3 (E^{(G)} term `N D₁ L_{n+1}`, the tracked 1-loop)
  have hline3 : N * (t - t1) * supOn (fun u => Dm 1 u * Lm (m + 1) u) t1 t
      ≤ ε * (M' * M) * x ^ m := by
    have hsup : supOn (fun u => Dm 1 u * Lm (m + 1) u) t1 t ≤ M' * M * x ^ (m + 1) := by
      refine supOn_le ht1t fun u hu => ?_
      have h1 : Dm 1 u ≤ M' * x := hD1u u hu
      have h2 : Lm (m + 1) u ≤ M * x ^ m := by simpa using hLu u hu (m + 1) (by omega) (by omega)
      calc Dm 1 u * Lm (m + 1) u ≤ (M' * x) * (M * x ^ m) :=
            mul_le_mul h1 h2 (hL0 (m + 1) u) (by positivity)
        _ = M' * M * x ^ (m + 1) := by rw [pow_succ']; ring
    calc _ ≤ N * (t - t1) * (M' * M * x ^ (m + 1)) := mul_le_mul_of_nonneg_left hsup hNt
      _ ≤ ε * x⁻¹ * (M' * M * x ^ (m + 1)) :=
          mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
      _ = ε * (M' * M) * (x⁻¹ * x ^ (m + 1)) := by ring
      _ = _ := by rw [hmx]
  -- line 4 (unchanged martingale term of (7.46))
  have hline4 : Real.sqrt (t - t1) *
      supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
      ≤ Real.sqrt (ε * M) * x ^ m := by
    have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Real.sqrt (Lm (2 * m) u)) t1 t
        ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * Real.sqrt (M * x ^ (2 * m - 1)) := by
      refine supOn_le ht1t fun u hu => ?_
      have hu0 := hsub hu
      have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
      have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
        gcongr
      have hs2 : Real.sqrt (Lm (2 * m) u) ≤ Real.sqrt (M * x ^ (2 * m - 1)) :=
        Real.sqrt_le_sqrt (hLu u hu (2 * m) (by omega) (by omega))
      exact mul_le_mul hs hs2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
    have hfin :
        Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) = Real.sqrt (ε * M) * x ^ m := by
      rw [← Real.sqrt_mul (by positivity)]
      have : ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x ^ m) ^ 2 := by
        have h2m : 2 * m - 1 + 1 = m * 2 := by omega
        have hxx : x * x ^ (2 * m - 1) = (x ^ m) ^ 2 := by
          rw [← pow_succ', h2m, pow_mul]
        calc ε * x * (M * x ^ (2 * m - 1)) = ε * M * (x * x ^ (2 * m - 1)) := by ring
          _ = ε * M * (x ^ m) ^ 2 := by rw [hxx]
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) *
            Real.sqrt (M * x ^ (2 * m - 1))) :=
          mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
      _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) *
            Real.sqrt (M * x ^ (2 * m - 1)) := by ring
      _ ≤ Real.sqrt (ε * x) * Real.sqrt (M * x ^ (2 * m - 1)) :=
          mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)
      _ = _ := hfin
  have hD := h746 m ⟨hm1, hmn⟩ t ht
  have hrhs : rhs746G N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + M') * M') + 1
      + ε * (M' * M) + Real.sqrt (ε * M)) * x ^ m := by
    unfold rhs746G
    rw [← hx]
    nlinarith
  have hDt := hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
  have hpos : 0 < x ^ m := pow_pos hxp _
  nlinarith

end LBootstrapG

section DominationG

open Set Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The smallness bookkeeping of (7.46)G: with `p = N^{τ'} ≥ 1`, `q = N^{-τ_U}`, `p³ q ≤ ρ`, the
condition of `BootstrapAt_eq728_pathG` holds with `Φ = M = p`, `M' = 3p`, `ε = q`. -/
private theorem BootstrapAt_cond728G {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p * (q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (3 * p * p) + Real.sqrt (q * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hp1 : q * p ≤ r := by
    rw [hrdef]; have : p ≤ p ^ 3 := by nlinarith
    nlinarith
  have hT1 : q * n0 * ((1 + 3 * p) * (3 * p)) ≤ 12 * n0 * r := by
    have h1 : (1 + 3 * p) * (3 * p) ≤ 12 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + 3 * p) * (3 * p)) ≤ q * n0 * (12 * p ^ 2) := by gcongr
      _ = 12 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 12 * n0 * r := by gcongr
  have hsr : Real.sqrt (q * p) ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt ((hp1.trans hr).trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hqpp : q * (3 * p * p) ≤ 3 * r := by
    have heq : q * (3 * p * p) = 3 * (p ^ 2 * q) := by ring
    rw [heq]; nlinarith [hp2]
  have hS : q * n0 * ((1 + 3 * p) * (3 * p)) + 1 + q * (3 * p * p) + Real.sqrt (q * p) < 2 := by
    nlinarith
  nlinarith

end DominationG

section LBootstrapGEven

open Set Filter MeasureTheory

variable (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ)

/-- **Odd-length extension of an even-length bound via (6.4).** If `Lm` is bounded by
`M * s ^ (j - 1)` at every even `j ∈ [2, n₀]` (`hbd`), and `hodd` gives the pathwise inequality
`L_{2l+1} ≤ √(L_{2l} L_{2l+2})`, then the same bound holds at the odd `m` too. -/
private theorem BootstrapAt_gEven_oddBound {Lm : ℕ → ℝ → ℝ} {n0 : ℕ} (hn0 : Even n0)
    (hL0 : ∀ m t, 0 ≤ Lm m t) {M s : ℝ} (hM0 : 0 ≤ M) (hs0 : 0 ≤ s) {t : ℝ}
    (hodd : ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 →
      Lm (2 * l + 1) t ≤ Real.sqrt (Lm (2 * l) t * Lm (2 * l + 2) t))
    {m : ℕ} (hm2 : 2 ≤ m) (hmn : m ≤ n0) (hmo : Odd m)
    (hbd : ∀ j, 2 ≤ j → j ≤ n0 → Even j → Lm j t ≤ M * s ^ (j - 1)) :
    Lm m t ≤ M * s ^ (m - 1) := by
  obtain ⟨l, hl⟩ := hmo
  have hl1 : 1 ≤ l := by omega
  have hl2 : 2 * l + 2 ≤ n0 := by
    obtain ⟨k, hk⟩ := hn0; omega
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have heL := hbd (2 * (k + 1)) (by omega) (by omega) ⟨k + 1, two_mul (k + 1)⟩
  have heL2 := hbd (2 * (k + 1) + 2) (by omega) hl2 ⟨k + 2, by ring⟩
  have e1 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have e2 : 2 * (k + 1) + 2 - 1 = 2 * k + 3 := by omega
  rw [e1] at heL
  rw [e2] at heL2
  have hoddt := hodd (k + 1) hl1 hl2
  have hprod : Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t ≤
      (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3)) :=
    mul_le_mul heL heL2 (hL0 _ _) (by positivity)
  have hpoweq : s ^ (2 * k + 1) * s ^ (2 * k + 3) = s ^ (2 * k + 2) * s ^ (2 * k + 2) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  have heq : (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3)) = (M * s ^ (2 * k + 2)) ^ 2 := by
    calc (M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3))
        = M * M * (s ^ (2 * k + 1) * s ^ (2 * k + 3)) := by ring
      _ = M * M * (s ^ (2 * k + 2) * s ^ (2 * k + 2)) := by rw [hpoweq]
      _ = (M * s ^ (2 * k + 2)) ^ 2 := by ring
  have hsq : Real.sqrt (Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t) ≤ M * s ^ (2 * k + 2) := by
    calc Real.sqrt (Lm (2 * (k + 1)) t * Lm (2 * (k + 1) + 2) t)
        ≤ Real.sqrt ((M * s ^ (2 * k + 1)) * (M * s ^ (2 * k + 3))) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt ((M * s ^ (2 * k + 2)) ^ 2) := by rw [heq]
      _ = M * s ^ (2 * k + 2) := Real.sqrt_sq (by positivity)
  have hfin : Lm (2 * (k + 1) + 1) t ≤ M * s ^ (2 * k + 2) := hoddt.trans hsq
  have hm1 : m - 1 = 2 * k + 2 := by omega
  rw [hm1, hl]
  exact hfin

/-- **(7.27) from (7.45)G at even lengths only, pathwise.** -/
private theorem BootstrapAt_eq727_pathGE {Lm Dm Km : ℕ → ℝ → ℝ} {n0 : ℕ} (hn0 : Even n0)
    {t0 A M Φ ε δ : ℝ}
    (hN : 0 < N) (ht10 : t1 ≤ t0)
    (hη : ∀ t ∈ Icc t1 t0, 0 < η t)
    (hanti : ∀ u ∈ Icc t1 t0, ∀ t ∈ Icc t1 t0, u ≤ t → η t ≤ η u)
    (hηc : ContinuousOn η (Icc t1 t0))
    (hδ : ∀ t ∈ Icc t1 t0, (N * η t)⁻¹ ≤ δ) (hδ1 : δ ≤ 1)
    (hsm : ∀ t ∈ Icc t1 t0, t - t1 ≤ ε * η t) (hε : 0 ≤ ε)
    (hLc : ∀ m ∈ Set.Icc 2 n0, Even m → ContinuousOn (Lm m) (Icc t1 t0))
    (hL0 : ∀ m t, 0 ≤ Lm m t) (hD0 : ∀ m t, 0 ≤ Dm m t)
    (hLDK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Lm m t ≤ Dm m t + Km m t)
    (hDLK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Dm m t ≤ Lm m t + Km m t)
    (hodd : ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 → ∀ t ∈ Icc t1 t0,
      Lm (2 * l + 1) t ≤ Real.sqrt (Lm (2 * l) t * Lm (2 * l + 2) t))
    (hK : ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc t1 t0, Km m t ≤ A * (N * η t)⁻¹ ^ (m - 1))
    (h745 : ∀ m ∈ Set.Icc 2 n0, Even m → ∀ t ∈ Icc t1 t0,
      Dm m t ≤ Φ * rhs745G N η t1 Lm Dm m t)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hΦ : 0 ≤ Φ)
    (hcond : A + Φ * (ε * n0 * ((1 + (M + A)) * (M + A)) + δ + ε * (M * M)
      + Real.sqrt ε * M) < M) :
    ∀ t ∈ Icc t1 t0, ∀ m ∈ Set.Icc 2 n0, Lm m t ≤ M * (N * η t)⁻¹ ^ (m - 1) := by
  have hx0 : ∀ t ∈ Icc t1 t0, 0 < (N * η t)⁻¹ := fun t ht => inv_pos.2 (mul_pos hN (hη t ht))
  have hgc : ∀ m ∈ {m ∈ Set.Icc 2 n0 | Even m},
      ContinuousOn (fun t => M * (N * η t)⁻¹ ^ (m - 1)) (Icc t1 t0) :=
    fun m _ => continuousOn_const.mul
      (((continuousOn_const.mul hηc).inv₀ fun t ht => (mul_pos hN (hη t ht)).ne').pow _)
  have hc1 : 0 ≤ ε * n0 * ((1 + (M + A)) * (M + A)) := by positivity
  have hc3 : 0 ≤ ε * (M * M) := by positivity
  have hc4 : 0 ≤ Real.sqrt ε * M := by positivity
  have hS : Set.Finite {m ∈ Set.Icc 2 n0 | Even m} :=
    (Set.finite_Icc 2 n0).subset fun x hx => hx.1
  have heven : ∀ t ∈ Icc t1 t0, ∀ m ∈ {m ∈ Set.Icc 2 n0 | Even m},
      Lm m t < M * (N * η t)⁻¹ ^ (m - 1) := by
    refine continuity_argument hS (fun m hm => hLc m hm.1 hm.2) hgc (fun m hm => ?_)
      (fun t ht hprev m hm => ?_)
    · obtain ⟨hm2n0, hme⟩ := hm
      have ht1 : t1 ∈ Icc t1 t0 := ⟨le_rfl, ht10⟩
      set x := (N * η t1)⁻¹ with hx
      have hxp := hx0 t1 ht1
      have hD := h745 m hm2n0 hme t1 ht1
      have hself : rhs745G N η t1 Lm Dm m t1 = (N * η t1)⁻¹ ^ m := by simp [rhs745G]
      rw [hself] at hD
      have hxm : x ^ m ≤ δ * x ^ (m - 1) := by
        have : x ^ m = x * x ^ (m - 1) := by
          rw [← pow_succ']; congr 1; have := hm2n0.1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_right (hδ t1 ht1) (by positivity)
      have hLt := hLDK m hm2n0 t1 ht1
      have hKt := hK m hm2n0 t1 ht1
      have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
      change Lm m t1 < M * x ^ (m - 1)
      have hΦx : Φ * x ^ m ≤ Φ * δ * x ^ (m - 1) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hxm hΦ
      have hcond' : A + Φ * δ < M := by nlinarith
      nlinarith
    · obtain ⟨hm2n0, hme⟩ := hm
      obtain ⟨hm2, hmn⟩ := hm2n0
      show Lm m t < M * (N * η t)⁻¹ ^ (m - 1)
      set x := (N * η t)⁻¹ with hx
      have hxp := hx0 t ht
      have hx1 : x ≤ 1 := (hδ t ht).trans hδ1
      have hηt := hη t ht
      have ht1t : t1 ≤ t := ht.1
      have hsub : Icc t1 t ⊆ Icc t1 t0 := Icc_subset_Icc_right ht.2
      have hxu : ∀ u ∈ Icc t1 t, 0 ≤ (N * η u)⁻¹ ∧ (N * η u)⁻¹ ≤ x := by
        intro u hu
        have hu0 := hsub hu
        refine ⟨(hx0 u hu0).le, inv_anti₀ (mul_pos hN hηt) ?_⟩
        exact mul_le_mul_of_nonneg_left (hanti u hu0 t ht hu.2) hN.le
      have hLu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ n0 → Lm j u ≤ M * x ^ (j - 1) := by
        intro u hu j h2 hj
        rcases Nat.even_or_odd j with hje | hjo
        · have hprevj := hprev u hu j ⟨⟨h2, hj⟩, hje⟩
          refine hprevj.trans ?_
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
        · have hLj : Lm j u ≤ M * (N * η u)⁻¹ ^ (j - 1) :=
            BootstrapAt_gEven_oddBound hn0 hL0 hM (hx0 u (hsub hu)).le
              (fun l hl1 hl2 => hodd l hl1 hl2 u (hsub hu)) h2 hj hjo
              (fun k hk1 hk2 hke => hprev u hu k ⟨⟨hk1, hk2⟩, hke⟩)
          refine hLj.trans ?_
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
      have hDu : ∀ u ∈ Icc t1 t, ∀ j, 2 ≤ j → j ≤ m → 0 ≤ Dm j u ∧
          Dm j u ≤ (M + A) * x ^ (j - 1 + 0) := by
        intro u hu j h2 hj
        refine ⟨hD0 j u, ?_⟩
        have hjn : j ∈ Set.Icc 2 n0 := ⟨h2, hj.trans hmn⟩
        have h1 := hDLK j hjn u (hsub hu)
        have h2' := hK j hjn u (hsub hu)
        have h3 : A * (N * η u)⁻¹ ^ (j - 1) ≤ A * x ^ (j - 1) := by
          gcongr
          · exact (hxu u hu).1
          · exact (hxu u hu).2
        have h4 := hLu u hu j h2 (hj.trans hmn)
        rw [Nat.add_zero]
        nlinarith
      -- line 1
      have hl1 := supOn_line1_le N η t1 (n := m) 0 (by norm_num) ht1t (by positivity) hxp.le
        hx1 hxu hDu
      have hmx : x⁻¹ * x ^ m = x ^ (m - 1) := inv_mul_pow hxp.ne' (by omega)
      have hm0 : (m : ℝ) ≤ n0 := by exact_mod_cast hmn
      have hline1 : N * (t - t1) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
          ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (m - k + 2) u) t1 t
          ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * x ^ (m - 1) := by
        have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
        calc _ ≤ N * (t - t1) * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
              mul_le_mul_of_nonneg_left hl1 hNt
          _ ≤ ε * x⁻¹ * (m * ((1 + (M + A)) * (M + A) * x ^ (m + 0))) :=
              mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
          _ = ε * m * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by ring
          _ ≤ ε * n0 * ((1 + (M + A)) * (M + A)) * (x⁻¹ * x ^ m) := by gcongr
          _ = _ := by rw [hmx]
      -- line 2
      have hline2 : x ^ m ≤ δ * x ^ (m - 1) := by
        have : x ^ m = x * x ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [this]
        exact mul_le_mul_of_nonneg_right (hδ t ht) (by positivity)
      -- line 3 (E^{(G)} term `N L₂ L_n`, no fluctuation averaging)
      have hline3 : N * (t - t1) * supOn (fun u => Lm 2 u * Lm m u) t1 t
          ≤ ε * (M * M) * x ^ (m - 1) := by
        have hsup : supOn (fun u => Lm 2 u * Lm m u) t1 t ≤ M * M * x ^ m := by
          refine supOn_le ht1t fun u hu => ?_
          have h2 : Lm 2 u ≤ M * x := by simpa using hLu u hu 2 le_rfl (by omega)
          have hm' : Lm m u ≤ M * x ^ (m - 1) := hLu u hu m hm2 hmn
          calc Lm 2 u * Lm m u ≤ (M * x) * (M * x ^ (m - 1)) :=
                mul_le_mul h2 hm' (hL0 m u) (by positivity)
            _ = M * M * (x * x ^ (m - 1)) := by ring
            _ = M * M * x ^ m := by rw [← pow_succ']; congr 2; omega
        have hNt : 0 ≤ N * (t - t1) := mul_nonneg hN.le (by linarith)
        calc _ ≤ N * (t - t1) * (M * M * x ^ m) := mul_le_mul_of_nonneg_left hsup hNt
          _ ≤ ε * x⁻¹ * (M * M * x ^ m) :=
              mul_le_of_eq730 N η t1 hN (by positivity) (hsm t ht)
          _ = ε * (M * M) * (x⁻¹ * x ^ m) := by ring
          _ = _ := by rw [hmx]
      -- line 4
      have hline4 : Real.sqrt (t - t1) *
          supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
          ≤ Real.sqrt ε * M * x ^ (m - 1) := by
        have hsup : supOn (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm m u) t1 t
            ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1)) := by
          refine supOn_le ht1t fun u hu => ?_
          have hu0 := hsub hu
          have hηu : (η u)⁻¹ ≤ (η t)⁻¹ := inv_anti₀ hηt (hanti u hu0 t ht hu.2)
          have hs : Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) ≤ Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) := by
            refine Real.sqrt_le_sqrt ?_
            have : 0 ≤ (η u)⁻¹ := (inv_pos.2 (hη u hu0)).le
            gcongr
          exact mul_le_mul hs (hLu u hu m hm2 hmn) (hL0 m u) (Real.sqrt_nonneg _)
        have hsq := sqrt_mul_sqrt_le N η t1 hN hηt ht1t (hsm t ht)
        have hsx : Real.sqrt (ε * (N * η t)⁻¹) ≤ Real.sqrt ε := by
          refine Real.sqrt_le_sqrt ?_
          calc ε * (N * η t)⁻¹ ≤ ε * 1 := mul_le_mul_of_nonneg_left hx1 hε
            _ = ε := mul_one ε
        have hpos : 0 ≤ M * x ^ (m - 1) := by positivity
        calc _ ≤ Real.sqrt (t - t1) * (Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2) * (M * x ^ (m - 1))) :=
              mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
          _ = (Real.sqrt (t - t1) * Real.sqrt (N⁻¹ * (η t)⁻¹ ^ 2)) * (M * x ^ (m - 1)) := by ring
          _ ≤ Real.sqrt ε * (M * x ^ (m - 1)) :=
              mul_le_mul_of_nonneg_right (hsq.trans hsx) hpos
          _ = _ := by ring
      -- assemble
      have hD := h745 m ⟨hm2, hmn⟩ hme t ht
      have hrhs : rhs745G N η t1 Lm Dm m t ≤ (ε * n0 * ((1 + (M + A)) * (M + A)) + δ
          + ε * (M * M) + Real.sqrt ε * M) * x ^ (m - 1) := by
        unfold rhs745G
        rw [← hx]
        nlinarith
      have hDt : Dm m t ≤ Φ * ((ε * n0 * ((1 + (M + A)) * (M + A)) + δ
          + ε * (M * M) + Real.sqrt ε * M) * x ^ (m - 1)) :=
        hD.trans (mul_le_mul_of_nonneg_left hrhs hΦ)
      have hLt := hLDK m ⟨hm2, hmn⟩ t ht
      have hKt := hK m ⟨hm2, hmn⟩ t ht
      have hpos : 0 < x ^ (m - 1) := pow_pos hxp _
      nlinarith
  intro t ht m hm
  rcases Nat.even_or_odd m with hme | hmo
  · exact (heven t ht m ⟨hm, hme⟩).le
  · obtain ⟨hm2, hmn⟩ := hm
    exact BootstrapAt_gEven_oddBound hn0 hL0 hM (hx0 t ht).le
      (fun l hl1 hl2 => hodd l hl1 hl2 t ht) hm2 hmn hmo
      (fun k hk1 hk2 hke => (heven t ht k ⟨⟨hk1, hk2⟩, hke⟩).le)

end LBootstrapGEven

section DominationGE

open Set Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The smallness bookkeeping of (7.45)G, restricted to even lengths. -/
private theorem BootstrapAt_gEven_cond727G {p q : ℝ} (n0 : ℕ) (hp : 1 ≤ p) (hq : 0 ≤ q)
    (hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48))) :
    p + p * (q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * (3 * p)) + Real.sqrt q * (3 * p)) < 3 * p := by
  set r := p ^ 3 * q with hrdef
  have hn0 : (0 : ℝ) ≤ n0 := Nat.cast_nonneg n0
  have hρ : 1 / (36 * (20 * (n0 : ℝ) + 48)) ≤ 1 / 36 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hp0 : 0 < p := by linarith
  have hp2 : p ^ 2 * q ≤ r := by
    rw [hrdef]; have : p ^ 2 ≤ p ^ 3 := pow_le_pow_right₀ hp (by norm_num)
    exact mul_le_mul_of_nonneg_right this hq
  have hq1 : q ≤ r := by
    rw [hrdef]; have : 1 ≤ p ^ 3 := one_le_pow₀ hp
    nlinarith
  have hT1 : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ 20 * n0 * r := by
    have h1 : (1 + (3 * p + p)) * (3 * p + p) ≤ 20 * p ^ 2 := by nlinarith
    calc q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) ≤ q * n0 * (20 * p ^ 2) := by gcongr
      _ = 20 * n0 * (p ^ 2 * q) := by ring
      _ ≤ 20 * n0 * r := by gcongr
  have hT3 : q * (3 * p * (3 * p)) ≤ 9 * r := by
    have heq : q * (3 * p * (3 * p)) = 9 * (p ^ 2 * q) := by ring
    rw [heq]; nlinarith [hp2]
  have hT4 : Real.sqrt q * (3 * p) ≤ 3 * Real.sqrt r := by
    have : Real.sqrt q * p = Real.sqrt (p ^ 2 * q) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp0.le]; ring
    have h2 : Real.sqrt (p ^ 2 * q) ≤ Real.sqrt r := Real.sqrt_le_sqrt hp2
    nlinarith
  have hsr : Real.sqrt r ≤ 1 / 6 := by
    rw [show (1 : ℝ) / 6 = Real.sqrt (1 / 36) by
      rw [show (1 : ℝ) / 36 = (1 / 6) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (hr.trans hρ)
  have hsum : (20 * n0 + 48) * r ≤ 1 / 36 := by
    have h48 : (0 : ℝ) < 20 * n0 + 48 := by positivity
    calc (20 * n0 + 48) * r ≤ (20 * n0 + 48) * (1 / (36 * (20 * n0 + 48))) := by gcongr
      _ = 1 / 36 := by field_simp
  have hr0 : 0 ≤ r := by positivity
  have hS : q * n0 * ((1 + (3 * p + p)) * (3 * p + p)) + q
      + q * (3 * p * (3 * p)) + Real.sqrt q * (3 * p) < 2 := by nlinarith
  nlinarith

end DominationGE

/-! ### Size-scale domination helpers -/

section DomAt

open Set MeasureTheory

/-- `UnifDetDom` along an admissible sequence of matrix dimensions `size N`. -/
def UnifDetDomAt (size : ℕ → ℕ) {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) : Prop :=
  ∀ τ > (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ u, f N u ≤ ((size N : ℕ) : ℝ) ^ τ * g N u

/-- The merged `RBM.UnifDetDom` (`Defs/Domination.lean:52`) is `UnifDetDomAt` at `size = id`, as
`RBM.stochDom_iff_at_id` and `RBM.Gauss.highProb_iff_at_id` are. -/
theorem unifDetDom_iff_at_id {U : ℕ → Type*} (f g : ∀ N, U N → ℝ) :
    UnifDetDom f g ↔ UnifDetDomAt id f g := Iff.rfl

/-- `(size N)^a ≤ ρ` for large `N`, if `a < 0`, `ρ > 0` and `size → ∞`. -/
theorem eventually_size_rpow_le_of_neg {size : ℕ → ℕ} (hsize : Tendsto size atTop atTop)
    {a ρ : ℝ} (ha : a < 0) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in atTop, ((size N : ℕ) : ℝ) ^ a ≤ ρ :=
  hsize.eventually (eventually_rpow_le_of_neg ha hρ)

/-- `≺` on the size scale from its good events: if for every `τ > 0` the event
`{∀ u, ξ ≤ (size N)^τ ζ}` holds w.h.p. (`HighProbAt`), then `ξ ≺ ζ` (`StochDomAt`). -/
theorem stochDomAt_of_forall_highProbAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {size : ℕ → ℕ} {U : ℕ → Type*} {ξ ζ : ∀ N, U N → Ω → ℝ}
    (h : ∀ τ > (0 : ℝ), RBM.Gauss.HighProbAt P size
      (fun N => {ω | ∀ u, ξ N u ω ≤ ((size N : ℕ) : ℝ) ^ τ * ζ N u ω})) :
    StochDomAt P size ξ ζ := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with N hN
  refine (measure_mono ?_).trans hN
  rintro ω ⟨u, hu⟩ hω
  exact absurd (hω u) (not_le.2 hu)

end DomAt

/-! ### (7.36) on the size scale -/

section KBootstrapAt

open Set

/-- **(7.36)** `max_{σ,a} |K_{t,σ,a}| ≺ (N η_t)^{-n+1}` on the size scale: `eq736_detDom` with
`UnifDetDom ↦ UnifDetDomAt size`, `Z2 ↦ Zd d` and the failure threshold `N^{-τU} ↦ (size N)^{-τU}` in (7.30);
the matrix dimension `size N` is not tied to `(Wf N * Lf N)^d` (`eq736` takes `A, ε` free). -/
theorem eq736_detDomAt (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) (d : ℕ)
    (Lf Wf : ℕ → ℕ) [∀ N, NeZero (Lf N)]
    (Kt : ∀ N, ℝ → LoopIdx (Zd d (Lf N)) → ℂ) (n : ℕ) (t1 t0 : ℕ → ℝ)
    (ht10 : ∀ N, t1 N ≤ t0 N) (lam : ℕ → ℝ → ℝ)
    (hlam : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < lam N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → lam N t ≤ lam N u)
    (hlamc : ∀ N, ContinuousOn (lam N) (Icc (t1 N) (t0 N)))
    (hK : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), ∀ I : LoopIdx (Zd d (Lf N)), I.WF → 2 ≤ I.length →
      I.length ≤ n →
      HasDerivWithinAt (fun s => Kt N s I) (primRhsGUE d (Lf N) (Wf N) (Kt N t) I)
        (Icc (t1 N) (t0 N)) t)
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N),
      (((Wf N * Lf N) ^ d : ℕ) : ℝ) * (t - t1 N) ≤ ((size N : ℕ) : ℝ) ^ (-τU) * lam N t)
    (h732 : UnifDetDomAt size (fun N (I : LoopSet d (Lf N) n) => ‖Kt N (t1 N) I.1‖)
      (fun N I => (lam N (t1 N))⁻¹ ^ (I.1.length - 1))) :
    UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × LoopSet d (Lf N) n) => ‖Kt N p.1 p.2.1‖)
      (fun N p => (lam N p.1)⁻¹ ^ (p.2.1.length - 1)) := by
  intro τ hτ
  set τ' := min τ τU / 2 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : τ' < τU := by have := min_le_right τ τU; linarith
  filter_upwards [h732 τ' hτ'0, h730, hsize.eventually (eventually_small (n := n) hτ'U),
    hsize.eventually (eventually_le_rpow 2 (sub_pos.2 hτ'τ)),
    hsize.eventually (eventually_ge_atTop 1)] with N hinit hsm hε h2 hN1
  rintro ⟨⟨t, ht⟩, I, hI⟩
  have hN0 : (0 : ℝ) < ((size N : ℕ) : ℝ) := by exact_mod_cast hN1
  have hA : 0 < ((size N : ℕ) : ℝ) ^ τ' := Real.rpow_pos_of_pos hN0 _
  have key := eq736 d (Lf N) (Wf N) (Kt N) (ht10 N) (lam N) (hlam N) (hanti N) (hlamc N) (hK N)
    hA (fun J hJ h2J hJn => hinit ⟨J, hJ, h2J, hJn⟩) hsm
    (by simpa [mul_assoc] using hε) t ht I hI.1 hI.2.1 hI.2.2
  have hx : 0 ≤ (lam N t)⁻¹ ^ (I.length - 1) := pow_nonneg (inv_pos.2 (hlam N t ht)).le _
  have hsplit : ((size N : ℕ) : ℝ) ^ τ
      = ((size N : ℕ) : ℝ) ^ (τ - τ') * ((size N : ℕ) : ℝ) ^ τ' := by
    rw [← Real.rpow_add hN0]; ring_nf
  change ‖Kt N t I‖ ≤ ((size N : ℕ) : ℝ) ^ τ * (lam N t)⁻¹ ^ (I.length - 1)
  rw [hsplit]
  have : 2 * ((size N : ℕ) : ℝ) ^ τ' * (lam N t)⁻¹ ^ (I.length - 1)
      ≤ ((size N : ℕ) : ℝ) ^ (τ - τ') * ((size N : ℕ) : ℝ) ^ τ' * (lam N t)⁻¹ ^ (I.length - 1) := by
    gcongr
  linarith

end KBootstrapAt

/-! ### (7.46)G ⟹ (7.28) and (7.45)G ⟹ (7.27) on the size scale -/

section TargetsAt

open Set Filter MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **(7.28)** on the size scale (`eq728G` with `StochDom`, `HighProb`, `N^{-τU}` read along `size N`). -/
theorem eq728GAt (P : Measure Ω) (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) {n0 : ℕ} (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ ((size N : ℕ) : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ ((size N : ℕ) : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (h727 : StochDomAt P size (fun N (p : Path.TimeIcc t1 t0 N × Set.Icc 2 (2 * n0)) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : RBM.Gauss.HighProbAt P size (fun N => {ω | ∀ m ∈ Set.Icc 1 n0,
      ContinuousOn (fun t => Dm N m t ω) (Icc (t1 N) (t0 N))}))
    (h746 : StochDomAt P size (fun N (p : Path.TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p ω => rhs746G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2 p.1)) :
    StochDomAt P size (fun N (p : Path.TimeIcc t1 t0 N × Set.Icc 1 n0) ω => Dm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ (p.2 : ℕ)) := by
  refine stochDomAt_of_forall_highProbAt fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h746 hτ'0) hcont)
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h727 hτ'0)) ?_
  filter_upwards [h730, hscale, eventually_size_rpow_le_of_neg hsize hτ'U hρ,
    hsize.eventually (eventually_le_rpow 3 (sub_pos.2 hτ'τ)), hsize.eventually (eventually_ge_atTop 1)]
    with N h730N hscN hrN h3N hN1
  rintro ω ⟨⟨h746ω, hcω⟩, hLω⟩
  simp only [Set.mem_ofPred_eq] at h746ω hcω hLω ⊢
  have hN0 : (0 : ℝ) < ((size N : ℕ) : ℝ) := by exact_mod_cast hN1
  set p := ((size N : ℕ) : ℝ) ^ τ' with hpdef
  set q := ((size N : ℕ) : ℝ) ^ (-τU) with hqdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by exact_mod_cast hN1) hτ'0.le
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48)) := by
    have : p ^ 3 * q = ((size N : ℕ) : ℝ) ^ (3 * τ' - τU) := by
      rw [hpdef, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [this]; exact hrN
  have key := BootstrapAt_eq728_pathG (Nf N) (η N) (t1 N) (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (n0 := n0) (M := p) (M' := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm => hcω m hm) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω)
    (fun j h2 hj t ht => by simpa using hLω (⟨t, ht⟩, ⟨j, h2, hj⟩))
    (fun m hm t ht => by simpa using h746ω (⟨t, ht⟩, ⟨m, hm⟩)) (by linarith) (by linarith)
    (by linarith) (BootstrapAt_cond728G n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ m := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ ((size N : ℕ) : ℝ) ^ τ := by
    have e : ((size N : ℕ) : ℝ) ^ τ = ((size N : ℕ) : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  change Dm N m t ω ≤ ((size N : ℕ) : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ m
  nlinarith


/-- **(7.27) from (7.45)G at even lengths** on the size scale (`eq727GE` along `size N`). -/
theorem eq727GEAt (P : Measure Ω) (size : ℕ → ℕ) (hsize : Tendsto size atTop atTop) {n0 : ℕ} (hn0 : Even n0) (Nf : ℕ → ℝ) (η : ℕ → ℝ → ℝ) (t1 t0 : ℕ → ℝ)
    (Lm Dm : ℕ → ℕ → ℝ → Ω → ℝ) (Km : ℕ → ℕ → ℝ → ℝ)
    (hN : ∀ N, 0 < Nf N) (ht10 : ∀ N, t1 N ≤ t0 N)
    (hη : ∀ N, ∀ t ∈ Icc (t1 N) (t0 N), 0 < η N t)
    (hanti : ∀ N, ∀ u ∈ Icc (t1 N) (t0 N), ∀ t ∈ Icc (t1 N) (t0 N), u ≤ t → η N t ≤ η N u)
    (hηc : ∀ N, ContinuousOn (η N) (Icc (t1 N) (t0 N)))
    {τU : ℝ} (hτU : 0 < τU)
    (h730 : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), t - t1 N ≤ ((size N : ℕ) : ℝ) ^ (-τU) * η N t)
    (hscale : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1 N) (t0 N), (Nf N * η N t)⁻¹ ≤ ((size N : ℕ) : ℝ) ^ (-τU))
    (hL0 : ∀ N m t ω, 0 ≤ Lm N m t ω) (hD0 : ∀ N m t ω, 0 ≤ Dm N m t ω)
    (hLDK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Lm N m t ω ≤ Dm N m t ω + Km N m t)
    (hDLK : ∀ N ω, ∀ m ∈ Set.Icc 2 n0, ∀ t ∈ Icc (t1 N) (t0 N), Dm N m t ω ≤ Lm N m t ω + Km N m t)
    (hodd : ∀ N ω, ∀ l : ℕ, 1 ≤ l → 2 * l + 2 ≤ n0 → ∀ t ∈ Icc (t1 N) (t0 N),
      Lm N (2 * l + 1) t ω ≤ Real.sqrt (Lm N (2 * l) t ω * Lm N (2 * l + 2) t ω))
    (hK : UnifDetDomAt size (fun N (p : Path.TimeIcc t1 t0 N × Set.Icc 2 n0) => Km N p.2 p.1)
      (fun N p => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)))
    (hcont : RBM.Gauss.HighProbAt P size (fun N => {ω | ∀ m ∈ Set.Icc 2 n0, Even m →
      ContinuousOn (fun t => Lm N m t ω) (Icc (t1 N) (t0 N))}))
    (h745 : StochDomAt P size
      (fun N (p : Path.TimeIcc t1 t0 N × {m : ℕ // m ∈ Set.Icc 2 n0 ∧ Even m}) ω => Dm N p.2.1 p.1 ω)
      (fun N p ω => rhs745G (Nf N) (η N) (t1 N) (fun m t => Lm N m t ω) (fun m t => Dm N m t ω)
        p.2.1 p.1)) :
    StochDomAt P size (fun N (p : Path.TimeIcc t1 t0 N × Set.Icc 2 n0) ω => Lm N p.2 p.1 ω)
      (fun N p _ => (Nf N * η N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) := by
  refine stochDomAt_of_forall_highProbAt fun τ hτ => ?_
  set τ' := min τ τU / 16 with hτ'
  have hτ'0 : 0 < τ' := by positivity
  have hτ'τ : τ' < τ := by have := min_le_left τ τU; linarith
  have hτ'U : 3 * τ' - τU < 0 := by have := min_le_right τ τU; linarith
  have hρ : (0 : ℝ) < 1 / (36 * (20 * n0 + 48)) := by positivity
  refine RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_mono (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_inter hsize
    (RBM.Ind.PerTimeCalc.perTimeCalc_highProbAt_of_stochDomAt h745 hτ'0) hcont) ?_
  filter_upwards [hK τ' hτ'0, h730, hscale, eventually_size_rpow_le_of_neg hsize hτ'U hρ,
    hsize.eventually (eventually_le_rpow 3 (sub_pos.2 hτ'τ)), hsize.eventually (eventually_ge_atTop 1)]
    with N hKN h730N hscN hrN h3N hN1
  rintro ω ⟨h745ω, hcω⟩
  simp only [Set.mem_ofPred_eq] at h745ω hcω ⊢
  have hN0 : (0 : ℝ) < ((size N : ℕ) : ℝ) := by exact_mod_cast hN1
  set p := ((size N : ℕ) : ℝ) ^ τ' with hpdef
  set q := ((size N : ℕ) : ℝ) ^ (-τU) with hqdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by exact_mod_cast hN1) hτ'0.le
  have hq0 : 0 ≤ q := Real.rpow_nonneg hN0.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN1) (by linarith)
  have hr : p ^ 3 * q ≤ 1 / (36 * (20 * n0 + 48)) := by
    have : p ^ 3 * q = ((size N : ℕ) : ℝ) ^ (3 * τ' - τU) := by
      rw [hpdef, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
      push_cast; ring_nf
    rw [this]; exact hrN
  have key := BootstrapAt_eq727_pathGE (Nf N) (η N) (t1 N) hn0 (Lm := fun m t => Lm N m t ω)
    (Dm := fun m t => Dm N m t ω) (Km := Km N) (n0 := n0) (A := p) (M := 3 * p) (Φ := p)
    (ε := q) (δ := q) (hN N) (ht10 N) (hη N) (hanti N) (hηc N) hscN hq1 h730N hq0
    (fun m hm hme => hcω m hm hme) (fun m t => hL0 N m t ω) (fun m t => hD0 N m t ω) (hLDK N ω)
    (hDLK N ω) (fun l hl1 hl2 t ht => hodd N ω l hl1 hl2 t ht)
    (fun m hm t ht => by simpa using hKN (⟨t, ht⟩, ⟨m, hm⟩))
    (fun m hm hme t ht => by simpa using h745ω (⟨t, ht⟩, ⟨m, hm, hme⟩)) (by linarith) (by linarith)
    (by linarith) (BootstrapAt_gEven_cond727G n0 hp1 hq0 hr)
  rintro ⟨⟨t, ht⟩, ⟨m, hm⟩⟩
  have h1 := key t ht m hm
  have hx : 0 ≤ (Nf N * η N t)⁻¹ ^ (m - 1) := by
    have := hη N t ht; have := hN N; positivity
  have h3 : 3 * p ≤ ((size N : ℕ) : ℝ) ^ τ := by
    have e : ((size N : ℕ) : ℝ) ^ τ = ((size N : ℕ) : ℝ) ^ (τ - τ') * p := by
      rw [hpdef, ← Real.rpow_add hN0]; ring_nf
    rw [e]; nlinarith
  change Lm N m t ω ≤ ((size N : ℕ) : ℝ) ^ τ * (Nf N * η N t)⁻¹ ^ (m - 1)
  nlinarith

end TargetsAt
/-! ### Compiled nonempty instances of the targets (CLAUDE.md §4 step 2) -/

namespace BootstrapAtCheck

open Set Filter MeasureTheory BootstrapCheck

/-- The size scale `size N = N + 1` of the instances: `size → ∞`. -/
def sizeD (N : ℕ) : ℕ := N + 1

theorem sizeD_tendsto : Tendsto sizeD atTop atTop :=
  tendsto_atTop_mono (fun N => Nat.le_succ N) tendsto_id

theorem sizeD_pos (N : ℕ) : (0 : ℝ) < ((sizeD N : ℕ) : ℝ) := by
  unfold sizeD; positivity

theorem sizeD_one_le (N : ℕ) : (1 : ℝ) ≤ ((sizeD N : ℕ) : ℝ) := by
  unfold sizeD; push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The zero family is dominated by any nonnegative control (its failure event is empty). -/
theorem zero_stochDomAt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (size : ℕ → ℕ)
    {U : ℕ → Type*} (ζ : ∀ N, U N → Ω → ℝ) (hζ : ∀ N u ω, 0 ≤ ζ N u ω) :
    StochDomAt P size (fun _ _ _ => (0 : ℝ)) ζ := by
  intro τ hτ D hD
  refine Eventually.of_forall fun N => ?_
  have : badSetAt size (fun _ _ _ => (0 : ℝ)) ζ τ N = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro ω ⟨u, hu⟩
    exact absurd hu (not_lt.2 (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hζ N u ω)))
  rw [this]; simp

/-- Data of the `eq728GAt` / `eq727GEAt` instances: `N_f = N + 1`, `η ≡ 1`, `t₁ = 0`,
`t₀ = 1/(N+1)` (a non-collapsed window), `τ_U = 1`.  Local copies of RBM2D `Bootstrap.lean:1391-1430`
at `c9a24cf`. -/
def NfD (N : ℕ) : ℝ := (N : ℝ) + 1

def etaD (_ : ℕ) (_ : ℝ) : ℝ := 1

def t1D (_ : ℕ) : ℝ := 0

def t0D (N : ℕ) : ℝ := 1 / ((N : ℝ) + 1)

theorem NfD_pos (N : ℕ) : 0 < NfD N := by unfold NfD; positivity

theorem t10D (N : ℕ) : t1D N ≤ t0D N := by unfold t1D t0D; positivity

theorem t0D_le_one (N : ℕ) : t0D N ≤ 1 := by
  unfold t0D
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- The scale `λ_N ≡ 216 (N+1)` used in the zero `eq736_detDomAt` instance (RBM2D `lamD`, `36 ↦ 216`). -/
def lamD (N : ℕ) (_ : ℝ) : ℝ := 216 * ((N : ℝ) + 1)

theorem rhs746G_zero_nonneg {N : ℝ} {η : ℝ → ℝ} {t1 t : ℝ} (hN : 0 < N) (hη : 0 < η t)
    (n : ℕ) : 0 ≤ rhs746G N η t1 (fun _ _ => 0) (fun _ _ => 0) n t := by
  have h : 0 ≤ (N * η t)⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (mul_pos hN hη).le) _
  simpa [rhs746G, supOn] using h

theorem rhs745G_zero_nonneg {N : ℝ} {η : ℝ → ℝ} {t1 t : ℝ} (hN : 0 < N) (hη : 0 < η t)
    (n : ℕ) : 0 ≤ rhs745G N η t1 (fun _ _ => 0) (fun _ _ => 0) n t := by
  have h : 0 ≤ (N * η t)⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (mul_pos hN hη).le) _
  simpa [rhs745G, supOn] using h

theorem ctrlD_nonneg (N : ℕ) (t : ℝ) (k : ℕ) : 0 ≤ (NfD N * etaD N t)⁻¹ ^ k :=
  pow_nonneg (inv_nonneg.2 (by unfold NfD etaD; positivity)) _

theorem h730At : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1D N) (t0D N),
    t - t1D N ≤ ((sizeD N : ℕ) : ℝ) ^ (-(1 : ℝ)) * etaD N t := by
  refine Eventually.of_forall fun N t ht => ?_
  have h2 : t ≤ 1 / ((N : ℝ) + 1) := ht.2
  simp only [t1D, etaD, sizeD, Real.rpow_neg_one, mul_one, Nat.cast_add, Nat.cast_one]
  simpa [one_div] using h2

theorem hscaleAt : ∀ᶠ N : ℕ in atTop, ∀ t ∈ Icc (t1D N) (t0D N),
    (NfD N * etaD N t)⁻¹ ≤ ((sizeD N : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
  refine Eventually.of_forall fun N t _ => ?_
  simp [NfD, etaD, sizeD, Real.rpow_neg_one]

theorem ctrlAt_nonneg (N : ℕ) (t : ℝ) (k : ℕ) (τ : ℝ) :
    0 ≤ ((sizeD N : ℕ) : ℝ) ^ τ * (NfD N * etaD N t)⁻¹ ^ k :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (ctrlD_nonneg N t k)

/-- Target `unifDetDom_iff_at_id` at `f N _ = (N+1)⁻¹ ≤ 1 = g N _`: the index-scale `UnifDetDom`
(from `UnifDetDom.of_le`) is the `UnifDetDomAt id` statement. -/
theorem inst_unifDetDom_iff_at_id :
    UnifDetDomAt id (fun (N : ℕ) (_ : Unit) => ((N : ℝ) + 1)⁻¹) (fun _ _ => (1 : ℝ)) :=
  (unifDetDom_iff_at_id (U := fun _ => Unit) _ _).1
    (UnifDetDom.of_le (fun _ _ => zero_le_one)
      (fun N _ => inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])))

/-- Target `eventually_size_rpow_le_of_neg` at `a = -1`, `ρ = 1/2`, `size N = N + 1`. -/
theorem inst_eventually_size_rpow_le_of_neg :
    ∀ᶠ N : ℕ in atTop, ((sizeD N : ℕ) : ℝ) ^ (-1 : ℝ) ≤ 1 / 2 :=
  eventually_size_rpow_le_of_neg sizeD_tendsto (a := -1) (ρ := 1 / 2) (by norm_num) (by norm_num)

/-- Target `stochDomAt_of_forall_highProbAt` at `ξ = ζ ≡ 1`, `P = δ_()`, `size N = N + 1`: the events
`{∀ u, 1 ≤ (N+1)^τ · 1}` hold for all `N` (`HighProbAt.of_eventually_univ`). -/
theorem inst_stochDomAt_of_forall_highProbAt :
    StochDomAt (Measure.dirac ()) sizeD (fun _ (_ : Unit) (_ : Unit) => (1 : ℝ))
      (fun _ _ _ => (1 : ℝ)) :=
  stochDomAt_of_forall_highProbAt fun τ hτ =>
    RBM.Gauss.HighProbAt.of_eventually_univ (Eventually.of_forall fun N _ _ => by
      have h1 : (1 : ℝ) ≤ ((sizeD N : ℕ) : ℝ) ^ τ := Real.one_le_rpow (sizeD_one_le N) hτ.le
      linarith)

/-- Target `eq736_detDomAt` at `d = 3`, `L ≡ 3`, `W ≡ 2`, `n = 2`, `K ≡ 0`, `t₁ = 0`, `t₀ = 1`,
`τ_U = 1`, `λ_N = 216 (N+1)`, `size N = N + 1`
(`(W L)^d (t - t₁) = 216 t ≤ (N+1)⁻¹ · 216 (N + 1)`). -/
theorem inst_eq736_detDomAt_zero : UnifDetDomAt sizeD
    (fun N (_ : Path.TimeIcc (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) N × LoopSet 3 3 2) =>
      ‖(0 : ℂ)‖)
    (fun N p => (lamD N p.1)⁻¹ ^ (p.2.1.length - 1)) :=
  eq736_detDomAt sizeD sizeD_tendsto 3 (fun _ => 3) (fun _ => 2) (fun _ _ _ => (0 : ℂ)) 2
    (fun _ => 0) (fun _ => 1)
    (fun _ => zero_le_one) lamD
    (fun N _ _ => by unfold lamD; positivity) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ => continuousOn_const)
    (fun N t _ I _ _ _ => by
      change HasDerivWithinAt (fun _ : ℝ => (0 : ℂ)) (primRhsGUE 3 3 2 (fun _ => 0) I) _ _
      rw [primRhsGUE_zero]
      exact hasDerivWithinAt_const _ _ _)
    (τU := 1) one_pos
    (Eventually.of_forall fun N t ht => by
      have h2 : t ≤ 1 := ht.2
      change (((2 * 3) ^ 3 : ℕ) : ℝ) * (t - 0) ≤ ((sizeD N : ℕ) : ℝ) ^ (-(1 : ℝ)) * lamD N t
      simp only [lamD, sizeD, Real.rpow_neg_one, Nat.cast_add, Nat.cast_one]
      have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have h1 : ((N : ℝ) + 1)⁻¹ * (216 * ((N : ℝ) + 1)) = 216 := by field_simp
      rw [h1]
      norm_num
      linarith)
    (fun τ _ => Eventually.of_forall fun N p => by
      simp only [norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg (inv_nonneg.2 (by unfold lamD; positivity)) _))

/-- Target `eq736_detDomAt` at the nonzero tight solution `K(t) = K₀ / (1 - 216 K₀ t)` of
`K' = 216 K²` (`n = 2`, `d = 3`, `L ≡ 3`, `W ≡ 2`, `K₀ = 1/7000`), `t₁ = 0`, `t₀ = 1/(N+1)`,
`λ ≡ 7000`, `τ_U = 1`, `size N = N + 1`: (7.30) is `216 t ≤ (N+1)⁻¹ · 7000`, `h732` is
`K(0) = 1/7000 ≤ (N+1)^τ · 7000⁻¹`. -/
theorem inst_eq736_detDomAt_tight : UnifDetDomAt sizeD
    (fun N (p : Path.TimeIcc t1D t0D N × LoopSet 3 3 2) => ‖(kTight p.1 : ℂ)‖)
    (fun _ p => (7000 : ℝ)⁻¹ ^ (p.2.1.length - 1)) :=
  eq736_detDomAt sizeD sizeD_tendsto 3 (fun _ => 3) (fun _ => 2) (fun _ t _ => (kTight t : ℂ)) 2
    t1D t0D t10D (fun _ _ => 7000)
    (fun _ _ _ => by norm_num) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ => continuousOn_const)
    (fun N t ht I _ h2 h2' => by
      have hI : I.length = 2 := le_antisymm h2' h2
      have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.trans (t0D_le_one N)⟩
      have h := (kTight_hasDerivAt ht1).ofReal_comp.hasDerivWithinAt
        (s := Icc (t1D N) (t0D N))
      change HasDerivWithinAt (fun s => (kTight s : ℂ))
        (primRhsGUE 3 3 2 (fun _ => (kTight t : ℂ)) I) (Icc (t1D N) (t0D N)) t
      rw [primRhsGUE_const_len_two _ I hI]
      convert h using 1
      push_cast
      ring)
    (τU := 1) one_pos
    (Eventually.of_forall fun N t ht => by
      have h2' : t ≤ 1 / ((N : ℝ) + 1) := ht.2
      rw [one_div] at h2'
      have h2 := h2'
      have hx0 : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
      change (((2 * 3) ^ 3 : ℕ) : ℝ) * (t - t1D N) ≤ ((sizeD N : ℕ) : ℝ) ^ (-(1 : ℝ)) * 7000
      simp only [t1D, sizeD, Real.rpow_neg_one, Nat.cast_add, Nat.cast_one]
      norm_num
      linarith)
    (fun τ hτ => Eventually.of_forall fun N I => by
      have hI : I.1.length = 2 := le_antisymm I.2.2.2 I.2.2.1
      have h1 : (1 : ℝ) ≤ ((sizeD N : ℕ) : ℝ) ^ τ := Real.one_le_rpow (sizeD_one_le N) hτ.le
      change ‖(kTight (t1D N) : ℂ)‖ ≤ ((sizeD N : ℕ) : ℝ) ^ τ * (7000 : ℝ)⁻¹ ^ (I.1.length - 1)
      rw [hI]
      simp only [t1D, Complex.norm_real, Real.norm_eq_abs, kTight_zero]
      norm_num
      nlinarith)

theorem inst_bounds :
    (∀ N : ℕ, (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 / ((N : ℝ) + 1) - 0) ≤
      ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) * 7000) ∧
    (∀ N : ℕ, ((N : ℝ) + 1)⁻¹ ≤ 1) ∧
    (∀ N : ℕ, (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 - 0) ≤
      ((N + 1 : ℕ) : ℝ) ^ (-(1 : ℝ)) * (216 * ((N : ℝ) + 1))) := by
  refine ⟨fun N => ?_, fun N => ?_, fun N => ?_⟩
  · have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    simp only [Real.rpow_neg_one, Nat.cast_add, Nat.cast_one, sub_zero]
    rw [div_eq_mul_inv, one_mul]
    norm_num
    have : 0 ≤ ((N : ℝ) + 1)⁻¹ := by positivity
    linarith
  · exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
  · have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    simp only [Real.rpow_neg_one, Nat.cast_add, Nat.cast_one]
    have h1 : ((N : ℝ) + 1)⁻¹ * (216 * ((N : ℝ) + 1)) = 216 := by field_simp
    rw [h1]
    norm_num

/-- Target `eq728GAt` (`P = δ_()`, `n₀ = 2`, `L = D = 0`, window `[0, 1/(N+1)]`,
`size N = N + 1`); every hypothesis is discharged. -/
theorem inst_eq728GAt_zero : StochDomAt (Measure.dirac ()) sizeD
    (fun N (_ : Path.TimeIcc t1D t0D N × Set.Icc 1 2) (_ : Unit) => (0 : ℝ))
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ (p.2 : ℕ)) :=
  eq728GAt (n0 := 2) (Measure.dirac ()) sizeD sizeD_tendsto NfD etaD t1D t0D
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) NfD_pos t10D (fun _ _ _ => one_pos)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ => continuousOn_const) (τU := 1) one_pos h730At hscaleAt
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (zero_stochDomAt _ _ _ (fun N p _ => pow_nonneg (inv_nonneg.2
      (by have := NfD_pos N; unfold NfD etaD at *; positivity)) _))
    (RBM.Gauss.HighProbAt.of_eventually_univ
      (Eventually.of_forall fun _ _ _ _ => continuousOn_const))
    (zero_stochDomAt _ _ _ (fun N p _ => rhs746G_zero_nonneg (NfD_pos N) one_pos _))

/-- Target `eq727GEAt` (`P = δ_()`, `n₀ = 4` even, `L = D = K = 0`, window `[0, 1/(N+1)]`,
`size N = N + 1`); every hypothesis is discharged. -/
theorem inst_eq727GEAt_zero : StochDomAt (Measure.dirac ()) sizeD
    (fun N (_ : Path.TimeIcc t1D t0D N × Set.Icc 2 4) (_ : Unit) => (0 : ℝ))
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) :=
  eq727GEAt (n0 := 4) (Measure.dirac ()) sizeD sizeD_tendsto (by decide) NfD etaD t1D t0D
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ _ => 0) NfD_pos t10D (fun _ _ _ => one_pos)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ => continuousOn_const) (τU := 1) one_pos h730At hscaleAt
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl)
    (fun _ _ _ _ _ _ => by simp) (fun _ _ _ _ _ _ => by simp) (fun _ _ _ _ _ _ _ => by simp)
    (fun τ _ => Eventually.of_forall fun N p => ctrlAt_nonneg N p.1.1 _ τ)
    (RBM.Gauss.HighProbAt.of_eventually_univ
      (Eventually.of_forall fun _ _ _ _ _ => continuousOn_const))
    (zero_stochDomAt _ _ _ (fun N p _ => rhs745G_zero_nonneg (NfD_pos N) one_pos _))

/-! #### The positive data of `eq727GEAt` and the chained `eq728GAt`

`x_N(t) = (N_f η_t)⁻¹ = 1/(N+1)`, `L_m = x^{m-1}`, `D_m = x^m`, `K_m = x^{m-1} - x^m`
(`L = D + K`, `D ≤ L + K` as `x ≤ 1`, `L_{2l+1} = √(L_{2l} L_{2l+2})`). -/

/-- `x_N(t) = (N_f η_t)⁻¹`. -/
def xD (N : ℕ) (t : ℝ) : ℝ := (NfD N * etaD N t)⁻¹

theorem xD_eq (N : ℕ) (t : ℝ) : xD N t = ((N : ℝ) + 1)⁻¹ := by
  simp [xD, NfD, etaD]

theorem xD_nonneg (N : ℕ) (t : ℝ) : 0 ≤ xD N t := by
  rw [xD_eq]; positivity

theorem xD_pos (N : ℕ) (t : ℝ) : 0 < xD N t := by
  rw [xD_eq]; positivity

theorem xD_le_one (N : ℕ) (t : ℝ) : xD N t ≤ 1 := by
  rw [xD_eq]; exact inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])

def LmD (N m : ℕ) (t : ℝ) (_ : Unit) : ℝ := xD N t ^ (m - 1)

def DmD (N m : ℕ) (t : ℝ) (_ : Unit) : ℝ := xD N t ^ m

def KmD (N m : ℕ) (t : ℝ) : ℝ := xD N t ^ (m - 1) - xD N t ^ m

theorem LmD_nonneg (N m : ℕ) (t : ℝ) (ω : Unit) : 0 ≤ LmD N m t ω :=
  pow_nonneg (xD_nonneg N t) _

theorem DmD_nonneg (N m : ℕ) (t : ℝ) (ω : Unit) : 0 ≤ DmD N m t ω :=
  pow_nonneg (xD_nonneg N t) _

theorem LmD_cont (N m : ℕ) (a b : ℝ) (ω : Unit) : ContinuousOn (fun t => LmD N m t ω) (Icc a b) := by
  simp only [LmD, xD_eq]; exact continuousOn_const

theorem DmD_cont (N m : ℕ) (a b : ℝ) (ω : Unit) : ContinuousOn (fun t => DmD N m t ω) (Icc a b) := by
  simp only [DmD, xD_eq]; exact continuousOn_const

theorem KmD_le (N m : ℕ) (t : ℝ) : KmD N m t ≤ xD N t ^ (m - 1) := by
  unfold KmD; linarith [pow_nonneg (xD_nonneg N t) m]

theorem DmD_le_LmD_add_KmD (N m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    DmD N m t () ≤ LmD N m t () + KmD N m t := by
  unfold DmD LmD KmD
  have h : xD N t ^ m ≤ xD N t ^ (m - 1) := by
    have : m = (m - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (xD_nonneg N t) _) (xD_le_one N t)
  linarith

theorem LmD_odd (N : ℕ) (l : ℕ) (hl : 1 ≤ l) (t : ℝ) :
    LmD N (2 * l + 1) t () ≤ Real.sqrt (LmD N (2 * l) t () * LmD N (2 * l + 2) t ()) := by
  unfold LmD
  have e : xD N t ^ (2 * l - 1) * xD N t ^ (2 * l + 2 - 1) = (xD N t ^ (2 * l)) ^ 2 := by
    rw [← pow_add, ← pow_mul]; congr 1; omega
  rw [e, Real.sqrt_sq (pow_nonneg (xD_nonneg N t) _)]
  simp

theorem DmD_le_rhs745G (N m : ℕ) {t : ℝ} (ht : t ∈ Icc (t1D N) (t0D N)) :
    DmD N m t () ≤ rhs745G (NfD N) (etaD N) (t1D N) (fun m t => LmD N m t ())
      (fun m t => DmD N m t ()) m t := by
  have hN := NfD_pos N
  have hx : ∀ u, 0 ≤ (NfD N * etaD N u)⁻¹ := fun u => (xD_nonneg N u)
  have ht1 : 0 ≤ t - t1D N := sub_nonneg.2 ht.1
  have e : DmD N m t () = (NfD N * etaD N t)⁻¹ ^ m := rfl
  have h1 : 0 ≤ NfD N * (t - t1D N) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((NfD N * etaD N u)⁻¹ ^ (k - 1) + DmD N k u ()) * DmD N (m - k + 2) u ()) (t1D N) t :=
    mul_nonneg (mul_nonneg hN.le ht1) (supOn_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (add_nonneg (pow_nonneg (hx u) _) (DmD_nonneg _ _ _ _)) (DmD_nonneg _ _ _ _))
  have h3 : 0 ≤ NfD N * (t - t1D N) * supOn (fun u => LmD N 2 u () * LmD N m u ()) (t1D N) t :=
    mul_nonneg (mul_nonneg hN.le ht1) (supOn_nonneg fun u _ =>
      mul_nonneg (LmD_nonneg _ _ _ _) (LmD_nonneg _ _ _ _))
  have h4 : 0 ≤ Real.sqrt (t - t1D N) * supOn (fun u => Real.sqrt ((NfD N)⁻¹ *
      (etaD N u)⁻¹ ^ 2) * LmD N m u ()) (t1D N) t :=
    mul_nonneg (Real.sqrt_nonneg _) (supOn_nonneg fun u _ =>
      mul_nonneg (Real.sqrt_nonneg _) (LmD_nonneg _ _ _ _))
  unfold rhs745G
  rw [e]
  linarith

theorem DmD_le_rhs746G (N m : ℕ) {t : ℝ} (ht : t ∈ Icc (t1D N) (t0D N)) :
    DmD N m t () ≤ rhs746G (NfD N) (etaD N) (t1D N) (fun m t => LmD N m t ())
      (fun m t => DmD N m t ()) m t := by
  have hN := NfD_pos N
  have hx : ∀ u, 0 ≤ (NfD N * etaD N u)⁻¹ := fun u => (xD_nonneg N u)
  have ht1 : 0 ≤ t - t1D N := sub_nonneg.2 ht.1
  have e : DmD N m t () = (NfD N * etaD N t)⁻¹ ^ m := rfl
  have h1 : 0 ≤ NfD N * (t - t1D N) * supOn (fun u => ∑ k ∈ Finset.Icc 2 m,
      ((NfD N * etaD N u)⁻¹ ^ (k - 1) + DmD N k u ()) * DmD N (m - k + 2) u ()) (t1D N) t :=
    mul_nonneg (mul_nonneg hN.le ht1) (supOn_nonneg fun u _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (add_nonneg (pow_nonneg (hx u) _) (DmD_nonneg _ _ _ _)) (DmD_nonneg _ _ _ _))
  have h3 : 0 ≤ NfD N * (t - t1D N) * supOn (fun u => DmD N 1 u () * LmD N (m + 1) u ()) (t1D N) t :=
    mul_nonneg (mul_nonneg hN.le ht1) (supOn_nonneg fun u _ =>
      mul_nonneg (DmD_nonneg _ _ _ _) (LmD_nonneg _ _ _ _))
  have h4 : 0 ≤ Real.sqrt (t - t1D N) * supOn (fun u => Real.sqrt ((NfD N)⁻¹ *
      (etaD N u)⁻¹ ^ 2) * Real.sqrt (LmD N (2 * m) u ())) (t1D N) t :=
    mul_nonneg (Real.sqrt_nonneg _) (supOn_nonneg fun u _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  unfold rhs746G
  rw [e]
  linarith

theorem rhs745G_nonneg (N m : ℕ) {t : ℝ} (ht : t ∈ Icc (t1D N) (t0D N)) :
    0 ≤ rhs745G (NfD N) (etaD N) (t1D N) (fun m t => LmD N m t ())
      (fun m t => DmD N m t ()) m t :=
  (DmD_nonneg N m t ()).trans (DmD_le_rhs745G N m ht)

theorem rhs746G_nonneg (N m : ℕ) {t : ℝ} (ht : t ∈ Icc (t1D N) (t0D N)) :
    0 ≤ rhs746G (NfD N) (etaD N) (t1D N) (fun m t => LmD N m t ())
      (fun m t => DmD N m t ()) m t :=
  (DmD_nonneg N m t ()).trans (DmD_le_rhs746G N m ht)

/-- Target `eq727GEAt` at the positive data (`P = δ_()`, `n₀ = 2 * 2` even, `L_m = x^{m-1}`,
`D_m = x^m`, `K_m = x^{m-1} - x^m`, `x = 1/(N+1)`, window `[0, 1/(N+1)]`, `size N = N + 1`,
`τ_U = 1`): every deterministic hypothesis is discharged; `h745` from `x^m ≤ rhs745G`. -/
theorem inst_eq727GEAt_pos : StochDomAt (Measure.dirac ()) sizeD
    (fun N (p : Path.TimeIcc t1D t0D N × Set.Icc 2 (2 * 2)) (ω : Unit) => LmD N p.2 p.1 ω)
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ ((p.2 : ℕ) - 1)) :=
  eq727GEAt (n0 := 2 * 2) (Measure.dirac ()) sizeD sizeD_tendsto (even_two_mul 2) NfD etaD
    t1D t0D LmD DmD KmD NfD_pos t10D (fun _ _ _ => one_pos) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ => continuousOn_const) (τU := 1) one_pos h730At hscaleAt LmD_nonneg DmD_nonneg
    (fun N _ m _ t _ => by
      change xD N t ^ (m - 1) ≤ xD N t ^ m + (xD N t ^ (m - 1) - xD N t ^ m)
      linarith)
    (fun N _ m hm t _ => DmD_le_LmD_add_KmD N m (by have := hm.1; omega) t)
    (fun N _ l hl _ t _ => LmD_odd N l hl t)
    (fun τ _ => Eventually.of_forall fun N p => by
      have h1 : (1 : ℝ) ≤ ((sizeD N : ℕ) : ℝ) ^ τ := Real.one_le_rpow (sizeD_one_le N) ‹0 < τ›.le
      have h2 := KmD_le N p.2 p.1
      have h3 : 0 ≤ xD N p.1 ^ ((p.2 : ℕ) - 1) := pow_nonneg (xD_nonneg N _) _
      change KmD N p.2 p.1 ≤ ((sizeD N : ℕ) : ℝ) ^ τ * xD N p.1 ^ ((p.2 : ℕ) - 1)
      nlinarith)
    (RBM.Gauss.HighProbAt.of_eventually_univ
      (Eventually.of_forall fun N ω m _ _ => LmD_cont N m _ _ ω))
    (StochDomAt.of_le_left (fun N p _ => DmD_le_rhs745G N p.2.1 p.1.2)
      (StochDomAt.refl sizeD_tendsto (fun N p _ => rhs745G_nonneg N p.2.1 p.1.2)))

/-- Target `eq728GAt` at the positive data, chained: `h727` is the output of `eq727GEAt` at
`n₀ := 2 * 2` (`inst_eq727GEAt_pos`), exactly as RBM2D `PathBounds.lean:491-507` (`n₀ = 2`, index set
`Set.Icc 2 (2 * 2)`); `h746` from `x^m ≤ rhs746G`. -/
theorem inst_eq728GAt_chain : StochDomAt (Measure.dirac ()) sizeD
    (fun N (p : Path.TimeIcc t1D t0D N × Set.Icc 1 2) (ω : Unit) => DmD N p.2 p.1 ω)
    (fun N p _ => (NfD N * etaD N p.1)⁻¹ ^ (p.2 : ℕ)) :=
  eq728GAt (n0 := 2) (Measure.dirac ()) sizeD sizeD_tendsto NfD etaD t1D t0D LmD DmD
    NfD_pos t10D (fun _ _ _ => one_pos) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ => continuousOn_const) (τU := 1) one_pos h730At hscaleAt LmD_nonneg DmD_nonneg
    inst_eq727GEAt_pos
    (RBM.Gauss.HighProbAt.of_eventually_univ
      (Eventually.of_forall fun N ω m _ => DmD_cont N m _ _ ω))
    (StochDomAt.of_le_left (fun N p _ => DmD_le_rhs746G N p.2.1 p.1.2)
      (StochDomAt.refl sizeD_tendsto (fun N p _ => rhs746G_nonneg N p.2.1 p.1.2)))

end BootstrapAtCheck

end RBM.Univ.GUEPhase

end
