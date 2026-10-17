/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.QtBootGen
import RBM3D.Chain.QEndB1Gen
import RBM3D.Induction.QtXiRoundLift

/-!
# The case-(i) round over the carrier family, uniformly in the pair, and `stOeqQtgL'_of` (U3s4 row a, file 2; ticket T2505)

Generic form of `Induction/QtXiRoundLift.lean` §2-§6 (not edited) over a carrier family `(law, Flow, mkM, T0)`, namespace `RBM.BA`, no `BA/*` import.  Paper:
arXiv:2507.20274, `lem:STOeq_Qt` (`3_5:1362-1378`, `(am;asoi222)` `3_5:1366`), proof `3_5:1678-1766`, the `N^{-C}`-net remark with `lem_ConArg` `3_5:1764`.
Composition, no new mathematics (`7_8:1841`).

* **Target 3** `stXiRoundgL'_of_PTfam` (private at one carrier: `QtLiftGen_lift`): the lift `STXiRoundPTgL'' → STXiRoundgL'`.  The envelope `X♯` of the controls, the diagonal restriction, the one-sided
  floor net (`qtLift_core_below`, model-free, used by `open private`) with the good event `G` of the flow modulus `LemDecCalELipG_FlowMod` (in place of `contGood`), the
  `𝓛` modulus `lemDecCalELipG_loops` (`LemDecCalELip_Lloop_subg`: `3 k N^{2k+6} N^c √|u-u'|`, `(η_t)⁻¹ ≤ N²` from `LemDecCalELip_envg`), the `𝒦` modulus
  `NQEndFlowGen_KLip` (family row 15), and the mesh `δ ≤ N^{-(6 n_ + 18 + 2c)}` (band `6 n_ + 20` at `c = 1`).
* **Target 4** `stXiRoundQtgL_of`, `stOeqQtgL'_of` (conclusion = the merged `STOeqQtgL'`, binding): the round of `stOeqQtRoundPTgL''_of` (U3s3c), the lift, then
  `stXiBootRgL'_of_round` at `STCaseI`.
* **Target 5** the band re-derivations `stOeqQtgL'_band` (every `d ≥ 3`, no open hypothesis), `stOeqQt'_holds_of_gen`, and compiled nonempty instances at `d = 3`.

The model-free privates of `QtXiRoundLift` (`qtLift_*`: the envelope, `ζ♯`, the net core) are used by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open private qtLift_sharp_one_le qtLift_sharp_le qtLift_sharp_mono qtLift_zeta_mono qtLift_zeta_le qtLift_zeta_one_le qtLift_core_below
  from RBM3D.Induction.QtXiRoundLift

open private NQEndFlowGen_prec_of_le_right NQEndFlowGen_isProb from RBM3D.Chain.NQEndFlowGen

open private nqEnd_rangeCond_mono from RBM3D.Induction.NQEndLin

open private QtBootGen_flow_abs_le from RBM3D.Chain.QtBootGen

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes
open RBM.Ind (nqFlowSharp QProxyG_KerEK4Fam)

/-! ## 1. The gluing lemmas over a law (private copies of `QtXiRoundLift` §2, §5) -/

section Glue

variable {d : ℕ}

/-- Envelope (d) over a law (band `qtLift_sharp_prec`, `QtXiRoundLift.lean:94`): the pair hypotheses carry over to `X♯`. -/
private theorem QtLiftGen_sharp_prec (sz : Sizes d) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ)
    (X : ℕ → ℕ → ℝ → ℝ) (m : ℕ) (hX : ∀ m n u, 1 ≤ X m n u)
    (h : PrecL sz μ (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => X m n q.1.2)) :
    PrecL sz μ (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => nqFlowSharp t X m n q.1.2) := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ, hτ, Eventually.of_forall fun n ω hω => ?_⟩
  obtain ⟨q, hq⟩ := hω
  have hc : 0 < ((sz.size n : ℕ) : ℝ) ^ τ :=
    Real.rpow_pos_of_pos (by exact_mod_cast sz.one_le_size n) _
  have hu : q.1.2 ≤ t n := q.2.2.2
  have hS : (X m n '' Set.Icc q.1.2 (t n)).Nonempty := ⟨X m n q.1.2, q.1.2, ⟨le_rfl, hu⟩, rfl⟩
  have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * max 1 (sInf (X m n '' Set.Icc q.1.2 (t n))) < f n q.1.1 ω := hq
  have hinf : sInf (X m n '' Set.Icc q.1.2 (t n)) < f n q.1.1 ω / ((sz.size n : ℕ) : ℝ) ^ τ := by
    rw [lt_div_iff₀ hc]
    have h1 : ((sz.size n : ℕ) : ℝ) ^ τ * sInf (X m n '' Set.Icc q.1.2 (t n)) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * max 1 (sInf (X m n '' Set.Icc q.1.2 (t n))) :=
      mul_le_mul_of_nonneg_left (le_max_right 1 _) hc.le
    linarith
  obtain ⟨y, ⟨u', hu', rfl⟩, hy⟩ := exists_lt_of_csInf_lt hS hinf
  refine ⟨⟨(q.1.1, u'), q.2.1, q.2.2.1.trans hu'.1, hu'.2⟩, ?_⟩
  rw [lt_div_iff₀ hc] at hy
  change ((sz.size n : ℕ) : ℝ) ^ τ * X m n u' < f n q.1.1 ω
  linarith

/-- **Diagonal restriction of the per-time statement** (band `qtLift_diag_PT`, `QtXiRoundLift.lean:611`): a per-time `≺` over the pairs, whose left side depends on `q.1.1`
only and whose right side on `q.1.2` only, restricts to the diagonal `w ↦ ((w, w), _)`. -/
private theorem QtLiftGen_diag_PT (sz : Sizes d) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ)
    (h : PrecPTL sz μ (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2)) :
    PrecPTL sz μ (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ)) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with l hl w
  exact hl ⟨((w.1 : ℝ), (w.1 : ℝ)), w.1.2.1, le_rfl, w.1.2.2⟩

/-- **Diagonal → pair propagation** (band `qtLift_diag_to_pair`, `QtXiRoundLift.lean:621`): for a right side `g` non-decreasing in the endpoint on `[s_n, t_n]`, the
uniform `≺` on the diagonal gives the uniform `≺` over the pairs. -/
private theorem QtLiftGen_diag_to_pair (sz : Sizes d) (μ : Measure sz.SeqΩ) (s t : ℕ → ℝ) (f : ℕ → ℝ → sz.SeqΩ → ℝ) (g : ℕ → ℝ → ℝ)
    (hmono : ∀ (n : ℕ) (v u : ℝ), s n ≤ v → v ≤ u → u ≤ t n → g n v ≤ g n u)
    (h : PrecL sz μ (U := fun n => TimeIcc s t n × Unit) (fun n w ω => f n (w.1 : ℝ) ω) (fun n w _ => g n (w.1 : ℝ))) :
    PrecL sz μ (U := STPair s t) (fun n q ω => f n q.1.1 ω) (fun n q _ => g n q.1.2) := by
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn
  refine (measure_mono fun ω hω => ?_).trans hn
  obtain ⟨q, hq⟩ := hω
  have hc : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨(⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩, ()), ?_⟩
  have hq' : ((sz.size n : ℕ) : ℝ) ^ τ * g n q.1.2 < f n q.1.1 ω := hq
  change ((sz.size n : ℕ) : ℝ) ^ τ * g n q.1.1 < f n q.1.1 ω
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hmono n q.1.1 q.1.2 q.2.1 q.2.2.1 q.2.2.2) hc) hq'

/-! ## 2. The mesh arithmetic and the closeness on the good event -/

/-- **The mesh arithmetic** (band `qtLift_arith`, `QtXiRoundLift.lean:439`, with the Hölder exponent `c` of `LemDecCalELipG_FlowMod`): for `δ ≤ N^{-(6 n_ + 18 + 2c)}`, `c ≥ 0`
and `N ≥ 3 n_ + 1`, `N^{n_} (3 n_ N^{2n_+6} N^c √δ + N^{2n_+2} δ) ≤ 1` (the first term is `≤ 3 n_ N^{-3}`, the second `≤ N^{-3}`). -/
private theorem QtLiftGen_arith {N δ c : ℝ} {n_ : ℕ} (hN : (3 * n_ + 1 : ℝ) ≤ N) (hc : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ N ^ (-(((6 * n_ + 18 : ℕ) : ℝ) + 2 * c))) :
    N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ + N ^ (2 * n_ + 2) * δ) ≤ 1 := by
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hC1 : (1 : ℝ) ≤ N ^ c := Real.one_le_rpow hN1 hc
  have hC0 : (0 : ℝ) < N ^ c := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = N ^ (3 * n_ + 9) * N ^ c := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; positivity
  have h2c : N ^ (2 * c) = (N ^ c) ^ 2 := by
    rw [show 2 * c = c + c by ring, Real.rpow_add hN0, sq]
  have hMsq : N ^ (6 * n_ + 18) * (N ^ c) ^ 2 = M ^ 2 := by
    rw [hM, mul_pow, ← pow_mul]; congr 2; omega
  have hδM : δ ≤ (M ^ 2)⁻¹ := by
    refine hδ.trans (le_of_eq ?_)
    rw [Real.rpow_neg hN0.le, Real.rpow_add hN0, Real.rpow_natCast, h2c, hMsq]
  have hsqrt : Real.sqrt δ ≤ M⁻¹ := by
    have h2 : Real.sqrt δ ≤ Real.sqrt ((M ^ 2)⁻¹) := Real.sqrt_le_sqrt hδM
    rwa [← inv_pow, Real.sqrt_sq (by positivity)] at h2
  have hA : N ^ n_ * (N ^ (2 * n_ + 6)) = N ^ (3 * n_ + 6) := by rw [← pow_add]; congr 1; ring
  have hM3 : N ^ (3 * n_ + 9) = N ^ (3 * n_ + 6) * N ^ 3 := by rw [← pow_add]
  have t1 : N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ) ≤ 3 * n_ * (N ^ 3)⁻¹ := by
    calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ)
        = 3 * n_ * (N ^ n_ * N ^ (2 * n_ + 6)) * N ^ c * Real.sqrt δ := by ring
      _ = 3 * n_ * N ^ (3 * n_ + 6) * N ^ c * Real.sqrt δ := by rw [hA]
      _ ≤ 3 * n_ * N ^ (3 * n_ + 6) * N ^ c * M⁻¹ := by gcongr
      _ = 3 * n_ * (N ^ 3)⁻¹ := by
          rw [hM, hM3]; field_simp
  have hB : N ^ n_ * N ^ (2 * n_ + 2) = N ^ (3 * n_ + 2) := by rw [← pow_add]; congr 1; ring
  have hMM : N ^ (3 * n_ + 2) * N ^ 3 ≤ M ^ 2 := by
    rw [← hMsq, ← pow_add]
    have h6 : N ^ (3 * n_ + 2 + 3) ≤ N ^ (6 * n_ + 18) := pow_le_pow_right₀ hN1 (by omega)
    have h7 : N ^ (6 * n_ + 18) ≤ N ^ (6 * n_ + 18) * (N ^ c) ^ 2 := by
      have : 1 ≤ (N ^ c) ^ 2 := one_le_pow₀ hC1
      nlinarith [pow_pos hN0 (6 * n_ + 18)]
    exact h6.trans h7
  have t2 : N ^ n_ * (N ^ (2 * n_ + 2) * δ) ≤ (N ^ 3)⁻¹ := by
    calc N ^ n_ * (N ^ (2 * n_ + 2) * δ) = N ^ (3 * n_ + 2) * δ := by rw [← hB]; ring
      _ ≤ N ^ (3 * n_ + 2) * (M ^ 2)⁻¹ := by gcongr
      _ ≤ N ^ (3 * n_ + 2) * (N ^ (3 * n_ + 2) * N ^ 3)⁻¹ := by gcongr
      _ = (N ^ 3)⁻¹ := by field_simp
  have hN3 : (3 * n_ + 1 : ℝ) * (N ^ 3)⁻¹ ≤ 1 := by
    have hN3pos : 0 < N ^ 3 := by positivity
    rw [← div_eq_mul_inv, div_le_one hN3pos]
    have : N ≤ N ^ 3 := le_self_pow₀ hN1 (by norm_num)
    linarith
  calc N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ + N ^ (2 * n_ + 2) * δ)
      = N ^ n_ * (3 * n_ * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt δ) + N ^ n_ * (N ^ (2 * n_ + 2) * δ) := by ring
    _ ≤ 3 * n_ * (N ^ 3)⁻¹ + (N ^ 3)⁻¹ := add_le_add t1 t2
    _ = (3 * n_ + 1) * (N ^ 3)⁻¹ := by ring
    _ ≤ 1 := hN3

/-- **The per-loop `ξ` closeness** (band `qtLift_xi_close`, `QtXiRoundLift.lean:491`; one-sided, for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 18 + 2c)}`):
`‖(𝓛-𝒦)_u‖ / B_u^{n_} ≤ ‖(𝓛-𝒦)_{u'}‖ / B_{u'}^{n_} + 1`.  The `𝓛` modulus `hL` (`3 n_ N^{2n_+6} N^c √|u-u'|`, `lemDecCalELipG_loops`) and the `𝒦` modulus `hK`
(`N^{2n_+2}|u-u'|`, `NQEndFlowGen_KLip`) are premises; `B_{u'} ≤ B_u` (`STBctl_mono`), `N⁻¹ ≤ B_u` (`cont_inv_size_le_Bctl`); the ratio term
`‖(𝓛-𝒦)_{u'}‖ (B_{u'}^{-n_} - B_u^{-n_}) ≥ 0` has the favourable sign and is dropped. -/
private theorem QtLiftGen_xi_close (sz : Sizes d) (Cf : FlowFM sz) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (3 * n_ + 1 : ℝ) ≤ N)
    (hΔ : u - u' ≤ N ^ (-(((6 * n_ + 18 : ℕ) : ℝ) + 2 * c)))
    (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n))
    (hL : ‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ ≤ 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt |u - u'|)
    (hK : ‖Cf.K n u σ a - Cf.K n u' σ a‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    ‖Cf.L n u σ a ω - Cf.K n u σ a‖ / (sz.Bctl n u) ^ n_ ≤
      ‖Cf.L n u' σ a ω - Cf.K n u' σ a‖ / (sz.Bctl n u') ^ n_ + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hu'0 : 0 ≤ u' := hs0.trans hsu'
  have hu0 : 0 ≤ u := hu'0.trans hu'u
  have hn0 : (0 : ℝ) ≤ n_ := Nat.cast_nonneg _
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hBu : 0 < sz.Bctl n u := st_Bctl_pos sz hu1
  have hBu' : 0 < sz.Bctl n u' := st_Bctl_pos sz hu'1
  have hBle : sz.Bctl n u' ≤ sz.Bctl n u := STBctl_mono sz n hu'u hu1
  have hBinv : N⁻¹ ≤ sz.Bctl n u := by
    rw [hN]; exact RBM.Ind.ContinuityNet.cont_inv_size_le_Bctl sz n hu0 hu1
  have hδ0 : 0 ≤ u - u' := sub_nonneg.2 hu'u
  rw [abs_of_nonneg hδ0] at hK hL
  have harith := QtLiftGen_arith hM hc hδ0 hΔ
  have hNn : 0 < N ^ n_ := pow_pos hN0 _
  have hsmall : 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt (u - u') + N ^ (2 * n_ + 2) * (u - u') ≤
      (sz.Bctl n u) ^ n_ := by
    have h1 : (N ^ n_)⁻¹ ≤ (sz.Bctl n u) ^ n_ := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 hN0.le) hBinv n_
    refine le_trans ?_ h1
    calc 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt (u - u') + N ^ (2 * n_ + 2) * (u - u')
        = (N ^ n_)⁻¹ * (N ^ n_ * (3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt (u - u') +
            N ^ (2 * n_ + 2) * (u - u'))) := by field_simp
      _ ≤ (N ^ n_)⁻¹ * 1 := mul_le_mul_of_nonneg_left harith (inv_nonneg.2 hNn.le)
      _ = (N ^ n_)⁻¹ := mul_one _
  have hsum2 : ‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ + ‖Cf.K n u σ a - Cf.K n u' σ a‖ ≤
      (sz.Bctl n u) ^ n_ := by
    linarith
  have htri : ‖Cf.L n u σ a ω - Cf.K n u σ a‖ ≤
      ‖Cf.L n u' σ a ω - Cf.K n u' σ a‖ +
        (‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ + ‖Cf.K n u σ a - Cf.K n u' σ a‖) := by
    have e : Cf.L n u σ a ω - Cf.K n u σ a =
        (Cf.L n u' σ a ω - Cf.K n u' σ a) + (Cf.L n u σ a ω - Cf.L n u' σ a ω) -
          (Cf.K n u σ a - Cf.K n u' σ a) := by ring
    rw [e]
    calc _ ≤ ‖(Cf.L n u' σ a ω - Cf.K n u' σ a) +
          (Cf.L n u σ a ω - Cf.L n u' σ a ω)‖ + ‖Cf.K n u σ a - Cf.K n u' σ a‖ :=
          norm_sub_le _ _
      _ ≤ _ := by
          have := norm_add_le (Cf.L n u' σ a ω - Cf.K n u' σ a)
            (Cf.L n u σ a ω - Cf.L n u' σ a ω)
          linarith
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos hBu _
  calc ‖Cf.L n u σ a ω - Cf.K n u σ a‖ / (sz.Bctl n u) ^ n_
      ≤ (‖Cf.L n u' σ a ω - Cf.K n u' σ a‖ +
          (‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ +
            ‖Cf.K n u σ a - Cf.K n u' σ a‖)) / (sz.Bctl n u) ^ n_ :=
        div_le_div_of_nonneg_right htri hBpow.le
    _ = ‖Cf.L n u' σ a ω - Cf.K n u' σ a‖ / (sz.Bctl n u) ^ n_ +
          (‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ +
            ‖Cf.K n u σ a - Cf.K n u' σ a‖) / (sz.Bctl n u) ^ n_ := add_div _ _ _
    _ ≤ ‖Cf.L n u' σ a ω - Cf.K n u' σ a‖ / (sz.Bctl n u') ^ n_ + 1 := by
        refine add_le_add ?_ ((div_le_one hBpow).2 hsum2)
        exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hBu' _) (pow_le_pow_left₀ hBu'.le hBle _)

/-- **The one-sided closeness of `Ξ̂^{(𝓛-𝒦)}_{·,n_}` on the good event** (band `qtLift_xiLK_close`, `QtXiRoundLift.lean:582`): the per-loop closeness passed through the finite
`sup'` of `STmaxLKg` (`Finset.sup'_le`, `Finset.le_sup'`): for `s ≤ u' ≤ u ≤ t`, `u - u' ≤ N^{-(6 n_ + 18 + 2c)}`, `STXiLKg_u ≤ STXiLKg_{u'} + 1`. -/
private theorem QtLiftGen_xiLK_close (sz : Sizes d) (Cf : FlowFM sz) (n : ℕ) {c : ℝ} (hc : 0 ≤ c) {n_ : ℕ} {s t u u' N : ℝ} (ω : sz.SeqΩ)
    (hs0 : 0 ≤ s) (hsu' : s ≤ u') (hu'u : u' ≤ u) (hut : u ≤ t) (ht1 : t < 1)
    (hN : N = ((sz.size n : ℕ) : ℝ)) (hM : (3 * n_ + 1 : ℝ) ≤ N)
    (hΔ : u - u' ≤ N ^ (-(((6 * n_ + 18 : ℕ) : ℝ) + 2 * c)))
    (hL : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖Cf.L n u σ a ω - Cf.L n u' σ a ω‖ ≤ 3 * (n_ : ℝ) * N ^ (2 * n_ + 6) * N ^ c * Real.sqrt |u - u'|)
    (hK : ∀ (σ : Fin n_ → Bool) (a : Fin n_ → Zd d (sz.L n)),
      ‖Cf.K n u σ a - Cf.K n u' σ a‖ ≤ N ^ (2 * n_ + 2) * |u - u'|) :
    STXiLKg Cf n u n_ ω ≤ STXiLKg Cf n u' n_ ω + 1 := by
  have hu1 : u < 1 := hut.trans_lt ht1
  have hu'1 : u' < 1 := hu'u.trans_lt hu1
  have hBpow : 0 < (sz.Bctl n u) ^ n_ := pow_pos (st_Bctl_pos sz hu1) _
  have hBpow' : 0 < (sz.Bctl n u') ^ n_ := pow_pos (st_Bctl_pos sz hu'1) _
  have key : STmaxLKg Cf n u n_ ω / (sz.Bctl n u) ^ n_ ≤
      STmaxLKg Cf n u' n_ ω / (sz.Bctl n u') ^ n_ + 1 := by
    rw [div_le_iff₀ hBpow]
    refine Finset.sup'_le _ _ fun p _ => ?_
    rw [← div_le_iff₀ hBpow]
    refine (QtLiftGen_xi_close sz Cf n hc ω hs0 hsu' hu'u hut ht1 hN hM hΔ p.1 p.2 (hL p.1 p.2) (hK p.1 p.2)).trans ?_
    have h2 : ‖Cf.L n u' p.1 p.2 ω - Cf.K n u' p.1 p.2‖ ≤ STmaxLKg Cf n u' n_ ω :=
      Finset.le_sup' (fun p : (Fin n_ → Bool) × (Fin n_ → Zd d (sz.L n)) =>
        ‖Cf.L n u' p.1 p.2 ω - Cf.K n u' p.1 p.2‖) (Finset.mem_univ p)
    have h3 := div_le_div_of_nonneg_right h2 hBpow'.le
    linarith
  unfold STXiLKg
  linarith

end Glue

/-! ## 3. Target 3: the lift `STXiRoundPTgL'' → STXiRoundgL'` at one carrier -/

section Lift

variable {d : ℕ}

/-- `(1 - t)⁻¹ ≤ N` from the range condition `N^{-1+τ} ≤ 1 - t` (`τ ≥ 0`; the band `stXiRoundQt_holds` has `τ = ε/2`). -/
private theorem QtLiftGen_htN (sz : Sizes d) {τ : ℝ} (hτ : 0 ≤ τ) {t : ℕ → ℝ} (hrange : sz.RangeCond τ t) :
    ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ) := by
  filter_upwards [hrange] with n hn
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ (-1 + τ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have h2 : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  calc (1 - t n)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 : ℝ))⁻¹ := inv_anti₀ h2 (h1.trans hn)
    _ = ((sz.size n : ℕ) : ℝ) := by rw [Real.rpow_neg_one, inv_inv]

/-- **Target 3, the lift at one carrier** (private as the band `qtLift_lift`, `QtXiRoundLift.lean:640`: its binder `STXiRoundPTgL''` is concluded only through the family pin; public at the family level: `stXiRoundgL'_of_PTfam`; check shape `T2314_lift`): the lift `STXiRoundPTgL'' → STXiRoundgL'` at a
carrier (`lem:STOeq_Qt` `3_5:1362-1378`, the `N^{-C}`-net remark `3_5:1764`).  At the envelope controls `(XL♯, XLK♯)` the per-time pin gives `PrecPTL (Ξ̂ ≺ ζ♯)` over the
pairs; restricted to the diagonal (`QtLiftGen_diag_PT`), the one-sided net core (`qtLift_core_below`, `P = μ`, `V = Unit`, `Cv = 0`, `Ξ = G`, `ε = 1`, `A = 6 n_ + 18 + 2c`) gives
the uniform `PrecL` on the diagonal, `QtLiftGen_diag_to_pair` the one over the pairs, and `ζ♯ ≤ ζ` gives `STXiRoundgL'`.  The closeness on `G` reads the `𝓛` modulus
`lemDecCalELipG_loops` (`Lloop_subg`: `3 k N^{2k+6} N^c √|u-u'|`; `(η_t)⁻¹ ≤ N²` from `LemDecCalELip_envg`) and the `𝒦` modulus `hKLip` (`NQEndFlowGen_KLip`, `k = n_ ≥ 2`). -/
private theorem QtLiftGen_lift {sz : Sizes d} (Cm : Step2Mat sz) (μ : Measure sz.SeqΩ) {E : ℕ → ℝ} (hL : StepDecompGen_LoopForm Cm E)
    (hm : ∀ n, ‖Cm.m n‖ ≤ 1) {κm : ℝ} (hspec : DecayGen_Spec Cm.toFlowFM κm) {c : ℝ} (hc : 0 ≤ c)
    (hFM : LemDecCalELipG_FlowMod Cm μ c) (hsize : sz.SizeTendsto) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (ht1 : ∀ n, t n < 1) (htN : ∀ᶠ n in atTop, (1 - t n)⁻¹ ≤ ((sz.size n : ℕ) : ℝ))
    (hKLip : ∀ k : ℕ, 2 ≤ k → NQEndFlowGen_KLip Cm.toFlowFM t k) (hPT : STXiRoundPTgL'' Cm.toFlowFM μ s t) :
    STXiRoundgL' Cm.toFlowFM μ s t := by
  obtain ⟨hκm, hIm, hηeq⟩ := hspec
  obtain ⟨Hm, G, hLM, hG, hmod⟩ := lemDecCalELipG_flowMod_base hFM
  intro n_ p hn hp XL XLK hXL hXLK hXLp hXLKp
  have hsizeN : Tendsto sz.size atTop atTop := sz.tendsto_size hsize
  have hXL' : ∀ m n u, 1 ≤ nqFlowSharp t XL m n u := fun m n u => qtLift_sharp_one_le t XL m n u
  have hXLK' : ∀ m n u, 1 ≤ nqFlowSharp t XLK m n u := fun m n u => qtLift_sharp_one_le t XLK m n u
  have hXLp' : ∀ m, 1 ≤ m → STlenL n_ p m →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLg Cm.toFlowFM n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XL m n q.1.2) := fun m hm1 hl =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLg Cm.toFlowFM n w m ω) XL m hXL (hXLp m hm1 hl)
  have hXLKp' : ∀ m, 1 ≤ m → m ≤ n_ →
      PrecL sz μ (U := STPair s t) (fun n q ω => STXiLKg Cm.toFlowFM n q.1.1 m ω)
        (fun n q _ => nqFlowSharp t XLK m n q.1.2) := fun m hm1 hm' =>
    QtLiftGen_sharp_prec sz μ s t (fun n w ω => STXiLKg Cm.toFlowFM n w m ω) XLK m hXLK (hXLKp m hm1 hm')
  have hPT' := hPT n_ p hn hp (fun m n u => nqFlowSharp t XL m n u) (fun m n u => nqFlowSharp t XLK m n u)
    hXL' hXLK' hXLp' hXLKp'
  have hdiag := QtLiftGen_diag_PT sz μ s t (fun n w ω => STXiLKg Cm.toFlowFM n w n_ ω)
    (fun n u => (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p) hPT'
  have hmain : PrecL sz μ (U := fun n => TimeIcc s t n × Unit)
      (fun n w ω => STXiLKg Cm.toFlowFM n (w.1 : ℝ) n_ ω)
      (fun n w _ => (sz.Bctl n (w.1 : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (w.1 : ℝ) +
        STbootRHS 1 (fun m => nqFlowSharp t XL m n (w.1 : ℝ)) (fun m => nqFlowSharp t XLK m n (w.1 : ℝ))
          (sz.Bctl n (s n)) n_ p) := by
    refine qtLift_core_below (Ω := sz.SeqΩ) μ sz.size hsizeN s t (fun n => (hst n).le)
      (fun n => by linarith [hs0 n, ht1 n]) (fun _ => Unit) _ _ (((6 * n_ + 18 : ℕ) : ℝ) + 2 * c) 0
      (by positivity) le_rfl ?_ hdiag G hG (fun _ => 1) (fun _ => zero_le_one) ?_ ?_
    · -- `hcard`: `#Unit = 1 ≤ N^0`
      exact Eventually.of_forall fun n => by simp
    · -- `hlow`: `ζ♯ ≥ 1`
      exact Eventually.of_forall fun n q ω =>
        qtLift_zeta_one_le sz ht1 n_ p n (by omega) q.1.2.1 q.1.2.2
    · -- `hclose`
      have hQev := LemDecCalELip_envg (Cm := Cm) hκm hIm hηeq hsize htN (3 * (n_ : ℝ) + 1)
      have hQ : ∀ᶠ n in atTop, (Cm.eta n (t n))⁻¹ ≤ ((sz.size n : ℕ) : ℝ) ^ 2 := hQev.mono fun n h => h.2.2.1
      filter_upwards [hQev, lemDecCalELipG_loops hL hLM hc hmod hm ht1 hQ, hKLip n_ hn] with n hnum hloop hK
      obtain ⟨hM, hN1, hQn, -⟩ := hnum
      intro ω hω u u' hle hΔ v
      refine ⟨?_, ?_⟩
      · exact QtLiftGen_xiLK_close sz Cm.toFlowFM n hc ω (hs0 n) u'.2.1 hle u.2.2 (ht1 n) rfl hM hΔ
          (fun σ a => (hloop ω hω).1 u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ a)
          (fun σ a => hK u u' ((hs0 n).trans u.2.1) u.2.2 ((hs0 n).trans u'.2.1) u'.2.2 σ a)
      · have h1 := qtLift_zeta_mono sz ht1 hXL hXLK n_ p n u'.2.1 hle u.2.2
        have h2 := qtLift_zeta_one_le sz ht1 (XL := XL) (XLK := XLK) n_ p n (by omega) u.2.1 u.2.2
        change (sz.Bctl n (u' : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u' : ℝ) +
            STbootRHS 1 (fun m => nqFlowSharp t XL m n (u' : ℝ)) (fun m => nqFlowSharp t XLK m n (u' : ℝ))
              (sz.Bctl n (s n)) n_ p ≤
          2 * ((sz.Bctl n (u : ℝ)) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n (u : ℝ) +
            STbootRHS 1 (fun m => nqFlowSharp t XL m n (u : ℝ)) (fun m => nqFlowSharp t XLK m n (u : ℝ))
              (sz.Bctl n (s n)) n_ p)
        linarith
  have hpair := QtLiftGen_diag_to_pair sz μ s t (fun n w ω => STXiLKg Cm.toFlowFM n w n_ ω)
    (fun n u => (sz.Bctl n u) ^ (1 / 6 : ℝ) * nqFlowSharp t XLK n_ n u +
      STbootRHS 1 (fun m => nqFlowSharp t XL m n u) (fun m => nqFlowSharp t XLK m n u)
        (sz.Bctl n (s n)) n_ p)
    (fun n v u hsv hvu hut => qtLift_zeta_mono sz ht1 hXL hXLK n_ p n hsv hvu hut) hmain
  exact NQEndFlowGen_prec_of_le_right hpair fun n q ω =>
    qtLift_zeta_le sz ht1 hXL hXLK n_ p n (q.2.1.trans q.2.2.1) q.2.2.2

end Lift

/-! ## 4. Target 4: the case-(i) round and `stOeqQtgL'_of` over a carrier family

The family-premise table of the ticket: rows 1-13 are the premises of `stOeqQtRoundPTgL''_of` (`Chain/QEndB1Gen.lean:886`, T2498 table `:62-78` with Amend 1), read under the merged
names; row 15 `hKLip` (`NQEndFlowGen_KLipFam`, T2491 target 15); row 16 `hFM` (`QtBootGen_FlowModFam`, the merged U4s3 text).  `∃ c` of `hFM` comes after `(κ, ε, 𝔡)`; the
constants of T2498 (`𝔠_d`, `C4`, `C₆`, `Aof κ`) are the pin's own and stay before `(sz, z)`.  No drift or hierarchy premise is `∀ n`. -/

/-- **Target 3, `stXiRoundgL'_of_PTfam`** (the lift at the family level; band `qtLift_lift` inside `stXiRoundQt_holds`, `QtXiRoundLift.lean:714-730`): from the per-time pin `STOeqQtRoundPTgL''` of a
carrier family (U3s3c, `stOeqQtRoundPTgL''_of`) to the uniform-in-the-pair round `STXiRoundgL'`, with the constant `𝔠_d` of the pin.  The flow premises are the table rows 2, 3, 4, 12 (`hFlow`,
`hSpec`, `hL`, `hm`, `hT0`), the `𝒦` modulus (row 15, `hKLip`) and the `𝓛` modulus (row 16, `hFM`, `∃ c` after `(κ, ε, 𝔡)`); no probability premise is read. -/
theorem stXiRoundgL'_of_PTfam (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ) (E : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM)
    (hPT : STOeqQtRoundPTgL'' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0) :
    STIngRgL d STCaseI law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t) := by
  intro hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨𝔠d, h0, h1, H⟩ := hPT hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  obtain ⟨cH, hcH, hFMall⟩ := hFM κ ε 𝔡 hκ hε h𝔡
  refine ⟨𝔠d, h0, h1, ?_⟩
  intro 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hPT' := H 𝔠 sz z hflow s t hs hst ht hR hK hKw hLK hcon hStep2
  have hA := hFlow.1 sz κ ε 𝔠 𝔡 z hflow
  have ht1 : ∀ n, t n < 1 := fun n => (ht n).trans_lt (hFlow.2 sz κ ε 𝔠 𝔡 z hκ hflow n)
  obtain ⟨κm, hspec⟩ := hSpec sz κ ε 𝔠 𝔡 z hκ hflow
  obtain ⟨τ0, hτ0, hrange0⟩ := hT0 sz κ ε 𝔠 𝔡 z hκ hε hflow
  have hrange : sz.RangeCond τ0 t := nqEnd_rangeCond_mono sz le_rfl ht hrange0
  exact QtLiftGen_lift (mkM sz z) (law sz) (hL sz κ ε 𝔠 𝔡 z hκ hflow) (hm sz κ ε 𝔠 𝔡 z hκ hflow) hspec hcH
    (hFMall sz 𝔠 z hflow) hA.2.2.1 hs hst ht1 (QtLiftGen_htN sz hτ0.le hrange)
    (fun k hk => hKLip hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht k hk) hPT'

/-- **Target 4, `stXiRoundQtgL_of`** (band `stXiRoundQt_holds`, `QtXiRoundLift.lean:714`; check shape `T2314_stXiRoundQt_holds`): the case-(i) round `STXiRoundgL'` over `STIngRgL d STCaseI`
of a carrier family, with the constant `𝔠_d` of `stOeqQtRoundPTgL''_of` (T2498).  The uniform-in-the-pair conclusion follows from the per-time pin by `stXiRoundgL'_of_PTfam`;
`STCaseI` enters only through `stOeqQtRoundPTgL''_of`.  Paper-delta candidate `T2505b` (the flow modulus `c` of `𝓛` is a pinned `∃` after `(κ, ε, 𝔡)`; band `c = 1`). -/
theorem stXiRoundQtgL_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- ticket rows 1-6: the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- ticket rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- ticket row 8 (D1 of the non-alternating half, `∃ Ck` before `(sz, z)`), row 10 (R1, the pinned `Aof κ`), row 12 (the flow window)
    (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- ticket row 8 (D1 of the alternating endpoint, `∃ C4` before `(sz, z)`) and row 9 (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`, Amend 1; `B45Gen_Facts`)
    (hEK4 : QProxyG_KerEK4Fam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- ticket rows 15, 16: the `𝒦` modulus (U3s2c, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (U4s3, family row 16)
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
    STIngRgL d STCaseI law Flow (fun sz z => (mkM sz z).toFlowFM) T0
      (fun sz z s t => STXiRoundgL' (mkM sz z).toFlowFM (law sz) s t) := by
  exact stXiRoundgL'_of_PTfam d law Flow mkM T0 E hFlow hSpec hL hm hT0 hKLip hFM
    (stOeqQtRoundPTgL''_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK
      hExp hKL hKT hU hKerFam hR1 hT0 hEK4 hTh hB45)

/-- **Target 4, `stOeqQtgL'_of`** (band `stOeqQt'_holds`, `QtXiRoundLift.lean:736`; conclusion = the merged T2491 pin `STOeqQtgL'`, binding): `lem:STOeq_Qt`, R2*, uniformly in
the pair `(v, u)`, over a carrier family.  `stXiBootRgL'_of_round d STCaseI` (the bundle `QtBootGen_Hyp` from the premises: the law is a probability measure at a flow by
`hW`, `hLaw` and `isProbabilityMeasure_pathP`) applied to `stXiRoundQtgL_of`; the self-absorbing current-length term is removed by the deterministic bootstrap. -/
theorem stOeqQtgL'_of (d : ℕ) (law : ∀ sz : Sizes d, Measure sz.SeqΩ)
    (Flow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), Prop) (mkM : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2Mat sz)
    (T0 : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Hf : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), ℝ → sz.SeqΩ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (E lam' gK : ∀ (sz : Sizes d) (z : ℕ → ℂ), ℕ → ℝ)
    (Ψ : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (Aof : ℝ → ℝ)
    -- ticket rows 1-6: the premises of `gridGoodNgL_of` and `nqLinGoodgL_of`
    (hSE : STSEforLngL d STAny law Flow mkM Hf T0) (hFlow : Step2EventsGen_Flow d Flow T0)
    (hSpec : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∃ κm, DecayGen_Spec (mkM sz z).toFlowFM κm)
    (hL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_LoopForm (mkM sz z) (E sz z))
    (hW : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      StepDecompGen_WalkForm (mkM sz z) (lam' sz z) (Ψ sz z))
    (hLaw : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step2EventsGen_Law (mkM sz z) (law sz) (Hf sz z))
    (hC : ∀ (sz : Sizes d) (z : ℕ → ℂ), Step34Gen_LCompat (mkM sz z) (Hf sz z))
    (hWard : ∀ (sz : Sizes d) (z : ℕ → ℂ), DecayGen_WardPair (mkM sz z).toFlowFM)
    (hKcal : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      STKcalDecaygL (mkM sz z).toFlowFM)
    (hEK : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ s t : ℕ → ℝ,
      (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → STDecayLoopUgL (mkM sz z).toFlowFM (law sz) s t →
      ∀ k : ℕ, 2 ≤ k → ∀ σ : Fin k → Bool,
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STegtg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        (∀ l : ℕ, STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STksimLKg (mkM sz z) (Hf sz z) n (v : ℝ) ω l ⟨List.ofFn σ, List.ofFn a⟩)) ∧
        STEKDecaygL (law sz) s t (m := k) (fun n v ω (a : Fin k → Zd d (sz.L n)) =>
          STelklkg (mkM sz z) (Hf sz z) n (v : ℝ) ω ⟨List.ofFn σ, List.ofFn a⟩) ∧
        STEKDecaygL (law sz) s t (m := k + k) (fun n v ω (b : Fin (k + k) → Zd d (sz.L n)) =>
          STeeg (mkM sz z) (Hf sz z) n (v : ℝ) ω σ (fun i => b (Fin.castAdd k i)) (fun i => b (Fin.natAdd k i))))
    -- ticket rows 3, 4, 7, 11: the spectral data, the walk's variance law, the kernel class, the drift classes
    (hm : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z → ∀ n, ‖(mkM sz z).m n‖ ≤ 1)
    (hSeq : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ), (mkM sz z).S n = SB d (sz.L n) (lam' sz z n))
    (hS : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (a : Zd d (sz.L n)), ∑ b : Zd d (sz.L n), ‖(mkM sz z).S n a b‖ ≤ 1)
    (hRow : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ n, GridRepTailGen_Ker (mkM sz z).toFlowFM n)
    (hKK : ∀ (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) (w : ℝ) (k : ℕ) (σ : Fin k → Bool) (a : Fin k → Zd d (sz.L n)),
      (mkM sz z).KI n w (KLloopOf d (sz.L n) σ a) = (mkM sz z).K n w σ a)
    (hExp : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, ∀ (s' t' : ℕ → ℝ) (K' : ℕ → ℕ), HierDriftGen_Expand (mkM sz z) s' t' K' n)
    (hKL : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KLoop (mkM sz z) n)
    (hKT : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_KTwo (mkM sz z) n)
    (hU : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      ∀ᶠ n : ℕ in atTop, HierDriftGen_UStep (mkM sz z).toFlowFM n)
    -- ticket row 8 (D1 of the non-alternating half, `∃ Ck` before `(sz, z)`), row 10 (R1, the pinned `Aof κ`), row 12 (the flow window)
    (hKerFam : NQGoodGen_KerNALFam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hR1 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → Flow sz κ ε 𝔠 𝔡 z →
      1 ≤ Aof κ ∧ ∀ n, 0 ≤ gK sz z n * sz.lam n ∧ gK sz z n ^ 2 ≤ sz.lam n ^ 2 ∧ sz.lam n ^ 2 ≤ Aof κ * gK sz z n ^ 2)
    (hT0 : ∀ (sz : Sizes d) (κ ε 𝔠 𝔡 : ℝ) (z : ℕ → ℂ), 0 < κ → 0 < ε → Flow sz κ ε 𝔠 𝔡 z →
      ∃ τ : ℝ, 0 < τ ∧ sz.RangeCond τ (T0 sz z))
    -- ticket row 8 (D1 of the alternating endpoint, `∃ C4` before `(sz, z)`) and row 9 (the `Θ`-decay class, `∃ C₆` after `(𝔡, κ)`, Amend 1; `B45Gen_Facts`)
    (hEK4 : QProxyG_KerEK4Fam d Flow (fun sz z => (mkM sz z).toFlowFM) gK)
    (hTh : ∀ 𝔡 : ℝ, 0 < 𝔡 → ∀ κ : ℝ, 0 < κ → ∃ C₆ : ℝ, 0 < C₆ ∧ ∀ (sz : Sizes d) (ε 𝔠 : ℝ) (z : ℕ → ℂ),
      Flow sz κ ε 𝔠 𝔡 z → Step5KerGen_ThDecay (mkM sz z).toFlowFM (gK sz z) 𝔡⁻¹ C₆)
    (hB45 : B45Gen_Facts d Flow (fun sz z => (mkM sz z).toFlowFM))
    -- ticket rows 15, 16: the `𝒦` modulus (U3s2c, `NQEndFlowGen_KLipFam`) and the `𝓛` modulus (U4s3, family row 16)
    (hKLip : NQEndFlowGen_KLipFam d Flow (fun sz z => (mkM sz z).toFlowFM) T0) (hFM : QtBootGen_FlowModFam d law Flow mkM) :
    STOeqQtgL' d law Flow (fun sz z => (mkM sz z).toFlowFM) T0 := by
  refine stXiBootRgL'_of_round d STCaseI law Flow mkM T0 ⟨hFlow, ?_, ?_, hT0, hFM⟩
    (stXiRoundQtgL_of d law Flow mkM T0 Hf E lam' gK Ψ Aof hSE hFlow hSpec hL hW hLaw hC hWard hKcal hEK hm hSeq hS hRow hKK hExp hKL hKT hU
      hKerFam hR1 hT0 hEK4 hTh hB45 hKLip hFM)
  · intro sz κ ε 𝔠 𝔡 z hκ hz
    have : IsProbabilityMeasure (mkM sz z).Pp := by
      rw [(hW sz κ ε 𝔠 𝔡 z hκ hz).2.1]; exact isProbabilityMeasure_pathP _
    exact NQEndFlowGen_isProb (hLaw sz z)
  · intro sz κ ε 𝔠 𝔡 z hκ hz
    exact ⟨⟨E sz z, hL sz κ ε 𝔠 𝔡 z hκ hz⟩, hm sz κ ε 𝔠 𝔡 z hκ hz, hSpec sz κ ε 𝔠 𝔡 z hκ hz⟩

/-! ## 5. The band re-derivation of `stOeqQt'_holds` (every `d`)

The band family `(seqP, STFlow, bandStep2Mat · (STflowE ·), lemT)`, `Hf = seqHflow`, `E = STflowE`, `lam' = sz.lam`, `Ψ = 0`, `gK = sz.lam`, `Aof = 1`: rows 1-13 are the discharges
of `stOeqQtRoundPTgL''_band` (`Chain/QEndB1Gen.lean`); row 15 `hKLip` is `nqEndFlowGen_kLip_band` (`stKloop_lip`), row 16 `hFM` is `lemDecCalELipG_flowMod_band` at `c = 1`
(`Hm = seqHflow`, `G = contGood`).  No hypothesis is left open: the pins are theorems at every `d ≥ 3`. -/

/-! ## 6. Compiled nonempty instances (`d = 3`)

Data of the merged band instances (`Induction/Defs.lean:403-440`, `Induction/Step34Pins.lean:843-944`): `sz0` (`L = 4(n+1)`, `W = (2(n+1))^5`, `lam = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`,
`N = 2^21`), the flow `z0` (`z_n = 1/2 + i N_n^{-4/5}`, `flow_z0` at `(κ, ε, 𝔠, 𝔡) = (1/10, 1/10, 1/6, 1/10)`), `s ≡ 0`, `t ≡ 1/16` (`t ≤ lemT z0`, `STCaseI`: `sz0_caseI`; `(con_st_ind)`
for every `𝔠_d > 0`: `sz0_con`), `C_d = 1`.  What stays a hypothesis of an example is a stochastic premise that is another gate's pin: `STLKgL s`, `STStep2ConclgL` (the premises of
`STIngRgL`; `STKboundgL`, `STKwardgL` are theorems of the flow), the pair hypotheses `Ξ̂ ≺ 1` of the pin, and the per-time pin `STXiRoundPTgL''` where the lift is applied directly. -/

end RBM.BA

end
