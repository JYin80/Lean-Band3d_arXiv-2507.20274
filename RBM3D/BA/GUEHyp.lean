/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.GUELLBA
import RBM3D.BA.GUEEq729BA
import RBM3D.BA.GUEPathBoundsBA
import RBM3D.BA.GUETwistBA2
import RBM3D.Universality.GUEPhase.Eq729B

/-!
# BA-C5 row d: (7.29), the (7.47) step and the BA producers of the §7.2 random layer

Ticket T2519 (row d, targets 14-17; DECISIONS §344, §346, §364; Amends 1-5; the texts
`T2519_ProdBA`, `T2519_LLBA`, `T2519_QueBA`, `T2519_KFamBA`, `T2519_PBBA`, `T2519_EdRealBA`,
`T2519_FlowEtaBA`, `T2519_KdiscBA`, `T2519_HoffBA` signed by `docs/reports/T2519-1a-audit.md`,
Amend 3).  New BA leaf: no merged file is edited.  Band twin: `Universality/GUEPhase/Eq729B.lean`
(`Eq729B_perN:140`, `gueGrid_eq729:622`, `Eq729B_eq747_of_eq729:1077`, `Eq729B_derived:1125`,
`Eq729B_eq747_of_inputs:1221`) and `RandomLayerB.lean` (`RandomLayerB_prod_band:400`,
`_LL_band:427`, `_Que_band:439`).  Paper: the GUE phase of Thm 2.4
(`paper/tex/1_2_Intro_model_result.tex:566-570`, "essentially identical to [YY_25, Theorem 2.6]"),
(7.26)-(7.29) and the (7.47) step of [YY_25] §7.2.

* §1 the vocabulary `Eq729BA_eqErr`, `Eq729BA_Concl`: (7.29) at `t₀` in the loss form `N^δ ((N
  η_{t₀})^{-3} + I₀(t₁))`, the 2-loop primitive being `kTwoGUEBA`.
* §2 `Eq729B_perNBA`: the recursion of `eq729_one_stepBA` (C4 b) closed by a discrete Grönwall.
* §3-§4 `gueGrid_eq729BA`: (7.29) at `t₀` on the BA grid: the one-loop law is
  `gueGrid_expect_oneLoopBA'` (C4 a, Amend 4) with the twisted 1-loop law `gueGrid_twistBA` (row
  b′) as `hoff`, the K-bounds are `Hyp_Kt_detDomBA`, `Hyp_Kt_oneBA` (row a), the failure events
  are the three `lk` fields of `GUEPathBoundsBA` (row a), the initial term is `STExp2gL` (the
  third conjunct of `BAMO`).
* §5-§8 the (7.47) step: the flow datum `Eq729BA_{t0,g,E,t1,m}` of `z`, `GUEHyp_flowQ` (the facts
  of `ba_flowG` at the QUE scale, `t₀ ≥ 1/2` eventually), `Eq729B_derivedBA`, the law (7.26) at
  the last grid step (`GUEHyp_law726`), the symmetry of the BA profile, `Eq729B_eq747_of_eq729BA`
  (the bridges `kTwoGUEBA_bridge_pm/pp`), `Eq729B_eq747_of_inputsBA`.
* §9 the producers: `ba_prodG`, `ba_LLG` (from `oull_of_pathBoundsBA`, `BA/GUELLBA`), `ba_QueG` at
  the exact types of `T2519_ProdBA BAKFam BAPB`, `T2519_LLBA BAPB`, `T2519_QueBA BAKFam BAPB`.
* Instances (§10 onwards): every endpoint theorem at `d = 3`, the class sequence `S0` of
  `BA/UNPins`.

Departures from the band statements: the flow datum is `(g, E, m)` with `BAReal` at every `n` and
the coupling window `0 < g n ≤ Λ` eventually (Amend 4); the loop primitive is `kTwoGUEBA`, the
local-law centre is `M^{(B)} ⊗ 1`; `n₀ ≥ 4` (Amend 1); the Lemma 2.8 facts are `ba_flowG`'s (`cT ≤
t₀`, `1 - t₀ ≤ Im z/c`) instead of `1/16 ≤ t₀`, which holds eventually at the QUE scale (`t₀ ≥
1/2`); `hell` is in the form `L^d (1 - t₁) ≤ 2 g²` of the K lemmas of row a.  Helpers the ticket
does not pin are `private` or carry the prefix `GUEHyp_`; the generic real-variable lemmas of
`Eq729B` are read by name, its private helpers by `open private`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open private GUEPathBoundsBA_m_eq GUEPathBoundsBA_gueHBA_zero from RBM3D.BA.GUEPathBoundsBA
open private PathBounds_map_eval0 from RBM3D.Universality.GUEPhase.PathBounds
open private GUEEq729BA_eta_pos GUEEq729BA_eta_le from RBM3D.BA.GUEEq729BA
open private GUELLBA_integral_transfer GUELLBA_green_scale from RBM3D.BA.GUELLBA
open private GUEPhaseGrid_loopL_smul_mul from RBM3D.Universality.GUEPhase.Grid
open private GUEKPrim_QJ GUEKPrim_r0_norm from RBM3D.BA.GUEKPrim


noncomputable section

namespace RBM.BA

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase RBM.Endpoints
open scoped NNReal ENNReal

variable {d : ℕ}

/-! ## 1. The vocabulary of (7.29) at block Anderson -/

/-- `‖𝔼 𝓛_{t₀,(+,σ₂),(a,b)} - 𝒦̃_{t₀,(+,σ₂),(a,b)}‖` at the last grid step of the BA grid path (twin of `Eq729B_eqErr`; `𝒦̃` is the 2-loop
primitive `kTwoGUEBA` at the flow datum `(g, E, m)`). -/
def Eq729BA_eqErr (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) (n : ℕ) (σ₂ : Bool) (a b : Zd d (sz.L n)) : ℝ :=
  ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n (K n) ω))
        (ztOf (m n) (E n) (t0 n)) ⟨[true, σ₂], [a, b]⟩ ∂(Pgue (sz.withLam 0))) -
    kTwoGUEBA d (sz.L n) (sz.W n) (g n) (E n) (m n) (t1 n) (t0 n) true σ₂ a b‖

/-- (7.29) at `t₀` at block Anderson, loss form `N^δ ((N η_{t₀})^{-3} + I₀(t₁))` (twin of `Eq729B_Concl`; `I₀` is `Eq729B_initTerm`). -/
def Eq729BA_Concl (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ) : Prop :=
  ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ (σ₂ : Bool) (a b : Zd d (sz.L n)),
    Eq729BA_eqErr sz g E t1 t0 m K n σ₂ a b ≤
      Nsz sz n ^ δ * ((Nsz sz n * etaOf (m n) (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n))

/-! ## 2. The recursion closed by a discrete Grönwall (target 14, `Eq729B_perNBA`) -/

/-- **The recursion closed by a discrete Grönwall at one size parameter** (twin of `Eq729B_perN`, `Eq729B:140`, with `eq729_one_stepBA`):
at the last grid step, `‖e_K‖ ≤ exp((t₀ - t₁)·2NρΛ) (B₀ + K c)`, `N = sz.size n`, `B₀` a bound of the initial error `e₀`; the flow datum is
`(g, E, m)` with `0 < Im m`, `‖m‖ ≤ 1`. -/
theorem Eq729B_perNBA (sz : Sizes d) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (K : ℕ → ℕ) {n : ℕ}
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hm : 0 < (m n).im) (hm1 : ‖m n‖ ≤ 1) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1) (hKN : K n ≠ 0)
    {Λ ρ p B0 : ℝ}
    (hΛ : Λ = (((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹) (hΛ1 : Λ ≤ 1)
    (hρ0 : 0 ≤ ρ) (hρΛ : ρ * Λ ≤ 1) (hp0 : 0 ≤ p)
    (hMΔ : ((sz.size n : ℕ) : ℝ) * gridStep t1 t0 K n ≤ 1)
    (hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ)
    (hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w, ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 2)
    (hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s)
    (hX : ∀ k < K n, ∀ a,
      ‖(∫ ω, eq729FBA sz g t1 t0 E m K n k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ρ * Λ ^ 2)
    {B : Set (PathΩ (sz.withLam 0))} (hB : Pgue (sz.withLam 0) B ≤ ENNReal.ofReal p)
    (hg1 : ∀ ω ∉ B, ∀ k < K n, ∀ σ a, ‖eq729FBA sz g t1 t0 E m K n k ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ ρ * Λ)
    (hg2 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 x y, ‖eq729FBA sz g t1 t0 E m K n k ω ⟨[s1, s2], [x, y]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Λ ^ 2)
    (hg3 : ∀ ω ∉ B, ∀ k < K n, ∀ s1 s2 s3 x y w, ‖eq729FBA sz g t1 t0 E m K n k ω ⟨[s1, s2, s3], [x, y, w]⟩
      - Kt n (gridTime t1 t0 K n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Λ ^ 3)
    (hinit : ∀ s1 s2 x y, ‖eq729eBA sz g t1 t0 E m K Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ B0)
    (s1 s2 : Bool) (a1 a2 : Zd d (sz.L n)) :
    ‖eq729eBA sz g t1 t0 E m K Kt n (K n) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      Real.exp ((t0 n - t1 n) * (2 * ((sz.size n : ℕ) : ℝ) * (ρ * Λ))) *
        (B0 + (K n : ℝ) * eq729c ((sz.size n : ℕ) : ℝ) ρ Λ p (gridStep t1 t0 K n)) := by
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  set Δ : ℝ := gridStep t1 t0 K n with hΔ
  set r : ℝ := 2 * N * (ρ * Λ) with hr
  set c : ℝ := eq729c N ρ Λ p Δ with hc
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hΔ0 : 0 ≤ Δ := eq729_step_nonneg ht10
  have hη0 : 0 < etaOf (m n) (t0 n) := mul_pos (by linarith) hm
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]; exact inv_nonneg.2 (mul_nonneg hN0 hη0.le)
  have hr0 : 0 ≤ r := by positivity
  have hc0 : 0 ≤ c := Eq729B_c_nonneg hN0 hρ0 hΛ0 hp0 hΔ0
  have hB00 : 0 ≤ B0 := (norm_nonneg _).trans (hinit true true 0 0)
  have hq1 : 1 ≤ 1 + Δ * r := by nlinarith
  have claim : ∀ k, k ≤ K n → ∀ s1 s2 x y,
      ‖eq729eBA sz g t1 t0 E m K Kt n k ⟨[s1, s2], [x, y]⟩‖ ≤ (1 + Δ * r) ^ k * (B0 + k * c) := by
    intro k
    induction k with
    | zero =>
      intro _ s1 s2 x y
      simpa using hinit s1 s2 x y
    | succ k ih =>
      intro hk s1 s2 x y
      have hk' : k < K n := hk
      have hstep := eq729_one_stepBA sz g t1 t0 E m K n Kt hm hm1 ht1 ht10 ht0 hΛ hΛ1 hρ0 hρΛ hp0 hMΔ hK2b hK3b hKd
        hk' (hX k hk') hB (fun ω hω => hg1 ω hω k hk') (fun ω hω => hg2 ω hω k hk')
        (fun ω hω => hg3 ω hω k hk') (ih hk'.le) s1 s2 x y
      refine hstep.trans ?_
      have hpow : 1 ≤ (1 + Δ * r) ^ (k + 1) := one_le_pow₀ hq1
      have hA : 0 ≤ B0 + k * c := by positivity
      rw [Nat.cast_succ]
      calc (1 + Δ * r) * ((1 + Δ * r) ^ k * (B0 + k * c)) + c
          = (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + c := by ring
        _ ≤ (1 + Δ * r) ^ (k + 1) * (B0 + k * c) + (1 + Δ * r) ^ (k + 1) * c := by
            gcongr; exact le_mul_of_one_le_left hc0 hpow
        _ = (1 + Δ * r) ^ (k + 1) * (B0 + (k + 1) * c) := by ring
  refine (claim (K n) le_rfl s1 s2 a1 a2).trans ?_
  have hexp : (1 + Δ * r) ^ (K n) ≤ Real.exp ((t0 n - t1 n) * r) := by
    have h1 : 1 + Δ * r ≤ Real.exp (Δ * r) := by linarith [Real.add_one_le_exp (Δ * r)]
    calc (1 + Δ * r) ^ (K n) ≤ Real.exp (Δ * r) ^ (K n) := pow_le_pow_left₀ (by linarith) h1 _
      _ = Real.exp ((K n : ℝ) * (Δ * r)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp ((t0 n - t1 n) * r) := by rw [← mul_assoc, hΔ, eq729_KΔ hKN]
  exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-! ## 3. Inputs at the size parameter `n` (the generic helpers of `Eq729B` are read by name) -/

/-- **A deterministic `≺` is a deterministic bound** (twin of `det_of_prec`, `Endpoints:443`, at an arbitrary probability law): the left side of
`STExp2gL` does not depend on `ω`, so `P(univ) = 1 > N^{-1}` and for `N > 1` the bad set is empty. -/
private theorem GUEHyp_det_of_prec (sz : Sizes d) (μ : Measure sz.SeqΩ) [IsProbabilityMeasure μ] (hsz : sz.SizeTendsto)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (hξ : ∀ n u ω ω', ξ n u ω = ξ n u ω')
    (hζ : ∀ n u ω ω', ζ n u ω = ζ n u ω') (h : StochDomAt μ sz.size ξ ζ) {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ n in atTop, ∀ u ω, ξ n u ω ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
  filter_upwards [h τ hτ 1 one_pos, hsz.eventually_gt_atTop 1] with n hn hN1
  intro u ω
  by_contra hlt
  push Not at hlt
  have huniv : badSetAt sz.size ξ ζ τ n = Set.univ := by
    ext ω'
    simp only [Set.mem_univ, iff_true]
    exact ⟨u, by rw [hζ n u ω' ω, hξ n u ω' ω]; exact hlt⟩
  rw [huniv, measure_univ] at hn
  have hlt1 : ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    have : ((sz.size n : ℕ) : ℝ) ^ (-(1 : ℝ)) = (((sz.size n : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    rw [this]
    exact inv_lt_one_of_one_lt₀ hN1
  exact absurd hn (not_le.mpr hlt1)

/-- **The only transfer between carriers at step `0`** (twin of `Eq729B_transfer`, `Eq729B:569`): the grid path at step `0` is the BA flow matrix at
`t₁` (`GUEPathBoundsBA_gueHBA_zero`) and the step-`0` marginal of `Pgue (sz.withLam 0)` is `seqP (sz.withLam 0)`. -/
private theorem GUEHyp_transfer (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (z : ℂ) (I : LoopIdx (Zd d (sz.L n))) :
    ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n 0 ω)) z I ∂(Pgue (sz.withLam 0)) =
      ∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (sz.seqHflowBA g n (t1 n) ω)) z I
        ∂(Sizes.seqP (sz.withLam 0)) := by
  have hc : Measurable fun M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ =>
      loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M) z I :=
    (RBM.Gauss.walk_measurable_loopL d (sz.L n) (sz.W n) z I).comp (RBM.Gauss.walk_measurable_blockMat d (sz.L n) (sz.W n))
  have hHf : Measurable (sz.seqHflowBA g n (t1 n)) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    unfold Sizes.seqHflowBA
    simp only [Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply]
    exact measurable_const.add (Sizes.measurable_seqHflow_entry (sz.withLam 0) n (t1 n) i j)
  simp_rw [GUEPathBoundsBA_gueHBA_zero sz g t1 t0 K n]
  rw [← PathBounds_map_eval0 (sz.withLam 0), integral_map (measurable_pi_apply (0 : ℕ)).aemeasurable (hc.comp hHf).aestronglyMeasurable]

/-- The failure event of `hP.1 l` at level `τ`, size index `n` (twin of the private `Eq729B_Bad`, `Eq729B:594`). -/
private def GUEHyp_Bad (sz : Sizes d) (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ) (n0 l : ℕ)
    (τ : ℝ) (n : ℕ) : Set (PathΩ (sz.withLam 0)) :=
  {ω | ∃ p : Fin (gueGridK sz n0 n + 1) × (Fin l → Bool) × (Fin l → Zd d (sz.L n)),
    ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹ ^ l <
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) (loopOf p.2.1 p.2.2) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n p.1) (loopOf p.2.1 p.2.2)‖}

private theorem GUEHyp_not_bad {sz : Sizes d} {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} {Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ}
    {n0 l n : ℕ} {τ : ℝ} {ω : PathΩ (sz.withLam 0)} (hω : ω ∉ GUEHyp_Bad sz g E t1 t0 m Kt n0 l τ n) {k : ℕ}
    (hk : k ≤ gueGridK sz n0 n) (σ : Fin l → Bool) (a : Fin l → Zd d (sz.L n)) :
    ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf σ a) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf σ a)‖
      ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ l := by
  by_contra h
  exact hω ⟨(⟨k, Nat.lt_succ_of_le hk⟩, σ, a), lt_of_not_ge h⟩

/-! ## 4. (7.29) at `t₀` on the BA grid (target 14, `gueGrid_eq729BA`) -/

/-- **(7.29) at `t₀` on the GUE-phase grid at block Anderson** ([YY_25] §7.2; twin of `gueGrid_eq729`, `Eq729B:622`), `σ = (+, σ₂)`, in the loss form
`N^δ ((N η_{t₀})^{-3} + I₀(t₁))` (`Eq729BA_Concl`; `I₀` the right side of `STExp2gL`, `Eq729B_initTerm`).  The flow datum is `(g, E, m)` with `BAReal`
at every `n` and the coupling window `0 < g n ≤ Λ` eventually (Amend 4 item 3); `h730`, `hscale` are in `etaOf (m n) t₀` (`T2519_FlowEtaBA`), `hell` is the
zero-mode premise in the form `L^d (1 - t₁) ≤ 2 g²` of the K lemmas of row a; the primitive family `Kt` is that of `BAKFam` (`hKinit`, `hK`, `hK2`, guarded by
`0 < g n`); `hB` is the initial term (the third conjunct of `BAMO`), `hP` the path bounds at `n₀ ≥ 4` (row c).  The one-loop law is
`gueGrid_expect_oneLoopBA'` with the twisted 1-loop law `gueGrid_twistBA` (row b′) as `hoff`; the K-bounds are `Hyp_Kt_detDomBA`, `Hyp_Kt_oneBA` (row a). -/
theorem gueGrid_eq729BA (hd : 3 ≤ d) (sz : Sizes d) {κ τU Λ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) (hτU : 0 < τU) (n0 : ℕ) (hn0 : 4 ≤ n0)
    {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hsize : Tendsto sz.size atTop atTop)
    (hr : ∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) (hlam : ∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ)
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1)
    (h730 : ∀ᶠ n in atTop, t0 n - t1 n ≤ Nsz sz n ^ (-τU) * etaOf (m n) (t0 n))
    (hscale : ∀ᶠ n in atTop, (Nsz sz n * etaOf (m n) (t0 n))⁻¹ ≤ Nsz sz n ^ (-τU))
    (hell : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * g n ^ 2)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < g n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (t1 n) I = BAKsol d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)))
        (PropSpin (m n)) (t1 n) I)
    (hK : ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length →
      I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I) (Set.Icc (t1 n) (t0 n)) s)
    (hK2 : ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
      Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA d (sz.L n) (sz.W n) (g n) (E n) (m n) (t1 n) s σ₁ σ₂ a b)
    (hB : STExp2gL (baFM sz g E) (Sizes.seqP (sz.withLam 0)) t1)
    (hP : GUEPathBoundsBA sz g E t1 t0 m (gueGridK sz n0) n0 Kt) :
    Eq729BA_Concl sz g E t1 t0 m (gueGridK sz n0) := by
  intro δ hδ
  have hm0 : ∀ n, 0 < (m n).im := fun n => (hr n).1.1
  have hm1 : ∀ n, ‖m n‖ ≤ 1 := fun n => BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) (hr n).1
  set τ : ℝ := min (δ / 4) τU with hτdef
  have hτ : 0 < τ := lt_min (by positivity) hτU
  have hττU : τ ≤ τU := min_le_right _ _
  have hτδ : τ ≤ δ / 4 := min_le_left _ _
  have hKne := gueGridK_ne_zero sz n0
  have hKone : ∀ n, 0 < g n → ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ σ a, Kt n s ⟨[σ], [a]⟩ = mSigOf (m n) σ :=
    fun n hg s hs σ a => Hyp_Kt_oneBA sz hκ n0 (by omega) Kt hr ht1 ht10 ht0 hKinit hK n hg hs σ a
  have hKmem : ∀ n k, k ≤ gueGridK sz n0 n → gridTime t1 t0 (gueGridK sz n0) n k ∈ Set.Icc (t1 n) (t0 n) :=
    fun n k hk => eq729_time_mem (ht10 n) (hKne n) hk
  have hKbd := Hyp_Kt_detDomBA hd sz hκ hΛ hτU n0 hr hlam ht1 ht10 ht0 hsize h730 hell Kt hKinit hK
  have hoff := gueGrid_twistBA d hd sz κ Λ hκ hΛ g E t1 t0 m n0 Kt hsize hn0 hlam hr ht1 ht10 ht0 hKone
    (fun ε hε => (hKbd ε hε).mono fun n hn s hs I hI h2 h4 => hn s hs I hI h2 (by omega)) hP
  -- the 1-loop input of Lemma 5.15, from `hP.1 1` (the `+` 1-loops, `K̃ = m`)
  have h1 : StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (gueGridK sz n0 n + 1) × Zd d (sz.L n)) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n p.1)) ⟨[true], [p.2]⟩ - m n‖)
      (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n p.1))⁻¹) := by
    intro τ' hτ' D hD
    filter_upwards [hP.1 1 le_rfl (by omega) τ' hτ' D hD, hlam] with n hn hlamn
    refine le_trans (measure_mono ?_) hn
    rintro ω ⟨⟨k, a⟩, hlt⟩
    refine ⟨(k, (fun _ => true), (fun _ => a)), ?_⟩
    have hk : (k : ℕ) ≤ gueGridK sz n0 n := Nat.lt_succ_iff.1 k.isLt
    have hKt := hKone n hlamn.1 _ (hKmem n k hk) true a
    have hloop : (loopOf (fun _ : Fin 1 => true) (fun _ : Fin 1 => a) : LoopIdx (Zd d (sz.L n))) = ⟨[true], [a]⟩ := rfl
    have hmσ : mSigOf (m n) true = m n := by simp [mSigOf]
    change ((sz.size n : ℕ) : ℝ) ^ τ' * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ 1 <
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 (gueGridK sz n0) n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 (gueGridK sz n0) n k)) (loopOf (fun _ : Fin 1 => true) (fun _ => a)) -
        Kt n (gridTime t1 t0 (gueGridK sz n0) n k) (loopOf (fun _ : Fin 1 => true) (fun _ => a))‖
    rw [hloop, hKt, hmσ, pow_one]
    exact hlt
  have hX := gueGrid_expect_oneLoopBA' d hd sz κ Λ hκ hΛ g E t1 t0 m (gueGridK sz n0) hsize hlam hr ht1 ht10 ht0 hKne h1 hoff τ hτ
  have hb1 := hP.1 1 le_rfl (by omega) τ hτ 12 (by norm_num)
  have hb2 := hP.1 2 (by norm_num) (by omega) τ hτ 12 (by norm_num)
  have hb3 := hP.1 3 (by norm_num) (by omega) τ hτ 12 (by norm_num)
  have hsz' : sz.SizeTendsto := tendsto_natCast_atTop_iff.mpr hsize
  have hin := GUEHyp_det_of_prec sz (Sizes.seqP (sz.withLam 0)) hsz' (U := fun n => (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
    (ξ := fun n p _ => ‖(∫ ω, (baFM sz g E).L n (t1 n) p.1 p.2 ω ∂(Sizes.seqP (sz.withLam 0))) - (baFM sz g E).K n (t1 n) p.1 p.2‖)
    (ζ := fun n _ _ => Eq729B_initTerm sz n (t1 n)) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) hB hτ
  filter_upwards [h730, hscale, hell, hKbd τ hτ, hX, hb1, hb2, hb3, hin, hlam,
    hsize.eventually (eventually_le_rpow 56 hτ)] with n h730n hscalen hellN hKbn hXn hb1n hb2n hb3n hinn hlamn hN56
  intro σ₂ a b
  change Eq729BA_eqErr sz g E t1 t0 m (gueGridK sz n0) n σ₂ a b ≤
    ((sz.size n : ℕ) : ℝ) ^ δ * ((((sz.size n : ℕ) : ℝ) * etaOf (m n) (t0 n))⁻¹ ^ 3 + Eq729B_initTerm sz n (t1 n))
  -- the size parameter `n`: scales
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN9 : (9 : ℝ) ≤ N := by rw [hNdef]; exact_mod_cast Eq729B_nine_le_size sz hd n
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0n0 : 0 ≤ t0 n := (ht1 n).trans (ht10 n)
  set η0 : ℝ := etaOf (m n) (t0 n) with hη0
  have hη0pos : 0 < η0 := GUEEq729BA_eta_pos (hm0 n) (ht0 n)
  have hη01 : η0 ≤ 1 := by
    rw [hη0]; unfold etaOf
    have him : (m n).im ≤ 1 := (Complex.im_le_norm (m n)).trans (hm1 n)
    have h0 : 0 ≤ 1 - t0 n := by linarith [ht0 n]
    have h1' : 1 - t0 n ≤ 1 := by linarith
    calc (1 - t0 n) * (m n).im ≤ 1 * 1 := mul_le_mul h1' him (hm0 n).le zero_le_one
      _ = 1 := one_mul 1
  set Lm : ℝ := (N * etaOf (m n) (t0 n))⁻¹ with hLm
  have hLmdef : Lm = (N * η0)⁻¹ := rfl
  have hLmpos : 0 < Lm := by rw [hLmdef]; positivity
  have hLmτ : Lm ≤ N ^ (-τU) := hscalen
  have hLm1 : Lm ≤ 1 := hLmτ.trans (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith))
  set ρ : ℝ := N ^ τ with hρ
  have hρ1 : 1 ≤ ρ := Real.one_le_rpow hN1 hτ.le
  have hρ0 : 0 ≤ ρ := by linarith
  have hρτ : ρ * N ^ (-τU) ≤ 1 := by
    rw [hρ, ← Real.rpow_add hN0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hρΛ : ρ * Lm ≤ 1 := (mul_le_mul_of_nonneg_left hLmτ hρ0).trans hρτ
  have hinvs : ∀ s ∈ Set.Icc (t1 n) (t0 n), (N * etaOf (m n) s)⁻¹ ≤ Lm := fun s hs =>
    inv_anti₀ (mul_pos hN0 hη0pos) (mul_le_mul_of_nonneg_left (GUEEq729BA_eta_le (hm0 n) hs.2) hN0.le)
  have hinvs0 : ∀ s ∈ Set.Icc (t1 n) (t0 n), 0 ≤ (N * etaOf (m n) s)⁻¹ := fun s hs =>
    (inv_pos.2 (mul_pos hN0 (GUEEq729BA_eta_pos (hm0 n) (lt_of_le_of_lt hs.2 (ht0 n))))).le
  have hinvsn : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ k : ℕ, (N * etaOf (m n) s)⁻¹ ^ k ≤ Lm ^ k :=
    fun s hs k => pow_le_pow_left₀ (hinvs0 s hs) (hinvs s hs) k
  -- `K̃` on 2- and 3-loops
  have hK2b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y, ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Lm := fun s hs s1 s2 x y => by
    have h := hKbn s hs ⟨[s1, s2], [x, y]⟩ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
    have h' : ‖Kt n s ⟨[s1, s2], [x, y]⟩‖ ≤ N ^ τ * (N * etaOf (m n) s)⁻¹ := by simpa [LoopIdx.length] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hinvs s hs) hρ0)
  have hK3b : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 s3 x y w,
      ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Lm ^ 2 := fun s hs s1 s2 s3 x y w => by
    have h := hKbn s hs ⟨[s1, s2, s3], [x, y, w]⟩ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
    have h' : ‖Kt n s ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ N ^ τ * (N * etaOf (m n) s)⁻¹ ^ 2 := by
      simpa [LoopIdx.length] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (hinvsn s hs 2) hρ0)
  have hKd : ∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ s1 s2 x y,
      HasDerivWithinAt (fun s => Kt n s ⟨[s1, s2], [x, y]⟩)
        (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) ⟨[s1, s2], [x, y]⟩) (Set.Icc (t1 n) (t0 n)) s := fun s hs s1 s2 x y =>
    hK n hlamn.1 s hs _ rfl (by simp [LoopIdx.length]) (by simp [LoopIdx.length]; omega)
  -- Lemma 5.15 at the grid times
  have hX' : ∀ k < gueGridK sz n0 n, ∀ a,
      ‖(∫ ω, eq729FBA sz g t1 t0 E m (gueGridK sz n0) n k ω ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤ ρ * Lm ^ 2 := by
    intro k hk a
    have := hXn (⟨k, by omega⟩, a)
    exact this.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  -- the bad event
  set B : Set (PathΩ (sz.withLam 0)) := GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n ∪ GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n
    ∪ GUEHyp_Bad sz g E t1 t0 m Kt n0 3 τ n with hBdef
  have hNrpow : N ^ (-(12 : ℝ)) = 1 / N ^ 12 := by
    rw [Real.rpow_neg hN0.le, show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  have hBm : Pgue (sz.withLam 0) B ≤ ENNReal.ofReal (3 / N ^ 12) := by
    have hb1' : Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb1n
    have hb2' : Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb2n
    have hb3' : Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 3 τ n) ≤ ENNReal.ofReal (N ^ (-(12 : ℝ))) := hb3n
    have h12 : Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n ∪ GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n)
        ≤ Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n) + Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n) :=
      measure_union_le _ _
    have h123 : Pgue (sz.withLam 0) B ≤ Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n ∪ GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n)
        + Pgue (sz.withLam 0) (GUEHyp_Bad sz g E t1 t0 m Kt n0 3 τ n) := measure_union_le _ _
    refine (h123.trans (add_le_add h12 le_rfl)).trans ?_
    refine (add_le_add (add_le_add hb1' hb2') hb3').trans (le_of_eq ?_)
    rw [hNrpow, ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  have hg1 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ σ a,
      ‖eq729FBA sz g t1 t0 E m (gueGridK sz n0) n k ω ⟨[σ], [a]⟩ - mSigOf (m n) σ‖ ≤ ρ * Lm := by
    intro ω hω k hk σ a
    have hω1 : ω ∉ GUEHyp_Bad sz g E t1 t0 m Kt n0 1 τ n := fun h => hω (Or.inl (Or.inl h))
    have h : ‖eq729FBA sz g t1 t0 E m (gueGridK sz n0) n k ω ⟨[σ], [a]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[σ], [a]⟩‖
        ≤ N ^ τ * (N * etaOf (m n) (gridTime t1 t0 (gueGridK sz n0) n k))⁻¹ ^ 1 :=
      GUEHyp_not_bad hω1 hk.le (fun _ => σ) (fun _ => a)
    rw [hKone n hlamn.1 _ (hKmem n k hk.le) σ a] at h
    refine h.trans ?_
    rw [pow_one]
    exact mul_le_mul_of_nonneg_left (hinvs _ (hKmem n k hk.le)) hρ0
  have hg2 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ s1 s2 x y,
      ‖eq729FBA sz g t1 t0 E m (gueGridK sz n0) n k ω ⟨[s1, s2], [x, y]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Lm ^ 2 := by
    intro ω hω k hk s1 s2 x y
    have hω2 : ω ∉ GUEHyp_Bad sz g E t1 t0 m Kt n0 2 τ n := fun h => hω (Or.inl (Or.inr h))
    have h := GUEHyp_not_bad hω2 hk.le ![s1, s2] ![x, y]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 2) hρ0)
  have hg3 : ∀ ω ∉ B, ∀ k < gueGridK sz n0 n, ∀ s1 s2 s3 x y w,
      ‖eq729FBA sz g t1 t0 E m (gueGridK sz n0) n k ω ⟨[s1, s2, s3], [x, y, w]⟩
        - Kt n (gridTime t1 t0 (gueGridK sz n0) n k) ⟨[s1, s2, s3], [x, y, w]⟩‖ ≤ ρ * Lm ^ 3 := by
    intro ω hω k hk s1 s2 s3 x y w
    have hω3 : ω ∉ GUEHyp_Bad sz g E t1 t0 m Kt n0 3 τ n := fun h => hω (Or.inr h)
    have h := GUEHyp_not_bad hω3 hk.le ![s1, s2, s3] ![x, y, w]
    exact h.trans (mul_le_mul_of_nonneg_left (hinvsn _ (hKmem n k hk.le) 3) hρ0)
  -- the initial term, from `STExp2gL`
  have ht1mem : t1 n ∈ Set.Icc (t1 n) (t0 n) := ⟨le_rfl, ht10 n⟩
  have hI0 := Eq729B_initTerm_nonneg sz n (t1 n)
  have hinit : ∀ s1 s2 x y,
      ‖eq729eBA sz g t1 t0 E m (gueGridK sz n0) Kt n 0 ⟨[s1, s2], [x, y]⟩‖ ≤ ρ * Eq729B_initTerm sz n (t1 n) := by
    intro s1 s2 x y
    have hmF : m = BAmF sz g E := funext fun n => GUEPathBoundsBA_m_eq (hr n)
    subst hmF
    have hl : (loopOf ![s1, s2] ![x, y] : LoopIdx (Zd d (sz.L n))) = ⟨[s1, s2], [x, y]⟩ := by
      simp [loopOf, List.ofFn_succ]
    have he : eq729eBA sz g t1 t0 E (BAmF sz g E) (gueGridK sz n0) Kt n 0 ⟨[s1, s2], [x, y]⟩
        = (∫ ω, (baFM sz g E).L n (t1 n) ![s1, s2] ![x, y] ω ∂(Sizes.seqP (sz.withLam 0))) -
          (baFM sz g E).K n (t1 n) ![s1, s2] ![x, y] := by
      unfold eq729eBA eq729FBA
      rw [← hl, Eq729B_gridTime_zero, hKinit n hlamn.1 (loopOf ![s1, s2] ![x, y]),
        GUEHyp_transfer sz g t1 t0 (gueGridK sz n0) n _ (loopOf ![s1, s2] ![x, y])]
      simp only [baFM, BALloop, BAKloop, loopFine, loopM_eq_loopL]
      rfl
    rw [he]
    exact hinn (![s1, s2], ![x, y]) 0
  -- `N Δ ≤ 1`
  have hKge : N + 1 ≤ (gueGridK sz n0 n : ℝ) := by
    unfold gueGridK; push_cast
    exact le_self_pow₀ (by linarith) (by omega)
  have hKpos : (0 : ℝ) < (gueGridK sz n0 n : ℝ) := by linarith
  have hE0 : 0 ≤ t0 n - t1 n := by linarith [ht10 n]
  have hE01 : t0 n - t1 n ≤ 1 := by linarith [ht1 n, ht0 n]
  have hMΔ : N * gridStep t1 t0 (gueGridK sz n0) n ≤ 1 := by
    unfold gridStep
    rw [mul_div_assoc']
    rw [div_le_one hKpos]
    nlinarith
  -- the one-size bound at `n`
  have hper := Eq729B_perNBA sz (gueGridK sz n0) Kt (hm0 n) (hm1 n) (ht1 n) (ht10 n) (ht0 n) (hKne n)
    (Λ := Lm) (ρ := ρ) (p := 3 / N ^ 12) (B0 := ρ * Eq729B_initTerm sz n (t1 n)) hLmdef hLm1
    hρ0 hρΛ (by positivity) hMΔ hK2b hK3b hKd hX' hBm hg1 hg2 hg3 hinit true σ₂ a b
  have hΛN : 1 ≤ N * Lm := by
    rw [hLmdef, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    calc N * η0 ≤ N * 1 := mul_le_mul_of_nonneg_left hη01 hN0.le
      _ = N := mul_one _
  have hθ : (t0 n - t1 n) * N * Lm * ρ ≤ 1 := by
    have h1 : (t0 n - t1 n) * N * Lm = (t0 n - t1 n) / η0 := by
      rw [hLmdef]; field_simp
    have h2 : (t0 n - t1 n) / η0 ≤ N ^ (-τU) := by
      rw [div_le_iff₀ hη0pos]; exact h730n
    rw [h1]
    calc (t0 n - t1 n) / η0 * ρ ≤ N ^ (-τU) * ρ := mul_le_mul_of_nonneg_right h2 hρ0
      _ = ρ * N ^ (-τU) := mul_comm _ _
      _ ≤ 1 := hρτ
  have hKr : ((gueGridK sz n0 n : ℕ) : ℝ) = (N + 1) ^ (2 * (16 * n0 + 32)) := by
    rw [show 2 * (16 * n0 + 32) = 32 * n0 + 64 by ring]
    unfold gueGridK; push_cast; rfl
  have harith := Eq729B_arith (N := sz.size n) (Eq729B_nine_le_size sz hd n) (ρ := ρ) (Λ := Lm)
    (E0 := t0 n - t1 n) (Δ := gridStep t1 t0 (gueGridK sz n0) n) (Kr := (gueGridK sz n0 n : ℝ))
    (16 * n0 + 32) (by omega) hKr hρ1 hLmpos hΛN hE01 (eq729_KΔ (hKne n)) (eq729_step_nonneg (ht10 n)) hθ
  have hexp : Real.exp ((t0 n - t1 n) * (2 * N * (ρ * Lm))) ≤ 7.4 :=
    (Eq729B_gronwall_factor hN0 hη0pos hρ0 h730n hρτ).trans Eq729B_exp_two_lt.le
  have hfin := Eq729B_final_729 hρ0 hI0 (by positivity : 0 ≤ Lm ^ 3) hexp harith
  -- `56 N^τ ≤ N^δ`
  have hW : 56 * ρ ≤ N ^ δ := by
    calc 56 * ρ ≤ N ^ τ * N ^ τ := mul_le_mul_of_nonneg_right hN56 hρ0
      _ = N ^ (τ + τ) := (Real.rpow_add hN0 _ _).symm
      _ ≤ N ^ δ := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  -- the left side is `e_K`
  have hlhs : Eq729BA_eqErr sz g E t1 t0 m (gueGridK sz n0) n σ₂ a b
      = ‖eq729eBA sz g t1 t0 E m (gueGridK sz n0) Kt n (gueGridK sz n0 n) ⟨[true, σ₂], [a, b]⟩‖ := by
    unfold Eq729BA_eqErr eq729eBA eq729FBA
    rw [gridTime_last t1 t0 (gueGridK sz n0) n (hKne n), hK2 n hlamn.1 (t0 n) ⟨ht10 n, le_rfl⟩ true σ₂ a b]
  rw [hlhs]
  calc ‖eq729eBA sz g t1 t0 E m (gueGridK sz n0) Kt n (gueGridK sz n0 n) ⟨[true, σ₂], [a, b]⟩‖
      ≤ 56 * ρ * (Lm ^ 3 + Eq729B_initTerm sz n (t1 n)) := hper.trans hfin
    _ ≤ N ^ δ * (Lm ^ 3 + Eq729B_initTerm sz n (t1 n)) := mul_le_mul_of_nonneg_right hW (by positivity)

/-! ## 5. The flow datum of (7.47) at block Anderson and its scale facts -/

/-- `t₀ = BAfT z_n` of the flow of `z` (Lemma 2.8 at BA, `(eq:t0E0_BA)`). -/
abbrev Eq729BA_t0 (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℝ := BAfT d sz n (z n)

/-- The flow coupling `g = √t₀ λ`. -/
abbrev Eq729BA_g (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℝ := Real.sqrt (Eq729BA_t0 sz z n) * sz.lam n

/-- The flow energy `E' = BAfE z_n`. -/
abbrev Eq729BA_E (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℝ := BAfE d sz n (z n)

/-- `t₁ = (1 - ζ(t_n)) t₀`. -/
abbrev Eq729BA_t1 (sz : Sizes d) (t : ℕ → ℝ) (z : ℕ → ℂ) (n : ℕ) : ℝ := (1 - ouZeta (t n)) * Eq729BA_t0 sz z n

/-- The flow value `m = BAm d L g E'` (the real-axis solution at the flow point; `m(z)/√t₀`, `GUELLBA_flow_data`). -/
abbrev Eq729BA_m (sz : Sizes d) (z : ℕ → ℂ) (n : ℕ) : ℂ :=
  BAm d (sz.L n) (Eq729BA_g sz z n) (Eq729BA_E sz z n : ℂ)

/-- `η_Q ≤ ε` eventually (`η_Q = W^{-𝔡/3} λ W^{d/2}/N ≤ 𝔡⁻¹ W^{-𝔡/3}`, `W → ∞`, `λ ≤ 𝔡⁻¹`, `N ≥ W^d`). -/
private theorem GUEHyp_etaQ_small (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ouEtaQ sz 𝔡 n ≤ ε := by
  obtain ⟨h𝔠, h𝔡, hsz, hbw, hWO⟩ := hA
  have hW := RBM.Green.tendsto_W sz h𝔠 hsz hbw
  filter_upwards [hWO, hW.eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by positivity : 0 < 𝔡 / 3)).comp hW).eventually_ge_atTop ((𝔡 * ε)⁻¹)] with n hWOn hW1 hWε
  have hw0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 _) hWOn.1
  have hWd : ((sz.W n : ℕ) : ℝ) ^ d ≤ Nsz sz n := by
    have h : (sz.W n) ^ d ≤ (sz.W n * sz.L n) ^ d :=
      Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by have := sz.three_le_L n; omega)) d
    exact_mod_cast h
  have hWd0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hw0 d
  have h1 : sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n ≤ 𝔡⁻¹ * 1 := by
    have e2 : ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) ≤ ((sz.W n : ℕ) : ℝ) ^ d := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hW1 (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
    calc sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n
        ≤ 𝔡⁻¹ * ((sz.W n : ℕ) : ℝ) ^ d / ((sz.W n : ℕ) : ℝ) ^ d := by
          gcongr
          exact hWOn.2
      _ = 𝔡⁻¹ * 1 := by field_simp
  have hpow : ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) ≤ 𝔡 * ε := by
    rw [Real.rpow_neg hw0.le]
    have : (𝔡 * ε)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 3) := hWε
    rw [inv_le_comm₀ (by positivity) (Real.rpow_pos_of_pos hw0 _)] at this
    exact this
  unfold ouEtaQ
  calc ((sz.W n : ℕ) : ℝ) ^ (-(𝔡 / 3)) * (sz.lam n * ((sz.W n : ℕ) : ℝ) ^ ((d : ℝ) / 2) / Nsz sz n)
      ≤ (𝔡 * ε) * (𝔡⁻¹ * 1) := by
        gcongr
      _ = ε := by field_simp

/-- The Lemma 2.8 facts of `ba_flowG` along the QUE point `z_n = E_n + i η_Q` (eventually): `0 < η_Q ≤ 1`, `η_Q ≤ c/2`,
`c_T ≤ t₀ < 1`, `1 - t₀ ≤ η_Q/c`, `1/2 ≤ t₀`, `η_Q ≤ 2 (1 - t₀)`. -/
private theorem GUEHyp_flowQ (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ) {E : ℕ → ℝ}
    (hE : ∀ n, BAbulk d (sz.L n) (sz.lam n) κ (E n)) {z : ℕ → ℂ} (hz : ∀ᶠ n in atTop, z n = Eq729B_zQ sz 𝔡 E n) :
    ∃ c cT : ℝ, 0 < c ∧ 0 < cT ∧ ∀ᶠ n in atTop, (z n).im = ouEtaQ sz 𝔡 n ∧ 0 < ouEtaQ sz 𝔡 n ∧ ouEtaQ sz 𝔡 n ≤ 1 ∧
      cT ≤ Eq729BA_t0 sz z n ∧ Eq729BA_t0 sz z n < 1 ∧ 1 - Eq729BA_t0 sz z n ≤ ouEtaQ sz 𝔡 n / c ∧
      1 / 2 ≤ Eq729BA_t0 sz z n ∧ ouEtaQ sz 𝔡 n ≤ 2 * (1 - Eq729BA_t0 sz z n) := by
  obtain ⟨κ'', c, cT, hκ'', hc, hcT, hF⟩ := ba_flowG d κ hκ
  refine ⟨c, cT, hc, hcT, ?_⟩
  filter_upwards [hz, RandomLayer_etaQ_le_one sz hA, GUEHyp_etaQ_small sz hA (half_pos hc),
    hA.2.2.2.2.mono fun n hn => hn.1] with n hzn hη1 hηs hlo
  have hw0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hw0 _) hlo
  have hη0 : 0 < ouEtaQ sz 𝔡 n := RandomLayer_etaQ_pos sz 𝔡 hlam
  have hzim : (z n).im = ouEtaQ sz 𝔡 n := by rw [hzn]; simp [Eq729B_zQ]
  have hzre : (z n).re = E n := by rw [hzn]; simp [Eq729B_zQ]
  obtain ⟨-, hcT_le, ht1, h1t⟩ := hF sz n (z n) (by rw [hzre]; exact hE n) (by rw [hzim]; exact hη0) (by rw [hzim]; exact hη1)
  rw [hzim] at h1t
  have hh : 1 / 2 ≤ Eq729BA_t0 sz z n := by
    have : ouEtaQ sz 𝔡 n / c ≤ 1 / 2 := by
      rw [div_le_iff₀ hc]; linarith
    linarith
  refine ⟨hzim, hη0, hη1, hcT_le, ht1, h1t, hh, ?_⟩
  -- `η_Q ≤ 2 (1 - t₀)`: `1 - t₀ = Im z / (Im m + Im z)`, `Im m ≤ 1`, `Im z ≤ 1`
  have hzpos : 0 < (z n).im := by rw [hzim]; exact hη0
  have hm := (BAm_self d (sz.L n) (sz.lam n) (z n) hzpos).1
  have hmn : ‖BAm d (sz.L n) (sz.lam n) (z n)‖ ≤ 1 :=
    BAm_norm_le_one d (sz.L n) (sz.lam n) (z n) _ hzpos.le (BAm_self d (sz.L n) (sz.lam n) (z n) hzpos)
  have hmim : (BAm d (sz.L n) (sz.lam n) (z n)).im ≤ 1 := (Complex.im_le_norm _).trans hmn
  have hmul : BAfT d sz n (z n) * (z n).im = (1 - BAfT d sz n (z n)) * (BAm d (sz.L n) (sz.lam n) (z n)).im :=
    BAt0_mul hzpos hm
  have hz1 : (z n).im ≤ 1 := by rw [hzim]; exact hη1
  change ouEtaQ sz 𝔡 n ≤ 2 * (1 - BAfT d sz n (z n))
  rw [← hzim]
  nlinarith [hmul, hmim, hz1, hzpos, hm]

/-! ## 6. The three asymptotic hypotheses at the QUE scale (target 14, `Eq729B_derivedBA`) -/

/-- **The three asymptotic hypotheses of `gueGrid_eq729BA` at the flow datum of `z_n = E_n + i η_Q`** (twin of `Eq729B_derived`, `Eq729B:1125`):
`h730`, `hscale`, and `hell` in the form `L^d (1 - t₁) ≤ 2 g²`, eventually, from `Admissible 𝔠 𝔡`, `τ_U ≤ ouTauMax 𝔠 𝔡`, `0 ≤ t_n ≤ N^{-1+τ_U}`, at the
QUE scale `η_Q = W^{-𝔡/3} λ W^{d/2}/N`; the Lemma 2.8 facts are those of `ba_flowG` (`c`, `c_T`, with `1 - t₀ ≤ η_Q/c`, so `t₀ ≥ 1/2` eventually and the
band chain applies); `1/2 ≤ t₀` is also returned.  The thresholds are `W`-only (`W → ∞`): `4 ≤ W^{𝔡/2}`, `2/c ≤ W^{4𝔡/3}`, `2 ≤ W^{23𝔡/12}`. -/
theorem Eq729B_derivedBA (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ τU : ℝ} (hκ : 0 < κ) (hτU : 0 < τU)
    (hτUm : τU ≤ ouTauMax 𝔠 𝔡) {E t : ℕ → ℝ} (hE : ∀ n, BAbulk d (sz.L n) (sz.lam n) κ (E n))
    (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n) {z : ℕ → ℂ} (hz : ∀ᶠ n in atTop, z n = Eq729B_zQ sz 𝔡 E n) :
    (∀ᶠ n in atTop, Eq729BA_t0 sz z n - Eq729BA_t1 sz t z n ≤
        Nsz sz n ^ (-τU) * etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n)) ∧
      (∀ᶠ n in atTop, (Nsz sz n * etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n))⁻¹ ≤ Nsz sz n ^ (-τU)) ∧
      (∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - Eq729BA_t1 sz t z n) ≤ 2 * Eq729BA_g sz z n ^ 2) ∧
      (∀ᶠ n in atTop, 1 / 2 ≤ Eq729BA_t0 sz z n) := by
  obtain ⟨c, cT, hc, hcT, hfl⟩ := GUEHyp_flowQ sz hA hκ hE hz
  have hτ12 : τU ≤ 𝔠 * 𝔡 / 12 := (hτUm.trans (min_le_left _ _)).trans (min_le_right _ _)
  have h𝔠 := hA.1
  have h𝔡 := hA.2.1
  have hWtop := RBM.Green.tendsto_W sz h𝔠 hA.2.2.1 hA.2.2.2.1
  have hall : ∀ᶠ n in atTop,
      (Eq729BA_t0 sz z n - Eq729BA_t1 sz t z n ≤ Nsz sz n ^ (-τU) * etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n)) ∧
      ((Nsz sz n * etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n))⁻¹ ≤ Nsz sz n ^ (-τU)) ∧
      (((sz.L n : ℕ) : ℝ) ^ d * (1 - Eq729BA_t1 sz t z n) ≤ 2 * Eq729BA_g sz z n ^ 2) ∧ 1 / 2 ≤ Eq729BA_t0 sz z n := by
    filter_upwards [hfl, hA.2.2.2.1, hA.2.2.2.2,
      ((tendsto_rpow_atTop (by positivity : 0 < 𝔡 / 2)).comp hWtop).eventually_ge_atTop 4,
      ((tendsto_rpow_atTop (by positivity : 0 < 4 * 𝔡 / 3)).comp hWtop).eventually_ge_atTop (2 / c),
      ((tendsto_rpow_atTop (by positivity : 0 < 23 * 𝔡 / 12)).comp hWtop).eventually_ge_atTop 2,
      hWtop.eventually_ge_atTop 1] with n hfln hNW hWOn h4 hc4 h2' hW1
    obtain ⟨hzim, hη, hη1, -, ht0lt, h1t, hhalf, -⟩ := hfln
    have h4' : 4 ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 2) := h4
    have hc4' : 2 / c ≤ ((sz.W n : ℕ) : ℝ) ^ (4 * 𝔡 / 3) := hc4
    have h2'' : 2 ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) := h2'
    have hN1 : 1 ≤ Nsz sz n := by exact_mod_cast sz.one_le_size n
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by linarith
    have hzpos : 0 < (z n).im := by rw [hzim]; exact hη
    have hs4 : 1 / 4 ≤ Real.sqrt (Eq729BA_t0 sz z n) := by
      rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
        rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hζ0 := ZeroModeProfile_ouZeta_nonneg (ht n).1
    have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
    have hζt : ouZeta (t n) ≤ t n := ZeroModeProfile_ouZeta_le (t n)
    have hζN : ouZeta (t n) ≤ Nsz sz n ^ (-1 + τU) := hζt.trans (ht n).2
    have hdiff : Eq729BA_t0 sz z n - Eq729BA_t1 sz t z n = ouZeta (t n) * Eq729BA_t0 sz z n := by
      simp only [Eq729BA_t1]; ring
    have hζt0 : ouZeta (t n) * Eq729BA_t0 sz z n ≤ Nsz sz n ^ (-1 + τU) :=
      calc ouZeta (t n) * Eq729BA_t0 sz z n ≤ ouZeta (t n) * 1 := mul_le_mul_of_nonneg_left ht0lt.le hζ0
        _ = ouZeta (t n) := mul_one _
        _ ≤ _ := hζN
    have hclaim := Eq729B_claimA sz n h𝔡 hτ12 hNW h4' hWOn.1
    obtain ⟨hh1, hh2⟩ := Eq729B_h730_hscale_real hN1 hτU hη hs4 hclaim hζt0
    have heta : etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n) = Real.sqrt (Eq729BA_t0 sz z n) * ouEtaQ sz 𝔡 n := by
      have := GUELLBA_flowEta d sz n (z n) hzpos
      rwa [hzim] at this
    refine ⟨?_, ?_, ?_, hhalf⟩
    · rw [hdiff, heta]; exact hh1
    · rw [heta]; exact hh2
    · -- `hell`: `Eq729B_hell_of_scales` gives `L^d (1 - t₁) ≤ λ²`, and `λ² ≤ 2 t₀ λ² = 2 g²` since `t₀ ≥ 1/2`
      have hN2 : 2 * Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) := by
        have e1 : Nsz sz n ^ τU ≤ ((sz.W n : ℕ) : ℝ) ^ (τU / 𝔠) := Sizes.size_rpow_le_W_rpow sz h𝔠 n hNW hτU.le
        have e2 : ((sz.W n : ℕ) : ℝ) ^ (τU / 𝔠) ≤ ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) :=
          Real.rpow_le_rpow_of_exponent_le hW1 (by rw [div_le_iff₀ h𝔠]; linarith)
        have e3 : ((sz.W n : ℕ) : ℝ) ^ (2 * 𝔡) =
            ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) := by
          rw [← Real.rpow_add hW0]; congr 1; ring
        rw [e3]
        have := Real.rpow_nonneg hW0.le (𝔡 / 12)
        calc 2 * Nsz sz n ^ τU ≤ 2 * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) := by linarith [e1.trans e2]
          _ ≤ ((sz.W n : ℕ) : ℝ) ^ (23 * 𝔡 / 12) * ((sz.W n : ℕ) : ℝ) ^ (𝔡 / 12) :=
              mul_le_mul_of_nonneg_right h2'' this
          _ = _ := mul_comm _ _
      have hl := Eq729B_hell_of_scales sz n hc hWOn.1 h1t hζ0 hζN ht0lt.le hc4' hN2
      have hg2 : Eq729BA_g sz z n ^ 2 = Eq729BA_t0 sz z n * sz.lam n ^ 2 := by
        simp only [Eq729BA_g]; rw [mul_pow, Real.sq_sqrt (by linarith)]
      rw [hg2]
      change ((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - ouZeta (t n)) * Eq729BA_t0 sz z n) ≤ _
      nlinarith [sq_nonneg (sz.lam n)]
  exact ⟨hall.mono fun n h => h.1, hall.mono fun n h => h.2.1, hall.mono fun n h => h.2.2.1, hall.mono fun n h => h.2.2.2⟩

/-! ## 7. The (7.47) step (target 14, `Eq729B_eq747_of_eq729BA`) -/

/-- `Ring.inverse (1 - Q S) * Q` is symmetric for symmetric `Q`, `S` (the push-through identity `Q (1 - S Q)⁻¹ = (1 - Q S)⁻¹ Q`; trivial when `1 - Q S`
is not a unit). -/
private theorem GUEHyp_ThQ_symm {ι : Type*} [Fintype ι] [DecidableEq ι] {Q S : Matrix ι ι ℂ} (hQ : Qᵀ = Q) (hS : Sᵀ = S) :
    (Ring.inverse (1 - Q * S) * Q)ᵀ = Ring.inverse (1 - Q * S) * Q := by
  by_cases hU : IsUnit (1 - Q * S)
  · have hT : (1 - Q * S)ᵀ = 1 - S * Q := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hQ, hS]
    have hU' : IsUnit (1 - S * Q) := by
      rw [← hT]
      exact (Matrix.isUnit_iff_isUnit_det _).2 (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 hU)
    have hd : IsUnit (1 - Q * S).det := (Matrix.isUnit_iff_isUnit_det _).1 hU
    have hd' : IsUnit (1 - S * Q).det := (Matrix.isUnit_iff_isUnit_det _).1 hU'
    have hcomm : (1 - Q * S) * Q = Q * (1 - S * Q) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.transpose_mul, hQ, Matrix.transpose_nonsing_inv, hT]
    calc Q * (1 - S * Q)⁻¹ = ((1 - Q * S)⁻¹ * (1 - Q * S)) * Q * (1 - S * Q)⁻¹ := by
          rw [Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
      _ = (1 - Q * S)⁻¹ * ((1 - Q * S) * Q) * (1 - S * Q)⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (1 - Q * S)⁻¹ * (Q * (1 - S * Q)) * (1 - S * Q)⁻¹ := by rw [hcomm]
      _ = (1 - Q * S)⁻¹ * Q := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd', Matrix.mul_one]
  · rw [Ring.inverse_non_unit _ hU]
    simp

/-- `S̃^{(B)}_ζ(0)` is symmetric. -/
private theorem GUEHyp_SBtilde_symm (d L : ℕ) [NeZero L] (ζ : ℝ) : (SBtilde d L 0 ζ)ᵀ = SBtilde d L 0 ζ := by
  unfold SBtilde
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, SB_transpose]
  congr 2

/-- `M^{(+,σ)}` is symmetric for a symmetric `M^{(B)}`. -/
private theorem GUEHyp_Mss_symm {L : ℕ} [NeZero L] {B : Matrix (Zd d L) (Zd d L) ℂ} (hB : Bᵀ = B) (σ : Bool) :
    (BAMss d L B true σ)ᵀ = BAMss d L B true σ := by
  ext a b
  have hba : B b a = B a b := by
    have := congrFun (congrFun hB a) b
    simpa [Matrix.transpose_apply] using this
  cases σ <;> simp [BAMss, BAMsigma, Matrix.conjTranspose_apply, hba, mul_comm]

/-- The BA OU profiles `pm`, `pp` are symmetric in `(a, b)` (`M^{(B)}` is symmetric, `BAMB_transpose`). -/
private theorem GUEHyp_prof_symm (sz : Sizes d) (n : ℕ) (ζ : ℝ) (z : ℂ) (a b : Zd d (sz.L n)) :
    (UNOUProfile.ba d).pm sz n ζ z b a = (UNOUProfile.ba d).pm sz n ζ z a b ∧
      (UNOUProfile.ba d).pp sz n ζ z b a = (UNOUProfile.ba d).pp sz n ζ z a b := by
  have hB := BAMB_transpose d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)
  have key : ∀ σ : Bool, (Ring.inverse (1 - BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ *
        SBtilde d (sz.L n) 0 ζ) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) b a =
      (Ring.inverse (1 - BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ *
        SBtilde d (sz.L n) 0 ζ) *
      BAMss d (sz.L n) (BAMB d (sz.L n) (sz.lam n) z (BAm d (sz.L n) (sz.lam n) z)) true σ) a b := fun σ => by
    have h := GUEHyp_ThQ_symm (GUEHyp_Mss_symm hB σ) (GUEHyp_SBtilde_symm d (sz.L n) ζ)
    simpa [Matrix.transpose_apply] using congrFun (congrFun h a) b
  exact ⟨by unfold UNOUProfile.ba; simp only; rw [key false], by unfold UNOUProfile.ba; simp only; rw [key true]⟩

/-- **The law (7.26) in expectation at block Anderson** (twin of `Eq729B_law726`, `Eq729B:935`): at the last grid step,
`𝔼 [avg2 G_xy G^σ_yx](z) = t₀ 𝔼 𝓛_{t₀,(+,σ),(b,a)}` for the centred OU flow `𝐇_t = λΨ + e^{-t/2} V + √(1-e^{-t}) X` under the BA carrier and the BA grid
path `gueHBA` at the flow datum of `z` (`t₁ = (1 - ζ(t)) t₀`, `g = √t₀ λ`): the homogeneity of `loopL` (`z_{t₀} = √t₀ z`, `GUELLBA_flow_data`) and the
one-time law at the last step (`GUELLBA_integral_transfer`). -/
private theorem GUEHyp_law726 (sz : Sizes d) {t : ℕ → ℝ} {z : ℕ → ℂ} (K : ℕ → ℕ) (n : ℕ) (hz : 0 < (z n).im) (ht : 0 ≤ t n)
    (hK : K n ≠ 0) (σ : Bool) (a b : Zd d (sz.L n)) :
    ∫ ω, avg2 sz n (fun x y => Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) true x y *
        Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) σ y x) a b ∂(ouP (UNModelC.ba sz).toUNModel n) =
      (Eq729BA_t0 sz z n : ℂ) * ∫ ω, loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueHBA sz (Eq729BA_g sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) K n (K n) ω))
        (ztOf (Eq729BA_m sz z n) (Eq729BA_E sz z n) (Eq729BA_t0 sz z n)) ⟨[true, σ], [b, a]⟩ ∂(Pgue (sz.withLam 0)) := by
  have hm := (BAm_self d (sz.L n) (sz.lam n) (z n) hz).1
  have ht0pos : 0 < Eq729BA_t0 sz z n := BAt0_pos hz hm
  have hs0 : 0 < Real.sqrt (Eq729BA_t0 sz z n) := Real.sqrt_pos.2 ht0pos
  have hzt : ztOf (Eq729BA_m sz z n) (Eq729BA_E sz z n) (Eq729BA_t0 sz z n) = (Real.sqrt (Eq729BA_t0 sz z n) : ℂ) * z n :=
    (GUELLBA_flow_data d sz n hz).2
  set F : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℂ := fun M =>
    loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) M)
      (ztOf (Eq729BA_m sz z n) (Eq729BA_E sz z n) (Eq729BA_t0 sz z n)) ⟨[true, σ], [b, a]⟩ with hF
  have hFm : Measurable F :=
    (RBM.Gauss.walk_measurable_loopL d (sz.L n) (sz.W n) _ _).comp (RBM.Gauss.walk_measurable_blockMat d (sz.L n) (sz.W n))
  have hti1 : Eq729BA_t1 sz t z n = Real.exp (-(t n)) * Eq729BA_t0 sz z n := by simp [Eq729BA_t1, ouZeta]
  have hint := GUELLBA_integral_transfer sz (Eq729BA_g sz z) (Eq729BA_t0 sz z) (Eq729BA_t1 sz t z) K n hK ht0pos.le ht hti1 rfl F hFm
  rw [← hint, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  change avg2 sz n (fun x y => Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) true x y *
        Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) σ y x) a b =
    (Eq729BA_t0 sz z n : ℂ) * loopL d (sz.L n) (sz.W n)
      (blockMat d (sz.L n) (sz.W n) (((Real.sqrt (Eq729BA_t0 sz z n) : ℝ) : ℂ) • ouMatC (UNModelC.ba sz) n (t n) ω))
      (ztOf (Eq729BA_m sz z n) (Eq729BA_E sz z n) (Eq729BA_t0 sz z n)) ⟨[true, σ], [b, a]⟩
  have hc : ((Real.sqrt (Eq729BA_t0 sz z n) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have hl := GUEPhaseGrid_loopL_smul_mul hc (blockMat d (sz.L n) (sz.W n) (ouMatC (UNModelC.ba sz) n (t n) ω)) (z n)
    ⟨[true, σ], [b, a]⟩
  have hlen : (([true, σ] : List Bool).zip [b, a]).length = 2 := rfl
  rw [Eq729B_avg2_eq_loop, Eq729B_blockMat_smul, hzt]
  rw [hlen] at hl
  rw [hl]
  have hss : ((Real.sqrt (Eq729BA_t0 sz z n) : ℝ) : ℂ) ^ 2 = (Eq729BA_t0 sz z n : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht0pos.le]
  rw [← mul_assoc, ← hss]
  field_simp

/-- **(7.47) at one size index** (twin of `Eq729B_core747`, `Eq729B:998`): from the loss-form (7.29) at the labels `(b, a)` and the main term
`prof = t₀ K̃_{t₀}`, `‖𝔼 [avg2 G_xy G^σ_yx] - prof‖ ≤ qdBoundExp` (`t₀ ≥ 1/2` replaces `1/16 ≤ t₀`). -/
private theorem Eq729B_core747BA (sz : Sizes d) (hd : 3 ≤ d) (𝔡 : ℝ) {τ δ : ℝ} {t : ℕ → ℝ} {z : ℕ → ℂ} {K : ℕ → ℕ} (n : ℕ)
    (σ : Bool) (a b : Zd d (sz.L n)) (ht : 0 ≤ t n) (hK : K n ≠ 0)
    (hη : 0 < ouEtaQ sz 𝔡 n) (hzim : (z n).im = ouEtaQ sz 𝔡 n) (hhalf : 1 / 2 ≤ Eq729BA_t0 sz z n)
    (ht0lt : Eq729BA_t0 sz z n < 1) (hu01 : ouEtaQ sz 𝔡 n ≤ 2 * (1 - Eq729BA_t0 sz z n))
    (hH : Eq729BA_eqErr sz (Eq729BA_g sz z) (Eq729BA_E sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) (Eq729BA_m sz z) K n σ b a ≤
      Nsz sz n ^ δ * ((Nsz sz n * etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n))⁻¹ ^ 3 + Eq729B_initTerm sz n (Eq729BA_t1 sz t z n)))
    (hW : 12 * Nsz sz n ^ δ ≤ ((sz.W n : ℕ) : ℝ) ^ τ) {prof : ℂ}
    (hprof : (Eq729BA_t0 sz z n : ℂ) * kTwoGUEBA d (sz.L n) (sz.W n) (Eq729BA_g sz z n) (Eq729BA_E sz z n) (Eq729BA_m sz z n)
      (Eq729BA_t1 sz t z n) (Eq729BA_t0 sz z n) true σ b a = prof) :
    ‖(∫ ω, avg2 sz n (fun x y => Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) true x y *
        Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) σ y x) a b ∂(ouP (UNModelC.ba sz).toUNModel n)) - prof‖ ≤
      qdBoundExp sz n τ (ouEtaQ sz 𝔡 n) := by
  have hzpos : 0 < (z n).im := by rw [hzim]; exact hη
  have hu0 : 0 ≤ Eq729BA_t0 sz z n := by linarith
  have hζ0 := ZeroModeProfile_ouZeta_nonneg ht
  have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
  rw [GUEHyp_law726 sz K n hzpos ht hK σ a b, ← hprof, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu0]
  have heq : Eq729BA_eqErr sz (Eq729BA_g sz z) (Eq729BA_E sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) (Eq729BA_m sz z) K n σ b a =
      ‖(∫ ω, loopL d (sz.L n) (sz.W n)
        (blockMat d (sz.L n) (sz.W n) (gueHBA sz (Eq729BA_g sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) K n (K n) ω))
        (ztOf (Eq729BA_m sz z n) (Eq729BA_E sz z n) (Eq729BA_t0 sz z n)) ⟨[true, σ], [b, a]⟩ ∂(Pgue (sz.withLam 0))) -
      kTwoGUEBA d (sz.L n) (sz.W n) (Eq729BA_g sz z n) (Eq729BA_E sz z n) (Eq729BA_m sz z n) (Eq729BA_t1 sz t z n)
        (Eq729BA_t0 sz z n) true σ b a‖ := rfl
  rw [← heq]
  -- the scales
  have hsc : etaOf (Eq729BA_m sz z n) (Eq729BA_t0 sz z n) = Real.sqrt (Eq729BA_t0 sz z n) * ouEtaQ sz 𝔡 n := by
    have := GUELLBA_flowEta d sz n (z n) hzpos
    rwa [hzim] at this
  have hu01' : ouEtaQ sz 𝔡 n ≤ 2 * (1 - Eq729BA_t1 sz t z n) := by
    have : Eq729BA_t1 sz t z n ≤ Eq729BA_t0 sz z n := by
      simp only [Eq729BA_t1]; nlinarith [mul_nonneg hζ0 hu0]
    linarith
  have hBt := Eq729B_bctl_le_two_calB sz n (by omega) hη hu01'
  have hNpos := Nsz_pos sz n
  have hB : (Nsz sz n * ouEtaQ sz 𝔡 n)⁻¹ ≤ calB sz n (ouEtaQ sz 𝔡 n) 0 := by
    unfold calB
    have : 0 ≤ (sz.lam n ^ 2 + ouEtaQ sz 𝔡 n)⁻¹ / (((sz.W n : ℕ) : ℝ) ^ 2 * (0 + ((sz.W n : ℕ) : ℝ)) ^ (d - 2)) := by
      positivity
    linarith
  have hX : 0 ≤ (sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hass := Eq729B_assembly_747 (by linarith) ht0lt.le hNpos hη hB hX (Eq729B_Bctl_nonneg sz n (Eq729BA_t1 sz t z n)) hBt
    (Real.rpow_nonneg hNpos.le δ) hW
  rw [hsc] at hH
  rw [Eq729B_qdBoundExp_eq]
  calc Eq729BA_t0 sz z n * Eq729BA_eqErr sz (Eq729BA_g sz z) (Eq729BA_E sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z)
        (Eq729BA_m sz z) K n σ b a
      ≤ Eq729BA_t0 sz z n * (Nsz sz n ^ δ * ((Nsz sz n * (Real.sqrt (Eq729BA_t0 sz z n) * ouEtaQ sz 𝔡 n))⁻¹ ^ 3 +
          Eq729B_initTerm sz n (Eq729BA_t1 sz t z n))) := mul_le_mul_of_nonneg_left hH hu0
    _ ≤ ((sz.W n : ℕ) : ℝ) ^ τ * (calB sz n (ouEtaQ sz 𝔡 n) 0 ^ 2 *
        ((sz.lam n ^ 2 * ((sz.W n : ℕ) : ℝ) ^ d) ^ (-(1 / 5 : ℝ)) + calB sz n (ouEtaQ sz 𝔡 n) 0)) := hass

/-- **(7.47) from (7.29) and (7.26) at block Anderson** (twin of `Eq729B_eq747_of_eq729`, `Eq729B:1077`).  Let `z_n = E_n + i η_Q`,
`η_Q = W^{-𝔡/3} λ W^{d/2}/N`, `(t₀, E', g, m)` the BA flow datum of `z_n` (`Eq729BA_*`, Lemma 2.8 at BA: `ba_flowG`), `t₁ = (1 - ζ(t_n)) t₀`.  If (7.29)
holds at `t₀` on the BA grid in the loss form `N^δ ((N η_{t₀})^{-3} + I₀(t₁))` (`Eq729BA_Concl`), the one-time law (7.26) at the last grid step and
`t₀ K̃_{t₀} = P` (`kTwoGUEBA_bridge_pm/pp`; the profile `P = UNOUProfile.ba` is symmetric) give the body of `UNOUEq747k` at the BA kind
(`RandomLayerB_QueAt (UNKind.ba d) (UNOUProfile.ba d)`): `W ≥ N^𝔠` turns the loss `N^{𝔠τ/2}` into `W^τ`, `t₀ (N η_{t₀})^{-3} ≤ 4 (N η_Q)^{-3}`,
`𝓑(t₁) ≤ 2 𝓑_{η_Q,0}` (`Eq729B_assembly_747`; `t₀ ≥ 1/2` eventually since `1 - t₀ ≤ η_Q/c` and `η_Q → 0`). -/
theorem Eq729B_eq747_of_eq729BA (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ : ℝ} (hκ : 0 < κ)
    {E t : ℕ → ℝ} (hE : ∀ n, BAbulk d (sz.L n) (sz.lam n) κ (E n)) (ht : ∀ n, 0 ≤ t n)
    {z : ℕ → ℂ} (hz : ∀ᶠ n in atTop, z n = Eq729B_zQ sz 𝔡 E n) {K : ℕ → ℕ} (hK : ∀ n, K n ≠ 0)
    (H729 : Eq729BA_Concl sz (Eq729BA_g sz z) (Eq729BA_E sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) (Eq729BA_m sz z) K)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, RandomLayerB_QueAt (UNKind.ba d) (UNOUProfile.ba d) sz 𝔡 n (E n) (t n) τ := by
  have hδ' : 0 < 𝔠 * τ / 2 := by have := mul_pos hA.1 hτ; linarith
  obtain ⟨c, cT, hc, hcT, hfl⟩ := GUEHyp_flowQ sz hA hκ hE hz
  filter_upwards [H729 (𝔠 * τ / 2) hδ', hfl, hz, hA.2.2.2.1,
    (Sizes.tendsto_size sz hA.2.2.1).eventually (eventually_le_rpow 12 hδ')] with n hH hfln hzn hNW h12
  intro a b
  obtain ⟨hzim, hη, hη1, -, ht0lt, -, hhalf, hu01⟩ := hfln
  have hW := Eq729B_loss_absorb (Nsz_pos sz n) hτ hNW h12
  have hζ0 := ZeroModeProfile_ouZeta_nonneg (ht n)
  have hζ1 := ZeroModeProfile_ouZeta_le_one (t n)
  have hzpos : 0 < (z n).im := by rw [hzim]; exact hη
  have hmeq : Eq729BA_m sz z n = BAm d (sz.L n) (sz.lam n) (z n) / (Real.sqrt (BAfT d sz n (z n)) : ℂ) :=
    (GUELLBA_flow_data d sz n hzpos).1
  rw [show ((E n : ℂ) + ((ouEtaQ sz 𝔡 n : ℝ) : ℂ) * Complex.I) = z n from hzn.symm]
  refine ⟨?_, ?_⟩
  · have e1 : (∫ ω, avg2 sz n (fun x y => ((‖Gres (ouMatC ((UNKind.ba d).M sz) n (t n) ω) (z n) true x y‖ ^ 2 : ℝ) : ℂ)) a b
        ∂(ouP ((UNKind.ba d).M sz).toUNModel n)) =
        ∫ ω, avg2 sz n (fun x y => Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) true x y *
          Gres (ouMatC (UNModelC.ba sz) n (t n) ω) (z n) false y x) a b ∂(ouP (UNModelC.ba sz).toUNModel n) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => Eq729B_avg2_abs_sq sz n (ouMatC_isHermitian _ _ _ ω) (z n) a b)
    rw [e1]
    refine Eq729B_core747BA sz hd 𝔡 (z := z) (K := K) n false a b (ht n) (hK n) hη hzim hhalf ht0lt hu01 (hH false b a) hW ?_
    have hbr := kTwoGUEBA_bridge_pm sz n hζ0 hζ1 hzpos b a
    rw [(GUEHyp_prof_symm sz n (ouZeta (t n)) (z n) a b).1.symm]
    rw [hmeq]
    exact hbr
  · refine Eq729B_core747BA sz hd 𝔡 (z := z) (K := K) n true a b (ht n) (hK n) hη hzim hhalf ht0lt hu01 (hH true b a) hW ?_
    have hbr := kTwoGUEBA_bridge_pp sz n hζ0 hζ1 hzpos b a
    rw [(GUEHyp_prof_symm sz n (ouZeta (t n)) (z n) a b).2.symm]
    rw [hmeq]
    exact hbr

/-! ## 8. (7.47) from the inputs of `gueGrid_eq729BA` (target 14, `Eq729B_eq747_of_inputsBA`) -/

/-- **(7.47) from the inputs of `gueGrid_eq729BA`** (twin of `Eq729B_eq747_of_inputs`, `Eq729B:1221`): at the flow datum of `z_n = E_n + i η_Q`,
`0 ≤ t_n ≤ N^{-1+τ_U}`, `τ_U ≤ ouTauMax 𝔠 𝔡`, `W ≥ N^𝔠`: `h730`, `hscale`, `hell` of `gueGrid_eq729BA` are derived (`Eq729B_derivedBA`), `Tendsto size` and
the window `0 < g ≤ 𝔡⁻¹` (`(eq:WO)`, `t₀ < 1`, `t₀ ≥ 1/2`) too; `gueGrid_eq729BA` followed by `Eq729B_eq747_of_eq729BA` is the body of `UNOUEq747k` at the BA kind.
The remaining inputs are those of `gueGrid_eq729BA`: the primitive family `Kt` (`hKinit`, `hK`, `hK2`, the clauses of `BAKFam`), `hB` (the third conjunct of `BAMO`) and `hP`
(`BAPB`, (7.28) on the grid); `hgood` (`Ed κ'`, `0 ≤ t₁ ≤ t₀ < 1` at every `n`) replaces RBM2D's `Eq729B_pw`. -/
theorem Eq729B_eq747_of_inputsBA (sz : Sizes d) (hd : 3 ≤ d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {κ κ' τU : ℝ}
    (hκ : 0 < κ) (hκ' : 0 < κ') (hτU : 0 < τU) (hτUm : τU ≤ ouTauMax 𝔠 𝔡) (n0 : ℕ) (hn0 : 4 ≤ n0) {E t : ℕ → ℝ}
    (hE : ∀ n, BAbulk d (sz.L n) (sz.lam n) κ (E n)) (ht : ∀ n, 0 ≤ t n ∧ t n ≤ ouTStar sz τU n)
    {z : ℕ → ℂ} (hz : ∀ᶠ n in atTop, z n = Eq729B_zQ sz 𝔡 E n)
    (hgood : ∀ n, BAEd d κ' sz n (z n) ∧ 0 ≤ Eq729BA_t1 sz t z n ∧ Eq729BA_t1 sz t z n ≤ Eq729BA_t0 sz z n ∧
      Eq729BA_t0 sz z n < 1)
    (Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ)
    (hKinit : ∀ n, 0 < Eq729BA_g sz z n → ∀ I : LoopIdx (Zd d (sz.L n)),
      Kt n (Eq729BA_t1 sz t z n) I = BAKsol d (sz.L n) (sz.W n)
        (BAMsigma d (sz.L n) (BAMB d (sz.L n) (Eq729BA_g sz z n) (Eq729BA_E sz z n : ℂ) (Eq729BA_m sz z n)))
        (PropSpin (Eq729BA_m sz z n)) (Eq729BA_t1 sz t z n) I)
    (hK : ∀ n, 0 < Eq729BA_g sz z n → ∀ s ∈ Set.Icc (Eq729BA_t1 sz t z n) (Eq729BA_t0 sz z n), ∀ I : LoopIdx (Zd d (sz.L n)),
      I.WF → 1 ≤ I.length → I.length ≤ 4 * n0 →
      HasDerivWithinAt (fun u => Kt n u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt n s) I)
        (Set.Icc (Eq729BA_t1 sz t z n) (Eq729BA_t0 sz z n)) s)
    (hK2 : ∀ n, 0 < Eq729BA_g sz z n → ∀ s ∈ Set.Icc (Eq729BA_t1 sz t z n) (Eq729BA_t0 sz z n), ∀ (σ₁ σ₂ : Bool)
      (a b : Zd d (sz.L n)), Kt n s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA d (sz.L n) (sz.W n) (Eq729BA_g sz z n) (Eq729BA_E sz z n)
        (Eq729BA_m sz z n) (Eq729BA_t1 sz t z n) s σ₁ σ₂ a b)
    (hB : STExp2gL (baFM sz (Eq729BA_g sz z) (Eq729BA_E sz z)) (Sizes.seqP (sz.withLam 0)) (Eq729BA_t1 sz t z))
    (hP : GUEPathBoundsBA sz (Eq729BA_g sz z) (Eq729BA_E sz z) (Eq729BA_t1 sz t z) (Eq729BA_t0 sz z) (Eq729BA_m sz z)
      (gueGridK sz n0) n0 Kt)
    (τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ n in atTop, RandomLayerB_QueAt (UNKind.ba d) (UNOUProfile.ba d) sz 𝔡 n (E n) (t n) τ := by
  obtain ⟨h730, hscale, hell, hhalf⟩ := Eq729B_derivedBA sz hA hκ hτU hτUm hE ht hz
  have hr : ∀ n, BAReal d (sz.L n) (Eq729BA_g sz z n) κ' (Eq729BA_E sz z n) (Eq729BA_m sz z n) := fun n =>
    GUELLBA_EdReal d κ' sz n (z n) (hgood n).1
  have hlam : ∀ᶠ n in atTop, 0 < Eq729BA_g sz z n ∧ Eq729BA_g sz z n ≤ 𝔡⁻¹ := by
    filter_upwards [hA.2.2.2.2, hhalf] with n hn hh
    have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
    refine ⟨mul_pos (Real.sqrt_pos.2 (by linarith)) hlam0, ?_⟩
    calc Real.sqrt (Eq729BA_t0 sz z n) * sz.lam n ≤ 1 * sz.lam n :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr (hgood n).2.2.2.le) hlam0.le
      _ ≤ 𝔡⁻¹ := by linarith [hn.2]
  exact Eq729B_eq747_of_eq729BA sz hd hA hκ hE (fun n => (ht n).1) hz (gueGridK_ne_zero sz n0)
    (gueGrid_eq729BA hd sz hκ' (inv_pos.2 hA.2.1) hτU n0 hn0 (Sizes.tendsto_size sz hA.2.2.1) hr hlam
      (fun n => (hgood n).2.1) (fun n => (hgood n).2.2.1) (fun n => (hgood n).2.2.2) h730 hscale hell Kt hKinit hK hK2 hB hP) τ hτ

/-! ## 9. The three producers at `UNKind.ba` (target 16: `ba_prodG`, `ba_LLG`, `ba_QueG`) -/

/-- `0 < t₀ < 1` forces `0 < Im m` and `0 < Im z` (`t₀ = Im m/(Im m + Im z)`, `Im m ≥ 0`, with `Im m = 0` only for the junk value `m = 0`). -/
private theorem GUEHyp_flow_pos (sz : Sizes d) (n : ℕ) (w : ℂ) (h0 : 0 < BAfT d sz n w) (h1 : BAfT d sz n w < 1) :
    0 < (BAm d (sz.L n) (sz.lam n) w).im ∧ 0 < w.im := by
  have hnn : 0 ≤ (BAm d (sz.L n) (sz.lam n) w).im := BAm_im_nonneg
  unfold BAfT BAt0 at h0 h1
  set mi : ℝ := (BAm d (sz.L n) (sz.lam n) w).im with hmi
  have hm : 0 < mi := by
    rcases hnn.lt_or_eq with h | h
    · exact h
    · rw [← h] at h0; simp at h0
  have hden : 0 < mi + w.im := by
    by_contra hnot
    have : mi / (mi + w.im) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hm.le (not_lt.1 hnot)
    linarith
  refine ⟨hm, ?_⟩
  rw [div_lt_one hden] at h1
  linarith

/-- **The primitive family of `BAKFam` exists** at flow data with `BAReal` at every `n` (`gueK_existsBA` at each `n` with `0 < g n`; the clauses are guarded). -/
private theorem GUEHyp_KFam_exists (sz : Sizes d) {κ' : ℝ} (hκ' : 0 < κ') {E' t1 t0 : ℕ → ℝ}
    (hr : ∀ n, BAReal d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) κ' (E' n)
      (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)))
    (ht1 : ∀ n, 0 ≤ t1 n) (ht10 : ∀ n, t1 n ≤ t0 n) (ht0 : ∀ n, t0 n < 1) :
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd d (sz.L n)) → ℂ, BAKFam d sz E' t1 t0 Kt := by
  classical
  have hex : ∀ n, ∃ Kt : ℝ → LoopIdx (Zd d (sz.L n)) → ℂ, 0 < Real.sqrt (t0 n) * sz.lam n →
      (∀ I, Kt (t1 n) I = BAKsol d (sz.L n) (sz.W n)
        (BAMsigma d (sz.L n) (BAMB d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)
          (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))))
        (PropSpin (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ))) (t1 n) I) ∧
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ I : LoopIdx (Zd d (sz.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * 4 →
        HasDerivWithinAt (fun u => Kt u I) (primRhsGUE d (sz.L n) (sz.W n) (Kt s) I) (Set.Icc (t1 n) (t0 n)) s) ∧
      (∀ s ∈ Set.Icc (t1 n) (t0 n), ∀ (σ₁ σ₂ : Bool) (a b : Zd d (sz.L n)),
        Kt s ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA d (sz.L n) (sz.W n) (Real.sqrt (t0 n) * sz.lam n) (E' n)
          (BAm d (sz.L n) (Real.sqrt (t0 n) * sz.lam n) (E' n : ℂ)) (t1 n) s σ₁ σ₂ a b) := fun n => by
    by_cases hg : 0 < Real.sqrt (t0 n) * sz.lam n
    · obtain ⟨K, h1, h2, h3⟩ := gueK_existsBA d (sz.L n) (sz.W n) (sz.three_le_L n) hg hκ' (hr n) (ht1 n) (ht10 n) (ht0 n) (4 * 4)
      exact ⟨K, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨fun _ _ => 0, fun h => absurd h hg⟩
  choose Kt hKt using hex
  exact ⟨Kt, fun n hn => (hKt n hn).1, fun n hn s hs I hI h1 h2 => (hKt n hn).2.1 s hs I hI h1 h2,
    fun n hn s hs σ₁ σ₂ a b => (hKt n hn).2.2 s hs σ₁ σ₂ a b⟩

/-- **`ba_LLG`, target 16b**: `RandomLayerB_LL` at the BA kind from `BAPB` (`oull_of_pathBoundsBA`; text `T2519_LLBA BAPB`). -/
theorem ba_LLG : ∀ d : ℕ, 3 ≤ d → RandomLayerB_LL (UNKind.ba d) (BAfE d) (BAfT d) (BAPB d) := by
  intro d _ 𝔠 𝔡 κ τU sz hA hκ hτU hτU1 E t hE ht Kt hP δ hδ p
  exact oull_of_pathBoundsBA sz hκ hτU hτU1 (Sizes.tendsto_size sz hA.2.2.1) (fun n => hE n) ht Kt hP δ hδ p

/-- **`ba_QueG`, target 16c**: `RBG_Que` at the BA kind with the BA profile `UNOUProfile.ba` (`Eq729B_eq747_of_inputsBA` at `n₀ = 4`; text
`T2519_QueBA BAKFam BAPB`): the clauses of `BAKFam` are `hKinit`, `hK`, `hK2`, `hB` is the third conjunct of `BAMO`, `hP` is `BAPB`. -/
theorem ba_QueG : ∀ d : ℕ, 3 ≤ d →
    RBG_Que (UNKind.ba d) (UNOUProfile.ba d) (BAEd d) (BAfE d) (BAfT d) (BAMO d) (BAKFam d) (BAPB d) := by
  intro d hd 𝔠 𝔡 κ κ' τU sz hA hκ hκ' hτU hτUm E t hE ht z hz hgood Kt hKF hMO hPB τ hτ
  exact Eq729B_eq747_of_inputsBA sz hd hA hκ hκ' hτU hτUm 4 le_rfl hE ht hz hgood Kt hKF.1 hKF.2.1 hKF.2.2 hMO.2.2 hPB τ hτ

/-- **`ba_prodG`, target 16a**: `RBG_Prod` at the BA vocabulary of C5g (`BAEd`, `BAfE`, `BAfT`, `BAMO`) with the primitive family `BAKFam` and the path bounds
`BAPB` (text `T2519_ProdBA BAKFam BAPB`; twin of `RandomLayerB_prod_band`, `RandomLayerB:400`): `Kt` is the family of `gueK_existsBA` (`GUEHyp_KFam_exists`),
`PB` is `gueGrid_pathBoundsBA` at `n₀ = 4` (row c) at the flow datum `(g, E, m) = (√t₀ λ, BAfE, BAm …)` (`GUELLBA_EdReal`: `BAEd κ'` is `BAReal`; `GUELLBA_flowEta`: the
scale `√t₀ Im z` of `h730`, `hscale` is `η_{t₀}`); `hell1` forces `t₀ ≥ t₁ ≥ 26/27`, so `t₀ > 0`, `Im z > 0` and `0 < g ≤ 𝔡⁻¹` eventually; `hell` in the
form `L^d (1 - t₁) ≤ 2 g²` is `GUEHypABA_hell_of_hell`; `hLK`, `hLoc` are the first two conjuncts of `BAMO`. -/
theorem ba_prodG : ∀ d : ℕ, 3 ≤ d → RBG_Prod (BAEd d) (BAfE d) (BAfT d) (BAMO d) (BAKFam d) (BAPB d) := by
  intro d hd 𝔠 𝔡 κ' τD sz hA hκ' hτD z t1 hEd ht1 ht10 ht0 h730 hscale hell hell1 hMO
  have hr : ∀ n, BAReal d (sz.L n) (Real.sqrt (BAfT d sz n (z n)) * sz.lam n) κ' (BAfE d sz n (z n))
      (BAm d (sz.L n) (Real.sqrt (BAfT d sz n (z n)) * sz.lam n) (BAfE d sz n (z n) : ℂ)) := fun n =>
    GUELLBA_EdReal d κ' sz n (z n) (hEd n)
  obtain ⟨Kt, hKF⟩ := GUEHyp_KFam_exists sz hκ' (E' := fun n => BAfE d sz n (z n)) (t0 := fun n => BAfT d sz n (z n)) hr ht1 ht10 ht0
  refine ⟨Kt, hKF, ?_⟩
  have hpos : ∀ᶠ n in atTop, 0 < (z n).im ∧ 0 < BAfT d sz n (z n) := by
    filter_upwards [hell1] with n h1
    have hL3 : (3 : ℝ) ≤ (sz.L n : ℝ) := by exact_mod_cast sz.three_le_L n
    have h27 : (27 : ℝ) ≤ (sz.L n : ℝ) ^ d :=
      calc (27 : ℝ) = 3 ^ 3 := by norm_num
        _ ≤ (sz.L n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hL3 3
        _ ≤ (sz.L n : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
    have ht1ge : 26 / 27 ≤ t1 n := by
      by_contra hc
      have : 1 / 27 < 1 - t1 n := by linarith [not_le.1 hc]
      nlinarith
    have hft0 : 0 < BAfT d sz n (z n) := by linarith [ht10 n]
    exact ⟨(GUEHyp_flow_pos sz n (z n) hft0 (ht0 n)).2, hft0⟩
  have h730' : ∀ᶠ n in atTop, BAfT d sz n (z n) - t1 n ≤ Nsz sz n ^ (-τD) *
      etaOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n (z n)) * sz.lam n) (BAfE d sz n (z n) : ℂ)) (BAfT d sz n (z n)) := by
    filter_upwards [h730, hpos] with n h hp
    rwa [GUELLBA_flowEta d sz n (z n) hp.1]
  have hscale' : ∀ᶠ n in atTop, (Nsz sz n * etaOf (BAm d (sz.L n) (Real.sqrt (BAfT d sz n (z n)) * sz.lam n)
      (BAfE d sz n (z n) : ℂ)) (BAfT d sz n (z n)))⁻¹ ≤ Nsz sz n ^ (-τD) := by
    filter_upwards [hscale, hpos] with n h hp
    rwa [GUELLBA_flowEta d sz n (z n) hp.1]
  have hlam : ∀ᶠ n in atTop, 0 < Real.sqrt (BAfT d sz n (z n)) * sz.lam n ∧ Real.sqrt (BAfT d sz n (z n)) * sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hA.2.2.2.2, hpos] with n hn hp
    have hlam0 : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hn.1
    refine ⟨mul_pos (Real.sqrt_pos.2 hp.2) hlam0, ?_⟩
    calc Real.sqrt (BAfT d sz n (z n)) * sz.lam n ≤ 1 * sz.lam n :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr (ht0 n).le) hlam0.le
      _ ≤ 𝔡⁻¹ := by linarith [hn.2]
  have hellg : ∀ᶠ n in atTop, ((sz.L n : ℕ) : ℝ) ^ d * (1 - t1 n) ≤ 2 * (Real.sqrt (BAfT d sz n (z n)) * sz.lam n) ^ 2 := by
    filter_upwards [hell, hell1] with n h h1
    exact GUEHypABA_hell_of_hell hd (sz.three_le_L n) (ht10 n) h h1
  exact gueGrid_pathBoundsBA sz hd hA hκ' hτD (g := fun n => Real.sqrt (BAfT d sz n (z n)) * sz.lam n)
    (E := fun n => BAfE d sz n (z n)) (t0 := fun n => BAfT d sz n (z n)) hr hlam ht1 ht10 ht0 h730' hscale' hell hell1 hellg Kt
    hKF.1 hKF.2.1 hMO.1 hMO.2.1

/-! ## 10. One grid step of the BA primitive 2-loop (target 15, `baEq729_Kdisc`) -/

/-- **`baEq729_Kdisc`, target 15** (T2517 target 8, moved to C5 by T2517 Decision (1); text `T2519_KdiscBA`): `eq729_Kdisc` (`Eq729A:562`) at the BA primitive
`Kf = kTwoGUELoopBA … t₁` on real-axis data `BAReal d L g κ E m`.  `hKd` is `hasDerivAt_kTwoGUELoopBA` (`GUEKPrim:776`); `b₂ ≤ 1` stays a premise (fed by `Hyp_Kt_detDomBA`
or the bound of `GUEHyp_kTwo_le`). -/
theorem baEq729_Kdisc :
    ∀ (d L : ℕ) [NeZero L] (W : ℕ) [NeZero W] (g κ E : ℝ) (m : ℂ), BAReal d L g κ E m →
      ∀ {t1 t0 u Δ b2 : ℝ}, 0 ≤ t1 → t0 < 1 → u ∈ Set.Icc t1 t0 → u + Δ ∈ Set.Icc t1 t0 → 0 ≤ Δ → b2 ≤ 1 →
        (((W * L) ^ d : ℕ) : ℝ) * Δ ≤ 1 →
        (∀ s ∈ Set.Icc t1 t0, ∀ s1 s2 x y, ‖kTwoGUELoopBA d L W g E m t1 s ⟨[s1, s2], [x, y]⟩‖ ≤ b2) →
        ∀ (s1 s2 : Bool) (a1 a2 : Zd d L),
          ‖kTwoGUELoopBA d L W g E m t1 u ⟨[s1, s2], [a1, a2]⟩ +
              (Δ : ℂ) * primRhsGUE d L W (kTwoGUELoopBA d L W g E m t1 u) ⟨[s1, s2], [a1, a2]⟩ -
            kTwoGUELoopBA d L W g E m t1 (u + Δ) ⟨[s1, s2], [a1, a2]⟩‖ ≤
            3 * (((W * L) ^ d : ℕ) : ℝ) ^ 2 * Δ ^ 2 := by
  intro d L _ W _ g κ E m hr t1 t0 u Δ b2 ht1 ht0 hu hu' hΔ hb2 hMΔ hKb s1 s2 a1 a2
  refine eq729_Kdisc (W := W) (kTwoGUELoopBA d L W g E m t1) hu hu' hΔ hb2 hMΔ hKb ?_ s1 s2 a1 a2
  intro s hs s1 s2 x y
  exact (hasDerivAt_kTwoGUELoopBA d L W g κ E m hr t1 s ht1 hs.1 (lt_of_le_of_lt hs.2 ht0) s1 s2 x y).hasDerivWithinAt

/-- **A bound for the BA primitive 2-loop at `t₁ = 0`**: `‖K̃_{t,(σ₁,σ₂),(a,b)}‖ ≤ 2 W^{-d}` for `0 ≤ t ≤ 1/2` (`Θ_0 = 1`, `K̃ = W^{-d} (Q_{ab} + β r)`, `|Q_{ab}| ≤ 1`, `|r| ≤ 1`,
`|β| ≤ t/(1 - t) ≤ 1`).  It feeds `hKb` of the instance of `baEq729_Kdisc`. -/
private theorem GUEHyp_kTwo_le {d L : ℕ} [NeZero L] (W : ℕ) {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) (σ₁ σ₂ : Bool) (a b : Zd d L) :
    ‖kTwoGUEBA d L W g E m 0 t σ₁ σ₂ a b‖ ≤ 2 * (((W : ℝ) ^ d)⁻¹) := by
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ with hQ
  obtain ⟨-, hJQ⟩ := GUEKPrim_QJ (d := d) (L := L) (Q := Q)
    (fun a b r => EKNonzero_Mss_shift (d := d) (L := L) g E m σ₁ σ₂ a b r)
  have hTh : BATheta d L g E m 0 σ₁ σ₂ = 1 := by unfold BATheta PropThetaQ; simp
  have hent : kTwoGUEBA d L W g E m 0 t σ₁ σ₂ a b =
      ((W : ℂ) ^ d)⁻¹ * (Q a b + gueShift d L (∑ c, Q 0 c) 0 t * ∑ c, Q 0 c) := by
    unfold kTwoGUEBA
    change ((W : ℂ) ^ d)⁻¹ * ((BATheta d L g E m 0 σ₁ σ₂ + gueShift d L (∑ c, Q 0 c) 0 t • Jmat d L) * Q) a b = _
    rw [hTh, add_mul, one_mul, Matrix.smul_mul, hJQ, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    simp [Jmat]
  have hQab : ‖Q a b‖ ≤ 1 := by
    rw [hQ, BAMss_norm_eq_BAK, ← BAK_row_sum d L g E m hr.1 a]
    exact Finset.single_le_sum (f := fun x => BAK d L g E m a x) (fun x _ => BAK_nonneg d L g E m a x) (Finset.mem_univ b)
  have hr0 : ‖∑ c, Q 0 c‖ ≤ 1 := GUEKPrim_r0_norm hr σ₁ σ₂
  set r : ℂ := ∑ c, Q 0 c with hrdef
  have hL1 : (1 : ℝ) ≤ ‖(L : ℂ) ^ d‖ := by
    rw [norm_pow, Complex.norm_natCast]
    exact one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hden : (1 / 2 : ℝ) ≤ ‖1 - (t : ℂ) * r‖ := by
    have h1 : ‖(t : ℂ) * r‖ ≤ t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      calc t * ‖r‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hr0 ht0
        _ = t := mul_one t
    have := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * r)
    rw [norm_one] at this
    linarith
  have hβ : ‖gueShift d L r 0 t‖ ≤ 1 := by
    unfold gueShift
    simp only [Complex.ofReal_zero, sub_zero, zero_mul, sub_zero, mul_one]
    rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [div_le_one (mul_pos (by linarith) (by linarith))]
    have h1 : t * ‖r‖ ≤ 1 / 2 := by nlinarith [norm_nonneg r]
    nlinarith [mul_le_mul hL1 hden (by norm_num) (norm_nonneg _)]
  rw [hent, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((W : ℝ) ^ d)⁻¹ * ‖Q a b + gueShift d L r 0 t * r‖ ≤ ((W : ℝ) ^ d)⁻¹ * 2 := by
        gcongr
        calc ‖Q a b + gueShift d L r 0 t * r‖ ≤ ‖Q a b‖ + ‖gueShift d L r 0 t * r‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by
              rw [norm_mul]
              nlinarith [norm_nonneg r, norm_nonneg (gueShift d L r 0 t)]
          _ = 2 := by norm_num
    _ = 2 * ((W : ℝ) ^ d)⁻¹ := mul_comm _ _

/-! ## 11. Compiled nonempty instances (CLAUDE.md §4 step 2)

`RBM.BA.GUEHypInst`.  `d = 3`.  `baEq729_Kdisc`: the merged flow point `P` (`BA/MFixedPoint`: `(L, g) = (4, 10)`, `P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`), `W = 2`
(`N = (W L)^d = 512`), `t₁ = 0`, `t₀ = 1/2`, `u = 1/4`, `Δ = 1/1024` (`N Δ = 1/2`), `b₂ = 1`; `hKb` is `GUEHyp_kTwo_le` (`‖K̃‖ ≤ 2 W^{-d} = 1/4`). -/

namespace GUEHypInst

open RBM.BA.MFixedPointInst

/-- **`baEq729_Kdisc` at `P`**: every deterministic hypothesis is discharged (`BAReal`, `0 ≤ t₁`, `t₀ < 1`, `u, u + Δ ∈ [t₁, t₀]`, `Δ ≥ 0`, `b₂ ≤ 1`, `N Δ ≤ 1`, `hKb`). -/
example (s1 s2 : Bool) (a1 a2 : Zd 3 4) :
    ‖kTwoGUELoopBA 3 4 2 P.g0 P.E P.m0 0 (1 / 4) ⟨[s1, s2], [a1, a2]⟩ +
        ((1 / 1024 : ℝ) : ℂ) * primRhsGUE 3 4 2 (kTwoGUELoopBA 3 4 2 P.g0 P.E P.m0 0 (1 / 4)) ⟨[s1, s2], [a1, a2]⟩ -
      kTwoGUELoopBA 3 4 2 P.g0 P.E P.m0 0 (1 / 4 + 1 / 1024) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      3 * (((2 * 4) ^ 3 : ℕ) : ℝ) ^ 2 * (1 / 1024 : ℝ) ^ 2 :=
  baEq729_Kdisc 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (t1 := 0) (t0 := 1 / 2) (u := 1 / 4) (Δ := 1 / 1024) (b2 := 1) le_rfl
    (by norm_num) ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num) le_rfl (by norm_num)
    (fun s hs s1 s2 x y => (GUEHyp_kTwo_le 2 P.real hs.1 hs.2 s1 s2 x y).trans (by norm_num)) s1 s2 a1 a2

end GUEHypInst

/-! ## 12. Instances at the class sequence `S0` (`BA/UNPins`)

`S0 = clsS 4 _ (3/10)`: `L = 4`, `W_n = (2 (n+1))^5`, the constant coupling `λ = g₀ := (fp 4 _).g₀ ∈ (0, 3/10]`, admissible at `(𝔠, 𝔡) = (1/6, 1/10)`, the energy `E_* := (fp 4 _).E`
in the ρ-bulk at `κ_* = clsκ 4 _` for every `n` (`cls_bulk`).  `ba_flowG` at `κ_*` gives `(κ', c, c_T)` (`c` is clamped to `≤ 1`: `1 - t₀ ≤ Im z / c ≤ Im z / min (c, 1)`);
the Lemma 2.8 facts hold at every `z = E_* + i y`, `0 < y ≤ 1`.  Amend 5 item 4 (C5D-C2): the producer instance sits in the GUE phase, `Im z_n = η := c g₀² / (2 L³)` (`L = 4`),
`t₁ := t₀ - N^{-τ_D} √t₀ η`, `τ_D = 1/20`, never at `zSeq`. -/

namespace GUEHypInst

open RBM.Univ.BAInst RBM.BA.UNPinsInst

private theorem hg : (0 : ℝ) < 3 / 10 := by norm_num

private abbrev E0 : ℝ := (fp 4 hg).E
private abbrev g0 : ℝ := (fp 4 hg).g0

private theorem g0_pos : 0 < g0 := (fp 4 hg).g0_pos
private theorem g0_le : g0 ≤ 3 / 10 := (fp 4 hg).g0_le

/-- `ba_flowG` at `κ_*` (`clsκ`) restricted to the points `E_* + i y`, with `c ≤ 1`. -/
private theorem flowS0 : ∃ κ'' c cT : ℝ, 0 < κ'' ∧ 0 < c ∧ c ≤ 1 ∧ 0 < cT ∧ ∀ (n : ℕ) (z : ℂ), z.re = E0 → 0 < z.im →
    z.im ≤ 1 → BAEd 3 κ'' S0 n z ∧ cT ≤ BAfT 3 S0 n z ∧ BAfT 3 S0 n z < 1 ∧ 1 - BAfT 3 S0 n z ≤ z.im / c := by
  obtain ⟨κ'', c, cT, hκ'', hc, hcT, hF⟩ := ba_flowG 3 (clsκ 4 hg) (clsκ_pos 4 hg)
  refine ⟨κ'', min c 1, cT, hκ'', lt_min hc one_pos, min_le_right _ _, hcT, fun n z hre him0 him1 => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hF S0 n z (by change BAbulk 3 4 g0 (clsκ 4 hg) z.re; rw [hre]; exact cls_bulk 4 (by norm_num) hg)
    him0 him1
  exact ⟨h1, h2, h3, h4.trans (div_le_div_of_nonneg_left him0.le (lt_min hc one_pos) (min_le_left _ _))⟩

private noncomputable def κI : ℝ := Classical.choose flowS0
private noncomputable def cI : ℝ := Classical.choose (Classical.choose_spec flowS0)
private noncomputable def cTI : ℝ := Classical.choose (Classical.choose_spec (Classical.choose_spec flowS0))

private theorem flowS0_spec : 0 < κI ∧ 0 < cI ∧ cI ≤ 1 ∧ 0 < cTI ∧ ∀ (n : ℕ) (z : ℂ), z.re = E0 → 0 < z.im → z.im ≤ 1 →
    BAEd 3 κI S0 n z ∧ cTI ≤ BAfT 3 S0 n z ∧ BAfT 3 S0 n z < 1 ∧ 1 - BAfT 3 S0 n z ≤ z.im / cI :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec flowS0))

/-- `(N κ₁)⁻¹ ≤ N^{-τ}` eventually for `0 < τ < 1`, `κ₁ > 0`, `N → ∞`. -/
private theorem GUEHyp_scale_ev {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) {κ1 τ : ℝ} (hκ1 : 0 < κ1) (hτ1 : τ < 1) :
    ∀ᶠ n in atTop, (N n * κ1)⁻¹ ≤ N n ^ (-τ) := by
  filter_upwards [((tendsto_rpow_atTop (sub_pos.2 hτ1)).comp hN).eventually_ge_atTop κ1⁻¹, hN.eventually_ge_atTop 1] with n h1 h2
  have hN0 : 0 < N n := by linarith
  have hsplit : N n = N n ^ τ * N n ^ (1 - τ) := by
    rw [← Real.rpow_add hN0]; simp
  rw [Real.rpow_neg hN0.le]
  refine inv_anti₀ (Real.rpow_pos_of_pos hN0 _) ?_
  have h3 : 1 ≤ κ1 * N n ^ (1 - τ) := by
    rw [inv_le_iff_one_le_mul₀' hκ1] at h1
    exact h1
  calc N n ^ τ = N n ^ τ * 1 := (mul_one _).symm
    _ ≤ N n ^ τ * (κ1 * N n ^ (1 - τ)) := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hN0.le _)
    _ = N n ^ τ * N n ^ (1 - τ) * κ1 := by ring
    _ = N n * κ1 := by rw [← hsplit]

/-- The GUE-phase scale `η = c g₀² / (2 L³)`, `L = 4`: `Im z_n = η` at every `n`. -/
private noncomputable def etaI : ℝ := cI * g0 ^ 2 / (2 * 4 ^ 3)

private theorem etaI_pos : 0 < etaI := by
  have := flowS0_spec.2.1; have := g0_pos; unfold etaI; positivity

private theorem etaI_le : etaI ≤ g0 ^ 2 / 128 := by
  have h1 := flowS0_spec.2.2.1; have := flowS0_spec.2.1; have := g0_pos
  unfold etaI
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg g0]

private theorem g0sq_le : g0 ^ 2 ≤ 9 / 100 := by nlinarith [g0_pos, g0_le]

private theorem etaI_le_one : etaI ≤ 1 := etaI_le.trans (by nlinarith [g0sq_le])

/-- The point `z_n = E_* + i η`. -/
private noncomputable def zI : ℕ → ℂ := fun _ => ⟨E0, etaI⟩

/-- `t₀ = fT` at `z_n` (constant along `S0`). -/
private noncomputable def fI : ℝ := BAfT 3 S0 0 ⟨E0, etaI⟩

private theorem fI_eq (n : ℕ) : BAfT 3 S0 n (zI n) = fI := rfl

private theorem zI_im (n : ℕ) : (zI n).im = etaI := rfl

private theorem fI_facts : BAEd 3 κI S0 0 ⟨E0, etaI⟩ ∧ cTI ≤ fI ∧ fI < 1 ∧ 1 - fI ≤ g0 ^ 2 / 128 := by
  obtain ⟨-, hc, -, -, hF⟩ := flowS0_spec
  obtain ⟨h1, h2, h3, h4⟩ := hF 0 ⟨E0, etaI⟩ rfl etaI_pos etaI_le_one
  refine ⟨h1, h2, h3, h4.trans (le_of_eq ?_)⟩
  change etaI / cI = g0 ^ 2 / 128
  unfold etaI; field_simp; ring

private theorem fI_pos : 0 < fI := lt_of_lt_of_le flowS0_spec.2.2.2.1 fI_facts.2.1

private theorem sqrt_fI_le : Real.sqrt fI ≤ 1 := Real.sqrt_le_one.mpr fI_facts.2.2.1.le

/-- `t₁ = t₀ - N^{-τ_D} √t₀ η`, `τ_D = 1/20`. -/
private noncomputable def t1I (n : ℕ) : ℝ := fI - Nsz S0 n ^ (-(1 / 20 : ℝ)) * (Real.sqrt fI * etaI)

private theorem Nsz_S0_one (n : ℕ) : (1 : ℝ) ≤ Nsz S0 n := by exact_mod_cast S0.one_le_size n

private theorem off_bounds (n : ℕ) : 0 ≤ Nsz S0 n ^ (-(1 / 20 : ℝ)) * (Real.sqrt fI * etaI) ∧
    Nsz S0 n ^ (-(1 / 20 : ℝ)) * (Real.sqrt fI * etaI) ≤ etaI := by
  have h0 : 0 ≤ Nsz S0 n ^ (-(1 / 20 : ℝ)) := Real.rpow_nonneg (by have := Nsz_S0_one n; linarith) _
  have h1 : Nsz S0 n ^ (-(1 / 20 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (Nsz_S0_one n) (by norm_num)
  have h2 := sqrt_fI_le
  have h3 : 0 ≤ Real.sqrt fI := Real.sqrt_nonneg _
  have h4 := etaI_pos
  refine ⟨by positivity, ?_⟩
  calc Nsz S0 n ^ (-(1 / 20 : ℝ)) * (Real.sqrt fI * etaI) ≤ 1 * (1 * etaI) := by gcongr
    _ = etaI := by ring

private theorem t1I_nonneg (n : ℕ) : 0 ≤ t1I n := by
  have := (off_bounds n).2; have := etaI_le; have := g0sq_le; have := fI_facts.2.2.2
  unfold t1I; nlinarith

private theorem t1I_le (n : ℕ) : t1I n ≤ fI := by
  have := (off_bounds n).1
  unfold t1I; linarith

private theorem hellI (n : ℕ) : ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - t1I n) ≤ S0.lam n ^ 2 := by
  have := (off_bounds n).2; have := etaI_le; have := fI_facts.2.2.2
  change (((4 : ℕ) : ℝ)) ^ 3 * (1 - t1I n) ≤ g0 ^ 2
  unfold t1I; norm_num; nlinarith

private theorem hell1I (n : ℕ) : ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - t1I n) ≤ 1 :=
  (hellI n).trans (show g0 ^ 2 ≤ 1 by have := g0sq_le; linarith)

/-- **`ba_prodG` in the GUE-phase regime at `S0`** (Amend 5 item 4, C5D-C2): `E_*` in the bulk, `Im z_n = η = c g₀²/(2 L³)`, `t₁ = t₀ - N^{-1/20} √t₀ η`, `τ_D = 1/20`.  Every
deterministic premise of `RBG_Prod` holds at the data (`Ed κ'` and `0 ≤ t₁ ≤ t₀ < 1`, `h730` (equality), `hell`, `hell1` at **every** `n`; `hscale` from `N_n^{19/20} ≥ 2/η` on:
`N_n = 64 (2 (n+1))^{15}`); the `G`-loop outputs `MO = BAMO` (V3's pin `UNMLOutBA`) stay a hypothesis, as in row c. -/
example (hMO : BAMO 3 S0 zI t1I) : ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ,
    BAKFam 3 S0 (fun n => BAfE 3 S0 n (zI n)) t1I (fun n => BAfT 3 S0 n (zI n)) Kt ∧
      BAPB 3 S0 (fun n => BAfE 3 S0 n (zI n)) t1I (fun n => BAfT 3 S0 n (zI n)) Kt :=
  ba_prodG 3 le_rfl (1 / 6) (1 / 10) κI (1 / 20) S0 S0_adm flowS0_spec.1 (by norm_num) zI t1I
    (fun n => (flowS0_spec.2.2.2.2 n (zI n) rfl etaI_pos etaI_le_one).1) t1I_nonneg t1I_le (fun n => fI_facts.2.2.1)
    (Eventually.of_forall fun n => le_of_eq (by simp only [t1I, fI_eq, zI_im]; ring))
    (GUEHyp_scale_ev (N := fun n => Nsz S0 n) S0_adm.2.2.1 (mul_pos (Real.sqrt_pos.2 fI_pos) etaI_pos) (by norm_num : (1 / 20 : ℝ) < 1))
    (Eventually.of_forall hellI) (Eventually.of_forall hell1I) hMO

/-- **`ba_LLG` at `S0`** (`E ≡ E_*`, `τ_U = 1/100`, `t_n = N^{-1+τ_U} > 0`, `δ = 1/10`): the path bounds `BAPB` at the Lemma 2.8 data (the output of the §7.2 random layer, another
gate's pin) stay a hypothesis; the output is the body of `UNOULLk (UNKind.ba 3) S0 (1/100)`. -/
example (Kt : ∀ n, ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ)
    (hP : BAPB 3 S0 (fun n => BAfE 3 S0 n ((E0 : ℂ) + ((ouEtaLL S0 (1 / 100) n : ℝ) : ℂ) * Complex.I))
      (fun n => (1 - ouZeta (ouTStar S0 (1 / 100) n)) *
        BAfT 3 S0 n ((E0 : ℂ) + ((ouEtaLL S0 (1 / 100) n : ℝ) : ℂ) * Complex.I))
      (fun n => BAfT 3 S0 n ((E0 : ℂ) + ((ouEtaLL S0 (1 / 100) n : ℝ) : ℂ) * Complex.I)) Kt) (p : ℕ) :
    ∀ᶠ n in atTop, RandomLayerB_LLAt (UNKind.ba 3) S0 (1 / 100) n E0 (ouTStar S0 (1 / 100) n) (1 / 10) p :=
  ba_LLG 3 le_rfl (1 / 6) (1 / 10) (clsκ 4 hg) (1 / 100) S0 S0_adm (clsκ_pos 4 hg) (by norm_num) (by norm_num)
    (fun _ => E0) (ouTStar S0 (1 / 100)) (fun _ => cls_bulk 4 (by norm_num) hg)
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) Kt hP (1 / 10) (by norm_num) p

/-! The QUE point at `S0`: `E ≡ E_*`, `t_n = ouTStar S0 τ_U n = N^{-1+τ_U} > 0`, `τ_U = ouTauMax (1/6) (1/10) = 1/720`, `z_n = E_* + i min (η_Q(n), 1)`
(`η_Q = W^{-𝔡/3} λ W^{d/2}/N`, `𝔡 = 1/10`; `0 < η_Q ≤ 1` eventually, so `z_n = E_* + i η_Q` eventually, and `0 < Im z_n ≤ 1` at every `n`). -/

private theorem tauU_pos : 0 < ouTauMax (1 / 6) (1 / 10) := ouTauMax_pos (by norm_num) (by norm_num)

private noncomputable def zQ : ℕ → ℂ := fun n => (E0 : ℂ) + ((min (ouEtaQ S0 (1 / 10) n) 1 : ℝ) : ℂ) * Complex.I

private noncomputable def tQ (n : ℕ) : ℝ := ouTStar S0 (ouTauMax (1 / 6) (1 / 10)) n

private theorem tQ_ok (n : ℕ) : 0 ≤ tQ n ∧ tQ n ≤ ouTStar S0 (ouTauMax (1 / 6) (1 / 10)) n :=
  ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _, le_rfl⟩

private theorem zQ_im (n : ℕ) : 0 < (zQ n).im ∧ (zQ n).im ≤ 1 := by
  have hlam : 0 < S0.lam n := g0_pos
  have h0 : 0 < ouEtaQ S0 (1 / 10) n := RandomLayer_etaQ_pos S0 (1 / 10) hlam
  simp only [zQ, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_add, add_zero]
  exact ⟨lt_min h0 one_pos, min_le_right _ _⟩

private theorem zQ_ev : ∀ᶠ n in atTop, zQ n = Eq729B_zQ S0 (1 / 10) (fun _ => E0) n := by
  filter_upwards [RandomLayer_etaQ_le_one S0 S0_adm] with n h
  have hm : min (ouEtaQ S0 (1 / 10) n) 1 = ouEtaQ S0 (1 / 10) n := min_eq_left h
  simp only [zQ, Eq729B_zQ, hm]

private theorem hgoodQ (n : ℕ) : BAEd 3 κI S0 n (zQ n) ∧ 0 ≤ (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n) ∧
    (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n) ≤ BAfT 3 S0 n (zQ n) ∧ BAfT 3 S0 n (zQ n) < 1 := by
  obtain ⟨-, -, -, hcT, hF⟩ := flowS0_spec
  obtain ⟨h1, h2, h3, -⟩ := hF n (zQ n) (by simp [zQ]) (zQ_im n).1 (zQ_im n).2
  have hζ0 := ZeroModeProfile_ouZeta_nonneg (tQ_ok n).1
  have hζ1 := ZeroModeProfile_ouZeta_le_one (tQ n)
  have hf0 : 0 < BAfT 3 S0 n (zQ n) := lt_of_lt_of_le hcT h2
  exact ⟨h1, mul_nonneg (by linarith) hf0.le, by nlinarith, h3⟩

/-- **`Eq729B_derivedBA` at `S0`** (every hypothesis discharged): `h730`, `hscale`, `hell` (`2 g²` form) and `t₀ ≥ 1/2`, eventually. -/
example : (∀ᶠ n in atTop, Eq729BA_t0 S0 zQ n - Eq729BA_t1 S0 tQ zQ n ≤
        Nsz S0 n ^ (-(ouTauMax (1 / 6) (1 / 10))) * etaOf (Eq729BA_m S0 zQ n) (Eq729BA_t0 S0 zQ n)) ∧
      (∀ᶠ n in atTop, (Nsz S0 n * etaOf (Eq729BA_m S0 zQ n) (Eq729BA_t0 S0 zQ n))⁻¹ ≤
        Nsz S0 n ^ (-(ouTauMax (1 / 6) (1 / 10)))) ∧
      (∀ᶠ n in atTop, ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - Eq729BA_t1 S0 tQ zQ n) ≤ 2 * Eq729BA_g S0 zQ n ^ 2) ∧
      (∀ᶠ n in atTop, 1 / 2 ≤ Eq729BA_t0 S0 zQ n) :=
  Eq729B_derivedBA S0 S0_adm (clsκ_pos 4 hg) tauU_pos le_rfl (E := fun _ => E0) (t := tQ) (fun _ => cls_bulk 4 (by norm_num) hg)
    tQ_ok zQ_ev

/-- **`ba_QueG` at `S0`**: `Ed κ'` and `0 ≤ t₁ ≤ t₀ < 1` at every `n` (`hgood`), the primitive family `Kt` of `BAKFam` (`gueK_existsBA`, `GUEHyp_KFam_exists`) and the
eventual form of `z_n` are discharged; the `G`-loop outputs `BAMO` (V3's pin) and the path bounds `BAPB` at the flow datum (the output of the §7.2 random layer) stay
hypotheses.  `τ = 1/100`. -/
example (hMO : BAMO 3 S0 zQ (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))) :
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ,
      BAKFam 3 S0 (fun n => BAfE 3 S0 n (zQ n)) (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))
        (fun n => BAfT 3 S0 n (zQ n)) Kt ∧
      (BAPB 3 S0 (fun n => BAfE 3 S0 n (zQ n)) (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))
        (fun n => BAfT 3 S0 n (zQ n)) Kt →
        ∀ᶠ n in atTop, RandomLayerB_QueAt (UNKind.ba 3) (UNOUProfile.ba 3) S0 (1 / 10) n E0 (tQ n) (1 / 100)) := by
  obtain ⟨Kt, hKF⟩ := GUEHyp_KFam_exists S0 flowS0_spec.1 (E' := fun n => BAfE 3 S0 n (zQ n))
    (t1 := fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n)) (t0 := fun n => BAfT 3 S0 n (zQ n))
    (fun n => GUELLBA_EdReal 3 κI S0 n (zQ n) (hgoodQ n).1) (fun n => (hgoodQ n).2.1) (fun n => (hgoodQ n).2.2.1)
    (fun n => (hgoodQ n).2.2.2)
  exact ⟨Kt, hKF, fun hPB => ba_QueG 3 le_rfl (1 / 6) (1 / 10) (clsκ 4 hg) κI (ouTauMax (1 / 6) (1 / 10)) S0 S0_adm
    (clsκ_pos 4 hg) flowS0_spec.1 tauU_pos le_rfl (fun _ => E0) tQ (fun _ => cls_bulk 4 (by norm_num) hg) tQ_ok zQ zQ_ev hgoodQ Kt hKF
    hMO hPB (1 / 100) (by norm_num)⟩

/-- **`Eq729B_eq747_of_inputsBA` at `S0`** (the same data; `n₀ = 4`): `ba_QueG` is this theorem at the clauses of `BAKFam`; here its inputs are given directly. -/
example (hMO : BAMO 3 S0 zQ (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))) :
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ,
      BAKFam 3 S0 (fun n => BAfE 3 S0 n (zQ n)) (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))
        (fun n => BAfT 3 S0 n (zQ n)) Kt ∧
      (GUEPathBoundsBA S0 (Eq729BA_g S0 zQ) (Eq729BA_E S0 zQ) (Eq729BA_t1 S0 tQ zQ) (Eq729BA_t0 S0 zQ) (Eq729BA_m S0 zQ)
        (gueGridK S0 4) 4 Kt →
        ∀ᶠ n in atTop, RandomLayerB_QueAt (UNKind.ba 3) (UNOUProfile.ba 3) S0 (1 / 10) n E0 (tQ n) (1 / 100)) := by
  obtain ⟨Kt, hKF⟩ := GUEHyp_KFam_exists S0 flowS0_spec.1 (E' := fun n => BAfE 3 S0 n (zQ n))
    (t1 := fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n)) (t0 := fun n => BAfT 3 S0 n (zQ n))
    (fun n => GUELLBA_EdReal 3 κI S0 n (zQ n) (hgoodQ n).1) (fun n => (hgoodQ n).2.1) (fun n => (hgoodQ n).2.2.1)
    (fun n => (hgoodQ n).2.2.2)
  exact ⟨Kt, hKF, fun hP => Eq729B_eq747_of_inputsBA S0 le_rfl S0_adm (clsκ_pos 4 hg) flowS0_spec.1 tauU_pos le_rfl 4 le_rfl
    (E := fun _ => E0) (t := tQ) (fun _ => cls_bulk 4 (by norm_num) hg) tQ_ok zQ_ev hgoodQ Kt hKF.1 hKF.2.1 hKF.2.2 hMO.2.2 hP
    (1 / 100) (by norm_num)⟩

/-! The window of the instance of `gueGrid_eq729BA`: the flow datum is the merged flow point `(g₀, E_*, m₀) = (fp 4 _).{g0, E, m0}` (`BAReal` at `κ = Im m₀`, constant in `n`), the GUE-phase
window `1 - t₀ = x`, `t₀ - t₁ = x / (2 N_n)`, `x = g₀² / 128` (so `L³ (1 - t₁) ≤ 128 x = g₀²`), `τ_U = 1/20`, `n₀ = 4`. -/

private noncomputable def xI : ℝ := g0 ^ 2 / 128
private noncomputable def t0S (_ : ℕ) : ℝ := 1 - xI
private noncomputable def t1S (n : ℕ) : ℝ := 1 - xI - xI / (2 * Nsz S0 n)

private theorem xI_pos : 0 < xI := by have := g0_pos; unfold xI; positivity
private theorem xI_le : xI ≤ 1 / 1000 := by have := g0sq_le; unfold xI; linarith

private theorem t1S_bounds (n : ℕ) : 0 ≤ t1S n ∧ t1S n ≤ t0S n ∧ t0S n < 1 ∧ 64 * (1 - t1S n) ≤ g0 ^ 2 := by
  have hN := Nsz_S0_one n
  have hx := xI_pos
  have hxle := xI_le
  have h2 : xI / (2 * Nsz S0 n) ≤ xI / 2 := by
    apply div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
  have h3 : 0 ≤ xI / (2 * Nsz S0 n) := by positivity
  have hg2 : g0 ^ 2 = 128 * xI := by unfold xI; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold t1S; linarith
  · unfold t1S t0S; linarith
  · unfold t0S; linarith
  · unfold t1S; rw [hg2]; nlinarith

private theorem etaOf_S (n : ℕ) : etaOf (fp 4 hg).m0 (t0S n) = xI * (fp 4 hg).m0.im := by
  unfold etaOf t0S; ring

/-- **`gueGrid_eq729BA` at `S0`** (the merged flow point, the GUE-phase window above): every deterministic hypothesis is discharged (`BAReal` at every `n`, `0 < g ≤ 10`, `0 ≤ t₁ ≤ t₀ < 1`,
`h730`, `hscale` (eventual: `N_n^{19/20} ≥ (x Im m₀)⁻¹`), `hell`, the primitive family `Kt` of `gueK_existsBA` with its three clauses, and `hP` by `gueGrid_pathBoundsBA`); the
`G`-loop outputs `hLK`, `hLoc`, `hB` (the conjuncts of `BAMO`, V3's pin) stay hypotheses. -/
example (hLK : STLKgL (baFM S0 (fun _ => g0) (fun _ => E0)) (Sizes.seqP (S0.withLam 0)) t1S)
    (hLoc : STLocalEntrygL (baFM S0 (fun _ => g0) (fun _ => E0)) (Sizes.seqP (S0.withLam 0)) t1S)
    (hB : STExp2gL (baFM S0 (fun _ => g0) (fun _ => E0)) (Sizes.seqP (S0.withLam 0)) t1S) :
    Eq729BA_Concl S0 (fun _ => g0) (fun _ => E0) t1S t0S (fun _ => (fp 4 hg).m0) (gueGridK S0 4) := by
  have hr : ∀ n, BAReal 3 (S0.L n) g0 (fp 4 hg).m0.im E0 (fp 4 hg).m0 := fun n => (fp 4 hg).real
  have hκ : 0 < (fp 4 hg).m0.im := (fp 4 hg).real.1.1
  have hN : Tendsto (fun n => Nsz S0 n) atTop atTop := S0_adm.2.2.1
  have hlam : ∀ᶠ _n : ℕ in atTop, 0 < g0 ∧ g0 ≤ (1 / 10 : ℝ)⁻¹ :=
    Eventually.of_forall fun _ => ⟨g0_pos, by have := g0_le; norm_num; linarith⟩
  have hscale : ∀ᶠ n in atTop, (Nsz S0 n * etaOf (fp 4 hg).m0 (t0S n))⁻¹ ≤ Nsz S0 n ^ (-(1 / 20 : ℝ)) := by
    have := GUEHyp_scale_ev hN (mul_pos xI_pos hκ) (by norm_num : (1 / 20 : ℝ) < 1)
    filter_upwards [this] with n h
    rwa [etaOf_S]
  have h730 : ∀ᶠ n in atTop, t0S n - t1S n ≤ Nsz S0 n ^ (-(1 / 20 : ℝ)) * etaOf (fp 4 hg).m0 (t0S n) := by
    filter_upwards [GUEHyp_scale_ev hN hκ (by norm_num : (1 / 20 : ℝ) < 1)] with n h
    have hN1 := Nsz_S0_one n
    rw [etaOf_S]
    have h1 : t0S n - t1S n = xI / (2 * Nsz S0 n) := by unfold t0S t1S; ring
    rw [h1]
    have h2 : xI / (2 * Nsz S0 n) ≤ xI * (Nsz S0 n * (fp 4 hg).m0.im)⁻¹ * (fp 4 hg).m0.im := by
      have : xI * (Nsz S0 n * (fp 4 hg).m0.im)⁻¹ * (fp 4 hg).m0.im = xI / Nsz S0 n := by field_simp
      rw [this]
      exact div_le_div_of_nonneg_left xI_pos.le (by linarith) (by linarith)
    calc xI / (2 * Nsz S0 n) ≤ xI * (Nsz S0 n * (fp 4 hg).m0.im)⁻¹ * (fp 4 hg).m0.im := h2
      _ ≤ xI * Nsz S0 n ^ (-(1 / 20 : ℝ)) * (fp 4 hg).m0.im := by gcongr; exact xI_pos.le
      _ = Nsz S0 n ^ (-(1 / 20 : ℝ)) * (xI * (fp 4 hg).m0.im) := by ring
  have hell : ∀ n, ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - t1S n) ≤ S0.lam n ^ 2 := fun n => by
    change (((4 : ℕ) : ℝ)) ^ 3 * (1 - t1S n) ≤ g0 ^ 2
    have := (t1S_bounds n).2.2.2; norm_num; linarith
  have hellg : ∀ n, ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - t1S n) ≤ 2 * g0 ^ 2 := fun n =>
    (hell n).trans (show g0 ^ 2 ≤ 2 * g0 ^ 2 by nlinarith [sq_nonneg g0])
  have hell1 : ∀ n, ((S0.L n : ℕ) : ℝ) ^ 3 * (1 - t1S n) ≤ 1 := fun n =>
    (hell n).trans (show g0 ^ 2 ≤ 1 by have := g0sq_le; linarith)
  have hex : ∀ n, ∃ Kt : ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ,
      (∀ I, Kt (t1S n) I = BAKsol 3 (S0.L n) (S0.W n)
        (BAMsigma 3 (S0.L n) (BAMB 3 (S0.L n) g0 (E0 : ℂ) (fp 4 hg).m0)) (PropSpin (fp 4 hg).m0) (t1S n) I) ∧
      (∀ t ∈ Set.Icc (t1S n) (t0S n), ∀ I : LoopIdx (Zd 3 (S0.L n)), I.WF → 1 ≤ I.length → I.length ≤ 4 * 4 →
        HasDerivWithinAt (fun s => Kt s I) (primRhsGUE 3 (S0.L n) (S0.W n) (Kt t) I) (Set.Icc (t1S n) (t0S n)) t) ∧
      (∀ t ∈ Set.Icc (t1S n) (t0S n), ∀ σ₁ σ₂ : Bool, ∀ a b : Zd 3 (S0.L n),
        Kt t ⟨[σ₁, σ₂], [a, b]⟩ = kTwoGUEBA 3 (S0.L n) (S0.W n) g0 E0 (fp 4 hg).m0 (t1S n) t σ₁ σ₂ a b) := fun n =>
    gueK_existsBA 3 (S0.L n) (S0.W n) (S0.three_le_L n) g0_pos hκ (hr n) (t1S_bounds n).1 (t1S_bounds n).2.1
      (t1S_bounds n).2.2.1 (4 * 4)
  choose Kt hKinit hK hK2 using hex
  have hP := gueGrid_pathBoundsBA S0 le_rfl (𝔠 := 1 / 6) (𝔡 := 1 / 10) (κ := (fp 4 hg).m0.im) (τU := 1 / 20) S0_adm hκ
    (by norm_num) (g := fun _ => g0) (E := fun _ => E0) (t1 := t1S) (t0 := t0S) (m := fun _ => (fp 4 hg).m0) hr hlam
    (fun n => (t1S_bounds n).1) (fun n => (t1S_bounds n).2.1) (fun n => (t1S_bounds n).2.2.1) h730 hscale
    (Eventually.of_forall hell) (Eventually.of_forall hell1) (Eventually.of_forall hellg) Kt (fun n _ => hKinit n)
    (fun n _ t ht => hK n t ht) hLK hLoc
  exact gueGrid_eq729BA le_rfl S0 hκ (by norm_num : (0 : ℝ) < (1 / 10 : ℝ)⁻¹) (by norm_num : (0 : ℝ) < 1 / 20) 4 le_rfl
    (g := fun _ => g0) (E := fun _ => E0) (t1 := t1S) (t0 := t0S) (m := fun _ => (fp 4 hg).m0)
    (Sizes.tendsto_size S0 S0_adm.2.2.1) hr hlam (fun n => (t1S_bounds n).1) (fun n => (t1S_bounds n).2.1)
    (fun n => (t1S_bounds n).2.2.1) h730 hscale (Eventually.of_forall hellg) Kt (fun n _ => hKinit n) (fun n _ t ht => hK n t ht)
    (fun n _ t ht => hK2 n t ht) hB hP

/-- **`Eq729B_eq747_of_eq729BA` at `S0`** (the QUE data above): `H729` is `gueGrid_eq729BA` at the flow datum of `z_n` (`hr`, `hlam` from `ba_flowG`, `h730`, `hscale`, `hell` from
`Eq729B_derivedBA`, the family `Kt` of `BAKFam`), with the pins `hB` (third conjunct of `BAMO`) and the path bounds `hP` (`BAPB`) as hypotheses. -/
example (hMO : BAMO 3 S0 zQ (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))) :
    ∃ Kt : ∀ n, ℝ → LoopIdx (Zd 3 (S0.L n)) → ℂ,
      BAKFam 3 S0 (fun n => BAfE 3 S0 n (zQ n)) (fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n))
        (fun n => BAfT 3 S0 n (zQ n)) Kt ∧
      (GUEPathBoundsBA S0 (Eq729BA_g S0 zQ) (Eq729BA_E S0 zQ) (Eq729BA_t1 S0 tQ zQ) (Eq729BA_t0 S0 zQ) (Eq729BA_m S0 zQ)
        (gueGridK S0 4) 4 Kt →
        ∀ᶠ n in atTop, RandomLayerB_QueAt (UNKind.ba 3) (UNOUProfile.ba 3) S0 (1 / 10) n E0 (tQ n) (1 / 100)) := by
  obtain ⟨Kt, hKF⟩ := GUEHyp_KFam_exists S0 flowS0_spec.1 (E' := fun n => BAfE 3 S0 n (zQ n))
    (t1 := fun n => (1 - ouZeta (tQ n)) * BAfT 3 S0 n (zQ n)) (t0 := fun n => BAfT 3 S0 n (zQ n))
    (fun n => GUELLBA_EdReal 3 κI S0 n (zQ n) (hgoodQ n).1) (fun n => (hgoodQ n).2.1) (fun n => (hgoodQ n).2.2.1)
    (fun n => (hgoodQ n).2.2.2)
  refine ⟨Kt, hKF, fun hP => ?_⟩
  obtain ⟨h730, hscale, hell, hhalf⟩ := Eq729B_derivedBA S0 S0_adm (clsκ_pos 4 hg) tauU_pos le_rfl (E := fun _ => E0) (t := tQ)
    (fun _ => cls_bulk 4 (by norm_num) hg) tQ_ok zQ_ev
  have hlam : ∀ᶠ n in atTop, 0 < Eq729BA_g S0 zQ n ∧ Eq729BA_g S0 zQ n ≤ (1 / 10 : ℝ)⁻¹ := by
    filter_upwards [hhalf] with n hh
    refine ⟨mul_pos (Real.sqrt_pos.2 (by linarith)) g0_pos, ?_⟩
    calc Real.sqrt (Eq729BA_t0 S0 zQ n) * S0.lam n ≤ 1 * S0.lam n :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr (hgoodQ n).2.2.2.le) g0_pos.le
      _ ≤ (1 / 10 : ℝ)⁻¹ := by have := g0_le; change 1 * g0 ≤ _; norm_num; linarith
  exact Eq729B_eq747_of_eq729BA S0 le_rfl S0_adm (clsκ_pos 4 hg) (E := fun _ => E0) (t := tQ) (fun _ => cls_bulk 4 (by norm_num) hg)
    (fun n => (tQ_ok n).1) zQ_ev (gueGridK_ne_zero S0 4)
    (gueGrid_eq729BA le_rfl S0 flowS0_spec.1 (by norm_num : (0 : ℝ) < (1 / 10 : ℝ)⁻¹) tauU_pos 4 le_rfl
      (Sizes.tendsto_size S0 S0_adm.2.2.1) (fun n => GUELLBA_EdReal 3 κI S0 n (zQ n) (hgoodQ n).1) hlam (fun n => (hgoodQ n).2.1)
      (fun n => (hgoodQ n).2.2.1) (fun n => (hgoodQ n).2.2.2) h730 hscale hell Kt hKF.1 hKF.2.1 hKF.2.2 hMO.2.2 hP) (1 / 100) (by norm_num)

/-- **`g1Rowk_of_inputsG` at the BA kind with the producers of this row** (target 17): the three C5 inputs `RBG_Prod`, `RandomLayerB_LL`, `RBG_Que` are `ba_prodG`, `ba_LLG`,
`ba_QueG`; `RBG_Flow`, `RBG_Dom` are `ba_flowG`, `ba_domG` (C5g), `RBG_Comp` is `RandomLayerBGBA_comp` with `baProfComp` (C3), T5 is `ba_mlout`.  `UNMLOutBA` (V3), `UNLocAvgBA`,
`UNQueBA` stay hypotheses (as in `RandomLayerBGBA`, whose last example has the three producers as hypotheses).  `d = 3`, `S0`, `(𝔠, 𝔡) = (1/6, 1/10)`, `τ_U = ouTauMax (1/6) (1/10)`. -/
example (hML : ∀ d : ℕ, UNMLOutBA d) (hLoc : UNLocAvgBA) (hQ : UNQueBA) :
    UNOULLk (UNKind.ba 3) S0 (ouTauMax (1 / 6) (1 / 10)) ∧
      UNOUEq747k (UNKind.ba 3) (UNOUProfile.ba 3) S0 (1 / 10) (ouTauMax (1 / 6) (1 / 10)) :=
  g1Rowk_of_inputsG (fun d => UNKind.ba d) (fun d => UNOUProfile.ba d) (∀ d : ℕ, UNMLOutBA d) UNLocAvgBA UNQueBA BAEd BAfE BAfT
    (fun _ sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) BAMO (fun d => BAKFam d) (fun d => BAPB d) (fun d _ => ba_flowG d)
    (fun d _ => ba_domG d) (fun d _ => RandomLayerBGBA_comp d (baProfComp d)) ba_prodG ba_LLG ba_QueG
    (fun hML' d hd => ba_mlout d hd (hML' d)) hML hLoc hQ 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm _ tauU_pos le_rfl

end GUEHypInst

/-! ## 13. `Eq729B_perNBA` at the flow datum of `sz0` (the data of the instance of `eq729_one_stepBA`, `BA/GUEEq729BA` §6)

`n = 0`, `t₁ = 17/20`, `t₀ = 9/10`, `K = 131072` (`N Δ = 4/5`), `ρ = 1`, `Λ = (N η(t₀))⁻¹`, `B₀ = 200`, the family `Eq729AInst_Kt`; `B = univ`, `p = 1` (`hB`, `hg1`-`hg3` hold
trivially), the one-loop input `hX` (row a's `gueGrid_expect_oneLoopBA'`) stays a hypothesis. -/

namespace GUEHypPerNInst

open RBM.Gauss.SizesInst RBM.BA.FlowPinsInst

open private gI EI mI t1I t0I KI im_pos norm_le ΛI Λ_le_one Λ_ge hBk_inst size0 from RBM3D.BA.GUEEq729BA
open private Eq729AInst_Kt Eq729AInst_hKb Eq729AInst_hKd Eq729AInst_Kt_three from RBM3D.Universality.GUEPhase.Eq729A

/-- **`Eq729B_perNBA` at `sz0`, `n = 0`**: every deterministic hypothesis is discharged. -/
example (hX : ∀ k < KI 0, ∀ a, ‖(∫ ω, eq729FBA sz0 gI t1I t0I EI mI KI 0 k ω ⟨[true], [a]⟩ ∂(Pgue (sz0.withLam 0))) - mI 0‖ ≤
      1 * ΛI ^ 2) (s1 s2 : Bool) (a1 a2 : Zd 3 (sz0.L 0)) :
    ‖eq729eBA sz0 gI t1I t0I EI mI KI (fun n => Eq729AInst_Kt (sz0.L n)) 0 (KI 0) ⟨[s1, s2], [a1, a2]⟩‖ ≤
      Real.exp ((t0I 0 - t1I 0) * (2 * ((sz0.size 0 : ℕ) : ℝ) * (1 * ΛI))) *
        (200 + (KI 0 : ℝ) * eq729c ((sz0.size 0 : ℕ) : ℝ) 1 ΛI 1 (gridStep t1I t0I KI 0)) :=
  Eq729B_perNBA sz0 KI (fun n => Eq729AInst_Kt (sz0.L n)) (g := gI) (E := EI) (t1 := t1I) (t0 := t0I) (m := mI) (n := 0) im_pos
    norm_le (by norm_num) (by norm_num) (by norm_num) (by norm_num) (Λ := ΛI) (ρ := 1) (p := 1) (B0 := 200) rfl Λ_le_one
    zero_le_one (by linarith [Λ_le_one]) zero_le_one (by rw [size0]; unfold gridStep; norm_num)
    (Eq729AInst_hKb (by linarith [Λ_ge]))
    (fun s _ s1 s2 s3 x y w => by rw [Eq729AInst_Kt_three, norm_zero]; positivity) Eq729AInst_hKd hX (B := Set.univ)
    (by simp) (fun _ h => absurd (Set.mem_univ _) h) (fun _ h => absurd (Set.mem_univ _) h)
    (fun _ h => absurd (Set.mem_univ _) h) (fun s1 s2 x y => hBk_inst s1 s2 x y) s1 s2 a1 a2

end GUEHypPerNInst

end RBM.BA

end
