/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MAPins
import RBM3D.BA.MReg
import RBM3D.Main.BUnivHolds
import RBM3D.Universality.PinsC2

/-!
# M/N M1, row b (T2514b): the tracial local laws of block Anderson (`BA/MATrLocalBA`)

Ticket T2514 (dispatcher V4, DECISIONS §337; supervisor `2026-10-15-0643` MNO-C3), row b.  The two
merged BA rows `UNTrLocalBARow`, `UNTrLocalInitBARow'` (`BA/UNPins.lean:169, 181`) are proved from
the per-`d` reading `UNLocAvgBAAt d` of `BA/MAPins` (P4), through per-`d` cores.

* B1 (private) the window uniformisation: `∀ x, |x - E| ≤ δ → ∀ᶠ n, BAbulk (κ/2) x` gives
  `∀ᶠ n, ∀ x, |x - E| ≤ δ → BAbulk (κ/4) x` (a finite cover of `[E - δ, E + δ]` by balls of radius
  `(π κ/2)³/8`, `BAbulk_window`).
* B2 `unTrLocalBAAt_of_locAvg`: `UNLocAvgBAAt d → UNTrLocalBAAt d`: the trace is the mean of the
  block averages (`BUniv_trace_le`, merged private, by `open private`).  B3 `unTrLocalBARow_holds`:
  one line from B2 and P6.
* B4 `unTrLocalInitBAAt'_of_locAvg`: `UNLocAvgBAAt d → UNTrLocalInitBAAt' d`.  The initial matrix is
  `ouInit = e^{-t*/2} H_{λ̂}` (`ouInit_ba`), `λ̂ = λ e^{t*/2}` (`lamHat`), admissible at `(𝔠, 𝔡/2)`
  (`admissible_lamHat`); the model at `λ̂` carries `UNLocAvgBAAt` at the bulk level `κ/16`, and the
  tolerance `W^τ (Bctl + t*)` absorbs the shift of `m`.  The exact scaling identity of `(self_m)`
  (`BASelf g₀ z m ⇒ BASelf (g₀/a) (z/a + a⁻¹ (1 - a²) m) (a m)`, the complex-`z` form of the merged
  real-`E` `BAzztE_inv_core`) replaces a coupling-Lipschitz bound; the bulk at `λ̂` comes from a
  complex-base twin of `BAbulk_window` (`MATrLocalBA_cplx_real`).  B5 `unTrLocalInitBARow'_holds`:
  one line from B4 and P6.

No new public definition; the instances (B6) are `example`s at `S0` (`d = 3`).  `UNLocAvgBAAt 3` and
`UNLocAvgBA` are pins of T2514 row a (A8, A7) and stay hypotheses of the instances.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter Topology

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

open private BUniv_trace_le from RBM3D.Main.BUnivHolds

/-! ## B1: the uniformisation of the window -/

/-- **B1** (private): the `κ/2`-bulk at every point of the window, eventually in `n` at each point, becomes the `κ/4`-bulk at every
point of the window, eventually in `n`: a finite cover of `[E - δ, E + δ]` by balls of radius `r = (π (κ/2))³/8` and
`BAbulk_window` at each centre. -/
private theorem MATrLocalBA_unif (d : ℕ) (sz : Sizes d) (κ E δ : ℝ) (hκ : 0 < κ)
    (hwin : ∀ x : ℝ, |x - E| ≤ δ → ∀ᶠ n in atTop, BAbulk d (sz.L n) (sz.lam n) (κ / 2) x) :
    ∀ᶠ n in atTop, ∀ x : ℝ, |x - E| ≤ δ → BAbulk d (sz.L n) (sz.lam n) (κ / 4) x := by
  have hr : 0 < (Real.pi * (κ / 2)) ^ 3 / 8 := by positivity
  obtain ⟨t, ht, htf, hcov⟩ := (isCompact_Icc (a := E - δ) (b := E + δ)).finite_cover_balls hr
  have hev : ∀ᶠ n in atTop, ∀ c ∈ t, BAbulk d (sz.L n) (sz.lam n) (κ / 2) c :=
    (htf.eventually_all).2 fun c hc => hwin c (abs_le.2 ⟨by linarith [(ht hc).1], by linarith [(ht hc).2]⟩)
  filter_upwards [hev] with n hn x hx
  have hxI : x ∈ Set.Icc (E - δ) (E + δ) := ⟨by linarith [(abs_le.1 hx).1], by linarith [(abs_le.1 hx).2]⟩
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcov hxI)
  have hdist : |x - c| ≤ (Real.pi * (κ / 2)) ^ 3 / 8 := by
    have := Metric.mem_ball.1 hxc
    rw [Real.dist_eq] at this
    exact this.le
  have h := BAbulk_window d (sz.L n) (sz.lam n) (κ / 2) c x (half_pos hκ) (hn c hc) hdist
  have e : κ / 2 / 2 = κ / 4 := by ring
  rwa [e] at h

/-! ## B2, B3: the tracial local law -/

/-- **B2 `unTrLocalBAAt_of_locAvg`** (twin of `unTrLocalBandRow`, `Main/BUnivHolds.lean:205`, with B1): the trace is the mean of the
block averages (`BUniv_trace_le`), so a trace deviation above `W^τ Bctl` forces a block deviation above `W^τ Bctl`; the window
points are in the `κ/4`-bulk by B1, and `UNLocAvgBAAt d` is applied at `κ/4`. -/
theorem unTrLocalBAAt_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalBAAt d := by
  intro d hd hLoc 𝔠 𝔡 sz hA κ hκ E hE δ hδ hwin ε τ D hε hτ hD
  filter_upwards [hLoc 𝔠 𝔡 sz hA (κ / 4) ε τ D (by positivity) hε hτ hD, MATrLocalBA_unif d sz κ E δ hκ hwin] with n hn hU
  refine le_trans (measure_mono ?_) hn
  rintro ω ⟨z, hz1, hz2, hz3, hz4⟩
  refine ⟨z, ⟨hU z.re hz1, hz2, hz3⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  have hle := BUniv_trace_le d (sz.L n) (sz.W n) (Gres ((UNModelC.ba sz).H n ω) z true) (BAm d (sz.L n) (sz.lam n) z) hcon
  exact absurd hle (not_le.2 hz4)

/-- **B3 `unTrLocalBARow_holds`**: the merged row `UNTrLocalBARow` (`BA/UNPins.lean:169`), one line from B2 and P6. -/
theorem unTrLocalBARow_holds : UNTrLocalBARow :=
  UNTrLocalBARow_iff_at.2 fun hLoc d hd => unTrLocalBAAt_of_locAvg d hd (UNLocAvgBA_iff_at.1 hLoc d hd)

/-! ## B4 (private tools): the scaling identity, the bulk at `λ̂`, the comparison of `Bctl` -/

/-- **The scaling identity of `(self_m)` at a complex point** (the complex-`z` form of the merged real-`E` `BAzztE_inv_core`,
`BA/CouplingWindow.lean:239`; the same algebra): `(g₀ Ψ - z - m) = a (g Ψ - ζ - a m)` with `g₀ = a g`,
`ζ = a⁻¹ z + a⁻¹ (1 - a²) m`, so `m` solves `(self_m)` at `(g₀, z)` iff `a m` does at `(g, ζ)`. -/
private theorem MATrLocalBA_scale (d L : ℕ) [NeZero L] (g g₀ a : ℝ) (z m : ℂ) (ha : 0 < a) (hg : a * g = g₀)
    (hz : 0 ≤ z.im) (h : BASelf d L g₀ z m) :
    BASelf d L g (((a : ℝ) : ℂ)⁻¹ * z + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * m) ((a : ℂ) * m) := by
  subst hg
  obtain ⟨hb, hmeq⟩ := h
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  set z' : ℂ := ((a : ℝ) : ℂ)⁻¹ * z + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * m with hz'
  have hkey : z' + (a : ℂ) * m = (z + m) / (a : ℂ) := by
    simp only [hz']; push_cast; field_simp; ring
  set A₀ : Matrix (Zd d L) (Zd d L) ℂ := (((a * g : ℝ) : ℂ)) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) with hA₀
  have hne : (z + m).im ≠ 0 := by
    simp only [Complex.add_im]; linarith
  have hA₀det : IsUnit A₀.det := by
    have := isUnit_sub_smul_of_isHermitian (BAPsi_isHermitian d L (a * g)) hne
    rw [Matrix.isUnit_iff_isUnit_det] at this
    exact this
  have hmat : (g : ℂ) • PsiB d L - (z' + (a : ℂ) * m) • (1 : Matrix (Zd d L) (Zd d L) ℂ) = ((a : ℂ)⁻¹) • A₀ := by
    rw [hkey, hA₀, smul_sub, smul_smul, smul_smul, Complex.ofReal_mul]
    congr 1
    · congr 1; field_simp
    · congr 1; field_simp
  have hMB : BAMB d L g z' ((a : ℂ) * m) = (a : ℂ) • BAMB d L (a * g) z m := by
    unfold BAMB Mres
    rw [hmat, ← Matrix.nonsing_inv_eq_ringInverse, ← Matrix.nonsing_inv_eq_ringInverse]
    have hinv : Invertible ((a : ℂ)⁻¹) := invertibleOfNonzero (inv_ne_zero hac)
    rw [Matrix.inv_smul A₀ ((a : ℂ)⁻¹) hA₀det, invOf_eq_inv, inv_inv]
  refine ⟨?_, ?_⟩
  · simp only [Complex.im_ofReal_mul]; exact mul_pos ha hb
  · rw [hMB, Matrix.trace_smul, smul_eq_mul]
    calc (a : ℂ) * m = (a : ℂ) * ((((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L (a * g) z m).trace) := by rw [← hmeq]
      _ = _ := by ring

/-- **Complex base point to the real axis** (twin of `MReg_key` and `BAbulk_window`, `BA/MReg.lean:97, 122`, with a complex base
solution): a solution `m` at `w` (`Im w ≥ 0`) with `Im m ≥ c` and `‖w - y‖ ≤ c³/16` gives a real-axis solution at `y` with
`Im ≥ c/2`: `c² ‖m - m(y + iη)‖ ≤ 2 ‖w - (y + iη)‖ ≤ c³/4` for `0 < η ≤ c³/16`, so `Im m(y + iη) ≥ 3c/4`, and a subsequence
`η_k ↓ 0` converges (`BASelf_of_tendsto`). -/
private theorem MATrLocalBA_cplx_real (d L : ℕ) [NeZero L] (g c : ℝ) (w m : ℂ) (y : ℝ) (hc : 0 < c)
    (hw : 0 ≤ w.im) (hs : BASelf d L g w m) (hm : c ≤ m.im) (hwy : ‖w - (y : ℂ)‖ ≤ c ^ 3 / 16) :
    BAbulk d L g (c / (2 * Real.pi)) y := by
  have hc3 : 0 < c ^ 3 / 16 := by positivity
  have key : ∀ η : ℝ, 0 < η → η ≤ c ^ 3 / 16 →
      c / 2 ≤ (BAm d L g ((y : ℂ) + (η : ℂ) * Complex.I)).im := by
    intro η hη hη'
    have hz' : 0 < ((y : ℂ) + (η : ℂ) * Complex.I).im := by simp [hη]
    have hs' := BAm_self d L g _ hz'
    have h1 := BASelf_sub_le d L g w _ m _ hw hz'.le hs hs'
    set m' := BAm d L g ((y : ℂ) + (η : ℂ) * Complex.I) with hm'
    have h2 : ‖w - ((y : ℂ) + (η : ℂ) * Complex.I)‖ ≤ c ^ 3 / 8 := by
      have e : w - ((y : ℂ) + (η : ℂ) * Complex.I) = (w - (y : ℂ)) - (η : ℂ) * Complex.I := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
      linarith
    have h3 : c ^ 2 * ‖m - m'‖ ≤ c ^ 3 / 4 := by
      have h4 : c ^ 2 ≤ m.im ^ 2 + m'.im ^ 2 := by nlinarith [sq_nonneg m'.im]
      have h5 := mul_le_mul_of_nonneg_right h4 (norm_nonneg (m - m'))
      nlinarith
    have h4 : ‖m - m'‖ ≤ c / 4 := by
      by_contra hcon
      have hcon := not_le.mp hcon
      have h5 : c ^ 2 * (c / 4) < c ^ 2 * ‖m - m'‖ := mul_lt_mul_of_pos_left hcon (by positivity)
      nlinarith
    have h5 : (m - m').im ≤ ‖m - m'‖ := Complex.im_le_norm _
    rw [Complex.sub_im] at h5
    linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℕ → ℝ, η = fun k : ℕ => c ^ 3 / 16 * (1 / ((k : ℝ) + 1)) := ⟨_, rfl⟩
  have hηpos : ∀ k, 0 < η k := fun k => by rw [hηdef]; positivity
  have hηle : ∀ k, η k ≤ c ^ 3 / 16 := fun k => by
    rw [hηdef]
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simpa using mul_le_mul_of_nonneg_left h1 hc3.le
  have hη0 : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c ^ 3 / 16)
    rw [hηdef]
    simpa using this
  obtain ⟨zs, hzsdef⟩ : ∃ zs : ℕ → ℂ, zs = fun k : ℕ => (y : ℂ) + (η k : ℂ) * Complex.I := ⟨_, rfl⟩
  have hzim : ∀ k, 0 < (zs k).im := fun k => by rw [hzsdef]; simp [hηpos k]
  have hself : ∀ k, BASelf d L g (zs k) (BAm d L g (zs k)) := fun k => BAm_self d L g _ (hzim k)
  have hbd : ∀ k, BAm d L g (zs k) ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro k
    rw [mem_closedBall_zero_iff]
    exact BAm_norm_le_one d L g _ _ (hzim k).le (hself k)
  obtain ⟨m₁, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall) hbd
  have hmim : c / 2 ≤ m₁.im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto m₁).comp hlim)
      (Eventually.of_forall fun k => by
        have := key (η (φ k)) (hηpos _) (hηle _)
        simpa [hzsdef] using this)
  have hzs : Tendsto (fun k => zs (φ k)) atTop (𝓝 (y : ℂ)) := by
    have h1 : Continuous (fun t : ℝ => (y : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have := (h1.tendsto 0).comp (hη0.comp hφ.tendsto_atTop)
    simpa [hzsdef, Function.comp_def] using this
  have hs1 : BASelf d L g (y : ℂ) m₁ :=
    BASelf_of_tendsto d L g (y : ℂ) m₁ _ _ hzs hlim (fun k => (hzim _).le) (fun k => hself _) (by linarith)
  refine (BAbulk_iff_exists d L g (c / (2 * Real.pi)) y (by positivity)).mpr ⟨m₁, hs1, ?_⟩
  have e : Real.pi * (c / (2 * Real.pi)) = c / 2 := by field_simp
  rw [e]; exact hmim

/-- `Bctl` at a larger coupling and a larger height is smaller (`PinsC2_Bctl_anti` with the coupling: `λ² ≤ λ̂²`,
`Bparam d L g t 0 = (g² + |1 - t|)⁻¹ + (L^d |1 - t|)⁻¹`). -/
private theorem MATrLocalBA_Bctl_le {d : ℕ} (sz : Sizes d) (g : ℕ → ℝ) (n : ℕ) {η η' : ℝ} (hη : 0 < η) (hηη' : η ≤ η')
    (hg : sz.lam n ^ 2 ≤ g n ^ 2) : (sz.withLam g).Bctl n (1 - η') ≤ sz.Bctl n (1 - η) := by
  unfold Sizes.Bctl Bparam
  have hxu : 0 < 1 - (1 - η) := by linarith
  have hxs : 0 < 1 - (1 - η') := by linarith
  rw [abs_of_pos hxu, abs_of_pos hxs]
  have hL : (0 : ℝ) < ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 0 < sz.L n)
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hg0 : (0 : ℝ) ≤ sz.lam n ^ 2 := sq_nonneg _
  have h1 : (g n ^ 2 + (1 - (1 - η')))⁻¹ ≤ (sz.lam n ^ 2 + (1 - (1 - η)))⁻¹ :=
    inv_anti₀ (by linarith) (by linarith)
  have h2 : (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η')))⁻¹ ≤ (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η)))⁻¹ :=
    inv_anti₀ (by positivity) (by gcongr)
  have hK : 0 ≤ ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ := by positivity
  change (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((g n ^ 2 + (1 - (1 - η')))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ +
      (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η')))⁻¹) ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
      ((sz.lam n ^ 2 + (1 - (1 - η)))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + (((sz.L n : ℕ) : ℝ) ^ d * (1 - (1 - η)))⁻¹)
  gcongr

/-! ## B4, B5: the initial-data local law -/

open private PinsC2_one_le_Nsz PinsC2_rpow_ev PinsC2_W_tendsto PinsC2_inv_le PinsC2_one_le_inv PinsC2_exp_le_one
  PinsC2_inv_mul_re PinsC2_inv_mul_im PinsC2_Bctl_nonneg PinsC2_aux1 PinsC2_aux2 PinsC2_stieltjesN_smul
  PinsC2_norm_re_zero from RBM3D.Universality.PinsC2

set_option maxHeartbeats 1000000 in
-- the rescaling argument has many `set` abbreviations and `linarith` calls in one proof
/-- **B4 `unTrLocalInitBAAt'_of_locAvg`** (twin of `unTrLocalInit'_of_unTrLocal`, `Universality/PinsC2.lean:590`, with `m` replaced by
the BA datum `m(·, λ_n)` and the coupling moved to `λ̂ = λ e^{t*/2}`).  `ouInit = a H_{λ̂}` (`ouInit_ba`), `a = e^{-t*/2}`, so
`stieltjesN ouInit z = a⁻¹ stieltjesN H_{λ̂} (a⁻¹ z)`.  At `ζ = a⁻¹ z` (`ẑ = ⟨Re ζ, min (Im ζ) 1⟩`): the bulk at `λ̂` and level `κ/16` at
`Re ζ` comes from the real solution `m_x` at `x = Re z` (B1: `κ/4`-bulk) by the scaling identity and `MATrLocalBA_cplx_real`;
`UNLocAvgBAAt d` at `sz.withLam λ̂` (admissible at `(𝔠, 𝔡/2)`) and `τ/2` bounds `stieltjesN H_{λ̂} ẑ - m(ẑ, λ̂)` by `W^{τ/2} Bctl`
(`BUniv_trace_le`, `Bctl_{λ̂} ≤ Bctl_λ`); the vertical bridge costs `T`; and `a m(z)` solves `(self_m)` at `(λ̂, ζ + a⁻¹ (1 - a²) m(z))`,
so `‖m(ẑ, λ̂) - a m(z)‖ ≤ 24 T / c₀²` (`BASelf_sub_le` with `Im (a m(z)) ≥ c₀/2`, `c₀ = (π κ/4)⁵/2048`). -/
theorem unTrLocalInitBAAt'_of_locAvg : ∀ d : ℕ, 3 ≤ d → UNLocAvgBAAt d → UNTrLocalInitBAAt' d := by
  intro d hd hLoc 𝔠 𝔡 sz hA κ hκ E hE δ hδ hwin τs hτs0 hτs1 ε τ D hε hτ hD
  have hκ₂ : 0 < κ / 4 := by positivity
  set c : ℝ := Real.pi * (κ / 4) with hcdef
  have hc0 : 0 < c := by positivity
  set c₁ : ℝ := c / 2 with hc₁def
  have hc₁0 : 0 < c₁ := by positivity
  set κt : ℝ := κ / 16 with hκtdef
  have hκt0 : 0 < κt := by positivity
  set c₀ : ℝ := c ^ 5 / 2048 with hc₀def
  have hc₀0 : 0 < c₀ := by positivity
  set Cb : ℝ := 2 + 48 / c₀ ^ 2 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  have hκeq : c₁ / (2 * Real.pi) = κt := by
    simp only [hc₁def, hcdef, hκtdef]; field_simp; ring
  have hN1' : ∀ n, (1 : ℝ) ≤ Nsz sz n := PinsC2_one_le_Nsz sz
  have hT0 : ∀ n, 0 ≤ ouTStar sz τs n := fun n => Real.rpow_nonneg (by linarith [hN1' n]) _
  have hT1 : ∀ n, ouTStar sz τs n ≤ 1 := fun n =>
    Real.rpow_le_one_of_one_le_of_nonpos (hN1' n) (by linarith)
  have hA' := admissible_lamHat hA (ouTStar sz τs) hT0 hT1
  have hP := hLoc 𝔠 (𝔡 / 2) _ hA' κt ε (τ / 2) D hκt0 hε (by positivity) hD
  have hU := MATrLocalBA_unif d sz κ E δ hκ hwin
  have hW := PinsC2_W_tendsto hA
  have hNtend : Tendsto (fun n => Nsz sz n) atTop atTop := hA.2.2.1
  filter_upwards [hP, hU,
    hNtend.eventually (PinsC2_rpow_ev (e := -1 + τs) (c := c₁ ^ 3 / 32) (by linarith) (by positivity)),
    ((tendsto_rpow_atTop (by positivity : 0 < τ / 2)).comp hW).eventually_ge_atTop (max 2 Cb)] with n hPn hUn hTn hXn
  have hN0 : (0 : ℝ) < Nsz sz n := by linarith [hN1' n]
  set T : ℝ := ouTStar sz τs n with hTdef
  have hTpos : 0 < T := Real.rpow_pos_of_pos hN0 _
  have hT1n : T ≤ 1 := hT1 n
  have hTc : T ≤ c₁ ^ 3 / 32 := hTn
  set X : ℝ := ((sz.W n : ℕ) : ℝ) ^ (τ / 2) with hXdef
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hXn
  have hXC : Cb ≤ X := (le_max_right _ _).trans hXn
  have hX0 : 0 ≤ X := by linarith
  have hWτ : ((sz.W n : ℕ) : ℝ) ^ τ = X * X := by
    have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
    rw [hXdef, ← Real.rpow_add hW0]; congr 1; ring
  set a : ℝ := Real.exp (-T / 2) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := PinsC2_exp_le_one hTpos.le
  have hainv : a⁻¹ ≤ 1 + T := PinsC2_inv_le hTpos.le hT1n
  have hainv1 : 1 ≤ a⁻¹ := PinsC2_one_le_inv hTpos.le
  have hainv2 : a⁻¹ ≤ 2 := by linarith
  have ha12 : 1 / 2 ≤ a := by
    have := inv_anti₀ (inv_pos.2 ha0) hainv2
    simpa using this
  have hasq : a ^ 2 = Real.exp (-T) := by
    rw [ha, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h1a : 1 - a ^ 2 ≤ T := by
    rw [hasq]; have := Real.add_one_le_exp (-T); linarith
  have h1a0 : 0 ≤ 1 - a ^ 2 := by nlinarith
  set lh : ℝ := lamHat sz (ouTStar sz τs) n with hlh
  have hag : a * lh = sz.lam n := by
    rw [hlh]
    change a * (sz.lam n * Real.exp (T / 2)) = sz.lam n
    calc a * (sz.lam n * Real.exp (T / 2)) = sz.lam n * (Real.exp (-T / 2) * Real.exp (T / 2)) := by rw [ha]; ring
      _ = sz.lam n := by rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero, mul_one]
  have hlam2 : sz.lam n ^ 2 ≤ (lamHat sz (ouTStar sz τs)) n ^ 2 := by
    change sz.lam n ^ 2 ≤ (sz.lam n * Real.exp (T / 2)) ^ 2
    rw [mul_pow]
    exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ (Real.one_le_exp (by linarith)))
  set sz' : Sizes d := sz.withLam (lamHat sz (ouTStar sz τs)) with hsz'
  refine le_trans (measure_mono (μ := (UNModelC.ba sz).μ) ?_) hPn
  rintro ω ⟨z, hz1, hz2, hz3, hz4⟩
  have hzim : 0 < z.im := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 _) hz2
  -- the real solution at `x = Re z` and the scaling to `λ̂`
  have hbulk₂ : BAbulk d (sz.L n) (sz.lam n) (κ / 4) z.re := hUn z.re hz1
  obtain ⟨mx, hmx, hmxc⟩ := (BAbulk_iff_exists d (sz.L n) (sz.lam n) (κ / 4) z.re hκ₂).mp hbulk₂
  have hmx1 : ‖mx‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ _ _ (by simp) hmx
  have hmxim : 0 ≤ mx.im := by linarith
  have hscx := MATrLocalBA_scale d (sz.L n) lh (sz.lam n) a (z.re : ℂ) mx ha0 hag (by simp) hmx
  have ew : ((a : ℝ) : ℂ)⁻¹ * (z.re : ℂ) + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mx =
      ((a⁻¹ * z.re : ℝ) : ℂ) + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mx := by push_cast; ring
  rw [ew] at hscx
  have hrnn : 0 ≤ a⁻¹ * (1 - a ^ 2) := mul_nonneg (by linarith) h1a0
  have hrle : a⁻¹ * (1 - a ^ 2) ≤ 2 * T := mul_le_mul hainv2 h1a (by linarith) (by norm_num)
  have hw0 : 0 ≤ (((a⁻¹ * z.re : ℝ) : ℂ) + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mx).im := by
    rw [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add]
    exact mul_nonneg hrnn hmxim
  have hmc : c₁ ≤ (((a : ℝ) : ℂ) * mx).im := by
    rw [Complex.im_ofReal_mul, hc₁def]
    nlinarith
  have hwy : ‖(((a⁻¹ * z.re : ℝ) : ℂ) + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mx) - ((a⁻¹ * z.re : ℝ) : ℂ)‖ ≤
      c₁ ^ 3 / 16 := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnn]
    nlinarith [norm_nonneg mx]
  have hbulkH : BAbulk d (sz.L n) lh κt (a⁻¹ * z.re) := by
    rw [← hκeq]
    exact MATrLocalBA_cplx_real d (sz.L n) lh c₁ _ _ (a⁻¹ * z.re) hc₁0 hw0 hscx hmc hwy
  -- the points `ζ = a⁻¹ z` and `ẑ`
  set ζ : ℂ := ((a : ℝ) : ℂ)⁻¹ * z with hζ
  have hζre : ζ.re = a⁻¹ * z.re := PinsC2_inv_mul_re a z
  have hζim : ζ.im = a⁻¹ * z.im := PinsC2_inv_mul_im a z
  have hζim_ge : z.im ≤ ζ.im := by rw [hζim]; nlinarith
  have hζim_le : ζ.im ≤ 1 + T := by rw [hζim]; nlinarith
  set zh : ℂ := ⟨ζ.re, min ζ.im 1⟩ with hzh
  have hzh_im : zh.im = min ζ.im 1 := rfl
  have hzh_re : zh.re = ζ.re := rfl
  have hzh_ge : z.im ≤ zh.im := by rw [hzh_im]; exact le_min hζim_ge hz3
  have hzh_le : zh.im ≤ 1 := min_le_right _ _
  have hzh_pos : 0 < zh.im := lt_of_lt_of_le hzim hzh_ge
  have hζpos : 0 < ζ.im := lt_of_lt_of_le hzim hζim_ge
  refine ⟨zh, ⟨?_, hz2.trans hzh_ge, hzh_le⟩, ?_⟩
  · change BAbulk d (sz.L n) lh κt zh.re
    rw [hzh_re, hζre]; exact hbulkH
  by_contra hcon
  push Not at hcon
  -- the trace of the block averages at `ẑ`, at the coupling `λ̂`
  have htr := BUniv_trace_le d (sz.L n) (sz.W n) (Gres ((UNModel.ba sz').H n ω) zh true) (BAm d (sz.L n) lh zh) hcon
  have hBc : sz'.Bctl n (1 - zh.im) ≤ sz.Bctl n (1 - z.im) :=
    MATrLocalBA_Bctl_le sz (lamHat sz (ouTStar sz τs)) n hzim hzh_ge hlam2
  have hB0 : 0 ≤ sz.Bctl n (1 - z.im) := PinsC2_Bctl_nonneg sz n hzim
  have hSz : ‖stieltjesN ((UNModel.ba sz').H n ω) zh - BAm d (sz.L n) lh zh‖ ≤ X * sz.Bctl n (1 - z.im) :=
    htr.trans (mul_le_mul_of_nonneg_left hBc hX0)
  have hH' := (UNModel.ba sz').herm n ω
  -- the vertical bridge from `ζ` to `ẑ`
  have hzh_eq : ζ.im ≤ 1 → zh = ζ := fun hc => Complex.ext rfl (by rw [hzh_im]; exact min_eq_left hc)
  have hzz : ‖ζ - zh‖ ≤ T := by
    by_cases hc : ζ.im ≤ 1
    · rw [hzh_eq hc, sub_self, norm_zero]; exact hTpos.le
    · push Not at hc
      have hz1' : zh.im = 1 := by rw [hzh_im]; exact min_eq_right hc.le
      have : ζ - zh = ((ζ.im - 1 : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hz1', hzh_re]
      rw [this, PinsC2_norm_re_zero, abs_of_pos (by linarith)]
      linarith
  have hbrS : ‖stieltjesN ((UNModel.ba sz').H n ω) ζ - stieltjesN ((UNModel.ba sz').H n ω) zh‖ ≤ T := by
    by_cases hc : ζ.im ≤ 1
    · rw [hzh_eq hc, sub_self, norm_zero]; exact hTpos.le
    · push Not at hc
      have hz1' : zh.im = 1 := by rw [hzh_im]; exact min_eq_right hc.le
      have hζeta : ζ = ⟨ζ.re, ζ.im⟩ := rfl
      have hzheta : zh = ⟨ζ.re, 1⟩ := Complex.ext rfl hz1'
      rw [hzheta]
      have := stieltjesN_vert_le hH' ζ.re ζ.im 1 hζpos one_pos
      rw [← hζeta] at this
      refine this.trans ?_
      rw [mul_one, abs_of_pos (by linarith), div_le_iff₀ hζpos]
      have h1 : ζ.im - 1 ≤ T := by linarith
      have h2 : T ≤ T * ζ.im := le_mul_of_one_le_right hTpos.le hc.le
      linarith
  -- the shift of `m`: `a m(z)` solves `(self_m)` at `(λ̂, ζ + a⁻¹ (1 - a²) m(z))`
  have hmz := BAm_self d (sz.L n) (sz.lam n) z hzim
  set mz : ℂ := BAm d (sz.L n) (sz.lam n) z with hmzdef
  have hmz1 : ‖mz‖ ≤ 1 := BAm_norm_le_one d (sz.L n) _ _ _ hzim.le hmz
  have hmzim : c₀ ≤ mz.im := by
    have := BAm_im_lower_window d (sz.L n) (sz.lam n) (κ / 4) z.re z.re z.im hκ₂ hbulk₂
      (by rw [sub_self, abs_zero]; positivity) hzim (by linarith)
    rwa [Complex.re_add_im] at this
  have hscz := MATrLocalBA_scale d (sz.L n) lh (sz.lam n) a z mz ha0 hag hzim.le hmz
  have hζ''im : 0 ≤ (ζ + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mz).im := by
    rw [Complex.add_im, Complex.im_ofReal_mul]
    exact add_nonneg hζpos.le (mul_nonneg hrnn (by linarith))
  have hsub := BASelf_sub_le d (sz.L n) lh zh _ (BAm d (sz.L n) lh zh) (((a : ℝ) : ℂ) * mz) hzh_pos.le hζ''im
    (BAm_self d (sz.L n) lh zh hzh_pos) hscz
  have hdiff : ‖zh - (ζ + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mz)‖ ≤ 3 * T := by
    have e : zh - (ζ + ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mz) = -(ζ - zh) - ((a⁻¹ * (1 - a ^ 2) : ℝ) : ℂ) * mz := by ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrnn]
    have := mul_le_of_le_one_right hrnn hmz1
    linarith
  have hmtΔ : ‖BAm d (sz.L n) lh zh - ((a : ℝ) : ℂ) * mz‖ ≤ 24 * T / c₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h0 : c₀ / 2 ≤ a * mz.im := by
      have := mul_le_mul ha12 hmzim hc₀0.le ha0.le
      linarith only [this]
    have h3 : (c₀ / 2) ^ 2 ≤ (a * mz.im) ^ 2 := pow_le_pow_left₀ (by positivity) h0 2
    have h1 : c₀ ^ 2 / 4 ≤ (BAm d (sz.L n) lh zh).im ^ 2 + (((a : ℝ) : ℂ) * mz).im ^ 2 := by
      rw [Complex.im_ofReal_mul]
      linarith only [h3, sq_nonneg (BAm d (sz.L n) lh zh).im]
    have h2 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (BAm d (sz.L n) lh zh - ((a : ℝ) : ℂ) * mz))
    linarith only [h2, hsub, hdiff]
  -- assemble
  have hdict : stieltjesN (ouInit (UNModelC.ba sz) n T ω) z =
      ((a : ℝ) : ℂ)⁻¹ * stieltjesN ((UNModel.ba sz').H n ω) ζ := by
    rw [show ouInit (UNModelC.ba sz) n T ω = Real.exp (-T / 2) • (UNModel.ba sz').H n ω from
      ouInit_ba sz (ouTStar sz τs) n ω, ← Complex.coe_smul]
    exact PinsC2_stieltjesN_smul _ (Complex.ofReal_ne_zero.mpr ha0.ne') z
  rw [hdict] at hz4
  have hac : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha0.ne'
  have hainvn : ‖((a : ℝ) : ℂ)⁻¹‖ ≤ 2 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]; exact hainv2
  have hfin : ‖((a : ℝ) : ℂ)⁻¹ * stieltjesN ((UNModel.ba sz').H n ω) ζ - mz‖ ≤
      2 * (X * sz.Bctl n (1 - z.im)) + T * Cb := by
    have hsplit : ((a : ℝ) : ℂ)⁻¹ * stieltjesN ((UNModel.ba sz').H n ω) ζ - mz =
        ((a : ℝ) : ℂ)⁻¹ * (stieltjesN ((UNModel.ba sz').H n ω) ζ - stieltjesN ((UNModel.ba sz').H n ω) zh) +
        ((a : ℝ) : ℂ)⁻¹ * (stieltjesN ((UNModel.ba sz').H n ω) zh - BAm d (sz.L n) lh zh) +
        ((a : ℝ) : ℂ)⁻¹ * (BAm d (sz.L n) lh zh - ((a : ℝ) : ℂ) * mz) := by
      linear_combination mz * (inv_mul_cancel₀ hac)
    rw [hsplit]
    have t1 := mul_le_mul hainvn hbrS (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have t2 := mul_le_mul hainvn hSz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have t3 := mul_le_mul hainvn hmtΔ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    rw [← norm_mul] at t1 t2 t3
    calc _ ≤ ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN ((UNModel.ba sz').H n ω) ζ - stieltjesN ((UNModel.ba sz').H n ω) zh)‖ +
          ‖((a : ℝ) : ℂ)⁻¹ * (stieltjesN ((UNModel.ba sz').H n ω) zh - BAm d (sz.L n) lh zh)‖ +
          ‖((a : ℝ) : ℂ)⁻¹ * (BAm d (sz.L n) lh zh - ((a : ℝ) : ℂ) * mz)‖ := norm_add₃_le
      _ ≤ 2 * T + 2 * (X * sz.Bctl n (1 - z.im)) + 2 * (24 * T / c₀ ^ 2) := by linarith
      _ = 2 * (X * sz.Bctl n (1 - z.im)) + T * Cb := by rw [hCb]; ring
  have hz4' : X * X * (sz.Bctl n (1 - z.im) + T) <
      ‖((a : ℝ) : ℂ)⁻¹ * stieltjesN ((UNModel.ba sz').H n ω) ζ - mz‖ := by rw [← hWτ]; exact hz4
  have hup : 2 * (X * sz.Bctl n (1 - z.im)) + T * Cb ≤ X * X * (sz.Bctl n (1 - z.im) + T) := by
    have h1 := PinsC2_aux1 hX2 hB0
    have h2 := PinsC2_aux2 (by linarith : (1 : ℝ) ≤ X) hXC hTpos.le
    linarith
  linarith

/-- **B5 `unTrLocalInitBARow'_holds`**: the merged row `UNTrLocalInitBARow'` (`BA/UNPins.lean:181`), one line from B4 and P6. -/
theorem unTrLocalInitBARow'_holds : UNTrLocalInitBARow' :=
  UNTrLocalInitBARow'_iff_at.2 fun hLoc d hd => unTrLocalInitBAAt'_of_locAvg d hd (UNLocAvgBA_iff_at.1 hLoc d hd)

/-! ## B6: compiled nonempty instances at `d = 3` on the class sequence `S0` (`(L, g) = (4, 3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`)

`E = E_* = (fp 4 _).E` (the bulk energy of the flow point), `κ = κ_* = clsκ 4 _`, `δ = (π κ_*)³/8`; the window hypothesis is discharged
by the merged `BAbulk_window`.  `UNLocAvgBAAt 3` and `UNLocAvgBA` are the pins of T2514 row a (A8, A7), not yet on `main`: they stay
hypotheses of the examples; every other hypothesis is discharged. -/

section Inst

open RBM.BA.UNPinsInst RBM.Univ.BAInst

private theorem MATrLocalBA_hg : (0 : ℝ) < 3 / 10 := by norm_num

private theorem MATrLocalBA_hδ : 0 < (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 := by
  have := clsκ_pos 4 MATrLocalBA_hg; positivity

private theorem MATrLocalBA_hwin : ∀ x : ℝ, |x - (fp 4 MATrLocalBA_hg).E| ≤ (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 →
    ∀ᶠ n in atTop, BAbulk 3 (S0.L n) (S0.lam n) (clsκ 4 MATrLocalBA_hg / 2) x := fun x hx =>
  S0_bulk.mono fun n hn => BAbulk_window 3 (S0.L n) (S0.lam n) _ _ x (clsκ_pos 4 MATrLocalBA_hg) hn hx

/-- **B2 at `S0`, `d = 3`**: the tracial local law of the block Anderson model at `S0`, `κ_*`, `E_*`, `δ = (π κ_*)³/8`, from the block
averaged local law `UNLocAvgBAAt 3` (a hypothesis: T2514 row a). -/
example (hL : UNLocAvgBAAt 3) :
    UNTrLocal S0 (UNModelC.ba S0).toUNModel (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalBAAt_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin

/-- **B2 at `S0`, one more step**: the conclusion applied at `(ε, τ, D) = (1/10, 1/10, 1)`. -/
example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
    |z.re - (fp 4 MATrLocalBA_hg).E| ≤ (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 ∧ Nsz S0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 1 ∧
      ((S0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * S0.Bctl n (1 - z.im) < ‖stieltjesN ((UNModelC.ba S0).H n ω) z - BAm 3 (S0.L n) (S0.lam n) z‖} ≤
      ENNReal.ofReal (Nsz S0 n ^ (-1 : ℝ)) :=
  unTrLocalBAAt_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin (1 / 10) (1 / 10) 1 (by norm_num) (by norm_num) (by norm_num)

/-- **B3 at `S0`**: `unTrLocalBARow_holds` applied at `S0` (`UNLocAvgBA` is the `∀ d` pin of row a, A7). -/
example (hL : UNLocAvgBA) :
    UNTrLocal S0 (UNModelC.ba S0).toUNModel (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalBARow_holds hL 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin

/-- **B4 at `S0`, `d = 3`**: the initial-data local law at `S0`, `κ_*`, `E_*`, `δ = (π κ_*)³/8`, from `UNLocAvgBAAt 3`. -/
example (hL : UNLocAvgBAAt 3) :
    UNTrLocalInit' S0 (UNModelC.ba S0) (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalInitBAAt'_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin

/-- **B4 at `S0`, one more step**: the conclusion applied at `τ_s = 1/2`, `(ε, τ, D) = (1/10, 1/10, 1)`. -/
example (hL : UNLocAvgBAAt 3) : ∀ᶠ n in atTop, (UNModelC.ba S0).μ {ω | ∃ z : ℂ,
    |z.re - (fp 4 MATrLocalBA_hg).E| ≤ (Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8 ∧ Nsz S0 n ^ (-1 + 1 / 10 : ℝ) ≤ z.im ∧ z.im ≤ 1 ∧
      ((S0.W n : ℕ) : ℝ) ^ (1 / 10 : ℝ) * (S0.Bctl n (1 - z.im) + ouTStar S0 (1 / 2) n) <
        ‖stieltjesN (ouInit (UNModelC.ba S0) n (ouTStar S0 (1 / 2) n) ω) z - BAm 3 (S0.L n) (S0.lam n) z‖} ≤
      ENNReal.ofReal (Nsz S0 n ^ (-1 : ℝ)) :=
  unTrLocalInitBAAt'_of_locAvg 3 le_rfl hL (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin (1 / 2) (by norm_num) (by norm_num) (1 / 10) (1 / 10) 1
    (by norm_num) (by norm_num) (by norm_num)

/-- **B5 at `S0`**: `unTrLocalInitBARow'_holds` applied at `S0`. -/
example (hL : UNLocAvgBA) :
    UNTrLocalInit' S0 (UNModelC.ba S0) (fun n => BAm 3 (S0.L n) (S0.lam n)) (fp 4 MATrLocalBA_hg).E
      ((Real.pi * clsκ 4 MATrLocalBA_hg) ^ 3 / 8) :=
  unTrLocalInitBARow'_holds hL 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MATrLocalBA_hg) (clsκ_pos 4 MATrLocalBA_hg)
    (fp 4 MATrLocalBA_hg).E S0_bulk _ MATrLocalBA_hδ MATrLocalBA_hwin

end Inst

end RBM.BA

end
