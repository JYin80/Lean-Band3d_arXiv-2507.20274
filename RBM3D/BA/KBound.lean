/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KStep
import RBM3D.BA.KWardIneq
import RBM3D.BA.GreenSchur
import RBM3D.BA.FlowPins
import RBM3D.Chain.Carrier
import RBM3D.Chain.Step2Gen
import RBM3D.Loop.KLFinal

/-!
# BA-K12: the stage-K outputs (ticket T2399)

Dispatcher V2, DECISIONS §212; design `docs/reports/T2360-design.md:133` (row K12); probe
`t/T2360:RBM3D/Probe/T2360Pins.lean:40-130` (`BAKbound`, `BAKbound_of_uniform`, `precL_of_loss`, `bparam_comp`, `t0_ge`).

1. **`baKBoundAt_holds`**: `BAKBoundAt d n Λ κ` for every `n ≥ 1` (`3 ≤ d`, `0 < Λ`, `0 < κ`).  `n = 1, 2, 3` are K10's
   `baKBoundAt_one/two/three` (`BA/KInduct.lean`); `n ≥ 4` is the layer decomposition `BAKsol = W^{-d(n-1)} Σ_π BAKpi`
   (`baK_eq_sum_Kpi`, `BA/KMolecule.lean:133`) and `baKpiBoundAt_holds` (`BA/KStep.lean:597`): the BA twin of
   `KLInduct_BoundAt_of_Kpi` (`Loop/KLInduct.lean:1154`).
2. **`BAKbound d`** and **`BAKward d`**, the flow-level pins `STKboundgL`, `STKwardgL` (`Chain/Carrier.lean`) at the carrier `baFMz sz z` and
   the law `seqP (sz.withLam 0)`, along every `BAFlow`.  Both are consequences of a uniform deterministic bound in real time
   `t ∈ [0,1)` at `BAReal` data (`BAKBoundAt`, resp. `BAWardIneqAt`, `BA/KWardIneq.lean:93`): the data of the carrier are `BAReal` for every `n`
   (`BAflow_real`), eventually `0 < g₀_n ≤ 𝔡⁻¹` (`BAflow_lam0_window`), `B_{t,0}(g₀) ≤ ((κ+1)/κ) B_{t,0}(g)` (`g₀² = t₀ g²`,
   `t₀ ≥ κ/(κ+1)`), and the loss `C L^s` is a `≺` (`L^s ≤ N^{s/d}`, `N → ∞`).  `baKbound_holds`, `baKward_holds` are the unconditional theorems.
3. `KBound_baKsol_ward`: the Ward identity on `BAKsol` (`baK_ward` at `BAKsol_isKLoopS`).
4. The nonempty instances (section 3): `inst_BAKbound`, `BAKward` at `d = 3`, `baKBoundAt_holds` and `KBound_baKsol_ward` at the flow point of `(d, L) = (3, 4)`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Matrix
open scoped Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. `BAKBoundAt` for every `n ≥ 1` -/

section Bound

/-- **`(eq:bcal_k)` for `n ≥ 3`, from the layers** (the BA twin of `KLInduct_BoundAt_of_Kpi`, `Loop/KLInduct.lean:1154`): `(eq_K-Kpi)`
(`baK_eq_sum_Kpi`) gives the prefactor `W^{-d(n-1)} = ((W^d)⁻¹)^{n-1}`, the same for every layer `π`, times the sum over the
`2^{|diagonals n|}` layers, each `≤ C L^τ B^{n-1}` (`baKpiBoundAt_holds`); the count is absorbed in the constant, the loss `L^τ` is not split. -/
private theorem KBound_of_Kpi (d n : ℕ) [NeZero n] {Λ κ : ℝ} (hd : 3 ≤ d) (hn : 3 ≤ n) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    BAKBoundAt d n Λ κ := by
  intro τ hτ
  obtain ⟨C, hC, H⟩ := baKpiBoundAt_holds d n hd hn hΛ hκ τ hτ
  refine ⟨2 ^ (diagonals n).card * C, by positivity, ?_⟩
  intro L hL W hW g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hB0 : 0 ≤ Bparam d L g t 0 := KLIndStepA_Bparam_nonneg _ _
  have hLτ0 : 0 ≤ (L : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  rw [baK_eq_sum_Kpi d hκ hg hL W hr ⟨ht0, ht1⟩ hn σ a, norm_mul, norm_pow, norm_inv, norm_pow,
    Complex.norm_natCast]
  have hsum : ‖∑ π ∈ (diagonals n).powerset, BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π‖
      ≤ 2 ^ (diagonals n).card * (C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1)) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ π ∈ (diagonals n).powerset, ‖BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π‖
        ≤ ∑ _π ∈ (diagonals n).powerset, C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1) :=
          Finset.sum_le_sum fun π _ => H L hL g hg hgΛ E m hr t ht0 ht1 σ π a
      _ = 2 ^ (diagonals n).card * (C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1)) := by
          rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
          push_cast
          ring
  calc (((W : ℝ) ^ d)⁻¹) ^ (n - 1) *
        ‖∑ π ∈ (diagonals n).powerset, BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π‖
      ≤ (((W : ℝ) ^ d)⁻¹) ^ (n - 1) *
        (2 ^ (diagonals n).card * (C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1))) :=
        mul_le_mul_of_nonneg_left hsum (pow_nonneg hW0 _)
    _ = 2 ^ (diagonals n).card * C * (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 1) := by
        rw [mul_pow]; ring

/-- **`ML:Kbound`, `(eq:bcal_k)`, is proved at BA for every `n ≥ 1`**: `|𝒦^{(n)}_{t,σ,a}| ≤ C L^τ (W^{-d} B_{t,0})^{n-1}`, uniformly in
`L ≥ 3`, `W ≥ 1`, `g ∈ (0, Λ]`, the real-axis data `BAReal d L g κ E m` and `t ∈ [0,1)`, with `C` depending on `(d, n, Λ, κ, τ)` only.
`n = 1, 2, 3` by `baKBoundAt_one/two/three` (`BA/KInduct.lean:270, 291, 425`), `n ≥ 4` by the layers (`KBound_of_Kpi`; no hypothesis of another gate). -/
theorem baKBoundAt_holds (d : ℕ) {Λ κ : ℝ} (hd : 3 ≤ d) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∀ n : ℕ, 1 ≤ n → BAKBoundAt d n Λ κ := by
  intro n hn
  rcases (show n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | rfl | h4
  · exact baKBoundAt_one d Λ κ
  · exact baKBoundAt_two hd hΛ hκ
  · exact baKBoundAt_three hd hΛ hκ
  · have : NeZero n := ⟨by omega⟩
    exact KBound_of_Kpi d n hd (by omega) hΛ hκ

end Bound

/-! ## 2. The reduction from the uniform bounds to the flow-level pins -/

section Reduction

/-- A loss `C L^s` is a `≺` at the scale `N`, under any law (the failure event is eventually empty): the law-free form of the private
`KLFinal_prec_of_loss` (`Loop/KLFinal.lean:212`; probe `precL_of_loss`). -/
private theorem KBound_precL_of_loss {d : ℕ} (sz : Sizes d) (μ : Measure sz.SeqΩ) (hd : 0 < d) (hN : sz.SizeTendsto)
    {U : ℕ → Type*} {ξ ζ : ∀ n, U n → sz.SeqΩ → ℝ} (hζ : ∀ n u ω, 0 ≤ ζ n u ω)
    (H : ∀ s : ℝ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, ∀ u ω,
      ξ n u ω ≤ C * ((sz.L n : ℕ) : ℝ) ^ s * ζ n u ω) :
    PrecL sz μ ξ ζ := by
  refine StochDomAt.of_eventually_empty fun τ hτ => ?_
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C, hC, hH⟩ := H (d * (τ / 2)) (by positivity)
  have hlarge : ∀ᶠ n in atTop, C ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
    ((tendsto_rpow_atTop (half_pos hτ)).comp hN).eventually_ge_atTop C
  filter_upwards [hH, hlarge] with n hn hCn
  ext ω
  simp only [badSetAt, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro u
  have hNn : (0 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hLN := sz.L_rpow_le hd n (by positivity : 0 ≤ d * (τ / 2))
  rw [show d * (τ / 2) / (d : ℝ) = τ / 2 by field_simp] at hLN
  calc ξ n u ω ≤ C * ((sz.L n : ℕ) : ℝ) ^ (d * (τ / 2)) * ζ n u ω := hn u ω
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ((sz.size n : ℕ) : ℝ) ^ (τ / 2) * ζ n u ω := by
        refine mul_le_mul_of_nonneg_right ?_ (hζ n u ω)
        exact mul_le_mul hCn hLN (by positivity) (by positivity)
    _ = ((sz.size n : ℕ) : ℝ) ^ τ * ζ n u ω := by
        rw [← Real.rpow_add' hNn (by linarith), add_halves]

/-- `B_{t,0}` at the flow coupling `g₀` against the coupling `g` of the pin: `g² ≤ c g₀²`, `1 ≤ c`, `t < 1` give `B(g₀) ≤ c B(g)`. -/
private theorem KBound_bparam_comp (d L : ℕ) {g g₀ t c : ℝ} (ht : t < 1) (hc : 1 ≤ c) (h : g ^ 2 ≤ c * g₀ ^ 2) :
    Bparam d L g₀ t 0 ≤ c * Bparam d L g t 0 := by
  have h1 : 0 < |1 - t| := abs_pos.2 (by linarith)
  have hA : 0 < g₀ ^ 2 + |1 - t| := by positivity
  have hB : 0 < g ^ 2 + |1 - t| := by positivity
  have hLd : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have e1 : (g₀ ^ 2 + |1 - t|)⁻¹ ≤ c * (g ^ 2 + |1 - t|)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, mul_one, div_le_div_iff₀ hA hB]
    nlinarith [abs_nonneg (1 - t)]
  have e2 : ((L : ℝ) ^ d * |1 - t|)⁻¹ ≤ c * ((L : ℝ) ^ d * |1 - t|)⁻¹ := by nlinarith
  unfold Bparam
  simp only [Nat.cast_zero, zero_add, one_pow, inv_one, mul_one]
  nlinarith

/-- `t₀ = Im m / (Im m + Im z) ≥ κ/(κ+1)` on the chain domain (`κ ≤ Im m`, `0 < Im z ≤ 1`). -/
private theorem KBound_t0_ge {z m : ℂ} {κ : ℝ} (hκ : 0 < κ) (hm : κ ≤ m.im) (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    κ / (κ + 1) ≤ BAt0 z m := by
  unfold BAt0
  have hm0 : 0 < m.im := lt_of_lt_of_le hκ hm
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `Im z_n > 0` on the chain domain (a copy of the private `GreenSchur_zim_pos`, `BA/GreenSchur.lean:49`). -/
private theorem KBound_zim_pos {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ}
    (h : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) : 0 < (z n).im := by
  have h1 := (h.2 n).2.1
  have h2 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (by have := sz.one_le_size n; omega)) _
  linarith

/-- **The comparison of the couplings along a flow**: `(W^d)⁻¹ B_{t,0}(g₀_n) ≤ ((κ+1)/κ) · (W^{-d} B_{t,0}(g_n))` for every `n` and `t < 1`
(`g₀² = t₀ g²`, `t₀ ≥ κ/(κ+1)`, `KBound_bparam_comp`); `W^{-d} B_{t,0}(g_n)` is `sz.Bctl n t`. -/
private theorem KBound_B_le {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht : t < 1) :
    (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) t 0 ≤ (κ + 1) / κ * sz.Bctl n t := by
  obtain ⟨hκm, -, hz1⟩ := hflow.2 n
  have hzim := KBound_zim_pos sz hflow n
  have ht0 := KBound_t0_ge hκ hκm hzim hz1
  have ht0' : 0 < BAflowT0 sz z n := BAt0_pos hzim (lt_of_lt_of_le hκ hκm)
  have hc : 1 ≤ (κ + 1) / κ := by rw [le_div_iff₀ hκ]; linarith
  have hg : sz.lam n ^ 2 ≤ (κ + 1) / κ * BAflowLam0 sz z n ^ 2 := by
    have e : BAflowLam0 sz z n ^ 2 = BAflowT0 sz z n * sz.lam n ^ 2 := by
      unfold BAflowLam0; rw [mul_pow, Real.sq_sqrt ht0'.le]
    rw [e]
    have h1 : 1 ≤ (κ + 1) / κ * BAflowT0 sz z n := by
      have := mul_le_mul_of_nonneg_left ht0 (by positivity : 0 ≤ (κ + 1) / κ)
      calc (1 : ℝ) = (κ + 1) / κ * (κ / (κ + 1)) := by field_simp
        _ ≤ _ := this
    nlinarith [sq_nonneg (sz.lam n)]
  have hcomp := KBound_bparam_comp d (sz.L n) ht hc hg
  have hW : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := by positivity
  unfold Sizes.Bctl
  calc _ ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ((κ + 1) / κ * Bparam d (sz.L n) (sz.lam n) t 0) :=
        mul_le_mul_of_nonneg_left hcomp hW
    _ = _ := by ring

/-- The data of the carrier `baFMz sz z` at the size index `n`: `BAReal`, and the sign of `η`. -/
private theorem KBound_eta_nonneg {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (sz : Sizes d) {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {t : ℝ} (ht : t < 1) :
    0 ≤ (baFMz sz z).eta n t := by
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have : 0 < (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := hr.1.1
  change 0 ≤ (1 - t) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im
  exact mul_nonneg (by linarith) this.le

/-- **The stage-K pin `BAKbound`** (`ML:Kbound` for `BA`, `1_2:1056`; probe `T2360Pins.lean:49-52`): along a flow,
`max |𝒦^{(k)}_{τ,σ,a}| ≺ (W^{-d} B_{τ,0})^{k-1}` for every time sequence `τ ∈ [0,1)`, under the block Anderson law
`seqP (sz.withLam 0)` (the generic `STKboundgL` at the carrier `baFMz`, `3 ≤ d` as in `STMainIndG`, `BA/FlowPins.lean:408`). -/
def BAKbound (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      STKboundgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))

/-- **The stage-K pin `BAKward`** (`lem_wardineq_K`, `(wardineq_K)`, `3_5:1001`, at BA): along a flow, for every time sequence `τ ∈ [0,1)`
and `k ≥ 2`, `max_σ Σ_{a_k} |𝒦^{(k)}_{τ,σ,a}| ≺ (W^d η_τ)⁻¹ (W^{-d} B_{τ,0})^{k-2}`, `η_τ = (1 - τ) Im m_F` (the generic `STKwardgL` at the carrier
`baFMz`).  Not to be confused with the identity `baK_ward` of K02 (`BA/KWard.lean:305`), the Ward identity of `BAKsol`. -/
def BAKward (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
    ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
      STKwardgL (baFMz sz z) (Sizes.seqP (sz.withLam 0))

/-- **The reduction (K2).**  The uniform deterministic bounds `BAKBoundAt` (real `t ∈ [0,1)`, `BAReal` data) give the stage-K pin along every
flow: the data of the carrier `baFMz sz z` are `BAReal` for every `n` (`BAflow_real`), the coupling is `g₀ ≤ 𝔡⁻¹` eventually
(`BAflow_lam0_window`), and `B(g₀) ≤ ((κ+1)/κ) B(g)` (`KBound_B_le`), so the constant of the pin is `C ((κ+1)/κ)^{k-1}`; no complex `t`,
no horizon (`BAflowT0` is not used).  `3 ≤ d` enters `U` because `baKBoundAt_two/three` need it (the probe's `U` had none). -/
theorem BAKbound_of_uniform (d : ℕ)
    (U : 3 ≤ d → ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 1 ≤ n → BAKBoundAt d n Λ κ) : BAKbound d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ hτ0 hτ1 k hk
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n => by
    unfold Sizes.Bctl Bparam
    positivity
  refine KBound_precL_of_loss sz _ (by omega) hflow.1.2.2.1 (fun n u ω => pow_nonneg (hB n) _) ?_
  intro s hs
  obtain ⟨C, hC, H⟩ := U hd 𝔡⁻¹ κ k (inv_pos.2 h𝔡) hκ hk s hs
  refine ⟨C * ((κ + 1) / κ) ^ (k - 1), by positivity, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro u ω
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hbd := H (sz.L n) (sz.three_le_L n) (sz.W n) (sz.W_pos n) (BAflowLam0 sz z n) hn.1 hn.2
    (BAflowEs sz z n) _ hreal (τ n) (hτ0 n) (hτ1 n) u.1 u.2
  have hstep := KBound_B_le hκ sz hflow n (hτ1 n)
  have hpow := pow_le_pow_left₀ (by unfold Bparam; positivity) hstep (k - 1)
  have hLs : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) s
  change ‖BAKsol d (sz.L n) (sz.W n)
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))
      (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (τ n) (KLloopOf d (sz.L n) u.1 u.2)‖ ≤ _
  refine hbd.trans ?_
  calc C * ((sz.L n : ℕ) : ℝ) ^ s *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) (τ n) 0) ^ (k - 1)
      ≤ C * ((sz.L n : ℕ) : ℝ) ^ s * (((κ + 1) / κ) * sz.Bctl n (τ n)) ^ (k - 1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = C * ((κ + 1) / κ) ^ (k - 1) * ((sz.L n : ℕ) : ℝ) ^ s * sz.Bctl n (τ n) ^ (k - 1) := by
        rw [mul_pow]; ring

/-- **`ML:Kbound` at BA is proved**: `BAKbound d`, for every `d` (the `3 ≤ d` is a hypothesis of the pin), no hypothesis of another gate. -/
theorem baKbound_holds (d : ℕ) : BAKbound d :=
  BAKbound_of_uniform d fun hd _ _ n hΛ hκ hn => baKBoundAt_holds d hd hΛ hκ n hn

/-- **The Ward reduction.**  The uniform bounds `BAWardIneqAt` (`BA/KWardIneq.lean:93`, real `t ∈ [0,1)`, `BAReal` data) give the pin
`STKwardgL` along every flow, by the same reduction as `BAKbound_of_uniform`; `η` is `etaOf (BAmF ..) t = (1 - t) Im m_F`, the same factor
`((1 - t) m.im)` on both sides (no `c` on `η`), so the constant of the pin is `C ((κ+1)/κ)^{k-2}`.  The last label is `x`, and the loop is
`KLloopOf d L σ (a, x) = ⟨List.ofFn σ, List.ofFn a ++ [x]⟩` (`Carrier_ofFn_ext`). -/
private theorem KBound_BAKward_of_uniform (d : ℕ)
    (U : 3 ≤ d → ∀ (Λ κ : ℝ) (n : ℕ), 0 < Λ → 0 < κ → 2 ≤ n → BAWardIneqAt d n Λ κ) : BAKward d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow τ hτ0 hτ1 k hk
  have hB : ∀ n, 0 ≤ sz.Bctl n (τ n) := fun n => by
    unfold Sizes.Bctl Bparam
    positivity
  have hζ : ∀ n, 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (τ n))⁻¹ * (sz.Bctl n (τ n)) ^ (k - 2) :=
    fun n => mul_nonneg (inv_nonneg.2 (mul_nonneg (by positivity) (KBound_eta_nonneg sz hflow n (hτ1 n))))
      (pow_nonneg (hB n) _)
  refine KBound_precL_of_loss sz _ (by omega) hflow.1.2.2.1 (fun n u ω => hζ n) ?_
  intro s hs
  obtain ⟨C, hC, H⟩ := U hd 𝔡⁻¹ κ k (inv_pos.2 h𝔡) hκ hk s hs
  refine ⟨C * ((κ + 1) / κ) ^ (k - 2), by positivity, ?_⟩
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow] with n hn
  intro u ω
  have : NeZero (sz.L n) := ⟨by have := sz.three_le_L n; omega⟩
  have hreal := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  have hbd := H (sz.L n) (sz.three_le_L n) (sz.W n) (sz.W_pos n) (BAflowLam0 sz z n) hn.1 hn.2
    (BAflowEs sz z n) _ hreal (τ n) (hτ0 n) (hτ1 n) u.1 u.2
  have hstep := KBound_B_le hκ sz hflow n (hτ1 n)
  have hpow := pow_le_pow_left₀ (by unfold Bparam; positivity) hstep (k - 2)
  have hLs : 0 ≤ ((sz.L n : ℕ) : ℝ) ^ s := Real.rpow_nonneg (Nat.cast_nonneg _) s
  have hη : (baFMz sz z).eta n (τ n) =
      (1 - τ n) * (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n).im := rfl
  have hηnn : 0 ≤ (((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (τ n))⁻¹ :=
    inv_nonneg.2 (mul_nonneg (by positivity) (KBound_eta_nonneg sz hflow n (hτ1 n)))
  have hsum : ∑ x : Zd d (sz.L n), ‖(baFMz sz z).K n (τ n) u.1
        (fun i : Fin k => if h : (i : ℕ) < k - 1 then u.2 ⟨i, h⟩ else x)‖ =
      ∑ x : Zd d (sz.L n), ‖BAKsol d (sz.L n) (sz.W n)
        (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
          (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))
        (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) (τ n)
        ⟨List.ofFn u.1, List.ofFn u.2 ++ [x]⟩‖ := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Carrier_ofFn_ext (by omega : 1 ≤ k) u.2 x]
    rfl
  rw [← hη] at hbd
  rw [hsum]
  refine hbd.trans ?_
  calc C * ((sz.L n : ℕ) : ℝ) ^ s * (((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (τ n))⁻¹ *
        ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) (τ n) 0) ^ (k - 2)
      ≤ C * ((sz.L n : ℕ) : ℝ) ^ s * (((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (τ n))⁻¹ *
        (((κ + 1) / κ) * sz.Bctl n (τ n)) ^ (k - 2) :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hηnn)
    _ = C * ((κ + 1) / κ) ^ (k - 2) * ((sz.L n : ℕ) : ℝ) ^ s *
        ((((sz.W n : ℕ) : ℝ) ^ d * (baFMz sz z).eta n (τ n))⁻¹ * sz.Bctl n (τ n) ^ (k - 2)) := by
        rw [mul_pow]; ring

/-- **`lem_wardineq_K` at BA is proved**: `BAKward d`, for every `d`, no hypothesis of another gate.  The premises `KWardIneq_IndAt d k Λ κ`
(`3 ≤ k ≤ n`) of K11's `baWardIneq_holds` are discharged by `KWardIneq_IndAt_of_abs` of K09b's `KStep_baIndStepAbs_holds`. -/
theorem baKward_holds (d : ℕ) : BAKward d :=
  KBound_BAKward_of_uniform d fun hd _ _ n hΛ hκ hn =>
    baWardIneq_holds d n hd hn hΛ hκ
      (fun k hk _ _ => KWardIneq_IndAt_of_abs (KStep_baIndStepAbs_holds k hd hk hΛ hκ))

/-- **The Ward identity on `BAKsol`, unconditional** (`lem_WI_K`, `(WI_calK)`, `1_2:1034-1046`; band: `KLK_ward`, `Loop/KLWard.lean:1318`):
for `σ = (s, μ, -s)`, `n = |μ| + 2`, `Σ_{a_n} 𝒦^{(n)}_{t,σ,a} = (2 i W^d η_t)⁻¹ (𝒦^{(n-1)}_{t,(+,μ),â} - 𝒦^{(n-1)}_{t,(-,μ),â})`.
This is the probe's `BAKward` (`t/T2360:RBM3D/Probe/T2360Pins.lean:306`, on `BAKsol`), which K02 (`BA/KWard.lean:304`, T2369) leaves to this row:
`baK_ward` (K02) at the family `BAKsol` (`BAKsol_isKLoopS (baKsolve d)`, K05b) and its level-2 clause (`baKsol_two`, K10).  Distinct from the
flow-level pin `BAKward` above (an estimate), which is the ticket's `BAKward`. -/
theorem KBound_baKsol_ward (d : ℕ) {Λ κ g : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) {L : ℕ} [NeZero L] (hL : 3 ≤ L) {W : ℕ}
    (hW : 1 ≤ W) (hg : 0 < g) (hgΛ : g ≤ Λ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * (PropSpin m true).im : ℝ) : ℂ))⁻¹ *
            (BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨true :: μ, a⟩
              - BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t ⟨false :: μ, a⟩) :=
  baK_ward d L W g κ E m hr hL hW (BAKsol_isKLoopS (baKsolve d) hΛ hκ hL hg hgΛ hr)
    (fun (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ : Bool × Bool) (a₁ a₂ : Zd d L) => by
    simpa [KLloopOf, List.ofFn_succ] using baKsol_two d hκ hg hL W hr ht ![σ.1, σ.2] ![a₁, a₂])

end Reduction

/-! ## 3. Compiled nonempty instances

Flow data: `d = 3`, `sz0` (`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `n = 0`: `L = 4`, `W = 32`, `N = 2097152`),
`zSeq`, `(κ, ε, 𝔠, 𝔡) = (1/2, 1/10, 1/6, 1/10)`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`, proved).  The pins
`inst_BAKbound` and the `BAKward` examples are the theorems `baKbound_holds`, `baKward_holds` at this data: no hypothesis is left, since the uniform
bounds `U` are the proved `baKBoundAt_holds`, `baWardIneq_holds`.  Deterministic datum: the flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`;
`P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀`, `0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `W = 2` (`W^d = 8`), `t = 1/2`, `τ = 1`, distinct labels of `Z_4^3`. -/

/-- **`inst_BAKbound`**: the pin `BAKbound` at `d = 3`, `sz0`, `zSeq`; no hypothesis left. -/
theorem inst_BAKbound :
    STKboundgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) :=
  baKbound_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0

/-- **The pin `BAKward` at `d = 3`, `sz0`, `zSeq`** (`STKwardgL` at the carrier `baFMz`); no hypothesis left. -/
example : STKwardgL (baFMz SizesInst.sz0 FlowPinsInst.zSeq) (Sizes.seqP (SizesInst.sz0.withLam 0)) :=
  baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0

/-- The two pins at `d = 3` as statements. -/
example : BAKbound 3 ∧ BAKward 3 := ⟨baKbound_holds 3, baKward_holds 3⟩

/-- `inst_BAKbound` at the time sequence `τ ≡ 1/2` and the loop length `k = 4`: `max_{σ,a} |𝒦^{(4)}_{1/2,σ,a}| ≺ (W^{-d} B_{1/2,0})^3` along `sz0`. -/
example :
    PrecL SizesInst.sz0 (Sizes.seqP (SizesInst.sz0.withLam 0))
      (U := fun n => (Fin 4 → Bool) × (Fin 4 → Zd 3 (SizesInst.sz0.L n)))
      (fun n p _ => ‖(baFMz SizesInst.sz0 FlowPinsInst.zSeq).K n (1 / 2) p.1 p.2‖)
      (fun n _ _ => (SizesInst.sz0.Bctl n (1 / 2)) ^ (4 - 1)) :=
  inst_BAKbound (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 4 (by norm_num)

/-- `BAKward` at `d = 3`, `sz0`, `zSeq`, `τ ≡ 1/2` and `k = 3`: `max_σ Σ_{a_3} |𝒦^{(3)}_{1/2,σ,a}| ≺ (W^d η_{1/2})⁻¹ (W^{-d} B_{1/2,0})` along `sz0`; the last label is summed. -/
example :
    PrecL SizesInst.sz0 (Sizes.seqP (SizesInst.sz0.withLam 0))
      (U := fun n => (Fin 3 → Bool) × (Fin (3 - 1) → Zd 3 (SizesInst.sz0.L n)))
      (fun n p _ => ∑ x : Zd 3 (SizesInst.sz0.L n),
        ‖(baFMz SizesInst.sz0 FlowPinsInst.zSeq).K n (1 / 2) p.1
          (fun i : Fin 3 => if h : (i : ℕ) < 3 - 1 then p.2 ⟨i, h⟩ else x)‖)
      (fun n _ _ => (((SizesInst.sz0.W n : ℕ) : ℝ) ^ 3 *
          (baFMz SizesInst.sz0 FlowPinsInst.zSeq).eta n (1 / 2))⁻¹ * (SizesInst.sz0.Bctl n (1 / 2)) ^ (3 - 2)) :=
  baKward_holds 3 le_rfl (1 / 2) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num) (1 / 6)
    SizesInst.sz0 FlowPinsInst.zSeq FlowPinsInst.flow_sz0 (fun _ => 1 / 2) (fun _ => by norm_num) (fun _ => by norm_num) 3
    (by norm_num)

/-- **The bridge `bandFM_STKward` applied** at the band flow `(sz0, z0)`: the proved band `STKward` (`stKward_of_flow`) is the generic
`STKwardgL` at the band carrier and the band law. -/
example : STKwardgL (bandFM SizesInst.sz0 (STflowE InductionDefsInst.z0)) (Sizes.seqP SizesInst.sz0) :=
  (bandFM_STKward SizesInst.sz0 (STflowE InductionDefsInst.z0)).1
    (stKward_of_flow SizesInst.sz0 le_rfl (by norm_num) InductionDefsInst.flow_z0)

namespace KBoundInst

open RBM.BA.MFixedPointInst

/-- **`baKBoundAt_holds`** at the flow point, `n = 4` (`n ≥ 4`: the layers), `σ = (+,+,-,+)`, distinct labels, `W = 2`, `t = 1/2`, `τ = 1`:
`|𝒦^{(4)}| ≤ C L^τ (W^{-d} B_{t,0})^{3}`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (4 - 1) := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_holds 3 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) P.real.1.1 4 (by norm_num) 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- `baKBoundAt_holds` at the flow point, `n = 5`, `σ = (+,+,-,+,+)` (the two-edge layer has a tree), `W = 2`, `t = 1/2`, `τ = 1`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, true, false, true, true]
          ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (5 - 1) := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_holds 3 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) P.real.1.1 5 (by norm_num) 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- `baKBoundAt_holds` at the flow point, `n = 3` (the base `baKBoundAt_three`), `σ = (+,-,+)`, `W = 2`, `t = 1/2`, `τ = 1`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ (3 - 1) := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_holds 3 (Λ := 10) (κ := P.m0.im) le_rfl (by norm_num) P.real.1.1 3 (by norm_num) 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) _ _⟩

/-- **`KBound_baKsol_ward`** at the flow point: `σ = (+, μ, -)` with `μ = (+, -)`, `n = 4`, labels `a = (a₁, a₂, a₃)` and the last label summed,
`W = 2`, `t = 1/2`. -/
example : ∑ x : Zd 3 4, BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        ⟨true :: [true, false] ++ [!true], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]] ++ [x]⟩
      = (2 * Complex.I * ((2 : ℕ) : ℂ) ^ 3 * (((1 - 1 / 2) * (PropSpin P.m0 true).im : ℝ) : ℂ))⁻¹ *
          (BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
              ⟨true :: [true, false], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩
            - BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
              ⟨false :: [true, false], [![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩) :=
  KBound_baKsol_ward 3 (Λ := 10) (κ := P.m0.im) (by norm_num) P.real.1.1 (by norm_num) (by norm_num) P.g0_pos P.g0_le P.real
    (1 / 2) ⟨by norm_num, by norm_num⟩ true [true, false] _ rfl

end KBoundInst

end RBM.BA
