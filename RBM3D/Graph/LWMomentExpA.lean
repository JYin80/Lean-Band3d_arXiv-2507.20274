/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWMoment
import RBM3D.Graph.LWTermExpN

/-!
# LW-13b R2 (A): `lem:LW_moment_exp` in the no-exponential regime (T2359)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex` (cited `7_8:line`): `lem:LW_moment_exp` (`7_8:78-83`) and the case
distinction of its proof (`7_8:1602-1611`): in the regime (A) `|a - b| ≤ K (log W)^{3/2} ℓ_t` or `ℓ ≤ K (log W)^{3/2} ℓ_t` the
exponential factor `e^{-(|a-b|∧ℓ/ℓ_t)^{1/2}}` costs only `e^{(K (log W)^{3/2})^{1/2}} = N^{o(1)}`, so the bound follows from
`lem:LW_moment` (`lwMoment_holds`, `Graph/LWMoment.lean:1785`) for the B class; this is the twin of `lwtermExpN_of_LWterm`
(`Graph/LWTermExpN.lean:414`, T2342), with `lem:LW_moment` in place of `lem:LWterm`.

`lwMomExpNoExp_holds : ∀ d K, 0 < K → LWMomExpNoExpF d K` (for every `K > 0`, DECISIONS §162 (2)): `LWMomExpNoExpF d K` is the
target `LWMomentExp` (`Graph/LWPins.lean:341`) on the subtype `λ²/L² < 1 - t` restricted by `regA d K`, with the merged `LWf`.

* Section 1: the statements `regA`, `LWMomExpNoExpF`.
* Section 2: `≺` with a factor `N^{o(1)}`, the data of the B class, `LWAssm` for the B class at `ε₁ = min(ε₀, d c/2)`.
* Section 3: the deterministic comparison `Φ_B(c r)² ≤ C e^{√(m/ℓ_t)} 𝖳_t(m)²`, `m = r ∧ ℓ`, and the loss `N^{o(1)}`.
* Section 4: `lwMomExpNoExp_holds`.
* Section 5: a compiled nonempty instance.

Ports (merged files, text copied and adapted): `Graph/LWTermExpN.lean:42-61, 182-185, 383-410, 414-514`
at the merged commit `1fcb883`, `Graph/LWPsi.lean:445-456` (`sfT²`), `Graph/LWMoment.lean:473-505` (`lwMoment_tail`).
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

open MeasureTheory Filter
open RBM RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. The statements -/

/-- the no-exponential-decay regime at scale `K` (`7_8:1602` with `K`): `|a-b| ≤ K (log W)^{3/2} ℓ_t` or `ℓ ≤ K (log W)^{3/2} ℓ_t` -/
def regA (d : ℕ) (K : ℝ) (sz : Sizes d) (n : ℕ) (t ℓ : ℝ) (q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) : Prop :=
  ((zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) : ℕ) : ℝ) ≤
      K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t ∨
    ℓ ≤ K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ) * ellT (sz.L n) (sz.lam n) t

/-- (A) on the regime `regA d K` (the target `LWMomentExp`, `Graph/LWPins.lean:341`, with the subtype restricted by `regA`; `LWf`
as in the target: the `D`-restricted `LWfD` of R1 is not used here, R3 converts by `LWfD … univ = LWf`). -/
def LWMomExpNoExpF (d : ℕ) (K : ℝ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (p : ℕ), 2 ∣ p → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ),
    STFlow sz κ ε 𝔠 𝔡 z → ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
      ∀ (ε₀ : ℝ) (Ψ ℓ : ℕ → ℝ), LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ → ∀ D : ℝ, 0 < D →
        sz.Prec (U := fun n => {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
            sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q})
          (fun n q _ => ∫ ω, ‖LWf sz n (STflowE z n) (t n) ω q.1.1 q.1.2‖ ^ p ∂(sz.seqP))
          (fun n q _ => ((etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) *
            sfT d (sz.L n) ((sz.W n : ℕ) : ℝ) (sz.lam n) (t n)
              (min ((zdistInf d (sz.L n) (STblk sz n q.1.1 - STblk sz n q.1.2) : ℕ) : ℝ) (ℓ n))) ^ p + ((sz.W n : ℕ) : ℝ) ^ (-D))

/-! ## 2. `≺` with a factor `N^{o(1)}`, the B class, `LWAssm` for the B class -/

/-- If `ζ ≤ N^σ ζ'` pointwise eventually for every `σ > 0` (with `ζ' ≥ 0`) and `ξ ≺ ζ`, then `ξ ≺ ζ'` (the twin of `lwN_prec_mono`,
`Graph/LWTermExpN.lean:42`, with a factor `N^{o(1)}` instead of a constant). -/
private theorem lwMEA_prec_mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Type*} {size : ℕ → ℕ}
    {ξ ζ ζ' : ∀ l, U l → Ω → ℝ}
    (hle : ∀ σ : ℝ, 0 < σ → ∀ᶠ l in atTop, ∀ u ω, 0 ≤ ζ' l u ω ∧ ζ l u ω ≤ (size l : ℝ) ^ σ * ζ' l u ω)
    (h : StochDomAt P size ξ ζ) : StochDomAt P size ξ ζ' := by
  refine StochDomAt.of_subset h fun τ hτ => ⟨τ / 2, half_pos hτ, ?_⟩
  filter_upwards [hle (τ / 2) (half_pos hτ)] with l hl
  rintro ω ⟨u, hu⟩
  refine ⟨u, ?_⟩
  obtain ⟨hnn, hz⟩ := hl u ω
  have hpos : 0 ≤ (size l : ℝ) ^ (τ / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmul : (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2)) = (size l : ℝ) ^ τ := by
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by linarith)]; congr 1; ring
  calc (size l : ℝ) ^ (τ / 2) * ζ l u ω ≤ (size l : ℝ) ^ (τ / 2) * ((size l : ℝ) ^ (τ / 2) * ζ' l u ω) :=
        mul_le_mul_of_nonneg_left hz hpos
    _ = (size l : ℝ) ^ τ * ζ' l u ω := by rw [← mul_assoc, hmul]
    _ < _ := hu

private theorem lwMEA_zdistInf_le {d : ℕ} (L : ℕ) [NeZero L] (x : Zd d L) : zdistInf d L x ≤ L := by
  refine Finset.sup_le fun i _ => ?_
  unfold zdist
  exact (min_le_left _ _).trans (ZMod.val_lt _).le

private theorem lwMEA_zdistInf_zero (d L : ℕ) : zdistInf d L (0 : Zd d L) = 0 := by
  unfold zdistInf
  exact Nat.eq_zero_of_le_zero (Finset.sup_le fun i _ => by simp)

private theorem lwMEA_flow_im_pos {d : ℕ} (sz : Sizes d) {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z)
    (n : ℕ) : 0 < (z n).im := by
  have h := (hflow.2 n).2.1
  have hN : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hN _) h

private theorem lwMEA_wneg (W : ℝ) (hW : 0 ≤ W) (d : ℕ) : W ^ (-(d : ℝ)) = (W ^ d)⁻¹ := by
  rw [Real.rpow_neg hW, Real.rpow_natCast]

/-- `Φ_n(0) = Bctl^{1/2}` for the B class with `c₀ = d`. -/
private theorem lwMEA_phi_zero {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) :
    LWPhiB sz (d : ℝ) K t n 0 = (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
  unfold LWPhiB Sizes.Bctl
  rw [lwMEA_wneg _ (Nat.cast_nonneg _)]
  simp

/-- `Φ_n(x)² = W^{-d} B_{t, ⌊x⌋ ∧ K}` for the B class with `c₀ = d`. -/
private theorem lwMEA_phi_sq {d : ℕ} (sz : Sizes d) (K : ℕ → ℕ) (t : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    LWPhiB sz (d : ℝ) K t n x ^ 2 =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (sz.lam n) (t n) (min ⌊x⌋₊ (K n)) := by
  unfold LWPhiB
  rw [lwMEA_wneg _ (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
  unfold Bparam
  positivity

/-- **`LWAssm` for the B class** (the first part of `lwtermExpN_of_LWterm`, `Graph/LWTermExpN.lean:414-470`): from `LWAssmExp`, the
B class `Φ = LWPhiB sz d K t`, `K n = ⌊ℓ n⌋ ∧ L n`, `c₀ = d`, satisfies `LWAssm` at the window `ε₁ = min(ε₀, d c/2)`,
`c = min(2𝔡𝔠, ε)/2`, with the constants `(2^d, d, (1 + 𝔡⁻²)^{1/2}, C ↦ ((C+1)^{d-2})^{1/2})` (`LWPhiB_psiAll`); `LWLoop2` for `Φ` is
`(LW_assm_exp)` at `D' = 1/𝔠` (`wT ≤ B_{r∧K}`, `W^{-D'} ≤ L^{-d}`). -/
private theorem lwMEA_assm {d : ℕ} (hd : 3 ≤ d) {κ ε 𝔡 𝔠 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (h𝔡 : 0 < 𝔡) (sz : Sizes d)
    {z : ℕ → ℂ} (hflow : STFlow sz κ ε 𝔠 𝔡 z) {t : ℕ → ℝ} (ht0 : ∀ n, 0 ≤ t n) (htT : ∀ n, t n ≤ lemT (z n))
    {ε₀ : ℝ} {Ψ ℓ : ℕ → ℝ} (hA : LWAssmExp sz (STflowE z) t ε₀ Ψ ℓ) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ LWAssm sz (STflowE z) t ε₁ Ψ (LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t)
      ((2 : ℝ) ^ d) (d : ℝ) (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2))) := by
  obtain ⟨hε₀, hwin, hinit, hℓ0, hℓt, hloop⟩ := hA
  have hd2 : 2 ≤ d := by omega
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hsize := tendsto_size sz hsz
  have him : ∀ n, 0 < (z n).im := lwMEA_flow_im_pos sz hflow
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (lemT_lt_one (him n))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (2 * 𝔡 * 𝔠) ε / 2 := ⟨_, rfl⟩
  have hc : 0 < c := by
    rw [hcdef]; have := lt_min (mul_pos (mul_pos two_pos h𝔡) h𝔠) hε; linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min ε₀ ((d : ℝ) * c / 2) := ⟨_, rfl⟩
  have hε₁pos : 0 < ε₁ := by
    rw [hε₁def]; exact lt_min hε₀ (by positivity)
  have hε₁a : ε₁ ≤ ε₀ := by rw [hε₁def]; exact min_le_left _ _
  have hε₁b : 2 * ε₁ ≤ (d : ℝ) * c := by
    have : ε₁ ≤ (d : ℝ) * c / 2 := by rw [hε₁def]; exact min_le_right _ _
    linarith
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => Nat.one_le_cast.2 (sz.W_pos n)
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => lt_of_lt_of_le one_pos (hW1 n)
  have hg : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  have ht : ∀ᶠ n in atTop, 0 ≤ t n ∧ t n ≤ 1 :=
    Eventually.of_forall fun n => ⟨ht0 n, (ht1 n).le⟩
  have hup : ∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ)) * Bparam d (sz.L n) (sz.lam n) (t n) 0 ≤
      ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) := by
    filter_upwards [lwN_Bctl_le sz hκ hε h𝔡 hflow htT] with n hn
    have h1 := hn (t n) (ht0 n) le_rfl
    rw [← hcdef] at h1
    have h2 := lwN_size_rpow_neg_le sz n hc.le
    have h3 : ((sz.W n : ℕ) : ℝ) ^ (-((d : ℝ) * c)) ≤ ((sz.W n : ℕ) : ℝ) ^ (-2 * ε₁) :=
      Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)
    rw [lwMEA_wneg _ (Nat.cast_nonneg _)]
    exact (h1.trans h2).trans h3
  set K : ℕ → ℕ := fun n => min ⌊ℓ n⌋₊ (sz.L n) with hKdef
  obtain ⟨-, hcls, hrel⟩ := LWPhiB_psiAll sz hd2 (ε₀ := ε₁) (c₀ := (d : ℝ)) K t hε₁pos le_rfl hg ht hup
  have hwin' : LWWindow sz ε₁ Ψ := by
    filter_upwards [hwin] with n hn
    exact ⟨hn.1, hn.2.trans (Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith))⟩
  have hinit' : LWInit sz (STflowE z) t ε₁ Ψ := by
    refine ⟨?_, hinit.2⟩
    refine lwN_prec_mono hsize (c := 1) ?_ hinit.1
    exact Eventually.of_forall fun n u ω => ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,
      by rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le (hW1 n) (by linarith)⟩
  have hD' : 0 < 1 / 𝔠 := by positivity
  have hL2 : LWLoop2 sz (STflowE z) t (LWPhiB sz (d : ℝ) K t) := by
    refine lwN_prec_mono hsize (c := 1) ?_ (hloop (1 / 𝔠) hD')
    filter_upwards [lwN_Wneg_le sz h𝔠 hband] with n hn
    rintro ⟨σ, a, b⟩ ω
    simp only
    have hLn : (zdistInf d (sz.L n) (a - b) : ℕ) ≤ sz.L n := lwMEA_zdistInf_le _ _
    rw [lwMEA_phi_sq, Nat.floor_natCast, one_mul]
    refine ⟨mul_nonneg (inv_nonneg.mpr (by positivity)) ?_, ?_⟩
    · unfold Bparam; positivity
    · refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
      exact lwN_tailW_le (L := sz.L n) _ hLn (by have := sz.three_le_L n; omega) rfl (hℓ0 n)
        (ht0 n) (ht1 n) hn
  exact ⟨ε₁, hε₁pos, hε₁pos, hwin', hinit', hcls, hrel, hL2⟩

/-! ## 3. The B class against `𝖳_t`, and the loss `N^{o(1)}` -/

/-- `[𝖳_t(r)]² = W^{-d} (g²+|1-t|)⁻¹ (r+1)^{-(d-2)} e^{-√(r/ℓ_t)}` (the copy of `LWPsi_sfT_sq`, `Graph/LWPsi.lean:445`). -/
private theorem lwMEA_sfT_sq {d L : ℕ} {W g t : ℝ} (hW : 0 < W) {r : ℝ} (hr : 0 ≤ r) :
    sfT d L W g t r ^ 2 = (W ^ d)⁻¹ * ((g ^ 2 + |1 - t|)⁻¹ * ((r + 1) ^ (d - 2))⁻¹) *
      Real.exp (-Real.sqrt (r / ellT L g t)) := by
  unfold sfT
  have h1 : 0 ≤ (W ^ d)⁻¹ := by positivity
  have h2 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have h3 : 0 ≤ ((r + 1) ^ (d - 2))⁻¹ := by positivity
  have h4 : Real.exp (-(1 / 2) * Real.sqrt (r / ellT L g t)) ^ 2 = Real.exp (-Real.sqrt (r / ellT L g t)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2, Real.sq_sqrt h3, h4]
  ring

/-- **The B class against `𝖳_t`** (regime `λ²/L² ≤ 1 - t`, block distance `r ≤ L`): with `m = r ∧ ℓ`,
`Φ_B(c r)² = W^{-d} B_{t, ⌊c r⌋ ∧ ⌊ℓ⌋ ∧ L} ≤ (2/(c ∧ 1))^{d-2} (1 + 2^{d-1}) e^{√(m/ℓ_t)} [𝖳_t(m)]²`:
`⌊c r⌋ ∧ ⌊ℓ⌋ ∧ L + 1 ≥ (c ∧ 1)(m+1)/2`, `B_{t,j} ≤ (2/(c∧1))^{d-2} B_{t,m}`, and the zero mode of `B_{t,m}` is dominated
(`zeroMode_le_of_ge`, `m ≤ L`). -/
private theorem lwMEA_phiB_sq_le {d L : ℕ} {W g t ℓ c : ℝ} (hd : 2 ≤ d) (hL : 1 ≤ (L : ℝ)) (ht : t < 1) (hW : 0 < W)
    (hgt : g ^ 2 / (L : ℝ) ^ 2 ≤ 1 - t) (hℓ : 0 ≤ ℓ) (hc : 0 < c) {r : ℕ} (hrL : r ≤ L) :
    (W ^ d)⁻¹ * Bparam d L g t (min ⌊c * (r : ℝ)⌋₊ (min ⌊ℓ⌋₊ L)) ≤
      ((2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1))) * Real.exp (Real.sqrt (min (r : ℝ) ℓ / ellT L g t)) *
        sfT d L W g t (min (r : ℝ) ℓ) ^ 2 := by
  have hc'0 : 0 < min c 1 := lt_min hc one_pos
  have hc'1 : min c 1 ≤ 1 := min_le_right _ _
  have hcc : min c 1 ≤ c := min_le_left _ _
  set c' : ℝ := min c 1 with hc'
  set m : ℝ := min (r : ℝ) ℓ with hm
  have hm0 : 0 ≤ m := le_min (Nat.cast_nonneg _) hℓ
  have hmr : m ≤ (r : ℝ) := min_le_left _ _
  have hmℓ : m ≤ ℓ := min_le_right _ _
  have hrL' : (r : ℝ) ≤ L := by exact_mod_cast hrL
  have hm1 : 0 < m + 1 := by linarith
  set j : ℕ := min ⌊c * (r : ℝ)⌋₊ (min ⌊ℓ⌋₊ L) with hj
  have hj1 : c' * m ≤ (j : ℝ) + 1 := by
    have ha : c * (r : ℝ) < (⌊c * (r : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hb : ℓ < (⌊ℓ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hcr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hcases : j = ⌊c * (r : ℝ)⌋₊ ∨ j = ⌊ℓ⌋₊ ∨ j = L := by omega
    rcases hcases with h | h | h <;> rw [h]
    · nlinarith [mul_le_mul_of_nonneg_left hmr hc'0.le, mul_le_mul_of_nonneg_right hcc hcr]
    · nlinarith [mul_le_mul_of_nonneg_left hmℓ hc'0.le, mul_le_mul_of_nonneg_right hc'1 hℓ]
    · nlinarith [mul_le_mul_of_nonneg_right hc'1 hm0]
  have hj2 : (c' / 2) * (m + 1) ≤ (j : ℝ) + 1 := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    nlinarith
  have hpow : (((j : ℝ) + 1) ^ (d - 2))⁻¹ ≤ (2 / c') ^ (d - 2) * ((m + 1) ^ (d - 2))⁻¹ := by
    have h1 : ((c' / 2) * (m + 1)) ^ (d - 2) ≤ ((j : ℝ) + 1) ^ (d - 2) := pow_le_pow_left₀ (by positivity) hj2 _
    rw [mul_pow] at h1
    calc (((j : ℝ) + 1) ^ (d - 2))⁻¹ ≤ ((c' / 2) ^ (d - 2) * (m + 1) ^ (d - 2))⁻¹ := inv_anti₀ (by positivity) h1
      _ = (2 / c') ^ (d - 2) * ((m + 1) ^ (d - 2))⁻¹ := by
          rw [div_pow, div_pow]; have := hc'0.ne'; have := hm1.ne'; field_simp
  have hA0 : 0 ≤ (g ^ 2 + |1 - t|)⁻¹ := by positivity
  have hZ0 : 0 ≤ ((L : ℝ) ^ d * |1 - t|)⁻¹ := by positivity
  have hp1 : 1 ≤ (2 / c') ^ (d - 2) := one_le_pow₀ (by rw [le_div_iff₀ hc'0]; linarith)
  have hB : Bparam d L g t j ≤ (2 / c') ^ (d - 2) * BparamR d L g t m := by
    unfold Bparam BparamR
    nlinarith [mul_le_mul_of_nonneg_left hpow hA0, mul_le_mul_of_nonneg_right hp1 hZ0]
  have hR : BparamR d L g t m ≤ (1 + 2 ^ (d - 1)) * ((g ^ 2 + |1 - t|)⁻¹ * ((m + 1) ^ (d - 2))⁻¹) := by
    have hz := zeroMode_le_of_ge hd hL ht hm0 (hmr.trans hrL') hgt
    unfold BparamR; linarith
  have hsq := lwMEA_sfT_sq (d := d) (L := L) (W := W) (g := g) (t := t) hW hm0
  have hexp : Real.exp (Real.sqrt (m / ellT L g t)) * Real.exp (-Real.sqrt (m / ellT L g t)) = 1 := by
    rw [← Real.exp_add]; simp
  calc (W ^ d)⁻¹ * Bparam d L g t j
      ≤ (W ^ d)⁻¹ * ((2 / c') ^ (d - 2) * ((1 + 2 ^ (d - 1)) * ((g ^ 2 + |1 - t|)⁻¹ * ((m + 1) ^ (d - 2))⁻¹))) :=
        mul_le_mul_of_nonneg_left (hB.trans (mul_le_mul_of_nonneg_left hR (by positivity))) (by positivity)
    _ = ((2 / c') ^ (d - 2) * (1 + 2 ^ (d - 1))) * ((W ^ d)⁻¹ * ((g ^ 2 + |1 - t|)⁻¹ * ((m + 1) ^ (d - 2))⁻¹)) * 1 := by ring
    _ = ((2 / c') ^ (d - 2) * (1 + 2 ^ (d - 1))) * ((W ^ d)⁻¹ * ((g ^ 2 + |1 - t|)⁻¹ * ((m + 1) ^ (d - 2))⁻¹)) *
          (Real.exp (Real.sqrt (m / ellT L g t)) * Real.exp (-Real.sqrt (m / ellT L g t))) := by rw [hexp]
    _ = _ := by rw [hsq]; ring

/-- **The loss is `N^{o(1)}`**: for `K > 0`, `q ∈ ℕ`, `C ≥ 0`, `σ > 0`, eventually
`(C e^{√(K (log W)^{3/2})})^q ≤ N^σ` (`W ≥ N^𝔠`, `N → ∞`: `√(K (log W)^{3/2}) ≤ ε log W` once `log W ≥ (K/ε²)²`, `ε = σ/(2(q+1))`, and
`log W ≤ log N`). -/
private theorem lwMEA_loss {d : ℕ} (sz : Sizes d) (hd : d ≠ 0) {𝔠 : ℝ} (h𝔠 : 0 < 𝔠) (hsz : sz.SizeTendsto)
    (hband : ∀ᶠ n in atTop, ((sz.size n : ℕ) : ℝ) ^ 𝔠 ≤ ((sz.W n : ℕ) : ℝ)) {K : ℝ} (hK : 0 < K) (q : ℕ) {C : ℝ}
    {σ : ℝ} (hσ : 0 < σ) :
    ∀ᶠ n in atTop, (C * Real.exp (Real.sqrt (K * Real.log ((sz.W n : ℕ) : ℝ) ^ (3 / 2 : ℝ)))) ^ q ≤
      ((sz.size n : ℕ) : ℝ) ^ σ := by
  set ε : ℝ := σ / (2 * ((q : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by positivity
  set Y₀ : ℝ := max 1 ((K / ε ^ 2) ^ 2) with hY₀
  have h1 : ∀ᶠ n in atTop, C ^ q ≤ ((sz.size n : ℕ) : ℝ) ^ (σ / 2) :=
    ((tendsto_rpow_atTop (half_pos hσ)).comp hsz).eventually_ge_atTop _
  filter_upwards [hband, ((tendsto_rpow_atTop h𝔠).comp hsz).eventually_ge_atTop (Real.exp Y₀), h1,
    hsz.eventually_ge_atTop 1] with n hb hbig hC1 hN1
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hN
  have hN0 : 0 < N := by linarith
  have hW0 : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hlogW : Y₀ ≤ Real.log ((sz.W n : ℕ) : ℝ) := (Real.le_log_iff_exp_le hW0).2 (le_trans hbig hb)
  set y : ℝ := Real.log ((sz.W n : ℕ) : ℝ) with hy
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hlogW
  have hy0 : 0 < y := by linarith
  have hWN : ((sz.W n : ℕ) : ℝ) ≤ N := by
    have hL : 0 < sz.L n := by have := sz.three_le_L n; omega
    have h : sz.W n ≤ sz.size n := by
      unfold Sizes.size
      calc sz.W n ≤ sz.W n * sz.L n := Nat.le_mul_of_pos_right _ hL
        _ ≤ (sz.W n * sz.L n) ^ d := Nat.le_self_pow hd _
    rw [hN]; exact_mod_cast h
  have hlogN : y ≤ Real.log N := Real.log_le_log hW0 hWN
  have hsq : K / ε ^ 2 ≤ Real.sqrt y :=
    (Real.le_sqrt (by positivity) hy0.le).2 (le_trans (le_max_right _ _) hlogW)
  have h32 : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy0, Real.rpow_one, Real.sqrt_eq_rpow]
  have hX : Real.sqrt (K * y ^ (3 / 2 : ℝ)) ≤ ε * y := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [h32]
    have hKε : K ≤ ε ^ 2 * Real.sqrt y :=
      calc K = ε ^ 2 * (K / ε ^ 2) := by field_simp
        _ ≤ ε ^ 2 * Real.sqrt y := mul_le_mul_of_nonneg_left hsq (sq_nonneg ε)
    calc K * (y * Real.sqrt y) ≤ (ε ^ 2 * Real.sqrt y) * (y * Real.sqrt y) :=
          mul_le_mul_of_nonneg_right hKε (by positivity)
      _ = ε ^ 2 * y * (Real.sqrt y * Real.sqrt y) := by ring
      _ = (ε * y) ^ 2 := by rw [Real.mul_self_sqrt hy0.le]; ring
  have hqε : (q : ℝ) * ε ≤ σ / 2 := by
    have : (q : ℝ) * ε ≤ ((q : ℝ) + 1) * ε := by nlinarith
    have e : ((q : ℝ) + 1) * ε = σ / 2 := by rw [hε]; field_simp
    linarith
  have hqX : (q : ℝ) * Real.sqrt (K * y ^ (3 / 2 : ℝ)) ≤ Real.log N * (σ / 2) := by
    have h2 : (q : ℝ) * Real.sqrt (K * y ^ (3 / 2 : ℝ)) ≤ (q : ℝ) * (ε * y) :=
      mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg _)
    have h3 : (q : ℝ) * (ε * y) ≤ (σ / 2) * y := by nlinarith [mul_le_mul_of_nonneg_right hqε hy0.le]
    nlinarith [mul_le_mul_of_nonneg_left hlogN (by positivity : (0 : ℝ) ≤ σ / 2)]
  have hexp2 : Real.exp ((q : ℝ) * Real.sqrt (K * y ^ (3 / 2 : ℝ))) ≤ N ^ (σ / 2) := by
    rw [Real.rpow_def_of_pos hN0]; exact Real.exp_le_exp.2 hqX
  calc (C * Real.exp (Real.sqrt (K * y ^ (3 / 2 : ℝ)))) ^ q
      = C ^ q * Real.exp ((q : ℝ) * Real.sqrt (K * y ^ (3 / 2 : ℝ))) := by
        rw [mul_pow, Real.exp_nat_mul]
    _ ≤ N ^ (σ / 2) * N ^ (σ / 2) := mul_le_mul hC1 hexp2 (Real.exp_pos _).le (Real.rpow_nonneg hN0.le _)
    _ = N ^ σ := by rw [← Real.rpow_add hN0]; congr 1; ring

/-! ## 4. `lem:LW_moment_exp` in the no-exponential regime -/

/-- **(A), `lem:LW_moment_exp` in the regime `regA d K`, for every `K > 0`** (DECISIONS §162 (2), supervisor 0143 C4 (b)): from
`lwMoment_holds` (`lem:LW_moment`) for the B class at the window `ε₁` of `lwMEA_assm`: `𝔼|f|^p ≺ (η⁻¹ Φ_B(0) Φ_B(c|a-b|))^p`, `p = 2q'`;
on `regA`, `Φ_B(c r)² ≤ C_c e^{√(K (log W)^{3/2})} 𝖳_t(r ∧ ℓ)²` (`lwMEA_phiB_sq_le`, `C_c = (2/(c∧1))^{d-2}(1 + 2^{d-1})`) and the loss
`(C_c e^{√(K (log W)^{3/2})})^{q'} ≤ N^σ` for every `σ` (`lwMEA_loss`).  `Φ_B(0) = B_{ctl}^{1/2}` (`lwMEA_phi_zero`). -/
theorem lwMomExpNoExp_holds : ∀ (d : ℕ) (K : ℝ), 0 < K → LWMomExpNoExpF d K := by
  intro d K hK hd κ ε 𝔡 hκ hε h𝔡 p hp2 𝔠 sz z hflow t ht0 htT ε₀ Ψ ℓ hA D hD
  obtain ⟨q', hq'⟩ := hp2
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hsize := tendsto_size sz hsz
  have him : ∀ n, 0 < (z n).im := lwMEA_flow_im_pos sz hflow
  have ht1 : ∀ n, t n < 1 := fun n => lt_of_le_of_lt (htT n) (lemT_lt_one (him n))
  have hℓ0 : ∀ n, 0 ≤ ℓ n := hA.2.2.2.1
  obtain ⟨ε₁, hε₁, hassm⟩ := lwMEA_assm hd hκ hε h𝔡 sz hflow ht0 htT hA
  obtain ⟨c, hc, H⟩ := lwMoment_holds d hd κ ε 𝔡 hκ hε h𝔡 p ⟨q', hq'⟩ ε₁ ((2 : ℝ) ^ d) (d : ℝ)
    (Real.sqrt (1 + (𝔡⁻¹) ^ 2)) (fun C => Real.sqrt ((C + 1) ^ (d - 2)))
  have hmain := H 𝔠 sz z hflow t ht0 htT Ψ _ hassm
  have h1 := StochDomAt.precomp_param hmain
    (fun n (v : {q : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) //
      sz.lam n ^ 2 / ((sz.L n : ℕ) : ℝ) ^ 2 < 1 - t n ∧ regA d K sz n (t n) (ℓ n) q}) => v.1)
  refine lwMEA_prec_mono ?_ h1
  intro σ hσ
  have hloss := lwMEA_loss sz (by omega) h𝔠 hsz hband hK q' (C := (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1))) hσ
  filter_upwards [hloss, hsize.eventually_ge_atTop 1] with n hl hN1
  rintro ⟨q, hq1, hq2⟩ ω
  dsimp only
  subst hq'
  set W : ℝ := ((sz.W n : ℕ) : ℝ) with hWdef
  have hW0 : 0 < W := Nat.cast_pos.2 (sz.W_pos n)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.one_le_cast.2 (by have := sz.three_le_L n; omega)
  set r : ℕ := zdistInf d (sz.L n) (STblk sz n q.1 - STblk sz n q.2) with hr
  have hrL : r ≤ sz.L n := lwMEA_zdistInf_le _ _
  set m : ℝ := min (r : ℝ) (ℓ n) with hm
  set s : ℝ := Real.sqrt (m / ellT (sz.L n) (sz.lam n) (t n)) with hs
  set Xn : ℝ := Real.sqrt (K * Real.log W ^ (3 / 2 : ℝ)) with hXn
  have hsX : s ≤ Xn := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_iff₀ (ellT_pos hL1)]
    rcases hq2 with h | h
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
  have h2 := lwMEA_phiB_sq_le (d := d) (L := sz.L n) (W := W) (g := sz.lam n) (t := t n) (ℓ := ℓ n) (c := c)
    (by omega) hL1 (ht1 n) hW0 hq1.le (hℓ0 n) hc hrL
  have hΦ2 : LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n (c * (r : ℝ)) ^ 2 ≤
      ((2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)) * Real.exp Xn) * sfT d (sz.L n) W (sz.lam n) (t n) m ^ 2 := by
    rw [lwMEA_phi_sq]
    calc _ ≤ _ := h2
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsX)
          (by positivity : (0 : ℝ) ≤ (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)))
  have hη : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ := inv_nonneg.mpr (lwN_etaT_nonneg _ _ (ht1 n).le)
  have hB0 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by unfold Sizes.Bctl Bparam; positivity) _
  have hsf : 0 ≤ sfT d (sz.L n) W (sz.lam n) (t n) m := sfT_nonneg _
  have hY : 0 ≤ (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) * sfT d (sz.L n) W (sz.lam n) (t n) m :=
    mul_nonneg (mul_nonneg hη hB0) hsf
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW0.le _
  refine ⟨add_nonneg (pow_nonneg hY _) hWD, ?_⟩
  rw [lwMEA_phi_zero]
  set x : ℝ := (etaT (STflowE z n) (t n))⁻¹ * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) with hx
  set Φ : ℝ := LWPhiB sz (d : ℝ) (fun n => min ⌊ℓ n⌋₊ (sz.L n)) t n (c * (r : ℝ)) with hΦ
  set C : ℝ := (2 / min c 1) ^ (d - 2) * (1 + 2 ^ (d - 1)) * Real.exp Xn with hC
  have hx0 : 0 ≤ x := mul_nonneg hη hB0
  calc (x * Φ) ^ (2 * q') = x ^ (2 * q') * (Φ ^ 2) ^ q' := by rw [mul_pow, pow_mul Φ 2 q']
    _ ≤ x ^ (2 * q') * (C * sfT d (sz.L n) W (sz.lam n) (t n) m ^ 2) ^ q' :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) hΦ2 q') (by positivity)
    _ = C ^ q' * (x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') := by
        rw [mul_pow C, ← pow_mul (sfT d (sz.L n) W (sz.lam n) (t n) m) 2 q', mul_pow x _ (2 * q')]
        ring
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ σ * (x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') :=
        mul_le_mul_of_nonneg_right hl (pow_nonneg (mul_nonneg hx0 hsf) _)
    _ ≤ ((sz.size n : ℕ) : ℝ) ^ σ * ((x * sfT d (sz.L n) W (sz.lam n) (t n) m) ^ (2 * q') + W ^ (-D)) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hWD) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-! ## 5. Compiled nonempty instances at `d = 3`

The merged preflight data (`sz0`: `L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `lam_n = (2(n+1))^{-6}`; `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`; `z0`, `flow_z0`;
`t ≡ 1/16`; `ε₀ = 1/20`, `Ψ0 = W^{-1}`, `ℓ_n = ℓ_t`, `LWAssmExp` from `assmExp_of`).  The subtype is nonempty at every `n`
(`λ²/L² < 1 - t` by `strict_all`; `regA` holds for the diagonal pairs `(x, x)`: `|a - a|_∞ = 0`).  What stays a hypothesis is
another gate's stochastic input: `LWInit` and `LWLoopExp` (`(initialGT2)`, `(LW_assm_exp)`). -/

section Instances

open RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.LWInst

/-- The index set of (A) at `K > 0` is nonempty at every size (the diagonal pair). -/
example (K : ℝ) (hK : 0 < K) (n : ℕ) :
    Nonempty {q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
      sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n ∧ regA 3 K sz0 n (tInst n) (ℓT tInst n) q} := by
  refine ⟨⟨(0, 0), strict_all n, Or.inl ?_⟩⟩
  simp only [sub_self, lwMEA_zdistInf_zero, Nat.cast_zero]
  have h1 := Real.log_nonneg (one_le_W n)
  have h2 : 0 ≤ ellT (sz0.L n) (sz0.lam n) (tInst n) := ellT_nonneg
  positivity

/-- **Instance of `lwMomExpNoExp_holds`** (`d = 3`, `p = 2`, `K = 6`, merged `sz0`, `t ≡ 1/16`, every `D > 0`): `LWInit` and `LWLoopExp`
stay hypotheses, every deterministic hypothesis is discharged. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst))
    (D : ℝ) (hD : 0 < D) :
    sz0.Prec (U := fun n => {q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n ∧ regA 3 6 sz0 n (tInst n) (ℓT tInst n) q})
      (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1.1 q.1.2‖ ^ 2 ∂(sz0.seqP))
      (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n)
          (min ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1.1 - STblk sz0 n q.1.2) : ℕ) : ℝ) (ℓT tInst n))) ^ 2 +
        ((sz0.W n : ℕ) : ℝ) ^ (-D)) :=
  lwMomExpNoExp_holds 3 6 (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    2 (dvd_refl 2) (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst)
    (assmExp_of hI hL) D hD

/-- **Instance of `lwMomExpNoExp_holds`** at another scale and moment, `p = 4`, `K = 1/2`. -/
example (hI : LWInit sz0 (STflowE z0) tInst (1 / 20) Ψ0) (hL : LWLoopExp sz0 (STflowE z0) tInst (ℓT tInst))
    (D : ℝ) (hD : 0 < D) :
    sz0.Prec (U := fun n => {q : Idx 3 (sz0.L n) (sz0.W n) × Idx 3 (sz0.L n) (sz0.W n) //
        sz0.lam n ^ 2 / ((sz0.L n : ℕ) : ℝ) ^ 2 < 1 - tInst n ∧ regA 3 (1 / 2) sz0 n (tInst n) (ℓT tInst n) q})
      (fun n q _ => ∫ ω, ‖LWf sz0 n (STflowE z0 n) (tInst n) ω q.1.1 q.1.2‖ ^ 4 ∂(sz0.seqP))
      (fun n q _ => ((etaT (STflowE z0 n) (tInst n))⁻¹ * (sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) *
        sfT 3 (sz0.L n) ((sz0.W n : ℕ) : ℝ) (sz0.lam n) (tInst n)
          (min ((zdistInf 3 (sz0.L n) (STblk sz0 n q.1.1 - STblk sz0 n q.1.2) : ℕ) : ℝ) (ℓT tInst n))) ^ 4 +
        ((sz0.W n : ℕ) : ℝ) ^ (-D)) :=
  lwMomExpNoExp_holds 3 (1 / 2) (by norm_num) le_rfl (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) 4 (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst tInst_range.1 tInst_range.2 (1 / 20) Ψ0 (ℓT tInst)
    (assmExp_of hI hL) D hD

end Instances

end RBM.Graph

end
