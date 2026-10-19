/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.IterationsA
import RBM3D.Induction.NQEndFlow
import RBM3D.Induction.KDecay
import RBM3D.Green.Pins
import RBM3D.Loop.KLFinal

/-!
# The step of Lemma 4.11 (`lem:iterations`) over the bootstrap bound `STXiBoot'`

Paper: arXiv:2507.20274, Lemma 4.11 `lem:iterations` (proved in Subsection 4.5 `subsec:support`),
its case (ii) (4.48) `eq:psipara_smalletacase`, (4.49) `eq:iteration_improve_smalleta` in Subsection
4.2 `sec:1-s<L-2` (for which the paper omits the details), and the bootstrap bound (4.36)
`am;asoi222`.

## The bootstrap bound at the window start

The bootstrap bound `STXiBoot'` (`Induction/NQEndFlow.lean`) has, in the first summand of
`STbootRHS`, the window start `B_s = sz.Bctl n (s n)` in place of the endpoint value `B_u`.  The
lower bound `(cv A)⁻¹ ≤ B` of `IterationsAScale.Bctl` that the chain bound needs holds at
`w = s ∈ [s,t]` as well as at `w = u`.  Hence the step `iterationsB_step` takes `hboot : STXiBoot'`
and uses that lower bound at `w = s` (`iterationsA_boot_bound` accepts any `B_u ≥ (cv A)⁻¹`); the
rest of the proof is the iteration of `IterationsA.lean`.

## Contents

* §1 the private envelopes `iterationsB_XLv`, `iterationsB_XLKv`, `iterationsB_XL`,
  `iterationsB_XLK`, `iterationsB_rho` and the obligations `Ξ̂^{(𝓛)}_m ≺ iterationsB_XL`,
  `Ξ̂^{(𝓛-𝒦)}_m ≺ iterationsB_XLK` for `m ≤ N+1`, `m = 2N-1`, `m = 4p` and (for `Ξ̂^{(𝓛-𝒦)}`)
  `m + 1 ≤ N`; the public names they use are `iterationsA_*` and `st_*`;
* §2 **`iterationsB_step`**: the step of Lemma 4.11 over `STXiBoot'`;
* §3 the setting facts (private): `iterationsB_flowLam` ((2.10) `eq:WO` gives `0 < lam ≤ 𝔡⁻¹`),
  `iterationsB_K_pairs` (`stKbound_timeIcc` reindexed to the pairs), `iterationsB_setting` (all the
  hypotheses of the step except the scale facts `hS`, from the premises of `STIterR'`);
* §4 **`stIterations'_holds`**, **`stIterationsII'_holds`**: `STIterR'` in its two regimes, with
  `𝔠d = 1/100` (`≤ 1/16` and `≤ 1/24` for the scale facts `iterationsA_scale_I`,
  `iterationsA_scale_II`); `STXiBoot'` stays a hypothesis of these statements; their hypothesis
  `STKbound` is not used (the uniform `𝒦` bound is rebuilt by `stKbound_timeIcc`).

Every helper of this file other than `iterationsB_step` and the two statements of §4 is `private`
and prefixed `iterationsB_`.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

variable {d : ℕ} (sz : Sizes d)

/-! ## 1. The private envelopes and obligations of the step -/

/-- `Bctl ≥ 0`. -/
private theorem iterationsB_Bctl_nonneg (n : ℕ) (u : ℝ) : 0 ≤ sz.Bctl n u := by
  unfold Sizes.Bctl Bparam
  have hW : (0 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
  positivity


/-! ### The envelopes of the step (value level)

`iterationsB_XLv A ρ T cB cv N k p m` is the envelope of `Ξ̂^{(𝓛)}_m` chosen in the proof of
Lemma 4.11 (`Ξ^{(𝓛)}_m = 1 + T Ψ(m,l)`, `l = k` for `m+1 ≤ N`, `l = k-1` for `N ≤ m ≤ N+1`;
(4.69) `auskoppw2` for `m = 2N-1`; the a priori level `ρ^{4p-1}` for `m = 4p`) and
`iterationsB_XLKv` that of `Ξ̂^{(𝓛-𝒦)}_m` (`1` for `m = 1`, `Ψ(m,k)` above). -/

/-- The envelope of `Ξ̂^{(𝓛)}_m`. -/
private noncomputable def iterationsB_XLv (A ρ T cB cv : ℝ) (N k p m : ℕ) : ℝ :=
  if m ≤ N + 1 then
    1 + T * (if m = 1 then 1 else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1))
  else if m = 2 * N - 1 then
    1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2
  else if m = 4 * p then 1 + ρ ^ (4 * p - 1) else 1

/-- The envelope of `Ξ̂^{(𝓛-𝒦)}_m`. -/
private noncomputable def iterationsB_XLKv (A ρ : ℝ) (k m : ℕ) : ℝ :=
  1 + (if m = 1 then 0 else STPsi A ρ m k)

private theorem iterationsB_XLv_ge_one {A ρ T cB cv : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T) (hcB : 0 ≤ cB)
    (hcv : 0 ≤ cv) (N k p m : ℕ) : 1 ≤ iterationsB_XLv A ρ T cB cv N k p m := by
  have hP : ∀ j, 0 ≤ STPsi A ρ m j := fun j => iterationsA_STPsi_nonneg hA hρ m j
  unfold iterationsB_XLv
  split_ifs
  · have : 0 ≤ T * (1 : ℝ) := by positivity
    linarith
  · have := hP k
    have : 0 ≤ T * STPsi A ρ m k := by positivity
    linarith
  · have := hP (k - 1)
    have : 0 ≤ T * STPsi A ρ m (k - 1) := by positivity
    linarith
  · have : 0 ≤ cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
      have := Real.rpow_nonneg hA (1 - ((k - 1 : ℕ) : ℝ) / 8)
      positivity
    linarith
  · have : 0 ≤ ρ ^ (4 * p - 1) := by positivity
    linarith
  · exact le_rfl

/-- `(E1)`: `m ≤ N+1` gives `iterationsB_XLv ≤ 1 + T Ψ(m,k-1)`. -/
private theorem iterationsB_XLv_le_pred {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    {N k p m : ℕ} (hk : 1 ≤ k) (hmN : m ≤ N + 1) :
    iterationsB_XLv A ρ T cB cv N k p m ≤ 1 + T * STPsi A ρ m (k - 1) := by
  unfold iterationsB_XLv
  rw [ite_eq_left hmN]
  have h1 := iterationsA_one_le_STPsi hA hρ m (k - 1)
  have h2 := iterationsA_STPsi_anti_k hA hρ m hk
  have hP : 1 + T * (if m = 1 then 1 else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
      1 + T * STPsi A ρ m (k - 1) := by
    have : (if m = 1 then (1 : ℝ) else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
        STPsi A ρ m (k - 1) := by
      split_ifs
      · exact h1
      · exact h2
      · exact le_rfl
    gcongr
  exact hP

/-- `(E1')`: `m + 1 ≤ N` gives `iterationsB_XLv ≤ 1 + T Ψ(m,k)`. -/
private theorem iterationsB_XLv_le {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    {N k p m : ℕ} (hmN : m + 1 ≤ N) :
    iterationsB_XLv A ρ T cB cv N k p m ≤ 1 + T * STPsi A ρ m k := by
  unfold iterationsB_XLv
  rw [ite_eq_left (by omega : m ≤ N + 1)]
  have h1 := iterationsA_one_le_STPsi hA hρ m k
  have : (if m = 1 then (1 : ℝ) else if m + 1 ≤ N then STPsi A ρ m k else STPsi A ρ m (k - 1)) ≤
      STPsi A ρ m k := by
    split_ifs
    · exact h1
    · exact le_rfl
  gcongr

/-- `(E2)`: the envelope of `Ξ̂_{2N-1}`: `iterationsB_XLv ≤ 1 + cv A Z²`,
`Z = 1 + cB + T ρ^N A^{1-(k-1)/8}`
(equality for `N ≥ 3`; for `N = 2` it is `Ξ̂_3 ≤ 1 + T Ψ(3,k-1) ≤ Z ≤ 1 + cv A Z²`). -/
private theorem iterationsB_XLv_le_chain {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) (hT : 0 ≤ T)
    (hcB : 0 ≤ cB) (hcv : 1 ≤ cv) (hT1 : T * A ^ (3 / 4 : ℝ) ≤ cB) {N k p : ℕ} (hN : 2 ≤ N) :
    iterationsB_XLv A ρ T cB cv N k p (2 * N - 1) ≤
      1 + cv * A * ((1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
  have hA0 : 0 < A := by linarith
  set Z : ℝ := (1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) with hZ
  have hZ1 : 1 ≤ Z := by
    have := Real.rpow_nonneg hA0.le (1 - ((k - 1 : ℕ) : ℝ) / 8)
    have : 0 ≤ T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by positivity
    rw [hZ]; linarith
  by_cases h3 : 3 ≤ N
  · unfold iterationsB_XLv
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  · have hN2 : N = 2 := by omega
    subst hN2
    unfold iterationsB_XLv
    rw [ite_eq_left (by omega)]
    -- `Ξ̂_3 ≤ 1 + T Ψ(3,k-1) ≤ Z ≤ 1 + cv A Z²`
    have hm : ¬ (2 * 2 - 1 = 1) := by omega
    have hm' : ¬ (2 * 2 - 1 + 1 ≤ 2) := by omega
    rw [ite_eq_right hm, ite_eq_right hm']
    have hPk : STPsi A ρ (2 * 2 - 1) (k - 1) = A ^ (3 / 4 : ℝ) + ρ ^ 2 * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
      unfold STPsi; norm_num
    rw [hPk]
    have h1 : 1 + T * (A ^ (3 / 4 : ℝ) + ρ ^ 2 * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ≤ Z := by
      rw [hZ]; nlinarith
    have h2 : Z ≤ 1 + cv * A * Z ^ 2 := by
      have : 1 ≤ cv * A := by nlinarith
      have h3 : Z ≤ Z ^ 2 := by nlinarith
      have h4 : Z ^ 2 ≤ cv * A * Z ^ 2 := by nlinarith [sq_nonneg Z]
      linarith
    exact h1.trans h2

/-- `(E3)`: for `N + 1 < 4p`, `4p ≠ 2N - 1`: `XLv_{4p} = 1 + ρ^{4p-1}`. -/
private theorem iterationsB_XLv_four_p (A ρ T cB cv : ℝ) {N k p : ℕ} (h1 : N + 1 < 4 * p) (_h2 : 2 * N - 1 ≠ 4 * p) :
    iterationsB_XLv A ρ T cB cv N k p (4 * p) = 1 + ρ ^ (4 * p - 1) := by
  unfold iterationsB_XLv
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]

private theorem iterationsB_XLKv_ge_one {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (k m : ℕ) : 1 ≤ iterationsB_XLKv A ρ k m := by
  unfold iterationsB_XLKv
  have := iterationsA_STPsi_nonneg hA hρ m k
  split_ifs <;> linarith

private theorem iterationsB_XLKv_le {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) {k m : ℕ} :
    iterationsB_XLKv A ρ k m ≤ 1 + STPsi A ρ m k := by
  unfold iterationsB_XLKv
  have := iterationsA_one_le_STPsi hA hρ m k
  split_ifs <;> linarith


/-- `iterationsB_XLv ≤ Z` for `m ≤ N+1`, `Z = 1 + cB + T ρ^N A^{1-(k-1)/8}`. -/
private theorem iterationsB_XLv_le_Z {A ρ T cB cv : ℝ} (hA : 1 ≤ A) (hρ : 1 ≤ ρ) (hT : 0 ≤ T)
    (hT1 : T * A ^ (3 / 4 : ℝ) ≤ cB) {N k p m : ℕ} (hk : 1 ≤ k) (hmN : m ≤ N + 1) :
    iterationsB_XLv A ρ T cB cv N k p m ≤ (1 + cB) + T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
  have hA0 : 0 < A := by linarith
  have h1 := iterationsB_XLv_le_pred (cB := cB) (cv := cv) (p := p) hA (by linarith : 0 ≤ ρ) hT hk hmN
  refine h1.trans ?_
  unfold STPsi
  have hρN : ρ ^ (m - 1) ≤ ρ ^ N := pow_le_pow_right₀ hρ (by omega)
  have he : 0 ≤ A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := Real.rpow_nonneg hA0.le _
  have h2 : T * (ρ ^ (m - 1) * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ≤ T * ρ ^ N * A ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := by
    rw [mul_assoc]; gcongr
  nlinarith

/-- `Ξ̂^{(𝓛)}_m ≺ 1 + T Y` from (4.38) `rela_XILXILK` and `Ξ̂^{(𝓛-𝒦)}_m ≺ Y`: the transfer
`1 + B_v Ξ̂^{(𝓛-𝒦)} ≺ 1 + B_v Y ≤ 1 + T Y` for `W^{-d}B_{v,0} ≤ T`. -/
private theorem iterationsB_prec_XL_of (hsize : Tendsto sz.size atTop atTop) {E s t T : ℕ → ℝ} {m : ℕ}
    (hrela : sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    {Y : ∀ n, STPair s t n → ℝ} (hY0 : ∀ n q, 0 ≤ Y n q)
    (hG : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => Y n q))
    (hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n) (ht1 : ∀ n, t n < 1) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => 1 + T n * Y n q) := by
  have hGnn : ∀ n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiLK sz n (E n) q.1.1 m ω := fun n q ω => by
    have hu : q.1.1 < 1 := lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n)
    linarith [st_one_le_XiLK sz (n := n) (E := E n) (v := q.1.1) m ω (st_Bctl_pos sz (n := n) hu)]
  have hA := iterationsA_prec_one_add_mul sz hsize (U := STPair s t) (c := fun n q => sz.Bctl n q.1.1)
    (fun n q => iterationsB_Bctl_nonneg sz n _) hGnn hG
  have hB := StochDomAt.trans hsize hrela hA
  refine iterationsA_prec_mono_right sz hB ?_
  filter_upwards [hT] with n hn q ω
  have := hY0 n q
  have := hn q
  nlinarith [mul_le_mul_of_nonneg_right (hn q) (hY0 n q)]


/-- The envelope `ρ_u = max 1 (η_s/η_u)` (equal to `η_s/η_u` on the pairs, where it is `≥ 1`). -/
private noncomputable def iterationsB_rho (E s : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  max 1 (etaT (E n) (s n) / etaT (E n) u)

/-- The envelope of `Ξ̂^{(𝓛)}_m` at the size `n` and the endpoint `u`. -/
private noncomputable def iterationsB_XL (E s A T : ℕ → ℝ) (cB cv : ℝ) (N k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsB_XLv (A n) (iterationsB_rho E s n u) (T n) cB cv N k (N + 4) m

/-- The envelope of `Ξ̂^{(𝓛-𝒦)}_m`. -/
private noncomputable def iterationsB_XLK (E s A : ℕ → ℝ) (k m n : ℕ) (u : ℝ) : ℝ :=
  iterationsB_XLKv (A n) (iterationsB_rho E s n u) k m

private theorem iterationsB_rho_ge_one (E s : ℕ → ℝ) (n : ℕ) (u : ℝ) : 1 ≤ iterationsB_rho E s n u :=
  le_max_left _ _

private theorem iterationsB_rho_eq {E s : ℕ → ℝ} {n : ℕ} {u : ℝ} (h : 1 ≤ etaT (E n) (s n) / etaT (E n) u) :
    iterationsB_rho E s n u = etaT (E n) (s n) / etaT (E n) u := max_eq_right h

/-- **The obligations for `m ≤ N+1`**: `Ξ̂^{(𝓛)}_m ≺ 1 + T Y_m` with `Y_1 = 1`, `Y_m = Ψ(m,k)` for `m + 1 ≤ N`
((4.41) `eq:iteration_induc` at `(m,k)`), `Y_m = Ψ(m,k-1)` for `N ≤ m ≤ N+1` (at `(m,k-1)`). -/
private theorem iterationsB_obl_short (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1))
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ N + 1) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsB_XL E s A T cB cv N k m n q.1.2) := by
  set Y : ∀ n, STPair s t n → ℝ := fun n q =>
    if m = 1 then 1 else if m + 1 ≤ N then STPsi (A n) (iterationsB_rho E s n q.1.2) m k
    else STPsi (A n) (iterationsB_rho E s n q.1.2) m (k - 1) with hY
  have hY0 : ∀ n q, 0 ≤ Y n q := by
    intro n q
    have hρ0 : 0 ≤ iterationsB_rho E s n q.1.2 := by linarith [iterationsB_rho_ge_one E s n q.1.2]
    simp only [hY]
    split_ifs
    · norm_num
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
    · exact iterationsA_STPsi_nonneg (hS.A_nonneg n) hρ0 _ _
  have hG : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω) (fun n q _ => Y n q) := by
    by_cases hm : m = 1
    · subst hm
      refine iterationsA_prec_mono_right sz havg ?_
      exact Eventually.of_forall fun n q ω => by simp [hY]
    · have hm2' : 2 ≤ m := by omega
      by_cases hmN : m + 1 ≤ N
      · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
            (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m k) := IH1 m hm2' hmN
        refine iterationsA_prec_mono_right sz h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_true, ite_false]
        rw [iterationsB_rho_eq this]
      · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
            (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m (k - 1)) := IH2 m hm2' (by omega)
        refine iterationsA_prec_mono_right sz h ?_
        filter_upwards [hS.rho] with n hn q ω
        have := (hn q).1
        simp only [hY, hm, hmN, ite_false]
        rw [iterationsB_rho_eq this]
  have hT : ∀ᶠ n in atTop, ∀ q : STPair s t n, sz.Bctl n q.1.1 ≤ T n := by
    filter_upwards [hS.Bctl] with n hn q
    exact (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).2
  have hmain := iterationsB_prec_XL_of sz hsize (hrela m hm1) hY0 hG hT hS.t_lt_one
  refine iterationsA_prec_mono_right sz hmain (Eventually.of_forall fun n q ω => le_of_eq ?_)
  unfold iterationsB_XL iterationsB_XLv
  rw [ite_eq_left hm2]

/-- The `≺` of `1 + c ((F₁F₂)(F₂F₃))^{1/2}` from `F_i ≺ X_i` (the four loops `2l₁, 2l₂, 2l₃ = 2l₂, 2l₄` of (4.69) `auskoppw2`). -/
private theorem iterationsB_prec_chain_abs (hsize : Tendsto sz.size atTop atTop) {U : ℕ → Type*}
    {F1 F2 F3 X1 X2 X3 : ∀ n, U n → sz.SeqΩ → ℝ} {c : ∀ n, U n → ℝ} (hc : ∀ n u, 0 ≤ c n u)
    (hF1 : ∀ n u ω, 0 ≤ F1 n u ω) (hF2 : ∀ n u ω, 0 ≤ F2 n u ω) (hF3 : ∀ n u ω, 0 ≤ F3 n u ω)
    (hX1 : ∀ n u ω, 0 ≤ X1 n u ω) (hX2 : ∀ n u ω, 0 ≤ X2 n u ω) (hX3 : ∀ n u ω, 0 ≤ X3 n u ω)
    (h1 : sz.Prec F1 X1) (h2 : sz.Prec F2 X2) (h3 : sz.Prec F3 X3) :
    sz.Prec (fun n u ω => 1 + c n u * ((F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω)) ^ (1 / 2 : ℝ))
      (fun n u ω => 1 + c n u * ((X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) ^ (1 / 2 : ℝ)) := by
  have h12 : sz.Prec (fun n u ω => F1 n u ω * F2 n u ω) (fun n u ω => X1 n u ω * X2 n u ω) :=
    StochDomAt.mul (ξ₁ := F1) (ξ₂ := F2) (ζ₁ := X1) (ζ₂ := X2) hsize hF2 hX1 h1 h2
  have h23 : sz.Prec (fun n u ω => F2 n u ω * F3 n u ω) (fun n u ω => X2 n u ω * X3 n u ω) :=
    StochDomAt.mul (ξ₁ := F2) (ξ₂ := F3) (ζ₁ := X2) (ζ₂ := X3) hsize hF3 hX2 h2 h3
  have hP : sz.Prec (fun n u ω => (F1 n u ω * F2 n u ω) * (F2 n u ω * F3 n u ω))
      (fun n u ω => (X1 n u ω * X2 n u ω) * (X2 n u ω * X3 n u ω)) :=
    StochDomAt.mul (ξ₁ := fun n u ω => F1 n u ω * F2 n u ω) (ξ₂ := fun n u ω => F2 n u ω * F3 n u ω)
      (ζ₁ := fun n u ω => X1 n u ω * X2 n u ω) (ζ₂ := fun n u ω => X2 n u ω * X3 n u ω) hsize
      (fun n u ω => mul_nonneg (hF2 n u ω) (hF3 n u ω)) (fun n u ω => mul_nonneg (hX1 n u ω) (hX2 n u ω)) h12 h23
  have hsq := iterationsA_prec_rpow sz
    (fun n u ω => mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω)) (mul_nonneg (hF2 n u ω) (hF3 n u ω)))
    (fun n u ω => mul_nonneg (mul_nonneg (hX1 n u ω) (hX2 n u ω)) (mul_nonneg (hX2 n u ω) (hX3 n u ω)))
    (θ := 1 / 2) (by norm_num) hP
  exact iterationsA_prec_one_add_mul sz hsize hc
    (fun n u ω => Real.rpow_nonneg (mul_nonneg (mul_nonneg (hF1 n u ω) (hF2 n u ω))
      (mul_nonneg (hF2 n u ω) (hF3 n u ω))) _) hsq

/-- `((x₁x₂)(x₂x₃))^{1/2} ≤ Z²` for `0 ≤ x_i ≤ Z`. -/
private theorem iterationsB_sqrt_prod_le {x1 x2 x3 Z : ℝ} (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3)
    (a1 : x1 ≤ Z) (a2 : x2 ≤ Z) (a3 : x3 ≤ Z) : ((x1 * x2) * (x2 * x3)) ^ (1 / 2 : ℝ) ≤ Z ^ 2 := by
  have hZ : 0 ≤ Z := h1.trans a1
  rw [← Real.sqrt_eq_rpow, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e12 : x1 * x2 ≤ Z * Z := mul_le_mul a1 a2 h2 hZ
  have e23 : x2 * x3 ≤ Z * Z := mul_le_mul a2 a3 h3 hZ
  calc (x1 * x2) * (x2 * x3) ≤ (Z * Z) * (Z * Z) := mul_le_mul e12 e23 (mul_nonneg h2 h3) (by positivity)
    _ = (Z ^ 2) ^ 2 := by ring

/-- **The obligation for `m = 2N-1`, `N ≥ 3`** ((4.69) `auskoppw2`): `Ξ̂^{(𝓛)}_{2N-1} ≺ 1 + cv A Z²`, from the
odd chain bound `iterationsA_xiL_odd_le` and the envelopes of the four loops `Ξ̂_{2l_i}`, `2 l_i ≤ N+1`. -/
private theorem iterationsB_obl_chain (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ} (hN3 : 3 ≤ N)
    (hk : 1 ≤ k)
    (hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsB_XL E s A T cB cv N k m n q.1.2)) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 (2 * N - 1) ω)
      (fun n q _ => iterationsB_XL E s A T cB cv N k (2 * N - 1) n q.1.2) := by
  have ht1 := hS.t_lt_one
  have hBpos : ∀ n (q : STPair s t n), 0 < sz.Bctl n q.1.1 := fun n q =>
    st_Bctl_pos sz (n := n) (lt_of_le_of_lt (q.2.2.1.trans q.2.2.2) (ht1 n))
  have hFge : ∀ m n (q : STPair s t n) (ω : sz.SeqΩ), 0 ≤ STXiL sz n (E n) q.1.1 m ω := fun m n q ω => by
    linarith [st_one_le_XiL sz (n := n) (E := E n) (v := q.1.1) m ω (hBpos n q)]
  have hXge : ∀ m n (q : STPair s t n), 1 ≤ iterationsB_XL E s A T cB cv N k m n q.1.2 := fun m n q =>
    iterationsB_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rho_ge_one E s n q.1.2]) (hS.T_nonneg n)
      hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m
  have hone := iterationsB_prec_chain_abs sz hsize (U := STPair s t) (c := fun n _ => cv * A n)
    (fun n _ => by have := hS.A_nonneg n; have := hS.one_le_cv; positivity)
    (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω) (fun n q ω => hFge _ n q ω)
    (fun n q _ => by linarith [hXge (2 * ((N + 1) / 2)) n q]) (fun n q _ => by linarith [hXge (2 * (N / 2)) n q])
    (fun n q _ => by linarith [hXge (2 * ((N - 1) / 2)) n q])
    (hshort (2 * ((N + 1) / 2)) (by omega) (by omega)) (hshort (2 * (N / 2)) (by omega) (by omega))
    (hshort (2 * ((N - 1) / 2)) (by omega) (by omega))
  -- the right side: `1 + cv A P^{1/2} ≤ iterationsB_XL (2N-1)`
  have hright : ∀ᶠ n in atTop, ∀ (q : STPair s t n) (ω : sz.SeqΩ),
      1 + cv * A n * (((iterationsB_XL E s A T cB cv N k (2 * ((N + 1) / 2)) n q.1.2 *
          iterationsB_XL E s A T cB cv N k (2 * (N / 2)) n q.1.2) *
        (iterationsB_XL E s A T cB cv N k (2 * (N / 2)) n q.1.2 *
          iterationsB_XL E s A T cB cv N k (2 * ((N - 1) / 2)) n q.1.2)) ^ (1 / 2 : ℝ)) ≤
        iterationsB_XL E s A T cB cv N k (2 * N - 1) n q.1.2 := by
    filter_upwards [hS.one_le_A, hS.TA] with n hAn hT1n q ω
    have hρ1 := iterationsB_rho_ge_one E s n q.1.2
    have hXZ : ∀ m, 1 ≤ m → m ≤ N + 1 → iterationsB_XL E s A T cB cv N k m n q.1.2 ≤
        (1 + cB) + T n * iterationsB_rho E s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8) := fun m hm1 hm2 =>
      iterationsB_XLv_le_Z hAn hρ1 (hS.T_nonneg n) hT1n hk hm2
    have hsqrt := iterationsB_sqrt_prod_le (by linarith [hXge (2 * ((N + 1) / 2)) n q])
      (by linarith [hXge (2 * (N / 2)) n q]) (by linarith [hXge (2 * ((N - 1) / 2)) n q])
      (hXZ (2 * ((N + 1) / 2)) (by omega) (by omega)) (hXZ (2 * (N / 2)) (by omega) (by omega))
      (hXZ (2 * ((N - 1) / 2)) (by omega) (by omega))
    have hcvA : 0 ≤ cv * A n := by have := hS.A_nonneg n; have := hS.one_le_cv; positivity
    calc _ ≤ 1 + cv * A n * ((1 + cB) + T n * iterationsB_rho E s n q.1.2 ^ N * A n ^ (1 - ((k - 1 : ℕ) : ℝ) / 8)) ^ 2 := by
          gcongr
      _ = iterationsB_XL E s A T cB cv N k (2 * N - 1) n q.1.2 := by
          unfold iterationsB_XL iterationsB_XLv
          rw [ite_eq_right (by omega), ite_eq_left rfl]
  have hone' := iterationsA_prec_mono_right sz hone (Eventually.mono hright fun n hn q ω => hn q ω)
  -- the left side: `Ξ̂_{2N-1} ≤ 1 + cv A P^{1/2}`
  refine iterationsA_prec_mono_left sz ?_ hone'
  filter_upwards [hS.Bctl, hS.one_le_A] with n hn hAn q ω
  have hB0 := hBpos n q
  have hlow : (sz.Bctl n q.1.1)⁻¹ ≤ cv * A n := by
    have := (hn ⟨q.1.1, q.2.1, q.2.2.1.trans q.2.2.2⟩).1
    have hcvA : 0 < cv * A n := by have := hS.one_le_cv; positivity
    exact inv_le_of_inv_le₀ hcvA this
  refine (iterationsA_xiL_odd_le sz n (E := E n) (v := q.1.1) ω hB0 hN3).trans ?_
  have hP0 := Real.rpow_nonneg (mul_nonneg (mul_nonneg (hFge (2 * ((N + 1) / 2)) n q ω) (hFge (2 * (N / 2)) n q ω))
    (mul_nonneg (hFge (2 * (N / 2)) n q ω) (hFge (2 * ((N - 1) / 2)) n q ω))) (1 / 2 : ℝ)
  gcongr


/-- **The obligation for `Ξ̂^{(𝓛)}_{4p}`**: the a priori level `ρ^{4p-1}` ((4.39) `sef8w483r324`), `p = N + 4`
(so that `4p > N + 1` and `4p ≠ 2N - 1`). -/
private theorem iterationsB_obl_four_p {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1))) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 (4 * (N + 4)) ω)
      (fun n q _ => iterationsB_XL E s A T cB cv N k (4 * (N + 4)) n q.1.2) := by
  refine iterationsA_prec_mono_right sz (hapri (4 * (N + 4)) (by omega)) ?_
  filter_upwards [hS.rho] with n hn q ω
  have hρ1 := (hn q).1
  unfold iterationsB_XL
  rw [iterationsB_XLv_four_p _ _ _ _ _ (by omega) (by omega), iterationsB_rho_eq hρ1]
  have : 0 ≤ (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (4 * (N + 4) - 1) := by positivity
  linarith

/-- **The obligations for `Ξ̂^{(𝓛-𝒦)}_m`, `m + 1 ≤ N`**: `m = 1` is the averaged law, `m ≥ 2` is (4.41) `eq:iteration_induc` at `(m,k)`. -/
private theorem iterationsB_obl_K {E s t A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : IterationsAScale sz E s t A T cB cv K) {N k : ℕ}
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m + 1 ≤ N) :
    sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
      (fun n q _ => iterationsB_XLK E s A k m n q.1.2) := by
  by_cases hm : m = 1
  · subst hm
    refine iterationsA_prec_mono_right sz havg ?_
    exact Eventually.of_forall fun n q ω => by simp [iterationsB_XLK, iterationsB_XLKv]
  · have h : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 m ω)
        (fun n q _ => STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) m k) := IH1 m (by omega) hm2
    refine iterationsA_prec_mono_right sz h ?_
    filter_upwards [hS.rho] with n hn q ω
    have hρ1 := (hn q).1
    have hP := iterationsA_STPsi_nonneg (hS.A_nonneg n) (by linarith : 0 ≤ etaT (E n) (s n) / etaT (E n) q.1.2) m k
    unfold iterationsB_XLK iterationsB_XLKv
    rw [iterationsB_rho_eq hρ1, ite_eq_right hm]
    linarith



/-! ## 2. The step of Lemma 4.11 over `STXiBoot'` -/

/-- **The step of Lemma 4.11 `lem:iterations` over `STXiBoot'`**: if `STIterHyp` ((4.41) `eq:iteration_induc`) holds at
`(r,k)` for `2 ≤ r ≤ N-1` and at `(r,k-1)` for `2 ≤ r ≤ N+2`, it holds at `(N,k)`.  The other hypotheses are the scale facts `hS`,
the bootstrap bound `hboot : STXiBoot'` (the first summand of `STbootRHS` at `B_s = sz.Bctl n (s n)`), (4.38) `rela_XILXILK`,
the averaged law and the a priori bound (4.39) on the pairs.  The lower bound `(cv A)⁻¹ ≤ B` of `IterationsAScale.Bctl` is
taken at `w = s ∈ [s,t]`. -/
theorem iterationsB_step (hsize : Tendsto sz.size atTop atTop)
    {E s t A T : ℕ → ℝ} {cB cv K : ℝ} (hS : IterationsAScale sz E s t A T cB cv K)
    (hboot : STXiBoot' sz E s t)
    (hrela : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q ω => 1 + sz.Bctl n q.1.1 * STXiLK sz n (E n) q.1.1 m ω))
    (havg : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 1 ω) (fun _ _ _ => 1))
    (hapri : ∀ m, 1 ≤ m → sz.Prec (U := STPair s t) (fun n q ω => STXiL sz n (E n) q.1.1 m ω)
      (fun n q _ => (etaT (E n) (s n) / etaT (E n) q.1.2) ^ (m - 1)))
    {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz E s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz E s t A r (k - 1)) :
    STIterHyp sz E s t A N k := by
  have hshort : ∀ m, 1 ≤ m → m ≤ N + 1 → sz.Prec (U := STPair s t)
      (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => iterationsB_XL E s A T cB cv N k m n q.1.2) :=
    fun m hm1 hm2 => iterationsB_obl_short sz hsize hS hrela havg IH1 IH2 hm1 hm2
  have hFobl : ∀ m, 1 ≤ m → STlenL N (N + 4) m → sz.Prec (U := STPair s t)
      (fun n q ω => STXiL sz n (E n) q.1.1 m ω) (fun n q _ => iterationsB_XL E s A T cB cv N k m n q.1.2) := by
    intro m hm1 hlen
    by_cases hmN : m ≤ N + 1
    · exact hshort m hm1 hmN
    · have h2 : m = 2 * N - 1 ∨ m = 4 * (N + 4) := by unfold STlenL at hlen; omega
      rcases h2 with h | h
      · subst h
        exact iterationsB_obl_chain sz hsize hS (by omega) hk hshort
      · subst h
        exact iterationsB_obl_four_p sz hS hapri
  have hbootN := hboot N (N + 4) hN (by omega) (fun m n u => iterationsB_XL E s A T cB cv N k m n u)
    (fun m n u => iterationsB_XLK E s A k m n u)
    (fun m n u => iterationsB_XLv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rho_ge_one E s n u])
      (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
    (fun m n u => iterationsB_XLKv_ge_one (hS.A_nonneg n) (by linarith [iterationsB_rho_ge_one E s n u]) k m)
    hFobl (fun m hm1 hm2 => iterationsB_obl_K sz hS havg IH1 hm1 hm2)
  obtain ⟨C, hCpos, hC⟩ := iterationsA_boot_bound cB cv K hS.cB_nonneg hS.one_le_cv hS.one_le_K N k hN hk
  have hmain : sz.Prec (U := STPair s t) (fun n q ω => STXiLK sz n (E n) q.1.1 N ω)
      (fun n q _ => C * STPsi (A n) (etaT (E n) (s n) / etaT (E n) q.1.2) N k) := by
    refine iterationsA_prec_mono_right sz hbootN ?_
    filter_upwards [hS.one_le_A, hS.rho, hS.TA, hS.Bctl] with n hAn hρn hTAn hBn q ω
    have hρ1 := (hρn q).1
    have hρeq := iterationsB_rho_eq hρ1
    have hρ1' := iterationsB_rho_ge_one E s n q.1.2
    have hρ0 : 0 ≤ iterationsB_rho E s n q.1.2 := by linarith
    -- the lower bound of `IterationsAScale.Bctl` at `w = s ∈ [s,t]` (`s ≤ v ≤ u ≤ t` on a pair)
    have hlow := (hBn ⟨s n, le_rfl, q.2.1.trans (q.2.2.1.trans q.2.2.2)⟩).1
    have hb := hC (A n) (iterationsB_rho E s n q.1.2) (T n) (sz.Bctl n (s n)) (N + 4)
      (fun m => iterationsB_XL E s A T cB cv N k m n q.1.2) (fun m => iterationsB_XLK E s A k m n q.1.2)
      (by omega) hAn hρ1' (by rw [hρeq]; exact (hρn q).2.1) (hS.T_nonneg n) hTAn
      (by rw [hρeq]; exact (hρn q).2.2) hlow
      (fun m hm1 hm2 => iterationsB_XLv_le_pred hAn hρ0 (hS.T_nonneg n) hk hm2)
      (fun m hm1 hm2 => iterationsB_XLv_le hAn hρ0 (hS.T_nonneg n) hm2)
      (fun m => iterationsB_XLv_ge_one (hS.A_nonneg n) hρ0 (hS.T_nonneg n) hS.cB_nonneg (by linarith [hS.one_le_cv]) N k (N + 4) m)
      (iterationsB_XLv_le_chain hAn hρ1' (hS.T_nonneg n) hS.cB_nonneg hS.one_le_cv hTAn hN)
      (iterationsB_XLv_four_p _ _ _ _ _ (by omega) (by omega)).le
      (fun m => iterationsB_XLKv_ge_one (hS.A_nonneg n) hρ0 k m)
      (fun m hm1 hm2 => iterationsB_XLKv_le hAn hρ0)
    rw [hρeq] at hb
    exact hb
  refine iterationsA_prec_absorb sz hsize ?_ hmain
  filter_upwards [hS.one_le_A, hS.rho] with n hAn hρn q ω
  exact iterationsA_STPsi_nonneg (by linarith) (by linarith [(hρn q).1]) N k

/-! ## 3. The setting facts (private) -/

/-- (2.10) `eq:WO` gives `0 < lam n ≤ 𝔡⁻¹` eventually (the statement of the private `KLFinal_flowLam` of `Loop/KLFinal.lean`). -/
private theorem iterationsB_flowLam {κ ε 𝔠 𝔡 : ℝ} {z : ℕ → ℂ} (hz : STFlow sz κ ε 𝔠 𝔡 z) :
    ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
  filter_upwards [hz.1.2.2.2.2] with n hn
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩

/-- The `𝒦`-loop bound (2.58) `eq:bcal_k` uniformly in the pairs `(v,u)` and the labels (the hypothesis `hK` of
`iterationsA_rela_of_K`): `stKbound_timeIcc` (uniform in `u ∈ [s,t]`) reindexed along `(q, p) ↦ (⟨q.1.1, _⟩, p)`. -/
private theorem iterationsB_K_pairs (hd : 3 ≤ d) {E : ℕ → ℝ} {κ gmax : ℝ} (hκ : 0 < κ) (hg : 0 < gmax)
    (hN : sz.SizeTendsto) (hE : ∀ᶠ n in atTop, |E n| ≤ 2 - κ)
    (hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ gmax) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hst : ∀ n, s n ≤ t n) (ht1 : ∀ n, t n < 1) (m : ℕ) (hm : 1 ≤ m) :
    sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (E n) p.1.1.1 p.2.1 p.2.2‖) (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) :=
  by
  have h := stKbound_timeIcc sz hd hκ hg hN hE hlam hs0 hst ht1 m hm
  let φ : ∀ n, STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))) →
      TimeIcc s t n × (Fin m → Bool) × (Fin m → Zd d (sz.L n)) :=
    fun n p => (⟨p.1.1.1, p.1.2.1, p.1.2.2.1.trans p.1.2.2.2⟩, p.2)
  exact StochDomAt.precomp_param h φ

/-- **All the hypotheses of `iterationsB_step` from the premises of `STIterR'`** except the scale facts `hS`, which
are an argument depending on the derived facts `t_n < 1`, `|E_n| < 2`, (2.10) `eq:WO` (case (i) uses all three, case (ii) the
first two).  The flow supplies `Admissible`, `|E_n| < 2 - κ/2`, `t_n < 1` (`v3_premises_of_stFlow`); `STAvgU` is part of
`STStep2Concl`; the a priori bound is (2.85) `lRB1`; (4.38) `rela_XILXILK` comes from the uniform `𝒦` bound. -/
private theorem iterationsB_setting (hd : 3 ≤ d) {κ ε 𝔠 𝔡 Cd : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {z : ℕ → ℂ}
    (hflow : STFlow sz κ ε 𝔠 𝔡 z) {s t : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n) (hst : ∀ n, s n < t n)
    (htT : ∀ n, t n ≤ lemT (z n)) (hStep1 : STStep1Loop sz (STflowE z) s t)
    (hStep2 : STStep2Concl sz (STflowE z) s t Cd) {A T : ℕ → ℝ} {cB cv K : ℝ}
    (hS : (∀ n, t n < 1) → (∀ n, |STflowE z n| < 2) → sz.WO 𝔡 →
      IterationsAScale sz (STflowE z) s t A T cB cv K)
    (hboot : STXiBoot' sz (STflowE z) s t) {N k : ℕ} (hN : 2 ≤ N) (hk : 1 ≤ k)
    (IH1 : ∀ r, 2 ≤ r → r + 1 ≤ N → STIterHyp sz (STflowE z) s t A r k)
    (IH2 : ∀ r, 2 ≤ r → r ≤ N + 2 → STIterHyp sz (STflowE z) s t A r (k - 1)) :
    STIterHyp sz (STflowE z) s t A N k := by
  obtain ⟨hA, hE', ht1, -⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hE : ∀ n, |STflowE z n| < 2 := fun n => by linarith [hE' n]
  have hsize := tendsto_size sz hA.2.2.1
  have hK : ∀ m, 1 ≤ m → sz.Prec (U := fun n => STPair s t n × ((Fin m → Bool) × (Fin m → Zd d (sz.L n))))
      (fun n p _ => ‖STKloop sz n (STflowE z n) p.1.1.1 p.2.1 p.2.2‖)
      (fun n p _ => sz.Bctl n p.1.1.1 ^ (m - 1)) := fun m hm =>
    iterationsB_K_pairs sz hd (half_pos hκ) (inv_pos.2 hA.2.1) hA.2.2.1
      (Eventually.of_forall fun n => (hE' n).le) (iterationsB_flowLam sz hflow) hs0 (fun n => (hst n).le) ht1 m hm
  exact iterationsB_step sz hsize (hS ht1 hE hA.2.2.2.2) hboot
    (fun m hm => iterationsA_rela_of_K sz hsize ht1 m hm (hK m hm))
    (iterationsA_avg_of_STAvgU sz hsize ht1 hStep2.2.1) (iterationsA_apriori_of_lRB1 sz hsize ht1 hE hStep1)
    hN hk IH1 IH2

/-! ## 4. The statements `STIterations'`, `STIterationsII'` -/

/-- **Lemma 4.11 `lem:iterations`, case (i)**: `STIterations' d` for every `d`, with `𝔠d = 1/100`.  The bootstrap bound `STXiBoot'`
is a hypothesis of the statement; its hypothesis `STKbound` is not used (see `iterationsB_K_pairs`).
Scale facts: `iterationsA_scale_I` (`2 ≤ d`, `𝔠d ≤ 1/16`). -/
theorem stIterations'_holds : ∀ d : ℕ, STIterations' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT hreg _hK _hLK hcon hStep1 hStep2 hboot n_ k hn hk IH1 IH2
  exact iterationsB_setting sz hd hκ hε hflow hs0 hst htT hStep1 hStep2
    (fun ht1 hE hWO => iterationsA_scale_I sz (by omega) (by norm_num) (by norm_num) hreg hcon hWO ht1 hE)
    hboot hn hk IH1 IH2

/-- **Lemma 4.11 `lem:iterations`, case (ii)**: `STIterationsII' d` for every `d`, with `𝔠d = 1/100`.  Scale facts:
`iterationsA_scale_II` (`𝔠d ≤ 1/24`); the regime `STCaseII` is not consumed (it enters through `A = (W^{-d}B_{s,0})⁻¹`,
as in `iterationsA_scale_II`). -/
theorem stIterationsII'_holds : ∀ d : ℕ, STIterationsII' d := by
  intro d hd κ ε 𝔡 hκ hε h𝔡 Cd hCd
  refine ⟨1 / 100, by norm_num, le_rfl, ?_⟩
  intro 𝔠 sz z hflow s t hs0 hst htT _hreg _hK _hLK hcon hStep1 hStep2 hboot n_ k hn hk IH1 IH2
  exact iterationsB_setting sz hd hκ hε hflow hs0 hst htT hStep1 hStep2
    (fun ht1 hE _ => iterationsA_scale_II sz (by norm_num) (by norm_num) hcon ht1 hE)
    hboot hn hk IH1 IH2

end RBM.Gauss.Sizes
