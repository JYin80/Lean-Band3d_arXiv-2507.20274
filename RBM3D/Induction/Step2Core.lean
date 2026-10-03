/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Defs
import RBM3D.Induction.ScaleFacts

/-!
# ST2-02 (ticket T2071): the real-number core of Step 2 of `lem:main_ind`

Moved from the T2039 design probe (`git show 0362cbc:RBM3D/Probe/T2039Pins.lean`), sections 3-8
(probe lines 819-2127): the discrete Gronwall inequality and the stopped bootstrap (section 3),
the tail functions along the flow (section 4), the transfer between the single-time model and the
grid walk through the merged `transferLaw` (section 5), the engine of the self-improving estimate
and the closure arithmetic (section 6), the good event `STGoodAt` of one self-improving step and
`ST_good_engine` (section 8).  Paper: `paper/tex/3_5_Loop_Hierarchy.tex:493-577`.

Differences from the probe text: the namespace `RBM.Probe.T2039` of sections 3-7 is `RBM.Gauss.Sizes`
(as in section 8 of the probe), the `open ... RBM.Probe.T2039` of section 8 is dropped, and the probe
section 7 (`ST2_Bctl_pos`, `ST2_Bctl_mono`) is replaced by the merged `STBctl_pos`, `STBctl_mono`
(`Induction/ScaleFacts.lean`), so that the six lines using them are renamed.  Nothing else is changed.
The final section `Instances` (new, not from the probe) holds one compiled nonempty `example` per
theorem, at `d = 3` (`sz0`, `n = 100` for the size-dependent ones); in the `ST_good_engine` example
the pin `STNewKLKAt` and the good event `STGoodAt` stay hypotheses.
-/

set_option linter.style.longLine false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

/-! ## 3. Deterministic core of the Step 2 argument (real numbers only)

2.1 the discrete Grönwall inequality (`Gronwall_inequality`, `3_5:493`), 2.2 the stopped bootstrap
(`eq:def2_stopping`, `3_5:533`, and the closing paragraph `3_5:568`): the stopping index never fires
if the Grönwall bound stays strictly below the threshold, 2.3 the logarithmic time sum (the left
Riemann sum of `1/(1-u)`), which turns `exp(Δ Σ C/(1-u_j))` into `((1-s)/(1-u))^C`. -/

namespace RBM.Gauss.Sizes

section Real

theorem ST_one_le_prod {k : ℕ} {Δ : ℝ} {β : ℕ → ℝ} (hΔ : 0 ≤ Δ) (hβ : ∀ j, j < k → 0 ≤ β j) :
    1 ≤ ∏ j ∈ Finset.range k, (1 + Δ * β j) := by
  calc (1 : ℝ) = ∏ _j ∈ Finset.range k, (1 : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range k, (1 + Δ * β j) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le_one)
          (fun j hj => by nlinarith [mul_nonneg hΔ (hβ j (Finset.mem_range.mp hj))])

/-- **Discrete Grönwall** (`Gronwall_inequality`, `3_5:493`, on a grid with step `Δ ≥ 0`): if
`J_k ≤ α_k + Δ Σ_{j<k} β_j J_j` for `k ≤ m`, with `α` nondecreasing, `β, J ≥ 0`, then
`J_k ≤ α_k Π_{j<k} (1 + Δ β_j)` for `k ≤ m`. -/
theorem ST_gronwall {m : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) {α β J : ℕ → ℝ}
    (hα : MonotoneOn α (Set.Iic m)) (hβ : ∀ j, j < m → 0 ≤ β j)
    (h : ∀ k, k ≤ m → J k ≤ α k + Δ * ∑ j ∈ Finset.range k, β j * J j) :
    ∀ k, k ≤ m → J k ≤ α k * ∏ j ∈ Finset.range k, (1 + Δ * β j) := by
  -- `S_k = Δ Σ_{j<k} β_j J_j ≤ α_k (Π_{j<k} (1 + Δ β_j) - 1)`
  have hS : ∀ k, k ≤ m → Δ * ∑ j ∈ Finset.range k, β j * J j ≤
      α k * (∏ j ∈ Finset.range k, (1 + Δ * β j) - 1) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hJk := h k (by omega)
      have hprod1 : 1 ≤ ∏ j ∈ Finset.range k, (1 + Δ * β j) :=
        ST_one_le_prod hΔ (fun j hj => hβ j (by omega))
      have hb : 0 ≤ Δ * β k := mul_nonneg hΔ (hβ k (by omega))
      have hαk : α k ≤ α (k + 1) := hα (by simp only [Set.mem_Iic]; omega) hk (Nat.le_succ k)
      set P := ∏ j ∈ Finset.range k, (1 + Δ * β j) with hP
      set S := Δ * ∑ j ∈ Finset.range k, β j * J j with hSdef
      have key : Δ * ∑ j ∈ Finset.range (k + 1), β j * J j = S + Δ * β k * J k := by
        rw [Finset.sum_range_succ]; simp only [hSdef]; ring
      have e1 : Δ * β k * J k ≤ Δ * β k * (α k + S) :=
        mul_le_mul_of_nonneg_left hJk hb
      have e3 : Δ * β k * (α k + S) ≤ Δ * β k * (α k + α k * (P - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb
      have e4 : α k * (P - 1) + Δ * β k * (α k + α k * (P - 1)) = α k * (P * (1 + Δ * β k) - 1) := by
        ring
      have e5 : α k * (P * (1 + Δ * β k) - 1) ≤ α (k + 1) * (P * (1 + Δ * β k) - 1) :=
        mul_le_mul_of_nonneg_right hαk (by nlinarith [hprod1, hb])
      rw [key, Finset.prod_range_succ]
      linarith
  intro k hk
  have h1 := h k hk
  have h2 := hS k hk
  nlinarith

/-- **The stopped bootstrap** (`eq:def2_stopping`, `3_5:533`; the closing paragraph `3_5:568`):
`τ ≤ K` is the stopping index of a process `J` against the thresholds `θ` (a hit at `τ` if
`τ < K`; the absence of a hit before `τ` is not needed here, only in the derivation of `hineq`).  If the Grönwall inequality holds up to `τ` (`hineq`) and the Grönwall
bound stays strictly below the threshold (`hclose`: the paper's "`𝔠_d` chosen sufficiently small"),
then the process never hits (`τ = K`) and the Grönwall bound holds on the whole grid. -/
theorem ST_bootstrap {K τ : ℕ} {Δ : ℝ} (hΔ : 0 ≤ Δ) {α β J θ : ℕ → ℝ}
    (hα : MonotoneOn α (Set.Iic K)) (hβ : ∀ j, j < K → 0 ≤ β j) (hτK : τ ≤ K)
    (hhit : τ < K → θ τ ≤ J τ)
    (hineq : ∀ k, k ≤ K → k ≤ τ → J k ≤ α k + Δ * ∑ j ∈ Finset.range k, β j * J j)
    (hclose : ∀ k, k ≤ K → α k * ∏ j ∈ Finset.range k, (1 + Δ * β j) < θ k) :
    τ = K ∧ ∀ k, k ≤ K → J k ≤ α k * ∏ j ∈ Finset.range k, (1 + Δ * β j) := by
  have hG := ST_gronwall (m := τ) hΔ (hα.mono (Set.Iic_subset_Iic.mpr hτK))
    (fun j hj => hβ j (lt_of_lt_of_le hj hτK)) (fun k hk => hineq k (hk.trans hτK) hk)
  have hτ : τ = K := by
    by_contra hne
    have hlt : τ < K := lt_of_le_of_ne hτK hne
    have h1 := hhit hlt
    have h2 := hG τ le_rfl
    have h3 := hclose τ hτK
    linarith
  subst hτ
  exact ⟨rfl, hG⟩

/-- `Δ/(1-u_j) ≤ log((1-u_j)/(1-u_{j+1}))` for one grid step. -/
theorem ST_logstep {x Δ : ℝ} (hx : 0 < x) (hy : 0 < x - Δ) :
    Δ * x⁻¹ ≤ Real.log (x / (x - Δ)) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := x / (x - Δ)) (div_pos hx hy)
  have e : 1 - (x / (x - Δ))⁻¹ = Δ * x⁻¹ := by
    rw [inv_div]; field_simp; ring
  linarith

/-- **The logarithmic time sum** (the left Riemann sum of `1/(1-u)`, RBM2D `TimeSums`
`Path/TimeSums.lean`, here exact): on the grid `u_j = s + jΔ` with `u_k < 1`,
`Δ Σ_{j<k} (1-u_j)^{-1} ≤ log((1-s)/(1-u_k))`. -/
theorem ST_logsum {s Δ : ℝ} (hΔ : 0 ≤ Δ) : ∀ k : ℕ, s + k * Δ < 1 →
    Δ * ∑ j ∈ Finset.range k, (1 - (s + j * Δ))⁻¹ ≤ Real.log ((1 - s) / (1 - (s + k * Δ))) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : s + (k : ℝ) * Δ < 1 := by
      have : (k : ℝ) * Δ ≤ ((k + 1 : ℕ) : ℝ) * Δ := by
        push_cast; nlinarith
      push_cast at hk ⊢; linarith
    have hx : 0 < 1 - (s + (k : ℝ) * Δ) := by linarith
    have hy : 0 < (1 - (s + (k : ℝ) * Δ)) - Δ := by push_cast at hk; linarith
    have hstep := ST_logstep hx hy
    have e : (1 - (s + (k : ℝ) * Δ)) - Δ = 1 - (s + ((k + 1 : ℕ) : ℝ) * Δ) := by push_cast; ring
    rw [e] at hstep
    have hs : 0 < 1 - s := by nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hΔ]
    have hylog : Real.log ((1 - (s + (k : ℝ) * Δ)) / (1 - (s + ((k + 1 : ℕ) : ℝ) * Δ))) =
        Real.log (1 - (s + (k : ℝ) * Δ)) - Real.log (1 - (s + ((k + 1 : ℕ) : ℝ) * Δ)) := by
      rw [Real.log_div hx.ne' (by rw [← e]; exact hy.ne')]
    have hlog : Real.log ((1 - s) / (1 - (s + (k : ℝ) * Δ))) =
        Real.log (1 - s) - Real.log (1 - (s + (k : ℝ) * Δ)) := Real.log_div hs.ne' hx.ne'
    have hlog2 : Real.log ((1 - s) / (1 - (s + ((k + 1 : ℕ) : ℝ) * Δ))) =
        Real.log (1 - s) - Real.log (1 - (s + ((k + 1 : ℕ) : ℝ) * Δ)) :=
      Real.log_div hs.ne' (by rw [← e]; exact hy.ne')
    rw [Finset.sum_range_succ, mul_add, hlog2]
    have := ih hk'
    rw [hlog] at this
    rw [hylog] at hstep
    linarith

/-- `Π_{j<k} (1 + Δ c/(1-u_j)) ≤ ((1-s)/(1-u_k))^c`: the Grönwall factor of `3_5:481–509`
(`exp ∫ C_0/(1-u) du = ((1-s)/(1-u))^{C_0}`). -/
theorem ST_prod_le_rpow {s Δ c : ℝ} (hΔ : 0 ≤ Δ) (hc : 0 ≤ c) {k : ℕ} (hk : s + k * Δ < 1) :
    ∏ j ∈ Finset.range k, (1 + Δ * (c * (1 - (s + j * Δ))⁻¹)) ≤
      ((1 - s) / (1 - (s + k * Δ))) ^ c := by
  have hpos : ∀ j ∈ Finset.range k, 0 < 1 - (s + (j : ℝ) * Δ) := by
    intro j hj
    have hjk : (j : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hj).le
    nlinarith [mul_le_mul_of_nonneg_right hjk hΔ]
  have hx : ∀ j ∈ Finset.range k, 0 ≤ Δ * (c * (1 - (s + (j : ℝ) * Δ))⁻¹) := fun j hj =>
    mul_nonneg hΔ (mul_nonneg hc (inv_nonneg.mpr (hpos j hj).le))
  have hprod : ∏ j ∈ Finset.range k, (1 + Δ * (c * (1 - (s + (j : ℝ) * Δ))⁻¹)) ≤
      ∏ j ∈ Finset.range k, Real.exp (Δ * (c * (1 - (s + (j : ℝ) * Δ))⁻¹)) :=
    Finset.prod_le_prod₀ (fun j hj => by have := hx j hj; linarith)
      (fun j hj => by have := Real.add_one_le_exp (Δ * (c * (1 - (s + (j : ℝ) * Δ))⁻¹)); linarith)
  rw [← Real.exp_sum] at hprod
  have hsum : ∑ j ∈ Finset.range k, Δ * (c * (1 - (s + (j : ℝ) * Δ))⁻¹) =
      c * (Δ * ∑ j ∈ Finset.range k, (1 - (s + (j : ℝ) * Δ))⁻¹) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlog := ST_logsum hΔ k hk
  have hs : 0 < 1 - s := by nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hΔ]
  have hu : 0 < 1 - (s + (k : ℝ) * Δ) := by linarith
  have hr : 0 < (1 - s) / (1 - (s + (k : ℝ) * Δ)) := div_pos hs hu
  calc _ ≤ Real.exp (c * (Δ * ∑ j ∈ Finset.range k, (1 - (s + (j : ℝ) * Δ))⁻¹)) := by
        rw [← hsum]; exact hprod
    _ ≤ Real.exp (c * Real.log ((1 - s) / (1 - (s + (k : ℝ) * Δ)))) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog hc)
    _ = ((1 - s) / (1 - (s + (k : ℝ) * Δ))) ^ c := by
        rw [Real.rpow_def_of_pos hr, mul_comm]

/-- **The pathwise Grönwall inequality** (`3_5:548–560`, from `(LKu2p2mmvj)` and `(defCALJ)`): at a
fixed sample, for labels `i` (the pairs `(σ, a)`), `x_k i = |(𝓛-𝒦)^{(2)}_{u_k, i}|`, profile
`P_k i = W^{-d} 𝒯̃^{K_{u_k}}_{u_k,D}(|a|)` (positive, nondecreasing in `k`: `(eq:monotone_Ku)`) and
`Ĵ_k = max_i x_k i / P_k i`: if up to the stopping index `τ` the grid increments are
`x_k ≤ x_0 + Δ Σ_{j<k} dr_j + remk_k + mart_k` with
* the initial value `x_0 ≤ a₀ P_0` (`(Eq:Gdecay+IND)` at `s`),
* the drift `dr_j ≤ (β_j Ĵ_j + e_j) P_j` (`lem:newKLK` for the `Θ∘(𝓛-𝒦)` and `𝓔^{LK×LK}` terms,
  `lem: EWGn2_N` for `𝓔^{G̃}`), for `j < τ`,
* the accumulated remainder `remk_k ≤ r₀ P_0`, `k ≤ K`,
* the martingale `mart_k ≤ m_k P_k` for `k ≤ τ` (`lem:DIfREP`, `lem: EMn2_N`),
then `Ĵ_k ≤ α_k + Δ Σ_{j<k} β_j Ĵ_j` with `α_k = a₀ + r₀ + Δ Σ_{j<k} e_j + m_k`, for `k ≤ τ`. -/
theorem ST_pathwise_ineq {ι : Type*} {K τ : ℕ} {Δ a₀ r₀ : ℝ}
    {x dr mart P : ℕ → ι → ℝ} {remk : ℕ → ι → ℝ} {Jh β e m : ℕ → ℝ}
    (hΔ : 0 ≤ Δ) (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀)
    (hJh0 : ∀ j, j ≤ K → 0 ≤ Jh j)
    (hJhsup : ∀ k B, k ≤ K → (∀ i, x k i / P k i ≤ B) → Jh k ≤ B)
    (hP0 : ∀ j i, j ≤ K → 0 < P j i) (hPm : ∀ i, MonotoneOn (fun j => P j i) (Set.Iic K))
    (hβ : ∀ j, j < K → 0 ≤ β j) (he : ∀ j, j < K → 0 ≤ e j)
    (hdec : ∀ i k, k ≤ K → k ≤ τ →
      x k i ≤ x 0 i + Δ * ∑ j ∈ Finset.range k, dr j i + remk k i + mart k i)
    (H0 : ∀ i, x 0 i ≤ a₀ * P 0 i)
    (Hd : ∀ i j, j < τ → dr j i ≤ (β j * Jh j + e j) * P j i)
    (Hr : ∀ i k, k ≤ K → remk k i ≤ r₀ * P 0 i)
    (Hm : ∀ i k, k ≤ τ → mart k i ≤ m k * P k i) :
    ∀ k, k ≤ K → k ≤ τ →
      Jh k ≤ (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k) +
        Δ * ∑ j ∈ Finset.range k, β j * Jh j := by
  intro k hkK hkτ
  refine hJhsup k _ hkK fun i => ?_
  rw [div_le_iff₀ (hP0 k i hkK)]
  have hPk : ∀ j, j ≤ k → P j i ≤ P k i := fun j hj =>
    hPm i (by simp only [Set.mem_Iic]; omega) (by simp only [Set.mem_Iic]; exact hkK) hj
  have h1 : x 0 i ≤ a₀ * P k i :=
    (H0 i).trans (mul_le_mul_of_nonneg_left (hPk 0 (Nat.zero_le k)) ha₀)
  have h2 : ∑ j ∈ Finset.range k, dr j i ≤
      ∑ j ∈ Finset.range k, ((β j * Jh j + e j) * P k i) := by
    refine Finset.sum_le_sum fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hnn : 0 ≤ β j * Jh j + e j :=
      add_nonneg (mul_nonneg (hβ j (by omega)) (hJh0 j (by omega))) (he j (by omega))
    exact (Hd i j (lt_of_lt_of_le hjk hkτ)).trans
        (mul_le_mul_of_nonneg_left (hPk j hjk.le) hnn)
  have h3 : remk k i ≤ r₀ * P k i :=
    (Hr i k hkK).trans (mul_le_mul_of_nonneg_left (hPk 0 (Nat.zero_le k)) hr₀)
  have h4 := Hm i k hkτ
  have h5 : ∑ j ∈ Finset.range k, ((β j * Jh j + e j) * P k i) =
      (∑ j ∈ Finset.range k, β j * Jh j + ∑ j ∈ Finset.range k, e j) * P k i := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
  have h2' := mul_le_mul_of_nonneg_left h2 hΔ
  have := hdec i k hkK hkτ
  rw [h5] at h2'
  nlinarith [this, h1, h2', h3, h4]

/-- `α_k = a₀ + r₀ + Δ Σ_{j<k} e_j + m_k` is nondecreasing in `k` when `e ≥ 0` and `m` is
nondecreasing. -/
theorem ST_alpha_mono {K : ℕ} {Δ a₀ r₀ : ℝ} {e m : ℕ → ℝ} (hΔ : 0 ≤ Δ)
    (he : ∀ j, j < K → 0 ≤ e j) (hm : MonotoneOn m (Set.Iic K)) :
    MonotoneOn (fun k => a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k) (Set.Iic K) := by
  intro k hk l hl hkl
  have hs : ∑ j ∈ Finset.range k, e j ≤ ∑ j ∈ Finset.range l, e j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkl)
      (fun j hj _ => he j (lt_of_lt_of_le (Finset.mem_range.mp hj) (by simpa using hl)))
  have := mul_le_mul_of_nonneg_left hs hΔ
  have := hm hk hl hkl
  simp only
  linarith

end Real

end RBM.Gauss.Sizes
/-! ## 4. The tail functions along the flow and the scale families (`3_5:520–527`, `3_5:570–577`)

3.1 `𝒯_u(r)` is nondecreasing in `u`; 3.2 the monotonicity `(eq:monotone_Ku)` of the truncated
profile follows from that of `𝒯_u(K_u)`; 3.3 the scale step `𝒯_u(K') = 𝒯_u(K) Δ_u^{1/6}`
(`(eq:def_ell1)`): `e · 𝒯̃^K ≤ 𝒯̃^{K'}` and `𝒯̃^L ≤ 𝒯̃^{K'}` on the range `|a-b| ≤ L`;
3.4 the final scale: once `𝒯_u(K_u) ≤ W^{-D}`, `𝒯̃^{K_u}_{u,D} = max(𝒯_u, W^{-D})`. -/

namespace RBM.Gauss.Sizes

open RBM

section Tail

variable {d L : ℕ}

/-- `𝒯_u(r) ≤ 𝒯_v(r)` for `u ≤ v < 1`, `r ≥ 0`: both `B_{u,r}` and `ℓ_u` increase with `u`. -/
theorem ST_tailT_mono_time {g u v r : ℝ} (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g) (huv : u ≤ v)
    (hv : v < 1) (hr : 0 ≤ r) : tailT d L g u r ≤ tailT d L g v r := by
  have hv' : 0 < 1 - v := by linarith
  have hu' : 0 < 1 - u := by linarith
  unfold tailT BparamR
  rw [abs_of_pos hv', abs_of_pos hu']
  have hr1 : (0 : ℝ) < ((r + 1) ^ (d - 2)) := pow_pos (by linarith) _
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (by linarith) _
  have h1 : (g ^ 2 + (1 - u))⁻¹ ≤ (g ^ 2 + (1 - v))⁻¹ :=
    inv_anti₀ (by positivity) (by linarith)
  have h2 : ((L : ℝ) ^ d * (1 - u))⁻¹ ≤ ((L : ℝ) ^ d * (1 - v))⁻¹ :=
    inv_anti₀ (by positivity) (by nlinarith)
  have hB : (g ^ 2 + (1 - u))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - u))⁻¹ ≤
      (g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
    have := mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hr1.le)
    linarith
  have hℓ : ellT L g u ≤ ellT L g v := ellT_mono hg huv hv
  have hℓ0 : 0 < ellT L g u := ellT_pos hL
  have hexp : Real.exp (-Real.sqrt (r / ellT L g u)) ≤ Real.exp (-Real.sqrt (r / ellT L g v)) :=
    Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hr hℓ0 hℓ)))
  have hBv : 0 ≤ (g ^ 2 + (1 - v))⁻¹ * ((r + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - v))⁻¹ := by
    positivity
  exact mul_le_mul hB hexp (Real.exp_pos _).le hBv

/-- **`(eq:monotone_Ku)`** (`3_5:525–527`): if `𝒯_u(K_u) ≤ 𝒯_v(K_v)` for `u ≤ v < 1` (and
`K_u, K_v ≥ 0`), then `𝒯̃^{K_u}_{u,D}(r) ≤ 𝒯̃^{K_v}_{v,D}(r)` for every `r ≥ 0`. -/
theorem ST_tailW_mono_time {g u v Ku Kv W D r : ℝ} (hL : 1 ≤ (L : ℝ)) (hg : 0 ≤ g)
    (huv : u ≤ v) (hv : v < 1) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv) (hr : 0 ≤ r)
    (hK : tailT d L g u Ku ≤ tailT d L g v Kv) :
    tailW d L g u Ku W D r ≤ tailW d L g v Kv W D r := by
  unfold tailW
  refine max_le_max ?_ le_rfl
  have ha : 0 ≤ min r Ku := le_min hr hKu
  have hb : 0 ≤ min r Kv := le_min hr hKv
  have h1 : tailT d L g u (min r Ku) ≤ tailT d L g v (min r Ku) :=
    ST_tailT_mono_time hL hg huv hv ha
  by_cases hab : min r Kv ≤ min r Ku
  · exact h1.trans (tailT_antitone hb hab)
  · push Not at hab
    -- `min r Ku < min r Kv ≤ r`, so `min r Ku = Ku`
    have hKu' : min r Ku = Ku := by
      rcases min_choice r Ku with h | h
      · exfalso; rw [h] at hab; exact absurd (min_le_left r Kv) (not_le.mpr hab)
      · exact h
    rw [hKu']
    exact hK.trans (tailT_antitone hb (min_le_right r Kv))

/-- **The scale step** (`(eq:def_ell1)`, `3_5:570–575`): if `0 ≤ K ≤ K'`, `𝒯_u(K') = e 𝒯_u(K)` with
`0 ≤ e ≤ 1`, then `e 𝒯̃^{K}_{u,D}(ρ) ≤ 𝒯̃^{K'}_{u,D}(ρ)` for every `ρ ≥ 0` (here `e = Δ_u^{1/6}`:
the factor `Ĵ ≤ Δ_u^{1/6}` gained by one iteration is absorbed by the larger scale). -/
theorem ST_tailW_scale_step {g u K K' W D e ρ : ℝ} (hW : 0 ≤ W) (hK : 0 ≤ K) (hKK : K ≤ K')
    (he0 : 0 ≤ e) (he1 : e ≤ 1) (hT : e * tailT d L g u K ≤ tailT d L g u K') (hρ : 0 ≤ ρ) :
    e * tailW d L g u K W D ρ ≤ tailW d L g u K' W D ρ := by
  have hWD : 0 ≤ W ^ (-D) := Real.rpow_nonneg hW _
  have hK' : 0 ≤ K' := hK.trans hKK
  unfold tailW
  by_cases hρK : ρ ≤ K
  · rw [min_eq_left hρK, min_eq_left (hρK.trans hKK)]
    have : 0 ≤ max (tailT d L g u ρ) (W ^ (-D)) := hWD.trans (le_max_right _ _)
    nlinarith
  · push Not at hρK
    rw [min_eq_right hρK.le]
    have hb : 0 ≤ min ρ K' := le_min hρ hK'
    have h1 : tailT d L g u K' ≤ tailT d L g u (min ρ K') := tailT_antitone hb (min_le_right ρ K')
    rw [mul_max_of_nonneg _ _ he0]
    refine max_le (le_trans ?_ (le_max_left _ _)) (le_trans ?_ (le_max_right _ _))
    · exact hT.trans h1
    · nlinarith

/-- `𝒯̃^{L}_{u,D}(ρ) ≤ 𝒯̃^{ℓ}_{u,D}(ρ)` for `0 ≤ ρ ≤ L` and every `ℓ ≥ 0`: the full-range profile
is the smallest one (`3_5:518`, `(eq:simpleboundK)`). -/
theorem ST_tailW_L_le {g u ℓ W D ρ : ℝ} (hℓ : 0 ≤ ℓ) (hρ : 0 ≤ ρ) (hρL : ρ ≤ (L : ℝ)) :
    tailW d L g u (L : ℝ) W D ρ ≤ tailW d L g u ℓ W D ρ := by
  unfold tailW
  refine max_le_max ?_ le_rfl
  rw [min_eq_left hρL]
  exact tailT_antitone (le_min hρ hℓ) (min_le_left ρ ℓ)

/-- **The final scale** (`3_5:575–577`): once `𝒯_u(K) ≤ W^{-D}`, the truncated profile is
`𝒯̃^{K}_{u,D}(ρ) = max(𝒯_u(ρ), W^{-D})`. -/
theorem ST_tailW_final {g u K W D ρ : ℝ} (hK : 0 ≤ K)
    (hT : tailT d L g u K ≤ W ^ (-D)) :
    tailW d L g u K W D ρ = max (tailT d L g u ρ) (W ^ (-D)) := by
  unfold tailW
  by_cases hρK : ρ ≤ K
  · rw [min_eq_left hρK]
  · push Not at hρK
    rw [min_eq_right hρK.le]
    have h1 : tailT d L g u ρ ≤ W ^ (-D) := (tailT_antitone hK hρK.le).trans hT
    rw [max_eq_right hT, max_eq_right h1]

end Tail

end RBM.Gauss.Sizes
/-! ## 5. The transfer between the single-time model and the grid walk

`transferLaw` (merged, `Path/Walk.lean`) says that the grid state `H_k = pathH sz s t K n k` has the
law of the single-time model at time `u_k = gridTime s t K n k`; this gives (5.1) the equality of
the probabilities of a measurable matrix event, (5.2) the passage from a per-time `≺` of the model
(at every time of `[s,t]`) to a `w.h.p.` event of the grid walk simultaneously for all grid indices,
(5.3) the converse at one grid index (the endpoint). -/

namespace RBM.Gauss.Sizes

open MeasureTheory Filter RBM RBM.Gauss RBM.Gauss.Sizes RBM.Path

section Transfer

variable {d : ℕ} (sz : Sizes d)

/-- `gridTime` stays in `[s_n, t_n]` for `k ≤ K_n`. -/
theorem ST_gridTime_mem (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hst : s n ≤ t n) (hK : K n ≠ 0)
    (hk : k ≤ K n) : gridTime s t K n k ∈ Set.Icc (s n) (t n) := by
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (by linarith) hKpos.le
  have hk' : (k : ℝ) ≤ K n := by exact_mod_cast hk
  refine ⟨?_, ?_⟩
  · unfold gridTime; nlinarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hΔ]
  · have hlast := gridTime_last s t K n hK
    unfold gridTime at hlast ⊢
    nlinarith [mul_le_mul_of_nonneg_right hk' hΔ]

/-- **(5.1)** the grid state at index `k` and the single-time model at the grid time have the same
law on measurable matrix events. -/
theorem ST_pathP_eq_seqP (s t : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (hs : 0 ≤ s n) (hst : s n ≤ t n)
    (hK : K n ≠ 0)
    {S : Set (Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)}
    (hS : MeasurableSet S) :
    pathP sz {ω | pathH sz s t K n k ω ∈ S} =
      Sizes.seqP sz {ω | sz.seqHflow n (gridTime s t K n k) ω ∈ S} := by
  have hp : Measurable (pathH sz s t K n k) :=
    Measurable.of_eval_matrix _ fun i j => measurable_pathH sz s t K n k i j
  have hq : Measurable (sz.seqHflow n (gridTime s t K n k)) :=
    Measurable.of_eval_matrix _ fun i j => Sizes.measurable_seqHflow_entry sz n _ i j
  have h1 := Measure.map_apply (μ := pathP sz) hp hS
  have h2 := Measure.map_apply (μ := Sizes.seqP sz) hq hS
  have h3 := transferLaw sz s t K n k hs hst hK
  calc _ = (pathP sz).map (pathH sz s t K n k) S := h1.symm
    _ = (Sizes.seqP sz).map (sz.seqHflow n (gridTime s t K n k)) S := by rw [h3]
    _ = _ := h2

/-- **(5.2) From the model to the grid walk.**  If, for every `D > 0`, eventually in `n`, every
grid index `j ∈ J_n` (a polynomially bounded set of indices `≤ K_n`) and every label `v ∈ V_n`
satisfy `P_model(N^τ Z(H_{u_j}) < F(H_{u_j})) ≤ N^{-D}` (this is what the per-time `≺` of the model
at the time `u_j ∈ [s,t]` gives), then w.h.p. the grid walk satisfies `F ≤ N^τ Z` at all
`j ∈ J_n`, `v ∈ V_n` simultaneously. -/
theorem ST_whp_grid {V : ℕ → Type} [∀ n, Fintype (V n)] (s t : ℕ → ℝ) (K : ℕ → ℕ)
    (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n) (hK : ∀ n, K n ≠ 0)
    (J : ℕ → Finset ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hcard : ∀ᶠ n in atTop,
      (((J n).card * Fintype.card (V n) : ℕ) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (F Z : ∀ n, V n → ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n v u, Measurable (F n v u)) (hZ : ∀ n v u, Measurable (Z n v u)) (τ : ℝ)
    (h : ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop, ∀ j ∈ J n, ∀ v : V n,
      Sizes.seqP sz {ω | ((sz.size n : ℕ) : ℝ) ^ τ *
            Z n v (gridTime s t K n j) (sz.seqHflow n (gridTime s t K n j) ω) <
          F n v (gridTime s t K n j) (sz.seqHflow n (gridTime s t K n j) ω)} ≤
        ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D))) :
    Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω | ∀ j ∈ J n, ∀ v : V n,
      F n v (gridTime s t K n j) (pathH sz s t K n j ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n v (gridTime s t K n j) (pathH sz s t K n j ω)}) := by
  have hmain := highProbAt_iInter (pathP sz) sz.size (K := fun n => ↥(J n) × V n)
    (Ξ := fun n p => {ω | F n p.2 (gridTime s t K n p.1) (pathH sz s t K n p.1 ω) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) (pathH sz s t K n p.1 ω)})
    hC0 (by
      filter_upwards [hcard] with n hn
      simpa [Fintype.card_prod, Fintype.card_coe] using hn) (by
      intro D hD
      filter_upwards [h D hD] with n hn p
      have hS : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
          ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) H <
            F n p.2 (gridTime s t K n p.1) H} :=
        measurableSet_lt (measurable_const.mul (hZ _ _ _)) (hF _ _ _)
      have hc : {ω : PathΩ sz | F n p.2 (gridTime s t K n p.1) (pathH sz s t K n p.1 ω) ≤
          ((sz.size n : ℕ) : ℝ) ^ τ * Z n p.2 (gridTime s t K n p.1) (pathH sz s t K n p.1 ω)}ᶜ =
          {ω | pathH sz s t K n p.1 ω ∈ {H : Matrix (Idx d (sz.L n) (sz.W n))
            (Idx d (sz.L n) (sz.W n)) ℂ | ((sz.size n : ℕ) : ℝ) ^ τ *
              Z n p.2 (gridTime s t K n p.1) H < F n p.2 (gridTime s t K n p.1) H}} := by
        ext ω; simp [not_le]
      rw [hc, ST_pathP_eq_seqP sz s t K n p.1 (hs n) (hst n) (hK n) hS]
      exact hn p.1 p.1.2 p.2)
  refine hmain.mono (Eventually.of_forall fun n => ?_)
  intro ω hω j hj v
  exact Set.mem_iInter.mp hω (⟨j, hj⟩, v)

/-- **(5.3) From the grid walk to the model at the endpoint.**  If a pathwise bound
`F ≤ N^τ Z` at the last grid index (`u_K = t_n`) holds w.h.p. for the grid walk, then the
single-time model at `t_n` satisfies the same bound with the failure probability `N^{-D}`. -/
theorem ST_model_of_whp_grid (s t : ℕ → ℝ) (K : ℕ → ℕ) (hs : ∀ n, 0 ≤ s n) (hst : ∀ n, s n ≤ t n)
    (hK : ∀ n, K n ≠ 0)
    (F Z : ∀ n, ℝ → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ → ℝ)
    (hF : ∀ n u, Measurable (F n u)) (hZ : ∀ n u, Measurable (Z n u)) (τ : ℝ)
    (hw : Gauss.HighProbAt (pathP sz) sz.size (fun n => {ω |
      F n (t n) (pathH sz s t K n (K n) ω) ≤
        ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (pathH sz s t K n (K n) ω)})) :
    ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (sz.seqHflow n (t n) ω) <
        F n (t n) (sz.seqHflow n (t n) ω)} ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-D)) := by
  intro D hD
  filter_upwards [hw D hD] with n hn
  have hS : MeasurableSet {H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ |
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) H < F n (t n) H} :=
    measurableSet_lt (measurable_const.mul (hZ _ _)) (hF _ _)
  have hlast := gridTime_last s t K n (hK n)
  have hq := ST_pathP_eq_seqP sz s t K n (K n) (hs n) (hst n) (hK n) hS
  rw [hlast] at hq
  have hc : {ω : PathΩ sz | F n (t n) (pathH sz s t K n (K n) ω) ≤
      ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (pathH sz s t K n (K n) ω)}ᶜ =
      {ω | pathH sz s t K n (K n) ω ∈ {H : Matrix (Idx d (sz.L n) (sz.W n))
        (Idx d (sz.L n) (sz.W n)) ℂ | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) H <
          F n (t n) H}} := by
    ext ω; simp [not_le]
  have heq : Sizes.seqP sz {ω | ((sz.size n : ℕ) : ℝ) ^ τ * Z n (t n) (sz.seqHflow n (t n) ω) <
      F n (t n) (sz.seqHflow n (t n) ω)} = (pathP sz) {ω : PathΩ sz | F n (t n)
        (pathH sz s t K n (K n) ω) ≤ ((sz.size n : ℕ) : ℝ) ^ τ *
          Z n (t n) (pathH sz s t K n (K n) ω)}ᶜ := by
    rw [hc]; exact hq.symm
  rw [heq]
  exact hn

/-- **(5.4) Per-time `≺` of the model from the single-time statements at every section.**  If for
every time section `tt n ∈ [s_n, t_n]` the family indexed by the labels `V_n` is dominated
(`Prec`, union over labels inside), then the family indexed by `[s,t] × V_n` is dominated per time
(`PrecPT`). -/
theorem ST_PT_of_sections {V : ℕ → Type} [∀ n, Fintype (V n)] [∀ n, Nonempty (V n)]
    {s t : ℕ → ℝ} (hst : ∀ n, s n ≤ t n) (ξ ζ : ∀ n, TimeIcc s t n × V n → Sizes.SeqΩ sz → ℝ)
    (h : ∀ tt : ∀ n, TimeIcc s t n,
      sz.Prec (U := V) (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω)) :
    sz.PrecPT (U := fun n => TimeIcc s t n × V n) ξ ζ := by
  have hU : ∀ n, Nonempty (TimeIcc s t n × V n) := fun n =>
    ⟨(⟨s n, le_rfl, hst n⟩, Classical.arbitrary (V n))⟩
  refine (perTimeDomAt_iff_forall_section (Sizes.seqP sz) sz.size hU ξ ζ).mpr ?_
  intro p
  have h1 := h (fun n => (p n).1)
  have h2 := StochDomAt.precomp_param (V := fun _ => Unit) h1 (fun n _ => (p n).2)
  exact h2

/-- **(5.5) The converse of (5.4)**: a per-time `≺` over `[s,t] × V_n` with `#V_n ≤ N^C` gives, at
every time section, the domination of the `V_n`-indexed family. -/
theorem ST_sections_of_PT {V : ℕ → Type} [∀ n, Fintype (V n)] {s t : ℕ → ℝ}
    (ξ ζ : ∀ n, TimeIcc s t n × V n → Sizes.SeqΩ sz → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᶠ n in atTop, (Fintype.card (V n) : ℝ) ≤ ((sz.size n : ℕ) : ℝ) ^ C)
    (h : sz.PrecPT (U := fun n => TimeIcc s t n × V n) ξ ζ) (tt : ∀ n, TimeIcc s t n) :
    sz.Prec (U := V) (fun n v ω => ξ n (tt n, v) ω) (fun n v ω => ζ n (tt n, v) ω) := by
  refine stochDomAt_of_perTimeDomAt (Sizes.seqP sz) sz.size hC0 hC ?_
  intro τ hτ D hD
  filter_upwards [h τ hτ D hD] with n hn v
  exact hn (tt n, v)

end Transfer

end RBM.Gauss.Sizes
/-! ## 6. The engine of the self-improving estimate (`3_5:537–577`)

Everything at a fixed sample of the grid walk, for real sequences: the Grönwall inequality for
`Ĵ` up to the stopping index (`ST_engine`), proved from the pathwise inequalities that the good
event provides.  Parameters: `Λ ≥ 1` the polynomial loss (`N^ε`), `C` the constant of `lem:newKLK`,
`mI = Im m(E)`, `b_j = W^{-d} B_{u_j,0}`, `θ_j = b_j^{1/6}`. -/

namespace RBM.Gauss.Sizes

section Engine

/-- `x^{1/2}` is nondecreasing on the nonnegative reals (`Real.rpow`). -/
theorem ST_rpow_half_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ (1 / 2 : ℝ) ≤ y ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hx hxy (by norm_num)

/-- `(x + y)^{1/2} ≤ x^{1/2} + y^{1/2}` for `x, y ≥ 0`. -/
theorem ST_rpow_half_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y) ^ (1 / 2 : ℝ) ≤ x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow x, ← Real.sqrt_eq_rpow y]
  refine Real.sqrt_le_iff.mpr ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- `J < b^{1/6}` and `J ≥ 0` give `J³ ≤ b^{1/2}` (`3_5:542`: `Ĵ^{3/2} ≤ Δ^{1/4}`). -/
theorem ST_cube_le {J b : ℝ} (hJ : 0 ≤ J) (hb : 0 ≤ b) (h : J < b ^ (1 / 6 : ℝ)) :
    J ^ 3 ≤ b ^ (1 / 2 : ℝ) := by
  have h1 : J ^ 3 ≤ (b ^ (1 / 6 : ℝ)) ^ 3 := pow_le_pow_left₀ hJ h.le 3
  have h2 : (b ^ (1 / 6 : ℝ)) ^ 3 = b ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num
  rw [← h2]; exact h1

/-- **`ST_engine`: the Grönwall closure of `3_5:556–568`, at a fixed sample.**  For the labels `i`
(pairs `(σ,a)`), with `x_k i = |(𝓛-𝒦)^{(2)}_{u_k,i}|`, `P_k i = W^{-d} 𝒯̃^{K_{u_k}}_{u_k,D}`,
`Ĵ_k = max_i x_k i/P_k i`, `u_k = s + kΔ`, `b_k = W^{-d} B_{u_k,0}`, stopping index `τ` of `Ĵ`
against `b_k^{1/6}` (`eq:def2_stopping`):  the pathwise facts
* the grid decomposition `x_k ≤ x_0 + Δ Σ_{j<k} dr_j + remk_k + mart_k` (`Sol_CalL`),
* the drift `dr_j ≤ th_j + el_j + eg_j` with `lem:newKLK` (`th`, `el`: `C/(1-u_j)`) and
  `lem: EWGn2_N` (`eg`: `Λ η_j^{-1} b_j^{1/2}`, `η_j = mI (1-u_j)`),
* the quadratic variation `ee_j ≤ Λ η_j^{-1} (b_j^{1/2} + Ĵ_j³) P_j²` (`lem: EMn2_N`) and the
  martingale tail `mart_k ≤ Λ (Σ_{j<k} Δ ee_j + ρ₁ P_0²)^{1/2}` (`lem:DIfREP`),
* the initial value and the remainder `x_0 ≤ a₀ P_0`, `remk_k ≤ r₀ P_0`,
and the closure `α_k ((1-s)/(1-u_k))^{3C} < b_k^{1/6}` give `τ = K` and
`Ĵ_k ≤ α_k ((1-s)/(1-u_k))^{3C}` for all `k ≤ K`, where
`α_k = a₀ + r₀ + Δ Σ_{j<k} Λ b_j^{1/2}/η_j + Λ (2 Λ b_k^{1/2} Δ Σ_{j<k} η_j^{-1} + ρ₁)^{1/2}`. -/
theorem ST_engine {ι : Type*} {K τ : ℕ} {Δ s a₀ r₀ ρ₁ Λ C mI : ℝ}
    {x dr th el eg mart remk ee P : ℕ → ι → ℝ} {Jh b : ℕ → ℝ}
    (hΔ : 0 ≤ Δ) (hsK : s + K * Δ < 1) (hmI : 0 < mI) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C)
    (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀) (hρ₁ : 0 ≤ ρ₁)
    (hb0 : ∀ j, j ≤ K → 0 < b j) (hb1 : ∀ j, j ≤ K → b j ≤ 1) (hbm : MonotoneOn b (Set.Iic K))
    (hP0 : ∀ j i, j ≤ K → 0 < P j i) (hPm : ∀ i, MonotoneOn (fun j => P j i) (Set.Iic K))
    (hJh0 : ∀ j, j ≤ K → 0 ≤ Jh j)
    (hJhsup : ∀ k B, k ≤ K → (∀ i, x k i / P k i ≤ B) → Jh k ≤ B)
    (hτK : τ ≤ K) (hbelow : ∀ j, j < τ → Jh j < b j ^ (1 / 6 : ℝ))
    (hhit : τ < K → b τ ^ (1 / 6 : ℝ) ≤ Jh τ)
    (hdec : ∀ i k, k ≤ K → k ≤ τ →
      x k i ≤ x 0 i + Δ * ∑ j ∈ Finset.range k, dr j i + remk k i + mart k i)
    (hdr : ∀ j i, dr j i ≤ th j i + el j i + eg j i)
    (hth : ∀ j i, j ≤ K → th j i ≤ C / (1 - (s + j * Δ)) * Jh j * P j i)
    (hel : ∀ j i, j ≤ K → el j i ≤ C / (1 - (s + j * Δ)) * (Jh j + Jh j ^ 2) * P j i)
    (heg : ∀ j i, j ≤ K →
      eg j i ≤ Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) * P j i)
    (hee : ∀ j i, j ≤ K → ee j i ≤
      Λ / (mI * (1 - (s + j * Δ))) * (b j ^ (1 / 2 : ℝ) + Jh j ^ 3) * P j i ^ 2)
    (hee0 : ∀ j i, 0 ≤ ee j i)
    (hmart : ∀ i k, k ≤ K →
      mart k i ≤ Λ * (∑ j ∈ Finset.range k, Δ * ee j i + ρ₁ * P 0 i ^ 2) ^ (1 / 2 : ℝ))
    (hrem : ∀ i k, k ≤ K → remk k i ≤ r₀ * P 0 i)
    (hinit : ∀ i, x 0 i ≤ a₀ * P 0 i)
    (hclose : ∀ k, k ≤ K →
      (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) +
          Λ * (2 * Λ * b k ^ (1 / 2 : ℝ) *
            (Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
        ((1 - s) / (1 - (s + k * Δ))) ^ (3 * C) < b k ^ (1 / 6 : ℝ)) :
    τ = K ∧ ∀ k, k ≤ K →
      Jh k ≤ (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) +
          Λ * (2 * Λ * b k ^ (1 / 2 : ℝ) *
            (Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
        ((1 - s) / (1 - (s + k * Δ))) ^ (3 * C) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  -- positivity of `1 - u_j` on `j ≤ K`
  have hu : ∀ j, j ≤ K → 0 < 1 - (s + j * Δ) := by
    intro j hj
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith [mul_le_mul_of_nonneg_right this hΔ]
  set β : ℕ → ℝ := fun j => 3 * C * (1 - (s + j * Δ))⁻¹ with hβdef
  set e : ℕ → ℝ := fun j => Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) with hedef
  set S : ℕ → ℝ := fun k => Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹ with hSdef
  set m : ℕ → ℝ := fun k => Λ * (2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁) ^ (1 / 2 : ℝ) with hmdef
  have hβ : ∀ j, j < K → 0 ≤ β j := fun j hj =>
    mul_nonneg (by positivity) (inv_nonneg.mpr (hu j hj.le).le)
  have he : ∀ j, j < K → 0 ≤ e j := fun j hj =>
    mul_nonneg (div_nonneg (by linarith) (mul_nonneg hmI.le (hu j hj.le).le))
      (Real.rpow_nonneg (hb0 j hj.le).le _)
  have hSnn : ∀ k, k ≤ K → 0 ≤ S k := by
    intro k hk
    refine mul_nonneg hΔ (Finset.sum_nonneg fun j hj => ?_)
    exact inv_nonneg.mpr (mul_nonneg hmI.le (hu j (by have := Finset.mem_range.mp hj; omega)).le)
  have hSm : MonotoneOn S (Set.Iic K) := by
    intro k hk l hl hkl
    simp only [hSdef]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr hkl) fun j hj _ => ?_) hΔ
    exact inv_nonneg.mpr (mul_nonneg hmI.le
      (hu j (by have := Finset.mem_range.mp hj; simp at hl; omega)).le)
  have hmm : MonotoneOn m (Set.Iic K) := by
    intro k hk l hl hkl
    simp only [hmdef]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    refine ST_rpow_half_mono (by
      have := hSnn k hk
      have := Real.rpow_nonneg (hb0 k hk).le (1 / 2 : ℝ)
      positivity) ?_
    have h1 : b k ^ (1 / 2 : ℝ) ≤ b l ^ (1 / 2 : ℝ) :=
      ST_rpow_half_mono (hb0 k hk).le (hbm hk hl hkl)
    have h2 : S k ≤ S l := hSm hk hl hkl
    have h3 : 0 ≤ b k ^ (1 / 2 : ℝ) := Real.rpow_nonneg (hb0 k hk).le _
    have h4 := hSnn k hk
    have h5 : b k ^ (1 / 2 : ℝ) * S k ≤ b l ^ (1 / 2 : ℝ) * S l :=
      mul_le_mul h1 h2 h4 (Real.rpow_nonneg (hb0 l hl).le _)
    nlinarith
  have hαm := ST_alpha_mono (Δ := Δ) (a₀ := a₀) (r₀ := r₀) (K := K) hΔ he hmm
  -- the drift bound for `j < τ`
  have hJle1 : ∀ j, j < τ → Jh j ≤ 1 := fun j hj =>
    (hbelow j hj).le.trans (Real.rpow_le_one (hb0 j (hj.le.trans hτK)).le
      (hb1 j (hj.le.trans hτK)) (by norm_num))
  have hHd : ∀ i j, j < τ → dr j i ≤ (β j * Jh j + e j) * P j i := by
    intro i j hj
    have hjK : j ≤ K := (hj.le.trans hτK)
    have h1 := hdr j i
    have h2 := hth j i hjK
    have h3 := hel j i hjK
    have h4 := heg j i hjK
    have hJ0 := hJh0 j hjK
    have hJ2 : Jh j ^ 2 ≤ Jh j := by nlinarith [hJle1 j hj]
    have hPj := (hP0 j i hjK).le
    have hC1 : 0 ≤ C / (1 - (s + j * Δ)) := div_nonneg hC (hu j hjK).le
    have e1 : C / (1 - (s + j * Δ)) * (Jh j + Jh j ^ 2) * P j i ≤
        C / (1 - (s + j * Δ)) * (2 * Jh j) * P j i := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC1) hPj
    have e2 : (β j * Jh j + e j) * P j i =
        (3 * (C / (1 - (s + j * Δ))) * Jh j) * P j i + Λ / (mI * (1 - (s + j * Δ))) *
          b j ^ (1 / 2 : ℝ) * P j i := by
      simp only [hβdef, hedef]; ring
    rw [e2]
    nlinarith [h1, h2, h3, h4, e1]
  -- the martingale bound for `k ≤ τ`
  have hHm : ∀ i k, k ≤ τ → mart k i ≤ m k * P k i := by
    intro i k hk
    have hkK : k ≤ K := hk.trans hτK
    have hPk : ∀ j, j ≤ k → P j i ≤ P k i := fun j hj =>
      hPm i (show j ∈ Set.Iic K from le_trans hj hkK) (show k ∈ Set.Iic K from hkK) hj
    have hPkpos := hP0 k i hkK
    have hsum : ∑ j ∈ Finset.range k, Δ * ee j i ≤
        2 * Λ * b k ^ (1 / 2 : ℝ) * S k * P k i ^ 2 := by
      have hterm : ∀ j ∈ Finset.range k, Δ * ee j i ≤
          Δ * (2 * Λ * b k ^ (1 / 2 : ℝ) * (mI * (1 - (s + j * Δ)))⁻¹ * P k i ^ 2) := by
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        have hjτ : j < τ := lt_of_lt_of_le hjk hk
        have hjK : j ≤ K := hjk.le.trans hkK
        have h1 := hee j i hjK
        have hcube := ST_cube_le (hJh0 j hjK) (hb0 j hjK).le (hbelow j hjτ)
        have hbj : b j ^ (1 / 2 : ℝ) ≤ b k ^ (1 / 2 : ℝ) :=
          ST_rpow_half_mono (hb0 j hjK).le
            (hbm (show j ∈ Set.Iic K from hjK) (show k ∈ Set.Iic K from hkK) hjk.le)
        have hPj : P j i ^ 2 ≤ P k i ^ 2 := pow_le_pow_left₀ (hP0 j i hjK).le (hPk j hjk.le) 2
        have hc : 0 ≤ Λ / (mI * (1 - (s + j * Δ))) := div_nonneg (by linarith)
          (mul_nonneg hmI.le (hu j hjK).le)
        have e1 : Λ / (mI * (1 - (s + j * Δ))) * (b j ^ (1 / 2 : ℝ) + Jh j ^ 3) * P j i ^ 2 ≤
            Λ / (mI * (1 - (s + j * Δ))) * (2 * b k ^ (1 / 2 : ℝ)) * P k i ^ 2 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hc) hPj (sq_nonneg _)
            (mul_nonneg hc (mul_nonneg (by norm_num) (Real.rpow_nonneg (hb0 k hkK).le _)))
        have e2 : Λ / (mI * (1 - (s + j * Δ))) * (2 * b k ^ (1 / 2 : ℝ)) * P k i ^ 2 =
            2 * Λ * b k ^ (1 / 2 : ℝ) * (mI * (1 - (s + j * Δ)))⁻¹ * P k i ^ 2 := by
          rw [div_eq_mul_inv]; ring
        exact mul_le_mul_of_nonneg_left (h1.trans (e1.trans e2.le)) hΔ
      calc ∑ j ∈ Finset.range k, Δ * ee j i
          ≤ ∑ j ∈ Finset.range k,
              Δ * (2 * Λ * b k ^ (1 / 2 : ℝ) * (mI * (1 - (s + j * Δ)))⁻¹ * P k i ^ 2) :=
            Finset.sum_le_sum hterm
        _ = 2 * Λ * b k ^ (1 / 2 : ℝ) * S k * P k i ^ 2 := by
            simp only [hSdef]
            have h : ∀ j ∈ Finset.range k, Δ * (2 * Λ * b k ^ (1 / 2 : ℝ) *
                (mI * (1 - (s + j * Δ)))⁻¹ * P k i ^ 2) =
                (2 * Λ * b k ^ (1 / 2 : ℝ) * P k i ^ 2) * (Δ * (mI * (1 - (s + j * Δ)))⁻¹) :=
              fun j _ => by ring
            rw [Finset.sum_congr rfl h, ← Finset.mul_sum, ← Finset.mul_sum]
            ring
    have hρ : ρ₁ * P 0 i ^ 2 ≤ ρ₁ * P k i ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hP0 0 i (Nat.zero_le K)).le (hPk 0 (Nat.zero_le k)) 2) hρ₁
    have hX0 : 0 ≤ 2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁ := by
      have := hSnn k hkK
      have := Real.rpow_nonneg (hb0 k hkK).le (1 / 2 : ℝ)
      positivity
    have hin : ∑ j ∈ Finset.range k, Δ * ee j i + ρ₁ * P 0 i ^ 2 ≤
        (2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁) * P k i ^ 2 := by nlinarith [hsum, hρ]
    have hsq : ((2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁) * P k i ^ 2) ^ (1 / 2 : ℝ) =
        (2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁) ^ (1 / 2 : ℝ) * P k i := by
      rw [Real.mul_rpow hX0 (sq_nonneg _)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hPkpos.le]; norm_num
    have hin0 : 0 ≤ ∑ j ∈ Finset.range k, Δ * ee j i + ρ₁ * P 0 i ^ 2 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) => mul_nonneg hΔ (hee0 j i))
      have : 0 ≤ ρ₁ * P 0 i ^ 2 := mul_nonneg hρ₁ (sq_nonneg _)
      linarith
    calc mart k i ≤ Λ * (∑ j ∈ Finset.range k, Δ * ee j i + ρ₁ * P 0 i ^ 2) ^ (1 / 2 : ℝ) :=
          hmart i k hkK
      _ ≤ Λ * (((2 * Λ * b k ^ (1 / 2 : ℝ) * S k + ρ₁) * P k i ^ 2)) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (ST_rpow_half_mono hin0 hin) (by linarith)
      _ = m k * P k i := by rw [hsq]; simp only [hmdef]; ring
  have hmain := ST_pathwise_ineq (K := K) (τ := τ) (Δ := Δ) (a₀ := a₀) (r₀ := r₀)
    (x := x) (dr := dr) (mart := mart) (P := P) (remk := remk) (Jh := Jh) (β := β) (e := e)
    (m := m) hΔ ha₀ hr₀ hJh0 hJhsup hP0 hPm hβ he hdec hinit hHd hrem hHm
  -- the bootstrap
  have hα0 : ∀ k, k ≤ K → 0 ≤ a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k := by
    intro k hk
    have h1 : 0 ≤ Δ * ∑ j ∈ Finset.range k, e j :=
      mul_nonneg hΔ (Finset.sum_nonneg fun j hj => he j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk))
    have h2 : 0 ≤ m k := by
      simp only [hmdef]
      refine mul_nonneg (by linarith) (Real.rpow_nonneg ?_ _)
      have := hSnn k hk
      have := Real.rpow_nonneg (hb0 k hk).le (1 / 2 : ℝ)
      positivity
    linarith
  have hprod : ∀ k, k ≤ K → ∏ j ∈ Finset.range k, (1 + Δ * β j) ≤
      ((1 - s) / (1 - (s + k * Δ))) ^ (3 * C) := by
    intro k hk
    have hk1 : s + (k : ℝ) * Δ < 1 := by
      have : (k : ℝ) ≤ K := by exact_mod_cast hk
      nlinarith [mul_le_mul_of_nonneg_right this hΔ]
    have := ST_prod_le_rpow (s := s) (Δ := Δ) (c := 3 * C) hΔ (by linarith) hk1
    simpa [hβdef] using this
  have hclose' : ∀ k, k ≤ K → (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k) *
      ∏ j ∈ Finset.range k, (1 + Δ * β j) < b k ^ (1 / 6 : ℝ) := by
    intro k hk
    have h1 := hclose k hk
    have h2 : (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k) *
        ∏ j ∈ Finset.range k, (1 + Δ * β j) ≤ (a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, e j + m k) *
        ((1 - s) / (1 - (s + k * Δ))) ^ (3 * C) :=
      mul_le_mul_of_nonneg_left (hprod k hk) (hα0 k hk)
    refine lt_of_le_of_lt h2 ?_
    simpa [hedef, hSdef, hmdef] using h1
  obtain ⟨hτ, hG⟩ := ST_bootstrap (K := K) (τ := τ) (Δ := Δ) hΔ hαm hβ hτK hhit
    (fun k hk hkτ => hmain k hk hkτ) hclose'
  refine ⟨hτ, fun k hk => (hG k hk).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (hprod k hk) (hα0 k hk)

end Engine

section Closure

/-- **The size of `α_k`** (`3_5:505–509`): with `L_k = log((1-s)/(1-u_k))` (the logarithmic time sum
`ST_logsum`) and `b_j ≤ b_k` (`j ≤ k`), `α_k` is at most
`a₀ + r₀ + Λ b_k^{1/2} L_k/mI + Λ (2 Λ b_k^{1/2} L_k/mI + ρ₁)^{1/2}`. -/
theorem ST_alpha_bound {k : ℕ} {Δ s a₀ r₀ ρ₁ Λ mI : ℝ} {b : ℕ → ℝ}
    (hΔ : 0 ≤ Δ) (hmI : 0 < mI) (hΛ : 1 ≤ Λ) (hρ₁ : 0 ≤ ρ₁) (hb0 : ∀ j, j ≤ k → 0 < b j)
    (hbm : MonotoneOn b (Set.Iic k)) (hk : s + k * Δ < 1) :
    a₀ + r₀ + Δ * ∑ j ∈ Finset.range k, Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) +
        Λ * (2 * Λ * b k ^ (1 / 2 : ℝ) *
          (Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ) ≤
      a₀ + r₀ + Λ * b k ^ (1 / 2 : ℝ) * (mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ)))) +
        Λ * (2 * Λ * b k ^ (1 / 2 : ℝ) * (mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ)))) + ρ₁) ^
          (1 / 2 : ℝ) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hlog := ST_logsum hΔ k hk
  have hsum : ∀ c : ℝ, 0 ≤ c → Δ * ∑ j ∈ Finset.range k, c * (mI * (1 - (s + j * Δ)))⁻¹ ≤
      c * (mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ)))) := by
    intro c hc
    have h1 : Δ * ∑ j ∈ Finset.range k, c * (mI * (1 - (s + j * Δ)))⁻¹ =
        c * mI⁻¹ * (Δ * ∑ j ∈ Finset.range k, (1 - (s + j * Δ))⁻¹) := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_inv]; ring
    rw [h1, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (inv_nonneg.mpr hmI.le)) hc
  have hpos : ∀ j, j < k → 0 < 1 - (s + (j : ℝ) * Δ) := by
    intro j hj
    have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
    nlinarith [mul_le_mul_of_nonneg_right this hΔ]
  have h1 : Δ * ∑ j ∈ Finset.range k, Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ) ≤
      Λ * b k ^ (1 / 2 : ℝ) * (mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ)))) := by
    calc Δ * ∑ j ∈ Finset.range k, Λ / (mI * (1 - (s + j * Δ))) * b j ^ (1 / 2 : ℝ)
        ≤ Δ * ∑ j ∈ Finset.range k, (Λ * b k ^ (1 / 2 : ℝ)) * (mI * (1 - (s + j * Δ)))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) hΔ
          have hjk := Finset.mem_range.mp hj
          have hbj : b j ^ (1 / 2 : ℝ) ≤ b k ^ (1 / 2 : ℝ) :=
            ST_rpow_half_mono (hb0 j hjk.le).le
              (hbm (show j ∈ Set.Iic k from hjk.le) (show k ∈ Set.Iic k from (le_refl k)) hjk.le)
          have hinv : 0 ≤ (mI * (1 - (s + j * Δ)))⁻¹ :=
            inv_nonneg.mpr (mul_nonneg hmI.le (hpos j hjk).le)
          rw [div_eq_mul_inv]
          calc Λ * (mI * (1 - (s + j * Δ)))⁻¹ * b j ^ (1 / 2 : ℝ)
              = Λ * b j ^ (1 / 2 : ℝ) * (mI * (1 - (s + j * Δ)))⁻¹ := by ring
            _ ≤ Λ * b k ^ (1 / 2 : ℝ) * (mI * (1 - (s + j * Δ)))⁻¹ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbj hΛ0) hinv
      _ ≤ _ := hsum _ (mul_nonneg hΛ0 (Real.rpow_nonneg (hb0 k le_rfl).le _))
  have h2 : Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹ ≤
      mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ))) := by
    have := hsum 1 zero_le_one
    simpa using this
  have hX0 : 0 ≤ 2 * Λ * b k ^ (1 / 2 : ℝ) * (Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹) + ρ₁ := by
    have : 0 ≤ Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹ :=
      mul_nonneg hΔ (Finset.sum_nonneg fun j hj =>
        inv_nonneg.mpr (mul_nonneg hmI.le (hpos j (Finset.mem_range.mp hj)).le))
    have := Real.rpow_nonneg (hb0 k le_rfl).le (1 / 2 : ℝ)
    positivity
  have h3 : 2 * Λ * b k ^ (1 / 2 : ℝ) * (Δ * ∑ j ∈ Finset.range k, (mI * (1 - (s + j * Δ)))⁻¹) + ρ₁ ≤
      2 * Λ * b k ^ (1 / 2 : ℝ) * (mI⁻¹ * Real.log ((1 - s) / (1 - (s + k * Δ)))) + ρ₁ := by
    have := Real.rpow_nonneg (hb0 k le_rfl).le (1 / 2 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2 * Λ * b k ^ (1 / 2 : ℝ) by positivity)]
  have h4 := ST_rpow_half_mono hX0 h3
  have h5 := mul_le_mul_of_nonneg_left h4 hΛ0
  linarith

/-- **The size of `α'`** (`3_5:505–509`): if `a₀, r₀, √ρ₁ ≤ q b^{1/5}` (`b ≤ 1`, `Λ ≥ 1`), then
`a₀ + r₀ + Λ b^{1/2} L/mI + Λ (2 Λ b^{1/2} L/mI + ρ₁)^{1/2} ≤ (3 + 3/mI) Λ² (1+q+L) b^{1/5}`. -/
theorem ST_alpha'_le {b q L Λ mI a₀ r₀ ρ₁ : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (hΛ : 1 ≤ Λ)
    (hmI : 0 < mI) (hL : 0 ≤ L) (hq : 0 ≤ q)
    (ha : a₀ ≤ q * b ^ (1 / 5 : ℝ)) (hr : r₀ ≤ q * b ^ (1 / 5 : ℝ))
    (hρ : ρ₁ ≤ (q * b ^ (1 / 5 : ℝ)) ^ 2) (hρ0 : 0 ≤ ρ₁) :
    a₀ + r₀ + Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) +
        Λ * (2 * Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) + ρ₁) ^ (1 / 2 : ℝ) ≤
      ((3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L)) * b ^ (1 / 5 : ℝ) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  have hb15 : 0 ≤ b ^ (1 / 5 : ℝ) := Real.rpow_nonneg hb0.le _
  have hb12 : b ^ (1 / 2 : ℝ) ≤ b ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (by norm_num)
  have hb14 : b ^ (1 / 4 : ℝ) ≤ b ^ (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hb0 hb1 (by norm_num)
  have hmI0 : 0 ≤ mI⁻¹ := inv_nonneg.mpr hmI.le
  set x : ℝ := mI⁻¹ * L with hx
  have hx0 : 0 ≤ x := mul_nonneg hmI0 hL
  -- `(2 Λ b^{1/2} x + ρ₁)^{1/2} ≤ (2 Λ x)^{1/2} b^{1/4} + q b^{1/5}`
  have hsq : (2 * Λ * b ^ (1 / 2 : ℝ) * x + ρ₁) ^ (1 / 2 : ℝ) ≤
      (2 * Λ * x) ^ (1 / 2 : ℝ) * b ^ (1 / 5 : ℝ) + q * b ^ (1 / 5 : ℝ) := by
    have h1 : (2 * Λ * b ^ (1 / 2 : ℝ) * x + ρ₁) ^ (1 / 2 : ℝ) ≤
        (2 * Λ * b ^ (1 / 2 : ℝ) * x) ^ (1 / 2 : ℝ) + ρ₁ ^ (1 / 2 : ℝ) :=
      ST_rpow_half_add_le (by positivity) hρ0
    have h2 : (2 * Λ * b ^ (1 / 2 : ℝ) * x) ^ (1 / 2 : ℝ) =
        (2 * Λ * x) ^ (1 / 2 : ℝ) * b ^ (1 / 4 : ℝ) := by
      have : 2 * Λ * b ^ (1 / 2 : ℝ) * x = (2 * Λ * x) * b ^ (1 / 2 : ℝ) := by ring
      rw [this, Real.mul_rpow (by positivity) (Real.rpow_nonneg hb0.le _), ← Real.rpow_mul hb0.le]
      norm_num
    have h3 : ρ₁ ^ (1 / 2 : ℝ) ≤ q * b ^ (1 / 5 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_iff.mpr ⟨by positivity, hρ⟩
    have h4 : (2 * Λ * x) ^ (1 / 2 : ℝ) * b ^ (1 / 4 : ℝ) ≤
        (2 * Λ * x) ^ (1 / 2 : ℝ) * b ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left hb14 (Real.rpow_nonneg (by positivity) _)
    linarith
  -- `(2 Λ x)^{1/2} ≤ Λ (1/2 + x) · 2`
  have hsq2 : (2 * Λ * x) ^ (1 / 2 : ℝ) ≤ Λ * (1 + 2 * x) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (Λ * (1 + 2 * x) - 1), mul_nonneg hΛ0 hx0, mul_nonneg hΛ0 hΛ0]
  have hα : a₀ + r₀ + Λ * b ^ (1 / 2 : ℝ) * x +
      Λ * (2 * Λ * b ^ (1 / 2 : ℝ) * x + ρ₁) ^ (1 / 2 : ℝ) ≤
      ((3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L)) * b ^ (1 / 5 : ℝ) := by
    have e1 : Λ * b ^ (1 / 2 : ℝ) * x ≤ Λ * x * b ^ (1 / 5 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hb12 (mul_nonneg hΛ0 hx0)]
    have e2 : Λ * (2 * Λ * b ^ (1 / 2 : ℝ) * x + ρ₁) ^ (1 / 2 : ℝ) ≤
        Λ * ((Λ * (1 + 2 * x)) * b ^ (1 / 5 : ℝ) + q * b ^ (1 / 5 : ℝ)) := by
      refine mul_le_mul_of_nonneg_left (hsq.trans ?_) hΛ0
      nlinarith [mul_le_mul_of_nonneg_right hsq2 hb15]
    have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
    have hq' : a₀ + r₀ ≤ 2 * q * b ^ (1 / 5 : ℝ) := by linarith
    have hkey : 2 * q + Λ * x + Λ ^ 2 * (1 + 2 * x) + Λ * q ≤
        (3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L) := by
      have hid : (3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L) -
          (2 * q + Λ * x + Λ ^ 2 * (1 + 2 * x) + Λ * q) =
          2 * Λ ^ 2 + q * ((Λ - 1) * (3 * Λ + 2)) + 3 * Λ ^ 2 * L + 3 * mI⁻¹ * Λ ^ 2 +
            3 * mI⁻¹ * Λ ^ 2 * q + mI⁻¹ * L * (Λ * (Λ - 1)) := by
        rw [hx]; ring
      have hnn : 0 ≤ 2 * Λ ^ 2 + q * ((Λ - 1) * (3 * Λ + 2)) + 3 * Λ ^ 2 * L + 3 * mI⁻¹ * Λ ^ 2 +
            3 * mI⁻¹ * Λ ^ 2 * q + mI⁻¹ * L * (Λ * (Λ - 1)) := by
        have h1 : 0 ≤ Λ - 1 := by linarith
        positivity
      linarith
    have e3 : a₀ + r₀ + Λ * x * b ^ (1 / 5 : ℝ) +
        Λ * ((Λ * (1 + 2 * x)) * b ^ (1 / 5 : ℝ) + q * b ^ (1 / 5 : ℝ)) ≤
        ((3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L)) * b ^ (1 / 5 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right hkey hb15]
    linarith
  linarith

/-- **The closure arithmetic** (`3_5:505–509`, `3_5:568`): if moreover
`c₁ Λ² (1+q+L) R b^{1/30} < 1` (`c₁ = 3 + 3/mI`, `L = log r`, `R = r^{3C}`), then `α' R < b^{1/6}`:
the exponent gap `1/5 - 1/6 = 1/30` absorbs the loss `Λ²`, the logarithm and the Grönwall factor
`r^{3C}`. -/
theorem ST_closure_arith {b q L Λ mI a₀ r₀ ρ₁ R : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) (hΛ : 1 ≤ Λ)
    (hmI : 0 < mI) (hL : 0 ≤ L) (hq : 0 ≤ q) (hR : 0 ≤ R)
    (ha : a₀ ≤ q * b ^ (1 / 5 : ℝ)) (hr : r₀ ≤ q * b ^ (1 / 5 : ℝ))
    (hρ : ρ₁ ≤ (q * b ^ (1 / 5 : ℝ)) ^ 2) (hρ0 : 0 ≤ ρ₁)
    (hsmall : (3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L) * R * b ^ (1 / 30 : ℝ) < 1) :
    (a₀ + r₀ + Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) +
        Λ * (2 * Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) + ρ₁) ^ (1 / 2 : ℝ)) * R < b ^ (1 / 6 : ℝ) := by
  have hα := ST_alpha'_le hb0 hb1 hΛ hmI hL hq ha hr hρ hρ0
  have hb16 : b ^ (1 / 5 : ℝ) = b ^ (1 / 6 : ℝ) * b ^ (1 / 30 : ℝ) := by
    rw [← Real.rpow_add hb0]; norm_num
  have hb6 : 0 < b ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hb0 _
  calc (a₀ + r₀ + Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) +
        Λ * (2 * Λ * b ^ (1 / 2 : ℝ) * (mI⁻¹ * L) + ρ₁) ^ (1 / 2 : ℝ)) * R
      ≤ (((3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L)) * b ^ (1 / 5 : ℝ)) * R :=
        mul_le_mul_of_nonneg_right hα hR
    _ = b ^ (1 / 6 : ℝ) * ((3 + 3 * mI⁻¹) * Λ ^ 2 * (1 + q + L) * R * b ^ (1 / 30 : ℝ)) := by
        rw [hb16]; ring
    _ < b ^ (1 / 6 : ℝ) * 1 := mul_lt_mul_of_pos_left hsmall hb6
    _ = b ^ (1 / 6 : ℝ) := mul_one _

end Closure

end RBM.Gauss.Sizes

/-! ## 8. The good event of one self-improving step and its pathwise consequence

`STGoodAt` collects the pathwise facts that the pins provide for the grid walk (section 9 and the events `ST_event_*` of
section 11 show that they hold with high probability); `ST_good_engine` applies the engine of section 6. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path

section Good

variable {d : ℕ} (sz : Sizes d)

/-- The labels `i = (σ, a)` of the 2-loops. -/
abbrev STLab (n : ℕ) : Type := (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n))

/-- The pathwise facts of one self-improving step at the sample `ω` of the grid walk from `s_n` to
`t_n` (`K_n` steps), energy `E`, floor `D`, scales `ℓk j = K_{u_j}` (`Λ ≥ 1` the loss `2N^ε`,
`δ₀` the weak-law threshold of `lem:newKLK`, `ρ₁` the martingale floor): the weak local law at the
grid states; the initial value `(Eq:Gdecay+IND)`; the light-weight bound `lem: EWGn2_N`; the
quadratic variation bound `lem: EMn2_N` with the random control `Ĵ`; the martingale tail
`lem:DIfREP`; the remainder; and the grid decomposition `Sol_CalL`. -/
structure STGoodAt (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (E D : ℝ) (ℓk : ℕ → ℝ) (Λ δ₀ a₀ r₀ ρ₁ : ℝ)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ)
    (ω : PathΩ sz) : Prop where
  weak : ∀ j, j ≤ K n → ∀ x y, ‖STGMM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) x y‖ ≤ δ₀
  init : ∀ i : STLab sz n, ‖STgA sz s t K n E i.1 i.2 0 ω‖ ≤
    a₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)
  lw : ∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEGtM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ ≤
    Λ / ((mE E).im * (1 - gridTime s t K n j)) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1)
  mg : ∀ j, j ≤ K n → ∀ i : STLab sz n, ‖STEEM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ ≤
    Λ / ((mE E).im * (1 - gridTime s t K n j)) *
      ((sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
        (STJhatM sz n E D (ℓk j) (gridTime s t K n j) (pathH sz s t K n j ω)) ^ 3) *
      STprof sz n (gridTime s t K n j) D (ℓk j) (i.2 0) (i.2 1) ^ 2
  mart : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Mart i k ω‖ ≤ Λ * (∑ j ∈ Finset.range k, gridStep s t K n *
      ‖STEEM sz n E (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ +
      ρ₁ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1) ^ 2) ^ (1 / 2 : ℝ)
  rem : ∀ i : STLab sz n, ∀ k, k ≤ K n → ‖Rem i k ω‖ ≤
    r₀ * STprof sz n (gridTime s t K n 0) D (ℓk 0) (i.2 0) (i.2 1)
  ident : ∀ i : STLab sz n, ∀ k, k ≤ K n → STgA sz s t K n E i.1 i.2 k ω =
    STgA sz s t K n E i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
      ∑ j ∈ Finset.range k, STgDrift sz s t K n E i.1 i.2 j ω + Rem i k ω + Mart i k ω

/-- Helper: the stopping index hits the threshold when it is `< K`. -/
theorem ST_firstHit_hit {Ω' : Type*} (J : ℕ → Ω' → ℝ) (θ : ℝ) (K : ℕ) {ω : Ω'}
    (h : firstHit J θ K ω < K) : θ ≤ J (firstHit J θ K ω) ω := by
  have h' : MeasureTheory.hittingBtwn J (Set.Ici θ) 0 K ω < K := h
  have := MeasureTheory.hittingBtwn_mem_set_of_hittingBtwn_lt (u := J) (s := Set.Ici θ) (n := 0)
    (m := K) (ω := ω) h'
  exact this

/-- **`ST_good_engine`**: on the good event of one step the stopping index never fires
(`T ≥ t`, `3_5:568`) and `Ĵ_k ≤ c₁ Λ² (1 + q + log r_k) b_k^{1/5} r_k^{3C}` for all grid indices
(`(eq:Gronwall_dervJuD)`), `r_k = (1-s)/(1-u_k)`, `b_k = W^{-d} B_{u_k,0}`, `c₁ = 3 + 3/Im m`. -/
theorem ST_good_engine (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (Efun : ℕ → ℝ) (D : ℝ)
    (Kf : ℕ → ℝ → ℝ) {Λ δ₀ C a₀ r₀ ρ₁ q κ 𝔡 : ℝ}
    (hK : K n ≠ 0) (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hD : 0 ≤ D)
    (hmI : 0 < (mE (Efun n)).im) (hΛ : 1 ≤ Λ) (hC : 0 ≤ C) (ha₀ : 0 ≤ a₀) (hr₀ : 0 ≤ r₀)
    (hρ₁ : 0 ≤ ρ₁) (hlam : 0 < sz.lam n) (hlam' : sz.lam n ≤ 𝔡⁻¹) (hE : |Efun n| ≤ 2 - κ)
    (hNew : STNewKLKAt d κ 𝔡 C δ₀)
    (hKf0 : ∀ j, j ≤ K n → 0 ≤ Kf n (gridTime s t K n j))
    (hKfL : ∀ j, j ≤ K n → Kf n (gridTime s t K n j) ≤ ((sz.L n : ℕ) : ℝ))
    (hTmono : ∀ j k, j ≤ k → k ≤ K n →
      tailT d (sz.L n) (sz.lam n) (gridTime s t K n j) (Kf n (gridTime s t K n j)) ≤
        tailT d (sz.L n) (sz.lam n) (gridTime s t K n k) (Kf n (gridTime s t K n k)))
    (hb1 : sz.Bctl n (t n) ≤ 1) (hq0 : 0 ≤ q)
    (ha : a₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) (hr : r₀ ≤ q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ))
    (hρ : ρ₁ ≤ (q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ)) ^ 2)
    (hsmall : ∀ k, k ≤ K n →
      (3 + 3 * ((mE (Efun n)).im)⁻¹) * Λ ^ 2 *
          (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) *
          (sz.Bctl n (gridTime s t K n k)) ^ (1 / 30 : ℝ) < 1)
    (Mart Rem : STLab sz n → ℕ → PathΩ sz → ℂ) (ω : PathΩ sz)
    (hg : STGoodAt sz s t K n (Efun n) D (fun j => Kf n (gridTime s t K n j)) Λ δ₀ a₀ r₀ ρ₁
      Mart Rem ω) :
    STstopIdx sz s t K Efun D Kf n ω = K n ∧ ∀ k, k ≤ K n →
      STJhatM sz n (Efun n) D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
          (pathH sz s t K n k ω) ≤
        ((3 + 3 * ((mE (Efun n)).im)⁻¹) * Λ ^ 2 *
            (1 + q + Real.log ((1 - s n) / (1 - gridTime s t K n k))) *
            (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) *
          ((1 - s n) / (1 - gridTime s t K n k)) ^ (3 * C) := by
  classical
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ : 0 ≤ gridStep s t K n := div_nonneg (by linarith) hKpos.le
  have hlast : s n + (K n : ℝ) * gridStep s t K n = t n := by
    have := gridTime_last s t K n hK
    simpa [gridTime] using this
  have hu_le : ∀ j, j ≤ K n → gridTime s t K n j ≤ t n := fun j hj =>
    (ST_gridTime_mem s t K n j hst hK hj).2
  have hu_ge : ∀ j, j ≤ K n → s n ≤ gridTime s t K n j := fun j hj =>
    (ST_gridTime_mem s t K n j hst hK hj).1
  have hu_mono : ∀ j k, j ≤ k → gridTime s t K n j ≤ gridTime s t K n k := by
    intro j k hjk
    unfold gridTime
    have : (j : ℝ) ≤ k := by exact_mod_cast hjk
    nlinarith [mul_le_mul_of_nonneg_right this hΔ]
  have hu_lt : ∀ j, j ≤ K n → gridTime s t K n j < 1 := fun j hj =>
    lt_of_le_of_lt (hu_le j hj) ht1
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hbpos : ∀ j, j ≤ K n → 0 < sz.Bctl n (gridTime s t K n j) := fun j hj =>
    STBctl_pos sz n (hu_lt j hj)
  have hbmono : MonotoneOn (fun j => sz.Bctl n (gridTime s t K n j)) (Set.Iic (K n)) := by
    intro j hj k hk hjk
    exact STBctl_mono sz n (hu_mono j k hjk) (hu_lt k hk)
  have hb1' : ∀ j, j ≤ K n → sz.Bctl n (gridTime s t K n j) ≤ 1 := fun j hj =>
    (STBctl_mono sz n (hu_le j hj) ht1).trans hb1
  -- the profile
  have hPpos : ∀ (j : ℕ) (i : STLab sz n), 0 < STprof sz n (gridTime s t K n j) D
      (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j i
    unfold STprof
    exact mul_pos (inv_pos.mpr (pow_pos hW d)) (tailW_pos hW _)
  have hPm : ∀ i : STLab sz n, MonotoneOn (fun j => STprof sz n (gridTime s t K n j) D
      (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1)) (Set.Iic (K n)) := by
    intro i j hj k hk hjk
    simp only [Set.mem_Iic] at hj hk
    unfold STprof
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg hW.le d))
    exact ST_tailW_mono_time hL1 hlam.le (hu_mono j k hjk) (hu_lt k hk) (hKf0 j hj) (hKf0 k hk)
      (Nat.cast_nonneg _) (hTmono j k hjk hk)
  have hJhsup : ∀ k B, k ≤ K n → (∀ i : STLab sz n, ‖STgA sz s t K n (Efun n) i.1 i.2 k ω‖ /
      STprof sz n (gridTime s t K n k) D (Kf n (gridTime s t K n k)) (i.2 0) (i.2 1) ≤ B) →
      STJhatM sz n (Efun n) D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
        (pathH sz s t K n k ω) ≤ B := by
    intro k B hk h
    unfold STJhatM
    exact Finset.sup'_le _ _ fun p _ => h p
  have hJh0 : ∀ j, j ≤ K n → 0 ≤ STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j))
      (gridTime s t K n j) (pathH sz s t K n j ω) := by
    intro j hj
    unfold STJhatM
    have hw : STLab sz n := ((fun _ => true), (fun _ => 0))
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ hw))
    exact div_nonneg (norm_nonneg _) (hPpos j hw).le
  -- the stopping index
  have hτK : STstopIdx sz s t K Efun D Kf n ω ≤ K n := firstHit_le _ _ _ ω
  have hbelow : ∀ j, j < STstopIdx sz s t K Efun D Kf n ω →
      STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (pathH sz s t K n j ω) < (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ) := by
    intro j hj
    have hj' : j < firstHit (fun j (ω : PathΩ sz) =>
        STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (pathH sz s t K n j ω) / (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n) ω := hj
    have h1 := lt_firstHit_imp _ _ _ hj'
    have hb6 : 0 < (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ) :=
      Real.rpow_pos_of_pos (hbpos j (hj.le.trans hτK)) _
    exact (div_lt_one hb6).mp h1
  have hhit : STstopIdx sz s t K Efun D Kf n ω < K n →
      (sz.Bctl n (gridTime s t K n (STstopIdx sz s t K Efun D Kf n ω))) ^ (1 / 6 : ℝ) ≤
        STJhatM sz n (Efun n) D (Kf n (gridTime s t K n (STstopIdx sz s t K Efun D Kf n ω)))
          (gridTime s t K n (STstopIdx sz s t K Efun D Kf n ω))
          (pathH sz s t K n (STstopIdx sz s t K Efun D Kf n ω) ω) := by
    intro h
    have h' : firstHit (fun j (ω : PathΩ sz) =>
        STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
          (pathH sz s t K n j ω) / (sz.Bctl n (gridTime s t K n j)) ^ (1 / 6 : ℝ)) 1 (K n) ω <
        K n := h
    have h1 := ST_firstHit_hit _ 1 (K n) h'
    have hb6 : 0 < (sz.Bctl n (gridTime s t K n (STstopIdx sz s t K Efun D Kf n ω))) ^
        (1 / 6 : ℝ) := Real.rpow_pos_of_pos (hbpos _ h.le) _
    exact (one_le_div hb6).mp h1
  -- the labels and the pathwise inequalities
  have hsK : s n + (K n : ℝ) * gridStep s t K n < 1 := by rw [hlast]; exact ht1
  have hg0 : gridTime s t K n 0 = s n := by simp [gridTime]
  have hdec : ∀ (i : STLab sz n) (k : ℕ), k ≤ K n → k ≤ STstopIdx sz s t K Efun D Kf n ω →
      ‖STgA sz s t K n (Efun n) i.1 i.2 k ω‖ ≤ ‖STgA sz s t K n (Efun n) i.1 i.2 0 ω‖ +
        gridStep s t K n * ∑ j ∈ Finset.range k, ‖STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖ +
        ‖Rem i k ω‖ + ‖Mart i k ω‖ := by
    intro i k hk _
    have hid := hg.ident i k hk
    have hsum : ‖((gridStep s t K n : ℝ) : ℂ) *
        ∑ j ∈ Finset.range k, STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖ ≤
        gridStep s t K n * ∑ j ∈ Finset.range k, ‖STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hΔ]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hΔ
    rw [hid]
    calc ‖STgA sz s t K n (Efun n) i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s t K n (Efun n) i.1 i.2 j ω + Rem i k ω + Mart i k ω‖
        ≤ ‖STgA sz s t K n (Efun n) i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s t K n (Efun n) i.1 i.2 j ω + Rem i k ω‖ +
          ‖Mart i k ω‖ := norm_add_le _ _
      _ ≤ (‖STgA sz s t K n (Efun n) i.1 i.2 0 ω + ((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖ + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖STgA sz s t K n (Efun n) i.1 i.2 0 ω‖ + ‖((gridStep s t K n : ℝ) : ℂ) *
          ∑ j ∈ Finset.range k, STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖) + ‖Rem i k ω‖) +
          ‖Mart i k ω‖ := by gcongr; exact norm_add_le _ _
      _ ≤ _ := by gcongr
  have hdr : ∀ (j : ℕ) (i : STLab sz n),
      ‖STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖ ≤
        ‖STthetaOp sz n (Efun n) (gridTime s t K n j) i.1
          (STLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1) i.2‖ +
        ‖STELKLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ +
        ‖STEGtM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ := by
    intro j i
    unfold STgDrift
    exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  -- `lem:newKLK` at the grid states
  have hnewk : ∀ j, j ≤ K n → ∀ i : STLab sz n,
      ‖STthetaOp sz n (Efun n) (gridTime s t K n j) i.1
          (STLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1) i.2‖ ≤
        C / (1 - gridTime s t K n j) * STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (pathH sz s t K n j ω) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) ∧
      ‖STELKLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ ≤
        C / (1 - gridTime s t K n j) * (STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (pathH sz s t K n j ω) +
          STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
            (pathH sz s t K n j ω) ^ 2 * (if 1 ≤ Kf n (gridTime s t K n j) then 1 else 0)) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j hj i
    exact hNew sz n (Efun n) (gridTime s t K n j) D (Kf n (gridTime s t K n j)) hlam hlam' hE
      (hs0.trans (hu_ge j hj)) (hu_lt j hj) hD (hKf0 j hj) (hKfL j hj)
      (pathH sz s t K n j ω) (pathH_isHermitian sz s t K n j ω) (hg.weak j hj) i.1 i.2
  have hCj : ∀ j, j ≤ K n → 0 ≤ C / (1 - gridTime s t K n j) := fun j hj =>
    div_nonneg hC (by linarith [hu_lt j hj])
  have hel : ∀ (j : ℕ) (i : STLab sz n), j ≤ K n →
      ‖STELKLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖ ≤
        C / (1 - gridTime s t K n j) * (STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j))
          (gridTime s t K n j) (pathH sz s t K n j ω) +
          STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
            (pathH sz s t K n j ω) ^ 2) *
          STprof sz n (gridTime s t K n j) D (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1) := by
    intro j i hj
    refine (hnewk j hj i).2.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right ?_ _) (hCj j hj))
      (hPpos j i).le
    split_ifs
    · simp
    · simp [sq_nonneg]
  have hs1 : s n < 1 := lt_of_le_of_lt hst ht1
  -- the closure `α'_k R_k < b_k^{1/6}` and the bound of `α_k`
  have hrk : ∀ k, k ≤ K n → 1 ≤ (1 - s n) / (1 - gridTime s t K n k) := by
    intro k hk
    have h1 : 0 < 1 - gridTime s t K n k := by linarith [hu_lt k hk]
    rw [le_div_iff₀ h1]
    linarith [hu_ge k hk]
  have hbs : ∀ k, k ≤ K n → sz.Bctl n (s n) ≤ sz.Bctl n (gridTime s t K n k) := fun k hk =>
    STBctl_mono sz n (hu_ge k hk) (hu_lt k hk)
  have hqb : ∀ k, k ≤ K n → q * (sz.Bctl n (s n)) ^ (1 / 5 : ℝ) ≤
      q * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ) := fun k hk =>
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (STBctl_pos sz n hs1).le (hbs k hk)
      (by norm_num)) hq0
  have hρb : ∀ k, k ≤ K n → ρ₁ ≤ (q * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 5 : ℝ)) ^ 2 := by
    intro k hk
    refine hρ.trans (pow_le_pow_left₀ (mul_nonneg hq0 (Real.rpow_nonneg (STBctl_pos sz n hs1).le _))
      (hqb k hk) 2)
  have hclose : ∀ k, k ≤ K n →
      (a₀ + r₀ + gridStep s t K n * ∑ j ∈ Finset.range k, Λ / ((mE (Efun n)).im *
          (1 - (s n + j * gridStep s t K n))) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
        Λ * (2 * Λ * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 2 : ℝ) *
          (gridStep s t K n * ∑ j ∈ Finset.range k,
            ((mE (Efun n)).im * (1 - (s n + j * gridStep s t K n)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
        ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) <
        (sz.Bctl n (gridTime s t K n k)) ^ (1 / 6 : ℝ) := by
    intro k hk
    have hk1 : s n + (k : ℝ) * gridStep s t K n < 1 := by
      have := hu_lt k hk; simpa [gridTime] using this
    have hα := ST_alpha_bound (k := k) (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀)
      (ρ₁ := ρ₁) (Λ := Λ) (mI := (mE (Efun n)).im)
      (b := fun j => sz.Bctl n (gridTime s t K n j)) hΔ hmI hΛ hρ₁
      (fun j hj => hbpos j (hj.trans hk)) (hbmono.mono (Set.Iic_subset_Iic.mpr hk)) hk1
    have hr1 : 1 ≤ (1 - s n) / (1 - (s n + k * gridStep s t K n)) := by
      have := hrk k hk; simpa [gridTime] using this
    have hR0 : 0 ≤ ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) :=
      Real.rpow_nonneg (by linarith) _
    have hcl := ST_closure_arith (b := sz.Bctl n (gridTime s t K n k)) (q := q)
      (L := Real.log ((1 - s n) / (1 - (s n + k * gridStep s t K n)))) (Λ := Λ)
      (mI := (mE (Efun n)).im) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁)
      (R := ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C))
      (hbpos k hk) (hb1' k hk) hΛ hmI (Real.log_nonneg hr1) hq0 hR0 (ha.trans (hqb k hk))
      (hr.trans (hqb k hk)) (hρb k hk) hρ₁ (by simpa [gridTime] using hsmall k hk)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα hR0) hcl
  have hmain : STstopIdx sz s t K Efun D Kf n ω = K n ∧ ∀ k, k ≤ K n →
      STJhatM sz n (Efun n) D (Kf n (gridTime s t K n k)) (gridTime s t K n k)
          (pathH sz s t K n k ω) ≤
        (a₀ + r₀ + gridStep s t K n * ∑ j ∈ Finset.range k, Λ / ((mE (Efun n)).im *
            (1 - (s n + j * gridStep s t K n))) * (sz.Bctl n (gridTime s t K n j)) ^ (1 / 2 : ℝ) +
          Λ * (2 * Λ * (sz.Bctl n (gridTime s t K n k)) ^ (1 / 2 : ℝ) *
            (gridStep s t K n * ∑ j ∈ Finset.range k,
              ((mE (Efun n)).im * (1 - (s n + j * gridStep s t K n)))⁻¹) + ρ₁) ^ (1 / 2 : ℝ)) *
          ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) := by
    refine ST_engine (K := K n) (τ := STstopIdx sz s t K Efun D Kf n ω)
      (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁) (Λ := Λ) (C := C)
      (mI := (mE (Efun n)).im)
      (x := fun j (i : STLab sz n) => ‖STgA sz s t K n (Efun n) i.1 i.2 j ω‖)
      (dr := fun j (i : STLab sz n) => ‖STgDrift sz s t K n (Efun n) i.1 i.2 j ω‖)
      (th := fun j (i : STLab sz n) => ‖STthetaOp sz n (Efun n) (gridTime s t K n j) i.1
        (STLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1) i.2‖)
      (el := fun j (i : STLab sz n) =>
        ‖STELKLKM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖)
      (eg := fun j (i : STLab sz n) =>
        ‖STEGtM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖)
      (mart := fun k (i : STLab sz n) => ‖Mart i k ω‖)
      (remk := fun k (i : STLab sz n) => ‖Rem i k ω‖)
      (ee := fun j (i : STLab sz n) =>
        ‖STEEM sz n (Efun n) (gridTime s t K n j) (pathH sz s t K n j ω) i.1 i.2‖)
      (P := fun j (i : STLab sz n) => STprof sz n (gridTime s t K n j) D
        (Kf n (gridTime s t K n j)) (i.2 0) (i.2 1))
      (Jh := fun j => STJhatM sz n (Efun n) D (Kf n (gridTime s t K n j)) (gridTime s t K n j)
        (pathH sz s t K n j ω))
      (b := fun j => sz.Bctl n (gridTime s t K n j))
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact hΔ
    · exact hsK
    · exact hmI
    · exact hΛ
    · exact hC
    · exact ha₀
    · exact hr₀
    · exact hρ₁
    · exact hbpos
    · exact hb1'
    · exact hbmono
    · exact fun j i hj => hPpos j i
    · exact hPm
    · exact hJh0
    · exact hJhsup
    · exact hτK
    · exact hbelow
    · exact hhit
    · exact hdec
    · exact hdr
    · exact fun j i hj => (hnewk j hj i).1
    · exact fun j i hj => hel j i hj
    · exact fun j i hj => hg.lw j hj i
    · exact fun j i hj => hg.mg j hj i
    · exact fun j i => norm_nonneg _
    · exact fun i k hk => hg.mart i k hk
    · exact fun i k hk => hg.rem i k hk
    · exact fun i => hg.init i
    · exact hclose
  refine ⟨hmain.1, fun k hk => (hmain.2 k hk).trans ?_⟩
  have hk1 : s n + (k : ℝ) * gridStep s t K n < 1 := by
    have := hu_lt k hk; simpa [gridTime] using this
  have hα := ST_alpha_bound (k := k) (Δ := gridStep s t K n) (s := s n) (a₀ := a₀) (r₀ := r₀)
    (ρ₁ := ρ₁) (Λ := Λ) (mI := (mE (Efun n)).im)
    (b := fun j => sz.Bctl n (gridTime s t K n j)) hΔ hmI hΛ hρ₁
    (fun j hj => hbpos j (hj.trans hk)) (hbmono.mono (Set.Iic_subset_Iic.mpr hk)) hk1
  have hr1 : 1 ≤ (1 - s n) / (1 - (s n + k * gridStep s t K n)) := by
    have := hrk k hk; simpa [gridTime] using this
  have hR0 : 0 ≤ ((1 - s n) / (1 - (s n + k * gridStep s t K n))) ^ (3 * C) :=
    Real.rpow_nonneg (by linarith) _
  have hα' := ST_alpha'_le (b := sz.Bctl n (gridTime s t K n k)) (q := q)
    (L := Real.log ((1 - s n) / (1 - (s n + k * gridStep s t K n)))) (Λ := Λ)
    (mI := (mE (Efun n)).im) (a₀ := a₀) (r₀ := r₀) (ρ₁ := ρ₁) (hbpos k hk) (hb1' k hk) hΛ hmI
    (Real.log_nonneg hr1) hq0 (ha.trans (hqb k hk)) (hr.trans (hqb k hk)) (hρb k hk) hρ₁
  have hfin := mul_le_mul_of_nonneg_right (hα.trans hα') hR0
  simpa [gridTime] using hfin


end Good

end RBM.Gauss.Sizes

/-! ## Compiled nonempty instances at `d = 3` (CLAUDE.md §4 step 2)

Data: `sz0` (`Defs/Sizes.lean`) at `n = 100` (`L = 404`, `W = 202^5`, `lam = 202^{-6}`), `E = 0`
(`mE 0 = I`), `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16` (`Δ = 1/256`).  The pin `STNewKLKAt` and the good event
`STGoodAt` of `ST_good_engine` stay hypotheses of its example. -/

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss.SizesInst RBM.Path

section Instances

private def sI : ℕ → ℝ := fun _ => 0
private def tI : ℕ → ℝ := fun _ => 1 / 16
private def KI : ℕ → ℕ := fun _ => 16

private theorem lam_pos (n : ℕ) : 0 < sz0.lam n := by
  change 0 < ((2 * ((n : ℝ) + 1)) ^ 6)⁻¹
  positivity

private theorem L100_real : ((sz0.L 100 : ℕ) : ℝ) = 404 := by
  change (((4 * (100 + 1) : ℕ)) : ℝ) = 404
  norm_num

private theorem one_le_L100 : (1 : ℝ) ≤ ((sz0.L 100 : ℕ) : ℝ) := by rw [L100_real]; norm_num

private theorem W100_real : ((sz0.W 100 : ℕ) : ℝ) = 202 ^ 5 := by
  change (((2 * (100 + 1)) ^ 5 : ℕ) : ℝ) = 202 ^ 5
  norm_num


/-! ### Section 3: the real-number core, `Δ = 1/16`, `K = 4` -/


example : 1 ≤ ∏ j ∈ Finset.range 4, (1 + (1 / 16 : ℝ) * ((j : ℝ) + 1)) :=
  ST_one_le_prod (k := 4) (Δ := 1 / 16) (β := fun j => (j : ℝ) + 1) (by norm_num)
    (fun j _ => by positivity)

example : ∀ k, k ≤ 4 → (fun _ : ℕ => (1 : ℝ)) k ≤
    (fun _ : ℕ => (1 : ℝ)) k * ∏ j ∈ Finset.range k, (1 + (1 / 16 : ℝ) * (fun _ : ℕ => (1 : ℝ)) j) :=
  ST_gronwall (m := 4) (Δ := 1 / 16) (by norm_num) (α := fun _ => 1) (β := fun _ => 1)
    (J := fun _ => 1) (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one)
    (fun k _ => by
      have : (0 : ℝ) ≤ (1 / 16 : ℝ) * ∑ j ∈ Finset.range k, (1 : ℝ) * 1 := by positivity
      linarith)

example : 4 = 4 ∧ ∀ k, k ≤ 4 → (fun _ : ℕ => (1 : ℝ)) k ≤
    (fun _ : ℕ => (1 : ℝ)) k * ∏ j ∈ Finset.range k, (1 + (1 / 16 : ℝ) * (fun _ : ℕ => (1 : ℝ)) j) :=
  ST_bootstrap (K := 4) (τ := 4) (Δ := 1 / 16) (by norm_num) (α := fun _ => 1) (β := fun _ => 1)
    (J := fun _ => 1) (θ := fun _ => 10) (fun _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one)
    le_rfl (fun h => absurd h (lt_irrefl _))
    (fun k _ _ => by
      have : (0 : ℝ) ≤ (1 / 16 : ℝ) * ∑ j ∈ Finset.range k, (1 : ℝ) * 1 := by positivity
      linarith)
    (fun k hk => by
      simp only [one_mul, mul_one, Finset.prod_const, Finset.card_range]
      have h1 : ((1 : ℝ) + 1 / 16) ^ k ≤ (1 + 1 / 16) ^ 4 := pow_le_pow_right₀ (by norm_num) hk
      have : ((1 : ℝ) + 1 / 16) ^ 4 < 10 := by norm_num
      linarith)

example : (1 / 16 : ℝ) * (1 : ℝ)⁻¹ ≤ Real.log (1 / (1 - 1 / 16)) :=
  ST_logstep (x := 1) (Δ := 1 / 16) (by norm_num) (by norm_num)

example : (1 / 16 : ℝ) * ∑ j ∈ Finset.range 4, (1 - (0 + (j : ℝ) * (1 / 16)))⁻¹ ≤
    Real.log ((1 - 0) / (1 - (0 + (4 : ℕ) * (1 / 16)))) :=
  ST_logsum (s := 0) (Δ := 1 / 16) (by norm_num) 4 (by norm_num)

example : ∏ j ∈ Finset.range 4, (1 + (1 / 16 : ℝ) * (1 * (1 - (0 + (j : ℝ) * (1 / 16)))⁻¹)) ≤
    ((1 - 0) / (1 - (0 + (4 : ℕ) * (1 / 16 : ℝ)))) ^ (1 : ℝ) :=
  ST_prod_le_rpow (s := 0) (Δ := 1 / 16) (c := 1) (by norm_num) (by norm_num) (k := 4)
    (by norm_num)

example : ∀ k, k ≤ 4 → k ≤ 4 →
    (fun _ : ℕ => (1 / 10 : ℝ)) k ≤ ((1 / 10 : ℝ) + 1 / 10 + (1 / 16 : ℝ) * ∑ _j ∈ Finset.range k, (0 : ℝ)
      + (fun _ : ℕ => (0 : ℝ)) k) + (1 / 16 : ℝ) * ∑ j ∈ Finset.range k, (fun _ : ℕ => (1 : ℝ)) j * (fun _ : ℕ => (1 / 10 : ℝ)) j :=
  ST_pathwise_ineq (ι := Unit) (K := 4) (τ := 4) (Δ := 1 / 16) (a₀ := 1 / 10) (r₀ := 1 / 10)
    (x := fun _ _ => 1 / 10) (dr := fun _ _ => 0) (mart := fun _ _ => 0) (P := fun _ _ => 1)
    (remk := fun _ _ => 0) (Jh := fun _ => 1 / 10) (β := fun _ => 1) (e := fun _ => 0)
    (m := fun _ => 0) (by norm_num) (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    (fun k B _ h => by simpa using h ()) (fun _ _ _ => zero_lt_one)
    (fun _ _ _ _ _ _ => le_rfl) (fun _ _ => zero_le_one) (fun _ _ => le_rfl)
    (fun i k _ _ => by simp) (fun i => by norm_num) (fun i j _ => by norm_num)
    (fun i k _ => by norm_num) (fun i k _ => by norm_num)

example : MonotoneOn (fun k => (1 / 10 : ℝ) + 1 / 10 + (1 / 16 : ℝ) * ∑ j ∈ Finset.range k, (fun _ : ℕ => (1 : ℝ)) j
      + (fun k : ℕ => (k : ℝ)) k) (Set.Iic 4) :=
  ST_alpha_mono (K := 4) (Δ := 1 / 16) (a₀ := 1 / 10) (r₀ := 1 / 10) (e := fun _ => 1)
    (m := fun k => (k : ℝ)) (by norm_num) (fun _ _ => zero_le_one)
    (fun a _ b _ h => Nat.cast_le.mpr h)


/-! ### Section 4: tails at `d = 3`, `L = 404`, `lam = 202^{-6}`, `W = 202^5` (`n = 100`) -/

example : tailT 3 (sz0.L 100) (sz0.lam 100) 0 1 ≤ tailT 3 (sz0.L 100) (sz0.lam 100) (1 / 16) 1 :=
  ST_tailT_mono_time one_le_L100 (lam_pos 100).le (by norm_num) (by norm_num) (by norm_num)

example : tailW 3 (sz0.L 100) (sz0.lam 100) 0 1 ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 ≤
    tailW 3 (sz0.L 100) (sz0.lam 100) (1 / 16) 1 ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 :=
  ST_tailW_mono_time one_le_L100 (lam_pos 100).le (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (ST_tailT_mono_time one_le_L100 (lam_pos 100).le (by norm_num) (by norm_num) (by norm_num))

example : (1 / 2 : ℝ) * tailW 3 (sz0.L 100) (sz0.lam 100) 0 1 ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 ≤
    tailW 3 (sz0.L 100) (sz0.lam 100) 0 1 ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 := by
  refine ST_tailW_scale_step (by positivity) (by norm_num) le_rfl (by norm_num)
    (by norm_num) ?_ (by norm_num)
  have h0 := tailT_nonneg (d := 3) (L := sz0.L 100) (g := sz0.lam 100) (t := 0) (r := 1)
    (by norm_num)
  linarith

example : tailW 3 (sz0.L 100) (sz0.lam 100) 0 ((sz0.L 100 : ℕ) : ℝ) ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 ≤
    tailW 3 (sz0.L 100) (sz0.lam 100) 0 1 ((sz0.W 100 : ℕ) : ℝ) (1 / 2) 1 :=
  ST_tailW_L_le (by norm_num) (by norm_num) one_le_L100

/-- `𝒯_0(404) ≤ 1 = W^{-0}` at `n = 100`. -/
private theorem tailT_le_one : tailT 3 (sz0.L 100) (sz0.lam 100) 0 (404 : ℝ) ≤ 1 := by
  unfold tailT BparamR
  have hlam := lam_pos 100
  have hex : Real.exp (-Real.sqrt (404 / ellT (sz0.L 100) (sz0.lam 100) 0)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
  have hB : (sz0.lam 100 ^ 2 + |1 - (0 : ℝ)|)⁻¹ * (((404 : ℝ) + 1) ^ (3 - 2))⁻¹ +
      (((sz0.L 100 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹ ≤ 1 := by
    rw [L100_real]
    simp only [sub_zero, abs_one, mul_one]
    have h1 : (sz0.lam 100 ^ 2 + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith)
    have : ((404 : ℝ) + 1) ^ (3 - 2) = 405 := by norm_num
    rw [this]
    have h2 : (sz0.lam 100 ^ 2 + 1)⁻¹ * (405 : ℝ)⁻¹ ≤ 1 * (405 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by norm_num)
    have h3 : ((404 : ℝ) ^ 3)⁻¹ ≤ 1 / 100 := by norm_num
    have h4 : (405 : ℝ)⁻¹ ≤ 1 / 100 := by norm_num
    linarith
  calc _ ≤ ((sz0.lam 100 ^ 2 + |1 - (0 : ℝ)|)⁻¹ * (((404 : ℝ) + 1) ^ (3 - 2))⁻¹ +
      (((sz0.L 100 : ℕ) : ℝ) ^ 3 * |1 - (0 : ℝ)|)⁻¹) * 1 := by
        gcongr
    _ ≤ 1 := by linarith

example : tailW 3 (sz0.L 100) (sz0.lam 100) 0 404 ((sz0.W 100 : ℕ) : ℝ) 0 1 =
    max (tailT 3 (sz0.L 100) (sz0.lam 100) 0 1) (((sz0.W 100 : ℕ) : ℝ) ^ (-(0 : ℝ))) :=
  ST_tailW_final (by norm_num) (by simpa using tailT_le_one)


/-! ### Section 5: the transfer lemmas -/

example : gridTime sI tI KI 0 3 ∈ Set.Icc (sI 0) (tI 0) :=
  ST_gridTime_mem sI tI KI 0 3 (by norm_num [sI, tI]) (by norm_num [KI]) (by norm_num [KI])

private theorem meas_S (n : ℕ) : MeasurableSet {H : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ | ‖H 0 0‖ ≤ 1} :=
  measurableSet_le (measurable_norm.comp ((measurable_pi_apply (0 : Idx 3 (sz0.L n) (sz0.W n))).comp (measurable_pi_apply (0 : Idx 3 (sz0.L n) (sz0.W n))))) measurable_const

example : pathP sz0 {ω | pathH sz0 sI tI KI 7 7 ω ∈ {H | ‖H 0 0‖ ≤ 1}} =
    Sizes.seqP sz0 {ω | sz0.seqHflow 7 (gridTime sI tI KI 7 7) ω ∈ {H | ‖H 0 0‖ ≤ 1}} :=
  ST_pathP_eq_seqP sz0 sI tI KI 7 7 (by norm_num [sI]) (by norm_num [sI, tI]) (by norm_num [KI]) (meas_S 7)

private abbrev VI : ℕ → Type := fun _ => Fin 1

private theorem sI_nonneg (n : ℕ) : 0 ≤ sI n := le_rfl
private theorem sI_le (n : ℕ) : sI n ≤ tI n := by norm_num [sI, tI]
private theorem KI_ne (n : ℕ) : KI n ≠ 0 := by norm_num [KI]

private theorem size_ge_17 (n : ℕ) : (((Finset.range 17).card * Fintype.card (Fin 1) : ℕ) : ℝ) ≤
    ((sz0.size n : ℕ) : ℝ) ^ (1 : ℝ) := by
  have h : 17 ≤ sz0.size n := by
    have h1 : 32 ≤ sz0.W n := by
      have := InductionDefsInst.W_ge_32 n
      exact_mod_cast this
    have h2 : 4 ≤ sz0.L n := by change 4 ≤ 4 * (n + 1); omega
    have h3 : 1 ≤ sz0.W n * sz0.L n := by nlinarith
    calc 17 ≤ sz0.W n * sz0.L n := by nlinarith
      _ ≤ (sz0.W n * sz0.L n) ^ 3 := Nat.le_self_pow (by norm_num) _
      _ = sz0.size n := rfl
  simp only [Finset.card_range, Fintype.card_fin, mul_one, Real.rpow_one]
  exact_mod_cast h

/-- **(5.2)** at `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`, `J_n = {0,…,16}`, one label, `F ≡ 0`, `Z ≡ 1`. -/
example : Gauss.HighProbAt (pathP sz0) sz0.size (fun n => {ω | ∀ j ∈ Finset.range (KI n + 1), ∀ v : Fin 1,
      (fun (n : ℕ) (_ : VI n) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (0 : ℝ)) n v (gridTime sI tI KI n j) (pathH sz0 sI tI KI n j ω) ≤
        ((sz0.size n : ℕ) : ℝ) ^ (0 : ℝ) * (fun (n : ℕ) (_ : VI n) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (1 : ℝ)) n v (gridTime sI tI KI n j) (pathH sz0 sI tI KI n j ω)}) :=
  ST_whp_grid sz0 (V := VI) sI tI KI sI_nonneg sI_le KI_ne (fun n => Finset.range (KI n + 1))
    (C := 1) (by norm_num) (Eventually.of_forall fun n => by simpa [KI] using size_ge_17 n)
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 1) (fun _ _ _ => measurable_const)
    (fun _ _ _ => measurable_const) 0 (fun D _ => Eventually.of_forall fun n j _ v => by simp [show ¬ ((1 : ℝ) < 0) by norm_num])

/-- **(5.3)** with `F ≡ 0`, `Z ≡ 1` (the premise is the whole space). -/
example : ∀ D : ℝ, 0 < D → ∀ᶠ n in atTop,
      Sizes.seqP sz0 {ω | ((sz0.size n : ℕ) : ℝ) ^ (0 : ℝ) * (fun (n : ℕ) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (1 : ℝ)) n (tI n) (sz0.seqHflow n (tI n) ω) <
        (fun (n : ℕ) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (0 : ℝ)) n (tI n) (sz0.seqHflow n (tI n) ω)} ≤
        ENNReal.ofReal (((sz0.size n : ℕ) : ℝ) ^ (-D)) :=
  ST_model_of_whp_grid sz0 sI tI KI sI_nonneg sI_le KI_ne (fun _ _ _ => 0) (fun _ _ _ => 1)
    (fun _ _ => measurable_const) (fun _ _ => measurable_const) 0
    (by
      have h : (fun n => {ω : PathΩ sz0 | (fun (n : ℕ) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (0 : ℝ)) n (tI n) (pathH sz0 sI tI KI n (KI n) ω) ≤
          ((sz0.size n : ℕ) : ℝ) ^ (0 : ℝ) * (fun (n : ℕ) (_ : ℝ) (_ : Matrix (Idx 3 (sz0.L n) (sz0.W n)) (Idx 3 (sz0.L n) (sz0.W n)) ℂ) => (1 : ℝ)) n (tI n) (pathH sz0 sI tI KI n (KI n) ω)}) =
          fun _ => Set.univ := by
        funext n
        ext ω
        simp
      rw [h]
      exact Gauss.highProbAt_univ _ _)

/-- **(5.4)** `F ≡ 0 ≤ 1 ≡ Z` over `[s,t] × Fin 1`. -/
example : sz0.PrecPT (U := fun n => TimeIcc sI tI n × Fin 1)
    (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ)) :=
  ST_PT_of_sections sz0 (V := VI) (s := sI) (t := tI) sI_le (fun _ _ _ => (0 : ℝ))
    (fun _ _ _ => (1 : ℝ))
    (fun _ => sz0.prec_of_le (fun _ _ _ => zero_le_one) (fun _ _ _ => zero_le_one))

/-- **(5.5)** the converse, at the section `tt n = s_n`. -/
example : sz0.Prec (U := VI) (fun n v ω => (fun (n : ℕ) (_ : TimeIcc sI tI n × Fin 1) (_ : Sizes.SeqΩ sz0) => (0 : ℝ)) n (⟨sI n, le_rfl, sI_le n⟩, v) ω)
    (fun n v ω => (fun (n : ℕ) (_ : TimeIcc sI tI n × Fin 1) (_ : Sizes.SeqΩ sz0) => (1 : ℝ)) n (⟨sI n, le_rfl, sI_le n⟩, v) ω) :=
  ST_sections_of_PT sz0 (V := VI) (s := sI) (t := tI) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (1 : ℝ))
    (C := 0) le_rfl (Eventually.of_forall fun n => by simp)
    (sz0.precPT_of_le (fun _ _ _ => zero_le_one) (fun _ _ _ => zero_le_one))
    (fun n => ⟨sI n, le_rfl, sI_le n⟩)


/-! ### Sections 6 and 8: the engine and `ST_good_engine` -/

/-- `((1/10)^{mk})^{1/k} = (1/10)^m`. -/
private theorem tenth_rpow (m k : ℕ) (hk : k ≠ 0) :
    (((1 / 10 : ℝ) ^ (m * k)) ^ (1 / (k : ℝ))) = (1 / 10) ^ m := by
  rw [pow_mul, one_div (k : ℝ)]
  exact Real.pow_rpow_inv_natCast (by positivity) hk

private theorem c30 : (((1 / 10 : ℝ) ^ 30) ^ (1 / 30 : ℝ)) = 1 / 10 := by
  have := tenth_rpow 1 30 (by norm_num)
  norm_num at this ⊢

private theorem c5 : (((1 / 10 : ℝ) ^ 30) ^ (1 / 5 : ℝ)) = (1 / 10) ^ 6 := by
  have := tenth_rpow 6 5 (by norm_num)
  norm_num at this ⊢

private theorem c6 : (((1 / 10 : ℝ) ^ 30) ^ (1 / 6 : ℝ)) = (1 / 10) ^ 5 := by
  have := tenth_rpow 5 6 (by norm_num)
  norm_num at this ⊢

/-- the closure at `s = 0`, `Δ = 1/256`, `q = 1/10`, `Λ = C = 1`, `mI = 1`, `b ≤ 10^{-30}`:
`(3+3/mI) Λ² (1+q+log r) r^{3C} b^{1/30} < 1` for `1 ≤ r ≤ 16/15`. -/
private theorem core_small {b r : ℝ} (hb0 : 0 < b) (hb : b ≤ (1 / 10 : ℝ) ^ 30) (hr1 : 1 ≤ r)
    (hr : r ≤ 16 / 15) :
    (3 + 3 * (1 : ℝ)⁻¹) * (1 : ℝ) ^ 2 * (1 + 1 / 10 + Real.log r) * r ^ (3 * (1 : ℝ)) *
      b ^ (1 / 30 : ℝ) < 1 := by
  have hb30 : b ^ (1 / 30 : ℝ) ≤ 1 / 10 := by
    calc b ^ (1 / 30 : ℝ) ≤ ((1 / 10 : ℝ) ^ 30) ^ (1 / 30 : ℝ) :=
          Real.rpow_le_rpow hb0.le hb (by norm_num)
      _ = 1 / 10 := c30
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hlog : Real.log r ≤ 1 / 15 := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < r)
    linarith
  have hr3 : r ^ (3 * (1 : ℝ)) ≤ (16 / 15) ^ 3 := by
    have : r ^ (3 * (1 : ℝ)) = r ^ 3 := by norm_num
    rw [this]
    exact pow_le_pow_left₀ (by linarith) hr 3
  have hr30 : 0 ≤ r ^ (3 * (1 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hb0' : 0 ≤ b ^ (1 / 30 : ℝ) := Real.rpow_nonneg hb0.le _
  have h1 : (1 + 1 / 10 + Real.log r) * r ^ (3 * (1 : ℝ)) ≤ (1 + 1 / 10 + 1 / 15) * (16 / 15) ^ 3 :=
    mul_le_mul (by linarith) hr3 hr30 (by norm_num)
  have h2 : (1 + 1 / 10 + Real.log r) * r ^ (3 * (1 : ℝ)) * b ^ (1 / 30 : ℝ) ≤
      (1 + 1 / 10 + 1 / 15) * (16 / 15) ^ 3 * (1 / 10) :=
    mul_le_mul h1 hb30 hb0' (by norm_num)
  calc (3 + 3 * (1 : ℝ)⁻¹) * (1 : ℝ) ^ 2 * (1 + 1 / 10 + Real.log r) * r ^ (3 * (1 : ℝ)) *
      b ^ (1 / 30 : ℝ) = 6 * ((1 + 1 / 10 + Real.log r) * r ^ (3 * (1 : ℝ)) * b ^ (1 / 30 : ℝ)) := by
        norm_num; ring
    _ ≤ 6 * ((1 + 1 / 10 + 1 / 15) * (16 / 15) ^ 3 * (1 / 10)) := by linarith
    _ < 1 := by norm_num

/-- grid points `u_k = k/256 ≤ 1/16` give `1 ≤ r ≤ 16/15`. -/
private theorem r_bounds {k : ℕ} (hk : k ≤ 16) :
    1 ≤ (1 - 0 : ℝ) / (1 - (0 + (k : ℝ) * (1 / 256))) ∧
      (1 - 0 : ℝ) / (1 - (0 + (k : ℝ) * (1 / 256))) ≤ 16 / 15 := by
  have hk' : (k : ℝ) ≤ 16 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hpos : 0 < 1 - (0 + (k : ℝ) * (1 / 256)) := by linarith
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

private theorem one_sub_pos {j : ℕ} (hj : j ≤ 16) : (0 : ℝ) < 1 - (0 + (j : ℝ) * (1 / 256)) := by
  have hj' : (j : ℝ) ≤ 16 := by exact_mod_cast hj
  linarith

/-- the engine at `K = 16`, `Δ = 1/256`, `s = 0`, one label, `b ≡ 10^{-30}`, `a₀ = r₀ = q b^{1/5}`. -/
example : 16 = 16 ∧ ∀ k, k ≤ 16 →
    (fun _ : ℕ => (1 / 10 * (1 / 10 : ℝ) ^ 6)) k ≤
      ((1 / 10 * (1 / 10 : ℝ) ^ 6) + (1 / 10 * (1 / 10 : ℝ) ^ 6) +
        (1 / 256 : ℝ) * ∑ j ∈ Finset.range k, (1 : ℝ) / (1 * (1 - (0 + (j : ℝ) * (1 / 256)))) *
          ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) +
        1 * (2 * 1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) *
          ((1 / 256 : ℝ) * ∑ j ∈ Finset.range k, (1 * (1 - (0 + (j : ℝ) * (1 / 256))))⁻¹) +
            (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) ^ (1 / 2 : ℝ)) *
        ((1 - 0) / (1 - (0 + (k : ℝ) * (1 / 256)))) ^ (3 * (1 : ℝ)) := by
  have hc0 : (0 : ℝ) < (1 / 10 : ℝ) ^ 30 := by positivity
  have hc1 : ((1 / 10 : ℝ) ^ 30) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  refine ST_engine (ι := Unit) (K := 16) (τ := 16) (Δ := 1 / 256) (s := 0)
    (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (Λ := 1) (C := 1) (mI := 1)
    (x := fun _ _ => 1 / 10 * (1 / 10 : ℝ) ^ 6) (dr := fun _ _ => 0) (th := fun _ _ => 0)
    (el := fun _ _ => 0) (eg := fun _ _ => 0) (mart := fun _ _ => 0) (remk := fun _ _ => 0)
    (ee := fun _ _ => 0) (P := fun _ _ => 1) (Jh := fun _ => 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (b := fun _ => (1 / 10 : ℝ) ^ 30)
    (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num) (by positivity)
    (by positivity) (by positivity) (fun _ _ => hc0) (fun _ _ => hc1)
    (fun _ _ _ _ _ => le_rfl) (fun _ _ _ => zero_lt_one) (fun _ _ _ _ _ _ => le_rfl)
    (fun _ _ => by positivity) (fun k B _ h => by simpa using h ()) le_rfl
    (fun j hj => by
      show 1 / 10 * (1 / 10 : ℝ) ^ 6 < ((1 / 10 : ℝ) ^ 30) ^ (1 / 6 : ℝ)
      rw [c6]; norm_num)
    (fun h => absurd h (by norm_num)) (fun i k _ _ => by simp) (fun j i => by simp)
    (fun j i hj => mul_nonneg (mul_nonneg (div_nonneg zero_le_one (one_sub_pos hj).le) (by positivity)) (by norm_num))
    (fun j i hj => mul_nonneg (mul_nonneg (div_nonneg zero_le_one (one_sub_pos hj).le) (by positivity)) (by norm_num))
    (fun j i hj => mul_nonneg (mul_nonneg (div_nonneg zero_le_one (mul_nonneg zero_le_one (one_sub_pos hj).le)) (by positivity)) (by norm_num))
    (fun j i hj => mul_nonneg (mul_nonneg (div_nonneg zero_le_one (mul_nonneg zero_le_one (one_sub_pos hj).le)) (by positivity)) (by norm_num))
    (fun j i => le_rfl) (fun i k _ => by positivity) (fun i k _ => by positivity)
    (fun i => by simp) ?_
  intro k hk
  have hrb := r_bounds hk
  have hR0 : 0 ≤ ((1 - 0 : ℝ) / (1 - (0 + (k : ℝ) * (1 / 256)))) ^ (3 * (1 : ℝ)) :=
    Real.rpow_nonneg (by linarith [hrb.1]) _
  have hα := ST_alpha_bound (k := k) (Δ := 1 / 256) (s := 0) (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (Λ := 1) (mI := 1)
    (b := fun _ => (1 / 10 : ℝ) ^ 30) (by norm_num) (by norm_num) le_rfl (by positivity)
    (fun _ _ => hc0) (fun a _ b _ _ => le_rfl) (by
      have : (k : ℝ) ≤ 16 := by exact_mod_cast hk
      linarith)
  have hcl := ST_closure_arith (b := (1 / 10 : ℝ) ^ 30) (q := 1 / 10)
    (L := Real.log ((1 - 0 : ℝ) / (1 - (0 + (k : ℝ) * (1 / 256))))) (Λ := 1) (mI := 1)
    (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (R := ((1 - 0 : ℝ) / (1 - (0 + (k : ℝ) * (1 / 256)))) ^ (3 * (1 : ℝ)))
    hc0 hc1 le_rfl (by norm_num) (Real.log_nonneg hrb.1) (by norm_num) hR0
    (by rw [c5]) (by rw [c5]) (by rw [c5]) (by positivity)
    (core_small hc0 le_rfl hrb.1 hrb.2)
  rw [c6]
  rw [c6] at hcl
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα hR0) hcl

example : ((1 : ℝ) / 4) ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) :=
  ST_rpow_half_mono (by norm_num) (by norm_num)

example : ((1 : ℝ) / 4 + 1 / 9) ^ (1 / 2 : ℝ) ≤ ((1 : ℝ) / 4) ^ (1 / 2 : ℝ) + ((1 : ℝ) / 9) ^ (1 / 2 : ℝ) :=
  ST_rpow_half_add_le (by norm_num) (by norm_num)

example : ((1 / 10 : ℝ) ^ 6) ^ 3 ≤ ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) :=
  ST_cube_le (by positivity) (by positivity) (by rw [c6]; norm_num)

/-- `ST_alpha_bound` at `k = 16`, `Δ = 1/256`, `s = 0`, `b ≡ 10^{-30}`. -/
example : (1 / 10 * (1 / 10 : ℝ) ^ 6) + (1 / 10 * (1 / 10 : ℝ) ^ 6) +
        (1 / 256 : ℝ) * ∑ j ∈ Finset.range 16, (1 : ℝ) / (1 * (1 - (0 + (j : ℝ) * (1 / 256)))) *
          ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) +
        1 * (2 * 1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) *
          ((1 / 256 : ℝ) * ∑ j ∈ Finset.range 16, (1 * (1 - (0 + (j : ℝ) * (1 / 256))))⁻¹) +
            (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) ^ (1 / 2 : ℝ) ≤
      (1 / 10 * (1 / 10 : ℝ) ^ 6) + (1 / 10 * (1 / 10 : ℝ) ^ 6) +
        1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) *
          ((1 : ℝ)⁻¹ * Real.log ((1 - 0) / (1 - (0 + ((16 : ℕ) : ℝ) * (1 / 256))))) +
        1 * (2 * 1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) *
          ((1 : ℝ)⁻¹ * Real.log ((1 - 0) / (1 - (0 + ((16 : ℕ) : ℝ) * (1 / 256))))) +
            (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) ^ (1 / 2 : ℝ) :=
  ST_alpha_bound (k := 16) (Δ := 1 / 256) (s := 0) (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (Λ := 1) (mI := 1)
    (b := fun _ => (1 / 10 : ℝ) ^ 30) (by norm_num) (by norm_num) le_rfl (by positivity)
    (fun _ _ => by positivity) (fun a _ b _ _ => le_rfl) (by norm_num)

/-- `ST_alpha'_le` at `b = 10^{-30}`, `q = 1/10`, `L = log (16/15)`. -/
example : (1 / 10 * (1 / 10 : ℝ) ^ 6) + (1 / 10 * (1 / 10 : ℝ) ^ 6) +
      1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) * ((1 : ℝ)⁻¹ * Real.log (16 / 15)) +
        1 * (2 * 1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) * ((1 : ℝ)⁻¹ * Real.log (16 / 15)) +
          (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) ^ (1 / 2 : ℝ) ≤
      ((3 + 3 * (1 : ℝ)⁻¹) * 1 ^ 2 * (1 + 1 / 10 + Real.log (16 / 15))) *
        ((1 / 10 : ℝ) ^ 30) ^ (1 / 5 : ℝ) :=
  ST_alpha'_le (b := (1 / 10 : ℝ) ^ 30) (q := 1 / 10) (L := Real.log (16 / 15)) (Λ := 1) (mI := 1)
    (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) le_rfl (by norm_num)
    (Real.log_nonneg (by norm_num)) (by norm_num) (by rw [c5]) (by rw [c5]) (by rw [c5])
    (by positivity)

/-- `ST_closure_arith` at the same data, `R = (16/15)^{3}`. -/
example : ((1 / 10 * (1 / 10 : ℝ) ^ 6) + (1 / 10 * (1 / 10 : ℝ) ^ 6) +
      1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) * ((1 : ℝ)⁻¹ * Real.log (16 / 15)) +
        1 * (2 * 1 * ((1 / 10 : ℝ) ^ 30) ^ (1 / 2 : ℝ) * ((1 : ℝ)⁻¹ * Real.log (16 / 15)) +
          (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) ^ (1 / 2 : ℝ)) * ((16 / 15 : ℝ) ^ (3 * (1 : ℝ))) <
      ((1 / 10 : ℝ) ^ 30) ^ (1 / 6 : ℝ) :=
  ST_closure_arith (b := (1 / 10 : ℝ) ^ 30) (q := 1 / 10) (L := Real.log (16 / 15)) (Λ := 1)
    (mI := 1) (a₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6) (r₀ := 1 / 10 * (1 / 10 : ℝ) ^ 6)
    (ρ₁ := (1 / 10 * (1 / 10 : ℝ) ^ 6) ^ 2) (R := (16 / 15 : ℝ) ^ (3 * (1 : ℝ))) (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num)) le_rfl (by norm_num)
    (Real.log_nonneg (by norm_num)) (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    (by rw [c5]) (by rw [c5]) (by rw [c5]) (by positivity)
    (core_small (by positivity) le_rfl (by norm_num) le_rfl)


private theorem mE_zero_im : (mE 0).im = 1 := by
  have h : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [mE, h]

private theorem gt_eq (n k : ℕ) : gridTime sI tI KI n k = 0 + (k : ℝ) * (1 / 256) := by
  norm_num [gridTime, gridStep, sI, tI, KI]

private theorem gt_le {k : ℕ} (hk : k ≤ 16) : gridTime sI tI KI 100 k ≤ 1 / 16 := by
  rw [gt_eq]
  have : (k : ℝ) ≤ 16 := by exact_mod_cast hk
  linarith

/-- `W^{-3} B_{c,0} ≤ 10^{-30}` for `c ≤ 1/16`, `n = 100`. -/
private theorem Bctl_small {c : ℝ} (hc : c ≤ 1 / 16) : sz0.Bctl 100 c ≤ (1 / 10 : ℝ) ^ 30 := by
  have h := InductionDefsInst.Bctl_const_le_gen sz0 100 (c := c) (by linarith)
  refine h.trans ?_
  have h1 : (1 - c)⁻¹ ≤ (15 / 16 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  rw [W100_real]
  have h2 : 2 * (1 - c)⁻¹ ≤ 2 * (15 / 16 : ℝ)⁻¹ := by linarith
  calc 2 * (1 - c)⁻¹ * (((202 : ℝ) ^ 5) ^ 3)⁻¹ ≤ 2 * (15 / 16 : ℝ)⁻¹ * (((202 : ℝ) ^ 5) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ ≤ (1 / 10 : ℝ) ^ 30 := by norm_num

private def a0 : ℝ := 1 / 10 * (sz0.Bctl 100 0) ^ (1 / 5 : ℝ)

private theorem a0_nonneg : 0 ≤ a0 :=
  mul_nonneg (by norm_num) (Real.rpow_nonneg (Sizes.STBctl_pos sz0 100 (by norm_num)).le _)

/-- `ST_good_engine` at `d = 3`, `sz0`, `n = 100` (`L = 404`, `W = 202^5`, `lam = 202^{-6}`),
`E = 0`, `s ≡ 0`, `t ≡ 1/16`, `K ≡ 16`, `D = 1/2`, `Kf ≡ 1`, `Λ = C = 1`, `q = 1/10`; the pin `hNew`
and the good event `hg` stay hypotheses. -/
example (δ₀ : ℝ) (ω : PathΩ sz0) (hNew : STNewKLKAt 3 (1 / 10) (1 / 10) 1 δ₀)
    (hg : STGoodAt sz0 sI tI KI 100 0 (1 / 2) (fun _ => 1) 1 δ₀ a0 a0 (a0 ^ 2)
      (fun _ _ _ => 0) (fun _ _ _ => 0) ω) :=
  ST_good_engine sz0 sI tI KI 100 (fun _ => 0) (1 / 2) (fun _ _ => 1) (Λ := 1) (δ₀ := δ₀) (C := 1)
    (a₀ := a0) (r₀ := a0) (ρ₁ := a0 ^ 2) (q := 1 / 10) (κ := 1 / 10) (𝔡 := 1 / 10)
    (by norm_num [KI]) (by norm_num [sI]) (by norm_num [sI, tI]) (by norm_num [tI]) (by norm_num)
    (by rw [mE_zero_im]; norm_num) le_rfl (by norm_num) a0_nonneg a0_nonneg (sq_nonneg _)
    (lam_pos 100) (by
      have : sz0.lam 100 ≤ 1 := by
        change ((2 * (((100 : ℕ) : ℝ) + 1)) ^ 6)⁻¹ ≤ 1
        exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
      linarith) (by norm_num) hNew
    (fun _ _ => by norm_num) (fun _ _ => one_le_L100)
    (fun j k hjk hk => by
      refine ST_tailT_mono_time one_le_L100 (lam_pos 100).le ?_ ?_ (by norm_num)
      · rw [gt_eq, gt_eq]
        have : (j : ℝ) ≤ k := by exact_mod_cast hjk
        linarith
      · have := gt_le hk; linarith)
    (by
      have := Bctl_small (c := tI 100) (by norm_num [tI])
      refine this.trans ?_
      norm_num)
    (by norm_num) le_rfl le_rfl le_rfl
    (fun k hk => by
      have hrb := r_bounds hk
      have hb := Bctl_small (c := gridTime sI tI KI 100 k) (gt_le hk)
      have hb0 : 0 < sz0.Bctl 100 (gridTime sI tI KI 100 k) :=
        Sizes.STBctl_pos sz0 100 (by have := gt_le hk; linarith)
      rw [gt_eq] at hb hb0
      have h := core_small hb0 hb hrb.1 hrb.2
      rw [mE_zero_im]
      simp only [sI]
      rw [gt_eq]
      simpa using h)
    (fun _ _ _ => 0) (fun _ _ _ => 0) ω hg

/-- `ST_firstHit_hit` at `J_k = k`, `θ = 2`, `K = 5`: the first hit is `2 < 5`. -/
example : (2 : ℝ) ≤ (fun (k : ℕ) (_ : Unit) => (k : ℝ)) (firstHit (fun (k : ℕ) (_ : Unit) => (k : ℝ)) 2 5 ()) () :=
  ST_firstHit_hit (fun (k : ℕ) (_ : Unit) => (k : ℝ)) 2 5 (ω := ())
    (lt_of_le_of_lt (MeasureTheory.hittingBtwn_le_of_mem (n := 0) (i := 2) (by norm_num)
      (by norm_num) (by simp)) (by norm_num))

end Instances

end RBM.Gauss.Sizes
