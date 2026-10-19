/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.PfStep5Alg
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.GridDuhamelN

/-!
# The level, the bound `J♯` and the Duhamel form of the stopped hierarchy

Paper: (3.13) `int_K-L_ST`, (3.12) `def_Ustz`, (3.18) `alu9_STime`, (5.41) `def_WTuD`, (5.47)
`eq:def_TTT`, Lemma 5.4 (`lem:pf_step5`; the paper omits the proof, "analogous to, and much simpler than,
`(2.76)` of [YY_25, §5.3]").

The vocabulary and the deterministic grid algebra of `lem:pf_step5`.  Every statement is deterministic,
per `n` and per sample, with no `Prec` and no probability, and nothing is lifted.  The statements
`PfStep5Grid_level_pin`, `PfStep5Grid_Jsharp_pin`, `PfStep5Grid_duhamel_pin` fix the statements of the
theorems; each theorem has the body of the statement of the same name.

* `PfStep5Grid_level W D* u = D* + 2 log_W (1 - u)`: the time-dependent level `D_u`;
  `PfStep5Grid_JsharpM`: `J♯` of a fine matrix (the matrix form of `LemDecCalELip_Jsharp`).
* `pfStep5Grid_level`: `W^{-D_{u'}} = (1-u')^{-2} W^{-D*}`, `D_u` nonincreasing,
  `D_u ≤ D*`, `D_{u'} ≥ D* - 2d` when `1 - u' ≥ W^{-d}`.
* `pfStep5Grid_Jsharp`: `LemDecCalELip_Jsharp` at the flow matrix is `PfStep5Grid_JsharpM`.
* `pfStep5Grid_duhamel`: the Duhamel form `(int_K-L_ST)` from the additive grid
  decomposition (`STGridRepNAt` conjunct 1) with the remainder `64 (1-u_k)^{-7} (R + ΔM)`.

Proof of `pfStep5Grid_duhamel` (the paper gives none): with `B = (1-u_k)^{-1}` and the bounded
operators `P_j = 𝒰_{u_j,u_k}`, `X_j = 𝒰_{u_j,u_{j+1}}`, `Θ_j = Θ^{(2)}_{u_j}` on the sup-normed
tensors, the algebraic telescope `A_k - P_0 A_0 = Σ_j [P_j ΔA_j + ΔP_j A_{j+1}]` (`P_k = 1`),
the decomposition `ΔA_j = Δ(Θ_j A_j + F_j) + ΔRem_j + ΔMart_j` and `P_j = P_{j+1} X_j` leave
`Σ_j P_j ΔRem_j + Σ_j P_{j+1}[(ΔΘ_j + 1 - X_j) A_j + Δ (X_j - 1) Θ_j A_j] + Σ_j ΔP_j ΔA_j`;
the first and the last sum are summed by parts (`pfStep5Grid_abel`), with `‖ΔP_j‖ ≤ 3ΔB⁴` and
the second difference `‖P_{j+2} - 2P_{j+1} + P_j‖ ≤ 17Δ²B⁶`; no increment bound for `A` enters
(`pfStep5Grid_abs`, generic in the space).  The kernel inputs are the one-slot facts
`uKer = 1 + (w-v) thetaKer`, `‖thetaKer_w‖ ≤ B`, the resolvent identity
`‖thetaKer_w - thetaKer_v‖ ≤ (w-v)B²`, the identity `𝒰_{v,w} = (1 + δS₀)(1 + δS₁)` with slot
operators `S_i` (`pfStep5Grid_Uc_expand`) and `Θ^{(2)} = S₀ + S₁` (`pfStep5Grid_ThetaN_eq`).
The semigroup law and `𝒰_{v,v} = 1` are `GridDuhamelN_Ugen_comp`, `_self`.
Every helper is `private` with the prefix `pfStep5Grid_`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Gauss.Sizes

open RBM RBM.Loop RBM.Path RBM.Gauss

/-! ## 0. Vocabulary -/

/-- The time-dependent level `D_u := D* + 2 log_W(1-u)`: `W^{-D_u} = (1-u)^{-2} W^{-D*}`. -/
noncomputable def PfStep5Grid_level (W Dst u : ℝ) : ℝ :=
  Dst + 2 * (Real.log (1 - u) / Real.log W)

/-- The realized bound `J♯ = max(1, max_{σ,a} |(𝓛-𝒦)^{(2)}_{u,σ,a}(H)| / T_{u,D}(|a₁-a₂|))` of a fine matrix `H`
(the matrix form of `LemDecCalELip_Jsharp`, same `sup'`). -/
noncomputable def PfStep5Grid_JsharpM {d : ℕ} (sz : Sizes d) (n : ℕ) (E D u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) : ℝ :=
  max 1 (Finset.univ.sup' ⟨((fun _ => true), (fun _ => 0)), Finset.mem_univ _⟩
    (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
      ‖STLKM sz n E u H p.1 p.2‖ / STtailTD sz n u D p.2))

/-! ## 1. The statements -/

/-- **The level**: for `W > 1`, `u ≤ u' < 1`: `W^{-D_{u'}} = (1-u')^{-2} W^{-D*}`;
`D_u` is nonincreasing in `u`; `D_u ≤ D*` for `u ≥ 0`; `D_{u'} ≥ D* - 2d` when `1 - u' ≥ W^{-d}`. -/
def PfStep5Grid_level_pin : Prop :=
  ∀ (d : ℕ) (W Dst u u' : ℝ), 1 < W → u ≤ u' → u' < 1 →
    W ^ (-(PfStep5Grid_level W Dst u')) = ((1 - u')⁻¹) ^ 2 * W ^ (-Dst) ∧
    PfStep5Grid_level W Dst u' ≤ PfStep5Grid_level W Dst u ∧
    (0 ≤ u → PfStep5Grid_level W Dst u ≤ Dst) ∧
    (W ^ (-(d : ℝ)) ≤ 1 - u' → Dst - 2 * (d : ℝ) ≤ PfStep5Grid_level W Dst u')

/-- **Bridge** (`rfl` after unfolding: `STLM_seqHflow`): the realized bound of the
model at `(n, u, ω)` is the matrix bound at the flow matrix `H_u(ω)`. -/
def PfStep5Grid_Jsharp_pin {d : ℕ} (sz : Sizes d) : Prop :=
  ∀ (E : ℕ → ℝ) (D : ℝ) (n : ℕ) (u : ℝ) (ω : sz.SeqΩ),
    LemDecCalELip_Jsharp sz E D n u ω = PfStep5Grid_JsharpM sz n (E n) D u (sz.seqHflow n u ω)

/-- **The Duhamel form** `(int_K-L_ST)` from the additive grid decomposition of `STGridRepNAt`
conjunct 1 (deterministic, any 2-index tensors): on a grid `u_{j+1} = u_j + Δ`, `0 ≤ u_0`, `u_k < 1`, if
`A_j = A_0 + Δ Σ_{i<j} (Θ^{(2)}_{u_i,σ} A_i + F_i) + Rem_j + Mart_j` for `j ≤ k` with `|A_j| ≤ M`, `|Rem_j| ≤ R`, then
`|A_k - 𝒰_{u_0,u_k} A_0 - Δ Σ_{j<k} 𝒰_{u_j,u_k} F_j - Σ_{j<k} 𝒰_{u_j,u_k}(Mart_{j+1} - Mart_j)| ≤ 64 (1-u_k)^{-7} (R + Δ M)`.
The martingale sum is token for token the one of `STGridRepNAt` conjunct 4 (`Ugen = UN … (fun i => mSigma E (σ i))`). -/
def PfStep5Grid_duhamel_pin (d : ℕ) : Prop :=
  ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ (g E Δ M R : ℝ) (σ : Fin 2 → Bool) (k : ℕ) (u : ℕ → ℝ)
    (A F Rem Mart : ℕ → (Fin 2 → Zd d L) → ℂ),
    |E| ≤ 2 → 0 ≤ Δ → 0 ≤ u 0 → (∀ j, u (j + 1) = u j + Δ) → u k < 1 →
    (∀ j, j ≤ k → ∀ b, ‖A j b‖ ≤ M) → (∀ j, j ≤ k → ∀ b, ‖Rem j b‖ ≤ R) →
    (∀ j, j ≤ k → ∀ b, A j b = A 0 b + (Δ : ℂ) * ∑ i ∈ Finset.range j,
        (ThetaN d L g (fun i' => mSigma E (σ i')) (u i) (A i) b + F i b) + Rem j b + Mart j b) →
    ∀ a, ‖A k a - RBM.Ind.Ugen d L g E σ (u 0) (u k) (A 0) a -
        ∑ j ∈ Finset.range k, (Δ : ℂ) * RBM.Ind.Ugen d L g E σ (u j) (u k) (F j) a -
        ∑ j ∈ Finset.range k,
          RBM.Ind.Ugen d L g E σ (u j) (u k) (fun b => Mart (j + 1) b - Mart j b) a‖ ≤
      64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M)

/-! ## 2. The level and the bridge -/

/-- `0 < log W` for `W > 1` (private helper). -/
private theorem pfStep5Grid_logW_pos {W : ℝ} (hW : 1 < W) : 0 < Real.log W := Real.log_pos hW

/-- **The level**. -/
theorem pfStep5Grid_level : PfStep5Grid_level_pin := by
  intro d W Dst u u' hW huu hu'
  have hW0 : 0 < W := by linarith
  have hlog : 0 < Real.log W := pfStep5Grid_logW_pos hW
  have h1u' : 0 < 1 - u' := by linarith
  have h1u : 0 < 1 - u := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `W^{-D_{u'}} = (1-u')^{-2} W^{-D*}`
    unfold PfStep5Grid_level
    rw [Real.rpow_def_of_pos hW0, Real.rpow_def_of_pos hW0]
    have e1 : Real.log W * -(Dst + 2 * (Real.log (1 - u') / Real.log W))
        = Real.log W * -Dst - 2 * Real.log (1 - u') := by
      field_simp
      ring
    have e2 : ((1 - u')⁻¹) ^ 2 = Real.exp (-(2 * Real.log (1 - u'))) := by
      have h : Real.exp (2 * Real.log (1 - u')) = (1 - u') ^ 2 := by
        rw [show 2 * Real.log (1 - u') = ((2 : ℕ) : ℝ) * Real.log (1 - u') by norm_num,
          Real.exp_nat_mul, Real.exp_log h1u']
      rw [Real.exp_neg, h, inv_pow]
    rw [e1, e2, ← Real.exp_add]
    congr 1
    ring
  · unfold PfStep5Grid_level
    have hl : Real.log (1 - u') ≤ Real.log (1 - u) := Real.log_le_log h1u' (by linarith)
    have := div_le_div_of_nonneg_right hl hlog.le
    linarith
  · intro hu0
    unfold PfStep5Grid_level
    have hl : Real.log (1 - u) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    have := div_nonpos_of_nonpos_of_nonneg hl hlog.le
    linarith
  · intro hW'
    unfold PfStep5Grid_level
    have hpos : 0 < W ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hW0 _
    have hl := Real.log_le_log hpos hW'
    rw [Real.log_rpow hW0] at hl
    have h2 : -(d : ℝ) ≤ Real.log (1 - u') / Real.log W := by
      rw [le_div_iff₀ hlog]
      linarith
    linarith

/-- **Bridge**. -/
theorem pfStep5Grid_Jsharp {d : ℕ} (sz : Sizes d) : PfStep5Grid_Jsharp_pin sz := by
  intro E D n u ω
  unfold LemDecCalELip_Jsharp PfStep5Grid_JsharpM
  rfl

section Kernel

open scoped Matrix.Norms.Operator

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem pfStep5Grid_abel (W : ℕ → (E →L[ℂ] E)) (A : ℕ → E) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), W j (A (j + 1) - A j) =
      W m (A (m + 1)) - W 0 (A 0) - ∑ j ∈ Finset.range m, (W (j + 1) - W j) (A (j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [map_sub, _root_.sub_apply]
    abel

private theorem pfStep5Grid_tele (P : ℕ → (E →L[ℂ] E)) (A : ℕ → E) (m : ℕ) :
    P m (A m) - P 0 (A 0) = ∑ j ∈ Finset.range m,
      (P j (A (j + 1) - A j) + (P (j + 1) - P j) (A (j + 1))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [map_sub, _root_.sub_apply]
    abel

private theorem pfStep5Grid_sumBound {F : Type*} [SeminormedAddCommGroup F] (n : ℕ) (f : ℕ → F)
    (c : ℝ) (h : ∀ j, j < n → ‖f j‖ ≤ c) : ‖∑ j ∈ Finset.range n, f j‖ ≤ n * c := by
  calc ‖∑ j ∈ Finset.range n, f j‖ ≤ ∑ j ∈ Finset.range n, ‖f j‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n, c :=
        Finset.sum_le_sum fun j hj => h j (Finset.mem_range.mp hj)
    _ = n * c := by simp

/-- per-term algebra -/
private theorem pfStep5Grid_term (Δ : ℝ) (Pj Pj1 Xj Θj : E →L[ℂ] E) (a a' F r r' mm mm' : E)
    (hPX : Pj = Pj1 * Xj)
    (hrec : a' - a = (Δ : ℂ) • (Θj a + F) + (r' - r) + (mm' - mm)) :
    Pj (a' - a) + (Pj1 - Pj) a' - (Δ : ℂ) • Pj F - Pj (mm' - mm)
      = Pj (r' - r)
        + Pj1 ((((Δ : ℂ) • Θj + 1 - Xj) a) + (Δ : ℂ) • ((Xj - 1) (Θj a)))
        + (Pj1 - Pj) (a' - a) := by
  subst hPX
  have h1 : (Pj1 * Xj) (a' - a) = (Pj1 * Xj) ((Δ : ℂ) • (Θj a + F) + (r' - r) + (mm' - mm)) := by
    rw [hrec]
  rw [h1]
  have h2 : a' = a + (a' - a) := by abel
  rw [h2]
  simp only [map_sub, map_add, map_smul, _root_.sub_apply, _root_.add_apply, _root_.smul_apply, mul_apply_eq_comp,
    one_apply_eq_self]
  module


/-- The abstract Duhamel remainder bound, `k = m + 1`. -/
private theorem pfStep5Grid_abs (m : ℕ) (Δ B M R : ℝ) (hB : 1 ≤ B) (hΔ : 0 ≤ Δ)
    (hmΔ : ((m : ℝ) + 1) * Δ ≤ 1)
    (P X Θ : ℕ → (E →L[ℂ] E)) (A F Rem Mart : ℕ → E)
    (hPk : P (m + 1) = 1) (hPX : ∀ j, j < m + 1 → P j = P (j + 1) * X j)
    (hP : ∀ j, j ≤ m + 1 → ‖P j‖ ≤ B ^ 2)
    (hXn : ∀ j, j < m + 1 → ‖X j‖ ≤ B ^ 2)
    (hX1 : ∀ j, j < m + 1 → ‖X j - 1‖ ≤ 3 * Δ * B ^ 2)
    (hX2 : ∀ j, j < m + 1 → ‖X j - 1 - (Δ : ℂ) • Θ j‖ ≤ 3 * Δ ^ 2 * B ^ 2)
    (hΘ : ∀ j, j < m + 1 → ‖Θ j‖ ≤ 2 * B)
    (hΘΘ : ∀ j, j + 1 < m + 1 → ‖Θ j - Θ (j + 1)‖ ≤ 2 * Δ * B ^ 2)
    (hA : ∀ j, j ≤ m + 1 → ‖A j‖ ≤ M) (hRem : ∀ j, j ≤ m + 1 → ‖Rem j‖ ≤ R)
    (hrec : ∀ j, j < m + 1 → A (j + 1) - A j = (Δ : ℂ) • (Θ j (A j) + F j) +
      (Rem (j + 1) - Rem j) + (Mart (j + 1) - Mart j)) :
    ‖A (m + 1) - P 0 (A 0) - (Δ : ℂ) • ∑ j ∈ Finset.range (m + 1), P j (F j)
        - ∑ j ∈ Finset.range (m + 1), P j (Mart (j + 1) - Mart j)‖
      ≤ 64 * B ^ 7 * (R + Δ * M) := by
  have hB0 : 0 ≤ B := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRem 0 (Nat.zero_le _))
  have hΔn : ‖(Δ : ℂ)‖ = Δ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hΔ]
  have hmΔ' : (m : ℝ) * Δ ≤ 1 := by nlinarith
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  -- the increments of `P`
  have hW1 : ∀ j, j < m + 1 → ‖P (j + 1) - P j‖ ≤ 3 * Δ * B ^ 4 := by
    intro j hj
    have h : P (j + 1) - P j = P (j + 1) * (1 - X j) := by
      rw [hPX j hj, mul_sub, mul_one]
    calc ‖P (j + 1) - P j‖ = ‖P (j + 1) * (1 - X j)‖ := by rw [h]
      _ ≤ ‖P (j + 1)‖ * ‖1 - X j‖ := norm_mul_le _ _
      _ ≤ B ^ 2 * (3 * Δ * B ^ 2) :=
          mul_le_mul (hP _ hj) (by rw [norm_sub_rev]; exact hX1 j hj) (norm_nonneg _) (by positivity)
      _ = 3 * Δ * B ^ 4 := by ring
  -- the second differences
  have hXX : ∀ j, j + 1 < m + 1 → ‖X j - X (j + 1)‖ ≤ 8 * Δ ^ 2 * B ^ 2 := by
    intro j hj
    have hj' : j < m + 1 := by omega
    have h : X j - X (j + 1) = (X j - 1 - (Δ : ℂ) • Θ j) - (X (j + 1) - 1 - (Δ : ℂ) • Θ (j + 1))
        + (Δ : ℂ) • (Θ j - Θ (j + 1)) := by
      rw [smul_sub]; abel
    calc ‖X j - X (j + 1)‖
        ≤ ‖(X j - 1 - (Δ : ℂ) • Θ j) - (X (j + 1) - 1 - (Δ : ℂ) • Θ (j + 1))‖
          + ‖(Δ : ℂ) • (Θ j - Θ (j + 1))‖ := by rw [h]; exact norm_add_le _ _
      _ ≤ (‖X j - 1 - (Δ : ℂ) • Θ j‖ + ‖X (j + 1) - 1 - (Δ : ℂ) • Θ (j + 1)‖)
          + Δ * ‖Θ j - Θ (j + 1)‖ := by
            rw [norm_smul, hΔn]
            exact add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (3 * Δ ^ 2 * B ^ 2 + 3 * Δ ^ 2 * B ^ 2) + Δ * (2 * Δ * B ^ 2) :=
          add_le_add (add_le_add (hX2 j hj') (hX2 (j + 1) hj))
            (mul_le_mul_of_nonneg_left (hΘΘ j hj) hΔ)
      _ = 8 * Δ ^ 2 * B ^ 2 := by ring
  have hW2 : ∀ j, j + 1 < m + 1 →
      ‖(P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)‖ ≤ 17 * Δ ^ 2 * B ^ 6 := by
    intro j hj
    have hj' : j < m + 1 := by omega
    have e1 : P (j + 1) = P (j + 1 + 1) * X (j + 1) := hPX (j + 1) hj
    have e0 : P j = P (j + 1) * X j := hPX j hj'
    have h : (P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)
        = P (j + 1 + 1) * ((1 - X (j + 1)) * (1 - X (j + 1)) + X (j + 1) * (X j - X (j + 1))) := by
      rw [e0, e1]
      noncomm_ring
    have h1 : ‖(1 - X (j + 1)) * (1 - X (j + 1))‖ ≤ 9 * Δ ^ 2 * B ^ 4 := by
      calc ‖(1 - X (j + 1)) * (1 - X (j + 1))‖ ≤ ‖1 - X (j + 1)‖ * ‖1 - X (j + 1)‖ := norm_mul_le _ _
        _ ≤ (3 * Δ * B ^ 2) * (3 * Δ * B ^ 2) := by
            have := hX1 (j + 1) hj
            rw [norm_sub_rev] at this
            exact mul_le_mul this this (norm_nonneg _) (by positivity)
        _ = 9 * Δ ^ 2 * B ^ 4 := by ring
    have h2 : ‖X (j + 1) * (X j - X (j + 1))‖ ≤ 8 * Δ ^ 2 * B ^ 4 := by
      calc ‖X (j + 1) * (X j - X (j + 1))‖ ≤ ‖X (j + 1)‖ * ‖X j - X (j + 1)‖ := norm_mul_le _ _
        _ ≤ B ^ 2 * (8 * Δ ^ 2 * B ^ 2) :=
            mul_le_mul (hXn _ hj) (hXX j hj) (norm_nonneg _) (by positivity)
        _ = 8 * Δ ^ 2 * B ^ 4 := by ring
    calc ‖(P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)‖
        = ‖P (j + 1 + 1) * ((1 - X (j + 1)) * (1 - X (j + 1)) + X (j + 1) * (X j - X (j + 1)))‖ := by
          rw [h]
      _ ≤ ‖P (j + 1 + 1)‖ * ‖(1 - X (j + 1)) * (1 - X (j + 1)) + X (j + 1) * (X j - X (j + 1))‖ :=
          norm_mul_le _ _
      _ ≤ B ^ 2 * (9 * Δ ^ 2 * B ^ 4 + 8 * Δ ^ 2 * B ^ 4) :=
          mul_le_mul (hP _ (by omega)) ((norm_add_le _ _).trans (add_le_add h1 h2))
            (norm_nonneg _) (by positivity)
      _ = 17 * Δ ^ 2 * B ^ 6 := by ring
  -- the three sums
  set SR : E := ∑ j ∈ Finset.range (m + 1), P j (Rem (j + 1) - Rem j) with hSR
  set S1 : E := ∑ j ∈ Finset.range (m + 1), P (j + 1)
      ((((Δ : ℂ) • Θ j + 1 - X j) (A j)) + (Δ : ℂ) • ((X j - 1) (Θ j (A j)))) with hS1
  set S2 : E := ∑ j ∈ Finset.range (m + 1), (P (j + 1) - P j) (A (j + 1) - A j) with hS2
  have key : A (m + 1) - P 0 (A 0) - (Δ : ℂ) • ∑ j ∈ Finset.range (m + 1), P j (F j)
        - ∑ j ∈ Finset.range (m + 1), P j (Mart (j + 1) - Mart j) = SR + S1 + S2 := by
    have ht := pfStep5Grid_tele P A (m + 1)
    rw [hPk, one_apply_eq_self] at ht
    rw [ht, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, hSR, hS1, hS2,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    exact pfStep5Grid_term Δ (P j) (P (j + 1)) (X j) (Θ j) (A j) (A (j + 1)) (F j) (Rem j)
      (Rem (j + 1)) (Mart j) (Mart (j + 1)) (hPX j hj') (hrec j hj')
  rw [key]
  -- bound of `SR`
  have hSRb : ‖SR‖ ≤ 5 * B ^ 4 * R := by
    have h := pfStep5Grid_abel P Rem m
    have hb1 : ‖P m (Rem (m + 1))‖ ≤ B ^ 2 * R :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hP m (by omega)) (hRem _ le_rfl) (norm_nonneg _) (by positivity))
    have hb2 : ‖P 0 (Rem 0)‖ ≤ B ^ 2 * R :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hP 0 (by omega)) (hRem _ (by omega)) (norm_nonneg _) (by positivity))
    have hb3 : ‖∑ j ∈ Finset.range m, (P (j + 1) - P j) (Rem (j + 1))‖ ≤ m * (3 * Δ * B ^ 4 * R) :=
      pfStep5Grid_sumBound m _ _ fun j hj =>
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hW1 j (by omega)) (hRem _ (by omega)) (norm_nonneg _) (by positivity))
    rw [hSR, h]
    calc ‖P m (Rem (m + 1)) - P 0 (Rem 0) - ∑ j ∈ Finset.range m, (P (j + 1) - P j) (Rem (j + 1))‖
        ≤ ‖P m (Rem (m + 1)) - P 0 (Rem 0)‖ +
          ‖∑ j ∈ Finset.range m, (P (j + 1) - P j) (Rem (j + 1))‖ := norm_sub_le _ _
      _ ≤ (‖P m (Rem (m + 1))‖ + ‖P 0 (Rem 0)‖) + m * (3 * Δ * B ^ 4 * R) :=
          add_le_add (norm_sub_le _ _) hb3
      _ ≤ (B ^ 2 * R + B ^ 2 * R) + 3 * B ^ 4 * R * ((m : ℝ) * Δ) := by
          have := add_le_add hb1 hb2
          nlinarith [this]
      _ ≤ (B ^ 4 * R + B ^ 4 * R) + 3 * B ^ 4 * R * 1 := by
          have h24 : B ^ 2 ≤ B ^ 4 := pow_le_pow_right₀ hB (by norm_num)
          have hR' : 0 ≤ B ^ 4 * R := by positivity
          have : B ^ 2 * R ≤ B ^ 4 * R := mul_le_mul_of_nonneg_right h24 hR
          have h3 : 3 * B ^ 4 * R * ((m : ℝ) * Δ) ≤ 3 * B ^ 4 * R * 1 :=
            mul_le_mul_of_nonneg_left hmΔ' (by positivity)
          linarith
      _ = 5 * B ^ 4 * R := by ring
  -- bound of `S1`
  have hS1b : ‖S1‖ ≤ 9 * Δ * B ^ 5 * M := by
    have hterm : ∀ j, j < m + 1 → ‖P (j + 1)
        ((((Δ : ℂ) • Θ j + 1 - X j) (A j)) + (Δ : ℂ) • ((X j - 1) (Θ j (A j))))‖
        ≤ 9 * Δ ^ 2 * B ^ 5 * M := by
      intro j hj
      have hu : ‖(((Δ : ℂ) • Θ j + 1 - X j) (A j))‖ ≤ 3 * Δ ^ 2 * B ^ 2 * M := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul ?_ (hA _ (by omega)) (norm_nonneg _) (by positivity))
        have : (Δ : ℂ) • Θ j + 1 - X j = -(X j - 1 - (Δ : ℂ) • Θ j) := by abel
        rw [this, norm_neg]
        exact hX2 j hj
      have hv : ‖(Δ : ℂ) • ((X j - 1) (Θ j (A j)))‖ ≤ 6 * Δ ^ 2 * B ^ 3 * M := by
        rw [norm_smul, hΔn]
        have h1 : ‖(X j - 1) (Θ j (A j))‖ ≤ 6 * Δ * B ^ 3 * M := by
          calc ‖(X j - 1) (Θ j (A j))‖ ≤ ‖X j - 1‖ * ‖Θ j (A j)‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ (3 * Δ * B ^ 2) * ((2 * B) * M) := by
                refine mul_le_mul (hX1 j hj) ((ContinuousLinearMap.le_opNorm _ _).trans
                  (mul_le_mul (hΘ j hj) (hA _ (by omega)) (norm_nonneg _) (by positivity)))
                  (norm_nonneg _) (by positivity)
            _ = 6 * Δ * B ^ 3 * M := by ring
        calc Δ * ‖(X j - 1) (Θ j (A j))‖ ≤ Δ * (6 * Δ * B ^ 3 * M) :=
              mul_le_mul_of_nonneg_left h1 hΔ
          _ = 6 * Δ ^ 2 * B ^ 3 * M := by ring
      calc ‖P (j + 1) ((((Δ : ℂ) • Θ j + 1 - X j) (A j)) + (Δ : ℂ) • ((X j - 1) (Θ j (A j))))‖
          ≤ ‖P (j + 1)‖ * ‖(((Δ : ℂ) • Θ j + 1 - X j) (A j)) + (Δ : ℂ) • ((X j - 1) (Θ j (A j)))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ B ^ 2 * (3 * Δ ^ 2 * B ^ 2 * M + 6 * Δ ^ 2 * B ^ 3 * M) :=
            mul_le_mul (hP _ (by omega)) ((norm_add_le _ _).trans (add_le_add hu hv))
              (norm_nonneg _) (by positivity)
        _ ≤ 9 * Δ ^ 2 * B ^ 5 * M := by
            have h45 : B ^ 4 ≤ B ^ 5 := pow_le_pow_right₀ hB (by norm_num)
            have : 0 ≤ Δ ^ 2 * M := by positivity
            nlinarith [mul_le_mul_of_nonneg_right h45 this]
    have := pfStep5Grid_sumBound (m + 1) _ _ hterm
    calc ‖S1‖ ≤ ((m + 1 : ℕ) : ℝ) * (9 * Δ ^ 2 * B ^ 5 * M) := this
      _ = 9 * B ^ 5 * M * Δ * (((m : ℝ) + 1) * Δ) := by push_cast; ring
      _ ≤ 9 * B ^ 5 * M * Δ * 1 :=
          mul_le_mul_of_nonneg_left hmΔ (by positivity)
      _ = 9 * Δ * B ^ 5 * M := by ring
  -- bound of `S2`
  have hS2b : ‖S2‖ ≤ 23 * Δ * B ^ 6 * M := by
    have h := pfStep5Grid_abel (fun j => P (j + 1) - P j) A m
    have hb1 : ‖(P (m + 1) - P m) (A (m + 1))‖ ≤ 3 * Δ * B ^ 4 * M :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hW1 m (by omega)) (hA _ le_rfl) (norm_nonneg _) (by positivity))
    have hb2 : ‖(P (0 + 1) - P 0) (A 0)‖ ≤ 3 * Δ * B ^ 4 * M :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul (hW1 0 (by omega)) (hA _ (by omega)) (norm_nonneg _) (by positivity))
    have hb3 : ‖∑ j ∈ Finset.range m,
        ((P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)) (A (j + 1))‖
        ≤ m * (17 * Δ ^ 2 * B ^ 6 * M) :=
      pfStep5Grid_sumBound m _ _ fun j hj =>
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hW2 j (by omega)) (hA _ (by omega)) (norm_nonneg _) (by positivity))
    rw [hS2]
    rw [h]
    calc ‖(P (m + 1) - P m) (A (m + 1)) - (P (0 + 1) - P 0) (A 0) -
          ∑ j ∈ Finset.range m, ((P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)) (A (j + 1))‖
        ≤ ‖(P (m + 1) - P m) (A (m + 1)) - (P (0 + 1) - P 0) (A 0)‖ +
          ‖∑ j ∈ Finset.range m, ((P (j + 1 + 1) - P (j + 1)) - (P (j + 1) - P j)) (A (j + 1))‖ :=
          norm_sub_le _ _
      _ ≤ (‖(P (m + 1) - P m) (A (m + 1))‖ + ‖(P (0 + 1) - P 0) (A 0)‖) + m * (17 * Δ ^ 2 * B ^ 6 * M) :=
          add_le_add (norm_sub_le _ _) hb3
      _ ≤ (3 * Δ * B ^ 4 * M + 3 * Δ * B ^ 4 * M) + 17 * Δ * B ^ 6 * M * ((m : ℝ) * Δ) := by
          have := add_le_add hb1 hb2
          nlinarith [this]
      _ ≤ (3 * Δ * B ^ 6 * M + 3 * Δ * B ^ 6 * M) + 17 * Δ * B ^ 6 * M * 1 := by
          have h46 : B ^ 4 ≤ B ^ 6 := pow_le_pow_right₀ hB (by norm_num)
          have hΔM : 0 ≤ Δ * M := by positivity
          have : 3 * Δ * B ^ 4 * M ≤ 3 * Δ * B ^ 6 * M := by
            have := mul_le_mul_of_nonneg_right h46 hΔM
            nlinarith [this]
          have h3 : 17 * Δ * B ^ 6 * M * ((m : ℝ) * Δ) ≤ 17 * Δ * B ^ 6 * M * 1 :=
            mul_le_mul_of_nonneg_left hmΔ' (by positivity)
          linarith
      _ = 23 * Δ * B ^ 6 * M := by ring
  -- conclusion
  calc ‖SR + S1 + S2‖ ≤ ‖SR‖ + ‖S1‖ + ‖S2‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 5 * B ^ 4 * R + 9 * Δ * B ^ 5 * M + 23 * Δ * B ^ 6 * M := add_le_add (add_le_add hSRb hS1b) hS2b
    _ ≤ 64 * B ^ 7 * (R + Δ * M) := by
        have h47 : B ^ 4 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
        have h57 : B ^ 5 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
        have h67 : B ^ 6 ≤ B ^ 7 := pow_le_pow_right₀ hB (by norm_num)
        have hΔM : 0 ≤ Δ * M := by positivity
        nlinarith [mul_le_mul_of_nonneg_right h47 hR, mul_le_mul_of_nonneg_right h57 hΔM,
          mul_le_mul_of_nonneg_right h67 hΔM, pow_nonneg hB0 7, mul_nonneg (pow_nonneg hB0 7) hR,
          mul_nonneg (pow_nonneg hB0 7) hΔM]

end Abstract

section Concrete

variable (d L : ℕ) [NeZero L]

/-- The slot operator -/
private def pfStep5Grid_slot (i : Fin 2) (K : Matrix (Zd d L) (Zd d L) ℂ) :
    ((Fin 2 → Zd d L) → ℂ) →L[ℂ] ((Fin 2 → Zd d L) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A a => ∑ c, K (a i) c * A (Function.update a i c)
      map_add' := fun A B => by
        funext a
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c A => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring }

private theorem pfStep5Grid_slot_apply (i : Fin 2) (K : Matrix (Zd d L) (Zd d L) ℂ)
    (A : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    pfStep5Grid_slot d L i K A a = ∑ c, K (a i) c * A (Function.update a i c) := rfl

private theorem pfStep5Grid_slot_add (i : Fin 2) (K K' : Matrix (Zd d L) (Zd d L) ℂ) :
    pfStep5Grid_slot d L i (K + K') = pfStep5Grid_slot d L i K + pfStep5Grid_slot d L i K' := by
  ext A a
  simp only [_root_.add_apply, Pi.add_apply, pfStep5Grid_slot_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

private theorem pfStep5Grid_slot_sub (i : Fin 2) (K K' : Matrix (Zd d L) (Zd d L) ℂ) :
    pfStep5Grid_slot d L i (K - K') = pfStep5Grid_slot d L i K - pfStep5Grid_slot d L i K' := by
  ext A a
  simp only [_root_.sub_apply, Pi.sub_apply, pfStep5Grid_slot_apply, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem pfStep5Grid_slot_smul (i : Fin 2) (c : ℂ) (K : Matrix (Zd d L) (Zd d L) ℂ) :
    pfStep5Grid_slot d L i (c • K) = c • pfStep5Grid_slot d L i K := by
  ext A a
  simp only [_root_.smul_apply, pfStep5Grid_slot_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

private theorem pfStep5Grid_slot_one (i : Fin 2) :
    pfStep5Grid_slot d L i 1 = 1 := by
  ext A a
  simp only [pfStep5Grid_slot_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_apply_eq_self]
  rw [Function.update_eq_self]

private theorem pfStep5Grid_norm_slot (i : Fin 2) (K : Matrix (Zd d L) (Zd d L) ℂ) :
    ‖pfStep5Grid_slot d L i K‖ ≤ ‖K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun A => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr fun a => ?_
  rw [pfStep5Grid_slot_apply]
  calc ‖∑ c, K (a i) c * A (Function.update a i c)‖
      ≤ ∑ c, ‖K (a i) c * A (Function.update a i c)‖ := norm_sum_le _ _
    _ ≤ ∑ c, ‖K (a i) c‖ * ‖A‖ := Finset.sum_le_sum fun c _ => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm A _) (norm_nonneg _)
    _ = (∑ c, ‖K (a i) c‖) * ‖A‖ := by rw [Finset.sum_mul]
    _ ≤ ‖K‖ * ‖A‖ := mul_le_mul_of_nonneg_right (sum_norm_row_le K (a i)) (norm_nonneg _)


private theorem pfStep5Grid_eta (b : Fin 2 → Zd d L) : ![b 0, b 1] = b := by
  ext i; fin_cases i <;> rfl

private theorem pfStep5Grid_sum2 (f : (Fin 2 → Zd d L) → ℂ) :
    ∑ b, f b = ∑ x, ∑ y, f ![x, y] := by
  rw [← Fintype.sum_prod_type' (f := fun x y => f ![x, y])]
  exact Fintype.sum_equiv (finTwoArrowEquiv (Zd d L)) _ _ fun b => by
    simp [finTwoArrowEquiv_apply, pfStep5Grid_eta]

private theorem pfStep5Grid_update2 (a : Fin 2 → Zd d L) (c c' : Zd d L) :
    Function.update (Function.update a 0 c) 1 c' = ![c, c'] := by
  ext i; fin_cases i <;> simp

private theorem pfStep5Grid_update2' (a : Fin 2 → Zd d L) (c : Zd d L) :
    (Function.update a 0 c) 1 = a 1 := by
  simp

/-- `𝒰_{v,w} = (slot 0 u₀)(slot 1 u₁)`. -/
private theorem pfStep5Grid_Ugen_eq (g E : ℝ) (σ : Fin 2 → Bool) (v w : ℝ)
    (A : (Fin 2 → Zd d L) → ℂ) :
    RBM.Ind.Ugen d L g E σ v w A =
      (pfStep5Grid_slot d L 0 (uKer d L g (cycProd (fun i => mSigma E (σ i)) 0) v w) *
        pfStep5Grid_slot d L 1 (uKer d L g (cycProd (fun i => mSigma E (σ i)) 1) v w)) A := by
  funext a
  rw [mul_apply_eq_comp]
  simp only [RBM.Ind.Ugen, UN, pfStep5Grid_slot_apply, Fin.prod_univ_two]
  rw [pfStep5Grid_sum2]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [pfStep5Grid_update2', pfStep5Grid_update2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- `Θ^{(2)}_t = (slot 0 θ₀) + (slot 1 θ₁)`. -/
private theorem pfStep5Grid_ThetaN_eq (g E : ℝ) (σ : Fin 2 → Bool) (t : ℝ)
    (A : (Fin 2 → Zd d L) → ℂ) :
    ThetaN d L g (fun i => mSigma E (σ i)) t A =
      (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) t) +
        pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) t)) A := by
  funext a
  simp only [ThetaN, Fin.sum_univ_two, Pi.add_apply, _root_.add_apply, pfStep5Grid_slot_apply]

end Concrete


/-- the algebra of the two-slot expansion, generic in the space. -/
private theorem pfStep5Grid_alg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (δ : ℂ)
    (S₀ S₁ : E →L[ℂ] E) :
    (1 + δ • S₀) * (1 + δ • S₁) - 1 - δ • (S₀ + S₁) = (δ * δ) • (S₀ * S₁) := by
  simp only [mul_add, add_mul, one_mul, mul_one]
  rw [smul_mul_smul_comm]
  module

section OneSlot

variable {d L : ℕ} [NeZero L] {g : ℝ}

private theorem pfStep5Grid_inv_le {v ut : ℝ} (hvu : v ≤ ut) (hu1 : ut < 1) :
    (1 - v)⁻¹ ≤ (1 - ut)⁻¹ := by
  have : 0 < 1 - ut := by linarith
  exact inv_anti₀ this (by linarith)

private theorem pfStep5Grid_norm_thetaKer (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w < 1) : ‖thetaKer d L g μ w‖ ≤ (1 - w)⁻¹ := by
  unfold thetaKer
  have h1 : ‖μ • SB d L g‖ = 1 := by rw [norm_smul, hμ, norm_SB d L g hL, one_mul]
  calc ‖(μ • SB d L g) * Theta d L g ((w : ℂ) * μ)‖
      ≤ ‖μ • SB d L g‖ * ‖Theta d L g ((w : ℂ) * μ)‖ := norm_mul_le _ _
    _ ≤ 1 * (1 - w)⁻¹ :=
        mul_le_mul (le_of_eq h1) (norm_Theta_le hL hw0 hw1 hμ) (norm_nonneg _) zero_le_one
    _ = (1 - w)⁻¹ := one_mul _

private theorem pfStep5Grid_uKer_eq (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {v w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) :
    uKer d L g μ v w = 1 + ((w - v : ℝ) : ℂ) • thetaKer d L g μ w := by
  rw [uKer_eq_one_add hL (norm_t_mul_lt_one hw0 hw1 hμ)]
  unfold thetaKer
  rw [smul_mul_assoc, smul_smul]
  push_cast
  rfl

private theorem pfStep5Grid_thetaKer_sub (hL : 3 ≤ L) {μ : ℂ} (hμ : ‖μ‖ = 1) {v w : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hw1 : w < 1) :
    ‖thetaKer d L g μ w - thetaKer d L g μ v‖ ≤ (w - v) * ((1 - w)⁻¹ * (1 - v)⁻¹) := by
  have hv1 : v < 1 := lt_of_le_of_lt hvw hw1
  have hw0 : 0 ≤ w := hv0.trans hvw
  have ha1 : Theta d L g ((w : ℂ) * μ) * (1 - ((w : ℂ) * μ) • SB d L g) = 1 :=
    Theta_mul_of_three_le hL (norm_t_mul_lt_one hw0 hw1 hμ)
  have hb1 : (1 - ((v : ℂ) * μ) • SB d L g) * Theta d L g ((v : ℂ) * μ) = 1 :=
    mul_Theta_of_three_le hL (norm_t_mul_lt_one hv0 hv1 hμ)
  set a := Theta d L g ((w : ℂ) * μ) with ha
  set b := Theta d L g ((v : ℂ) * μ) with hb
  have hab : a - b = (((w : ℂ) - v) * μ) • (a * SB d L g * b) := by
    have e1 : a - b = a * ((1 - ((v : ℂ) * μ) • SB d L g) * b)
        - (a * (1 - ((w : ℂ) * μ) • SB d L g)) * b := by
      rw [hb1, ha1, mul_one, one_mul]
    rw [e1]
    simp only [mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm, sub_smul, mul_assoc]
    abel
  have hθ : thetaKer d L g μ w - thetaKer d L g μ v = (μ • SB d L g) * (a - b) := by
    unfold thetaKer; rw [mul_sub]
  have hc : ‖((w : ℂ) - v) * μ‖ = w - v := by
    rw [norm_mul, hμ, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith)]
  have h1 : ‖μ • SB d L g‖ = 1 := by rw [norm_smul, hμ, norm_SB d L g hL, one_mul]
  have hna : ‖a‖ ≤ (1 - w)⁻¹ := norm_Theta_le hL hw0 hw1 hμ
  have hnb : ‖b‖ ≤ (1 - v)⁻¹ := norm_Theta_le hL hv0 hv1 hμ
  have hSB : ‖SB d L g‖ = 1 := norm_SB d L g hL
  rw [hθ, hab]
  calc ‖(μ • SB d L g) * ((((w : ℂ) - v) * μ) • (a * SB d L g * b))‖
      ≤ ‖μ • SB d L g‖ * ‖(((w : ℂ) - v) * μ) • (a * SB d L g * b)‖ := norm_mul_le _ _
    _ = (w - v) * ‖a * SB d L g * b‖ := by rw [h1, one_mul, norm_smul, hc]
    _ ≤ (w - v) * (‖a‖ * ‖SB d L g‖ * ‖b‖) :=
        mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (by linarith)
    _ ≤ (w - v) * ((1 - w)⁻¹ * 1 * (1 - v)⁻¹) := by
        rw [hSB]
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact mul_le_mul (mul_le_mul_of_nonneg_right hna (by norm_num)) hnb (norm_nonneg _)
          (by have : 0 < 1 - w := by linarith
              positivity)
    _ = (w - v) * ((1 - w)⁻¹ * (1 - v)⁻¹) := by ring

end OneSlot


section Ops

variable (d L : ℕ) [NeZero L] (g E : ℝ) (σ : Fin 2 → Bool)

/-- `𝒰_{v,w}` as a bounded operator. -/
private def pfStep5Grid_Uc (v w : ℝ) :
    ((Fin 2 → Zd d L) → ℂ) →L[ℂ] ((Fin 2 → Zd d L) → ℂ) :=
  pfStep5Grid_slot d L 0 (uKer d L g (cycProd (fun i => mSigma E (σ i)) 0) v w) *
    pfStep5Grid_slot d L 1 (uKer d L g (cycProd (fun i => mSigma E (σ i)) 1) v w)

/-- `Θ^{(2)}_v` as a bounded operator. -/
private def pfStep5Grid_Tc (v : ℝ) :
    ((Fin 2 → Zd d L) → ℂ) →L[ℂ] ((Fin 2 → Zd d L) → ℂ) :=
  pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) v) +
    pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) v)

variable {d L g E σ}

private theorem pfStep5Grid_Uc_apply (A : (Fin 2 → Zd d L) → ℂ) (v w : ℝ) :
    pfStep5Grid_Uc d L g E σ v w A = RBM.Ind.Ugen d L g E σ v w A :=
  (pfStep5Grid_Ugen_eq d L g E σ v w A).symm

private theorem pfStep5Grid_Tc_apply (A : (Fin 2 → Zd d L) → ℂ) (v : ℝ) :
    pfStep5Grid_Tc d L g E σ v A = ThetaN d L g (fun i => mSigma E (σ i)) v A :=
  (pfStep5Grid_ThetaN_eq d L g E σ v A).symm

private theorem pfStep5Grid_mu (hE : |E| ≤ 2) (i : Fin 2) :
    ‖cycProd (fun i => mSigma E (σ i)) i‖ = 1 :=
  norm_cycProd (fun i => norm_mSigma hE (σ i)) i

/-- every slot `θ`-operator at a time `x ∈ [0,ut]` has norm `≤ (1-ut)⁻¹`. -/
private theorem pfStep5Grid_norm_slotTheta (hL : 3 ≤ L) (hE : |E| ≤ 2) (i : Fin 2) {x ut : ℝ}
    (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d L i (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) i) x)‖ ≤
      (1 - ut)⁻¹ :=
  (pfStep5Grid_norm_slot d L i _).trans
    ((pfStep5Grid_norm_thetaKer hL (pfStep5Grid_mu hE i) hx0 (lt_of_le_of_lt hxu hu1)).trans
      (pfStep5Grid_inv_le hxu hu1))

private theorem pfStep5Grid_norm_Tc (hL : 3 ≤ L) (hE : |E| ≤ 2) {x ut : ℝ}
    (hx0 : 0 ≤ x) (hxu : x ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_Tc d L g E σ x‖ ≤ 2 * (1 - ut)⁻¹ := by
  unfold pfStep5Grid_Tc
  have h0 := pfStep5Grid_norm_slotTheta (d := d) (g := g) (σ := σ) hL hE 0 hx0 hxu hu1
  have h1 := pfStep5Grid_norm_slotTheta (d := d) (g := g) (σ := σ) hL hE 1 hx0 hxu hu1
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (1 - ut)⁻¹ + (1 - ut)⁻¹ := add_le_add h0 h1
    _ = 2 * (1 - ut)⁻¹ := by ring

private theorem pfStep5Grid_norm_Tc_sub (hL : 3 ≤ L) (hE : |E| ≤ 2) {v w ut : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_Tc d L g E σ w - pfStep5Grid_Tc d L g E σ v‖ ≤
      2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d L i (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) i) w -
      thetaKer d L g (cycProd (fun i => mSigma E (σ i)) i) v)‖ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 := by
    intro i
    refine (pfStep5Grid_norm_slot d L i _).trans ((pfStep5Grid_thetaKer_sub hL
      (pfStep5Grid_mu hE i) hv0 hvw hw1).trans ?_)
    have h1 := pfStep5Grid_inv_le hwu hu1
    have h2 := pfStep5Grid_inv_le (hvw.trans hwu) hu1
    have hp : 0 ≤ (1 - w)⁻¹ := inv_nonneg.mpr (by linarith)
    have hp' : 0 ≤ (1 - ut)⁻¹ := inv_nonneg.mpr (by linarith)
    have : (1 - w)⁻¹ * (1 - v)⁻¹ ≤ ((1 - ut)⁻¹) ^ 2 := by
      rw [sq]; exact mul_le_mul h1 h2 (inv_nonneg.mpr (by linarith)) hp'
    exact mul_le_mul_of_nonneg_left this (by linarith)
  have e : pfStep5Grid_Tc d L g E σ w - pfStep5Grid_Tc d L g E σ v =
      pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w -
        thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) v) +
      pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w -
        thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) v) := by
    unfold pfStep5Grid_Tc
    rw [pfStep5Grid_slot_sub, pfStep5Grid_slot_sub]
    abel
  rw [e]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ (w - v) * ((1 - ut)⁻¹) ^ 2 + (w - v) * ((1 - ut)⁻¹) ^ 2 := add_le_add (hB 0) (hB 1)
    _ = 2 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by ring

private theorem pfStep5Grid_norm_Uc (hL : 3 ≤ L) (hE : |E| ≤ 2) {v w ut : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_Uc d L g E σ v w‖ ≤ ((1 - ut)⁻¹) ^ 2 := by
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hB : ∀ i : Fin 2, ‖pfStep5Grid_slot d L i
      (uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v w)‖ ≤ (1 - ut)⁻¹ := by
    intro i
    refine (pfStep5Grid_norm_slot d L i _).trans ((norm_uKer_le hL hv0 hvw hw1
      (pfStep5Grid_mu hE i)).trans ?_)
    have h1 : (1 - v) / (1 - w) ≤ (1 - w)⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr (by linarith)) (by linarith)
    exact h1.trans (pfStep5Grid_inv_le hwu hu1)
  unfold pfStep5Grid_Uc
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul (hB 0) (hB 1) (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring


private theorem pfStep5Grid_Uc_expand (hL : 3 ≤ L) (hE : |E| ≤ 2) {v w : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) :
    pfStep5Grid_Uc d L g E σ v w - 1 - ((w - v : ℝ) : ℂ) • pfStep5Grid_Tc d L g E σ w =
      (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w)) := by
  unfold pfStep5Grid_Uc pfStep5Grid_Tc
  rw [pfStep5Grid_uKer_eq hL (pfStep5Grid_mu hE 0) hw0 hw1,
    pfStep5Grid_uKer_eq hL (pfStep5Grid_mu hE 1) hw0 hw1,
    pfStep5Grid_slot_add, pfStep5Grid_slot_add, pfStep5Grid_slot_smul, pfStep5Grid_slot_smul,
    pfStep5Grid_slot_one, pfStep5Grid_slot_one]
  exact pfStep5Grid_alg _ _ _

/-- the quadratic remainder `δ² S₀ S₁` has norm `≤ δ² B²`. -/
private theorem pfStep5Grid_norm_quad (hL : 3 ≤ L) (hE : |E| ≤ 2) {w ut : ℝ}
    (hw0 : 0 ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w)‖ ≤
      ((1 - ut)⁻¹) ^ 2 := by
  have h0 := pfStep5Grid_norm_slotTheta (d := d) (g := g) (σ := σ) hL hE 0 hw0 hwu hu1
  have h1 := pfStep5Grid_norm_slotTheta (d := d) (g := g) (σ := σ) hL hE 1 hw0 hwu hu1
  calc _ ≤ _ := norm_mul_le _ _
    _ ≤ (1 - ut)⁻¹ * (1 - ut)⁻¹ :=
        mul_le_mul h0 h1 (norm_nonneg _) (inv_nonneg.mpr (by linarith))
    _ = ((1 - ut)⁻¹) ^ 2 := by ring

private theorem pfStep5Grid_norm_Uc_sub_one (hL : 3 ≤ L) (hE : |E| ≤ 2) {v w ut : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_Uc d L g E σ v w - 1‖ ≤ 3 * (w - v) * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hB1 : 1 ≤ (1 - ut)⁻¹ := by
    rw [one_le_inv₀ (by linarith)]; linarith
  have hδ0 : 0 ≤ w - v := by linarith
  have hδ1 : w - v ≤ 1 := by linarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := pfStep5Grid_Uc_expand (d := d) (g := g) (σ := σ) (v := v) hL hE hw0 hw1
  have e' : pfStep5Grid_Uc d L g E σ v w - 1 =
      ((w - v : ℝ) : ℂ) • pfStep5Grid_Tc d L g E σ w + (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w)) := by
    rw [← e]; abel
  rw [e']
  have hT := pfStep5Grid_norm_Tc (d := d) (g := g) (σ := σ) hL hE hw0 hwu hu1
  have hQ := pfStep5Grid_norm_quad (d := d) (g := g) (σ := σ) hL hE hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ ‖((w - v : ℝ) : ℂ) • pfStep5Grid_Tc d L g E σ w‖ + ‖(((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w))‖ := norm_add_le _ _
    _ ≤ (w - v) * (2 * B) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ ≤ 3 * (w - v) * B ^ 2 := by
        have h1 : B ≤ B ^ 2 := by nlinarith
        have h2 : (w - v) * (w - v) * B ^ 2 ≤ 1 * (w - v) * B ^ 2 := by
          have := mul_le_mul_of_nonneg_right hδ1 hδ0
          have := mul_le_mul_of_nonneg_right this (sq_nonneg B)
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h1 hδ0]

private theorem pfStep5Grid_norm_Uc_sub_one_Tc (hL : 3 ≤ L) (hE : |E| ≤ 2) {v w ut : ℝ}
    (hv0 : 0 ≤ v) (hvw : v ≤ w) (hwu : w ≤ ut) (hu1 : ut < 1) :
    ‖pfStep5Grid_Uc d L g E σ v w - 1 - ((w - v : ℝ) : ℂ) • pfStep5Grid_Tc d L g E σ v‖ ≤
      3 * (w - v) ^ 2 * ((1 - ut)⁻¹) ^ 2 := by
  have hw0 : 0 ≤ w := hv0.trans hvw
  have hw1 : w < 1 := lt_of_le_of_lt hwu hu1
  have hδ0 : 0 ≤ w - v := by linarith
  have hδn : ‖((w - v : ℝ) : ℂ)‖ = w - v := by
    rw [Complex.norm_real, Real.norm_of_nonneg hδ0]
  have e := pfStep5Grid_Uc_expand (d := d) (g := g) (σ := σ) (v := v) hL hE hw0 hw1
  have e' : pfStep5Grid_Uc d L g E σ v w - 1 - ((w - v : ℝ) : ℂ) • pfStep5Grid_Tc d L g E σ v =
      ((w - v : ℝ) : ℂ) • (pfStep5Grid_Tc d L g E σ w - pfStep5Grid_Tc d L g E σ v) +
        (((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w)) := by
    rw [← e, smul_sub]; abel
  rw [e']
  have hT := pfStep5Grid_norm_Tc_sub (d := d) (g := g) (σ := σ) hL hE hv0 hvw hwu hu1
  have hQ := pfStep5Grid_norm_quad (d := d) (g := g) (σ := σ) hL hE hw0 hwu hu1
  set B := (1 - ut)⁻¹ with hBdef
  calc _ ≤ ‖((w - v : ℝ) : ℂ) • (pfStep5Grid_Tc d L g E σ w - pfStep5Grid_Tc d L g E σ v)‖ +
        ‖(((w - v : ℝ) : ℂ) * ((w - v : ℝ) : ℂ)) •
        (pfStep5Grid_slot d L 0 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 0) w) *
          pfStep5Grid_slot d L 1 (thetaKer d L g (cycProd (fun i => mSigma E (σ i)) 1) w))‖ :=
        norm_add_le _ _
    _ ≤ (w - v) * (2 * (w - v) * B ^ 2) + (w - v) * (w - v) * B ^ 2 := by
        rw [norm_smul, norm_smul, hδn, norm_mul, hδn]
        exact add_le_add (mul_le_mul_of_nonneg_left hT hδ0)
          (mul_le_mul_of_nonneg_left hQ (by positivity))
    _ = 3 * (w - v) ^ 2 * B ^ 2 := by ring

end Ops



/-! ## 5. The Duhamel form -/

/-- **The Duhamel form**. -/
theorem pfStep5Grid_duhamel (d : ℕ) : PfStep5Grid_duhamel_pin d := by
  intro L hLz hL g E Δ M R σ k u A F Rem Mart hE hΔ hu0 hu hk hA hRem hrec a
  -- the time grid
  have hmono : Monotone u := monotone_nat_of_le_succ fun j => by rw [hu j]; linarith
  have hform : ∀ j, u j = u 0 + j * Δ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [hu j, ih]; push_cast; ring
  have hunn : ∀ j, 0 ≤ u j := fun j => hu0.trans (hmono (Nat.zero_le j))
  have hlt : ∀ j, j ≤ k → u j < 1 := fun j hj => lt_of_le_of_lt (hmono hj) hk
  have hkΔ : (k : ℝ) * Δ ≤ 1 := by
    have := hform k
    have := hunn 0
    linarith
  -- the constants
  have hM : 0 ≤ M := (norm_nonneg _).trans (hA 0 (Nat.zero_le _) 0)
  have hR : 0 ≤ R := (norm_nonneg _).trans (hRem 0 (Nat.zero_le _) 0)
  have hB : 1 ≤ ((1 - u k)⁻¹) := by
    rw [one_le_inv₀ (by linarith [hunn k])]
    linarith [hunn k]
  have hB0 : 0 ≤ ((1 - u k)⁻¹) := by linarith
  have hrhs : 0 ≤ 64 * ((1 - u k)⁻¹) ^ 7 * (R + Δ * M) := by positivity
  cases k with
  | zero =>
    have h0 : RBM.Ind.Ugen d L g E σ (u 0) (u 0) (A 0) = A 0 :=
      RBM.Ind.GridDuhamelN_Ugen_self hL hE σ (hunn 0) hk (A 0)
    simpa [h0] using hrhs
  | succ m =>
    have hu1 : u (m + 1) < 1 := hk
    have hmΔ : ((m : ℝ) + 1) * Δ ≤ 1 := by exact_mod_cast hkΔ
    have hd : ∀ j, u (j + 1) - u j = Δ := fun j => by rw [hu j]; ring
    have hPk : pfStep5Grid_Uc d L g E σ (u (m + 1)) (u (m + 1)) = 1 :=
      ContinuousLinearMap.ext fun B => by
        rw [pfStep5Grid_Uc_apply, one_apply_eq_self]
        exact RBM.Ind.GridDuhamelN_Ugen_self hL hE σ (hunn _) hu1 B
    have hPX : ∀ j, j < m + 1 → pfStep5Grid_Uc d L g E σ (u j) (u (m + 1)) =
        pfStep5Grid_Uc d L g E σ (u (j + 1)) (u (m + 1)) * pfStep5Grid_Uc d L g E σ (u j) (u (j + 1)) := by
      intro j hj
      refine ContinuousLinearMap.ext fun B => ?_
      rw [mul_apply_eq_comp, pfStep5Grid_Uc_apply, pfStep5Grid_Uc_apply, pfStep5Grid_Uc_apply]
      exact (RBM.Ind.GridDuhamelN_Ugen_comp hL hE σ (hunn _) (hlt _ hj) (hunn _) hu1 B).symm
    have hP : ∀ j, j ≤ m + 1 → ‖pfStep5Grid_Uc d L g E σ (u j) (u (m + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => pfStep5Grid_norm_Uc hL hE (hunn j) (hmono hj) le_rfl hu1
    have hXn : ∀ j, j < m + 1 → ‖pfStep5Grid_Uc d L g E σ (u j) (u (j + 1))‖ ≤ ((1 - u (m + 1))⁻¹) ^ 2 :=
      fun j hj => pfStep5Grid_norm_Uc hL hE (hunn j) (hmono (Nat.le_succ j)) (hmono hj) hu1
    have hX1 : ∀ j, j < m + 1 → ‖pfStep5Grid_Uc d L g E σ (u j) (u (j + 1)) - 1‖ ≤
        3 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := pfStep5Grid_norm_Uc_sub_one (d := d) (g := g) (σ := σ) hL hE (hunn j)
        (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hX2 : ∀ j, j < m + 1 → ‖pfStep5Grid_Uc d L g E σ (u j) (u (j + 1)) - 1 -
        (Δ : ℂ) • pfStep5Grid_Tc d L g E σ (u j)‖ ≤ 3 * Δ ^ 2 * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      have := pfStep5Grid_norm_Uc_sub_one_Tc (d := d) (g := g) (σ := σ) hL hE (hunn j)
        (hmono (Nat.le_succ j)) (hmono hj) hu1
      rwa [hd] at this
    have hΘ : ∀ j, j < m + 1 → ‖pfStep5Grid_Tc d L g E σ (u j)‖ ≤ 2 * ((1 - u (m + 1))⁻¹) :=
      fun j hj => pfStep5Grid_norm_Tc hL hE (hunn j) (hmono (Nat.le_of_lt hj)) hu1
    have hΘΘ : ∀ j, j + 1 < m + 1 → ‖pfStep5Grid_Tc d L g E σ (u j) -
        pfStep5Grid_Tc d L g E σ (u (j + 1))‖ ≤ 2 * Δ * ((1 - u (m + 1))⁻¹) ^ 2 := by
      intro j hj
      rw [norm_sub_rev]
      have := pfStep5Grid_norm_Tc_sub (d := d) (g := g) (σ := σ) hL hE (hunn j)
        (hmono (Nat.le_succ j)) (hmono hj.le) hu1
      rwa [hd] at this
    have hA' : ∀ j, j ≤ m + 1 → ‖A j‖ ≤ M := fun j hj =>
      (pi_norm_le_iff_of_nonneg hM).mpr (hA j hj)
    have hRem' : ∀ j, j ≤ m + 1 → ‖Rem j‖ ≤ R := fun j hj =>
      (pi_norm_le_iff_of_nonneg hR).mpr (hRem j hj)
    have hrec' : ∀ j, j < m + 1 → A (j + 1) - A j =
        (Δ : ℂ) • (pfStep5Grid_Tc d L g E σ (u j) (A j) + F j) + (Rem (j + 1) - Rem j) +
          (Mart (j + 1) - Mart j) := by
      intro j hj
      funext b
      have h1 := hrec (j + 1) (by omega) b
      have h0 := hrec j (by omega) b
      rw [Finset.sum_range_succ] at h1
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, pfStep5Grid_Tc_apply]
      linear_combination h1 - h0
    have habs := pfStep5Grid_abs (E := (Fin 2 → Zd d L) → ℂ) m Δ ((1 - u (m + 1))⁻¹) M R hB hΔ hmΔ
      (fun j => pfStep5Grid_Uc d L g E σ (u j) (u (m + 1)))
      (fun j => pfStep5Grid_Uc d L g E σ (u j) (u (j + 1)))
      (fun j => pfStep5Grid_Tc d L g E σ (u j)) A F Rem Mart hPk hPX hP hXn hX1 hX2 hΘ hΘΘ hA' hRem'
      hrec'
    refine le_trans ?_ habs
    refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ a)
    congr 1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, pfStep5Grid_Uc_apply]
    rw [Finset.mul_sum]
    rfl

end Kernel

end RBM.Gauss.Sizes
