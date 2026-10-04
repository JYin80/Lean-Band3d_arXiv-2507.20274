/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.EMn2Exp1
import RBM3D.Evolution.PropTInf

/-!
# ST2-11 (ticket T2118): `lem: EMn2_N`, `(eq:MG_conclusion3)`, part 2: the far sum `S̃₃`

Paper: arXiv:2507.20274, `paper/tex/3_5_Loop_Hierarchy.tex` (`3_5:line`): the lemma `3_5:427-444`
(`(eq:MG_conclusion3)` `3_5:438`), the proof of the far sum `S̃₃` `3_5:871-888` (`(eq_L2-J)`,
the six legs of the 6-loop, `(TTT2)`).  The near case and `S̃₁ + S̃₂` are merged (`EMn2Exp1.lean`:
`emn2Exp_near`, `emn2Exp_far12`); this file proves the hypothesis `h3` of the merged
`emn2Exp_of_far3` and the pin `STEMn2Exp`.

**The route (Amend 1 of the ticket, DECISIONS §35).**  The paper bounds all six legs by
`(Ĵ + W^{-D}) W^{-d} 𝒯̃` and then needs `W^{-2D} Σ_c 1 ≲ (1-t)⁻¹ W^{-D}`, i.e.
`D ≥ (d-2) log_W ℓ_t` (the paper's "large `D`", `3_5:881-886`).  The pin has `∀ D > 0`,
so `S̃₃` is split by the value of the profile `P = W^{-d} 𝒯̃^ℓ_{t,D}` on the `(b,c')` leg:

* `A^f = {P(|c'-b|) ≤ P(|a-b|)}`: the contraction inequality exactly as for `S̃₁`
  (`stContractPt_holds`, `emn2Poly_norm_loop4_alt_le`, `emn2Poly_norm_loop3_le`), with
  `M = y² P(|a-b|)`: `emn2Exp2_partF`; no sum over `c`, no `Ĵ`, no condition on `D`;
* `A^n = {P(|a-b|) < P(|c'-b|)}`: there `P(|c'-b|) = W^{-d} 𝒯_t(|c'-b|)` is a genuine tail
  (`P ≥ W^{-d-D}`), the 6-loop is bounded by the product of three 2-loops
  `|𝓛⁶| ≤ |𝓛²_{(a,c)}| |𝓛²_{(b,a)}| |𝓛²_{(c',b)}|` (each pair twice, `emn2Exp2_loop6_le`: block
  Cauchy-Schwarz, `‖XY‖_HS ≤ ‖X‖_HS ‖Y‖_HS`; **no entry bound `(GijGEX)`**), each 2-loop at
  distance `> ℓ*` is at most `(Ĵ + W^{-d}) P` (`(eq_L2-J)`: `𝒦^{(2)} = W^{-d} Θ_t` and the far
  field `kellStarEv`), and the sum over `c, c'` is `(TTT2)` (`ekPropTInf_holds`) plus
  `Σ_c 𝒯_t(|c|_∞) ≲ (1-t)⁻¹` (`emn2Exp2_sum_tailT_le`): `emn2Exp2_partN`, `emn2Exp2_profile_sum`.

`emn2Exp2_S3_le` is the deterministic bound of `S̃₃` at a Hermitian matrix; `emn2Exp_far3` is `h3`
(the stochastic form on the good event of `(eq:LW_assm_exp)` with the random control `Ĵ`);
`stEMn2Exp_holds` is the pin.  **`3 ≤ d` is a hypothesis of both**: `kellStarEv` and
`ekPropTInf_holds` (the propagator decay `prop:ThfadC` and `(TTT2)`) are statements for `d ≥ 3`;
the pin `STEMn2Exp d` has no such premise (DECISIONS §31, T2080 entry: the bridges
`STLWB_of_LWterm`, `STLWT_of_LWtermExp` carry `(hd : 3 ≤ d)` for the same reason; the consumers of
`STEMn2Exp` are under `3 ≤ d →`, e.g. `STStep2`).
The private lemmas of the merged files are reached with `open private` (Batteries) instead of
being copied, as in `Loop/KLIndStepA.lean`.
-/

set_option linter.style.longLine false

open private emn2Exp_zdistInf_zero emn2Exp_zdistInf_tri emn2Exp_zdistInf_sub_comm
  emn2Exp_loop3_ctrl emn2Exp_stochDomAt_of_subset emn2Exp_tailT_shift emn2Exp_sw_dist
  from RBM3D.Induction.EMn2Exp1
open private hs hs_nonneg trace_mul_conjTranspose_eq Gres_conjTranspose Pm Eblk_eq_smul_Pm
  Pm_conjTranspose Pm_mul_Pm_mul trace_Pm_sandwich loop2_eq from RBM3D.Induction.EMn2Poly
open private card_ball_le from RBM3D.Induction.ContractPt
open private pti_sum_radial from RBM3D.Evolution.PropTInf
open private KLWard_mSigma_mul from RBM3D.Loop.KLWard

noncomputable section

open Matrix Finset Filter MeasureTheory

namespace RBM.Gauss.Sizes

open RBM RBM.Gauss RBM.Loop RBM.Path

/-! ## 1. Hilbert-Schmidt submultiplicativity -/

section Generic

variable {ι : Type*} [Fintype ι]

/-- **Submultiplicativity of the Hilbert-Schmidt norm**: `‖AB‖²_HS ≤ ‖A‖²_HS ‖B‖²_HS`
(Cauchy-Schwarz on each entry of `AB`). -/
private lemma emn2Exp2_hs_mul_le (A B : Matrix ι ι ℂ) : hs (A * B) ≤ hs A * hs B := by
  unfold hs
  have h1 : ∀ i k, ‖(A * B) i k‖ ^ 2 ≤ (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖B j k‖ ^ 2) := by
    intro i k
    rw [Matrix.mul_apply]
    calc ‖∑ j, A i j * B j k‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖B j k‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)
      _ ≤ (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖B j k‖ ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ k, ‖(A * B) i k‖ ^ 2
      ≤ ∑ i, ∑ k, (∑ j, ‖A i j‖ ^ 2) * (∑ j, ‖B j k‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => h1 i k
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ k, ∑ j, ‖B j k‖ ^ 2) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * (∑ j, ∑ k, ‖B j k‖ ^ 2) := by
        rw [Finset.sum_comm (f := fun k j => ‖B j k‖ ^ 2)]

end Generic

/-! ## 2. The Hölder bound of the 6-loop by three 2-loops -/

section Holder

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- The 6-loop of the cut `k = 0`: `𝓛^{(6)} = W^{-6d} tr(G P_a G P_b G P_{c'} Ḡ P_b Ḡ P_a Ḡ P_c)`. -/
private lemma emn2Exp2_loop6_eq (s0 s1 : Bool) (a b c c' : Zd d L) :
    loopFine d L W H z ![s0, s1, s0, !s0, !s1, !s0] ![a, b, c', b, a, c] =
      (((W : ℂ) ^ d)⁻¹) ^ 6 *
        (Gres (blockMat d L W H) z s0 * Pm d L W a *
          Gres (blockMat d L W H) z s1 * Pm d L W b *
          Gres (blockMat d L W H) z s0 * Pm d L W c' *
          Gres (blockMat d L W H) z (!s0) * Pm d L W b *
          Gres (blockMat d L W H) z (!s1) * Pm d L W a *
          Gres (blockMat d L W H) z (!s0) * Pm d L W c).trace := by
  conv_lhs => simp [loopFine, loopM, List.ofFn_succ]
  simp only [Eblk_eq_smul_Pm, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

/-- `𝓛^{(2)}_{(s,-s),(y,x)} = W^{-2d} ‖P_x G(s) P_y‖²_HS`. -/
private lemma emn2Exp2_loop2_hs (hH : H.IsHermitian) (s : Bool) (x y : Zd d L) :
    loopFine d L W H z ![s, !s] ![y, x] =
      (((W : ℂ) ^ d)⁻¹) ^ 2 *
        (hs (Pm d L W x * Gres (blockMat d L W H) z s * Pm d L W y) : ℂ) := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  set G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ := Gres (blockMat d L W H) z with hGdef
  have hG : ∀ s, (G s)ᴴ = G (!s) := Gres_conjTranspose hHb z
  obtain ⟨Y, hYdef⟩ : ∃ Y : Matrix (Vtx d L W) (Vtx d L W) ℂ,
      Y = Pm d L W x * G s * Pm d L W y := ⟨_, rfl⟩
  have hYH : Yᴴ = Pm d L W y * G (!s) * Pm d L W x := by
    rw [hYdef]
    simp only [Matrix.conjTranspose_mul, Pm_conjTranspose, hG, Matrix.mul_assoc]
  rw [← hYdef, loop2_eq, ← trace_mul_conjTranspose_eq, hYH]
  have h1 : Y * (Pm d L W y * G (!s) * Pm d L W x) =
      Pm d L W x * (G s * Pm d L W y * G (!s)) * Pm d L W x := by
    rw [hYdef]; simp only [Matrix.mul_assoc, Pm_mul_Pm_mul]
  rw [h1, trace_Pm_sandwich]

/-- **Hölder bound of the 6-loop by three 2-loops** (`3_5:871-888`, the six legs of the 6-loop): for
every Hermitian `H` and every `z`, `|𝓛^{(6)}_{(σ⊗σ̄)^{(1)},(a,b,c',b,a,c)}| ≤ |𝓛^{(2)}_{(σ₀,-σ₀),(a,c)}|
|𝓛^{(2)}_{(σ₁,-σ₁),(b,a)}| |𝓛^{(2)}_{(σ₀,-σ₀),(c',b)}|`.  The 6-loop is `W^{-6d} ‖Y₁Y₂Y₃‖²_HS` with
`Y₁ = P_c G(σ₀) P_a`, `Y₂ = P_a G(σ₁) P_b`, `Y₃ = P_b G(σ₀) P_{c'}` (the last three factors are the adjoints of
these), and the HS norm is submultiplicative: no entry bound `(GijGEX)` is used. -/
theorem emn2Exp2_loop6_le (hH : H.IsHermitian) (σ₀ σ₁ : Bool) (a b c c' : Zd d L) :
    ‖loopFine d L W H z ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![a, b, c', b, a, c]‖ ≤
      ‖loopFine d L W H z ![σ₀, !σ₀] ![a, c]‖ * ‖loopFine d L W H z ![σ₁, !σ₁] ![b, a]‖ *
        ‖loopFine d L W H z ![σ₀, !σ₀] ![c', b]‖ := by
  have hHb : (blockMat d L W H).IsHermitian := hH.submatrix _
  set G : Bool → Matrix (Vtx d L W) (Vtx d L W) ℂ := Gres (blockMat d L W H) z with hGdef
  have hG : ∀ s, (G s)ᴴ = G (!s) := Gres_conjTranspose hHb z
  set P : Zd d L → Matrix (Vtx d L W) (Vtx d L W) ℂ := fun x => Pm d L W x with hPdef
  have hPH : ∀ x, (P x)ᴴ = P x := fun x => Pm_conjTranspose x
  have hPPm : ∀ x (X : Matrix (Vtx d L W) (Vtx d L W) ℂ), P x * (P x * X) = P x * X :=
    fun x X => Pm_mul_Pm_mul x X
  set w : ℝ := ((W : ℕ) : ℝ) ^ d with hwdef
  have hWpos : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hw : 0 < w := pow_pos hWpos d
  have hκ : ‖((W : ℂ) ^ d)⁻¹‖ = w⁻¹ := by
    rw [norm_inv, norm_pow, Complex.norm_natCast]
  obtain ⟨Y1, hY1⟩ : ∃ Y : Matrix (Vtx d L W) (Vtx d L W) ℂ, Y = P c * G σ₀ * P a := ⟨_, rfl⟩
  obtain ⟨Y2, hY2⟩ : ∃ Y : Matrix (Vtx d L W) (Vtx d L W) ℂ, Y = P a * G σ₁ * P b := ⟨_, rfl⟩
  obtain ⟨Y3, hY3⟩ : ∃ Y : Matrix (Vtx d L W) (Vtx d L W) ℂ, Y = P b * G σ₀ * P c' := ⟨_, rfl⟩
  have hY1H : Y1ᴴ = P a * G (!σ₀) * P c := by
    rw [hY1]; simp only [Matrix.conjTranspose_mul, hPH, hG, Matrix.mul_assoc]
  have hY2H : Y2ᴴ = P b * G (!σ₁) * P a := by
    rw [hY2]; simp only [Matrix.conjTranspose_mul, hPH, hG, Matrix.mul_assoc]
  have hY3H : Y3ᴴ = P c' * G (!σ₀) * P b := by
    rw [hY3]; simp only [Matrix.conjTranspose_mul, hPH, hG, Matrix.mul_assoc]
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Vtx d L W) (Vtx d L W) ℂ, Z = Y1 * Y2 * Y3 := ⟨_, rfl⟩
  have hZH : Zᴴ = Y3ᴴ * (Y2ᴴ * Y1ᴴ) := by
    rw [hZ]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hZZ : Z * Zᴴ = P c * (G σ₀ * P a * G σ₁ * P b * G σ₀ * P c' * G (!σ₀) * P b * G (!σ₁) *
      P a * G (!σ₀)) * P c := by
    rw [hZH, hY1H, hY2H, hY3H, hZ, hY1, hY2, hY3]
    simp only [Matrix.mul_assoc, hPPm]
  have h6 : loopFine d L W H z ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![a, b, c', b, a, c] =
      (((W : ℂ) ^ d)⁻¹) ^ 6 * (hs Z : ℂ) := by
    rw [emn2Exp2_loop6_eq, ← trace_mul_conjTranspose_eq, hZZ, trace_Pm_sandwich]
  have h2a := emn2Exp2_loop2_hs H z hH σ₀ c a
  have h2b := emn2Exp2_loop2_hs H z hH σ₁ a b
  have h2c := emn2Exp2_loop2_hs H z hH σ₀ b c'
  have n6 : ‖loopFine d L W H z ![σ₀, σ₁, σ₀, !σ₀, !σ₁, !σ₀] ![a, b, c', b, a, c]‖ =
      w⁻¹ ^ 6 * hs Z := by
    rw [h6, norm_mul, norm_pow, hκ, Complex.norm_real, Real.norm_of_nonneg (hs_nonneg _)]
  have n2a : ‖loopFine d L W H z ![σ₀, !σ₀] ![a, c]‖ = w⁻¹ ^ 2 * hs Y1 := by
    rw [h2a, ← hY1, norm_mul, norm_pow, hκ, Complex.norm_real,
      Real.norm_of_nonneg (hs_nonneg _)]
  have n2b : ‖loopFine d L W H z ![σ₁, !σ₁] ![b, a]‖ = w⁻¹ ^ 2 * hs Y2 := by
    rw [h2b, ← hY2, norm_mul, norm_pow, hκ, Complex.norm_real,
      Real.norm_of_nonneg (hs_nonneg _)]
  have n2c : ‖loopFine d L W H z ![σ₀, !σ₀] ![c', b]‖ = w⁻¹ ^ 2 * hs Y3 := by
    rw [h2c, ← hY3, norm_mul, norm_pow, hκ, Complex.norm_real,
      Real.norm_of_nonneg (hs_nonneg _)]
  have hs3 : hs Z ≤ hs Y1 * hs Y2 * hs Y3 := by
    rw [hZ]
    calc hs (Y1 * Y2 * Y3) ≤ hs (Y1 * Y2) * hs Y3 := emn2Exp2_hs_mul_le _ _
      _ ≤ (hs Y1 * hs Y2) * hs Y3 :=
          mul_le_mul_of_nonneg_right (emn2Exp2_hs_mul_le _ _) (hs_nonneg _)
  rw [n6, n2a, n2b, n2c]
  calc w⁻¹ ^ 6 * hs Z ≤ w⁻¹ ^ 6 * (hs Y1 * hs Y2 * hs Y3) := by
        gcongr
    _ = _ := by ring

end Holder


/-! ## 3. Lattice: the neighbour count -/

section Lattice

/-- Each `c` has at most `3^d` neighbours `c'` (`|c - c'|_∞ ≤ 1`): for `q ≥ 0` and a relation `P` inside
the neighbour relation, `Σ_c Σ_{c'} 1_{P c c'} q(c) ≤ 3^d Σ_c q(c)`. -/
private lemma emn2Exp2_sum_nbr_le (d L : ℕ) [NeZero L] (q : Zd d L → ℝ) (hq : ∀ c, 0 ≤ q c)
    (P : Zd d L → Zd d L → Prop) [∀ c c', Decidable (P c c')]
    (hP : ∀ c c', P c c' → zdistInf d L (c - c') ≤ 1) :
    ∑ c : Zd d L, ∑ c' : Zd d L, (if P c c' then q c else 0) ≤ 3 ^ d * ∑ c, q c := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have h1 : ∑ c' : Zd d L, (if P c c' then q c else 0) ≤
      ∑ c' : Zd d L, (if zdistInf d L (c - c') ≤ 1 then q c else 0) := by
    refine Finset.sum_le_sum fun c' _ => ?_
    by_cases hc : P c c'
    · simp [hc, hP c c' hc]
    · simp only [hc, ↓reduceIte]
      split_ifs <;> simp [hq c]
  refine h1.trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c - c') ≤ 1)).card : ℝ) ≤
      3 ^ d := by
    have : (Finset.univ.filter (fun c' : Zd d L => zdistInf d L (c - c') ≤ 1)).card ≤ 3 ^ d := by
      refine le_trans (Finset.card_le_card_of_injOn (fun c' => c - c') ?_ ?_)
        (card_ball_le d L)
      · intro c' hc'
        simpa using (Finset.mem_filter.mp hc').2
      · intro x _ y _ hxy
        simpa using hxy
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcard (hq c)

end Lattice

/-! ## 4. The profile `𝒯_t`: the unit shift and the radial sum `Σ_c 𝒯_t(|c - b|) ≤ C/(1-t)` -/

section Profile

variable {d L : ℕ} {g t : ℝ}

/-- **The unit shift of `𝒯_t`**: `𝒯_t(x) ≤ 2^{d-2} e 𝒯_t(x + 1)` for `x ≥ 0` (`ℓ_t ≥ 1`; `K₁ = 2^{d-2} e`,
the `|c - c'| ≤ 1` comparison of `𝒯_t` in `3_5:880-888`); the merged shift `emn2Exp_tailT_shift` with `s = 1`. -/
private lemma emn2Exp2_tailT_shift1 (hL : 1 ≤ (L : ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    tailT d L g t x ≤ 2 ^ (d - 2) * Real.exp 1 * tailT d L g t (x + 1) := by
  have hℓ : 1 ≤ ellT L g t := one_le_ellT hL
  have hℓ0 : 0 < ellT L g t := by linarith
  have h := emn2Exp_tailT_shift (d := d) (L := L) (g := g) (t := t) hL hx (y := x + 1) (s := 1)
    (by linarith) (by linarith) zero_le_one (by linarith)
  have hsq : Real.sqrt (1 / ellT L g t) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact (div_le_one hℓ0).mpr hℓ
  have hT1 := tailT_nonneg (d := d) (L := L) (g := g) (t := t) (by linarith : 0 ≤ x + 1)
  calc tailT d L g t x ≤ 2 ^ (d - 2) * Real.exp (Real.sqrt (1 / ellT L g t)) *
        tailT d L g t (x + 1) := h
    _ ≤ 2 ^ (d - 2) * Real.exp 1 * tailT d L g t (x + 1) := by
        gcongr

/-- **The radial sum** (`Σ_a 𝒯_t(|a|) ≲ (1 - t)⁻¹`, `3_5:885-888`): for `d = k + 2` and `t < 1`,
`Σ_c 𝒯_t(|c - b|_∞) ≤ (C_rad + 1)/(1 - t)`, `C_rad = d^d 2^d C(1)` depends on `d` only.  The decay term
is `A_t Σ_x (|x|+1)^{-k} e^{-√(|x|/ℓ_t)} ≤ C_rad A_t ℓ_t²` (K2, `pti_sum_radial`) with `A_t ℓ_t² ≤ (1 - t)⁻¹`,
the zero mode `Z_t Σ_x e^{...} ≤ Z_t L^d = (1 - t)⁻¹`. -/
private theorem emn2Exp2_sum_tailT_le (k : ℕ) {L : ℕ} [NeZero L] {g t : ℝ} (hg : 0 ≤ g) (ht : t < 1)
    (b : Zd (k + 2) L) :
    ∑ c : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L (c - b))
      ≤ (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1) + 1) / (1 - t) := by
  have hL1 : (1 : ℝ) ≤ L := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have hv : 0 < 1 - t := by linarith
  have hℓ1 : 1 ≤ ellT L g t := one_le_ellT hL1
  have hre : ∑ c : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L (c - b)) =
      ∑ x : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L x) :=
    Equiv.sum_comp (Equiv.subRight b) (fun x => tailT (k + 2) L g t (zdistInf (k + 2) L x))
  rw [hre]
  set A := (g ^ 2 + |1 - t|)⁻¹ with hA
  set Z := ((L : ℝ) ^ (k + 2) * |1 - t|)⁻¹ with hZ
  have hA0 : 0 ≤ A := inv_nonneg.mpr (by positivity)
  have hZ0 : 0 ≤ Z := inv_nonneg.mpr (by positivity)
  have hrad := pti_sum_radial (L := L) k (κ := 1) (ℓ := ellT L g t) one_pos hℓ1
  simp only [one_mul] at hrad
  have hAℓ : A * ellT L g t ^ 2 ≤ (1 - t)⁻¹ := inv_mul_ellT_sq_le hg hv
  have hcrad : 0 ≤ ((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1) := by
    have := radC_pos (one_pos : (0 : ℝ) < 1)
    positivity
  calc ∑ x : Zd (k + 2) L, tailT (k + 2) L g t (zdistInf (k + 2) L x)
      = ∑ x : Zd (k + 2) L, (A * (((zdistInf (k + 2) L x : ℝ) + 1) ^ k)⁻¹ *
          Real.exp (-√((zdistInf (k + 2) L x : ℝ) / ellT L g t)) +
        Z * Real.exp (-√((zdistInf (k + 2) L x : ℝ) / ellT L g t))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [tailT_natCast]
        simp only [powW]
        ring
    _ = A * ∑ x : Zd (k + 2) L, (((zdistInf (k + 2) L x : ℝ) + 1) ^ k)⁻¹ *
          Real.exp (-√((zdistInf (k + 2) L x : ℝ) / ellT L g t)) +
        Z * ∑ x : Zd (k + 2) L, Real.exp (-√((zdistInf (k + 2) L x : ℝ) / ellT L g t)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]
    _ ≤ A * (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1) * ellT L g t ^ 2) +
        Z * ∑ x : Zd (k + 2) L, (1 : ℝ) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hrad hA0)
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) hZ0)
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
    _ = (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1)) * (A * ellT L g t ^ 2) +
        Z * (L : ℝ) ^ (k + 2) := by
        rw [sum_one_torus]; ring
    _ ≤ (((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1)) * (1 - t)⁻¹ + (1 - t)⁻¹ := by
        refine add_le_add (mul_le_mul_of_nonneg_left hAℓ hcrad) (le_of_eq ?_)
        rw [hZ, abs_of_pos hv]
        have : (L : ℝ) ^ (k + 2) ≠ 0 := by positivity
        field_simp
    _ = _ := by rw [div_eq_mul_inv]; ring

/-- The radial sum with a constant that depends on `d ≥ 3` only. -/
private theorem emn2Exp2_exists_CR (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) [NeZero L] (g t : ℝ), 0 ≤ g → t < 1 → ∀ b : Zd d L,
      ∑ c : Zd d L, tailT d L g t (zdistInf d L (c - b)) ≤ C / (1 - t) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have := radC_pos (one_pos : (0 : ℝ) < 1)
  exact ⟨((k + 2 : ℕ) : ℝ) ^ (k + 2) * (2 ^ (k + 2) * radC 1) + 1, by positivity,
    fun L _ g t hg ht b => emn2Exp2_sum_tailT_le k hg ht b⟩

end Profile


/-! ## 5. The region `R₃`, and the sum of the product of the two profile legs on `A^n` -/

section Region

/-- The condition of the region `R₃` of `emn2ExpS3` (`3_5:842-845`): `|c - c'| ≤ 1`, `ℓ* < |c'-b| ≤ ℓ`,
`ℓ* < |c-a| ≤ ℓ`. -/
private abbrev emn2Exp2_R3 (d L : ℕ) [NeZero L] (ℓs ℓ : ℝ) (a b c c' : Zd d L) : Prop :=
  zdistInf d L (c - c') ≤ 1 ∧
    ((ℓs < (zdistInf d L (c' - b) : ℝ) ∧ (zdistInf d L (c' - b) : ℝ) ≤ ℓ) ∧
      (ℓs < (zdistInf d L (c - a) : ℝ) ∧ (zdistInf d L (c - a) : ℝ) ≤ ℓ))

variable {d L : ℕ} [NeZero L] {g t : ℝ}

/-- **The profile sum on `A^n`** (`3_5:880-888`, `(TTT2)` and `Σ_a 𝒯_t(|a|) ≲ (1 - t)⁻¹`): with
`P(m) = W^{-d} 𝒯̃^ℓ_{t,D}(m)` (`hPfdef`), `T = 𝒯_t`, the pairs `(c, c')` of `R₃` with `P(|a-b|) < P(|c'-b|)` satisfy
`Σ P(|a-c|) P(|c'-b|) ≤ 3^d K₁ W^{-d} (C_T + C_R) P(|a-b|)`, `K₁ = 2^{d-2} e`, where
`Σ_c T(|a-c|) T(|c-b|) ≤ C_T T(|a-b|)` and `Σ_c T(|c-b|) ≤ C_R`.  On `A^n` the leg `P(|c'-b|)` is the tail
`W^{-d} T(|c'-b|)` (it exceeds `P(|a-b|) ≥ W^{-d-D}`), so the floor-floor term `W^{-2D} Σ_c 1` never
occurs; the shift `T(|c'-b|) ≤ K₁ T(|c-b|)` is the unit shift. -/
private theorem emn2Exp2_profile_sum {Wr D ℓ ℓs : ℝ} (hWr : 0 < Wr) (hℓ : 0 ≤ ℓ) (a b : Zd d L)
    {CT CR : ℝ} (hCT : 0 ≤ CT) (hCR : 0 ≤ CR) {Pf : ℕ → ℝ}
    (hPfdef : ∀ m : ℕ, Pf m = (Wr ^ d)⁻¹ * tailW d L g t ℓ Wr D (m : ℝ))
    (hTTT : ∑ c : Zd d L, tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ))
    (hrad : ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤ CR) :
    ∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b)) then
          Pf (zdistInf d L (a - c)) * Pf (zdistInf d L (c' - b))
        else 0) ≤
      3 ^ d * (2 ^ (d - 2) * Real.exp 1) * (Wr ^ d)⁻¹ * (CT + CR) *
        Pf (zdistInf d L (a - b)) := by
  classical
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by
    have := NeZero.ne L
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  set w : ℝ := (Wr ^ d)⁻¹ with hwdef
  have hw : 0 < w := inv_pos.mpr (pow_pos hWr d)
  set K1 : ℝ := 2 ^ (d - 2) * Real.exp 1 with hK1def
  have hK1 : 0 ≤ K1 := by positivity
  set fl : ℝ := Wr ^ (-D) with hfl
  have hfl0 : 0 < fl := Real.rpow_pos_of_pos hWr _
  have hPf0 : ∀ m, 0 ≤ Pf m := fun m => by
    rw [hPfdef m]
    exact mul_nonneg hw.le (tailW_pos (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ) (D := D) hWr _).le
  -- the floor is below every value of `P`
  have hfloor : ∀ m : ℕ, w * fl ≤ Pf m := fun m => by
    rw [hPfdef m]
    exact mul_le_mul_of_nonneg_left (rpow_neg_le_tailW (d := d) (L := L) (g := g) (t := t) (ℓ := ℓ)
      (W := Wr) (D := D) (m : ℝ)) hw.le
  have hPfeq : ∀ m : ℕ, Pf m = w * max (tailT d L g t (min (m : ℝ) ℓ)) fl := fun m => by
    rw [hPfdef m]; rfl
  -- (i) on `A^n` the near leg is the tail
  have hnearTail : ∀ m : ℕ, (m : ℝ) ≤ ℓ → Pf (zdistInf d L (a - b)) < Pf m →
      Pf m ≤ w * tailT d L g t (m : ℝ) := by
    intro m hmℓ hlt
    by_contra hcon
    have h1 : tailT d L g t (m : ℝ) < fl := by
      by_contra h
      apply hcon
      rw [hPfeq m, min_eq_left hmℓ, max_eq_left (not_lt.mp h)]
    have h2 : Pf m = w * fl := by rw [hPfeq m, min_eq_left hmℓ, max_eq_right h1.le]
    have := hfloor (zdistInf d L (a - b))
    linarith
  -- the pointwise bound
  have hterm : ∀ c c' : Zd d L, (emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
      Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b))) →
      Pf (zdistInf d L (a - c)) * Pf (zdistInf d L (c' - b)) ≤
        w ^ 2 * K1 * ((tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) + fl) *
          tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ)) := by
    rintro c c' ⟨⟨hn, ⟨hc'b1, hc'b2⟩, ⟨hca1, hca2⟩⟩, hlt⟩
    have hsc : zdistInf d L (a - c) = zdistInf d L (c - a) := emn2Exp_zdistInf_sub_comm d L a c
    have hm'ℓ : ((zdistInf d L (c' - b) : ℕ) : ℝ) ≤ ℓ := hc'b2
    have hpℓ : ((zdistInf d L (a - c) : ℕ) : ℝ) ≤ ℓ := by rw [hsc]; exact hca2
    have hmc : ((zdistInf d L (c - b) : ℕ) : ℝ) ≤ ((zdistInf d L (c' - b) : ℕ) : ℝ) + 1 := by
      have := emn2Exp_zdistInf_tri d L c c' b
      have h' : zdistInf d L (c - b) ≤ zdistInf d L (c' - b) + 1 := by omega
      exact_mod_cast h'
    have h1 : Pf (zdistInf d L (c' - b)) ≤ w * tailT d L g t ((zdistInf d L (c' - b) : ℕ) : ℝ) :=
      hnearTail _ hm'ℓ hlt
    have h2 : Pf (zdistInf d L (a - c)) ≤
        w * (tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) + fl) := by
      rw [hPfeq, min_eq_left hpℓ]
      exact mul_le_mul_of_nonneg_left
        (max_le_add_of_nonneg (tailT_nonneg (Nat.cast_nonneg _)) hfl0.le) hw.le
    have h3 : tailT d L g t ((zdistInf d L (c' - b) : ℕ) : ℝ) ≤
        K1 * tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) :=
      (emn2Exp2_tailT_shift1 hL1 (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (tailT_antitone (Nat.cast_nonneg _) hmc) hK1)
    have hT1 : 0 ≤ tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) :=
      tailT_nonneg (Nat.cast_nonneg _)
    calc Pf (zdistInf d L (a - c)) * Pf (zdistInf d L (c' - b))
        ≤ (w * (tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) + fl)) *
            (w * (K1 * tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ))) :=
          mul_le_mul h2 (h1.trans (mul_le_mul_of_nonneg_left h3 hw.le)) (hPf0 _) (by positivity)
      _ = _ := by ring
  -- sum over the neighbours
  set q : Zd d L → ℝ := fun c => w ^ 2 * K1 * ((tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) + fl) *
    tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ)) with hq
  have hq0 : ∀ c, 0 ≤ q c := fun c => by
    have h1 : 0 ≤ tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) := tailT_nonneg (Nat.cast_nonneg _)
    have h2 : 0 ≤ tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) := tailT_nonneg (Nat.cast_nonneg _)
    simp only [hq]; positivity
  have hsumq : ∑ c, q c = w ^ 2 * K1 * (∑ c : Zd d L, tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) *
      tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) +
        fl * ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ)) := by
    simp only [hq]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  -- the right-hand side: `T(r) ≤ w⁻¹ P(r)` and `fl ≤ w⁻¹ P(r)`
  have hM : w⁻¹ * Pf (zdistInf d L (a - b)) =
      max (tailT d L g t (min ((zdistInf d L (a - b) : ℕ) : ℝ) ℓ)) fl := by
    rw [hPfeq, ← mul_assoc, inv_mul_cancel₀ hw.ne', one_mul]
  have hTr : tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ) ≤ w⁻¹ * Pf (zdistInf d L (a - b)) := by
    rw [hM]
    refine le_trans ?_ (le_max_left _ _)
    exact tailT_antitone (le_min (Nat.cast_nonneg _) hℓ) (min_le_left _ _)
  have hflM : fl ≤ w⁻¹ * Pf (zdistInf d L (a - b)) := by
    rw [hM]; exact le_max_right _ _
  calc ∑ c : Zd d L, ∑ c' : Zd d L, _
      ≤ ∑ c : Zd d L, ∑ c' : Zd d L,
          (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b)) then q c else 0) := by
        refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun c' _ => ?_
        split_ifs with h
        · exact hterm c c' h
        · exact le_rfl
    _ ≤ 3 ^ d * ∑ c, q c :=
        emn2Exp2_sum_nbr_le d L q hq0 (fun c c' => emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
          Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b))) (fun c c' h => h.1.1)
    _ = 3 ^ d * (w ^ 2 * K1 * (∑ c : Zd d L, tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) *
          tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) +
        fl * ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ))) := by rw [hsumq]
    _ ≤ 3 ^ d * (w ^ 2 * K1 * (CT * (w⁻¹ * Pf (zdistInf d L (a - b))) +
          CR * (w⁻¹ * Pf (zdistInf d L (a - b))))) := by
        have hA : ∑ c : Zd d L, tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) *
            tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤
            CT * (w⁻¹ * Pf (zdistInf d L (a - b))) :=
          hTTT.trans (mul_le_mul_of_nonneg_left hTr hCT)
        have hB : fl * ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤
            CR * (w⁻¹ * Pf (zdistInf d L (a - b))) := by
          calc fl * ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ)
              ≤ fl * CR := mul_le_mul_of_nonneg_left hrad hfl0.le
            _ = CR * fl := by ring
            _ ≤ CR * (w⁻¹ * Pf (zdistInf d L (a - b))) := mul_le_mul_of_nonneg_left hflM hCR
        have hAB := add_le_add hA hB
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAB (by positivity))
          (by positivity)
    _ = 3 ^ d * K1 * w * (CT + CR) * Pf (zdistInf d L (a - b)) := by
        have h2 : w ^ 2 * w⁻¹ = w := by field_simp
        calc 3 ^ d * (w ^ 2 * K1 * (CT * (w⁻¹ * Pf (zdistInf d L (a - b))) +
              CR * (w⁻¹ * Pf (zdistInf d L (a - b)))))
            = 3 ^ d * ((w ^ 2 * w⁻¹) * K1 * (CT + CR) * Pf (zdistInf d L (a - b))) := by ring
          _ = _ := by rw [h2]; ring

end Region

/-! ## 6. The two parts of `S̃₃`: the contraction on `A^f`, the Hölder bound on `A^n` -/

section RegionSums

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **`S̃₃` on `A^f`** (the contraction inequality, as for `S̃₁`, `emn2Exp_part1`): the pairs of `R₃` with
`P(|c'-b|) ≤ P(|a-b|)`, through `stContractPt_holds` with `𝒜 = {c' : ∃ c, …}` and `M = y² P(|a-b|)` (`K = 1`):
`Σ ≤ 3^d/(W^d η) · y² P(|a-b|) · y √P(0) · y² P(|a-b|)`.  No sum over `c`, no `Ĵ`, no condition on `D`. -/
private lemma emn2Exp2_partF (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool)
    (a b : Zd d L) {y ℓs ℓ : ℝ} (hy : 0 ≤ y) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x'))) :
    ∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * Pf (zdistInf d L (a - b))) *
        (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b)))) := by
  set 𝒜 : Finset (Zd d L) := Finset.univ.filter (fun c' : Zd d L => ∃ c : Zd d L,
    emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
      Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b))) with h𝒜
  have hM0 : 0 ≤ y ^ 2 * Pf (zdistInf d L (a - b)) := by
    have := hPf (zdistInf d L (a - b)); positivity
  have hM : ∀ c' ∈ 𝒜, ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^
      (1 / 2 : ℝ) ≤ y ^ 2 * Pf (zdistInf d L (a - b)) := by
    intro c' hc'
    obtain ⟨c, _, hcmp⟩ := (Finset.mem_filter.mp hc').2
    calc ‖loopFine d L W H z ![σ 0, !(σ 0), σ 0, !(σ 0)] ![c', b, c', b]‖ ^ (1 / 2 : ℝ)
        ≤ ‖loopFine d L W H z ![σ 0, !(σ 0)] ![c', b]‖ := emn2Poly_norm_loop4_alt_le H z hH (σ 0) b c'
      _ ≤ y ^ 2 * Pf (zdistInf d L (c' - b)) := h2 (σ 0) c' b
      _ ≤ y ^ 2 * Pf (zdistInf d L (a - b)) := mul_le_mul_of_nonneg_left hcmp (sq_nonneg y)
  have hpin := stContractPt_holds d L W H z hH hz σ a b 𝒜 _ hM0 hM
  have hmax : max ‖loopFine d L W H z ![true, σ 1, !(σ 1)] ![a, b, a]‖
      ‖loopFine d L W H z ![false, σ 1, !(σ 1)] ![a, b, a]‖ ≤
      y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b))) := by
    have e : zdistInf d L (b - a) = zdistInf d L (a - b) := emn2Exp_zdistInf_sub_comm d L b a
    have h3 := emn2Exp_loop3_ctrl H z hH hy h2
    refine max_le ?_ ?_
    · have := h3 true (σ 1) a b; rwa [e] at this
    · have := h3 false (σ 1) a b; rwa [e] at this
  have hK' : 0 ≤ 3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) * (y ^ 2 * Pf (zdistInf d L (a - b))) := by
    have : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
    positivity
  have hrearr : ∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      ∑ c' ∈ 𝒜, ∑ c ∈ Finset.univ.filter (fun c : Zd d L => zdistInf d L (c - c') ≤ 1),
        ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖ := by
    rw [Finset.sum_comm]
    have hz0 : ∀ c' ∉ 𝒜, ∑ c : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) = 0 := by
      intro c' hc'
      refine Finset.sum_eq_zero fun c _ => ?_
      have hn : ¬ (emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b))) := fun hn =>
        hc' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, c, hn⟩)
      simp only [hn, ↓reduceIte]
    calc ∑ c' : Zd d L, ∑ c : Zd d L,
          (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
              Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0)
        = ∑ c' ∈ 𝒜, ∑ c : Zd d L,
          (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
              Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
            ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
            else 0) := by
          symm
          exact Finset.sum_subset (Finset.filter_subset _ _) fun c' _ hc' => hz0 c' hc'
      _ ≤ _ := by
          refine Finset.sum_le_sum fun c' _ => ?_
          rw [← Finset.sum_filter]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
          intro c hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.1.1⟩
  calc _ ≤ _ := hrearr
    _ ≤ _ := hpin
    _ ≤ _ := mul_le_mul_of_nonneg_left hmax hK'

/-- **`S̃₃` on `A^n`** (Hölder, `3_5:871-880`): if every 2-loop of the pattern `(s,-s)` at a distance `> ℓ*`
is at most `F P(|x-x'|)`, then on the pairs of `R₃` with `P(|a-b|) < P(|c'-b|)` (and `|a-b| > ℓ*`),
`Σ |𝓛^{(6)}| ≤ F³ P(|a-b|) Σ P(|a-c|) P(|c'-b|)`: the six legs are `(a,c),(b,a),(c',b)` twice
(`emn2Exp2_loop6_le`). -/
private lemma emn2Exp2_partN (hH : H.IsHermitian) (σ : Fin 2 → Bool) (a b : Zd d L)
    {F ℓs ℓ : ℝ} (hF0 : 0 ≤ F) {Pf : ℕ → ℝ} (hPf : ∀ m, 0 ≤ Pf m)
    (hF : ∀ (s : Bool) (x x' : Zd d L), ℓs < (zdistInf d L (x - x') : ℝ) →
      ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤ F * Pf (zdistInf d L (x - x')))
    (hr : ℓs < (zdistInf d L (a - b) : ℝ)) :
    ∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0) ≤
      F ^ 3 * Pf (zdistInf d L (a - b)) * ∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b)) then
          Pf (zdistInf d L (a - c)) * Pf (zdistInf d L (c' - b)) else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c' _ => ?_
  by_cases h : emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
      Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b))
  · rw [ite_eq_left_iff.mpr (fun hn => absurd h hn), ite_eq_left_iff.mpr (fun hn => absurd h hn)]
    obtain ⟨⟨_, ⟨hc'b, _⟩, ⟨hca, _⟩⟩, _⟩ := h
    have hac : ℓs < (zdistInf d L (a - c) : ℝ) := by
      rw [emn2Exp_zdistInf_sub_comm d L a c]; exact hca
    have hba : ℓs < (zdistInf d L (b - a) : ℝ) := by
      rw [emn2Exp_zdistInf_sub_comm d L b a]; exact hr
    have e : zdistInf d L (b - a) = zdistInf d L (a - b) := emn2Exp_zdistInf_sub_comm d L b a
    have h1 := emn2Exp2_loop6_le H z hH (σ 0) (σ 1) a b c c'
    have l1 := hF (σ 0) a c hac
    have l2 := hF (σ 1) b a hba
    have l3 := hF (σ 0) c' b hc'b
    rw [e] at l2
    refine h1.trans ?_
    calc ‖loopFine d L W H z ![σ 0, !(σ 0)] ![a, c]‖ * ‖loopFine d L W H z ![σ 1, !(σ 1)] ![b, a]‖ *
          ‖loopFine d L W H z ![σ 0, !(σ 0)] ![c', b]‖
        ≤ (F * Pf (zdistInf d L (a - c))) * (F * Pf (zdistInf d L (a - b))) *
            (F * Pf (zdistInf d L (c' - b))) := by
          refine mul_le_mul (mul_le_mul l1 l2 (norm_nonneg _) (mul_nonneg hF0 (hPf _))) l3
            (norm_nonneg _) (mul_nonneg (mul_nonneg hF0 (hPf _)) (mul_nonneg hF0 (hPf _)))
      _ = _ := by ring
  · rw [ite_eq_right_iff.mpr (fun hh => absurd hh h), ite_eq_right_iff.mpr (fun hh => absurd hh h),
      mul_zero]

end RegionSums


/-! ## 7. The deterministic bound of `S̃₃` -/

section S3

variable {d L W : ℕ} [NeZero L] [NeZero W] (H : Matrix (Idx d L W) (Idx d L W) ℂ) (z : ℂ)

/-- **`S̃₃`, deterministically** (`3_5:871-888`, split route): for every Hermitian `H` and `Im z > 0`, if every
2-loop of the pattern `(s,-s)` is at most `y² P(|x-x'|)` and, at distances `> ℓ*`, at most `F P(|x-x'|)`
(`P = W^{-d} 𝒯̃^ℓ_{t,D}`), if `|a-b| > ℓ*` and `(TTT2)`, `Σ_c 𝒯_t(|c-b|) ≤ C_R` hold, then
`S̃₃ ≤ 3^d η⁻¹ y⁵ √P(0) P(|a-b|)² + 3^d K₁ (C_T + C_R) F³ P(|a-b|)²`, `K₁ = 2^{d-2} e`, `η = Im z`.
The first term is the contraction on `A^f`, the second the Hölder bound on `A^n`. -/
theorem emn2Exp2_S3_le (hH : H.IsHermitian) (hz : 0 < z.im) (σ : Fin 2 → Bool) (a b : Zd d L)
    {g t D ℓ ℓs y F CT CR : ℝ} (hℓ : 0 ≤ ℓ) (hy : 0 ≤ y) (hF0 : 0 ≤ F) (hCT : 0 ≤ CT)
    (hCR : 0 ≤ CR) {Pf : ℕ → ℝ}
    (hPfdef : ∀ m : ℕ, Pf m =
      (((W : ℕ) : ℝ) ^ d)⁻¹ * tailW d L g t ℓ ((W : ℕ) : ℝ) D (m : ℝ))
    (h2 : ∀ (s : Bool) (x x' : Zd d L), ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤
      y ^ 2 * Pf (zdistInf d L (x - x')))
    (hF : ∀ (s : Bool) (x x' : Zd d L), ℓs < (zdistInf d L (x - x') : ℝ) →
      ‖loopFine d L W H z ![s, !s] ![x, x']‖ ≤ F * Pf (zdistInf d L (x - x')))
    (hr : ℓs < (zdistInf d L (a - b) : ℝ))
    (hTTT : ∑ c : Zd d L, tailT d L g t ((zdistInf d L (a - c) : ℕ) : ℝ) *
        tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤
      CT * tailT d L g t ((zdistInf d L (a - b) : ℕ) : ℝ))
    (hrad : ∑ c : Zd d L, tailT d L g t ((zdistInf d L (c - b) : ℕ) : ℝ) ≤ CR) :
    emn2ExpS3 H z ℓs ℓ σ a b ≤
      3 ^ d / z.im * y ^ 5 * Real.sqrt (Pf 0) * Pf (zdistInf d L (a - b)) ^ 2 +
        3 ^ d * (2 ^ (d - 2) * Real.exp 1) * (CT + CR) * F ^ 3 * Pf (zdistInf d L (a - b)) ^ 2 := by
  classical
  have hW : (0 : ℝ) < ((W : ℕ) : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne W)
  have hWd : (0 : ℝ) < ((W : ℕ) : ℝ) ^ d := pow_pos hW d
  have hPf0 : ∀ m, 0 ≤ Pf m := fun m => by
    rw [hPfdef m]
    exact mul_nonneg (inv_nonneg.mpr hWd.le) (tailW_pos hW _).le
  -- the split `R₃ = (R₃ ∩ A^f) ⊔ (R₃ ∩ A^n)`
  have hsplit : emn2ExpS3 H z ℓs ℓ σ a b =
      ((W : ℕ) : ℝ) ^ d * ((∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0)) +
        (∑ c : Zd d L, ∑ c' : Zd d L,
        (if emn2Exp2_R3 d L ℓs ℓ a b c c' ∧
            Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b)) then
          ‖loopFine d L W H z ![σ 0, σ 1, σ 0, !(σ 0), !(σ 1), !(σ 0)] ![a, b, c', b, a, c]‖
          else 0))) := by
    unfold emn2ExpS3
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c' _ => ?_
    by_cases h : emn2Exp2_R3 d L ℓs ℓ a b c c'
    · rcases le_or_gt (Pf (zdistInf d L (c' - b))) (Pf (zdistInf d L (a - b))) with hle | hlt
      · have hnlt : ¬ (Pf (zdistInf d L (a - b)) < Pf (zdistInf d L (c' - b))) := not_lt.mpr hle
        rw [ite_eq_left h, ite_eq_left ⟨h, hle⟩, ite_eq_right (fun hh => hnlt hh.2), add_zero]
      · have hnle : ¬ (Pf (zdistInf d L (c' - b)) ≤ Pf (zdistInf d L (a - b))) := not_le.mpr hlt
        rw [ite_eq_left h, ite_eq_right (fun hh => hnle hh.2), ite_eq_left ⟨h, hlt⟩, zero_add]
    · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.1), ite_eq_right (fun hh => h hh.1), add_zero]
  have hFA := emn2Exp2_partF H z hH hz σ a b (ℓs := ℓs) (ℓ := ℓ) hy hPf0 h2
  have hNA := emn2Exp2_partN H z hH σ a b (ℓs := ℓs) (ℓ := ℓ) hF0 hPf0 hF hr
  have hPS := emn2Exp2_profile_sum (g := g) (t := t) (D := D) (ℓs := ℓs) hW hℓ a b hCT hCR hPfdef
    hTTT hrad
  have hF3 : 0 ≤ F ^ 3 * Pf (zdistInf d L (a - b)) := by
    have := hPf0 (zdistInf d L (a - b)); positivity
  rw [hsplit]
  calc ((W : ℕ) : ℝ) ^ d * (_ + _)
      ≤ ((W : ℕ) : ℝ) ^ d * (3 ^ d / (((W : ℕ) : ℝ) ^ d * z.im) *
          (y ^ 2 * Pf (zdistInf d L (a - b))) *
          (y * Real.sqrt (Pf 0) * (y ^ 2 * Pf (zdistInf d L (a - b)))) +
        F ^ 3 * Pf (zdistInf d L (a - b)) *
          (3 ^ d * (2 ^ (d - 2) * Real.exp 1) * (((W : ℕ) : ℝ) ^ d)⁻¹ * (CT + CR) *
            Pf (zdistInf d L (a - b)))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hFA (hNA.trans ?_)) hWd.le
        exact mul_le_mul_of_nonneg_left hPS hF3
    _ = _ := by
        field_simp

end S3


/-! ## 8. `(eq_L2-J)`: the 2-loop at distance `> ℓ*` is at most `(Ĵ + W^{-d}) P` -/

section L2J

variable {d : ℕ} (sz : Sizes d)

/-- `m(σ) m(-σ) = |m|² = 1` for `|E| ≤ 2`. -/
private lemma emn2Exp2_mSigma_mul {E : ℝ} (hE : |E| ≤ 2) (s : Bool) :
    mSigma E s * mSigma E (!s) = 1 := by
  cases s
  · simpa [mul_comm] using KLWard_mSigma_mul hE
  · simpa using KLWard_mSigma_mul hE

/-- `𝒦^{(2)} = W^{-d} m₁ m₂ Θ_{u m₁ m₂}(a₁, a₂)` for the model's `STKloop` (`KLK_two`; copy of the
private `nkl_STKloop_eq` of `Induction/NewKLK.lean`, which is not in the import closure). -/
private lemma emn2Exp2_STKloop_two (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (a : Fin 2 → Zd d (sz.L n)) :
    STKloop sz n E u σ a =
      (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * (mSigma E (σ 0) * mSigma E (σ 1)) *
        Theta d (sz.L n) (sz.lam n) ((u : ℂ) * (mSigma E (σ 0) * mSigma E (σ 1))) (a 0) (a 1) := by
  have h2 : KLloopOf d (sz.L n) σ a = ⟨[σ 0, σ 1], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  unfold STKloop
  rw [h2, KLK_two]

/-- For the pattern `(s,-s)`: `‖𝒦^{(2)}_{(s,-s),(x,x')}‖ = W^{-d} ‖Θ_u(x,x')‖`. -/
private lemma emn2Exp2_norm_STKloop {E : ℝ} (hE : |E| ≤ 2) (n : ℕ) (u : ℝ) (s : Bool)
    (x x' : Zd d (sz.L n)) :
    ‖STKloop sz n E u ![s, !s] ![x, x']‖ =
      (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) x x'‖ := by
  rw [emn2Exp2_STKloop_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [emn2Exp2_mSigma_mul hE s, mul_one, mul_one, norm_mul, norm_inv, norm_pow,
    Complex.norm_natCast]

/-- `‖(𝓛-𝒦)^{(2)}_{σ,a}‖ ≤ Ĵ · W^{-d} 𝒯̃(|a₁-a₂|)`: the definition of `Ĵ` (`STJhatM`). -/
private lemma emn2Exp2_STLKM_le (n : ℕ) (E D ℓ u : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (σ : Fin 2 → Bool) (x : Fin 2 → Zd d (sz.L n)) :
    ‖STLKM sz n E u H σ x‖ ≤ STJhatM sz n E D ℓ u H * STprof sz n u D ℓ (x 0) (x 1) := by
  have hP := ST_STprof_pos sz n u D ℓ (x 0) (x 1)
  have h := Finset.le_sup' (fun p : (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)) =>
    ‖STLKM sz n E u H p.1 p.2‖ / STprof sz n u D ℓ (p.2 0) (p.2 1)) (Finset.mem_univ (σ, x))
  have h' : ‖STLKM sz n E u H σ x‖ / STprof sz n u D ℓ (x 0) (x 1) ≤ STJhatM sz n E D ℓ u H := h
  rwa [div_le_iff₀ hP] at h'

/-- **`(eq_L2-J)`** (`3_5:871-875`): at a distance `x, x'` where `Θ_u(x,x') ≤ W^{-(D+d)}` (the far field of
`kellStarEv` beyond `ℓ*`), the 2-loop `𝓛^{(2)}_{(s,-s),(x,x')} = (𝓛-𝒦) + 𝒦` is at most
`(Ĵ + W^{-d}) W^{-d} 𝒯̃^ℓ_{u,D}(|x-x'|)`: `‖𝒦^{(2)}‖ = W^{-d} ‖Θ_u‖ ≤ W^{-2d-D}` and `P ≥ W^{-d-D}`. -/
theorem emn2Exp2_loop2_far_le (n : ℕ) {E : ℝ} (hE : |E| ≤ 2) (u D ℓ : ℝ)
    (H : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (s : Bool)
    (x x' : Zd d (sz.L n))
    (hΘ : ‖Theta d (sz.L n) (sz.lam n) (u : ℂ) x x'‖ ≤
      ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ)))) :
    ‖loopFine d (sz.L n) (sz.W n) H (zt E u) ![s, !s] ![x, x']‖ ≤
      (STJhatM sz n E D ℓ u H + (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) *
        STprof sz n u D ℓ x x' := by
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := pow_pos hW d
  set w : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ with hwdef
  have hw : 0 < w := inv_pos.mpr hWd
  have hdec : loopFine d (sz.L n) (sz.W n) H (zt E u) ![s, !s] ![x, x'] =
      STLKM sz n E u H ![s, !s] ![x, x'] + STKloop sz n E u ![s, !s] ![x, x'] := by
    simp [STLKM, STLM]
  have hJ := emn2Exp2_STLKM_le sz n E D ℓ u H ![s, !s] ![x, x']
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hJ
  have hK := emn2Exp2_norm_STKloop sz hE n u s x x'
  -- `w · W^{-(D+d)} ≤ w · P`
  have hrpow : ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ))) = ((sz.W n : ℕ) : ℝ) ^ (-D) * w := by
    rw [hwdef, neg_add, Real.rpow_add hW, ← Real.rpow_natCast, ← Real.rpow_neg hW.le]
  have hfloor : ((sz.W n : ℕ) : ℝ) ^ (-D) ≤
      tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D
        ((zdistInf d (sz.L n) (x - x') : ℕ) : ℝ) := rpow_neg_le_tailW _
  have hPle : w * ((sz.W n : ℕ) : ℝ) ^ (-(D + (d : ℝ))) ≤ w * STprof sz n u D ℓ x x' := by
    rw [hrpow]
    unfold STprof
    calc w * (((sz.W n : ℕ) : ℝ) ^ (-D) * w)
        = w * (w * ((sz.W n : ℕ) : ℝ) ^ (-D)) := by ring
      _ ≤ w * (w * tailW d (sz.L n) (sz.lam n) u ℓ ((sz.W n : ℕ) : ℝ) D
          ((zdistInf d (sz.L n) (x - x') : ℕ) : ℝ)) := by gcongr
  rw [hdec]
  calc ‖STLKM sz n E u H ![s, !s] ![x, x'] + STKloop sz n E u ![s, !s] ![x, x']‖
      ≤ ‖STLKM sz n E u H ![s, !s] ![x, x']‖ + ‖STKloop sz n E u ![s, !s] ![x, x']‖ :=
        norm_add_le _ _
    _ ≤ STJhatM sz n E D ℓ u H * STprof sz n u D ℓ x x' + w * STprof sz n u D ℓ x x' := by
        refine add_le_add hJ ?_
        rw [hK]
        exact (mul_le_mul_of_nonneg_left hΘ hw.le).trans hPle
    _ = _ := by ring

end L2J


/-! ## 9. The far sum `S̃₃` on the good event: the hypothesis `h3` of `emn2Exp_of_far3` -/

section Far3

private lemma emn2Exp2_cube_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [mul_nonneg (add_nonneg ha hb) (sq_nonneg (a - b))]

/-- `W^{-3d} ≤ (cB W^{-d})^{1/2}` once `W^{-5d} ≤ cB`: `w³ ≤ B^{1/2}` from `c w ≤ B` and `w⁵ ≤ c`. -/
private lemma emn2Exp2_w3_le {w c B : ℝ} (hw : 0 < w) (hB : c * w ≤ B) (hw5 : w ^ 5 ≤ c) :
    w ^ 3 ≤ B ^ (1 / 2 : ℝ) := by
  have h6 : (w ^ 3) ^ 2 ≤ B := by
    calc (w ^ 3) ^ 2 = w * w ^ 5 := by ring
      _ ≤ w * c := mul_le_mul_of_nonneg_left hw5 hw.le
      _ = c * w := by ring
      _ ≤ B := hB
  rw [← Real.sqrt_eq_rpow]
  calc w ^ 3 = Real.sqrt ((w ^ 3) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt h6

/-- **The real-number assembly of the bound of `S̃₃`**: with `ζ = η⁻¹ (B + J³) P²`, `B = Bctl^{1/2}`,
if `S ≤ c₃ η⁻¹ Y s₀ P² + c₃ K (C_I/v + C_R/v) (J + w)³ P²`, `s₀ ≤ q B`, `w³ ≤ B`, `η ≤ v` and
`2 (A₁ + A₂ + 1) ≤ Y` (`A₁ = c₃ q`, `A₂ = 4 c₃ K (C_I + C_R)`), then `S ≤ Y² ζ`. -/
private lemma emn2Exp2_assemble {S Y η v B q J w P2 s0 c3 K CI CR A1 A2 : ℝ} (hη : 0 < η)
    (hηv : η ≤ v) (hc3 : 0 ≤ c3) (hK : 0 ≤ K) (hCI : 0 ≤ CI) (hCR : 0 ≤ CR)
    (hJ : 0 ≤ J) (hw : 0 ≤ w) (hB : 0 ≤ B) (hP2 : 0 ≤ P2) (hs0 : s0 ≤ q * B)
    (hw3 : w ^ 3 ≤ B)
    (hS : S ≤ c3 / η * Y * s0 * P2 + c3 * K * (CI / v + CR / v) * (J + w) ^ 3 * P2)
    (hA1 : A1 = c3 * q) (hA2 : A2 = 4 * (c3 * K * (CI + CR))) (hA10 : 0 ≤ A1) (hA20 : 0 ≤ A2)
    (hY : 2 * (A1 + A2 + 1) ≤ Y) :
    S ≤ Y * Y * (η⁻¹ * (B + J ^ 3) * P2) := by
  have hv : 0 < v := lt_of_lt_of_le hη hηv
  have hY0 : 0 ≤ Y := by linarith
  have hY1 : 1 ≤ Y := by linarith
  have hJ3 : 0 ≤ J ^ 3 := by positivity
  have hζ0 : 0 ≤ η⁻¹ * (B + J ^ 3) * P2 := by positivity
  -- term 1 (`A^f`)
  have h1 : c3 / η * Y * s0 * P2 ≤ A1 * Y * (η⁻¹ * (B + J ^ 3) * P2) := by
    calc c3 / η * Y * s0 * P2 ≤ c3 / η * Y * (q * B) * P2 := by gcongr
      _ = A1 * Y * (η⁻¹ * B * P2) := by rw [hA1]; field_simp
      _ ≤ A1 * Y * (η⁻¹ * (B + J ^ 3) * P2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ hP2
          exact mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hη.le)
  -- term 2 (`A^n`)
  have h2 : c3 * K * (CI / v + CR / v) * (J + w) ^ 3 * P2 ≤ A2 * (η⁻¹ * (B + J ^ 3) * P2) := by
    have hcube : (J + w) ^ 3 ≤ 4 * (B + J ^ 3) := by
      have := emn2Exp2_cube_le hJ hw
      linarith
    have hvη : v⁻¹ ≤ η⁻¹ := inv_anti₀ hη hηv
    have hKK : 0 ≤ c3 * K * (CI + CR) := by positivity
    calc c3 * K * (CI / v + CR / v) * (J + w) ^ 3 * P2
        = (c3 * K * (CI + CR)) * v⁻¹ * (J + w) ^ 3 * P2 := by field_simp
      _ ≤ (c3 * K * (CI + CR)) * η⁻¹ * (4 * (B + J ^ 3)) * P2 := by
          apply mul_le_mul_of_nonneg_right _ hP2
          exact mul_le_mul (mul_le_mul_of_nonneg_left hvη hKK) hcube (by positivity) (by positivity)
      _ = A2 * (η⁻¹ * (B + J ^ 3) * P2) := by rw [hA2]; ring
  -- the loss
  have hloss : A1 * Y + A2 ≤ Y * Y := by
    have ha : A1 + A2 ≤ Y / 2 := by linarith
    have hb : (A1 + A2) * Y ≤ Y / 2 * Y := mul_le_mul_of_nonneg_right ha hY0
    have hc : A2 ≤ A2 * Y := le_mul_of_one_le_right hA20 hY1
    have hd : 0 ≤ Y * Y := mul_nonneg hY0 hY0
    linarith
  calc S ≤ c3 / η * Y * s0 * P2 + c3 * K * (CI / v + CR / v) * (J + w) ^ 3 * P2 := hS
    _ ≤ A1 * Y * (η⁻¹ * (B + J ^ 3) * P2) + A2 * (η⁻¹ * (B + J ^ 3) * P2) := add_le_add h1 h2
    _ = (A1 * Y + A2) * (η⁻¹ * (B + J ^ 3) * P2) := by ring
    _ ≤ (Y * Y) * (η⁻¹ * (B + J ^ 3) * P2) := mul_le_mul_of_nonneg_right hloss hζ0

variable {d : ℕ} (sz : Sizes d)

/-- `ℓ*_t ≤ ℓ†_t` once `log W ≥ 1`. -/
private lemma emn2Exp2_star_le_dag (n : ℕ) (u : ℝ) (hLg1 : 1 ≤ Real.log ((sz.W n : ℕ) : ℝ)) :
    emn2ExpEllStar sz n u ≤ emn2ExpEllDag sz n u := by
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by
    exact_mod_cast (by have := sz.three_le_L n; omega : 1 ≤ sz.L n)
  have hlt1 : 1 ≤ ellT (sz.L n) (sz.lam n) u := one_le_ellT hL1
  unfold emn2ExpEllStar emn2ExpEllDag
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hLg1 (by norm_num)) (by linarith)

/-- **`S̃₃` on the far pairs** (`3_5:871-888`, the hypothesis `h3` of `emn2Exp_of_far3`): under the premises
of `STEMn2Exp` and `3 ≤ d`, on the pairs with `|a-b| > ℓ†_t`,
`S̃₃ ≺ η_t^{-1} [(W^{-d} B_{t,0})^{1/2} + (Ĵ^ℓ_{t,D})³] (W^{-d} 𝒯̃^ℓ_{t,D}(|a-b|))²`, for **every** `D > 0`.
Proof: on the good event of `(eq:LW_assm_exp)` at `τ/5`, `emn2Exp2_S3_le` with `y = N^{τ/10}`,
`F = Ĵ + W^{-d}` (`emn2Exp2_loop2_far_le`, the far field of `kellStarEv` at `δ = 1`, `D_K = D + d`),
`(TTT2)` (`ekPropTInf_holds`) and the radial sum; `(1-t)⁻¹ ≤ η⁻¹`, `(Ĵ + W^{-d})³ ≤ 4(Ĵ³ + W^{-3d})`,
`W^{-3d} ≤ Bctl^{1/2}` eventually, and the constants `3^d, K₁, C_I, C_R, √(1+cB⁻¹)` are `≤ N^{τ/2}` eventually.
The premises `Ψ`, its window, `STInitialGT2`, `ε₀` and the upper bound on `ℓ` are not used. -/
theorem emn2Exp_far3 (d : ℕ) (hd : 3 ≤ d) :
    ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 →
      ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), STFlow sz κ ε 𝔠 𝔡 z →
        ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ lemT (z n)) →
          ∀ ε₀ : ℝ, 0 < ε₀ → ∀ Ψ : ℕ → ℝ,
            (∀ᶠ n in atTop, ((sz.W n : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ Ψ n ∧
              Ψ n ≤ ((sz.W n : ℕ) : ℝ) ^ (-ε₀)) →
            STInitialGT2 sz (STflowE z) t ε₀ Ψ →
            ∀ ℓ : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ ℓ n ∧ ℓ n ≤ (Real.log ((sz.W n : ℕ) : ℝ)) ^ 10 *
                ellT (sz.L n) (sz.lam n) (t n)) →
              (∀ D : ℝ, 0 < D → STLWassmExp sz (STflowE z) t D ℓ) →
              ∀ D : ℝ, 0 < D →
                Prec sz (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd d (sz.L n)))
                  (fun n p ω => if emn2ExpEllDag sz n (t n) <
                      (zdistInf d (sz.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
                    emn2ExpS3M sz n (STflowE z n) (t n) (ℓ n) p.1 p.2.1 p.2.2 ω else 0)
                  (fun n p ω => (etaT (STflowE z n) (t n))⁻¹ *
                    ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
                      (STJhat sz n (STflowE z n) D (ℓ n) (t n) ω) ^ 3) *
                    (STprof sz n (t n) D (ℓ n) (p.2.2 0) (p.2.2 1)) ^ 2) := by
  intro κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT ε₀ hε₀ Ψ _hΨ _hI ℓ hℓ hA D hD
  classical
  have hsz : sz.SizeTendsto := hflow.1.2.2.1
  have hsize : Tendsto sz.size atTop atTop := tendsto_size sz hsz
  have h𝔠 : 0 < 𝔠 := hflow.1.1
  have hband : sz.Bandwidth 𝔠 := hflow.1.2.2.2.1
  have hWO : sz.WO 𝔡 := hflow.1.2.2.2.2
  have hd0 : 0 < d := by omega
  have hWt := ST_W_tendsto sz hsz h𝔠 hband
  obtain ⟨-, -, ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz hκ hε hflow htT
  have hη : ∀ n, 0 < etaT (STflowE z n) (t n) := by
    intro n
    have hzim := ST_flow_im_pos sz hflow n
    exact etaT_pos (abs_lemE_lt_two hzim) ((htT n).trans_lt (lemT_lt_one hzim))
  have hE2 : ∀ n, |STflowE z n| ≤ 2 := fun n => (abs_lemE_lt_two (ST_flow_im_pos sz hflow n)).le
  -- `η = (1 - t) Im m ≤ 1 - t`
  have hηv : ∀ n, etaT (STflowE z n) (t n) ≤ 1 - t n := by
    intro n
    have h1 : 0 < 1 - t n := by linarith [ht1 n]
    have hm1 : (mE (STflowE z n)).im ≤ 1 := (Complex.im_le_norm _).trans (norm_mE (hE2 n)).le
    unfold etaT
    exact mul_le_of_le_one_right h1.le hm1
  have hW1 : ∀ n, (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  have hWpos : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  obtain ⟨cB, hcB, hBd⟩ := ST_Bdata_holds hd0 κ ε 𝔡 hκ hε h𝔡
  obtain ⟨c, hc, hbd⟩ := hBd 𝔠
  have hbdn := hbd sz z hflow t ht0 htT
  have hBt : ∀ᶠ n in atTop, cB * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ sz.Bctl n (t n) :=
    hbdn.mono fun n hn => (hn (t n) (ht0 n) le_rfl).1
  have hLg1 : ∀ᶠ n in atTop, 1 ≤ Real.log ((sz.W n : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hWt).eventually (eventually_ge_atTop _)
  have hlam : ∀ᶠ n in atTop, 0 < sz.lam n ∧ sz.lam n ≤ 𝔡⁻¹ := by
    filter_upwards [hWO] with n hn
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos (hWpos n) _) hn.1, hn.2⟩
  -- the far field of `Θ_t` beyond `ℓ*_t` (`δ = 1`) at `D_K = D + d`
  have hK := emn2Exp_kellStar_far sz 𝔠 𝔡⁻¹ (ε / 2) 1 (D + (d : ℝ)) t hd h𝔠 (inv_pos.mpr h𝔡)
    (half_pos hε) one_pos hsz hband hrange ht1 hlam
  -- `(TTT2)` and the radial sum: constants depending on `d` only
  obtain ⟨CI, hCI, hTTT⟩ := ekPropTInf_holds d hd
  obtain ⟨CR, hCR, hrad⟩ := emn2Exp2_exists_CR d hd
  obtain ⟨A1, hA1⟩ : ∃ A1 : ℝ, A1 = 3 ^ d * Real.sqrt (1 + cB⁻¹) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = 4 * (3 ^ d * (2 ^ (d - 2) * Real.exp 1) * (CI + CR)) := ⟨_, rfl⟩
  have hA1' : 0 ≤ A1 := by rw [hA1]; positivity
  have hA2' : 0 ≤ A2 := by rw [hA2]; positivity
  -- `W^{-5d} ≤ cB` eventually
  have hw5 : ∀ᶠ n in atTop, ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 ≤ cB := by
    filter_upwards [hWt.eventually (eventually_ge_atTop (max 1 cB⁻¹))] with n hn
    have hW1' : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) := (le_max_left _ _).trans hn
    have hWc : cB⁻¹ ≤ ((sz.W n : ℕ) : ℝ) := (le_max_right _ _).trans hn
    have hwd : ((sz.W n : ℕ) : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := le_self_pow₀ hW1' hd0.ne'
    have hw_le : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ cB := by
      calc (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((sz.W n : ℕ) : ℝ)⁻¹ :=
            inv_anti₀ (hWpos n) hwd
        _ ≤ cB := by
            rw [inv_le_comm₀ (hWpos n) hcB]; exact hWc
    have hw_le1 : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ hW1')
    calc ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹) ^ 5 ≤ (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ :=
          pow_le_of_le_one (inv_nonneg.mpr (pow_nonneg (hWpos n).le d)) hw_le1 (by norm_num)
      _ ≤ cB := hw_le
  refine emn2Exp_stochDomAt_of_subset (hA D hD) ?_
  intro τ hτ
  refine ⟨τ / 5, by positivity, ?_⟩
  have hQ := ST_size_pow_big sz hsize (a := τ / 2) (M := 2 * (A1 + A2 + 1)) (by positivity)
  filter_upwards [hℓ, hBt, hLg1, hK, hw5, hlam, hQ] with n hℓn hBn hLg1n hKn hw5n hlamn hQn
  intro ω hω
  obtain ⟨p, hp⟩ := hω
  by_contra hno
  have hgood : ∀ u' : {σ : Fin 2 → Bool // σ 0 ≠ σ 1} × (Fin 2 → Zd d (sz.L n)),
      ‖Lloop sz n (STflowE z n) (t n) u'.1.1 u'.2 ω‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (τ / 5) * STprof sz n (t n) D (ℓ n) (u'.2 0) (u'.2 1) :=
    fun u' => not_lt.mp fun h => hno ⟨u', h⟩
  obtain ⟨k, σ, a⟩ := p
  have hNpos : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hBpos : 0 ≤ sz.Bctl n (t n) :=
    (mul_nonneg hcB.le (inv_nonneg.mpr (pow_nonneg (hWpos n).le d))).trans hBn
  have hηn := hη n
  by_cases hfar : emn2ExpEllDag sz n (t n) < (zdistInf d (sz.L n) (a 0 - a 1) : ℝ)
  · simp only [hfar, ↓reduceIte] at hp
    set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
    set y : ℝ := N ^ (τ / 10) with hy
    have hy0 : 0 ≤ y := Real.rpow_nonneg hNpos.le _
    have hy2 : y ^ 2 = N ^ (τ / 5) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    have hy5 : y ^ 5 = N ^ (τ / 2) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    have hNτ : N ^ τ = N ^ (τ / 2) * N ^ (τ / 2) := by
      rw [← Real.rpow_add hNpos]; congr 1; ring
    -- the profile `P`
    set Pf : ℕ → ℝ := fun m => emn2ExpPf sz n (t n) D (ℓ n) (m : ℝ) with hPfdef
    have hPfdef' : ∀ m : ℕ, Pf m = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ *
        tailW d (sz.L n) (sz.lam n) (t n) (ℓ n) ((sz.W n : ℕ) : ℝ) D (m : ℝ) := fun m => rfl
    have hPf0 : ∀ m, 0 ≤ Pf m := fun m => by
      change 0 ≤ emn2ExpPf sz n (t n) D (ℓ n) (m : ℝ)
      unfold emn2ExpPf
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hWpos n).le d))
        (tailW_pos (hWpos n) _).le
    have hH : (sz.seqHflow n (t n) ω).IsHermitian := sz.seqHflow_isHermitian n (t n) ω
    have hz' : 0 < (zt (STflowE z n) (t n)).im := by
      rw [← etaT_eq_zt_im]; exact hηn
    have h2 : ∀ (s : Bool) (x x' : Zd d (sz.L n)),
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) (zt (STflowE z n) (t n))
            ![s, !s] ![x, x']‖ ≤ y ^ 2 * Pf (zdistInf d (sz.L n) (x - x')) := by
      intro s x x'
      have hne : (![s, !s] : Fin 2 → Bool) 0 ≠ (![s, !s] : Fin 2 → Bool) 1 := by
        cases s <;> simp
      rw [hy2]
      exact hgood (⟨![s, !s], hne⟩, ![x, x'])
    -- the random control and `(eq_L2-J)`
    obtain ⟨Jh, hJh⟩ : ∃ Jh : ℝ, Jh = STJhat sz n (STflowE z n) D (ℓ n) (t n) ω := ⟨_, rfl⟩
    have hJ0 : 0 ≤ Jh := by
      rw [hJh]; exact ST_JhatM_nonneg sz n _ _ _ _ _
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ := ⟨_, rfl⟩
    have hw : 0 < w := by rw [hwdef]; exact inv_pos.mpr (pow_pos (hWpos n) d)
    have hF : ∀ (s : Bool) (x x' : Zd d (sz.L n)),
        emn2ExpEllStar sz n (t n) < (zdistInf d (sz.L n) (x - x') : ℝ) →
        ‖loopFine d (sz.L n) (sz.W n) (sz.seqHflow n (t n) ω) (zt (STflowE z n) (t n))
            ![s, !s] ![x, x']‖ ≤ (Jh + w) * Pf (zdistInf d (sz.L n) (x - x')) := by
      intro s x x' hfar'
      have hΘ := (hKn 0 (t n) le_rfl (ht0 n) le_rfl x x' (by rw [one_mul]; exact hfar'.le)).1
      have := emn2Exp2_loop2_far_le sz n (hE2 n) (t n) D (ℓ n)
        (sz.seqHflow n (t n) ω) s x x' hΘ
      rw [hJh, hwdef]
      exact this
    have hsw := emn2Exp_sw_dist sz n k a
    have hr : emn2ExpEllStar sz n (t n) <
        (zdistInf d (sz.L n) (emn2ExpSw k a 0 - emn2ExpSw k a 1) : ℝ) := by
      rw [hsw]
      exact lt_of_le_of_lt (emn2Exp2_star_le_dag sz n (t n) hLg1n) hfar
    have hv : 0 < 1 - t n := by linarith [ht1 n]
    have hTTTn := hTTT (sz.L n) (sz.lam n) (t n) (t n) hlamn.1 (ht0 n) le_rfl (ht1 n)
      (le_total _ _) (emn2ExpSw k a 0) (emn2ExpSw k a 1)
    have hradn := hrad (sz.L n) (sz.lam n) (t n) hlamn.1.le (ht1 n) (emn2ExpSw k a 1)
    have hS := emn2Exp2_S3_le (sz.seqHflow n (t n) ω) (zt (STflowE z n) (t n)) hH hz'
      (emn2ExpSw k σ) (emn2ExpSw k a 0) (emn2ExpSw k a 1) (g := sz.lam n) (t := t n) (D := D)
      (ℓ := ℓ n) (ℓs := emn2ExpEllStar sz n (t n)) (y := y) (F := Jh + w) (CT := CI / (1 - t n))
      (CR := CR / (1 - t n)) hℓn.1 hy0 (by positivity) (div_nonneg hCI.le hv.le)
      (div_nonneg hCR.le hv.le) hPfdef' h2 hF hr hTTTn hradn
    rw [hsw] at hS
    -- `Pf 0 ≤ (1 + cB⁻¹) Bctl`
    have hP0 : Pf 0 ≤ (1 + cB⁻¹) * sz.Bctl n (t n) := by
      have := ST_prof_le_Bctl sz n hcB hℓn.1 hD hBn (0 : Zd d (sz.L n)) 0
      rw [emn2Exp_STprof_eq, sub_self, emn2Exp_zdistInf_zero] at this
      simpa [hPfdef] using this
    have hsq0 : Real.sqrt (Pf 0) ≤ Real.sqrt (1 + cB⁻¹) * (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hP0
    have hw3 : w ^ 3 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := by
      rw [hwdef] at hw ⊢
      exact emn2Exp2_w3_le hw hBn hw5n
    unfold emn2ExpS3M at hp
    rw [← etaT_eq_zt_im] at hS
    have hb0 : 0 ≤ (sz.Bctl n (t n)) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hBpos _
    have hfinal := emn2Exp2_assemble (hηn) (hηv n) (by positivity : (0 : ℝ) ≤ 3 ^ d)
      (by positivity : (0 : ℝ) ≤ 2 ^ (d - 2) * Real.exp 1) hCI.le hCR.le hJ0
      hw.le hb0 (sq_nonneg _) hsq0 hw3 hS hA1 hA2 hA1' hA2'
      (by rw [hy5]; exact hQn)
    rw [hy5, ← hNτ] at hfinal
    refine absurd hp (not_lt.mpr (hfinal.trans (le_of_eq ?_)))
    rw [hJh]
    rfl
  · exfalso
    simp only [hfar, ↓reduceIte] at hp
    have : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ * ((etaT (STflowE z n) (t n))⁻¹ *
        ((sz.Bctl n (t n)) ^ (1 / 2 : ℝ) +
          STJhat sz n (STflowE z n) D (ℓ n) (t n) ω ^ 3) *
        (STprof sz n (t n) D (ℓ n) (a 0) (a 1)) ^ 2) := by
      have hJ := ST_JhatM_nonneg sz n (STflowE z n) D (ℓ n) (t n) (sz.seqHflow n (t n) ω)
      have : 0 ≤ STJhat sz n (STflowE z n) D (ℓ n) (t n) ω ^ 3 := by
        unfold STJhat; positivity
      positivity
    linarith

end Far3


/-! ## 10. The pin `STEMn2Exp` -/

section Pin

/-- **`lem: EMn2_N`, third estimate `(eq:MG_conclusion3)`** (`3_5:437-440`, proof `3_5:829-888`): the pin
`STEMn2Exp d` for `d ≥ 3`, from the merged near case `emn2Exp_near`, `S̃₁ + S̃₂` (`emn2Exp_far12`) and the far sum
`S̃₃` (`emn2Exp_far3`) by the assembly `emn2Exp_of_far3`.  For every `D > 0` (the paper's "large `D`" is not needed:
paper-delta candidate `T2118a`).  **`3 ≤ d` is a hypothesis** (the pin has none; see the module docstring). -/
theorem stEMn2Exp_holds (d : ℕ) (hd : 3 ≤ d) : STEMn2Exp d :=
  emn2Exp_of_far3 d (emn2Exp_far3 d hd)

end Pin


end RBM.Gauss.Sizes

/-! ## 11. Compiled nonempty instances at `d = 3`

**Matrix level** (`emn2Exp2_loop6_le`, `emn2Exp2_S3_le`): `d = 3`, `L = 3`, `W = 2`, the Hermitian matrix
`H_{ij} = (i)_0 + (j)_0` (not block diagonal, not a multiple of the identity), `z = 1/2 + i/4`, `σ = (+,-)`,
`a = 0`, `b = (1,1,1)`, the profile `P = W^{-d} 𝒯̃^ℓ_{t,D}` at `ilambda = 1/8`, `t = 1/16`, `ℓ = 1`, `D = 1`,
`ℓ* = 0` (so that `|a - b| = 1 > ℓ*`); the 2-loop control is the deterministic envelope `‖𝓛^{(2)}‖ ≤ η⁻² = 16 ≤ 256 P`
(`P ≥ W^{-d-D} = 1/16`), `(TTT2)` and the radial sum from `ekPropTInf_holds`, `emn2Exp2_exists_CR`.

**Model level** (`emn2Exp2_loop2_far_le`, `emn2Exp_far3`, `stEMn2Exp_holds`): the merged size sequence `sz0`
(`L_n = 4(n+1)`, `W_n = (2(n+1))^5`, `ilambda_n = (2(n+1))^{-6}`), `κ = ε = 𝔡 = 1/10`, `𝔠 = 1/6`,
`z_n = 1/2 + i N_n^{-4/5}` (`flow_z0`), `t ≡ 1/16 ≤ lemT z_n`, `ε₀ = 1/20`, `Ψ_n = W_n^{-1}`, the scale
`ℓ_n = ℓ_t`, every `D > 0`; every deterministic hypothesis is discharged; what stays a hypothesis of the
examples is `STInitialGT2` and `STLWassmExp` (Step 1 / ST-6 chain and the LW gate, other gates' pins; limit
check in the preflight report (a)).  `3 ≤ d` is `by norm_num`. -/

namespace RBM.Gauss.EMn2Exp2Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst
  RBM.Gauss.Step2DefsInst RBM.Path Filter

/-- The instance matrix `H_{ij} = (i)_0 + (j)_0` on `Idx 3 3 2` (copy of the private `EMn2Exp1Inst.exH`). -/
private noncomputable def exH : Matrix (Idx 3 3 2) (Idx 3 3 2) ℂ :=
  Matrix.of fun i j => (((i 0).val + (j 0).val : ℕ) : ℂ)

private theorem exH_herm : exH.IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, exH, Matrix.of_apply]
  rw [add_comm (j 0).val, star_natCast]

private def exZ : ℂ := ⟨1 / 2, 1 / 4⟩

private theorem exZ_im : 0 < exZ.im := by
  change (0 : ℝ) < 1 / 4
  norm_num

private def exB : Zd 3 3 := fun _ => 1

private def exC : Zd 3 3 := fun i => if i = 0 then 1 else 0

private def exC' : Zd 3 3 := fun i => if i = 1 then 1 else 0

/-- **`emn2Exp2_loop6_le`** at the instance matrix: the cut-`0` 6-loop at the four distinct labels
`a = 0`, `b = (1,1,1)`, `c = (1,0,0)`, `c' = (0,1,0)` is at most the product of three 2-loops. -/
example :
    ‖loopFine 3 3 2 exH exZ ![true, false, true, !true, !false, !true] ![0, exB, exC', exB, 0, exC]‖ ≤
      ‖loopFine 3 3 2 exH exZ ![true, !true] ![0, exC]‖ *
        ‖loopFine 3 3 2 exH exZ ![false, !false] ![exB, 0]‖ *
          ‖loopFine 3 3 2 exH exZ ![true, !true] ![exC', exB]‖ :=
  emn2Exp2_loop6_le (L := 3) (W := 2) exH exZ exH_herm true false 0 exB exC exC'

/-- The profile `P = W^{-3} 𝒯̃^1_{1/16,1}` at `L = 3`, `W = 2`, `ilambda = 1/8`. -/
private noncomputable def exPf (m : ℕ) : ℝ :=
  (((2 : ℕ) : ℝ) ^ 3)⁻¹ * tailW 3 3 (1 / 8) (1 / 16) 1 ((2 : ℕ) : ℝ) 1 (m : ℝ)

private theorem exPf_ge (m : ℕ) : (1 / 16 : ℝ) ≤ exPf m := by
  unfold exPf
  have hf := rpow_neg_le_tailW (d := 3) (L := 3) (g := 1 / 8) (t := 1 / 16) (ℓ := 1)
    (W := ((2 : ℕ) : ℝ)) (D := 1) (m : ℝ)
  have h2 : (((2 : ℕ) : ℝ)) ^ (-(1 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg_one]; norm_num
  rw [h2] at hf
  have : (0 : ℝ) < (((2 : ℕ) : ℝ) ^ 3)⁻¹ := by norm_num
  norm_num at this ⊢
  nlinarith

/-- The 2-loops of the instance matrix: `‖𝓛^{(2)}‖ ≤ η⁻² = 16 ≤ 16² P`. -/
private theorem ex_two_loop (s : Bool) (x x' : Zd 3 3) :
    ‖loopFine 3 3 2 exH exZ ![s, !s] ![x, x']‖ ≤ 16 ^ 2 * exPf (zdistInf 3 3 (x - x')) := by
  have hη : (0 : ℝ) < exZ.im := exZ_im
  have hb : (blockMat 3 3 2 exH).IsHermitian := exH_herm.submatrix _
  have h := norm_loopM_le (d := 3) (L := 3) (W := 2) (n := 1) hb (z := exZ) hη
    (by rw [abs_of_pos hη]) ![s, !s] ![x, x']
  have h' : ‖loopFine 3 3 2 exH exZ ![s, !s] ![x, x']‖ ≤ (exZ.im⁻¹) ^ 2 := by
    simpa [loopFine] using h
  have hz : exZ.im⁻¹ = 4 := by
    change ((1 : ℝ) / 4)⁻¹ = 4
    norm_num
  rw [hz] at h'
  have := exPf_ge (zdistInf 3 3 (x - x'))
  nlinarith

/-- **`emn2Exp2_S3_le`** at the instance matrix, for `ℓ* = 0`, `ℓ = 1`, `a = 0`, `b = (1,1,1)`
(`|a - b| = 1 > ℓ*`), `y = 16`, `F = 16²`: `S̃₃ ≤ 3³ η⁻¹ y⁵ √P(0) P(r)² + 3³ K₁ (C_T + C_R) F³ P(r)²` with
`C_T = C_I/(1-t)` from `ekPropTInf_holds` and `C_R/(1-t)` from the radial sum (constants of `d = 3` only);
every hypothesis is discharged. -/
example : ∃ CT CR : ℝ, 0 ≤ CT ∧ 0 ≤ CR ∧
    emn2ExpS3 exH exZ 0 1 ![true, false] 0 exB ≤
      3 ^ 3 / exZ.im * 16 ^ 5 * Real.sqrt (exPf 0) * exPf (zdistInf 3 3 (0 - exB)) ^ 2 +
        3 ^ 3 * (2 ^ (3 - 2) * Real.exp 1) * (CT + CR) * (16 ^ 2) ^ 3 *
          exPf (zdistInf 3 3 (0 - exB)) ^ 2 := by
  obtain ⟨CI, hCI, hTTT⟩ := ekPropTInf_holds 3 (by norm_num)
  obtain ⟨CR, hCR, hrad⟩ := emn2Exp2_exists_CR 3 (by norm_num)
  have hr : (0 : ℝ) < ((zdistInf 3 3 (0 - exB) : ℕ) : ℝ) := by
    have : 0 < zdistInf 3 3 (0 - exB) := by decide
    exact_mod_cast this
  exact ⟨CI / (1 - 1 / 16), CR / (1 - 1 / 16), div_nonneg hCI.le (by norm_num),
    div_nonneg hCR.le (by norm_num),
    emn2Exp2_S3_le (L := 3) (W := 2) exH exZ exH_herm exZ_im ![true, false] 0 exB
      (g := 1 / 8) (t := 1 / 16) (D := 1) (ℓ := 1) (ℓs := 0) (y := 16) (F := 16 ^ 2)
      (CT := CI / (1 - 1 / 16)) (CR := CR / (1 - 1 / 16)) zero_le_one (by norm_num) (by norm_num)
      (div_nonneg hCI.le (by norm_num)) (div_nonneg hCR.le (by norm_num)) (Pf := exPf)
      (fun m => rfl) ex_two_loop (fun s x x' _ => ex_two_loop s x x') hr
      (hTTT 3 (1 / 8) (1 / 16) (1 / 16) (by norm_num) (by norm_num) le_rfl (by norm_num)
        (le_total _ _) 0 exB)
      (hrad 3 (1 / 8) (1 / 16) (by norm_num) (by norm_num) exB)⟩

private theorem sz0_logW (n : ℕ) : 1 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := by
  have h32 : (32 : ℝ) ≤ ((sz0.W n : ℕ) : ℝ) := by
    have : (32 : ℕ) ≤ sz0.W n := by
      change 32 ≤ (2 * (n + 1)) ^ 5
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ (2 * (n + 1)) ^ 5 := Nat.pow_le_pow_left (by omega) 5
    exact_mod_cast this
  have h1 : Real.log 32 ≤ Real.log ((sz0.W n : ℕ) : ℝ) := Real.log_le_log (by norm_num) h32
  have h2 : Real.log 32 = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  linarith

private theorem ℓ_range_inst : ∀ᶠ n in atTop,
    0 ≤ ellT (sz0.L n) (sz0.lam n) (tInst n) ∧
      ellT (sz0.L n) (sz0.lam n) (tInst n) ≤
        (Real.log ((sz0.W n : ℕ) : ℝ)) ^ 10 * ellT (sz0.L n) (sz0.lam n) (tInst n) :=
  Eventually.of_forall fun n => ⟨ellT_nonneg, le_mul_of_one_le_left ellT_nonneg
    (one_le_pow₀ (sz0_logW n))⟩

/-- **`emn2Exp2_loop2_far_le`** (`(eq_L2-J)`) at `sz0`, `t ≡ 1/16`, `D = 1`, `ℓ_n = ℓ_t`: eventually, for every
pair at distance `≥ ℓ*_t`, every sign `s` and every sample `ω`, the 2-loop is at most `(Ĵ + W^{-d}) P`; the far
field `‖Θ_t(x,x')‖ ≤ W^{-(D+d)}` is `emn2Exp_kellStar_far` (`δ = 1`). -/
example : ∀ᶠ n in atTop, ∀ (x x' : Zd 3 (sz0.L n)) (s : Bool) (ω : sz0.SeqΩ),
    emn2ExpEllStar sz0 n (tInst n) ≤ (zdistInf 3 (sz0.L n) (x - x') : ℝ) →
      ‖loopFine 3 (sz0.L n) (sz0.W n) (sz0.seqHflow n (tInst n) ω) (zt (STflowE z0 n) (tInst n))
          ![s, !s] ![x, x']‖ ≤
        (STJhatM sz0 n (STflowE z0 n) 1 (ellT (sz0.L n) (sz0.lam n) (tInst n)) (tInst n)
            (sz0.seqHflow n (tInst n) ω) + (((sz0.W n : ℕ) : ℝ) ^ 3)⁻¹) *
          STprof sz0 n (tInst n) 1 (ellT (sz0.L n) (sz0.lam n) (tInst n)) x x' := by
  obtain ⟨-, -, ht1, hrange⟩ := RBM.Green.v3_premises_of_stFlow sz0 (κ := 1 / 10) (ε := 1 / 10)
    (by norm_num) (by norm_num) flow_z0 sixteenth_le_lemT
  have hlam : ∀ᶠ n : ℕ in atTop, 0 < sz0.lam n ∧ sz0.lam n ≤ (1 / 10 : ℝ)⁻¹ := by
    have hWO : sz0.WO (1 / 10) := flow_z0.1.2.2.2.2
    filter_upwards [hWO] with n hn
    have hW : (0 : ℝ) < ((sz0.W n : ℕ) : ℝ) := by exact_mod_cast sz0.W_pos n
    exact ⟨lt_of_lt_of_le (Real.rpow_pos_of_pos hW _) hn.1, hn.2⟩
  have hK := emn2Exp_kellStar_far sz0 (1 / 6) (1 / 10)⁻¹ (1 / 10 / 2) 1 (1 + ((3 : ℕ) : ℝ)) tInst
    le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) sz0_tendsto sz0_bandwidth hrange
    ht1 hlam
  filter_upwards [hK] with n hn x x' s ω hfar
  have hE : |STflowE z0 n| ≤ 2 :=
    (abs_lemE_lt_two (ST_flow_im_pos sz0 flow_z0 n)).le
  exact emn2Exp2_loop2_far_le sz0 n hE (tInst n) 1 _ _ s x x'
    (hn 0 (tInst n) le_rfl (by simp only [tInst]; norm_num) le_rfl x x' (by rwa [one_mul])).1

/-- **`emn2Exp_far3`** (`S̃₃` in the far case `|a - b| > ℓ†_t`, the hypothesis `h3` of `emn2Exp_of_far3`) at
the instance data above, `ε₀ = 1/20`, `Ψ_n = W_n^{-1}`, `ℓ_n = ℓ_t`, every `D > 0`. -/
example
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D →
      STLWassmExp sz0 (STflowE z0) tInst D (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)))
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => if emn2ExpEllDag sz0 n (tInst n) <
          (zdistInf 3 (sz0.L n) (p.2.2 0 - p.2.2 1) : ℝ) then
        emn2ExpS3M sz0 n (STflowE z0 n) (tInst n) (ellT (sz0.L n) (sz0.lam n) (tInst n))
            p.1 p.2.1 p.2.2 ω else 0)
      (fun n p ω => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        ((sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) +
          (STJhat sz0 n (STflowE z0 n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (tInst n) ω) ^ 3) *
        (STprof sz0 n (tInst n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (p.2.2 0) (p.2.2 1)) ^ 2) :=
  emn2Exp_far3 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num) (by norm_num)
    (1 / 6) sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num) sixteenth_le_lemT (1 / 20)
    (by norm_num) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))) Ψ1_window hI
    (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) ℓ_range_inst hA D hD

/-- **`stEMn2Exp_holds`** (the pin `STEMn2Exp 3`, `(eq:MG_conclusion3)`) at the same data: for both cuts, all
signs and labels, `‖(𝓔⊗𝓔)^{M,(2;k)}‖ ≺ η_t⁻¹ [(W^{-d} B_{t,0})^{1/2} + Ĵ³] P²`, every `D > 0`. -/
example
    (hI : STInitialGT2 sz0 (STflowE z0) tInst (1 / 20) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ))))
    (hA : ∀ D : ℝ, 0 < D →
      STLWassmExp sz0 (STflowE z0) tInst D (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)))
    (D : ℝ) (hD : 0 < D) :
    Prec sz0 (U := fun n => Fin 2 × (Fin 2 → Bool) × (Fin 2 → Zd 3 (sz0.L n)))
      (fun n p ω => ‖STEEk sz0 n (STflowE z0 n) (tInst n) p.1 p.2.1 p.2.2 ω‖)
      (fun n p ω => (etaT (STflowE z0 n) (tInst n))⁻¹ *
        ((sz0.Bctl n (tInst n)) ^ (1 / 2 : ℝ) +
          (STJhat sz0 n (STflowE z0 n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (tInst n) ω) ^ 3) *
        (STprof sz0 n (tInst n) D (ellT (sz0.L n) (sz0.lam n) (tInst n)) (p.2.2 0) (p.2.2 1)) ^ 2) :=
  stEMn2Exp_holds 3 (by norm_num) (1 / 10) (1 / 10) (1 / 10) (by norm_num) (by norm_num)
    (by norm_num) (1 / 6) sz0 z0 flow_z0 tInst (fun n => by simp only [tInst]; norm_num)
    sixteenth_le_lemT (1 / 20) (by norm_num) (fun n => ((sz0.W n : ℕ) : ℝ) ^ (-(1 : ℝ)))
    Ψ1_window hI (fun n => ellT (sz0.L n) (sz0.lam n) (tInst n)) ℓ_range_inst hA D hD

/-- **The downstream pin fits**: `STEMn2Exp d` is discharged in `ST_step2_of_pins'` by `stEMn2Exp_holds` (the
consumer `STStep2 d` is under `3 ≤ d →`); the five other pins stay hypotheses. -/
example (d : ℕ) (hNew : STNewKLK d) (hLWT : STLWT d) (hMart : STGridMart d) (hOpt : STOptL2 d)
    (hClos : STLocalAvgOfL2 d) : STStep2 d :=
  fun hd3 => ST_step2_of_pins' hNew hLWT (stEMn2Exp_holds d hd3) hMart hOpt hClos hd3

end RBM.Gauss.EMn2Exp2Inst
