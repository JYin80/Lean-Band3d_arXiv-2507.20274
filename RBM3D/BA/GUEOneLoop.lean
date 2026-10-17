/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.GUEPhase.OneLoop
import RBM3D.Universality.GUEPhase.Drift
import RBM3D.BA.GreenStab
import RBM3D.BA.EKNonzero
import RBM3D.BA.EMn2BA
import RBM3D.Chain.ExpAvgGen

/-!
# BA-C4 row a: Lemma 5.15 on the GUE-phase grid at block Anderson (`BA/GUEOneLoop`)

Ticket T2517 (row a; DECISIONS §339, §340; design gate D1 signed by
`docs/reports/T2517-1a-audit.md`).  New BA leaf: no merged file is edited.  Band twin:
`Universality/GUEPhase/OneLoop.lean` (`gueGrid_expect_oneLoop:1308`, T2353); chain twin:
`Chain/ExpAvgGen.lean` (`lem:improve_exp_aver` at a matrix `M`, T2502 c).  Paper: arXiv:2507.20274
`paper/tex/6_Step6_two_loop.tex:12-21` ("the same as [YY_25, Lemma 5.15]").  Private pieces of
`OneLoop` and `ExpAvgGen` are read by `open private`; helpers not pinned by the ticket are
`private` with the stem `GUEOneLoop_`.

* §1 (target 1) `gueHBA`, the BA grid path `g Ψ_I + H_k` (`H_k` of the model `sz.withLam 0`,
  `S^{(B)}(0) = 1`), `gueHBA_isHermitian`, `gueHBA_succ`, `ol_gueHBA_eq`.
* §2 (target 2) `baOneLoop_gap` (`κ⁴/16 ≤ |1 - u r_a|`, `r_a = Σ_b M_{ab}²`), `baOneLoop_stable`
  (stability of `1 - M^{(+,+)} Ŝ`, `Ŝ = t₁ 1 + σ J`, `K = 16 κ⁻⁴ (1 + 16 κ⁻⁴)`).
* §3 (target 3) the mixed-law Stein layer and `GUEOneLoop_blockId`:
  `𝔼 g_a - m = Σ_{p,q} Ŝ_{pq} 𝔼[t_{ap} (g_q - m)]`, `t_{ap} = W^d tr(G E_a M E_p)`.
* §4-§5 the core (`R_a` against the pathwise inputs and the envelopes), the bound at one grid time,
  **`gueGrid_expect_oneLoopBA`** (target 4): `h1` and `hoff` (`|t_{aq} - M^{(+,+)}_{aq}| ≺
  |M_{aq}| (N η_u)⁻¹`) give `|𝔼 g_a - m| ≤ N^ε (N η_u)⁻²` (bad event at `D = 7`).
* §6 (target 5) compiled nonempty instances at `d = 3`, `sz0` and the BA flow datum of `sz0`.
-/

set_option linter.style.longLine false

open private ExpAvgGen_G_cont ExpAvgGen_G_norm ExpAvgGen_trG_bdd ExpAvgGen_trace3_le ExpAvgGen_norm_GXG
  ExpAvgGen_trace_expand ExpAvgGen_resolvent_id ExpAvgGen_Hb_herm ExpAvgGen_trace_four ExpAvgGen_trace_Eblk
  ExpAvgGen_Gres_blockMat ExpAvgGen_blockMat_one ExpAvgGen_blockMat_sub_smul
  ExpAvgGen_blockMat_mul from RBM3D.Chain.ExpAvgGen
open private OneLoop_integrable_coord_smul OneLoop_integrable_of_cont_bdd OneLoop_sum_gue_block
  OneLoop_blockMat_Xmat OneLoop_gloop_one OneLoop_sum_Eblk OneLoop_card_Zd from
  RBM3D.Universality.GUEPhase.OneLoop

noncomputable section

namespace RBM.BA

open MeasureTheory Filter Matrix RBM RBM.Gauss RBM.Path RBM.Loop RBM.Univ RBM.Univ.GUEPhase
open scoped NNReal ENNReal

/-! ## 1. Target 1: the BA grid path -/

/-- **Target 1, the BA grid path `g Ψ_I + H_k`** (`H_k` of the model `sz.withLam 0`, `S^{(B)}(0) = 1`):
`PsiI` is read at `sz.withLam 0` (the sizes of `sz` and `sz.withLam 0` agree by `rfl`), so that
the sum has one matrix type; it is `rfl`-equal to the reading `g • PsiI d (sz.L n) (sz.W n) + gueH …`. -/
def gueHBA {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) :
    Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ :=
  ((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n) + gueH (sz.withLam 0) t1 t0 K n k ω

theorem gueHBA_isHermitian {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ)
    (ω : PathΩ (sz.withLam 0)) : (gueHBA sz g t1 t0 K n k ω).IsHermitian := by
  have h1 : (((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n)).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star ((g n : ℝ) : ℂ) = ((g n : ℝ) : ℂ) from Complex.conj_ofReal _]
  exact h1.add (gueH_isHermitian (sz.withLam 0) t1 t0 K n k ω)

/-- **The one-step recursion** `H_{k+1} = H_k + √(Δ/N) X_{k+1}` of the BA grid path (`gueH_succ` at `sz.withLam 0`,
shifted by `g Ψ_I`). -/
theorem gueHBA_succ {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) :
    gueHBA sz g t1 t0 K n (k + 1) ω
      = gueHBA sz g t1 t0 K n k ω
        + show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
          (Real.sqrt (gridStep t1 t0 K n / (((sz.withLam 0).size n : ℕ) : ℝ)) : ℂ) •
            Sizes.seqXmat (sz.withLam 0) n (ω (k + 1)) := by
  have h := congrArg (fun X => ((g n : ℝ) : ℂ) • PsiI d ((sz.withLam 0).L n) ((sz.withLam 0).W n) + X)
    (gueH_succ (sz.withLam 0) t1 t0 K n k ω)
  simp only [← add_assoc] at h
  exact h

/-- **The one-time law of the BA grid path** (`ol_gueH_eq`, `OneLoop:125`, at `sz.withLam 0`): `H_k` is `Xmat` of
the size-`n` slice of `√t₁ ω₀ + √(Δ/N) Σ_{i ≤ k} ω_i`, shifted by `g Ψ_I`. -/
theorem ol_gueHBA_eq {d : ℕ} (sz : Sizes d) (g t1 t0 : ℕ → ℝ) (K : ℕ → ℕ) (n k : ℕ) (ω : PathΩ (sz.withLam 0)) :
    gueHBA sz g t1 t0 K n k ω
      = ((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n) +
        show Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ from
          Xmat d ((sz.withLam 0).L n) ((sz.withLam 0).W n)
            (Sizes.slice (sz.withLam 0) n (olComb (sz.withLam 0) (Real.sqrt (t1 n))
              (Real.sqrt (gridStep t1 t0 K n / (((sz.withLam 0).size n : ℕ) : ℝ))) k ω)) := by
  unfold gueHBA
  rw [ol_gueH_eq (sz.withLam 0) t1 t0 K n k ω]
  rfl

/-! ## 2. Target 2: the zero-mode gap and the block stability of `1 - M^{(+,+)} Ŝ`

`Ŝ = t₁ 1 + σ J` (`S^{(B)}(0) = 1`), `u = t₁ + L^d σ`; `Q = M^{(+,+)}`, `Q_{ab} = M_{ba} M_{ab}`. -/

/-- **The zero-mode gap** (replaces the band `gapK κ ≤ |1 - u m²|`, `OneLoop_gapK_le_norm`): at real-axis data
every row sum `r_a = Σ_b M_{ab}²` of `Q` satisfies `κ⁴/16 ≤ |1 - u r_a|` for `0 ≤ u ≤ 1`.  Route: `Q_{aa} = m²`
(`BAMss_ss_diag`), `Σ_{b ≠ a} |Q_{ab}| = 1 - |m|²` (`BAMss_row_offdiag_sum`) and
`ε ≤ |1 - u m²|`, `1 - |m|² ≤ (1 - ε)|1 - u m²|` (`BAoffDiag_scalar`, `ε = κ²/4`, `t = u`):
`|1 - u r_a| ≥ ε |1 - u m²| ≥ ε²`. -/
theorem baOneLoop_gap :
    ∀ κ : ℝ, 0 < κ → ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m →
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 → ∀ a : Zd d L,
        κ ^ 4 / 16 ≤ ‖1 - (u : ℂ) * ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b‖ := by
  intro κ hκ d L _ g E m hr u hu0 hu1 a
  have hn : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  obtain ⟨hD1, hD2⟩ := BAoffDiag_scalar κ u m hκ hr.2 hn hu0 hu1
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) true true with hQ
  have hdiag : Q a a = m ^ 2 := by simpa using BAMss_ss_diag d L g (E : ℂ) m hr.1 true a
  have hoff : ∑ b ∈ Finset.univ.erase a, ‖Q a b‖ = 1 - ‖m‖ ^ 2 :=
    BAMss_row_offdiag_sum d L g E m hr.1 true a
  have hsplit : ∑ b, Q a b = m ^ 2 + ∑ b ∈ Finset.univ.erase a, Q a b := by
    rw [← hdiag]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  have hR : ‖∑ b ∈ Finset.univ.erase a, Q a b‖ ≤ 1 - ‖m‖ ^ 2 := hoff ▸ norm_sum_le _ _
  have h1m : 0 ≤ 1 - ‖m‖ ^ 2 := by nlinarith [norm_nonneg m]
  have hε : 0 < κ ^ 2 / 4 := by positivity
  set A : ℂ := 1 - (u : ℂ) * m ^ 2 with hA
  have hid : 1 - (u : ℂ) * ∑ b, Q a b = A - (u : ℂ) * ∑ b ∈ Finset.univ.erase a, Q a b := by
    rw [hsplit, hA]; ring
  have hB : ‖(u : ℂ) * ∑ b ∈ Finset.univ.erase a, Q a b‖ ≤ (1 - κ ^ 2 / 4) * ‖A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hu0]
    calc u * ‖∑ b ∈ Finset.univ.erase a, Q a b‖ ≤ 1 * (1 - ‖m‖ ^ 2) :=
          mul_le_mul hu1 hR (norm_nonneg _) zero_le_one
      _ ≤ (1 - κ ^ 2 / 4) * ‖A‖ := by rw [one_mul]; exact hD2
  have h2 : ‖A‖ - (1 - κ ^ 2 / 4) * ‖A‖ ≤ ‖1 - (u : ℂ) * ∑ b, Q a b‖ := by
    rw [hid]
    have := norm_sub_norm_le A ((u : ℂ) * ∑ b ∈ Finset.univ.erase a, Q a b)
    linarith
  calc κ ^ 4 / 16 = κ ^ 2 / 4 * (κ ^ 2 / 4) := by ring
    _ ≤ κ ^ 2 / 4 * ‖A‖ := mul_le_mul_of_nonneg_left hD1 hε.le
    _ = ‖A‖ - (1 - κ ^ 2 / 4) * ‖A‖ := by ring
    _ ≤ _ := h2

open private EKNonzero_row_sum EKNonzero_col_sum from RBM3D.BA.EKNonzero

/-- **Target 2, block stability of `1 - M^{(+,+)} Ŝ`** (twin of the private `OneLoop_stable`, `OneLoop:857`),
`Ŝ = t₁ 1 + σ J` (`S^{(B)}(0) = 1`), `u = t₁ + L^d σ ≤ 1`: the constant `K = 16 κ⁻⁴ (1 + 16 κ⁻⁴)` depends on `κ`
only (uniform in `d`, `L`, `g`, `E`, `m`, `t₁`, `σ`).  Route: the sum `S = Σ x` through `baOneLoop_gap`
(the row sums of `Q` equal the column sums and are constant, `EKNonzero_Mss_shift`): `(1 - u r) S = Σ y`;
then `x - t₁ Q x = y + σ r S` by `baStab_of_real` at `t = t₁`. -/
theorem baOneLoop_stable :
    ∀ κ : ℝ, 0 < κ → ∃ K : ℝ, 0 < K ∧ ∀ (d L : ℕ) [NeZero L] (g E : ℝ) (m : ℂ), BAReal d L g κ E m →
      ∀ t1 σ : ℝ, 0 ≤ t1 → 0 ≤ σ → t1 + (L : ℝ) ^ d * σ ≤ 1 →
        ∀ (x y : Zd d L → ℂ) (B : ℝ), (∀ a, ‖y a‖ ≤ B) →
          (∀ a, x a = ∑ b, BAMss d L (BAMB d L g (E : ℂ) m) true true a b *
            ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) + y a) →
          ∀ a, ‖x a‖ ≤ K * B := by
  intro κ hκ
  refine ⟨16 * κ⁻¹ ^ 4 * (1 + 16 * κ⁻¹ ^ 4), by positivity, ?_⟩
  intro d L _ g E m hr t1 σ ht1 hσ hu x y B hB hx a
  set Q := BAMss d L (BAMB d L g (E : ℂ) m) true true with hQ
  have hn : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have hLσ : 0 ≤ (L : ℝ) ^ d * σ := by positivity
  set u : ℝ := t1 + (L : ℝ) ^ d * σ with hudef
  have hu0 : 0 ≤ u := by positivity
  have ht11 : t1 ≤ 1 := by linarith
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hcard : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by simp [Zd, ZMod.card]
  have hT : ∀ a b r : Zd d L, Q (a + r) (b + r) = Q a b :=
    fun a b r => EKNonzero_Mss_shift (d := d) (L := L) g E m true true a b r
  set r : ℂ := ∑ c, Q 0 c with hr_def
  have hrow : ∀ a, ∑ c, Q a c = r := fun a => EKNonzero_row_sum hT a
  have hcol : ∀ b, ∑ c, Q c b = r := fun b => EKNonzero_col_sum hT b
  -- `|r| ≤ 1`
  have hrn : ‖r‖ ≤ 1 := by
    have hdiag : Q 0 0 = m ^ 2 := by simpa using BAMss_ss_diag d L g (E : ℂ) m hr.1 true (0 : Zd d L)
    have hoff : ∑ b ∈ Finset.univ.erase (0 : Zd d L), ‖Q 0 b‖ = 1 - ‖m‖ ^ 2 :=
      BAMss_row_offdiag_sum d L g E m hr.1 true 0
    calc ‖r‖ ≤ ∑ c, ‖Q 0 c‖ := norm_sum_le _ _
      _ = ‖Q 0 0‖ + ∑ b ∈ Finset.univ.erase (0 : Zd d L), ‖Q 0 b‖ :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
      _ = 1 := by rw [hoff, hdiag, norm_pow]; ring
  -- the average: `(1 - u r) S = Σ y`
  obtain ⟨S, hS⟩ : ∃ S : ℂ, S = ∑ c, x c := ⟨_, rfl⟩
  simp only [← hS] at hx
  have hcardC : (Fintype.card (Zd d L) : ℂ) = (L : ℂ) ^ d := by simp [Zd, ZMod.card]
  have hsb : ∑ b : Zd d L, ((t1 : ℂ) * x b + (σ : ℂ) * S) = (u : ℂ) * S := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hS, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcardC, hudef]
    push_cast
    ring
  have hsum : (1 - (u : ℂ) * r) * S = ∑ a, y a := by
    have e1 : ∑ a, ∑ b, Q a b * ((t1 : ℂ) * x b + (σ : ℂ) * S) = r * ((u : ℂ) * S) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hcol]
      rw [← Finset.mul_sum, hsb]
    have h1 : S = r * ((u : ℂ) * S) + ∑ a, y a := by
      conv_lhs => rw [hS, Finset.sum_congr rfl fun a _ => hx a]
      rw [Finset.sum_add_distrib, e1]
    linear_combination h1
  have hgap : κ ^ 4 / 16 ≤ ‖1 - (u : ℂ) * r‖ := baOneLoop_gap κ hκ d L g E m hr u hu0 hu 0
  have hgpos : 0 < κ ^ 4 / 16 := by positivity
  have hY : ‖∑ a, y a‖ ≤ (L : ℝ) ^ d * B := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ a, ‖y a‖ ≤ ∑ _a : Zd d L, B := Finset.sum_le_sum fun a _ => hB a
      _ = (L : ℝ) ^ d * B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  have hSle : ‖S‖ ≤ (L : ℝ) ^ d * B / (κ ^ 4 / 16) := by
    rw [le_div_iff₀ hgpos]
    calc ‖S‖ * (κ ^ 4 / 16) ≤ ‖S‖ * ‖1 - (u : ℂ) * r‖ := mul_le_mul_of_nonneg_left hgap (norm_nonneg _)
      _ = ‖∑ a, y a‖ := by rw [← hsum, norm_mul, mul_comm]
      _ ≤ _ := hY
  -- the remainder `y' = y + σ r S` and `x - t₁ Q x = y'`
  have hy' : ∀ a, ‖y a + (σ : ℂ) * r * S‖ ≤ (1 + 16 * κ⁻¹ ^ 4) * B := by
    intro a
    have e : (16 * κ⁻¹ ^ 4 : ℝ) = 1 / (κ ^ 4 / 16) := by field_simp
    calc ‖y a + (σ : ℂ) * r * S‖ ≤ ‖y a‖ + ‖(σ : ℂ) * r * S‖ := norm_add_le _ _
      _ ≤ B + σ * ((L : ℝ) ^ d * B / (κ ^ 4 / 16)) := by
          refine add_le_add (hB a) ?_
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ]
          calc σ * ‖r‖ * ‖S‖ ≤ σ * 1 * ((L : ℝ) ^ d * B / (κ ^ 4 / 16)) := by gcongr
            _ = _ := by ring
      _ = B + ((L : ℝ) ^ d * σ) * B / (κ ^ 4 / 16) := by ring
      _ ≤ B + 1 * B / (κ ^ 4 / 16) := by
          have : (L : ℝ) ^ d * σ ≤ 1 := by linarith
          gcongr
      _ = (1 + 16 * κ⁻¹ ^ 4) * B := by rw [e]; ring
  have hxr : ∀ a, ‖x a - (t1 : ℂ) * ∑ b, Q a b * x b‖ ≤ (1 + 16 * κ⁻¹ ^ 4) * B := by
    intro a
    have h3 : x a - (t1 : ℂ) * ∑ b, Q a b * x b = y a + (σ : ℂ) * r * S := by
      rw [hx a]
      have : ∑ b, Q a b * ((t1 : ℂ) * x b + (σ : ℂ) * S) =
          (t1 : ℂ) * ∑ b, Q a b * x b + (σ : ℂ) * S * r := by
        have h1 : ∑ b, Q a b * ((t1 : ℂ) * x b + (σ : ℂ) * S) =
            ∑ b, ((t1 : ℂ) * (Q a b * x b) + (σ : ℂ) * S * Q a b) :=
          Finset.sum_congr rfl fun b _ => by ring
        rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hrow a]
      rw [this]
      ring
    rw [h3]
    exact hy' a
  have := baStab_of_real d L g κ E m hκ hr t1 ht1 ht11 x _ hxr a
  calc ‖x a‖ ≤ 16 * κ⁻¹ ^ 4 * ((1 + 16 * κ⁻¹ ^ 4) * B) := this
    _ = _ := by ring

/-! ## 3. Target 3: the BA block identity (D1 (i))

The Stein identity for the product Gaussian `GaussianProduct.law v` of the step-`k` coordinate variances
`v_c = t₁ gvar_c + c₀ w_c` (`w_c = 1` on the diagonal, `1/2` off it), at `H₀ + H`, `H₀ ≠ 0`, for a trace
`tr(P X G Q)`: the mixed-law twin of `ExpAvgGen_stein_trace` (`ExpAvgGen:348`, law `PF g`, `H = √u X`);
`Ŝ_{pq} = t₁ S^{(B)}_{pq} + σ`, `σ = c₀ W^d`.  Then `x_a = Σ_{p,q} Ŝ_{pq} 𝔼[t_{ap} (g_q - m)]`, the twin of
`ExpAvgGen_selfcons_fixed` (`:470`) on the block-product index, `t_{ap} = W^d tr(G E_a M E_p)`. -/

section Stein

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- One-coordinate Stein identity for `tr(P B_c G Q)`, `G = (H₀ + H - z)⁻¹`, under the product Gaussian `law v`
(`ExpAvgGen_stein_coord`, `ExpAvgGen:237`, at flow time `1` with the law `law v`). -/
private theorem GUEOneLoop_stein_coord (v : CoordF d L W → ℝ≥0) {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) (c : CoordF d L W) :
    ∫ ω : Ω d L W, ω c • Matrix.trace (P * coordinateBlock d L W c * Gres (H₀b + HflowBlock d L W 1 ω) z true * Q)
        ∂(GaussianProduct.law v) =
      (v c : ℝ) • ∫ ω : Ω d L W, Matrix.trace (P * coordinateBlock d L W c *
        (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * coordinateBlock d L W c *
          Gres (H₀b + HflowBlock d L W 1 ω) z true)) * Q) ∂(GaussianProduct.law v) := by
  set B := coordinateBlock d L W c with hB
  let f : Ω d L W → ℂ := fun ω => Matrix.trace (P * B * Gres (H₀b + HflowBlock d L W 1 ω) z true * Q)
  let f' : Ω d L W → ℂ := fun ω => Matrix.trace (P * B * (-(Gres (H₀b + HflowBlock d L W 1 ω) z true * B *
    Gres (H₀b + HflowBlock d L W 1 ω) z true)) * Q)
  have hGc := ExpAvgGen_G_cont hH 1 hz
  have hgc : Continuous f := (continuous_matrixTrace d L W).comp ((continuous_const.mul hGc).mul continuous_const)
  have hg'c : Continuous f' :=
    (continuous_matrixTrace d L W).comp ((continuous_const.mul (((hGc.mul continuous_const).mul hGc).neg)).mul
      continuous_const)
  have hderiv : ∀ ω : Ω d L W, HasDerivAt (fun t : ℝ => f (Function.update ω c t)) (f' ω) (ω c) := by
    intro ω
    set T : Matrix (Vtx d L W) (Vtx d L W) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap (Vtx d L W) ℂ ℂ).restrictScalars ℝ)
    have hT : ∀ M, T M = Matrix.trace M := fun _ => rfl
    have h1 := hasDerivAt_green_moving
      (H := fun t : ℝ => H₀b + HflowBlock d L W 1 (Function.update ω c t)) (z := fun _ => z)
      ((hasDerivAt_HflowBlock_update d L W 1 ω c).const_add H₀b) (hasDerivAt_const (ω c) z)
      (by simpa only [Function.update_eq_self] using ExpAvgGen_Hb_herm hH 1 ω) hz
    have h2 := ((hasDerivAt_const (ω c) (P * B)).mul h1).mul_const Q
    have h3 := T.hasFDerivAt.comp_hasDerivAt (ω c) h2
    refine h3.congr_deriv ?_
    simp only [hT, f', zero_mul, zero_add, Function.update_eq_self, zero_smul, sub_zero, Real.sqrt_one,
      one_smul, ← hB]
  have hgb : ∃ C : ℝ, ∀ ω, ‖f ω‖ ≤ C :=
    ⟨(((L * W) ^ d : ℕ) : ℝ) * (‖P * B‖ * |z.im|⁻¹ * ‖Q‖),
      fun ω => ExpAvgGen_trace3_le _ _ _ (ExpAvgGen_G_norm hH 1 hz ω)⟩
  have hg'b : ∃ C : ℝ, ∀ ω, ‖f' ω‖ ≤ C := by
    refine ⟨(((L * W) ^ d : ℕ) : ℝ) * (‖P * B‖ * ((|z.im|⁻¹ * ‖B‖ * |z.im|⁻¹)) * ‖Q‖), fun ω => ?_⟩
    have hM : ‖-(Gres (H₀b + HflowBlock d L W 1 ω) z true * B * Gres (H₀b + HflowBlock d L W 1 ω) z true)‖ ≤
        |z.im|⁻¹ * ‖B‖ * |z.im|⁻¹ := by
      rw [norm_neg]
      exact ExpAvgGen_norm_GXG _ _ (ExpAvgGen_G_norm hH 1 hz ω)
    exact ExpAvgGen_trace3_le _ _ _ hM
  exact GaussianProduct.stein v c f f' hgc hg'c hderiv hgb hg'b

/-- Integrability of the integrands of the Stein identity for a continuous `G` with `‖G‖ ≤ r`, under `law v`
(`ExpAvgGen_stein_int`, `ExpAvgGen:303`, with the law `law v`). -/
private theorem GUEOneLoop_stein_int (v : CoordF d L W → ℝ≥0) (r : ℝ) {G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ}
    (hGc : Continuous G) (hGn : ∀ ω, ‖G ω‖ ≤ r) (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    (∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => ω c • Matrix.trace (P * coordinateBlock d L W c * G ω * Q))
      (GaussianProduct.law v)) ∧
    (∀ c : CoordF d L W, Integrable (fun ω : Ω d L W => Matrix.trace (P * coordinateBlock d L W c *
      (-(G ω * coordinateBlock d L W c * G ω)) * Q)) (GaussianProduct.law v)) ∧
    (∀ p : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p))
      (GaussianProduct.law v)) ∧
    (∀ q : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Eblk d L W q)) (GaussianProduct.law v)) ∧
    (∀ p q : Zd d L, Integrable (fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p) *
      Matrix.trace (G ω * Eblk d L W q)) (GaussianProduct.law v)) := by
  have hc1 : ∀ p : Zd d L, Continuous fun ω : Ω d L W => Matrix.trace (G ω * Q * P * Eblk d L W p) := fun p =>
    (continuous_matrixTrace d L W).comp (((hGc.mul continuous_const).mul continuous_const).mul continuous_const)
  have hc2 : ∀ q : Zd d L, Continuous fun ω : Ω d L W => Matrix.trace (G ω * Eblk d L W q) := fun q =>
    (continuous_matrixTrace d L W).comp (hGc.mul continuous_const)
  have hb1 : ∀ (p : Zd d L) (ω : Ω d L W), ‖Matrix.trace (G ω * Q * P * Eblk d L W p)‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖) := by
    intro p ω
    have e : G ω * Q * P * Eblk d L W p = G ω * (Q * P * Eblk d L W p) := by simp only [Matrix.mul_assoc]
    rw [e]
    exact ExpAvgGen_trG_bdd _ _ (hGn ω)
  have hb2 : ∀ (q : Zd d L) (ω : Ω d L W), ‖Matrix.trace (G ω * Eblk d L W q)‖ ≤
      (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Eblk d L W q‖) :=
    fun q ω => ExpAvgGen_trG_bdd _ _ (hGn ω)
  refine ⟨fun c => ?_, fun c => ?_, fun p => ?_, fun q => ?_, fun p q => ?_⟩
  · refine OneLoop_integrable_coord_smul d L W v c _
      ((continuous_matrixTrace d L W).comp ((continuous_const.mul hGc).mul continuous_const)).measurable
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖P * coordinateBlock d L W c‖ * r * ‖Q‖)) fun ω => ?_
    exact ExpAvgGen_trace3_le _ _ _ (hGn ω)
  · refine OneLoop_integrable_of_cont_bdd d L W v ((continuous_matrixTrace d L W).comp ((continuous_const.mul
      (((hGc.mul continuous_const).mul hGc).neg)).mul continuous_const))
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖P * coordinateBlock d L W c‖ *
        ((r * ‖coordinateBlock d L W c‖ * r)) * ‖Q‖)) fun ω => ?_
    have hM : ‖-(G ω * coordinateBlock d L W c * G ω)‖ ≤ r * ‖coordinateBlock d L W c‖ * r := by
      rw [norm_neg]
      exact ExpAvgGen_norm_GXG _ _ (hGn ω)
    exact ExpAvgGen_trace3_le _ _ _ hM
  · exact OneLoop_integrable_of_cont_bdd d L W v (hc1 p) (hb1 p)
  · exact OneLoop_integrable_of_cont_bdd d L W v (hc2 q) (hb2 q)
  · refine OneLoop_integrable_of_cont_bdd d L W v ((hc1 p).mul (hc2 q))
      (C := ((((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖)) *
        ((((L * W) ^ d : ℕ) : ℝ) * (r * ‖Eblk d L W q‖))) fun ω => ?_
    have hr0 : 0 ≤ r := (norm_nonneg _).trans (hGn ω)
    have hA : 0 ≤ (((L * W) ^ d : ℕ) : ℝ) * (r * ‖Q * P * Eblk d L W p‖) :=
      mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hr0 (norm_nonneg _))
    change ‖Matrix.trace (G ω * Q * P * Eblk d L W p) * Matrix.trace (G ω * Eblk d L W q)‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (hb1 p ω) (hb2 q ω) (norm_nonneg _) hA

/-- `tr X = W^d Σ_p tr(X E_p)` (`Σ_p E_p = W^{-d} 1`; the step `htr` of `OneLoop_contraction`). -/
private theorem GUEOneLoop_trace_eq (X : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    Matrix.trace X = ((W : ℂ) ^ d) * ∑ p : Zd d L, Matrix.trace (X * Eblk d L W p) := by
  have hW : (W : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne W)
  have h := congrArg (fun M => Matrix.trace (X * M)) (OneLoop_sum_Eblk d L W)
  simp only [Finset.mul_sum, Matrix.trace_sum, Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_one,
    smul_eq_mul] at h
  rw [h]
  field_simp

/-- The bookkeeping of the mixed profile: `t₁ (W^d Σ a S b) + c₀ W^d (W^d Σ a)(Σ b) = W^d Σ_{p,q} (t₁ S_{pq} + c₀ W^d) a_p b_q`. -/
private theorem GUEOneLoop_alg {ι : Type*} [Fintype ι] (t1 c0 Wd : ℂ) (a b : ι → ℂ) (s : ι → ι → ℂ) :
    t1 * (Wd * ∑ p, ∑ q, a p * s p q * b q) + c0 * Wd * ((Wd * ∑ p, a p) * (∑ q, b q)) =
      Wd * ∑ p, ∑ q, (t1 * s p q + c0 * Wd) * (a p * b q) := by
  have h : (∑ p, a p) * (∑ q, b q) = ∑ p, ∑ q, a p * b q := Finset.sum_mul_sum _ _ _ _
  have e : ∑ p, ∑ q, (t1 * s p q + c0 * Wd) * (a p * b q) =
      t1 * ∑ p, ∑ q, a p * s p q * b q + c0 * Wd * ∑ p, ∑ q, a p * b q := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [e, ← h]
  ring

/-- **Pointwise contraction under the mixed variances** `v_c = t₁ gvar_c + c₀ w_c`:
`Σ_c v_c tr(P B_c (-(G B_c G)) Q) = -W^d Σ_{p,q} Ŝ_{pq} tr(G Q P E_p) tr(G E_q)`, `Ŝ = t₁ S^{(B)} + σ`, `σ = c₀ W^d`
(the `t₁` part is `sum_coordinateBlock_trace_pair`, the `c₀` part is `OneLoop_sum_gue_block`; twin of
`ExpAvgGen_contract`, `ExpAvgGen:275`, and of `OneLoop_contraction`, `OneLoop:484`, for general `P`, `Q`). -/
private theorem GUEOneLoop_contract (g : ℝ) {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    (G P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
      (-(G * coordinateBlock d L W c * G)) * Q) =
      -(((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L g p q + (σ : ℂ)) *
        (Matrix.trace (G * Q * P * Eblk d L W p) * Matrix.trace (G * Eblk d L W q))) := by
  have hterm : ∀ c : CoordF d L W, ((v c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
      (-(G * coordinateBlock d L W c * G)) * Q) =
      -(((v c : ℝ) : ℂ) * Matrix.trace (G * Q * P * coordinateBlock d L W c * G * coordinateBlock d L W c)) := by
    intro c
    set B := coordinateBlock d L W c
    have h1 : P * B * (-(G * B * G)) * Q = -((P * B * G * B) * (G * Q)) := by
      simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    have h2 : Matrix.trace ((P * B * G * B) * (G * Q)) = Matrix.trace (G * Q * P * B * G * B) := by
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.trace_neg, h2]
    ring
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hvC : ∀ c : CoordF d L W, ((v c : ℝ) : ℂ) =
      (t1 : ℂ) * ((gvarF d L W g c : ℝ) : ℂ) + (c0 : ℂ) * (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) := by
    intro c
    rw [hv c]
    split_ifs <;> push_cast <;> ring
  have hsplit : ∑ c : CoordF d L W, ((v c : ℝ) : ℂ) *
        Matrix.trace (G * Q * P * coordinateBlock d L W c * G * coordinateBlock d L W c) =
      (t1 : ℂ) * ∑ c : CoordF d L W, ((gvarF d L W g c : ℝ) : ℂ) *
        Matrix.trace (G * Q * P * coordinateBlock d L W c * G * coordinateBlock d L W c) +
      (c0 : ℂ) * ∑ c : CoordF d L W, (if c.1 = c.2.1 then (1 : ℂ) else 1 / 2) *
        Matrix.trace (G * Q * P * coordinateBlock d L W c * G * coordinateBlock d L W c) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hvC c]
    ring
  rw [hsplit, sum_coordinateBlock_trace_pair d L W g (G * Q * P) G, OneLoop_sum_gue_block d L W (G * Q * P) G,
    GUEOneLoop_trace_eq (G * Q * P), GUEOneLoop_trace_eq G, hσ]
  have h := GUEOneLoop_alg (t1 : ℂ) (c0 : ℂ) ((W : ℂ) ^ d) (fun p => Matrix.trace (G * Q * P * Eblk d L W p))
    (fun q => Matrix.trace (G * Eblk d L W q)) (fun p q => SB d L g p q)
  beta_reduce at h
  push_cast
  linear_combination h

/-- **The Stein identity at `H₀ + H`** under `law v` (twin of `ExpAvgGen_stein_trace`, `ExpAvgGen:348`):
`𝔼 tr(P X G Q) = -W^d Σ_{p,q} Ŝ_{pq} 𝔼[tr(G Q P E_p) tr(G E_q)]`, `G = (H₀ + X - z)⁻¹`. -/
private theorem GUEOneLoop_stein_trace (g : ℝ) {t1 c0 σ : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W g c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z : ℂ} (hz : z.im ≠ 0)
    (P Q : Matrix (Vtx d L W) (Vtx d L W) ℂ) :
    ∫ ω : Ω d L W, Matrix.trace (P * blockMat d L W (Xmat d L W ω) * Gres (H₀b + HflowBlock d L W 1 ω) z true * Q)
        ∂(GaussianProduct.law v) =
      -(((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L g p q + (σ : ℂ)) * ∫ ω : Ω d L W,
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Q * P * Eblk d L W p) *
          Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W q) ∂(GaussianProduct.law v)) := by
  classical
  obtain ⟨G, hG⟩ : ∃ G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ,
      ∀ ω, G ω = Gres (H₀b + HflowBlock d L W 1 ω) z true := ⟨_, fun _ => rfl⟩
  have hGc : Continuous G :=
    (funext hG : G = fun ω => Gres (H₀b + HflowBlock d L W 1 ω) z true) ▸ ExpAvgGen_G_cont hH 1 hz
  have hGn : ∀ ω, ‖G ω‖ ≤ |z.im|⁻¹ := fun ω => (hG ω) ▸ ExpAvgGen_G_norm hH 1 hz ω
  simp only [← hG]
  obtain ⟨hI1, hI2, -, -, hF0⟩ := GUEOneLoop_stein_int v (|z.im|⁻¹) hGc hGn P Q
  simp_rw [ExpAvgGen_trace_expand]
  rw [integral_finsetSum _ (fun c _ => hI1 c)]
  have hst : ∀ c : CoordF d L W, ∫ ω : Ω d L W, ω c • Matrix.trace (P * coordinateBlock d L W c * G ω * Q)
      ∂(GaussianProduct.law v) =
      ∫ ω : Ω d L W, ((v c : ℝ) : ℂ) * Matrix.trace (P * coordinateBlock d L W c *
        (-(G ω * coordinateBlock d L W c * G ω)) * Q) ∂(GaussianProduct.law v) := by
    intro c
    have := GUEOneLoop_stein_coord v hH hz P Q c
    simp only [← hG] at this
    rw [this, integral_const_mul, Complex.real_smul]
  simp_rw [hst]
  rw [← integral_finsetSum _ (fun c _ => (hI2 c).const_mul _)]
  simp_rw [GUEOneLoop_contract g hσ v hv]
  have hF : ∀ p q : Zd d L, Integrable (fun ω : Ω d L W => ((t1 : ℂ) * SB d L g p q + (σ : ℂ)) *
      (Matrix.trace (G ω * Q * P * Eblk d L W p) * Matrix.trace (G ω * Eblk d L W q))) (GaussianProduct.law v) :=
    fun p q => (hF0 p q).const_mul _
  rw [integral_neg, integral_const_mul,
    integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => hF p q))]
  congr 2
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ (fun q _ => hF p q)]
  exact Finset.sum_congr rfl fun q _ => by rw [integral_const_mul]

/-- **The BA block identity** (target 3; D1 (i)): for `(H₀ - (z + u m)) M = 1`, the block average `tr(M E_a) = m`,
the row sums `u = t₁ + L^d σ` of `Ŝ = t₁ S^{(B)} + σ`, and `G = (H₀ + X - z)⁻¹` with `X ~ law v`, writing
`g_q = tr(G E_q)` and `t_{ap} = W^d tr(G E_a M E_p) = W^{-d} Σ_{x∈[a], y∈[p]} M_{xy} G_{yx}`:
`𝔼 g_a - m = Σ_{p,q} Ŝ_{pq} 𝔼[t_{ap} (g_q - m)]` (twin of `ExpAvgGen_selfcons_fixed`, `ExpAvgGen:470`,
on the block-product index; band `OneLoop_selfcons`, `OneLoop:700`, is `M = m`). -/
theorem GUEOneLoop_blockId (hL : 3 ≤ L) {t1 c0 σ u : ℝ} (hσ : σ = c0 * (W : ℝ) ^ d)
    (hu : t1 + (L : ℝ) ^ d * σ = u) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0)
    (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1)
    (hm : ∀ a : Zd d L, Matrix.trace (Mb * Eblk d L W a) = m) (a : Zd d L) :
    (∫ ω : Ω d L W, Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W a)
        ∂(GaussianProduct.law v)) - m =
      ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * ∫ ω : Ω d L W,
        (((W : ℂ) ^ d) * Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W a * Mb *
          Eblk d L W p)) *
          (Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W q) - m)
        ∂(GaussianProduct.law v) := by
  classical
  have hM1 : (H₀b - (z + ((1 : ℝ) : ℂ) * ((u : ℂ) * m)) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1 := by
    simpa using hM
  obtain ⟨G, hG⟩ : ∃ G : Ω d L W → Matrix (Vtx d L W) (Vtx d L W) ℂ,
      ∀ ω, G ω = Gres (H₀b + HflowBlock d L W 1 ω) z true := ⟨_, fun _ => rfl⟩
  have hGc : Continuous G :=
    (funext hG : G = fun ω => Gres (H₀b + HflowBlock d L W 1 ω) z true) ▸ ExpAvgGen_G_cont hH 1 hz
  have hGn : ∀ ω, ‖G ω‖ ≤ |z.im|⁻¹ := fun ω => (hG ω) ▸ ExpAvgGen_G_norm hH 1 hz ω
  have hst := GUEOneLoop_stein_trace 0 hσ v hv hH hz Mb (Eblk d L W a)
  simp only [← hG] at hst ⊢
  obtain ⟨hI1, -, hIp, hIq, hIpq⟩ := GUEOneLoop_stein_int v (|z.im|⁻¹) hGc hGn Mb (Eblk d L W a)
  have hW : ((W : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne W))
  -- the resolvent identity, pointwise
  have hpt : ∀ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a) = Matrix.trace (Mb * Eblk d L W a) -
      ((u : ℂ) * m) * Matrix.trace (Mb * G ω * Eblk d L W a) -
      Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a) := by
    intro ω
    have h := ExpAvgGen_resolvent_id (Mb := Mb) hH hz hM1 ω
    rw [← hG] at h
    have h2 : G ω * Eblk d L W a = Mb * Eblk d L W a - (((u : ℂ) * m) • (Mb * G ω * Eblk d L W a) +
        (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) := by
      conv_lhs => rw [h]
      simp only [Complex.ofReal_one, one_mul, Real.sqrt_one, one_smul, Matrix.sub_mul, Matrix.mul_add,
        Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [h2, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
    ring
  have hi1 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * G ω * Eblk d L W a)) (GaussianProduct.law v) :=
    OneLoop_integrable_of_cont_bdd d L W v ((continuous_matrixTrace d L W).comp
      ((continuous_const.mul hGc).mul continuous_const))
      (C := (((L * W) ^ d : ℕ) : ℝ) * (‖Mb‖ * |z.im|⁻¹ * ‖Eblk d L W a‖)) fun ω =>
        ExpAvgGen_trace3_le _ _ _ (hGn ω)
  have hi2 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω *
      Eblk d L W a)) (GaussianProduct.law v) := by
    have : (fun ω : Ω d L W => Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)) =
        fun ω => ∑ c : CoordF d L W, ω c • Matrix.trace (Mb * coordinateBlock d L W c * G ω * Eblk d L W a) :=
      funext fun ω => ExpAvgGen_trace_expand _ _ _ ω
    rw [this]
    exact integrable_finsetSum _ fun c _ => hI1 c
  have i1 : Integrable (fun ω : Ω d L W => Matrix.trace (Mb * Eblk d L W a) -
      ((u : ℂ) * m) * Matrix.trace (Mb * G ω * Eblk d L W a)) (GaussianProduct.law v) :=
    (integrable_const _).sub (hi1.const_mul _)
  have hX : (∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a) ∂(GaussianProduct.law v)) - m =
      -(((u : ℂ) * m) * ∫ ω : Ω d L W, Matrix.trace (Mb * G ω * Eblk d L W a) ∂(GaussianProduct.law v)) -
        ∫ ω : Ω d L W, Matrix.trace (Mb * blockMat d L W (Xmat d L W ω) * G ω * Eblk d L W a)
          ∂(GaussianProduct.law v) := by
    simp_rw [hpt]
    rw [integral_sub i1 hi2, integral_sub (integrable_const _) (hi1.const_mul _), integral_const_mul,
      integral_const]
    simp only [probReal_univ, one_smul, hm a]
    ring
  rw [hst] at hX
  -- the pointwise identity `tr(M G E_a) = Σ_p t_{ap}`
  have hT : ∀ ω : Ω d L W, Matrix.trace (Mb * G ω * Eblk d L W a) =
      ((W : ℂ) ^ d) * ∑ p : Zd d L, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) := by
    intro ω
    have h1 : Matrix.trace (Mb * G ω * Eblk d L W a) = Matrix.trace (G ω * Eblk d L W a * Mb) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [h1, GUEOneLoop_trace_eq (G ω * Eblk d L W a * Mb)]
  simp_rw [hT] at hX
  rw [integral_const_mul, integral_finsetSum _ (fun p _ => hIp p)] at hX
  -- the row sums of the profile
  have hrow : ∀ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) = (u : ℂ) := by
    intro p
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_SB_row d L 0 hL p, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, OneLoop_card_Zd d L, ← hu]
    push_cast
    ring
  -- the centred integrals
  have hcen : ∀ p q : Zd d L, ∫ ω : Ω d L W, (((W : ℂ) ^ d) * Matrix.trace (G ω * Eblk d L W a * Mb *
        Eblk d L W p)) * (Matrix.trace (G ω * Eblk d L W q) - m) ∂(GaussianProduct.law v) =
      ((W : ℂ) ^ d) * ((∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
        Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v)) -
        m * ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v)) := by
    intro p q
    have e : ∀ ω : Ω d L W, (((W : ℂ) ^ d) * Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p)) *
        (Matrix.trace (G ω * Eblk d L W q) - m) =
        ((W : ℂ) ^ d) * (Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
          Matrix.trace (G ω * Eblk d L W q) -
          m * Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p)) := fun ω => by ring
    simp only [e]
    rw [integral_const_mul, integral_sub (hIpq p q) ((hIp p).const_mul m), integral_const_mul]
  simp only [hcen]
  have hrhs : ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
      (((W : ℂ) ^ d) * ((∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
        Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v)) -
        m * ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v))) =
      ((W : ℂ) ^ d) * ∑ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
        ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
          Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v) -
      ((u : ℂ) * m) * (((W : ℂ) ^ d) * ∑ p : Zd d L, ∫ ω : Ω d L W,
        Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v)) := by
    have h1 : ∀ p : Zd d L, ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
        (((W : ℂ) ^ d) * ((∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
          Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v)) -
          m * ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v))) =
        ((W : ℂ) ^ d) * ∑ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
          ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
            Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v) -
        ((u : ℂ) * m) * (((W : ℂ) ^ d) * ∫ ω : Ω d L W,
          Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v)) := by
      intro p
      have e : ∀ q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
          (((W : ℂ) ^ d) * ((∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
            Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v)) -
            m * ∫ ω : Ω d L W, Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v))) =
          ((W : ℂ) ^ d) * (((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * ∫ ω : Ω d L W,
            Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) *
              Matrix.trace (G ω * Eblk d L W q) ∂(GaussianProduct.law v)) -
          (((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * (m * (W : ℂ) ^ d)) * ∫ ω : Ω d L W,
            Matrix.trace (G ω * Eblk d L W a * Mb * Eblk d L W p) ∂(GaussianProduct.law v) :=
        fun q => by ring
      simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hrow p]
      ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hrhs, hX]
  ring

end Stein

/-! ## 4. The core: from the pathwise input to the expectation bound at one grid time

`R_a = Σ_{p,q} Ŝ_{pq} 𝔼[(t_{ap} - Q_{ap})(g_q - m)]`, `Q = M^{(+,+)}`: on the good event
`|t_{ap} - Q_{ap}| ≤ ρ |M_{ap}| Λ_u` (`hoff`) and `|g_q - m| ≤ ρ Λ_u` (`h1`), and the row `ℓ¹` bound of `M^{(B)}`
(`baM_row_l1`) give `|R_a| ≤ ρ² u C_M Λ_u²`; the bad event is bounded by the envelopes. -/

section Core

open scoped Matrix.Norms.L2Operator

variable {d L W : ℕ} [NeZero L] [NeZero W]

/-- The centred block 1-loop `g_b(ω) - m`, `g_b = tr(G E_b)`, `G = (H₀ + X(ω) - z)⁻¹` (`X` at flow time `1`). -/
private def GUEOneLoop_Phi (d L W : ℕ) [NeZero L] [NeZero W] (H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z m : ℂ)
    (b : Zd d L) (ω : Ω d L W) : ℂ :=
  Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W b) - m

/-- The `M`-weighted block trace `t_{ap}(ω) = W^d tr(G E_a M E_p) = W^{-d} Σ_{x∈[a], y∈[p]} M_{xy} G_{yx}`. -/
private def GUEOneLoop_Tt (d L W : ℕ) [NeZero L] [NeZero W] (H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ) (z : ℂ)
    (a p : Zd d L) (ω : Ω d L W) : ℂ :=
  ((W : ℂ) ^ d) * Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω) z true * Eblk d L W a * Mb * Eblk d L W p)

/-- **D1 (i), the pathwise step** (compiled at the 1a, `probe_R_good`): `|τ_p| ≤ ρ w_p Λ₁` (`hoff`, `w = |M^{(B)}_{a·}|`)
and `|γ_q| ≤ ρ Λ₂` (`h1`) give `|Σ_{p,q} Ŝ_{pq} τ_p γ_q| ≤ ρ² (t₁ + L^d σ) (Σ_p w_p) Λ₁ Λ₂`, `Ŝ_{pq} = t₁ δ_{pq} + σ`. -/
private theorem GUEOneLoop_R_good {t1 σ ρ Λ₁ Λ₂ : ℝ} (ht1 : 0 ≤ t1) (hσ : 0 ≤ σ) (w : Zd d L → ℝ)
    (τ γ : Zd d L → ℂ) (hτ : ∀ p, ‖τ p‖ ≤ ρ * w p * Λ₁) (hγ : ∀ q, ‖γ q‖ ≤ ρ * Λ₂) :
    ‖∑ p, ∑ q, (((if p = q then t1 else 0) + σ : ℝ) : ℂ) * (τ p * γ q)‖ ≤
      ρ ^ 2 * (t1 + (L : ℝ) ^ d * σ) * (∑ p, w p) * (Λ₁ * Λ₂) := by
  have hc : ∀ p q : Zd d L, 0 ≤ (if p = q then t1 else 0) + σ := fun p q => by split_ifs <;> linarith
  have hpq : ∀ p q : Zd d L, ‖(((if p = q then t1 else 0) + σ : ℝ) : ℂ) * (τ p * γ q)‖ ≤
      ((if p = q then t1 else 0) + σ) * (ρ * w p * Λ₁ * (ρ * Λ₂)) := fun p q => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc p q), norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hτ p) (hγ q) (norm_nonneg _) ((norm_nonneg _).trans (hτ p))) (hc p q)
  have hrow : ∀ p : Zd d L, ∑ q : Zd d L, ((if p = q then t1 else 0) + σ) = t1 + (L : ℝ) ^ d * σ := fun p => by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]; simp [Zd, ZMod.card]
  calc _ ≤ ∑ p, ∑ q : Zd d L, ((if p = q then t1 else 0) + σ) * (ρ * w p * Λ₁ * (ρ * Λ₂)) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => hpq p q))
    _ = ∑ p, ρ ^ 2 * (t1 + (L : ℝ) ^ d * σ) * (Λ₁ * Λ₂) * w p :=
        Finset.sum_congr rfl fun p _ => by rw [← Finset.sum_mul, hrow]; ring
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem GUEOneLoop_cont_Phi {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true) (m : ℂ) (b : Zd d L) :
    Continuous (GUEOneLoop_Phi d L W H₀b z m b) :=
  ((continuous_matrixTrace d L W).comp (hGc.mul continuous_const)).sub continuous_const

private theorem GUEOneLoop_cont_Tt {H₀b : Matrix (Vtx d L W) (Vtx d L W) ℂ} {z : ℂ}
    (hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true)
    (Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ) (a p : Zd d L) :
    Continuous (GUEOneLoop_Tt d L W H₀b Mb z a p) :=
  continuous_const.mul ((continuous_matrixTrace d L W).comp
    (((hGc.mul continuous_const).mul continuous_const).mul continuous_const))

/-- **The core of the bound at one grid time** (twin of `OneLoop_expect_core`, `OneLoop:953`): given a measurable
exceptional set `T`, `μ.real T ≤ δ`, off which `|g_q - m| ≤ ρ Λ_u` and `|t_{ap} - Q_{ap}| ≤ ρ w_{ap} Λ_u` (row `ℓ¹` sums
of `w` at most `C_M`), the envelopes `E_Φ`, `E_τ` on the bad event with `δ L^d u E_τ E_Φ ≤ c_b`, and the stability
`hstab` of `1 - Q Ŝ` (constant `K_st`, target 2): `|𝔼 g_a - m| ≤ K_st (ρ² u C_M Λ_u² + c_b)`, `g_a = tr(G E_a)`.  `Q = Qd` is `M^{(+,+)}`,
`Mb` the block matrix of `M`; the profile is `Ŝ = t₁ 1 + σ J` (`S^{(B)}(0) = 1`, `EMn2BA_SB_zero`). -/
private theorem GUEOneLoop_expect_core (hL : 3 ≤ L) {t1 c0 σ u : ℝ} (ht1 : 0 ≤ t1) (hc0 : 0 ≤ c0)
    (hσ : σ = c0 * (W : ℝ) ^ d) (hu : t1 + (L : ℝ) ^ d * σ = u) (v : CoordF d L W → ℝ≥0)
    (hv : ∀ c : CoordF d L W, (v c : ℝ) =
      t1 * (gvarF d L W 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2))
    {H₀b Mb : Matrix (Vtx d L W) (Vtx d L W) ℂ} (hH : H₀b.IsHermitian) {z m : ℂ} (hz : z.im ≠ 0)
    (hM : (H₀b - (z + (u : ℂ) * m) • (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) * Mb = 1)
    (hm : ∀ a : Zd d L, Matrix.trace (Mb * Eblk d L W a) = m)
    (Qd : Zd d L → Zd d L → ℂ) (w : Zd d L → Zd d L → ℝ) (hw0 : ∀ a p, 0 ≤ w a p) {CM Kst : ℝ}
    (hCM : ∀ a, ∑ p, w a p ≤ CM)
    (hstab : ∀ (x y : Zd d L → ℂ) (B : ℝ), (∀ a, ‖y a‖ ≤ B) →
      (∀ a, x a = ∑ b, Qd a b * ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) + y a) → ∀ a, ‖x a‖ ≤ Kst * B)
    {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω') [IsProbabilityMeasure μ]
    (φ : Ω' → Ω d L W) (hφ : Measurable φ) (hmap : μ.map φ = GaussianProduct.law v)
    {Λu ρ EnvΦ Envτ δ cb : ℝ} (T : Set Ω') (hT : MeasurableSet T)
    (hEΦ : ∀ (b : Zd d L) (ω' : Ω d L W), ‖GUEOneLoop_Phi d L W H₀b z m b ω'‖ ≤ EnvΦ)
    (hEτ : ∀ (a p : Zd d L) (ω' : Ω d L W), ‖GUEOneLoop_Tt d L W H₀b Mb z a p ω' - Qd a p‖ ≤ Envτ)
    (hTδ : μ.real T ≤ δ) (hbad : δ * ((L : ℝ) ^ d * (u * (Envτ * EnvΦ))) ≤ cb)
    (hgΦ : ∀ ω ∉ T, ∀ b : Zd d L, ‖GUEOneLoop_Phi d L W H₀b z m b (φ ω)‖ ≤ ρ * Λu)
    (hgτ : ∀ ω ∉ T, ∀ a p : Zd d L, ‖GUEOneLoop_Tt d L W H₀b Mb z a p (φ ω) - Qd a p‖ ≤ ρ * w a p * Λu)
    (a : Zd d L) :
    ‖(∫ ω, Matrix.trace (Gres (H₀b + HflowBlock d L W 1 (φ ω)) z true * Eblk d L W a) ∂μ) - m‖ ≤
      Kst * (ρ ^ 2 * u * CM * Λu ^ 2 + cb) := by
  classical
  have hσ0 : 0 ≤ σ := by rw [hσ]; positivity
  have hu0 : 0 ≤ u := by rw [← hu]; positivity
  set Q := GaussianProduct.law v with hQ
  have hGc : Continuous fun ω : Ω d L W => Gres (H₀b + HflowBlock d L W 1 ω) z true := ExpAvgGen_G_cont hH 1 hz
  have hGn : ∀ ω : Ω d L W, ‖Gres (H₀b + HflowBlock d L W 1 ω) z true‖ ≤ |z.im|⁻¹ := ExpAvgGen_G_norm hH 1 hz
  -- integrability
  have hPhiI : ∀ b, Integrable (GUEOneLoop_Phi d L W H₀b z m b) Q := fun b =>
    ((GUEOneLoop_stein_int v _ hGc hGn 1 1).2.2.2.1 b).sub (integrable_const m)
  have hTI : ∀ a p, Integrable (GUEOneLoop_Tt d L W H₀b Mb z a p) Q := fun a p =>
    ((GUEOneLoop_stein_int v _ hGc hGn Mb (Eblk d L W a)).2.2.1 p).const_mul _
  have hTPhi : ∀ a p q, Integrable (fun ω' => GUEOneLoop_Tt d L W H₀b Mb z a p ω' * GUEOneLoop_Phi d L W H₀b z m q ω') Q := by
    intro a p q
    have h := (((GUEOneLoop_stein_int v _ hGc hGn Mb (Eblk d L W a)).2.2.2.2 p q).sub
      (((GUEOneLoop_stein_int v _ hGc hGn Mb (Eblk d L W a)).2.2.1 p).const_mul m)).const_mul ((W : ℂ) ^ d)
    refine h.congr (Filter.Eventually.of_forall fun ω' => ?_)
    simp only [Pi.sub_apply, GUEOneLoop_Tt, GUEOneLoop_Phi]
    ring
  have htPhi : ∀ a p q, Integrable (fun ω' => (GUEOneLoop_Tt d L W H₀b Mb z a p ω' - Qd a p) *
      GUEOneLoop_Phi d L W H₀b z m q ω') Q := by
    intro a p q
    refine ((hTPhi a p q).sub ((hPhiI q).const_mul (Qd a p))).congr (Filter.Eventually.of_forall fun ω' => ?_)
    simp only [Pi.sub_apply]
    ring
  -- transfer along `φ`
  have hint : ∀ {F : Ω d L W → ℂ}, Continuous F → ∫ ω, F (φ ω) ∂μ = ∫ ω', F ω' ∂Q := by
    intro F hF
    have h := integral_map hφ.aemeasurable (hF.aestronglyMeasurable (μ := μ.map φ))
    rw [hmap] at h
    exact h.symm
  have hSB : ∀ p q : Zd d L, SB d L 0 p q = if p = q then 1 else 0 := fun p q => by
    rw [EMn2BA_SB_zero]; simp [Matrix.one_apply]
  have hSh : ∀ p q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) = (((if p = q then t1 else 0) + σ : ℝ) : ℂ) := by
    intro p q
    rw [hSB p q]
    split_ifs <;> simp
  -- the first moments `x_b = 𝔼 (g_b - m)` and the block identity
  set x : Zd d L → ℂ := fun b => ∫ ω', GUEOneLoop_Phi d L W H₀b z m b ω' ∂Q with hx
  have hxe : ∀ a', x a' = (∫ ω' : Ω d L W, Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω') z true *
      Eblk d L W a') ∂(GaussianProduct.law v)) - m := by
    intro a'
    simp only [hx, GUEOneLoop_Phi]
    rw [integral_sub ((GUEOneLoop_stein_int v _ hGc hGn 1 1).2.2.2.1 a') (integrable_const _), integral_const]
    simp
  have hid : ∀ a', x a' = ∑ p, ∑ q, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
      ∫ ω', GUEOneLoop_Tt d L W H₀b Mb z a' p ω' * GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q := by
    intro a'
    rw [hxe a']
    exact GUEOneLoop_blockId hL hσ hu v hv hH hz hM hm a'
  have hrowx : ∀ p, ∑ q, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * x q = (t1 : ℂ) * x p + (σ : ℂ) * ∑ c, x c := by
    intro p
    simp only [hSB, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    simp
  set R : Zd d L → ℂ := fun a' => ∑ p, ∑ q, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
    ∫ ω', (GUEOneLoop_Tt d L W H₀b Mb z a' p ω' - Qd a' p) * GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q with hR
  have hxR : ∀ a', x a' = ∑ b, Qd a' b * ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) + R a' := by
    intro a'
    have hsplit : ∀ p q, ∫ ω', GUEOneLoop_Tt d L W H₀b Mb z a' p ω' * GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q =
        Qd a' p * x q + ∫ ω', (GUEOneLoop_Tt d L W H₀b Mb z a' p ω' - Qd a' p) *
          GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q := by
      intro p q
      have e1 : ∀ ω', GUEOneLoop_Tt d L W H₀b Mb z a' p ω' * GUEOneLoop_Phi d L W H₀b z m q ω' =
          Qd a' p * GUEOneLoop_Phi d L W H₀b z m q ω' + (GUEOneLoop_Tt d L W H₀b Mb z a' p ω' - Qd a' p) *
            GUEOneLoop_Phi d L W H₀b z m q ω' := fun ω' => by ring
      simp only [e1]
      rw [integral_add ((hPhiI q).const_mul _) (htPhi a' p q), integral_const_mul]
    have e1 : ∀ p q : Zd d L, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) *
        ∫ ω', GUEOneLoop_Tt d L W H₀b Mb z a' p ω' * GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q =
        ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * (Qd a' p * x q) +
          ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * ∫ ω', (GUEOneLoop_Tt d L W H₀b Mb z a' p ω' - Qd a' p) *
            GUEOneLoop_Phi d L W H₀b z m q ω' ∂Q := fun p q => by rw [hsplit p q]; ring
    have h1 : ∑ p, ∑ q, ((t1 : ℂ) * SB d L 0 p q + (σ : ℂ)) * (Qd a' p * x q) =
        ∑ b, Qd a' b * ((t1 : ℂ) * x b + (σ : ℂ) * ∑ c, x c) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← hrowx p, Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hid a']
    simp only [e1, Finset.sum_add_distrib]
    rw [h1]
  -- the bound on the remainder
  have hRbound : ∀ a', ‖R a'‖ ≤ ρ ^ 2 * u * CM * Λu ^ 2 + cb := by
    intro a'
    set F : Ω d L W → ℂ := fun ω' => ∑ p, ∑ q, (((if p = q then t1 else 0) + σ : ℝ) : ℂ) *
      ((GUEOneLoop_Tt d L W H₀b Mb z a' p ω' - Qd a' p) * GUEOneLoop_Phi d L W H₀b z m q ω') with hF
    have hFc : Continuous F := by
      refine continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => continuous_const.mul ?_
      exact ((GUEOneLoop_cont_Tt hGc Mb a' p).sub continuous_const).mul (GUEOneLoop_cont_Phi hGc m q)
    have hRF : R a' = ∫ ω', F ω' ∂Q := by
      simp only [hR, hF, hSh]
      rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (htPhi a' p q).const_mul _))]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_finsetSum _ (fun q _ => (htPhi a' p q).const_mul _)]
      exact Finset.sum_congr rfl fun q _ => by rw [integral_const_mul]
    have hEτ0 : 0 ≤ Envτ := (norm_nonneg _).trans (hEτ a' a' 0)
    have hEΦ0 : 0 ≤ EnvΦ := (norm_nonneg _).trans (hEΦ a' 0)
    have hbadnn : 0 ≤ (L : ℝ) ^ d * (u * (Envτ * EnvΦ)) := by positivity
    have hglob : ∀ ω : Ω' , ‖F (φ ω)‖ ≤ (L : ℝ) ^ d * (u * (Envτ * EnvΦ)) := by
      intro ω
      have h := GUEOneLoop_R_good (L := L) ht1 hσ0 (fun _ => (1 : ℝ))
        (fun p => GUEOneLoop_Tt d L W H₀b Mb z a' p (φ ω) - Qd a' p)
        (fun q => GUEOneLoop_Phi d L W H₀b z m q (φ ω)) (ρ := 1) (Λ₁ := Envτ) (Λ₂ := EnvΦ)
        (fun p => by simpa using hEτ a' p (φ ω)) (fun q => by simpa using hEΦ q (φ ω))
      refine h.trans (le_of_eq ?_)
      have hc : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by rw [OneLoop_card_Zd d L]; push_cast; ring
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_pow, hc, hu]
      ring
    have hpt : ∀ ω : Ω', ‖F (φ ω)‖ ≤ ρ ^ 2 * u * CM * Λu ^ 2 +
        T.indicator (fun _ => (L : ℝ) ^ d * (u * (Envτ * EnvΦ))) ω := by
      intro ω
      by_cases hω : ω ∈ T
      · rw [Set.indicator_of_mem hω]
        have := hglob ω
        have hCM0 : 0 ≤ CM := (Finset.sum_nonneg fun p _ => hw0 a' p).trans (hCM a')
        have hpos : 0 ≤ ρ ^ 2 * u * CM * Λu ^ 2 := by positivity
        linarith
      · rw [Set.indicator_of_notMem hω, add_zero]
        have h := GUEOneLoop_R_good (L := L) ht1 hσ0 (w a')
          (fun p => GUEOneLoop_Tt d L W H₀b Mb z a' p (φ ω) - Qd a' p)
          (fun q => GUEOneLoop_Phi d L W H₀b z m q (φ ω)) (ρ := ρ) (Λ₁ := Λu) (Λ₂ := Λu)
          (fun p => hgτ ω hω a' p) (fun q => hgΦ ω hω q)
        refine h.trans ?_
        rw [hu]
        have h2 : ρ ^ 2 * u * (∑ p, w a' p) * (Λu * Λu) ≤ ρ ^ 2 * u * CM * (Λu * Λu) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hCM a') (by positivity)) (mul_self_nonneg _)
        calc _ ≤ _ := h2
          _ = _ := by ring
    have hFm : Measurable fun ω : Ω' => F (φ ω) := hFc.measurable.comp hφ
    have hint1 : Integrable (fun ω : Ω' => ‖F (φ ω)‖) μ := by
      refine Integrable.of_bound (C := (L : ℝ) ^ d * (u * (Envτ * EnvΦ))) hFm.norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [norm_norm]
      exact hglob ω
    have hint2 : Integrable (fun ω : Ω' => ρ ^ 2 * u * CM * Λu ^ 2 +
        T.indicator (fun _ => (L : ℝ) ^ d * (u * (Envτ * EnvΦ))) ω) μ :=
      (integrable_const _).add ((integrable_const _).indicator hT)
    rw [hRF, ← hint hFc]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine (integral_mono hint1 hint2 hpt).trans ?_
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hT), integral_const,
      integral_indicator_const _ hT]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    have : μ.real T * ((L : ℝ) ^ d * (u * (Envτ * EnvΦ))) ≤ cb :=
      (mul_le_mul_of_nonneg_right hTδ hbadnn).trans hbad
    linarith
  have hxbound := hstab x R (ρ ^ 2 * u * CM * Λu ^ 2 + cb) hRbound hxR a
  have hxa : (∫ ω, Matrix.trace (Gres (H₀b + HflowBlock d L W 1 (φ ω)) z true * Eblk d L W a) ∂μ) - m = x a := by
    have hcont : Continuous fun ω' : Ω d L W =>
        Matrix.trace (Gres (H₀b + HflowBlock d L W 1 ω') z true * Eblk d L W a) :=
      (continuous_matrixTrace d L W).comp (hGc.mul continuous_const)
    have h := hint hcont
    beta_reduce at h
    rw [h, hxe a]
  rw [hxa]
  exact hxbound

end Core

/-! ## 5. The bound at one grid time and Lemma 5.15 on the GUE-phase grid at BA (target 4) -/

section Wrapper

open scoped Matrix.Norms.L2Operator

/-- `blockMat (g Ψ_I)` is Hermitian (`PsiI_isHermitian`, `g` real). -/
private theorem GUEOneLoop_H0_herm (d L W : ℕ) [NeZero L] [NeZero W] (g : ℝ) :
    (blockMat d L W (((g : ℝ) : ℂ) • PsiI d L W)).IsHermitian := by
  have h : (((g : ℝ) : ℂ) • PsiI d L W).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star ((g : ℝ) : ℂ) = ((g : ℝ) : ℂ) from Complex.conj_ofReal _]
  exact h.submatrix _

/-- **The block data of `M = (g Ψ_I - E - m)⁻¹`** at real-axis data `BAReal`: `(H₀ - (z + u m)) M = 1` for
`z + u m = E + m` (`z = z_u = E + (1-u) m`), and the block average `tr(M E_a) = m` (`M_{xx} = M^{(B)}_{[x][x]} = m`,
`BAMres_fine_apply`, `BAMB_diag_eq`). -/
private theorem GUEOneLoop_Mdata {d L W : ℕ} [NeZero L] [NeZero W] {g E κ : ℝ} {m : ℂ} (hκ : 0 < κ)
    (hr : BAReal d L g κ E m) {u : ℝ} {z : ℂ} (hzm : z + (u : ℂ) * m = (E : ℂ) + m) :
    (blockMat d L W (((g : ℝ) : ℂ) • PsiI d L W) - (z + (u : ℂ) * m) •
        (1 : Matrix (Vtx d L W) (Vtx d L W) ℂ)) *
      blockMat d L W (Mres (((g : ℝ) : ℂ) • PsiI d L W) (E : ℂ) m) = 1 ∧
    ∀ a : Zd d L, Matrix.trace (blockMat d L W (Mres (((g : ℝ) : ℂ) • PsiI d L W) (E : ℂ) m) *
      Eblk d L W a) = m := by
  have hEm : ((E : ℂ) + m).im ≠ 0 := by
    have : ((E : ℂ) + m).im = m.im := by simp
    rw [this]
    exact (lt_of_lt_of_le hκ hr.2).ne'
  have hHg : (((g : ℝ) : ℂ) • PsiI d L W).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_smul, (PsiI_isHermitian d _ _).eq,
      show star ((g : ℝ) : ℂ) = ((g : ℝ) : ℂ) from Complex.conj_ofReal _]
  refine ⟨?_, fun a => ?_⟩
  · rw [hzm, ExpAvgGen_blockMat_sub_smul, ← ExpAvgGen_blockMat_mul]
    have h1 : (((g : ℝ) : ℂ) • PsiI d L W - ((E : ℂ) + m) • (1 : Matrix (Idx d L W) (Idx d L W) ℂ)) *
        Mres (((g : ℝ) : ℂ) • PsiI d L W) (E : ℂ) m = 1 :=
      Ring.mul_inverse_cancel _ (isUnit_sub_smul_of_isHermitian hHg hEm)
    rw [h1, ExpAvgGen_blockMat_one]
  · rw [ExpAvgGen_trace_Eblk]
    have hdiag : ∀ x : Idx d L W, Mres (((g : ℝ) : ℂ) • PsiI d L W) (E : ℂ) m x x = m := by
      intro x
      rw [BAMres_fine_apply d L W g (E : ℂ) m hEm x x]
      simp only [↓reduceIte]
      exact BAMB_diag_eq d L g (E : ℂ) m hr.1 _
    simp only [hdiag, Finset.sum_const, card_Iblk, nsmul_eq_mul]
    have hWd : ((W : ℂ)) ^ d ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne _))
    push_cast
    field_simp

/-- **The bound at one grid time** (twin of `OneLoop_expect_bound`, `OneLoop:1125`): for sets `B1`, `B2` of
probability `≤ N^{-7}` each, off `B1` the diagonal 1-loops are `≤ ρ Λ_u` (`h1`), off `B2` the `M`-weighted block
traces are within `ρ |M^{(B)}_{aq}| Λ_u` of `M^{(+,+)}_{aq}` (`hoff`), `Λ_u = (N η_u)⁻¹`; with the stability
constant `K_st` of target 2: `|𝔼 g_a - m| ≤ K_st (ρ² C_M + 8 κ⁻¹) Λ_u²`, `C_M = c₀⁻¹ S_{c₀}` (`baM_row_l1`).
(`D = 7`: the envelopes of `g_q - m` and of `t_{ap} - M^{(+,+)}_{ap}` are `L^d η⁻¹`, `L^d κ⁻¹ η⁻¹`, `‖M‖ ≤ κ⁻¹`.) -/
private theorem GUEOneLoop_expect_bound {d : ℕ} (sz : Sizes d) (hd : 3 ≤ d) {Λ κ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ)
    (n : ℕ) {g E t1 t0 : ℕ → ℝ} {m : ℕ → ℂ} (hg : 0 < g n ∧ g n ≤ Λ)
    (hr : BAReal d (sz.L n) (g n) κ (E n) (m n)) (ht1 : 0 ≤ t1 n) (ht10 : t1 n ≤ t0 n) (ht0 : t0 n < 1)
    (K : ℕ → ℕ) (hK : K n ≠ 0) (k : ℕ) (hkK : k ≤ K n) {Kst : ℝ} (hKst0 : 0 ≤ Kst)
    (hstab : ∀ t1' σ' : ℝ, 0 ≤ t1' → 0 ≤ σ' → t1' + ((sz.L n : ℕ) : ℝ) ^ d * σ' ≤ 1 →
      ∀ (x y : Zd d (sz.L n) → ℂ) (B : ℝ), (∀ a, ‖y a‖ ≤ B) →
        (∀ a, x a = ∑ b, BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a b *
          ((t1' : ℂ) * x b + (σ' : ℂ) * ∑ c, x c) + y a) → ∀ a, ‖x a‖ ≤ Kst * B)
    {ρ : ℝ} (B1 B2 : Set (PathΩ (sz.withLam 0)))
    (hPB1 : Pgue (sz.withLam 0) B1 ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(7 : ℝ))))
    (hPB2 : Pgue (sz.withLam 0) B2 ≤ ENNReal.ofReal (((sz.size n : ℕ) : ℝ) ^ (-(7 : ℝ))))
    (hgood1 : ∀ ω ∉ B1, ∀ b : Zd d (sz.L n),
      ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k)) ⟨[true], [b]⟩ - m n‖ ≤
        ρ * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹)
    (hgood2 : ∀ ω ∉ B2, ∀ a q : Zd d (sz.L n),
      ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) q,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (gueHBA sz g t1 t0 K n k ω) (ztOf (m n) (E n) (gridTime t1 t0 K n k)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a q‖ ≤
        ρ * (‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a q‖ *
          (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹))
    (a : Zd d (sz.L n)) :
    ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
          (ztOf (m n) (E n) (gridTime t1 t0 K n k)) ⟨[true], [a]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤
      Kst * ((ρ ^ 2 * ((BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ)) + 8 * κ⁻¹) *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ 2) := by
  classical
  have hL3 := sz.three_le_L n
  have hW0 := sz.W_pos n
  have hLpos : (0 : ℝ) < sz.L n := by exact_mod_cast (show 0 < sz.L n by omega)
  have hWpos : (0 : ℝ) < sz.W n := by exact_mod_cast hW0
  have hNeq : ((sz.size n : ℕ) : ℝ) = (sz.W n : ℝ) ^ d * (sz.L n : ℝ) ^ d := by
    unfold Sizes.size; push_cast; ring
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by rw [hNeq]; positivity
  have hN1 : 1 ≤ N := by
    have h1 : 1 ≤ sz.size n := sz.one_le_size n
    rw [hNdef]
    exact_mod_cast h1
  -- the grid time
  set Δ := gridStep t1 t0 K n with hΔdef
  set u := gridTime t1 t0 K n k with hudef
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast Nat.pos_of_ne_zero hK
  have hΔ0 : 0 ≤ Δ := div_nonneg (by linarith) hKpos.le
  have hkK' : (k : ℝ) ≤ K n := by exact_mod_cast hkK
  have hkΔ : (k : ℝ) * Δ ≤ t0 n - t1 n := by
    calc (k : ℝ) * Δ ≤ K n * Δ := mul_le_mul_of_nonneg_right hkK' hΔ0
      _ = t0 n - t1 n := by rw [hΔdef, gridStep]; field_simp
  have hu_eq : u = t1 n + (k : ℝ) * Δ := rfl
  have hkΔ0 : 0 ≤ (k : ℝ) * Δ := mul_nonneg (Nat.cast_nonneg _) hΔ0
  have hu0 : 0 ≤ u := by rw [hu_eq]; linarith
  have hu1 : u < 1 := by rw [hu_eq]; linarith
  -- the flow data
  have hmim : κ ≤ (m n).im := hr.2
  have hm1 : ‖m n‖ ≤ 1 := BAm_norm_le_one d (sz.L n) (g n) (E n : ℂ) (m n) (by simp) hr.1
  have him1 : (m n).im ≤ 1 := ((le_abs_self _).trans (Complex.abs_im_le_norm (m n))).trans hm1
  have hκ1 : κ ≤ 1 := hmim.trans him1
  set η := etaOf (m n) u with hηdef
  have hηpos : 0 < η := by
    rw [hηdef, etaOf]
    exact mul_pos (by linarith) (by linarith)
  have hηle : η ≤ 1 := by
    rw [hηdef, etaOf]
    calc (1 - u) * (m n).im ≤ 1 * 1 :=
          mul_le_mul (by linarith) him1 (by linarith) zero_le_one
      _ = 1 := one_mul 1
  set Λu := (N * η)⁻¹ with hΛdef
  have hΛ0 : 0 ≤ Λu := by positivity
  have hηinv : η⁻¹ = N * Λu := by rw [hΛdef]; field_simp
  have hη1 : 1 ≤ η⁻¹ := by rw [le_inv_comm₀ one_pos hηpos, inv_one]; exact hηle
  -- the one-time law of step `k`
  set aa := Real.sqrt (t1 n) with haa
  set bb := Real.sqrt (Δ / N) with hbb
  have haa2 : aa ^ 2 = t1 n := Real.sq_sqrt ht1
  have hbb2 : bb ^ 2 = Δ / N := Real.sq_sqrt (div_nonneg hΔ0 hNpos.le)
  set c0 : ℝ := (k : ℝ) * bb ^ 2 with hc0
  have hc00 : 0 ≤ c0 := by rw [hc0]; positivity
  set σ : ℝ := c0 * (sz.W n : ℝ) ^ d with hσdef
  have hσ0 : 0 ≤ σ := by rw [hσdef]; positivity
  have hsum : t1 n + (sz.L n : ℝ) ^ d * σ = u := by
    rw [hσdef, hc0, hbb2, hu_eq, hNeq]
    field_simp
  set X : ℝ := (sz.L n : ℝ) ^ d with hXdef
  have hX1 : 1 ≤ X := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ sz.L n))
  have hXN : X ≤ N := by
    rw [hNeq]
    have hW2 : (1 : ℝ) ≤ (sz.W n : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW0)
    calc X = 1 * X := (one_mul X).symm
      _ ≤ (sz.W n : ℝ) ^ d * X := mul_le_mul_of_nonneg_right hW2 (by linarith)
  have hv : ∀ c : CoordF d (sz.L n) (sz.W n), (olVar (sz.withLam 0) aa bb k ⟨n, c⟩ : ℝ) =
      t1 n * (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) + c0 * (if c.1 = c.2.1 then 1 else 1 / 2) := by
    intro c
    have hg' : ((Sizes.seqGvar (sz.withLam 0) ⟨n, c⟩ : ℝ≥0) : ℝ) = (gvarF d (sz.L n) (sz.W n) 0 c : ℝ) := rfl
    simp only [olVar, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk, nsmul_eq_mul, hg', haa2]
    by_cases hc : c.1 = c.2.1
    · have hc' : (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.1 = (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.2.1 := hc
      simp only [gueUnitVar, eq_true hc', eq_true hc, hc0, ↓reduceIte, NNReal.coe_one]
      push_cast
      ring
    · have hc' : ¬ ((⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.1 =
          (⟨n, c⟩ : Sizes.SeqCoord (sz.withLam 0)).2.2.1) := hc
      simp only [gueUnitVar, eq_false hc', eq_false hc, hc0, ↓reduceIte]
      push_cast
      ring
  set φ : PathΩ (sz.withLam 0) → Ω d (sz.L n) (sz.W n) :=
    fun ω => Sizes.slice (sz.withLam 0) n (olComb (sz.withLam 0) aa bb k ω) with hφdef
  have hmap : (Pgue (sz.withLam 0)).map φ =
      GaussianProduct.law (fun c : CoordF d (sz.L n) (sz.W n) => olVar (sz.withLam 0) aa bb k ⟨n, c⟩) :=
    ol_map_comb_slice (sz.withLam 0) aa bb k n
  have hφ : Measurable φ := (Sizes.measurable_slice (sz.withLam 0) n).comp (olComb_measurable (sz.withLam 0) aa bb k)
  -- the BA data on the block-product index
  set H₀b : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
    blockMat d (sz.L n) (sz.W n) (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) with hH₀b
  have hH₀bh : H₀b.IsHermitian := GUEOneLoop_H0_herm d (sz.L n) (sz.W n) (g n)
  set Mb : Matrix (Vtx d (sz.L n) (sz.W n)) (Vtx d (sz.L n) (sz.W n)) ℂ :=
    blockMat d (sz.L n) (sz.W n) (Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) with hMb
  set z : ℂ := ztOf (m n) (E n) u with hzdef
  have hzim : z.im = η := ztOf_im (m n) (E n) u
  have hz : z.im ≠ 0 := by rw [hzim]; exact hηpos.ne'
  have hEm : ((E n : ℂ) + m n).im ≠ 0 := by
    have : ((E n : ℂ) + m n).im = (m n).im := by simp
    rw [this]
    exact (lt_of_lt_of_le hκ hmim).ne'
  have hblock : ∀ ω, blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω) =
      H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω) := by
    intro ω
    rw [ol_gueHBA_eq, hH₀b, ← OneLoop_blockMat_Xmat]
    rfl
  obtain ⟨hMM, hmm⟩ := GUEOneLoop_Mdata (L := sz.L n) (W := sz.W n) (u := u) (z := z) hκ hr
    (by simp only [hzdef, ztOf]; ring)
  -- the envelopes
  have hηabs : |z.im| = η := by rw [hzim]; exact abs_of_pos hηpos
  have hGn : ∀ ω' : Ω d (sz.L n) (sz.W n),
      ‖Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true‖ ≤ η⁻¹ := by
    intro ω'
    have := ExpAvgGen_G_norm hH₀bh 1 hz ω'
    rwa [hηabs] at this
  have hE_b : ∀ (b : Zd d (sz.L n)) (ω' : Ω d (sz.L n) (sz.W n)),
      ‖Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true * Eblk d (sz.L n) (sz.W n) b)‖ ≤
        X * η⁻¹ := by
    intro b ω'
    refine (ExpAvgGen_trG_bdd _ _ (hGn ω')).trans ?_
    have h2 := norm_Eblk_le_inv_W_sq d (sz.L n) (sz.W n) b
    calc (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) * (η⁻¹ * ‖Eblk d (sz.L n) (sz.W n) b‖) ≤
          (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) * (η⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹) := by gcongr
      _ = X * η⁻¹ := by
        have hWd : ((sz.W n : ℝ)) ^ d ≠ 0 := (pow_pos hWpos d).ne'
        rw [hXdef]
        push_cast
        rw [mul_pow]
        field_simp
  have hEΦ : ∀ (b : Zd d (sz.L n)) (ω' : Ω d (sz.L n) (sz.W n)),
      ‖GUEOneLoop_Phi d (sz.L n) (sz.W n) H₀b z (m n) b ω'‖ ≤ 2 * (X * η⁻¹) := by
    intro b ω'
    unfold GUEOneLoop_Phi
    calc _ ≤ ‖Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true *
          Eblk d (sz.L n) (sz.W n) b)‖ + ‖m n‖ := norm_sub_le _ _
      _ ≤ X * η⁻¹ + 1 := add_le_add (hE_b b ω') hm1
      _ ≤ 2 * (X * η⁻¹) := by linarith [one_le_mul_of_one_le_of_one_le hX1 hη1]
  have hMbn : ‖Mb‖ ≤ κ⁻¹ := by
    have h1 : Mb = Gres H₀b ((E n : ℂ) + m n) true := by
      rw [hMb, hH₀b, ExpAvgGen_Gres_blockMat]
      rfl
    rw [h1]
    refine (norm_Gsig_le_inv_eta hH₀bh (abs_pos.mpr hEm) le_rfl true).trans ?_
    have : |((E n : ℂ) + m n).im| = (m n).im := by
      have : ((E n : ℂ) + m n).im = (m n).im := by simp
      rw [this]
      exact abs_of_pos (lt_of_lt_of_le hκ hmim)
    rw [this]
    exact inv_anti₀ hκ hmim
  have hQn : ∀ a p : Zd d (sz.L n),
      ‖BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a p‖ ≤ 1 := by
    intro a p
    rw [BAMss_ss_norm d (sz.L n) (g n) (E n : ℂ) (m n) true a p]
    have hrow := BAMB_row_sq_real d (sz.L n) (g n) (E n) (m n) hr.1 a
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a b‖ ^ 2)
      (fun b _ => by positivity) (Finset.mem_univ p)
  have hEτ : ∀ (a p : Zd d (sz.L n)) (ω' : Ω d (sz.L n) (sz.W n)),
      ‖GUEOneLoop_Tt d (sz.L n) (sz.W n) H₀b Mb z a p ω' -
        BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a p‖ ≤ 2 * (X * η⁻¹ * κ⁻¹) := by
    intro a p ω'
    have hWd : ((sz.W n : ℝ)) ^ d ≠ 0 := (pow_pos hWpos d).ne'
    have hnorm : ‖Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true *
        Eblk d (sz.L n) (sz.W n) a * Mb * Eblk d (sz.L n) (sz.W n) p)‖ ≤
        (((sz.L n * sz.W n) ^ d : ℕ) : ℝ) * ((η⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹) * κ⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹) := by
      refine (ExpAvgGen_trace3_le _ _ _ hMbn).trans ?_
      have ha := norm_Eblk_le_inv_W_sq d (sz.L n) (sz.W n) a
      have hp := norm_Eblk_le_inv_W_sq d (sz.L n) (sz.W n) p
      have hA : ‖Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true * Eblk d (sz.L n) (sz.W n) a‖ ≤
          η⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹ :=
        (norm_mul_le _ _).trans (mul_le_mul (hGn ω') ha (norm_nonneg _) (by positivity))
      gcongr
    have hT : ‖GUEOneLoop_Tt d (sz.L n) (sz.W n) H₀b Mb z a p ω'‖ ≤ X * η⁻¹ * κ⁻¹ := by
      unfold GUEOneLoop_Tt
      rw [norm_mul]
      have hWn : ‖((sz.W n : ℂ)) ^ d‖ = ((sz.W n : ℝ)) ^ d := by simp
      rw [hWn]
      calc ((sz.W n : ℝ)) ^ d * ‖Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 ω') z true *
            Eblk d (sz.L n) (sz.W n) a * Mb * Eblk d (sz.L n) (sz.W n) p)‖ ≤
          ((sz.W n : ℝ)) ^ d * ((((sz.L n * sz.W n) ^ d : ℕ) : ℝ) *
            ((η⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹) * κ⁻¹ * (((sz.W n : ℝ)) ^ d)⁻¹)) := by gcongr
        _ = X * η⁻¹ * κ⁻¹ := by
          rw [hXdef]
          push_cast
          rw [mul_pow]
          field_simp
    have hk1 : 1 ≤ κ⁻¹ := (one_le_inv₀ hκ).mpr hκ1
    calc _ ≤ ‖GUEOneLoop_Tt d (sz.L n) (sz.W n) H₀b Mb z a p ω'‖ +
          ‖BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a p‖ := norm_sub_le _ _
      _ ≤ X * η⁻¹ * κ⁻¹ + 1 := add_le_add hT (hQn a p)
      _ ≤ 2 * (X * η⁻¹ * κ⁻¹) := by
        linarith [one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX1 hη1) hk1]
  -- the bad event
  have hPB : Pgue (sz.withLam 0) (B1 ∪ B2) ≤ ENNReal.ofReal (2 * N ^ (-(7 : ℝ))) := by
    refine (measure_union_le _ _).trans ?_
    have h0 : 0 ≤ N ^ (-(7 : ℝ)) := by positivity
    calc _ ≤ ENNReal.ofReal (N ^ (-(7 : ℝ))) + ENNReal.ofReal (N ^ (-(7 : ℝ))) := add_le_add hPB1 hPB2
      _ = ENNReal.ofReal (2 * N ^ (-(7 : ℝ))) := by
        rw [← ENNReal.ofReal_add h0 h0]
        congr 1
        ring
  set T := toMeasurable (Pgue (sz.withLam 0)) (B1 ∪ B2) with hT
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hBT : B1 ∪ B2 ⊆ T := subset_toMeasurable _ _
  have hTδ : (Pgue (sz.withLam 0)).real T ≤ 2 * N ^ (-(7 : ℝ)) := by
    rw [measureReal_def, hT, measure_toMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hPB
  have hbad : 2 * N ^ (-(7 : ℝ)) * (X * (u * ((2 * (X * η⁻¹ * κ⁻¹)) * (2 * (X * η⁻¹))))) ≤
      8 * κ⁻¹ * Λu ^ 2 := by
    have h7 : N ^ (-(7 : ℝ)) = (N ^ 7)⁻¹ := by rw [Real.rpow_neg hNpos.le]; norm_cast
    rw [h7, hηinv]
    have hκ0 : 0 < κ⁻¹ := inv_pos.mpr hκ
    have key : u * X ^ 3 * N ^ 2 ≤ N ^ 7 := by
      calc u * X ^ 3 * N ^ 2 ≤ 1 * N ^ 3 * N ^ 2 := by
            gcongr
        _ = N ^ 5 := by ring
        _ ≤ N ^ 7 := pow_le_pow_right₀ hN1 (by norm_num)
    calc 2 * (N ^ 7)⁻¹ * (X * (u * ((2 * (X * (N * Λu) * κ⁻¹)) * (2 * (X * (N * Λu)))))) =
          8 * κ⁻¹ * Λu ^ 2 * ((u * X ^ 3 * N ^ 2) / N ^ 7) := by
          field_simp
          ring
      _ ≤ 8 * κ⁻¹ * Λu ^ 2 * 1 := by
          gcongr
          exact (div_le_one (by positivity)).mpr key
      _ = _ := mul_one _
  have hgΦ : ∀ ω ∉ T, ∀ b : Zd d (sz.L n),
      ‖GUEOneLoop_Phi d (sz.L n) (sz.W n) H₀b z (m n) b (φ ω)‖ ≤ ρ * Λu := by
    intro ω hω b
    have h := hgood1 ω (fun h => hω (hBT (Or.inl h))) b
    rw [hblock ω, OneLoop_gloop_one] at h
    exact h
  have hgτ : ∀ ω ∉ T, ∀ a p : Zd d (sz.L n),
      ‖GUEOneLoop_Tt d (sz.L n) (sz.W n) H₀b Mb z a p (φ ω) -
        BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a p‖ ≤
        ρ * ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a p‖ * Λu := by
    intro ω hω a p
    have h := hgood2 ω (fun h => hω (hBT (Or.inr h))) a p
    have e : GUEOneLoop_Tt d (sz.L n) (sz.W n) H₀b Mb z a p (φ ω) =
        (((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) a, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p,
          Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
            Gres (gueHBA sz g t1 t0 K n k ω) z true y x := by
      unfold GUEOneLoop_Tt
      rw [← hblock ω, ExpAvgGen_Gres_blockMat]
      exact ExpAvgGen_trace_four (Gres (gueHBA sz g t1 t0 K n k ω) z true)
        (Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n)) a p
    rw [e, mul_assoc]
    exact h
  have hCM : ∀ a : Zd d (sz.L n), ∑ p, ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a p‖ ≤
      (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) :=
    fun a => baM_row_l1 (by omega) hL3 Λ (g n) κ (E n) (m n) hΛ hg.1 hg.2 hκ hr a
  have hstab' := hstab (t1 n) σ ht1 hσ0 (by linarith [hsum, hu1])
  have hcore := GUEOneLoop_expect_core (L := sz.L n) (W := sz.W n) hL3 ht1 hc00 hσdef hsum
    (fun c => olVar (sz.withLam 0) aa bb k ⟨n, c⟩) hv hH₀bh hz hMM hmm
    (fun a p => BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true a p)
    (fun a p => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) a p‖) (fun a p => norm_nonneg _) hCM hstab'
    (Pgue (sz.withLam 0)) φ hφ hmap T hTm hEΦ hEτ hTδ hbad hgΦ hgτ a
  have hfun : (fun ω => loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n) (gueHBA sz g t1 t0 K n k ω))
      z ⟨[true], [a]⟩) = fun ω => Matrix.trace (Gres (H₀b + HflowBlock d (sz.L n) (sz.W n) 1 (φ ω)) z true *
        Eblk d (sz.L n) (sz.W n) a) := funext fun ω => by rw [hblock ω, OneLoop_gloop_one]
  rw [hfun]
  refine hcore.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hKst0
  have hCM0 : 0 ≤ (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) :=
    (Finset.sum_nonneg fun p _ => norm_nonneg _).trans (hCM a)
  linarith [mul_nonneg (sub_nonneg.2 hu1.le) (mul_nonneg (mul_nonneg (sq_nonneg ρ) hCM0) (sq_nonneg Λu))]

end Wrapper

/-- **`gueGrid_expect_oneLoopBA'`** (T2519 Amend 4 item 2): `gueGrid_expect_oneLoopBA` with the coupling window `0 < g n ≤ Λ`
eventually (`hr` stays at every `n`); the proof of `gueGrid_expect_oneLoopBA` moved here, the window is one more entry of the
`filter_upwards` and `CM ≥ 0` is by positivity. -/
theorem gueGrid_expect_oneLoopBA' (d : ℕ) :
  3 ≤ d → ∀ (sz : Sizes d) (κ Λ : ℝ), 0 < κ → 0 < Λ →
    ∀ (g E t1 t0 : ℕ → ℝ) (m : ℕ → ℂ) (K : ℕ → ℕ),
    Tendsto (fun n => sz.size n) atTop atTop →
    (∀ᶠ n in atTop, 0 < g n ∧ g n ≤ Λ) → (∀ n, BAReal d (sz.L n) (g n) κ (E n) (m n)) →
    (∀ n, 0 ≤ t1 n) → (∀ n, t1 n ≤ t0 n) → (∀ n, t0 n < 1) → (∀ n, K n ≠ 0) →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (K n + 1) × Zd d (sz.L n)) ω =>
        ‖loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
            (gueHBA sz g t1 t0 K n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ - m n‖)
      (fun n p _ => (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) →
    StochDomAt (Pgue (sz.withLam 0)) sz.size
      (fun n (p : Fin (K n + 1) × Zd d (sz.L n) × Zd d (sz.L n)) ω =>
        ‖(((sz.W n : ℕ) : ℂ) ^ d)⁻¹ * ∑ x ∈ Iblk d (sz.L n) (sz.W n) p.2.1, ∑ y ∈ Iblk d (sz.L n) (sz.W n) p.2.2,
            Mres (((g n : ℝ) : ℂ) • PsiI d (sz.L n) (sz.W n)) (E n : ℂ) (m n) x y *
              Gres (gueHBA sz g t1 t0 K n p.1 ω)
                (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) true y x -
          BAMss d (sz.L n) (BAMB d (sz.L n) (g n) (E n : ℂ) (m n)) true true p.2.1 p.2.2‖)
      (fun n p _ => ‖BAMB d (sz.L n) (g n) (E n : ℂ) (m n) p.2.1 p.2.2‖ *
        (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹) →
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ p : Fin (K n + 1) × Zd d (sz.L n),
      ‖(∫ ω, loopL d (sz.L n) (sz.W n) (blockMat d (sz.L n) (sz.W n)
            (gueHBA sz g t1 t0 K n p.1 ω))
            (ztOf (m n) (E n) (gridTime t1 t0 K n p.1)) ⟨[true], [p.2]⟩ ∂(Pgue (sz.withLam 0))) - m n‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ ε * (((sz.size n : ℕ) : ℝ) * etaOf (m n) (gridTime t1 t0 K n p.1))⁻¹ ^ 2
    := by
  intro hd sz κ Λ hκ hΛ g E t1 t0 m K hsize hg hr ht1 ht10 ht0 hK h1 hoff ε hε
  obtain ⟨Kst, hKst0, hKst⟩ := baOneLoop_stable κ hκ
  set CM : ℝ := (BAct_rate d Λ κ)⁻¹ * expC (d - 2) (BAct_rate d Λ κ) with hCMdef
  have hCM0 : 0 ≤ CM := by
    have hc := BAct_rate_pos d Λ κ (by omega) hΛ hκ
    rw [hCMdef]; unfold expC; positivity
  have hsz : Tendsto (fun n => ((sz.size n : ℕ) : ℝ)) atTop atTop := tendsto_natCast_atTop_iff.mpr hsize
  have hb1 := h1 (ε / 4) (by positivity) 7 (by norm_num)
  have hb2 := hoff (ε / 4) (by positivity) 7 (by norm_num)
  set C0 : ℝ := Kst * (CM + 8 * κ⁻¹) with hC0
  have hC00 : 0 ≤ C0 := mul_nonneg hKst0.le (add_nonneg hCM0 (by positivity))
  have habs : ∀ᶠ n : ℕ in atTop, C0 + 1 ≤ ((sz.size n : ℕ) : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (half_pos hε)).comp hsz).eventually (eventually_ge_atTop (C0 + 1))
  filter_upwards [hb1, hb2, habs, hsz.eventually (eventually_ge_atTop 1), hg] with n h1n h2n hn hN1r hgn
  rintro ⟨k, a⟩
  set N : ℝ := ((sz.size n : ℕ) : ℝ) with hNdef
  have hN0 : (0 : ℝ) < N := by linarith
  have hbound := GUEOneLoop_expect_bound sz hd hκ hΛ n hgn (hr n) (ht1 n) (ht10 n) (ht0 n) K (hK n) k
    (Nat.lt_succ_iff.1 k.isLt) hKst0.le (hKst d (sz.L n) (g n) (E n) (m n) (hr n)) (ρ := N ^ (ε / 4)) _ _ h1n h2n
    (fun ω hω b => by
      by_contra hc
      exact hω ⟨(k, b), lt_of_not_ge hc⟩)
    (fun ω hω a' q => by
      by_contra hc
      exact hω ⟨(k, a', q), lt_of_not_ge hc⟩) a
  -- the constants
  set Λ2 := (N * etaOf (m n) (gridTime t1 t0 K n k))⁻¹ ^ 2 with hΛ2
  have hΛ20 : 0 ≤ Λ2 := by rw [hΛ2]; exact sq_nonneg _
  set X := N ^ (ε / 2) with hX
  have hρ : (N ^ (ε / 4)) ^ 2 = X := by
    rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    ring_nf
  have hNε : N ^ ε = X * X := by
    rw [hX, ← Real.rpow_add hN0]
    ring_nf
  have hX1 : 1 ≤ X := by linarith
  have hk8 : 0 ≤ 8 * κ⁻¹ := by positivity
  have key : Kst * (X * CM + 8 * κ⁻¹) ≤ X * X := by
    have h1' : Kst * (X * CM + 8 * κ⁻¹) ≤ X * C0 := by
      have : 8 * κ⁻¹ ≤ 8 * κ⁻¹ * X := le_mul_of_one_le_right hk8 hX1
      calc Kst * (X * CM + 8 * κ⁻¹) ≤ Kst * (X * CM + 8 * κ⁻¹ * X) :=
            mul_le_mul_of_nonneg_left (by linarith) hKst0.le
        _ = X * C0 := by rw [hC0]; ring
    calc _ ≤ X * C0 := h1'
      _ ≤ X * X := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [hρ] at hbound
  calc _ ≤ Kst * ((X * CM + 8 * κ⁻¹) * Λ2) := hbound
    _ = (Kst * (X * CM + 8 * κ⁻¹)) * Λ2 := by ring
    _ ≤ (X * X) * Λ2 := mul_le_mul_of_nonneg_right key hΛ20
    _ = N ^ ε * Λ2 := by rw [hNε]


/-! ## 6. Compiled nonempty instances (target 5)

`d = 3`, `sz0` (`L_n = 4 (n + 1)`, `W_n = (2 (n + 1))^5`, `N_0 = 2^21`, `Defs/Sizes.lean`), the BA flow datum
of `sz0` at every `n` (`g_n = BAflowLam0`, `E_n = BAflowEs`, `m_n = BAmF`; `BAReal` at `κ = 1/2` for every `n` by
`BAflow_real`, `GreenStab:352` is `n = 0`), the grid `t₁ = 1/4`, `t₀ = 1/2`, `K = 4`.  Only `h1` and `hoff` of the main
instance stay premises (the pins of C5); every deterministic hypothesis is discharged. -/

end RBM.BA

end
