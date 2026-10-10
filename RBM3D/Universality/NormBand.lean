/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Universality.Pins
import RBM3D.Gauss.FineModel
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The band-model row `UNNormBandRow` (UN-10a, ticket T2372), `d ≥ 3`

`theorem unNormBandRow : UNNormBandRow` (`Universality/Pins.lean:834`): with probability
`≥ 1 - N^{-D}` every eigenvalue of `H = seqXmat sz n` satisfies `|λ_i| ≤ N^{CV₀}` (`UNNormBound`,
`Pins.lean:477`), `N = (W L)^d`.

Paper: arXiv:2507.20274, `(bandcw0)` (`paper/tex/1_2_Intro_model_result.tex:296`): the entries of
`H` are Gaussian with variance `S_xy ≤ 1`.  The bound `(2.3)` of the pin (`‖V‖ ≤ N^{C_V}`) is [32]
Def 2.1; the row is the band-model instance.  Route (every step proved here):

* each real coordinate `ω c` of `seqP sz` is `N(0, v)` with `v ≤ 1` (`Sizes.seqP_map_eval`,
  `NormBand_gvar_le`), hence sub-Gaussian with proxy `1`;
* the tail `P(|ω c| ≥ N) ≤ 2 e^{-N²/2}` and a union over the `2 N²` real coordinates of size `n`
  (`measure_iUnion_fintype_le`) leave probability `≤ 4 N² e^{-N²/2} ≤ N^{-D}` eventually in `n`
  (`NormBand_tail_arith`, from `N → ∞` only);
* on the complement every real coordinate is `≤ N`, every entry `≤ 2N` (`NormBand_Xentry_le`), and
  `|λ_i| ≤ N · 2N ≤ N³` (`NormBand_eig_le`), so `CV₀ = 3` works for `N ≥ 2`; the eigenvalue event
  lies inside the union of the coordinate tails (`measure_mono`; no measurability of the
  eigenvalues).

Ports (read only; copied and adapted in this file): RBM2D
`Universality/Step1RegularityB.lean:474` (`Step1RegularityB_eigenvalue_le`, RBM2D HEAD `9e0f275`,
last commit touching the file `81fca44`; there entries `≤ 1`, bound `#ι`; here a general entry
bound `B`, via the `ℓ^∞` operator norm), and the entry event of RBM2D
`Universality/Step1RegularityA.lean` (Gaussian tail and union bound).  The sub-Gaussian tail and
the `gvarF ≤ 1` count follow `Universality/GUEPhase/Markov.lean:690` (`Markov_gaussian_tail_le`)
and `Induction/AzumaProxyN2.lean:227` (`azumaProxy2_gvarF_le_one`).  What changes from `d = 2`:
the index set `Idx d L W` has `(W L)^d = sz.size n` elements (`Sizes.card_Idx`), the number of real
coordinates is `2 N²` (`Idx × Idx × Bool`), and the variance bound uses `sum_sbKernelR`
(`3 ≤ L`, from `sz.three_le_L`); only `Admissible`'s `SizeTendsto` is used.

The compiled instances at the end: the deterministic step on a `Fin 2` nondiagonal Hermitian
matrix; the threshold arithmetic at `sz0`, `n = 0`, `N = 2097152`, `D = 1`; and the theorem itself
at `sz0`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Univ

open MeasureTheory ProbabilityTheory Filter Matrix Topology
open RBM RBM.Gauss RBM.Gauss.Sizes
open scoped NNReal ENNReal

/-! ### The deterministic step -/

section Deterministic

open scoped Matrix.Norms.Operator in
/-- `|λ_i| ≤ #ι · B` when every entry has modulus `≤ B`: `H ψ = λ ψ` and the `ℓ^∞` operator norm
(RBM2D `Step1RegularityB.lean:474`, generalised from `B = 1`). -/
private theorem NormBand_eig_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {B : ℝ} (hent : ∀ x y, ‖H x y‖ ≤ B) (i : ι) :
    |hH.eigenvalues i| ≤ Fintype.card ι * B := by
  have hψ : (hH.eigenvectorBasis i).ofLp ≠ 0 := by
    intro h
    have h1 := hH.eigenvectorBasis.norm_eq_one i
    have : hH.eigenvectorBasis i = 0 := by ext x; simpa using congrFun h x
    rw [this] at h1
    simp at h1
  have hpos : 0 < ‖(hH.eigenvectorBasis i).ofLp‖ := norm_pos_iff.2 hψ
  have h1 := Matrix.linfty_opNorm_mulVec H (hH.eigenvectorBasis i).ofLp
  rw [hH.mulVec_eigenvectorBasis i, norm_smul, Real.norm_eq_abs] at h1
  refine (le_of_mul_le_mul_right h1 hpos).trans ?_
  rw [Matrix.linfty_opNorm_def]
  have hB : 0 ≤ B := (norm_nonneg _).trans (hent i i)
  have hsup : (Finset.univ.sup fun x : ι => ∑ y : ι, ‖H x y‖₊) ≤
      (Fintype.card ι : NNReal) * B.toNNReal := by
    refine Finset.sup_le fun x _ => ?_
    calc ∑ y, ‖H x y‖₊ ≤ ∑ _y : ι, B.toNNReal := Finset.sum_le_sum fun y _ => by
          rw [← NNReal.coe_le_coe]; simpa [Real.coe_toNNReal _ hB] using hent x y
      _ = _ := by simp
  simpa [Real.coe_toNNReal _ hB] using NNReal.coe_le_coe.2 hsup

/-- Every entry has modulus `≤ 2B` when every real coordinate has modulus `≤ B`
(`Universality/GUEPhase/Markov.lean:661`, `Markov_norm_Xentry_le`). -/
private theorem NormBand_Xentry_le (d L W : ℕ) [NeZero L] [NeZero W] (s : Ω d L W) {B : ℝ}
    (hs : ∀ c, |s c| ≤ B) (i j : Idx d L W) : ‖Xentry d L W s i j‖ ≤ 2 * B := by
  have h2 : ∀ a b : ℝ, |a| ≤ B → |b| ≤ B →
      ‖(a : ℂ) + Complex.I * (b : ℂ)‖ ≤ 2 * B ∧ ‖(a : ℂ) - Complex.I * (b : ℂ)‖ ≤ 2 * B :=
    fun a b ha hb => ⟨(norm_add_le _ _).trans (by simp; linarith),
      (norm_sub_le _ _).trans (by simp; linarith)⟩
  unfold Xentry
  split_ifs
  · exact (h2 _ _ (hs _) (hs _)).1
  · exact (h2 _ _ (hs _) (hs _)).2
  · simp only [Complex.norm_real, Real.norm_eq_abs]; linarith [hs (i, j, true), abs_nonneg (s (i, j, true))]

/-- Threshold arithmetic: if `N ≥ 1` and `N^{D+2} e^{-N/2} ≤ 1/4` then `4 N² e^{-N²/2} ≤ N^{-D}`
(`x² ≥ x`). -/
private theorem NormBand_tail_arith (D N : ℝ) (hN : 1 ≤ N)
    (h : N ^ (D + 2) * Real.exp (-(1 / 2) * N) ≤ 1 / 4) :
    4 * N ^ 2 * Real.exp (-(N ^ 2 / 2)) ≤ N ^ (-D) := by
  have hNpos : 0 < N := by linarith
  have h3 : N ^ 2 * N ^ D = N ^ (D + 2) := by
    rw [← Real.rpow_natCast N 2, ← Real.rpow_add hNpos]; push_cast; ring_nf
  have hexp : Real.exp (-(N ^ 2 / 2)) ≤ Real.exp (-(1 / 2) * N) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hpos : 0 < N ^ D := Real.rpow_pos_of_pos hNpos _
  rw [Real.rpow_neg hNpos.le, ← one_div, le_div_iff₀ hpos]
  calc 4 * N ^ 2 * Real.exp (-(N ^ 2 / 2)) * N ^ D
      = 4 * (N ^ (D + 2) * Real.exp (-(N ^ 2 / 2))) := by rw [← h3]; ring
    _ ≤ 4 * (N ^ (D + 2) * Real.exp (-(1 / 2) * N)) := by gcongr
    _ ≤ 4 * (1 / 4) := by gcongr
    _ = 1 := by norm_num

/-- `4 N² e^{-N²/2} ≤ N^{-D}` eventually in `n`, from `N → ∞` only (`x^s e^{-x/2} → 0`). -/
private theorem NormBand_tail_eventually (D : ℝ) {d : ℕ} (sz : Sizes d) (hd : sz.SizeTendsto) :
    ∀ᶠ n in atTop, 4 * Nsz sz n ^ 2 * Real.exp (-(Nsz sz n ^ 2 / 2)) ≤ Nsz sz n ^ (-D) := by
  have hdecay := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (D + 2) (1 / 2) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (D + 2) * Real.exp (-(1 / 2) * x) ≤ 1 / 4 :=
    hdecay.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [hd.eventually hsmall, hd.eventually_ge_atTop 1] with n hn hN1
  exact NormBand_tail_arith D _ hN1 hn

end Deterministic

/-! ### The Gaussian coordinates of `seqP` -/

section Coordinates

/-- Every coordinate has variance `≤ 1` (`S_xy = W^{-d} S^{(B)} ≤ 1`, `sum_sbKernelR`; copy of
`azumaProxy2_gvarF_le_one`, `Induction/AzumaProxyN2.lean:227`, at the size-sequence level). -/
private theorem NormBand_gvar_le {d : ℕ} (sz : Sizes d) (c : SeqCoord sz) : (seqGvar sz c : ℝ) ≤ 1 := by
  obtain ⟨n, c⟩ := c
  have hS : svarF d (sz.L n) (sz.W n) (sz.lam n) c.1 c.2.1 ≤ 1 := by
    have hW : ((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (Nat.one_le_cast.2 (sz.W_pos n)))
    have hK : ∀ x, sbKernelR d (sz.L n) (sz.lam n) x ≤ 1 := fun x =>
      (Finset.single_le_sum (fun y _ => sbKernelR_nonneg d (sz.L n) (sz.lam n) y)
        (Finset.mem_univ x)).trans_eq (sum_sbKernelR d (sz.L n) (sz.lam n) (sz.three_le_L n))
    exact (mul_le_mul hW (hK _) (sbKernelR_nonneg _ _ _ _) zero_le_one).trans_eq (one_mul 1)
  change ((gvarF d (sz.L n) (sz.W n) (sz.lam n) c : ℝ≥0) : ℝ) ≤ 1
  simp only [gvarF]
  split_ifs
  · exact hS
  · change svarF d (sz.L n) (sz.W n) (sz.lam n) c.1 c.2.1 / 2 ≤ 1
    linarith [svarF_nonneg d (sz.L n) (sz.W n) (sz.lam n) c.1 c.2.1]

/-- Each coordinate of `seqP` is sub-Gaussian with variance proxy `1`. -/
private theorem NormBand_subgaussian {d : ℕ} (sz : Sizes d) (c : SeqCoord sz) :
    HasSubgaussianMGF (fun ω : SeqΩ sz => ω c) 1 (seqP sz) := by
  have hX : AEMeasurable (fun ω : SeqΩ sz => ω c) (seqP sz) := (measurable_pi_apply _).aemeasurable
  rw [← HasSubgaussianMGF.id_map_iff hX, Sizes.seqP_map_eval]
  refine ⟨fun t => integrable_exp_mul_gaussianReal t, fun t => ?_⟩
  rw [mgf_id_gaussianReal]
  simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
  exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg t, NormBand_gvar_le sz c])

end Coordinates

/-! ### The row -/

/-- **Row `UNNormBandRow`, proved** with `CV₀ = 3`.  Every real coordinate is `N(0, v)`, `v ≤ 1`
(`NormBand_gvar_le`), so `P(|ω_c| ≥ N) ≤ 2e^{-N²/2}`; a union over the `2N²` coordinates leaves
probability `≤ 4N²e^{-N²/2} ≤ N^{-D}`; on the complement every entry is `≤ 2N`, so
`|λ_i| ≤ N · 2N ≤ N³` (`NormBand_eig_le`).  RBM2D `Step1RegularityA` (entry event),
`Step1RegularityB_eigenvalue_le`.  Uses of `Admissible 𝔠 𝔡`: `SizeTendsto` only. -/
theorem unNormBandRow : UNNormBandRow := by
  intro d hd 𝔠 𝔡 sz hA
  refine ⟨3, by norm_num, fun D hD => ?_⟩
  filter_upwards [NormBand_tail_eventually D sz hA.2.2.1, hA.2.2.1.eventually_ge_atTop 2] with n hn hN2
  set N : ℝ := Nsz sz n with hNdef
  have hN0 : 0 < N := by linarith
  have hcard : (Fintype.card (CoordF d (sz.L n) (sz.W n)) : ℝ) = 2 * N ^ 2 := by
    change (Fintype.card (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) : ℝ) = _
    rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, Sizes.card_Idx]; push_cast; ring
  have hsub : {ω : SeqΩ sz | ∃ i, N ^ (3 : ℝ) < |(Sizes.seqXmat_isHermitian sz n ω).eigenvalues i|} ⊆
      ⋃ c : CoordF d (sz.L n) (sz.W n), ({ω : SeqΩ sz | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ sz | N ≤ -ω ⟨n, c⟩}) := by
    rintro ω ⟨i, hi⟩
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, not_exists, not_or, not_le] at hcon
    have hs : ∀ c, |slice sz n ω c| ≤ N := fun c =>
      abs_le.2 ⟨by have h := (hcon c).2; change -N ≤ ω ⟨n, c⟩; linarith, (hcon c).1.le⟩
    have h1 := NormBand_eig_le (Sizes.seqXmat_isHermitian sz n ω) (B := 2 * N)
      (NormBand_Xentry_le d (sz.L n) (sz.W n) (slice sz n ω) hs) i
    rw [Sizes.card_Idx] at h1
    change |_| ≤ N * (2 * N) at h1
    have h3 : N ^ (3 : ℝ) = N ^ (3 : ℕ) := by exact_mod_cast Real.rpow_natCast N 3
    rw [h3] at hi
    have hN2' : 2 ≤ N := hN2
    nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.2 hN2')]
  have hterm : ∀ c : CoordF d (sz.L n) (sz.W n),
      seqP sz ({ω : SeqΩ sz | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ sz | N ≤ -ω ⟨n, c⟩}) ≤
        ENNReal.ofReal (2 * Real.exp (-(N ^ 2 / 2))) := by
    intro c
    have hsg := NormBand_subgaussian sz ⟨n, c⟩
    have h1 : (seqP sz).real {ω | N ≤ ω ⟨n, c⟩} ≤ Real.exp (-N ^ 2 / (2 * (1 : ℝ≥0))) :=
      hsg.measure_ge_le hN0.le
    have h2 : (seqP sz).real {ω | N ≤ -ω ⟨n, c⟩} ≤ Real.exp (-N ^ 2 / (2 * (1 : ℝ≥0))) :=
      hsg.neg.measure_ge_le hN0.le
    refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 ?_
    have h3 : -N ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) = -(N ^ 2 / 2) := by simp [neg_div]
    rw [h3] at h1 h2
    exact (measureReal_union_le _ _).trans (by linarith)
  change seqP sz {ω : SeqΩ sz | ∃ i, N ^ (3 : ℝ) < |(Sizes.seqXmat_isHermitian sz n ω).eigenvalues i|} ≤ _
  calc _ ≤ seqP sz (⋃ c : CoordF d (sz.L n) (sz.W n),
        ({ω : SeqΩ sz | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ sz | N ≤ -ω ⟨n, c⟩})) := measure_mono hsub
    _ ≤ ∑ c : CoordF d (sz.L n) (sz.W n),
        seqP sz ({ω : SeqΩ sz | N ≤ ω ⟨n, c⟩} ∪ {ω : SeqΩ sz | N ≤ -ω ⟨n, c⟩}) :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ _c : CoordF d (sz.L n) (sz.W n), ENNReal.ofReal (2 * Real.exp (-(N ^ 2 / 2))) :=
        Finset.sum_le_sum fun c _ => hterm c
    _ = ENNReal.ofReal (4 * N ^ 2 * Real.exp (-(N ^ 2 / 2))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcard]
        congr 1; ring
    _ ≤ ENNReal.ofReal (N ^ (-D)) := ENNReal.ofReal_le_ofReal hn

/-! ### Compiled instances -/

namespace NormBandInst

open RBM.Gauss.SizesInst

/-- A nondiagonal Hermitian `2 × 2` matrix, eigenvalues `±√3` (`tr = 0`, `det = -3`). -/
def H2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1 + Complex.I; 1 - Complex.I, -1]

theorem H2_isHermitian : H2.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [H2, Matrix.conjTranspose_apply, sub_eq_add_neg]

theorem H2_entry_le (x y : Fin 2) : ‖H2 x y‖ ≤ 3 / 2 := by
  have h1 : ‖(1 + Complex.I : ℂ)‖ ≤ 3 / 2 := by
    have : ‖(1 + Complex.I : ℂ)‖ ^ 2 = 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply]; norm_num
    nlinarith [norm_nonneg (1 + Complex.I : ℂ)]
  have h2 : ‖(1 - Complex.I : ℂ)‖ ≤ 3 / 2 := by
    have : ‖(1 - Complex.I : ℂ)‖ ^ 2 = 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply]; norm_num
    nlinarith [norm_nonneg (1 - Complex.I : ℂ)]
  fin_cases x <;> fin_cases y
  · change ‖(1 : ℂ)‖ ≤ 3 / 2
    norm_num
  · exact h1
  · exact h2
  · change ‖(-1 : ℂ)‖ ≤ 3 / 2
    norm_num

/-- The deterministic step (`NormBand_eig_le`) at `H2`: the matrix is nondiagonal (`H2 0 1 ≠ 0`),
every entry has modulus `≤ 3/2` (the actual maximum is `√2`), and `|λ_i| ≤ #ι · B = 2 · 3/2 = 3`
for both eigenvalues (they are `±√3`). -/
example : H2 0 1 ≠ 0 ∧ ∀ i : Fin 2, |H2_isHermitian.eigenvalues i| ≤ 3 := by
  refine ⟨?_, fun i => ?_⟩
  · have h : H2 0 1 = 1 + Complex.I := rfl
    rw [h]
    intro hz
    have := congrArg Complex.im hz
    simp at this
  have h := NormBand_eig_le H2_isHermitian H2_entry_le i
  simpa using h.trans_eq (by norm_num)

/-- `N = Nsz sz0 0 = 2097152` (`sz0_values`). -/
theorem Nsz_sz0_zero : Nsz sz0 0 = 2097152 := by
  rw [Nsz, sz0_values.2.2.1]; norm_num

/-- `e^{2^20} ≥ 131073^8`, from `1 + x ≤ e^x` at `x = 2^17` and `e^{8x} = (e^x)^8`. -/
theorem exp_ge : (131073 : ℝ) ^ 8 ≤ Real.exp 1048576 := by
  have h : (131072 : ℝ) + 1 ≤ Real.exp 131072 := by linarith [Real.add_one_le_exp (131072 : ℝ)]
  calc (131073 : ℝ) ^ 8 = (131072 + 1) ^ 8 := by norm_num
    _ ≤ (Real.exp 131072) ^ 8 := pow_le_pow_left₀ (by norm_num) h 8
    _ = Real.exp 1048576 := by rw [← Real.exp_nat_mul]; norm_num

/-- The threshold arithmetic of the union bound (`NormBand_tail_arith`) at `sz0`, `n = 0`,
`N = 2097152`, `D = 1`: both hypotheses (`N ≥ 1`, `N^{D+2} e^{-N/2} ≤ 1/4`) are discharged, and
`4 N² e^{-N²/2} ≤ N^{-1}`. -/
example : 4 * Nsz sz0 0 ^ 2 * Real.exp (-(Nsz sz0 0 ^ 2 / 2)) ≤ Nsz sz0 0 ^ (-(1 : ℝ)) := by
  rw [Nsz_sz0_zero]
  refine NormBand_tail_arith 1 _ (by norm_num) ?_
  rw [show ((1 : ℝ) + 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    show (-(1 / 2) * (2097152 : ℝ)) = -1048576 by norm_num, Real.exp_neg,
    ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc (2097152 : ℝ) ^ 3 ≤ 1 / 4 * 131073 ^ 8 := by norm_num
    _ ≤ 1 / 4 * Real.exp 1048576 := by gcongr; exact exp_ge

/-- **The target at concrete data**: `unNormBandRow` at `d = 3`, `sz0` (`N = 2097152` at `n = 0`),
`(𝔠, 𝔡) = (1/6, 1/10)` (`sz0_admissible`, every deterministic hypothesis discharged). -/
example : ∃ CV₀ : ℝ, 0 ≤ CV₀ ∧ UNNormBound sz0 (UNModel.band sz0) CV₀ :=
  unNormBandRow 3 le_rfl (1 / 6) (1 / 10) sz0 sz0_admissible

example : UNNormBandRow := unNormBandRow

end NormBandInst

end RBM.Univ
