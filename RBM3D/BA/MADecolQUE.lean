/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.MALocal
import RBM3D.BA.MAQDiff
import RBM3D.BA.GUEKPrim
import RBM3D.Main.QUEFromQDiff
import RBM3D.Universality.QUEFlow

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology
open scoped ENNReal Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss RBM.Gauss.Sizes RBM.Univ RBM.Endpoints

open private QUEFlow_queFixed QUEFlow_core QUEFlow_X QUEFlow_obs_eq QUEFlow_obs_herm QUEFlow_sub_of_normSq
  QUEFlow_rpow_sub from RBM3D.Universality.QUEFlow
open private queCore_quad_blk from RBM3D.Main.QUECore

/-!
# M/N M3 (T2518): decol and QUE at block Anderson, per `d`, and the `UNQueBA` bridge (`BA/MADecolQUE`)

Ticket T2518 (dispatcher V4, DECISIONS §341; supervisor `2026-10-15-0643` Q4 (a), MNO-C1, MNO-C3, MNO-C4).  Paper: `MR:decol_BA`
bullets 1 and 3 (`1_2:651`, `1_2:655`), `(eq:psikLinfty)` (`1_2:367`), `(Meq:QUE)`, `(Meq:QUE2)` (`1_2:411-417`), the proof outlines
`1_2:397-401`, `1_2:524-543`.  Law `Sizes.seqP (sz.withLam 0)`, matrix `sz.seqHBA`, ρ-bulk `BAbulk` (DECISIONS §51), profile `BAprof`.
The MN1 pin texts are those of `BA/MAPins`, read by name.

* P `UNQueBAAt`, `UNQueBA_iff_at` (the only public definition; `Iff.rfl`): `UNQuek` at `UNKind.ba d` after `∀ d, 3 ≤ d →` (MNO-C3).
* §2 decol: `baMz_diag` (`M_xx = m`, `Im M_xx ≤ 1`), the private core (band `decol_core`, `Main/FixedZ:750`, with `C_M = 1`), `baMADecol`,
  `baEnd_decolL`, `baEnd_decolL_three`.
* §3 QUE: the private measurability, domain and row-difference lemmas, the generic `que2Bad_sub`, `baQueFixed`, `baMAQUE`,
  `baEnd_QUEL`, `baEnd_QUEL_three`.
* §4 `unQueBAAt_of_QUEL` (the per-`d` core of `UNQueBA_of_BAEnd_QUEL`), `unQueBAAt_of_ML`, `unQueBAAt_three`.
* §5 compiled nonempty instances at `d = 3` on `S0`.

`d > 3` enters only through `UNMLOutBA d` (Jun decision B, DECISIONS §316).  Every helper is `private` or prefixed `MADecolQUE_`.
-/

/-! ## P: the per-`d` reading of `UNQueBA` -/

/-- **`UNQueBAAt d`** (new, MNO-C3): `UNQuek` (`Universality/PinsK.lean:398-403`) at `UNKind.ba d`, after `∀ d, 3 ≤ d →` (cut as
`UNLocAvgBAAt`, `BA/MAPins.lean:170`). -/
def UNQueBAAt (d : ℕ) : Prop :=
  ∀ 𝔠 𝔡 : ℝ, ∀ sz : Sizes d, sz.Admissible 𝔠 𝔡 → ∀ κ : ℝ, 0 < κ →
    ∀ ε₀ c τ : ℝ, 0 < ε₀ → ε₀ < 𝔡 / 2 → 0 < c → c < ε₀ → c < 𝔡 / 5 → 0 < τ →
      ∀ᶠ n in atTop, ∀ E : ℝ, (UNKind.ba d).bulk sz κ E n → ∀ a : Zd d (sz.L n),
        ((UNKind.ba d).M sz).μ {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (((UNKind.ba d).M sz).H n ω)} ≤
          queBound (sz.W n) 𝔡 ε₀ c τ

/-- **P2**: `UNQueBA` is `∀ d, 3 ≤ d → UNQueBAAt d` (`Iff.rfl`; twin `UNLocAvgBA_iff_at`, `BA/MAPins.lean:196`). -/
theorem UNQueBA_iff_at : UNQueBA ↔ ∀ d : ℕ, 3 ≤ d → UNQueBAAt d := Iff.rfl

/-! ## 2. Decol at BA (twin `decol_of_locSC`, `Main/FixedZ.lean:789`) -/

section Decol

/-- **Target 1, `baMz_diag`**: on the fine lattice `M_xx = m(z)` (`BAMres_fine_apply` at the same offset, `BAMB_diag_eq` at `BAm_self`),
so `Im M_xx ≤ ‖m‖ ≤ 1` (`BAm_norm_le_one`): the band's `Mband x x = msc`, `‖msc‖ < 1`, with the same constant `C_M = 1`. -/
theorem baMz_diag {d : ℕ} (sz : Sizes d) (n : ℕ) (z : ℂ) (hz : 0 < z.im) (x : Idx d (sz.L n) (sz.W n)) :
    BAMz sz n z x x = BAm d (sz.L n) (sz.lam n) z ∧ (BAMz sz n z x x).im ≤ 1 := by
  have hs := BAm_self d (sz.L n) (sz.lam n) z hz
  have hw : (z + BAm d (sz.L n) (sz.lam n) z).im ≠ 0 := by
    have := hs.1
    simp only [Complex.add_im]
    linarith
  have h : BAMz sz n z x x = BAm d (sz.L n) (sz.lam n) z := by
    unfold BAMz
    rw [BAMres_fine_apply d (sz.L n) (sz.W n) (sz.lam n) z _ hw x x]
    simp only [↓reduceIte]
    exact BAMB_diag_eq d (sz.L n) (sz.lam n) z _ hs _
  refine ⟨h, ?_⟩
  rw [h]
  exact (Complex.im_le_norm _).trans (BAm_norm_le_one d (sz.L n) (sz.lam n) z _ hz.le hs)

/-- **Target 2 (private), the deterministic core of `decol` from `locSC`** (band `decol_core`, `Main/FixedZ.lean:750`): on the event
`¬ ∃ z ∈ BAendDom κ ε, BAlocBad1z τ_L` every orthonormal eigenbasis of `sz.seqHBA n ω` has `‖ψ_k(x)‖² ≤ N^{-1+τ}` for the ρ-bulk
eigenvalues: take `z = μ_k + iη`, `η = N^{-1+ε}`, `‖G_xx - m‖² ≤ W^{τ_L} 𝓑_{η,0} ≤ 1` (`baMz_diag`), `Im m ≤ 1 = C_M`, so
`‖ψ_k(x)‖² ≤ 2η ≤ N^{-1+τ}` (`decol_spectral_core`, carrier-free). -/
private theorem MADecolQUE_decol_core {d : ℕ} (sz : Sizes d) {κ ε τ τL : ℝ} (n : ℕ) (ω : sz.SeqΩ) (hε1 : ε ≤ 1)
    (hgood : ¬ ∃ z : ℂ, BAendDom sz κ ε n z ∧ BAlocBad1z sz τL n z ω)
    (hs1 : ((sz.W n : ℕ) : ℝ) ^ τL * calB sz n (Nsz sz n ^ (-1 + ε)) 0 ≤ 1)
    (hs2 : 2 * Nsz sz n ^ (-1 + ε) ≤ Nsz sz n ^ (-1 + τ)) : ¬ BAdecolBad sz κ τ n ω := by
  intro hbad
  apply hbad
  intro μ ψ hψ k hk x
  set η := Nsz sz n ^ (-1 + ε) with hηdef
  have hNpos := Nsz_pos sz n
  have hη0 : 0 < η := Real.rpow_pos_of_pos hNpos _
  have hN1 : (1 : ℝ) ≤ Nsz sz n := by exact_mod_cast one_le_size sz n
  have hη1 : η ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hdom : BAendDom sz κ ε n ((μ k : ℂ) + η * Complex.I) :=
    ⟨by simpa using hk, by simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]; exact le_rfl, by simpa using hη1⟩
  have hnot : ¬ BAlocBad1z sz τL n ((μ k : ℂ) + η * Complex.I) ω := fun h => hgood ⟨_, hdom, h⟩
  unfold BAlocBad1z at hnot
  push Not at hnot
  have hxx := hnot x x
  have hdist : distB sz n (STblk sz n x) (STblk sz n x) = 0 := by simp [distB, zdistInf_zero]
  have him : ((μ k : ℂ) + η * Complex.I).im = η := by simp
  rw [hdist, him] at hxx
  obtain ⟨hM, hMim⟩ := baMz_diag sz n ((μ k : ℂ) + η * Complex.I) (by simpa using hη0) x
  rw [hM] at hxx
  have hsq := hxx.trans hs1
  have hloc : ‖Gres (sz.seqHBA n ω) ((μ k : ℂ) + η * Complex.I) true x x -
      BAm (d) (sz.L n) (sz.lam n) ((μ k : ℂ) + η * Complex.I)‖ ≤ 1 := by
    have h0 := norm_nonneg (BAGz sz n ((μ k : ℂ) + η * Complex.I) ω x x -
      BAm d (sz.L n) (sz.lam n) ((μ k : ℂ) + η * Complex.I))
    have : ‖BAGz sz n ((μ k : ℂ) + η * Complex.I) ω x x -
      BAm d (sz.L n) (sz.lam n) ((μ k : ℂ) + η * Complex.I)‖ ≤ 1 := by nlinarith
    exact this
  rw [hM] at hMim
  exact decol_spectral_core hψ hη0 hloc hMim (by linarith)

/-- **Target 3, `baMADecol`** (`MADecol` at BA; `1_2:397-401`, `(eq:ukx)` `1_2:399`): `decol` from `locSC`, at `ε = min(τ/2, 1/2)` and
`τ_L = min(𝔡, dε/2)` as the band `decol_of_locSC` (`decol_scalars` verbatim). -/
theorem baMADecol (d : ℕ) : BAMADecol d := by
  intro h hd 𝔠 𝔡 sz hA κ τ D hκ hτ hD
  have hd2 : 2 ≤ d := by omega
  have h𝔡 : 0 < 𝔡 := hA.2.1
  have hε0 : 0 < min (τ / 2) (1 / 2 : ℝ) := lt_min (half_pos hτ) (by norm_num)
  have hε1 : min (τ / 2) (1 / 2 : ℝ) ≤ 1 := (min_le_right _ _).trans (by norm_num)
  have hτL0 : 0 < min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2) := by
    refine lt_min h𝔡 ?_
    have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  filter_upwards [h hd 𝔠 𝔡 sz hA κ (min (τ / 2) (1 / 2)) (min 𝔡 ((d : ℝ) * min (τ / 2) (1 / 2) / 2)) D
    hκ hε0 hτL0 hD, decol_scalars sz hd2 hA hτ] with n hn hsc
  refine le_trans (measure_mono ?_) hn.1
  intro ω hbad
  by_contra hnot
  exact MADecolQUE_decol_core sz n ω hε1 hnot hsc.1 hsc.2 hbad

/-- **Target 4, `baEnd_decolL`** (`MR:decol_BA` bullet 1, `1_2:651`): `BAEnd_decolL d` from `UNMLOutBA d` (`baMADecol d` ∘ `baEnd_locSCL`). -/
theorem baEnd_decolL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_decolL d :=
  baMADecol d (baEnd_locSCL d hML)

/-- **Target 4, `baEnd_decolL_three`**: `BAEnd_decolL 3`, unconditional (`baMADecol 3` at `baEnd_locSCL_three`); closing condition (i). -/
theorem baEnd_decolL_three : BAEnd_decolL 3 := baMADecol 3 baEnd_locSCL_three

end Decol

/-! ## 3. QUE at BA (twin `QUE_of_QDiff`, `Main/QUEFromQDiff.lean:502`) -/

section QUE

/-- **Target 5a (private)**: the matrix `sz.seqHBA n` is measurable (`(UNModel.ba sz).meas`, entrywise, `measurable_pi_iff` twice). -/
private theorem MADecolQUE_meas {d : ℕ} (sz : Sizes d) (n : ℕ) : Measurable (sz.seqHBA n) :=
  measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => (UNModel.ba sz).meas n i j

/-- **Target 5b (private)**: `z = E + iη_Q ∈ BAendDom κ (𝔠(𝔡 - ε₀))` for `E` in the ρ-bulk, eventually.  The `Im` bounds do not depend on
`E`: they are the `Im` half of the band `queDomain` (`Main/QUEFromQDiff.lean:91`) at `(κ, E) = (1, 0)` (a proof use only); the real part is `E`. -/
private theorem MADecolQUE_domain {d : ℕ} (sz : Sizes d) {𝔠 𝔡 : ℝ} (hA : sz.Admissible 𝔠 𝔡) {ε₀ κ : ℝ} (hε₀ : 0 < ε₀)
    (hε₀𝔡 : ε₀ < 𝔡) :
    ∀ᶠ n in atTop, ∀ E : ℝ, BAbulk d (sz.L n) (sz.lam n) κ E →
      BAendDom sz κ (𝔠 * (𝔡 - ε₀)) n ((E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) := by
  filter_upwards [queDomain sz hA (κ := 1) hε₀ hε₀𝔡] with n hn E hE
  have h0 := hn 0 (by norm_num)
  refine ⟨by simpa using hE, ?_, ?_⟩
  · simpa using h0.2.1
  · simpa using h0.2.2

/-- **Target 5c (private), the row differences of `BAprof`** (`T2518_RowDiff`): `baThetaDiff` (`BA/GUEKPrim`) at `σ = false, true` by
unfolding `BAprof`; the consumer form of `queRowDiff` (`Main/QUEFromQDiff.lean:244`).  `∃ C` before `sz`. -/
private theorem MADecolQUE_rowDiff : ∀ d : ℕ, 3 ≤ d → ∀ 𝔡 κ : ℝ, 0 < 𝔡 → 0 < κ → ∃ C : ℝ, 0 < C ∧
    ∀ (sz : Sizes d) (n : ℕ), 0 < sz.lam n → sz.lam n ≤ 𝔡⁻¹ →
      ∀ z : ℂ, 0 < z.im → z.im ≤ 1 → BAbulk d (sz.L n) (sz.lam n) κ z.re → ∀ a b b' : Zd d (sz.L n),
        ‖BAprof sz n z true false a b - BAprof sz n z true false a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d ∧
        ‖BAprof sz n z true true a b - BAprof sz n z true true a b'‖ ≤ C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d := by
  intro d hd 𝔡 κ h𝔡 hκ
  obtain ⟨C, hC, H⟩ := baThetaDiff d hd 𝔡 κ h𝔡 hκ
  exact ⟨C, hC, fun sz n hl hl1 z hz hz1 hb a b b' =>
    ⟨H sz n hl hl1 z hz hz1 hb false a b b', H sz n hl hl1 z hz hz1 hb true a b b'⟩⟩

/-- **Target 6 (private), the generic `que2Bad_sub`**: `(Meq:QUE2)` event `⊆ {W^{-2c} ≤ 4N²η² X_{1_A/|A|}}` on any matrix-valued `Hm`
(copy of the band `que2Bad_sub`, `Main/QUECore.lean:1013-1082`, bound to `seqXmat`; the first half is `QUEFlow_queBad_sub` inside
`QUEFlow_queFixed`).  The private helpers `QUEFlow_obs_eq`, `QUEFlow_obs_herm`, `QUEFlow_sub_of_normSq`, `QUEFlow_rpow_sub` and
`queCore_quad_blk` are reached by `open private`. -/
private theorem MADecolQUE_que2Bad_sub {d : ℕ} {sz : Sizes d} {n : ℕ} {Ω : Type}
    (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ε₀ c E η : ℝ) (hη : 0 < η)
    (hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ η)
    (A : Finset (Zd d (sz.L n))) (hA : A.Nonempty) :
    {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (Hm ω)} ⊆
      {ω | ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) ≤
        4 * Nsz sz n ^ 2 * η ^ 2 *
          QUEFlow_X Hm ((E : ℂ) + (η : ℂ) * Complex.I)
            (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) ω} := by
  intro ω hω
  obtain ⟨μ, ψ, hψ, k, hk, hbad⟩ := hω
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hN : (0 : ℝ) < Nsz sz n := Nsz_pos sz n
  have hNeq : ((((sz.W n * sz.L n) ^ d : ℕ) : ℝ)) = Nsz sz n := rfl
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  set cA : Zd d (sz.L n) → ℝ := fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0 with hcA
  have hdom := normSq_le_trace (Hm ω) μ ψ hψ E η hη
    (queObs d (sz.L n) (sz.W n) cA) (QUEFlow_obs_herm _ _ _ _) k k (hwin _ hk) (hwin _ hk)
  set S : Zd d (sz.L n) → ℝ := fun u => ∑ x ∈ Iblk d (sz.L n) (sz.W n) u, ‖ψ k x‖ ^ 2 with hS
  set r : ℝ := (A.card : ℝ)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ a ∈ A, S a - (Nsz sz n)⁻¹ with hr
  have hunit : star (ψ k) ⬝ᵥ ψ k = 1 := by rw [hψ.1 k k]; simp
  have hC : star (ψ k) ⬝ᵥ (queObs d (sz.L n) (sz.W n) cA *ᵥ ψ k) = (r : ℂ) := by
    rw [QUEFlow_obs_eq, Matrix.sub_mulVec, Matrix.sum_mulVec, dotProduct_sub, dotProduct_sum,
      Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hunit]
    simp only [Matrix.smul_mulVec, dotProduct_smul, queCore_quad_blk, smul_eq_mul]
    have hsum : ∑ u, ((cA u : ℝ) : ℂ) * ((((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ * S u : ℝ) : ℂ) =
        (((A.card : ℝ)⁻¹ * (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * ∑ a ∈ A, S a : ℝ) : ℂ) := by
      have h1 : ∀ u, ((cA u : ℝ) : ℂ) * ((((((sz.W n : ℕ) : ℝ)) ^ d)⁻¹ * S u : ℝ) : ℂ) =
          if u ∈ A then (((A.card : ℝ)⁻¹ * ((((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * S u) : ℝ) : ℂ) else 0 := by
        intro u
        by_cases hu : u ∈ A
        · simp only [hcA, hu, ↓reduceIte]
          push_cast
          ring
        · simp [hcA, hu]
      simp only [h1]
      rw [Finset.sum_ite_mem, Finset.univ_inter]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      ring
    rw [hsum, hr]
    have : ((((sz.W n * sz.L n) ^ d : ℕ) : ℂ))⁻¹ = (((Nsz sz n)⁻¹ : ℝ) : ℂ) := by
      rw [← hNeq]; push_cast; rfl
    rw [this]
    push_cast
    ring
  rw [hC] at hdom
  have hWd : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ d := by positivity
  have hid : (∑ a ∈ A, S a) - ((sz.W n : ℕ) : ℝ) ^ d / Nsz sz n * (A.card : ℝ) =
      (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * r := by
    rw [hr]
    field_simp
  have hbad' := hbad
  rw [QUEFlow_rpow_sub hW, hNeq] at hbad'
  have hbad'' : (((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ * (A.card : ℝ) / Nsz sz n) ≤
      (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * |r| := by
    have h2 : |A.sum S - ((sz.W n : ℕ) : ℝ) ^ d / Nsz sz n * (A.card : ℝ)| =
        (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * |r| := by
      rw [show A.sum S = ∑ a ∈ A, S a from rfl, hid, abs_mul, abs_of_pos (by positivity)]
    rw [← h2]
    exact hbad'
  have hnorm : (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n ≤ ‖(r : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine le_of_mul_le_mul_left (a := (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d) ?_ (by positivity)
    calc (A.card : ℝ) * ((sz.W n : ℕ) : ℝ) ^ d * ((((sz.W n : ℕ) : ℝ) ^ c)⁻¹ / Nsz sz n)
        = ((sz.W n : ℕ) : ℝ) ^ d * (((sz.W n : ℕ) : ℝ) ^ c)⁻¹ * (A.card : ℝ) / Nsz sz n := by ring
      _ ≤ _ := hbad''
  exact QUEFlow_sub_of_normSq hW hN _ hnorm hdom

/-- The second half of `QUEFlow_queFixed` on a generic carrier (private; target 6 continued): `QUEFlow_core` at `c = 1_A/|A|`, the generic
`que2Bad_sub`, `queMarkov` with `s = W^{-2c}`, `f = 4N²η_Q² X_c`, `T = 4N²η_Q² · 4(K + ε)`. -/
private theorem MADecolQUE_que2Fixed {d : ℕ} {sz : Sizes d} {n : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Hm : Ω → Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (hHm : Measurable Hm)
    (hH : ∀ ω, (Hm ω).IsHermitian) (ε₀ c E ε K : ℝ) (z : ℂ) (PM PP : Zd d (sz.L n) → Zd d (sz.L n) → ℂ)
    (hz : z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) (hη : 0 < etaQ sz n ε₀)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖Gres (Hm ω) z true x y‖ ^ 2 : ℝ) : ℂ)) a b ∂P) - PM a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => Gres (Hm ω) z true x y * Gres (Hm ω) z true y x) a b ∂P) - PP a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n), ‖PM a b - PM a b'‖ ≤ K ∧ ‖PP a b - PP a b'‖ ≤ K)
    (A : Finset (Zd d (sz.L n))) (hA : A.Nonempty) :
    P {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (Hm ω)} ≤
      ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c))) := by
  have hz0 : 0 < z.im := by rw [hz]; simpa using hη
  have hwin : ∀ x : ℝ, queWindow d (sz.L n) (sz.W n) (sz.lam n) ε₀ E x → |x - E| ≤ etaQ sz n ε₀ :=
    fun x hx => hx
  have hW : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := by exact_mod_cast sz.W_pos n
  have hs : (0 : ℝ) < ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)) := Real.rpow_pos_of_pos hW _
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  obtain ⟨hint, hnn, hI⟩ := QUEFlow_core (P := P) hHm hH z hz0 ε K PM PP hQ hK
    (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) (fun u => by split_ifs <;> positivity) (by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ hcard.ne')
  have hN := Nsz_pos sz n
  have hsub := MADecolQUE_que2Bad_sub Hm ε₀ c E _ hη hwin A hA
  rw [← hz] at hsub
  refine queMarkov P
    (fun ω => 4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 *
      QUEFlow_X Hm z (fun u => if u ∈ A then ((A.card : ℝ))⁻¹ else 0) ω)
    (hint.const_mul _) (fun ω => mul_nonneg (by positivity) (hnn ω)) hs ?_ _ hsub
  rw [MeasureTheory.integral_const_mul]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- **Target 7, `baQueFixed`** (twin `queFixed`, `Main/QUEFromQDiff.lean:285`): QUE at one `(sz, n, E)` under the law `seqP (sz.withLam 0)`,
matrix `sz.seqHBA`, `z = E + iη_Q`, the profile `BAprof`.  First half: `QUEFlow_queFixed` (`Universality/QUEFlow.lean:815`) at
`Hm = sz.seqHBA n`; second half: `MADecolQUE_que2Fixed` (target 6). -/
theorem baQueFixed {d : ℕ} (sz : Sizes d) (n : ℕ) (ε₀ c E ε K : ℝ) (z : ℂ)
    (hz : z = (E : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) (hη : 0 < etaQ sz n ε₀)
    (hQ : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n z ω x y‖ ^ 2 : ℝ) : ℂ)) a b ∂(Sizes.seqP (sz.withLam 0))) -
          BAprof sz n z true false a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n z ω x y * BAGz sz n z ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
          BAprof sz n z true true a b‖ ≤ ε)
    (hK : ∀ a b b' : Zd d (sz.L n),
      ‖BAprof sz n z true false a b - BAprof sz n z true false a b'‖ ≤ K ∧
        ‖BAprof sz n z true true a b - BAprof sz n z true true a b'‖ ≤ K) :
    (∀ a : Zd d (sz.L n),
      Sizes.seqP (sz.withLam 0) {ω | queBadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E a (sz.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) ∧
    (∀ A : Finset (Zd d (sz.L n)), A.Nonempty →
      Sizes.seqP (sz.withLam 0) {ω | que2BadMat d (sz.L n) (sz.W n) (sz.lam n) ε₀ c E A (sz.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz sz n ^ 2 * etaQ sz n ε₀ ^ 2 * (4 * (K + ε)) / ((sz.W n : ℕ) : ℝ) ^ (-(2 * c)))) := by
  have hmeas := MADecolQUE_meas sz n
  have hherm := seqHBA_isHermitian sz n
  exact ⟨fun a => QUEFlow_queFixed (Sizes.seqP (sz.withLam 0)) (sz.seqHBA n) hmeas hherm ε₀ c E ε K z
    (BAprof sz n z true false) (BAprof sz n z true true) hz hη hQ hK a,
    fun A hA => MADecolQUE_que2Fixed (Sizes.seqP (sz.withLam 0)) (sz.seqHBA n) hmeas hherm ε₀ c E ε K z
      (BAprof sz n z true false) (BAprof sz n z true true) hz hη hQ hK A hA⟩

/-- **Target 8, `baMAQUE`** (`MAQUE` at BA; `1_2:411-417`, proof `1_2:524-543`; twin `QUE_of_QDiff`, `Main/QUEFromQDiff.lean:502`):
`BAEnd_QDiffL d` at `(κ, 𝔠(𝔡 - ε₀), τ/2, 1)` (the expectation half at `z = E + iη_Q ∈ BAendDom`, `MADecolQUE_domain`), the row differences of
`baThetaDiff`, `baQueFixed` at each `(n, E)` and the carrier-free exponent count `queChain`.  The hypotheses `0 < c`, `c < ε₀`, `c < 𝔡/5`
are not used, as for the band. -/
theorem baMAQUE (d : ℕ) : BAMAQUE d := by
  intro hQD hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ hε₀ hε₀𝔡 hc hcε hc𝔡 hτ
  have h𝔠 : 0 < 𝔠 := hA.1
  have h𝔡 : 0 < 𝔡 := hA.2.1
  obtain ⟨C, hC, hrow⟩ := MADecolQUE_rowDiff d hd 𝔡 κ h𝔡 hκ
  have hε : 0 < 𝔠 * (𝔡 - ε₀) := mul_pos h𝔠 (by linarith)
  have hQ := hQD hd 𝔠 𝔡 sz hA κ (𝔠 * (𝔡 - ε₀)) (τ / 2) 1 hκ hε (half_pos hτ) one_pos
  have hdom := MADecolQUE_domain sz hA (κ := κ) hε₀ (by linarith)
  have hch := queChain hd sz hA ε₀ c τ C hε₀ hε₀𝔡 hτ hC
  have hW : ∀ n, (0 : ℝ) < ((sz.W n : ℕ) : ℝ) := fun n => by exact_mod_cast sz.W_pos n
  filter_upwards [hQ, hdom, hch, hA.2.2.2.2] with n hQn hdomn hchn hWOn E hE
  have hD := hdomn E hE
  have him : (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im = etaQ sz n ε₀ := by simp
  have hη : 0 < etaQ sz n ε₀ := by
    have h0 := hD.2.1
    rw [him] at h0
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (Nsz_pos sz n) _) h0
  have hz0 : 0 < (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im := by rw [him]; exact hη
  have hz1 : (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I).im ≤ 1 := hD.2.2
  have hlam : 0 < sz.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos (hW n) _) hWOn.1
  have hK := hrow sz n hlam hWOn.2 _ hz0 hz1 hD.1
  have hQ' : ∀ a b : Zd d (sz.L n),
      ‖(∫ ω, avg2 sz n (fun x y => ((‖BAGz sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω x y‖ ^ 2 : ℝ) : ℂ)) a b
          ∂(Sizes.seqP (sz.withLam 0))) - BAprof sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) true false a b‖ ≤
        qdBoundExp sz n (τ / 2) (etaQ sz n ε₀) ∧
      ‖(∫ ω, avg2 sz n (fun x y => BAGz sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω x y *
          BAGz sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) ω y x) a b ∂(Sizes.seqP (sz.withLam 0))) -
          BAprof sz n (((E : ℝ) : ℂ) + (etaQ sz n ε₀ : ℂ) * Complex.I) true true a b‖ ≤
        qdBoundExp sz n (τ / 2) (etaQ sz n ε₀) := by
    intro a b
    have h := hQn.2 _ hD a b
    rwa [him] at h
  obtain ⟨h1, h2⟩ := baQueFixed sz n ε₀ c E (qdBoundExp sz n (τ / 2) (etaQ sz n ε₀))
    (C * (sz.lam n ^ 2)⁻¹ / ((sz.W n : ℕ) : ℝ) ^ d) _ rfl hη hQ' (fun a b b' => hK a b b')
  exact ⟨fun a => (h1 a).trans (ENNReal.ofReal_le_ofReal hchn),
    fun A hA' => (h2 A hA').trans (ENNReal.ofReal_le_ofReal hchn)⟩

/-- **Target 8, `baEnd_QUEL`** (`MR:decol_BA` bullet 3, `1_2:655`): `BAEnd_QUEL d` from `UNMLOutBA d` (`baMAQUE d` ∘ `baEnd_QDiffL`). -/
theorem baEnd_QUEL (d : ℕ) (hML : UNMLOutBA d) : BAEnd_QUEL d :=
  baMAQUE d (baEnd_QDiffL d hML)

/-- **Target 8, `baEnd_QUEL_three`**: `BAEnd_QUEL 3`, unconditional (`baMAQUE 3` at `baEnd_QDiffL_three`); closing condition (i). -/
theorem baEnd_QUEL_three : BAEnd_QUEL 3 := baMAQUE 3 baEnd_QDiffL_three

end QUE

/-! ## 4. The `UNQueBA` bridge through a per-`d` core (MNO-C3; T2513 D5 `T2513_que_core`) -/

section Bridge

/-- **Target 9, `unQueBAAt_of_QUEL`** (the per-`d` core): the first half of `BAqueConclL` at one `d` is `UNQueBAAt d`
(the merged bridge's `.mono fun n hn E hE a => (hn E hE).1 a`, `UNPins.lean:357-359`). -/
theorem unQueBAAt_of_QUEL (d : ℕ) (hd : 3 ≤ d) (h : BAEnd_QUEL d) : UNQueBAAt d := by
  intro 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6
  exact (h hd 𝔠 𝔡 sz hA κ hκ ε₀ c τ h1 h2 h3 h4 h5 h6).mono fun n hn E hE a => (hn E hE).1 a

/-- **Target 9, `unQueBAAt_of_ML`** (core ∘ `baEnd_QUEL`): `UNQueBAAt d` from `UNMLOutBA d`. -/
theorem unQueBAAt_of_ML (d : ℕ) (hd : 3 ≤ d) (hML : UNMLOutBA d) : UNQueBAAt d :=
  unQueBAAt_of_QUEL d hd (baEnd_QUEL d hML)

/-- **Target 9, `unQueBAAt_three`** (core at `baEnd_QUEL_three`): `UNQueBAAt 3`, unconditional; N2's `d = 3` input, no `∀ d` BA input. -/
theorem unQueBAAt_three : UNQueBAAt 3 := unQueBAAt_of_QUEL 3 le_rfl baEnd_QUEL_three

end Bridge

/-! ## 5. Compiled nonempty instances at `d = 3` on the class sequence `S0` (`(L, g) = (4, 3/10)`, `(𝔠, 𝔡) = (1/6, 1/10)`) -/

section Inst

open RBM.BA.UNPinsInst RBM.Univ.BAInst RBM.BA.FlowPinsInst RBM.Gauss.SizesInst

private theorem MADecolQUE_hg : (0 : ℝ) < 3 / 10 := by norm_num

/-- **Target 1** at `sz0`, `n = 0`, `z = i`, the fine-lattice point `x = 0`: `M_xx = m(i)` and `Im M_xx ≤ 1`. -/
example := baMz_diag sz0 0 Complex.I (by simp) (0 : Idx 3 (sz0.L 0) (sz0.W 0))

/-- **Target 1** at `S0`, `n = 1`, `z = E_* + i/2`, `x = 0`. -/
example := baMz_diag S0 1 (⟨(fp 4 MADecolQUE_hg).E, 1 / 2⟩ : ℂ) (by norm_num) (0 : Idx 3 (S0.L 1) (S0.W 1))

/-- **Target 3** at `S0`, `κ_*`, `(τ, D) = (1/10, 1)`: the step pin `BAMADecol 3` applied to the step chain `baMANetLoc ∘ baLocSCFixed_of_ML`
(probe `:286`, with the merged `unMLOutBA_three`). -/
example := baMADecol 3 (baMANetLoc 3 (baLocSCFixed_of_ML 3 unMLOutBA_three)) le_rfl (1 / 6) (1 / 10) S0 S0_adm
  (clsκ 4 MADecolQUE_hg) (1 / 10) 1 (clsκ_pos 4 MADecolQUE_hg) (by norm_num) (by norm_num)

/-- **Target 4** at `S0`, `κ_*`, `(τ, D) = (1/10, 1)`: `BAEnd_decolL 3`, unconditional, and `baEnd_decolL 3` from the flow output. -/
example := baEnd_decolL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (1 / 10) 1
  (clsκ_pos 4 MADecolQUE_hg) (by norm_num) (by norm_num)

example := baEnd_decolL 3 unMLOutBA_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (1 / 10) 1
  (clsκ_pos 4 MADecolQUE_hg) (by norm_num) (by norm_num)

/-- **Targets 5b, 5c** at `S0` (`κ_*`, `ε₀ = 1/30`): the domain is nonempty (`E_*` is in the bulk at every `n`, so the eventual domain
statement has a witness) and the row differences hold with some `C > 0` at `n = 0`, `z = E_* + i/2`. -/
example : (∃ n : ℕ, BAendDom S0 (clsκ 4 MADecolQUE_hg) (1 / 6 * (1 / 10 - 1 / 30)) n
    ((((fp 4 MADecolQUE_hg).E : ℝ) : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ a b b' : Zd 3 (S0.L 0),
      ‖BAprof S0 0 (⟨(fp 4 MADecolQUE_hg).E, 1 / 2⟩ : ℂ) true false a b - BAprof S0 0 (⟨(fp 4 MADecolQUE_hg).E, 1 / 2⟩ : ℂ) true false a b'‖ ≤
        C * (S0.lam 0 ^ 2)⁻¹ / ((S0.W 0 : ℕ) : ℝ) ^ 3 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨n, hn⟩ := ((MADecolQUE_domain S0 S0_adm (κ := clsκ 4 MADecolQUE_hg) (ε₀ := 1 / 30) (by norm_num)
      (by norm_num)).and S0_bulk).exists
    exact ⟨n, hn.1 _ hn.2⟩
  · obtain ⟨C, hC, h⟩ := MADecolQUE_rowDiff 3 le_rfl (1 / 10) (clsκ 4 MADecolQUE_hg) (by norm_num) (clsκ_pos 4 MADecolQUE_hg)
    have hlam : 0 < S0.lam 0 ∧ S0.lam 0 ≤ (1 / 10 : ℝ)⁻¹ :=
      ⟨(fp 4 MADecolQUE_hg).g0_pos, by
        change (fp 4 MADecolQUE_hg).g0 ≤ (1 / 10 : ℝ)⁻¹
        have := (fp 4 MADecolQUE_hg).g0_le
        norm_num
        linarith⟩
    exact ⟨C, hC, fun a b b' => (h S0 0 hlam.1 hlam.2 (⟨(fp 4 MADecolQUE_hg).E, 1 / 2⟩ : ℂ) (by norm_num) (by norm_num)
      (cls_bulk 4 (by norm_num) MADecolQUE_hg) a b b').1⟩

/-- **Targets 6, 7** at `S0`, `κ_*`, `E_*`, `(ε₀, c) = (1/30, 1/60)` (`baQueFixed`, with the private generic `que2Bad_sub` inside): at some `n`
(eventually in the domain, the window `(eq:WO)` and the bulk) every hypothesis of `baQueFixed` holds with `ε = qdBoundExp` (the
expectation half, from M2's `baEnd_QDiffL_three`) and `K = C λ⁻² W^{-d}` (from `baThetaDiff`), and both Markov bounds follow. -/
example : ∃ n : ℕ, ∃ ε K : ℝ, 0 < etaQ S0 n (1 / 30) ∧
    (∀ a b : Zd 3 (S0.L n),
      ‖(∫ ω, avg2 S0 n (fun x y => ((‖BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω x y‖ ^ 2 : ℝ) : ℂ))
            a b ∂(Sizes.seqP (S0.withLam 0))) -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true false a b‖ ≤ ε ∧
      ‖(∫ ω, avg2 S0 n (fun x y => BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω x y *
            BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω y x) a b ∂(Sizes.seqP (S0.withLam 0))) -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true true a b‖ ≤ ε) ∧
    (∀ a b b' : Zd 3 (S0.L n),
      ‖BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true false a b -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true false a b'‖ ≤ K ∧
        ‖BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true true a b -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true true a b'‖ ≤ K) ∧
    (∀ a : Zd 3 (S0.L n),
      Sizes.seqP (S0.withLam 0) {ω | queBadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60) (fp 4 MADecolQUE_hg).E a
          (S0.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz S0 n ^ 2 * etaQ S0 n (1 / 30) ^ 2 * (4 * (K + ε)) / ((S0.W n : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))))) ∧
    (∀ A : Finset (Zd 3 (S0.L n)), A.Nonempty →
      Sizes.seqP (S0.withLam 0) {ω | que2BadMat 3 (S0.L n) (S0.W n) (S0.lam n) (1 / 30) (1 / 60) (fp 4 MADecolQUE_hg).E A
          (S0.seqHBA n ω)} ≤
        ENNReal.ofReal (4 * Nsz S0 n ^ 2 * etaQ S0 n (1 / 30) ^ 2 * (4 * (K + ε)) / ((S0.W n : ℕ) : ℝ) ^ (-(2 * (1 / 60 : ℝ))))) := by
  obtain ⟨C, hC, hrow⟩ := MADecolQUE_rowDiff 3 le_rfl (1 / 10) (clsκ 4 MADecolQUE_hg) (by norm_num) (clsκ_pos 4 MADecolQUE_hg)
  have hQD := baEnd_QDiffL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (1 / 6 * (1 / 10 - 1 / 30)) (1 / 600) 1
    (clsκ_pos 4 MADecolQUE_hg) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨n, ⟨hQn, hdomn⟩, hWOn, hbulk⟩ := ((hQD.and (MADecolQUE_domain S0 S0_adm (κ := clsκ 4 MADecolQUE_hg) (ε₀ := 1 / 30)
    (by norm_num) (by norm_num))).and (S0_adm.2.2.2.2.and S0_bulk)).exists
  have hD := hdomn _ hbulk
  have him : ((((fp 4 MADecolQUE_hg).E : ℝ) : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I).im = etaQ S0 n (1 / 30) := by simp
  have hη : 0 < etaQ S0 n (1 / 30) := by
    have h0 := hD.2.1
    rw [him] at h0
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (Nsz_pos S0 n) _) h0
  have hWpos : (0 : ℝ) < ((S0.W n : ℕ) : ℝ) := by exact_mod_cast S0.W_pos n
  have hlam : 0 < S0.lam n := lt_of_lt_of_le (Real.rpow_pos_of_pos hWpos _) hWOn.1
  have hK := hrow S0 n hlam hWOn.2 _ (by rw [him]; exact hη) hD.2.2 hD.1
  have hQ' : ∀ a b : Zd 3 (S0.L n),
      ‖(∫ ω, avg2 S0 n (fun x y => ((‖BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω x y‖ ^ 2 : ℝ) : ℂ))
            a b ∂(Sizes.seqP (S0.withLam 0))) -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true false a b‖ ≤
        qdBoundExp S0 n (1 / 600) (etaQ S0 n (1 / 30)) ∧
      ‖(∫ ω, avg2 S0 n (fun x y => BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω x y *
            BAGz S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) ω y x) a b ∂(Sizes.seqP (S0.withLam 0))) -
          BAprof S0 n (((fp 4 MADecolQUE_hg).E : ℂ) + (etaQ S0 n (1 / 30) : ℂ) * Complex.I) true true a b‖ ≤
        qdBoundExp S0 n (1 / 600) (etaQ S0 n (1 / 30)) := by
    intro a b
    have h := hQn.2 _ hD a b
    rwa [him] at h
  have hKK := fun a b b' => hK a b b'
  exact ⟨n, qdBoundExp S0 n (1 / 600) (etaQ S0 n (1 / 30)), C * (S0.lam n ^ 2)⁻¹ / ((S0.W n : ℕ) : ℝ) ^ 3, hη, hQ', hKK,
    baQueFixed S0 n (1 / 30) (1 / 60) _ _ _ _ rfl hη hQ' hKK⟩

/-- **Target 8** at `S0`, `κ_*`, `(ε₀, c, τ) = (1/30, 1/60, 1/300)` (exponent `-1/300 < 0`, the bound is `< 1`; not the merged `τ = 1/100` of
`inst_BAEnd_QUEL`): `BAEnd_QUEL 3`, unconditional; the step pin `baMAQUE 3` at the step chain `baMANetQD ∘ baQDiffFixed_of_ML`; `baEnd_QUEL 3`. -/
example := baEnd_QUEL_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example := baMAQUE 3 (baMANetQD 3 (baQDiffFixed_of_ML 3 unMLOutBA_three)) le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg)
  (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  (by norm_num)

example := baEnd_QUEL 3 unMLOutBA_three le_rfl (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30)
  (1 / 60) (1 / 300) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Target 8, non-vacuity**: the bound `queBound W 𝔡 ε₀ c τ` at `(1/10, 1/30, 1/60, 1/300)` is `W^{-1/300} < 1` for every `W > 1`. -/
example (W : ℕ) (hW : 1 < W) : queBound W (1 / 10) (1 / 30) (1 / 60) (1 / 300) < 1 := by
  unfold queBound
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
  refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hW) ?_
  norm_num

/-- **Target 9** at `S0`, `κ_*`, `(ε₀, c, τ) = (1/30, 1/60, 1/300)`: `UNQueBAAt 3`, unconditional (N2's `d = 3` input); from the flow output
(`unQueBAAt_of_ML`); the core at `baEnd_QUEL_three`. -/
example := unQueBAAt_three (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300)
  (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example := unQueBAAt_of_ML 3 le_rfl unMLOutBA_three (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg)
  (1 / 30) (1 / 60) (1 / 300) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example := unQueBAAt_of_QUEL 3 le_rfl baEnd_QUEL_three (1 / 6) (1 / 10) S0 S0_adm (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg)
  (1 / 30) (1 / 60) (1 / 300) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The merged `∀ d` text** (the statement of `UNQueBA_of_BAEnd_QUEL`, `UNPins.lean:357`) as one line from the core and P2 (`d > 3` forms
are Jun decision B's open pins, a hypothesis of this example), read at `d = 3`, `S0`. -/
example (h : ∀ d : ℕ, BAEnd_QUEL d) : UNQueBA := UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QUEL d hd (h d)

example (h : ∀ d : ℕ, BAEnd_QUEL d) : True := by
  have _ := (UNQueBA_iff_at.1 (UNQueBA_iff_at.2 fun d hd => unQueBAAt_of_QUEL d hd (h d))) 3 le_rfl (1 / 6) (1 / 10) S0 S0_adm
    (clsκ 4 MADecolQUE_hg) (clsκ_pos 4 MADecolQUE_hg) (1 / 30) (1 / 60) (1 / 300) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  trivial

end Inst

end RBM.BA

end
