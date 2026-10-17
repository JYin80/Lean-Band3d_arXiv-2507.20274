/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.BAExp14cB
import RBM3D.Graph.BAExp14dB

/-!
# The joined-graph bound, the leaf statement `BAG5LeafPrec` proved, and `BAExp14bS3`

Paper: Subappendix B.1: (B.5) `eq;I42inG`, (B.7) `Gammamuxy`, (B.8) `eq:sizeGammamu_E`;
Definition B.5 (`def scalingBA`) with (B.16) `eq_defsize_BA`; and the claim "`Γ ≺ size(Γ)` for any
normal graph" after (7.18) `eq:estSpm-W` in Subsection 7.1.  This is the BA counterpart of the band
file `Graph/LWExpTerm6.lean` (Sections 1-4: `LwGraphPrecJoin`, `lwExpTerm6_pathwise`,
`lwExpTerm6_arith`, `lwGraphPrecJoin_holds`) and of the one-line chain `lwExpG5'_holds`.

## Contents (namespace `RBM.BA`; private helpers carry the stem `BAExp14e_`)

1. The statement `BAGraphPrecJoin`.
2. The kernel bounds of the rescaled data `D'_t` (`BAExp14d_dataT`): `S' = svarF(0)`,
   `S⁺' = lift(ω_t)`, `M`, `g₀Ψ`.
3. The pathwise bound of a normal packed graph with `n_M = 0` (`baClaimSize` at `D'_t`).
4. `baGraphPrecJoin_holds`: entry event, arithmetic `lwExpTerm6_arith`, `≺ → 𝔼`.
5. `baG5LeafPrec_of`, `baG5LeafPrec_holds`: the case split `n_M = 0` (`BAGraphPrecJoin`) /
   `n_M = 1` (`BAG5LeafPrec1`, `Graph/BAExp14dB.lean`).
6. `baExp14bS3_holds`: the proof of `BAExp14bS3` through `baExp14bS3_of_leaf`
   (`Graph/BAExp14cB.lean`).
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false

open private BASizeClaim_theta_decay from RBM3D.Graph.BASizeClaim
open private BAVocab_val_of_factor BAVocab_val_of_not from RBM3D.Graph.BAVocab
open private BAExp14d_svar0 from RBM3D.Graph.BAExp14d
open private BAExp14d_entry_whp from RBM3D.Graph.BAExp14dB

open MeasureTheory Filter Matrix

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes RBM.Graph

/-! ## 1. The statement -/

/-- **(B.7) `Gammamuxy` for a joined graph** (as `LwGraphPrecJoin` in `Graph/LWExpTerm6.lean`): for a normal packed BA graph with `n_M = 0` (every vertex in a molecule of an external vertex),
`‖𝔼 Γ_{xy}‖ ≺ t^{n_W} η_t⁻¹ B^{ord/2}` at every pair `(x, y)`, from the entrywise law alone.  The data are those of the leaf statement
`BAG5LeafPrec` (`BAExp14a_slc`, `(baFMz sz z).m n`). -/
def BAGraphPrecJoin (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ ε 𝔡 : ℝ, 0 < κ → 0 < ε → 0 < 𝔡 → ∀ (𝔠 : ℝ) (sz : Sizes d) (z : ℕ → ℂ), BAFlow sz κ ε 𝔠 𝔡 z →
    ∀ t : ℕ → ℝ, (∀ n, 0 ≤ t n) → (∀ n, t n ≤ BAflowT0 sz z n) →
      STLocalEntrygL (baFMz sz z) (Sizes.seqP (sz.withLam 0)) t → ∀ P : BAPGraph (Fin 2), P.g.Normal → P.g.nM = 0 →
        PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
          (fun n p _ => ‖∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
            (BAExp14a_slc sz n ω)) ![p.1, p.2] ∂(Sizes.seqP (sz.withLam 0))‖)
          (fun n _ _ => (t n) ^ P.g.nW * ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((P.scalingOrder : ℝ) / 2))

/-! ## 2. The kernel bounds of the rescaled data -/

section Kernels

/-- **The kernel constants of `D'_t`** (the band's `lwExpTerm3_Sp_decay` in `Graph/LWExpTerm3.lean`, in the rescaled frame of `Graph/BAExp14d.lean`: `S = t S'`, `S⁺ = t S⁺'`
by `BAExp14d_val_scale`, so no `t` is carried by the constants): `S' = svarF(0)` and `S⁺' = lift(ω_t)`, `ω_t = Θ_t^{(+,+)}`, have entries
`≤ K₀ W^{-d}` and row and column sums `≤ K₁`, `M` and `g₀ Ψ` entries, row and column sums `≤ Kd`; the constants depend on `(d, Λ, κ)` only,
uniformly in `0 ≤ t < 1`, `L ≥ 3`, `W`, `E`, `0 < g₀ ≤ Λ`.  The decay of `ω_t` is `BASizeClaim_theta_decay` (`prop:ThfadC_short`). -/
private theorem BAExp14e_kernels (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ ω : Ω d L W,
          LWKBound (BAExp14d_dataT d L W g0 E t m ω).S (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
          LWKBound (BAExp14d_dataT d L W g0 E t m ω).Sp (K₀ * ((W : ℝ) ^ d)⁻¹) K₁ ∧
          LWKBound (BAExp14d_dataT d L W g0 E t m ω).M Kd Kd ∧
          LWKBound (BAExp14d_dataT d L W g0 E t m ω).gPsi Kd Kd := by
  obtain ⟨_K₀, _K₁, Kd, -, -, hKd, hK⟩ := baKBound_E d hd Λ κ hΛ hκ
  have hd0 : 0 < d := by omega
  have hC5 := BAp5s_C_pos d Λ κ hd0 hΛ hκ
  have hc0 := BAp5s_rate_pos d Λ κ hd0 hΛ hκ
  set Cθ : ℝ := (1 + Λ ^ 2) * BAp5s_C d Λ κ with hCθ
  have hCθ0 : 0 < Cθ := by positivity
  set C : ℝ := Cθ + 1 with hCdef
  set c : ℝ := BAp5s_rate d Λ κ with hcdef
  have hC1 : 1 ≤ C := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hE : 0 < expC (d - 2) c := by unfold expC; positivity
  refine ⟨C, C * expC (d - 2) c, Kd, by linarith, by positivity, hKd, ?_⟩
  intro L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 ω
  obtain ⟨-, -, hM', hP'⟩ := hK L W hL g0 E t m hg hgΛ hr ht0 ht1
  have hWd : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hSd : ∀ x y, ‖(BAExp14d_dataT d L W g0 E t m ω).S x y‖ ≤
      C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    change ‖((svarF d L W 0 x y : ℝ) : ℂ)‖ ≤ _
    rw [BAExp14d_svar0]
    by_cases h : (split d L W x).1 = (split d L W y).1
    · have h0 : (lwBdist d L W x y : ℝ) = 0 := by simp [lwBdist, h]
      rw [h0]
      simp only [h, ite_true, mul_one, mul_zero, neg_zero, Real.exp_zero, norm_inv, norm_pow, Complex.norm_natCast]
      nlinarith
    · simp only [h, ite_false, mul_zero, norm_zero]
      positivity
  have hSpd : ∀ x y, ‖(BAExp14d_dataT d L W g0 E t m ω).Sp x y‖ ≤
      C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
    intro x y
    change ‖lwLift d L W (BATheta d L g0 E m t true true) x y‖ ≤ _
    have hθ := BASizeClaim_theta_decay hL hd Λ g0 κ E t m hΛ hg hgΛ hκ hr ht0 ht1 (split d L W x).1 (split d L W y).1
    have e : ‖lwLift d L W (BATheta d L g0 E m t true true) x y‖ =
        ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖ := by
      simp [lwLift, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    rw [e]
    calc ((W : ℝ) ^ d)⁻¹ * ‖BATheta d L g0 E m t true true (split d L W x).1 (split d L W y).1‖
        ≤ ((W : ℝ) ^ d)⁻¹ * (Cθ * Real.exp (-(c * (zdistD d L ((split d L W x).1 - (split d L W y).1) : ℝ)))) :=
          mul_le_mul_of_nonneg_left hθ hWd
      _ = Cθ * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by unfold lwBdist; ring
      _ ≤ C * ((W : ℝ) ^ d)⁻¹ * Real.exp (-(c * (lwBdist d L W x y : ℝ))) := by
          gcongr
          linarith
  exact ⟨lwKBound_of_decay hd hC0 hc0 hSd, lwKBound_of_decay hd hC0 hc0 hSpd, hM', hP'⟩

end Kernels

/-! ## 3. The pathwise bound of a graph with `n_M = 0` -/

section Pathwise

/-- **The pathwise bound of a normal packed graph without internal molecule at `D'_t`** (the claim `Γ ≺ size(Γ)` of Subsection 7.1, with the BA size of Definition B.5; as
`lwExpTerm6_pathwise` in `Graph/LWExpTerm6.lean`): on the entry event `‖(G - M)_{xy}‖ ≤ Ψ`,
`|Γ_{xy}| ≤ C_Γ Ψ^{n_S} (W^{-d})^{n_W - n_A}` at the rescaled data, `C_Γ = Γ.sizeConst K₀ K₁ Kd` (`(L^d)^{n_M} = 1`).  No `ξ`, no `GtoAG`. -/
private theorem BAExp14e_pathwise (d : ℕ) (hd : 3 ≤ d) (Λ κ : ℝ) (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ K₀ K₁ Kd : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ 0 ≤ Kd ∧
      ∀ (L W : ℕ) [NeZero L] [NeZero W], 3 ≤ L → ∀ (g0 E t : ℝ) (m : ℂ), 0 < g0 → g0 ≤ Λ →
        BAReal d L g0 κ E m → 0 ≤ t → t < 1 → ∀ (ω : Ω d L W) (P : BAPGraph (Fin 2)), P.g.Normal → P.g.nM = 0 →
          ∀ Ψ : ℝ, 0 ≤ Ψ →
            (∀ x y, ‖(BAExp14d_dataT d L W g0 E t m ω).G x y - (BAExp14d_dataT d L W g0 E t m ω).M x y‖ ≤ Ψ) →
            ∀ ℓ : Fin 2 → Idx d L W,
              ‖P.val (BAExp14d_dataT d L W g0 E t m ω) ℓ‖ ≤
                P.g.sizeConst K₀ K₁ Kd * (Ψ ^ P.g.nS * (((W : ℝ) ^ d)⁻¹) ^ (P.g.nW - P.g.nA)) := by
  obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hK⟩ := BAExp14e_kernels d hd Λ κ hΛ hκ
  refine ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, ?_⟩
  intro L W _ _ hL g0 E t m hg hgΛ hr ht0 ht1 ω P hN hnM Ψ hΨ hG ℓ
  obtain ⟨hS, hSp, hM, hP⟩ := hK L W hL g0 E t m hg hgΛ hr ht0 ht1 ω
  have hsc : 0 ≤ P.g.sizeConst K₀ K₁ Kd := by unfold BAGraph.sizeConst; positivity
  have hcnt := P.g.counters_le hN.1
  have hkW : 0 ≤ (((W : ℝ) ^ d)⁻¹) ^ (P.g.nW - P.g.nA) := by positivity
  by_cases hf : ∃ ℓ' : P.E' → Idx d L W, ℓ = ℓ' ∘ P.ext
  swap
  · rw [BAVocab_val_of_not P _ hf, norm_zero]
    exact mul_nonneg hsc (mul_nonneg (pow_nonneg hΨ _) hkW)
  obtain ⟨ℓ', hℓ'⟩ := hf
  rw [BAVocab_val_of_factor P _ hℓ']
  refine (baClaimSize P.g hN _ hG hS hSp hM hP ℓ').trans (le_of_eq ?_)
  have hnA : P.g.nA ≤ P.g.nW := by have := hcnt.1; have := hcnt.2; omega
  have hW0 : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne W)
  have hexp : (-(d : ℤ) * ((P.g.nW : ℤ) - P.g.nA)) = -((d * (P.g.nW - P.g.nA) : ℕ) : ℤ) := by
    have : ((P.g.nW : ℤ) - P.g.nA) = ((P.g.nW - P.g.nA : ℕ) : ℤ) := by omega
    rw [this]; push_cast; ring
  unfold BAGraph.scalingSize Counters.scalingSize BAGraph.counters
  simp only [hnM, pow_zero, one_mul]
  rw [hexp, _root_.zpow_neg, zpow_natCast, pow_mul, inv_pow]

end Pathwise

/-! ## 4. (B.7) `Gammamuxy` for a joined graph -/

/-- **`baGraphPrecJoin_holds`** (as `lwGraphPrecJoin_holds` in `Graph/LWExpTerm6.lean`, with the BA ingredients):
`X = (t^{n_W})⁻¹ P_{xy}` (`= P_{xy}` at `D'_t` when `t^{n_W} ≠ 0`, by `BAExp14d_val_scale`; `0` otherwise); the polynomial envelope `BAExp14c_val_env` and the floor
`BAExp14c_floor` (`Graph/BAExp14c.lean`); on the entry event of `STLocalEntrygL` (`BAExp14d_entry_whp`) the pathwise bound `BAExp14e_pathwise` with
`Ψ = N^{τ'} B^{1/2}`, `W^{-d} ≤ (𝔡⁻² + 1) B` (`BAExp14a_Wd_le`), and the arithmetic `lwExpTerm6_arith`; then `≺ → 𝔼`
(`BAExp14a_prec_integral`, `BAExp14a_det_iff`).  Only `STLocalEntrygL` of the five Step 1/2 inputs is used, and only it appears in the statement. -/
theorem baGraphPrecJoin_holds (d : ℕ) : BAGraphPrecJoin d := by
  intro hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE P hN hnM
  classical
  obtain ⟨-, -, hsz, -, hWO⟩ := hflow.1
  have hsz' : Tendsto sz.size atTop atTop := Sizes.tendsto_size sz hsz
  have ht1 : ∀ n, t n < 1 := fun n => (ba_G_data hκ sz hflow n (ht0 n) (htT n)).1
  have hr : ∀ n, BAReal d (sz.L n) (BAflowLam0 sz z n) κ (BAflowEs sz z n) ((baFMz sz z).m n) :=
    fun n => BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨K₀, K₁, Kd, hK₀, hK₁, hKd, hpath⟩ := BAExp14e_pathwise d hd 𝔡⁻¹ κ (inv_pos.2 h𝔡) hκ
  have hcnt := P.g.counters_le hN.1
  have hnAW : P.g.nA ≤ P.g.nW := by have := hcnt.1; have := hcnt.2; omega
  set k : ℕ := P.g.nW - P.g.nA with hk
  set o : ℤ := P.scalingOrder with ho
  have hoR : (o : ℝ) = (P.g.nS : ℝ) + 2 * (k : ℝ) := by
    have : o = (P.g.nS : ℤ) + 2 * ((k : ℕ) : ℤ) := by
      rw [ho, hk]
      unfold BAPGraph.scalingOrder BAPGraph.counters BAGraph.counters ord
      simp only
      omega
    rw [this]; push_cast; ring
  -- the random statement
  set X : ∀ n, (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n)) → sz.SeqΩ → ℂ := fun n v ω =>
    (((t n) ^ P.g.nW : ℝ)⁻¹ : ℝ) * P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] with hX
  have hXeq : ∀ n v ω, (t n) ^ P.g.nW ≠ 0 → X n v ω =
      P.val (BAExp14d_dataT d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n) ((baFMz sz z).m n)
        (BAExp14a_slc sz n ω)) ![v.1, v.2] := by
    intro n v ω h
    simp only [hX]
    rw [BAExp14d_val_scale d (sz.L n) (sz.W n) (sz.three_le_L n) _ κ _ (t n) _ (hr n) (ht0 n) (ht1 n)
      (BAExp14a_slc sz n ω) P ![v.1, v.2], Complex.ofReal_inv, Complex.ofReal_pow, ← mul_assoc,
      inv_mul_cancel₀ (by exact_mod_cast h), one_mul]
  have hX0 : ∀ n v ω, (t n) ^ P.g.nW = 0 → X n v ω = 0 := by
    intro n v ω h
    simp only [hX, h, _root_.inv_zero, Complex.ofReal_zero, zero_mul]
  -- the polynomial envelope
  obtain ⟨Kenv, henv'⟩ := BAExp14c_val_env d hd κ ε 𝔠 𝔡 sz z hκ hflow P
  have henv : ∀ᶠ n in atTop, ∀ v ω, ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
    filter_upwards [henv'] with n hn v ω
    have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
    by_cases h : (t n) ^ P.g.nW = 0
    · rw [hX0 n v ω h, norm_zero]
      exact Real.rpow_nonneg hN0.le _
    · have hpos : 0 < (t n) ^ P.g.nW := lt_of_le_of_ne (pow_nonneg (ht0 n) _) (Ne.symm h)
      have h1 := hn (t n) (ht0 n) (htT n) ω v.1 v.2
      have h2 := BAExp14d_val_scale d (sz.L n) (sz.W n) (sz.three_le_L n) _ κ _ (t n) _ (hr n) (ht0 n) (ht1 n)
        (BAExp14a_slc sz n ω) P ![v.1, v.2]
      rw [hXeq n v ω h]
      rw [h2, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (ht0 n)] at h1
      calc _ ≤ ((sz.size n : ℕ) : ℝ) ^ Kenv := by
            refine le_of_mul_le_mul_left ?_ hpos
            linarith
        _ = _ := rfl
  have hfloor : ∀ᶠ n in atTop, ∀ v : Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n),
      ((sz.size n : ℕ) : ℝ) ^ (-(((|o| : ℤ) : ℝ) / 2)) ≤
        ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2) := by
    filter_upwards [BAExp14a_eventual_scalars hκ hε h𝔡 hflow ht0 htT] with n hsc v
    obtain ⟨-, h4, -, hB2, -⟩ := hsc
    exact BAExp14c_floor hκ hflow n (ht0 n) (htT n) (by linarith) hB2 o
  have hprecX : PrecL sz (Sizes.seqP (sz.withLam 0)) (U := fun n => Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n))
      (fun n v ω => ‖X n v ω‖)
      (fun n _ _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) := by
    refine StochDomAt.of_highProbAt_add_rpow_neg (P := Sizes.seqP (sz.withLam 0)) (size := sz.size) hsz'
      (b := ((|o| : ℤ) : ℝ) / 2) ?_ ?_
    · refine HighProbAt.of_eventually_univ ?_
      filter_upwards [hfloor] with n hn ω v
      exact hn v
    · intro τ hτ D hD
      set τ' : ℝ := τ / (2 * ((P.g.nS : ℝ) + 1)) with hτ'def
      have hτ'0 : 0 < τ' := by positivity
      have hτ' : τ' * (P.g.nS : ℝ) ≤ τ / 2 := by
        rw [hτ'def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [(Nat.cast_nonneg P.g.nS : (0 : ℝ) ≤ P.g.nS)]
      have hE₁ := BAExp14d_entry_whp ht1 hE hτ'0
      refine HighProbAt.mono hE₁ ?_
      set Kp : ℝ := P.g.sizeConst K₀ K₁ Kd with hKp
      have hτ2 : 0 < τ / 2 := by positivity
      have hKp0 : 0 ≤ Kp := by rw [hKp]; unfold BAGraph.sizeConst; positivity
      have hev1 : ∀ᶠ n in atTop, Kp * ((𝔡⁻¹) ^ 2 + 1) ^ k ≤ ((sz.size n : ℕ) : ℝ) ^ (τ / 2) :=
        ((tendsto_rpow_atTop hτ2).comp hsz).eventually_ge_atTop _
      filter_upwards [BAExp14a_eventually hκ hε hflow htT, hWO, hev1] with n hgg hlamn hK1n
      intro ω hω1 v
      obtain ⟨-, -, hg, hgΛ⟩ := hgg
      have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
      have hN0 : (0 : ℝ) < ((sz.size n : ℕ) : ℝ) := by linarith
      have hB0 : 0 < sz.Bctl n (t n) := STBctl_pos sz n (ht1 n)
      have hη0 := BAExp14a_eta_pos hκ hflow n (ht0 n) (htT n)
      have hη1 := BAExp14c_eta_le_one hκ hflow n (ht0 n) (htT n)
      have hΨ0 : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n)) :=
        mul_nonneg (Real.rpow_nonneg hN0.le _) (Real.sqrt_nonneg _)
      have hlam0 : 0 < sz.lam n :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by exact_mod_cast sz.W_pos n) _) hlamn.1
      have hl2 : sz.lam n ^ 2 + 1 ≤ (𝔡⁻¹) ^ 2 + 1 := by
        have := pow_le_pow_left₀ hlam0.le hlamn.2 2
        linarith
      have hWinv : (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ ≤ ((𝔡⁻¹) ^ 2 + 1) * sz.Bctl n (t n) :=
        (BAExp14a_Wd_le (sz := sz) n (ht0 n) (ht1 n)).trans (mul_le_mul_of_nonneg_right hl2 hB0.le)
      change ‖X n v ω‖ ≤ ((sz.size n : ℕ) : ℝ) ^ τ * (((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2)) +
        ((sz.size n : ℕ) : ℝ) ^ (-D)
      have hDnn : 0 ≤ ((sz.size n : ℕ) : ℝ) ^ (-D) := Real.rpow_nonneg hN0.le _
      refine le_trans ?_ (le_add_of_nonneg_right hDnn)
      by_cases h : (t n) ^ P.g.nW = 0
      · rw [hX0 n v ω h, norm_zero]
        have hη' : 0 < (((baFMz sz z).eta n (t n)))⁻¹ := inv_pos.2 hη0
        have hBo : 0 ≤ sz.Bctl n (t n) ^ ((o : ℝ) / 2) := Real.rpow_nonneg hB0.le _
        positivity
      · rw [hXeq n v ω h]
        have hpt := hpath (sz.L n) (sz.W n) (sz.three_le_L n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
          ((baFMz sz z).m n) hg hgΛ (hr n) (ht0 n) (ht1 n) (BAExp14a_slc sz n ω) P hN hnM _ hΨ0 hω1 ![v.1, v.2]
        have harith := lwExpTerm6_arith (N := ((sz.size n : ℕ) : ℝ)) (B := sz.Bctl n (t n))
          (η := (baFMz sz z).eta n (t n)) (Wi := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹) (A := (𝔡⁻¹) ^ 2 + 1) (K := Kp)
          (τ := τ) (τ' := τ') (Ψ := ((sz.size n : ℕ) : ℝ) ^ τ' * Real.sqrt (sz.Bctl n (t n))) P.g.nS k hN1 hB0 hη0 hη1
          rfl hτ' (by positivity) hWinv hKp0 hK1n
        rw [← hoR] at harith
        exact hpt.trans harith
  have hint := BAExp14a_prec_integral (P := Sizes.seqP (sz.withLam 0)) hsz' X
    (fun n _ => ((baFMz sz z).eta n (t n))⁻¹ * (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))
    (Kf := ((|o| : ℤ) : ℝ) / 2) henv hfloor hprecX
  have hdet := (BAExp14a_det_iff hsz' _ _).1 hint
  refine (BAExp14a_det_iff hsz' _ _).2 fun τ hτ => ?_
  filter_upwards [hdet τ hτ] with n hn v
  have h1 := hn v
  have hval : ∀ ω : sz.SeqΩ, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] = (((t n) ^ P.g.nW : ℝ) : ℂ) * X n v ω := by
    intro ω
    by_cases h : (t n) ^ P.g.nW = 0
    · have hnW : P.g.nW ≠ 0 := by
        intro h0; rw [h0, pow_zero] at h; exact one_ne_zero h
      have ht : t n = 0 := (pow_eq_zero_iff hnW).1 h
      have h0 : P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
          ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] = 0 := by
        rw [ht]; exact BAExp14c_val_zero d sz z n _ P hnW _
      rw [h0, hX0 n v ω h]; simp
    · simp only [hX]
      rw [Complex.ofReal_inv, mul_inv_cancel_left₀ (by exact_mod_cast h)]
  have hI : ∫ ω, P.val (BAlwData d (sz.L n) (sz.W n) (BAflowLam0 sz z n) (BAflowEs sz z n) (t n)
      ((baFMz sz z).m n) (BAExp14a_slc sz n ω)) ![v.1, v.2] ∂(Sizes.seqP (sz.withLam 0)) =
      (((t n) ^ P.g.nW : ℝ) : ℂ) * ∫ ω, X n v ω ∂(Sizes.seqP (sz.withLam 0)) := by
    exact (integral_congr_ae (Eventually.of_forall hval)).trans (integral_const_mul _ _)
  rw [hI, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (ht0 n) _)]
  calc (t n) ^ P.g.nW * ‖∫ ω, X n v ω ∂(Sizes.seqP (sz.withLam 0))‖
      ≤ (t n) ^ P.g.nW * (((sz.size n : ℕ) : ℝ) ^ τ * (((baFMz sz z).eta n (t n))⁻¹ *
        (sz.Bctl n (t n)) ^ ((o : ℝ) / 2))) := mul_le_mul_of_nonneg_left h1 (pow_nonneg (ht0 n) _)
    _ = _ := by ring

/-! ## 5. The leaf statement, proved -/

/-- **The conditional form** (`baG5LeafPrec_of`, with `LP := BAG5LeafPrec` and `Q1 := BAG5LeafPrec1`): the joined
bound (the `n_M = 0` half, `BAGraphPrecJoin`) and the `n_M = 1` bound `BAG5LeafPrec1` give the leaf statement `BAG5LeafPrec`.  Proof: destructure
`BAG5LeafProps (fun _ _ => [P])` (`Normal`, `n_M ≤ 1`, ...); `n_M = 0` goes to the joined bound (of the five Step 1/2 premises only
`STLocalEntrygL` is used), `n_M = 1` to `BAG5LeafPrec1` (the pointwise `(Gammamuxy)` half for `BAG5Leaf` leaves). -/
theorem baG5LeafPrec_of : ∀ d : ℕ, BAGraphPrecJoin d → BAG5LeafPrec1 d → BAG5LeafPrec d := by
  intro d hJ hQ1 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT μ hE hA hLmax hLK hDec P hLP
  obtain ⟨hN, hnM1, -, -, -⟩ := hLP true true P (List.mem_singleton_self P)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hnM1 with h0 | h1
  · exact hJ hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE P hN h0
  · exact hQ1 hd κ ε 𝔡 hκ hε h𝔡 𝔠 sz z hflow t ht0 htT hE hA hLmax hLK hDec P hLP h1

/-- **Unconditionally** (`baG5LeafPrec_holds`): the leaf statement `BAG5LeafPrec` for every `d`, from `baGraphPrecJoin_holds` and `baG5LeafPrec1_holds`. -/
theorem baG5LeafPrec_holds : ∀ d : ℕ, BAG5LeafPrec d := fun d =>
  baG5LeafPrec_of d (baGraphPrecJoin_holds d) (baG5LeafPrec1_holds d)

/-! ## 6. The proof of `BAExp14bS3` -/

/-- **`baExp14bS3_holds`** (as `lwExpG5'_holds` in `Graph/LWExpTerm6.lean`): the statement `BAExp14bS3` (`Graph/BAExp14b.lean`, per family,
the five premises of `LWCutExpG`, no `BATwist*`) for every `d`, by the assembly `baExp14bS3_of_leaf` applied to the leaf statement `baG5LeafPrec_holds`. -/
theorem baExp14bS3_holds : ∀ d : ℕ, BAExp14bS3 d := fun d => baExp14bS3_of_leaf d (baG5LeafPrec_holds d)

end RBM.BA

end
