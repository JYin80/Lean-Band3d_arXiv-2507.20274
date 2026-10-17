/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Chain.NQEndFlowGen
import RBM3D.BA.KBound
import RBM3D.BA.KInduct
import RBM3D.BA.KSolve
import RBM3D.BA.KTreeRep
import RBM3D.BA.EMn2BA
import RBM3D.BA.GreenSchur

/-!
# U3-BA (a), file 2: the time modulus of `𝒦` at the BA family, every `k ≥ 2` (ticket T2507, row a)

Paper: arXiv:2507.20274, `ML:Kbound` (`(eq:bcal_k)`, proved at BA by stage K: `baKBoundAt_holds`, `BA/KBound.lean:85`) and the convolution tree equation
`(pro_dyncalK)` at `S = 1` (`BAKsol_isKLoopS`, `BA/KSolve.lean:606`, from `baKsolve`, `BA/KTreeRep.lean:1699`).  New leaf: no merged file is edited.  The check is
`docs/tickets/checks/T2507-check.lean` (pin `T2507_KLipBA`).

* `baKloop_lip` (= `T2507_KLipBA`; T2491 D2, family row 15 of T2505): `NQEndFlowGen_KLipFam` at the BA tuple
  `(BAFlow, baFMz, BAflowT0)`, every `k ≥ 2`: `‖𝒦^{(k)}_u - 𝒦^{(k)}_{u'}‖ ≤ N^{2k+2} |u - u'|` on `[0, t_n]`, `t_n ≤ t₀_n`, eventually.  It is the
  twin of `stKloop_lip` (`Induction/NQEndFlowLift.lean:581`, 250 lines): `∂_u 𝒦 = treeEqRhsS` on `[0,1)` (`BAKsol_isKLoopS`), the cut loops have lengths in
  `[2, k]` and `baKBoundAt_holds` (`τ = 1`, `Λ = 𝔡⁻¹`, constants depending on `(d, m, κ, 𝔡)` only) bounds them, the tree bound uses `|S_{ab}| ≤ 1` for
  `S = 1`, `(1 - u)⁻¹ ≤ 2N` for `u ≤ t₀` (`EMn2BA_one_sub_T0`), and the mean value theorem on `[0, t_n]`; `N^{2k+2}` absorbs `k² Cm² 4^k N^{k+3}` eventually
  (`2k + 2 > k + 3`).  `baKLip_two` (`BA/Step5KerBA.lean:476`, `k = 2` only) is not edited.

Private helpers carry the stem `KLipBA_`; the band privates (`nqLift_loopOf_eq`, `nqLift_treeEq_bound`, `nqLift_Bctl_le`, `NQEndFlowLift.lean:457-562`) are
copied at `S = 1` and the BA control.
-/

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory Filter

noncomputable section

namespace RBM.BA

open RBM RBM.Loop RBM.Path RBM.Gauss RBM.Gauss.Sizes

/-! ## 1. Private helpers (copies of the band privates at `S = 1`) -/

section Helpers

/-- A loop index of length `m` is `KLloopOf σ a` (`nqLift_loopOf_eq`, `NQEndFlowLift.lean:457`). -/
private theorem KLipBA_loopOf_eq {d L : ℕ} (J : LoopIdx (Zd d L)) (hJ : J.WF) {m : ℕ} (hm : J.length = m) :
    ∃ (σ : Fin m → Bool) (a : Fin m → Zd d L), J = KLloopOf d L σ a := by
  obtain ⟨σl, al⟩ := J
  have hal : al.length = m := hm
  subst hal
  have hJ' : σl.length = al.length := hJ
  refine ⟨fun i => σl.get (Fin.cast hJ'.symm i), al.get, ?_⟩
  refine LoopIdx.ext ?_ ?_
  · change σl = List.ofFn (fun i : Fin al.length => σl.get (Fin.cast hJ'.symm i))
    apply List.ext_getElem <;> simp [hJ']
  · change al = List.ofFn al.get
    exact (List.ofFn_get al).symm

/-- **The crude bound of `𝒦^{(m)}`** (`ML:Kbound`, `τ = 1`) as a statement about loop indices, with the constant uniform over `0 < g ≤ Λ` and the real-axis
data `BAReal d L g κ E mm`: `baKBoundAt_holds` and `KLipBA_loopOf_eq` (`nqLift_KLK_bound`, `NQEndFlowLift.lean:472`, at BA). -/
private theorem KLipBA_bound {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ (1 ≤ m → ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ → ∀ (E : ℝ) (mm : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E mm → ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ J : LoopIdx (Zd d L), J.WF → J.length = m →
        ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) mm)) (PropSpin mm) r J‖ ≤
          C * (L : ℝ) * (((W : ℝ) ^ d)⁻¹ * Bparam d L g r 0) ^ (m - 1)) := by
  by_cases hm : 1 ≤ m
  · obtain ⟨C, hC, H⟩ := baKBoundAt_holds d hd hΛ hκ m hm 1 one_pos
    refine ⟨C, hC, fun _ L hL W hW g hg hgΛ E mm hr r hr0 hr1 J hJ hJm => ?_⟩
    obtain ⟨σ, a, rfl⟩ := KLipBA_loopOf_eq J hJ hJm
    have h := H L hL W hW g hg hgΛ E mm hr r hr0 hr1 σ a
    rwa [Real.rpow_one] at h
  · exact ⟨1, one_pos, fun h => absurd h hm⟩

/-- **The tree-equation right side at `S = 1` is bounded by the product bound of its cut loops**: if every loop `J` of length `2 ≤ |J| ≤ n` has
`‖K J‖ ≤ C X^{|J|-1}`, then `‖treeEqRhsS 1 K I‖ ≤ W^d n² L^{2d} C² X^n` for `|I| = n` (the two cut loops of `(k, l)` have lengths `k + n - l + 1`,
`l - k + 1 ∈ [2, n]` with `(k + n - l) + (l - k) = n`; `|1_{ab}| ≤ 1`).  (`nqLift_treeEq_bound`, `NQEndFlowLift.lean:487`, with `SB` read as `1`.) -/
private theorem KLipBA_treeEq_bound {d L W : ℕ} [NeZero L] {K : LoopIdx (Zd d L) → ℂ} {I : LoopIdx (Zd d L)} {n : ℕ}
    (hI : I.WF) (hn : I.length = n) {X C : ℝ} (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hK : ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length → J.length ≤ n → ‖K J‖ ≤ C * X ^ (J.length - 1)) :
    ‖treeEqRhsS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) K I‖ ≤
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) := by
  have hcardZ : (Fintype.card (Zd d L) : ℝ) = (L : ℝ) ^ d := by
    rw [card_Zd]; push_cast; rfl
  have hterm : ∀ k ∈ Finset.Icc 1 I.length, ∀ l ∈ Finset.Ioc k I.length, ∀ a b : Zd d L,
      ‖K (I.cutGlueL k l a) * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * K (I.cutGlueR k l b)‖ ≤ C ^ 2 * X ^ n := by
    intro k hk l hl a b
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_Ioc] at hl
    have hlenL := LoopIdx.length_cutGlueL I a hk.1 hl.1 hl.2
    have hlenR := LoopIdx.length_cutGlueR I b hk.1 hl.1 hl.2
    have hwL := LoopIdx.wf_cutGlueL I a hI hk.1 hl.1 hl.2
    have hwR := LoopIdx.wf_cutGlueR I b hI hk.1 hl.1 hl.2
    have h1 := hK _ hwL (by rw [hlenL]; omega) (by rw [hlenL]; omega)
    have h2 := hK _ hwR (by rw [hlenR]; omega) (by rw [hlenR]; omega)
    have hS : ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b‖ ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have hX1 : 0 ≤ C * X ^ ((I.cutGlueL k l a).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    have hX2 : 0 ≤ C * X ^ ((I.cutGlueR k l b).length - 1) := mul_nonneg hC (pow_nonneg hX _)
    rw [norm_mul, norm_mul]
    calc ‖K (I.cutGlueL k l a)‖ * ‖(1 : Matrix (Zd d L) (Zd d L) ℂ) a b‖ * ‖K (I.cutGlueR k l b)‖
        ≤ (C * X ^ ((I.cutGlueL k l a).length - 1)) * 1 *
            (C * X ^ ((I.cutGlueR k l b).length - 1)) :=
          mul_le_mul (mul_le_mul h1 hS (norm_nonneg _) hX1) h2 (norm_nonneg _) (by positivity)
      _ = C ^ 2 * X ^ n := by
          rw [hlenL, hlenR]
          have hexp : (k + I.length - l + 1 - 1) + (l - k + 1 - 1) = n := by omega
          calc C * X ^ (k + I.length - l + 1 - 1) * 1 * (C * X ^ (l - k + 1 - 1))
              = C ^ 2 * (X ^ (k + I.length - l + 1 - 1) * X ^ (l - k + 1 - 1)) := by ring
            _ = C ^ 2 * X ^ n := by rw [← pow_add, hexp]
  have hrhs : (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d)) * (C ^ 2 * X ^ n) =
      (W : ℝ) ^ d * ((n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n)) := by ring
  rw [hrhs]
  unfold treeEqRhsS
  rw [norm_mul, norm_pow, Complex.norm_natCast]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        K (I.cutGlueL k l a) * (1 : Matrix (Zd d L) (Zd d L) ℂ) a b * K (I.cutGlueR k l b)‖ ≤
      ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun l hl => (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => hterm k hk l hl a b))))
  refine hsum.trans ?_
  have hT : 0 ≤ (L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)) := by positivity
  calc ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length, ∑ a : Zd d L, ∑ b : Zd d L,
        C ^ 2 * X ^ n
      ≤ ∑ k ∈ Finset.Icc 1 I.length, ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardZ, Nat.card_Ioc]
        have hkn : ((I.length - k : ℕ) : ℝ) ≤ n := by
          rw [← hn]; exact_mod_cast Nat.sub_le _ _
        calc ((I.length - k : ℕ) : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))
            ≤ (n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n))) :=
              mul_le_mul_of_nonneg_right hkn hT
          _ = _ := rfl
    _ = (n : ℝ) * ((n : ℝ) * ((L : ℝ) ^ d * ((L : ℝ) ^ d * (C ^ 2 * X ^ n)))) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hn]
        simp
    _ = (n : ℝ) * n * ((L : ℝ) ^ d * (L : ℝ) ^ d) * (C ^ 2 * X ^ n) := by ring

/-- `0 ≤ W^{-d} B_{r,0}(g) ≤ 2 M` for `r < 1` with `(1 - r)⁻¹ ≤ M` (`W^{-d} B_{r,0} ≤ W^{-d} 2 (1 - r)⁻¹`; `nqLift_Bctl_le`, `NQEndFlowLift.lean:553`, at the
coupling `g` of the BA datum). -/
private theorem KLipBA_X_le {d L W : ℕ} (hL : 1 ≤ L) (hW : 1 ≤ W) (g : ℝ) {r : ℝ} (hr : r < 1) {M : ℝ} (hM : (1 - r)⁻¹ ≤ M) :
    (((W : ℝ) ^ d)⁻¹ * Bparam d L g r 0) ≤ 2 * M := by
  have h1r : 0 < 1 - r := by linarith
  unfold Bparam
  rw [abs_of_pos h1r]
  have hL1 : (1 : ℝ) ≤ (L : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hL)
  have hW1 : (1 : ℝ) ≤ (W : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW)
  have hz : ((((0 : ℕ) : ℝ) + 1) ^ (d - 2)) = 1 := by simp
  have e1 : (g ^ 2 + (1 - r))⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ h1r (by nlinarith [sq_nonneg g])
  have e2 : ((L : ℝ) ^ d * (1 - r))⁻¹ ≤ (1 - r)⁻¹ := inv_anti₀ h1r (by nlinarith)
  have hWi : (((W : ℝ) ^ d))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hW1
  have hsum : (g ^ 2 + (1 - r))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - r))⁻¹ ≤ 2 * M := by
    rw [hz, inv_one, mul_one]; linarith
  have hnn : 0 ≤ (g ^ 2 + (1 - r))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - r))⁻¹ := by positivity
  calc (((W : ℝ) ^ d)⁻¹) * ((g ^ 2 + (1 - r))⁻¹ * ((((0 : ℕ) : ℝ) + 1) ^ (d - 2))⁻¹ + ((L : ℝ) ^ d * (1 - r))⁻¹)
      ≤ 1 * (2 * M) := mul_le_mul hWi hsum hnn zero_le_one
    _ = 2 * M := one_mul _

/-- `(1 - u)⁻¹ ≤ 2 N` for `u ≤ t₀_n`: `1 - u ≥ 1 - t₀ ≥ Im z_n / 2 ≥ N^{-1+ε} / 2` (`EMn2BA_one_sub_T0`), `N^{1-ε} ≤ N` (a copy of the private
`Step5KerBA_one_sub_inv`, `BA/Step5KerBA.lean:416`). -/
private theorem KLipBA_one_sub_inv {d : ℕ} {κ ε 𝔠 𝔡 : ℝ} (hκ : 0 < κ) (hε : 0 < ε) {sz : Sizes d} {z : ℕ → ℂ}
    (hflow : BAFlow sz κ ε 𝔠 𝔡 z) (n : ℕ) {u : ℝ} (hu : u ≤ BAflowT0 sz z n) :
    (1 - u)⁻¹ ≤ 2 * ((sz.size n : ℕ) : ℝ) := by
  have hN : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := by exact_mod_cast sz.one_le_size n
  have hz := EMn2BA_one_sub_T0 hκ sz hflow n
  have hNim : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) ≤ (z n).im := (hflow.2 n).2.1
  have hp : 0 < ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have h1 : ((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2 ≤ 1 - u := by linarith
  calc (1 - u)⁻¹ ≤ (((sz.size n : ℕ) : ℝ) ^ (-1 + ε) / 2)⁻¹ := inv_anti₀ (by positivity) h1
    _ = 2 * ((sz.size n : ℕ) : ℝ) ^ (-(-1 + ε)) := by
        rw [Real.rpow_neg (by linarith), inv_div, div_eq_mul_inv]
    _ ≤ 2 * ((sz.size n : ℕ) : ℝ) ^ (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by norm_num)
    _ = _ := by rw [Real.rpow_one]

/-- **The mean value step**: `∂_u K = treeEqRhsS S (K u) I` on `[0, 1)` and `‖treeEqRhsS S (K r) I‖ ≤ B` on `[0, T]`, `T < 1`, give
`‖K u I - K u' I‖ ≤ B |u - u'|` on `[0, T]` (the last step of `stKloop_lip`, `NQEndFlowLift.lean:675-690`). -/
private theorem KLipBA_mvt {d L W : ℕ} [NeZero L] {S : Matrix (Zd d L) (Zd d L) ℂ} {K : ℝ → LoopIdx (Zd d L) → ℂ} {T B : ℝ}
    (hT : T < 1) {I : LoopIdx (Zd d L)} (hI : I.WF) (h2 : 2 ≤ I.length)
    (hder : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ J : LoopIdx (Zd d L), J.WF → 2 ≤ J.length →
      HasDerivAt (fun s => K s J) (treeEqRhsS d L W S (K t) J) t)
    (hbound : ∀ r ∈ Set.Icc (0 : ℝ) T, ‖treeEqRhsS d L W S (K r) I‖ ≤ B)
    {u u' : ℝ} (hu0 : 0 ≤ u) (hut : u ≤ T) (hu'0 : 0 ≤ u') (hu't : u' ≤ T) :
    ‖K u I - K u' I‖ ≤ B * |u - u'| := by
  have hf : ∀ r ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun r => K r I) (treeEqRhsS d L W S (K r) I) (Set.Icc (0 : ℝ) T) r :=
    fun r hr => (hder r ⟨hr.1, hr.2.trans_lt hT⟩ I hI h2).hasDerivWithinAt
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f' := fun r => treeEqRhsS d L W S (K r) I) hf hbound (convex_Icc (0 : ℝ) T) ⟨hu'0, hu't⟩ ⟨hu0, hut⟩
  rw [Real.norm_eq_abs] at hmvt
  exact hmvt

end Helpers

/-! ## 2. Target 6: `baKloop_lip` -/

/-- **Target 6, `baKloop_lip`** (= `T2507_KLipBA`; T2491 D2, family row 15 of T2505): `NQEndFlowGen_KLipFam` at the BA tuple `(BAFlow, baFMz, BAflowT0)`, every `k ≥ 2`.
`κ` and `𝔡` are fixed before `n` (the constants `Cf m` of `baKBoundAt_holds` at `(d, m, 𝔡⁻¹, κ)` do not depend on `n`); the window `0 < g₀_n ≤ 𝔡⁻¹` is
`BAflow_lam0_window` (eventually); `∂_u 𝒦 = treeEqRhsS` on `[0, 1)` is `BAKsol_isKLoopS (baKsolve d)`; `(1 - u)⁻¹ ≤ 2N` for `u ≤ t_n ≤ t₀_n`
(`KLipBA_one_sub_inv`).  The chain `‖treeEqRhsS‖ ≤ k² Cm² 4^k N^{k+3} ≤ N^{k+4} ≤ N^{2k+2}` holds for `N ≥ max 1 (k² Cm² 4^k)` and `k ≥ 2`. -/
theorem baKloop_lip (d : ℕ) : NQEndFlowGen_KLipFam d (fun sz κ ε 𝔠 𝔡 z => BAFlow sz κ ε 𝔠 𝔡 z) (fun sz z => baFMz sz z)
    (fun sz z => BAflowT0 sz z) := by
  intro hd sz κ ε 𝔠 𝔡 z hκ hε hflow t ht k hk
  have hΛ : 0 < 𝔡⁻¹ := inv_pos.2 hflow.1.2.1
  choose Cf hCf0 hCf using fun m : ℕ => KLipBA_bound hd hΛ hκ m
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = ∑ m ∈ Finset.range (k + 1), Cf m := ⟨_, rfl⟩
  have hCm_ge : ∀ m ≤ k, Cf m ≤ Cm := fun m hm => by
    rw [hCm]
    exact Finset.single_le_sum (f := Cf) (fun i _ => (hCf0 i).le) (Finset.mem_range.2 (by omega))
  have hCm0 : 0 < Cm := lt_of_lt_of_le (hCf0 0) (hCm_ge 0 (Nat.zero_le k))
  filter_upwards [BAflow_lam0_window κ ε 𝔠 𝔡 sz z hflow,
    hflow.1.2.2.1.eventually_ge_atTop (max 1 ((k : ℝ) * k * Cm ^ 2 * 4 ^ k))] with n hlamn hNn
  intro u u' hu0 hut hu'0 hu't σ a
  have hN1 : (1 : ℝ) ≤ ((sz.size n : ℕ) : ℝ) := (le_max_left _ _).trans hNn
  have hNQ : (k : ℝ) * k * Cm ^ 2 * 4 ^ k ≤ ((sz.size n : ℕ) : ℝ) := (le_max_right _ _).trans hNn
  have hL3 : 3 ≤ sz.L n := sz.three_le_L n
  have hW1 : 1 ≤ sz.W n := sz.W_pos n
  have htn : t n < 1 := (ht n).trans_lt (EMn2BA_T0_lt_one hκ sz hflow n)
  have hr := BAflow_real κ ε 𝔠 𝔡 sz z hflow n
  obtain ⟨Kf, hKf⟩ : ∃ Kf : ℝ → LoopIdx (Zd d (sz.L n)) → ℂ, Kf = BAKsol d (sz.L n) (sz.W n)
      (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ) (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))
      (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)) := ⟨_, rfl⟩
  have hKL : IsKLoopS d (sz.L n) (sz.W n) (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)
      (PropSpin (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n))
      (BAMLoop d (sz.L n) (sz.W n) (BAMsigma d (sz.L n) (BAMB d (sz.L n) (BAflowLam0 sz z n) (BAflowEs sz z n : ℂ)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n)))) (Set.Ico (0 : ℝ) 1) Kf := by
    rw [hKf]; exact BAKsol_isKLoopS (baKsolve d) hΛ hκ hL3 (W := sz.W n) hlamn.1 hlamn.2 hr
  have hIWF : (KLloopOf d (sz.L n) σ a).WF := by simp [KLloopOf, LoopIdx.WF]
  have hIlen : (KLloopOf d (sz.L n) σ a).length = k := by simp [KLloopOf, LoopIdx.length]
  -- the counting facts
  have hsz : ((sz.size n : ℕ) : ℝ) = ((sz.W n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d := by
    simp [Sizes.size, mul_pow]
  have hWd1 : (1 : ℝ) ≤ ((sz.W n : ℕ) : ℝ) ^ d := one_le_pow₀ (by exact_mod_cast hW1)
  have hL1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ sz.L n)
  have hLd1 : (1 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := one_le_pow₀ hL1
  have hLdN : ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.size n : ℕ) : ℝ) := by
    rw [hsz]; nlinarith
  have hL2d : ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.L n : ℕ) : ℝ) ^ d := pow_le_pow_right₀ hL1 (by omega)
  have hcount : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
      ((sz.L n : ℕ) : ℝ) ^ 2 ≤ ((sz.size n : ℕ) : ℝ) ^ 3 := by
    have hLd0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) ^ d := by positivity
    have h1 : ((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) =
        ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d := by rw [hsz]; ring
    rw [h1]
    calc ((sz.size n : ℕ) : ℝ) * ((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ 2
        ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) := by
          gcongr
          exact hL2d.trans hLdN
      _ = ((sz.size n : ℕ) : ℝ) ^ 3 := by ring
  -- the derivative of `𝒦^{(k)}` is bounded by `N^{2k+2}` on `[0, t_n]`
  have hbound : ∀ r ∈ Set.Icc (0 : ℝ) (t n),
      ‖treeEqRhsS d (sz.L n) (sz.W n) (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (Kf r) (KLloopOf d (sz.L n) σ a)‖ ≤
        ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := by
    intro r hr0
    have hr1 : r < 1 := hr0.2.trans_lt htn
    set X : ℝ := (((sz.W n : ℕ) : ℝ) ^ d)⁻¹ * Bparam d (sz.L n) (BAflowLam0 sz z n) r 0 with hXdef
    have hX0 : 0 ≤ X := mul_nonneg (by positivity) (KLIndStepA_Bparam_nonneg r 0)
    have hXle : X ≤ 2 * (2 * ((sz.size n : ℕ) : ℝ)) :=
      KLipBA_X_le (by omega) hW1 _ hr1 (KLipBA_one_sub_inv hκ hε hflow n (hr0.2.trans (ht n)))
    have hKJ : ∀ J : LoopIdx (Zd d (sz.L n)), J.WF → 2 ≤ J.length → J.length ≤ k →
        ‖Kf r J‖ ≤ (Cm * ((sz.L n : ℕ) : ℝ)) * X ^ (J.length - 1) := by
      intro J hJ h2 hJk
      have h := hCf J.length (by omega) (sz.L n) hL3 (sz.W n) hW1 (BAflowLam0 sz z n) hlamn.1 hlamn.2 (BAflowEs sz z n)
        (BAmF sz (BAflowLam0 sz z) (BAflowEs sz z) n) hr r hr0.1 hr1 J hJ rfl
      rw [hKf]
      refine h.trans ?_
      have hL0 : (0 : ℝ) ≤ ((sz.L n : ℕ) : ℝ) := Nat.cast_nonneg _
      have hCle := hCm_ge J.length hJk
      have hXp : 0 ≤ X ^ (J.length - 1) := pow_nonneg hX0 _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hL0) hXp
    have h1 := KLipBA_treeEq_bound (W := sz.W n) hIWF hIlen (X := X) (C := Cm * ((sz.L n : ℕ) : ℝ)) (by positivity) hX0 hKJ
    have hXk : X ^ k ≤ (2 * (2 * ((sz.size n : ℕ) : ℝ))) ^ k := pow_le_pow_left₀ hX0 hXle k
    have h4 : (2 * (2 * ((sz.size n : ℕ) : ℝ))) ^ k = 4 ^ k * ((sz.size n : ℕ) : ℝ) ^ k := by
      rw [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num, mul_pow]
    calc ‖treeEqRhsS d (sz.L n) (sz.W n) (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ) (Kf r) (KLloopOf d (sz.L n) σ a)‖
        ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * X ^ k) := h1
      _ ≤ ((sz.W n : ℕ) : ℝ) ^ d * ((k : ℝ) * k * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d)) *
            ((Cm * ((sz.L n : ℕ) : ℝ)) ^ 2 * (4 ^ k * ((sz.size n : ℕ) : ℝ) ^ k)) := by
          rw [← h4]; gcongr
      _ = ((k : ℝ) * k * Cm ^ 2 * 4 ^ k) *
            (((sz.W n : ℕ) : ℝ) ^ d * (((sz.L n : ℕ) : ℝ) ^ d * ((sz.L n : ℕ) : ℝ) ^ d) *
              ((sz.L n : ℕ) : ℝ) ^ 2) * ((sz.size n : ℕ) : ℝ) ^ k := by
          rw [mul_pow]; ring
      _ ≤ ((sz.size n : ℕ) : ℝ) * ((sz.size n : ℕ) : ℝ) ^ 3 * ((sz.size n : ℕ) : ℝ) ^ k := by
          gcongr
      _ = ((sz.size n : ℕ) : ℝ) ^ (k + 4) := by ring
      _ ≤ ((sz.size n : ℕ) : ℝ) ^ (2 * k + 2) := pow_le_pow_right₀ hN1 (by omega)
  -- the mean value theorem on `[0, t_n]`
  have hgoal := KLipBA_mvt (S := (1 : Matrix (Zd d (sz.L n)) (Zd d (sz.L n)) ℂ)) (W := sz.W n) htn hIWF
    (by rw [hIlen]; exact hk) hKL.1 hbound hu0 hut hu'0 hu't
  rw [hKf] at hgoal
  exact hgoal

/-! ## 3. Compiled nonempty instance at `d = 3`

`sz0`, `zSeq`, `flow_sz0 : BAFlow sz0 (1/2) (1/10) (1/6) (1/10) zSeq` (`BA/FlowPins.lean:1214`), `k = 3`, `t ≡ 1/2 ≤ t₀_n` (`half_lt_t0`, `t₀ ≥ 2/3`). -/

end RBM.BA

end
