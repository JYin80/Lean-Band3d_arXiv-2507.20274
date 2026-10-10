/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.BA.KMolecule
import RBM3D.BA.KCactusCut
import RBM3D.BA.KTreeRep
import RBM3D.BA.KSolve
import RBM3D.Loop.KLIndStepB
import RBM3D.BA.Prop6Path
import RBM3D.BA.GreenSchur
import RBM3D.BA.KKernel

/-!
# Stage K, row K10: the base levels and the cut of `K^{(π)}` for the molecule induction

Ticket T2381 (design BA-DK, `docs/reports/T2360-design.md` §4 row K10, §1 row `KLInduct`, §5;
supervisor `docs/supervisor/2026-10-10-0350.md` C2, C4).  The BA twin of `Loop/KLInduct.lean`
§1-§6 (everything except the generic step §7, which K09b restates over abstract data).

1. The pins `BAKBoundAt` (verbatim: the probe pin `t/T2360:RBM3D/Probe/T2360Pins.lean:38-44`) and
   `BAKpiBoundAt` (the twin of `KLKpiBoundAt`, no `W`).
2. The base levels of `BAKsol`: `baKsol_one/two/three` (`𝒦^{(1)} = m(σ)`, `(Kn2sol)`, `(Kn3sol)`),
   through `BAKsol_isKLoopS`, `baK_unique` against the `baKsolve` witness (0350 C4) and `baTreeRep`
   at `n = 3`.
3. The bounds the induction uses at these levels: `baKBoundAt_one/two/three` (the shape of
   `BAKBoundAt`).
4. `baKpi_cut`: `K^{(π)}` at an innermost long edge `J ∈ π`: the outer `BAKpi` on `sigmaOut σ J`,
   the BA chord `tΘ^{(σ_i,σ_j)}` glued to the outer glue leaf (no `S^{(B)}`, no `Θ - 1 = ξ_J SΘ`),
   the inner molecule `Σ^{(∅)}` on `sigmaIn σ J` with the identity as the last leaf.
   `baKpi_cut_abs` states it over the abstract data of `IndStepAbs`, `baKpi_cut_S` in the shape of
   `KLKpi_cut` (kernel `S = 1`).  The cut machinery is `baCactus_cut` (`BA/KCactusCut.lean`), the
   layer bijection is `Flong_eq_iff_cut` and `KLsum_cut`.
5. The layer `π = ∅`: `baKpi_empty_slice`, `baKpi_empty_short` (the algebra of
   `KLInduct_Kpi_empty_*`).
6. Compiled instances at the flow point `P` of `(d, L) = (3, 4)`.

Public: the declarations above; every other helper is `private` with the stem `KInduct_`.
-/

set_option linter.style.longLine false

namespace RBM.BA

open RBM RBM.Loop
open scoped Matrix

/-! ## 1. The pins and the base levels of `BAKsol` -/

/-- **`BAKBoundAt`** (the BA analogue of `KLBoundAt`, `Loop/KLInduct.lean:89`; verbatim the probe pin
`t/T2360:RBM3D/Probe/T2360Pins.lean:38`): at `(d, n, Λ, κ)` fixed, for every `τ > 0` one constant `C`, uniform in
`L ≥ 3`, `W ≥ 1`, `g ∈ (0, Λ]`, in the real-axis data `BAReal d L g κ E m` and in the real time `t ∈ [0,1)`:
`|𝒦^{(n)}_{t,σ,a}| ≤ C L^τ (W^{-d} B_{t,0})^{n-1}`. -/
def BAKBoundAt (d n : ℕ) (Λ κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (W : ℕ), 1 ≤ W → ∀ g : ℝ, 0 < g → g ≤ Λ →
    ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (a : Fin n → Zd d L),
        ‖BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a)‖
          ≤ C * (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) ^ (n - 1)

/-- **`BAKpiBoundAt`** (the BA twin of `KLKpiBoundAt`, `Loop/KLInduct.lean:105`, `(eq:K-pi-bound)`): for every `τ > 0` one
constant `C`, uniform in `L ≥ 3`, `g ∈ (0, Λ]`, the real-axis data `BAReal d L g κ E m`, `t ∈ [0,1)`, `σ`, every layer `π`
and `a`: `|K^{(π)}_{t,σ,a}| ≤ C L^τ B_{t,0}^{n-1}`.  No `W` (`BAKpi` carries none). -/
def BAKpiBoundAt (d n : ℕ) [NeZero n] (Λ κ : ℝ) : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Fin n → Bool) (π : Finset (Fin n × Fin n))
      (a : Fin n → Zd d L),
      ‖BAKpi d L n (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a π‖
        ≤ C * (L : ℝ) ^ τ * (Bparam d L g t 0) ^ (n - 1)

section BaseLevels

/-- **`𝒦^{(1)} = m(σ)`**: the third clause of `IsKLoopS` for `BAKsol` (`BAKsol_isKLoopS` at `baKsolve`, `Λ = g`). -/
theorem baKsol_one (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (σ : Fin 1 → Bool) (a : Fin 1 → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) = PropSpin m (σ 0) := by
  have h := (BAKsol_isKLoopS (baKsolve d) hg hκ hL hg le_rfl hr (W := W)).2.2 t ht (σ 0) (a 0)
  have hloop : KLloopOf d L σ a = ⟨[σ 0], [a 0]⟩ := by simp [KLloopOf, List.ofFn_succ]
  rw [hloop]
  exact h

/-- **`(Kn2sol)`** for `BAKsol`: `𝒦^{(2)}_{σ,a} = W^{-d} (Θ_t^{(σ_0,σ_1)} M^{(σ_0,σ_1)})(a_0, a_1)`.  `BAKsol` carries no
`(Kn2sol)` clause of its own (0350 C4): it is transferred through `baK_unique` from the `baKsolve` witness. -/
theorem baKsol_two (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1) := by
  obtain ⟨K, hK, h2⟩ := baKsolve d g κ hg hκ L hL W g hg le_rfl E m hr
  have heq := baK_unique _ _ hK (BAKsol_isKLoopS (baKsolve d) hg hκ hL hg le_rfl hr) t ht (KLloopOf d L σ a)
    (by simp [LoopIdx.WF, KLloopOf]) (by simp [LoopIdx.length, KLloopOf])
  rw [← heq]
  have hloop : KLloopOf d L σ a = ⟨[(σ 0, σ 1).1, (σ 0, σ 1).2], [a 0, a 1]⟩ := by
    simp [KLloopOf, List.ofFn_succ]
  rw [hloop]
  exact h2 t ht (σ 0, σ 1) (a 0) (a 1)

/-- **`(Kn3sol)`** for `BAKsol`: `𝒦^{(3)}_{σ,a} = Σ_b ∏_k Θ_t^{(σ_k,σ_{k+1})}(a_k, b_k) · 𝓜^{(3)}_{σ,b}`, with the `M`-loop
`BAMLoop` (`baTreeRep` at `n = 3`: `TSP 3 = {∅}`, `BACactusVal_three_BAMLoop`). -/
theorem baKsol_three (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L) (W : ℕ)
    {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1)
    (σ : Fin 3 → Bool) (a : Fin 3 → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) =
      ∑ b₀ : Zd d L, ∑ b₁ : Zd d L, ∑ b₂ : Zd d L,
        BATheta d L g E m t (σ 0) (σ 1) (a 0) b₀ * BATheta d L g E m t (σ 1) (σ 2) (a 1) b₁ *
          BATheta d L g E m t (σ 2) (σ 0) (a 2) b₂ *
        BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (KLloopOf d L σ ![b₀, b₁, b₂]) := by
  rw [baTreeRep d g κ hg hκ L hL W g hg le_rfl E m hr t ht 3 le_rfl σ a, TSP_three, Finset.sum_singleton]
  exact BACactusVal_three_BAMLoop W _ t σ a

end BaseLevels


/-! ## 2. The `Θ` and `M` calculus at the BA data -/

section Calculus

variable {d L : ℕ} [NeZero L]

/-- `Θ^{(s,s')} = (1 - t M^{(s,s')})⁻¹` is invariant under a permutation `e` of the labels fixing every `M(σ)` (a copy of the
private `KMolecule_theta_perm`, `BA/KMolecule.lean:166`: the conjugation of `Ring.inverse` by a permutation matrix,
`Matrix.inv_submatrix_equiv`; no invertibility). -/
private theorem KInduct_theta_perm (e : Zd d L ≃ Zd d L) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hM : ∀ σ x y, M σ (e x) (e y) = M σ x y) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BAThetaOf M t s s' (e x) (e y) = BAThetaOf M t s s' x y := by
  have hQ : ∀ x y, BAMssOf M s s' (e x) (e y) = BAMssOf M s s' x y := fun x y => by
    simp only [BAMssOf, Matrix.of_apply, hM]
  have hA : ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s').submatrix e e =
      1 - (t : ℂ) • BAMssOf M s s' := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      e.injective.eq_iff, hQ]
  have h2 := Matrix.inv_submatrix_equiv ((1 : Matrix (Zd d L) (Zd d L) ℂ) - (t : ℂ) • BAMssOf M s s') e e
  rw [hA] at h2
  unfold BAThetaOf PropThetaQ
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  have h3 := congrFun (congrFun h2 x) y
  rw [Matrix.submatrix_apply] at h3
  exact h3.symm

/-- Translation invariance of `Θ`: `Θ_t^{(s,s')}(x, y) = Θ_t^{(s,s')}(0, y - x)` (`KInduct_theta_perm`, `BAMsigma_shift`). -/
private theorem KInduct_theta_shift (g E : ℝ) (m : ℂ) (t : ℝ) (s s' : Bool) (x y : Zd d L) :
    BATheta d L g E m t s s' x y = BATheta d L g E m t s s' 0 (y - x) := by
  have h := KInduct_theta_perm (Equiv.addRight (-x)) (BAMsigma d L (BAMB d L g (E : ℂ) m))
    (fun σ u v => BAMsigma_shift d L g (E : ℂ) m σ u v (-x)) t s s' x y
  simp only [Equiv.coe_addRight, add_neg_cancel, ← sub_eq_add_neg] at h
  exact h.symm

/-- `|M(σ)_{ab}| = |M^{(B)}_{ab}|` (`M(-) = (M^{(B)})^*`, `M^{(B)}` symmetric; a copy of the private `BKK_norm_sigma`,
`BA/KKernel.lean:76`). -/
private theorem KInduct_norm_sigma (g E : ℝ) (m : ℂ) (σ : Bool) (a b : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ a b‖ = ‖BAMB d L g (E : ℂ) m a b‖ := by
  cases σ
  · simp only [BAMsigma, Bool.false_eq_true, ite_false, Matrix.conjTranspose_apply, Complex.star_def,
      Complex.norm_conj]
    rw [BAMB_symm d L g (E : ℂ) m b a]
  · simp only [BAMsigma, ite_true]

/-- `|M(σ)_{ab}| ≤ 1`: the Ward row identity `Σ_b |M^{(B)}_{ab}|² = 1` (`BAMB_row_sq_real`). -/
private theorem KInduct_M_le_one {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ : Bool) (x y : Zd d L) :
    ‖BAMsigma d L (BAMB d L g (E : ℂ) m) σ x y‖ ≤ 1 := by
  rw [KInduct_norm_sigma]
  have hrow := BAMB_row_sq_real d L g E m hr.1 x
  have hle : ‖BAMB d L g (E : ℂ) m x y‖ ^ 2 ≤ 1 := by
    rw [← hrow]
    exact Finset.single_le_sum (f := fun b => ‖BAMB d L g (E : ℂ) m x b‖ ^ 2) (fun b _ => by positivity)
      (Finset.mem_univ y)
  nlinarith [norm_nonneg (BAMB d L g (E : ℂ) m x y)]

/-- The column sum of the moduli of `M^{(σ₁,σ₂)}` is `1`: `|M^{(σ₁,σ₂)}_{zy}| = K_{zy}` (`BAMss_norm_eq_BAK`) and `K` is doubly
stochastic (`BAK_col_sum`). -/
private theorem KInduct_mss_col {g κ E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) (σ₁ σ₂ : Bool) (y : Zd d L) :
    ∑ z, ‖BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂ z y‖ = 1 := by
  simp only [BAMss_norm_eq_BAK]
  exact BAK_col_sum d L g E m hr.1 y

end Calculus

section Constants

/-- **Properties 4 + 5** (`BAProp5`): every entry of every `Θ_t^{(σ₁,σ₂)}` is `≤ C_d B_{t,0}`: translation invariance,
`B_{t,|a|} ≤ B_{t,0}` and `exp ≤ 1` (`KLIndStepA_decay_le_zero`).  The constant depends on `(d, Λ, κ)` only. -/
private theorem KInduct_theta_sup {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ₁ σ₂ : Bool) (x y : Zd d L),
        ‖BATheta d L g E m t σ₁ σ₂ x y‖ ≤ Cd * Bparam d L g t 0 := by
  obtain ⟨Cd, hCd, cd, hcd, hbd⟩ := baProp5_holds d Λ κ hd hΛ hκ
  refine ⟨Cd, hCd, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ₁ σ₂ x y
  rw [KInduct_theta_shift]
  exact KLIndStepA_decay_le_zero (by omega) hCd.le hcd.le (y - x)
    (hbd L hL g hg hgΛ E m hr t ht0 ht1 σ₁ σ₂ (y - x))

/-- **Property 5'** (`BAProp5s`) gives an `ℓ¹` bound for a short edge: `Σ_b |Θ_t^{(σ,σ)}(x, b)| ≤ S`, `S = C_s (1 + Λ² expC k c_s)`,
uniformly in `L` (`d = k + 2`; the port of `KLedge_l1`, `Loop/KLInduct.lean:168`). -/
private theorem KInduct_theta_l1 {k : ℕ} (hd : 3 ≤ k + 2) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ S : ℝ, 0 < S ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ (σ : Bool) (x : Zd (k + 2) L),
        ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖ ≤ S := by
  obtain ⟨Cs, hCs, cs, hcs, hbd⟩ := baProp5s_holds (k + 2) Λ κ hd hΛ hκ
  have hexpC : 0 ≤ expC k cs := by unfold expC; positivity
  refine ⟨Cs * (1 + Λ ^ 2 * expC k cs), by positivity, fun L hL g hg hgΛ E m => ?_⟩
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ x
  have hpt : ∀ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
    intro b
    rw [KInduct_theta_shift]
    have := hbd L hL g hg hgΛ E m hr t ht0 ht1 σ (b - x)
    simpa [neg_mul] using this
  have h1 : ∑ b : Zd (k + 2) L, (if b - x = 0 then (1 : ℝ) else 0) = 1 := by
    simp [sub_eq_zero]
  have h2 : ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ))) ≤ expC k cs :=
    (le_of_eq (Fintype.sum_equiv (Equiv.subRight x) _
      (fun y : Zd (k + 2) L => Real.exp (-(cs * (zdistD (k + 2) L y : ℝ)))) fun b => rfl)).trans
      (sum_radial_exp_decay_le k hcs)
  calc ∑ b : Zd (k + 2) L, ‖BATheta (k + 2) L g E m t σ σ x b‖
      ≤ ∑ b : Zd (k + 2) L, Cs * ((if b - x = 0 then (1 : ℝ) else 0)
          + g ^ 2 * Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) :=
        Finset.sum_le_sum fun b _ => hpt b
    _ = Cs * (1 + g ^ 2 * ∑ b : Zd (k + 2) L, Real.exp (-(cs * (zdistD (k + 2) L (b - x) : ℝ)))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, h1, ← Finset.mul_sum]
    _ ≤ Cs * (1 + g ^ 2 * expC k cs) := by gcongr
    _ ≤ Cs * (1 + Λ ^ 2 * expC k cs) := by
        have : g ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hg.le hgΛ 2
        gcongr

/-- **`ℓ¹` rows and columns of `M(σ)`, uniform in `L`** (`BAMB_row_l1`, `BA/GreenSchur.lean:139`; `M(σ)` and `M^{(B)}` have the same
moduli, `M^{(B)}` is symmetric): `Σ_y |M(σ)_{xy}| ≤ C_M` and `Σ_y |M(σ)_{yx}| ≤ C_M`, `C_M = c⁻¹ expC k c`, `c = BAct_rate (k+2) Λ κ`. -/
private theorem KInduct_M_l1 {k : ℕ} {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) :
    ∃ Cm : ℝ, 0 < Cm ∧ ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
      haveI : NeZero L := ⟨by omega⟩
      BAReal (k + 2) L g κ E m → ∀ (σ : Bool) (x : Zd (k + 2) L),
        ∑ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ x y‖ ≤ Cm ∧
        ∑ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ y x‖ ≤ Cm := by
  have hc := BAct_rate_pos (k + 2) Λ κ (by omega) hΛ hκ
  refine ⟨(BAct_rate (k + 2) Λ κ)⁻¹ * expC k (BAct_rate (k + 2) Λ κ), by unfold expC; positivity, ?_⟩
  intro L hL g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr σ x
  have h := BAMB_row_l1 k L hL Λ g κ E m hΛ hg hgΛ hκ hr x
  have e1 : ∀ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ x y‖
      = ‖BAMB (k + 2) L g (E : ℂ) m x y‖ := fun y => KInduct_norm_sigma g E m σ x y
  have e2 : ∀ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) σ y x‖
      = ‖BAMB (k + 2) L g (E : ℂ) m x y‖ := fun y => by
    rw [KInduct_norm_sigma, BAMB_symm (k + 2) L g (E : ℂ) m y x]
  exact ⟨by simpa only [e1] using h, by simpa only [e2] using h⟩

end Constants

/-! ## 3. The bounds at the base levels, in the shape of `BAKBoundAt` -/

section BaseBounds

/-- `1 ≤ L^τ` for `L ≥ 3`, `τ > 0` (a copy of `KLone_le_rpow`, `Loop/KLInduct.lean:219`; that file is not imported). -/
private theorem KInduct_one_le_rpow {L : ℕ} (hL : 3 ≤ L) {τ : ℝ} (hτ : 0 < τ) : (1 : ℝ) ≤ (L : ℝ) ^ τ :=
  Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ L)) hτ.le

/-- **`(eq:bcal_k)` at `n = 1`**: `𝒦^{(1)} = m(σ)`, `|m| ≤ 1` (`BAm_norm_le_one`), `L^τ ≥ 1`; no hypothesis on `(d, Λ, κ)`: the third
clause of `IsKLoopS` of the solution, and `BAKsol = 0` where there is none (the probe's `BAKBoundAt_one`). -/
theorem baKBoundAt_one (d : ℕ) (Λ κ : ℝ) : BAKBoundAt d 1 Λ κ := by
  intro τ hτ
  refine ⟨1, one_pos, ?_⟩
  intro L hL W hW g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hm : ‖m‖ ≤ 1 := BAm_norm_le_one d L g (E : ℂ) m (by simp) hr.1
  have hs : ∀ s : Bool, ‖PropSpin m s‖ ≤ 1 := fun s => by
    cases s <;> simpa [PropSpin] using hm
  have hL1 := KInduct_one_le_rpow hL hτ
  have hI : KLloopOf d L σ a = ⟨[σ 0], [a 0]⟩ := by simp [KLloopOf, List.ofFn_succ]
  rw [hI]
  simp only [Nat.sub_self, pow_zero, mul_one, one_mul]
  unfold BAKsol
  split_ifs with h
  · rw [h.choose_spec.2.2 t ⟨ht0, ht1⟩ (σ 0) (a 0)]
    exact (hs _).trans hL1
  · simpa using (zero_le_one.trans hL1)

/-- **`(eq:bcal_k)` at `n = 2`**: `(Kn2sol)` (`baKsol_two`), the sup bound `|Θ^{(σσ')}(x,y)| ≤ C_d B_{t,0}` (properties 4, 5) and the
column sum `Σ_z |M^{(σσ')}_{zy}| = Σ_z K_{zy} = 1`; the loss is `L^τ ≥ 1`. -/
theorem baKBoundAt_two {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : BAKBoundAt d 2 Λ κ := by
  obtain ⟨Cd, hCd, hsup⟩ := KInduct_theta_sup hd hΛ hκ
  intro τ hτ
  refine ⟨Cd, hCd, ?_⟩
  intro L hL W hW g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hB0 := KLIndStepA_Bparam_nonneg (d := d) (L := L) (g := g) t 0
  have hL1 := KInduct_one_le_rpow hL hτ
  have hW0 : 0 ≤ ((W : ℝ) ^ d)⁻¹ := by positivity
  have hmain : ‖(BATheta d L g E m t (σ 0) (σ 1) * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1)‖
      ≤ Cd * Bparam d L g t 0 := by
    rw [Matrix.mul_apply]
    calc ‖∑ z, BATheta d L g E m t (σ 0) (σ 1) (a 0) z * BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1) z (a 1)‖
        ≤ ∑ z, ‖BATheta d L g E m t (σ 0) (σ 1) (a 0) z‖ *
            ‖BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1) z (a 1)‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq ?_)
          simp only [norm_mul]
      _ ≤ ∑ z, (Cd * Bparam d L g t 0) * ‖BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1) z (a 1)‖ :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right
            (hsup L hL g hg hgΛ E m hr t ht0 ht1 _ _ _ _) (norm_nonneg _)
      _ = Cd * Bparam d L g t 0 := by rw [← Finset.mul_sum, KInduct_mss_col hr, mul_one]
  rw [baKsol_two d hκ hg hL W hr ⟨ht0, ht1⟩ σ a, norm_mul, norm_inv, norm_pow, Complex.norm_natCast,
    show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  calc ((W : ℝ) ^ d)⁻¹ * ‖(BATheta d L g E m t (σ 0) (σ 1) *
          BAMss d L (BAMB d L g (E : ℂ) m) (σ 0) (σ 1)) (a 0) (a 1)‖
      ≤ ((W : ℝ) ^ d)⁻¹ * (Cd * Bparam d L g t 0) := mul_le_mul_of_nonneg_left hmain hW0
    _ = Cd * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) := by ring
    _ ≤ Cd * (L : ℝ) ^ τ * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) := by
        have hX := mul_nonneg hW0 hB0
        calc Cd * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0)
            = (Cd * 1) * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) := by ring
          _ ≤ (Cd * (L : ℝ) ^ τ) * (((W : ℝ) ^ d)⁻¹ * Bparam d L g t 0) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 hCd.le) hX

/-- Reordering of a triple sum: `Σ_x Σ_y Σ_z f x y z = Σ_y Σ_z Σ_x f x y z`. -/
private theorem KInduct_sum_rot {G : Type*} [Fintype G] (f : G → G → G → ℂ) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ y, ∑ z, ∑ x, f x y z := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

/-- **The star bound of the `3`-loop with the short leaf first**: `‖Σ_b T₀(a₀,b₀) T₁(a₁,b₁) T₂(a₂,b₂) M₀(b₂,b₀) M₁(b₀,b₁) M₂(b₁,b₂)‖
≤ A² S C²` when `T₁, T₂` are bounded by `A` in sup norm, `T₀(a₀,·)` has `ℓ¹` norm `≤ S`, the entries of the `M_i` are `≤ 1`, the columns of
`M₀` and the rows of `M₁` have `ℓ¹` norm `≤ C` (the sum over `b₂` and `b₁`; the sum over `b₀` is the short leaf). -/
private theorem KInduct_three_short {G : Type*} [Fintype G] (T₀ T₁ T₂ M₀ M₁ M₂ : G → G → ℂ) (a₀ a₁ a₂ : G)
    {A S C : ℝ} (hT₁ : ∀ x y, ‖T₁ x y‖ ≤ A) (hT₂ : ∀ x y, ‖T₂ x y‖ ≤ A) (hT₀ : ∑ b, ‖T₀ a₀ b‖ ≤ S)
    (hM₂ : ∀ x y, ‖M₂ x y‖ ≤ 1) (hM₀ : ∀ x, ∑ y, ‖M₀ y x‖ ≤ C) (hM₁ : ∀ x, ∑ y, ‖M₁ x y‖ ≤ C) :
    ‖∑ b₀, ∑ b₁, ∑ b₂, T₀ a₀ b₀ * T₁ a₁ b₁ * T₂ a₂ b₂ * (M₀ b₂ b₀ * M₁ b₀ b₁ * M₂ b₁ b₂)‖
      ≤ A ^ 2 * S * C ^ 2 := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hT₁ a₁ a₀)
  have hC : 0 ≤ C := (Finset.sum_nonneg fun _ _ => norm_nonneg _).trans (hM₁ a₀)
  calc ‖∑ b₀, ∑ b₁, ∑ b₂, T₀ a₀ b₀ * T₁ a₁ b₁ * T₂ a₂ b₂ * (M₀ b₂ b₀ * M₁ b₀ b₁ * M₂ b₁ b₂)‖
      ≤ ∑ b₀, ∑ b₁, ∑ b₂, ‖T₀ a₀ b₀ * T₁ a₁ b₁ * T₂ a₂ b₂ * (M₀ b₂ b₀ * M₁ b₀ b₁ * M₂ b₁ b₂)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₀ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b₁ _ => ?_)
        exact norm_sum_le _ _
    _ ≤ ∑ b₀, ∑ b₁, ∑ b₂, ‖T₀ a₀ b₀‖ * (A * A) * (‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖) := by
        refine Finset.sum_le_sum fun b₀ _ => Finset.sum_le_sum fun b₁ _ => Finset.sum_le_sum fun b₂ _ => ?_
        have h1 := hT₁ a₁ b₁
        have h2 := hT₂ a₂ b₂
        have h3 := hM₂ b₁ b₂
        have h12 : ‖T₁ a₁ b₁‖ * ‖T₂ a₂ b₂‖ ≤ A * A := mul_le_mul h1 h2 (norm_nonneg _) hA
        have h0 := norm_nonneg (T₀ a₀ b₀)
        have hm0 := norm_nonneg (M₀ b₂ b₀)
        have hm1 := norm_nonneg (M₁ b₀ b₁)
        have hm2 := norm_nonneg (M₂ b₁ b₂)
        calc ‖T₀ a₀ b₀ * T₁ a₁ b₁ * T₂ a₂ b₂ * (M₀ b₂ b₀ * M₁ b₀ b₁ * M₂ b₁ b₂)‖
            = ‖T₀ a₀ b₀‖ * (‖T₁ a₁ b₁‖ * ‖T₂ a₂ b₂‖) * (‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖ * ‖M₂ b₁ b₂‖) := by
              simp only [norm_mul]; ring
          _ ≤ ‖T₀ a₀ b₀‖ * (A * A) * (‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖ * 1) := by gcongr
          _ = ‖T₀ a₀ b₀‖ * (A * A) * (‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖) := by ring
    _ ≤ ∑ b₀, ‖T₀ a₀ b₀‖ * (A * A) * (C * C) := by
        refine Finset.sum_le_sum fun b₀ _ => ?_
        have hrow : ∑ b₁, ∑ b₂, ‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖ ≤ C * C := by
          calc ∑ b₁, ∑ b₂, ‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖
              = (∑ b₂, ‖M₀ b₂ b₀‖) * (∑ b₁, ‖M₁ b₀ b₁‖) := by
                rw [Finset.sum_mul_sum, Finset.sum_comm]
            _ ≤ C * C := mul_le_mul (hM₀ b₀) (hM₁ b₀) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hC
        calc ∑ b₁, ∑ b₂, ‖T₀ a₀ b₀‖ * (A * A) * (‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖)
            = ‖T₀ a₀ b₀‖ * (A * A) * ∑ b₁, ∑ b₂, ‖M₀ b₂ b₀‖ * ‖M₁ b₀ b₁‖ := by
              simp_rw [← Finset.mul_sum]
          _ ≤ ‖T₀ a₀ b₀‖ * (A * A) * (C * C) :=
              mul_le_mul_of_nonneg_left hrow (mul_nonneg (norm_nonneg _) (mul_nonneg hA hA))
    _ = (∑ b₀, ‖T₀ a₀ b₀‖) * (A * A) * (C * C) := by rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ S * (A * A) * (C * C) := by gcongr
    _ = A ^ 2 * S * C ^ 2 := by ring

/-- **The star bound of the `3`-loop, every position of the short leaf**: `KInduct_three_short` after the cyclic rotations of the
labels `(b₀, b₁, b₂)`; the leaves `T_i` are bounded by `A` in sup norm, one `T_i(a_i, ·)` has `ℓ¹` norm `≤ S`, the entries of the
`M_i` are `≤ 1` and their rows and columns have `ℓ¹` norm `≤ C`. -/
private theorem KInduct_three_bound {G : Type*} [Fintype G] (T₀ T₁ T₂ M₀ M₁ M₂ : G → G → ℂ) (a₀ a₁ a₂ : G)
    {A S C : ℝ} (hT₀ : ∀ x y, ‖T₀ x y‖ ≤ A) (hT₁ : ∀ x y, ‖T₁ x y‖ ≤ A) (hT₂ : ∀ x y, ‖T₂ x y‖ ≤ A)
    (hS : (∑ b, ‖T₀ a₀ b‖ ≤ S) ∨ (∑ b, ‖T₁ a₁ b‖ ≤ S) ∨ (∑ b, ‖T₂ a₂ b‖ ≤ S))
    (hM₀ : (∀ x y, ‖M₀ x y‖ ≤ 1) ∧ (∀ x, ∑ y, ‖M₀ x y‖ ≤ C) ∧ (∀ x, ∑ y, ‖M₀ y x‖ ≤ C))
    (hM₁ : (∀ x y, ‖M₁ x y‖ ≤ 1) ∧ (∀ x, ∑ y, ‖M₁ x y‖ ≤ C) ∧ (∀ x, ∑ y, ‖M₁ y x‖ ≤ C))
    (hM₂ : (∀ x y, ‖M₂ x y‖ ≤ 1) ∧ (∀ x, ∑ y, ‖M₂ x y‖ ≤ C) ∧ (∀ x, ∑ y, ‖M₂ y x‖ ≤ C)) :
    ‖∑ b₀, ∑ b₁, ∑ b₂, T₀ a₀ b₀ * T₁ a₁ b₁ * T₂ a₂ b₂ * (M₀ b₂ b₀ * M₁ b₀ b₁ * M₂ b₁ b₂)‖
      ≤ A ^ 2 * S * C ^ 2 := by
  rcases hS with h | h | h
  · exact KInduct_three_short T₀ T₁ T₂ M₀ M₁ M₂ a₀ a₁ a₂ hT₁ hT₂ h hM₂.1 hM₀.2.2 hM₁.2.1
  · refine le_trans (le_of_eq ?_) (KInduct_three_short T₁ T₂ T₀ M₁ M₂ M₀ a₁ a₂ a₀ hT₂ hT₀ h hM₀.1 hM₁.2.2 hM₂.2.1)
    rw [KInduct_sum_rot]
    congr 1
    refine Finset.sum_congr rfl fun b₁ _ => Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₀ _ => ?_
    ring
  · refine le_trans (le_of_eq ?_) (KInduct_three_short T₂ T₀ T₁ M₂ M₀ M₁ a₂ a₀ a₁ hT₀ hT₁ h hM₁.1 hM₂.2.2 hM₀.2.1)
    rw [KInduct_sum_rot, KInduct_sum_rot]
    congr 1
    refine Finset.sum_congr rfl fun b₂ _ => Finset.sum_congr rfl fun b₀ _ => Finset.sum_congr rfl fun b₁ _ => ?_
    ring

/-- Among three charges, if the neighbouring pairs `(x, y)` and `(y, z)` differ then `z = x` (a triangle of charges has an equal
neighbouring pair). -/
private theorem KInduct_bool3 (x y z : Bool) (h01 : ¬x = y) (h12 : ¬y = z) : z = x := by
  cases x <;> cases y <;> cases z <;> simp_all

/-- The `3`-loop of `BAKsol` as the one-tree cactus sum, in the product form of `BACactusVal_three`
(`baTreeRep` at `n = 3`, `TSP 3 = {∅}`): `W^{-2d} Σ_b ∏_k Θ^{(σ_k,σ_{k+1})}(a_k, b_k) · ∏_i M(σ_i)_{b_{i-1} b_i}`. -/
private theorem KInduct_Ksol_three (d : ℕ) {κ g : ℝ} (hκ : 0 < κ) (hg : 0 < g) {L : ℕ} [NeZero L] (hL : 3 ≤ L)
    (W : ℕ) {E : ℝ} {m : ℂ} (hr : BAReal d L g κ E m) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) 1) (σ : Fin 3 → Bool)
    (a : Fin 3 → Zd d L) :
    BAKsol d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) (PropSpin m) t (KLloopOf d L σ a) =
      (((W : ℂ) ^ d)⁻¹) ^ 2 * ∑ b₀, ∑ b₁, ∑ b₂,
        BATheta d L g E m t (σ 0) (σ 1) (a 0) b₀ * BATheta d L g E m t (σ 1) (σ 2) (a 1) b₁ *
          BATheta d L g E m t (σ 2) (σ 0) (a 2) b₂ *
        (BAMsigma d L (BAMB d L g (E : ℂ) m) (σ 0) b₂ b₀ * BAMsigma d L (BAMB d L g (E : ℂ) m) (σ 1) b₀ b₁ *
          BAMsigma d L (BAMB d L g (E : ℂ) m) (σ 2) b₁ b₂) := by
  rw [baTreeRep d g κ hg hκ L hL W g hg le_rfl E m hr t ht 3 le_rfl σ a, TSP_three, Finset.sum_singleton]
  exact congrArg _ (BACactusVal_three (BAMsigma d L (BAMB d L g (E : ℂ) m)) t σ a)

/-- **`(eq:bcal_k)` at `n = 3`**: `(Kn3sol)` as the one-tree cactus sum; the three leaves `Θ^{(σ_k,σ_{k+1})}`, one of them short
(a triangle of charges has an equal neighbouring pair): the short leaf is summed (property 5', `ℓ¹ ≤ S`), the two others are bounded in
sup norm by `C_d B_{t,0}` (properties 4, 5); the `M`-loop is bounded by `1` (Ward row identity) and by two `ℓ¹` rows of `M` (`C_M`).
The exponent is `2 = n - 1`; the loss is `L^τ ≥ 1`. -/
theorem baKBoundAt_three {d : ℕ} (hd : 3 ≤ d) {Λ κ : ℝ} (hΛ : 0 < Λ) (hκ : 0 < κ) : BAKBoundAt d 3 Λ κ := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cd, hCd, hsup⟩ := KInduct_theta_sup hd hΛ hκ
  obtain ⟨S, hS0, hl1⟩ := KInduct_theta_l1 (k := k) hd hΛ hκ
  obtain ⟨Cm, hCm0, hM⟩ := KInduct_M_l1 (k := k) hΛ hκ
  intro τ hτ
  refine ⟨Cd ^ 2 * S * Cm ^ 2, by positivity, ?_⟩
  intro L hL W hW g hg hgΛ E m
  have : NeZero L := ⟨by omega⟩
  intro hr t ht0 ht1 σ a
  have hB0 := KLIndStepA_Bparam_nonneg (d := k + 2) (L := L) (g := g) t 0
  have hL1 := KInduct_one_le_rpow hL hτ
  have hW0 : 0 ≤ ((W : ℝ) ^ (k + 2))⁻¹ := by positivity
  have hsupp : ∀ (s s' : Bool) (x y : Zd (k + 2) L),
      ‖BATheta (k + 2) L g E m t s s' x y‖ ≤ Cd * Bparam (k + 2) L g t 0 := fun s s' x y =>
    hsup L hL g hg hgΛ E m hr t ht0 ht1 s s' x y
  have hshort : ∀ (s : Bool) (x : Zd (k + 2) L), ∑ b, ‖BATheta (k + 2) L g E m t s s x b‖ ≤ S := fun s x =>
    hl1 L hL g hg hgΛ E m hr t ht0 ht1 s x
  have hM1 : ∀ (s : Bool) (x y : Zd (k + 2) L),
      ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) s x y‖ ≤ 1 := fun s x y => KInduct_M_le_one hr s x y
  have hMr : ∀ (s : Bool) (x : Zd (k + 2) L),
      ∑ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) s x y‖ ≤ Cm := fun s x =>
    (hM L hL g hg hgΛ E m hr s x).1
  have hMc : ∀ (s : Bool) (x : Zd (k + 2) L),
      ∑ y, ‖BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) s y x‖ ≤ Cm := fun s x =>
    (hM L hL g hg hgΛ E m hr s x).2
  have hS : (∑ b, ‖BATheta (k + 2) L g E m t (σ 0) (σ 1) (a 0) b‖ ≤ S) ∨
      (∑ b, ‖BATheta (k + 2) L g E m t (σ 1) (σ 2) (a 1) b‖ ≤ S) ∨
      (∑ b, ‖BATheta (k + 2) L g E m t (σ 2) (σ 0) (a 2) b‖ ≤ S) := by
    by_cases h01 : σ 0 = σ 1
    · left; rw [← h01]; exact hshort _ _
    · by_cases h12 : σ 1 = σ 2
      · right; left; rw [← h12]; exact hshort _ _
      · right; right
        rw [KInduct_bool3 (σ 0) (σ 1) (σ 2) h01 h12]; exact hshort _ _
  have hstar := KInduct_three_bound (BATheta (k + 2) L g E m t (σ 0) (σ 1)) (BATheta (k + 2) L g E m t (σ 1) (σ 2))
    (BATheta (k + 2) L g E m t (σ 2) (σ 0)) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 0))
    (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 1)) (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 2))
    (a 0) (a 1) (a 2) (fun x y => hsupp _ _ x y) (fun x y => hsupp _ _ x y) (fun x y => hsupp _ _ x y) hS
    ⟨fun x y => hM1 _ x y, fun x => hMr _ x, fun x => hMc _ x⟩ ⟨fun x y => hM1 _ x y, fun x => hMr _ x, fun x => hMc _ x⟩
    ⟨fun x y => hM1 _ x y, fun x => hMr _ x, fun x => hMc _ x⟩
  rw [KInduct_Ksol_three (k + 2) hκ hg hL W hr ⟨ht0, ht1⟩ σ a, norm_mul, norm_pow, norm_inv, norm_pow,
    Complex.norm_natCast, show (3 : ℕ) - 1 = 2 from rfl]
  calc (((W : ℝ) ^ (k + 2))⁻¹) ^ 2 * ‖∑ b₀, ∑ b₁, ∑ b₂,
        BATheta (k + 2) L g E m t (σ 0) (σ 1) (a 0) b₀ * BATheta (k + 2) L g E m t (σ 1) (σ 2) (a 1) b₁ *
          BATheta (k + 2) L g E m t (σ 2) (σ 0) (a 2) b₂ *
        (BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 0) b₂ b₀ *
          BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 1) b₀ b₁ *
          BAMsigma (k + 2) L (BAMB (k + 2) L g (E : ℂ) m) (σ 2) b₁ b₂)‖
      ≤ (((W : ℝ) ^ (k + 2))⁻¹) ^ 2 * ((Cd * Bparam (k + 2) L g t 0) ^ 2 * S * Cm ^ 2) :=
        mul_le_mul_of_nonneg_left hstar (by positivity)
    _ = Cd ^ 2 * S * Cm ^ 2 * (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2 := by ring
    _ ≤ Cd ^ 2 * S * Cm ^ 2 * (L : ℝ) ^ τ * (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2 := by
        have h1 : 0 ≤ (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2 := by positivity
        calc Cd ^ 2 * S * Cm ^ 2 * (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2
            = (Cd ^ 2 * S * Cm ^ 2 * 1) * (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2 := by ring
          _ ≤ (Cd ^ 2 * S * Cm ^ 2 * (L : ℝ) ^ τ) * (((W : ℝ) ^ (k + 2))⁻¹ * Bparam (k + 2) L g t 0) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL1 (by positivity)) h1

end BaseBounds

/-! ## 4. The cut of `K^{(π)}` at an innermost long edge -/

section Cut

variable {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n}

/-- The generic value with the last leaf `r` of weight `1` at the label `u`: the sum over the labels `δ` with `δ_r = u` of the value with
leaf weights `1` times the product of the other leaf weights at `δ`.  The first stage of `(eq:molecule-Kpi)` (the reattachment of the
leaves to the self-energy, as `KMolecule_gval_eq_sum`, `BA/KMolecule.lean:87`, whose proof is the first `have` here) with the root leaf
`1` at `u`; the twin of `KLInduct_inner_eq`, `Loop/KLInduct.lean:558`. -/
private theorem KInduct_gval_last {Nd Lf Ed : Type*} [Fintype Nd] [DecidableEq Nd] [Fintype Lf] [DecidableEq Lf]
    [Fintype Ed] (r : Lf) (u : Zd d L) (a : Lf → Zd d L) (Lw : Lf → Matrix (Zd d L) (Zd d L) ℂ) (p : Lf → Nd)
    (E : Ed → Matrix (Zd d L) (Zd d L) ℂ) (c q : Ed → Nd) :
    KLgval d L (Function.update a r u) (Function.update Lw r 1) p E c q =
      ∑ δ ∈ Finset.univ.filter (fun δ : Lf → Zd d L => δ r = u),
        KLgval d L δ (fun _ => 1) p E c q * ∏ ℓ ∈ Finset.univ.erase r, Lw ℓ (a ℓ) (δ ℓ) := by
  have h1 : ∀ (a' : Lf → Zd d L) (Lw' : Lf → Matrix (Zd d L) (Zd d L) ℂ),
      KLgval d L a' Lw' p E c q = ∑ δ : Lf → Zd d L, KLgval d L δ (fun _ => 1) p E c q * ∏ ℓ, Lw' ℓ (a' ℓ) (δ ℓ) := by
    intro a' Lw'
    simp only [KLgval, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h : ∀ δ : Lf → Zd d L, (∏ ℓ, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ))) *
        (∏ e, E e (b (c e)) (b (q e))) * ∏ ℓ, Lw' ℓ (a' ℓ) (δ ℓ) =
        (∏ e, E e (b (c e)) (b (q e))) * ∏ ℓ, ((1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ)) * Lw' ℓ (a' ℓ) (δ ℓ)) := by
      intro δ
      rw [mul_comm (∏ ℓ, (1 : Matrix (Zd d L) (Zd d L) ℂ) (δ ℓ) (b (p ℓ))), mul_assoc, ← Finset.prod_mul_distrib]
    simp_rw [h, ← Finset.mul_sum]
    rw [mul_comm]
    congr 1
    have := (Finset.prod_univ_sum (fun _ : Lf => (Finset.univ : Finset (Zd d L)))
      (fun ℓ x => (1 : Matrix (Zd d L) (Zd d L) ℂ) x (b (p ℓ)) * Lw' ℓ (a' ℓ) x)).symm
    rw [Fintype.piFinset_univ] at this
    rw [this]
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    simp [Matrix.one_apply]
  rw [h1, Finset.sum_filter]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hleaf : ∏ ℓ, Function.update Lw r 1 ℓ (Function.update a r u ℓ) (δ ℓ) =
      (if δ r = u then (1 : ℂ) else 0) * ∏ ℓ ∈ Finset.univ.erase r, Lw ℓ (a ℓ) (δ ℓ) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r)]
    congr 1
    · simp only [Function.update_self, Matrix.one_apply]
      by_cases h : δ r = u
      · simp [h]
      · simp [h, Ne.symm h]
    · refine Finset.prod_congr rfl fun ℓ hℓ => ?_
      have hne : ℓ ≠ r := Finset.ne_of_mem_erase hℓ
      simp only [Function.update_of_ne hne]
  rw [hleaf]
  by_cases h : δ r = u
  · simp [h]
  · simp [h]

/-- The leaf weights of the inner polygon off its last vertex: `Θ^{(σ_{i+k},σ_{i+k+1})} = Θ^{(σin_k,σin_{k+1})}` for `k < last`
(`baCactus_leafW_in` at the vertex `k`). -/
private theorem KInduct_leafW_in (hJ : J.1.val + 2 ≤ J.2.val) (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ)
    (σ : Fin n → Bool) (ℓ : Fin (KLwIn J + 1)) (hℓ : ℓ ≠ Fin.last _) :
    BACactusValLeafW M t σ (BAinVinv J ℓ) = BAThetaOf M t (sigmaIn σ J ℓ) (sigmaIn σ J (ℓ + 1)) := by
  have h := congrFun (baCactus_leafW_in hJ M t σ) ℓ
  simp only [BAdeltaIn, Function.update_of_ne hℓ] at h
  exact h

/-- **The cut of one tree at its chord `J`** (the tree level of `baKpi_cut`): the generic cut `baCactus_cut` at the leaf weights `Θ`,
`P = 1`, `S = t·1`, `Q = Θ^{(σ_i,σ_j)}` (so `P S Q = tΘ^{(σ_i,σ_j)}` is the weight already on the chord `J` and the update is the identity).
`S = t·1` collapses the glue labels `w = u`; the outer leaf `Q` is the glue leaf of the outer polygon (`baCactus_leafW_out`), so the outer
factor is `Γ` of the outer tree at the glue label `u`; the inner polygon has the identity as its last leaf, i.e. the inner value is the sum
over the labels `δ` with `δ_last = u` of the self-energy of the inner tree times the other leaves (the reversed inner leaf is `1ᵀ = 1`,
C2: no symmetry of `M` is used). -/
private theorem KInduct_tree_cut {F : Finset (Fin n × Fin n)} (hF : KLIsTSP F) (hn : 2 ≤ n) (hJ : J ∈ F)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) :
    BAGamma d L n M t F σ a = ∑ u : Zd d L, (t : ℂ) *
      (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
        BASigmaTree d L M t (KLFIn F J) (sigmaIn σ J) δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
      BAGamma d L (n - KLwIn J + 1) M t (KLFOut F J) (sigmaOut σ J) (BAdeltaOut J a u) := by
  have hJw := KLdiag_width hF hJ
  have h := baCactus_cut hF hn hJ M t σ a (BACactusValLeafW M t σ) 1 ((t : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ))
    (BAThetaOf M t (σ J.1) (σ J.2))
  have hupd : Function.update (BACactusValEdgeW M t F σ) (Sum.inl ⟨J, hJ⟩)
      (1 * ((t : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)) * BAThetaOf M t (σ J.1) (σ J.2)) =
      BACactusValEdgeW M t F σ := by
    have : 1 * ((t : ℂ) • (1 : Matrix (Zd d L) (Zd d L) ℂ)) * BAThetaOf M t (σ J.1) (σ J.2) =
        BACactusValEdgeW M t F σ (Sum.inl ⟨J, hJ⟩) := by
      rw [one_mul, Matrix.smul_mul, Matrix.one_mul]
      rfl
    rw [this]
    exact Function.update_eq_self _ _
  rw [hupd, Matrix.transpose_one, baCactus_leafW_out hJw M t σ] at h
  refine h.trans (Finset.sum_congr rfl fun u _ => ?_)
  rw [Finset.sum_eq_single u]
  · have hin : KLgval d L (Nd := BAslot (KLFIn F J)) (Lf := Fin (KLwIn J + 1)) (BAdeltaIn J a u)
        (BAdeltaIn J (BACactusValLeafW M t σ) 1) (BAslotLeaf (KLFIn F J))
        (BACactusValEdgeW M t (KLFIn F J) (sigmaIn σ J)) (BACactusValSrc (KLFIn F J)) (BACactusValTgt (KLFIn F J)) =
        ∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
          BASigmaTree d L M t (KLFIn F J) (sigmaIn σ J) δ *
            ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k) := by
      refine (KInduct_gval_last (Fin.last _) u (fun k => a (BAinVinv J k))
        (fun k => BACactusValLeafW M t σ (BAinVinv J k)) _ _ _ _).trans ?_
      refine Finset.sum_congr rfl fun δ _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun ℓ hℓ => by rw [KInduct_leafW_in hJw M t σ ℓ (Finset.ne_of_mem_erase hℓ)]
    rw [hin]
    simp only [Matrix.smul_apply, Matrix.one_apply, ite_true, smul_eq_mul, mul_one]
    rw [mul_comm _ (t : ℂ)]
    rfl
  · intro w _ hw
    simp [Ne.symm hw]
  · intro hu
    exact absurd (Finset.mem_univ u) hu

/-- The double sum of the layer assembly: `Σ_G Σ_H Σ_u t a(H,u) b(G,u) = Σ_u t (Σ_H a(H,u)) (Σ_G b(G,u))`. -/
private theorem KInduct_sum3 {α β γ : Type*} [Fintype γ] (sG : Finset α) (sH : Finset β) (t : ℂ)
    (a : β → γ → ℂ) (b : α → γ → ℂ) :
    ∑ G ∈ sG, ∑ H ∈ sH, ∑ u, t * a H u * b G u = ∑ u, t * (∑ H ∈ sH, a H u) * ∑ G ∈ sG, b G u := by
  calc ∑ G ∈ sG, ∑ H ∈ sH, ∑ u, t * a H u * b G u
      = ∑ G ∈ sG, ∑ u, ∑ H ∈ sH, t * a H u * b G u := Finset.sum_congr rfl fun G _ => Finset.sum_comm
    _ = ∑ u, ∑ G ∈ sG, ∑ H ∈ sH, t * a H u * b G u := Finset.sum_comm
    _ = ∑ u, t * (∑ H ∈ sH, a H u) * ∑ G ∈ sG, b G u := by
        refine Finset.sum_congr rfl fun u _ => ?_
        calc ∑ G ∈ sG, ∑ H ∈ sH, t * a H u * b G u
            = ∑ G ∈ sG, (t * ∑ H ∈ sH, a H u) * b G u := by
              refine Finset.sum_congr rfl fun G _ => ?_
              rw [Finset.mul_sum, Finset.sum_mul]
          _ = (t * ∑ H ∈ sH, a H u) * ∑ G ∈ sG, b G u := by rw [← Finset.mul_sum]

end Cut

section CutThm

/-- **The cut of `K^{(π)}` at an innermost long edge** (`n ≥ 3`; the BA twin of `KLKpi_cut`, `Loop/KLInduct.lean:606`; a step of `(eq:molecule-Kpi)`, `A_deterministic_estimates.tex:625`, whose long edges `tS^{(B)}Θ_t^{(+,-)}` are `tΘ_t^{(+,-)}` for BA).  If
`π = F_long(F₀, σ)` for a tree `F₀` and `J = (i, j) ∈ π` is innermost (no other edge of `π` inside its arc), then
`K^{(π)}(t,σ,a) = t Σ_u A(u) K^{(π')}(σ_out, a_out(u))`, where `π' = (π ∖ {J})` moved to the outer polygon (`n - (j - i) + 1` vertices, glue
vertex at `i`, charges `sigmaOut σ J`, labels `BAdeltaOut J a u`), and `A(u)` is the summand, at the root label `u`, of the left side of
`IndStepAbs` for the inner polygon (`j - i + 1` vertices, charges `sigmaIn σ J`, root `Fin.last`, labels `a_i, …, a_{j-1}`):
`A(u) = Σ_{δ: δ_last = u} Σ^{(∅)}(δ) ∏_{k ≠ last} Θ^{(σin_k,σin_{k+1})}(a_{i+k}, δ_k)`.  The glue is the BA chord `tΘ^{(σ_i,σ_j)}`, with prefactor
exactly `t` (no `∏ m(σ_i)`): it is the standard glue leaf `Θ^{(σ_i,σ_j)}` of the outer polygon at the label `u`, so one glue sum replaces the
band's `Σ_{u,w} ξ_J S^{(B)}_{uw}`; BA has no `Θ - 1 = ξ_J SΘ` (paper-delta candidate `T2381a`).  No hypothesis on `M` or `t` (the reversed
inner leaf is `1ᵀ = 1`: C2).  `KLsum_cut` and `Flong_eq_iff_cut` (the layer bijection), `KInduct_tree_cut` (one tree). -/
theorem baKpi_cut {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π)
    (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) :
    BAKpi d L n M t σ a π = ∑ u : Zd d L, (t : ℂ) *
      (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
        BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
      BAKpi d L (n - KLwIn J + 1) M t (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J)) := by
  have hn2 : 2 ≤ n := by omega
  have hF₀' := KLisTSP_of_mem_TSP hF₀
  have hJF₀ : J ∈ F₀ := Flong_subset F₀ σ (hπ ▸ hJπ)
  have hJd : IsDiag n J.1 J.2 := hF₀'.1 J hJF₀
  set π' := (π.erase J).image (KLshiftOut J) with hπ'
  set Ain : Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → Zd d L → ℂ := fun H u =>
    if KLFlong H (sigmaIn σ J) = ∅ then
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
        BASigmaTree d L M t H (sigmaIn σ J) δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)
    else 0 with hAin
  set Bout : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) → Zd d L → ℂ := fun G u =>
    if KLFlong G (sigmaOut σ J) = π' then
      BAGamma d L (n - KLwIn J + 1) M t G (sigmaOut σ J) (BAdeltaOut J a u) else 0 with hBout
  set f : Finset (Fin (n - KLwIn J + 1) × Fin (n - KLwIn J + 1)) →
      Finset (Fin (KLwIn J + 1) × Fin (KLwIn J + 1)) → ℂ := fun G H =>
    ∑ u, (t : ℂ) * Ain H u * Bout G u with hf
  have hlayer : KLTSPlong n σ π = ((TSP n).filter fun F => J ∈ F).filter fun F => KLFlong F σ = π := by
    ext F
    simp only [KLTSPlong, Finset.mem_filter]
    constructor
    · rintro ⟨hF, h⟩
      exact ⟨⟨hF, Flong_subset F σ (h ▸ hJπ)⟩, h⟩
    · rintro ⟨⟨hF, -⟩, h⟩
      exact ⟨hF, h⟩
  have hpt : ∀ F ∈ (TSP n).filter (fun F => J ∈ F),
      (if KLFlong F σ = π then BAGamma d L n M t F σ a else 0) = f (KLFOut F J) (KLFIn F J) := by
    intro F hF
    obtain ⟨hFT, hJF⟩ := Finset.mem_filter.1 hF
    have hF' := KLisTSP_of_mem_TSP hFT
    have hiff := Flong_eq_iff_cut hF' hn2 hJF σ hF₀' hπ hJπ hinner
    by_cases h : KLFlong F σ = π
    · obtain ⟨h1, h2⟩ := hiff.1 h
      have h1' : KLFlong (KLFOut F J) (sigmaOut σ J) = π' := h1
      simp only [h, ↓reduceIte, f, Ain, Bout, h1', h2]
      exact KInduct_tree_cut hF' hn2 hJF M t σ a
    · simp only [h, ↓reduceIte, f]
      by_cases h1 : KLFlong (KLFOut F J) (sigmaOut σ J) = π'
      · have h2 : ¬KLFlong (KLFIn F J) (sigmaIn σ J) = ∅ := fun h2 => h (hiff.2 ⟨h1, h2⟩)
        simp [Ain, h2]
      · simp [Bout, h1]
  have hA' : ∀ u : Zd d L, ∑ H ∈ TSP (KLwIn J + 1), Ain H u =
      ∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
        BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k) := by
    intro u
    have h1 : ∑ H ∈ TSP (KLwIn J + 1), Ain H u = ∑ H ∈ KLTSPlong (KLwIn J + 1) (sigmaIn σ J) ∅,
        ∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
          BASigmaTree d L M t H (sigmaIn σ J) δ *
            ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k) := by
      simp only [KLTSPlong, hAin, Finset.sum_filter]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun δ _ => ?_
    rw [← Finset.sum_mul]
    rfl
  have hB' : ∀ u : Zd d L, ∑ G ∈ TSP (n - KLwIn J + 1), Bout G u =
      ∑ G ∈ KLTSPlong (n - KLwIn J + 1) (sigmaOut σ J) π',
        BAGamma d L (n - KLwIn J + 1) M t G (sigmaOut σ J) (BAdeltaOut J a u) := fun u => by
    simp only [KLTSPlong, hBout, Finset.sum_filter]
  unfold BAKpi
  rw [hlayer, Finset.sum_filter, Finset.sum_congr rfl hpt, KLsum_cut hJd hn2 f]
  simp only [hf]
  rw [KInduct_sum3]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [hA' u, hB' u]

/-- **`baKpi_cut` in the shape of `KLKpi_cut`** (kernel `S = 1`): `K^{(π)} = Σ_u Σ_w t A(u) 1_{uw} K^{(π')}(σ_out, a_out(w))`; the band's `S^{(B)}_{uw}`
is the identity matrix `1` here (`S = 1`, `Finset.sum_ite_eq`).  For a generic induction whose hypothesis carries a kernel `S`. -/
theorem baKpi_cut_S {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n)
    (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (t : ℝ) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π)
    (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d L) :
    BAKpi d L n M t σ a π = ∑ u : Zd d L, ∑ w : Zd d L, (t : ℂ) *
      (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d L => δ (Fin.last _) = u),
        BASigmaPi d L (KLwIn J + 1) M t (sigmaIn σ J) ∅ δ *
          ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
            BAThetaOf M t (sigmaIn σ J k) (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
      (1 : Matrix (Zd d L) (Zd d L) ℂ) u w *
      BAKpi d L (n - KLwIn J + 1) M t (sigmaOut σ J) (BAdeltaOut J a w) ((π.erase J).image (KLshiftOut J)) := by
  rw [baKpi_cut hn M t σ hF₀ hπ hJπ hinner a]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp [Matrix.one_apply]

end CutThm

/-! ### The cut over the abstract data of the generic step -/

section Abstract

/-- **`baKpi_cut` over the abstract data of `IndStepAbs`** (`Loop/KLIndStepB.lean:77`): the index family `ι` with sizes `L`, couplings `g`,
energies `E`, the self-energy `m`, times `t`, the molecule weight `Sig = BASig` and the leaf edges `TH i = Θ^{(·,·)}` of the BA data.  The
summand `A(u)` of the cut is, verbatim, the summand of the left side of `IndStepAbs d (KLwIn J + 1) L Bp (BASig d (KLwIn J + 1) L g E m t) TH`
at the root `r = Fin.last _` of the charges `sigmaIn σ J` (`σin_last = σ_j ≠ σ_i = σin_0` when `J` is long, as `J ∈ KLFlong F₀ σ`) and the labels
`a ∘ BAinVinv J`, so the generic step applies with `Iff.rfl` (`KLindStepAt_iff`) or a one-line bridge. -/
theorem baKpi_cut_abs {ι : Type} (d : ℕ) (L : ι → ℕ) [∀ i, NeZero (L i)] (g E : ι → ℝ) (m : ι → ℂ) (t : ι → ℝ)
    (i : ι) {n : ℕ} [NeZero n] {J : Fin n × Fin n} (hn : 3 ≤ n) (σ : Fin n → Bool)
    {F₀ : Finset (Fin n × Fin n)} (hF₀ : F₀ ∈ TSP n) {π : Finset (Fin n × Fin n)} (hπ : KLFlong F₀ σ = π)
    (hJπ : J ∈ π) (hinner : ∀ e ∈ π, KLArcLe e J → e = J) (a : Fin n → Zd d (L i)) :
    BAKpi d (L i) n (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) σ a π =
      ∑ u : Zd d (L i), (t i : ℂ) *
        (∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn J + 1) → Zd d (L i) => δ (Fin.last _) = u),
          BASig d (KLwIn J + 1) L g E m t i (sigmaIn σ J) δ *
            ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn J)),
              BAThetaOf (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i) (sigmaIn σ J k)
                (sigmaIn σ J (k + 1)) (a (BAinVinv J k)) (δ k)) *
        BAKpi d (L i) (n - KLwIn J + 1) (BAMsigma d (L i) (BAMB d (L i) (g i) ((E i : ℝ) : ℂ) (m i))) (t i)
          (sigmaOut σ J) (BAdeltaOut J a u) ((π.erase J).image (KLshiftOut J)) :=
  baKpi_cut hn _ (t i) σ hF₀ hπ hJπ hinner a

end Abstract

/-! ## 5. The layer `π = ∅` -/

section Empty

/-- **`K^{(∅)}` through a root leaf `r`**: `K^{(∅)}(σ,a) = Σ_b Θ_t^{(σ_r,σ_{r+1})}(a_r, b) X_b` with
`X_b = Σ_{δ_r = b} Σ^{(∅)}(δ) ∏_{i ≠ r} Θ_t^{(σ_i,σ_{i+1})}(a_i, δ_i)`, the summand of `IndStepAbs` (`baKpi_eq_sum_SigmaPi` and the fibres of
`δ ↦ δ_r`; the BA twin of `KLInduct_Kpi_empty_slice`, `Loop/KLInduct.lean:781`). -/
theorem baKpi_empty_slice {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) (r : Fin n) :
    BAKpi d L n M t σ a ∅ =
      ∑ b : Zd d L, BAThetaOf M t (σ r) (σ (r + 1)) (a r) b *
        ∑ δ ∈ Finset.univ.filter (fun δ : Fin n → Zd d L => δ r = b),
          BASigmaPi d L n M t σ ∅ δ *
            ∏ i ∈ Finset.univ.erase r, BAThetaOf M t (σ i) (σ (i + 1)) (a i) (δ i) := by
  rw [baKpi_eq_sum_SigmaPi, ← Finset.sum_fiberwise Finset.univ (fun δ : Fin n → Zd d L => δ r)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  have hb : δ r = b := (Finset.mem_filter.1 hδ).2
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r), hb]
  ring

/-- **The layer `π = ∅` when every leaf has an `ℓ¹` bound**: `|K^{(∅)}| ≤ C_Σ S^n` from the molecule bound `|Σ^{(∅)}| ≤ C_Σ` and
`Σ_b |Θ_t^{(σ_v,σ_{v+1})}(x, b)| ≤ S` for every leaf `v` and label `x` (the BA twin of `KLInduct_Kpi_empty_short`, `Loop/KLInduct.lean:799`;
used when every leaf is short, `σ_v = σ_{v+1}`, by property 5', `KInduct_theta_l1`).  The molecule bound is K07's `(eq:molecule-decay)`. -/
theorem baKpi_empty_short {d L : ℕ} [NeZero L] {n : ℕ} [NeZero n] (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (t : ℝ) (σ : Fin n → Bool) (a : Fin n → Zd d L) {Cm S : ℝ} (hCm : ∀ δ, ‖BASigmaPi d L n M t σ ∅ δ‖ ≤ Cm)
    (hS : ∀ (v : Fin n) (x : Zd d L), ∑ b, ‖BAThetaOf M t (σ v) (σ (v + 1)) x b‖ ≤ S) :
    ‖BAKpi d L n M t σ a ∅‖ ≤ Cm * S ^ n := by
  have hCm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 0)
  rw [baKpi_eq_sum_SigmaPi]
  have hprod : ∑ δ : Fin n → Zd d L, ∏ v, ‖BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v)‖
      = ∏ v, ∑ b, ‖BAThetaOf M t (σ v) (σ (v + 1)) (a v) b‖ := by
    have := (Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Zd d L)))
      (fun v x => ‖BAThetaOf M t (σ v) (σ (v + 1)) (a v) x‖)).symm
    rw [Fintype.piFinset_univ] at this
    exact this
  calc ‖∑ δ : Fin n → Zd d L, BASigmaPi d L n M t σ ∅ δ * ∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v)‖
      ≤ ∑ δ : Fin n → Zd d L, ‖BASigmaPi d L n M t σ ∅ δ * ∏ v, BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ δ : Fin n → Zd d L, Cm * ∏ v, ‖BAThetaOf M t (σ v) (σ (v + 1)) (a v) (δ v)‖ := by
        refine Finset.sum_le_sum fun δ _ => ?_
        rw [norm_mul, norm_prod]
        exact mul_le_mul_of_nonneg_right (hCm δ) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = Cm * ∏ v, ∑ b, ‖BAThetaOf M t (σ v) (σ (v + 1)) (a v) b‖ := by
        rw [← Finset.mul_sum, hprod]
    _ ≤ Cm * ∏ _v : Fin n, S :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun v _ => hS v (a v))) hCm0
    _ = Cm * S ^ n := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Empty

/-! ## 6. Compiled nonempty instances

Datum: the merged flow point `P` of `(d, L) = (3, 4)` (`BA/MFixedPoint.lean:893`; `P.real : BAReal 3 4 P.g0 P.m0.im P.E P.m0`,
`0 < P.g0 ≤ 10`), `Λ = 10`, `κ = Im m₀ > 0`, `W = 2` (`W^d = 8`), `t = 1/2`.  The base levels at `n = 1, 2, 3`: every deterministic hypothesis
is discharged (`baKsolve`, `baTreeRep` and the properties 5, 5' of `lem_propTH` are theorems on `main`).  The cut at `n = 4`,
`π = {(0,2)}`, `σ = (+,+,-,+)` (`TSP 4 = {∅, {(0,2)}, {(1,3)}}`: an inner and an outer triangle), and at `n = 5`, `π = {(0,2),(2,4)}`,
`σ = (+,+,-,+,+)` (mixed charges, both edges long and innermost; at either cut an inner triangle and an outer quadrilateral, `π' = {(1,3)}`
resp. `{(0,2)}`), with distinct labels of `Z_4^3`.  Only `IndStepAbs` (K09a's pin) is a hypothesis, of the bridge example. -/

namespace KInductInst

open RBM.BA.MFixedPointInst

/-- `𝒦^{(1)} = m(σ_0)` (`baKsol_one`) at the flow point, `W = 2`, `t = 1/2`. -/
example :=
  baKsol_one 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    ![true] ![![0, 0, 0]]

/-- `(Kn2sol)` (`baKsol_two`) at the flow point: the `2`-loop `(+,-)` with labels `(0,0,0)`, `(1,0,0)`. -/
example :=
  baKsol_two 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    ![true, false] ![![0, 0, 0], ![1, 0, 0]]

/-- `(Kn3sol)` (`baKsol_three`) at the flow point: the `3`-loop `(+,-,+)` with three distinct labels. -/
example :=
  baKsol_three 3 P.real.1.1 P.g0_pos (L := 4) (by norm_num) 2 P.real (t := 1 / 2) ⟨by norm_num, by norm_num⟩
    ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]

/-- `baKBoundAt_one` at the flow point (`n = 1`, `W = 2`, `t = 1/2`, `τ = 1`): `|𝒦^{(1)}| ≤ C L^τ`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true] ![![0, 0, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ 0 := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_one 3 10 P.m0.im 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) ![true] ![![0, 0, 0]]⟩

/-- `baKBoundAt_two` at the flow point (`n = 2`, `W = 2`, `t = 1/2`, `τ = 1`): `|𝒦^{(2)}| ≤ C L^τ (W^{-d} B_{t,0})`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, false] ![![0, 0, 0], ![1, 0, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ 1 := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_two (d := 3) le_rfl (Λ := 10) (by norm_num) P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) ![true, false] ![![0, 0, 0], ![1, 0, 0]]⟩

/-- `baKBoundAt_three` at the flow point (`n = 3`, `W = 2`, `t = 1/2`, `τ = 1`): `|𝒦^{(3)}| ≤ C L^τ (W^{-d} B_{t,0})²`. -/
example : ∃ C : ℝ, 0 < C ∧
    ‖BAKsol 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (PropSpin P.m0) (1 / 2)
        (KLloopOf 3 4 ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]])‖
      ≤ C * (4 : ℝ) ^ (1 : ℝ) * (((2 : ℝ) ^ 3)⁻¹ * Bparam 3 4 P.g0 (1 / 2) 0) ^ 2 := by
  obtain ⟨C, hC, H⟩ := baKBoundAt_three (d := 3) le_rfl (Λ := 10) (by norm_num) P.real.1.1 1 one_pos
  exact ⟨C, hC, H 4 (by norm_num) 2 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2)
    (by norm_num) (by norm_num) ![true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0]]⟩

/-- **`baKpi_cut`** at the flow point, `n = 4`: `σ = (+,+,-,+)`, `F₀ = π = {(0,2)}`, `J = (0,2)` (`σ_0 ≠ σ_2`: the chord is long), `π' = ∅`,
the inner and the outer polygon are triangles, four distinct labels. -/
example :=
  baKpi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
    (F₀ := {((0 : Fin 4), (2 : Fin 4))}) (by rw [TSP_four]; simp) (π := {((0 : Fin 4), (2 : Fin 4))})
    (by decide) (Finset.mem_singleton_self _) (fun e he _ => Finset.mem_singleton.1 he)
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- **No hypothesis on `M`** (0350 C2): `baKpi_cut` at the same cut for a non-symmetric, non-translation-invariant, charge-dependent
`M(σ)` (one nonzero entry `(0, e₁)`, value `1` for `σ = +`, `2` for `σ = -`), `t = 1/2`. -/
example :=
  baKpi_cut (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
    (fun s : Bool => Matrix.of fun x y : Zd 3 4 => if x = ![0, 0, 0] ∧ y = ![1, 0, 0] then (if s then (1 : ℂ) else 2) else 0)
    (1 / 2) ![true, true, false, true]
    (F₀ := {((0 : Fin 4), (2 : Fin 4))}) (by rw [TSP_four]; simp) (π := {((0 : Fin 4), (2 : Fin 4))})
    (by decide) (Finset.mem_singleton_self _) (fun e he _ => Finset.mem_singleton.1 he)
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- **`baKpi_cut_S`** (the shape of `KLKpi_cut` at `S = 1`) at the same data. -/
example :=
  baKpi_cut_S (d := 3) (L := 4) (n := 4) (J := ((0 : Fin 4), (2 : Fin 4))) (by norm_num)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true]
    (F₀ := {((0 : Fin 4), (2 : Fin 4))}) (by rw [TSP_four]; simp) (π := {((0 : Fin 4), (2 : Fin 4))})
    (by decide) (Finset.mem_singleton_self _) (fun e he _ => Finset.mem_singleton.1 he)
    ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]]

/-- The two-edge layer `{(0,2),(2,4)}` of `TSP 5` (both diagonals, crossing-free). -/
private theorem KInduct_F5_mem :
    ({((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)) ∈ TSP 5 := by decide

/-- Both edges of `{(0,2),(2,4)}` are long for the charges `(+,+,-,+,+)` (`σ_0 ≠ σ_2`, `σ_2 ≠ σ_4`). -/
private theorem KInduct_F5_long :
    KLFlong ({((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5))
        ![true, true, false, true, true] = {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} := by decide

/-- `(0,2)` is innermost in `{(0,2),(2,4)}`. -/
private theorem KInduct_F5_inner02 : ∀ e ∈ ({((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} :
    Finset (Fin 5 × Fin 5)), KLArcLe e ((0 : Fin 5), (2 : Fin 5)) → e = ((0 : Fin 5), (2 : Fin 5)) := by
  intro e he h
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · rfl
  · exact absurd h.2 (by decide)

/-- `(2,4)` is innermost in `{(0,2),(2,4)}`. -/
private theorem KInduct_F5_inner24 : ∀ e ∈ ({((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))} :
    Finset (Fin 5 × Fin 5)), KLArcLe e ((2 : Fin 5), (4 : Fin 5)) → e = ((2 : Fin 5), (4 : Fin 5)) := by
  intro e he h
  simp only [Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · exact absurd h.1 (by decide)
  · rfl

/-- The sizes and the outer layer of the two cuts of the pentagon: `(0,2)` gives `π' = {(1,3)}` and `(2,4)` gives `π' = {(0,2)}`, both with
an inner triangle (`n_in = 3`) and an outer quadrilateral (`n_out = 4`). -/
example : (({((2 : Fin 5), (4 : Fin 5))} : Finset (Fin 5 × Fin 5)).image (KLshiftOut ((0 : Fin 5), (2 : Fin 5))))
      = {((1 : Fin 4), (3 : Fin 4))} ∧ KLwIn ((0 : Fin 5), (2 : Fin 5)) + 1 = 3 ∧
    5 - KLwIn ((0 : Fin 5), (2 : Fin 5)) + 1 = 4 ∧
    (({((0 : Fin 5), (2 : Fin 5))} : Finset (Fin 5 × Fin 5)).image (KLshiftOut ((2 : Fin 5), (4 : Fin 5))))
      = {((0 : Fin 4), (2 : Fin 4))} ∧ KLwIn ((2 : Fin 5), (4 : Fin 5)) + 1 = 3 ∧
    5 - KLwIn ((2 : Fin 5), (4 : Fin 5)) + 1 = 4 :=
  ⟨by decide, rfl, rfl, by decide, rfl, rfl⟩

/-- **`baKpi_cut`** at the flow point, `n = 5`, the two-edge layer `π = {(0,2),(2,4)}` with the mixed charges `σ = (+,+,-,+,+)`, cut at `J = (0,2)`
(`π' = {(1,3)}`), five distinct labels. -/
example :=
  baKpi_cut (d := 3) (L := 4) (n := 5) (J := ((0 : Fin 5), (2 : Fin 5))) (by norm_num)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true, true]
    (F₀ := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_mem
    (π := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_long (by simp)
    KInduct_F5_inner02 ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]]

/-- **`baKpi_cut`** at the same data, cut at `J = (2,4)` (`π' = {(0,2)}`). -/
example :=
  baKpi_cut (d := 3) (L := 4) (n := 5) (J := ((2 : Fin 5), (4 : Fin 5))) (by norm_num)
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) ![true, true, false, true, true]
    (F₀ := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_mem
    (π := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_long (by simp)
    KInduct_F5_inner24 ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]]

/-- **`baKpi_cut_abs`**: the same cut over the abstract data `ι = Unit`, `L = 4`, `g = g₀`, `E`, `m = m₀`, `t = 1/2` (`BASig` at `Unit`). -/
example :=
  baKpi_cut_abs (ι := Unit) 3 (fun _ => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => 1 / 2) ()
    (n := 5) (J := ((0 : Fin 5), (2 : Fin 5))) (by norm_num) ![true, true, false, true, true]
    (F₀ := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_mem
    (π := {((0 : Fin 5), (2 : Fin 5)), ((2 : Fin 5), (4 : Fin 5))}) KInduct_F5_long (by simp)
    KInduct_F5_inner02 ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]]

/-- **The bridge to the generic step**: the summand `A(u)` of `baKpi_cut_abs` is, verbatim, the summand of `IndStepAbs` at the inner size `3`, the root
`Fin.last _` of the charges `sigmaIn σ J` (`σin_last = σ_2 ≠ σ_0 = σin_0`, checked by `decide`) and the labels `a ∘ BAinVinv J`: a bound `IndStepAbs`
for the BA molecule weight `BASig` and the leaf edges `Θ` is a bound on `Σ_u |A(u)|` (the generic step's input), with no change of shape. -/
example (h : IndStepAbs (ι := Unit) 3 3 (fun _ => 4) (fun _ => Bparam 3 4 P.g0 (1 / 2) 0)
    (BASig 3 3 (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E) (fun _ => P.m0) (fun _ => (1 : ℝ) / 2))
    (fun _ s s' => BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) s s')) :
    ∃ C : ℝ, 0 < C ∧
      ∑ u : Zd 3 4, ‖∑ δ ∈ Finset.univ.filter (fun δ : Fin (KLwIn ((0 : Fin 5), (2 : Fin 5)) + 1) → Zd 3 4 =>
            δ (Fin.last _) = u),
          BASig 3 (KLwIn ((0 : Fin 5), (2 : Fin 5)) + 1) (fun _ : Unit => 4) (fun _ => P.g0) (fun _ => P.E)
              (fun _ => P.m0) (fun _ => (1 : ℝ) / 2) ()
              (sigmaIn ![true, true, false, true, true] ((0 : Fin 5), (2 : Fin 5))) δ *
            ∏ k ∈ Finset.univ.erase (Fin.last (KLwIn ((0 : Fin 5), (2 : Fin 5)))),
              BAThetaOf (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2)
                (sigmaIn ![true, true, false, true, true] ((0 : Fin 5), (2 : Fin 5)) k)
                (sigmaIn ![true, true, false, true, true] ((0 : Fin 5), (2 : Fin 5)) (k + 1))
                (![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0], ![0, 1, 0]]
                  (BAinVinv ((0 : Fin 5), (2 : Fin 5)) k)) (δ k)‖
        ≤ C * (4 : ℝ) ^ (1 : ℝ) * (Bparam 3 4 P.g0 (1 / 2) 0) ^ 1 := by
  obtain ⟨C, hC, H⟩ := h 1 one_pos
  exact ⟨C, hC, H () _ (Fin.last _) (by decide) (fun k => ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0],
    ![0, 1, 0]] (BAinVinv ((0 : Fin 5), (2 : Fin 5)) k))⟩

/-- **`baKpi_empty_slice`** at the flow point: `n = 4`, `σ = (+,+,-,+)`, the root `r = 1`. -/
example :=
  baKpi_empty_slice (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2)
    ![true, true, false, true] ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] 1

/-- **`baKpi_empty_short`** at the flow point: all charges equal (every leaf is short), `n = 4`; the leaf constant `S > 0` is the uniform `ℓ¹` bound of the
short leaf (`KInduct_theta_l1`, property 5', `d = 1 + 2`), the molecule bound is the finite supremum of `|Σ^{(∅)}|` over the labels `δ` (it is
K07's `(eq:molecule-decay)` in general). -/
example : ∃ S : ℝ, 0 < S ∧ ∃ Cm : ℝ,
    ‖BAKpi 3 4 4 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (fun _ => true)
      ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] ∅‖ ≤ Cm * S ^ 4 := by
  obtain ⟨S, hS0, hS⟩ := KInduct_theta_l1 (k := 1) (by norm_num) (Λ := 10) (by norm_num) P.real.1.1
  obtain ⟨Cm, hCm⟩ := Finite.bddAbove_range (fun δ : Fin 4 → Zd 3 4 => ‖BASigmaPi 3 4 4
    (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0)) (1 / 2) (fun _ => true) ∅ δ‖)
  exact ⟨S, hS0, Cm, baKpi_empty_short (d := 3) (L := 4) (n := 4) (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
    (1 / 2) (fun _ => true) ![![0, 0, 0], ![1, 0, 0], ![2, 0, 0], ![3, 0, 0]] (fun δ => hCm ⟨δ, rfl⟩)
    (fun v x => hS 4 (by norm_num) P.g0 P.g0_pos P.g0_le P.E P.m0 P.real (1 / 2) (by norm_num) (by norm_num) true x)⟩

end KInductInst

end RBM.BA
