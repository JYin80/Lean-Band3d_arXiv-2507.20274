/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Loop.KLWard
import RBM3D.BA.KBase
import RBM3D.BA.Ward
import RBM3D.BA.KKernel

/-!
# Stage K, row K02 (BA instance): Ward's identity `lem_WI_K` for the block Anderson `K`-loops

Ticket T2369 (design BA-DK, `docs/reports/T2360-design.md` §3 (d), §4 row K02).  `baK_ward` is
`wardS_holds` (`RBM3D/Loop/KLWard.lean`) at the block Anderson data `S = 1`, `m = PropSpin m`,
`M = BAMLoop d L W (BAMsigma d L M^{(B)})`.  The inputs, one by one:

* `KernelFacts 1`: `kernelFacts_one`;
* `Im m > 0`: `BAReal`; `PropSpin m false = conj (PropSpin m true)`: by definition;
* the flip of `BAMLoop` (`BAKWard_BAMLoop_flip`): `M(-) = (M^{(B)})^*` and `M^{(B)}` is symmetric
  (`BAMB_symm`);
* the rotation of `BAMLoop` (`BAKWard_BAMLoop_rot`): the cyclic product of `BAMLoop` (`σ_i` on the
  edge `(a_{i-1}, a_i)`); private, the public `BAMLoop_rot` is K03's;
* the `M`-loop identity at `t = 0` (`BAKWard_zero`): `∑_x 𝓜^{(n+1)}_{(+,μ,-),(a,x)}` carries `x` on
  two factors, `M(-)_{a_{n-1} x} M(+)_{x a_0}`, and the entrywise resolvent identity
  `M - M^* = 2 i Im m · M^* M` (`BAKWard_resolvent`, `Im (E + m) = Im m > 0`) closes it;
  `BAMB_ward_row` is only the diagonal entry of this identity and is not used;
* the level-`2` identity: the `(Kn2sol)` clause, `BAMss_pm_eq`, `BAK_row_sum`,
  `BATheta_row_sum_pm`.

`BAKward` itself (`BAKsol` under `BAKsolve`) is not proved here: it is `baK_ward` composed with the
existence of the family (K03, assembled at K12).
-/

set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false

noncomputable section

open Matrix

namespace RBM.BA

open RBM RBM.Loop RBM.Gauss

section KWard

variable (d L W : ℕ) [NeZero L]

/-! ## 1. The flip of `BAMLoop` -/

/-- `M(¬σ)_{xy} = conj M(σ)_{xy}` for `M(+) = M`, `M(-) = M^*`, `M` symmetric. -/
private theorem BAKWard_Msigma_not (M : Matrix (Zd d L) (Zd d L) ℂ) (hs : ∀ x y, M x y = M y x)
    (s : Bool) (x y : Zd d L) :
    BAMsigma d L M (!s) x y = (starRingEnd ℂ) (BAMsigma d L M s x y) := by
  cases s <;> simp [BAMsigma, Matrix.conjTranspose_apply, hs x y]

omit [NeZero L] in
private theorem BAKWard_prod_flip (N : Bool → Zd d L → Zd d L → ℂ)
    (hN : ∀ s x y, N (!s) x y = (starRingEnd ℂ) (N s x y)) (σ : List Bool)
    (p : List (Zd d L × Zd d L)) :
    (((σ.map not).zip p).map fun q => N q.1 q.2.1 q.2.2).prod
      = (starRingEnd ℂ) (((σ.zip p).map fun q => N q.1 q.2.1 q.2.2).prod) := by
  induction σ generalizing p with
  | nil => simp
  | cons s σ ih =>
    cases p with
    | nil => simp
    | cons q p => simp [List.zip_cons_cons, hN, ih]

omit [NeZero L] in
/-- The flip of `BAMLoop`: `𝓜_{-σ,a} = conj 𝓜_{σ,a}`. -/
private theorem BAKWard_BAMLoop_flip (M : Bool → Matrix (Zd d L) (Zd d L) ℂ)
    (hN : ∀ s x y, M (!s) x y = (starRingEnd ℂ) (M s x y)) (σ : List Bool) (a : List (Zd d L)) :
    BAMLoop d L W M ⟨σ.map not, a⟩ = (starRingEnd ℂ) (BAMLoop d L W M ⟨σ, a⟩) := by
  unfold BAMLoop
  simp only [LoopIdx.length]
  rw [map_mul, BAKWard_prod_flip d L (fun s x y => M s x y) hN]
  congr 1
  simp [map_pow, map_inv₀]


/-! ## 2. The rotation of `BAMLoop` -/

private theorem BAKWard_zip_rotate {α β : Type*} (l₁ : List α) (l₂ : List β) (h : l₁.length = l₂.length)
    (k : ℕ) : (l₁.zip l₂).rotate k = (l₁.rotate k).zip (l₂.rotate k) := by
  simp only [List.zip_eq_zipWith]
  exact List.zipWith_rotate_distrib _ _ _ _ h

omit [NeZero L] in
/-- The rotation of `BAMLoop`. -/
private theorem BAKWard_BAMLoop_rot (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (s : Bool) (b : Zd d L)
    (σ : List Bool) (a : List (Zd d L)) (h : σ.length = a.length) :
    BAMLoop d L W M ⟨s :: σ, b :: a⟩ = BAMLoop d L W M ⟨σ ++ [s], a ++ [b]⟩ := by
  have e1 : ((a ++ [b]).rotate a.length) = b :: a := by
    simp [List.rotate_append_length_eq a [b]]
  have e2 : ((b :: a).rotate 1) = a ++ [b] := by simp [List.rotate_cons_succ]
  have e3 : ((s :: σ).rotate 1) = σ ++ [s] := by simp [List.rotate_cons_succ]
  have e4 : (((b :: a).rotate a.length).rotate 1) = b :: a := by
    rw [List.rotate_rotate]
    have : (b :: a).length = a.length + 1 := rfl
    rw [← this, List.rotate_length]
  have key : (σ ++ [s]).zip (((a ++ [b]).rotate a.length).zip (a ++ [b]))
      = ((s :: σ).zip (((b :: a).rotate a.length).zip (b :: a))).rotate 1 := by
    have h1 : ((b :: a).rotate a.length).length = (b :: a).length := List.length_rotate _ _
    rw [BAKWard_zip_rotate _ _ (by simp [h1, h]), BAKWard_zip_rotate _ _ (by simp [h1]), e2, e3, e4, e1]
  unfold BAMLoop
  simp only [LoopIdx.length, List.length_cons, List.length_append, List.length_singleton, List.length_nil, zero_add, Nat.add_sub_cancel]
  rw [key, List.map_rotate]
  congr 1
  exact (List.rotate_perm _ 1).prod_eq.symm

/-! ## 3. The two loops of the `t = 0` identity -/

omit [NeZero L] in
/-- The loop `(s, μ; a)`, `|μ| = k`, `|a| = k + 1`: `σ_0 = s` on `(a_k, a_0)`, `σ_{i+1} = μ_i` on `(a_i, a_{i+1})`. -/
private theorem BAKWard_pm (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (s : Bool) (μ : List Bool)
    (a : List (Zd d L)) (k : ℕ) (hμ : μ.length = k) (ha : a.length = k + 1) :
    BAMLoop d L W M ⟨s :: μ, a⟩ = (((W : ℂ) ^ d)⁻¹) ^ k *
      ((∏ i ∈ Finset.range k, M (μ.getD i false) (a.getD i 0) (a.getD (i + 1) 0))
        * M s (a.getD k 0) (a.getD 0 0)) := by
  rw [BAMLoop_apply d L W M ⟨s :: μ, a⟩ (k + 1) (by omega) (by simp [hμ]) ha, Finset.prod_range_succ',
    Nat.add_sub_cancel]
  have hmod : ∀ i, i < k + 1 → (i + 1 + k) % (k + 1) = i := by
    intro i hi
    rw [show i + 1 + k = i + (k + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  dsimp only
  congr 2
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [hmod i (by omega), List.getD_cons_succ]
  · rw [show (0 + k) % (k + 1) = k from by rw [zero_add]; exact Nat.mod_eq_of_lt (by omega)]
    simp

omit [NeZero L] in
/-- The loop `(+, μ, -; a, x)`: `σ_0 = +` on `(x, a_0)`, `σ_{i+1} = μ_i` on `(a_i, a_{i+1})`, the last charge `-` on
`(a_k, x)`. -/
private theorem BAKWard_full (M : Bool → Matrix (Zd d L) (Zd d L) ℂ) (μ : List Bool)
    (a : List (Zd d L)) (x : Zd d L) (k : ℕ) (hμ : μ.length = k) (ha : a.length = k + 1) :
    BAMLoop d L W M ⟨true :: μ ++ [false], a ++ [x]⟩ = (((W : ℂ) ^ d)⁻¹) ^ (k + 1) *
      ((∏ i ∈ Finset.range k, M (μ.getD i false) (a.getD i 0) (a.getD (i + 1) 0))
        * M true x (a.getD 0 0) * M false (a.getD k 0) x) := by
  rw [BAMLoop_apply d L W M ⟨true :: μ ++ [false], a ++ [x]⟩ (k + 2) (by omega) (by simp [hμ])
    (by simp [ha])]
  have e : k + 2 - 1 = k + 1 := rfl
  rw [e, Finset.prod_range_succ, Finset.prod_range_succ']
  have hmod : ∀ i, i < k + 1 → (i + 1 + (k + 1)) % (k + 2) = i := by
    intro i hi
    rw [show i + 1 + (k + 1) = i + (k + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hxa : (a ++ [x]).getD (k + 1) 0 = x := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [ha]
  have hlast : (k + 1 + (k + 1)) % (k + 2) = k := by
    rw [show k + 1 + (k + 1) = k + (k + 2) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hfirst : (0 + (k + 1)) % (k + 2) = k + 1 := by
    rw [zero_add, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [hlast, hfirst, hxa]
  have hlast' : (true :: μ ++ [false]).getD (k + 1) false = false := by
    rw [List.cons_append, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega)]
    simp [hμ]
  have hfirst' : (a ++ [x]).getD 0 0 = a.getD 0 0 := List.getD_append _ _ _ _ (by omega)
  have hak : (a ++ [x]).getD k 0 = a.getD k 0 := List.getD_append _ _ _ _ (by omega)
  have hfirst'' : (true :: μ ++ [false]).getD 0 false = true := by
    rw [List.cons_append, List.getD_cons_zero]
  rw [hlast', hfirst', hak, hfirst'']
  have hmid : ∀ i ∈ Finset.range k,
      M ((true :: μ ++ [false]).getD (i + 1) false) ((a ++ [x]).getD ((i + 1 + (k + 1)) % (k + 2)) 0)
        ((a ++ [x]).getD (i + 1) 0) = M (μ.getD i false) (a.getD i 0) (a.getD (i + 1) 0) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hmod i (by omega), List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by omega),
      List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  rw [Finset.prod_congr rfl hmid]


/-! ## 4. The resolvent identity and the `t = 0` identity -/

private theorem BAKWard_BAMB_eq (g : ℝ) (z m : ℂ) :
    BAMB d L g z m = ((g : ℂ) • PsiB d L - (z + m) • (1 : Matrix (Zd d L) (Zd d L) ℂ))⁻¹ := by
  unfold BAMB Mres
  rw [Matrix.nonsing_inv_eq_ringInverse]

/-- The entrywise resolvent identity `M - M^* = 2 i Im m · M^* M` (`G - G^* = 2 i Im w · G^* G`,
`G = (H - w)⁻¹`, `H` Hermitian, `Im w = Im m > 0`). -/
private theorem BAKWard_resolvent (g E : ℝ) (m : ℂ) (hm : 0 < m.im) :
    BAMB d L g (E : ℂ) m - (BAMB d L g (E : ℂ) m)ᴴ
      = (2 * Complex.I * (m.im : ℂ)) • ((BAMB d L g (E : ℂ) m)ᴴ * BAMB d L g (E : ℂ) m) := by
  set H : Matrix (Zd d L) (Zd d L) ℂ := (g : ℂ) • PsiB d L with hH
  have hHerm : H.IsHermitian := BAPsi_isHermitian d L g
  set w : ℂ := (E : ℂ) + m with hw
  have hwim : w.im = m.im := by simp [hw]
  have hA : IsUnit (H - w • (1 : Matrix (Zd d L) (Zd d L) ℂ)) :=
    RBM.isUnit_sub_smul_of_isHermitian hHerm (by rw [hwim]; exact hm.ne')
  set A : Matrix (Zd d L) (Zd d L) ℂ := H - w • 1 with hAdef
  have hAd : Aᴴ = H - (starRingEnd ℂ w) • 1 := by
    simp only [hAdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      hHerm.eq, Complex.star_def]
  have hA' : IsUnit Aᴴ := by
    rw [hAd]
    exact RBM.isUnit_sub_smul_of_isHermitian hHerm
      (by rw [Complex.conj_im, hwim]; exact neg_ne_zero.2 hm.ne')
  have hMA : BAMB d L g (E : ℂ) m = A⁻¹ := BAKWard_BAMB_eq d L g (E : ℂ) m
  have hdA := (Matrix.isUnit_iff_isUnit_det A).1 hA
  have hdA' := (Matrix.isUnit_iff_isUnit_det Aᴴ).1 hA'
  have h1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hdA
  have h2 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hdA
  have h3 : (Aᴴ)⁻¹ * Aᴴ = 1 := Matrix.nonsing_inv_mul Aᴴ hdA'
  have hdiff : Aᴴ - A = (2 * Complex.I * (m.im : ℂ)) • (1 : Matrix (Zd d L) (Zd d L) ℂ) := by
    rw [hAd, hAdef, sub_sub_sub_cancel_left, ← sub_smul]
    congr 1
    apply Complex.ext
    · simp [hw]
    · simp [hw]; ring
  rw [hMA, Matrix.conjTranspose_nonsing_inv]
  calc A⁻¹ - (Aᴴ)⁻¹ = (Aᴴ)⁻¹ * (Aᴴ - A) * A⁻¹ := by
        rw [mul_sub, sub_mul, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one, ← Matrix.mul_assoc,
          h3, Matrix.one_mul]
    _ = _ := by
        rw [hdiff, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]


/-- **The `t = 0` identity** of `(WI_calK)` for the block Anderson initial data `BAMLoop`. -/
private theorem BAKWard_zero (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (hW : 1 ≤ W) :
    ∀ (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 → 1 ≤ μ.length →
      ∑ x : Zd d L, BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨true :: μ ++ [false], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (m.im : ℂ))⁻¹ *
            (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨true :: μ, a⟩
              - BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m)) ⟨false :: μ, a⟩) := by
  intro μ a ha hμ1
  obtain ⟨k, hk⟩ : ∃ k, μ.length = k := ⟨_, rfl⟩
  have ha' : a.length = k + 1 := by omega
  have hres := BAKWard_resolvent d L g E m hr.1.1
  set Mb := BAMB d L g (E : ℂ) m with hMb
  simp only [BAKWard_full d L W (BAMsigma d L Mb) μ a _ k hk ha',
    BAKWard_pm d L W (BAMsigma d L Mb) _ μ a k hk ha']
  set P := ∏ i ∈ Finset.range k, BAMsigma d L Mb (μ.getD i false) (a.getD i 0) (a.getD (i + 1) 0) with hP
  set u := a.getD k 0 with hu
  set v := a.getD 0 0 with hv
  have hent := congrFun (congrFun hres u) v
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hent
  have hsum : ∑ x, BAMsigma d L Mb false u x * BAMsigma d L Mb true x v = (Mbᴴ * Mb) u v := by
    simp [BAMsigma, Matrix.mul_apply]
  have hL : ∑ x : Zd d L, (((W : ℂ) ^ d)⁻¹ ^ (k + 1) *
        (P * BAMsigma d L Mb true x v * BAMsigma d L Mb false u x))
      = ((W : ℂ) ^ d)⁻¹ ^ (k + 1) * P * (Mbᴴ * Mb) u v := by
    rw [← hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hL]
  have hT : BAMsigma d L Mb true u v = Mb u v := by simp [BAMsigma]
  have hF : BAMsigma d L Mb false u v = Mbᴴ u v := by simp [BAMsigma]
  rw [hT, hF]
  have hW0 : (W : ℂ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
  have him : (m.im : ℂ) ≠ 0 := by exact_mod_cast hr.1.1.ne'
  have hrw : ((W : ℂ) ^ d)⁻¹ ^ k * (P * Mb u v) - ((W : ℂ) ^ d)⁻¹ ^ k * (P * Mbᴴ u v)
      = ((W : ℂ) ^ d)⁻¹ ^ k * P * (2 * Complex.I * (m.im : ℂ)) * (Mbᴴ * Mb) u v := by
    linear_combination ((W : ℂ) ^ d)⁻¹ ^ k * P * hent
  have hc : (2 * Complex.I * (W : ℂ) ^ d * (m.im : ℂ))⁻¹ * (2 * Complex.I * (m.im : ℂ))
      = ((W : ℂ) ^ d)⁻¹ := by
    have hpow : (W : ℂ) ^ d ≠ 0 := pow_ne_zero d hW0
    field_simp
  rw [hrw]
  linear_combination (-(((W : ℂ) ^ d)⁻¹ ^ k * P * (Mbᴴ * Mb) u v)) * hc

/-! ## 5. The level-`2` identity -/

/-- The level-`2` identity from the `(Kn2sol)` clause. -/
private theorem BAKWard_two (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ a : Zd d L,
      ∑ x : Zd d L, K t ⟨[true, false], [a, x]⟩ = (((W : ℂ) ^ d) * ((1 - t : ℝ) : ℂ))⁻¹ := by
  intro t ht a
  have h1 : ∀ x : Zd d L, K t ⟨[true, false], [a, x]⟩ = ((W : ℂ) ^ d)⁻¹ *
      (BATheta d L g E m t true false * BAMss d L (BAMB d L g (E : ℂ) m) true false) a x :=
    fun x => hn2 t ht (true, false) a x
  simp only [h1]
  rw [← Finset.mul_sum, BAMss_pm_eq]
  have hrow : ∀ y : Zd d L, ∑ x : Zd d L, ((BAK d L g E m y x : ℝ) : ℂ) = 1 := fun y => by
    exact_mod_cast BAK_row_sum d L g E m hr.1 y
  have h2 : ∑ x : Zd d L, (BATheta d L g E m t true false *
      Matrix.map (BAK d L g E m) Complex.ofReal) a x = ∑ y : Zd d L, BATheta d L g E m t true false a y := by
    simp only [Matrix.mul_apply, Matrix.map_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, hrow, mul_one]
  rw [h2, BATheta_row_sum_pm d L g κ E m hr t ht.1 ht.2 a]
  push_cast
  rw [mul_inv]

/-! ## 6. `baK_ward` -/

/-- **`lem_WI_K` for the block Anderson `K`-loops** (`1_2:1034-1046`, `(WI_calK)`; band: `KLK_ward`).  Every family `K`
of `K`-loops on `[0,1)` over the kernel `S^{(B)}(0) = I` with the initial data `BAMLoop` (the `𝓜`-loops of `M^{(B)}`)
and `m(σ) = PropSpin m` which satisfies the level-`2` clause `(Kn2sol)` of `BAKsolve`
(`K^{(2)}_{t,(σ₁,σ₂),(a₁,a₂)} = W^{-d} (Θ^{(σ₁σ₂)}_t M^{(σ₁σ₂)})_{a₁a₂}`) satisfies, for `σ = (s, μ, -s)`,
`∑_{a_n} K^{(n)}_{t,σ,a} = (2 i W^d η_t)⁻¹ (K^{(n-1)}_{t,(+,μ),â} - K^{(n-1)}_{t,(-,μ),â})`, `η_t = (1 - t) Im m`.
This is `wardS_holds` at `S = 1`, `m(+) = m`; no hypothesis beyond `BAReal`, `1 ≤ W`, `IsKLoopS` and `(Kn2sol)`.
`BAKward` (on `BAKsol`) is `baK_ward` composed with the existence of the family (K03, assembled at K12). -/
theorem baK_ward (g κ E : ℝ) (m : ℂ) (hr : BAReal d L g κ E m) (hL : 3 ≤ L) (hW : 1 ≤ W)
    {K : ℝ → LoopIdx (Zd d L) → ℂ}
    (hK : IsKLoopS d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
      (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) (Set.Ico (0 : ℝ) 1) K)
    (hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd d L),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((W : ℂ) ^ d)⁻¹) *
        (BATheta d L g E m t σ.1 σ.2 * BAMss d L (BAMB d L g (E : ℂ) m) σ.1 σ.2) a₁ a₂) :
    ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (s : Bool) (μ : List Bool) (a : List (Zd d L)), a.length = μ.length + 1 →
      ∑ x : Zd d L, K t ⟨s :: μ ++ [!s], a ++ [x]⟩
        = (2 * Complex.I * (W : ℂ) ^ d * (((1 - t) * (PropSpin m true).im : ℝ) : ℂ))⁻¹ *
            (K t ⟨true :: μ, a⟩ - K t ⟨false :: μ, a⟩) := by
  intro t ht s μ a ha
  exact wardS_holds d L W (1 : Matrix (Zd d L) (Zd d L) ℂ) (PropSpin m)
    (BAMLoop d L W (BAMsigma d L (BAMB d L g (E : ℂ) m))) kernelFacts_one hW hr.1.1
    (by simp [PropSpin])
    (fun σ a _ _ => BAKWard_BAMLoop_flip d L W _
      (fun s x y => BAKWard_Msigma_not d L _ (BAMB_symm d L g (E : ℂ) m) s x y) σ a)
    (fun s b σ a h => BAKWard_BAMLoop_rot d L W _ s b σ a h)
    (BAKWard_zero d L W g κ E m hr hW) hK (BAKWard_two d L W g κ E m hr hn2) t ht s μ a ha

end KWard

/-! ## 7. Compiled instances: the merged flow point `P` of `(d, L) = (3, 4)`, `W = 2`

`P.real : BAReal 3 4 P.g0 (Im m₀) P.E P.m₀` (`BA/MFixedPoint.lean:893`), `g₀ ≈ 4.67`, `M^{(B)} ≠ m I`.  The identity of the
initial data at `t = 0` (`BAKWard_zero`), the flip and the rotation of `BAMLoop` are checked unconditionally at loops of
length `3`-`4` with distinct labels.  `baK_ward` is applied at `t = 1/2`, `(s, μ, a) = (+, [-], (0, e₁))` (`n = 3`); the family
`K` and its level-`2` clause `(Kn2sol)` are hypotheses of the example: they are the existence statement `BAKsolve`
(T2368, not merged), every other hypothesis (`BAReal`, `3 ≤ L`, `1 ≤ W`, `t ∈ [0,1)`, the loop) is discharged. -/

section Instances

open RBM.BA.MFixedPointInst

/-- The `t = 0` identity (`BAKWard_zero`) at the flow point, `W = 2`: the loops `(+, -, +, -)` and `(±, -, +)` with
labels `(0, e₁, e₂)`, summed over the last label `x`. -/
example : ∑ x : Zd 3 4, BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨true :: [false, true] ++ [false], [0, ![1, 0, 0], ![0, 1, 0]] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (P.m0.im : ℂ))⁻¹ *
          (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
              ⟨true :: [false, true], [0, ![1, 0, 0], ![0, 1, 0]]⟩
            - BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
              ⟨false :: [false, true], [0, ![1, 0, 0], ![0, 1, 0]]⟩) :=
  BAKWard_zero 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (by norm_num) [false, true]
    [0, ![1, 0, 0], ![0, 1, 0]] rfl (by norm_num)

/-- The flip of `BAMLoop` at the flow point: `𝓜_{(-,+,-),a} = conj 𝓜_{(+,-,+),a}`. -/
example : BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨[true, false, true].map not, [0, ![1, 0, 0], ![0, 1, 0]]⟩
      = (starRingEnd ℂ) (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨[true, false, true], [0, ![1, 0, 0], ![0, 1, 0]]⟩) :=
  BAKWard_BAMLoop_flip 3 4 2 _
    (fun s x y => BAKWard_Msigma_not 3 4 _ (BAMB_symm 3 4 P.g0 (P.E : ℂ) P.m0) s x y) _ _

/-- The rotation of `BAMLoop` at the flow point: `𝓜_{(+,-,-),(0,e₁,e₂)} = 𝓜_{(-,-,+),(e₁,e₂,0)}`. -/
example : BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨true :: [false, false], 0 :: [![1, 0, 0], ![0, 1, 0]]⟩
      = BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))
        ⟨[false, false] ++ [true], [![1, 0, 0], ![0, 1, 0]] ++ [0]⟩ :=
  BAKWard_BAMLoop_rot 3 4 2 _ true 0 [false, false] [![1, 0, 0], ![0, 1, 0]] rfl

/-- The explicit level-`2` family of `(Kn2sol)` at the flow point `P`, `W = 2` (zero off the `2`-loops). -/
private def BAKWardInst_K2 : ℝ → LoopIdx (Zd 3 4) → ℂ := fun t I =>
  match I.σ, I.a with
  | [s₁, s₂], [a₁, a₂] => (((2 : ℂ) ^ 3)⁻¹) *
      (BATheta 3 4 P.g0 P.E P.m0 t s₁ s₂ * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) s₁ s₂) a₁ a₂
  | _, _ => 0

/-- The level-`2` consequence (`n = 2`, `μ = []`, `s = +`) with **every** hypothesis discharged by hand: the family is
the explicit level-`2` formula `BAKWardInst_K2` (its `(Kn2sol)` clause holds by `rfl`), and `BAKWard_two` (the identity
`∑_x K^{(2)}_{(+,-),(a,x)} = (W^d (1 - t))⁻¹` from `BAMss_pm_eq`, `BAK_row_sum`, `BATheta_row_sum_pm`) is applied at the
flow point `P`, `W = 2`, all `t ∈ [0,1)`, all `a`. -/
example : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ a : Zd 3 4,
    ∑ x : Zd 3 4, BAKWardInst_K2 t ⟨[true, false], [a, x]⟩ = (((2 : ℂ) ^ 3) * ((1 - t : ℝ) : ℂ))⁻¹ :=
  BAKWard_two 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (K := BAKWardInst_K2) (fun t ht σ a₁ a₂ => rfl)

/-- **`baK_ward` at the flow point `P`**, `W = 2`, `t = 1/2`, `(s, μ, a) = (+, [-], (0, e₁))` (`n = 3`).  `BAReal`
(`P.real`), `3 ≤ 4`, `1 ≤ 2`, `t ∈ [0,1)` and the loop are discharged; the family `K` of `K`-loops and its level-`2` clause
`(Kn2sol)` are the existence statement `BAKsolve` (T2368, not merged: `baKsolveLe3_holds` is not available), so they
remain hypotheses of the example. -/
example (K : ℝ → LoopIdx (Zd 3 4) → ℂ)
    (hK : IsKLoopS 3 4 2 (1 : Matrix (Zd 3 4) (Zd 3 4) ℂ) (PropSpin P.m0)
      (BAMLoop 3 4 2 (BAMsigma 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0))) (Set.Ico (0 : ℝ) 1) K)
    (hn2 : ∀ t ∈ Set.Ico (0 : ℝ) 1, ∀ (σ : Bool × Bool) (a₁ a₂ : Zd 3 4),
      K t ⟨[σ.1, σ.2], [a₁, a₂]⟩ = (((2 : ℂ) ^ 3)⁻¹) *
        (BATheta 3 4 P.g0 P.E P.m0 t σ.1 σ.2 * BAMss 3 4 (BAMB 3 4 P.g0 (P.E : ℂ) P.m0) σ.1 σ.2) a₁ a₂) :
    ∑ x : Zd 3 4, K (1 / 2) ⟨true :: [false] ++ [!true], [0, ![1, 0, 0]] ++ [x]⟩
      = (2 * Complex.I * (2 : ℂ) ^ 3 * (((1 - 1 / 2) * (PropSpin P.m0 true).im : ℝ) : ℂ))⁻¹ *
          (K (1 / 2) ⟨true :: [false], [0, ![1, 0, 0]]⟩ - K (1 / 2) ⟨false :: [false], [0, ![1, 0, 0]]⟩) :=
  baK_ward 3 4 2 P.g0 P.m0.im P.E P.m0 P.real (by norm_num) (by norm_num) hK hn2 (1 / 2)
    ⟨by norm_num, by norm_num⟩ true [false] [0, ![1, 0, 0]] rfl

end Instances

end RBM.BA
