/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.Step2Defs
import RBM3D.Path.Azuma
import RBM3D.Path.Kernel
import RBM3D.Path.Stop
import RBM3D.Kernel.Evolution

/-!
# The general-`n` stopped grid Duhamel identity (`d ≥ 3`)

Paper: (3.13) `int_K-L_ST` (Lemma 3.4, `Sol_CalL`), (3.12) `def_Ustz`, and (3.18) `alu9_STime`
(Lemma 3.6, `lem:DIfREP`).

Contents: the kernel `Ugen d L g E σ v w`, which is `UN d L g (fun i => mSigma E (σ i)) v w`
(`Kernel/Evolution.lean`; slot parameter `m(σ_i) m(σ_{i+1})`, cyclic, `finRotate`), with its
additivity, identity and semigroup laws (from `ukerMat_mul` slot by slot); the algebraic telescope
`GridDuhamelN_Ugen_duhamel_telescope`; and the vocabulary `AvecN`, `martIncN`, `predIncN` along the
walk with the identity `stoppedDuhamelN_at`.  `Ugen` needs no `[NeZero k]`; `AvecN` is
`sz.STLKM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a` (`(𝓛 - 𝒦)_{u_j,σ}` of the walk),
whose measurability along the walk is `walk_measurable_loopFine` composed with
`pathH_measurable_filt`.  No exponent of this file is `d`-specific: the file uses neither `W` nor
`N` nor `L²`.

At `k = 2`, `σ = (+,-)` both slots of `Ugen` carry `m_+ m_- = |m|²`.  Every other helper is
`private` and carries the prefix `GridDuhamelN_`.
-/

noncomputable section

namespace RBM.Ind

open MeasureTheory ProbabilityTheory Filter Matrix RBM RBM.Gauss RBM.Path
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

/-! ### 1. The kernel `Ugen`: additivity, identity and semigroup laws -/

section UgenAlgebra

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `(𝒰_{v,w,σ} ∘ 𝒜)_a = Σ_b Π_i ((1 - v m_i m_{i+1} S)/(1 - w m_i m_{i+1} S))_{a_i b_i} 𝒜_b`
for a loop of length `k` ((3.12) `def_Ustz`), `m_i = m(σ_i)` at the energy `E`:
`UN` with `m i = mSigma E (σ i)`. -/
def Ugen (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) (A : (Fin k → Zd d L) → ℂ) :
    (Fin k → Zd d L) → ℂ :=
  UN d L g (fun i => mSigma E (σ i)) v w A

variable {d L g}

/-- The slot condition `‖v m(σ_i) m(σ_{i+1})‖ < 1` for `0 ≤ v < 1`, `|E| ≤ 2`. -/
private theorem GridDuhamelN_norm_slot_lt_one {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool)
    (i : Fin k) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ‖(v : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 :=
  norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (finRotate k i))

/-- `𝒰_{v,w,σ}` is additive. -/
theorem GridDuhamelN_Ugen_add (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v w (A + B) = Ugen d L g E σ v w A + Ugen d L g E σ v w B := by
  funext a
  simp only [Ugen, UN, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `𝒰_{v,v,σ} = id` for `0 ≤ v < 1`, `|E| ≤ 2` (`ukerMat_self` slot by slot). -/
theorem GridDuhamelN_Ugen_self (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (A : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v v A = A := by
  funext a
  have h1 : ∀ i : Fin k,
      uKer d L g (cycProd (fun i => mSigma E (σ i)) i) v v = 1 := fun i =>
    ukerMat_self d L g hL (GridDuhamelN_norm_slot_lt_one hE σ i hv0 hv1)
  simp only [Ugen, UN, h1, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have : ¬ ∀ i, a i = b i := fun h => hb (funext h).symm
    simp [Fintype.prod_boole, this]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- **Semigroup law** `𝒰_{v,w,σ} ∘ 𝒰_{u,v,σ} = 𝒰_{u,w,σ}` for `0 ≤ v, w < 1`, `|E| ≤ 2`
(`ukerMat_mul` slot by slot; no condition on `u`). -/
theorem GridDuhamelN_Ugen_comp (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u v w : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (hw0 : 0 ≤ w) (hw1 : w < 1)
    (A : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v w (Ugen d L g E σ u v A) = Ugen d L g E σ u w A := by
  funext a
  set ξ : Fin k → ℂ := fun i => cycProd (fun i => mSigma E (σ i)) i with hξ
  have hm : ∀ (i : Fin k) (x y : Zd d L),
      ∑ c : Zd d L, uKer d L g (ξ i) v w x c * uKer d L g (ξ i) u v c y
      = uKer d L g (ξ i) u w x y := fun i x y => by
    have h := congrFun (congrFun (ukerMat_mul d L g (u := u) hL
      (GridDuhamelN_norm_slot_lt_one hE σ i hv0 hv1)
      (GridDuhamelN_norm_slot_lt_one hE σ i hw0 hw1)) x) y
    rwa [Matrix.mul_apply] at h
  calc Ugen d L g E σ v w (Ugen d L g E σ u v A) a
      = ∑ c : Fin k → Zd d L, (∏ i, uKer d L g (ξ i) v w (a i) (c i)) *
          ∑ b : Fin k → Zd d L, (∏ i, uKer d L g (ξ i) u v (c i) (b i)) * A b := rfl
    _ = ∑ c : Fin k → Zd d L, ∑ b : Fin k → Zd d L,
          (∏ i, uKer d L g (ξ i) v w (a i) (c i) * uKer d L g (ξ i) u v (c i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = ∑ b : Fin k → Zd d L, ∑ c : Fin k → Zd d L,
          (∏ i, uKer d L g (ξ i) v w (a i) (c i) * uKer d L g (ξ i) u v (c i) (b i)) * A b :=
        Finset.sum_comm
    _ = ∑ b : Fin k → Zd d L, (∏ i, uKer d L g (ξ i) u w (a i) (b i)) * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← Finset.sum_mul]
        congr 1
        rw [← Fintype.prod_sum (fun i x => uKer d L g (ξ i) v w (a i) x *
          uKer d L g (ξ i) u v x (b i))]
        exact Finset.prod_congr rfl fun i _ => hm i (a i) (b i)
    _ = Ugen d L g E σ u w A a := rfl

variable (d L g)

/-- `𝒰_{v,w,σ}` bundled as an `AddMonoidHom`. -/
def GridDuhamelN_UgenHom (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) :
    ((Fin k → Zd d L) → ℂ) →+ ((Fin k → Zd d L) → ℂ) :=
  AddMonoidHom.mk' (Ugen d L g E σ v w) (GridDuhamelN_Ugen_add E σ v w)

@[simp] theorem GridDuhamelN_UgenHom_apply (E : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (v w : ℝ) (A : (Fin k → Zd d L) → ℂ) :
    GridDuhamelN_UgenHom d L g E σ v w A = Ugen d L g E σ v w A := rfl

variable {d L g}

/-- **The algebraic part of `int_K-L_ST` for `Ugen`** (via the clamped index):
`A_m = 𝒰_{u_0,u_m,σ} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m,σ} (A_{j+1} - 𝒰_{u_j,u_{j+1},σ} A_j)`
for times with `0 ≤ u_j < 1` at the indices `j ≤ m`.  At `k = 2`, `σ = (+,-)` both slots carry
`m_+ m_- = |m|²`. -/
theorem GridDuhamelN_Ugen_duhamel_telescope (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j)
    (hu1 : ∀ j ≤ m, u j < 1) (A : ℕ → ((Fin k → Zd d L) → ℂ)) :
    A m = Ugen d L g E σ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Ugen d L g E σ (u (j + 1)) (u m)
        (A (j + 1) - Ugen d L g E σ (u j) (u (j + 1)) (A j)) := by
  set uc : ℕ → ℝ := fun j => u (min j m) with huc
  have hc0 : ∀ j, 0 ≤ uc j := fun j => hu0 _ (min_le_right j m)
  have hc1 : ∀ j, uc j < 1 := fun j => hu1 _ (min_le_right j m)
  have hself : ∀ j, GridDuhamelN_UgenHom d L g E σ (uc j) (uc j)
      = AddMonoidHom.id ((Fin k → Zd d L) → ℂ) := fun j => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.id_apply, GridDuhamelN_UgenHom_apply]
    exact GridDuhamelN_Ugen_self hL hE σ (hc0 j) (hc1 j) B
  have hcomp : ∀ i j l, i ≤ j → j ≤ l →
      (GridDuhamelN_UgenHom d L g E σ (uc j) (uc l)).comp
        (GridDuhamelN_UgenHom d L g E σ (uc i) (uc j))
        = GridDuhamelN_UgenHom d L g E σ (uc i) (uc l) := fun i j l _ _ => by
    apply AddMonoidHom.ext
    intro B
    rw [AddMonoidHom.comp_apply, GridDuhamelN_UgenHom_apply, GridDuhamelN_UgenHom_apply,
      GridDuhamelN_UgenHom_apply]
    exact GridDuhamelN_Ugen_comp hL hE σ (hc0 j) (hc1 j) (hc0 l) (hc1 l) B
  have htel := duhamel_telescope (fun i j => GridDuhamelN_UgenHom d L g E σ (uc i) (uc j))
    hself hcomp A m
  simp only [GridDuhamelN_UgenHom_apply, huc] at htel
  rw [Nat.zero_min, min_self, sub_eq_iff_eq_add'] at htel
  rw [htel, add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  rw [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]

end UgenAlgebra

/-! ### 2. Grid-time arithmetic -/

section GridArith

variable (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

private theorem GridDuhamelN_gridStep_nonneg (hst : s n ≤ t n) : 0 ≤ gridStep s t K n :=
  div_nonneg (sub_nonneg.2 hst) (Nat.cast_nonneg _)

private theorem GridDuhamelN_gridTime_mono (hst : s n ≤ t n) {i j : ℕ} (hij : i ≤ j) :
    gridTime s t K n i ≤ gridTime s t K n j := by
  have hΔ := GridDuhamelN_gridStep_nonneg s t K n hst
  unfold gridTime
  have : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.2 hij
  nlinarith

private theorem GridDuhamelN_gridTime_nonneg (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (j : ℕ) :
    0 ≤ gridTime s t K n j := by
  have h := GridDuhamelN_gridTime_mono s t K n hst (Nat.zero_le j)
  have h0 : gridTime s t K n 0 = s n := by simp [gridTime]
  rw [h0] at h
  linarith

private theorem GridDuhamelN_gridTime_lt_one (hst : s n ≤ t n) (hK : K n ≠ 0) (ht1 : t n < 1)
    {j : ℕ} (hj : j ≤ K n) : gridTime s t K n j < 1 := by
  have h := GridDuhamelN_gridTime_mono s t K n hst hj
  rw [gridTime_last s t K n hK] at h
  linarith

end GridArith

/-! ### 3. The vocabulary `AvecN`, `martIncN`, `predIncN` and the identity `stoppedDuhamelN_at` -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- `A_j = (𝓛 - 𝒦)_{u_j,σ}` along the walk, a `k`-tensor. -/
def AvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => sz.STLKM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a

/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]`. -/
def martIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => AvecN sz E s t K n (j + 1) σ ω a -
    (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω

/-- `P_j = 𝔼[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A_j` (the
kernel is `Ugen` at the coupling `g = sz.lam n`). -/
def predIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω -
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (AvecN sz E s t K n j σ ω) a

/-- **The stopped grid Duhamel identity at one size index** (hypotheses only at
`n`): pathwise, for every `τ : PathΩ sz → ℕ`,
`A_{j∧τ} = 𝒰_{u_0,u_{j∧τ},σ} A_0 + Σ_{i<j∧τ} 𝒰_{u_{i+1},u_{j∧τ},σ} (P_i + ξ_{i+1})`.  From
`GridDuhamelN_Ugen_duhamel_telescope`: `A_{i+1} - 𝒰 A_i = predIncN_i + martIncN_i` label by label
(the conditional expectation cancels). -/
theorem stoppedDuhamelN_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) (hE : |E n| < 2)
    (hs0 : 0 ≤ s n) (hst : s n ≤ t n) (ht1 : t n < 1) (hK : K n ≠ 0) {k : ℕ}
    (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz) (hjτ : min j (τ ω) ≤ K n) :
    AvecN sz E s t K n (min j (τ ω)) σ ω =
      Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
          (AvecN sz E s t K n 0 σ ω) +
        ∑ i ∈ Finset.range (min j (τ ω)),
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
            (gridTime s t K n (min j (τ ω)))
            (predIncN sz E s t K n i σ ω + martIncN sz E s t K n i σ ω) := by
  have h := GridDuhamelN_Ugen_duhamel_telescope (g := sz.lam n) (sz.three_le_L n) hE.le σ
    (gridTime s t K n) (min j (τ ω))
    (fun i _ => GridDuhamelN_gridTime_nonneg s t K n hs0 hst i)
    (fun i hi => GridDuhamelN_gridTime_lt_one s t K n hst hK ht1 (hi.trans hjτ))
    (fun i => AvecN sz E s t K n i σ ω)
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  funext a
  simp only [predIncN, martIncN, Pi.add_apply, Pi.sub_apply]
  ring

end Vocab

end RBM.Ind
