/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Path.Expansion
import RBM3D.Path.Azuma
import RBM3D.Path.Kernel
import RBM3D.Path.Stop
import RBM3D.Kernel.Evolution

/-!
# The general-`n` stopped grid Duhamel identity and the stopped Azuma bound (`d ≥ 3`)

Ticket T2104 (ST2-27, second file).  Port of `RBM2D/Induction/GridDuhamelN.lean` at commit
`c9a24cf` (cited `GridDuhamelN:<line>`; RBM2D ticket T2137), whose telescope is a port of RBM1D
`grid_duhamel_telescope_n` (`RBM1D/Gauss/Lemma514NonAlt.lean:2662`, commit `86573b9`) and whose
vocabulary (`AvecN`, `martIncN`, `predIncN`, `StoppedDuhamelN`, `StoppedAzumaN`: RBM2D
`Induction/HierVocab.lean:387-474`) T2049 did not port.  Paper: arXiv:2507.20274, `int_K-L_ST`
(`3_5:134`), `def_Ustz`, `alu9_STime` (`3_5:218-240`) with BDG replaced by Azuma-Hoeffding
(DECISIONS §10).

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `d : Sizes` becomes `sz : Sizes d`, `Z2 L` becomes
`Zd d L`, and the `Gauss/Model`, `Hierarchy/Loops` vocabulary becomes the merged one.  The kernel
`Ugen d L g E σ v w` is the merged `UN d L g (fun i => mSigma E (σ i)) v w`
(`RBM3D/Kernel/Evolution.lean`; slot parameter `m(σ_i) m(σ_{i+1})`, cyclic, `finRotate`), so its
semigroup law comes from `ukerMat_mul` slot by slot.  `Ugen` needs no `[NeZero k]` (RBM2D had it for
`σ (i + 1)`); `AvecN` is `sz.STLKM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a`
(`(𝓛 - 𝒦)_{u_j,σ}` of the walk), whose measurability along the walk is `walk_measurable_loopFine`
composed with `pathH_measurable_filt` (RBM2D `GoodEvent_measurable_gloop`).  No exponent of RBM2D
is `d = 2`-specific in this file: the file uses neither `W` nor `N` nor `L^2`.

Reduction at `n = 2`, `σ = (+,-)` (D161, D162, D190): `Ugen_two_eq_Uop` (both slots carry
`m_+ m_- = |m|²`), `AvecN_two`, `martIncN_two`, `predIncN_two`, and
`stoppedDuhamel105_of_stoppedDuhamelN` (`StoppedDuhamelN sz (fun _ => E) s t K` gives
`StoppedDuhamel105 sz E s t K`);
`GridDuhamelN_Ugen_duhamel_telescope` at `k = 2` is the merged `Uop_duhamel_telescope`.

Dropped: nothing.  `stoppedAzumaN` is not in P.1's consumed list for this file (row 4), but it is
kept (the weighted tail of `STGridRepN` uses the same step).  Every other helper is `private` and
carries the prefix `GridDuhamelN_`.
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
for a loop of length `k` (`def_Ustz`), `m_i = m(σ_i)` at the energy `E` (RBM2D `Ugen`,
`Induction/Defs.lean:90`): the merged `UN` with `m i = mSigma E (σ i)`. -/
def Ugen (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) (A : (Fin k → Zd d L) → ℂ) :
    (Fin k → Zd d L) → ℂ :=
  UN d L g (fun i => mSigma E (σ i)) v w A

/-- The one-index kernel `uKer` is the merged `ukerMat` (same formula). -/
private theorem GridDuhamelN_uKer_eq (μ : ℂ) (v w : ℝ) :
    uKer d L g μ v w = ukerMat d L g μ v w := rfl

variable {d L g}

/-- The slot condition `‖v m(σ_i) m(σ_{i+1})‖ < 1` for `0 ≤ v < 1`, `|E| ≤ 2`. -/
private theorem GridDuhamelN_norm_slot_lt_one {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool)
    (i : Fin k) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) :
    ‖(v : ℂ) * cycProd (fun i => mSigma E (σ i)) i‖ < 1 :=
  norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (finRotate k i))

/-- `𝒰_{v,w,σ}` is additive (RBM2D `GridDuhamelN_Ugen_add`, `GridDuhamelN:62`). -/
theorem GridDuhamelN_Ugen_add (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    (A B : (Fin k → Zd d L) → ℂ) :
    Ugen d L g E σ v w (A + B) = Ugen d L g E σ v w A + Ugen d L g E σ v w B := by
  funext a
  simp only [Ugen, UN, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `𝒰_{v,v,σ} = id` for `0 ≤ v < 1`, `|E| ≤ 2` (`ukerMat_self` slot by slot; RBM2D
`GridDuhamelN:70`). -/
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
(`ukerMat_mul` slot by slot; no condition on `u`; RBM2D `GridDuhamelN:87`). -/
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

/-- `𝒰_{v,w,σ}` bundled as an `AddMonoidHom` (RBM2D `GridDuhamelN_UgenHom`, `GridDuhamelN:121`). -/
def GridDuhamelN_UgenHom (E : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ) :
    ((Fin k → Zd d L) → ℂ) →+ ((Fin k → Zd d L) → ℂ) :=
  AddMonoidHom.mk' (Ugen d L g E σ v w) (GridDuhamelN_Ugen_add E σ v w)

@[simp] theorem GridDuhamelN_UgenHom_apply (E : ℝ) {k : ℕ} (σ : Fin k → Bool)
    (v w : ℝ) (A : (Fin k → Zd d L) → ℂ) :
    GridDuhamelN_UgenHom d L g E σ v w A = Ugen d L g E σ v w A := rfl

variable {d L g}

/-- **The algebraic part of `int_K-L_ST` for `Ugen`** (port of RBM1D `grid_duhamel_telescope_n`,
`Gauss/Lemma514NonAlt.lean:2662`, commit `86573b9`, via the clamped index; RBM2D
`GridDuhamelN:133`):
`A_m = 𝒰_{u_0,u_m,σ} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m,σ} (A_{j+1} - 𝒰_{u_j,u_{j+1},σ} A_j)`
for times with `0 ≤ u_j < 1` at the indices `j ≤ m`.  At `k = 2`, `σ = (+,-)` this is the merged
`Uop_duhamel_telescope` (`Ugen_two_eq_Uop`). -/
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

/-! ### 2. The reduction at `n = 2`, `σ = (+,-)` for the kernel -/

section TwoSlots

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- At `k = 2`, `σ = (+,-)` both slots carry `m_+ m_- = |m|²` (`z conj z = normSq z`), so
`Ugen` is the merged two-index `Uop` at `ξ = |m(E)|²` (via `finTwoArrowEquiv`). -/
theorem Ugen_two_eq_Uop (E v w : ℝ) (A : (Fin 2 → Zd d L) → ℂ) (a : Fin 2 → Zd d L) :
    Ugen d L g E ![true, false] v w A a =
      Uop d L g ((Complex.normSq (mE E) : ℝ) : ℂ) v w (fun b => A ![b.1, b.2]) (a 0, a 1) := by
  have hc : ∀ i : Fin 2,
      cycProd (fun i => mSigma E ((![true, false] : Fin 2 → Bool) i)) i
        = ((Complex.normSq (mE E) : ℝ) : ℂ) := by
    intro i
    fin_cases i
    · simp [cycProd, mSigma, Complex.mul_conj]
    · simp [cycProd, mSigma, mul_comm, Complex.mul_conj]
  have hsum := Fintype.sum_equiv (finTwoArrowEquiv (Zd d L))
    (fun b : Fin 2 → Zd d L => (∏ i, uKer d L g (cycProd (fun i => mSigma E
      ((![true, false] : Fin 2 → Bool) i)) i) v w (a i) (b i)) * A b)
    (fun p : Zd d L × Zd d L => ukerMat d L g ((Complex.normSq (mE E) : ℝ) : ℂ) v w (a 0) p.1 *
      ukerMat d L g ((Complex.normSq (mE E) : ℝ) : ℂ) v w (a 1) p.2 * A ![p.1, p.2])
    (fun b => by
      have hb : (![b 0, b 1] : Fin 2 → Zd d L) = b := by
        ext i; fin_cases i <;> rfl
      simp only [hc, Fin.prod_univ_two]
      change _ * _ * A b = ukerMat d L g _ v w (a 0) (b 0) * ukerMat d L g _ v w (a 1) (b 1) *
        A ![b 0, b 1]
      rw [hb]
      rfl)
  change ∑ b : Fin 2 → Zd d L, _ = _
  rw [hsum]
  rfl

end TwoSlots

/-! ### 3. Grid-time arithmetic (re-proved; the `Expansion_`/`DuhamelTail_` versions are private) -/

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

/-! ### 4. The vocabulary `AvecN`, `martIncN`, `predIncN` and the pin `StoppedDuhamelN` -/

section Vocab

variable {d : ℕ} (sz : Sizes d)

/-- `A_j = (𝓛 - 𝒦)_{u_j,σ}` along the walk, a `k`-tensor (general-`n` `Avec`; RBM2D `AvecN`,
`HierVocab:387`).  At `k = 2`, `σ = (+,-)` it is the merged `Avec` (`AvecN_two`). -/
def AvecN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => sz.STLKM n (E n) (gridTime s t K n j) (pathH sz s t K n j ω) σ a

/-- `ξ_{j+1} = A_{j+1} - 𝔼[A_{j+1} | F_j]` (RBM2D `martIncN`, `HierVocab:395`). -/
def martIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => AvecN sz E s t K n (j + 1) σ ω a -
    (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω

/-- `P_j = 𝔼[A_{j+1} | F_j] - 𝒰_{u_j,u_{j+1},σ} A_j` (RBM2D `predIncN`, `HierVocab:402`; the
kernel is `Ugen` at the coupling `g = sz.lam n`). -/
def predIncN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n j : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (ω : PathΩ sz) : (Fin k → Zd d (sz.L n)) → ℂ :=
  fun a => (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω -
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n j) (gridTime s t K n (j + 1))
      (AvecN sz E s t K n j σ ω) a

/-- **Pin G1 (`int_K-L_ST`, `3_5:134`, general `n`, all `σ`)**: the stopped grid Duhamel
identity, pathwise.  At `k = 2`, `σ = (+,-)` it is the merged `StoppedDuhamel105`
(`stoppedDuhamel105_of_stoppedDuhamelN`).  RBM2D `StoppedDuhamelN` (`HierVocab:413`). -/
def StoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
    ∀ (n k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (j : ℕ) (ω : PathΩ sz),
      min j (τ ω) ≤ K n →
      AvecN sz E s t K n (min j (τ ω)) σ ω =
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n 0) (gridTime s t K n (min j (τ ω)))
            (AvecN sz E s t K n 0 σ ω) +
          ∑ i ∈ Finset.range (min j (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (i + 1))
              (gridTime s t K n (min j (τ ω)))
              (predIncN sz E s t K n i σ ω + martIncN sz E s t K n i σ ω)

/-- **Pin G1 at one size index** (DECISIONS §29 (4), the `_at` form of T2098: hypotheses only at
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

/-- **Pin G1 proved**: `StoppedDuhamelN sz E s t K` (RBM2D `stoppedDuhamelN`,
`GridDuhamelN:204`). -/
theorem stoppedDuhamelN (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : StoppedDuhamelN sz E s t K :=
  fun hE hs0 hst ht1 hK n _ σ τ j ω hjτ =>
    stoppedDuhamelN_at sz E s t K n (hE n) (hs0 n) (hst n) (ht1 n) (hK n) σ τ j ω hjτ

end Vocab

/-! ### 5. The reduction of the vocabulary and of the pin at `n = 2` -/

section Reduction

variable {d : ℕ} (sz : Sizes d) (E : ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- `AvecN` at `k = 2`, `σ = (+,-)`, constant energy is the merged `Avec`. -/
theorem AvecN_two (j : ℕ) (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    AvecN sz (fun _ => E) s t K n j ![true, false] ω ![a.1, a.2] = Avec sz E s t K n j ω a := rfl

/-- `martIncN` at `k = 2`, `σ = (+,-)` is the merged `martInc`. -/
theorem martIncN_two (j : ℕ) (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    martIncN sz (fun _ => E) s t K n j ![true, false] ω ![a.1, a.2] = martInc sz E s t K n j ω a :=
  rfl

/-- `predIncN` at `k = 2`, `σ = (+,-)` is the merged `predInc` (`Ugen_two_eq_Uop`). -/
theorem predIncN_two (j : ℕ) (ω : PathΩ sz) (a : Zd d (sz.L n) × Zd d (sz.L n)) :
    predIncN sz (fun _ => E) s t K n j ![true, false] ω ![a.1, a.2] = predInc sz E s t K n j ω a := by
  unfold predIncN predInc
  rw [Ugen_two_eq_Uop]
  rfl

/-- **The reduction at `n = 2`**: the general-`n` pin at the constant energy `E` and `σ = (+,-)`
gives the merged `StoppedDuhamel105`. -/
theorem stoppedDuhamel105_of_stoppedDuhamelN (h : StoppedDuhamelN sz (fun _ => E) s t K) :
    StoppedDuhamel105 sz E s t K := by
  intro hE hs0 hst ht1 hK n τ k ω hkτ
  have h1 := h (fun _ => hE) hs0 hst ht1 hK n 2 ![true, false] τ k ω hkτ
  funext a
  have h2 := congrFun h1 ![a.1, a.2]
  have e1 : ∀ (u v : ℝ) (A : (Fin 2 → Zd d (sz.L n)) → ℂ),
      Ugen d (sz.L n) (sz.lam n) E ![true, false] u v A ![a.1, a.2]
        = Uop d (sz.L n) (sz.lam n) ((Complex.normSq (mE E) : ℝ) : ℂ) u v
            (fun b => A ![b.1, b.2]) a := fun u v A => by
    rw [Ugen_two_eq_Uop]; rfl
  simp only [Pi.add_apply, Finset.sum_apply, e1] at h2 ⊢
  refine h2.trans ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  funext b
  simp only [Pi.add_apply, predIncN_two, martIncN_two]

end Reduction

/-! ### 6. Measurability along the walk -/

section Measurability

variable {d : ℕ} (sz : Sizes d) (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ)

/-- Every label of `A_j` is `filt sz j`-measurable: `AvecN` is `loopFine` of the walk minus a
constant (merged `walk_measurable_loopFine`, `pathH_measurable_filt`; RBM2D
`GoodEvent_measurable_gloop`; no window hypothesis). -/
private theorem GridDuhamelN_measurable_AvecN (j : ℕ) {k : ℕ} (σ : Fin k → Bool)
    (a : Fin k → Zd d (sz.L n)) :
    Measurable[filt sz j] (fun ω => AvecN sz E s t K n j σ ω a) :=
  ((walk_measurable_loopFine d (sz.L n) (sz.W n) (zt (E n) (gridTime s t K n j)) σ a).comp
    (pathH_measurable_filt sz s t K n j)).sub measurable_const

/-- The martingale difference `ξ_{j+1}` is `filt sz (j+1)`-strongly measurable as a tensor. -/
private theorem GridDuhamelN_stronglyMeasurable_martIncN (j : ℕ) {k : ℕ} (σ : Fin k → Bool) :
    StronglyMeasurable[filt sz (j + 1)] (martIncN sz E s t K n j σ) := by
  have hme : Measurable[filt sz (j + 1)] (martIncN sz E s t K n j σ) := by
    refine @measurable_pi_iff _ _ _ (filt sz (j + 1)) _ _ |>.mpr fun a => ?_
    have h1 := GridDuhamelN_measurable_AvecN sz E s t K n (j + 1) σ a
    have h2 : StronglyMeasurable[filt sz (j + 1)]
        (fun ω => (pathP sz)[fun ω' => AvecN sz E s t K n (j + 1) σ ω' a | filt sz j] ω) :=
      stronglyMeasurable_condExp.mono ((filt sz).mono (Nat.le_succ j))
    exact h1.sub h2.measurable
  exact hme.stronglyMeasurable

/-- `A ↦ (𝒰_{v,w,σ} A)_a` is continuous, so it preserves strong measurability. -/
private theorem GridDuhamelN_stronglyMeasurable_Ugen_apply {Ω' : Type*} {m : MeasurableSpace Ω'}
    (d L : ℕ) [NeZero L] (g E' : ℝ) {k : ℕ} (σ : Fin k → Bool) (v w : ℝ)
    {W : Ω' → (Fin k → Zd d L) → ℂ} (hW : StronglyMeasurable[m] W) (a : Fin k → Zd d L) :
    StronglyMeasurable[m] (fun ω => Ugen d L g E' σ v w (W ω) a) := by
  have hcont : Continuous (fun A : (Fin k → Zd d L) → ℂ => Ugen d L g E' σ v w A a) := by
    unfold Ugen UN
    exact continuous_finsetSum _ (fun c _ => continuous_const.mul (continuous_apply c))
  exact hcont.comp_stronglyMeasurable hW

end Measurability

/-! ### 7. A generic stopped complex Azuma step -/

section AzumaStep

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] {μ : Measure Ω'}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ'}

private def GridDuhamelN_prependZero {M : Type*} [Zero M] (f : ℕ → M) : ℕ → M
  | 0 => 0
  | j + 1 => f j

private theorem GridDuhamelN_sum_range_succ_prependZero {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), GridDuhamelN_prependZero f i = ∑ j ∈ Finset.range m, f j := by
  rw [Finset.sum_range_succ' (GridDuhamelN_prependZero f) m]
  simp [GridDuhamelN_prependZero]

/-- The complex Azuma tail for `Σ_{j<m} X_j` when `X_j` is `ℱ (j+1)`-strongly measurable and its
real and imaginary parts are conditionally sub-Gaussian given `ℱ j` with proxy `c j` (the process
`0, X_0, …, X_{m-1}, 0, …` fed to `azuma_complex` with horizon `m + 1`; as the private
`DuhamelTail_azuma_stoppedEdge`, for a scalar process; RBM2D `GridDuhamelN_azuma_step`,
`GridDuhamelN:280`). -/
private theorem GridDuhamelN_azuma_step {X : ℕ → Ω' → ℂ} {m : ℕ}
    (hX : ∀ j < m, StronglyMeasurable[ℱ (j + 1)] (X j)) {c : ℕ → ℝ≥0}
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).re) (c j) μ ∧
      HasCondSubgaussianMGF (ℱ j) (ℱ.le j) (fun ω => (X j ω).im) (c j) μ)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set Y : ℕ → Ω' → ℂ := fun i => if i ≤ m then GridDuhamelN_prependZero X i else 0 with hYdef
  set cc : ℕ → ℝ≥0 := GridDuhamelN_prependZero c with hccdef
  have hYsucc : ∀ j, j + 1 ≤ m → Y (j + 1) = X j := by
    intro j hj
    simp only [hYdef, hj, ↓reduceIte]
    rfl
  have hYzero : Y 0 = 0 := by
    simp [hYdef, GridDuhamelN_prependZero]
  have hYR : StronglyAdapted ℱ (fun i ω => (Y i ω).re) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).re)
        rw [hYsucc j hj]
        exact Complex.continuous_re.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have hYI : StronglyAdapted ℱ (fun i ω => (Y i ω).im) := by
    intro i
    cases i with
    | zero => simpa [hYzero] using stronglyMeasurable_const
    | succ j =>
      by_cases hj : j + 1 ≤ m
      · change StronglyMeasurable[ℱ (j + 1)] (fun ω => (Y (j + 1) ω).im)
        rw [hYsucc j hj]
        exact Complex.continuous_im.comp_stronglyMeasurable (hX j hj)
      · simpa [hYdef, hj] using stronglyMeasurable_const
  have h0R : HasSubgaussianMGF (fun ω => (Y 0 ω).re) (cc 0) μ := by
    simp [hYzero, hccdef, GridDuhamelN_prependZero]
  have h0I : HasSubgaussianMGF (fun ω => (Y 0 ω).im) (cc 0) μ := by
    simp [hYzero, hccdef, GridDuhamelN_prependZero]
  have hCR : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).re) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).1
  have hCI : ∀ i < m + 1 - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (fun ω => (Y (i + 1) ω).im) (cc (i + 1)) μ := by
    intro i hi
    simp only [Nat.add_sub_cancel] at hi
    rw [hYsucc i hi]
    exact (hsubG i hi).2
  have hazuma := azuma_complex (Z := Y) (c := cc) hYR hYI (m + 1) h0R h0I hCR hCI hx
  rw [NNReal.coe_sum] at hazuma
  have hsum : ∀ ω, ∑ j ∈ Finset.range m, X j ω = ∑ i ∈ Finset.range (m + 1), Y i ω := by
    intro ω
    have h3 := GridDuhamelN_sum_range_succ_prependZero (fun j => X j ω) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    simp only [hYdef, him, ↓reduceIte]
    cases i <;> rfl
  have hsumeq : ∑ i ∈ Finset.range (m + 1), (cc i : ℝ) = ∑ j ∈ Finset.range m, (c j : ℝ) := by
    have h3 := GridDuhamelN_sum_range_succ_prependZero (fun j => (c j : ℝ)) m
    rw [← h3]
    refine Finset.sum_congr rfl fun i _ => ?_
    cases i <;> rfl
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖}
      = {ω | x ≤ ‖∑ i ∈ Finset.range (m + 1), Y i ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum ω]
  rw [hset, ← hsumeq]
  exact hazuma

end AzumaStep

/-! ### 8. Pin G3: the stopped Azuma bound, general `n`, all `σ` -/

section StoppedAzuma

variable {d : ℕ} (sz : Sizes d)

/-- **Pin G3 (`alu9_STime`-type Azuma, general `n`)**: the merged `StoppedAzuma108` for the
general tensor (RBM2D `StoppedAzumaN`, `HierVocab:458`). -/
def StoppedAzumaN [IsFiniteMeasure (pathP sz)] (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) : Prop :=
  (∀ n, |E n| < 2) → (∀ n, 0 ≤ s n) → (∀ n, s n ≤ t n) → (∀ n, t n < 1) → (∀ n, K n ≠ 0) →
  ∀ (n : ℕ) (k : ℕ) (σ : Fin k → Bool) (τ : PathΩ sz → ℕ),
    (∀ j, MeasurableSet[filt sz j] {ω | j < τ ω}) →
    ∀ (m : ℕ), m ≤ K n → ∀ (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0),
      (∀ j < m,
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (martIncN sz E s t K n j σ ω') a) ω).re) (c j) (pathP sz) ∧
        HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
          (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (martIncN sz E s t K n j σ ω') a) ω).im) (c j) (pathP sz)) →
      ∀ x : ℝ, 0 ≤ x →
        (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
            Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
              (martIncN sz E s t K n j σ ω) a‖} ≤
          4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ)))

/-- **Pin G3 at one size index** (DECISIONS §29 (4)): `sum_stopped` rewrites the stopped sum as
`Σ_{j<m} 1{j<τ} (𝒰_{u_{j+1},u_m,σ} ξ_{j+1})_a`, each term is `filt sz (j+1)`-strongly measurable,
and `azuma_complex` gives the tail.  No window hypothesis is needed (`Ugen` is a total function
of its real times, and the measurability does not use `|E n| < 2`).  A conditional adapter: the
sub-Gaussian hypothesis is an input, not derived. -/
theorem stoppedAzumaN_at (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) (n : ℕ) {k : ℕ}
    (σ : Fin k → Bool) (τ : PathΩ sz → ℕ) (hτ : ∀ j, MeasurableSet[filt sz j] {ω | j < τ ω})
    (m : ℕ) (a : Fin k → Zd d (sz.L n)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < m,
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (martIncN sz E s t K n j σ ω') a) ω).re) (c j) (pathP sz) ∧
      HasCondSubgaussianMGF (filt sz j) ((filt sz).le j)
        (fun ω => ({ω' | j < τ ω'}.indicator (fun ω' =>
          Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
            (martIncN sz E s t K n j σ ω') a) ω).im) (c j) (pathP sz))
    {x : ℝ} (hx : 0 ≤ x) :
    (pathP sz).real {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (martIncN sz E s t K n j σ ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range m, (c j : ℝ))) := by
  set X : ℕ → PathΩ sz → ℂ := fun j => {ω' | j < τ ω'}.indicator (fun ω' =>
    Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
      (martIncN sz E s t K n j σ ω') a) with hXdef
  have hX : ∀ j < m, StronglyMeasurable[filt sz (j + 1)] (X j) := by
    intro j _
    have hset : MeasurableSet[filt sz (j + 1)] {ω | j < τ ω} :=
      ((filt sz).mono (Nat.le_succ j)) _ (hτ j)
    exact (GridDuhamelN_stronglyMeasurable_Ugen_apply d (sz.L n) (sz.lam n) (E n) σ _ _
      (GridDuhamelN_stronglyMeasurable_martIncN sz E s t K n j σ) a).indicator hset
  have hset : {ω | x ≤ ‖∑ j ∈ Finset.range (min m (τ ω)),
        Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n (j + 1)) (gridTime s t K n m)
          (martIncN sz E s t K n j σ ω) a‖}
      = {ω | x ≤ ‖∑ j ∈ Finset.range m, X j ω‖} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    have h := sum_stopped (Ω' := PathΩ sz) (M := ℂ)
      (fun i ω' => Ugen d (sz.L n) (sz.lam n) (E n) σ (gridTime s t K n i) (gridTime s t K n m)
        (martIncN sz E s t K n (i - 1) σ ω') a) τ m ω
    simp only [Nat.add_sub_cancel] at h
    rw [h]
  rw [hset]
  exact GridDuhamelN_azuma_step (μ := pathP sz) (ℱ := filt sz) hX hsubG hx

/-- **Pin G3 proved**: `StoppedAzumaN sz E s t K` (RBM2D `stoppedAzumaN`, `GridDuhamelN:363`).
The instance argument `[IsFiniteMeasure (pathP sz)]` is the pin's (redundant). -/
theorem stoppedAzumaN [IsFiniteMeasure (pathP sz)] (E : ℕ → ℝ) (s t : ℕ → ℝ) (K : ℕ → ℕ) :
    StoppedAzumaN sz E s t K :=
  fun _ _ _ _ _ n _ σ τ hτ m _ a c hsubG _ hx =>
    stoppedAzumaN_at sz E s t K n σ τ hτ m a c hsubG hx

end StoppedAzuma

/-! ### 9. Compiled nonempty instances (`d = 3`)

All at the non-constant sign vector `σ = (+,+,-)` (`k = 3`).  The algebra of `Ugen` is applied at
`d = 3`, `L = 3`, `g = 1/2`, `E = 0` and arbitrary tensors; the two pins at the merged `sz0`
(`d = 3`, `L_0 = 4`, `W_0 = 32`, `lam_0 = 1/64`), `n = 0`, `E ≡ 0`, `s ≡ 1/10`, `t ≡ 1/2`,
`K ≡ 4`, `τ ≡ 3`.  The conditional sub-Gaussian hypothesis of `stoppedAzumaN` is the pin's input
(Mathlib has no conditional Hoeffding lemma) and stays a hypothesis of the first Azuma example; the
second example (`τ ≡ 0`, `c ≡ 0`) discharges it by `HasCondSubgaussianMGF.fun_zero`. -/

section Instances

open RBM.Gauss.SizesInst

private def GridDuhamelN_instSigma : Fin 3 → Bool := ![true, true, false]

private theorem GridDuhamelN_instSigma_nonconst :
    GridDuhamelN_instSigma 0 ≠ GridDuhamelN_instSigma 2 := by decide

private def GridDuhamelN_instE : ℕ → ℝ := fun _ => 0
private def GridDuhamelN_instS : ℕ → ℝ := fun _ => 1 / 10
private def GridDuhamelN_instT : ℕ → ℝ := fun _ => 1 / 2
private def GridDuhamelN_instK : ℕ → ℕ := fun _ => 4

private theorem GridDuhamelN_inst_E : ∀ n, |GridDuhamelN_instE n| < 2 := fun _ => by
  norm_num [GridDuhamelN_instE]

private theorem GridDuhamelN_inst_s0 : ∀ n, 0 ≤ GridDuhamelN_instS n := fun _ => by
  norm_num [GridDuhamelN_instS]

private theorem GridDuhamelN_inst_st : ∀ n, GridDuhamelN_instS n ≤ GridDuhamelN_instT n :=
  fun _ => by norm_num [GridDuhamelN_instS, GridDuhamelN_instT]

private theorem GridDuhamelN_inst_t1 : ∀ n, GridDuhamelN_instT n < 1 := fun _ => by
  norm_num [GridDuhamelN_instT]

private theorem GridDuhamelN_inst_K : ∀ n, GridDuhamelN_instK n ≠ 0 := fun _ => by
  norm_num [GridDuhamelN_instK]

/-- `GridDuhamelN_Ugen_add` at `d = 3`, `L = 3`, `σ = (+,+,-)`. -/
example (A B : (Fin 3 → Zd 3 3) → ℂ) :
    Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) (A + B) =
      Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A +
        Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) B :=
  GridDuhamelN_Ugen_add 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A B

/-- `GridDuhamelN_Ugen_self` at `v = 1/4` (all hypotheses discharged). -/
example (A : (Fin 3 → Zd 3 3) → ℂ) :
    Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 4) A = A :=
  GridDuhamelN_Ugen_self (by norm_num) (by norm_num) GridDuhamelN_instSigma
    (by norm_num) (by norm_num) A

/-- `GridDuhamelN_Ugen_comp` at `(u, v, w) = (1/4, 1/2, 3/4)`. -/
example (A : (Fin 3 → Zd 3 3) → ℂ) :
    Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 2) (3 / 4)
        (Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A) =
      Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (3 / 4) A :=
  GridDuhamelN_Ugen_comp (u := 1 / 4) (by norm_num) (by norm_num) GridDuhamelN_instSigma
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) A

/-- `GridDuhamelN_UgenHom` applied (`GridDuhamelN_UgenHom_apply`). -/
example (A : (Fin 3 → Zd 3 3) → ℂ) :
    GridDuhamelN_UgenHom 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A =
      Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A :=
  GridDuhamelN_UgenHom_apply 3 3 (1 / 2) 0 GridDuhamelN_instSigma (1 / 4) (1 / 2) A

/-- `GridDuhamelN_Ugen_duhamel_telescope` at `u j = j / 10`, `m = 3` (times `0, 1/10, 1/5, 3/10`),
all hypotheses discharged, for an arbitrary family of `3`-tensors. -/
example (A : ℕ → ((Fin 3 → Zd 3 3) → ℂ)) :
    A 3 = Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma ((fun j : ℕ => (j : ℝ) / 10) 0)
        ((fun j : ℕ => (j : ℝ) / 10) 3) (A 0) +
      ∑ j ∈ Finset.range 3, Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma
        ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) ((fun j : ℕ => (j : ℝ) / 10) 3)
        (A (j + 1) - Ugen 3 3 (1 / 2) 0 GridDuhamelN_instSigma
          ((fun j : ℕ => (j : ℝ) / 10) j) ((fun j : ℕ => (j : ℝ) / 10) (j + 1)) (A j)) :=
  GridDuhamelN_Ugen_duhamel_telescope (by norm_num) (by norm_num) GridDuhamelN_instSigma
    (fun j : ℕ => (j : ℝ) / 10) 3
    (fun j _ => by positivity)
    (fun j hj => by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj
      change (j : ℝ) / 10 < 1
      linarith) A

/-- **`stoppedDuhamelN` at `sz0`**: `τ ≡ 3`, `j = 4` (so `min j τ = 3 ≤ K = 4`), `σ = (+,+,-)`,
for every sample `ω`. -/
example (ω : PathΩ sz0) :
    AvecN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0
        (min 4 ((fun _ : PathΩ sz0 => 3) ω)) GridDuhamelN_instSigma ω =
      Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 0)
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0
            (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
          (AvecN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK
            0 0 GridDuhamelN_instSigma ω) +
        ∑ i ∈ Finset.range (min 4 ((fun _ : PathΩ sz0 => 3) ω)),
          Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 (i + 1))
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0
              (min 4 ((fun _ : PathΩ sz0 => 3) ω)))
            (predIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
                GridDuhamelN_instK 0 i GridDuhamelN_instSigma ω +
              martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
                GridDuhamelN_instK 0 i GridDuhamelN_instSigma ω) :=
  stoppedDuhamelN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
    GridDuhamelN_instK GridDuhamelN_inst_E GridDuhamelN_inst_s0 GridDuhamelN_inst_st
    GridDuhamelN_inst_t1 GridDuhamelN_inst_K 0 3 GridDuhamelN_instSigma (fun _ => 3) 4 ω
    (by norm_num [GridDuhamelN_instK])

/-- The reduction at `n = 2`: the merged `StoppedDuhamel105` at `sz0`, `E = 0`, from the
general-`n` pin. -/
example : StoppedDuhamel105 sz0 0 GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK :=
  stoppedDuhamel105_of_stoppedDuhamelN sz0 0 GridDuhamelN_instS GridDuhamelN_instT
    GridDuhamelN_instK (stoppedDuhamelN sz0 (fun _ => 0) GridDuhamelN_instS GridDuhamelN_instT
      GridDuhamelN_instK)

/-- **`stoppedAzumaN` at `sz0`**, `τ ≡ 3`, `m = 2` (the two genuine terms `j = 0, 1`), `σ = (+,+,-)`
(sub-Gaussian input kept as the hypothesis `hsubG`). -/
example (a : Fin 3 → Zd 3 (sz0.L 0)) (c : ℕ → ℝ≥0)
    (hsubG : ∀ j < 2,
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 (j + 1))
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 2)
            (martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
              GridDuhamelN_instK 0 j GridDuhamelN_instSigma ω') a) ω).re) (c j) (pathP sz0) ∧
      HasCondSubgaussianMGF (filt sz0 j) ((filt sz0).le j)
        (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 3) ω'}.indicator (fun ω' =>
          Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 (j + 1))
            (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 2)
            (martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
              GridDuhamelN_instK 0 j GridDuhamelN_instSigma ω') a) ω).im) (c j) (pathP sz0))
    (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 3) ω)),
        Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 (j + 1))
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 2)
          (martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
            GridDuhamelN_instK 0 j GridDuhamelN_instSigma ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (c j : ℝ))) :=
  stoppedAzumaN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
    GridDuhamelN_instK GridDuhamelN_inst_E GridDuhamelN_inst_s0 GridDuhamelN_inst_st
    GridDuhamelN_inst_t1 GridDuhamelN_inst_K 0 3 GridDuhamelN_instSigma (fun _ => 3)
    (fun _ => MeasurableSet.const _) 2 (by norm_num [GridDuhamelN_instK]) a c hsubG x hx

/-- Fully discharged companion at `τ ≡ 0`, `c ≡ 0`: the stopped increments vanish, so the
sub-Gaussian hypothesis holds by `HasCondSubgaussianMGF.fun_zero`. -/
example (a : Fin 3 → Zd 3 (sz0.L 0)) (x : ℝ) (hx : 0 ≤ x) :
    (pathP sz0).real {ω | x ≤ ‖∑ j ∈ Finset.range (min 2 ((fun _ : PathΩ sz0 => 0) ω)),
        Ugen 3 (sz0.L 0) (sz0.lam 0) (GridDuhamelN_instE 0) GridDuhamelN_instSigma
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 (j + 1))
          (gridTime GridDuhamelN_instS GridDuhamelN_instT GridDuhamelN_instK 0 2)
          (martIncN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
            GridDuhamelN_instK 0 j GridDuhamelN_instSigma ω) a‖} ≤
      4 * Real.exp (-x ^ 2 / (4 * ∑ j ∈ Finset.range 2, (((fun _ => 0 : ℕ → ℝ≥0) j : ℝ≥0) : ℝ))) := by
  refine stoppedAzumaN sz0 GridDuhamelN_instE GridDuhamelN_instS GridDuhamelN_instT
    GridDuhamelN_instK GridDuhamelN_inst_E GridDuhamelN_inst_s0 GridDuhamelN_inst_st
    GridDuhamelN_inst_t1 GridDuhamelN_inst_K 0 3 GridDuhamelN_instSigma (fun _ => 0)
    (fun _ => MeasurableSet.const _) 2 (by norm_num [GridDuhamelN_instK]) a
    (fun _ => 0) ?_ x hx
  intro j _
  have h0 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).re) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  have h1 : ∀ f : PathΩ sz0 → ℂ,
      (fun ω => ({ω' | j < (fun _ : PathΩ sz0 => 0) ω'}.indicator f ω).im) = fun _ => (0 : ℝ) := by
    intro f; funext ω; simp
  refine ⟨?_, ?_⟩
  · rw [h0]; exact HasCondSubgaussianMGF.fun_zero
  · rw [h1]; exact HasCondSubgaussianMGF.fun_zero

end Instances

end RBM.Ind
