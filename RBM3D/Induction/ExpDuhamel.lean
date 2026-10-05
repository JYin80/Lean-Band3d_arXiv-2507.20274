/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Induction.ExpHier
import RBM3D.Induction.ZeroModeCalc
import RBM3D.Induction.QopAlgebra
import RBM3D.Induction.GridDuhamelN
import RBM3D.Propagator.Deriv
import RBM3D.Propagator.Props4

/-!
# S6-05 (T2224): the two Duhamel formulas of Step 6 (the pins `STExpDuhamelZ`, `STExpDuhamelQ`)

Port of RBM2D `Evolution/MLExpDuhamel.lean` at commit `c9a24cf` (cited `MLExpDuhamel:<line>`; 532
lines there) and of `Evolution/MLExpVocab.lean` (`uker_mul_thetaGenMat` `:190`, `qop_source`
`:229`) to `d ≥ 3`, to a start time `s` and to an abstract mollifier.  Paper: arXiv:2507.20274,
`(Eexpint_K-L)` `paper/tex/6_Step6_two_loop.tex:3-7`, `(iisuwjyys_exp)` `6:142-146`,
`(int_K-L+QE)` `6:109-116`, `Def:QtPt` `paper/tex/3_5_Loop_Hierarchy.tex:1200-1260`.

**Targets**: `stExpDuhamelZ_holds d : STExpDuhamelZ d` and `stExpDuhamelQ_holds d : STExpDuhamelQ d`
(the pins of `Induction/Step6Pins.lean:225, 246`, unchanged), for every `d` (the premise `3 ≤ d` is
not used).

## Route (as in RBM2D, `MLExpDuhamel:18-24`)

`v ↦ (𝒰_{v,t,σ} Y_v)_a` has derivative `𝒰_{v,t}(Y'_v - Θ_v Y_v)`: `uKer μ r t` is affine in `r`
with `∂_r = -thetaKer μ t` (1a), and `𝒰_{v,t} Θ_v = Θ_t` slot by slot (1b, 1c; RBM2D
`MLExpDuhamel_Uker_theta` `:96`).  With continuity on `[s,t]`, the derivative on `(s,t)` and
`𝒰_{t,t} = id`, the fundamental theorem of calculus gives
`Y_t = 𝒰_{s,t} Y_s + ∫_s^t 𝒰_{u,t} D_u du` (2a).  The plain form is `Y = f`, `D = STExpDrift`
(3a, from the three conjuncts of `STExpHier`); the zero-mode form is `Y = Q^{(A)} f`,
`D = Q^{(A)} D`, followed by `Q^{(A)} 𝒰 = 𝒰 Q^{(A)}` (3d); the `𝒬` form is `Y_u = 𝒬_u f_u`,
`D = STExpQsrc` (4e).

## Changes against RBM2D

1. **Start at `s`**: the initial term `𝒰_{s,t} f_s` replaces `f_0 = 0` (the merged `STExpHier`
   does not state it).
2. **Abstract mollifier**: `ϑ` is any family with `STMollifierProps` (the closed form of RBM2D is
   not admissible at `d ≥ 3`, `Step34Pins.lean:504-509`), so `∂_uϑ` exists on `(0,1)` and is
   bounded, not continuous: the engine takes an interval integrable source (`measurable_deriv`
   and the fourth conjunct with `1 ≤ ℓ_u`, `expDuh_intervalIntegrable_Qsrc`).
3. **Zero-mode sets** `Q^{(A)}` (absent in RBM2D): a finite linear map, it passes through `∂_u`
   and continuity entrywise.
4. Kernel on `Zd d L` (`uKer`, `thetaKer`, `ThetaN`, `Ugen`), labels `Fin k → Zd d L`, slot
   parameters `cycProd`.

Every helper is `private` and prefixed `expDuh_`.  The compiled instances are section 5.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace RBM.Gauss.Sizes

open MeasureTheory Filter Matrix RBM

/-! ## 1. The kernel `𝒰_{v,t,σ}` as a function of its first time -/

/-- `uKer μ r t = Θ_{tμ} - r • thetaKer μ t` (RBM2D `MLExpDuhamel_ukerMat_eq`, `:50`). -/
private theorem expDuh_uKer_eq {d L : ℕ} [NeZero L] (g : ℝ) (μ : ℂ) (t r : ℝ) :
    RBM.uKer d L g μ r t = RBM.Theta d L g ((t : ℂ) * μ) - (r : ℂ) • RBM.thetaKer d L g μ t := by
  simp only [RBM.uKer, RBM.thetaKer, sub_mul, one_mul, smul_mul_assoc, smul_smul]

/-- **1a** `∂_r (uKer μ r t)_{xy} = -(thetaKer μ t)_{xy}` (RBM2D `MLExpDuhamel_hasDerivAt_ukerMat`, `:55`). -/
theorem expDuh_hasDerivAt_uKer {d L : ℕ} [NeZero L] (g : ℝ) (μ : ℂ) (t : ℝ) (x y : Zd d L) (v : ℝ) :
    HasDerivAt (fun r : ℝ => RBM.uKer d L g μ r t x y) (-(RBM.thetaKer d L g μ t x y)) v := by
  have h : (fun r : ℝ => RBM.uKer d L g μ r t x y) = fun r : ℝ =>
      RBM.Theta d L g ((t : ℂ) * μ) x y - (r : ℂ) * (RBM.thetaKer d L g μ t x y) := by
    funext r
    rw [expDuh_uKer_eq]
    simp [Matrix.sub_apply, Matrix.smul_apply]
  rw [h]
  have hid : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 v := (hasDerivAt_id v).ofReal_comp
  exact ((hasDerivAt_const v (RBM.Theta d L g ((t : ℂ) * μ) x y)).fun_sub
    (hid.mul_const (RBM.thetaKer d L g μ t x y))).congr_deriv (by ring)

private theorem expDuh_continuous_uKer {d L : ℕ} [NeZero L] (g : ℝ) (μ : ℂ) (t : ℝ) (x y : Zd d L) :
    Continuous fun r : ℝ => RBM.uKer d L g μ r t x y :=
  continuous_iff_continuousAt.2 fun v => (expDuh_hasDerivAt_uKer g μ t x y v).continuousAt

/-- **1b** the one-slot identity `(1 - vμS) Θ_{tμ} · μ S Θ_{vμ} = μ S Θ_{tμ}`
(RBM2D `uker_mul_thetaGenMat`, `MLExpVocab.lean:190`; here from `uKer_eq_one_add` and `Theta_sub_Theta`). -/
theorem expDuh_uKer_mul_thetaKer {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {μ : ℂ} {v t : ℝ}
    (hv : ‖(v : ℂ) * μ‖ < 1) (ht : ‖(t : ℂ) * μ‖ < 1) :
    RBM.uKer d L g μ v t * RBM.thetaKer d L g μ v = RBM.thetaKer d L g μ t := by
  have h1 := RBM.uKer_eq_one_add (d := d) (L := L) (g := g) (s := v) hL ht
  have h2 := RBM.Theta_sub_Theta d L g (RBM.norm_SB d L g hL) hv ht
  have h3 : (μ • RBM.SB d L g) * RBM.Theta d L g ((t : ℂ) * μ) =
      (μ • RBM.SB d L g) * RBM.Theta d L g ((v : ℂ) * μ) +
        (μ • RBM.SB d L g) * (((t : ℂ) * μ - (v : ℂ) * μ) •
          (RBM.Theta d L g ((t : ℂ) * μ) * RBM.SB d L g * RBM.Theta d L g ((v : ℂ) * μ))) := by
    rw [← mul_add]
    congr 1
    rw [← h2]
    abel
  unfold RBM.thetaKer
  rw [h1, h3]
  simp only [add_mul, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc]
  rw [smul_add, smul_smul]
  congr 2
  ring

/-- Reindexing of a double sum over a tensor `b` and one replaced slot `c` (RBM2D
`MLExpDuhamel_sum_update_reindex`, `:75`). -/
private theorem expDuh_sum_update_reindex {d L : ℕ} [NeZero L] {k : ℕ} (i : Fin k)
    (f : (Fin k → Zd d L) → Zd d L → ℂ) :
    ∑ b : Fin k → Zd d L, ∑ c : Zd d L, f b c
      = ∑ e : Fin k → Zd d L, ∑ x : Zd d L, f (Function.update e i x) (e i) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  refine Finset.sum_nbij' (i := fun p => (Function.update p.1 i p.2, p.1 i))
    (j := fun q => (Function.update q.1 i q.2, q.1 i)) ?_ ?_ ?_ ?_ ?_
  · intro p _
    exact Finset.mem_univ _
  · intro q _
    exact Finset.mem_univ _
  · intro p _
    exact Prod.ext (by simp) (by simp)
  · intro q _
    exact Prod.ext (by simp) (by simp)
  · intro p _
    simp

/-- `𝒰_{v,t} ∘ Θ_v` slot by slot, for general slot parameters `ξ` (RBM2D `MLExpDuhamel_Uker_theta`, `:96`). -/
private theorem expDuh_Uker_theta {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {k : ℕ} (ξ : Fin k → ℂ)
    {v t : ℝ} (hv : ∀ i, ‖(v : ℂ) * ξ i‖ < 1) (ht : ∀ i, ‖(t : ℂ) * ξ i‖ < 1)
    (A : (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) :
    ∑ b : Fin k → Zd d L, (∏ i, RBM.uKer d L g (ξ i) v t (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Zd d L, RBM.thetaKer d L g (ξ i) v (b i) c * A (Function.update b i c)) =
      ∑ b : Fin k → Zd d L, (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) v t (a j) (b j)) *
          RBM.thetaKer d L g (ξ i) t (a i) (b i)) * A b := by
  classical
  have step1 : ∑ b : Fin k → Zd d L, (∏ i, RBM.uKer d L g (ξ i) v t (a i) (b i)) *
        (∑ i : Fin k, ∑ c : Zd d L, RBM.thetaKer d L g (ξ i) v (b i) c * A (Function.update b i c))
      = ∑ i : Fin k, ∑ b : Fin k → Zd d L, ∑ c : Zd d L,
          (∏ j, RBM.uKer d L g (ξ j) v t (a j) (b j)) *
            (RBM.thetaKer d L g (ξ i) v (b i) c * A (Function.update b i c)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Finset.mul_sum]
  have step2 : ∀ i : Fin k,
      (∑ b : Fin k → Zd d L, ∑ c : Zd d L, (∏ j, RBM.uKer d L g (ξ j) v t (a j) (b j)) *
            (RBM.thetaKer d L g (ξ i) v (b i) c * A (Function.update b i c)))
        = ∑ e : Fin k → Zd d L,
            ((∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) v t (a j) (e j)) *
              RBM.thetaKer d L g (ξ i) t (a i) (e i)) * A e := by
    intro i
    rw [expDuh_sum_update_reindex i (fun b c => (∏ j, RBM.uKer d L g (ξ j) v t (a j) (b j)) *
      (RBM.thetaKer d L g (ξ i) v (b i) c * A (Function.update b i c)))]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hkey : ∀ x : Zd d L,
        (∏ j, RBM.uKer d L g (ξ j) v t (a j) (Function.update e i x j)) *
            (RBM.thetaKer d L g (ξ i) v (Function.update e i x i) (e i) *
              A (Function.update (Function.update e i x) i (e i)))
          = ((∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) v t (a j) (e j)) * A e) *
              (RBM.uKer d L g (ξ i) v t (a i) x * RBM.thetaKer d L g (ξ i) v x (e i)) := by
      intro x
      have hprod : (∏ j, RBM.uKer d L g (ξ j) v t (a j) (Function.update e i x j))
          = RBM.uKer d L g (ξ i) v t (a i) x *
            ∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) v t (a j) (e j) := by
        rw [← Finset.mul_prod_erase Finset.univ
          (fun j => RBM.uKer d L g (ξ j) v t (a j) (Function.update e i x j)) (Finset.mem_univ i)]
        congr 1
        · rw [Function.update_self]
        · exact Finset.prod_congr rfl fun j hj => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      have hup : Function.update (Function.update e i x) i (e i) = e := by
        rw [Function.update_idem, Function.update_eq_self]
      rw [hprod, hup, Function.update_self]
      ring
    simp_rw [hkey]
    rw [← Finset.mul_sum]
    have hmul : ∑ x : Zd d L, RBM.uKer d L g (ξ i) v t (a i) x * RBM.thetaKer d L g (ξ i) v x (e i)
        = (RBM.uKer d L g (ξ i) v t * RBM.thetaKer d L g (ξ i) v) (a i) (e i) :=
      (Matrix.mul_apply).symm
    rw [hmul, expDuh_uKer_mul_thetaKer g hL (hv i) (ht i)]
    ring
  rw [step1]
  simp_rw [step2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_mul]

/-- The slot condition `‖v m(σ_i) m(σ_{i+1})‖ < 1` for `0 ≤ v < 1`, `|E| ≤ 2` (RBM2D `MLExpDuhamel_norm_xi`, `:167`). -/
private theorem expDuh_norm_slot {E : ℝ} (hE : |E| ≤ 2) {k : ℕ} (σ : Fin k → Bool) {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v < 1) (i : Fin k) :
    ‖(v : ℂ) * RBM.cycProd (fun l => RBM.mSigma E (σ l)) i‖ < 1 :=
  RBM.norm_mul_mSigma_lt_one hE hv0 hv1 (σ i) (σ (finRotate k i))

/-- **1c** `𝒰_{v,t} (Θ_v A)` slot by slot (RBM2D `MLExpDuhamel_Uker_theta`, `:96`). -/
theorem expDuh_Ugen_ThetaN {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {v t : ℝ} (hv0 : 0 ≤ v) (hv1 : v < 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (A : (Fin k → Zd d L) → ℂ) (a : Fin k → Zd d L) :
    RBM.Ind.Ugen d L g E σ v t (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) v A) a =
      ∑ b : Fin k → Zd d L, (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i,
            RBM.uKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) j) v t (a j) (b j)) *
          RBM.thetaKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) t (a i) (b i)) * A b :=
  expDuh_Uker_theta g hL (fun i => RBM.cycProd (fun l => RBM.mSigma E (σ l)) i)
    (expDuh_norm_slot hE σ hv0 hv1) (expDuh_norm_slot hE σ ht0 ht1) A a

/-- **1d** `∂_v (𝒰_{v,t} Y_v) = 𝒰_{v,t}(Y' - Θ_v Y_v)` (RBM2D `MLExpDuhamel_ftc`, `:188`, the `hterm`/`hprod`/`hθ'` part). -/
theorem expDuh_hasDerivAt_Ugen {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {u t : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (ht0 : 0 ≤ t) (ht1 : t < 1)
    {Y : ℝ → (Fin k → Zd d L) → ℂ} {Y' : (Fin k → Zd d L) → ℂ}
    (hY : ∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) (a : Fin k → Zd d L) :
    HasDerivAt (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a)
      (RBM.Ind.Ugen d L g E σ u t
        (fun b => Y' b - RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b) a) u := by
  classical
  set ξ : Fin k → ℂ := fun i => RBM.cycProd (fun l => RBM.mSigma E (σ l)) i with hξ
  have hterm : ∀ b : Fin k → Zd d L,
      HasDerivAt (fun r : ℝ => (∏ i, RBM.uKer d L g (ξ i) r t (a i) (b i)) * Y r b)
        ((∑ i, (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
            (-(RBM.thetaKer d L g (ξ i) t (a i) (b i)))) * Y u b +
          (∏ i, RBM.uKer d L g (ξ i) u t (a i) (b i)) * Y' b) u := by
    intro b
    have hprod : HasDerivAt (fun r : ℝ => ∏ i, RBM.uKer d L g (ξ i) r t (a i) (b i))
        (∑ i, (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
            (-(RBM.thetaKer d L g (ξ i) t (a i) (b i)))) u := by
      have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin k)))
        (f := fun (i : Fin k) (r : ℝ) => RBM.uKer d L g (ξ i) r t (a i) (b i))
        (f' := fun i => -(RBM.thetaKer d L g (ξ i) t (a i) (b i)))
        (fun i _ => expDuh_hasDerivAt_uKer g (ξ i) t (a i) (b i) u)
      simpa only [smul_eq_mul] using h
    exact hprod.mul (hY b)
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin k → Zd d L)))
    (fun b _ => hterm b)
  refine hsum.congr_deriv ?_
  have hθ := expDuh_Ugen_ThetaN g hL hE σ hu0 hu1 ht0 ht1 (Y u) a
  have hθ' : ∑ b : Fin k → Zd d L, (∏ i, RBM.uKer d L g (ξ i) u t (a i) (b i)) *
      RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b = ∑ b : Fin k → Zd d L, (∑ i : Fin k,
        (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
          RBM.thetaKer d L g (ξ i) t (a i) (b i)) * Y u b := hθ
  calc ∑ b : Fin k → Zd d L, ((∑ i, (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
            (-(RBM.thetaKer d L g (ξ i) t (a i) (b i)))) * Y u b +
          (∏ i, RBM.uKer d L g (ξ i) u t (a i) (b i)) * Y' b)
      = ∑ b : Fin k → Zd d L, (-((∑ i,
            (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
              RBM.thetaKer d L g (ξ i) t (a i) (b i)) * Y u b) +
          (∏ i, RBM.uKer d L g (ξ i) u t (a i) (b i)) * Y' b) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [mul_neg, Finset.sum_neg_distrib]
        ring
    _ = -(∑ b : Fin k → Zd d L, (∑ i : Fin k,
            (∏ j ∈ Finset.univ.erase i, RBM.uKer d L g (ξ j) u t (a j) (b j)) *
              RBM.thetaKer d L g (ξ i) t (a i) (b i)) * Y u b) +
          ∑ b : Fin k → Zd d L, (∏ i, RBM.uKer d L g (ξ i) u t (a i) (b i)) * Y' b := by
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = RBM.Ind.Ugen d L g E σ u t (fun b => Y' b - RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b) a := by
        rw [← hθ']
        unfold RBM.Ind.Ugen RBM.UN
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring

/-- **1e** `u ↦ (𝒰_{u,t} Y_u)_a` is continuous on `S` when every entry of `Y` is; no hypothesis on the times
(RBM2D `MLExpDuhamel_continuousOn_Ugen`, `:174`). -/
theorem expDuh_continuousOn_Ugen {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (t : ℝ)
    {S : Set ℝ} {Y : ℝ → (Fin k → Zd d L) → ℂ} (hY : ∀ b, ContinuousOn (fun v => Y v b) S)
    (a : Fin k → Zd d L) :
    ContinuousOn (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a) S := by
  unfold RBM.Ind.Ugen RBM.UN
  refine continuousOn_finsetSum _ fun b _ => ?_
  exact (continuous_finsetProd _ fun i _ =>
    expDuh_continuous_uKer g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) t (a i) (b i)).continuousOn.mul (hY b)

/-- **1f** `u ↦ (𝒰_{u,t} D_u)_a` is interval integrable when every entry of `D` is (new: `∂_uϑ` is only
measurable and bounded, so the source of the `𝒬`-Duhamel formula is not continuous). -/
theorem expDuh_intervalIntegrable_Ugen {d L : ℕ} [NeZero L] (g E : ℝ) {k : ℕ} (σ : Fin k → Bool) (s t : ℝ)
    {D : ℝ → (Fin k → Zd d L) → ℂ}
    (hD : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t) (a : Fin k → Zd d L) :
    IntervalIntegrable (fun u => RBM.Ind.Ugen d L g E σ u t (D u) a) MeasureTheory.volume s t := by
  unfold RBM.Ind.Ugen RBM.UN
  have h := IntervalIntegrable.sum (Finset.univ : Finset (Fin k → Zd d L))
    (f := fun (b : Fin k → Zd d L) (u : ℝ) =>
      (∏ i, RBM.uKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) u t (a i) (b i)) * D u b)
    (a := s) (b := t) (μ := MeasureTheory.volume) (fun b _ => by
      have hc : ContinuousOn (fun u : ℝ =>
          ∏ i, RBM.uKer d L g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) u t (a i) (b i)) (Set.uIcc s t) :=
        (continuous_finsetProd _ fun i _ =>
          expDuh_continuous_uKer g (RBM.cycProd (fun l => RBM.mSigma E (σ l)) i) t (a i) (b i)).continuousOn
      exact (hD b).continuousOn_mul hc)
  convert h using 1
  funext u
  simp [Finset.sum_apply]

/-! ## 2. The Duhamel engine from `s`, and the `Θ^{(2)}` bridge -/

/-- **2a** The Duhamel formula from the drift identity on the open window: if `Y` is continuous on `[s,t]`, `D` is
interval integrable and `∂_u Y = Θ_u Y + D` on `(s,t)`, then `Y_t = 𝒰_{s,t} Y_s + ∫_s^t 𝒰_{u,t} D_u du`
(RBM2D `MLExpDuhamel_ftc`, `:188`, from `s` instead of `0`, integrable instead of continuous source). -/
theorem expDuh_duhamel {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2) {k : ℕ}
    (σ : Fin k → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    {Y D : ℝ → (Fin k → Zd d L) → ℂ}
    (hYc : ∀ b, ContinuousOn (fun u => Y u b) (Set.Icc s t))
    (hDi : ∀ b, IntervalIntegrable (fun u => D u b) MeasureTheory.volume s t)
    (hYd : ∀ u ∈ Set.Ioo s t, ∀ b, HasDerivAt (fun v => Y v b)
      (RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) b + D u b) u)
    (a : Fin k → Zd d L) :
    Y t a = RBM.Ind.Ugen d L g E σ s t (Y s) a + ∫ u in s..t, RBM.Ind.Ugen d L g E σ u t (D u) a := by
  have ht0 : 0 ≤ t := hs0.trans hst
  have hcont := expDuh_continuousOn_Ugen g E σ t hYc a
  have hderiv : ∀ u ∈ Set.Ioo s t,
      HasDerivAt (fun v => RBM.Ind.Ugen d L g E σ v t (Y v) a) (RBM.Ind.Ugen d L g E σ u t (D u) a) u := by
    intro u hu
    have h := expDuh_hasDerivAt_Ugen g hL hE σ (hs0.trans hu.1.le) (hu.2.trans ht1) ht0 ht1 (hYd u hu) a
    refine h.congr_deriv ?_
    congr 1
    funext b
    ring
  have hint := expDuh_intervalIntegrable_Ugen g E σ s t hDi a
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst hcont hderiv hint
  have hgt : RBM.Ind.Ugen d L g E σ t t (Y t) a = Y t a := by
    rw [RBM.Ind.GridDuhamelN_Ugen_self hL hE σ ht0 ht1 (Y t)]
  rw [hFTC, hgt]
  ring

/-- **2b** `Θ^{(2)}_{u,σ}` is `ThetaN` at `k = 2` (public copy of the private `expHier_ThetaN_two`,
`ExpHier.lean:375`, reversed): slot `0` has `m₀ m₁`, slot `1` has `m₁ m₀`. -/
theorem expDuh_STthetaOp_eq_ThetaN {d : ℕ} (sz : Sizes d) (n : ℕ) (E u : ℝ) (σ : Fin 2 → Bool)
    (A : (Fin 2 → Zd d (sz.L n)) → ℂ) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STthetaOp n E u σ A a = RBM.ThetaN d (sz.L n) (sz.lam n) (fun l => RBM.mSigma E (σ l)) u A a := by
  unfold RBM.ThetaN STthetaOp
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  have hμ : RBM.cycProd (fun l => RBM.mSigma E (σ l)) i = STmsig E (σ 0) * STmsig E (σ 1) := by
    fin_cases i
    · rfl
    · exact mul_comm _ _
  simp only [RBM.thetaKer, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, hμ]

/-! ## 3. The plain and zero-mode Duhamel formulas -/

/-- `Q^{(A)}` as an `ℝ`-continuous-linear map on `k`-index tensors (finite-dimensional). -/
private def expDuh_zeroModeCLM {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k)) :
    ((Fin k → Zd d L) → ℂ) →L[ℝ] ((Fin k → Zd d L) → ℂ) :=
  LinearMap.toContinuousLinearMap ((RBM.zeroModeSetLin (d := d) (L := L) A).restrictScalars ℝ)

private theorem expDuh_zeroModeCLM_apply {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k))
    (T : (Fin k → Zd d L) → ℂ) : expDuh_zeroModeCLM A T = RBM.zeroModeSet d L A T := rfl

/-- **3b** `Q^{(A)}` is a finite linear map: it commutes with `∂_u` entrywise. -/
theorem expDuh_zeroModeSet_hasDerivAt {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k))
    {Y : ℝ → (Fin k → Zd d L) → ℂ} {Y' : (Fin k → Zd d L) → ℂ} {u : ℝ}
    (hY : ∀ b, HasDerivAt (fun v => Y v b) (Y' b) u) (a : Fin k → Zd d L) :
    HasDerivAt (fun v => RBM.zeroModeSet d L A (Y v) a) (RBM.zeroModeSet d L A Y' a) u := by
  have h : HasDerivAt Y Y' u := hasDerivAt_pi.mpr hY
  have h2 := (expDuh_zeroModeCLM (d := d) (L := L) A).hasFDerivAt.comp_hasDerivAt u h
  exact hasDerivAt_pi.mp h2 a

/-- **3c** the same for continuity. -/
theorem expDuh_zeroModeSet_continuousOn {d L : ℕ} [NeZero L] {k : ℕ} (A : Finset (Fin k))
    {Y : ℝ → (Fin k → Zd d L) → ℂ} {S : Set ℝ} (hY : ∀ b, ContinuousOn (fun v => Y v b) S)
    (a : Fin k → Zd d L) :
    ContinuousOn (fun v => RBM.zeroModeSet d L A (Y v) a) S := by
  have h : ContinuousOn Y S := continuousOn_pi.mpr hY
  have h2 := (expDuh_zeroModeCLM (d := d) (L := L) A).continuous.comp_continuousOn h
  exact continuousOn_pi.mp h2 a

/-- **3a** the plain Duhamel formula from `s` (`A = ∅`), every `d` (RBM2D `expDuhamelPin_of_hier`, `:412`, from `s`). -/
theorem expDuh_plain {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) (s t : ℝ) (hs0 : 0 ≤ s)
    (hst : s ≤ t) (ht1 : t < 1) (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    sz.STExpErr n E t σ a =
      RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ s t (fun b => sz.STExpErr n E s σ b) a +
      ∫ u in s..t, RBM.Ind.Ugen d (sz.L n) (sz.lam n) E σ u t (fun b => sz.STExpDrift n E u σ b) a := by
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  exact expDuh_duhamel (sz.lam n) (sz.three_le_L n) hE.le σ hs0 hst ht1
    (Y := fun u b => sz.STExpErr n E u σ b) (D := fun u b => sz.STExpDrift n E u σ b)
    (fun b => (expHier_continuousOn_err sz n hE σ b).mono hI)
    (fun b => ((expHier_continuousOn_drift sz n hE σ b).mono hI).intervalIntegrable_of_Icc hst)
    (fun u hu b => by
      have h := expHier_hasDerivAt sz n hE σ b u ⟨hs0.trans_lt hu.1, hu.2.trans ht1⟩
      rw [expDuh_STthetaOp_eq_ThetaN] at h
      exact h) a

/-- **3d** the pin `STExpDuhamelZ` (`(Eexpint_K-L)` `6:3-7`, `(iisuwjyys_exp)` `6:142-146`), every `d`
(RBM2D `expDuhamelPin_of_hier`, `:412`, from `s`, with `Q^{(A)}`): the engine at `Y = Q^{(A)} f`, `D = Q^{(A)} D`,
then `Q^{(A)} 𝒰 = 𝒰 Q^{(A)}` (`zeroModeSet_Ugen`, `t < 1`). -/
theorem stExpDuhamelZ_holds (d : ℕ) : STExpDuhamelZ d := by
  intro _ sz n E hE s t hs0 hst ht1 σ A a
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have ht0 : 0 ≤ t := hs0.trans hst
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  have hcf : ∀ b, ContinuousOn (fun u => sz.STExpErr n E u σ b) (Set.Icc s t) := fun b =>
    (expHier_continuousOn_err sz n hE σ b).mono hI
  have hcD : ∀ b, ContinuousOn (fun u => sz.STExpDrift n E u σ b) (Set.Icc s t) := fun b =>
    (expHier_continuousOn_drift sz n hE σ b).mono hI
  have key := expDuh_duhamel (sz.lam n) hL hE.le σ hs0 hst ht1
    (Y := fun u b => RBM.zeroModeSet d (sz.L n) A (fun c => sz.STExpErr n E u σ c) b)
    (D := fun u b => RBM.zeroModeSet d (sz.L n) A (fun c => sz.STExpDrift n E u σ c) b)
    (fun b => expDuh_zeroModeSet_continuousOn A hcf b)
    (fun b => (expDuh_zeroModeSet_continuousOn A hcD b).intervalIntegrable_of_Icc hst)
    (fun u hu b => by
      have hu0 : 0 ≤ u := hs0.trans hu.1.le
      have hu1 : u < 1 := hu.2.trans ht1
      have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs0.trans_lt hu.1, hu1⟩
      have h := expDuh_zeroModeSet_hasDerivAt (d := d) (L := sz.L n) A
        (Y := fun v c => sz.STExpErr n E v σ c)
        (Y' := fun c => RBM.ThetaN d (sz.L n) (sz.lam n) (fun l => RBM.mSigma E (σ l)) u
          (fun c' => sz.STExpErr n E u σ c') c + sz.STExpDrift n E u σ c)
        (fun c => by
          have h0 := expHier_hasDerivAt sz n hE σ c u hu'
          rwa [expDuh_STthetaOp_eq_ThetaN] at h0) b
      refine h.congr_deriv ?_
      have hadd := congrFun (RBM.zeroModeSet_add (d := d) (L := sz.L n) A
        (RBM.ThetaN d (sz.L n) (sz.lam n) (fun l => RBM.mSigma E (σ l)) u (fun c' => sz.STExpErr n E u σ c'))
        (fun c => sz.STExpDrift n E u σ c)) b
      have hth := congrFun (RBM.zeroModeSet_ThetaN (g := sz.lam n) hL
        (m := fun l => RBM.mSigma E (σ l)) (t := u) (fun i => expDuh_norm_slot hE.le σ hu0 hu1 i) A
        (fun c' => sz.STExpErr n E u σ c')) b
      exact hadd.trans (by simp only [Pi.add_apply]; rw [hth])) a
  simp only [RBM.Ind.zeroModeSet_Ugen hL hE.le σ ht0 ht1]
  exact key

/-! ## 4. The `𝒬`-Duhamel formula (abstract mollifier `ϑ`, from `s`) -/

/-- `u ↦ (𝒬_u X_u)_a` is continuous on `S ⊆ [0,1)` when every entry of `X` is: `ϑ` is differentiable on `[0,1)`
(third conjunct of `STMollifierProps`), `𝒫` is a finite sum (RBM2D `MLExpDuhamel_continuousOn_Qop`, `:320`). -/
private theorem expDuh_continuousOn_Qop_gen {d L m : ℕ} [NeZero L] {g C c : ℝ}
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ) {S : Set ℝ}
    (hS : S ⊆ Set.Ico 0 1) {X : ℝ → (Fin (m + 1) → Zd d L) → ℂ}
    (hX : ∀ b, ContinuousOn (fun u => X u b) S) (a : Fin (m + 1) → Zd d L) :
    ContinuousOn (fun u => STQop (d := d) ϑ u (X u) a) S := by
  unfold STQop STPsum
  exact (hX a).sub ((continuousOn_finsetSum _ fun b _ => hX b).mul
    ((hϑ.2.2.1 a).continuousOn.mono hS))

/-- **4a** `u ↦ (𝒬_u f_u)_a` is continuous on `[0,1)`. -/
theorem expDuh_continuousOn_Qop {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ}
    {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (σ : Fin 2 → Bool) (a : Fin 2 → Zd d (sz.L n)) :
    ContinuousOn (fun u => STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b) a) (Set.Ico 0 1) :=
  expDuh_continuousOn_Qop_gen hϑ subset_rfl (fun b => expHier_continuousOn_err sz n hE σ b) a

/-- **4b** `∂_u (𝒬_u f_u) = Θ^{(2)}_u (𝒬_u f_u) + A_u` on `(0,1)`, `A_u = STExpQsrc`
(RBM2D `MLExpDuhamel_hasDerivAt_Qop`, `:367`, with `qop_source`, `MLExpVocab.lean:229`, sign of T2166a). -/
theorem expDuh_Qop_hasDerivAt {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ}
    {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (σ : Fin 2 → Bool) (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) (a : Fin 2 → Zd d (sz.L n)) :
    HasDerivAt (fun v => STQop (d := d) ϑ v (fun b => sz.STExpErr n E v σ b) a)
      (sz.STthetaOp n E u σ (STQop (d := d) ϑ u (fun b => sz.STExpErr n E u σ b)) a +
        sz.STExpQsrc n E u σ ϑ a) u := by
  have hA : ∀ c', HasDerivAt (fun v => sz.STExpErr n E v σ c')
      (sz.STthetaOp n E u σ (fun b => sz.STExpErr n E u σ b) c' + sz.STExpDrift n E u σ c') u :=
    fun c' => expHier_hasDerivAt sz n hE σ c' u hu
  have hϑd : ∀ c', HasDerivAt (fun τ => ϑ τ c') (deriv (fun τ => ϑ τ c') u) u := fun c' =>
    ((hϑ.2.2.1 c').differentiableAt (Ico_mem_nhds hu.1 hu.2)).hasDerivAt
  have h := QopAlgebra_Qop_hasDerivAt (d := d) (ϑ := ϑ) (A := fun v c' => sz.STExpErr n E v σ c')
    (A' := fun c' => sz.STthetaOp n E u σ (fun b => sz.STExpErr n E u σ b) c' + sz.STExpDrift n E u σ c')
    (ϑ' := fun c' => deriv (fun τ => ϑ τ c') u) hA hϑd a
  refine h.congr_deriv ?_
  simp only [STExpQsrc, STQop, STPsum, Finset.sum_add_distrib]
  ring

/-- **4c** `1 ≤ ℓ_t`: `ellT = min (max (g/√|1-t|) 1) L` and `1 ≤ L`. -/
theorem expDuh_one_le_ellT (L : ℕ) (g t : ℝ) (hL : 1 ≤ L) : 1 ≤ RBM.ellT L g t :=
  RBM.one_le_ellT (Nat.one_le_cast.mpr hL)

/-- `∂_uϑ_{u,b}` is interval integrable on `[s,t] ⊂ [0,1)`: measurable (`measurable_deriv`) and, by the fourth
conjunct of `STMollifierProps` and `1 ≤ ℓ_u`, bounded by `|C| (1-t)⁻¹`. -/
private theorem expDuh_intervalIntegrable_deriv {d L m : ℕ} [NeZero L] {g C c : ℝ}
    {ϑ : ℝ → (Fin (m + 1) → Zd d L) → ℂ} (hϑ : STMollifierProps (d := d) g C c ϑ) (hL : 1 ≤ L)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1) (b : Fin (m + 1) → Zd d L) :
    IntervalIntegrable (fun u => deriv (fun τ => ϑ τ b) u) MeasureTheory.volume s t := by
  have hmeas : Measurable (deriv (fun τ => ϑ τ b)) := measurable_deriv _
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hst]
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := |C| * (1 - t)⁻¹)
    (by simp [Real.volume_Icc]) hmeas.aestronglyMeasurable ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun u hu => ?_
  have hu0 : 0 ≤ u := hs0.trans hu.1
  have hu1 : u < 1 := hu.2.trans_lt ht1
  have hb := hϑ.2.2.2 u hu0 hu1 b
  have hℓ : 1 ≤ RBM.ellT L g u := expDuh_one_le_ellT L g u hL
  have hx0 : 0 ≤ (((RBM.ellT L g u) ^ d)⁻¹) ^ m := by positivity
  have hx1 : (((RBM.ellT L g u) ^ d)⁻¹) ^ m ≤ 1 :=
    pow_le_one₀ (inv_nonneg.2 (by positivity)) (inv_le_one_of_one_le₀ (one_le_pow₀ hℓ))
  have h1t : 0 < 1 - t := by linarith
  have hinv : (1 - u)⁻¹ ≤ (1 - t)⁻¹ := inv_anti₀ h1t (by linarith [hu.2])
  have hinv0 : 0 ≤ (1 - u)⁻¹ := inv_nonneg.2 (by linarith)
  calc ‖deriv (fun τ => ϑ τ b) u‖
      ≤ C * (1 - u)⁻¹ * (((RBM.ellT L g u) ^ d)⁻¹) ^ m := hb
    _ ≤ |C| * (1 - u)⁻¹ * (((RBM.ellT L g u) ^ d)⁻¹) ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hinv0) hx0
    _ ≤ |C| * (1 - u)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hx1 (mul_nonneg (abs_nonneg C) hinv0)
    _ ≤ |C| * (1 - t)⁻¹ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left hinv (abs_nonneg C)

/-- `u ↦ (Θ_{uζ})_{xy}` is continuous at `‖uζ‖ < 1` (RBM2D `MLExpDuhamel_continuousAt_Theta_entry`, `:285`). -/
private theorem expDuh_continuousAt_Theta_entry {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) (ζ : ℂ) {u : ℝ}
    (hu : ‖(u : ℂ) * ζ‖ < 1) (x y : Zd d L) :
    ContinuousAt (fun r : ℝ => RBM.Theta d L g ((r : ℂ) * ζ) x y) u := by
  have h1 : ContinuousAt (fun r : ℝ => (r : ℂ) * ζ) u :=
    (Complex.continuous_ofReal.mul continuous_const).continuousAt
  exact (RBM.continuous_matrix_entry d L x y).continuousAt.comp
    ((RBM.continuousAt_Theta d L g (RBM.norm_SB d L g hL) hu).comp (f := fun r : ℝ => (r : ℂ) * ζ) h1)

/-- The kernel `(thetaKer μ u)_{xy}` is continuous in `u` on `{u : ‖uμ‖ < 1}` (RBM2D
`MLExpDuhamel_continuousOn_thetaGenMat`, `:294`). -/
private theorem expDuh_continuousOn_thetaKer {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) (μ : ℂ) {S : Set ℝ}
    (hS : ∀ u ∈ S, ‖(u : ℂ) * μ‖ < 1) (x y : Zd d L) :
    ContinuousOn (fun u : ℝ => RBM.thetaKer d L g μ u x y) S := by
  simp only [RBM.thetaKer, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
  refine continuousOn_finsetSum _ fun z _ => continuousOn_const.mul fun u hu => ?_
  exact (expDuh_continuousAt_Theta_entry g hL μ (hS u hu) z y).continuousWithinAt

/-- `Θ^{(k)}_{u,σ}` preserves continuity in `u` on a window `S ⊆ [0,1)` (RBM2D
`MLExpDuhamel_continuousOn_thetaSig`, `:303`). -/
private theorem expDuh_continuousOn_ThetaN {d L : ℕ} [NeZero L] (g : ℝ) (hL : 3 ≤ L) {E : ℝ} (hE : |E| ≤ 2)
    {k : ℕ} (σ : Fin k → Bool) {S : Set ℝ} (hS : S ⊆ Set.Ico 0 1)
    {Y : ℝ → (Fin k → Zd d L) → ℂ} (hY : ∀ b, ContinuousOn (fun u => Y u b) S) (a : Fin k → Zd d L) :
    ContinuousOn (fun u => RBM.ThetaN d L g (fun l => RBM.mSigma E (σ l)) u (Y u) a) S := by
  unfold RBM.ThetaN
  refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun b _ => ?_
  exact (expDuh_continuousOn_thetaKer g hL _
    (fun u hu => expDuh_norm_slot hE σ (hS hu).1 (hS hu).2 i) (a i) b).mul (hY (Function.update a i b))

/-- **4d** the source `A_u = STExpQsrc` of the `𝒬`-Duhamel formula is interval integrable on `[s,t] ⊂ [0,1)`:
`𝒬D`, `𝒬Θf`, `Θ𝒬f`, `𝒫f` are continuous; `∂_uϑ` is measurable and bounded (new: RBM2D has a continuous `ϑ̇`). -/
theorem expDuh_intervalIntegrable_Qsrc {d : ℕ} (sz : Sizes d) (n : ℕ) {E : ℝ} (hE : |E| < 2) {C c : ℝ}
    {ϑ : ℝ → (Fin 2 → Zd d (sz.L n)) → ℂ} (hϑ : STMollifierProps (d := d) (sz.lam n) C c ϑ)
    (σ : Fin 2 → Bool) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t < 1)
    (b : Fin 2 → Zd d (sz.L n)) :
    IntervalIntegrable (fun u => sz.STExpQsrc n E u σ ϑ b) MeasureTheory.volume s t := by
  have hL : 3 ≤ sz.L n := sz.three_le_L n
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  have hcf : ∀ b, ContinuousOn (fun u => sz.STExpErr n E u σ b) (Set.Icc s t) := fun b =>
    (expHier_continuousOn_err sz n hE σ b).mono hI
  have hcD : ∀ b, ContinuousOn (fun u => sz.STExpDrift n E u σ b) (Set.Icc s t) := fun b =>
    (expHier_continuousOn_drift sz n hE σ b).mono hI
  have hQD : ContinuousOn (fun u => STQop (d := d) ϑ u (fun c' => sz.STExpDrift n E u σ c') b) (Set.Icc s t) :=
    expDuh_continuousOn_Qop_gen hϑ hI hcD b
  have hθf : ∀ b', ContinuousOn (fun u => sz.STthetaOp n E u σ (fun c' => sz.STExpErr n E u σ c') b')
      (Set.Icc s t) := fun b' =>
    (expDuh_continuousOn_ThetaN (sz.lam n) hL hE.le σ hI hcf b').congr fun u _ =>
      expDuh_STthetaOp_eq_ThetaN sz n E u σ _ b'
  have hQθf : ContinuousOn (fun u => STQop (d := d) ϑ u
      (sz.STthetaOp n E u σ (fun c' => sz.STExpErr n E u σ c')) b) (Set.Icc s t) :=
    expDuh_continuousOn_Qop_gen hϑ hI hθf b
  have hQf : ∀ b', ContinuousOn (fun u => STQop (d := d) ϑ u (fun c' => sz.STExpErr n E u σ c') b')
      (Set.Icc s t) := fun b' => expDuh_continuousOn_Qop_gen hϑ hI hcf b'
  have hθQf : ContinuousOn (fun u => sz.STthetaOp n E u σ
      (STQop (d := d) ϑ u (fun c' => sz.STExpErr n E u σ c')) b) (Set.Icc s t) :=
    (expDuh_continuousOn_ThetaN (sz.lam n) hL hE.le σ hI hQf b).congr fun u _ =>
      expDuh_STthetaOp_eq_ThetaN sz n E u σ _ b
  have hPf : ContinuousOn (fun u => STPsum (d := d) (fun c' => sz.STExpErr n E u σ c') (b 0)) (Set.Icc s t) := by
    unfold STPsum
    exact continuousOn_finsetSum _ fun b' _ => hcf b'
  have hdv := expDuh_intervalIntegrable_deriv hϑ (by omega : 1 ≤ sz.L n) hs0 hst ht1 b
  have hprod : IntervalIntegrable (fun u => STPsum (d := d) (fun c' => sz.STExpErr n E u σ c') (b 0) *
      deriv (fun τ => ϑ τ b) u) MeasureTheory.volume s t :=
    hdv.continuousOn_mul (by rwa [Set.uIcc_of_le hst])
  have hint1 := (hQD.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst).add
    ((hQθf.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst).sub
      (hθQf.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hst))
  have hint2 := hint1.sub hprod
  simp only [STExpQsrc]
  exact hint2

/-- **4e** the pin `STExpDuhamelQ` (`(int_K-L+QE)` `6:109-116`), every `d` (RBM2D `expQDuhamelPin_of_hier`, `:423`,
from `s`, abstract mollifier): the engine at `Y = 𝒬_u f_u`, `D = STExpQsrc`. -/
theorem stExpDuhamelQ_holds (d : ℕ) : STExpDuhamelQ d := by
  intro _ sz n E hE C c ϑ hϑ s t hs0 hst ht1 σ a
  have hI : Set.Icc s t ⊆ Set.Ico 0 1 := fun u hu => ⟨hs0.trans hu.1, hu.2.trans_lt ht1⟩
  exact expDuh_duhamel (sz.lam n) (sz.three_le_L n) hE.le σ hs0 hst ht1
    (Y := fun u b => STQop (d := d) ϑ u (fun c' => sz.STExpErr n E u σ c') b)
    (D := fun u b => sz.STExpQsrc n E u σ ϑ b)
    (fun b => (expDuh_continuousOn_Qop sz n hE hϑ σ b).mono hI)
    (fun b => expDuh_intervalIntegrable_Qsrc sz n hE hϑ σ hs0 hst ht1 b)
    (fun u hu b => by
      have h := expDuh_Qop_hasDerivAt sz n hE hϑ σ u ⟨hs0.trans_lt hu.1, hu.2.trans ht1⟩ b
      rw [expDuh_STthetaOp_eq_ThetaN] at h
      exact h) a

end RBM.Gauss.Sizes

/-! ## 5. Compiled nonempty instances

Data: `d = 3`, `sz0` (`n = 0`: `L = 4`, `W = 32`, `ilambda = 1/64`, so `L^d = 64` sites), `E = 1/2`, the loop
labels `a = (0, e₁)`.  The two pins of this file are applied at `[1/4, 1/2]` (`inst_duhamelZ_holds`,
`inst_duhamelQ_holds`, `inst_duhEq_holds`) and from `s = 0` (`inst_expDuh_plain`, `inst_expDuh_single`).  The
lower-level theorems are applied to the hierarchy `f = STExpErr`, `D = STExpDrift` of `sz0` and to the
mollifier of `stMollifierEx_holds` (all deterministic hypotheses discharged; nothing stays a hypothesis:
`STExpHier` is proved in `Induction/ExpHier`). -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

/-- The pin `STExpDuhamelZ` at `d = 3`, `sz0`, `n = 0`, `E = 1/2`, `[1/4, 1/2]`, `A = {1,2}`, `σ = (+,-)`. -/
theorem inst_duhamelZ_holds :
    RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
      RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
          (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
      ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) (Finset.univ : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
          (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)) ![0, Pi.single 0 1] :=
  inst_duhamelZ (stExpDuhamelZ_holds 3)

/-- The pin `STExpDuhamelQ` at the same data, for the mollifier of `stMollifierEx_holds`. -/
theorem inst_duhamelQ_holds :
    ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
      STQop (d := 3) ϑ (1 / 2) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, false] b) ![0, Pi.single 0 1] =
        RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
          (STQop (d := 3) ϑ (1 / 4) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b)) ![0, Pi.single 0 1] +
        ∫ u in (1 / 4 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] u (1 / 2)
          (sz0.STExpQsrc 0 (1 / 2) u ![true, false] ϑ) ![0, Pi.single 0 1] :=
  inst_duhamelQ (stExpDuhamelQ_holds 3)

/-- The Duhamel identities of `STExpDuhEq` along `[0, 1/16]` (the flow `z0`), from `stExpDuhamelZ_holds 3`. -/
theorem inst_duhEq_holds : STExpDuhEq sz0 (STflowE z0) sInst tInst :=
  inst_duhEq (stExpDuhamelZ_holds 3)

/-- `expDuh_plain` from `s = 0` (the endpoint where `STExpHier` gives continuity only), `σ = (+,+)`, `t = 1/2`. -/
theorem inst_expDuh_plain :
    sz0.STExpErr 0 (1 / 2) (1 / 2) ![true, true] ![0, Pi.single 0 1] =
      RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] 0 (1 / 2)
        (fun b => sz0.STExpErr 0 (1 / 2) 0 ![true, true] b) ![0, Pi.single 0 1] +
      ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![true, true] u (1 / 2)
        (fun b => sz0.STExpDrift 0 (1 / 2) u ![true, true] b) ![0, Pi.single 0 1] :=
  expDuh_plain sz0 0 (by norm_num [abs_of_pos]) 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
    ![true, true] ![0, Pi.single 0 1]

/-- `stExpDuhamelZ_holds 3` at `A = {2}` (`Fin` index `1`), `σ = (-,+)`, from `s = 0` to `t = 1/2`. -/
theorem inst_expDuh_single :
    RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
        (fun b => sz0.STExpErr 0 (1 / 2) (1 / 2) ![false, true] b) ![0, Pi.single 0 1] =
      RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] 0 (1 / 2)
          (fun b => sz0.STExpErr 0 (1 / 2) 0 ![false, true] b)) ![0, Pi.single 0 1] +
      ∫ u in (0 : ℝ)..(1 / 2 : ℝ), RBM.zeroModeSet 3 (sz0.L 0) ({1} : Finset (Fin 2))
        (RBM.Ind.Ugen 3 (sz0.L 0) (sz0.lam 0) (1 / 2) ![false, true] u (1 / 2)
          (fun b => sz0.STExpDrift 0 (1 / 2) u ![false, true] b)) ![0, Pi.single 0 1] :=
  stExpDuhamelZ_holds 3 (by norm_num) sz0 0 (1 / 2) (by norm_num [abs_of_pos]) 0 (1 / 2) le_rfl
    (by norm_num) (by norm_num) ![false, true] {1} ![0, Pi.single 0 1]

end RBM.Gauss.Step6Inst

/-! ### The lower-level theorems at the same data -/

namespace RBM.Gauss.Step6Inst

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.Gauss.SizesInst RBM.Gauss.InductionDefsInst RBM.Gauss.Step34Inst

private theorem expDuh_inst_hier (σ : Fin 2 → Bool) (b : Fin 2 → Zd 3 (sz0.L 0)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun v => sz0.STExpErr 0 (1 / 2) v σ b)
      (RBM.ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun l => RBM.mSigma (1 / 2) (σ l)) u
        (fun c => sz0.STExpErr 0 (1 / 2) u σ c) b + sz0.STExpDrift 0 (1 / 2) u σ b) u := by
  intro u hu
  have h := expHier_hasDerivAt sz0 0 (E := 1 / 2) (by norm_num [abs_of_pos]) σ b u hu
  rwa [expDuh_STthetaOp_eq_ThetaN] at h

private theorem expDuh_inst_Icc : Set.Icc (1 / 4 : ℝ) (1 / 2) ⊆ Set.Ico 0 1 :=
  fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩

private theorem expDuh_inst_cont_err (σ : Fin 2 → Bool) (b : Fin 2 → Zd 3 (sz0.L 0)) :
    ContinuousOn (fun u => sz0.STExpErr 0 (1 / 2) u σ b) (Set.Icc (1 / 4 : ℝ) (1 / 2)) :=
  (expHier_continuousOn_err sz0 0 (by norm_num [abs_of_pos]) σ b).mono expDuh_inst_Icc

private theorem expDuh_inst_cont_drift (σ : Fin 2 → Bool) (b : Fin 2 → Zd 3 (sz0.L 0)) :
    ContinuousOn (fun u => sz0.STExpDrift 0 (1 / 2) u σ b) (Set.Icc (1 / 4 : ℝ) (1 / 2)) :=
  (expHier_continuousOn_drift sz0 0 (by norm_num [abs_of_pos]) σ b).mono expDuh_inst_Icc

private theorem expDuh_inst_mollifier :
    ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ := by
  obtain ⟨C, c, hC, hc, hex⟩ := stMollifierEx_holds 3 (by norm_num) 1 1 one_pos
  have hlam : 0 < sz0.lam 0 := by simp [sz0]
  have hlam' : sz0.lam 0 ≤ 1 := by
    have : sz0.lam 0 = 1 / 64 := by norm_num [sz0]
    rw [this]; norm_num
  obtain ⟨ϑ, hϑ⟩ := hex (sz0.L 0) (sz0.three_le_L 0) (sz0.lam 0) hlam hlam'
  exact ⟨C, c, ϑ, hϑ⟩

-- 1a at `μ = 1`, `t = 1/2`, `x = 0`, `y = e₁`, `v = 1/4`
example := expDuh_hasDerivAt_uKer (d := 3) (L := sz0.L 0) (sz0.lam 0) 1 (1 / 2) 0 (Pi.single 0 1) (1 / 4)

-- 1b at `μ = m(+) m(-)`, `v = 1/4`, `t = 1/2`
example := expDuh_uKer_mul_thetaKer (d := 3) (L := sz0.L 0) (sz0.lam 0) (sz0.three_le_L 0)
  (μ := RBM.mSigma (1 / 2) true * RBM.mSigma (1 / 2) false) (v := 1 / 4) (t := 1 / 2)
  (RBM.norm_mul_mSigma_lt_one (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) true false)
  (RBM.norm_mul_mSigma_lt_one (by norm_num [abs_of_pos]) (by norm_num) (by norm_num) true false)

-- 1c at `σ = (+,-)`, `v = 1/4`, `t = 1/2`, `A = f_{1/4}`
example := expDuh_Ugen_ThetaN (d := 3) (L := sz0.L 0) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2)
  (by norm_num [abs_of_pos]) ![true, false] (v := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b) ![0, Pi.single 0 1]

-- 1d at `Y = f`, `u = 1/4`, `t = 1/2`
example := expDuh_hasDerivAt_Ugen (d := 3) (L := sz0.L 0) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2)
  (by norm_num [abs_of_pos]) ![true, false] (u := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num)
  (by norm_num) (by norm_num) (Y := fun u b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
  (Y' := fun b => RBM.ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun l => RBM.mSigma (1 / 2) (![true, false] l)) (1 / 4)
    (fun c => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] c) b + sz0.STExpDrift 0 (1 / 2) (1 / 4) ![true, false] b)
  (fun b => expDuh_inst_hier ![true, false] b (1 / 4) ⟨by norm_num, by norm_num⟩) ![0, Pi.single 0 1]

-- 1e at `Y = f` on `[1/4, 1/2]`
example := expDuh_continuousOn_Ugen (d := 3) (L := sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 2)
  (S := Set.Icc (1 / 4 : ℝ) (1 / 2)) (Y := fun u b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
  (fun b => expDuh_inst_cont_err ![true, false] b) ![0, Pi.single 0 1]

-- 1f at `D = STExpDrift` on `[1/4, 1/2]`
example := expDuh_intervalIntegrable_Ugen (d := 3) (L := sz0.L 0) (sz0.lam 0) (1 / 2) ![true, false] (1 / 4) (1 / 2)
  (D := fun u b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)
  (fun b => (expDuh_inst_cont_drift ![true, false] b).intervalIntegrable_of_Icc (by norm_num))
  ![0, Pi.single 0 1]

-- 2a at the hierarchy `Y = f`, `D = STExpDrift`, `[1/4, 1/2]`, `σ = (+,-)`
example := expDuh_duhamel (d := 3) (L := sz0.L 0) (sz0.lam 0) (sz0.three_le_L 0) (E := 1 / 2)
  (by norm_num [abs_of_pos]) ![true, false] (s := 1 / 4) (t := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
  (Y := fun u b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
  (D := fun u b => sz0.STExpDrift 0 (1 / 2) u ![true, false] b)
  (fun b => expDuh_inst_cont_err ![true, false] b)
  (fun b => (expDuh_inst_cont_drift ![true, false] b).intervalIntegrable_of_Icc (by norm_num))
  (fun u hu b => expDuh_inst_hier ![true, false] b u ⟨by linarith [hu.1], by linarith [hu.2]⟩)
  ![0, Pi.single 0 1]

-- 2b at `u = 1/4`, `σ = (+,-)`, `A = f_{1/4}`
example := expDuh_STthetaOp_eq_ThetaN sz0 0 (1 / 2) (1 / 4) ![true, false]
  (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b) ![0, Pi.single 0 1]

-- 3b at `A = {1,2}`, `Y = f`, `u = 1/4`
example := expDuh_zeroModeSet_hasDerivAt (d := 3) (L := sz0.L 0) (Finset.univ : Finset (Fin 2)) (u := 1 / 4)
  (Y := fun v b => sz0.STExpErr 0 (1 / 2) v ![true, false] b)
  (Y' := fun b => RBM.ThetaN 3 (sz0.L 0) (sz0.lam 0) (fun l => RBM.mSigma (1 / 2) (![true, false] l)) (1 / 4)
    (fun c => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] c) b + sz0.STExpDrift 0 (1 / 2) (1 / 4) ![true, false] b)
  (fun b => expDuh_inst_hier ![true, false] b (1 / 4) ⟨by norm_num, by norm_num⟩) ![0, Pi.single 0 1]

-- 3c at `A = {2}`, `Y = f` on `[1/4, 1/2]`
example := expDuh_zeroModeSet_continuousOn (d := 3) (L := sz0.L 0) ({1} : Finset (Fin 2))
  (S := Set.Icc (1 / 4 : ℝ) (1 / 2)) (Y := fun v b => sz0.STExpErr 0 (1 / 2) v ![true, false] b)
  (fun b => expDuh_inst_cont_err ![true, false] b) ![0, Pi.single 0 1]

-- 4a at the mollifier of `stMollifierEx_holds`
example : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
    ContinuousOn (fun u => STQop (d := 3) ϑ u (fun b => sz0.STExpErr 0 (1 / 2) u ![true, false] b)
      ![0, Pi.single 0 1]) (Set.Ico 0 1) := by
  obtain ⟨C, c, ϑ, hϑ⟩ := expDuh_inst_mollifier
  exact ⟨C, c, ϑ, hϑ, expDuh_continuousOn_Qop sz0 0 (by norm_num [abs_of_pos]) hϑ ![true, false] _⟩

-- 4b at `u = 1/4`
example : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
    HasDerivAt (fun v => STQop (d := 3) ϑ v (fun b => sz0.STExpErr 0 (1 / 2) v ![true, false] b)
      ![0, Pi.single 0 1])
      (sz0.STthetaOp 0 (1 / 2) (1 / 4) ![true, false]
          (STQop (d := 3) ϑ (1 / 4) (fun b => sz0.STExpErr 0 (1 / 2) (1 / 4) ![true, false] b))
          ![0, Pi.single 0 1] + sz0.STExpQsrc 0 (1 / 2) (1 / 4) ![true, false] ϑ ![0, Pi.single 0 1]) (1 / 4) := by
  obtain ⟨C, c, ϑ, hϑ⟩ := expDuh_inst_mollifier
  exact ⟨C, c, ϑ, hϑ, expDuh_Qop_hasDerivAt sz0 0 (by norm_num [abs_of_pos]) hϑ ![true, false] (1 / 4)
    ⟨by norm_num, by norm_num⟩ _⟩

-- 4c at `L = 4`, `t = 1/2`
example : 1 ≤ RBM.ellT (sz0.L 0) (sz0.lam 0) (1 / 2) :=
  expDuh_one_le_ellT (sz0.L 0) (sz0.lam 0) (1 / 2) (by have := sz0.three_le_L 0; omega)

-- 4d on `[1/4, 1/2]`
example : ∃ (C c : ℝ) (ϑ : ℝ → (Fin 2 → Zd 3 (sz0.L 0)) → ℂ), STMollifierProps (d := 3) (sz0.lam 0) C c ϑ ∧
    IntervalIntegrable (fun u => sz0.STExpQsrc 0 (1 / 2) u ![true, false] ϑ ![0, Pi.single 0 1])
      MeasureTheory.volume (1 / 4) (1 / 2) := by
  obtain ⟨C, c, ϑ, hϑ⟩ := expDuh_inst_mollifier
  exact ⟨C, c, ϑ, hϑ, expDuh_intervalIntegrable_Qsrc sz0 0 (by norm_num [abs_of_pos]) hϑ ![true, false]
    (by norm_num) (by norm_num) (by norm_num) _⟩

end RBM.Gauss.Step6Inst

end

#print axioms RBM.Gauss.Sizes.expDuh_hasDerivAt_uKer
#print axioms RBM.Gauss.Sizes.expDuh_uKer_mul_thetaKer
#print axioms RBM.Gauss.Sizes.expDuh_Ugen_ThetaN
#print axioms RBM.Gauss.Sizes.expDuh_hasDerivAt_Ugen
#print axioms RBM.Gauss.Sizes.expDuh_continuousOn_Ugen
#print axioms RBM.Gauss.Sizes.expDuh_intervalIntegrable_Ugen
#print axioms RBM.Gauss.Sizes.expDuh_duhamel
#print axioms RBM.Gauss.Sizes.expDuh_STthetaOp_eq_ThetaN
#print axioms RBM.Gauss.Sizes.expDuh_plain
#print axioms RBM.Gauss.Sizes.expDuh_zeroModeSet_hasDerivAt
#print axioms RBM.Gauss.Sizes.expDuh_zeroModeSet_continuousOn
#print axioms RBM.Gauss.Sizes.stExpDuhamelZ_holds
#print axioms RBM.Gauss.Sizes.expDuh_continuousOn_Qop
#print axioms RBM.Gauss.Sizes.expDuh_Qop_hasDerivAt
#print axioms RBM.Gauss.Sizes.expDuh_one_le_ellT
#print axioms RBM.Gauss.Sizes.expDuh_intervalIntegrable_Qsrc
#print axioms RBM.Gauss.Sizes.stExpDuhamelQ_holds
#print axioms RBM.Gauss.Step6Inst.inst_duhamelZ_holds
#print axioms RBM.Gauss.Step6Inst.inst_duhamelQ_holds
#print axioms RBM.Gauss.Step6Inst.inst_duhEq_holds
#print axioms RBM.Gauss.Step6Inst.inst_expDuh_plain
#print axioms RBM.Gauss.Step6Inst.inst_expDuh_single
