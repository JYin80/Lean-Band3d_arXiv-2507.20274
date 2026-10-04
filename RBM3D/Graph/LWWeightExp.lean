/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Graph.LWPins
import RBM3D.Graph.LWStein
import RBM3D.Graph.LWVocab
import RBM3D.Gauss.FineModel
import RBM3D.Green.IBPPoly
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# LW-05: the weight expansion `(Owx)` (T2107)

Paper: arXiv:2507.20274, `paper/tex/7_8_light_weight.tex:294-306` (`7_8:294-306`, lemma `ssl`,
cited from `[yang2021]` Lemma 3.5).  Design: T2040 (split row LW-05).

## Contents (namespace `RBM.Graph`)

1. **The bridge** from the one-size law `PF d L W g` to the merged Stein layer on `Sizes.seqP`
   (`lwWxSizes` is the constant size sequence `(L, W, g)`; the section index is `n = 0`):
   `lwWx_integral` (a: `∫ F ∘ slice ∂seqP = ∫ F ∂PF`, through the section `lwWxSec` of `slice`),
   `lwWx_lwG`, `lwWx_lwS_apply`, `lwWx_lwSp`, `lwWx_hSp`, `lwWx_flow`, `lwWx_im_pos`,
   `lwWx_mE_ne` (b), the ring map `lwWxRename` of resolvent polynomials, with the swap
   `(false, a, b) ↦ (b, a, false)` (c: `lwWx_lwPoly`), and `lwWx_dh`, `lwWx_lwdf`,
   `lwWx_hasDerivAt` (d).
2. **The weight expansion on `PF`.**  `lwWeightExp_holds : ∀ d, LWweightExp d` (the pin of
   `Graph/LWPins.lean:106`, with `S⁺ = LWPins_lwSp d L W g E t`, the argument order of the
   definition of `LWPins_lwSp`, after the six-edit amendment of T2107, DECISIONS §34), for every
   `d`, from `owx_integral` through the bridge for `0 < t < 1`, and `t = 0` separately.
3. **`(Owx)` as a graph operation**: `owxT1`, `owxT2`, `owxT3 q`, `owxT4 q` (the four terms as
   graphs on `I ⊕ Fin k`), `owx_graph_E` (the identity of expectations of values),
   `owxT*_counters`, `owxT*_ord` (every term has `ord Γ + 1`; `n_S + 1`, `n_W + 1 or 2`,
   `n_V + 1 or 2`, `n_M` unchanged).
4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped NNReal ENNReal

namespace RBM.Graph

open RBM RBM.Gauss RBM.Green

/-! ## 1. The bridge `PF d L W g` ↔ `Sizes.seqP` -/

section Bridge

/-- The constant size sequence `(L n, W n, lam n) = (L, W, g)`; the bridge sits at `n = 0`. -/
abbrev lwWxSizes (d L W : ℕ) (g : ℝ) [NeZero W] (hL : 3 ≤ L) : Sizes d where
  L := fun _ => L
  W := fun _ => W
  lam := fun _ => g
  three_le_L := fun _ => hL
  W_pos := fun _ => Nat.pos_of_ne_zero (NeZero.ne W)

variable {d L W : ℕ} [NeZero L] [NeZero W] {g : ℝ} (hL : 3 ≤ L) (E t : ℝ)

/-- (b) the resolvent entry of the one-size law is that of the sequence-space flow (`seqHflow = Hflow ∘ slice`). -/
theorem lwWx_lwG (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (x y : Idx d L W) :
    lwG (lwWxSizes d L W g hL) 0 (zt E t) t x y ω =
      LWPins_lwG d L W E t (Sizes.slice (lwWxSizes d L W g hL) 0 ω) x y := rfl

/-- (b) `S = t S^{(B)}`: the merged `lwS` at `n = 0`, `u = t` is the matrix of the pin's `LWPins_lwS`. -/
theorem lwWx_lwS : lwS (lwWxSizes d L W g hL) 0 t = Matrix.of (LWPins_lwS d L W g t) := by
  ext i j
  simp [lwS, LWPins_lwS]

/-- (b) `S⁺`: the merged `lwSplus` at `n = 0`, `u = t`, `m = m(E)` is `LWPins_lwSp d L W g E t` (coupling `g`,
energy `E`, the argument order of the definition). -/
theorem lwWx_lwSp : lwSplus (lwWxSizes d L W g hL) 0 t (mE E) = LWPins_lwSp d L W g E t := by
  unfold lwSplus LWPins_lwSp
  rw [lwWx_lwS]

/-- (b) `Im z_t > 0` for `|E| < 2` and `t < 1`. -/
theorem lwWx_im_pos (hE : |E| < 2) (ht1 : t < 1) : 0 < (zt E t).im := by
  rw [zt_im]
  exact mul_pos (by linarith) (mE_im_pos hE)

/-- (b) `m(E) ≠ 0` for `|E| < 2`. -/
theorem lwWx_mE_ne (hE : |E| < 2) : mE E ≠ 0 := by
  intro h
  have := mE_im_pos hE
  rw [h] at this
  simp at this

/-- (b) the flow relation `z_t + t m = -m⁻¹`. -/
theorem lwWx_flow (hE : |E| < 2) : zt E t + (t : ℂ) * mE E = -(mE E)⁻¹ := by
  have h0 := lwWx_mE_ne E hE
  have hm := mE_mul hE.le
  unfold zt
  field_simp
  linear_combination hm

/-- (b) `S⁺` solves `S⁺ - m² S⁺ S = S` (`hSp` of `owx_integral`) at `0 ≤ t < 1`. -/
theorem lwWx_hSp (hE : |E| < 2) (ht0 : 0 ≤ t) (ht1 : t < 1) (i j : Idx d L W) :
    LWPins_lwSp d L W g E t i j - mE E ^ 2 * ∑ w, LWPins_lwSp d L W g E t i w *
        lwS (lwWxSizes d L W g hL) 0 t w j = lwS (lwWxSizes d L W g hL) 0 t i j := by
  have hm : ‖mE E‖ ^ 2 * t < 1 := by
    rw [norm_mE hE.le]; simpa using ht1
  have := lwSplus_spec (sz := lwWxSizes d L W g hL) (n := 0) ht0 hm i j
  rwa [lwWx_lwSp] at this

/-- The resolvent `G^* = (H - z̄)⁻¹` is the conjugate transpose of `G = (H - z)⁻¹` at a Hermitian `H`. -/
theorem lwWx_Gres_conjTranspose {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) : (Gres H z true)ᴴ = Gres H z false := by
  have hH' : Hᴴ = H := hH
  simp only [Gres, ↓reduceIte, Bool.false_eq_true, ← Matrix.nonsing_inv_eq_ringInverse,
    Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, hH', Complex.star_def]

/-- (c) the swap: `(H - z̄)⁻¹_{ab} = conj ((H - z)⁻¹_{ba})` at a Hermitian `H`.  The plain reordering
`(false, a, b) ↦ (a, b, false)` is wrong for `a ≠ b`. -/
theorem lwWx_Gres_false {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (z : ℂ) (a b : ι) : Gres H z false a b = star (Gres H z true b a) := by
  rw [← lwWx_Gres_conjTranspose hH z]
  rfl

/-- (d) the matrix-level derivative of `G^σ_{ab}` in the direction `E_{αw}`: `-G^σ_{aα} G^σ_{wb}`
(`σ = +`: the merged `hasDerivAt_inverse_apply`; `σ = -` is the same for `A = H - z̄`). -/
theorem lwWx_hasDerivAt_Gres {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (σ : Bool) (α w a b : ι) :
    HasDerivAt (fun s : ℂ => Gres (H + s • single α w (1 : ℂ)) z σ a b)
      (-(Gres H z σ a α * Gres H z σ w b)) 0 := by
  have hz' : (if σ then z else (starRingEnd ℂ) z).im ≠ 0 := by
    cases σ <;> simpa using hz
  have hU := isUnit_sub_smul_of_isHermitian hH hz'
  have h := hasDerivAt_inverse_apply hU α w a b
  have hfun : (fun s : ℂ => Gres (H + s • single α w (1 : ℂ)) z σ a b) = fun s : ℂ =>
      Ring.inverse ((H - (if σ then z else (starRingEnd ℂ) z) • (1 : Matrix ι ι ℂ)) +
        s • single α w (1 : ℂ)) a b := by
    funext s
    simp only [Gres]
    rw [add_sub_right_comm]
  rw [hfun]
  exact h

variable (d L W) in
/-- (c) the variable map: the entry `(false, a, b)` of `G^* = (H - z̄)⁻¹` is `conj G_{ba}`, the variable
`(b, a, false)` of `lwVar`; the variable `(true, a, b)` is `(a, b, true)`. -/
def lwWxVar (v : Bool × Idx d L W × Idx d L W) : Idx d L W × Idx d L W × Bool :=
  if v.1 then (v.2.1, v.2.2, true) else (v.2.2, v.2.1, false)

variable (d L W) in
/-- (c) **the ring map** of resolvent polynomials `P ↦ P'`: `LWPins_resPoly`'s `Bool × Idx × Idx`
variables to `lwVar`'s `Idx × Idx × Bool` variables, `P' = rename (lwWxVar) P`. -/
def lwWxRename :
    MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ →ₐ[ℂ] MvPolynomial (Idx d L W × Idx d L W × Bool) ℂ :=
  MvPolynomial.rename (lwWxVar d L W)

/-- (c) the resolvent polynomial `P'` of `lwWxRename P` at the sample `ω` is `P` evaluated at the resolvents
`Gres (H_u(slice ω)) z σ` of `LWPins_resPoly` (any `z`, `u`). -/
theorem lwWx_lwPoly_eval (z : ℂ) (u : ℝ) (ω : Sizes.SeqΩ (lwWxSizes d L W g hL))
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W P) ω =
      MvPolynomial.eval (fun v => Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)) z
        v.1 v.2.1 v.2.2) P := by
  unfold lwPoly lwWxRename
  rw [MvPolynomial.eval_rename]
  refine congrArg (fun F => MvPolynomial.eval F P) (funext fun v => ?_)
  rcases v with ⟨σ, a, b⟩
  have hH : (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)).IsHermitian :=
    Sizes.seqHflow_isHermitian (lwWxSizes d L W g hL) 0 u ω
  cases σ
  · simp only [Function.comp_apply, lwWxVar, lwVar, lwG, lwGm, Bool.false_eq_true, ↓reduceIte]
    exact (lwWx_Gres_false hH z a b).symm
  · rfl

/-- (c) `lwPoly sz 0 z_t t P' ω = LWPins_lwf P (slice ω)`. -/
theorem lwWx_lwPoly (ω : Sizes.SeqΩ (lwWxSizes d L W g hL))
    (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    lwPoly (lwWxSizes d L W g hL) 0 (zt E t) t (lwWxRename d L W P) ω =
      LWPins_lwf d L W E t P (Sizes.slice (lwWxSizes d L W g hL) 0 ω) :=
  lwWx_lwPoly_eval hL (zt E t) t ω P

/-- (d) the derivative of a variable: `∂_{h_{αw}}` of `lwVar (lwWxVar v)` is the matrix-level derivative
`-G^σ_{aα} G^σ_{wb}` of the entry `(σ, a, b)` of `Gres` (blue: `dhSample_lwG`; red: `dhSample_lwG_star`,
with the swap `x ↔ y`). -/
theorem lwWx_dh_var {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (v : Bool × Idx d L W × Idx d L W) :
    dhSample (lwWxSizes d L W g hL) 0 u α w (lwVar (lwWxSizes d L W g hL) 0 z u (lwWxVar d L W v)) ω =
      -(Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)) z v.1 v.2.1 α *
        Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)) z v.1 w v.2.2) := by
  rcases v with ⟨σ, a, b⟩
  have hH : (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)).IsHermitian :=
    Sizes.seqHflow_isHermitian (lwWxSizes d L W g hL) 0 u ω
  cases σ
  · have h1 : dhSample (lwWxSizes d L W g hL) 0 u α w
        (lwVar (lwWxSizes d L W g hL) 0 z u (lwWxVar d L W (false, a, b))) ω =
        dhSample (lwWxSizes d L W g hL) 0 u α w (fun ω => star (lwG (lwWxSizes d L W g hL) 0 z u b a ω)) ω := by
      rfl
    rw [h1, dhSample_lwG_star (lwWxSizes d L W g hL) 0 hz hu α w b a ω]
    simp only [lwG, lwGm, lwWx_Gres_false hH z, star_mul']
    rw [mul_comm]
    rfl
  · have h1 : dhSample (lwWxSizes d L W g hL) 0 u α w
        (lwVar (lwWxSizes d L W g hL) 0 z u (lwWxVar d L W (true, a, b))) ω =
        dhSample (lwWxSizes d L W g hL) 0 u α w (lwG (lwWxSizes d L W g hL) 0 z u a b) ω := by
      rfl
    rw [h1, dhSample_lwG (lwWxSizes d L W g hL) 0 hz hu α w a b ω]
    rfl

/-- (d) **the derivatives agree**: for a resolvent polynomial `P`, the map `s ↦ f_P(H + s E_{αw})` has at
`s = 0` the derivative `∂_{h_{αw}}` of `lwPoly (P')` (`dhSample`). -/
theorem lwWx_hasDerivAt {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    HasDerivAt (fun s : ℂ => MvPolynomial.eval (fun v => Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω) +
        s • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2) P)
      (dhSample (lwWxSizes d L W g hL) 0 u α w (lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W P)) ω) 0 := by
  have hH : (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)).IsHermitian :=
    Sizes.seqHflow_isHermitian (lwWxSizes d L W g hL) 0 u ω
  -- the value at `s = 0`
  have hval : ∀ P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ,
      MvPolynomial.eval (fun v => Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω) +
        (0 : ℂ) • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2) P =
        lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W P) ω := by
    intro P
    simp only [zero_smul, add_zero]
    exact (lwWx_lwPoly_eval hL z u ω P).symm
  have ht1 := fun P => lwPoly_tame1 (sz := lwWxSizes d L W g hL) (n := 0) hz u (lwWxRename d L W P)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have e : lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W (MvPolynomial.C a)) = fun _ => a := by
      funext ω'
      simp [lwPoly, lwWxRename]
    rw [e, lwStein_dh_const]
    exact (hasDerivAt_const (0 : ℂ) a).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by simp)
  | add p q hp hq =>
    have e : lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W (p + q)) = fun ω' =>
        lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W p) ω' +
          lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W q) ω' := by
      funext ω'
      simp [lwPoly, lwWxRename]
    rw [e, lwStein_dh_add (ht1 p) (ht1 q)]
    exact (hp.add hq).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by simp)
  | mul_X p v hp =>
    have e : lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W (p * MvPolynomial.X v)) = fun ω' =>
        lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W p) ω' *
          lwVar (lwWxSizes d L W g hL) 0 z u (lwWxVar d L W v) ω' := by
      funext ω'
      simp [lwPoly, lwWxRename]
    rw [e, lwStein_dh_mul (ht1 p) (lwVar_tame1 hz u _), lwWx_dh_var hL hz hu α w ω v]
    have hv := lwWx_hasDerivAt_Gres hH hz.ne' v.1 α w v.2.1 v.2.2
    have hm := hp.mul hv
    refine (hm.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    · have hvar : Gres (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω) +
          (0 : ℂ) • single α w (1 : ℂ)) z v.1 v.2.1 v.2.2 =
          lwVar (lwWxSizes d L W g hL) 0 z u (lwWxVar d L W v) ω := by
        have := hval (MvPolynomial.X v)
        simpa [lwPoly, lwWxRename, MvPolynomial.eval_X, MvPolynomial.rename_X] using this
      rw [hval p, hvar]
    · simp

/-- (d) **the derivatives agree** (the matrix-level `LWPins_dH` against `dhSample`), for `0 < t` and `Im z > 0`:
`LWPins_lwdf P (slice ω) α w = dhSample sz 0 t α w (lwPoly sz 0 z_t t P') ω`. -/
theorem lwWx_dh {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    dhSample (lwWxSizes d L W g hL) 0 u α w (lwPoly (lwWxSizes d L W g hL) 0 z u (lwWxRename d L W P)) ω =
      LWPins_dH (LWPins_resPoly d L W z P) (Hflow d L W u (Sizes.slice (lwWxSizes d L W g hL) 0 ω)) α w :=
  (lwWx_hasDerivAt hL hz hu α w ω P).deriv.symm

/-- The pin's `LWPins_lwdf` at `(z_t, t)`, the form of `lwWx_dh` used below. -/
theorem lwWx_lwdf (hz : 0 < (zt E t).im) (ht : 0 < t) (α w : Idx d L W)
    (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (P : MvPolynomial (Bool × Idx d L W × Idx d L W) ℂ) :
    LWPins_lwdf d L W E t P (Sizes.slice (lwWxSizes d L W g hL) 0 ω) α w =
      dhSample (lwWxSizes d L W g hL) 0 t α w (lwPoly (lwWxSizes d L W g hL) 0 (zt E t) t (lwWxRename d L W P)) ω :=
  (lwWx_dh hL hz ht α w ω P).symm

/-- The entries of `lwS` and `LWPins_lwS` agree. -/
theorem lwWx_lwS_apply (x y : Idx d L W) :
    lwS (lwWxSizes d L W g hL) 0 t x y = LWPins_lwS d L W g t x y := by
  simp [lwS, LWPins_lwS]

/-- The resolvent entry of the pin, the centred one: `Ǧ_{xy} = G_{xy} - m δ_{xy}`. -/
theorem lwWx_lwGc (ω : Sizes.SeqΩ (lwWxSizes d L W g hL)) (x : Idx d L W) :
    LWPins_lwGc d L W E t (Sizes.slice (lwWxSizes d L W g hL) 0 ω) x x =
      lwG (lwWxSizes d L W g hL) 0 (zt E t) t x x ω - mE E := by
  simp [LWPins_lwGc, lwWx_lwG hL E t ω x x]

/-! ### (a) the transport of the integral from `seqP` to `PF` -/

variable (g) in
/-- The section of `slice` at size `0`: the one-size sample, extended by `0` at the other sizes. -/
def lwWxSec (ω : Ω d L W) : Sizes.SeqΩ (lwWxSizes d L W g hL) :=
  Function.extend (fun c : CoordF d L W => (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL))) ω 0

theorem lwWx_sec_inj : Function.Injective
    (fun c : CoordF d L W => (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL))) := by
  intro c c' h
  simpa using h

variable (g) in
theorem lwWx_slice_sec (ω : Ω d L W) : Sizes.slice (lwWxSizes d L W g hL) 0 (lwWxSec g hL ω) = ω := by
  funext c
  exact (lwWx_sec_inj (g := g) hL).extend_apply ω 0 c

theorem lwWx_continuous_sec : Continuous (lwWxSec (d := d) (L := L) (W := W) g hL) := by
  classical
  refine continuous_pi fun b => ?_
  by_cases h : ∃ c : CoordF d L W, (⟨0, c⟩ : Sizes.SeqCoord (lwWxSizes d L W g hL)) = b
  · obtain ⟨c, rfl⟩ := h
    have : (fun ω : Ω d L W => lwWxSec g hL ω ⟨0, c⟩) = fun ω => ω c := by
      funext ω
      exact (lwWx_sec_inj (g := g) hL).extend_apply ω 0 c
    change Continuous (fun ω : Ω d L W => lwWxSec g hL ω ⟨0, c⟩)
    rw [this]
    exact continuous_apply c
  · have : (fun ω : Ω d L W => lwWxSec g hL ω b) = fun _ => 0 := by
      funext ω
      simp only [lwWxSec]
      rw [Function.extend_apply' _ _ _ h]
      rfl
    change Continuous (fun ω : Ω d L W => lwWxSec g hL ω b)
    rw [this]
    exact continuous_const

/-- **(a) the bridge of the integral**: `∫ F ∂seqP = ∫ G ∂PF` whenever `F = G ∘ slice` and `F` is
continuous (`Sizes.seqP_map_slice`). -/
theorem lwWx_integral {F : Sizes.SeqΩ (lwWxSizes d L W g hL) → ℂ} {G : Ω d L W → ℂ}
    (hF : Continuous F) (h : ∀ ω', G (Sizes.slice (lwWxSizes d L W g hL) 0 ω') = F ω') :
    ∫ ω, G ω ∂(PF d L W g) = ∫ ω', F ω' ∂(Sizes.seqP (lwWxSizes d L W g hL)) := by
  have hG : G = F ∘ lwWxSec g hL := by
    funext ω
    have := h (lwWxSec g hL ω)
    rw [lwWx_slice_sec] at this
    exact this
  have hGc : Continuous G := by rw [hG]; exact hF.comp (lwWx_continuous_sec hL)
  have hmap := Sizes.seqP_map_slice (lwWxSizes d L W g hL) 0
  have e : ∫ ω', F ω' ∂(Sizes.seqP (lwWxSizes d L W g hL)) =
      ∫ ω', G (Sizes.slice (lwWxSizes d L W g hL) 0 ω') ∂(Sizes.seqP (lwWxSizes d L W g hL)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω' => (h ω').symm)
  rw [e, ← integral_map (Sizes.measurable_slice (lwWxSizes d L W g hL) 0).aemeasurable
    hGc.aestronglyMeasurable, hmap]

end Bridge

/-! ## 2. The weight expansion on `PF` (the pin `LWweightExp`, `Graph/LWPins.lean:106`) -/

section PinProof

/-- Closure of `Tame` under the operations of the expansion (copy of the local macro of
`Graph/LWStein.lean`, which is not exported). -/
local macro "lwx_tame" : tactic =>
  `(tactic| repeat' first
    | exact Tame.const _
    | assumption
    | (apply lwStein_tame_lwG; assumption)
    | (apply lwStein_tame_dhSample; assumption)
    | apply Tame.mul
    | apply Tame.add
    | apply Tame.sub
    | apply Tame.neg
    | (apply Tame.sum; intros; skip))

/-- `G = (0 - z)⁻¹` at `H = 0` on the index type `Idx` (the merged `Gres_zero_eq_scalar` is on `Vtx`). -/
theorem lwWx_gres_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {z : ℂ} (hz : z ≠ 0) :
    Gres (0 : Matrix ι ι ℂ) z true = (-z)⁻¹ • (1 : Matrix ι ι ℂ) := by
  rw [Gres]
  simp only [↓reduceIte]
  rw [zero_sub, ← neg_smul, ring_inverse_smul_one (neg_ne_zero.2 hz)]

/-- **`t = 0`**: `H_0 = 0`, `z_0 = E + m = -m⁻¹`, `G = m I`, so `Ǧ_{yy} = 0`. -/
theorem lwWx_gc_zero {E : ℝ} (hE : |E| < 2) {d L W : ℕ} [NeZero L] [NeZero W] (ω : Ω d L W)
    (y : Idx d L W) : LWPins_lwGc d L W E 0 ω y y = 0 := by
  have hm0 : mE E ≠ 0 := by
    intro h
    have := mE_im_pos hE
    rw [h] at this
    simp at this
  have hz : zt E 0 = -(mE E)⁻¹ := by
    have hm := mE_mul hE.le
    simp only [zt, Complex.ofReal_zero, sub_zero, one_mul]
    field_simp
    linear_combination hm
  have hH : Hflow d L W 0 ω = 0 := by
    simp [Hflow]
  have hz0 : zt E 0 ≠ 0 := by
    rw [hz]; exact neg_ne_zero.2 (inv_ne_zero hm0)
  have hG : Gres (Hflow d L W 0 ω) (zt E 0) true = mE E • (1 : Matrix (Idx d L W) (Idx d L W) ℂ) := by
    rw [hH, lwWx_gres_zero hz0, hz, neg_neg, inv_inv]
  simp [LWPins_lwGc, LWPins_lwG, hG]

theorem lwWx_lwS_zero (d L W : ℕ) [NeZero W] (g : ℝ) (x y : Idx d L W) : LWPins_lwS d L W g 0 x y = 0 := by
  simp [LWPins_lwS]

theorem lwWx_lwSp_zero (d L W : ℕ) [NeZero L] [NeZero W] (g E : ℝ) (x y : Idx d L W) :
    LWPins_lwSp d L W g E 0 x y = 0 := by
  have : Matrix.of (LWPins_lwS d L W g 0) = 0 := by
    ext i j
    simp [lwWx_lwS_zero]
  simp [LWPins_lwSp, this]

/-- **The weight expansion `(Owx)`** (`7_8:294-306`, `ssl`) on the one-size law `PF d L W g`: the pin `LWweightExp`
for every `d`, with `S⁺ = LWPins_lwSp d L W g E t`.  For `0 < t < 1`: `owx_integral` (hypothesis `gaussIBP`,
proved) through the bridge; for `t = 0` both sides vanish.  No condition on the sign of `g`. -/
theorem lwWeightExp_holds (d : ℕ) : LWweightExp d := by
  intro L W _ _ hL g E t hE ht0 ht1 P x
  rcases ht0.eq_or_lt with rfl | ht
  · simp [lwWx_gc_zero hE, lwWx_lwS_zero, lwWx_lwSp_zero]
  · set sz := lwWxSizes d L W g hL with hsz
    have hz : 0 < (zt E t).im := lwWx_im_pos E t hE ht1
    have key := owx_integral (sz := sz) (n := 0) (gaussIBP sz) hz ht (lwWx_mE_ne E hE) (lwWx_flow E t hE)
      (LWPins_lwSp d L W g E t) (lwWx_hSp hL E t hE ht.le ht1) (lwWxRename d L W P) x
    have hz' : (zt E t).im ≠ 0 := hz.ne'
    have hf : Tame1 sz 0 (lwPoly sz 0 (zt E t) t (lwWxRename d L W P)) :=
      lwPoly_tame1 (sz := sz) (n := 0) hz t (lwWxRename d L W P)
    have tf : Tame sz (lwPoly sz 0 (zt E t) t (lwWxRename d L W P)) := hf.tame
    refine (lwWx_integral hL ?_ ?_).trans (key.trans (lwWx_integral hL ?_ ?_).symm)
    · refine Tame.cont ?_
      lwx_tame
    · intro ω'
      rw [lwWx_lwGc hL E t ω' x, lwWx_lwPoly hL E t ω' P]
    · refine Tame.cont ?_
      lwx_tame
    · intro ω'
      simp only [lwWx_lwGc hL E t ω', ← lwWx_lwPoly hL E t ω' P, lwWx_lwdf hL E t hz ht _ _ ω' P,
        ← lwWx_lwG hL E t ω', ← lwWx_lwS_apply hL t]
      rfl

end PinProof



/-! ## 3. `(Owx)` as a graph operation (T2060d, design row LW-05)

For a graph `Γ` with the weight `Ǧ_{xx}` (the blue circled self-loop `⟨true, true, inr x, inr x⟩`) at an
internal vertex `x`, `p ∈ lwSplit Γ.solid` is the pair (this edge, the other solid edges).  The four terms of
`(Owx)` are graphs on `I ⊕ Fin k` (the `k` new internal vertices `α`, `β`): the old vertices are `inr (inl ·)`
(`owxEmb`), the new ones `inr (inr ·)`; the coefficients carry `m`, `m³` and the signs of `(Owx)`.

* `owxT1`: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f` (`Γ` plus a leaf `α`);
* `owxT2`: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ} f` (the weight dropped, a path `x - α - β`);
* `owxT3 q`, one graph for each solid edge `q.1` of `f` (`q ∈ lwSplit p.2`): `-m Σ_α S_{xα} G_{αx} ∂_{h_{αx}} f`
  (the weight dropped, a leaf `α`, the edge `q.1` replaced by the two edges of its derivative with `w = x`);
* `owxT4 q`: `-m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}} f` (path `x - α - β`, derivative with `(α, w) = (β, α)`).
-/

section OwxGraph

variable {E I : Type*}

/-- The inclusion of the vertices of `Γ` into those of a graph with `k` more internal vertices. -/
def owxEmb (k : ℕ) : E ⊕ I → E ⊕ (I ⊕ Fin k) := Sum.map id Sum.inl

/-- `Γ` with its vertices renamed by `emb`, the edges `s` (solid) and `w` (waved) appended, and the
coefficient multiplied by `c`. -/
def LGraph.owxExt {E' I' : Type*} (Γ : LGraph E I) (emb : E ⊕ I → E' ⊕ I') (c : ℂ)
    (s : List (SEdge (E' ⊕ I'))) (w : List (WEdge (E' ⊕ I'))) : LGraph E' I' where
  solid := Γ.solid.map (SEdge.map emb) ++ s
  waved := Γ.waved.map (WEdge.map emb) ++ w
  dotted := Γ.dotted.map (DEdge.map emb)
  coeff := c * Γ.coeff

/-- The edges replacing a solid edge `e` in its derivative `∂_{h_{αw}}` with the labels `α`, `w` given by the
vertices `a`, `w` (`lwDEdges` with the two new vertices replaced by `a`, `w`): `G_{ab} ↦ G_{aα} G_{wb}`,
`Ḡ_{ab} ↦ Ḡ_{aw} Ḡ_{αb}` (the circle is dropped, `M` is constant). -/
def owxDE {V : Type*} (a w : V) (e : SEdge V) : SEdge V × SEdge V :=
  if e.σ then (⟨true, false, e.src, a⟩, ⟨true, false, w, e.dst⟩)
  else (⟨false, false, e.src, w⟩, ⟨false, false, a, e.dst⟩)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

theorem LGraph.term_owxExt {E' I' : Type*} (Γ : LGraph E I) (emb : E ⊕ I → E' ⊕ I') (c : ℂ)
    (s : List (SEdge (E' ⊕ I'))) (w : List (WEdge (E' ⊕ I'))) (D : LData ι) (ℓ : E' ⊕ I' → ι) :
    (Γ.owxExt emb c s w).term D ℓ =
      c * Γ.term D (ℓ ∘ emb) * (s.map (SEdge.val D ℓ)).prod * (w.map (WEdge.val D ℓ)).prod := by
  simp only [LGraph.term, LGraph.owxExt, List.map_append, List.prod_append, List.map_map]
  have h1 : (SEdge.val D ℓ) ∘ (SEdge.map emb) = SEdge.val D (ℓ ∘ emb) := funext fun e => rfl
  have h2 : (WEdge.val D ℓ) ∘ (WEdge.map emb) = WEdge.val D (ℓ ∘ emb) := funext fun e => rfl
  have h3 : (DEdge.val ℓ) ∘ (DEdge.map emb) = DEdge.val (ℓ ∘ emb) := funext fun e => rfl
  rw [h1, h2, h3]
  ring

/-- The product of the two derivative edge factors of `owxDE` is `-∂_{h_{aw}}` of the edge factor
(`G_{src a} G_{w dst}` for a blue edge, `\bar G_{src w} \bar G_{a dst}` for a red one). -/
theorem owxDE_val {V : Type*} (D : LData ι) (ℓ : V → ι) (a w : V) (e : SEdge V) :
    SEdge.val D ℓ (owxDE a w e).1 * SEdge.val D ℓ (owxDE a w e).2 =
      if e.σ then D.G (ℓ e.src) (ℓ a) * D.G (ℓ w) (ℓ e.dst)
      else star (D.G (ℓ e.src) (ℓ w)) * star (D.G (ℓ a) (ℓ e.dst)) := by
  unfold owxDE
  split_ifs <;> simp [SEdge.val]

end OwxGraph


/-! ### The molecule counter of a graph with pendant vertices -/

section PendantNM

variable {E I I' : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [Fintype I']
  [DecidableEq I']

private theorem owx_adj_comm (Γ : LGraph E I) (u v : E ⊕ I) : Γ.adj u v = Γ.adj v u := by
  simp only [LGraph.adj, or_comm]

theorem owx_molGraph_adj (Γ : LGraph E I) (u v : E ⊕ I) :
    Γ.molGraph.Adj u v ↔ u ≠ v ∧ Γ.adj u v = true := by
  simp only [LGraph.molGraph, SimpleGraph.fromRel_adj, owx_adj_comm Γ v u, or_self]

/-- **Pendant vertices do not change `n_M`**: if `Γ'` has the vertices of `Γ` (`emb`, with a retraction
`ρ`), every edge of `Γ'` either comes from an edge of `Γ` or joins two vertices with the same `ρ`-image, and every
vertex of `Γ'` is joined to the image of its `ρ`-image, then `Γ` and `Γ'` have the same internal molecules. -/
theorem owx_nM_eq (Γ : LGraph E I) (Γ' : LGraph E I') (emb : E ⊕ I → E ⊕ I') (ρ : E ⊕ I' → E ⊕ I)
    (hρ : ∀ v, ρ (emb v) = v) (hemb : ∀ e : E, emb (Sum.inl e) = Sum.inl e)
    (hρe : ∀ e : E, ρ (Sum.inl e) = Sum.inl e)
    (ha : ∀ u v, Γ.adj u v = true → Γ'.adj (emb u) (emb v) = true)
    (hb : ∀ u v, Γ'.adj u v = true → ρ u = ρ v ∨ Γ.adj (ρ u) (ρ v) = true)
    (hc : ∀ w, Γ'.molGraph.Reachable w (emb (ρ w))) : Γ'.nM = Γ.nM := by
  classical
  have hinj : Function.Injective emb := fun u v h => by rw [← hρ u, ← hρ v, h]
  rw [Γ'.nM_eq_card, Γ.nM_eq_card]
  let f : Γ.molGraph →g Γ'.molGraph :=
    ⟨emb, fun {u v} h => by
      rw [owx_molGraph_adj] at h ⊢
      exact ⟨fun e => h.1 (hinj e), ha u v h.2⟩⟩
  have hstep : ∀ u v, Γ'.molGraph.Adj u v → Γ.molOf (ρ u) = Γ.molOf (ρ v) := by
    intro u v h
    rw [owx_molGraph_adj] at h
    rcases hb u v h.2 with h1 | h1
    · rw [h1]
    · by_cases h2 : ρ u = ρ v
      · rw [h2]
      · exact SimpleGraph.ConnectedComponent.eq.2
          (SimpleGraph.Adj.reachable ((owx_molGraph_adj Γ _ _).2 ⟨h2, h1⟩))
  have hwalk : ∀ {v w : E ⊕ I'} (p : Γ'.molGraph.Walk v w), Γ.molOf (ρ v) = Γ.molOf (ρ w) := by
    intro v w p
    induction p with
    | nil => rfl
    | cons h p ih => exact (hstep _ _ h).trans ih
  let φ : Γ.Mol → Γ'.Mol := SimpleGraph.ConnectedComponent.map f
  let ψ : Γ'.Mol → Γ.Mol :=
    SimpleGraph.ConnectedComponent.lift (fun v => Γ.molOf (ρ v)) (fun _ _ p _ => hwalk p)
  have hψφ : ∀ c, ψ (φ c) = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    change Γ.molOf (ρ (emb v)) = Γ.molOf v
    rw [hρ]
  have hφψ : ∀ c, φ (ψ c) = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h v => ?_
    exact SimpleGraph.ConnectedComponent.eq.2 (hc v).symm
  have hext : ∀ c, Γ.IsExtMol c ↔ Γ'.IsExtMol (φ c) := by
    intro c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, by
        change _ = Γ'.molOf (emb (Sum.inl a))
        rw [hemb]⟩
    · rintro ⟨a, ha'⟩
      refine ⟨a, ?_⟩
      have := hψφ c
      rw [← ha'] at this
      rw [← this]
      change Γ.molOf (Sum.inl a) = Γ.molOf (ρ (Sum.inl a))
      rw [hρe]
  refine Nat.card_congr
    { toFun := fun c => ⟨ψ c.1, fun h => c.2 (by
        have := (hext (ψ c.1)).1 h
        rwa [hφψ] at this)⟩
      invFun := fun c => ⟨φ c.1, fun h => c.2 ((hext c.1).2 h)⟩
      left_inv := fun c => Subtype.ext (hφψ c.1)
      right_inv := fun c => Subtype.ext (hψφ c.1) }

end PendantNM


section OwxNM

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The retraction of the vertices of a graph with `k` pendant vertices: the new vertices go to `x`. -/
def owxRho (k : ℕ) (x : I) : E ⊕ (I ⊕ Fin k) → E ⊕ I :=
  Sum.elim Sum.inl (Sum.elim Sum.inr (fun _ => Sum.inr x))

theorem owxRho_emb (k : ℕ) (x : I) (v : E ⊕ I) : owxRho k x (owxEmb k v) = v := by
  rcases v with a | b <;> rfl

/-- `n_M` of `Γ.owxExt` is that of `Γ` when the appended waved edges only join vertices that the retraction
`owxRho k x` identifies, and every new vertex is joined to `x`. -/
theorem owxExt_nM (Γ : LGraph E I) (k : ℕ) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin k))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin k)))) (hw : ∀ e ∈ w, owxRho k x e.x = owxRho k x e.y)
    (hc : ∀ v, (Γ.owxExt (owxEmb k) c s w).molGraph.Reachable v (owxEmb k (owxRho k x v))) :
    (Γ.owxExt (owxEmb k) c s w).nM = Γ.nM := by
  refine owx_nM_eq Γ (Γ.owxExt (owxEmb k) c s w) (owxEmb k) (owxRho k x) (owxRho_emb k x)
    (fun e => rfl) (fun e => rfl) ?_ ?_ hc
  · intro u v h
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h ⊢
    rcases h with ⟨e, he, h⟩ | ⟨e, he, h1, h⟩
    · left
      refine ⟨WEdge.map (owxEmb k) e, ?_, ?_⟩
      · exact List.mem_append_left _ (List.mem_map_of_mem he)
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; simp [WEdge.map, h1, h2]
        · right; simp [WEdge.map, h1, h2]
    · right
      refine ⟨DEdge.map (owxEmb k) e, ?_, ?_, ?_⟩
      · exact List.mem_map_of_mem he
      · simpa [DEdge.map] using h1
      · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; simp [DEdge.map, h1, h2]
        · right; simp [DEdge.map, h1, h2]
  · intro u v h
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq,
      Bool.and_eq_true] at h
    rcases h with ⟨e', he', h⟩ | ⟨e', he', h1, h⟩
    · simp only [LGraph.owxExt, List.mem_append, List.mem_map] at he'
      rcases he' with ⟨e, he, rfl⟩ | he'
      · right
        simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
        left
        refine ⟨e, he, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          subst h1 h2
          simp [WEdge.map, owxRho_emb]
        · right
          subst h1 h2
          simp [WEdge.map, owxRho_emb]
      · left
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · subst h1 h2; exact hw e' he'
        · subst h1 h2; exact (hw e' he').symm
    · simp only [LGraph.owxExt, List.mem_map] at he'
      obtain ⟨e, he, rfl⟩ := he'
      right
      simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq, Bool.and_eq_true]
      right
      refine ⟨e, he, by simpa [DEdge.map] using h1, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        subst h1 h2
        simp [DEdge.map, owxRho_emb]
      · right
        subst h1 h2
        simp [DEdge.map, owxRho_emb]

end OwxNM


section OwxTerms

variable {E I : Type*}

/-- **Term 1 of `(Owx)`**: `m Σ_α S_{xα} Ǧ_{xx} Ǧ_{αα} f` -- `Γ` (the weight kept) with a leaf `α` joined to
`x` by the waved edge `S_{xα}` and the light-weight `Ǧ_{αα}`; `coeff = m · coeff Γ`. -/
def owxT1 (m : ℂ) (Γ : LGraph E I) (x : I) : LGraph E (I ⊕ Fin 1) :=
  Γ.owxExt (owxEmb 1) m [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- **Term 2 of `(Owx)`**: `m³ Σ_{α,β} S⁺_{xα} S_{αβ} Ǧ_{αα} Ǧ_{ββ} f` -- the weight (`p.1`) is dropped (`p.2` are
the other solid edges of `Γ`), the path `x - α - β` with the blue `S⁺_{xα}` and the black `S_{αβ}`; `coeff = m³ ·
coeff Γ`. -/
def owxT2 (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (x : I) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := p.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [⟨true, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 0)⟩,
      ⟨true, true, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 1)⟩]
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

/-- **Term 3 of `(Owx)` for the solid edge `q.1` of `f`** (`q ∈ lwSplit p.2`, `q.2` the others):
`-m Σ_α S_{xα} G_{αx} ∂_{h_{αx}}` applied to the factor `q.1`: the weight and `q.1` are dropped, a leaf `α` is
joined to `x` by `S_{xα}`, the factor `G_{αx}` is added and `q.1` is replaced by the two edges of its
derivative with `(α, w) = (α, x)` (`owxDE`); `coeff = m · coeff Γ` (the sign of the derivative is in `owxDE`). -/
def owxT3 (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 1) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 1) m
    [(owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 0), Sum.inr (Sum.inl x)⟩]
    [⟨false, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩]

/-- **Term 4 of `(Owx)` for the solid edge `q.1` of `f`**: `-m³ Σ_{α,β} S⁺_{xα} S_{αβ} G_{βα} ∂_{h_{βα}}` applied
to the factor `q.1`: the path `x - α - β`, the factor `G_{βα}`, and `q.1` replaced by the two edges of its
derivative with `(α, w) = (β, α)`; `coeff = m³ · coeff Γ`. -/
def owxT4 (m : ℂ) (Γ : LGraph E I) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) :
    LGraph E (I ⊕ Fin 2) :=
  ({ Γ with solid := q.2 } : LGraph E I).owxExt (owxEmb 2) (m ^ 3)
    [(owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1,
      (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2,
      ⟨true, false, Sum.inr (Sum.inr 1), Sum.inr (Sum.inr 0)⟩]
    [⟨true, true, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩,
      ⟨false, true, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩]

end OwxTerms

section OwxCounters

variable {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- With one new vertex `α` joined to `x` by an appended waved edge, every vertex is joined to its
retraction. -/
theorem owxExt_reach1 (Γ : LGraph E I) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 1))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 1)))) (col σ : Bool)
    (hw : (⟨col, σ, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 1) c s w).molGraph.Reachable v (owxEmb 1 (owxRho 1 x v)) := by
  intro v
  rcases v with a | b | j
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.refl _
  · have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp [owxEmb, owxRho], ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw, Or.inr ⟨rfl, rfl⟩⟩

/-- With two new vertices (a path `x - α - β`), every vertex is joined to its retraction. -/
theorem owxExt_reach2 (Γ : LGraph E I) (x : I) (c : ℂ) (s : List (SEdge (E ⊕ (I ⊕ Fin 2))))
    (w : List (WEdge (E ⊕ (I ⊕ Fin 2)))) (col σ col' σ' : Bool)
    (hw : (⟨col, σ, Sum.inr (Sum.inl x), Sum.inr (Sum.inr 0)⟩ : WEdge _) ∈ w)
    (hw' : (⟨col', σ', Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1)⟩ : WEdge _) ∈ w) :
    ∀ v, (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable v (owxEmb 2 (owxRho 2 x v)) := by
  have h1 : (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) := by
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw, Or.inr ⟨rfl, rfl⟩⟩
  have h2 : (Γ.owxExt (owxEmb 2) c s w).molGraph.Reachable (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) := by
    refine SimpleGraph.Adj.reachable ((owx_molGraph_adj _ _ _).2 ⟨by simp, ?_⟩)
    simp only [LGraph.adj, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
    exact Or.inl ⟨_, List.mem_append_right _ hw', Or.inr ⟨rfl, rfl⟩⟩
  intro v
  rcases v with a | b | j
  · exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Reachable.refl _
  · fin_cases j
    · exact h1
    · exact h2.trans h1

theorem owxT1_counters (m : ℂ) (Γ : LGraph E I) (x : I) :
    (owxT1 m Γ x).nS = Γ.nS + 1 ∧ (owxT1 m Γ x).nW = Γ.nW + 1 ∧ (owxT1 m Γ x).nV = Γ.nV + 1 ∧
      (owxT1 m Γ x).nM = Γ.nM := by
  refine ⟨by simp [owxT1, LGraph.owxExt, LGraph.nS], by simp [owxT1, LGraph.owxExt, LGraph.nW],
    by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  refine owxExt_nM Γ 1 x m _ _ ?_ (owxExt_reach1 Γ x m _ _ false true (by simp))
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  rfl

theorem owxT2_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) :
    (owxT2 m Γ p x).nS = Γ.nS + 1 ∧ (owxT2 m Γ p x).nW = Γ.nW + 2 ∧ (owxT2 m Γ p x).nV = Γ.nV + 2 ∧
      (owxT2 m Γ p x).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  refine ⟨?_, by simp [owxT2, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxT2, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxT2 m Γ p x).nM = ({ Γ with solid := p.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 2 x (m ^ 3) _ _ ?_
        (owxExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem owxT3_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    (owxT3 m Γ x q).nS = Γ.nS + 1 ∧ (owxT3 m Γ x q).nW = Γ.nW + 1 ∧ (owxT3 m Γ x q).nV = Γ.nV + 1 ∧
      (owxT3 m Γ x q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [owxT3, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxT3, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxT3 m Γ x q).nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 1 x m _ _ ?_ (owxExt_reach1 _ x m _ _ false true (by simp))
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl

theorem owxT4_counters (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) :
    (owxT4 m Γ x q).nS = Γ.nS + 1 ∧ (owxT4 m Γ x q).nW = Γ.nW + 2 ∧ (owxT4 m Γ x q).nV = Γ.nV + 2 ∧
      (owxT4 m Γ x q).nM = Γ.nM := by
  have hl := lwSplit_snd_length Γ.solid p hp
  have hl' := lwSplit_snd_length p.2 q hq
  refine ⟨?_, by simp [owxT4, LGraph.owxExt, LGraph.nW], by simp [LGraph.nV, Fintype.card_sum], ?_⟩
  · simp only [owxT4, LGraph.owxExt, LGraph.nS, List.length_append, List.length_map, List.length_cons,
      List.length_nil]
    omega
  · have h : (owxT4 m Γ x q).nM = ({ Γ with solid := q.2 } : LGraph E I).nM := by
      refine owxExt_nM _ 2 x (m ^ 3) _ _ ?_
        (owxExt_reach2 _ x (m ^ 3) _ _ true true false true (by simp) (by simp))
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl
    rw [h]
    exact lwStein_nM_congr _ _ rfl rfl


theorem owxT1_ord (m : ℂ) (Γ : LGraph E I) (x : I) :
    ord (owxT1 m Γ x).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxT1_counters m Γ x
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxT2_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) : ord (owxT2 m Γ p x).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxT2_counters m Γ p hp x
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxT3_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) : ord (owxT3 m Γ x q).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxT3_counters m Γ p hp x q hq
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

theorem owxT4_ord (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hp : p ∈ lwSplit Γ.solid) (x : I) (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (hq : q ∈ lwSplit p.2) : ord (owxT4 m Γ x q).counters = ord Γ.counters + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := owxT4_counters m Γ p hp x q hq
  simp only [LGraph.counters, ord, h1, h2, h3, h4]
  push_cast
  ring

end OwxCounters


section OwxTermVal

variable {E I : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [DecidableEq I]

/-- The value of a term of `owxT1` at a labelling `ℓ'` extending `ℓ` (`ℓ' ∘ owxEmb 1 = ℓ`). -/
theorem owxT1_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I) (ℓ : E ⊕ I → ι)
    (ℓ' : E ⊕ (I ⊕ Fin 1) → ι) (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (owxT1 m Γ x).term D ℓ' = m * Γ.term D ℓ *
      (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0))) -
        D.M (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0)))) *
      D.S (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  rw [owxT1, LGraph.term_owxExt, hℓ]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxT2` (the weight dropped: `Γ'` has the solid edges `p.2`). -/
theorem owxT2_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I)))
    (x : I) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι) (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (owxT2 m Γ p x).term D ℓ' = m ^ 3 * ({ Γ with solid := p.2 } : LGraph E I).term D ℓ *
      ((D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0))) -
          D.M (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 0)))) *
        (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1))) -
          D.M (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 1))))) *
      (D.Sp (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) *
        D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1)))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  rw [owxT2, LGraph.term_owxExt, hℓ]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxT3`. -/
theorem owxT3_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 1) → ι)
    (hℓ : ℓ' ∘ owxEmb 1 = ℓ) :
    (owxT3 m Γ x q).term D ℓ' = m * ({ Γ with solid := q.2 } : LGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ (Sum.inr x))) *
      D.S (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 1 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inl x)) (SEdge.map (owxEmb 1) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0))) * D.G (ℓ (Sum.inr x)) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ (Sum.inr x))) * star (D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq, hx]
  rw [owxT3, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D ℓ' _)), h]
  simp [SEdge.val, WEdge.val, hx]

/-- The value of a term of `owxT4`. -/
theorem owxT4_term (D : LData ι) (m : ℂ) (Γ : LGraph E I) (x : I)
    (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (ℓ : E ⊕ I → ι) (ℓ' : E ⊕ (I ⊕ Fin 2) → ι)
    (hℓ : ℓ' ∘ owxEmb 2 = ℓ) :
    (owxT4 m Γ x q).term D ℓ' = m ^ 3 * ({ Γ with solid := q.2 } : LGraph E I).term D ℓ *
      ((if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
        else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst))) *
        D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ' (Sum.inr (Sum.inr 0)))) *
      (D.Sp (ℓ (Sum.inr x)) (ℓ' (Sum.inr (Sum.inr 0))) *
        D.S (ℓ' (Sum.inr (Sum.inr 0))) (ℓ' (Sum.inr (Sum.inr 1)))) := by
  have hx : ℓ' (Sum.inr (Sum.inl x)) = ℓ (Sum.inr x) := by
    rw [← hℓ]; rfl
  have hq : ∀ v, ℓ' (owxEmb 2 v) = ℓ v := fun v => by rw [← hℓ]; rfl
  have h : SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).1 *
      SEdge.val D ℓ' (owxDE (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 0)) (SEdge.map (owxEmb 2) q.1)).2 =
      if q.1.σ then D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 1))) * D.G (ℓ' (Sum.inr (Sum.inr 0))) (ℓ q.1.dst)
      else star (D.G (ℓ q.1.src) (ℓ' (Sum.inr (Sum.inr 0)))) * star (D.G (ℓ' (Sum.inr (Sum.inr 1))) (ℓ q.1.dst)) := by
    rw [owxDE_val]
    simp only [SEdge.map, hq]
  rw [owxT4, LGraph.term_owxExt, hℓ]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc ((SEdge.val D ℓ' _)), h]
  simp [SEdge.val, WEdge.val, hx]

end OwxTermVal


section OwxHelpers

/-- `lwSplit l` splits `l` into an element and the rest: `l ~ p.1 :: p.2`. -/
theorem lwSplit_perm {κ : Type*} (l : List κ) : ∀ p ∈ lwSplit l, l.Perm (p.1 :: p.2) := by
  induction l with
  | nil => intro p hp; simp [lwSplit] at hp
  | cons a l ih =>
    intro p hp
    simp only [lwSplit, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · exact List.Perm.refl _
    · exact ((ih q hq).cons a).trans (List.Perm.swap q.1 a q.2)

/-- The product over a list is that of the element split off times the product of the rest. -/
theorem lwSplit_prod {κ : Type*} {M : Type*} [CommMonoid M] (l : List κ) (f : κ → M)
    (p : κ × List κ) (hp : p ∈ lwSplit l) :
    (l.map f).prod = f p.1 * (p.2.map f).prod := by
  have := ((lwSplit_perm l p hp).map f).prod_eq
  simpa using this

/-- A list sum of integrable functions is integrable. -/
theorem owx_integrable_list_sum {Ω κ : Type*} [MeasurableSpace Ω] {P : Measure Ω} (L : List κ)
    (f : κ → Ω → ℂ) (hf : ∀ a ∈ L, Integrable (f a) P) :
    Integrable (fun ω => (L.map fun a => f a ω).sum) P := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (List.mem_cons_self ..)).add (ih fun b hb => hf b (List.mem_cons_of_mem _ hb))

/-- The integral of a list sum of integrable functions is the list sum of the integrals. -/
theorem owx_integral_list_sum {Ω κ : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L : List κ)
    (f : κ → Ω → ℂ) (hf : ∀ a ∈ L, Integrable (f a) P) :
    ∫ ω, (L.map fun a => f a ω).sum ∂P = (L.map fun a => ∫ ω, f a ω ∂P).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have h1 := hf a (List.mem_cons_self ..)
    have h2 := owx_integrable_list_sum (P := P) L f fun b hb => hf b (List.mem_cons_of_mem _ hb)
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add h1 h2, ih fun b hb => hf b (List.mem_cons_of_mem _ hb)]

/-- A list sum whose terms are `-c` times those of another list. -/
theorem owx_list_aux {κ : Type*} (L : List κ) (c : ℂ) (F G : κ → ℂ) (h : ∀ q ∈ L, G q = -c * F q) :
    (L.map G).sum = -(c * (L.map F).sum) := by
  have : L.map G = L.map fun q => -c * F q := List.map_congr_left h
  rw [this, List.sum_map_mul_left]
  ring

variable {I : Type*} {ι : Type*} [Fintype ι] [Fintype I] [DecidableEq I]

/-- A labelling of `I ⊕ Fin 1` is a labelling of `I` and a label `α`. -/
theorem owx_sum_fin1 (F : (I ⊕ Fin 1 → ι) → ℂ) :
    ∑ ℓ', F ℓ' = ∑ ℓi : I → ι, ∑ α : ι, F (Sum.elim ℓi fun _ => α) := by
  rw [← (Equiv.sumArrowEquivProdArrow I (Fin 1) ι).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
  rfl

/-- A labelling of `I ⊕ Fin 2` is a labelling of `I` and two labels `α, β`. -/
theorem owx_sum_fin2 (F : (I ⊕ Fin 2 → ι) → ℂ) :
    ∑ ℓ', F ℓ' = ∑ ℓi : I → ι, ∑ α : ι, ∑ β : ι, F (Sum.elim ℓi ![α, β]) := by
  rw [← (Equiv.sumArrowEquivProdArrow I (Fin 2) ι).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [← (finTwoArrowEquiv ι).symm.sum_comp, Fintype.sum_prod_type]
  rfl

end OwxHelpers


section OwxEdgePoly

variable {d : ℕ} (sz : Sizes d) (n : ℕ) {V : Type*}

/-- The resolvent polynomial of a solid edge at a labelling `ℓ` (`G_{ab} - M_{ab}` or its conjugate; the
constant `M_{ab}` is `0` without the circle). -/
def owxEdgePoly (M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (e : SEdge V) :
    MvPolynomial (Idx d (sz.L n) (sz.W n) × Idx d (sz.L n) (sz.W n) × Bool) ℂ :=
  if e.σ then MvPolynomial.X (ℓ e.src, ℓ e.dst, true) -
      MvPolynomial.C (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0)
  else MvPolynomial.X (ℓ e.src, ℓ e.dst, false) -
      MvPolynomial.C (star (if e.circ then M (ℓ e.src) (ℓ e.dst) else 0))

variable {sz n}

theorem lwPoly_owxEdgePoly (z : ℂ) (u : ℝ) (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (e : SEdge V) (ω : Sizes.SeqΩ sz) :
    lwPoly sz n z u (owxEdgePoly sz n M ℓ e) ω = SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ e := by
  cases hσ : e.σ
  · rw [lwStein_sedge_val_red e hσ ℓ ω]
    simp [owxEdgePoly, hσ, lwPoly, lwVar]
  · rw [lwStein_sedge_val_blue e hσ ℓ ω]
    simp [owxEdgePoly, hσ, lwPoly, lwVar]

theorem lwPoly_owxEdgePoly_prod (z : ℂ) (u : ℝ)
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (ℓ : V → Idx d (sz.L n) (sz.W n)) (l : List (SEdge V)) (ω : Sizes.SeqΩ sz) :
    lwPoly sz n z u ((l.map (owxEdgePoly sz n M ℓ)).prod) ω =
      (l.map (SEdge.val (lwSampleData sz n z u M S Sp ω) ℓ)).prod := by
  unfold lwPoly
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact lwPoly_owxEdgePoly z u M S Sp ℓ e ω

end OwxEdgePoly


section OwxIdentity

variable {d : ℕ} {sz : Sizes d} {n : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

/-- The labelling of `E ⊕ (I ⊕ Fin 1)` extending `(ℓe, ℓi)` by the label `α` of the new vertex. -/
def owxLab1 {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α : ι) : E ⊕ (I ⊕ Fin 1) → ι :=
  Sum.elim ℓe (Sum.elim ℓi fun _ => α)

/-- The labelling of `E ⊕ (I ⊕ Fin 2)` extending `(ℓe, ℓi)` by the labels `α, β` of the new vertices. -/
def owxLab2 {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α β : ι) : E ⊕ (I ⊕ Fin 2) → ι :=
  Sum.elim ℓe (Sum.elim ℓi ![α, β])

theorem owxLab1_emb {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α : ι) :
    owxLab1 ℓe ℓi α ∘ owxEmb 1 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

theorem owxLab2_emb {ι : Type*} (ℓe : E → ι) (ℓi : I → ι) (α β : ι) :
    owxLab2 ℓe ℓi α β ∘ owxEmb 2 = Sum.elim ℓe ℓi := by
  funext v
  rcases v with a | b <;> rfl

/-- **`(Owx)` for one labelling of the vertices of `Γ`** (expectations of terms): the weight `Ǧ_{xx}` of `Γ`
(`p.1`) at the internal vertex `x`; `E Γ.term(ℓ)` is the sum over the new labels `α`, `(α, β)` of the expectations
of the terms of `owxT1`, `owxT2` and, for each solid edge `q.1` of `f`, of `owxT3 q`, `owxT4 q`.  Hypotheses:
`GaussIBP` (proved: `gaussIBP sz`), `Im z > 0`, `u > 0`, `m ≠ 0`, `z + u m = -m⁻¹`, `S⁺ (1 - m² S) = S`, `M_{aa} = m`. -/
theorem owx_term_integral (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (hx : p.1 = ⟨true, true, Sum.inr x, Sum.inr x⟩)
    (ℓe : E → Idx d (sz.L n) (sz.W n)) (ℓi : I → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) =
      ∑ α, ∫ ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)
          ∂(Sizes.seqP sz) +
      ∑ α, ∑ β, ∫ ω, (owxT2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
          (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) +
      ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
  classical
  have hz' : z.im ≠ 0 := hz.ne'
  set ℓ : E ⊕ I → Idx d (sz.L n) (sz.W n) := Sum.elim ℓe ℓi with hℓ
  set xl : Idx d (sz.L n) (sz.W n) := ℓi x with hxl
  set K : ℂ := lwK Γ M (lwS sz n u) Sp ℓ with hK
  set P := (p.2.map (owxEdgePoly sz n M ℓ)).prod with hPdef
  have hf : ∀ ω, lwPoly sz n z u P ω =
      (p.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod :=
    fun ω => lwPoly_owxEdgePoly_prod z u M (lwS sz n u) Sp ℓ p.2 ω
  have hP1 : Tame1 sz n (lwPoly sz n z u P) := lwPoly_tame1 hz u P
  have hw : ∀ ω, SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ p.1 =
      lwG sz n z u xl xl ω - m := by
    intro ω
    rw [hx]
    simp [SEdge.val, lwSampleData, lwG, hM, hℓ, hxl]
  have hΓ : ∀ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
      K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω) := by
    intro ω
    rw [lwStein_term_eq, lwSplit_prod Γ.solid _ p hp, hw ω, hf ω]
  have hℓx : ℓ (Sum.inr x) = xl := rfl
  have hK' : ∀ s : List (SEdge (E ⊕ I)),
      lwK ({ Γ with solid := s } : LGraph E I) M (lwS sz n u) Sp ℓ = K := fun s => rfl
  have hT1 : ∀ α ω, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω)) * (lwG sz n z u α α ω - m) *
        lwS sz n u xl α := by
    intro α ω
    rw [owxT1_term _ m Γ x ℓ _ (owxLab1_emb ℓe ℓi α), hΓ ω]
    simp [owxLab1, lwSampleData, lwG, hM, hℓx]
  have hT2 : ∀ α β ω, (owxT2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
      (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * lwPoly sz n z u P ω) * ((lwG sz n z u α α ω - m) * (lwG sz n z u β β ω - m)) *
        (Sp xl α * lwS sz n u α β) := by
    intro α β ω
    rw [owxT2_term _ m Γ p x ℓ _ (owxLab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := p.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * lwPoly sz n z u P ω := by
      rw [lwStein_term_eq, hf ω, hK']
    rw [this]
    simp [owxLab2, lwSampleData, lwG, hM, hℓx]
  have hT3 : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α ω,
      (owxT3 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) =
      m * (K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        ((if q.1.σ then lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u xl (ℓ q.1.dst) ω
          else star (lwG sz n z u (ℓ q.1.src) xl ω) * star (lwG sz n z u α (ℓ q.1.dst) ω)) *
          lwG sz n z u α xl ω) * lwS sz n u xl α := by
    intro q α ω
    rw [owxT3_term _ m Γ x q ℓ _ (owxLab1_emb ℓe ℓi α)]
    have : ({ Γ with solid := q.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
      rw [lwStein_term_eq, hK']
    rw [this]
    simp [owxLab1, lwSampleData, lwG, hℓx]
  have hT4 : ∀ (q : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) α β ω,
      (owxT4 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) =
      m ^ 3 * (K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod) *
        ((if q.1.σ then lwG sz n z u (ℓ q.1.src) β ω * lwG sz n z u α (ℓ q.1.dst) ω
          else star (lwG sz n z u (ℓ q.1.src) α ω) * star (lwG sz n z u β (ℓ q.1.dst) ω)) *
          lwG sz n z u β α ω) * (Sp xl α * lwS sz n u α β) := by
    intro q α β ω
    rw [owxT4_term _ m Γ x q ℓ _ (owxLab2_emb ℓe ℓi α β)]
    have : ({ Γ with solid := q.2 } : LGraph E I).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ =
        K * (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod := by
      rw [lwStein_term_eq, hK']
    rw [this]
    simp [owxLab2, lwSampleData, lwG, hℓx]
  have hdh : ∀ (α w : Idx d (sz.L n) (sz.W n)) ω, dhSample sz n u α w (lwPoly sz n z u P) ω =
      ((lwSplit p.2).map fun q =>
        (if q.1.σ then -(lwG sz n z u (ℓ q.1.src) α ω * lwG sz n z u w (ℓ q.1.dst) ω)
          else -(star (lwG sz n z u (ℓ q.1.src) w ω) * star (lwG sz n z u α (ℓ q.1.dst) ω))) *
        (q.2.map (SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ)).prod).sum := by
    intro α w ω
    have hfun : lwPoly sz n z u P = fun ω => (p.2.map fun a =>
        SEdge.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ a).prod := funext hf
    rw [hfun, lwStein_dh_listProd p.2 (fun e _ => lwStein_sedge_val_tame1 hz e ℓ)]
    congr 1
    refine List.map_congr_left fun q _ => ?_
    rw [lwStein_dh_sedge_val hz hu q.1 α w ℓ ω]
  have hS3 : ∀ α ω, ((lwSplit p.2).map fun q => (owxT3 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum =
      -(K * (m * (lwS sz n u xl α * lwG sz n z u α xl ω)) *
        dhSample sz n u α xl (lwPoly sz n z u P) ω) := by
    intro α ω
    rw [hdh α xl ω]
    refine owx_list_aux _ _ _ _ fun q _ => ?_
    rw [hT3 q α ω]
    by_cases hσ : q.1.σ <;> simp [hσ] <;> ring
  have hS4 : ∀ α β ω, ((lwSplit p.2).map fun q => (owxT4 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum =
      -(K * (m ^ 3 * (Sp xl α * lwS sz n u α β * lwG sz n z u β α ω)) *
        dhSample sz n u β α (lwPoly sz n z u P) ω) := by
    intro α β ω
    rw [hdh β α ω]
    refine owx_list_aux _ _ _ _ fun q _ => ?_
    rw [hT4 q α β ω]
    by_cases hσ : q.1.σ <;> simp [hσ] <;> ring
  have hpath : ∀ ω, K * (m * ∑ α, lwS sz n u xl α * (lwG sz n z u xl xl ω - m) * (lwG sz n z u α α ω - m) *
            lwPoly sz n z u P ω +
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
            (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω -
          m * ∑ α, lwS sz n u xl α * lwG sz n z u α xl ω * dhSample sz n u α xl (lwPoly sz n z u P) ω -
          m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β α ω *
            dhSample sz n u β α (lwPoly sz n z u P) ω) =
      ∑ α, (owxT1 m Γ x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) +
      ∑ α, ∑ β, (owxT2 m Γ p x).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) +
      ∑ α, ((lwSplit p.2).map fun q => (owxT3 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum +
      ∑ α, ∑ β, ((lwSplit p.2).map fun q => (owxT4 m Γ x q).term (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum := by
    intro ω
    simp only [hT1, hT2, hS3, hS4]
    have hA : ∑ x, m * (K * ((lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω)) *
        (lwG sz n z u x x ω - m) * lwS sz n u xl x =
        K * (m * ∑ α, lwS sz n u xl α * (lwG sz n z u xl xl ω - m) * (lwG sz n z u α α ω - m) *
          lwPoly sz n z u P ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hB : ∑ x, ∑ x_1, m ^ 3 * (K * lwPoly sz n z u P ω) *
        ((lwG sz n z u x x ω - m) * (lwG sz n z u x_1 x_1 ω - m)) * (Sp xl x * lwS sz n u x x_1) =
        K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * (lwG sz n z u α α ω - m) *
          (lwG sz n z u β β ω - m) * lwPoly sz n z u P ω) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun β _ => by ring
    have hC : ∑ x, -(K * (m * (lwS sz n u xl x * lwG sz n z u x xl ω)) *
        dhSample sz n u x xl (lwPoly sz n z u P) ω) =
        -(K * (m * ∑ α, lwS sz n u xl α * lwG sz n z u α xl ω *
          dhSample sz n u α xl (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have hD : ∑ x, ∑ x_1, -(K * (m ^ 3 * (Sp xl x * lwS sz n u x x_1 * lwG sz n z u x_1 x ω)) *
        dhSample sz n u x_1 x (lwPoly sz n z u P) ω) =
        -(K * (m ^ 3 * ∑ α, ∑ β, Sp xl α * lwS sz n u α β * lwG sz n z u β α ω *
          dhSample sz n u β α (lwPoly sz n z u P) ω)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun β _ => by ring
    rw [hA, hB, hC, hD]
    ring
  have key := owx_integral hG hz hu hm0 hzm Sp hSp P xl
  have hint : ∀ {E' I' : Type} (T : LGraph E' I') (ℓ' : E' ⊕ I' → Idx d (sz.L n) (sz.W n)),
      Integrable (fun ω => T.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ') (Sizes.seqP sz) :=
    fun T ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have e1 : ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ ∂(Sizes.seqP sz) =
      K * ∫ ω, (lwG sz n z u xl xl ω - m) * lwPoly sz n z u P ω ∂(Sizes.seqP sz) := by
    simp_rw [hΓ]
    rw [integral_const_mul]
  rw [e1, key, ← integral_const_mul]
  simp_rw [hpath]
  set S1 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, (owxT1 m Γ x).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) with hS1
  set S2 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, (owxT2 m Γ p x).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) with hS2
  set S3 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ((lwSplit p.2).map fun q => (owxT3 m Γ x q).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α)).sum with hS3'
  set S4 : Sizes.SeqΩ sz → ℂ := fun ω => ∑ α, ∑ β, ((lwSplit p.2).map fun q => (owxT4 m Γ x q).term
    (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β)).sum with hS4'
  have hi1 : Integrable S1 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => hint _ _
  have hi2 : Integrable S2 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _
  have hi3 : Integrable S3 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi4 : Integrable S4 (Sizes.seqP sz) :=
    integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _
  have hi12 : Integrable (fun ω => S1 ω + S2 ω) (Sizes.seqP sz) := hi1.add hi2
  have hi123 : Integrable (fun ω => S1 ω + S2 ω + S3 ω) (Sizes.seqP sz) := hi12.add hi3
  change ∫ ω, (S1 ω + S2 ω + S3 ω + S4 ω) ∂(Sizes.seqP sz) = _
  rw [integral_add hi123 hi4, integral_add hi12 hi3, integral_add hi1 hi2]
  have e1' : ∫ ω, S1 ω ∂(Sizes.seqP sz) = ∑ α, ∫ ω, (owxT1 m Γ x).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
    integral_finsetSum _ fun α _ => hint _ _
  have e2' : ∫ ω, S2 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ∫ ω, (owxT2 m Γ p x).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
    rw [hS2, integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact integral_finsetSum _ fun β _ => hint _ _
  have e3' : ∫ ω, S3 ω ∂(Sizes.seqP sz) = ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    rw [hS3', integral_finsetSum _ fun α _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  have e4' : ∫ ω, S4 ω ∂(Sizes.seqP sz) = ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).term
      (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    rw [hS4', integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
      owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [integral_finsetSum _ fun β _ => owx_integrable_list_sum _ _ fun q _ => hint _ _]
    refine Finset.sum_congr rfl fun β _ => ?_
    exact owx_integral_list_sum _ _ _ fun q _ => hint _ _
  rw [e1', e2', e3', e4']


/-- The expectation of the value of a graph with one new internal vertex is the sum, over the labels of the
old internal vertices and of the new one, of the expectations of its terms. -/
theorem owx_integral_val1 (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ}
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T : LGraph E (I ⊕ Fin 1))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, T.term (lwSampleData sz n z u M S Sp ω)
        (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M S Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have h1 : ∀ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, T.term (lwSampleData sz n z u M S Sp ω) (owxLab1 ℓe ℓi α) :=
    fun ω => owx_sum_fin1 (fun ℓ' => T.term (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ℓ'))
  simp_rw [h1]
  rw [integral_finsetSum _ fun ℓi _ => integrable_finsetSum _ fun α _ => hint _]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  exact integral_finsetSum _ fun α _ => hint _

/-- The same for two new internal vertices. -/
theorem owx_integral_val2 (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ}
    (M S Sp : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ) (T : LGraph E (I ⊕ Fin 2))
    (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, T.term (lwSampleData sz n z u M S Sp ω)
        (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) := by
  have hint : ∀ ℓ', Integrable (fun ω => T.term (lwSampleData sz n z u M S Sp ω) ℓ') (Sizes.seqP sz) :=
    fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz T ℓ').tame
  have h1 : ∀ ω, T.val (lwSampleData sz n z u M S Sp ω) ℓe =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β,
        T.term (lwSampleData sz n z u M S Sp ω) (owxLab2 ℓe ℓi α β) :=
    fun ω => owx_sum_fin2 (fun ℓ' => T.term (lwSampleData sz n z u M S Sp ω) (Sum.elim ℓe ℓ'))
  simp_rw [h1]
  rw [integral_finsetSum _ fun ℓi _ => integrable_finsetSum _ fun α _ =>
    integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun ℓi _ => ?_
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => hint _]
  refine Finset.sum_congr rfl fun α _ => ?_
  exact integral_finsetSum _ fun β _ => hint _

/-- **`(Owx)` as a graph operation: the identity of expectations of values** (`7_8:294-306`, `ssl`; T2060d,
design row LW-05).  For a graph `Γ` with the weight `Ǧ_{xx}` at the internal vertex `x` (`p.1`, `p ∈ lwSplit
Γ.solid`, `p.2` the other solid edges, i.e. `Γ.val = E[Ǧ_{xx} f]` with the monomial `f`):
`E Γ.val = E (owxT1 m Γ x).val + E (owxT2 m Γ p x).val + Σ_q E (owxT3 m Γ x q).val + Σ_q E (owxT4 m Γ x q).val`,
`q` running over `lwSplit p.2` (one graph for each solid edge of `f`).  The counters of the four families:
`owxT1_counters` ... `owxT4_ord` (each `ord Γ + 1`).  Data: the resolvent `G = (H_u - z)⁻¹` of the flow of size `n`,
deterministic `M` (`M_{aa} = m`), `S = lwS sz n u`, `S⁺ = Sp` with `S⁺ (1 - m² S) = S`. -/
theorem owx_graph_E (hG : GaussIBP sz) {z : ℂ} (hz : 0 < z.im) {u : ℝ} (hu : 0 < u) {m : ℂ}
    (hm0 : m ≠ 0) (hzm : z + (u : ℂ) * m = -m⁻¹)
    (Sp M : Matrix (Idx d (sz.L n) (sz.W n)) (Idx d (sz.L n) (sz.W n)) ℂ)
    (hSp : ∀ i j, Sp i j - m ^ 2 * ∑ w, Sp i w * lwS sz n u w j = lwS sz n u i j)
    (hM : ∀ a, M a a = m)
    (Γ : LGraph E I) (p : SEdge (E ⊕ I) × List (SEdge (E ⊕ I))) (hp : p ∈ lwSplit Γ.solid) (x : I)
    (hx : p.1 = ⟨true, true, Sum.inr x, Sum.inr x⟩) (ℓe : E → Idx d (sz.L n) (sz.W n)) :
    ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∫ ω, (owxT1 m Γ x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ∫ ω, (owxT2 m Γ p x).val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) +
      ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum +
      ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum := by
  classical
  have hint : ∀ ℓ', Integrable (fun ω => Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓ')
      (Sizes.seqP sz) := fun ℓ' => Tame.integrable hG (lwStein_term_tame1 hz Γ ℓ').tame
  have hL : ∫ ω, Γ.val (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz) =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∫ ω, Γ.term (lwSampleData sz n z u M (lwS sz n u) Sp ω)
        (Sum.elim ℓe ℓi) ∂(Sizes.seqP sz) := by
    unfold LGraph.val
    exact integral_finsetSum _ fun ℓi _ => hint _
  rw [hL, owx_integral_val1 hG hz M _ Sp, owx_integral_val2 hG hz M _ Sp]
  simp_rw [owx_term_integral hG hz hu hm0 hzm Sp M hSp hM Γ p hp x hx ℓe]
  simp only [Finset.sum_add_distrib]
  have h3 : ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (owxT3 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∫ ω, (owxT3 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab1 ℓe ℓi α) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => owx_integral_val1 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  have h4 : ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)).sum =
      ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).term
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz)).sum := by
    have e : ((lwSplit p.2).map fun q => ∫ ω, (owxT4 m Γ x q).val
        (lwSampleData sz n z u M (lwS sz n u) Sp ω) ℓe ∂(Sizes.seqP sz)) =
        (lwSplit p.2).map fun q => ∑ ℓi : I → Idx d (sz.L n) (sz.W n), ∑ α, ∑ β, ∫ ω, (owxT4 m Γ x q).term
          (lwSampleData sz n z u M (lwS sz n u) Sp ω) (owxLab2 ℓe ℓi α β) ∂(Sizes.seqP sz) :=
      List.map_congr_left fun q _ => owx_integral_val2 hG hz M _ Sp _ ℓe
    rw [e, ← lwStein_sum_list]
    refine Finset.sum_congr rfl fun ℓi _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← lwStein_sum_list (β := Idx d (sz.L n) (sz.W n))]
  rw [h3, h4]

end OwxIdentity


/-! ## 4. Compiled instances at `d = 3`, `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`

(`N = (W L)^d = 27`; `m(0) = i`, `z_{1/2} = i/2`; `H_{1/2} = X / √2` on `27 × 27`.)  The constant size
sequence `lwWxSizes 3 3 1 (1/2)`; every deterministic hypothesis is discharged. -/

section Instances

open RBM.Gauss.SizesInst

/-- The size sequence of the instances. -/
def lwWxInstSz : Sizes 3 := lwWxSizes 3 3 1 (1 / 2) (le_refl 3)

theorem lwWx_inst_hE : |(0 : ℝ)| < 2 := by norm_num

theorem lwWx_inst_im : 0 < (zt 0 (1 / 2)).im := lwWx_im_pos 0 (1 / 2) lwWx_inst_hE (by norm_num)

theorem lwWx_inst_norm : ‖mE 0‖ ^ 2 * (1 / 2 : ℝ) < 1 := by
  rw [norm_mE (by norm_num)]; norm_num

/-- Bridge (b): the flow data at the instance -- `Im z > 0`, `m ≠ 0`, `z + t m = -m⁻¹`, `|m| = 1`, `|m|² t < 1`,
and `S⁺ - m² S⁺ S = S` for `S⁺ = LWPins_lwSp g E t`. -/
example : 0 < (zt 0 (1 / 2)).im ∧ mE 0 ≠ 0 ∧ zt 0 (1 / 2) + (((1 / 2 : ℝ)) : ℂ) * mE 0 = -(mE 0)⁻¹ ∧
    ‖mE 0‖ = 1 ∧ ‖mE 0‖ ^ 2 * (1 / 2 : ℝ) < 1 ∧
    (∀ i j : Idx 3 3 1, LWPins_lwSp 3 3 1 (1 / 2) 0 (1 / 2) i j - mE 0 ^ 2 *
        ∑ w, LWPins_lwSp 3 3 1 (1 / 2) 0 (1 / 2) i w * lwS lwWxInstSz 0 (1 / 2) w j =
      lwS lwWxInstSz 0 (1 / 2) i j) :=
  ⟨lwWx_inst_im, lwWx_mE_ne 0 lwWx_inst_hE, lwWx_flow 0 (1 / 2) lwWx_inst_hE, norm_mE (by norm_num),
    lwWx_inst_norm, lwWx_hSp (le_refl 3) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)⟩

/-- Bridge (a): `∫ G_{00} ∂PF = ∫ G_{00} ∂seqP` -- the resolvent entry of the one-size law and of the sequence space
at the instance. -/
example : ∫ ω, LWPins_lwG 3 3 1 0 (1 / 2) ω 0 0 ∂(PF 3 3 1 (1 / 2)) =
    ∫ ω', lwG lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) 0 0 ω' ∂(Sizes.seqP lwWxInstSz) :=
  lwWx_integral (le_refl 3)
    (lwStein_tame_lwG lwWxInstSz 0 lwWx_inst_im.ne' (1 / 2) 0 0).cont
    (fun ω' => lwWx_lwG (le_refl 3) 0 (1 / 2) ω' 0 0)

/-- Bridge (c): the variable map at `x ≠ y`: the red variable `(false, a, b)` of `LWPins_resPoly` is the variable
`(b, a, false)` of `lwVar` (a swap, not the plain reordering). -/
example (a b : Idx 3 3 1) :
    lwWxRename 3 3 1 (MvPolynomial.X (false, a, b)) = MvPolynomial.X (b, a, false) := by
  simp [lwWxRename, lwWxVar]

example : ((0 : Idx 3 3 1) ≠ Pi.single 0 1) := by
  intro h
  have := congrFun h 0
  simp at this

/-- Bridge (c) at the instance, on a polynomial with a red variable at `a ≠ b` times a blue one: the resolvent polynomial
of `lwWxRename` is the pin's `LWPins_lwf` at every sample. -/
example (ω : Sizes.SeqΩ lwWxInstSz) :
    lwPoly lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2) (lwWxRename 3 3 1
        (MvPolynomial.X (false, (0 : Idx 3 3 1), Pi.single 0 1) * MvPolynomial.X (true, 0, 0))) ω =
      LWPins_lwf 3 3 1 0 (1 / 2) (MvPolynomial.X (false, (0 : Idx 3 3 1), Pi.single 0 1) *
        MvPolynomial.X (true, 0, 0)) (Sizes.slice lwWxInstSz 0 ω) :=
  lwWx_lwPoly (le_refl 3) 0 (1 / 2) ω _

/-- Bridge (d) at the instance: `LWPins_lwdf = dhSample` for `P = G_{00} Ḡ_{ab}`, directions `(α, w)`. -/
example (ω : Sizes.SeqΩ lwWxInstSz) (α w : Idx 3 3 1) :
    LWPins_lwdf 3 3 1 0 (1 / 2) (MvPolynomial.X (true, (0 : Idx 3 3 1), 0) *
        MvPolynomial.X (false, (0 : Idx 3 3 1), Pi.single 0 1)) (Sizes.slice lwWxInstSz 0 ω) α w =
      dhSample lwWxInstSz 0 (1 / 2) α w (lwPoly lwWxInstSz 0 (zt 0 (1 / 2)) (1 / 2)
        (lwWxRename 3 3 1 (MvPolynomial.X (true, (0 : Idx 3 3 1), 0) *
          MvPolynomial.X (false, (0 : Idx 3 3 1), Pi.single 0 1)))) ω :=
  lwWx_lwdf (le_refl 3) 0 (1 / 2) lwWx_inst_im (by norm_num) α w ω _

/-- **Target 2 at the instance** (`P = X (true, x, x)`, `x = 0`): `(Owx)` on `PF 3 3 1 (1/2)`, the pin
`LWweightExp 3` at `L = 3`, `W = 1`, `g = 1/2`, `E = 0`, `t = 1/2`. -/
example := lwWeightExp_holds 3 3 1 (le_refl 3) (1 / 2) 0 (1 / 2) lwWx_inst_hE (by norm_num) (by norm_num)
  (MvPolynomial.X (true, (0 : Idx 3 3 1), 0)) 0

/-- **Target 2, the instance of `Graph/LWPins.lean`** (`inst_ssl`: `d = 3`, `L = 3`, `W = 2`, `N = 216`, `g = 1`,
`E = 0`, `t = 1/2`, `P = G_{01} Ḡ_{01}`, any vertex `x`): the merged instance of the pin now has its hypothesis
`LWweightExp 3` proved. -/
example (x : Idx 3 3 2) := LWInstFixed.inst_ssl (lwWeightExp_holds 3) x


/-- The matrix `S⁺ = S (1 - m² S)⁻¹` of the instances (`n = 0`, `u = 1/2`, `m = m(0) = i`). -/
def lwWxInstSp : Matrix (Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) (Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) ℂ :=
  lwSplus lwWxInstSz 0 (1 / 2) (mE 0)

/-- The deterministic centre `M = m I` of the instances. -/
def lwWxInstM : Matrix (Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) (Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) ℂ :=
  Matrix.of fun a b => if a = b then mE 0 else 0

theorem lwWx_inst_hSp (i j : Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) :
    lwWxInstSp i j - mE 0 ^ 2 * ∑ w, lwWxInstSp i w * lwS lwWxInstSz 0 (1 / 2) w j =
      lwS lwWxInstSz 0 (1 / 2) i j :=
  lwSplus_spec (sz := lwWxInstSz) (n := 0) (by norm_num) lwWx_inst_norm i j

theorem lwWx_inst_hM (a : Idx 3 (lwWxInstSz.L 0) (lwWxInstSz.W 0)) : lwWxInstM a a = mE 0 := by
  simp [lwWxInstM]

/-- **Target 3 on the merged `owxG2` data**: the graph `owxG2 m` has the weights `Ǧ_{αα} = Ǧ_{(inr 0)(inr 0)}` and
`Ǧ_{ββ}`; `x = inr 0`, `p = (Ǧ_{xx}, [Ǧ_{ββ}])`.  The identity of expectations of values at the instance
(`gaussIBP` proved, every other hypothesis deterministic). -/
example := owx_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwWx_inst_hM (owxG2 (mE 0))
  (⟨true, true, Sum.inr 0, Sum.inr 0⟩, [⟨true, true, Sum.inr 1, Sum.inr 1⟩])
  (by simp [lwSplit, owxG2]) 0 rfl (fun _ => 0)

/-- The graph `Ǧ_{xx} G_{ax}` with the external vertex `a = inl 0` and the internal vertex `x = inr 0`: the weight
`Ǧ_{xx}` and one more solid edge, so that the derivative terms of `(Owx)` exist. -/
def lwWxInstGraph (m : ℂ) : LGraph (Fin 1) (Fin 1) where
  solid := [⟨true, true, Sum.inr 0, Sum.inr 0⟩, ⟨true, false, Sum.inl 0, Sum.inr 0⟩]
  waved := []
  dotted := []
  coeff := m

/-- **Target 3 on `Ǧ_{xx} G_{ax}`**: `p = (Ǧ_{xx}, [G_{ax}])`; the derivative terms `owxT3 q`, `owxT4 q` have one graph
each (`q = (G_{ax}, [])`). -/
example := owx_graph_E (sz := lwWxInstSz) (n := 0) (gaussIBP lwWxInstSz) lwWx_inst_im
  (by norm_num : (0 : ℝ) < 1 / 2) (lwWx_mE_ne 0 lwWx_inst_hE) (lwWx_flow 0 (1 / 2) lwWx_inst_hE)
  lwWxInstSp lwWxInstM lwWx_inst_hSp lwWx_inst_hM (lwWxInstGraph (mE 0))
  (⟨true, true, Sum.inr 0, Sum.inr 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩])
  (by simp [lwSplit, lwWxInstGraph]) 0 rfl (fun _ => 0)

/-- The counters of the four terms of `Ǧ_{xx} G_{ax}`, computed: `Γ` has `(n_S, n_W, n_V, n_M) = (2, 0, 1, 1)`;
`owxT1`: `(3, 1, 2, 1)`, `owxT2`: `(3, 2, 3, 1)`, `owxT3`: `(3, 1, 2, 1)`, `owxT4`: `(3, 2, 3, 1)`. -/
example :
    let Γ := lwWxInstGraph 1
    let q : SEdge (Fin 1 ⊕ Fin 1) × List (SEdge (Fin 1 ⊕ Fin 1)) := (⟨true, false, Sum.inl 0, Sum.inr 0⟩, [])
    let p : SEdge (Fin 1 ⊕ Fin 1) × List (SEdge (Fin 1 ⊕ Fin 1)) :=
      (⟨true, true, Sum.inr 0, Sum.inr 0⟩, [⟨true, false, Sum.inl 0, Sum.inr 0⟩])
    (Γ.nS, Γ.nW, Γ.nV, Γ.nM) = (2, 0, 1, 1) ∧
    ((owxT1 1 Γ 0).nS, (owxT1 1 Γ 0).nW, (owxT1 1 Γ 0).nV, (owxT1 1 Γ 0).nM) = (3, 1, 2, 1) ∧
    ((owxT2 1 Γ p 0).nS, (owxT2 1 Γ p 0).nW, (owxT2 1 Γ p 0).nV, (owxT2 1 Γ p 0).nM) = (3, 2, 3, 1) ∧
    ((owxT3 1 Γ 0 q).nS, (owxT3 1 Γ 0 q).nW, (owxT3 1 Γ 0 q).nV, (owxT3 1 Γ 0 q).nM) = (3, 1, 2, 1) ∧
    ((owxT4 1 Γ 0 q).nS, (owxT4 1 Γ 0 q).nW, (owxT4 1 Γ 0 q).nV, (owxT4 1 Γ 0 q).nM) = (3, 2, 3, 1) := by
  decide

end Instances


end RBM.Graph
