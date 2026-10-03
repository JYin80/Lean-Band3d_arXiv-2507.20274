/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Green.LDEQuadMom

/-!
# The positive chaos moment bound `E[T^p] ≤ C_p E[Vq^p]`

Port of `RBM2D/Green/LDEQuadT.lean` (lines 1-1008, up to the private `Checks` section) of RBM2D at
commit `c9a24cf` (T2052, portmap P.7 row S1-14), to the `d`-dimensional sequence model of
`RBM3D/Gauss/FineModel.lean`, on top of `RBM3D/Green/LDEQuad.lean` (T2031) and
`RBM3D/Green/LDEQuadMom.lean` (T2044).  The paper (arXiv:2507.20274) does not state this file as a
lemma: it is abstract Gaussian calculus on independent centred coordinates, used inside the
delegated proof of the resolvent-entry large deviation estimate.  The file involves neither
`Z_L^d` nor the variance profile `S`: the statements are those of RBM2D after rule R1 of
`docs/tickets/ST1-COMMON.md` (`d : Sizes` becomes `sz : Sizes d`, and `Sizes.SeqΩ`, `Sizes.seqP`,
`Sizes.seqGvar`, `Tame`, `GaussIBP`, `RowChaos`, `Tame.const (d := d)` take `sz`; namespace
`RBM.Green.RowChaos`).  No exponent of `W`, `L`, `N` occurs, and the constants `4q + 2` and
`(2p − 1)(4p − 2)` are dimension-free.  Only the `Checks` section at the end is dimension-specific
(`d = 3`).

`RBM3D/Green/LDEQuadMom.lean` closes the Hanson–Wright recursion at
`RBM.Green.RowChaos.mom_succ_le`:

`E|Q|^{2p} ≤ (2p−1)^p E[T^p]`,  `T = ∑_k σ_k(‖U_k‖² + ‖V_k‖²)`.

What is left to reach the paper's control `Vq = ∑_{k,l} σ_k‖B_{kl}‖²σ_l` is the *positive
chaos* moment bound `E[T^p] ≤ C_p E[Vq^p]`.  This file proves it by the same Gaussian
integration by parts on `E[T^p]`, with the **Wirtinger derivation along the row entry**

`D_l = r(∂_{a_l} − ε_l i ∂_{b_l})`,   `a_l = co l tt`,  `b_l = co l ff`.

It satisfies

`D_l U_k = 0`,  `D_l \bar V_k = 0`,  `D_l \bar U_k = 2r² \bar B_{kl}`,  `D_l V_k = 2r² B_{lk}`,

which is why `T` — built from `U \bar U` and `V \bar V` — differentiates into something
controlled by `B` alone.  These four values are used only in the combined forms `wirtVal_term`
and `wirtVal_termW`; they are not separate declarations.

## Main results (all in `RBM.Green.RowChaos`)

* `integral_conj_h_mul_gen` : **the master identity** `∫ \bar h_l Z = w_l ∫ D_l Z` for tame `Z`
* `Tq_eq_sum_conj_h_mul`    : `T = ∑_l \bar h_l W_l`
* `integral_Tq_pow_succ`    : `E[T^{q+1}] = ∑_l w_l E[D_l Z_{q,l}]`
* `norm_crossT_le`          : the cross term is `≤ 4q V_q T^q`
* `momTpow_succ_le`         : `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]`
* `momTpow_le`              : **`E[T^{q+1}] ≤ (4q+2)^{q+1} E[V_q^{q+1}]`**
* `mom_le_momVpow`          : **Hanson–Wright in the paper's control**,
  `E|Q|^{2p} ≤ ((2p−1)(4p−2))^p E[V_q^p]`

The constants are explicit and not optimal.

## Hypotheses carried

`RBM.Green.GaussIBP sz` (T2031; proved for the model by S1-19) is a hypothesis `hG` of exactly the
declarations that integrate (`integral_conj_h_mul_gen`, `integral_Tq_pow_succ`,
`integrable_Vq_mul_Tq_pow`, `integrable_Vq_pow`, `momTpow_succ_le`, `momTpow_le`,
`mom_le_momVpow`).  Nothing else is assumed.

## Declarations dropped from the source

None: every public declaration of the source at lines 56-1008 is ported.  The source `Checks`
section (`chkT*`, private there) is re-instantiated at `SizesInst.sz0` (`d = 3`), see the end of
the file.
-/

namespace RBM.Green

open MeasureTheory ProbabilityTheory Finset RBM.Gauss
open scoped NNReal

namespace RowChaos

variable {d : ℕ} {sz : Sizes d} {κ : Type*} [Fintype κ] [DecidableEq κ] (C : RowChaos sz κ)

/-! ### The Wirtinger derivation along the row -/

/-- `D_l Z = r(∂_{a_l}Z − ε_l i ∂_{b_l}Z)`, as a function of the two partials `a`, `b`. -/
noncomputable def wirtVal (l : κ) (a b : ℂ) : ℂ :=
  (C.r : ℂ) * (a - ((C.eps l : ℂ) * Complex.I) * b)

variable {C}

theorem wirtVal_add (l : κ) (a b a' b' : ℂ) :
    C.wirtVal l (a + a') (b + b') = C.wirtVal l a b + C.wirtVal l a' b' := by
  simp only [wirtVal]; ring

theorem wirtVal_smul (l : κ) (z a b : ℂ) :
    C.wirtVal l (z * a) (z * b) = z * C.wirtVal l a b := by
  simp only [wirtVal]; ring

theorem wirtVal_sum {ι : Type*} (s : Finset ι) (l : κ) (A B : ι → ℂ) :
    C.wirtVal l (∑ j ∈ s, A j) (∑ j ∈ s, B j) = ∑ j ∈ s, C.wirtVal l (A j) (B j) := by
  classical
  induction s using Finset.induction with
  | empty => simp [wirtVal]
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.sum_insert hj,
        wirtVal_add, ih]

/-! #### The four derivation values -/

/-! ### The master identity `∫ \bar h_l Z = w_l ∫ D_l Z` -/

variable (C)

/-- **Gaussian integration by parts along one row entry.**  For every tame `Z` whose partials
along the two coordinates of the index `l` are `ZA`, `ZB`,

`∫ \bar h_l · Z = w_l ∫ D_l Z`,  `D_l Z = r(ZA − ε_l i ZB)`.

This is `RBM.Green.GaussIBP.stein` applied once to each of the two coordinates, combined with
`\bar h_l = r(ω_{a_l} − ε_l i ω_{b_l})`.  It is the analogue of
`RBM.Green.RowChaos.integral_chaos_mul` for a single row entry rather than the whole chaos. -/
theorem integral_conj_h_mul_gen (hG : GaussIBP sz) {Z ZA ZB : Sizes.SeqΩ sz → ℂ} (l : κ)
    (hZ : Tame sz Z) (hZA : Tame sz ZA) (hZB : Tame sz ZB)
    (hdA : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l true) s)) (ZA ω)
      (ω (C.co l true)))
    (hdB : ∀ ω, HasDerivAt (fun s : ℝ => Z (Function.update ω (C.co l false) s)) (ZB ω)
      (ω (C.co l false))) :
    ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(Sizes.seqP sz)
      = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(Sizes.seqP sz) := by
  have hA : ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(Sizes.seqP sz)
      = (C.w l : ℂ) * ∫ ω, ZA ω ∂(Sizes.seqP sz) :=
    hG.stein (C.co l true) Z ZA hZ hZA hdA
  have hB : ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(Sizes.seqP sz)
      = (C.w l : ℂ) * ∫ ω, ZB ω ∂(Sizes.seqP sz) := by
    have h := hG.stein (C.co l false) Z ZB hZ hZB hdB
    have hgv : ((Sizes.seqGvar sz (C.co l false) : ℝ) : ℂ) = ((C.w l : ℝ) : ℂ) := by
      rw [C.gvar_tag l]; rfl
    rw [h, hgv]
  have hi1 : Integrable (fun ω : Sizes.SeqΩ sz => (ω (C.co l true) : ℂ) * Z ω) (Sizes.seqP sz) :=
    ((Tame.coord (C.co l true)).mul hZ).integrable hG
  have hi2 : Integrable (fun ω : Sizes.SeqΩ sz => (ω (C.co l false) : ℂ) * Z ω) (Sizes.seqP sz) :=
    ((Tame.coord (C.co l false)).mul hZ).integrable hG
  have hiA : Integrable ZA (Sizes.seqP sz) := hZA.integrable hG
  have hiB : Integrable ZB (Sizes.seqP sz) := hZB.integrable hG
  calc ∫ ω, (starRingEnd ℂ) (C.h ω l) * Z ω ∂(Sizes.seqP sz)
      = ∫ ω, ((C.r : ℂ) * ((ω (C.co l true) : ℂ) * Z ω)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
            ((ω (C.co l false) : ℂ) * Z ω)) ∂(Sizes.seqP sz) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only [C.conj_h]; ring
    _ = (C.r : ℂ) * ∫ ω, (ω (C.co l true) : ℂ) * Z ω ∂(Sizes.seqP sz)
        - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) *
          ∫ ω, (ω (C.co l false) : ℂ) * Z ω ∂(Sizes.seqP sz) := by
        rw [integral_sub (hi1.const_mul _) (hi2.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = (C.w l : ℂ) * ((C.r : ℂ) * ∫ ω, ZA ω ∂(Sizes.seqP sz)
          - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ∫ ω, ZB ω ∂(Sizes.seqP sz)) := by
        rw [hA, hB]; ring
    _ = (C.w l : ℂ) * ∫ ω, C.wirtVal l (ZA ω) (ZB ω) ∂(Sizes.seqP sz) := by
        congr 1
        rw [show (fun ω => C.wirtVal l (ZA ω) (ZB ω))
            = fun ω => (C.r : ℂ) * ZA ω
              - ((C.r : ℂ) * ((C.eps l : ℂ) * Complex.I)) * ZB ω from by
          funext ω; simp only [wirtVal]; ring]
        rw [integral_sub (hiA.const_mul _) (hiB.const_mul _), integral_const_mul,
          integral_const_mul]

/-- Right-hand scalar: `D_l (a·z, b·z) = (D_l(a,b))·z`. -/
theorem wirtVal_mul_right (l : κ) (z a b : ℂ) :
    C.wirtVal l (a * z) (b * z) = C.wirtVal l a b * z := by
  simp only [wirtVal]; ring

/-! ### The partials of `T` along the row -/

/-- `∂T/∂a_l`, in complex form. -/
noncomputable def TA (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
      + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))

/-- `∂T/∂b_l`, in complex form. -/
noncomputable def TB (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
      + C.U ω k *
        (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k *
        (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))

theorem tameTA (l : κ) : Tame sz (C.TA l) :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (Tame.const (sz := sz) ((C.r : ℂ)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (Tame.const (sz := sz) ((C.r : ℂ)))).conj))).add
      (((Tame.const (sz := sz) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((Tame.const (sz := sz) ((C.r : ℂ))).mul (C.tameB l k)).conj)))

theorem tameTB (l : κ) : Tame sz (C.TB l) :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
    (((((C.tameB k l).mul (Tame.const (sz := sz)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).mul (C.tameU k).conj).add
      ((C.tameU k).mul (((C.tameB k l).mul (Tame.const (sz := sz)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj))).add
      (((Tame.const (sz := sz) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameV k).conj) |>.add
      ((C.tameV k).mul (((Tame.const (sz := sz)
        ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul (C.tameB l k)).conj)))

theorem hasDerivAt_Tq_true (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      (C.TA l ω) (ω (C.co l true)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l true) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l true) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
          + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hU := C.hasDerivAt_U_true l k ω
    have hV := C.hasDerivAt_V_true l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

theorem hasDerivAt_Tq_false (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      (C.TB l ω) (ω (C.co l false)) := by
  have hfun : (fun s : ℝ => ((C.Tq (Function.update ω (C.co l false) s) : ℝ) : ℂ))
      = fun s : ℝ => ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)) := by
    funext s; exact C.Tq_complex _
  rw [hfun]
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.U (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.V (Function.update ω (C.co l false) s) k)))
      (((C.sg k : ℝ) : ℂ) *
        ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
          + C.U ω k *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
          + C.V ω k *
            (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hU := C.hasDerivAt_U_false l k ω
    have hV := C.hasDerivAt_V_false l k ω
    have hUc := hasDerivAt_conj' hU
    have hVc := hasDerivAt_conj' hV
    have h1 := hU.fun_mul hUc
    have h2 := hV.fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    ring
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k
  exact hsum

variable {C}

/-- The `k`-th summand of `D_l T`: `D_l(U_k\bar U_k + V_k\bar V_k)
= 2r²(U_k\bar B_{kl} + B_{lk}\bar V_k)`. -/
theorem wirtVal_term (l k : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l
      ((C.B ω k l * (C.r : ℂ)) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k * (starRingEnd ℂ) ((C.r : ℂ) * C.B ω l k))
      ((C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I))) * (starRingEnd ℂ) (C.U ω k)
        + C.U ω k *
          (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.V ω k)
        + C.V ω k *
          (starRingEnd ℂ) (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 *
        (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination ((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.U ω k) - C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      - C.B ω l k * (starRingEnd ℂ) (C.V ω k)
      + C.V ω k * (starRingEnd ℂ) (C.B ω l k))) * hq

/-- **`D_l T = 2r² ∑_k σ_k (U_k \bar B_{kl} + B_{lk} \bar V_k)`.**  Both `U` and `\bar V` are
killed by `D_l`, so only `B` survives — this is the whole point of the derivation. -/
theorem wirtVal_TA_TB (l : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l (C.TA l ω) (C.TB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)) := by
  rw [TA, TB, wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_term]
  ring

/-! ### `T` as a linear form in the row: `T = ∑_l \bar h_l W_l` -/

variable (C)

/-- `W_l = ∑_k σ_k(B_{kl}\bar U_k + V_k \bar B_{lk})`, the coefficient of `\bar h_l` in `T`. -/
noncomputable def Wt (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.U ω k)
    + C.V ω k * (starRingEnd ℂ) (C.B ω l k))

theorem tameWt (l : κ) : Tame sz (C.Wt l) :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul (C.tameU k).conj).add ((C.tameV k).mul (C.tameB l k).conj))

variable {C}

/-- **`T` is a linear form in the conjugated row.**  Both `U_k\bar U_k` and `V_k\bar V_k`
contain exactly one factor `\bar h`, so `T = ∑_l \bar h_l W_l`.  This is what makes the
integration by parts of `E[T^{q+1}]` possible. -/
theorem Tq_eq_sum_conj_h_mul (ω : Sizes.SeqΩ sz) :
    ((C.Tq ω : ℝ) : ℂ) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by
  have hU : ∀ k : κ, C.U ω k = ∑ l, C.B ω k l * (starRingEnd ℂ) (C.h ω l) := fun _ => rfl
  have hV : ∀ k : κ, (starRingEnd ℂ) (C.V ω k)
      = ∑ l, (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k) := by
    intro k
    change (starRingEnd ℂ) (∑ m, C.h ω m * C.B ω m k) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => map_mul _ _ _
  have hexp : (∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω)
      = ∑ l, ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.U ω k)
          + C.V ω k * ((starRingEnd ℂ) (C.h ω l) * (starRingEnd ℂ) (C.B ω l k))) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Wt, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [C.Tq_complex ω, hexp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  nth_rewrite 1 [hU k]
  rw [hV k, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The `k`-th summand of `D_l W_l`. -/
theorem wirtVal_termW (l k : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))
      (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
        + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
          (starRingEnd ℂ) (C.B ω l k))
      = 2 * (C.r : ℂ) ^ 2 * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
        + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  have hq : ((C.eps l : ℂ) * Complex.I) ^ 2 = -1 := by
    rw [mul_pow, C.eps_sq_complex l, Complex.I_sq, one_mul]
  simp only [wirtVal, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  linear_combination (-((C.r : ℂ) ^ 2 *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)))) * hq

/-- **`D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`.** -/
theorem wirtVal_Wt (l : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l
      (∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) := by
  rw [wirtVal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [wirtVal_smul, wirtVal_termW]
  ring

/-! ### The partials of `W_l` -/

variable (C)

/-- `∂W_l/∂a_l`. -/
noncomputable def WA (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
    + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

/-- `∂W_l/∂b_l`. -/
noncomputable def WB (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ k, ((C.sg k : ℝ) : ℂ) *
    (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
      + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k))

theorem tameWA (l : κ) : Tame sz (C.WA l) :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (Tame.const (sz := sz) ((C.r : ℂ)))).conj).add
      (((Tame.const (sz := sz) ((C.r : ℂ))).mul (C.tameB l k)).mul (C.tameB l k).conj))

theorem tameWB (l : κ) : Tame sz (C.WB l) :=
  Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
    (((C.tameB k l).mul ((C.tameB k l).mul (Tame.const (sz := sz)
        (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))).conj).add
      (((Tame.const (sz := sz) ((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)).mul
        (C.tameB l k)).mul (C.tameB l k).conj))

theorem hasDerivAt_Wt_true (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l true) s)) (C.WA l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l true) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l true) s) k)
          + C.V (Function.update ω (C.co l true) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l true) s) l k)))
      (((C.sg k : ℝ) : ℂ) * (C.B ω k l * (starRingEnd ℂ) (C.B ω k l * (C.r : ℂ))
        + ((C.r : ℂ) * C.B ω l k) * (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l true)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l true k l ω
    have hB2 := C.hasDerivAt_B_const l true l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_true l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_true l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

theorem hasDerivAt_Wt_false (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.Wt l (Function.update ω (C.co l false) s)) (C.WB l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hterm : ∀ k : κ, HasDerivAt
      (fun s : ℝ => ((C.sg k : ℝ) : ℂ) *
        (C.B (Function.update ω (C.co l false) s) k l *
            (starRingEnd ℂ) (C.U (Function.update ω (C.co l false) s) k)
          + C.V (Function.update ω (C.co l false) s) k *
            (starRingEnd ℂ) (C.B (Function.update ω (C.co l false) s) l k)))
      (((C.sg k : ℝ) : ℂ) *
        (C.B ω k l *
            (starRingEnd ℂ) (C.B ω k l * (-((C.r : ℂ) * (C.eps l : ℂ) * Complex.I)))
          + (((C.r : ℂ) * (C.eps l : ℂ) * Complex.I) * C.B ω l k) *
            (starRingEnd ℂ) (C.B ω l k)))
      (ω (C.co l false)) := by
    intro k
    have hB1 := C.hasDerivAt_B_const l false k l ω
    have hB2 := C.hasDerivAt_B_const l false l k ω
    have hUc := hasDerivAt_conj' (C.hasDerivAt_U_false l k ω)
    have hVc := hasDerivAt_conj' hB2
    have h1 := hB1.fun_mul hUc
    have h2 := (C.hasDerivAt_V_false l k ω).fun_mul hVc
    have hadd := (h1.add h2).const_mul (((C.sg k : ℝ) : ℂ))
    simp only [hself] at hadd
    convert hadd using 1
    simp only [map_zero]
    ring
  exact HasDerivAt.fun_sum (u := (Finset.univ : Finset κ)) fun k _ => hterm k

variable {C}

/-- `D_l W_l = 2r² ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²)`, in terms of `WA`/`WB`. -/
theorem wirtVal_WA_WB (l : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l (C.WA l ω) (C.WB l ω)
      = 2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.B ω l k)) :=
  C.wirtVal_Wt l ω

/-! ### The integration by parts of `E[T^{q+1}]` -/

variable (C)

/-- `Z_{q,l} = W_l · T^q`, the coefficient of `\bar h_l` in `T^{q+1}`. -/
noncomputable def Zt (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  C.Wt l ω * ((C.Tq ω : ℝ) : ℂ) ^ q

/-- `∂Z_{q,l}/∂a_l`. -/
noncomputable def ZA (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  C.WA l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TA l ω)

/-- `∂Z_{q,l}/∂b_l`. -/
noncomputable def ZB (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) : ℂ :=
  C.WB l ω * ((C.Tq ω : ℝ) : ℂ) ^ q
    + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) * C.TB l ω)

theorem tameZt (q : ℕ) (l : κ) : Tame sz (C.Zt q l) :=
  (C.tameWt l).mul (C.tameTq.pow q)

theorem tameZA (q : ℕ) (l : κ) : Tame sz (C.ZA q l) :=
  ((C.tameWA l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((Tame.const (sz := sz) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTA l)))

theorem tameZB (q : ℕ) (l : κ) : Tame sz (C.ZB q l) :=
  ((C.tameWB l).mul (C.tameTq.pow q)).add
    ((C.tameWt l).mul
      (((Tame.const (sz := sz) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul (C.tameTB l)))

variable {C}

theorem Tq_pow_succ_eq_sum (q : ℕ) (ω : Sizes.SeqΩ sz) :
    ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
  have h := Tq_eq_sum_conj_h_mul (C := C) ω
  calc ((C.Tq ω : ℝ) : ℂ) ^ (q + 1)
      = ((C.Tq ω : ℝ) : ℂ) ^ q * ((C.Tq ω : ℝ) : ℂ) := pow_succ _ _
    _ = ((C.Tq ω : ℝ) : ℂ) ^ q * ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Wt l ω := by rw [← h]
    _ = ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [Zt]; ring

variable (C)

theorem hasDerivAt_Zt_true (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l true) s)) (C.ZA q l ω)
      (ω (C.co l true)) := by
  have hself := Function.update_eq_self (C.co l true) ω
  have hW := C.hasDerivAt_Wt_true l ω
  have hT := (C.hasDerivAt_Tq_true l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

theorem hasDerivAt_Zt_false (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) :
    HasDerivAt (fun s : ℝ => C.Zt q l (Function.update ω (C.co l false) s)) (C.ZB q l ω)
      (ω (C.co l false)) := by
  have hself := Function.update_eq_self (C.co l false) ω
  have hW := C.hasDerivAt_Wt_false l ω
  have hT := (C.hasDerivAt_Tq_false l ω).fun_pow q
  have hmul := hW.fun_mul hT
  simp only [hself] at hmul
  exact hmul

variable {C}

/-- **`D_l Z_{q,l}`**: the diagonal term (which will sum to `2V_q T^q`) plus the cross term. -/
theorem wirtVal_ZA_ZB (q : ℕ) (l : κ) (ω : Sizes.SeqΩ sz) :
    C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q
        + C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
            (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))) := by
  rw [ZA, ZB, wirtVal_add, wirtVal_mul_right, wirtVal_WA_WB, wirtVal_smul, wirtVal_smul,
    wirtVal_TA_TB]

/-- **The integration by parts of `E[T^{q+1}]`.**  `T^{q+1} = ∑_l \bar h_l Z_{q,l}`, and each
`\bar h_l` is integrated by parts against `Z_{q,l}`. -/
theorem integral_Tq_pow_succ (hG : GaussIBP sz) (q : ℕ) :
    ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(Sizes.seqP sz)
      = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(Sizes.seqP sz) := by
  have hint : ∀ l : κ,
      Integrable (fun ω => (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω) (Sizes.seqP sz) :=
    fun l => (((C.tameh l).conj).mul (C.tameZt q l)).integrable hG
  calc ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(Sizes.seqP sz)
      = ∫ ω, ∑ l, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(Sizes.seqP sz) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => Tq_pow_succ_eq_sum q ω)
    _ = ∑ l, ∫ ω, (starRingEnd ℂ) (C.h ω l) * C.Zt q l ω ∂(Sizes.seqP sz) :=
        integral_finsetSum _ fun l _ => hint l
    _ = ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(Sizes.seqP sz) :=
        Finset.sum_congr rfl fun l _ =>
          C.integral_conj_h_mul_gen hG l (C.tameZt q l) (C.tameZA q l) (C.tameZB q l)
            (C.hasDerivAt_Zt_true q l) (C.hasDerivAt_Zt_false q l)

/-! ### The diagonal term sums to `2 V_q` -/

/-- `∑_l σ_l ∑_k σ_k(‖B_{kl}‖² + ‖B_{lk}‖²) = 2V_q`: the two double sums are the same after
swapping the indices. -/
theorem sum_sg_mul_normSq (ω : Sizes.SeqΩ sz) :
    ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) = 2 * C.Vq ω := by
  have e1 : ∑ l, C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)
      = (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l)
        + ∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : (∑ l, ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 * C.sg l) = C.Vq ω := by
    rw [Vq, Finset.sum_comm]
  have e3 : (∑ l, ∑ k, C.sg l * ‖C.B ω l k‖ ^ 2 * C.sg k) = C.Vq ω := rfl
  rw [e1, e2, e3]; ring

/-- The diagonal part of `∑_l w_l D_l Z_{q,l}` is `2 V_q T^q`. -/
theorem sum_w_diag (q : ℕ) (ω : Sizes.SeqΩ sz) :
    ∑ l, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) := by
  have hterm : ∀ l : κ, (C.w l : ℂ) * ((2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))) * ((C.Tq ω : ℝ) : ℂ) ^ q)
      = ((C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ)
        * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    intro l
    have hk : ∀ k : κ, ((C.sg k : ℝ) : ℂ) *
        (C.B ω k l * (starRingEnd ℂ) (C.B ω k l)
          + C.B ω l k * (starRingEnd ℂ) (C.B ω l k))
        = ((C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) : ℝ) : ℂ) := by
      intro k
      rw [Complex.ofReal_mul, Complex.ofReal_add, ofReal_normSq, ofReal_normSq]
    rw [Finset.sum_congr rfl fun k _ => hk k, ← Complex.ofReal_sum, Complex.ofReal_mul,
      C.sg_complex l]
    ring
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.sum_mul, ← Complex.ofReal_sum,
    C.sum_sg_mul_normSq ω, ← Complex.ofReal_pow, ← Complex.ofReal_mul]

/-! ### The cross term -/

/-- Weighted Cauchy–Schwarz: `(∑ σ x y)² ≤ (∑ σ x²)(∑ σ y²)`. -/
theorem weighted_cauchy {ι : Type*} (s : Finset ι) (σ x y : ι → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (∑ i ∈ s, σ i * (x i * y i)) ^ 2
      ≤ (∑ i ∈ s, σ i * x i ^ 2) * ∑ i ∈ s, σ i * y i ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun i _ => mul_nonneg (hσ i) (sq_nonneg _))
    (fun i _ => mul_nonneg (hσ i) (sq_nonneg _)) (fun i _ => le_of_eq (by ring))

/-- `q·x^{q-1}·x = q·x^q`, valid also at `q = 0`. -/
theorem nat_mul_pow_pred (x : ℝ) (q : ℕ) : (q : ℝ) * x ^ (q - 1) * x = (q : ℝ) * x ^ q := by
  cases q with
  | zero => simp
  | succ n => simp [pow_succ]; ring

variable (C)

/-- The common majorant of `‖W_l‖` and of `‖D_l T‖/(2r²)`. -/
noncomputable def Arow (l : κ) (ω : Sizes.SeqΩ sz) : ℝ :=
  ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖ + ‖C.V ω k‖ * ‖C.B ω l k‖)

variable {C}

theorem Arow_nonneg (l : κ) (ω : Sizes.SeqΩ sz) : 0 ≤ C.Arow l ω :=
  Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)

theorem norm_Wt_le (l : κ) (ω : Sizes.SeqΩ sz) : ‖C.Wt l ω‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]

theorem norm_sum_UV_le (l : κ) (ω : Sizes.SeqΩ sz) :
    ‖∑ k, ((C.sg k : ℝ) : ℂ) * (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
      + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖ ≤ C.Arow l ω := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.sg_nonneg k)]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (C.sg_nonneg k)
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
  have h1 : ‖C.U ω k‖ * ‖C.B ω k l‖ = ‖C.B ω k l‖ * ‖C.U ω k‖ := mul_comm _ _
  have h2 : ‖C.B ω l k‖ * ‖C.V ω k‖ = ‖C.V ω k‖ * ‖C.B ω l k‖ := mul_comm _ _
  rw [h1, h2]

theorem sum_sg_normSq_U_le (ω : Sizes.SeqΩ sz) : ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  have := mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.V ω k‖] : ‖C.U ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)
  exact this

theorem sum_sg_normSq_V_le (ω : Sizes.SeqΩ sz) : ∑ k, C.sg k * ‖C.V ω k‖ ^ 2 ≤ C.Tq ω := by
  refine Finset.sum_le_sum fun k _ => ?_
  exact mul_le_mul_of_nonneg_left
    (by nlinarith [sq_nonneg ‖C.U ω k‖] : ‖C.V ω k‖ ^ 2 ≤ ‖C.U ω k‖ ^ 2 + ‖C.V ω k‖ ^ 2)
    (C.sg_nonneg k)

/-- `A_l² ≤ 2T(∑_kσ_k‖B_{kl}‖² + ∑_kσ_k‖B_{lk}‖²)`, by Cauchy–Schwarz in `k`. -/
theorem sq_Arow_le (l : κ) (ω : Sizes.SeqΩ sz) :
    C.Arow l ω ^ 2
      ≤ 2 * C.Tq ω * ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2) := by
  set P : ℝ := ∑ k, C.sg k * (‖C.B ω k l‖ * ‖C.U ω k‖) with hP
  set Q : ℝ := ∑ k, C.sg k * (‖C.V ω k‖ * ‖C.B ω l k‖) with hQ
  have hsplit : C.Arow l ω = P + Q := by
    rw [hP, hQ, Arow, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hPc : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * ∑ k, C.sg k * ‖C.U ω k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hQc : Q ^ 2 ≤ (∑ k, C.sg k * ‖C.V ω k‖ ^ 2) * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    weighted_cauchy _ _ _ _ (fun k => C.sg_nonneg k)
  have hB1 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω k l‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hB2 : (0 : ℝ) ≤ ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (C.sg_nonneg k) (by positivity)
  have hU := C.sum_sg_normSq_U_le ω
  have hV := C.sum_sg_normSq_V_le ω
  have hP2 : P ^ 2 ≤ (∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) * C.Tq ω := by
    refine hPc.trans (mul_le_mul_of_nonneg_left hU hB1)
  have hQ2 : Q ^ 2 ≤ C.Tq ω * ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2 := by
    refine hQc.trans (mul_le_mul_of_nonneg_right hV hB2)
  rw [hsplit]
  nlinarith [sq_nonneg (P - Q)]

/-! ### The cross term, bounded -/

variable (C)

/-- The cross term of `∑_l w_l D_l Z_{q,l}`. -/
noncomputable def crossT (q : ℕ) (ω : Sizes.SeqΩ sz) : ℂ :=
  ∑ l, (C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
    (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
      (C.U ω k * (starRingEnd ℂ) (C.B ω k l) + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))

variable {C}

theorem Vq_nonneg (ω : Sizes.SeqΩ sz) : 0 ≤ C.Vq ω :=
  Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    mul_nonneg (mul_nonneg (C.sg_nonneg k) (by positivity)) (C.sg_nonneg l)

/-- `∑_l w_l D_l Z_{q,l}` splits into the diagonal `2V_qT^q` and the cross term. -/
theorem sum_w_wirtVal_ZA_ZB (q : ℕ) (ω : Sizes.SeqΩ sz) :
    ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)
      = ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω := by
  rw [← C.sum_w_diag q ω, crossT, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by rw [wirtVal_ZA_ZB]; ring

/-- **The cross term is `≤ 4q V_q T^q`.**  Two Cauchy–Schwarz steps: first in `k`
(`sq_Arow_le`), then the sum over `l` against `σ_l` is `2V_q` (`sum_sg_mul_normSq`). -/
theorem norm_crossT_le (q : ℕ) (ω : Sizes.SeqΩ sz) :
    ‖C.crossT q ω‖ ≤ 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
  have hTn := C.Tq_nonneg ω
  have hTp : (0 : ℝ) ≤ C.Tq ω ^ (q - 1) := by positivity
  have hterm : ∀ l : κ, ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
        (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
          (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
            + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
      ≤ C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
    intro l
    have hw : ‖(C.w l : ℂ)‖ = C.w l := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (C.w_nonneg l)]
    have hqn : ‖(q : ℂ)‖ = (q : ℝ) := by simp
    have hT : ‖((C.Tq ω : ℝ) : ℂ) ^ (q - 1)‖ = C.Tq ω ^ (q - 1) := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hTn]
    have hr : ‖(2 : ℂ) * (C.r : ℂ) ^ 2‖ = 2 * C.r ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      norm_num
    have hA := C.Arow_nonneg l ω
    have hr2 : (0 : ℝ) ≤ 2 * C.r ^ 2 := by positivity
    calc ‖(C.w l : ℂ) * (C.Wt l ω * ((q : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ (q - 1) *
          (2 * (C.r : ℂ) ^ 2 * ∑ k, ((C.sg k : ℝ) : ℂ) *
            (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
              + C.B ω l k * (starRingEnd ℂ) (C.V ω k)))))‖
        = C.w l * (‖C.Wt l ω‖ * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * ‖∑ k, ((C.sg k : ℝ) : ℂ) *
              (C.U ω k * (starRingEnd ℂ) (C.B ω k l)
                + C.B ω l k * (starRingEnd ℂ) (C.V ω k))‖))) := by
          simp only [norm_mul, hw, hqn, hT, hr]
      _ ≤ C.w l * (C.Arow l ω * ((q : ℝ) * C.Tq ω ^ (q - 1) *
            (2 * C.r ^ 2 * C.Arow l ω))) := by
          gcongr
          · exact C.w_nonneg l
          · exact norm_Wt_le l ω
          · exact norm_sum_UV_le l ω
      _ = C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) := by
          change C.w l * _ = 2 * C.r ^ 2 * C.w l * _
          ring
  have hstep1 : ‖C.crossT q ω‖
      ≤ ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2) :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => hterm l)
  have hstep2 : ∑ l, C.sg l * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Arow l ω ^ 2)
      = (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hstep3 : ∑ l, C.sg l * C.Arow l ω ^ 2 ≤ 2 * C.Tq ω * (2 * C.Vq ω) := by
    have hbound : ∀ l : κ, C.sg l * C.Arow l ω ^ 2
        ≤ 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by
      intro l
      have h := C.sq_Arow_le l ω
      have hmerge : ((∑ k, C.sg k * ‖C.B ω k l‖ ^ 2) + ∑ k, C.sg k * ‖C.B ω l k‖ ^ 2)
          = ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hmerge] at h
      have := mul_le_mul_of_nonneg_left h (C.sg_nonneg l)
      calc C.sg l * C.Arow l ω ^ 2
          ≤ C.sg l * (2 * C.Tq ω *
              ∑ k, C.sg k * (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := this
        _ = 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
              (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := by ring
    calc ∑ l, C.sg l * C.Arow l ω ^ 2
        ≤ ∑ l, 2 * C.Tq ω * (C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2)) := Finset.sum_le_sum fun l _ => hbound l
      _ = 2 * C.Tq ω * ∑ l, C.sg l * ∑ k, C.sg k *
            (‖C.B ω k l‖ ^ 2 + ‖C.B ω l k‖ ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * C.Tq ω * (2 * C.Vq ω) := by rw [C.sum_sg_mul_normSq ω]
  have hqT : (0 : ℝ) ≤ (q : ℝ) * C.Tq ω ^ (q - 1) := by positivity
  calc ‖C.crossT q ω‖
      ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * ∑ l, C.sg l * C.Arow l ω ^ 2 := by
        rw [← hstep2]; exact hstep1
    _ ≤ (q : ℝ) * C.Tq ω ^ (q - 1) * (2 * C.Tq ω * (2 * C.Vq ω)) :=
        mul_le_mul_of_nonneg_left hstep3 hqT
    _ = 4 * ((q : ℝ) * C.Tq ω ^ (q - 1) * C.Tq ω) * C.Vq ω := by ring
    _ = 4 * (q : ℝ) * C.Vq ω * C.Tq ω ^ q := by
        rw [nat_mul_pow_pred (C.Tq ω) q]; ring

/-! ### `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]` -/

variable (C)

theorem tameCrossT (q : ℕ) : Tame sz (C.crossT q) :=
  Tame.sum _ fun l _ => (Tame.const (sz := sz) ((C.w l : ℂ))).mul
    ((C.tameWt l).mul (((Tame.const (sz := sz) ((q : ℂ))).mul (C.tameTq.pow (q - 1))).mul
      ((Tame.const (sz := sz) (2 * (C.r : ℂ) ^ 2)).mul
        (Tame.sum _ fun k _ => (Tame.const (sz := sz) ((C.sg k : ℝ) : ℂ)).mul
          (((C.tameU k).mul (C.tameB k l).conj).add
            ((C.tameB l k).mul (C.tameV k).conj))))))

theorem tameWirt (q : ℕ) (l : κ) :
    Tame sz fun ω => C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) :=
  (Tame.const (sz := sz) ((C.r : ℂ))).mul
    ((C.tameZA q l).sub ((Tame.const (sz := sz) ((C.eps l : ℂ) * Complex.I)).mul (C.tameZB q l)))

/-- `V_q T^q` is integrable. -/
theorem integrable_Vq_mul_Tq_pow (hG : GaussIBP sz) (q : ℕ) :
    Integrable (fun ω => C.Vq ω * C.Tq ω ^ q) (Sizes.seqP sz) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Sizes.SeqΩ sz => ((C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) * ((C.Tq ω : ℝ) : ℂ) ^ q := by
    funext ω; rw [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.mul (C.tameTq.pow q)

/-- `V_q^q` is integrable. -/
theorem integrable_Vq_pow (hG : GaussIBP sz) (q : ℕ) :
    Integrable (fun ω => C.Vq ω ^ q) (Sizes.seqP sz) := by
  refine integrable_of_tame_ofReal hG ?_
  have hfun : (fun ω : Sizes.SeqΩ sz => ((C.Vq ω ^ q : ℝ) : ℂ))
      = fun ω => ((C.Vq ω : ℝ) : ℂ) ^ q := by funext ω; rw [Complex.ofReal_pow]
  rw [hfun]
  exact C.tame_ofReal_Vq.pow q

/-- `E[V_q^q]`. -/
noncomputable def momVpow (q : ℕ) : ℝ := ∫ ω, C.Vq ω ^ q ∂(Sizes.seqP sz)

theorem momVpow_nonneg (q : ℕ) : 0 ≤ C.momVpow q :=
  MeasureTheory.integral_nonneg fun ω => pow_nonneg (C.Vq_nonneg ω) q

variable {C}

/-- **The recursion for the positive chaos**: `E[T^{q+1}] ≤ (4q+2) E[V_q T^q]`.  The diagonal
term of the integration by parts is `2E[V_qT^q]`; the cross term is at most `4qE[V_qT^q]`. -/
theorem momTpow_succ_le (hG : GaussIBP sz) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) * ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(Sizes.seqP sz) := by
  set I1 : ℝ := ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(Sizes.seqP sz) with hI1
  have hiVT := C.integrable_Vq_mul_Tq_pow hG q
  have hiCross : Integrable (C.crossT q) (Sizes.seqP sz) := (C.tameCrossT q).integrable hG
  have hiW : ∀ l : κ, Integrable (fun ω => (C.w l : ℂ) *
      C.wirtVal l (C.ZA q l ω) (C.ZB q l ω)) (Sizes.seqP sz) :=
    fun l => ((Tame.const (sz := sz) ((C.w l : ℂ))).mul (C.tameWirt q l)).integrable hG
  have hiDiag :
      Integrable (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
        (Sizes.seqP sz) := by
    have : (fun ω : Sizes.SeqΩ sz => ((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ))
        = fun ω => ((2 * (C.Vq ω * C.Tq ω ^ q) : ℝ) : ℂ) := by
      funext ω; norm_num; ring_nf
    rw [this]
    exact (MeasureTheory.Integrable.ofReal (hiVT.const_mul 2))
  -- the complex identity
  have hId : ((C.momTpow (q + 1) : ℝ) : ℂ)
      = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(Sizes.seqP sz) := by
    have h1 : ((C.momTpow (q + 1) : ℝ) : ℂ)
        = ∫ ω, ((C.Tq ω : ℝ) : ℂ) ^ (q + 1) ∂(Sizes.seqP sz) := by
      rw [momTpow, ← integral_ofReal']
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => Complex.ofReal_pow _ _)
    have h2 : ∑ l, (C.w l : ℂ) * ∫ ω, C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(Sizes.seqP sz)
        = ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(Sizes.seqP sz) := by
      rw [MeasureTheory.integral_finsetSum _ fun l _ => hiW l]
      exact Finset.sum_congr rfl fun l _ => (MeasureTheory.integral_const_mul _ _).symm
    have h3 : ∫ ω, ∑ l, (C.w l : ℂ) * C.wirtVal l (C.ZA q l ω) (C.ZB q l ω) ∂(Sizes.seqP sz)
        = ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(Sizes.seqP sz) :=
      MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun ω => sum_w_wirtVal_ZA_ZB q ω)
    have h4 : ∫ ω, (((2 * C.Vq ω * C.Tq ω ^ q : ℝ) : ℂ) + C.crossT q ω) ∂(Sizes.seqP sz)
        = ((2 * I1 : ℝ) : ℂ) + ∫ ω, C.crossT q ω ∂(Sizes.seqP sz) := by
      rw [MeasureTheory.integral_add hiDiag hiCross]
      congr 1
      rw [integral_ofReal']
      congr 1
      rw [hI1, ← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, integral_Tq_pow_succ hG, h2, h3, h4]
  -- the cross term is small
  have hcross : ‖∫ ω, C.crossT q ω ∂(Sizes.seqP sz)‖ ≤ 4 * (q : ℝ) * I1 := by
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖C.crossT q ω‖ ∂(Sizes.seqP sz)
        ≤ ∫ ω, 4 * (q : ℝ) * (C.Vq ω * C.Tq ω ^ q) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_mono hiCross.norm (hiVT.const_mul (4 * (q : ℝ)))
            (fun ω => (norm_crossT_le (C := C) q ω).trans_eq (by ring))
      _ = 4 * (q : ℝ) * I1 := by
          rw [hI1, MeasureTheory.integral_const_mul]
  have hsub : ((C.momTpow (q + 1) - 2 * I1 : ℝ) : ℂ) = ∫ ω, C.crossT q ω ∂(Sizes.seqP sz) := by
    rw [Complex.ofReal_sub, hId]; ring
  have habs : |C.momTpow (q + 1) - 2 * I1| ≤ 4 * (q : ℝ) * I1 := by
    have := hcross
    rw [← hsub, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have := (abs_le.1 habs).2
  linarith

/-! ### Closing the recursion: `E[T^p] ≤ (4p−2)^p E[V_q^p]` -/

/-- **The positive chaos moment bound.**  `E[T^{q+1}] ≤ (4q+2)^{q+1} E[V_q^{q+1}]`.

The recursion `E[T^{q+1}] ≤ (4q+2)E[V_qT^q]` is closed by the same pointwise Young inequality
`RBM.Green.young_pow` that closes `RBM.Green.RowChaos.mom_succ_le`, with the rational parameter
`K = 4q+2`; every exponent stays a natural number. -/
theorem momTpow_le (hG : GaussIBP sz) (q : ℕ) :
    C.momTpow (q + 1) ≤ (4 * (q : ℝ) + 2) ^ (q + 1) * C.momVpow (q + 1) := by
  set K : ℝ := 4 * (q : ℝ) + 2 with hKdef
  have hK0 : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hpt : ∀ ω : Sizes.SeqΩ sz, C.Vq ω * C.Tq ω ^ q
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1) := by
    intro ω
    have hV := C.Vq_nonneg ω
    have hT := C.Tq_nonneg ω
    have hy := young_pow q (mul_nonneg hV hK0.le) hT
    have hmul : (0 : ℝ) < ((q : ℝ) + 1) * K := by positivity
    refine le_of_mul_le_mul_left ?_ hmul
    have hleft : ((q : ℝ) + 1) * K * (C.Vq ω * C.Tq ω ^ q)
        = ((q : ℝ) + 1) * (C.Vq ω * K * C.Tq ω ^ q) := by ring
    have hrhs : ((q : ℝ) + 1) * K * ((K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
          + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1))
        = (C.Vq ω * K) ^ (q + 1) + (q : ℝ) * C.Tq ω ^ (q + 1) := by
      rw [mul_pow]
      field_simp
      ring
    rw [hleft, hrhs]
    exact hy
  have hi1 := C.integrable_Vq_pow hG (q + 1)
  have hi2 := C.integrable_Tq_pow hG (q + 1)
  have hA : (∫ ω, C.Vq ω * C.Tq ω ^ q ∂(Sizes.seqP sz))
      ≤ (K ^ q / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.momTpow (q + 1) := by
    calc ∫ ω, C.Vq ω * C.Tq ω ^ q ∂(Sizes.seqP sz)
        ≤ ∫ ω, ((K ^ q / ((q : ℝ) + 1)) * C.Vq ω ^ (q + 1)
            + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.Tq ω ^ (q + 1)) ∂(Sizes.seqP sz) :=
          MeasureTheory.integral_mono (C.integrable_Vq_mul_Tq_pow hG q)
            ((hi1.const_mul _).add (hi2.const_mul _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (hi1.const_mul _) (hi2.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          rfl
  have hKne : K ≠ 0 := ne_of_gt hK0
  have hqne : ((q : ℝ) + 1) ≠ 0 := ne_of_gt hq1
  have hM := C.momTpow_succ_le hG q
  rw [← hKdef] at hM
  have hN := C.momVpow_nonneg (q + 1)
  have hT0 := C.momTpow_nonneg (q + 1)
  have hKmul : K * ((K ^ q / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / (((q : ℝ) + 1) * K)) * C.momTpow (q + 1))
      = (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1) := by
    rw [pow_succ]
    field_simp
  have hchain : C.momTpow (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1)
        + ((q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1) := by
    refine hM.trans ?_
    rw [← hKmul]
    exact mul_le_mul_of_nonneg_left hA hK0.le
  have hA' : K ^ (q + 1) / ((q : ℝ) + 1) ≤ K ^ (q + 1) := by
    rw [div_le_iff₀ hq1]
    nlinarith [pow_nonneg hK0.le (q + 1), Nat.cast_nonneg (α := ℝ) q]
  have hstep : (1 - (q : ℝ) / ((q : ℝ) + 1)) * C.momTpow (q + 1)
      ≤ (K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1) := by nlinarith [hchain]
  have hone : (1 : ℝ) - (q : ℝ) / ((q : ℝ) + 1) = 1 / ((q : ℝ) + 1) := by
    rw [eq_div_iff hqne, sub_mul, div_mul_cancel₀ _ hqne, one_mul]
    ring
  rw [hone] at hstep
  have := mul_le_mul_of_nonneg_left hstep hq1.le
  have hl : ((q : ℝ) + 1) * (1 / ((q : ℝ) + 1) * C.momTpow (q + 1)) = C.momTpow (q + 1) := by
    field_simp
  have hr : ((q : ℝ) + 1) * ((K ^ (q + 1) / ((q : ℝ) + 1)) * C.momVpow (q + 1))
      = K ^ (q + 1) * C.momVpow (q + 1) := by field_simp
  rw [hl, hr] at this
  exact this

/-- **Hanson–Wright for the Gaussian row chaos, in the paper's control.**  Combining the
recursion of `RBM.Green.RowChaos.mom_succ_le` with the positive chaos bound,

`E|Q|^{2(q+1)} ≤ ((2q+1)(4q+2))^{q+1} E[V_q^{q+1}]`,

with `V_q = ∑_{k,l}σ_k‖B_{kl}‖²σ_l` — exactly `RBM.Green.ldeQuadRHS` up to the factor `t²`
(`RBM.Green.RowChaos.Vq_eq_ldeQuadRHS`).  This is the moment form of the quadratic large
deviation estimate for an abstract row chaos; the instance for the model is a separate file. -/
theorem mom_le_momVpow (hG : GaussIBP sz) (q : ℕ) :
    C.mom (q + 1)
      ≤ ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
  have h1 := C.mom_succ_le hG q
  have h2 := C.momTpow_le hG q
  have hc : (0 : ℝ) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) := by positivity
  calc C.mom (q + 1) ≤ (2 * (q : ℝ) + 1) ^ (q + 1) * C.momTpow (q + 1) := h1
    _ ≤ (2 * (q : ℝ) + 1) ^ (q + 1) *
        ((4 * (q : ℝ) + 2) ^ (q + 1) * C.momVpow (q + 1)) :=
          mul_le_mul_of_nonneg_left h2 hc
    _ = ((2 * (q : ℝ) + 1) * (4 * (q : ℝ) + 2)) ^ (q + 1) * C.momVpow (q + 1) := by
        rw [mul_pow]; ring

end RowChaos

/-! ### Compile checks: a three-dimensional row chaos indexed by `{k : Fin 3 // k ≠ 0}`

The data of the checks of `RBM3D/Green/LDEQuadMom.lean` (private there, so a fresh copy with the
prefix `chkT`): `SizesInst.sz0` at `d = 3`, slice `n = 0` (`L = 4`, `W = 32`, `lam = 1/64`,
`N = 2097152`), the row `x = 0`, the columns `k = 1` (the point `(1,0,0)`, same block) and `k = 2`
(the point `(32,0,0)`, neighbouring block), `eps = 1`, `r = 1`, and the constant matrix
`B = [[2,1],[0,3]]` (`Ifree = ∅`, `Bbd = 3`).  `σ_k = S_{x,k} > 0` for both columns, so `Vq > 0`.
`GaussIBP sz0` (S1-19) stays a hypothesis of the examples. -/

section Checks

open SizesInst

/-- The lattice points of the three matrix indices: the row `x = 0`, then `(1,0,0)` and
`(32,0,0)`. -/
private noncomputable def chkTPos : Fin 3 → Idx 3 (sz0.L 0) (sz0.W 0) :=
  ![0, ![1, 0, 0], ![32, 0, 0]]

private theorem chkTPos_injective : Function.Injective chkTPos := by
  intro a b h
  revert a b
  decide

/-- The two coordinates of each column index. -/
private noncomputable def chkTCo (k : {k : Fin 3 // k ≠ 0}) (b : Bool) : Sizes.SeqCoord sz0 :=
  ⟨0, (chkTPos 0, chkTPos k.1, b)⟩

/-- The matrix `G = diag(1, [[2,1],[0,3]])`. -/
private def chkTG : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 2, 1; 0, 0, 3]

private theorem chkT_green (k l : Fin 3) : ‖greenMinor chkTG 0 k l‖ ≤ 3 := by
  fin_cases k <;> fin_cases l <;> (simp [greenMinor, chkTG]; try norm_num)

private theorem chkTCo_injective :
    Function.Injective fun p : {k : Fin 3 // k ≠ 0} × Bool => chkTCo p.1 p.2 := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ h
  simp only [chkTCo, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨hy, hb⟩ := h
  rw [Subtype.ext (chkTPos_injective hy), hb]

/-- The row chaos on `{k : Fin 3 // k ≠ 0}`. -/
private noncomputable def chkTChaos : RowChaos sz0 {k : Fin 3 // k ≠ 0} where
  co := chkTCo
  co_inj := chkTCo_injective
  gvar_tag _ := rfl
  eps _ := 1
  eps_sq _ := by norm_num
  r := 1
  B _ k l := greenMinor chkTG 0 k.1 l.1
  B_cont _ _ := continuous_const
  Bbd := 3
  B_bdd _ k l := chkT_green k.1 l.1
  Ifree := ∅
  Ifree_free _ _ := Finset.notMem_empty _
  B_free _ _ _ := rfl

private theorem chkT_gvarF_offDiag (i j : Idx 3 (sz0.L 0) (sz0.W 0)) (b : Bool) (hij : i ≠ j) :
    (gvarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (i, j, b) : ℝ) =
      svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j / 2 := by
  change (if i = j then svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j
    else svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) i j / 2) = _
  simp [hij]

/-- **Check (nondegeneracy).** Same-block column: `S_{xy} = (W^3)⁻¹ (1 + 6 g²)⁻¹` with
`W = 32`, `g = 1/64`. -/
private theorem chkT_svarF_one :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos 1) =
      ((32 : ℝ) ^ 3)⁻¹ * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹ := by
  have h1 : (split 3 (sz0.L 0) (sz0.W 0) (chkTPos 0)).1 = 0 := by decide
  have h2 : (split 3 (sz0.L 0) (sz0.W 0) (chkTPos 1)).1 = 0 := by decide
  have h3 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have h4 : sz0.W 0 = 32 := sz0_values.2.1
  simp only [svarF, SBR, Matrix.of_apply, h1, h2, sub_self, sbKernelR, h3, h4, ite_true]
  norm_num

/-- **Check (nondegeneracy).** Neighbouring-block column:
`S_{xy} = (W^3)⁻¹ g² (1 + 6 g²)⁻¹` with `W = 32`, `g = 1/64`. -/
private theorem chkT_svarF_two :
    svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos 2) =
      ((32 : ℝ) ^ 3)⁻¹ * ((1 / 64 : ℝ) ^ 2 * (1 + 2 * 3 * (1 / 64 : ℝ) ^ 2)⁻¹) := by
  have h1 : (split 3 (sz0.L 0) (sz0.W 0) (chkTPos 0)).1 = 0 := by decide
  have h2 : (split 3 (sz0.L 0) (sz0.W 0) (chkTPos 2)).1 = ![1, 0, 0] := by decide
  have h3 : sz0.lam 0 = 1 / 64 := sz0_values.2.2.2
  have h4 : sz0.W 0 = 32 := sz0_values.2.1
  have h5 : zdistD 3 (sz0.L 0) (-(![1, 0, 0] : Zd 3 (sz0.L 0))) = 1 := by decide
  have h6 : (-(![1, 0, 0] : Zd 3 (sz0.L 0))) ≠ 0 := by decide
  simp only [svarF, SBR, Matrix.of_apply, h1, h2, zero_sub, sbKernelR, h3, h4, h5, h6, ite_false,
    ite_true, zero_add]
  norm_num

/-- **Check (nondegeneracy).** `σ_k = 2 r² w_k = S_{x, pos k}` for the private chaos. -/
private theorem chkT_sg (k : {k : Fin 3 // k ≠ 0}) :
    chkTChaos.sg k = svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos k.1) := by
  have hne : chkTPos 0 ≠ chkTPos k.1 := fun h => k.2 (chkTPos_injective h).symm
  have hw : chkTChaos.w k = svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos k.1) / 2 :=
    chkT_gvarF_offDiag _ _ true hne
  have hr : chkTChaos.r = 1 := rfl
  rw [RowChaos.sg, hw, hr]
  ring

/-- **Check (nondegeneracy).** Both columns have `σ_k > 0`. -/
private theorem chkT_sg_pos (k : {k : Fin 3 // k ≠ 0}) : 0 < chkTChaos.sg k := by
  rw [chkT_sg]
  obtain ⟨k, hk⟩ := k
  fin_cases k
  · exact absurd rfl hk
  · change 0 < svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos 1)
    rw [chkT_svarF_one]; norm_num
  · change 0 < svarF 3 (sz0.L 0) (sz0.W 0) (sz0.lam 0) (chkTPos 0) (chkTPos 2)
    rw [chkT_svarF_two]; norm_num

/-- **Check (nondegeneracy).** The paper's control of the private chaos is strictly positive: the
`(1,1)`-term `σ_1 ‖B_{11}‖² σ_1 = 4 σ_1²` of `Vq` is positive, and `Vq ≥ 0`. -/
private theorem chkT_Vq_pos (ω : Sizes.SeqΩ sz0) : 0 < chkTChaos.Vq ω := by
  classical
  let k1 : {k : Fin 3 // k ≠ 0} := ⟨1, by decide⟩
  have hB : ‖chkTChaos.B ω k1 k1‖ = 2 := by
    change ‖greenMinor chkTG 0 1 1‖ = 2
    simp [greenMinor, chkTG]
  have hrow : chkTChaos.sg k1 * ‖chkTChaos.B ω k1 k1‖ ^ 2 * chkTChaos.sg k1
      ≤ ∑ l, chkTChaos.sg k1 * ‖chkTChaos.B ω k1 l‖ ^ 2 * chkTChaos.sg l :=
    Finset.single_le_sum (f := fun l => chkTChaos.sg k1 * ‖chkTChaos.B ω k1 l‖ ^ 2 *
      chkTChaos.sg l) (fun l _ => mul_nonneg (mul_nonneg (chkTChaos.sg_nonneg k1) (by positivity))
        (chkTChaos.sg_nonneg l)) (Finset.mem_univ k1)
  have hall : ∑ l, chkTChaos.sg k1 * ‖chkTChaos.B ω k1 l‖ ^ 2 * chkTChaos.sg l
      ≤ chkTChaos.Vq ω :=
    Finset.single_le_sum (f := fun k => ∑ l, chkTChaos.sg k * ‖chkTChaos.B ω k l‖ ^ 2 *
      chkTChaos.sg l) (fun k _ => Finset.sum_nonneg fun l _ =>
        mul_nonneg (mul_nonneg (chkTChaos.sg_nonneg k) (by positivity)) (chkTChaos.sg_nonneg l))
      (Finset.mem_univ k1)
  have hpos : 0 < chkTChaos.sg k1 * ‖chkTChaos.B ω k1 k1‖ ^ 2 * chkTChaos.sg k1 := by
    rw [hB]; have := chkT_sg_pos k1; positivity
  exact lt_of_lt_of_le hpos (hrow.trans hall)

section Instances

variable (hG : GaussIBP sz0)
include hG

/-- **Instance of `mom_le_momVpow`** (the target) at `q = 0, 1, 2` (`p = 1, 2, 3`), on the
nondegenerate chaos with `Vq > 0` (`chkT_Vq_pos`): `GaussIBP sz0` a hypothesis (S1-19), every
other hypothesis discharged. -/
example :
    chkTChaos.mom 1 ≤ ((2 * ((0 : ℕ) : ℝ) + 1) * (4 * ((0 : ℕ) : ℝ) + 2)) ^ (0 + 1) *
        chkTChaos.momVpow (0 + 1) ∧
    chkTChaos.mom 2 ≤ ((2 * ((1 : ℕ) : ℝ) + 1) * (4 * ((1 : ℕ) : ℝ) + 2)) ^ (1 + 1) *
        chkTChaos.momVpow (1 + 1) ∧
    chkTChaos.mom 3 ≤ ((2 * ((2 : ℕ) : ℝ) + 1) * (4 * ((2 : ℕ) : ℝ) + 2)) ^ (2 + 1) *
        chkTChaos.momVpow (2 + 1) :=
  ⟨chkTChaos.mom_le_momVpow hG 0, chkTChaos.mom_le_momVpow hG 1, chkTChaos.mom_le_momVpow hG 2⟩

/-- **Instance of `momTpow_le`** at `q = 0, 1`. -/
example :
    chkTChaos.momTpow (0 + 1)
      ≤ (4 * ((0 : ℕ) : ℝ) + 2) ^ (0 + 1) * chkTChaos.momVpow (0 + 1) ∧
    chkTChaos.momTpow (1 + 1)
      ≤ (4 * ((1 : ℕ) : ℝ) + 2) ^ (1 + 1) * chkTChaos.momVpow (1 + 1) :=
  ⟨chkTChaos.momTpow_le hG 0, chkTChaos.momTpow_le hG 1⟩

/-- **Instance of `momTpow_succ_le`** at `q = 1`. -/
example :
    chkTChaos.momTpow (1 + 1)
      ≤ (4 * ((1 : ℕ) : ℝ) + 2) * ∫ ω, chkTChaos.Vq ω * chkTChaos.Tq ω ^ 1
          ∂(Sizes.seqP sz0) :=
  chkTChaos.momTpow_succ_le hG 1

end Instances

/-- **Instance of `norm_crossT_le`** at `q = 0`: the cross term vanishes. -/
example (ω : Sizes.SeqΩ sz0) :
    ‖chkTChaos.crossT 0 ω‖ ≤ 4 * ((0 : ℕ) : ℝ) * chkTChaos.Vq ω * chkTChaos.Tq ω ^ 0 :=
  chkTChaos.norm_crossT_le 0 ω

end Checks

end RBM.Green
