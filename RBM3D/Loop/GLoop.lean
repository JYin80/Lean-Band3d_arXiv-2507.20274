/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Gauss.Model
import RBM3D.Defs.Semicircle
import RBM3D.Analysis.Resolvent

/-!
# `G`-loops

`(Eq:defGLoop)`: for `σ ∈ {+,-}^n` and `a ∈ (Z_L^d)^n`, the `n`-`G`-loop is

  `L^(n)_{t,σ,a} = tr ( Π_i G_t(σ_i) E_{a_i} )`,  `(E_a)_{xy} = W^{-d} 1(x = y ∈ [a])`,

with `G_t(+) = (H_t - z_t)^{-1}` and `G_t(-) = G_t^*`, along the flow
`z_t = E + (1-t) m^{(E)}` of `(eq:zt)`.

## What is here

The definitions, and the two facts that do not need any operator-norm machinery:

* `RBM.Gauss.Eblk` : the rescaled block identity `E_a`, and `Eblk_isHermitian`;
* `RBM.Gauss.etaT` : `η_t = (1-t) Im m^{(E)}`, `etaT_eq_zt_im`, and `etaT_pos` -- positive
  for `|E| < 2` and `t < 1`, which is what puts `z_t` off the real axis and makes the
  resolvent exist;
* `RBM.Gauss.Gsig` : `G_t(σ)` as `Ring.inverse (H - z • 1)`, in the same style as
  `RBM.Theta`, and `gloop`, `loopMax`.

## What is missing, and what it needs

The deterministic envelope `|L^(n)| ≤ (η_t^{-1})^n` of `(5.2)`.  The analytic input is in
place (`RBM3D/Analysis/Resolvent.lean`: `‖(H-z)⁻¹‖ ≤ (Im z)⁻¹` pointwise on the whole
space), but turning it into a bound on a **trace of a product** needs `|tr X| ≤ rank · ‖X‖`
or a trace-norm inequality, and Mathlib's `Matrix.trace` has no such API for the `ℓ²`
operator norm.  That gap is recorded in `docs/QUEUE.md` (Q50) rather than papered over
here: the project does not state what it cannot prove.
-/

namespace RBM.Gauss

open Matrix Complex

variable (d L W : ℕ) [NeZero L] (g : ℝ)

/-! ### The rescaled block identity `E_a` -/

/-- `(E_a)_{xy} = W^{-d} 1(x = y ∈ [a])` of `(Eq:defGLoop)`. -/
noncomputable def Eblk (a : Zd d L) : Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Matrix.diagonal fun x => if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0

variable {d L W}

omit [NeZero L] in
theorem Eblk_apply (a : Zd d L) (x y : Vtx d L W) :
    Eblk d L W a x y = if x = y then (if x.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) else 0 := by
  simp [Eblk, Matrix.diagonal_apply]

omit [NeZero L] in
theorem Eblk_isHermitian (a : Zd d L) : (Eblk d L W a).IsHermitian := by
  refine Matrix.isHermitian_diagonal_iff.mpr fun x => ?_
  by_cases h : x.1 = a <;> simp [h, IsSelfAdjoint]

/-! ### The flow `z_t` and its imaginary part -/

variable (E t : ℝ)

/-- `η_t = (1 - t) Im m^{(E)}`, the imaginary part of the flow `(eq:zt)`; `(eta)`. -/
noncomputable def etaT : ℝ := (1 - t) * (mE E).im

variable {E t}

theorem etaT_eq_zt_im : etaT E t = (zt E t).im := by
  rw [etaT, zt_im]

/-- `η_t > 0` in the bulk for `t < 1`: this is what keeps `z_t` off the real axis. -/
theorem etaT_pos (hE : |E| < 2) (ht : t < 1) : 0 < etaT E t :=
  mul_pos (by linarith) (mE_im_pos hE)

/-! ### `G_t(σ)` and the loops -/

variable (d L W)

/-- `G_t(σ)`: the resolvent at `z_t` for `σ = +` and at `conj z_t` for `σ = -`, as
`Ring.inverse`, in the same style as `RBM.Theta`. -/
noncomputable def Gsig (ω : Omega d L W) (E t : ℝ) (σ : Bool) :
    Matrix (Vtx d L W) (Vtx d L W) ℂ :=
  Ring.inverse (Hmat d L W ω - (if σ then zt E t else (starRingEnd ℂ) (zt E t)) • 1)

/-- **`(Eq:defGLoop)`**: the `n`-`G`-loop `tr (Π_i G_t(σ_i) E_{a_i})`. -/
noncomputable def gloop (ω : Omega d L W) (E t : ℝ) {n : ℕ} (σ : Fin n → Bool)
    (a : Fin n → Zd d L) : ℂ :=
  Matrix.trace (List.ofFn fun i : Fin n => Gsig d L W ω E t (σ i) * Eblk d L W (a i)).prod

/-- `max_{σ,a} |L^(n)_{t,σ,a}|`, the quantity the loop estimates are stated for. -/
noncomputable def loopMax (ω : Omega d L W) (E t : ℝ) (n : ℕ) : ℝ :=
  ⨆ p : (Fin n → Bool) × (Fin n → Zd d L), ‖gloop d L W ω E t p.1 p.2‖

/-! ### The deterministic envelope `(5.2)`

`|L^(n)_{t,σ,a}| ≤ (η_t^{-1})^n`, pointwise in `ω` and on the whole space.

**Why not through the operator norm.**  Bounding each factor by `‖G E_a‖₂ ≤ η^{-1}W^{-d}`
and the trace by `|tr X| ≤ card · ‖X‖₂` gives `L^d W^{d(1-n)} η^{-n}`, which is *not*
`η^{-n}` for `n ≥ 2`: the volume of the matrix beats the smallness of `E_a`.  The entries
have to be kept, and the block structure of `E_a` used: each factor is supported in one
block of `W^d` sites and carries `W^{-d}`, so summing over an internal vertex is an
*average*, not a sum.  That is the invariant below.
-/

/-- One factor: `(G E_a)_{xz} = G_{xz} W^{-d} 1(z ∈ [a])`. -/
theorem gsigEblk_apply (ω : Omega d L W) (E t : ℝ) (σ : Bool) (a : Zd d L)
    (x z : Vtx d L W) :
    (Gsig d L W ω E t σ * Eblk d L W a) x z
      = Gsig d L W ω E t σ x z * (if z.1 = a then ((W : ℂ) ^ d)⁻¹ else 0) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single z (fun b _ hb => by simp [Eblk_apply, hb])
    (fun h => absurd (Finset.mem_univ z) h)]
  simp [Eblk_apply]

/-- The entries of `G_t(σ)` are bounded by `η_t^{-1}`, on the whole space. -/
theorem norm_Gsig_entry_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (σ : Bool) (x z : Vtx d L W) :
    ‖Gsig d L W ω E t σ x z‖ ≤ (etaT E t)⁻¹ := by
  have hpos : 0 < etaT E t := etaT_pos hE ht
  set w : ℂ := if σ then zt E t else (starRingEnd ℂ) (zt E t) with hw
  have hwim : w.im = if σ then (zt E t).im else -(zt E t).im := by
    cases σ with
    | false => simp [hw, Complex.conj_im]
    | true => simp [hw]
  have habs : |w.im| = etaT E t := by
    rw [hwim, ← etaT_eq_zt_im]
    cases σ with
    | false => simp [abs_of_pos hpos]
    | true => simp [abs_of_pos hpos]
  have hzim : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    exact absurd habs.symm (ne_of_gt hpos)
  have := norm_inverse_entry_le (Hmat_isHermitian d L W ω) hzim x z
  rwa [habs] at this

/-- **The invariant.**  A product of factors `G_i E_{a_i}`, with the last one indexed by
`a`, has entries at most `W^{-d} η^{-k}` and is supported in the block `[a]`:

`|(Π_{i<k} G_i E_{a_i})_{xz}| ≤ W^{-d} η^{-k} · 1(z ∈ [a])`.

Each step sums over a block of `W^d` sites and carries `W^{-d}`, so it is an **average**;
that is what keeps the bound from growing with the volume. -/
theorem norm_prod_entry_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1)
    (b : Bool) (a : Zd d L) :
    ∀ (l : List (Bool × Zd d L)) (x z : Vtx d L W),
      ‖((l.map fun p => Gsig d L W ω E t p.1 * Eblk d L W p.2)
          ++ [Gsig d L W ω E t b * Eblk d L W a]).prod x z‖
        ≤ (((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (l.length + 1))
          * (if z.1 = a then 1 else 0) := by
  have hpos : 0 < etaT E t := etaT_pos hE ht
  have hWpos : (0 : ℝ) < (W : ℝ) ^ d ∨ (W : ℝ) ^ d = 0 := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (W : ℝ) ^ d) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  intro l
  induction l with
  | nil =>
    intro x z
    simp only [List.map_nil, List.nil_append, List.prod_singleton, List.length_nil,
      gsigEblk_apply, norm_mul]
    by_cases hz : z.1 = a
    · have h1 := norm_Gsig_entry_le d L W ω hE ht b x z
      have hWn : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
      simp only [hz, ite_true, mul_one, norm_inv, hWn, zero_add, pow_one]
      calc ‖Gsig d L W ω E t b x z‖ * ((W : ℝ) ^ d)⁻¹
          ≤ (etaT E t)⁻¹ * ((W : ℝ) ^ d)⁻¹ :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ := by ring
    · simp [hz]
  | cons p tl ih =>
    intro x z
    have hstep : ((((p :: tl).map fun q => Gsig d L W ω E t q.1 * Eblk d L W q.2)
        ++ [Gsig d L W ω E t b * Eblk d L W a]).prod) x z
        = ∑ y : Vtx d L W,
            (Gsig d L W ω E t p.1 * Eblk d L W p.2) x y
            * (((tl.map fun q => Gsig d L W ω E t q.1 * Eblk d L W q.2)
                ++ [Gsig d L W ω E t b * Eblk d L W a]).prod) y z := by
      simp only [List.map_cons, List.cons_append, List.prod_cons]
      rw [Matrix.mul_apply]
    rw [hstep]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ y : Vtx d L W,
        ‖(Gsig d L W ω E t p.1 * Eblk d L W p.2) x y
          * (((tl.map fun q => Gsig d L W ω E t q.1 * Eblk d L W q.2)
              ++ [Gsig d L W ω E t b * Eblk d L W a]).prod) y z‖
          ≤ ((etaT E t)⁻¹ * ((W : ℝ) ^ d)⁻¹ * (if y.1 = p.2 then 1 else 0))
            * ((((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (tl.length + 1))
              * (if z.1 = a then 1 else 0)) := by
      intro y
      rw [norm_mul]
      refine mul_le_mul ?_ (ih y z) (norm_nonneg _) (by positivity)
      rw [gsigEblk_apply, norm_mul]
      by_cases hy : y.1 = p.2
      · have h1 := norm_Gsig_entry_le d L W ω hE ht p.1 x y
        have hWn : ‖((W : ℂ) ^ d)‖ = (W : ℝ) ^ d := by simp
        simp only [hy, ite_true, mul_one, norm_inv, hWn]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      · simp [hy]
    refine le_trans (Finset.sum_le_sum fun y _ => hterm y) ?_
    have hcount : ∑ y : Vtx d L W, (if y.1 = p.2 then (1 : ℝ) else 0) = (W : ℝ) ^ d := by
      rw [Fintype.sum_prod_type]
      simp [apply_ite Finset.card, Finset.sum_ite_eq', Fintype.card_fin]
    have hrw : ∀ y : Vtx d L W,
        ((etaT E t)⁻¹ * ((W : ℝ) ^ d)⁻¹ * (if y.1 = p.2 then 1 else 0))
          * ((((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (tl.length + 1))
            * (if z.1 = a then 1 else 0))
        = ((etaT E t)⁻¹ * ((W : ℝ) ^ d)⁻¹ * (((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (tl.length + 1))
            * (if z.1 = a then 1 else 0)) * (if y.1 = p.2 then 1 else 0) := by
      intro y; ring
    simp only [hrw]
    rw [← Finset.mul_sum, hcount]
    have hfinal : (etaT E t)⁻¹ * ((W : ℝ) ^ d)⁻¹
          * (((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (tl.length + 1))
          * (if z.1 = a then 1 else 0) * (W : ℝ) ^ d
        = ((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ ((p :: tl).length + 1)
          * (if z.1 = a then 1 else 0) := by
      rcases hWpos with hW | hW
      · have hη : etaT E t ≠ 0 := ne_of_gt hpos
        have hWne : ((W : ℝ) ^ d) ≠ 0 := ne_of_gt hW
        rw [List.length_cons]
        have hpow : (etaT E t)⁻¹ ^ (tl.length + 1 + 1)
            = (etaT E t)⁻¹ * (etaT E t)⁻¹ ^ (tl.length + 1) := by
          rw [pow_succ']
        rw [hpow]
        field_simp
      · rw [hW]
        simp
    rw [hfinal]

/-- **`(5.2)`, the deterministic envelope of a `G`-loop**: `|L^(n)| ≤ (η_t^{-1})^n`,
pointwise in `ω` and with no exceptional set. -/
theorem norm_gloop_le (ω : Omega d L W) {E t : ℝ} (hE : |E| < 2) (ht : t < 1) {n : ℕ}
    (σ : Fin (n + 1) → Bool) (a : Fin (n + 1) → Zd d L) :
    ‖gloop d L W ω E t σ a‖ ≤ (etaT E t)⁻¹ ^ (n + 1) := by
  have hpos : 0 < etaT E t := etaT_pos hE ht
  -- split off the last factor
  set l : List (Bool × Zd d L) :=
    List.ofFn fun i : Fin n => (σ i.castSucc, a i.castSucc) with hl
  have hsplit : (List.ofFn fun i : Fin (n + 1) => (σ i, a i))
      = l ++ [(σ (Fin.last n), a (Fin.last n))] := by
    rw [hl, List.ofFn_succ' (fun i : Fin (n + 1) => (σ i, a i)), List.concat_eq_append]
  have hmap : (List.ofFn fun i : Fin (n + 1) =>
        Gsig d L W ω E t (σ i) * Eblk d L W (a i))
      = (l.map fun p => Gsig d L W ω E t p.1 * Eblk d L W p.2)
        ++ [Gsig d L W ω E t (σ (Fin.last n)) * Eblk d L W (a (Fin.last n))] := by
    rw [show (List.ofFn fun i : Fin (n + 1) => Gsig d L W ω E t (σ i) * Eblk d L W (a i))
        = ((List.ofFn fun i : Fin (n + 1) => (σ i, a i)).map
          fun p => Gsig d L W ω E t p.1 * Eblk d L W p.2) from by
      rw [List.map_ofFn]; rfl]
    rw [hsplit, List.map_append, List.map_singleton]
  have hlen : l.length = n := by rw [hl, List.length_ofFn]
  rw [gloop, hmap, Matrix.trace]
  refine le_trans (norm_sum_le _ _) ?_
  have hbd : ∀ x : Vtx d L W,
      ‖((l.map fun p => Gsig d L W ω E t p.1 * Eblk d L W p.2)
        ++ [Gsig d L W ω E t (σ (Fin.last n)) * Eblk d L W (a (Fin.last n))]).prod
          x x‖
        ≤ (((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (n + 1))
          * (if x.1 = a (Fin.last n) then 1 else 0) := by
    intro x
    have := norm_prod_entry_le d L W ω hE ht (σ (Fin.last n)) (a (Fin.last n)) l x x
    rwa [hlen] at this
  refine le_trans (Finset.sum_le_sum fun x _ => hbd x) ?_
  rw [← Finset.mul_sum]
  have hcount : ∑ x : Vtx d L W, (if x.1 = a (Fin.last n) then (1 : ℝ) else 0)
      = (W : ℝ) ^ d := by
    rw [Fintype.sum_prod_type]
    simp [apply_ite Finset.card, Finset.sum_ite_eq', Fintype.card_fin]
  rw [hcount]
  have hWdich : (0 : ℝ) < (W : ℝ) ^ d ∨ (W : ℝ) ^ d = 0 := by
    rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ (W : ℝ) ^ d) with h | h
    · exact Or.inr h.symm
    · exact Or.inl h
  rcases hWdich with hW | hW
  · have : ((W : ℝ) ^ d)⁻¹ * (etaT E t)⁻¹ ^ (n + 1) * (W : ℝ) ^ d
        = (etaT E t)⁻¹ ^ (n + 1) := by
      field_simp
    rw [this]
  · rw [hW]
    simp only [_root_.inv_zero, inv_pow, zero_mul, mul_zero, inv_nonneg, ge_iff_le]
    positivity

end RBM.Gauss


