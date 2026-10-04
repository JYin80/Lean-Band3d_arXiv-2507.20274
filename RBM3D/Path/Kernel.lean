/-
Copyright (c) 2026 Jun Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Yin
-/
import RBM3D.Propagator.Props4

/-!
# The kernel `𝒰_{v,w}` on two-index tensors and the Duhamel telescope (`d ≥ 3`)

Ticket T2085 (ST2-24, part 1).  Port of `RBM2D/Path/Kernel.lean` at commit `c9a24cf` (cited
`Kernel:<line>`; itself a port of RBM1D `RBM1D/Gauss/GridDuhamel.lean:47`, `:101`, `:117`, `:127`,
`:148` and `RBM1D/Hierarchy/Kernel.lean:102-333`, commit `86573b9`).  Paper: arXiv:2507.20274,
`def_Ustz`.

Renaming (`docs/tickets/ST1-COMMON.md` item 2): `Z2 L` becomes `Zd d L`; the propagator
`Theta L`, `SB L` of RBM2D become `Theta d L g`, `SB d L g` with the coupling `g` an explicit real
parameter, so `ukerMat` carries `(d, L, g)` (for the model, `g = sz.lam n`).  The structural facts
`mul_Theta`, `Theta_commute_SB`, `Theta_commute` are the merged `*_of_three_le` forms of
`RBM3D/Propagator/Props4.lean`, which discharge `‖SB d L g‖ = 1` from `3 ≤ L`.

* `ukerMat`, `Uop`, `UopSemigroup`, `uopSemigroup` : `Kernel:45`, `:50`, `:58`, `:163`.
* `ukerMat_mul`, `ukerMat_self`, `Uop_add`, `Uop_smul`, `Uop_self`, `Uop_comp`, `UopHom`.
* `duhamel_telescope`, `duhamel_telescope_stopped` : the abstract discrete Duhamel telescope.
* `Uop_grid_semigroup`, `Uop_factor`, `Uop_duhamel_telescope`, `Uop_duhamel_telescope_stopped`.

`d` enters only through `Theta d L g` and `SB d L g`; no closed form of `Θ` is used.  The dimension
and the coupling are free (`3 ≤ L` is the only constraint, as in every RBM2D statement).  The
compile checks at the end of the file are at `d = 3`, `L = 3`.
-/

set_option linter.style.longLine false

noncomputable section

namespace RBM.Path

open Matrix

section Kernel

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- The one-index kernel `(1 - v ξ S^{(B)}) Θ^{(B)}_{w ξ}` of `𝒰_{v,w}` (`def_Ustz`;
`Kernel:45`). -/
def ukerMat (ξ : ℂ) (v w : ℝ) : Matrix (Zd d L) (Zd d L) ℂ :=
  (1 - ((v : ℂ) * ξ) • SB d L g) * Theta d L g ((w : ℂ) * ξ)

/-- `𝒰_{v,w,(+,-)}` on two-index tensors (`def_Ustz`); for `σ = (+,-)` both slots
carry `m_i m_{i+1} = |m|²` (`Kernel:50`). -/
def Uop (ξ : ℂ) (v w : ℝ) (A : Zd d L × Zd d L → ℂ) : Zd d L × Zd d L → ℂ :=
  fun a => ∑ b : Zd d L × Zd d L, ukerMat d L g ξ v w a.1 b.1 * ukerMat d L g ξ v w a.2 b.2 * A b

/-- **Pin (semigroup)**: `𝒰_{v,w} ∘ 𝒰_{u,v} = 𝒰_{u,w}` and `𝒰_{u,u} = id` for `|ξ| ≤ 1`,
`0 ≤ u ≤ v ≤ w < 1` (`Kernel:58`; RBM1D `Uker_grid_semigroup`). -/
def UopSemigroup : Prop :=
  3 ≤ L → ∀ (ξ : ℂ), ‖ξ‖ ≤ 1 → ∀ u v w : ℝ, 0 ≤ u → u ≤ v → v ≤ w → w < 1 →
    (∀ A, Uop d L g ξ v w (Uop d L g ξ u v A) = Uop d L g ξ u w A) ∧
      (∀ A, Uop d L g ξ u u A = A)

end Kernel

section KernelLemmas

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- `‖(v : ℂ) ξ‖ < 1` from `‖ξ‖ ≤ 1` and `0 ≤ v < 1`. -/
private theorem Kernel_norm_ofReal_mul_lt_one {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) {v : ℝ} (h0 : 0 ≤ v)
    (h1 : v < 1) : ‖(v : ℂ) * ξ‖ < 1 := by
  rw [norm_mul, Complex.norm_of_nonneg h0]
  calc v * ‖ξ‖ ≤ v * 1 := mul_le_mul_of_nonneg_left hξ h0
    _ = v := mul_one v
    _ < 1 := h1

/-- The one-index kernels compose (`Kernel:72`; port of RBM1D `edgeKer_mul`,
`Hierarchy/Kernel.lean:149`): `(1 - vξS) Θ_{wξ} (1 - uξS) Θ_{vξ} = (1 - uξS) Θ_{wξ}`. -/
theorem ukerMat_mul (hL : 3 ≤ L) {ξ : ℂ} {u v w : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (hw : ‖(w : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v w * ukerMat d L g ξ u v = ukerMat d L g ξ u w := by
  set P : Matrix (Zd d L) (Zd d L) ℂ := 1 - ((u : ℂ) * ξ) • SB d L g with hP
  set Q : Matrix (Zd d L) (Zd d L) ℂ := 1 - ((v : ℂ) * ξ) • SB d L g with hQ
  set Tw : Matrix (Zd d L) (Zd d L) ℂ := Theta d L g ((w : ℂ) * ξ) with hTw
  set Tv : Matrix (Zd d L) (Zd d L) ℂ := Theta d L g ((v : ℂ) * ξ) with hTv
  have h1 : Commute Tw P :=
    (Commute.one_right Tw).sub_right
      ((Theta_commute_SB_of_three_le (g := g) hL hw).smul_right ((u : ℂ) * ξ))
  have h2 : Commute Q P :=
    (Commute.one_left P).sub_left
      ((Commute.one_right (((v : ℂ) * ξ) • SB d L g)).sub_right
        (((Commute.refl (SB d L g)).smul_left ((v : ℂ) * ξ)).smul_right ((u : ℂ) * ξ)))
  have h3 : Commute Tw Tv := Theta_commute_of_three_le (g := g) hL hw hv
  have h4 : Q * Tv = 1 := mul_Theta_of_three_le (g := g) hL hv
  calc ukerMat d L g ξ v w * ukerMat d L g ξ u v = Q * Tw * (P * Tv) := rfl
    _ = Q * (Tw * P) * Tv := by noncomm_ring
    _ = Q * (P * Tw) * Tv := by rw [h1.eq]
    _ = (Q * P) * (Tw * Tv) := by noncomm_ring
    _ = (P * Q) * (Tv * Tw) := by rw [h2.eq, h3.eq]
    _ = P * (Q * Tv) * Tw := by noncomm_ring
    _ = P * Tw := by rw [h4, Matrix.mul_one]

/-- At equal times the one-index kernel is the identity (`Kernel:93`; port of RBM1D `edgeKer_self`,
`Hierarchy/Kernel.lean:120`). -/
theorem ukerMat_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1) :
    ukerMat d L g ξ v v = 1 :=
  mul_Theta_of_three_le (g := g) hL hv

/-- `𝒰_{v,w}` is additive (`Kernel:98`; port of RBM1D `Uker_add`, `Hierarchy/Kernel.lean:241`). -/
theorem Uop_add (ξ : ℂ) (v w : ℝ) (A B : Zd d L × Zd d L → ℂ) :
    Uop d L g ξ v w (A + B) = Uop d L g ξ v w A + Uop d L g ξ v w B := by
  funext a
  simp only [Uop, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- `𝒰_{v,w}` is homogeneous (`Kernel:105`; port of RBM1D `Uker_smul`,
`Hierarchy/Kernel.lean:247`). -/
theorem Uop_smul (ξ : ℂ) (v w : ℝ) (c : ℂ) (A : Zd d L × Zd d L → ℂ) :
    Uop d L g ξ v w (c • A) = c • Uop d L g ξ v w A := by
  funext a
  simp only [Uop, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- At equal times `𝒰_{v,v} = id` (`Kernel:112`; port of RBM1D `Uker_self`,
`Hierarchy/Kernel.lean:282`). -/
theorem Uop_self (hL : 3 ≤ L) {ξ : ℂ} {v : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (A : Zd d L × Zd d L → ℂ) : Uop d L g ξ v v A = A := by
  funext a
  obtain ⟨a₁, a₂⟩ := a
  simp only [Uop, ukerMat_self d L g hL hv, Matrix.one_apply, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_prod_type]
  simp

/-- **Semigroup law** `𝒰_{v,w} ∘ 𝒰_{u,v} = 𝒰_{u,w}` on two-index tensors (`Kernel:121`; port of
RBM1D `Uker_comp`, `Hierarchy/Kernel.lean:306`, with `n = 2` and the same kernel in both slots). -/
theorem Uop_comp (hL : 3 ≤ L) {ξ : ℂ} {u v w : ℝ} (hv : ‖(v : ℂ) * ξ‖ < 1)
    (hw : ‖(w : ℂ) * ξ‖ < 1) (A : Zd d L × Zd d L → ℂ) :
    Uop d L g ξ v w (Uop d L g ξ u v A) = Uop d L g ξ u w A := by
  funext a
  calc Uop d L g ξ v w (Uop d L g ξ u v A) a
      = ∑ c : Zd d L × Zd d L, ukerMat d L g ξ v w a.1 c.1 * ukerMat d L g ξ v w a.2 c.2 *
          ∑ b : Zd d L × Zd d L, ukerMat d L g ξ u v c.1 b.1 * ukerMat d L g ξ u v c.2 b.2 * A b :=
        rfl
    _ = ∑ c : Zd d L × Zd d L, ∑ b : Zd d L × Zd d L,
          (ukerMat d L g ξ v w a.1 c.1 * ukerMat d L g ξ u v c.1 b.1) *
            (ukerMat d L g ξ v w a.2 c.2 * ukerMat d L g ξ u v c.2 b.2) * A b := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ b : Zd d L × Zd d L, ∑ c : Zd d L × Zd d L,
          (ukerMat d L g ξ v w a.1 c.1 * ukerMat d L g ξ u v c.1 b.1) *
            (ukerMat d L g ξ v w a.2 c.2 * ukerMat d L g ξ u v c.2 b.2) * A b :=
        Finset.sum_comm
    _ = ∑ b : Zd d L × Zd d L, ukerMat d L g ξ u w a.1 b.1 * ukerMat d L g ξ u w a.2 b.2 * A b := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have hm : ∀ x y : Zd d L, ∑ c : Zd d L, ukerMat d L g ξ v w x c * ukerMat d L g ξ u v c y
            = ukerMat d L g ξ u w x y := fun x y => by
          have h := congrFun (congrFun (ukerMat_mul d L g (u := u) hL hv hw) x) y
          rwa [Matrix.mul_apply] at h
        rw [← Finset.sum_mul, Fintype.sum_prod_type, ← hm a.1 b.1, ← hm a.2 b.2,
          Finset.sum_mul_sum]
    _ = Uop d L g ξ u w A a := rfl

/-- `𝒰_{v,w}` bundled as an `AddMonoidHom` (`Kernel:152`; port of RBM1D `UkerHom`,
`Gauss/GridDuhamel.lean:117`). -/
def UopHom (ξ : ℂ) (v w : ℝ) : (Zd d L × Zd d L → ℂ) →+ (Zd d L × Zd d L → ℂ) :=
  AddMonoidHom.mk' (Uop d L g ξ v w) (Uop_add d L g ξ v w)

@[simp] theorem UopHom_apply (ξ : ℂ) (v w : ℝ) (A : Zd d L × Zd d L → ℂ) :
    UopHom d L g ξ v w A = Uop d L g ξ v w A := rfl

end KernelLemmas

/-- **Pin**: the semigroup law `UopSemigroup` holds (`Kernel:163`). -/
theorem uopSemigroup (d L : ℕ) [NeZero L] (g : ℝ) : UopSemigroup d L g := by
  intro hL ξ hξ u v w hu huv hvw hw
  have hv0 : 0 ≤ v := le_trans hu huv
  have hw0 : 0 ≤ w := le_trans hv0 hvw
  have hv1 : v < 1 := lt_of_le_of_lt hvw hw
  have hu1 : u < 1 := lt_of_le_of_lt huv hv1
  refine ⟨fun A => ?_, fun A => ?_⟩
  · exact Uop_comp d L g hL (Kernel_norm_ofReal_mul_lt_one hξ hv0 hv1)
      (Kernel_norm_ofReal_mul_lt_one hξ hw0 hw) A
  · exact Uop_self d L g hL (Kernel_norm_ofReal_mul_lt_one hξ hu hu1) A

section Telescope

variable {V : Type*} [AddCommGroup V]

-- Ported verbatim from RBM1D `RBM1D/Gauss/GridDuhamel.lean:47` (commit `86573b9`).
/-- **(T1)**: the discrete Duhamel telescoping identity.  For a family `U j k : V →+ V`
satisfying the evolution-kernel laws `U k k = id` and `(U j k).comp (U i j) = U i k`
for `i ≤ j ≤ k`, and any sequence `A : ℕ → V`,
`A k - U 0 k (A 0) = ∑_{j < k} U (j+1) k (A (j+1) - U j (j+1) (A j))` (`Kernel:176`). -/
theorem duhamel_telescope (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (k : ℕ) :
    A k - U 0 k (A 0) =
      ∑ j ∈ Finset.range k, U (j + 1) k (A (j + 1) - U j (j + 1) (A j)) := by
  induction k with
  | zero =>
      have h0 : U 0 0 (A 0) = A 0 := by rw [hself 0]; rfl
      simp [h0]
  | succ k ih =>
      have hrw : ∀ j ∈ Finset.range k,
          U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
            = U k (k + 1) (U (j + 1) k (A (j + 1) - U j (j + 1) (A j))) := by
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hcomp' := hcomp (j + 1) k (k + 1) hjk (Nat.le_succ k)
        rw [← hcomp']
        rfl
      have hsum : ∑ j ∈ Finset.range k, U (j + 1) (k + 1) (A (j + 1) - U j (j + 1) (A j))
          = U k (k + 1) (A k - U 0 k (A 0)) := by
        rw [ih]
        rw [map_sum (U k (k+1))]
        exact Finset.sum_congr rfl (fun j hj => hrw j hj)
      have htail : U (k + 1) (k + 1) (A (k + 1) - U k (k + 1) (A k))
          = A (k + 1) - U k (k + 1) (A k) := by rw [hself (k+1)]; rfl
      have hfront : U k (k + 1) (A k - U 0 k (A 0))
          = U k (k + 1) (A k) - U 0 (k + 1) (A 0) := by
        rw [map_sub]
        have := hcomp 0 k (k + 1) (Nat.zero_le k) (Nat.le_succ k)
        rw [show U k (k+1) (U 0 k (A 0)) = (U k (k+1)).comp (U 0 k) (A 0) from rfl, this]
      rw [Finset.sum_range_succ, hsum, hfront, htail]
      abel

end Telescope

section Stopped

variable {V : Type*} [AddCommGroup V]

-- Ported verbatim from RBM1D `RBM1D/Gauss/GridDuhamel.lean:101` (commit `86573b9`).
/-- **(T2)**: the stopped version of (T1), a pointwise (per `ω`) corollary: the identity holds
with `k` replaced by `min k (τ ω)` for any `τ : Ω' → ℕ` (`Kernel:211`). -/
theorem duhamel_telescope_stopped {Ω' : Type*} (U : ℕ → ℕ → V →+ V)
    (hself : ∀ k, U k k = AddMonoidHom.id V)
    (hcomp : ∀ i j k, i ≤ j → j ≤ k → (U j k).comp (U i j) = U i k)
    (A : ℕ → V) (τ : Ω' → ℕ) (ω : Ω') (k : ℕ) :
    A (min k (τ ω)) - U 0 (min k (τ ω)) (A 0) =
      ∑ j ∈ Finset.range (min k (τ ω)),
        U (j + 1) (min k (τ ω)) (A (j + 1) - U j (j + 1) (A j)) :=
  duhamel_telescope U hself hcomp A (min k (τ ω))

end Stopped

section UopGrid

variable (d L : ℕ) [NeZero L] (g : ℝ)

/-- **(T3)** for `Uop`: the family `fun j k => UopHom ξ (u j) (u k)` satisfies the hypotheses
of `duhamel_telescope` (`Kernel:226`; port of RBM1D `Uker_grid_semigroup`,
`Gauss/GridDuhamel.lean:127`; the hypothesis `‖u k * ξ i‖ < 1` there is re-derived from
`‖ξ‖ ≤ 1`, `0 ≤ u k < 1`). -/
theorem Uop_grid_semigroup (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (u : ℕ → ℝ)
    (hu0 : ∀ k, 0 ≤ u k) (hu1 : ∀ k, u k < 1) :
    (∀ k, UopHom d L g ξ (u k) (u k) = AddMonoidHom.id (Zd d L × Zd d L → ℂ)) ∧
      (∀ i j k, i ≤ j → j ≤ k →
        (UopHom d L g ξ (u j) (u k)).comp (UopHom d L g ξ (u i) (u j))
          = UopHom d L g ξ (u i) (u k)) := by
  have hu : ∀ k, ‖(u k : ℂ) * ξ‖ < 1 := fun k =>
    Kernel_norm_ofReal_mul_lt_one hξ (hu0 k) (hu1 k)
  constructor
  · intro k
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.id_apply, UopHom_apply]
    exact Uop_self d L g hL (hu k) A
  · intro i j k _ _
    apply AddMonoidHom.ext
    intro A
    rw [AddMonoidHom.comp_apply, UopHom_apply, UopHom_apply, UopHom_apply]
    exact Uop_comp d L g hL (hu j) (hu k) A

/-- **(T4)** for `Uop`: `𝒰_{u_k,t} ∘ 𝒰_{u_{j+1},u_k} = 𝒰_{u_{j+1},t}`, and `𝒰_{u_k,t}` is
two-sided invertible with inverse `𝒰_{t,u_k}` (`Kernel:248`; port of RBM1D `Uker_factor`,
`Gauss/GridDuhamel.lean:148`). -/
theorem Uop_factor (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1) (u : ℕ → ℝ) (t : ℝ) (j k : ℕ)
    (hu : 0 ≤ u k ∧ u k < 1) (ht : 0 ≤ t ∧ t < 1) (A : Zd d L × Zd d L → ℂ) :
    Uop d L g ξ (u k) t (Uop d L g ξ (u (j + 1)) (u k) A) = Uop d L g ξ (u (j + 1)) t A ∧
      (∀ B, Uop d L g ξ (u k) t (Uop d L g ξ t (u k) B) = B) ∧
      (∀ B, Uop d L g ξ t (u k) (Uop d L g ξ (u k) t B) = B) := by
  have hu' := Kernel_norm_ofReal_mul_lt_one hξ hu.1 hu.2
  have ht' := Kernel_norm_ofReal_mul_lt_one hξ ht.1 ht.2
  refine ⟨Uop_comp d L g hL hu' ht' A, fun B => ?_, fun B => ?_⟩
  · rw [Uop_comp d L g hL hu' ht' B, Uop_self d L g hL ht' B]
  · rw [Uop_comp d L g hL ht' hu' B, Uop_self d L g hL hu' B]

/-- **The algebraic part of (105)** (`int_K-L_ST`) in `Uop` form (`Kernel:263`):
`A_m = 𝒰_{u_0,u_m} A_0 + Σ_{j<m} 𝒰_{u_{j+1},u_m} (A_{j+1} - 𝒰_{u_j,u_{j+1}} A_j)`,
for grid times with `0 ≤ u_j < 1` at the indices `j ≤ m`. -/
theorem Uop_duhamel_telescope (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    (u : ℕ → ℝ) (m : ℕ) (hu0 : ∀ j ≤ m, 0 ≤ u j) (hu1 : ∀ j ≤ m, u j < 1)
    (A : ℕ → (Zd d L × Zd d L → ℂ)) :
    A m = Uop d L g ξ (u 0) (u m) (A 0) +
      ∑ j ∈ Finset.range m, Uop d L g ξ (u (j + 1)) (u m)
        (A (j + 1) - Uop d L g ξ (u j) (u (j + 1)) (A j)) := by
  have hsg := Uop_grid_semigroup d L g hL hξ (fun j => u (min j m))
    (fun j => hu0 _ (min_le_right j m)) (fun j => hu1 _ (min_le_right j m))
  have htel := duhamel_telescope
    (fun i j => UopHom d L g ξ (u (min i m)) (u (min j m))) hsg.1 hsg.2 A m
  simp only [UopHom_apply] at htel
  rw [Nat.zero_min, min_self, sub_eq_iff_eq_add'] at htel
  rw [htel, add_right_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : j + 1 ≤ m := Finset.mem_range.mp hj
  rw [min_eq_left hj1, min_eq_left (Nat.le_of_succ_le hj1)]

/-- The stopped form of `Uop_duhamel_telescope`: the identity at `m := min k (τ ω)` for any
`τ : Ω' → ℕ` (`Kernel:285`; as RBM1D `duhamel_telescope_stopped`). -/
theorem Uop_duhamel_telescope_stopped (hL : 3 ≤ L) {ξ : ℂ} (hξ : ‖ξ‖ ≤ 1)
    {Ω' : Type*} (u : ℕ → ℝ) (τ : Ω' → ℕ) (ω : Ω') (k : ℕ)
    (hu0 : ∀ j ≤ min k (τ ω), 0 ≤ u j) (hu1 : ∀ j ≤ min k (τ ω), u j < 1)
    (A : ℕ → (Zd d L × Zd d L → ℂ)) :
    A (min k (τ ω)) = Uop d L g ξ (u 0) (u (min k (τ ω))) (A 0) +
      ∑ j ∈ Finset.range (min k (τ ω)), Uop d L g ξ (u (j + 1)) (u (min k (τ ω)))
        (A (j + 1) - Uop d L g ξ (u j) (u (j + 1)) (A j)) :=
  Uop_duhamel_telescope d L g hL hξ u (min k (τ ω)) hu0 hu1 A

end UopGrid

/-! ### Compile checks at `d = 3`, `L = 3`, `g = 1/2` (ST1-COMMON item 7) -/

/-- Check: `uopSemigroup` at `d = 3`, `L = 3`, `g = 1/2`. -/
example : UopSemigroup 3 3 (1 / 2) := uopSemigroup 3 3 (1 / 2)

/-- Check: the semigroup law and the identity at equal times, applied at `d = 3`, `L = 3`,
`ξ = 1`, `(u, v, w) = (1/4, 1/2, 3/4)`, for an arbitrary tensor `A` (all hypotheses discharged). -/
example (A : Zd 3 3 × Zd 3 3 → ℂ) :
    Uop 3 3 (1 / 2) 1 (1 / 2) (3 / 4) (Uop 3 3 (1 / 2) 1 (1 / 4) (1 / 2) A)
        = Uop 3 3 (1 / 2) 1 (1 / 4) (3 / 4) A ∧
      Uop 3 3 (1 / 2) 1 (1 / 4) (1 / 4) A = A :=
  uopSemigroup 3 3 (1 / 2) (le_refl 3) 1 (by simp) (1 / 4) (1 / 2) (3 / 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) |>.imp (fun h => h A) (fun h => h A)

/-- Check: `Uop_duhamel_telescope` at `d = 3`, `L = 3`, `g = 1/2`, `ξ = 1`, `u j = j / (j + 2)`. -/
example (A : ℕ → (Zd 3 3 × Zd 3 3 → ℂ)) (m : ℕ) :
    A m = Uop 3 3 (1 / 2) 1 ((0 : ℕ) / ((0 : ℕ) + 2 : ℝ)) ((m : ℝ) / ((m : ℝ) + 2)) (A 0) +
      ∑ j ∈ Finset.range m, Uop 3 3 (1 / 2) 1 (((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 2))
        ((m : ℝ) / ((m : ℝ) + 2))
        (A (j + 1) - Uop 3 3 (1 / 2) 1 ((j : ℝ) / ((j : ℝ) + 2))
          (((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 2)) (A j)) :=
  Uop_duhamel_telescope 3 3 (1 / 2) (le_refl 3) (by simp) (fun j => (j : ℝ) / ((j : ℝ) + 2)) m
    (fun j _ => by positivity)
    (fun j _ => by rw [div_lt_one (by positivity)]; linarith)
    A

/-- Check: the stopped telescope at `d = 3`, `L = 3`, with a stopping time `τ`. -/
example {Ω' : Type*} (τ : Ω' → ℕ) (ω : Ω') (k : ℕ) (A : ℕ → (Zd 3 3 × Zd 3 3 → ℂ)) :
    A (min k (τ ω)) =
      Uop 3 3 (1 / 2) 1 ((0 : ℕ) / ((0 : ℕ) + 2 : ℝ))
        (((min k (τ ω) : ℕ) : ℝ) / (((min k (τ ω) : ℕ) : ℝ) + 2)) (A 0) +
      ∑ j ∈ Finset.range (min k (τ ω)),
        Uop 3 3 (1 / 2) 1 (((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 2))
          (((min k (τ ω) : ℕ) : ℝ) / (((min k (τ ω) : ℕ) : ℝ) + 2))
          (A (j + 1) - Uop 3 3 (1 / 2) 1 ((j : ℝ) / ((j : ℝ) + 2))
            (((j + 1 : ℕ) : ℝ) / (((j + 1 : ℕ) : ℝ) + 2)) (A j)) :=
  Uop_duhamel_telescope_stopped 3 3 (1 / 2) (le_refl 3) (by simp)
    (fun j => (j : ℝ) / ((j : ℝ) + 2)) τ ω k
    (fun j _ => by positivity)
    (fun j _ => by rw [div_lt_one (by positivity)]; linarith)
    A

/-- Check: `ukerMat_self` and `ukerMat_mul` at `d = 3`, `L = 3`, `ξ = 1`. -/
example : ukerMat 3 3 (1 / 2) 1 (1 / 4) (1 / 4) = 1 :=
  ukerMat_self 3 3 (1 / 2) (le_refl 3) (by norm_num)

example : ukerMat 3 3 (1 / 2) 1 (1 / 2) (3 / 4) * ukerMat 3 3 (1 / 2) 1 (1 / 4) (1 / 2)
    = ukerMat 3 3 (1 / 2) 1 (1 / 4) (3 / 4) :=
  ukerMat_mul 3 3 (1 / 2) (le_refl 3) (by norm_num) (by norm_num)

end RBM.Path

end
