/-
Release check for T2249 (dispatcher V1, Tue Oct  6 03:08 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §81 (2)-(4), §73,
§76, §64 (4), §45 O2, §29, §20, §17, §16; supervisor `docs/supervisor/2026-10-06-0255.md` §2.2 route (d) step 1,
"(c) is needed in every option", §2.3, O3).
S6-09c (stochastic layer ST-5, deterministic, public, generic in the tensor order): the derivative decay of the explicit
mollifier `QopAlgebra_mollifier` (paper-delta T2239a = D556) and the propagation of `(deccA0)` (`EKFastDecay`) through
`Θ^{(n)}_{u}` (`ThetaN`, `STthetaOp`).  New file `RBM3D/Induction/QopDecay.lean`.
Section 1: the merged names the proof uses (exact namespaces, from the enclosing `namespace … end` blocks; file and last
commit on `main` b35643d).
Section 2: the statements of the public theorems of `QopDecay.lean` as closed `Prop`s, in the temporary namespace
`RBM.Gauss.Sizes.T2249Check` (T2249 proves each under the same name in `RBM.Gauss.Sizes`).
No instance section: the five targets are deterministic theorems with no `Prop`-pin hypothesis.
Statements and `#check` only: no theorem, no proof term, no proof placeholder.  Never imported or merged.
Imports: merged modules only, not `RBM3D`.  No Mathlib lemma is `#check`ed.
Run from the main worktree: `lake env lean docs/tickets/checks/T2249-check.lean`.
-/
import RBM3D.Induction.QopNorm
import RBM3D.Induction.B45
import RBM3D.Induction.Step2Iterate
import RBM3D.Induction.Step6Pins
import RBM3D.Propagator.Prop6Hold

/-! ## 1. Merged names -/

-- `RBM3D/Induction/QopAlgebra.lean` (6b2494e; S3-04 = T2055): the mollifier (public part; the helpers
-- `qaZ1` … `qa_deriv_real`, `:40-505`, are private and are copied, see the ticket)
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_sum
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_props
#check @RBM.Gauss.Sizes.stMollifierEx_holds
#check @RBM.Gauss.Sizes.QopAlgebra_mollifier_differentiableAt
#check @RBM.Gauss.Sizes.QopAlgebra_ThetaN_sumZero

-- `RBM3D/Induction/QopNorm.lean` (eb6d67a; S3-05 = T2059): the decay clause (pattern for targets 2, 3)
#check @RBM.Gauss.Sizes.stQop_sub_fastDecay

-- `RBM3D/Induction/Step34Pins.lean` (fc76526): the mollifier class and the `𝒫`, `𝒬` operators
#check @RBM.Gauss.Sizes.STMollifierProps
#check @RBM.Gauss.Sizes.STMollifierEx
#check @RBM.Gauss.Sizes.STPsum
#check @RBM.Gauss.Sizes.STQop
#check @RBM.Gauss.Sizes.STEKDecay

-- `RBM3D/Evolution/Pins.lean` (d9de66f): `(deccA0)`, `(sumAzero)`, sign data
#check @RBM.EKFastDecay
#check @RBM.EKSumZero
#check @RBM.EKsgn
#check @RBM.ek_norm_spin

-- `RBM3D/Kernel/Evolution.lean` (ff8d36d): `Θ^{(n)}`, its one-index kernel
#check @RBM.ThetaN
#check @RBM.thetaKer
#check @RBM.cycProd
#check @RBM.norm_cycProd
#check @RBM.sum_norm_row_le
#check @RBM.UN

-- propagator: `Θ`, property 2 (translation), property 4 (`(eq:THETAinftinf)`), property 5 (`(prop:ThfadC)`)
#check @RBM.Theta
#check @RBM.Theta_apply_add_right_of_three_le
#check @RBM.sum_norm_Theta_row_le
#check @RBM.norm_Theta_le
#check @RBM.PropSpin
#check @RBM.Prop5Decay
#check @RBM.Prop5to8
#check @RBM.prop5Decay_holds
#check @RBM.prop5to8_holds

-- `RBM3D/Defs/Block.lean` (a722f63): `S^{(B)}` (nearest neighbour)
#check @RBM.SB
#check @RBM.SB_apply
#check @RBM.sbKernel
#check @RBM.sum_SB_row
#check @RBM.sum_norm_SB_row
#check @RBM.norm_SB

-- `RBM3D/Defs/Params.lean` (c3f3d5d), `RBM3D/Defs/Lattice.lean` (51f1a17): scales, distances
#check @RBM.ellT
#check @RBM.Bparam
#check @RBM.one_le_ellT
#check @RBM.ellT_pos
#check @RBM.ellT_le_L
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_add_le
#check @RBM.zdistD_neg

-- `RBM3D/Induction/B45.lean` (1ef8fa7): row sums of the kernel
#check @RBM.Gauss.Sizes.B45_row_thetaKer

-- `Θ^{(2)}` of Step 2/6: `RBM3D/Induction/Step2Defs.lean` (86124dc), `Step2Iterate.lean` (c5bbae7),
-- `RBM3D/Defs/Semicircle.lean` (fbc9870), `RBM3D/Induction/Step6Pins.lean` (cda3bb2; downstream `STExpQsrc`)
#check @RBM.Gauss.Sizes.STthetaOp
#check @RBM.Gauss.Sizes.STmsig
#check @RBM.Gauss.Sizes.STthetaOp_eq_ThetaN
#check @RBM.mSigma
#check @RBM.norm_mSigma
#check @RBM.Gauss.Sizes.STExpQsrc
#check @RBM.Gauss.Sizes.STExpDuhamelQ

/-! ## 2. Statements of the public theorems of `QopDecay.lean` (closed `Prop`s) -/

noncomputable section

namespace RBM.Gauss.Sizes.T2249Check

open RBM RBM.Gauss

/-- Target 1 (supervisor 0255 §2.2 (d) step 1): the derivative of the explicit mollifier decays, with the constant
`C = (1 + 40 d m) 6^{d m}` of `QopAlgebra_mollifier_props` and `c = 1/4`; the shape is clause 4 of `STMollifierProps`
times the decay factor of its clause 2 (at `m = 1`: `C* = (1 + 40 d) 6^d`, `c* = 1/4`, as the supervisor wrote). -/
def QopAlgebra_mollifier_derivDecay : Prop :=
  ∀ (d L m : ℕ) [NeZero L], 3 ≤ L → ∀ {g : ℝ}, 0 < g →
    ∀ t : ℝ, 0 ≤ t → t < 1 → ∀ a : Fin (m + 1) → Zd d L,
      ‖deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t‖ ≤
        (1 + 40 * ((d * m : ℕ) : ℝ)) * 6 ^ (d * m) * (1 - t)⁻¹ * (((ellT L g t) ^ d)⁻¹) ^ m *
          Real.exp (-(1 / 4) * (∑ i ∈ Finset.univ.erase (0 : Fin (m + 1)),
            (zdistD d L (a i - a 0) : ℝ)) / ellT L g t)

/-- Target 2: the source term `(𝒫 f)_{a₁} ∂_tϑ_{t,a}` of `STExpQsrc` is `(t, ε', D')`-decaying for every `ε', D'`,
once `W ≥ W₀(d, m, K, C₀, ε', D')`, if `‖𝒫 f‖ ≤ W^{C₀}` and `(1 - t)⁻¹ ≤ W^K` (pattern `stQop_sub_fastDecay`). -/
def QopDecay_deriv_fastDecay : Prop :=
  ∀ (d m : ℕ) (K C₀ ε' D' : ℝ), 0 < ε' →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g →
      ∀ W : ℝ, W₀ ≤ W → ∀ t : ℝ, 0 ≤ t → t < 1 → (1 - t)⁻¹ ≤ W ^ K →
      ∀ B : Zd d L → ℂ, ‖B‖ ≤ W ^ C₀ →
        EKFastDecay g t W ε' D'
          (fun a : Fin (m + 1) → Zd d L => B (a 0) * deriv (fun τ => QopAlgebra_mollifier d L m g τ a) t)

/-- Target 3: the one-index kernel `μ S^{(B)} Θ_{uμ}` of `Θ^{(n)}_u` (`3_5:112`) decays at scale `ℓ_u` with prefactor
`(1 - u)⁻¹` (property 5 `Prop5Decay` + `(eq:THETAinftinf)`-size `B_{u,·} ≤ 2 (1 - u)⁻¹`), for every `|μ| = 1`
(every sign pair, alternating or not); constants `(d, Λ)`. -/
def QopDecay_thetaKer_decay : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ Λ : ℝ, 0 < Λ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ u : ℝ, 0 ≤ u → u < 1 → ∀ μ : ℂ, ‖μ‖ = 1 → ∀ x y : Zd d L,
        ‖thetaKer d L g μ u x y‖ ≤ C * (1 - u)⁻¹ * Real.exp (-c * (zdistD d L (y - x) : ℝ) / ellT L g u)

/-- Target 4 (supervisor 0255 §2.2 "(c)"): `Θ^{(n)}_{u}` maps a `(u, ε, D)`-decaying tensor of size `≤ W^{C₀}` to a
`(u, 2ε, D - (K + 1))`-decaying tensor, for `W ≥ W₀(d, n, Λ, K, C₀, ε, D)`, `L^d ≤ W^K`, `(1 - u)⁻¹ ≤ W^K`; any tensor
order `n`, any unit charges `μs` (covers `EKsgn m σ` and `fun i => mSigma E (σ i)`). -/
def QopDecay_ThetaN_fastDecay : Prop :=
  ∀ (d n : ℕ), 3 ≤ d → ∀ (Λ K C₀ ε D : ℝ), 0 < Λ → 0 < ε →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (L : ℕ) [NeZero L], 3 ≤ L → ∀ g : ℝ, 0 < g → g ≤ Λ →
      ∀ W : ℝ, W₀ ≤ W → (L : ℝ) ^ d ≤ W ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ W ^ K →
      ∀ μs : Fin n → ℂ, (∀ i, ‖μs i‖ = 1) →
      ∀ A : (Fin n → Zd d L) → ℂ, ‖A‖ ≤ W ^ C₀ → EKFastDecay g u W ε D A →
        EKFastDecay g u W (2 * ε) (D - (K + 1)) (ThetaN d L g μs u A)

/-- Target 5: target 4 for the Step 2/6 operator `STthetaOp` (`n = 2`, through `STthetaOp_eq_ThetaN`, `norm_mSigma`),
the form S6-09b applies to the commutator part of `STExpQsrc`. -/
def QopDecay_STthetaOp_fastDecay : Prop :=
  ∀ {d : ℕ}, 3 ≤ d → ∀ (Λ K C₀ ε D : ℝ), 0 < Λ → 0 < ε →
    ∃ W₀ : ℝ, 1 < W₀ ∧ ∀ (sz : Sizes d) (n : ℕ) (E : ℝ), |E| ≤ 2 → 0 < sz.lam n → sz.lam n ≤ Λ →
      W₀ ≤ ((sz.W n : ℕ) : ℝ) → ((sz.L n : ℕ) : ℝ) ^ d ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ u : ℝ, 0 ≤ u → u < 1 → (1 - u)⁻¹ ≤ ((sz.W n : ℕ) : ℝ) ^ K →
      ∀ (σ : Fin 2 → Bool) (A : (Fin 2 → Zd d (sz.L n)) → ℂ), ‖A‖ ≤ ((sz.W n : ℕ) : ℝ) ^ C₀ →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) ε D A →
        EKFastDecay (sz.lam n) u ((sz.W n : ℕ) : ℝ) (2 * ε) (D - (K + 1)) (STthetaOp sz n E u σ A)

end RBM.Gauss.Sizes.T2249Check

end
