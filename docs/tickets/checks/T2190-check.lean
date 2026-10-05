/-
Release check for T2190 (dispatcher V1, Mon Oct  5 07:53 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §11, §19, §20, §56).
UN-07 (free convolution against a regular reference density; new mathematics, no RBM2D source; T2162 portmap
`docs/reports/T2162-portmap.md:201`).
Section 1: the merged names the ticket builds on (T2176 free convolution, T2174 UN pins, the semicircle) and the
Mathlib names of the route (Cauchy estimate, mean value on a convex set, Banach fixed point on a closed set, Cauchy
limits).
Section 2: the six new statements of T2190 as `def … : Prop` in the temporary namespace `RBM.Univ.T2190Check`;
the library states each as a theorem in `RBM.Univ` with exactly this body (only `Type` → `Type*` in the index
binders may differ).  Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2190-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2176 (UN-06, 52c856e): `RBM3D/Universality/FreeConv.lean`, `RBM3D/Universality/FreeConvStability.lean`
#check @RBM.Univ.freeConv_existsUnique
#check @RBM.Univ.freeConvST
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.exists_isFreeConv32
#check @RBM.Univ.isFreeConv32_unique
#check @RBM.Univ.FreeConvStability.msc_tendsto_mE
#check @RBM.Univ.FreeConvStability.freeConv_stable_local
-- T2174 (UN-01, f8ad4b4): `RBM3D/Universality/Pins.lean`
#check @RBM.Univ.mV
#check @RBM.Univ.IsRegular32
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.rhoSC
#check @RBM.Univ.Nsz
#check @RBM.Univ.UNUnivDilAt
#check @RBM.Univ.UNTrLocal
#check @RBM.Univ.UNDens
#check @RBM.Univ.UNNormBound
#check @RBM.Univ.vOU
#check @RBM.Univ.UNStep1Good
#check @RBM.Univ.UNCore
#check @RBM.Univ.UNDensBandRow
#check @RBM.Univ.un_dens_msc_zero
-- the semicircle: `RBM3D/Defs/Semicircle.lean`
#check @RBM.msc
#check @RBM.msc_im_pos
#check @RBM.norm_msc_lt_one
#check @RBM.msc_add_eq_neg_inv
-- Mathlib (the route; the same four are used by the merged `FreeConvStability.lean`)
#check @Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
#check @Convex.norm_image_sub_le_of_norm_deriv_le
#check @ContractingWith.exists_fixedPoint'
#check @cauchy_map_iff_exists_tendsto

/-! ## 2. New statements of T2190 (each a theorem with this body in `RBM.Univ`, file
`RBM3D/Universality/FreeConvRegular.lean`) -/

noncomputable section

open Filter
open scoped Topology

namespace RBM.Univ.T2190Check

open RBM RBM.Univ

/-- Target 1 `freeConvST_sub_le`: the joint modulus of `(u, z) ↦ m_{u ⊞ sc_s}(z)`, for every `s > 0`, every pair of
vectors on the same index set and every pair of points of the upper half plane (no window, no lower bound assumed;
the lower bound of `Im` enters only through the left side). -/
def freeConvST_sub_le_stmt : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (u u' : ι → ℝ) (r s : ℝ), 0 < s → (∀ i, |u i - u' i| ≤ r) →
    ∀ z z' : ℂ, 0 < z.im → 0 < z'.im →
      s ^ 2 * ((freeConvST u s z).im + (freeConvST u' s z').im) ^ 2 *
          ‖freeConvST u s z - freeConvST u' s z'‖ ≤ 2 * (r + ‖z - z'‖)

/-- Target 2 `freeConvST_norm_sq_le`: `s |m_{u ⊞ sc_s}(z)|² ≤ 1`. -/
def freeConvST_norm_sq_le_stmt : Prop :=
  ∀ {ι : Type} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (s : ℝ), 0 ≤ s → ∀ z : ℂ, 0 < z.im →
    s * ‖freeConvST u s z‖ ^ 2 ≤ 1

/-- Target 3 `unDens_freeConvST`: a sequence `m_n = m_{u_n ⊞ sc_1}` with `Im m_n ≥ c` on the window satisfies the
merged pin `UNDens`, and in addition the uniform `η`-modulus of the limit that `UNDens` does not contain (target 6). -/
def unDens_freeConvST_stmt : Prop :=
  ∀ {ι : ℕ → Type} [∀ n, Fintype (ι n)] [∀ n, Nonempty (ι n)] (u : ∀ n, ι n → ℝ) (E δ c : ℝ),
    0 < δ → 0 < c →
    (∀ᶠ n in atTop, ∀ x η : ℝ, |x - E| ≤ δ → 0 < η → η ≤ 10 → c ≤ (freeConvST (u n) 1 ⟨x, η⟩).im) →
    ∃ ρ : ℕ → ℝ, UNDens (fun n => freeConvST (u n) 1) E ρ δ ∧
      ∀ᶠ n in atTop, ∀ η : ℝ, 0 < η → η ≤ 10 →
        |(freeConvST (u n) 1 ⟨E, η⟩).im / Real.pi - ρ n| ≤ η / c ^ 2

/-- Target 4 `freeConv_stable_lip`: stability of the free convolution `v ⊞ sc_t` against an abstract reference
`mref` that is bounded below in `Im`, bounded and Lipschitz (as a complex function) on the box
`|Re z - E₀| ≤ δ`, `0 < Im z ≤ 1`.  The reference enters through the rescaled closeness hypothesis of
`FreeConvStability.freeConv_stable_local` (`msc` replaced by `mref`); the price is the term `t`. -/
def freeConv_stable_lip_stmt : Prop :=
  ∀ c K Lp δ A : ℝ, 0 < c → 0 < K → 0 < Lp → 0 < δ → 0 ≤ A →
    ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧
      ∀ (mref : ℂ → ℂ) (E₀ : ℝ), |E₀| ≤ A →
        (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (mref z).im ∧ ‖mref z‖ ≤ K) →
        (∀ z z' : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 →
          |z'.re - E₀| ≤ δ → 0 < z'.im → z'.im ≤ 1 → ‖mref z - mref z'‖ ≤ Lp * ‖z - z'‖) →
        ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t →
          0 ≤ ε → ε ≤ c₀ →
          (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
            ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * mref ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
          ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
            Tendsto (fun η : ℝ => (mref ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
            |ρ - ρ₀| ≤ C₀ * (ε + t) ∧
            ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4), ‖freeConvST v t ⟨0, η⟩ - mref ⟨E₀, η⟩‖ ≤ C₀ * (ε + t)

/-- Target 5 `freeConv_stable_freeConvST`: target 4 at the reference `mref = m_{u ⊞ sc_1}` (the block Anderson
`m(z, g)` is of this form, T2189 `BAm_eq_freeConvST`; the semicircle is `u ≡ 0`): only the lower bound of `Im` on the
box is assumed; the constants do not depend on `u`, `ι` or `card ι`. -/
def freeConv_stable_freeConvST_stmt : Prop :=
  ∀ c δ A : ℝ, 0 < c → 0 < δ → 0 ≤ A →
    ∃ c₀ c₁ C₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c₁ ∧ c₁ ≤ δ / (4 * (1 + A)) ∧ 0 < C₀ ∧
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] (u : ι → ℝ) (E₀ : ℝ), |E₀| ≤ A →
        (∀ z : ℂ, |z.re - E₀| ≤ δ → 0 < z.im → z.im ≤ 1 → c ≤ (freeConvST u 1 z).im) →
        ∀ {n : Type} [Fintype n] [Nonempty n] (v : n → ℝ) (s t ε : ℝ), 0 < t → t ≤ c₀ → s = 1 - t →
          0 ≤ ε → ε ≤ c₀ →
          (∀ w : ℂ, |w.re| ≤ c₁ → c₀ * t / 4 ≤ w.im → w.im ≤ 1 / 2 →
            ‖mV v w - (Real.sqrt s : ℂ)⁻¹ * freeConvST u 1 ((Real.sqrt s : ℂ)⁻¹ * (w + E₀))‖ ≤ ε) →
          ∃ ρ ρ₀ : ℝ, Tendsto (fun η : ℝ => (freeConvST v t ⟨0, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ) ∧
            Tendsto (fun η : ℝ => (freeConvST u 1 ⟨E₀, η⟩).im / Real.pi) (𝓝[>] 0) (𝓝 ρ₀) ∧
            |ρ - ρ₀| ≤ C₀ * (ε + t) ∧
            ∀ η ∈ Set.Ioc (0 : ℝ) (1 / 4),
              ‖freeConvST v t ⟨0, η⟩ - freeConvST u 1 ⟨E₀, η⟩‖ ≤ C₀ * (ε + t)

/-- Target 6 `unDens_not_eta_determined` (finding T2190a, compiled): the limit `ρ_n` in `UNDens` is not determined
by `m_n` on any region `Im z ≥ h_n`, `h_n > 0`: a sequence equal to `msc` there satisfies `UNDens` with
`ρ_n = ρ_sc(0) + 1/(2π)`, while `un_dens_msc_zero` gives `UNDens (fun _ => msc) 0 (fun _ => rhoSC 0) (1/2)`. -/
def unDens_not_eta_determined_stmt : Prop :=
  ∀ h : ℕ → ℝ, (∀ n, 0 < h n) →
    ∃ (m : ℕ → ℂ → ℂ) (ρ : ℕ → ℝ), UNDens m 0 ρ (1 / 2) ∧
      (∀ n (z : ℂ), h n ≤ z.im → m n z = msc z) ∧ ∀ n, ρ n = rhoSC 0 + 1 / (2 * Real.pi)

end RBM.Univ.T2190Check

end
