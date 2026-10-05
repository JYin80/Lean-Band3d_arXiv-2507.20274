/-
Release check for T2189 (dispatcher V1, Mon Oct  5 07:12 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §19, §29, §45 O2, §51).
BA-D1 (law-free part: T2161 probe sections 0-3) + BA-D2 (`(self_m)`: existence and uniqueness of `m(z, g)`).
Section 1: the merged names the ticket builds on (T2013 BA wrapper, T2176 free convolution, T2174 UN pins,
the resolvent, propagator and lattice vocabulary) and the Mathlib names of the spectral bridge.
Section 2: the pinned vocabulary and the seven deterministic pins, verbatim from `RBM3D/Probe/T2161Pins.lean`
on `t/T2161` at 82e72b3 (`:187-197`, `:278-279`, `:381-387`, `:451-460`, `:531-548`, `:571-651`; the 21 bodies
were compared with the probe by md5 of the whitespace-normalised text: 21/21 equal), here in namespace
`RBM.BA.T2189Check`; T2189 defines them in `RBM.BA` verbatim (docstrings may be kept from the probe).
Section 3: `BAspec` (target 1) and the new statements of targets 4a-4f as `def … : Prop` (the library states them as theorems with exactly
these bodies).  Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2189-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2013 (MD-3, 868b3b4): the block Anderson wrapper and the flow data
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.PsiI
#check @RBM.Gauss.Mres
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.Gres
#check @RBM.Gauss.Sizes.seqHBA
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.Gt_BA
-- T2176 (UN-06, 52c856e) and T2174 (UN-01, f8ad4b4): the free convolution with the semicircle
#check @RBM.Univ.freeConv_existsUnique
#check @RBM.Univ.freeConvST
#check @RBM.Univ.isFreeConv51_freeConvST
#check @RBM.Univ.isFreeConv32_unique
#check @RBM.Univ.IsFreeConv32
#check @RBM.Univ.mV
-- resolvent, propagator, lattice, parameters
#check @RBM.isUnit_sub_smul_of_isHermitian
#check @RBM.PropThetaQ
#check @RBM.Zd
#check @RBM.zdistD
#check @RBM.zdistD_neg
#check @RBM.Adj
#check @RBM.ellT
#check @RBM.Bparam
-- Mathlib (spectral bridge; the model is the private `RBM.Univ.InjSum_green_eq_spectral`, `Universality/InjSum.lean:43`)
#check @Matrix.IsHermitian.eigenvalues
#check @Matrix.IsHermitian.eigenvectorUnitary
#check @Matrix.IsHermitian.spectral_theorem
#check @Matrix.trace_mul_comm
#check @Matrix.trace_diagonal
#check @Matrix.trace_smul
#check @Matrix.nonsing_inv_eq_ringInverse
#check @Matrix.inv_smul
#check @Unitary.coe_star_mul_self
#check @Unitary.coe_mul_star_self
#check @Ring.inverse
#check @Ring.mul_inverse_cancel

/-! ## 2. Pinned vocabulary and pins (T2189 targets 1-2; defined in `RBM.BA` verbatim) -/

noncomputable section

open Filter Matrix
open scoped Topology

namespace RBM.BA.T2189Check

open RBM RBM.Gauss

section Det
variable (d L : ℕ) [NeZero L]

/-- `M^{(B)}(z) = (g Ψ^{(B)} - z - m)⁻¹` of `(def_G0)` (`1_2:631`), the value `m` given. -/
def BAMB (g : ℝ) (z m : ℂ) : Matrix (Zd d L) (Zd d L) ℂ := Mres ((g : ℂ) • PsiB d L) z m

/-- **`(self_m)`** (`1_2:626-629`): `m = L^{-d} tr (g Ψ^{(B)} - z - m)⁻¹`, `Im m > 0`. -/
def BASelf (g : ℝ) (z m : ℂ) : Prop :=
  0 < m.im ∧ m = (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g z m).trace

/-- The subordination datum `m_w = L^{-d} tr (g Ψ^{(B)} - w)⁻¹`. -/
def BAmSubord (g : ℝ) (w : ℂ) : ℂ :=
  (((L ^ d : ℕ) : ℂ))⁻¹ * (Ring.inverse ((g : ℂ) • PsiB d L - w • (1 : Matrix (Zd d L) (Zd d L) ℂ))).trace

def BAt0 (z m : ℂ) : ℝ := m.im / (m.im + z.im)
def BAflowE (z m : ℂ) : ℝ := (BAt0 z m * z.re - (1 - BAt0 z m) * m.re) / Real.sqrt (BAt0 z m)

end Det

section DetPins
variable (d L : ℕ) [NeZero L]

/-- **`m(z, g)`** of `(self_m)`: the solution with `Im m > 0`; `0` if `(self_m)` has none. -/
def BAm (g : ℝ) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable (∃ m, BASelf d L g z m)
  if h : ∃ m, BASelf d L g z m then h.choose else 0

/-- **`ρ_N(E) = π⁻¹ Im m(E + i0)`** (`1_2:624`; DECISIONS §11, §51). -/
def BArho (g E : ℝ) : ℝ := (BAm d L g (E : ℂ)).im / Real.pi

end DetPins

section Bulk
variable (d L : ℕ) [NeZero L]

/-- **The bulk set `B_κ = {E : ρ_N(E) ≥ κ}`** (DECISIONS §51). -/
def BAbulk (g κ E : ℝ) : Prop := κ ≤ BArho d L g E

/-- The data of the real-axis pins: `m` solves `(self_m)` at the real energy `E` and `κ ≤ Im m`. -/
def BAReal (g κ E : ℝ) (m : ℂ) : Prop := BASelf d L g (E : ℂ) m ∧ κ ≤ m.im

/-- The chain domain at a complex point: `Im m(z, g) ≥ κ`, `N^{-1+ε} ≤ Im z ≤ 1`. -/
def BAdom (N : ℕ) (g κ ε : ℝ) (z : ℂ) : Prop :=
  κ ≤ (BAm d L g z).im ∧ (N : ℝ) ^ (-1 + ε) ≤ z.im ∧ z.im ≤ 1

end Bulk

section Thetas
variable (d L : ℕ) [NeZero L]

/-- `M(σ)`: `M(+) = M^{(B)}`, `M(-) = (M^{(B)})^*` (`1_2:1071`). -/
def BAMsigma (M : Matrix (Zd d L) (Zd d L) ℂ) (σ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  if σ then M else Mᴴ

/-- `M^{(σ₁,σ₂)}_{ab} = M^{(B)}_{ba}(σ₁) M^{(B)}_{ab}(σ₂)` (`(eq:Msig)`, `1_2:1070-1071`). -/
def BAMss (M : Matrix (Zd d L) (Zd d L) ℂ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => BAMsigma d L M σ₁ b a * BAMsigma d L M σ₂ a b

/-- `Θ_t^{(σ₁,σ₂)} = (1 - t M^{(σ₁,σ₂)})⁻¹` (`(def_Thxi)`, `1_2:1073-1076`) at the real-axis data `(g, E, m)`. -/
def BATheta (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  PropThetaQ (BAMss d L (BAMB d L g (E : ℂ) m) σ₁ σ₂) t

/-- `Θ̊`: the propagator without its zero mode (`(def_Thxi0)`, `1_2:1105`). -/
def BATheta0 (g E : ℝ) (m : ℂ) (t : ℝ) (σ₁ σ₂ : Bool) : Matrix (Zd d L) (Zd d L) ℂ :=
  Matrix.of fun a b => BATheta d L g E m t σ₁ σ₂ a b
    - ((L : ℂ) ^ (2 * d))⁻¹ * ∑ a', ∑ b', BATheta d L g E m t σ₁ σ₂ a' b'

end Thetas

section DetPins2
variable (d : ℕ)

/-- **Pin BA-1, existence and uniqueness of `m(z, g)`** (`1_2:626-629`).  T2189 target 4e proves it. -/
def BAmExists : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ z : ℂ, 0 < z.im →
    haveI : NeZero L := ⟨by omega⟩
    ∃! m : ℂ, BASelf d L g z m

/-- **Pin BA-1, uniqueness on the real axis.**  T2189 target 4e proves it. -/
def BAmUniqReal : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m m' : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    BASelf d L g (E : ℂ) m → BASelf d L g (E : ℂ) m' → m = m'

/-- **Pin BA-2, the boundary value** (`1_2:715`).  Owed: BA-D6. -/
def BAmBoundary : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ E : ℝ,
    haveI : NeZero L := ⟨by omega⟩
    (∀ m : ℂ, BASelf d L g (E : ℂ) m →
      Tendsto (fun η : ℝ => BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝 m)) ∧
    ((¬ ∃ m : ℂ, BASelf d L g (E : ℂ) m) →
      Tendsto (fun η : ℝ => (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] (0 : ℝ)) (𝓝 0))

/-- **Pin BA-1, Ward's identity row by row** (`(eq:WardM)`, `7_8:1869`), translation invariance, `M_aa = m`.
Owed: BA-D3. -/
def BAWard : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (z m : ℂ),
    haveI : NeZero L := ⟨by omega⟩
    0 ≤ z.im → BASelf d L g z m →
      (∀ a b r : Zd d L, BAMB d L g z m (a + r) (b + r) = BAMB d L g z m a b) ∧
      (∀ a : Zd d L, BAMB d L g z m a a = m) ∧
      ∀ a : Zd d L, (m.im + z.im) * ∑ b, ‖BAMB d L g z m a b‖ ^ 2 = m.im

/-- **`lem:propM`** (`7_8:1847-1912`) in the bulk `κ ≤ Im m`.  Owed: BA-D3 (items (1)(2)), BA-D4 (item (3)). -/
def BAPropM (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m →
          (∀ a b r : Zd d L, BAMB d L g (E : ℂ) m (a + r) (b + r) = BAMB d L g (E : ℂ) m a b) ∧
          (∀ a : Zd d L, BAMB d L g (E : ℂ) m a a = m) ∧
          (∀ a : Zd d L, ∑ b, ‖BAMB d L g (E : ℂ) m a b‖ ^ 2 = 1) ∧ ‖m‖ ≤ 1 ∧
          (g < (2 * C)⁻¹ → ∀ a b : Zd d L,
            C⁻¹ * g * (if Adj d L a b then 1 else 0) ≤ ‖BAMB d L g (E : ℂ) m a b‖ ∧
              ‖BAMB d L g (E : ℂ) m a b‖ ≤ (C * g) ^ zdistD d L (a - b)) ∧
          ((2 * C)⁻¹ ≤ g → ∀ a b : Zd d L,
            ‖BAMB d L g (E : ℂ) m a b‖ ≤ c⁻¹ * Real.exp (-c * (zdistD d L (a - b) : ℝ)))

/-- **`(eq:off_diagM)`** (`A:32-34`).  Owed: BA-D3. -/
def BAoffDiag (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ε ≤ ‖1 - (t : ℂ) * m ^ 2‖ ∧
          ∑ a ∈ Finset.univ.erase (0 : Zd d L), ‖BAMss d L (BAMB d L g (E : ℂ) m) true true 0 a‖
            ≤ (1 - ε) * ‖1 - (t : ℂ) * m ^ 2‖

/-- **The bridge of the bulk forms** (`[LeeSchSteYau2015, Lemma 3.5]`, internal).  Owed: BA-D7. -/
def BAImmLower (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c : ℝ, 0 < c ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨by omega⟩
        BAReal d L g κ E m → ∀ η : ℝ, 0 < η → η ≤ 1 →
          c ≤ (BAm d L g ((E : ℂ) + (η : ℂ) * Complex.I)).im

end DetPins2

/-! ## 3. New statements of T2189 (`BAspec` of target 1; targets 4a-4f, each a theorem with this body in the library) -/

/-- Target 1 (new vocabulary): the spectrum of `g Ψ^{(B)}`, `v_i = g λ_i(Ψ^{(B)})` (the eigenvalues of the merged
`PsiB_isHermitian`, scaled; no proof term of the scaled matrix enters). -/
def BAspec (d L : ℕ) [NeZero L] (g : ℝ) : Zd d L → ℝ :=
  fun i => g * (PsiB_isHermitian d L).eigenvalues i

/-- Target 4a `BAMB_trace_eq_sum` (spectral bridge). -/
def BAMB_trace_eq_sum_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), (z + m).im ≠ 0 →
    (BAMB d L g z m).trace = ∑ i, ((BAspec d L g i : ℂ) - (z + m))⁻¹

/-- Target 4b `BASelf_iff_freeConv`: `(self_m)` is `[32] (2.5)` at `v = BAspec`, `t = 1`, in the exact form of
`RBM.Univ.freeConv_existsUnique`. -/
def BASelf_iff_freeConv_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z m : ℂ), 0 ≤ z.im →
    (BASelf d L g z m ↔ 0 < m.im ∧
      m = ((Fintype.card (Zd d L) : ℕ) : ℂ)⁻¹ * ∑ i, ((BAspec d L g i : ℂ) - z - ((1 : ℝ) : ℂ) * m)⁻¹)

/-- Target 4c `BASelf_exists`. -/
def BASelf_exists_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z : ℂ), 0 < z.im → ∃ m : ℂ, BASelf d L g z m

/-- Target 4d `BASelf_unique` (every `Im z ≥ 0`, real axis included). -/
def BASelf_unique_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z m m' : ℂ), 0 ≤ z.im → BASelf d L g z m → BASelf d L g z m' → m = m'

/-- Target 4f `BAm_self`. -/
def BAm_self_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z : ℂ), 0 < z.im → BASelf d L g z (BAm d L g z)

/-- Target 4f `BAm_eq_freeConvST` (the bridge to the merged free-convolution Stieltjes transform). -/
def BAm_eq_freeConvST_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g : ℝ) (z : ℂ), 0 < z.im → BAm d L g z = RBM.Univ.freeConvST (BAspec d L g) 1 z

/-- Target 4f `BAm_real_eq_of_self` (unconditional form of the probe's `BAm_real_eq`, `:1740`). -/
def BAm_real_eq_of_self_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g E : ℝ) (m : ℂ), BASelf d L g (E : ℂ) m → BAm d L g (E : ℂ) = m

/-- Target 4f `BAbulk_iff_exists` (unconditional form of the probe's `BAbulk_iff`, `:472`). -/
def BAbulk_iff_exists_stmt (d L : ℕ) [NeZero L] : Prop :=
  ∀ (g κ E : ℝ), 0 < κ → (BAbulk d L g κ E ↔ ∃ m : ℂ, BASelf d L g (E : ℂ) m ∧ Real.pi * κ ≤ m.im)

end RBM.BA.T2189Check

end
