/-
Release check for T2205 (dispatcher V1, Mon Oct  5 2026; CLAUDE.md §4 step 0; DECISIONS §20, §29, §45 O2, §68).
BA-D3: the BA Step-1 / main-induction design note (report only; probe `RBM3D/Probe/T2205Pins.lean` on `t/T2205`).
Section 1: `#check` of every merged name the ticket cites (namespaces as on `main` 3429d7d).
Section 2: target 2, the three deterministic pins (`BAgapReal`, `BAmWindow`, `BAzztE_inv`) as `def … : Prop`, written
from merged definitions only (the probe states them with exactly these bodies, or the report gives the change and why).
Section 3: target 1, the family vocabulary that is writable from merged definitions (`BAWinBulk`, `BAFamCone`, `BAFamZ`)
and two deterministic statements about it (`…_stmt`, the probe proves them under the names without `_stmt`).
Section 4: Prop-valued examples at concrete data (no proof obligation).
No theorem, no proof, no placeholder, no tactic block.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2205-check.lean`.
-/
import RBM3D

/-! ## 1. Merged names -/

-- T2189 (BA-D1a + BA-D2, ae63e74): `RBM3D/BA/MFixedPoint.lean`
#check @RBM.BA.BAMB
#check @RBM.BA.BASelf
#check @RBM.BA.BAspec
#check @RBM.BA.BAPsi_isHermitian
#check @RBM.BA.BAt0
#check @RBM.BA.BAflowE
#check @RBM.BA.BAt0_pos
#check @RBM.BA.BAt0_lt_one
#check @RBM.BA.BAt0_mul
#check @RBM.BA.BAzztE_data
#check @RBM.BA.BAm
#check @RBM.BA.BArho
#check @RBM.BA.BAward_avg
#check @RBM.BA.BAbulk
#check @RBM.BA.BAReal
#check @RBM.BA.BAdom
#check @RBM.BA.BAm_spec
#check @RBM.BA.BAdom_real
#check @RBM.BA.BAg0_le
#check @RBM.BA.BAmBoundary
#check @RBM.BA.BAWard
#check @RBM.BA.BAPropM
#check @RBM.BA.BAoffDiag
#check @RBM.BA.BAImmLower
#check @RBM.BA.BAMB_trace_eq_sum
#check @RBM.BA.BASelf_iff_freeConv
#check @RBM.BA.BASelf_exists
#check @RBM.BA.BASelf_unique
#check @RBM.BA.baMUniqReal_holds
#check @RBM.BA.BAm_self
#check @RBM.BA.BAm_real_eq_of_self
#check @RBM.BA.MFixedPointInst.FlowPt
#check @RBM.BA.MFixedPointInst.P
-- T2013 (MD-3, 868b3b4): `RBM3D/Gauss/BlockAnderson.lean`, `RBM3D/Loop/GLoopFlow.lean`
#check @RBM.Gauss.PsiB
#check @RBM.Gauss.PsiB_isHermitian
#check @RBM.Gauss.Sizes.seqHflowBA
#check @RBM.Gauss.Sizes.Gt_BA
#check @RBM.Gauss.ztOf
#check @RBM.Gauss.etaOf
#check @RBM.Gauss.Mres
#check @RBM.Gauss.Sizes.Lloop
-- T2006 (MD-1, 0a873f1): `RBM3D/Defs/Sizes.lean`, `RBM3D/Gauss/FineModel.lean`
#check @RBM.Gauss.Sizes
#check @RBM.Gauss.Sizes.size
#check @RBM.Gauss.Sizes.WO
#check @RBM.Gauss.Sizes.Admissible
#check @RBM.Gauss.Sizes.withLam
#check @RBM.Gauss.Sizes.Bctl
#check @RBM.Gauss.Sizes.SeqΩ
#check @RBM.Gauss.Sizes.seqP
#check @RBM.Gauss.SizesInst.sz0
-- T2012 (MD-2, 9e2b00f): `RBM3D/Defs/StochDomAt.lean`
#check @RBM.StochDomAt
#check @RBM.Path.TimeIcc
#check @RBM.Gauss.Sizes.Prec
#check @RBM.Gauss.Sizes.Whp
-- T2028 (S1-07, 64bdfd3): `RBM3D/Induction/Defs.lean` (the band Step 1 and `lem:main_ind`: the template)
#check @RBM.Gauss.Sizes.STLK
#check @RBM.Gauss.Sizes.STLmax
#check @RBM.Gauss.Sizes.STDecay
#check @RBM.Gauss.Sizes.STDecayStrong
#check @RBM.Gauss.Sizes.STLocalMax
#check @RBM.Gauss.Sizes.STLocalEntry
#check @RBM.Gauss.Sizes.STExp2
#check @RBM.Gauss.Sizes.STConStInd
#check @RBM.Gauss.Sizes.STKbound
#check @RBM.Gauss.Sizes.STStep1Loop
#check @RBM.Gauss.Sizes.STStep1Weak
#check @RBM.Gauss.Sizes.STForbidden
#check @RBM.Gauss.Sizes.STConArg
#check @RBM.Gauss.Sizes.STBootstrap
#check @RBM.Gauss.Sizes.STFlow
#check @RBM.Gauss.Sizes.STMainInd
#check @RBM.Gauss.Sizes.STStep1
-- the proved band Step 1 and ConArg (T2126 0ce09c2 `Green/GbEXP.lean`; T2076 8a8cfeb `Induction/ConArg.lean`)
#check @RBM.Green.stStep1_holds
#check @RBM.Ind.ConArgPin
#check @RBM.Ind.conArg
#check @RBM.Gauss.Sizes.stConArg_holds
-- the regime pins Steps 2-5 (T2066 86124dc, T2053 fc76526, T2138 c8e4f17)
#check @RBM.Gauss.Sizes.STStep2
#check @RBM.Gauss.Sizes.STStep3R
#check @RBM.Gauss.Sizes.STStep4R
#check @RBM.Gauss.Sizes.STIngR5
#check @RBM.Gauss.Sizes.STStep5R
#check @RBM.Gauss.Sizes.STReg5I
#check @RBM.Gauss.Sizes.STReg5II
#check @RBM.Gauss.Sizes.STReg5III
#check @RBM.Gauss.Sizes.STReg5IV
#check @RBM.Gauss.Sizes.STGdecayW
-- the restriction of `(con_st_ind)` used at the stage starts (T2058 7c3072a, `Induction/ScaleFacts3.lean:478`)
#check @RBM.Gauss.Sizes.st_conStInd_sub
-- deterministic vocabulary
#check @RBM.Zd
#check @RBM.Bparam
#check @RBM.ellT
-- T2174 (UN-01, f8ad4b4), T2187 (UN-01b, fdbb6f0): the band consumer shape of the BA-V3 output
#check @RBM.Univ.UNMLOut
#check @RBM.Univ.UNKind

noncomputable section

namespace RBM.BA.T2205Check

open RBM RBM.Gauss RBM.Gauss.Sizes RBM.BA

/-! ## 2. Target 2: the deterministic pins (coupling window; `d` is the dimension, constants first) -/

section DetPins

variable (d : ℕ)

/-- **The stability gap on the real axis.**  For a real-axis solution `m` of `(self_m)` at `(g, E)`:
`Re (1 - L^{-d} tr (M^{(B)})²) ≥ 2 (Im m)²`.  (With `w_i = g λ_i - E - m`: `⟨|w|^{-2}⟩ = 1` by `BAward_avg`,
`Re (1 - ⟨w^{-2}⟩) = 2 (Im m)² ⟨|w|^{-4}⟩ ≥ 2 (Im m)²` by Cauchy-Schwarz.)  Not in `MFixedPoint`; owed or proved
(BA-D8). -/
def BAgapReal : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (E : ℝ) (m : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    BASelf d L g (E : ℂ) m →
      2 * m.im ^ 2 ≤
        (1 - (((L ^ d : ℕ) : ℂ))⁻¹ * (BAMB d L g (E : ℂ) m * BAMB d L g (E : ℂ) m).trace).re

/-- **`m(E, ·)` on the coupling window** (supervisor 1806 §1.5 (b)).  For `g ≤ Λ` and `E` in the κ-bulk at `g`
(`BAReal`), every `g' ∈ [√(1 - c₁) g, g]` has a real-axis solution `m(E, g')` with `Im m(E, g') ≥ κ/2`, and
`|m(E, g') - m(E, g)| ≤ C (g - g')`; `c₁ ∈ (0, 1/2]` and `C` depend on `(d, Λ, κ)` only
(`∂_g m = -L^{-d} tr (M²Ψ) / (1 - L^{-d} tr M²)`, `|L^{-d} tr (M²Ψ)| ≤ 2d`, gap `BAgapReal`). -/
def BAmWindow (Λ κ : ℝ) : Prop :=
  3 ≤ d → 0 < Λ → 0 < κ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → g ≤ Λ → ∀ (E : ℝ) (m : ℂ),
        haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
        BAReal d L g κ E m → ∀ g' : ℝ, Real.sqrt (1 - c₁) * g ≤ g' → g' ≤ g →
          BAReal d L g' (κ / 2) E (BAm d L g' (E : ℂ)) ∧ ‖BAm d L g' (E : ℂ) - m‖ ≤ C * (g - g')

/-- **The inverse of `zztE_BA`** (used by supervisor 1806 §1.4): flow data `(τ, E, √τ g)` with a real-axis solution
`m₀` come from the spectral parameter `z' = z_τ(E, √τ g)/√τ` at coupling `g`, with `m(z', g) = √τ m₀`. -/
def BAzztE_inv : Prop :=
  ∀ (L : ℕ) (hL : 3 ≤ L) (g : ℝ), 0 < g → ∀ (τ E : ℝ) (m₀ : ℂ),
    haveI : NeZero L := ⟨Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 2) hL)⟩
    0 < τ → τ < 1 → BASelf d L (Real.sqrt τ * g) (E : ℂ) m₀ →
      BAm d L g (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) = (Real.sqrt τ : ℂ) * m₀ ∧
        BAt0 (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = τ ∧
        BAflowE (ztOf m₀ E τ / (Real.sqrt τ : ℂ)) ((Real.sqrt τ : ℂ) * m₀) = E

end DetPins

/-! ## 3. Target 1: the family vocabulary writable from merged definitions

Along a sequence `z`, with `t₀_n = BAt0 (z n) (BAm … (z n))`, `E_n = BAflowE (z n) (BAm … (z n))` and
`g₀_n = √t₀_n · sz.lam n` (T2161 `BAflowT0`, `BAflowEs`, `BAflowLam0`, written out). -/

/-- The window `[√(1 - c₁) g₀, g₀]` lies in the κ-bulk at the energy `E` (structural premise of the family pins). -/
def BAWinBulk {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ κ : ℝ) : Prop :=
  ∀ (n : ℕ) (g' : ℝ),
    Real.sqrt (1 - c₁) * (Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n) ≤ g' →
    g' ≤ Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n →
    κ ≤ (BAm d (sz.L n) g' (BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n)) : ℂ)).im

/-- From the chain domain and `BAmWindow`: the window is in the `κ/2`-bulk (`c₁` after `κ, Λ`, before the sequence). -/
def BAWinBulk_of_dom_stmt (d : ℕ) : Prop :=
  3 ≤ d → ∀ κ Λ : ℝ, 0 < κ → 0 < Λ →
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 / 2 ∧
      ∀ (ε : ℝ) (sz : Sizes d) (z : ℕ → ℂ), (∀ n, 0 < sz.lam n ∧ sz.lam n ≤ Λ) →
        (∀ n, BAdom d (sz.L n) (sz.size n) (sz.lam n) κ ε (z n)) → BAWinBulk sz z c₁ (κ / 2)

/-- Route (B) family at time `u`, the `g₀`-cone: carrier couplings `lam'` with `g₀ √(max(u, 1 - c₁)) ≤ lam' ≤ g₀`. -/
def BAFamCone {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u lam' : ℕ → ℝ) : Prop :=
  ∀ n, Real.sqrt (max (u n) (1 - c₁)) * (Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n)
      ≤ lam' n ∧
    lam' n ≤ Real.sqrt (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) * sz.lam n

/-- The cone is closed under the ConArg rescaling `lam' ↦ √(s/u) lam'` from a target at time `u` to a source at time
`s ∈ [1 - c₁, u]` (a fixed window `[g₀√(1 - c₁), g₀]` is not: a target at its bottom has its source below it). -/
def BAFamCone_closed_stmt (d : ℕ) : Prop :=
  ∀ (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (s u lam' : ℕ → ℝ),
    (∀ n, 0 ≤ sz.lam n) → (∀ n, 1 - c₁ ≤ s n) → (∀ n, s n ≤ u n) → (∀ n, 0 < s n) →
    BAFamCone sz z c₁ u lam' → BAFamCone sz z c₁ s (fun n => Real.sqrt (s n / u n) * lam' n)

/-- Route (A) family at time `u`, the horizon cone: spectral parameters `z'` with the energy of `z` and a horizon
`t₀(z') ∈ [min(t₀(z), max(u, 1 - c₁)), t₀(z)]` (so `u ≤ t₀(z')` when `u ≤ t₀(z)` and `1 - c₁ ≤ t₀(z)`). -/
def BAFamZ {d : ℕ} (sz : Sizes d) (z : ℕ → ℂ) (c₁ : ℝ) (u : ℕ → ℝ) (z' : ℕ → ℂ) : Prop :=
  ∀ n, BAflowE (z' n) (BAm d (sz.L n) (sz.lam n) (z' n)) = BAflowE (z n) (BAm d (sz.L n) (sz.lam n) (z n)) ∧
    min (BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))) (max (u n) (1 - c₁))
      ≤ BAt0 (z' n) (BAm d (sz.L n) (sz.lam n) (z' n)) ∧
    BAt0 (z' n) (BAm d (sz.L n) (sz.lam n) (z' n)) ≤ BAt0 (z n) (BAm d (sz.L n) (sz.lam n) (z n))

/-! ## 4. Statement shapes at concrete data (no proof obligation) -/

-- the deterministic pins at `d = 3`, `Λ = 10` and the `κ` of the merged flow point `P` (`FlowPt 4 10`)
example : Prop := BAgapReal 3
example : Prop := BAmWindow 3 10 (RBM.BA.MFixedPointInst.P).m0.im
example : Prop := BAzztE_inv 3
-- the family vocabulary along the merged sequence `sz0`
example : Prop := BAWinBulk RBM.Gauss.SizesInst.sz0 (fun _ => Complex.I) (1 / 10) (1 / 10)
example : Prop := BAWinBulk_of_dom_stmt 3
example : Prop := BAFamCone RBM.Gauss.SizesInst.sz0 (fun _ => Complex.I) (1 / 10) (fun _ => 1 / 2) (fun _ => 0)
example : Prop := BAFamCone_closed_stmt 3
example : Prop := BAFamZ RBM.Gauss.SizesInst.sz0 (fun _ => Complex.I) (1 / 10) (fun _ => 1 / 2) (fun _ => Complex.I)

end RBM.BA.T2205Check

end
