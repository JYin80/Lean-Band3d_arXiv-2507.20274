/-
Release check for T2202 (dispatcher V1, Mon Oct  5 17:24 UTC 2026; CLAUDE.md §4 step 0; DECISIONS §16, §20, §29, §54, §57 (2)).
UN-26a (bulk universality, GUE phase, second ticket): the abstract bootstraps of the GUE phase on the index scale,
port of the live part of RBM2D `Universality/GUEPhase/Bootstrap.lean` at `c9a24cf` (`:1-645` without
`eq736_detDom` `:477-516` and `stochDom_of_forall_highProb` `:624-632`) to `d` dimensions: `S^{(B)}_{GUE} = L^{-d}` on
`Z_L^d`, prefactor `W^d`, `N = (W L)^d`, and the merged `ellT` with the coupling `g`.  Class G of T2173 (no model
data): nothing model-specific (DECISIONS §57 (2)).
Section 1: the merged names the new file builds on (and, marked, those UN-26b will build on), and the Mathlib names
of the route (same Mathlib revision as RBM2D `c9a24cf`).
Section 2: vocabulary (`SBgueV`, `primBilGUEV`, `primRhsGUEV`, `supOnV`, `rhs745GV`, `rhs746GV`) and the pinned
statements as `def … : Prop` in the temporary namespace `RBM.Univ.GUEPhase.T2202Check`.  The library states each
pin as a theorem in `RBM.Univ.GUEPhase` whose type unfolds to exactly this body (only `Type` → `Type*` in the index
binders of `T2202_continuity_argument`, `T2202_K_bootstrap` may differ); each vocabulary def is `rfl`-equal to the
library def of the same stem (`SBgueV d L = SBgue d L`, …).
Statement and `#check` only: no theorem, no proof, no `sorry`.  Never imported or merged.
Run from the main worktree: `lake env lean docs/tickets/checks/T2202-check.lean`.
-/
import RBM3D
import Mathlib.Data.Set.Finite.List

/-! ## 1. Merged names -/

-- `RBM3D/Defs/Lattice.lean` (51f1a17)
#check @RBM.Zd
#check @RBM.card_Zd
-- `RBM3D/Loop/TreeRep.lean` (b06ff9b): replaces RBM2D `Hierarchy/Loops` + `Hierarchy/OperationsPair`
#check @RBM.Loop.LoopIdx
#check @RBM.Loop.LoopIdx.WF
#check @RBM.Loop.LoopIdx.length
#check @RBM.Loop.LoopIdx.cutGlueL
#check @RBM.Loop.LoopIdx.cutGlueR
#check @RBM.Loop.LoopIdx.length_cutGlueL
#check @RBM.Loop.LoopIdx.length_cutGlueR
#check @RBM.Loop.LoopIdx.length_cutGlueL_le
#check @RBM.Loop.LoopIdx.length_cutGlueR_le
#check @RBM.Loop.LoopIdx.wf_cutGlueL
#check @RBM.Loop.LoopIdx.wf_cutGlueR
#check @RBM.Loop.treeEqRhs
-- `RBM3D/Defs/Block.lean` (a722f63): the band profile of `treeEqRhs` (template of `primBilGUE`)
#check @RBM.SB
-- `RBM3D/Defs/Params.lean` (c3f3d5d): replaces RBM2D `Path/Scales` `ellT` (here with the coupling `g`)
#check @RBM.ellT
#check @RBM.one_le_ellT
#check @RBM.ellT_le_L
-- `RBM3D/Defs/Domination.lean` (4c5302f)
#check @RBM.UnifDetDom
#check @RBM.DetDom
#check @RBM.eventually_le_rpow
#check @RBM.UnifDetDom.of_le
-- `RBM3D/Defs/StochDom.lean` (1c2e756)
#check @RBM.StochDom
#check @RBM.HighProb
-- for UN-26b only (not imported by T2202): `RBM3D/Defs/StochDomAt.lean` (9e2b00f), `RBM3D/Gauss/DominationAt.lean`
-- (9e2b00f)
#check @RBM.StochDomAt
#check @RBM.Gauss.HighProbAt
#check @RBM.Path.TimeIcc
#check @RBM.stochDom_iff_at_id
#check @RBM.Gauss.highProb_iff_at_id
#check @RBM.Gauss.highProbAt_univ
-- Mathlib names of the route (all used verbatim or by dot notation in the RBM2D source)
#check @norm_image_sub_le_of_norm_deriv_le_segment'
#check @List.finite_length_le
#check @Set.Finite.isClosed_biUnion
#check @IsClosed.isClosed_le
#check @IsClosed.csInf_mem
#check @ContinuousWithinAt.closure_le
#check @closure_Ico
#check @ciSup_le
#check @Real.iSup_nonneg

/-! ## 2. Vocabulary and pinned statements -/

set_option linter.unusedVariables false

noncomputable section

namespace RBM.Univ.GUEPhase.T2202Check

open Filter

/-- `S^{(B)}_{GUE}` on `Z_L^d`: every entry `L^{-d}` (the block reduction `W^d · N⁻¹` of the GUE variance `N⁻¹`,
`N = (W L)^d`).  RBM2D `SBgue` (`Bootstrap.lean:55`) with `Z2 L ↦ Zd d L`, `L² ↦ L^d`. -/
def SBgueV (d L : ℕ) : Matrix (RBM.Zd d L) (RBM.Zd d L) ℂ :=
  Matrix.of fun _ _ => ((L : ℂ) ^ d)⁻¹

/-- The polarized right side of the GUE-phase primitive equation (7.33):
`W^d ∑_{1≤k<l≤n} ∑_{a,b} K(cutL^{(a)}_{k,l}) (S_GUE)_{ab} K'(cutR^{(b)}_{k,l})`.  RBM2D `primBilGUE`
(`Bootstrap.lean:152`) with `W² ↦ W^d`; the merged `treeEqRhs` (`Loop/TreeRep.lean:133`) with `SB ↦ SBgue`. -/
def primBilGUEV (d L : ℕ) [NeZero L] (W : ℕ) (K K' : RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ)
    (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  (W : ℂ) ^ d * ∑ k ∈ Finset.Icc 1 I.length, ∑ l ∈ Finset.Ioc k I.length,
    ∑ a : RBM.Zd d L, ∑ b : RBM.Zd d L,
      K (I.cutGlueL k l a) * SBgueV d L a b * K' (I.cutGlueR k l b)

/-- (7.33): RBM2D `primRhsGUE` (`Bootstrap.lean:157`). -/
def primRhsGUEV (d L : ℕ) [NeZero L] (W : ℕ) (K : RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ)
    (I : RBM.Loop.LoopIdx (RBM.Zd d L)) : ℂ :=
  primBilGUEV d L W K K I

/-- `sup_{u ∈ [a, b]} g(u)`: RBM2D `supOn` (`Bootstrap.lean:526`), verbatim. -/
def supOnV (g : ℝ → ℝ) (a b : ℝ) : ℝ := ⨆ u : Set.Icc a b, g u

/-- (7.45) with the `E^{(G)}` term `N L₂ L_n`: RBM2D `rhs745G` (`Bootstrap.lean:534`), verbatim (`N` is the matrix
size, `(W L)^d` at the consumers). -/
def rhs745GV (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOnV (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOnV (fun u => Lm 2 u * Lm n u) t1 t
    + Real.sqrt (t - t1) * supOnV (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) * Lm n u) t1 t

/-- (7.46) with the `E^{(G)}` term `N D₁ L_{n+1}`: RBM2D `rhs746G` (`Bootstrap.lean:542`), verbatim. -/
def rhs746GV (N : ℝ) (η : ℝ → ℝ) (t1 : ℝ) (Lm Dm : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  N * (t - t1) * supOnV (fun u => ∑ k ∈ Finset.Icc 2 n,
      ((N * η u)⁻¹ ^ (k - 1) + Dm k u) * Dm (n - k + 2) u) t1 t
    + (N * η t)⁻¹ ^ n
    + N * (t - t1) * supOnV (fun u => Dm 1 u * Lm (n + 1) u) t1 t
    + Real.sqrt (t - t1) * supOnV (fun u => Real.sqrt (N⁻¹ * (η u)⁻¹ ^ 2) *
        Real.sqrt (Lm (2 * n) u)) t1 t

/-- Target 1 (`sum_SBgue_col`): the columns of `S_GUE` sum to `1` (`|Z_L^d| = L^d`).  New public form of the private
RBM2D `Generator_sum_SBgue_col` (`Generator.lean:1014`), consumer UN-28. -/
def T2202_sum_SBgue_col : Prop :=
  ∀ (d L : ℕ) [NeZero L] (b : RBM.Zd d L), ∑ a : RBM.Zd d L, SBgueV d L a b = 1

/-- Target 2 (`continuity_argument`): RBM2D `Bootstrap.lean:71`, verbatim. -/
def T2202_continuity_argument : Prop :=
  ∀ {ι : Type} {S : Set ι}, S.Finite → ∀ {f g : ι → ℝ → ℝ} {t1 t0 : ℝ},
    (∀ i ∈ S, ContinuousOn (f i) (Set.Icc t1 t0)) →
    (∀ i ∈ S, ContinuousOn (g i) (Set.Icc t1 t0)) → (∀ i ∈ S, f i t1 < g i t1) →
    (∀ t ∈ Set.Icc t1 t0, (∀ u ∈ Set.Icc t1 t, ∀ i ∈ S, f i u ≤ g i u) → ∀ i ∈ S, f i t < g i t) →
    ∀ t ∈ Set.Icc t1 t0, ∀ i ∈ S, f i t < g i t

/-- Target 3 (`ellT_eq_L`): (7.30) ⟹ `ℓ_{t₁} = L` for the merged `ellT L g t = min (max (g/√|1−t|) 1) L`
(`Defs/Params.lean:32`).  RBM2D `ellT_eq_L` (`Bootstrap.lean:131`, `ellT L t = min (1/√(1−t)) L`, hypothesis
`L² (1 − t) ≤ 1`) with the coupling: `L² (1 − t) ≤ g²`, `0 ≤ g`.  `ℓ_t` is a length: the exponent stays `2` for
every `d`. -/
def T2202_ellT_eq_L : Prop :=
  ∀ {L : ℕ} {g t : ℝ}, 0 ≤ g → t < 1 → (L : ℝ) ^ 2 * (1 - t) ≤ g ^ 2 → RBM.ellT L g t = L

/-- Target 4 (`norm_primBilGUE_le`): the power counting (7.34) at `N = (W L)^d`: the double sum over
`a, b ∈ Z_L^d` with entries `L^{-d}` costs `L^{2d} L^{-d} = L^d`, times `W^d`.  RBM2D `Bootstrap.lean:208` with
`(W L)^2 ↦ (W L)^d`. -/
def T2202_norm_primBilGUE_le : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) (K K' : RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) (B B' : ℕ → ℝ)
    (I : RBM.Loop.LoopIdx (RBM.Zd d L)), I.WF →
    (∀ J : RBM.Loop.LoopIdx (RBM.Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ B J.length) →
    (∀ J : RBM.Loop.LoopIdx (RBM.Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K' J‖ ≤ B' J.length) →
    (∀ j, 0 ≤ B j) → (∀ j, 0 ≤ B' j) →
    ‖primBilGUEV d L W K K' I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) *
      ∑ j ∈ Finset.Icc 2 I.length, B (I.length - j + 2) * B' j

/-- Target 4' (`norm_primRhsGUE_le`): RBM2D `Bootstrap.lean:285` with `(W L)^2 ↦ (W L)^d` (consumer RBM2D
`HypA.lean:694`). -/
def T2202_norm_primRhsGUE_le : Prop :=
  ∀ (d L : ℕ) [NeZero L] (W : ℕ) (K : RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) (B : ℕ → ℝ)
    (I : RBM.Loop.LoopIdx (RBM.Zd d L)), I.WF →
    (∀ J : RBM.Loop.LoopIdx (RBM.Zd d L), J.WF → 2 ≤ J.length → J.length ≤ I.length →
      ‖K J‖ ≤ B J.length) →
    (∀ j, 0 ≤ B j) →
    ‖primRhsGUEV d L W K I‖ ≤ (I.length : ℝ) ^ 2 * (((W * L) ^ d : ℕ) : ℝ) *
      ∑ j ∈ Finset.Icc 2 I.length, B (I.length - j + 2) * B j

/-- Target 5 (`K_bootstrap`): (7.35) ⟹ (7.36), deterministic core.  RBM2D `Bootstrap.lean:324`, verbatim (the
drift is named `dk` here only to keep `d` for the dimension). -/
def T2202_K_bootstrap : Prop :=
  ∀ {ι : Type} {S : Set ι}, S.Finite → ∀ (len : ι → ℕ) {n : ℕ},
    (∀ i ∈ S, 2 ≤ len i ∧ len i ≤ n) → ∀ (k dk : ℝ → ι → ℂ) {t1 t0 C N A ε : ℝ},
    t1 ≤ t0 → ∀ (lam : ℝ → ℝ), (∀ t ∈ Set.Icc t1 t0, 0 < lam t) →
    (∀ u ∈ Set.Icc t1 t0, ∀ t ∈ Set.Icc t1 t0, u ≤ t → lam t ≤ lam u) →
    ContinuousOn lam (Set.Icc t1 t0) →
    (∀ t ∈ Set.Icc t1 t0, ∀ i ∈ S,
      HasDerivWithinAt (fun s => k s i) (dk t i) (Set.Icc t1 t0) t) →
    (∀ t ∈ Set.Icc t1 t0, ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → (∀ j ∈ S, ‖k t j‖ ≤ B (len j)) →
      ∀ i ∈ S, ‖dk t i‖ ≤ C * N * ∑ j ∈ Finset.Icc 2 (len i), B (len i - j + 2) * B j) →
    0 ≤ C → 0 ≤ N → 0 < A →
    (∀ i ∈ S, ‖k t1 i‖ ≤ A * (lam t1)⁻¹ ^ (len i - 1)) →
    (∀ t ∈ Set.Icc t1 t0, N * (t - t1) ≤ ε * lam t) → 4 * C * n * A * ε < 1 →
    ∀ t ∈ Set.Icc t1 t0, ∀ i ∈ S, ‖k t i‖ < 2 * A * (lam t)⁻¹ ^ (len i - 1)

/-- Target 6 (`finite_loopIdx`): RBM2D `Bootstrap.lean:408` with `Z2 L ↦ Zd d L` (consumer RBM2D `KPrim.lean:587`). -/
def T2202_finite_loopIdx : Prop :=
  ∀ (d L : ℕ) [NeZero L] (n : ℕ),
    {I : RBM.Loop.LoopIdx (RBM.Zd d L) | I.WF ∧ 2 ≤ I.length ∧ I.length ≤ n}.Finite

/-- Target 7 (`eq736`): (7.36) for the primitive loops of the GUE phase at `N = (W L)^d`.  RBM2D `Bootstrap.lean:420`
with `Z2 L ↦ Zd d L`, `(W L)^2 ↦ (W L)^d` in (7.30); explicit arguments in the order `d L W Kt`. -/
def T2202_eq736 : Prop :=
  ∀ (d L W : ℕ) [NeZero L] (Kt : ℝ → RBM.Loop.LoopIdx (RBM.Zd d L) → ℂ) {n : ℕ} {t1 t0 A ε : ℝ},
    t1 ≤ t0 → ∀ (lam : ℝ → ℝ), (∀ t ∈ Set.Icc t1 t0, 0 < lam t) →
    (∀ u ∈ Set.Icc t1 t0, ∀ t ∈ Set.Icc t1 t0, u ≤ t → lam t ≤ lam u) →
    ContinuousOn lam (Set.Icc t1 t0) →
    (∀ t ∈ Set.Icc t1 t0, ∀ I : RBM.Loop.LoopIdx (RBM.Zd d L), I.WF → 2 ≤ I.length →
      I.length ≤ n →
      HasDerivWithinAt (fun s => Kt s I) (primRhsGUEV d L W (Kt t) I) (Set.Icc t1 t0) t) →
    0 < A →
    (∀ I : RBM.Loop.LoopIdx (RBM.Zd d L), I.WF → 2 ≤ I.length → I.length ≤ n →
      ‖Kt t1 I‖ ≤ A * (lam t1)⁻¹ ^ (I.length - 1)) →
    (∀ t ∈ Set.Icc t1 t0, (((W * L) ^ d : ℕ) : ℝ) * (t - t1) ≤ ε * lam t) →
    4 * ((n : ℝ) ^ 2) * n * A * ε < 1 →
    ∀ t ∈ Set.Icc t1 t0, ∀ I : RBM.Loop.LoopIdx (RBM.Zd d L), I.WF → 2 ≤ I.length →
      I.length ≤ n → ‖Kt t I‖ < 2 * A * (lam t)⁻¹ ^ (I.length - 1)

/-- Target 8 (`eventually_small`): RBM2D `Bootstrap.lean:459`, verbatim (`N` the sequence index). -/
def T2202_eventually_small : Prop :=
  ∀ {n : ℕ} {τ' τU : ℝ}, τ' < τU →
    ∀ᶠ N : ℕ in atTop, 4 * ((n : ℝ) ^ 2) * n * (N : ℝ) ^ τ' * (N : ℝ) ^ (-τU) < 1

/-- Target 9 (`eventually_rpow_le_of_neg`): RBM2D `Bootstrap.lean:634`, verbatim (consumer RBM2D
`PathBounds.lean:541`, `BootstrapAt.lean:539`). -/
def T2202_eventually_rpow_le_of_neg : Prop :=
  ∀ {a ρ : ℝ}, a < 0 → 0 < ρ → ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ a ≤ ρ

/-- The data of the `eq736` and `ellT_eq_L` instances are nondegenerate: `N = (2·3)^3 = 216`, `N (t − t₁) ≤ 216 ≤
ε λ = 400`, `4 n³ A ε = 0.32 < 1` at `n = 2`; `L² (1 − t) = 1/4 ≤ g² = 1/4` at `L = 4`, `g = 1/2`, `t = 63/64`. -/
def T2202_inst_bounds : Prop :=
  (((2 * 3) ^ 3 : ℕ) : ℝ) * (1 - 0) ≤ 1 / 100 * 40000 ∧
    4 * ((2 : ℝ) ^ 2) * 2 * 1 * (1 / 100) < 1 ∧
    (4 : ℝ) ^ 2 * (1 - 63 / 64) ≤ (1 / 2) ^ 2

/-- Type check of the vocabulary at the instance data (`d = 3`, `L = 3`, `W = 2`, the loop of length 3 with block labels
`0, 1, 2`): with `K = K' ≡ 1` the left side is `W^d · #{k < l} · L^{2d} · L^{-d} = 8 · 3 · 27 = 648`, the bound of
target 4 is `3² · 216 · 2 = 3888`. -/
example : Prop :=
  ‖primBilGUEV 3 3 2 (fun _ => 1) (fun _ => 1)
      ⟨[true, false, true], [fun _ => 0, fun _ => 1, fun _ => 2]⟩‖ ≤ 3888

end RBM.Univ.GUEPhase.T2202Check

end

#check @RBM.Univ.GUEPhase.T2202Check.SBgueV
#check @RBM.Univ.GUEPhase.T2202Check.primBilGUEV
#check @RBM.Univ.GUEPhase.T2202Check.primRhsGUEV
#check @RBM.Univ.GUEPhase.T2202Check.supOnV
#check @RBM.Univ.GUEPhase.T2202Check.rhs745GV
#check @RBM.Univ.GUEPhase.T2202Check.rhs746GV
#check (RBM.Univ.GUEPhase.T2202Check.T2202_sum_SBgue_col : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_continuity_argument : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_ellT_eq_L : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_norm_primBilGUE_le : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_norm_primRhsGUE_le : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_K_bootstrap : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_finite_loopIdx : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_eq736 : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_eventually_small : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_eventually_rpow_le_of_neg : Prop)
#check (RBM.Univ.GUEPhase.T2202Check.T2202_inst_bounds : Prop)
